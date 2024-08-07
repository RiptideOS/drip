use std::{collections::BTreeMap, num::IntErrorKind};

use strum::IntoEnumIterator;

use crate::{
    frontend::{
        ast::{
            Block, Expression, ExpressionKind, FunctionDefinition, Literal, LiteralKind, Local,
            LocalKind, Module, NodeId, Statement, StatementKind, Type, TypeKind, UnaryOperatorKind,
        },
        intern::InternedSymbol,
        lexer::Span,
    },
    middle::resolve::{TypeNameResolution, ValueNameResolution},
};

use super::{
    hir::{
        AssignmentKind, HirBlock, HirExpression, HirExpressionKind, HirFunctionDefinition,
        HirFunctionParameter, HirLiteral, HirLocal, HirLocalKind, HirModule, HirStatement,
    },
    primitive::PrimitiveKind,
    resolve::{DefinitionId, ModuleResolutionMap, ValueDefinitionKind},
};

#[derive(Debug)]
pub struct TypeChecker<'module> {
    module: &'module Module<'module>,
    resolution_map: &'module ModuleResolutionMap,
    type_table: TypeTable,
    function_type_map: BTreeMap<DefinitionId, TypeId>,
    next_local_id: u32,
    node_to_local_map: BTreeMap<NodeId, LocalDefinitionId>,
    local_type_map: BTreeMap<LocalDefinitionId, TypeId>,
    return_points: Vec<NodeId>,
    return_type_map: BTreeMap<NodeId, TypeId>,
    return_span_map: BTreeMap<NodeId, Span>,
}

impl<'module> TypeChecker<'module> {
    pub fn type_check_module(
        module: &'module Module,
        resolution_map: &'module ModuleResolutionMap,
    ) -> HirModule {
        let mut type_checker = Self {
            module,
            resolution_map,
            type_table: TypeTable::new(),
            function_type_map: BTreeMap::new(),
            next_local_id: 0,
            node_to_local_map: BTreeMap::new(),
            local_type_map: BTreeMap::new(),
            return_points: Vec::new(),
            return_type_map: BTreeMap::new(),
            return_span_map: BTreeMap::new(),
        };

        type_checker.analyze_built_ins();

        // First, analyze all the functions in the module so at their call sites
        // we can determine if the arguments match the signature

        for function in &type_checker.module.function_definitions {
            type_checker.analyze_function(function);
        }

        // Next, analyze the bodies of all the functions and check that all
        // expression types match their expected types

        let mut function_definitions =
            Vec::with_capacity(type_checker.module.function_definitions.len());

        for function in &type_checker.module.function_definitions {
            function_definitions.push(type_checker.type_check_function(function))
        }

        HirModule {
            id: type_checker.module.id,
            function_definitions,
            type_table: type_checker.type_table,
        }
    }

    fn analyze_built_ins(&mut self) {
        let println_id = self
            .type_table
            .insert_if_absent(UniqueType::FunctionPointer {
                parameters: vec![UniqueType::Str],
                return_type: Box::new(UniqueType::Primitive(PrimitiveKind::Unit)),
                is_variadic: true,
            });

        self.function_type_map
            .insert(DefinitionId::BUILT_IN_PRINTLN, println_id);
    }

    /// Compute the type signature for the function and insert it into the type
    /// table so that at function call sights we can assign the correct
    /// "function" type for each function call target
    fn analyze_function(&mut self, function: &FunctionDefinition) {
        let parameters = function
            .signature
            .parameters
            .parameters
            .iter()
            .map(|parameter| self.compute_unique_type(&parameter.ty))
            .collect();
        let return_type = function
            .signature
            .return_type
            .as_ref()
            .map(|ty| self.compute_unique_type(ty))
            .unwrap_or(UniqueType::Primitive(PrimitiveKind::Unit));

        let type_id = self
            .type_table
            .insert_if_absent(UniqueType::FunctionPointer {
                parameters,
                return_type: Box::new(return_type),
                is_variadic: false,
            });

        self.function_type_map.insert(
            DefinitionId::new_module(self.module.id, function.id),
            type_id,
        );
    }

    /// Computes the unique type for an AST type node
    fn compute_unique_type(&mut self, ty: &Type) -> UniqueType {
        match &ty.kind {
            TypeKind::Primitive(kind) => UniqueType::Primitive(*kind),
            TypeKind::QualifiedIdentifier(qualified_ident) => {
                // We already resolved type names in the previous compilation
                // step so all we need to do is look it up and turn it into a
                // unique type

                let resolution = self
                    .resolution_map
                    .type_name_resolutions
                    .get(&qualified_ident.id)
                    .expect("Failed to retrieve type name resolution (this should never happen)");

                match resolution {
                    TypeNameResolution::Definition(_, _) => {
                        todo!("create unique types for user defined types")
                    }
                }
            }
            TypeKind::Pointer(ty) => UniqueType::Pointer(Box::new(self.compute_unique_type(ty))),
            TypeKind::Slice(ty) => UniqueType::Slice(Box::new(self.compute_unique_type(ty))),
            TypeKind::Str => UniqueType::Str,
            TypeKind::CStr => UniqueType::CStr,
            TypeKind::Array { ty, length } => {
                let length: usize = match length.symbol.value().parse() {
                    Ok(value) => value,
                    Err(e) => match e.kind() {
                        IntErrorKind::PosOverflow => {
                            self.report_error(length.span, "Integer is too large for it's type")
                        }
                        _ => unreachable!(),
                    },
                };

                UniqueType::Array {
                    ty: Box::new(self.compute_unique_type(ty)),
                    length,
                }
            }
            TypeKind::Any => UniqueType::Any,
        }
    }

    fn next_local_id(&mut self) -> LocalDefinitionId {
        let id = LocalDefinitionId(self.next_local_id);
        self.next_local_id += 1;
        id
    }

    fn report_error(&self, offending_span: Span, message: &str) -> ! {
        eprintln!(
            "{} ({}:{}:{})",
            message,
            self.module.source_file.origin,
            self.module
                .source_file
                .row_for_position(offending_span.start),
            self.module
                .source_file
                .column_for_position(offending_span.start)
        );
        self.module.source_file.highlight_span(offending_span);
        // TODO: recover from this error and keep moving
        std::process::exit(1);
    }

    fn type_check_function(&mut self, function: &FunctionDefinition) -> HirFunctionDefinition {
        // First we check that the body of the function is valid, then we make
        // sure that the return type of the block is the same as the return type
        // of the function

        self.next_local_id = 0;
        self.node_to_local_map.clear();
        self.local_type_map.clear();
        self.return_points.clear();
        self.return_type_map.clear();

        let parameters = function
            .signature
            .parameters
            .parameters
            .iter()
            .map(|parameter| {
                let id = self.next_local_id();

                self.node_to_local_map.insert(parameter.id, id);

                let unique_type = self.compute_unique_type(&parameter.ty);
                let ty = self.type_table.insert_if_absent(unique_type);

                self.local_type_map.insert(id, ty);

                HirFunctionParameter {
                    id,
                    name: parameter.name.symbol,
                    ty,
                }
            })
            .collect();

        let return_type = if let Some(ty) = &function.signature.return_type {
            let unique_type = self.compute_unique_type(ty);
            self.type_table.insert_if_absent(unique_type)
        } else {
            self.type_table.get_primitive(PrimitiveKind::Unit)
        };

        let body = self.type_check_block(&function.body);

        for return_point in &self.return_points {
            let ty = self
                .return_type_map
                .get(return_point)
                .expect("All return points should have an associated type in the map");

            if *ty != return_type {
                let span = *self
                    .return_span_map
                    .get(return_point)
                    .expect("All return points should have an associated span in the map");

                self.report_error(span, "Function return type does not match it's signature")
            }
        }

        if body.return_type != return_type {
            let span = if let Some(last) = function.body.statements.last() {
                last.span
            } else {
                function.body.span
            };

            self.report_error(span, "Function return type does not match it's signature")
        }

        HirFunctionDefinition {
            name: function.signature.name.symbol,
            parameters,
            return_type,
            body,
        }
    }

    fn type_check_block(&mut self, block: &Block) -> HirBlock {
        // We need to type check all the contained statements and determine the
        // return type of the block

        let statements: Vec<_> = block
            .statements
            .iter()
            .flat_map(|statement| self.type_check_statement(statement))
            .collect();

        // If there is no last statement, the block is empty and the return type
        // is unit
        let return_type = statements
            .last()
            .and_then(|statement| {
                // It's not enough to check the type of the last statement. The
                // last statement needs to have been a bare-expression (locals,
                // semi-expressions, and empty expressions are all invalid and
                // cause the block to have no return type)

                let StatementKind::BareExpr(_) = block.statements.last().unwrap().kind else {
                    return None;
                };

                let HirStatement::Expression(expression) = statement else {
                    unreachable!(
                        "BareExpr AST statement was not turned into Expression HIR statement"
                    );
                };

                Some(expression.ty)
            })
            .unwrap_or_else(|| self.type_table.get_primitive(PrimitiveKind::Unit));

        HirBlock {
            statements,
            return_type,
        }
    }

    /// Empty statements are filtered out and return None
    fn type_check_statement(&mut self, statement: &Statement) -> Option<HirStatement> {
        Some(match &statement.kind {
            StatementKind::Local(local) => {
                HirStatement::Local(Box::new(self.type_check_local(local)))
            }
            StatementKind::BareExpr(expression) => {
                let checked_expression = self.type_check_expression(expression);

                if let HirExpressionKind::Block(_)
                | HirExpressionKind::If { .. }
                | HirExpressionKind::While { .. } = checked_expression.kind
                {
                    if checked_expression.ty != self.type_table.get_primitive(PrimitiveKind::Unit) {
                        // TODO: highlight return point
                        self.report_error(
                            expression.span,
                            "Bare block expression with non-unit return value",
                        )
                    }
                }

                HirStatement::Expression(Box::new(checked_expression))
            }
            StatementKind::SemiExpr(expression) => {
                HirStatement::Expression(Box::new(self.type_check_expression(expression)))
            }
            StatementKind::Empty => return None,
        })
    }

    fn type_check_local(&mut self, local: &Local) -> HirLocal {
        // Create a local definition ID, type check the expression if it exists,
        // calculate the type ID for the explicit type if it's present, and if
        // it is then check that the types match

        let id = self.next_local_id();
        self.node_to_local_map.insert(local.id, id);

        let explicit_type = local.ty.as_ref().map(|ty| {
            let unique_type = self.compute_unique_type(ty);
            self.type_table.insert_if_absent(unique_type)
        });

        let kind = match &local.kind {
            LocalKind::Declaration => HirLocalKind::Declaration,
            LocalKind::Initialization(expression) => {
                HirLocalKind::Initialization(Box::new(self.type_check_expression(expression)))
            }
        };

        // 4 Cases for the local type:
        //   1) Declaration and no explicit type (invalid)
        //   2) Declaration and explicit type
        //   3) Initialization and no explicit type (local takes the type of the expression)
        //   4) Initialization and explicit type (both must match)

        let ty = match &kind {
            HirLocalKind::Declaration => explicit_type.unwrap_or_else(|| {
                self.report_error(local.span, "Local declaration is missing an explicit type")
            }),
            HirLocalKind::Initialization(expression) => {
                if let Some(explicit_type) = explicit_type {
                    if explicit_type != expression.ty {
                        let init_type = self.type_table.get(expression.ty);
                        let explicit_type = self.type_table.get(explicit_type);

                        self.report_error(
                            local.span,
                            &format!("Local variable initializer of type {init_type} does not match explicit type {explicit_type}"),
                        );
                    }

                    explicit_type
                } else {
                    expression.ty
                }
            }
        };

        self.local_type_map.insert(id, ty);

        HirLocal {
            id,
            name: local.name.symbol,
            is_mutable: local.is_mutable,
            ty,
            kind,
        }
    }

    fn type_check_expression(&mut self, expression: &Expression) -> HirExpression {
        match &expression.kind {
            ExpressionKind::Literal(literal) => {
                let (ty, literal) = self.type_check_literal(literal);

                HirExpression {
                    ty,
                    kind: HirExpressionKind::Literal(Box::new(literal)),
                }
            }
            ExpressionKind::QualifiedIdentifier(qualified_ident) => {
                // Either a local definition or an external definition

                let value_name_resolution = self
                    .resolution_map
                    .value_name_resolutions
                    .get(&qualified_ident.id)
                    .expect("Failed to retrieve value name resolution (this should never happen)");

                match value_name_resolution {
                    ValueNameResolution::Local(node_id)
                    | ValueNameResolution::Parameter(node_id) => {
                        let local_def_id = *self
                            .node_to_local_map
                            .get(node_id)
                            .expect("Nodes that reference local definitions should be in the map");

                        let ty = *self
                            .local_type_map
                            .get(&local_def_id)
                            .expect("Local definitions should be in the local type map");

                        HirExpression {
                            ty,
                            kind: HirExpressionKind::LocalDefinition(local_def_id),
                        }
                    }
                    ValueNameResolution::Definition(kind, id) => match kind {
                        ValueDefinitionKind::Function => {
                            let ty = *self
                                .function_type_map
                                .get(id)
                                .expect("Function definitions should be in the function type map");

                            HirExpression {
                                ty,
                                kind: HirExpressionKind::Definition(*id),
                            }
                        }
                        ValueDefinitionKind::Constant => unimplemented!(),
                        ValueDefinitionKind::Static => unimplemented!(),
                    },
                }
            }
            ExpressionKind::Grouping(expression) => self.type_check_expression(expression),
            ExpressionKind::Block(block) => {
                let block = self.type_check_block(block);

                HirExpression {
                    ty: block.return_type,
                    kind: HirExpressionKind::Block(Box::new(block)),
                }
            }
            ExpressionKind::FunctionCall { target, arguments } => {
                // Target must be a function type and it's signature must match
                // the arguments

                /* Check the target and arguments first */

                let checked_target = self.type_check_expression(target);
                let checked_arguments: Vec<_> = arguments
                    .arguments
                    .iter()
                    .map(|a| self.type_check_expression(a))
                    .collect();

                /* Resolve the function signature */

                let unique_type = self.type_table.get(checked_target.ty);

                let UniqueType::FunctionPointer {
                    parameters,
                    return_type,
                    is_variadic,
                } = unique_type
                else {
                    self.report_error(
                        target.span,
                        &format!("Type {unique_type} is not a function"),
                    );
                };

                /* Make sure arguments match their corresponding parameters */

                if parameters.len() != checked_arguments.len() && !is_variadic {
                    self.report_error(
                        arguments.span,
                        &format!(
                            "Expected {} argument(s) but found {}",
                            parameters.len(),
                            checked_arguments.len()
                        ),
                    );
                }

                for (i, (parameter_type, argument)) in
                    parameters.iter().zip(checked_arguments.iter()).enumerate()
                {
                    let argument_type = self.type_table.get(argument.ty);

                    if parameter_type != argument_type {
                        self.report_error(
                            arguments.arguments[i].span,
                            &format!("Expected type {parameter_type} but found {argument_type}"),
                        );
                    }
                }

                /* Resolve return type */

                let ty = self
                    .type_table
                    .index_of(return_type)
                    .expect("Function return type should exist in the type table");

                HirExpression {
                    ty,
                    kind: HirExpressionKind::FunctionCall {
                        target: Box::new(checked_target),
                        arguments: checked_arguments,
                    },
                }
            }
            ExpressionKind::Binary { lhs, operator, rhs } => {
                let lhs = self.type_check_expression(lhs);
                let rhs = self.type_check_expression(rhs);

                // TODO: Allow lhs and rhs types to be different

                if lhs.ty != rhs.ty {
                    let lhs = self.type_table.get(lhs.ty);
                    let rhs = self.type_table.get(rhs.ty);

                    self.report_error(
                        expression.span,
                        &format!(
                            "Sides of binary expression have different types. Left side of binary expression is of type {} while right side is of type {}.", 
                            lhs,
                            rhs
                        ),
                    )
                }

                let ty = lhs.ty;
                let unique_type = self.type_table.get(ty);

                let UniqueType::Primitive(kind) = unique_type else {
                    self.report_error(
                        expression.span,
                        "Binary operators can only be applied to primitive types at this time",
                    )
                };

                if !kind.supports_binary_op(operator.kind) {
                    self.report_error(
                        expression.span,
                        &format!("Type {unique_type} does not support this operator"),
                    )
                }

                HirExpression {
                    ty,
                    kind: HirExpressionKind::Binary {
                        lhs: Box::new(lhs),
                        operator: operator.kind,
                        rhs: Box::new(rhs),
                    },
                }
            }
            ExpressionKind::Unary { operator, operand } => {
                let operand = self.type_check_expression(operand);

                let ty = operand.ty;
                let unique_type = self.type_table.get(ty);

                let ty = match operator.kind {
                    UnaryOperatorKind::Deref => {
                        let unique_type = self.type_table.get(ty);

                        match unique_type {
                            UniqueType::Primitive(_) => self.report_error(
                                expression.span,
                                &format!("Primitive type {unique_type} cannot be dereferenced"),
                            ),
                            UniqueType::Pointer(inner_type) =>  self.type_table.insert_if_absent(*inner_type.clone()),
                            UniqueType::Slice(_) => self.report_error(
                                expression.span,
                                &format!("Slice type {unique_type} cannot be dereferenced"),
                            ),
                            UniqueType::Str => self.report_error(
                                expression.span,
                                &format!("Type {unique_type} cannot be dereferenced"),
                            ),
                            UniqueType::CStr => self.type_table.get_primitive(PrimitiveKind::I8),
                            UniqueType::Array { ..} => self.report_error(
                                expression.span,
                                &format!("Array type {unique_type} cannot be dereferenced. Index the array or first cast an array pointer to a raw pointer type."),
                            ),
                            UniqueType::FunctionPointer {
                          ..
                            } => self.report_error(
                                expression.span,
                                "Function pointers cannot be dereferenced, only called. To read the bytes from a function definition, first cast it to a `*u8` pointer.",
                            ),
                            UniqueType::Any => self.report_error(
                                expression.span,
                                &format!("{unique_type} pointers cannot be dereferenced directly. Cast it to a defined pointer type first."),
                            ),
                        }
                    }
                    UnaryOperatorKind::AddressOf => {
                        let unique_type = self.type_table.get(ty);

                        self.type_table
                            .insert_if_absent(UniqueType::Pointer(Box::new(unique_type.clone())))
                    }
                    UnaryOperatorKind::LogicalNot
                    | UnaryOperatorKind::BitwiseNot
                    | UnaryOperatorKind::Negate => {
                        let UniqueType::Primitive(kind) = unique_type else {
                            self.report_error(
                                expression.span,
                                &format!(
                                    "The `{}` operator can only be applied to primitive types",
                                    operator.kind
                                ),
                            )
                        };

                        if !kind.supports_unary_op(operator.kind) {
                            self.report_error(
                                expression.span,
                                &format!(
                                    "Type {unique_type} does not support the `{}` operator",
                                    operator.kind
                                ),
                            )
                        }

                        ty
                    }
                };

                HirExpression {
                    ty,
                    kind: HirExpressionKind::Unary {
                        operator: operator.kind,
                        operand: Box::new(operand),
                    },
                }
            }
            ExpressionKind::Cast {
                expression: current,
                ty,
            } => {
                let checked_expression = self.type_check_expression(current);

                let target_type = self.compute_unique_type(ty);
                let type_id = self.type_table.insert_if_absent(target_type.clone());

                let UniqueType::Primitive(target_primitive) = &target_type else {
                    self.report_error(
                        ty.span,
                        &format!("Cannot cast as non-primitive type {target_type}"),
                    );
                };

                let current_type = self.type_table.get(checked_expression.ty);

                let UniqueType::Primitive(current_primitive) = current_type else {
                    self.report_error(
                        current.span,
                        &format!("Cannot cast non-primitive type {current_type} as {target_type}"),
                    );
                };

                if current_primitive != target_primitive
                    && !current_primitive.can_be_cast_to(*target_primitive)
                {
                    self.report_error(expression.span, &format!("Cast types are incompatible. Cannot cast {current_type} as {target_type}"));
                }

                HirExpression {
                    ty: type_id,
                    kind: HirExpressionKind::Cast {
                        expression: Box::new(checked_expression),
                        ty: type_id,
                    },
                }
            }
            ExpressionKind::If {
                condition,
                positive,
                negative,
            } => {
                let checked_condition = self.type_check_expression(condition);

                if checked_condition.ty != self.type_table.get_primitive(PrimitiveKind::Bool) {
                    self.report_error(condition.span, "If condition must be of type `bool`");
                }

                let positive = self.type_check_block(positive);
                let checked_negative = negative.as_ref().map(|n| self.type_check_expression(n));

                if let Some(checked_negative) = &checked_negative {
                    if positive.return_type != checked_negative.ty {
                        self.report_error(
                            negative.as_ref().unwrap().span,
                            "Types of positive and negative blocks of if statement do not match",
                        )
                    }
                }

                HirExpression {
                    ty: positive.return_type,
                    kind: HirExpressionKind::If {
                        condition: Box::new(checked_condition),
                        positive: Box::new(positive),
                        negative: checked_negative.map(Box::new),
                    },
                }
            }
            ExpressionKind::While { condition, block } => {
                let checked_condition = self.type_check_expression(condition);

                if checked_condition.ty != self.type_table.get_primitive(PrimitiveKind::Bool) {
                    self.report_error(condition.span, "While condition must be of type `bool`");
                }

                let block = self.type_check_block(block);

                HirExpression {
                    ty: block.return_type,
                    kind: HirExpressionKind::While {
                        condition: Box::new(checked_condition),
                        block: Box::new(block),
                    },
                }
            }
            ExpressionKind::Assignment { lhs, rhs } => self.type_check_assignment(lhs, rhs),
            ExpressionKind::OperatorAssignment { operator, lhs, rhs } => {
                let rhs = self.type_check_expression(rhs);
                let lhs = self.type_check_expression(lhs);

                // This operation is slightly different than the normal
                // assignment operation but boils down to the same idea.
                // Interestingly, the HIR for this expression actually turns
                // into an assignment and a binary expression.
                //
                // We need to make sure that:
                //   1) The lhs supports assignment (MUST be a local
                //      identifier (reassigns the value of the identifier), a
                //      dereference of a pointer type, (dereferences the
                //      pointer and reassigns the value), or a field access
                //      (dereferences the field and reassigns the value))
                //   2) The lhs type supports the binary operator for the
                //      rhs type (does not require that both sides are
                //      necessarily the same type)

                todo!("Type check assignment with operator")
            }
            // TODO: make sure we are inside a loop
            ExpressionKind::Break => HirExpression {
                ty: self.type_table.get_primitive(PrimitiveKind::Unit),
                kind: HirExpressionKind::Break,
            },
            // TODO: make sure we are inside a loop
            ExpressionKind::Continue => HirExpression {
                ty: self.type_table.get_primitive(PrimitiveKind::Unit),
                kind: HirExpressionKind::Continue,
            },
            ExpressionKind::Return(result) => {
                let result = dbg!(result).as_ref().map(|e| self.type_check_expression(e));
                let ty = result
                    .as_ref()
                    .map(|e| e.ty)
                    .unwrap_or_else(|| self.type_table.get_primitive(PrimitiveKind::Unit));

                self.return_points.push(expression.id);
                self.return_type_map.insert(expression.id, ty);
                self.return_span_map.insert(expression.id, expression.span);

                HirExpression {
                    ty: self.type_table.get_primitive(PrimitiveKind::Unit),
                    kind: HirExpressionKind::Return(result.map(Box::new)),
                }
            }
        }
    }

    fn type_check_assignment(&mut self, lhs: &Expression, rhs: &Expression) -> HirExpression {
        let span = Span::new(lhs.span.start, rhs.span.end);
        let lhs = self.type_check_expression(lhs);
        let rhs = self.type_check_expression(rhs);

        // We have to make sure that:
        //   1) The lhs supports assignment (MUST be a local identifier
        //      (reassigns the value of the identifier), a dereference of a
        //      pointer type, (dereferences the pointer and reassigns the
        //      value), or a field access (dereferences the field and
        //      reassigns the value))
        //   2) Both sides are the same type (if lhs is an
        //      identifier/field access, it must be the same type as the rhs.
        //      if the lhs is a pointer deref, the pointer type must be the
        //      same as the rhs)

        match lhs.kind {
            HirExpressionKind::LocalDefinition(_) => {
                if lhs.ty != rhs.ty {
                    let lhs = self.type_table.get(lhs.ty);
                    let rhs = self.type_table.get(rhs.ty);

                    self.report_error(span, &format!("Left and right side of assignment expression have incompatible types. Cannot assign type {rhs} to variable of type {lhs}."));
                }

                HirExpression {
                    ty: self.type_table.get_primitive(PrimitiveKind::Unit),
                    kind: HirExpressionKind::Assignment {
                        kind: AssignmentKind::Local,
                        lhs: Box::new(lhs),
                        rhs: Box::new(rhs),
                    },
                }
            }
            HirExpressionKind::Unary { operator, .. } => match operator {
                UnaryOperatorKind::Deref => {
                    // Type of the LHS will be the dereferenced type
                    if lhs.ty != rhs.ty {
                        let lhs = self.type_table.get(lhs.ty);
                        let rhs = self.type_table.get(rhs.ty);

                        self.report_error(span, &format!("Left and right side of assignment expression have incompatible types. Cannot assign type {rhs} to dereferenced type {lhs}."));
                    }

                    HirExpression {
                        ty: self.type_table.get_primitive(PrimitiveKind::Unit),
                        kind: HirExpressionKind::Assignment {
                            kind: AssignmentKind::Deref,
                            lhs: Box::new(lhs),
                            rhs: Box::new(rhs),
                        },
                    }
                }
                _ => self.report_error(
                    span,
                    &format!("Cannot assign a value to the result of a `{operator} operation"),
                ),
            },
            HirExpressionKind::Literal(_) => {
                self.report_error(span, "Cannot reassign the value of a literal")
            }
            HirExpressionKind::Definition(_) => {
                self.report_error(span, "Cannot reassign the value of a non-local definition")
            }
            HirExpressionKind::Block(_) => {
                self.report_error(span, "Cannot assign a value to a block expression")
            }
            HirExpressionKind::FunctionCall { .. } => {
                self.report_error(span, "Cannot assign a value to a function call expression")
            }
            HirExpressionKind::Binary { .. } => self.report_error(
                span,
                "Cannot assign a value to the result of a binary expression",
            ),
            HirExpressionKind::Cast { .. } => self.report_error(
                span,
                "Cannot assign a value to the result of a cast expression",
            ),
            HirExpressionKind::If { .. } => {
                self.report_error(span, "Cannot assign a value to an if expression")
            }
            HirExpressionKind::While { .. } => {
                self.report_error(span, "Cannot assign a value to an while expression")
            }
            HirExpressionKind::Assignment { .. } => {
                unreachable!("Assignment expressions cannot be the left hand side of other assignment expressions")
            }
            HirExpressionKind::Break => {
                self.report_error(span, "Cannot assign a value to a break expression")
            }
            HirExpressionKind::Continue => {
                self.report_error(span, "Cannot assign a value to a continue expression")
            }
            HirExpressionKind::Return(_) => {
                self.report_error(span, "Cannot assign a value to a return expression")
            }
        }
    }

    /// Parses the contents of a literal and determines the type
    fn type_check_literal(&mut self, literal: &Literal) -> (TypeId, HirLiteral) {
        // TODO: allow type inference if a suffix isn't explicitly specified for
        // integer and float types

        let value = literal.symbol.value();

        match literal.kind {
            LiteralKind::Boolean => {
                let value = match value {
                    "true" => true,
                    "false" => false,
                    _ => unreachable!(),
                };

                (
                    self.type_table.get_primitive(PrimitiveKind::Bool),
                    HirLiteral::Boolean(value),
                )
            }
            LiteralKind::Byte => todo!(),
            LiteralKind::Char => {
                // Chop the single quotes off the ends of the char
                let Ok(value) = value[1..value.len() - 1].parse() else {
                    self.report_error(literal.span, "Failed to parse malformed char literal")
                };

                (
                    self.type_table.get_primitive(PrimitiveKind::Char),
                    HirLiteral::Char(value),
                )
            }
            LiteralKind::Integer => {
                // The lexer guarantees everything about the value of the symbol
                // besides the integer fitting into the limit for it's type.
                // Therefore we can ignore the other parsing error variants as
                // they are impossible
                let value: u64 = match value.parse() {
                    Ok(value) => value,
                    Err(e) => match e.kind() {
                        IntErrorKind::PosOverflow => {
                            self.report_error(literal.span, "Integer is too large for it's type")
                        }
                        _ => unreachable!(),
                    },
                };

                (
                    self.type_table.get_primitive(PrimitiveKind::I32),
                    HirLiteral::Integer(value),
                )
            }
            LiteralKind::Float => {
                // The lexer guarantees everything about the value of the symbol
                // besides the float fitting into the limit for it's type.
                // Therefore any error generated in parsing the float literal
                // must be because of that.
                let Ok(value) = value.parse() else {
                    self.report_error(literal.span, "Float is too large for it's type")
                };

                (
                    self.type_table.get_primitive(PrimitiveKind::F64),
                    HirLiteral::Float64(value),
                )
            }
            LiteralKind::String => {
                // Chop the quotes off the ends of the string
                let value = InternedSymbol::new(&value[1..value.len() - 1]);

                (
                    self.type_table.insert_if_absent(UniqueType::Str),
                    HirLiteral::String(value),
                )
            }
            LiteralKind::ByteString => todo!(),
            LiteralKind::CString => todo!(),
        }
    }
}

/// Represents a reference to a previously defined variable binding in the
/// current function's scope
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct LocalDefinitionId(pub u32);

/// Represents a reference to a unique type within the type table
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct TypeId(u32);

impl TypeId {
    pub fn as_index(&self) -> usize {
        self.0 as usize
    }
}

/// A table for storing unique types.
///
/// Any 2 types which are completely equivalent will resolve to the same TypeId
/// which also acts as an index into the table
#[derive(Debug)]
pub struct TypeTable {
    types: Vec<UniqueType>,
}

impl TypeTable {
    fn new() -> Self {
        let mut types = Vec::new();

        for kind in PrimitiveKind::iter() {
            types.push(UniqueType::Primitive(kind))
        }

        Self { types }
    }

    pub fn get_primitive(&self, kind: PrimitiveKind) -> TypeId {
        self.index_of(&UniqueType::Primitive(kind))
            .expect("All primitives should exist in the type table")
    }

    pub fn get(&self, type_id: TypeId) -> &UniqueType {
        self.types.get(type_id.as_index()).expect("All TypeIds should exist within the type table since thats the only way to construct them")
    }

    pub fn insert_if_absent(&mut self, ty: UniqueType) -> TypeId {
        if let Some(index) = self.index_of(&ty) {
            return index;
        }

        self.types.push(ty);

        TypeId(self.types.len() as u32 - 1)
    }

    pub fn index_of(&self, ty: &UniqueType) -> Option<TypeId> {
        self.types
            .iter()
            .position(|t| t == ty)
            .map(|i| TypeId(i as u32))
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum UniqueType {
    Primitive(PrimitiveKind),
    Pointer(Box<UniqueType>),
    Slice(Box<UniqueType>),
    Str,
    CStr,
    Array {
        ty: Box<UniqueType>,
        length: usize,
    },
    FunctionPointer {
        parameters: Vec<UniqueType>,
        return_type: Box<UniqueType>,
        is_variadic: bool,
    },
    Any,
}

impl core::fmt::Display for UniqueType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            UniqueType::Primitive(kind) => write!(f, "{kind}"),
            UniqueType::Pointer(ty) => write!(f, "*{ty}"),
            UniqueType::Slice(ty) => write!(f, "[{ty}]"),
            UniqueType::Str => write!(f, "str"),
            UniqueType::CStr => write!(f, "cstr"),
            UniqueType::Array { ty, length } => write!(f, "[{ty}; {length}]"),
            UniqueType::FunctionPointer { .. } => todo!("Format function pointers"),
            UniqueType::Any => write!(f, "*any"),
        }
    }
}
