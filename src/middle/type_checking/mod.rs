//! Drip Type Checker
//!
//! Type checking the HIR has 2 main components:
//!
//!   1) analyzing type definitions and function signatures to build up a typing
//!      environment
//!   2) type checking all the executable bodies in the HIR to make sure they
//!      comply with our type system's rules
//!   
//! The first step is fairly strait-forward since its mostly get collecting
//! information. The second step is more involved and can be further broken down
//! into 2 more main steps:
//!
//!   1) traversing the body, assigning type variables to HIR nodes and
//!      collecting inference constraints
//!   2) solving the collected constraints and substituting types in the HIR
//!      until we either catch a type error or all constraints are satisfied
//!      and no more free type variables exist
//!
//! After we have verified that our program is type safe, we should no longer
//! report any errors since the input source code has been fully validated. From
//! there, the next step is to use the computed types to lower the HIR to LIR.

use std::{cell::RefCell, collections::BTreeMap, rc::Rc};

use hashbrown::{HashMap, HashSet};
use ty::{FloatVariableId, IntVariableId, Type, TypeKind};

use super::{
    hir::{self, Module, OwnerNode},
    primitive::{PrimitiveKind, UIntKind},
};
use crate::{
    frontend::lexer::Span,
    index::Index,
    middle::{
        hir::{HirId, LocalDefId},
        type_checking::ty::TypeVariable,
    },
};

pub mod ty;

#[derive(Debug)]
struct TypeContext<'hir> {
    /// Module we are type checking
    module: &'hir hir::Module,
    /// Type interning table to prevent duplicate types
    type_table: HashSet<Rc<TypeKind>>,

    /// Stores the computed types of top level items in the module
    def_id_to_type_map: BTreeMap<hir::LocalDefId, Type>,
}

impl<'hir> TypeContext<'hir> {
    fn new(module: &'hir Module) -> Self {
        Self {
            module,
            type_table: HashSet::new(),
            def_id_to_type_map: BTreeMap::new(),
        }
    }

    fn compute_hir_type(&mut self, ty: Rc<hir::Type>) -> Type {
        match &ty.kind {
            hir::TypeKind::Path(path) => match path.resolution() {
                hir::Resolution::Definition(_definition_kind, local_def_id) => {
                    let owner = &self.module.owners[*local_def_id];
                    todo!("compute user defined types")
                }
                hir::Resolution::Primitive(primitive_kind) => {
                    self.get_primitive_type(*primitive_kind)
                }
                _ => unreachable!("encountered value resolution in type namespace"),
            },
            hir::TypeKind::Pointer(ty) => {
                let inner = self.compute_hir_type(ty.clone());
                self.intern_type(TypeKind::Pointer(inner))
            }
            hir::TypeKind::Slice(ty) => {
                let inner = self.compute_hir_type(ty.clone());
                self.intern_type(TypeKind::Slice(inner))
            }
            hir::TypeKind::Array { ty, length } => {
                let inner = self.compute_hir_type(ty.clone());
                self.intern_type(TypeKind::Array {
                    ty: inner,
                    length: *length,
                })
            }
            hir::TypeKind::FunctionPointer {
                parameters,
                return_type,
                is_variadic,
            } => {
                let parameters = parameters
                    .iter()
                    .map(|ty| self.compute_hir_type(ty.clone()))
                    .collect();

                let return_type = return_type
                    .as_ref()
                    .map(|ty| self.compute_hir_type(ty.clone()))
                    .unwrap_or_else(|| self.get_unit_type());

                self.intern_type(TypeKind::FunctionPointer {
                    parameters,
                    return_type,
                    is_variadic: *is_variadic,
                })
            }
            hir::TypeKind::Any => self.intern_type(TypeKind::Any),
        }
    }
}

/// Traverses the top level items in a module and computes their types, adding
/// them to a type resolution map
#[derive(Debug)]
struct GlobalTypeEnvironmentIndexer<'tcx, 'hir> {
    type_context: &'tcx mut TypeContext<'hir>,
}

impl<'tcx, 'hir> GlobalTypeEnvironmentIndexer<'tcx, 'hir> {
    fn compute_type_for_function_signature(&mut self, signature: &hir::FunctionSignature) -> Type {
        let parameters = signature
            .parameters
            .iter()
            .map(|ty| self.type_context.compute_hir_type(ty.clone()))
            .collect();

        let return_type = signature
            .return_type
            .as_ref()
            .map(|ty| self.type_context.compute_hir_type(ty.clone()))
            .unwrap_or_else(|| self.type_context.get_unit_type());

        self.type_context.intern_type(TypeKind::FunctionPointer {
            parameters,
            return_type,
            is_variadic: signature.variadic_type.is_some(),
        })
    }
}

impl<'tcx, 'hir> hir::visit::Visitor for GlobalTypeEnvironmentIndexer<'tcx, 'hir> {
    fn visit_item(&mut self, item: Rc<hir::Item>) {
        match &item.kind {
            hir::ItemKind::Function { signature, .. } => {
                let ty = self.compute_type_for_function_signature(signature);
                self.type_context
                    .def_id_to_type_map
                    .insert(item.owner_id, ty);
            }
        }
    }
}

/// The context associated with type checking an individual executable body
struct BodyTypeChecker<'tcx, 'hir> {
    type_context: &'tcx mut TypeContext<'hir>,
    owner_id: hir::LocalDefId,

    /// Stores what types we've assigned to HIR nodes so far. This is
    /// effectively the type environment Γ from type theory just without using
    /// the names directlt (resolved during ast lowering)
    node_to_type_map: BTreeMap<hir::ItemLocalId, Type>,

    /// A list of accumulated constraints on the existing free type variables
    constraints: Vec<TypeConstraint>,

    next_integer_variable_id: IntVariableId,
    next_float_variable_id: FloatVariableId,
}

#[derive(Debug)]
struct TypeConstraint {
    left: Type,
    right: Type,
    origin: TypeConstraintOrigin,
}

#[derive(Debug)]
struct TypeConstraintOrigin {
    /// The span enclosing the entire node which generated the constraint in the
    /// original traversal
    span: Span,
    /// Used to format error messages better
    kind: TypeBoundary,
}

/// A kind of place in the source code where a constraint may be generated
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum TypeBoundary {
    /// If an explicit type is specified for a let binding, the expression must
    /// have that type
    LetStatement,
    /// Function argument type must match function paramter type
    FunctionArgument,
    /// Cast operand must match target type
    Cast,
    /// If conditions must be the bool type
    IfCondition,
    /// Blocks of an if statement must have the same type
    IfBlock,
    /// While conditions must be the bool type
    WhileCondition,
    /// Bare expressions in a block which are not the last in the block must
    /// have be unit type
    BareExpression,
    /// Sides of binary op must have the same type
    BinaryOp,
    /// Sides of assignment must have the same type
    Assignment,
    /// Sides of op assignment must have the same type
    OpAssignment,
}

impl<'tcx, 'hir> BodyTypeChecker<'tcx, 'hir> {
    fn insert_type(&mut self, hir_id: hir::HirId, ty: Type) -> Type {
        assert_eq!(hir_id.owner, self.owner_id);

        self.node_to_type_map.insert(hir_id.local_id, ty.clone());
        ty
    }

    fn copy_type_from(&mut self, dest_id: hir::HirId, src_id: impl Into<hir::ItemLocalId>) -> Type {
        assert_eq!(dest_id.owner, self.owner_id);

        let shared = self.node_to_type_map[&src_id.into()].clone();
        self.node_to_type_map
            .insert(dest_id.local_id, shared.clone());
        shared
    }

    fn get_type(&mut self, id: impl Into<hir::ItemLocalId>) -> Type {
        self.node_to_type_map[&id.into()].clone()
    }

    /// Adds a constraint that the left type should equal the right type
    fn create_type_constraint(&mut self, left: Type, right: Type, origin: TypeConstraintOrigin) {
        self.constraints.push(TypeConstraint {
            left,
            right,
            origin,
        });
    }

    fn create_fresh_integer_var(&mut self) -> Type {
        let id = self.next_integer_variable_id;
        self.next_integer_variable_id.increment_by(1);

        self.type_context
            .intern_type(TypeKind::Infer(TypeVariable::Int(id)))
    }

    fn create_fresh_float_var(&mut self) -> Type {
        let id = self.next_float_variable_id;
        self.next_float_variable_id.increment_by(1);

        self.type_context
            .intern_type(TypeKind::Infer(TypeVariable::Float(id)))
    }

    fn compute_type_for_literal(&mut self, literal: &hir::Literal) -> Type {
        match literal {
            hir::Literal::Boolean(_) => self.type_context.get_primitive_type(PrimitiveKind::Bool),
            hir::Literal::Char(_) => self.type_context.get_primitive_type(PrimitiveKind::Char),
            hir::Literal::Integer(_, literal_integer_kind) => match literal_integer_kind {
                hir::LiteralIntegerKind::Unsigned(uint_kind) => self
                    .type_context
                    .get_primitive_type(PrimitiveKind::UInt(*uint_kind)),
                hir::LiteralIntegerKind::Signed(int_kind) => self
                    .type_context
                    .get_primitive_type(PrimitiveKind::Int(*int_kind)),
                hir::LiteralIntegerKind::Unsuffixed => self.create_fresh_integer_var(),
            },
            hir::Literal::Float(_, literal_float_kind) => match literal_float_kind {
                hir::LiteralFloatKind::Suffixed(float_kind) => self
                    .type_context
                    .get_primitive_type(PrimitiveKind::Float(*float_kind)),
                hir::LiteralFloatKind::Unsuffixed => self.create_fresh_float_var(),
            },
            hir::Literal::String(_) => self.type_context.get_primitive_type(PrimitiveKind::Str),
            hir::Literal::ByteString(_) => {
                let inner = self
                    .type_context
                    .get_primitive_type(PrimitiveKind::UInt(UIntKind::U8));
                self.type_context.intern_type(TypeKind::Slice(inner))
            }
            hir::Literal::CString(_) => self.type_context.get_primitive_type(PrimitiveKind::CStr),
        }
    }

    fn unify_constraints(&mut self) -> Result<SubstitutionMap, Vec<TypeError>> {
        let mut substitution_map = SubstitutionMap::new();
        let mut errors = vec![];

        for TypeConstraint {
            left,
            right,
            origin,
        } in core::mem::take(&mut self.constraints)
        {
            match self.unify(left, right, &mut substitution_map) {
                Ok(_) => {}
                Err(e) => errors.push(TypeError { origin, kind: e }),
            }
        }

        if errors.is_empty() {
            Ok(substitution_map)
        } else {
            Err(errors)
        }
    }

    fn unify(
        &mut self,
        t1: Type,
        t2: Type,
        substitution_map: &mut SubstitutionMap,
    ) -> Result<(), TypeErrorKind> {
        let t1 = self.apply_substitution(substitution_map, t1);
        let t2 = self.apply_substitution(substitution_map, t2);

        match (&*t1, &*t2) {
            // Both same type variable
            (TypeKind::Infer(id1), TypeKind::Infer(id2)) if id1 == id2 => Ok(()),

            // One is an integral inference type and one is an integer type
            (TypeKind::Infer(TypeVariable::Int(id)), ty @ TypeKind::Integer(_))
            | (ty @ TypeKind::Integer(_), TypeKind::Infer(TypeVariable::Int(id))) => {
                // It is guaranteed that this type is already interned, but I
                // cant figure out a nicer way to write this
                let ty = self.type_context.intern_type(ty.clone());
                let variable = TypeVariable::Int(*id);

                if self.occurs_in(variable, ty.clone(), substitution_map) {
                    return Err(TypeErrorKind::InfinitelyRecursiveType { variable, ty });
                }

                substitution_map.int_map.insert(*id, ty);
                Ok(())
            }

            // One is a float inference type and one is an float type
            (TypeKind::Infer(TypeVariable::Float(id)), ty @ TypeKind::Float(_))
            | (ty @ TypeKind::Float(_), TypeKind::Infer(TypeVariable::Float(id))) => {
                // It is guaranteed that this type is already interned, but I
                // cant figure out a nicer way to write this
                let ty = self.type_context.intern_type(ty.clone());
                let variable = TypeVariable::Float(*id);

                if self.occurs_in(variable, ty.clone(), substitution_map) {
                    return Err(TypeErrorKind::InfinitelyRecursiveType { variable, ty });
                }

                substitution_map.float_map.insert(*id, ty);
                Ok(())
            }

            // Both same concrete type
            (t1, t2) if t1 == t2 => Ok(()),

            // Any other type combination
            _ => Err(TypeErrorKind::Mismatch {
                expected: t1,
                actual: t2,
            }),
        }
    }

    fn occurs_in(
        &mut self,
        var: TypeVariable,
        ty: Type,
        substitution_map: &SubstitutionMap,
    ) -> bool {
        match &*self.apply_substitution(substitution_map, ty) {
            TypeKind::Infer(id) => *id == var,
            TypeKind::Pointer(inner)
            | TypeKind::Slice(inner)
            | TypeKind::Array { ty: inner, .. } => {
                self.occurs_in(var, inner.clone(), substitution_map)
            }
            TypeKind::FunctionPointer {
                parameters,
                return_type,
                ..
            } => {
                parameters
                    .iter()
                    .any(|ty| self.occurs_in(var, ty.clone(), substitution_map))
                    || self.occurs_in(var, return_type.clone(), substitution_map)
            }
            _ => false,
        }
    }

    /// Recursively applies substitutions to the provided type to generate a new
    /// type with less or ideally no type variables
    fn apply_substitution(&mut self, substitution_map: &SubstitutionMap, ty: Type) -> Type {
        match &*ty {
            TypeKind::Infer(TypeVariable::Int(id)) => {
                if let Some(t) = substitution_map.int_map.get(id) {
                    self.apply_substitution(substitution_map, t.clone())
                } else {
                    ty
                }
            }
            TypeKind::Infer(TypeVariable::Float(id)) => {
                if let Some(t) = substitution_map.float_map.get(id) {
                    self.apply_substitution(substitution_map, t.clone())
                } else {
                    ty
                }
            }
            TypeKind::Pointer(inner) => {
                let substituted = self.apply_substitution(substitution_map, inner.clone());
                self.type_context
                    .intern_type(TypeKind::Pointer(substituted))
            }
            TypeKind::Slice(inner) => {
                let substituted = self.apply_substitution(substitution_map, inner.clone());
                self.type_context.intern_type(TypeKind::Slice(substituted))
            }
            TypeKind::Array { ty: inner, length } => {
                let substituted = self.apply_substitution(substitution_map, inner.clone());
                self.type_context.intern_type(TypeKind::Array {
                    ty: substituted,
                    length: *length,
                })
            }
            TypeKind::FunctionPointer {
                parameters,
                return_type,
                is_variadic,
            } => {
                let parameters = parameters
                    .iter()
                    .map(|ty| self.apply_substitution(substitution_map, ty.clone()))
                    .collect();
                let return_type = self.apply_substitution(substitution_map, return_type.clone());

                self.type_context.intern_type(TypeKind::FunctionPointer {
                    parameters,
                    return_type,
                    is_variadic: *is_variadic,
                })
            }
            _ => ty,
        }
    }

    /// Attempts to solve type constraints, returning type check results if it
    /// was able to do so successfully
    pub fn into_output(mut self) -> Result<TypeCheckResults, Vec<TypeError>> {
        // Solve the collected constraints
        let substitution_map = self.unify_constraints()?;

        // FIXME: we could optimize this by first only applying substitutions to
        // the set of unique types, create a map of the resulting substitutions,
        // and then apply those computed recursive substitutions to all the
        // types in the node type map.

        // Apply all the substitutions we calcualted to all the nodes in the type
        let mut node_types = core::mem::take(&mut self.node_to_type_map);

        for ty in node_types.values_mut() {
            *ty = self.apply_substitution(&substitution_map, ty.clone());
        }

        // TODO: assert that no more type variables exist in the resulting
        // type, or apply default substitutions like i32 for integers and
        // f32 for floats. we could do this by collecting the remaining free
        // type variables and creating a new substitution map with default
        // substitutions and then applying that again to all the types or only
        // the types we know are still unconstrained

        Ok(TypeCheckResults {
            owner_id: self.owner_id,
            node_types,
        })
    }
}

struct SubstitutionMap {
    int_map: HashMap<IntVariableId, Type>,
    float_map: HashMap<FloatVariableId, Type>,
}

impl SubstitutionMap {
    fn new() -> Self {
        Self {
            int_map: HashMap::new(),
            float_map: HashMap::new(),
        }
    }
}

#[derive(Debug)]
struct TypeError {
    origin: TypeConstraintOrigin,
    kind: TypeErrorKind,
}

#[derive(Debug)]
enum TypeErrorKind {
    /// The expected type did not match the actual type we found in that
    /// position (semantics depend a lot on the constraint origin which caused
    /// this error)
    Mismatch { expected: Type, actual: Type },
    /// A type variable whose type contains itself. Not sure if this is actually
    /// possible to happen in our type system, but maybe it could happen in the
    /// future depending on the features we add so its good to implement it
    /// early on
    InfinitelyRecursiveType { variable: TypeVariable, ty: Type },
}

impl<'tcx, 'hir> hir::visit::Visitor for BodyTypeChecker<'tcx, 'hir> {
    /// Bind the types for function parameters
    fn visit_function_definition(
        &mut self,
        _name: &hir::Identifier,
        signature: &hir::FunctionSignature,
        body: hir::BodyId,
    ) {
        hir::visit::walk_function_signature(self, signature);

        let body = self.type_context.module.get_body(body);
        for (name, ty) in body.params.iter().zip(signature.parameters.iter()) {
            self.copy_type_from(name.hir_id, ty.hir_id);
        }

        hir::visit::walk_body(self, body);
    }

    /// Precompute types in function parameters and local bindings
    fn visit_type(&mut self, ty: Rc<hir::Type>) {
        let computed_ty = self.type_context.compute_hir_type(ty.clone());
        self.insert_type(ty.hir_id, computed_ty);
    }

    fn visit_let_statement(&mut self, let_stmt: Rc<hir::LetStatement>) {
        // 4 cases:
        //   1) no type no   initializer -> recoverable error
        //   2)    type no   initializer -> assign type to binding
        //   3) no type with initializer -> assign initializer type to binding
        //   4)    type with initializer -> assign type to binding + add constraint on initializer

        hir::visit::walk_let_statement(self, let_stmt.clone());

        // Compute and insert the explicit type
        let explicit_type = let_stmt.ty.as_ref().map(|ty| self.get_type(ty.hir_id));

        // Determine the type of the RHS expression
        let initializer_type = let_stmt
            .initializer
            .as_ref()
            .map(|init| self.get_type(init.hir_id));

        // Assign the type of the let based on the combination of explicit type
        // and initializer type using the rules we defined above
        match (explicit_type, initializer_type) {
            (None, None) => todo!("report this as an error"),
            (None, Some(initializer)) => {
                self.node_to_type_map
                    .insert(let_stmt.hir_id.local_id, initializer);
            }
            (Some(explicit), None) => {
                self.node_to_type_map
                    .insert(let_stmt.hir_id.local_id, explicit);
            }
            (Some(explicit), Some(initializer)) => {
                self.create_type_constraint(
                    explicit.clone(),
                    initializer,
                    TypeConstraintOrigin {
                        span: let_stmt.span,
                        kind: TypeBoundary::LetStatement,
                    },
                );
                self.insert_type(let_stmt.hir_id, explicit);
            }
        }
    }

    fn visit_expression(&mut self, expression: Rc<hir::Expression>) {
        hir::visit::walk_expression(self, expression.clone());

        match &expression.kind {
            hir::ExpressionKind::Literal(literal) => {
                let ty = self.compute_type_for_literal(literal);
                self.insert_type(expression.hir_id, ty);
            }
            hir::ExpressionKind::Path(path) => match path.resolution() {
                hir::Resolution::Definition(_, def_id) => {
                    let ty = self.type_context.def_id_to_type_map[def_id].clone();
                    self.insert_type(expression.hir_id, ty);
                }
                hir::Resolution::Local(local_id) => {
                    self.copy_type_from(expression.hir_id, *local_id);
                }
                hir::Resolution::IntrinsicFunction => {
                    let ty = match path.segments.last().unwrap().identifier.symbol.value() {
                        "println" => {
                            let unit = self.type_context.get_unit_type();
                            let string = self.type_context.get_primitive_type(PrimitiveKind::Str);

                            self.type_context.intern_type(TypeKind::FunctionPointer {
                                parameters: [string].into(),
                                return_type: unit,
                                is_variadic: true,
                            })
                        }
                        _ => unreachable!(),
                    };

                    self.insert_type(expression.hir_id, ty);
                }
                _ => unreachable!("encountered type resolution in value namespace"),
            },
            hir::ExpressionKind::Block(block) => {
                self.copy_type_from(expression.hir_id, block.hir_id);

                // TODO: check that bare expressions in the middle of the block
                // have a unit return type. put this in visit_block?
            }
            hir::ExpressionKind::FunctionCall { target, arguments } => {
                // check that the target of the call is a function pointer

                let TypeKind::FunctionPointer {
                    parameters,
                    return_type,
                    is_variadic,
                } = &*self.get_type(target.hir_id)
                else {
                    todo!(
                        "report error: function call expression requires that target type be a function pointer"
                    )
                };

                // check that argument types match the target's call signature
                for (parameter_ty, argument) in parameters.iter().zip(arguments.iter()) {
                    let argument_ty = self.get_type(argument.hir_id);

                    self.create_type_constraint(
                        parameter_ty.clone(),
                        argument_ty,
                        TypeConstraintOrigin {
                            span: argument.span,
                            kind: TypeBoundary::FunctionArgument,
                        },
                    );

                    // TODO: respect permitence of variadic arguments, but
                    // require them to be concrete types if present
                }

                // expression has the same type as the function's return type
                self.insert_type(expression.hir_id, return_type.clone());
            }
            hir::ExpressionKind::Binary { lhs, operator, rhs } => todo!(),
            hir::ExpressionKind::Unary { operator, operand } => todo!(),
            hir::ExpressionKind::Cast {
                expression: castee,
                ty,
            } => {
                let castee_ty = self.get_type(castee.hir_id);
                let target_ty = self.get_type(ty.hir_id);

                self.create_type_constraint(
                    target_ty.clone(),
                    castee_ty,
                    TypeConstraintOrigin {
                        span: expression.span,
                        kind: TypeBoundary::Cast,
                    },
                );
                self.insert_type(expression.hir_id, target_ty);
            }
            hir::ExpressionKind::If {
                condition,
                positive,
                negative,
            } => todo!(),
            hir::ExpressionKind::While { condition, block } => todo!(),
            hir::ExpressionKind::Assignment { lhs, rhs } => todo!(),
            hir::ExpressionKind::OperatorAssignment { operator, lhs, rhs } => todo!(),
            hir::ExpressionKind::Break => todo!(),
            hir::ExpressionKind::Continue => todo!(),
            hir::ExpressionKind::Return(_) => {
                // TODO: check that return type matches current body return type

                let ty = self.type_context.get_primitive_type(PrimitiveKind::Never);
                self.insert_type(expression.hir_id, ty);
            }
        }
    }
}

#[derive(Debug)]

pub struct ModuleTypeCheckResults {
    item_results: BTreeMap<hir::LocalDefId, TypeCheckResults>,
}

#[derive(Debug)]
pub struct TypeCheckResults {
    owner_id: hir::LocalDefId,
    node_types: BTreeMap<hir::ItemLocalId, Type>,
}

pub fn type_check_module(module: &hir::Module) -> ModuleTypeCheckResults {
    let mut ctx = TypeContext::new(module);

    // Compute types for top level items we might reference in body contexts
    let mut global_indexer = GlobalTypeEnvironmentIndexer {
        type_context: &mut ctx,
    };
    hir::visit::walk_module(&mut global_indexer, module);

    let mut results = ModuleTypeCheckResults {
        item_results: BTreeMap::new(),
    };

    // Check the content of bodies and assign types to all nodes
    for owner_id in module.get_owners() {
        let mut body_ctx = BodyTypeChecker {
            type_context: &mut ctx,
            owner_id,
            node_to_type_map: BTreeMap::new(),
            constraints: Vec::new(),
            next_integer_variable_id: IntVariableId::new(0),
            next_float_variable_id: FloatVariableId::new(0),
        };

        let OwnerNode::Item(item) = module.get_owner(owner_id).node();
        hir::visit::walk_item(&mut body_ctx, item);

        println!("{:#?}", body_ctx.constraints);

        match body_ctx.into_output() {
            Ok(output) => {
                results.item_results.insert(owner_id, output);
            }
            Err(errors) => {
                todo!("report errors: {errors:#?}")
            }
        }
    }

    results
}
