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

use hashbrown::HashSet;
use ty::{FloatVariableId, IntVariableId, Type, TypeKind};

use super::{
    hir::{self, Module, OwnerNode},
    primitive::{PrimitiveKind, UIntKind},
};
use crate::index::Index;

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

    /// Stores what types we've assigned to HIR nodes so far. We use an
    /// Rc<RefCell<Type>> so that once we determine the type of a variable
    /// through inference, we can update all references to that type.
    node_to_type_map: BTreeMap<hir::ItemLocalId, Rc<RefCell<Type>>>,

    next_integer_variable_id: IntVariableId,
    next_float_variable_id: FloatVariableId,
}

impl<'tcx, 'hir> BodyTypeChecker<'tcx, 'hir> {
    fn insert_type(&mut self, hir_id: hir::HirId, ty: Type) -> Rc<RefCell<Type>> {
        assert_eq!(hir_id.owner, self.owner_id);

        let ty = Rc::new(RefCell::new(ty));
        self.node_to_type_map.insert(hir_id.local_id, ty.clone());
        ty
    }

    fn copy_type_from(
        &mut self,
        dest_id: hir::HirId,
        src_id: impl Into<hir::ItemLocalId>,
    ) -> Rc<RefCell<Type>> {
        assert_eq!(dest_id.owner, self.owner_id);

        let shared = self.node_to_type_map[&src_id.into()].clone();
        self.node_to_type_map
            .insert(dest_id.local_id, shared.clone());
        shared
    }

    fn get_type(&mut self, id: impl Into<hir::ItemLocalId>) -> Rc<RefCell<Type>> {
        self.node_to_type_map[&id.into()].clone()
    }

    fn next_integer_id(&mut self) -> IntVariableId {
        let id = self.next_integer_variable_id;
        self.next_integer_variable_id.increment_by(1);
        id
    }

    fn next_float_id(&mut self) -> FloatVariableId {
        let id = self.next_float_variable_id;
        self.next_float_variable_id.increment_by(1);
        id
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
                hir::LiteralIntegerKind::Unsuffixed => {
                    let id = self.next_integer_id();
                    self.type_context
                        .intern_type(TypeKind::Infer(ty::TypeVariable::Int(id)))
                }
            },
            hir::Literal::Float(_, literal_float_kind) => match literal_float_kind {
                hir::LiteralFloatKind::Suffixed(float_kind) => self
                    .type_context
                    .get_primitive_type(PrimitiveKind::Float(*float_kind)),
                hir::LiteralFloatKind::Unsuffixed => {
                    let id = self.next_float_id();
                    self.type_context
                        .intern_type(TypeKind::Infer(ty::TypeVariable::Float(id)))
                }
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
        //   4)    type with initializer -> assign type to binding + recoverable error if initializer does not match

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
                // This is a "type boundary" since we have both a known concrete
                // type and a potentially inferred type that have to compare equal

                // 3 cases:
                //   1) both types are the same -> assign either to the let stmt
                //   2) initializer is can be inferred into the explicit type -> update initializer and assign explicit type to let stmt
                //   3) initializer can't be inferred into the explicit type -> throw a recoverable error

                let e = explicit.borrow().clone();
                let i = initializer.borrow().clone();

                if e == i {
                    // Don't need to do anything here
                } else if i.can_infer_into(&e) {
                    // Replace the initializer type with the explicit type
                    let mut i = initializer.borrow_mut();
                    *i = e;
                } else {
                    todo!("report error")
                }

                self.node_to_type_map
                    .insert(let_stmt.hir_id.local_id, explicit);
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
                hir::Resolution::IntrinsicFunction => todo!("resolve type of intrinsic function"),
                _ => unreachable!("encountered type resolution in value namespace"),
            },
            hir::ExpressionKind::Block(block) => {
                self.copy_type_from(expression.hir_id, block.hir_id);

                // TODO: check that bare expressions in the middle of the block
                // have a unit return type. put this in visit_block?
            }
            hir::ExpressionKind::FunctionCall { target, arguments } => todo!(),
            hir::ExpressionKind::Binary { lhs, operator, rhs } => todo!(),
            hir::ExpressionKind::Unary { operator, operand } => todo!(),
            hir::ExpressionKind::Cast { expression, ty } => todo!(),
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
                let ty = self.type_context.get_primitive_type(PrimitiveKind::Never);
                self.insert_type(expression.hir_id, ty);
            }
        }
    }
}

pub fn type_check_module(module: &hir::Module) {
    let mut ctx = TypeContext::new(module);

    // Compute types for top level items we might reference in body contexts
    let mut global_indexer = GlobalTypeEnvironmentIndexer {
        type_context: &mut ctx,
    };
    hir::visit::walk_module(&mut global_indexer, module);

    // Check the content of bodies and assign types to all nodes
    for owner_id in module.get_owners() {
        let mut body_ctx = BodyTypeChecker {
            type_context: &mut ctx,
            owner_id,
            node_to_type_map: BTreeMap::new(),
            next_integer_variable_id: IntVariableId::new(0),
            next_float_variable_id: FloatVariableId::new(0),
        };

        let OwnerNode::Item(item) = module.get_owner(owner_id).node();
        hir::visit::walk_item(&mut body_ctx, item);
    }
}
