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

use std::{cell::OnceCell, collections::BTreeMap, rc::Rc};

use colored::Colorize;
use hashbrown::{HashMap, HashSet};

use super::{
    hir::{self, Module, OwnerNode},
    primitive::{PrimitiveKind, UIntKind},
};
use crate::{
    frontend::{
        SourceFile,
        ast::{AssignmentOperatorClass, BinaryOperatorClass, UnaryOperatorKind},
        lexer::Span,
    },
    index::Index,
    middle::{
        primitive::{FloatKind, IntKind},
        ty::{FloatVariableId, IntVariableId, Type, TypeKind, TypeVariable},
    },
};

#[derive(Debug)]
struct TypeContext<'hir> {
    /// Module we are type checking
    module: &'hir hir::Module,
    /// Used for error reporting
    source_file: &'hir SourceFile,
    /// Type interning table to prevent duplicate types
    type_table: HashSet<Rc<TypeKind>>,
    /// Stores the computed types of top level items in the module
    def_id_to_type_map: BTreeMap<hir::LocalDefId, Type>,
}

impl<'hir> TypeContext<'hir> {
    fn new(module: &'hir Module, source_file: &'hir SourceFile) -> Self {
        Self {
            module,
            source_file,
            type_table: HashSet::new(),
            def_id_to_type_map: BTreeMap::new(),
        }
    }

    pub fn intern_type(&mut self, kind: TypeKind) -> Type {
        let rc = self.type_table.get_or_insert(Rc::new(kind));
        Type::new_from_reference_only_for_interning(rc.clone())
    }

    pub fn get_error_type(&mut self) -> Type {
        self.intern_type(TypeKind::Error)
    }

    pub fn get_unit_type(&mut self) -> Type {
        self.get_primitive_type(PrimitiveKind::Unit)
    }

    pub fn get_primitive_type(&mut self, primitive: PrimitiveKind) -> Type {
        match primitive {
            PrimitiveKind::Never => self.intern_type(TypeKind::Never),
            PrimitiveKind::Unit => self.intern_type(TypeKind::Unit),
            PrimitiveKind::Int(int_kind) => self.intern_type(TypeKind::Integer(int_kind)),
            PrimitiveKind::UInt(uint_kind) => {
                self.intern_type(TypeKind::UnsignedInteger(uint_kind))
            }
            PrimitiveKind::Float(float_kind) => self.intern_type(TypeKind::Float(float_kind)),
            PrimitiveKind::Bool => self.intern_type(TypeKind::Bool),
            PrimitiveKind::Char => self.intern_type(TypeKind::Char),
            PrimitiveKind::Str => self.intern_type(TypeKind::Str),
            PrimitiveKind::CStr => self.intern_type(TypeKind::CStr),
        }
    }

    fn compute_hir_type(&mut self, ty: Rc<hir::Type>) -> Type {
        match &ty.kind {
            hir::TypeKind::Path(path) => self.compute_hir_resolution_type(*path.resolution()),
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

    fn compute_hir_resolution_type(&mut self, resolution: hir::Resolution) -> Type {
        match resolution {
            hir::Resolution::Definition(_definition_kind, local_def_id) => {
                let _owner = &self.module.owners[local_def_id];
                todo!("compute user defined types")
            }
            hir::Resolution::Primitive(primitive_kind) => self.get_primitive_type(primitive_kind),
            r => unreachable!("encountered value resolution in type namespace: {r:?}"),
        }
    }

    fn report_error(&self, error: TypeError) {
        let message = match error.kind {
            TypeErrorKind::TypeMismatch { expected, actual } => match error.origin.kind {
                TypeBoundary::LetStatement => {
                    format!(
                        "let binding initializer type {actual} does not match explicit type {expected}"
                    )
                }
                TypeBoundary::FunctionArgument => {
                    format!("expected function argument to be {expected} but found {actual}")
                }
                TypeBoundary::Cast => {
                    format!("{actual} cannot be trivially cast to {expected}")
                }
                TypeBoundary::IfCondition => {
                    format!("expected if condition type to be {expected} but found {actual}")
                }
                TypeBoundary::IfBlock => {
                    format!(
                        "expected positive type of if condition {expected} to match negative type {actual}"
                    )
                }
                TypeBoundary::WhileCondition => {
                    format!("expected while condition type to be {expected} but found {actual}")
                }
                TypeBoundary::BareExpression => {
                    format!("expected bare expression type to be {expected} but found {actual}")
                }
                TypeBoundary::BinaryOp => format!(
                    "expected left-hand side of binary op {expected} to match right-hand side {actual}"
                ),
                TypeBoundary::Assignment => {
                    format!("cannot assign {actual} to variable with type {expected}")
                }
                TypeBoundary::OpAssignment => format!(
                    "cannot use {actual} in operator assignment to variable with type {expected}"
                ),
                TypeBoundary::ExplicitReturn => format!(
                    "explicit type {actual} does not match the function signature's type {expected}"
                ),
                   TypeBoundary::ImplicitReturn => format!(
                    "implicit type {actual} does not match the function signature's type {expected}"
                ),
                TypeBoundary::FunctionCall
                | TypeBoundary::Deref
                | TypeBoundary::LogicalOp
                | TypeBoundary::ArithmeticOp | TypeBoundary::LoopControlFlow  => {
                    unreachable!("these are not used with type mismatch")
                }
            },
            // TODO: use error.origin.kind for even better error reporting in some cases
            TypeErrorKind::InvalidOperation {
                attempted_usage,
                provided,
            } => match attempted_usage {
                TypeUsage::ArithmeticOperation => {
                    format!("cannot use type {provided} in an arithmetic context")
                }
                TypeUsage::LogicalOperation => {
                    format!("cannot use type {provided} in a logical context")
                }
                TypeUsage::FunctionCall => {
                    format!("cannot use type {provided} as the target of a function call")
                }
                TypeUsage::Deref => {
                    format!("type {provided} cannot be dereferenced")
                }
            },
            TypeErrorKind::InfinitelyRecursiveType { variable, ty } => {
                // I'm fairly certain that this is impossible, so if we catch it
                // in the wild then I will be impressed
                format!("type {ty} is infinitely recursive (variable = {variable:?})")
            }
            TypeErrorKind::ArgumentLengthMismatch { expected, actual } => {
                format!("expected {expected} argument(s) to this function but found {actual}")
            }
            TypeErrorKind::CannotInfer => match error.origin.kind {
                TypeBoundary::LetStatement => "cannot infer the type of this binding without an explicit type or initializer expression".to_string(),
                _ => unreachable!()
            },
            TypeErrorKind::IllegalLoopControlFlow(LoopControlFlowKind::Break) => "`break` statement can only be used within loops".to_string(),
            TypeErrorKind::IllegalLoopControlFlow(LoopControlFlowKind::Continue) => "`continue` statement can only be used within loops".to_string(),
            TypeErrorKind::MissingReturnValue { expected } => match error.origin.kind {
                TypeBoundary::ExplicitReturn =>  format!("explicit return type does not match the expected type {expected}"),
                TypeBoundary::ImplicitReturn =>  format!("expected function to return type {expected} but no implicit or explicit returns found"),
                _ => unreachable!()
            },
            TypeErrorKind::InvalidCast { from, to } => format!("non-trivial cast from {from} to {to}"),
        };

        eprintln!(
            "{}: {} {}",
            "error".red(),
            message,
            format!(
                "(at {})",
                self.source_file.format_span_position(error.origin.span),
            )
            .white()
        );
        self.source_file.highlight_span(error.origin.span);
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
struct TypeChecker<'tcx, 'hir> {
    type_context: &'tcx mut TypeContext<'hir>,
    owner_id: hir::LocalDefId,

    /// Stores what types we've assigned to HIR nodes so far. This is
    /// effectively the type environment Γ from type theory just without using
    /// the names directly (resolved during ast lowering)
    node_to_type_map: BTreeMap<hir::ItemLocalId, Type>,

    /// A list of accumulated constraints on the existing free type variables
    constraints: Vec<TypeConstraint>,
    /// Errors we've collected while type checking
    errors: Vec<TypeError>,

    /// Keeps track of whether we are in a loop context (for break and continue)
    within_loop: bool,
    return_type: OnceCell<Type>,

    next_integer_variable_id: IntVariableId,
    next_float_variable_id: FloatVariableId,
}

#[derive(Debug)]
struct TypeConstraint {
    kind: TypeConstraintKind,
    origin: TypeConstraintOrigin,
}

#[derive(Debug)]
enum TypeConstraintKind {
    Equal { left: Type, right: Type },
    Cast { from: Type, to: Type },
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
    /// Function arguments must match the expected number
    FunctionCall,
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
    /// Dereferencing can only be done on pointer types
    Deref,
    /// Cannot use non-boolean types in a logical context
    LogicalOp,
    /// Cannot use non-arithmetic types in arithmetic contexts
    ArithmeticOp,
    /// Sides of binary op must have the same type
    BinaryOp,
    /// Sides of assignment must have the same type
    Assignment,
    /// Sides of op assignment must have the same type
    OpAssignment,
    /// Break or continue statement
    LoopControlFlow,
    /// Return value type must match body return type
    ExplicitReturn,
    /// Implicit return type must match function signature type
    ImplicitReturn,
}

impl<'tcx, 'hir> TypeChecker<'tcx, 'hir> {
    fn insert_type(&mut self, hir_id: hir::HirId, ty: Type) -> Type {
        assert_eq!(hir_id.owner, self.owner_id);

        self.node_to_type_map.insert(hir_id.local_id, ty.clone());
        ty
    }

    #[track_caller]
    fn copy_type_from(&mut self, dest_id: hir::HirId, src_id: impl Into<hir::ItemLocalId>) -> Type {
        assert_eq!(dest_id.owner, self.owner_id);

        let shared = self.node_to_type_map[&src_id.into()].clone();
        self.node_to_type_map
            .insert(dest_id.local_id, shared.clone());
        shared
    }

    #[track_caller]
    fn get_type(&mut self, id: impl Into<hir::ItemLocalId>) -> Type {
        self.node_to_type_map[&id.into()].clone()
    }

    /// Adds a constraint that the left type should equal the right type
    fn add_equality_constraint(&mut self, left: Type, right: Type, origin: TypeConstraintOrigin) {
        self.constraints.push(TypeConstraint {
            kind: TypeConstraintKind::Equal { left, right },
            origin,
        });
    }

    /// Adds a constraint that `from` needs to be able to be cast to `to`
    fn add_cast_constraint(&mut self, from: Type, to: Type, origin: TypeConstraintOrigin) {
        self.constraints.push(TypeConstraint {
            kind: TypeConstraintKind::Cast { from, to },
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

    fn solve_constraints(&mut self) -> (SubstitutionMap, Vec<TypeError>) {
        let mut substitution_map = SubstitutionMap::new();
        let mut defered_casts: Vec<TypeConstraint> = vec![];
        let mut errors = vec![];

        for constraint in core::mem::take(&mut self.constraints) {
            match &constraint.kind {
                TypeConstraintKind::Equal { left, right } => {
                    if let Err(e) = self.unify(left.clone(), right.clone(), &mut substitution_map) {
                        errors.push(TypeError {
                            origin: constraint.origin,
                            kind: e,
                        })
                    }
                }
                TypeConstraintKind::Cast { from, to } => {
                    if self
                        .solve_cast(from.clone(), to.clone(), &mut substitution_map, false)
                        .is_err()
                    {
                        defered_casts.push(constraint);
                    }
                }
            }
        }

        // Do a second pass after we've done all our substitutions
        for constraint in defered_casts {
            let TypeConstraintKind::Cast { from, to } = constraint.kind else {
                unreachable!()
            };

            if let Err(e) = self.solve_cast(from, to, &mut substitution_map, true) {
                errors.push(TypeError {
                    origin: constraint.origin,
                    kind: e,
                })
            }
        }

        (substitution_map, errors)
    }

    /// Attempts to equate the provided types using our type system's inference
    /// and coersion rules.
    fn unify(
        &mut self,
        t1: Type,
        t2: Type,
        substitution_map: &mut SubstitutionMap,
    ) -> Result<(), TypeErrorKind> {
        let t1 = self.apply_substitution(substitution_map, t1);
        let t2 = self.apply_substitution(substitution_map, t2);

        match (&*t1, &*t2) {
            // Both already the same type (trivial)
            (t1, t2) if t1 == t2 => Ok(()),

            // One is an integral inference type and one is an integer type
            (TypeKind::Infer(variable), ty_kind) | (ty_kind, TypeKind::Infer(variable)) => {
                // It is guaranteed that this type is already interned, but I
                // cant figure out a nicer way to write this
                let ty = self.type_context.intern_type(ty_kind.clone());

                // This is where we define our inference coersion rules
                let coercable = match variable {
                    TypeVariable::Int(_) => ty_kind.is_integer_like(),
                    TypeVariable::Float(_) => ty_kind.is_float_like(),
                };

                if !coercable {
                    return Err(TypeErrorKind::TypeMismatch {
                        expected: t1,
                        actual: t2,
                    });
                }

                if self.occurs_in(*variable, ty.clone(), substitution_map) {
                    return Err(TypeErrorKind::InfinitelyRecursiveType {
                        variable: *variable,
                        ty,
                    });
                }

                substitution_map.insert(*variable, ty);

                Ok(())
            }

            // Any other type combination
            _ => Err(TypeErrorKind::TypeMismatch {
                expected: t1,
                actual: t2,
            }),
        }
    }

    /// Checks that `from` may be cast to `to`, potentially coercing `from` if
    /// it is a free type variable
    fn solve_cast(
        &mut self,
        from: Type,
        to: Type,
        substitution_map: &mut SubstitutionMap,
        coerce_type_variables: bool,
    ) -> Result<(), TypeErrorKind> {
        assert!(
            to.free_type_variables().is_empty(),
            "attempted to solve cast to non-concrete type: {to}"
        );

        let from = self.apply_substitution(substitution_map, from);

        match (&*from, &*to) {
            (_, TypeKind::Infer(_)) => unreachable!(),
            // Trivially possible case
            (from_kind, to_kind) if from_kind == to_kind => Ok(()),
            // If the source type is a free type variable, just coerce it into
            // the target type if allowed for the variable kind and coersion is
            // enabled
            (TypeKind::Infer(variable), ty_kind) => {
                let coercable = {
                    match variable {
                        TypeVariable::Int(_) => ty_kind.is_integer_like(),
                        TypeVariable::Float(_) => ty_kind.is_float_like(),
                    }
                };

                if coercable && coerce_type_variables {
                    substitution_map.insert(*variable, to);
                    return Ok(());
                }

                Err(TypeErrorKind::InvalidCast { from, to })
            }
            // Allow casting between any numeric types
            (
                TypeKind::Integer(_) | TypeKind::UnsignedInteger(_) | TypeKind::Float(_),
                TypeKind::Integer(_) | TypeKind::UnsignedInteger(_) | TypeKind::Float(_),
            ) => Ok(()),
            // Allow casting between integer types and bools
            (
                TypeKind::Integer(_) | TypeKind::UnsignedInteger(_) | TypeKind::Bool,
                TypeKind::Integer(_) | TypeKind::UnsignedInteger(_) | TypeKind::Bool,
            ) => Ok(()),
            (TypeKind::Char, TypeKind::UnsignedInteger(UIntKind::U32)) => Ok(()),
            // Allow pointer type hacking
            (TypeKind::Pointer(_), TypeKind::Pointer(_)) => Ok(()),
            // Anything not explicitly allowed is an error
            _ => Err(TypeErrorKind::InvalidCast { from, to }),
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
        let (substitution_map, mut errors) = self.solve_constraints();
        self.errors.append(&mut errors);

        // If we unified successfully but had other problems before, stop here
        if !self.errors.is_empty() {
            let mut errors = core::mem::take(&mut self.errors);

            // Apply substitutions on types in the collected errors to generate
            // more useful output
            for err in &mut errors {
                for ty in err.kind.get_substitutable_types_mut() {
                    *ty = self.apply_substitution(&substitution_map, ty.clone());
                }
            }

            return Err(errors);
        }

        // FIXME: we could optimize this by first only applying substitutions to
        // the set of unique types, create a map of the resulting substitutions,
        // and then apply those computed recursive substitutions to all the
        // types in the node type map.

        // Apply all the substitutions we calcualted to all the nodes in the type
        let mut node_types = core::mem::take(&mut self.node_to_type_map);

        for ty in node_types.values_mut() {
            *ty = self.apply_substitution(&substitution_map, ty.clone());
        }

        // Apply default substitutions to any remaining free type variables
        let mut default_substitutions = SubstitutionMap::new();
        let mut unconstrained_nodes = HashSet::new();

        for (id, ty) in &mut node_types {
            let free_type_variables = ty.free_type_variables();

            if free_type_variables.is_empty() {
                continue;
            }

            for ftv in free_type_variables {
                let default_ty = match ftv {
                    TypeVariable::Int(_) => self
                        .type_context
                        .get_primitive_type(PrimitiveKind::Int(IntKind::I32)),
                    TypeVariable::Float(_) => self
                        .type_context
                        .get_primitive_type(PrimitiveKind::Float(FloatKind::F32)),
                };

                default_substitutions.insert(ftv, default_ty);
            }

            unconstrained_nodes.insert(*id);
        }

        for (id, ty) in &mut node_types {
            // Simple optimization to not check nodes which we know dont have
            // any unconstrained types
            if !unconstrained_nodes.contains(id) {
                continue;
            }

            *ty = self.apply_substitution(&default_substitutions, ty.clone());
        }

        self.node_to_type_map = node_types;

        for (id, node) in self
            .type_context
            .module
            .get_owner(self.owner_id)
            .nodes
            .enumerate()
        {
            // Skip the owner node
            if id == hir::ItemLocalId::ZERO {
                continue;
            }

            assert!(
                self.node_to_type_map.contains_key(&id),
                "missing type for node {id:?} = {node:?}"
            );
            assert!(
                self.get_type(id).free_type_variables().is_empty(),
                "node {id:?} has remaining free type variables in its type"
            );
        }

        Ok(TypeCheckResults {
            owner_id: self.owner_id,
            node_types: self.node_to_type_map,
        })
    }
}

#[derive(Debug)]
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

    fn insert(&mut self, variable: TypeVariable, ty: Type) {
        match variable {
            TypeVariable::Int(id) => {
                self.int_map.insert(id, ty);
            }
            TypeVariable::Float(id) => {
                self.float_map.insert(id, ty);
            }
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
    /// this error). This only applies when we know exactly what the target type
    /// should be, not for generic requirements like "binary ops should have
    /// arithmetic types". For that, we use
    /// [`InvalidOperation`](`Self::InvalidOperation`)
    TypeMismatch {
        expected: Type,
        actual: Type,
    },
    /// The provided type does not support the operation it is used in. For
    /// example, using a str in an arithmetic expression, or using an int as the
    /// target of a function call expression.
    InvalidOperation {
        attempted_usage: TypeUsage,
        provided: Type,
    },
    /// A type variable whose type contains itself. Not sure if this is actually
    /// possible to happen in our type system, but maybe it could happen in the
    /// future depending on the features we add so its good to implement it
    /// early on
    InfinitelyRecursiveType {
        variable: TypeVariable,
        ty: Type,
    },
    ArgumentLengthMismatch {
        expected: usize,
        actual: usize,
    },
    /// Local binding declared with no explicit type and no initializer
    CannotInfer,
    /// Tried to use break or continue outside loop context
    IllegalLoopControlFlow(LoopControlFlowKind),
    /// If function's return type is not `()`, return expressions must contain a
    /// value
    MissingReturnValue {
        expected: Type,
    },
    InvalidCast {
        from: Type,
        to: Type,
    },
}

impl TypeErrorKind {
    pub fn get_substitutable_types_mut(&mut self) -> Vec<&mut Type> {
        match self {
            TypeErrorKind::TypeMismatch { expected, actual } => vec![expected, actual],
            TypeErrorKind::InvalidOperation { provided, .. } => vec![provided],
            TypeErrorKind::MissingReturnValue { expected } => vec![expected],
            TypeErrorKind::InfinitelyRecursiveType { .. }
            | TypeErrorKind::ArgumentLengthMismatch { .. }
            | TypeErrorKind::CannotInfer
            | TypeErrorKind::IllegalLoopControlFlow(_)
            | TypeErrorKind::InvalidCast { .. } => vec![],
        }
    }
}

#[derive(Debug)]
enum TypeUsage {
    ArithmeticOperation,
    LogicalOperation,
    FunctionCall,
    Deref,
}

#[derive(Debug)]
enum LoopControlFlowKind {
    Continue,
    Break,
}

impl<'tcx, 'hir> hir::visit::Visitor for TypeChecker<'tcx, 'hir> {
    /// Bind the types for function parameters
    fn visit_function_definition(
        &mut self,
        _name: &hir::Identifier,
        signature: &hir::FunctionSignature,
        body: hir::BodyId,
    ) {
        // Collect parameter types
        hir::visit::walk_function_signature(self, signature);

        // Default return type is unit if none specified
        let return_ty = if let Some(r) = &signature.return_type {
            self.get_type(r.hir_id)
        } else {
            self.type_context.get_unit_type()
        };
        self.return_type.set(return_ty.clone()).unwrap();

        // Assign types to function paramters
        let body = self.type_context.module.get_body(body);
        for (name, ty) in body.params.iter().zip(signature.parameters.iter()) {
            self.copy_type_from(name.hir_id, ty.hir_id);
        }

        // Type check the function body
        hir::visit::walk_body(self, body.clone());

        // Validate that either the implicit return type matches the expected
        // type or that there are no code paths laeading to the end of the
        // function
        if let Some(last_expr) = &body.block.expression {
            // The body's implicit return type needs to match the function's signature

            let last_expr_ty = self.get_type(last_expr.hir_id);
            self.add_equality_constraint(
                return_ty,
                last_expr_ty,
                TypeConstraintOrigin {
                    span: if let Some(e) = &body.block.expression {
                        e.span
                    } else if let Some(r) = &signature.return_type {
                        r.span
                    } else {
                        // NOTE: this should never actually happen because this
                        // constraint would never be violated with both
                        // (both default to unit in that case and the constraint is
                        // upheld), but we need to provide a span here so just use
                        // the name bc thats fine
                        Span::INVALID
                    },
                    kind: TypeBoundary::ImplicitReturn,
                },
            );
        } else if let Some(ret) = &signature.return_type {
            // If there is no implicit return and a diverging path inside the
            // function, we can never reach the end of the body and don't need
            // to generate an error

            let has_explicit_return = body.block.statements.iter().any(|stmt| {
                // Any statement that propogates a never type up from any of its
                // subexpressions must have a return somewhere within it
                match &stmt.kind {
                    hir::StatementKind::Let(let_statement) => {
                        if let Some(initializer) = &let_statement.initializer
                            && self.get_type(initializer.hir_id).is_never()
                        {
                            return true;
                        }
                    }
                    hir::StatementKind::BareExpression(expression)
                    | hir::StatementKind::SemiExpression(expression) => {
                        if self.get_type(expression.hir_id).is_never() {
                            return true;
                        }
                    }
                }

                false
            });

            if !has_explicit_return {
                self.errors.push(TypeError {
                    origin: TypeConstraintOrigin {
                        span: ret.span,
                        kind: TypeBoundary::ImplicitReturn,
                    },
                    kind: TypeErrorKind::MissingReturnValue {
                        expected: return_ty,
                    },
                });
            }
        }
    }

    /// Precompute types in function parameters and local bindings
    fn visit_type(&mut self, ty: Rc<hir::Type>) {
        hir::visit::walk_type(self, ty.clone());

        let computed_ty = self.type_context.compute_hir_type(ty.clone());
        self.insert_type(ty.hir_id, computed_ty);
    }

    fn visit_path_segment(&mut self, segment: Rc<hir::PathSegment>) {
        if let hir::Resolution::Local(local_id) = &segment.resolution {
            self.copy_type_from(segment.hir_id, *local_id);
            return;
        }

        let computed_ty = self
            .type_context
            .compute_hir_resolution_type(segment.resolution);
        self.insert_type(segment.hir_id, computed_ty);
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
            (None, None) => {
                self.errors.push(TypeError {
                    origin: TypeConstraintOrigin {
                        span: let_stmt.span,
                        kind: TypeBoundary::LetStatement,
                    },
                    kind: TypeErrorKind::CannotInfer,
                });

                let error_ty = self.type_context.get_error_type();
                self.insert_type(let_stmt.hir_id, error_ty);
            }
            (None, Some(initializer)) => {
                self.node_to_type_map
                    .insert(let_stmt.hir_id.local_id, initializer);
            }
            (Some(explicit), None) => {
                self.node_to_type_map
                    .insert(let_stmt.hir_id.local_id, explicit);
            }
            (Some(explicit), Some(initializer)) => {
                self.add_equality_constraint(
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
            }
            hir::ExpressionKind::FunctionCall { target, arguments } => {
                // check that the target of the call is a function pointer

                let target_ty = self.get_type(target.hir_id);

                let TypeKind::FunctionPointer {
                    parameters,
                    return_type,
                    is_variadic,
                } = &*target_ty
                else {
                    let err = self.type_context.get_error_type();
                    self.insert_type(expression.hir_id, err);

                    self.errors.push(TypeError {
                        origin: TypeConstraintOrigin {
                            span: target.span,
                            kind: TypeBoundary::FunctionCall,
                        },
                        kind: TypeErrorKind::InvalidOperation {
                            attempted_usage: TypeUsage::FunctionCall,
                            provided: target_ty.clone(),
                        },
                    });
                    return;
                };

                // expression has the same type as the function's return type
                self.insert_type(expression.hir_id, return_type.clone());

                // Make sure the passed number of arguments matches the expected
                // number (allowing variadics if applicable)
                if arguments.len() < parameters.len()
                    || (arguments.len() > parameters.len() && !*is_variadic)
                {
                    self.errors.push(TypeError {
                        origin: TypeConstraintOrigin {
                            span: expression.span,
                            kind: TypeBoundary::FunctionCall,
                        },
                        kind: TypeErrorKind::ArgumentLengthMismatch {
                            expected: parameters.len(),
                            actual: arguments.len(),
                        },
                    });
                    return;
                }

                // check that argument types match the target's call signature
                for (parameter_ty, argument) in parameters.iter().zip(arguments.iter()) {
                    let argument_ty = self.get_type(argument.hir_id);

                    self.add_equality_constraint(
                        parameter_ty.clone(),
                        argument_ty,
                        TypeConstraintOrigin {
                            span: argument.span,
                            kind: TypeBoundary::FunctionArgument,
                        },
                    );
                }
            }
            hir::ExpressionKind::Binary { lhs, operator, rhs } => {
                let lhs_ty = self.get_type(lhs.hir_id);
                let rhs_ty = self.get_type(rhs.hir_id);

                match operator.class() {
                    // If this is an arithmetic operator, require that both
                    // types are arithmetic
                    BinaryOperatorClass::Arithmetic => {
                        let mut error = false;

                        if !lhs_ty.is_arithmetic() {
                            error = true;

                            self.errors.push(TypeError {
                                origin: TypeConstraintOrigin {
                                    span: lhs.span,
                                    kind: TypeBoundary::BinaryOp,
                                },
                                kind: TypeErrorKind::InvalidOperation {
                                    attempted_usage: TypeUsage::ArithmeticOperation,
                                    provided: lhs_ty.clone(),
                                },
                            });
                        }

                        if !rhs_ty.is_arithmetic() {
                            error = true;

                            self.errors.push(TypeError {
                                origin: TypeConstraintOrigin {
                                    span: rhs.span,
                                    kind: TypeBoundary::BinaryOp,
                                },
                                kind: TypeErrorKind::InvalidOperation {
                                    attempted_usage: TypeUsage::ArithmeticOperation,
                                    provided: rhs_ty.clone(),
                                },
                            });
                        }

                        if error {
                            let error_ty = self.type_context.get_error_type();
                            self.insert_type(expression.hir_id, error_ty);

                            return;
                        }

                        // For arithmetic operations the result is always the same as the inputs
                        self.insert_type(expression.hir_id, lhs_ty.clone());
                    }
                    // If this is a logical operator, require that both types
                    // are bools
                    class @ (BinaryOperatorClass::Logical | BinaryOperatorClass::Equality) => {
                        let bool_ty = self.type_context.get_primitive_type(PrimitiveKind::Bool);

                        // should this be a type constraint? maybe but it seems
                        // like we can do all the logic here instead and
                        // possibly report better errors
                        if class == BinaryOperatorClass::Logical {
                            let mut error = false;

                            if !lhs_ty.is_bool() {
                                error = true;

                                self.errors.push(TypeError {
                                    origin: TypeConstraintOrigin {
                                        span: lhs.span,
                                        kind: TypeBoundary::BinaryOp,
                                    },
                                    kind: TypeErrorKind::InvalidOperation {
                                        attempted_usage: TypeUsage::LogicalOperation,
                                        provided: lhs_ty.clone(),
                                    },
                                });
                            }

                            if !rhs_ty.is_bool() {
                                error = true;

                                self.errors.push(TypeError {
                                    origin: TypeConstraintOrigin {
                                        span: rhs.span,
                                        kind: TypeBoundary::BinaryOp,
                                    },
                                    kind: TypeErrorKind::InvalidOperation {
                                        attempted_usage: TypeUsage::LogicalOperation,
                                        provided: rhs_ty.clone(),
                                    },
                                });
                            }

                            if error {
                                let error_ty = self.type_context.get_error_type();
                                self.insert_type(expression.hir_id, error_ty);

                                return;
                            }
                        }

                        // For logical operations, the result is always a
                        // boolean no matter what
                        self.insert_type(expression.hir_id, bool_ty);
                    }
                }

                // For operators like && and ||, the types need to be
                // bools. For operators like == and !=, the types need
                // to be the same. In either case we need to add this
                // equality constraint.
                self.add_equality_constraint(
                    lhs_ty.clone(),
                    rhs_ty,
                    TypeConstraintOrigin {
                        span: expression.span,
                        kind: TypeBoundary::BinaryOp,
                    },
                );
            }
            hir::ExpressionKind::Unary { operator, operand } => {
                let operand_ty = self.get_type(operand.hir_id);

                match operator {
                    UnaryOperatorKind::Deref => {
                        let TypeKind::Pointer(inner_ty) = &*operand_ty else {
                            let err = self.type_context.get_error_type();
                            self.insert_type(expression.hir_id, err);

                            self.errors.push(TypeError {
                                origin: TypeConstraintOrigin {
                                    span: expression.span,
                                    kind: TypeBoundary::Deref,
                                },
                                kind: TypeErrorKind::InvalidOperation {
                                    attempted_usage: TypeUsage::Deref,
                                    provided: operand_ty.clone(),
                                },
                            });
                            return;
                        };

                        self.insert_type(expression.hir_id, inner_ty.clone());
                    }
                    UnaryOperatorKind::AddressOf => {
                        // TODO: can all types have their address taken? this is
                        // unclear. what about error types? what about zero
                        // sized types? (rust returns 0x1 for ZSTs)

                        let pointer_ty =
                            self.type_context.intern_type(TypeKind::Pointer(operand_ty));
                        self.insert_type(expression.hir_id, pointer_ty);
                    }
                    UnaryOperatorKind::LogicalNot => {
                        if !operand_ty.is_bool() {
                            let err = self.type_context.get_error_type();
                            self.insert_type(expression.hir_id, err);

                            self.errors.push(TypeError {
                                origin: TypeConstraintOrigin {
                                    span: expression.span,
                                    kind: TypeBoundary::LogicalOp,
                                },
                                kind: TypeErrorKind::InvalidOperation {
                                    attempted_usage: TypeUsage::LogicalOperation,
                                    provided: operand_ty.clone(),
                                },
                            });
                            return;
                        }

                        self.insert_type(expression.hir_id, operand_ty);
                    }
                    UnaryOperatorKind::BitwiseNot | UnaryOperatorKind::Negate => {
                        if !operand_ty.is_arithmetic() {
                            let err = self.type_context.get_error_type();
                            self.insert_type(expression.hir_id, err);

                            self.errors.push(TypeError {
                                origin: TypeConstraintOrigin {
                                    span: expression.span,
                                    kind: TypeBoundary::ArithmeticOp,
                                },
                                kind: TypeErrorKind::InvalidOperation {
                                    attempted_usage: TypeUsage::ArithmeticOperation,
                                    provided: operand_ty.clone(),
                                },
                            });
                            return;
                        }

                        self.insert_type(expression.hir_id, operand_ty);
                    }
                }
            }
            hir::ExpressionKind::Cast {
                expression: castee,
                ty,
            } => {
                let castee_ty = self.get_type(castee.hir_id);
                let target_ty = self.get_type(ty.hir_id);

                // We know that the target type cannot have any free type
                // variables because it can only be a named concrete type. This
                // may change however if we add a "typeof" mechanism or
                // equivalent.
                self.add_cast_constraint(
                    castee_ty,
                    target_ty.clone(),
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
            } => {
                let condition_ty = self.get_type(condition.hir_id);
                let positive_ty = self.get_type(positive.hir_id);

                if !condition_ty.is_bool() && !condition_ty.is_error() {
                    let bool_ty = self.type_context.get_primitive_type(PrimitiveKind::Bool);

                    self.errors.push(TypeError {
                        origin: TypeConstraintOrigin {
                            span: condition.span,
                            kind: TypeBoundary::IfCondition,
                        },
                        kind: TypeErrorKind::TypeMismatch {
                            expected: bool_ty,
                            actual: condition_ty,
                        },
                    });
                }

                if let Some(n) = negative.as_ref() {
                    let negative_ty = self.get_type(n.hir_id);

                    self.add_equality_constraint(
                        positive_ty.clone(),
                        negative_ty,
                        TypeConstraintOrigin {
                            // TODO: use the span of the last expr in the block chain (lol)
                            span: n.span,
                            kind: TypeBoundary::IfBlock,
                        },
                    );
                }

                self.insert_type(expression.hir_id, positive_ty);
            }
            hir::ExpressionKind::While { condition, block } => {
                let condition_ty = self.get_type(condition.hir_id);
                let block_ty = self.get_type(block.hir_id);
                let unit_ty = self.type_context.get_unit_type();

                if !condition_ty.is_bool() && !condition_ty.is_error() {
                    let bool_ty = self.type_context.get_primitive_type(PrimitiveKind::Bool);

                    self.errors.push(TypeError {
                        origin: TypeConstraintOrigin {
                            span: condition.span,
                            kind: TypeBoundary::WhileCondition,
                        },
                        kind: TypeErrorKind::TypeMismatch {
                            expected: bool_ty,
                            actual: condition_ty,
                        },
                    });
                }

                if !block_ty.is_unit() {
                    self.errors.push(TypeError {
                        origin: TypeConstraintOrigin {
                            span: condition.span,
                            kind: TypeBoundary::WhileCondition,
                        },
                        kind: TypeErrorKind::TypeMismatch {
                            expected: unit_ty.clone(),
                            actual: block_ty,
                        },
                    });
                }

                self.insert_type(expression.hir_id, unit_ty);
            }
            hir::ExpressionKind::Assignment { lhs, rhs } => {
                let lhs_ty = self.get_type(lhs.hir_id);
                let rhs_ty = self.get_type(rhs.hir_id);
                let unit_ty = self.type_context.get_unit_type();

                self.add_equality_constraint(
                    lhs_ty,
                    rhs_ty,
                    TypeConstraintOrigin {
                        span: expression.span,
                        kind: TypeBoundary::Assignment,
                    },
                );

                self.insert_type(expression.hir_id, unit_ty);
            }
            hir::ExpressionKind::OperatorAssignment { operator, lhs, rhs } => {
                let lhs_ty = self.get_type(lhs.hir_id);
                let rhs_ty = self.get_type(rhs.hir_id);
                let unit_ty = self.type_context.get_unit_type();

                match operator.class() {
                    // If this is an arithmetic operator, require that both
                    // types are arithmetic
                    AssignmentOperatorClass::Arithmetic => {
                        let mut error = false;

                        if !lhs_ty.is_arithmetic() {
                            error = true;

                            self.errors.push(TypeError {
                                origin: TypeConstraintOrigin {
                                    span: lhs.span,
                                    kind: TypeBoundary::OpAssignment,
                                },
                                kind: TypeErrorKind::InvalidOperation {
                                    attempted_usage: TypeUsage::ArithmeticOperation,
                                    provided: lhs_ty.clone(),
                                },
                            });
                        }

                        if !rhs_ty.is_arithmetic() {
                            error = true;

                            self.errors.push(TypeError {
                                origin: TypeConstraintOrigin {
                                    span: rhs.span,
                                    kind: TypeBoundary::OpAssignment,
                                },
                                kind: TypeErrorKind::InvalidOperation {
                                    attempted_usage: TypeUsage::ArithmeticOperation,
                                    provided: rhs_ty.clone(),
                                },
                            });
                        }

                        if error {
                            let error_ty = self.type_context.get_error_type();
                            self.insert_type(expression.hir_id, error_ty);

                            return;
                        }
                    }
                    // If this is a logical operator, require that both
                    // types are bools
                    AssignmentOperatorClass::Logical => {
                        let mut error = false;

                        if !lhs_ty.is_bool() {
                            error = true;

                            self.errors.push(TypeError {
                                origin: TypeConstraintOrigin {
                                    span: lhs.span,
                                    kind: TypeBoundary::OpAssignment,
                                },
                                kind: TypeErrorKind::InvalidOperation {
                                    attempted_usage: TypeUsage::LogicalOperation,
                                    provided: lhs_ty.clone(),
                                },
                            });
                        }

                        if !rhs_ty.is_bool() {
                            error = true;

                            self.errors.push(TypeError {
                                origin: TypeConstraintOrigin {
                                    span: rhs.span,
                                    kind: TypeBoundary::OpAssignment,
                                },
                                kind: TypeErrorKind::InvalidOperation {
                                    attempted_usage: TypeUsage::LogicalOperation,
                                    provided: rhs_ty.clone(),
                                },
                            });
                        }

                        if error {
                            let error_ty = self.type_context.get_error_type();
                            self.insert_type(expression.hir_id, error_ty);

                            return;
                        }
                    }
                }

                // For operators like &&= and ||=, the types need to be
                // bools. For operators like += and -=, the types need
                // to be the same. In either case we need to add this
                // equality constraint.
                self.add_equality_constraint(
                    lhs_ty.clone(),
                    rhs_ty,
                    TypeConstraintOrigin {
                        span: expression.span,
                        kind: TypeBoundary::OpAssignment,
                    },
                );
                self.insert_type(expression.hir_id, unit_ty);
            }
            kind @ (hir::ExpressionKind::Break | hir::ExpressionKind::Continue) => {
                let kind = if matches!(kind, hir::ExpressionKind::Break) {
                    LoopControlFlowKind::Break
                } else {
                    LoopControlFlowKind::Continue
                };

                if !self.within_loop {
                    self.errors.push(TypeError {
                        origin: TypeConstraintOrigin {
                            span: expression.span,
                            kind: TypeBoundary::LoopControlFlow,
                        },
                        kind: TypeErrorKind::IllegalLoopControlFlow(kind),
                    });
                }

                let ty = self.type_context.get_primitive_type(PrimitiveKind::Never);
                self.insert_type(expression.hir_id, ty);
            }
            hir::ExpressionKind::Return(value) => {
                let return_ty = self.return_type.get().unwrap().clone();

                if let Some(v) = value {
                    let value_ty = self.get_type(v.hir_id);

                    if value_ty != return_ty {
                        self.add_equality_constraint(
                            value_ty,
                            return_ty,
                            TypeConstraintOrigin {
                                span: expression.span,
                                kind: TypeBoundary::ExplicitReturn,
                            },
                        );
                    }
                } else if !return_ty.is_unit() {
                    self.errors.push(TypeError {
                        origin: TypeConstraintOrigin {
                            span: expression.span,
                            kind: TypeBoundary::ExplicitReturn,
                        },
                        kind: TypeErrorKind::MissingReturnValue {
                            expected: return_ty,
                        },
                    });
                }

                let ty = self.type_context.get_primitive_type(PrimitiveKind::Never);
                self.insert_type(expression.hir_id, ty);
            }
        }
    }

    fn visit_block(&mut self, block: Rc<hir::Block>, context: hir::visit::BlockContext) {
        // Add to loop context if necessary
        {
            let previous = self.within_loop;
            self.within_loop = self.within_loop || context == hir::visit::BlockContext::Loop;

            hir::visit::walk_block(self, block.clone());

            self.within_loop = previous;
        }

        for stmt in block.statements.iter() {
            let hir::StatementKind::BareExpression(e) = &stmt.kind else {
                continue;
            };

            let expr_ty = self.get_type(e.hir_id);
            let unit_ty = self.type_context.get_unit_type();

            if !expr_ty.is_unit() && !expr_ty.is_never() && !expr_ty.is_error() {
                self.errors.push(TypeError {
                    origin: TypeConstraintOrigin {
                        // TODO: use the span of the last expr in the block
                        span: e.span,
                        kind: TypeBoundary::BareExpression,
                    },
                    kind: TypeErrorKind::TypeMismatch {
                        expected: unit_ty,
                        actual: expr_ty,
                    },
                });
            }
        }

        if let Some(e) = &block.expression {
            self.copy_type_from(block.hir_id, e.hir_id);
        } else {
            let unit_ty = self.type_context.get_unit_type();
            self.insert_type(block.hir_id, unit_ty);
        }
    }

    fn visit_statement(&mut self, statement: Rc<hir::Statement>) {
        hir::visit::walk_statement(self, statement.clone());

        let unit_ty = self.type_context.get_unit_type();
        self.insert_type(statement.hir_id, unit_ty);
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

pub fn type_check_module(module: &hir::Module, source_file: &SourceFile) -> ModuleTypeCheckResults {
    let mut ctx = TypeContext::new(module, source_file);

    // Compute types for top level items we might reference in body contexts
    let mut global_indexer = GlobalTypeEnvironmentIndexer {
        type_context: &mut ctx,
    };
    hir::visit::walk_module(&mut global_indexer, module);

    let mut results = ModuleTypeCheckResults {
        item_results: BTreeMap::new(),
    };

    let mut tainted_with_errors = false;

    // Check the content of bodies and assign types to all nodes
    for owner_id in module.get_owners() {
        let mut body_ctx = TypeChecker {
            type_context: &mut ctx,
            owner_id,
            node_to_type_map: BTreeMap::new(),
            constraints: Vec::new(),
            errors: Vec::new(),
            within_loop: false,
            return_type: OnceCell::new(),
            next_integer_variable_id: IntVariableId::new(0),
            next_float_variable_id: FloatVariableId::new(0),
        };

        let OwnerNode::Item(item) = module.get_owner(owner_id).node();
        hir::visit::walk_item(&mut body_ctx, item);

        // println!("{:#?}", body_ctx.constraints);

        match body_ctx.into_output() {
            Ok(output) => {
                results.item_results.insert(owner_id, output);
            }
            Err(errors) => {
                tainted_with_errors = true;

                for err in errors {
                    ctx.report_error(err);
                }
            }
        }
    }

    if tainted_with_errors {
        std::process::exit(1);
    }

    results
}
