use std::rc::Rc;

use colored::Colorize;

use super::TypeContext;
use crate::{
    index::{Index, simple_index},
    middle::primitive::{FloatKind, IntKind, PrimitiveKind, UIntKind},
};

#[doc(hidden)]
mod private {
    #[doc(hidden)]
    #[derive(Debug, Clone, PartialEq, Eq, Hash)]
    pub struct PrivateZst;
}

/// Thin pointer to an interned type kind. Do not construct directly. Instead,
/// use [`TypeContext::insert_type`]
///
/// FIXME: we could use referential equality here since types are intered and
/// guaranteed to be unique
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct Type(Rc<TypeKind>, private::PrivateZst);

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum TypeKind {
    /// !
    Never,
    /// ()
    Unit,
    // true, false
    Bool,
    // 'a', '\n'
    Char,
    /// i32, i64, etc.
    Integer(IntKind),
    /// u8, u32, etc.
    UnsignedInteger(UIntKind),
    /// f32, f64
    Float(FloatKind),
    /// *T
    ///
    /// A raw pointer to a T
    Pointer(Type),
    /// [T]
    ///
    /// A pointer and length to some amount of T's
    Slice(Type),
    /// str
    ///
    /// A pointer and length to some UTF-8 data
    Str,
    /// cstr
    ///
    /// A raw pointer which is guaranteed to point to a valid, null terminated,
    /// ASCII C-style string
    CStr,
    /// [T; <length>]
    ///
    /// A raw pointer to a fixed size allocation of T's
    Array {
        ty: Type,
        length: usize,
    },
    /// fn(i32, str, *T) -> u8
    ///
    /// A raw pointer to a function body
    FunctionPointer {
        parameters: Rc<[Type]>,
        return_type: Type,
        is_variadic: bool,
    },
    /// *any
    ///
    /// A raw pointer to some data of an unknown type. `any` can not be used on
    /// its own since it has an unknown size, so it must be used as a pointer.
    Any,
    /// An unresolved type variable whose type must be inferred
    Infer(TypeVariable),
    /// The type which is created as a result of some illegal operation which we
    /// can't compute the type of. If you find this in your type, there is no
    /// use emitting another error since one has already been created.
    Error,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum TypeVariable {
    Int(IntVariableId),
    Float(FloatVariableId),
}

simple_index! {
    /// An integral type variable to be inferred
    pub struct IntVariableId;
}

simple_index! {
    /// A floating point type variable to be inferred
    pub struct FloatVariableId;
}

impl<'hir> TypeContext<'hir> {
    pub fn intern_type(&mut self, kind: TypeKind) -> Type {
        let rc = self.type_table.get_or_insert(Rc::new(kind));
        Type(rc.clone(), private::PrivateZst)
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
}

impl core::fmt::Debug for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_tuple("Type").field(&self.0).finish()
    }
}

impl core::ops::Deref for Type {
    type Target = TypeKind;

    fn deref(&self) -> &Self::Target {
        self.0.as_ref()
    }
}

impl TypeKind {
    pub fn is_arithmetic(&self) -> bool {
        // TODO: pointer arithmetic?

        match self {
            TypeKind::Integer(_)
            | TypeKind::UnsignedInteger(_)
            | TypeKind::Float(_)
            | TypeKind::Infer(_) => true,
            TypeKind::Never
            | TypeKind::Unit
            | TypeKind::Bool
            | TypeKind::Char
            | TypeKind::Pointer(_)
            | TypeKind::Slice(_)
            | TypeKind::Str
            | TypeKind::CStr
            | TypeKind::Array { .. }
            | TypeKind::FunctionPointer { .. }
            | TypeKind::Any
            | TypeKind::Error => false,
        }
    }

    pub fn is_integer_like(&self) -> bool {
        matches!(
            self,
            TypeKind::Integer(_)
                | TypeKind::UnsignedInteger(_)
                | TypeKind::Infer(TypeVariable::Int(_))
        )
    }

    pub fn is_float_like(&self) -> bool {
        matches!(
            self,
            TypeKind::Float(_) | TypeKind::Infer(TypeVariable::Float(_))
        )
    }

    pub fn is_unit(&self) -> bool {
        matches!(self, TypeKind::Unit)
    }

    pub fn is_bool(&self) -> bool {
        matches!(self, TypeKind::Bool)
    }

    pub fn is_error(&self) -> bool {
        matches!(self, TypeKind::Error)
    }
}

impl core::fmt::Display for TypeKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Never => write!(f, "!"),
            Self::Unit => write!(f, "()"),
            Self::Bool => write!(f, "bool"),
            Self::Char => write!(f, "char"),
            Self::Integer(int_kind) => write!(f, "{int_kind}"),
            Self::UnsignedInteger(uint_kind) => write!(f, "{uint_kind}"),
            Self::Float(float_kind) => write!(f, "{float_kind}"),
            Self::Pointer(ty) => write!(f, "*{}", **ty),
            Self::Slice(ty) => write!(f, "[{}]", **ty),
            Self::Str => write!(f, "str"),
            Self::CStr => write!(f, "cstr"),
            Self::Array { ty, length } => write!(f, "[{}; {length}]", **ty),
            Self::FunctionPointer { .. } => todo!("Format function pointers"),
            Self::Any => write!(f, "*any"),
            Self::Infer(type_variable) => match type_variable {
                TypeVariable::Int(id) => write!(f, "{{integer@{}}}", id.index()),
                TypeVariable::Float(id) => write!(f, "{{float@{}}}", id.index()),
            },
            Self::Error => write!(f, "{{unknown}}"),
        }
    }
}

impl core::fmt::Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.colored().yellow())
    }
}

impl From<Type> for colored::ColoredString {
    fn from(s: Type) -> Self {
        (*s).to_string().into()
    }
}

impl Type {
    pub fn colored(&self) -> colored::ColoredString {
        self.clone().into()
    }
}
