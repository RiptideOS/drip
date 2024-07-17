use strum::{EnumIter, EnumString};

use crate::frontend::ast::{BinaryOperatorKind, UnaryOperatorKind};

#[derive(Debug, Clone, Copy, PartialEq, Eq, EnumString, EnumIter)]
#[strum(serialize_all = "lowercase")]
pub enum PrimitiveKind {
    Unit,
    U8,
    U16,
    U32,
    U64,
    USize,
    I8,
    I16,
    I32,
    I64,
    ISize,
    F32,
    F64,
    Char,
    Bool,
}

impl core::fmt::Display for PrimitiveKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PrimitiveKind::Unit => write!(f, "()"),
            PrimitiveKind::U8 => write!(f, "u8"),
            PrimitiveKind::U16 => write!(f, "u16"),
            PrimitiveKind::U32 => write!(f, "u32"),
            PrimitiveKind::U64 => write!(f, "u64"),
            PrimitiveKind::USize => write!(f, "usize"),
            PrimitiveKind::I8 => write!(f, "i8"),
            PrimitiveKind::I16 => write!(f, "i16"),
            PrimitiveKind::I32 => write!(f, "i32"),
            PrimitiveKind::I64 => write!(f, "i64"),
            PrimitiveKind::ISize => write!(f, "isize"),
            PrimitiveKind::F32 => write!(f, "f32"),
            PrimitiveKind::F64 => write!(f, "f64"),
            PrimitiveKind::Char => write!(f, "char"),
            PrimitiveKind::Bool => write!(f, "bool"),
        }
    }
}

impl PrimitiveKind {
    pub fn supports_binary_op(&self, kind: BinaryOperatorKind) -> bool {
        match self {
            // All ops besides logical
            PrimitiveKind::U8
            | PrimitiveKind::U16
            | PrimitiveKind::U32
            | PrimitiveKind::U64
            | PrimitiveKind::USize
            | PrimitiveKind::I8
            | PrimitiveKind::I16
            | PrimitiveKind::I32
            | PrimitiveKind::I64
            | PrimitiveKind::ISize => match kind {
                BinaryOperatorKind::Add
                | BinaryOperatorKind::Subtract
                | BinaryOperatorKind::Multiply
                | BinaryOperatorKind::Divide
                | BinaryOperatorKind::Modulus
                | BinaryOperatorKind::Equals
                | BinaryOperatorKind::NotEquals
                | BinaryOperatorKind::LessThan
                | BinaryOperatorKind::LessThanOrEqualTo
                | BinaryOperatorKind::GreaterThan
                | BinaryOperatorKind::GreaterThanOrEqualTo
                | BinaryOperatorKind::BitwiseAnd
                | BinaryOperatorKind::BitwiseOr
                | BinaryOperatorKind::BitwiseXor
                | BinaryOperatorKind::ShiftLeft
                | BinaryOperatorKind::ShiftRight => true,
                BinaryOperatorKind::LogicalAnd | BinaryOperatorKind::LogicalOr => false,
            },
            // No bitwise or logical ops
            PrimitiveKind::F32 | PrimitiveKind::F64 => match kind {
                BinaryOperatorKind::Add
                | BinaryOperatorKind::Subtract
                | BinaryOperatorKind::Multiply
                | BinaryOperatorKind::Divide
                | BinaryOperatorKind::Modulus
                | BinaryOperatorKind::Equals
                | BinaryOperatorKind::NotEquals
                | BinaryOperatorKind::LessThan
                | BinaryOperatorKind::LessThanOrEqualTo
                | BinaryOperatorKind::GreaterThan
                | BinaryOperatorKind::GreaterThanOrEqualTo => true,
                BinaryOperatorKind::LogicalAnd
                | BinaryOperatorKind::LogicalOr
                | BinaryOperatorKind::BitwiseAnd
                | BinaryOperatorKind::BitwiseOr
                | BinaryOperatorKind::BitwiseXor
                | BinaryOperatorKind::ShiftLeft
                | BinaryOperatorKind::ShiftRight => false,
            },
            // Only comparison ops
            PrimitiveKind::Char => match kind {
                BinaryOperatorKind::Equals
                | BinaryOperatorKind::NotEquals
                | BinaryOperatorKind::LessThan
                | BinaryOperatorKind::LessThanOrEqualTo
                | BinaryOperatorKind::GreaterThan
                | BinaryOperatorKind::GreaterThanOrEqualTo => true,
                BinaryOperatorKind::Add
                | BinaryOperatorKind::Subtract
                | BinaryOperatorKind::Multiply
                | BinaryOperatorKind::Divide
                | BinaryOperatorKind::Modulus
                | BinaryOperatorKind::LogicalAnd
                | BinaryOperatorKind::LogicalOr
                | BinaryOperatorKind::BitwiseAnd
                | BinaryOperatorKind::BitwiseOr
                | BinaryOperatorKind::BitwiseXor
                | BinaryOperatorKind::ShiftLeft
                | BinaryOperatorKind::ShiftRight => false,
            },
            // Only simple comparison and logical ops
            PrimitiveKind::Bool => match kind {
                BinaryOperatorKind::Equals
                | BinaryOperatorKind::NotEquals
                | BinaryOperatorKind::LogicalAnd
                | BinaryOperatorKind::LogicalOr => true,
                BinaryOperatorKind::LessThan
                | BinaryOperatorKind::LessThanOrEqualTo
                | BinaryOperatorKind::GreaterThan
                | BinaryOperatorKind::GreaterThanOrEqualTo
                | BinaryOperatorKind::Add
                | BinaryOperatorKind::Subtract
                | BinaryOperatorKind::Multiply
                | BinaryOperatorKind::Divide
                | BinaryOperatorKind::Modulus
                | BinaryOperatorKind::BitwiseAnd
                | BinaryOperatorKind::BitwiseOr
                | BinaryOperatorKind::BitwiseXor
                | BinaryOperatorKind::ShiftLeft
                | BinaryOperatorKind::ShiftRight => false,
            },
            // No ops supported
            PrimitiveKind::Unit => false,
        }
    }

    pub fn supports_unary_op(&self, kind: UnaryOperatorKind) -> bool {
        match self {
            PrimitiveKind::Unit
            | PrimitiveKind::U8
            | PrimitiveKind::U16
            | PrimitiveKind::U32
            | PrimitiveKind::U64
            | PrimitiveKind::USize => match kind {
                UnaryOperatorKind::BitwiseNot | UnaryOperatorKind::AddressOf => true,
                UnaryOperatorKind::Deref
                | UnaryOperatorKind::LogicalNot
                | UnaryOperatorKind::Negate => false,
            },
            PrimitiveKind::I8
            | PrimitiveKind::I16
            | PrimitiveKind::I32
            | PrimitiveKind::I64
            | PrimitiveKind::ISize => match kind {
                UnaryOperatorKind::BitwiseNot
                | UnaryOperatorKind::Negate
                | UnaryOperatorKind::AddressOf => true,
                UnaryOperatorKind::Deref | UnaryOperatorKind::LogicalNot => false,
            },
            PrimitiveKind::F32 | PrimitiveKind::F64 => match kind {
                UnaryOperatorKind::BitwiseNot
                | UnaryOperatorKind::Negate
                | UnaryOperatorKind::AddressOf => true,
                UnaryOperatorKind::Deref | UnaryOperatorKind::LogicalNot => false,
            },
            PrimitiveKind::Bool => match kind {
                UnaryOperatorKind::LogicalNot | UnaryOperatorKind::AddressOf => true,
                UnaryOperatorKind::Deref
                | UnaryOperatorKind::BitwiseNot
                | UnaryOperatorKind::Negate => false,
            },
            PrimitiveKind::Char => match kind {
                UnaryOperatorKind::AddressOf => true,
                UnaryOperatorKind::Deref
                | UnaryOperatorKind::LogicalNot
                | UnaryOperatorKind::BitwiseNot
                | UnaryOperatorKind::Negate => false,
            },
        }
    }

    pub fn can_be_cast_to(&self, target: Self) -> bool {
        match self {
            PrimitiveKind::U8
            | PrimitiveKind::U16
            | PrimitiveKind::U32
            | PrimitiveKind::U64
            | PrimitiveKind::USize
            | PrimitiveKind::I8
            | PrimitiveKind::I16
            | PrimitiveKind::I32
            | PrimitiveKind::I64
            | PrimitiveKind::ISize => match target {
                PrimitiveKind::U8
                | PrimitiveKind::U16
                | PrimitiveKind::U32
                | PrimitiveKind::U64
                | PrimitiveKind::USize
                | PrimitiveKind::I8
                | PrimitiveKind::I16
                | PrimitiveKind::I32
                | PrimitiveKind::I64
                | PrimitiveKind::ISize
                | PrimitiveKind::F32
                | PrimitiveKind::F64
                | PrimitiveKind::Char
                | PrimitiveKind::Bool => true,
                PrimitiveKind::Unit => false,
            },
            PrimitiveKind::F32 | PrimitiveKind::F64 => match target {
                PrimitiveKind::U8
                | PrimitiveKind::U16
                | PrimitiveKind::U32
                | PrimitiveKind::U64
                | PrimitiveKind::USize
                | PrimitiveKind::I8
                | PrimitiveKind::I16
                | PrimitiveKind::I32
                | PrimitiveKind::I64
                | PrimitiveKind::ISize
                | PrimitiveKind::F32
                | PrimitiveKind::F64 => true,
                PrimitiveKind::Unit | PrimitiveKind::Char | PrimitiveKind::Bool => false,
            },
            PrimitiveKind::Char => match target {
                PrimitiveKind::U8
                | PrimitiveKind::U16
                | PrimitiveKind::U32
                | PrimitiveKind::Char => true,
                PrimitiveKind::Unit
                | PrimitiveKind::U64
                | PrimitiveKind::USize
                | PrimitiveKind::I8
                | PrimitiveKind::I16
                | PrimitiveKind::I32
                | PrimitiveKind::ISize
                | PrimitiveKind::I64
                | PrimitiveKind::F32
                | PrimitiveKind::F64
                | PrimitiveKind::Bool => false,
            },
            PrimitiveKind::Bool => match target {
                PrimitiveKind::U8
                | PrimitiveKind::U16
                | PrimitiveKind::U32
                | PrimitiveKind::U64
                | PrimitiveKind::USize
                | PrimitiveKind::I8
                | PrimitiveKind::I16
                | PrimitiveKind::I32
                | PrimitiveKind::I64
                | PrimitiveKind::ISize
                | PrimitiveKind::F32
                | PrimitiveKind::F64
                | PrimitiveKind::Bool => true,
                PrimitiveKind::Unit | PrimitiveKind::Char => false,
            },
            PrimitiveKind::Unit => false,
        }
    }
}
