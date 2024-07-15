use strum::{EnumIter, EnumString};

use crate::frontend::ast::{BinaryOperatorKind, UnaryOperatorKind};

#[derive(Debug, Clone, Copy, PartialEq, Eq, EnumString, EnumIter)]
#[strum(serialize_all = "snake_case")]
pub enum PrimitiveKind {
    Unit,
    U8,
    U16,
    U32,
    U64,
    I8,
    I16,
    I32,
    I64,
    F32,
    F64,
    Char,
    Bool,
    #[strum(serialize = "str")]
    String,
    #[strum(serialize = "cstr")]
    CString,
    #[strum(serialize = "bytes")]
    ByteString,
}

impl PrimitiveKind {
    pub fn supports_binary_op(&self, kind: BinaryOperatorKind) -> bool {
        match self {
            // All ops besides logical
            PrimitiveKind::U8
            | PrimitiveKind::U16
            | PrimitiveKind::U32
            | PrimitiveKind::U64
            | PrimitiveKind::I8
            | PrimitiveKind::I16
            | PrimitiveKind::I32
            | PrimitiveKind::I64 => match kind {
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
            PrimitiveKind::Unit
            | PrimitiveKind::String
            | PrimitiveKind::CString
            | PrimitiveKind::ByteString => false,
        }
    }

    pub fn supports_unary_op(&self, kind: UnaryOperatorKind) -> bool {
        match self {
            PrimitiveKind::Unit
            | PrimitiveKind::U8
            | PrimitiveKind::U16
            | PrimitiveKind::U32
            | PrimitiveKind::U64 => match kind {
                UnaryOperatorKind::BitwiseNot => true,
                UnaryOperatorKind::Deref
                | UnaryOperatorKind::LogicalNot
                | UnaryOperatorKind::Negate => false,
            },
            PrimitiveKind::I8 | PrimitiveKind::I16 | PrimitiveKind::I32 | PrimitiveKind::I64 => {
                match kind {
                    UnaryOperatorKind::BitwiseNot | UnaryOperatorKind::Negate => true,
                    UnaryOperatorKind::Deref | UnaryOperatorKind::LogicalNot => false,
                }
            }
            PrimitiveKind::F32 | PrimitiveKind::F64 => match kind {
                UnaryOperatorKind::BitwiseNot | UnaryOperatorKind::Negate => true,
                UnaryOperatorKind::Deref | UnaryOperatorKind::LogicalNot => false,
            },
            PrimitiveKind::Bool => match kind {
                UnaryOperatorKind::LogicalNot => true,
                UnaryOperatorKind::Deref
                | UnaryOperatorKind::BitwiseNot
                | UnaryOperatorKind::Negate => false,
            },
            PrimitiveKind::Char
            | PrimitiveKind::String
            | PrimitiveKind::CString
            | PrimitiveKind::ByteString => false,
        }
    }

    pub fn can_be_cast_to(&self, target: Self) -> bool {
        match self {
            PrimitiveKind::U8
            | PrimitiveKind::U16
            | PrimitiveKind::U32
            | PrimitiveKind::U64
            | PrimitiveKind::I8
            | PrimitiveKind::I16
            | PrimitiveKind::I32
            | PrimitiveKind::I64 => match target {
                PrimitiveKind::U8
                | PrimitiveKind::U16
                | PrimitiveKind::U32
                | PrimitiveKind::U64
                | PrimitiveKind::I8
                | PrimitiveKind::I16
                | PrimitiveKind::I32
                | PrimitiveKind::I64
                | PrimitiveKind::F32
                | PrimitiveKind::F64
                | PrimitiveKind::Char
                | PrimitiveKind::Bool => true,
                PrimitiveKind::Unit
                | PrimitiveKind::String
                | PrimitiveKind::CString
                | PrimitiveKind::ByteString => false,
            },
            PrimitiveKind::F32 | PrimitiveKind::F64 => match target {
                PrimitiveKind::U8
                | PrimitiveKind::U16
                | PrimitiveKind::U32
                | PrimitiveKind::U64
                | PrimitiveKind::I8
                | PrimitiveKind::I16
                | PrimitiveKind::I32
                | PrimitiveKind::I64
                | PrimitiveKind::F32
                | PrimitiveKind::F64 => true,
                PrimitiveKind::Unit
                | PrimitiveKind::Char
                | PrimitiveKind::Bool
                | PrimitiveKind::String
                | PrimitiveKind::CString
                | PrimitiveKind::ByteString => false,
            },
            PrimitiveKind::Char => match target {
                PrimitiveKind::U8
                | PrimitiveKind::U16
                | PrimitiveKind::U32
                | PrimitiveKind::Char => true,
                PrimitiveKind::Unit
                | PrimitiveKind::U64
                | PrimitiveKind::I8
                | PrimitiveKind::I16
                | PrimitiveKind::I32
                | PrimitiveKind::I64
                | PrimitiveKind::F32
                | PrimitiveKind::F64
                | PrimitiveKind::Bool
                | PrimitiveKind::String
                | PrimitiveKind::CString
                | PrimitiveKind::ByteString => false,
            },
            PrimitiveKind::Bool => match target {
                PrimitiveKind::U8
                | PrimitiveKind::U16
                | PrimitiveKind::U32
                | PrimitiveKind::U64
                | PrimitiveKind::I8
                | PrimitiveKind::I16
                | PrimitiveKind::I32
                | PrimitiveKind::I64
                | PrimitiveKind::F32
                | PrimitiveKind::F64
                | PrimitiveKind::Bool => true,
                PrimitiveKind::Unit
                | PrimitiveKind::Char
                | PrimitiveKind::String
                | PrimitiveKind::CString
                | PrimitiveKind::ByteString => false,
            },
            PrimitiveKind::Unit
            | PrimitiveKind::String
            | PrimitiveKind::CString
            | PrimitiveKind::ByteString => false,
        }
    }
}
