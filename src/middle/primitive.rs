use strum::{Display, EnumIter, EnumString};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Display)]
#[strum(serialize_all = "lowercase")]
pub enum PrimitiveKind {
    #[strum(serialize = "!")]
    Never,
    #[strum(serialize = "()")]
    Unit,
    #[strum(to_string = "{0}")]
    Int(IntKind),
    #[strum(to_string = "{0}")]
    UInt(UIntKind),
    #[strum(to_string = "{0}")]
    Float(FloatKind),
    Bool,
    Char,
    Str,
    CStr,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Display, EnumString, EnumIter)]
#[strum(serialize_all = "lowercase")]
pub enum IntKind {
    I8,
    I16,
    I32,
    I64,
    ISize,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Display, EnumString, EnumIter)]
#[strum(serialize_all = "lowercase")]
pub enum UIntKind {
    U8,
    U16,
    U32,
    U64,
    USize,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Display, EnumString, EnumIter)]
#[strum(serialize_all = "lowercase")]
pub enum FloatKind {
    F32,
    F64,
}

impl PrimitiveKind {
    pub const ALL: &[Self] = &[
        Self::Never,
        Self::Unit,
        Self::Int(IntKind::I8),
        Self::Int(IntKind::I16),
        Self::Int(IntKind::I32),
        Self::Int(IntKind::I64),
        Self::Int(IntKind::ISize),
        Self::UInt(UIntKind::U8),
        Self::UInt(UIntKind::U16),
        Self::UInt(UIntKind::U32),
        Self::UInt(UIntKind::U64),
        Self::UInt(UIntKind::USize),
        Self::Float(FloatKind::F32),
        Self::Float(FloatKind::F64),
        Self::Bool,
        Self::Char,
        Self::Str,
        Self::CStr,
    ];
}
