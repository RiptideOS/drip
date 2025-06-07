
impl Type {
    pub fn size(self) -> Bytes {
        match self {
            Type::Int(IntKind::I8) => Bytes(1),
            Type::Int(IntKind::I16) => Bytes(2),
            Type::Int(IntKind::I32) => Bytes(4),
            Type::Int(IntKind::I64) => Bytes(8),
            Type::Int(IntKind::ISize) => Bytes(8),
            Type::UInt(UIntKind::U8) => Bytes(1),
            Type::UInt(UIntKind::U16) => Bytes(2),
            Type::UInt(UIntKind::U32) => Bytes(4),
            Type::UInt(UIntKind::U64) => Bytes(8),
            Type::UInt(UIntKind::USize) => Bytes(8),
            Type::Float(FloatKind::F32) => Bytes(4),
            Type::Float(FloatKind::F64) => Bytes(8),
            Type::Bool => Bytes(1),
            Type::Pointer => Bytes(8),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Bytes(pub u8);

impl Bytes {
    pub fn bytes(self) -> u8 {
        self.0
    }

    pub fn bits(self) -> u8 {
        self.bytes() * 8
    }
}