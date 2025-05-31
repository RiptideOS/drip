use crate::frontend::intern::InternedSymbol;

pub struct LirModule {
    pub id: u32,
    pub function_definitions: Vec<LirFunctionDefinition>,
}

pub struct LirFunctionDefinition {
    pub name: InternedSymbol,
    pub parameters: Vec<LirFunctionParameter>,
    pub return_type: TypeId,
    pub body: LirBlock,
}

pub struct LirFunctionParameter {
    pub id: LocalDefinitionId,
    pub name: InternedSymbol,
    pub ty: TypeId,
}

pub struct LirBlock {
    /// Allocated virtual registers used to store temporary data
    pub registers: Vec<LirRegister>,
    pub labels: Vec<LirLabel>,
    pub instructions: Vec<LirInstruction>,
    pub return_type: TypeId,
}

pub struct LirRegister {
    pub id: u32,
    pub size: usize,
    pub alignment: usize,
}

pub struct LirLabel {
    pub id: u32,
}
