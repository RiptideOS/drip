//! LIR (Low-level Intermediate Representation). In this form, many abstract
//! concepts like loops and conditionals are simplified to labels and jumps,
//! expression trees are flattened into ordered post fix operations, etc.

use std::collections::{BTreeMap, BTreeSet};

use crate::{
    frontend::{
        ast::{BinaryOperatorKind, UnaryOperatorKind},
        intern::InternedSymbol,
    },
    index::simple_index,
    middle::{hir, ty},
};

pub mod hir_lowering;
pub mod pretty_print;

#[derive(Debug)]
pub struct Module {
    pub function_definitions: BTreeMap<hir::LocalDefId, FunctionDefinition>,
}

#[derive(Debug)]
pub struct FunctionDefinition {
    pub symbol_name: InternedSymbol,
    /// Allocated virtual registers used to store temporary data
    pub registers: BTreeMap<RegisterId, Register>,
    pub arguments: Vec<RegisterId>,
    pub blocks: BTreeMap<BlockId, Block>,
}

#[derive(Debug)]
pub struct Block {
    pub id: BlockId,
    pub instructions: Vec<Instruction>,
    pub predecessors: BTreeSet<BlockId>,
}

impl Block {
    pub fn returns(&self) -> bool {
        self.instructions
            .last()
            .is_some_and(|i| matches!(i, Instruction::Return { .. }))
    }
}

simple_index! {
    /// Identifies an LIR block
    pub struct BlockId;
}

impl BlockId {
    pub const ZERO: Self = Self(0);
}

/// A temporary virtual register of some size and alignment
#[derive(Debug, Clone, PartialEq, Hash)]
pub struct Register {
    pub id: RegisterId,
    pub ty: ty::Type,
}

simple_index! {
    /// Identifies a virtual LIR register which holds a temporary value
    pub struct RegisterId;
}

#[derive(Debug, Clone, PartialEq)]
pub enum Instruction {
    Move {
        destination: RegisterId,
        source: Operand,
    },
    UnaryOperation {
        operator: UnaryOperatorKind,
        destination: RegisterId,
        operand: Operand,
    },
    BinaryOperation {
        operator: BinaryOperatorKind,
        destination: RegisterId,
        lhs: Operand,
        rhs: Operand,
    },
    Branch {
        condition: Operand,
        positive: BlockId,
        negative: BlockId,
    },
    Jump {
        destination: BlockId,
    },
    Return {
        value: Option<Operand>,
    },
    FunctionCall {
        target: RegisterId,
        arguments: Vec<Operand>,
        destination: Option<RegisterId>,
    },
    Phi {
        destination: RegisterId,
        sources: BTreeMap<BlockId, RegisterId>,
    },
    Comment(String),
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Immediate {
    Int(u64),
    Float(f64),
    Bool(bool),
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Operand {
    Immediate(Immediate),
    Register(RegisterId),
}
