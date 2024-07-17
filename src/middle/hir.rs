//! A high level type checked intermediate representation of the source code. A
//! lot of unnecessary information from the AST is removed like individual node
//! IDs (besides for identifiers), spans, parenthesis, etc. At this point the
//! input source is guaranteed to be valid and any errors generated are the
//! compiler's fault.

use crate::frontend::{
    ast::{BinaryOperatorKind, UnaryOperatorKind},
    intern::InternedSymbol,
};

use super::{
    resolve::DefinitionId,
    type_checker::{LocalDefinitionId, TypeId, TypeTable},
};

#[derive(Debug)]
pub struct HirModule {
    pub id: u32,
    pub function_definitions: Vec<HirFunctionDefinition>,
    pub type_table: TypeTable,
}

#[derive(Debug)]
pub struct HirFunctionDefinition {
    pub name: InternedSymbol,
    pub parameters: Vec<HirFunctionParameter>,
    pub return_type: TypeId,
    pub body: HirBlock,
}

#[derive(Debug)]
pub struct HirFunctionParameter {
    pub id: LocalDefinitionId,
    pub name: InternedSymbol,
    pub ty: TypeId,
}

#[derive(Debug)]
pub struct HirBlock {
    pub statements: Vec<HirStatement>,
    /// Will be unit if the block is empty or the last statement ends in a
    /// semicolon
    pub return_type: TypeId,
}

#[derive(Debug)]
pub enum HirStatement {
    Local(Box<HirLocal>),
    Expression(Box<HirExpression>),
}

#[derive(Debug)]
pub struct HirLocal {
    pub id: LocalDefinitionId,
    pub name: InternedSymbol,
    pub is_mutable: bool,
    pub ty: TypeId,
    pub kind: HirLocalKind,
}

#[derive(Debug)]
pub enum HirLocalKind {
    Declaration,
    Initialization(Box<HirExpression>),
}

#[derive(Debug)]
pub struct HirExpression {
    pub ty: TypeId,
    pub kind: HirExpressionKind,
}

#[derive(Debug)]
pub enum HirExpressionKind {
    Literal(Box<HirLiteral>),
    LocalDefinition(LocalDefinitionId),
    Definition(DefinitionId),
    Block(Box<HirBlock>),
    FunctionCall {
        target: Box<HirExpression>,
        arguments: Vec<HirExpression>,
    },
    Binary {
        lhs: Box<HirExpression>,
        operator: BinaryOperatorKind,
        rhs: Box<HirExpression>,
    },
    Unary {
        operator: UnaryOperatorKind,
        operand: Box<HirExpression>,
    },
    Cast {
        expression: Box<HirExpression>,
        ty: TypeId,
    },
    If {
        condition: Box<HirExpression>,
        positive: Box<HirBlock>,
        /// must be a block expression or an if expression
        negative: Option<Box<HirExpression>>,
    },
    While {
        condition: Box<HirExpression>,
        block: Box<HirBlock>,
    },
    Assignment {
        kind: AssignmentKind,
        lhs: Box<HirExpression>,
        rhs: Box<HirExpression>,
    },
    Break,
    Continue,
    // Least priority
    Return(Option<Box<HirExpression>>),
}

#[derive(Debug)]
pub enum AssignmentKind {
    /// let a = 0;
    /// a = 1;
    Local,
    /// let a = 0;
    /// let b = &a;
    /// *b = 1;
    Deref,
    /// let a = [0,2,3];
    /// a[0] = 1;
    Index,
    /// let a = MyStruct { some_field: 0 };
    /// a.some_field = 1;
    Field,
}

#[derive(Debug)]
pub enum HirLiteral {
    Boolean(bool),
    Integer(u64),
    Char(char),
    Float32(f32),
    Float64(f64),
    String(InternedSymbol),
    ByteString(Vec<u8>),
    CString(Vec<u8>),
}
