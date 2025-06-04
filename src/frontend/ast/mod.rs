use super::{SourceFile, intern::InternedSymbol};
use crate::frontend::lexer::Span;

pub mod visit;

#[derive(Debug)]
pub struct Module<'source> {
    pub source_file: &'source SourceFile,
    /// Top level items in the module (nested items are in the tree and not in
    /// this list)
    pub items: Vec<Item>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct NodeId(pub u32);

#[derive(Debug)]
pub struct Item {
    pub id: NodeId,
    pub span: Span,
    pub kind: ItemKind,
}

#[derive(Debug)]
pub enum ItemKind {
    FunctionDefinition(Box<FunctionDefinition>),
}

#[derive(Debug)]
pub struct FunctionDefinition {
    pub id: NodeId,
    pub span: Span,
    pub signature: FunctionSignature,
    pub body: Block,
}

#[derive(Debug)]
pub struct FunctionSignature {
    pub id: NodeId,
    pub span: Span,
    pub name: Identifier,
    pub parameters: FunctionParameterList,
    pub return_type: Option<Type>,
}

#[derive(Debug)]
pub struct FunctionParameterList {
    pub id: NodeId,
    pub span: Span,
    pub parameters: Vec<FunctionParameter>,
}

#[derive(Debug)]
pub struct FunctionParameter {
    pub id: NodeId,
    pub span: Span,
    pub name: Identifier,
    pub ty: Type,
}

#[derive(Debug)]
pub struct Type {
    pub id: NodeId,
    pub span: Span,
    pub kind: TypeKind,
}

#[derive(Debug)]
pub enum TypeKind {
    Unit,
    QualifiedIdentifier(QualifiedIdentifier),
    Pointer(Box<Type>),
    Slice(Box<Type>),
    Array { ty: Box<Type>, length: Box<Literal> },
    Tuple(Box<[Type]>),
    Any,
}

#[derive(Debug)]
pub struct QualifiedIdentifier {
    pub id: NodeId,
    pub span: Span,
    pub segments: Vec<Identifier>,
}

impl QualifiedIdentifier {
    pub fn last(&self) -> &Identifier {
        self.segments
            .last()
            .expect("QualifiedIdentifier should always have at least one segment")
    }
}

#[derive(Debug)]
pub struct Identifier {
    pub id: NodeId,
    pub span: Span,
    pub symbol: InternedSymbol,
}

#[derive(Debug)]
pub struct Block {
    pub id: NodeId,
    pub span: Span,
    pub statements: Vec<Statement>,
}

#[derive(Debug)]
pub struct Statement {
    pub id: NodeId,
    pub span: Span,
    pub kind: StatementKind,
}

#[derive(Debug)]
pub enum StatementKind {
    // Local (let) binding or declaration
    Local(Box<Local>),
    // Expression without a trailing semicolon
    BareExpr(Box<Expression>),
    // Expression terminated with a semicolon
    SemiExpr(Box<Expression>),
    /// Empty statement (just a semicolon)
    Empty,
}

#[derive(Debug)]
pub struct Local {
    pub id: NodeId,
    pub span: Span,
    pub is_mutable: bool,
    pub name: Identifier,
    pub ty: Option<Type>,
    pub kind: LocalKind,
}

#[derive(Debug)]
pub enum LocalKind {
    Declaration,
    Initialization(Box<Expression>),
}

#[derive(Debug)]
pub struct Expression {
    pub id: NodeId,
    pub span: Span,
    pub kind: ExpressionKind,
}

#[derive(Debug)]
pub enum ExpressionKind {
    Literal(Box<Literal>),
    QualifiedIdentifier(Box<QualifiedIdentifier>),
    Grouping(Box<Expression>),
    Tuple(Box<[Expression]>),
    Block(Box<Block>),
    FunctionCall {
        target: Box<Expression>,
        arguments: Box<FunctionCallArgumentList>,
    },
    Binary {
        lhs: Box<Expression>,
        operator: BinaryOperator,
        rhs: Box<Expression>,
    },
    Unary {
        operator: UnaryOperator,
        operand: Box<Expression>,
    },
    Cast {
        expression: Box<Expression>,
        ty: Box<Type>,
    },
    If {
        condition: Box<Expression>,
        positive: Box<Block>,
        /// must be a block expression or an if expression
        negative: Option<Box<Expression>>,
    },
    While {
        condition: Box<Expression>,
        block: Box<Block>,
    },
    Assignment {
        lhs: Box<Expression>,
        rhs: Box<Expression>,
    },
    OperatorAssignment {
        operator: AssignmentOperator,
        lhs: Box<Expression>,
        rhs: Box<Expression>,
    },
    Break,
    Continue,
    // Least priority
    Return(Option<Box<Expression>>),
}

#[derive(Debug)]
pub struct FunctionCallArgumentList {
    pub id: NodeId,
    pub span: Span,
    pub arguments: Vec<Expression>,
}

#[derive(Debug)]
pub struct BinaryOperator {
    pub id: NodeId,
    pub span: Span,
    pub kind: BinaryOperatorKind,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinaryOperatorKind {
    Add,                  // +
    Subtract,             // -
    Multiply,             // *
    Divide,               // /
    Modulus,              // %
    Equals,               // ==
    NotEquals,            // !=
    LessThan,             // <
    LessThanOrEqualTo,    // <=
    GreaterThan,          // >
    GreaterThanOrEqualTo, // >=
    LogicalAnd,           // &&
    LogicalOr,            // ||
    BitwiseAnd,           // &
    BitwiseOr,            // |
    BitwiseXor,           // ^
    ShiftLeft,            // <<
    ShiftRight,           // >>
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinaryOperatorClass {
    Arithmetic,
    Logical,
    Equality,
}

impl BinaryOperatorKind {
    pub fn class(self) -> BinaryOperatorClass {
        match self {
            Self::Add
            | Self::Subtract
            | Self::Multiply
            | Self::Divide
            | Self::Modulus
            | Self::LessThan
            | Self::LessThanOrEqualTo
            | Self::GreaterThan
            | Self::GreaterThanOrEqualTo
            | Self::BitwiseAnd
            | Self::BitwiseOr
            | Self::BitwiseXor
            | Self::ShiftLeft
            | Self::ShiftRight => BinaryOperatorClass::Arithmetic,
            Self::LogicalAnd | Self::LogicalOr => BinaryOperatorClass::Logical,
            Self::Equals | Self::NotEquals => BinaryOperatorClass::Equality,
        }
    }
}

#[derive(Debug)]
pub struct UnaryOperator {
    pub id: NodeId,
    pub span: Span,
    pub kind: UnaryOperatorKind,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnaryOperatorKind {
    Deref,      // *
    AddressOf,  // &
    LogicalNot, // !
    BitwiseNot, // ~
    Negate,     // -
}

impl core::fmt::Display for UnaryOperatorKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Deref => write!(f, "*"),
            Self::AddressOf => write!(f, "&"),
            Self::LogicalNot => write!(f, "!"),
            Self::BitwiseNot => write!(f, "~"),
            Self::Negate => write!(f, "-"),
        }
    }
}

#[derive(Debug)]
pub struct Literal {
    pub id: NodeId,
    pub span: Span,
    pub kind: LiteralKind,
    pub symbol: InternedSymbol,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LiteralKind {
    Boolean,    // true
    Byte,       // b'A'
    Char,       // 'A'
    Integer,    // 1 or 1u32
    Float,      // 1.0 or 1.0f32
    String,     // "hello, world"
    ByteString, // b"hello, world"
    CString,    // c"hello, world"
}

#[derive(Debug)]
pub struct AssignmentOperator {
    pub id: NodeId,
    pub span: Span,
    pub kind: AssignmentOperatorKind,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AssignmentOperatorKind {
    Add,        // +=
    Subtract,   // -=
    Multiply,   // *=
    Divide,     // /=
    Modulus,    // %=
    LogicalAnd, // &&=
    LogicalOr,  // ||=
    BitwiseAnd, // &=
    BitwiseOr,  // |=
    BitwiseXor, // ^=
    ShiftLeft,  // <<=
    ShiftRight, // >>=
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AssignmentOperatorClass {
    Arithmetic,
    Logical,
}

impl AssignmentOperatorKind {
    pub fn class(self) -> AssignmentOperatorClass {
        match self {
            Self::Add
            | Self::Subtract
            | Self::Multiply
            | Self::Divide
            | Self::Modulus
            | Self::BitwiseAnd
            | Self::BitwiseOr
            | Self::BitwiseXor
            | Self::ShiftLeft
            | Self::ShiftRight => AssignmentOperatorClass::Arithmetic,
            Self::LogicalAnd | Self::LogicalOr => AssignmentOperatorClass::Logical,
        }
    }
}
