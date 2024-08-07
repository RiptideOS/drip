use crate::{frontend::lexer::Span, middle::primitive::PrimitiveKind};

use super::{intern::InternedSymbol, SourceFile};

#[derive(Debug)]
pub struct Module<'source> {
    pub id: u32,
    pub source_file: &'source SourceFile,
    pub function_definitions: Vec<FunctionDefinition>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct NodeId(pub u32);

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
    Primitive(PrimitiveKind),
    QualifiedIdentifier(QualifiedIdentifier),
    Pointer(Box<Type>),
    Slice(Box<Type>),
    Str,
    CStr,
    Array { ty: Box<Type>, length: Box<Literal> },
    Any,
}

#[derive(Debug)]
pub struct QualifiedIdentifier {
    pub id: NodeId,
    pub span: Span,
    pub segments: Vec<Identifier>,
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
        operator: AssignmentOperatorKind,
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
