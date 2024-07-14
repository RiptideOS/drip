use crate::{intern::INTERNING_TABLE, lexer::Span};

#[derive(Debug)]
pub struct Module {
    pub function_definitions: Vec<FunctionDefinition>,
}

#[derive(Debug)]
pub struct FunctionDefinition {
    pub signature: FunctionSignature,
    pub body: Block,
}

#[derive(Debug)]
pub struct FunctionSignature {
    pub span: Span,
    pub name: Identifier,
    pub parameters: FunctionParameterList,
    pub return_type: Option<Type>,
}

#[derive(Debug)]
pub struct FunctionParameterList {
    pub span: Span,
    pub parameters: Vec<FunctionParameter>,
}

#[derive(Debug)]
pub struct FunctionParameter {
    pub span: Span,
    pub name: Identifier,
    pub ty: Type,
}

#[derive(Debug)]
pub struct Type {
    pub span: Span,
    pub kind: TypeKind,
}

#[derive(Debug)]
pub enum TypeKind {
    QualifiedIdentifier(QualifiedIdentifier),
}

#[derive(Debug)]
pub struct QualifiedIdentifier {
    pub span: Span,
    pub segments: Vec<Identifier>,
}

#[derive(Debug)]
pub struct Identifier {
    pub span: Span,
    pub symbol: InternedSymbol,
}

/// An index into the string interning table
pub struct InternedSymbol(usize);

impl InternedSymbol {
    pub fn new(value: &str) -> Self {
        let index = INTERNING_TABLE.insert_if_absent(value);

        Self(index)
    }

    pub fn value(&self) -> &'static str {
        INTERNING_TABLE.get(self.0).expect("Once an interned symbol is created, the string it references should never be removed from the table")
    }
}

impl core::fmt::Debug for InternedSymbol {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_tuple("InternedSymbol")
            .field(&self.0)
            .field(&self.value())
            .finish()
    }
}

#[derive(Debug)]
pub struct Block {
    pub span: Span,
    pub statements: Vec<Statement>,
}

#[derive(Debug)]
pub struct Statement {
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
        function: Box<Expression>,
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
    pub span: Span,
    pub arguments: Vec<Expression>,
}

#[derive(Debug)]
pub struct BinaryOperator {
    pub span: Span,
    pub kind: BinaryOperatorKind,
}

#[derive(Debug)]
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
    pub span: Span,
    pub kind: UnaryOperatorKind,
}

#[derive(Debug)]
pub enum UnaryOperatorKind {
    Deref,  // *
    Invert, // !
    Negate, // -
}

#[derive(Debug)]
pub struct Literal {
    pub span: Span,
    pub kind: LiteralKind,
    pub symbol: InternedSymbol,
}

#[derive(Debug)]
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
