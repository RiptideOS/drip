//! A high level intermediate representation of the source code. Some
//! unnecessary information from the AST is removed like node IDs and spans for
//! individual pieces of syntax. Certain constructs from the AST are removed and
//! blocks are collected and separated from their owning nodes.

use core::fmt::Debug;
use std::{collections::BTreeMap, rc::Rc};

use super::primitive::{FloatKind, IntKind, PrimitiveKind, UIntKind};
use crate::{
    frontend::{
        ast::{AssignmentOperatorKind, BinaryOperatorKind, UnaryOperatorKind},
        intern::InternedSymbol,
        lexer::Span,
    },
    index::IndexVec,
};

pub mod id;
pub mod visit;

pub use id::*;

#[derive(Debug)]
pub struct Module {
    /// All the item definitions within the module including those nested within
    /// other items
    pub owners: IndexVec<LocalDefId, Owner>,
}

/// Represents a top level owner within a module. HIR owners may be nested
#[derive(Debug)]
pub struct Owner {
    /// Contains all the HIR nodes for this owner. The first node is always the
    /// owner itself. This is how nodes are looked up by LocalId within an owner
    /// which is much faster than traversing the tree searching for it.
    /// Important to note is that this owner may contain nested owner nodes
    /// (i.e. functions defined within another function or functions defined
    /// within an impl block)
    pub nodes: IndexVec<ItemLocalId, ParentedNode>,
    /// Map from nested owners to their local ID within this owner
    pub parenting: BTreeMap<LocalDefId, ItemLocalId>,
    /// If present, the executable body within the owner. Will not be set for
    /// items like type definitions. The LocalId is the id of the expression
    /// represented by the body.
    pub body: Option<(ItemLocalId, Rc<Body>)>,
}

impl Owner {
    /// Returns the associated owner node kind
    pub fn node(&self) -> OwnerNode {
        // Indexing must ensure it is an OwnerNode.
        self.nodes[ItemLocalId::ZERO]
            .node
            .clone()
            .as_owner()
            .unwrap()
    }
}

/// An HIR node coupled with the ID of it's parent node. This makes the tree
/// structure of the HIR traversable easily in both directions.
///
/// When the node is a top level owner in the module, the parent id is always
/// INVALID. However, it will be set if the owner is a nested owner.
#[derive(Debug)]
pub struct ParentedNode {
    pub parent: ItemLocalId,
    pub node: Node,
}

#[derive(Debug, Clone)]
pub enum Node {
    Item(Rc<Item>),
    FunctionParameter(Rc<FunctionParameter>),
    Expression(Rc<Expression>),
    Block(Rc<Block>),
    Statement(Rc<Statement>),
    /// Exists so that we can resolve local variable references to a node ID
    LetStatement(Rc<LetStatement>),
    Type(Rc<Type>),
    PathSegment(Rc<PathSegment>),
}

#[derive(Debug, Clone)]
pub enum NodeRef<'a> {
    Item(&'a Item),
    FunctionParameter(&'a FunctionParameter),
    Expression(&'a Expression),
    Block(&'a Block),
    Statement(&'a Statement),
    LetStatement(&'a LetStatement),
    Type(&'a Type),
    PathSegment(&'a PathSegment),
}

impl Node {
    pub fn as_owner(self) -> Option<OwnerNode> {
        match self {
            Node::Item(item) => Some(OwnerNode::Item(item)),
            Node::Block(_)
            | Node::Statement(_)
            | Node::LetStatement(_)
            | Node::Type(_)
            | Node::FunctionParameter(_)
            | Node::Expression(_)
            | Node::PathSegment(_) => None,
        }
    }

    pub fn as_ref(&self) -> NodeRef<'_> {
        match self {
            Node::Item(rc) => NodeRef::Item(&rc),
            Node::FunctionParameter(rc) => NodeRef::FunctionParameter(&rc),
            Node::Expression(rc) => NodeRef::Expression(&rc),
            Node::Block(rc) => NodeRef::Block(&rc),
            Node::Statement(rc) => NodeRef::Statement(&rc),
            Node::LetStatement(rc) => NodeRef::LetStatement(&rc),
            Node::Type(rc) => NodeRef::Type(&rc),
            Node::PathSegment(rc) => NodeRef::PathSegment(&rc),
        }
    }

    pub fn id(&self) -> HirId {
        match self.as_ref() {
            NodeRef::Item(Item { hir_id, .. })
            | NodeRef::FunctionParameter(FunctionParameter { hir_id, .. })
            | NodeRef::Expression(Expression { hir_id, .. })
            | NodeRef::Block(Block { hir_id, .. })
            | NodeRef::Statement(Statement { hir_id, .. })
            | NodeRef::LetStatement(LetStatement { hir_id, .. })
            | NodeRef::Type(Type { hir_id, .. })
            | NodeRef::PathSegment(PathSegment { hir_id, .. }) => *hir_id,
        }
    }
}

/// Represents an HIR node that can be a top level owner
#[derive(Debug)]
pub enum OwnerNode {
    ///
    Item(Rc<Item>),
    // TODO: submodules
    // TODO: foreign items
    // TODO: impl blocks?
}

impl OwnerNode {
    pub fn hir_id(&self) -> HirId {
        match self {
            OwnerNode::Item(item) => item.hir_id,
        }
    }
}

impl From<OwnerNode> for Node {
    fn from(value: OwnerNode) -> Self {
        match value {
            OwnerNode::Item(item) => Node::Item(item),
        }
    }
}

#[derive(Debug, Clone)]
pub struct Identifier {
    pub symbol: InternedSymbol,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct Item {
    pub hir_id: HirId,
    pub kind: ItemKind,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub enum ItemKind {
    Function {
        name: Identifier,
        signature: FunctionSignature,
        body: HirId,
    },
    // TODO: structs, enums, unions, static, const, type alias, submodule, impl
}

#[derive(Debug, Clone)]
pub struct FunctionSignature {
    /// List of inputs to the function
    pub parameters: Rc<[Rc<Type>]>,
    /// If present, is the expected variadic type (`any` for compat with c
    /// variadics)
    pub variadic_type: Option<Rc<Type>>,
    /// None if no return type is specified (defaults to `()` in this case)
    pub return_type: Option<Rc<Type>>,
    // Span of the function decl without body
    pub span: Span,
}

/// The body of a function or constant value
#[derive(Debug)]
pub struct Body {
    pub params: Rc<[Rc<FunctionParameter>]>,
    pub block: Rc<Block>,
}

impl Body {
    pub fn id(&self) -> HirId {
        self.block.hir_id
    }
}

#[derive(Debug)]
pub struct FunctionParameter {
    pub hir_id: HirId,
    pub name: Identifier, // TODO: replace with pattern
    pub ty_span: Span,
    pub span: Span,
}

#[derive(Debug)]
pub struct Block {
    pub hir_id: HirId,
    pub statements: Rc<[Rc<Statement>]>,
    /// An expression at the end of the block without a semicolon, if any. (Used
    /// to infer the type of the block later)
    pub expression: Option<Rc<Expression>>,
    pub is_const: bool,
    pub span: Span,
}

#[derive(Debug)]
pub struct Statement {
    pub hir_id: HirId,
    pub kind: StatementKind,
    pub span: Span,
}

#[derive(Debug)]
pub enum StatementKind {
    Let(Rc<LetStatement>),
    /// An expression without a trailing semi-colon (must have unit type).
    BareExpression(Rc<Expression>),
    /// An expression with a trailing semi-colon (may have any type).
    SemiExpression(Rc<Expression>),
}

#[derive(Debug)]
pub struct LetStatement {
    pub hir_id: HirId,
    pub is_mutable: bool, // TODO: replace with pattern
    pub name: Identifier, // TODO: replace with pattern
    pub ty: Option<Rc<Type>>,
    pub initializer: Option<Rc<Expression>>,
    pub span: Span,
}

#[derive(Debug)]
pub struct Expression {
    pub hir_id: HirId,
    pub kind: ExpressionKind,
    pub span: Span,
}

#[derive(Debug)]
pub enum ExpressionKind {
    Literal(Literal),
    Path(Path),
    Block(Rc<Block>),
    FunctionCall {
        target: Rc<Expression>,
        arguments: Rc<[Rc<Expression>]>,
    },
    Binary {
        lhs: Rc<Expression>,
        operator: BinaryOperatorKind,
        rhs: Rc<Expression>,
    },
    Unary {
        operator: UnaryOperatorKind,
        operand: Rc<Expression>,
    },
    Cast {
        expression: Rc<Expression>,
        ty: Rc<Type>,
    },
    If {
        condition: Rc<Expression>,
        positive: Rc<Block>,
        /// must be a block expression or an if expression
        negative: Option<Rc<Expression>>,
    },
    While {
        condition: Rc<Expression>,
        block: Rc<Block>,
    },
    Assignment {
        lhs: Rc<Expression>,
        rhs: Rc<Expression>,
    },
    OperatorAssignment {
        operator: AssignmentOperatorKind,
        lhs: Rc<Expression>,
        rhs: Rc<Expression>,
    },
    Break,
    Continue,
    // Least priority
    Return(Option<Rc<Expression>>),
}

#[derive(Debug)]
pub enum Literal {
    Boolean(bool),
    Char(char),
    Integer(u64, LiteralIntegerKind),
    Float(InternedSymbol, LiteralFloatKind),
    String(InternedSymbol),
    ByteString(Rc<[u8]>),
    CString(Rc<[u8]>),
}

#[derive(Debug)]
pub enum LiteralIntegerKind {
    /// e.g. `42_u32`
    Unsigned(UIntKind),
    /// e.g. `42_i32`
    Signed(IntKind),
    /// e.g. `42`
    Unsuffixed,
}

#[derive(Debug)]
pub enum LiteralFloatKind {
    Suffixed(FloatKind),
    Unsuffixed,
}

#[derive(Debug)]
pub struct Type {
    pub hir_id: HirId,
    pub kind: TypeKind,
    pub span: Span,
}

#[derive(Debug)]
pub enum TypeKind {
    /// core::string::String | u32 | some_local
    Path(Path),
    /// *T
    Pointer(Rc<Type>),
    /// [T]
    Slice(Rc<Type>),
    /// [T; 1024]
    Array { ty: Rc<Type>, length: usize },
    /// fn(T1, T2, ... *any) -> T3
    FunctionPointer {
        parameters: Rc<[Rc<Type>]>,
        return_type: Option<Rc<Type>>,
        is_variadic: bool, // FIXME: type?
    },
    /// any
    Any,
}

/// A path made up of multiple segments separated by `::`.
#[derive(Debug)]
pub struct Path {
    pub segments: Rc<[Rc<PathSegment>]>,
    pub span: Span,
}

impl Path {
    /// Returns the final resolution in the path (last segment)
    pub fn resolution(&self) -> &Resolution {
        &self.segments.last().as_ref().unwrap().resolution
    }
}

#[derive(Debug)]
pub struct PathSegment {
    pub hir_id: HirId,
    pub identifier: Identifier,
    pub resolution: Resolution,
    pub span: Span,
}

#[derive(Debug, Clone, Copy)]
pub enum Resolution<R = ItemLocalId> {
    // Any namespace
    // TODO: use global ID once we support modules
    Definition(DefinitionKind, LocalDefId),
    // Value namespace
    Local(R),
    IntrinsicFunction,
    // Type namespace
    Primitive(PrimitiveKind),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum DefinitionKind {
    // Value namespace
    Function,
    Constant,
    Static,

    // Type namespace
    Struct,
    Enum,
    Union,
    Alias,
}
