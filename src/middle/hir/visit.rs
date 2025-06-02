// Item(Rc<Item>),
// FunctionParameter(Rc<FunctionParameter>),
// Expression(Rc<Expression>),
// Block(Rc<Block>),
// Statement(Rc<Statement>),
// /// Exists so that we can resolve local variable references to a node ID
// LetStatement(Rc<LetStatement>),
// Type(Rc<Type>),
// PathSegment(Rc<PathSegment>),

use std::rc::Rc;

use super::{
    Block, Body, BodyId, Expression, ExpressionKind, FunctionParameter, FunctionSignature,
    Identifier, Item, ItemKind, LetStatement, Literal, Module, OwnerNode, Path, PathSegment,
    Statement, StatementKind, Type, TypeKind,
};

pub trait Visitor: Sized {
    fn visit_item(&mut self, item: Rc<Item>) {
        walk_item(self, item)
    }

    fn visit_function_definition(
        &mut self,
        name: &Identifier,
        signature: &FunctionSignature,
        body: BodyId,
    ) {
        walk_function_definition(self, name, signature, body)
    }

    fn visit_identifier(&mut self, _identifier: &Identifier) {}

    fn visit_function_signature(&mut self, signature: &FunctionSignature) {
        walk_function_signature(self, signature)
    }

    fn visit_function_parameter(&mut self, parameter: Rc<FunctionParameter>) {
        walk_function_parameter(self, parameter)
    }

    fn visit_type(&mut self, ty: Rc<Type>) {
        walk_type(self, ty)
    }

    fn visit_path(&mut self, path: &Path) {
        walk_path(self, path)
    }

    fn visit_path_segment(&mut self, segment: Rc<PathSegment>) {
        walk_path_segment(self, segment)
    }

    fn visit_body(&mut self, _body_id: BodyId) {
        panic!("must be overridden if used to allow resolving body ids")
    }

    fn visit_block(&mut self, block: Rc<Block>) {
        walk_block(self, block)
    }

    fn visit_statement(&mut self, statement: Rc<Statement>) {
        walk_statement(self, statement)
    }

    fn visit_let_statement(&mut self, let_stmt: Rc<LetStatement>) {
        walk_let_statement(self, let_stmt)
    }

    fn visit_expression(&mut self, expression: Rc<Expression>) {
        walk_expression(self, expression)
    }

    fn visit_literal(&mut self, _literal: &Literal) {}
}

pub fn walk_module(visitor: &mut impl Visitor, module: &Module) {
    for owner in module.owners.iter() {
        match owner.node() {
            OwnerNode::Item(item) => {
                visitor.visit_item(item);
            }
        }
    }
}

pub fn walk_item(visitor: &mut impl Visitor, item: Rc<Item>) {
    match &item.kind {
        ItemKind::Function {
            name,
            signature,
            body,
        } => visitor.visit_function_definition(name, signature, *body),
    }
}

pub fn walk_function_definition(
    visitor: &mut impl Visitor,
    name: &Identifier,
    signature: &FunctionSignature,
    body: BodyId,
) {
    visitor.visit_identifier(name);
    visitor.visit_function_signature(signature);
    visitor.visit_body(body);
}

pub fn walk_function_signature(visitor: &mut impl Visitor, signature: &FunctionSignature) {
    for ty in signature.parameters.iter() {
        visitor.visit_type(ty.clone());
    }

    if let Some(ty) = &signature.variadic_type {
        visitor.visit_type(ty.clone());
    }

    if let Some(ty) = &signature.return_type {
        visitor.visit_type(ty.clone());
    }
}

pub fn walk_function_parameter(visitor: &mut impl Visitor, parameter: Rc<FunctionParameter>) {
    visitor.visit_identifier(&parameter.name);
}

pub fn walk_type(visitor: &mut impl Visitor, ty: Rc<Type>) {
    match &ty.kind {
        TypeKind::Path(path) => visitor.visit_path(&path),
        TypeKind::Pointer(ty) => visitor.visit_type(ty.clone()),
        TypeKind::Slice(ty) => visitor.visit_type(ty.clone()),
        TypeKind::Array { ty, .. } => visitor.visit_type(ty.clone()),
        TypeKind::FunctionPointer {
            parameters,
            return_type,
            ..
        } => {
            for param in parameters.iter() {
                visitor.visit_type(param.clone())
            }

            if let Some(ty) = return_type {
                visitor.visit_type(ty.clone());
            }
        }
        TypeKind::Any => {}
    }
}

pub fn walk_path(visitor: &mut impl Visitor, path: &Path) {
    for segment in path.segments.iter() {
        visitor.visit_path_segment(segment.clone())
    }
}

pub fn walk_path_segment(visitor: &mut impl Visitor, segment: Rc<PathSegment>) {
    visitor.visit_identifier(&segment.identifier);
}

pub fn walk_body(visitor: &mut impl Visitor, body: Rc<Body>) {
    for param in body.params.iter() {
        visitor.visit_function_parameter(param.clone());
    }

    visitor.visit_block(body.block.clone());
}

pub fn walk_block(visitor: &mut impl Visitor, block: Rc<Block>) {
    for statement in block.statements.iter() {
        visitor.visit_statement(statement.clone());
    }

    if let Some(e) = &block.expression {
        visitor.visit_expression(e.clone());
    }
}

pub fn walk_statement(visitor: &mut impl Visitor, statement: Rc<Statement>) {
    match &statement.kind {
        StatementKind::Let(let_stmt) => visitor.visit_let_statement(let_stmt.clone()),
        StatementKind::BareExpression(expression) => visitor.visit_expression(expression.clone()),
        StatementKind::SemiExpression(expression) => visitor.visit_expression(expression.clone()),
    }
}

pub fn walk_let_statement(visitor: &mut impl Visitor, let_statement: Rc<LetStatement>) {
    visitor.visit_identifier(&let_statement.name);

    if let Some(ty) = &let_statement.ty {
        visitor.visit_type(ty.clone());
    }

    if let Some(e) = &let_statement.initializer {
        visitor.visit_expression(e.clone());
    }
}

pub fn walk_expression(visitor: &mut impl Visitor, expression: Rc<Expression>) {
    match &expression.kind {
        ExpressionKind::Literal(literal) => visitor.visit_literal(literal),
        ExpressionKind::Path(path) => visitor.visit_path(path),
        ExpressionKind::Block(block) => visitor.visit_block(block.clone()),
        ExpressionKind::FunctionCall { target, arguments } => {
            visitor.visit_expression(target.clone());

            for arg in arguments.iter() {
                visitor.visit_expression(arg.clone());
            }
        }
        ExpressionKind::Binary { lhs, rhs, .. } => {
            visitor.visit_expression(lhs.clone());
            visitor.visit_expression(rhs.clone());
        }
        ExpressionKind::Unary { operand, .. } => visitor.visit_expression(operand.clone()),
        ExpressionKind::Cast { expression, ty } => {
            visitor.visit_expression(expression.clone());
            visitor.visit_type(ty.clone());
        }
        ExpressionKind::If {
            condition,
            positive,
            negative,
        } => {
            visitor.visit_expression(condition.clone());
            visitor.visit_block(positive.clone());

            if let Some(n) = &negative {
                visitor.visit_expression(n.clone());
            }
        }
        ExpressionKind::While { condition, block } => {
            visitor.visit_expression(condition.clone());
            visitor.visit_block(block.clone());
        }
        ExpressionKind::Assignment { lhs, rhs } => {
            visitor.visit_expression(lhs.clone());
            visitor.visit_expression(rhs.clone());
        }
        ExpressionKind::OperatorAssignment { lhs, rhs, .. } => {
            visitor.visit_expression(lhs.clone());
            visitor.visit_expression(rhs.clone());
        }
        ExpressionKind::Break => {}
        ExpressionKind::Continue => {}
        ExpressionKind::Return(expression) => {
            if let Some(e) = &expression {
                visitor.visit_expression(e.clone())
            }
        }
    }
}
