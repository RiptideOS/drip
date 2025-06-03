//! This module contains all the code related to lowering an AST into HIR
//!
//! This involves indexing the AST and resolving all names within types and
//! function bodies

use std::{collections::BTreeMap, rc::Rc};

use self::index::{index_ast, index_hir};
use super::resolve::{ResolutionMap, Resolver};
use crate::{
    frontend::{ast, lexer::Span},
    index::{Index, IndexVec},
    middle::{hir, primitive::UIntKind},
};

mod index;

pub struct ItemLoweringContext<'a, 'ast> {
    // Global refs
    module: &'ast ast::Module<'ast>,
    resolver: &'a ResolutionMap,

    // Context specific to this owner
    owner_id: hir::LocalDefId,
    next_local_id: hir::ItemLocalId,
    body: Option<Rc<hir::Body>>,
    /// Maps IDs of local (let) bindings to their allocated hir item local ids
    local_id_map: BTreeMap<ast::NodeId, hir::ItemLocalId>,
}

impl<'a, 'ast> ItemLoweringContext<'a, 'ast> {
    fn new(
        module: &'ast ast::Module<'ast>,
        resolver: &'a ResolutionMap,
        owner_id: hir::LocalDefId,
    ) -> Self {
        Self {
            module,
            resolver,
            owner_id,
            next_local_id: hir::ItemLocalId::new(1),
            body: None,
            local_id_map: BTreeMap::new(),
        }
    }

    fn next_id(&mut self) -> hir::HirId {
        assert_ne!(self.next_local_id, hir::ItemLocalId::ZERO);
        let id = hir::HirId::new(self.owner_id, self.next_local_id);
        self.next_local_id.increment_by(1);
        id
    }

    fn set_body(&mut self, body: hir::Body) -> hir::BodyId {
        assert!(self.body.is_none(), "tried to set body more than once");

        let body_id = body.id();
        self.body = Some(Rc::new(body));
        body_id
    }

    fn lower_item(&mut self, item: &'ast ast::Item) -> Rc<hir::Item> {
        let kind = match &item.kind {
            ast::ItemKind::FunctionDefinition(f) => {
                let signature = self.lower_function_signature(&f.signature);

                // NOTE: must lower parameters first to bind names
                let params = self.lower_function_parameters(&f.signature.parameters);
                let block = self.lower_block(&f.body);

                let body = self.set_body(hir::Body { params, block });

                hir::ItemKind::Function {
                    name: self.lower_ident(&f.signature.name),
                    signature,
                    body,
                }
            }
        };

        Rc::new(hir::Item {
            owner_id: self.owner_id,
            kind,
            span: item.span,
        })
    }

    fn lower_function_signature(
        &mut self,
        signature: &'ast ast::FunctionSignature,
    ) -> hir::FunctionSignature {
        hir::FunctionSignature {
            parameters: self.lower_function_parameters_as_types(&signature.parameters),
            variadic_type: None, // TODO
            return_type: signature.return_type.as_ref().map(|ty| self.lower_type(ty)),
            span: signature.span,
        }
    }

    fn lower_ident(&mut self, ident: &'ast ast::Identifier) -> hir::Identifier {
        hir::Identifier {
            symbol: ident.symbol,
            span: ident.span,
        }
    }

    fn lower_function_parameters_as_types(
        &mut self,
        params: &'ast ast::FunctionParameterList,
    ) -> Rc<[Rc<hir::Type>]> {
        params
            .parameters
            .iter()
            .map(|param| self.lower_type(&param.ty))
            .collect()
    }

    fn lower_type(&mut self, ty: &'ast ast::Type) -> Rc<hir::Type> {
        let kind = match &ty.kind {
            ast::TypeKind::QualifiedIdentifier(qualified_identifier) => {
                // There are 2 possibilities here:
                //   1) The identifier only has one segment and must be a
                //      primitive or local/imported custom type (alias, struct, enum,
                //      etc.). This can be resolved by checking if it's a primitive
                //      and then checking the global scope if that fails
                //  2) The identifier has more than one segment and we must start
                //      from the first and resolve from there

                let mut segments = Vec::new();

                if let [identifier] = qualified_identifier.segments.as_slice() {
                    let resolution = self
                        .resolver
                        .type_name_resolutions
                        .get(&identifier.id)
                        .expect("type identifier had no resolution");

                    segments.push(Rc::new(hir::PathSegment {
                        hir_id: self.next_id(),
                        span: identifier.span,
                        identifier: self.lower_ident(identifier),
                        resolution: self.lower_resolution(resolution),
                    }));
                } else {
                    todo!("Resolve identifiers with multiple segments")
                }

                hir::TypeKind::Path(hir::Path {
                    segments: segments.into(),
                    span: qualified_identifier.span,
                })
            }
            ast::TypeKind::Pointer(ty) => hir::TypeKind::Pointer(self.lower_type(ty)),
            ast::TypeKind::Slice(ty) => hir::TypeKind::Slice(self.lower_type(ty)),
            ast::TypeKind::Array { ty, length } => {
                let ty = self.lower_type(ty);
                let length = match length.kind {
                    ast::LiteralKind::Integer => length
                        .symbol
                        .value()
                        .parse()
                        // TODO: handle errors here
                        .expect("Failed to parse array length"),
                    _ => {
                        self.report_error(length.span, "Array length must be an integer literal");
                    }
                };

                hir::TypeKind::Array { ty, length }
            }
            ast::TypeKind::Any => hir::TypeKind::Any,
        };

        Rc::new(hir::Type {
            hir_id: self.next_id(),
            kind,
            span: ty.span,
        })
    }

    fn lower_resolution(&mut self, resolution: &hir::Resolution<ast::NodeId>) -> hir::Resolution {
        match resolution {
            hir::Resolution::Definition(definition_kind, local_def_id) => {
                hir::Resolution::Definition(*definition_kind, *local_def_id)
            }
            hir::Resolution::Local(node_id) => hir::Resolution::Local(
                *self
                    .local_id_map
                    .get(node_id)
                    .expect("node id for local (let) binding was not found"),
            ),
            hir::Resolution::IntrinsicFunction => hir::Resolution::IntrinsicFunction,
            hir::Resolution::Primitive(primitive_kind) => {
                hir::Resolution::Primitive(*primitive_kind)
            }
        }
    }

    /// Lowers the function parameter and binds all the names into the current
    /// value resolution scope
    fn lower_function_parameters(
        &mut self,
        params: &'ast ast::FunctionParameterList,
    ) -> Rc<[Rc<hir::FunctionParameter>]> {
        let params: Rc<[_]> = params
            .parameters
            .iter()
            .map(|p| {
                let param = hir::FunctionParameter {
                    hir_id: self.next_id(),
                    name: self.lower_ident(&p.name),
                    ty_span: p.ty.span,
                    span: p.span,
                };

                self.local_id_map.insert(p.id, param.hir_id.local_id);

                param
            })
            .map(Rc::new)
            .collect();

        params
    }

    fn lower_block(&mut self, block: &'ast ast::Block) -> Rc<hir::Block> {
        let (statements, expr) = self.lower_statements(&block.statements);

        Rc::new(hir::Block {
            hir_id: self.next_id(),
            statements,
            expression: expr,
            is_const: false, // TODO: constexpr
            span: block.span,
        })
    }

    /// Lowers the provided statement unless it is an empty statement, in which
    /// case None is returned (we discard these during lowering)
    fn lower_statements(
        &mut self,
        statements: &'ast [ast::Statement],
    ) -> (Rc<[Rc<hir::Statement>]>, Option<Rc<hir::Expression>>) {
        let len = statements.len();

        let mut result = Vec::new();
        let mut expr = None;

        for (i, statement) in statements.iter().enumerate() {
            let kind = match &statement.kind {
                ast::StatementKind::Local(local) => {
                    let initializer = match &local.kind {
                        ast::LocalKind::Declaration => None,
                        ast::LocalKind::Initialization(expression) => {
                            Some(self.lower_expression(expression))
                        }
                    };

                    let let_stmt = hir::LetStatement {
                        hir_id: self.next_id(),
                        is_mutable: local.is_mutable,
                        name: self.lower_ident(&local.name),
                        ty: local.ty.as_ref().map(|ty| self.lower_type(ty)),
                        initializer,
                        span: local.span,
                    };

                    self.local_id_map.insert(local.id, let_stmt.hir_id.local_id);

                    hir::StatementKind::Let(Rc::new(let_stmt))
                }
                ast::StatementKind::BareExpr(expression) => {
                    let expression = self.lower_expression(expression);

                    if i == len - 1 {
                        expr = Some(expression);
                        break;
                    }

                    hir::StatementKind::BareExpression(expression)
                }
                ast::StatementKind::SemiExpr(expression) => {
                    hir::StatementKind::SemiExpression(self.lower_expression(expression))
                }
                ast::StatementKind::Empty => continue,
            };

            result.push(Rc::new(hir::Statement {
                hir_id: self.next_id(),
                kind,
                span: statement.span,
            }));
        }

        (result.into(), expr)
    }

    fn lower_expression(&mut self, expression: &'ast ast::Expression) -> Rc<hir::Expression> {
        let kind = match &expression.kind {
            ast::ExpressionKind::Literal(literal) => {
                hir::ExpressionKind::Literal(self.lower_literal(literal))
            }
            ast::ExpressionKind::QualifiedIdentifier(qualified_identifier) => {
                // There are 2 possibilities here:
                //   1) The ident has no qualifier and it refers to a local, function
                //      parameter, or local/imported definition
                //   2) The ident has a qualifier so we should start at the first segment
                //      and resolve from there

                let mut segments = Vec::new();

                if let [identifier] = qualified_identifier.segments.as_slice() {
                    let resolution = self
                        .resolver
                        .value_name_resolutions
                        .get(&identifier.id)
                        .expect("value identifier had no resolution");

                    segments.push(Rc::new(hir::PathSegment {
                        hir_id: self.next_id(),
                        span: identifier.span,
                        identifier: self.lower_ident(identifier),
                        resolution: self.lower_resolution(resolution),
                    }));
                } else {
                    todo!("resolve identifier expressions with multiple segments")
                }

                hir::ExpressionKind::Path(hir::Path {
                    segments: segments.into(),
                    span: qualified_identifier.span,
                })
            }
            ast::ExpressionKind::Grouping(expression) => return self.lower_expression(expression),
            ast::ExpressionKind::Block(block) => {
                hir::ExpressionKind::Block(self.lower_block(block))
            }
            ast::ExpressionKind::FunctionCall { target, arguments } => {
                hir::ExpressionKind::FunctionCall {
                    target: self.lower_expression(target),
                    arguments: self.lower_function_call_argument_list(arguments),
                }
            }
            ast::ExpressionKind::Binary { lhs, operator, rhs } => hir::ExpressionKind::Binary {
                lhs: self.lower_expression(lhs),
                operator: operator.kind,
                rhs: self.lower_expression(rhs),
            },
            ast::ExpressionKind::Unary { operator, operand } => hir::ExpressionKind::Unary {
                operator: operator.kind,
                operand: self.lower_expression(operand),
            },
            ast::ExpressionKind::Cast { expression, ty } => hir::ExpressionKind::Cast {
                expression: self.lower_expression(expression),
                ty: self.lower_type(ty),
            },
            ast::ExpressionKind::If {
                condition,
                positive,
                negative,
            } => hir::ExpressionKind::If {
                condition: self.lower_expression(condition),
                positive: self.lower_block(positive),
                negative: negative.as_ref().map(|e| self.lower_expression(e)),
            },
            ast::ExpressionKind::While { condition, block } => hir::ExpressionKind::While {
                condition: self.lower_expression(condition),
                block: self.lower_block(block),
            },
            ast::ExpressionKind::Assignment { lhs, rhs } => hir::ExpressionKind::Assignment {
                lhs: self.lower_expression(lhs),
                rhs: self.lower_expression(rhs),
            },
            ast::ExpressionKind::OperatorAssignment { operator, lhs, rhs } => {
                hir::ExpressionKind::OperatorAssignment {
                    operator: operator.kind,
                    lhs: self.lower_expression(lhs),
                    rhs: self.lower_expression(rhs),
                }
            }
            ast::ExpressionKind::Break => hir::ExpressionKind::Break,
            ast::ExpressionKind::Continue => hir::ExpressionKind::Continue,
            ast::ExpressionKind::Return(expression) => {
                hir::ExpressionKind::Return(expression.as_ref().map(|e| self.lower_expression(e)))
            }
        };

        Rc::new(hir::Expression {
            hir_id: self.next_id(),
            kind,
            span: expression.span,
        })
    }

    fn lower_literal(&mut self, literal: &'ast ast::Literal) -> hir::Literal {
        // FIXME: it feels like a lot of the work in this function should
        // probably be moved to the parser, but to make the experience nicer we
        // should only do that if we can gracefully recover from errors like
        // integers being too large

        let value = literal.symbol.value();

        match literal.kind {
            ast::LiteralKind::Boolean => {
                hir::Literal::Boolean(value.parse().unwrap_or_else(|_| {
                    unreachable!("invalid boolean literal value in AST: {value}")
                }))
            }
            ast::LiteralKind::Byte => {
                // TODO: parse escaped byte chars like b'\n' which may be
                // multiple characters. should the parser do this for us?

                let v = &value[2..value.len() - 1];

                assert_eq!(v.chars().count(), 1);
                hir::Literal::Integer(
                    value.chars().next().unwrap() as _,
                    hir::LiteralIntegerKind::Unsigned(UIntKind::U8),
                )
            }
            ast::LiteralKind::Char => {
                // TODO: parse escaped chars like '\n' which may be multiple
                // characters. should the parser do this for us?

                let v = &value[1..value.len() - 1];

                assert_eq!(v.chars().count(), 1);
                hir::Literal::Char(value.chars().next().unwrap())
            }
            ast::LiteralKind::Integer => {
                let value = value
                    .parse::<u64>()
                    .expect("Failed to parse integer literal");

                // TODO: detect suffix (should parser do this?)
                hir::Literal::Integer(value, hir::LiteralIntegerKind::Unsuffixed)
            }
            ast::LiteralKind::Float => {
                // TODO: detect suffix (should parser do this?)
                hir::Literal::Float(literal.symbol, hir::LiteralFloatKind::Unsuffixed)
            }
            // TODO: parse out escaped chars? should the parser do this to
            // validate escape sequences? should this be a recoverable error?
            ast::LiteralKind::String => hir::Literal::String(literal.symbol),
            ast::LiteralKind::ByteString => hir::Literal::ByteString(value.as_bytes().into()),
            ast::LiteralKind::CString => hir::Literal::CString(value.as_bytes().into()),
        }
    }

    fn lower_function_call_argument_list(
        &mut self,
        arguments: &'ast ast::FunctionCallArgumentList,
    ) -> Rc<[Rc<hir::Expression>]> {
        arguments
            .arguments
            .iter()
            .map(|e| self.lower_expression(e))
            .collect()
    }

    fn report_error(&self, offending_span: Span, message: &str) -> ! {
        eprintln!(
            "{} ({}:{}:{})",
            message,
            self.module.source_file.origin,
            self.module
                .source_file
                .row_for_position(offending_span.start),
            self.module
                .source_file
                .column_for_position(offending_span.start)
        );
        self.module.source_file.highlight_span(offending_span);
        std::process::exit(1);
    }
}

struct ItemLowerer<'a, 'ast> {
    module: &'ast ast::Module<'ast>,
    ast_index: &'a IndexVec<hir::LocalDefId, &'ast ast::Item>,
    resolver: &'a ResolutionMap,
    owners: &'a mut IndexVec<hir::LocalDefId, hir::Owner>,
}

impl<'a, 'ast> ItemLowerer<'a, 'ast> {
    // Invokes the given lowering function using the provided ID to construct
    // new HIR nodes
    fn with_lctx(
        &mut self,
        owner_id: hir::LocalDefId,
        f: impl FnOnce(&mut ItemLoweringContext<'_, 'ast>) -> hir::OwnerNode,
    ) {
        let mut lctx = ItemLoweringContext::new(self.module, self.resolver, owner_id);

        // invoke the function after preparing the context for this owner
        let node = f(&mut lctx);

        let (nodes, parenting) = index_hir(&node, lctx.next_local_id.index(), lctx.body.clone());

        // store the resulting owner
        assert_eq!(self.owners.next_index(), owner_id);
        self.owners.push(hir::Owner {
            nodes,
            parenting,
            body: lctx.body,
        });
    }

    pub fn lower_node(&mut self, def_id: hir::LocalDefId) {
        let item = self.ast_index[def_id];

        self.with_lctx(def_id, |lctx| hir::OwnerNode::Item(lctx.lower_item(item)));
    }
}

pub fn lower_to_hir<'ast>(module: &'ast ast::Module<'ast>) -> hir::Module {
    let mut resolver = Resolver::new();
    resolver.resolve_module(module);
    let resolver = resolver.into_outputs();

    let index = index_ast(&resolver.node_to_def_id_map, module);
    let mut owners = IndexVec::new();

    let mut lowerer = ItemLowerer {
        module,
        ast_index: &index,
        resolver: &resolver,
        owners: &mut owners,
    };

    // lower nodes one at a time, resolving names and constructing HIR
    for def_id in index.indices() {
        lowerer.lower_node(def_id);
    }

    hir::Module { owners }
}
