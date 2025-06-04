use std::{collections::BTreeMap, rc::Rc};

use crate::{
    frontend::ast,
    index::{Index, IndexVec},
    middle::hir::{self, visit::Visitor},
};

/// Pulls out the items from the AST and indexes them based on their assigned
/// local def ID
pub fn index_ast<'ast>(
    node_to_def_id_map: &BTreeMap<ast::NodeId, hir::LocalDefId>,
    module: &'ast ast::Module,
) -> IndexVec<hir::LocalDefId, &'ast ast::Item> {
    let mut indexer = AstIndexer {
        node_to_def_id_map,
        index: BTreeMap::new(),
    };
    ast::visit::walk_module(&mut indexer, module);

    let mut res = IndexVec::new();

    for (def_id, item) in indexer.index {
        assert_eq!(def_id, res.next_index());
        res.push(item);
    }

    res
}

pub struct AstIndexer<'a, 'ast> {
    node_to_def_id_map: &'a BTreeMap<ast::NodeId, hir::LocalDefId>,
    index: BTreeMap<hir::LocalDefId, &'ast ast::Item>,
}

impl<'a, 'ast> ast::visit::Visitor<'ast> for AstIndexer<'a, 'ast> {
    fn visit_item(&mut self, item: &'ast ast::Item) {
        let def_id = *self.node_to_def_id_map.get(&item.id).unwrap();
        self.index.insert(def_id, item);
    }
}

pub fn index_hir(
    node: &hir::OwnerNode,
    node_count: usize,
    body: Option<Rc<hir::Body>>,
) -> (
    IndexVec<hir::ItemLocalId, hir::ParentedNode>,
    BTreeMap<hir::LocalDefId, hir::ItemLocalId>,
) {
    let mut indexer = HirIndexer {
        nodes: BTreeMap::new(),
        parenting: BTreeMap::new(),
        parent_node: hir::ItemLocalId::INVALID,
        owner: node.hir_id().owner,
        body,
    };

    match node {
        hir::OwnerNode::Item(item) => indexer.visit_item(item.clone()),
    }

    // collect map into index vec

    let mut index = IndexVec::new();

    for (local_id, node) in indexer.nodes {
        assert_eq!(
            local_id,
            index.next_index(),
            "missed node id during indexing"
        );
        index.push(node);
    }

    assert_eq!(
        index.next_index().index(),
        node_count,
        "less nodes indexed than expected"
    );

    (index, indexer.parenting)
}

pub struct HirIndexer {
    nodes: BTreeMap<hir::ItemLocalId, hir::ParentedNode>,
    parenting: BTreeMap<hir::LocalDefId, hir::ItemLocalId>,

    /// The parent of this node
    parent_node: hir::ItemLocalId,

    owner: hir::LocalDefId,
    body: Option<Rc<hir::Body>>,
}

impl HirIndexer {
    fn insert(&mut self, hir_id: hir::HirId, node: hir::Node) {
        self.nodes.insert(
            hir_id.local_id,
            hir::ParentedNode {
                parent: self.parent_node,
                node,
            },
        );
    }

    fn with_parent(&mut self, parent_id: hir::HirId, f: impl FnOnce(&mut Self)) {
        assert_eq!(parent_id.owner, self.owner);

        let parent_node = self.parent_node;
        self.parent_node = parent_id.local_id;
        f(self);
        self.parent_node = parent_node;
    }
}

impl hir::visit::Visitor for HirIndexer {
    fn visit_body(&mut self, body_id: hir::BodyId) {
        let Some(body) = &self.body else {
            unreachable!()
        };

        assert_eq!(body.id(), body_id);

        hir::visit::walk_body(self, body.clone());
    }

    fn visit_item(&mut self, item: Rc<hir::Item>) {
        assert_eq!(self.nodes.len(), 0);
        assert_eq!(self.parent_node, hir::ItemLocalId::INVALID);

        self.insert(item.hir_id(), hir::Node::Item(item.clone()));
        self.with_parent(item.hir_id(), |this| {
            hir::visit::walk_item(this, item);
        });
    }

    fn visit_function_parameter(&mut self, parameter: Rc<hir::FunctionParameter>) {
        self.insert(parameter.hir_id, hir::Node::FunctionParameter(parameter));
    }

    fn visit_expression(&mut self, expression: Rc<hir::Expression>) {
        self.insert(expression.hir_id, hir::Node::Expression(expression.clone()));
        self.with_parent(expression.hir_id, |this| {
            hir::visit::walk_expression(this, expression);
        });
    }

    fn visit_block(&mut self, block: Rc<hir::Block>, _context: hir::visit::BlockContext) {
        self.insert(block.hir_id, hir::Node::Block(block.clone()));
        self.with_parent(block.hir_id, |this| {
            hir::visit::walk_block(this, block);
        });
    }

    fn visit_statement(&mut self, statement: Rc<hir::Statement>) {
        self.insert(statement.hir_id, hir::Node::Statement(statement.clone()));
        self.with_parent(statement.hir_id, |this| {
            hir::visit::walk_statement(this, statement);
        });
    }

    fn visit_let_statement(&mut self, let_stmt: Rc<hir::LetStatement>) {
        self.insert(let_stmt.hir_id, hir::Node::LetStatement(let_stmt.clone()));
        self.with_parent(let_stmt.hir_id, |this| {
            hir::visit::walk_let_statement(this, let_stmt);
        });
    }

    fn visit_type(&mut self, ty: Rc<hir::Type>) {
        self.insert(ty.hir_id, hir::Node::Type(ty.clone()));
        self.with_parent(ty.hir_id, |this| {
            hir::visit::walk_type(this, ty);
        });
    }

    fn visit_path_segment(&mut self, segment: Rc<hir::PathSegment>) {
        self.insert(segment.hir_id, hir::Node::PathSegment(segment.clone()));
        self.with_parent(segment.hir_id, |this| {
            hir::visit::walk_path_segment(this, segment);
        });
    }
}
