use std::collections::{BTreeMap, BTreeSet, VecDeque};

use crate::{
    backend::lir::{self, BlockId, Instruction},
    index::{Index, IndexVec},
    middle::{hir, ty, type_check::ModuleTypeCheckResults},
};

struct LirLowereringContext<'hir> {
    module: &'hir hir::Module,
    type_map: &'hir ModuleTypeCheckResults,
    owner_id: hir::LocalDefId,

    register_map: IndexVec<lir::RegisterId, lir::Register>,
    local_to_register_map: BTreeMap<hir::ItemLocalId, lir::RegisterId>,
    expression_to_register_map: BTreeMap<hir::ItemLocalId, lir::RegisterId>,
    arguments: Vec<lir::RegisterId>,

    block_map: IndexVec<lir::BlockId, lir::Block>,
    block_stack: VecDeque<lir::BlockId>,
}

impl<'hir> LirLowereringContext<'hir> {
    fn create_register(&mut self, ty: ty::Type) -> lir::RegisterId {
        let id = self.register_map.next_index();
        self.register_map.push(lir::Register { id, ty })
    }

    fn create_block(&mut self) -> lir::BlockId {
        let id = self.block_map.next_index();
        self.block_map.push(lir::Block {
            id,
            instructions: Vec::new(),
            predecessors: BTreeSet::new(),
        })
    }

    fn push_instruction(&mut self, instruction: lir::Instruction) {
        let current_block = self.block_stack.back().unwrap();
        self.block_map[*current_block]
            .instructions
            .push(instruction);
    }

    fn into_output(self) -> lir::FunctionDefinition {
        let hir::ItemKind::Function { name, .. } = &self
            .module
            .get_owner(self.owner_id)
            .node()
            .as_item()
            .unwrap()
            .kind;

        lir::FunctionDefinition {
            symbol_name: name.symbol,
            registers: self.register_map.into_entries().collect(),
            arguments: self.arguments,
            blocks: self.block_map.into_entries().collect(),
        }
    }
}

impl<'hir> hir::visit::Visitor for LirLowereringContext<'hir> {
    fn visit_function_definition(
        &mut self,
        _name: &hir::Identifier,
        signature: &hir::FunctionSignature,
        body: hir::BodyId,
    ) {
        let body = self.module.get_body(body);

        for (name, ty) in body.params.iter().zip(signature.parameters.iter()) {
            let ty = self.type_map.get_type(ty.hir_id);
            let id = self.create_register(ty);
            self.local_to_register_map.insert(name.hir_id.local_id, id);
            self.arguments.push(id);
        }

        let block_id = self.create_block();
        self.block_stack.push_back(block_id);

        hir::visit::walk_body(self, body);

        let current_block = lir::BlockId::new(self.block_map.len() - 1);
        self.block_map[current_block]
            .instructions
            .push(lir::Instruction::Return { value: None });
    }

    fn visit_let_statement(&mut self, let_stmt: std::rc::Rc<hir::LetStatement>) {
        hir::visit::walk_let_statement(self, let_stmt.clone());

        let ty = self.type_map.get_type(let_stmt.hir_id);

        if let Some(init) = &let_stmt.initializer {
            let reg = self.expression_to_register_map[&init.hir_id.local_id];
            self.local_to_register_map
                .insert(let_stmt.hir_id.local_id, reg);
        } else {
            let reg = self.create_register(ty);
            self.local_to_register_map
                .insert(let_stmt.hir_id.local_id, reg);
        }
    }

    fn visit_expression(&mut self, expression: std::rc::Rc<hir::Expression>) {
        match &expression.kind {
            hir::ExpressionKind::Literal(literal) => {
                let value = match literal {
                    hir::Literal::Boolean(v) => lir::Immediate::Bool(*v),
                    hir::Literal::Char(v) => lir::Immediate::Int(*v as u64),
                    hir::Literal::Integer(v, _) => lir::Immediate::Int(*v),
                    hir::Literal::Float(..) => todo!("load float"),
                    hir::Literal::String(_) => {
                        todo!("load string (need to allocate in static mem)")
                    }
                    hir::Literal::ByteString(_) => {
                        todo!("load byte string (need to allocate in static mem)")
                    }
                    hir::Literal::CString(_) => {
                        todo!("load c string (need to allocate in static mem)")
                    }
                };

                let ty = self.type_map.get_type(expression.hir_id);
                let reg = self.create_register(ty);

                self.push_instruction(Instruction::Move {
                    destination: reg,
                    source: lir::Operand::Immediate(value),
                });
                self.expression_to_register_map
                    .insert(expression.hir_id.local_id, reg);
            }
            hir::ExpressionKind::Path(path) => {
                hir::visit::walk_expression(self, expression.clone());

                let reg =
                    self.expression_to_register_map[&path.segments.last().unwrap().hir_id.local_id];
                self.expression_to_register_map
                    .insert(expression.hir_id.local_id, reg);
            }
            hir::ExpressionKind::Block(block) => {
                hir::visit::walk_expression(self, expression.clone());

                if let Some(reg) = self.expression_to_register_map.get(&block.hir_id.local_id) {
                    self.expression_to_register_map
                        .insert(expression.hir_id.local_id, *reg);
                }
            }
            hir::ExpressionKind::Tuple(expressions) => todo!(),
            hir::ExpressionKind::FunctionCall { target, arguments } => todo!(),
            hir::ExpressionKind::Binary { lhs, operator, rhs } => {
                hir::visit::walk_expression(self, expression.clone());

                let ty = self.type_map.get_type(expression.hir_id);
                let reg = self.create_register(ty);

                let lhs = self.expression_to_register_map[&lhs.hir_id.local_id];
                let rhs = self.expression_to_register_map[&rhs.hir_id.local_id];

                self.push_instruction(Instruction::BinaryOperation {
                    operator: *operator,
                    destination: reg,
                    lhs: lir::Operand::Register(lhs),
                    rhs: lir::Operand::Register(rhs),
                });

                self.expression_to_register_map
                    .insert(expression.hir_id.local_id, reg);
            }
            hir::ExpressionKind::Unary { operator, operand } => todo!(),
            hir::ExpressionKind::Cast { expression, ty } => todo!(),
            hir::ExpressionKind::If {
                condition,
                positive,
                negative,
            } => {
                self.visit_expression(condition.clone());
                let condition = self.expression_to_register_map[&condition.hir_id.local_id];

                let ty = self.type_map.get_type(expression.hir_id);

                let mut destination_register = None;

                // If this conditional has a return value, allocate a register
                // for it and set it in the context so that we know which
                // register to put the block result in later
                if !ty.is_unit() && !ty.is_never() {
                    let reg = self.create_register(ty);
                    destination_register = Some(reg);

                    self.expression_to_register_map
                        .insert(expression.hir_id.local_id, reg);
                }

                // For if expressions, there are 2 possible cases. In the first
                // case where there is no else, we allocate a new block for the
                // positive branch and a new block to act as both the negative
                // fallthrugh and the merge point. In the second case where
                // there is an else, we allocate a new block for the positive
                // branch, a new block for the negative branch, and a new block
                // for the merge point.

                let current_block_id = *self.block_stack.back().unwrap();

                let positive_block_id = self.create_block();
                self.block_map[positive_block_id]
                    .predecessors
                    .insert(current_block_id);

                let positive_branch_last_block: BlockId;
                {
                    self.block_stack.push_back(positive_block_id);
                    self.visit_block(positive.clone(), hir::visit::BlockContext::Scope);
                    self.block_stack.pop_back();

                    // the most recently created block is the block we need to
                    // insert the merge jump into. if no blocks were created
                    // while visiting the subexpression, its still the current
                    // block.
                    positive_branch_last_block = lir::BlockId::new(self.block_map.len() - 1);

                    // assign the destination register by inserting a move
                    if let Some(destination) = destination_register {
                        let source = self.expression_to_register_map[&positive.hir_id.local_id];

                        self.block_map[positive_branch_last_block]
                            .instructions
                            .push(lir::Instruction::Move {
                                destination,
                                source: lir::Operand::Register(source),
                            });
                    }
                }

                let mut merge_block_id = self.create_block();
                let negative_block_id = if let Some(n) = &negative {
                    // allocate a negative branch block before the merge branch
                    let negative_branch_block_id = merge_block_id;

                    self.block_map[negative_branch_block_id]
                        .predecessors
                        .insert(current_block_id);

                    self.block_stack.push_back(negative_branch_block_id);
                    self.visit_expression(n.clone());
                    self.block_stack.pop_back();

                    let last_inserted_block = lir::BlockId::new(self.block_map.len() - 1);

                    // assign the destination register by inserting a move
                    if let Some(destination) = destination_register {
                        let source = self.expression_to_register_map[&n.hir_id.local_id];

                        self.block_map[last_inserted_block].instructions.push(
                            lir::Instruction::Move {
                                destination,
                                source: lir::Operand::Register(source),
                            },
                        );
                    }

                    merge_block_id = self.create_block();

                    // insert unconditional jump in the negative branch to the
                    // allocated merge block if the branch does not return
                    if !self.block_map[last_inserted_block].returns() {
                        self.block_map[last_inserted_block].instructions.push(
                            lir::Instruction::Jump {
                                destination: merge_block_id,
                            },
                        );
                        self.block_map[merge_block_id]
                            .predecessors
                            .insert(last_inserted_block);
                    }

                    negative_branch_block_id
                } else {
                    // in this case the negative fallthrough is the same as the
                    // merge block id
                    merge_block_id
                };

                // insert unconditional jump in the postive branch to the
                // allocated merge block if the branch does not return
                if !self.block_map[positive_branch_last_block].returns() {
                    self.block_map[positive_branch_last_block]
                        .instructions
                        .push(lir::Instruction::Jump {
                            destination: merge_block_id,
                        });
                    self.block_map[merge_block_id]
                        .predecessors
                        .insert(positive_branch_last_block);
                }

                self.block_map[current_block_id]
                    .instructions
                    .push(Instruction::Branch {
                        condition: lir::Operand::Register(condition),
                        positive: positive_block_id,
                        negative: negative_block_id,
                    });

                self.block_stack.pop_back();
                self.block_stack.push_back(merge_block_id);
            }
            hir::ExpressionKind::While { condition, block } => todo!(),
            hir::ExpressionKind::Assignment { lhs, rhs } => {
                hir::visit::walk_expression(self, expression.clone());

                let lhs = self.expression_to_register_map[&lhs.hir_id.local_id];
                let rhs = self.expression_to_register_map[&rhs.hir_id.local_id];

                self.push_instruction(lir::Instruction::Move {
                    destination: lhs,
                    source: lir::Operand::Register(rhs),
                });
            }
            hir::ExpressionKind::OperatorAssignment { operator, lhs, rhs } => todo!(),
            hir::ExpressionKind::Break => todo!(),
            hir::ExpressionKind::Continue => todo!(),
            hir::ExpressionKind::Return(value) => {
                hir::visit::walk_expression(self, expression.clone());

                let value = value
                    .as_ref()
                    .map(|e| self.expression_to_register_map[&e.hir_id.local_id])
                    .map(lir::Operand::Register);

                self.push_instruction(lir::Instruction::Return { value });
            }
        }
    }

    fn visit_path_segment(&mut self, segment: std::rc::Rc<hir::PathSegment>) {
        match &segment.resolution {
            hir::Resolution::Definition(definition_kind, local_def_id) => todo!(),
            hir::Resolution::Local(local_id) => {
                let reg = self.local_to_register_map[local_id];
                self.expression_to_register_map
                    .insert(segment.hir_id.local_id, reg);
            }
            hir::Resolution::IntrinsicFunction(interned_symbol) => todo!(),
            hir::Resolution::Primitive(primitive_kind) => {}
        }
    }
}

pub fn lower_to_lir(module: &hir::Module, type_map: &ModuleTypeCheckResults) -> lir::Module {
    let mut function_definitions = BTreeMap::new();

    for owner_id in module.get_owners() {
        let mut ctx = LirLowereringContext {
            module,
            owner_id,
            type_map,
            register_map: IndexVec::new(),
            arguments: Vec::new(),
            block_map: IndexVec::new(),
            block_stack: VecDeque::new(),
            local_to_register_map: BTreeMap::new(),
            expression_to_register_map: BTreeMap::new(),
        };

        let hir::OwnerNode::Item(item) = module.get_owner(owner_id).node();
        hir::visit::walk_item(&mut ctx, item);

        function_definitions.insert(owner_id, ctx.into_output());
    }

    lir::Module {
        function_definitions,
    }
}
