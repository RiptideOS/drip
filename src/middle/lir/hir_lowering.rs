use std::{
    collections::{BTreeMap, BTreeSet, VecDeque},
    rc::Rc,
};

use hashbrown::HashSet;

use crate::{
    frontend::intern::InternedSymbol,
    index::{Index, IndexVec},
    middle::{
        hir,
        lir::{self, StaticLabelId},
        primitive::{IntKind, UIntKind},
        ty,
        type_check::ModuleTypeCheckResults,
    },
};

struct BodyLowereringContext<'hir> {
    module: &'hir hir::Module,
    type_map: &'hir ModuleTypeCheckResults,
    owner_id: hir::LocalDefId,
    symbol_name: InternedSymbol,

    next_static_label_id: &'hir mut StaticLabelId,
    static_strings: &'hir mut BTreeMap<lir::StaticLabelId, InternedSymbol>,
    static_c_strings: &'hir mut BTreeMap<lir::StaticLabelId, InternedSymbol>,

    register_map: IndexVec<lir::RegisterId, lir::Register>,
    local_to_register_map: BTreeMap<hir::ItemLocalId, lir::RegisterId>,
    expression_to_register_map: BTreeMap<hir::ItemLocalId, lir::RegisterId>,
    arguments: Vec<lir::RegisterId>,

    block_map: IndexVec<lir::BlockId, lir::Block>,
    block_stack: VecDeque<lir::BlockId>,
}

impl<'hir> BodyLowereringContext<'hir> {
    fn create_static_label_id(&mut self) -> lir::StaticLabelId {
        let prev = *self.next_static_label_id;
        self.next_static_label_id.increment_by(1);
        prev
    }

    fn create_register(&mut self, ty: ty::Type) -> lir::RegisterId {
        let id = self.register_map.next_index();
        let ty = self.lower_type(ty);
        self.register_map.push(lir::Register { id, ty })
    }

    fn create_register_with_lir_type(&mut self, ty: lir::Type) -> lir::RegisterId {
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
        lir::FunctionDefinition {
            symbol_name: self.symbol_name,
            registers: self.register_map.into_entries().collect(),
            arguments: self.arguments,
            blocks: self.block_map.into_entries().collect(),
        }
    }

    fn lower_type(&mut self, ty: ty::Type) -> lir::Type {
        //  match &*ty {
        //     ty::TypeKind::Integer(IntKind::I8)
        //     | ty::TypeKind::UnsignedInteger(UIntKind::U8) => {
        //         lir::IntegerWidth::I8
        //     }
        //     ty::TypeKind::Integer(IntKind::I16)
        //     | ty::TypeKind::UnsignedInteger(UIntKind::U16) => {
        //         lir::IntegerWidth::I16
        //     }
        //     ty::TypeKind::Integer(IntKind::I32)
        //     | ty::TypeKind::UnsignedInteger(UIntKind::U32) => {
        //         lir::IntegerWidth::I32
        //     }
        //     ty::TypeKind::Integer(IntKind::I64)
        //     | ty::TypeKind::UnsignedInteger(UIntKind::U64)
        //     | ty::TypeKind::Integer(IntKind::ISize)
        //     | ty::TypeKind::UnsignedInteger(UIntKind::USize) => {
        //         lir::IntegerWidth::I64
        //     }
        //     _ => unreachable!(),
        // }
        match &*ty {
            ty::TypeKind::Unit => todo!("what do we do here?"),
            ty::TypeKind::Bool => lir::Type::Integer(lir::IntegerWidth::I8),
            ty::TypeKind::Char => lir::Type::Integer(lir::IntegerWidth::I32),
            ty::TypeKind::Integer(int_kind) => lir::Type::Integer((*int_kind).into()),
            ty::TypeKind::UnsignedInteger(uint_kind) => lir::Type::Integer((*uint_kind).into()),
            ty::TypeKind::Float(float_kind) => lir::Type::Float((*float_kind).into()),
            ty::TypeKind::CStr | ty::TypeKind::Pointer(_) => lir::Type::Pointer,
            ty::TypeKind::Str | ty::TypeKind::Slice(_) => lir::Type::Struct(lir::Struct::slice()),
            ty::TypeKind::Array { ty, length } => {
                lir::Type::Array(Rc::new(self.lower_type(ty.clone())), *length)
            }
            ty::TypeKind::Tuple(items) => lir::Type::Struct(lir::Struct(
                items.iter().map(|ty| self.lower_type(ty.clone())).collect(),
            )),
            ty::TypeKind::FunctionPointer { .. } => lir::Type::Pointer,
            ty::TypeKind::Any => unreachable!("any should always be within a pointer type"),
            ty::TypeKind::Never | ty::TypeKind::Infer(_) | ty::TypeKind::Error => unreachable!(),
        }
    }
}

impl<'hir> hir::visit::Visitor for BodyLowereringContext<'hir> {
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

        // Main implicitly returns 0 even if the signature does not
        // say so
        let value = (self.symbol_name.value() == "main").then_some(lir::Operand::Immediate(
            lir::Immediate::Int(0, lir::IntegerWidth::I8),
        ));

        self.block_map[current_block]
            .instructions
            .push(lir::Instruction::Return { value });
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
                    hir::Literal::Char(v) => lir::Immediate::Int(*v as u64, lir::IntegerWidth::I32),
                    hir::Literal::Integer(v, k) => lir::Immediate::Int(
                        *v,
                        match k {
                            hir::LiteralIntegerKind::Signed(int_kind) => (*int_kind).into(),
                            hir::LiteralIntegerKind::Unsigned(uint_kind) => (*uint_kind).into(),
                            hir::LiteralIntegerKind::Unsuffixed => {
                                let ty = self.type_map.get_type(expression.hir_id);

                                match &*ty {
                                    ty::TypeKind::Integer(int_kind) => (*int_kind).into(),
                                    ty::TypeKind::UnsignedInteger(uint_kind) => (*uint_kind).into(),
                                    _ => unreachable!(),
                                }
                            }
                        },
                    ),
                    hir::Literal::Float(..) => todo!("load float"),
                    hir::Literal::String(s) => {
                        // strings are actually fat pointers which need to be
                        // stored as structs on the stack. we need to allocate
                        // room for the string struct, fill its fields with the
                        // static pointer and length, and then return the
                        // register which stores the pointer as the target of
                        // the move instead of an immediate.

                        /* Create the struct on the stack */

                        let struct_ptr_reg = self.create_register_with_lir_type(lir::Type::Pointer);

                        self.push_instruction(lir::Instruction::AllocStack {
                            destination: struct_ptr_reg,
                            ty: lir::Type::Struct(lir::Struct::slice()),
                        });

                        /* Set the pointer field */

                        let pointer_element_ptr_reg =
                            self.create_register_with_lir_type(lir::Type::Pointer);
                        self.push_instruction(lir::Instruction::GetStructElementPointer {
                            destination: pointer_element_ptr_reg,
                            source: lir::Operand::Register(struct_ptr_reg),
                            ty: lir::Struct::slice(),
                            index: 0,
                        });

                        let id = self.create_static_label_id();
                        self.static_strings.insert(id, *s);
                        self.push_instruction(lir::Instruction::StoreMem {
                            destination: lir::Operand::Register(pointer_element_ptr_reg),
                            source: lir::Operand::Immediate(lir::Immediate::StaticLabel(id)),
                        });

                        /* Set the length field */

                        let length_element_ptr_reg =
                            self.create_register_with_lir_type(lir::Type::Pointer);
                        self.push_instruction(lir::Instruction::GetStructElementPointer {
                            destination: length_element_ptr_reg,
                            source: lir::Operand::Register(struct_ptr_reg),
                            ty: lir::Struct::slice(),
                            index: 1,
                        });

                        self.push_instruction(lir::Instruction::StoreMem {
                            destination: lir::Operand::Register(length_element_ptr_reg),
                            source: lir::Operand::Immediate(lir::Immediate::Int(
                                s.value().len() as _,
                                lir::IntegerWidth::I64,
                            )),
                        });

                        /* Move operand is the reg that points to the base of the struct */

                        self.expression_to_register_map
                            .insert(expression.hir_id.local_id, struct_ptr_reg);
                        return;
                    }
                    hir::Literal::ByteString(_) => {
                        // byte strings follow the same rule as above since they
                        // are native slices (fat pointers) and not just a
                        // pointer to some bytes.
                        todo!("load byte string (need to allocate in static mem)")
                    }
                    hir::Literal::CString(_) => {
                        // c strings are much simpler since they are just fancy
                        // raw pointers
                        todo!("load c string (need to allocate in static mem)")
                    }
                };

                let ty = self.type_map.get_type(expression.hir_id);
                let reg = self.create_register(ty);

                self.push_instruction(lir::Instruction::Move {
                    destination: reg,
                    source: lir::Operand::Immediate(value),
                });
                self.expression_to_register_map
                    .insert(expression.hir_id.local_id, reg);
            }
            hir::ExpressionKind::Path(path) => {
                hir::visit::walk_expression(self, expression.clone());

                if let Some(reg) = self
                    .expression_to_register_map
                    .get(&path.segments.last().unwrap().hir_id.local_id)
                {
                    self.expression_to_register_map
                        .insert(expression.hir_id.local_id, *reg);
                }
            }
            hir::ExpressionKind::Block(block) => {
                hir::visit::walk_expression(self, expression.clone());

                if let Some(reg) = self.expression_to_register_map.get(&block.hir_id.local_id) {
                    self.expression_to_register_map
                        .insert(expression.hir_id.local_id, *reg);
                }
            }
            hir::ExpressionKind::Tuple(expressions) => todo!(),
            hir::ExpressionKind::FunctionCall { target, arguments } => {
                hir::visit::walk_expression(self, expression.clone());

                let hir::ExpressionKind::Path(path) = &target.kind else {
                    todo!("lower function pointer calls")
                };

                let hir::Resolution::IntrinsicFunction(name) = path.resolution() else {
                    todo!("non-intrinsic functions");
                };

                if name.value() != "print" {
                    todo!("non-print functions");
                }

                assert_eq!(arguments.len(), 1, "no variadic print for now");

                let str_ptr_reg = self.expression_to_register_map[&arguments[0].hir_id.local_id];

                /* Extract struct fields */

                let ptr_ptr_reg = self.create_register_with_lir_type(lir::Type::Pointer);
                self.push_instruction(lir::Instruction::GetStructElementPointer {
                    destination: ptr_ptr_reg,
                    source: lir::Operand::Register(str_ptr_reg),
                    ty: lir::Struct::slice(),
                    index: 0,
                });
                let ptr_reg = self.create_register_with_lir_type(lir::Type::Pointer);
                self.push_instruction(lir::Instruction::LoadMem {
                    destination: ptr_reg,
                    source: lir::Operand::Register(ptr_ptr_reg),
                });

                let len_ptr_reg =
                    self.create_register_with_lir_type(lir::Type::Integer(lir::IntegerWidth::I64));
                self.push_instruction(lir::Instruction::GetStructElementPointer {
                    destination: len_ptr_reg,
                    source: lir::Operand::Register(str_ptr_reg),
                    ty: lir::Struct::slice(),
                    index: 1,
                });
                let len_reg =
                    self.create_register_with_lir_type(lir::Type::Integer(lir::IntegerWidth::I64));
                self.push_instruction(lir::Instruction::LoadMem {
                    destination: len_reg,
                    source: lir::Operand::Register(len_ptr_reg),
                });

                let dest_reg =
                    self.create_register_with_lir_type(lir::Type::Integer(lir::IntegerWidth::I64));

                self.push_instruction(lir::Instruction::FunctionCall {
                    target: lir::Operand::Immediate(lir::Immediate::FunctionLabel(
                        InternedSymbol::new("__$print_str"),
                    )),
                    arguments: vec![
                        lir::Operand::Register(ptr_reg),
                        lir::Operand::Register(len_reg),
                    ],
                    destination: Some(dest_reg),
                });

                self.expression_to_register_map
                    .insert(expression.hir_id.local_id, dest_reg);
            }
            hir::ExpressionKind::Binary { lhs, operator, rhs } => {
                hir::visit::walk_expression(self, expression.clone());

                let ty = self.type_map.get_type(expression.hir_id);
                let reg = self.create_register(ty);

                let lhs = self.expression_to_register_map[&lhs.hir_id.local_id];
                let rhs = self.expression_to_register_map[&rhs.hir_id.local_id];

                self.push_instruction(lir::Instruction::BinaryOperation {
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

                let positive_branch_last_block: lir::BlockId;
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
                    .push(lir::Instruction::Branch {
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

                dbg!(self.symbol_name.value(), value);

                // Main implicitly returns 0 even if the signature does not
                // say so
                let value = if self.symbol_name.value() == "main" {
                    Some(value.unwrap_or(lir::Operand::Immediate(lir::Immediate::Int(
                        0,
                        lir::IntegerWidth::I8,
                    ))))
                } else {
                    value
                };

                dbg!(value);

                self.push_instruction(lir::Instruction::Return { value });
            }
        }
    }

    fn visit_path_segment(&mut self, segment: std::rc::Rc<hir::PathSegment>) {
        match &segment.resolution {
            hir::Resolution::Definition(definition_kind, local_def_id) => {}
            hir::Resolution::Local(local_id) => {
                let reg = self.local_to_register_map[local_id];
                self.expression_to_register_map
                    .insert(segment.hir_id.local_id, reg);
            }
            hir::Resolution::IntrinsicFunction(interned_symbol) => {}
            hir::Resolution::Primitive(primitive_kind) => {}
        }
    }
}

pub fn lower_to_lir(module: &hir::Module, type_map: &ModuleTypeCheckResults) -> lir::Module {
    let mut function_definitions = BTreeMap::new();

    let mut next_static_label_id = StaticLabelId::new(0);
    let mut static_strings = BTreeMap::new();
    let mut static_c_strings = BTreeMap::new();

    for owner_id in module.get_owners() {
        let hir::ItemKind::Function { name, .. } =
            &module.get_owner(owner_id).node().as_item().unwrap().kind;

        let mut ctx = BodyLowereringContext {
            module,
            owner_id,
            symbol_name: name.symbol,
            type_map,
            next_static_label_id: &mut next_static_label_id,
            static_strings: &mut static_strings,
            static_c_strings: &mut static_c_strings,
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
        static_strings,
        static_c_strings,
    }
}
