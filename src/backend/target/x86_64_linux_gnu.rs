use core::fmt::Write;
use std::{collections::BTreeMap, path::Path, process::Command};

use itertools::Itertools;

use crate::{
    backend::{CodegenOptions, target::CodeGenerator},
    frontend::ast::{BinaryOperatorKind, UnaryOperatorKind},
    index::Index,
    middle::lir,
};

pub struct CodeGeneratorX86_64LinuxGnu;

impl CodeGenerator for CodeGeneratorX86_64LinuxGnu {
    fn translate_to_asm(&self, module: &lir::Module, options: &CodegenOptions) -> String {
        // TODO: remove unused static labels
        let static_strings = module
            .static_strings
            .iter()
            .map(|(id, symbol)| {
                format!(
                    r#"__$static_alloc_{}: db {}"#,
                    id.index(),
                    format_nasm_string(symbol.value())
                )
            })
            .join("\n");

        let function_bodies = module
            .function_definitions
            .values()
            .map(|f| codegen_function(f, options))
            .join("\n\n");

        format!(
            indoc::indoc! {r#"
            global _start

            bits 64
            section .text

            ; program entrypoint
            _start:
                call main

                ; exit syscall using code passed in rax
                mov rdi, rax
                mov rax, 60
                syscall

            ; user code
            {0}

            ; built-in functions
            {1}

            ; static data
            section .data
            
            ; utf-8 strings
            {2}
            "#
            },
            function_bodies,
            include_str!("./x86_64-linux-gnu_core.s"),
            static_strings
        )
    }

    fn create_assembler_command(
        &self,
        input_file: &Path,
        output_file: &Path,
    ) -> std::process::Command {
        let mut cmd = Command::new("nasm");

        cmd.args([
            "-f",
            "elf64",
            "-o",
            output_file
                .to_str()
                .expect("Could not convert output_file to string"),
            input_file
                .to_str()
                .expect("Could not convert input_file to string"),
        ]);

        cmd
    }

    fn create_linker_command(
        &self,
        input_file: &Path,
        output_file: &Path,
    ) -> std::process::Command {
        let mut cmd = Command::new("x86_64-linux-gnu-gcc");

        cmd.args([
            "-v",
            "-nostdlib",
            "-ffreestanding",
            "-Xlinker",
            "-x",
            "-o",
            output_file
                .to_str()
                .expect("Could not convert output_file to string"),
            input_file
                .to_str()
                .expect("Could not convert input_file to string"),
        ]);

        cmd
    }
}

fn format_nasm_string(string: &str) -> String {
    let mut parts = Vec::new();

    let mut last = 0;
    for (index, matched) in string.match_indices(['\n', '\r']) {
        if last != index {
            parts.push(format!("\"{}\"", &string[last..index]));
        }

        for b in matched.bytes() {
            parts.push(format!("0x{b:X}"));
        }

        last = index + matched.len();
    }
    if last < string.len() {
        parts.push(format!("\"{}\"", &string[last..]));
    }

    parts.join(", ")
}

fn codegen_function(function: &lir::FunctionDefinition, options: &CodegenOptions) -> String {
    const ARG_REGS: &[&str] = &["rdi", "rsi", "rdx", "rcx", "r8", "r9"];

    let mut stack_frame_register_offset_map = BTreeMap::new();
    let mut stack_frame_size = 0;

    for reg in function.registers.values() {
        stack_frame_size = lir::align_to(
            stack_frame_size + reg.ty.layout().size,
            reg.ty.layout().alignment,
        );
        stack_frame_register_offset_map.insert(reg.id, stack_frame_size);
    }

    /* Assembly output */

    let mut output = String::new();

    macro_rules! emit {
        ($($arg:tt)*) => {
            writeln!(&mut output, $($arg)*).unwrap();
        };
    }

    emit!("global {}", function.symbol_name.value());
    emit!("{}:", function.symbol_name.value());

    /* Function Prologue */

    emit!("    push rbp");
    emit!("    mov rbp, rsp");
    emit!("    sub rsp, {stack_frame_size}");

    macro_rules! load {
        ($register:ident, $operand:expr) => {
            match $operand {
                lir::Operand::Immediate(lir::Immediate::Bool(value)) => {
                    emit!("    mov {}, {}", stringify!($register), *value as u8);
                }
                lir::Operand::Immediate(immediate) => {
                    emit!("    mov {}, {}", stringify!($register), immediate);
                }
                lir::Operand::Register(reg) => {
                    emit!(
                        "    mov {}, [rbp - {}]",
                        stringify!($register),
                        stack_frame_register_offset_map[reg]
                    );
                }
            }
        };
    }

    macro_rules! store {
        ($dest:expr, $src:ident) => {
            emit!(
                "    mov [rbp - {}], {}",
                stack_frame_register_offset_map[$dest],
                stringify!($src),
            );
        };
        ([$size:expr] $dest:expr, $src:ident) => {
            emit!(
                "    mov {} [rbp - {}], {}",
                match $size {
                    1 => "byte",
                    2 => "word",
                    4 => "dword",
                    8 => "qword",
                    _ => unreachable!(),
                },
                stack_frame_register_offset_map[$dest],
                stringify!($src),
            );
        };
    }

    /* Move the function arguments into the stack registers */

    for (i, arg) in function.arguments.iter().enumerate() {
        emit!(
            "    ; store arg {} into its stack register",
            strip_ansi_escapes::strip_str(arg.to_string())
        );
        emit!(
            "    mov [rbp - {}], {}",
            stack_frame_register_offset_map[arg],
            ARG_REGS[i],
        );
    }

    /* Intermediate Blocks */
    for block in function.blocks.values() {
        emit!("{}:", block.id);

        for instruction in block.instructions.iter() {
            emit!(
                "    ; {}",
                strip_ansi_escapes::strip_str(instruction.to_string())
            );

            match instruction {
                lir::Instruction::LoadMem {
                    destination,
                    source,
                } => {
                    load!(rax, source);
                    emit!("    mov rax, [rax]");
                    store!(destination, rax);
                }
                lir::Instruction::StoreMem {
                    destination,
                    source,
                } => {
                    load!(rax, source);
                    load!(rcx, destination);
                    emit!("    mov [rcx], rax");
                }
                lir::Instruction::AllocStack { destination, ty } => {
                    emit!(
                        "    sub rsp, {}",
                        lir::align_to(ty.layout().size, ty.layout().alignment)
                    );
                    store!(destination, rsp);
                }
                lir::Instruction::GetStructElementPointer {
                    destination,
                    source,
                    ty,
                    index,
                } => {
                    load!(rax, source);
                    emit!("    lea rax, [rax + {}]", ty.offset_of(*index));
                    store!(destination, rax);
                }
                lir::Instruction::GetArrayElementPointer {
                    destination,
                    source,
                    ty,
                    index,
                } => todo!(),
                lir::Instruction::Move {
                    destination,
                    source,
                } => {
                    load!(rax, source);
                    store!(destination, rax);
                }
                lir::Instruction::IntegerCast {
                    kind,
                    destination,
                    operand,
                } => {
                    todo!("emit asm for integer cast")
                }
                lir::Instruction::UnaryOperation {
                    operator,
                    destination,
                    operand,
                } => {
                    load!(rax, operand);

                    match operator {
                        UnaryOperatorKind::Deref => todo!(),
                        UnaryOperatorKind::AddressOf => todo!(),
                        UnaryOperatorKind::LogicalNot => {
                            emit!("    cmp rcx, rcx");
                            emit!("    test rax, rax");
                            emit!("    sete cl");
                            store!([1] destination, cl);
                        }
                        UnaryOperatorKind::BitwiseNot => todo!(),
                        UnaryOperatorKind::Negate => todo!(),
                    }
                }
                lir::Instruction::BinaryOperation {
                    operator,
                    destination,
                    lhs,
                    rhs,
                } => {
                    load!(rax, lhs);
                    load!(rcx, rhs);

                    // TODO: seprate into several instructions. group all
                    // sign-agnostic math instructions (and specify size) which
                    // includes equality, group signed math instructions (with
                    // specified size), group unsigned math instructions (with
                    // specified size)

                    match operator {
                        BinaryOperatorKind::Add => todo!(),
                        BinaryOperatorKind::Subtract => todo!(),
                        BinaryOperatorKind::Multiply => todo!(),
                        BinaryOperatorKind::Divide => todo!(),
                        BinaryOperatorKind::Modulus => {
                            // TODO: signed vs unsigned div
                            // TODO: operand sizes
                            emit!("    cqo");
                            emit!("    idiv rcx");
                            store!(destination, rdx);
                        }
                        BinaryOperatorKind::Equals => {
                            // sete only works on 8-bit registers
                            emit!("    cmp rax, rcx");
                            emit!("    sete al");
                            store!([1] destination, al);
                        }
                        BinaryOperatorKind::NotEquals => todo!(),
                        BinaryOperatorKind::LessThan => todo!(),
                        BinaryOperatorKind::LessThanOrEqualTo => todo!(),
                        BinaryOperatorKind::GreaterThan => todo!(),
                        BinaryOperatorKind::GreaterThanOrEqualTo => todo!(),
                        BinaryOperatorKind::LogicalAnd => todo!(),
                        BinaryOperatorKind::LogicalOr => todo!(),
                        BinaryOperatorKind::BitwiseAnd => todo!(),
                        BinaryOperatorKind::BitwiseOr => todo!(),
                        BinaryOperatorKind::BitwiseXor => todo!(),
                        BinaryOperatorKind::ShiftLeft => todo!(),
                        BinaryOperatorKind::ShiftRight => todo!(),
                    }
                }
                lir::Instruction::Branch {
                    condition,
                    positive,
                    negative,
                } => {
                    match condition {
                        lir::Operand::Immediate(immediate) => {
                            assert!(matches!(immediate, lir::Immediate::Bool(_)))
                        }
                        lir::Operand::Register(register_id) => {
                            assert!(matches!(
                                function.registers[register_id].ty,
                                lir::Type::Integer(lir::IntegerWidth::I8)
                            ))
                        }
                    }

                    load!(al, condition);
                    emit!("    test al, al");
                    emit!("    jnz {positive}");
                    emit!("    jmp {negative}");
                }
                lir::Instruction::Jump { destination } => {
                    emit!("    jmp {destination}");
                }
                lir::Instruction::Return { value } => {
                    // TODO: dont emit jmp if we are in the last block?

                    // load return value into rax
                    if let Some(v) = value {
                        load!(rax, v);
                    }

                    emit!("    jmp .exit");
                }
                lir::Instruction::FunctionCall {
                    target,
                    arguments,
                    destination,
                } => {
                    assert!(matches!(
                        function.type_of_operand(*target),
                        lir::Type::Pointer
                    ));

                    // Depending on the types of the arguments, we need to determine how we move them into registers

                    // First 6 integer arguments are passed in rdi, rsi, rdx, r10, r9, r8
                    // All other arguments are passed on the stack for now.

                    // Struct fields must be manually deconstructed in lowering
                    // for optimizations like passing the fields of small
                    // structs in registers.

                    let mut register_arguments = Vec::with_capacity(6);
                    let mut stack_arguments = Vec::new();

                    for arg in arguments {
                        match arg {
                            lir::Operand::Immediate(_) => {
                                if register_arguments.len() < 6 {
                                    register_arguments.push(arg);
                                } else {
                                    stack_arguments.push(arg);
                                }
                            }
                            lir::Operand::Register(register_id) => {
                                let ty = &function.registers[register_id].ty;

                                match ty {
                                    lir::Type::Integer(_)
                                    | lir::Type::Float(_)
                                    | lir::Type::Pointer => {
                                        if register_arguments.len() < 6 {
                                            register_arguments.push(arg);
                                        } else {
                                            stack_arguments.push(arg);
                                        }
                                    }
                                    lir::Type::Struct(_) | lir::Type::Array(_, _) => {
                                        stack_arguments.push(arg)
                                    }
                                }
                            }
                        }
                    }

                    for (i, operand) in register_arguments.into_iter().enumerate() {
                        let reg = ARG_REGS[i];
                        match operand {
                            lir::Operand::Immediate(lir::Immediate::Bool(value)) => {
                                emit!("    mov {}, {}", reg, *value as u8);
                            }
                            lir::Operand::Immediate(lir::Immediate::Int(value, width)) => {
                                // special handing for different integet sizes
                                // to make sure we dont load too many bytes

                                // FIXME: is this actually necessary since the
                                // callee only cares about the lower bits
                                // anyway?
                                emit!("    xor rax, rax");
                                let intermediate = match width {
                                    lir::IntegerWidth::I8 => "al",
                                    lir::IntegerWidth::I16 => "ax",
                                    lir::IntegerWidth::I32 => "eax",
                                    lir::IntegerWidth::I64 => "rax",
                                };
                                emit!("    mov {}, {}", intermediate, value);
                                emit!("    mov {}, rax", reg);
                            }
                            lir::Operand::Immediate(
                                imm @ (lir::Immediate::StaticLabel(_)
                                | lir::Immediate::FunctionLabel(_)),
                            ) => {
                                emit!("    mov {}, {}", reg, imm);
                            }
                            lir::Operand::Immediate(lir::Immediate::Float(..)) => {
                                todo!("xmm registers")
                            }
                            lir::Operand::Register(reg_id) => {
                                let ty = &function.registers[reg_id].ty;

                                match ty {
                                    lir::Type::Integer(width) => {
                                        // FIXME: same as above

                                        emit!("    xor rax, rax");
                                        let intermediate = match width {
                                            lir::IntegerWidth::I8 => "al",
                                            lir::IntegerWidth::I16 => "ax",
                                            lir::IntegerWidth::I32 => "eax",
                                            lir::IntegerWidth::I64 => "rax",
                                        };
                                        emit!(
                                            "    mov {}, [rbp - {}]",
                                            intermediate,
                                            stack_frame_register_offset_map[reg_id]
                                        );
                                        emit!("    mov {}, rax", reg);
                                    }
                                    lir::Type::Pointer => {
                                        emit!(
                                            "    mov {}, [rbp - {}]",
                                            reg,
                                            stack_frame_register_offset_map[reg_id]
                                        );
                                    }
                                    lir::Type::Float(_) => todo!("xmm registers"),
                                    lir::Type::Struct(_) | lir::Type::Array(_, _) => unreachable!(),
                                }
                            }
                        }
                    }

                    // TODO: reserve enough stack space for the stack arguments
                    // (each one must be 8 byte aligned unless we figure out a
                    // better way to handle smaller integer loading)

                    for (i, arg) in stack_arguments.into_iter().enumerate() {
                        // similar to above but need to push to the stack
                        // instead + handle copying memory from our local stack
                        // frame into the newly allocated region
                        todo!("handle passing args on the stack")
                    }

                    match target {
                        lir::Operand::Immediate(lir::Immediate::FunctionLabel(name)) => {
                            emit!("    call {}", name.value());
                        }
                        _ => {
                            load!(rax, target);
                            emit!("    call rax");
                        }
                    }

                    if let Some(dest) = destination {
                        let ty = &function.registers[dest].ty;

                        match ty {
                            lir::Type::Integer(width) => {
                                let reg = match width {
                                    lir::IntegerWidth::I8 => "al",
                                    lir::IntegerWidth::I16 => "ax",
                                    lir::IntegerWidth::I32 => "eax",
                                    lir::IntegerWidth::I64 => "rax",
                                };
                                emit!(
                                    "    mov [rbp - {}], {}",
                                    stack_frame_register_offset_map[dest],
                                    reg
                                );
                            }
                            lir::Type::Float(_) => todo!("xmm registers"),
                            lir::Type::Pointer => {
                                emit!(
                                    "    mov [rbp - {}], rax",
                                    stack_frame_register_offset_map[dest]
                                );
                            }
                            lir::Type::Struct(_) | lir::Type::Array(_, _) => {
                                todo!("allocate room on the stack for the return value")
                            }
                        }
                    }
                }
                lir::Instruction::Syscall {
                    number,
                    arguments,
                    destination,
                } => {
                    assert_eq!(arguments.len(), 3);

                    emit!("    mov rax, {}", number);
                    load!(rdi, &arguments[0]);
                    load!(rsi, &arguments[1]);
                    load!(rdx, &arguments[2]);
                    emit!("    syscall");

                    store!(destination, rax);
                }
                lir::Instruction::Phi { .. } => {
                    unreachable!("phi instructions should be eliminated before codegen")
                }
                lir::Instruction::Comment(text) => {
                    if options.emit_debug_info {
                        emit!("    ; {text}");
                    }
                }
            }
        }
    }

    /* Function Epilogue */

    emit!(".exit:");
    emit!("    mov rsp, rbp");
    emit!("    pop rbp");
    emit!("    ret");

    output
}
