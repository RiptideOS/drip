use core::fmt::Write;
use std::{collections::BTreeMap, path::Path, process::Command};

use itertools::Itertools;

use crate::{
    backend::{CodegenOptions, target::CodeGenerator},
    frontend::ast::BinaryOperatorKind,
    middle::lir,
};

pub struct CodeGeneratorX86_64LinuxGnu;

impl CodeGenerator for CodeGeneratorX86_64LinuxGnu {
    fn translate_to_asm(&self, module: &lir::Module, options: &CodegenOptions) -> String {
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

            {0}
            "#
            },
            function_bodies,
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

fn codegen_function(function: &lir::FunctionDefinition, options: &CodegenOptions) -> String {
    let stack_frame_register_size_map: BTreeMap<_, _> = function
        .registers
        .values()
        .map(|r| (r.id, r.ty.size()))
        .collect();

    let mut stack_frame_register_offset_map = BTreeMap::new();
    let mut stack_frame_size = 0;

    // TODO: account for address alignment
    for (id, size) in &stack_frame_register_size_map {
        stack_frame_register_offset_map.insert(id, stack_frame_size);
        stack_frame_size += size;
    }

    /* Assembly output */

    let mut output = String::new();

    macro_rules! emit {
        ($($arg:tt)*) => {
            writeln!(&mut output, $($arg)*).unwrap();
        };
    }

    emit!("{}:", function.symbol_name.value());

    /* Function Prologue */

    emit!("    push rbp");
    emit!("    mov rbp, rsp");
    emit!("    sub rsp, {stack_frame_size}");

    /* Intermediate Blocks */

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

    for block in function.blocks.values() {
        emit!("{}:", block.id);

        for instruction in block.instructions.iter() {
            emit!(
                "    ; {}",
                strip_ansi_escapes::strip_str(instruction.to_string())
            );

            match instruction {
                lir::Instruction::Move {
                    destination,
                    source,
                } => {
                    load!(rax, source);
                    store!(destination, rax);
                }
                lir::Instruction::UnaryOperation {
                    operator: _,
                    destination: _,
                    operand: _,
                } => todo!(),
                lir::Instruction::BinaryOperation {
                    operator,
                    destination,
                    lhs,
                    rhs,
                } => {
                    load!(rax, lhs);
                    load!(rbx, rhs);

                    match operator {
                        BinaryOperatorKind::Add => todo!(),
                        BinaryOperatorKind::Subtract => todo!(),
                        BinaryOperatorKind::Multiply => todo!(),
                        BinaryOperatorKind::Divide => todo!(),
                        BinaryOperatorKind::Modulus => todo!(),
                        BinaryOperatorKind::Equals => {
                            // sete only works on 8-bit registers
                            emit!("    cmp rax, rbx");
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
                            assert!(function.registers[register_id].ty.is_bool())
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
                    target: _,
                    arguments: _,
                    destination: _,
                } => todo!(),
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
