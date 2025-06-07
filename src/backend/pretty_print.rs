use colored::Colorize;
use itertools::Itertools;

use crate::{backend::lir, index::Index};

pub fn pretty_print_lir(function: &lir::FunctionDefinition) {
    print!(
        "{} {}{}",
        "fn".magenta(),
        function.symbol_name.value().blue(),
        "(".white()
    );

    print!(
        "{}",
        function
            .arguments
            .iter()
            .map(|arg| arg.to_string())
            .join(", ")
            .white()
    );

    println!("{}", ") {".white());

    for block in function.blocks.values() {
        println!("{}", format!("{}:", block.id).bright_red());

        for instruction in &block.instructions {
            print!("    ");

            match instruction {
                lir::Instruction::Move {
                    destination,
                    source,
                } => {
                    println!("{destination} {} {source}", "=".white());
                }
                lir::Instruction::UnaryOperation {
                    operator,
                    destination,
                    operand,
                } => {
                    println!(
                        "{destination} {} {} {operand}",
                        "=".white(),
                        operator.to_string().white()
                    );
                }
                lir::Instruction::BinaryOperation {
                    operator,
                    destination,
                    lhs,
                    rhs,
                } => {
                    println!(
                        "{destination} {} {lhs} {} {rhs}",
                        "=".white(),
                        operator.to_string().white()
                    );
                }
                lir::Instruction::Branch {
                    condition,
                    positive,
                    negative,
                } => {
                    println!(
                        "{} {condition} {} {}",
                        "br".cyan(),
                        positive.to_string().blue(),
                        negative.to_string().blue()
                    );
                }
                lir::Instruction::Jump { destination } => {
                    println!("{} {}", "jmp".cyan(), destination.to_string().blue());
                }
                lir::Instruction::Return { value: Some(value) } => {
                    println!("{} {value}", "ret".cyan());
                }
                lir::Instruction::Return { value: _ } => {
                    println!("{}", "ret".cyan());
                }
                lir::Instruction::FunctionCall {
                    target,
                    arguments,
                    destination,
                } => {
                    todo!();
                }
                lir::Instruction::Phi {
                    destination,
                    sources,
                } => {
                    print!(
                        "{destination} {} {}{}",
                        "=".white(),
                        "phi".bright_green(),
                        "(".white(),
                    );

                    print!(
                        "{}",
                        sources
                            .iter()
                            .map(|(block, reg)| format!("{} -> {reg}", block.to_string().blue(),))
                            .join(", ")
                            .white()
                    );

                    println!("{}", ")".white())
                }
                lir::Instruction::Comment(_) => todo!(),
            }
        }
    }

    println!("{}", "}".white())
}

impl core::fmt::Display for lir::RegisterId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", format!("%{}", self.index()).yellow())
    }
}

impl core::fmt::Display for lir::BlockId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, ".label_{}", self.index())
    }
}

impl core::fmt::Display for lir::Immediate {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            lir::Immediate::Int(value) => write!(f, "{}", format!("{value}").purple()),
            lir::Immediate::Float(value) => write!(f, "{}", format!("{value}").purple()),
            lir::Immediate::Bool(value) => write!(f, "{}", format!("{value}").purple()),
        }
    }
}

impl core::fmt::Display for lir::Operand {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            lir::Operand::Immediate(immediate) => write!(f, "{immediate}"),
            lir::Operand::Register(register_id) => write!(f, "{register_id}"),
        }
    }
}
