use colored::Colorize;
use itertools::Itertools;

use crate::{index::Index, middle::lir};

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

            println!("{instruction}");
        }
    }

    println!("{}", "}".white())
}

impl core::fmt::Display for lir::Instruction {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            lir::Instruction::Move {
                destination,
                source,
            } => {
                write!(f, "{destination} {} {source}", "=".white())
            }
            lir::Instruction::UnaryOperation {
                operator,
                destination,
                operand,
            } => {
                write!(
                    f,
                    "{destination} {} {} {operand}",
                    "=".white(),
                    operator.to_string().white()
                )
            }
            lir::Instruction::BinaryOperation {
                operator,
                destination,
                lhs,
                rhs,
            } => {
                write!(
                    f,
                    "{destination} {} {lhs} {} {rhs}",
                    "=".white(),
                    operator.to_string().white()
                )
            }
            lir::Instruction::Branch {
                condition,
                positive,
                negative,
            } => {
                write!(
                    f,
                    "{} {condition} {} {}",
                    "br".cyan(),
                    positive.to_string().blue(),
                    negative.to_string().blue()
                )
            }
            lir::Instruction::Jump { destination } => {
                write!(f, "{} {}", "jmp".cyan(), destination.to_string().blue())
            }
            lir::Instruction::Return { value: Some(value) } => {
                write!(f, "{} {value}", "ret".cyan())
            }
            lir::Instruction::Return { value: _ } => {
                write!(f, "{}", "ret".cyan())
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
                write!(
                    f,
                    "{destination} {} {}{}",
                    "=".white(),
                    "phi".bright_green(),
                    "(".white(),
                )?;

                write!(
                    f,
                    "{}",
                    sources
                        .iter()
                        .map(|(block, reg)| format!("{} -> {reg}", block.to_string().blue(),))
                        .join(", ")
                        .white()
                )?;

                write!(f, "{}", ")".white())
            }
            lir::Instruction::Comment(_) => todo!(),
        }
    }
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
            lir::Immediate::Int(value) => write!(f, "{value}"),
            lir::Immediate::Float(value) => write!(f, "{value}"),
            lir::Immediate::Bool(value) => write!(f, "{value}"),
        }
    }
}

impl core::fmt::Display for lir::Operand {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            lir::Operand::Immediate(immediate) => write!(f, "{}", immediate.to_string().purple()),
            lir::Operand::Register(register_id) => write!(f, "{register_id}"),
        }
    }
}
