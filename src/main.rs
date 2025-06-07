#![feature(decl_macro)]

use std::path::PathBuf;

use clap::{CommandFactory, Parser as ClapParser, error::ErrorKind};

use crate::{
    backend::{
        early_optimizations::perform_early_optimizations, hir_lowering::lower_to_lir,
        pretty_print::pretty_print_lir,
    },
    frontend::{SourceFile, SourceFileOrigin, parser::Parser},
    middle::{ast_lowering::lower_to_hir, type_check::type_check_module},
};

mod backend;
mod frontend;
mod index;
mod middle;

#[derive(Debug, ClapParser)]
#[command(version, about, long_about = None)]
pub struct Args {
    #[arg(short = 'e', value_enum, default_value_t = Default::default())]
    emit: EmitFormat,
    #[arg(short = 'O', value_enum, default_value_t = Default::default())]
    optimization_level: OptimizationLevel,
    source_files: Vec<PathBuf>,
}

#[derive(Debug, Default, Clone, Copy, PartialEq, Eq, clap::ValueEnum)]
pub enum EmitFormat {
    #[default]
    #[value(name = "exe")]
    Executable,
    #[value(name = "obj")]
    Object,
    #[value(name = "asm")]
    Assembly,
    #[value(name = "lir")]
    Lir,
    #[value(name = "hir")]
    Hir,
    #[value(name = "ast")]
    Ast,
}

#[derive(Debug, Default, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, clap::ValueEnum)]
pub enum OptimizationLevel {
    #[default]
    #[value(name = "0")]
    Zero,
    #[value(name = "1")]
    One,
    #[value(name = "2")]
    Two,
    #[value(name = "3")]
    Three,
}

fn main() {
    let args = Args::parse();

    if args.source_files.is_empty() {
        Args::command()
            .error(ErrorKind::MissingRequiredArgument, "Missing source files!")
            .exit();
    }

    for source_file in &args.source_files {
        if !source_file.exists() {
            Args::command()
                .error(
                    ErrorKind::InvalidValue,
                    format!("Source file '{}' does not exist!", source_file.display()),
                )
                .exit()
        }

        if !source_file.is_file() {
            Args::command()
                .error(
                    ErrorKind::InvalidValue,
                    format!("Input path '{}' is not a file!", source_file.display()),
                )
                .exit()
        }
    }

    /* Read in source files */

    let source_files = args
        .source_files
        .into_iter()
        .map(|path| {
            let contents = std::fs::read_to_string(&path)
                .expect("Failed to read input file (or invalid UTF-8)");

            SourceFile {
                contents,
                origin: SourceFileOrigin::File(path),
            }
        })
        .collect::<Vec<_>>();

    for source_file in &source_files {
        // Construct AST from the source code
        let ast = Parser::parse_module(source_file);

        if args.emit == EmitFormat::Ast {
            println!("{ast:#?}");
            return;
        }

        // Index AST and resolve names to produce HIR
        let hir = lower_to_hir(&ast);

        if args.emit == EmitFormat::Hir {
            println!("{hir:#?}");
            return;
        }

        let types = type_check_module(&hir, source_file);
        let lir = lower_to_lir(&hir, &types);

        let mut function = lir.function_definitions.into_values().next().unwrap();
        // pretty_print_lir(&function);
        // println!();

        if args.optimization_level > OptimizationLevel::Zero {
            perform_early_optimizations(&mut function);
            // pretty_print_lir(&function);
        }

        // if args.emit == EmitFormat::Lir {
        pretty_print_lir(&function);
        //     return;
        // }
    }
}
