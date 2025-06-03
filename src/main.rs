#![feature(decl_macro)]

use std::path::PathBuf;

use clap::{CommandFactory, Parser as ClapParser, error::ErrorKind};
use middle::type_check::type_check_module;

use crate::{
    frontend::{SourceFile, SourceFileOrigin, parser::Parser},
    middle::{
        ast_lowering::lower_to_hir,
        // type_checker::TypeChecker
    },
};

mod backend;
mod frontend;
mod index;
mod middle;

#[derive(Debug, ClapParser)]
#[command(version, about, long_about = None)]
pub struct Args {
    source_files: Vec<PathBuf>,
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
        // println!("{ast:#?}");

        // Index AST and resolve names to produce HIR
        let hir = lower_to_hir(&ast);
        // println!("{hir:#?}");

        let types = type_check_module(&hir, source_file);
        println!("{types:#?}");
    }
}
