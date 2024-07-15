use std::path::PathBuf;

use clap::{error::ErrorKind, CommandFactory, Parser as ClapParser};
use frontend::{resolve::Resolver, SourceFile, SourceFileOrigin};

use crate::frontend::parser::Parser;

mod frontend;
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
        let module = Parser::parse_module(source_file);

        println!("{:#?}", module);

        let name_resolutions = Resolver::resolve_names(&module);

        println!("{:#?}", name_resolutions);
    }
}
