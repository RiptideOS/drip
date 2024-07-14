use std::path::PathBuf;

use self::lexer::Span;

pub mod ast;
pub mod intern;
pub mod lexer;
pub mod parser;

#[derive(Debug)]
pub struct SourceFile {
    pub contents: String,
    pub origin: SourceFileOrigin,
}

impl SourceFile {
    pub fn value_of_span(&self, span: Span) -> &str {
        &self.contents[span.start..span.end]
    }
}

#[derive(Debug)]
pub enum SourceFileOrigin {
    Memory,
    File(PathBuf),
}

impl core::fmt::Display for SourceFileOrigin {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SourceFileOrigin::Memory => f.write_str("<memory>"),
            SourceFileOrigin::File(path) => f.write_fmt(format_args!("{}", path.display())),
        }
    }
}
