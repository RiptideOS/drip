use std::path::PathBuf;

use self::lexer::Span;

pub mod ast;
pub mod intern;
pub mod lexer;
pub mod parser;
pub mod resolve;

#[derive(Debug)]
pub struct SourceFile {
    pub contents: String,
    pub origin: SourceFileOrigin,
}

impl SourceFile {
    pub fn value_of_span(&self, span: Span) -> &str {
        &self.contents[span.start..span.end]
    }

    pub fn line_number_for_position(&self, mut position: usize) -> usize {
        let mut line_number = 1;

        for line in self.contents.lines() {
            if position < line.len() {
                break;
            } else {
                position -= line.len();
            }

            line_number += 1;
        }

        line_number
    }

    pub fn column_for_position(&self, position: usize) -> usize {
        let mut pos = 0;

        for line in self
            .contents
            .lines()
            .take(self.line_number_for_position(position) - 1)
        {
            pos += line.len()
        }

        position - pos
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
