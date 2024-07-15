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

    pub fn row_for_position(&self, position: usize) -> usize {
        let mut row = 1;

        for c in self.contents.chars().take(position) {
            if c == '\n' {
                row += 1;
            }
        }

        row
    }

    pub fn column_for_position(&self, position: usize) -> usize {
        let mut col = 1;

        for c in self.contents.chars().take(position) {
            if c == '\n' {
                col = 0;
            }

            col += 1;
        }

        col
    }

    pub fn highlight_span(&self, span: Span) {
        let lines: Vec<_> = self.contents.lines().collect();

        let span_starting_row = self.row_for_position(span.start);
        let span_ending_row = self.row_for_position(span.end);

        let span_starting_column = self.column_for_position(span.start);
        let span_ending_column = self.column_for_position(span.end);

        // Print the lines around and including the one with the error
        let start_idx = if span_starting_row < 3 {
            0
        } else {
            span_starting_row - 3
        };

        // Print each line and the line number
        for (n, line) in lines[start_idx..span_starting_row].iter().enumerate() {
            eprintln!("{:>3}: {}", n + start_idx + 1, line);
        }

        let prepending_count = span_starting_column + 4;
        let token_width = if span_ending_row == span_starting_row {
            span_ending_column - span_starting_column
        } else {
            1
        };

        // Print the space before the highlight
        eprint!("{}", String::from(" ").repeat(prepending_count));

        // Print the underline highlight
        eprintln!(
            "{}",
            String::from("^").repeat(if token_width > 0 { token_width } else { 1 })
        );

        // Print the space before "here"
        eprint!("{}", String::from(" ").repeat(prepending_count));

        eprintln!("here");
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
