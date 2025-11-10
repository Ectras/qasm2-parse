use std::path::Path;

use crate::{
    ast::Program,
    lexing::{MultiLexer, PeekableMultiLexer},
    parsing::{Parser, ParsingError},
};

pub mod ast;
pub mod expr_eval;
pub mod gate_inliner;
mod lexing;
mod parsing;

/// Parses OpenQASM2 code and returns the abstract syntax tree.
pub fn parse_string(code: String) -> Result<Program, ParsingError> {
    parse(MultiLexer::from_text(code))
}

/// Parses OpenQASM2 from a file and returns the abstract syntax tree.
pub fn parse_file<P>(path: P) -> std::io::Result<Result<Program, ParsingError>>
where
    P: AsRef<Path>,
{
    Ok(parse(MultiLexer::from_file(path)?))
}

fn parse(lexer: MultiLexer) -> Result<Program, ParsingError> {
    let mut parser = Parser::new(PeekableMultiLexer::new(lexer));
    parser.parse()
}
