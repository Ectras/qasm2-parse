use std::num::ParseFloatError;

use thiserror::Error;

use crate::{
    ast::Program,
    lexing::{LexingError, MultiLexer, Token, TokenKind},
};

#[derive(Error, Debug, PartialEq)]
pub enum ParsingError {
    #[error("expected {expected}, but found {actual:?}")]
    UnexpectedToken { actual: TokenKind, expected: String },
    #[error(transparent)]
    LexingError(#[from] LexingError),
    #[error(transparent)]
    ParsingError(#[from] ParseFloatError),
    #[error("expected OPENQASM version \"2.0\", but found \"{0}\"")]
    WrongQasmVersion(String),
}

struct Parser {
    lexer: MultiLexer,
}

impl Parser {
    pub fn new(lexer: MultiLexer) -> Self {
        Self { lexer }
    }

    /// Pops the next token and checks that it is of the expected kind. Returns the
    /// token for further processing (e.g. accessing the text) if it was the correct
    /// kind.
    fn expect(&mut self, expected: TokenKind) -> Result<Token, ParsingError> {
        // We can use unwrap() because we know the lexer will always return an EoF last,
        // wich will trigger an ParsingError first.
        let token = self.lexer.next().unwrap()?;
        if token.kind == expected {
            Ok(token)
        } else {
            Err(ParsingError::UnexpectedToken {
                actual: token.kind,
                expected: expected.to_string(),
            })
        }
    }

    /// Given a slice of [`TokenKind`] options, returns a string concatenated with
    /// commas and a final "or".
    fn stringify_tokenvec(tokens: &[TokenKind]) -> String {
        let mut out = String::new();
        for (i, token) in tokens.iter().enumerate() {
            if i == tokens.len() - 1 {
                out += " or ";
            } else if i > 0 {
                out += ", ";
            }
            out += &token.to_string();
        }
        out
    }

    /// Pops the next token and checks that it is one of the expected kinds. Returns
    /// the token for further processing (e.g. accessing the text) if it was the
    /// correct kind.
    fn expect_either(&mut self, expected: &[TokenKind]) -> Result<Token, ParsingError> {
        let token = self.lexer.next().unwrap()?;
        if expected.contains(&token.kind) {
            Ok(token)
        } else {
            Err(ParsingError::UnexpectedToken {
                actual: token.kind,
                expected: format!("one of {}", Self::stringify_tokenvec(&expected)),
            })
        }
    }

    pub fn parse(&mut self) -> Result<Program, ParsingError> {
        self.parse_program()
    }

    fn parse_program(&mut self) -> Result<Program, ParsingError> {
        self.parse_version()?;
        // TODO: parse statements
        self.expect(TokenKind::Eof)?;
        todo!()
    }

    fn parse_version(&mut self) -> Result<(), ParsingError> {
        self.expect(TokenKind::OPENQASM)?;
        let version = self.expect_either(&[TokenKind::Float, TokenKind::Integer])?;
        let version = version.text.unwrap();
        if version != "2.0" {
            return Err(ParsingError::WrongQasmVersion(version));
        }
        self.expect(TokenKind::Semicolon)?;
        Ok(())
    }
}
