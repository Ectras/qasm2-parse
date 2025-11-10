use std::{iter::Peekable, num::ParseIntError};

use thiserror::Error;

use crate::{
    ast::{Program, Statement},
    lexing::{LexingError, MultiLexer, Token, TokenKind},
};

#[derive(Error, Debug, PartialEq)]
pub enum ParsingError {
    #[error("expected {expected}, but found {actual:?}")]
    UnexpectedToken { actual: TokenKind, expected: String },
    #[error(transparent)]
    LexingError(#[from] LexingError),
    #[error(transparent)]
    ParsingError(#[from] ParseIntError),
    #[error("expected OPENQASM version \"2.0\", but found \"{0}\"")]
    WrongQasmVersion(String),
}

struct Parser {
    lexer: Peekable<MultiLexer>,
}

impl Parser {
    pub fn new(lexer: MultiLexer) -> Self {
        Self {
            lexer: lexer.peekable(),
        }
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
        let mut statements = Vec::new();
        loop {
            // Peek the next token
            let next_token = self.lexer.peek().unwrap().as_ref().map_err(|err| *err)?;

            // End when we are done with all input
            if next_token.kind == TokenKind::Eof {
                break;
            }

            // Parse the statement
            let statement = match next_token.kind {
                TokenKind::Qreg | TokenKind::Creg => self.parse_declaration(),
                _ => {
                    return Err(ParsingError::UnexpectedToken {
                        actual: next_token.kind,
                        expected: "a statement".into(),
                    });
                }
            }?;

            statements.push(statement);
        }
        self.expect(TokenKind::Eof)?;
        Ok(Program { statements })
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

    fn parse_declaration(&mut self) -> Result<Statement, ParsingError> {
        let decl = self.expect_either(&[TokenKind::Qreg, TokenKind::Creg])?;
        let is_quantum = decl.kind == TokenKind::Qreg;
        let identifier = self.expect(TokenKind::Identifier)?;
        let name = identifier.text.unwrap();
        let size = self.parse_designator()?;
        self.expect(TokenKind::Semicolon)?;
        Ok(Statement::RegisterDeclaration {
            is_quantum,
            name,
            size,
        })
    }

    fn parse_designator(&mut self) -> Result<usize, ParsingError> {
        self.expect(TokenKind::LBracket)?;
        let size = self.expect(TokenKind::Integer)?;
        self.expect(TokenKind::RBracket)?;
        size.text.unwrap().parse().map_err(Into::into)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn single_declaration() {
        let text = "OPENQASM 2.0; qreg foo[5];";
        let lexer = MultiLexer::from_text(text.into());
        let mut parser = Parser::new(lexer);
        let res = parser.parse();
        assert_eq!(
            res,
            Ok(Program {
                statements: vec![Statement::RegisterDeclaration {
                    is_quantum: true,
                    name: "foo".into(),
                    size: 5
                }]
            })
        );
    }
}
