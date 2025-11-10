use std::{
    f64::consts,
    num::{ParseFloatError, ParseIntError},
};

use thiserror::Error;

use crate::{
    ast::{
        Argument, BinOp, Expr, FuncType, GateCall, GateDeclaration, Precedence, Program, Statement,
        UnOp,
    },
    lexing::{LexingError, PeekableMultiLexer, Token, TokenKind},
};

#[derive(Error, Debug, PartialEq)]
pub enum ParsingError {
    #[error("expected {expected}, but found {actual}")]
    UnexpectedToken { actual: TokenKind, expected: String },
    #[error(transparent)]
    LexingError(#[from] LexingError),
    #[error(transparent)]
    ParseIntError(#[from] ParseIntError),
    #[error(transparent)]
    ParseFloatError(#[from] ParseFloatError),
    #[error("unable to include file {file}: {reason}")]
    IncludeError { file: String, reason: String },
    #[error("expected OPENQASM version \"2.0\", but found \"{0}\"")]
    WrongQasmVersion(String),
}

struct Parser {
    lexer: PeekableMultiLexer,
}

impl Parser {
    pub fn new(lexer: PeekableMultiLexer) -> Self {
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
                expected: format!("one of {}", Self::stringify_tokenvec(expected)),
            })
        }
    }

    /// Peeks the next token. It is assumed that a next token is always available, as
    /// the iter should end with an "EoF" token and peek should not be called after
    /// that.
    fn peek(&mut self) -> Result<&Token, ParsingError> {
        Ok(self.lexer.peek().unwrap()?)
    }

    pub fn parse(&mut self) -> Result<Program, ParsingError> {
        self.parse_program()
    }

    /// `<program> ::= <version> {<statement>}`
    fn parse_program(&mut self) -> Result<Program, ParsingError> {
        self.parse_version()?;
        let mut statements = Vec::new();
        loop {
            // Peek the next token
            let next_token = self.peek()?;

            // End when we are done with all input
            if next_token.kind == TokenKind::Eof {
                break;
            }

            // Handle includes separately, because they are not statements in the AST
            if next_token.kind == TokenKind::Include {
                self.parse_include()?;
                continue;
            }

            // Parse the statement
            let statement = match next_token.kind {
                TokenKind::Qreg | TokenKind::Creg => self.parse_declaration(),
                TokenKind::Gate | TokenKind::Opaque => self.parse_gate_declaration(),
                TokenKind::If => self.parse_if_statement(),
                TokenKind::Barrier => self.parse_barrier(),
                _ => self.parse_quantum_operation(),
            }?;

            statements.push(statement);
        }
        self.expect(TokenKind::Eof)?;
        Ok(Program { statements })
    }

    /// `<version> ::= "OPENQASM" (<integer> | <float>) ";"`
    fn parse_version(&mut self) -> Result<(), ParsingError> {
        self.expect(TokenKind::OpenQasm)?;
        let version = self.expect_either(&[TokenKind::Float, TokenKind::Integer])?;
        let version = version.text.unwrap();
        if version != "2.0" {
            return Err(ParsingError::WrongQasmVersion(version));
        }
        self.expect(TokenKind::Semicolon)?;
        Ok(())
    }

    /// `<includeStatement> ::= "include" <string> ";"`
    fn parse_include(&mut self) -> Result<(), ParsingError> {
        self.expect(TokenKind::Include)?;
        let path = self.expect(TokenKind::String)?;
        self.expect(TokenKind::Semicolon)?;

        // Remove the quotation marks around the string literal
        let mut path = path.text.unwrap();
        path.remove(0);
        path.remove(path.len() - 1);

        // Since we just popped a few tokens, we can be sure that no peeked element
        // is buffered. So no worries about accidentially reading tokens from the old
        // file.
        self.lexer
            .lexer
            .source_file(&path)
            .map_err(|err| ParsingError::IncludeError {
                file: path,
                reason: err.to_string(),
            })?;
        Ok(())
    }

    /// `<declaration> ::= ("qreg" | "creg") <identifier> <designator> ";"`
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

    /// `<gateDeclaration> ::= "gate" <identifier> [<params>] <idlist> "{" {<bodyStatement>} "}" | "opaque" <identifier> [<params>] <idlist> ";"`
    fn parse_gate_declaration(&mut self) -> Result<Statement, ParsingError> {
        let key = self.expect_either(&[TokenKind::Gate, TokenKind::Opaque])?;
        let identifier = self.expect(TokenKind::Identifier)?;
        let next_token = self.peek()?;
        let classical_params = if next_token.kind == TokenKind::LParen {
            self.parse_params()?
        } else {
            Vec::new()
        };
        let qubit_params = self.parse_idlist()?;
        let body = if key.kind == TokenKind::Gate {
            let body = self.parse_body()?;
            Some(body)
        } else {
            self.expect(TokenKind::Semicolon)?;
            None
        };
        Ok(Statement::GateDeclaration(GateDeclaration {
            name: identifier.text.unwrap(),
            params: classical_params,
            qubits: qubit_params,
            body,
        }))
    }

    /// `<quantumOperation> ::= <gateCall> | "measure" <argument> "->" <argument> ";" | "reset" <argument> ";"`
    fn parse_quantum_operation(&mut self) -> Result<Statement, ParsingError> {
        let next_token = self.peek()?;
        let statement = match next_token.kind {
            TokenKind::Measure => {
                self.expect(TokenKind::Measure)?;
                let src = self.parse_argument()?;
                self.expect(TokenKind::Arrow)?;
                let dest = self.parse_argument()?;
                self.expect(TokenKind::Semicolon)?;
                Ok(Statement::Measurement { src, dest })
            }
            TokenKind::Reset => {
                self.expect(TokenKind::Reset)?;
                let dest = self.parse_argument()?;
                self.expect(TokenKind::Semicolon)?;
                Ok(Statement::Reset { dest })
            }
            _ => self.parse_gate_call(),
        }?;
        Ok(statement)
    }

    /// `<ifStatement> ::= "if" "(" <identifier> "==" <integer> ")" <quantumOperation>`
    fn parse_if_statement(&mut self) -> Result<Statement, ParsingError> {
        self.expect(TokenKind::If)?;
        self.expect(TokenKind::LParen)?;
        let identifier = self.expect(TokenKind::Identifier)?;
        let variable = identifier.text.unwrap();
        self.expect(TokenKind::Equals)?;
        let condition = self.expect(TokenKind::Integer)?;
        let condition = condition.text.unwrap().parse()?;
        self.expect(TokenKind::RParen)?;
        let body = self.parse_quantum_operation()?;
        Ok(Statement::If {
            variable,
            condition,
            body: Box::new(body),
        })
    }

    /// `<gateCall> ::= ("U" | "CX" | <identifier>) [<args>] <mixedlist> ";"`
    fn parse_gate_call(&mut self) -> Result<Statement, ParsingError> {
        let gate = self.expect_either(&[TokenKind::U, TokenKind::CX, TokenKind::Identifier])?;
        // All gate names should be lowercase
        let name = match gate.kind {
            TokenKind::U => String::from("u"),
            TokenKind::CX => String::from("cx"),
            TokenKind::Identifier => gate.text.unwrap(),
            _ => unreachable!(),
        };
        let next_token = self.peek()?;
        let args = if next_token.kind == TokenKind::LParen {
            self.parse_args()?
        } else {
            Vec::new()
        };
        let qargs = self.parse_mixed_list()?;
        self.expect(TokenKind::Semicolon)?;
        Ok(Statement::GateCall(GateCall { name, args, qargs }))
    }

    /// `<barrier> ::= "barrier" <mixedlist> ";"`
    fn parse_barrier(&mut self) -> Result<Statement, ParsingError> {
        self.expect(TokenKind::Barrier)?;
        let arguments = self.parse_mixed_list()?;
        self.expect(TokenKind::Semicolon)?;
        Ok(Statement::Barrier(arguments))
    }

    /// `<body> ::= "{" {<bodyStatement>} "}"`
    fn parse_body(&mut self) -> Result<Vec<Statement>, ParsingError> {
        self.expect(TokenKind::LBrace)?;
        let mut statements = Vec::new();
        loop {
            // Parse next statement until we hit the closing brace
            let next_token = self.peek()?;
            if next_token.kind == TokenKind::RBrace {
                break;
            }

            let statement = self.parse_body_statement()?;
            statements.push(statement);
        }
        self.expect(TokenKind::RBrace)?;
        Ok(statements)
    }

    /// `<bodyStatement> ::= <gateCall> | "barrier" <idlist> ";"`
    fn parse_body_statement(&mut self) -> Result<Statement, ParsingError> {
        let next_token = self.peek()?;
        match next_token.kind {
            TokenKind::Barrier => {
                self.expect(TokenKind::Barrier)?;
                let identifiers = self.parse_idlist()?;
                self.expect(TokenKind::Semicolon)?;
                let arguments = identifiers
                    .into_iter()
                    .map(|id| Argument(id, None))
                    .collect();
                Ok(Statement::Barrier(arguments))
            }
            _ => self.parse_gate_call(),
        }
    }

    /// `<params> ::= "(" [<idlist>] ")"`
    fn parse_params(&mut self) -> Result<Vec<String>, ParsingError> {
        self.expect(TokenKind::LParen)?;
        let next_token = self.peek()?;
        let identifiers = if next_token.kind != TokenKind::RParen {
            self.parse_idlist()?
        } else {
            Vec::new()
        };
        self.expect(TokenKind::RParen)?;
        Ok(identifiers)
    }

    /// `<idlist> ::= <identifier> {"," <identifier>}`
    fn parse_idlist(&mut self) -> Result<Vec<String>, ParsingError> {
        let mut identifiers = Vec::new();
        let identifier = self.expect(TokenKind::Identifier)?;
        identifiers.push(identifier.text.unwrap());

        loop {
            // Parse more identifiers as long as there are commas
            let next_token = self.peek()?;
            if next_token.kind != TokenKind::Comma {
                break;
            }

            self.expect(TokenKind::Comma)?;
            let identifier = self.expect(TokenKind::Identifier)?;
            identifiers.push(identifier.text.unwrap());
        }
        Ok(identifiers)
    }

    /// `<args> ::= "(" [<explist>] ")"`
    fn parse_args(&mut self) -> Result<Vec<Expr>, ParsingError> {
        self.expect(TokenKind::LParen)?;
        let next_token = self.peek()?;
        let exprs = if next_token.kind != TokenKind::RParen {
            self.parse_exp_list()?
        } else {
            Vec::new()
        };
        self.expect(TokenKind::RParen)?;
        Ok(exprs)
    }

    /// `<explist> ::= <exp> {"," <exp>}`
    fn parse_exp_list(&mut self) -> Result<Vec<Expr>, ParsingError> {
        let mut exprs = Vec::new();
        exprs.push(self.parse_expr()?);
        loop {
            // Parse more expressions as long as there are commas
            let next_token = self.peek()?;
            if next_token.kind != TokenKind::Comma {
                break;
            }

            self.expect(TokenKind::Comma)?;
            exprs.push(self.parse_expr()?);
        }
        Ok(exprs)
    }

    /// `<mixedlist> ::= <argument> {"," <argument>}`
    fn parse_mixed_list(&mut self) -> Result<Vec<Argument>, ParsingError> {
        let mut args = Vec::new();
        args.push(self.parse_argument()?);
        loop {
            // Parse more arguments as long as there are commas
            let next_token = self.peek()?;
            if next_token.kind != TokenKind::Comma {
                break;
            }

            self.expect(TokenKind::Comma)?;
            args.push(self.parse_argument()?);
        }
        Ok(args)
    }

    /// `<argument> ::= <identifier> [<designator>]`
    fn parse_argument(&mut self) -> Result<Argument, ParsingError> {
        let identifier = self.expect(TokenKind::Identifier)?;
        let name = identifier.text.unwrap();
        let next_token = self.peek()?;
        let size = if next_token.kind == TokenKind::LBracket {
            Some(self.parse_designator()?)
        } else {
            None
        };
        Ok(Argument(name, size))
    }

    /// `<designator> ::= "[" <integer> "]"`
    fn parse_designator(&mut self) -> Result<usize, ParsingError> {
        self.expect(TokenKind::LBracket)?;
        let size = self.expect(TokenKind::Integer)?;
        self.expect(TokenKind::RBracket)?;
        size.text.unwrap().parse().map_err(Into::into)
    }

    /// `<exp> ::= <factor> | <exp> <binop> <exp>`
    fn parse_expr(&mut self) -> Result<Expr, ParsingError> {
        self.parse_expr_prec(Precedence::default())
    }

    fn parse_expr_prec(&mut self, min_prec: Precedence) -> Result<Expr, ParsingError> {
        let mut left = self.parse_factor()?;
        loop {
            // Peek the next token
            let next_token = self.peek()?;
            // If it is a binary operator...
            let Some(op) = Self::get_binop(next_token.kind) else {
                break;
            };
            // and it has higher precedence...
            if op.precedence() < min_prec {
                break;
            }

            // ...then parse as binary expr
            let kind = next_token.kind;
            self.expect(kind)?;
            let right = self.parse_expr_prec(op.precedence() + 1)?;
            left = Expr::Binary(op, Box::new(left), Box::new(right));
        }
        Ok(left)
    }

    /// `<factor> ::= <float> | <integer> | "pi" | <identifier> | "-" <factor> | "(" <exp> ")" | ("sin" | "cos" | "tan" | "exp" | "ln" | "sqrt") "(" <exp> ")"`
    fn parse_factor(&mut self) -> Result<Expr, ParsingError> {
        let token = self.expect_either(&[
            TokenKind::Float,
            TokenKind::Integer,
            TokenKind::Pi,
            TokenKind::Identifier,
            TokenKind::Minus,
            TokenKind::LParen,
            TokenKind::Sin,
            TokenKind::Cos,
            TokenKind::Tan,
            TokenKind::Exp,
            TokenKind::Ln,
            TokenKind::Sqrt,
        ])?;
        let expr = match token.kind {
            TokenKind::Float => Expr::Float(token.text.unwrap().parse()?),
            TokenKind::Integer => Expr::Int(token.text.unwrap().parse()?),
            TokenKind::Pi => Expr::Float(consts::PI),
            TokenKind::Identifier => Expr::Variable(token.text.unwrap()),
            TokenKind::Minus => {
                let inner = self.parse_factor()?;
                Expr::Unary(UnOp::Neg, Box::new(inner))
            }
            TokenKind::LParen => {
                let inner = self.parse_expr()?;
                self.expect(TokenKind::RParen)?;
                inner
            }
            _ => {
                let fun = match token.kind {
                    TokenKind::Sin => FuncType::Sin,
                    TokenKind::Cos => FuncType::Cos,
                    TokenKind::Tan => FuncType::Tan,
                    TokenKind::Exp => FuncType::Exp,
                    TokenKind::Ln => FuncType::Ln,
                    TokenKind::Sqrt => FuncType::Sqrt,
                    _ => unreachable!(),
                };
                self.expect(TokenKind::LParen)?;
                let inner = self.parse_expr()?;
                self.expect(TokenKind::RParen)?;
                Expr::Function(fun, Box::new(inner))
            }
        };
        Ok(expr)
    }

    /// Returns the [`BinOp`] this token represents (if it is a binary operator).
    fn get_binop(kind: TokenKind) -> Option<BinOp> {
        match kind {
            TokenKind::Plus => Some(BinOp::Add),
            TokenKind::Minus => Some(BinOp::Sub),
            TokenKind::Asterisk => Some(BinOp::Mul),
            TokenKind::Slash => Some(BinOp::Div),
            TokenKind::Caret => Some(BinOp::BitXor),
            _ => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::lexing::MultiLexer;

    use super::*;

    #[test]
    fn single_declaration() {
        let text = "OPENQASM 2.0; qreg foo[5];";
        let lexer = MultiLexer::from_text(text.into());
        let mut parser = Parser::new(PeekableMultiLexer::new(lexer));
        let res = parser.parse();
        assert_eq!(
            res,
            Ok(Program {
                statements: vec![Statement::qreg("foo", 5)]
            })
        );
    }

    #[test]
    fn bell_state() {
        let text = "\
OPENQASM 2.0;

qreg q[2];
creg c[2];
U(pi/2, 0, pi) q[0];
CX q[0], q[1];
measure q -> c;";
        let lexer = MultiLexer::from_text(text.into());
        let mut parser = Parser::new(PeekableMultiLexer::new(lexer));
        let res = parser.parse();
        assert_eq!(
            res,
            Ok(Program {
                statements: vec![
                    Statement::qreg("q", 2),
                    Statement::creg("c", 2),
                    Statement::gate_call(
                        "u",
                        vec![
                            Expr::Binary(
                                BinOp::Div,
                                Box::new(Expr::Float(consts::PI)),
                                Box::new(Expr::Int(2))
                            ),
                            Expr::Int(0),
                            Expr::Float(consts::PI)
                        ],
                        vec![Argument("q".into(), Some(0))]
                    ),
                    Statement::gate_call(
                        "cx",
                        vec![],
                        vec![Argument("q".into(), Some(0)), Argument("q".into(), Some(1))]
                    ),
                    Statement::Measurement {
                        src: Argument("q".into(), None),
                        dest: Argument("c".into(), None)
                    }
                ]
            })
        );
    }

    #[test]
    fn only_include() {
        let text = "OPENQASM 2.0; include \"qelib1.inc\";";
        let lexer = MultiLexer::from_text(text.into());
        let mut parser = Parser::new(PeekableMultiLexer::new(lexer));
        let res = parser.parse();
        assert!(res.is_ok(), "{res:?}");
    }

    #[test]
    fn expr_mul_funcs() {
        let text = "OPENQASM 2.0; qreg q[1]; u1(cos(3.14) * sin(0)) q[0];";
        let lexer = MultiLexer::from_text(text.into());
        let mut parser = Parser::new(PeekableMultiLexer::new(lexer));
        let res = parser.parse();
        assert_eq!(
            res,
            Ok(Program {
                statements: vec![
                    Statement::qreg("q", 1),
                    Statement::gate_call(
                        "u1",
                        vec![Expr::Binary(
                            BinOp::Mul,
                            Box::new(Expr::Function(FuncType::Cos, Box::new(Expr::Float(3.14)))),
                            Box::new(Expr::Function(FuncType::Sin, Box::new(Expr::Int(0))))
                        )],
                        vec![Argument("q".into(), Some(0))]
                    )
                ]
            })
        );
    }

    #[test]
    fn custom_gate_decl_and_call() {
        let text = "OPENQASM 2.0; gate foo(a) c,t { cp(a) c, t; } qreg q[2]; foo(pi) q[1], q[0];";
        let lexer = MultiLexer::from_text(text.into());
        let mut parser = Parser::new(PeekableMultiLexer::new(lexer));
        let res = parser.parse();
        assert_eq!(
            res,
            Ok(Program {
                statements: vec![
                    Statement::gate_declaration(
                        "foo",
                        vec!["a".into()],
                        vec!["c".into(), "t".into()],
                        vec![Statement::gate_call(
                            "cp",
                            vec![Expr::Variable("a".into())],
                            vec![Argument("c".into(), None), Argument("t".into(), None)]
                        )]
                    ),
                    Statement::qreg("q", 2),
                    Statement::gate_call(
                        "foo",
                        vec![Expr::Float(consts::PI)],
                        vec![Argument("q".into(), Some(1)), Argument("q".into(), Some(0))]
                    )
                ]
            })
        );
    }

    #[test]
    fn if_statement() {
        let text = "OPENQASM 2.0; qreg q[1]; creg c[2]; if(c==3) h q[0];";
        let lexer = MultiLexer::from_text(text.into());
        let mut parser = Parser::new(PeekableMultiLexer::new(lexer));
        let res = parser.parse();
        assert_eq!(
            res,
            Ok(Program {
                statements: vec![
                    Statement::qreg("q", 1),
                    Statement::creg("c", 2),
                    Statement::If {
                        variable: "c".into(),
                        condition: 3,
                        body: Box::new(Statement::gate_call(
                            "h",
                            vec![],
                            vec![Argument("q".into(), Some(0))]
                        ))
                    }
                ]
            })
        );
    }
}
