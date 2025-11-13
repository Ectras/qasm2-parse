use std::iter::zip;

use rustc_hash::{FxHashMap, FxHashSet};
use thiserror::Error;

use crate::ast::{Expr, GateCall, GateDeclaration, Program, Statement};

#[derive(Error, Debug, PartialEq, Eq)]
pub enum GateCallError {
    #[error("Wrong number of classical arguments: Got {actual} but expected {expected}")]
    WrongNumberClassicalArgs { actual: usize, expected: usize },
    #[error("Wrong number of quantum arguments: Got {actual} but expected {expected}")]
    WrongNumberQuantumArgs { actual: usize, expected: usize },
    #[error("The called gate \"{0}\" was not yet defined")]
    UndefinedGate(String),
    #[error("The called gate \"{0}\" is opaque and not known")]
    OpaqueGate(String),
    #[error("Undefined variable \"{0}\"")]
    UndefinedVariable(String),
}

/// A set of gate names.
pub type GateSet = FxHashSet<&'static str>;

/// Predefined gate sets.
pub mod gate_sets {
    use lazy_static::lazy_static;
    use rustc_hash::FxHashSet;

    use crate::gate_inliner::GateSet;

    lazy_static! {
        /// Gate set containing only the `U` and `CX` gate.
        pub static ref MINIMAL: GateSet = FxHashSet::from_iter(["U", "CX"]);

        /// Gate set containing all gates from the `qelib1.inc` standard file.
        pub static ref STANDARD: GateSet = FxHashSet::from_iter([
            "U", "CX", "u3", "u2", "u1", "cx", "id", "u0", "u", "p", "x", "y", "z", "h", "s", "sdg", "t",
            "tdg", "rx", "ry", "rz", "sx", "sxdg", "cz", "cy", "swap", "ch", "ccx", "cswap", "crx",
            "cry", "crz", "cu1", "cp", "cu3", "csx", "cu", "rxx", "rzz", "rccx", "rc3x", "c3x",
            "c3sqrtx", "c4x",
        ]);
    }
}

/// Struct to inline gate calls with previous gate declarations.
#[derive(Debug)]
pub struct GateInliner<'a> {
    definitions: FxHashMap<String, GateDeclaration>,
    terminal_gates: &'a GateSet,
}

impl<'a> GateInliner<'a> {
    /// Creates a new inliner that inlines all gate calls with the respective gate
    /// definitions until all calls are to gates in the `gate_set`. Predefined gate
    /// sets can be found in [`gate_sets`].
    pub fn new(gate_set: &'a GateSet) -> Self {
        Self {
            definitions: FxHashMap::default(),
            terminal_gates: gate_set,
        }
    }

    /// Returns whether a gate with the given name is terminal, i.e., doesn't need
    /// further inlining.
    fn is_terminal_gate(&self, name: &str) -> bool {
        self.terminal_gates.contains(name)
    }

    /// Traverses an expression and replaces all variables with the expressions given
    /// by the context.
    fn replace_vars(
        expr: &mut Expr,
        context: &FxHashMap<&String, &Expr>,
    ) -> Result<(), GateCallError> {
        match expr {
            Expr::Variable(x) => {
                let Some(val) = context.get(x) else {
                    return Err(GateCallError::UndefinedVariable(x.clone()));
                };
                *expr = (*val).clone();
            }
            Expr::Unary(_, inner) | Expr::Function(_, inner) => Self::replace_vars(inner, context)?,
            Expr::Binary(_, lhs, rhs) => {
                Self::replace_vars(lhs, context)?;
                Self::replace_vars(rhs, context)?;
            }
            _ => (),
        }
        Ok(())
    }

    /// Returns a copy of the body of callee with the specific data filled in from
    /// the gate call.
    fn get_body(
        &self,
        call: &GateCall,
        callee: &GateDeclaration,
    ) -> Result<Vec<Statement>, GateCallError> {
        // We can only inline non-opaque gates
        let Some(body) = &callee.body else {
            return Err(GateCallError::OpaqueGate(callee.name.clone()));
        };

        // Map the names in the declaration to the actual values passed in the call
        let binded_vars = if callee.params.len() == call.args.len() {
            zip(&callee.params, &call.args).collect::<FxHashMap<_, _>>()
        } else {
            return Err(GateCallError::WrongNumberClassicalArgs {
                actual: call.args.len(),
                expected: callee.params.len(),
            });
        };
        let binded_qargs = if callee.qubits.len() == call.qargs.len() {
            zip(&callee.qubits, &call.qargs).collect::<FxHashMap<_, _>>()
        } else {
            return Err(GateCallError::WrongNumberQuantumArgs {
                actual: call.qargs.len(),
                expected: callee.qubits.len(),
            });
        };

        // Replace the variables in the body with the actual values
        let mut statements = Vec::with_capacity(body.len());
        for statement in body {
            let Statement::GateCall(call) = statement else {
                // TODO: It can also contain barriers
                panic!("Expected only gate calls in a gate definition")
            };

            // Ensure that all calls of the gates to be inlined are already inlined
            assert!(self.is_terminal_gate(&call.name));

            // Replace any used variables by their actual values given by the caller
            let mut new_args = Vec::with_capacity(call.args.len());
            for arg in &call.args {
                let mut arg = arg.clone();
                Self::replace_vars(&mut arg, &binded_vars)?;
                new_args.push(arg);
            }

            // Replace any used qubit by the actual qreg reference
            let mut new_qargs = Vec::with_capacity(call.qargs.len());
            for qarg in &call.qargs {
                let Some(global_name) = binded_qargs.get(&qarg.0) else {
                    return Err(GateCallError::UndefinedVariable(qarg.0.clone()));
                };
                new_qargs.push((*global_name).clone());
            }

            statements.push(Statement::GateCall(GateCall {
                name: call.name.clone(),
                args: new_args,
                qargs: new_qargs,
            }));
        }
        Ok(statements)
    }

    /// Returns the body of the called gate, with all parameters filled in.
    fn get_inlined_body(&self, call: &GateCall) -> Result<Vec<Statement>, GateCallError> {
        if let Some(callee) = self.definitions.get(&call.name) {
            self.get_body(call, callee)
        } else {
            Err(GateCallError::UndefinedGate(call.name.clone()))
        }
    }

    /// Takes a list of statements and inlines every gate call with the corresponding
    /// gate definition. Gate definitions are removed and added to the internal list
    /// of known gates.
    fn inline(&mut self, statements: &mut Vec<Statement>) -> Result<(), GateCallError> {
        enum Change {
            Remove(usize),
            Replace(usize, Vec<Statement>),
        }

        let mut changes = Vec::new();
        for (i, statement) in statements.iter_mut().enumerate() {
            match statement {
                Statement::GateDeclaration(data) => {
                    // Take ownership of gate body from AST node
                    let mut data = std::mem::take(data);

                    // Inline all gate calls inside the gate body
                    if let Some(body) = data.body.as_mut() {
                        self.inline(body)?;
                    }

                    // Store the gate and mark statement as to be removed
                    self.register_gate(data);
                    changes.push(Change::Remove(i));
                }
                Statement::GateCall(call) => {
                    if !self.is_terminal_gate(&call.name) {
                        // Get the inlined body and mark the call as to be replaced
                        let body = self.get_inlined_body(call)?;
                        changes.push(Change::Replace(i, body));
                    }
                }
                _ => (),
            }
        }

        // Since we are done iterating, apply all changes.
        // Changes are applied in reverse, as the indices would otherwise become wrong.
        for change in changes.into_iter().rev() {
            match change {
                Change::Remove(idx) => {
                    statements.remove(idx);
                }
                Change::Replace(idx, body) => {
                    statements.splice(idx..=idx, body);
                }
            }
        }
        Ok(())
    }

    /// Registers a new gate definition.
    fn register_gate(&mut self, gate: GateDeclaration) {
        self.definitions.insert(gate.name.clone(), gate);
    }

    /// Inlines all gate calls in the program.
    pub fn inline_program(&mut self, program: &mut Program) -> Result<(), GateCallError> {
        self.inline(&mut program.statements)
    }
}

#[cfg(test)]
mod tests {
    use crate::ast::{Argument, BinOp, FuncType, UnOp};

    use super::*;

    use rustc_hash::FxHashMap;

    #[test]
    fn recursive_inline() {
        // INPUT:
        // gate bar (a, b) q {
        //   U(a + b, 0, b) q;
        // }
        // gate foo (a) q1, q2 {
        //   bar(a, 0) q2;
        //   U(1, 2, 3) q1;
        //   bar(1, a) q1;
        // }
        // foo(2) q[0], q[1];

        // RESULT:
        // U(2 + 0, 0, 0) q[1];
        // U(1, 2, 3) q[0];
        // U(1 + 2, 0, 2) q[0];

        let mut program = Program {
            statements: vec![
                Statement::gate_declaration(
                    "bar",
                    vec![String::from("a"), String::from("b")],
                    vec![String::from("q")],
                    vec![Statement::gate_call(
                        "U",
                        vec![
                            Expr::Binary(
                                BinOp::Add,
                                Box::new(Expr::Variable(String::from("a"))),
                                Box::new(Expr::Variable(String::from("b"))),
                            ),
                            Expr::Int(0),
                            Expr::Variable(String::from("b")),
                        ],
                        vec![Argument(String::from("q"), None)],
                    )],
                ),
                Statement::gate_declaration(
                    "foo",
                    vec![String::from("a")],
                    vec![String::from("q1"), String::from("q2")],
                    vec![
                        Statement::gate_call(
                            "bar",
                            vec![Expr::Variable(String::from("a")), Expr::Int(0)],
                            vec![Argument(String::from("q2"), None)],
                        ),
                        Statement::gate_call(
                            "U",
                            vec![Expr::Int(1), Expr::Int(2), Expr::Int(3)],
                            vec![Argument(String::from("q1"), None)],
                        ),
                        Statement::gate_call(
                            "bar",
                            vec![Expr::Int(1), Expr::Variable(String::from("a"))],
                            vec![Argument(String::from("q1"), None)],
                        ),
                    ],
                ),
                Statement::gate_call(
                    "foo",
                    vec![Expr::Int(2)],
                    vec![
                        Argument(String::from("q"), Some(0)),
                        Argument(String::from("q"), Some(1)),
                    ],
                ),
            ],
        };

        let mut inliner = GateInliner::new(&gate_sets::MINIMAL);
        let result = inliner.inline_program(&mut program);

        assert_eq!(result, Ok(()));
        assert_eq!(
            program,
            Program {
                statements: vec![
                    Statement::gate_call(
                        "U",
                        vec![
                            Expr::Binary(
                                BinOp::Add,
                                Box::new(Expr::Int(2)),
                                Box::new(Expr::Int(0))
                            ),
                            Expr::Int(0),
                            Expr::Int(0)
                        ],
                        vec![Argument(String::from("q"), Some(1))]
                    ),
                    Statement::gate_call(
                        "U",
                        vec![Expr::Int(1), Expr::Int(2), Expr::Int(3)],
                        vec![Argument(String::from("q"), Some(0))]
                    ),
                    Statement::gate_call(
                        "U",
                        vec![
                            Expr::Binary(
                                BinOp::Add,
                                Box::new(Expr::Int(1)),
                                Box::new(Expr::Int(2))
                            ),
                            Expr::Int(0),
                            Expr::Int(2)
                        ],
                        vec![Argument(String::from("q"), Some(0))]
                    )
                ]
            }
        );
    }

    #[test]
    fn replacement_of_vars_in_expr() {
        // INPUT:
        // sin(a) + b, with a = 2, b = -4, c = 42
        //
        // RESULT:
        // sin(2) + (-4)

        let mut expr = Expr::Binary(
            BinOp::Add,
            Box::new(Expr::Function(
                FuncType::Sin,
                Box::new(Expr::Variable(String::from("a"))),
            )),
            Box::new(Expr::Variable(String::from("b"))),
        );

        let a = String::from("a");
        let b = String::from("b");
        let c = String::from("c");
        let expr_a = Expr::Int(2);
        let expr_b = Expr::Unary(UnOp::Neg, Box::new(Expr::Int(4)));
        let expr_c = Expr::Int(42);
        let context = FxHashMap::from_iter([(&a, &expr_a), (&b, &expr_b), (&c, &expr_c)]);

        let replaced = Expr::Binary(
            BinOp::Add,
            Box::new(Expr::Function(FuncType::Sin, Box::new(expr_a.clone()))),
            Box::new(expr_b.clone()),
        );

        let result = GateInliner::replace_vars(&mut expr, &context);
        assert_eq!(result, Ok(()));
        assert_eq!(expr, replaced);
    }
}
