use std::{
    f64::consts,
    ops::{Add, Div, Mul, Neg, Sub},
};

use crate::ast::{BinOp, Expr, FuncType, GateCall, Program, Statement, UnOp};

/// Replaces all expressions inside gate calls with their numerical result. This does
/// *not* traverse into gate definitions.
pub fn eval_all_args(program: &mut Program) {
    for statement in &mut program.statements {
        if let Statement::GateCall(GateCall { args, .. }) = statement {
            for arg in args.iter_mut() {
                *arg = Expr::Float(eval(arg));
            }
        }
    }
}

/// Numerically evalutes expressions. The expressions should no longer contain
/// variables. Also, BitXor is currently not supported.
#[inline]
pub fn eval(expr: &Expr) -> f64 {
    eval_expr(expr).float()
}

fn eval_expr(expr: &Expr) -> Value {
    match expr {
        Expr::Pi => Value::Float(consts::PI),
        Expr::Int(x) => Value::Int((*x).try_into().unwrap()),
        Expr::Float(x) => Value::Float(*x),
        Expr::Variable(_) => panic!("Can not evaluate expressions with variables"),
        Expr::Unary(un_op, inner) => eval_unop(*un_op, inner),
        Expr::Binary(bin_op, lhs, rhs) => eval_binop(*bin_op, lhs, rhs),
        Expr::Function(func_type, inner) => eval_func(*func_type, inner),
    }
}

fn eval_unop(op: UnOp, inner: &Expr) -> Value {
    match op {
        UnOp::Neg => -eval_expr(inner),
    }
}

fn eval_binop(op: BinOp, lhs: &Expr, rhs: &Expr) -> Value {
    let lhs = eval_expr(lhs);
    let rhs = eval_expr(rhs);
    match op {
        BinOp::Add => lhs + rhs,
        BinOp::Sub => lhs - rhs,
        BinOp::Mul => lhs * rhs,
        BinOp::Div => lhs / rhs,
        BinOp::BitXor => match (lhs, rhs) {
            (Value::Int(a), Value::Int(b)) => Value::Int(a ^ b),
            _ => panic!("BitXor is only allowed between integers"),
        },
    }
}

fn eval_func(op: FuncType, inner: &Expr) -> Value {
    let val = eval_expr(inner).float();
    let res = match op {
        FuncType::Sin => val.sin(),
        FuncType::Cos => val.cos(),
        FuncType::Tan => val.tan(),
        FuncType::Exp => val.exp(),
        FuncType::Ln => val.ln(),
        FuncType::Sqrt => val.sqrt(),
    };
    Value::Float(res)
}

/// A numerical typed value.
#[derive(Debug, Clone, Copy, PartialEq)]
enum Value {
    /// A floating point number.
    Float(f64),
    /// An integer number.
    Int(i64),
}

impl Value {
    fn float(self) -> f64 {
        match self {
            Value::Float(x) => x,
            Value::Int(x) => x as _,
        }
    }
}

impl Neg for Value {
    type Output = Value;

    fn neg(self) -> Self::Output {
        match self {
            Value::Float(x) => Value::Float(-x),
            Value::Int(x) => Value::Int(-x),
        }
    }
}

impl Add for Value {
    type Output = Value;

    fn add(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (Value::Int(a), Value::Int(b)) => Value::Int(a + b),
            _ => Value::Float(self.float() + rhs.float()),
        }
    }
}

impl Sub for Value {
    type Output = Value;

    fn sub(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (Value::Int(a), Value::Int(b)) => Value::Int(a - b),
            _ => Value::Float(self.float() - rhs.float()),
        }
    }
}

impl Mul for Value {
    type Output = Value;

    fn mul(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (Value::Int(a), Value::Int(b)) => Value::Int(a * b),
            _ => Value::Float(self.float() * rhs.float()),
        }
    }
}

impl Div for Value {
    type Output = Value;

    fn div(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (Value::Int(a), Value::Int(b)) => Value::Int(a / b),
            _ => Value::Float(self.float() / rhs.float()),
        }
    }
}

#[cfg(test)]
mod tests {
    use std::f64::consts;

    use float_cmp::assert_approx_eq;

    use super::*;

    #[test]
    fn eval_add() {
        // -2 + 2
        let out = eval(&Expr::Binary(
            BinOp::Add,
            Box::new(Expr::Unary(UnOp::Neg, Box::new(Expr::Int(2)))),
            Box::new(Expr::Int(2)),
        ));
        assert_approx_eq!(f64, out, 0.0);
    }

    #[test]
    fn eval_div() {
        // 3.6 / -2.4
        let out = eval(&Expr::Binary(
            BinOp::Div,
            Box::new(Expr::Float(3.6)),
            Box::new(Expr::Float(-2.4)),
        ));
        assert_approx_eq!(f64, out, -1.5);
    }

    #[test]
    fn eval_fun() {
        // 2 * sin(pi / 2)
        let out = eval(&Expr::Binary(
            BinOp::Mul,
            Box::new(Expr::Int(2)),
            Box::new(Expr::Function(
                FuncType::Sin,
                Box::new(Expr::Binary(
                    BinOp::Div,
                    Box::new(Expr::Float(consts::PI)),
                    Box::new(Expr::Int(2)),
                )),
            )),
        ));
        assert_approx_eq!(f64, out, 2.0);
    }

    #[test]
    fn eval_linear() {
        // (2 + 3) * 4.0
        let out = eval(&Expr::Binary(
            BinOp::Mul,
            Box::new(Expr::Binary(
                BinOp::Add,
                Box::new(Expr::Int(2)),
                Box::new(Expr::Int(3)),
            )),
            Box::new(Expr::Float(4.0)),
        ));
        assert_approx_eq!(f64, out, 20.0);
    }

    #[test]
    fn eval_bitxor() {
        // 3 ^ 5
        let out = eval(&Expr::Binary(
            BinOp::BitXor,
            Box::new(Expr::Int(3)),
            Box::new(Expr::Int(5)),
        ));
        assert_approx_eq!(f64, out, 6.0);
    }

    #[test]
    #[should_panic(expected = "BitXor is only allowed between integers")]
    fn eval_bitxor_float_fails() {
        // 3 ^ 5.0
        let _ = eval(&Expr::Binary(
            BinOp::BitXor,
            Box::new(Expr::Int(3)),
            Box::new(Expr::Float(5.0)),
        ));
    }

    #[test]
    fn eval_expr_int_mul() {
        // 5 * 3
        let out = eval_expr(&Expr::Binary(
            BinOp::Mul,
            Box::new(Expr::Int(5)),
            Box::new(Expr::Int(3)),
        ));
        assert_eq!(out, Value::Int(15));
    }

    #[test]
    fn eval_expr_mixed_sub() {
        // 2.0 - 4
        let out = eval_expr(&Expr::Binary(
            BinOp::Sub,
            Box::new(Expr::Float(2.0)),
            Box::new(Expr::Int(4)),
        ));

        let Value::Float(f) = out else {
            panic!("Expected float")
        };
        assert_approx_eq!(f64, f, -2.0);
    }

    #[test]
    fn eval_expr_fun_int_arg() {
        // sqrt(25)
        let out = eval_expr(&Expr::Function(FuncType::Sqrt, Box::new(Expr::Int(25))));

        let Value::Float(f) = out else {
            panic!("Expected float")
        };
        assert_approx_eq!(f64, f, 5.0);
    }
}
