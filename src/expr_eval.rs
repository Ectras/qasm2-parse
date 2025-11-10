use crate::ast::{BinOp, Expr, FuncType, UnOp};

/// Numerically evalutes expressions. The expressions should no longer contain
/// variables. Also, BitXor is currently not supported.
pub fn eval(expr: &Expr) -> f64 {
    match expr {
        Expr::Int(x) => *x as _,
        Expr::Float(x) => *x,
        Expr::Variable(_) => panic!("Can not evaluate expressions with variables"),
        Expr::Unary(un_op, inner) => eval_unop(*un_op, &inner),
        Expr::Binary(bin_op, lhs, rhs) => eval_binop(*bin_op, &lhs, &rhs),
        Expr::Function(func_type, inner) => eval_func(*func_type, &inner),
    }
}

fn eval_unop(op: UnOp, inner: &Expr) -> f64 {
    match op {
        UnOp::Neg => -eval(inner),
    }
}

fn eval_binop(op: BinOp, lhs: &Expr, rhs: &Expr) -> f64 {
    let lhs = eval(lhs);
    let rhs = eval(rhs);
    match op {
        BinOp::Add => lhs + rhs,
        BinOp::Sub => lhs - rhs,
        BinOp::Mul => lhs * rhs,
        BinOp::Div => lhs / rhs,
        // BitXor only works on integers, so one would need to return a Float/Int
        // enum from the eval methods and check that both operands are int. This is
        // not hard to do, but given how unimportant the bitxor is, this is left for
        // future work.
        BinOp::BitXor => panic!("BitXor is not supported"),
    }
}

fn eval_func(op: FuncType, inner: &Expr) -> f64 {
    let val = eval(inner);
    match op {
        FuncType::Sin => val.sin(),
        FuncType::Cos => val.cos(),
        FuncType::Tan => val.tan(),
        FuncType::Exp => val.exp(),
        FuncType::Ln => val.ln(),
        FuncType::Sqrt => val.sqrt(),
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
            Box::new(Expr::Int(-2)),
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
}
