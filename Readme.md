# qasm2-parse

This create provides functionality to parse [OpenQASM 2](https://arxiv.org/abs/1707.03429) code into an abstract syntax tree (AST) that can then be used to e.g. construct a quantum circuit from it.

Example:
```rust
use qasm2_parse::parse_string;

fn main() {
    // Load from string
    let text = "\
OPENQASM 2.0;

qreg q[2];
creg c[2];
U(pi/2, 0, pi) q[0];
CX q[0], q[1];
measure q -> c;";
    let program = parse_string(text.to_owned()).unwrap();

    // Load from file
    let program = parse_file("foo.qasm").unwrap().unwrap();
}
```

## Additional functionality

### Include file handling
Include statements will be resolved during parsing and the final parsed program will contain all definitions from the included files.
The `qelib1.inc` file which has definitions of common gates is built in.
```rust
use qasm2_parse::parse_string;

fn main() {
    let text = "\
OPENQASM 2.0;
include \"qelib1.inc\";
";

    let program = parse_string(text.to_owned()).unwrap();

    assert_eq!(program.statements.len(), 42);
}
```

### Gate inlining
OpenQASM 2 allows the users to define custom gates as a sequence of calls to other gates.
Actually, the only built-in gates are `U` and `CX`.
Other standard gates are provided by the include file `qelib1.inc` and are defined in terms of `U` and `CX` files.

To make it easier to work with programs of these different levels of abstractions, this crate provides a gate inliner.
It will recursively inline custom gates until only calls to "known" gates are left (where the set of known gate names can be provided by the user).

Example:
```rust
use qasm2_parse::{gate_inliner::GateInliner, parse_string};

fn main() {
    let text = "\
OPENQASM 2.0;
gate u3(theta,phi,lambda) q {
    U(theta,phi,lambda) q;
}

gate x a {
    u3(pi,0,pi) a;
}

qreg q[1];
x q[0];";

    let mut program = parse_string(text.to_owned()).unwrap();
    let mut inliner = GateInliner::new_full_inliner();
    inliner.inline_program(&mut program).unwrap();

    assert_eq!(
        program.to_string(),
        "\
OPENQASM 2.0;
qreg q[1];
U(pi, 0, pi) q[0];
"
    );
}
```

### Expression evaluation
Expressions (such as in the classical arguments of gate calls) can be numerically evaluated.
Note that this only evaluates the gate calls on the outer level, as gate calls within gate declarations might contain variables whose value is not known yet.

Example:
```rust
use qasm2_parse::{expr_eval::eval_all_args, parse_string};

fn main() {
    let text = "\
OPENQASM 2.0;
qreg q[1];
U(2*pi + sin(4.0), 0, 0) q[0];";

    let mut program = parse_string(text.to_owned()).unwrap();
    eval_all_args(&mut program);

    assert_eq!(
        program.to_string(),
        "\
OPENQASM 2.0;
qreg q[1];
U(5.526382811871658, 0, 0) q[0];
"
    );
}
```

## Planned features
- Annotate parsing errors with source locations
- Make include resolving an (optional) separate step?
- Support BitXor in expression evaluation
- Make parsing only require &str, not String
