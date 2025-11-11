use qasm2_parse::{
    ast::Statement,
    gate_inliner::{GateInliner, gate_sets},
};

#[test]
fn full_inlining() {
    let code = include_str!("random_indep_qiskit_10.qasm");
    let mut program = qasm2_parse::parse_string(code.to_owned()).expect("Error parsing file");

    let mut inliner = GateInliner::new(&gate_sets::MINIMAL);
    inliner
        .inline_program(&mut program)
        .expect("Error inlining");

    // Assert that no gate declarations are left and all gate calls are U or CX
    for statement in &program.statements {
        match statement {
            Statement::GateDeclaration(gate_declaration) => {
                panic!("Expected no gate declaration, but found {gate_declaration:?}")
            }
            Statement::GateCall(gate_call) => assert!(
                gate_call.name == "U" || gate_call.name == "CX",
                "Expected only U or CX calls, but found {gate_call:?}"
            ),
            _ => (),
        }
    }
}
