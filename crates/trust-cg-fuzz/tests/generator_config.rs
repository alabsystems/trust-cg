use trust_cg_codegen::interpreter::{InterpreterValue, interpret};
use trust_cg_fuzz::trust_ir_gen::{FUZZ_FN_NAME, GenConfig, gen_module};

#[test]
fn zero_parameter_generation_has_a_real_operand_and_is_reproducible() {
    for num_ops in [0, 1, 8] {
        let config = GenConfig {
            num_params: 0,
            num_ops,
            allow_div: false,
            allow_shift: false,
        };
        for seed in 0..8 {
            let first = gen_module(seed, &config).expect("the generated module builds");
            let second = gen_module(seed, &config).expect("the generated module builds");
            assert_eq!(
                serde_json::to_vec(&first).unwrap(),
                serde_json::to_vec(&second).unwrap()
            );
            let result = interpret(&first, FUZZ_FN_NAME, &[]).unwrap();
            assert!(matches!(result.as_slice(), [InterpreterValue::Int(_)]));
        }
    }
}

#[test]
fn zero_operations_still_return_the_last_parameter() {
    let config = GenConfig {
        num_params: 2,
        num_ops: 0,
        ..GenConfig::default()
    };
    let module = gen_module(42, &config).expect("the generated module builds");
    let result = interpret(
        &module,
        FUZZ_FN_NAME,
        &[InterpreterValue::Int(5), InterpreterValue::Int(9)],
    )
    .unwrap();
    assert!(matches!(result.as_slice(), [InterpreterValue::Int(9)]));
}
