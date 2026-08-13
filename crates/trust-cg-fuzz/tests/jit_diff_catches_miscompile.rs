// trust-cg-fuzz/tests/jit_diff_catches_miscompile.rs
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Part of #436.

// The jit_diff harness is unix-only (its per-invoke sandbox is a POSIX fork);
// mirror that gate here so the test compiles out cleanly on non-unix hosts
// rather than failing to resolve `trust_cg_fuzz::jit_diff`.
#![cfg(all(unix, any(target_arch = "aarch64", target_arch = "x86_64")))]

use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_fuzz::jit_diff::{JitOutcome, classify_outputs, compile_and_run, run_oracle_one};
use trust_cg_fuzz::trust_ir_gen::{GenConfig, gen_module};

fn fixture_module() -> trust_ir::Module {
    let cfg = GenConfig {
        num_params: 4,
        num_ops: 4,
        allow_div: false,
        allow_shift: false,
    };
    gen_module(42, &cfg)
}

#[test]
fn harness_flags_synthetic_o2_miscompile() {
    let module = fixture_module();
    let row: [i64; 4] = [1, 2, 3, 4];
    let oracle = run_oracle_one(&module, &row);
    let o0 = compile_and_run(&module, OptLevel::O0, &row);

    let oracle_val = oracle.clone().expect("interpreter must succeed on fixture");
    let o0_val = match o0.clone() {
        JitOutcome::Value(v) => v,
        other => panic!("O0 JIT must produce a value on fixture, got {:?}", other),
    };
    assert_eq!(oracle_val, o0_val);

    let fake_o2 = JitOutcome::Value(o0_val.wrapping_add(1));
    let verdict = classify_outputs(Some(oracle), &o0, &fake_o2, &row);
    let (category, summary) = verdict.expect("harness must flag oracle != O2 disagreement");
    assert_eq!(category, "miscompile");
    assert!(summary.contains("interp=") && summary.contains("O2_jit="));
}

#[test]
fn harness_flags_synthetic_o0_miscompile() {
    let module = fixture_module();
    let row: [i64; 4] = [5, 6, 7, 8];
    let oracle = run_oracle_one(&module, &row);
    let o2 = compile_and_run(&module, OptLevel::O2, &row);

    let oracle_val = oracle.clone().expect("interpreter must succeed");
    let o2_val = match o2.clone() {
        JitOutcome::Value(v) => v,
        other => panic!("O2 JIT must produce a value, got {:?}", other),
    };
    assert_eq!(oracle_val, o2_val);

    let fake_o0 = JitOutcome::Value(o2_val.wrapping_sub(7));
    let verdict = classify_outputs(Some(oracle), &fake_o0, &o2, &row);
    let (category, summary) = verdict.expect("harness must flag oracle != O0 disagreement");
    assert_eq!(category, "miscompile");
    assert!(summary.contains("O0_jit=") && summary.contains("interp="));
}

#[test]
fn harness_flags_o0_vs_o2_disagreement_even_when_oracle_silent() {
    let row: [i64; 4] = [0, 0, 0, 0];
    let o0 = JitOutcome::Value(100);
    let o2 = JitOutcome::Value(101);

    let verdict = classify_outputs(None, &o0, &o2, &row);
    let (category, summary) = verdict.expect("must catch O0/O2 disagreement without oracle");
    assert_eq!(category, "miscompile");
    assert!(summary.contains("O0_jit=100"));
    assert!(summary.contains("O2_jit=101"));
}

#[test]
fn harness_returns_none_when_all_three_agree() {
    let row: [i64; 4] = [1, 2, 3, 4];
    let oracle = Some(Ok(42i64));
    let o0 = JitOutcome::Value(42);
    let o2 = JitOutcome::Value(42);

    assert!(classify_outputs(oracle, &o0, &o2, &row).is_none());
}

#[test]
fn harness_flags_o2_panic_as_crash() {
    let row: [i64; 4] = [0, 0, 0, 0];
    let o0 = JitOutcome::Value(7);
    let o2 = JitOutcome::Panic("simulated_crash".to_string());

    let (category, summary) =
        classify_outputs(Some(Ok(7)), &o0, &o2, &row).expect("panic must produce a finding");
    assert_eq!(category, "crash");
    assert!(summary.contains("O2 JIT panic"));
    assert!(summary.contains("simulated_crash"));
}

#[test]
fn harness_flags_o0_timeout_as_timeout() {
    let row: [i64; 4] = [0, 0, 0, 0];
    let o0 = JitOutcome::Timeout;
    let o2 = JitOutcome::Value(0);

    let (category, _) =
        classify_outputs(Some(Ok(0)), &o0, &o2, &row).expect("timeout must produce a finding");
    assert_eq!(category, "timeout");
}

// --- Hardware-trap (SIGFPE on idiv #DE, etc.) classification rules. ---
//
// SIGFPE == signal 8. A trap means the JIT produced NO value. The rule is:
// both-no-value is OK; trap-while-the-other-side-had-a-value is a finding.

#[test]
fn harness_flags_trap_when_oracle_has_a_value() {
    // INT_MIN / -1 case: interpreter defines a value (wrapping), x86 idiv traps.
    let row: [i64; 4] = [i64::MIN, -1, 0, 0];
    let o0 = JitOutcome::Trapped(8);
    let o2 = JitOutcome::Value(i64::MIN);

    let (category, summary) = classify_outputs(Some(Ok(i64::MIN)), &o0, &o2, &row)
        .expect("trap while oracle has a defined value must be a finding");
    assert_eq!(category, "miscompile");
    assert!(summary.contains("O0_jit=TRAP"), "summary={summary}");
    assert!(summary.contains("interp="), "summary={summary}");
}

#[test]
fn harness_excuses_trap_when_oracle_also_trapped() {
    // Genuine divide-by-zero: the interpreter rejected it (Err) AND the JIT
    // trapped. No defined value on either side -> NOT a finding.
    let row: [i64; 4] = [1, 0, 0, 0];
    let o0 = JitOutcome::Trapped(8);
    let o2 = JitOutcome::Trapped(8);

    assert!(
        classify_outputs(
            Some(Err("interp_err: division by zero".to_string())),
            &o0,
            &o2,
            &row
        )
        .is_none(),
        "both sides trapping must not be flagged as a defect"
    );
}

#[test]
fn harness_flags_cross_opt_trap_vs_value() {
    // Same program + inputs: one opt level traps, another returns a value. That
    // is a real divergence in the compiled program's behavior, even when the
    // oracle is silent.
    let row: [i64; 4] = [i64::MIN, -1, 0, 0];
    let trap_then_value =
        classify_outputs(None, &JitOutcome::Trapped(8), &JitOutcome::Value(7), &row)
            .expect("O0 trap vs O2 value must be flagged");
    assert_eq!(trap_then_value.0, "miscompile");

    let value_then_trap =
        classify_outputs(None, &JitOutcome::Value(7), &JitOutcome::Trapped(8), &row)
            .expect("O0 value vs O2 trap must be flagged");
    assert_eq!(value_then_trap.0, "miscompile");
}

#[test]
fn harness_excuses_all_three_trapping() {
    use trust_cg_fuzz::jit_diff::classify_outputs_o0_o2_o3;
    let row: [i64; 4] = [1, 0, 0, 0];
    let t = JitOutcome::Trapped(8);
    assert!(
        classify_outputs_o0_o2_o3(Some(Err("interp_err".to_string())), &t, &t, &t, &row).is_none(),
        "all opt levels trapping with no oracle value must not be a defect"
    );
}
