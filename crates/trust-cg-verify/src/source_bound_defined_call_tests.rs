// Copyright 2026 Andrew Yates | Apache-2.0

use super::*;
use crate::smt::{EvalResult, SmtSort};

fn words(code: &[u32]) -> Vec<u8> {
    code.iter().flat_map(|w| w.to_le_bytes()).collect()
}

fn evaluated_goal(obligation: &ProofObligation, sp: u64, base: u64) -> bool {
    // Regression witnesses only. The production query retains arbitrary byte
    // memory; no constant memory substitution enters construction or replay.
    let expression = obligation
        .aarch64_expr
        .try_rewrite_dag(&mut |node| {
            Ok::<_, String>(match node {
                E::UF { name, .. } if name == "trace_entry_memory" => {
                    Some(E::const_array(SmtSort::BitVec(64), E::bv_const(0x7d, 8)))
                }
                _ => None,
            })
        })
        .unwrap()
        .unwrap_or_else(|| obligation.aarch64_expr.clone());
    let mut env = std::collections::HashMap::new();
    for (name, _) in &obligation.inputs {
        env.insert(name.clone(), 0);
    }
    env.insert("trace_entry_sp".into(), sp);
    env.insert("trace_image_base".into(), base);
    for n in 0..31 {
        env.insert(format!("trace_x{n}"), 0x9876 + n * 3);
    }
    for probe in [0, sp - 32, sp - 17, sp - 16, sp - 1, sp, sp + 1, u64::MAX] {
        env.insert("trace_memory_probe".into(), probe);
        if !matches!(expression.try_eval(&env), Ok(EvalResult::Bool(true))) {
            return false;
        }
    }
    true
}

#[test]
fn actual_bl_leaf_ret_and_epilogue_form_one_finite_trace() {
    let caller = words(&[0xa9bf7bfd, 0x910003fd, 0x94000003, 0xa8c17bfd, 0xd65f03c0]);
    let callee = words(&[0xd2800540, 0xd65f03c0]);
    let (obligation, steps) = trace_obligation(&caller, 0, &callee, 20, 28, 16, 42).unwrap();
    assert_eq!(steps, 7);
    for sp in [32, 0x1000, u64::MAX - 15] {
        assert!(evaluated_goal(&obligation, sp, 0x10000));
    }
    // The relation, link, and return must remain load-bearing conclusions.
    assert!(obligation.aarch64_expr != E::bool_const(true));
    assert_eq!(obligation.preconditions.len(), 5);
}

#[test]
fn changed_callee_result_target_return_and_frame_refute_the_aggregate() {
    let caller = [0xa9bf7bfd, 0x910003fd, 0x94000003, 0xa8c17bfd, 0xd65f03c0];
    let callee = [0xd2800540, 0xd65f03c0];
    for (which, index, changed) in [
        (0, 2, 0x94000004), // BL lands at RET instead of leaf entry.
        (0, 3, 0xa8c27bfd), // Restore SP+32 instead of16.
        (0, 4, 0xd65f0000), // Final RET X0.
        (1, 0, 0xd2800560), // Actual callee returns43.
        (1, 1, 0xd65f0000), // Callee returns to X0, not actual BL LR.
    ] {
        let mut a = caller;
        let mut b = callee;
        if which == 0 {
            a[index] = changed;
        } else {
            b[index] = changed;
        }
        let (obligation, _) = trace_obligation(&words(&a), 0, &words(&b), 20, 28, 16, 42).unwrap();
        assert!(!evaluated_goal(&obligation, 0x1000, 0x10000));
    }
    let (wrong_source, _) =
        trace_obligation(&words(&caller), 0, &words(&callee), 20, 28, 16, 43).unwrap();
    assert!(!evaluated_goal(&wrong_source, 0x1000, 0x10000));
}

#[test]
fn nested_real_leaf_frame_uses_full_extent_and_preserves_saved_bytes() {
    let caller = words(&[0xa9bf7bfd, 0x910003fd, 0x94000003, 0xa8c17bfd, 0xd65f03c0]);
    let callee = words(&[0xa9bf7bfd, 0x910003fd, 0xd2800540, 0xa8c17bfd, 0xd65f03c0]);
    let (obligation, steps) = trace_obligation(&caller, 0, &callee, 20, 40, 32, 42).unwrap();
    assert_eq!(steps, 10);
    assert!(evaluated_goal(&obligation, 0x1000, 0x10000));
    let (too_small, _) = trace_obligation(&caller, 0, &callee, 20, 40, 16, 42).unwrap();
    assert!(!evaluated_goal(&too_small, 0x1000, 0x10000));
}

#[test]
fn unsupported_control_memory_and_provider_like_calls_refuse() {
    let caller = words(&[0xa9bf7bfd, 0x910003fd, 0x94000003, 0xa8c17bfd, 0xd65f03c0]);
    for code in [
        vec![0x94000000, 0xd65f03c0], // Recursive/direct leaf call.
        vec![0xd63f0000, 0xd65f03c0], // Unknown indirect/provider call.
        vec![0xf9400000, 0xd65f03c0], // Unowned scalar memory.
        vec![0x14000000, 0xd65f03c0], // Generic/possibly infinite B.
    ] {
        assert!(trace_obligation(&caller, 0, &words(&code), 20, 28, 16, 42).is_err());
    }
}

#[test]
fn complete_conjunctive_replay_inventory_retains_every_goal_and_original_scope() {
    let caller = words(&[0xa9bf7bfd, 0x910003fd, 0x94000003, 0xa8c17bfd, 0xd65f03c0]);
    let callee = words(&[0xd2800540, 0xd65f03c0]);
    let (statement, _) = trace_obligation(&caller, 0, &callee, 20, 28, 16, 42).unwrap();
    let parts = crate::conjunctive_obligations::split_parts(&statement, &statement.name).unwrap();
    let check = |parts: &[ProofObligation]| {
        crate::conjunctive_obligations::check_parts(
            &statement,
            parts,
            &statement.name,
            &["trace_entry_memory"],
        )
    };
    check(&parts).unwrap();
    assert!(parts.len() > 1);
    assert!(parts.iter().all(|p| evaluated_goal(p, 0x1000, 0x10000)));
    let rename = |parts: &mut Vec<ProofObligation>| {
        let n = parts.len();
        for (index, p) in parts.iter_mut().enumerate() {
            p.name = format!("{} -- part {} of {}", statement.name, index + 1, n);
        }
    };
    let mut missing = parts.clone();
    missing.pop();
    rename(&mut missing);
    assert!(check(&missing).unwrap_err().contains("conjuncts"));
    let mut duplicate = parts.clone();
    duplicate.push(parts[0].clone());
    rename(&mut duplicate);
    assert!(check(&duplicate).is_err());
    let mut assumed_false = parts.clone();
    assumed_false[0].preconditions.push(E::bool_const(false));
    assert!(check(&assumed_false).unwrap_err().contains("premise"));
    let mut wrong_input = parts.clone();
    let p = wrong_input
        .iter_mut()
        .find(|p| !p.inputs.is_empty())
        .unwrap();
    p.inputs[0].1 += 1;
    assert!(check(&wrong_input).unwrap_err().contains("inputs"));
    let mut weakened = parts.clone();
    weakened[0].aarch64_expr = E::bool_const(true);
    assert!(check(&weakened).is_err());
    // A changed actual callee result is still a false complete theorem, and
    // its falsified goal must survive partitioning (not be omitted as hard).
    let wrong_leaf = words(&[0xd2800560, 0xd65f03c0]);
    let (wrong, _) = trace_obligation(&caller, 0, &wrong_leaf, 20, 28, 16, 42).unwrap();
    let wrong_parts = crate::conjunctive_obligations::split_parts(&wrong, &wrong.name).unwrap();
    crate::conjunctive_obligations::check_parts(
        &wrong,
        &wrong_parts,
        &wrong.name,
        &["trace_entry_memory"],
    )
    .unwrap();
    assert!(!evaluated_goal(&wrong, 0x1000, 0x10000));
    assert!(
        wrong_parts
            .iter()
            .any(|p| !evaluated_goal(p, 0x1000, 0x10000))
    );
}
