// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Raw scalar operations inside ORIGINAL diamond arms, including an untaken
//! constant arm. The 4096 bound is per expression tree and at the outer state
//! fork, not a global bound on all retained arm dictionary terms. Node counts
//! measure logical tree expansion; SmtExpr children are Arc-shared, so their
//! sum is not a measurement of distinct allocations or resident memory.

use super::*;

#[derive(Clone, Copy)]
struct ScalarArm {
    base: u32,
    constant: InstId,
    live: [InstId; 8],
    dead: [InstId; 5],
}

fn scalar_fixture(bits: u32) -> (Function, MachFunction, Ids, [ScalarArm; 2]) {
    let (mut source, mut machine, ids) = fixture(bits, IntCC::SignedLessThan, 11, Route::Direct);
    let mut controls = Vec::new();
    for which in 0..2 {
        let base = 20 + which as u32 * 20;
        let source_arm = source.blocks.get_mut(&Block(which as u32 + 1)).unwrap();
        source_arm.instructions[3].results = vec![Value(base)];
        let additions = vec![
            lir(
                L::Iconst {
                    ty: Type::B1,
                    imm: 1,
                },
                &[],
                Some(base + 1),
            ),
            lir(L::Copy, &[base + 1], Some(base + 2)),
            lir(L::Icmp { cond: IntCC::Equal }, &[2, 3], Some(base + 3)),
            lir(L::Copy, &[base + 3], Some(base + 4)),
            // Equal integer arms keep the semantic frame domain flat, but
            // raw replay must retain this actual dynamic Eq-zero selection.
            lir(
                L::Select { cond: IntCC::Equal },
                &[base + 4, base, base],
                Some(base + 5),
            ),
            // A defined canonical true B1 selects the arithmetic arm. The
            // unequal fallback makes a wrong constant/copy route refutable.
            lir(
                L::Select {
                    cond: IntCC::NotEqual,
                },
                &[base + 2, base + 5, 2],
                Some(12),
            ),
            lir(
                L::Iconst {
                    ty: Type::B1,
                    imm: 0,
                },
                &[],
                Some(base + 6),
            ),
            lir(L::Copy, &[base + 6], Some(base + 7)),
            lir(
                L::Icmp {
                    cond: IntCC::SignedLessThan,
                },
                &[0, 1],
                Some(base + 8),
            ),
            lir(L::Copy, &[base + 8], Some(base + 9)),
        ];
        source_arm.instructions.splice(4..4, additions);
        for n in 0..10 {
            source.value_types.insert(
                Value(base + n),
                if matches!(n, 0 | 5) {
                    ty(bits)
                } else {
                    Type::B1
                },
            );
        }
        let constant = push(&mut machine, M::Movz, vec![r(16, 32), O::Imm(1)]);
        let bool_copy = push(&mut machine, M::MOVWrr, vec![r(17, 32), r(16, 32)]);
        let compare = push(&mut machine, M::CmpRR, vec![r(11, bits), r(12, bits)]);
        let cset = push(&mut machine, M::CSet, vec![r(14, 32), O::Imm(0)]);
        let compare_copy = push(&mut machine, M::MOVWrr, vec![r(15, 32), r(14, 32)]);
        let eq_test = push(&mut machine, M::CmpRI, vec![r(15, 32), O::Imm(0)]);
        let eq_select = push(
            &mut machine,
            M::Csel,
            vec![r(13, bits), r(13, bits), r(13, bits), O::Imm(0)],
        );
        let ne_test = push(&mut machine, M::CmpRI, vec![r(17, 32), O::Imm(0)]);
        let ne_select = push(
            &mut machine,
            M::Csel,
            vec![r(13, bits), r(13, bits), r(11, bits), O::Imm(1)],
        );
        let dead_constant = push(&mut machine, M::Movz, vec![r(16, 32), O::Imm(0)]);
        let dead_const_copy = push(&mut machine, M::MOVWrr, vec![r(17, 32), r(16, 32)]);
        let dead_compare = push(&mut machine, M::CmpRR, vec![r(9, bits), r(10, bits)]);
        let dead_cset = push(&mut machine, M::CSet, vec![r(14, 32), O::Imm(11)]);
        let dead_compare_copy = push(&mut machine, M::MOVWrr, vec![r(15, 32), r(14, 32)]);
        let live = [
            bool_copy,
            compare,
            cset,
            compare_copy,
            eq_test,
            eq_select,
            ne_test,
            ne_select,
        ];
        let dead = [
            dead_constant,
            dead_const_copy,
            dead_compare,
            dead_cset,
            dead_compare_copy,
        ];
        let mut additions = vec![constant];
        additions.extend(live);
        additions.extend(dead);
        // All new instructions execute after the original arithmetic result,
        // but before the arm's own merge jump and common return route.
        machine.blocks[which + 1].insts.splice(3..3, additions);
        controls.push(ScalarArm {
            base,
            constant,
            live,
            dead,
        });
    }
    (
        source,
        machine,
        ids,
        controls
            .try_into()
            .unwrap_or_else(|_| panic!("two scalar arms")),
    )
}

fn initial_values(bits: u32) -> HashMap<Value, SourceValue> {
    (0..4)
        .map(|n| {
            let input = Term::leaf(E::var(format!("abi_x{n}"), 64));
            (
                Value(n),
                SourceValue {
                    term: if bits == 32 {
                        input.unary(1, |e| e.extract(31, 0)).unwrap()
                    } else {
                        input
                    },
                    boolean: false,
                },
            )
        })
        .collect()
}

fn run_source_arm(source: &Function, bits: u32, arm: usize) -> Option<HashMap<Value, SourceValue>> {
    let mut values = initial_values(bits);
    let entry = &source.blocks[&Block(0)].instructions;
    if super::super::source_run(
        &entry[..entry.len() - 1],
        &ty(bits),
        bits,
        false,
        &mut values,
    )?
    .is_some()
    {
        return None;
    }
    let instructions = &source.blocks[&Block(arm as u32)].instructions;
    if super::super::source_run(
        &instructions[..instructions.len() - 1],
        &ty(bits),
        bits,
        false,
        &mut values,
    )?
    .is_some()
    {
        return None;
    }
    Some(values)
}

fn constant_condition(
    source: &mut Function,
    machine: &mut MachFunction,
    ids: Ids,
    taken: bool,
    bits: u32,
) {
    source.blocks.get_mut(&Block(0)).unwrap().instructions[0].opcode = L::Iconst {
        ty: Type::B1,
        imm: i64::from(taken),
    };
    source.blocks.get_mut(&Block(0)).unwrap().instructions[0]
        .args
        .clear();
    machine.insts[ids.cmp.0 as usize].operands = vec![r(9, bits), r(9, bits)];
    machine.insts[ids.branch.0 as usize].operands[0] = O::Imm(if taken { 0 } else { 1 });
}

#[test]
fn original_scalar_arm_bool_copy_compare_and_eq_ne_selects_stay_raw_and_only_live_rows_are_credited()
 {
    for bits in [32, 64] {
        let (source, machine, ids, arms) = scalar_fixture(bits);
        let frame = source_bound_frame(&source, &machine).expect("original scalar-arm frame");
        let body =
            SourceBoundBody::bind(&frame).expect("independent original scalar-arm raw owner");
        assert_eq!(body.category(), ProofCategory::Arithmetic);
        assert!(body.obligation().preconditions.is_empty());
        assert_eq!(body.obligation().inputs.len(), 4);
        assert!(!body.obligation().is_degenerate());
        for arm in arms {
            for id in arm.live {
                assert!(body.credits(id), "actual live scalar row {id:?}");
            }
            for id in arm.dead.into_iter().chain([arm.constant]) {
                assert!(
                    !body.credits(id),
                    "dead row/uncertified constant cannot acquire live credit"
                );
            }
            let values = run_source_arm(&source, bits, (arm.base / 20) as usize).unwrap();
            for offset in [1, 2, 3, 4, 6, 7, 8, 9] {
                assert!(values[&Value(arm.base + offset)].boolean);
            }
            assert!(!values[&Value(12)].boolean);
        }
        for id in [ids.dead, ids.stale, ids.restore, ids.ret] {
            assert!(!body.credits(id));
        }
        for a in INPUTS {
            for b in INPUTS {
                for (c, d) in ARMS {
                    let want = EvalResult::Bv(arm_value(
                        bits,
                        predicate(IntCC::SignedLessThan, bits, a, b),
                        c,
                        d,
                    ));
                    assert_eq!(
                        evaluate(body.obligation(), [a, b, c, d]),
                        (want.clone(), want)
                    );
                }
            }
        }
        let query = crate::serialize_to_smt2(body.obligation());
        assert!(query.contains("ite") && query.contains("zero_extend 1"));
        // Inverting the inner compare changes the ORIGINAL raw source query,
        // even though its equal selected integer arms remain semantically equal.
        for which in 0..2 {
            let mut changed = source.clone();
            changed
                .blocks
                .get_mut(&Block(which + 1))
                .unwrap()
                .instructions[6]
                .opcode = L::Icmp {
                cond: IntCC::NotEqual,
            };
            let (changed, _) = raw_control_body(
                &changed,
                &machine,
                frame.raw_control().unwrap(),
                frame.envelope_instructions(),
            )
            .unwrap();
            assert_ne!(
                crate::serialize_to_smt2(&changed),
                query,
                "original inner compare cannot be taken from normalized terms"
            );
            assert_eq!(changed.aarch64_expr, body.obligation().aarch64_expr);
            assert_eq!(
                evaluate(&changed, [7, 23, 111, 222]).0,
                evaluate(body.obligation(), [7, 23, 111, 222]).0
            );
        }
    }
}

#[test]
fn each_original_scalar_arm_is_visited_and_supported_boolean_route_mutations_are_refuted() {
    for bits in [32, 64] {
        let (source, machine, ids, arms) = scalar_fixture(bits);
        let original_frame = source_bound_frame(&source, &machine).unwrap();
        for (which, arm) in arms.into_iter().enumerate() {
            let input = if which == 0 {
                [7, 23, 111, 222]
            } else {
                [23, 7, 111, 222]
            };
            let mut wrong = machine.clone();
            wrong.insts[arm.constant.0 as usize].operands[1] = O::Imm(0);
            refuted(
                &source,
                &machine,
                &wrong,
                input,
                "arm canonical Bool constant route",
            );
            let mut wrong = machine.clone();
            wrong.insts[arm.live[7].0 as usize].operands[3] = O::Imm(0);
            refuted(&source, &machine, &wrong, input, "arm CSEL Eq/Ne polarity");
            let mut changed_source = source.clone();
            changed_source
                .blocks
                .get_mut(&Block(which as u32 + 1))
                .unwrap()
                .instructions[4]
                .opcode = L::Iconst {
                ty: Type::B1,
                imm: 0,
            };
            let (changed, _) = raw_control_body(
                &changed_source,
                &machine,
                original_frame.raw_control().unwrap(),
                original_frame.envelope_instructions(),
            )
            .unwrap();
            assert_ne!(evaluate(&changed, input).0, evaluate(&changed, input).1);
            assert_eq!(
                changed.aarch64_expr,
                SourceBoundBody::bind(&original_frame)
                    .unwrap()
                    .obligation()
                    .aarch64_expr
            );
        }
        // The original outer branch can be constant, but raw source and target
        // interpretation must still reject malformed/unsupported untaken rows.
        for taken in [false, true] {
            let (mut source, mut machine, _, arms) = scalar_fixture(bits);
            constant_condition(&mut source, &mut machine, ids, taken, bits);
            let frame = source_bound_frame(&source, &machine).unwrap();
            assert!(SourceBoundBody::bind(&frame).is_some());
            let untaken = if taken { 2 } else { 1 };
            let arm = arms[untaken - 1];
            for mutation in 0..6 {
                let mut wrong = source.clone();
                let instructions = &mut wrong
                    .blocks
                    .get_mut(&Block(untaken as u32))
                    .unwrap()
                    .instructions;
                match mutation {
                    0 => {
                        instructions[10].opcode = L::Iconst {
                            ty: Type::B1,
                            imm: 2,
                        }
                    }
                    1 => instructions[11].results = vec![Value(arm.base)],
                    2 => instructions[12].args[0] = Value(arm.base + 1),
                    3 => instructions[13].args = vec![Value(99_999)],
                    4 => {
                        instructions[11].opcode = L::GuardDivZero { obligation: None };
                        instructions[11].args = vec![Value(2)];
                        instructions[11].results.clear();
                    }
                    _ => {
                        instructions[13].opcode = L::Select {
                            cond: IntCC::NotEqual,
                        };
                        instructions[13].args = vec![Value(0), Value(arm.base), Value(arm.base)];
                    }
                }
                assert!(
                    run_source_arm(&wrong, bits, untaken).is_none(),
                    "raw untaken arm rejects malformed/guard row {mutation}"
                );
                assert!(
                    raw_control_body(
                        &wrong,
                        &machine,
                        frame.raw_control().unwrap(),
                        frame.envelope_instructions()
                    )
                    .is_none()
                );
            }
            let mut wrong = machine.clone();
            wrong.insts[arm.dead[2].0 as usize] =
                MachInst::new(M::AddsRR, vec![r(14, bits), r(11, bits), r(12, bits)]);
            assert!(
                raw_control_body(
                    &source,
                    &wrong,
                    frame.raw_control().unwrap(),
                    frame.envelope_instructions()
                )
                .is_none(),
                "unsupported flag writer inside untaken arm cannot reuse earlier flags"
            );
        }
    }
}

fn duplicate_return_selects(source: &mut Function, arm: usize, steps: usize) {
    let base = 20 + (arm as u32 - 1) * 20;
    let instructions = &mut source
        .blocks
        .get_mut(&Block(arm as u32))
        .unwrap()
        .instructions;
    let returned_at = instructions
        .iter()
        .position(|i| i.results == [Value(12)])
        .unwrap();
    let mut input = 1_000 + arm as u32 * 100;
    instructions[returned_at].results = vec![Value(input)];
    source
        .value_types
        .insert(Value(input), source.signature.returns[0].clone());
    let mut added = Vec::new();
    for step in 0..steps {
        let output = if step + 1 == steps { 12 } else { input + 1 };
        added.push(lir(
            L::Select { cond: IntCC::Equal },
            &[base + 1, input, input],
            Some(output),
        ));
        source
            .value_types
            .insert(Value(output), source.signature.returns[0].clone());
        input = output;
    }
    instructions.splice(returned_at + 1..returned_at + 1, added);
}

#[test]
fn scalar_arm_return_trees_are_bounded_before_conditional_expression_clones_even_when_untaken() {
    for bits in [32, 64] {
        for taken in [false, true] {
            let (mut source, mut machine, ids, _) = scalar_fixture(bits);
            constant_condition(&mut source, &mut machine, ids, taken, bits);
            for arm in [1, 2] {
                duplicate_return_selects(&mut source, arm, 6);
            }
            let frame = source_bound_frame(&source, &machine)
                .expect("equivalent duplicate-arm selections remain in the flat semantic domain");
            let left = run_source_arm(&source, bits, 1).unwrap();
            let right = run_source_arm(&source, bits, 2).unwrap();
            assert!(
                left.values()
                    .chain(right.values())
                    .all(|v| v.term.nodes <= MAX_NODES)
            );
            assert!(left[&Value(12)].term.nodes + right[&Value(12)].term.nodes > MAX_NODES);
            assert!(
                SourceBoundBody::bind(&frame).is_none(),
                "aggregate OUTER return tree must decline before building/cloning its ite, not a global dictionary limit"
            );

            let (mut source, mut machine, ids, _) = scalar_fixture(bits);
            constant_condition(&mut source, &mut machine, ids, taken, bits);
            let untaken = if taken { 2 } else { 1 };
            duplicate_return_selects(&mut source, untaken, 7);
            let frame = source_bound_frame(&source, &machine)
                .expect("individual source tree cap is independent of the affine frame gate");
            assert!(
                run_source_arm(&source, bits, untaken).is_none(),
                "individual untaken arm selection tree exceeds 4096"
            );
            assert!(SourceBoundBody::bind(&frame).is_none());
        }
    }
}

fn machine_arm_results(frame: &SourceBoundFrame<'_>, bits: u32) -> Vec<Option<Word>> {
    let RawControl::Diamond { prefix, paths, .. } = frame.raw_control().unwrap() else {
        panic!("original diamond")
    };
    let mut prefix_registers = registers();
    let mut prefix_flags = None;
    let mut credited = HashSet::new();
    assert!(
        !super::super::machine_run(
            frame.machine(),
            &prefix,
            frame.envelope_instructions(),
            &mut prefix_registers,
            &mut prefix_flags,
            &mut credited
        )
        .unwrap()
    );
    paths
        .into_iter()
        .map(|path| {
            let mut registers = prefix_registers.clone();
            let mut flags = prefix_flags.clone();
            super::super::machine_run(
                frame.machine(),
                &path,
                frame.envelope_instructions(),
                &mut registers,
                &mut flags,
                &mut credited,
            )?;
            registers.read(&r(0, bits), bits, false)
        })
        .collect()
}

fn duplicate_machine_selects(machine: &mut MachFunction, bits: u32, arm: usize, steps: usize) {
    let mut added = Vec::new();
    for _ in 0..steps {
        added.push(push(
            machine,
            M::Csel,
            vec![r(13, bits), r(13, bits), r(13, bits), O::Imm(1)],
        ));
    }
    let at = machine.blocks[arm].insts.len() - 1;
    machine.blocks[arm].insts.splice(at..at, added);
}

#[test]
fn scalar_machine_arm_select_trees_preflight_reads_before_cloning_large_register_terms() {
    for bits in [32, 64] {
        let steps = if bits == 32 { 1 } else { 2 };
        for taken in [false, true] {
            let (mut source, mut machine, ids, _) = scalar_fixture(bits);
            constant_condition(&mut source, &mut machine, ids, taken, bits);
            for arm in [1, 2] {
                duplicate_machine_selects(&mut machine, bits, arm, steps);
            }
            let frame = source_bound_frame(&source, &machine)
                .expect("duplicate machine selections preserve arm return semantics");
            let results = machine_arm_results(&frame, bits);
            assert!(
                results
                    .iter()
                    .all(|w| w.as_ref().is_some_and(|w| w.term.nodes <= MAX_NODES))
            );
            assert!(
                results
                    .iter()
                    .flatten()
                    .map(|w| w.term.nodes)
                    .sum::<usize>()
                    > MAX_NODES
            );
            assert!(
                SourceBoundBody::bind(&frame).is_none(),
                "aggregate outer machine result term exceeds its per-tree cap"
            );

            let (mut source, mut machine, ids, _) = scalar_fixture(bits);
            constant_condition(&mut source, &mut machine, ids, taken, bits);
            let untaken = if taken { 2 } else { 1 };
            duplicate_machine_selects(&mut machine, bits, untaken, steps + 1);
            let frame = source_bound_frame(&source, &machine).unwrap();
            assert!(
                machine_arm_results(&frame, bits)
                    .iter()
                    .any(Option::is_none),
                "untaken CSEL must reject before large register/flag expression clones"
            );
            assert!(SourceBoundBody::bind(&frame).is_none());
        }
    }
}

#[test]
fn admitted_dead_scalar_arm_dictionaries_can_exceed_4096_without_claiming_a_global_memory_cap() {
    for bits in [32, 64] {
        let (mut source, mut machine, ids, _) = scalar_fixture(bits);
        constant_condition(&mut source, &mut machine, ids, true, bits);
        // Dead, constant-untaken source arm: two independent eight-step chains
        // each obey the per-tree limit, while their summed logical expansion
        // does not. Shared AST children mean this is not an allocation census.
        let mut added = Vec::new();
        for chain in 0..2 {
            let mut input = 2 + chain;
            for step in 0..8 {
                let output = 2_000 + chain * 100 + step;
                added.push(lir(L::Iadd, &[input, input], Some(output)));
                source.value_types.insert(Value(output), ty(bits));
                input = output;
            }
        }
        let arm = source.blocks.get_mut(&Block(2)).unwrap();
        let at = arm.instructions.len() - 1;
        arm.instructions.splice(at..at, added);
        let values = run_source_arm(&source, bits, 2).unwrap();
        assert!(values.values().all(|v| v.term.nodes <= MAX_NODES));
        let dictionary_nodes = values.values().map(|v| v.term.nodes).sum::<usize>();
        assert!(dictionary_nodes > MAX_NODES);
        let frame = source_bound_frame(&source, &machine)
            .expect("dead same-width affine terms remain semantically admitted");
        assert!(
            SourceBoundBody::bind(&frame).is_some(),
            "there is NO arm dictionary-wide 4096 cap; this is memory-audit debt, not new proof credit"
        );
        println!(
            "A64_SCALAR_ARM_MEMORY_AUDIT bits={bits} arm=constant-untaken source_dictionary_logical_nodes={dictionary_nodes} per_tree_limit={MAX_NODES} global_dictionary_cap=none physical_memory_measurement=none"
        );
    }
}

#[test]
fn scalar_arm_source_structural_budgets_decline_before_definition_collection_or_view_clones() {
    for bits in [32, 64] {
        let (source, machine, _, _) = scalar_fixture(bits);
        let frame = source_bound_frame(&source, &machine).expect("bounded scalar-arm baseline");
        assert!(SourceBoundBody::bind(&frame).is_some());
        assert!(crate::source_bound_frame::raw_source_view(&source).is_some());
        for mutation in 0..5 {
            let mut wrong = source.clone();
            match mutation {
                0 => wrong.signature.params.resize(9, ty(bits)),
                1 => {
                    wrong.blocks.get_mut(&Block(2)).unwrap().params = vec![(Value(0), ty(bits)); 9]
                }
                2 => wrong.blocks.get_mut(&Block(0)).unwrap().instructions[0]
                    .results
                    .push(Value(99_999)),
                3 => {
                    wrong.blocks.get_mut(&Block(2)).unwrap().instructions[6].args =
                        vec![Value(2); 4]
                }
                _ => {
                    let nodes = wrong
                        .blocks
                        .values()
                        .map(|block| block.instructions.len())
                        .sum::<usize>();
                    for n in 0..nodes + wrong.signature.params.len() + 1 {
                        wrong.value_types.insert(Value(80_000 + n as u32), ty(bits));
                    }
                    assert!(wrong.value_types.len() > nodes + wrong.signature.params.len());
                }
            }
            assert!(
                crate::source_bound_frame::raw_source_view(&wrong).is_none(),
                "structural profile {mutation} must refuse before normalization allocation"
            );
            assert!(
                raw_control_body(
                    &wrong,
                    &machine,
                    frame.raw_control().unwrap(),
                    frame.envelope_instructions()
                )
                .is_none()
            );
        }
    }
}

#[test]
fn scalar_arm_explained_replay_retains_captured_solver_disabled_refusal() {
    use crate::function_request::FunctionDischargeContext;
    use crate::provenance_xcheck::ProvenanceXCheckMode;
    use crate::{FunctionVerifier, VerificationConfig};
    crate::env_lock::with_env_overrides(
        &[
            ("TCG_REFINE_SOLVER", "0"),
            ("TCG_NO_PROOF_CACHE", "1"),
            ("TCG_BLOCKING_IDENTITY", "1"),
        ],
        || {
            let verifier = FunctionVerifier::with_config(VerificationConfig::for_proof_promotion());
            let request = verifier.capture_request_with_mode(ProvenanceXCheckMode::Enforce);
            for bits in [32, 64] {
                let (source, machine, _, _) = scalar_fixture(bits);
                let frame =
                    source_bound_frame(&source, &machine).expect("original scalar-arm frame");
                let body = SourceBoundBody::bind(&frame).expect("original scalar-arm raw owner");
                let raw_query = crate::serialize_to_smt2(body.obligation());
                let scope = FunctionDischargeContext::new(&request);
                crate::env_lock::with_env_overrides(&[("TCG_REFINE_SOLVER", "1")], || {
                    let (result, why) = scope.a64_body_explained(&body);
                    assert!(result.is_none(), "a captured refusal cannot mint Valid");
                    assert_eq!(
                        why.as_deref(),
                        Some("replay refused: TCG_REFINE_SOLVER=0"),
                        "captured policy, not the ambient solver enablement, governs replay"
                    );
                    assert!(scope.replays_bound());
                    assert!(
                        scope.a64_body(&body).is_none(),
                        "legacy verdict is unchanged"
                    );
                    assert_eq!(crate::serialize_to_smt2(body.obligation()), raw_query);
                });
            }
        },
    );
}

#[test]
fn scalar_arm_exact_raw_proofs_are_inspected_before_cleanup_at_both_widths() {
    use crate::function_request::FunctionDischargeContext;
    use crate::provenance_xcheck::ProvenanceXCheckMode;
    use crate::{FunctionVerifier, VerificationConfig};

    crate::env_lock::with_env_overrides(
        &[
            ("TCG_REFINE_SOLVER", "1"),
            ("TCG_NO_PROOF_CACHE", "1"),
            ("TCG_BLOCKING_IDENTITY", "1"),
        ],
        || {
            let verifier = FunctionVerifier::with_config(VerificationConfig::for_proof_promotion());
            let request = verifier.capture_request_with_mode(ProvenanceXCheckMode::Enforce);
            assert!(!request.recording_active(), "diagnostic is not a recorder");
            for bits in [32, 64] {
                let (source, machine, _, _) = scalar_fixture(bits);
                let frame = source_bound_frame(&source, &machine).unwrap();
                let body = SourceBoundBody::bind(&frame).unwrap();
                let scope = FunctionDischargeContext::new(&request);
                let diagnostic = request.with_policy(|| {
                    let config = crate::verdict_db::live_source_bound_config();
                    let diagnostic = request
                        .ay()
                        .inspect_fresh_source_bound(&body, &config)
                        .expect("exact captured raw proof diagnostic must run, not skip");
                    assert_eq!(
                        diagnostic.smt2,
                        crate::ay_bridge::generate_smt2_query_raw(body.obligation(), &config)
                    );
                    assert_eq!(diagnostic.timeout_ms, config.timeout_ms);
                    diagnostic
                });
                println!(
                    "A64_SCALAR_ARM_RAW_PROOF_DIAGNOSTIC bits={bits} json={}",
                    serde_json::to_string(&diagnostic).unwrap()
                );
                assert_eq!(
                    diagnostic.solver_sha256,
                    request
                        .ay_solver()
                        .expect("captured admitted solver")
                        .sha256()
                );
                assert!(diagnostic.proof_error.is_none());
                assert!(diagnostic.proof.as_ref().is_some_and(|p| !p.is_empty()));
                assert!(diagnostic.checker_error.is_none());
                assert!(diagnostic.checker_accepted.is_some());
                assert!(scope.replays_bound(), "inspection minted no replay receipt");
                if diagnostic.candidate_debug != "SolverUnsat" {
                    assert!(
                        diagnostic.candidate_debug.starts_with("Unknown("),
                        "expected certificate candidate/refusal, not a different verdict"
                    );
                    assert_eq!(
                        diagnostic.checker_accepted,
                        Some(false),
                        "incomplete raw proof must not be independently accepted"
                    );
                }
            }
        },
    );
}

#[test]
fn scalar_arm_raw_obligations_require_independent_positive_ay_clean_replay_without_skips() {
    use crate::function_request::FunctionDischargeContext;
    use crate::provenance_xcheck::ProvenanceXCheckMode;
    use crate::verify::VerificationResult;
    use crate::{FunctionVerifier, VerificationConfig};
    crate::env_lock::with_env_overrides(
        &[
            ("TCG_REFINE_SOLVER", "1"),
            ("TCG_NO_PROOF_CACHE", "1"),
            ("TCG_BLOCKING_IDENTITY", "1"),
        ],
        || {
            let verifier = FunctionVerifier::with_config(VerificationConfig::for_proof_promotion());
            let request = verifier.capture_request_with_mode(ProvenanceXCheckMode::Enforce);
            let mut failures = Vec::new();
            for bits in [32, 64] {
                let (source, machine, _, _) = scalar_fixture(bits);
                let frame =
                    source_bound_frame(&source, &machine).expect("original scalar-arm frame");
                let body = SourceBoundBody::bind(&frame).expect("original scalar-arm raw owner");
                println!(
                    "A64_SCALAR_ARM_REPLAY_QUERY bits={bits} smt2={}",
                    serde_json::to_string(&crate::serialize_to_smt2(body.obligation())).unwrap()
                );
                let (result, why) =
                    FunctionDischargeContext::new(&request).a64_body_explained(&body);
                println!("A64_SCALAR_ARM_REPLAY_RESULT bits={bits} result={result:?} why={why:?}");
                if !matches!(result, Some(VerificationResult::Valid)) {
                    failures.push(format!("i{bits}: {result:?}; why={why:?}"));
                }
            }
            assert!(
                failures.is_empty(),
                "required independent AY/Clean scalar-arm replay failed: {}; no unavailable-proof skip and concrete agreement is not proof evidence",
                failures.join("; ")
            );
        },
    );
}
