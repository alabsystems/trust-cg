//! Construction and publication controls, not native or formal equivalence.
use super::*;
use crate::candidate::tests::support;

fn plan(func: &MachFunction) -> Recognized {
    let dom = DomTree::compute(func);
    let loops = LoopAnalysis::compute(func, &dom);
    let defs = build_def_map(func);
    loops
        .all_loops()
        .find_map(|lp| Recognized::recognize(func, &dom, &defs, lp.header, lp.latch, &lp.body))
        .expect("positive fixture must be recognized")
}

fn apply_plan(func: &mut MachFunction, rec: &Recognized, dotprod: bool) -> bool {
    if rec.widen.is_some() {
        apply_widen(func, rec, dotprod)
    } else if rec.dot.is_some() {
        apply_dot_widen(func, rec)
    } else if rec.abs.is_some() {
        apply_abs_widen(func, rec)
    } else if rec.is_i64 {
        apply_i64(func, rec)
    } else {
        apply(func, rec, dotprod)
    }
}

fn fixture(path: usize) -> MachFunction {
    use AArch64Opcode::*;
    match path {
        0 => build_array_loop(false, ELEM_BYTES),
        1 => build_i64_array_loop(false, AddRR),
        2 => build_widening_dot_loop(Sxtw, Sxtw),
        3 => build_chain_abs_loop(0),
        4 => build_widen_loop(Uxtb, false),
        _ => unreachable!("unknown construction path"),
    }
}

fn reclassify(func: &mut MachFunction, ids: &[u32], class: RegClass) {
    for at in func.block_order.clone() {
        for id in func.block(at).insts.clone() {
            for operand in &mut func.inst_mut(id).operands {
                if let MachOperand::VReg(v) = operand
                    && ids.contains(&v.id)
                {
                    v.class = class;
                }
            }
        }
    }
}

fn mixed_bound_loop(narrow_bound: bool) -> MachFunction {
    let mut func = build_i64_rotated_loop(AArch64Opcode::AddRR);
    reclassify(&mut func, &[6, 12, 16], RegClass::Gpr32);
    if narrow_bound {
        reclassify(&mut func, &[1], RegClass::Gpr32);
    }
    let size = func
        .block(func.entry)
        .insts
        .iter()
        .copied()
        .find(|&id| func.inst(id).operands.first() == Some(&v64(40)))
        .unwrap();
    func.inst_mut(size).operands[1] = i(ELEM_BYTES);
    func
}

fn extended_bound(mut func: MachFunction, opcode: AArch64Opcode, reassign: bool) -> MachFunction {
    reclassify(&mut func, &[1], RegClass::Gpr64);
    let bound_def = func
        .block(func.entry)
        .insts
        .iter()
        .copied()
        .find(|&id| func.inst(id).operands.first() == Some(&v64(1)))
        .unwrap();
    crate::candidate::emit_before(
        &mut func,
        bound_def,
        AArch64Opcode::Movz,
        vec![v(70), i(17)],
    )
    .unwrap();
    *func.inst_mut(bound_def) = MachInst::new(opcode, vec![v64(1), v(70)]);
    if reassign {
        let term = *func.block(func.entry).insts.last().unwrap();
        crate::candidate::emit_before(&mut func, term, AArch64Opcode::Movz, vec![v(70), i(32)])
            .unwrap();
    }
    func
}

fn variants() -> Vec<(&'static str, MachFunction)> {
    use AArch64Opcode::*;
    vec![
        ("sum", fixture(0)),
        ("dot", build_array_loop(true, ELEM_BYTES)),
        ("iota", build_iv_term_loop(false)),
        ("popcount", build_popcount_loop(false)),
        ("popcount-nested", build_popcount_loop(true)),
        ("i64-sum", fixture(1)),
        ("i64-xor", build_i64_array_loop(false, EorRR)),
        ("i64-or", build_i64_array_loop(false, OrrRR)),
        ("i64-rotated-sum", build_i64_rotated_loop(AddRR)),
        ("i64-rotated-xor", build_i64_rotated_loop(EorRR)),
        ("dot-signed", fixture(2)),
        ("dot-unsigned", build_widening_dot_loop(Uxtw, Uxtw)),
        ("abs-add", fixture(3)),
        ("abs-plain", build_chain_abs_loop(1)),
        ("byte-unsigned", fixture(4)),
        ("byte-signed", build_widen_loop(Sxtb, false)),
        ("half-unsigned", build_widen_loop(Uxth, false)),
        ("half-signed", build_widen_loop(Sxth, false)),
        ("byte-popcount", build_widen_loop(Uxtb, true)),
        (
            "inline-bound-step",
            build_inlined_puzzle_loop(41249, 7, false),
        ),
        ("chain-dot", build_chain_dot_loop(0)),
        ("chain-dot-diamond", build_chain_dot_loop(1)),
        ("merged-bound", build_merged_bound_carrier_loop(2)),
        ("same-bound-carrier", build_merged_bound_carrier_loop(1)),
        (
            "mixed-bound-signed",
            extended_bound(mixed_bound_loop(false), Sxtw, false),
        ),
        (
            "mixed-bound-unsigned",
            extended_bound(mixed_bound_loop(false), Uxtw, false),
        ),
        (
            "mixed-bound-captured",
            extended_bound(mixed_bound_loop(false), Sxtw, true),
        ),
        ("mixed-bound-raw", mixed_bound_loop(false)),
        ("mixed-bound-word", mixed_bound_loop(true)),
        (
            "i64-bound-signed",
            extended_bound(build_i64_rotated_loop(AddRR), Sxtw, false),
        ),
        (
            "i64-bound-unsigned",
            extended_bound(build_i64_rotated_loop(AddRR), Uxtw, false),
        ),
        ("i32-bound-wide", extended_bound(fixture(0), Uxtw, false)),
        ("byte-bound-wide", extended_bound(fixture(4), Sxtw, false)),
        (
            "half-bound-wide",
            extended_bound(build_widen_loop(Uxth, false), Uxtw, false),
        ),
    ]
}

fn assert_corruption(path: usize, kind: usize) {
    for dotprod in [false, true] {
        let mut func = fixture(path);
        let rec = plan(&func);
        support::corrupt(&mut func, rec.preheader_term, rec.guard, kind);
        support::assert_refusal(&mut func, |func| apply_plan(func, &rec, dotprod));
    }
}

macro_rules! corruption_test {
    ($name:ident, $path:expr, $kind:expr) => {
        #[test]
        fn $name() {
            assert_corruption($path, $kind);
        }
    };
}
corruption_test!(scalar_early_exhaustion, 0, 0);
corruption_test!(scalar_late_exhaustion, 0, 1);
corruption_test!(scalar_metadata_exhaustion, 0, 2);
corruption_test!(scalar_splice_refusal, 0, 3);
corruption_test!(scalar_missing_setup, 0, 4);
corruption_test!(scalar_missing_layout, 0, 5);
corruption_test!(i64_early_exhaustion, 1, 0);
corruption_test!(i64_late_exhaustion, 1, 1);
corruption_test!(i64_metadata_exhaustion, 1, 2);
corruption_test!(i64_splice_refusal, 1, 3);
corruption_test!(i64_missing_setup, 1, 4);
corruption_test!(i64_missing_layout, 1, 5);
corruption_test!(dot_early_exhaustion, 2, 0);
corruption_test!(dot_late_exhaustion, 2, 1);
corruption_test!(dot_metadata_exhaustion, 2, 2);
corruption_test!(dot_splice_refusal, 2, 3);
corruption_test!(dot_missing_setup, 2, 4);
corruption_test!(dot_missing_layout, 2, 5);
corruption_test!(abs_early_exhaustion, 3, 0);
corruption_test!(abs_late_exhaustion, 3, 1);
corruption_test!(abs_metadata_exhaustion, 3, 2);
corruption_test!(abs_splice_refusal, 3, 3);
corruption_test!(abs_missing_setup, 3, 4);
corruption_test!(abs_missing_layout, 3, 5);
corruption_test!(widen_early_exhaustion, 4, 0);
corruption_test!(widen_late_exhaustion, 4, 1);
corruption_test!(widen_metadata_exhaustion, 4, 2);
corruption_test!(widen_splice_refusal, 4, 3);
corruption_test!(widen_missing_setup, 4, 4);
corruption_test!(widen_missing_layout, 4, 5);

#[test]
fn success_snapshots() {
    for (label, fixture) in variants() {
        for dotprod in [false, true] {
            let mut func = fixture.clone();
            let rec = plan(&func);
            assert!(apply_plan(&mut func, &rec, dotprod), "{label}");
            println!("ARRAY_CANDIDATE_SNAPSHOT {label}-{dotprod}: {func:?}");
        }
    }
}

#[test]
fn every_register_cutoff_and_final_range() {
    for (label, fixture) in variants() {
        let rec = plan(&fixture);
        for dotprod in [false, true] {
            support::every_reservation(&format!("{label}-{dotprod}"), &fixture, |func| {
                apply_plan(func, &rec, dotprod)
            });
        }
    }
}

#[test]
fn sparse_detached_and_metadata_ids() {
    for (_, fixture) in variants() {
        let rec = plan(&fixture);
        for dotprod in [false, true] {
            support::sparse_ids(&fixture, |func| apply_plan(func, &rec, dotprod));
        }
    }
}

#[test]
fn duplicate_setup_ownership() {
    for path in 0..5 {
        let mut func = fixture(path);
        let rec = plan(&func);
        func.block_mut(rec.guard).insts.push(rec.preheader_term);
        support::assert_refusal(&mut func, |func| apply_plan(func, &rec, false));
    }
}

#[test]
fn lowering_refusal_preserves_live_function() {
    for path in 0..2 {
        let mut func = fixture(path);
        let mut rec = plan(&func);
        rec.term = Term::Value(VReg::new(u32::MAX, rec.acc.class));
        support::assert_refusal(&mut func, |func| apply_plan(func, &rec, false));
    }
}

#[test]
fn public_routes_refuse_without_mutation() {
    for (label, fixture) in variants() {
        for dotprod in [false, true] {
            for cached in [false, true] {
                let mut pass = NeonArrayPass::new().with_aarch64_dotprod(dotprod);
                let run = |pass: &mut NeonArrayPass, func: &mut MachFunction| {
                    if cached {
                        pass.run_with_analyses(func, &mut AnalysisCache::new())
                    } else {
                        pass.run(func)
                    }
                };
                let mut positive = fixture.clone();
                assert!(run(&mut pass, &mut positive), "{label}");
                assert_eq!(pass.fired(), 1);
                let after = format!("{positive:?}");
                assert!(!run(&mut pass, &mut positive), "{label}: repeated rewrite");
                assert_eq!(pass.fired(), 0);
                assert_eq!(after, format!("{positive:?}"));
                for metadata in [false, true] {
                    let mut func = fixture.clone();
                    if metadata {
                        func.noalias_params.push(u32::MAX);
                    } else {
                        func.next_vreg = u32::MAX;
                    }
                    support::assert_refusal(&mut func, |func| run(&mut pass, func));
                    assert_eq!(pass.fired(), 0);
                }
            }
        }
    }
}

#[test]
fn absent_specialized_plans_refuse() {
    for path in 2..5 {
        let mut func = fixture(path);
        let mut rec = plan(&func);
        rec.dot = None;
        rec.abs = None;
        rec.widen = None;
        support::assert_refusal(&mut func, |func| match path {
            2 => apply_dot_widen(func, &rec),
            3 => apply_abs_widen(func, &rec),
            _ => apply_widen(func, &rec, true),
        });
    }
}

#[test]
fn missing_loaded_stream_refuses_without_publication() {
    for path in 0..2 {
        let mut func = fixture(path);
        let mut rec = plan(&func);
        rec.loads.values_mut().next().unwrap().id = u32::MAX;
        support::assert_refusal(&mut func, |func| apply_plan(func, &rec, false));
    }
}

#[test]
fn dotprod_requires_explicit_target_support() {
    for fixture in [
        build_popcount_loop(false),
        build_widen_loop(AArch64Opcode::Uxtb, true),
    ] {
        for dotprod in [false, true] {
            let mut func = fixture.clone();
            let mut pass = NeonArrayPass::new().with_aarch64_dotprod(dotprod);
            assert!(pass.run(&mut func));
            assert_eq!(count(&func, AArch64Opcode::NeonUdotV) > 0, dotprod);
        }
        let mut func = fixture;
        assert!(NeonArrayPass::default().run(&mut func));
        assert_eq!(count(&func, AArch64Opcode::NeonUdotV), 0);
    }
}

#[test]
fn unsupported_shapes_remain_scalar() {
    for fixture in [
        build_iv_term_loop(true),
        build_i64_array_loop(true, AArch64Opcode::AddRR),
        build_merged_bound_carrier_loop(0),
    ] {
        for dotprod in [false, true] {
            let mut func = fixture.clone();
            let mut pass = NeonArrayPass::new().with_aarch64_dotprod(dotprod);
            support::assert_refusal(&mut func, |func| pass.run(func));
            assert_eq!(pass.fired(), 0);
        }
    }
}

#[test]
fn strict_entry_rejects_different_comparison_domain() {
    for path in [0, 1, 2, 4] {
        let mut func = fixture(path);
        let rec = plan(&func);
        let branch = func.block(rec.guard).insts[1];
        assert_eq!(func.inst(branch).opcode, AArch64Opcode::BCond);
        func.inst_mut(branch).operands[0] = i(CC_LO);
        support::assert_refusal(&mut func, |func| NeonArrayPass::default().run(func));
    }
}

#[test]
fn strict_entry_rejects_different_bound() {
    for path in [0, 1, 2, 4] {
        let mut func = fixture(path);
        let rec = plan(&func);
        let compare = func.block(rec.guard).insts[0];
        assert_eq!(func.inst(compare).opcode, AArch64Opcode::CmpRR);
        func.inst_mut(compare).operands[1] = vreg(rec.acc);
        support::assert_refusal(&mut func, |func| NeonArrayPass::default().run(func));
    }
}

#[test]
fn strict_entry_rejects_bypassed_accumulator_edit() {
    for path in [0, 1, 2, 4] {
        let mut func = fixture(path);
        let rec = plan(&func);
        let compare = func.block(rec.guard).insts[0];
        crate::candidate::emit_before(
            &mut func,
            compare,
            AArch64Opcode::Movz,
            vec![vreg(rec.acc), i(7)],
        )
        .unwrap();
        support::assert_refusal(&mut func, |func| NeonArrayPass::default().run(func));
    }
}

#[test]
fn widening_bound_keeps_compared_identity_and_lane_width() {
    for wide in [false, true] {
        for opcode in [AArch64Opcode::Sxtw, AArch64Opcode::Uxtw] {
            for reassign in [false, true] {
                let func = extended_bound(
                    if wide {
                        build_i64_rotated_loop(AArch64Opcode::AddRR)
                    } else {
                        mixed_bound_loop(false)
                    },
                    opcode,
                    reassign,
                );
                let rec = plan(&func);
                assert_eq!(rec.bound, VReg::new(1, RegClass::Gpr64));
                assert_eq!(rec.bound_const, None);
                assert_eq!(rec.is_i64, wide);
            }
        }
    }
}

#[test]
fn wide_comparison_checks_actual_bound_against_lane_projection() {
    let mut func = extended_bound(mixed_bound_loop(false), AArch64Opcode::Uxtw, true);
    let rec = plan(&func);
    assert!(apply_plan(&mut func, &rec, false));
    let entry = func.block(rec.preheader).succs[0];
    let checks: Vec<_> = func
        .block(entry)
        .insts
        .iter()
        .map(|&id| func.inst(id))
        .collect();
    let compare = checks
        .windows(2)
        .find(|pair| {
            pair[0].opcode == AArch64Opcode::CmpRR
                && pair[0].operands.first() == Some(&v64(1))
                && pair[1].opcode == AArch64Opcode::BCond
                && pair[1].operands == vec![i(CC_NE), b(rec.guard)]
        })
        .expect("bound projection mismatch must take the untouched scalar entry");
    let projected = compare[0].operands[1].as_vreg().unwrap();
    let defs = build_def_map(&func);
    let projection = func.inst(defs[&projected.id]);
    assert_eq!(projection.opcode, AArch64Opcode::Sxtw);
    assert_eq!(projection.operands[1], v64(1));
}

#[test]
fn word_bound_in_wide_comparison_requires_nonnegative_projection() {
    let mut func = mixed_bound_loop(true);
    let rec = plan(&func);
    assert!(apply_plan(&mut func, &rec, false));
    let entry = func.block(rec.preheader).succs[0];
    let checks: Vec<_> = func
        .block(entry)
        .insts
        .iter()
        .map(|&id| func.inst(id))
        .collect();
    assert!(checks.windows(2).any(|pair| {
        pair[0].opcode == AArch64Opcode::CmpRI
            && pair[0].operands[1] == i(0)
            && pair[1].opcode == AArch64Opcode::BCond
            && pair[1].operands == vec![i(CC_LT), b(rec.guard)]
    }));
}
