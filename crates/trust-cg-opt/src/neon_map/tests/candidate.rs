//! Construction/refusal controls, not native execution or formal equivalence.
use super::*;
use trust_cg_ir::MachInst;

#[test]
fn selected_mla_fusion_uses_checked_construction() {
    let mut fixture = build_map_loop(0);
    let rec = candidate_plan(&fixture);
    let term = rec.def[&rec.term.id];
    assert_eq!(fixture.inst(term).opcode, AArch64Opcode::AddRR);
    let lhs = fixture.inst(term).operands[1].clone();
    let mul = fixture.push_inst(MachInst::new(
        AArch64Opcode::MulRR,
        vec![v(501), lhs, v(41)],
    ));
    let owner = fixture
        .blocks
        .iter_mut()
        .find(|block| block.insts.contains(&term))
        .unwrap();
    let pos = owner.insts.iter().position(|id| *id == term).unwrap();
    owner.insts.insert(pos, mul);
    fixture.inst_mut(term).operands[1] = v(501);
    let rec = candidate_plan(&fixture);
    let mut positive = fixture.clone();
    assert!(apply(&mut positive, &rec));
    assert_eq!(count(&positive, AArch64Opcode::NeonMlaV), UNROLL);
    assert_eq!(count(&positive, AArch64Opcode::NeonMulV), 0);
    support::every_reservation("integer-mla-fusion", &fixture, |func| apply(func, &rec));
}

#[test]
fn lowering_refusal_preserves_live_function() {
    let mut func = candidate_fixture(0);
    let mut rec = candidate_plan(&func);
    rec.term.id = u32::MAX;
    support::assert_refusal(&mut func, |func| apply(func, &rec));
}

use crate::candidate::tests::support;

fn noalias(mut func: MachFunction, ids: &[u32]) -> MachFunction {
    func.noalias_params = ids.to_vec();
    func
}
fn candidate_plan(func: &MachFunction) -> Recognized {
    let dom = DomTree::compute(func);
    let loops = LoopAnalysis::compute(func, &dom);
    loops
        .all_loops()
        .find_map(|lp| Recognized::recognize(func, &dom, lp.header, lp.latch, &lp.body))
        .expect("positive fixture must be recognized")
}
fn apply_plan(func: &mut MachFunction, rec: &Recognized, _rotate: bool) -> bool {
    apply(func, rec)
}
fn anchors(rec: &Recognized) -> (InstId, BlockId) {
    (rec.preheader_term, rec.guard)
}
fn candidate_fixture(_path: usize) -> MachFunction {
    build_map_loop(0)
}
fn rotations() -> &'static [bool] {
    &[false]
}
fn variants() -> Vec<(&'static str, MachFunction)> {
    vec![
        ("forward-versioned", build_map_loop(0)),
        ("forward-noalias", noalias(build_map_loop(0), &[0, 2, 10])),
        ("in-place", build_map_loop(3)),
        ("descending", build_map_loop_reverse(3)),
        (
            "rotated-descending",
            build_map_loop_rotated_reverse(0, false),
        ),
        ("i64", noalias(build_map_loop_i64(false), &[0, 2])),
        ("matmul", noalias(build_matmul_inner(0, 1), &[0, 1])),
        ("chain-versioned", build_chain_map_loop(0)),
        ("chain-in-place", build_chain_map_loop(3)),
        ("chain-clamp", build_chain_clamp_loop(0)),
    ]
}
fn assert_corruption(path: usize, kind: usize) {
    for &rotate in rotations() {
        let mut func = candidate_fixture(path);
        let rec = candidate_plan(&func);
        let (pre, guard) = anchors(&rec);
        support::corrupt(&mut func, pre, guard, kind);
        support::assert_refusal(&mut func, |func| apply_plan(func, &rec, rotate));
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
corruption_test!(map_early_exhaustion, 0, 0);
corruption_test!(map_late_exhaustion, 0, 1);
corruption_test!(map_metadata_exhaustion, 0, 2);
corruption_test!(map_splice_refusal, 0, 3);
corruption_test!(map_missing_setup, 0, 4);
corruption_test!(map_missing_layout, 0, 5);

#[test]
fn success_snapshots() {
    for (label, fixture) in variants() {
        for &rotate in rotations() {
            let mut func = fixture.clone();
            let rec = candidate_plan(&func);
            assert!(apply_plan(&mut func, &rec, rotate), "{label}/{rotate}");
            println!("STORE_CANDIDATE_SNAPSHOT neon_map/{label}/{rotate}: {func:?}");
        }
    }
}
#[test]
fn every_register_cutoff_and_final_range() {
    for (label, fixture) in variants() {
        for &rotate in rotations() {
            let rec = candidate_plan(&fixture);
            support::every_reservation(&format!("neon_map/{label}/{rotate}"), &fixture, |func| {
                apply_plan(func, &rec, rotate)
            });
        }
    }
}
#[test]
fn sparse_detached_and_metadata_ids() {
    for (_, fixture) in variants() {
        for &rotate in rotations() {
            let rec = candidate_plan(&fixture);
            support::sparse_ids(&fixture, |func| apply_plan(func, &rec, rotate));
        }
    }
}
#[test]
fn duplicate_setup_ownership() {
    for path in 0..1 {
        let mut func = candidate_fixture(path);
        let rec = candidate_plan(&func);
        let (pre, guard) = anchors(&rec);
        func.block_mut(guard).insts.push(pre);
        support::assert_refusal(&mut func, |func| apply_plan(func, &rec, true));
    }
}
#[test]
fn public_routes_refuses_without_mutation() {
    for (_, fixture) in variants() {
        for &_rotate in rotations() {
            for analyses_route in [false, true] {
                let mut pass = NeonMapPass::new();
                let mut positive = fixture.clone();
                let run = |pass: &mut NeonMapPass, func: &mut MachFunction| {
                    if analyses_route {
                        pass.run_with_analyses(func, &mut AnalysisCache::new())
                    } else {
                        pass.run(func)
                    }
                };
                assert!(run(&mut pass, &mut positive));
                assert_eq!(pass.fired(), 1);
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
fn repeated_run_preserves_remainder() {
    for (label, fixture) in variants() {
        for &rotate in rotations() {
            let mut func = fixture.clone();
            let mut pass = NeonMapPass::new();
            println!("REMAINDER_VARIANT neon_map/{label}/{rotate}");
            assert!(pass.run(&mut func));
            support::assert_refusal(&mut func, |func| pass.run(func));
            assert_eq!(pass.fired(), 0);
        }
    }
}
