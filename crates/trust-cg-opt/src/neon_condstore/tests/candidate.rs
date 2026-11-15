//! Construction/refusal controls, not native execution or formal equivalence.
use super::*;

#[test]
fn lowering_refusal_preserves_live_function() {
    let mut func = candidate_fixture(0);
    let mut rec = candidate_plan(&func);
    rec.term.id = u32::MAX;
    support::assert_refusal(&mut func, |func| apply(func, &rec));
}

use crate::candidate::tests::support;
use crate::pass_manager::AnalysisCache;

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
    (rec.preheader_term, rec.header)
}
fn candidate_fixture(_path: usize) -> MachFunction {
    noalias(build_condstore_loop(false), &[0, 1])
}
fn rotations() -> &'static [bool] {
    &[false]
}
fn variants() -> Vec<(&'static str, MachFunction)> {
    vec![
        ("i32-noalias", noalias(build_condstore_loop(false), &[0, 1])),
        ("i32-in-place", build_condstore_loop(true)),
        (
            "i64-noalias",
            noalias(build_condstore_loop_i64(false), &[0, 1]),
        ),
        ("i64-in-place", build_condstore_loop_i64(true)),
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
corruption_test!(structural_early_exhaustion, 0, 0);
corruption_test!(structural_late_exhaustion, 0, 1);
corruption_test!(structural_metadata_exhaustion, 0, 2);
corruption_test!(structural_splice_refusal, 0, 3);
corruption_test!(structural_missing_setup, 0, 4);
corruption_test!(structural_missing_layout, 0, 5);

#[test]
fn success_snapshots() {
    for (label, fixture) in variants() {
        for &rotate in rotations() {
            let mut func = fixture.clone();
            let rec = candidate_plan(&func);
            assert!(apply_plan(&mut func, &rec, rotate), "{label}/{rotate}");
            println!("STORE_CANDIDATE_SNAPSHOT neon_condstore/{label}/{rotate}: {func:?}");
        }
    }
}
#[test]
fn every_register_cutoff_and_final_range() {
    for (label, fixture) in variants() {
        for &rotate in rotations() {
            let rec = candidate_plan(&fixture);
            support::every_reservation(
                &format!("neon_condstore/{label}/{rotate}"),
                &fixture,
                |func| apply_plan(func, &rec, rotate),
            );
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
fn structural_runner_refuses_without_mutation() {
    for (_, fixture) in variants() {
        for &_rotate in rotations() {
            for analyses_route in [false, true] {
                let mut pass = NeonCondStorePass::new();
                let mut positive = fixture.clone();
                let run = |pass: &mut NeonCondStorePass, func: &mut MachFunction| {
                    let _ = analyses_route;
                    pass.run_with_structural_test_authority(func)
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
            let mut pass = NeonCondStorePass::new();
            println!("REMAINDER_VARIANT neon_condstore/{label}/{rotate}");
            assert!(pass.run_with_structural_test_authority(&mut func));
            support::assert_refusal(&mut func, |func| {
                pass.run_with_structural_test_authority(func)
            });
            assert_eq!(pass.fired(), 0);
        }
    }
}

#[test]
fn public_routes_remain_inert_without_typed_authority() {
    for (_, mut func) in variants() {
        let mut pass = NeonCondStorePass::new();
        support::assert_refusal(&mut func, |func| pass.run(func));
        support::assert_refusal(&mut func, |func| {
            pass.run_with_analyses(func, &mut AnalysisCache::new())
        });
        assert_eq!(pass.fired(), 0);
    }
}
