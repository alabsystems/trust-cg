//! Construction/refusal controls, not native execution or formal equivalence.
use super::*;

#[test]
fn lowering_refusal_preserves_live_function() {
    let mut func = candidate_fixture(0);
    let Plan::Map(mut rec) = candidate_plan(&func) else {
        panic!("expected map");
    };
    rec.term.id = u32::MAX;
    support::assert_refusal(&mut func, |func| apply_map(func, &rec, true));
}

use crate::candidate::tests::support;
enum Plan {
    Map(RecognizedFMap),
    Count(RecognizedFCount),
}
fn noalias(mut func: MachFunction, ids: &[u32]) -> MachFunction {
    func.noalias_params = ids.to_vec();
    func
}
fn candidate_plan(func: &MachFunction) -> Plan {
    let dom = DomTree::compute(func);
    let loops = LoopAnalysis::compute(func, &dom);
    loops
        .all_loops()
        .find_map(|lp| {
            RecognizedFMap::recognize(func, &dom, lp.header, lp.latch, &lp.body)
                .map(Plan::Map)
                .or_else(|| {
                    RecognizedFCount::recognize(func, &dom, lp.header, lp.latch, &lp.body)
                        .map(Plan::Count)
                })
        })
        .expect("positive fixture must be recognized")
}
fn apply_plan(func: &mut MachFunction, rec: &Plan, rotate: bool) -> bool {
    match rec {
        Plan::Map(rec) => apply_map(func, rec, rotate),
        Plan::Count(rec) => apply_count(func, rec),
    }
}
fn anchors(rec: &Plan) -> (InstId, BlockId) {
    match rec {
        Plan::Map(rec) => (rec.preheader_term, rec.guard),
        Plan::Count(rec) => (rec.preheader_term, rec.guard),
    }
}
fn candidate_fixture(path: usize) -> MachFunction {
    if path == 0 {
        noalias(build_fmap_loop(0, false), &[0, 2])
    } else {
        build_fcount_loop(CC_GT, false)
    }
}
fn rotations() -> &'static [bool] {
    &[true, false]
}
fn variants() -> Vec<(&'static str, MachFunction)> {
    vec![
        ("f32", noalias(build_fmap_loop(0, false), &[0, 2])),
        ("f64", noalias(build_fmap_loop(0, true), &[0, 2])),
        ("saxpy", noalias(build_fmap_loop(1, false), &[0, 2])),
        ("stencil", noalias(build_fmap_loop(2, false), &[0, 2])),
        ("in-place", build_fmap_loop(3, false)),
        ("rotated-versioned", build_rotated_fmap(0)),
        ("rotated-i64-bound", build_rotated_fmap_i64bound(0)),
        ("f32-count", build_fcount_loop(CC_GT, false)),
        ("f64-count", build_fcount_loop(CC_GT, true)),
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
corruption_test!(count_early_exhaustion, 1, 0);
corruption_test!(count_late_exhaustion, 1, 1);
corruption_test!(count_metadata_exhaustion, 1, 2);
corruption_test!(count_splice_refusal, 1, 3);
corruption_test!(count_missing_setup, 1, 4);
corruption_test!(count_missing_layout, 1, 5);

#[test]
fn success_snapshots() {
    for (label, fixture) in variants() {
        for &rotate in rotations() {
            let mut func = fixture.clone();
            let rec = candidate_plan(&func);
            assert!(apply_plan(&mut func, &rec, rotate), "{label}/{rotate}");
            println!("STORE_CANDIDATE_SNAPSHOT neon_fmap/{label}/{rotate}: {func:?}");
        }
    }
}
#[test]
fn every_register_cutoff_and_final_range() {
    for (label, fixture) in variants() {
        for &rotate in rotations() {
            let rec = candidate_plan(&fixture);
            support::every_reservation(&format!("neon_fmap/{label}/{rotate}"), &fixture, |func| {
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
    for path in 0..2 {
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
        for &rotate in rotations() {
            for analyses_route in [false, true] {
                let mut pass = NeonFMapPass::with_rotate(rotate);
                let mut positive = fixture.clone();
                let run = |pass: &mut NeonFMapPass, func: &mut MachFunction| {
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
            let mut pass = NeonFMapPass::with_rotate(rotate);
            println!("REMAINDER_VARIANT neon_fmap/{label}/{rotate}");
            assert!(pass.run(&mut func));
            support::assert_refusal(&mut func, |func| pass.run(func));
            assert_eq!(pass.fired(), 0);
        }
    }
}
