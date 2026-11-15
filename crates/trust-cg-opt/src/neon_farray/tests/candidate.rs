//! Construction/rollback controls; not native execution or formal equivalence.
use super::*;
use crate::candidate::tests::support;

enum Plan {
    Reduction(Recognized),
    Fill(RecognizedFill),
}

fn plan(func: &MachFunction) -> Plan {
    let dom = DomTree::compute(func);
    let loops = LoopAnalysis::compute(func, &dom);
    let defs = build_def_map(func);
    loops
        .all_loops()
        .find_map(|lp| {
            Recognized::recognize(func, &dom, &defs, lp.header, lp.latch, &lp.body, true)
                .map(Plan::Reduction)
                .or_else(|| {
                    RecognizedFill::recognize(func, &dom, &defs, lp.header, lp.latch, &lp.body)
                        .map(Plan::Fill)
                })
        })
        .expect("positive fixture must be recognized")
}

fn apply_plan(func: &mut MachFunction, rec: &Plan) -> bool {
    match rec {
        Plan::Reduction(rec) => apply(func, rec),
        Plan::Fill(rec) => apply_fill(func, rec),
    }
}

fn anchors(rec: &Plan) -> (InstId, BlockId) {
    match rec {
        Plan::Reduction(rec) => (rec.preheader_term, rec.vec_guard),
        Plan::Fill(rec) => (rec.preheader_term, rec.vec_guard),
    }
}

fn fixture(path: usize) -> MachFunction {
    if path == 0 {
        build_loop(Kind::FusedDot, 1, 4, true, false)
    } else {
        build_fill(true, true, false, 100, false, false)
    }
}

fn variants() -> Vec<(&'static str, MachFunction)> {
    let mut licensed = build_loop(Kind::FusedDot, 1, 8, false, false);
    for inst in &mut licensed.insts {
        if inst.opcode == AArch64Opcode::FmaddRR {
            inst.flags.insert(InstFlags::FMULADD_MAY_UNFUSE);
        }
    }
    vec![
        ("f64-fused", build_loop(Kind::FusedDot, 1, 8, false, false)),
        ("f64-licensed", licensed),
        ("f64-sum", build_loop(Kind::PlainSum, 1, 8, false, false)),
        (
            "f64-unfused",
            build_loop(Kind::UnfusedDot, 1, 8, false, false),
        ),
        ("widen-fused", fixture(0)),
        ("widen-sum", build_loop(Kind::PlainSum, 1, 4, true, false)),
        (
            "widen-unfused",
            build_loop(Kind::UnfusedDot, 1, 4, true, false),
        ),
        ("fill-two", fixture(1)),
        ("fill-three", three_stream_fill()),
        (
            "fill-one",
            build_fill(false, false, false, 100, false, false),
        ),
        (
            "fill-signed",
            build_fill(false, true, true, 100, false, false),
        ),
    ]
}

pub(super) fn three_stream_fill() -> MachFunction {
    let mut func = build_fill(true, true, false, 12, false, false);
    let pre = *func.block(func.entry).insts.last().unwrap();
    crate::candidate::emit_before(&mut func, pre, AArch64Opcode::MovR, vec![g(55), g(85)]).unwrap();
    let step = func
        .insts
        .iter()
        .position(|inst| inst.opcode == AArch64Opcode::AddRI)
        .unwrap();
    let step = InstId(u32::try_from(step).unwrap());
    crate::candidate::emit_before(
        &mut func,
        step,
        AArch64Opcode::Madd,
        vec![g(56), g(10), g(3), g(55)],
    )
    .unwrap();
    crate::candidate::emit_before(
        &mut func,
        step,
        AArch64Opcode::StrRI,
        vec![s(7), g(56), i(0)],
    )
    .unwrap();
    func
}

fn assert_corruption(path: usize, kind: usize) {
    let mut func = fixture(path);
    let rec = plan(&func);
    let (pre, guard) = anchors(&rec);
    support::corrupt(&mut func, pre, guard, kind);
    support::assert_refusal(&mut func, |func| apply_plan(func, &rec));
}

macro_rules! corruption_test {
    ($name:ident, $path:expr, $kind:expr) => {
        #[test]
        fn $name() {
            assert_corruption($path, $kind);
        }
    };
}
corruption_test!(reduction_early_exhaustion, 0, 0);
corruption_test!(reduction_late_exhaustion, 0, 1);
corruption_test!(reduction_metadata_exhaustion, 0, 2);
corruption_test!(reduction_splice_refusal, 0, 3);
corruption_test!(reduction_missing_setup, 0, 4);
corruption_test!(reduction_missing_layout, 0, 5);
corruption_test!(fill_early_exhaustion, 1, 0);
corruption_test!(fill_late_exhaustion, 1, 1);
corruption_test!(fill_metadata_exhaustion, 1, 2);
corruption_test!(fill_splice_refusal, 1, 3);
corruption_test!(fill_missing_setup, 1, 4);
corruption_test!(fill_missing_layout, 1, 5);

#[test]
fn success_snapshots() {
    for (label, mut func) in variants() {
        let rec = plan(&func);
        assert!(apply_plan(&mut func, &rec), "{label}");
        println!("FARRAY_CANDIDATE_SNAPSHOT {label}: {func:?}");
    }
}

#[test]
fn every_register_cutoff_and_final_range() {
    for (label, fixture) in variants() {
        let rec = plan(&fixture);
        support::every_reservation(label, &fixture, |func| apply_plan(func, &rec));
    }
}

#[test]
fn sparse_detached_and_metadata_ids() {
    for (_, fixture) in variants() {
        let rec = plan(&fixture);
        support::sparse_ids(&fixture, |func| apply_plan(func, &rec));
    }
}

#[test]
fn duplicate_setup_ownership() {
    for path in 0..2 {
        let mut func = fixture(path);
        let rec = plan(&func);
        let (pre, guard) = anchors(&rec);
        func.block_mut(guard).insts.push(pre);
        support::assert_refusal(&mut func, |func| apply_plan(func, &rec));
    }
}

#[test]
fn lowering_refusal_preserves_live_function() {
    for path in 0..2 {
        let mut func = fixture(path);
        let mut rec = plan(&func);
        match &mut rec {
            Plan::Reduction(rec) => {
                rec.root = Root::PlainFadd {
                    term: VReg::new(u32::MAX, RegClass::Fpr64),
                }
            }
            Plan::Fill(rec) => rec.stores[0].1.id = u32::MAX,
        }
        support::assert_refusal(&mut func, |func| apply_plan(func, &rec));
    }
}

#[test]
fn missing_store_base_refuses_without_mutation() {
    let mut func = fixture(1);
    let Plan::Fill(mut rec) = plan(&func) else {
        panic!("fill");
    };
    rec.stores[0].0.id = u32::MAX;
    support::assert_refusal(&mut func, |func| apply_fill(func, &rec));
}

#[test]
fn public_routes_refuse_without_mutation() {
    for (_, fixture) in variants() {
        for cached in [false, true] {
            let mut pass = NeonFArrayPass::new();
            let run = |pass: &mut NeonFArrayPass, func: &mut MachFunction| {
                if cached {
                    pass.run_with_analyses(func, &mut AnalysisCache::new())
                } else {
                    pass.run(func)
                }
            };
            let mut positive = fixture.clone();
            assert!(run(&mut pass, &mut positive));
            assert_eq!(pass.fired(), 1);
            let after = format!("{positive:?}");
            assert!(!run(&mut pass, &mut positive));
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

#[test]
fn default_mode_still_selects_only_widening_and_fills() {
    for (label, mut func) in variants() {
        let expected = !label.starts_with("f64-");
        let before = format!("{func:?}");
        let mut pass = NeonFArrayPass::default();
        assert_eq!(pass.run(&mut func), expected, "{label}");
        assert_eq!(pass.fired(), usize::from(expected));
        if !expected {
            assert_eq!(format!("{func:?}"), before);
        }
    }
}

#[test]
fn incomplete_disjointness_chain_refuses() {
    let func = fixture(1);
    let Plan::Fill(rec) = plan(&func) else {
        panic!("fill");
    };
    for guards in 0..=3 {
        let mut changed = func.clone();
        support::assert_refusal(&mut changed, |candidate| {
            crate::candidate::commit(candidate, |candidate| {
                let blocks = (0..guards)
                    .map(|_| candidate.try_create_block())
                    .collect::<Option<Vec<_>>>()?;
                // Exact block count still must reject missing range endpoints.
                emit_disjointness_chain(candidate, &rec, &blocks, &rec.bases, &[], rec.exit)
            })
        });
    }
}
