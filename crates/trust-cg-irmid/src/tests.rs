// trust-cg-irmid/tests.rs - pass manager, passes and transport
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use trust_cg_verify::trust_ir_mid_tv::{CopyForward, CopyPropWitness, PassWitness};
use trust_ir::proof::{ObligationKind, ProofObligation, ProofStatus};
use trust_ir::{CastOp, FuncId, Function, Inst, Module, Ty, ValueId};

use crate::cfg::TrustIrCfg;
use crate::manager;
use crate::passes::{self, MidPass, PassContext};
use crate::{MidConfig, MidProfile, optimize_module};

const HEADER: &str = "; TrustIr text format v1\nmodule \"irmid\"\n\
                      target \"wasm32-unknown-unknown\" 4 little\n\n";

fn module(body: &str) -> Module {
    trust_ir::parser::parse_module(&format!("{HEADER}{body}"))
        .unwrap_or_else(|e| panic!("test module failed to parse: {e}\n{body}"))
}

fn func<'m>(module: &'m Module, name: &str) -> &'m Function {
    module
        .functions
        .iter()
        .find(|f| f.name == name)
        .expect("function")
}

fn insts(func: &Function) -> Vec<&Inst> {
    func.blocks
        .iter()
        .flat_map(|b| &b.body)
        .map(|n| &n.inst)
        .collect()
}

fn run_pass(pass: &dyn MidPass, module: &Module, name: &str) -> Option<(Function, PassWitness)> {
    let cx = PassContext {
        module,
        pointer_bits: 32,
    };
    pass.run(&cx, func(module, name))
}

/// The bridge's frame-slot shape: a field of a memory-backed local addressed
/// through `ptrtoint`/`add`/`inttoptr`, with copies between, a constant
/// branch and a dead multiply.
const FRAME: &str = "type ty.0 = i32\n\nfuncty.0 = (i32, u32) -> (i32)\n\n\
    fn @frame(functy.0) {\n\
    bb0(%0: i32, %1: u32):\n\
    \x20   %2 = alloca [ty.0 x 2], align 4\n\
    \x20   %3 = copy ptr %2\n\
    \x20   %4 = ptrtoint ptr %3 to i32\n\
    \x20   %5 = const i32 4\n\
    \x20   %6 = copy i32 %5\n\
    \x20   %7 = add i32 %4, %6\n\
    \x20   %8 = inttoptr i32 %7 to ptr\n\
    \x20   store i32 %0, ptr %8\n\
    \x20   %9 = mul u32 %1, %1\n\
    \x20   %10 = const bool true\n\
    \x20   condbr %10, bb1, bb2\n\
    bb1:\n\
    \x20   %11 = load i32, ptr %8\n\
    \x20   ret %11\n\
    bb2:\n\
    \x20   ret %0\n\
    }\n";

#[test]
fn copy_prop_forwards_same_type_copies_only() {
    let text = "functy.0 = (i32) -> (u32)\n\n\
        fn @f(functy.0) {\n\
        bb0(%0: i32):\n\
        \x20   %1 = copy i32 %0\n\
        \x20   %2 = copy u32 %1\n\
        \x20   %3 = copy u32 %2\n\
        \x20   ret %3\n\
        }\n";
    let m = module(text);
    let (out, witness) = run_pass(&passes::CopyProp, &m, "f").expect("copies to forward");
    let PassWitness::CopyProp(CopyPropWitness { forwards }) = &witness else {
        panic!("copy-prop witness");
    };
    assert_eq!(
        forwards,
        &vec![
            CopyForward {
                copy: ValueId::new(1),
                root: ValueId::new(0)
            },
            CopyForward {
                copy: ValueId::new(3),
                root: ValueId::new(2)
            },
        ],
        "the i32 -> u32 copy is not an identity and stays as the root of its chain"
    );
    assert_eq!(
        insts(&out),
        vec![
            &Inst::Copy {
                ty: Ty::U32,
                operand: ValueId::new(0)
            },
            &Inst::Return {
                values: vec![ValueId::new(2)]
            },
        ]
    );
}

#[test]
fn ptr_gep_rewrites_in_bounds_chains_only() {
    let m = module(FRAME);
    // The chain reads through copies; copy propagation runs first in the
    // pipeline, so the pass alone sees no chain here.
    assert!(run_pass(&passes::PtrGep, &m, "frame").is_none());
    let (after_copies, _) = run_pass(&passes::CopyProp, &m, "frame").unwrap();
    let mut m2 = m.clone();
    m2.functions[0] = after_copies;
    let (out, witness) = run_pass(&passes::PtrGep, &m2, "frame").expect("one chain");
    assert_eq!(witness.rewrite_count(), 1);
    assert!(insts(&out).iter().any(|i| matches!(
        i,
        Inst::GEP {
            pointee_ty: Ty::U8,
            inbounds: true,
            ..
        }
    )));

    // Offset 8 is one past the 8-byte slot: left alone.
    let oob = FRAME.replace("%5 = const i32 4", "%5 = const i32 8");
    let m = module(&oob);
    let (after_copies, _) = run_pass(&passes::CopyProp, &m, "frame").unwrap();
    let mut m2 = m.clone();
    m2.functions[0] = after_copies;
    assert!(run_pass(&passes::PtrGep, &m2, "frame").is_none());
}

/// The bridge's other address shapes: an integer round trip of a slot's
/// address, a constant offset from a pointer already inside the slot, and an
/// array element addressed by a constant index times the element size.
const CHAINS: &str = "type ty.0 = i32\n\nfuncty.0 = (i32) -> (i32)\n\n\
    fn @f(functy.0) {\n\
    bb0(%0: i32):\n\
    \x20   %1 = alloca [ty.0 x 4], align 4\n\
    \x20   %2 = ptrtoint ptr %1 to i32\n\
    \x20   %3 = inttoptr i32 %2 to ptr\n\
    \x20   store i32 %0, ptr %3\n\
    \x20   %4 = const i32 4\n\
    \x20   %5 = gep inbounds u8, ptr %1, %4\n\
    \x20   %6 = ptrtoint ptr %5 to i32\n\
    \x20   %7 = add i32 %6, %4\n\
    \x20   %8 = inttoptr i32 %7 to ptr\n\
    \x20   store i32 %0, ptr %8\n\
    \x20   %9 = const u32 3\n\
    \x20   %10 = bitcast u32 %9 to i32\n\
    \x20   %11 = mul i32 %10, %4\n\
    \x20   %12 = add i32 %2, %11\n\
    \x20   %13 = inttoptr i32 %12 to ptr\n\
    \x20   store i32 %0, ptr %13\n\
    \x20   %14 = load i32, ptr %3\n\
    \x20   %15 = load i32, ptr %8\n\
    \x20   %16 = load i32, ptr %13\n\
    \x20   %17 = add i32 %14, %15\n\
    \x20   %18 = add i32 %17, %16\n\
    \x20   ret %18\n\
    }\n";

#[test]
fn ptr_gep_rewrites_round_trips_derived_bases_and_constant_indices() {
    let m = module(CHAINS);
    let (out, witness) = run_pass(&passes::PtrGep, &m, "f").expect("three chains");
    trust_cg_verify::trust_ir_mid_tv::check_pass(&m, 32, func(&m, "f"), &out, &witness)
        .unwrap_or_else(|e| panic!("the checker refused the pass's own rewrite: {e}"));
    let PassWitness::PtrGep(w) = &witness else {
        panic!("pointer-chain witness");
    };
    let offsets: Vec<(u32, u64)> = w
        .rewrites
        .iter()
        .map(|r| (r.base.index(), r.offset))
        .collect();
    assert_eq!(offsets, vec![(1, 0), (5, 4), (1, 12)]);
    // Each slot address is now a pointer of its provenance, so the slot is
    // promoted and the function returns three times its argument.
    let (out, report) = optimize_module(&m, &MidConfig::wasm32());
    assert_eq!(report.rollback_count(), 0, "{:?}", report.rollbacks);
    assert!(report.tv.samples_compared > 0, "{:?}", report.tv);
    assert_eq!(report.allocas_after, 0, "{}", out);
    assert!(
        !insts(func(&out, "f"))
            .iter()
            .any(|i| matches!(i, Inst::Load { .. } | Inst::Store { .. })),
        "{:#?}",
        func(&out, "f")
    );

    // Negative controls, each left alone: a constant index that reaches one
    // past the end (3 * 4 + 4 = 16 bytes into 16), a derived base whose
    // offset leaves the slot (8 + 8), an index whose product would be
    // negative, and an unknown base.
    for (what, from, to) in [
        (
            "an index past the end",
            "%9 = const u32 3",
            "%9 = const u32 4",
        ),
        (
            "a derived offset past the end",
            "%7 = add i32 %6, %4",
            "%30 = const i32 12\n    %7 = add i32 %6, %30",
        ),
        (
            "a negative index",
            "%9 = const u32 3",
            "%9 = const u32 4294967295",
        ),
    ] {
        let text = CHAINS.replace(from, to);
        let m = module(&text);
        let (_, witness) = run_pass(&passes::PtrGep, &m, "f").expect("the other chains");
        let PassWitness::PtrGep(w) = &witness else {
            panic!("pointer-chain witness");
        };
        assert_eq!(w.rewrites.len(), 2, "{what}: {:?}", w.rewrites);
    }
    let unknown = "functy.0 = (ptr, i32) -> ()\n\n\
        fn @f(functy.0) {\n\
        bb0(%1: ptr, %0: i32):\n\
        \x20   %2 = ptrtoint ptr %1 to i32\n\
        \x20   %3 = inttoptr i32 %2 to ptr\n\
        \x20   store i32 %0, ptr %3\n\
        \x20   ret\n\
        }\n";
    assert!(run_pass(&passes::PtrGep, &module(unknown), "f").is_none());
}

#[test]
fn branch_fold_folds_and_removes_the_dead_arm() {
    let m = module(FRAME);
    let (out, witness) = run_pass(&passes::BranchFold, &m, "frame").expect("constant branch");
    assert_eq!(witness.rewrite_count(), 2, "one fold, one removed block");
    assert_eq!(out.blocks.len(), 2);
    assert!(matches!(
        out.blocks[0].body.last().unwrap().inst,
        Inst::Br { .. }
    ));
}

#[test]
fn dce_removes_dead_pure_code_and_keeps_effects() {
    let m = module(FRAME);
    let (out, witness) = run_pass(&passes::Dce, &m, "frame").expect("dead multiply");
    let PassWitness::Dce(dce) = &witness else {
        panic!("dce witness");
    };
    assert_eq!(dce.removals.len(), 1, "only the unused multiply is dead");
    assert_eq!(
        dce.removals[0].class,
        trust_cg_verify::trust_ir_mid_tv::RemovalClass::Refinement
    );
    assert!(
        insts(&out).iter().any(|i| matches!(i, Inst::Store { .. })),
        "the store stays"
    );
}

#[test]
fn the_pipeline_validates_every_pass_and_shrinks_the_frame_shape() {
    let m = module(FRAME);
    let (out, report) = optimize_module(&m, &MidConfig::wasm32());
    assert!(report.enabled);
    assert_eq!(report.functions_changed, 1);
    assert_eq!(report.rollback_count(), 0, "{:?}", report.rollbacks);
    let f = func(&out, "frame");
    assert!(
        !insts(f).iter().any(|i| matches!(
            i,
            Inst::Cast {
                op: CastOp::IntToPtr | CastOp::PtrToInt,
                ..
            } | Inst::Copy { .. }
                | Inst::CondBr { .. }
        )),
        "{f:#?}"
    );
    // The folded branch's target is merged into the entry.
    assert_eq!(f.blocks.len(), 1);
    assert!(report.tv.samples_compared > 0, "{:?}", report.tv);
    assert_eq!(report.proof_table.rejected, 0);
    let dce = report.passes.iter().find(|p| p.name == "dce").unwrap();
    assert!(
        dce.refinements >= 1,
        "the dead multiply's removal is a refinement"
    );
}

/// A pass that claims to forward a copy but rewrites the use to another
/// value: the checker refuses it and the manager keeps the snapshot.
struct LyingCopyProp;

impl MidPass for LyingCopyProp {
    fn name(&self) -> &'static str {
        "lying_copy_prop"
    }

    fn run(&self, cx: &PassContext<'_>, func: &Function) -> Option<(Function, PassWitness)> {
        let (mut out, witness) = passes::CopyProp.run(cx, func)?;
        // Send the returned value to the first parameter instead.
        let first = func.blocks[0].params.first()?.0;
        for node in out.blocks.iter_mut().flat_map(|b| &mut b.body) {
            if let Inst::Return { values } = &mut node.inst {
                values.fill(first);
            }
        }
        Some((out, witness))
    }
}

#[test]
fn a_refused_witness_rolls_the_function_back() {
    let text = "functy.0 = (i32, i32) -> (i32)\n\n\
        fn @f(functy.0) {\n\
        bb0(%0: i32, %1: i32):\n\
        \x20   %2 = copy i32 %1\n\
        \x20   ret %2\n\
        }\n";
    let m = module(text);
    let lying = LyingCopyProp;
    let (out, report) = manager::run(&m, &MidConfig::wasm32(), &[&lying]);
    assert_eq!(out, m, "the snapshot stays");
    assert_eq!(report.functions_changed, 0);
    assert_eq!(report.rollback_count(), 1);
    assert!(report.rollbacks[0].reason.starts_with("witness:"));
}

#[test]
fn proof_carrying_functions_are_skipped_and_counted() {
    let mut m = module(FRAME);
    m.proof_obligations.push(ProofObligation::new(
        trust_ir::value::ProofId::new(0),
        ObligationKind::MemorySafety,
        ProofStatus::Pending,
        "names the function",
    ));
    m.proof_obligations[0].function = Some(FuncId::new(0));
    let (out, report) = optimize_module(&m, &MidConfig::wasm32());
    assert_eq!(out, m);
    assert_eq!(report.skipped.get("module_obligation"), Some(&1));
    assert_eq!(report.functions_changed, 0);
}

#[test]
fn an_unrelated_obligation_is_preserved_by_the_transaction() {
    let mut m = module(FRAME);
    m.proof_obligations.push(ProofObligation::new(
        trust_ir::value::ProofId::new(0),
        ObligationKind::MemorySafety,
        ProofStatus::Pending,
        "names another function",
    ));
    m.proof_obligations[0].function = Some(FuncId::new(77));
    let (_, report) = optimize_module(&m, &MidConfig::wasm32());
    assert_eq!(report.functions_changed, 1);
    assert_eq!(report.proof_table.rejected, 0);
    assert!(report.proof_table.validated >= 1);
    assert_eq!(
        report.proof_table.preserved, report.proof_table.validated,
        "one Preserved row per validated transaction"
    );
}

#[test]
fn negative_control_an_untransported_obligation_is_refused() {
    let mut before = module(FRAME);
    before.proof_obligations.push(ProofObligation::new(
        trust_ir::value::ProofId::new(0),
        ObligationKind::MemorySafety,
        ProofStatus::Pending,
        "must be accounted for",
    ));
    let after = before.clone();
    // No disposition for obligation 0.
    let refused = manager::transport(&before, &after, "dce", Vec::new());
    assert!(refused.is_err(), "an obligation without a disposition");
    let accepted = manager::transport(&before, &after, "dce", manager::preserved_rows(&before));
    assert_eq!(accepted.map(|v| v.preserved), Ok(1));
}

#[test]
fn negative_control_an_untransportable_table_rolls_the_pass_back() {
    // Two obligations share one id: no transaction over this table validates,
    // so every function a pass changed is restored.
    let mut m = module(FRAME);
    for _ in 0..2 {
        let mut obligation = ProofObligation::new(
            trust_ir::value::ProofId::new(5),
            ObligationKind::MemorySafety,
            ProofStatus::Pending,
            "duplicate id",
        );
        obligation.function = Some(FuncId::new(77));
        m.proof_obligations.push(obligation);
    }
    let (out, report) = optimize_module(&m, &MidConfig::wasm32());
    assert_eq!(out, m, "every pass rolled back");
    assert!(report.proof_table.rejected > 0);
    assert_eq!(report.proof_table.validated, 0);
    assert!(
        report
            .rollbacks
            .iter()
            .all(|r| r.reason.starts_with("proof_table:"))
    );
}

#[test]
fn the_native_profile_is_reserved() {
    let m = module(FRAME);
    let config = MidConfig {
        profile: MidProfile::Native,
        ..MidConfig::wasm32()
    };
    let (out, report) = optimize_module(&m, &config);
    assert_eq!(out, m);
    assert!(!report.enabled);
}

#[test]
fn the_cfg_view_feeds_the_shared_analysis() {
    let m = module(FRAME);
    let analysis = TrustIrCfg::new(func(&m, "frame")).analysis();
    assert_eq!(analysis.rpo.len(), 3);
    let entry = func(&m, "frame").entry;
    for block in &analysis.rpo {
        assert!(analysis.dominates(entry, *block));
    }
}

#[test]
fn dce_keeps_the_bridges_write_through_insertfield() {
    let text = "type ty.0 = i32\n\nfuncty.0 = (i32) -> (i32)\n\n\
        fn @f(functy.0) {\n\
        bb0(%0: i32):\n\
        \x20   %1 = alloca [ty.0 x 1], align 4\n\
        \x20   %2 = insertfield [ty.0 x 1] %1, 0, %0\n\
        \x20   %3 = load i32, ptr %1\n\
        \x20   ret %3\n\
        }\n";
    let m = module(text);
    assert!(
        run_pass(&passes::Dce, &m, "f").is_none(),
        "a store through the slot is not dead"
    );
    // Scalar replacement reads the write-through form as the store it is
    // and promotes the slot.
    let (out, report) = optimize_module(&m, &MidConfig::wasm32());
    assert_eq!(report.rollback_count(), 0, "{:?}", report.rollbacks);
    assert!(report.tv.samples_compared > 0, "{:?}", report.tv);
    assert_eq!(
        insts(func(&out, "f")),
        vec![&Inst::Return {
            values: vec![ValueId::new(0)]
        }]
    );
}

#[test]
fn dce_keeps_a_division_whose_definedness_depends_on_its_operands() {
    let text = "type ty.0 = i32\n\nfuncty.0 = (i32) -> (i32)\n\n\
        fn @f(functy.0) {\n\
        bb0(%0: i32):\n\
        \x20   %1 = alloca [ty.0 x 1], align 4\n\
        \x20   %2 = ptrtoint ptr %1 to i32\n\
        \x20   %3 = const i32 1\n\
        \x20   %4 = udiv i32 %3, %2\n\
        \x20   ret %0\n\
        }\n";
    let m = module(text);
    assert!(
        run_pass(&passes::Dce, &m, "f").is_none(),
        "the division, and the address it reads, stay"
    );
}

#[test]
fn a_module_over_the_block_budget_is_left_unchanged() {
    let m = module(FRAME);
    let config = MidConfig {
        max_function_blocks: 2,
        ..MidConfig::wasm32()
    };
    let (out, report) = optimize_module(&m, &config);
    assert_eq!(out, m);
    assert!(!report.enabled);
    assert!(
        report
            .not_run
            .as_deref()
            .is_some_and(|why| why.contains("3 blocks"))
    );
}

/// A declared closure frame (trust-ir v58) gives `Ty::Closure` a byte size
/// in trust-ir's layout engine, which the passes read as plain bytes: the
/// mid-end is a barrier for such a module, though the same module without
/// the row is rewritten.
#[test]
fn a_module_declaring_a_closure_layout_is_left_unchanged() {
    let mut m = module(FRAME);
    let sig = m.functions[0].ty;
    m.closure_types.push(trust_ir::ClosureTy {
        func: sig,
        captures: vec![Ty::U64, Ty::U8],
    });
    let (rewritten, report) = optimize_module(&m, &MidConfig::wasm32());
    assert!(report.enabled && rewritten != m, "the control is rewritten");
    m.closure_layouts.push(trust_ir::ClosureLayoutDescriptor {
        origin: None,
        closure: trust_ir::ClosureTyId::new(0),
        size: 16,
        align: 8,
        capture_offsets: vec![8, 0],
    });
    m.validate_closure_layouts()
        .expect("the declared frame is coherent");
    assert!(
        m.ty_layout_shape(&Ty::Closure(trust_ir::ClosureTyId::new(0)))
            .is_ok_and(|shape| shape.size_bytes() == Some(16)),
        "the premise: a declared frame gives the closure a size"
    );
    let (out, report) = optimize_module(&m, &MidConfig::wasm32());
    assert_eq!(out, m);
    assert!(!report.enabled);
    assert!(
        report
            .not_run
            .as_deref()
            .is_some_and(|why| why.contains("closure layout")),
        "{:?}",
        report.not_run
    );
}

/// No mid-end pass models the validity fact on `BoxDeref`. Its presence is a
/// hard module barrier: even an unrelated dead instruction must remain, and
/// the complete instruction (operand, pointee and fact) must be byte-for-byte
/// unchanged under the wasm profile.
#[test]
fn a_module_with_box_deref_is_left_unchanged_and_reported_not_run() {
    use trust_ir::box_validity::{BoxDerefSite, BoxFactSession, BoxValidityFact, PremiseRoot};
    use trust_ir::{Endianness, StructPassingPolicy, TargetInfo};
    use trust_ir_build::ModuleBuilder;

    let mut builder = ModuleBuilder::new_with_target_info(
        "irmid_box_barrier",
        TargetInfo {
            triple: "wasm32-unknown-unknown".to_string(),
            pointer_size: 4,
            endianness: Endianness::Little,
            abi: None,
            struct_passing: StructPassingPolicy::NativeC,
        },
    );
    let signature = builder.add_func_type(vec![Ty::Ptr], vec![Ty::Ptr]);
    let mut function = builder.function("box_barrier", signature);
    let entry = function.create_block();
    let pointer = function.add_block_param(entry, Ty::Ptr);
    function.switch_to_block(entry);
    let _dead = function.iconst(Ty::I32, 7);
    let boxed = function.box_deref(
        Ty::I64,
        pointer,
        BoxValidityFact::premise(
            BoxDerefSite {
                item: [0x5a; 16],
                ordinal: 1,
            },
            BoxFactSession::PROOF_SNAPSHOT,
            PremiseRoot::ParamByValue,
        ),
    );
    function.ret(vec![boxed]);
    function.build();
    let module = builder.build().expect("valid BoxDeref fixture");
    assert_eq!(module.pointer_bits(), 32);

    let (out, report) = optimize_module(&module, &MidConfig::wasm32());
    assert_eq!(
        out, module,
        "the entire module, including its fact, is preserved"
    );
    assert!(!report.enabled);
    assert!(report.passes.is_empty());
    assert!(
        report.not_run.as_deref().is_some_and(|why| {
            why.contains("box_barrier")
                && why.contains("Inst::BoxDeref")
                && why.contains("validity fact")
        }),
        "{:?}",
        report.not_run
    );
}

// ---------------------------------------------------------------------------
// Stage B: store forwarding, dead slots, constant-table promotion
// ---------------------------------------------------------------------------

/// Two `i32` fields of a memory-backed local, each stored once in the entry
/// and read in one arm of a branch.
const SLOTS: &str = "type ty.0 = i32\n\nfuncty.0 = (i32, i32) -> (i32)\n\n\
    fn @f(functy.0) {\n\
    bb0(%0: i32, %1: i32):\n\
    \x20   %2 = alloca [ty.0 x 2], align 4\n\
    \x20   %3 = const i32 4\n\
    \x20   %4 = gep inbounds u8, ptr %2, %3\n\
    \x20   store i32 %0, ptr %2\n\
    \x20   store i32 %1, ptr %4\n\
    \x20   %5 = icmp slt i32 %0, %1\n\
    \x20   condbr %5, bb1, bb2\n\
    bb1:\n\
    \x20   %6 = load i32, ptr %2\n\
    \x20   br bb3(%6)\n\
    bb2:\n\
    \x20   %7 = load i32, ptr %4\n\
    \x20   br bb3(%7)\n\
    bb3(%8: i32):\n\
    \x20   ret %8\n\
    }\n";

fn forwarded(text: &str) -> usize {
    let m = module(text);
    run_pass(&passes::StoreFwd, &m, "f").map_or(0, |(_, w)| w.rewrite_count())
}

#[test]
fn store_forwarding_replaces_dominated_loads_and_the_slot_goes() {
    let m = module(SLOTS);
    let (out, witness) = run_pass(&passes::StoreFwd, &m, "f").expect("two loads to forward");
    assert_eq!(witness.rewrite_count(), 2);
    assert!(!insts(&out).iter().any(|i| matches!(i, Inst::Load { .. })));

    let (out, report) = optimize_module(&m, &MidConfig::wasm32());
    assert_eq!(report.rollback_count(), 0, "{:?}", report.rollbacks);
    let f = func(&out, "f");
    assert!(
        !insts(f).iter().any(|i| matches!(
            i,
            Inst::Alloca { .. } | Inst::Load { .. } | Inst::Store { .. } | Inst::GEP { .. }
        )),
        "the slot, its stores and its offset are gone: {f:#?}"
    );
    let pass = |name: &str| report.passes.iter().find(|p| p.name == name).unwrap();
    assert_eq!(pass("store_fwd").exact, 2);
    assert_eq!(pass("dead_slot").refinements, 2, "two dead stores");
    assert_eq!((report.allocas_before, report.allocas_after), (1, 0));
    assert!(report.tv.samples_compared > 0, "{:?}", report.tv);
}

#[test]
fn negative_control_a_may_alias_store_on_one_path_blocks_forwarding() {
    let text = SLOTS.replace(
        "bb1:\n    %6 = load i32, ptr %2\n    br bb3(%6)\n",
        "bb1:\n    store i32 %1, ptr %2\n    br bb4\nbb4:\n    %6 = load i32, ptr %2\n    br bb3(%6)\n",
    );
    assert_ne!(text, SLOTS);
    // The bb1 load now reads the bb1 store (forwarded); a load after a join
    // of the two stores would not be. Join them before a third load.
    let joined = text.replace(
        "bb3(%8: i32):\n    ret %8\n",
        "bb3(%8: i32):\n    %9 = load i32, ptr %2\n    %10 = add i32 %8, %9\n    ret %10\n",
    );
    let m = module(&joined);
    let (_, witness) = run_pass(&passes::StoreFwd, &m, "f").expect("the local reads forward");
    let PassWitness::StoreFwd(w) = &witness else {
        panic!("store-forwarding witness");
    };
    assert!(
        !w.forwards.iter().any(|f| f.result == ValueId::new(9)),
        "two stores reach the joined load: {w:?}"
    );
}

#[test]
fn negative_control_partial_overlap_and_mixed_width_are_left_alone() {
    // A byte store into the first field after its i32 store.
    let partial = SLOTS.replace(
        "    store i32 %1, ptr %4\n",
        "    store i32 %1, ptr %4\n    %20 = const i32 1\n    %21 = gep inbounds u8, ptr %2, %20\n    %22 = const u8 7\n    store u8 %22, ptr %21\n",
    );
    assert_eq!(forwarded(&partial), 1, "only the untouched field forwards");
    // The first field read as u32 after an i32 store.
    let mixed = SLOTS.replace("%6 = load i32, ptr %2", "%6 = load u32, ptr %2");
    let mixed = mixed.replace("br bb3(%6)", "%23 = bitcast u32 %6 to i32\n    br bb3(%23)");
    assert_eq!(forwarded(&mixed), 1, "a mixed-width read is not forwarded");
}

#[test]
fn negative_control_an_undefined_read_is_left_alone() {
    // The second field is stored only on one arm.
    let text = SLOTS
        .replace("    store i32 %1, ptr %4\n", "")
        .replace("bb2:\n", "bb2:\n    br bb5\nbb5:\n")
        .replace("bb1:\n", "bb1:\n    store i32 %1, ptr %4\n");
    assert_eq!(forwarded(&text), 1, "the bb2 read sees no store");
}

#[test]
fn negative_control_an_escaping_or_observed_slot_is_left_alone() {
    let escaped = format!(
        "{}\nfn @g(functy.1) {{\n}}\n",
        SLOTS
            .replace(
                "functy.0 = (i32, i32) -> (i32)\n\n",
                "functy.0 = (i32, i32) -> (i32)\n\nfuncty.1 = (ptr) -> ()\n\n",
            )
            .replace(
                "    %5 = icmp slt",
                "    call @func.1(%2)\n    %5 = icmp slt"
            )
    );
    assert_eq!(forwarded(&escaped), 0, "the callee may write the slot");
    let observed = SLOTS.replace(
        "bb3(%8: i32):\n    ret %8\n",
        "bb3(%8: i32):\n    %30 = ptrtoint ptr %2 to i32\n    %31 = add i32 %8, %30\n    ret %31\n",
    );
    assert_eq!(forwarded(&observed), 0, "the address is observed");
    let pointer = "functy.0 = (ptr) -> (ptr)\n\n\
        fn @f(functy.0) {\n\
        bb0(%0: ptr):\n\
        \x20   %1 = alloca ptr\n\
        \x20   store ptr %0, ptr %1\n\
        \x20   %2 = load ptr, ptr %1\n\
        \x20   ret %2\n\
        }\n";
    assert_eq!(forwarded(pointer), 0, "a reloaded pointer is re-resolved");
}

#[test]
fn negative_control_an_irreducible_cfg_is_left_alone() {
    let text = "functy.0 = (i32, bool) -> (i32)\n\n\
        fn @f(functy.0) {\n\
        bb0(%0: i32, %1: bool):\n\
        \x20   %2 = alloca i32\n\
        \x20   store i32 %0, ptr %2\n\
        \x20   condbr %1, bb1, bb2\n\
        bb1:\n\
        \x20   %3 = load i32, ptr %2\n\
        \x20   condbr %1, bb2, bb3\n\
        bb2:\n\
        \x20   condbr %1, bb1, bb3\n\
        bb3:\n\
        \x20   ret %0\n\
        }\n";
    assert_eq!(forwarded(text), 0, "two entries into the bb1/bb2 cycle");
    // The same load in a reducible shape forwards.
    let reducible = text.replace("condbr %1, bb1, bb2\nbb1:", "br bb1\nbb1:");
    assert_eq!(forwarded(&reducible), 1);
}

#[test]
fn dead_slot_removal_drops_the_stores_of_an_unread_slot() {
    let text = "type ty.0 = i32\n\nfuncty.0 = (i32) -> (i32)\n\n\
        fn @f(functy.0) {\n\
        bb0(%0: i32):\n\
        \x20   %1 = alloca [ty.0 x 2], align 4\n\
        \x20   store i32 %0, ptr %1\n\
        \x20   ret %0\n\
        }\n";
    let m = module(text);
    let (out, witness) = run_pass(&passes::DeadSlotRemoval, &m, "f").expect("a dead slot");
    assert_eq!(witness.rewrite_count(), 1);
    assert!(!insts(&out).iter().any(|i| matches!(i, Inst::Store { .. })));
    // A read slot stays.
    let read = text.replace("    ret %0\n", "    %2 = load i32, ptr %1\n    ret %2\n");
    assert!(run_pass(&passes::DeadSlotRemoval, &module(&read), "f").is_none());
}

/// The rustc bridge's local constant table, `[3, 1, 4, 1][i & 7]` behind the
/// bounds check `i & 7 < 4`: four constant stores through pointer chains,
/// then a read through `inttoptr(ptrtoint(t) + idx * 4)`.
const TABLE: &str = "type ty.0 = u32\n\nfuncty.0 = (u32) -> (u32)\n\n\
    fn @tbl(functy.0) {\n\
    bb0(%1: u32):\n\
    \x20   %6 = alloca [ty.0 x 4], align 4\n\
    \x20   %7 = const u32 3\n\
    \x20   store u32 %7, ptr %6\n\
    \x20   %8 = const u32 1\n\
    \x20   %9 = const i32 4\n\
    \x20   %11 = ptrtoint ptr %6 to i32\n\
    \x20   %13 = add i32 %11, %9\n\
    \x20   %14 = inttoptr i32 %13 to ptr\n\
    \x20   store u32 %8, ptr %14\n\
    \x20   %15 = const u32 4\n\
    \x20   %16 = const i32 8\n\
    \x20   %18 = ptrtoint ptr %6 to i32\n\
    \x20   %20 = add i32 %18, %16\n\
    \x20   %21 = inttoptr i32 %20 to ptr\n\
    \x20   store u32 %15, ptr %21\n\
    \x20   %22 = const u32 1\n\
    \x20   %23 = const i32 12\n\
    \x20   %25 = ptrtoint ptr %6 to i32\n\
    \x20   %27 = add i32 %25, %23\n\
    \x20   %28 = inttoptr i32 %27 to ptr\n\
    \x20   store u32 %22, ptr %28\n\
    \x20   %58 = const u32 7\n\
    \x20   %57 = and u32 %1, %58\n\
    \x20   %61 = const u32 4\n\
    \x20   %60 = icmp ult u32 %57, %61\n\
    \x20   condbr %60, bb1, bb3\n\
    bb3:\n\
    \x20   unreachable\n\
    bb1:\n\
    \x20   %67 = ptrtoint ptr %6 to i32\n\
    \x20   %68 = bitcast u32 %57 to i32\n\
    \x20   %69 = const i32 4\n\
    \x20   %70 = mul i32 %68, %69\n\
    \x20   %71 = add i32 %67, %70\n\
    \x20   %72 = inttoptr i32 %71 to ptr\n\
    \x20   %65 = load u32, ptr %72\n\
    \x20   ret %65\n\
    }\n";

fn promoted(text: &str) -> (Module, crate::IrmidReport) {
    let m = module(text);
    optimize_module(&m, &MidConfig::wasm32())
}

fn ctp_count(report: &crate::IrmidReport) -> usize {
    report
        .passes
        .iter()
        .find(|p| p.name == "ctp")
        .map_or(0, |p| p.exact + p.refinements)
}

#[test]
fn a_local_constant_table_becomes_read_only_data() {
    let (out, report) = promoted(TABLE);
    assert_eq!(report.rollback_count(), 0, "{:?}", report.rollbacks);
    assert_eq!(ctp_count(&report), 1, "{:?}", report.passes);
    assert_eq!(report.globals_added, 1);
    assert_eq!((report.allocas_before, report.allocas_after), (1, 0));
    let f = func(&out, "tbl");
    assert!(
        !insts(f)
            .iter()
            .any(|i| matches!(i, Inst::Alloca { .. } | Inst::Store { .. })),
        "{f:#?}"
    );
    assert!(
        insts(f)
            .iter()
            .any(|i| matches!(i, Inst::GlobalAddr { .. }))
    );
    let global = out.globals.last().expect("the promoted table");
    assert!(!global.mutable);
    assert_eq!(global.linkage, trust_ir::Linkage::Internal);
    assert_eq!(
        global.initializer,
        Some(trust_ir::Constant::Bytes {
            data: vec![3, 0, 0, 0, 1, 0, 0, 0, 4, 0, 0, 0, 1, 0, 0, 0],
            utf8: false
        })
    );
    assert!(report.tv.samples_compared > 0, "{:?}", report.tv);
}

#[test]
fn negative_controls_the_table_stays_a_slot() {
    // The address is compared: its bits are observed.
    let observed = TABLE.replace(
        "    ret %65\n",
        "    %80 = icmp ult i32 %67, %69\n    %81 = select u32 %80, %65, %57\n    ret %81\n",
    );
    // The address escapes through a call.
    let escaped = format!(
        "{}\nfn @g(functy.1) {{\n}}\n",
        TABLE
            .replace(
                "functy.0 = (u32) -> (u32)\n\n",
                "functy.0 = (u32) -> (u32)\n\nfuncty.1 = (ptr) -> ()\n\n",
            )
            .replace(
                "    %58 = const u32 7\n",
                "    call @func.1(%6)\n    %58 = const u32 7\n"
            )
    );
    // A write after initialization (not a constant).
    let written = TABLE.replace(
        "    %65 = load u32",
        "    store u32 %1, ptr %6\n    %65 = load u32",
    );
    // An index the bounds check no longer bounds.
    let unbounded = TABLE.replace("condbr %60, bb1, bb3", "br bb1");
    for (what, text) in [
        ("observed", observed),
        ("escaped", escaped),
        ("written", written),
        ("unbounded", unbounded),
    ] {
        let (out, report) = promoted(&text);
        assert_eq!(ctp_count(&report), 0, "{what}: {:?}", report.passes);
        assert_eq!(out.globals.len(), module(&text).globals.len(), "{what}");
        assert_eq!(report.rollback_count(), 0, "{what}: {:?}", report.rollbacks);
    }
}

#[test]
fn the_shared_escape_analysis_bounds_the_table_index() {
    // The lane's capture facts, asked the promotion's question: under the
    // dominating check the read through `inttoptr` resolves to the
    // allocation (not stray); without it the pointer may land in a
    // neighbour, and reading through it is a capture.
    use crate::escape::{Extent, FuncFacts, ParamCaptures, derive};
    for (text, bounded) in [
        (TABLE.to_string(), true),
        (TABLE.replace("condbr %60, bb1, bb3", "br bb1"), false),
    ] {
        let m = module(&text);
        let f = func(&m, "tbl");
        let index = f
            .blocks
            .iter()
            .enumerate()
            .map(|(i, b)| (b.id, i))
            .collect();
        let facts = FuncFacts::new(f, index, passes::value_types(f));
        let d = derive(
            &facts,
            &ParamCaptures::default(),
            Extent::Bytes(16),
            &[ValueId::new(6)],
        );
        assert_eq!(d.captured, !bounded, "{text}");
        if bounded {
            assert!(!d.facts[&ValueId::new(72)].stray);
        }
    }
}

#[test]
fn negative_control_a_value_of_another_type_is_not_forwarded() {
    let text = format!(
        "{}\nfn @g(functy.1) {{\n}}\n",
        SLOTS
            .replace(
                "functy.0 = (i32, i32) -> (i32)\n\n",
                "functy.0 = (i32, i32) -> (i32)\n\nfuncty.1 = () -> (u32)\n\n",
            )
            .replace(
                "    store i32 %0, ptr %2\n",
                "    %40 = call @func.1()\n    store i32 %40, ptr %2\n",
            )
    );
    assert_eq!(forwarded(&text), 1, "only the second field's load forwards");
    let same = text
        .replace("funcy.1 = () -> (u32)", "")
        .replace("() -> (u32)", "() -> (i32)");
    assert_eq!(
        forwarded(&same),
        2,
        "a call result of the load's type forwards"
    );
}

/// The differential's view follows the module: a promoted table's global is
/// in the view the candidate runs against even when the promotion adds no
/// type (the module already has `u8`), so the candidate is compared, not
/// rolled back as reading a global the view lacks.
#[test]
fn a_promoted_table_is_compared_against_its_global() {
    let text = TABLE.replace("type ty.0 = u32\n", "type ty.0 = u32\n\ntype ty.1 = u8\n");
    let (_, report) = promoted(&text);
    assert_eq!(report.rollback_count(), 0, "{:?}", report.rollbacks);
    assert_eq!(ctp_count(&report), 1);
    let ctp = &report.tv.by_pass["ctp"];
    assert_eq!((ctp.candidates, ctp.compared), (1, 1), "{:?}", report.tv);
}

/// Every candidate is counted once: compared, or under one reason. A
/// function reaching memory through a pointer parameter is compared under a
/// driver (the scalar-only differential had no input for it); one that
/// calls a declaration, and one with a function-pointer parameter, are not,
/// by name.
#[test]
fn every_candidate_is_compared_or_counted_under_one_reason() {
    let text = "type ty.0 = i32\n\n\
        functy.0 = (ptr, i32) -> (i32)\n\n\
        functy.1 = (i32) -> (i32)\n\n\
        functy.2 = (functy.1, i32) -> (i32)\n\n\
        fn @mem(functy.0) {\n\
        bb0(%0: ptr, %1: i32):\n\
        \x20   %2 = copy ptr %0\n\
        \x20   store i32 %1, ptr %2\n\
        \x20   %3 = load i32, ptr %0\n\
        \x20   %4 = copy i32 %3\n\
        \x20   ret %4\n\
        }\n\n\
        fn @ext(functy.1) {\n\
        }\n\n\
        fn @calls(functy.1) {\n\
        bb0(%0: i32):\n\
        \x20   %1 = copy i32 %0\n\
        \x20   %2 = call @func.1(%1)\n\
        \x20   ret %2\n\
        }\n\n\
        fn @fnptr(functy.2) {\n\
        bb0(%0: functy.1, %1: i32):\n\
        \x20   %2 = copy i32 %1\n\
        \x20   ret %2\n\
        }\n";
    let m = module(text);
    let (_, report) = optimize_module(&m, &MidConfig::wasm32());
    let tv = &report.tv;
    assert_eq!(report.rollback_count(), 0, "{:?}", report.rollbacks);
    let not_compared: usize = tv.not_compared.values().sum();
    assert_eq!(
        tv.function_passes,
        tv.function_passes_compared + not_compared,
        "{tv:?}"
    );
    let by_pass: usize = tv.by_pass.values().map(|p| p.candidates).sum();
    assert_eq!(by_pass, tv.function_passes);
    assert!(tv.function_passes_driven >= 1, "{tv:?}");
    assert!(tv.samples_memory_compared > 0, "{tv:?}");
    assert!(
        tv.not_compared
            .contains_key("not_executed:call_to_declaration"),
        "{tv:?}"
    );
    assert!(
        tv.not_compared
            .contains_key("not_synthesizable:function_pointer"),
        "{tv:?}"
    );
    assert_eq!(
        tv.function_passes_not_synthesizable,
        tv.not_compared["not_synthesizable:function_pointer"]
    );
    let json = report.to_json();
    assert!(json["tv"]["by_pass"]["copy_prop"]["compared"].as_u64() >= Some(1));
    assert!(json["tv"]["not_compared"].is_object());
}

/// A module's interpreter steps are bounded by its budget: past it,
/// candidates are checked by their witness alone and counted.
#[test]
fn a_spent_budget_is_counted_as_over_budget() {
    let config = MidConfig {
        module_step_budget: 0,
        ..MidConfig::wasm32()
    };
    let (_, report) = optimize_module(&module(FRAME), &config);
    assert!(report.tv.function_passes > 0);
    assert_eq!(
        report.tv.not_compared.get("over_budget"),
        Some(&report.tv.function_passes)
    );
    assert_eq!(report.tv.steps, 0);
}

/// A candidate whose inputs have nothing to compare (no parameter memory,
/// no result) is not counted as compared: both bodies returning observes
/// only termination.
#[test]
fn a_candidate_with_nothing_to_observe_is_not_compared() {
    let text = "functy.0 = (i32) -> ()\n\n\
        fn @f(functy.0) {\n\
        bb0(%0: i32):\n\
        \x20   %1 = copy i32 %0\n\
        \x20   %2 = add i32 %1, %0\n\
        \x20   ret\n\
        }\n";
    let (_, report) = optimize_module(&module(text), &MidConfig::wasm32());
    let tv = &report.tv;
    assert!(tv.function_passes > 0, "{tv:?}");
    assert_eq!(tv.function_passes_compared, 0, "{tv:?}");
    assert_eq!(
        tv.not_compared.get("nothing_observed"),
        Some(&tv.function_passes),
        "{tv:?}"
    );
    assert_eq!(tv.samples_compared, 0);
    assert!(tv.samples_nothing_observed > 0);
}

/// Inputs that alias two pointer parameters are run and counted.
#[test]
fn aliasing_inputs_are_compared_and_counted() {
    let text = "type ty.0 = i32\n\n\
        functy.0 = (ptr, ptr) -> (i32)\n\n\
        fn @f(functy.0) {\n\
        bb0(%0: ptr, %1: ptr):\n\
        \x20   %2 = copy ptr %0\n\
        \x20   %3 = const i32 1\n\
        \x20   store i32 %3, ptr %2\n\
        \x20   %4 = const i32 2\n\
        \x20   store i32 %4, ptr %1\n\
        \x20   %5 = load i32, ptr %0\n\
        \x20   ret %5\n\
        }\n";
    let (_, report) = optimize_module(&module(text), &MidConfig::wasm32());
    let tv = &report.tv;
    assert_eq!(report.rollback_count(), 0, "{:?}", report.rollbacks);
    assert!(tv.function_passes_compared > 0, "{tv:?}");
    assert!(tv.samples_aliased_compared >= 2, "{tv:?}");
    assert!(tv.samples_memory_compared > 0, "{tv:?}");
}

/// A disagreement on which the candidate's run reached a verdict of its own
/// is a comparison; one it could not finish is counted by why.
#[test]
fn a_disagreement_is_compared_only_when_the_candidate_finished() {
    use trust_cg_verify::trust_ir_mid_tv::InputOutcome;
    let returned = InputOutcome::Returned {
        results: Vec::new(),
        memory: Vec::new(),
    };
    assert_eq!(manager::unfinished(&returned), None);
    assert_eq!(manager::unfinished(&InputOutcome::Undefined), None);
    assert_eq!(
        manager::unfinished(&InputOutcome::NotExecuted("out_of_fuel")).as_deref(),
        Some("mismatch:target_not_executed:out_of_fuel")
    );
    assert_eq!(
        manager::unfinished(&InputOutcome::OverBudget).as_deref(),
        Some("mismatch:target_over_budget")
    );
}

// ---------------------------------------------------------------------------
// P5 stage A: scalar replacement
// ---------------------------------------------------------------------------

/// Run scalar replacement alone on `name`, check its witness, and return the
/// rewrite.
fn sroa(m: &Module, name: &str) -> Option<(Function, PassWitness)> {
    let (out, witness) = run_pass(&passes::Sroa, m, name)?;
    trust_cg_verify::trust_ir_mid_tv::check_pass(m, 32, func(m, name), &out, &witness)
        .unwrap_or_else(|e| panic!("the checker refused the pass's own rewrite: {e}"));
    Some((out, witness))
}

fn promoted_slots(m: &Module, name: &str) -> usize {
    sroa(m, name).map_or(0, |(_, w)| match w {
        PassWitness::Sroa(w) => w.slots.len(),
        _ => panic!("scalar-replacement witness"),
    })
}

/// A loop-carried accumulator and a two-field slot written on one arm of a
/// diamond and read at the join: both need block parameters.
const JOINS: &str = "type ty.0 = i32\n\nfuncty.0 = (i32, i32) -> (i32)\n\n\
    fn @f(functy.0) {\n\
    bb0(%0: i32, %1: i32):\n\
    \x20   %2 = alloca [ty.0 x 2], align 4\n\
    \x20   %3 = const i32 4\n\
    \x20   %4 = gep inbounds u8, ptr %2, %3\n\
    \x20   %30 = alloca i32\n\
    \x20   %31 = const i32 0\n\
    \x20   store i32 %31, ptr %30\n\
    \x20   store i32 %0, ptr %2\n\
    \x20   store i32 %1, ptr %4\n\
    \x20   %5 = icmp slt i32 %0, %1\n\
    \x20   condbr %5, bb1, bb2\n\
    bb1:\n\
    \x20   store i32 %1, ptr %2\n\
    \x20   br bb3\n\
    bb2:\n\
    \x20   br bb3\n\
    bb3:\n\
    \x20   %32 = const i32 7\n\
    \x20   %33 = and i32 %1, %32\n\
    \x20   br bb4(%31)\n\
    bb4(%34: i32):\n\
    \x20   %35 = icmp slt i32 %34, %33\n\
    \x20   condbr %35, bb5, bb6\n\
    bb5:\n\
    \x20   %36 = load i32, ptr %30\n\
    \x20   %37 = load i32, ptr %2\n\
    \x20   %38 = add i32 %36, %37\n\
    \x20   store i32 %38, ptr %30\n\
    \x20   %39 = const i32 1\n\
    \x20   %40 = add i32 %34, %39\n\
    \x20   br bb4(%40)\n\
    bb6:\n\
    \x20   %6 = load i32, ptr %2\n\
    \x20   %7 = load i32, ptr %4\n\
    \x20   %8 = load i32, ptr %30\n\
    \x20   %9 = add i32 %6, %7\n\
    \x20   %10 = add i32 %9, %8\n\
    \x20   ret %10\n\
    }\n";

#[test]
fn scalar_replacement_joins_through_block_parameters_and_the_frame_empties() {
    let m = module(JOINS);
    let (out, witness) = sroa(&m, "f").expect("two slots to promote");
    let PassWitness::Sroa(w) = &witness else {
        panic!("scalar-replacement witness");
    };
    assert_eq!(w.slots.len(), 2);
    assert!(
        !insts(&out)
            .iter()
            .any(|i| matches!(i, Inst::Load { .. } | Inst::Store { .. }))
    );
    let params = |id: u32| {
        out.blocks
            .iter()
            .find(|b| b.id == trust_ir::BlockId::new(id))
            .unwrap()
            .params
            .len()
    };
    assert_eq!(params(3), 1, "field 0 of the pair joins at bb3");
    assert_eq!(params(4), 2, "the accumulator joins at the loop header");

    let (out, report) = optimize_module(&m, &MidConfig::wasm32());
    assert_eq!(report.rollback_count(), 0, "{:?}", report.rollbacks);
    assert_eq!((report.allocas_before, report.allocas_after), (2, 0));
    let f = func(&out, "f");
    assert!(
        !insts(f).iter().any(|i| matches!(
            i,
            Inst::Alloca { .. } | Inst::Load { .. } | Inst::Store { .. } | Inst::GEP { .. }
        )),
        "{f:#?}"
    );
    let pass = report.passes.iter().find(|p| p.name == "sroa").unwrap();
    assert!(pass.refinements >= 9, "{pass:?}");
    assert!(report.tv.samples_compared > 0, "{:?}", report.tv);
}

#[test]
fn scalar_replacement_reinterprets_full_values_only() {
    // A signedness view of a parameter, a float's bits, and a pointer field.
    let text = "functy.0 = (u32, f32) -> (i32)\n\n\
        fn @f(functy.0) {\n\
        bb0(%0: u32, %1: f32):\n\
        \x20   %2 = alloca i32\n\
        \x20   %3 = alloca i32\n\
        \x20   %4 = alloca ptr\n\
        \x20   store u32 %0, ptr %2\n\
        \x20   %5 = load i32, ptr %2\n\
        \x20   store f32 %1, ptr %3\n\
        \x20   %6 = load i32, ptr %3\n\
        \x20   store ptr %2, ptr %4\n\
        \x20   %7 = load ptr, ptr %4\n\
        \x20   %8 = ptrtoint ptr %7 to i32\n\
        \x20   %9 = sub i32 %8, %8\n\
        \x20   %10 = add i32 %5, %6\n\
        \x20   %11 = add i32 %10, %9\n\
        \x20   ret %11\n\
        }\n";
    let m = module(text);
    // The pointer stored in %4 is %2's address, so %2 escapes and stays.
    assert_eq!(promoted_slots(&m, "f"), 2);
    let (out, report) = optimize_module(&m, &MidConfig::wasm32());
    assert_eq!(report.rollback_count(), 0, "{:?}", report.rollbacks);
    assert!(report.tv.samples_compared > 0, "{:?}", report.tv);
    let casts: Vec<CastOp> = insts(func(&out, "f"))
        .iter()
        .filter_map(|i| match i {
            Inst::Cast { op, .. } => Some(*op),
            _ => None,
        })
        .collect();
    // The pointer field holds a slot's address, so it is carried as a `ptr`
    // (no integer round trip); the source's own `ptrtoint` stays.
    assert!(
        casts.contains(&CastOp::Bitcast) && !casts.contains(&CastOp::IntToPtr),
        "{casts:?}"
    );

    // The same views of a value that may be poison (a load) stay in memory.
    let poison = text
        .replace(
            "    store u32 %0, ptr %2\n",
            "    %20 = alloca u32\n    %21 = load u32, ptr %20\n    store u32 %21, ptr %2\n",
        )
        .replace(
            "    store f32 %1, ptr %3\n",
            "    %22 = alloca f32\n    %23 = load f32, ptr %22\n    store f32 %23, ptr %3\n",
        );
    let m = module(&poison);
    assert_eq!(promoted_slots(&m, "f"), 1, "only the pointer field");
}

#[test]
fn negative_control_scalar_replacement_leaves_unsafe_slots_alone() {
    let base = "functy.0 = (i32, i64) -> (i32)\n\nfuncty.1 = (ptr) -> ()\n\n\
        fn @f(functy.0) {\n\
        bb0(%0: i32, %5: i64):\n\
        \x20   %1 = alloca i64\n\
        \x20   store i32 %0, ptr %1\n\
        \x20   %2 = load i32, ptr %1\n\
        \x20   ret %2\n\
        }\n\n\
        fn @g(functy.1) {\n\
        }\n";
    assert_eq!(promoted_slots(&module(base), "f"), 1);
    let cases = [
        (
            "a mixed width over a value that may be poison",
            base.replace(
                "    store i32 %0, ptr %1\n",
                "    %6 = alloca i32\n    %7 = load i32, ptr %6\n    store i32 %7, ptr %1\n",
            )
            .replace("%2 = load i32, ptr %1", "%2 = load i32, ptr %1\n    %3 = load i64, ptr %1"),
        ),
        (
            "a partial overlap",
            base.replace(
                "    %2 = load i32, ptr %1\n",
                "    %2 = load i32, ptr %1\n    %3 = const i32 2\n    %4 = gep inbounds u8, ptr %1, %3\n    store i32 %0, ptr %4\n",
            ),
        ),
        ("a volatile access", base.replace("%2 = load", "%2 = volatile load")),
        (
            "an atomic access",
            base.replace(
                "    %2 = load i32, ptr %1\n",
                "    %2 = load i32, ptr %1\n    %3 = atomic_load seq_cst i32, ptr %1\n",
            ),
        ),
        (
            "an escape through a call",
            base.replace("    ret %2\n", "    call @func.1(%1)\n    ret %2\n"),
        ),
        (
            "observed address bits",
            base.replace(
                "    ret %2\n",
                "    %3 = ptrtoint ptr %1 to i32\n    %4 = add i32 %2, %3\n    ret %4\n",
            ),
        ),
        (
            "a stored address",
            base.replace(
                "    ret %2\n",
                "    %3 = alloca ptr\n    store ptr %1, ptr %3\n    ret %2\n",
            ),
        ),
        (
            "a returned address",
            base.replace("(i32, i64) -> (i32)", "(i32, i64) -> (ptr)").replace("    ret %2\n", "    ret %1\n"),
        ),
        (
            "an undefined read",
            base.replace("    store i32 %0, ptr %1\n", ""),
        ),
        (
            "a 16-byte field read as a pair of words",
            base.replace("alloca i64", "alloca i128")
                .replace("store i32 %0", "%6 = sext i64 %5 to i128\n    store i128 %6")
                .replace("%2 = load i32, ptr %1\n    ret %2", "%2 = load (i64, i64), ptr %1\n    %7 = extractfield i64 %2, 0\n    %8 = trunc i64 %7 to i32\n    ret %8"),
        ),
        (
            "a stored undef",
            base.replace("    store i32 %0, ptr %1\n", "    %6 = undef i32\n    store i32 %6, ptr %1\n"),
        ),
    ];
    for (what, text) in cases {
        assert_eq!(promoted_slots(&module(&text), "f"), 0, "{what}:\n{text}");
    }
}

/// A 16-byte field read and written as 128-bit integers alone is promoted
/// (the wasm32 lane carries it in two `i64` locals), its signedness views
/// joined by a `bitcast`.
#[test]
fn scalar_replacement_promotes_a_128_bit_integer_field() {
    let text = "functy.0 = (i64, bool) -> (i32)\n\n\
        fn @f(functy.0) {\n\
        bb0(%0: i64, %1: bool):\n\
        \x20   %2 = alloca i128\n\
        \x20   %3 = sext i64 %0 to i128\n\
        \x20   store i128 %3, ptr %2\n\
        \x20   condbr %1, bb1, bb2\n\
        bb1:\n\
        \x20   %4 = zext i64 %0 to u128\n\
        \x20   store u128 %4, ptr %2\n\
        \x20   br bb2\n\
        bb2:\n\
        \x20   %5 = load i128, ptr %2\n\
        \x20   %6 = trunc i128 %5 to i32\n\
        \x20   ret %6\n\
        }\n";
    let m = module(text);
    assert_eq!(promoted_slots(&m, "f"), 1);
    let (_, report) = optimize_module(&m, &MidConfig::wasm32());
    assert_eq!(report.rollback_count(), 0, "{:?}", report.rollbacks);
    assert_eq!(report.allocas_after, 0);
}

#[test]
fn negative_control_scalar_replacement_leaves_irreducible_and_unreachable_cfgs_alone() {
    let irreducible = "functy.0 = (i32, bool) -> (i32)\n\n\
        fn @f(functy.0) {\n\
        bb0(%0: i32, %1: bool):\n\
        \x20   %2 = alloca i32\n\
        \x20   store i32 %0, ptr %2\n\
        \x20   condbr %1, bb1, bb2\n\
        bb1:\n\
        \x20   %3 = load i32, ptr %2\n\
        \x20   condbr %1, bb2, bb3\n\
        bb2:\n\
        \x20   condbr %1, bb1, bb3\n\
        bb3:\n\
        \x20   ret %0\n\
        }\n";
    assert_eq!(promoted_slots(&module(irreducible), "f"), 0);
    let reducible = irreducible.replace("condbr %1, bb1, bb2\nbb1:", "br bb1\nbb1:");
    assert_eq!(promoted_slots(&module(&reducible), "f"), 1);
    let unreachable =
        reducible.replace("bb3:\n    ret %0\n", "bb3:\n    ret %0\nbb9:\n    br bb1\n");
    assert_eq!(promoted_slots(&module(&unreachable), "f"), 0);
}

#[test]
fn dce_removes_a_dead_offset_chain_rooted_at_an_allocation() {
    let text = "functy.0 = (i32) -> (i32)\n\n\
        fn @f(functy.0) {\n\
        bb0(%0: i32):\n\
        \x20   %1 = alloca (i32, i32, i32)\n\
        \x20   %2 = const i32 1\n\
        \x20   %3 = gep inbounds i32, ptr %1, %2\n\
        \x20   %4 = gep inbounds u8, ptr %3, %2\n\
        \x20   %5 = ptrtoptr ptr %4 to &u8\n\
        \x20   ret %0\n\
        }\n";
    let m = module(text);
    let (out, report) = optimize_module(&m, &MidConfig::wasm32());
    assert_eq!(report.rollback_count(), 0, "{:?}", report.rollbacks);
    assert_eq!(report.allocas_after, 0);
    assert_eq!(insts(func(&out, "f")).len(), 1, "only the return stays");
}

#[test]
fn a_pointer_slot_holding_a_slot_address_is_carried_as_a_ptr() {
    let text = "functy.0 = (i32) -> (i32)\n\n\
        fn @f(functy.0) {\n\
        bb0(%0: i32):\n\
        \x20   %1 = alloca i32\n\
        \x20   %2 = alloca ptr\n\
        \x20   store i32 %0, ptr %1\n\
        \x20   %5 = ptrtoptr ptr %1 to &i32\n\
        \x20   store &i32 %5, ptr %2\n\
        \x20   %3 = load *const i32, ptr %2\n\
        \x20   %4 = load i32, ptr %3\n\
        \x20   ret %4\n\
        }\n";
    let m = module(text);
    let (out, witness) = sroa(&m, "f").expect("the pointer slot");
    let PassWitness::Sroa(w) = &witness else {
        panic!("scalar-replacement witness");
    };
    assert_eq!(w.slots[0].fields[0].carrier, Ty::Ptr);
    // Views of the carried pointer are `ptrtoptr`s: the address never
    // becomes an integer, so the pointee's address is not observed.
    assert!(!insts(&out).iter().any(|i| matches!(
        i,
        Inst::Cast {
            op: CastOp::PtrToInt | CastOp::IntToPtr,
            ..
        }
    )));
    let (out, report) = optimize_module(&m, &MidConfig::wasm32());
    assert_eq!(report.rollback_count(), 0, "{:?}", report.rollbacks);
    assert!(report.tv.samples_compared > 0, "{:?}", report.tv);
    assert_eq!(report.allocas_after, 0, "the pointee is promoted too");
    assert_eq!(
        insts(func(&out, "f")),
        vec![&Inst::Return {
            values: vec![ValueId::new(0)]
        }]
    );

    // A stored pointer of unknown provenance (a parameter) is carried as an
    // integer instead, its `ptrtoint` and `inttoptr` on `ptr` only (trust-ir's
    // validator).
    let param = text
        .replace("(i32) -> (i32)", "(i32, &i32) -> (i32)")
        .replace("bb0(%0: i32):", "bb0(%0: i32, %9: &i32):")
        .replace("store &i32 %5, ptr %2", "store &i32 %9, ptr %2");
    let m = module(&param);
    let (out, witness) = sroa(&m, "f").expect("the pointer slot");
    let PassWitness::Sroa(w) = &witness else {
        panic!("scalar-replacement witness");
    };
    let pointer_slot = w
        .slots
        .iter()
        .find(|s| s.alloca == ValueId::new(2))
        .unwrap();
    assert_eq!(pointer_slot.fields[0].carrier, Ty::I32);
    for inst in insts(&out) {
        if let Inst::Cast {
            op: CastOp::PtrToInt,
            src_ty,
            ..
        } = inst
        {
            assert_eq!(src_ty, &Ty::Ptr);
        }
        if let Inst::Cast {
            op: CastOp::IntToPtr,
            dst_ty,
            ..
        } = inst
        {
            assert_eq!(dst_ty, &Ty::Ptr);
        }
    }
    let (_, report) = optimize_module(&m, &MidConfig::wasm32());
    assert_eq!(report.rollback_count(), 0, "{:?}", report.rollbacks);
    assert!(report.tv.samples_compared > 0, "{:?}", report.tv);

    // An address one past the end of its allocation is not stable: a reload
    // may resolve it to a neighbour, so it is not carried as a pointer.
    let past = text.replace(
        "    %5 = ptrtoptr ptr %1 to &i32\n",
        "    %6 = const i32 4\n    %7 = gep inbounds u8, ptr %1, %6\n    %5 = ptrtoptr ptr %7 to &i32\n",
    );
    let m = module(&past);
    let carriers: Vec<Ty> = match sroa(&m, "f") {
        Some((_, PassWitness::Sroa(w))) => w
            .slots
            .iter()
            .flat_map(|s| s.fields.iter().map(|f| f.carrier.clone()))
            .collect(),
        _ => Vec::new(),
    };
    assert!(!carriers.contains(&Ty::Ptr), "{carriers:?}");
}

/// The bridge's field access through a pointer: lanes written through the
/// slot (`insertfield` over a pointer, its result unused) and read through
/// it (`extractfield` over a pointer) or by plain loads.
const THROUGH: &str = "type ty.0 = i32\n\ntype ty.1 = i64\n\nfuncty.0 = (i32, i64) -> (i64)\n\n\
    fn @f(functy.0) {\n\
    bb0(%0: i32, %1: i64):\n\
    \x20   %2 = alloca [ty.1 x 2], align 8\n\
    \x20   %3 = insertfield [ty.1 x 2] %2, 1, %1\n\
    \x20   %20 = const i64 3\n\
    \x20   %21 = mul i64 %1, %20\n\
    \x20   %4 = insertfield [ty.1 x 2] %2, 0, %21\n\
    \x20   %5 = extractfield [ty.1 x 2] %2, 1\n\
    \x20   %6 = const i32 8\n\
    \x20   %7 = gep inbounds u8, ptr %2, %6\n\
    \x20   %8 = load i64, ptr %7\n\
    \x20   %9 = load i64, ptr %2\n\
    \x20   %10 = add i64 %5, %8\n\
    \x20   %11 = add i64 %10, %9\n\
    \x20   ret %11\n\
    }\n";

#[test]
fn scalar_replacement_promotes_fields_written_and_read_through_the_slot() {
    let m = module(THROUGH);
    let (out, witness) = sroa(&m, "f").expect("the slot");
    assert_eq!(witness.rewrite_count(), 5);
    // Each write-through `insertfield` is removed with its unused result.
    assert!(
        !insts(&out)
            .iter()
            .any(|i| matches!(i, Inst::InsertField { .. } | Inst::ExtractField { .. })),
        "{out:#?}"
    );
    let (out, report) = optimize_module(&m, &MidConfig::wasm32());
    assert_eq!(report.rollback_count(), 0, "{:?}", report.rollbacks);
    assert!(report.tv.samples_compared > 0, "{:?}", report.tv);
    assert_eq!(report.allocas_after, 0);
    assert!(
        !insts(func(&out, "f")).iter().any(|i| matches!(
            i,
            Inst::InsertField { .. } | Inst::ExtractField { .. } | Inst::Load { .. }
        )),
        "{:#?}",
        func(&out, "f")
    );

    // Left alone: a lane written with a value of another type (the lane
    // would reinterpret it), and a lane the aggregate does not have.
    for (what, from, to) in [
        (
            "a value of another type",
            "insertfield [ty.1 x 2] %2, 1, %1",
            "insertfield [ty.1 x 2] %2, 1, %0",
        ),
        (
            "no such lane",
            "insertfield [ty.1 x 2] %2, 0, %21",
            "insertfield [ty.1 x 2] %2, 2, %21",
        ),
        // The lane types a write-through's result as the record: an access
        // through it is not one through the slot.
        (
            "a write-through's result used",
            "%9 = load i64, ptr %2",
            "%9 = load i64, ptr %4",
        ),
        // A read-through result read as another type (the bridge's
        // sign-reinterpreting `copy`) would add a validator finding.
        (
            "a read-through result read as another type",
            "%10 = add i64 %5, %8",
            "%30 = copy u64 %5\n    %31 = bitcast u64 %30 to i64\n    %10 = add i64 %31, %8",
        ),
    ] {
        let text = THROUGH.replace(from, to);
        assert_eq!(promoted_slots(&module(&text), "f"), 0, "{what}");
    }
}

/// The bridge's word copies over narrower fields: an enum built in a slot
/// (a `u32` tag, the payload word left unwritten on one arm) and copied out
/// as `i64` words into a second slot, whose words are read back; and a pair
/// of pointers into an array copied as one `i64` word through a slot counted
/// by a constant, then read back as pointers.
const WORDS: &str = "type ty.0 = i64\n\ntype ty.1 = i32\n\nfuncty.0 = (i32, i64) -> (i64)\n\n\
    fn @f(functy.0) {\n\
    bb0(%0: i32, %1: i64):\n\
    \x20   %2 = alloca [ty.0 x 2], align 8\n\
    \x20   %3 = alloca [ty.0 x 2], align 8\n\
    \x20   %4 = const i32 8\n\
    \x20   %5 = const i32 0\n\
    \x20   %6 = icmp slt i32 %0, %5\n\
    \x20   condbr %6, bb1, bb2\n\
    bb1:\n\
    \x20   %7 = const u32 1\n\
    \x20   store u32 %7, ptr %2\n\
    \x20   %8 = gep inbounds u8, ptr %2, %4\n\
    \x20   store i64 %1, ptr %8\n\
    \x20   br bb3\n\
    bb2:\n\
    \x20   %9 = const u32 0\n\
    \x20   store u32 %9, ptr %2\n\
    \x20   br bb3\n\
    bb3:\n\
    \x20   %10 = load i64, ptr %2\n\
    \x20   store i64 %10, ptr %3\n\
    \x20   %11 = load u32, ptr %3\n\
    \x20   %12 = zext u32 %11 to i64\n\
    \x20   %13 = icmp eq u32 %11, %9\n\
    \x20   condbr %13, bb4, bb5\n\
    bb4:\n\
    \x20   ret %12\n\
    bb5:\n\
    \x20   %14 = gep inbounds u8, ptr %2, %4\n\
    \x20   %15 = load i64, ptr %14\n\
    \x20   %16 = add i64 %15, %12\n\
    \x20   ret %16\n\
    }\n\n\
    fn @g(functy.0) {\n\
    bb0(%0: i32, %1: i64):\n\
    \x20   %2 = alloca [ty.1 x 4], align 4\n\
    \x20   store i32 %0, ptr %2\n\
    \x20   %3 = const i32 1\n\
    \x20   %4 = alloca i64, %3, align 8\n\
    \x20   %5 = alloca [ty.1 x 2], align 4\n\
    \x20   %6 = const i32 4\n\
    \x20   %7 = gep inbounds u8, ptr %2, %6\n\
    \x20   store i32 %0, ptr %7\n\
    \x20   %8 = gep inbounds u8, ptr %5, %6\n\
    \x20   %9 = ptrtoptr ptr %2 to *const i32\n\
    \x20   store *const i32 %9, ptr %5\n\
    \x20   %10 = ptrtoptr ptr %7 to *const i32\n\
    \x20   store *const i32 %10, ptr %8\n\
    \x20   %11 = load i64, ptr %5\n\
    \x20   store i64 %11, ptr %4\n\
    \x20   %12 = load *const i32, ptr %4\n\
    \x20   %13 = gep inbounds u8, ptr %4, %6\n\
    \x20   %14 = load *const i32, ptr %13\n\
    \x20   %15 = load i32, ptr %12\n\
    \x20   %16 = load i32, ptr %14\n\
    \x20   %17 = add i32 %15, %16\n\
    \x20   %18 = sext i32 %17 to i64\n\
    \x20   ret %18\n\
    }\n";

#[test]
fn scalar_replacement_carries_word_copies_in_parts() {
    let m = module(WORDS);
    // The enum slot: a `u64` field written in parts (from a zero where no
    // store reaches its high half) and a `u64` payload field.
    let (_, witness) = sroa(&m, "f").expect("the enum slot");
    let PassWitness::Sroa(w) = &witness else {
        panic!("scalar-replacement witness");
    };
    let built = w
        .slots
        .iter()
        .find(|s| s.alloca == ValueId::new(2))
        .unwrap();
    assert_eq!(built.fields[0].carrier, Ty::U64);
    assert!(built.fields[0].init.is_some());
    assert!(built.stores.iter().any(|s| s.merge.is_some()));
    let (out, report) = optimize_module(&m, &MidConfig::wasm32());
    assert_eq!(report.rollback_count(), 0, "{:?}", report.rollbacks);
    assert!(report.tv.samples_compared > 0, "{:?}", report.tv);
    // Every slot goes: algebraic simplification reads the two pointers
    // back out of the word they were copied as, so the array `g` reads
    // through them is no longer observed through it.
    assert_eq!(report.allocas_after, 0, "{out}");
    for name in ["f", "g"] {
        assert!(
            !insts(func(&out, name)).iter().any(|i| matches!(
                i,
                Inst::Load { ty: Ty::I64, .. } | Inst::Store { ty: Ty::I64, .. }
            )),
            "{name}: {:#?}",
            func(&out, name)
        );
    }

    // Left alone: a part stored from a value that may be poison (a load),
    // and overlapping accesses that run past one 8-byte word.
    for (what, from, to) in [
        (
            "a part that may be poison",
            "    %7 = const u32 1\n    store u32 %7, ptr %2\n",
            "    %20 = alloca i32\n    %21 = load u32, ptr %20\n    store u32 %21, ptr %2\n",
        ),
        (
            "overlapping accesses wider than a word",
            "    store i64 %1, ptr %8\n",
            "    %22 = sitofp i64 %1 to f64\n    %23 = const i32 4\n    %24 = gep inbounds u8, ptr %2, %23\n    store f64 %22, ptr %24\n",
        ),
    ] {
        let text = WORDS.replace(from, to);
        let m = module(&text);
        let promoted = match sroa(&m, "f") {
            Some((_, PassWitness::Sroa(w))) => w.slots.iter().any(|s| s.alloca == ValueId::new(2)),
            _ => false,
        };
        assert!(!promoted, "{what}");
    }
}

/// The pass names why each slot it leaves stays (the reasons the remaining
/// `alloca`s were measured by): an escape through a call, an observed
/// address, a variable index, a volatile access, a 16-byte field also read
/// as a word (a 128-bit integer field alone is promoted), a part stored from
/// a value that may be poison, and none for a promotable slot.
#[test]
fn scalar_replacement_names_why_a_slot_stays() {
    let text = "type ty.0 = i32\n\nfuncty.0 = (i32, i32) -> (i32)\n\nfuncty.1 = (ptr) -> ()\n\n\
        fn @f(functy.0) {\n\
        bb0(%0: i32, %1: i32):\n\
        \x20   %2 = alloca i32\n\
        \x20   store i32 %0, ptr %2\n\
        \x20   call @func.1(%2)\n\
        \x20   %3 = alloca i32\n\
        \x20   store i32 %0, ptr %3\n\
        \x20   %4 = ptrtoint ptr %3 to i32\n\
        \x20   %5 = alloca [ty.0 x 4]\n\
        \x20   %6 = gep inbounds i32, ptr %5, %1\n\
        \x20   store i32 %0, ptr %6\n\
        \x20   %7 = alloca i32\n\
        \x20   store i32 %0, ptr %7\n\
        \x20   %8 = volatile load i32, ptr %7\n\
        \x20   %9 = alloca i128\n\
        \x20   %10 = sext i32 %0 to i128\n\
        \x20   store i128 %10, ptr %9\n\
        \x20   %11 = load i64, ptr %9\n\
        \x20   %12 = alloca i64\n\
        \x20   %13 = load i32, ptr %3\n\
        \x20   store i32 %13, ptr %12\n\
        \x20   %14 = load i64, ptr %12\n\
        \x20   %15 = alloca i32\n\
        \x20   store i32 %1, ptr %15\n\
        \x20   %16 = load i32, ptr %15\n\
        \x20   ret %16\n\
        }\n\n\
        fn @g(functy.1) {\n\
        }\n";
    let m = module(text);
    let cx = PassContext {
        module: &m,
        pointer_bits: 32,
    };
    let reasons: Vec<(u32, &str)> = passes::sroa_refusals(&cx, func(&m, "f"))
        .into_iter()
        .map(|(v, why)| (v.index(), why))
        .collect();
    assert_eq!(
        reasons,
        vec![
            (2, "escape_call"),
            (3, "ptrtoint"),
            (5, "variable_index"),
            (7, "volatile"),
            (9, "wide_field"),
            (12, "mixed_width_may_be_poison"),
            (15, "promotable"),
        ]
    );
}

/// A two-field slot stored on one arm of a diamond, then `chain` blocks of
/// gotos laid out against the flow (`bb0 -> bbN+3 -> ... -> bb4 -> bb3`)
/// before the loads.
fn reversed_chain(chain: u32) -> String {
    let top = chain + 3;
    let mut text = format!(
        "type ty.0 = i32\n\nfuncty.0 = (i32, i32) -> (i32)\n\n\
         fn @f(functy.0) {{\n\
         bb0(%0: i32, %1: i32):\n\
         \x20   %2 = alloca [ty.0 x 2], align 4\n\
         \x20   %3 = const i32 4\n\
         \x20   %4 = gep inbounds u8, ptr %2, %3\n\
         \x20   store i32 %0, ptr %2\n\
         \x20   store i32 %1, ptr %4\n\
         \x20   %5 = icmp slt i32 %0, %1\n\
         \x20   condbr %5, bb1, bb2\n\
         bb1:\n\
         \x20   store i32 %1, ptr %2\n\
         \x20   br bb{top}\n\
         bb2:\n\
         \x20   br bb{top}\n\
         bb3:\n\
         \x20   %6 = load i32, ptr %2\n\
         \x20   %7 = load i32, ptr %4\n\
         \x20   %8 = sub i32 %6, %7\n\
         \x20   ret %8\n"
    );
    for b in 4..=top {
        text.push_str(&format!("bb{b}:\n    br bb{}\n", b - 1));
    }
    text.push_str("}\n");
    text
}

/// Block visits of the liveness of scalar replacement on `@f`, which
/// promotes `slots` slots.
fn liveness_visits(m: &Module, slots: usize) -> usize {
    passes::LIVENESS_VISITS.with(|c| c.set(0));
    assert_eq!(promoted_slots(m, "f"), slots);
    passes::LIVENESS_VISITS.with(std::cell::Cell::get)
}

#[test]
fn scalar_replacement_liveness_visits_each_block_once_against_the_layout() {
    // An acyclic CFG takes one visit per block in any layout; a sweep in
    // layout order would take one sweep per chain block here.
    for chain in [1, 64, 400] {
        let m = module(&reversed_chain(chain));
        let blocks = func(&m, "f").blocks.len();
        assert_eq!(liveness_visits(&m, 1), blocks, "chain of {chain}");
    }
    let m = module(&reversed_chain(400));
    let (out, _) = sroa(&m, "f").expect("the slot");
    let top = trust_ir::BlockId::new(403);
    let params: usize = out.blocks.iter().map(|b| b.params.len()).sum::<usize>()
        - func(&m, "f")
            .blocks
            .iter()
            .map(|b| b.params.len())
            .sum::<usize>();
    assert_eq!(params, 1, "only field 0 joins");
    assert_eq!(
        out.blocks
            .iter()
            .find(|b| b.id == top)
            .unwrap()
            .params
            .len(),
        1,
        "at the head of the chain"
    );
    let (_, report) = optimize_module(&m, &MidConfig::wasm32());
    assert_eq!(report.rollback_count(), 0, "{:?}", report.rollbacks);
    assert_eq!((report.allocas_before, report.allocas_after), (1, 0));
    assert!(report.tv.samples_compared > 0, "{:?}", report.tv);
}

#[test]
fn scalar_replacement_liveness_is_bounded_on_a_loop() {
    // Two slots over seven blocks with one loop: at most two visits per block
    // per slot.
    let m = module(JOINS);
    let visits = liveness_visits(&m, 2);
    let blocks = func(&m, "f").blocks.len();
    assert!(
        visits <= 2 * 2 * blocks,
        "{visits} visits over {blocks} blocks"
    );
}

// ---------------------------------------------------------------------------
// Inlining
// ---------------------------------------------------------------------------

/// `init` writes two fields through its out-pointer; `f` reads them back
/// from its own slot.
const OUT_POINTER: &str = "type ty.0 = i32\n\n\
    functy.0 = (ptr, i32) -> ()\n\
    functy.1 = (i32) -> (i32)\n\n\
    fn @init(functy.0) {\n\
    \x20   ; #visibility: hidden\n\
    bb0(%0: ptr, %1: i32):\n\
    \x20   %2 = const i32 4\n\
    \x20   %3 = gep inbounds u8, ptr %0, %2\n\
    \x20   store i32 %1, ptr %0\n\
    \x20   %4 = add i32 %1, %1\n\
    \x20   store i32 %4, ptr %3\n\
    \x20   ret\n\
    }\n\n\
    fn @f(functy.1) {\n\
    bb0(%0: i32):\n\
    \x20   %1 = alloca [ty.0 x 2], align 4\n\
    \x20   call @func.0(%1, %0)\n\
    \x20   %2 = const i32 4\n\
    \x20   %3 = gep inbounds u8, ptr %1, %2\n\
    \x20   %4 = load i32, ptr %3\n\
    \x20   %5 = load i32, ptr %1\n\
    \x20   %6 = sub i32 %4, %5\n\
    \x20   ret %6\n\
    }\n";

fn calls(func: &Function) -> usize {
    insts(func)
        .iter()
        .filter(|i| matches!(i, Inst::Call { .. }))
        .count()
}

fn allocas(func: &Function) -> usize {
    insts(func)
        .iter()
        .filter(|i| matches!(i, Inst::Alloca { .. }))
        .count()
}

fn inline_stats(report: &crate::IrmidReport) -> crate::PassStats {
    report
        .passes
        .iter()
        .find(|p| p.name == "inline")
        .cloned()
        .unwrap_or_default()
}

/// The inliner runs before scalar replacement: once `init` is spliced, the
/// slot it wrote through its out-pointer is reached only by plain accesses,
/// and the pipeline promotes it (the frame empties).
#[test]
fn inlining_an_out_pointer_callee_lets_the_slot_be_promoted() {
    let m = module(OUT_POINTER);
    let (out, report) = optimize_module(&m, &MidConfig::wasm32());
    assert_eq!(report.rollback_count(), 0, "{:?}", report.rollbacks);
    let stats = inline_stats(&report);
    assert_eq!(
        (stats.functions_changed, stats.refinements),
        (1, 1),
        "{stats:?}"
    );
    let f = func(&out, "f");
    assert_eq!(calls(f), 0);
    assert_eq!(allocas(f), 0, "{f:#?}");
    assert!(report.tv.samples_compared > 0, "{:?}", report.tv);
    assert_eq!(report.proof_table.rejected, 0);
    // Without the inliner the slot escapes through the call and stays.
    let config = MidConfig {
        never_inline: ["init".to_string()].into_iter().collect(),
        ..MidConfig::wasm32()
    };
    let (out, report) = optimize_module(&m, &config);
    let f = func(&out, "f");
    assert_eq!(calls(f), 1, "#[inline(never)] is honoured");
    assert_eq!(allocas(f), 1);
    assert_eq!(inline_stats(&report).functions_changed, 0);
}

/// A callee another definition may replace at link time, a recursive one,
/// a cold one and one a proof obligation names stay calls.
#[test]
fn negative_controls_ineligible_callees_stay_calls() {
    let tiny = "functy.0 = (i32, i32) -> (i32)\n\n\
        LINKAGEfn @g(functy.0) {\n\
        ATTRS\
        bb0(%0: i32, %1: i32):\n\
        \x20   %2 = mul i32 %0, %1\n\
        \x20   ret %2\n\
        }\n\n\
        fn @f(functy.0) {\n\
        bb0(%0: i32, %1: i32):\n\
        \x20   %2 = call @func.0(%1, %0)\n\
        \x20   %3 = add i32 %2, %0\n\
        \x20   ret %3\n\
        }\n";
    let plain = module(&tiny.replace("LINKAGE", "").replace("ATTRS", ""));
    let (out, _) = optimize_module(&plain, &MidConfig::wasm32());
    assert_eq!(
        calls(func(&out, "f")),
        0,
        "the plain tiny callee is inlined"
    );
    for linkage in ["weak ", "linkonce ", "linkonce_odr ", "weak_odr "] {
        let m = module(&tiny.replace("LINKAGE", linkage).replace("ATTRS", ""));
        let (out, report) = optimize_module(&m, &MidConfig::wasm32());
        assert_eq!(calls(func(&out, "f")), 1, "{linkage}");
        assert_eq!(inline_stats(&report).rollbacks, 0);
    }
    let cold = module(
        &tiny
            .replace("LINKAGE", "")
            .replace("ATTRS", "\x20   ; #attrs: cold\n"),
    );
    let (out, _) = optimize_module(&cold, &MidConfig::wasm32());
    assert_eq!(calls(func(&out, "f")), 1, "cold");
    let mut obligated = plain.clone();
    obligated.proof_obligations.push(ProofObligation::new(
        trust_ir::value::ProofId::new(0),
        ObligationKind::MemorySafety,
        ProofStatus::Pending,
        "names the callee",
    ));
    obligated.proof_obligations[0].function = Some(FuncId::new(0));
    let (out, _) = optimize_module(&obligated, &MidConfig::wasm32());
    assert_eq!(calls(func(&out, "f")), 1, "a callee an obligation names");
    let recursive = "functy.0 = (i32, i32) -> (i32)\n\n\
        fn @r(functy.0) {\n\
        bb0(%0: i32, %1: i32):\n\
        \x20   %2 = icmp slt i32 %0, %1\n\
        \x20   condbr %2, bb1, bb2\n\
        bb1:\n\
        \x20   %3 = call @func.0(%1, %0)\n\
        \x20   ret %3\n\
        bb2:\n\
        \x20   ret %0\n\
        }\n\n\
        fn @f(functy.0) {\n\
        bb0(%0: i32, %1: i32):\n\
        \x20   %2 = call @func.0(%0, %1)\n\
        \x20   ret %2\n\
        }\n";
    let m = module(recursive);
    let (out, _) = optimize_module(&m, &MidConfig::wasm32());
    assert_eq!(calls(func(&out, "f")), 1, "recursive");
}

/// A callee of `n` chained additions (`n + 1` instructions), exported or
/// hidden, called from `sites` call sites of `f`.
fn sized(n: usize, hidden: bool, sites: usize) -> Module {
    let mut text = String::from("functy.0 = (i32) -> (i32)\n\nfn @big(functy.0) {\n");
    if hidden {
        text.push_str("    ; #visibility: hidden\n");
    }
    text.push_str("bb0(%0: i32):\n");
    for i in 0..n {
        text.push_str(&format!("    %{} = add i32 %{}, %0\n", i + 1, i));
    }
    text.push_str(&format!(
        "    ret %{n}\n}}\n\nfn @f(functy.0) {{\nbb0(%0: i32):\n"
    ));
    let mut last = 0;
    for s in 0..sites {
        text.push_str(&format!("    %{} = call @func.0(%{last})\n", s + 1));
        last = s + 1;
    }
    text.push_str(&format!("    ret %{last}\n}}\n"));
    module(&text)
}

/// The size budget: a small callee is inlined at every site; a larger one,
/// or one with a loop, only when it has a single call site and is not
/// exported (the linker then drops its out-of-line copy); one past the
/// single-site cap never.
#[test]
fn the_size_budget_decides_which_callees_are_inlined() {
    use crate::passes::inline::{SINGLE_SITE_INSTS, SMALL_INSTS};
    let case = |n: usize, hidden: bool, sites: usize| {
        let m = sized(n, hidden, sites);
        let (out, report) = optimize_module(&m, &MidConfig::wasm32());
        assert_eq!(report.rollback_count(), 0, "{:?}", report.rollbacks);
        calls(func(&out, "f"))
    };
    // Small: every site.
    assert_eq!(case(SMALL_INSTS - 1, false, 3), 0);
    // Medium, exported, two sites: stays.
    assert_eq!(case(SMALL_INSTS + 10, false, 2), 2);
    // Medium, hidden, one site: inlined (single site).
    assert_eq!(case(SMALL_INSTS + 10, true, 1), 0);
    // Medium, exported, one site: stays (the out-of-line copy is kept).
    assert_eq!(case(SMALL_INSTS + 10, false, 1), 1);
    // Medium, hidden, two sites: stays.
    assert_eq!(case(SMALL_INSTS + 10, true, 2), 2);
    // Past the single-site cap: stays.
    assert_eq!(case(SINGLE_SITE_INSTS + 10, true, 1), 1);
    // A small callee with a loop: only at a single call site.
    let looping = |hidden: bool, sites: usize| {
        let mut text = String::from("functy.0 = (i32) -> (i32)\n\nfn @spin(functy.0) {\n");
        if hidden {
            text.push_str("    ; #visibility: hidden\n");
        }
        text.push_str(
            "bb0(%0: i32):\n    br bb1(%0)\nbb1(%1: i32):\n    %2 = const i32 1\n    \
             %3 = sub i32 %1, %2\n    %4 = const i32 0\n    %5 = icmp sgt i32 %3, %4\n    \
             condbr %5, bb1(%3), bb2\nbb2:\n    ret %3\n}\n\nfn @f(functy.0) {\nbb0(%0: i32):\n",
        );
        let mut last = 0;
        for s in 0..sites {
            text.push_str(&format!("    %{} = call @func.0(%{last})\n", s + 1));
            last = s + 1;
        }
        text.push_str(&format!("    ret %{last}\n}}\n"));
        let m = module(&text);
        let (out, report) = optimize_module(&m, &MidConfig::wasm32());
        assert_eq!(report.rollback_count(), 0, "{:?}", report.rollbacks);
        calls(func(&out, "f"))
    };
    assert_eq!(looping(true, 2), 2);
    assert_eq!(looping(false, 1), 1);
    assert_eq!(looping(true, 1), 0);
}

/// Callees are visited first: a chain `f -> g -> h` of tiny functions
/// collapses into `f` in one run of the pass.
#[test]
fn a_call_chain_collapses_callee_first() {
    let text = "functy.0 = (i32) -> (i32)\n\n\
        fn @f(functy.0) {\n\
        bb0(%0: i32):\n\
        \x20   %1 = call @func.1(%0)\n\
        \x20   ret %1\n\
        }\n\n\
        fn @g(functy.0) {\n\
        bb0(%0: i32):\n\
        \x20   %1 = call @func.2(%0)\n\
        \x20   %2 = add i32 %1, %0\n\
        \x20   ret %2\n\
        }\n\n\
        fn @h(functy.0) {\n\
        bb0(%0: i32):\n\
        \x20   %1 = mul i32 %0, %0\n\
        \x20   ret %1\n\
        }\n";
    let m = module(text);
    let (out, report) = optimize_module(&m, &MidConfig::wasm32());
    assert_eq!(report.rollback_count(), 0, "{:?}", report.rollbacks);
    assert_eq!(calls(func(&out, "f")), 0, "{:#?}", func(&out, "f"));
    assert_eq!(calls(func(&out, "g")), 0);
    let order = passes::callee_first_order(&m, &[0, 1, 2]);
    assert_eq!(order, vec![2, 1, 0]);
}

/// A callee returning from two blocks is spliced by splitting the call's
/// block, the results joining at the continuation; an allocating callee is
/// not spliced into a loop of the caller (its volatile read keeps the slot
/// through the memory cleanup that runs before the inliner).
#[test]
fn a_multi_block_callee_is_split_in_and_an_allocating_one_stays_out_of_loops() {
    let text = "type ty.0 = i32\n\n\
        functy.0 = (i32, i32) -> (i32)\n\
        functy.1 = (i32) -> (i32)\n\n\
        fn @pick(functy.0) {\n\
        bb0(%0: i32, %1: i32):\n\
        \x20   %2 = icmp slt i32 %0, %1\n\
        \x20   condbr %2, bb1, bb2\n\
        bb1:\n\
        \x20   ret %0\n\
        bb2:\n\
        \x20   ret %1\n\
        }\n\n\
        fn @tmp(functy.1) {\n\
        bb0(%0: i32):\n\
        \x20   %1 = alloca [ty.0 x 1], align 4\n\
        \x20   store i32 %0, ptr %1\n\
        \x20   %2 = volatile load i32, ptr %1\n\
        \x20   ret %2\n\
        }\n\n\
        fn @f(functy.0) {\n\
        bb0(%0: i32, %1: i32):\n\
        \x20   %2 = call @func.0(%0, %1)\n\
        \x20   br bb1(%2)\n\
        bb1(%3: i32):\n\
        \x20   %4 = call @func.1(%3)\n\
        \x20   %5 = const i32 1\n\
        \x20   %6 = sub i32 %4, %5\n\
        \x20   %7 = const i32 0\n\
        \x20   %8 = icmp sgt i32 %6, %7\n\
        \x20   condbr %8, bb1(%6), bb2\n\
        bb2:\n\
        \x20   ret %6\n\
        }\n";
    let m = module(text);
    let cx = PassContext {
        module: &m,
        pointer_bits: 32,
    };
    let inline = passes::Inline::new(Default::default());
    let (out, witness) = inline.run(&cx, func(&m, "f")).expect("pick is inlined");
    let PassWitness::Inline(w) = &witness else {
        panic!("inline witness");
    };
    assert_eq!(w.sites.len(), 1, "tmp allocates and its call is in a loop");
    assert_eq!(w.sites[0].callee, FuncId::new(0));
    assert!(w.sites[0].continuation.is_some());
    assert_eq!(calls(&out), 1);
    trust_cg_verify::trust_ir_mid_tv::check_pass(&m, 32, func(&m, "f"), &out, &witness)
        .expect("the checker accepts the pass's splice");
    let (out, report) = optimize_module(&m, &MidConfig::wasm32());
    assert_eq!(report.rollback_count(), 0, "{:?}", report.rollbacks);
    assert!(report.tv.samples_compared > 0);
    assert_eq!(calls(func(&out, "f")), 1);
}

fn calls_of(func: &Function, callee: u32) -> usize {
    insts(func)
        .iter()
        .filter(|i| matches!(i, Inst::Call { callee: c, .. } if *c == FuncId::new(callee)))
        .count()
}

/// The stack bound covers the callee's own loops: a single-call-site callee
/// that makes a slot inside its loop stays a call (spliced, the loop and its
/// `alloca` would sit on a cycle of the caller, carved per iteration and held
/// until the caller returns), while the same loop over a slot made once in
/// the callee's entry is spliced.
#[test]
fn an_allocating_callee_with_a_slot_in_its_own_loop_stays_a_call() {
    let text = |in_loop: bool| {
        let (entry_slot, loop_slot) = if in_loop {
            ("", "\x20   %2 = alloca [ty.0 x 64], align 4\n")
        } else {
            ("\x20   %2 = alloca [ty.0 x 64], align 4\n", "")
        };
        format!(
            "type ty.0 = i32\n\n\
             functy.0 = (i32) -> (i32)\n\
             functy.1 = (ptr) -> ()\n\n\
             fn @ext(functy.1) {{\n\
             }}\n\n\
             fn @lp(functy.0) {{\n\
             \x20   ; #visibility: hidden\n\
             bb0(%0: i32):\n\
             {entry_slot}\
             \x20   br bb1(%0)\n\
             bb1(%1: i32):\n\
             {loop_slot}\
             \x20   call @func.0(%2)\n\
             \x20   %3 = const i32 1\n\
             \x20   %4 = sub i32 %1, %3\n\
             \x20   %5 = const i32 0\n\
             \x20   %6 = icmp sgt i32 %4, %5\n\
             \x20   condbr %6, bb1(%4), bb2\n\
             bb2:\n\
             \x20   ret %4\n\
             }}\n\n\
             fn @f(functy.0) {{\n\
             bb0(%0: i32):\n\
             \x20   %1 = call @func.1(%0)\n\
             \x20   ret %1\n\
             }}\n"
        )
    };
    for (in_loop, calls) in [(true, 1), (false, 0)] {
        let m = module(&text(in_loop));
        let cx = PassContext {
            module: &m,
            pointer_bits: 32,
        };
        let spliced = passes::Inline::new(Default::default())
            .run(&cx, func(&m, "f"))
            .is_some();
        assert_eq!(spliced, !in_loop, "slot in the callee's loop: {in_loop}");
        let (out, report) = optimize_module(&m, &MidConfig::wasm32());
        assert_eq!(report.rollback_count(), 0, "{:?}", report.rollbacks);
        assert_eq!(
            calls_of(func(&out, "f"), 1),
            calls,
            "slot in the callee's loop: {in_loop}"
        );
    }
}

/// `tmp` (func.0, hidden) with a slot of `words` 32-bit words, then `rest`.
/// Its volatile read keeps the slot through the memory cleanup that runs
/// before the inliner, so the inliner sees an allocating callee.
fn slot_module(words: usize, rest: &str) -> Module {
    module(&format!(
        "type ty.0 = i32\n\n\
         functy.0 = (i32) -> (i32)\n\
         functy.1 = (ptr) -> ()\n\n\
         fn @tmp(functy.0) {{\n\
         \x20   ; #visibility: hidden\n\
         bb0(%0: i32):\n\
         \x20   %1 = alloca [ty.0 x {words}], align 4\n\
         \x20   store i32 %0, ptr %1\n\
         \x20   %2 = volatile load i32, ptr %1\n\
         \x20   ret %2\n\
         }}\n\n{rest}"
    ))
}

/// The stack bound: an allocating callee is not spliced into a caller on a
/// cycle of direct calls (each recursion level would hold its slot), the
/// slots spliced into one caller total at most `MAX_SPLICED_SLOT_BYTES`, and
/// an allocating callee is never "tiny" (an address-taken one, whose own copy
/// stays, is not copied into its callers at all).
#[test]
fn the_stack_bound_keeps_allocating_callees_out_of_recursive_callers_and_big_frames() {
    use crate::passes::inline::MAX_SPLICED_SLOT_BYTES;
    assert_eq!(
        MAX_SPLICED_SLOT_BYTES,
        trust_cg_verify::trust_ir_mid_tv::MAX_SPLICED_SLOT_BYTES,
        "the pass and its checker state the same bound"
    );
    let run = |m: &Module| {
        let (out, report) = optimize_module(m, &MidConfig::wasm32());
        assert_eq!(report.rollback_count(), 0, "{:?}", report.rollbacks);
        calls_of(func(&out, "f"), 0)
    };
    let recursive = "fn @f(functy.0) {\n\
        bb0(%0: i32):\n\
        \x20   %1 = const i32 0\n\
        \x20   %2 = icmp sgt i32 %0, %1\n\
        \x20   condbr %2, bb1, bb2\n\
        bb1:\n\
        \x20   %3 = const i32 1\n\
        \x20   %4 = sub i32 %0, %3\n\
        \x20   %5 = call @func.1(%4)\n\
        \x20   %6 = add i32 %5, %0\n\
        \x20   ret %6\n\
        bb2:\n\
        \x20   %7 = call @func.0(%0)\n\
        \x20   ret %7\n\
        }\n";
    assert_eq!(run(&slot_module(1, recursive)), 1, "recursive caller");
    let sites = |n: usize| {
        let mut text = String::from("fn @f(functy.0) {\nbb0(%0: i32):\n");
        for s in 0..n {
            text.push_str(&format!("    %{} = call @func.0(%{s})\n", s + 1));
        }
        text.push_str(&format!("    ret %{n}\n}}\n"));
        text
    };
    assert_eq!(
        run(&slot_module(1, &sites(1))),
        0,
        "a small slot, no recursion"
    );
    let words = usize::try_from(MAX_SPLICED_SLOT_BYTES / 4).unwrap();
    assert_eq!(run(&slot_module(words, &sites(1))), 0, "exactly the bound");
    assert_eq!(run(&slot_module(words + 1, &sites(1))), 1, "past the bound");
    assert_eq!(
        run(&slot_module(words / 2 + 1, &sites(2))),
        1,
        "the second site would pass the caller's bound"
    );
    // Address-taken: an allocating tiny callee stays a call (it keeps its own
    // copy, and a copy would give each caller a frame), a non-allocating one
    // is still inlined at every site.
    let taker = "fn @h(functy.1) {\n\
        bb0(%0: ptr):\n\
        \x20   %1 = const ptr fndef<func.0>\n\
        \x20   store ptr %1, ptr %0\n\
        \x20   ret\n\
        }\n\n";
    let m = slot_module(1, &format!("{}{taker}", sites(2)));
    assert_eq!(run(&m), 2, "an address-taken allocating callee");
    let plain = module(&format!(
        "type ty.0 = i32\n\n\
         functy.0 = (i32) -> (i32)\n\
         functy.1 = (ptr) -> ()\n\n\
         fn @tmp(functy.0) {{\n\
         \x20   ; #visibility: hidden\n\
         bb0(%0: i32):\n\
         \x20   %1 = mul i32 %0, %0\n\
         \x20   ret %1\n\
         }}\n\n{}{taker}",
        sites(2)
    ));
    assert_eq!(
        run(&plain),
        0,
        "an address-taken tiny callee without a slot"
    );
}

// ---------------------------------------------------------------------------
// Range rules
// ---------------------------------------------------------------------------

fn range_stats(report: &crate::IrmidReport) -> crate::PassStats {
    report
        .passes
        .iter()
        .find(|p| p.name == "range")
        .cloned()
        .unwrap_or_default()
}

/// The bounds check of `t[(x & 63) as usize]` on a 64-entry table, in the
/// bridge's shape: a compare, a branch to the panic arm, and a table read.
const MASKED_INDEX: &str = "type ty.0 = u32\n\n\
    functy.0 = (u32) -> (u32)\n\n\
    fn @f(functy.0) {\n\
    bb0(%0: u32):\n\
    \x20   %1 = const u32 63\n\
    \x20   %2 = and u32 %0, %1\n\
    \x20   %3 = zext u32 %2 to usize\n\
    \x20   %4 = const usize 64\n\
    \x20   %5 = icmp ult usize %3, %4\n\
    \x20   condbr %5, bb1, bb2\n\
    bb1:\n\
    \x20   %6 = const u32 3\n\
    \x20   %7 = mul u32 %2, %6\n\
    \x20   ret %7\n\
    bb2:\n\
    \x20   %8 = const u32 0\n\
    \x20   ret %8\n\
    }\n";

#[test]
fn range_rules_fold_a_masked_bounds_check_and_drop_its_panic_arm() {
    let m = module(MASKED_INDEX);
    let (out, witness) = run_pass(&passes::RangeRules, &m, "f").expect("a decided compare");
    let PassWitness::Range(w) = &witness else {
        panic!("range witness");
    };
    let counts = w.counts();
    assert_eq!(counts.get("icmp"), Some(&1), "{counts:?}");
    assert_eq!(counts.get("condbr"), Some(&1), "{counts:?}");
    assert_eq!(counts.get("removed_block"), Some(&1), "{counts:?}");
    assert_eq!(out.blocks.len(), 2);

    let (out, report) = optimize_module(&m, &MidConfig::wasm32());
    assert_eq!(report.rollback_count(), 0, "{:?}", report.rollbacks);
    let stats = range_stats(&report);
    assert_eq!(stats.functions_changed, 1, "{stats:?}");
    assert_eq!(stats.rules.get("icmp"), Some(&1), "{stats:?}");
    assert_eq!(stats.rules.get("condbr"), Some(&1), "{stats:?}");
    assert!(stats.rules_rolled_back.is_empty(), "{stats:?}");
    let f = func(&out, "f");
    assert!(
        !insts(f)
            .iter()
            .any(|i| matches!(i, Inst::CondBr { .. } | Inst::ICmp { .. })),
        "{f:#?}"
    );
    assert_eq!(f.blocks.len(), 1, "the panic arm is gone, the rest merged");
    assert!(report.tv.samples_compared > 0, "{:?}", report.tv);
    assert_eq!(report.proof_table.rejected, 0);
    let json = report.to_json();
    let range = json["passes"]
        .as_array()
        .unwrap()
        .iter()
        .find(|p| p["name"] == "range")
        .unwrap();
    assert_eq!(range["rules"]["icmp"], 1, "{range}");
    // Passes without rules render as before.
    let dce = json["passes"]
        .as_array()
        .unwrap()
        .iter()
        .find(|p| p["name"] == "dce")
        .unwrap();
    assert!(dce.get("rules").is_none(), "{dce}");
}

#[test]
fn negative_control_an_undecided_compare_is_left_alone() {
    // A 127 mask reaches past the 64-entry table.
    let m = module(&MASKED_INDEX.replace("const u32 63", "const u32 127"));
    assert!(run_pass(&passes::RangeRules, &m, "f").is_none());
    let (out, report) = optimize_module(&m, &MidConfig::wasm32());
    assert_eq!(range_stats(&report).functions_changed, 0);
    assert!(
        insts(func(&out, "f"))
            .iter()
            .any(|i| matches!(i, Inst::CondBr { .. }))
    );
}

/// A saturating add of two bytes in the bridge's shape (`add.overflow` and a
/// clamp `select`), and the compare of the flag the bridge writes for an
/// `assert(!flag)`.
const SATURATING: &str = "functy.0 = (u8, u8) -> (u32)\n\n\
    fn @f(functy.0) {\n\
    bb0(%0: u8, %1: u8):\n\
    \x20   %2 = zext u8 %0 to u32\n\
    \x20   %3 = zext u8 %1 to u32\n\
    \x20   %4, %5 = add.overflow u32 %2, %3\n\
    \x20   %6 = const u32 4294967295\n\
    \x20   %7 = select u32 %5, %6, %4\n\
    \x20   %8 = const bool false\n\
    \x20   %9 = icmp eq bool %5, %8\n\
    \x20   condbr %9, bb1, bb2\n\
    bb1:\n\
    \x20   ret %7\n\
    bb2:\n\
    \x20   %10 = const u32 7\n\
    \x20   ret %10\n\
    }\n";

#[test]
fn range_rules_drop_an_impossible_overflow_and_its_clamp() {
    let m = module(SATURATING);
    let (out, report) = optimize_module(&m, &MidConfig::wasm32());
    assert_eq!(report.rollback_count(), 0, "{:?}", report.rollbacks);
    let stats = range_stats(&report);
    for rule in ["add_overflow", "select", "icmp", "condbr", "removed_block"] {
        assert_eq!(stats.rules.get(rule), Some(&1), "{rule}: {stats:?}");
    }
    let f = func(&out, "f");
    assert_eq!(
        insts(f),
        vec![
            &Inst::Cast {
                op: CastOp::ZExt,
                src_ty: Ty::U8,
                dst_ty: Ty::U32,
                operand: ValueId::new(0),
            },
            &Inst::Cast {
                op: CastOp::ZExt,
                src_ty: Ty::U8,
                dst_ty: Ty::U32,
                operand: ValueId::new(1),
            },
            &Inst::BinOp {
                op: trust_ir::BinOp::Add,
                ty: Ty::U32,
                lhs: ValueId::new(2),
                rhs: ValueId::new(3),
            },
            &Inst::Return {
                values: vec![ValueId::new(4)]
            },
        ],
        "{f:#?}"
    );
}

#[test]
fn negative_control_a_possible_overflow_keeps_its_flag() {
    // Two full u32s may overflow.
    let text = SATURATING.replace("%2 = zext u8 %0 to u32", "%2 = const u32 4294967295");
    let m = module(&text);
    let (out, report) = optimize_module(&m, &MidConfig::wasm32());
    assert!(
        !range_stats(&report).rules.contains_key("add_overflow"),
        "{:?}",
        range_stats(&report)
    );
    assert!(
        insts(func(&out, "f"))
            .iter()
            .any(|i| matches!(i, Inst::Overflow { .. }))
    );
}

/// A pass that applies the compare rule outside its precondition: it folds
/// the first `icmp` to `true` and claims premises that decide it. The checker
/// derives other intervals, refuses the witness, and the manager keeps the
/// snapshot and counts the rule as rolled back.
struct LyingRange;

impl MidPass for LyingRange {
    fn name(&self) -> &'static str {
        "range"
    }

    fn run(&self, _cx: &PassContext<'_>, func: &Function) -> Option<(Function, PassWitness)> {
        use trust_cg_verify::trust_ir_mid_tv::{
            RangePremise, RangeRewrite, RangeRule, RangeWitness,
        };
        let mut out = func.clone();
        for (bi, block) in out.blocks.iter_mut().enumerate() {
            for (ni, node) in block.body.iter_mut().enumerate() {
                if let Inst::ICmp { lhs, rhs, .. } = node.inst {
                    node.inst = Inst::Const {
                        ty: Ty::Bool,
                        value: trust_ir::Constant::Bool(true),
                    };
                    let witness = RangeWitness {
                        rewrites: vec![RangeRewrite {
                            block: func.blocks[bi].id,
                            index: ni,
                            rule: RangeRule::ICmp,
                            premises: vec![
                                RangePremise {
                                    value: lhs,
                                    lo: 0,
                                    hi: 0,
                                },
                                RangePremise {
                                    value: rhs,
                                    lo: 64,
                                    hi: 64,
                                },
                            ],
                        }],
                        removed_blocks: vec![],
                        invariants: Vec::new(),
                    };
                    return Some((out, PassWitness::Range(witness)));
                }
            }
        }
        None
    }
}

#[test]
fn negative_control_a_rule_outside_its_precondition_is_rolled_back() {
    let m = module(&MASKED_INDEX.replace("const u32 63", "const u32 127"));
    let lying = LyingRange;
    let (out, report) = manager::run(&m, &MidConfig::wasm32(), &[&lying]);
    assert_eq!(out, m, "the snapshot stays");
    assert_eq!(report.rollback_count(), 1);
    assert!(
        report.rollbacks[0].reason.starts_with("witness:"),
        "{:?}",
        report.rollbacks
    );
    let stats = range_stats(&report);
    assert_eq!(stats.rules_rolled_back.get("icmp"), Some(&1), "{stats:?}");
    assert!(stats.rules.is_empty(), "{stats:?}");
}

/// A pass that applies one rule to the first instruction of its form with
/// premises that CONTAIN the derived facts (the full range of each overflow
/// operand, `[0, 1]` for a condition), so the witness passes the premise
/// check and the checker's own decision of the rule refuses it.
struct LyingRule(trust_cg_verify::trust_ir_mid_tv::RangeRule);

impl MidPass for LyingRule {
    fn name(&self) -> &'static str {
        "range"
    }

    fn run(&self, _cx: &PassContext<'_>, func: &Function) -> Option<(Function, PassWitness)> {
        use trust_cg_verify::trust_ir_mid_tv::{
            RangePremise, RangeRewrite, RangeRule, RangeWitness,
        };
        use trust_ir::{BinOp, Constant, OverflowOp};
        let premise = |value: ValueId, hi: u128| RangePremise { value, lo: 0, hi };
        let mut out = func.clone();
        for (bi, block) in func.blocks.iter().enumerate() {
            for (ni, node) in block.body.iter().enumerate() {
                let (premises, nodes) = match (self.0, &node.inst) {
                    (
                        RangeRule::Select,
                        Inst::Select {
                            ty, cond, then_val, ..
                        },
                    ) => {
                        let mut n = node.clone();
                        n.inst = Inst::Copy {
                            ty: ty.clone(),
                            operand: *then_val,
                        };
                        (vec![premise(*cond, 1)], vec![n])
                    }
                    (RangeRule::Assert, Inst::Assert { cond, .. }) => {
                        (vec![premise(*cond, 1)], vec![])
                    }
                    (
                        RangeRule::CondBr,
                        Inst::CondBr {
                            cond,
                            then_target,
                            then_args,
                            ..
                        },
                    ) => {
                        let mut n = node.clone();
                        n.inst = Inst::Br {
                            target: *then_target,
                            args: then_args.clone(),
                        };
                        (vec![premise(*cond, 1)], vec![n])
                    }
                    (
                        RangeRule::AddOverflow | RangeRule::MulOverflow,
                        Inst::Overflow {
                            op, ty, lhs, rhs, ..
                        },
                    ) => {
                        let arithmetic = match (self.0, op) {
                            (RangeRule::AddOverflow, OverflowOp::AddOverflow) => BinOp::Add,
                            (RangeRule::MulOverflow, OverflowOp::MulOverflow) => BinOp::Mul,
                            _ => continue,
                        };
                        let full = u128::from(u32::MAX);
                        let mut value = node.clone();
                        value.inst = Inst::BinOp {
                            op: arithmetic,
                            ty: ty.clone(),
                            lhs: *lhs,
                            rhs: *rhs,
                        };
                        value.results = vec![node.results[0]];
                        let mut flag = node.clone();
                        flag.inst = Inst::Const {
                            ty: Ty::Bool,
                            value: Constant::Bool(false),
                        };
                        flag.results = vec![node.results[1]];
                        (
                            vec![premise(*lhs, full), premise(*rhs, full)],
                            vec![value, flag],
                        )
                    }
                    _ => continue,
                };
                out.blocks[bi].body.splice(ni..=ni, nodes);
                let witness = RangeWitness {
                    rewrites: vec![RangeRewrite {
                        block: block.id,
                        index: ni,
                        rule: self.0,
                        premises,
                    }],
                    removed_blocks: vec![],
                    invariants: Vec::new(),
                };
                return Some((out, PassWitness::Range(witness)));
            }
        }
        None
    }
}

/// A `select`, an `assert` and a `condbr` on a compare the mask does not
/// decide (its fact is `[0, 1]`).
const UNDECIDED: &str = "functy.0 = (u32, u32, u32) -> (u32)\n\n\
    fn @f(functy.0) {\n\
    bb0(%0: u32, %1: u32, %2: u32):\n\
    \x20   %3 = const u32 127\n\
    \x20   %4 = and u32 %0, %3\n\
    \x20   %5 = const u32 64\n\
    \x20   %6 = icmp ult u32 %4, %5\n\
    \x20   %7 = select u32 %6, %1, %2\n\
    \x20   assert %6\n\
    \x20   condbr %6, bb1, bb2\n\
    bb1:\n\
    \x20   ret %7\n\
    bb2:\n\
    \x20   ret %1\n\
    }\n";

#[test]
fn negative_control_each_rule_outside_its_precondition_is_rolled_back() {
    use trust_cg_verify::trust_ir_mid_tv::RangeRule;
    // Two full u32s may overflow, as sum and as product.
    let overflowing = SATURATING.replace("%2 = zext u8 %0 to u32", "%2 = const u32 4294967295");
    let multiplying = overflowing.replace("add.overflow", "mul.overflow");
    for (rule, text, why) in [
        (RangeRule::Select, UNDECIDED, "the condition is not decided"),
        (
            RangeRule::Assert,
            UNDECIDED,
            "the condition is not decided true",
        ),
        (RangeRule::CondBr, UNDECIDED, "the condition is not decided"),
        (
            RangeRule::AddOverflow,
            overflowing.as_str(),
            "the premises do not exclude overflow",
        ),
        (
            RangeRule::MulOverflow,
            multiplying.as_str(),
            "the premises do not exclude overflow",
        ),
    ] {
        let m = module(text);
        let lying = LyingRule(rule);
        assert!(
            run_pass(&lying, &m, "f").is_some(),
            "{rule:?} finds its instruction"
        );
        let (out, report) = manager::run(&m, &MidConfig::wasm32(), &[&lying]);
        assert_eq!(out, m, "{rule:?}: the snapshot stays");
        assert_eq!(report.rollback_count(), 1, "{rule:?}");
        let reason = &report.rollbacks[0].reason;
        assert!(
            reason.starts_with("witness:") && reason.ends_with(why),
            "{rule:?}: {reason}"
        );
        let stats = range_stats(&report);
        assert_eq!(
            stats.rules_rolled_back.get(rule.as_str()),
            Some(&1),
            "{rule:?}: {stats:?}"
        );
        assert_eq!(stats.rules_rolled_back.len(), 1, "{rule:?}: {stats:?}");
        assert!(stats.rules.is_empty(), "{rule:?}: {stats:?}");
    }
}

/// Signed compares over non-negative intervals, and facts through `lshr`,
/// `urem`, `sub`, `trunc` and `sext`; every compare folds and the function
/// returns constants.
#[test]
fn range_rules_fold_signed_and_shifted_compares() {
    let text = "functy.0 = (u32, u8) -> (bool, bool, bool, bool)\n\n\
        fn @f(functy.0) {\n\
        bb0(%0: u32, %1: u8):\n\
        \x20   %2 = zext u8 %1 to i32\n\
        \x20   %3 = const i32 -1\n\
        \x20   %4 = icmp sgt i32 %2, %3\n\
        \x20   %5 = const u32 28\n\
        \x20   %6 = lshr u32 %0, %5\n\
        \x20   %7 = const u32 16\n\
        \x20   %8 = icmp ult u32 %6, %7\n\
        \x20   %9 = const u32 7\n\
        \x20   %10 = urem u32 %0, %9\n\
        \x20   %11 = icmp ule u32 %10, %9\n\
        \x20   %12 = trunc u32 %6 to u8\n\
        \x20   %13 = sext u8 %12 to i64\n\
        \x20   %14 = const i64 16\n\
        \x20   %15 = icmp slt i64 %13, %14\n\
        \x20   ret %4, %8, %11, %15\n\
        }\n";
    let m = module(text);
    let (out, report) = optimize_module(&m, &MidConfig::wasm32());
    assert_eq!(report.rollback_count(), 0, "{:?}", report.rollbacks);
    assert_eq!(range_stats(&report).rules.get("icmp"), Some(&4));
    let f = func(&out, "f");
    assert!(
        !insts(f).iter().any(|i| matches!(i, Inst::ICmp { .. })),
        "{f:#?}"
    );
}
