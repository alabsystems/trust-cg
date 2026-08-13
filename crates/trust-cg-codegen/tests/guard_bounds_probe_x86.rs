// guard_bounds_probe_x86.rs — soundness pins for the OPT-6a FRONTEND BOUNDS-CHECK PROBE.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! OPT-6a: the rustc bridge lowers a CONSTANT-bound, ay-proven MIR bounds check as a
//! "frontend bounds probe" — an `Inst::ICmp { op: Ult, lhs: index, rhs: <const bound> }`
//! node annotated `ProofAnnotation::InBounds` (+ `ProofRef(obligation)`) — which the
//! adapter turns into a proof-only `GuardBoundsCheck` carrier routed through the
//! default-on Certified-Elimination Kernel.
//!
//! These tests pin the probe channel's REVIEWER-MANDATED soundness rules:
//!
//!   1. NEVER-SYNTHESIZE: a probe WITHOUT a `ProofRef` must keep its guard. The
//!      adapter's `synthesize_discharged_obligation` path (the "InBounds IS the
//!      upstream safety proof" doctrine, earned by the LLVM importer's
//!      `getelementptr inbounds` on array-typed bases) is FORBIDDEN for this
//!      frontend-origin channel: the bridge's `InBounds` is a claim the kernel checks
//!      against solver-discharged evidence, never a self-certified proof.
//!   2. UNDISCHARGED => KEPT: a probe bound to a module obligation whose status is
//!      `Pending` (no real proof) must keep its guard — the runtime check survives
//!      and still traps out-of-bounds.
//!   3. DISCHARGED => ELIMINATED: only a genuinely `Discharged` obligation authorizes
//!      the kernel (plus its independent `recheck_kernel_eliminations`) to delete the
//!      check.
//!   4. SHAPE-DRIFT FAILS CLOSED: a probe whose bound the adapter cannot resolve
//!      (non-constant rhs) or whose compare op is wrong must FAIL THE COMPILE — the
//!      frontend already dropped its eager compare+branch on the promise of a
//!      carrier, so silently skipping would DELETE a bounds check.
//!
//! Observable: a SURVIVING x86 bounds-check carrier expands to `CMP + Jcc(AE) -> UD2`,
//! so the presence of `UD2` (0F 0B) in the emitted object is "guard kept" and its
//! absence "guard eliminated" (these tiny functions emit no other UD2).

use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::target::{Target, TargetSpec};

use trust_ir::proof::{ObligationKind, ProofObligation, ProofStatus};
use trust_ir::value::ProofId;
use trust_ir::{
    Block as TrustIrBlock, BlockId, Constant, FuncId, FuncTy, Function as TrustIrFunction, ICmpOp,
    Inst, InstrNode, Module, ProofAnnotation, Ty, ValueId,
};

const OBLIGATION_ID: u32 = 3;
const BOUND: i128 = 8;

/// How the probe binds (or fails to bind) its module obligation.
enum ProbeBinding {
    /// `InBounds` + `ProofRef(OBLIGATION_ID)`, module obligation with the given status.
    ProofRef(ProofStatus),
    /// `InBounds` only — NO `ProofRef`, NO module obligation. The never-synthesize pin.
    NoProofRef,
}

/// Build `fn <name>(idx: i64) -> i64 { probe: icmp.ult idx, 8 [InBounds, ...]; idx }`.
///
/// The probe is exactly the shape the rustc bridge emits in
/// `try_lower_bounds_check_as_verified_guard`: an `Ult` compare of the index against a
/// plain integer `Inst::Const` bound, annotated `InBounds` (+ optionally `ProofRef`).
fn build_probe_module(name: &str, binding: ProbeBinding) -> Module {
    let mut module = Module::new("guard_bounds_probe_x86");
    let ft = module.add_func_type(FuncTy {
        params: vec![Ty::I64],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let mut func = TrustIrFunction::new(FuncId::new(0), name, ft, BlockId::new(0));

    let idx = ValueId::new(0);
    let bound = ValueId::new(1);
    let probe_result = ValueId::new(2);

    let bound_node = InstrNode::new(Inst::Const {
        ty: Ty::I64,
        value: Constant::Int(BOUND),
    })
    .with_result(bound);

    let mut probe = InstrNode::new(Inst::ICmp {
        op: ICmpOp::Ult,
        ty: Ty::I64,
        lhs: idx,
        rhs: bound,
    })
    .with_result(probe_result)
    .with_proof(ProofAnnotation::InBounds);

    match &binding {
        ProbeBinding::ProofRef(status) => {
            probe = probe.with_proof(ProofAnnotation::ProofRef(ProofId::new(OBLIGATION_ID)));
            module.proof_obligations.push(ProofObligation::new(
                ProofId::new(OBLIGATION_ID),
                ObligationKind::MemorySafety,
                *status,
                "frontend bounds probe obligation",
            ));
        }
        ProbeBinding::NoProofRef => {}
    }

    func.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(idx, Ty::I64)],
        body: vec![
            bound_node,
            probe,
            InstrNode::new(Inst::Return { values: vec![idx] }),
        ],
    }];
    module.add_function(func);
    module
}

fn compile_x86_object(module: &Module) -> Result<Vec<u8>, String> {
    let spec = TargetSpec::parse("x86_64-apple-darwin").expect("parse x86_64-apple-darwin");
    let compiler = Compiler::new_for_target_spec(
        CompilerConfig {
            opt_level: OptLevel::O2,
            target: Target::X86_64,
            ..CompilerConfig::default()
        },
        spec,
    );
    compiler
        .compile(module)
        .map(|artifact| artifact.object_code)
        .map_err(|e| format!("{e:?}"))
}

/// Count `UD2` (`0F 0B`) occurrences in raw object bytes — the surviving-carrier
/// observable (a kept x86 bounds-check carrier expands to a `UD2` trap block).
fn ud2_count(bytes: &[u8]) -> usize {
    bytes.windows(2).filter(|w| w == b"\x0F\x0B").count()
}

/// (3) PUBLIC DISCHARGED STATUS => KEPT: producer-supplied status is report
/// metadata, not replay authority. Until an opaque validator-issued replay
/// capability is wired, the runtime bounds-check trap must remain.
#[test]
fn probe_with_public_discharged_status_keeps_guard() {
    let module = build_probe_module(
        "probe_discharged",
        ProbeBinding::ProofRef(ProofStatus::Discharged),
    );
    let obj = compile_x86_object(&module).expect("discharged probe must compile");
    assert!(
        ud2_count(&obj) >= 1,
        "public Discharged status must not eliminate the runtime bounds-check guard"
    );
}

/// (2) UNDISCHARGED => KEPT (reviewer-mandated refutation test): a bridge-origin
/// probe whose module obligation has NO real proof (status `Pending`) must KEEP its
/// guard — the carrier expands to the real `CMP+Jcc(AE)+UD2` runtime check.
#[test]
fn probe_with_pending_obligation_keeps_guard() {
    let module = build_probe_module(
        "probe_pending",
        ProbeBinding::ProofRef(ProofStatus::Pending),
    );
    let obj = compile_x86_object(&module).expect("pending probe must compile (guard kept)");
    assert!(
        ud2_count(&obj) >= 1,
        "a probe carrier bound to a PENDING (undischarged) obligation must be KEPT \
         and expanded to a real UD2-trapping runtime bounds check"
    );
}

/// (2b) FAILED => KEPT: same as above for a `Failed` obligation (a refuted proof
/// must never authorize an elimination).
#[test]
fn probe_with_failed_obligation_keeps_guard() {
    let module = build_probe_module("probe_failed", ProbeBinding::ProofRef(ProofStatus::Failed));
    let obj = compile_x86_object(&module).expect("failed-status probe must compile (guard kept)");
    assert!(
        ud2_count(&obj) >= 1,
        "a probe carrier bound to a FAILED obligation must be KEPT and expanded to a \
         real UD2-trapping runtime bounds check"
    );
}

/// (1) NEVER-SYNTHESIZE (the mandatory OPT-6a refutation test): a frontend probe
/// carrying `InBounds` but NO `ProofRef` must NOT be discharged through the
/// adapter's `synthesize_discharged_obligation` path — the carrier stays unbound,
/// the kernel keeps it, and the runtime check survives.
///
/// Contrast: the array-typed `ExtractElement`/GEP channel (the LLVM importer's
/// `getelementptr inbounds`) DOES synthesize — that doctrine is earned by producers
/// whose `InBounds` is itself a proof and is pinned by guard_kernel_gate_x86_linkrun.
/// The frontend-origin ICmp probe channel must never inherit it.
#[test]
fn probe_without_proof_ref_is_never_synthesized_discharged() {
    let module = build_probe_module("probe_no_proofref", ProbeBinding::NoProofRef);
    let obj = compile_x86_object(&module).expect("unbound probe must compile (guard kept)");
    assert!(
        ud2_count(&obj) >= 1,
        "NEVER-SYNTHESIZE VIOLATION: a frontend bounds probe with no ProofRef was \
         eliminated — a bridge-origin InBounds claim with no real solver-discharged \
         obligation must KEEP its runtime bounds check"
    );
}

/// Build the RESULT-LESS variant of the probe module (OPT-6b proof-only
/// contract): identical to [`build_probe_module`] except the probe `ICmp`
/// carries NO result value — the frontend declared the compare's value
/// unobservable, so the adapter emits ONLY the `GuardBoundsCheck` carrier
/// (no dead flag-materialization). The CHECK semantics must be unchanged:
/// the carrier still expands to the real runtime check whenever it is kept.
fn build_resultless_probe_module(name: &str, binding: ProbeBinding) -> Module {
    let mut module = Module::new("guard_bounds_probe_x86");
    let ft = module.add_func_type(FuncTy {
        params: vec![Ty::I64],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let mut func = TrustIrFunction::new(FuncId::new(0), name, ft, BlockId::new(0));
    let idx = ValueId::new(0);
    let bound = ValueId::new(1);
    let bound_node = InstrNode::new(Inst::Const {
        ty: Ty::I64,
        value: Constant::Int(BOUND),
    })
    .with_result(bound);
    let mut probe = InstrNode::new(Inst::ICmp {
        op: ICmpOp::Ult,
        ty: Ty::I64,
        lhs: idx,
        rhs: bound,
    })
    .with_proof(ProofAnnotation::InBounds);
    match &binding {
        ProbeBinding::ProofRef(status) => {
            probe = probe.with_proof(ProofAnnotation::ProofRef(ProofId::new(OBLIGATION_ID)));
            module.proof_obligations.push(ProofObligation::new(
                ProofId::new(OBLIGATION_ID),
                ObligationKind::MemorySafety,
                *status,
                "frontend bounds probe obligation (result-less)",
            ));
        }
        ProbeBinding::NoProofRef => {}
    }
    func.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(idx, Ty::I64)],
        body: vec![
            bound_node,
            probe,
            InstrNode::new(Inst::Return { values: vec![idx] }),
        ],
    }];
    module.add_function(func);
    module
}

/// (5) RESULT-LESS + PUBLIC DISCHARGED STATUS => KEPT: OPT-6b's solver report
/// remains non-authoritative without exact replay, so the load-bearing runtime
/// guard is retained even though the carrier has no SSA result.
#[test]
fn resultless_probe_with_public_discharged_status_keeps_guard() {
    let module = build_resultless_probe_module(
        "rl_probe_discharged",
        ProbeBinding::ProofRef(ProofStatus::Discharged),
    );
    let obj = compile_x86_object(&module).expect("result-less discharged probe must compile");
    assert!(
        ud2_count(&obj) >= 1,
        "public Discharged status must not eliminate a result-less runtime guard"
    );
}

/// (5b) RESULT-LESS + UNDISCHARGED => KEPT — the LOAD-BEARING pin for the
/// proof-only contract: skipping the dead compare must NOT skip the CHECK.
/// A kept carrier still expands to the full `CMP+Jcc(AE)+UD2` runtime check.
#[test]
fn resultless_probe_with_pending_obligation_keeps_guard() {
    let module = build_resultless_probe_module(
        "rl_probe_pending",
        ProbeBinding::ProofRef(ProofStatus::Pending),
    );
    let obj = compile_x86_object(&module).expect("result-less pending probe must compile");
    assert!(
        ud2_count(&obj) >= 1,
        "PROOF-ONLY CONTRACT VIOLATION: a result-less probe with a PENDING \
         obligation lost its runtime check — the carrier alone must expand to \
         the real UD2-trapping bounds check"
    );
}

/// (5c) RESULT-LESS + NO PROOFREF => KEPT (never-synthesize, result-less leg).
#[test]
fn resultless_probe_without_proof_ref_keeps_guard() {
    let module = build_resultless_probe_module("rl_probe_no_proofref", ProbeBinding::NoProofRef);
    let obj = compile_x86_object(&module).expect("unbound result-less probe must compile");
    assert!(
        ud2_count(&obj) >= 1,
        "NEVER-SYNTHESIZE VIOLATION (result-less leg): a result-less probe with no \
         ProofRef was eliminated — it must keep its expanded runtime check"
    );
}

/// (4) DYNAMIC BOUNDS ARE A SUPPORTED SHAPE THAT KEEPS ITS CHECK: a probe whose
/// bound operand is NOT a plain integer constant (here: the function's other
/// parameter) was previously rejected outright; the adapter now models it as
/// `BoundsProbeBound::Dyn` (heap slice / `Vec` lengths) so such checks can reach
/// the Certified-Elimination Kernel. The fail-closed contract MOVED, it did not
/// disappear: a dynamic-bound probe must COMPILE and RETAIN its expanded runtime
/// check unless a replayed lattice capability plus kernel authorization elide
/// it — and a production compile (no evidence, no carrier bindings, as here)
/// can never elide it. Silent elision, not compilation, is the failure mode
/// this test now polices.
#[test]
fn probe_with_non_constant_bound_retains_runtime_check() {
    let mut module = Module::new("guard_bounds_probe_x86");
    let ft = module.add_func_type(FuncTy {
        params: vec![Ty::I64, Ty::I64],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let mut func = TrustIrFunction::new(FuncId::new(0), "probe_dyn_bound", ft, BlockId::new(0));
    let idx = ValueId::new(0);
    let dyn_bound = ValueId::new(1);
    let probe_result = ValueId::new(2);
    func.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(idx, Ty::I64), (dyn_bound, Ty::I64)],
        body: vec![
            InstrNode::new(Inst::ICmp {
                op: ICmpOp::Ult,
                ty: Ty::I64,
                lhs: idx,
                rhs: dyn_bound,
            })
            .with_result(probe_result)
            .with_proof(ProofAnnotation::InBounds),
            InstrNode::new(Inst::Return { values: vec![idx] }),
        ],
    }];
    module.add_function(func);

    let obj = compile_x86_object(&module)
        .expect("a dynamic-bound InBounds probe is a supported shape and must compile");
    assert!(
        ud2_count(&obj) >= 1,
        "NEVER-SYNTHESIZE VIOLATION (dynamic-bound leg): a dynamic-bound probe was \
         eliminated in a production compile — without replayed lattice authority the \
         carrier must expand to a runtime check"
    );
}

/// (4b) SHAPE-DRIFT FAILS CLOSED: an `InBounds`-annotated compare with the WRONG op
/// (signed less-than instead of unsigned) must fail the compile.
#[test]
fn probe_with_wrong_compare_op_fails_closed() {
    let mut module = Module::new("guard_bounds_probe_x86");
    let ft = module.add_func_type(FuncTy {
        params: vec![Ty::I64],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let mut func = TrustIrFunction::new(FuncId::new(0), "probe_wrong_op", ft, BlockId::new(0));
    let idx = ValueId::new(0);
    let bound = ValueId::new(1);
    let probe_result = ValueId::new(2);
    func.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(idx, Ty::I64)],
        body: vec![
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(BOUND),
            })
            .with_result(bound),
            InstrNode::new(Inst::ICmp {
                op: ICmpOp::Slt,
                ty: Ty::I64,
                lhs: idx,
                rhs: bound,
            })
            .with_result(probe_result)
            .with_proof(ProofAnnotation::InBounds),
            InstrNode::new(Inst::Return { values: vec![idx] }),
        ],
    }];
    module.add_function(func);

    let result = compile_x86_object(&module);
    assert!(
        result.is_err(),
        "an InBounds-annotated SIGNED compare must FAIL CLOSED (the probe contract is \
         Ult only), got a successful compile"
    );
}

/// A plain `Ult` compare WITHOUT `InBounds` is not a probe: it compiles exactly as
/// before (no carrier, no UD2 from this channel) — the recognizer must not widen.
#[test]
fn plain_icmp_without_inbounds_is_not_a_probe() {
    let mut module = Module::new("guard_bounds_probe_x86");
    let ft = module.add_func_type(FuncTy {
        params: vec![Ty::I64],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let mut func = TrustIrFunction::new(FuncId::new(0), "plain_icmp", ft, BlockId::new(0));
    let idx = ValueId::new(0);
    let bound = ValueId::new(1);
    let cmp_result = ValueId::new(2);
    func.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(idx, Ty::I64)],
        body: vec![
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(BOUND),
            })
            .with_result(bound),
            InstrNode::new(Inst::ICmp {
                op: ICmpOp::Ult,
                ty: Ty::I64,
                lhs: idx,
                rhs: bound,
            })
            .with_result(cmp_result),
            InstrNode::new(Inst::Return { values: vec![idx] }),
        ],
    }];
    module.add_function(func);

    let obj = compile_x86_object(&module).expect("plain icmp must compile");
    assert_eq!(
        ud2_count(&obj),
        0,
        "a plain Ult compare without InBounds must not grow a bounds-check carrier"
    );
}
