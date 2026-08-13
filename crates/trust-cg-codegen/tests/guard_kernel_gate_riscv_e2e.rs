// guard_kernel_gate_riscv_e2e.rs — End-to-end proof of kernel-gated bounds-check elimination on RISC-V
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Sentinel S5 — the RISC-V integration proof that public proof metadata cannot authorize
//! bounds-check elimination through the arch-neutral Certified-Elimination Kernel.
//!
//! ## Scope note (honest)
//!
//! Unlike x86, the RISC-V backend has NO trust_ir → ISel instruction selector and is NOT wired into
//! `Compiler::compile` (it returns an error for `Target::Riscv64`). So this test cannot drive the
//! `X86InstructionSelector`-style path x86 has. Instead it drives every layer that DOES exist
//! end-to-end:
//!
//! 1. Build a trust-ir [`Module`] with `array[index]` (`Inst::ExtractElement`) on an `Array(_, N)`
//!    value annotated with `InBounds` (+ optionally `ProofRef`).
//! 2. Run the REAL adapter (`translate_function`) and assert it emits the proof-only producer opcode
//!    `Opcode::GuardBoundsCheck { bound, obligation }` — the genuine upstream that a RISC-V ISel
//!    would consume — plus the adapter's empty synthesized-authority list.
//! 3. Lower that producer opcode to the RISC-V carrier via the PRODUCTION emit helper
//!    `emit_riscv_bounds_check_carrier` (the exact code a RISC-V ISel would call), which records the
//!    carrier→obligation binding by the kernel fingerprint, exactly as x86 ISel does.
//! 4. Confirm public `Discharged` status and `InBounds` do not populate authoritative evidence, then
//!    run [`RiscVProofGuardElimination`] with the kernel gate enabled.
//! 5. Assert the carrier is kept and compiles to a real `BGEU + EBREAK` runtime trap.
//! 6. Repeat with `Pending`, preserving the explicit fail-closed control.
//!
//! `InBounds`, `ProofRef`, and `ProofStatus` are report/runtime-carrier metadata, not replayed proof
//! authority. A kept carrier expands to a real BGEU+EBREAK check.

use std::collections::HashMap;

use trust_cg_codegen::riscv::pipeline::{
    RiscVISelFunction, RiscVISelInst, RiscVISelOperand, RiscVProofGuardElimination,
    emit_riscv_bounds_check_carrier, riscv_compile_to_bytes,
};
use trust_cg_ir::regs::{RegClass, VReg};
use trust_cg_ir::riscv_ops::RiscVOpcode;
use trust_cg_ir::{GuardKind, GuardOperandRef, RiscvGuardTarget};
use trust_cg_lower::function::Signature;
use trust_cg_lower::instructions::{Block as LirBlock, Opcode as LirOpcode};
use trust_cg_lower::types::Type;
use trust_cg_lower::{Function as LirFunction, ProofContext as LirProofContext};

use trust_ir::proof::{ObligationKind, ProofObligation, ProofStatus};
use trust_ir::value::ProofId;
use trust_ir::{
    Block as TrustIrBlock, BlockId, FuncId, FuncTy, Function as TrustIrFunction, Inst, InstrNode,
    Module, ProofAnnotation, Ty, ValueId,
};

const OBLIGATION_ID: u32 = 7;
const ARRAY_LEN: u64 = 8;
const EBREAK_WORD: u32 = 0x0010_0073;

/// Build a trust-ir module whose single function does `array[index]` on an `Array(I64, ARRAY_LEN)`
/// parameter, carrying `InBounds` (+ `ProofRef(OBLIGATION_ID)` when `with_proof_ref`), with a single
/// module obligation of the given `status`. Mirrors the x86 e2e fixture exactly.
fn build_module(status: ProofStatus, with_proof_ref: bool) -> (Module, TrustIrFunction) {
    let mut module = Module::new("guard_kernel_gate_riscv_e2e");
    let elem_ty = module.add_type(Ty::I64);
    let array_ty = Ty::Array(elem_ty, ARRAY_LEN);
    let ft = module.add_func_type(FuncTy {
        params: vec![array_ty.clone(), Ty::I64],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let mut func =
        TrustIrFunction::new(FuncId::new(0), "proven_extract_riscv", ft, BlockId::new(0));
    let mut node = InstrNode::new(Inst::ExtractElement {
        ty: Ty::I64,
        array: ValueId::new(0),
        index: ValueId::new(1),
    })
    .with_result(ValueId::new(2))
    .with_proof(ProofAnnotation::InBounds);
    if with_proof_ref {
        node = node.with_proof(ProofAnnotation::ProofRef(ProofId::new(OBLIGATION_ID)));
    }
    func.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), array_ty), (ValueId::new(1), Ty::I64)],
        body: vec![
            node,
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(2)],
            }),
        ],
    }];

    if with_proof_ref {
        module.proof_obligations.push(ProofObligation::new(
            ProofId::new(OBLIGATION_ID),
            ObligationKind::MemorySafety,
            status,
            "array index is in bounds",
        ));
    }

    module.add_function(func.clone());
    (module, func)
}

/// The bound + base/index Values + obligation that the REAL adapter attached to the proof-only
/// producer opcode `GuardBoundsCheck`. Fails the test if the adapter did not emit one.
struct ProducerGuard {
    base: u32,
    index: u32,
    bound: i64,
    obligation: Option<u64>,
}

/// Run the real adapter and extract the `GuardBoundsCheck` producer the RISC-V ISel would consume,
/// plus the (necessarily empty) synthesized-authority list. This is the genuine upstream producer
/// — the exact opcode the (future) RISC-V ISel will lower into the carrier via `emit_riscv_*`.
fn lower_to_producer(func: &TrustIrFunction, module: &Module) -> (ProducerGuard, Vec<u64>) {
    let (lir_func, proof_ctx): (LirFunction, LirProofContext) =
        trust_cg_lower::translate_function(func, module).expect("adapter translate");

    let mut found: Option<ProducerGuard> = None;
    for block in lir_func.blocks.values() {
        for inst in &block.instructions {
            if let LirOpcode::GuardBoundsCheck { bound, obligation } = inst.opcode {
                assert_eq!(inst.args.len(), 2, "GuardBoundsCheck carries [base, index]");
                assert!(found.is_none(), "exactly one GuardBoundsCheck expected");
                found = Some(ProducerGuard {
                    base: inst.args[0].0,
                    index: inst.args[1].0,
                    bound: bound as i64,
                    obligation,
                });
            }
        }
    }

    (
        found.expect("adapter must emit a GuardBoundsCheck for an InBounds exact-bound access"),
        proof_ctx.synthesized_discharged.clone(),
    )
}

/// Lower the adapter's producer guard into a RISC-V ISel function with the proof-only carrier, via
/// the PRODUCTION emit helper (the exact code a RISC-V ISel would call). Returns the function with
/// the recorded carrier→obligation bindings, mirroring x86's `lower_to_x86_isel`.
fn build_riscv_isel_with_carrier(guard: &ProducerGuard) -> RiscVISelFunction {
    let sig = Signature {
        params: vec![Type::I64, Type::I64],
        returns: vec![Type::I64],
    };
    let mut func = RiscVISelFunction::new("proven_extract_riscv".to_string(), sig);
    let entry = LirBlock(0);
    func.ensure_block(entry);
    // A 1:1 Value→vreg map is what a trivial RISC-V ISel produces; use the Value ids directly.
    func.next_vreg = guard.base.max(guard.index) + 1;
    emit_riscv_bounds_check_carrier(
        &mut func,
        entry,
        RiscVISelOperand::VReg(VReg::new(guard.base, RegClass::Gpr64)),
        RiscVISelOperand::VReg(VReg::new(guard.index, RegClass::Gpr64)),
        guard.bound,
        guard.obligation,
    );
    // A trailing return so the survivor expansion has a fall-through.
    func.push_inst(
        entry,
        RiscVISelInst::new(
            RiscVOpcode::Jalr,
            vec![
                RiscVISelOperand::PReg(trust_cg_ir::riscv_regs::ZERO),
                RiscVISelOperand::PReg(trust_cg_ir::riscv_regs::RA),
                RiscVISelOperand::Imm(0),
            ],
        ),
    );
    func
}

fn live_riscv_carriers(func: &RiscVISelFunction) -> usize {
    func.block_order
        .iter()
        .filter_map(|b| func.blocks.get(b))
        .flat_map(|b| b.insts.iter())
        .filter(|i: &&RiscVISelInst| i.opcode == RiscVOpcode::TrapBoundsCheckExact)
        .count()
}

/// Build the carrier→obligation map the RISC-V gate consumes: re-derive each carrier's operand
/// fingerprint exactly as the kernel does (`RiscvGuardTarget::operand_identity`) and look the
/// obligation up in the recorded `guard_obligations` (keyed by that same fingerprint).
fn build_carrier_obligation_map(func: &RiscVISelFunction) -> HashMap<u128, (u128, Option<u128>)> {
    let target = RiscvGuardTarget;
    let mut map = HashMap::new();
    for block in func.block_order.iter().filter_map(|b| func.blocks.get(b)) {
        for inst in &block.insts {
            let Some(kind) = target.classify_carrier(inst.opcode) else {
                continue;
            };
            let refs: Vec<GuardOperandRef> = inst
                .operands
                .iter()
                .filter_map(|op| match op {
                    RiscVISelOperand::VReg(v) => Some(GuardOperandRef::Reg(v.id)),
                    RiscVISelOperand::Imm(i) => Some(GuardOperandRef::Imm(*i)),
                    _ => None,
                })
                .collect();
            let identity = target.operand_identity(&refs);
            let fp = trust_cg_ir::fingerprint_for_kind(kind, &identity.operands);
            if let Some(&oid) = func.guard_obligations.get(&fp) {
                map.insert(fp, (oid as u128, None));
            }
        }
    }
    map
}

fn ebreak_count(bytes: &[u8]) -> usize {
    bytes
        .chunks_exact(4)
        .filter(|w| *w == EBREAK_WORD.to_le_bytes())
        .count()
}

#[test]
fn riscv_kernel_gate_keeps_report_only_discharged_bounds_check_end_to_end() {
    let (module, func) = build_module(ProofStatus::Discharged, true);
    let (guard, synthesized) = lower_to_producer(&func, &module);
    assert!(
        synthesized.is_empty(),
        "the carrier has an explicit ProofRef, so no obligation is synthesized"
    );
    assert_eq!(
        guard.obligation,
        Some(OBLIGATION_ID as u64),
        "the adapter must thread the ProofRef obligation onto the producer"
    );

    let mut isel_func = build_riscv_isel_with_carrier(&guard);
    assert_eq!(
        live_riscv_carriers(&isel_func),
        1,
        "production RISC-V emit must produce exactly one carrier"
    );
    assert_eq!(
        isel_func.guard_obligations.len(),
        1,
        "the report-only ProofRef binding must be recorded by fingerprint"
    );

    // Public Discharged status is report-only. It must not mint optimization authority.
    let evidence = trust_cg_lower::guard_evidence::build_discharged_evidence_table(
        &module.proof_obligations,
        &module.proof_certificates,
    );
    assert!(
        evidence.is_empty(),
        "public Discharged/ProofRef metadata must not populate authoritative evidence"
    );

    let carrier_map = build_carrier_obligation_map(&isel_func);
    assert_eq!(
        carrier_map.len(),
        1,
        "fingerprint round-trip: the kernel's fingerprint matches the recorded one"
    );

    let mut pass = RiscVProofGuardElimination::new();
    pass.enable_kernel_gate(evidence, carrier_map);
    let changed = pass.run_on_function(&mut isel_func);

    assert!(
        !changed,
        "report-only proof metadata must not authorize elimination"
    );
    assert_eq!(
        live_riscv_carriers(&isel_func),
        1,
        "the RISC-V runtime carrier must survive without replayed proof authority"
    );
    assert_eq!(pass.stats().guards_eliminated, 0);
    assert_eq!(pass.kernel_eliminations().len(), 0);
    assert!(
        pass.recheck_kernel_eliminations().is_ok(),
        "nothing eliminated, so the independent re-check remains vacuously sound"
    );

    let bytes = riscv_compile_to_bytes(&isel_func).expect("compile retained carrier");
    assert!(
        ebreak_count(&bytes) >= 1,
        "the retained carrier must expand to an EBREAK bounds-check trap"
    );
}

#[test]
fn riscv_kernel_gate_keeps_pending_bounds_check_end_to_end() {
    // NEGATIVE: obligation is Pending, so it is NOT in the evidence table => fail-safe Keep.
    let (module, func) = build_module(ProofStatus::Pending, true);
    let (guard, _synthesized) = lower_to_producer(&func, &module);
    let mut isel_func = build_riscv_isel_with_carrier(&guard);
    assert_eq!(live_riscv_carriers(&isel_func), 1);

    let evidence = trust_cg_lower::guard_evidence::build_discharged_evidence_table(
        &module.proof_obligations,
        &module.proof_certificates,
    );
    assert!(
        evidence.is_empty(),
        "Pending obligation must NOT appear in the evidence table"
    );

    let carrier_map = build_carrier_obligation_map(&isel_func);

    let mut pass = RiscVProofGuardElimination::new();
    pass.enable_kernel_gate(evidence, carrier_map);
    pass.run_on_function(&mut isel_func);

    assert_eq!(
        live_riscv_carriers(&isel_func),
        1,
        "the RISC-V carrier MUST be KEPT: the obligation is not discharged (fail-safe)"
    );
    assert_eq!(pass.stats().guards_eliminated, 0);
    assert_eq!(pass.kernel_eliminations().len(), 0);
    assert!(pass.recheck_kernel_eliminations().is_ok());

    // Full pipeline: the KEPT carrier compiles to a real BGEU + EBREAK runtime trap.
    let bytes = riscv_compile_to_bytes(&isel_func).expect("compile kept");
    assert!(
        ebreak_count(&bytes) >= 1,
        "a kept carrier must expand to an EBREAK bounds-check trap"
    );
}

#[test]
fn riscv_kernel_gate_keeps_inbounds_annotation_without_replayed_authority() {
    // A bare InBounds annotation must retain its runtime carrier. It cannot synthesize a discharge
    // that bypasses exact proof replay.
    let (module, func) = build_module(ProofStatus::Discharged, false);
    let (guard, synthesized) = lower_to_producer(&func, &module);

    assert!(
        synthesized.is_empty(),
        "InBounds must not synthesize proof authority"
    );
    assert_eq!(
        guard.obligation, None,
        "the producer has no authoritative obligation binding"
    );

    let mut isel_func = build_riscv_isel_with_carrier(&guard);
    assert_eq!(live_riscv_carriers(&isel_func), 1);
    assert!(isel_func.guard_obligations.is_empty());

    let evidence = trust_cg_lower::guard_evidence::build_discharged_evidence_table(
        &module.proof_obligations,
        &module.proof_certificates,
    );
    assert!(
        evidence.is_empty(),
        "no replayed proof authority exists in this fixture"
    );

    let carrier_map = build_carrier_obligation_map(&isel_func);
    assert!(carrier_map.is_empty());

    let mut pass = RiscVProofGuardElimination::new();
    pass.enable_kernel_gate(evidence, carrier_map);
    let changed = pass.run_on_function(&mut isel_func);

    assert!(!changed);
    assert_eq!(
        live_riscv_carriers(&isel_func),
        1,
        "the RISC-V InBounds carrier must survive without replayed proof authority"
    );
    assert_eq!(pass.stats().guards_eliminated, 0);
    assert!(pass.recheck_kernel_eliminations().is_ok());
    let bytes = riscv_compile_to_bytes(&isel_func).expect("compile retained carrier");
    assert!(
        ebreak_count(&bytes) >= 1,
        "the runtime carrier must expand to an EBREAK trap"
    );
}

/// Cross-arch invariant: the fingerprint the RISC-V descriptor computes for the carrier is
/// reproducible and is exactly the key the emit helper recorded — a single shared kernel makes the
/// fail-closed decision, with no per-arch drift.
#[test]
fn riscv_carrier_fingerprint_round_trips_through_kernel() {
    let (module, func) = build_module(ProofStatus::Discharged, true);
    let (guard, _) = lower_to_producer(&func, &module);
    let isel_func = build_riscv_isel_with_carrier(&guard);

    let carrier = isel_func
        .block_order
        .iter()
        .filter_map(|b| isel_func.blocks.get(b))
        .flat_map(|b| b.insts.iter())
        .find(|i| i.opcode == RiscVOpcode::TrapBoundsCheckExact)
        .expect("carrier present");

    let refs: Vec<GuardOperandRef> = carrier
        .operands
        .iter()
        .filter_map(|op| match op {
            RiscVISelOperand::VReg(v) => Some(GuardOperandRef::Reg(v.id)),
            RiscVISelOperand::Imm(i) => Some(GuardOperandRef::Imm(*i)),
            _ => None,
        })
        .collect();
    // The binding key folds in the carrier's GuardKind (defense-in-depth, Item B).
    let fp = trust_cg_ir::fingerprint_for_kind(GuardKind::BoundsCheck, &refs);
    assert!(
        isel_func.guard_obligations.contains_key(&fp),
        "kernel-recomputed binding key must match the recorded key"
    );
}
