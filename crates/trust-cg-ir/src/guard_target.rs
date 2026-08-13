// trust-cg-ir/guard_target.rs — Per-backend guard descriptor bridging MachIR to the arch-neutral kernel
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Sentinel S2 — the thin per-backend boundary for proof-driven guard elimination.
//!
//! The arch-neutral Certified-Elimination Kernel ([`crate::guard::decide`]) reasons only over
//! [`GuardObligationReceipt`]s. Each backend supplies a small [`GuardTarget`] descriptor that
//! recognizes its proof-only carrier opcodes and lifts a carrier's machine operands into the
//! arch-neutral [`GuardOperandIdentity`]. This is the *entire* per-architecture surface of the
//! soundness-critical path: classification + operand lifting. The decision itself stays in the
//! shared kernel, so adding a backend (x86_64, RISC-V — S5) is ~one descriptor, not a parallel
//! copy of the elimination logic.
//!
//! S2 keeps this descriptor in `trust-cg-ir` so both the optimizer (`trust-cg-opt`) and the
//! codegen observer/verifier (`trust-cg-codegen`) share one implementation rather than each
//! re-deriving the operand mapping. Classification scope in S2 matches S1: the two opcode-only
//! carriers `TrapBoundsCheckExact` (bounds) and `TrapNullIfZero` (null). Div-zero / shift-range /
//! overflow carriers (which need next-instruction shape inspection) are added in a later stage.

use crate::guard::{GuardKind, GuardObligationReceipt, GuardOperandIdentity, GuardOperandRef};
use crate::inst::{AArch64Opcode, MachInst};
use crate::operand::MachOperand;
use crate::riscv_ops::RiscVOpcode;
use crate::x86_64_ops::X86Opcode;

/// A per-backend guard descriptor: recognize carriers and lift their operands. The only
/// arch-specific code on the soundness-critical path.
pub trait GuardTarget {
    /// Recognize a proof-only guard carrier instruction and classify it, or `None` if `inst` is
    /// not a carrier this backend eliminates by proof.
    fn classify_carrier(&self, inst: &MachInst) -> Option<GuardKind>;

    /// Build the operand-bound receipt for a carrier. The obligation id and lineage are left
    /// unbound here; S3 threads the real trust-ir obligation/CleanCic evidence onto the receipt.
    fn build_receipt(&self, kind: GuardKind, inst: &MachInst) -> GuardObligationReceipt {
        GuardObligationReceipt::unbound(kind, self.operand_identity(inst))
    }

    /// Lift a carrier's machine operands into the arch-neutral operand identity.
    fn operand_identity(&self, inst: &MachInst) -> GuardOperandIdentity;
}

/// Lift AArch64 machine operands to arch-neutral guard operand refs. Only register and immediate
/// operands carry proof-relevant identity; block/symbol/stack/memory operands are dropped.
/// Register identity uses the `VReg` id, which regalloc remaps consistently.
pub fn aarch64_guard_operands(operands: &[MachOperand]) -> GuardOperandIdentity {
    let refs = operands
        .iter()
        .filter_map(|op| match op {
            MachOperand::VReg(v) => Some(GuardOperandRef::Reg(v.id)),
            MachOperand::Imm(i) => Some(GuardOperandRef::Imm(*i)),
            _ => None,
        })
        .collect();
    GuardOperandIdentity::new(refs)
}

/// Classify a `TrapOverflowExact` carrier's [`GuardKind`] from its op-tag (operand 2).
///
/// Signed add/sub map to [`GuardKind::SignedOverflow`]; unsigned add/sub map to
/// [`GuardKind::UnsignedOverflow`]. A carrier whose third operand is missing or is
/// not a well-formed op-tag returns `None` — it is then NOT treated as a carrier,
/// so the kernel cannot eliminate a guard whose op-kind it cannot interpret. This
/// is the fail-closed default the soundness obligation requires.
pub fn overflow_carrier_kind(inst: &MachInst) -> Option<GuardKind> {
    let tag = match inst.operands.get(2) {
        Some(MachOperand::Imm(t)) => *t,
        _ => return None,
    };
    let (op, _width) = crate::overflow_tag::unpack_overflow_tag(tag)?;
    match op {
        crate::overflow_tag::OverflowOp::SignedAdd
        | crate::overflow_tag::OverflowOp::SignedSub
        | crate::overflow_tag::OverflowOp::SignedMul => Some(GuardKind::SignedOverflow),
        crate::overflow_tag::OverflowOp::UnsignedAdd
        | crate::overflow_tag::OverflowOp::UnsignedSub
        | crate::overflow_tag::OverflowOp::UnsignedMul => Some(GuardKind::UnsignedOverflow),
    }
}

/// The AArch64 guard descriptor.
#[derive(Debug, Clone, Copy, Default)]
pub struct AArch64GuardTarget;

impl GuardTarget for AArch64GuardTarget {
    fn classify_carrier(&self, inst: &MachInst) -> Option<GuardKind> {
        match inst.opcode {
            AArch64Opcode::TrapBoundsCheckExact => Some(GuardKind::BoundsCheck),
            AArch64Opcode::TrapNullIfZero => Some(GuardKind::NullPtr),
            AArch64Opcode::TrapDivZeroIfZero => Some(GuardKind::DivZero),
            AArch64Opcode::TrapShiftRangeIfOOB => Some(GuardKind::ShiftRange),
            // The overflow carrier's op-tag (operand 2) selects signed vs unsigned
            // overflow. A malformed/missing tag classifies to `None` (NOT a carrier),
            // so the kernel never decides on a tag it cannot interpret — fail-closed.
            AArch64Opcode::TrapOverflowExact => overflow_carrier_kind(inst),
            _ => None,
        }
    }

    fn operand_identity(&self, inst: &MachInst) -> GuardOperandIdentity {
        aarch64_guard_operands(&inst.operands)
    }
}

// ---------------------------------------------------------------------------
// x86-64 guard descriptor (Sentinel S5).
//
// The x86 ISel-output instruction type (`X86ISelInst`) lives in `trust-cg-lower`,
// which depends on `trust-cg-ir` — so this crate cannot take an `&X86ISelInst`
// the way `GuardTarget` takes an `&MachInst`. We therefore split the x86
// descriptor's two soundness-critical responsibilities the same way the
// arch-neutral kernel already factors them:
//
//   * classification is a pure function of the `X86Opcode` (here), and
//   * operand lifting is a pure function of an *already arch-neutral* operand
//     list (`x86_guard_operands`), which the backend produces by mapping
//     `X86ISelOperand::{VReg,Imm}` exactly as `aarch64_guard_operands` maps
//     `MachOperand::{VReg,Imm}`.
//
// The decision itself stays in the shared kernel ([`crate::guard::decide`]). The
// fingerprint is identical to AArch64's because both lift to the same
// [`GuardOperandRef`] sequence `[base, index, Imm(bound)]`, so an x86 carrier and
// an AArch64 carrier over the same operands are interchangeable to the kernel.
// ---------------------------------------------------------------------------

/// Classify an x86-64 proof-only guard carrier opcode, or `None` if `opcode` is
/// not a carrier this backend eliminates by proof. Mirrors
/// [`AArch64GuardTarget::classify_carrier`].
pub fn classify_x86_carrier(opcode: X86Opcode) -> Option<GuardKind> {
    match opcode {
        X86Opcode::TrapBoundsCheckExact => Some(GuardKind::BoundsCheck),
        X86Opcode::TrapNullIfZeroExact => Some(GuardKind::NullPtr),
        X86Opcode::TrapDivZeroExact => Some(GuardKind::DivZero),
        X86Opcode::TrapShiftRangeExact => Some(GuardKind::ShiftRange),
        _ => None,
    }
}

/// Build the arch-neutral operand identity for an x86 carrier from a list of
/// already-lifted guard operand refs (register ids + immediates only, in role
/// order `[base, index, bound]`). The backend lifts `X86ISelOperand::{VReg,Imm}`
/// into this list; everything else (blocks/symbols/memory/cond codes) is dropped,
/// exactly as [`aarch64_guard_operands`] does for `MachOperand`.
pub fn x86_guard_operands(operands: &[GuardOperandRef]) -> GuardOperandIdentity {
    GuardOperandIdentity::new(operands.to_vec())
}

/// The x86-64 guard descriptor.
///
/// Unlike [`AArch64GuardTarget`] (which implements the [`GuardTarget`] trait over
/// `&MachInst`), this descriptor operates on an `X86Opcode` plus a pre-lifted
/// arch-neutral operand list, because `X86ISelInst` is not visible from this
/// crate. The classification + receipt-building logic is otherwise identical.
#[derive(Debug, Clone, Copy, Default)]
pub struct X86GuardTarget;

impl X86GuardTarget {
    /// Classify an x86 carrier opcode (see [`classify_x86_carrier`]).
    pub fn classify_carrier(&self, opcode: X86Opcode) -> Option<GuardKind> {
        classify_x86_carrier(opcode)
    }

    /// Lift an x86 carrier's already-arch-neutral operands into a
    /// [`GuardOperandIdentity`] (see [`x86_guard_operands`]).
    pub fn operand_identity(&self, operands: &[GuardOperandRef]) -> GuardOperandIdentity {
        x86_guard_operands(operands)
    }

    /// Build the operand-bound receipt for an x86 carrier. The obligation id and
    /// lineage are left unbound here; the backend threads the real trust-ir
    /// obligation onto the receipt (mirrors [`GuardTarget::build_receipt`]).
    pub fn build_receipt(
        &self,
        kind: GuardKind,
        operands: &[GuardOperandRef],
    ) -> GuardObligationReceipt {
        GuardObligationReceipt::unbound(kind, self.operand_identity(operands))
    }
}

// ---------------------------------------------------------------------------
// RISC-V guard descriptor (Sentinel S5).
//
// The RISC-V ISel-output instruction type (`RiscVISelInst`) lives in
// `trust-cg-codegen`, which depends on `trust-cg-ir` — and (unlike x86's
// `X86ISelInst`, which lives in `trust-cg-lower`) it is not even reachable from
// the optimizer crate without inverting the dependency edge. We therefore use the
// SAME split the x86 descriptor uses:
//
//   * classification is a pure function of the `RiscVOpcode` (here), and
//   * operand lifting is a pure function of an *already arch-neutral* operand
//     list (`riscv_guard_operands`), which the backend produces by mapping
//     `RiscVISelOperand::{VReg,Imm}` exactly as `aarch64_guard_operands` maps
//     `MachOperand::{VReg,Imm}`.
//
// The decision itself stays in the shared kernel ([`crate::guard::decide`]). The
// fingerprint is identical to AArch64's and x86's because all three lift to the
// same [`GuardOperandRef`] sequence `[base, index, Imm(bound)]`, so the same
// carrier over the same operands is interchangeable to the kernel across all
// backends (no per-arch fingerprint drift).
// ---------------------------------------------------------------------------

/// Classify a RISC-V proof-only guard carrier opcode, or `None` if `opcode` is
/// not a carrier this backend eliminates by proof. Mirrors
/// [`classify_x86_carrier`].
pub fn classify_riscv_carrier(opcode: RiscVOpcode) -> Option<GuardKind> {
    match opcode {
        RiscVOpcode::TrapBoundsCheckExact => Some(GuardKind::BoundsCheck),
        _ => None,
    }
}

/// Build the arch-neutral operand identity for a RISC-V carrier from a list of
/// already-lifted guard operand refs (register ids + immediates only, in role
/// order `[base, index, bound]`). The backend lifts `RiscVISelOperand::{VReg,Imm}`
/// into this list; everything else (blocks/symbols/pregs/stack slots) is dropped,
/// exactly as [`x86_guard_operands`] does for the x86 carrier.
pub fn riscv_guard_operands(operands: &[GuardOperandRef]) -> GuardOperandIdentity {
    GuardOperandIdentity::new(operands.to_vec())
}

/// The RISC-V guard descriptor.
///
/// Like [`X86GuardTarget`] (and unlike [`AArch64GuardTarget`], which implements
/// the [`GuardTarget`] trait over `&MachInst`), this descriptor operates on a
/// `RiscVOpcode` plus a pre-lifted arch-neutral operand list, because
/// `RiscVISelInst` is not visible from this crate.
#[derive(Debug, Clone, Copy, Default)]
pub struct RiscvGuardTarget;

impl RiscvGuardTarget {
    /// Classify a RISC-V carrier opcode (see [`classify_riscv_carrier`]).
    pub fn classify_carrier(&self, opcode: RiscVOpcode) -> Option<GuardKind> {
        classify_riscv_carrier(opcode)
    }

    /// Lift a RISC-V carrier's already-arch-neutral operands into a
    /// [`GuardOperandIdentity`] (see [`riscv_guard_operands`]).
    pub fn operand_identity(&self, operands: &[GuardOperandRef]) -> GuardOperandIdentity {
        riscv_guard_operands(operands)
    }

    /// Build the operand-bound receipt for a RISC-V carrier. The obligation id and
    /// lineage are left unbound here; the backend threads the real trust-ir
    /// obligation onto the receipt (mirrors [`GuardTarget::build_receipt`]).
    pub fn build_receipt(
        &self,
        kind: GuardKind,
        operands: &[GuardOperandRef],
    ) -> GuardObligationReceipt {
        GuardObligationReceipt::unbound(kind, self.operand_identity(operands))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::regs::{RegClass, VReg};

    fn vreg(id: u32) -> MachOperand {
        MachOperand::VReg(VReg::new(id, RegClass::Gpr64))
    }

    #[test]
    fn classifies_bounds_and_null_only() {
        let t = AArch64GuardTarget;
        let bounds = MachInst::new(
            AArch64Opcode::TrapBoundsCheckExact,
            vec![vreg(0), vreg(1), MachOperand::Imm(8)],
        );
        let null = MachInst::new(AArch64Opcode::TrapNullIfZero, vec![vreg(2)]);
        let divzero = MachInst::new(AArch64Opcode::TrapDivZeroIfZero, vec![vreg(3)]);
        let shift = MachInst::new(
            AArch64Opcode::TrapShiftRangeIfOOB,
            vec![vreg(4), MachOperand::Imm(64)],
        );
        let other = MachInst::new(AArch64Opcode::Brk, vec![]);
        // The bare div/shift traps (panic-target shape) are NOT self-contained proof carriers.
        let bare_divzero = MachInst::new(AArch64Opcode::TrapDivZero, vec![]);
        let bare_shift = MachInst::new(AArch64Opcode::TrapShiftRange, vec![]);
        assert_eq!(t.classify_carrier(&bounds), Some(GuardKind::BoundsCheck));
        assert_eq!(t.classify_carrier(&null), Some(GuardKind::NullPtr));
        assert_eq!(t.classify_carrier(&divzero), Some(GuardKind::DivZero));
        assert_eq!(t.classify_carrier(&shift), Some(GuardKind::ShiftRange));
        assert_eq!(t.classify_carrier(&other), None);
        assert_eq!(t.classify_carrier(&bare_divzero), None);
        assert_eq!(t.classify_carrier(&bare_shift), None);
    }

    #[test]
    fn classifies_overflow_carrier_by_op_tag() {
        use crate::overflow_tag::{OverflowOp, pack_overflow_tag};
        let t = AArch64GuardTarget;
        let signed_add = MachInst::new(
            AArch64Opcode::TrapOverflowExact,
            vec![
                vreg(0),
                vreg(1),
                MachOperand::Imm(pack_overflow_tag(OverflowOp::SignedAdd, 64)),
            ],
        );
        let signed_sub = MachInst::new(
            AArch64Opcode::TrapOverflowExact,
            vec![
                vreg(0),
                vreg(1),
                MachOperand::Imm(pack_overflow_tag(OverflowOp::SignedSub, 32)),
            ],
        );
        let unsigned_add = MachInst::new(
            AArch64Opcode::TrapOverflowExact,
            vec![
                vreg(0),
                vreg(1),
                MachOperand::Imm(pack_overflow_tag(OverflowOp::UnsignedAdd, 64)),
            ],
        );
        let unsigned_sub = MachInst::new(
            AArch64Opcode::TrapOverflowExact,
            vec![
                vreg(0),
                vreg(1),
                MachOperand::Imm(pack_overflow_tag(OverflowOp::UnsignedSub, 64)),
            ],
        );
        // Mul carriers (width 64 only): signed -> SignedOverflow, unsigned -> UnsignedOverflow,
        // EXACTLY mirroring the ISel-side `overflow_kind_from_op_tag` so the carrier->obligation
        // fingerprint binding stays symmetric.
        let signed_mul = MachInst::new(
            AArch64Opcode::TrapOverflowExact,
            vec![
                vreg(0),
                vreg(1),
                MachOperand::Imm(pack_overflow_tag(OverflowOp::SignedMul, 64)),
            ],
        );
        let unsigned_mul = MachInst::new(
            AArch64Opcode::TrapOverflowExact,
            vec![
                vreg(0),
                vreg(1),
                MachOperand::Imm(pack_overflow_tag(OverflowOp::UnsignedMul, 64)),
            ],
        );
        // Malformed tag (op code out of range) and missing tag => NOT a carrier (fail-closed).
        let bad_tag = MachInst::new(
            AArch64Opcode::TrapOverflowExact,
            vec![vreg(0), vreg(1), MachOperand::Imm(99999)],
        );
        let no_tag = MachInst::new(AArch64Opcode::TrapOverflowExact, vec![vreg(0), vreg(1)]);

        assert_eq!(
            t.classify_carrier(&signed_add),
            Some(GuardKind::SignedOverflow)
        );
        assert_eq!(
            t.classify_carrier(&signed_sub),
            Some(GuardKind::SignedOverflow)
        );
        assert_eq!(
            t.classify_carrier(&unsigned_add),
            Some(GuardKind::UnsignedOverflow)
        );
        assert_eq!(
            t.classify_carrier(&unsigned_sub),
            Some(GuardKind::UnsignedOverflow)
        );
        assert_eq!(
            t.classify_carrier(&signed_mul),
            Some(GuardKind::SignedOverflow)
        );
        assert_eq!(
            t.classify_carrier(&unsigned_mul),
            Some(GuardKind::UnsignedOverflow)
        );
        assert_eq!(t.classify_carrier(&bad_tag), None);
        assert_eq!(t.classify_carrier(&no_tag), None);
    }

    #[test]
    fn builds_operand_bound_receipt() {
        let t = AArch64GuardTarget;
        let inst = MachInst::new(
            AArch64Opcode::TrapBoundsCheckExact,
            vec![vreg(4), vreg(5), MachOperand::Imm(16)],
        );
        let receipt = t.build_receipt(GuardKind::BoundsCheck, &inst);
        assert_eq!(receipt.kind, GuardKind::BoundsCheck);
        assert_eq!(
            receipt.operand_identity.operands,
            vec![
                GuardOperandRef::Reg(4),
                GuardOperandRef::Reg(5),
                GuardOperandRef::Imm(16)
            ]
        );
        assert!(receipt.operand_identity.is_consistent());
        assert_eq!(receipt.proof_obligation_id, None);
    }

    #[test]
    fn operand_lift_drops_non_identity_operands() {
        let id = aarch64_guard_operands(&[
            vreg(1),
            MachOperand::Imm(2),
            MachOperand::Block(crate::types::BlockId(0)),
            MachOperand::Symbol("s".to_string()),
        ]);
        assert_eq!(
            id.operands,
            vec![GuardOperandRef::Reg(1), GuardOperandRef::Imm(2)]
        );
    }

    // --- x86-64 guard descriptor (Sentinel S5). ---

    #[test]
    fn x86_classifies_proof_only_carriers() {
        let t = X86GuardTarget;
        assert_eq!(
            t.classify_carrier(X86Opcode::TrapBoundsCheckExact),
            Some(GuardKind::BoundsCheck)
        );
        assert_eq!(
            t.classify_carrier(X86Opcode::TrapNullIfZeroExact),
            Some(GuardKind::NullPtr)
        );
        assert_eq!(
            t.classify_carrier(X86Opcode::TrapDivZeroExact),
            Some(GuardKind::DivZero)
        );
        assert_eq!(
            t.classify_carrier(X86Opcode::TrapShiftRangeExact),
            Some(GuardKind::ShiftRange)
        );
        // Real instructions used by the eager expansion are NOT carriers: only the
        // proof-only pseudos are classified, so the gate never deletes a genuine
        // runtime TEST/CMP/Jcc/UD2 check.
        assert_eq!(t.classify_carrier(X86Opcode::CmpRI), None);
        assert_eq!(t.classify_carrier(X86Opcode::TestRR), None);
        assert_eq!(t.classify_carrier(X86Opcode::Ud2), None);
        assert_eq!(t.classify_carrier(X86Opcode::Jcc), None);
    }

    #[test]
    fn x86_builds_operand_bound_receipt() {
        let t = X86GuardTarget;
        let operands = vec![
            GuardOperandRef::Reg(4),
            GuardOperandRef::Reg(5),
            GuardOperandRef::Imm(16),
        ];
        let receipt = t.build_receipt(GuardKind::BoundsCheck, &operands);
        assert_eq!(receipt.kind, GuardKind::BoundsCheck);
        assert_eq!(receipt.operand_identity.operands, operands);
        assert!(receipt.operand_identity.is_consistent());
        assert_eq!(receipt.proof_obligation_id, None);
    }

    /// The x86 and AArch64 descriptors MUST produce the same fingerprint for the
    /// same `[base, index, bound]` operands, so a single shared kernel decides
    /// both backends identically (no per-arch fingerprint drift).
    #[test]
    fn x86_and_aarch64_fingerprints_agree_for_same_operands() {
        let aarch64 = AArch64GuardTarget.operand_identity(&MachInst::new(
            AArch64Opcode::TrapBoundsCheckExact,
            vec![vreg(10), vreg(11), MachOperand::Imm(64)],
        ));
        let x86 = X86GuardTarget.operand_identity(&[
            GuardOperandRef::Reg(10),
            GuardOperandRef::Reg(11),
            GuardOperandRef::Imm(64),
        ]);
        assert_eq!(aarch64.fingerprint, x86.fingerprint);
        assert_eq!(aarch64.operands, x86.operands);
    }

    // --- RISC-V guard descriptor (Sentinel S5). ---

    #[test]
    fn riscv_classifies_bounds_carrier_only() {
        let t = RiscvGuardTarget;
        assert_eq!(
            t.classify_carrier(RiscVOpcode::TrapBoundsCheckExact),
            Some(GuardKind::BoundsCheck)
        );
        assert_eq!(t.classify_carrier(RiscVOpcode::Bgeu), None);
        assert_eq!(t.classify_carrier(RiscVOpcode::Ebreak), None);
        assert_eq!(t.classify_carrier(RiscVOpcode::Addi), None);
        assert_eq!(t.classify_carrier(RiscVOpcode::Nop), None);
    }

    #[test]
    fn riscv_builds_operand_bound_receipt() {
        let t = RiscvGuardTarget;
        let operands = vec![
            GuardOperandRef::Reg(4),
            GuardOperandRef::Reg(5),
            GuardOperandRef::Imm(16),
        ];
        let receipt = t.build_receipt(GuardKind::BoundsCheck, &operands);
        assert_eq!(receipt.kind, GuardKind::BoundsCheck);
        assert_eq!(receipt.operand_identity.operands, operands);
        assert!(receipt.operand_identity.is_consistent());
        assert_eq!(receipt.proof_obligation_id, None);
    }

    /// All three backends MUST produce the same fingerprint for the same
    /// `[base, index, bound]` operands, so a single shared kernel decides all of
    /// them identically (no per-arch fingerprint drift).
    #[test]
    fn riscv_x86_and_aarch64_fingerprints_all_agree() {
        let aarch64 = AArch64GuardTarget.operand_identity(&MachInst::new(
            AArch64Opcode::TrapBoundsCheckExact,
            vec![vreg(10), vreg(11), MachOperand::Imm(64)],
        ));
        let x86 = X86GuardTarget.operand_identity(&[
            GuardOperandRef::Reg(10),
            GuardOperandRef::Reg(11),
            GuardOperandRef::Imm(64),
        ]);
        let riscv = RiscvGuardTarget.operand_identity(&[
            GuardOperandRef::Reg(10),
            GuardOperandRef::Reg(11),
            GuardOperandRef::Imm(64),
        ]);
        assert_eq!(riscv.fingerprint, x86.fingerprint);
        assert_eq!(riscv.fingerprint, aarch64.fingerprint);
        assert_eq!(riscv.operands, aarch64.operands);
    }
}
