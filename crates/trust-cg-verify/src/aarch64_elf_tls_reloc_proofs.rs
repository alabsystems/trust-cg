// trust-cg-verify/aarch64_elf_tls_reloc_proofs.rs - SMT proofs for AArch64 ELF
// TLS local-exec (TLSLE) relocation selection/encoding correctness.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Sibling of the Mach-O relocation proof lanes
// (`aarch64_macho_data_reloc_proofs.rs` — PAGE21/PAGEOFF12 data rows,
// `aarch64_macho_tlvp_reloc_proofs.rs` — Darwin TLV descriptor rows). This lane
// proves the AArch64 *ELF* TLS local-exec relocation rows — the
// `R_AARCH64_TLSLE_ADD_TPREL_HI12` on the first ADD and the
// `R_AARCH64_TLSLE_ADD_TPREL_LO12_NC` on the second ADD — reconstruct exactly the
// thread-local variable's runtime address, so their object-relocation inventory
// rows can be promoted on the strict certified-output path.
//
// What the relocations address. On ELF/aarch64 a `#[thread_local]` read in the
// local-exec model lowers to (`isel.rs::select_tls_ref`, `TlsModel::LocalExec`
// with no pre-resolved offset; pipeline.rs skeleton emission):
//
//     MRS  Xd, TPIDR_EL0                      ; Xd = TP (thread pointer)
//     ADD  Xd, Xd, #:tprel_hi12:sym, LSL #12  ; R_AARCH64_TLSLE_ADD_TPREL_HI12
//     ADD  Xd, Xd, #:tprel_lo12_nc:sym        ; R_AARCH64_TLSLE_ADD_TPREL_LO12_NC
//
// The in-object bytes are FIXED skeletons: `ADD Xd, Xd, #0, LSL #12` (sh=1) and
// `ADD Xd, Xd, #0` (sh=0), each carrying imm12 placeholder 0. The static linker
// resolves `X = TPREL(S+A)` — the offset of the symbol from the thread pointer
// (the symbol's offset within the static TLS block, plus the ABI TCB/alignment
// bias, plus the addend `A`) — and patches the two ADD imm12 fields:
//
//   * TLSLE_ADD_TPREL_HI12 writes bits [23:12] of `X` into the first ADD's imm12.
//     Because that ADD carries `LSL #12` (sh=1), at runtime it contributes
//     `((X >> 12) & 0xFFF) << 12` to the TP-holding register — i.e. `X`'s
//     bits [23:12] placed back at [23:12] (`X & 0x00FF_F000`).
//   * TLSLE_ADD_TPREL_LO12_NC writes bits [11:0] of `X` into the second ADD's
//     imm12. That ADD has sh=0, so it contributes `X & 0xFFF` — `X`'s low 12
//     bits at [11:0].
//
// The two disjoint 12-bit slices reconstruct the 24-bit window `X & 0x00FF_FFFF`
// on top of TP. The AArch64 ELF ABI (IHI0056, "TLS relocations") range-checks the
// HI12 relocation `0 <= X < 2^24`, and ISel refuses `off > 0xFF_FFFF`
// (`ISelError::LocalExecTlsRefOffsetTooLarge`), so within every admitted program
// `X < 2^24` and the reconstructed address `TP + (X & 0xFFFFFF)` equals the exact
// intended thread-local address `TP + X`.
//
// Scope / soundness boundary. This lane proves the ELF TLS relocation
// *bit-field placement + value reconstruction* — the part the relocations are
// actually responsible for. The TPREL(S+A) VALUE itself (the symbol's
// TP-relative offset resolution) is the linker's job, exactly as `S + A`
// symbol resolution is the linker's job in the PAGE21/PAGEOFF12 data proofs;
// this lane treats `X = TPREL(S+A)` as the linker-resolved input, modeled as
// `S + A` (S = the symbol's TP-relative TLS-block offset, A = the addend).
//
// INITIAL-EXEC (TLSIE) rows. The backend also emits the GOT-indirect
// initial-exec sequence (`isel.rs::select_tls_ref`, `TlsModel::InitialExec`):
//
//     ADRP Xg, :gottprel:sym                 ; R_AARCH64_TLSIE_ADR_GOTTPREL_PAGE21
//     LDR  Xg, [Xg, #:gottprel_lo12:sym]     ; R_AARCH64_TLSIE_LD64_GOTTPREL_LO12_NC
//     MRS  Xt, TPIDR_EL0
//     ADD  Xd, Xt, Xg
//
// Here `G` is the address of the 8-byte GOT slot the linker creates to hold
// `TPREL(sym)` — the GOT-slot indirection is modeled exactly like the data GOT
// rows (`aarch64_macho_data_reloc_proofs::proof_got_load_page21/pageoff12`,
// GOT entry `G` in place of section symbol `S`): the PAGE21 row proves the
// ADRP reconstructs `page(G+A)` (PC-relative ring identity), and the LD64
// LO12 row proves the ADRP+LDR pair addresses exactly the slot `G+A` under
// the ABI's 8-byte slot alignment (the LDR imm12 is scaled by 8, so the
// relocation writes bits [11:3] — a wrong scale or dropped alignment
// REFUTES). The slot CONTENT (`TPREL(sym)`) is the linker/loader's GOT
// initialization contract, exactly as the dereferenced GOT value is in the
// data-GOT rows; the MRS+ADD completion is plain register arithmetic covered
// by the integer-op proof family.
//
// The GeneralDynamic/LocalDynamic (`__tls_get_addr`/TLSDESC) rows and the
// CHECKED (non-`_NC`) `R_AARCH64_TLSLE_ADD_TPREL_LO12` are NOT emitted by the
// backend (`select_tls_ref` fails closed: GD/LD are unreachable-by-lane —
// trust-cg emits main-executable objects only, no dylib/dlopen lane exists),
// so they stay FAIL-CLOSED — not proven here, not registered in any
// proof-required registry.
//
// Technique mirrors the Mach-O reloc lanes (Alive2-style, PLDI 2021): encode the
// linker-patched + runtime ADD arithmetic as the `aarch64_expr` (the "emitted"
// side) and the intended TP-relative address as the `trust_ir_expr` (the "spec"
// side), then prove equivalence. Each obligation is NON-DEGENERATE (the two sides
// are structurally distinct), so a row with the WRONG shift / wrong bit slice /
// dropped range check REFUTES — exercised by the `*_refutes` negative controls
// and the unit tests.
//
// Reference: "ELF for the Arm 64-bit Architecture (AArch64)" (IHI0056), Table
// "TLS relocations" (`R_AARCH64_TLSLE_ADD_TPREL_HI12` = 0x225,
// `R_AARCH64_TLSLE_ADD_TPREL_LO12_NC` = 0x227); LLVM
// `AArch64ELFObjectWriter.cpp` / `RuntimeDyldELF.cpp`; binutils
// `bfd/elfnn-aarch64.c`.

//! SMT proofs for AArch64 ELF TLS local-exec (TLSLE) relocation
//! selection/encoding correctness.

use crate::lowering_proof::{ProofObligation, TransvalCheckKind};
use crate::smt::SmtExpr;

/// Native pointer width on AArch64.
const W: u32 = 64;

/// Low-12-bit immediate mask `0xFFF` (bits [11:0]).
fn mask_lo12() -> SmtExpr {
    SmtExpr::bv_const(0xFFF, W)
}

/// In-place high-12 mask `0x00FF_F000` (bits [23:12]).
fn mask_hi12_in_place() -> SmtExpr {
    SmtExpr::bv_const(0x00FF_F000, W)
}

/// 24-bit TP-relative window mask `0x00FF_FFFF` (bits [23:0]) — the exact range
/// the HI12 + LO12_NC add pair reconstructs.
fn mask_lo24() -> SmtExpr {
    SmtExpr::bv_const(0x00FF_FFFF, W)
}

/// Shift-by-12 amount for the `LSL #12` on the HI12 add and the bit extraction.
fn shift12() -> SmtExpr {
    SmtExpr::bv_const(12, W)
}

/// `X = TPREL(S + A)` — the linker-resolved thread-pointer-relative offset of the
/// TLS symbol. Modeled as `S + A` (S = the symbol's TP-relative offset within the
/// static TLS block, A = the addend), mirroring the `S + A` target in the
/// PAGE21/PAGEOFF12 data proofs. The value derivation itself is the linker's TPREL
/// resolution; this lane proves the reconstruction of `X` from its relocated
/// bit-fields.
fn tprel(s: &SmtExpr, a: &SmtExpr) -> SmtExpr {
    s.clone().bvadd(a.clone())
}

/// Runtime contribution of the HI12 add: `((X >> 12) & 0xFFF) << 12`.
///
/// The linker writes `bits[23:12] of X` into the ADD's imm12; the `LSL #12`
/// (sh=1) shifts it back into place, so the add contributes `X & 0x00FF_F000`.
fn hi12_contribution(x: &SmtExpr) -> SmtExpr {
    x.clone()
        .bvlshr(shift12())
        .bvand(mask_lo12())
        .bvshl(shift12())
}

/// Runtime contribution of the LO12_NC add: `X & 0xFFF`.
///
/// The linker writes `bits[11:0] of X` into the ADD's imm12; the add has sh=0, so
/// it contributes `X`'s low 12 bits unshifted.
fn lo12_contribution(x: &SmtExpr) -> SmtExpr {
    x.clone().bvand(mask_lo12())
}

// ===========================================================================
// 1. R_AARCH64_TLSLE_ADD_TPREL_HI12 — high-12 bit-field placement (LSL #12)
// ===========================================================================

/// Proof: `R_AARCH64_TLSLE_ADD_TPREL_HI12` on the first ADD (`LSL #12`, sh=1)
/// places `X`'s bits [23:12] back at [23:12] on top of TP.
///
/// Theorem: forall TP, S, A : BV64, X = S + A .
///   (TP + (((X >> 12) & 0xFFF) << 12)) == (TP + (X & 0x00FF_F000))
///
/// The spec side (`trust_ir_expr`) is the intended partial address after the HI12
/// add: TP plus `X`'s high-12 slice in place (`X & 0x00FF_F000`). The emitted side
/// (`aarch64_expr`) is the runtime computation: the linker writes `bits[23:12]`
/// (`(X >> 12) & 0xFFF`) into the imm12 and the ADD's `LSL #12` shifts it up
/// (`<< 12`). The equality needs the bit-slice identity
/// `((X >> 12) & 0xFFF) << 12 == X & 0x00FF_F000`, so it is a genuine equivalence
/// (non-degenerate), NOT `x == x`. An encoder that drops the `LSL #12` (sh=0)
/// leaves the slice at [11:0] — see `proof_tlsle_hi12_missing_lsl12_refutes`.
pub fn proof_tlsle_add_tprel_hi12() -> ProofObligation {
    let tp = SmtExpr::var("TP", W);
    let s = SmtExpr::var("S", W);
    let a = SmtExpr::var("A", W);
    let x = tprel(&s, &a);

    // Spec: TP plus X's bits [23:12] in place.
    let intended = tp.clone().bvadd(x.clone().bvand(mask_hi12_in_place()));
    // Emitted/runtime: TP plus the HI12 add's LSL#12 contribution.
    let reconstructed = tp.bvadd(hi12_contribution(&x));

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "ELF AArch64: R_AARCH64_TLSLE_ADD_TPREL_HI12 ADD(LSL#12) == TP + (TPREL & 0xFFF000)"
            .to_string(),
        trust_ir_expr: intended,
        aarch64_expr: reconstructed,
        inputs: vec![
            ("TP".to_string(), W),
            ("S".to_string(), W),
            ("A".to_string(), W),
        ],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(TransvalCheckKind::InstructionLowering),
    }
}

/// Negative control: a HI12 add that (incorrectly) DROPS the `LSL #12` (sh=0)
/// would leave `X`'s bits [23:12] at [11:0], contributing `(X >> 12) & 0xFFF`
/// instead of `((X >> 12) & 0xFFF) << 12`. That differs from the intended
/// `X & 0x00FF_F000` whenever `X`'s bits [23:12] are nonzero.
///
/// This obligation is intentionally REFUTABLE; the unit tests / AY lane assert it
/// is Invalid (a counterexample exists), demonstrating the positive HI12 proof is
/// a real equivalence and not a tautology.
pub fn proof_tlsle_hi12_missing_lsl12_refutes() -> ProofObligation {
    let tp = SmtExpr::var("TP", W);
    let s = SmtExpr::var("S", W);
    let a = SmtExpr::var("A", W);
    let x = tprel(&s, &a);

    let intended = tp.clone().bvadd(x.clone().bvand(mask_hi12_in_place()));
    // WRONG: sh=0 drops the `<< 12`, leaving the high slice at [11:0].
    let wrong = tp.bvadd(x.clone().bvlshr(shift12()).bvand(mask_lo12()));

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "ELF AArch64: TLSLE_ADD_TPREL_HI12 with dropped LSL#12 must REFUTE".to_string(),
        trust_ir_expr: intended,
        aarch64_expr: wrong,
        inputs: vec![
            ("TP".to_string(), W),
            ("S".to_string(), W),
            ("A".to_string(), W),
        ],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(TransvalCheckKind::InstructionLowering),
    }
}

// ===========================================================================
// 2. R_AARCH64_TLSLE_ADD_TPREL_LO12_NC — full 24-bit TP-relative reconstruction
// ===========================================================================

/// Proof: the `MRS; ADD(hi12,LSL#12); ADD(lo12_nc)` sequence reconstructs the full
/// 24-bit TP-relative window `TP + (X & 0x00FF_FFFF)` — the LO12_NC add completes
/// the HI12 add.
///
/// Theorem: forall TP, S, A : BV64, X = S + A .
///   (TP + (((X >> 12) & 0xFFF) << 12) + (X & 0xFFF)) == (TP + (X & 0x00FF_FFFF))
///
/// The spec side (`trust_ir_expr`) is the intended TP-relative address over the
/// 24-bit window the two adds control: `TP + (X & 0x00FF_FFFF)`. The emitted side
/// (`aarch64_expr`) is TP plus the HI12 contribution (bits [23:12], proven by
/// `proof_tlsle_add_tprel_hi12`) plus the LO12_NC contribution (bits [11:0]). The
/// two slices are disjoint, so their sum is the bit-decomposition identity
/// `(X & 0xFFF000) + (X & 0xFFF) == X & 0xFFFFFF`, a genuine equivalence
/// (non-degenerate). A LO12_NC add that takes the wrong slice REFUTES — see
/// `proof_tlsle_lo12nc_wrong_slice_refutes`.
pub fn proof_tlsle_add_tprel_lo12nc() -> ProofObligation {
    let tp = SmtExpr::var("TP", W);
    let s = SmtExpr::var("S", W);
    let a = SmtExpr::var("A", W);
    let x = tprel(&s, &a);

    // Spec: TP plus the 24-bit TP-relative offset window.
    let intended = tp.clone().bvadd(x.clone().bvand(mask_lo24()));
    // Emitted/runtime: TP + HI12 contribution + LO12_NC contribution.
    let reconstructed = tp.bvadd(hi12_contribution(&x)).bvadd(lo12_contribution(&x));

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "ELF AArch64: R_AARCH64_TLSLE_ADD_TPREL_LO12_NC ADD;ADD == TP + (TPREL & 0xFFFFFF)"
            .to_string(),
        trust_ir_expr: intended,
        aarch64_expr: reconstructed,
        inputs: vec![
            ("TP".to_string(), W),
            ("S".to_string(), W),
            ("A".to_string(), W),
        ],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(TransvalCheckKind::InstructionLowering),
    }
}

/// Negative control: a LO12_NC add that (incorrectly) adds the HIGH slice
/// `(X >> 12) & 0xFFF` instead of the low slice `X & 0xFFF` double-counts bits
/// [23:12] and drops bits [11:0]. The reconstructed `TP + (X & 0xFFF000) +
/// ((X >> 12) & 0xFFF)` differs from the intended `TP + (X & 0xFFFFFF)` in
/// general (whenever `X`'s low 12 bits differ from its bits [23:12]).
///
/// This obligation is intentionally REFUTABLE.
pub fn proof_tlsle_lo12nc_wrong_slice_refutes() -> ProofObligation {
    let tp = SmtExpr::var("TP", W);
    let s = SmtExpr::var("S", W);
    let a = SmtExpr::var("A", W);
    let x = tprel(&s, &a);

    let intended = tp.clone().bvadd(x.clone().bvand(mask_lo24()));
    // WRONG: the low add takes bits [23:12] instead of [11:0].
    let wrong = tp
        .bvadd(hi12_contribution(&x))
        .bvadd(x.clone().bvlshr(shift12()).bvand(mask_lo12()));

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "ELF AArch64: TLSLE_ADD_TPREL_LO12_NC with wrong (high) slice must REFUTE"
            .to_string(),
        trust_ir_expr: intended,
        aarch64_expr: wrong,
        inputs: vec![
            ("TP".to_string(), W),
            ("S".to_string(), W),
            ("A".to_string(), W),
        ],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(TransvalCheckKind::InstructionLowering),
    }
}

// ===========================================================================
// 3. Exact intended address under the ABI range check (0 <= X < 2^24)
// ===========================================================================

/// Proof: under the AArch64 ELF ABI range check `0 <= TPREL(S+A) < 2^24` (enforced
/// by the linker on the HI12 relocation and by ISel's `off > 0xFF_FFFF` reject),
/// the local-exec sequence reconstructs the EXACT thread-local address `TP + X`.
///
/// Theorem: forall TP, S, A : BV64, X = S + A, X < 2^24 .
///   (TP + (((X >> 12) & 0xFFF) << 12) + (X & 0xFFF)) == (TP + X)
///
/// This ties the 24-bit-window reconstruction (`proof_tlsle_add_tprel_lo12nc`) to
/// the exact intended address: because the two adds control bits [23:0] and the
/// ABI guarantees the resolved offset fits there, `X & 0x00FF_FFFF == X`, so the
/// reconstructed address is exactly `TP + X`. The precondition is the ABI's own
/// range check — DROP it and the claim REFUTES on any offset with a bit >= 24 set
/// (see `proof_tlsle_full_tprel_without_range_refutes`), which is why the linker
/// range-checks HI12 and ISel rejects offsets above `0xFF_FFFF`.
pub fn proof_tlsle_full_tprel_address() -> ProofObligation {
    let tp = SmtExpr::var("TP", W);
    let s = SmtExpr::var("S", W);
    let a = SmtExpr::var("A", W);
    let x = tprel(&s, &a);

    // ABI range check: 0 <= X < 2^24.
    let in_range = x.clone().bvult(SmtExpr::bv_const(0x0100_0000, W));

    // Spec: the exact intended thread-local address.
    let intended = tp.clone().bvadd(x.clone());
    // Emitted/runtime: TP + HI12 contribution + LO12_NC contribution.
    let reconstructed = tp.bvadd(hi12_contribution(&x)).bvadd(lo12_contribution(&x));

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "ELF AArch64: TLSLE local-exec MRS;ADD;ADD == TP + TPREL(S+A) under 0<=X<2^24"
            .to_string(),
        trust_ir_expr: intended,
        aarch64_expr: reconstructed,
        inputs: vec![
            ("TP".to_string(), W),
            ("S".to_string(), W),
            ("A".to_string(), W),
        ],
        preconditions: vec![in_range],
        fp_inputs: vec![],
        category: Some(TransvalCheckKind::InstructionLowering),
    }
}

/// Negative control: the exact-address claim WITHOUT the ABI range check is FALSE.
/// The two adds reconstruct only the low 24 bits, so an offset with any bit
/// >= 24 set makes `TP + (X & 0xFFFFFF) != TP + X`. Asserting the sequence yields
/// > `TP + X` for an UNBOUNDED `X` is REFUTABLE — witnessing that the linker's HI12
/// > range check (and ISel's `off > 0xFF_FFFF` reject) is load-bearing.
///
/// This obligation is intentionally REFUTABLE.
pub fn proof_tlsle_full_tprel_without_range_refutes() -> ProofObligation {
    let tp = SmtExpr::var("TP", W);
    let s = SmtExpr::var("S", W);
    let a = SmtExpr::var("A", W);
    let x = tprel(&s, &a);

    let intended = tp.clone().bvadd(x.clone());
    let reconstructed = tp.bvadd(hi12_contribution(&x)).bvadd(lo12_contribution(&x));

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "ELF AArch64: TLSLE exact TP+TPREL WITHOUT range check must REFUTE".to_string(),
        trust_ir_expr: intended,
        aarch64_expr: reconstructed,
        inputs: vec![
            ("TP".to_string(), W),
            ("S".to_string(), W),
            ("A".to_string(), W),
        ],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(TransvalCheckKind::InstructionLowering),
    }
}

// ===========================================================================
// 4. R_AARCH64_TLSIE_ADR_GOTTPREL_PAGE21 — GOT-TPREL slot page (PC-relative)
// ===========================================================================

/// Page base mask `~0xFFF` (clears the low 12 bits).
fn not_mask12() -> SmtExpr {
    SmtExpr::bv_const(!0xFFFu64, W)
}

/// `page(x) = x & ~0xFFF`.
fn page(x: SmtExpr) -> SmtExpr {
    x.bvand(not_mask12())
}

/// 8-byte-scaled low-12 slice mask `0xFF8` (bits [11:3] in place) — the exact
/// window an LD64 (8-byte) unsigned-offset LDR's scaled imm12 controls.
fn mask_lo12_scaled8() -> SmtExpr {
    SmtExpr::bv_const(0xFF8, W)
}

/// Proof: `R_AARCH64_TLSIE_ADR_GOTTPREL_PAGE21` (pcrel) makes the ADRP of the
/// initial-exec sequence reconstruct `page(G+A)` — the page base of the GOT
/// slot holding `TPREL(sym)`.
///
/// Theorem: forall G, A, P : BV64 .
///   (page(P) + (page(G+A) - page(P))) == page(G+A)
///
/// The spec side (`trust_ir_expr`) is the intended ADRP result `page(G+A)`
/// (`G` = the GOT-TPREL slot address the linker materializes, `A` = addend).
/// The emitted side (`aarch64_expr`) is the runtime computation: the linker
/// encodes the page delta `Page(G(GTPREL(S+A))) - Page(P)` (IHI0056 formula)
/// into the ADRP immhi/immlo and the CPU adds `page(P)` at execution. Needs
/// the ring identity `p + (t - p) == t` — a genuine equivalence, structurally
/// the GOT-slot sibling of the data-GOT `proof_got_load_page21` and the
/// PC-relative sibling of the TLSLE rows above. A row that drops the PC-page
/// subtraction REFUTES — see `proof_tlsie_page21_missing_pcrel_refutes`.
pub fn proof_tlsie_adr_gottprel_page21() -> ProofObligation {
    let g = SmtExpr::var("G", W);
    let a = SmtExpr::var("A", W);
    let p = SmtExpr::var("P", W);

    let target = g.bvadd(a);
    let page_target = page(target);
    let page_p = page(p);

    // Spec: ADRP lands on the GOT-TPREL slot's page base.
    let intended = page_target.clone();
    // Emitted/runtime: page(P) + linker-encoded page delta.
    let page_delta = page_target.bvsub(page_p.clone());
    let reconstructed = page_p.bvadd(page_delta);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "ELF AArch64: R_AARCH64_TLSIE_ADR_GOTTPREL_PAGE21 ADRP == page(G+A) (GOT-TPREL page, PC-relative)"
            .to_string(),
        trust_ir_expr: intended,
        aarch64_expr: reconstructed,
        inputs: vec![
            ("G".to_string(), W),
            ("A".to_string(), W),
            ("P".to_string(), W),
        ],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(TransvalCheckKind::InstructionLowering),
    }
}

/// Negative control: a TLSIE PAGE21 row that (incorrectly) drops the PC-page
/// subtraction (absolute instead of PC-relative) makes the ADRP land on
/// `page(P) + page(G+A)` instead of `page(G+A)` — wrong whenever
/// `page(P) != 0`. REFUTABLE, demonstrating the positive proof is a real
/// ring-identity equivalence and not a tautology.
pub fn proof_tlsie_page21_missing_pcrel_refutes() -> ProofObligation {
    let g = SmtExpr::var("G", W);
    let a = SmtExpr::var("A", W);
    let p = SmtExpr::var("P", W);

    let target = g.bvadd(a);
    let page_target = page(target);
    let page_p = page(p);

    let intended = page_target.clone();
    // WRONG: absolute page value with the runtime page(P) still added.
    let wrong = page_p.bvadd(page_target);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "ELF AArch64: TLSIE_ADR_GOTTPREL_PAGE21 without PC-page subtraction must REFUTE"
            .to_string(),
        trust_ir_expr: intended,
        aarch64_expr: wrong,
        inputs: vec![
            ("G".to_string(), W),
            ("A".to_string(), W),
            ("P".to_string(), W),
        ],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(TransvalCheckKind::InstructionLowering),
    }
}

// ===========================================================================
// 5. R_AARCH64_TLSIE_LD64_GOTTPREL_LO12_NC — exact GOT-TPREL slot address
// ===========================================================================

/// Proof: `R_AARCH64_TLSIE_LD64_GOTTPREL_LO12_NC` on the LDR completes the
/// ADRP+LDR pair to address exactly the GOT-TPREL slot `G+A`, under the ABI's
/// 8-byte GOT-slot alignment.
///
/// Theorem: forall G, A : BV64, X = G + A, X & 7 == 0 .
///   (page(X) + (X & 0xFF8)) == X
///
/// The LDR is a 64-bit (LD64) unsigned-offset load, so its imm12 is SCALED BY
/// 8: the linker writes bits [11:3] of `X` (`(X & 0xFF8) >> 3`) into the
/// imm12 field and the CPU computes `base + (imm12 << 3)`, contributing
/// `X & 0xFF8` on top of the ADRP page base `page(X)` (proven by
/// `proof_tlsie_adr_gottprel_page21`). Because the GOT slot is 8-byte aligned
/// (`X & 7 == 0` — the AArch64 ELF ABI's GOT layout, the same alignment
/// contract the LD64 relocation's check enforces), the scaled slice covers
/// all of `X`'s low 12 bits: `page(X) + (X & 0xFF8) == X`. The equality is a
/// genuine bit-decomposition equivalence — NOT X==X. Drop the alignment
/// precondition and the claim REFUTES on any misaligned address (see
/// `proof_tlsie_lo12_without_alignment_refutes`), witnessing that the 8-byte
/// scaling is load-bearing (a byte-granular `0xFFF` model would hide a
/// wrong-scale encoder). The loaded VALUE (`TPREL(sym)`) is the linker/loader
/// GOT-initialization contract, exactly as the dereference is orthogonal in
/// the data-GOT `proof_got_load_pageoff12`.
pub fn proof_tlsie_ld64_gottprel_lo12nc() -> ProofObligation {
    let g = SmtExpr::var("G", W);
    let a = SmtExpr::var("A", W);

    let target = g.bvadd(a);

    // ABI GOT-slot alignment: X & 7 == 0.
    let aligned = target
        .clone()
        .bvand(SmtExpr::bv_const(0x7, W))
        .eq_expr(SmtExpr::bv_const(0, W));

    // Spec: the exact GOT-TPREL slot address.
    let intended = target.clone();
    // Emitted/runtime: ADRP page base + the LD64's 8-scaled imm12 slice.
    let reconstructed = page(target.clone()).bvadd(target.bvand(mask_lo12_scaled8()));

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "ELF AArch64: R_AARCH64_TLSIE_LD64_GOTTPREL_LO12_NC ADRP+LDR == G+A (8-aligned GOT-TPREL slot)"
            .to_string(),
        trust_ir_expr: intended,
        aarch64_expr: reconstructed,
        inputs: vec![("G".to_string(), W), ("A".to_string(), W)],
        preconditions: vec![aligned],
        fp_inputs: vec![],
        category: Some(TransvalCheckKind::InstructionLowering),
    }
}

/// Negative control: the exact-slot-address claim WITHOUT the 8-byte
/// alignment precondition is FALSE — the LD64's scaled imm12 only controls
/// bits [11:3], so a misaligned `X` loses its low 3 bits
/// (`page(X) + (X & 0xFF8) != X` whenever `X & 7 != 0`). REFUTABLE,
/// witnessing that the ABI's 8-byte GOT-slot alignment (and the LD64
/// relocation's scale) is load-bearing.
pub fn proof_tlsie_lo12_without_alignment_refutes() -> ProofObligation {
    let g = SmtExpr::var("G", W);
    let a = SmtExpr::var("A", W);

    let target = g.bvadd(a);

    let intended = target.clone();
    let reconstructed = page(target.clone()).bvadd(target.bvand(mask_lo12_scaled8()));

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "ELF AArch64: TLSIE_LD64_GOTTPREL_LO12_NC without 8-byte slot alignment must REFUTE"
            .to_string(),
        trust_ir_expr: intended,
        aarch64_expr: reconstructed,
        inputs: vec![("G".to_string(), W), ("A".to_string(), W)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(TransvalCheckKind::InstructionLowering),
    }
}

// ===========================================================================
// Registry
// ===========================================================================

/// Collect the AArch64 ELF TLS relocation selection/encoding proofs
/// (local-exec TLSLE + initial-exec TLSIE).
///
/// Returns the 5 positive obligations covering the relocation rows the
/// AArch64 ELF emitter produces for `#[thread_local]` reads:
///
/// Local-exec (`MRS; ADD #:tprel_hi12:; ADD #:tprel_lo12_nc:`):
/// - HI12 (the first ADD's `LSL #12` places `X`'s bits [23:12]),
/// - LO12_NC (the second ADD completes the 24-bit TP-relative reconstruction),
/// - the exact-address composition under the ABI's `0 <= X < 2^24` range check.
///
/// Initial-exec (`ADRP :gottprel:; LDR #:gottprel_lo12:; MRS; ADD`):
/// - ADR_GOTTPREL_PAGE21 (the ADRP reconstructs `page(G+A)`, the GOT-TPREL
///   slot's page — PC-relative ring identity),
/// - LD64_GOTTPREL_LO12_NC (the ADRP+LDR pair addresses exactly the 8-aligned
///   GOT-TPREL slot `G+A`; the LDR imm12 is 8-scaled, bits [11:3]).
///
/// All must verify. The GD/LD (`__tls_get_addr`/TLSDESC) rows and the checked
/// (non-`_NC`) `R_AARCH64_TLSLE_ADD_TPREL_LO12` are NOT emitted by the backend
/// (GD/LD are unreachable-by-lane: trust-cg emits main-executable objects
/// only), so they are intentionally NOT proven here and stay fail-closed.
pub fn aarch64_elf_tls_relocation_proofs() -> Vec<ProofObligation> {
    vec![
        proof_tlsle_add_tprel_hi12(),
        proof_tlsle_add_tprel_lo12nc(),
        proof_tlsle_full_tprel_address(),
        proof_tlsie_adr_gottprel_page21(),
        proof_tlsie_ld64_gottprel_lo12nc(),
    ]
}

/// Negative-control obligations (each is REFUTABLE — a wrong encoding / dropped
/// range check).
///
/// These are NOT registered as proofs; they are used by tests to demonstrate the
/// positive proofs are real equivalences (a malformed row is rejected).
pub fn aarch64_elf_tls_relocation_negative_controls() -> Vec<ProofObligation> {
    vec![
        proof_tlsle_hi12_missing_lsl12_refutes(),
        proof_tlsle_lo12nc_wrong_slice_refutes(),
        proof_tlsle_full_tprel_without_range_refutes(),
        proof_tlsie_page21_missing_pcrel_refutes(),
        proof_tlsie_lo12_without_alignment_refutes(),
    ]
}

// ===========================================================================
// Tests
// ===========================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lowering_proof::verify_by_evaluation;
    use crate::verify::VerificationResult;

    #[test]
    fn all_aarch64_elf_tls_reloc_proofs_verify() {
        for obligation in aarch64_elf_tls_relocation_proofs() {
            let result = verify_by_evaluation(&obligation);
            assert!(
                matches!(result, VerificationResult::Valid),
                "AArch64 ELF TLSLE relocation proof '{}' failed: {:?}",
                obligation.name,
                result
            );
        }
    }

    #[test]
    fn all_aarch64_elf_tls_reloc_negative_controls_refute() {
        for obligation in aarch64_elf_tls_relocation_negative_controls() {
            let result = verify_by_evaluation(&obligation);
            assert!(
                matches!(result, VerificationResult::Invalid { .. }),
                "AArch64 ELF TLSLE relocation NEGATIVE control '{}' should be Invalid \
                 (a wrong encoding must refute), got: {:?}",
                obligation.name,
                result
            );
        }
    }

    #[test]
    fn aarch64_elf_tls_reloc_proofs_are_non_degenerate() {
        for obligation in aarch64_elf_tls_relocation_proofs() {
            assert!(
                obligation.is_genuinely_proven(),
                "AArch64 ELF TLSLE relocation proof '{}' is DEGENERATE (X==X); it proves nothing",
                obligation.name
            );
        }
    }

    #[test]
    fn aarch64_elf_tls_reloc_proof_count_and_names_unique() {
        let proofs = aarch64_elf_tls_relocation_proofs();
        assert_eq!(
            proofs.len(),
            5,
            "expected 3 ELF TLSLE + 2 ELF TLSIE relocation proofs"
        );
        let mut names: Vec<&str> = proofs.iter().map(|p| p.name.as_str()).collect();
        names.sort();
        let before = names.len();
        names.dedup();
        assert_eq!(before, names.len(), "duplicate ELF TLS reloc proof names");
    }

    /// The function-verifier credits `LdrGottprel` via a lowercase substring
    /// query against the LD64 proof name; pin the containment so a proof
    /// rename cannot silently orphan the opcode's coverage credit.
    #[test]
    fn tlsie_ld64_proof_name_matches_function_verifier_query() {
        let name = proof_tlsie_ld64_gottprel_lo12nc().name.to_lowercase();
        assert!(
            name.contains("tlsie_ld64_gottprel_lo12_nc adrp+ldr == g+a"),
            "TLSIE LD64 proof name no longer contains the function-verifier query: {name}"
        );
    }
}
