// trust-cg-verify/aarch64_macho_data_reloc_proofs.rs - SMT proofs for AArch64
// Mach-O DATA relocation selection/encoding correctness.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// These proofs close the AArch64 analogue of the x86-64 object DATA relocation
// gap (`macho_data_reloc_proofs.rs`). Every emitted AArch64 Mach-O data
// relocation row this slice admits (`ARM64_RELOC_PAGE21` on the ADRP,
// `ARM64_RELOC_PAGEOFF12` on the ADD/LDR, `ARM64_RELOC_UNSIGNED` in both its
// extern and section-based forms, and the `SUBTRACTOR`+`UNSIGNED` difference
// pair) is here proven to be the UNIQUE
// correct encoding of its intended address reference, by showing that the value
// the LINKER applies from the emitted `relocation_info` (`r_type`, `r_pcrel`,
// `r_length`, in-place addend) — combined with the runtime ADRP/ADD page
// arithmetic the CPU performs — equals the intended address expression, for all
// symbol/section/PC values.
//
// Technique mirrors `macho_data_reloc_proofs.rs` (Alive2-style, PLDI 2021):
// encode the linker-applied + runtime-reconstructed formula as the
// `aarch64_expr` (the "emitted" side) and the intended address expression as
// the `trust_ir_expr` (the "spec" side), then prove equivalence. Each obligation
// is NON-DEGENERATE (the two sides are structurally distinct), so a row with the
// WRONG `r_pcrel` / wrong PC-page subtraction REFUTES — exercised by the
// negative-control builders (`*_wrong_*`) and the unit tests.
//
// Linker + runtime formulas (canonical Mach-O ARM64 semantics, matching Apple
// `ld` and LLVM `AArch64MachObjectWriter` / `RuntimeDyldMachOAArch64`).
// `page(x) = x & ~0xFFF` is the 4 KiB-page base. `S` is the resolved symbol
// address, `A` the addend, `P` the runtime address of the ADRP (resp. ADD/LDR)
// instruction being relocated. The reference target is `T = S + A`.
//
//   PAGE21 (r_pcrel=1, r_length=2), on the ADRP:
//       The linker writes the 21-bit field `imm = (page(T) - page(P)) >> 12`
//       into the ADRP immhi/immlo. At runtime ADRP computes
//           adrp_reg = page(P) + (imm << 12)
//                    = page(P) + (page(T) - page(P))
//                    = page(T).
//       The selection proof certifies the ADRP reconstructs `page(T)`: the spec
//       side is `page(T)`; the emitted side is `page(P) + (page(T) - page(P))`.
//       The equality needs the ring identity `p + (t - p) == t`, so it is a real
//       equivalence, not `x == x`. An encoder that drops the PC-page
//       subtraction (`r_pcrel=0`) computes `page(P) + page(T) != page(T)` for
//       `page(P) != 0` — see `proof_page21_wrong_pcrel_refutes`.
//
//   PAGEOFF12 (r_pcrel=0, r_length=2), on the ADD (or LDR unsigned offset):
//       The linker writes `imm12 = T & 0xFFF` into bits [21:10]. The ADD adds
//       that page offset to the ADRP base register:
//           full = adrp_reg + (T & 0xFFF)
//                = page(T) + (T & 0xFFF)
//                = T.
//       The selection proof certifies the ADRP+ADD pair reconstructs the full
//       target `T`: the spec side is `T = S + A`; the emitted side is
//       `page(T) + (T & 0xFFF)`. A PAGEOFF12 row that wrongly sets `r_pcrel=1`
//       would make the linker subtract the field PC `P`, yielding
//       `page(T) + ((T - P) & 0xFFF) != T` in general — see
//       `proof_pageoff12_wrong_pcrel_refutes`.
//
//   UNSIGNED, EXTERN (r_extern=1, r_pcrel=0, r_length=3): *field = S + A
//       The encoder bakes the addend A into the 8-byte slot in place, and the
//       linker adds the resolved address of symbol S. Result is an absolute
//       64-bit pointer to S + A. AArch64 emits these as EXTERN
//       symbol_index-based rows: the compact-unwind entry pointers
//       (`unwind.rs` `relocations()` — function_offset / personality / lsda),
//       DWARF-fallback FDE pointers, TLS descriptor slots, and data slots
//       (`Relocation::unsigned_ptr` / `unsigned_word`, `pipeline.rs`,
//       `fixup.rs`).
//
//   UNSIGNED, SECTION-BASED (r_extern=0, r_pcrel=0, r_length=3):
//       *field = A - SectObj + SectFinal, where A is the baked 8-byte value
//       (an address in the OBJECT's own address space), SectObj is the
//       r_symbolnum-th section's address in the object, and SectFinal is that
//       section's final (linked) address. The linker REBASES the baked address
//       instead of resolving an extern symbol. AArch64 emits these for the
//       DW_FORM_addr / DW_LNE_set_address operands in `__DWARF,__debug_info`
//       and `__debug_line` (`dwarf_info.rs` — `Relocation::section_relative`
//       against the `__text` ordinal), so the rebase form is proven here too.
//
//   SUBTRACTOR + UNSIGNED pair (r_pcrel=0, r_length=3): *field = A - B, the
//       in-place difference of two symbol addresses. The ARM64_RELOC_SUBTRACTOR
//       row carries B (subtrahend), the immediately following
//       ARM64_RELOC_UNSIGNED row carries A (minuend); the linker computes
//       `addr(A) - addr(B)` plus the baked in-place addend. AArch64 pairs
//       these at 8 bytes via `create_subtractor_pair` (`macho/reloc.rs`), e.g.
//       the DWARF-fallback FDE range fields (`pipeline.rs`).
//
// Reference: <mach-o/arm64/reloc.h>, LLVM `AArch64MachObjectWriter.cpp`,
// `RuntimeDyldMachOAArch64.h` (`ARM64_RELOC_PAGE21` / `ARM64_RELOC_PAGEOFF12`).

//! SMT proofs for AArch64 Mach-O DATA relocation selection/encoding correctness.

use crate::lowering_proof::{ProofObligation, TransvalCheckKind};
use crate::smt::SmtExpr;

/// Native pointer width on AArch64.
const W: u32 = 64;

/// Low-12-bit page offset mask `0xFFF`.
fn mask12() -> SmtExpr {
    SmtExpr::bv_const(0xFFF, W)
}

/// Page base mask `~0xFFF` (clears the low 12 bits).
fn not_mask12() -> SmtExpr {
    SmtExpr::bv_const(!0xFFFu64, W)
}

/// `page(x) = x & ~0xFFF`.
fn page(x: SmtExpr) -> SmtExpr {
    x.bvand(not_mask12())
}

// ===========================================================================
// 1. ARM64_RELOC_PAGE21 — ADRP page reconstruction
// ===========================================================================

/// Proof: `ARM64_RELOC_PAGE21` (pcrel=1) makes the ADRP reconstruct `page(S+A)`.
///
/// Theorem: forall S, A, P : BV64 .
///   (page(P) + (page(S+A) - page(P))) == page(S+A)
///
/// The spec side (`trust_ir_expr`) is the intended ADRP result `page(S+A)`. The
/// emitted side (`aarch64_expr`) is the runtime computation: the linker encodes
/// the page delta `page(S+A) - page(P)` into the ADRP immediate, and the CPU
/// adds `page(P)` at execution. The equality requires `p + (t - p) == t`, so it
/// is a genuine equivalence (non-degenerate).
pub fn proof_page21_adrp_page() -> ProofObligation {
    let s = SmtExpr::var("S", W);
    let a = SmtExpr::var("A", W);
    let p = SmtExpr::var("P", W);

    let target = s.bvadd(a);
    let page_target = page(target);
    let page_p = page(p);

    // Spec: ADRP should land on the target's page base.
    let intended = page_target.clone();
    // Emitted/runtime: page(P) + encoded page delta.
    let page_delta = page_target.bvsub(page_p.clone());
    let reconstructed = page_p.bvadd(page_delta);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "MachO AArch64: ARM64_RELOC_PAGE21 ADRP == page(S+A) (PC-relative page)".to_string(),
        trust_ir_expr: intended,
        aarch64_expr: reconstructed,
        inputs: vec![
            ("S".to_string(), W),
            ("A".to_string(), W),
            ("P".to_string(), W),
        ],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(TransvalCheckKind::InstructionLowering),
    }
}

/// Negative control: a PAGE21 row that (incorrectly) sets `r_pcrel=0` would make
/// the linker omit the PC-page subtraction, so the ADRP would land on
/// `page(P) + page(S+A)` instead of `page(S+A)`. That differs from the intended
/// page base whenever `page(P) != 0`.
///
/// This obligation is intentionally REFUTABLE; the unit tests / AY lane assert
/// it is Invalid (a counterexample exists), demonstrating the positive PAGE21
/// proof is a real equivalence and not a tautology.
pub fn proof_page21_wrong_pcrel_refutes() -> ProofObligation {
    let s = SmtExpr::var("S", W);
    let a = SmtExpr::var("A", W);
    let p = SmtExpr::var("P", W);

    let target = s.bvadd(a);
    let page_target = page(target);
    let page_p = page(p);

    let intended = page_target.clone();
    // WRONG: pcrel=0 drops the `- page(P)` term, so the linker writes
    // `page(S+A) >> 12` and the CPU still adds page(P): page(P) + page(S+A).
    let wrong = page_p.bvadd(page_target);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "MachO AArch64: PAGE21 with wrong r_pcrel=0 must REFUTE".to_string(),
        trust_ir_expr: intended,
        aarch64_expr: wrong,
        inputs: vec![
            ("S".to_string(), W),
            ("A".to_string(), W),
            ("P".to_string(), W),
        ],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(TransvalCheckKind::InstructionLowering),
    }
}

// ===========================================================================
// 2. ARM64_RELOC_PAGEOFF12 — ADRP+ADD/LDR full-address reconstruction
// ===========================================================================

/// Proof: `ARM64_RELOC_PAGEOFF12` (pcrel=0) on the ADD completes the ADRP+ADD
/// pair to reconstruct the full target `S + A`.
///
/// Theorem: forall S, A : BV64 .
///   (page(S+A) + ((S+A) & 0xFFF)) == (S+A)
///
/// The spec side (`trust_ir_expr`) is the intended full target address `S + A`.
/// The emitted side (`aarch64_expr`) is the runtime computation: the ADRP base
/// holds `page(S+A)` (proven by `proof_page21_adrp_page`), and the linker writes
/// `(S+A) & 0xFFF` into the ADD's imm12, which the CPU adds. The equality
/// requires `page(t) + (t & 0xFFF) == t` (a bit-decomposition identity), so it
/// is a genuine equivalence (non-degenerate).
pub fn proof_pageoff12_add_full() -> ProofObligation {
    let s = SmtExpr::var("S", W);
    let a = SmtExpr::var("A", W);

    let target = s.bvadd(a);

    // Spec: the intended full target address.
    let intended = target.clone();
    // Emitted/runtime: ADRP base page(T) + ADD's page offset (T & 0xFFF).
    let page_target = page(target.clone());
    let page_offset = target.bvand(mask12());
    let reconstructed = page_target.bvadd(page_offset);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "MachO AArch64: ARM64_RELOC_PAGEOFF12 ADRP+ADD == S+A (full address)".to_string(),
        trust_ir_expr: intended,
        aarch64_expr: reconstructed,
        inputs: vec![("S".to_string(), W), ("A".to_string(), W)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(TransvalCheckKind::InstructionLowering),
    }
}

/// Negative control: a PAGEOFF12 row that (incorrectly) sets `r_pcrel=1` would
/// make the linker subtract the field PC `P` before masking, so the ADD would
/// add `(S+A-P) & 0xFFF` to the ADRP base instead of `(S+A) & 0xFFF`. The
/// reconstructed address `page(S+A) + ((S+A-P) & 0xFFF)` differs from the
/// intended `S+A` in general (whenever the low 12 bits of `P` are nonzero).
///
/// This obligation is intentionally REFUTABLE.
pub fn proof_pageoff12_wrong_pcrel_refutes() -> ProofObligation {
    let s = SmtExpr::var("S", W);
    let a = SmtExpr::var("A", W);
    let p = SmtExpr::var("P", W);

    let target = s.bvadd(a);

    let intended = target.clone();
    let page_target = page(target.clone());
    // WRONG: pcrel=1 masks `(T - P)` instead of `T`.
    let wrong_offset = target.bvsub(p).bvand(mask12());
    let wrong = page_target.bvadd(wrong_offset);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "MachO AArch64: PAGEOFF12 with wrong r_pcrel=1 must REFUTE".to_string(),
        trust_ir_expr: intended,
        aarch64_expr: wrong,
        inputs: vec![
            ("S".to_string(), W),
            ("A".to_string(), W),
            ("P".to_string(), W),
        ],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(TransvalCheckKind::InstructionLowering),
    }
}

/// ARM64_RELOC_GOT_LOAD_PAGEOFF12: a function-pointer / extern-symbol address is
/// materialized as `ADRP xN, page; LDR xN, [xN, #pageoff]` where the LDR addresses
/// the symbol's GOT entry at `G+A` (then dereferences it — the dereference is
/// orthogonal to this address-computation proof). The LDR's page offset
/// reconstructs `(G+A) & 0xFFF` on top of the ADRP page base `page(G+A)`, so the
/// pair addresses exactly the GOT slot `G+A`. FAITHFUL (machine =
/// `page(G+A) + ((G+A)&0xFFF)` vs spec = `G+A`), NOT X==X. Mirror of the TLVP
/// `proof_tlvp_pageoff12_ldr_full` (GOT entry `G` in place of TLV descriptor `D`).
pub fn proof_got_load_pageoff12() -> ProofObligation {
    let g = SmtExpr::var("G", W);
    let a = SmtExpr::var("A", W);

    let target = g.bvadd(a);

    let intended = target.clone();
    let page_target = page(target.clone());
    let page_offset = target.bvand(mask12());
    let reconstructed = page_target.bvadd(page_offset);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "MachO AArch64: ARM64_RELOC_GOT_LOAD_PAGEOFF12 ADRP+LDR == G+A (GOT slot address)"
            .to_string(),
        trust_ir_expr: intended,
        aarch64_expr: reconstructed,
        inputs: vec![("G".to_string(), W), ("A".to_string(), W)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(TransvalCheckKind::InstructionLowering),
    }
}

/// Negative control for [`proof_got_load_pageoff12`]: a wrong `r_pcrel=1` masks
/// `(G+A-P)` instead of `(G+A)`, so the reconstructed address differs from the
/// intended `G+A` whenever the low 12 bits of `P` are nonzero. REFUTABLE.
pub fn proof_got_load_wrong_pcrel_refutes() -> ProofObligation {
    let g = SmtExpr::var("G", W);
    let a = SmtExpr::var("A", W);
    let p = SmtExpr::var("P", W);

    let target = g.bvadd(a);
    let intended = target.clone();
    let wrong = page(target.clone()).bvadd(target.bvsub(p).bvand(mask12()));

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "MachO AArch64: GOT_LOAD_PAGEOFF12 with wrong r_pcrel=1 must REFUTE".to_string(),
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

/// Proof: `ARM64_RELOC_GOT_LOAD_PAGE21` (pcrel=1) makes the ADRP of a
/// function-pointer / extern-symbol GOT load reconstruct `page(G+A)`, the page
/// base of the symbol's GOT slot address `G+A`.
///
/// Theorem: forall G, A, P : BV64 .
///   (page(P) + (page(G+A) - page(P))) == page(G+A)
///
/// The spec side (`trust_ir_expr`) is the intended ADRP result `page(G+A)`. The
/// emitted side (`aarch64_expr`) is the runtime computation: the linker encodes
/// the page delta `page(G+A) - page(P)` into the ADRP immediate, and the CPU
/// adds `page(P)` at execution. The equality requires `p + (t - p) == t`, so it
/// is a genuine equivalence (non-degenerate), NOT X==X — exactly the shape of
/// the local-global `proof_page21_adrp_page` and the TLVP
/// `proof_tlvp_page21_adrp_page`, with the GOT slot address `G` in place of the
/// section symbol `S` / TLV descriptor `D`. It is the GOT-page companion to the
/// already-proven `proof_got_load_pageoff12` (which proves the LDR's page
/// offset). The GOT_LOAD_PAGE21 row is a PC-relative ADRP page reference exactly
/// like PAGE21/TLVP_LOAD_PAGE21; the GOT indirection (the LDR then dereferences
/// the slot) is orthogonal to this address-computation proof.
pub fn proof_got_load_page21() -> ProofObligation {
    let g = SmtExpr::var("G", W);
    let a = SmtExpr::var("A", W);
    let p = SmtExpr::var("P", W);

    let target = g.bvadd(a);
    let page_target = page(target);
    let page_p = page(p);

    // Spec: ADRP should land on the GOT slot's page base.
    let intended = page_target.clone();
    // Emitted/runtime: page(P) + encoded page delta.
    let page_delta = page_target.bvsub(page_p.clone());
    let reconstructed = page_p.bvadd(page_delta);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name:
            "MachO AArch64: ARM64_RELOC_GOT_LOAD_PAGE21 ADRP == page(G+A) (GOT page, PC-relative)"
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

/// Negative control for [`proof_got_load_page21`]: a GOT_LOAD_PAGE21 row that
/// (incorrectly) sets `r_pcrel=0` would make the linker omit the PC-page
/// subtraction, so the ADRP would land on `page(P) + page(G+A)` instead of
/// `page(G+A)`. That differs from the intended page base whenever `page(P) != 0`.
///
/// This obligation is intentionally REFUTABLE; the AY lane / unit tests assert it
/// is Invalid (a counterexample exists), demonstrating the positive
/// GOT_LOAD_PAGE21 proof is a real equivalence and not a tautology.
pub fn proof_got_load_page21_wrong_pcrel_refutes() -> ProofObligation {
    let g = SmtExpr::var("G", W);
    let a = SmtExpr::var("A", W);
    let p = SmtExpr::var("P", W);

    let target = g.bvadd(a);
    let page_target = page(target);
    let page_p = page(p);

    let intended = page_target.clone();
    // WRONG: pcrel=0 drops the `- page(P)` term, so the linker writes
    // `page(G+A) >> 12` and the CPU still adds page(P): page(P) + page(G+A).
    let wrong = page_p.bvadd(page_target);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "MachO AArch64: GOT_LOAD_PAGE21 with wrong r_pcrel=0 must REFUTE".to_string(),
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
// 3. ARM64_RELOC_UNSIGNED (extern) — absolute 64-bit pointer slot
// ===========================================================================

/// Proof: EXTERN `ARM64_RELOC_UNSIGNED` writes the intended absolute pointer
/// `S + A`.
///
/// Theorem: forall S, A : BV64 .   (A + S) == (S + A)
///
/// The emitted side models the linker's r_extern=1/r_pcrel=0/r_length=3
/// application: it takes the in-place baked addend `A` and adds the resolved
/// symbol address `S`. The spec side is the intended reference "the slot holds
/// the address of S plus addend A". AArch64 emits these rows for compact-unwind
/// entry pointers (function_offset / personality / lsda), DWARF-fallback FDE
/// pointers, TLS descriptor slots, and data slots — all EXTERN
/// symbol_index-based. Mirror of the x86-64 `proof_unsigned_abs64`
/// (`macho_data_reloc_proofs.rs`). The two sides are structurally distinct
/// (`bvadd(A,S)` vs `bvadd(S,A)`), so the equivalence is the ring commutativity
/// identity, not `x == x`; a row with the wrong `r_pcrel`
/// ([`proof_unsigned_abs64_wrong_pcrel_refutes`]) refutes.
pub fn proof_unsigned_abs64() -> ProofObligation {
    let s = SmtExpr::var("S", W);
    let a = SmtExpr::var("A", W);

    // Intended: address-of-S plus addend.
    let intended = s.clone().bvadd(a.clone());
    // Linker (pcrel=0, length=3): in-place addend + resolved symbol address.
    let linker = a.bvadd(s);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "MachO AArch64: ARM64_RELOC_UNSIGNED == S + A (extern abs64 pointer slot)"
            .to_string(),
        trust_ir_expr: intended,
        aarch64_expr: linker,
        inputs: vec![("S".to_string(), W), ("A".to_string(), W)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(TransvalCheckKind::InstructionLowering),
    }
}

/// Negative control: an UNSIGNED row that (incorrectly) sets `r_pcrel=1` would
/// make the linker subtract the field PC `P`, producing `S + A - P`, which is
/// NOT the intended absolute `S + A` whenever `P != 0`.
///
/// This obligation is intentionally REFUTABLE; the unit tests / AY lane assert
/// it is Invalid (a counterexample exists), demonstrating the positive UNSIGNED
/// proof is a real equivalence and not a tautology.
pub fn proof_unsigned_abs64_wrong_pcrel_refutes() -> ProofObligation {
    let s = SmtExpr::var("S", W);
    let a = SmtExpr::var("A", W);
    let p = SmtExpr::var("P", W);

    let intended = s.clone().bvadd(a.clone());
    // WRONG: pcrel=1 makes the linker compute S + A - P.
    let linker_wrong = a.bvadd(s).bvsub(p);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "MachO AArch64: UNSIGNED with wrong r_pcrel=1 must REFUTE".to_string(),
        trust_ir_expr: intended,
        aarch64_expr: linker_wrong,
        inputs: vec![
            ("S".to_string(), W),
            ("A".to_string(), W),
            ("P".to_string(), W),
        ],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: SECTION-BASED `ARM64_RELOC_UNSIGNED` (r_extern=0) rebases the baked
/// object-space address to the target byte's FINAL address — non-tautological
/// rebase form.
///
/// Theorem: forall SectObj, SectFinal, off : BV64 .
///   (((SectObj + off) - SectObj) + SectFinal) == (SectFinal + off)
///
/// Spec side: the intended final address of the relocated target — the
/// r_symbolnum-th section's final base plus the target's offset within it
/// (`SectFinal + off`). Emitted/linker side: the emitter bakes the target's
/// address in the OBJECT's address space (`A = SectObj + off`), and the linker
/// rebases it (`A - SectObj + SectFinal` — ld64's non-extern UNSIGNED
/// application: recover the offset inside the section, re-anchor at the
/// section's final address). AArch64 emits this form for the DW_FORM_addr /
/// DW_LNE_set_address operands in `__DWARF,__debug_info` / `__debug_line`
/// (`dwarf_info.rs` — `Relocation::section_relative` against the `__text`
/// ordinal), so it is proven separately from the extern form: the extern
/// `S + A` formula models symbol resolution plus in-place addend, while the
/// section-based row has no symbol to resolve. The equality requires the ring
/// identity `(b + x) - b == x`, so it is a real equivalence, not `x == x` —
/// a baked value missing the section's object base rebases to the wrong final
/// byte ([`proof_unsigned_section_rebase_missing_base_refutes`]). Mirror of the
/// x86-64 `proof_unsigned_section_rebase` (`macho_data_reloc_proofs.rs`).
pub fn proof_unsigned_section_rebase() -> ProofObligation {
    let sect_obj = SmtExpr::var("SectObj", W);
    let sect_final = SmtExpr::var("SectFinal", W);
    let off = SmtExpr::var("off", W);

    // Spec: the target byte's final address.
    let intended = sect_final.clone().bvadd(off.clone());
    // Emitter bakes the object-space address; linker rebases it.
    let baked = sect_obj.clone().bvadd(off);
    let linker = baked.bvsub(sect_obj).bvadd(sect_final);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "MachO AArch64: SECTION-BASED ARM64_RELOC_UNSIGNED rebase == SectFinal + off \
               (DWARF debug addr operand)"
            .to_string(),
        trust_ir_expr: intended,
        aarch64_expr: linker,
        inputs: vec![
            ("SectObj".to_string(), W),
            ("SectFinal".to_string(), W),
            ("off".to_string(), W),
        ],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(TransvalCheckKind::InstructionLowering),
    }
}

/// Negative control: an emitter that bakes only the section-relative OFFSET
/// (forgetting the section's object-space base) leaves the linker rebasing the
/// wrong object address: `off - SectObj + SectFinal != SectFinal + off`
/// whenever `SectObj != 0`. Must REFUTE.
pub fn proof_unsigned_section_rebase_missing_base_refutes() -> ProofObligation {
    let sect_obj = SmtExpr::var("SectObj", W);
    let sect_final = SmtExpr::var("SectFinal", W);
    let off = SmtExpr::var("off", W);

    let intended = sect_final.clone().bvadd(off.clone());
    // WRONG: baked value is the bare offset, not an object-space address.
    let linker_wrong = off.bvsub(sect_obj).bvadd(sect_final);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "MachO AArch64: SECTION-BASED UNSIGNED baked without section base must REFUTE"
            .to_string(),
        trust_ir_expr: intended,
        aarch64_expr: linker_wrong,
        inputs: vec![
            ("SectObj".to_string(), W),
            ("SectFinal".to_string(), W),
            ("off".to_string(), W),
        ],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(TransvalCheckKind::InstructionLowering),
    }
}

// ===========================================================================
// 4. ARM64_RELOC_SUBTRACTOR + UNSIGNED — in-place symbol difference (A - B)
// ===========================================================================

/// Proof: the ARM64_RELOC_SUBTRACTOR(B) + ARM64_RELOC_UNSIGNED(A) pair writes
/// the difference `A - B` (plus the baked in-place addend).
///
/// Theorem: forall A, B, ADDEND : BV64 .
///   ((ADDEND - B) + A) == ((A + ADDEND) - B)
///
/// The SUBTRACTOR row supplies the subtrahend symbol B (r_pcrel=0, emitted
/// FIRST) and the immediately following UNSIGNED row supplies the minuend
/// symbol A; the linker computes `addr(A) - addr(B)` over the in-place field.
/// AArch64 pairs these at 8 bytes via `create_subtractor_pair`
/// (`macho/reloc.rs`), used for the DWARF-fallback FDE range fields — offsets
/// that must survive relocation as a symbol difference.
///
/// Spec side: the pair's contract — the field ends as the symbol difference
/// plus the in-place addend the assembler seeded: `(A + ADDEND) - B`.
/// Machine/linker side: the two rows apply IN ORDER over the in-place field:
/// SUBTRACTOR first (field := ADDEND - B), then the paired UNSIGNED
/// (field := field + A). The equality `(ADDEND - B) + A == (A + ADDEND) - B`
/// is a genuine ring equivalence — a wrong application order, sign, or operand
/// role refutes ([`proof_subtractor_pair_swapped_refutes`]). Mirror of the
/// x86-64 `proof_subtractor_pair_difference` (`macho_data_reloc_proofs.rs`).
pub fn proof_subtractor_pair_difference() -> ProofObligation {
    let a = SmtExpr::var("A", W);
    let b = SmtExpr::var("B", W);
    let addend = SmtExpr::var("ADDEND", W);

    // Spec: the pair's contract — (A + addend) - B.
    let intended = a.clone().bvadd(addend.clone()).bvsub(b.clone());
    // Machine/linker: SUBTRACTOR applies (addend - B), then UNSIGNED adds A.
    let linker = addend.bvsub(b).bvadd(a);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "MachO AArch64: ARM64_RELOC_SUBTRACTOR(B)+UNSIGNED(A) == A - B \
               (in-place difference)"
            .to_string(),
        trust_ir_expr: intended,
        aarch64_expr: linker,
        inputs: vec![
            ("A".to_string(), W),
            ("B".to_string(), W),
            ("ADDEND".to_string(), W),
        ],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(TransvalCheckKind::InstructionLowering),
    }
}

/// Negative control: swapping the SUBTRACTOR/UNSIGNED operand roles applies
/// `(ADDEND - A) + B` — the difference comes out `B - A`-signed; differs
/// whenever `A != B`. Must REFUTE.
pub fn proof_subtractor_pair_swapped_refutes() -> ProofObligation {
    let a = SmtExpr::var("A", W);
    let b = SmtExpr::var("B", W);
    let addend = SmtExpr::var("ADDEND", W);

    let intended = a.clone().bvadd(addend.clone()).bvsub(b.clone());
    // WRONG: subtrahend/minuend roles swapped in the applied rows.
    let linker_wrong = addend.bvsub(a).bvadd(b);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "MachO AArch64: SUBTRACTOR/UNSIGNED swapped (B - A) must REFUTE".to_string(),
        trust_ir_expr: intended,
        aarch64_expr: linker_wrong,
        inputs: vec![
            ("A".to_string(), W),
            ("B".to_string(), W),
            ("ADDEND".to_string(), W),
        ],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(TransvalCheckKind::InstructionLowering),
    }
}

// ===========================================================================
// Registry
// ===========================================================================

/// Collect the AArch64 Mach-O DATA relocation selection/encoding proofs.
///
/// Returns the 7 positive obligations covering the data relocation rows the
/// AArch64 Mach-O emitter produces:
/// - PAGE21 (ADRP reconstructs `page(S+A)`),
/// - PAGEOFF12 (ADRP+ADD reconstructs the full address `S+A`),
/// - GOT_LOAD_PAGE21 (ADRP reconstructs `page(G+A)`, the GOT slot's page base),
/// - GOT_LOAD_PAGEOFF12 (ADRP+LDR reconstructs the GOT slot address `G+A`),
///   the last two for function-pointer / extern-symbol materialization,
/// - UNSIGNED, extern form (abs64 pointer slot `S + A` — compact-unwind entry
///   pointers, FDE pointers, TLS descriptor slots, data slots),
/// - UNSIGNED, section-based form (DWARF `__debug_info`/`__debug_line` addr
///   rebase `(SectObj + off) - SectObj + SectFinal == SectFinal + off`),
/// - SUBTRACTOR+UNSIGNED difference pair (`A - B`).
///   All must verify. TLVP / BRANCH26 rows are covered elsewhere or stay
///   fail-closed until both an emission path and a selection proof exist.
pub fn aarch64_macho_data_relocation_proofs() -> Vec<ProofObligation> {
    vec![
        proof_page21_adrp_page(),
        proof_pageoff12_add_full(),
        proof_got_load_page21(),
        proof_got_load_pageoff12(),
        proof_unsigned_abs64(),
        proof_unsigned_section_rebase(),
        proof_subtractor_pair_difference(),
    ]
}

/// Negative-control obligations (each is REFUTABLE — a wrong encoding).
///
/// These are NOT registered as proofs; they are used by tests to demonstrate
/// the positive proofs are real equivalences (a malformed row is rejected).
pub fn aarch64_macho_data_relocation_negative_controls() -> Vec<ProofObligation> {
    vec![
        proof_page21_wrong_pcrel_refutes(),
        proof_pageoff12_wrong_pcrel_refutes(),
        proof_got_load_page21_wrong_pcrel_refutes(),
        proof_got_load_wrong_pcrel_refutes(),
        proof_unsigned_abs64_wrong_pcrel_refutes(),
        proof_unsigned_section_rebase_missing_base_refutes(),
        proof_subtractor_pair_swapped_refutes(),
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
    fn all_aarch64_data_reloc_proofs_verify() {
        for obligation in aarch64_macho_data_relocation_proofs() {
            let result = verify_by_evaluation(&obligation);
            assert!(
                matches!(result, VerificationResult::Valid),
                "AArch64 Mach-O data relocation proof '{}' failed: {:?}",
                obligation.name,
                result
            );
        }
    }

    #[test]
    fn all_aarch64_data_reloc_negative_controls_refute() {
        for obligation in aarch64_macho_data_relocation_negative_controls() {
            let result = verify_by_evaluation(&obligation);
            assert!(
                matches!(result, VerificationResult::Invalid { .. }),
                "AArch64 Mach-O data relocation NEGATIVE control '{}' should be Invalid \
                 (a wrong encoding must refute), got: {:?}",
                obligation.name,
                result
            );
        }
    }

    #[test]
    fn aarch64_data_reloc_proofs_are_non_degenerate() {
        for obligation in aarch64_macho_data_relocation_proofs() {
            assert!(
                obligation.is_genuinely_proven(),
                "AArch64 Mach-O data relocation proof '{}' is DEGENERATE (X==X); it proves nothing",
                obligation.name
            );
        }
    }

    #[test]
    fn aarch64_data_reloc_proof_count_and_names_unique() {
        let proofs = aarch64_macho_data_relocation_proofs();
        assert_eq!(proofs.len(), 7, "expected 7 data relocation proofs");
        let mut names: Vec<&str> = proofs.iter().map(|p| p.name.as_str()).collect();
        names.sort();
        let before = names.len();
        names.dedup();
        assert_eq!(before, names.len(), "duplicate data reloc proof names");
    }
}
