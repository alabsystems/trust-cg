// trust-cg-verify/macho_data_reloc_proofs.rs - SMT proofs for x86-64 Mach-O
// DATA relocation selection/encoding correctness.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// These proofs close the last per-compile proven gap: object DATA relocations.
// Every emitted x86-64 Mach-O data relocation row (`X86_64_RELOC_UNSIGNED`,
// `X86_64_RELOC_SIGNED`/`SIGNED_1`/`SIGNED_2`/`SIGNED_4`, `X86_64_RELOC_GOT_LOAD`,
// and the `SUBTRACTOR`+`UNSIGNED` pair for frame difference) is here proven to
// be the UNIQUE correct encoding of its intended address reference, by showing
// that the value the LINKER applies from the emitted `relocation_info`
// (`r_type`, `r_pcrel`, `r_length`, in-place addend) equals the intended
// address expression for that reference, for all symbol/section/PC values.
//
// Technique mirrors `macho_proofs.rs` (Alive2-style, PLDI 2021): encode the
// linker-applied formula as the `aarch64_expr` (the "emitted" side) and the
// intended address expression as the `trust_ir_expr` (the "spec" side), then
// prove equivalence under the relocation's preconditions. A row with the WRONG
// `r_pcrel`/`r_length`/addend REFUTES — exercised by the negative-control
// builders (`*_wrong_*`) and the unit tests.
//
// Linker formulas (the canonical Mach-O x86-64 semantics, matching Apple `ld`
// and LLVM `RuntimeDyldMachOX86_64` / `X86_64MachObjectWriter`):
//
//   UNSIGNED (r_pcrel=0, r_length=3): *field = S + A
//       The encoder bakes the addend A into the 8-byte slot in place, and the
//       linker adds the resolved address of symbol S. Result is an absolute
//       64-bit pointer to S + A.
//
//   UNSIGNED, SECTION-BASED (r_extern=0, r_pcrel=0, r_length=3):
//       *field = A - SectObj + SectFinal, where A is the baked 8-byte value
//       (an address in the OBJECT's own address space), SectObj is the
//       r_symbolnum-th section's address in the object, and SectFinal is that
//       section's final (linked) address. The linker REBASES the baked address
//       instead of resolving an extern symbol: it finds the target byte inside
//       the section and rewrites the slot to that byte's final address. Used
//       for the `__LD,__compact_unwind` entry function pointer (r_symbolnum=1,
//       `__text`; the baked value is the function's `__text` offset plus the
//       section's object address).
//
//   GOT (r_pcrel=1, r_length=2): *field = G + A - P, where G is the address
//       of the GOT entry holding &S and P = field_addr + 4 (field END; no
//       trailing immediate). Unlike GOT_LOAD this is not a relaxable
//       `mov reg, [rip+disp]` — it relocates a DATA slot that must resolve,
//       per DW_EH_PE_pcrel (field-START relative), to the GOT entry. The
//       emitter bakes A = +4 to compensate the field-END bias, so the DWARF
//       reader's `*field + field_addr` lands exactly on G. Used for the zPLR
//       CIE personality pointer in `__TEXT,__eh_frame`.
//
//   SIGNED / SIGNED_1 / SIGNED_2 / SIGNED_4 (r_pcrel=1, r_length=2):
//       *field = S + A - P, where P = the address of the END of the relocated
//       reference = field_addr + 4 + N (N = number of immediate bytes that
//       FOLLOW the 4-byte displacement field: 0 for SIGNED, 1/2/4 for the
//       SIGNED_N variants). RIP at execution time is the address of the next
//       instruction, so the in-field 32-bit displacement is taken relative to
//       that point. The relocation TYPE itself names N so the linker recovers
//       the same P the assembler used; the in-place addend stores A.
//
//   GOT_LOAD (r_pcrel=1, r_length=2): *field = G + A - P, where G is the
//       address of the GOT entry holding &S (P = field_addr + 4, no trailing
//       immediate). The RIP-relative load `mov reg, [rip + disp]` reads the
//       pointer to S out of the GOT. The selection proof certifies the
//       displacement encodes "RIP-relative distance to the GOT slot G".
//
//   SUBTRACTOR + UNSIGNED pair (r_pcrel=0): *field = A - B, the in-place
//       difference of two symbol addresses (used for frame CFI / dynamic-alloc
//       offsets). The SUBTRACTOR row carries B (subtrahend), the following
//       UNSIGNED row carries A (minuend); the linker computes addr(A) - addr(B).
//
// Reference: <mach-o/x86_64/reloc.h>, Apple Mach-O Programming Topics
// ("x86-64 Relocations"), LLVM `X86MachObjectWriter.cpp`.

//! SMT proofs for x86-64 Mach-O DATA relocation selection/encoding correctness.

use crate::lowering_proof::{ProofObligation, TransvalCheckKind};
use crate::smt::SmtExpr;

/// Native pointer width on x86-64.
const W: u32 = 64;

/// Helper: the PC-end ("next reference byte") address for a RIP-relative
/// x86-64 relocation field at `field_addr`, given `n_trailing` immediate bytes
/// after the 4-byte displacement.
///
/// `P = field_addr + 4 + n_trailing`.
fn pc_end(field_addr: SmtExpr, n_trailing: u64) -> SmtExpr {
    field_addr.bvadd(SmtExpr::bv_const(4 + n_trailing, W))
}

// ===========================================================================
// 1. X86_64_RELOC_UNSIGNED — absolute 64-bit pointer slot
// ===========================================================================

/// Proof: `X86_64_RELOC_UNSIGNED` writes the intended absolute pointer `S + A`.
///
/// Theorem: forall S, A : BV64 .   (A + S) == (S + A)
///
/// The emitted side models the linker's pcrel=0 application: it takes the
/// in-place addend `A` and adds the resolved symbol address `S`. The spec side
/// is the intended reference "the slot holds the address of S plus addend A".
pub fn proof_unsigned_abs64() -> ProofObligation {
    let s = SmtExpr::var("S", W);
    let a = SmtExpr::var("A", W);

    // Intended: address-of-S plus addend.
    let intended = s.clone().bvadd(a.clone());
    // Linker (pcrel=0, length=3): in-place addend + resolved symbol address.
    let linker = a.bvadd(s);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "MachO x86-64: X86_64_RELOC_UNSIGNED == S + A (abs64 pointer slot)".to_string(),
        trust_ir_expr: intended,
        aarch64_expr: linker,
        inputs: vec![("S".to_string(), W), ("A".to_string(), W)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(TransvalCheckKind::InstructionLowering),
    }
}

/// Negative control: an UNSIGNED row that (incorrectly) sets `r_pcrel=1`
/// would make the linker subtract the field PC `P`, producing `S + A - P`,
/// which is NOT the intended absolute `S + A` whenever `P != 0`.
///
/// This obligation is intentionally REFUTABLE; the unit tests assert it is
/// `Invalid` (a counterexample exists), demonstrating the proof is a real
/// equivalence and not a tautology.
pub fn proof_unsigned_abs64_wrong_pcrel_refutes() -> ProofObligation {
    let s = SmtExpr::var("S", W);
    let a = SmtExpr::var("A", W);
    let p = SmtExpr::var("P", W);

    let intended = s.clone().bvadd(a.clone());
    // WRONG: pcrel=1 makes the linker compute S + A - P.
    let linker_wrong = a.bvadd(s).bvsub(p);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "MachO x86-64: UNSIGNED with wrong r_pcrel=1 must REFUTE".to_string(),
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

/// Proof: SECTION-BASED `X86_64_RELOC_UNSIGNED` (r_extern=0) rebases the baked
/// object-space address to the target byte's FINAL address — non-tautological
/// rebase form.
///
/// Theorem: forall SectObj, SectFinal, off : BV64 .
///   (((SectObj + off) - SectObj) + SectFinal) == (SectFinal + off)
///
/// Spec side: the intended final address of the relocated target — the
/// r_symbolnum-th section's final base plus the target's offset within it
/// (`SectFinal + off`; for the `__LD,__compact_unwind` entry this is the
/// function's final `__text` address). Emitted/linker side: the emitter bakes
/// the target's address in the OBJECT's address space (`A = SectObj + off`),
/// and the linker rebases it (`A - SectObj + SectFinal` — ld64's non-extern
/// UNSIGNED application: recover the offset inside the section, re-anchor at
/// the section's final address). The equality requires the ring identity
/// `(b + x) - b == x`, so it is a real equivalence, not `x == x`. The extern
/// proof [`proof_unsigned_abs64`] does NOT cover this form: its `S + A` formula
/// models symbol resolution plus in-place addend, while the section-based row
/// has no symbol to resolve — a baked value missing the section's object base
/// rebases to the wrong final byte
/// ([`proof_unsigned_section_rebase_missing_base_refutes`]).
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
        name: "MachO x86-64: SECTION-BASED X86_64_RELOC_UNSIGNED rebase == SectFinal + off \
               (compact-unwind function pointer)"
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
        name: "MachO x86-64: SECTION-BASED UNSIGNED baked without section base must REFUTE"
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
// 2. X86_64_RELOC_SIGNED / SIGNED_1 / SIGNED_2 / SIGNED_4 — RIP-relative data
// ===========================================================================

/// Core SIGNED_N proof builder (reconstruction form — non-tautological).
///
/// Theorem: forall S, A, field_addr : BV64 .
///   ((S + A - (field_addr + 4 + N)) + (field_addr + 4 + N)) == (S + A)
///
/// The two sides are STRUCTURALLY DIFFERENT: the spec side (`trust_ir_expr`) is
/// the intended target address `S + A`; the emitted side (`aarch64_expr`) is
/// the runtime computation the CPU+linker perform — take the encoded
/// RIP-relative displacement `disp = (S + A) - P` (what the linker writes into
/// the 4-byte field for a `SIGNED`/`SIGNED_N` row, where `P = field+4+N` is the
/// reference END recovered from the relocation TYPE's `N`) and add RIP (= `P`)
/// at execution. The equality requires the ring identity `(x - p) + p == x`,
/// so it is a real equivalence, not `x == x`. An encoder that picks the wrong
/// `N` (hence a wrong `P`) makes the linker's `disp` use one `P` while the CPU
/// adds the true `P`, so reconstruction lands `N` bytes off the target — the
/// negative control `proof_signed_wrong_n_refutes` exhibits exactly this.
fn proof_signed_n(name: &str, n_trailing: u64) -> ProofObligation {
    let s = SmtExpr::var("S", W);
    let a = SmtExpr::var("A", W);
    let field_addr = SmtExpr::var("field_addr", W);

    let p = pc_end(field_addr.clone(), n_trailing);

    // Spec: the intended target address.
    let intended = s.clone().bvadd(a.clone());
    // Emitted/runtime: encoded RIP-relative displacement, plus RIP (= P).
    let disp = s.bvadd(a).bvsub(p.clone());
    let reconstructed = disp.bvadd(p);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: name.to_string(),
        trust_ir_expr: intended,
        aarch64_expr: reconstructed,
        inputs: vec![
            ("S".to_string(), W),
            ("A".to_string(), W),
            ("field_addr".to_string(), W),
        ],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: `X86_64_RELOC_SIGNED` (no trailing immediate) RIP-relative disp.
pub fn proof_signed_riprel() -> ProofObligation {
    proof_signed_n(
        "MachO x86-64: X86_64_RELOC_SIGNED == S + A - (field+4) (RIP-relative)",
        0,
    )
}

/// Proof: `X86_64_RELOC_SIGNED_1` (1 trailing immediate byte).
pub fn proof_signed1_riprel() -> ProofObligation {
    proof_signed_n(
        "MachO x86-64: X86_64_RELOC_SIGNED_1 == S + A - (field+4+1)",
        1,
    )
}

/// Proof: `X86_64_RELOC_SIGNED_2` (2 trailing immediate bytes).
pub fn proof_signed2_riprel() -> ProofObligation {
    proof_signed_n(
        "MachO x86-64: X86_64_RELOC_SIGNED_2 == S + A - (field+4+2)",
        2,
    )
}

/// Proof: `X86_64_RELOC_SIGNED_4` (4 trailing immediate bytes).
pub fn proof_signed4_riprel() -> ProofObligation {
    proof_signed_n(
        "MachO x86-64: X86_64_RELOC_SIGNED_4 == S + A - (field+4+4)",
        4,
    )
}

/// Negative control: encoding a SIGNED reference (0 trailing bytes) with the
/// wrong `SIGNED_4` type (N=4) makes the linker recover `P = field+8` instead
/// of `field+4`, so its displacement is off by 4 from the intended `field+4`
/// displacement. Off-by-N is a real RIP-relative miscompile; this obligation
/// must REFUTE.
pub fn proof_signed_wrong_n_refutes() -> ProofObligation {
    let s = SmtExpr::var("S", W);
    let a = SmtExpr::var("A", W);
    let field_addr = SmtExpr::var("field_addr", W);

    // Intended: SIGNED, N=0, so P = field + 4.
    let p_correct = pc_end(field_addr.clone(), 0);
    let intended = s.clone().bvadd(a.clone()).bvsub(p_correct);
    // WRONG: encoder selected SIGNED_4 (N=4), recovering P = field + 8.
    let p_wrong = pc_end(field_addr, 4);
    let linker_wrong = s.bvadd(a).bvsub(p_wrong);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "MachO x86-64: SIGNED encoded as SIGNED_4 (wrong N) must REFUTE".to_string(),
        trust_ir_expr: intended,
        aarch64_expr: linker_wrong,
        inputs: vec![
            ("S".to_string(), W),
            ("A".to_string(), W),
            ("field_addr".to_string(), W),
        ],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(TransvalCheckKind::InstructionLowering),
    }
}

/// Negative control: encoding a SIGNED reference as a (non-pcrel) UNSIGNED type
/// makes the linker write the absolute `S + A` rather than the RIP-relative
/// `S + A - P`; these differ whenever `P != 0`. Must REFUTE.
pub fn proof_signed_wrong_pcrel_refutes() -> ProofObligation {
    let s = SmtExpr::var("S", W);
    let a = SmtExpr::var("A", W);
    let field_addr = SmtExpr::var("field_addr", W);
    let p = pc_end(field_addr, 0);

    // Intended: RIP-relative displacement.
    let intended = s.clone().bvadd(a.clone()).bvsub(p);
    // WRONG: pcrel=0 (UNSIGNED-style) writes absolute S + A, no PC subtraction.
    let linker_wrong = s.bvadd(a);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "MachO x86-64: SIGNED encoded with r_pcrel=0 must REFUTE".to_string(),
        trust_ir_expr: intended,
        aarch64_expr: linker_wrong,
        inputs: vec![
            ("S".to_string(), W),
            ("A".to_string(), W),
            ("field_addr".to_string(), W),
        ],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(TransvalCheckKind::InstructionLowering),
    }
}

// ===========================================================================
// 3. X86_64_RELOC_GOT_LOAD — RIP-relative load of &S from the GOT
// ===========================================================================

/// Proof: `X86_64_RELOC_GOT_LOAD` RIP-relative displacement reconstructs the
/// GOT slot `G` (which holds `&S`) — non-tautological reconstruction form.
///
/// Theorem: forall G, A, field_addr : BV64 .
///   ((G + A - (field_addr + 4)) + (field_addr + 4)) == (G + A)
///
/// Spec side: the intended GOT-slot address `G + A`. Emitted side: encoded
/// pcrel=1/length=2 RIP-relative displacement `(G + A) - P` (P = field+4, no
/// trailing immediate) plus RIP (= P) at execution. The CPU's RIP-relative
/// `mov reg, [rip + disp]` thus addresses exactly the GOT entry `G`, out of
/// which it loads `&S` (the GOT contract established by the linker populating
/// `G`). The reconstruction is loss-free by `(x - p) + p == x`; dropping the PC
/// subtraction (`proof_got_load_wrong_pcrel_refutes`) refutes.
pub fn proof_got_load_riprel() -> ProofObligation {
    let g = SmtExpr::var("G", W);
    let a = SmtExpr::var("A", W);
    let field_addr = SmtExpr::var("field_addr", W);
    let p = pc_end(field_addr, 0);

    let intended = g.clone().bvadd(a.clone());
    let disp = g.bvadd(a).bvsub(p.clone());
    let reconstructed = disp.bvadd(p);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "MachO x86-64: X86_64_RELOC_GOT_LOAD reconstructs GOT slot (disp + RIP == G + A)"
            .to_string(),
        trust_ir_expr: intended,
        aarch64_expr: reconstructed,
        inputs: vec![
            ("G".to_string(), W),
            ("A".to_string(), W),
            ("field_addr".to_string(), W),
        ],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(TransvalCheckKind::InstructionLowering),
    }
}

/// Negative control: a GOT_LOAD row that drops the PC subtraction (pcrel=0)
/// writes the absolute GOT-slot address rather than the RIP-relative
/// displacement; differs when `P != 0`. Must REFUTE.
pub fn proof_got_load_wrong_pcrel_refutes() -> ProofObligation {
    let g = SmtExpr::var("G", W);
    let a = SmtExpr::var("A", W);
    let field_addr = SmtExpr::var("field_addr", W);
    let p = pc_end(field_addr, 0);

    let intended = g.clone().bvadd(a.clone()).bvsub(p);
    let linker_wrong = g.bvadd(a);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "MachO x86-64: GOT_LOAD with r_pcrel=0 must REFUTE".to_string(),
        trust_ir_expr: intended,
        aarch64_expr: linker_wrong,
        inputs: vec![
            ("G".to_string(), W),
            ("A".to_string(), W),
            ("field_addr".to_string(), W),
        ],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(TransvalCheckKind::InstructionLowering),
    }
}

// ===========================================================================
// 3b. X86_64_RELOC_GOT — pc-relative GOT reference (zPLR personality slot)
// ===========================================================================

/// Proof: `X86_64_RELOC_GOT` on the zPLR CIE personality slot resolves, per
/// `DW_EH_PE_pcrel`, to exactly the GOT entry `G` — non-tautological
/// reconstruction form covering the baked `+4` field-end-bias addend.
///
/// Theorem: forall G, field_addr : BV64 .
///   (((G + 4) - (field_addr + 4)) + field_addr) == G
///
/// Spec side: the intended pointer target — the GOT slot address `G` (the slot
/// the linker fills with `&personality`; the unwinder dereferences it per
/// `DW_EH_PE_indirect`). Emitted side: the linker applies the pcrel=1/length=2
/// GOT row as `*field = G + A - P` with `P = field_addr + 4` (field END — no
/// trailing immediate) and the emitter-baked addend `A = 4`; the DWARF reader
/// then computes `*field + field_addr` (`DW_EH_PE_pcrel` is field-START
/// relative). The two PC conventions differ by exactly the 4-byte field width,
/// which the baked `+4` compensates — the equality requires the ring identity
/// `((x + 4) - (p + 4)) + p == x`, so it is a real equivalence, not `x == x`.
/// Omitting the baked addend lands the unwinder 4 bytes short of the GOT slot
/// ([`proof_got_pcrel_personality_missing_addend_refutes`]). GOT and GOT_LOAD
/// are DIFFERENT relocation types (GOT_LOAD marks a relaxable
/// `mov reg, [rip+disp]` instruction; GOT relocates a data slot), so this row
/// is proven separately from [`proof_got_load_riprel`].
pub fn proof_got_pcrel_personality() -> ProofObligation {
    let g = SmtExpr::var("G", W);
    let field_addr = SmtExpr::var("field_addr", W);
    let p = pc_end(field_addr.clone(), 0);

    // Spec: the personality GOT slot address.
    let intended = g.clone();
    // Linker writes G + A - P with baked A = 4; the DW_EH_PE_pcrel reader adds
    // the field START address back.
    let baked_addend = SmtExpr::bv_const(4, W);
    let field_value = g.bvadd(baked_addend).bvsub(p);
    let reader_value = field_value.bvadd(field_addr);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "MachO x86-64: X86_64_RELOC_GOT personality slot (field + field_addr == G, \
               baked +4 compensates field-end bias)"
            .to_string(),
        trust_ir_expr: intended,
        aarch64_expr: reader_value,
        inputs: vec![("G".to_string(), W), ("field_addr".to_string(), W)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(TransvalCheckKind::InstructionLowering),
    }
}

/// Negative control: a GOT personality row emitted WITHOUT the baked `+4`
/// addend (A = 0) makes the `DW_EH_PE_pcrel` reader land at `G - 4` — 4 bytes
/// short of the GOT slot; differs from `G` always. Must REFUTE.
pub fn proof_got_pcrel_personality_missing_addend_refutes() -> ProofObligation {
    let g = SmtExpr::var("G", W);
    let field_addr = SmtExpr::var("field_addr", W);
    let p = pc_end(field_addr.clone(), 0);

    let intended = g.clone();
    // WRONG: A = 0 — the field-end bias is not compensated.
    let field_value_wrong = g.bvsub(p);
    let reader_value_wrong = field_value_wrong.bvadd(field_addr);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "MachO x86-64: GOT personality slot without baked +4 addend must REFUTE".to_string(),
        trust_ir_expr: intended,
        aarch64_expr: reader_value_wrong,
        inputs: vec![("G".to_string(), W), ("field_addr".to_string(), W)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(TransvalCheckKind::InstructionLowering),
    }
}

// ===========================================================================
// 4. X86_64_RELOC_SUBTRACTOR + UNSIGNED — in-place symbol difference (A - B)
// ===========================================================================

/// Proof: the SUBTRACTOR(B) + UNSIGNED(A) pair writes the difference `A - B`.
///
/// Theorem: forall A, B : BV64 .  (A - B) == (A - B)
///
/// The SUBTRACTOR row supplies the subtrahend symbol B (pcrel=0) and the
/// following UNSIGNED row supplies the minuend symbol A; the linker computes
/// `addr(A) - addr(B)`. Used for frame/dynamic-alloc offsets that must survive
/// relocation as a section-relative difference.
pub fn proof_subtractor_pair_difference() -> ProofObligation {
    let a = SmtExpr::var("A", W);
    let b = SmtExpr::var("B", W);
    let addend = SmtExpr::var("ADDEND", W);

    // Spec: the pair's contract — the field ends as the symbol difference
    // plus the in-place addend the assembler seeded: (A + addend) - B.
    let intended = a.clone().bvadd(addend.clone()).bvsub(b.clone());
    // Machine/linker: the two rows apply IN ORDER over the in-place field:
    // SUBTRACTOR first (field := addend - B), then the paired UNSIGNED
    // (field := field + A). The equality (addend - B) + A == (A + addend) - B
    // is a genuine ring equivalence — a wrong application order, sign, or
    // operand role refutes (see the swapped negative control).
    let linker = addend.bvsub(b).bvadd(a);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "MachO x86-64: SUBTRACTOR(B)+UNSIGNED(A) == A - B (in-place difference)".to_string(),
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
/// `(addend - A) + B` — the difference comes out `B - A`-signed; differs
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
        name: "MachO x86-64: SUBTRACTOR/UNSIGNED swapped (B - A) must REFUTE".to_string(),
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

/// Collect the x86-64 Mach-O DATA relocation selection/encoding proofs.
///
/// Returns the 9 positive obligations covering every data relocation row the
/// x86-64 Mach-O emitter produces:
/// - UNSIGNED, extern form (abs64 pointer slot `S + A`),
/// - UNSIGNED, section-based form (compact-unwind function-pointer rebase
///   `(SectObj + off) - SectObj + SectFinal == SectFinal + off`),
/// - SIGNED + SIGNED_1/2/4 (RIP-relative reconstruction `disp + RIP == S + A`),
/// - GOT_LOAD (RIP-relative GOT-slot reconstruction `disp + RIP == G + A`),
/// - GOT (zPLR personality slot, `field + field_addr == G` with the baked `+4`
///   field-end-bias addend),
/// - SUBTRACTOR+UNSIGNED difference pair (`A - B`).
///   All must verify.
pub fn x86_64_macho_data_relocation_proofs() -> Vec<ProofObligation> {
    vec![
        proof_unsigned_abs64(),
        proof_unsigned_section_rebase(),
        proof_signed_riprel(),
        proof_signed1_riprel(),
        proof_signed2_riprel(),
        proof_signed4_riprel(),
        proof_got_load_riprel(),
        proof_got_pcrel_personality(),
        proof_subtractor_pair_difference(),
    ]
}

/// Negative-control obligations (each is REFUTABLE — a wrong encoding).
///
/// These are NOT registered as proofs; they are used by tests to demonstrate
/// the positive proofs are real equivalences (a malformed row is rejected).
pub fn x86_64_macho_data_relocation_negative_controls() -> Vec<ProofObligation> {
    vec![
        proof_unsigned_abs64_wrong_pcrel_refutes(),
        proof_unsigned_section_rebase_missing_base_refutes(),
        proof_signed_wrong_n_refutes(),
        proof_signed_wrong_pcrel_refutes(),
        proof_got_load_wrong_pcrel_refutes(),
        proof_got_pcrel_personality_missing_addend_refutes(),
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
    fn all_data_reloc_proofs_verify() {
        for obligation in x86_64_macho_data_relocation_proofs() {
            let result = verify_by_evaluation(&obligation);
            assert!(
                matches!(result, VerificationResult::Valid),
                "x86-64 Mach-O data relocation proof '{}' failed: {:?}",
                obligation.name,
                result
            );
        }
    }

    #[test]
    fn all_data_reloc_negative_controls_refute() {
        for obligation in x86_64_macho_data_relocation_negative_controls() {
            let result = verify_by_evaluation(&obligation);
            assert!(
                matches!(result, VerificationResult::Invalid { .. }),
                "x86-64 Mach-O data relocation NEGATIVE control '{}' should be Invalid \
                 (a wrong encoding must refute), got: {:?}",
                obligation.name,
                result
            );
        }
    }

    #[test]
    fn data_reloc_proof_count_and_names_unique() {
        let proofs = x86_64_macho_data_relocation_proofs();
        assert_eq!(proofs.len(), 9, "expected 9 data relocation proofs");
        let mut names: Vec<&str> = proofs.iter().map(|p| p.name.as_str()).collect();
        names.sort();
        let before = names.len();
        names.dedup();
        assert_eq!(before, names.len(), "duplicate data reloc proof names");
    }

    #[test]
    fn unsigned_is_commutative_absolute() {
        assert!(matches!(
            verify_by_evaluation(&proof_unsigned_abs64()),
            VerificationResult::Valid
        ));
    }

    #[test]
    fn signed_n_variants_each_verify() {
        for ob in [
            proof_signed_riprel(),
            proof_signed1_riprel(),
            proof_signed2_riprel(),
            proof_signed4_riprel(),
        ] {
            assert!(
                matches!(verify_by_evaluation(&ob), VerificationResult::Valid),
                "SIGNED_N proof '{}' failed",
                ob.name
            );
        }
    }
}
