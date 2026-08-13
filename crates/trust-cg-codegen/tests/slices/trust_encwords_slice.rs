// Trust-toolchain slice — trust-cg AArch64 INSTRUCTION-WORD BUILDERS
// (trust-cg/crates/trust-cg-codegen/src/aarch64/encoding.rs), transcribed
// VERBATIM.
//
// SELF-APPLICATION of verify-native==JIT to TRUST ITSELF (round 2, thread T4).
//
// These are the format-level encoders that assemble the 32-bit AArch64
// instruction words trust-cg emits (bit layouts from ARM DDI 0487). They are
// the LAST pure step before bytes hit memory: a wrong field shift here is a
// wrong instruction in every compiled program. All are PURE, deterministic,
// closure-free, scalar-in/scalar-out:
//
//   * `encode_add_sub_shifted_reg` (encoding.rs:63-92)   — ADD/SUB/ADDS/SUBS reg
//   * `encode_logical_shifted_reg` (encoding.rs:102-130) — AND/ORR/EOR/... reg
//   * `encode_add_sub_imm`         (encoding.rs:177-194) — ADD/SUB imm
//   * `encode_move_wide`           (encoding.rs:216-232) — MOVN/MOVZ/MOVK
//                                    (incl. the #387/#447 defensive masking)
//   * `encode_cond_branch`         (encoding.rs:242-248) — B.cond
//   * `encode_cmp_branch`          (encoding.rs:402-409) — CBZ/CBNZ
//   * `encode_load_store_unscaled` (encoding.rs:332-352) — LDUR/STUR
//                                    (signed imm9 -> 9-bit field masking)
//
// MODELED BOUNDARY (documented honestly): the `debug_assert!` guards are
// STRIPPED from this slice. PINNED FRONTEND LIMIT found by this thread: a
// function body containing `debug_assert!` fails to lower under the stage1
// MIR closure driver — the expanded `core::panicking::panic("...")` call's
// `&str` message constant is rejected ("call arg constant of non-scalar type
// ref"; MIR `Assert` TERMINATORS lower fine as condbr+unreachable, explicit
// panic CALLS do not). Stripping the guards is exactly the RELEASE-MODE
// semantics of these functions (`debug_assert!` compiles out with
// debug-assertions off, which is how trust-cg ships), so what is verified is
// the release semantics over the encoder contract domain (in-range fields);
// out-of-contract inputs are NOT differentially tested (native-debug would
// panic where the JIT computes the release value). The value-computing bodies
// are byte-for-byte in all seven functions
// (compare against ~/trust-cg/crates/trust-cg-codegen/src/aarch64/encoding.rs).

#![allow(dead_code)]

// ── encode_add_sub_shifted_reg (encoding.rs:63-92) — VERBATIM ──────────────
fn encode_add_sub_shifted_reg(
    sf: u32,
    op: u32,
    s: u32,
    shift: u32,
    rm: u32,
    imm6: u32,
    rn: u32,
    rd: u32,
) -> u32 {

    (sf << 31)
        | (op << 30)
        | (s << 29)
        | (0b01011 << 24)
        | (shift << 22)
        // bit 21 = 0 (implicit)
        | (rm << 16)
        | (imm6 << 10)
        | (rn << 5)
        | rd
}

// ── encode_logical_shifted_reg (encoding.rs:102-130) — VERBATIM ────────────
fn encode_logical_shifted_reg(
    sf: u32,
    opc: u32,
    shift: u32,
    n: u32,
    rm: u32,
    imm6: u32,
    rn: u32,
    rd: u32,
) -> u32 {

    (sf << 31)
        | (opc << 29)
        | (0b01010 << 24)
        | (shift << 22)
        | (n << 21)
        | (rm << 16)
        | (imm6 << 10)
        | (rn << 5)
        | rd
}

// ── encode_add_sub_imm (encoding.rs:177-194) — VERBATIM ────────────────────
fn encode_add_sub_imm(sf: u32, op: u32, s: u32, sh: u32, imm12: u32, rn: u32, rd: u32) -> u32 {

    (sf << 31)
        | (op << 30)
        | (s << 29)
        | (0b100010 << 23)
        | (sh << 22)
        | (imm12 << 10)
        | (rn << 5)
        | rd
}

// ── encode_move_wide (encoding.rs:216-232) — VERBATIM (incl. the #387/#447
//    defensive masking of hw/imm16/rd) ──────────────────────────────────────
fn encode_move_wide(sf: u32, opc: u32, hw: u32, imm16: u32, rd: u32) -> u32 {

    // Mask `hw` and `imm16` defensively: on untrusted inputs (e.g. a
    // Movk dispatch arm that took a garbage shift operand) the caller
    // is expected to have already returned `Err(..)` — see #447. The
    // masking here guarantees that if it hasn't, we still produce a
    // well-formed (but semantically unspecified) encoding instead of
    // panicking in debug mode.
    let hw = hw & 0b11;
    let imm16 = imm16 & 0xFFFF;
    let rd = rd & 0b1_1111;

    (sf << 31) | (opc << 29) | (0b100101 << 23) | (hw << 21) | (imm16 << 5) | rd
}

// ── encode_cond_branch (encoding.rs:242-248) — VERBATIM ────────────────────
fn encode_cond_branch(imm19: u32, cond: u32) -> u32 {

    (0b01010100 << 24) | (imm19 << 5) | cond
    // bit 4 is 0 (o1 field)
}

// ── encode_cmp_branch (encoding.rs:402-409) — VERBATIM ─────────────────────
fn encode_cmp_branch(sf: u32, op: u32, imm19: u32, rt: u32) -> u32 {

    (sf << 31) | (0b011010 << 25) | (op << 24) | (imm19 << 5) | rt
}

// ── encode_load_store_unscaled (encoding.rs:332-352) — VERBATIM body
//    (debug_asserts stripped per header MODELED BOUNDARY) ────────────────────
fn encode_load_store_unscaled(size: u32, v: u32, opc: u32, imm9: i32, rn: u32, rt: u32) -> u32 {

    let imm9_bits = (imm9 as u32) & 0x1FF;

    (size << 30)
        | (0b111 << 27)
        | (v << 26)
        // bits [25:24] = 00 (unscaled/pre/post family)
        | (opc << 22)
        // bit [21] = 0
        | (imm9_bits << 12)
        // bits [11:10] = 00 (unscaled)
        | (rn << 5)
        | rt
}

// ── C-ABI keep-alive entries (one per emit root; the roots themselves are the
//    plain fns above, matched by --mir-emit-closure fnsubstr) ────────────────
#[no_mangle]
pub extern "C" fn t4_entry_encwords(sel: u32) -> u32 {
    match sel {
        0 => encode_add_sub_shifted_reg(1, 0, 0, 0, 2, 0, 1, 0),
        1 => encode_logical_shifted_reg(1, 0, 0, 0, 2, 0, 1, 0),
        2 => encode_add_sub_imm(1, 0, 0, 0, 42, 1, 0),
        3 => encode_move_wide(1, 2, 0, 0xBEEF, 0),
        4 => encode_cond_branch(4, 0),
        5 => encode_cmp_branch(1, 0, 4, 3),
        _ => encode_load_store_unscaled(3, 0, 1, -8, 29, 0),
    }
}

fn main() {
    println!("{:#010X}", t4_entry_encwords(0)); // 0x8B020020 (ADD X0, X1, X2)
    println!("{:#010X}", t4_entry_encwords(3));
}
