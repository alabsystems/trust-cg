// Trust-toolchain slice — trust-cg AArch64 INSTRUCTION-WORD BUILDERS, round 3
// (trust-cg/crates/trust-cg-codegen/src/aarch64/encoding.rs), transcribed
// VERBATIM. Companion to round 2's trust_encwords_slice.rs — these are the
// SIX encoding.rs builders round 2 did NOT cover.
//
// SELF-APPLICATION of verify-native==JIT to TRUST ITSELF (round 3, thread R2-B).
//
//   * `encode_extract`         (encoding.rs:142-151) — EXTR (ROR Rd,Rn,#sh is
//                                EXTR Rd,Rn,Rn,#sh — every rotate trust-cg emits)
//   * `encode_bit_reverse`     (encoding.rs:161-167) — RBIT
//   * `encode_uncond_branch`   (encoding.rs:260-265) — B / BL (every call +
//                                every unconditional jump)
//   * `encode_branch_reg`      (encoding.rs:277-287) — BR / BLR / RET (every
//                                indirect call and every function return)
//   * `encode_load_store_ui`   (encoding.rs:299-315) — LDR/STR unsigned scaled
//                                offset (the workhorse addressing mode)
//   * `encode_load_store_pair` (encoding.rs:364-390) — LDP/STP (every
//                                prologue/epilogue callee-save pair)
//
// MODELED BOUNDARY (documented honestly, same as round 2's word builders): the
// `debug_assert!` guards are STRIPPED from this slice. PINNED FRONTEND LIMIT
// (found by round 2, thread T4): a function body containing `debug_assert!`
// fails to lower under the stage1 MIR closure driver — the expanded
// `core::panicking::panic("...")` call's `&str` message constant is rejected
// ("call arg constant of non-scalar type ref"; MIR `Assert` TERMINATORS lower
// fine as condbr+unreachable, explicit panic CALLS do not). Stripping the
// guards is exactly the RELEASE-MODE semantics of these functions
// (`debug_assert!` compiles out with debug-assertions off, which is how
// trust-cg ships), so what is verified is the release semantics over the
// encoder contract domain (in-range fields); out-of-contract inputs are NOT
// differentially tested (native-debug would panic where the JIT computes the
// release value). The value-computing bodies are byte-for-byte in all six
// functions (compare against
// ~/trust-cg/crates/trust-cg-codegen/src/aarch64/encoding.rs).

#![allow(dead_code)]

// ── encode_extract (encoding.rs:142-151) — VERBATIM body
//    (debug_asserts stripped per header MODELED BOUNDARY) ────────────────────
fn encode_extract(sf: u32, n: u32, rm: u32, imms: u32, rn: u32, rd: u32) -> u32 {

    (sf << 31) | (0b100111 << 23) | (n << 22) | (rm << 16) | (imms << 10) | (rn << 5) | rd
}

// ── encode_bit_reverse (encoding.rs:161-167) — VERBATIM body
//    (debug_asserts stripped per header MODELED BOUNDARY) ────────────────────
fn encode_bit_reverse(sf: u32, rn: u32, rd: u32) -> u32 {

    (sf << 31) | (0b1011010110u32 << 21) | (rn << 5) | rd
}

// ── encode_uncond_branch (encoding.rs:260-265) — VERBATIM body
//    (debug_asserts stripped per header MODELED BOUNDARY) ────────────────────
fn encode_uncond_branch(op: u32, imm26: u32) -> u32 {

    (op << 31) | (0b00101 << 26) | imm26
}

// ── encode_branch_reg (encoding.rs:277-287) — VERBATIM body
//    (debug_asserts stripped per header MODELED BOUNDARY) ────────────────────
fn encode_branch_reg(opc: u32, rn: u32) -> u32 {

    (0b1101011 << 25)
        | (opc << 21)
        | (0b11111 << 16)
        // bits 15:10 = 000000 (implicit)
        | (rn << 5)
    // bits 4:0 = 00000 (implicit)
}

// ── encode_load_store_ui (encoding.rs:299-315) — VERBATIM body
//    (debug_asserts stripped per header MODELED BOUNDARY) ────────────────────
fn encode_load_store_ui(size: u32, v: u32, opc: u32, imm12: u32, rn: u32, rt: u32) -> u32 {

    (size << 30)
        | (0b111 << 27)
        | (v << 26)
        | (0b01 << 24)
        | (opc << 22)
        | (imm12 << 10)
        | (rn << 5)
        | rt
}

// ── encode_load_store_pair (encoding.rs:364-390) — VERBATIM body
//    (debug_asserts stripped per header MODELED BOUNDARY) ────────────────────
fn encode_load_store_pair(
    opc: u32,
    v: u32,
    l: u32,
    imm7: u32,
    rt2: u32,
    rn: u32,
    rt: u32,
) -> u32 {

    (opc << 30)
        | (0b101 << 27)
        | (v << 26)
        | (0b010 << 23)
        | (l << 22)
        | (imm7 << 15)
        | (rt2 << 10)
        | (rn << 5)
        | rt
}

// ── C-ABI keep-alive entry (one arm per emit root; the roots themselves are
//    the plain fns above, matched by --mir-emit-closure fnsubstr) ─────────────
#[no_mangle]
pub extern "C" fn t5_entry_encwords2(sel: u32) -> u32 {
    match sel {
        0 => encode_extract(1, 1, 1, 4, 1, 0),
        1 => encode_bit_reverse(1, 3, 2),
        2 => encode_uncond_branch(1, 2),
        3 => encode_branch_reg(2, 30),
        4 => encode_load_store_ui(3, 0, 1, 1, 1, 0),
        _ => encode_load_store_pair(2, 0, 1, 2, 1, 31, 0),
    }
}

fn main() {
    println!("{:#010X}", t5_entry_encwords2(1)); // 0xDAC00062 (RBIT X2, X3)
    println!("{:#010X}", t5_entry_encwords2(3)); // 0xD65F03C0 (RET X30)
}
