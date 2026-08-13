// Trust-toolchain slice — the trust-cg AArch64 LOGICAL-IMMEDIATE bitmask DECODER
// gate (`logical_immediate_bitmask_is_allocated`,
// trust-cg/crates/trust-cg-lift/src/disasm/aarch64.rs:843-856), transcribed
// VERBATIM.
//
// SELF-APPLICATION of verify-native==JIT to TRUST ITSELF (round 27, TRUST BATCH 14).
//
// `logical_immediate_bitmask_is_allocated(n, imms)` is the DECODER-side reserved-
// value gate for AND/ORR/EOR (immediate): it is the ARM `DecodeBitMasks`
// reserved check (ARM DDI 0487, `if len<1 || (imms AND levels)==levels then
// UNDEFINED`). It is the INVERSE-CHECK of the R1-verified encoder
// `encode_logical_imm_fields`: the encoder emits ONLY (N,immr,imms) triples the
// decoder must accept as ALLOCATED. An asymmetry between the two (encoder emits a
// triple this gate rejects, or this gate accepts a triple no bitmask produces) is
// a real encode/decode bug. `bit`/`bits`/`sign_extend` and the gate below are
// byte-for-byte from disasm/aarch64.rs.
//
// MODELED BOUNDARIES:
//   1. The `#[unsafe(no_mangle)]` root `logimm_gate_root` is a harness ABI adapter
//      (NOT production) exposing scalar-in/scalar-out.
//   2. F4 (R21) — `pattern.leading_zeros()` lowers to an UNRESOLVED extern leaf at
//      JIT link (`Jit(UnresolvedSymbol core::num::…leading_zeros)`); the emit
//      validates (a CALL is emitted) but the JIT cannot link the leaf. It is
//      replaced by the equivalent highest-set-bit scan producing the IDENTICAL
//      `len = 7 - pattern.leading_zeros()` for the pattern domain (pattern in
//      1..=0x7f — bit7 is always 0, and pattern != 0 by the guard above; `len` is
//      the index of the highest set bit). The rewrite is verdict-cross-checked
//      EXHAUSTIVELY against the INDEPENDENT `DecodeBitMasks` spec oracle (which uses
//      its own scan, not this one) in the test — so a scan bug cannot hide.

#![allow(dead_code)]

// ── logical_immediate_bitmask_is_allocated (disasm/aarch64.rs:843-856); the
//    `leading_zeros` line replaced per boundary #2, rest VERBATIM ──
fn logical_immediate_bitmask_is_allocated(n: bool, imms: u8) -> bool {
    let pattern = ((n as u8) << 6) | (!imms & 0x3f);
    if pattern == 0 {
        return false;
    }

    // VERBATIM was: `let len = 7 - pattern.leading_zeros() as u8;`
    // F4 rewrite: `len` = index of the highest set bit of `pattern` (== the above
    // for pattern in 1..=0x7f, pattern != 0 here).
    let mut len: u8 = 0;
    let mut probe: u8 = 6;
    while probe > 0 {
        if (pattern >> probe) & 1 != 0 {
            len = probe;
            break;
        }
        probe -= 1;
    }
    if len < 1 {
        return false;
    }

    let levels = (1u8 << len) - 1;
    imms & levels != levels
}

// ── C-ABI emit root (harness adapter): (n_bit, imms) -> allocated as u32 ──
#[unsafe(no_mangle)]
pub extern "C" fn logimm_gate_root(n_bit: u32, imms: u32) -> u32 {
    logical_immediate_bitmask_is_allocated(n_bit != 0, imms as u8) as u32
}

fn main() {
    // 64-bit N=1, imms=0 -> encodes a 1-bit ones-run over esize 64 -> allocated.
    println!("{}", logimm_gate_root(1, 0));
    // N=0, imms=0x3f over esize<=32 -> all-ones for the esize -> reserved.
    println!("{}", logimm_gate_root(0, 0x3f));
}
