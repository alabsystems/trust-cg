// Trust-toolchain slice — the trust-cg AArch64 LOGICAL-IMMEDIATE encoder cluster
// (trust-cg/crates/trust-cg-codegen/src/aarch64/encode.rs:152-224), transcribed
// VERBATIM.
//
// SELF-APPLICATION of verify-native==JIT to TRUST ITSELF (round 2, thread T4).
//
// `encode_logical_imm_fields(raw, register_width)` is THE AArch64 bitmask-
// immediate encoder: it decides whether a constant is expressible as a logical
// immediate (a rotated replicated ones-run) and, if so, computes the exact
// (N, immr, imms) field triple for AND/ORR/EOR-immediate instructions
// (`encode_logical_immediate`, encode.rs:244). A wrong triple here silently
// changes the MASK VALUE of a logical instruction in every program trust-cg
// compiles — a miscompile generator. Its helpers:
//   * `low_mask(bits)`                (encode.rs:152-158) — VERBATIM
//   * `rotate_right_within(v,rot,w)`  (encode.rs:160-168) — VERBATIM
//   * `replicate_logical_element(...)`(encode.rs:170-178) — VERBATIM
//   * `encode_logical_imm_fields(...)`(encode.rs:180-224) — VERBATIM search
//     logic; see MODELED BOUNDARY below.
//
// MODELED BOUNDARIES (documented honestly):
//   1. ERROR-DIAGNOSTIC PAYLOAD: production returns
//      `Err(EncodeError::InvalidOperand { opcode, index, desc: format!(..) })`
//      — a String-carrying diagnostic. The `opcode: AArch64Opcode` and
//      `index: usize` parameters exist ONLY to populate that diagnostic and are
//      dead in the success path. The slice models the error as `Err(())` and
//      drops the two diagnostic-only parameters. The VERIFIED semantics is the
//      encodability DECISION plus the exact (n, immr, imms) success triple; the
//      diagnostic string content is NOT verified.
//   2. The `#[no_mangle]` emit root `encode_logical_imm_fields_packed` is a
//      test-harness ABI adapter (NOT production code): it packs the
//      `Result<(u32,u32,u32), ()>` into one u64 (bit 63 = ok flag,
//      bits 12..=12 = n, 6..=11 = immr, 0..=5 = imms) so the root has a pure
//      scalar ABI. The packing is injective on outcomes, so native==JIT through
//      the adapter verifies the verbatim callee.
//   3. CONST-SLICE ITERATION REWRITTEN (frontend limit: a `&[u32]` const slice
//      aggregate does not lower — "constant value not a single scalar").
//      Production iterates `element_widths = &[2,4,8,16,32(,64)]`; the slice
//      iterates `element_width` by DOUBLING from 2 up to `register_width` —
//      the identical sequence for the production domain register_width ∈
//      {32, 64} (the only call sites, encode.rs:230/232: `if sf == 1 { 64 }
//      else { 32 }`). The NATIVE ORACLE in the test keeps the verbatim
//      const-slice form, so the differential itself checks this rewrite.
//   4. RANGE FOR-LOOPS REWRITTEN AS WHILE (frontend limit: `Range<u32>`
//      iterator `into_iter`/`next` lower to EMPTY extern bodies). Production's
//      `for ones_len in 1..element_width` / `for rotation in 0..element_width`
//      become explicit `while` counters with identical bounds/step. Likewise
//      `u32::from(element_width == 64)` (an empty-extern `From::from`) becomes
//      the identical-value cast `(element_width == 64) as u32`. Both rewrites
//      are checked by the differential against the verbatim native oracle.
//
// All four bodies below are otherwise byte-for-byte from encode.rs (compare
// against ~/trust-cg/crates/trust-cg-codegen/src/aarch64/encode.rs).

#![allow(dead_code)]

// ── low_mask (encode.rs:152-158) — VERBATIM ────────────────────────────────
fn low_mask(bits: u32) -> u64 {
    if bits == 64 {
        u64::MAX
    } else {
        (1u64 << bits) - 1
    }
}

// ── rotate_right_within (encode.rs:160-168) — VERBATIM ─────────────────────
fn rotate_right_within(value: u64, rot: u32, width: u32) -> u64 {
    let mask = low_mask(width);
    let value = value & mask;
    if rot == 0 {
        value
    } else {
        ((value >> rot) | (value << (width - rot))) & mask
    }
}

// ── replicate_logical_element (encode.rs:170-178) — VERBATIM ───────────────
fn replicate_logical_element(pattern: u64, element_width: u32, register_width: u32) -> u64 {
    let mut out = 0;
    let mut shift = 0;
    while shift < register_width {
        out |= pattern << shift;
        shift += element_width;
    }
    out & low_mask(register_width)
}

// ── encode_logical_imm_fields (encode.rs:180-224) — VERBATIM search logic;
//    error payload + diagnostic-only params MODELED (see header boundary #1) ──
fn encode_logical_imm_fields(
    raw: i64,
    register_width: u32,
) -> Result<(u32, u32, u32), ()> {
    let register_mask = low_mask(register_width);
    let raw_mask = (raw as u64) & register_mask;
    if raw_mask == 0 || raw_mask == register_mask {
        return Err(());
    }

    // MODELED (boundary #3): production's `for &element_width in
    // &[2,4,8,16,32(,64)]` — identical sequence via doubling for
    // register_width ∈ {32, 64}.
    let mut element_width: u32 = 2;
    while element_width <= register_width {
        // MODELED (boundary #4): `for ones_len in 1..element_width`.
        let mut ones_len: u32 = 1;
        while ones_len < element_width {
            let ones = low_mask(ones_len);
            // MODELED (boundary #4): `for rotation in 0..element_width`.
            let mut rotation: u32 = 0;
            while rotation < element_width {
                let element = rotate_right_within(ones, rotation, element_width);
                let candidate = replicate_logical_element(element, element_width, register_width);
                if candidate == raw_mask {
                    // MODELED (boundary #4): `u32::from(element_width == 64)`.
                    let n = (element_width == 64) as u32;
                    let immr = rotation & 0x3f;
                    let imms_prefix = (!((element_width << 1) - 1)) & 0x3f;
                    let imms = imms_prefix | (ones_len - 1);
                    return Ok((n, immr, imms));
                }
                rotation += 1;
            }
            ones_len += 1;
        }
        element_width <<= 1;
    }

    Err(())
}

// ── C-ABI emit root (harness adapter, boundary #2): packs the Result into a
//    u64 so the root ABI is scalar-only. ok → bit63 | n<<12 | immr<<6 | imms;
//    err → 0. Injective: any Ok triple has bit 63 set, Err is exactly 0. ──
#[no_mangle]
pub extern "C" fn encode_logical_imm_fields_packed(raw: i64, register_width: u32) -> u64 {
    match encode_logical_imm_fields(raw, register_width) {
        Ok((n, immr, imms)) => {
            (1u64 << 63) | ((n as u64) << 12) | ((immr as u64) << 6) | (imms as u64)
        }
        Err(()) => 0,
    }
}

fn main() {
    // Smoke: 0xFF (8 ones in 64-bit) is encodable; 0 / all-ones are not.
    println!("{:#x}", encode_logical_imm_fields_packed(0xFF, 64));
    println!("{:#x}", encode_logical_imm_fields_packed(0, 64));
    println!("{:#x}", encode_logical_imm_fields_packed(-1, 64));
    println!("{:#x}", encode_logical_imm_fields_packed(0x5555_5555, 32));
}
