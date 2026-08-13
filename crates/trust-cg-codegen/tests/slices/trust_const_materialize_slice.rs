// HISTORICAL trust-toolchain slice (round 21) — the AArch64 CONST-FOLD
// MATERIALIZATION deciders and mul-to-shift STRENGTH-REDUCTION decider as they
// existed at pinned working tree b2c58eb. This fixture is retained only for the
// frontend/JIT unresolved-symbol regression in e2e_trust_fns_round8.rs; it is
// NOT a transcription of, or coverage claim for, the current v0.1.0
// constant-materialization implementation (which restricts MOVN to hw0).
//
// The historical bodies were transcribed from:
//   * trust-cg/crates/trust-cg-opt/src/const_fold.rs   `single_movn_materialization` (660-669)
//   * trust-cg/crates/trust-cg-lower/src/isel.rs        `move_wide_chunks`            (2646-2654)
//   * trust-cg/crates/trust-cg-lower/src/isel.rs        `fmov_imm8_encodable`         (2864-2869)
//   * trust-cg/crates/trust-cg-codegen/src/aarch64/encode.rs `encode_fmov_imm8`       (3605-3632)
//   * trust-cg-opt/src/peephole.rs @ b2c58eb `is_power_of_two` (historical)
// pinned working tree @ b2c58eb.
//
// SELF-APPLICATION of verify-native==JIT to TRUST ITSELF (round 21,
// TRUST BATCH 8, part 2 — the CONST-FOLD MATERIALIZATION + STRENGTH-REDUCE
// predicate layer named by the R20 next_steps as clean and high-yield).
//
// HISTORICAL CONTEXT: these deciders answered "how do I materialize this
// constant / is it a legal strength-reduction target" — a wrong answer emits
// a WRONG constant or applies an ILLEGAL rewrite:
//   * `single_movn_materialization(v)` — decides whether the 64-bit constant v
//     is materializable in ONE MOVN (all-ones except one 16-bit lane, so the
//     bitwise-NOT of v is confined to a single aligned 16-bit field) and
//     returns the (imm16, shift) for that MOVN. A wrong imm/shift materializes
//     the wrong 64-bit value silently;
//   * `move_wide_chunks(imm, n)` — the little-endian 16-bit chunk decomposition
//     the MOVZ/MOVK sequence writes; a wrong chunk is a wrong constant;
//   * `fmov_imm8_encodable(x)` — whether the float x is exactly representable
//     in the AArch64 8-bit FMOV-immediate encoding (else the lowerer MUST fall
//     back to a constant-pool load). A false positive emits a WRONG float;
//   * `encode_fmov_imm8(x)` — the actual 8-bit FMOV immediate word (the encoder
//     companion to the encodability predicate);
//   * `is_power_of_two(v)` — the mul-to-shift strength-reduction gate: returns
//     Some(log2(v)) so `MUL x, k`  ->  `LSL x, log2(k)` when k is a positive
//     power of two (the historical AArch64 peephole rule). A wrong shift
//     rewrites `x*k` to the wrong value; a false positive rewrites a
//     non-power-of-two multiply.
//
// EMIT: stage1 `trust_ir_mir --mir-emit-closure <root>` per the README recipe,
// one emit per root, `-C overflow-checks=off -C debug-assertions=off`.
//
// MODELED BOUNDARIES:
//   [B1] `Option<(u16,u64)>` / `Option<u32>` / `[u16;4]` results are
//        destructured IN-MODULE and materialized into a `#[repr(C)]` POD of
//        u32 lanes so the differential compares plain scalars (the R4
//        interpreter-int-core discipline). The transcribed bodies are
//        UNMODIFIED.
//   [B2] At the pinned revision all five were PRIVATE in production (fn, not
//        pub). Any historical VERBATIM statement below refers only to b2c58eb,
//        not the current release implementation.
//   [B3] `move_wide_chunks` carries `debug_assert!((1..=4).contains(&chunk_count))`
//        in production. `RangeInclusive::contains` does not lower (owner item
//        #6) AND the assert is compiled out under `-C debug-assertions=off`, so
//        the contract check is DROPPED here and the sweep stays inside the
//        production contract domain `chunk_count in 1..=4` (the R20 note:
//        "encode_move_wide sweep excludes opc=1 — production debug_assert
//        contract domain").
//   [B4] EXECUTION STATUS (round 21): every function here is transcribed and
//        emits with `validate_module = 0`, but NONE executes native==JIT — each
//        depends on a core leaf the trust-ir frontend lowers to an EMPTY-BODIED
//        external symbol the trust-cg JIT cannot resolve ([F4], owner-#6 class):
//          * `single_movn_materialization` — `[u64;4]::into_iter`,
//          * `move_wide_chunks`            — slice `iter_mut`/`enumerate`/`take`,
//          * `is_power_of_two`             — `i64::trailing_zeros`,
//          * `fmov_imm8_encodable`/`encode_fmov_imm8` — `f64::to_bits`, AND the
//            fmov pair ALSO trips [F3] (a `u32 >> <i32 literal>` emits
//            `lshr u32 by i32`, which the validator rejects — so the fmov root
//            is validate!=0 too).
//        The movn / chunks / historical-power-of-two roots are F4-PINNED
//        fail-loud in e2e_trust_fns_round8.rs (assert `Jit(UnresolvedSymbol)`);
//        the fmov pair is DECLARED blocked. All auto-promote when [F3]/[F4] are
//        fixed at the frontend root.

// ── historical single_movn_materialization (b2c58eb, VERBATIM) ──────────────
fn single_movn_materialization(value: u64) -> Option<(u16, u64)> {
    let inverted = !value;
    for shift in [0u64, 16, 32, 48] {
        let lane_mask = 0xFFFFu64 << shift;
        if inverted & !lane_mask == 0 {
            return Some((((inverted >> shift) & 0xFFFF) as u16, shift));
        }
    }
    None
}

// ── move_wide_chunks (isel.rs:2646-2654, VERBATIM sans the debug_assert; [B3]) ─
fn move_wide_chunks(imm: i64, chunk_count: usize) -> [u16; 4] {
    let value = imm as u64;
    let mut chunks = [0u16; 4];
    for (idx, chunk) in chunks.iter_mut().enumerate().take(chunk_count) {
        *chunk = ((value >> (idx * 16)) & 0xFFFF) as u16;
    }
    chunks
}

// ── fmov_imm8_encodable (isel.rs:2864-2869, VERBATIM sans the (1020..=1027)
//    RangeInclusive::contains -> the RESULT-IDENTICAL `>= && <=`; owner #6) ────
fn fmov_imm8_encodable(value: f64) -> bool {
    let bits = value.to_bits();
    let exp = ((bits >> 52) & 0x7FF) as i32;
    let frac = bits & 0x000F_FFFF_FFFF_FFFF;
    (frac & 0x0000_FFFF_FFFF_FFFF) == 0 && (exp >= 1020 && exp <= 1027)
}

// ── encode_fmov_imm8 (encode.rs:3605-3632, VERBATIM sans the two
//    RangeInclusive::contains -> RESULT-IDENTICAL `>= && <=`; owner #6) ────────
fn encode_fmov_imm8(value: f64) -> u32 {
    let bits = value.to_bits();

    let sign = ((bits >> 63) & 1) as u32;
    let exp = ((bits >> 52) & 0x7FF) as i32;
    let frac = bits & 0x000F_FFFF_FFFF_FFFF;

    if frac & 0x0000_FFFF_FFFF_FFFF != 0 {
        return 0;
    }

    let top4 = ((frac >> 48) & 0xF) as u32;

    if !(exp >= 1020 && exp <= 1027) {
        return 0;
    }

    let biased_3 = (exp - 1020) as u32;
    let not_b = ((biased_3 >> 2) ^ 1) & 1;

    (sign << 7) | (not_b << 6) | ((biased_3 & 0b11) << 4) | top4
}

// ── historical is_power_of_two (peephole.rs @ b2c58eb, VERBATIM) ─────────────
fn is_power_of_two(val: i64) -> Option<u32> {
    if val > 0 && (val & (val - 1)) == 0 {
        Some(val.trailing_zeros())
    } else {
        None
    }
}

// ── out-PODs + #[no_mangle] mono ROOTS ───────────────────────────────────────

/// single_movn_materialization result, split into scalar lanes.
#[repr(C)]
pub struct MovnProps {
    pub is_some: u32,
    pub imm16: u32,
    pub shift: u32,
}

/// ROOT 1: single_movn_materialization decider.
#[no_mangle]
pub fn movn_props_root(value: u64, out: &mut MovnProps) {
    match single_movn_materialization(value) {
        Some((imm, shift)) => {
            out.is_some = 1;
            out.imm16 = imm as u32;
            out.shift = shift as u32;
        }
        None => {
            out.is_some = 0;
            out.imm16 = 0;
            out.shift = 0;
        }
    }
}

/// move_wide_chunks result (4 x u16 chunks).
#[repr(C)]
pub struct ChunksProps {
    pub c0: u32,
    pub c1: u32,
    pub c2: u32,
    pub c3: u32,
}

/// ROOT 2: move_wide_chunks little-endian 16-bit decomposition.
#[no_mangle]
pub fn chunks_root(value: u64, chunk_count: u32, out: &mut ChunksProps) {
    let chunks = move_wide_chunks(value as i64, chunk_count as usize);
    out.c0 = chunks[0] as u32;
    out.c1 = chunks[1] as u32;
    out.c2 = chunks[2] as u32;
    out.c3 = chunks[3] as u32;
}

/// fmov encodability + 8-bit encoding.
#[repr(C)]
pub struct FmovProps {
    pub encodable: u32,
    pub encoded: u32,
}

/// ROOT 3: fmov_imm8_encodable + encode_fmov_imm8 over one f64.
#[no_mangle]
pub fn fmov_props_root(value: f64, out: &mut FmovProps) {
    out.encodable = fmov_imm8_encodable(value) as u32;
    out.encoded = encode_fmov_imm8(value);
}

/// is_power_of_two result, split into scalar lanes.
#[repr(C)]
pub struct Pow2Props {
    pub is_some: u32,
    pub shift: u32,
}

/// ROOT 4: is_power_of_two (mul-to-shift strength-reduction decider).
#[no_mangle]
pub fn pow2_props_root(value: i64, out: &mut Pow2Props) {
    match is_power_of_two(value) {
        Some(s) => {
            out.is_some = 1;
            out.shift = s;
        }
        None => {
            out.is_some = 0;
            out.shift = 0;
        }
    }
}
