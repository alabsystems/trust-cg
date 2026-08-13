// Trust-toolchain slice — the STRENGTH-REDUCTION / ALGEBRAIC-SIMPLIFICATION
// legality gates, originally transcribed at b2c58eb and still matched against
// their active sources:
//   * trust-cg-opt/src/cmp_branch_fusion.rs `is_power_of_two`
//   * trust-cg-opt/src/rewrite/patterns.rs  `shift_amount_in_width`
//   * trust-cg-opt/src/x86_const_fold.rs    `shift_amount`
//
// SELF-APPLICATION of verify-native==JIT to TRUST ITSELF (round 21,
// TRUST BATCH 8, part 3 — the STRENGTH-REDUCE / ALGEBRAIC predicate layer named
// by the R20 next_steps). These are the deciders that gate strength-reduction
// and algebraic simplification rewrites; a wrong answer applies an ILLEGAL
// rewrite:
//   * `is_power_of_two(v)` — the AND-mask / mul-to-BT single-bit gate
//     (cmp_branch_fusion.rs:366 guards the AND-imm -> BT fusion); a false
//     positive fuses a multi-bit mask into a single-bit test;
//   * `shift_amount_in_width(k, width)` — whether a shift amount k is a LEGAL
//     in-range shift for a width-bit value (1 <= k < width), the gate on the
//     declarative clear-low/high-bits shift-pair rules; a false positive folds
//     an out-of-range shift (UB on the target);
//   * `shift_amount(imm, max)` — the x86 const-fold shift-amount range gate
//     (0 <= imm <= max) returning the normalized u32 shift; a false positive
//     folds a shift whose amount exceeds the operand width.
//
// EMIT: stage1 `trust_ir_mir --mir-emit-closure sr_props_root` per the README
// recipe; `-C overflow-checks=off -C debug-assertions=off`.
//
// MODELED BOUNDARIES:
//   [B1] `Option<u32>` (from `shift_amount`) is destructured IN-MODULE and
//        materialized into a `#[repr(C)]` POD of u32 lanes (the R4 int-core
//        discipline). The transcribed bodies are UNMODIFIED except [B2].
//   [B2] Production `shift_amount_in_width` is `(1..width).contains(&k)` and
//        `shift_amount` is `(0..=max).contains(&imm)`. `Range::contains` /
//        `RangeInclusive::contains` do not lower (owner item #6 / R20 [F2]):
//        the range literal lowers to a const aggregate and the compare asserts
//        a single scalar. `(1..width).contains(&k)` is DEFINITIONALLY
//        `k >= 1 && k < width` and `(0..=max).contains(&imm)` is
//        `imm >= 0 && imm <= max`, transcribed here as those RESULT-IDENTICAL
//        comparisons. [F2] is RE-DECLARED (not re-pinned).
//   [B3] All three are PRIVATE in production (fn, not pub) — no linked dual
//        oracle; verified by VERBATIM transcription + an independent naive
//        semantic reference computed in the test (R16/R20 discipline).

// ── is_power_of_two (cmp_branch_fusion.rs, VERBATIM) ──────────────────────────
fn is_power_of_two(v: u64) -> bool {
    v != 0 && (v & (v - 1)) == 0
}

// ── shift_amount_in_width (rewrite/patterns.rs; [B2] Range rewrite) ────────────
fn shift_amount_in_width(k: i64, width: i64) -> bool {
    k >= 1 && k < width
}

// ── shift_amount (x86_const_fold.rs:186-192; [B2] RangeInclusive::contains) ────
fn shift_amount(imm: i64, max: i64) -> Option<u32> {
    if imm >= 0 && imm <= max {
        Some(imm as u32)
    } else {
        None
    }
}

// ── out-POD + #[no_mangle] mono ROOT ─────────────────────────────────────────

#[repr(C)]
pub struct SrProps {
    pub is_pow2: u32,
    pub in_width: u32,
    pub shamt_is_some: u32,
    pub shamt: u32,
}

/// ROOT: sweep one (v, k, width, max) through every strength-reduce gate. The
/// same scalar `k` is used as the candidate shift amount for both range gates.
#[no_mangle]
pub fn sr_props_root(v: u64, k: i64, width: i64, max: i64, out: &mut SrProps) {
    out.is_pow2 = is_power_of_two(v) as u32;
    out.in_width = shift_amount_in_width(k, width) as u32;
    match shift_amount(k, max) {
        Some(s) => {
            out.shamt_is_some = 1;
            out.shamt = s;
        }
        None => {
            out.shamt_is_some = 0;
            out.shamt = 0;
        }
    }
}
