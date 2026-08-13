// Trust-toolchain slice — the FP-VERIFICATION BIT-MODEL (the checker's FP
// semantics oracle), transcribed VERBATIM from
//   trust-cg/crates/trust-cg-verify/src/fp_bitmodel.rs
// plus one TRANSLATION-VALIDATION arch-legality gate from
//   trust-cg/crates/trust-cg-verify/src/pass_validators.rs  (TargetArch::idiv_traps).
//
// ROUND 25 / TRUST BATCH 12 — the trust-cg-VERIFY layer (the checker of the
// checker). No prior verification round (e2e_trust_fns_round2..11,
// e2e_fold_cast_status) linked `trust_cg_verify` at all — this whole crate is
// net-new to the native==JIT inventory (grep-confirmed).
//
// WHY SOUNDNESS-CRITICAL: fp_bitmodel.rs is the INTEGER-ONLY IEEE-754 model that
// EVICTED the host FPU from trust-cg's FP-verification trust base. Every FP
// lowering proof (smt.rs `try_eval` FP cases) checks the machine instruction's
// result against THIS model. A wrong classify predicate (is_nan/is_qnan/…) or a
// wrong FCMP-flag/FMIN result means the FP equivalence proof is comparing against
// a WRONG ORACLE — so it could ACCEPT a bad FP lowering (a soundness hole in the
// self-verification). Hence the REJECT direction matters as much as accept:
//   * is_nan MUST be false for every non-NaN pattern (inf, normal, subnormal,
//     zero) — a false "NaN" hides a real value miscompile.
//   * is_snan vs is_qnan — the mantissa-MSB split; confusing them mis-models the
//     FP-exception semantics.
//   * fmin PROPAGATES a lone qNaN (result NaN); fminnm returns the NUMBER — a
//     checker that used the wrong one accepts an FMINNM-as-FMIN miscompile.
//   * TargetArch::idiv_traps — the crux of #67: the SDIV-identity div expansion
//     is TOTAL on AArch64 (idiv_traps=false, legal) but a TRAPPING miscompile on
//     x86 (idiv_traps=true, must be rejected). A wrong answer accepts a #DE trap.
//
// FpFmt FLATTENED to its geometry scalars (total, mant, exp_w): the production
// `FpFmt { total, mant, exp_w, bias }` is passed by value; here we pass the
// fields as scalars. `bias` is UNUSED by every classify/fcmp/min-max function
// (source: bias only enters the fadd/fmul/fcvt rounding pipeline, none of which
// is transcribed here), so it is omitted — a trivially-faithful destructuring.
// Widths driven by the harness: F16 (16,10,5), F32 (32,23,8), F64 (64,52,11).
//
// EMIT: stage1 `trust_ir_mir --mir-emit-closure <root>` per the README recipe;
// `-C overflow-checks=off -C debug-assertions=off` (the runtime `1u64 << mant`
// shifts, exactly as batch-8/9). Roots: fp_classify_root / fp_fcmp_root /
// fp_minmax_root / idiv_traps_root. working tree @ (see report).

#![allow(dead_code)]
#![allow(clippy::needless_return)]

// ===========================================================================
// FIELD EXTRACT + CLASSIFY (integer-only; mirrors fp_bitmodel.rs classify).
//   FpFmt::{sign_bit,exp_max,mant_mask,word_mask} inlined as scalar exprs.
// ===========================================================================

// sign(f,x) = (x >> (total-1)) & 1 == 1
fn sign(total: u32, x: u64) -> bool {
    (x >> (total - 1)) & 1 == 1
}
// exp_field(f,x) = ((x >> mant) & ((1<<exp_w)-1)) as u32
fn exp_field(mant: u32, exp_w: u32, x: u64) -> u32 {
    ((x >> mant) & ((1u64 << exp_w) - 1)) as u32
}
// exp_max(f) = (1<<exp_w)-1
fn exp_max(exp_w: u32) -> u32 {
    (1u32 << exp_w) - 1
}
// mant_field(f,x) = x & ((1<<mant)-1)
fn mant_field(mant: u32, x: u64) -> u64 {
    x & ((1u64 << mant) - 1)
}
fn exp_all_ones(mant: u32, exp_w: u32, x: u64) -> bool {
    exp_field(mant, exp_w, x) == exp_max(exp_w)
}
fn exp_all_zero(mant: u32, exp_w: u32, x: u64) -> bool {
    exp_field(mant, exp_w, x) == 0
}
fn mant_zero(mant: u32, x: u64) -> bool {
    mant_field(mant, x) == 0
}

fn is_nan(mant: u32, exp_w: u32, x: u64) -> bool {
    exp_all_ones(mant, exp_w, x) && !mant_zero(mant, x)
}
fn is_inf(mant: u32, exp_w: u32, x: u64) -> bool {
    exp_all_ones(mant, exp_w, x) && mant_zero(mant, x)
}
fn is_zero(mant: u32, exp_w: u32, x: u64) -> bool {
    exp_all_zero(mant, exp_w, x) && mant_zero(mant, x)
}
fn is_subnormal(mant: u32, exp_w: u32, x: u64) -> bool {
    exp_all_zero(mant, exp_w, x) && !mant_zero(mant, x)
}
fn is_normal(mant: u32, exp_w: u32, x: u64) -> bool {
    !exp_all_ones(mant, exp_w, x) && !exp_all_zero(mant, exp_w, x)
}
// mant_msb(f,x) = (x >> (mant-1)) & 1 == 1  (set => quiet NaN)
fn mant_msb(mant: u32, x: u64) -> bool {
    (x >> (mant - 1)) & 1 == 1
}
fn is_qnan(mant: u32, exp_w: u32, x: u64) -> bool {
    is_nan(mant, exp_w, x) && mant_msb(mant, x)
}
fn is_snan(mant: u32, exp_w: u32, x: u64) -> bool {
    is_nan(mant, exp_w, x) && !mant_msb(mant, x)
}

// ===========================================================================
// FABS / FNEG — pure sign-bit ops.  word_mask needs `total`.
// ===========================================================================

fn word_mask(total: u32) -> u64 {
    if total >= 64 {
        u64::MAX
    } else {
        (1u64 << total) - 1
    }
}
fn fabs(total: u32, x: u64) -> u64 {
    x & !(1u64 << (total - 1)) & word_mask(total)
}
fn fneg(total: u32, x: u64) -> u64 {
    (x ^ (1u64 << (total - 1))) & word_mask(total)
}

// ===========================================================================
// ORDERED COMPARE on bit patterns (NaN guarded by the caller).
// ===========================================================================

fn magnitude(total: u32, x: u64) -> u64 {
    x & !(1u64 << (total - 1)) & word_mask(total)
}

// Strict ordered less-than (assumes neither is NaN). Mirrors fp_lt.
fn fp_lt(total: u32, a: u64, b: u64) -> bool {
    let sa = sign(total, a);
    let sb = sign(total, b);
    let ma = magnitude(total, a);
    let mb = magnitude(total, b);
    if sa {
        if sb {
            // both negative: a<b iff |a|>|b|
            mb < ma
        } else {
            // a neg, b pos: a<b unless both zero
            !(ma == 0 && mb == 0)
        }
    } else if sb {
        // a pos, b neg: false
        false
    } else {
        // both positive: a<b iff |a|<|b|
        ma < mb
    }
}

// Equality as reals (no NaN): bit-equal OR both zero (+0 == -0).
fn fp_eq(total: u32, mant: u32, exp_w: u32, a: u64, b: u64) -> bool {
    let am = a & word_mask(total);
    let bm = b & word_mask(total);
    am == bm || (is_zero(mant, exp_w, a) && is_zero(mant, exp_w, b))
}

// ===========================================================================
// FCMP -> NZCV.  ordered EQ->0110 ; LT->1000 ; GT->0010 ; UNORDERED->0011.
// ===========================================================================

fn fcmp_unord(mant: u32, exp_w: u32, a: u64, b: u64) -> bool {
    is_nan(mant, exp_w, a) || is_nan(mant, exp_w, b)
}
// N: set only on ordered LT.
fn fcmp_n(total: u32, mant: u32, exp_w: u32, a: u64, b: u64) -> bool {
    !fcmp_unord(mant, exp_w, a, b) && fp_lt(total, a, b)
}
// Z: set only on ordered EQ.
fn fcmp_z(total: u32, mant: u32, exp_w: u32, a: u64, b: u64) -> bool {
    !fcmp_unord(mant, exp_w, a, b) && fp_eq(total, mant, exp_w, a, b)
}
// C: set unless ordered LT (i.e. GT, EQ, or unordered).
fn fcmp_c(total: u32, mant: u32, exp_w: u32, a: u64, b: u64) -> bool {
    !fcmp_n(total, mant, exp_w, a, b)
}
// V: set only when unordered.
fn fcmp_v(mant: u32, exp_w: u32, a: u64, b: u64) -> bool {
    fcmp_unord(mant, exp_w, a, b)
}

// ===========================================================================
// NaN PROCESSING (ARM FPProcessNaNs) + numeric MIN/MAX + {F}MIN/MAX family.
// ===========================================================================

fn quiet(total: u32, mant: u32, x: u64) -> u64 {
    (x | (1u64 << (mant - 1))) & word_mask(total)
}
// selectNaN: sNaN(a)->quiet a ; sNaN(b)->quiet b ; qNaN(a)->a ; else b.
fn select_nan(total: u32, mant: u32, exp_w: u32, a: u64, b: u64) -> u64 {
    if is_snan(mant, exp_w, a) {
        quiet(total, mant, a)
    } else if is_snan(mant, exp_w, b) {
        quiet(total, mant, b)
    } else if is_qnan(mant, exp_w, a) {
        a & word_mask(total)
    } else {
        b & word_mask(total)
    }
}

fn num_min(total: u32, mant: u32, exp_w: u32, a: u64, b: u64) -> u64 {
    if is_zero(mant, exp_w, a) && is_zero(mant, exp_w, b) {
        // signed-zero rule: min returns the -0 one.
        if sign(total, a) {
            a & word_mask(total)
        } else {
            b & word_mask(total)
        }
    } else if fp_lt(total, a, b) {
        a & word_mask(total)
    } else {
        b & word_mask(total)
    }
}
fn num_max(total: u32, mant: u32, exp_w: u32, a: u64, b: u64) -> u64 {
    if is_zero(mant, exp_w, a) && is_zero(mant, exp_w, b) {
        // signed-zero rule: max returns the +0 one.
        if sign(total, a) {
            b & word_mask(total)
        } else {
            a & word_mask(total)
        }
    } else if fp_lt(total, b, a) {
        a & word_mask(total)
    } else {
        b & word_mask(total)
    }
}

// FMIN — NaN-propagating (NaN whenever either input is NaN).
fn fmin(total: u32, mant: u32, exp_w: u32, a: u64, b: u64) -> u64 {
    if is_nan(mant, exp_w, a) || is_nan(mant, exp_w, b) {
        select_nan(total, mant, exp_w, a, b)
    } else {
        num_min(total, mant, exp_w, a, b)
    }
}
// FMAX — NaN-propagating.
fn fmax(total: u32, mant: u32, exp_w: u32, a: u64, b: u64) -> u64 {
    if is_nan(mant, exp_w, a) || is_nan(mant, exp_w, b) {
        select_nan(total, mant, exp_w, a, b)
    } else {
        num_max(total, mant, exp_w, a, b)
    }
}
fn nm_force_nan(mant: u32, exp_w: u32, a: u64, b: u64) -> bool {
    is_snan(mant, exp_w, a)
        || is_snan(mant, exp_w, b)
        || (is_nan(mant, exp_w, a) && is_nan(mant, exp_w, b))
}
// FMINNM — IEEE minNum: a lone qNaN yields the NUMBER.
fn fminnm(total: u32, mant: u32, exp_w: u32, a: u64, b: u64) -> u64 {
    if nm_force_nan(mant, exp_w, a, b) {
        select_nan(total, mant, exp_w, a, b)
    } else if is_nan(mant, exp_w, a) {
        b & word_mask(total)
    } else if is_nan(mant, exp_w, b) {
        a & word_mask(total)
    } else {
        num_min(total, mant, exp_w, a, b)
    }
}
// FMAXNM — IEEE maxNum.
fn fmaxnm(total: u32, mant: u32, exp_w: u32, a: u64, b: u64) -> u64 {
    if nm_force_nan(mant, exp_w, a, b) {
        select_nan(total, mant, exp_w, a, b)
    } else if is_nan(mant, exp_w, a) {
        b & word_mask(total)
    } else if is_nan(mant, exp_w, b) {
        a & word_mask(total)
    } else {
        num_max(total, mant, exp_w, a, b)
    }
}

// ===========================================================================
// TRANSLATION-VALIDATION arch-legality gate — pass_validators.rs
//   TargetArch::idiv_traps (the SDIV-identity expansion legality decider, #67).
// ===========================================================================

enum TargetArch {
    Aarch64,
    X86_64,
}
impl TargetArch {
    fn idiv_traps(self) -> bool {
        match self {
            TargetArch::Aarch64 => false,
            TargetArch::X86_64 => true,
        }
    }
}

// ===========================================================================
// MONO ROOTS — write results to a 0xDEAD-poisonable out-POD (round-11 style).
// ===========================================================================

#[repr(C)]
pub struct ClassifyOut {
    pub is_nan: u32,
    pub is_inf: u32,
    pub is_zero: u32,
    pub is_subnormal: u32,
    pub is_normal: u32,
    pub is_qnan: u32,
    pub is_snan: u32,
}

#[no_mangle]
pub extern "C" fn fp_classify_root(mant: u32, exp_w: u32, x: u64, out: *mut ClassifyOut) {
    let r = ClassifyOut {
        is_nan: if is_nan(mant, exp_w, x) { 1 } else { 0 },
        is_inf: if is_inf(mant, exp_w, x) { 1 } else { 0 },
        is_zero: if is_zero(mant, exp_w, x) { 1 } else { 0 },
        is_subnormal: if is_subnormal(mant, exp_w, x) { 1 } else { 0 },
        is_normal: if is_normal(mant, exp_w, x) { 1 } else { 0 },
        is_qnan: if is_qnan(mant, exp_w, x) { 1 } else { 0 },
        is_snan: if is_snan(mant, exp_w, x) { 1 } else { 0 },
    };
    unsafe {
        *out = r;
    }
}

#[repr(C)]
pub struct FcmpOut {
    pub n: u32,
    pub z: u32,
    pub c: u32,
    pub v: u32,
}

#[no_mangle]
pub extern "C" fn fp_fcmp_root(total: u32, mant: u32, exp_w: u32, a: u64, b: u64, out: *mut FcmpOut) {
    let r = FcmpOut {
        n: if fcmp_n(total, mant, exp_w, a, b) { 1 } else { 0 },
        z: if fcmp_z(total, mant, exp_w, a, b) { 1 } else { 0 },
        c: if fcmp_c(total, mant, exp_w, a, b) { 1 } else { 0 },
        v: if fcmp_v(mant, exp_w, a, b) { 1 } else { 0 },
    };
    unsafe {
        *out = r;
    }
}

#[repr(C)]
pub struct MinMaxOut {
    pub fmin: u64,
    pub fmax: u64,
    pub fminnm: u64,
    pub fmaxnm: u64,
    pub fabs_a: u64,
    pub fneg_a: u64,
}

#[no_mangle]
pub extern "C" fn fp_minmax_root(
    total: u32,
    mant: u32,
    exp_w: u32,
    a: u64,
    b: u64,
    out: *mut MinMaxOut,
) {
    let r = MinMaxOut {
        fmin: fmin(total, mant, exp_w, a, b),
        fmax: fmax(total, mant, exp_w, a, b),
        fminnm: fminnm(total, mant, exp_w, a, b),
        fmaxnm: fmaxnm(total, mant, exp_w, a, b),
        fabs_a: fabs(total, a),
        fneg_a: fneg(total, a),
    };
    unsafe {
        *out = r;
    }
}

#[repr(C)]
pub struct IdivOut {
    pub traps: u32,
}

#[no_mangle]
pub extern "C" fn idiv_traps_root(arch_tag: u32, out: *mut IdivOut) {
    let arch = if arch_tag == 0 {
        TargetArch::Aarch64
    } else {
        TargetArch::X86_64
    };
    let r = IdivOut {
        traps: if arch.idiv_traps() { 1 } else { 0 },
    };
    unsafe {
        *out = r;
    }
}
