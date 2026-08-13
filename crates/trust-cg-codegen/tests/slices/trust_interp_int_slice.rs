// Trust-toolchain slice — trust-ir's REFERENCE-INTERPRETER integer core,
// transcribed from trust-ir/crates/trust-ir/src/interpret.rs (rev 9e4f5d2 ==
// the Cargo.lock pin 357750a for this file; the two revs differ only in lock
// files) plus the op enums from inst.rs.
//
// SELF-APPLICATION of verify-native==JIT to TRUST ITSELF (round 4).
//
// WHY SOUNDNESS-CRITICAL: `interpret.rs` is trust-ir's SEMANTIC GROUND TRUTH —
// the deterministic reference interpreter that differential harnesses (and
// humans) consult to decide what a trust-ir program MEANS. `eval_int_binop` /
// `eval_int_unop` / `eval_int_icmp` / `eval_int_overflow` and their pure helper
// closure (`int_mask`, `signed_bounds`, `InterpretInt::{from_raw,from_i128,
// as_signed}`, `signed_div_overflows`, `shift_amount`, `unsigned_overflow`,
// `signed_overflow`) DEFINE the meaning of every integer instruction. If Trust
// miscompiles these, the reference oracle itself lies when run through Trust.
//
// TRANSCRIBED FROM (all re-checked against production on 2026-07-03):
//   * `BinOp` (inst.rs:11-40), `UnOp` (inst.rs:44-63), `OverflowOp`
//     (inst.rs:67-71), `ICmpOp` (inst.rs:75-86) — VERBATIM variant set & order
//     (serde cfg_attr dropped — the established slice convention).
//   * `InterpretInt` (interpret.rs:202-243) — struct + `from_i128`/`from_raw`/
//     `as_unsigned`/`as_signed`, field order and masking VERBATIM.
//   * `eval_int_binop` (interpret.rs:4186-4271), `eval_int_unop` (4273-4327),
//     `eval_int_overflow` (4329-4358), `eval_int_icmp` (4360-4373),
//     `unsigned_overflow` (4581-4594), `signed_overflow` (4596-4606),
//     `signed_div_overflows` (4608-4611), `shift_amount` (4613-4624),
//     `int_mask` (4659-4665), `signed_bounds` (4667-4673).
//
// EMIT: this slice is emitted with `-C overflow-checks=off -C debug-assertions=off`
// (recorded in every module's regen line). trust-ir ships release-profile
// (wrapping) semantics for its own arithmetic; the flag makes the raw
// operators below EXACTLY the production `wrapping_*` calls (see REWRITE
// notes). The stage1 driver forwards unrecognized args to rustc.
//
// MODELED BOUNDARIES (each also marked REWRITE/MODELED at the exact line):
//   [B1] Error identity, not error prose: production returns
//        `InterpretError { code, message: String, .. }` built through
//        `type_error`/`ub`/`err` with `format!` diagnostics (String
//        construction does not lower — known frontend gap). The slice models
//        the error as the fieldless `EvalErr` enum with ONE VARIANT PER
//        PRODUCTION ERROR SITE, so the differential verifies WHICH error
//        fires (and its InterpretErrorCode class), dropping only the message
//        text. Mapping (site -> production code):
//          WidthMismatch          -> TypeError    ("integer widths differ")
//          UDivByZero             -> UndefinedBehavior
//          URemByZero             -> UndefinedBehavior
//          SDivByZero             -> UndefinedBehavior
//          SDivOverflow           -> UndefinedBehavior
//          SRemByZero             -> UndefinedBehavior
//          SRemOverflow           -> UndefinedBehavior
//          ShiftOutOfRange        -> UndefinedBehavior
//          FloatBinopUnsupported  -> UnsupportedInstruction
//          FloatUnopUnsupported   -> UnsupportedInstruction
//   [B2] `int_mask(..).expect("validated integer width")` (a PANIC site,
//        provably unreachable for the closed width set {8,16,32,64,128} that
//        `InterpretInt` construction admits — interpret.rs:4649-4658 documents
//        exactly this) is rewritten as a `match` whose `None` arm returns a
//        sentinel (`Err(EvalErr::InvalidWidthPanic)` in the eval fns; `0` /
//        `false` in `as_signed`/`unsigned_overflow`). The harness NEVER
//        sweeps an invalid width into these fns (production would abort);
//        in-domain the arm is dead and the transcription is exact.
//   [B3] REWRITE `wrapping_add/sub/mul` -> `+ - *` and
//        `0u128.wrapping_sub(x)` -> `0u128 - x`, compiled under
//        `-C overflow-checks=off`: the u128/i128 `wrapping_*` inherent
//        methods lower to EMPTY-BODIED externs (the known core-method
//        frontend gap); with overflow checks off the raw operators are
//        DEFINITIONALLY the wrapping operations (two's-complement wrap is
//        the specified release-mode semantics). This keeps the interpreter's
//        core arithmetic INSIDE the JIT-verified module instead of
//        outsourcing it to native host shims.
//   [B4] REWRITE `lhs.raw.overflowing_add(rhs.raw)` (unsigned_overflow) ->
//        wrapping `+` plus the definitional carry test `sum < lhs.raw`;
//        REWRITE `lhs.raw.overflowing_mul(rhs.raw)` -> wrapping `*` plus the
//        definitional full-width test `rhs != 0 && lhs > u128::MAX / rhs`.
//        Both differentially checked against the verbatim-form native oracle
//        in the test file.
//   [B5] REWRITE `u128::from(bits)` (shift_amount) -> `bits as u128` and
//        `u128::from(value.raw.count_ones())` (CtPop) -> a definitional
//        bit-at-a-time popcount while-loop (`From`/`count_ones` lower to
//        empty externs — known gap; the loop is checked against the native
//        `count_ones` oracle over the full sweep).
//   [B6] REWRITE `?` on `Result` (`shift_amount(..)?` in eval_int_binop,
//        `eval_int_binop(..)?` in eval_int_overflow) -> explicit `match`
//        (the Result-flavored Try lowers to empty-bodied externs — pinned
//        round-2 frontend limit; same rewrite as the round-3 encoders).
//        `?` on `Option` in `from_raw`/`from_i128` is KEPT VERBATIM and
//        lowered through the `Try::branch`/`FromResidual` empty-extern shims
//        (host-bound in the test — the round-2 fold_cast pattern).
//   [B7] `signed_overflow`'s `i128::checked_add/checked_sub/checked_mul`
//        are KEPT VERBATIM; they lower to empty-bodied externs bound to
//        faithful host shims in the test (the exact already-verified
//        `fold_binop` boundary). Everything around them (signed_bounds, the
//        as_signed decodes, the range test) runs inside the JIT.
//   [B8] `block: BlockId` params (diagnostic-only: they feed the dropped
//        message strings) are omitted from the slice signatures, and the
//        `matches!` macro in signed_overflow is kept (it is plain match
//        syntax). `Interpreter`/`InterpretValue` plumbing above these pure
//        fns is out of scope (modeled out, as with every prior slice).
//
// Every root passes 128-bit values BY POINTER and returns through out-params:
// the u128/i128 HALF-SPLITTING register-pair ABI (rebuilding a 128 from two
// u64 halves) is the KNOWN-BROKEN ISel class (owner item #3) and is
// deliberately never built here.

#![allow(dead_code)]
#![allow(clippy::all)]

// ── the production op enums, VERBATIM variant SET + ORDER ──────────────────

// inst.rs:11-40 (serde cfg_attr dropped; doc comments elided).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    UDiv,
    SDiv,
    URem,
    SRem,
    FAdd,
    FSub,
    FMul,
    FDiv,
    FRem,
    FMin,
    FMax,
    And,
    Or,
    Xor,
    Shl,
    LShr,
    AShr,
}

// inst.rs:44-63.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum UnOp {
    Neg,
    FNeg,
    FAbs,
    FSqrt,
    FFloor,
    FCeil,
    FTrunc,
    Not,
    CtPop,
}

// inst.rs:67-71.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum OverflowOp {
    AddOverflow,
    SubOverflow,
    MulOverflow,
}

// inst.rs:75-86.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ICmpOp {
    Eq,
    Ne,
    Ult,
    Ule,
    Ugt,
    Uge,
    Slt,
    Sle,
    Sgt,
    Sge,
}

// ── [B1] the MODELED error-identity enum (one variant per production error
//    site; see the module header for the site -> InterpretErrorCode map). ──
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EvalErr {
    WidthMismatch,
    InvalidWidthPanic, // [B2] stand-in for the production expect() panic
    UDivByZero,
    URemByZero,
    SDivByZero,
    SDivOverflow,
    SRemByZero,
    SRemOverflow,
    ShiftOutOfRange,
    FloatBinopUnsupported,
    FloatUnopUnsupported,
}

// ── InterpretInt (interpret.rs:202-243) ─────────────────────────────────────

/// interpret.rs:201-206, VERBATIM (field order/types; derives as production).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct InterpretInt {
    pub bits: u32,
    pub signed: bool,
    pub raw: u128,
}

impl InterpretInt {
    /// interpret.rs:209-215, VERBATIM (incl. the `?` on `int_mask` — lowered
    /// through the Option-Try empty-extern shims, host-bound in the test [B6]).
    pub fn from_i128(bits: u32, signed: bool, value: i128) -> Option<Self> {
        Some(Self {
            bits,
            signed,
            raw: (value as u128) & int_mask(bits)?,
        })
    }

    /// interpret.rs:217-223, VERBATIM (same `?` note as from_i128 [B6]).
    pub fn from_raw(bits: u32, signed: bool, raw: u128) -> Option<Self> {
        Some(Self {
            bits,
            signed,
            raw: raw & int_mask(bits)?,
        })
    }

    /// interpret.rs:225-227, VERBATIM.
    pub fn as_unsigned(self) -> u128 {
        self.raw
    }

    /// interpret.rs:229-242. VERBATIM except [B2]: the production
    /// `int_mask(self.bits).expect("validated integer width")` panic site is
    /// a `match` whose (in-domain dead) `None` arm returns 0.
    pub fn as_signed(self) -> i128 {
        if self.bits == 128 {
            return self.raw as i128;
        }

        let mask = match int_mask(self.bits) {
            Some(m) => m,
            None => return 0, // [B2] production: panic (unreachable in-domain)
        };
        let sign_bit = 1u128 << (self.bits - 1);
        if self.raw & sign_bit == 0 {
            self.raw as i128
        } else {
            let magnitude = ((!self.raw & mask) + 1) & mask;
            -(magnitude as i128)
        }
    }
}

// ── the pure helpers (interpret.rs:4608-4673) ───────────────────────────────

/// interpret.rs:4659-4665, VERBATIM.
fn int_mask(bits: u32) -> Option<u128> {
    match bits {
        1..=127 => Some((1u128 << bits) - 1),
        128 => Some(u128::MAX),
        _ => None,
    }
}

/// interpret.rs:4667-4673, VERBATIM. (Domain note: callers only pass bits
/// from constructed `InterpretInt`s, i.e. 1..=128; `bits == 0` would wrap
/// `bits - 1` under checks-off where production debug-panics — never swept.)
fn signed_bounds(bits: u32) -> (i128, i128) {
    if bits == 128 {
        return (i128::MIN, i128::MAX);
    }
    let sign = 1u128 << (bits - 1);
    (-(sign as i128), (sign - 1) as i128)
}

/// interpret.rs:4608-4611, VERBATIM.
fn signed_div_overflows(bits: u32, lhs: i128, rhs: i128) -> bool {
    let (min, _) = signed_bounds(bits);
    lhs == min && rhs == -1
}

/// interpret.rs:4613-4624. VERBATIM control flow; [B1] the UB error is the
/// `ShiftOutOfRange` code; [B5] `u128::from(bits)` -> `bits as u128`.
fn shift_amount(rhs: InterpretInt, bits: u32) -> Result<u32, EvalErr> {
    if rhs.raw >= bits as u128 {
        return Err(EvalErr::ShiftOutOfRange);
    }
    Ok(rhs.raw as u32)
}

/// interpret.rs:4581-4594. VERBATIM structure; [B2] expect -> match/false;
/// [B4] `overflowing_add`/`overflowing_mul` -> wrapping operators + the
/// definitional carry/full-width tests.
fn unsigned_overflow(op: OverflowOp, lhs: InterpretInt, rhs: InterpretInt) -> bool {
    let mask = match int_mask(lhs.bits) {
        Some(m) => m,
        None => return false, // [B2] production: panic (unreachable in-domain)
    };
    match op {
        OverflowOp::AddOverflow => {
            // [B4] production: let (sum, overflow) = lhs.raw.overflowing_add(rhs.raw);
            let sum = lhs.raw + rhs.raw; // wrapping under -C overflow-checks=off [B3]
            let overflow = sum < lhs.raw;
            overflow || sum > mask
        }
        OverflowOp::SubOverflow => lhs.raw < rhs.raw,
        OverflowOp::MulOverflow => {
            // [B4] production: let (product, overflow) = lhs.raw.overflowing_mul(rhs.raw);
            let product = lhs.raw * rhs.raw; // wrapping [B3]
            let overflow = rhs.raw != 0 && lhs.raw > u128::MAX / rhs.raw;
            overflow || product > mask || (rhs.raw != 0 && lhs.raw > mask / rhs.raw)
        }
    }
}

/// interpret.rs:4596-4606, VERBATIM (incl. the `matches!` guard). The
/// `i128::checked_add/sub/mul` calls lower to empty-bodied externs bound to
/// faithful host shims in the test [B7].
fn signed_overflow(op: OverflowOp, lhs: InterpretInt, rhs: InterpretInt) -> bool {
    let (min, max) = signed_bounds(lhs.bits);
    let lhs = lhs.as_signed();
    let rhs = rhs.as_signed();
    let checked = match op {
        OverflowOp::AddOverflow => lhs.checked_add(rhs),
        OverflowOp::SubOverflow => lhs.checked_sub(rhs),
        OverflowOp::MulOverflow => lhs.checked_mul(rhs),
    };
    !matches!(checked, Some(value) if value >= min && value <= max)
}

// ── the eval core (interpret.rs:4186-4373) ──────────────────────────────────

/// interpret.rs:4186-4271. VERBATIM structure, arm ORDER and guard ORDER;
/// [B1] error sites -> EvalErr; [B2] expect -> match; [B3] wrapping_* -> raw
/// operators (checks-off emit); [B6] `shift_amount(..)?` -> explicit match.
pub fn eval_int_binop(op: BinOp, lhs: InterpretInt, rhs: InterpretInt) -> Result<InterpretInt, EvalErr> {
    if lhs.bits != rhs.bits {
        return Err(EvalErr::WidthMismatch);
    }
    let mask = match int_mask(lhs.bits) {
        Some(m) => m,
        None => return Err(EvalErr::InvalidWidthPanic), // [B2]
    };
    let raw = match op {
        BinOp::Add => lhs.raw + rhs.raw, // [B3] wrapping_add
        BinOp::Sub => lhs.raw - rhs.raw, // [B3] wrapping_sub
        BinOp::Mul => lhs.raw * rhs.raw, // [B3] wrapping_mul
        BinOp::And => lhs.raw & rhs.raw,
        BinOp::Or => lhs.raw | rhs.raw,
        BinOp::Xor => lhs.raw ^ rhs.raw,
        BinOp::UDiv => {
            if rhs.raw == 0 {
                return Err(EvalErr::UDivByZero);
            }
            lhs.raw / rhs.raw
        }
        BinOp::URem => {
            if rhs.raw == 0 {
                return Err(EvalErr::URemByZero);
            }
            lhs.raw % rhs.raw
        }
        BinOp::SDiv => {
            let rhs_signed = rhs.as_signed();
            if rhs_signed == 0 {
                return Err(EvalErr::SDivByZero);
            }
            let lhs_signed = lhs.as_signed();
            if signed_div_overflows(lhs.bits, lhs_signed, rhs_signed) {
                return Err(EvalErr::SDivOverflow);
            }
            (lhs_signed / rhs_signed) as u128
        }
        BinOp::SRem => {
            let rhs_signed = rhs.as_signed();
            if rhs_signed == 0 {
                return Err(EvalErr::SRemByZero);
            }
            let lhs_signed = lhs.as_signed();
            if signed_div_overflows(lhs.bits, lhs_signed, rhs_signed) {
                return Err(EvalErr::SRemOverflow);
            }
            (lhs_signed % rhs_signed) as u128
        }
        BinOp::Shl => {
            let amount = match shift_amount(rhs, lhs.bits) {
                // [B6] production: shift_amount(rhs, lhs.bits, block)?
                Ok(a) => a,
                Err(e) => return Err(e),
            };
            lhs.raw << amount
        }
        BinOp::LShr => {
            let amount = match shift_amount(rhs, lhs.bits) {
                Ok(a) => a,
                Err(e) => return Err(e),
            };
            lhs.raw >> amount
        }
        BinOp::AShr => {
            let amount = match shift_amount(rhs, lhs.bits) {
                Ok(a) => a,
                Err(e) => return Err(e),
            };
            (lhs.as_signed() >> amount) as u128
        }
        BinOp::FAdd
        | BinOp::FSub
        | BinOp::FMul
        | BinOp::FDiv
        | BinOp::FRem
        | BinOp::FMin
        | BinOp::FMax => {
            return Err(EvalErr::FloatBinopUnsupported);
        }
    } & mask;
    Ok(InterpretInt {
        bits: lhs.bits,
        signed: lhs.signed,
        raw,
    })
}

/// interpret.rs:4273-4327. VERBATIM structure/order; [B2] expect -> match;
/// [B3] `0u128.wrapping_sub(value.raw)` -> `0u128 - value.raw` (checks-off);
/// [B5] CtPop `u128::from(value.raw.count_ones())` -> the definitional
/// bit-at-a-time popcount loop (checked against native `count_ones`).
pub fn eval_int_unop(op: UnOp, value: InterpretInt) -> Result<InterpretInt, EvalErr> {
    let mask = match int_mask(value.bits) {
        Some(m) => m,
        None => return Err(EvalErr::InvalidWidthPanic), // [B2]
    };
    let raw = match op {
        UnOp::Neg => 0u128 - value.raw, // [B3] 0u128.wrapping_sub(value.raw)
        UnOp::Not => !value.raw,
        UnOp::CtPop => {
            // [B5] production: u128::from(value.raw.count_ones())
            let mut n = value.raw;
            let mut c = 0u128;
            while n != 0 {
                c += n & 1;
                n >>= 1u128;
            }
            c
        }
        UnOp::FNeg
        | UnOp::FAbs
        | UnOp::FSqrt
        | UnOp::FFloor
        | UnOp::FCeil
        | UnOp::FTrunc => {
            return Err(EvalErr::FloatUnopUnsupported);
        }
    } & mask;
    Ok(InterpretInt {
        bits: value.bits,
        signed: value.signed,
        raw,
    })
}

/// interpret.rs:4329-4358. VERBATIM structure; [B6] `eval_int_binop(..)?` ->
/// explicit match.
pub fn eval_int_overflow(
    op: OverflowOp,
    lhs: InterpretInt,
    rhs: InterpretInt,
) -> Result<(InterpretInt, bool), EvalErr> {
    if lhs.bits != rhs.bits {
        return Err(EvalErr::WidthMismatch);
    }
    let result = match eval_int_binop(
        match op {
            OverflowOp::AddOverflow => BinOp::Add,
            OverflowOp::SubOverflow => BinOp::Sub,
            OverflowOp::MulOverflow => BinOp::Mul,
        },
        lhs,
        rhs,
    ) {
        // [B6] production: eval_int_binop(.., block)?
        Ok(v) => v,
        Err(e) => return Err(e),
    };

    let overflow = if lhs.signed {
        signed_overflow(op, lhs, rhs)
    } else {
        unsigned_overflow(op, lhs, rhs)
    };
    Ok((result, overflow))
}

/// interpret.rs:4360-4373, VERBATIM.
pub fn eval_int_icmp(op: ICmpOp, lhs: InterpretInt, rhs: InterpretInt) -> bool {
    match op {
        ICmpOp::Eq => lhs.raw == rhs.raw,
        ICmpOp::Ne => lhs.raw != rhs.raw,
        ICmpOp::Ult => lhs.raw < rhs.raw,
        ICmpOp::Ule => lhs.raw <= rhs.raw,
        ICmpOp::Ugt => lhs.raw > rhs.raw,
        ICmpOp::Uge => lhs.raw >= rhs.raw,
        ICmpOp::Slt => lhs.as_signed() < rhs.as_signed(),
        ICmpOp::Sle => lhs.as_signed() <= rhs.as_signed(),
        ICmpOp::Sgt => lhs.as_signed() > rhs.as_signed(),
        ICmpOp::Sge => lhs.as_signed() >= rhs.as_signed(),
    }
}

// ── tag decoders (harness plumbing, mirrored 1:1 in the test oracles) ───────

fn binop_from_u32(tag: u32) -> BinOp {
    match tag {
        0 => BinOp::Add,
        1 => BinOp::Sub,
        2 => BinOp::Mul,
        3 => BinOp::UDiv,
        4 => BinOp::SDiv,
        5 => BinOp::URem,
        6 => BinOp::SRem,
        7 => BinOp::FAdd,
        8 => BinOp::FSub,
        9 => BinOp::FMul,
        10 => BinOp::FDiv,
        11 => BinOp::FRem,
        12 => BinOp::FMin,
        13 => BinOp::FMax,
        14 => BinOp::And,
        15 => BinOp::Or,
        16 => BinOp::Xor,
        17 => BinOp::Shl,
        18 => BinOp::LShr,
        _ => BinOp::AShr,
    }
}

fn unop_from_u32(tag: u32) -> UnOp {
    match tag {
        0 => UnOp::Neg,
        1 => UnOp::FNeg,
        2 => UnOp::FAbs,
        3 => UnOp::FSqrt,
        4 => UnOp::FFloor,
        5 => UnOp::FCeil,
        6 => UnOp::FTrunc,
        7 => UnOp::Not,
        _ => UnOp::CtPop,
    }
}

fn ovop_from_u32(tag: u32) -> OverflowOp {
    match tag {
        0 => OverflowOp::AddOverflow,
        1 => OverflowOp::SubOverflow,
        _ => OverflowOp::MulOverflow,
    }
}

fn icmp_from_u32(tag: u32) -> ICmpOp {
    match tag {
        0 => ICmpOp::Eq,
        1 => ICmpOp::Ne,
        2 => ICmpOp::Ult,
        3 => ICmpOp::Ule,
        4 => ICmpOp::Ugt,
        5 => ICmpOp::Uge,
        6 => ICmpOp::Slt,
        7 => ICmpOp::Sle,
        8 => ICmpOp::Sgt,
        _ => ICmpOp::Sge,
    }
}

fn err_code(e: EvalErr) -> u64 {
    match e {
        EvalErr::WidthMismatch => 1,
        EvalErr::InvalidWidthPanic => 2,
        EvalErr::UDivByZero => 3,
        EvalErr::URemByZero => 4,
        EvalErr::SDivByZero => 5,
        EvalErr::SDivOverflow => 6,
        EvalErr::SRemByZero => 7,
        EvalErr::SRemOverflow => 8,
        EvalErr::ShiftOutOfRange => 9,
        EvalErr::FloatBinopUnsupported => 10,
        EvalErr::FloatUnopUnsupported => 11,
    }
}

// ── out-PODs + #[no_mangle] mono ROOTS (128-bit values cross BY POINTER) ────

/// POD view of `Result<InterpretInt, EvalErr>`:
/// tag 1 = Ok (bits/signed_/raw valid), tag 0 = Err (err = err_code).
#[repr(C, align(16))]
pub struct EvalOut {
    pub tag: u64,
    pub err: u64,
    pub bits: u32,
    pub signed_: u32,
    pub _pad: u64,
    pub raw: u128,
}

#[no_mangle]
pub fn interp_int_mask_root(bits: u32, out_present: &mut u64, out_mask: &mut u128) {
    match int_mask(bits) {
        Some(m) => {
            *out_present = 1;
            *out_mask = m;
        }
        None => {
            *out_present = 0;
            *out_mask = 0;
        }
    }
}

#[no_mangle]
pub fn interp_signed_bounds_root(bits: u32, out_min: &mut i128, out_max: &mut i128) {
    let (min, max) = signed_bounds(bits);
    *out_min = min;
    *out_max = max;
}

#[no_mangle]
pub fn interp_from_raw_root(
    bits: u32,
    signed_: u32,
    raw: &u128,
    out_present: &mut u64,
    out_bits: &mut u32,
    out_signed: &mut u32,
    out_raw: &mut u128,
) {
    match InterpretInt::from_raw(bits, signed_ != 0, *raw) {
        Some(v) => {
            *out_present = 1;
            *out_bits = v.bits;
            *out_signed = v.signed as u32;
            *out_raw = v.raw;
        }
        None => {
            *out_present = 0;
            *out_bits = 0;
            *out_signed = 0;
            *out_raw = 0;
        }
    }
}

#[no_mangle]
pub fn interp_from_i128_root(
    bits: u32,
    signed_: u32,
    value: &i128,
    out_present: &mut u64,
    out_bits: &mut u32,
    out_signed: &mut u32,
    out_raw: &mut u128,
) {
    match InterpretInt::from_i128(bits, signed_ != 0, *value) {
        Some(v) => {
            *out_present = 1;
            *out_bits = v.bits;
            *out_signed = v.signed as u32;
            *out_raw = v.raw;
        }
        None => {
            *out_present = 0;
            *out_bits = 0;
            *out_signed = 0;
            *out_raw = 0;
        }
    }
}

#[no_mangle]
pub fn interp_as_signed_root(bits: u32, signed_: u32, raw: &u128, out: &mut i128) {
    let v = InterpretInt {
        bits,
        signed: signed_ != 0,
        raw: *raw,
    };
    *out = v.as_signed();
}

#[no_mangle]
pub fn interp_sdiv_overflows_root(bits: u32, lhs: &i128, rhs: &i128) -> u32 {
    signed_div_overflows(bits, *lhs, *rhs) as u32
}

#[no_mangle]
pub fn interp_shift_amount_root(
    rbits: u32,
    rsigned: u32,
    rraw: &u128,
    bits: u32,
    out_tag: &mut u64,
    out_amount: &mut u32,
    out_err: &mut u64,
) {
    let rhs = InterpretInt {
        bits: rbits,
        signed: rsigned != 0,
        raw: *rraw,
    };
    match shift_amount(rhs, bits) {
        Ok(a) => {
            *out_tag = 1;
            *out_amount = a;
            *out_err = 0;
        }
        Err(e) => {
            *out_tag = 0;
            *out_amount = 0;
            *out_err = err_code(e);
        }
    }
}

#[no_mangle]
pub fn interp_icmp_root(
    op_tag: u32,
    lbits: u32,
    lsigned: u32,
    lraw: &u128,
    rbits: u32,
    rsigned: u32,
    rraw: &u128,
) -> u32 {
    let lhs = InterpretInt {
        bits: lbits,
        signed: lsigned != 0,
        raw: *lraw,
    };
    let rhs = InterpretInt {
        bits: rbits,
        signed: rsigned != 0,
        raw: *rraw,
    };
    eval_int_icmp(icmp_from_u32(op_tag), lhs, rhs) as u32
}

#[no_mangle]
pub fn interp_unop_root(op_tag: u32, bits: u32, signed_: u32, raw: &u128, out: &mut EvalOut) {
    let value = InterpretInt {
        bits,
        signed: signed_ != 0,
        raw: *raw,
    };
    match eval_int_unop(unop_from_u32(op_tag), value) {
        Ok(v) => {
            out.tag = 1;
            out.err = 0;
            out.bits = v.bits;
            out.signed_ = v.signed as u32;
            out.raw = v.raw;
        }
        Err(e) => {
            out.tag = 0;
            out.err = err_code(e);
            out.bits = 0;
            out.signed_ = 0;
            out.raw = 0;
        }
    }
}

#[no_mangle]
pub fn interp_binop_root(
    op_tag: u32,
    lbits: u32,
    lsigned: u32,
    lraw: &u128,
    rbits: u32,
    rsigned: u32,
    rraw: &u128,
    out: &mut EvalOut,
) {
    let lhs = InterpretInt {
        bits: lbits,
        signed: lsigned != 0,
        raw: *lraw,
    };
    let rhs = InterpretInt {
        bits: rbits,
        signed: rsigned != 0,
        raw: *rraw,
    };
    match eval_int_binop(binop_from_u32(op_tag), lhs, rhs) {
        Ok(v) => {
            out.tag = 1;
            out.err = 0;
            out.bits = v.bits;
            out.signed_ = v.signed as u32;
            out.raw = v.raw;
        }
        Err(e) => {
            out.tag = 0;
            out.err = err_code(e);
            out.bits = 0;
            out.signed_ = 0;
            out.raw = 0;
        }
    }
}

#[no_mangle]
pub fn interp_overflow_root(
    op_tag: u32,
    lbits: u32,
    lsigned: u32,
    lraw: &u128,
    rbits: u32,
    rsigned: u32,
    rraw: &u128,
    out: &mut EvalOut,
    out_flag: &mut u32,
) {
    let lhs = InterpretInt {
        bits: lbits,
        signed: lsigned != 0,
        raw: *lraw,
    };
    let rhs = InterpretInt {
        bits: rbits,
        signed: rsigned != 0,
        raw: *rraw,
    };
    match eval_int_overflow(ovop_from_u32(op_tag), lhs, rhs) {
        Ok((v, flag)) => {
            out.tag = 1;
            out.err = 0;
            out.bits = v.bits;
            out.signed_ = v.signed as u32;
            out.raw = v.raw;
            *out_flag = flag as u32;
        }
        Err(e) => {
            out.tag = 0;
            out.err = err_code(e);
            out.bits = 0;
            out.signed_ = 0;
            out.raw = 0;
            *out_flag = 0xFF;
        }
    }
}

/// The PINNED-FINDING repro root: byte-for-byte what production writes as
/// `*out = *x as i128` — the frontend lowers this same-width cast to
/// `bitcast u128 -> i128`, which trust-cg ISel cannot lower ("value not
/// defined before use"). Kept as a SEPARATE module so the verified modules
/// above stay bitcast-free while the pin auto-detects the backend fix.
#[no_mangle]
pub fn interp_bitcast_pin_root(x: &u128, out: &mut i128) {
    *out = *x as i128;
}

fn main() {}
