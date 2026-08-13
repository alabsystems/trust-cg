//! TRUST-SELF ROUND 4 (thread R3-B): verifying trust-ir's REFERENCE
//! INTERPRETER integer core — the functions that DEFINE correct integer
//! execution for trust-ir programs (`interpret.rs`) — through the full
//! pipeline Rust -> MIR -> trust-ir (stage1 `trust_ir_mir --mir-emit-closure`)
//! -> trust-cg JIT -> machine code, asserting native Rust == JIT over swept
//! real inputs.
//!
//! WHY SOUNDNESS-CRITICAL: `interpret.rs` is trust-ir's SEMANTIC GROUND
//! TRUTH — the deterministic reference interpreter that differential
//! harnesses (and humans) consult to decide what a trust-ir program MEANS.
//! If Trust miscompiles the interpreter's own `eval_int_binop`, the
//! reference oracle itself lies when run through Trust.
//!
//! New verified functions in this file (13):
//!   * the EVAL CORE (interpret.rs): `eval_int_binop` (all 20 BinOp arms:
//!     wrapping add/sub/mul, udiv/urem/sdiv/srem incl. every
//!     div-by-zero/overflow error path, dynamic shl/lshr/ashr through
//!     `shift_amount`, the float-arm rejections), `eval_int_unop`
//!     (Neg/Not/CtPop + float rejections), `eval_int_icmp` (all 10 ops),
//!     `eval_int_overflow` (add/sub/mul overflow, signed + unsigned)
//!   * the pure helper closure: `int_mask`, `signed_bounds`,
//!     `signed_div_overflows`, `shift_amount`, `unsigned_overflow`,
//!     `signed_overflow`, `InterpretInt::{from_raw, from_i128, as_signed}`
//!     (the last three ALSO cross-checked against the PRODUCTION
//!     `trust_ir::InterpretInt` linked into this test binary, and
//!     `eval_int_binop` cross-checked against the PRODUCTION
//!     `trust_ir::Interpreter` executing one-inst modules — see
//!     `prod_interp_binop`)
//!
//! THIS ROUND'S PINNED BACKEND FINDING (scope-narrows owner item #3): the
//! 128-bit int<->int BITCAST is broken in ISel ON ITS OWN — a standalone
//! `load u128; bitcast u128->i128; store` (or the reverse direction) fails
//! `Pipeline(ISel("value ... not defined before use"))`. Bisect table
//! (hand-minimal modules, all at the rev under test):
//!     add/sub/mul/udiv/urem/and u128            OK
//!     sdiv/srem i128 (operands loaded AS i128)  OK
//!     dynamic shl/lshr u128, dynamic ashr i128  OK
//!     icmp eq i128, select bool                 OK
//!     u128 BLOCK ARGS across condbr/br/switch   OK
//!     bitcast u128<->i128 (either direction)    FAIL (the pinned class)
//! The prior "u128/i128 half-splitting register-pair" class (fold_cast
//! halves, edge_bounds) CONTAINS this bitcast — the bare bitcast is now the
//! now lowered and verified native==JIT in
//! `trust_cg_lowers_int128_bitcast_native_eq_jit`, on a module
//! the FRONTEND emits from plain production-shaped Rust (`*out = *x as i128`).
//! Because the production interpreter spells same-width 128-bit sign
//! reinterprets as `as` casts, the slice carries the [B9] memory-reinterpret
//! rewrite (alloca + typed load — the same bit-identity) so the eval core is
//! verifiable TODAY; drop [B9] when the pin promotes.
//!
//! Slice (verbatim transcription, modeled boundaries [B1]-[B9] documented
//! inline there and summarized at each fixture below):
//!   tests/slices/trust_interp_int_slice.rs
//! Transcribed from trust-ir @ 9e4f5d2 (== the Cargo.lock pin 357750a for
//! interpret.rs/inst.rs; the two revs differ only in lock files) and
//! re-checked against $HOME/trust-ir sources on 2026-07-03.
//!
//! REGEN (per module; NOTE the -C flags — [B3] wrapping semantics):
//!   S=$HOME/trust/build/aarch64-apple-darwin/stage1
//!   cd $HOME/trust-ir/frontend && env -u RUSTUP_TOOLCHAIN RUSTC=$S/bin/rustc \
//!     DYLD_LIBRARY_PATH=$S/lib/rustlib/aarch64-apple-darwin/lib \
//!     $S/bin/cargo run --bin trust_ir_mir -- \
//!     <tests/slices/trust_interp_int_slice.rs> --crate-type=lib \
//!     -C overflow-checks=off -C debug-assertions=off \
//!     --mir-emit-closure <root> <out.tir>
//!
//! WIDE-CONSTANT NOTE: older captured modules spelled `u128::MAX` as
//! `const u128 -1`. TrustIr's v24 one-spelling rule rejects that signed
//! carrier for an unsigned type, and the production lowering now emits the
//! positive `Constant::U128` magnitude. These fixtures use that canonical
//! spelling so validation and codegen exercise the same representation.
//!
//! BUILD-BLOCKER CONTEXT (repo-level, reported to the owner): at authoring
//! time trust-cg HEAD (87e341a + 103719c) does not build against its own
//! Cargo.lock — the FPToSISat/FPToUISat consumer fix references CastOp
//! variants that exist in neither the locked trust-ir (357750a) nor the
//! sibling checkout (9e4f5d2). This file was validated in a worktree at
//! 1ec7170 (the last buildable rev; HEAD differs only by the fail-closed
//! arms for cast ops that never appear in these modules, plus test files).
//!
//! MODELED BOUNDARIES (summary; [B1]-[B9] fully documented in the slice):
//!   [B1] error IDENTITY not error PROSE (fieldless EvalErr, one variant per
//!        production error site; message Strings dropped — format!/String
//!        does not lower);
//!   [B2] the `expect("validated integer width")` panic sites -> sentinel
//!        arms, dead in-domain (harness never sweeps an invalid width into
//!        them; interpret.rs:4649-4658 documents the same invariant);
//!   [B3] `wrapping_*` -> raw operators under `-C overflow-checks=off`
//!        (definitionally identical; keeps the arithmetic IN the JIT);
//!   [B4] `overflowing_add/mul` -> wrapping ops + definitional carry /
//!        full-width tests; [B5] `u128::from` -> `as`, `count_ones` ->
//!        popcount loop; [B6] Result-`?` -> match (Option-`?` KEPT, through
//!        host-bound Try shims); [B7] `i128::checked_add/sub/mul` -> host
//!        shims (the verified fold_binop boundary); [B8] diagnostic-only
//!        `block` params omitted; [B9] 128-bit `as` reinterprets ->
//!        memory round-trip (see the pinned finding above).
//!        EVERY rewrite is differentially checked: the native oracle in this
//!        file is the VERBATIM production text (wrapping_*/overflowing_*/
//!        count_ones/checked_*/expect), so native==JIT over the full sweep
//!        proves each rewrite equivalent on the swept domain.
//!
//! COVERAGE NOTE: gated to aarch64 (the JIT target); on any other host this
//! file compiles to ZERO tests. Run tests ONE AT A TIME
//! (`-- --exact <name> --test-threads=1`): the JIT engine is not thread-safe
//! at suite scale (see jit-parallel-race-2026-06-29.md). Every JIT execution
//! runs inside a WATCHDOG worker thread (hang-class discipline).

#![cfg(target_arch = "aarch64")]

use std::collections::HashMap;
use std::sync::mpsc;
use std::time::Duration;

use trust_cg_codegen::Target;
use trust_cg_codegen::compiler::{Compiler, CompilerConfig};

// ── shared harness ──────────────────────────────────────────────────────────

/// Parse + JIT one embedded module with bound host externs; return the buffer
/// (keep it alive while calling fn pointers bound from it).
fn jit_module_with(
    text: &str,
    what: &str,
    externs: &HashMap<String, *const u8>,
) -> trust_cg_codegen::jit::ExecutableBuffer {
    let module = trust_ir::parser::parse_module(text)
        .unwrap_or_else(|e| panic!("MIR-emitted `{what}` trust-ir text must parse: {e:?}"));
    let config = CompilerConfig::jit_fast(Target::Aarch64);
    Compiler::new(config)
        .compile_module_to_jit(&module, externs)
        .unwrap_or_else(|e| panic!("trust-cg JIT compile of MIR-emitted `{what}` failed: {e:?}"))
        .buffer
}

fn jit_module(text: &str, what: &str) -> trust_cg_codegen::jit::ExecutableBuffer {
    jit_module_with(text, what, &HashMap::new())
}

fn bind(buffer: &trust_cg_codegen::jit::ExecutableBuffer, sym: &str) -> *const u8 {
    buffer
        .get_fn_ptr_bound(sym)
        .unwrap_or_else(|| panic!("JIT symbol `{sym}` not found"))
        .as_ptr()
}

const WATCHDOG_SECS: u64 = 120;

/// Run `worker` (which JITs a module and streams `expected` rows) under the
/// watchdog: the JIT buffer lives (and on a hang is leaked) entirely inside
/// the worker thread, so a hung thread never executes freed machine code;
/// the main thread bounds every wait. Workers enumerate inputs
/// deterministically and echo them in each row, so a stall at row N
/// identifies its input.
fn run_watchdogged<T: Send + 'static>(
    what: &'static str,
    expected: usize,
    worker: impl FnOnce(mpsc::Sender<T>) + Send + 'static,
) -> Vec<T> {
    let (tx, rx) = mpsc::channel::<T>();
    std::thread::spawn(move || worker(tx));
    let mut rows = Vec::with_capacity(expected);
    for i in 0..expected {
        match rx.recv_timeout(Duration::from_secs(WATCHDOG_SECS)) {
            Ok(row) => rows.push(row),
            Err(_) => panic!(
                "JIT `{what}` HUNG (watchdog {WATCHDOG_SECS}s): no progress at row {i} of {expected}"
            ),
        }
    }
    rows
}

// ── the NATIVE ORACLE: the interpreter integer core transcribed VERBATIM
//    from production (interpret.rs / inst.rs — re-checked 2026-07-03),
//    INCLUDING the production `wrapping_*` / `overflowing_*` / `count_ones` /
//    `u128::from` / `checked_*` / `expect` forms that the slice rewrites
//    ([B3]-[B5], [B9]) — so the differential also proves every rewrite. ──────

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum NOp {
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

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum NUnOp {
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

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum NOvOp {
    Add,
    Sub,
    Mul,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum NCmp {
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

/// Mirrors the slice's `EvalErr` (one variant per production error site;
/// numeric codes == the slice's `err_code`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum NErr {
    WidthMismatch,
    #[allow(dead_code)]
    InvalidWidthPanic,
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

fn n_err_code(e: NErr) -> u64 {
    match e {
        NErr::WidthMismatch => 1,
        NErr::InvalidWidthPanic => 2,
        NErr::UDivByZero => 3,
        NErr::URemByZero => 4,
        NErr::SDivByZero => 5,
        NErr::SDivOverflow => 6,
        NErr::SRemByZero => 7,
        NErr::SRemOverflow => 8,
        NErr::ShiftOutOfRange => 9,
        NErr::FloatBinopUnsupported => 10,
        NErr::FloatUnopUnsupported => 11,
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct NInt {
    bits: u32,
    signed: bool,
    raw: u128,
}

impl NInt {
    /// interpret.rs:209-215 VERBATIM.
    fn from_i128(bits: u32, signed: bool, value: i128) -> Option<Self> {
        Some(Self {
            bits,
            signed,
            raw: (value as u128) & n_int_mask(bits)?,
        })
    }
    /// interpret.rs:217-223 VERBATIM.
    fn from_raw(bits: u32, signed: bool, raw: u128) -> Option<Self> {
        Some(Self {
            bits,
            signed,
            raw: raw & n_int_mask(bits)?,
        })
    }
    /// interpret.rs:229-242 VERBATIM (incl. the expect — the harness domain
    /// keeps bits in 1..=128 so it never fires natively either).
    fn as_signed(self) -> i128 {
        if self.bits == 128 {
            return self.raw as i128;
        }
        let mask = n_int_mask(self.bits).expect("validated integer width");
        let sign_bit = 1u128 << (self.bits - 1);
        if self.raw & sign_bit == 0 {
            self.raw as i128
        } else {
            let magnitude = ((!self.raw & mask) + 1) & mask;
            -(magnitude as i128)
        }
    }
}

/// interpret.rs:4659-4665 VERBATIM.
fn n_int_mask(bits: u32) -> Option<u128> {
    match bits {
        1..=127 => Some((1u128 << bits) - 1),
        128 => Some(u128::MAX),
        _ => None,
    }
}

/// interpret.rs:4667-4673 VERBATIM.
fn n_signed_bounds(bits: u32) -> (i128, i128) {
    if bits == 128 {
        return (i128::MIN, i128::MAX);
    }
    let sign = 1u128 << (bits - 1);
    (-(sign as i128), (sign - 1) as i128)
}

/// interpret.rs:4608-4611 VERBATIM.
fn n_signed_div_overflows(bits: u32, lhs: i128, rhs: i128) -> bool {
    let (min, _) = n_signed_bounds(bits);
    lhs == min && rhs == -1
}

/// interpret.rs:4613-4624 (error identity per [B1]).
fn n_shift_amount(rhs: NInt, bits: u32) -> Result<u32, NErr> {
    if rhs.raw >= u128::from(bits) {
        return Err(NErr::ShiftOutOfRange);
    }
    Ok(rhs.raw as u32)
}

/// interpret.rs:4581-4594 VERBATIM (production overflowing_* forms).
fn n_unsigned_overflow(op: NOvOp, lhs: NInt, rhs: NInt) -> bool {
    let mask = n_int_mask(lhs.bits).expect("validated integer width");
    match op {
        NOvOp::Add => {
            let (sum, overflow) = lhs.raw.overflowing_add(rhs.raw);
            overflow || sum > mask
        }
        NOvOp::Sub => lhs.raw < rhs.raw,
        NOvOp::Mul => {
            let (product, overflow) = lhs.raw.overflowing_mul(rhs.raw);
            overflow || product > mask || (rhs.raw != 0 && lhs.raw > mask / rhs.raw)
        }
    }
}

/// interpret.rs:4596-4606 VERBATIM (production checked_* forms).
fn n_signed_overflow(op: NOvOp, lhs: NInt, rhs: NInt) -> bool {
    let (min, max) = n_signed_bounds(lhs.bits);
    let lhs = lhs.as_signed();
    let rhs = rhs.as_signed();
    let checked = match op {
        NOvOp::Add => lhs.checked_add(rhs),
        NOvOp::Sub => lhs.checked_sub(rhs),
        NOvOp::Mul => lhs.checked_mul(rhs),
    };
    !matches!(checked, Some(value) if value >= min && value <= max)
}

/// interpret.rs:4186-4271 (production wrapping_* forms; error identity [B1]).
fn n_eval_int_binop(op: NOp, lhs: NInt, rhs: NInt) -> Result<NInt, NErr> {
    if lhs.bits != rhs.bits {
        return Err(NErr::WidthMismatch);
    }
    let mask = n_int_mask(lhs.bits).expect("validated integer width");
    let raw = match op {
        NOp::Add => lhs.raw.wrapping_add(rhs.raw),
        NOp::Sub => lhs.raw.wrapping_sub(rhs.raw),
        NOp::Mul => lhs.raw.wrapping_mul(rhs.raw),
        NOp::And => lhs.raw & rhs.raw,
        NOp::Or => lhs.raw | rhs.raw,
        NOp::Xor => lhs.raw ^ rhs.raw,
        NOp::UDiv => {
            if rhs.raw == 0 {
                return Err(NErr::UDivByZero);
            }
            lhs.raw / rhs.raw
        }
        NOp::URem => {
            if rhs.raw == 0 {
                return Err(NErr::URemByZero);
            }
            lhs.raw % rhs.raw
        }
        NOp::SDiv => {
            let rhs_signed = rhs.as_signed();
            if rhs_signed == 0 {
                return Err(NErr::SDivByZero);
            }
            let lhs_signed = lhs.as_signed();
            if n_signed_div_overflows(lhs.bits, lhs_signed, rhs_signed) {
                return Err(NErr::SDivOverflow);
            }
            (lhs_signed / rhs_signed) as u128
        }
        NOp::SRem => {
            let rhs_signed = rhs.as_signed();
            if rhs_signed == 0 {
                return Err(NErr::SRemByZero);
            }
            let lhs_signed = lhs.as_signed();
            if n_signed_div_overflows(lhs.bits, lhs_signed, rhs_signed) {
                return Err(NErr::SRemOverflow);
            }
            (lhs_signed % rhs_signed) as u128
        }
        NOp::Shl => {
            let amount = n_shift_amount(rhs, lhs.bits)?;
            lhs.raw << amount
        }
        NOp::LShr => {
            let amount = n_shift_amount(rhs, lhs.bits)?;
            lhs.raw >> amount
        }
        NOp::AShr => {
            let amount = n_shift_amount(rhs, lhs.bits)?;
            (lhs.as_signed() >> amount) as u128
        }
        NOp::FAdd | NOp::FSub | NOp::FMul | NOp::FDiv | NOp::FRem | NOp::FMin | NOp::FMax => {
            return Err(NErr::FloatBinopUnsupported);
        }
    } & mask;
    Ok(NInt {
        bits: lhs.bits,
        signed: lhs.signed,
        raw,
    })
}

/// interpret.rs:4273-4327 (production count_ones form).
fn n_eval_int_unop(op: NUnOp, value: NInt) -> Result<NInt, NErr> {
    let mask = n_int_mask(value.bits).expect("validated integer width");
    let raw = match op {
        NUnOp::Neg => 0u128.wrapping_sub(value.raw),
        NUnOp::Not => !value.raw,
        NUnOp::CtPop => u128::from(value.raw.count_ones()),
        NUnOp::FNeg | NUnOp::FAbs | NUnOp::FSqrt | NUnOp::FFloor | NUnOp::FCeil | NUnOp::FTrunc => {
            return Err(NErr::FloatUnopUnsupported);
        }
    } & mask;
    Ok(NInt {
        bits: value.bits,
        signed: value.signed,
        raw,
    })
}

/// interpret.rs:4329-4358.
fn n_eval_int_overflow(op: NOvOp, lhs: NInt, rhs: NInt) -> Result<(NInt, bool), NErr> {
    if lhs.bits != rhs.bits {
        return Err(NErr::WidthMismatch);
    }
    let result = n_eval_int_binop(
        match op {
            NOvOp::Add => NOp::Add,
            NOvOp::Sub => NOp::Sub,
            NOvOp::Mul => NOp::Mul,
        },
        lhs,
        rhs,
    )?;
    let overflow = if lhs.signed {
        n_signed_overflow(op, lhs, rhs)
    } else {
        n_unsigned_overflow(op, lhs, rhs)
    };
    Ok((result, overflow))
}

/// interpret.rs:4360-4373 VERBATIM.
fn n_eval_int_icmp(op: NCmp, lhs: NInt, rhs: NInt) -> bool {
    match op {
        NCmp::Eq => lhs.raw == rhs.raw,
        NCmp::Ne => lhs.raw != rhs.raw,
        NCmp::Ult => lhs.raw < rhs.raw,
        NCmp::Ule => lhs.raw <= rhs.raw,
        NCmp::Ugt => lhs.raw > rhs.raw,
        NCmp::Uge => lhs.raw >= rhs.raw,
        NCmp::Slt => lhs.as_signed() < rhs.as_signed(),
        NCmp::Sle => lhs.as_signed() <= rhs.as_signed(),
        NCmp::Sgt => lhs.as_signed() > rhs.as_signed(),
        NCmp::Sge => lhs.as_signed() >= rhs.as_signed(),
    }
}

fn n_binop_from_tag(tag: u32) -> NOp {
    match tag {
        0 => NOp::Add,
        1 => NOp::Sub,
        2 => NOp::Mul,
        3 => NOp::UDiv,
        4 => NOp::SDiv,
        5 => NOp::URem,
        6 => NOp::SRem,
        7 => NOp::FAdd,
        8 => NOp::FSub,
        9 => NOp::FMul,
        10 => NOp::FDiv,
        11 => NOp::FRem,
        12 => NOp::FMin,
        13 => NOp::FMax,
        14 => NOp::And,
        15 => NOp::Or,
        16 => NOp::Xor,
        17 => NOp::Shl,
        18 => NOp::LShr,
        _ => NOp::AShr,
    }
}

fn n_unop_from_tag(tag: u32) -> NUnOp {
    match tag {
        0 => NUnOp::Neg,
        1 => NUnOp::FNeg,
        2 => NUnOp::FAbs,
        3 => NUnOp::FSqrt,
        4 => NUnOp::FFloor,
        5 => NUnOp::FCeil,
        6 => NUnOp::FTrunc,
        7 => NUnOp::Not,
        _ => NUnOp::CtPop,
    }
}

fn n_ovop_from_tag(tag: u32) -> NOvOp {
    match tag {
        0 => NOvOp::Add,
        1 => NOvOp::Sub,
        _ => NOvOp::Mul,
    }
}

fn n_icmp_from_tag(tag: u32) -> NCmp {
    match tag {
        0 => NCmp::Eq,
        1 => NCmp::Ne,
        2 => NCmp::Ult,
        3 => NCmp::Ule,
        4 => NCmp::Ugt,
        5 => NCmp::Uge,
        6 => NCmp::Slt,
        7 => NCmp::Sle,
        8 => NCmp::Sgt,
        _ => NCmp::Sge,
    }
}

// ── sweep menus ─────────────────────────────────────────────────────────────

const WIDTHS: [u32; 5] = [8, 16, 32, 64, 128];

fn mask_of(bits: u32) -> u128 {
    if bits == 128 {
        u128::MAX
    } else {
        (1u128 << bits) - 1
    }
}

/// Per-width raw menu: boundary/sign/pattern probes, all pre-masked to the
/// width (the production `InterpretInt` invariant: `raw` is always masked).
fn raw_menu(bits: u32) -> Vec<u128> {
    let m = mask_of(bits);
    let sign = 1u128 << (bits - 1);
    let mut v = vec![
        0,
        1 & m,
        2 & m,
        3 & m,
        5 & m,
        7 & m,
        8 & m,
        63 & m,
        64 & m,
        127 & m,
        128 & m,
        m,
        m - 1,
        m / 2,
        m / 2 + 1,
        sign & m,
        sign.wrapping_sub(1) & m,
        (sign + 1) & m,
        0xAAAA_AAAA_AAAA_AAAA_AAAA_AAAA_AAAA_AAAA & m,
        0x0123_4567_89AB_CDEF_0123_4567_89AB_CDEF & m,
    ];
    v.sort_unstable();
    v.dedup();
    v
}

/// Smaller pair menu for the binop/overflow cross products.
fn pair_menu(bits: u32) -> Vec<u128> {
    let m = mask_of(bits);
    let sign = 1u128 << (bits - 1);
    let mut v = vec![
        0,
        1 & m,
        2 & m,
        3 & m,
        7 & m,
        64 & m,
        m,
        m - 1,
        m / 2,
        sign & m,
        sign.wrapping_sub(1) & m,
        0xAAAA_AAAA_AAAA_AAAA_AAAA_AAAA_AAAA_AAAA & m,
    ];
    v.sort_unstable();
    v.dedup();
    v
}

// ── PRODUCTION-LINKED oracle helpers ────────────────────────────────────────
//
// `trust_ir::InterpretInt` (from_raw/from_i128/as_signed/as_unsigned) is PUB
// and linked into this test binary: those rows are checked against the REAL
// production code, not just the transcription. For the (private)
// `eval_int_binop`, `prod_interp_binop` executes a one-instruction module
// through the PUB production `Interpreter`, whose Inst-level eval routes
// into the production `eval_int_binop` — wiring the production semantics
// into the differential for every well-typed sampled row.

/// Execute `%2 = <op> <ty> %0, %1; ret %2` through the production
/// interpreter. Returns Ok(bits, signed, raw) or Err(code).
fn prod_interp_binop(
    op_txt: &str,
    ty_txt: &str,
    ty: trust_ir::Ty,
    lhs_raw: u128,
    rhs_raw: u128,
) -> Result<(u32, bool, u128), trust_ir::InterpretErrorCode> {
    let text = format!(
        "; TrustIr text format v1\nmodule \"oracle\"\n\nfuncty.0 = ({ty_txt}, {ty_txt}) -> ({ty_txt})\n\nfn @t(functy.0) {{\nbb0(%0: {ty_txt}, %1: {ty_txt}):\n    %2 = {op_txt} {ty_txt} %0, %1\n    ret %2\n}}\n"
    );
    let module = trust_ir::parser::parse_module(&text)
        .unwrap_or_else(|e| panic!("oracle module must parse: {e:?}\n{text}"));
    let interp = trust_ir::Interpreter::with_module(&module);
    let lhs =
        trust_ir::InterpretValue::int(ty.clone(), lhs_raw as i128).expect("oracle arg must build");
    let rhs =
        trust_ir::InterpretValue::int(ty.clone(), rhs_raw as i128).expect("oracle arg must build");
    match interp.execute_function(&module.functions[0], [lhs, rhs]) {
        Ok(outcome) => {
            let int = outcome.returns[0]
                .as_int()
                .expect("oracle result must be an int");
            Ok((int.bits, int.signed, int.raw))
        }
        Err(e) => Err(e.code),
    }
}

// ── host shims (layouts read off the emitted modules, documented here) ──────

/// `Option<u128>` / `ControlFlow<Option<Infallible>, u128>` — the 16-byte-tag
/// pair ABI: { tag: i128 @0, payload: u128 @16 } (Option: 0=None/1=Some;
/// ControlFlow: 0=Continue/1=Break(None)). Read off `InterpretInt__from_raw`
/// bb1-bb4 in the from_raw module.
#[repr(C, align(16))]
struct PairU128 {
    tag: i128,
    payload: u128,
}

/// `<Option<u128> as Try>::branch` — Some(v) -> Continue(v), None -> Break.
unsafe extern "C" fn shim_try_branch_u128(out: *mut PairU128, opt: *const PairU128) {
    unsafe {
        if (*opt).tag == 1 {
            (*out).tag = 0;
            (*out).payload = (*opt).payload;
        } else {
            (*out).tag = 1;
            (*out).payload = 0;
        }
    }
}

/// `Option<InterpretInt>` — 32 bytes, NICHE layout (the `signed: bool` byte):
/// { raw: u128 @0, bits: u32 @16, signed/tag: u8 @20 } with tag byte 2 = None
/// (0/1 = Some(signed=false/true)). Read off the roots' `== 2` decode and
/// `InterpretInt__from_raw` bb4's field stores. `from_residual` writes None.
unsafe extern "C" fn shim_from_residual_opt_interp_int(out: *mut u8) {
    unsafe {
        std::ptr::write_bytes(out, 0, 32);
        *out.add(20) = 2;
    }
}

/// `Option<i128>` — the 16-byte-tag pair ABI { tag: i128 @0 (0=None,1=Some),
/// value: i128 @16 } (same as the verified fold_binop boundary).
#[repr(C, align(16))]
struct PairI128 {
    tag: i128,
    payload: i128,
}

unsafe extern "C" fn shim_checked_add_i128(out: *mut PairI128, a: i128, b: i128) {
    unsafe {
        match a.checked_add(b) {
            Some(v) => {
                (*out).tag = 1;
                (*out).payload = v;
            }
            None => {
                (*out).tag = 0;
                (*out).payload = 0;
            }
        }
    }
}

unsafe extern "C" fn shim_checked_sub_i128(out: *mut PairI128, a: i128, b: i128) {
    unsafe {
        match a.checked_sub(b) {
            Some(v) => {
                (*out).tag = 1;
                (*out).payload = v;
            }
            None => {
                (*out).tag = 0;
                (*out).payload = 0;
            }
        }
    }
}

unsafe extern "C" fn shim_checked_mul_i128(out: *mut PairI128, a: i128, b: i128) {
    unsafe {
        match a.checked_mul(b) {
            Some(v) => {
                (*out).tag = 1;
                (*out).payload = v;
            }
            None => {
                (*out).tag = 0;
                (*out).payload = 0;
            }
        }
    }
}

// NOTE: the crate-hash suffix in these mangled names derives from the slice
// file path/name; regenerating from a different path changes the suffix
// (update alongside the embedded IR).
const EXT_TRY_BRANCH_U128: &str = "_RNvXsJ_NtCs2EYQwhfuABO_4core6optionINtB5_6OptionoENtNtNtB7_3ops9try_trait3Try6branchCserZe6P5R4Ij_22trust_interp_int_slice";
const EXT_FROM_RESIDUAL_OPT_INT: &str = "_RNvXsK_NtCs2EYQwhfuABO_4core6optionINtB5_6OptionNtCserZe6P5R4Ij_22trust_interp_int_slice12InterpretIntEINtNtNtB7_3ops9try_trait12FromResidualIBy_NtNtB7_7convert10InfallibleEE13from_residualBM_";
const EXT_CHECKED_ADD_I128: &str =
    "_RNvMs2_NtCs2EYQwhfuABO_4core3numn11checked_addCserZe6P5R4Ij_22trust_interp_int_slice";
const EXT_CHECKED_SUB_I128: &str =
    "_RNvMs2_NtCs2EYQwhfuABO_4core3numn11checked_subCserZe6P5R4Ij_22trust_interp_int_slice";
const EXT_CHECKED_MUL_I128: &str =
    "_RNvMs2_NtCs2EYQwhfuABO_4core3numn11checked_mulCserZe6P5R4Ij_22trust_interp_int_slice";

/// Extern bindings as Send-able (symbol, address) pairs — fn addresses cross
/// into the watchdog worker as `usize` (raw pointers are not Send).
fn from_variant_externs() -> Vec<(&'static str, usize)> {
    vec![
        (
            EXT_TRY_BRANCH_U128,
            shim_try_branch_u128 as *const () as usize,
        ),
        (
            EXT_FROM_RESIDUAL_OPT_INT,
            shim_from_residual_opt_interp_int as *const () as usize,
        ),
    ]
}

fn checked_externs() -> Vec<(&'static str, usize)> {
    vec![
        (
            EXT_CHECKED_ADD_I128,
            shim_checked_add_i128 as *const () as usize,
        ),
        (
            EXT_CHECKED_SUB_I128,
            shim_checked_sub_i128 as *const () as usize,
        ),
        (
            EXT_CHECKED_MUL_I128,
            shim_checked_mul_i128 as *const () as usize,
        ),
    ]
}

fn externs_map(pairs: &[(&'static str, usize)]) -> HashMap<String, *const u8> {
    pairs
        .iter()
        .map(|&(name, addr)| (name.to_string(), addr as *const u8))
        .collect()
}

/// Mirror of the slice's `EvalOut` POD (offsets read off the emitted roots:
/// tag@0, err@8, bits@16, signed_@20, raw@32; size 48).
#[repr(C, align(16))]
#[derive(Clone, Copy)]
struct EvalOutC {
    tag: u64,
    err: u64,
    bits: u32,
    signed_: u32,
    _pad: u64,
    raw: u128,
}

impl EvalOutC {
    fn poisoned() -> Self {
        EvalOutC {
            tag: 0xDEAD,
            err: 0xDEAD,
            bits: 0xDEAD_BEEF,
            signed_: 0xDEAD_BEEF,
            _pad: 0,
            raw: 0xDEAD,
        }
    }
}

/// Flattened JIT result row for the eval fns.
type EvRow = (u64, u64, u32, u32, u128);

fn ev_of(out: &EvalOutC) -> EvRow {
    (out.tag, out.err, out.bits, out.signed_, out.raw)
}

/// The expected EvRow for a native Result.
fn ev_expect(res: Result<NInt, NErr>) -> EvRow {
    match res {
        Ok(v) => (1, 0, v.bits, v.signed as u32, v.raw),
        Err(e) => (0, n_err_code(e), 0, 0, 0),
    }
}

/// VERBATIM MIR-closure emit of `interp_int_mask_root` (slice:
/// tests/slices/trust_interp_int_slice.rs; regen per the file header).
/// Emit reported: 1610 bytes; 2 closure members. The captured wide constant was
/// migrated to TrustIr's canonical `Constant::U128` spelling. Extern-free.
const INT_MASK_IR: &str = r#"; TrustIr text format v1
module "mir::closure::interp_int_mask_root"

functy.0 = (u32, ptr, ptr) -> ()

functy.1 = (ptr, u32) -> ()

fn @interp_int_mask_root(functy.0) {
bb0(%0: u32, %1: ptr, %2: ptr):
    %9 = alloca (i128, i128), align 16
    call @func.1(%9, %0)
    br bb1(%1, %2)
bb1(%3: ptr, %4: ptr):
    %10 = load i128, ptr %9
    %11 = trunc i128 %10 to i64
    switch %11 [ 0: bb3(%3, %4) 1: bb4(%3, %4) default: bb2 ]
bb2:
    unreachable
bb3(%5: ptr, %6: ptr):
    %12 = const u64 0
    store u64 %12, ptr %5
    %13 = const u128 0
    store u128 %13, ptr %6
    br bb5
bb4(%7: ptr, %8: ptr):
    %14 = const i64 16
    %15 = gep i8, ptr %9, %14
    %16 = load u128, ptr %15
    %17 = const u64 1
    store u64 %17, ptr %7
    store u128 %16, ptr %8
    br bb5
bb5:
    ret
}

fn @int_mask(functy.1) {
bb0(%0: ptr, %1: u32):
    %5 = const u32 1
    %6 = icmp ule u32 %5, %1
    condbr %6, bb4(%1), bb3(%1)
bb1:
    %7 = const i128 0
    store i128 %7, ptr %0
    br bb6
bb2(%2: u32):
    %8 = const u128 1
    %9 = zext u32 %2 to u128
    %10 = shl u128 %8, %9
    %11 = const u128 1
    %12 = sub u128 %10, %11
    %13 = const i64 16
    %14 = gep i8, ptr %0, %13
    store u128 %12, ptr %14
    %15 = const i128 1
    store i128 %15, ptr %0
    br bb6
bb3(%3: u32):
    switch %3 [ 128: bb5 default: bb1 ]
bb4(%4: u32):
    %16 = const u32 127
    %17 = icmp ule u32 %4, %16
    condbr %17, bb2(%4), bb3(%4)
bb5:
    %18 = const u128 340282366920938463463374607431768211455
    %19 = const i64 16
    %20 = gep i8, ptr %0, %19
    store u128 %18, ptr %20
    %21 = const i128 1
    store i128 %21, ptr %0
    br bb6
bb6:
    ret
}
"#;

/// VERBATIM emit of `interp_signed_bounds_root`: 1609 bytes; 3 closure
/// members (root + signed_bounds + u128_as_i128 [B9]); validate_module = 0;
/// re-parse OK. Extern-free.
const SIGNED_BOUNDS_IR: &str = r#"; TrustIr text format v1
module "mir::closure::interp_signed_bounds_root"

functy.0 = (u32, ptr, ptr) -> ()

functy.1 = (ptr, u32) -> ()

functy.2 = (u128) -> (i128)

fn @interp_signed_bounds_root(functy.0) {
bb0(%0: u32, %1: ptr, %2: ptr):
    %5 = alloca (i128, i128), align 16
    call @func.1(%5, %0)
    br bb1(%1, %2)
bb1(%3: ptr, %4: ptr):
    %6 = load i128, ptr %5
    %7 = const i64 16
    %8 = gep i8, ptr %5, %7
    %9 = load i128, ptr %8
    store i128 %6, ptr %3
    store i128 %9, ptr %4
    ret
}

fn @signed_bounds(functy.1) {
bb0(%0: ptr, %1: u32):
    %7 = const u32 128
    %8 = icmp eq u32 %1, %7
    condbr %8, bb1, bb2(%1)
bb1:
    %9 = const i128 -170141183460469231731687303715884105728
    store i128 %9, ptr %0
    %10 = const i128 170141183460469231731687303715884105727
    %11 = const i64 16
    %12 = gep i8, ptr %0, %11
    store i128 %10, ptr %12
    br bb5
bb2(%2: u32):
    %13 = const u32 1
    %14 = sub u32 %2, %13
    %15 = const u128 1
    %16 = zext u32 %14 to u128
    %17 = shl u128 %15, %16
    %18 = call @func.2(%17)
    br bb3(%17, %18)
bb3(%3: u128, %4: i128):
    %19 = neg i128 %4
    %20 = const u128 1
    %21 = sub u128 %3, %20
    %22 = call @func.2(%21)
    br bb4(%19, %22)
bb4(%5: i128, %6: i128):
    store i128 %5, ptr %0
    %23 = const i64 16
    %24 = gep i8, ptr %0, %23
    store i128 %6, ptr %24
    br bb5
bb5:
    ret
}

fn @u128_as_i128(functy.2) {
bb0(%0: u128):
    %1 = alloca i128, align 16
    %2 = alloca i64, align 8
    store u128 %0, ptr %1
    store ptr %1, ptr %2
    %3 = load ptr, ptr %2
    %4 = load i128, ptr %3
    ret %4
}
"#;

/// VERBATIM emit of `interp_from_raw_root`: 4189 bytes; 3 closure members;
/// canonical wide constants; re-parse OK.
/// Imports: the `Option<u128>` `Try::branch` + `Option<InterpretInt>`
/// `FromResidual` empty-extern shims ([B6] — the production `?`), host-bound.
const FROM_RAW_IR: &str = r#"; TrustIr text format v1
module "mir::closure::interp_from_raw_root"

functy.0 = (u32, u32, ptr, ptr, ptr, ptr, ptr) -> ()

functy.1 = (ptr, ptr) -> ()

functy.2 = (ptr) -> ()

functy.3 = (ptr, u32, bool, u128) -> ()

functy.4 = (ptr, u32) -> ()

fn @interp_from_raw_root(functy.0) {
bb0(%0: u32, %1: u32, %2: ptr, %3: ptr, %4: ptr, %5: ptr, %6: ptr):
    %19 = alloca (i128, i128), align 16
    %20 = alloca (i128, i128), align 16
    %21 = const u32 0
    %22 = icmp ne u32 %1, %21
    %23 = load u128, ptr %2
    call @func.3(%19, %0, %22, %23)
    br bb1(%3, %4, %5, %6)
bb1(%7: ptr, %8: ptr, %9: ptr, %10: ptr):
    %24 = const i64 20
    %25 = gep i8, ptr %19, %24
    %26 = load i8, ptr %25
    %27 = const i8 2
    %28 = icmp eq i8 %26, %27
    %29 = const i64 0
    %30 = const i64 1
    %31 = select i64 %28, %29, %30
    switch %31 [ 0: bb3(%7, %8, %9, %10) 1: bb4(%7, %8, %9, %10) default: bb2 ]
bb2:
    unreachable
bb3(%11: ptr, %12: ptr, %13: ptr, %14: ptr):
    %32 = const u64 0
    store u64 %32, ptr %11
    %33 = const u32 0
    store u32 %33, ptr %12
    %34 = const u32 0
    store u32 %34, ptr %13
    %35 = const u128 0
    store u128 %35, ptr %14
    br bb5
bb4(%15: ptr, %16: ptr, %17: ptr, %18: ptr):
    %36 = load i128, ptr %19
    store i128 %36, ptr %20
    %37 = const i64 16
    %38 = gep i8, ptr %19, %37
    %39 = const i64 16
    %40 = gep i8, ptr %20, %39
    %41 = load i128, ptr %38
    store i128 %41, ptr %40
    %42 = const u64 1
    store u64 %42, ptr %15
    %43 = const i64 16
    %44 = gep i8, ptr %20, %43
    %45 = load u32, ptr %44
    store u32 %45, ptr %16
    %46 = const i64 20
    %47 = gep i8, ptr %20, %46
    %48 = load bool, ptr %47
    %49 = const u32 1
    %50 = const u32 0
    %51 = select u32 %48, %49, %50
    store u32 %51, ptr %17
    %52 = load u128, ptr %20
    store u128 %52, ptr %18
    br bb5
bb5:
    ret
}

fn @_RNvXsJ_NtCs2EYQwhfuABO_4core6optionINtB5_6OptionoENtNtNtB7_3ops9try_trait3Try6branchCserZe6P5R4Ij_22trust_interp_int_slice(functy.1) {
}

fn @_RNvXsK_NtCs2EYQwhfuABO_4core6optionINtB5_6OptionNtCserZe6P5R4Ij_22trust_interp_int_slice12InterpretIntEINtNtNtB7_3ops9try_trait12FromResidualIBy_NtNtB7_7convert10InfallibleEE13from_residualBM_(functy.2) {
}

fn @InterpretInt__from_raw(functy.3) {
bb0(%0: ptr, %1: u32, %2: bool, %3: u128):
    %13 = alloca (i128, i128), align 16
    %14 = alloca (i128, i128), align 16
    %15 = alloca (i128, i128), align 16
    call @func.4(%15, %1)
    br bb1(%1, %2, %3)
bb1(%4: u32, %5: bool, %6: u128):
    call @func.1(%14, %15)
    br bb2(%4, %5, %6)
bb2(%7: u32, %8: bool, %9: u128):
    %16 = load i128, ptr %14
    %17 = trunc i128 %16 to i64
    switch %17 [ 0: bb4(%7, %8, %9) 1: bb5 default: bb3 ]
bb3:
    unreachable
bb4(%10: u32, %11: bool, %12: u128):
    %18 = const i64 16
    %19 = gep i8, ptr %14, %18
    %20 = load u128, ptr %19
    %21 = and u128 %12, %20
    %22 = const i64 16
    %23 = gep i8, ptr %13, %22
    store u32 %10, ptr %23
    %24 = const i64 20
    %25 = gep i8, ptr %13, %24
    store bool %11, ptr %25
    store u128 %21, ptr %13
    %26 = load i128, ptr %13
    store i128 %26, ptr %0
    %27 = const i64 16
    %28 = gep i8, ptr %13, %27
    %29 = const i64 16
    %30 = gep i8, ptr %0, %29
    %31 = load i128, ptr %28
    store i128 %31, ptr %30
    br bb6
bb5:
    call @func.2(%0)
    br bb6
bb6:
    ret
}

fn @int_mask(functy.4) {
bb0(%0: ptr, %1: u32):
    %5 = const u32 1
    %6 = icmp ule u32 %5, %1
    condbr %6, bb4(%1), bb3(%1)
bb1:
    %7 = const i128 0
    store i128 %7, ptr %0
    br bb6
bb2(%2: u32):
    %8 = const u128 1
    %9 = zext u32 %2 to u128
    %10 = shl u128 %8, %9
    %11 = const u128 1
    %12 = sub u128 %10, %11
    %13 = const i64 16
    %14 = gep i8, ptr %0, %13
    store u128 %12, ptr %14
    %15 = const i128 1
    store i128 %15, ptr %0
    br bb6
bb3(%3: u32):
    switch %3 [ 128: bb5 default: bb1 ]
bb4(%4: u32):
    %16 = const u32 127
    %17 = icmp ule u32 %4, %16
    condbr %17, bb2(%4), bb3(%4)
bb5:
    %18 = const u128 340282366920938463463374607431768211455
    %19 = const i64 16
    %20 = gep i8, ptr %0, %19
    store u128 %18, ptr %20
    %21 = const i128 1
    store i128 %21, ptr %0
    br bb6
bb6:
    ret
}
"#;

/// VERBATIM emit of `interp_from_i128_root`: 4534 bytes; 4 closure members
/// (+ i128_as_u128 [B9]); canonical wide constants; re-parse OK.
/// Same two Try imports as FROM_RAW_IR.
const FROM_I128_IR: &str = r#"; TrustIr text format v1
module "mir::closure::interp_from_i128_root"

functy.0 = (u32, u32, ptr, ptr, ptr, ptr, ptr) -> ()

functy.1 = (ptr, ptr) -> ()

functy.2 = (ptr) -> ()

functy.3 = (ptr, u32, bool, i128) -> ()

functy.4 = (i128) -> (u128)

functy.5 = (ptr, u32) -> ()

fn @interp_from_i128_root(functy.0) {
bb0(%0: u32, %1: u32, %2: ptr, %3: ptr, %4: ptr, %5: ptr, %6: ptr):
    %19 = alloca (i128, i128), align 16
    %20 = alloca (i128, i128), align 16
    %21 = const u32 0
    %22 = icmp ne u32 %1, %21
    %23 = load i128, ptr %2
    call @func.3(%19, %0, %22, %23)
    br bb1(%3, %4, %5, %6)
bb1(%7: ptr, %8: ptr, %9: ptr, %10: ptr):
    %24 = const i64 20
    %25 = gep i8, ptr %19, %24
    %26 = load i8, ptr %25
    %27 = const i8 2
    %28 = icmp eq i8 %26, %27
    %29 = const i64 0
    %30 = const i64 1
    %31 = select i64 %28, %29, %30
    switch %31 [ 0: bb3(%7, %8, %9, %10) 1: bb4(%7, %8, %9, %10) default: bb2 ]
bb2:
    unreachable
bb3(%11: ptr, %12: ptr, %13: ptr, %14: ptr):
    %32 = const u64 0
    store u64 %32, ptr %11
    %33 = const u32 0
    store u32 %33, ptr %12
    %34 = const u32 0
    store u32 %34, ptr %13
    %35 = const u128 0
    store u128 %35, ptr %14
    br bb5
bb4(%15: ptr, %16: ptr, %17: ptr, %18: ptr):
    %36 = load i128, ptr %19
    store i128 %36, ptr %20
    %37 = const i64 16
    %38 = gep i8, ptr %19, %37
    %39 = const i64 16
    %40 = gep i8, ptr %20, %39
    %41 = load i128, ptr %38
    store i128 %41, ptr %40
    %42 = const u64 1
    store u64 %42, ptr %15
    %43 = const i64 16
    %44 = gep i8, ptr %20, %43
    %45 = load u32, ptr %44
    store u32 %45, ptr %16
    %46 = const i64 20
    %47 = gep i8, ptr %20, %46
    %48 = load bool, ptr %47
    %49 = const u32 1
    %50 = const u32 0
    %51 = select u32 %48, %49, %50
    store u32 %51, ptr %17
    %52 = load u128, ptr %20
    store u128 %52, ptr %18
    br bb5
bb5:
    ret
}

fn @_RNvXsJ_NtCs2EYQwhfuABO_4core6optionINtB5_6OptionoENtNtNtB7_3ops9try_trait3Try6branchCserZe6P5R4Ij_22trust_interp_int_slice(functy.1) {
}

fn @_RNvXsK_NtCs2EYQwhfuABO_4core6optionINtB5_6OptionNtCserZe6P5R4Ij_22trust_interp_int_slice12InterpretIntEINtNtNtB7_3ops9try_trait12FromResidualIBy_NtNtB7_7convert10InfallibleEE13from_residualBM_(functy.2) {
}

fn @InterpretInt__from_i128(functy.3) {
bb0(%0: ptr, %1: u32, %2: bool, %3: i128):
    %16 = alloca (i128, i128), align 16
    %17 = alloca (i128, i128), align 16
    %18 = alloca (i128, i128), align 16
    %19 = call @func.4(%3)
    br bb1(%1, %2, %19)
bb1(%4: u32, %5: bool, %6: u128):
    call @func.5(%18, %4)
    br bb2(%4, %5, %6)
bb2(%7: u32, %8: bool, %9: u128):
    call @func.1(%17, %18)
    br bb3(%7, %8, %9)
bb3(%10: u32, %11: bool, %12: u128):
    %20 = load i128, ptr %17
    %21 = trunc i128 %20 to i64
    switch %21 [ 0: bb5(%10, %11, %12) 1: bb6 default: bb4 ]
bb4:
    unreachable
bb5(%13: u32, %14: bool, %15: u128):
    %22 = const i64 16
    %23 = gep i8, ptr %17, %22
    %24 = load u128, ptr %23
    %25 = and u128 %15, %24
    %26 = const i64 16
    %27 = gep i8, ptr %16, %26
    store u32 %13, ptr %27
    %28 = const i64 20
    %29 = gep i8, ptr %16, %28
    store bool %14, ptr %29
    store u128 %25, ptr %16
    %30 = load i128, ptr %16
    store i128 %30, ptr %0
    %31 = const i64 16
    %32 = gep i8, ptr %16, %31
    %33 = const i64 16
    %34 = gep i8, ptr %0, %33
    %35 = load i128, ptr %32
    store i128 %35, ptr %34
    br bb7
bb6:
    call @func.2(%0)
    br bb7
bb7:
    ret
}

fn @i128_as_u128(functy.4) {
bb0(%0: i128):
    %1 = alloca i128, align 16
    %2 = alloca i64, align 8
    store i128 %0, ptr %1
    store ptr %1, ptr %2
    %3 = load ptr, ptr %2
    %4 = load u128, ptr %3
    ret %4
}

fn @int_mask(functy.5) {
bb0(%0: ptr, %1: u32):
    %5 = const u32 1
    %6 = icmp ule u32 %5, %1
    condbr %6, bb4(%1), bb3(%1)
bb1:
    %7 = const i128 0
    store i128 %7, ptr %0
    br bb6
bb2(%2: u32):
    %8 = const u128 1
    %9 = zext u32 %2 to u128
    %10 = shl u128 %8, %9
    %11 = const u128 1
    %12 = sub u128 %10, %11
    %13 = const i64 16
    %14 = gep i8, ptr %0, %13
    store u128 %12, ptr %14
    %15 = const i128 1
    store i128 %15, ptr %0
    br bb6
bb3(%3: u32):
    switch %3 [ 128: bb5 default: bb1 ]
bb4(%4: u32):
    %16 = const u32 127
    %17 = icmp ule u32 %4, %16
    condbr %17, bb2(%4), bb3(%4)
bb5:
    %18 = const u128 340282366920938463463374607431768211455
    %19 = const i64 16
    %20 = gep i8, ptr %0, %19
    store u128 %18, ptr %20
    %21 = const i128 1
    store i128 %21, ptr %0
    br bb6
bb6:
    ret
}
"#;

/// VERBATIM emit of `interp_as_signed_root`: 3164 bytes; 4 closure members;
/// canonical wide constants; re-parse OK. Extern-free.
const AS_SIGNED_IR: &str = r#"; TrustIr text format v1
module "mir::closure::interp_as_signed_root"

functy.0 = (u32, u32, ptr, ptr) -> ()

functy.1 = (ptr) -> (i128)

functy.2 = (u128) -> (i128)

functy.3 = (ptr, u32) -> ()

fn @interp_as_signed_root(functy.0) {
bb0(%0: u32, %1: u32, %2: ptr, %3: ptr):
    %6 = alloca (i128, i128), align 16
    %7 = const u32 0
    %8 = icmp ne u32 %1, %7
    %9 = load u128, ptr %2
    %10 = const i64 16
    %11 = gep i8, ptr %6, %10
    store u32 %0, ptr %11
    %12 = const i64 20
    %13 = gep i8, ptr %6, %12
    store bool %8, ptr %13
    store u128 %9, ptr %6
    %14 = call @func.1(%6)
    br bb1(%3, %14)
bb1(%4: ptr, %5: i128):
    store i128 %5, ptr %4
    ret
}

fn @InterpretInt__as_signed(functy.1) {
bb0(%0: ptr):
    %4 = alloca (i128, i128), align 16
    %5 = const i64 16
    %6 = gep i8, ptr %0, %5
    %7 = load u32, ptr %6
    %8 = const u32 128
    %9 = icmp eq u32 %7, %8
    condbr %9, bb1, bb2
bb1:
    %10 = load u128, ptr %0
    %11 = call @func.2(%10)
    br bb10(%11)
bb2:
    %12 = const i64 16
    %13 = gep i8, ptr %0, %12
    %14 = load u32, ptr %13
    call @func.3(%4, %14)
    br bb3
bb3:
    %15 = load i128, ptr %4
    %16 = trunc i128 %15 to i64
    switch %16 [ 0: bb5 1: bb6 default: bb4 ]
bb4:
    unreachable
bb5:
    %17 = const i128 0
    br bb10(%17)
bb6:
    %18 = const i64 16
    %19 = gep i8, ptr %4, %18
    %20 = load u128, ptr %19
    %21 = const i64 16
    %22 = gep i8, ptr %0, %21
    %23 = load u32, ptr %22
    %24 = const u32 1
    %25 = sub u32 %23, %24
    %26 = const u128 1
    %27 = zext u32 %25 to u128
    %28 = shl u128 %26, %27
    %29 = load u128, ptr %0
    %30 = and u128 %29, %28
    %31 = const u128 0
    %32 = icmp eq u128 %30, %31
    condbr %32, bb7, bb8(%20)
bb7:
    %33 = load u128, ptr %0
    %34 = call @func.2(%33)
    br bb10(%34)
bb8(%1: u128):
    %35 = load u128, ptr %0
    %36 = not u128 %35
    %37 = and u128 %36, %1
    %38 = const u128 1
    %39 = add u128 %37, %38
    %40 = and u128 %39, %1
    %41 = call @func.2(%40)
    br bb9(%41)
bb9(%2: i128):
    %42 = neg i128 %2
    br bb10(%42)
bb10(%3: i128):
    ret %3
}

fn @u128_as_i128(functy.2) {
bb0(%0: u128):
    %1 = alloca i128, align 16
    %2 = alloca i64, align 8
    store u128 %0, ptr %1
    store ptr %1, ptr %2
    %3 = load ptr, ptr %2
    %4 = load i128, ptr %3
    ret %4
}

fn @int_mask(functy.3) {
bb0(%0: ptr, %1: u32):
    %5 = const u32 1
    %6 = icmp ule u32 %5, %1
    condbr %6, bb4(%1), bb3(%1)
bb1:
    %7 = const i128 0
    store i128 %7, ptr %0
    br bb6
bb2(%2: u32):
    %8 = const u128 1
    %9 = zext u32 %2 to u128
    %10 = shl u128 %8, %9
    %11 = const u128 1
    %12 = sub u128 %10, %11
    %13 = const i64 16
    %14 = gep i8, ptr %0, %13
    store u128 %12, ptr %14
    %15 = const i128 1
    store i128 %15, ptr %0
    br bb6
bb3(%3: u32):
    switch %3 [ 128: bb5 default: bb1 ]
bb4(%4: u32):
    %16 = const u32 127
    %17 = icmp ule u32 %4, %16
    condbr %17, bb2(%4), bb3(%4)
bb5:
    %18 = const u128 340282366920938463463374607431768211455
    %19 = const i64 16
    %20 = gep i8, ptr %0, %19
    store u128 %18, ptr %20
    %21 = const i128 1
    store i128 %21, ptr %0
    br bb6
bb6:
    ret
}
"#;

/// VERBATIM emit of `interp_sdiv_overflows_root`: 2012 bytes; 4 closure
/// members; validate_module = 0; re-parse OK. Extern-free. (Note the
/// in-module `(u32, i128, i128) -> (bool)` call ABI — 128-bit BY-VALUE args.)
const SDIV_OVERFLOWS_IR: &str = r#"; TrustIr text format v1
module "mir::closure::interp_sdiv_overflows_root"

functy.0 = (u32, ptr, ptr) -> (u32)

functy.1 = (u32, i128, i128) -> (bool)

functy.2 = (ptr, u32) -> ()

functy.3 = (u128) -> (i128)

fn @interp_sdiv_overflows_root(functy.0) {
bb0(%0: u32, %1: ptr, %2: ptr):
    %4 = load i128, ptr %1
    %5 = load i128, ptr %2
    %6 = call @func.1(%0, %4, %5)
    br bb1(%6)
bb1(%3: bool):
    %7 = const u32 1
    %8 = const u32 0
    %9 = select u32 %3, %7, %8
    ret %9
}

fn @signed_div_overflows(functy.1) {
bb0(%0: u32, %1: i128, %2: i128):
    %7 = alloca (i128, i128), align 16
    call @func.2(%7, %0)
    br bb1(%1, %2)
bb1(%3: i128, %4: i128):
    %8 = load i128, ptr %7
    %9 = icmp eq i128 %3, %8
    condbr %9, bb2(%4), bb3
bb2(%5: i128):
    %10 = const i128 -1
    %11 = icmp eq i128 %5, %10
    br bb4(%11)
bb3:
    %12 = const bool false
    br bb4(%12)
bb4(%6: bool):
    ret %6
}

fn @signed_bounds(functy.2) {
bb0(%0: ptr, %1: u32):
    %7 = const u32 128
    %8 = icmp eq u32 %1, %7
    condbr %8, bb1, bb2(%1)
bb1:
    %9 = const i128 -170141183460469231731687303715884105728
    store i128 %9, ptr %0
    %10 = const i128 170141183460469231731687303715884105727
    %11 = const i64 16
    %12 = gep i8, ptr %0, %11
    store i128 %10, ptr %12
    br bb5
bb2(%2: u32):
    %13 = const u32 1
    %14 = sub u32 %2, %13
    %15 = const u128 1
    %16 = zext u32 %14 to u128
    %17 = shl u128 %15, %16
    %18 = call @func.3(%17)
    br bb3(%17, %18)
bb3(%3: u128, %4: i128):
    %19 = neg i128 %4
    %20 = const u128 1
    %21 = sub u128 %3, %20
    %22 = call @func.3(%21)
    br bb4(%19, %22)
bb4(%5: i128, %6: i128):
    store i128 %5, ptr %0
    %23 = const i64 16
    %24 = gep i8, ptr %0, %23
    store i128 %6, ptr %24
    br bb5
bb5:
    ret
}

fn @u128_as_i128(functy.3) {
bb0(%0: u128):
    %1 = alloca i128, align 16
    %2 = alloca i64, align 8
    store u128 %0, ptr %1
    store ptr %1, ptr %2
    %3 = load ptr, ptr %2
    %4 = load i128, ptr %3
    ret %4
}
"#;

/// VERBATIM emit of `interp_shift_amount_root`: 2956 bytes; 3 closure
/// members; validate_module = 0; re-parse OK. Extern-free.
const SHIFT_AMOUNT_IR: &str = r#"; TrustIr text format v1
module "mir::closure::interp_shift_amount_root"

functy.0 = (u32, u32, ptr, u32, ptr, ptr, ptr) -> ()

functy.1 = (ptr, ptr, u32) -> ()

functy.2 = (u8) -> (u64)

fn @interp_shift_amount_root(functy.0) {
bb0(%0: u32, %1: u32, %2: ptr, %3: u32, %4: ptr, %5: ptr, %6: ptr):
    %18 = alloca (i128, i128), align 16
    %19 = alloca (i32, i32), align 4
    %20 = alloca i8, align 1
    %21 = const u32 0
    %22 = icmp ne u32 %1, %21
    %23 = load u128, ptr %2
    %24 = const i64 16
    %25 = gep i8, ptr %18, %24
    store u32 %0, ptr %25
    %26 = const i64 20
    %27 = gep i8, ptr %18, %26
    store bool %22, ptr %27
    store u128 %23, ptr %18
    call @func.1(%19, %18, %3)
    br bb1(%4, %5, %6)
bb1(%7: ptr, %8: ptr, %9: ptr):
    %28 = load i8, ptr %19
    %29 = sext i8 %28 to i64
    switch %29 [ 0: bb4(%7, %8, %9) 1: bb3(%7, %8, %9) default: bb2 ]
bb2:
    unreachable
bb3(%10: ptr, %11: ptr, %12: ptr):
    %30 = const i64 1
    %31 = gep i8, ptr %19, %30
    %32 = load i8, ptr %31
    store i8 %32, ptr %20
    %33 = const u64 0
    store u64 %33, ptr %10
    %34 = const u32 0
    store u32 %34, ptr %11
    %35 = load u8, ptr %20
    %36 = call @func.2(%35)
    br bb5(%12, %36)
bb4(%13: ptr, %14: ptr, %15: ptr):
    %37 = const i64 4
    %38 = gep i8, ptr %19, %37
    %39 = load u32, ptr %38
    %40 = const u64 1
    store u64 %40, ptr %13
    store u32 %39, ptr %14
    %41 = const u64 0
    store u64 %41, ptr %15
    br bb6
bb5(%16: ptr, %17: u64):
    store u64 %17, ptr %16
    br bb6
bb6:
    ret
}

fn @shift_amount(functy.1) {
bb0(%0: ptr, %1: ptr, %2: u32):
    %3 = alloca i8, align 1
    %4 = load u128, ptr %1
    %5 = zext u32 %2 to u128
    %6 = icmp uge u128 %4, %5
    condbr %6, bb1, bb2
bb1:
    %7 = const i8 8
    store i8 %7, ptr %3
    %8 = const i64 1
    %9 = gep i8, ptr %0, %8
    %10 = load i8, ptr %3
    store i8 %10, ptr %9
    %11 = const i8 1
    store i8 %11, ptr %0
    br bb3
bb2:
    %12 = load u128, ptr %1
    %13 = trunc u128 %12 to u32
    %14 = const i64 4
    %15 = gep i8, ptr %0, %14
    store u32 %13, ptr %15
    %16 = const i8 0
    store i8 %16, ptr %0
    br bb3
bb3:
    ret
}

fn @err_code(functy.2) {
bb0(%0: u8):
    %2 = alloca i8, align 1
    store u8 %0, ptr %2
    %3 = load i8, ptr %2
    %4 = sext i8 %3 to i64
    switch %4 [ 0: bb12 1: bb11 2: bb10 3: bb9 4: bb8 5: bb7 6: bb6 7: bb5 8: bb4 9: bb3 10: bb2 default: bb1 ]
bb1:
    unreachable
bb2:
    %5 = const u64 11
    br bb13(%5)
bb3:
    %6 = const u64 10
    br bb13(%6)
bb4:
    %7 = const u64 9
    br bb13(%7)
bb5:
    %8 = const u64 8
    br bb13(%8)
bb6:
    %9 = const u64 7
    br bb13(%9)
bb7:
    %10 = const u64 6
    br bb13(%10)
bb8:
    %11 = const u64 5
    br bb13(%11)
bb9:
    %12 = const u64 4
    br bb13(%12)
bb10:
    %13 = const u64 3
    br bb13(%13)
bb11:
    %14 = const u64 2
    br bb13(%14)
bb12:
    %15 = const u64 1
    br bb13(%15)
bb13(%1: u64):
    ret %1
}
"#;

/// VERBATIM emit of `interp_icmp_root`: 6259 bytes; 6 closure members
/// (root + icmp_from_u32 + eval_int_icmp + as_signed + u128_as_i128 +
/// int_mask); canonical wide constants; re-parse OK. Extern-free.
const ICMP_IR: &str = r#"; TrustIr text format v1
module "mir::closure::interp_icmp_root"

functy.0 = (u32, u32, u32, ptr, u32, u32, ptr) -> (u32)

functy.1 = (ptr, u32) -> ()

functy.2 = (u8, ptr, ptr) -> (bool)

functy.3 = (ptr) -> (i128)

functy.4 = (u128) -> (i128)

functy.5 = (ptr, u32) -> ()

fn @interp_icmp_root(functy.0) {
bb0(%0: u32, %1: u32, %2: u32, %3: ptr, %4: u32, %5: u32, %6: ptr):
    %8 = alloca (i128, i128), align 16
    %9 = alloca (i128, i128), align 16
    %10 = alloca i8, align 1
    %11 = const u32 0
    %12 = icmp ne u32 %2, %11
    %13 = load u128, ptr %3
    %14 = const i64 16
    %15 = gep i8, ptr %8, %14
    store u32 %1, ptr %15
    %16 = const i64 20
    %17 = gep i8, ptr %8, %16
    store bool %12, ptr %17
    store u128 %13, ptr %8
    %18 = const u32 0
    %19 = icmp ne u32 %5, %18
    %20 = load u128, ptr %6
    %21 = const i64 16
    %22 = gep i8, ptr %9, %21
    store u32 %4, ptr %22
    %23 = const i64 20
    %24 = gep i8, ptr %9, %23
    store bool %19, ptr %24
    store u128 %20, ptr %9
    call @func.1(%10, %0)
    br bb1
bb1:
    %25 = load u8, ptr %10
    %26 = call @func.2(%25, %8, %9)
    br bb2(%26)
bb2(%7: bool):
    %27 = const u32 1
    %28 = const u32 0
    %29 = select u32 %7, %27, %28
    ret %29
}

fn @icmp_from_u32(functy.1) {
bb0(%0: ptr, %1: u32):
    switch %1 [ 0: bb10 1: bb9 2: bb8 3: bb7 4: bb6 5: bb5 6: bb4 7: bb3 8: bb2 default: bb1 ]
bb1:
    %2 = const i8 9
    store i8 %2, ptr %0
    br bb11
bb2:
    %3 = const i8 8
    store i8 %3, ptr %0
    br bb11
bb3:
    %4 = const i8 7
    store i8 %4, ptr %0
    br bb11
bb4:
    %5 = const i8 6
    store i8 %5, ptr %0
    br bb11
bb5:
    %6 = const i8 5
    store i8 %6, ptr %0
    br bb11
bb6:
    %7 = const i8 4
    store i8 %7, ptr %0
    br bb11
bb7:
    %8 = const i8 3
    store i8 %8, ptr %0
    br bb11
bb8:
    %9 = const i8 2
    store i8 %9, ptr %0
    br bb11
bb9:
    %10 = const i8 1
    store i8 %10, ptr %0
    br bb11
bb10:
    %11 = const i8 0
    store i8 %11, ptr %0
    br bb11
bb11:
    ret
}

fn @eval_int_icmp(functy.2) {
bb0(%0: u8, %1: ptr, %2: ptr):
    %16 = alloca i8, align 1
    store u8 %0, ptr %16
    %17 = load i8, ptr %16
    %18 = sext i8 %17 to i64
    switch %18 [ 0: bb11 1: bb10 2: bb9 3: bb8 4: bb7 5: bb6 6: bb5 7: bb4 8: bb3 9: bb2 default: bb1 ]
bb1:
    unreachable
bb2:
    %19 = call @func.3(%1)
    br bb18(%19)
bb3:
    %20 = call @func.3(%1)
    br bb16(%20)
bb4:
    %21 = call @func.3(%1)
    br bb14(%21)
bb5:
    %22 = call @func.3(%1)
    br bb12(%22)
bb6:
    %23 = load u128, ptr %1
    %24 = load u128, ptr %2
    %25 = icmp uge u128 %23, %24
    br bb20(%25)
bb7:
    %26 = load u128, ptr %1
    %27 = load u128, ptr %2
    %28 = icmp ugt u128 %26, %27
    br bb20(%28)
bb8:
    %29 = load u128, ptr %1
    %30 = load u128, ptr %2
    %31 = icmp ule u128 %29, %30
    br bb20(%31)
bb9:
    %32 = load u128, ptr %1
    %33 = load u128, ptr %2
    %34 = icmp ult u128 %32, %33
    br bb20(%34)
bb10:
    %35 = load u128, ptr %1
    %36 = load u128, ptr %2
    %37 = icmp ne u128 %35, %36
    br bb20(%37)
bb11:
    %38 = load u128, ptr %1
    %39 = load u128, ptr %2
    %40 = icmp eq u128 %38, %39
    br bb20(%40)
bb12(%3: i128):
    %41 = call @func.3(%2)
    br bb13(%3, %41)
bb13(%4: i128, %5: i128):
    %42 = icmp slt i128 %4, %5
    br bb20(%42)
bb14(%6: i128):
    %43 = call @func.3(%2)
    br bb15(%6, %43)
bb15(%7: i128, %8: i128):
    %44 = icmp sle i128 %7, %8
    br bb20(%44)
bb16(%9: i128):
    %45 = call @func.3(%2)
    br bb17(%9, %45)
bb17(%10: i128, %11: i128):
    %46 = icmp sgt i128 %10, %11
    br bb20(%46)
bb18(%12: i128):
    %47 = call @func.3(%2)
    br bb19(%12, %47)
bb19(%13: i128, %14: i128):
    %48 = icmp sge i128 %13, %14
    br bb20(%48)
bb20(%15: bool):
    ret %15
}

fn @InterpretInt__as_signed(functy.3) {
bb0(%0: ptr):
    %4 = alloca (i128, i128), align 16
    %5 = const i64 16
    %6 = gep i8, ptr %0, %5
    %7 = load u32, ptr %6
    %8 = const u32 128
    %9 = icmp eq u32 %7, %8
    condbr %9, bb1, bb2
bb1:
    %10 = load u128, ptr %0
    %11 = call @func.4(%10)
    br bb10(%11)
bb2:
    %12 = const i64 16
    %13 = gep i8, ptr %0, %12
    %14 = load u32, ptr %13
    call @func.5(%4, %14)
    br bb3
bb3:
    %15 = load i128, ptr %4
    %16 = trunc i128 %15 to i64
    switch %16 [ 0: bb5 1: bb6 default: bb4 ]
bb4:
    unreachable
bb5:
    %17 = const i128 0
    br bb10(%17)
bb6:
    %18 = const i64 16
    %19 = gep i8, ptr %4, %18
    %20 = load u128, ptr %19
    %21 = const i64 16
    %22 = gep i8, ptr %0, %21
    %23 = load u32, ptr %22
    %24 = const u32 1
    %25 = sub u32 %23, %24
    %26 = const u128 1
    %27 = zext u32 %25 to u128
    %28 = shl u128 %26, %27
    %29 = load u128, ptr %0
    %30 = and u128 %29, %28
    %31 = const u128 0
    %32 = icmp eq u128 %30, %31
    condbr %32, bb7, bb8(%20)
bb7:
    %33 = load u128, ptr %0
    %34 = call @func.4(%33)
    br bb10(%34)
bb8(%1: u128):
    %35 = load u128, ptr %0
    %36 = not u128 %35
    %37 = and u128 %36, %1
    %38 = const u128 1
    %39 = add u128 %37, %38
    %40 = and u128 %39, %1
    %41 = call @func.4(%40)
    br bb9(%41)
bb9(%2: i128):
    %42 = neg i128 %2
    br bb10(%42)
bb10(%3: i128):
    ret %3
}

fn @u128_as_i128(functy.4) {
bb0(%0: u128):
    %1 = alloca i128, align 16
    %2 = alloca i64, align 8
    store u128 %0, ptr %1
    store ptr %1, ptr %2
    %3 = load ptr, ptr %2
    %4 = load i128, ptr %3
    ret %4
}

fn @int_mask(functy.5) {
bb0(%0: ptr, %1: u32):
    %5 = const u32 1
    %6 = icmp ule u32 %5, %1
    condbr %6, bb4(%1), bb3(%1)
bb1:
    %7 = const i128 0
    store i128 %7, ptr %0
    br bb6
bb2(%2: u32):
    %8 = const u128 1
    %9 = zext u32 %2 to u128
    %10 = shl u128 %8, %9
    %11 = const u128 1
    %12 = sub u128 %10, %11
    %13 = const i64 16
    %14 = gep i8, ptr %0, %13
    store u128 %12, ptr %14
    %15 = const i128 1
    store i128 %15, ptr %0
    br bb6
bb3(%3: u32):
    switch %3 [ 128: bb5 default: bb1 ]
bb4(%4: u32):
    %16 = const u32 127
    %17 = icmp ule u32 %4, %16
    condbr %17, bb2(%4), bb3(%4)
bb5:
    %18 = const u128 340282366920938463463374607431768211455
    %19 = const i64 16
    %20 = gep i8, ptr %0, %19
    store u128 %18, ptr %20
    %21 = const i128 1
    store i128 %21, ptr %0
    br bb6
bb6:
    ret
}
"#;

/// VERBATIM emit of `interp_unop_root`: 7560 bytes; 5 closure members;
/// canonical wide constants; re-parse OK. Extern-free (the
/// CtPop popcount loop [B5] is IN-MODULE — no count_ones import).
const UNOP_IR: &str = r#"; TrustIr text format v1
module "mir::closure::interp_unop_root"

functy.0 = (u32, u32, u32, ptr, ptr) -> ()

functy.1 = (ptr, u32) -> ()

functy.2 = (ptr, u8, ptr) -> ()

functy.3 = (u8) -> (u64)

functy.4 = (ptr, u32) -> ()

fn @interp_unop_root(functy.0) {
bb0(%0: u32, %1: u32, %2: u32, %3: ptr, %4: ptr):
    %11 = alloca (i128, i128), align 16
    %12 = alloca (i128, i128), align 16
    %13 = alloca i8, align 1
    %14 = alloca (i128, i128), align 16
    %15 = alloca i8, align 1
    %16 = const u32 0
    %17 = icmp ne u32 %2, %16
    %18 = load u128, ptr %3
    %19 = const i64 16
    %20 = gep i8, ptr %11, %19
    store u32 %1, ptr %20
    %21 = const i64 20
    %22 = gep i8, ptr %11, %21
    store bool %17, ptr %22
    store u128 %18, ptr %11
    call @func.1(%13, %0)
    br bb1(%4)
bb1(%5: ptr):
    %23 = load u8, ptr %13
    call @func.2(%12, %23, %11)
    br bb2(%5)
bb2(%6: ptr):
    %24 = const i64 20
    %25 = gep i8, ptr %12, %24
    %26 = load i8, ptr %25
    %27 = const i8 2
    %28 = icmp eq i8 %26, %27
    %29 = const i64 1
    %30 = const i64 0
    %31 = select i64 %28, %29, %30
    switch %31 [ 0: bb5(%6) 1: bb4(%6) default: bb3 ]
bb3:
    unreachable
bb4(%7: ptr):
    %32 = load i8, ptr %12
    store i8 %32, ptr %15
    %33 = const u64 0
    store u64 %33, ptr %7
    %34 = load u8, ptr %15
    %35 = call @func.3(%34)
    br bb6(%7, %35)
bb5(%8: ptr):
    %36 = load i128, ptr %12
    store i128 %36, ptr %14
    %37 = const i64 16
    %38 = gep i8, ptr %12, %37
    %39 = const i64 16
    %40 = gep i8, ptr %14, %39
    %41 = load i128, ptr %38
    store i128 %41, ptr %40
    %42 = const u64 1
    store u64 %42, ptr %8
    %43 = const u64 0
    %44 = const i64 8
    %45 = gep i8, ptr %8, %44
    store u64 %43, ptr %45
    %46 = const i64 16
    %47 = gep i8, ptr %14, %46
    %48 = load u32, ptr %47
    %49 = const i64 16
    %50 = gep i8, ptr %8, %49
    store u32 %48, ptr %50
    %51 = const i64 20
    %52 = gep i8, ptr %14, %51
    %53 = load bool, ptr %52
    %54 = const u32 1
    %55 = const u32 0
    %56 = select u32 %53, %54, %55
    %57 = const i64 20
    %58 = gep i8, ptr %8, %57
    store u32 %56, ptr %58
    %59 = load u128, ptr %14
    %60 = const i64 32
    %61 = gep i8, ptr %8, %60
    store u128 %59, ptr %61
    br bb7
bb6(%9: ptr, %10: u64):
    %62 = const i64 8
    %63 = gep i8, ptr %9, %62
    store u64 %10, ptr %63
    %64 = const u32 0
    %65 = const i64 16
    %66 = gep i8, ptr %9, %65
    store u32 %64, ptr %66
    %67 = const u32 0
    %68 = const i64 20
    %69 = gep i8, ptr %9, %68
    store u32 %67, ptr %69
    %70 = const u128 0
    %71 = const i64 32
    %72 = gep i8, ptr %9, %71
    store u128 %70, ptr %72
    br bb7
bb7:
    ret
}

fn @unop_from_u32(functy.1) {
bb0(%0: ptr, %1: u32):
    switch %1 [ 0: bb9 1: bb8 2: bb7 3: bb6 4: bb5 5: bb4 6: bb3 7: bb2 default: bb1 ]
bb1:
    %2 = const i8 8
    store i8 %2, ptr %0
    br bb10
bb2:
    %3 = const i8 7
    store i8 %3, ptr %0
    br bb10
bb3:
    %4 = const i8 6
    store i8 %4, ptr %0
    br bb10
bb4:
    %5 = const i8 5
    store i8 %5, ptr %0
    br bb10
bb5:
    %6 = const i8 4
    store i8 %6, ptr %0
    br bb10
bb6:
    %7 = const i8 3
    store i8 %7, ptr %0
    br bb10
bb7:
    %8 = const i8 2
    store i8 %8, ptr %0
    br bb10
bb8:
    %9 = const i8 1
    store i8 %9, ptr %0
    br bb10
bb9:
    %10 = const i8 0
    store i8 %10, ptr %0
    br bb10
bb10:
    ret
}

fn @eval_int_unop(functy.2) {
bb0(%0: ptr, %1: u8, %2: ptr):
    %16 = alloca i8, align 1
    %17 = alloca (i128, i128), align 16
    %18 = alloca i8, align 1
    %19 = alloca i8, align 1
    %20 = alloca (i128, i128), align 16
    store u8 %1, ptr %16
    %21 = const i64 16
    %22 = gep i8, ptr %2, %21
    %23 = load u32, ptr %22
    call @func.4(%17, %23)
    br bb1
bb1:
    %24 = load i128, ptr %17
    %25 = trunc i128 %24 to i64
    switch %25 [ 0: bb3 1: bb4 default: bb2 ]
bb2:
    unreachable
bb3:
    %26 = const i8 1
    store i8 %26, ptr %18
    %27 = load i8, ptr %18
    store i8 %27, ptr %0
    %28 = const i64 20
    %29 = gep i8, ptr %0, %28
    %30 = const i8 2
    store i8 %30, ptr %29
    br bb13
bb4:
    %31 = const i64 16
    %32 = gep i8, ptr %17, %31
    %33 = load u128, ptr %32
    %34 = load i8, ptr %16
    %35 = sext i8 %34 to i64
    switch %35 [ 0: bb8(%33) 1: bb5 2: bb5 3: bb5 4: bb5 5: bb5 6: bb5 7: bb7(%33) 8: bb6(%33) default: bb2 ]
bb5:
    %36 = const i8 10
    store i8 %36, ptr %19
    %37 = load i8, ptr %19
    store i8 %37, ptr %0
    %38 = const i64 20
    %39 = gep i8, ptr %0, %38
    %40 = const i8 2
    store i8 %40, ptr %39
    br bb13
bb6(%3: u128):
    %41 = load u128, ptr %2
    %42 = const u128 0
    br bb9(%3, %41, %42)
bb7(%4: u128):
    %43 = load u128, ptr %2
    %44 = not u128 %43
    br bb12(%4, %44)
bb8(%5: u128):
    %45 = load u128, ptr %2
    %46 = const u128 0
    %47 = sub u128 %46, %45
    br bb12(%5, %47)
bb9(%6: u128, %7: u128, %8: u128):
    %48 = const u128 0
    %49 = icmp ne u128 %7, %48
    condbr %49, bb10(%6, %7, %8), bb11(%6, %8)
bb10(%9: u128, %10: u128, %11: u128):
    %50 = const u128 1
    %51 = and u128 %10, %50
    %52 = add u128 %11, %51
    %53 = const u128 1
    %54 = lshr u128 %10, %53
    br bb9(%9, %54, %52)
bb11(%12: u128, %13: u128):
    br bb12(%12, %13)
bb12(%14: u128, %15: u128):
    %55 = and u128 %15, %14
    %56 = const i64 16
    %57 = gep i8, ptr %2, %56
    %58 = load u32, ptr %57
    %59 = const i64 20
    %60 = gep i8, ptr %2, %59
    %61 = load bool, ptr %60
    %62 = const i64 16
    %63 = gep i8, ptr %20, %62
    store u32 %58, ptr %63
    %64 = const i64 20
    %65 = gep i8, ptr %20, %64
    store bool %61, ptr %65
    store u128 %55, ptr %20
    %66 = load i128, ptr %20
    store i128 %66, ptr %0
    %67 = const i64 16
    %68 = gep i8, ptr %20, %67
    %69 = const i64 16
    %70 = gep i8, ptr %0, %69
    %71 = load i128, ptr %68
    store i128 %71, ptr %70
    br bb13
bb13:
    ret
}

fn @err_code(functy.3) {
bb0(%0: u8):
    %2 = alloca i8, align 1
    store u8 %0, ptr %2
    %3 = load i8, ptr %2
    %4 = sext i8 %3 to i64
    switch %4 [ 0: bb12 1: bb11 2: bb10 3: bb9 4: bb8 5: bb7 6: bb6 7: bb5 8: bb4 9: bb3 10: bb2 default: bb1 ]
bb1:
    unreachable
bb2:
    %5 = const u64 11
    br bb13(%5)
bb3:
    %6 = const u64 10
    br bb13(%6)
bb4:
    %7 = const u64 9
    br bb13(%7)
bb5:
    %8 = const u64 8
    br bb13(%8)
bb6:
    %9 = const u64 7
    br bb13(%9)
bb7:
    %10 = const u64 6
    br bb13(%10)
bb8:
    %11 = const u64 5
    br bb13(%11)
bb9:
    %12 = const u64 4
    br bb13(%12)
bb10:
    %13 = const u64 3
    br bb13(%13)
bb11:
    %14 = const u64 2
    br bb13(%14)
bb12:
    %15 = const u64 1
    br bb13(%15)
bb13(%1: u64):
    ret %1
}

fn @int_mask(functy.4) {
bb0(%0: ptr, %1: u32):
    %5 = const u32 1
    %6 = icmp ule u32 %5, %1
    condbr %6, bb4(%1), bb3(%1)
bb1:
    %7 = const i128 0
    store i128 %7, ptr %0
    br bb6
bb2(%2: u32):
    %8 = const u128 1
    %9 = zext u32 %2 to u128
    %10 = shl u128 %8, %9
    %11 = const u128 1
    %12 = sub u128 %10, %11
    %13 = const i64 16
    %14 = gep i8, ptr %0, %13
    store u128 %12, ptr %14
    %15 = const i128 1
    store i128 %15, ptr %0
    br bb6
bb3(%3: u32):
    switch %3 [ 128: bb5 default: bb1 ]
bb4(%4: u32):
    %16 = const u32 127
    %17 = icmp ule u32 %4, %16
    condbr %17, bb2(%4), bb3(%4)
bb5:
    %18 = const u128 340282366920938463463374607431768211455
    %19 = const i64 16
    %20 = gep i8, ptr %0, %19
    store u128 %18, ptr %20
    %21 = const i128 1
    store i128 %21, ptr %0
    br bb6
bb6:
    ret
}
"#;

/// VERBATIM emit of `interp_binop_root` — THE CENTERPIECE: 21245 bytes; 11
/// closure members (root, binop_from_u32, eval_int_binop, err_code, int_mask,
/// shift_amount, InterpretInt__as_signed, signed_div_overflows, i128_as_u128,
/// u128_as_i128, signed_bounds); canonical wide constants; re-parse OK.
/// EXTERN-FREE: every arm of the production integer evaluator —
/// including udiv/urem u128, sdiv/srem i128 and the dynamic shifts — executes
/// as JIT machine code.
const BINOP_IR: &str = r#"; TrustIr text format v1
module "mir::closure::interp_binop_root"

functy.0 = (u32, u32, u32, ptr, u32, u32, ptr, ptr) -> ()

functy.1 = (ptr, u32) -> ()

functy.2 = (ptr, u8, ptr, ptr) -> ()

functy.3 = (u8) -> (u64)

functy.4 = (ptr, u32) -> ()

functy.5 = (ptr, ptr, u32) -> ()

functy.6 = (ptr) -> (i128)

functy.7 = (u32, i128, i128) -> (bool)

functy.8 = (i128) -> (u128)

functy.9 = (u128) -> (i128)

functy.10 = (ptr, u32) -> ()

fn @interp_binop_root(functy.0) {
bb0(%0: u32, %1: u32, %2: u32, %3: ptr, %4: u32, %5: u32, %6: ptr, %7: ptr):
    %14 = alloca (i128, i128), align 16
    %15 = alloca (i128, i128), align 16
    %16 = alloca (i128, i128), align 16
    %17 = alloca i8, align 1
    %18 = alloca (i128, i128), align 16
    %19 = alloca i8, align 1
    %20 = const u32 0
    %21 = icmp ne u32 %2, %20
    %22 = load u128, ptr %3
    %23 = const i64 16
    %24 = gep i8, ptr %14, %23
    store u32 %1, ptr %24
    %25 = const i64 20
    %26 = gep i8, ptr %14, %25
    store bool %21, ptr %26
    store u128 %22, ptr %14
    %27 = const u32 0
    %28 = icmp ne u32 %5, %27
    %29 = load u128, ptr %6
    %30 = const i64 16
    %31 = gep i8, ptr %15, %30
    store u32 %4, ptr %31
    %32 = const i64 20
    %33 = gep i8, ptr %15, %32
    store bool %28, ptr %33
    store u128 %29, ptr %15
    call @func.1(%17, %0)
    br bb1(%7)
bb1(%8: ptr):
    %34 = load u8, ptr %17
    call @func.2(%16, %34, %14, %15)
    br bb2(%8)
bb2(%9: ptr):
    %35 = const i64 20
    %36 = gep i8, ptr %16, %35
    %37 = load i8, ptr %36
    %38 = const i8 2
    %39 = icmp eq i8 %37, %38
    %40 = const i64 1
    %41 = const i64 0
    %42 = select i64 %39, %40, %41
    switch %42 [ 0: bb5(%9) 1: bb4(%9) default: bb3 ]
bb3:
    unreachable
bb4(%10: ptr):
    %43 = load i8, ptr %16
    store i8 %43, ptr %19
    %44 = const u64 0
    store u64 %44, ptr %10
    %45 = load u8, ptr %19
    %46 = call @func.3(%45)
    br bb6(%10, %46)
bb5(%11: ptr):
    %47 = load i128, ptr %16
    store i128 %47, ptr %18
    %48 = const i64 16
    %49 = gep i8, ptr %16, %48
    %50 = const i64 16
    %51 = gep i8, ptr %18, %50
    %52 = load i128, ptr %49
    store i128 %52, ptr %51
    %53 = const u64 1
    store u64 %53, ptr %11
    %54 = const u64 0
    %55 = const i64 8
    %56 = gep i8, ptr %11, %55
    store u64 %54, ptr %56
    %57 = const i64 16
    %58 = gep i8, ptr %18, %57
    %59 = load u32, ptr %58
    %60 = const i64 16
    %61 = gep i8, ptr %11, %60
    store u32 %59, ptr %61
    %62 = const i64 20
    %63 = gep i8, ptr %18, %62
    %64 = load bool, ptr %63
    %65 = const u32 1
    %66 = const u32 0
    %67 = select u32 %64, %65, %66
    %68 = const i64 20
    %69 = gep i8, ptr %11, %68
    store u32 %67, ptr %69
    %70 = load u128, ptr %18
    %71 = const i64 32
    %72 = gep i8, ptr %11, %71
    store u128 %70, ptr %72
    br bb7
bb6(%12: ptr, %13: u64):
    %73 = const i64 8
    %74 = gep i8, ptr %12, %73
    store u64 %13, ptr %74
    %75 = const u32 0
    %76 = const i64 16
    %77 = gep i8, ptr %12, %76
    store u32 %75, ptr %77
    %78 = const u32 0
    %79 = const i64 20
    %80 = gep i8, ptr %12, %79
    store u32 %78, ptr %80
    %81 = const u128 0
    %82 = const i64 32
    %83 = gep i8, ptr %12, %82
    store u128 %81, ptr %83
    br bb7
bb7:
    ret
}

fn @binop_from_u32(functy.1) {
bb0(%0: ptr, %1: u32):
    switch %1 [ 0: bb20 1: bb19 2: bb18 3: bb17 4: bb16 5: bb15 6: bb14 7: bb13 8: bb12 9: bb11 10: bb10 11: bb9 12: bb8 13: bb7 14: bb6 15: bb5 16: bb4 17: bb3 18: bb2 default: bb1 ]
bb1:
    %2 = const i8 19
    store i8 %2, ptr %0
    br bb21
bb2:
    %3 = const i8 18
    store i8 %3, ptr %0
    br bb21
bb3:
    %4 = const i8 17
    store i8 %4, ptr %0
    br bb21
bb4:
    %5 = const i8 16
    store i8 %5, ptr %0
    br bb21
bb5:
    %6 = const i8 15
    store i8 %6, ptr %0
    br bb21
bb6:
    %7 = const i8 14
    store i8 %7, ptr %0
    br bb21
bb7:
    %8 = const i8 13
    store i8 %8, ptr %0
    br bb21
bb8:
    %9 = const i8 12
    store i8 %9, ptr %0
    br bb21
bb9:
    %10 = const i8 11
    store i8 %10, ptr %0
    br bb21
bb10:
    %11 = const i8 10
    store i8 %11, ptr %0
    br bb21
bb11:
    %12 = const i8 9
    store i8 %12, ptr %0
    br bb21
bb12:
    %13 = const i8 8
    store i8 %13, ptr %0
    br bb21
bb13:
    %14 = const i8 7
    store i8 %14, ptr %0
    br bb21
bb14:
    %15 = const i8 6
    store i8 %15, ptr %0
    br bb21
bb15:
    %16 = const i8 5
    store i8 %16, ptr %0
    br bb21
bb16:
    %17 = const i8 4
    store i8 %17, ptr %0
    br bb21
bb17:
    %18 = const i8 3
    store i8 %18, ptr %0
    br bb21
bb18:
    %19 = const i8 2
    store i8 %19, ptr %0
    br bb21
bb19:
    %20 = const i8 1
    store i8 %20, ptr %0
    br bb21
bb20:
    %21 = const i8 0
    store i8 %21, ptr %0
    br bb21
bb21:
    ret
}

fn @eval_int_binop(functy.2) {
bb0(%0: ptr, %1: u8, %2: ptr, %3: ptr):
    %76 = alloca i8, align 1
    %77 = alloca i8, align 1
    %78 = alloca (i128, i128), align 16
    %79 = alloca i8, align 1
    %80 = alloca i8, align 1
    %81 = alloca i8, align 1
    %82 = alloca i8, align 1
    %83 = alloca i8, align 1
    %84 = alloca i8, align 1
    %85 = alloca i8, align 1
    %86 = alloca (i32, i32), align 4
    %87 = alloca i8, align 1
    %88 = alloca (i32, i32), align 4
    %89 = alloca i8, align 1
    %90 = alloca (i32, i32), align 4
    %91 = alloca i8, align 1
    %92 = alloca i8, align 1
    %93 = alloca (i128, i128), align 16
    store u8 %1, ptr %76
    %94 = const i64 16
    %95 = gep i8, ptr %2, %94
    %96 = load u32, ptr %95
    %97 = const i64 16
    %98 = gep i8, ptr %3, %97
    %99 = load u32, ptr %98
    %100 = icmp ne u32 %96, %99
    condbr %100, bb1, bb2
bb1:
    %101 = const i8 0
    store i8 %101, ptr %77
    %102 = load i8, ptr %77
    store i8 %102, ptr %0
    %103 = const i64 20
    %104 = gep i8, ptr %0, %103
    %105 = const i8 2
    store i8 %105, ptr %104
    br bb56
bb2:
    %106 = const i64 16
    %107 = gep i8, ptr %2, %106
    %108 = load u32, ptr %107
    call @func.4(%78, %108)
    br bb3
bb3:
    %109 = load i128, ptr %78
    %110 = trunc i128 %109 to i64
    switch %110 [ 0: bb5 1: bb6 default: bb4 ]
bb4:
    unreachable
bb5:
    %111 = const i8 1
    store i8 %111, ptr %79
    %112 = load i8, ptr %79
    store i8 %112, ptr %0
    %113 = const i64 20
    %114 = gep i8, ptr %0, %113
    %115 = const i8 2
    store i8 %115, ptr %114
    br bb56
bb6:
    %116 = const i64 16
    %117 = gep i8, ptr %78, %116
    %118 = load u128, ptr %117
    %119 = load i8, ptr %76
    %120 = sext i8 %119 to i64
    switch %120 [ 0: bb20(%118) 1: bb19(%118) 2: bb18(%118) 3: bb14(%118) 4: bb12(%118) 5: bb13(%118) 6: bb11(%118) 7: bb7 8: bb7 9: bb7 10: bb7 11: bb7 12: bb7 13: bb7 14: bb17(%118) 15: bb16(%118) 16: bb15(%118) 17: bb10(%118) 18: bb9(%118) 19: bb8(%118) default: bb4 ]
bb7:
    %121 = const i8 9
    store i8 %121, ptr %92
    %122 = load i8, ptr %92
    store i8 %122, ptr %0
    %123 = const i64 20
    %124 = gep i8, ptr %0, %123
    %125 = const i8 2
    store i8 %125, ptr %124
    br bb56
bb8(%4: u128):
    %126 = const i64 16
    %127 = gep i8, ptr %2, %126
    %128 = load u32, ptr %127
    call @func.5(%90, %3, %128)
    br bb51(%4)
bb9(%5: u128):
    %129 = const i64 16
    %130 = gep i8, ptr %2, %129
    %131 = load u32, ptr %130
    call @func.5(%88, %3, %131)
    br bb48(%5)
bb10(%6: u128):
    %132 = const i64 16
    %133 = gep i8, ptr %2, %132
    %134 = load u32, ptr %133
    call @func.5(%86, %3, %134)
    br bb45(%6)
bb11(%7: u128):
    %135 = call @func.6(%3)
    br bb36(%7, %135)
bb12(%8: u128):
    %136 = call @func.6(%3)
    br bb27(%8, %136)
bb13(%9: u128):
    %137 = load u128, ptr %3
    %138 = const u128 0
    %139 = icmp eq u128 %137, %138
    condbr %139, bb24, bb25(%9)
bb14(%10: u128):
    %140 = load u128, ptr %3
    %141 = const u128 0
    %142 = icmp eq u128 %140, %141
    condbr %142, bb21, bb22(%10)
bb15(%11: u128):
    %143 = load u128, ptr %2
    %144 = load u128, ptr %3
    %145 = xor u128 %143, %144
    br bb55(%11, %145)
bb16(%12: u128):
    %146 = load u128, ptr %2
    %147 = load u128, ptr %3
    %148 = or u128 %146, %147
    br bb55(%12, %148)
bb17(%13: u128):
    %149 = load u128, ptr %2
    %150 = load u128, ptr %3
    %151 = and u128 %149, %150
    br bb55(%13, %151)
bb18(%14: u128):
    %152 = load u128, ptr %2
    %153 = load u128, ptr %3
    %154 = mul u128 %152, %153
    br bb55(%14, %154)
bb19(%15: u128):
    %155 = load u128, ptr %2
    %156 = load u128, ptr %3
    %157 = sub u128 %155, %156
    br bb55(%15, %157)
bb20(%16: u128):
    %158 = load u128, ptr %2
    %159 = load u128, ptr %3
    %160 = add u128 %158, %159
    br bb55(%16, %160)
bb21:
    %161 = const i8 2
    store i8 %161, ptr %80
    %162 = load i8, ptr %80
    store i8 %162, ptr %0
    %163 = const i64 20
    %164 = gep i8, ptr %0, %163
    %165 = const i8 2
    store i8 %165, ptr %164
    br bb56
bb22(%17: u128):
    %166 = load u128, ptr %2
    %167 = load u128, ptr %3
    %168 = const u128 0
    %169 = icmp eq u128 %167, %168
    %170 = const bool false
    %171 = icmp eq bool %169, %170
    condbr %171, bb23(%17, %166, %167), bb57
bb23(%18: u128, %19: u128, %20: u128):
    %172 = udiv u128 %19, %20
    br bb55(%18, %172)
bb24:
    %173 = const i8 3
    store i8 %173, ptr %81
    %174 = load i8, ptr %81
    store i8 %174, ptr %0
    %175 = const i64 20
    %176 = gep i8, ptr %0, %175
    %177 = const i8 2
    store i8 %177, ptr %176
    br bb56
bb25(%21: u128):
    %178 = load u128, ptr %2
    %179 = load u128, ptr %3
    %180 = const u128 0
    %181 = icmp eq u128 %179, %180
    %182 = const bool false
    %183 = icmp eq bool %181, %182
    condbr %183, bb26(%21, %178, %179), bb57
bb26(%22: u128, %23: u128, %24: u128):
    %184 = urem u128 %23, %24
    br bb55(%22, %184)
bb27(%25: u128, %26: i128):
    %185 = const i128 0
    %186 = icmp eq i128 %26, %185
    condbr %186, bb28, bb29(%25, %26)
bb28:
    %187 = const i8 4
    store i8 %187, ptr %82
    %188 = load i8, ptr %82
    store i8 %188, ptr %0
    %189 = const i64 20
    %190 = gep i8, ptr %0, %189
    %191 = const i8 2
    store i8 %191, ptr %190
    br bb56
bb29(%27: u128, %28: i128):
    %192 = call @func.6(%2)
    br bb30(%27, %28, %192)
bb30(%29: u128, %30: i128, %31: i128):
    %193 = const i64 16
    %194 = gep i8, ptr %2, %193
    %195 = load u32, ptr %194
    %196 = call @func.7(%195, %31, %30)
    br bb31(%29, %30, %31, %196)
bb31(%32: u128, %33: i128, %34: i128, %35: bool):
    condbr %35, bb32, bb33(%32, %33, %34)
bb32:
    %197 = const i8 5
    store i8 %197, ptr %83
    %198 = load i8, ptr %83
    store i8 %198, ptr %0
    %199 = const i64 20
    %200 = gep i8, ptr %0, %199
    %201 = const i8 2
    store i8 %201, ptr %200
    br bb56
bb33(%36: u128, %37: i128, %38: i128):
    %202 = const i128 0
    %203 = icmp eq i128 %37, %202
    %204 = const bool false
    %205 = icmp eq bool %203, %204
    condbr %205, bb34(%36, %37, %38), bb57
bb34(%39: u128, %40: i128, %41: i128):
    %206 = const i128 -1
    %207 = icmp eq i128 %40, %206
    %208 = const i128 -170141183460469231731687303715884105728
    %209 = icmp eq i128 %41, %208
    %210 = const bool false
    %211 = select bool %207, %209, %210
    %212 = const bool false
    %213 = icmp eq bool %211, %212
    condbr %213, bb35(%39, %40, %41), bb57
bb35(%42: u128, %43: i128, %44: i128):
    %214 = sdiv i128 %44, %43
    %215 = call @func.8(%214)
    br bb55(%42, %215)
bb36(%45: u128, %46: i128):
    %216 = const i128 0
    %217 = icmp eq i128 %46, %216
    condbr %217, bb37, bb38(%45, %46)
bb37:
    %218 = const i8 6
    store i8 %218, ptr %84
    %219 = load i8, ptr %84
    store i8 %219, ptr %0
    %220 = const i64 20
    %221 = gep i8, ptr %0, %220
    %222 = const i8 2
    store i8 %222, ptr %221
    br bb56
bb38(%47: u128, %48: i128):
    %223 = call @func.6(%2)
    br bb39(%47, %48, %223)
bb39(%49: u128, %50: i128, %51: i128):
    %224 = const i64 16
    %225 = gep i8, ptr %2, %224
    %226 = load u32, ptr %225
    %227 = call @func.7(%226, %51, %50)
    br bb40(%49, %50, %51, %227)
bb40(%52: u128, %53: i128, %54: i128, %55: bool):
    condbr %55, bb41, bb42(%52, %53, %54)
bb41:
    %228 = const i8 7
    store i8 %228, ptr %85
    %229 = load i8, ptr %85
    store i8 %229, ptr %0
    %230 = const i64 20
    %231 = gep i8, ptr %0, %230
    %232 = const i8 2
    store i8 %232, ptr %231
    br bb56
bb42(%56: u128, %57: i128, %58: i128):
    %233 = const i128 0
    %234 = icmp eq i128 %57, %233
    %235 = const bool false
    %236 = icmp eq bool %234, %235
    condbr %236, bb43(%56, %57, %58), bb57
bb43(%59: u128, %60: i128, %61: i128):
    %237 = const i128 -1
    %238 = icmp eq i128 %60, %237
    %239 = const i128 -170141183460469231731687303715884105728
    %240 = icmp eq i128 %61, %239
    %241 = const bool false
    %242 = select bool %238, %240, %241
    %243 = const bool false
    %244 = icmp eq bool %242, %243
    condbr %244, bb44(%59, %60, %61), bb57
bb44(%62: u128, %63: i128, %64: i128):
    %245 = srem i128 %64, %63
    %246 = call @func.8(%245)
    br bb55(%62, %246)
bb45(%65: u128):
    %247 = load i8, ptr %86
    %248 = sext i8 %247 to i64
    switch %248 [ 0: bb47(%65) 1: bb46 default: bb4 ]
bb46:
    %249 = const i64 1
    %250 = gep i8, ptr %86, %249
    %251 = load i8, ptr %250
    store i8 %251, ptr %87
    %252 = load i8, ptr %87
    store i8 %252, ptr %0
    %253 = const i64 20
    %254 = gep i8, ptr %0, %253
    %255 = const i8 2
    store i8 %255, ptr %254
    br bb56
bb47(%66: u128):
    %256 = const i64 4
    %257 = gep i8, ptr %86, %256
    %258 = load u32, ptr %257
    %259 = load u128, ptr %2
    %260 = zext u32 %258 to u128
    %261 = shl u128 %259, %260
    br bb55(%66, %261)
bb48(%67: u128):
    %262 = load i8, ptr %88
    %263 = sext i8 %262 to i64
    switch %263 [ 0: bb50(%67) 1: bb49 default: bb4 ]
bb49:
    %264 = const i64 1
    %265 = gep i8, ptr %88, %264
    %266 = load i8, ptr %265
    store i8 %266, ptr %89
    %267 = load i8, ptr %89
    store i8 %267, ptr %0
    %268 = const i64 20
    %269 = gep i8, ptr %0, %268
    %270 = const i8 2
    store i8 %270, ptr %269
    br bb56
bb50(%68: u128):
    %271 = const i64 4
    %272 = gep i8, ptr %88, %271
    %273 = load u32, ptr %272
    %274 = load u128, ptr %2
    %275 = zext u32 %273 to u128
    %276 = lshr u128 %274, %275
    br bb55(%68, %276)
bb51(%69: u128):
    %277 = load i8, ptr %90
    %278 = sext i8 %277 to i64
    switch %278 [ 0: bb53(%69) 1: bb52 default: bb4 ]
bb52:
    %279 = const i64 1
    %280 = gep i8, ptr %90, %279
    %281 = load i8, ptr %280
    store i8 %281, ptr %91
    %282 = load i8, ptr %91
    store i8 %282, ptr %0
    %283 = const i64 20
    %284 = gep i8, ptr %0, %283
    %285 = const i8 2
    store i8 %285, ptr %284
    br bb56
bb53(%70: u128):
    %286 = const i64 4
    %287 = gep i8, ptr %90, %286
    %288 = load u32, ptr %287
    %289 = call @func.6(%2)
    br bb54(%70, %288, %289)
bb54(%71: u128, %72: u32, %73: i128):
    %290 = zext u32 %72 to i128
    %291 = ashr i128 %73, %290
    %292 = call @func.8(%291)
    br bb55(%71, %292)
bb55(%74: u128, %75: u128):
    %293 = and u128 %75, %74
    %294 = const i64 16
    %295 = gep i8, ptr %2, %294
    %296 = load u32, ptr %295
    %297 = const i64 20
    %298 = gep i8, ptr %2, %297
    %299 = load bool, ptr %298
    %300 = const i64 16
    %301 = gep i8, ptr %93, %300
    store u32 %296, ptr %301
    %302 = const i64 20
    %303 = gep i8, ptr %93, %302
    store bool %299, ptr %303
    store u128 %293, ptr %93
    %304 = load i128, ptr %93
    store i128 %304, ptr %0
    %305 = const i64 16
    %306 = gep i8, ptr %93, %305
    %307 = const i64 16
    %308 = gep i8, ptr %0, %307
    %309 = load i128, ptr %306
    store i128 %309, ptr %308
    br bb56
bb56:
    ret
bb57:
    unreachable
}

fn @err_code(functy.3) {
bb0(%0: u8):
    %2 = alloca i8, align 1
    store u8 %0, ptr %2
    %3 = load i8, ptr %2
    %4 = sext i8 %3 to i64
    switch %4 [ 0: bb12 1: bb11 2: bb10 3: bb9 4: bb8 5: bb7 6: bb6 7: bb5 8: bb4 9: bb3 10: bb2 default: bb1 ]
bb1:
    unreachable
bb2:
    %5 = const u64 11
    br bb13(%5)
bb3:
    %6 = const u64 10
    br bb13(%6)
bb4:
    %7 = const u64 9
    br bb13(%7)
bb5:
    %8 = const u64 8
    br bb13(%8)
bb6:
    %9 = const u64 7
    br bb13(%9)
bb7:
    %10 = const u64 6
    br bb13(%10)
bb8:
    %11 = const u64 5
    br bb13(%11)
bb9:
    %12 = const u64 4
    br bb13(%12)
bb10:
    %13 = const u64 3
    br bb13(%13)
bb11:
    %14 = const u64 2
    br bb13(%14)
bb12:
    %15 = const u64 1
    br bb13(%15)
bb13(%1: u64):
    ret %1
}

fn @int_mask(functy.4) {
bb0(%0: ptr, %1: u32):
    %5 = const u32 1
    %6 = icmp ule u32 %5, %1
    condbr %6, bb4(%1), bb3(%1)
bb1:
    %7 = const i128 0
    store i128 %7, ptr %0
    br bb6
bb2(%2: u32):
    %8 = const u128 1
    %9 = zext u32 %2 to u128
    %10 = shl u128 %8, %9
    %11 = const u128 1
    %12 = sub u128 %10, %11
    %13 = const i64 16
    %14 = gep i8, ptr %0, %13
    store u128 %12, ptr %14
    %15 = const i128 1
    store i128 %15, ptr %0
    br bb6
bb3(%3: u32):
    switch %3 [ 128: bb5 default: bb1 ]
bb4(%4: u32):
    %16 = const u32 127
    %17 = icmp ule u32 %4, %16
    condbr %17, bb2(%4), bb3(%4)
bb5:
    %18 = const u128 340282366920938463463374607431768211455
    %19 = const i64 16
    %20 = gep i8, ptr %0, %19
    store u128 %18, ptr %20
    %21 = const i128 1
    store i128 %21, ptr %0
    br bb6
bb6:
    ret
}

fn @shift_amount(functy.5) {
bb0(%0: ptr, %1: ptr, %2: u32):
    %3 = alloca i8, align 1
    %4 = load u128, ptr %1
    %5 = zext u32 %2 to u128
    %6 = icmp uge u128 %4, %5
    condbr %6, bb1, bb2
bb1:
    %7 = const i8 8
    store i8 %7, ptr %3
    %8 = const i64 1
    %9 = gep i8, ptr %0, %8
    %10 = load i8, ptr %3
    store i8 %10, ptr %9
    %11 = const i8 1
    store i8 %11, ptr %0
    br bb3
bb2:
    %12 = load u128, ptr %1
    %13 = trunc u128 %12 to u32
    %14 = const i64 4
    %15 = gep i8, ptr %0, %14
    store u32 %13, ptr %15
    %16 = const i8 0
    store i8 %16, ptr %0
    br bb3
bb3:
    ret
}

fn @InterpretInt__as_signed(functy.6) {
bb0(%0: ptr):
    %4 = alloca (i128, i128), align 16
    %5 = const i64 16
    %6 = gep i8, ptr %0, %5
    %7 = load u32, ptr %6
    %8 = const u32 128
    %9 = icmp eq u32 %7, %8
    condbr %9, bb1, bb2
bb1:
    %10 = load u128, ptr %0
    %11 = call @func.9(%10)
    br bb10(%11)
bb2:
    %12 = const i64 16
    %13 = gep i8, ptr %0, %12
    %14 = load u32, ptr %13
    call @func.4(%4, %14)
    br bb3
bb3:
    %15 = load i128, ptr %4
    %16 = trunc i128 %15 to i64
    switch %16 [ 0: bb5 1: bb6 default: bb4 ]
bb4:
    unreachable
bb5:
    %17 = const i128 0
    br bb10(%17)
bb6:
    %18 = const i64 16
    %19 = gep i8, ptr %4, %18
    %20 = load u128, ptr %19
    %21 = const i64 16
    %22 = gep i8, ptr %0, %21
    %23 = load u32, ptr %22
    %24 = const u32 1
    %25 = sub u32 %23, %24
    %26 = const u128 1
    %27 = zext u32 %25 to u128
    %28 = shl u128 %26, %27
    %29 = load u128, ptr %0
    %30 = and u128 %29, %28
    %31 = const u128 0
    %32 = icmp eq u128 %30, %31
    condbr %32, bb7, bb8(%20)
bb7:
    %33 = load u128, ptr %0
    %34 = call @func.9(%33)
    br bb10(%34)
bb8(%1: u128):
    %35 = load u128, ptr %0
    %36 = not u128 %35
    %37 = and u128 %36, %1
    %38 = const u128 1
    %39 = add u128 %37, %38
    %40 = and u128 %39, %1
    %41 = call @func.9(%40)
    br bb9(%41)
bb9(%2: i128):
    %42 = neg i128 %2
    br bb10(%42)
bb10(%3: i128):
    ret %3
}

fn @signed_div_overflows(functy.7) {
bb0(%0: u32, %1: i128, %2: i128):
    %7 = alloca (i128, i128), align 16
    call @func.10(%7, %0)
    br bb1(%1, %2)
bb1(%3: i128, %4: i128):
    %8 = load i128, ptr %7
    %9 = icmp eq i128 %3, %8
    condbr %9, bb2(%4), bb3
bb2(%5: i128):
    %10 = const i128 -1
    %11 = icmp eq i128 %5, %10
    br bb4(%11)
bb3:
    %12 = const bool false
    br bb4(%12)
bb4(%6: bool):
    ret %6
}

fn @i128_as_u128(functy.8) {
bb0(%0: i128):
    %1 = alloca i128, align 16
    %2 = alloca i64, align 8
    store i128 %0, ptr %1
    store ptr %1, ptr %2
    %3 = load ptr, ptr %2
    %4 = load u128, ptr %3
    ret %4
}

fn @u128_as_i128(functy.9) {
bb0(%0: u128):
    %1 = alloca i128, align 16
    %2 = alloca i64, align 8
    store u128 %0, ptr %1
    store ptr %1, ptr %2
    %3 = load ptr, ptr %2
    %4 = load i128, ptr %3
    ret %4
}

fn @signed_bounds(functy.10) {
bb0(%0: ptr, %1: u32):
    %7 = const u32 128
    %8 = icmp eq u32 %1, %7
    condbr %8, bb1, bb2(%1)
bb1:
    %9 = const i128 -170141183460469231731687303715884105728
    store i128 %9, ptr %0
    %10 = const i128 170141183460469231731687303715884105727
    %11 = const i64 16
    %12 = gep i8, ptr %0, %11
    store i128 %10, ptr %12
    br bb5
bb2(%2: u32):
    %13 = const u32 1
    %14 = sub u32 %2, %13
    %15 = const u128 1
    %16 = zext u32 %14 to u128
    %17 = shl u128 %15, %16
    %18 = call @func.9(%17)
    br bb3(%17, %18)
bb3(%3: u128, %4: i128):
    %19 = neg i128 %4
    %20 = const u128 1
    %21 = sub u128 %3, %20
    %22 = call @func.9(%21)
    br bb4(%19, %22)
bb4(%5: i128, %6: i128):
    store i128 %5, ptr %0
    %23 = const i64 16
    %24 = gep i8, ptr %0, %23
    store i128 %6, ptr %24
    br bb5
bb5:
    ret
}
"#;

/// VERBATIM emit of `interp_overflow_root`: 28234 bytes; 14 closure members;
/// canonical wide constants; re-parse OK. Imports: the 3
/// `i128::checked_add/sub/mul` empty externs ([B7], host-bound — the verified
/// fold_binop boundary).
const OVERFLOW_IR: &str = r#"; TrustIr text format v1
module "mir::closure::interp_overflow_root"

functy.0 = (u32, u32, u32, ptr, u32, u32, ptr, ptr, ptr) -> ()

functy.1 = (ptr, u32) -> ()

functy.2 = (ptr, u8, ptr, ptr) -> ()

functy.3 = (u8) -> (u64)

functy.4 = (ptr, u8, ptr, ptr) -> ()

functy.5 = (ptr, i128, i128) -> ()

functy.6 = (ptr, i128, i128) -> ()

functy.7 = (ptr, i128, i128) -> ()

functy.8 = (u8, ptr, ptr) -> (bool)

functy.9 = (u8, ptr, ptr) -> (bool)

functy.10 = (ptr, u32) -> ()

functy.11 = (ptr, ptr, u32) -> ()

functy.12 = (ptr) -> (i128)

functy.13 = (u32, i128, i128) -> (bool)

functy.14 = (i128) -> (u128)

functy.15 = (ptr, u32) -> ()

functy.16 = (u128) -> (i128)

fn @interp_overflow_root(functy.0) {
bb0(%0: u32, %1: u32, %2: u32, %3: ptr, %4: u32, %5: u32, %6: ptr, %7: ptr, %8: ptr):
    %20 = alloca (i128, i128), align 16
    %21 = alloca (i128, i128), align 16
    %22 = alloca (i128, i128, i128), align 16
    %23 = alloca i8, align 1
    %24 = alloca (i128, i128), align 16
    %25 = alloca i8, align 1
    %26 = const u32 0
    %27 = icmp ne u32 %2, %26
    %28 = load u128, ptr %3
    %29 = const i64 16
    %30 = gep i8, ptr %20, %29
    store u32 %1, ptr %30
    %31 = const i64 20
    %32 = gep i8, ptr %20, %31
    store bool %27, ptr %32
    store u128 %28, ptr %20
    %33 = const u32 0
    %34 = icmp ne u32 %5, %33
    %35 = load u128, ptr %6
    %36 = const i64 16
    %37 = gep i8, ptr %21, %36
    store u32 %4, ptr %37
    %38 = const i64 20
    %39 = gep i8, ptr %21, %38
    store bool %34, ptr %39
    store u128 %35, ptr %21
    call @func.1(%23, %0)
    br bb1(%7, %8)
bb1(%9: ptr, %10: ptr):
    %40 = load u8, ptr %23
    call @func.2(%22, %40, %20, %21)
    br bb2(%9, %10)
bb2(%11: ptr, %12: ptr):
    %41 = const i64 20
    %42 = gep i8, ptr %22, %41
    %43 = load i8, ptr %42
    %44 = const i8 2
    %45 = icmp eq i8 %43, %44
    %46 = const i64 1
    %47 = const i64 0
    %48 = select i64 %45, %46, %47
    switch %48 [ 0: bb5(%11, %12) 1: bb4(%11, %12) default: bb3 ]
bb3:
    unreachable
bb4(%13: ptr, %14: ptr):
    %49 = load i8, ptr %22
    store i8 %49, ptr %25
    %50 = const u64 0
    store u64 %50, ptr %13
    %51 = load u8, ptr %25
    %52 = call @func.3(%51)
    br bb6(%13, %14, %52)
bb5(%15: ptr, %16: ptr):
    %53 = load i128, ptr %22
    store i128 %53, ptr %24
    %54 = const i64 16
    %55 = gep i8, ptr %22, %54
    %56 = const i64 16
    %57 = gep i8, ptr %24, %56
    %58 = load i128, ptr %55
    store i128 %58, ptr %57
    %59 = const i64 32
    %60 = gep i8, ptr %22, %59
    %61 = load bool, ptr %60
    %62 = const u64 1
    store u64 %62, ptr %15
    %63 = const u64 0
    %64 = const i64 8
    %65 = gep i8, ptr %15, %64
    store u64 %63, ptr %65
    %66 = const i64 16
    %67 = gep i8, ptr %24, %66
    %68 = load u32, ptr %67
    %69 = const i64 16
    %70 = gep i8, ptr %15, %69
    store u32 %68, ptr %70
    %71 = const i64 20
    %72 = gep i8, ptr %24, %71
    %73 = load bool, ptr %72
    %74 = const u32 1
    %75 = const u32 0
    %76 = select u32 %73, %74, %75
    %77 = const i64 20
    %78 = gep i8, ptr %15, %77
    store u32 %76, ptr %78
    %79 = load u128, ptr %24
    %80 = const i64 32
    %81 = gep i8, ptr %15, %80
    store u128 %79, ptr %81
    %82 = const u32 1
    %83 = const u32 0
    %84 = select u32 %61, %82, %83
    store u32 %84, ptr %16
    br bb7
bb6(%17: ptr, %18: ptr, %19: u64):
    %85 = const i64 8
    %86 = gep i8, ptr %17, %85
    store u64 %19, ptr %86
    %87 = const u32 0
    %88 = const i64 16
    %89 = gep i8, ptr %17, %88
    store u32 %87, ptr %89
    %90 = const u32 0
    %91 = const i64 20
    %92 = gep i8, ptr %17, %91
    store u32 %90, ptr %92
    %93 = const u128 0
    %94 = const i64 32
    %95 = gep i8, ptr %17, %94
    store u128 %93, ptr %95
    %96 = const u32 255
    store u32 %96, ptr %18
    br bb7
bb7:
    ret
}

fn @ovop_from_u32(functy.1) {
bb0(%0: ptr, %1: u32):
    switch %1 [ 0: bb3 1: bb2 default: bb1 ]
bb1:
    %2 = const i8 2
    store i8 %2, ptr %0
    br bb4
bb2:
    %3 = const i8 1
    store i8 %3, ptr %0
    br bb4
bb3:
    %4 = const i8 0
    store i8 %4, ptr %0
    br bb4
bb4:
    ret
}

fn @eval_int_overflow(functy.2) {
bb0(%0: ptr, %1: u8, %2: ptr, %3: ptr):
    %5 = alloca i8, align 1
    %6 = alloca i8, align 1
    %7 = alloca (i128, i128), align 16
    %8 = alloca i8, align 1
    %9 = alloca (i128, i128), align 16
    %10 = alloca i8, align 1
    %11 = alloca (i128, i128, i128), align 16
    store u8 %1, ptr %5
    %12 = const i64 16
    %13 = gep i8, ptr %2, %12
    %14 = load u32, ptr %13
    %15 = const i64 16
    %16 = gep i8, ptr %3, %15
    %17 = load u32, ptr %16
    %18 = icmp ne u32 %14, %17
    condbr %18, bb1, bb2
bb1:
    %19 = const i8 0
    store i8 %19, ptr %6
    %20 = load i8, ptr %6
    store i8 %20, ptr %0
    %21 = const i64 20
    %22 = gep i8, ptr %0, %21
    %23 = const i8 2
    store i8 %23, ptr %22
    br bb14
bb2:
    %24 = load i8, ptr %5
    %25 = sext i8 %24 to i64
    switch %25 [ 0: bb6 1: bb5 2: bb4 default: bb3 ]
bb3:
    unreachable
bb4:
    %26 = const i8 2
    store i8 %26, ptr %8
    br bb7
bb5:
    %27 = const i8 1
    store i8 %27, ptr %8
    br bb7
bb6:
    %28 = const i8 0
    store i8 %28, ptr %8
    br bb7
bb7:
    %29 = load u8, ptr %8
    call @func.4(%7, %29, %2, %3)
    br bb8
bb8:
    %30 = const i64 20
    %31 = gep i8, ptr %7, %30
    %32 = load i8, ptr %31
    %33 = const i8 2
    %34 = icmp eq i8 %32, %33
    %35 = const i64 1
    %36 = const i64 0
    %37 = select i64 %34, %35, %36
    switch %37 [ 0: bb10 1: bb9 default: bb3 ]
bb9:
    %38 = load i8, ptr %7
    store i8 %38, ptr %10
    %39 = load i8, ptr %10
    store i8 %39, ptr %0
    %40 = const i64 20
    %41 = gep i8, ptr %0, %40
    %42 = const i8 2
    store i8 %42, ptr %41
    br bb14
bb10:
    %43 = load i128, ptr %7
    store i128 %43, ptr %9
    %44 = const i64 16
    %45 = gep i8, ptr %7, %44
    %46 = const i64 16
    %47 = gep i8, ptr %9, %46
    %48 = load i128, ptr %45
    store i128 %48, ptr %47
    %49 = const i64 20
    %50 = gep i8, ptr %2, %49
    %51 = load bool, ptr %50
    condbr %51, bb11, bb12
bb11:
    %52 = load u8, ptr %5
    %53 = call @func.8(%52, %2, %3)
    br bb13(%53)
bb12:
    %54 = load u8, ptr %5
    %55 = call @func.9(%54, %2, %3)
    br bb13(%55)
bb13(%4: bool):
    %56 = load i128, ptr %9
    store i128 %56, ptr %11
    %57 = const i64 16
    %58 = gep i8, ptr %9, %57
    %59 = const i64 16
    %60 = gep i8, ptr %11, %59
    %61 = load i128, ptr %58
    store i128 %61, ptr %60
    %62 = const i64 32
    %63 = gep i8, ptr %11, %62
    store bool %4, ptr %63
    %64 = load i128, ptr %11
    store i128 %64, ptr %0
    %65 = const i64 16
    %66 = gep i8, ptr %11, %65
    %67 = const i64 16
    %68 = gep i8, ptr %0, %67
    %69 = load i128, ptr %66
    store i128 %69, ptr %68
    %70 = const i64 32
    %71 = gep i8, ptr %11, %70
    %72 = const i64 32
    %73 = gep i8, ptr %0, %72
    %74 = load i128, ptr %71
    store i128 %74, ptr %73
    br bb14
bb14:
    ret
}

fn @err_code(functy.3) {
bb0(%0: u8):
    %2 = alloca i8, align 1
    store u8 %0, ptr %2
    %3 = load i8, ptr %2
    %4 = sext i8 %3 to i64
    switch %4 [ 0: bb12 1: bb11 2: bb10 3: bb9 4: bb8 5: bb7 6: bb6 7: bb5 8: bb4 9: bb3 10: bb2 default: bb1 ]
bb1:
    unreachable
bb2:
    %5 = const u64 11
    br bb13(%5)
bb3:
    %6 = const u64 10
    br bb13(%6)
bb4:
    %7 = const u64 9
    br bb13(%7)
bb5:
    %8 = const u64 8
    br bb13(%8)
bb6:
    %9 = const u64 7
    br bb13(%9)
bb7:
    %10 = const u64 6
    br bb13(%10)
bb8:
    %11 = const u64 5
    br bb13(%11)
bb9:
    %12 = const u64 4
    br bb13(%12)
bb10:
    %13 = const u64 3
    br bb13(%13)
bb11:
    %14 = const u64 2
    br bb13(%14)
bb12:
    %15 = const u64 1
    br bb13(%15)
bb13(%1: u64):
    ret %1
}

fn @eval_int_binop(functy.4) {
bb0(%0: ptr, %1: u8, %2: ptr, %3: ptr):
    %76 = alloca i8, align 1
    %77 = alloca i8, align 1
    %78 = alloca (i128, i128), align 16
    %79 = alloca i8, align 1
    %80 = alloca i8, align 1
    %81 = alloca i8, align 1
    %82 = alloca i8, align 1
    %83 = alloca i8, align 1
    %84 = alloca i8, align 1
    %85 = alloca i8, align 1
    %86 = alloca (i32, i32), align 4
    %87 = alloca i8, align 1
    %88 = alloca (i32, i32), align 4
    %89 = alloca i8, align 1
    %90 = alloca (i32, i32), align 4
    %91 = alloca i8, align 1
    %92 = alloca i8, align 1
    %93 = alloca (i128, i128), align 16
    store u8 %1, ptr %76
    %94 = const i64 16
    %95 = gep i8, ptr %2, %94
    %96 = load u32, ptr %95
    %97 = const i64 16
    %98 = gep i8, ptr %3, %97
    %99 = load u32, ptr %98
    %100 = icmp ne u32 %96, %99
    condbr %100, bb1, bb2
bb1:
    %101 = const i8 0
    store i8 %101, ptr %77
    %102 = load i8, ptr %77
    store i8 %102, ptr %0
    %103 = const i64 20
    %104 = gep i8, ptr %0, %103
    %105 = const i8 2
    store i8 %105, ptr %104
    br bb56
bb2:
    %106 = const i64 16
    %107 = gep i8, ptr %2, %106
    %108 = load u32, ptr %107
    call @func.10(%78, %108)
    br bb3
bb3:
    %109 = load i128, ptr %78
    %110 = trunc i128 %109 to i64
    switch %110 [ 0: bb5 1: bb6 default: bb4 ]
bb4:
    unreachable
bb5:
    %111 = const i8 1
    store i8 %111, ptr %79
    %112 = load i8, ptr %79
    store i8 %112, ptr %0
    %113 = const i64 20
    %114 = gep i8, ptr %0, %113
    %115 = const i8 2
    store i8 %115, ptr %114
    br bb56
bb6:
    %116 = const i64 16
    %117 = gep i8, ptr %78, %116
    %118 = load u128, ptr %117
    %119 = load i8, ptr %76
    %120 = sext i8 %119 to i64
    switch %120 [ 0: bb20(%118) 1: bb19(%118) 2: bb18(%118) 3: bb14(%118) 4: bb12(%118) 5: bb13(%118) 6: bb11(%118) 7: bb7 8: bb7 9: bb7 10: bb7 11: bb7 12: bb7 13: bb7 14: bb17(%118) 15: bb16(%118) 16: bb15(%118) 17: bb10(%118) 18: bb9(%118) 19: bb8(%118) default: bb4 ]
bb7:
    %121 = const i8 9
    store i8 %121, ptr %92
    %122 = load i8, ptr %92
    store i8 %122, ptr %0
    %123 = const i64 20
    %124 = gep i8, ptr %0, %123
    %125 = const i8 2
    store i8 %125, ptr %124
    br bb56
bb8(%4: u128):
    %126 = const i64 16
    %127 = gep i8, ptr %2, %126
    %128 = load u32, ptr %127
    call @func.11(%90, %3, %128)
    br bb51(%4)
bb9(%5: u128):
    %129 = const i64 16
    %130 = gep i8, ptr %2, %129
    %131 = load u32, ptr %130
    call @func.11(%88, %3, %131)
    br bb48(%5)
bb10(%6: u128):
    %132 = const i64 16
    %133 = gep i8, ptr %2, %132
    %134 = load u32, ptr %133
    call @func.11(%86, %3, %134)
    br bb45(%6)
bb11(%7: u128):
    %135 = call @func.12(%3)
    br bb36(%7, %135)
bb12(%8: u128):
    %136 = call @func.12(%3)
    br bb27(%8, %136)
bb13(%9: u128):
    %137 = load u128, ptr %3
    %138 = const u128 0
    %139 = icmp eq u128 %137, %138
    condbr %139, bb24, bb25(%9)
bb14(%10: u128):
    %140 = load u128, ptr %3
    %141 = const u128 0
    %142 = icmp eq u128 %140, %141
    condbr %142, bb21, bb22(%10)
bb15(%11: u128):
    %143 = load u128, ptr %2
    %144 = load u128, ptr %3
    %145 = xor u128 %143, %144
    br bb55(%11, %145)
bb16(%12: u128):
    %146 = load u128, ptr %2
    %147 = load u128, ptr %3
    %148 = or u128 %146, %147
    br bb55(%12, %148)
bb17(%13: u128):
    %149 = load u128, ptr %2
    %150 = load u128, ptr %3
    %151 = and u128 %149, %150
    br bb55(%13, %151)
bb18(%14: u128):
    %152 = load u128, ptr %2
    %153 = load u128, ptr %3
    %154 = mul u128 %152, %153
    br bb55(%14, %154)
bb19(%15: u128):
    %155 = load u128, ptr %2
    %156 = load u128, ptr %3
    %157 = sub u128 %155, %156
    br bb55(%15, %157)
bb20(%16: u128):
    %158 = load u128, ptr %2
    %159 = load u128, ptr %3
    %160 = add u128 %158, %159
    br bb55(%16, %160)
bb21:
    %161 = const i8 2
    store i8 %161, ptr %80
    %162 = load i8, ptr %80
    store i8 %162, ptr %0
    %163 = const i64 20
    %164 = gep i8, ptr %0, %163
    %165 = const i8 2
    store i8 %165, ptr %164
    br bb56
bb22(%17: u128):
    %166 = load u128, ptr %2
    %167 = load u128, ptr %3
    %168 = const u128 0
    %169 = icmp eq u128 %167, %168
    %170 = const bool false
    %171 = icmp eq bool %169, %170
    condbr %171, bb23(%17, %166, %167), bb57
bb23(%18: u128, %19: u128, %20: u128):
    %172 = udiv u128 %19, %20
    br bb55(%18, %172)
bb24:
    %173 = const i8 3
    store i8 %173, ptr %81
    %174 = load i8, ptr %81
    store i8 %174, ptr %0
    %175 = const i64 20
    %176 = gep i8, ptr %0, %175
    %177 = const i8 2
    store i8 %177, ptr %176
    br bb56
bb25(%21: u128):
    %178 = load u128, ptr %2
    %179 = load u128, ptr %3
    %180 = const u128 0
    %181 = icmp eq u128 %179, %180
    %182 = const bool false
    %183 = icmp eq bool %181, %182
    condbr %183, bb26(%21, %178, %179), bb57
bb26(%22: u128, %23: u128, %24: u128):
    %184 = urem u128 %23, %24
    br bb55(%22, %184)
bb27(%25: u128, %26: i128):
    %185 = const i128 0
    %186 = icmp eq i128 %26, %185
    condbr %186, bb28, bb29(%25, %26)
bb28:
    %187 = const i8 4
    store i8 %187, ptr %82
    %188 = load i8, ptr %82
    store i8 %188, ptr %0
    %189 = const i64 20
    %190 = gep i8, ptr %0, %189
    %191 = const i8 2
    store i8 %191, ptr %190
    br bb56
bb29(%27: u128, %28: i128):
    %192 = call @func.12(%2)
    br bb30(%27, %28, %192)
bb30(%29: u128, %30: i128, %31: i128):
    %193 = const i64 16
    %194 = gep i8, ptr %2, %193
    %195 = load u32, ptr %194
    %196 = call @func.13(%195, %31, %30)
    br bb31(%29, %30, %31, %196)
bb31(%32: u128, %33: i128, %34: i128, %35: bool):
    condbr %35, bb32, bb33(%32, %33, %34)
bb32:
    %197 = const i8 5
    store i8 %197, ptr %83
    %198 = load i8, ptr %83
    store i8 %198, ptr %0
    %199 = const i64 20
    %200 = gep i8, ptr %0, %199
    %201 = const i8 2
    store i8 %201, ptr %200
    br bb56
bb33(%36: u128, %37: i128, %38: i128):
    %202 = const i128 0
    %203 = icmp eq i128 %37, %202
    %204 = const bool false
    %205 = icmp eq bool %203, %204
    condbr %205, bb34(%36, %37, %38), bb57
bb34(%39: u128, %40: i128, %41: i128):
    %206 = const i128 -1
    %207 = icmp eq i128 %40, %206
    %208 = const i128 -170141183460469231731687303715884105728
    %209 = icmp eq i128 %41, %208
    %210 = const bool false
    %211 = select bool %207, %209, %210
    %212 = const bool false
    %213 = icmp eq bool %211, %212
    condbr %213, bb35(%39, %40, %41), bb57
bb35(%42: u128, %43: i128, %44: i128):
    %214 = sdiv i128 %44, %43
    %215 = call @func.14(%214)
    br bb55(%42, %215)
bb36(%45: u128, %46: i128):
    %216 = const i128 0
    %217 = icmp eq i128 %46, %216
    condbr %217, bb37, bb38(%45, %46)
bb37:
    %218 = const i8 6
    store i8 %218, ptr %84
    %219 = load i8, ptr %84
    store i8 %219, ptr %0
    %220 = const i64 20
    %221 = gep i8, ptr %0, %220
    %222 = const i8 2
    store i8 %222, ptr %221
    br bb56
bb38(%47: u128, %48: i128):
    %223 = call @func.12(%2)
    br bb39(%47, %48, %223)
bb39(%49: u128, %50: i128, %51: i128):
    %224 = const i64 16
    %225 = gep i8, ptr %2, %224
    %226 = load u32, ptr %225
    %227 = call @func.13(%226, %51, %50)
    br bb40(%49, %50, %51, %227)
bb40(%52: u128, %53: i128, %54: i128, %55: bool):
    condbr %55, bb41, bb42(%52, %53, %54)
bb41:
    %228 = const i8 7
    store i8 %228, ptr %85
    %229 = load i8, ptr %85
    store i8 %229, ptr %0
    %230 = const i64 20
    %231 = gep i8, ptr %0, %230
    %232 = const i8 2
    store i8 %232, ptr %231
    br bb56
bb42(%56: u128, %57: i128, %58: i128):
    %233 = const i128 0
    %234 = icmp eq i128 %57, %233
    %235 = const bool false
    %236 = icmp eq bool %234, %235
    condbr %236, bb43(%56, %57, %58), bb57
bb43(%59: u128, %60: i128, %61: i128):
    %237 = const i128 -1
    %238 = icmp eq i128 %60, %237
    %239 = const i128 -170141183460469231731687303715884105728
    %240 = icmp eq i128 %61, %239
    %241 = const bool false
    %242 = select bool %238, %240, %241
    %243 = const bool false
    %244 = icmp eq bool %242, %243
    condbr %244, bb44(%59, %60, %61), bb57
bb44(%62: u128, %63: i128, %64: i128):
    %245 = srem i128 %64, %63
    %246 = call @func.14(%245)
    br bb55(%62, %246)
bb45(%65: u128):
    %247 = load i8, ptr %86
    %248 = sext i8 %247 to i64
    switch %248 [ 0: bb47(%65) 1: bb46 default: bb4 ]
bb46:
    %249 = const i64 1
    %250 = gep i8, ptr %86, %249
    %251 = load i8, ptr %250
    store i8 %251, ptr %87
    %252 = load i8, ptr %87
    store i8 %252, ptr %0
    %253 = const i64 20
    %254 = gep i8, ptr %0, %253
    %255 = const i8 2
    store i8 %255, ptr %254
    br bb56
bb47(%66: u128):
    %256 = const i64 4
    %257 = gep i8, ptr %86, %256
    %258 = load u32, ptr %257
    %259 = load u128, ptr %2
    %260 = zext u32 %258 to u128
    %261 = shl u128 %259, %260
    br bb55(%66, %261)
bb48(%67: u128):
    %262 = load i8, ptr %88
    %263 = sext i8 %262 to i64
    switch %263 [ 0: bb50(%67) 1: bb49 default: bb4 ]
bb49:
    %264 = const i64 1
    %265 = gep i8, ptr %88, %264
    %266 = load i8, ptr %265
    store i8 %266, ptr %89
    %267 = load i8, ptr %89
    store i8 %267, ptr %0
    %268 = const i64 20
    %269 = gep i8, ptr %0, %268
    %270 = const i8 2
    store i8 %270, ptr %269
    br bb56
bb50(%68: u128):
    %271 = const i64 4
    %272 = gep i8, ptr %88, %271
    %273 = load u32, ptr %272
    %274 = load u128, ptr %2
    %275 = zext u32 %273 to u128
    %276 = lshr u128 %274, %275
    br bb55(%68, %276)
bb51(%69: u128):
    %277 = load i8, ptr %90
    %278 = sext i8 %277 to i64
    switch %278 [ 0: bb53(%69) 1: bb52 default: bb4 ]
bb52:
    %279 = const i64 1
    %280 = gep i8, ptr %90, %279
    %281 = load i8, ptr %280
    store i8 %281, ptr %91
    %282 = load i8, ptr %91
    store i8 %282, ptr %0
    %283 = const i64 20
    %284 = gep i8, ptr %0, %283
    %285 = const i8 2
    store i8 %285, ptr %284
    br bb56
bb53(%70: u128):
    %286 = const i64 4
    %287 = gep i8, ptr %90, %286
    %288 = load u32, ptr %287
    %289 = call @func.12(%2)
    br bb54(%70, %288, %289)
bb54(%71: u128, %72: u32, %73: i128):
    %290 = zext u32 %72 to i128
    %291 = ashr i128 %73, %290
    %292 = call @func.14(%291)
    br bb55(%71, %292)
bb55(%74: u128, %75: u128):
    %293 = and u128 %75, %74
    %294 = const i64 16
    %295 = gep i8, ptr %2, %294
    %296 = load u32, ptr %295
    %297 = const i64 20
    %298 = gep i8, ptr %2, %297
    %299 = load bool, ptr %298
    %300 = const i64 16
    %301 = gep i8, ptr %93, %300
    store u32 %296, ptr %301
    %302 = const i64 20
    %303 = gep i8, ptr %93, %302
    store bool %299, ptr %303
    store u128 %293, ptr %93
    %304 = load i128, ptr %93
    store i128 %304, ptr %0
    %305 = const i64 16
    %306 = gep i8, ptr %93, %305
    %307 = const i64 16
    %308 = gep i8, ptr %0, %307
    %309 = load i128, ptr %306
    store i128 %309, ptr %308
    br bb56
bb56:
    ret
bb57:
    unreachable
}

fn @_RNvMs2_NtCs2EYQwhfuABO_4core3numn11checked_mulCserZe6P5R4Ij_22trust_interp_int_slice(functy.5) {
}

fn @_RNvMs2_NtCs2EYQwhfuABO_4core3numn11checked_subCserZe6P5R4Ij_22trust_interp_int_slice(functy.6) {
}

fn @_RNvMs2_NtCs2EYQwhfuABO_4core3numn11checked_addCserZe6P5R4Ij_22trust_interp_int_slice(functy.7) {
}

fn @signed_overflow(functy.8) {
bb0(%0: u8, %1: ptr, %2: ptr):
    %29 = alloca i8, align 1
    %30 = alloca (i128, i128), align 16
    %31 = alloca (i128, i128), align 16
    store u8 %0, ptr %29
    %32 = const i64 16
    %33 = gep i8, ptr %1, %32
    %34 = load u32, ptr %33
    call @func.15(%30, %34)
    br bb1
bb1:
    %35 = load i128, ptr %30
    %36 = const i64 16
    %37 = gep i8, ptr %30, %36
    %38 = load i128, ptr %37
    %39 = call @func.12(%1)
    br bb2(%35, %38, %39)
bb2(%3: i128, %4: i128, %5: i128):
    %40 = call @func.12(%2)
    br bb3(%3, %4, %5, %40)
bb3(%6: i128, %7: i128, %8: i128, %9: i128):
    %41 = load i8, ptr %29
    %42 = sext i8 %41 to i64
    switch %42 [ 0: bb7(%6, %7, %8, %9) 1: bb6(%6, %7, %8, %9) 2: bb5(%6, %7, %8, %9) default: bb4 ]
bb4:
    unreachable
bb5(%10: i128, %11: i128, %12: i128, %13: i128):
    call @func.5(%31, %12, %13)
    br bb8(%10, %11)
bb6(%14: i128, %15: i128, %16: i128, %17: i128):
    call @func.6(%31, %16, %17)
    br bb8(%14, %15)
bb7(%18: i128, %19: i128, %20: i128, %21: i128):
    call @func.7(%31, %20, %21)
    br bb8(%18, %19)
bb8(%22: i128, %23: i128):
    %43 = load i128, ptr %31
    %44 = trunc i128 %43 to i64
    switch %44 [ 1: bb10(%22, %23) 0: bb9 default: bb4 ]
bb9:
    %45 = const bool false
    br bb13(%45)
bb10(%24: i128, %25: i128):
    %46 = const i64 16
    %47 = gep i8, ptr %31, %46
    %48 = load i128, ptr %47
    %49 = icmp sge i128 %48, %24
    condbr %49, bb11(%25, %47), bb9
bb11(%26: i128, %27: ptr):
    %50 = load i128, ptr %27
    %51 = icmp sle i128 %50, %26
    condbr %51, bb12, bb9
bb12:
    %52 = const i64 16
    %53 = gep i8, ptr %31, %52
    %54 = load i128, ptr %53
    %55 = const bool true
    br bb13(%55)
bb13(%28: bool):
    %56 = const bool false
    %57 = icmp eq bool %28, %56
    ret %57
}

fn @unsigned_overflow(functy.9) {
bb0(%0: u8, %1: ptr, %2: ptr):
    %26 = alloca i8, align 1
    %27 = alloca (i128, i128), align 16
    store u8 %0, ptr %26
    %28 = const i64 16
    %29 = gep i8, ptr %1, %28
    %30 = load u32, ptr %29
    call @func.10(%27, %30)
    br bb1
bb1:
    %31 = load i128, ptr %27
    %32 = trunc i128 %31 to i64
    switch %32 [ 0: bb3 1: bb4 default: bb2 ]
bb2:
    unreachable
bb3:
    %33 = const bool false
    br bb20(%33)
bb4:
    %34 = const i64 16
    %35 = gep i8, ptr %27, %34
    %36 = load u128, ptr %35
    %37 = load i8, ptr %26
    %38 = sext i8 %37 to i64
    switch %38 [ 0: bb7(%36) 1: bb6 2: bb5(%36) default: bb2 ]
bb5(%3: u128):
    %39 = load u128, ptr %1
    %40 = load u128, ptr %2
    %41 = mul u128 %39, %40
    %42 = load u128, ptr %2
    %43 = const u128 0
    %44 = icmp ne u128 %42, %43
    condbr %44, bb10(%3, %41), bb11(%3, %41)
bb6:
    %45 = load u128, ptr %1
    %46 = load u128, ptr %2
    %47 = icmp ult u128 %45, %46
    br bb20(%47)
bb7(%4: u128):
    %48 = load u128, ptr %1
    %49 = load u128, ptr %2
    %50 = add u128 %48, %49
    %51 = load u128, ptr %1
    %52 = icmp ult u128 %50, %51
    condbr %52, bb8, bb9(%4, %50)
bb8:
    %53 = const bool true
    br bb20(%53)
bb9(%5: u128, %6: u128):
    %54 = icmp ugt u128 %6, %5
    br bb20(%54)
bb10(%7: u128, %8: u128):
    %55 = load u128, ptr %1
    %56 = load u128, ptr %2
    %57 = const u128 0
    %58 = icmp eq u128 %56, %57
    %59 = const bool false
    %60 = icmp eq bool %58, %59
    condbr %60, bb12(%7, %8, %55, %56), bb21
bb11(%9: u128, %10: u128):
    %61 = const bool false
    br bb13(%9, %10, %61)
bb12(%11: u128, %12: u128, %13: u128, %14: u128):
    %62 = const u128 340282366920938463463374607431768211455
    %63 = udiv u128 %62, %14
    %64 = icmp ugt u128 %13, %63
    br bb13(%11, %12, %64)
bb13(%15: u128, %16: u128, %17: bool):
    condbr %17, bb15, bb14(%15, %16)
bb14(%18: u128, %19: u128):
    %65 = icmp ugt u128 %19, %18
    condbr %65, bb15, bb16(%18)
bb15:
    %66 = const bool true
    br bb20(%66)
bb16(%20: u128):
    %67 = load u128, ptr %2
    %68 = const u128 0
    %69 = icmp ne u128 %67, %68
    condbr %69, bb17(%20), bb18
bb17(%21: u128):
    %70 = load u128, ptr %1
    %71 = load u128, ptr %2
    %72 = const u128 0
    %73 = icmp eq u128 %71, %72
    %74 = const bool false
    %75 = icmp eq bool %73, %74
    condbr %75, bb19(%21, %70, %71), bb21
bb18:
    %76 = const bool false
    br bb20(%76)
bb19(%22: u128, %23: u128, %24: u128):
    %77 = udiv u128 %22, %24
    %78 = icmp ugt u128 %23, %77
    br bb20(%78)
bb20(%25: bool):
    ret %25
bb21:
    unreachable
}

fn @int_mask(functy.10) {
bb0(%0: ptr, %1: u32):
    %5 = const u32 1
    %6 = icmp ule u32 %5, %1
    condbr %6, bb4(%1), bb3(%1)
bb1:
    %7 = const i128 0
    store i128 %7, ptr %0
    br bb6
bb2(%2: u32):
    %8 = const u128 1
    %9 = zext u32 %2 to u128
    %10 = shl u128 %8, %9
    %11 = const u128 1
    %12 = sub u128 %10, %11
    %13 = const i64 16
    %14 = gep i8, ptr %0, %13
    store u128 %12, ptr %14
    %15 = const i128 1
    store i128 %15, ptr %0
    br bb6
bb3(%3: u32):
    switch %3 [ 128: bb5 default: bb1 ]
bb4(%4: u32):
    %16 = const u32 127
    %17 = icmp ule u32 %4, %16
    condbr %17, bb2(%4), bb3(%4)
bb5:
    %18 = const u128 340282366920938463463374607431768211455
    %19 = const i64 16
    %20 = gep i8, ptr %0, %19
    store u128 %18, ptr %20
    %21 = const i128 1
    store i128 %21, ptr %0
    br bb6
bb6:
    ret
}

fn @shift_amount(functy.11) {
bb0(%0: ptr, %1: ptr, %2: u32):
    %3 = alloca i8, align 1
    %4 = load u128, ptr %1
    %5 = zext u32 %2 to u128
    %6 = icmp uge u128 %4, %5
    condbr %6, bb1, bb2
bb1:
    %7 = const i8 8
    store i8 %7, ptr %3
    %8 = const i64 1
    %9 = gep i8, ptr %0, %8
    %10 = load i8, ptr %3
    store i8 %10, ptr %9
    %11 = const i8 1
    store i8 %11, ptr %0
    br bb3
bb2:
    %12 = load u128, ptr %1
    %13 = trunc u128 %12 to u32
    %14 = const i64 4
    %15 = gep i8, ptr %0, %14
    store u32 %13, ptr %15
    %16 = const i8 0
    store i8 %16, ptr %0
    br bb3
bb3:
    ret
}

fn @InterpretInt__as_signed(functy.12) {
bb0(%0: ptr):
    %4 = alloca (i128, i128), align 16
    %5 = const i64 16
    %6 = gep i8, ptr %0, %5
    %7 = load u32, ptr %6
    %8 = const u32 128
    %9 = icmp eq u32 %7, %8
    condbr %9, bb1, bb2
bb1:
    %10 = load u128, ptr %0
    %11 = call @func.16(%10)
    br bb10(%11)
bb2:
    %12 = const i64 16
    %13 = gep i8, ptr %0, %12
    %14 = load u32, ptr %13
    call @func.10(%4, %14)
    br bb3
bb3:
    %15 = load i128, ptr %4
    %16 = trunc i128 %15 to i64
    switch %16 [ 0: bb5 1: bb6 default: bb4 ]
bb4:
    unreachable
bb5:
    %17 = const i128 0
    br bb10(%17)
bb6:
    %18 = const i64 16
    %19 = gep i8, ptr %4, %18
    %20 = load u128, ptr %19
    %21 = const i64 16
    %22 = gep i8, ptr %0, %21
    %23 = load u32, ptr %22
    %24 = const u32 1
    %25 = sub u32 %23, %24
    %26 = const u128 1
    %27 = zext u32 %25 to u128
    %28 = shl u128 %26, %27
    %29 = load u128, ptr %0
    %30 = and u128 %29, %28
    %31 = const u128 0
    %32 = icmp eq u128 %30, %31
    condbr %32, bb7, bb8(%20)
bb7:
    %33 = load u128, ptr %0
    %34 = call @func.16(%33)
    br bb10(%34)
bb8(%1: u128):
    %35 = load u128, ptr %0
    %36 = not u128 %35
    %37 = and u128 %36, %1
    %38 = const u128 1
    %39 = add u128 %37, %38
    %40 = and u128 %39, %1
    %41 = call @func.16(%40)
    br bb9(%41)
bb9(%2: i128):
    %42 = neg i128 %2
    br bb10(%42)
bb10(%3: i128):
    ret %3
}

fn @signed_div_overflows(functy.13) {
bb0(%0: u32, %1: i128, %2: i128):
    %7 = alloca (i128, i128), align 16
    call @func.15(%7, %0)
    br bb1(%1, %2)
bb1(%3: i128, %4: i128):
    %8 = load i128, ptr %7
    %9 = icmp eq i128 %3, %8
    condbr %9, bb2(%4), bb3
bb2(%5: i128):
    %10 = const i128 -1
    %11 = icmp eq i128 %5, %10
    br bb4(%11)
bb3:
    %12 = const bool false
    br bb4(%12)
bb4(%6: bool):
    ret %6
}

fn @i128_as_u128(functy.14) {
bb0(%0: i128):
    %1 = alloca i128, align 16
    %2 = alloca i64, align 8
    store i128 %0, ptr %1
    store ptr %1, ptr %2
    %3 = load ptr, ptr %2
    %4 = load u128, ptr %3
    ret %4
}

fn @signed_bounds(functy.15) {
bb0(%0: ptr, %1: u32):
    %7 = const u32 128
    %8 = icmp eq u32 %1, %7
    condbr %8, bb1, bb2(%1)
bb1:
    %9 = const i128 -170141183460469231731687303715884105728
    store i128 %9, ptr %0
    %10 = const i128 170141183460469231731687303715884105727
    %11 = const i64 16
    %12 = gep i8, ptr %0, %11
    store i128 %10, ptr %12
    br bb5
bb2(%2: u32):
    %13 = const u32 1
    %14 = sub u32 %2, %13
    %15 = const u128 1
    %16 = zext u32 %14 to u128
    %17 = shl u128 %15, %16
    %18 = call @func.16(%17)
    br bb3(%17, %18)
bb3(%3: u128, %4: i128):
    %19 = neg i128 %4
    %20 = const u128 1
    %21 = sub u128 %3, %20
    %22 = call @func.16(%21)
    br bb4(%19, %22)
bb4(%5: i128, %6: i128):
    store i128 %5, ptr %0
    %23 = const i64 16
    %24 = gep i8, ptr %0, %23
    store i128 %6, ptr %24
    br bb5
bb5:
    ret
}

fn @u128_as_i128(functy.16) {
bb0(%0: u128):
    %1 = alloca i128, align 16
    %2 = alloca i64, align 8
    store u128 %0, ptr %1
    store ptr %1, ptr %2
    %3 = load ptr, ptr %2
    %4 = load i128, ptr %3
    ret %4
}
"#;

/// The PIN module: MIR emit of `interp_bitcast_pin_root` — byte-for-byte the
/// production spelling `*out = *x as i128`, which the frontend lowers to
/// `bitcast u128 -> i128`. 261 bytes; 1 member; validate_module = 0;
/// re-parse OK. trust-cg ISel CANNOT lower it (this round's pinned finding).
const BITCAST_PIN_IR: &str = r#"; TrustIr text format v1
module "mir::closure::interp_bitcast_pin_root"

functy.0 = (ptr, ptr) -> ()

fn @interp_bitcast_pin_root(functy.0) {
bb0(%0: ptr, %1: ptr):
    %2 = load u128, ptr %0
    %3 = bitcast u128 %2 to i128
    store i128 %3, ptr %1
    ret
}
"#;

// ═══════════════════════════════════════════════════════════════════════════
// Differential tests (one per verified fn/cluster; run ONE per process)
// ═══════════════════════════════════════════════════════════════════════════

/// `int_mask` — exhaustive over bits 0..=300 plus extremes. Every valid width
/// mask and every None edge, native == JIT.
#[test]
fn trust_interp_int_mask_exhaustive_native_eq_jit() {
    let bits_menu: Vec<u32> = (0..=300).chain([1000, 65535, u32::MAX]).collect();
    let expected = bits_menu.len();
    let menu = bits_menu.clone();
    let rows = run_watchdogged::<(u32, u64, u128)>("int_mask", expected, move |tx| {
        let buffer = jit_module(INT_MASK_IR, "int_mask");
        // SAFETY: machine code for functy.0 = (u32, ptr, ptr) -> ().
        let f: unsafe extern "C" fn(u32, *mut u64, *mut u128) =
            unsafe { std::mem::transmute(bind(&buffer, "interp_int_mask_root")) };
        for &bits in &menu {
            let (mut present, mut mask) = (0xDEADu64, 0xDEADu128);
            unsafe { f(bits, &mut present, &mut mask) };
            if tx.send((bits, present, mask)).is_err() {
                return;
            }
        }
    });
    for &(bits, present, mask) in &rows {
        let native = n_int_mask(bits);
        let jit = (present != 0).then_some(mask);
        assert_eq!(
            native, jit,
            "int_mask({bits}): native={native:?} jit={jit:?}"
        );
    }
    // Ground truth (independent literals).
    let find = |b: u32| {
        rows.iter()
            .find(|r| r.0 == b)
            .map(|r| (r.1 != 0).then_some(r.2))
            .unwrap()
    };
    assert_eq!(find(8), Some(0xFF));
    assert_eq!(find(64), Some(u64::MAX as u128));
    assert_eq!(find(127), Some(u128::MAX >> 1));
    assert_eq!(
        find(128),
        Some(u128::MAX),
        "the u128::MAX const the validator flags — codegen must still produce the right bits"
    );
    assert_eq!(find(0), None);
    assert_eq!(find(129), None);

    // NEGATIVE CONTROL (armed): an off-by-one oracle must DISAGREE with the JIT.
    fn int_mask_corrupt(bits: u32) -> Option<u128> {
        n_int_mask(bits).map(|m| m >> 1) // bug: mask one bit short
    }
    assert_ne!(int_mask_corrupt(8), find(8), "negative control must FAIL");
}

/// `signed_bounds` — bits 1..=128, min/max native == JIT (both i128s cross
/// by out-pointer).
#[test]
fn trust_interp_signed_bounds_native_eq_jit() {
    let expected = 128;
    let rows = run_watchdogged::<(u32, i128, i128)>("signed_bounds", expected, move |tx| {
        let buffer = jit_module(SIGNED_BOUNDS_IR, "signed_bounds");
        // SAFETY: machine code for functy.0 = (u32, ptr, ptr) -> ().
        let f: unsafe extern "C" fn(u32, *mut i128, *mut i128) =
            unsafe { std::mem::transmute(bind(&buffer, "interp_signed_bounds_root")) };
        for bits in 1..=128u32 {
            let (mut min, mut max) = (0xDEADi128, 0xDEADi128);
            unsafe { f(bits, &mut min, &mut max) };
            if tx.send((bits, min, max)).is_err() {
                return;
            }
        }
    });
    for &(bits, min, max) in &rows {
        assert_eq!(
            n_signed_bounds(bits),
            (min, max),
            "signed_bounds({bits}) diverged"
        );
    }
    let find = |b: u32| rows.iter().find(|r| r.0 == b).map(|r| (r.1, r.2)).unwrap();
    assert_eq!(find(8), (i8::MIN as i128, i8::MAX as i128));
    assert_eq!(find(16), (i16::MIN as i128, i16::MAX as i128));
    assert_eq!(find(32), (i32::MIN as i128, i32::MAX as i128));
    assert_eq!(find(64), (i64::MIN as i128, i64::MAX as i128));
    assert_eq!(find(128), (i128::MIN, i128::MAX));

    // NEGATIVE CONTROL: swapped bounds must disagree.
    let (min8, max8) = find(8);
    assert_ne!((max8, min8), (min8, max8), "negative control must FAIL");
}

/// `InterpretInt::from_raw` — the `?`-verbatim constructor through the
/// host-bound Option-Try shims, checked against BOTH the transcription and
/// the PRODUCTION `trust_ir::InterpretInt::from_raw`.
#[test]
fn trust_interp_from_raw_native_and_production_eq_jit() {
    let bits_menu: [u32; 11] = [0, 1, 7, 8, 16, 32, 64, 127, 128, 129, 200];
    let raws = raw_menu(128); // from_raw itself masks: feed UNMASKED probes
    let expected = bits_menu.len() * 2 * raws.len();
    let raws_w = raws.clone();
    let externs = from_variant_externs();
    let rows =
        run_watchdogged::<(u32, u32, u128, u64, u32, u32, u128)>("from_raw", expected, move |tx| {
            let buffer = jit_module_with(FROM_RAW_IR, "from_raw", &externs_map(&externs));
            // SAFETY: functy.0 = (u32, u32, ptr, ptr, ptr, ptr, ptr) -> ().
            let f: unsafe extern "C" fn(
                u32,
                u32,
                *const u128,
                *mut u64,
                *mut u32,
                *mut u32,
                *mut u128,
            ) = unsafe { std::mem::transmute(bind(&buffer, "interp_from_raw_root")) };
            for &bits in &bits_menu {
                for signed in 0..=1u32 {
                    for &raw in &raws_w {
                        let (mut p, mut ob, mut os, mut orw) =
                            (0xDEADu64, 0xDEADu32, 0xDEADu32, 0xDEADu128);
                        unsafe { f(bits, signed, &raw, &mut p, &mut ob, &mut os, &mut orw) };
                        if tx.send((bits, signed, raw, p, ob, os, orw)).is_err() {
                            return;
                        }
                    }
                }
            }
        });
    for &(bits, signed, raw, p, ob, os, orw) in &rows {
        let native = NInt::from_raw(bits, signed != 0, raw);
        let jit = (p != 0).then_some((ob, os != 0, orw));
        assert_eq!(
            native.map(|v| (v.bits, v.signed, v.raw)),
            jit,
            "from_raw({bits}, {signed}, {raw:#x}) diverged"
        );
        // PRODUCTION cross-check (the real linked trust_ir type).
        let prod = trust_ir::InterpretInt::from_raw(bits, signed != 0, raw);
        assert_eq!(
            prod.map(|v| (v.bits, v.signed, v.raw)),
            jit,
            "from_raw({bits}, {signed}, {raw:#x}): PRODUCTION disagreed with JIT"
        );
    }

    // NEGATIVE CONTROL: an unmasking oracle must disagree on a masked row.
    let witness = rows
        .iter()
        .find(|r| r.0 == 8 && r.2 > 0xFF && r.3 != 0)
        .expect("sweep contains an 8-bit masked row");
    assert_ne!(
        witness.2, witness.6,
        "negative control must FAIL: dropping the mask should disagree with the JIT"
    );
}

/// `InterpretInt::from_i128` — same surface as from_raw for the i128-valued
/// constructor (the [B9] i128_as_u128 reinterpret in its closure).
#[test]
fn trust_interp_from_i128_native_and_production_eq_jit() {
    let bits_menu: [u32; 11] = [0, 1, 7, 8, 16, 32, 64, 127, 128, 129, 200];
    let vals: Vec<i128> = vec![
        0,
        1,
        -1,
        7,
        -7,
        127,
        -128,
        255,
        256,
        -256,
        i64::MAX as i128,
        i64::MIN as i128,
        i128::MAX,
        i128::MIN,
        i128::MIN + 1,
        0x0123_4567_89AB_CDEF_0123_4567_89AB_CDEF,
        -0x0123_4567_89AB_CDEF_0123_4567_89AB_CDEF,
    ];
    let expected = bits_menu.len() * 2 * vals.len();
    let vals_w = vals.clone();
    let externs = from_variant_externs();
    let rows = run_watchdogged::<(u32, u32, i128, u64, u32, u32, u128)>(
        "from_i128",
        expected,
        move |tx| {
            let buffer = jit_module_with(FROM_I128_IR, "from_i128", &externs_map(&externs));
            // SAFETY: functy.0 = (u32, u32, ptr, ptr, ptr, ptr, ptr) -> ().
            let f: unsafe extern "C" fn(
                u32,
                u32,
                *const i128,
                *mut u64,
                *mut u32,
                *mut u32,
                *mut u128,
            ) = unsafe { std::mem::transmute(bind(&buffer, "interp_from_i128_root")) };
            for &bits in &bits_menu {
                for signed in 0..=1u32 {
                    for &value in &vals_w {
                        let (mut p, mut ob, mut os, mut orw) =
                            (0xDEADu64, 0xDEADu32, 0xDEADu32, 0xDEADu128);
                        unsafe { f(bits, signed, &value, &mut p, &mut ob, &mut os, &mut orw) };
                        if tx.send((bits, signed, value, p, ob, os, orw)).is_err() {
                            return;
                        }
                    }
                }
            }
        },
    );
    for &(bits, signed, value, p, ob, os, orw) in &rows {
        let native = NInt::from_i128(bits, signed != 0, value);
        let jit = (p != 0).then_some((ob, os != 0, orw));
        assert_eq!(
            native.map(|v| (v.bits, v.signed, v.raw)),
            jit,
            "from_i128({bits}, {signed}, {value:#x}) diverged"
        );
        let prod = trust_ir::InterpretInt::from_i128(bits, signed != 0, value);
        assert_eq!(
            prod.map(|v| (v.bits, v.signed, v.raw)),
            jit,
            "from_i128({bits}, {signed}, {value:#x}): PRODUCTION disagreed with JIT"
        );
    }

    // NEGATIVE CONTROL: sign-dropping oracle must disagree on a negative row.
    let witness = rows
        .iter()
        .find(|r| r.0 == 128 && r.2 == -1 && r.3 != 0)
        .expect("sweep contains -1 at width 128");
    assert_ne!(
        1u128, witness.6,
        "negative control must FAIL: |value| oracle should disagree with the JIT"
    );
}

/// `InterpretInt::as_signed` — the sign-magnitude decode (the [B9]
/// reinterprets + the two's-complement negation path), against BOTH oracles,
/// over widths 1..=128 including non-power-of-two widths.
#[test]
fn trust_interp_as_signed_native_and_production_eq_jit() {
    let bits_menu: [u32; 9] = [1, 2, 7, 8, 16, 32, 64, 127, 128];
    let mut inputs = Vec::new();
    for &bits in &bits_menu {
        for signed in 0..=1u32 {
            for raw in raw_menu(bits) {
                inputs.push((bits, signed, raw));
            }
        }
    }
    let expected = inputs.len();
    let inputs_w = inputs.clone();
    let rows = run_watchdogged::<(u32, u32, u128, i128)>("as_signed", expected, move |tx| {
        let buffer = jit_module(AS_SIGNED_IR, "as_signed");
        // SAFETY: functy.0 = (u32, u32, ptr, ptr) -> ().
        let f: unsafe extern "C" fn(u32, u32, *const u128, *mut i128) =
            unsafe { std::mem::transmute(bind(&buffer, "interp_as_signed_root")) };
        for &(bits, signed, raw) in &inputs_w {
            let mut out = 0xDEADi128;
            unsafe { f(bits, signed, &raw, &mut out) };
            if tx.send((bits, signed, raw, out)).is_err() {
                return;
            }
        }
    });
    for &(bits, signed, raw, jit) in &rows {
        let native = NInt {
            bits,
            signed: signed != 0,
            raw,
        }
        .as_signed();
        assert_eq!(native, jit, "as_signed({bits}, {raw:#x}) diverged");
        // PRODUCTION cross-check via from_raw (masks are no-ops: menu is
        // pre-masked) then as_signed.
        let prod = trust_ir::InterpretInt::from_raw(bits, signed != 0, raw)
            .expect("valid width")
            .as_signed();
        assert_eq!(
            prod, jit,
            "as_signed({bits}, {raw:#x}): PRODUCTION disagreed with JIT"
        );
    }
    // Ground truths.
    let find = |b: u32, raw: u128| {
        rows.iter()
            .find(|r| r.0 == b && r.2 == raw)
            .map(|r| r.3)
            .unwrap()
    };
    assert_eq!(find(8, 0x80), -128);
    assert_eq!(find(8, 0xFF), -1);
    assert_eq!(find(8, 0x7F), 127);
    assert_eq!(find(1, 1), -1, "1-bit two's complement: 1 is -1");
    assert_eq!(find(128, u128::MAX), -1);
    assert_eq!(find(128, 1u128 << 127), i128::MIN);

    // NEGATIVE CONTROL: a zero-extending (sign-ignoring) oracle must disagree.
    assert_ne!(0x80i128, find(8, 0x80), "negative control must FAIL");
}

/// `signed_div_overflows` — the MIN/-1 predicate over every width (i128s by
/// value through the in-module `(u32, i128, i128) -> (bool)` call ABI).
#[test]
fn trust_interp_sdiv_overflows_native_eq_jit() {
    let vals: Vec<i128> = vec![
        0,
        1,
        -1,
        2,
        -2,
        127,
        -127,
        -128,
        32767,
        -32768,
        i32::MIN as i128,
        i64::MIN as i128,
        i128::MIN,
        i128::MAX,
    ];
    let mut inputs = Vec::new();
    for &bits in &WIDTHS {
        for &l in &vals {
            for &r in &vals {
                inputs.push((bits, l, r));
            }
        }
    }
    let expected = inputs.len();
    let inputs_w = inputs.clone();
    let rows =
        run_watchdogged::<(u32, i128, i128, u32)>("signed_div_overflows", expected, move |tx| {
            let buffer = jit_module(SDIV_OVERFLOWS_IR, "signed_div_overflows");
            // SAFETY: functy.0 = (u32, ptr, ptr) -> (u32).
            let f: unsafe extern "C" fn(u32, *const i128, *const i128) -> u32 =
                unsafe { std::mem::transmute(bind(&buffer, "interp_sdiv_overflows_root")) };
            for &(bits, l, r) in &inputs_w {
                let out = unsafe { f(bits, &l, &r) };
                if tx.send((bits, l, r, out)).is_err() {
                    return;
                }
            }
        });
    for &(bits, l, r, jit) in &rows {
        assert_eq!(
            n_signed_div_overflows(bits, l, r),
            jit != 0,
            "signed_div_overflows({bits}, {l}, {r}) diverged"
        );
    }
    let find = |b: u32, l: i128, r: i128| {
        rows.iter()
            .find(|x| x.0 == b && x.1 == l && x.2 == r)
            .map(|x| x.3 != 0)
            .unwrap()
    };
    assert!(find(8, -128, -1), "i8::MIN / -1 must be flagged");
    assert!(find(128, i128::MIN, -1));
    assert!(!find(8, -127, -1));
    assert!(!find(64, i128::MIN, -1), "i128::MIN is not i64::MIN");

    // NEGATIVE CONTROL: inverted predicate must disagree.
    assert_ne!(
        !n_signed_div_overflows(8, -128, -1),
        find(8, -128, -1),
        "negative control must FAIL"
    );
}

/// `shift_amount` — the UB gate for every shift; error identity checked
/// (ShiftOutOfRange fires exactly when `rhs.raw >= bits`).
#[test]
fn trust_interp_shift_amount_native_eq_jit() {
    let bits_menu: [u32; 8] = [0, 1, 7, 8, 32, 64, 127, 128];
    let mut inputs = Vec::new();
    for &rbits in &[8u32, 64, 128] {
        for &bits in &bits_menu {
            for raw in raw_menu(rbits) {
                inputs.push((rbits, raw, bits));
            }
        }
    }
    let expected = inputs.len();
    let inputs_w = inputs.clone();
    let rows =
        run_watchdogged::<(u32, u128, u32, u64, u32, u64)>("shift_amount", expected, move |tx| {
            let buffer = jit_module(SHIFT_AMOUNT_IR, "shift_amount");
            // SAFETY: functy.0 = (u32, u32, ptr, u32, ptr, ptr, ptr) -> ().
            let f: unsafe extern "C" fn(u32, u32, *const u128, u32, *mut u64, *mut u32, *mut u64) =
                unsafe { std::mem::transmute(bind(&buffer, "interp_shift_amount_root")) };
            for &(rbits, raw, bits) in &inputs_w {
                let (mut tag, mut amount, mut err) = (0xDEADu64, 0xDEADu32, 0xDEADu64);
                unsafe { f(rbits, 0, &raw, bits, &mut tag, &mut amount, &mut err) };
                if tx.send((rbits, raw, bits, tag, amount, err)).is_err() {
                    return;
                }
            }
        });
    for &(rbits, raw, bits, tag, amount, err) in &rows {
        let native = n_shift_amount(
            NInt {
                bits: rbits,
                signed: false,
                raw,
            },
            bits,
        );
        match native {
            Ok(a) => assert_eq!(
                (1u64, a, 0u64),
                (tag, amount, err),
                "shift_amount(rbits={rbits}, raw={raw:#x}, bits={bits}) diverged"
            ),
            Err(e) => assert_eq!(
                (0u64, 0u32, n_err_code(e)),
                (tag, amount, err),
                "shift_amount error identity diverged"
            ),
        }
    }
    let find = |raw: u128, bits: u32| {
        rows.iter()
            .find(|r| r.0 == 128 && r.1 == raw && r.2 == bits)
            .map(|r| (r.3, r.4, r.5))
            .unwrap()
    };
    assert_eq!(find(63, 64), (1, 63, 0));
    assert_eq!(
        find(64, 64),
        (0, 0, 9),
        "amount == bits is the exact boundary"
    );
    assert_eq!(find(127, 128), (1, 127, 0));
    assert_eq!(find(0, 0), (0, 0, 9), "bits == 0 rejects every amount");

    // NEGATIVE CONTROL: an off-by-one gate (`>` instead of `>=`) must
    // disagree at the boundary row.
    let boundary = find(64, 64);
    assert_ne!((1u64, 64u32, 0u64), boundary, "negative control must FAIL");
}

/// `eval_int_icmp` — all 10 predicates over widths and MIXED signedness
/// (production compares by decoded value, so the sign decode is on the line).
#[test]
fn trust_interp_icmp_full_sweep_native_eq_jit() {
    let widths: [u32; 4] = [8, 16, 64, 128];
    let mut inputs = Vec::new();
    for op in 0..10u32 {
        for &bits in &widths {
            for ls in 0..=1u32 {
                for rs in 0..=1u32 {
                    for &lr in &pair_menu(bits) {
                        for &rr in &pair_menu(bits) {
                            inputs.push((op, bits, ls, rs, lr, rr));
                        }
                    }
                }
            }
        }
    }
    let expected = inputs.len();
    let inputs_w = inputs.clone();
    let rows = run_watchdogged::<((u32, u32, u32, u32, u128, u128), u32)>(
        "eval_int_icmp",
        expected,
        move |tx| {
            let buffer = jit_module(ICMP_IR, "eval_int_icmp");
            // SAFETY: functy.0 = (u32, u32, u32, ptr, u32, u32, ptr) -> (u32).
            let f: unsafe extern "C" fn(u32, u32, u32, *const u128, u32, u32, *const u128) -> u32 =
                unsafe { std::mem::transmute(bind(&buffer, "interp_icmp_root")) };
            for &(op, bits, ls, rs, lr, rr) in &inputs_w {
                let out = unsafe { f(op, bits, ls, &lr, bits, rs, &rr) };
                if tx.send(((op, bits, ls, rs, lr, rr), out)).is_err() {
                    return;
                }
            }
        },
    );
    for &((op, bits, ls, rs, lr, rr), jit) in &rows {
        let native = n_eval_int_icmp(
            n_icmp_from_tag(op),
            NInt {
                bits,
                signed: ls != 0,
                raw: lr,
            },
            NInt {
                bits,
                signed: rs != 0,
                raw: rr,
            },
        );
        assert_eq!(
            native,
            jit != 0,
            "icmp op={op} bits={bits} ls={ls} rs={rs} {lr:#x} vs {rr:#x} diverged"
        );
    }
    // Ground truth: the sign-bit witness where Slt and Ult MUST differ.
    let find = |op: u32, bits: u32, lr: u128, rr: u128| {
        rows.iter()
            .find(|r| {
                r.0.0 == op
                    && r.0.1 == bits
                    && r.0.2 == 1
                    && r.0.3 == 1
                    && r.0.4 == lr
                    && r.0.5 == rr
            })
            .map(|r| r.1 != 0)
            .unwrap()
    };
    assert!(find(6, 8, 0x80, 0), "Slt: -128 < 0");
    assert!(!find(2, 8, 0x80, 0), "Ult: 0x80 is not < 0");

    // NEGATIVE CONTROL: an oracle that confuses Slt with Ult must disagree
    // exactly at that witness.
    assert_ne!(
        find(2, 8, 0x80, 0),
        find(6, 8, 0x80, 0),
        "negative control must FAIL: the sweep must discriminate signed vs unsigned compare"
    );
}

/// `eval_int_unop` — Neg/Not/CtPop + the six float rejections; the CtPop
/// popcount loop [B5] checked against the native `count_ones` for every row.
#[test]
fn trust_interp_unop_full_sweep_native_eq_jit() {
    let mut inputs = Vec::new();
    for op in 0..9u32 {
        for &bits in &WIDTHS {
            for signed in 0..=1u32 {
                for raw in raw_menu(bits) {
                    inputs.push((op, bits, signed, raw));
                }
            }
        }
    }
    let expected = inputs.len();
    let inputs_w = inputs.clone();
    let rows =
        run_watchdogged::<((u32, u32, u32, u128), EvRow)>("eval_int_unop", expected, move |tx| {
            let buffer = jit_module(UNOP_IR, "eval_int_unop");
            // SAFETY: functy.0 = (u32, u32, u32, ptr, ptr) -> ().
            let f: unsafe extern "C" fn(u32, u32, u32, *const u128, *mut EvalOutC) =
                unsafe { std::mem::transmute(bind(&buffer, "interp_unop_root")) };
            for &(op, bits, signed, raw) in &inputs_w {
                let mut out = EvalOutC::poisoned();
                unsafe { f(op, bits, signed, &raw, &mut out) };
                if tx.send(((op, bits, signed, raw), ev_of(&out))).is_err() {
                    return;
                }
            }
        });
    for &((op, bits, signed, raw), jit) in &rows {
        let native = n_eval_int_unop(
            n_unop_from_tag(op),
            NInt {
                bits,
                signed: signed != 0,
                raw,
            },
        );
        assert_eq!(
            ev_expect(native),
            jit,
            "unop op={op} bits={bits} raw={raw:#x} diverged"
        );
    }
    let find = |op: u32, bits: u32, raw: u128| {
        rows.iter()
            .find(|r| r.0.0 == op && r.0.1 == bits && r.0.2 == 0 && r.0.3 == raw)
            .map(|r| r.1)
            .unwrap()
    };
    assert_eq!(find(0, 8, 1).4, 0xFF, "Neg(1) @8 = 0xFF");
    assert_eq!(find(7, 8, 0).4, 0xFF, "Not(0) @8 = 0xFF");
    assert_eq!(find(8, 8, 0xFF).4, 8, "CtPop(0xFF) = 8");
    assert_eq!(find(8, 128, u128::MAX).4, 128, "CtPop(u128::MAX) = 128");
    assert_eq!(
        find(1, 64, 7),
        (0, 11, 0, 0, 0),
        "FNeg rejects: FloatUnopUnsupported"
    );

    // NEGATIVE CONTROL: a count_zeros oracle must disagree with CtPop rows.
    let ctpop_ff = find(8, 8, 0xFF).4;
    assert_ne!(
        u128::from(0xFFu8.count_zeros()),
        ctpop_ff,
        "negative control must FAIL"
    );
}

/// `eval_int_binop` — THE CENTERPIECE: all 20 arms x widths x signedness
/// combinations x value pairs, plus width-mismatch rows; every result AND
/// every error identity native == JIT, and a PRODUCTION-interpreter
/// cross-check on the well-typed subset (transitively production == JIT).
#[test]
fn trust_interp_binop_full_sweep_native_eq_jit() {
    let mut inputs = Vec::new();
    for op in 0..20u32 {
        for &bits in &WIDTHS {
            for ls in 0..=1u32 {
                for rs in 0..=1u32 {
                    for &lr in &pair_menu(bits) {
                        for &rr in &pair_menu(bits) {
                            inputs.push((op, bits, ls, bits, rs, lr, rr));
                        }
                    }
                }
            }
        }
        // width-mismatch rows (the TypeError path).
        for &(lb, rb) in &[(8u32, 16u32), (64, 128), (128, 8)] {
            inputs.push((op, lb, 1, rb, 1, 1, 1));
        }
    }
    let expected = inputs.len();
    let inputs_w = inputs.clone();
    let rows = run_watchdogged::<((u32, u32, u32, u32, u32, u128, u128), EvRow)>(
        "eval_int_binop",
        expected,
        move |tx| {
            let buffer = jit_module(BINOP_IR, "eval_int_binop");
            // SAFETY: functy.0 = (u32, u32, u32, ptr, u32, u32, ptr, ptr) -> ().
            let f: unsafe extern "C" fn(
                u32,
                u32,
                u32,
                *const u128,
                u32,
                u32,
                *const u128,
                *mut EvalOutC,
            ) = unsafe { std::mem::transmute(bind(&buffer, "interp_binop_root")) };
            for &(op, lb, ls, rb, rs, lr, rr) in &inputs_w {
                let mut out = EvalOutC::poisoned();
                unsafe { f(op, lb, ls, &lr, rb, rs, &rr, &mut out) };
                if tx
                    .send(((op, lb, ls, rb, rs, lr, rr), ev_of(&out)))
                    .is_err()
                {
                    return;
                }
            }
        },
    );
    for &((op, lb, ls, rb, rs, lr, rr), jit) in &rows {
        let native = n_eval_int_binop(
            n_binop_from_tag(op),
            NInt {
                bits: lb,
                signed: ls != 0,
                raw: lr,
            },
            NInt {
                bits: rb,
                signed: rs != 0,
                raw: rr,
            },
        );
        assert_eq!(
            ev_expect(native),
            jit,
            "binop op={op} lb={lb} ls={ls} rb={rb} rs={rs} {lr:#x}, {rr:#x} diverged"
        );
    }

    // Ground-truth spot checks (independent literals).
    let find = |op: u32, bits: u32, ls: u32, lr: u128, rr: u128| {
        rows.iter()
            .find(|r| r.0 == (op, bits, ls, bits, ls, lr, rr))
            .map(|r| r.1)
            .unwrap()
    };
    assert_eq!(find(0, 8, 0, 0xFF, 1).4, 0, "u8 0xFF + 1 wraps to 0");
    assert_eq!(
        find(4, 8, 1, 0x80, 0xFF),
        (0, 6, 0, 0, 0),
        "i8 MIN / -1 = SDivOverflow"
    );
    assert_eq!(
        find(3, 8, 0, 7, 0),
        (0, 3, 0, 0, 0),
        "u8 7 / 0 = UDivByZero"
    );
    assert_eq!(
        find(6, 8, 1, 0xFF, 2).4,
        0xFF,
        "i8 -1 % 2 = -1 (0xFF masked)"
    );
    assert_eq!(find(17, 8, 0, 1, 7).4, 0x80, "u8 1 << 7 = 0x80");
    assert_eq!(
        find(17, 8, 0, 1, 64),
        (0, 9, 0, 0, 0),
        "shift amount >= bits rejected"
    );
    assert_eq!(
        find(19, 8, 1, 0x80, 1).4,
        0xC0,
        "i8 AShr propagates the sign bit"
    );
    assert_eq!(find(7, 8, 0, 1, 1), (0, 10, 0, 0, 0), "FAdd rejects");
    assert_eq!(
        find(3, 128, 0, u128::MAX, 3).4,
        u128::MAX / 3,
        "full-width u128 division"
    );

    // PRODUCTION cross-check: run the well-typed sampled subset through the
    // REAL trust_ir::Interpreter (routes into the production eval_int_binop).
    // Transitivity: interpreter == transcription == JIT on these rows.
    let int_ops: [(u32, &str); 13] = [
        (0, "add"),
        (1, "sub"),
        (2, "mul"),
        (3, "udiv"),
        (4, "sdiv"),
        (5, "urem"),
        (6, "srem"),
        (14, "and"),
        (15, "or"),
        (16, "xor"),
        (17, "shl"),
        (18, "lshr"),
        (19, "ashr"),
    ];
    let tys: [(u32, u32, &str, trust_ir::Ty); 6] = [
        (8, 1, "i8", trust_ir::Ty::I8),
        (8, 0, "u8", trust_ir::Ty::U8),
        (64, 1, "i64", trust_ir::Ty::I64),
        (64, 0, "u64", trust_ir::Ty::U64),
        (128, 1, "i128", trust_ir::Ty::I128),
        (128, 0, "u128", trust_ir::Ty::U128),
    ];
    let mut prod_checked = 0usize;
    for &(op_tag, op_txt) in &int_ops {
        for (bits, signed, ty_txt, ty) in &tys {
            let sample: Vec<u128> = pair_menu(*bits).into_iter().take(6).collect();
            for &lr in &sample {
                for &rr in &sample {
                    let native = n_eval_int_binop(
                        n_binop_from_tag(op_tag),
                        NInt {
                            bits: *bits,
                            signed: *signed != 0,
                            raw: lr,
                        },
                        NInt {
                            bits: *bits,
                            signed: *signed != 0,
                            raw: rr,
                        },
                    );
                    match prod_interp_binop(op_txt, ty_txt, ty.clone(), lr, rr) {
                        Ok((pb, ps, pr)) => {
                            let n = native.unwrap_or_else(|e| {
                                panic!("production Ok but transcription Err({e:?}) at {op_txt} {ty_txt} {lr:#x},{rr:#x}")
                            });
                            assert_eq!(
                                (n.bits, n.signed, n.raw),
                                (pb, ps, pr),
                                "PRODUCTION interpreter disagreed at {op_txt} {ty_txt} {lr:#x},{rr:#x}"
                            );
                        }
                        Err(code) => {
                            let e = match native {
                                Err(e) => e,
                                Ok(v) => panic!(
                                    "production Err({code:?}) but transcription Ok({v:?}) at {op_txt} {ty_txt} {lr:#x},{rr:#x}"
                                ),
                            };
                            assert_eq!(
                                code,
                                trust_ir::InterpretErrorCode::UndefinedBehavior,
                                "production error code class at {op_txt} {ty_txt} {lr:#x},{rr:#x} (transcription: {e:?})"
                            );
                        }
                    }
                    prod_checked += 1;
                }
            }
        }
    }
    assert!(
        prod_checked >= 2500,
        "production cross-check must actually run ({prod_checked})"
    );

    // NEGATIVE CONTROL: a mask-dropping oracle must disagree on the wrap row.
    let wrap = find(0, 8, 0, 0xFF, 1);
    assert_ne!(
        (1u64, 0u64, 8u32, 0u32, 256u128),
        wrap,
        "negative control must FAIL"
    );
}

/// `eval_int_overflow` — add/sub/mul with the overflow FLAG, signed
/// (production `checked_*` host-shim boundary [B7]) and unsigned
/// (the [B4]-rewritten `overflowing_*`), against the verbatim-form oracle.
#[test]
fn trust_interp_overflow_full_sweep_native_eq_jit() {
    let mut inputs = Vec::new();
    for op in 0..3u32 {
        for &bits in &WIDTHS {
            for ls in 0..=1u32 {
                for rs in 0..=1u32 {
                    for &lr in &pair_menu(bits) {
                        for &rr in &pair_menu(bits) {
                            inputs.push((op, bits, ls, bits, rs, lr, rr));
                        }
                    }
                }
            }
        }
        for &(lb, rb) in &[(8u32, 16u32), (64, 128), (128, 8)] {
            inputs.push((op, lb, 1, rb, 1, 1, 1));
        }
    }
    let expected = inputs.len();
    let inputs_w = inputs.clone();
    let externs = checked_externs();
    let rows = run_watchdogged::<((u32, u32, u32, u32, u32, u128, u128), EvRow, u32)>(
        "eval_int_overflow",
        expected,
        move |tx| {
            let buffer = jit_module_with(OVERFLOW_IR, "eval_int_overflow", &externs_map(&externs));
            // SAFETY: functy.0 = (u32, u32, u32, ptr, u32, u32, ptr, ptr, ptr) -> ().
            let f: unsafe extern "C" fn(
                u32,
                u32,
                u32,
                *const u128,
                u32,
                u32,
                *const u128,
                *mut EvalOutC,
                *mut u32,
            ) = unsafe { std::mem::transmute(bind(&buffer, "interp_overflow_root")) };
            for &(op, lb, ls, rb, rs, lr, rr) in &inputs_w {
                let mut out = EvalOutC::poisoned();
                let mut flag = 0xDEADu32;
                unsafe { f(op, lb, ls, &lr, rb, rs, &rr, &mut out, &mut flag) };
                if tx
                    .send(((op, lb, ls, rb, rs, lr, rr), ev_of(&out), flag))
                    .is_err()
                {
                    return;
                }
            }
        },
    );
    for &((op, lb, ls, rb, rs, lr, rr), jit, flag) in &rows {
        let native = n_eval_int_overflow(
            n_ovop_from_tag(op),
            NInt {
                bits: lb,
                signed: ls != 0,
                raw: lr,
            },
            NInt {
                bits: rb,
                signed: rs != 0,
                raw: rr,
            },
        );
        match native {
            Ok((v, nf)) => {
                assert_eq!(
                    (1u64, 0u64, v.bits, v.signed as u32, v.raw),
                    jit,
                    "overflow op={op} bits={lb} ls={ls} rs={rs} {lr:#x},{rr:#x} result diverged"
                );
                assert_eq!(
                    nf as u32, flag,
                    "overflow FLAG diverged at op={op} bits={lb} ls={ls} {lr:#x},{rr:#x}"
                );
            }
            Err(e) => {
                assert_eq!(
                    (0u64, n_err_code(e), 0, 0, 0),
                    jit,
                    "overflow error identity diverged"
                );
                assert_eq!(0xFFu32, flag, "error rows carry the 0xFF flag sentinel");
            }
        }
    }
    let find = |op: u32, bits: u32, ls: u32, lr: u128, rr: u128| {
        rows.iter()
            .find(|r| r.0 == (op, bits, ls, bits, ls, lr, rr))
            .map(|r| (r.1, r.2))
            .unwrap()
    };
    let (row, flag) = find(0, 8, 0, 0xFF, 0xFF); // u8 255 + 255
    assert_eq!((row.4, flag), (0xFE, 1), "u8 255+255 = (254, overflow)");
    let (row, flag) = find(2, 128, 0, u128::MAX, 2);
    assert_eq!(
        (row.4, flag),
        (u128::MAX << 1, 1),
        "u128 MAX*2 wraps with flag"
    );
    let (row, flag) = find(2, 128, 1, 1u128 << 127, u128::MAX); // i128 MIN * -1
    assert_eq!(
        (row.4, flag),
        (1u128 << 127, 1),
        "i128 MIN * -1 = (MIN, overflow)"
    );
    let (row, flag) = find(1, 8, 0, 0, 1); // u8 0 - 1
    assert_eq!((row.4, flag), (0xFF, 1), "u8 0-1 wraps with flag");

    // NEGATIVE CONTROL: an inverted-flag oracle must disagree on the wrap row.
    let (_, jit_flag) = find(0, 8, 0, 0xFF, 0xFF);
    let native_inverted = !n_eval_int_overflow(
        NOvOp::Add,
        NInt {
            bits: 8,
            signed: false,
            raw: 0xFF,
        },
        NInt {
            bits: 8,
            signed: false,
            raw: 0xFF,
        },
    )
    .unwrap()
    .1;
    assert_ne!(
        native_inverted as u32, jit_flag,
        "negative control must FAIL"
    );
}

// ═══════════════════════════════════════════════════════════════════════════
// PROMOTED: the 128-bit int<->int bitcast now lowers
// ═══════════════════════════════════════════════════════════════════════════

/// PROMOTED CAPABILITY (was round 4's pinned ISel limit): trust-cg lowers the
/// 128-bit int<->int BITCAST. This module is the MIR emit of production-shaped
/// Rust (`*out = *x as i128` — exactly how interpret.rs spells its sign
/// reinterprets): one load, one bitcast, one store. trust-cg used to fail it
/// `Pipeline(ISel("value ... not defined before use"))`; it now lowers and
/// runs it correctly. This test compiles the module (a compile Err is a hard
/// REGRESSION) and runs the full identity differential (hang-guarded),
/// asserting the JIT reproduces the native `x as i128` reinterpret bit-exactly
/// on every swept 128-bit input.
#[test]
fn trust_cg_lowers_int128_bitcast_native_eq_jit() {
    let module = trust_ir::parser::parse_module(BITCAST_PIN_IR)
        .expect("MIR-emitted `interp_bitcast_pin_root` trust-ir must parse (frontend is fine)");
    let config = CompilerConfig::jit_fast(Target::Aarch64);
    if let Err(e) = Compiler::new(config).compile_module_to_jit(&module, &HashMap::new()) {
        panic!(
            "REGRESSION: trust-cg can no longer lower the 128-bit int<->int bitcast \
             (`*out = *x as i128`) that it previously compiled: {e:?}"
        );
    }
    // Full identity differential (hang-guarded): the JIT reinterpret must be
    // bit-exact against the native `x as i128` on every swept 128-bit input.
    let rows = run_watchdogged::<(u128, i128)>("int128 bitcast", raw_menu(128).len(), move |tx| {
        let buffer = jit_module(BITCAST_PIN_IR, "int128 bitcast");
        // SAFETY: functy.0 = (ptr, ptr) -> ().
        let f: unsafe extern "C" fn(*const u128, *mut i128) =
            unsafe { std::mem::transmute(bind(&buffer, "interp_bitcast_pin_root")) };
        for &x in &raw_menu(128) {
            let mut out = 0xDEADi128;
            unsafe { f(&x, &mut out) };
            if tx.send((x, out)).is_err() {
                return;
            }
        }
    });
    for &(x, out) in &rows {
        assert_eq!(
            x as i128, out,
            "bitcast identity must be bit-exact at {x:#x}"
        );
    }
}
