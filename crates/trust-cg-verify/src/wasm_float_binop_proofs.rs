// trust-cg-verify/wasm_float_binop_proofs.rs - FMin / FMax / FCopySign bodies from the emitted bytes
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Reference: WebAssembly Core Specification, Release 2.0 — §4.3.3 (Floating-
//            Point Operations: fmin, fmax, fcopysign, feq, fne, fabs, fneg,
//            and the NaN set nans_N), §4.4 (the instructions local.get /
//            local.set / local.tee / select / return), §5.4 (their encodings).
//
// WHY A WHOLE BODY. wasm's `f.min` / `f.max` propagate NaN; trust-ir `FMin` /
// `FMax` return the non-NaN operand. The lowering therefore never emits the
// opcode alone: it emits `isnan(a) ? b : (isnan(b) ? a : f.min(a, b))` as
// eleven instructions around it (two `f.ne` self-comparisons and two
// `select`s). A per-opcode reconstruction of `f.min` would compare the wrong
// thing — it would REFUTE against trust-ir, correctly, because the opcode is
// not the lowering. The unit of evidence is the emitted SEQUENCE, so this
// module runs the REAL emitted function body.
//
// THE TWO SIDES.
//
//   * MACHINE: [`run_float_binop_body`] decodes the captured code entry byte by
//     byte and executes it on concrete bit patterns under the spec's
//     definitions of each instruction, transcribed case by case. `f.min` /
//     `f.max` on a NaN operand return an element of the spec's NaN set, which
//     the spec leaves nondeterministic: every body is run once per
//     [`NanChoice`], both canonical NaNs and two arithmetic NaNs, and must hold
//     for all of them.
//   * SOURCE: [`trust_ir_float_binop_allows`] states the trust-ir contract as a
//     RELATION on (a, b, result), because the contract is not a function: two
//     NaN operands give "a NaN", and a `-0.0` / `+0.0` pair gives either
//     operand (trust-ir's numerics policy: which zero a min/max returns is not
//     pinned; Rust's `f32::min` says the same). A lone NaN gives the other
//     operand bit-exactly; an ordered pair gives the lesser (greater). The
//     reference interpreter runs the host's `f32::min`, which picks one member
//     of that relation.
//
// FCopySign is emitted as a single instruction, and the per-opcode
// reconstruction in `wasm_function_verifier` already states it; its bodies are
// here too because only the emitted body shows the operand ORDER (magnitude
// first, sign second) the representative reconstruction assumes.
//
// WHAT THIS DOES NOT ESTABLISH. It is decided on a finite battery of bit
// patterns (every pair of 18 per width, zeros, infinities, extremes,
// subnormals, quiet and signalling NaNs of both signs, with payloads), not
// over all 2^64 / 2^128 inputs — the obligations are piecewise over exactly
// these classes, and each class is present, but it is a battery. It runs the
// body of a `(a, b) -> fop(a, b)` function; the same instruction sequence
// inside a larger function is the same bytes around different local indices,
// which the value-domain differential exercises, not this. And it credits the
// reading of the ±0 tie as unpinned: under a reading that pins it to the
// second operand (the x86 MINSS convention the `FMin` doc comment mentions),
// the body REFUTES at `min(-0.0, +0.0)`, and a negative control asserts that.

//! Execution of the captured FMin / FMax / FCopySign function bodies against a
//! relational statement of the trust-ir contract, with negative controls.

use std::collections::BTreeSet;
use std::fmt;

use crate::wasm_encoding_proofs::spec_decode_unsigned;

/// The trust-ir float binary op a captured body lowers.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum FloatBinopKind {
    /// `BinOp::FMin`.
    Min,
    /// `BinOp::FMax`.
    Max,
    /// `BinOp::FCopySign`.
    CopySign,
}

/// One captured body: `(op, width in bits, the code ENTRY — locals vector and
/// expression — of a `(a: fN, b: fN) -> fN { ret op(a, b) }` function)`.
pub type EmittedFloatBinopBody = (FloatBinopKind, u32, &'static [u8]);

/// The code entries the real wasm backend emits for the six
/// `(a, b) -> op(a, b)` functions, captured from the module's code section
/// at the default level, where the emission pass's control cleanup has
/// deleted the final `return` (and the `unreachable` after it): the result
/// falls off the end.
///
/// Like the other captured corpora in this crate it exists because the credit
/// hook cannot compile, and it cannot rot: `tests/support/wasm_float_live_emit.rs`
/// recompiles all six through the live backend and requires byte identity, from
/// `wasm_encoding_gate` and from the ratio-pinning `coverage_gate_tests`.
pub const EMITTED_FLOAT_BINOP_BODIES: &[EmittedFloatBinopBody] = &[
    (
        FloatBinopKind::Min,
        32,
        &[
            0x00, 0x20, 0x01, 0x20, 0x00, 0x20, 0x00, 0x20, 0x01, 0x96, 0x20, 0x01, 0x20, 0x01,
            0x5c, 0x1b, 0x20, 0x00, 0x20, 0x00, 0x5c, 0x1b, 0x0b,
        ],
    ),
    (
        FloatBinopKind::Max,
        32,
        &[
            0x00, 0x20, 0x01, 0x20, 0x00, 0x20, 0x00, 0x20, 0x01, 0x97, 0x20, 0x01, 0x20, 0x01,
            0x5c, 0x1b, 0x20, 0x00, 0x20, 0x00, 0x5c, 0x1b, 0x0b,
        ],
    ),
    (
        FloatBinopKind::CopySign,
        32,
        &[0x00, 0x20, 0x00, 0x20, 0x01, 0x98, 0x0b],
    ),
    (
        FloatBinopKind::Min,
        64,
        &[
            0x00, 0x20, 0x01, 0x20, 0x00, 0x20, 0x00, 0x20, 0x01, 0xa4, 0x20, 0x01, 0x20, 0x01,
            0x62, 0x1b, 0x20, 0x00, 0x20, 0x00, 0x62, 0x1b, 0x0b,
        ],
    ),
    (
        FloatBinopKind::Max,
        64,
        &[
            0x00, 0x20, 0x01, 0x20, 0x00, 0x20, 0x00, 0x20, 0x01, 0xa5, 0x20, 0x01, 0x20, 0x01,
            0x62, 0x1b, 0x20, 0x00, 0x20, 0x00, 0x62, 0x1b, 0x0b,
        ],
    ),
    (
        FloatBinopKind::CopySign,
        64,
        &[0x00, 0x20, 0x00, 0x20, 0x01, 0xa6, 0x0b],
    ),
];

/// The `(op, width)` whose coverage row an opcode byte is: `f32.min` 0x96,
/// `f32.max` 0x97, `f32.copysign` 0x98, `f64.min` 0xa4, `f64.max` 0xa5,
/// `f64.copysign` 0xa6. `None` for every other byte.
pub fn float_binop_row(byte: u8) -> Option<(FloatBinopKind, u32)> {
    Some(match byte {
        0x96 => (FloatBinopKind::Min, 32),
        0x97 => (FloatBinopKind::Max, 32),
        0x98 => (FloatBinopKind::CopySign, 32),
        0xa4 => (FloatBinopKind::Min, 64),
        0xa5 => (FloatBinopKind::Max, 64),
        0xa6 => (FloatBinopKind::CopySign, 64),
        _ => return None,
    })
}

// ===========================================================================
// Bit-pattern helpers
// ===========================================================================

fn sign_bit(width: u32) -> u64 {
    1u64 << (width - 1)
}

fn exp_mask(width: u32) -> u64 {
    if width == 32 {
        0x7f80_0000
    } else {
        0x7ff0_0000_0000_0000
    }
}

fn frac_mask(width: u32) -> u64 {
    if width == 32 {
        0x007f_ffff
    } else {
        0x000f_ffff_ffff_ffff
    }
}

fn quiet_bit(width: u32) -> u64 {
    if width == 32 { 1 << 22 } else { 1 << 51 }
}

fn is_nan(z: u64, width: u32) -> bool {
    z & exp_mask(width) == exp_mask(width) && z & frac_mask(width) != 0
}

fn is_zero(z: u64, width: u32) -> bool {
    z & !sign_bit(width) == 0
}

fn is_negative(z: u64, width: u32) -> bool {
    z & sign_bit(width) != 0
}

fn pos_inf(width: u32) -> u64 {
    exp_mask(width)
}

fn neg_inf(width: u32) -> u64 {
    exp_mask(width) | sign_bit(width)
}

/// The real number a non-NaN pattern denotes (exact: every binary32 value is a
/// binary64 value). Used only for ordering, never for a result.
fn numeric(z: u64, width: u32) -> f64 {
    if width == 32 {
        f64::from(f32::from_bits(z as u32))
    } else {
        f64::from_bits(z)
    }
}

// ===========================================================================
// MACHINE side: the spec's instruction semantics on bit patterns
// ===========================================================================

/// One representative of the spec's NaN result set `nans_N{z1, z2}`, which
/// `f.min` / `f.max` return when an operand is a NaN. The spec leaves the
/// choice open (a canonical NaN of either sign, or — when an operand is not
/// canonical — any arithmetic NaN), so a body must hold under every choice.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum NanChoice {
    /// `+nan(canon_N)`.
    CanonicalPositive,
    /// `-nan(canon_N)`.
    CanonicalNegative,
    /// `+nan(n)` with every payload bit set.
    ArithmeticPositive,
    /// `-nan(n)` with every payload bit set.
    ArithmeticNegative,
}

impl NanChoice {
    /// Every choice.
    pub const ALL: [NanChoice; 4] = [
        NanChoice::CanonicalPositive,
        NanChoice::CanonicalNegative,
        NanChoice::ArithmeticPositive,
        NanChoice::ArithmeticNegative,
    ];

    /// The NaN pattern this choice denotes at `width`.
    pub fn pattern(self, width: u32) -> u64 {
        let canonical = exp_mask(width) | quiet_bit(width);
        let arithmetic = exp_mask(width) | frac_mask(width);
        match self {
            NanChoice::CanonicalPositive => canonical,
            NanChoice::CanonicalNegative => canonical | sign_bit(width),
            NanChoice::ArithmeticPositive => arithmetic,
            NanChoice::ArithmeticNegative => arithmetic | sign_bit(width),
        }
    }
}

/// Spec `fmin_N(z1, z2)`, case by case.
fn spec_fmin(z1: u64, z2: u64, width: u32, nan: NanChoice) -> u64 {
    if is_nan(z1, width) || is_nan(z2, width) {
        nan.pattern(width)
    } else if z1 == neg_inf(width) || z2 == neg_inf(width) {
        neg_inf(width)
    } else if z1 == pos_inf(width) {
        z2
    } else if z2 == pos_inf(width) {
        z1
    } else if is_zero(z1, width) && is_zero(z2, width) && z1 != z2 {
        sign_bit(width)
    } else if numeric(z1, width) <= numeric(z2, width) {
        z1
    } else {
        z2
    }
}

/// Spec `fmax_N(z1, z2)`, case by case.
fn spec_fmax(z1: u64, z2: u64, width: u32, nan: NanChoice) -> u64 {
    if is_nan(z1, width) || is_nan(z2, width) {
        nan.pattern(width)
    } else if z1 == pos_inf(width) || z2 == pos_inf(width) {
        pos_inf(width)
    } else if z1 == neg_inf(width) {
        z2
    } else if z2 == neg_inf(width) {
        z1
    } else if is_zero(z1, width) && is_zero(z2, width) && z1 != z2 {
        0
    } else if numeric(z1, width) >= numeric(z2, width) {
        z1
    } else {
        z2
    }
}

/// Spec `fcopysign_N(z1, z2)`: `z1` if the signs agree, else `z1` negated.
fn spec_fcopysign(z1: u64, z2: u64, width: u32) -> u64 {
    if is_negative(z1, width) == is_negative(z2, width) {
        z1
    } else {
        z1 ^ sign_bit(width)
    }
}

/// Spec `feq_N(z1, z2)` as the `i32` it pushes.
fn spec_feq(z1: u64, z2: u64, width: u32) -> u64 {
    if is_nan(z1, width) || is_nan(z2, width) {
        0
    } else if (is_zero(z1, width) && is_zero(z2, width)) || z1 == z2 {
        1
    } else {
        0
    }
}

/// Spec `fne_N(z1, z2)` as the `i32` it pushes.
fn spec_fne(z1: u64, z2: u64, width: u32) -> u64 {
    if is_nan(z1, width) || is_nan(z2, width) {
        1
    } else if (is_zero(z1, width) && is_zero(z2, width)) || z1 == z2 {
        0
    } else {
        1
    }
}

/// A value type the body evaluator admits.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Ty {
    I32,
    F32,
    F64,
}

impl Ty {
    fn of_float_width(width: u32) -> Option<Ty> {
        match width {
            32 => Some(Ty::F32),
            64 => Some(Ty::F64),
            _ => None,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Val {
    ty: Ty,
    bits: u64,
}

/// Why a body could not be executed. Every variant is a refusal to credit,
/// never a best-effort result.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BodyRefusal {
    /// The bytes do not decode as the admitted instruction surface.
    Decode {
        /// Byte offset in the entry.
        offset: usize,
        /// What was wrong.
        what: String,
    },
    /// An instruction found the wrong operand types or too few operands.
    Stack {
        /// Byte offset in the entry.
        offset: usize,
        /// What was wrong.
        what: String,
    },
    /// Execution reached `unreachable`.
    Trap {
        /// Byte offset in the entry.
        offset: usize,
    },
}

impl fmt::Display for BodyRefusal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            BodyRefusal::Decode { offset, what } => write!(f, "decode at +{offset}: {what}"),
            BodyRefusal::Stack { offset, what } => write!(f, "stack at +{offset}: {what}"),
            BodyRefusal::Trap { offset } => write!(f, "execution TRAPS at +{offset}"),
        }
    }
}

fn read_index(entry: &[u8], at: &mut usize) -> Result<u32, BodyRefusal> {
    let (v, used) = spec_decode_unsigned(&entry[*at..], 32).map_err(|e| BodyRefusal::Decode {
        offset: *at,
        what: format!("index: {e}"),
    })?;
    *at += used;
    Ok(v as u32)
}

/// Decode the locals vector at the start of a code entry: the declared local
/// types and the offset where the expression starts.
fn decode_locals(entry: &[u8]) -> Result<(Vec<Ty>, usize), BodyRefusal> {
    let mut at = 0usize;
    let runs = read_index(entry, &mut at)?;
    let mut declared = Vec::new();
    for _ in 0..runs {
        let count = read_index(entry, &mut at)?;
        let Some(&code) = entry.get(at) else {
            return Err(BodyRefusal::Decode {
                offset: at,
                what: "locals vector ends before a value type".to_string(),
            });
        };
        let ty = match code {
            0x7f => Ty::I32,
            0x7d => Ty::F32,
            0x7c => Ty::F64,
            other => {
                return Err(BodyRefusal::Decode {
                    offset: at,
                    what: format!("local value type 0x{other:02x} is outside i32/f32/f64"),
                });
            }
        };
        at += 1;
        if count > 16 {
            return Err(BodyRefusal::Decode {
                offset: at,
                what: format!("{count} locals of one type: not a two-operand body"),
            });
        }
        declared.extend(std::iter::repeat_n(ty, count as usize));
    }
    Ok((declared, at))
}

/// The instructions of a body expression as `(offset in the entry, opcode,
/// immediate index if any)`, decoded over the admitted surface only.
fn decode_expression(
    entry: &[u8],
    start: usize,
) -> Result<Vec<(usize, u8, Option<u32>)>, BodyRefusal> {
    let mut out = Vec::new();
    let mut at = start;
    while at < entry.len() {
        let offset = at;
        let op = entry[at];
        at += 1;
        let imm = match op {
            0x20..=0x22 => Some(read_index(entry, &mut at)?),
            0x00 | 0x0b | 0x0f | 0x1b | 0x5b | 0x5c | 0x61 | 0x62 | 0x8b | 0x8c | 0x96 | 0x97
            | 0x98 | 0x99 | 0x9a | 0xa4 | 0xa5 | 0xa6 => None,
            other => {
                return Err(BodyRefusal::Decode {
                    offset,
                    what: format!(
                        "opcode 0x{other:02x} is outside the float-binop body surface \
                         (local.get/set/tee, select, return, end, unreachable, f32/f64 \
                         eq/ne/abs/neg/min/max/copysign)"
                    ),
                });
            }
        };
        out.push((offset, op, imm));
    }
    Ok(out)
}

/// Run a captured code entry as the function `(a: fN, b: fN) -> fN` on the
/// bit patterns `a` and `b`, with `nan` resolving the spec's nondeterministic
/// `f.min` / `f.max` NaN result. Returns the result's bit pattern.
///
/// Fails closed on any byte outside the admitted surface, any type or arity
/// mismatch, execution of `unreachable`, anything left on the stack, and any
/// byte after the function's `end` or after a `return` other than dead
/// `unreachable`s and the closing `end`.
pub fn run_float_binop_body(
    entry: &[u8],
    width: u32,
    a: u64,
    b: u64,
    nan: NanChoice,
) -> Result<u64, BodyRefusal> {
    let Some(fty) = Ty::of_float_width(width) else {
        return Err(BodyRefusal::Decode {
            offset: 0,
            what: format!("width {width} is not a float width"),
        });
    };
    let (declared, start) = decode_locals(entry)?;
    let instrs = decode_expression(entry, start)?;
    let mut locals: Vec<Val> = vec![Val { ty: fty, bits: a }, Val { ty: fty, bits: b }];
    locals.extend(declared.into_iter().map(|ty| Val { ty, bits: 0 }));
    let mut stack: Vec<Val> = Vec::new();

    let stack_err = |offset: usize, what: &str| BodyRefusal::Stack {
        offset,
        what: what.to_string(),
    };
    for (i, &(offset, op, imm)) in instrs.iter().enumerate() {
        let float_op_width = match op {
            0x5b | 0x5c | 0x8b | 0x8c | 0x96 | 0x97 | 0x98 => Some(32u32),
            0x61 | 0x62 | 0x99 | 0x9a | 0xa4 | 0xa5 | 0xa6 => Some(64),
            _ => None,
        };
        if let Some(w) = float_op_width {
            let want = Ty::of_float_width(w).expect("32/64");
            let unary = matches!(op, 0x8b | 0x8c | 0x99 | 0x9a);
            let z2 = if unary {
                None
            } else {
                Some(
                    stack
                        .pop()
                        .ok_or_else(|| stack_err(offset, "missing operand"))?,
                )
            };
            let z1 = stack
                .pop()
                .ok_or_else(|| stack_err(offset, "missing operand"))?;
            if z1.ty != want || z2.is_some_and(|z| z.ty != want) {
                return Err(stack_err(
                    offset,
                    "operand type is not the opcode's float type",
                ));
            }
            let z2 = z2.map(|z| z.bits).unwrap_or(0);
            let (ty, bits) = match op {
                0x5b | 0x61 => (Ty::I32, spec_feq(z1.bits, z2, w)),
                0x5c | 0x62 => (Ty::I32, spec_fne(z1.bits, z2, w)),
                0x8b | 0x99 => (want, z1.bits & !sign_bit(w)),
                0x8c | 0x9a => (want, z1.bits ^ sign_bit(w)),
                0x96 | 0xa4 => (want, spec_fmin(z1.bits, z2, w, nan)),
                0x97 | 0xa5 => (want, spec_fmax(z1.bits, z2, w, nan)),
                _ => (want, spec_fcopysign(z1.bits, z2, w)),
            };
            stack.push(Val { ty, bits });
            continue;
        }
        match op {
            0x20 => {
                let v = *locals
                    .get(imm.expect("decoded with an index") as usize)
                    .ok_or_else(|| stack_err(offset, "local.get of an undeclared local"))?;
                stack.push(v);
            }
            0x21 | 0x22 => {
                let idx = imm.expect("decoded with an index") as usize;
                let v = stack
                    .pop()
                    .ok_or_else(|| stack_err(offset, "local.set with an empty stack"))?;
                let slot = locals
                    .get_mut(idx)
                    .ok_or_else(|| stack_err(offset, "local.set of an undeclared local"))?;
                if slot.ty != v.ty {
                    return Err(stack_err(offset, "local.set of a value of another type"));
                }
                *slot = v;
                if op == 0x22 {
                    stack.push(v);
                }
            }
            0x1b => {
                let c = stack
                    .pop()
                    .ok_or_else(|| stack_err(offset, "select without a condition"))?;
                let v2 = stack
                    .pop()
                    .ok_or_else(|| stack_err(offset, "select without val2"))?;
                let v1 = stack
                    .pop()
                    .ok_or_else(|| stack_err(offset, "select without val1"))?;
                if c.ty != Ty::I32 || v1.ty != v2.ty {
                    return Err(stack_err(offset, "select operand types"));
                }
                stack.push(if c.bits != 0 { v1 } else { v2 });
            }
            0x00 => return Err(BodyRefusal::Trap { offset }),
            0x0f | 0x0b => {
                let rest = &instrs[i + 1..];
                let dead_tail_ok = match op {
                    // After `return`: only dead `unreachable`s, then the
                    // function's closing `end` as the last byte.
                    0x0f => rest.split_last().is_some_and(|(last, dead)| {
                        last.1 == 0x0b && dead.iter().all(|d| d.1 == 0x00)
                    }),
                    _ => rest.is_empty(),
                };
                if !dead_tail_ok {
                    return Err(BodyRefusal::Decode {
                        offset,
                        what: "bytes after the function's exit are not a dead `unreachable* end`"
                            .to_string(),
                    });
                }
                let result = stack
                    .pop()
                    .ok_or_else(|| stack_err(offset, "no result at the function's exit"))?;
                if result.ty != fty {
                    return Err(stack_err(
                        offset,
                        "the result is not the function's float type",
                    ));
                }
                if op == 0x0b && !stack.is_empty() {
                    return Err(stack_err(offset, "values left on the stack at `end`"));
                }
                return Ok(result.bits);
            }
            _ => unreachable!("decode_expression admits only the handled opcodes"),
        }
    }
    Err(BodyRefusal::Decode {
        offset: entry.len(),
        what: "the body has no `end`".to_string(),
    })
}

// ===========================================================================
// SOURCE side: the trust-ir contract as a relation
// ===========================================================================

/// The input class a pair of operands falls in; the trust-ir contract is
/// piecewise over exactly these.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum InputClass {
    /// Both operands are NaNs.
    BothNan,
    /// Exactly one operand is a NaN.
    OneNan,
    /// Numerically equal operands with different bits: `-0.0` and `+0.0`.
    SignedZeroTie,
    /// Neither is a NaN and they are not a signed-zero tie.
    Ordered,
}

/// Classify an operand pair.
pub fn classify(a: u64, b: u64, width: u32) -> InputClass {
    match (is_nan(a, width), is_nan(b, width)) {
        (true, true) => InputClass::BothNan,
        (true, false) | (false, true) => InputClass::OneNan,
        _ if a != b && is_zero(a, width) && is_zero(b, width) => InputClass::SignedZeroTie,
        _ => InputClass::Ordered,
    }
}

/// How the `FMin` / `FMax` `-0.0` / `+0.0` tie is read.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TieReading {
    /// Either operand (trust-ir's numerics policy: not pinned). The credit's
    /// reading.
    EitherOperand,
    /// The second operand (the x86 MINSS / MAXSS convention). Used only by a
    /// negative control, to show the battery reaches the tie.
    SecondOperand,
}

/// Does the trust-ir contract of `kind` at `width` admit `result` for
/// operands `(a, b)`? `Err` names why not.
///
/// * `FCopySign`: exactly the magnitude bits of `a` with the sign bit of `b`.
/// * `FMin` / `FMax`: two NaNs — any NaN; one NaN — the other operand,
///   bit-exactly; a signed-zero tie — per `tie`; otherwise the numerically
///   lesser (greater) operand, bit-exactly.
pub fn trust_ir_float_binop_allows(
    kind: FloatBinopKind,
    width: u32,
    a: u64,
    b: u64,
    result: u64,
    tie: TieReading,
) -> Result<(), String> {
    let want_exact = |want: u64, what: &str| -> Result<(), String> {
        if result == want {
            Ok(())
        } else {
            Err(format!("{what}: expected 0x{want:x}, got 0x{result:x}"))
        }
    };
    if kind == FloatBinopKind::CopySign {
        let s = sign_bit(width);
        return want_exact((a & !s) | (b & s), "copySign");
    }
    let min = kind == FloatBinopKind::Min;
    match classify(a, b, width) {
        InputClass::BothNan => {
            if is_nan(result, width) {
                Ok(())
            } else {
                Err(format!(
                    "two NaN operands must give a NaN, got 0x{result:x}"
                ))
            }
        }
        InputClass::OneNan => {
            let other = if is_nan(a, width) { b } else { a };
            want_exact(other, "a lone NaN must give the other operand")
        }
        InputClass::SignedZeroTie => match tie {
            TieReading::EitherOperand if result == a || result == b => Ok(()),
            TieReading::EitherOperand => Err(format!(
                "a signed-zero tie must give one of the operands, got 0x{result:x}"
            )),
            TieReading::SecondOperand => want_exact(b, "the tie pinned to the second operand"),
        },
        InputClass::Ordered => {
            let (x, y) = (numeric(a, width), numeric(b, width));
            let pick_a = if min { x <= y } else { x >= y };
            want_exact(
                if pick_a { a } else { b },
                if min {
                    "an ordered pair must give the lesser operand"
                } else {
                    "an ordered pair must give the greater operand"
                },
            )
        }
    }
}

/// The operand battery at `width`: both zeros, both ones, a fraction, both
/// infinities, both extremes, both least subnormals, the least normal, and
/// quiet / signalling NaNs of both signs with and without payloads. Every
/// [`InputClass`] occurs among its pairs.
pub fn operand_battery(width: u32) -> Vec<u64> {
    let s = sign_bit(width);
    let one = if width == 32 {
        0x3f80_0000
    } else {
        0x3ff0_0000_0000_0000
    };
    let one_and_half = if width == 32 {
        0x3fc0_0000
    } else {
        0x3ff8_0000_0000_0000
    };
    let two_and_half = if width == 32 {
        0x4020_0000
    } else {
        0x4004_0000_0000_0000
    };
    let max = exp_mask(width) - 1;
    let least_normal = frac_mask(width) + 1;
    let qnan = exp_mask(width) | quiet_bit(width);
    let snan = exp_mask(width) | 1;
    vec![
        0,
        s,
        one,
        one | s,
        one_and_half,
        two_and_half | s,
        pos_inf(width),
        neg_inf(width),
        max,
        max | s,
        1,
        1 | s,
        least_normal,
        qnan,
        qnan | s,
        qnan | 5,
        snan,
        snan | s | 0x10,
    ]
}

/// The verdict on one body over the whole battery.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct BodyVerdict {
    /// The first refusal to execute, if any (not credit, not a refutation).
    pub refusal: Option<String>,
    /// The input classes at which the body diverged from the contract.
    pub refuted_classes: BTreeSet<InputClass>,
    /// One witness line per refuted class.
    pub witnesses: Vec<String>,
    /// The input classes the battery exercised.
    pub exercised: BTreeSet<InputClass>,
    /// Executions compared (pairs times NaN choices).
    pub executions: usize,
}

impl BodyVerdict {
    /// The body met the contract on every execution.
    pub fn holds(&self) -> bool {
        self.refusal.is_none() && self.refuted_classes.is_empty() && self.executions > 0
    }
}

/// Run `entry` as the `kind` body at `width` over every battery pair and every
/// [`NanChoice`], comparing each result against [`trust_ir_float_binop_allows`]
/// under `tie`.
pub fn check_float_binop_body(
    kind: FloatBinopKind,
    width: u32,
    entry: &[u8],
    tie: TieReading,
) -> BodyVerdict {
    let mut verdict = BodyVerdict::default();
    let battery = operand_battery(width);
    for &a in &battery {
        for &b in &battery {
            let class = classify(a, b, width);
            verdict.exercised.insert(class);
            for nan in NanChoice::ALL {
                verdict.executions += 1;
                match run_float_binop_body(entry, width, a, b, nan) {
                    Err(why) => {
                        verdict.refusal.get_or_insert_with(|| why.to_string());
                        return verdict;
                    }
                    Ok(r) => {
                        if let Err(why) = trust_ir_float_binop_allows(kind, width, a, b, r, tie)
                            && verdict.refuted_classes.insert(class)
                        {
                            verdict.witnesses.push(format!(
                                "{kind:?} f{width} a=0x{a:x} b=0x{b:x} ({class:?}, {nan:?}): {why}"
                            ));
                        }
                    }
                }
            }
        }
    }
    verdict
}

// ===========================================================================
// Negative controls
// ===========================================================================

/// A negative control: a mutation of the REAL captured body (or of the
/// reading it is checked under) that a wrong lowering would produce, with the
/// input class at which it must refute.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FloatBinopControl {
    /// `f.max` for `f.min` or the reverse. Must refute at an ordered pair.
    OppositeOp,
    /// The bare opcode with no NaN guards (`a b f.min`). Must refute at a lone
    /// NaN: wasm propagates it where trust-ir returns the other operand.
    UnguardedOp,
    /// The guards' `f.ne` self-tests replaced by `f.eq`. Must refute at a lone
    /// NaN.
    InvertedGuards,
    /// The outer guard returns `a` (the NaN) instead of `b`. Must refute at a
    /// lone NaN.
    GuardSelectsNan,
    /// The REAL body checked with the tie pinned to the second operand. Must
    /// refute at the signed-zero tie, which shows the battery reaches it.
    TiePinnedToSecond,
    /// `copysign` with its two operands swapped. Must refute.
    SwappedOperands,
    /// `f.abs` of the magnitude operand for `copysign`. Must refute.
    AbsForCopysign,
    /// `f.neg` of the magnitude operand for `copysign`. Must refute.
    NegForCopysign,
}

impl FloatBinopControl {
    /// Every control.
    pub const ALL: [FloatBinopControl; 8] = [
        FloatBinopControl::OppositeOp,
        FloatBinopControl::UnguardedOp,
        FloatBinopControl::InvertedGuards,
        FloatBinopControl::GuardSelectsNan,
        FloatBinopControl::TiePinnedToSecond,
        FloatBinopControl::SwappedOperands,
        FloatBinopControl::AbsForCopysign,
        FloatBinopControl::NegForCopysign,
    ];

    /// Whether the control belongs to `kind`'s row.
    pub fn applies_to(self, kind: FloatBinopKind) -> bool {
        use FloatBinopControl as C;
        match self {
            C::OppositeOp
            | C::UnguardedOp
            | C::InvertedGuards
            | C::GuardSelectsNan
            | C::TiePinnedToSecond => kind != FloatBinopKind::CopySign,
            C::SwappedOperands | C::AbsForCopysign | C::NegForCopysign => {
                kind == FloatBinopKind::CopySign
            }
        }
    }

    /// The input class the control must refute at; `None` means any class
    /// (the copysign controls are wrong on ordinary operands).
    pub fn stated_class(self) -> Option<InputClass> {
        use FloatBinopControl as C;
        match self {
            C::OppositeOp => Some(InputClass::Ordered),
            C::UnguardedOp | C::InvertedGuards | C::GuardSelectsNan => Some(InputClass::OneNan),
            C::TiePinnedToSecond => Some(InputClass::SignedZeroTie),
            C::SwappedOperands | C::AbsForCopysign | C::NegForCopysign => None,
        }
    }

    /// Build the control from a captured entry: the mutated entry and the tie
    /// reading to check it under. `None` when the entry lacks the shape the
    /// mutation needs (which the credit treats as a failure).
    pub fn build(
        self,
        kind: FloatBinopKind,
        width: u32,
        entry: &[u8],
    ) -> Option<(Vec<u8>, TieReading)> {
        use FloatBinopControl as C;
        if !self.applies_to(kind) {
            return None;
        }
        let (_, start) = decode_locals(entry).ok()?;
        let instrs = decode_expression(entry, start).ok()?;
        let wide = width == 64;
        let (min, max, copysign, eq, ne, abs, neg) = if wide {
            (0xa4u8, 0xa5u8, 0xa6u8, 0x61u8, 0x62u8, 0x99u8, 0x9au8)
        } else {
            (0x96, 0x97, 0x98, 0x5b, 0x5c, 0x8b, 0x8c)
        };
        let row_op = match kind {
            FloatBinopKind::Min => min,
            FloatBinopKind::Max => max,
            FloatBinopKind::CopySign => copysign,
        };
        let prefix = &entry[..start];
        let with_expr = |expr: &[u8]| -> Vec<u8> {
            let mut v = prefix.to_vec();
            v.extend_from_slice(expr);
            v
        };
        let mut mutated = entry.to_vec();
        match self {
            C::OppositeOp => {
                let at = instrs.iter().find(|i| i.1 == row_op)?.0;
                mutated[at] = if row_op == min { max } else { min };
                Some((mutated, TieReading::EitherOperand))
            }
            C::UnguardedOp => Some((
                with_expr(&[0x20, 0x00, 0x20, 0x01, row_op, 0x0b]),
                TieReading::EitherOperand,
            )),
            C::InvertedGuards => {
                let guards: Vec<usize> = instrs.iter().filter(|i| i.1 == ne).map(|i| i.0).collect();
                if guards.is_empty() {
                    return None;
                }
                for at in guards {
                    mutated[at] = eq;
                }
                Some((mutated, TieReading::EitherOperand))
            }
            C::GuardSelectsNan => {
                let first = instrs.first()?;
                if first.1 != 0x20 || first.2 != Some(1) {
                    return None;
                }
                mutated[first.0 + 1] = 0x00;
                Some((mutated, TieReading::EitherOperand))
            }
            C::TiePinnedToSecond => Some((mutated, TieReading::SecondOperand)),
            C::SwappedOperands => {
                let op_at = instrs.iter().position(|i| i.1 == copysign)?;
                if op_at < 2 {
                    return None;
                }
                let (x, y) = (instrs[op_at - 2], instrs[op_at - 1]);
                // Single-byte local indices only, so the swap is in place.
                if x.1 != 0x20 || y.1 != 0x20 || x.2 == y.2 || x.2? > 0x7f || y.2? > 0x7f {
                    return None;
                }
                mutated[x.0 + 1] = y.2? as u8;
                mutated[y.0 + 1] = x.2? as u8;
                Some((mutated, TieReading::EitherOperand))
            }
            C::AbsForCopysign => Some((
                with_expr(&[0x20, 0x00, abs, 0x0b]),
                TieReading::EitherOperand,
            )),
            C::NegForCopysign => Some((
                with_expr(&[0x20, 0x00, neg, 0x0b]),
                TieReading::EitherOperand,
            )),
        }
    }
}

/// Every reason the credit for the row of opcode `byte` must be REFUSED over
/// `corpus`; empty means it stands. Public so the gate tests can show the hook
/// refusing a doctored corpus.
///
/// It demands exactly one captured body for the row; that the body contains
/// the row's opcode as an instruction; that it executes and meets the
/// contract over every battery pair and NaN choice, with every input class
/// exercised; and that every control of the row builds and refutes at its
/// stated class.
pub fn float_binop_credit_failures(byte: u8, corpus: &[EmittedFloatBinopBody]) -> Vec<String> {
    let Some((kind, width)) = float_binop_row(byte) else {
        return vec![format!("0x{byte:02x} is not an f.min/f.max/f.copysign row")];
    };
    let bodies: Vec<&[u8]> = corpus
        .iter()
        .filter(|(k, w, _)| *k == kind && *w == width)
        .map(|(_, _, e)| *e)
        .collect();
    let [entry] = bodies.as_slice() else {
        return vec![format!(
            "{} captured body(ies) for {kind:?} f{width}: exactly one is required",
            bodies.len()
        )];
    };
    let mut failures = Vec::new();
    let has_op = decode_locals(entry)
        .and_then(|(_, start)| decode_expression(entry, start))
        .is_ok_and(|instrs| instrs.iter().any(|i| i.1 == byte));
    if !has_op {
        failures.push(format!(
            "the {kind:?} f{width} body does not contain opcode 0x{byte:02x} as an instruction"
        ));
    }
    let verdict = check_float_binop_body(kind, width, entry, TieReading::EitherOperand);
    if let Some(why) = &verdict.refusal {
        failures.push(format!("the {kind:?} f{width} body is refused: {why}"));
    }
    failures.extend(verdict.witnesses.iter().map(|w| format!("REFUTED: {w}")));
    for class in [
        InputClass::BothNan,
        InputClass::OneNan,
        InputClass::SignedZeroTie,
        InputClass::Ordered,
    ] {
        if !verdict.exercised.contains(&class) {
            failures.push(format!("the battery never exercised {class:?}"));
        }
    }
    for control in FloatBinopControl::ALL {
        if !control.applies_to(kind) {
            continue;
        }
        let Some((mutated, tie)) = control.build(kind, width, entry) else {
            failures.push(format!(
                "control {control:?} cannot be built on the {kind:?} f{width} body"
            ));
            continue;
        };
        let v = check_float_binop_body(kind, width, &mutated, tie);
        if let Some(why) = &v.refusal {
            failures.push(format!("control {control:?} did not execute: {why}"));
        } else if v.refuted_classes.is_empty() {
            failures.push(format!("control {control:?} SURVIVED on {kind:?} f{width}"));
        } else if let Some(class) = control.stated_class()
            && !v.refuted_classes.contains(&class)
        {
            failures.push(format!(
                "control {control:?} refuted at {:?} but not at its stated {class:?}",
                v.refuted_classes
            ));
        }
    }
    failures
}

/// THE COVERAGE-GATE CREDIT HOOK for `f32.min`/`f32.max`/`f64.min`/`f64.max`
/// and the body half of the `copysign` rows: `true` iff
/// [`float_binop_credit_failures`] is empty over [`EMITTED_FLOAT_BINOP_BODIES`].
pub fn float_binop_body_discharges_valid(byte: u8) -> bool {
    float_binop_row(byte).is_some()
        && float_binop_credit_failures(byte, EMITTED_FLOAT_BINOP_BODIES).is_empty()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn every_captured_body_holds_and_every_row_credits() {
        for byte in [0x96, 0x97, 0x98, 0xa4, 0xa5, 0xa6] {
            let failures = float_binop_credit_failures(byte, EMITTED_FLOAT_BINOP_BODIES);
            assert!(failures.is_empty(), "0x{byte:02x}: {failures:#?}");
        }
    }

    #[test]
    fn spec_min_max_signed_zero_and_infinity_cases() {
        let s = sign_bit(32);
        assert_eq!(spec_fmin(0, s, 32, NanChoice::CanonicalPositive), s);
        assert_eq!(spec_fmin(s, 0, 32, NanChoice::CanonicalPositive), s);
        assert_eq!(spec_fmax(0, s, 32, NanChoice::CanonicalPositive), 0);
        assert_eq!(spec_fmax(s, 0, 32, NanChoice::CanonicalPositive), 0);
        assert_eq!(
            spec_fmin(neg_inf(32), 1, 32, NanChoice::CanonicalPositive),
            neg_inf(32)
        );
        assert_eq!(
            spec_fmax(pos_inf(32), 1, 32, NanChoice::CanonicalPositive),
            pos_inf(32)
        );
        let qnan = exp_mask(32) | quiet_bit(32);
        assert!(is_nan(
            spec_fmin(qnan, 1, 32, NanChoice::ArithmeticNegative),
            32
        ));
    }

    #[test]
    fn spec_ne_eq_follow_ieee_equality() {
        let s = sign_bit(64);
        let qnan = exp_mask(64) | quiet_bit(64);
        assert_eq!(spec_fne(qnan, qnan, 64), 1);
        assert_eq!(spec_feq(qnan, qnan, 64), 0);
        assert_eq!(spec_fne(0, s, 64), 0);
        assert_eq!(spec_feq(0, s, 64), 1);
        assert_eq!(spec_fne(1, 2, 64), 1);
    }

    #[test]
    fn the_evaluator_refuses_what_it_does_not_model() {
        // i32.add inside a float body.
        let entry = [0x00, 0x20, 0x00, 0x6a, 0x0b];
        assert!(matches!(
            run_float_binop_body(&entry, 32, 0, 0, NanChoice::CanonicalPositive),
            Err(BodyRefusal::Decode { .. })
        ));
        // Executed `unreachable`.
        let entry = [0x00, 0x00, 0x0b];
        assert!(matches!(
            run_float_binop_body(&entry, 32, 0, 0, NanChoice::CanonicalPositive),
            Err(BodyRefusal::Trap { .. })
        ));
        // Live code after `return`.
        let entry = [0x00, 0x20, 0x00, 0x0f, 0x20, 0x01, 0x0b];
        assert!(matches!(
            run_float_binop_body(&entry, 32, 0, 0, NanChoice::CanonicalPositive),
            Err(BodyRefusal::Decode { .. })
        ));
        // An f64 op on f32 operands.
        let entry = [0x00, 0x20, 0x00, 0x20, 0x01, 0xa4, 0x0b];
        assert!(matches!(
            run_float_binop_body(&entry, 32, 0, 0, NanChoice::CanonicalPositive),
            Err(BodyRefusal::Stack { .. })
        ));
    }
}
