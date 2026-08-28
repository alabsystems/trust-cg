// trust-cg-verify/wasm_encoding_proofs.rs - P4 families (4)(5)(6): the encoder/byte family
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Reference: WebAssembly Core Specification, Release 2.0 — §5.2.2 (Integers:
//            the inductive uN / sN LEB128 definitions), §5.4 (Instructions),
//            §5.5 (Modules: the section grammar and the index spaces).
//
// WHAT THIS FAMILY IS. P0-P3 proved things about VALUES: what an instruction
// computes. This family proves things about BYTES and INDICES: that the module
// the backend hands an engine says what the compile meant. Three obligations
// live here, matching the ratified ladder's families (4), (5) and (6):
//
//   (5) BYTE RECONSTRUCTION with an INDEPENDENT signed-LEB128 decoder. The
//       coverage gate refuses to credit `I32Const` / `I64Const` because
//       `const == const` is a self-equality: the only thing standing between
//       "the backend meant -1" and "the module says -1" is `write_sleb128`, and
//       asking that function what it wrote proves nothing. [`spec_decode_signed`]
//       is written from the spec's INDUCTIVE sN definition — a recursion on the
//       7-bit budget with the spec's own three cases and its range side
//       conditions — and shares no code, and no shape, with the encoder's
//       `value >>= 7` loop. The obligation decodes the REAL emitted immediate
//       bytes and compares against the constant the trust-ir carried.
//
//   (4) MODULE-LEVEL INDEXING / ENCODING. Every index the backend hands out
//       must resolve in its space, imported entities must occupy the LOW
//       indices with definitions following (P2's shift, whose silent failure is
//       `call 0` landing on a host import instead of the defined function it
//       type-checks against), the funcref element segment must cover the whole
//       function index space, and the section framing must be well-formed. The
//       machine side is DECODED from the emitted module bytes by
//       [`decode_module`] — this module never asks [`WasmModule`] what it wrote.
//
//   (6) TARGETINFO CONFORMANCE. The compile REQUIRED a wasm32 pin (32-bit
//       pointers, little-endian). This closes the loop on that P1 guard by
//       checking the emitted module actually spends it: MVP 32-bit memory
//       limits (never a memory64 limits flag), i32 offset expressions, i32
//       shadow-stack and host-base globals, memarg alignment inside the wasm32
//       scalar access set, and static-data images laid down LITTLE-ENDIAN.
//
// HOW THE MACHINE SIDE STAYS INDEPENDENT. Three separate mechanisms, because
// this crate cannot depend on `trust-cg-codegen` (that crate depends on THIS
// one; a normal edge would be a Cargo cycle):
//
//   * the module/target obligations take `&[u8]` and are driven by
//     `tests/wasm_encoding_gate.rs`, which holds `trust-cg-codegen` as a
//     DEV-dependency and compiles real modules through the real backend;
//   * the const-immediate obligation ALSO takes bytes, so the same live path
//     drives it;
//   * the COVERAGE-GATE credit hook cannot compile anything (it runs inside
//     `coverage_gate.rs`, in this crate), so it runs over
//     [`EMITTED_CONST_IMMEDIATES`] — immediate bytes CAPTURED from the real
//     backend. That capture is not trusted on its word: the gate test
//     `corpus_is_what_the_live_backend_emits_today` recompiles every entry
//     through the live backend and fails on any divergence, so the corpus
//     cannot rot into a fiction while the row stays green.
//
// WHAT THIS FAMILY DOES NOT ESTABLISH, said plainly:
//
//   * NOTHING here is a proof of the wasm SEMANTICS of the decoded module. The
//     decoder is a SYNTACTIC one derived from the binary-format grammar; it does
//     not run wasm VALIDATION (operand-stack typing, block arity, unreachable
//     typing). A module can decode perfectly and still be rejected by an engine.
//     The reference-validator gate that does check that lives in the codegen
//     crate's `tests/wasm_module_validation.rs`, and it is a different claim.
//   * Nothing here says the lowering chose the RIGHT constant, the RIGHT callee,
//     or the right anything. Family (5) says: whatever integer the lowering
//     handed the encoder is the integer the bytes denote. Family (4) says: the
//     index in the bytes resolves, and shifts by exactly the import count.
//     Choosing correctly is the lowering-refinement family's obligation.
//   * A label index is checked to be IN RANGE of the enclosing nesting depth.
//     Nothing here says which block that label DENOTES — that is the relooper
//     bisimulation's obligation, and [`WASM_ENCODING_DEFERRALS`] says so.
//   * The full i32 / i64 const ranges are not swept by the default lane; the
//     corpus is the byte-length boundaries, the sign-extension edges and the
//     maximum-length encodings. `tests/wasm_encoding_gate.rs` carries an
//     `#[ignore]`d EXHAUSTIVE full-i32 sweep for anyone who wants the whole
//     4.29e9, and the report states which one was run.

//! P4 encoder/byte obligations for the WebAssembly backend: an independent
//! spec-derived LEB128 decoder, a module-bytes decoder, and the indexing /
//! encoding / target-conformance obligations built on top of them.

use std::collections::HashMap;
use std::fmt;

// ===========================================================================
// (5a) LEB128, transcribed from the spec's INDUCTIVE definition
// ===========================================================================

/// Why an LEB128 decode failed. Every variant is a REFUTATION of the encoding,
/// never a "could not tell": the decoder fails closed.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LebError {
    /// The byte stream ended while a continuation byte promised more.
    Truncated {
        /// Bytes available when the decoder needed one more.
        available: usize,
    },
    /// A continuation byte appeared with fewer than 8 bits of budget left —
    /// the encoding claims more groups than the target width can hold.
    ContinuationPastBudget {
        /// Bits of budget remaining when the continuation byte appeared.
        budget_bits: u32,
        /// The offending byte.
        byte: u8,
    },
    /// The final group's value does not fit the remaining budget: an OVERLONG
    /// or out-of-range encoding. The spec's `uN` / `sN` side conditions reject
    /// these, and so does every conforming engine.
    OutOfRange {
        /// Bits of budget remaining at the final group.
        budget_bits: u32,
        /// The offending final byte.
        byte: u8,
    },
}

impl fmt::Display for LebError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            LebError::Truncated { available } => write!(
                f,
                "LEB128 truncated: a continuation byte promised another group but only \
                 {available} byte(s) were available"
            ),
            LebError::ContinuationPastBudget { budget_bits, byte } => write!(
                f,
                "LEB128 byte 0x{byte:02x} sets the continuation bit with only {budget_bits} bit(s) \
                 of budget left — the encoding claims more groups than the target width holds"
            ),
            LebError::OutOfRange { budget_bits, byte } => write!(
                f,
                "LEB128 final byte 0x{byte:02x} does not fit the remaining {budget_bits} bit(s) of \
                 budget — an overlong or out-of-range encoding"
            ),
        }
    }
}

/// The spec's `sN` production, transcribed directly (WebAssembly Core
/// Specification §5.2.2, "Integers"):
///
/// ```text
///   sN ::= n:byte            => n                      (if n < 2^6 and n < 2^(N-1))
///        | n:byte            => n - 2^7                (if 2^6 <= n < 2^7 and n >= 2^7 - 2^(N-1))
///        | n:byte  m:s(N-7)  => 2^7 * m + (n - 2^7)    (if n >= 2^7 and N > 7)
/// ```
///
/// This is a RECURSION ON THE BIT BUDGET with the spec's three cases and its
/// two range side conditions, which is a structurally different program from
/// the encoder's iterative `value >>= 7` accumulate loop
/// (`trust_cg_codegen::wasm::encode::write_sleb128`). Neither one can be
/// rewritten into the other by renaming, and neither reads the other's source.
/// That independence is the entire point: `decode(emit(v)) == v` is then a real
/// agreement between two implementations of the spec, not the `const == const`
/// self-equality the coverage gate refuses to credit.
///
/// Returns the decoded value and the number of bytes consumed. Fails closed:
/// an overlong encoding, a value outside `sN`, or a truncated stream is an
/// `Err`, never a best-effort value.
///
/// # Panics
///
/// Never. `bits` outside `1..=64` returns `Err(LebError::OutOfRange)` on the
/// first byte rather than panicking, because a zero budget admits no group.
pub fn spec_decode_signed(bytes: &[u8], bits: u32) -> Result<(i64, usize), LebError> {
    fn s_n(bytes: &[u8], at: usize, bits: u32) -> Result<(i64, usize), LebError> {
        let Some(&n) = bytes.get(at) else {
            return Err(LebError::Truncated {
                available: bytes.len().saturating_sub(at),
            });
        };
        // `2^(N-1)` as an i128 so the N=64 case does not have to be special.
        let half = if bits == 0 || bits > 64 {
            0i128
        } else {
            1i128 << (bits - 1)
        };
        let n_val = i128::from(n);
        if n < 0x40 {
            // Case 1: a terminal non-negative group.
            if n_val < half {
                return Ok((i64::from(n), at + 1));
            }
            return Err(LebError::OutOfRange {
                budget_bits: bits,
                byte: n,
            });
        }
        if n < 0x80 {
            // Case 2: a terminal negative group, `n - 2^7`.
            if n_val >= 128 - half {
                return Ok((i64::from(n) - 128, at + 1));
            }
            return Err(LebError::OutOfRange {
                budget_bits: bits,
                byte: n,
            });
        }
        // Case 3: a continuation group, `2^7 * m + (n - 2^7)`.
        if bits <= 7 {
            return Err(LebError::ContinuationPastBudget {
                budget_bits: bits,
                byte: n,
            });
        }
        let (m, next) = s_n(bytes, at + 1, bits - 7)?;
        // No overflow is possible: `m` inhabits `[-2^(N-8), 2^(N-8))` by the
        // recursion's own postcondition and `(n - 2^7)` inhabits `[0, 127]`, so
        // `128*m + (n - 128)` inhabits exactly `[-2^(N-1), 2^(N-1))`.
        let value = 128i128 * i128::from(m) + (n_val - 128);
        Ok((value as i64, next))
    }
    s_n(bytes, 0, bits)
}

/// The spec's `uN` production, transcribed directly (§5.2.2):
///
/// ```text
///   uN ::= n:byte            => n                    (if n < 2^7 and n < 2^N)
///        | n:byte  m:u(N-7)  => 2^7 * m + (n - 2^7)  (if n >= 2^7 and N > 7)
/// ```
///
/// Same independence argument as [`spec_decode_signed`]; used for every index,
/// count, length and `memarg` field in the module grammar.
pub fn spec_decode_unsigned(bytes: &[u8], bits: u32) -> Result<(u64, usize), LebError> {
    fn u_n(bytes: &[u8], at: usize, bits: u32) -> Result<(u128, usize), LebError> {
        let Some(&n) = bytes.get(at) else {
            return Err(LebError::Truncated {
                available: bytes.len().saturating_sub(at),
            });
        };
        let limit = if bits == 0 || bits > 64 {
            0u128
        } else {
            1u128 << bits
        };
        if n < 0x80 {
            if u128::from(n) < limit {
                return Ok((u128::from(n), at + 1));
            }
            return Err(LebError::OutOfRange {
                budget_bits: bits,
                byte: n,
            });
        }
        if bits <= 7 {
            return Err(LebError::ContinuationPastBudget {
                budget_bits: bits,
                byte: n,
            });
        }
        let (m, next) = u_n(bytes, at + 1, bits - 7)?;
        Ok((128 * m + u128::from(n - 128), next))
    }
    let (v, next) = u_n(bytes, 0, bits)?;
    Ok((v as u64, next))
}

/// The number of bytes the spec's CANONICAL (shortest) `sN` encoding of `value`
/// occupies, derived from the RANGE the spec's production admits at each length
/// rather than by simulating any encoder.
///
/// An `L`-group `sN` encoding denotes exactly the values in `[-2^(7L-1),
/// 2^(7L-1))` — that is what the case-1 and case-2 side conditions say, unrolled
/// `L` times — so the canonical length is the least `L` whose interval contains
/// the value, capped at `ceil(N/7)`.
///
/// The derivation matters. The obvious implementation is the encoder's own
/// termination test (`v >>= 7` until the remaining bits are all sign), and an
/// implementation written that way would AGREE with a buggy encoder by
/// construction — it would be the same program twice, which is the tautology
/// this whole family exists to avoid. The closed form below shares nothing with
/// `write_sleb128`.
///
/// The length half of the const obligation is load-bearing on its own: the wasm
/// spec's `sN` production ADMITS padded encodings (`0x80 0x00` really is a legal
/// `i32.const 0`), so a decode-only check cannot see a padding change. This can.
pub fn canonical_signed_len(value: i64, bits: u32) -> usize {
    let max_groups = bits.div_ceil(7).max(1) as usize;
    let v = i128::from(value);
    for len in 1..=max_groups {
        let half = 1i128 << (7 * len - 1);
        if -half <= v && v < half {
            return len;
        }
    }
    max_groups
}

// ===========================================================================
// (5b) The captured emitted-immediate corpus + its freshness contract
// ===========================================================================

/// One captured const immediate: `(intended value, value width in bits, the
/// immediate bytes the REAL backend emitted)`.
pub type EmittedConstImmediate = (i64, u32, &'static [u8]);

/// The immediate bytes the real wasm backend emitted for each intended
/// constant, captured by compiling a `() -> iN { ret <const> }` trust-ir module
/// and DECODING the emitted code section (never by asking the encoder).
///
/// # Why a captured corpus exists at all
///
/// The coverage gate's credit hook runs inside this crate, and this crate
/// cannot depend on `trust-cg-codegen` (that crate depends on this one). So the
/// gate cannot compile a module to get live bytes. It runs over these instead.
///
/// # Why the capture is not a trust-me
///
/// `tests/wasm_encoding_gate.rs::corpus_is_what_the_live_backend_emits_today`
/// recompiles EVERY entry through the live backend and asserts the emitted
/// immediate is byte-identical to the capture. A backend change that alters
/// these bytes turns that test RED; the corpus cannot silently drift out from
/// under a green gate row.
///
/// # What the value set covers
///
/// Both signs of zero-adjacent values; every SLEB128 byte-length boundary for
/// the width (`±(2^(7k-1) - 1)`, `±2^(7k-1)`, `±(2^(7k-1) + 1)`) where the
/// continuation bits flip; the sign-extension edges `-1`, `i32::MIN`,
/// `i64::MIN`; and the MAXIMUM-LENGTH encodings (5 bytes for i32, 10 for i64,
/// where the final group carries only 4 / 1 significant bits).
///
/// It does NOT cover the full i32 / i64 ranges — see the module header and
/// [`WASM_ENCODING_DEFERRALS`].
pub const EMITTED_CONST_IMMEDIATES: &[EmittedConstImmediate] = &[
    // ---- i32.const (0x41), immediate is s32 ----
    (0, 32, &[0x00]),
    (1, 32, &[0x01]),
    (-1, 32, &[0x7f]),
    (2, 32, &[0x02]),
    (-2, 32, &[0x7e]),
    (42, 32, &[0x2a]),
    (-42, 32, &[0x56]),
    (63, 32, &[0x3f]),
    (64, 32, &[0xc0, 0x00]),
    (-64, 32, &[0x40]),
    (-65, 32, &[0xbf, 0x7f]),
    (127, 32, &[0xff, 0x00]),
    (128, 32, &[0x80, 0x01]),
    (-128, 32, &[0x80, 0x7f]),
    (-129, 32, &[0xff, 0x7e]),
    (8191, 32, &[0xff, 0x3f]),
    (8192, 32, &[0x80, 0xc0, 0x00]),
    (-8192, 32, &[0x80, 0x40]),
    (-8193, 32, &[0xff, 0xbf, 0x7f]),
    (1_048_575, 32, &[0xff, 0xff, 0x3f]),
    (1_048_576, 32, &[0x80, 0x80, 0xc0, 0x00]),
    (-1_048_576, 32, &[0x80, 0x80, 0x40]),
    (-1_048_577, 32, &[0xff, 0xff, 0xbf, 0x7f]),
    (134_217_727, 32, &[0xff, 0xff, 0xff, 0x3f]),
    (134_217_728, 32, &[0x80, 0x80, 0x80, 0xc0, 0x00]),
    (-134_217_728, 32, &[0x80, 0x80, 0x80, 0x40]),
    (-134_217_729, 32, &[0xff, 0xff, 0xff, 0xbf, 0x7f]),
    (2_147_483_646, 32, &[0xfe, 0xff, 0xff, 0xff, 0x07]),
    (2_147_483_647, 32, &[0xff, 0xff, 0xff, 0xff, 0x07]),
    (-2_147_483_647, 32, &[0x81, 0x80, 0x80, 0x80, 0x78]),
    (-2_147_483_648, 32, &[0x80, 0x80, 0x80, 0x80, 0x78]),
    // ---- i64.const (0x42), immediate is s64 ----
    (0, 64, &[0x00]),
    (1, 64, &[0x01]),
    (-1, 64, &[0x7f]),
    (63, 64, &[0x3f]),
    (64, 64, &[0xc0, 0x00]),
    (-64, 64, &[0x40]),
    (-65, 64, &[0xbf, 0x7f]),
    (8191, 64, &[0xff, 0x3f]),
    (8192, 64, &[0x80, 0xc0, 0x00]),
    (-8192, 64, &[0x80, 0x40]),
    (-8193, 64, &[0xff, 0xbf, 0x7f]),
    (1_048_575, 64, &[0xff, 0xff, 0x3f]),
    (1_048_576, 64, &[0x80, 0x80, 0xc0, 0x00]),
    (-1_048_576, 64, &[0x80, 0x80, 0x40]),
    (-1_048_577, 64, &[0xff, 0xff, 0xbf, 0x7f]),
    (134_217_727, 64, &[0xff, 0xff, 0xff, 0x3f]),
    (134_217_728, 64, &[0x80, 0x80, 0x80, 0xc0, 0x00]),
    (-134_217_728, 64, &[0x80, 0x80, 0x80, 0x40]),
    (-134_217_729, 64, &[0xff, 0xff, 0xff, 0xbf, 0x7f]),
    (17_179_869_183, 64, &[0xff, 0xff, 0xff, 0xff, 0x3f]),
    (17_179_869_184, 64, &[0x80, 0x80, 0x80, 0x80, 0xc0, 0x00]),
    (-17_179_869_184, 64, &[0x80, 0x80, 0x80, 0x80, 0x40]),
    (-17_179_869_185, 64, &[0xff, 0xff, 0xff, 0xff, 0xbf, 0x7f]),
    (2_199_023_255_551, 64, &[0xff, 0xff, 0xff, 0xff, 0xff, 0x3f]),
    (
        2_199_023_255_552,
        64,
        &[0x80, 0x80, 0x80, 0x80, 0x80, 0xc0, 0x00],
    ),
    (
        -2_199_023_255_552,
        64,
        &[0x80, 0x80, 0x80, 0x80, 0x80, 0x40],
    ),
    (
        -2_199_023_255_553,
        64,
        &[0xff, 0xff, 0xff, 0xff, 0xff, 0xbf, 0x7f],
    ),
    (
        281_474_976_710_655,
        64,
        &[0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x3f],
    ),
    (
        281_474_976_710_656,
        64,
        &[0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0xc0, 0x00],
    ),
    (
        -281_474_976_710_656,
        64,
        &[0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x40],
    ),
    (
        -281_474_976_710_657,
        64,
        &[0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xbf, 0x7f],
    ),
    (
        36_028_797_018_963_967,
        64,
        &[0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x3f],
    ),
    (
        36_028_797_018_963_968,
        64,
        &[0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0xc0, 0x00],
    ),
    (
        -36_028_797_018_963_968,
        64,
        &[0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x40],
    ),
    (
        -36_028_797_018_963_969,
        64,
        &[0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xbf, 0x7f],
    ),
    (
        4_611_686_018_427_387_903,
        64,
        &[0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x3f],
    ),
    (
        4_611_686_018_427_387_904,
        64,
        &[0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0xc0, 0x00],
    ),
    (
        -4_611_686_018_427_387_904,
        64,
        &[0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x40],
    ),
    (
        -4_611_686_018_427_387_905,
        64,
        &[0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xbf, 0x7f],
    ),
    (
        9_223_372_036_854_775_806,
        64,
        &[0xfe, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x00],
    ),
    (
        9_223_372_036_854_775_807,
        64,
        &[0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x00],
    ),
    (
        -9_223_372_036_854_775_807,
        64,
        &[0x81, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x7f],
    ),
    (
        -9_223_372_036_854_775_808,
        64,
        &[0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x7f],
    ),
];

/// The `i32.const` opcode byte (spec §5.4.5). Its immediate is `s32`.
pub const OP_I32_CONST: u8 = 0x41;
/// The `i64.const` opcode byte. Its immediate is `s64`.
pub const OP_I64_CONST: u8 = 0x42;
/// The `f32.const` opcode byte. Its immediate is 4 RAW little-endian bytes.
pub const OP_F32_CONST: u8 = 0x43;
/// The `f64.const` opcode byte. Its immediate is 8 RAW little-endian bytes.
pub const OP_F64_CONST: u8 = 0x44;

// ===========================================================================
// Obligation vocabulary
// ===========================================================================

/// Which ratified P4 family an obligation belongs to.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EncodingFamily {
    /// Family (5): byte reconstruction via the independent LEB128 decoder.
    ConstImmediate,
    /// Family (4): module-level indexing and encoding.
    ModuleIndexing,
    /// Family (6): TargetInfo conformance.
    TargetConformance,
}

impl fmt::Display for EncodingFamily {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            EncodingFamily::ConstImmediate => f.write_str("P4-5 const-immediate"),
            EncodingFamily::ModuleIndexing => f.write_str("P4-4 module-indexing"),
            EncodingFamily::TargetConformance => f.write_str("P4-6 target-conformance"),
        }
    }
}

/// The verdict on one obligation. There are exactly three, and only the first
/// is credit.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Outcome {
    /// The obligation HOLDS on the bytes examined.
    Holds,
    /// The obligation is REFUTED, with the concrete divergence named.
    Refuted(String),
    /// The construct the obligation speaks about is ABSENT from these bytes
    /// (e.g. element-segment obligations on a table-free module). This is
    /// **not credit** — it is counted separately and reported separately, so a
    /// corpus that happens to exercise nothing can never read as green.
    NotApplicable(String),
}

/// One encoding obligation and its verdict.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EncodingObligation {
    /// The P4 family this obligation discharges.
    pub family: EncodingFamily,
    /// What it claims, in one line.
    pub name: String,
    /// Whether it held on the bytes it was given.
    pub outcome: Outcome,
}

impl EncodingObligation {
    /// Construct a holding obligation.
    pub fn holds(family: EncodingFamily, name: impl Into<String>) -> Self {
        Self {
            family,
            name: name.into(),
            outcome: Outcome::Holds,
        }
    }

    /// Construct a refuted obligation.
    pub fn refuted(
        family: EncodingFamily,
        name: impl Into<String>,
        why: impl Into<String>,
    ) -> Self {
        Self {
            family,
            name: name.into(),
            outcome: Outcome::Refuted(why.into()),
        }
    }

    /// Construct a not-applicable obligation (no construct to speak about).
    pub fn not_applicable(
        family: EncodingFamily,
        name: impl Into<String>,
        why: impl Into<String>,
    ) -> Self {
        Self {
            family,
            name: name.into(),
            outcome: Outcome::NotApplicable(why.into()),
        }
    }

    /// True iff this obligation is credit.
    pub fn is_holding(&self) -> bool {
        matches!(self.outcome, Outcome::Holds)
    }

    /// True iff this obligation was REFUTED (the anti-tautology guards demand
    /// this of every mutated input).
    pub fn is_refuted(&self) -> bool {
        matches!(self.outcome, Outcome::Refuted(_))
    }
}

/// A real proven / refuted / not-applicable tally — never a bare headline count.
///
/// "Proven" here means DECIDED on the bytes examined: every obligation in this
/// module is a total predicate over a concrete emitted module, so it is exact
/// and complete for that module — and says nothing whatever about a module it
/// was not run on. That is a different kind of evidence from the SMT/evaluator
/// obligations elsewhere in this crate, which quantify over symbolic inputs.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct EncodingReport {
    /// Obligations that HELD on the bytes examined.
    pub proven: usize,
    /// Obligations that were REFUTED.
    pub refuted: usize,
    /// Obligations whose construct was absent (NOT credit).
    pub not_applicable: usize,
    /// One line per refutation, so a failure names itself.
    pub refutations: Vec<String>,
    /// One line per not-applicable, so absent coverage names itself too.
    pub inapplicable: Vec<String>,
}

impl EncodingReport {
    /// Tally a slice of obligations.
    pub fn of(obligations: &[EncodingObligation]) -> Self {
        let mut r = Self::default();
        for ob in obligations {
            match &ob.outcome {
                Outcome::Holds => r.proven += 1,
                Outcome::Refuted(why) => {
                    r.refuted += 1;
                    r.refutations.push(format!("{}: {why}", ob.name));
                }
                Outcome::NotApplicable(why) => {
                    r.not_applicable += 1;
                    r.inapplicable.push(format!("{}: {why}", ob.name));
                }
            }
        }
        r
    }

    /// Fold another report into this one.
    pub fn absorb(&mut self, other: EncodingReport) {
        self.proven += other.proven;
        self.refuted += other.refuted;
        self.not_applicable += other.not_applicable;
        self.refutations.extend(other.refutations);
        self.inapplicable.extend(other.inapplicable);
    }
}

impl fmt::Display for EncodingReport {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{} proven / {} refuted / {} not-applicable",
            self.proven, self.refuted, self.not_applicable
        )
    }
}

// ===========================================================================
// (5c) The const-immediate obligation
// ===========================================================================

/// The FAMILY-(5) obligation for one emitted constant.
///
/// * SOURCE side: `intended` — the integer the trust-ir `Const` carried,
///   independent of anything the encoder did.
/// * MACHINE side: `immediate` — the REAL bytes that followed the const opcode
///   in the emitted module, put through [`spec_decode_signed`] at the width the
///   opcode's spec production names (`s32` for `0x41`, `s64` for `0x42`).
///
/// It holds iff the decode succeeds, consumes EXACTLY the immediate, yields
/// `intended`, and the encoding is the CANONICAL (shortest) one. All four
/// conjuncts matter, and the LAST one is not redundant: the spec's `sN`
/// production admits PADDED encodings (`0x80 0x00` is a legal `i32.const 0`), so
/// a value-only check cannot see an overlong pad — and a length-only check
/// cannot see a wrong value of the right length.
pub fn const_immediate_obligation(
    intended: i64,
    opcode: u8,
    immediate: &[u8],
) -> EncodingObligation {
    let bits = match opcode {
        OP_I32_CONST => 32,
        OP_I64_CONST => 64,
        other => {
            return EncodingObligation::refuted(
                EncodingFamily::ConstImmediate,
                format!("const immediate for opcode 0x{other:02x}"),
                format!(
                    "0x{other:02x} is not an integer const opcode (0x41 i32.const / 0x42 \
                     i64.const); fail closed rather than decode an immediate whose production is \
                     unknown"
                ),
            );
        }
    };
    let name = format!(
        "0x{opcode:02x} i{bits}.const {intended} -> the emitted immediate {immediate:02x?} decodes \
         to {intended} under the spec s{bits} production"
    );
    // Fitting the width is part of the claim: `i32.const` carries s32, so an
    // immediate outside `[-2^31, 2^31)` is malformed even if it decodes.
    if bits == 32 && (intended < i64::from(i32::MIN) || intended > i64::from(i32::MAX)) {
        return EncodingObligation::refuted(
            EncodingFamily::ConstImmediate,
            name,
            format!("intended value {intended} does not inhabit s32"),
        );
    }
    match spec_decode_signed(immediate, bits) {
        Err(e) => EncodingObligation::refuted(
            EncodingFamily::ConstImmediate,
            name,
            format!("independent spec decoder REJECTED the emitted immediate: {e}"),
        ),
        Ok((decoded, used)) => {
            if decoded != intended {
                return EncodingObligation::refuted(
                    EncodingFamily::ConstImmediate,
                    name,
                    format!(
                        "decoded {decoded}, intended {intended} (a {} divergence)",
                        if decoded.wrapping_sub(intended) == 0 {
                            "zero"
                        } else {
                            "value"
                        }
                    ),
                );
            }
            if used != immediate.len() {
                return EncodingObligation::refuted(
                    EncodingFamily::ConstImmediate,
                    name,
                    format!(
                        "decode consumed {used} of {} immediate byte(s) — trailing bytes are not \
                         part of the immediate",
                        immediate.len()
                    ),
                );
            }
            let canonical = canonical_signed_len(intended, bits);
            if used != canonical {
                return EncodingObligation::refuted(
                    EncodingFamily::ConstImmediate,
                    name,
                    format!(
                        "encoding is {used} byte(s); the canonical s{bits} form is {canonical}"
                    ),
                );
            }
            EncodingObligation::holds(EncodingFamily::ConstImmediate, name)
        }
    }
}

/// Every family-(5) obligation over [`EMITTED_CONST_IMMEDIATES`].
pub fn emitted_const_immediate_obligations() -> Vec<EncodingObligation> {
    EMITTED_CONST_IMMEDIATES
        .iter()
        .map(|&(intended, bits, bytes)| {
            let opcode = if bits == 32 {
                OP_I32_CONST
            } else {
                OP_I64_CONST
            };
            const_immediate_obligation(intended, opcode, bytes)
        })
        .collect()
}

/// THE COVERAGE-GATE CREDIT HOOK for the two RED const rows.
///
/// `byte` is [`OP_I32_CONST`] or [`OP_I64_CONST`]. Returns `true` iff EVERY
/// captured immediate at that width decodes, under the independent spec
/// decoder, to exactly the constant the compile intended, at canonical length.
///
/// Fails CLOSED: `false` for any other opcode byte, and `false` if the corpus
/// holds no entry at that width (an empty set is not a discharged set).
///
/// # The verdict on the two RED rows
///
/// `coverage_gate::wasm_deferred_value_op_reason` currently keeps
/// `WasmOpcode::I32Const` / `I64Const` RED with the reason "no independent
/// signed-LEB immediate decode/value obligation; const==const would be a
/// degenerate self-equality". **That reason no longer holds.** There is now an
/// independent decoder, it is derived from the spec's own production rather than
/// from the encoder, it runs on the REAL emitted bytes, and every mutation of
/// those bytes — a dropped continuation bit, a ULEB-for-SLEB confusion, an
/// overlong pad, a truncation — is REFUTED
/// (`tests/wasm_encoding_gate.rs::live_const_immediate_mutants_are_refuted`).
/// So the rows CAN be credited, and this is the hook that credits them.
///
/// # What crediting them does NOT say
///
/// Read the row as exactly this and nothing more: **the immediate bytes the
/// backend emitted for a constant denote that constant.** In particular it does
/// NOT say —
///
/// * that the lowering picked the RIGHT constant. `emit_const` canonicalizes an
///   integer into its narrow carrier before encoding (`Const { ty: U8, value:
///   300 }` becomes `i32.const 44`); whether that canonicalization is correct is
///   the P3 narrow-width family's obligation, and a wrong carrier value would
///   encode and decode perfectly here.
/// * anything about `f32.const` / `f64.const`. Those carry a raw IEEE-754
///   payload, not an LEB128; they stay RED, by name, in
///   [`WASM_ENCODING_DEFERRALS`].
/// * that the constant is on the operand stack at the right moment, or is
///   consumed by the right instruction. That is the stack/CFG discipline, not
///   the immediate encoding.
/// * that EVERY i32/i64 constant in the whole 2^32 / 2^64 space round-trips
///   through the MODULE path. The corpus is the byte-length boundaries, the
///   sign-extension edges and the maximum-length encodings; the full-i32 sweep
///   in the gate test covers the encoder function, not the module path. The
///   difference is named in [`WASM_ENCODING_DEFERRALS`].
pub fn const_immediate_discharges_valid(byte: u8) -> bool {
    let bits = match byte {
        OP_I32_CONST => 32u32,
        OP_I64_CONST => 64,
        _ => return false,
    };
    let mut seen = 0usize;
    for &(intended, w, bytes) in EMITTED_CONST_IMMEDIATES {
        if w != bits {
            continue;
        }
        seen += 1;
        if !const_immediate_obligation(intended, byte, bytes).is_holding() {
            return false;
        }
    }
    seen > 0
}

// ===========================================================================
// (4a) The module decoder — every structure rebuilt FROM THE BYTES
// ===========================================================================

/// Why a module failed to decode. Every variant is a refutation of the
/// encoding's well-formedness: the decoder never guesses.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct WasmDecodeError {
    /// Byte offset in the module where the decode gave up.
    pub offset: usize,
    /// What went wrong.
    pub what: String,
}

impl fmt::Display for WasmDecodeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "at byte {}: {}", self.offset, self.what)
    }
}

fn err<T>(offset: usize, what: impl Into<String>) -> Result<T, WasmDecodeError> {
    Err(WasmDecodeError {
        offset,
        what: what.into(),
    })
}

/// A cursor over a byte slice that fails closed on every read.
struct Cur<'a> {
    bytes: &'a [u8],
    /// Offset of `bytes[0]` within the whole module, so errors are absolute.
    base: usize,
    at: usize,
}

impl<'a> Cur<'a> {
    fn new(bytes: &'a [u8], base: usize) -> Self {
        Self { bytes, base, at: 0 }
    }
    fn abs(&self) -> usize {
        self.base + self.at
    }
    fn done(&self) -> bool {
        self.at >= self.bytes.len()
    }
    fn remaining(&self) -> usize {
        self.bytes.len() - self.at
    }
    fn byte(&mut self) -> Result<u8, WasmDecodeError> {
        let Some(&b) = self.bytes.get(self.at) else {
            return err(self.abs(), "unexpected end of input");
        };
        self.at += 1;
        Ok(b)
    }
    fn take(&mut self, n: usize) -> Result<&'a [u8], WasmDecodeError> {
        if self.remaining() < n {
            return err(
                self.abs(),
                format!("need {n} byte(s), only {} left", self.remaining()),
            );
        }
        let s = &self.bytes[self.at..self.at + n];
        self.at += n;
        Ok(s)
    }
    fn u32(&mut self) -> Result<u32, WasmDecodeError> {
        match spec_decode_unsigned(&self.bytes[self.at..], 32) {
            Ok((v, used)) => {
                self.at += used;
                Ok(v as u32)
            }
            Err(e) => err(self.abs(), format!("u32 LEB128: {e}")),
        }
    }
    fn s32(&mut self) -> Result<i32, WasmDecodeError> {
        match spec_decode_signed(&self.bytes[self.at..], 32) {
            Ok((v, used)) => {
                self.at += used;
                Ok(v as i32)
            }
            Err(e) => err(self.abs(), format!("s32 LEB128: {e}")),
        }
    }
    fn s64(&mut self) -> Result<i64, WasmDecodeError> {
        match spec_decode_signed(&self.bytes[self.at..], 64) {
            Ok((v, used)) => {
                self.at += used;
                Ok(v)
            }
            Err(e) => err(self.abs(), format!("s64 LEB128: {e}")),
        }
    }
    fn s33(&mut self) -> Result<i64, WasmDecodeError> {
        match spec_decode_signed(&self.bytes[self.at..], 33) {
            Ok((v, used)) => {
                self.at += used;
                Ok(v)
            }
            Err(e) => err(self.abs(), format!("s33 LEB128: {e}")),
        }
    }
    fn name(&mut self) -> Result<String, WasmDecodeError> {
        let n = self.u32()? as usize;
        let start = self.abs();
        let raw = self.take(n)?;
        String::from_utf8(raw.to_vec()).map_err(|_| WasmDecodeError {
            offset: start,
            what: "wasm `name` is not valid UTF-8".to_string(),
        })
    }
    fn valtype(&mut self) -> Result<ValType, WasmDecodeError> {
        let at = self.abs();
        match self.byte()? {
            0x7f => Ok(ValType::I32),
            0x7e => Ok(ValType::I64),
            0x7d => Ok(ValType::F32),
            0x7c => Ok(ValType::F64),
            other => err(at, format!("0x{other:02x} is not a numeric valtype")),
        }
    }
    fn limits(&mut self) -> Result<Limits, WasmDecodeError> {
        let at = self.abs();
        let flag = self.byte()?;
        match flag {
            0x00 => Ok(Limits {
                flag,
                min: u64::from(self.u32()?),
                max: None,
            }),
            0x01 => {
                let min = u64::from(self.u32()?);
                let max = u64::from(self.u32()?);
                Ok(Limits {
                    flag,
                    min,
                    max: Some(max),
                })
            }
            other => err(
                at,
                format!(
                    "limits flag 0x{other:02x} is outside the wasm32 MVP set {{0x00, 0x01}} — \
                     0x02/0x03 are the shared-memory (threads) forms and 0x04/0x05 the MEMORY64 \
                     forms, and the wasm32 lane must emit neither"
                ),
            ),
        }
    }
}

/// A numeric value type.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ValType {
    /// `i32` (0x7f).
    I32,
    /// `i64` (0x7e).
    I64,
    /// `f32` (0x7d).
    F32,
    /// `f64` (0x7c).
    F64,
}

/// A decoded `functype`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FuncTypeShape {
    /// Parameter types, in order.
    pub params: Vec<ValType>,
    /// Result types, in order.
    pub results: Vec<ValType>,
}

/// A decoded `limits`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Limits {
    /// The raw flag byte, kept so the target-conformance obligation can name it.
    pub flag: u8,
    /// Minimum, in pages for a memory / elements for a table.
    pub min: u64,
    /// Maximum, if the flag declares one.
    pub max: Option<u64>,
}

/// A decoded import.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ImportEntry {
    /// Two-level name: the module.
    pub module: String,
    /// Two-level name: the entity.
    pub name: String,
    /// What is being imported.
    pub desc: ImportDesc,
}

/// The descriptor half of an import.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ImportDesc {
    /// A function of the named type index.
    Func(u32),
    /// A table.
    Table {
        /// Element-type byte (0x70 funcref).
        elem_type: u8,
        /// Declared limits.
        limits: Limits,
    },
    /// A linear memory.
    Memory(Limits),
    /// A global.
    Global {
        /// Value type.
        ty: ValType,
        /// Mutability.
        mutable: bool,
    },
}

/// A decoded defined global.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GlobalDefShape {
    /// Value type.
    pub ty: ValType,
    /// Mutability.
    pub mutable: bool,
    /// The constant initializer expression, decoded.
    pub init: Vec<Instr>,
}

/// A decoded export.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExportEntry {
    /// Export name.
    pub name: String,
    /// Kind byte: 0 func, 1 table, 2 mem, 3 global.
    pub kind: u8,
    /// Index into the kind's index space.
    pub index: u32,
}

/// A decoded element segment (the active, table-0, funcidx-vector form).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ElemSegment {
    /// Segment flags (0 = active, table 0, funcidx vector).
    pub flags: u32,
    /// The offset constant expression, decoded.
    pub offset: Vec<Instr>,
    /// The function indices the segment installs, in order.
    pub func_indices: Vec<u32>,
}

/// A decoded code entry.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CodeBody {
    /// Run-length local declarations `(count, type)`.
    pub locals: Vec<(u32, ValType)>,
    /// The instruction stream, decoded, INCLUDING the terminating `end`.
    pub instrs: Vec<Instr>,
}

impl CodeBody {
    /// Total number of declared local slots (not counting parameters).
    pub fn local_slot_count(&self) -> u64 {
        self.locals.iter().map(|(c, _)| u64::from(*c)).sum()
    }
}

/// A decoded active data segment.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DataSegmentShape {
    /// Segment kind (0 = active, memory 0).
    pub kind: u32,
    /// The offset constant expression, decoded.
    pub offset: Vec<Instr>,
    /// The bytes the segment writes.
    pub bytes: Vec<u8>,
}

/// One decoded instruction: where it starts, its opcode byte, and its immediate.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Instr {
    /// Offset of the opcode byte, relative to the expression's first byte.
    pub offset: usize,
    /// The opcode byte (or the 0xfc prefix for the saturating conversions).
    pub opcode: u8,
    /// The decoded immediate.
    pub imm: Imm,
    /// Block nesting depth at this instruction (0 at the function's top level;
    /// a `block`/`loop`/`if` reports the depth it OPENS from, and its body is
    /// one deeper).
    pub depth: u32,
}

/// A decoded instruction immediate.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Imm {
    /// No immediate.
    None,
    /// A `blocktype`: the raw byte for the void/valtype forms, or a positive
    /// type index for the s33 form.
    BlockType(i64),
    /// A branch label index.
    Label(u32),
    /// `br_table`: the label vector plus the default label.
    BrTable {
        /// Case labels, in order.
        labels: Vec<u32>,
        /// The default label.
        default: u32,
    },
    /// A function index (`call`).
    Func(u32),
    /// `call_indirect`: the signature type index and the table index.
    CallIndirect {
        /// Signature type index.
        type_idx: u32,
        /// Table index (0 in the MVP).
        table_idx: u32,
    },
    /// A local slot index.
    Local(u32),
    /// A global index.
    Global(u32),
    /// A `memarg`: the alignment EXPONENT and the static byte offset.
    MemArg {
        /// log2 of the claimed alignment in bytes.
        align_exp: u32,
        /// Static byte offset added to the dynamic address.
        offset: u32,
    },
    /// The memory index byte carried by `memory.size` / `memory.grow`.
    MemIdx(u8),
    /// An `i32.const` immediate, decoded.
    I32(i32),
    /// An `i64.const` immediate, decoded.
    I64(i64),
    /// The RAW 4 little-endian bytes of an `f32.const`.
    F32([u8; 4]),
    /// The RAW 8 little-endian bytes of an `f64.const`.
    F64([u8; 8]),
    /// The sub-index after a 0xfc prefix (the saturating conversions, 0..=7).
    FcSub(u32),
}

/// Every decoded section, plus the raw ids in EMISSION ORDER.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct DecodedModule {
    /// The binary-format version word.
    pub version: u32,
    /// Section ids in the order they appeared, with their body lengths.
    pub section_ids: Vec<(u8, usize)>,
    /// Section 1.
    pub types: Vec<FuncTypeShape>,
    /// Section 2, in appearance order (which IS index order within a kind).
    pub imports: Vec<ImportEntry>,
    /// Section 3: the type index of each DEFINED function, in order.
    pub func_type_idx: Vec<u32>,
    /// Section 4.
    pub tables: Vec<(u8, Limits)>,
    /// Section 5.
    pub memories: Vec<Limits>,
    /// Section 6.
    pub globals: Vec<GlobalDefShape>,
    /// Section 7.
    pub exports: Vec<ExportEntry>,
    /// Section 9.
    pub elements: Vec<ElemSegment>,
    /// Section 10, parallel to [`DecodedModule::func_type_idx`].
    pub code: Vec<CodeBody>,
    /// Section 11.
    pub data: Vec<DataSegmentShape>,
}

impl DecodedModule {
    /// Number of IMPORTED functions — the base of the defined-function index
    /// space, computed from the decoded import section, never from a caller.
    pub fn func_import_count(&self) -> u32 {
        self.imports
            .iter()
            .filter(|i| matches!(i.desc, ImportDesc::Func(_)))
            .count() as u32
    }
    /// Number of IMPORTED globals.
    pub fn global_import_count(&self) -> u32 {
        self.imports
            .iter()
            .filter(|i| matches!(i.desc, ImportDesc::Global { .. }))
            .count() as u32
    }
    /// Number of IMPORTED memories.
    pub fn memory_import_count(&self) -> u32 {
        self.imports
            .iter()
            .filter(|i| matches!(i.desc, ImportDesc::Memory(_)))
            .count() as u32
    }
    /// Number of IMPORTED tables.
    pub fn table_import_count(&self) -> u32 {
        self.imports
            .iter()
            .filter(|i| matches!(i.desc, ImportDesc::Table { .. }))
            .count() as u32
    }
    /// The whole function index space: imports first, definitions after.
    pub fn total_funcs(&self) -> u32 {
        self.func_import_count() + self.func_type_idx.len() as u32
    }
    /// The whole global index space.
    pub fn total_globals(&self) -> u32 {
        self.global_import_count() + self.globals.len() as u32
    }
    /// The whole memory index space.
    pub fn total_memories(&self) -> u32 {
        self.memory_import_count() + self.memories.len() as u32
    }
    /// The whole table index space.
    pub fn total_tables(&self) -> u32 {
        self.table_import_count() + self.tables.len() as u32
    }
    /// Map an exported function's NAME to its function index.
    pub fn exported_funcs(&self) -> HashMap<&str, u32> {
        self.exports
            .iter()
            .filter(|e| e.kind == 0)
            .map(|e| (e.name.as_str(), e.index))
            .collect()
    }
    /// The defined function at function index `idx`, as an index into
    /// [`DecodedModule::code`]. `None` for an imported index or one past the end.
    pub fn defined_ordinal(&self, idx: u32) -> Option<usize> {
        let base = self.func_import_count();
        if idx < base {
            return None;
        }
        let ord = (idx - base) as usize;
        (ord < self.code.len()).then_some(ord)
    }
    /// Every instruction of every defined body, flattened, tagged with the
    /// defining body's ordinal.
    pub fn all_instrs(&self) -> Vec<(usize, &Instr)> {
        self.code
            .iter()
            .enumerate()
            .flat_map(|(i, b)| b.instrs.iter().map(move |ins| (i, ins)))
            .collect()
    }
}

/// Decode a whole `.wasm` module from its bytes.
///
/// Fails closed on anything the wasm32 backend is not supposed to emit — an
/// unknown opcode, a memory64 limits flag, a bulk-memory sub-index, a SIMD
/// prefix, a section body that is not consumed EXACTLY by its own grammar. That
/// last one is the load-bearing check: a vector count that disagrees with the
/// items actually present shows up as leftover or missing bytes, not as a
/// silently truncated list.
pub fn decode_module(bytes: &[u8]) -> Result<DecodedModule, WasmDecodeError> {
    if bytes.len() < 8 {
        return err(0, "shorter than the 8-byte preamble");
    }
    if &bytes[0..4] != b"\0asm" {
        return err(0, format!("magic is {:02x?}, not \\0asm", &bytes[0..4]));
    }
    let version = u32::from_le_bytes([bytes[4], bytes[5], bytes[6], bytes[7]]);

    let mut m = DecodedModule {
        version,
        ..DecodedModule::default()
    };

    let mut at = 8usize;
    while at < bytes.len() {
        let id_at = at;
        let id = bytes[at];
        at += 1;
        let (size, used) = spec_decode_unsigned(&bytes[at..], 32)
            .map_err(|e| WasmDecodeError {
                offset: at,
                what: format!("section {id} length LEB128: {e}"),
            })
            .map(|(v, u)| (v as usize, u))?;
        at += used;
        if bytes.len() - at < size {
            return err(
                at,
                format!(
                    "section {id} declares {size} body byte(s) but only {} remain",
                    bytes.len() - at
                ),
            );
        }
        let body = &bytes[at..at + size];
        let base = at;
        at += size;
        m.section_ids.push((id, size));

        let mut c = Cur::new(body, base);
        match id {
            0 => {
                // Custom section: the backend emits none. Fail CLOSED rather
                // than skip — an unexpected custom section is unexamined bytes,
                // and unexamined bytes are exactly what this family exists to
                // refuse.
                return err(
                    id_at,
                    "custom section (id 0) — the wasm32 backend emits none, so its contents are outside every obligation here; fail closed rather than skip unexamined bytes",
                );
            }
            1 => {
                let n = c.u32()?;
                for _ in 0..n {
                    let tag_at = c.abs();
                    let tag = c.byte()?;
                    if tag != 0x60 {
                        return err(tag_at, format!("functype tag is 0x{tag:02x}, not 0x60"));
                    }
                    let np = c.u32()?;
                    let mut params = Vec::with_capacity(np as usize);
                    for _ in 0..np {
                        params.push(c.valtype()?);
                    }
                    let nr = c.u32()?;
                    let mut results = Vec::with_capacity(nr as usize);
                    for _ in 0..nr {
                        results.push(c.valtype()?);
                    }
                    m.types.push(FuncTypeShape { params, results });
                }
            }
            2 => {
                let n = c.u32()?;
                for _ in 0..n {
                    let module = c.name()?;
                    let name = c.name()?;
                    let kind_at = c.abs();
                    let desc = match c.byte()? {
                        0x00 => ImportDesc::Func(c.u32()?),
                        0x01 => {
                            let et_at = c.abs();
                            let elem_type = c.byte()?;
                            if elem_type != 0x70 {
                                return err(
                                    et_at,
                                    format!("table elemtype 0x{elem_type:02x} is not funcref"),
                                );
                            }
                            ImportDesc::Table {
                                elem_type,
                                limits: c.limits()?,
                            }
                        }
                        0x02 => ImportDesc::Memory(c.limits()?),
                        0x03 => {
                            let ty = c.valtype()?;
                            let mut_at = c.abs();
                            let mutable = match c.byte()? {
                                0x00 => false,
                                0x01 => true,
                                o => return err(mut_at, format!("global mut byte 0x{o:02x}")),
                            };
                            ImportDesc::Global { ty, mutable }
                        }
                        o => return err(kind_at, format!("importdesc kind 0x{o:02x}")),
                    };
                    m.imports.push(ImportEntry { module, name, desc });
                }
            }
            3 => {
                let n = c.u32()?;
                for _ in 0..n {
                    m.func_type_idx.push(c.u32()?);
                }
            }
            4 => {
                let n = c.u32()?;
                for _ in 0..n {
                    let et_at = c.abs();
                    let elem_type = c.byte()?;
                    if elem_type != 0x70 {
                        return err(
                            et_at,
                            format!("table elemtype 0x{elem_type:02x} is not funcref"),
                        );
                    }
                    m.tables.push((elem_type, c.limits()?));
                }
            }
            5 => {
                let n = c.u32()?;
                for _ in 0..n {
                    m.memories.push(c.limits()?);
                }
            }
            6 => {
                let n = c.u32()?;
                for _ in 0..n {
                    let ty = c.valtype()?;
                    let mut_at = c.abs();
                    let mutable = match c.byte()? {
                        0x00 => false,
                        0x01 => true,
                        o => return err(mut_at, format!("global mut byte 0x{o:02x}")),
                    };
                    let init = decode_expr_at(&mut c)?;
                    m.globals.push(GlobalDefShape { ty, mutable, init });
                }
            }
            7 => {
                let n = c.u32()?;
                for _ in 0..n {
                    let name = c.name()?;
                    let kind_at = c.abs();
                    let kind = c.byte()?;
                    if kind > 0x03 {
                        return err(kind_at, format!("export kind 0x{kind:02x}"));
                    }
                    let index = c.u32()?;
                    m.exports.push(ExportEntry { name, kind, index });
                }
            }
            8 => {
                return err(
                    id_at,
                    "start section (id 8) — the wasm32 backend emits none; nothing here checks a \
                     start function's type or effects, so fail closed",
                );
            }
            9 => {
                let n = c.u32()?;
                for _ in 0..n {
                    let flags_at = c.abs();
                    let flags = c.u32()?;
                    if flags != 0 {
                        return err(
                            flags_at,
                            format!(
                                "element segment flags {flags} — only the active/table-0/funcidx \
                                 form (0) is emitted by this backend"
                            ),
                        );
                    }
                    let offset = decode_expr_at(&mut c)?;
                    let cnt = c.u32()?;
                    let mut func_indices = Vec::with_capacity(cnt as usize);
                    for _ in 0..cnt {
                        func_indices.push(c.u32()?);
                    }
                    m.elements.push(ElemSegment {
                        flags,
                        offset,
                        func_indices,
                    });
                }
            }
            10 => {
                let n = c.u32()?;
                for _ in 0..n {
                    let size = c.u32()? as usize;
                    let entry_base = c.abs();
                    let entry = c.take(size)?;
                    let mut e = Cur::new(entry, entry_base);
                    let runs = e.u32()?;
                    let mut locals = Vec::with_capacity(runs as usize);
                    for _ in 0..runs {
                        let count = e.u32()?;
                        locals.push((count, e.valtype()?));
                    }
                    let instrs = decode_expr_at(&mut e)?;
                    if !e.done() {
                        return err(
                            e.abs(),
                            format!(
                                "code entry has {} byte(s) after its terminating `end` — the \
                                 length prefix does not frame the body",
                                e.remaining()
                            ),
                        );
                    }
                    m.code.push(CodeBody { locals, instrs });
                }
            }
            11 => {
                let n = c.u32()?;
                for _ in 0..n {
                    let kind_at = c.abs();
                    let kind = c.u32()?;
                    if kind != 0 {
                        return err(
                            kind_at,
                            format!(
                                "data segment kind {kind} — only the ACTIVE memory-0 form (0) is \
                                 emitted by this backend"
                            ),
                        );
                    }
                    let offset = decode_expr_at(&mut c)?;
                    let len = c.u32()? as usize;
                    let bytes = c.take(len)?.to_vec();
                    m.data.push(DataSegmentShape {
                        kind,
                        offset,
                        bytes,
                    });
                }
            }
            12 => {
                return err(
                    id_at,
                    "datacount section (id 12) — it is the ONE section the spec places out of id \
                     order (before code, id 10), and it exists only for the bulk-memory \
                     instructions this backend does not emit. Its presence would invalidate the \
                     strictly-increasing-id obligation, so fail closed",
                );
            }
            other => return err(id_at, format!("unknown section id {other}")),
        }
        if !c.done() {
            return err(
                c.abs(),
                format!(
                    "section {id} has {} byte(s) its own grammar did not consume — a vector count \
                     and its contents disagree",
                    c.remaining()
                ),
            );
        }
    }
    Ok(m)
}

/// Decode an expression (instruction stream) up to and INCLUDING the `end` that
/// closes the outermost level, advancing the cursor past it.
fn decode_expr_at(c: &mut Cur<'_>) -> Result<Vec<Instr>, WasmDecodeError> {
    let mut out = Vec::new();
    let mut depth: u32 = 0;
    let expr_base = c.at;
    loop {
        let off = c.at - expr_base;
        let at = c.abs();
        let opcode = c.byte()?;
        let imm = match opcode {
            // --- control ---
            0x00 | 0x01 | 0x05 | 0x0f | 0x1a | 0x1b => Imm::None, // unreachable/nop/else/return/drop/select
            0x02 | 0x03 | 0x04 => {
                let bt = decode_blocktype(c)?;
                depth += 1;
                Imm::BlockType(bt)
            }
            0x0b => {
                // `end`: closes one level, or the whole expression at depth 0.
                if depth == 0 {
                    out.push(Instr {
                        offset: off,
                        opcode,
                        imm: Imm::None,
                        depth: 0,
                    });
                    return Ok(out);
                }
                depth -= 1;
                Imm::None
            }
            0x0c | 0x0d => Imm::Label(c.u32()?),
            0x0e => {
                let n = c.u32()?;
                let mut labels = Vec::with_capacity(n as usize);
                for _ in 0..n {
                    labels.push(c.u32()?);
                }
                Imm::BrTable {
                    labels,
                    default: c.u32()?,
                }
            }
            0x10 => Imm::Func(c.u32()?),
            0x11 => {
                let type_idx = c.u32()?;
                let table_idx = c.u32()?;
                Imm::CallIndirect {
                    type_idx,
                    table_idx,
                }
            }
            // --- variables ---
            0x20..=0x22 => Imm::Local(c.u32()?),
            0x23 | 0x24 => Imm::Global(c.u32()?),
            // --- linear memory ---
            0x28..=0x3e => {
                let align_exp = c.u32()?;
                let offset = c.u32()?;
                Imm::MemArg { align_exp, offset }
            }
            0x3f | 0x40 => Imm::MemIdx(c.byte()?),
            // --- constants ---
            0x41 => Imm::I32(c.s32()?),
            0x42 => Imm::I64(c.s64()?),
            0x43 => {
                let b = c.take(4)?;
                Imm::F32([b[0], b[1], b[2], b[3]])
            }
            0x44 => {
                let b = c.take(8)?;
                Imm::F64([b[0], b[1], b[2], b[3], b[4], b[5], b[6], b[7]])
            }
            // --- numeric: the whole 0x45..=0xc4 block takes no immediate ---
            0x45..=0xc4 => Imm::None,
            // --- 0xfc prefix: only the saturating conversions are decodable ---
            0xfc => {
                let sub_at = c.abs();
                let sub = c.u32()?;
                if sub > 7 {
                    return err(
                        sub_at,
                        format!(
                            "0xfc sub-index {sub} is a BULK-MEMORY instruction \
                             (memory.init/data.drop/memory.copy/memory.fill); the wasm32 backend \
                             does not emit those and nothing here decodes their data-index \
                             immediates, so fail closed"
                        ),
                    );
                }
                Imm::FcSub(sub)
            }
            other => {
                return err(
                    at,
                    format!(
                        "opcode 0x{other:02x} is outside the decodable emitted surface (control \
                         0x00..0x1b, variables 0x20..0x24, memory 0x28..0x40, constants \
                         0x41..0x44, numeric 0x45..0xc4, 0xfc trunc_sat). Reference types \
                         (0xd0..0xd2) and SIMD (0xfd) are NOT emitted by this backend; crediting a \
                         module containing one would be crediting bytes nothing examined"
                    ),
                );
            }
        };
        out.push(Instr {
            offset: off,
            opcode,
            imm,
            depth: if matches!(opcode, 0x02 | 0x03 | 0x04) {
                depth - 1
            } else {
                depth
            },
        });
    }
}

fn decode_blocktype(c: &mut Cur<'_>) -> Result<i64, WasmDecodeError> {
    // Peek: 0x40 is the void form, 0x7c..=0x7f the single-valtype forms, and
    // anything else is a NON-NEGATIVE s33 type index.
    let Some(&b) = c.bytes.get(c.at) else {
        return err(c.abs(), "unexpected end of input in blocktype");
    };
    if b == 0x40 || (0x7c..=0x7f).contains(&b) {
        c.at += 1;
        return Ok(i64::from(b));
    }
    let at = c.abs();
    let v = c.s33()?;
    if v < 0 {
        return err(at, format!("blocktype s33 index {v} is negative"));
    }
    Ok(v)
}

// ===========================================================================
// (4b) The module-level indexing / encoding obligations
// ===========================================================================

const F4: EncodingFamily = EncodingFamily::ModuleIndexing;

fn check(
    family: EncodingFamily,
    name: String,
    ok: bool,
    why: impl FnOnce() -> String,
) -> EncodingObligation {
    if ok {
        EncodingObligation::holds(family, name)
    } else {
        EncodingObligation::refuted(family, name, why())
    }
}

/// [`check`] for a row that QUANTIFIES over a set of constructs, with the size
/// of that set passed in.
///
/// THE RULE, applied uniformly across this family: **a row is credited only
/// when its domain is non-empty.** `∀ x ∈ ∅. P(x)` is true of every module ever
/// compiled, so crediting it counts the corpus's SILENCE as evidence. A
/// `() -> i32 { ret -1 }` module has no calls, no globals, no branches, no
/// memory access and no imports; it must earn NOTHING for the rows about them,
/// and `Outcome::NotApplicable` is the vocabulary this module already uses for
/// exactly that (see the element-segment and data-segment rows).
///
/// The rule separates two kinds of row and only constrains the first:
///
/// * QUANTIFIED — `∀ x ∈ S. P(x)`. Credited iff `S` is non-empty. Every such
///   row in this family goes through this function.
/// * RELATIONAL — an equality or bound between two quantities decoded
///   INDEPENDENTLY from the bytes (the code section's body count against the
///   function section's declared count; the version word; the at-most-one-memory
///   bound). These are total statements about the module rather than about a set
///   of instances, so they stay credited on every module that decodes, and they
///   use [`check`] directly.
fn check_over(
    family: EncodingFamily,
    domain: usize,
    name: String,
    absent: impl Into<String>,
    ok: bool,
    why: impl FnOnce() -> String,
) -> EncodingObligation {
    if domain == 0 {
        return EncodingObligation::not_applicable(family, name, absent);
    }
    check(family, name, ok, why)
}

/// Every FAMILY-(4) obligation over one emitted module's BYTES.
///
/// The module is decoded first; a decode failure collapses the whole family to
/// a single refutation naming the offset, because an undecodable module is one
/// about which nothing can be claimed.
pub fn module_indexing_obligations(bytes: &[u8]) -> Vec<EncodingObligation> {
    let m = match decode_module(bytes) {
        Ok(m) => m,
        Err(e) => {
            return vec![EncodingObligation::refuted(
                F4,
                "the emitted module decodes under the spec binary grammar",
                format!("{e}"),
            )];
        }
    };
    let mut out = vec![EncodingObligation::holds(
        F4,
        format!(
            "the emitted module decodes under the spec binary grammar ({} section(s), every \
             section body consumed exactly)",
            m.section_ids.len()
        ),
    )];

    // --- preamble ---
    out.push(check(
        F4,
        format!("binary-format version word is 1 (got {})", m.version),
        m.version == 1,
        || format!("version {} is not the MVP version 1", m.version),
    ));

    // --- section order + uniqueness ---
    let ids: Vec<u8> = m.section_ids.iter().map(|(i, _)| *i).collect();
    let strictly_increasing = ids.windows(2).all(|w| w[0] < w[1]);
    out.push(check(
        F4,
        format!("section ids are STRICTLY increasing (order {ids:?})"),
        strictly_increasing,
        || {
            format!(
                "section ids {ids:?} are not strictly increasing — a repeated or out-of-order \
                 section. (The decoder already fail-closes on id 12, the one section the spec \
                 places out of id order.)"
            )
        },
    ));

    // --- vector counts vs. parallel sections ---
    out.push(check(
        F4,
        format!(
            "the code section has exactly one body per declared function ({} function(s))",
            m.func_type_idx.len()
        ),
        m.code.len() == m.func_type_idx.len(),
        || {
            format!(
                "function section declares {} function(s) but the code section carries {} body(ies)",
                m.func_type_idx.len(),
                m.code.len()
            )
        },
    ));

    // --- every declared type index resolves ---
    let n_types = m.types.len() as u32;
    let bad_func_ty: Vec<String> = m
        .func_type_idx
        .iter()
        .enumerate()
        .filter(|(_, t)| **t >= n_types)
        .map(|(i, t)| format!("defined function {i} names type {t}"))
        .collect();
    out.push(check_over(
        F4,
        m.func_type_idx.len(),
        format!(
            "every DEFINED function's type index resolves (< {n_types} type(s)) — over {} defined \
             function(s)",
            m.func_type_idx.len()
        ),
        "this module defines no function",
        bad_func_ty.is_empty(),
        || bad_func_ty.join("; "),
    ));

    let bad_import_ty: Vec<String> = m
        .imports
        .iter()
        .enumerate()
        .filter_map(|(i, imp)| match imp.desc {
            ImportDesc::Func(t) if t >= n_types => Some(format!(
                "import {i} `{}.{}` names type {t}",
                imp.module, imp.name
            )),
            _ => None,
        })
        .collect();
    let n_fimp = m.func_import_count();
    out.push(check_over(
        F4,
        n_fimp as usize,
        format!(
            "every IMPORTED function's type index resolves (< {n_types} type(s)) — over {n_fimp} \
             function import(s)"
        ),
        "this module imports no function",
        bad_import_ty.is_empty(),
        || bad_import_ty.join("; "),
    ));

    // --- the import shift: imports own the LOW indices, definitions follow ---
    //
    // THERE IS NO SINGLE-MODULE PARTITION ROW HERE, and the absence is
    // deliberate. A predicate of the shape
    //
    //     total_funcs() == func_import_count() + func_type_idx.len()
    //
    // is not evidence: [`DecodedModule::total_funcs`] is DEFINED as exactly that
    // sum, so it compares a value with its own definition, and no module —
    // correct or miscompiled — can refute it. The imports-then-definitions
    // partition is a fact about this DECODER, not about the bytes, and one
    // decoded module offers no second, independent handle on the import base:
    // the import section is the only place the base is written down.
    //
    // What that row's NAME promised — that a forgotten import shift is caught —
    // is carried instead by two things that CAN fail:
    //
    //   * [`import_shift_obligations`], the TWO-COMPILE differential. The same
    //     trust-ir lowered closed and lowered as an island must agree on
    //     everything except a uniform +k shift of the function index space. The
    //     closed compile is a genuinely independent source side, which is the
    //     one thing a forgotten shift cannot forge, and
    //     `tests/wasm_encoding_gate.rs::the_forgotten_import_shift_is_refuted`
    //     exhibits it refuting the exact silent miscompile (a byte-length
    //     preserving `call k` -> `call k-imports` rewrite that still decodes,
    //     still type-checks, and runs into the host). That test also asserts the
    //     other half: the single-module obligations here are BLIND to it.
    //   * the export-range row below, the one single-module SIGNATURE a
    //     forgotten shift can leave — and only on a module that has function
    //     imports at all, which is why it is not-applicable otherwise.
    //
    // Every DEFINED-function export must land in the DEFINED half. A forgotten
    // import shift shows up here as an export index below the import base.
    let total_f = m.total_funcs();
    let n_func_exports = m.exports.iter().filter(|e| e.kind == 0).count();
    let low_exports: Vec<String> = m
        .exports
        .iter()
        .filter(|e| e.kind == 0 && e.index < n_fimp)
        .map(|e| {
            format!(
                "`{}` exports function {} (< import base {n_fimp})",
                e.name, e.index
            )
        })
        .collect();
    out.push(check_over(
        F4,
        if n_fimp == 0 { 0 } else { n_func_exports },
        format!(
            "no exported function index falls inside the IMPORT range [0,{n_fimp}) — an export of \
             a host import would be the forgotten-shift signature ({n_func_exports} function \
             export(s))"
        ),
        if n_fimp == 0 {
            "this module imports no function, so the IMPORT range is empty and no export index \
             can fall inside it — the forgotten-shift signature this row watches for cannot \
             exist here. On a closed module the shift obligation is the two-compile differential's \
             alone"
                .to_string()
        } else {
            format!(
                "this module exports no function, so there is nothing to place ({n_fimp} \
                     function import(s) declared)"
            )
        },
        low_exports.is_empty(),
        || low_exports.join("; "),
    ));

    // --- every index in every emitted body resolves in its space ---
    let n_glob = m.total_globals();
    let n_glob_imp = m.global_import_count();
    let n_mem = m.total_memories();
    let n_tab = m.total_tables();

    let mut bad_calls = Vec::new();
    let mut bad_indirect = Vec::new();
    let mut bad_globals = Vec::new();
    let mut bad_locals = Vec::new();
    let mut bad_labels = Vec::new();
    let mut bad_memidx = Vec::new();
    let mut bad_memaccess = Vec::new();
    // The DOMAIN of each row below, counted alongside its defects. An empty
    // domain means the module contains none of the construct the row speaks
    // about, and the row reports not-applicable rather than banking the
    // module's silence as credit — see [`check_over`].
    let mut n_calls = 0usize;
    let mut n_indirect = 0usize;
    let mut n_global_refs = 0usize;
    let mut n_local_refs = 0usize;
    let mut n_branches = 0usize;
    let mut n_mem_ops = 0usize;
    for (ord, body) in m.code.iter().enumerate() {
        // A local index addresses parameters first, then declared locals.
        let params = m
            .func_type_idx
            .get(ord)
            .and_then(|t| m.types.get(*t as usize))
            .map(|t| t.params.len() as u64)
            .unwrap_or(0);
        let slots = params + body.local_slot_count();
        for ins in &body.instrs {
            match &ins.imm {
                Imm::Func(f) => {
                    n_calls += 1;
                    if *f >= total_f {
                        bad_calls
                            .push(format!("body {ord}: `call {f}` with {total_f} function(s)"));
                    }
                }
                Imm::CallIndirect {
                    type_idx,
                    table_idx,
                } => {
                    n_indirect += 1;
                    if *type_idx >= n_types {
                        bad_indirect.push(format!(
                            "body {ord}: `call_indirect` names type {type_idx} with {n_types} type(s)"
                        ));
                    }
                    if *table_idx >= n_tab {
                        bad_indirect.push(format!(
                            "body {ord}: `call_indirect` names table {table_idx} with {n_tab} table(s)"
                        ));
                    }
                }
                Imm::Global(g) => {
                    n_global_refs += 1;
                    if *g >= n_glob {
                        bad_globals.push(format!("body {ord}: global {g} with {n_glob} global(s)"));
                    }
                }
                Imm::Local(l) => {
                    n_local_refs += 1;
                    if u64::from(*l) >= slots {
                        bad_locals.push(format!(
                            "body {ord}: local {l} with {params} param(s) + {} declared local(s)",
                            body.local_slot_count()
                        ));
                    }
                }
                Imm::Label(l) => {
                    n_branches += 1;
                    if *l > ins.depth {
                        bad_labels.push(format!(
                            "body {ord}: `br {l}` at nesting depth {} — the label is outside every \
                             enclosing block",
                            ins.depth
                        ));
                    }
                }
                Imm::BrTable { labels, default } => {
                    n_branches += 1;
                    for l in labels.iter().chain(std::iter::once(default)) {
                        if *l > ins.depth {
                            bad_labels.push(format!(
                                "body {ord}: `br_table` label {l} at nesting depth {}",
                                ins.depth
                            ));
                        }
                    }
                }
                Imm::MemIdx(i) => {
                    n_mem_ops += 1;
                    if *i != 0 {
                        bad_memidx
                            .push(format!("body {ord}: memory index {i} (the MVP has only 0)"));
                    }
                    if n_mem == 0 {
                        bad_memidx.push(format!(
                            "body {ord}: memory.size/grow in a module with NO memory"
                        ));
                    }
                }
                Imm::MemArg { .. } => {
                    n_mem_ops += 1;
                    if n_mem == 0 {
                        bad_memaccess.push(format!(
                            "body {ord}: a 0x{:02x} linear-memory access in a module with NO memory",
                            ins.opcode
                        ));
                    }
                }
                _ => {}
            }
        }
    }
    out.push(check_over(
        F4,
        n_calls,
        format!(
            "every `call` immediate resolves in the function index space (< {total_f}) — over \
             {n_calls} call(s)"
        ),
        "this module emits no `call`",
        bad_calls.is_empty(),
        || bad_calls.join("; "),
    ));
    out.push(check_over(
        F4,
        n_indirect,
        format!(
            "every `call_indirect` names a declared signature type and an existing table — over \
             {n_indirect} indirect call(s)"
        ),
        "this module emits no `call_indirect`",
        bad_indirect.is_empty(),
        || bad_indirect.join("; "),
    ));
    out.push(check_over(
        F4,
        n_global_refs,
        format!(
            "every global.get/global.set index resolves (< {n_glob}) — over {n_global_refs} \
             reference(s)"
        ),
        "this module's bodies reference no global",
        bad_globals.is_empty(),
        || bad_globals.join("; "),
    ));
    out.push(check_over(
        F4,
        n_local_refs,
        format!(
            "every local.get/local.set/local.tee index addresses a parameter or a declared local \
             slot — over {n_local_refs} reference(s)"
        ),
        "this module's bodies reference no local",
        bad_locals.is_empty(),
        || bad_locals.join("; "),
    ));
    out.push(check_over(
        F4,
        n_branches,
        format!(
            "every branch label is IN RANGE of its enclosing block nesting depth over \
             {n_branches} branch(es) (ENCODING well-formedness only — which block a label DENOTES \
             is the relooper family's obligation)"
        ),
        "this module's bodies contain no br / br_if / br_table",
        bad_labels.is_empty(),
        || bad_labels.join("; "),
    ));
    out.push(check_over(
        F4,
        n_mem_ops,
        format!(
            "every memory index is 0 and every access has a memory to touch ({n_mem} memory, \
             {n_mem_ops} memory operation(s))"
        ),
        "this module's bodies contain no linear-memory access and no memory.size/grow",
        bad_memidx.is_empty() && bad_memaccess.is_empty(),
        || {
            bad_memidx
                .iter()
                .chain(bad_memaccess.iter())
                .cloned()
                .collect::<Vec<_>>()
                .join("; ")
        },
    ));

    // --- exports resolve in their own index spaces, and names are unique ---
    let mut bad_exports = Vec::new();
    for e in &m.exports {
        let (space, n) = match e.kind {
            0 => ("function", total_f),
            1 => ("table", n_tab),
            2 => ("memory", n_mem),
            3 => ("global", n_glob),
            _ => ("<unknown>", 0),
        };
        if e.index >= n {
            bad_exports.push(format!(
                "`{}` exports {space} {} with {n} in that space",
                e.name, e.index
            ));
        }
    }
    out.push(check_over(
        F4,
        m.exports.len(),
        format!(
            "every export index resolves in ITS OWN index space — over {} export(s)",
            m.exports.len()
        ),
        "this module exports nothing",
        bad_exports.is_empty(),
        || bad_exports.join("; "),
    ));

    let mut names: Vec<&str> = m.exports.iter().map(|e| e.name.as_str()).collect();
    names.sort_unstable();
    let dup: Vec<&str> = names
        .windows(2)
        .filter(|w| w[0] == w[1])
        .map(|w| w[0])
        .collect();
    out.push(check_over(
        F4,
        // Uniqueness quantifies over PAIRS: fewer than two names is an empty
        // domain, and "the one name is unique" is not evidence of anything.
        names.len().saturating_sub(1),
        format!("export names are unique ({} export(s))", names.len()),
        format!(
            "this module exports {} name(s) — uniqueness quantifies over pairs, and there is no \
             pair",
            names.len()
        ),
        dup.is_empty(),
        || format!("duplicate export name(s): {dup:?}"),
    ));

    // --- the element segment covers the WHOLE function index space ---
    if m.tables.is_empty() && m.table_import_count() == 0 {
        out.push(EncodingObligation::not_applicable(
            F4,
            "the funcref element segment installs element i = function i over the WHOLE index \
             space",
            "this module declares no table, so there is no element segment to check",
        ));
    } else {
        let seg = m.elements.first();
        match seg {
            None => out.push(EncodingObligation::refuted(
                F4,
                "the funcref element segment installs element i = function i over the WHOLE index \
                 space",
                "the module declares a table but emits NO element segment — every indirect call \
                 would trap on an uninitialized element",
            )),
            Some(s) => {
                let count_ok = s.func_indices.len() as u32 == total_f;
                let identity_ok = s
                    .func_indices
                    .iter()
                    .enumerate()
                    .all(|(i, f)| *f == i as u32);
                let offset_ok = matches!(s.offset.first().map(|i| &i.imm), Some(Imm::I32(0)))
                    && s.offset.len() == 2
                    && s.offset[1].opcode == 0x0b;
                out.push(check(
                    F4,
                    format!(
                        "the funcref element segment holds exactly {total_f} entry(ies) — the \
                         WHOLE function index space, imports included"
                    ),
                    count_ok,
                    || {
                        format!(
                            "element segment holds {} entry(ies) for a {total_f}-function index \
                             space — a table sized from the DEFINED count would leave every \
                             imported index unfilled",
                            s.func_indices.len()
                        )
                    },
                ));
                out.push(check(
                    F4,
                    "element i is function i (so a function pointer IS its funcidx)".to_string(),
                    identity_ok,
                    || format!("element vector is {:?}, not the identity", s.func_indices),
                ));
                out.push(check(
                    F4,
                    "the element segment's offset expression is `i32.const 0; end`".to_string(),
                    offset_ok,
                    || format!("offset expression decodes to {:?}", s.offset),
                ));
                // The table must be large enough to hold what the segment writes.
                let declared = m.tables.first().map(|(_, l)| l.min).unwrap_or_else(|| {
                    m.imports
                        .iter()
                        .find_map(|i| match &i.desc {
                            ImportDesc::Table { limits, .. } => Some(limits.min),
                            _ => None,
                        })
                        .unwrap_or(0)
                });
                out.push(check(
                    F4,
                    format!(
                        "the table's declared minimum ({declared}) holds the whole element \
                         segment ({} entry(ies))",
                        s.func_indices.len()
                    ),
                    declared >= s.func_indices.len() as u64,
                    || {
                        format!(
                            "table min {declared} < {} element(s) — instantiation would trap",
                            s.func_indices.len()
                        )
                    },
                ));
            }
        }
        out.push(check(
            F4,
            "the module emits at most ONE element segment".to_string(),
            m.elements.len() <= 1,
            || format!("{} element segment(s)", m.elements.len()),
        ));
    }

    // --- globals: the constant-expression rule ---
    let mut bad_init = Vec::new();
    for (i, g) in m.globals.iter().enumerate() {
        // A constant expression is one const/global.get instruction then `end`.
        if g.init.len() != 2 || g.init[1].opcode != 0x0b {
            bad_init.push(format!(
                "defined global {i} initializer is {} instruction(s), not <const-expr>; end",
                g.init.len()
            ));
            continue;
        }
        match (&g.init[0].imm, g.ty) {
            (Imm::I32(_), ValType::I32) | (Imm::I64(_), ValType::I64) => {}
            (Imm::Global(src), _) => {
                if *src >= n_glob_imp {
                    bad_init.push(format!(
                        "defined global {i} initializes from `global.get {src}`, which is not an \
                         IMPORTED global (only imported immutable globals are constant \
                         expressions; imports own [0,{n_glob_imp}))"
                    ));
                } else if let Some(ImportDesc::Global { ty, mutable }) = m
                    .imports
                    .iter()
                    .filter(|imp| matches!(imp.desc, ImportDesc::Global { .. }))
                    .nth(*src as usize)
                    .map(|imp| &imp.desc)
                {
                    if *mutable {
                        bad_init.push(format!(
                            "defined global {i} reads MUTABLE imported global {src}"
                        ));
                    }
                    if *ty != g.ty {
                        bad_init.push(format!(
                            "defined global {i} is {:?} but reads {ty:?} imported global {src}",
                            g.ty
                        ));
                    }
                }
            }
            (imm, ty) => bad_init.push(format!(
                "defined global {i} of type {ty:?} has initializer {imm:?}"
            )),
        }
    }
    out.push(check_over(
        F4,
        m.globals.len(),
        format!(
            "every DEFINED global's initializer is a spec constant expression of its own type \
             ({} global(s))",
            m.globals.len()
        ),
        "this module defines no global",
        bad_init.is_empty(),
        || bad_init.join("; "),
    ));

    // --- memory: the MVP allows at most one, imported or defined ---
    out.push(check(
        F4,
        format!("the module declares AT MOST ONE linear memory (has {n_mem})"),
        n_mem <= 1,
        || format!("{n_mem} memories — multi-memory is not the wasm32 MVP this backend targets"),
    ));

    // --- data segments fit the memory they target ---
    if m.data.is_empty() {
        out.push(EncodingObligation::not_applicable(
            F4,
            "every active data segment fits the DECLARED minimum of the memory it targets",
            "this module emits no data segment",
        ));
    } else {
        let declared_min_bytes = m.memories.first().map(|l| l.min * 65536);
        let mut bad_data = Vec::new();
        for (i, d) in m.data.iter().enumerate() {
            let Some(Imm::I32(off)) = d.offset.first().map(|ins| ins.imm.clone()) else {
                bad_data.push(format!("data segment {i} has no i32.const offset"));
                continue;
            };
            let start = u64::from(off as u32);
            let end = start + d.bytes.len() as u64;
            if end > u64::from(u32::MAX) + 1 {
                bad_data.push(format!(
                    "data segment {i} runs to {end}, past the wasm32 address space"
                ));
            }
            if let Some(limit) = declared_min_bytes
                && end > limit
            {
                bad_data.push(format!(
                    "data segment {i} ends at {end}, past the {limit}-byte declared minimum of \
                     this module's OWN memory — instantiation would trap"
                ));
            }
        }
        out.push(check(
            F4,
            format!(
                "every active data segment fits the DECLARED minimum of the memory it targets \
                 ({} segment(s))",
                m.data.len()
            ),
            bad_data.is_empty(),
            || bad_data.join("; "),
        ));
    }

    out
}

/// The FAMILY-(4) IMPORT-SHIFT differential: the SAME trust-ir module compiled
/// closed and as an island must agree on everything except a uniform shift of
/// the function index space by the island's import count.
///
/// This is the obligation whose silent failure is a call landing on the wrong
/// function. The imports in the island deliberately share the callee's
/// signature, so a forgotten shift emits `call 0` — which still type-checks,
/// still validates, and still runs, into the host.
///
/// * `closed_bytes`: the module compiled with no function imports.
/// * `island_bytes`: the same trust-ir compiled with `k` function imports.
/// * `exported_names`: the trust-ir function names that must appear in both.
pub fn import_shift_obligations(
    closed_bytes: &[u8],
    island_bytes: &[u8],
    exported_names: &[&str],
) -> Vec<EncodingObligation> {
    let (closed, island) = match (decode_module(closed_bytes), decode_module(island_bytes)) {
        (Ok(a), Ok(b)) => (a, b),
        (a, b) => {
            let mut why = String::new();
            if let Err(e) = a {
                why.push_str(&format!("closed module: {e}; "));
            }
            if let Err(e) = b {
                why.push_str(&format!("island module: {e}"));
            }
            return vec![EncodingObligation::refuted(
                F4,
                "the closed/island import-shift differential",
                why,
            )];
        }
    };

    let k = island.func_import_count();
    let mut out = Vec::new();
    out.push(check(
        F4,
        format!("the closed module imports NO function (its boundary is the module); the island imports {k}"),
        closed.func_import_count() == 0 && k > 0,
        || {
            format!(
                "closed module imports {} function(s), island imports {k} — the differential needs \
                 a real shift to observe",
                closed.func_import_count()
            )
        },
    ));

    // Every named function's EXPORT index must shift by exactly k.
    let ce = closed.exported_funcs();
    let ie = island.exported_funcs();
    let mut bad = Vec::new();
    for name in exported_names {
        match (ce.get(name), ie.get(name)) {
            (Some(a), Some(b)) => {
                if *b != a + k {
                    bad.push(format!(
                        "`{name}` is function {a} closed and {b} in the island; the shift must be \
                         exactly +{k}"
                    ));
                }
            }
            (a, b) => bad.push(format!(
                "`{name}` exported as {a:?} closed / {b:?} in the island — it must be exported by \
                 both"
            )),
        }
    }
    out.push(check(
        F4,
        format!("every exported function's index shifts by EXACTLY the import count (+{k})"),
        bad.is_empty(),
        || bad.join("; "),
    ));

    // Every `call` immediate inside every defined body must shift by exactly k.
    let mut call_bad = Vec::new();
    if closed.code.len() != island.code.len() {
        call_bad.push(format!(
            "closed module has {} defined body(ies), island has {} — the same trust-ir must lower \
             to the same definitions",
            closed.code.len(),
            island.code.len()
        ));
    } else {
        for (ord, (cb, ib)) in closed.code.iter().zip(island.code.iter()).enumerate() {
            let cc: Vec<u32> = cb
                .instrs
                .iter()
                .filter_map(|i| match i.imm {
                    Imm::Func(f) => Some(f),
                    _ => None,
                })
                .collect();
            let ic: Vec<u32> = ib
                .instrs
                .iter()
                .filter_map(|i| match i.imm {
                    Imm::Func(f) => Some(f),
                    _ => None,
                })
                .collect();
            if cc.len() != ic.len() {
                call_bad.push(format!(
                    "body {ord}: {} call(s) closed vs {} in the island",
                    cc.len(),
                    ic.len()
                ));
                continue;
            }
            for (a, b) in cc.iter().zip(ic.iter()) {
                if *b != a + k {
                    call_bad.push(format!(
                        "body {ord}: `call {a}` closed became `call {b}` in the island; the \
                         shifted target is {}. `call {b}` names an IMPORT — the host — and still \
                         type-checks",
                        a + k
                    ));
                }
            }
        }
    }
    out.push(check(
        F4,
        format!(
            "every `call` immediate in every defined body shifts by EXACTLY the import count (+{k})"
        ),
        call_bad.is_empty(),
        || call_bad.join("; "),
    ));

    // And no shifted call may land in the import range.
    let island_calls = island
        .all_instrs()
        .iter()
        .filter(|(_, ins)| matches!(ins.imm, Imm::Func(_)))
        .count();
    let landed_on_import: Vec<String> = island
        .all_instrs()
        .iter()
        .filter_map(|(ord, ins)| match ins.imm {
            Imm::Func(f) if f < k => Some(format!("body {ord}: `call {f}` names host import {f}")),
            _ => None,
        })
        .collect();
    out.push(check_over(
        F4,
        island_calls,
        format!(
            "no `call` in the island's own bodies targets the IMPORT range [0,{k}) over \
             {island_calls} call(s) — this trust-ir calls only its own functions"
        ),
        "the island's bodies emit no `call`",
        landed_on_import.is_empty(),
        || landed_on_import.join("; "),
    ));

    out
}

// ===========================================================================
// (6) TargetInfo conformance
// ===========================================================================

const F6: EncodingFamily = EncodingFamily::TargetConformance;

/// The canonical wasm32 pin the compile REQUIRES, restated here independently of
/// `trust_cg_codegen::wasm::target` so the obligation has a source side of its
/// own: `(triple prefix, pointer bytes, little-endian)`.
pub const WASM32_PIN: (&str, u8, bool) = ("wasm32", 4, true);

/// Every FAMILY-(6) obligation over one emitted module's BYTES: does the module
/// actually SPEND the wasm32 pin the compile demanded?
///
/// `expected_le_images` lets a caller assert the LITTLE-ENDIAN half concretely:
/// `(data segment index, the bytes that segment must hold)`, where the caller
/// derived those bytes from the source constant independently (e.g.
/// `0x1234_5678u32.to_le_bytes()`). Endianness is otherwise INVISIBLE in a wasm
/// module — it is the engine's memory semantics, not a byte in the file — so
/// without a caller-supplied image this half honestly reports not-applicable
/// rather than claiming coverage.
pub fn target_conformance_obligations(
    bytes: &[u8],
    expected_le_images: &[(usize, &[u8])],
) -> Vec<EncodingObligation> {
    let m = match decode_module(bytes) {
        Ok(m) => m,
        Err(e) => {
            return vec![EncodingObligation::refuted(
                F6,
                "the emitted module decodes under the spec binary grammar",
                format!("{e}"),
            )];
        }
    };
    let mut out = Vec::new();

    // --- 32-bit memory: the MVP limits forms only ---
    let mut mem_flags: Vec<u8> = m.memories.iter().map(|l| l.flag).collect();
    mem_flags.extend(m.imports.iter().filter_map(|i| match &i.desc {
        ImportDesc::Memory(l) => Some(l.flag),
        _ => None,
    }));
    if mem_flags.is_empty() {
        out.push(EncodingObligation::not_applicable(
            F6,
            "every memory declares 32-BIT limits (flag 0x00/0x01), never a memory64 flag",
            "this module declares no linear memory",
        ));
    } else {
        // The decoder already fail-closes on 0x02..0x05; state the obligation
        // anyway so the audit row exists whether or not the decode reached it.
        out.push(check(
            F6,
            format!("every memory declares 32-BIT MVP limits (flags {mem_flags:02x?}) — never the memory64 forms 0x04/0x05"),
            mem_flags.iter().all(|f| *f == 0x00 || *f == 0x01),
            || format!("memory limits flags {mem_flags:02x?} include a non-wasm32 form"),
        ));
        // wasm32 pages: min must fit the 32-bit address space (2^16 pages).
        let mut over: Vec<String> = Vec::new();
        for l in m
            .memories
            .iter()
            .chain(m.imports.iter().filter_map(|i| match &i.desc {
                ImportDesc::Memory(l) => Some(l),
                _ => None,
            }))
        {
            if l.min > 65536 || l.max.is_some_and(|x| x > 65536) {
                over.push(format!("limits {l:?} exceed the 65536-page wasm32 space"));
            }
        }
        out.push(check(
            F6,
            "every memory's page limits fit the 65536-page wasm32 address space".to_string(),
            over.is_empty(),
            || over.join("; "),
        ));
    }

    // --- every offset / address expression is i32, never i64 ---
    let mut wrong_width = Vec::new();
    for (i, d) in m.data.iter().enumerate() {
        match d.offset.first().map(|ins| &ins.imm) {
            Some(Imm::I32(_)) => {}
            other => wrong_width.push(format!(
                "data segment {i}'s offset expression is {other:?} — a wasm32 active segment \
                 offsets with i32.const; an i64.const there is a memory64 module"
            )),
        }
    }
    for (i, e) in m.elements.iter().enumerate() {
        match e.offset.first().map(|ins| &ins.imm) {
            Some(Imm::I32(_)) => {}
            other => wrong_width.push(format!(
                "element segment {i}'s offset expression is {other:?}, not i32.const"
            )),
        }
    }
    if m.data.is_empty() && m.elements.is_empty() {
        out.push(EncodingObligation::not_applicable(
            F6,
            "every data / element segment offset expression is i32.const (32-BIT addressing)",
            "this module emits no data or element segment",
        ));
    } else {
        out.push(check(
            F6,
            format!(
                "every data / element segment offset expression is i32.const — 32-BIT addressing \
                 ({} data + {} element segment(s))",
                m.data.len(),
                m.elements.len()
            ),
            wrong_width.is_empty(),
            || wrong_width.join("; "),
        ));
    }

    // --- the shadow-stack pointer and any address-bearing global is i32 ---
    let mut_i32_globals = m
        .globals
        .iter()
        .filter(|g| g.mutable && g.ty == ValType::I32)
        .count();
    let mut_non_i32: Vec<String> = m
        .globals
        .iter()
        .enumerate()
        .filter(|(_, g)| g.mutable && g.ty != ValType::I32)
        .map(|(i, g)| format!("defined global {i} is a MUTABLE {:?}", g.ty))
        .collect();
    if m.globals.iter().all(|g| !g.mutable) {
        out.push(EncodingObligation::not_applicable(
            F6,
            "the shadow-stack pointer global is i32 (a wasm32 ADDRESS), never i64",
            "this module defines no mutable global (no function needs a stack frame)",
        ));
    } else {
        out.push(check(
            F6,
            format!(
                "every MUTABLE defined global is i32 — the shadow-stack pointer is a wasm32 \
                 ADDRESS ({mut_i32_globals} such global(s))"
            ),
            mut_non_i32.is_empty(),
            || mut_non_i32.join("; "),
        ));
    }
    let imported_addr_globals: Vec<String> = m
        .imports
        .iter()
        .filter_map(|i| match &i.desc {
            ImportDesc::Global { ty, mutable } if *ty != ValType::I32 => Some(format!(
                "imported global `{}.{}` is {ty:?} (mutable={mutable})",
                i.module, i.name
            )),
            _ => None,
        })
        .collect();
    if m.global_import_count() == 0 {
        out.push(EncodingObligation::not_applicable(
            F6,
            "every IMPORTED global (the host-published region base) is i32",
            "this module imports no global",
        ));
    } else {
        out.push(check(
            F6,
            "every IMPORTED global (the host-published region base) is i32".to_string(),
            imported_addr_globals.is_empty(),
            || imported_addr_globals.join("; "),
        ));
    }

    // --- memarg offsets and materialized addresses inhabit the wasm32 space ---
    let mut bad_memarg = Vec::new();
    let mut memargs = 0usize;
    for (ord, ins) in m.all_instrs() {
        if let Imm::MemArg { align_exp, offset } = ins.imm {
            memargs += 1;
            // `offset` is already a decoded u32, so it inhabits the wasm32
            // address space by construction; what CAN go wrong is an alignment
            // exponent naming an alignment wider than the access.
            if align_exp > 3 {
                bad_memarg.push(format!(
                    "body {ord}: memarg align exponent {align_exp} claims {}-byte alignment; the \
                     widest wasm32 scalar access is 8 bytes (exponent 3)",
                    1u64 << align_exp
                ));
            }
            let _ = offset;
        }
    }
    if memargs == 0 {
        out.push(EncodingObligation::not_applicable(
            F6,
            "every memarg's static offset and alignment inhabit the wasm32 scalar access space",
            "this module emits no linear-memory access",
        ));
    } else {
        out.push(check(
            F6,
            format!(
                "every memarg's alignment exponent is <= 3 (the widest wasm32 scalar access is 8 \
                 bytes) over {memargs} access(es); the static offset is a u32 by the spec's own \
                 production, so it inhabits the wasm32 address space by construction"
            ),
            bad_memarg.is_empty(),
            || bad_memarg.join("; "),
        ));
    }

    // --- LITTLE-ENDIAN static data ---
    if expected_le_images.is_empty() {
        out.push(EncodingObligation::not_applicable(
            F6,
            "static-data images are laid down LITTLE-ENDIAN",
            "no expected little-endian image was supplied; endianness is not otherwise a byte in \
             the module (it is the ENGINE's memory semantics), so claiming coverage here without \
             one would be inventing it",
        ));
    } else {
        let mut bad_le = Vec::new();
        for (idx, expected) in expected_le_images {
            match m.data.get(*idx) {
                None => bad_le.push(format!(
                    "data segment {idx} does not exist ({} segment(s) emitted)",
                    m.data.len()
                )),
                Some(d) if d.bytes.as_slice() != *expected => bad_le.push(format!(
                    "data segment {idx} holds {:02x?}, the little-endian image is {expected:02x?}",
                    d.bytes
                )),
                Some(_) => {}
            }
        }
        out.push(check(
            F6,
            format!(
                "static-data images are laid down LITTLE-ENDIAN ({} image(s) checked against the \
                 source constant's own to_le_bytes)",
                expected_le_images.len()
            ),
            bad_le.is_empty(),
            || bad_le.join("; "),
        ));
    }

    // --- pointer_size 4 ---
    //
    // THERE IS NO SUMMARY ROW HERE. The one that used to sit at this spot was
    // named "the module materializes addresses as i32 values (N i32.const(s) in
    // code, 0 i64 address expressions)" and checked only whether a DATA SEGMENT
    // offset carried an i64 immediate — so it asserted a count it never used, it
    // asserted "0 i64 address expressions" of a scan that looked at one
    // construct, and on a module with no data segment it was credited over the
    // empty set. It was also strictly subsumed: the segment-offset row above
    // demands `Some(Imm::I32(_))` POSITIVELY over the data AND element segments,
    // which implies everything the summary row's predicate could see.
    //
    // The `pointer_size = 4` half of the wasm32 pin is what the rows above
    // already establish, each over a non-empty domain or not at all:
    //
    //   * data / element segment offsets are `i32.const`, never `i64.const`;
    //   * memory limits inhabit the 65536-page wasm32 space and use an MVP
    //     (non-memory64) limits flag;
    //   * every memarg's static offset is a u32 by the spec's own production and
    //     its alignment exponent is <= 3;
    //   * every mutable defined global (the shadow-stack pointer) and every
    //     imported global (a host-published region base) is i32.
    //
    // What NO row in this family establishes, and what a summary row would have
    // been read as saying: that the i32 value an instruction pushes is USED as
    // an address by a load/store. That is an operand-typing fact about the
    // instruction stream, and it belongs to `wasm_cfg_proofs`, whose transcribed
    // §7.3.2 rule pops `i32` for the address of every 0x28..=0x3e access.

    out
}

// ===========================================================================
// Named deferrals — RED in the denominator, never a weak obligation
// ===========================================================================

/// One honestly DEFERRED encoder/byte obligation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct WasmEncodingDeferral {
    /// Display name of the construct or property.
    pub name: &'static str,
    /// The P4 family that would have to own it.
    pub family: &'static str,
    /// Why THIS family cannot honestly discharge it.
    pub reason: &'static str,
}

/// The named encoder/byte deferrals. These stay RED IN this family's
/// denominator. Each names a property a reader could reasonably assume the
/// encoding family covers; inventing a weak obligation for any of them (a
/// range-only check on a `br_table` label, say) would launder the row green
/// while refuting none of the wrong lowerings that matter.
///
/// Pinned by `tests/wasm_encoding_gate.rs`: removing one requires landing its
/// evidence; adding one is a deliberate, reviewable admission of debt.
pub const WASM_ENCODING_DEFERRALS: &[WasmEncodingDeferral] = &[
    WasmEncodingDeferral {
        name: "module VALIDATION (operand-stack typing, block arity, unreachable typing)",
        family: "the reference-validator gate (trust-cg-codegen \
                 tests/wasm_module_validation.rs), not an obligation family here",
        reason: "everything in this module is a SYNTACTIC decode derived from the binary-format \
                 grammar (spec §5). A module can decode perfectly — every index resolving, every \
                 vector framed, every section consumed — and still be REJECTED by an engine \
                 because a value of the wrong type reached an operand, a block's arity does not \
                 match its label, or code after `unreachable` fails the polymorphic-stack rule. \
                 None of that is expressible over a byte grammar: it needs the type system. \
                 Claiming this family covers it would be the single most misleading thing it \
                 could say, so it is named RED here and left to the independent reference \
                 validator that really does run the spec's validation algorithm",
    },
    WasmEncodingDeferral {
        name: "which BLOCK a branch label denotes (br / br_if / br_table)",
        family: "relooper / CFG structural bisimulation (P4 family 1)",
        reason: "the label-in-range obligation above checks only that a label index is <= the \
                 nesting depth at its instruction, which is an ENCODING property: it refutes a \
                 label that escapes every enclosing block. It says NOTHING about which block the \
                 label denotes, because a byte decoder sees a depth counter, not the trust-ir \
                 block a `block`/`loop` was opened for. The wrong lowering that matters — a \
                 correctly-formed label wired to the wrong depth, which validates and runs and \
                 branches to the wrong place — is invisible here and belongs to the relooper \
                 bisimulation",
    },
    WasmEncodingDeferral {
        name: "the CALLEE identity of a `call` to a NON-EXPORTED function",
        family: "call/table ABI discipline (P4 family 3) + lowering refinement (P4 family 2)",
        reason: "the index obligations prove a `call` immediate RESOLVES, and the import-shift \
                 differential proves it moves by exactly the import count. Binding an index to a \
                 NAME needs the export section, so a call to an exported trust-ir function can be \
                 named — but the backend also emits functions nothing exports (the memory.size / \
                 memory.grow shims are appended after every trust-ir function), and for those the \
                 decoder has no name to bind. A `call` that resolves to the wrong unexported \
                 function is therefore outside this family's reach",
    },
    WasmEncodingDeferral {
        name: "the FULL i32 / i64 constant ranges",
        family: "P4 family 5 itself — this is a coverage limit, not a structural one",
        reason: "the const-immediate corpus is the byte-length boundaries (where the continuation \
                 bits flip), the sign-extension edges (-1, i32::MIN, i64::MIN) and the \
                 maximum-length encodings; it is 31 i32 + 43 i64 values, not 2^32 + 2^64. \
                 `tests/wasm_encoding_gate.rs` carries an `#[ignore]`d EXHAUSTIVE full-i32 sweep \
                 over the encoder function, plus a 2.1M-value i64 window in the default lane — but \
                 the WHOLE-MODULE path (trust-ir Const -> lowering -> module bytes -> decode) runs \
                 only over the corpus, because a full sweep of module compiles is 4.29e9 compiles. \
                 The gap named here is precisely that: between the corpus points the immediate \
                 encoding is proven at the byte level, not through the module",
    },
    WasmEncodingDeferral {
        name: "f32.const / f64.const immediates",
        family: "P4 family 5 (byte reconstruction), currently unbuilt",
        reason: "the float const forms carry a RAW 4/8-byte little-endian IEEE-754 payload, not an \
                 LEB128, so the independent LEB decoder says nothing about them and the two RED \
                 rows this family closes are the INTEGER ones. Decoding the raw payload is easy; \
                 what is NOT easy is the source side, because the trust-ir carries an f64 and the \
                 f32 form is a lossy `as f32` narrowing whose rounding is its own obligation. \
                 Stating a bit-pattern equality without stating the narrowing would credit a \
                 rounding bug, so no obligation is built and the row stays RED",
    },
    WasmEncodingDeferral {
        name: "TargetInfo `abi` and `struct_passing`",
        family: "P4 family 6 (target conformance)",
        reason: "the wasm32 pin also declares `abi: None` and `struct_passing: Unclassified`. \
                 NEITHER is observable in an emitted module: wasm has no ABI byte and no \
                 aggregate-classification record, and the backend refuses by-value aggregates at \
                 type mapping rather than encoding a classification. So there is nothing in the \
                 bytes for an obligation to decode, and a conformance claim over those two fields \
                 would be assertion, not evidence",
    },
    WasmEncodingDeferral {
        name: "custom sections, the start section, datacount, bulk memory, reference types, SIMD",
        family: "no family — the decoder FAIL-CLOSES on each",
        reason: "the backend emits none of these today, and the decoder refuses a module \
                 containing one rather than skipping it. That is deliberate: skipping unexamined \
                 bytes is how an encoding gate goes quietly vacuous. The cost is equally \
                 deliberate and named here — the day the backend legitimately emits a name \
                 section or a bulk-memory op, this family goes RED until its decoder and its \
                 obligations are extended, which is the correct direction to fail",
    },
];

// ===========================================================================
// Anti-tautology guards — mutate the thing under proof, demand a REFUTATION
// ===========================================================================

// Every mutator below is EXERCISED by `tests/wasm_encoding_gate.rs` against
// REAL emitted bytes, and each is asserted to fire the SPECIFIC obligation it
// targets — a guard that merely "refutes something" would let an unrelated
// obligation stand in for the one under test.

/// Flip the continuation bit OFF in the FIRST byte of a multi-byte immediate:
/// the classic "forgot to set 0x80" encoder bug. The decoder then stops early
/// and recovers a different (truncated) value.
pub fn mutate_drop_continuation(immediate: &[u8]) -> Option<Vec<u8>> {
    if immediate.len() < 2 {
        return None;
    }
    let mut v = immediate.to_vec();
    v[0] &= 0x7f;
    // Keep only the bytes the mutated encoding actually spans, so the caller
    // hands the obligation a well-framed (but wrong) immediate.
    v.truncate(1);
    Some(v)
}

/// Re-encode `value` as UNSIGNED LEB128 — the sleb/uleb confusion bug. For a
/// negative value the two encodings differ, and decoding the unsigned form as
/// `sN` yields a different value or an out-of-range rejection.
pub fn mutate_as_unsigned(value: i64, bits: u32) -> Vec<u8> {
    // The unsigned encoding of the value's two's-complement bit pattern at
    // `bits` width — written here (not reused from the encoder) because it is a
    // MUTANT, not an obligation.
    let mut v: u64 = if bits >= 64 {
        value as u64
    } else {
        (value as u64) & ((1u64 << bits) - 1)
    };
    let mut out = Vec::new();
    loop {
        let mut b = (v & 0x7f) as u8;
        v >>= 7;
        if v != 0 {
            b |= 0x80;
        }
        out.push(b);
        if v == 0 {
            break;
        }
    }
    out
}

/// Append a redundant `0x80 0x00` pair: an OVERLONG encoding that decodes to
/// the same value under a permissive decoder and must be REJECTED by a
/// spec-conforming one (the `sN` range side conditions forbid it).
pub fn mutate_overlong(immediate: &[u8]) -> Vec<u8> {
    let mut v = immediate.to_vec();
    if let Some(last) = v.last_mut() {
        *last |= 0x80;
    }
    v.push(0x00);
    v
}

/// Drop the last byte: a TRUNCATED immediate the decoder must reject.
pub fn mutate_truncate(immediate: &[u8]) -> Vec<u8> {
    let mut v = immediate.to_vec();
    v.pop();
    v
}

/// Rewrite every `call k` in every code body to `call (k - by)` — the FORGOTTEN
/// IMPORT SHIFT. It is byte-length preserving whenever both indices are below
/// 128, which is the case that matters: it still type-checks, still validates,
/// and still runs, into the host.
///
/// Returns `None` when the module has no single-byte `call` immediate to rewrite.
pub fn mutate_unshift_calls(bytes: &[u8], by: u32) -> Option<Vec<u8>> {
    let m = decode_module(bytes).ok()?;
    // Locate the code section's absolute body offset by re-walking the section
    // headers exactly as `decode_module` does.
    let mut at = 8usize;
    let mut code_base = None;
    while at < bytes.len() {
        let id = bytes[at];
        at += 1;
        let (size, used) = spec_decode_unsigned(&bytes[at..], 32).ok()?;
        at += used;
        if id == 10 {
            code_base = Some(at);
        }
        at += size as usize;
    }
    let code_base = code_base?;

    // Re-walk the code section to find each body's absolute start, then apply
    // each instruction's recorded relative offset.
    let mut out = bytes.to_vec();
    let mut c = code_base;
    let (n, used) = spec_decode_unsigned(&bytes[c..], 32).ok()?;
    c += used;
    let mut changed = false;
    for body in m.code.iter().take(n as usize) {
        let (size, used) = spec_decode_unsigned(&bytes[c..], 32).ok()?;
        c += used;
        let entry_start = c;
        c += size as usize;
        // Skip the locals vector to find where the expression begins.
        let mut e = entry_start;
        let (runs, used) = spec_decode_unsigned(&bytes[e..], 32).ok()?;
        e += used;
        for _ in 0..runs {
            let (_cnt, used) = spec_decode_unsigned(&bytes[e..], 32).ok()?;
            e += used + 1;
        }
        for ins in &body.instrs {
            if let Imm::Func(f) = ins.imm
                && f >= by
                && f - by < 0x80
                && f < 0x80
            {
                out[e + ins.offset + 1] = (f - by) as u8;
                changed = true;
            }
        }
    }
    changed.then_some(out)
}

/// Point the FIRST function export at an out-of-range index. Byte-length
/// preserving as long as the replacement stays below 128.
pub fn mutate_export_out_of_range(bytes: &[u8], to: u8) -> Option<Vec<u8>> {
    let mut at = 8usize;
    while at < bytes.len() {
        let id = bytes[at];
        at += 1;
        let (size, used) = spec_decode_unsigned(&bytes[at..], 32).ok()?;
        at += used;
        if id == 7 {
            let mut c = at;
            let (n, used) = spec_decode_unsigned(&bytes[c..], 32).ok()?;
            c += used;
            if n == 0 {
                return None;
            }
            // First export: name length, name, kind byte, index.
            let (len, used) = spec_decode_unsigned(&bytes[c..], 32).ok()?;
            c += used + len as usize;
            c += 1; // kind
            if *bytes.get(c)? >= 0x80 {
                return None;
            }
            let mut out = bytes.to_vec();
            out[c] = to;
            return Some(out);
        }
        at += size as usize;
    }
    None
}

/// Reverse the bytes of a data segment's image — the BIG-ENDIAN lowering bug.
/// Byte-length preserving by construction.
pub fn mutate_reverse_data_image(bytes: &[u8], segment: usize) -> Option<Vec<u8>> {
    let mut at = 8usize;
    while at < bytes.len() {
        let id = bytes[at];
        at += 1;
        let (size, used) = spec_decode_unsigned(&bytes[at..], 32).ok()?;
        at += used;
        if id == 11 {
            let mut c = at;
            let (n, used) = spec_decode_unsigned(&bytes[c..], 32).ok()?;
            c += used;
            for i in 0..n as usize {
                let (_kind, used) = spec_decode_unsigned(&bytes[c..], 32).ok()?;
                c += used;
                // offset expr: one const instruction + `end`
                c += 1; // the const opcode
                let (_v, used) = spec_decode_signed(&bytes[c..], 64).ok()?;
                c += used;
                c += 1; // end
                let (len, used) = spec_decode_unsigned(&bytes[c..], 32).ok()?;
                c += used;
                if i == segment {
                    let mut out = bytes.to_vec();
                    out[c..c + len as usize].reverse();
                    return Some(out);
                }
                c += len as usize;
            }
            return None;
        }
        at += size as usize;
    }
    None
}

/// Shrink the element segment's function-index vector count by one, so the
/// table no longer covers the whole function index space. Byte-length
/// preserving only when the count is a single LEB byte, which it is for every
/// module this backend emits; returns `None` otherwise.
pub fn mutate_shrink_element_count(bytes: &[u8]) -> Option<Vec<u8>> {
    let mut at = 8usize;
    while at < bytes.len() {
        let id = bytes[at];
        at += 1;
        let (size, used) = spec_decode_unsigned(&bytes[at..], 32).ok()?;
        at += used;
        if id == 9 {
            let mut c = at;
            let (_n, used) = spec_decode_unsigned(&bytes[c..], 32).ok()?;
            c += used;
            let (_flags, used) = spec_decode_unsigned(&bytes[c..], 32).ok()?;
            c += used;
            // offset expr: i32.const <s32> end
            c += 1;
            let (_v, used) = spec_decode_signed(&bytes[c..], 32).ok()?;
            c += used;
            c += 1;
            if *bytes.get(c)? == 0 || bytes[c] >= 0x80 {
                return None;
            }
            let mut out = bytes.to_vec();
            out[c] -= 1;
            return Some(out);
        }
        at += size as usize;
    }
    None
}

/// The absolute `(start, end)` span of every section block (id byte through the
/// last body byte), in emission order.
pub fn section_spans(bytes: &[u8]) -> Option<Vec<(usize, usize)>> {
    let mut at = 8usize;
    let mut out = Vec::new();
    while at < bytes.len() {
        let start = at;
        at += 1;
        let (size, used) = spec_decode_unsigned(bytes.get(at..)?, 32).ok()?;
        at += used + size as usize;
        if at > bytes.len() {
            return None;
        }
        out.push((start, at));
    }
    Some(out)
}

/// SWAP two adjacent complete section blocks. Unlike a raw id rewrite this
/// leaves every section individually decodable, so the module still decodes and
/// the STRICTLY-INCREASING-ID obligation is the thing that fires — which is what
/// makes it a guard for that obligation rather than for the decoder.
pub fn mutate_swap_adjacent_sections(bytes: &[u8], first: usize) -> Option<Vec<u8>> {
    let spans = section_spans(bytes)?;
    if first + 1 >= spans.len() {
        return None;
    }
    let (a0, a1) = spans[first];
    let (b0, b1) = spans[first + 1];
    let mut out = bytes[..a0].to_vec();
    out.extend_from_slice(&bytes[b0..b1]);
    out.extend_from_slice(&bytes[a0..a1]);
    out.extend_from_slice(&bytes[b1..]);
    Some(out)
}

/// DROP the last element-segment entry AND repair both the segment's count and
/// the section's length prefix, so the result is a perfectly WELL-FORMED module
/// whose element segment simply does not cover the whole function index space —
/// exactly what "sized the table from the DEFINED function count" produces.
///
/// This is the mutation that fires the coverage obligation itself;
/// [`mutate_shrink_element_count`] fires the exact-consumption rule instead,
/// because it leaves the dropped entry's byte behind.
pub fn mutate_drop_last_element(bytes: &[u8]) -> Option<Vec<u8>> {
    let m = decode_module(bytes).ok()?;
    if m.elements.first()?.func_indices.len() < 2 {
        return None;
    }
    let spans = section_spans(bytes)?;
    let (start, end) = *spans.iter().find(|(s, _)| bytes[*s] == 9)?;
    let len_at = start + 1;
    if bytes[len_at] >= 0x80 || bytes[len_at] == 0 {
        return None; // multi-byte section length: repairing it would move bytes
    }
    let mut c = len_at + 1;
    let (_n, used) = spec_decode_unsigned(&bytes[c..], 32).ok()?;
    c += used;
    let (_flags, used) = spec_decode_unsigned(&bytes[c..], 32).ok()?;
    c += used;
    c += 1; // i32.const opcode
    let (_v, used) = spec_decode_signed(&bytes[c..], 32).ok()?;
    c += used;
    c += 1; // end
    let count_at = c;
    let (cnt, used) = spec_decode_unsigned(&bytes[c..], 32).ok()?;
    c += used;
    if bytes[count_at] >= 0x80 || cnt < 2 {
        return None;
    }
    // Every entry must be single-byte so dropping the last removes exactly one.
    for i in 0..cnt as usize {
        if *bytes.get(c + i)? >= 0x80 {
            return None;
        }
    }
    let last = c + cnt as usize - 1;
    let mut out = bytes[..last].to_vec();
    out.extend_from_slice(&bytes[last + 1..]);
    out[count_at] -= 1;
    out[len_at] -= 1;
    debug_assert_eq!(out.len() + 1, bytes.len());
    let _ = end;
    Some(out)
}

/// Rewrite the LAST element-segment entry to function 0, breaking the
/// `element i == function i` identity while leaving the count intact. Length
/// preserving whenever both indices are single-byte, which they are for every
/// module this backend emits.
pub fn mutate_element_identity(bytes: &[u8]) -> Option<Vec<u8>> {
    let m = decode_module(bytes).ok()?;
    let seg = m.elements.first()?;
    if seg.func_indices.len() < 2 {
        return None;
    }
    let spans = section_spans(bytes)?;
    let (start, _) = *spans.iter().find(|(s, _)| bytes[*s] == 9)?;
    let mut c = start + 1;
    let (_len, used) = spec_decode_unsigned(&bytes[c..], 32).ok()?;
    c += used;
    let (_n, used) = spec_decode_unsigned(&bytes[c..], 32).ok()?;
    c += used;
    let (_flags, used) = spec_decode_unsigned(&bytes[c..], 32).ok()?;
    c += used;
    c += 1; // i32.const opcode
    let (_v, used) = spec_decode_signed(&bytes[c..], 32).ok()?;
    c += used;
    c += 1; // end
    let (cnt, used) = spec_decode_unsigned(&bytes[c..], 32).ok()?;
    c += used;
    // Step to the LAST entry; every entry must be single-byte for the rewrite
    // to preserve length.
    for _ in 0..cnt.saturating_sub(1) {
        if *bytes.get(c)? >= 0x80 {
            return None;
        }
        c += 1;
    }
    if *bytes.get(c)? >= 0x80 || bytes[c] == 0 {
        return None;
    }
    let mut out = bytes.to_vec();
    out[c] = 0;
    Some(out)
}

/// Point the FIRST defined function's type index past the end of the type
/// section. Length preserving while both indices are single-byte.
pub fn mutate_function_type_index(bytes: &[u8], to: u8) -> Option<Vec<u8>> {
    let spans = section_spans(bytes)?;
    let (start, _) = *spans.iter().find(|(s, _)| bytes[*s] == 3)?;
    let mut c = start + 1;
    let (_len, used) = spec_decode_unsigned(&bytes[c..], 32).ok()?;
    c += used;
    let (n, used) = spec_decode_unsigned(&bytes[c..], 32).ok()?;
    c += used;
    if n == 0 || *bytes.get(c)? >= 0x80 || to >= 0x80 {
        return None;
    }
    let mut out = bytes.to_vec();
    out[c] = to;
    Some(out)
}

/// Rewrite a memory section's limits flag to the MEMORY64 form (0x04).
/// Byte-length preserving.
pub fn mutate_memory64_flag(bytes: &[u8]) -> Option<Vec<u8>> {
    let mut at = 8usize;
    while at < bytes.len() {
        let id = bytes[at];
        at += 1;
        let (size, used) = spec_decode_unsigned(&bytes[at..], 32).ok()?;
        at += used;
        if id == 5 {
            let mut c = at;
            let (n, used) = spec_decode_unsigned(&bytes[c..], 32).ok()?;
            c += used;
            if n == 0 || c >= bytes.len() {
                return None;
            }
            let mut out = bytes.to_vec();
            out[c] = 0x04;
            return Some(out);
        }
        at += size as usize;
    }
    None
}

// ---------------------------------------------------------------------------
// Tests — the byte-level half. The LIVE-BACKEND half lives in
// `tests/wasm_encoding_gate.rs`, which can reach `trust-cg-codegen`.
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    /// The spec's canonical LEB128 examples, transcribed from the specification
    /// text itself (a THIRD oracle: neither the encoder nor the decoder).
    #[test]
    fn spec_worked_examples_decode() {
        // Unsigned (spec §5.2.2 examples + the standard DWARF table).
        for (bytes, want) in [
            (&[0x00u8][..], 0u64),
            (&[0x7f], 127),
            (&[0x80, 0x01], 128),
            (&[0xe5, 0x8e, 0x26], 624_485),
        ] {
            assert_eq!(
                spec_decode_unsigned(bytes, 64).unwrap(),
                (want, bytes.len())
            );
        }
        // Signed.
        for (bytes, want) in [
            (&[0x00u8][..], 0i64),
            (&[0x7f], -1),
            (&[0x3f], 63),
            (&[0x40], -64),
            (&[0xc0, 0x00], 64),
            (&[0xbf, 0x7f], -65),
            (&[0x9b, 0xf1, 0x59], -624_485),
        ] {
            assert_eq!(spec_decode_signed(bytes, 64).unwrap(), (want, bytes.len()));
        }
    }

    /// The decoder REJECTS what the spec's side conditions forbid: overlong
    /// encodings, values outside `sN`/`uN`, and truncated streams. A permissive
    /// decoder would make every range obligation below vacuous.
    #[test]
    fn decoder_fails_closed_on_malformed_leb128() {
        // Overlong: 0x80 0x00 is 0 padded to two groups.
        assert!(matches!(
            spec_decode_signed(&[0x80, 0x00], 7),
            Err(LebError::ContinuationPastBudget { .. })
        ));
        // s32 with a 5th group carrying more than 4 significant bits.
        assert!(matches!(
            spec_decode_signed(&[0xff, 0xff, 0xff, 0xff, 0x0f], 32),
            Err(LebError::OutOfRange { .. })
        ));
        // s64 with an 11th group at all.
        assert!(matches!(
            spec_decode_signed(&[0x80; 11], 64),
            Err(LebError::ContinuationPastBudget { .. })
        ));
        // Truncated.
        assert!(matches!(
            spec_decode_signed(&[0x80], 32),
            Err(LebError::Truncated { .. })
        ));
        assert!(matches!(
            spec_decode_unsigned(&[], 32),
            Err(LebError::Truncated { .. })
        ));
        // u32 with a 5th group carrying more than 4 bits.
        assert!(matches!(
            spec_decode_unsigned(&[0xff, 0xff, 0xff, 0xff, 0x1f], 32),
            Err(LebError::OutOfRange { .. })
        ));
    }

    /// The captured corpus discharges family (5) in full, and the two RED
    /// coverage-gate rows are creditable by the hook.
    #[test]
    fn captured_const_corpus_discharges() {
        let obs = emitted_const_immediate_obligations();
        let report = EncodingReport::of(&obs);
        assert_eq!(
            report.refuted, 0,
            "captured immediates that do NOT decode to their intended value: {:?}",
            report.refutations
        );
        assert_eq!(report.not_applicable, 0);
        assert_eq!(report.proven, EMITTED_CONST_IMMEDIATES.len());
        assert!(const_immediate_discharges_valid(OP_I32_CONST));
        assert!(const_immediate_discharges_valid(OP_I64_CONST));
        // Fail closed for everything else.
        for b in [0x00u8, 0x40, 0x43, 0x44, 0x6a, 0xff] {
            assert!(!const_immediate_discharges_valid(b), "0x{b:02x}");
        }
    }

    /// Both widths are actually represented, including the maximum-length
    /// encodings and the sign-extension edges. A corpus that quietly lost its
    /// i64 half would still pass the test above.
    #[test]
    fn corpus_covers_the_edges_it_claims() {
        let i32s: Vec<i64> = EMITTED_CONST_IMMEDIATES
            .iter()
            .filter(|(_, b, _)| *b == 32)
            .map(|(v, _, _)| *v)
            .collect();
        let i64s: Vec<i64> = EMITTED_CONST_IMMEDIATES
            .iter()
            .filter(|(_, b, _)| *b == 64)
            .map(|(v, _, _)| *v)
            .collect();
        for want in [-1, 0, i64::from(i32::MIN), i64::from(i32::MAX)] {
            assert!(i32s.contains(&want), "i32 corpus is missing {want}");
        }
        for want in [-1, 0, i64::MIN, i64::MAX] {
            assert!(i64s.contains(&want), "i64 corpus is missing {want}");
        }
        // The maximum-length encodings are present at both widths.
        assert!(
            EMITTED_CONST_IMMEDIATES
                .iter()
                .any(|(_, b, e)| *b == 32 && e.len() == 5)
        );
        assert!(
            EMITTED_CONST_IMMEDIATES
                .iter()
                .any(|(_, b, e)| *b == 64 && e.len() == 10)
        );
        // Every 7-bit boundary up to the width is crossed in BOTH signs.
        for (bits, vals) in [(32u32, &i32s), (64, &i64s)] {
            for k in 1..=(bits / 7) {
                let b = 1i64 << (7 * k - 1);
                assert!(
                    vals.contains(&b) || vals.contains(&(b - 1)),
                    "s{bits} corpus does not cross the +2^{} boundary",
                    7 * k - 1
                );
                assert!(
                    vals.contains(&-b) || vals.contains(&(-b - 1)),
                    "s{bits} corpus does not cross the -2^{} boundary",
                    7 * k - 1
                );
            }
        }
    }

    /// THE TEETH for family (5): every mutation of a REAL emitted immediate is
    /// REFUTED. If any passes, the const obligation is vacuous.
    #[test]
    fn const_mutants_are_refuted() {
        let mut checked = 0usize;
        for &(intended, bits, imm) in EMITTED_CONST_IMMEDIATES {
            let opcode = if bits == 32 {
                OP_I32_CONST
            } else {
                OP_I64_CONST
            };
            // 1. dropped continuation bit
            if let Some(m) = mutate_drop_continuation(imm) {
                let ob = const_immediate_obligation(intended, opcode, &m);
                assert!(
                    ob.is_refuted(),
                    "dropping the continuation bit of {intended} ({imm:02x?} -> {m:02x?}) was NOT \
                     refuted"
                );
                checked += 1;
            }
            // 2. unsigned-LEB confusion (differs only when the encodings differ)
            let unsigned = mutate_as_unsigned(intended, bits);
            if unsigned != imm {
                let ob = const_immediate_obligation(intended, opcode, &unsigned);
                assert!(
                    ob.is_refuted(),
                    "encoding {intended} as ULEB128 ({unsigned:02x?} instead of {imm:02x?}) was \
                     NOT refuted"
                );
                checked += 1;
            }
            // 3. overlong pad
            let ob = const_immediate_obligation(intended, opcode, &mutate_overlong(imm));
            assert!(
                ob.is_refuted(),
                "an OVERLONG encoding of {intended} was NOT refuted"
            );
            checked += 1;
            // 4. truncation
            let ob = const_immediate_obligation(intended, opcode, &mutate_truncate(imm));
            assert!(
                ob.is_refuted(),
                "a TRUNCATED encoding of {intended} was NOT refuted"
            );
            checked += 1;
            // 5. off-by-one on the SOURCE side
            let ob = const_immediate_obligation(intended.wrapping_add(1), opcode, imm);
            assert!(
                ob.is_refuted(),
                "claiming {intended}'s bytes denote {} was NOT refuted",
                intended.wrapping_add(1)
            );
            checked += 1;
        }
        assert!(checked > 250, "only {checked} mutants exercised");
        eprintln!("const_mutants_are_refuted: {checked} mutants, all REFUTED");
    }

    /// The canonical-length function agrees with every captured encoding's real
    /// length — the LENGTH half of the const obligation is not vacuous.
    #[test]
    fn canonical_lengths_match_the_captured_encodings() {
        for &(v, bits, imm) in EMITTED_CONST_IMMEDIATES {
            assert_eq!(
                canonical_signed_len(v, bits),
                imm.len(),
                "canonical s{bits} length of {v}"
            );
        }
    }

    /// WHY THE LENGTH CONJUNCT EXISTS. The spec's `sN` production ADMITS padded
    /// encodings, so the independent decoder accepts `0x80 0x00` as `i32.const 0`
    /// and a value-only obligation would too. This pins that: the decode
    /// SUCCEEDS with the right value, and the obligation is REFUTED anyway.
    #[test]
    fn a_padded_encoding_decodes_correctly_but_is_still_refuted() {
        // The decoder is a faithful `sN`: it accepts the pad.
        assert_eq!(spec_decode_signed(&[0x80, 0x00], 32).unwrap(), (0, 2));
        assert_eq!(spec_decode_signed(&[0xff, 0x7f], 32).unwrap(), (-1, 2));
        // The obligation is not, because the canonical length is 1.
        for (v, padded) in [(0i64, &[0x80u8, 0x00][..]), (-1, &[0xff, 0x7f])] {
            let ob = const_immediate_obligation(v, OP_I32_CONST, padded);
            assert!(
                ob.is_refuted(),
                "the padded encoding of {v} decoded correctly AND was credited — the length \
                 conjunct is doing nothing"
            );
            assert_eq!(canonical_signed_len(v, 32), 1);
        }
    }

    /// The deferrals are present, distinct, and each states a family and a
    /// substantive reason.
    #[test]
    fn deferrals_are_named_and_substantive() {
        assert_eq!(WASM_ENCODING_DEFERRALS.len(), 7);
        let names: std::collections::HashSet<_> =
            WASM_ENCODING_DEFERRALS.iter().map(|d| d.name).collect();
        assert_eq!(names.len(), WASM_ENCODING_DEFERRALS.len());
        for d in WASM_ENCODING_DEFERRALS {
            assert!(!d.family.is_empty(), "{} has no family", d.name);
            assert!(
                d.reason.len() > 120,
                "{} has a token reason, not an auditable one",
                d.name
            );
        }
    }

    /// The wasm32 pin restated here is the one the backend's own guard demands.
    /// (The guard itself is exercised against the live compiler in
    /// `tests/wasm_encoding_gate.rs`.)
    #[test]
    fn the_pin_is_wasm32_le_4() {
        assert_eq!(WASM32_PIN, ("wasm32", 4, true));
    }
}
