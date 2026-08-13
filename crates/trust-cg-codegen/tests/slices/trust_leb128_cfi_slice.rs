// Trust-toolchain slice — the trust-cg LEB128 + DWARF-CFI byte encoders and the
// eh_frame LEB128 DECODERS, transcribed VERBATIM.
//
// SELF-APPLICATION of verify-native==JIT to TRUST ITSELF (round 28, TRUST BATCH 15).
//
// SURFACE: the DWARF/eh_frame unwind-table byte machinery. A wrong LEB128 byte or a
// wrong CFI opcode byte produces a corrupt `.eh_frame`/`__eh_frame` section — broken
// stack unwinding / exception handling at runtime. The functions here are the pure,
// scalar-shaped byte producers/consumers:
//
//   ENCODERS (write LEB128 / CFI bytes):
//     * `encode_uleb128`  — dwarf_cfi.rs:800   (ULEB128 encoder)
//     * `encode_sleb128`  — dwarf_cfi.rs:815   (SLEB128 encoder, `while more` form)
//     * `write_uleb128`   — wasm/encode.rs:23  (ULEB128 encoder, wasm — distinct fn)
//     * `write_sleb128`   — wasm/encode.rs:38  (SLEB128 encoder, wasm `loop`/`done` form)
//     * `encode_advance_loc`       — dwarf_cfi.rs:837 (DW_CFA_advance_loc opcode assembly)
//     * `encode_advance_loc_bytes` — dwarf_cfi.rs:857 (byte-granularity DW_CFA_advance_loc)
//     * `pointer_encoding_size`    — dwarf_cfi.rs:782 (DW_EH_PE pointer-size decode)
//   DECODERS (read LEB128 bytes back — the eh_frame roundtrip checker):
//     * `Reader::uleb128` — dwarf_cfi_decode_check.rs:209 (ULEB128 decoder)
//     * `Reader::sleb128` — dwarf_cfi_decode_check.rs:226 (SLEB128 decoder; SIGN-EXTENSION)
//
// THE ROUND'S POWER — three independent oracles per LEB128 value:
//   (1) native==JIT: the verbatim slice, compiled by native rustc, must equal the JIT.
//   (2) ENCODE<->DECODE ROUND-TRIP: decode(encode(v)) == v for a swept value set. An
//       asymmetry between `encode_*` and `Reader::*` is a REAL bug (a wrong unwind table).
//       ALSO: the two independent SLEB encoders (`encode_sleb128` `while more` vs
//       `write_sleb128` `loop/done`) must produce byte-identical output — a cross-impl
//       differential.
//   (3) SPEC ORACLE: the DWARF-v5 Appendix C canonical LEB128 byte examples (also pinned
//       in dwarf_cfi_decode_check.rs::{uleb128,sleb128}_decoder_matches_spec_examples and
//       wasm/encode.rs::{uleb128,sleb128}_examples) — a third oracle that catches a bug
//       even if BOTH encoder and decoder share the same mistake.
//
// MODELED BOUNDARIES (documented honestly):
//   A. Vec<u8> SINK -> `LebBuf` (two u64 halves + len). The production encoders write
//      into `out: &mut Vec<u8>` via `out.push(byte)`. The frontend's Vec<u8>::push shim
//      is by-value only and reading a Vec back across the JIT FFI boundary is not a
//      supported shape; so the byte sink is modeled as a fixed two-u64 accumulator
//      (`lo` holds bytes 0..8, `hi` holds bytes 8..16 — LEB128 of a u64/i64 is <=10
//      bytes). The two-u64 split uses an explicit branch (NOT a u128 bitcast), avoiding
//      the u128 half-splitting register-pair class (owner item #3). The encoder LOOP
//      BODIES are byte-for-byte the production source; only the type of `out` changes
//      (Vec<u8> -> LebBuf) and `out.push(byte)` stays textually identical. `to_le_bytes`
//      + `extend_from_slice` (advance_loc2's 2-byte tail) is modeled as `push_u16_le`
//      (two LE pushes — byte-identical output).
//   B. Reader BYTE SOURCE + ERROR TYPE. Production `Reader` reads `self.bytes[pos]`
//      (a `&[u8]`) and returns `Result<_, EhFrameDecodeError>` whose payload is a
//      `String` diagnostic built with `format!`. The bytes are modeled as the same
//      two-u64 (lo,hi) pair + a `limit` (valid byte count); the error is modeled as the
//      FIELDLESS 2-variant enum `DecErr {Overflow, Truncated}` (drops the `String`
//      message but keeps the fail-closed error KIND — same discipline as the R27 decode
//      slice that modeled DecodeError as a fieldless enum). The DECODE LOOP BODIES (the
//      `shift >= 64` overflow guard, `byte & 0x7F` mask, `byte & 0x80` continuation test,
//      and the SLEB `shift < 64 && byte & 0x40` sign-extension) are byte-for-byte source.
//   C. `?`-operator on `Result<_, DecErr>` (the `self.u8()?` sites) is rewritten to the
//      explicit `match { Ok(v)=>v, Err(e)=>return Err(e) }` it desugars to — the R27 [F4]
//      finding: `?` on `Result<_, custom-enum>` desugars to `Try::branch`/`FromResidual`
//      calls that lower to unresolved extern leaves at JIT link. Semantically identical.
//      Production's `err(msg)` (returns `Err(EhFrameDecodeError{..})`) is likewise
//      `return Err(DecErr::Overflow)`.
//   D. `u64::from(x)` / `i64::from(x)` widening is written `x as u64` / `x as i64`
//      (value-identical unsigned/sign widening) to avoid a From-trait leaf — see the
//      empirical note; the mask/shift arithmetic is otherwise byte-for-byte.
//
// The `#[unsafe(no_mangle)]` roots are test-harness ABI adapters (NOT production): each
// runs the verbatim callee and packs the LebBuf / decode result into a scalar POD.
//
// Everything else is byte-for-byte from dwarf_cfi.rs / dwarf_cfi_decode_check.rs /
// wasm/encode.rs (compare against those three files).

#![allow(dead_code)]

// ── DWARF CFA opcode constants (VERBATIM, dwarf_cfi.rs:79-100) ──────────────
const DW_CFA_ADVANCE_LOC: u8 = 0x40;
const DW_CFA_ADVANCE_LOC1: u8 = 0x02;
const DW_CFA_ADVANCE_LOC2: u8 = 0x03;
const DW_EH_PE_SDATA4: u8 = 0x0B;
const DW_EH_PE_SDATA8: u8 = 0x0C;

// ── MODELED (boundary A): Vec<u8> sink -> two-u64 accumulator ───────────────
struct LebBuf {
    lo: u64,
    hi: u64,
    len: u32,
}

impl LebBuf {
    fn new() -> Self {
        LebBuf {
            lo: 0,
            hi: 0,
            len: 0,
        }
    }
    // models `Vec<u8>::push(byte)` — append one byte at index `len`.
    fn push(&mut self, byte: u8) {
        if self.len < 8 {
            self.lo |= (byte as u64) << (8u32 * self.len);
        } else {
            self.hi |= (byte as u64) << (8u32 * (self.len - 8));
        }
        self.len += 1;
    }
    // models `out.extend_from_slice(&v.to_le_bytes())` for u16 — two LE pushes.
    fn push_u16_le(&mut self, v: u16) {
        self.push((v & 0x00FF) as u8);
        self.push((v >> 8) as u8);
    }
}

// ── ENCODERS (VERBATIM loop bodies; sink = LebBuf per boundary A) ────────────

/// Encode a value as ULEB128 (unsigned LEB128).  [dwarf_cfi.rs:800]
fn encode_uleb128(mut value: u64, out: &mut LebBuf) {
    loop {
        let mut byte = (value & 0x7F) as u8;
        value >>= 7;
        if value != 0 {
            byte |= 0x80; // more bytes follow
        }
        out.push(byte);
        if value == 0 {
            break;
        }
    }
}

/// Encode a value as SLEB128 (signed LEB128).  [dwarf_cfi.rs:815, `while more` form]
fn encode_sleb128(mut value: i64, out: &mut LebBuf) {
    let mut more = true;
    while more {
        let mut byte = (value & 0x7F) as u8;
        value >>= 7;
        // If the sign bit of the current byte matches the remaining value,
        // we're done.
        if (value == 0 && byte & 0x40 == 0) || (value == -1 && byte & 0x40 != 0) {
            more = false;
        } else {
            byte |= 0x80;
        }
        out.push(byte);
    }
}

/// Append an unsigned LEB128 encoding of `value` to `buf`.  [wasm/encode.rs:23]
fn write_uleb128(buf: &mut LebBuf, mut value: u64) {
    loop {
        let mut byte = (value & 0x7f) as u8;
        value >>= 7;
        if value != 0 {
            byte |= 0x80;
        }
        buf.push(byte);
        if value == 0 {
            break;
        }
    }
}

/// Append a signed LEB128 encoding of `value` to `buf`.  [wasm/encode.rs:38, `loop`/`done` form]
fn write_sleb128(buf: &mut LebBuf, mut value: i64) {
    loop {
        let byte = (value & 0x7f) as u8;
        // Arithmetic shift keeps the sign bit replicated.
        value >>= 7;
        let sign_bit_set = byte & 0x40 != 0;
        let done = (value == 0 && !sign_bit_set) || (value == -1 && sign_bit_set);
        if done {
            buf.push(byte);
            break;
        }
        buf.push(byte | 0x80);
    }
}

/// Encode a DW_CFA_advance_loc for `n` instructions.  [dwarf_cfi.rs:837]
///
/// Uses the smallest encoding that fits:
/// - DW_CFA_advance_loc (6-bit delta, 0-63 instructions)
/// - DW_CFA_advance_loc1 (8-bit delta)
/// - DW_CFA_advance_loc2 (16-bit delta)
fn encode_advance_loc(n_instructions: u32, out: &mut LebBuf) {
    if n_instructions <= 63 {
        // DW_CFA_advance_loc: high 2 bits = 0b01, low 6 bits = delta
        out.push(DW_CFA_ADVANCE_LOC | (n_instructions as u8));
    } else if n_instructions <= 255 {
        out.push(DW_CFA_ADVANCE_LOC1);
        out.push(n_instructions as u8);
    } else {
        out.push(DW_CFA_ADVANCE_LOC2);
        out.push_u16_le(n_instructions as u16);
    }
}

/// Encode a DW_CFA_advance_loc for `n_bytes` of code (byte granularity).  [dwarf_cfi.rs:857]
fn encode_advance_loc_bytes(n_bytes: u32, out: &mut LebBuf) {
    if n_bytes == 0 {
        return;
    }
    if n_bytes <= 63 {
        out.push(DW_CFA_ADVANCE_LOC | (n_bytes as u8));
    } else if n_bytes <= 255 {
        out.push(DW_CFA_ADVANCE_LOC1);
        out.push(n_bytes as u8);
    } else {
        out.push(DW_CFA_ADVANCE_LOC2);
        out.push_u16_le(n_bytes as u16);
    }
}

/// DW_EH_PE pointer-encoding -> byte size.  [dwarf_cfi.rs:782]
fn pointer_encoding_size(encoding: u8) -> usize {
    match encoding & 0x0F {
        0 => 8,
        DW_EH_PE_SDATA4 => 4,
        DW_EH_PE_SDATA8 => 8,
        _ => 8,
    }
}

// ── DECODERS (VERBATIM loop bodies; source/err modeled per boundaries B/C) ───

// MODELED (boundary B): fail-closed decode error KIND (drops the String message).
#[derive(Clone, Copy)]
pub enum DecErr {
    Overflow,
    Truncated,
}

struct Reader {
    lo: u64,
    hi: u64,
    pos: u32,
    limit: u32,
}

impl Reader {
    // models `self.bytes[pos]` over the two-u64 (lo,hi) pair.
    fn byte_at(&self, i: u32) -> u8 {
        if i < 8 {
            (self.lo >> (8u32 * i)) as u8
        } else {
            (self.hi >> (8u32 * (i - 8))) as u8
        }
    }

    // models `Reader::u8` (decode_check.rs:146): read one byte or fail-closed
    // (production returns Err with a "truncated: need 1 byte" String).
    fn u8(&mut self) -> Result<u8, DecErr> {
        if self.pos >= self.limit {
            return Err(DecErr::Truncated);
        }
        let b = self.byte_at(self.pos);
        self.pos += 1;
        Ok(b)
    }

    /// Independent ULEB128 decoder (DWARF-5 §7.6).  [decode_check.rs:209]
    fn uleb128(&mut self) -> Result<u64, DecErr> {
        let mut result: u64 = 0;
        let mut shift = 0u32;
        loop {
            // boundary C: `self.u8()?`
            let byte = self.u8()?;
            if shift >= 64 {
                return Err(DecErr::Overflow); // production: err("ULEB128 overflows u64")
            }
            result |= ((byte & 0x7F) as u64) << shift;
            if byte & 0x80 == 0 {
                return Ok(result);
            }
            shift += 7;
        }
    }

    /// Independent SLEB128 decoder (DWARF-5 §7.6).  [decode_check.rs:226]
    fn sleb128(&mut self) -> Result<i64, DecErr> {
        let mut result: i64 = 0;
        let mut shift = 0u32;
        loop {
            // boundary C: `self.u8()?`
            let byte = self.u8()?;
            if shift >= 64 {
                return Err(DecErr::Overflow); // production: err("SLEB128 overflows i64")
            }
            result |= ((byte & 0x7F) as i64) << shift;
            shift += 7;
            if byte & 0x80 == 0 {
                // Sign-extend if the sign bit of the final group is set.
                if shift < 64 && byte & 0x40 != 0 {
                    result |= -1i64 << shift;
                }
                return Ok(result);
            }
        }
    }
}

// ── harness adapter roots (NOT production) ──────────────────────────────────

#[repr(C)]
pub struct EncOut {
    pub lo: u64,
    pub hi: u64,
    pub len: u32,
}

#[repr(C)]
pub struct DecOut {
    pub value: u64, // decoded bits (sleb: i64 reinterpreted as u64)
    pub err: u32,   // 0 = Ok, 1 = Overflow, 2 = Truncated
}

#[unsafe(no_mangle)]
pub extern "C" fn enc_uleb_root(value: u64, out: *mut EncOut) {
    let mut buf = LebBuf::new();
    encode_uleb128(value, &mut buf);
    unsafe {
        (*out).lo = buf.lo;
        (*out).hi = buf.hi;
        (*out).len = buf.len;
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn enc_sleb_root(value: i64, out: *mut EncOut) {
    let mut buf = LebBuf::new();
    encode_sleb128(value, &mut buf);
    unsafe {
        (*out).lo = buf.lo;
        (*out).hi = buf.hi;
        (*out).len = buf.len;
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn wasm_uleb_root(value: u64, out: *mut EncOut) {
    let mut buf = LebBuf::new();
    write_uleb128(&mut buf, value);
    unsafe {
        (*out).lo = buf.lo;
        (*out).hi = buf.hi;
        (*out).len = buf.len;
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn wasm_sleb_root(value: i64, out: *mut EncOut) {
    let mut buf = LebBuf::new();
    write_sleb128(&mut buf, value);
    unsafe {
        (*out).lo = buf.lo;
        (*out).hi = buf.hi;
        (*out).len = buf.len;
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn adv_loc_root(n: u32, out: *mut EncOut) {
    let mut buf = LebBuf::new();
    encode_advance_loc(n, &mut buf);
    unsafe {
        (*out).lo = buf.lo;
        (*out).hi = buf.hi;
        (*out).len = buf.len;
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn adv_loc_bytes_root(n: u32, out: *mut EncOut) {
    let mut buf = LebBuf::new();
    encode_advance_loc_bytes(n, &mut buf);
    unsafe {
        (*out).lo = buf.lo;
        (*out).hi = buf.hi;
        (*out).len = buf.len;
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn ptr_enc_size_root(encoding: u32) -> u32 {
    pointer_encoding_size(encoding as u8) as u32
}

#[unsafe(no_mangle)]
pub extern "C" fn dec_uleb_root(lo: u64, hi: u64, limit: u32, out: *mut DecOut) {
    let mut r = Reader {
        lo,
        hi,
        pos: 0,
        limit,
    };
    let (value, err) = match r.uleb128() {
        Ok(v) => (v, 0u32),
        Err(DecErr::Overflow) => (0, 1),
        Err(DecErr::Truncated) => (0, 2),
    };
    unsafe {
        (*out).value = value;
        (*out).err = err;
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn dec_sleb_root(lo: u64, hi: u64, limit: u32, out: *mut DecOut) {
    let mut r = Reader {
        lo,
        hi,
        pos: 0,
        limit,
    };
    let (value, err) = match r.sleb128() {
        Ok(v) => (v as u64, 0u32),
        Err(DecErr::Overflow) => (0, 1),
        Err(DecErr::Truncated) => (0, 2),
    };
    unsafe {
        (*out).value = value;
        (*out).err = err;
    }
}

fn main() {
    let mut o = EncOut {
        lo: 0,
        hi: 0,
        len: 0,
    };
    enc_uleb_root(129, &mut o);
    println!("uleb(129) lo={} len={}", o.lo, o.len);
    let mut d = DecOut { value: 0, err: 0 };
    dec_uleb_root(o.lo, o.hi, o.len, &mut d);
    println!("dec -> {} err={}", d.value, d.err);
}
