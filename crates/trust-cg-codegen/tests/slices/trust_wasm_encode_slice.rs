// Trust-toolchain slice — the trust-cg WebAssembly binary ENCODER's pure,
// scalar-shaped byte producers, transcribed VERBATIM from wasm/encode.rs.
//
// SELF-APPLICATION of verify-native==JIT to TRUST ITSELF (round 29, TRUST BATCH 16).
//
// SURFACE: the WebAssembly binary format is FULLY SPECIFIED (WebAssembly Core
// Specification, section 5 "Binary Format"), so the wasm spec provides an
// INDEPENDENT ground-truth oracle for every byte these encoders emit. A byte that
// disagrees with the spec is a REAL bug — a malformed `.wasm` module. The functions
// here are the pure scalar-shaped byte producers of the wasm encoder that were NOT
// already verified in round 28 (round 28 covered `write_uleb128`/`write_sleb128` —
// those appear here only as already-verified CALLEES, they are NOT re-counted):
//
//   * `ValType::code`   — wasm/encode.rs:64  (the value-type byte: i32=0x7F, i64=0x7E,
//                                             f32=0x7D, f64=0x7C — exhaustive over the enum)
//   * `ExportKind::code`— wasm/encode.rs:99  (export-descriptor kind byte: Func=0x00)
//   * `emit_local_get`  — wasm/encode.rs:495 (`local.get $idx` = opcode 0x20 + uleb idx)
//   * `emit_i32_const`  — wasm/encode.rs:501 (`i32.const $v`  = opcode 0x41 + sleb value)
//   * `emit_memarg`     — wasm/encode.rs:508 (load/store memarg = uleb(align_exp), uleb(offset))
//   * `push_section`    — wasm/encode.rs:318 (section framing: id byte + uleb(len) + body)
//   * `wasm_header`     — wasm/encode.rs:192-195 (the finish() prologue: MAGIC "\0asm"
//                                             0x00 0x61 0x73 0x6d + version 0x01 0x00 0x00 0x00)
//
// THE ROUND'S POWER — the wasm SPEC as an INDEPENDENT oracle:
//   (1) native==JIT: the verbatim slice, compiled by native rustc, must equal the JIT.
//   (2) SPEC ORACLE: each encoder must emit EXACTLY the wasm-spec-mandated bytes
//       (ValType::code(i32)==0x7F; emit_i32_const(1)==[0x41,0x01];
//        emit_i32_const(-1)==[0x41,0x7f]; emit_local_get(128)==[0x20,0x80,0x01];
//        push_section(1,body)==[0x01, uleb(len), ..body]; the module header ==
//        [0x00,0x61,0x73,0x6d,0x01,0x00,0x00,0x00]). A mismatch is a malformed module = a bug.
//
// MODELED BOUNDARIES (documented honestly — diff against wasm/encode.rs):
//   A. Vec<u8> SINK -> `LebBuf` (two u64 halves + len), IDENTICAL to the round-28 model.
//      The production encoders write into `code: &mut Vec<u8>` / `out: &mut Vec<u8>` via
//      `.push(byte)`. The frontend's Vec<u8>::push shim is by-value-only and reading a Vec
//      back across the JIT FFI boundary is unsupported, so the byte sink is a fixed two-u64
//      accumulator (`lo` = bytes 0..8, `hi` = bytes 8..16). The two-u64 split uses an
//      explicit branch (NOT a u128 bitcast), avoiding the u128 half-splitting register-pair
//      class (owner item #3). The encoder BODIES are byte-for-byte the production source;
//      only the type of the sink changes (Vec<u8> -> LebBuf) and `.push(byte)` stays textual.
//      For `push_section`, production `out.extend_from_slice(body)` (a `&[u8]`) is modeled as
//      a `while i < body.len { out.push(body.byte_at(i)) }` copy — byte-identical output; and
//      for `wasm_header`, production `out.extend_from_slice(&[a,b,c,d])` (array literals) is
//      modeled as the four individual `out.push(_)` calls it expands to (same discipline as
//      round-28's `push_u16_le`).
//   D. `u64::from(x)` / `i64::from(x)` widening [round-28 boundary D]. EMPIRICALLY this
//      round: `u64::from(u32)` (emit_local_get, emit_memarg) and `i64::from(i32)`
//      (emit_i32_const) lower to a `core::convert::num::<impl From>::from` extern leaf that
//      is UNRESOLVED at JIT link — while the *emit* validates clean (a call is emitted; the
//      failure surfaces only at JIT link, the same F4 nuance round 27 recorded for
//      leading_zeros/trailing_zeros). So each such site is rewritten to the value-identical
//      `x as u64` / `x as i64` (zero-/sign-extension), documented inline. NOTE: round 28
//      found `u64::from(u8)`/`i64::from(u8)` DO lower in-module — the From<u8> impls are
//      in-closure but From<u32>/From<i32> are not. (`push_section` already uses `body.len
//      as u64`; `wasm_header`/`ValType::code`/`ExportKind::code` use no widening.)
//
// The `#[unsafe(no_mangle)]` roots are test-harness ABI adapters (NOT production): each runs
// the verbatim callee and packs the LebBuf / result byte into a scalar POD.
//
// Everything else is byte-for-byte from wasm/encode.rs (compare against that file).

#![allow(dead_code)]

// ── op constants (VERBATIM, wasm/encode.rs `op` module) ─────────────────────
const LOCAL_GET: u8 = 0x20; // wasm/encode.rs:345
const I32_CONST: u8 = 0x41; // wasm/encode.rs:358

// ── MODELED (boundary A): Vec<u8> sink -> two-u64 accumulator (round-28 LebBuf) ──
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
    // models `self.bytes[i]` (for push_section's extend_from_slice body copy).
    fn byte_at(&self, i: u32) -> u8 {
        if i < 8 {
            (self.lo >> (8u32 * i)) as u8
        } else {
            (self.hi >> (8u32 * (i - 8))) as u8
        }
    }
}

// ── ValType (VERBATIM, wasm/encode.rs:54-72) ────────────────────────────────
#[derive(Clone, Copy)]
enum ValType {
    I32,
    I64,
    F32,
    F64,
}

impl ValType {
    /// The single-byte encoding of this value type.  [wasm/encode.rs:64]
    fn code(self) -> u8 {
        match self {
            ValType::I32 => 0x7f,
            ValType::I64 => 0x7e,
            ValType::F32 => 0x7d,
            ValType::F64 => 0x7c,
        }
    }
}

// ── ExportKind (VERBATIM, wasm/encode.rs:93-104) ────────────────────────────
#[derive(Clone, Copy)]
enum ExportKind {
    Func,
}

impl ExportKind {
    /// The export-descriptor kind byte.  [wasm/encode.rs:99]
    fn code(self) -> u8 {
        match self {
            ExportKind::Func => 0x00,
        }
    }
}

// ── write_uleb128 / write_sleb128 (VERBATIM callees, sink=LebBuf per boundary A) ──
//    [ROUND-28 verified — present only as callees of the emit_* functions; NOT re-counted]

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

/// Append a signed LEB128 encoding of `value` to `buf`.  [wasm/encode.rs:38]
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

// ── the NET-NEW instruction OPCODE encoders (VERBATIM, wasm/encode.rs:495-511) ──

/// Append a `local.get $idx` instruction to an instruction buffer.  [wasm/encode.rs:495]
fn emit_local_get(code: &mut LebBuf, idx: u32) {
    code.push(LOCAL_GET);
    // production: write_uleb128(code, u64::from(idx));  [boundary D: `u64::from(u32)`
    // lowers to a `core::convert::num::<impl From>::from` extern leaf UNRESOLVED at JIT
    // link — the emit still validates clean (a call is emitted). `idx as u64` is the
    // value-identical zero-extension.]
    write_uleb128(code, idx as u64);
}

/// Append an `i32.const $value` instruction to an instruction buffer.  [wasm/encode.rs:501]
fn emit_i32_const(code: &mut LebBuf, value: i32) {
    code.push(I32_CONST);
    // production: write_sleb128(code, i64::from(value));  [boundary D: `i64::from(i32)`
    // is likewise an unresolved From leaf at JIT link. `value as i64` is the
    // value-identical sign-extension.]
    write_sleb128(code, value as i64);
}

/// Append a load/store `memarg` immediate: alignment exponent (log2 of the
/// alignment in bytes) and a static byte offset, both ULEB128.  [wasm/encode.rs:508]
fn emit_memarg(code: &mut LebBuf, align_exponent: u32, offset: u32) {
    // production: write_uleb128(code, u64::from(align_exponent));  [boundary D]
    write_uleb128(code, align_exponent as u64);
    // production: write_uleb128(code, u64::from(offset));  [boundary D]
    write_uleb128(code, offset as u64);
}

// ── section-TAG / header assembly (VERBATIM, wasm/encode.rs) ─────────────────

/// Write a section: id byte, ULEB128 length prefix, then the body.  [wasm/encode.rs:318]
/// (production `out.extend_from_slice(body)` for the `&[u8]` body is modeled as the
/// byte-identical `while` copy over the LebBuf sink — boundary A.)
fn push_section(out: &mut LebBuf, id: u8, body: &LebBuf) {
    out.push(id);
    write_uleb128(out, body.len as u64); // production: body.len() as u64
    // production: out.extend_from_slice(body);
    let mut i = 0u32;
    while i < body.len {
        out.push(body.byte_at(i));
        i += 1;
    }
}

/// The `finish()` prologue: module MAGIC "\0asm" + version 1.  [wasm/encode.rs:192-195]
/// (production `out.extend_from_slice(&[..])` array literals modeled as the individual
/// `out.push(_)` calls they expand to — boundary A.)
fn wasm_header(out: &mut LebBuf) {
    // out.extend_from_slice(&[0x00, 0x61, 0x73, 0x6d]);  // "\0asm"
    out.push(0x00);
    out.push(0x61);
    out.push(0x73);
    out.push(0x6d);
    // out.extend_from_slice(&[0x01, 0x00, 0x00, 0x00]);  // version 1
    out.push(0x01);
    out.push(0x00);
    out.push(0x00);
    out.push(0x00);
}

// ── harness adapter roots (NOT production) ──────────────────────────────────

#[repr(C)]
pub struct EncOut {
    pub lo: u64,
    pub hi: u64,
    pub len: u32,
}

#[unsafe(no_mangle)]
pub extern "C" fn valtype_code_root(which: u32) -> u32 {
    let vt = match which {
        0 => ValType::I32,
        1 => ValType::I64,
        2 => ValType::F32,
        _ => ValType::F64,
    };
    vt.code() as u32
}

#[unsafe(no_mangle)]
pub extern "C" fn export_kind_code_root(_which: u32) -> u32 {
    ExportKind::Func.code() as u32
}

#[unsafe(no_mangle)]
pub extern "C" fn emit_local_get_root(idx: u32, out: *mut EncOut) {
    let mut buf = LebBuf::new();
    emit_local_get(&mut buf, idx);
    unsafe {
        (*out).lo = buf.lo;
        (*out).hi = buf.hi;
        (*out).len = buf.len;
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn emit_i32_const_root(value: i32, out: *mut EncOut) {
    let mut buf = LebBuf::new();
    emit_i32_const(&mut buf, value);
    unsafe {
        (*out).lo = buf.lo;
        (*out).hi = buf.hi;
        (*out).len = buf.len;
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn emit_memarg_root(align_exp: u32, offset: u32, out: *mut EncOut) {
    let mut buf = LebBuf::new();
    emit_memarg(&mut buf, align_exp, offset);
    unsafe {
        (*out).lo = buf.lo;
        (*out).hi = buf.hi;
        (*out).len = buf.len;
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn push_section_root(
    id: u32,
    body_lo: u64,
    body_hi: u64,
    body_len: u32,
    out: *mut EncOut,
) {
    let body = LebBuf {
        lo: body_lo,
        hi: body_hi,
        len: body_len,
    };
    let mut buf = LebBuf::new();
    push_section(&mut buf, id as u8, &body);
    unsafe {
        (*out).lo = buf.lo;
        (*out).hi = buf.hi;
        (*out).len = buf.len;
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn wasm_header_root(out: *mut EncOut) {
    let mut buf = LebBuf::new();
    wasm_header(&mut buf);
    unsafe {
        (*out).lo = buf.lo;
        (*out).hi = buf.hi;
        (*out).len = buf.len;
    }
}

fn main() {
    let mut o = EncOut {
        lo: 0,
        hi: 0,
        len: 0,
    };
    emit_local_get_root(128, &mut o);
    println!("local.get 128 lo={:#x} len={}", o.lo, o.len);
    emit_i32_const_root(-1, &mut o);
    println!("i32.const -1 lo={:#x} len={}", o.lo, o.len);
    println!("valtype i32 = {:#x}", valtype_code_root(0));
}
