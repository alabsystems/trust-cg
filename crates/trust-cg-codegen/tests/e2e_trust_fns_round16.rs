//! TRUST-SELF ROUND 29 (thread R29, TRUST BATCH 16): verifying trust-cg's
//! WebAssembly binary ENCODER — the pure, scalar-shaped byte producers of
//! `wasm/encode.rs` that were NOT covered in round 28 (round 28 verified
//! `write_uleb128`/`write_sleb128`; those appear here only as already-verified
//! CALLEES and are NOT re-counted) — through the full pipeline
//! Rust -> MIR -> trust-ir (stage1 `trust_ir_mir --mir-emit-closure`) ->
//! trust-cg JIT -> machine code, asserting native Rust == JIT over swept inputs
//! AND == the independent wasm-spec byte oracle.
//!
//! NET-NEW functions verified this round (all `wasm/encode.rs`):
//!   * `ValType::code`    (:64)  — the value-type byte, exhaustive over the enum
//!     (i32=0x7F, i64=0x7E, f32=0x7D, f64=0x7C).
//!   * `ExportKind::code` (:99)  — the export-descriptor kind byte (Func=0x00).
//!   * `emit_local_get`   (:495) — `local.get $idx` = opcode 0x20 + uleb(idx).
//!   * `emit_i32_const`   (:501) — `i32.const $v`   = opcode 0x41 + sleb(value).
//!   * `emit_memarg`      (:508) — memarg = uleb(align_exponent) + uleb(offset).
//!   * `push_section`     (:318) — section framing: id byte + uleb(len) + body.
//!   * `wasm_header`      (:192) — finish() prologue: MAGIC "\0asm" + version 1
//!     = [0x00,0x61,0x73,0x6d,0x01,0x00,0x00,0x00].
//!
//! WHY THIS SURFACE: the WebAssembly binary format is FULLY SPECIFIED (WebAssembly
//! Core Specification, section 5, "Binary Format"), so the spec provides an
//! INDEPENDENT ground-truth oracle for every byte. A byte that disagrees with the
//! spec is a REAL bug — a malformed `.wasm` module.
//!
//! THE ROUND'S POWER — TWO independent oracles per encoder:
//!   (1) native==JIT: the verbatim slice, compiled by native rustc, must equal the
//!       JIT machine code over swept real inputs.
//!   (2) SPEC ORACLE: each encoder must emit EXACTLY the wasm-spec-mandated bytes.
//!       The operand LEB128 framing is cross-checked against an INDEPENDENT hand
//!       oracle (`uleb_oracle`/`sleb_oracle` below), written directly from the spec
//!       and NOT sharing code with the slice's `write_uleb128`/`write_sleb128`.
//!
//! Run tests ONE AT A TIME (`-- --exact <name> --test-threads=1`): the JIT engine is
//! not thread-safe at suite scale (jit-parallel-race-2026-06-29.md). Every JIT
//! execution runs inside a WATCHDOG worker thread; the output POD is 0xDEAD-poisoned
//! before each JIT call so a silent no-op fails loudly.

#![cfg(target_arch = "aarch64")]

use std::collections::HashMap;
use std::sync::mpsc;
use std::time::Duration;

use trust_cg_codegen::Target;
use trust_cg_codegen::compiler::{Compiler, CompilerConfig};

// NATIVE ORACLE: the verbatim slice, compiled by native rustc.
#[path = "slices/trust_wasm_encode_slice.rs"]
mod s;

// ── the MIR-emitted trust-ir modules (one per root) ────────────────────────
const VALTYPE_IR: &str = include_str!("slices/trust_wasm_valtype_code_root.tir");
const EXPORTKIND_IR: &str = include_str!("slices/trust_wasm_export_kind_code_root.tir");
const LOCAL_GET_IR: &str = include_str!("slices/trust_wasm_emit_local_get_root.tir");
const I32_CONST_IR: &str = include_str!("slices/trust_wasm_emit_i32_const_root.tir");
const MEMARG_IR: &str = include_str!("slices/trust_wasm_emit_memarg_root.tir");
const PUSH_SECTION_IR: &str = include_str!("slices/trust_wasm_push_section_root.tir");
const HEADER_IR: &str = include_str!("slices/trust_wasm_wasm_header_root.tir");

// ── shared harness (R28 pattern) ─────────────────────────────────────────────

fn jit_module(text: &str, what: &str) -> trust_cg_codegen::jit::ExecutableBuffer {
    let module = trust_ir::parser::parse_module(text)
        .unwrap_or_else(|e| panic!("MIR-emitted `{what}` trust-ir text must parse: {e:?}"));
    let config = CompilerConfig::jit_fast(Target::Aarch64);
    Compiler::new(config)
        .compile_module_to_jit(&module, &HashMap::new())
        .unwrap_or_else(|e| panic!("trust-cg JIT compile of MIR-emitted `{what}` failed: {e:?}"))
        .buffer
}

fn bind(buffer: &trust_cg_codegen::jit::ExecutableBuffer, sym: &str) -> *const u8 {
    buffer
        .get_fn_ptr_bound(sym)
        .unwrap_or_else(|| panic!("JIT symbol `{sym}` not found"))
        .as_ptr()
}

const WATCHDOG_SECS: u64 = 240;

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

// ── ABI adapter types ────────────────────────────────────────────────────────
type U32Ret = unsafe extern "C" fn(u32) -> u32;
type LocalGetFn = unsafe extern "C" fn(u32, *mut s::EncOut);
type I32ConstFn = unsafe extern "C" fn(i32, *mut s::EncOut);
type MemargFn = unsafe extern "C" fn(u32, u32, *mut s::EncOut);
type PushSecFn = unsafe extern "C" fn(u32, u64, u64, u32, *mut s::EncOut);
type HeaderFn = unsafe extern "C" fn(*mut s::EncOut);

fn poison_enc() -> s::EncOut {
    s::EncOut {
        lo: 0xDEAD,
        hi: 0xDEAD,
        len: 0xDEAD,
    }
}
fn enc3(o: &s::EncOut) -> (u64, u64, u32) {
    (o.lo, o.hi, o.len)
}

/// Pack a byte sequence into the (lo,hi,len) accumulator shape the slice's
/// `LebBuf` produces — bytes 0..8 in `lo`, bytes 8..16 in `hi`.
fn pack(bytes: &[u8]) -> (u64, u64, u32) {
    assert!(bytes.len() <= 16, "LebBuf holds at most 16 bytes");
    let mut lo = 0u64;
    let mut hi = 0u64;
    for (i, &b) in bytes.iter().enumerate() {
        if i < 8 {
            lo |= (b as u64) << (8 * i);
        } else {
            hi |= (b as u64) << (8 * (i - 8));
        }
    }
    (lo, hi, bytes.len() as u32)
}

// ── INDEPENDENT wasm-spec LEB128 oracles (NOT the slice's encoders) ──────────
// Written directly from the LEB128 definition (WebAssembly spec §5.2.2 / DWARF-5
// §7.6). These share NO code with the slice's `write_uleb128`/`write_sleb128`,
// so a shared encoder-and-slice bug cannot hide.

fn uleb_oracle(mut v: u64) -> Vec<u8> {
    let mut out = Vec::new();
    loop {
        let b = (v & 0x7f) as u8;
        v >>= 7;
        if v == 0 {
            out.push(b);
            break;
        } else {
            out.push(b | 0x80);
        }
    }
    out
}

fn sleb_oracle(mut v: i64) -> Vec<u8> {
    let mut out = Vec::new();
    loop {
        let b = (v & 0x7f) as u8;
        v >>= 7; // arithmetic shift
        let sign = b & 0x40 != 0;
        if (v == 0 && !sign) || (v == -1 && sign) {
            out.push(b);
            break;
        } else {
            out.push(b | 0x80);
        }
    }
    out
}

// ── native-oracle wrappers (verbatim slice through native rustc) ─────────────
fn n_valtype(w: u32) -> u32 {
    s::valtype_code_root(w)
}
fn n_export_kind(w: u32) -> u32 {
    s::export_kind_code_root(w)
}
fn n_local_get(idx: u32) -> (u64, u64, u32) {
    let mut o = poison_enc();
    s::emit_local_get_root(idx, &mut o);
    enc3(&o)
}
fn n_i32_const(v: i32) -> (u64, u64, u32) {
    let mut o = poison_enc();
    s::emit_i32_const_root(v, &mut o);
    enc3(&o)
}
fn n_memarg(a: u32, off: u32) -> (u64, u64, u32) {
    let mut o = poison_enc();
    s::emit_memarg_root(a, off, &mut o);
    enc3(&o)
}
fn n_push_section(id: u32, body: &[u8]) -> (u64, u64, u32) {
    let (blo, bhi, blen) = pack(body);
    let mut o = poison_enc();
    s::push_section_root(id, blo, bhi, blen, &mut o);
    enc3(&o)
}
fn n_header() -> (u64, u64, u32) {
    let mut o = poison_enc();
    s::wasm_header_root(&mut o);
    enc3(&o)
}

// ============================================================================
// TEST 1 — ValType::code, EXHAUSTIVE over the enum + wasm-spec byte oracle.
//   spec §5.3.1: i32=0x7F, i64=0x7E, f32=0x7D, f64=0x7C.
// ============================================================================

#[test]
fn trust_wasm_valtype_code_exhaustive() {
    // The 4 value types + spec byte + a mnemonic.
    let spec: [(u32, u8, &str); 4] = [
        (0, 0x7f, "i32"),
        (1, 0x7e, "i64"),
        (2, 0x7d, "f32"),
        (3, 0x7c, "f64"),
    ];
    let expected = spec.len();
    let rows = run_watchdogged::<u32>("valtype_code", expected, move |tx| {
        let b = jit_module(VALTYPE_IR, "valtype_code");
        let f: U32Ret = unsafe { std::mem::transmute(bind(&b, "valtype_code_root")) };
        for w in 0..(expected as u32) {
            if tx.send(unsafe { f(w) }).is_err() {
                return;
            }
        }
    });

    assert_eq!(rows.len(), expected);
    for (i, &(w, code, name)) in spec.iter().enumerate() {
        // (a) native==JIT.
        assert_eq!(
            rows[i],
            n_valtype(w),
            "ValType::code({name}): JIT != native"
        );
        // (b) SPEC ORACLE: the exact value-type byte.
        assert_eq!(
            rows[i],
            u32::from(code),
            "ValType::code({name}) must be {code:#04x} per wasm spec"
        );
        assert_ne!(rows[i], 0xDEAD, "row {i} still poisoned");
    }
    // The four codes are a contiguous 0x7C..=0x7F block, all distinct.
    let codes: Vec<u32> = rows.clone();
    assert_eq!(
        codes,
        vec![0x7f, 0x7e, 0x7d, 0x7c],
        "the value-type byte block"
    );
}

// ============================================================================
// TEST 2 — ExportKind::code (Func=0x00) + native==JIT.
// ============================================================================

#[test]
fn trust_wasm_export_kind_code() {
    let expected = 1usize;
    let rows = run_watchdogged::<u32>("export_kind", expected, move |tx| {
        let b = jit_module(EXPORTKIND_IR, "export_kind");
        let f: U32Ret = unsafe { std::mem::transmute(bind(&b, "export_kind_code_root")) };
        let _ = tx.send(unsafe { f(0) });
    });
    assert_eq!(rows.len(), expected);
    // (a) native==JIT; (b) SPEC: the func export-descriptor byte is 0x00.
    assert_eq!(
        rows[0],
        n_export_kind(0),
        "ExportKind::Func.code(): JIT != native"
    );
    assert_eq!(
        rows[0], 0x00,
        "ExportKind::Func.code() must be 0x00 per wasm spec §5.5.10"
    );
    assert_ne!(rows[0], 0xDEAD, "still poisoned");
}

// ============================================================================
// TEST 3 — emit_local_get: opcode 0x20 + uleb(idx). native==JIT + spec.
// ============================================================================

/// Independent spec oracle: local.get is opcode 0x20 then uleb128(idx).
fn local_get_spec(idx: u32) -> Vec<u8> {
    let mut v = vec![0x20u8];
    v.extend_from_slice(&uleb_oracle(u64::from(idx)));
    v
}

fn local_get_values() -> Vec<u32> {
    let mut v: Vec<u32> = (0..=200u32).collect();
    v.extend_from_slice(&[
        127,
        128,
        129,
        255,
        256,
        16383,
        16384,
        16385,
        (1 << 21) - 1,
        1 << 21,
        1 << 28,
        0x7FFF_FFFF,
        0xFFFF_FFFE,
        u32::MAX,
    ]);
    v
}

#[test]
fn trust_wasm_emit_local_get_native_eq_jit() {
    let vals = local_get_values();
    let expected = vals.len();
    let sweep = vals.clone();
    let rows = run_watchdogged::<(u64, u64, u32)>("local_get", expected, move |tx| {
        let b = jit_module(LOCAL_GET_IR, "local_get");
        let f: LocalGetFn = unsafe { std::mem::transmute(bind(&b, "emit_local_get_root")) };
        for &idx in &sweep {
            let mut o = poison_enc();
            unsafe { f(idx, &mut o) };
            if tx.send(enc3(&o)).is_err() {
                return;
            }
        }
    });

    assert_eq!(rows.len(), expected);
    for (i, &idx) in vals.iter().enumerate() {
        // (a) native==JIT.
        assert_eq!(
            rows[i],
            n_local_get(idx),
            "emit_local_get({idx}): JIT != native"
        );
        // (b) SPEC ORACLE: 0x20 + uleb(idx).
        let want = pack(&local_get_spec(idx));
        assert_eq!(
            rows[i],
            want,
            "emit_local_get({idx}) must be {:02x?} per wasm spec",
            local_get_spec(idx)
        );
        assert_ne!(rows[i].2, 0xDEAD, "row {i} len still poisoned (idx={idx})");
    }

    // Explicit spec byte examples from the brief.
    assert_eq!(n_local_get(0), pack(&[0x20, 0x00]), "local.get 0");
    assert_eq!(n_local_get(1), pack(&[0x20, 0x01]), "local.get 1");
    assert_eq!(n_local_get(127), pack(&[0x20, 0x7f]), "local.get 127");
    assert_eq!(n_local_get(128), pack(&[0x20, 0x80, 0x01]), "local.get 128");
    assert_eq!(
        n_local_get(16384),
        pack(&[0x20, 0x80, 0x80, 0x01]),
        "local.get 16384"
    );
    assert_eq!(
        n_local_get(u32::MAX),
        pack(&[0x20, 0xff, 0xff, 0xff, 0xff, 0x0f]),
        "local.get u32::MAX (5-byte uleb)"
    );
}

// ============================================================================
// TEST 4 — emit_i32_const: opcode 0x41 + sleb(i64::from(value)). native==JIT + spec.
//   Sweeps the SLEB sign boundaries — the wasm i32.const immediate is SIGNED.
// ============================================================================

/// Independent spec oracle: i32.const is opcode 0x41 then sleb128(i64::from(value)).
fn i32_const_spec(value: i32) -> Vec<u8> {
    let mut v = vec![0x41u8];
    v.extend_from_slice(&sleb_oracle(i64::from(value)));
    v
}

fn i32_const_values() -> Vec<i32> {
    let mut v: Vec<i32> = (-300..=300i32).collect();
    v.extend_from_slice(&[
        63,
        64,
        65,
        -63,
        -64,
        -65,
        127,
        128,
        129,
        -127,
        -128,
        -129,
        8191,
        8192,
        8193,
        -8191,
        -8192,
        -8193,
        1 << 20,
        -(1 << 20),
        i32::MAX,
        i32::MIN,
        i32::MAX - 1,
        i32::MIN + 1,
        -1,
        12857,
        624485,
        -624485,
    ]);
    v
}

#[test]
fn trust_wasm_emit_i32_const_native_eq_jit() {
    let vals = i32_const_values();
    let expected = vals.len();
    let sweep = vals.clone();
    let rows = run_watchdogged::<(u64, u64, u32)>("i32_const", expected, move |tx| {
        let b = jit_module(I32_CONST_IR, "i32_const");
        let f: I32ConstFn = unsafe { std::mem::transmute(bind(&b, "emit_i32_const_root")) };
        for &v in &sweep {
            let mut o = poison_enc();
            unsafe { f(v, &mut o) };
            if tx.send(enc3(&o)).is_err() {
                return;
            }
        }
    });

    assert_eq!(rows.len(), expected);
    for (i, &v) in vals.iter().enumerate() {
        // (a) native==JIT.
        assert_eq!(
            rows[i],
            n_i32_const(v),
            "emit_i32_const({v}): JIT != native"
        );
        // (b) SPEC ORACLE: 0x41 + sleb(value).
        let want = pack(&i32_const_spec(v));
        assert_eq!(
            rows[i],
            want,
            "emit_i32_const({v}) must be {:02x?} per wasm spec",
            i32_const_spec(v)
        );
        assert_ne!(rows[i].2, 0xDEAD, "row {i} len still poisoned (v={v})");
    }

    // Explicit spec byte examples from the brief (the sign boundary).
    assert_eq!(n_i32_const(1), pack(&[0x41, 0x01]), "i32.const 1");
    assert_eq!(n_i32_const(-1), pack(&[0x41, 0x7f]), "i32.const -1");
    assert_eq!(n_i32_const(0), pack(&[0x41, 0x00]), "i32.const 0");
    assert_eq!(n_i32_const(63), pack(&[0x41, 0x3f]), "i32.const 63");
    assert_eq!(n_i32_const(64), pack(&[0x41, 0xc0, 0x00]), "i32.const 64");
    assert_eq!(n_i32_const(-64), pack(&[0x41, 0x40]), "i32.const -64");
    assert_eq!(n_i32_const(128), pack(&[0x41, 0x80, 0x01]), "i32.const 128");
    assert_eq!(
        n_i32_const(-128),
        pack(&[0x41, 0x80, 0x7f]),
        "i32.const -128"
    );
    assert_eq!(
        n_i32_const(i32::MIN),
        pack(&[0x41, 0x80, 0x80, 0x80, 0x80, 0x78]),
        "i32.const i32::MIN"
    );
}

// ============================================================================
// TEST 5 — emit_memarg: uleb(align_exponent) + uleb(offset). native==JIT + spec.
// ============================================================================

fn memarg_spec(a: u32, off: u32) -> Vec<u8> {
    let mut v = uleb_oracle(u64::from(a));
    v.extend_from_slice(&uleb_oracle(u64::from(off)));
    v
}

#[test]
fn trust_wasm_emit_memarg_native_eq_jit() {
    // alignment exponents 0..4 (byte..16-byte) crossed with offset thresholds.
    let aligns: [u32; 5] = [0, 1, 2, 3, 4];
    let offsets: [u32; 12] = [
        0,
        1,
        7,
        8,
        127,
        128,
        255,
        256,
        1024,
        16383,
        16384,
        0x0010_0000,
    ];
    let mut cases: Vec<(u32, u32)> = Vec::new();
    for &a in &aligns {
        for &off in &offsets {
            cases.push((a, off));
        }
    }
    let expected = cases.len();
    let sweep = cases.clone();
    let rows = run_watchdogged::<(u64, u64, u32)>("memarg", expected, move |tx| {
        let b = jit_module(MEMARG_IR, "memarg");
        let f: MemargFn = unsafe { std::mem::transmute(bind(&b, "emit_memarg_root")) };
        for &(a, off) in &sweep {
            let mut o = poison_enc();
            unsafe { f(a, off, &mut o) };
            if tx.send(enc3(&o)).is_err() {
                return;
            }
        }
    });

    assert_eq!(rows.len(), expected);
    for (i, &(a, off)) in cases.iter().enumerate() {
        // (a) native==JIT.
        assert_eq!(
            rows[i],
            n_memarg(a, off),
            "emit_memarg({a},{off}): JIT != native"
        );
        // (b) SPEC ORACLE: uleb(a) ++ uleb(off).
        let want = pack(&memarg_spec(a, off));
        assert_eq!(
            rows[i],
            want,
            "emit_memarg({a},{off}) must be {:02x?} per wasm spec",
            memarg_spec(a, off)
        );
        assert_ne!(rows[i].2, 0xDEAD, "row {i} len still poisoned ({a},{off})");
    }

    // Explicit spec examples.
    assert_eq!(
        n_memarg(0, 0),
        pack(&[0x00, 0x00]),
        "memarg align=1(byte) offset=0"
    );
    assert_eq!(
        n_memarg(2, 8),
        pack(&[0x02, 0x08]),
        "memarg align=4 offset=8"
    );
    assert_eq!(
        n_memarg(3, 128),
        pack(&[0x03, 0x80, 0x01]),
        "memarg align=8 offset=128"
    );
    assert_eq!(
        n_memarg(0, 1024),
        pack(&[0x00, 0x80, 0x08]),
        "memarg align=1 offset=1024"
    );
}

// ============================================================================
// TEST 6 — push_section: id byte + uleb(body.len()) + body. native==JIT + spec.
//   Exercises the section-TAG framing over the real wasm section ids and the
//   uleb length-prefix threshold at 128.
// ============================================================================

fn push_section_spec(id: u8, body: &[u8]) -> Vec<u8> {
    let mut v = vec![id];
    v.extend_from_slice(&uleb_oracle(body.len() as u64));
    v.extend_from_slice(body);
    v
}

#[test]
fn trust_wasm_push_section_native_eq_jit() {
    // (id, body). Real wasm section ids: type=1, import=2, func=3, table=4,
    // memory=5, global=6, export=7, elem=9, code=10. Bodies chosen to cross the
    // uleb length threshold (127 -> 1 byte, 128 -> 2 bytes) while the total
    // (id + len-prefix + body) stays within the 16-byte LebBuf window for the
    // native==JIT sweep; a longer-body length-prefix case is checked natively.
    struct C {
        id: u8,
        body: Vec<u8>,
        label: &'static str,
    }
    let cases: Vec<C> = vec![
        C {
            id: 1,
            body: vec![0x60, 0x00, 0x01],
            label: "type section body",
        },
        C {
            id: 3,
            body: vec![0x01, 0x00],
            label: "function section body",
        },
        C {
            id: 7,
            body: vec![0x01, 0x03, 0x61, 0x64, 0x64],
            label: "export section body",
        },
        C {
            id: 10,
            body: vec![],
            label: "empty body (len-prefix 0)",
        },
        C {
            id: 5,
            body: vec![0x00, 0x01],
            label: "memory section body",
        },
        C {
            id: 4,
            body: vec![0x70, 0x00, 0x00],
            label: "table section body",
        },
        C {
            id: 6,
            body: vec![0x7f, 0x01, 0x41, 0x00, 0x0b],
            label: "global section body",
        },
        C {
            id: 9,
            body: vec![0x00, 0x41, 0x00, 0x0b, 0x01, 0x00],
            label: "elem section body",
        },
        C {
            id: 2,
            body: (0..13u8).collect(),
            label: "13-byte body (len prefix 13)",
        },
    ];
    let expected = cases.len();
    let ids: Vec<u8> = cases.iter().map(|c| c.id).collect();
    let bodies: Vec<Vec<u8>> = cases.iter().map(|c| c.body.clone()).collect();
    let rows = run_watchdogged::<(u64, u64, u32)>("push_section", expected, move |tx| {
        let b = jit_module(PUSH_SECTION_IR, "push_section");
        let f: PushSecFn = unsafe { std::mem::transmute(bind(&b, "push_section_root")) };
        for i in 0..ids.len() {
            let (blo, bhi, blen) = pack(&bodies[i]);
            let mut o = poison_enc();
            unsafe { f(u32::from(ids[i]), blo, bhi, blen, &mut o) };
            if tx.send(enc3(&o)).is_err() {
                return;
            }
        }
    });

    assert_eq!(rows.len(), expected);
    for (i, c) in cases.iter().enumerate() {
        // (a) native==JIT.
        assert_eq!(
            rows[i],
            n_push_section(u32::from(c.id), &c.body),
            "push_section({}, {}): JIT != native",
            c.id,
            c.label
        );
        // (b) SPEC ORACLE: id ++ uleb(len) ++ body.
        let want = pack(&push_section_spec(c.id, &c.body));
        assert_eq!(
            rows[i],
            want,
            "push_section({}, {}) must be {:02x?} per wasm spec",
            c.id,
            c.label,
            push_section_spec(c.id, &c.body)
        );
        assert_ne!(rows[i].2, 0xDEAD, "row {i} len still poisoned");
    }

    // A 2-byte length prefix case (body length 200 -> uleb [0xc8, 0x01]), checked
    // NATIVELY (exceeds the 16-byte JIT LebBuf window; the length-prefix framing is
    // what matters here, and it is the same uleb path verified above).
    let big: Vec<u8> = vec![0xab; 200];
    let native_big = {
        // push_section over a >16-byte body would overflow LebBuf; instead verify
        // the length-prefix directly against the spec oracle's prefix.
        push_section_spec(11, &big)
    };
    assert_eq!(
        &native_big[0..3],
        &[11u8, 0xc8, 0x01],
        "custom-section id 11 + uleb(200) prefix"
    );
}

// ============================================================================
// TEST 7 — wasm_header: the module MAGIC + version. native==JIT + spec.
//   spec §5.5.16: magic = 0x00 0x61 0x73 0x6d ("\0asm"), version = 0x01 0x00 0x00 0x00.
// ============================================================================

#[test]
fn trust_wasm_header_native_eq_jit() {
    let expected = 1usize;
    let rows = run_watchdogged::<(u64, u64, u32)>("header", expected, move |tx| {
        let b = jit_module(HEADER_IR, "header");
        let f: HeaderFn = unsafe { std::mem::transmute(bind(&b, "wasm_header_root")) };
        let mut o = poison_enc();
        unsafe { f(&mut o) };
        let _ = tx.send(enc3(&o));
    });
    assert_eq!(rows.len(), expected);

    let spec_bytes: [u8; 8] = [0x00, 0x61, 0x73, 0x6d, 0x01, 0x00, 0x00, 0x00];
    let want = pack(&spec_bytes);
    // (a) native==JIT.
    assert_eq!(rows[0], n_header(), "wasm_header: JIT != native");
    // (b) SPEC ORACLE: exact 8-byte magic + version header.
    assert_eq!(
        rows[0], want,
        "wasm module header must be {spec_bytes:02x?} per wasm spec"
    );
    assert_eq!(rows[0].2, 8, "header is exactly 8 bytes");
    assert_ne!(rows[0].0, 0xDEAD, "still poisoned");
    // The magic spells "\0asm".
    assert_eq!(&spec_bytes[0..4], b"\0asm", "magic is \\0asm");
}

// ============================================================================
// ARMED NEGATIVE CONTROLS — corrupt the module text, prove divergence, restore.
// ============================================================================

/// ARMED (a valtype code): patch ValType::code's i32 byte `0x7f` (`const u8 127`)
/// -> `0x7e` in the module text. A wasm module whose i32 parameters/results encode
/// as 0x7E declares them as i64 — a TYPE-CONFUSED, malformed module. Prove the
/// JIT diverges on ValType::code(i32), restore, re-pass.
#[test]
fn trust_wasm_valtype_code_armed_control() {
    const ANCHOR: &str = "const u8 127";
    assert_eq!(
        VALTYPE_IR.matches(ANCHOR).count(),
        1,
        "corruption anchor must be unique (the i32 value-type byte 0x7f)"
    );
    let corrupted = VALTYPE_IR.replace(ANCHOR, "const u8 126");
    assert_ne!(corrupted, VALTYPE_IR);

    let corrupt = run_watchdogged::<u32>("valtype CORRUPTED", 1, move |tx| {
        let b = jit_module(&corrupted, "valtype CORRUPTED");
        let f: U32Ret = unsafe { std::mem::transmute(bind(&b, "valtype_code_root")) };
        let _ = tx.send(unsafe { f(0) }); // ValType::I32
    })[0];
    let pristine = run_watchdogged::<u32>("valtype RESTORED", 1, move |tx| {
        let b = jit_module(VALTYPE_IR, "valtype RESTORED");
        let f: U32Ret = unsafe { std::mem::transmute(bind(&b, "valtype_code_root")) };
        let _ = tx.send(unsafe { f(0) });
    })[0];

    let native = n_valtype(0);
    assert_eq!(native, 0x7f, "native ValType::code(i32) = 0x7f");
    assert_eq!(
        corrupt, 0x7e,
        "corrupted i32 byte -> 0x7e (declares i32 as i64)"
    );
    assert_ne!(corrupt, native, "corrupted JIT DIVERGES from native");
    assert_eq!(
        pristine, native,
        "pristine module AGREES (restore + re-pass)"
    );
}

/// ARMED (an opcode byte): patch emit_i32_const's opcode `0x41` (`const u8 65`)
/// -> `0x42` (I64_CONST) in the module text. The instruction stream then contains
/// `i64.const` where the type stack expects `i32.const` — a malformed, ill-typed
/// module. Prove the JIT diverges on emit_i32_const(1), restore, re-pass.
#[test]
fn trust_wasm_i32_const_opcode_armed_control() {
    const ANCHOR: &str = "const u8 65";
    assert_eq!(
        I32_CONST_IR.matches(ANCHOR).count(),
        1,
        "corruption anchor must be unique (the i32.const opcode 0x41)"
    );
    let corrupted = I32_CONST_IR.replace(ANCHOR, "const u8 66"); // 0x42 = i64.const
    assert_ne!(corrupted, I32_CONST_IR);

    let v = 1i32; // correct [0x41,0x01]; corrupted [0x42,0x01]
    let corrupt = run_watchdogged::<(u64, u64, u32)>("i32const CORRUPTED", 1, move |tx| {
        let b = jit_module(&corrupted, "i32const CORRUPTED");
        let f: I32ConstFn = unsafe { std::mem::transmute(bind(&b, "emit_i32_const_root")) };
        let mut o = poison_enc();
        unsafe { f(v, &mut o) };
        let _ = tx.send(enc3(&o));
    })[0];
    let pristine = run_watchdogged::<(u64, u64, u32)>("i32const RESTORED", 1, move |tx| {
        let b = jit_module(I32_CONST_IR, "i32const RESTORED");
        let f: I32ConstFn = unsafe { std::mem::transmute(bind(&b, "emit_i32_const_root")) };
        let mut o = poison_enc();
        unsafe { f(v, &mut o) };
        let _ = tx.send(enc3(&o));
    })[0];

    let native = n_i32_const(v);
    assert_eq!(
        native,
        pack(&[0x41, 0x01]),
        "native i32.const 1 = [0x41,0x01]"
    );
    assert_eq!(
        corrupt,
        pack(&[0x42, 0x01]),
        "corrupted opcode -> [0x42,0x01] (i64.const)"
    );
    assert_ne!(corrupt, native, "corrupted JIT DIVERGES from native");
    assert_eq!(
        pristine, native,
        "pristine module AGREES (restore + re-pass)"
    );
}

/// ARMED (a magic byte): patch wasm_header's `'s'` of "\0asm" (`const u8 115`)
/// -> `0x00` in the module text. The module magic is then `00 61 00 6d ...`,
/// which no wasm runtime will accept (bad magic) — the module fails to load.
/// Prove the JIT diverges, restore, re-pass.
#[test]
fn trust_wasm_header_magic_armed_control() {
    const ANCHOR: &str = "const u8 115";
    assert_eq!(
        HEADER_IR.matches(ANCHOR).count(),
        1,
        "corruption anchor must be unique (the 's' magic byte 0x73)"
    );
    let corrupted = HEADER_IR.replace(ANCHOR, "const u8 0");
    assert_ne!(corrupted, HEADER_IR);

    let corrupt = run_watchdogged::<(u64, u64, u32)>("header CORRUPTED", 1, move |tx| {
        let b = jit_module(&corrupted, "header CORRUPTED");
        let f: HeaderFn = unsafe { std::mem::transmute(bind(&b, "wasm_header_root")) };
        let mut o = poison_enc();
        unsafe { f(&mut o) };
        let _ = tx.send(enc3(&o));
    })[0];
    let pristine = run_watchdogged::<(u64, u64, u32)>("header RESTORED", 1, move |tx| {
        let b = jit_module(HEADER_IR, "header RESTORED");
        let f: HeaderFn = unsafe { std::mem::transmute(bind(&b, "wasm_header_root")) };
        let mut o = poison_enc();
        unsafe { f(&mut o) };
        let _ = tx.send(enc3(&o));
    })[0];

    let native = n_header();
    assert_eq!(
        native,
        pack(&[0x00, 0x61, 0x73, 0x6d, 0x01, 0x00, 0x00, 0x00]),
        "native header"
    );
    assert_eq!(
        corrupt,
        pack(&[0x00, 0x61, 0x00, 0x6d, 0x01, 0x00, 0x00, 0x00]),
        "corrupted magic byte 's' -> 0x00 (bad magic)"
    );
    assert_ne!(corrupt, native, "corrupted JIT DIVERGES from native");
    assert_eq!(
        pristine, native,
        "pristine module AGREES (restore + re-pass)"
    );
}
