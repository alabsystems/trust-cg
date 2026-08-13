//! TRUST-SELF ROUND 28 (thread R28, TRUST BATCH 15): verifying trust-cg's
//! LEB128 + DWARF-CFI byte machinery — the `.eh_frame`/`__eh_frame` UNWIND-TABLE
//! encoders (`dwarf_cfi.rs::{encode_uleb128,encode_sleb128,encode_advance_loc,
//! encode_advance_loc_bytes,pointer_encoding_size}` + `wasm/encode.rs::{write_uleb128,
//! write_sleb128}`) and the eh_frame LEB128 DECODERS (`dwarf_cfi_decode_check.rs::
//! Reader::{uleb128,sleb128}`) — through the full pipeline Rust -> MIR -> trust-ir
//! (stage1 `trust_ir_mir --mir-emit-closure`) -> trust-cg JIT -> machine code,
//! asserting native Rust == JIT over swept real inputs.
//!
//! WHY THIS SURFACE: a wrong LEB128 byte or a wrong DW_CFA opcode byte produces a
//! CORRUPT unwind table — broken stack unwinding / exception handling at runtime.
//! These are the soundness-relevant pure byte producers/consumers of the DWARF path.
//!
//! THE ROUND'S POWER — THREE INDEPENDENT ORACLES per LEB128 value:
//!   (1) native==JIT: the verbatim slice, compiled by native rustc, must equal the JIT.
//!   (2) ENCODE<->DECODE ROUND-TRIP: decode(encode(v)) == v over a swept value set. An
//!       asymmetry between an `encode_*` and its `Reader::*` decoder is a REAL bug (a
//!       wrong unwind table). ALSO a CROSS-IMPL differential: the two SLEB encoders are
//!       structurally DIFFERENT (`encode_sleb128` `while more` vs `write_sleb128`
//!       `loop`/`done`) and must produce byte-identical output.
//!   (3) SPEC ORACLE: the DWARF-v5 Appendix C canonical LEB128 byte examples (also
//!       pinned in the production `*_decoder_matches_spec_examples` / `*_examples`
//!       tests) — a third oracle that catches a bug even if BOTH encoder and decoder
//!       share the same mistake.
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
#[path = "slices/trust_leb128_cfi_slice.rs"]
mod s;

// ── the MIR-emitted trust-ir modules (one per root) ────────────────────────
const ENC_ULEB_IR: &str = include_str!("slices/trust_leb128_enc_uleb_root.tir");
const ENC_SLEB_IR: &str = include_str!("slices/trust_leb128_enc_sleb_root.tir");
const WASM_ULEB_IR: &str = include_str!("slices/trust_leb128_wasm_uleb_root.tir");
const WASM_SLEB_IR: &str = include_str!("slices/trust_leb128_wasm_sleb_root.tir");
const ADV_LOC_IR: &str = include_str!("slices/trust_leb128_adv_loc_root.tir");
const ADV_LOC_BYTES_IR: &str = include_str!("slices/trust_leb128_adv_loc_bytes_root.tir");
const PTR_ENC_IR: &str = include_str!("slices/trust_leb128_ptr_enc_size_root.tir");
const DEC_ULEB_IR: &str = include_str!("slices/trust_leb128_dec_uleb_root.tir");
const DEC_SLEB_IR: &str = include_str!("slices/trust_leb128_dec_sleb_root.tir");

// ── shared harness (R27 pattern) ────────────────────────────────────────────

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

// ── ABI adapters ────────────────────────────────────────────────────────────
type EncU = unsafe extern "C" fn(u64, *mut s::EncOut);
type EncI = unsafe extern "C" fn(i64, *mut s::EncOut);
type AdvFn = unsafe extern "C" fn(u32, *mut s::EncOut);
type PtrFn = unsafe extern "C" fn(u32) -> u32;
type DecFn = unsafe extern "C" fn(u64, u64, u32, *mut s::DecOut);

fn poison_enc() -> s::EncOut {
    s::EncOut {
        lo: 0xDEAD,
        hi: 0xDEAD,
        len: 0xDEAD,
    }
}
fn poison_dec() -> s::DecOut {
    s::DecOut {
        value: 0xDEAD,
        err: 0xDEAD,
    }
}
fn enc3(o: &s::EncOut) -> (u64, u64, u32) {
    (o.lo, o.hi, o.len)
}
fn dec2(o: &s::DecOut) -> (u64, u32) {
    (o.value, o.err)
}

/// Pack a byte sequence into the (lo,hi,len) accumulator shape.
fn pack(bytes: &[u8]) -> (u64, u64, u32) {
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

// ── native-oracle wrappers (the verbatim slice through native rustc) ─────────
fn n_enc_uleb(v: u64) -> (u64, u64, u32) {
    let mut o = poison_enc();
    s::enc_uleb_root(v, &mut o);
    enc3(&o)
}
fn n_enc_sleb(v: i64) -> (u64, u64, u32) {
    let mut o = poison_enc();
    s::enc_sleb_root(v, &mut o);
    enc3(&o)
}
fn n_wasm_uleb(v: u64) -> (u64, u64, u32) {
    let mut o = poison_enc();
    s::wasm_uleb_root(v, &mut o);
    enc3(&o)
}
fn n_wasm_sleb(v: i64) -> (u64, u64, u32) {
    let mut o = poison_enc();
    s::wasm_sleb_root(v, &mut o);
    enc3(&o)
}
fn n_adv_loc(n: u32) -> (u64, u64, u32) {
    let mut o = poison_enc();
    s::adv_loc_root(n, &mut o);
    enc3(&o)
}
fn n_adv_loc_bytes(n: u32) -> (u64, u64, u32) {
    let mut o = poison_enc();
    s::adv_loc_bytes_root(n, &mut o);
    enc3(&o)
}
fn n_dec_uleb(lo: u64, hi: u64, limit: u32) -> (u64, u32) {
    let mut o = poison_dec();
    s::dec_uleb_root(lo, hi, limit, &mut o);
    dec2(&o)
}
fn n_dec_sleb(lo: u64, hi: u64, limit: u32) -> (u64, u32) {
    let mut o = poison_dec();
    s::dec_sleb_root(lo, hi, limit, &mut o);
    dec2(&o)
}

// ── swept value sets ─────────────────────────────────────────────────────────

/// ULEB inputs: dense small + every byte-length threshold up to u64::MAX.
fn uleb_values() -> Vec<u64> {
    let mut v: Vec<u64> = (0..=300u64).collect();
    let t: [u64; 24] = [
        127,
        128,
        129,
        16383,
        16384,
        16385,
        (1 << 21) - 1,
        1 << 21,
        (1 << 21) + 1,
        (1 << 28) - 1,
        1 << 28,
        (1 << 35) - 1,
        1 << 35,
        1 << 42,
        1 << 49,
        1 << 56,
        1 << 63,
        u64::MAX,
        u64::MAX - 1,
        12857,
        624485,
        300,
        0x7FFF_FFFF,
        0xFFFF_FFFF,
    ];
    v.extend_from_slice(&t);
    v
}

/// SLEB inputs: dense small (both signs) + threshold + the sign boundaries.
fn sleb_values() -> Vec<i64> {
    let mut v: Vec<i64> = (-300..=300i64).collect();
    let t: [i64; 30] = [
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
        i64::MAX,
        i64::MIN,
        i64::MAX - 1,
        i64::MIN + 1,
        -1,
        12857,
        624485,
        -624485,
        1 << 40,
        -(1 << 40),
    ];
    v.extend_from_slice(&t);
    v
}

// ============================================================================
// TEST 1 — ULEB128 ENCODERS (dwarf `encode_uleb128` + wasm `write_uleb128`).
//   native==JIT, SPEC ORACLE, and the dwarf==wasm cross-encoder differential.
// ============================================================================

/// DWARF-v5 App.C / production canonical ULEB128 examples (independent 3rd oracle).
fn uleb_spec() -> Vec<(u64, Vec<u8>)> {
    vec![
        (0, vec![0x00]),
        (1, vec![0x01]),
        (2, vec![0x02]),
        (127, vec![0x7f]),
        (128, vec![0x80, 0x01]),
        (129, vec![0x81, 0x01]),
        (300, vec![0xac, 0x02]),
        (12857, vec![0xb9, 0x64]),
        (624485, vec![0xe5, 0x8e, 0x26]),
    ]
}

#[test]
fn trust_leb_uleb_encode_native_eq_jit() {
    let vals = uleb_values();
    let expected = vals.len();
    // JIT both the dwarf and wasm ULEB encoders in one worker (sequential modules).
    let sweep = vals.clone();
    let rows =
        run_watchdogged::<((u64, u64, u32), (u64, u64, u32))>("uleb_enc", expected, move |tx| {
            let db = jit_module(ENC_ULEB_IR, "enc_uleb");
            let wb = jit_module(WASM_ULEB_IR, "wasm_uleb");
            let df: EncU = unsafe { std::mem::transmute(bind(&db, "enc_uleb_root")) };
            let wf: EncU = unsafe { std::mem::transmute(bind(&wb, "wasm_uleb_root")) };
            for &v in &sweep {
                let mut od = poison_enc();
                let mut ow = poison_enc();
                unsafe {
                    df(v, &mut od);
                    wf(v, &mut ow);
                }
                if tx.send((enc3(&od), enc3(&ow))).is_err() {
                    return;
                }
            }
        });

    assert_eq!(rows.len(), expected);
    for (i, &v) in vals.iter().enumerate() {
        let (jd, jw) = rows[i];
        // (a) native==JIT for both encoders.
        assert_eq!(
            jd,
            n_enc_uleb(v),
            "dwarf encode_uleb128({v}): JIT != native"
        );
        assert_eq!(jw, n_wasm_uleb(v), "wasm write_uleb128({v}): JIT != native");
        // (b) dwarf==wasm cross-encoder differential (byte-identical).
        assert_eq!(
            jd, jw,
            "encode_uleb128({v}) != write_uleb128({v}) (cross-encoder asymmetry)"
        );
        assert_ne!(jd.2, 0xDEAD, "row {i} len still poisoned (v={v})");
    }

    // (c) SPEC ORACLE: canonical DWARF-v5 byte sequences.
    for (v, bytes) in uleb_spec() {
        let want = pack(&bytes);
        assert_eq!(
            n_enc_uleb(v),
            want,
            "SPEC uleb128({v}) native must be {bytes:02x?}"
        );
        // and it appears in the swept JIT rows (if v is in the sweep):
        if let Some(pos) = vals.iter().position(|&x| x == v) {
            assert_eq!(
                rows[pos].0, want,
                "SPEC uleb128({v}) JIT must be {bytes:02x?}"
            );
        }
    }
}

// ============================================================================
// TEST 2 — SLEB128 ENCODERS (dwarf `encode_sleb128` + wasm `write_sleb128`).
//   native==JIT, SPEC ORACLE, and the CROSS-IMPL differential: two structurally
//   DIFFERENT signed encoders must produce byte-identical output.
// ============================================================================

/// DWARF-v5 App.C / production canonical SLEB128 examples (independent 3rd oracle).
fn sleb_spec() -> Vec<(i64, Vec<u8>)> {
    vec![
        (0, vec![0x00]),
        (1, vec![0x01]),
        (2, vec![0x02]),
        (-1, vec![0x7f]),
        (-2, vec![0x7e]),
        (63, vec![0x3f]),
        (64, vec![0xc0, 0x00]),
        (-64, vec![0x40]),
        (-65, vec![0xbf, 0x7f]),
        (127, vec![0xff, 0x00]),
        (-127, vec![0x81, 0x7f]),
        (128, vec![0x80, 0x01]),
        (-128, vec![0x80, 0x7f]),
        (129, vec![0x81, 0x01]),
        (-129, vec![0xff, 0x7e]),
    ]
}

#[test]
fn trust_leb_sleb_encode_native_eq_jit() {
    let vals = sleb_values();
    let expected = vals.len();
    let sweep = vals.clone();
    let rows =
        run_watchdogged::<((u64, u64, u32), (u64, u64, u32))>("sleb_enc", expected, move |tx| {
            let db = jit_module(ENC_SLEB_IR, "enc_sleb");
            let wb = jit_module(WASM_SLEB_IR, "wasm_sleb");
            let df: EncI = unsafe { std::mem::transmute(bind(&db, "enc_sleb_root")) };
            let wf: EncI = unsafe { std::mem::transmute(bind(&wb, "wasm_sleb_root")) };
            for &v in &sweep {
                let mut od = poison_enc();
                let mut ow = poison_enc();
                unsafe {
                    df(v, &mut od);
                    wf(v, &mut ow);
                }
                if tx.send((enc3(&od), enc3(&ow))).is_err() {
                    return;
                }
            }
        });

    assert_eq!(rows.len(), expected);
    for (i, &v) in vals.iter().enumerate() {
        let (jd, jw) = rows[i];
        // (a) native==JIT for both encoders.
        assert_eq!(
            jd,
            n_enc_sleb(v),
            "dwarf encode_sleb128({v}): JIT != native"
        );
        assert_eq!(jw, n_wasm_sleb(v), "wasm write_sleb128({v}): JIT != native");
        // (b) CROSS-IMPL differential: `while more` == `loop`/`done`, byte-identical.
        assert_eq!(
            jd, jw,
            "encode_sleb128({v}) != write_sleb128({v}) (cross-impl asymmetry)"
        );
        assert_ne!(jd.2, 0xDEAD, "row {i} len still poisoned (v={v})");
    }

    // (c) SPEC ORACLE.
    for (v, bytes) in sleb_spec() {
        let want = pack(&bytes);
        assert_eq!(
            n_enc_sleb(v),
            want,
            "SPEC sleb128({v}) native must be {bytes:02x?}"
        );
        if let Some(pos) = vals.iter().position(|&x| x == v) {
            assert_eq!(
                rows[pos].0, want,
                "SPEC sleb128({v}) JIT must be {bytes:02x?}"
            );
        }
    }
}

// ============================================================================
// TEST 3 — ULEB128 DECODER + ENCODE<->DECODE ROUND-TRIP (Reader::uleb128).
//   decode(encode(v)) == v; native==JIT; SPEC oracle; reject direction.
// ============================================================================

#[test]
fn trust_leb_uleb_decode_roundtrip() {
    let vals = uleb_values();
    // build the decode inputs from the NATIVE encoder (proven == JIT in test 1),
    // plus crafted reject-direction cases.
    #[derive(Clone)]
    struct Case {
        lo: u64,
        hi: u64,
        limit: u32,
        expect_val: u64,
        expect_err: u32,
        label: String,
    }
    let mut cases: Vec<Case> = Vec::new();
    for &v in &vals {
        let (lo, hi, len) = n_enc_uleb(v);
        cases.push(Case {
            lo,
            hi,
            limit: len,
            expect_val: v,
            expect_err: 0,
            label: format!("roundtrip v={v}"),
        });
        // TRUNCATION reject: cut the buffer one byte short (multi-byte only).
        if len >= 2 {
            cases.push(Case {
                lo,
                hi,
                limit: len - 1,
                expect_val: 0,
                expect_err: 2,
                label: format!("truncated v={v}"),
            });
        }
    }
    // OVERFLOW reject: 11 continuation bytes (0x80) — shift reaches 70 >= 64.
    {
        let over = vec![0x80u8; 11];
        let (lo, hi, len) = pack(&over);
        cases.push(Case {
            lo,
            hi,
            limit: len,
            expect_val: 0,
            expect_err: 1,
            label: "overflow 11x0x80".to_string(),
        });
    }

    let expected = cases.len();
    let sweep = cases.clone();
    let rows = run_watchdogged::<(u64, u32)>("uleb_dec", expected, move |tx| {
        let b = jit_module(DEC_ULEB_IR, "dec_uleb");
        let f: DecFn = unsafe { std::mem::transmute(bind(&b, "dec_uleb_root")) };
        for c in &sweep {
            let mut o = poison_dec();
            unsafe { f(c.lo, c.hi, c.limit, &mut o) };
            if tx.send(dec2(&o)).is_err() {
                return;
            }
        }
    });

    assert_eq!(rows.len(), expected);
    for (i, c) in cases.iter().enumerate() {
        // (a) native==JIT.
        let native = n_dec_uleb(c.lo, c.hi, c.limit);
        assert_eq!(
            rows[i], native,
            "{}: JIT {:?} != native {:?}",
            c.label, rows[i], native
        );
        // (b) round-trip / reject expectation.
        assert_eq!(
            rows[i],
            (c.expect_val, c.expect_err),
            "{}: decode {:?} != expected ({},{})",
            c.label,
            rows[i],
            c.expect_val,
            c.expect_err
        );
        assert_ne!(rows[i].1, 0xDEAD, "row {i} err still poisoned");
    }

    // (c) SPEC ORACLE: decode the canonical byte sequences directly.
    for (v, bytes) in uleb_spec() {
        let (lo, hi, len) = pack(&bytes);
        assert_eq!(
            n_dec_uleb(lo, hi, len),
            (v, 0),
            "SPEC decode {bytes:02x?} must be {v}"
        );
    }
}

// ============================================================================
// TEST 4 — SLEB128 DECODER + ROUND-TRIP (Reader::sleb128, SIGN-EXTENSION).
// ============================================================================

#[test]
fn trust_leb_sleb_decode_roundtrip() {
    let vals = sleb_values();
    #[derive(Clone)]
    struct Case {
        lo: u64,
        hi: u64,
        limit: u32,
        expect_val: i64,
        expect_err: u32,
        label: String,
    }
    let mut cases: Vec<Case> = Vec::new();
    for &v in &vals {
        let (lo, hi, len) = n_enc_sleb(v);
        cases.push(Case {
            lo,
            hi,
            limit: len,
            expect_val: v,
            expect_err: 0,
            label: format!("roundtrip v={v}"),
        });
        if len >= 2 {
            cases.push(Case {
                lo,
                hi,
                limit: len - 1,
                expect_val: 0,
                expect_err: 2,
                label: format!("truncated v={v}"),
            });
        }
    }
    {
        let over = vec![0x80u8; 11];
        let (lo, hi, len) = pack(&over);
        cases.push(Case {
            lo,
            hi,
            limit: len,
            expect_val: 0,
            expect_err: 1,
            label: "overflow 11x0x80".to_string(),
        });
    }

    let expected = cases.len();
    let sweep = cases.clone();
    let rows = run_watchdogged::<(u64, u32)>("sleb_dec", expected, move |tx| {
        let b = jit_module(DEC_SLEB_IR, "dec_sleb");
        let f: DecFn = unsafe { std::mem::transmute(bind(&b, "dec_sleb_root")) };
        for c in &sweep {
            let mut o = poison_dec();
            unsafe { f(c.lo, c.hi, c.limit, &mut o) };
            if tx.send(dec2(&o)).is_err() {
                return;
            }
        }
    });

    assert_eq!(rows.len(), expected);
    for (i, c) in cases.iter().enumerate() {
        let native = n_dec_sleb(c.lo, c.hi, c.limit);
        assert_eq!(
            rows[i], native,
            "{}: JIT {:?} != native {:?}",
            c.label, rows[i], native
        );
        assert_eq!(
            (rows[i].0 as i64, rows[i].1),
            (c.expect_val, c.expect_err),
            "{}: decode ({},{}) != expected ({},{})",
            c.label,
            rows[i].0 as i64,
            rows[i].1,
            c.expect_val,
            c.expect_err
        );
        assert_ne!(rows[i].1, 0xDEAD, "row {i} err still poisoned");
    }

    // SPEC ORACLE: decode canonical signed sequences (the sign-extension edges).
    for (v, bytes) in sleb_spec() {
        let (lo, hi, len) = pack(&bytes);
        let got = n_dec_sleb(lo, hi, len);
        assert_eq!(
            (got.0 as i64, got.1),
            (v, 0),
            "SPEC decode {bytes:02x?} must be {v}"
        );
    }
}

// ============================================================================
// TEST 5 — DWARF CFI opcode byte assembly (encode_advance_loc[_bytes]).
//   native==JIT + SPEC oracle over the three size thresholds.
// ============================================================================

/// Hand oracle for DW_CFA_advance_loc byte assembly (DWARF-v5 §6.4.2.1).
fn adv_loc_oracle(n: u32) -> Vec<u8> {
    if n <= 63 {
        vec![0x40 | (n as u8)]
    } else if n <= 255 {
        vec![0x02, n as u8]
    } else {
        let w = n as u16;
        vec![0x03, (w & 0xff) as u8, (w >> 8) as u8]
    }
}

#[test]
fn trust_leb_cfi_advance_loc_native_eq_jit() {
    // Sweep across the three encodings incl. the exact thresholds.
    let mut ns: Vec<u32> = (0..=70u32).collect();
    ns.extend_from_slice(&[
        63, 64, 100, 200, 254, 255, 256, 257, 300, 1000, 12857, 65535,
    ]);
    let expected = ns.len();
    let sweep = ns.clone();
    let rows =
        run_watchdogged::<((u64, u64, u32), (u64, u64, u32))>("adv_loc", expected, move |tx| {
            let ab = jit_module(ADV_LOC_IR, "adv_loc");
            let bb = jit_module(ADV_LOC_BYTES_IR, "adv_loc_bytes");
            let af: AdvFn = unsafe { std::mem::transmute(bind(&ab, "adv_loc_root")) };
            let bf: AdvFn = unsafe { std::mem::transmute(bind(&bb, "adv_loc_bytes_root")) };
            for &n in &sweep {
                let mut oa = poison_enc();
                let mut ob = poison_enc();
                unsafe {
                    af(n, &mut oa);
                    bf(n, &mut ob);
                }
                if tx.send((enc3(&oa), enc3(&ob))).is_err() {
                    return;
                }
            }
        });

    assert_eq!(rows.len(), expected);
    for (i, &n) in ns.iter().enumerate() {
        let (ja, jb) = rows[i];
        // (a) native==JIT.
        assert_eq!(ja, n_adv_loc(n), "encode_advance_loc({n}): JIT != native");
        assert_eq!(
            jb,
            n_adv_loc_bytes(n),
            "encode_advance_loc_bytes({n}): JIT != native"
        );
        // (b) SPEC oracle: advance_loc byte assembly.
        let want = pack(&adv_loc_oracle(n));
        assert_eq!(
            ja,
            want,
            "SPEC advance_loc({n}) bytes {:02x?}",
            adv_loc_oracle(n)
        );
        // (c) advance_loc_bytes == advance_loc EXCEPT n==0 emits nothing.
        if n == 0 {
            assert_eq!(jb, (0, 0, 0), "advance_loc_bytes(0) emits no bytes");
        } else {
            assert_eq!(
                jb, want,
                "advance_loc_bytes({n}) == advance_loc({n}) for n>0"
            );
        }
    }

    // Threshold spot-checks (independent).
    assert_eq!(n_adv_loc(5), pack(&[0x45]), "advance_loc(5) = 0x40|5");
    assert_eq!(
        n_adv_loc(63),
        pack(&[0x7f]),
        "advance_loc(63) = 0x40|63 (max small)"
    );
    assert_eq!(
        n_adv_loc(64),
        pack(&[0x02, 0x40]),
        "advance_loc(64) = advance_loc1 64"
    );
    assert_eq!(
        n_adv_loc(255),
        pack(&[0x02, 0xff]),
        "advance_loc(255) = advance_loc1 255"
    );
    assert_eq!(
        n_adv_loc(256),
        pack(&[0x03, 0x00, 0x01]),
        "advance_loc(256) = advance_loc2 LE"
    );
    assert_eq!(
        n_adv_loc(1000),
        pack(&[0x03, 0xe8, 0x03]),
        "advance_loc(1000) = advance_loc2 LE"
    );
}

// ============================================================================
// TEST 6 — DW_EH_PE pointer_encoding_size, EXHAUSTIVE over all 256 encodings.
// ============================================================================

#[test]
fn trust_leb_pointer_encoding_size_exhaustive() {
    let expected = 256usize;
    let rows = run_watchdogged::<u32>("ptr_enc", expected, move |tx| {
        let b = jit_module(PTR_ENC_IR, "ptr_enc");
        let f: PtrFn = unsafe { std::mem::transmute(bind(&b, "ptr_enc_size_root")) };
        for e in 0..256u32 {
            if tx.send(unsafe { f(e) }).is_err() {
                return;
            }
        }
    });

    assert_eq!(rows.len(), expected);
    let mut n4 = 0u32;
    let mut n8 = 0u32;
    for e in 0..256u32 {
        let native = s::ptr_enc_size_root(e);
        assert_eq!(
            rows[e as usize], native,
            "ptr_enc_size({e:#x}): JIT != native"
        );
        // independent oracle: only low-nibble 0x0B -> 4; all else -> 8.
        let oracle = if (e & 0x0F) == 0x0B { 4 } else { 8 };
        assert_eq!(rows[e as usize], oracle, "ptr_enc_size({e:#x}) oracle");
        if rows[e as usize] == 4 {
            n4 += 1;
        } else {
            n8 += 1;
        }
    }
    // Both verdicts non-trivially exercised (16 encodings with low-nibble 0x0B).
    assert_eq!(
        n4, 16,
        "exactly 16 encodings (low-nibble 0x0B) yield size 4"
    );
    assert_eq!(n8, 240, "the other 240 yield size 8");
}

// ============================================================================
// ARMED NEGATIVE CONTROLS — corrupt the module text, prove divergence, restore.
// ============================================================================

/// ARMED (encoder): patch the ULEB128 CONTINUATION-BIT mask `0x80` (`const u8 128`)
/// -> `0x00` in `encode_uleb128`. The "more bytes follow" flag is then never set, so
/// a multi-byte ULEB drops every continuation bit — a decoder stops after byte 0 and
/// reads a WRONG (truncated) value. Prove divergence on uleb128(128), restore, re-pass.
#[test]
fn trust_leb_uleb_encode_armed_control() {
    const ANCHOR: &str = "const u8 128";
    assert_eq!(
        ENC_ULEB_IR.matches(ANCHOR).count(),
        1,
        "corruption anchor must be unique (0x80 continuation mask)"
    );
    let corrupted = ENC_ULEB_IR.replace(ANCHOR, "const u8 0");
    assert_ne!(corrupted, ENC_ULEB_IR);

    let v = 128u64; // correct [0x80,0x01]; corrupted [0x00,0x01]
    let corrupt = run_watchdogged::<(u64, u64, u32)>("uleb CORRUPTED", 1, move |tx| {
        let b = jit_module(&corrupted, "uleb CORRUPTED");
        let f: EncU = unsafe { std::mem::transmute(bind(&b, "enc_uleb_root")) };
        let mut o = poison_enc();
        unsafe { f(v, &mut o) };
        let _ = tx.send(enc3(&o));
    })[0];
    let pristine = run_watchdogged::<(u64, u64, u32)>("uleb RESTORED", 1, move |tx| {
        let b = jit_module(ENC_ULEB_IR, "uleb RESTORED");
        let f: EncU = unsafe { std::mem::transmute(bind(&b, "enc_uleb_root")) };
        let mut o = poison_enc();
        unsafe { f(v, &mut o) };
        let _ = tx.send(enc3(&o));
    })[0];

    let native = n_enc_uleb(v);
    assert_eq!(
        native,
        pack(&[0x80, 0x01]),
        "native uleb128(128) = [0x80,0x01]"
    );
    assert_eq!(
        corrupt,
        pack(&[0x00, 0x01]),
        "corrupted drops the continuation bit -> [0x00,0x01]"
    );
    assert_ne!(corrupt, native, "corrupted JIT DIVERGES from native");
    assert_eq!(
        pristine, native,
        "pristine module AGREES (restore + re-pass)"
    );
}

/// ARMED (decoder, THE SLEB SIGN-EXTENSION BUG SITE): patch the sign-fill constant
/// `-1i64` (`const i64 -1`) -> `0` in `Reader::sleb128`'s
/// `result |= -1i64 << shift`. Negative SLEB values then FAIL to sign-extend and
/// decode to a wrong (truncated positive) value. Prove divergence on decode([0x7e])
/// (= sleb -2), restore, re-pass.
#[test]
fn trust_leb_sleb_decode_signext_armed_control() {
    const ANCHOR: &str = "const i64 -1";
    assert_eq!(
        DEC_SLEB_IR.matches(ANCHOR).count(),
        1,
        "corruption anchor must be unique (sign-extension fill -1)"
    );
    let corrupted = DEC_SLEB_IR.replace(ANCHOR, "const i64 0");
    assert_ne!(corrupted, DEC_SLEB_IR);

    // sleb128(-2) = [0x7e]; correct decode = -2; broken sign-ext = 126.
    let (lo, hi, len) = pack(&[0x7e]);
    let corrupt = run_watchdogged::<(u64, u32)>("sleb dec CORRUPTED", 1, move |tx| {
        let b = jit_module(&corrupted, "sleb dec CORRUPTED");
        let f: DecFn = unsafe { std::mem::transmute(bind(&b, "dec_sleb_root")) };
        let mut o = poison_dec();
        unsafe { f(lo, hi, len, &mut o) };
        let _ = tx.send(dec2(&o));
    })[0];
    let pristine = run_watchdogged::<(u64, u32)>("sleb dec RESTORED", 1, move |tx| {
        let b = jit_module(DEC_SLEB_IR, "sleb dec RESTORED");
        let f: DecFn = unsafe { std::mem::transmute(bind(&b, "dec_sleb_root")) };
        let mut o = poison_dec();
        unsafe { f(lo, hi, len, &mut o) };
        let _ = tx.send(dec2(&o));
    })[0];

    let native = n_dec_sleb(lo, hi, len);
    assert_eq!(
        (native.0 as i64, native.1),
        (-2, 0),
        "native decode [0x7e] = -2"
    );
    assert_eq!(
        corrupt,
        (126, 0),
        "corrupted sign-fill 0 -> decode [0x7e] = 126 (no sign-extension)"
    );
    assert_ne!(corrupt, native, "corrupted JIT DIVERGES from native");
    assert_eq!(
        pristine, native,
        "pristine module AGREES (restore + re-pass)"
    );
}

/// ARMED (CFI opcode): patch DW_CFA_advance_loc (`const u8 64` = 0x40) -> `0x00` in
/// `encode_advance_loc`. The small-form opcode high-bits (0b01) are dropped, so
/// `advance_loc(5)` emits `0x05` (which the unwinder reads as a DIFFERENT DW_CFA
/// instruction) instead of `0x45` — a corrupt unwind program. Prove divergence,
/// restore, re-pass.
#[test]
fn trust_leb_cfi_advance_loc_armed_control() {
    const ANCHOR: &str = "const u8 64";
    assert_eq!(
        ADV_LOC_IR.matches(ANCHOR).count(),
        1,
        "corruption anchor must be unique (DW_CFA_advance_loc 0x40)"
    );
    let corrupted = ADV_LOC_IR.replace(ANCHOR, "const u8 0");
    assert_ne!(corrupted, ADV_LOC_IR);

    let n = 5u32; // correct [0x45]; corrupted [0x05]
    let corrupt = run_watchdogged::<(u64, u64, u32)>("adv CORRUPTED", 1, move |tx| {
        let b = jit_module(&corrupted, "adv CORRUPTED");
        let f: AdvFn = unsafe { std::mem::transmute(bind(&b, "adv_loc_root")) };
        let mut o = poison_enc();
        unsafe { f(n, &mut o) };
        let _ = tx.send(enc3(&o));
    })[0];
    let pristine = run_watchdogged::<(u64, u64, u32)>("adv RESTORED", 1, move |tx| {
        let b = jit_module(ADV_LOC_IR, "adv RESTORED");
        let f: AdvFn = unsafe { std::mem::transmute(bind(&b, "adv_loc_root")) };
        let mut o = poison_enc();
        unsafe { f(n, &mut o) };
        let _ = tx.send(enc3(&o));
    })[0];

    let native = n_adv_loc(n);
    assert_eq!(native, pack(&[0x45]), "native advance_loc(5) = 0x45");
    assert_eq!(
        corrupt,
        pack(&[0x05]),
        "corrupted drops the 0b01 opcode -> 0x05 (wrong DW_CFA)"
    );
    assert_ne!(corrupt, native, "corrupted JIT DIVERGES from native");
    assert_eq!(
        pristine, native,
        "pristine module AGREES (restore + re-pass)"
    );
}
