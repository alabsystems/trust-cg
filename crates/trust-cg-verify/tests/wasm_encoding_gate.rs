// trust-cg-verify/tests/wasm_encoding_gate.rs - P4 families (4)(5)(6) against the LIVE backend
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! The live half of the encoder/byte family.
//!
//! `src/wasm_encoding_proofs.rs` holds the independent spec-derived LEB128
//! decoder, the module-bytes decoder, and the obligations built on them — all of
//! which take BYTES. This file supplies the bytes by running the REAL wasm
//! backend (`trust-cg-codegen` is a DEV-dependency of this crate; it cannot be a
//! normal one, because that crate depends on this one).
//!
//! Three things happen here that cannot happen inside the library:
//!
//!   1. the captured [`EMITTED_CONST_IMMEDIATES`] corpus is RE-DERIVED from the
//!      live backend and asserted byte-identical, so the coverage-gate credit
//!      hook can never stand on a stale capture;
//!   2. real modules — closed, island, table-bearing, static-data-bearing — are
//!      compiled and put through the family-(4) and family-(6) obligations;
//!   3. the P1 `TargetInfo` guard is closed from the other side: a module pinned
//!      to anything but the wasm32 shape must be REFUSED by the compiler.
//!
//! Every anti-tautology guard here mutates REAL emitted bytes and demands the
//! obligation set REFUTE. A guard that passes means the obligation is vacuous.

use trust_cg_verify::wasm_encoding_proofs as enc;

use enc::{
    EMITTED_CONST_IMMEDIATES, EncodingObligation, EncodingReport, Imm, OP_I32_CONST, OP_I64_CONST,
    WASM_ENCODING_DEFERRALS, WASM32_PIN, decode_module,
};

use trust_ir::{BinOp, CastOp, Constant, Global, ICmpOp, Ty};
use trust_ir_build::ModuleBuilder;

use trust_cg_codegen::wasm;
use wasm::{
    WasmFuncImportPolicy, WasmMemoryGrowthPolicy, WasmModulePolicy, WasmStaticDataPolicy,
    island_host_namespace,
};

// ---------------------------------------------------------------------------
// Module builders — the corpus of real modules the obligations run over
// ---------------------------------------------------------------------------

fn finish_wasm32(mb: ModuleBuilder) -> trust_ir::Module {
    let mut m = mb.build();
    m.target_info = Some(wasm::wasm32_target_info());
    m
}

/// `() -> iN { ret <v> }` — the smallest shape that carries one const immediate.
fn const_module(ty: Ty, v: i128) -> Vec<u8> {
    let mut mb = ModuleBuilder::new("k");
    let ft = mb.add_func_type(vec![], vec![ty.clone()]);
    let mut fb = mb.function("k", ft);
    let e = fb.create_block();
    fb.switch_to_block(e);
    let c = fb.iconst(ty, v);
    fb.ret(vec![c]);
    fb.build();
    wasm::compile_module(&finish_wasm32(mb)).expect("const module must compile")
}

/// The import-shift shape: two host declarations interleaved with two defined
/// functions, one of which calls the other. The imports share the callee's
/// signature ON PURPOSE — a forgotten shift emits `call 0`, which still
/// type-checks, still validates, and runs into the host.
fn import_shift_ir() -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("island_calls");
    let ft = mb.add_func_type(vec![Ty::I32, Ty::I32], vec![Ty::I32]);
    mb.function("host_a", ft).build();
    let callee = {
        let mut fb = mb.function("callee", ft);
        let e = fb.create_block();
        let a = fb.add_block_param(e, Ty::I32);
        let b = fb.add_block_param(e, Ty::I32);
        fb.switch_to_block(e);
        let three = fb.iconst(Ty::I32, 3);
        let m = fb.mul(Ty::I32, a, three);
        let r = fb.add(Ty::I32, m, b);
        fb.ret(vec![r]);
        fb.build()
    };
    mb.function("host_b", ft).build();
    {
        let mut fb = mb.function("caller", ft);
        let e = fb.create_block();
        let a = fb.add_block_param(e, Ty::I32);
        let b = fb.add_block_param(e, Ty::I32);
        fb.switch_to_block(e);
        let c = fb.call(callee, vec![a, b]);
        let seven = fb.iconst(Ty::I32, 7);
        let r = fb.add(Ty::I32, c, seven);
        fb.ret(vec![r]);
        fb.build();
    }
    mb.function("host_c", ft).build();
    finish_wasm32(mb)
}

/// The SAME trust-ir with the declarations stripped, so it compiles closed.
fn import_shift_ir_closed() -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("island_calls");
    let ft = mb.add_func_type(vec![Ty::I32, Ty::I32], vec![Ty::I32]);
    let callee = {
        let mut fb = mb.function("callee", ft);
        let e = fb.create_block();
        let a = fb.add_block_param(e, Ty::I32);
        let b = fb.add_block_param(e, Ty::I32);
        fb.switch_to_block(e);
        let three = fb.iconst(Ty::I32, 3);
        let m = fb.mul(Ty::I32, a, three);
        let r = fb.add(Ty::I32, m, b);
        fb.ret(vec![r]);
        fb.build()
    };
    {
        let mut fb = mb.function("caller", ft);
        let e = fb.create_block();
        let a = fb.add_block_param(e, Ty::I32);
        let b = fb.add_block_param(e, Ty::I32);
        fb.switch_to_block(e);
        let c = fb.call(callee, vec![a, b]);
        let seven = fb.iconst(Ty::I32, 7);
        let r = fb.add(Ty::I32, c, seven);
        fb.ret(vec![r]);
        fb.build();
    }
    finish_wasm32(mb)
}

fn island_policy() -> WasmModulePolicy {
    WasmModulePolicy {
        func_imports: WasmFuncImportPolicy::FromModule(island_host_namespace("calls")),
        ..WasmModulePolicy::closed()
    }
}

/// A table-bearing module: a function pointer dispatched through
/// `call_indirect`, so the element segment must cover the whole index space.
fn table_module(with_imports: bool) -> Vec<u8> {
    let mut mb = ModuleBuilder::new("island_table");
    let ft = mb.add_func_type(vec![Ty::I32, Ty::I32], vec![Ty::I32]);
    if with_imports {
        mb.function("host_a", ft).build();
        mb.function("host_b", ft).build();
    }
    let imul = {
        let mut fb = mb.function("imul", ft);
        let e = fb.create_block();
        let a = fb.add_block_param(e, Ty::I32);
        let b = fb.add_block_param(e, Ty::I32);
        fb.switch_to_block(e);
        let r = fb.mul(Ty::I32, a, b);
        fb.ret(vec![r]);
        fb.build()
    };
    {
        let mut fb = mb.function("dispatch", ft);
        let e = fb.create_block();
        let x = fb.add_block_param(e, Ty::I32);
        let y = fb.add_block_param(e, Ty::I32);
        fb.switch_to_block(e);
        let fp = fb.fn_addr(ft, imul);
        let r = fb.call_indirect(fp, ft, vec![x, y]);
        fb.ret(vec![r]);
        fb.build();
    }
    let m = finish_wasm32(mb);
    if with_imports {
        wasm::compile_module_with_policy(&m, &island_policy()).expect("island table compiles")
    } else {
        wasm::compile_module(&m).expect("closed table compiles")
    }
}

/// The little-endian witness: an `i32` global with a byte-distinguishable value
/// (`0x1234_5678`), whose data-segment image must be `78 56 34 12`.
const LE_WITNESS: u32 = 0x1234_5678;

fn static_data_module() -> Vec<u8> {
    let mut mb = ModuleBuilder::new("statics");
    mb.add_global(Global {
        name: "WORD".to_string(),
        ty: Ty::I32,
        mutable: false,
        initializer: Some(Constant::Int(i128::from(LE_WITNESS))),
        linkage: Default::default(),
        tls: None,
        align: None,
    });
    let ft = mb.add_func_type(vec![Ty::I32], vec![Ty::I32]);
    let mut fb = mb.function("readw", ft);
    let e = fb.create_block();
    let i = fb.add_block_param(e, Ty::I32);
    fb.switch_to_block(e);
    let base = fb.global_addr(trust_ir::value::GlobalId::new(0));
    let w = fb.load(Ty::I32, base);
    let r = fb.binop(BinOp::Add, Ty::I32, w, i);
    fb.ret(vec![r]);
    fb.build();
    wasm::compile_module(&finish_wasm32(mb)).expect("static-data module compiles")
}

/// A memory + shadow-stack shape: an alloca round-trip pulls in the linear
/// memory, the mutable i32 stack-pointer global, and sub-word memory accesses.
fn memory_module() -> Vec<u8> {
    let mut mb = ModuleBuilder::new("memops");
    let elem = mb.add_type(Ty::U8);
    let ft = mb.add_func_type(vec![Ty::I32, Ty::I32], vec![Ty::I32]);
    let mut fb = mb.function("memops", ft);
    let e = fb.create_block();
    let i = fb.add_block_param(e, Ty::I32);
    let x = fb.add_block_param(e, Ty::I32);
    fb.switch_to_block(e);
    let buf = fb.alloca(Ty::Array(elem, 8));
    let seven = fb.iconst(Ty::I32, 7);
    let idx = fb.binop(BinOp::And, Ty::I32, i, seven);
    let p = fb.gep(Ty::U8, buf, vec![idx]);
    let xb = fb.cast(CastOp::Trunc, Ty::I32, Ty::U8, x);
    fb.store(Ty::U8, p, xb);
    let p2 = fb.gep(Ty::U8, buf, vec![idx]);
    let b = fb.load(Ty::U8, p2);
    let out = fb.cast(CastOp::ZExt, Ty::U8, Ty::I32, b);
    fb.ret(vec![out]);
    fb.build();
    wasm::compile_module(&finish_wasm32(mb)).expect("memory module compiles")
}

/// Where the host reserved this island's static-data region.
const ISLAND_STATIC_BASE: u32 = 1024;

/// THE FULL-SURFACE ISLAND: it imports the host's memory, takes its shadow-stack
/// base from a host-published immutable `i32` global, imports a host function,
/// writes static data into a host-reserved region, dispatches through a funcref
/// table, and carries the memory-growth shims.
///
/// Every family-(6) obligation is APPLICABLE to this one module — imported
/// memory limits, an imported i32 global, a defined mutable i32 global, data and
/// element offset expressions, memargs, and a little-endian static image — which
/// is what makes `the_full_surface_island_leaves_no_row_unexercised` a real
/// claim rather than a count.
fn full_surface_island() -> Vec<u8> {
    let mut mb = ModuleBuilder::new("full_island");
    mb.add_global(Global {
        name: "WORD".to_string(),
        ty: Ty::I32,
        mutable: false,
        initializer: Some(Constant::Int(i128::from(LE_WITNESS))),
        linkage: Default::default(),
        tls: None,
        align: None,
    });
    let elem = mb.add_type(Ty::U8);
    let ft = mb.add_func_type(vec![Ty::I32, Ty::I32], vec![Ty::I32]);
    // A body-less declaration becomes a wasm function IMPORT.
    mb.function("host_a", ft).build();
    let imul = {
        let mut fb = mb.function("imul", ft);
        let e = fb.create_block();
        let a = fb.add_block_param(e, Ty::I32);
        let b = fb.add_block_param(e, Ty::I32);
        fb.switch_to_block(e);
        let r = fb.mul(Ty::I32, a, b);
        fb.ret(vec![r]);
        fb.build()
    };
    {
        // alloca + sub-word memory traffic (memargs, shadow stack), a static
        // global read (data segment + i32 address), an indirect dispatch
        // (funcref table + element segment), a DIRECT call to a defined function
        // (the `call` immediate row), and a counted loop (the branch-label row).
        //
        // The last two are here because the family-(4) rows about them are
        // quantified: with no `call` and no `br` in the corpus at all, those rows
        // report not-applicable everywhere and the family would state them
        // without ever exercising them. A diamond would NOT do — the relooper
        // emits an `if`/`else` for one, with no branch instruction — so the loop
        // is what puts a real `br`/`br_if` label immediate in the bytes.
        let mut fb = mb.function("work", ft);
        let e = fb.create_block();
        let i = fb.add_block_param(e, Ty::I32);
        let x = fb.add_block_param(e, Ty::I32);
        let head = fb.create_block();
        let acc = fb.add_block_param(head, Ty::I32);
        let n = fb.add_block_param(head, Ty::I32);
        let body = fb.create_block();
        let bacc = fb.add_block_param(body, Ty::I32);
        let bn = fb.add_block_param(body, Ty::I32);
        let exit = fb.create_block();
        let res = fb.add_block_param(exit, Ty::I32);

        fb.switch_to_block(e);
        let buf = fb.alloca(Ty::Array(elem, 8));
        let seven = fb.iconst(Ty::I32, 7);
        let idx = fb.binop(BinOp::And, Ty::I32, i, seven);
        let p = fb.gep(Ty::U8, buf, vec![idx]);
        let xb = fb.cast(CastOp::Trunc, Ty::I32, Ty::U8, x);
        fb.store(Ty::U8, p, xb);
        let p2 = fb.gep(Ty::U8, buf, vec![idx]);
        let b = fb.load(Ty::U8, p2);
        let widened = fb.cast(CastOp::ZExt, Ty::U8, Ty::I32, b);
        let gbase = fb.global_addr(trust_ir::value::GlobalId::new(0));
        let w = fb.load(Ty::I32, gbase);
        let sum = fb.binop(BinOp::Add, Ty::I32, w, widened);
        let fp = fb.fn_addr(ft, imul);
        let r = fb.call_indirect(fp, ft, vec![sum, x]);
        let d = fb.call(imul, vec![r, x]);
        let zero = fb.iconst(Ty::I32, 0);
        fb.br(head, vec![d, zero]);

        fb.switch_to_block(head);
        let four = fb.iconst(Ty::I32, 4);
        let more = fb.icmp(ICmpOp::Slt, Ty::I32, n, four);
        fb.condbr(more, body, vec![acc, n], exit, vec![acc]);

        fb.switch_to_block(body);
        let one = fb.iconst(Ty::I32, 1);
        let acc2 = fb.binop(BinOp::Add, Ty::I32, bacc, bn);
        let n2 = fb.binop(BinOp::Add, Ty::I32, bn, one);
        fb.br(head, vec![acc2, n2]);

        fb.switch_to_block(exit);
        fb.ret(vec![res]);
        fb.build();
    }
    let policy = WasmModulePolicy {
        static_data: WasmStaticDataPolicy::HostReservedAt {
            base: ISLAND_STATIC_BASE,
        },
        memory_growth: WasmMemoryGrowthPolicy::HostGrantedShims,
        ..WasmModulePolicy::island("full")
    };
    wasm::compile_module_with_policy(&finish_wasm32(mb), &policy)
        .expect("the full-surface island must compile")
}

/// Every real module the family-(4)/(6) obligations run over, named.
fn module_corpus() -> Vec<(&'static str, Vec<u8>)> {
    vec![
        ("closed const i32", const_module(Ty::I32, -1)),
        (
            "closed const i64",
            const_module(Ty::I64, i128::from(i64::MIN)),
        ),
        (
            "closed calls",
            wasm::compile_module(&import_shift_ir_closed()).expect("closed calls compile"),
        ),
        (
            "island calls (2 func imports)",
            wasm::compile_module_with_policy(&import_shift_ir(), &island_policy())
                .expect("island calls compile"),
        ),
        ("closed table", table_module(false)),
        ("island table (2 func imports)", table_module(true)),
        ("static data (little-endian witness)", static_data_module()),
        ("memory + shadow stack", memory_module()),
        ("full-surface island", full_surface_island()),
    ]
}

/// The little-endian image a module's FIRST data segment must hold, for the
/// modules that emit one. Derived from the source constant independently
/// (`u32::to_le_bytes`), never from anything the backend wrote.
fn expected_le_image(name: &str) -> Vec<(usize, Vec<u8>)> {
    if name.starts_with("static data") || name.starts_with("full-surface") {
        vec![(0, LE_WITNESS.to_le_bytes().to_vec())]
    } else {
        vec![]
    }
}

// ---------------------------------------------------------------------------
// Byte extraction — the machine side, decoded, never asked of the encoder
// ---------------------------------------------------------------------------

/// The FIRST integer-const instruction of the FIRST defined body, as
/// `(opcode, immediate bytes)`, obtained by DECODING the emitted module.
///
/// The immediate bytes are re-sliced out of the raw code entry using the
/// decoder's own recorded instruction offset and the canonical length of the
/// value it decoded — never by asking the encoder how long it wrote.
fn first_const_immediate(bytes: &[u8]) -> (u8, Vec<u8>) {
    let m = decode_module(bytes).expect("emitted module must decode");
    let body = m.code.first().expect("at least one defined body");
    let ins = body
        .instrs
        .iter()
        .find(|i| matches!(i.imm, Imm::I32(_) | Imm::I64(_)))
        .expect("the shape carries an integer const");
    // Re-walk the raw bytes to this body's expression start.
    let (entry_start, expr_start) = raw_body_spans(bytes)[0];
    let _ = entry_start;
    let start = expr_start + ins.offset + 1;
    let (value, bits) = match ins.imm {
        Imm::I32(v) => (i64::from(v), 32u32),
        Imm::I64(v) => (v, 64),
        _ => unreachable!("filtered above"),
    };
    let len = enc::canonical_signed_len(value, bits);
    (ins.opcode, bytes[start..start + len].to_vec())
}

/// For each defined code entry, `(absolute entry start, absolute expression
/// start)` — the expression start is past the locals vector.
fn raw_body_spans(bytes: &[u8]) -> Vec<(usize, usize)> {
    let mut at = 8usize;
    let mut out = Vec::new();
    while at < bytes.len() {
        let id = bytes[at];
        at += 1;
        let (size, used) = enc::spec_decode_unsigned(&bytes[at..], 32).expect("section length");
        at += used;
        if id == 10 {
            let mut c = at;
            let (n, used) = enc::spec_decode_unsigned(&bytes[c..], 32).expect("code count");
            c += used;
            for _ in 0..n {
                let (sz, used) = enc::spec_decode_unsigned(&bytes[c..], 32).expect("entry size");
                c += used;
                let entry_start = c;
                let mut e = c;
                let (runs, used) = enc::spec_decode_unsigned(&bytes[e..], 32).expect("local runs");
                e += used;
                for _ in 0..runs {
                    let (_cnt, used) =
                        enc::spec_decode_unsigned(&bytes[e..], 32).expect("local count");
                    e += used + 1;
                }
                out.push((entry_start, e));
                c += sz as usize;
            }
            return out;
        }
        at += size as usize;
    }
    out
}

fn report_of(obs: &[EncodingObligation]) -> EncodingReport {
    EncodingReport::of(obs)
}

fn assert_no_refutations(what: &str, obs: &[EncodingObligation]) -> EncodingReport {
    let r = report_of(obs);
    assert_eq!(
        r.refuted,
        0,
        "{what}: {} obligation(s) REFUTED:\n  {}",
        r.refuted,
        r.refutations.join("\n  ")
    );
    r
}

// ===========================================================================
// FAMILY (5) — the const immediates, against the LIVE backend
// ===========================================================================

/// THE FRESHNESS CONTRACT. Every captured immediate in
/// [`EMITTED_CONST_IMMEDIATES`] is re-derived by compiling a real module through
/// the real backend and DECODING the result. A backend change that alters these
/// bytes turns this test red, so the coverage-gate credit hook can never stand
/// on a stale capture.
#[test]
fn corpus_is_what_the_live_backend_emits_today() {
    let mut checked = 0usize;
    for &(intended, bits, captured) in EMITTED_CONST_IMMEDIATES {
        let ty = if bits == 32 { Ty::I32 } else { Ty::I64 };
        let want_op = if bits == 32 {
            OP_I32_CONST
        } else {
            OP_I64_CONST
        };
        let module = const_module(ty, i128::from(intended));
        let (op, live) = first_const_immediate(&module);
        assert_eq!(
            op, want_op,
            "i{bits}.const {intended}: the live backend emitted opcode 0x{op:02x}"
        );
        assert_eq!(
            live.as_slice(),
            captured,
            "i{bits}.const {intended}: the live backend emits {live:02x?} but the captured corpus \
             says {captured:02x?} — the corpus has rotted, or the encoder changed"
        );
        checked += 1;
    }
    assert_eq!(checked, EMITTED_CONST_IMMEDIATES.len());
    eprintln!(
        "corpus_is_what_the_live_backend_emits_today: {checked}/{} captured immediates re-derived \
         from the LIVE backend, all byte-identical",
        EMITTED_CONST_IMMEDIATES.len()
    );
}

/// The family-(5) obligation over LIVE bytes: for every corpus value, compile a
/// real module, decode the real immediate, and prove it denotes the constant the
/// trust-ir carried.
#[test]
fn live_const_immediates_decode_to_their_intended_value() {
    let mut obs = Vec::new();
    for &(intended, bits, _) in EMITTED_CONST_IMMEDIATES {
        let ty = if bits == 32 { Ty::I32 } else { Ty::I64 };
        let module = const_module(ty, i128::from(intended));
        let (op, imm) = first_const_immediate(&module);
        obs.push(enc::const_immediate_obligation(intended, op, &imm));
    }
    let r = assert_no_refutations("live const immediates", &obs);
    eprintln!("live_const_immediates: {r}");
    assert_eq!(r.proven, EMITTED_CONST_IMMEDIATES.len());
    assert_eq!(r.not_applicable, 0);
}

/// ANTI-TAUTOLOGY (family 5), against LIVE bytes: every mutation of a real
/// emitted immediate must be REFUTED. If any survives, the obligation is
/// vacuous and the two RED coverage-gate rows must NOT be credited.
#[test]
fn live_const_immediate_mutants_are_refuted() {
    let mut mutants = 0usize;
    let mut survived = Vec::new();
    for &(intended, bits, _) in EMITTED_CONST_IMMEDIATES {
        let ty = if bits == 32 { Ty::I32 } else { Ty::I64 };
        let module = const_module(ty, i128::from(intended));
        let (op, imm) = first_const_immediate(&module);

        let mut cases: Vec<(&str, Vec<u8>)> = vec![
            ("overlong pad", enc::mutate_overlong(&imm)),
            ("truncated", enc::mutate_truncate(&imm)),
        ];
        if let Some(m) = enc::mutate_drop_continuation(&imm) {
            cases.push(("dropped continuation bit", m));
        }
        let unsigned = enc::mutate_as_unsigned(intended, bits);
        if unsigned != imm {
            cases.push(("encoded as ULEB128 (sleb/uleb confusion)", unsigned));
        }
        for (why, m) in cases {
            mutants += 1;
            if !enc::const_immediate_obligation(intended, op, &m).is_refuted() {
                survived.push(format!("i{bits}.const {intended}: {why} ({m:02x?})"));
            }
        }
        // The SOURCE side moved instead: the same real bytes, a different claim.
        mutants += 1;
        if !enc::const_immediate_obligation(intended.wrapping_add(1), op, &imm).is_refuted() {
            survived.push(format!(
                "i{bits}.const {intended}: claiming the bytes denote {}",
                intended.wrapping_add(1)
            ));
        }
    }
    assert!(
        survived.is_empty(),
        "{} of {mutants} mutant(s) SURVIVED — the const obligation is vacuous:\n  {}",
        survived.len(),
        survived.join("\n  ")
    );
    eprintln!("live_const_immediate_mutants_are_refuted: {mutants} mutants, all REFUTED");
}

/// EXHAUSTIVE over the full i32 range: every `v: i32` encoded by the backend's
/// own `write_sleb128` (the function the module path calls) must decode, under
/// the INDEPENDENT spec decoder, to exactly `v` at canonical length.
///
/// `#[ignore]`d because it is 4.29e9 iterations: run it with
/// `cargo test -p trust-cg-verify --release --test wasm_encoding_gate -- --ignored --nocapture`.
/// The default lane runs the corpus, which is the byte-length boundaries and
/// the sign-extension edges; this is the whole space, and the difference is
/// named in `WASM_ENCODING_DEFERRALS`.
#[test]
#[ignore = "4.29e9 iterations; run explicitly with --release --ignored"]
fn sleb128_full_i32_range_is_exhaustive() {
    let mut buf = Vec::with_capacity(8);
    let mut n: u64 = 0;
    let mut v: i64 = i64::from(i32::MIN);
    while v <= i64::from(i32::MAX) {
        buf.clear();
        wasm::encode::write_sleb128(&mut buf, v);
        match enc::spec_decode_signed(&buf, 32) {
            Ok((got, used)) => {
                assert_eq!(got, v, "sleb128({v}) decoded as {got} from {buf:02x?}");
                assert_eq!(used, buf.len(), "sleb128({v}) length");
                assert_eq!(used, enc::canonical_signed_len(v, 32), "canonical len {v}");
            }
            Err(e) => panic!("sleb128({v}) = {buf:02x?} REJECTED by the spec decoder: {e}"),
        }
        n += 1;
        v += 1;
    }
    assert_eq!(n, 1u64 << 32);
    eprintln!("sleb128_full_i32_range_is_exhaustive: {n} values, ALL decoded to themselves");
}

/// The same sweep over a contiguous i64 window straddling zero plus every
/// 7-bit boundary neighbourhood up to 2^63 — the part of the i64 space the
/// default lane can afford.
#[test]
fn sleb128_i64_window_and_boundaries() {
    let mut buf = Vec::with_capacity(16);
    let mut n: u64 = 0;
    let check = |v: i64, buf: &mut Vec<u8>, n: &mut u64| {
        buf.clear();
        wasm::encode::write_sleb128(buf, v);
        let (got, used) = enc::spec_decode_signed(buf, 64)
            .unwrap_or_else(|e| panic!("sleb128({v}) = {buf:02x?} rejected: {e}"));
        assert_eq!(got, v, "sleb128({v}) decoded as {got}");
        assert_eq!(used, buf.len());
        assert_eq!(used, enc::canonical_signed_len(v, 64));
        *n += 1;
    };
    for v in -(1i64 << 20)..=(1i64 << 20) {
        check(v, &mut buf, &mut n);
    }
    for k in 1..=9u32 {
        let b = 1i64 << (7 * k - 1);
        for d in -3i64..=3 {
            check(b + d, &mut buf, &mut n);
            check(-b + d, &mut buf, &mut n);
        }
    }
    for v in [i64::MIN, i64::MIN + 1, i64::MAX, i64::MAX - 1] {
        check(v, &mut buf, &mut n);
    }
    eprintln!("sleb128_i64_window_and_boundaries: {n} values decoded to themselves");
}

// ===========================================================================
// FAMILY (4) — module-level indexing / encoding, over REAL modules
// ===========================================================================

/// Every real module in the corpus discharges every APPLICABLE family-(4)
/// obligation.
///
/// The split is pinned EXACTLY, both halves. A `proven`-only floor cannot tell
/// a corpus that exercises more from a family that quantifies over less: every
/// row here is `∀ x ∈ S. P(x)`, and a row whose `S` is empty reports
/// not-applicable rather than banking the module's silence (see
/// `wasm_encoding_proofs::check_over`). Pinning `not_applicable` too is what
/// makes "114 proven" mean 114 rows with something under them.
#[test]
fn every_real_module_discharges_the_indexing_family() {
    let mut total = EncodingReport::default();
    for (name, bytes) in module_corpus() {
        let obs = enc::module_indexing_obligations(&bytes);
        assert!(!obs.is_empty(), "{name}: no obligation was built");
        let r = assert_no_refutations(name, &obs);
        eprintln!("  P4-4 {name}: {r}");
        for line in &r.inapplicable {
            eprintln!("      n/a: {line}");
        }
        total.absorb(r);
    }
    eprintln!("every_real_module_discharges_the_indexing_family: {total}");
    assert_eq!(total.refuted, 0);
    assert_eq!(
        (total.proven, total.not_applicable),
        (114, 69),
        "the family-(4) split over the 9-module corpus moved: {total}. Re-derive it, and update \
         `encoding_family_tally`'s pin and the P4 line of SOUNDNESS_CHECK.md with it"
    );
}

/// THE P2 SHIFT, as a differential over two real compiles of the SAME trust-ir.
#[test]
fn the_import_shift_holds_over_real_bytes() {
    let closed = wasm::compile_module(&import_shift_ir_closed()).expect("closed compiles");
    let island = wasm::compile_module_with_policy(&import_shift_ir(), &island_policy())
        .expect("island compiles");
    let obs = enc::import_shift_obligations(&closed, &island, &["callee", "caller"]);
    let r = assert_no_refutations("import shift", &obs);
    eprintln!("the_import_shift_holds_over_real_bytes: {r}");

    // And name the concrete indices the differential is about, so a reader can
    // see the shift rather than trust the predicate.
    let ci = decode_module(&closed).expect("closed decodes");
    let ii = decode_module(&island).expect("island decodes");
    assert_eq!(ci.func_import_count(), 0);
    assert_eq!(ii.func_import_count(), 3, "host_a, host_b, host_c");
    assert_eq!(ci.exported_funcs()["callee"], 0);
    assert_eq!(ii.exported_funcs()["callee"], 3);
    let island_calls: Vec<u32> = ii
        .all_instrs()
        .iter()
        .filter_map(|(_, i)| match i.imm {
            Imm::Func(f) => Some(f),
            _ => None,
        })
        .collect();
    assert_eq!(
        island_calls,
        vec![3],
        "the island's `caller` must `call 3` (the defined callee); `call 0` is host_a and still \
         type-checks"
    );
}

/// ANTI-TAUTOLOGY (family 4): the FORGOTTEN IMPORT SHIFT. Rewriting every
/// `call k` back to `call (k - imports)` in the real island bytes must be
/// REFUTED. This is the exact silent miscompile the family exists to catch: the
/// mutated module is byte-length identical, type-checks, and runs into the host.
#[test]
fn the_forgotten_import_shift_is_refuted() {
    let closed = wasm::compile_module(&import_shift_ir_closed()).expect("closed compiles");
    let island = wasm::compile_module_with_policy(&import_shift_ir(), &island_policy())
        .expect("island compiles");
    let k = decode_module(&island).expect("decodes").func_import_count();
    let broken = enc::mutate_unshift_calls(&island, k)
        .expect("the island has a single-byte call immediate to un-shift");
    assert_eq!(
        broken.len(),
        island.len(),
        "the mutation must be byte-length preserving — that is what makes it silent"
    );
    assert_ne!(broken, island, "the mutation must actually change bytes");

    // It still DECODES: nothing structural gives it away.
    let bm = decode_module(&broken).expect("the broken module still decodes");
    assert_eq!(
        bm.all_instrs()
            .iter()
            .filter_map(|(_, i)| match i.imm {
                Imm::Func(f) => Some(f),
                _ => None,
            })
            .collect::<Vec<_>>(),
        vec![0],
        "the un-shifted call names host import 0"
    );

    // The differential REFUTES it.
    let obs = enc::import_shift_obligations(&closed, &broken, &["callee", "caller"]);
    let r = report_of(&obs);
    assert!(
        r.refuted > 0,
        "the FORGOTTEN IMPORT SHIFT survived the differential — the family is vacuous"
    );

    // AND THE HONEST HALF: the STANDALONE index obligations do NOT see this.
    // `call 0` resolves perfectly well — index 0 is a real function — so every
    // single-module obligation holds on the broken bytes. That is exactly why
    // the differential exists, and saying so here keeps the single-module
    // family from being read as more than it is.
    let solo = report_of(&enc::module_indexing_obligations(&broken));
    assert_eq!(
        solo.refuted, 0,
        "if the single-module family CAN see a forgotten shift, this comment (and the deferral \
         reasoning behind the differential) is wrong: {:?}",
        solo.refutations
    );
    eprintln!(
        "the_forgotten_import_shift_is_refuted: differential {r} (the single-module family is \
         blind to it: {solo})\n  {}",
        r.refutations.join("\n  ")
    );
}

/// Assert that mutating `bytes` refutes family (4), and that the obligation
/// which fired is the one named by `must_name` — so a guard cannot pass because
/// some UNRELATED obligation happened to break.
fn assert_indexing_refutes(what: &str, broken: &[u8], must_name: &str) {
    let r = report_of(&enc::module_indexing_obligations(broken));
    assert!(
        r.refuted > 0,
        "{what}: the mutation SURVIVED family (4) — the obligation is vacuous"
    );
    assert!(
        r.refutations.iter().any(|line| line.contains(must_name)),
        "{what}: family (4) refuted, but not via `{must_name}`; it said:\n  {}",
        r.refutations.join("\n  ")
    );
}

/// ANTI-TAUTOLOGY (family 4): structural mutations of real module bytes are each
/// REFUTED, and each fires the SPECIFIC obligation it targets — an out-of-range
/// export index, an out-of-order section, a shrunken or non-identity element
/// segment, an unresolvable type index, a corrupted vector count.
#[test]
fn structural_mutants_of_real_modules_are_refuted() {
    let mut fired = 0usize;

    for (name, bytes) in module_corpus() {
        // 1. An export pointed past the end of the function index space.
        if let Some(broken) = enc::mutate_export_out_of_range(&bytes, 120) {
            assert_eq!(broken.len(), bytes.len(), "{name}: length preserving");
            assert_indexing_refutes(
                &format!("{name}: out-of-range export index"),
                &broken,
                "every export index resolves in ITS OWN index space",
            );
            fired += 1;
        }

        // 2. Two adjacent sections SWAPPED: each still decodes on its own, so
        //    the strictly-increasing-id obligation is what must fire.
        if let Some(broken) = enc::mutate_swap_adjacent_sections(&bytes, 1) {
            assert_eq!(broken.len(), bytes.len(), "{name}: length preserving");
            assert_indexing_refutes(
                &format!("{name}: swapped adjacent sections"),
                &broken,
                "section ids are STRICTLY increasing",
            );
            fired += 1;
        }

        // 3. A defined function's type index pointed past the type section.
        if let Some(broken) = enc::mutate_function_type_index(&bytes, 100) {
            assert_eq!(broken.len(), bytes.len(), "{name}: length preserving");
            assert_indexing_refutes(
                &format!("{name}: unresolvable function type index"),
                &broken,
                "every DEFINED function's type index resolves",
            );
            fired += 1;
        }

        // 4. A vector count that disagrees with its contents — the decoder's
        //    exact-consumption rule is what must catch this.
        let spans = enc::section_spans(&bytes).expect("sections walk");
        if let Some((start, _)) = spans.iter().find(|(s, _)| bytes[*s] == 3) {
            let mut c = start + 1;
            let (_len, used) = enc::spec_decode_unsigned(&bytes[c..], 32).expect("len");
            c += used;
            if bytes[c] < 0x7f {
                let mut broken = bytes.clone();
                broken[c] += 1;
                assert_indexing_refutes(
                    &format!("{name}: function-section count off by one"),
                    &broken,
                    "the emitted module decodes under the spec binary grammar",
                );
                fired += 1;
            }
        }

        // 5. The element segment: a short count, and a broken identity.
        if enc::decode_module(&bytes)
            .expect("decodes")
            .elements
            .is_empty()
        {
            continue;
        }
        // A count that disagrees with the entries present: the exact-consumption
        // rule catches it, because the dropped entry's byte is still there.
        let broken = enc::mutate_shrink_element_count(&bytes)
            .unwrap_or_else(|| panic!("{name}: a single-byte element count"));
        assert_eq!(broken.len(), bytes.len());
        assert_indexing_refutes(
            &format!("{name}: element count disagrees with its contents"),
            &broken,
            "the emitted module decodes under the spec binary grammar",
        );
        fired += 1;

        // A perfectly WELL-FORMED module whose element segment is simply one
        // entry short — the "sized the table from the DEFINED count" bug. Only
        // the coverage obligation can see this one.
        let broken = enc::mutate_drop_last_element(&bytes)
            .unwrap_or_else(|| panic!("{name}: droppable last element entry"));
        assert_eq!(broken.len() + 1, bytes.len(), "one entry byte removed");
        assert!(
            enc::decode_module(&broken).is_ok(),
            "{name}: the short-segment module must still DECODE — that is what makes it silent"
        );
        assert_indexing_refutes(
            &format!("{name}: element segment one entry short"),
            &broken,
            "the WHOLE function index space, imports included",
        );
        fired += 1;

        let broken = enc::mutate_element_identity(&bytes)
            .unwrap_or_else(|| panic!("{name}: a single-byte element entry"));
        assert_eq!(broken.len(), bytes.len());
        assert_indexing_refutes(
            &format!("{name}: element i != function i"),
            &broken,
            "element i is function i",
        );
        fired += 1;
    }

    assert!(
        fired >= 30,
        "only {fired} structural mutants were exercised"
    );
    eprintln!(
        "structural_mutants_of_real_modules_are_refuted: {fired} mutants, all REFUTED via the \
         SPECIFIC obligation each targets"
    );
}

/// The decoder itself fails CLOSED on bytes outside the emitted surface, rather
/// than skipping them. A decoder that skipped would make every obligation above
/// silently partial.
#[test]
fn the_decoder_refuses_what_it_does_not_examine() {
    let base = const_module(Ty::I32, 7);
    // A custom section (id 0) appended to a valid module.
    let mut with_custom = base.clone();
    with_custom.extend_from_slice(&[0x00, 0x05, 0x04, b'n', b'a', b'm', b'e']);
    assert!(
        decode_module(&with_custom).is_err(),
        "a custom section must be REFUSED, not skipped"
    );
    // An unknown section id.
    let mut with_unknown = base.clone();
    with_unknown.extend_from_slice(&[0x7f, 0x01, 0x00]);
    assert!(decode_module(&with_unknown).is_err());
    // A truncated module.
    assert!(decode_module(&base[..base.len() - 1]).is_err());
    // Wrong magic.
    let mut wrong_magic = base.clone();
    wrong_magic[1] = b'A';
    assert!(decode_module(&wrong_magic).is_err());
    // An unknown opcode inside a body: 0xd2 (`ref.func`) is a real spec opcode
    // this backend never emits, so it must fail closed rather than be skipped.
    let spans = raw_body_spans(&base);
    let mut with_reffunc = base.clone();
    with_reffunc[spans[0].1] = 0xd2;
    assert!(
        decode_module(&with_reffunc).is_err(),
        "an opcode outside the emitted surface must be REFUSED"
    );
}

// ===========================================================================
// FAMILY (6) — TargetInfo conformance
// ===========================================================================

/// Every real module discharges the target-conformance family, and the
/// little-endian half is checked against a byte-distinguishable witness.
#[test]
fn every_real_module_conforms_to_the_wasm32_pin() {
    let mut total = EncodingReport::default();
    for (name, bytes) in module_corpus() {
        let owned = expected_le_image(name);
        let images: Vec<(usize, &[u8])> = owned.iter().map(|(i, b)| (*i, b.as_slice())).collect();
        let obs = enc::target_conformance_obligations(&bytes, &images);
        let r = assert_no_refutations(name, &obs);
        eprintln!("  P4-6 {name}: {r}");
        for line in &r.inapplicable {
            eprintln!("      n/a: {line}");
        }
        total.absorb(r);
    }
    eprintln!("every_real_module_conforms_to_the_wasm32_pin: {total}");
    assert_eq!(total.refuted, 0);
    // Pinned exactly, both halves — see the note on
    // `every_real_module_discharges_the_indexing_family`. Family (6) is
    // n/a-DOMINATED on this corpus (18 applicable rows against 39 absent
    // constructs) and that is the honest shape of it: most of these modules
    // declare no memory, no data segment and no global, so most of what the
    // wasm32 pin talks about is simply not in their bytes. The one module that
    // makes every row applicable is the full-surface island, which is what
    // `the_full_surface_island_leaves_no_row_unexercised` exists to state.
    assert_eq!(
        (total.proven, total.not_applicable),
        (18, 39),
        "the family-(6) split over the 9-module corpus moved: {total}. Re-derive it, and update \
         `encoding_family_tally`'s pin and the P4 line of SOUNDNESS_CHECK.md with it"
    );
}

/// A count of holding obligations is a weak claim when most rows are
/// NOT-APPLICABLE. This is the strong one: there is a real module the backend
/// emits for which EVERY family-(6) obligation is applicable AND holds, so no
/// row of that family is unexercised across the corpus.
///
/// The same claim for family (4) needs the table and data sections, which this
/// module also carries — so it is stated here too.
#[test]
fn the_full_surface_island_leaves_no_row_unexercised() {
    let bytes = full_surface_island();
    let owned = LE_WITNESS.to_le_bytes();
    let t = report_of(&enc::target_conformance_obligations(
        &bytes,
        &[(0, &owned[..])],
    ));
    eprintln!("full-surface island P4-6: {t}");
    for line in &t.inapplicable {
        eprintln!("  n/a: {line}");
    }
    assert_eq!(t.refuted, 0, "{:?}", t.refutations);
    assert_eq!(
        t.not_applicable, 0,
        "the full-surface island must make EVERY family-(6) obligation applicable; still n/a: {:?}",
        t.inapplicable
    );

    let i = report_of(&enc::module_indexing_obligations(&bytes));
    eprintln!("full-surface island P4-4: {i}");
    for line in &i.inapplicable {
        eprintln!("  n/a: {line}");
    }
    assert_eq!(i.refuted, 0, "{:?}", i.refutations);
    assert_eq!(
        i.not_applicable, 0,
        "the full-surface island must make EVERY family-(4) obligation applicable; still n/a: {:?}",
        i.inapplicable
    );

    // And it really is the full surface: name what the module carries.
    let m = decode_module(&bytes).expect("decodes");
    assert_eq!(m.func_import_count(), 1, "one host function import");
    assert_eq!(m.memory_import_count(), 1, "the host's linear memory");
    assert_eq!(m.global_import_count(), 1, "the host-published stack base");
    assert!(
        m.globals.iter().any(|g| g.mutable),
        "the shadow-stack pointer"
    );
    assert_eq!(m.tables.len(), 1, "the funcref table");
    assert_eq!(m.elements.len(), 1, "the element segment");
    assert_eq!(m.data.len(), 1, "the host-reserved static data segment");
    assert!(
        m.all_instrs()
            .iter()
            .any(|(_, ins)| matches!(ins.imm, Imm::MemArg { .. })),
        "linear-memory accesses"
    );
    assert!(
        m.all_instrs()
            .iter()
            .any(|(_, ins)| matches!(ins.imm, Imm::MemIdx(_))),
        "the memory.size / memory.grow shims"
    );
}

/// The LITTLE-ENDIAN witness, spelled out: the backend writes `0x12345678` as
/// `78 56 34 12`, and reversing those bytes is REFUTED.
#[test]
fn static_data_is_little_endian_and_big_endian_is_refuted() {
    let bytes = static_data_module();
    let le = LE_WITNESS.to_le_bytes();
    let m = decode_module(&bytes).expect("decodes");
    assert_eq!(
        m.data.first().map(|d| d.bytes.as_slice()),
        Some(&le[..]),
        "the emitted data image must be the little-endian one"
    );
    let obs = enc::target_conformance_obligations(&bytes, &[(0, &le[..])]);
    assert_no_refutations("little-endian witness", &obs);

    // ANTI-TAUTOLOGY: reverse the image (the big-endian lowering bug).
    let broken = enc::mutate_reverse_data_image(&bytes, 0).expect("a data image to reverse");
    assert_eq!(broken.len(), bytes.len());
    assert_ne!(broken, bytes);
    let r = report_of(&enc::target_conformance_obligations(
        &broken,
        &[(0, &le[..])],
    ));
    assert!(
        r.refuted > 0,
        "a BIG-ENDIAN static-data image survived — the endianness obligation is vacuous"
    );
    eprintln!(
        "static_data_is_little_endian_and_big_endian_is_refuted: {r}\n  {}",
        r.refutations.join("\n  ")
    );
}

/// ANTI-TAUTOLOGY (family 6): a memory64 limits flag in a real module must be
/// REFUTED — the wasm32 lane must never emit one.
#[test]
fn a_memory64_limits_flag_is_refuted() {
    let bytes = memory_module();
    assert!(
        decode_module(&bytes)
            .expect("decodes")
            .memories
            .iter()
            .all(|l| l.flag == 0x00),
        "the real module must declare MVP limits"
    );
    let broken = enc::mutate_memory64_flag(&bytes).expect("a memory section to mutate");
    assert_eq!(broken.len(), bytes.len());
    let r = report_of(&enc::target_conformance_obligations(&broken, &[]));
    assert!(
        r.refuted > 0,
        "a memory64 limits flag survived the conformance family"
    );
    // The decoder itself also fail-closes on it, which is where it is caught.
    assert!(decode_module(&broken).is_err());
    eprintln!("a_memory64_limits_flag_is_refuted: {r}");
}

/// THE P1 GUARD, CLOSED FROM THE OTHER SIDE. The conformance obligations above
/// say the emitted module SPENDS the wasm32 pin. This says the compile REFUSES
/// to run without it — so the pin is not merely declared, it is load-bearing.
#[test]
fn the_wasm32_pin_is_enforced_by_the_compiler() {
    let (triple, ptr_bytes, little) = WASM32_PIN;
    let canonical = wasm::wasm32_target_info();
    assert!(canonical.triple.starts_with(triple));
    assert_eq!(canonical.pointer_size, u32::from(ptr_bytes));
    assert_eq!(
        canonical.endianness == trust_ir::Endianness::Little,
        little,
        "the pin's endianness half"
    );

    let build = || {
        let mut mb = ModuleBuilder::new("pinned");
        let ft = mb.add_func_type(vec![Ty::I32], vec![Ty::I32]);
        let mut fb = mb.function("f", ft);
        let e = fb.create_block();
        let a = fb.add_block_param(e, Ty::I32);
        fb.switch_to_block(e);
        let one = fb.iconst(Ty::I32, 1);
        let r = fb.add(Ty::I32, a, one);
        fb.ret(vec![r]);
        fb.build();
        mb.build()
    };

    // The canonical pin compiles.
    let mut ok = build();
    ok.target_info = Some(wasm::wasm32_target_info());
    assert!(wasm::compile_module(&ok).is_ok());

    // Every mutation of the pin is REFUSED, and the refusal names the field.
    let mutations: Vec<(&str, Option<trust_ir::TargetInfo>, &str)> = vec![
        ("target-free", None, "target_info"),
        (
            "pointer_size 8",
            Some(trust_ir::TargetInfo {
                pointer_size: 8,
                ..wasm::wasm32_target_info()
            }),
            "pointer_size",
        ),
        (
            "big-endian",
            Some(trust_ir::TargetInfo {
                endianness: trust_ir::Endianness::Big,
                ..wasm::wasm32_target_info()
            }),
            "endianness",
        ),
        (
            "aarch64 triple",
            Some(trust_ir::TargetInfo {
                triple: "aarch64-apple-darwin".to_string(),
                ..wasm::wasm32_target_info()
            }),
            "triple",
        ),
    ];
    for (what, ti, must_name) in mutations {
        let mut m = build();
        m.target_info = ti;
        let err = wasm::compile_module(&m)
            .err()
            .unwrap_or_else(|| panic!("a {what} module must NOT enter the wasm32 lane"));
        let msg = err.to_string();
        assert!(
            msg.contains(must_name),
            "the {what} refusal must name `{must_name}`: {msg}"
        );
    }
    eprintln!(
        "the_wasm32_pin_is_enforced_by_the_compiler: 4 pin mutations, all REFUSED by the compiler"
    );
}

// ===========================================================================
// The honest tally
// ===========================================================================

/// The deferral list is pinned: removing one requires landing its evidence,
/// adding one is a reviewable admission of debt.
#[test]
fn the_named_deferrals_are_pinned() {
    assert_eq!(WASM_ENCODING_DEFERRALS.len(), 7);
    let mut names: Vec<&str> = WASM_ENCODING_DEFERRALS.iter().map(|d| d.name).collect();
    names.sort_unstable();
    let before = names.len();
    names.dedup();
    assert_eq!(names.len(), before, "deferral names must be distinct");
    for d in WASM_ENCODING_DEFERRALS {
        assert!(d.reason.len() > 120, "{}: token reason", d.name);
        assert!(!d.family.is_empty());
    }
    eprintln!("the_named_deferrals_are_pinned: {} RED rows", names.len());
    for d in WASM_ENCODING_DEFERRALS {
        eprintln!("  RED  {} -> {}", d.name, d.family);
    }
}

/// The whole family's real proven / refuted / not-applicable tally, printed as
/// numbers a reader can check, with every not-applicable row named.
#[test]
fn encoding_family_tally() {
    let mut total = EncodingReport::default();

    let const_obs = enc::emitted_const_immediate_obligations();
    let c = report_of(&const_obs);
    eprintln!("P4-5 const immediates (captured corpus): {c}");
    total.absorb(c);

    for (name, bytes) in module_corpus() {
        let i = report_of(&enc::module_indexing_obligations(&bytes));
        eprintln!("P4-4 {name}: {i}");
        total.absorb(i);
    }

    let closed = wasm::compile_module(&import_shift_ir_closed()).expect("closed");
    let island =
        wasm::compile_module_with_policy(&import_shift_ir(), &island_policy()).expect("island");
    let s = report_of(&enc::import_shift_obligations(
        &closed,
        &island,
        &["callee", "caller"],
    ));
    eprintln!("P4-4 import-shift differential: {s}");
    total.absorb(s);

    for (name, bytes) in module_corpus() {
        let owned = expected_le_image(name);
        let images: Vec<(usize, &[u8])> = owned.iter().map(|(i, b)| (*i, b.as_slice())).collect();
        let t = report_of(&enc::target_conformance_obligations(&bytes, &images));
        eprintln!("P4-6 {name}: {t}");
        total.absorb(t);
    }

    eprintln!("\n==== P4 encoder/byte family TOTAL: {total} ====");
    eprintln!(
        "  plus {} NAMED DEFERRALS, RED in the denominator:",
        WASM_ENCODING_DEFERRALS.len()
    );
    for d in WASM_ENCODING_DEFERRALS {
        eprintln!("    RED  {}", d.name);
    }
    if !total.inapplicable.is_empty() {
        eprintln!(
            "  {} NOT-APPLICABLE row(s) (absent construct — NOT credit):",
            total.not_applicable
        );
        for line in &total.inapplicable {
            eprintln!("    n/a  {line}");
        }
    }
    assert_eq!(
        total.refuted,
        0,
        "refutations:\n  {}",
        total.refutations.join("\n  ")
    );
    // THE HEADLINE, pinned so it cannot drift silently: 210 proven / 0 refuted
    // / 108 not-applicable, plus 7 named RED deferrals.
    //
    //   74  family (5), the captured const-immediate corpus
    //  114  family (4) over the 9-module corpus
    //    4  family (4), the two-compile import-shift differential
    //   18  family (6) over the same corpus
    //
    // It was 284/0/52 before the audit of 2026-08-27, and the drop is the point:
    // 18 rows that no module could refute were removed (a `total_funcs() ==
    // func_import_count() + func_type_idx.len()` self-equality, and a duplicate
    // "materializes addresses as i32" row that only scanned data-segment
    // offsets), and every remaining quantified row now reports not-applicable on
    // an empty domain instead of banking it as credit. A count that fell because
    // vacuous rows stopped counting is a more honest count, not a worse one.
    assert_eq!(
        (total.proven, total.refuted, total.not_applicable),
        (210, 0, 108),
        "the P4 encoder/byte family headline moved: {total}. Re-derive it and update the pins in \
         this file and the P4 line of SOUNDNESS_CHECK.md; never adjust the pin to match a row \
         that cannot fail"
    );
}
