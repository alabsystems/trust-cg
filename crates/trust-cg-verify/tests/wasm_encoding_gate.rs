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

/// The float const and float binop corpora, re-derived from the live backend
/// (shared with `coverage_gate_tests`, which pins the ratio those rows move).
#[path = "support/wasm_float_live_emit.rs"]
mod float_live;

/// The guarded MemCopy / MemSet bodies, re-derived from the live backend
/// (shared with `coverage_gate_tests`, which pins the ratio those rows move).
#[path = "support/wasm_bulk_memory_live_emit.rs"]
mod bulk_live;

use wasm::{
    WasmFuncImportPolicy, WasmMemoryGrowthPolicy, WasmModulePolicy, WasmStaticDataPolicy,
    island_host_namespace,
};

// ---------------------------------------------------------------------------
// Module builders — the corpus of real modules the obligations run over
// ---------------------------------------------------------------------------

/// The lane at its default level without the trust-ir mid-end: the modules
/// that exist to put real `call` immediates in the bytes compile through it,
/// because the mid-end's inliner would splice their direct calls away.
fn lane_with_policy(
    module: &trust_ir::Module,
    policy: &WasmModulePolicy,
) -> Result<Vec<u8>, wasm::WasmLowerError> {
    wasm::compile_module_with_evidence_policy_license_options(
        module,
        policy,
        &permit_unlicensed(),
        wasm::WasmOptOptions {
            level: trust_cg_codegen::pipeline::OptLevel::O2,
            mid_end: false,
        },
    )
    .map(|(bytes, _)| bytes)
}

/// [`lane_with_policy`] for a closed module.
fn lane(module: &trust_ir::Module) -> Result<Vec<u8>, wasm::WasmLowerError> {
    lane_with_policy(module, &WasmModulePolicy::closed())
}

fn finish_wasm32(mb: ModuleBuilder) -> trust_ir::Module {
    let mut m = mb.build().expect("ModuleBuilder::build: test fixture");
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
    wasm::compile_module_with_policy_and_license(
        &finish_wasm32(mb),
        &trust_cg_codegen::wasm::WasmModulePolicy::closed(),
        &permit_unlicensed(),
    )
    .expect("const module must compile")
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
        wasm::compile_module_with_policy_and_license(&m, &island_policy(), &permit_unlicensed())
            .expect("island table compiles")
    } else {
        wasm::compile_module_with_policy_and_license(
            &m,
            &trust_cg_codegen::wasm::WasmModulePolicy::closed(),
            &permit_unlicensed(),
        )
        .expect("closed table compiles")
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
        // trust-ir v41: an ordinary, unretained global in the consumer-chosen section.
        section: None,
        visibility: trust_ir::Visibility::Default,
        retained: false,
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
    wasm::compile_module_with_policy_and_license(
        &finish_wasm32(mb),
        &trust_cg_codegen::wasm::WasmModulePolicy::closed(),
        &permit_unlicensed(),
    )
    .expect("static-data module compiles")
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
    wasm::compile_module_with_policy_and_license(
        &finish_wasm32(mb),
        &trust_cg_codegen::wasm::WasmModulePolicy::closed(),
        &permit_unlicensed(),
    )
    .expect("memory module compiles")
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
        // trust-ir v41: an ordinary, unretained global in the consumer-chosen section.
        section: None,
        visibility: trust_ir::Visibility::Default,
        retained: false,
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
    lane_with_policy(&finish_wasm32(mb), &policy).expect("the full-surface island must compile")
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
            lane(&import_shift_ir_closed()).expect("closed calls compile"),
        ),
        (
            "island calls (2 func imports)",
            lane_with_policy(&import_shift_ir(), &island_policy()).expect("island calls compile"),
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

// ===========================================================================
// FAMILY (5), FLOAT — the raw IEEE-754 payloads, against the LIVE backend
// ===========================================================================

/// THE FRESHNESS CONTRACT for the float const credit: every captured payload
/// is re-derived by compiling a real `() -> fN` module and decoding it.
#[test]
fn float_const_corpus_is_what_the_live_backend_emits_today() {
    let checked = float_live::assert_float_const_corpus_is_what_the_live_backend_emits();
    assert_eq!(checked, enc::EMITTED_FLOAT_CONST_IMMEDIATES.len());
    eprintln!(
        "float_const_corpus_is_what_the_live_backend_emits_today: {checked} payloads re-derived, \
         all byte-identical"
    );
}

/// The float const obligation over LIVE bytes: each compiled module's payload
/// is bit-exactly the pattern its carrier denotes.
#[test]
fn live_float_const_immediates_denote_their_intended_pattern() {
    let mut obs = Vec::new();
    for &(carrier, bits, _) in enc::EMITTED_FLOAT_CONST_IMMEDIATES {
        let module = float_live::float_const_module(bits, carrier);
        let (op, imm) = float_live::first_float_const_immediate(&module);
        obs.push(enc::float_const_immediate_obligation(carrier, op, &imm));
    }
    let r = assert_no_refutations("live float const immediates", &obs);
    assert_eq!(r.proven, enc::EMITTED_FLOAT_CONST_IMMEDIATES.len());
}

/// ANTI-TAUTOLOGY, against LIVE bytes: every negative control built from a real
/// emitted payload refutes, and for its stated reason; every control that
/// applies at a width is built at least once there.
#[test]
fn live_float_const_controls_refute_for_their_stated_reason() {
    use enc::FloatConstControl;
    let mut built = std::collections::BTreeMap::<(u32, String), usize>::new();
    let mut wrong = Vec::new();
    for &(carrier, bits, _) in enc::EMITTED_FLOAT_CONST_IMMEDIATES {
        let module = float_live::float_const_module(bits, carrier);
        let (_, imm) = float_live::first_float_const_immediate(&module);
        for control in FloatConstControl::ALL {
            let Some((claimed, op, bytes)) = control.build(carrier, bits, &imm) else {
                continue;
            };
            *built.entry((bits, format!("{control:?}"))).or_default() += 1;
            match enc::float_const_immediate_verdict(claimed, op, &bytes) {
                Err(why) if control.is_its_refutation(bits, &why) => {}
                other => wrong.push(format!(
                    "f{bits} carrier 0x{carrier:016x} {control:?}: {other:?} ({bytes:02x?})"
                )),
            }
        }
    }
    assert!(
        wrong.is_empty(),
        "controls that did not refute for their reason:\n  {}",
        wrong.join("\n  ")
    );
    for bits in [32u32, 64] {
        for control in FloatConstControl::ALL {
            if control.applies_at(bits) {
                assert!(
                    built.contains_key(&(bits, format!("{control:?}"))),
                    "{control:?} was never built at f{bits}: it is not evidence there"
                );
            }
        }
    }
    eprintln!("live_float_const_controls: {built:?}");
}

/// The intended patterns are the trust-ir side, so they are checked against the
/// ground truth they transcribe: for every entry, the pattern the reference
/// interpreter materializes for the constant equals the stated one (the
/// narrowing at 32 bits, NaN payloads included, on this host).
#[test]
fn stated_f32_narrowing_is_what_the_reference_interpreter_materializes() {
    use trust_ir::FuncId;
    use trust_ir::interpret::{InterpretValueKind, Interpreter};
    let mut checked = 0usize;
    for &(carrier, bits, _) in enc::EMITTED_FLOAT_CONST_IMMEDIATES {
        let module = float_live::float_const_ir(bits, carrier);
        let outcome = Interpreter::with_module(&module)
            .execute_func(FuncId::new(0), vec![])
            .expect("a float const function executes");
        let InterpretValueKind::FloatBits(pattern) = outcome.returns[0].kind else {
            panic!("f{bits} const returned {:?}", outcome.returns[0]);
        };
        assert_eq!(
            Some(pattern),
            enc::trust_ir_float_const_bits(carrier, bits),
            "f{bits} carrier 0x{carrier:016x}: the interpreter materializes 0x{pattern:x}"
        );
        checked += 1;
    }
    assert_eq!(checked, enc::EMITTED_FLOAT_CONST_IMMEDIATES.len());
}

/// The stated narrowing agrees bit-exactly with the host binary64-to-binary32
/// conversion (the one the reference interpreter uses) at every ROUNDING
/// BOUNDARY, which a random sweep essentially never reaches (a tie needs all 29
/// dropped bits to equal exactly `1 << 28`). For every binary64 exponent whose
/// binary32 result is normal, subnormal, or rounds to zero at the half of the
/// least subnormal, and for both signs, the dropped bits are set to the exact
/// half quantum and to one unit either side of it, under kept bits with both
/// parities (so ties round both down and up to even), plus all-ones kept bits
/// (so a tie carries into the exponent, and past `f32::MAX` into infinity).
/// Finite carriers only: the NaN payload rule is pinned by the live corpus.
#[test]
fn stated_f32_narrowing_matches_the_host_conversion_at_every_rounding_boundary() {
    const MANT_MASK: u64 = (1 << 52) - 1;
    const HIDDEN: u64 = 1 << 52;
    let mut state = 0x2545_f491_4f6c_dd1du64;
    let mut checked = 0usize;
    let mut ties = 0usize;
    // Biased binary64 exponents: 873 puts the least-subnormal half at the
    // hidden bit (binary32 result 0 or the least subnormal), 874..=896 give
    // subnormal results, 897..=1150 normal ones.
    for exp in 873u64..=1150 {
        // Bits of the 53-bit significand below the binary32 result quantum.
        let dropped: u32 = if exp >= 897 { 29 } else { (926 - exp) as u32 };
        let half = 1u64 << (dropped - 1);
        let low_mask = (1u64 << dropped) - 1;
        for pattern in 0..34u32 {
            let high = match pattern {
                0 => 0,
                1 => u64::MAX,
                _ => {
                    state ^= state << 13;
                    state ^= state >> 7;
                    state ^= state << 17;
                    // Kept-bit parity alternates with the pattern index.
                    (state & !(1 << dropped)) | (u64::from(pattern & 1) << dropped)
                }
            };
            for low in [half - 1, half, half + 1] {
                let significand = ((high & !low_mask) | low) & (HIDDEN | MANT_MASK);
                let significand = if dropped == 53 {
                    significand
                } else {
                    significand | HIDDEN
                };
                if significand & HIDDEN == 0 {
                    // Not representable at this exponent (a 53-bit drop below
                    // the half): covered by the neighbouring exponent.
                    continue;
                }
                for sign in [0u64, 1 << 63] {
                    let carrier = sign | (exp << 52) | (significand & MANT_MASK);
                    let host = (f64::from_bits(carrier) as f32).to_bits();
                    assert_eq!(
                        enc::spec_narrow_binary64_to_binary32(carrier),
                        host,
                        "carrier 0x{carrier:016x} (exponent {exp}, dropped {dropped})"
                    );
                    checked += 1;
                    ties += usize::from(low == half);
                }
            }
        }
    }
    assert!(
        checked > 50_000 && ties > 15_000,
        "{checked} checked, {ties} ties"
    );
}

// ===========================================================================
// f.min / f.max / copysign — the emitted BODIES, against the LIVE backend
// ===========================================================================

/// THE FRESHNESS CONTRACT for the float binop bodies.
#[test]
fn float_binop_bodies_are_what_the_live_backend_emits_today() {
    let checked = float_live::assert_float_binop_bodies_are_what_the_live_backend_emits();
    assert_eq!(checked, 6);
}

/// Over LIVE bodies: each executes and meets the relational trust-ir contract
/// on the whole battery for every wasm NaN choice, and each of its controls
/// refutes at its stated input class.
#[test]
fn live_float_binop_bodies_hold_and_their_controls_refute() {
    use trust_cg_verify::wasm_float_binop_proofs::{
        FloatBinopControl, TieReading, check_float_binop_body,
    };
    for &(kind, bits, _) in trust_cg_verify::wasm_float_binop_proofs::EMITTED_FLOAT_BINOP_BODIES {
        let entries = float_live::code_entries(&float_live::float_binop_module(kind, bits));
        let live = &entries[0];
        let v = check_float_binop_body(kind, bits, live, TieReading::EitherOperand);
        assert!(v.holds(), "{kind:?} f{bits}: {v:#?}");
        for control in FloatBinopControl::ALL {
            if !control.applies_to(kind) {
                continue;
            }
            let (mutated, tie) = control
                .build(kind, bits, live)
                .unwrap_or_else(|| panic!("{control:?} cannot be built on {kind:?} f{bits}"));
            let cv = check_float_binop_body(kind, bits, &mutated, tie);
            assert!(
                cv.refusal.is_none(),
                "{control:?} {kind:?} f{bits}: {cv:#?}"
            );
            assert!(
                !cv.refuted_classes.is_empty(),
                "{control:?} SURVIVED on {kind:?} f{bits}"
            );
            if let Some(class) = control.stated_class() {
                assert!(
                    cv.refuted_classes.contains(&class),
                    "{control:?} on {kind:?} f{bits} refuted at {:?}, not its stated {class:?}",
                    cv.refuted_classes
                );
            }
        }
    }
}

/// Every captured guarded MemCopy / MemSet body is what the live backend emits.
#[test]
fn bulk_memory_bodies_are_what_the_live_backend_emits_today() {
    let checked = bulk_live::assert_bulk_memory_bodies_are_what_the_live_backend_emits();
    assert_eq!(checked, 3);
}

/// Over LIVE bodies: each passes the operand-provenance check, executes on
/// the model memory and meets the relational trust-ir contract on every
/// battery class, observes every operand bit below `OBSERVED_OPERAND_BITS`,
/// and each of its controls refutes — at its stated input class on the
/// battery, and an operand mask also on the provenance check. The unguarded
/// body (the lowering before the zero-length guard) fails at exactly the
/// zero-byte range past the memory.
#[test]
fn live_bulk_memory_bodies_hold_and_their_controls_refute() {
    use trust_cg_verify::wasm_bulk_memory_proofs::{
        BulkInputClass, BulkMemoryControl, BulkMemoryShape, CopyModel, bulk_operand_provenance,
        check_bulk_memory_body, decode_bulk_body, unobserved_operand_bits,
    };
    for shape in BulkMemoryShape::ALL {
        let live = decode_bulk_body(&bulk_live::live_bulk_memory_body(shape))
            .unwrap_or_else(|e| panic!("{shape:?}: the live body does not decode: {e}"));
        assert_eq!(live.count_op(shape.sub_opcode()), 1, "{shape:?}");
        bulk_operand_provenance(shape, &live)
            .unwrap_or_else(|e| panic!("{shape:?}: live operand provenance: {e}"));
        let v = check_bulk_memory_body(shape, &live, CopyModel::Spec);
        assert!(v.holds(), "{shape:?}: {v:#?}");
        assert_eq!(
            unobserved_operand_bits(shape, &live),
            Ok(Vec::new()),
            "{shape:?}: an operand bit below the model width is not observed"
        );
        let mut refuted_controls = 0;
        let mut provenance_only = 0;
        for control in BulkMemoryControl::ALL {
            if !control.applies_to(shape) {
                continue;
            }
            let (mutated, model) = control
                .build(&live)
                .unwrap_or_else(|| panic!("{control:?} cannot be built on {shape:?}"));
            if matches!(control, BulkMemoryControl::OperandMasked { .. }) {
                assert!(
                    bulk_operand_provenance(shape, &mutated).is_err(),
                    "{control:?} on {shape:?}: the provenance check accepts it"
                );
            }
            let Some(class) = control.stated_class(shape) else {
                provenance_only += 1;
                continue;
            };
            let cv = check_bulk_memory_body(shape, &mutated, model);
            assert!(cv.refusal.is_none(), "{control:?} {shape:?}: {cv:#?}");
            assert!(
                cv.refuted_classes.contains(&class),
                "{control:?} on {shape:?} refuted at {:?}, not its stated {class:?}",
                cv.refuted_classes
            );
            refuted_controls += 1;
        }
        assert!(
            refuted_controls >= 7,
            "{shape:?}: the control battery shrank ({refuted_controls})"
        );
        assert_eq!(
            provenance_only, 1,
            "{shape:?}: the count mask past the model must be a provenance-only control"
        );
        // The guard is exactly what separates the body from the old lowering.
        let (bare, model) = BulkMemoryControl::Unguarded.build(&live).expect("builds");
        let bv = check_bulk_memory_body(shape, &bare, model);
        assert_eq!(
            bv.refuted_classes,
            std::collections::BTreeSet::from([BulkInputClass::ZeroLengthOutOfBounds]),
            "{shape:?}: without its guard the body must fail at exactly the zero-length class"
        );
    }
}

/// EXHAUSTIVE over the full i32 range: every `v: i32` encoded by the backend's
/// own `write_sleb128` (the function the module path calls) must decode, under
/// the INDEPENDENT spec decoder, to exactly `v` at canonical length.
///
/// `#[ignore]`d because it is 4.29e9 iterations: run it with
/// `scripts/trust_cargo.sh test -p trust-cg-verify --release --test wasm_encoding_gate
/// -- --ignored --nocapture`.
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
/// makes "112 proven" mean 112 rows with something under them. (It was
/// 114 / 69 before the local emission pass: the two `() -> iN { ret -1 }`
/// modules no longer reference any local, their constant being
/// rematerialized at the `return`, so their local-index row is not
/// applicable.)
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
        (112, 71),
        "the family-(4) split over the 9-module corpus moved: {total}. Re-derive it, and update \
         `encoding_family_tally`'s pin and the P4 line of SOUNDNESS_CHECK.md with it"
    );
}

/// THE P2 SHIFT, as a differential over two real compiles of the SAME trust-ir.
#[test]
fn the_import_shift_holds_over_real_bytes() {
    let closed = lane(&import_shift_ir_closed()).expect("closed compiles");
    let island = lane_with_policy(&import_shift_ir(), &island_policy()).expect("island compiles");
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
    let closed = lane(&import_shift_ir_closed()).expect("closed compiles");
    let island = lane_with_policy(&import_shift_ir(), &island_policy()).expect("island compiles");
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
            "element vector entry i is function i",
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
        mb.build().expect("ModuleBuilder::build: test fixture")
    };

    // The canonical pin compiles.
    let mut ok = build();
    ok.target_info = Some(wasm::wasm32_target_info());
    assert!(
        wasm::compile_module_with_policy_and_license(
            &ok,
            &trust_cg_codegen::wasm::WasmModulePolicy::closed(),
            &permit_unlicensed()
        )
        .is_ok()
    );

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
        let err = wasm::compile_module_with_policy_and_license(
            &m,
            &trust_cg_codegen::wasm::WasmModulePolicy::closed(),
            &permit_unlicensed(),
        )
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
    assert_eq!(WASM_ENCODING_DEFERRALS.len(), 6);
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

    let closed = lane(&import_shift_ir_closed()).expect("closed");
    let island = lane_with_policy(&import_shift_ir(), &island_policy()).expect("island");
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
    // THE HEADLINE, pinned so it cannot drift silently: 208 proven / 0 refuted
    // / 110 not-applicable, plus 6 named RED deferrals. The float const
    // obligations are pinned by their own targets below and by the coverage
    // gate, not folded into this tally.
    //
    //   74  family (5), the captured const-immediate corpus
    //  112  family (4) over the 9-module corpus (114 before the local
    //       emission pass left the two const modules with no local reference)
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
        (208, 0, 110),
        "the P4 encoder/byte family headline moved: {total}. Re-derive it and update the pins in \
         this file and the P4 line of SOUNDNESS_CHECK.md; never adjust the pin to match a row \
         that cannot fail"
    );
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes because it was silently refused.
fn permit_unlicensed() -> trust_cg_codegen::CodegenLicensePolicy {
    trust_cg_codegen::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_codegen::UnlicensedBodyPolicy::Permit)
}
