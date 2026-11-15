// trust-cg-verify/tests/support/wasm_never_selected_live_scan.rs - the never-selected exclusions, checked against live emission
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! LIVENESS for the never-selected exclusions of the wasm gates.
//!
//! `GateArch::WasmValueDomain` excludes the twelve `i64` sub-word access and
//! `i64` sign-extension bytes, and `GateArch::Wasm` the v128 forms, as NEVER
//! SELECTED: outside the credited denominator because no emitted module
//! contains them. That premise is a fact about the lowering, so it is checked
//! against the lowering: a corpus of trust-ir modules that reaches every
//! integer width conversion, every scalar load and store type, narrow
//! arithmetic, float conversions, 128-bit values, struct field traffic and
//! the call / table fixtures is compiled through the LIVE backend and scanned
//! with `wasm_value_domain::never_selected_opcodes_in`. One module per v128
//! form (`v128.const`, `v128.load`/`store`, the four lane-wise ops) must be
//! either refused at the vector carrier, the one guard that keeps them
//! unselected today, or compiled and scanned like the rest. A lowering change that
//! emits an excluded opcode (an `i64.extend32_s` for a sign extension, an
//! `i64.load8_u` for a byte) fails the gates that pin the exclusions, instead
//! of leaving emitted code outside a denominator reported as complete.
//!
//! Shared via `#[path]` by `coverage_gate_tests` and `wasm_value_domain_gate`.

#![allow(dead_code)]

use trust_cg_codegen::wasm::{self, WasmFuncImportPolicy, WasmModulePolicy, island_host_namespace};
use trust_cg_verify::coverage_gate::{ALL_WASM_OPCODES, OpcodeClass, classify_wasm};
use trust_cg_verify::wasm_abi_proofs::WASM_ABI_FIXTURES;
use trust_cg_verify::wasm_memarg_offset_proofs::MEMARG_FIELDS_TIR;
use trust_cg_verify::wasm_value_domain::{SIMD_PREFIX, never_selected_opcodes_in};

/// Every integer width change between the narrow, word and 64-bit types, in
/// both directions, and the float conversions from and to narrow integers.
const WIDTHS: &str = r#"; TrustIr text format v1
module "never_selected_widths"
target "wasm32-unknown-unknown" 4 little

functy.0 = (i8, u8, i16, u16, i32, u32, bool) -> (i64)
functy.1 = (i8, u8, i16, u16, i32, u32, bool) -> (u64)
functy.2 = (i64) -> (i32)
functy.3 = (i64, i32) -> (i64)
functy.4 = (f64, f32) -> (i64)
functy.5 = (i8, u16, i64) -> (f64)

fn @sext64(functy.0) {
bb0(%0: i8, %1: u8, %2: i16, %3: u16, %4: i32, %5: u32, %6: bool):
    %7 = sext i8 %0 to i64
    %8 = sext i16 %2 to i64
    %9 = sext i32 %4 to i64
    %10 = zext u8 %1 to i64
    %11 = zext u16 %3 to i64
    %12 = zext u32 %5 to i64
    %13 = zext bool %6 to i64
    %14 = add i64 %7, %8
    %15 = add i64 %14, %9
    %16 = add i64 %15, %10
    %17 = add i64 %16, %11
    %18 = add i64 %17, %12
    %19 = add i64 %18, %13
    ret %19
}

fn @zext64(functy.1) {
bb0(%0: i8, %1: u8, %2: i16, %3: u16, %4: i32, %5: u32, %6: bool):
    %7 = zext i8 %0 to u64
    %8 = zext i16 %2 to u64
    %9 = zext i32 %4 to u64
    %10 = sext u8 %1 to u64
    %11 = sext u16 %3 to u64
    %12 = sext u32 %5 to u64
    %13 = add u64 %7, %8
    %14 = add u64 %13, %9
    %15 = add u64 %14, %10
    %16 = add u64 %15, %11
    %17 = add u64 %16, %12
    ret %17
}

fn @narrow(functy.2) {
bb0(%0: i64):
    %1 = trunc i64 %0 to i8
    %2 = trunc i64 %0 to u16
    %3 = trunc i64 %0 to i32
    %4 = add i8 %1, %1
    %5 = mul u16 %2, %2
    %6 = sext i8 %4 to i32
    %7 = zext u16 %5 to i32
    %8 = add i32 %6, %7
    %9 = add i32 %8, %3
    ret %9
}

fn @mixed(functy.3) {
bb0(%0: i64, %1: i32):
    %2 = trunc i64 %0 to i16
    %3 = sext i16 %2 to i64
    %4 = trunc i32 %1 to i8
    %5 = sext i8 %4 to i64
    %6 = sext i32 %1 to i64
    %7 = mul i64 %3, %5
    %8 = sub i64 %7, %6
    ret %8
}

fn @floats(functy.4) {
bb0(%0: f64, %1: f32):
    %2 = fptosi f64 %0 to i8
    %3 = fptoui f32 %1 to u16
    %4 = fptosi f64 %0 to i32
    %5 = sext i8 %2 to i64
    %6 = zext u16 %3 to i64
    %7 = sext i32 %4 to i64
    %8 = add i64 %5, %6
    %9 = add i64 %8, %7
    ret %9
}

fn @tofloat(functy.5) {
bb0(%0: i8, %1: u16, %2: i64):
    %3 = sitofp i8 %0 to f64
    %4 = uitofp u16 %1 to f64
    %5 = sitofp i64 %2 to f64
    %6 = fadd f64 %3, %4
    %7 = fadd f64 %6, %5
    ret %7
}
"#;

/// Loads and stores of every scalar type through a pointer, and 128-bit
/// arithmetic and widening.
const MEMORY_AND_WIDE: &str = r#"; TrustIr text format v1
module "never_selected_memory"
target "wasm32-unknown-unknown" 4 little

functy.0 = (ptr, i64) -> (i64)
functy.1 = (i64, i64) -> (i64)

fn @roundtrip(functy.0) {
bb0(%0: ptr, %1: i64):
    %2 = trunc i64 %1 to i8
    store i8 %2, ptr %0
    %3 = load i8, ptr %0
    %4 = sext i8 %3 to i64
    %5 = trunc i64 %1 to u8
    store u8 %5, ptr %0
    %6 = load u8, ptr %0
    %7 = zext u8 %6 to i64
    %8 = trunc i64 %1 to i16
    store i16 %8, ptr %0
    %9 = load i16, ptr %0
    %10 = sext i16 %9 to i64
    %11 = trunc i64 %1 to u16
    store u16 %11, ptr %0
    %12 = load u16, ptr %0
    %13 = zext u16 %12 to i64
    %14 = trunc i64 %1 to i32
    store i32 %14, ptr %0
    %15 = load i32, ptr %0
    %16 = sext i32 %15 to i64
    %17 = trunc i64 %1 to u32
    store u32 %17, ptr %0
    %18 = load u32, ptr %0
    %19 = zext u32 %18 to i64
    store i64 %1, ptr %0
    %20 = load i64, ptr %0
    %21 = bitcast i64 %1 to f64
    store f64 %21, ptr %0
    %22 = load f64, ptr %0
    %23 = fptosi f64 %22 to i64
    %24 = add i64 %4, %7
    %25 = add i64 %24, %10
    %26 = add i64 %25, %13
    %27 = add i64 %26, %16
    %28 = add i64 %27, %19
    %29 = add i64 %28, %20
    %30 = add i64 %29, %23
    ret %30
}

fn @wide(functy.1) {
bb0(%0: i64, %1: i64):
    %2 = sext i64 %0 to i128
    %3 = zext i64 %1 to i128
    %4 = mul i128 %2, %3
    %5 = add i128 %4, %2
    %6 = trunc i128 %5 to i64
    ret %6
}
"#;

/// Re-create the compile policy an ABI fixture's `policy` tag names.
fn policy_for(tag: &str) -> WasmModulePolicy {
    match tag {
        "closed" => WasmModulePolicy::closed(),
        "func-imports:trust:island/calls@1" => WasmModulePolicy {
            func_imports: WasmFuncImportPolicy::FromModule(island_host_namespace("calls")),
            ..WasmModulePolicy::closed()
        },
        "island:abi" => WasmModulePolicy::island("abi"),
        other => panic!("unknown fixture policy tag `{other}`"),
    }
}

/// One module per never-selected v128 form, as trust-ir vector values.
const VECTOR_FORMS: [(&str, &str); 6] = [
    (
        "v128_const",
        "functy.0 = () -> (<4 x i32>)\n\nfn @f(functy.0) {\nbb0:\n    %0 = const <4 x i32> vec[1, 2, 3, 4]\n    ret %0\n}\n",
    ),
    (
        "v128_load_store",
        "functy.0 = (ptr, ptr) -> ()\n\nfn @f(functy.0) {\nbb0(%0: ptr, %1: ptr):\n    %2 = load <4 x i32>, ptr %0\n    store <4 x i32> %2, ptr %1\n    ret\n}\n",
    ),
    (
        "i32x4_add",
        "functy.0 = (<4 x i32>, <4 x i32>) -> (<4 x i32>)\n\nfn @f(functy.0) {\nbb0(%0: <4 x i32>, %1: <4 x i32>):\n    %2 = add <4 x i32> %0, %1\n    ret %2\n}\n",
    ),
    (
        "i32x4_mul",
        "functy.0 = (<4 x i32>, <4 x i32>) -> (<4 x i32>)\n\nfn @f(functy.0) {\nbb0(%0: <4 x i32>, %1: <4 x i32>):\n    %2 = mul <4 x i32> %0, %1\n    ret %2\n}\n",
    ),
    (
        "f32x4_add",
        "functy.0 = (<4 x f32>, <4 x f32>) -> (<4 x f32>)\n\nfn @f(functy.0) {\nbb0(%0: <4 x f32>, %1: <4 x f32>):\n    %2 = fadd <4 x f32> %0, %1\n    ret %2\n}\n",
    ),
    (
        "f32x4_mul",
        "functy.0 = (<4 x f32>, <4 x f32>) -> (<4 x f32>)\n\nfn @f(functy.0) {\nbb0(%0: <4 x f32>, %1: <4 x f32>):\n    %2 = fmul <4 x f32> %0, %1\n    ret %2\n}\n",
    ),
];

/// The scanned corpus, compiled by the LIVE backend: `(name, module bytes)`.
/// A [`VECTOR_FORMS`] module the backend refuses at the vector carrier emits
/// nothing and is not listed; one it compiles is.
pub fn live_corpus() -> Vec<(String, Vec<u8>)> {
    let mut out = Vec::new();
    for (name, body) in VECTOR_FORMS {
        let text = format!(
            "; TrustIr text format v1\nmodule \"{name}\"\ntarget \"wasm32-unknown-unknown\" 4 little\n\n{body}"
        );
        let module = trust_ir::parser::parse_module(&text)
            .unwrap_or_else(|e| panic!("{name}: the vector form does not parse: {e:?}"));
        match wasm::compile_module_with_license(&module, &permit_unlicensed()) {
            Ok(bytes) => out.push((name.to_string(), bytes)),
            Err(e) => assert!(
                e.to_string().contains("no wasm32 carrier"),
                "{name}: refused, but not at the vector carrier: {e}"
            ),
        }
    }
    for (name, text) in [
        ("never_selected_widths", WIDTHS),
        ("never_selected_memory", MEMORY_AND_WIDE),
        ("memarg_fields", MEMARG_FIELDS_TIR),
    ] {
        let module = trust_ir::parser::parse_module(text)
            .unwrap_or_else(|e| panic!("{name}: the corpus text does not parse: {e:?}"));
        let bytes = wasm::compile_module_with_license(&module, &permit_unlicensed())
            .unwrap_or_else(|e| panic!("{name}: the live backend refused the corpus: {e}"));
        out.push((name.to_string(), bytes));
    }
    for f in WASM_ABI_FIXTURES {
        let module = trust_ir::parser::parse_module(f.tir).expect("the fixture parses");
        let bytes = wasm::compile_module_with_policy_and_license(
            &module,
            &policy_for(f.policy),
            &permit_unlicensed(),
        )
        .unwrap_or_else(|e| panic!("{}: the live backend refused the fixture: {e}", f.name));
        out.push((f.name.to_string(), bytes));
    }
    out
}

/// Every never-selected wasm row the coverage gate excludes (`GateArch::Wasm`)
/// is a v128 form, so the scanner's `0xfd` check covers it; the value-domain
/// exclusions are scanned byte by byte.
pub fn assert_every_excluded_wasm_opcode_is_under_the_simd_prefix() {
    let mut excluded = 0;
    for &op in ALL_WASM_OPCODES {
        if let OpcodeClass::FailClosedAllowlisted { reason } = classify_wasm(op)
            && reason.contains("never selected")
        {
            assert_eq!(
                op.opcode_byte(),
                SIMD_PREFIX,
                "{op:?} is excluded as never selected but is not 0xfd-prefixed, so the \
                 never-selected scan does not see it"
            );
            excluded += 1;
        }
    }
    assert_eq!(excluded, 7, "the 7 never-selected v128 forms");
}

/// PINS the never-selected exclusions on the live backend: no module of the
/// corpus contains an excluded opcode. Returns the number of modules scanned.
pub fn assert_no_never_selected_opcode_is_emitted() -> usize {
    assert_every_excluded_wasm_opcode_is_under_the_simd_prefix();
    let corpus = live_corpus();
    for (name, bytes) in &corpus {
        let hits = never_selected_opcodes_in(bytes)
            .unwrap_or_else(|e| panic!("{name}: the scan cannot read the module: {e}"));
        assert!(
            hits.is_empty(),
            "{name}: the live backend emits never-selected opcodes {hits:?} — an excluded row is \
             emitted code; it must re-enter the credited denominator with its evidence"
        );
    }
    corpus.len()
}

/// The scan has teeth: a live module with its `i64.extend_i32_s` (0xac)
/// replaced by `i64.extend32_s` (0xc4) — the equivalent-looking lowering the
/// exclusion must not hide — and with it replaced by the `0xfd` prefix are
/// both reported, as is an `i64.load8_u` (0x31) in place of an `i64.load`.
pub fn assert_the_scan_reports_an_emitted_excluded_opcode() {
    let module = trust_ir::parser::parse_module(WIDTHS).expect("parses");
    let bytes = wasm::compile_module_with_license(&module, &permit_unlicensed()).expect("compiles");
    let patch = |from: u8, to: u8| -> Vec<u8> {
        let decoded = trust_cg_verify::wasm_abi_proofs::decode_module(&bytes).expect("decodes");
        for body in &decoded.bodies {
            let base = bytes
                .windows(body.code.len())
                .position(|w| w == body.code.as_slice())
                .expect("the body occurs in the module");
            let insts =
                trust_cg_verify::wasm_abi_proofs::decode_insts(&body.code).expect("decodes");
            if let Some(i) = insts.iter().find(|i| i.op == from) {
                let mut out = bytes.clone();
                out[base + i.at] = to;
                return out;
            }
        }
        panic!("no 0x{from:02x} in the corpus module");
    };
    for (from, to) in [(0xac, 0xc4), (0xac, SIMD_PREFIX)] {
        let hits = never_selected_opcodes_in(&patch(from, to)).expect("scans");
        assert!(
            !hits.is_empty(),
            "the scan missed 0x{to:02x} emitted in place of 0x{from:02x}"
        );
    }
    let module = trust_ir::parser::parse_module(MEMORY_AND_WIDE).expect("parses");
    let bytes_mem =
        wasm::compile_module_with_license(&module, &permit_unlicensed()).expect("compiles");
    let decoded = trust_cg_verify::wasm_abi_proofs::decode_module(&bytes_mem).expect("decodes");
    let body = &decoded.bodies[0];
    let base = bytes_mem
        .windows(body.code.len())
        .position(|w| w == body.code.as_slice())
        .expect("the body occurs");
    let insts = trust_cg_verify::wasm_abi_proofs::decode_insts(&body.code).expect("decodes");
    let load = insts
        .iter()
        .find(|i| i.op == 0x29)
        .expect("an i64.load in the roundtrip");
    let mut out = bytes_mem.clone();
    out[base + load.at] = 0x31;
    let hits = never_selected_opcodes_in(&out).expect("scans");
    assert!(
        hits.iter().any(|(_, _, what)| what.contains("0x31")),
        "the scan missed an i64.load8_u: {hits:?}"
    );
}

/// This module's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes (or is refused) because the license silently refused it.
fn permit_unlicensed() -> trust_cg_codegen::CodegenLicensePolicy {
    trust_cg_codegen::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_codegen::UnlicensedBodyPolicy::Permit)
}
