// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Ledger L05-P11: the dialect rows of the pinned trust-ir conformance corpus,
//! legalized by registry-driven rules (`trust_cg_codegen::dialect_legalization`)
//! and executed natively on this AArch64 host, both as an AOT object linked
//! with a C driver and in-process through the JIT, at O0 through O3.
//!
//! Every native result is compared with an interpretation of the dialect
//! semantics that does not go through the legalization:
//!
//! * `inst_vector_crosslane`, `inst_vector_dialect` and the per-op sweep:
//!   trust-ir's reference interpreter executing the SOURCE module, dialect
//!   ops included (`trust_ir::interpret`).
//! * `inst_dialect`: an opaque `verif.bfs_step` payload with no semantics in
//!   trust-ir; the test binds it to a runtime (C for AOT, Rust for the JIT)
//!   that decodes the payload descriptor, and the expected value is computed
//!   from the source op's attributes directly, never from the descriptor.
//! * `ty_dialect_v39`: a nominal value moved by `copy`; a transport reading
//!   of the source body names the parameter each return carries, and the
//!   legalized object must be byte-identical to the hand-written core twin.
//! * A runtime call whose operand is a registered nominal type (a test
//!   dialect, not a corpus row): the runtime receives the carrier, and the
//!   expected value is the cell's contents plus a descriptor length counted
//!   by hand.
//!
//! Evidence strength: native differential tests on one host. A rule whose
//! evidence the compile does not check is refused by name under a proof
//! requirement (`emit_proofs`, or a verifying JIT validation mode on its own),
//! which these tests also pin.

// Test fixture: the big `Err` is the compiler's own public error type.
#![allow(clippy::result_large_err)]
#![cfg(target_arch = "aarch64")]

#[path = "common/aarch64_native.rs"]
#[allow(dead_code)] // Only `link_run` is shared; this file compiles with its own registry.
mod native;

use std::collections::HashMap;
use std::fmt::Write as _;
use std::path::PathBuf;
use std::sync::atomic::{AtomicUsize, Ordering};

use sha2::{Digest, Sha256};
use trust_cg_codegen::compiler::{
    CompilationResult, CompileError, Compiler, CompilerConfig, JitCompilationResult,
    JitValidationMode,
};
use trust_cg_codegen::dialect_legalization::{
    DialectGrammar, DialectLegalizationRegistry, DialectLegalizationReport, DialectRegistration,
    LegalizationEvidence, LegalizationOptions, LegalizationSite, LegalizationSubject,
    OPAQUE_MASK_UNBOUND_REASON, TypeRule, legalize_module, verify_legalization,
};
use trust_cg_codegen::dialect_pipeline::DialectPipelineError;
use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::target::TargetSpec;
use trust_ir::dialect::schema::{AttributeKind, AttributeSchema, OperandType, OperationSchema};
use trust_ir::dialect::vector::{self as vector, ReduceKind};
use trust_ir::dialect::{AttrValue, DialectInst};
use trust_ir::interpret::{ArrayValue, InterpretValue, InterpretValueKind, Interpreter};
use trust_ir::{
    Block, BlockId, Constant, DialectTy, Endianness, FuncId, FuncTy, Function, Inst, InstrNode,
    Module, StructPassingPolicy, TargetInfo, Ty, ValueId,
};

const LEVELS: [OptLevel; 4] = [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3];
const DIALECT_ROWS: [&str; 4] = [
    "inst_dialect",
    "inst_vector_crosslane",
    "inst_vector_dialect",
    "ty_dialect_v39",
];

// ---------------------------------------------------------------------------
// Fixtures
// ---------------------------------------------------------------------------

fn conformance_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/fixtures/trust_ir_binary_container/conformance")
}

/// The SHA-256 `tests/fixtures/trust_ir_binary_container/SOURCE.txt` records
/// for a vendored conformance artifact.
fn recorded_sha256(file: &str) -> String {
    let source = std::fs::read_to_string(conformance_dir().join("../SOURCE.txt"))
        .expect("read the vendored corpus manifest");
    let suffix = format!("./conformance/{file}");
    source
        .lines()
        .find_map(|line| {
            let (digest, path) = line.split_once("  ")?;
            (path == suffix).then(|| digest.to_string())
        })
        .unwrap_or_else(|| panic!("SOURCE.txt records no digest for {file}"))
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().fold(String::new(), |mut out, byte| {
        let _ = write!(out, "{byte:02x}");
        out
    })
}

/// A dialect row of the pinned corpus, decoded from its canonical binary.
fn fixture(name: &str) -> Module {
    let file = format!("{name}.tmbc");
    let bytes = std::fs::read(conformance_dir().join(&file)).expect("read corpus fixture");
    assert_eq!(
        hex(&Sha256::digest(&bytes)),
        recorded_sha256(&file),
        "{file} is not the vendored pinned-corpus artifact"
    );
    let module = trust_ir::binary::deserialize_module(&bytes).expect("decode corpus fixture");
    assert_eq!(module.name, name);
    module
}

fn has_dialect_constructs(module: &Module) -> bool {
    trust_cg_codegen::dialect_legalization::module_has_dialect_constructs(module)
}

#[test]
fn the_dialect_rows_of_the_pinned_corpus_are_exactly_these_four() {
    let mut rows = Vec::new();
    for entry in std::fs::read_dir(conformance_dir()).expect("list the corpus") {
        let path = entry.unwrap().path();
        let name = path.file_stem().unwrap().to_string_lossy().to_string();
        // compat_v22_composition is a below-floor refusal control.
        if path.extension().is_none_or(|ext| ext != "tmbc") || name.starts_with("compat_") {
            continue;
        }
        let module = trust_ir::binary::deserialize_module(&std::fs::read(&path).unwrap())
            .unwrap_or_else(|error| panic!("decode {name}: {error:?}"));
        if has_dialect_constructs(&module) {
            rows.push(name);
        }
    }
    rows.sort();
    assert_eq!(
        rows, DIALECT_ROWS,
        "a corpus row that adds a dialect op or type must get a legalization test here"
    );
}

// ---------------------------------------------------------------------------
// Compilation helpers
// ---------------------------------------------------------------------------

fn host_triple() -> &'static str {
    if cfg!(target_os = "linux") {
        "aarch64-unknown-linux-gnu"
    } else {
        "aarch64-apple-darwin"
    }
}

fn with_host_target(module: &Module) -> Module {
    let mut module = module.clone();
    module.target_info = Some(TargetInfo {
        triple: host_triple().into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: Some("aapcs64".into()),
        struct_passing: StructPassingPolicy::NativeC,
    });
    module
}

fn aot(
    module: &Module,
    registry: &DialectLegalizationRegistry,
    opt_level: OptLevel,
    emit_proofs: bool,
) -> Result<CompilationResult, CompileError> {
    Compiler::new_for_target_spec(
        CompilerConfig {
            opt_level,
            emit_proofs,
            ..CompilerConfig::default()
        },
        TargetSpec::parse(host_triple()).expect("host triple"),
    )
    .with_codegen_license(permit_unlicensed())
    .with_dialect_legalization_registry(registry.clone())
    .compile(&with_host_target(module))
}

fn jit(
    module: &Module,
    registry: &DialectLegalizationRegistry,
    opt_level: OptLevel,
    emit_proofs: bool,
    symbols: &HashMap<String, *const u8>,
) -> Result<JitCompilationResult, CompileError> {
    Compiler::new(CompilerConfig {
        opt_level,
        emit_proofs,
        ..CompilerConfig::for_host_jit()
    })
    .with_codegen_license(permit_unlicensed())
    .with_dialect_legalization_registry(registry.clone())
    .compile_module_to_jit(module, symbols)
}

fn function_ptr(result: &JitCompilationResult, name: &str) -> *const u8 {
    result
        .buffer
        .get_fn_ptr_bound(name)
        .unwrap_or_else(|| panic!("JIT buffer exports {name}"))
        .as_ptr()
}

/// The report a compile must carry: the legalization of exactly the module
/// it compiled, under its proof requirement.
fn expected_report(
    module: &Module,
    registry: &DialectLegalizationRegistry,
    proof_required: bool,
) -> DialectLegalizationReport {
    let options = LegalizationOptions::new(trust_cg_codegen::Target::Aarch64, proof_required);
    let legalized = legalize_module(module, registry, options).expect("legalizes");
    let report = legalized
        .report
        .clone()
        .expect("a dialect row has a report");
    verify_legalization(module, &legalized.module, &report, registry, options)
        .expect("the report replays");
    report
}

fn dialect_error(error: CompileError) -> DialectPipelineError {
    match error {
        CompileError::DialectPipeline(error) => error,
        other => panic!("expected a dialect legalization refusal, got {other}"),
    }
}

// ---------------------------------------------------------------------------
// Memory harness: lets a C driver and the JIT call a multi-result function
// ---------------------------------------------------------------------------

const SLOT: usize = 16;
const CANARY: u8 = 0xa5;

fn v(index: u32) -> ValueId {
    ValueId::new(index)
}

fn harness_name(function: &str) -> String {
    format!("{function}__harness")
}

/// Append `<name>__harness(in: ptr, out: ptr)`: it loads parameter `i` of
/// `name` from `in + 16*i`, calls `name`, and stores result `j` at
/// `out + 16*j`. Core trust-ir only.
fn add_harness(module: &mut Module, name: &str) {
    let callee = module
        .functions
        .iter()
        .find(|function| function.name == name)
        .unwrap_or_else(|| panic!("no function {name}"));
    let callee_id = callee.id;
    let signature = module.func_type(callee.ty).expect("signature").clone();
    let id = FuncId::new(
        module
            .functions
            .iter()
            .map(|function| function.id.index())
            .max()
            .unwrap()
            + 1,
    );
    let ty = module
        .add_func_type(FuncTy {
            params: vec![Ty::Ptr, Ty::Ptr],
            returns: vec![],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut function = Function::new(id, harness_name(name), ty, BlockId::new(0));
    let mut block = Block::new(BlockId::new(0));
    block.params = vec![(v(0), Ty::Ptr), (v(1), Ty::Ptr)];
    let mut next = 2u32;
    let mut fresh = || {
        next += 1;
        v(next - 1)
    };
    let mut body = Vec::new();
    let mut slot_address = |body: &mut Vec<InstrNode>, base: ValueId, slot: usize| {
        let offset = fresh();
        body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: Constant::Int((slot * SLOT) as i128),
            })
            .with_result(offset),
        );
        let address = fresh();
        body.push(
            InstrNode::new(Inst::GEP {
                pointee_ty: Ty::U8,
                base,
                indices: vec![offset],
                inbounds: true,
            })
            .with_result(address),
        );
        (address, fresh())
    };
    let mut args = Vec::new();
    for (slot, ty) in signature.params.iter().enumerate() {
        let (address, value) = slot_address(&mut body, v(0), slot);
        body.push(
            InstrNode::new(Inst::Load {
                ty: ty.clone(),
                ptr: address,
                volatile: false,
                align: None,
            })
            .with_result(value),
        );
        args.push(value);
    }
    let mut results = Vec::new();
    let mut stores = Vec::new();
    for (slot, ty) in signature.returns.iter().enumerate() {
        let (address, value) = slot_address(&mut stores, v(1), slot);
        results.push(value);
        stores.push(InstrNode::new(Inst::Store {
            ty: ty.clone(),
            ptr: address,
            value,
            volatile: false,
            align: None,
        }));
    }
    body.push(
        InstrNode::new(Inst::Call {
            callee: callee_id,
            args,
        })
        .with_results(results.iter().copied()),
    );
    body.extend(stores);
    body.push(InstrNode::new(Inst::Return { values: vec![] }));
    block.body = body;
    function.blocks.push(block);
    module.functions.push(function);
}

fn lane_bytes(ty: &Ty) -> usize {
    match ty {
        Ty::I8 | Ty::U8 => 1,
        Ty::I16 | Ty::U16 => 2,
        Ty::I32 | Ty::U32 | Ty::F32 => 4,
        Ty::I64 | Ty::U64 | Ty::F64 => 8,
        other => panic!("no harness layout for {other:?}"),
    }
}

fn ty_bytes(ty: &Ty) -> usize {
    match ty {
        Ty::Vector(elem, lanes) => lane_bytes(elem) * *lanes as usize,
        scalar => lane_bytes(scalar),
    }
}

fn scalar_value(ty: &Ty, bytes: &[u8]) -> InterpretValue {
    let width = lane_bytes(ty);
    let mut raw = [0u8; 8];
    raw[..width].copy_from_slice(&bytes[..width]);
    let bits = u64::from_le_bytes(raw);
    match ty {
        Ty::F32 | Ty::F64 => InterpretValue {
            ty: ty.clone(),
            kind: InterpretValueKind::FloatBits(bits),
        },
        _ => {
            let shift = 64 - 8 * width as u32;
            let signed = ((bits << shift) as i64) >> shift;
            InterpretValue::int(ty.clone(), i128::from(signed)).expect("integer lane")
        }
    }
}

fn value_from_bytes(ty: &Ty, bytes: &[u8]) -> InterpretValue {
    match ty {
        Ty::Vector(elem, lanes) => {
            let width = lane_bytes(elem);
            let lanes = (0..*lanes as usize)
                .map(|lane| scalar_value(elem, &bytes[lane * width..]))
                .collect();
            InterpretValue {
                ty: ty.clone(),
                kind: InterpretValueKind::Vector(ArrayValue::from_vec(lanes)),
            }
        }
        scalar => scalar_value(scalar, bytes),
    }
}

fn value_bytes(ty: &Ty, value: &InterpretValue) -> Vec<u8> {
    match (ty, &value.kind) {
        (Ty::Vector(elem, _), InterpretValueKind::Vector(lanes)) => lanes
            .to_vec()
            .iter()
            .flat_map(|lane| value_bytes(elem, lane))
            .collect(),
        (_, InterpretValueKind::Int(int)) => {
            int.as_unsigned().to_le_bytes()[..lane_bytes(ty)].to_vec()
        }
        (_, InterpretValueKind::FloatBits(bits)) => bits.to_le_bytes()[..lane_bytes(ty)].to_vec(),
        (ty, other) => panic!("no byte image for {ty:?} = {other:?}"),
    }
}

struct SplitMix(u64);

impl SplitMix {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        z ^ (z >> 31)
    }
}

/// Finite floats only (fma of finite inputs may still overflow to infinity;
/// no NaN reaches a comparison).
fn lane_input(elem: &Ty, rng: &mut SplitMix, case: usize, lane: usize) -> Vec<u8> {
    let bits = rng.next();
    match elem {
        Ty::F32 => {
            let specials = [
                0.0f32,
                -0.0,
                1.0,
                -1.5,
                1.0e-40,
                f32::MAX,
                f32::MIN_POSITIVE,
                3.25,
            ];
            let value = if (case + lane).is_multiple_of(3) {
                specials[(case * 7 + lane) % specials.len()]
            } else {
                let raw = bits as u32;
                let exponent = ((raw >> 23) & 0xff) % 0xfe;
                f32::from_bits((raw & 0x807f_ffff) | (exponent << 23))
            };
            value.to_bits().to_le_bytes().to_vec()
        }
        Ty::F64 => {
            let specials = [
                0.0f64,
                -0.0,
                1.0,
                -2.75,
                5.0e-324,
                f64::MAX,
                f64::MIN_POSITIVE,
                0.1,
            ];
            let value = if (case + lane).is_multiple_of(3) {
                specials[(case * 5 + lane) % specials.len()]
            } else {
                let exponent = ((bits >> 52) & 0x7ff) % 0x7fe;
                f64::from_bits((bits & 0x800f_ffff_ffff_ffff) | (exponent << 52))
            };
            value.to_bits().to_le_bytes().to_vec()
        }
        _ => bits.to_le_bytes()[..lane_bytes(elem)].to_vec(),
    }
}

fn input_bytes(ty: &Ty, rng: &mut SplitMix, case: usize) -> Vec<u8> {
    match ty {
        Ty::Vector(elem, lanes) => (0..*lanes as usize)
            .flat_map(|lane| lane_input(elem, rng, case, lane))
            .collect(),
        scalar => lane_input(scalar, rng, case, 0),
    }
}

/// One harness case: the input slots and the expected output slots (each
/// result's bytes, the rest of its slot left as the canary).
struct Case {
    input: Vec<u8>,
    expected: Vec<u8>,
}

/// Cases for `name` whose expected outputs come from trust-ir's interpreter
/// executing the source module (dialect ops included).
fn interpreted_cases(source: &Module, name: &str, count: usize, seed: u64) -> Vec<Case> {
    let function = source
        .functions
        .iter()
        .find(|function| function.name == name)
        .unwrap_or_else(|| panic!("no function {name}"));
    let signature = source.func_type(function.ty).expect("signature").clone();
    let mut rng = SplitMix(seed);
    (0..count)
        .map(|case| {
            let mut input = vec![0u8; SLOT * signature.params.len().max(1)];
            let mut args = Vec::new();
            for (slot, ty) in signature.params.iter().enumerate() {
                let bytes = input_bytes(ty, &mut rng, case);
                input[slot * SLOT..slot * SLOT + bytes.len()].copy_from_slice(&bytes);
                args.push(value_from_bytes(ty, &bytes));
            }
            let outcome = Interpreter::with_module(source)
                .execute_function(function, args)
                .unwrap_or_else(|error| panic!("interpret {name}: {error:?}"));
            assert_eq!(outcome.host_calls, 0, "an in-format reference run");
            let mut expected = vec![CANARY; SLOT * signature.returns.len().max(1)];
            for (slot, (ty, value)) in signature.returns.iter().zip(&outcome.returns).enumerate() {
                let bytes = value_bytes(ty, value);
                assert_eq!(bytes.len(), ty_bytes(ty));
                expected[slot * SLOT..slot * SLOT + bytes.len()].copy_from_slice(&bytes);
            }
            Case { input, expected }
        })
        .collect()
}

fn c_bytes(bytes: &[u8]) -> String {
    bytes
        .iter()
        .map(|byte| format!("0x{byte:02x}"))
        .collect::<Vec<_>>()
        .join(",")
}

/// A C driver that runs every case through `<function>__harness` and exits
/// nonzero on the first byte that differs.
fn harness_driver(functions: &[(&str, &[Case])]) -> String {
    let mut c = String::from("#include <stdio.h>\n#include <string.h>\n");
    let mut calls = String::new();
    for (index, (name, cases)) in functions.iter().enumerate() {
        let harness = harness_name(name);
        let (in_len, out_len) = (cases[0].input.len(), cases[0].expected.len());
        let _ = writeln!(
            c,
            "extern void {harness}(const unsigned char *, unsigned char *);"
        );
        let _ = writeln!(
            c,
            "static const unsigned char IN{index}[{}][{in_len}] = {{{}}};",
            cases.len(),
            cases
                .iter()
                .map(|case| format!("{{{}}}", c_bytes(&case.input)))
                .collect::<Vec<_>>()
                .join(",")
        );
        let _ = writeln!(
            c,
            "static const unsigned char WANT{index}[{}][{out_len}] = {{{}}};",
            cases.len(),
            cases
                .iter()
                .map(|case| format!("{{{}}}", c_bytes(&case.expected)))
                .collect::<Vec<_>>()
                .join(",")
        );
        let _ = writeln!(
            calls,
            "  for (int c = 0; c < {count}; c++) {{\n\
             \x20   static unsigned char in[{in_len}] __attribute__((aligned(16)));\n\
             \x20   static unsigned char out[{out_len}] __attribute__((aligned(16)));\n\
             \x20   memcpy(in, IN{index}[c], {in_len});\n\
             \x20   memset(out, 0x{CANARY:02x}, {out_len});\n\
             \x20   {harness}(in, out);\n\
             \x20   for (int i = 0; i < {out_len}; i++) if (out[i] != WANT{index}[c][i]) {{\n\
             \x20     printf(\"{name} case %d byte %d: got %02x want %02x\\n\", c, i, out[i], WANT{index}[c][i]);\n\
             \x20     return 1;\n\
             \x20   }}\n\
             \x20   checks++;\n\
             \x20 }}",
            count = cases.len(),
        );
    }
    let total: usize = functions.iter().map(|(_, cases)| cases.len()).sum();
    let _ = write!(
        c,
        "int main(void) {{\n  int checks = 0;\n{calls}  printf(\"checks=%d\\n\", checks);\n  return checks == {total} ? 0 : 2;\n}}\n"
    );
    c
}

/// Run every case of every function through the JIT buffer's harnesses.
fn run_jit_cases(result: &JitCompilationResult, functions: &[(&str, &[Case])], label: &str) {
    for (name, cases) in functions {
        let entry = function_ptr(result, &harness_name(name));
        // SAFETY: the harness was compiled from `add_harness` with the
        // `(ptr, ptr) -> ()` signature; the buffers outlive the call.
        let harness: extern "C" fn(*const u8, *mut u8) = unsafe { std::mem::transmute(entry) };
        for (index, case) in cases.iter().enumerate() {
            let mut input = vec![0u128; case.input.len() / SLOT];
            let mut output = vec![0u128; case.expected.len() / SLOT];
            // SAFETY: u128 storage is 16-byte aligned and exactly as long.
            let input_bytes = unsafe {
                std::slice::from_raw_parts_mut(input.as_mut_ptr().cast::<u8>(), case.input.len())
            };
            input_bytes.copy_from_slice(&case.input);
            let output_bytes = unsafe {
                std::slice::from_raw_parts_mut(
                    output.as_mut_ptr().cast::<u8>(),
                    case.expected.len(),
                )
            };
            output_bytes.fill(CANARY);
            harness(input_bytes.as_ptr(), output_bytes.as_mut_ptr());
            assert_eq!(
                output_bytes,
                case.expected.as_slice(),
                "{label}: JIT {name} case {index} differs from the reference"
            );
        }
    }
}

/// Compile `module` (with harnesses for `functions`) at every level, AOT and
/// JIT, and compare every case with the reference. Returns the AOT reports.
fn run_native(
    label: &str,
    module: &Module,
    registry: &DialectLegalizationRegistry,
    functions: &[(&str, &[Case])],
) {
    let mut harnessed = module.clone();
    for (name, _) in functions {
        add_harness(&mut harnessed, name);
    }
    let driver = harness_driver(functions);
    let aot_report = expected_report(&with_host_target(&harnessed), registry, false);
    let jit_report = expected_report(&harnessed, registry, false);
    for level in LEVELS {
        let object = aot(&harnessed, registry, level, false)
            .unwrap_or_else(|error| panic!("{label} AOT {level:?}: {error}"));
        assert_eq!(
            object.dialect_legalization.as_ref(),
            Some(&aot_report),
            "{label} AOT report"
        );
        native::link_run(&format!("{label}-{level:?}"), &object.object_code, &driver)
            .expect("native AArch64 host");
        let buffer = jit(&harnessed, registry, level, false, &HashMap::new())
            .unwrap_or_else(|error| panic!("{label} JIT {level:?}: {error}"));
        assert_eq!(
            buffer.dialect_legalization.as_ref(),
            Some(&jit_report),
            "{label} JIT report"
        );
        run_jit_cases(&buffer, functions, &format!("{label} {level:?}"));
    }
}

fn rules(report: &DialectLegalizationReport) -> Vec<&str> {
    report
        .receipts
        .iter()
        .map(|receipt| receipt.rule.as_str())
        .collect()
}

// ---------------------------------------------------------------------------
// inst_vector_crosslane: vector.reduce, vector.shuffle, vector.fma
// ---------------------------------------------------------------------------

#[test]
fn inst_vector_crosslane_executes_natively_against_the_trust_ir_interpreter() {
    let source = fixture("inst_vector_crosslane");
    let registry = DialectLegalizationRegistry::trust_cg_default();
    let report = expected_report(&source, &registry, false);
    assert_eq!(
        rules(&report),
        vec![
            "vector.reduce/trust-ir-lane-fold",
            "vector.reduce/trust-ir-lane-fold",
            "vector.shuffle/trust-ir-lane-gather",
            "vector.shuffle/trust-ir-lane-gather",
            "vector.fma/aarch64-per-lane-fmadd",
            "vector.fma/aarch64-per-lane-fmadd",
        ]
    );
    for receipt in &report.receipts {
        assert_eq!(
            (receipt.dialect.as_str(), receipt.dialect_version),
            ("vector", 1)
        );
        assert_ne!(
            receipt.input_digest, receipt.output_digest,
            "every site is rewritten"
        );
    }
    let cases = interpreted_cases(&source, "portable_vector_crosslane", 24, 0x5eed_c805);
    run_native(
        "inst_vector_crosslane",
        &source,
        &registry,
        &[("portable_vector_crosslane", &cases)],
    );

    // Neither a cited upstream theorem nor tests are checked in the compile.
    for error in [
        aot(&source, &registry, OptLevel::O2, true).expect_err("proof-required AOT"),
        jit(&source, &registry, OptLevel::O2, true, &HashMap::new())
            .expect_err("proof-required JIT"),
    ] {
        let error = dialect_error(error);
        assert!(
            matches!(&error, DialectPipelineError::ProofPolicy { rule, evidence, .. }
                if rule == "vector.reduce/trust-ir-lane-fold"
                    && evidence.starts_with("cited-upstream-theorem")),
            "{error}"
        );
    }
}

// ---------------------------------------------------------------------------
// inst_vector_dialect: pack/extract/insert lanes and compare-mask bits
// ---------------------------------------------------------------------------

/// `inst_vector_dialect` without the two `vector.mask_to_bits` sites whose
/// masks are function parameters: those parameters and results are removed,
/// every other instruction is kept as the corpus wrote it.
fn without_parameter_masks(source: &Module) -> Module {
    let mut module = source.clone();
    let function = &mut module.functions[0];
    let entry = &mut function.blocks[0];
    let parameter_values: Vec<ValueId> = entry.params.iter().map(|(value, _)| *value).collect();
    let mut removed_params = Vec::new();
    let mut removed_results = Vec::new();
    entry.body.retain(|node| match &node.inst {
        Inst::DialectOp(op)
            if vector::is_mask_to_bits_op(op) && parameter_values.contains(&op.operands[0]) =>
        {
            removed_params.push(op.operands[0]);
            removed_results.extend(node.results.iter().copied());
            false
        }
        _ => true,
    });
    assert_eq!(
        removed_params.len(),
        2,
        "the corpus row has two parameter masks"
    );
    let kept_params: Vec<usize> = (0..entry.params.len())
        .filter(|index| !removed_params.contains(&entry.params[*index].0))
        .collect();
    let mut kept_returns = Vec::new();
    for node in &mut entry.body {
        if let Inst::Return { values } = &mut node.inst {
            kept_returns = (0..values.len())
                .filter(|index| !removed_results.contains(&values[*index]))
                .collect();
            values.retain(|value| !removed_results.contains(value));
        }
    }
    entry.params = kept_params
        .iter()
        .map(|index| entry.params[*index].clone())
        .collect();
    let signature = module.func_types[function.ty.index() as usize].clone();
    assert!(
        signature.abi.is_none(),
        "fixture carrier edits cannot erase recorded ABI claims"
    );
    module.func_types[function.ty.index() as usize] = FuncTy {
        params: kept_params
            .iter()
            .map(|index| signature.params[*index].clone())
            .collect(),
        returns: kept_returns
            .iter()
            .map(|index| signature.returns[*index].clone())
            .collect(),
        abi: None,
        is_vararg: signature.is_vararg,
    };
    function.source_provenance = None;
    module
}

#[test]
fn inst_vector_dialect_compare_masks_execute_and_parameter_masks_are_refused_by_name() {
    let source = fixture("inst_vector_dialect");
    let registry = DialectLegalizationRegistry::trust_cg_default();

    // A `<8 x bool>` / `<16 x bool>` parameter has no defined lane image in
    // this backend, so `mask_to_bits` of it is refused at legalization.
    for error in [
        aot(&source, &registry, OptLevel::O0, false).expect_err("AOT"),
        jit(&source, &registry, OptLevel::O0, false, &HashMap::new()).expect_err("JIT"),
    ] {
        let error = dialect_error(error);
        assert!(
            matches!(&error, DialectPipelineError::Unbound { dialect, op, function, reason, .. }
                if dialect == "vector" && op == "mask_to_bits"
                    && function == "portable_vector_dialect"
                    && reason == OPAQUE_MASK_UNBOUND_REASON),
            "{error}"
        );
    }

    let derived = without_parameter_masks(&source);
    let report = expected_report(&derived, &registry, true);
    assert_eq!(
        rules(&report),
        vec![
            "vector.pack_lanes/adapter-native",
            "vector.extract_lane/adapter-native",
            "vector.insert_lane/adapter-native",
            "vector.pack_lanes/adapter-native",
            "vector.extract_lane/adapter-native",
            "vector.insert_lane/adapter-native",
            "vector.mask_to_bits/adapter-native-compare-mask",
            "vector.mask_to_bits/adapter-native-compare-mask",
        ]
    );
    assert!(
        report
            .receipts
            .iter()
            .all(|receipt| receipt.evidence == LegalizationEvidence::AdapterInstructionLowering),
        "every kept op stays under the adapter's instruction evidence"
    );
    let cases = interpreted_cases(&derived, "portable_vector_dialect", 24, 0x0d1a_1ec7);
    run_native(
        "inst_vector_dialect",
        &derived,
        &registry,
        &[("portable_vector_dialect", &cases)],
    );
}

// ---------------------------------------------------------------------------
// Per-op sweep: every vector op the rules rewrite, every admitted shape
// ---------------------------------------------------------------------------

fn sweep_module() -> (Module, Vec<String>) {
    let mut module = Module::new("vector_dialect_sweep");
    let mut names = Vec::new();
    let mut add = |module: &mut Module, name: String, params: Vec<Ty>, ret: Ty, op: DialectInst| {
        let ty = module
            .add_func_type(FuncTy {
                params: params.clone(),
                returns: vec![ret],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let id = FuncId::new(module.functions.len() as u32);
        let mut function = Function::new(id, name.clone(), ty, BlockId::new(0));
        let mut block = Block::new(BlockId::new(0));
        block.params = params
            .into_iter()
            .enumerate()
            .map(|(index, ty)| (v(index as u32), ty))
            .collect();
        let result = v(block.params.len() as u32);
        block.body = vec![
            InstrNode::new(Inst::DialectOp(Box::new(op))).with_result(result),
            InstrNode::new(Inst::Return {
                values: vec![result],
            }),
        ];
        function.blocks.push(block);
        module.functions.push(function);
        names.push(name);
    };
    for (elem, lanes) in [(Ty::I8, 16), (Ty::I16, 8), (Ty::I32, 4), (Ty::I64, 2)] {
        let vty = Ty::Vector(Box::new(elem.clone()), lanes);
        let shape = format!("v{lanes}{elem}");
        for kind in [ReduceKind::Add, ReduceKind::Or] {
            add(
                &mut module,
                format!("reduce_{}_{shape}", kind.as_str()),
                vec![vty.clone()],
                elem.clone(),
                vector::reduce(vty.clone(), v(0), kind),
            );
        }
        let permutation: Vec<u8> = (0..lanes)
            .map(|lane| ((lane * 5 + 3) % lanes) as u8)
            .collect();
        add(
            &mut module,
            format!("shuffle_perm_{shape}"),
            vec![vty.clone()],
            vty.clone(),
            vector::shuffle(vty.clone(), v(0), permutation),
        );
        add(
            &mut module,
            format!("shuffle_splat_{shape}"),
            vec![vty.clone()],
            vty.clone(),
            vector::shuffle(vty.clone(), v(0), vec![(lanes - 1) as u8; lanes as usize]),
        );
    }
    for (elem, lanes) in [(Ty::F32, 4), (Ty::F64, 2)] {
        let vty = Ty::Vector(Box::new(elem.clone()), lanes);
        add(
            &mut module,
            format!("fma_v{lanes}{elem}"),
            vec![vty.clone(); 3],
            vty.clone(),
            vector::fma(vty, v(0), v(1), v(2)),
        );
    }
    (module, names)
}

#[test]
fn v64_lane_expansions_are_refused_by_name_before_the_adapter() {
    let vty = Ty::Vector(Box::new(Ty::I8), 8);
    let registry = DialectLegalizationRegistry::trust_cg_default();
    for (op, ret) in [
        (vector::reduce(vty.clone(), v(0), ReduceKind::Or), Ty::I8),
        (
            vector::shuffle(vty.clone(), v(0), vec![7u8, 6, 5, 4, 3, 2, 1, 0]),
            vty.clone(),
        ),
    ] {
        let name = op.op.clone();
        let mut module = Module::new("v64");
        let ty = module
            .add_func_type(FuncTy {
                params: vec![vty.clone()],
                returns: vec![ret],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut function = Function::new(FuncId::new(0), "f", ty, BlockId::new(0));
        let mut block = Block::new(BlockId::new(0));
        block.params = vec![(v(0), vty.clone())];
        block.body = vec![
            InstrNode::new(Inst::DialectOp(Box::new(op))).with_result(v(1)),
            InstrNode::new(Inst::Return { values: vec![v(1)] }),
        ];
        function.blocks.push(block);
        module.functions.push(function);
        for error in [
            aot(&module, &registry, OptLevel::O0, false).expect_err("AOT"),
            jit(&module, &registry, OptLevel::O0, false, &HashMap::new()).expect_err("JIT"),
        ] {
            let error = dialect_error(error);
            assert!(
                matches!(&error, DialectPipelineError::Unbound { op, reason, .. }
                    if *op == name
                        && reason
                            == trust_cg_codegen::dialect_legalization::V64_LANE_EXPANSION_UNBOUND_REASON),
                "{error}"
            );
        }
    }
}

#[test]
fn every_rewritten_vector_op_and_shape_executes_natively_against_the_interpreter() {
    let (source, names) = sweep_module();
    let registry = DialectLegalizationRegistry::trust_cg_default();
    let report = expected_report(&source, &registry, false);
    assert_eq!(report.receipts.len(), names.len());
    assert_eq!(report.rewritten_op_sites(), names.len());
    let cases: Vec<(String, Vec<Case>)> = names
        .iter()
        .enumerate()
        .map(|(index, name)| {
            (
                name.clone(),
                interpreted_cases(&source, name, 12, 0xfeed + index as u64),
            )
        })
        .collect();
    let functions: Vec<(&str, &[Case])> = cases
        .iter()
        .map(|(name, cases)| (name.as_str(), cases.as_slice()))
        .collect();
    for (name, cases) in &cases {
        if name.starts_with("fma_") {
            assert_fma_cases_discriminate(name, cases);
        }
    }
    run_native("vector_dialect_sweep", &source, &registry, &functions);
}

/// The fma cases can tell a fused multiply-add from the twice-rounded
/// `a*b` then `+c`, and `a*b + c` from `a*c + b`: a native match is then
/// evidence of one rounding and of the operand order, not just of agreement
/// on inputs that cannot distinguish them.
fn assert_fma_cases_discriminate(name: &str, cases: &[Case]) {
    let (mut unfused_differs, mut order_differs) = (false, false);
    for case in cases {
        let slot = |index: usize| &case.input[index * SLOT..(index + 1) * SLOT];
        if name.ends_with("f32") {
            for lane in 0..4 {
                let read = |index: usize| {
                    f32::from_le_bytes(slot(index)[lane * 4..lane * 4 + 4].try_into().unwrap())
                };
                let (a, b, c) = (read(0), read(1), read(2));
                let fused = a.mul_add(b, c);
                unfused_differs |= fused.to_bits() != (a * b + c).to_bits();
                order_differs |= fused.to_bits() != a.mul_add(c, b).to_bits();
            }
        } else {
            for lane in 0..2 {
                let read = |index: usize| {
                    f64::from_le_bytes(slot(index)[lane * 8..lane * 8 + 8].try_into().unwrap())
                };
                let (a, b, c) = (read(0), read(1), read(2));
                let fused = a.mul_add(b, c);
                unfused_differs |= fused.to_bits() != (a * b + c).to_bits();
                order_differs |= fused.to_bits() != a.mul_add(c, b).to_bits();
            }
        }
    }
    assert!(
        unfused_differs,
        "{name}: no case distinguishes fused from unfused"
    );
    assert!(
        order_differs,
        "{name}: no case distinguishes the operand order"
    );
}

// ---------------------------------------------------------------------------
// inst_dialect: an opaque verif.bfs_step payload bound to a runtime
// ---------------------------------------------------------------------------

const RUNTIME_SYMBOL: &str = "tcg_corpus_inst_dialect_bfs_step";
const RUNTIME_SENTINEL: i32 = 0x7fff_dead;
const FNV_OFFSET: u32 = 0x811c_9dc5;
const FNV_PRIME: u32 = 0x0100_0193;

fn mix(hash: &mut u32, bytes: &[u8]) {
    for byte in bytes {
        *hash = (*hash ^ u32::from(*byte)).wrapping_mul(FNV_PRIME);
    }
}

/// The test runtime's meaning of the payload, read from the SOURCE op: an
/// FNV-1a digest over every attribute's name, kind tag and typed value, in
/// payload order, xor the operand.
fn reference_result(op: &DialectInst, x: i32) -> i32 {
    let mut hash = FNV_OFFSET;
    for attr in &op.attrs {
        mix(&mut hash, attr.name.as_bytes());
        let (tag, value): (u8, Vec<u8>) = match &attr.value {
            AttrValue::I64(value) => (0, value.to_le_bytes().to_vec()),
            AttrValue::U64(value) => (1, value.to_le_bytes().to_vec()),
            AttrValue::F64(value) => (2, value.to_bits().to_le_bytes().to_vec()),
            AttrValue::Bool(value) => (3, vec![u8::from(*value)]),
            AttrValue::Str(value) => (4, value.as_bytes().to_vec()),
            AttrValue::Bytes(value) => (5, value.clone()),
            AttrValue::Ty(ty) => (6, ty.to_string().into_bytes()),
        };
        mix(&mut hash, &[tag]);
        mix(&mut hash, &value);
    }
    (hash ^ x as u32) as i32
}

/// The Rust runtime the JIT binds: decodes the payload descriptor (an
/// implementation independent of the encoder) and applies the same meaning.
fn decode_descriptor(bytes: &[u8]) -> Option<u32> {
    struct Cursor<'a>(&'a [u8]);
    impl<'a> Cursor<'a> {
        fn take(&mut self, n: usize) -> Option<&'a [u8]> {
            let (head, tail) = (self.0.get(..n)?, self.0.get(n..)?);
            self.0 = tail;
            Some(head)
        }
        fn u32(&mut self) -> Option<u32> {
            Some(u32::from_le_bytes(self.take(4)?.try_into().ok()?))
        }
        fn string(&mut self) -> Option<&'a [u8]> {
            let len = self.u32()? as usize;
            self.take(len)
        }
    }
    let mut cursor = Cursor(bytes);
    if cursor.take(4)? != b"TCGD" || cursor.u32()? != 1 {
        return None;
    }
    if cursor.string()? != b"verif" || cursor.string()? != b"bfs_step" || cursor.u32()? != 1 {
        return None;
    }
    let count = cursor.u32()?;
    let mut hash = FNV_OFFSET;
    for _ in 0..count {
        mix(&mut hash, cursor.string()?);
        let tag = cursor.take(1)?[0];
        mix(&mut hash, &[tag]);
        let value = match tag {
            0..=2 => cursor.take(8)?,
            3 => {
                let value = cursor.take(1)?;
                (value[0] <= 1).then_some(value)?
            }
            4..=6 => cursor.string()?,
            _ => return None,
        };
        mix(&mut hash, value);
    }
    cursor.0.is_empty().then_some(hash)
}

static RUNTIME_CALLS: AtomicUsize = AtomicUsize::new(0);

extern "C" fn rust_runtime(descriptor: *const u8, len: u64, x: i32) -> i32 {
    RUNTIME_CALLS.fetch_add(1, Ordering::SeqCst);
    // SAFETY: the legalized call passes the address and exact length of the
    // module's read-only descriptor object.
    let bytes = unsafe { std::slice::from_raw_parts(descriptor, len as usize) };
    match decode_descriptor(bytes) {
        Some(hash) => (hash ^ x as u32) as i32,
        None => RUNTIME_SENTINEL,
    }
}

const C_RUNTIME: &str = r#"
#include <stdint.h>
#include <string.h>
#define SENTINEL 0x7fffdead
typedef struct { const uint8_t *p; uint64_t n; int bad; } cursor;
static uint32_t hash;
static void mix(const uint8_t *p, uint64_t n) {
  for (uint64_t i = 0; i < n; i++) hash = (hash ^ p[i]) * 16777619u;
}
static const uint8_t *take(cursor *c, uint64_t k) {
  if (c->bad || c->n < k) { c->bad = 1; return 0; }
  const uint8_t *q = c->p; c->p += k; c->n -= k; return q;
}
static uint32_t rd32(cursor *c) {
  const uint8_t *q = take(c, 4);
  return q ? (uint32_t)q[0] | ((uint32_t)q[1] << 8) | ((uint32_t)q[2] << 16) | ((uint32_t)q[3] << 24) : 0;
}
static const uint8_t *str(cursor *c, uint32_t *len) { *len = rd32(c); return take(c, *len); }
static int str_is(cursor *c, const char *want) {
  uint32_t len; const uint8_t *s = str(c, &len);
  return s && len == strlen(want) && memcmp(s, want, len) == 0;
}
int32_t tcg_corpus_inst_dialect_bfs_step(const uint8_t *d, uint64_t n, int32_t x) {
  cursor c = { d, n, 0 };
  const uint8_t *magic = take(&c, 4);
  if (!magic || memcmp(magic, "TCGD", 4) != 0 || rd32(&c) != 1) return SENTINEL;
  if (!str_is(&c, "verif") || !str_is(&c, "bfs_step") || rd32(&c) != 1) return SENTINEL;
  uint32_t count = rd32(&c);
  hash = 2166136261u;
  for (uint32_t i = 0; i < count && !c.bad; i++) {
    uint32_t len; const uint8_t *name = str(&c, &len);
    if (!name) break;
    mix(name, len);
    const uint8_t *tag = take(&c, 1);
    if (!tag) break;
    mix(tag, 1);
    const uint8_t *value = 0;
    switch (*tag) {
      case 0: case 1: case 2: len = 8; value = take(&c, 8); break;
      case 3: len = 1; value = take(&c, 1); if (value && *value > 1) c.bad = 1; break;
      case 4: case 5: case 6: value = str(&c, &len); break;
      default: c.bad = 1;
    }
    if (value) mix(value, len);
  }
  if (c.bad || c.n != 0) return SENTINEL;
  return (int32_t)(hash ^ (uint32_t)x);
}
"#;

/// The default registry with `verif` replaced by a binding for exactly the
/// corpus row's payload grammar: `bfs_step(i32) -> i32` carrying one
/// attribute of every kind, lowered to a call of the test runtime.
fn inst_dialect_registry() -> DialectLegalizationRegistry {
    let mut registrations: Vec<DialectRegistration> =
        DialectLegalizationRegistry::default_registrations()
            .into_iter()
            .filter(|registration| registration.namespace != "verif")
            .collect();
    let attributes = [
        ("i64_attr", AttributeKind::I64),
        ("u64_attr", AttributeKind::U64),
        ("f64_attr", AttributeKind::F64),
        ("bool_attr", AttributeKind::Bool),
        ("str_attr", AttributeKind::Str),
        ("bytes_attr", AttributeKind::Bytes),
        ("ty_attr", AttributeKind::Ty),
    ];
    registrations.push(
        DialectRegistration {
            namespace: "verif".to_string(),
            version: 1,
            owner: "trust-cg corpus test: the inst_dialect row's opaque payload, given meaning \
                    only by the bound test runtime"
                .to_string(),
            grammar: DialectGrammar::Exact(vec![OperationSchema {
                name: "bfs_step".to_string(),
                operands: vec![OperandType::Exact(Ty::I32)],
                results: vec![Ty::I32],
                attributes: attributes
                    .iter()
                    .map(|(name, kind)| AttributeSchema {
                        name: name.to_string(),
                        kind: *kind,
                    })
                    .collect(),
            }]),
            ops: Vec::new(),
            types: Vec::new(),
        }
        .bind_runtime_call(
            "bfs_step",
            RUNTIME_SYMBOL,
            "the dialect_legalization_corpus.rs test runtime (C for AOT, Rust for the JIT)",
        ),
    );
    DialectLegalizationRegistry::new(registrations).expect("well-formed")
}

fn the_op(module: &Module) -> DialectInst {
    module
        .instructions()
        .find_map(|node| match &node.inst {
            Inst::DialectOp(op) => Some(op.as_ref().clone()),
            _ => None,
        })
        .expect("one dialect op")
}

#[test]
fn inst_dialect_runs_through_a_bound_runtime_and_is_refused_unbound_or_under_proof() {
    let source = fixture("inst_dialect");
    let op = the_op(&source);
    assert_eq!(op.qualified_name(), "verif.bfs_step");
    assert_eq!(
        op.attrs.len(),
        7,
        "the row carries one attribute of every kind"
    );

    // The default registry holds trust-ir's verif v1 contract, which this
    // payload does not satisfy: refused by name.
    let default = DialectLegalizationRegistry::trust_cg_default();
    let error = dialect_error(aot(&source, &default, OptLevel::O0, false).expect_err("default"));
    assert!(
        matches!(&error, DialectPipelineError::Grammar { dialect, op, function, .. }
            if dialect == "verif" && op == "bfs_step" && function == "dialect_roundtrip"),
        "{error}"
    );

    let registry = inst_dialect_registry();
    let report = expected_report(&source, &registry, false);
    let [receipt] = report.receipts.as_slice() else {
        panic!("one receipt");
    };
    assert_eq!(
        (
            receipt.dialect.as_str(),
            receipt.dialect_version,
            receipt.rule.as_str()
        ),
        (
            "verif",
            1,
            "verif.bfs_step/runtime-call:tcg_corpus_inst_dialect_bfs_step"
        )
    );
    assert_eq!(
        receipt.subject,
        LegalizationSubject::Op {
            op: "bfs_step".into(),
            payload_version: 1,
        }
    );
    assert!(
        matches!(&receipt.site, LegalizationSite::Instruction { function, block: 0, index: 0 }
        if function == "dialect_roundtrip")
    );

    let inputs = [
        0,
        1,
        -1,
        7,
        i32::MIN,
        i32::MAX,
        0x1234_5678,
        -0x0765_4321,
        1 << 20,
        -42,
    ];
    let expected: Vec<i32> = inputs.iter().map(|x| reference_result(&op, *x)).collect();
    assert!(expected.iter().all(|value| *value != RUNTIME_SENTINEL));

    let mut driver = String::from(C_RUNTIME);
    let _ = write!(
        driver,
        "#include <stdio.h>\nextern int32_t dialect_roundtrip(int32_t);\n\
         static const int32_t XS[] = {{{}}};\nstatic const int32_t WANT[] = {{{}}};\n\
         int main(void) {{\n  int checks = 0;\n  for (int i = 0; i < {count}; i++) {{\n\
         \x20   int32_t got = dialect_roundtrip(XS[i]);\n\
         \x20   if (got != WANT[i]) {{ printf(\"case %d: got %d want %d\\n\", i, got, WANT[i]); return 1; }}\n\
         \x20   checks++;\n  }}\n  printf(\"checks=%d\\n\", checks);\n  return checks == {count} ? 0 : 2;\n}}\n",
        inputs
            .iter()
            .map(|x| format!("(int32_t){x}"))
            .collect::<Vec<_>>()
            .join(","),
        expected
            .iter()
            .map(|x| format!("(int32_t){x}"))
            .collect::<Vec<_>>()
            .join(","),
        count = inputs.len(),
    );
    let aot_report = expected_report(&with_host_target(&source), &registry, false);
    let mut symbols: HashMap<String, *const u8> = HashMap::new();
    symbols.insert(RUNTIME_SYMBOL.to_string(), rust_runtime as *const u8);
    for level in LEVELS {
        let object = aot(&source, &registry, level, false)
            .unwrap_or_else(|error| panic!("inst_dialect AOT {level:?}: {error}"));
        assert_eq!(object.dialect_legalization.as_ref(), Some(&aot_report));
        native::link_run(
            &format!("inst_dialect-{level:?}"),
            &object.object_code,
            &driver,
        )
        .expect("native AArch64 host");

        let buffer = jit(&source, &registry, level, false, &symbols)
            .unwrap_or_else(|error| panic!("inst_dialect JIT {level:?}: {error}"));
        assert_eq!(buffer.dialect_legalization.as_ref(), Some(&report));
        // SAFETY: `dialect_roundtrip` is `(i32) -> i32` in the corpus row.
        let entry: extern "C" fn(i32) -> i32 =
            unsafe { std::mem::transmute(function_ptr(&buffer, "dialect_roundtrip")) };
        let before = RUNTIME_CALLS.load(Ordering::SeqCst);
        for (x, want) in inputs.iter().zip(&expected) {
            assert_eq!(entry(*x), *want, "JIT {level:?} dialect_roundtrip({x})");
        }
        assert!(RUNTIME_CALLS.load(Ordering::SeqCst) >= before + inputs.len());
    }

    // A runtime contract is not checked in the compile.
    for error in [
        aot(&source, &registry, OptLevel::O2, true).expect_err("proof-required AOT"),
        jit(&source, &registry, OptLevel::O2, true, &symbols).expect_err("proof-required JIT"),
    ] {
        let error = dialect_error(error);
        assert!(
            matches!(&error, DialectPipelineError::ProofPolicy { rule, evidence, .. }
                if rule == "verif.bfs_step/runtime-call:tcg_corpus_inst_dialect_bfs_step"
                    && evidence.starts_with("runtime-contract")),
            "{error}"
        );
    }
}

#[test]
fn the_rust_runtime_decoder_refuses_a_corrupted_descriptor() {
    let op = the_op(&fixture("inst_dialect"));
    let descriptor =
        trust_cg_codegen::dialect_legalization::encode_payload_descriptor(&op).unwrap();
    assert_eq!(
        decode_descriptor(&descriptor).map(|hash| (hash ^ 5) as i32),
        Some(reference_result(&op, 5)),
        "encoder and the independent decoder agree on the row's payload"
    );
    for cut in [0, 4, 8, descriptor.len() - 1] {
        assert_eq!(
            decode_descriptor(&descriptor[..cut]),
            None,
            "truncated at {cut}"
        );
    }
    let mut trailing = descriptor.clone();
    trailing.push(0);
    assert_eq!(decode_descriptor(&trailing), None);
    let mut flipped = descriptor.clone();
    let last = flipped.len() - 1;
    flipped[last] ^= 1;
    assert_ne!(decode_descriptor(&flipped), decode_descriptor(&descriptor));
}

// ---------------------------------------------------------------------------
// ty_dialect_v39: a nominal type legalized to its carrier
// ---------------------------------------------------------------------------

fn example_registry() -> DialectLegalizationRegistry {
    let mut registrations = DialectLegalizationRegistry::default_registrations();
    registrations.push(DialectRegistration {
        namespace: "example".to_string(),
        version: 1,
        owner: "trust-cg corpus test: the ty_dialect_v39 row's nominal `example.value@1`, \
                which trust-ir gives exact-typed transport and nothing else; this \
                registration declares its machine carrier and native ABI as i64"
            .to_string(),
        grammar: DialectGrammar::Exact(Vec::new()),
        ops: Vec::new(),
        types: vec![TypeRule {
            name: "value".to_string(),
            version: 1,
            carrier: Ty::I64,
            rule: "example.value@1/i64-carrier".to_string(),
            evidence: LegalizationEvidence::CheckedTransportSubstitution,
        }],
    });
    DialectLegalizationRegistry::new(registrations).expect("well-formed")
}

/// Which parameter each returned value of `function` carries, reading only
/// exact-typed transport (`copy`) and `ret`; anything else is not transport.
fn transport_reading(function: &Function) -> Vec<usize> {
    let [block] = function.blocks.as_slice() else {
        panic!("one block");
    };
    let mut carries: HashMap<ValueId, usize> = block
        .params
        .iter()
        .enumerate()
        .map(|(index, (value, _))| (*value, index))
        .collect();
    for node in &block.body {
        match &node.inst {
            Inst::Copy { operand, .. } => {
                let parameter = carries[operand];
                carries.insert(node.results[0], parameter);
            }
            Inst::Return { values } => return values.iter().map(|value| carries[value]).collect(),
            other => panic!("not transport: {other:?}"),
        }
    }
    panic!("no return")
}

/// A C spelling of `x` with no literal outside `long long`'s range.
fn c_i64(x: i64) -> String {
    if x == i64::MIN {
        "(-9223372036854775807LL - 1)".to_string()
    } else {
        format!("{x}LL")
    }
}

/// The core module a frontend would have written with `i64` in place of the
/// nominal type.
fn core_twin(source: &Module) -> Module {
    let mut twin = source.clone();
    for signature in &mut twin.func_types {
        for ty in signature
            .params
            .iter_mut()
            .chain(signature.returns.iter_mut())
        {
            *ty = Ty::I64;
        }
    }
    for function in &mut twin.functions {
        function.source_provenance = None;
        for block in &mut function.blocks {
            for (_, ty) in &mut block.params {
                *ty = Ty::I64;
            }
            for node in &mut block.body {
                if let Inst::Copy { ty, .. } = &mut node.inst {
                    *ty = Ty::I64;
                }
            }
        }
    }
    assert!(!has_dialect_constructs(&twin));
    twin
}

#[test]
fn ty_dialect_v39_legalizes_to_its_carrier_and_compiles_exactly_like_core() {
    let source = fixture("ty_dialect_v39");
    let function = &source.functions[0];
    assert_eq!(function.name, "nominal_identity");
    assert_eq!(
        transport_reading(function),
        vec![0],
        "the body returns its parameter"
    );

    let default = DialectLegalizationRegistry::trust_cg_default();
    for error in [
        aot(&source, &default, OptLevel::O0, false).expect_err("AOT"),
        jit(&source, &default, OptLevel::O0, false, &HashMap::new()).expect_err("JIT"),
    ] {
        let error = dialect_error(error);
        assert!(
            matches!(&error, DialectPipelineError::UnregisteredDialect { namespace, usage }
                if namespace == "example" && usage == "nominal type `example.value@1`"),
            "{error}"
        );
    }

    let registry = example_registry();
    let report = expected_report(&source, &registry, true);
    let [receipt] = report.receipts.as_slice() else {
        panic!("one receipt");
    };
    assert_eq!(
        (
            receipt.dialect.as_str(),
            receipt.dialect_version,
            receipt.rule.as_str()
        ),
        ("example", 1, "example.value@1/i64-carrier")
    );
    assert_eq!(
        receipt.subject,
        LegalizationSubject::Type {
            name: "value".into(),
            version: 1,
            carrier: "i64".into(),
        }
    );
    // Signature parameter and return, the block parameter, the copy.
    assert_eq!(receipt.site, LegalizationSite::Module { occurrences: 4 });
    assert_eq!(
        report.provenance_invalidated,
        vec!["nominal_identity".to_string()]
    );

    let twin = core_twin(&source);
    let inputs = [
        0i64,
        1,
        -1,
        i64::MIN,
        i64::MAX,
        0x0123_4567_89ab_cdef,
        -0x7654_3210,
        1 << 40,
    ];
    let driver = format!(
        "#include <stdint.h>\n#include <stdio.h>\nextern int64_t nominal_identity(int64_t);\n\
         static const int64_t XS[] = {{{}}};\n\
         int main(void) {{\n  int checks = 0;\n  for (int i = 0; i < {count}; i++) {{\n\
         \x20   if (nominal_identity(XS[i]) != XS[i]) {{ printf(\"case %d\\n\", i); return 1; }}\n\
         \x20   checks++;\n  }}\n  printf(\"checks=%d\\n\", checks);\n  return checks == {count} ? 0 : 2;\n}}\n",
        inputs
            .iter()
            .map(|x| c_i64(*x))
            .collect::<Vec<_>>()
            .join(","),
        count = inputs.len(),
    );
    let aot_report = expected_report(&with_host_target(&source), &registry, false);
    for level in LEVELS {
        let object = aot(&source, &registry, level, false)
            .unwrap_or_else(|error| panic!("ty_dialect_v39 AOT {level:?}: {error}"));
        assert_eq!(object.dialect_legalization.as_ref(), Some(&aot_report));
        let core = aot(&twin, &registry, level, false).expect("core twin compiles");
        assert!(core.dialect_legalization.is_none());
        assert_eq!(
            object.object_code, core.object_code,
            "{level:?}: the legalized module takes exactly the core path"
        );
        native::link_run(
            &format!("ty_dialect_v39-{level:?}"),
            &object.object_code,
            &driver,
        )
        .expect("native AArch64 host");

        let buffer = jit(&source, &registry, level, false, &HashMap::new())
            .unwrap_or_else(|error| panic!("ty_dialect_v39 JIT {level:?}: {error}"));
        // SAFETY: the carrier ABI of `(example.value@1) -> example.value@1`
        // is `(i64) -> i64` under this registration.
        let entry: extern "C" fn(i64) -> i64 =
            unsafe { std::mem::transmute(function_ptr(&buffer, "nominal_identity")) };
        for x in inputs {
            assert_eq!(entry(x), x, "JIT {level:?}");
        }
    }

    // A proof requirement admits the checked carrier substitution; what the
    // compile then decides is exactly what it decides for the core twin.
    for level in [OptLevel::O0, OptLevel::O2] {
        let legalized = aot(&source, &registry, level, true);
        let core = aot(&twin, &registry, level, true);
        match (&legalized, &core) {
            (Ok(legalized), Ok(core)) => {
                assert_eq!(legalized.object_code, core.object_code);
                assert!(
                    legalized
                        .dialect_legalization
                        .as_ref()
                        .unwrap()
                        .proof_required
                );
            }
            (Err(legalized), Err(core)) => {
                assert!(
                    !matches!(legalized, CompileError::DialectPipeline(_)),
                    "the legalization itself is admitted: {legalized}"
                );
                assert_eq!(legalized.to_string(), core.to_string(), "{level:?}");
            }
            _ => panic!(
                "{level:?}: proof-required verdicts differ: legalized {:?} vs core {:?}",
                legalized.as_ref().map(|_| ()).map_err(ToString::to_string),
                core.as_ref().map(|_| ()).map_err(ToString::to_string)
            ),
        }
        let legalized = jit(&source, &registry, level, true, &HashMap::new()).map(|_| ());
        let core = jit(&twin, &registry, level, true, &HashMap::new()).map(|_| ());
        assert_eq!(
            legalized.map_err(|error| error.to_string()),
            core.map_err(|error| error.to_string()),
            "{level:?}: proof-required JIT verdicts agree"
        );
    }
}

// ---------------------------------------------------------------------------
// The proof policy of a verifying JIT validation mode
// ---------------------------------------------------------------------------

#[test]
fn a_verifying_jit_validation_mode_alone_imposes_the_proof_policy() {
    // The sweep's first site is `vector.reduce`, a cited-theorem rewrite.
    let (sweep, _) = sweep_module();
    let registry = DialectLegalizationRegistry::trust_cg_default();
    let compiler = |mode: JitValidationMode| {
        Compiler::new(CompilerConfig {
            emit_proofs: false,
            jit_validation_mode_override: Some(mode),
            ..CompilerConfig::for_host_jit()
        })
        .with_codegen_license(permit_unlicensed())
        .with_dialect_legalization_registry(registry.clone())
    };
    // `emit_proofs` is off: the validation mode is the only proof claim.
    for mode in [
        JitValidationMode::CachedVerified,
        JitValidationMode::AlwaysVerify,
    ] {
        let error = dialect_error(
            compiler(mode)
                .compile_module_to_jit(&sweep, &HashMap::new())
                .expect_err("a verifying JIT refuses an unchecked rewrite"),
        );
        assert!(
            matches!(&error, DialectPipelineError::ProofPolicy { rule, evidence, .. }
                if rule == "vector.reduce/trust-ir-lane-fold"
                    && evidence.starts_with("cited-upstream-theorem")),
            "{mode:?}: {error}"
        );
    }
    let unchecked = compiler(JitValidationMode::Unchecked)
        .compile_module_to_jit(&sweep, &HashMap::new())
        .expect("an explicitly unchecked JIT admits the rewrite");
    assert!(
        !unchecked
            .dialect_legalization
            .as_ref()
            .expect("report")
            .proof_required
    );
}

// ---------------------------------------------------------------------------
// A runtime call over a registered nominal type
// ---------------------------------------------------------------------------

const PEEK_SYMBOL: &str = "tcg_corpus_acme_peek";
/// The descriptor of an attribute-free `acme.peek` v1 payload, counted by
/// hand: magic 4, format version 4, "acme" 4+4, "peek" 4+4, payload version
/// 4, attribute count 4.
const PEEK_DESCRIPTOR_LEN: u64 = 32;

fn cell_ty() -> Ty {
    Ty::Dialect(Box::new(DialectTy::new("acme", "cell", 1)))
}

/// `acme` v1: a nominal `acme.cell@1` carried as `ptr` (the address of an
/// `i64`), and `peek(acme.cell@1) -> i64` bound to the test runtime.
fn acme_peek_registration(peek_operand: Ty) -> DialectRegistration {
    DialectRegistration {
        namespace: "acme".to_string(),
        version: 1,
        owner: "trust-cg corpus test: `acme.cell@1` is the address of an i64 and `acme.peek` \
                reads it, a meaning only the bound test runtime gives"
            .to_string(),
        grammar: DialectGrammar::Exact(vec![OperationSchema {
            name: "peek".to_string(),
            operands: vec![OperandType::Exact(peek_operand)],
            results: vec![Ty::I64],
            attributes: Vec::new(),
        }]),
        ops: Vec::new(),
        types: vec![TypeRule {
            name: "cell".to_string(),
            version: 1,
            carrier: Ty::Ptr,
            rule: "acme.cell@1/ptr-carrier".to_string(),
            evidence: LegalizationEvidence::CheckedTransportSubstitution,
        }],
    }
    .bind_runtime_call(
        "peek",
        PEEK_SYMBOL,
        "the dialect_legalization_corpus.rs test runtime (C for AOT, Rust for the JIT)",
    )
}

fn registry_with(extra: Vec<DialectRegistration>) -> DialectLegalizationRegistry {
    let mut registrations = DialectLegalizationRegistry::default_registrations();
    registrations.extend(extra);
    DialectLegalizationRegistry::new(registrations).expect("well-formed")
}

/// `read_cell(c: param) -> i64 { c1 = copy c; r = acme.peek(c1); ret r }`.
fn peek_module(param: Ty) -> Module {
    let mut module = Module::new("acme_peek");
    let ty = module
        .add_func_type(FuncTy {
            params: vec![param.clone()],
            returns: vec![Ty::I64],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut function = Function::new(FuncId::new(0), "read_cell", ty, BlockId::new(0));
    let mut block = Block::new(BlockId::new(0));
    block.params = vec![(v(0), param.clone())];
    let mut peek = DialectInst::new("acme", "peek")
        .with_operand(v(1))
        .with_result_ty(Ty::I64);
    peek.version = 1;
    block.body = vec![
        InstrNode::new(Inst::Copy {
            ty: param,
            operand: v(0),
        })
        .with_result(v(1)),
        InstrNode::new(Inst::DialectOp(Box::new(peek))).with_result(v(2)),
        InstrNode::new(Inst::Return { values: vec![v(2)] }),
    ];
    function.blocks.push(block);
    module.functions.push(function);
    module
}

static PEEK_CALLS: AtomicUsize = AtomicUsize::new(0);

extern "C" fn rust_peek(descriptor: *const u8, len: u64, cell: *const i64) -> i64 {
    PEEK_CALLS.fetch_add(1, Ordering::SeqCst);
    // SAFETY: the legalized call passes the address and exact length of the
    // module's read-only descriptor, and the caller's `i64` cell.
    let bytes = unsafe { std::slice::from_raw_parts(descriptor, len as usize) };
    if !bytes.starts_with(b"TCGD") {
        return i64::MIN;
    }
    unsafe { *cell }.wrapping_add(1000 * len as i64)
}

const C_PEEK_RUNTIME: &str = r#"
#include <stdint.h>
#include <string.h>
int64_t tcg_corpus_acme_peek(const uint8_t *d, uint64_t n, const int64_t *cell) {
  if (n < 4 || memcmp(d, "TCGD", 4) != 0) return INT64_MIN;
  return (int64_t)((uint64_t)*cell + 1000u * n);
}
"#;

#[test]
fn a_runtime_call_over_a_nominal_type_executes_with_the_carrier_abi() {
    let source = peek_module(cell_ty());
    let registry = registry_with(vec![acme_peek_registration(cell_ty())]);
    let report = expected_report(&source, &registry, false);
    assert_eq!(
        rules(&report),
        vec![
            "acme.peek/runtime-call:tcg_corpus_acme_peek",
            "acme.cell@1/ptr-carrier"
        ]
    );
    // The runtime declaration the legalization adds is not a source function.
    assert_eq!(report.provenance_invalidated, vec!["read_cell".to_string()]);
    // Signature parameter, block parameter and the copy.
    assert_eq!(
        report.receipts[1].site,
        LegalizationSite::Module { occurrences: 3 }
    );

    let inputs = [0i64, 1, -1, 42, i64::MIN, i64::MAX, -0x0123_4567_89ab];
    let expected: Vec<i64> = inputs
        .iter()
        .map(|x| x.wrapping_add(1000 * PEEK_DESCRIPTOR_LEN as i64))
        .collect();
    let mut driver = String::from(C_PEEK_RUNTIME);
    let _ = write!(
        driver,
        "#include <stdio.h>\nextern int64_t read_cell(const int64_t *);\n\
         static const int64_t XS[] = {{{}}};\nstatic const int64_t WANT[] = {{{}}};\n\
         int main(void) {{\n  int checks = 0;\n  for (int i = 0; i < {count}; i++) {{\n\
         \x20   int64_t cell = XS[i];\n\
         \x20   if (read_cell(&cell) != WANT[i]) {{ printf(\"case %d\\n\", i); return 1; }}\n\
         \x20   checks++;\n  }}\n  printf(\"checks=%d\\n\", checks);\n  return checks == {count} ? 0 : 2;\n}}\n",
        inputs
            .iter()
            .map(|x| c_i64(*x))
            .collect::<Vec<_>>()
            .join(","),
        expected
            .iter()
            .map(|x| c_i64(*x))
            .collect::<Vec<_>>()
            .join(","),
        count = inputs.len(),
    );
    let aot_report = expected_report(&with_host_target(&source), &registry, false);
    let mut symbols: HashMap<String, *const u8> = HashMap::new();
    symbols.insert(PEEK_SYMBOL.to_string(), rust_peek as *const u8);
    for level in LEVELS {
        let object = aot(&source, &registry, level, false)
            .unwrap_or_else(|error| panic!("acme.peek AOT {level:?}: {error}"));
        assert_eq!(object.dialect_legalization.as_ref(), Some(&aot_report));
        native::link_run(
            &format!("acme_peek-{level:?}"),
            &object.object_code,
            &driver,
        )
        .expect("native AArch64 host");

        let buffer = jit(&source, &registry, level, false, &symbols)
            .unwrap_or_else(|error| panic!("acme.peek JIT {level:?}: {error}"));
        assert_eq!(buffer.dialect_legalization.as_ref(), Some(&report));
        // SAFETY: under this registration `read_cell` is `(ptr) -> i64`.
        let entry: extern "C" fn(*const i64) -> i64 =
            unsafe { std::mem::transmute(function_ptr(&buffer, "read_cell")) };
        let before = PEEK_CALLS.load(Ordering::SeqCst);
        for (x, want) in inputs.iter().zip(&expected) {
            assert_eq!(entry(x), *want, "JIT {level:?} read_cell(&{x})");
        }
        assert!(PEEK_CALLS.load(Ordering::SeqCst) >= before + inputs.len());
    }

    // A runtime contract is not checked in the compile.
    for error in [
        aot(&source, &registry, OptLevel::O2, true).expect_err("proof-required AOT"),
        jit(&source, &registry, OptLevel::O2, true, &symbols).expect_err("proof-required JIT"),
    ] {
        let error = dialect_error(error);
        assert!(
            matches!(&error, DialectPipelineError::ProofPolicy { rule, .. }
                if rule == "acme.peek/runtime-call:tcg_corpus_acme_peek"),
            "{error}"
        );
    }

    // An op consuming another namespace's nominal value is refused by name,
    // by the compiler entries themselves.
    let other_ty = Ty::Dialect(Box::new(DialectTy::new("other", "t", 1)));
    let other = DialectRegistration {
        namespace: "other".to_string(),
        version: 1,
        owner: "trust-cg corpus test (other)".to_string(),
        grammar: DialectGrammar::Exact(Vec::new()),
        ops: Vec::new(),
        types: vec![TypeRule {
            name: "t".to_string(),
            version: 1,
            carrier: Ty::Ptr,
            rule: "other.t@1/ptr-carrier".to_string(),
            evidence: LegalizationEvidence::CheckedTransportSubstitution,
        }],
    };
    let foreign = peek_module(other_ty.clone());
    let registry = registry_with(vec![acme_peek_registration(other_ty), other]);
    for error in [
        aot(&foreign, &registry, OptLevel::O0, false).expect_err("AOT"),
        jit(&foreign, &registry, OptLevel::O0, false, &symbols).expect_err("JIT"),
    ] {
        let error = dialect_error(error);
        assert!(
            matches!(&error, DialectPipelineError::NominalUse { detail }
                if detail.contains("`acme.peek`") && detail.contains("`other.t@1`")),
            "{error}"
        );
    }
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes (or is refused) because the license silently refused it.
fn permit_unlicensed() -> trust_cg_codegen::CodegenLicensePolicy {
    trust_cg_codegen::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_codegen::UnlicensedBodyPolicy::Permit)
}
