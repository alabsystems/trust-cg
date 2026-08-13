// trust-cg-codegen/tests/jit_integration_x86_64.rs - x86-64 JIT smoke test
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Smoke test for the x86-64 JIT path: compile a trivial `const42()` and
// `add(i64, i64) -> i64` function through the x86-64 pipeline (`X86Pipeline`),
// mmap the resulting raw code bytes as executable memory, invoke them as
// `extern "C"` function pointers, and assert the return values.
//
// Part of #467 — Add x86-64 JIT smoke test (x86_64 Unix-gated)
// Part of #445 — x86-64 end-to-end production hardening
//
// # cfg-gating
//
// This entire file is gated on `#[cfg(all(target_arch = "x86_64", unix))]`.
// On AArch64 hosts (the primary dev platform) and Windows x86_64 hosts, this
// Unix mmap/mprotect smoke is skipped at compile time. `cargo check --tests`
// still validates its syntax via the outer file-level `#![cfg]` attribute
// (rustc parses and attribute-filters the contents before type-checking). The
// test body runs only on Unix x86-64 hosts (Linux x86_64, macOS Intel).
//
// # Design choice: bypass JitCompiler::compile_raw
//
// `JitCompiler::compile_raw` (in `trust-cg-codegen::jit`) internally calls
// `crate::pipeline::encode_function_with_fixups`, which is an AArch64-only
// encoder keyed off `AArch64Opcode`. Feeding an x86-64 function through
// that path is not currently supported — extending `compile_raw` to
// dispatch on the input function's architecture (via a new
// `X86ISelFunction` input variant) is a JIT API change tracked separately
// and is explicitly out of scope for this smoke test (see task prompt).
//
// For this smoke we bypass the `JitCompiler` wrapper and exercise the
// raw x86-64 compile-and-execute path directly:
//   1. Build an `X86ISelFunction` (reuses the existing
//      `build_x86_const_test_function` / `build_x86_add_test_function`
//      helpers from `trust_cg_codegen::x86_64`).
//   2. Compile to raw machine code bytes via `X86Pipeline::compile_function`
//      with `X86OutputFormat::RawBytes` and `emit_frame = false` so the
//      emitted sequence is directly callable with the System V AMD64 ABI
//      (args in RDI/RSI, return in RAX) without touching RSP.
//   3. Allocate a writable page via `libc::mmap`, copy the bytes in,
//      flip to `PROT_READ | PROT_EXEC` via `libc::mprotect`, and invoke
//      the page as a function pointer.
//   4. Assert the returned value matches the expected semantic.
//
// x86-64 has coherent I/D caches, so no explicit `flush_icache` is needed
// after writing to executable memory (see `jit.rs:748-753`).
//
// # Acceptance criteria (#467)
//
// - [x] Test file `crates/trust-cg-codegen/tests/jit_integration_x86_64.rs`
//       (this file).
// - [x] Test is SKIPPED (not failed) on AArch64 hosts via cfg-gate
//       (`#![cfg(all(target_arch = "x86_64", unix))]`).
// - [x] No regression in AArch64 JIT tests (this file does not touch the
//       AArch64 JIT path; `jit_integration.rs` is unmodified).
// - [ ] Test runs on Unix x86-64 hosts (Linux x86_64, macOS Intel). This
//       repository's primary CI/dev hosts are AArch64 (Apple Silicon); Windows
//       x86_64 coverage uses separate COFF/object and platform-execution tests.

#![cfg(all(target_arch = "x86_64", unix))]

use std::collections::HashMap;

use std::arch::x86_64::__m128i;

use trust_cg_codegen::compiler::{
    Compiler, CompilerConfig, FunctionQualityMetrics, JitCompilationResult,
};
use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::x86_64::{
    X86OutputFormat, X86Pipeline, X86PipelineConfig, X86RegallocPressureEvidence, X86TargetFeature,
    X86TargetFeatures, build_x86_add_test_function, build_x86_const_test_function,
};
use trust_cg_ir::x86_64_ops::X86Opcode;
use trust_cg_ir::x86_64_regs::{RDI, RDX, RSI, X86PReg, XMM0, XMM1};
use trust_cg_lower::adapter::translate_function;
use trust_cg_lower::function::{BasicBlock, Function as LirFunction, Signature, StackSlotInfo};
use trust_cg_lower::instructions::{Block, Instruction, IntCC, Opcode, Value};
use trust_cg_lower::types::Type;
use trust_cg_lower::x86_64_isel::{X86ISelFunction, X86ISelInst, X86ISelOperand};
use trust_cg_opt::OptLevel as X86OptLevel;
use trust_ir::dialect::{AttrValue, DialectInst};
use trust_ir::{
    BinOp, Block as TrustIrBlock, BlockId, Constant, FuncId, FuncTy, FuncTyId,
    Function as TrustIrFunction, ICmpOp, Inst, InstrNode, Module as TrustIrModule, Ty as TrustIrTy,
    ValueId,
};

// ---------------------------------------------------------------------------
// Minimal raw mmap/mprotect/munmap bindings for test-local JIT execution.
//
// We avoid pulling in the `libc` crate as a dev-dependency — the codegen
// crate's dependency graph is intentionally lean and we don't want a test-
// only binding crate leaking into the production build even transitively.
// POSIX `mmap` / `mprotect` / `munmap` are ABI-stable and their prototypes
// have been frozen since SUSv3. Declaring them directly via `extern "C"`
// is safe and self-contained.
// ---------------------------------------------------------------------------

#[allow(non_camel_case_types)]
type c_void = core::ffi::c_void;
#[allow(non_camel_case_types)]
type c_int = core::ffi::c_int;
#[allow(non_camel_case_types)]
type size_t = usize;
#[allow(non_camel_case_types)]
type off_t = i64;

const PROT_NONE: c_int = 0;
const PROT_READ: c_int = 1;
const PROT_WRITE: c_int = 2;
const PROT_EXEC: c_int = 4;

const MAP_PRIVATE: c_int = 0x0002;
#[cfg(target_os = "macos")]
const MAP_ANON: c_int = 0x1000;
#[cfg(target_os = "linux")]
const MAP_ANON: c_int = 0x0020;

const MAP_FAILED: *mut c_void = !0usize as *mut c_void;

unsafe extern "C" {
    fn mmap(
        addr: *mut c_void,
        len: size_t,
        prot: c_int,
        flags: c_int,
        fd: c_int,
        offset: off_t,
    ) -> *mut c_void;
    fn mprotect(addr: *mut c_void, len: size_t, prot: c_int) -> c_int;
    fn munmap(addr: *mut c_void, len: size_t) -> c_int;
}

const PAGE_SIZE: usize = 4096; // x86-64 on macOS + Linux

fn page_align(len: usize) -> usize {
    (len + PAGE_SIZE - 1) & !(PAGE_SIZE - 1)
}

/// RAII-style executable code buffer. Allocates a page, writes the code,
/// flips to RX. `Drop` releases the mapping.
struct ExecPage {
    ptr: *mut c_void,
    size: usize,
}

impl ExecPage {
    fn new(code: &[u8]) -> Self {
        assert!(!code.is_empty(), "code must be nonempty");
        let size = page_align(code.len());
        // SAFETY: standard POSIX mmap anonymous allocation; we check
        // MAP_FAILED below before dereferencing.
        let ptr = unsafe {
            mmap(
                core::ptr::null_mut(),
                size,
                PROT_READ | PROT_WRITE,
                MAP_PRIVATE | MAP_ANON,
                -1,
                0,
            )
        };
        assert!(ptr != MAP_FAILED, "mmap failed");
        let _ = PROT_NONE; // silence unused warning on non-debug builds

        // SAFETY: `ptr` is a page-aligned writable region of at least
        // `size >= code.len()` bytes; `code.as_ptr()` is valid for
        // `code.len()` bytes; regions do not overlap.
        unsafe {
            core::ptr::copy_nonoverlapping(code.as_ptr(), ptr as *mut u8, code.len());
        }

        // Flip the page to RX. x86-64 has coherent I/D caches, no icache
        // flush needed (see jit.rs sys::flush_icache x86_64 branch).
        // SAFETY: `ptr`/`size` describe the live mapping just produced.
        let rc = unsafe { mprotect(ptr, size, PROT_READ | PROT_EXEC) };
        assert_eq!(rc, 0, "mprotect RX failed");

        ExecPage { ptr, size }
    }

    fn as_ptr(&self) -> *const u8 {
        self.ptr as *const u8
    }
}

impl Drop for ExecPage {
    fn drop(&mut self) {
        // SAFETY: `ptr`/`size` describe the live mapping created in `new`.
        // After `drop` the `ExecPage` is gone and no reference survives.
        unsafe {
            let _ = munmap(self.ptr, self.size);
        }
    }
}

// ---------------------------------------------------------------------------
// Helper: compile an X86ISelFunction to raw callable bytes.
//
// `emit_frame = false` is required here — the test invokes the returned
// bytes directly as an `extern "C"` leaf function. With a prologue that
// pushes RBP/saves RSP, the simplified regalloc + test builders (which do
// not allocate stack slots) would still need epilogue RBP pop; the leaf
// form (no frame) is the smallest self-contained executable sequence.
// ---------------------------------------------------------------------------

fn compile_leaf(func: &trust_cg_lower::x86_64_isel::X86ISelFunction) -> Vec<u8> {
    let pipeline = X86Pipeline::new(X86PipelineConfig {
        emit_frame: false,
        output_format: X86OutputFormat::RawBytes,
        ..X86PipelineConfig::default()
    });
    pipeline
        .compile_function(func)
        .expect("x86-64 compile_function should succeed for the smoke test")
}

fn compile_lir_leaf(func: &LirFunction) -> Vec<u8> {
    let pipeline = X86Pipeline::new(X86PipelineConfig {
        emit_frame: false,
        output_format: X86OutputFormat::RawBytes,
        ..X86PipelineConfig::default()
    });
    pipeline
        .compile_trust_ir_function(func)
        .expect("x86-64 compile_trust_ir_function should succeed for the smoke test")
}

fn compile_lir_host_jit_o0_raw(func: &LirFunction) -> Vec<u8> {
    let pipeline = X86Pipeline::new(X86PipelineConfig {
        opt_level: X86OptLevel::O0,
        emit_frame: true,
        output_format: X86OutputFormat::RawBytes,
        ..X86PipelineConfig::default()
    });
    pipeline
        .compile_trust_ir_function(func)
        .expect("x86-64 host JIT raw pipeline should compile the helper")
}

fn compile_lir_o0_raw_with_features(
    func: &LirFunction,
    target_features: X86TargetFeatures,
) -> Result<(Vec<u8>, X86RegallocPressureEvidence), trust_cg_codegen::x86_64::X86PipelineError> {
    let pipeline = X86Pipeline::new(X86PipelineConfig {
        opt_level: X86OptLevel::O0,
        emit_frame: true,
        output_format: X86OutputFormat::RawBytes,
        target_features,
        ..X86PipelineConfig::host_jit()
    });
    pipeline.compile_trust_ir_function_with_regalloc_pressure_evidence(func)
}

fn compile_isel_o0_raw_with_features(
    func: &X86ISelFunction,
    target_features: X86TargetFeatures,
) -> (Vec<u8>, X86RegallocPressureEvidence) {
    let pipeline = X86Pipeline::new(X86PipelineConfig {
        opt_level: X86OptLevel::O0,
        emit_frame: true,
        output_format: X86OutputFormat::RawBytes,
        target_features,
        ..X86PipelineConfig::host_jit()
    });
    pipeline
        .compile_function_with_regalloc_pressure_evidence(func)
        .expect("x86-64 spill-fold canary should compile")
}

fn single_translated_lir_function(module: &TrustIrModule) -> LirFunction {
    let mut translated = trust_cg_lower::translate_module(module)
        .expect("test trust_ir helper must translate to LIR");
    assert_eq!(
        translated.len(),
        1,
        "test helper should translate to one LIR function"
    );
    translated.pop().expect("translated function").0
}

fn contains_sse2_opcode(code: &[u8], opcode: u8) -> bool {
    code.windows(3).any(|w| w == [0x66, 0x0F, opcode])
        || code.windows(4).any(|w| {
            w[0] == 0x66 && (0x40..=0x4F).contains(&w[1]) && w[2] == 0x0F && w[3] == opcode
        })
}

fn contains_packed_dword_shift_imm(code: &[u8], subopcode: u8, imm: u8) -> bool {
    code.windows(5).any(|w| {
        w[0] == 0x66
            && w[1] == 0x0F
            && w[2] == 0x72
            && ((w[3] >> 3) & 0x07) == subopcode
            && w[4] == imm
    }) || code.windows(6).any(|w| {
        w[0] == 0x66
            && (0x40..=0x4F).contains(&w[1])
            && w[2] == 0x0F
            && w[3] == 0x72
            && ((w[4] >> 3) & 0x07) == subopcode
            && w[5] == imm
    })
}

fn contains_any_packed_dword_shift_imm(code: &[u8]) -> bool {
    code.windows(4).any(|w| {
        w[0] == 0x66 && w[1] == 0x0F && w[2] == 0x72 && matches!((w[3] >> 3) & 0x07, 2 | 4 | 6)
    }) || code.windows(5).any(|w| {
        w[0] == 0x66
            && (0x40..=0x4F).contains(&w[1])
            && w[2] == 0x0F
            && w[3] == 0x72
            && matches!((w[4] >> 3) & 0x07, 2 | 4 | 6)
    })
}

fn contains_sse41_0f38_opcode(code: &[u8], opcode: u8) -> bool {
    code.windows(4).any(|w| w == [0x66, 0x0F, 0x38, opcode])
        || code.windows(5).any(|w| {
            w[0] == 0x66
                && (0x40..=0x4F).contains(&w[1])
                && w[2] == 0x0F
                && w[3] == 0x38
                && w[4] == opcode
        })
}

fn contains_sse41_0f3a_opcode(code: &[u8], opcode: u8) -> bool {
    code.windows(4).any(|w| w == [0x66, 0x0F, 0x3A, opcode])
        || code.windows(5).any(|w| {
            w[0] == 0x66
                && (0x40..=0x4F).contains(&w[1])
                && w[2] == 0x0F
                && w[3] == 0x3A
                && w[4] == opcode
        })
}

fn is_legacy_pmovmskb_modrm_byte(code: &[u8], idx: usize) -> bool {
    if idx < 3 || code.get(idx - 1) != Some(&0xD7) || code.get(idx - 2) != Some(&0x0F) {
        return false;
    }
    code.get(idx - 3) == Some(&0x66)
        || (idx >= 4 && (0x40..=0x4F).contains(&code[idx - 3]) && code.get(idx - 4) == Some(&0x66))
}

fn contains_vex_prefix_byte(code: &[u8]) -> bool {
    code.iter()
        .enumerate()
        .any(|(idx, byte)| matches!(byte, 0xC4 | 0xC5) && !is_legacy_pmovmskb_modrm_byte(code, idx))
}

fn contains_vex_instruction_prefix(code: &[u8]) -> bool {
    code.iter().enumerate().any(|(idx, byte)| match byte {
        0xC4 if !is_legacy_pmovmskb_modrm_byte(code, idx) => {
            let Some(vex_m) = code.get(idx + 1) else {
                return false;
            };
            matches!(vex_m & 0x1F, 0x01..=0x03) && code.get(idx + 3).is_some()
        }
        0xC5 if !is_legacy_pmovmskb_modrm_byte(code, idx) => code.get(idx + 2).is_some(),
        _ => false,
    })
}

fn assert_no_scalar_lane_fallback(
    evidence: &trust_cg_codegen::x86_64::X86MachineCodeEvidence,
    label: &str,
) {
    assert_eq!(evidence.pinsrd_count, 0, "{label}: {evidence:?}");
    assert_eq!(evidence.pinsrq_count, 0, "{label}: {evidence:?}");
    assert_eq!(evidence.pextrd_count, 0, "{label}: {evidence:?}");
    assert_eq!(evidence.pextrq_count, 0, "{label}: {evidence:?}");
}

fn contains_rbp_relative_local_lea(code: &[u8]) -> bool {
    code.windows(3).any(|w| {
        w[0] == 0x48
            && w[1] == 0x8D
            && matches!(w[2], 0x45 | 0x4D | 0x55 | 0x5D | 0x65 | 0x6D | 0x75 | 0x7D)
    })
}

fn contains_rbp_disp8_movdqa_load(code: &[u8], disp: u8) -> bool {
    code.windows(5).any(|w| {
        w[0] == 0x66 && w[1] == 0x0F && w[2] == 0x6F && w[3] & 0b1100_0111 == 0x45 && w[4] == disp
    })
}

fn contains_rbp_disp8_i32_load(code: &[u8], disp: u8) -> bool {
    code.windows(4)
        .any(|w| w[0] == 0x8B && w[1] & 0b1100_0111 == 0x45 && w[2] == disp)
        || code.windows(5).any(|w| {
            (0x40..=0x4F).contains(&w[0])
                && w[1] == 0x8B
                && w[2] & 0b1100_0111 == 0x45
                && w[3] == disp
        })
}

fn host_jit_o0_compiler() -> Compiler {
    // JIT-5: this suite exercises raw x86-64 codegen mechanics — including SIMD
    // lane opcodes whose per-instruction proofs are still pending — so it uses
    // the dev-only Unchecked validation mode explicitly. Under the new x86
    // default (CachedVerified) these SIMD functions would (correctly) fail
    // closed because their bytes are not yet cert-covered. `for_host_jit_unchecked`
    // is the loud in-code opt-in for exactly this dev/codegen-test case; the
    // CachedVerified default path is covered by jit_x86_64_profile_modes and the
    // dedicated jit_validation_modes_x86_64 suite.
    let mut config = CompilerConfig::for_host_jit_unchecked();
    config.opt_level = OptLevel::O0;
    Compiler::new(config)
}

fn v2i64_ty() -> TrustIrTy {
    TrustIrTy::Vector(Box::new(TrustIrTy::I64), 2)
}

fn v4i32_ty() -> TrustIrTy {
    TrustIrTy::Vector(Box::new(TrustIrTy::I32), 4)
}

fn v16i8_ty() -> TrustIrTy {
    TrustIrTy::Vector(Box::new(TrustIrTy::I8), 16)
}

fn v8i16_ty() -> TrustIrTy {
    TrustIrTy::Vector(Box::new(TrustIrTy::I16), 8)
}

fn v(n: u32) -> ValueId {
    ValueId::new(n)
}

fn b(n: u32) -> BlockId {
    BlockId::new(n)
}

fn f(n: u32) -> FuncId {
    FuncId::new(n)
}

fn func_ty(params: Vec<TrustIrTy>, returns: Vec<TrustIrTy>) -> FuncTy {
    FuncTy {
        params,
        returns,
        is_vararg: false,
    }
}

fn single_function_module(
    func_id: u32,
    name: &str,
    ty: FuncTy,
    blocks: Vec<TrustIrBlock>,
) -> TrustIrModule {
    let entry = blocks.first().expect("module must have a block").id;
    let mut module = TrustIrModule::new(format!("{}_module", name));
    let func_ty_id: FuncTyId = module.add_func_type(ty);
    let mut func = TrustIrFunction::new(f(func_id), name, func_ty_id, entry);
    func.blocks = blocks;
    module.add_function(func);
    module
}

fn add_function_to_module(
    module: &mut TrustIrModule,
    func_id: u32,
    name: &str,
    ty: FuncTy,
    blocks: Vec<TrustIrBlock>,
) {
    let entry = blocks.first().expect("function must have a block").id;
    let func_ty_id: FuncTyId = module.add_func_type(ty);
    let mut func = TrustIrFunction::new(f(func_id), name, func_ty_id, entry);
    func.blocks = blocks;
    module.add_function(func);
}

fn metrics_for<'a>(result: &'a JitCompilationResult, name: &str) -> &'a FunctionQualityMetrics {
    result
        .per_function_metrics
        .iter()
        .find(|metrics| metrics.name == name)
        .unwrap_or_else(|| panic!("{name} per-function metrics should be present"))
}

fn jit_symbol_code_bytes<'a>(result: &'a JitCompilationResult, name: &str) -> &'a [u8] {
    let metrics = metrics_for(result, name);
    let ptr = result
        .buffer
        .get_fn_ptr_bound(name)
        .unwrap_or_else(|| panic!("{name} symbol must be present"))
        .as_ptr();
    // SAFETY: `ptr` is a lifetime-bound pointer into `result.buffer`, and
    // `code_size_bytes` is checked against replay metadata by the callers.
    unsafe { core::slice::from_raw_parts(ptr, metrics.code_size_bytes) }
}

fn assert_metrics_code_size_matches_replay(result: &JitCompilationResult, name: &str) {
    let metrics = metrics_for(result, name);
    let replay = result.buffer.replay_report_metadata();
    let symbol = replay
        .symbols
        .iter()
        .find(|symbol| symbol.name == name)
        .unwrap_or_else(|| panic!("{name} replay symbol should be present"));
    let symbol_size = usize::try_from(symbol.range.end_offset - symbol.range.start_offset)
        .expect("symbol range should fit usize");

    assert!(
        metrics.code_size_bytes > 0,
        "{name} should expose nonzero per-symbol code bytes"
    );
    assert_eq!(
        metrics.code_size_bytes, symbol_size,
        "{name} code_size_bytes should match replay symbol range"
    );
}

const INST_VECTOR_DIALECT_FIXTURE: &str =
    include_str!("fixtures/trust_ir_conformance/inst_vector_dialect.trust_ir");
const INST_VECTOR_DIALECT_SOURCE_RECORD: &str =
    include_str!("fixtures/trust_ir_conformance/inst_vector_dialect.source.txt");
const INST_VECTOR_DIALECT_SOURCE_COMMIT: &str = "e2cc0db8208a7ee04e4219bbbad05a8fd91871cc";
const PORTABLE_VECTOR_DIALECT_FN: &str = "portable_vector_dialect";

fn v4_bool_ty() -> TrustIrTy {
    TrustIrTy::Vector(Box::new(TrustIrTy::Bool), 4)
}

fn v2_bool_ty() -> TrustIrTy {
    TrustIrTy::Vector(Box::new(TrustIrTy::Bool), 2)
}

fn v16_bool_ty() -> TrustIrTy {
    TrustIrTy::Vector(Box::new(TrustIrTy::Bool), 16)
}

fn v8_bool_ty() -> TrustIrTy {
    TrustIrTy::Vector(Box::new(TrustIrTy::Bool), 8)
}

fn load_inst_vector_dialect_fixture() -> TrustIrModule {
    assert!(
        INST_VECTOR_DIALECT_SOURCE_RECORD.contains(INST_VECTOR_DIALECT_SOURCE_COMMIT),
        "vendored inst_vector_dialect fixture must record its trust_ir source commit"
    );
    let module = trust_ir::parser::parse_module(INST_VECTOR_DIALECT_FIXTURE)
        .expect("vendored inst_vector_dialect .trust_ir fixture must parse");
    let errors = trust_ir_build::validate_module(&module);
    assert!(
        errors.is_empty(),
        "vendored inst_vector_dialect fixture must validate: {errors:?}"
    );
    assert_eq!(module.name, "inst_vector_dialect");
    module
}

fn vector_dialect_ops(module: &TrustIrModule) -> Vec<&DialectInst> {
    module
        .functions
        .iter()
        .flat_map(|function| function.blocks.iter())
        .flat_map(|block| block.body.iter())
        .filter_map(|node| match &node.inst {
            Inst::DialectOp(op) if op.dialect == trust_ir::dialect::vector::DIALECT => {
                Some(op.as_ref())
            }
            _ => None,
        })
        .collect()
}

fn dialect_attr_eq(op: &DialectInst, name: &str, value: &AttrValue) -> bool {
    op.attrs
        .iter()
        .any(|attr| attr.name == name && &attr.value == value)
}

fn assert_inst_vector_fixture_payloads(module: &TrustIrModule) {
    let ops = vector_dialect_ops(module);
    assert_eq!(
        ops.iter().map(|op| op.op.as_str()).collect::<Vec<_>>(),
        vec![
            trust_ir::dialect::vector::PACK_LANES_OP,
            trust_ir::dialect::vector::EXTRACT_LANE_OP,
            trust_ir::dialect::vector::INSERT_LANE_OP,
            trust_ir::dialect::vector::PACK_LANES_OP,
            trust_ir::dialect::vector::EXTRACT_LANE_OP,
            trust_ir::dialect::vector::INSERT_LANE_OP,
            trust_ir::dialect::vector::MASK_TO_BITS_OP,
            trust_ir::dialect::vector::MASK_TO_BITS_OP,
        ],
        "fixture must preserve canonical vector dialect op order"
    );
    assert!(
        ops.iter()
            .any(|op| op.op == trust_ir::dialect::vector::PACK_LANES_OP
                && op.operands.len() == 4
                && op.result_tys == vec![v4i32_ty()]),
        "serialized fixture must exercise <4 x i32> vector.pack_lanes"
    );
    assert!(
        ops.iter()
            .any(|op| op.op == trust_ir::dialect::vector::PACK_LANES_OP
                && op.operands.len() == 2
                && op.result_tys == vec![v2i64_ty()]),
        "serialized fixture must exercise <2 x i64> vector.pack_lanes"
    );
    assert!(
        ops.iter()
            .any(|op| op.op == trust_ir::dialect::vector::EXTRACT_LANE_OP
                && op.result_tys == vec![TrustIrTy::I32]
                && dialect_attr_eq(op, "vector_ty", &AttrValue::Ty(v4i32_ty()))
                && dialect_attr_eq(op, "lane", &AttrValue::U64(2))),
        "serialized fixture must exercise <4 x i32> vector.extract_lane"
    );
    assert!(
        ops.iter()
            .any(|op| op.op == trust_ir::dialect::vector::EXTRACT_LANE_OP
                && op.result_tys == vec![TrustIrTy::I64]
                && dialect_attr_eq(op, "vector_ty", &AttrValue::Ty(v2i64_ty()))
                && dialect_attr_eq(op, "lane", &AttrValue::U64(1))),
        "serialized fixture must exercise <2 x i64> vector.extract_lane"
    );
    assert!(
        ops.iter()
            .any(|op| op.op == trust_ir::dialect::vector::INSERT_LANE_OP
                && op.result_tys == vec![v4i32_ty()]
                && dialect_attr_eq(op, "lane", &AttrValue::U64(1))),
        "serialized fixture must exercise <4 x i32> vector.insert_lane"
    );
    assert!(
        ops.iter()
            .any(|op| op.op == trust_ir::dialect::vector::INSERT_LANE_OP
                && op.result_tys == vec![v2i64_ty()]
                && dialect_attr_eq(op, "lane", &AttrValue::U64(0))),
        "serialized fixture must exercise <2 x i64> vector.insert_lane"
    );
    assert!(
        ops.iter()
            .any(|op| op.op == trust_ir::dialect::vector::MASK_TO_BITS_OP
                && op.result_tys == vec![TrustIrTy::I32]
                && dialect_attr_eq(op, "mask_ty", &AttrValue::Ty(v4_bool_ty()))
                && dialect_attr_eq(op, "bit_order", &AttrValue::Str("lsb_lane0".to_string()))),
        "serialized fixture must exercise <4 x bool> vector.mask_to_bits"
    );
    assert!(
        ops.iter()
            .any(|op| op.op == trust_ir::dialect::vector::MASK_TO_BITS_OP
                && op.result_tys == vec![TrustIrTy::I64]
                && dialect_attr_eq(op, "mask_ty", &AttrValue::Ty(v2_bool_ty()))
                && dialect_attr_eq(op, "bit_order", &AttrValue::Str("lsb_lane0".to_string()))),
        "serialized fixture must exercise <2 x bool> vector.mask_to_bits"
    );
}

fn portable_vector_dialect_function(module: &TrustIrModule) -> &TrustIrFunction {
    module
        .functions
        .iter()
        .find(|function| function.name == PORTABLE_VECTOR_DIALECT_FN)
        .expect("inst_vector_dialect fixture must contain portable_vector_dialect")
}

fn count_lir_ops(lir_func: &LirFunction, mut matches_opcode: impl FnMut(&Opcode) -> bool) -> usize {
    lir_func
        .blocks
        .values()
        .flat_map(|block| block.instructions.iter())
        .filter(|inst| matches_opcode(&inst.opcode))
        .count()
}

fn assert_inst_vector_fixture_lir_direct_paths(lir_func: &LirFunction) {
    assert!(
        lir_func.stack_slots.is_empty(),
        "fixture vector dialect lowering should avoid adapter stack materialization"
    );
    assert_eq!(
        count_lir_ops(lir_func, |opcode| matches!(opcode, Opcode::V4I32PackLanes)),
        1
    );
    assert_eq!(
        count_lir_ops(lir_func, |opcode| matches!(opcode, Opcode::V2I64PackLanes)),
        1
    );
    assert_eq!(
        count_lir_ops(lir_func, |opcode| matches!(
            opcode,
            Opcode::V4I32ExtractLane { lane: 2 }
        )),
        1
    );
    assert_eq!(
        count_lir_ops(lir_func, |opcode| matches!(
            opcode,
            Opcode::V4I32InsertLane { lane: 1 }
        )),
        1
    );
    assert_eq!(
        count_lir_ops(lir_func, |opcode| matches!(
            opcode,
            Opcode::V2I64ExtractLane { lane: 1 }
        )),
        1
    );
    assert_eq!(
        count_lir_ops(lir_func, |opcode| matches!(
            opcode,
            Opcode::V2I64InsertLane { lane: 0 }
        )),
        1
    );
    assert_eq!(
        count_lir_ops(lir_func, |opcode| matches!(
            opcode,
            Opcode::V4I32MaskExtract
        )),
        1
    );
    assert_eq!(
        count_lir_ops(lir_func, |opcode| matches!(
            opcode,
            Opcode::V2I64MaskExtract {
                result_ty: Type::I64
            }
        )),
        1
    );
}

#[test]
fn test_x86_64_jit_replays_trust_ir_inst_vector_dialect_fixture() {
    let module = load_inst_vector_dialect_fixture();
    assert_inst_vector_fixture_payloads(&module);

    let (lir_func, _) = translate_function(portable_vector_dialect_function(&module), &module)
        .expect("adapter must translate canonical inst_vector_dialect fixture");
    assert_inst_vector_fixture_lir_direct_paths(&lir_func);

    let result = host_jit_o0_compiler()
        .compile_module_to_jit(&module, &HashMap::new())
        .expect("x86-64 host JIT must compile canonical inst_vector_dialect fixture");
    assert_eq!(result.metrics.function_count, 1);
    assert_metrics_code_size_matches_replay(&result, PORTABLE_VECTOR_DIALECT_FN);
    assert!(
        result
            .buffer
            .get_fn_ptr_bound(PORTABLE_VECTOR_DIALECT_FN)
            .is_some(),
        "JIT buffer must publish the fixture function symbol"
    );

    let metrics = metrics_for(&result, PORTABLE_VECTOR_DIALECT_FN);
    eprintln!(
        "x86 inst_vector_dialect fixture metrics: code_size={}, movd_to_xmm={}, movq_to_xmm={}, \
         punpckldq={}, punpcklqdq={}, pshufd={}, pmovmskb={}, pinsrd={}, pinsrq={}, \
         pextrd={}, pextrq={}",
        metrics.code_size_bytes,
        metrics.x86_machine_code.movd_to_xmm_count,
        metrics.x86_machine_code.movq_to_xmm_count,
        metrics.x86_machine_code.punpckldq_count,
        metrics.x86_machine_code.punpcklqdq_count,
        metrics.x86_machine_code.pshufd_count,
        metrics.x86_machine_code.pmovmskb_count,
        metrics.x86_machine_code.pinsrd_count,
        metrics.x86_machine_code.pinsrq_count,
        metrics.x86_machine_code.pextrd_count,
        metrics.x86_machine_code.pextrq_count
    );
    assert_eq!(
        metrics.x86_machine_code.pmovmskb_count, 2,
        "both fixture mask_to_bits ops should compact through PMOVMSKB: {:?}",
        metrics.x86_machine_code
    );
    assert!(
        metrics.x86_machine_code.movd_to_xmm_count >= 4,
        "fixture <4 x i32> lane ops should seed dword lanes directly: {:?}",
        metrics.x86_machine_code
    );
    assert!(
        metrics.x86_machine_code.movq_to_xmm_count >= 2,
        "fixture <2 x i64> lane ops should seed qword lanes directly: {:?}",
        metrics.x86_machine_code
    );
    assert!(
        metrics.x86_machine_code.punpckldq_count >= 2,
        "fixture <4 x i32> lane ops should assemble through SSE2 unpack: {:?}",
        metrics.x86_machine_code
    );
    assert!(
        metrics.x86_machine_code.punpcklqdq_count >= 2,
        "fixture vector lane ops should assemble qword lanes directly: {:?}",
        metrics.x86_machine_code
    );
    assert_eq!(
        metrics.x86_machine_code.pinsrd_count, 0,
        "fixture should not use scalar PINSRD lane materialization: {:?}",
        metrics.x86_machine_code
    );
    assert_eq!(
        metrics.x86_machine_code.pinsrq_count, 0,
        "fixture should not use scalar PINSRQ lane materialization: {:?}",
        metrics.x86_machine_code
    );
    assert_eq!(
        metrics.x86_machine_code.pextrd_count, 0,
        "fixture should not scalarize dword lanes with PEXTRD: {:?}",
        metrics.x86_machine_code
    );
    assert_eq!(
        metrics.x86_machine_code.pextrq_count, 0,
        "fixture should not scalarize qword lanes with PEXTRQ: {:?}",
        metrics.x86_machine_code
    );
}

fn v2i64_mask_const(value: i128) -> Constant {
    Constant::Vector(vec![Constant::Int(value), Constant::Int(value)])
}

fn v4i32_mask_const(value: i128) -> Constant {
    Constant::Vector(vec![
        Constant::Int(value),
        Constant::Int(value),
        Constant::Int(value),
        Constant::Int(value),
    ])
}

fn bool_mask_const_from_bits(lanes: usize, true_bits: u32) -> Constant {
    Constant::Vector(
        (0..lanes)
            .map(|lane| Constant::Bool((true_bits & (1_u32 << lane)) != 0))
            .collect(),
    )
}

fn m128i_from_i32x4(lanes: [i32; 4]) -> __m128i {
    // SAFETY: `__m128i` and four i32 lanes are both exactly 16 bytes.
    unsafe { core::mem::transmute(lanes) }
}

fn i64x2_from_m128i(value: __m128i) -> [i64; 2] {
    // SAFETY: `__m128i` and two i64 lanes are both exactly 16 bytes.
    unsafe { core::mem::transmute(value) }
}

fn i32x4_from_m128i(value: __m128i) -> [i32; 4] {
    // SAFETY: `__m128i` and four i32 lanes are both exactly 16 bytes.
    unsafe { core::mem::transmute(value) }
}

fn x86_preg_mem(base: X86PReg, disp: i32) -> X86ISelOperand {
    X86ISelOperand::MemAddr {
        base: Box::new(X86ISelOperand::PReg(base)),
        disp,
    }
}

fn x86_stack_slot_mem(slot: u32) -> X86ISelOperand {
    X86ISelOperand::MemAddr {
        base: Box::new(X86ISelOperand::StackSlot(slot)),
        disp: 0,
    }
}

fn build_packed_rhs_spill_canary_function(
    name: &str,
    opcode: X86Opcode,
    folded_rhs: bool,
) -> X86ISelFunction {
    let mut func = X86ISelFunction::new(
        name.to_string(),
        Signature {
            params: vec![Type::I64, Type::I64, Type::I64],
            returns: vec![],
        },
    );
    let entry = Block(0);
    func.ensure_block(entry);
    func.stack_slots.push(StackSlotInfo::new(16, 16));

    func.push_inst(
        entry,
        X86ISelInst::new(
            X86Opcode::MovdquRM,
            vec![X86ISelOperand::PReg(XMM0), x86_preg_mem(RDI, 0)],
        ),
    );
    func.push_inst(
        entry,
        X86ISelInst::new(
            X86Opcode::MovdquRM,
            vec![X86ISelOperand::PReg(XMM1), x86_preg_mem(RSI, 0)],
        ),
    );
    func.push_inst(
        entry,
        X86ISelInst::new(
            X86Opcode::MovdquMR,
            vec![x86_stack_slot_mem(0), X86ISelOperand::PReg(XMM1)],
        ),
    );

    let rhs = if folded_rhs {
        x86_stack_slot_mem(0)
    } else {
        func.push_inst(
            entry,
            X86ISelInst::new(
                X86Opcode::MovdquRM,
                vec![X86ISelOperand::PReg(XMM1), x86_stack_slot_mem(0)],
            ),
        );
        X86ISelOperand::PReg(XMM1)
    };

    func.push_inst(
        entry,
        X86ISelInst::new(
            opcode,
            vec![X86ISelOperand::PReg(XMM0), X86ISelOperand::PReg(XMM0), rhs],
        ),
    );
    func.push_inst(
        entry,
        X86ISelInst::new(
            X86Opcode::MovdquMR,
            vec![x86_preg_mem(RDX, 0), X86ISelOperand::PReg(XMM0)],
        ),
    );
    func.push_inst(entry, X86ISelInst::new(X86Opcode::Ret, vec![]));
    func
}

fn build_pshufd_rhs_spill_canary_function(name: &str, folded_rhs: bool) -> X86ISelFunction {
    let mut func = X86ISelFunction::new(
        name.to_string(),
        Signature {
            params: vec![Type::I64, Type::I64],
            returns: vec![],
        },
    );
    let entry = Block(0);
    func.ensure_block(entry);
    func.stack_slots.push(StackSlotInfo::new(16, 16));

    func.push_inst(
        entry,
        X86ISelInst::new(
            X86Opcode::MovdquRM,
            vec![X86ISelOperand::PReg(XMM1), x86_preg_mem(RDI, 0)],
        ),
    );
    func.push_inst(
        entry,
        X86ISelInst::new(
            X86Opcode::MovdquMR,
            vec![x86_stack_slot_mem(0), X86ISelOperand::PReg(XMM1)],
        ),
    );

    let src = if folded_rhs {
        x86_stack_slot_mem(0)
    } else {
        func.push_inst(
            entry,
            X86ISelInst::new(
                X86Opcode::MovdquRM,
                vec![X86ISelOperand::PReg(XMM1), x86_stack_slot_mem(0)],
            ),
        );
        X86ISelOperand::PReg(XMM1)
    };

    func.push_inst(
        entry,
        X86ISelInst::new(
            X86Opcode::Pshufd,
            vec![X86ISelOperand::PReg(XMM0), src, X86ISelOperand::Imm(0x1B)],
        ),
    );
    func.push_inst(
        entry,
        X86ISelInst::new(
            X86Opcode::MovdquMR,
            vec![x86_preg_mem(RSI, 0), X86ISelOperand::PReg(XMM0)],
        ),
    );
    func.push_inst(entry, X86ISelInst::new(X86Opcode::Ret, vec![]));
    func
}

fn build_v2i64_repeated_const_store_module(func_id: u32, name: &str, value: i128) -> TrustIrModule {
    let vector_ty = v2i64_ty();

    single_function_module(
        func_id,
        name,
        func_ty(vec![TrustIrTy::Ptr], vec![]),
        vec![TrustIrBlock {
            id: b(0),
            params: vec![(v(0), TrustIrTy::Ptr)],
            body: vec![
                InstrNode::new(Inst::Const {
                    ty: vector_ty.clone(),
                    value: v2i64_mask_const(value),
                })
                .with_result(v(10)),
                InstrNode::new(Inst::Store {
                    ty: vector_ty,
                    ptr: v(0),
                    value: v(10),
                    align: None,
                    volatile: false,
                }),
                InstrNode::new(Inst::Return { values: vec![] }),
            ],
        }],
    )
}

fn build_jit_opcode_evidence_module() -> TrustIrModule {
    let mut module = TrustIrModule::new("jit_opcode_evidence_module");
    let v4_i32 = v4i32_ty();
    let v2_i64 = v2i64_ty();

    add_function_to_module(
        &mut module,
        8820,
        "jit_evidence_v4_mask_extract",
        func_ty(vec![TrustIrTy::Ptr], vec![TrustIrTy::I32]),
        vec![TrustIrBlock {
            id: b(0),
            params: vec![(v(0), TrustIrTy::Ptr)],
            body: vec![
                InstrNode::new(Inst::Load {
                    ty: v4_i32.clone(),
                    ptr: v(0),
                    align: None,
                    volatile: false,
                })
                .with_result(v(10)),
                InstrNode::new(Inst::DialectOp(Box::new(
                    trust_cg_lower::bitfield_dialect::v4i32_mask_extract(v(10)),
                )))
                .with_result(v(11)),
                InstrNode::new(Inst::Return {
                    values: vec![v(11)],
                }),
            ],
        }],
    );

    add_function_to_module(
        &mut module,
        8821,
        "jit_evidence_v2_mask_extract",
        func_ty(vec![TrustIrTy::Ptr], vec![TrustIrTy::I32]),
        vec![TrustIrBlock {
            id: b(0),
            params: vec![(v(0), TrustIrTy::Ptr)],
            body: vec![
                InstrNode::new(Inst::Load {
                    ty: v2_i64.clone(),
                    ptr: v(0),
                    align: None,
                    volatile: false,
                })
                .with_result(v(10)),
                InstrNode::new(Inst::DialectOp(Box::new(
                    trust_cg_lower::bitfield_dialect::v2i64_mask_extract(v(10), TrustIrTy::I32),
                )))
                .with_result(v(11)),
                InstrNode::new(Inst::Return {
                    values: vec![v(11)],
                }),
            ],
        }],
    );

    add_function_to_module(
        &mut module,
        8822,
        "jit_evidence_v2_zero_lane0_insert",
        func_ty(vec![TrustIrTy::Ptr, TrustIrTy::I64], vec![]),
        vec![TrustIrBlock {
            id: b(0),
            params: vec![(v(0), TrustIrTy::Ptr), (v(1), TrustIrTy::I64)],
            body: vec![
                InstrNode::new(Inst::Const {
                    ty: v2_i64.clone(),
                    value: v2i64_mask_const(0),
                })
                .with_result(v(10)),
                InstrNode::new(Inst::Const {
                    ty: TrustIrTy::I64,
                    value: Constant::Int(0),
                })
                .with_result(v(11)),
                InstrNode::new(Inst::InsertElement {
                    ty: v2_i64.clone(),
                    array: v(10),
                    index: v(11),
                    value: v(1),
                })
                .with_result(v(12)),
                InstrNode::new(Inst::Store {
                    ty: v2_i64.clone(),
                    ptr: v(0),
                    value: v(12),
                    align: None,
                    volatile: false,
                }),
                InstrNode::new(Inst::Return { values: vec![] }),
            ],
        }],
    );

    add_function_to_module(
        &mut module,
        8830,
        "jit_evidence_v2_all_ones_const_store",
        func_ty(vec![TrustIrTy::Ptr], vec![]),
        vec![TrustIrBlock {
            id: b(0),
            params: vec![(v(0), TrustIrTy::Ptr)],
            body: vec![
                InstrNode::new(Inst::Const {
                    ty: v2_i64.clone(),
                    value: v2i64_mask_const(-1),
                })
                .with_result(v(10)),
                InstrNode::new(Inst::Store {
                    ty: v2_i64.clone(),
                    ptr: v(0),
                    value: v(10),
                    align: None,
                    volatile: false,
                }),
                InstrNode::new(Inst::Return { values: vec![] }),
            ],
        }],
    );

    add_function_to_module(
        &mut module,
        8831,
        "jit_evidence_v2_repeated_const_store",
        func_ty(vec![TrustIrTy::Ptr], vec![]),
        vec![TrustIrBlock {
            id: b(0),
            params: vec![(v(0), TrustIrTy::Ptr)],
            body: vec![
                InstrNode::new(Inst::Const {
                    ty: v2_i64.clone(),
                    value: v2i64_mask_const(42),
                })
                .with_result(v(10)),
                InstrNode::new(Inst::Store {
                    ty: v2_i64.clone(),
                    ptr: v(0),
                    value: v(10),
                    align: None,
                    volatile: false,
                }),
                InstrNode::new(Inst::Return { values: vec![] }),
            ],
        }],
    );

    add_function_to_module(
        &mut module,
        8823,
        "jit_evidence_v4_lane_ops",
        func_ty(vec![TrustIrTy::Ptr, TrustIrTy::I32], vec![TrustIrTy::I32]),
        vec![TrustIrBlock {
            id: b(0),
            params: vec![(v(0), TrustIrTy::Ptr), (v(1), TrustIrTy::I32)],
            body: vec![
                InstrNode::new(Inst::Load {
                    ty: v4_i32.clone(),
                    ptr: v(0),
                    align: None,
                    volatile: false,
                })
                .with_result(v(10)),
                InstrNode::new(Inst::Const {
                    ty: TrustIrTy::I64,
                    value: Constant::Int(2),
                })
                .with_result(v(11)),
                InstrNode::new(Inst::ExtractElement {
                    ty: TrustIrTy::I32,
                    array: v(10),
                    index: v(11),
                })
                .with_result(v(12)),
                InstrNode::new(Inst::InsertElement {
                    ty: v4_i32.clone(),
                    array: v(10),
                    index: v(11),
                    value: v(1),
                })
                .with_result(v(13)),
                InstrNode::new(Inst::Copy {
                    ty: v4_i32.clone(),
                    operand: v(13),
                })
                .with_result(v(14)),
                InstrNode::new(Inst::Store {
                    ty: v4_i32,
                    ptr: v(0),
                    value: v(14),
                    align: None,
                    volatile: false,
                }),
                InstrNode::new(Inst::Return {
                    values: vec![v(12)],
                }),
            ],
        }],
    );

    add_function_to_module(
        &mut module,
        8824,
        "jit_evidence_v2_lane_ops",
        func_ty(vec![TrustIrTy::Ptr, TrustIrTy::I64], vec![TrustIrTy::I64]),
        vec![TrustIrBlock {
            id: b(0),
            params: vec![(v(0), TrustIrTy::Ptr), (v(1), TrustIrTy::I64)],
            body: vec![
                InstrNode::new(Inst::Load {
                    ty: v2_i64.clone(),
                    ptr: v(0),
                    align: None,
                    volatile: false,
                })
                .with_result(v(10)),
                InstrNode::new(Inst::Const {
                    ty: TrustIrTy::I64,
                    value: Constant::Int(1),
                })
                .with_result(v(11)),
                InstrNode::new(Inst::ExtractElement {
                    ty: TrustIrTy::I64,
                    array: v(10),
                    index: v(11),
                })
                .with_result(v(12)),
                InstrNode::new(Inst::InsertElement {
                    ty: v2_i64.clone(),
                    array: v(10),
                    index: v(11),
                    value: v(1),
                })
                .with_result(v(13)),
                InstrNode::new(Inst::Copy {
                    ty: v2_i64.clone(),
                    operand: v(13),
                })
                .with_result(v(14)),
                InstrNode::new(Inst::Store {
                    ty: v2_i64,
                    ptr: v(0),
                    value: v(14),
                    align: None,
                    volatile: false,
                }),
                InstrNode::new(Inst::Return {
                    values: vec![v(12)],
                }),
            ],
        }],
    );

    add_function_to_module(
        &mut module,
        8825,
        "jit_evidence_v2_ptest_select",
        func_ty(vec![TrustIrTy::Ptr, TrustIrTy::Ptr], vec![TrustIrTy::Ptr]),
        build_v2i64_cmp_pointer_select_module(8825, "jit_evidence_v2_ptest_select", ICmpOp::Slt)
            .functions
            .into_iter()
            .next()
            .expect("helper module should contain one function")
            .blocks,
    );

    let v4_same_lane_pack_ty = v4i32_ty();
    add_function_to_module(
        &mut module,
        8832,
        "jit_evidence_v4_same_lane_pack",
        func_ty(vec![TrustIrTy::Ptr, TrustIrTy::I32], vec![]),
        vec![TrustIrBlock {
            id: b(0),
            params: vec![(v(0), TrustIrTy::Ptr), (v(1), TrustIrTy::I32)],
            body: vec![
                InstrNode::new(Inst::DialectOp(Box::new(
                    trust_ir::dialect::vector::pack_lanes(
                        v4_same_lane_pack_ty.clone(),
                        [v(1), v(1), v(1), v(1)],
                    ),
                )))
                .with_result(v(10)),
                InstrNode::new(Inst::Store {
                    ty: v4_same_lane_pack_ty,
                    ptr: v(0),
                    value: v(10),
                    align: None,
                    volatile: false,
                }),
                InstrNode::new(Inst::Return { values: vec![] }),
            ],
        }],
    );

    let v4_distinct_lane_pack_ty = v4i32_ty();
    add_function_to_module(
        &mut module,
        8836,
        "jit_evidence_v4_distinct_lane_pack",
        func_ty(
            vec![
                TrustIrTy::Ptr,
                TrustIrTy::I32,
                TrustIrTy::I32,
                TrustIrTy::I32,
                TrustIrTy::I32,
            ],
            vec![],
        ),
        vec![TrustIrBlock {
            id: b(0),
            params: vec![
                (v(0), TrustIrTy::Ptr),
                (v(1), TrustIrTy::I32),
                (v(2), TrustIrTy::I32),
                (v(3), TrustIrTy::I32),
                (v(4), TrustIrTy::I32),
            ],
            body: vec![
                InstrNode::new(Inst::DialectOp(Box::new(
                    trust_ir::dialect::vector::pack_lanes(
                        v4_distinct_lane_pack_ty.clone(),
                        [v(1), v(2), v(3), v(4)],
                    ),
                )))
                .with_result(v(10)),
                InstrNode::new(Inst::Store {
                    ty: v4_distinct_lane_pack_ty,
                    ptr: v(0),
                    value: v(10),
                    align: None,
                    volatile: false,
                }),
                InstrNode::new(Inst::Return { values: vec![] }),
            ],
        }],
    );

    let v2_same_lane_pack_ty = v2i64_ty();
    add_function_to_module(
        &mut module,
        8833,
        "jit_evidence_v2_same_lane_pack",
        func_ty(vec![TrustIrTy::Ptr, TrustIrTy::I64], vec![]),
        vec![TrustIrBlock {
            id: b(0),
            params: vec![(v(0), TrustIrTy::Ptr), (v(1), TrustIrTy::I64)],
            body: vec![
                InstrNode::new(Inst::DialectOp(Box::new(
                    trust_ir::dialect::vector::pack_lanes(
                        v2_same_lane_pack_ty.clone(),
                        [v(1), v(1)],
                    ),
                )))
                .with_result(v(10)),
                InstrNode::new(Inst::Store {
                    ty: v2_same_lane_pack_ty,
                    ptr: v(0),
                    value: v(10),
                    align: None,
                    volatile: false,
                }),
                InstrNode::new(Inst::Return { values: vec![] }),
            ],
        }],
    );

    let v4_pack_extract_ty = v4i32_ty();
    add_function_to_module(
        &mut module,
        8834,
        "jit_evidence_v4_pack_extract_forward",
        func_ty(
            vec![
                TrustIrTy::I32,
                TrustIrTy::I32,
                TrustIrTy::I32,
                TrustIrTy::I32,
            ],
            vec![TrustIrTy::I32],
        ),
        vec![TrustIrBlock {
            id: b(0),
            params: vec![
                (v(0), TrustIrTy::I32),
                (v(1), TrustIrTy::I32),
                (v(2), TrustIrTy::I32),
                (v(3), TrustIrTy::I32),
            ],
            body: vec![
                InstrNode::new(Inst::DialectOp(Box::new(
                    trust_ir::dialect::vector::pack_lanes(
                        v4_pack_extract_ty.clone(),
                        [v(0), v(1), v(2), v(3)],
                    ),
                )))
                .with_result(v(10)),
                InstrNode::new(Inst::DialectOp(Box::new(
                    trust_ir::dialect::vector::extract_lane(v4_pack_extract_ty, v(10), 2),
                )))
                .with_result(v(11)),
                InstrNode::new(Inst::Return {
                    values: vec![v(11)],
                }),
            ],
        }],
    );

    let v2_pack_extract_ty = v2i64_ty();
    add_function_to_module(
        &mut module,
        8835,
        "jit_evidence_v2_pack_extract_forward",
        func_ty(vec![TrustIrTy::I64, TrustIrTy::I64], vec![TrustIrTy::I64]),
        vec![TrustIrBlock {
            id: b(0),
            params: vec![(v(0), TrustIrTy::I64), (v(1), TrustIrTy::I64)],
            body: vec![
                InstrNode::new(Inst::DialectOp(Box::new(
                    trust_ir::dialect::vector::pack_lanes(v2_pack_extract_ty.clone(), [v(0), v(1)]),
                )))
                .with_result(v(10)),
                InstrNode::new(Inst::DialectOp(Box::new(
                    trust_ir::dialect::vector::extract_lane(v2_pack_extract_ty, v(10), 1),
                )))
                .with_result(v(11)),
                InstrNode::new(Inst::Return {
                    values: vec![v(11)],
                }),
            ],
        }],
    );

    let v4_i32_mask_select = v4i32_ty();
    add_function_to_module(
        &mut module,
        8826,
        "jit_evidence_v4_mask_select",
        func_ty(vec![TrustIrTy::Ptr, TrustIrTy::Ptr, TrustIrTy::Ptr], vec![]),
        vec![TrustIrBlock {
            id: b(0),
            params: vec![
                (v(0), TrustIrTy::Ptr),
                (v(1), TrustIrTy::Ptr),
                (v(2), TrustIrTy::Ptr),
            ],
            body: vec![
                InstrNode::new(Inst::Load {
                    ty: v4_i32_mask_select.clone(),
                    ptr: v(0),
                    align: None,
                    volatile: false,
                })
                .with_result(v(10)),
                InstrNode::new(Inst::Load {
                    ty: v4_i32_mask_select.clone(),
                    ptr: v(1),
                    align: None,
                    volatile: false,
                })
                .with_result(v(11)),
                InstrNode::new(Inst::ICmp {
                    op: ICmpOp::Eq,
                    ty: v4_i32_mask_select.clone(),
                    lhs: v(10),
                    rhs: v(11),
                })
                .with_result(v(12)),
                InstrNode::new(Inst::Select {
                    ty: v4_i32_mask_select.clone(),
                    cond: v(12),
                    then_val: v(10),
                    else_val: v(11),
                })
                .with_result(v(13)),
                InstrNode::new(Inst::Store {
                    ty: v4_i32_mask_select,
                    ptr: v(2),
                    value: v(13),
                    align: None,
                    volatile: false,
                }),
                InstrNode::new(Inst::Return { values: vec![] }),
            ],
        }],
    );

    let v4_i32_ops = v4i32_ty();
    add_function_to_module(
        &mut module,
        8836,
        "jit_evidence_v4_i32_arith_logic",
        func_ty(vec![TrustIrTy::Ptr, TrustIrTy::Ptr, TrustIrTy::Ptr], vec![]),
        vec![TrustIrBlock {
            id: b(0),
            params: vec![
                (v(0), TrustIrTy::Ptr),
                (v(1), TrustIrTy::Ptr),
                (v(2), TrustIrTy::Ptr),
            ],
            body: vec![
                InstrNode::new(Inst::Load {
                    ty: v4_i32_ops.clone(),
                    ptr: v(0),
                    align: None,
                    volatile: false,
                })
                .with_result(v(10)),
                InstrNode::new(Inst::Load {
                    ty: v4_i32_ops.clone(),
                    ptr: v(1),
                    align: None,
                    volatile: false,
                })
                .with_result(v(11)),
                InstrNode::new(Inst::BinOp {
                    op: BinOp::Add,
                    ty: v4_i32_ops.clone(),
                    lhs: v(10),
                    rhs: v(11),
                })
                .with_result(v(12)),
                InstrNode::new(Inst::BinOp {
                    op: BinOp::Sub,
                    ty: v4_i32_ops.clone(),
                    lhs: v(10),
                    rhs: v(11),
                })
                .with_result(v(13)),
                InstrNode::new(Inst::BinOp {
                    op: BinOp::Mul,
                    ty: v4_i32_ops.clone(),
                    lhs: v(10),
                    rhs: v(11),
                })
                .with_result(v(14)),
                InstrNode::new(Inst::ICmp {
                    op: ICmpOp::Sgt,
                    ty: v4_i32_ops.clone(),
                    lhs: v(10),
                    rhs: v(11),
                })
                .with_result(v(15)),
                InstrNode::new(Inst::BinOp {
                    op: BinOp::And,
                    ty: v4_i32_ops.clone(),
                    lhs: v(12),
                    rhs: v(13),
                })
                .with_result(v(16)),
                InstrNode::new(Inst::BinOp {
                    op: BinOp::Or,
                    ty: v4_i32_ops.clone(),
                    lhs: v(16),
                    rhs: v(14),
                })
                .with_result(v(17)),
                InstrNode::new(Inst::BinOp {
                    op: BinOp::Xor,
                    ty: v4_i32_ops.clone(),
                    lhs: v(17),
                    rhs: v(15),
                })
                .with_result(v(18)),
                InstrNode::new(Inst::Store {
                    ty: v4_i32_ops,
                    ptr: v(2),
                    value: v(18),
                    align: None,
                    volatile: false,
                }),
                InstrNode::new(Inst::Return { values: vec![] }),
            ],
        }],
    );

    let v4_i32_bitselect = v4i32_ty();
    add_function_to_module(
        &mut module,
        8837,
        "jit_evidence_v4_i32_bitselect",
        func_ty(
            vec![
                TrustIrTy::Ptr,
                TrustIrTy::Ptr,
                TrustIrTy::Ptr,
                TrustIrTy::Ptr,
            ],
            vec![],
        ),
        vec![TrustIrBlock {
            id: b(0),
            params: vec![
                (v(0), TrustIrTy::Ptr),
                (v(1), TrustIrTy::Ptr),
                (v(2), TrustIrTy::Ptr),
                (v(3), TrustIrTy::Ptr),
            ],
            body: vec![
                InstrNode::new(Inst::Load {
                    ty: v4_i32_bitselect.clone(),
                    ptr: v(0),
                    align: None,
                    volatile: false,
                })
                .with_result(v(10)),
                InstrNode::new(Inst::Load {
                    ty: v4_i32_bitselect.clone(),
                    ptr: v(1),
                    align: None,
                    volatile: false,
                })
                .with_result(v(11)),
                InstrNode::new(Inst::Load {
                    ty: v4_i32_bitselect.clone(),
                    ptr: v(2),
                    align: None,
                    volatile: false,
                })
                .with_result(v(12)),
                InstrNode::new(Inst::Select {
                    ty: v4_i32_bitselect.clone(),
                    cond: v(10),
                    then_val: v(11),
                    else_val: v(12),
                })
                .with_result(v(13)),
                InstrNode::new(Inst::Store {
                    ty: v4_i32_bitselect,
                    ptr: v(3),
                    value: v(13),
                    align: None,
                    volatile: false,
                }),
                InstrNode::new(Inst::Return { values: vec![] }),
            ],
        }],
    );

    for (func_id, suffix, op) in [
        (8840, "ishl", BinOp::Shl),
        (8841, "ushr", BinOp::LShr),
        (8842, "sshr", BinOp::AShr),
    ] {
        let v4_i32_shift = v4i32_ty();
        add_function_to_module(
            &mut module,
            func_id,
            &format!("jit_evidence_v4_i32_lane_shift_{suffix}"),
            func_ty(vec![TrustIrTy::Ptr, TrustIrTy::Ptr, TrustIrTy::Ptr], vec![]),
            vec![TrustIrBlock {
                id: b(0),
                params: vec![
                    (v(0), TrustIrTy::Ptr),
                    (v(1), TrustIrTy::Ptr),
                    (v(2), TrustIrTy::Ptr),
                ],
                body: vec![
                    InstrNode::new(Inst::Load {
                        ty: v4_i32_shift.clone(),
                        ptr: v(0),
                        align: None,
                        volatile: false,
                    })
                    .with_result(v(10)),
                    InstrNode::new(Inst::Load {
                        ty: v4_i32_shift.clone(),
                        ptr: v(1),
                        align: None,
                        volatile: false,
                    })
                    .with_result(v(11)),
                    InstrNode::new(Inst::BinOp {
                        op,
                        ty: v4_i32_shift.clone(),
                        lhs: v(10),
                        rhs: v(11),
                    })
                    .with_result(v(12)),
                    InstrNode::new(Inst::Store {
                        ty: v4_i32_shift,
                        ptr: v(2),
                        value: v(12),
                        align: None,
                        volatile: false,
                    }),
                    InstrNode::new(Inst::Return { values: vec![] }),
                ],
            }],
        );
    }

    let v2_i64_eq = v2i64_ty();
    add_function_to_module(
        &mut module,
        8838,
        "jit_evidence_v2_i64_eq_mask_store",
        func_ty(vec![TrustIrTy::Ptr, TrustIrTy::Ptr, TrustIrTy::Ptr], vec![]),
        vec![TrustIrBlock {
            id: b(0),
            params: vec![
                (v(0), TrustIrTy::Ptr),
                (v(1), TrustIrTy::Ptr),
                (v(2), TrustIrTy::Ptr),
            ],
            body: vec![
                InstrNode::new(Inst::Load {
                    ty: v2_i64_eq.clone(),
                    ptr: v(0),
                    align: None,
                    volatile: false,
                })
                .with_result(v(10)),
                InstrNode::new(Inst::Load {
                    ty: v2_i64_eq.clone(),
                    ptr: v(1),
                    align: None,
                    volatile: false,
                })
                .with_result(v(11)),
                InstrNode::new(Inst::ICmp {
                    op: ICmpOp::Eq,
                    ty: v2_i64_eq.clone(),
                    lhs: v(10),
                    rhs: v(11),
                })
                .with_result(v(12)),
                InstrNode::new(Inst::Store {
                    ty: v2_i64_eq,
                    ptr: v(2),
                    value: v(12),
                    align: None,
                    volatile: false,
                }),
                InstrNode::new(Inst::Return { values: vec![] }),
            ],
        }],
    );

    let v2_i64_gt = v2i64_ty();
    add_function_to_module(
        &mut module,
        8839,
        "jit_evidence_v2_i64_gt_mask_store",
        func_ty(vec![TrustIrTy::Ptr, TrustIrTy::Ptr, TrustIrTy::Ptr], vec![]),
        vec![TrustIrBlock {
            id: b(0),
            params: vec![
                (v(0), TrustIrTy::Ptr),
                (v(1), TrustIrTy::Ptr),
                (v(2), TrustIrTy::Ptr),
            ],
            body: vec![
                InstrNode::new(Inst::Load {
                    ty: v2_i64_gt.clone(),
                    ptr: v(0),
                    align: None,
                    volatile: false,
                })
                .with_result(v(10)),
                InstrNode::new(Inst::Load {
                    ty: v2_i64_gt.clone(),
                    ptr: v(1),
                    align: None,
                    volatile: false,
                })
                .with_result(v(11)),
                InstrNode::new(Inst::ICmp {
                    op: ICmpOp::Sgt,
                    ty: v2_i64_gt.clone(),
                    lhs: v(10),
                    rhs: v(11),
                })
                .with_result(v(12)),
                InstrNode::new(Inst::Store {
                    ty: v2_i64_gt,
                    ptr: v(2),
                    value: v(12),
                    align: None,
                    volatile: false,
                }),
                InstrNode::new(Inst::Return { values: vec![] }),
            ],
        }],
    );

    module
}

fn build_v2i64_cmp_mask_module(func_id: u32, name: &str, op: ICmpOp) -> TrustIrModule {
    let vector_ty = v2i64_ty();
    single_function_module(
        func_id,
        name,
        func_ty(vec![TrustIrTy::Ptr, TrustIrTy::Ptr, TrustIrTy::Ptr], vec![]),
        vec![TrustIrBlock {
            id: b(0),
            params: vec![
                (v(0), TrustIrTy::Ptr),
                (v(1), TrustIrTy::Ptr),
                (v(2), TrustIrTy::Ptr),
            ],
            body: vec![
                InstrNode::new(Inst::Load {
                    ty: vector_ty.clone(),
                    ptr: v(0),
                    align: None,
                    volatile: false,
                })
                .with_result(v(10)),
                InstrNode::new(Inst::Load {
                    ty: vector_ty.clone(),
                    ptr: v(1),
                    align: None,
                    volatile: false,
                })
                .with_result(v(11)),
                InstrNode::new(Inst::ICmp {
                    op,
                    ty: vector_ty.clone(),
                    lhs: v(10),
                    rhs: v(11),
                })
                .with_result(v(12)),
                InstrNode::new(Inst::Const {
                    ty: vector_ty.clone(),
                    value: v2i64_mask_const(-1),
                })
                .with_result(v(13)),
                InstrNode::new(Inst::Const {
                    ty: vector_ty.clone(),
                    value: v2i64_mask_const(0),
                })
                .with_result(v(14)),
                InstrNode::new(Inst::Select {
                    ty: vector_ty.clone(),
                    cond: v(12),
                    then_val: v(13),
                    else_val: v(14),
                })
                .with_result(v(15)),
                InstrNode::new(Inst::Store {
                    ty: vector_ty,
                    ptr: v(2),
                    value: v(15),
                    align: None,
                    volatile: false,
                }),
                InstrNode::new(Inst::Return { values: vec![] }),
            ],
        }],
    )
}

fn build_v2i64_cmp_pointer_select_module(func_id: u32, name: &str, op: ICmpOp) -> TrustIrModule {
    let vector_ty = v2i64_ty();
    single_function_module(
        func_id,
        name,
        func_ty(vec![TrustIrTy::Ptr, TrustIrTy::Ptr], vec![TrustIrTy::Ptr]),
        vec![TrustIrBlock {
            id: b(0),
            params: vec![(v(0), TrustIrTy::Ptr), (v(1), TrustIrTy::Ptr)],
            body: vec![
                InstrNode::new(Inst::Load {
                    ty: vector_ty.clone(),
                    ptr: v(0),
                    align: None,
                    volatile: false,
                })
                .with_result(v(10)),
                InstrNode::new(Inst::Load {
                    ty: vector_ty.clone(),
                    ptr: v(1),
                    align: None,
                    volatile: false,
                })
                .with_result(v(11)),
                InstrNode::new(Inst::ICmp {
                    op,
                    ty: vector_ty,
                    lhs: v(10),
                    rhs: v(11),
                })
                .with_result(v(12)),
                InstrNode::new(Inst::Select {
                    ty: TrustIrTy::Ptr,
                    cond: v(12),
                    then_val: v(0),
                    else_val: v(1),
                })
                .with_result(v(15)),
                InstrNode::new(Inst::Return {
                    values: vec![v(15)],
                }),
            ],
        }],
    )
}

fn build_v2i64_cmp_bool_extract_return_module(
    func_id: u32,
    name: &str,
    op: ICmpOp,
    result_ty: TrustIrTy,
) -> TrustIrModule {
    let vector_ty = v2i64_ty();
    single_function_module(
        func_id,
        name,
        func_ty(
            vec![TrustIrTy::Ptr, TrustIrTy::Ptr],
            vec![result_ty.clone()],
        ),
        vec![TrustIrBlock {
            id: b(0),
            params: vec![(v(0), TrustIrTy::Ptr), (v(1), TrustIrTy::Ptr)],
            body: vec![
                InstrNode::new(Inst::Load {
                    ty: vector_ty.clone(),
                    ptr: v(0),
                    align: None,
                    volatile: false,
                })
                .with_result(v(10)),
                InstrNode::new(Inst::Load {
                    ty: vector_ty.clone(),
                    ptr: v(1),
                    align: None,
                    volatile: false,
                })
                .with_result(v(11)),
                InstrNode::new(Inst::ICmp {
                    op,
                    ty: vector_ty,
                    lhs: v(10),
                    rhs: v(11),
                })
                .with_result(v(12)),
                InstrNode::new(Inst::DialectOp(Box::new(
                    trust_cg_lower::bitfield_dialect::v2i64_bool_mask_extract(
                        v(12),
                        result_ty.clone(),
                    ),
                )))
                .with_result(v(13)),
                InstrNode::new(Inst::Return {
                    values: vec![v(13)],
                }),
            ],
        }],
    )
}

fn build_v4i32_ne_mask_extract_return_module(func_id: u32, name: &str) -> TrustIrModule {
    let vector_ty = v4i32_ty();
    single_function_module(
        func_id,
        name,
        func_ty(vec![TrustIrTy::Ptr, TrustIrTy::Ptr], vec![TrustIrTy::I32]),
        vec![TrustIrBlock {
            id: b(0),
            params: vec![(v(0), TrustIrTy::Ptr), (v(1), TrustIrTy::Ptr)],
            body: vec![
                InstrNode::new(Inst::Load {
                    ty: vector_ty.clone(),
                    ptr: v(0),
                    align: None,
                    volatile: false,
                })
                .with_result(v(10)),
                InstrNode::new(Inst::Load {
                    ty: vector_ty.clone(),
                    ptr: v(1),
                    align: None,
                    volatile: false,
                })
                .with_result(v(11)),
                InstrNode::new(Inst::ICmp {
                    op: ICmpOp::Ne,
                    ty: vector_ty.clone(),
                    lhs: v(10),
                    rhs: v(11),
                })
                .with_result(v(12)),
                InstrNode::new(Inst::Const {
                    ty: vector_ty.clone(),
                    value: v4i32_mask_const(-1),
                })
                .with_result(v(13)),
                InstrNode::new(Inst::Const {
                    ty: vector_ty.clone(),
                    value: v4i32_mask_const(0),
                })
                .with_result(v(14)),
                InstrNode::new(Inst::Select {
                    ty: vector_ty.clone(),
                    cond: v(12),
                    then_val: v(13),
                    else_val: v(14),
                })
                .with_result(v(15)),
                InstrNode::new(Inst::DialectOp(Box::new(
                    trust_cg_lower::bitfield_dialect::v4i32_mask_extract(v(15)),
                )))
                .with_result(v(16)),
                InstrNode::new(Inst::Return {
                    values: vec![v(16)],
                }),
            ],
        }],
    )
}

fn build_narrow_cmp_mask_to_bits_return_module(
    func_id: u32,
    name: &str,
    vector_ty: TrustIrTy,
    mask_ty: TrustIrTy,
    op: ICmpOp,
) -> TrustIrModule {
    single_function_module(
        func_id,
        name,
        func_ty(vec![TrustIrTy::Ptr, TrustIrTy::Ptr], vec![TrustIrTy::I32]),
        vec![TrustIrBlock {
            id: b(0),
            params: vec![(v(0), TrustIrTy::Ptr), (v(1), TrustIrTy::Ptr)],
            body: vec![
                InstrNode::new(Inst::Load {
                    ty: vector_ty.clone(),
                    ptr: v(0),
                    align: None,
                    volatile: false,
                })
                .with_result(v(10)),
                InstrNode::new(Inst::Load {
                    ty: vector_ty.clone(),
                    ptr: v(1),
                    align: None,
                    volatile: false,
                })
                .with_result(v(11)),
                InstrNode::new(Inst::ICmp {
                    op,
                    ty: vector_ty,
                    lhs: v(10),
                    rhs: v(11),
                })
                .with_result(v(12)),
                InstrNode::new(Inst::DialectOp(Box::new(
                    trust_ir::dialect::vector::mask_to_bits(mask_ty, v(12), TrustIrTy::I32),
                )))
                .with_result(v(13)),
                InstrNode::new(Inst::Return {
                    values: vec![v(13)],
                }),
            ],
        }],
    )
}

fn build_bool_const_mask_to_bits_return_module(
    func_id: u32,
    name: &str,
    mask_ty: TrustIrTy,
    lanes: usize,
    true_bits: u32,
) -> TrustIrModule {
    single_function_module(
        func_id,
        name,
        func_ty(vec![], vec![TrustIrTy::I32]),
        vec![TrustIrBlock {
            id: b(0),
            params: vec![],
            body: vec![
                InstrNode::new(Inst::Const {
                    ty: mask_ty.clone(),
                    value: bool_mask_const_from_bits(lanes, true_bits),
                })
                .with_result(v(10)),
                InstrNode::new(Inst::DialectOp(Box::new(
                    trust_ir::dialect::vector::mask_to_bits(mask_ty, v(10), TrustIrTy::I32),
                )))
                .with_result(v(11)),
                InstrNode::new(Inst::Return {
                    values: vec![v(11)],
                }),
            ],
        }],
    )
}

fn build_narrow_cmp_select_store_module(
    func_id: u32,
    name: &str,
    vector_ty: TrustIrTy,
    op: ICmpOp,
) -> TrustIrModule {
    single_function_module(
        func_id,
        name,
        func_ty(
            vec![
                TrustIrTy::Ptr,
                TrustIrTy::Ptr,
                TrustIrTy::Ptr,
                TrustIrTy::Ptr,
                TrustIrTy::Ptr,
            ],
            vec![],
        ),
        vec![TrustIrBlock {
            id: b(0),
            params: vec![
                (v(0), TrustIrTy::Ptr),
                (v(1), TrustIrTy::Ptr),
                (v(2), TrustIrTy::Ptr),
                (v(3), TrustIrTy::Ptr),
                (v(4), TrustIrTy::Ptr),
            ],
            body: vec![
                InstrNode::new(Inst::Load {
                    ty: vector_ty.clone(),
                    ptr: v(0),
                    align: None,
                    volatile: false,
                })
                .with_result(v(10)),
                InstrNode::new(Inst::Load {
                    ty: vector_ty.clone(),
                    ptr: v(1),
                    align: None,
                    volatile: false,
                })
                .with_result(v(11)),
                InstrNode::new(Inst::Load {
                    ty: vector_ty.clone(),
                    ptr: v(2),
                    align: None,
                    volatile: false,
                })
                .with_result(v(12)),
                InstrNode::new(Inst::Load {
                    ty: vector_ty.clone(),
                    ptr: v(3),
                    align: None,
                    volatile: false,
                })
                .with_result(v(13)),
                InstrNode::new(Inst::ICmp {
                    op,
                    ty: vector_ty.clone(),
                    lhs: v(10),
                    rhs: v(11),
                })
                .with_result(v(14)),
                InstrNode::new(Inst::Select {
                    ty: vector_ty.clone(),
                    cond: v(14),
                    then_val: v(12),
                    else_val: v(13),
                })
                .with_result(v(15)),
                InstrNode::new(Inst::Store {
                    ty: vector_ty,
                    ptr: v(4),
                    value: v(15),
                    align: None,
                    volatile: false,
                }),
                InstrNode::new(Inst::Return { values: vec![] }),
            ],
        }],
    )
}

fn build_bool_const_select_store_module(
    func_id: u32,
    name: &str,
    vector_ty: TrustIrTy,
    mask_ty: TrustIrTy,
    lanes: usize,
    true_bits: u32,
) -> TrustIrModule {
    single_function_module(
        func_id,
        name,
        func_ty(vec![TrustIrTy::Ptr, TrustIrTy::Ptr, TrustIrTy::Ptr], vec![]),
        vec![TrustIrBlock {
            id: b(0),
            params: vec![
                (v(0), TrustIrTy::Ptr),
                (v(1), TrustIrTy::Ptr),
                (v(2), TrustIrTy::Ptr),
            ],
            body: vec![
                InstrNode::new(Inst::Load {
                    ty: vector_ty.clone(),
                    ptr: v(0),
                    align: None,
                    volatile: false,
                })
                .with_result(v(10)),
                InstrNode::new(Inst::Load {
                    ty: vector_ty.clone(),
                    ptr: v(1),
                    align: None,
                    volatile: false,
                })
                .with_result(v(11)),
                InstrNode::new(Inst::Const {
                    ty: mask_ty,
                    value: bool_mask_const_from_bits(lanes, true_bits),
                })
                .with_result(v(12)),
                InstrNode::new(Inst::Select {
                    ty: vector_ty.clone(),
                    cond: v(12),
                    then_val: v(10),
                    else_val: v(11),
                })
                .with_result(v(13)),
                InstrNode::new(Inst::Store {
                    ty: vector_ty,
                    ptr: v(2),
                    value: v(13),
                    align: None,
                    volatile: false,
                }),
                InstrNode::new(Inst::Return { values: vec![] }),
            ],
        }],
    )
}

fn build_chc_v4i32_pack_mask_extract_module(func_id: u32, name: &str) -> TrustIrModule {
    let vector_ty = v4i32_ty();
    single_function_module(
        func_id,
        name,
        func_ty(
            vec![
                TrustIrTy::I32,
                TrustIrTy::I32,
                TrustIrTy::I32,
                TrustIrTy::I32,
                TrustIrTy::Ptr,
            ],
            vec![TrustIrTy::I32],
        ),
        vec![TrustIrBlock {
            id: b(0),
            params: vec![
                (v(0), TrustIrTy::I32),
                (v(1), TrustIrTy::I32),
                (v(2), TrustIrTy::I32),
                (v(3), TrustIrTy::I32),
                (v(4), TrustIrTy::Ptr),
            ],
            body: vec![
                InstrNode::new(Inst::DialectOp(Box::new(
                    trust_ir::dialect::vector::pack_lanes(
                        vector_ty.clone(),
                        [v(0), v(1), v(2), v(3)],
                    ),
                )))
                .with_result(v(10)),
                InstrNode::new(Inst::Load {
                    ty: vector_ty.clone(),
                    ptr: v(4),
                    align: None,
                    volatile: false,
                })
                .with_result(v(11)),
                InstrNode::new(Inst::ICmp {
                    op: ICmpOp::Ne,
                    ty: vector_ty.clone(),
                    lhs: v(10),
                    rhs: v(11),
                })
                .with_result(v(12)),
                InstrNode::new(Inst::Const {
                    ty: vector_ty.clone(),
                    value: v4i32_mask_const(-1),
                })
                .with_result(v(13)),
                InstrNode::new(Inst::Const {
                    ty: vector_ty.clone(),
                    value: v4i32_mask_const(0),
                })
                .with_result(v(14)),
                InstrNode::new(Inst::Select {
                    ty: vector_ty.clone(),
                    cond: v(12),
                    then_val: v(13),
                    else_val: v(14),
                })
                .with_result(v(15)),
                InstrNode::new(Inst::DialectOp(Box::new(
                    trust_cg_lower::bitfield_dialect::v4i32_mask_extract(v(15)),
                )))
                .with_result(v(16)),
                InstrNode::new(Inst::Return {
                    values: vec![v(16)],
                }),
            ],
        }],
    )
}

fn build_sysv_v4i32_vector_arg_eq_mask_module(func_id: u32, name: &str) -> TrustIrModule {
    let vector_ty = v4i32_ty();
    single_function_module(
        func_id,
        name,
        func_ty(
            vec![vector_ty.clone(), vector_ty.clone()],
            vec![TrustIrTy::I32],
        ),
        vec![TrustIrBlock {
            id: b(0),
            params: vec![(v(0), vector_ty.clone()), (v(1), vector_ty.clone())],
            body: vec![
                InstrNode::new(Inst::ICmp {
                    op: ICmpOp::Eq,
                    ty: vector_ty.clone(),
                    lhs: v(0),
                    rhs: v(1),
                })
                .with_result(v(10)),
                InstrNode::new(Inst::Const {
                    ty: vector_ty.clone(),
                    value: v4i32_mask_const(-1),
                })
                .with_result(v(11)),
                InstrNode::new(Inst::Const {
                    ty: vector_ty.clone(),
                    value: v4i32_mask_const(0),
                })
                .with_result(v(12)),
                InstrNode::new(Inst::Select {
                    ty: vector_ty,
                    cond: v(10),
                    then_val: v(11),
                    else_val: v(12),
                })
                .with_result(v(13)),
                InstrNode::new(Inst::DialectOp(Box::new(
                    trust_cg_lower::bitfield_dialect::v4i32_mask_extract(v(13)),
                )))
                .with_result(v(14)),
                InstrNode::new(Inst::Return {
                    values: vec![v(14)],
                }),
            ],
        }],
    )
}

fn build_sysv_v2i64_vector_return_pack_module(func_id: u32, name: &str) -> TrustIrModule {
    let vector_ty = v2i64_ty();
    single_function_module(
        func_id,
        name,
        func_ty(
            vec![TrustIrTy::I64, TrustIrTy::I64],
            vec![vector_ty.clone()],
        ),
        vec![TrustIrBlock {
            id: b(0),
            params: vec![(v(0), TrustIrTy::I64), (v(1), TrustIrTy::I64)],
            body: vec![
                InstrNode::new(Inst::DialectOp(Box::new(
                    trust_ir::dialect::vector::pack_lanes(vector_ty, [v(0), v(1)]),
                )))
                .with_result(v(10)),
                InstrNode::new(Inst::Return {
                    values: vec![v(10)],
                }),
            ],
        }],
    )
}

fn build_sysv_v4i32_vector_stack_arg_add_module(func_id: u32, name: &str) -> TrustIrModule {
    let vector_ty = v4i32_ty();
    single_function_module(
        func_id,
        name,
        func_ty(vec![vector_ty.clone(); 9], vec![vector_ty.clone()]),
        vec![TrustIrBlock {
            id: b(0),
            params: (0..9).map(|idx| (v(idx), vector_ty.clone())).collect(),
            body: vec![
                InstrNode::new(Inst::BinOp {
                    op: BinOp::Add,
                    ty: vector_ty,
                    lhs: v(0),
                    rhs: v(8),
                })
                .with_result(v(20)),
                InstrNode::new(Inst::Return {
                    values: vec![v(20)],
                }),
            ],
        }],
    )
}

fn build_sysv_mixed_i32_v128_stack_arg_canary_module(func_id: u32, name: &str) -> TrustIrModule {
    let vector_ty = v4i32_ty();
    let mut params = vec![TrustIrTy::I32; 7];
    params.extend(std::iter::repeat_n(vector_ty.clone(), 9));
    params.push(TrustIrTy::I32);

    let mut block_params: Vec<_> = (0..7).map(|idx| (v(idx), TrustIrTy::I32)).collect();
    block_params.extend((7..16).map(|idx| (v(idx), vector_ty.clone())));
    block_params.push((v(16), TrustIrTy::I32));

    single_function_module(
        func_id,
        name,
        func_ty(params, vec![TrustIrTy::I32]),
        vec![TrustIrBlock {
            id: b(0),
            params: block_params,
            body: vec![
                InstrNode::new(Inst::BinOp {
                    op: BinOp::Add,
                    ty: vector_ty.clone(),
                    lhs: v(7),
                    rhs: v(15),
                })
                .with_result(v(30)),
                InstrNode::new(Inst::DialectOp(Box::new(
                    trust_ir::dialect::vector::extract_lane(vector_ty, v(30), 2),
                )))
                .with_result(v(31)),
                InstrNode::new(Inst::BinOp {
                    op: BinOp::Add,
                    ty: TrustIrTy::I32,
                    lhs: v(6),
                    rhs: v(16),
                })
                .with_result(v(32)),
                InstrNode::new(Inst::BinOp {
                    op: BinOp::Add,
                    ty: TrustIrTy::I32,
                    lhs: v(32),
                    rhs: v(31),
                })
                .with_result(v(33)),
                InstrNode::new(Inst::Return {
                    values: vec![v(33)],
                }),
            ],
        }],
    )
}

fn expected_i64_mask(op: ICmpOp, lhs: i64, rhs: i64) -> i64 {
    let matched = match op {
        ICmpOp::Eq => lhs == rhs,
        ICmpOp::Ne => lhs != rhs,
        ICmpOp::Slt => lhs < rhs,
        ICmpOp::Sle => lhs <= rhs,
        ICmpOp::Sgt => lhs > rhs,
        ICmpOp::Sge => lhs >= rhs,
        other => panic!("unexpected v2i64 boundary predicate {other:?}"),
    };
    if matched { -1 } else { 0 }
}

fn expected_i8_signed_mask(cond: IntCC, lhs: i8, rhs: i8) -> i8 {
    let matched = match cond {
        IntCC::SignedLessThan => lhs < rhs,
        IntCC::SignedLessThanOrEqual => lhs <= rhs,
        IntCC::SignedGreaterThan => lhs > rhs,
        IntCC::SignedGreaterThanOrEqual => lhs >= rhs,
        other => panic!("unexpected i8 signed comparison predicate {other:?}"),
    };
    if matched { -1 } else { 0 }
}

fn expected_i16_signed_mask(cond: IntCC, lhs: i16, rhs: i16) -> i16 {
    let matched = match cond {
        IntCC::SignedLessThan => lhs < rhs,
        IntCC::SignedLessThanOrEqual => lhs <= rhs,
        IntCC::SignedGreaterThan => lhs > rhs,
        IntCC::SignedGreaterThanOrEqual => lhs >= rhs,
        other => panic!("unexpected i16 signed comparison predicate {other:?}"),
    };
    if matched { -1 } else { 0 }
}

fn expected_i8_unsigned_mask(cond: IntCC, lhs: i8, rhs: i8) -> i8 {
    let lhs = lhs as u8;
    let rhs = rhs as u8;
    let matched = match cond {
        IntCC::UnsignedLessThan => lhs < rhs,
        IntCC::UnsignedLessThanOrEqual => lhs <= rhs,
        IntCC::UnsignedGreaterThan => lhs > rhs,
        IntCC::UnsignedGreaterThanOrEqual => lhs >= rhs,
        other => panic!("unexpected i8 unsigned comparison predicate {other:?}"),
    };
    if matched { -1 } else { 0 }
}

fn expected_i16_unsigned_mask(cond: IntCC, lhs: i16, rhs: i16) -> i16 {
    let lhs = lhs as u16;
    let rhs = rhs as u16;
    let matched = match cond {
        IntCC::UnsignedLessThan => lhs < rhs,
        IntCC::UnsignedLessThanOrEqual => lhs <= rhs,
        IntCC::UnsignedGreaterThan => lhs > rhs,
        IntCC::UnsignedGreaterThanOrEqual => lhs >= rhs,
        other => panic!("unexpected i16 unsigned comparison predicate {other:?}"),
    };
    if matched { -1 } else { 0 }
}

fn expected_v2i64_cmp_lane_bits(op: ICmpOp, lhs: [i64; 2], rhs: [i64; 2]) -> u32 {
    let lane0 = u32::from(expected_i64_mask(op, lhs[0], rhs[0]) != 0);
    let lane1 = u32::from(expected_i64_mask(op, lhs[1], rhs[1]) != 0);
    lane0 | (lane1 << 1)
}

fn expected_v4i32_ne_lane_bits(lhs: [i32; 4], rhs: [i32; 4]) -> u32 {
    lhs.into_iter().zip(rhs).enumerate().fold(
        0,
        |mask, (lane, (lhs, rhs))| {
            if lhs != rhs { mask | (1 << lane) } else { mask }
        },
    )
}

fn expected_v4i32_eq_lane_bits(lhs: [i32; 4], rhs: [i32; 4]) -> u32 {
    lhs.into_iter().zip(rhs).enumerate().fold(
        0,
        |mask, (lane, (lhs, rhs))| {
            if lhs == rhs { mask | (1 << lane) } else { mask }
        },
    )
}

fn i32_cmp_matches(op: ICmpOp, lhs: i32, rhs: i32) -> bool {
    match op {
        ICmpOp::Eq => lhs == rhs,
        ICmpOp::Ne => lhs != rhs,
        ICmpOp::Slt => lhs < rhs,
        ICmpOp::Sle => lhs <= rhs,
        ICmpOp::Sgt => lhs > rhs,
        ICmpOp::Sge => lhs >= rhs,
        other => panic!("unexpected v4i32 select predicate {other:?}"),
    }
}

fn expected_v4i32_select(
    op: ICmpOp,
    lhs: [i32; 4],
    rhs: [i32; 4],
    then_values: [i32; 4],
    else_values: [i32; 4],
) -> [i32; 4] {
    core::array::from_fn(|lane| {
        if i32_cmp_matches(op, lhs[lane], rhs[lane]) {
            then_values[lane]
        } else {
            else_values[lane]
        }
    })
}

fn expected_v2i64_select(
    op: ICmpOp,
    lhs: [i64; 2],
    rhs: [i64; 2],
    then_values: [i64; 2],
    else_values: [i64; 2],
) -> [i64; 2] {
    core::array::from_fn(|lane| {
        if expected_i64_mask(op, lhs[lane], rhs[lane]) != 0 {
            then_values[lane]
        } else {
            else_values[lane]
        }
    })
}

fn expected_v16i8_cmp_lane_bits(op: ICmpOp, lhs: [i8; 16], rhs: [i8; 16]) -> u32 {
    lhs.into_iter()
        .zip(rhs)
        .enumerate()
        .fold(0, |mask, (lane, (lhs, rhs))| {
            let matched = match op {
                ICmpOp::Eq => lhs == rhs,
                ICmpOp::Ne => lhs != rhs,
                other => panic!("unexpected v16i8 mask_to_bits predicate {other:?}"),
            };
            if matched { mask | (1 << lane) } else { mask }
        })
}

fn expected_v8i16_cmp_lane_bits(op: ICmpOp, lhs: [i16; 8], rhs: [i16; 8]) -> u32 {
    lhs.into_iter()
        .zip(rhs)
        .enumerate()
        .fold(0, |mask, (lane, (lhs, rhs))| {
            let matched = match op {
                ICmpOp::Eq => lhs == rhs,
                ICmpOp::Ne => lhs != rhs,
                other => panic!("unexpected v8i16 mask_to_bits predicate {other:?}"),
            };
            if matched { mask | (1 << lane) } else { mask }
        })
}

fn narrow_i8_cmp_matches(op: ICmpOp, lhs: i8, rhs: i8) -> bool {
    match op {
        ICmpOp::Eq => lhs == rhs,
        ICmpOp::Ne => lhs != rhs,
        ICmpOp::Slt => lhs < rhs,
        ICmpOp::Sle => lhs <= rhs,
        ICmpOp::Sgt => lhs > rhs,
        ICmpOp::Sge => lhs >= rhs,
        other => panic!("unexpected v16i8 select predicate {other:?}"),
    }
}

fn narrow_i16_cmp_matches(op: ICmpOp, lhs: i16, rhs: i16) -> bool {
    match op {
        ICmpOp::Eq => lhs == rhs,
        ICmpOp::Ne => lhs != rhs,
        ICmpOp::Slt => lhs < rhs,
        ICmpOp::Sle => lhs <= rhs,
        ICmpOp::Sgt => lhs > rhs,
        ICmpOp::Sge => lhs >= rhs,
        other => panic!("unexpected v8i16 select predicate {other:?}"),
    }
}

fn expected_v16i8_select(
    op: ICmpOp,
    lhs: [i8; 16],
    rhs: [i8; 16],
    then_values: [i8; 16],
    else_values: [i8; 16],
) -> [i8; 16] {
    core::array::from_fn(|lane| {
        if narrow_i8_cmp_matches(op, lhs[lane], rhs[lane]) {
            then_values[lane]
        } else {
            else_values[lane]
        }
    })
}

fn expected_v8i16_select(
    op: ICmpOp,
    lhs: [i16; 8],
    rhs: [i16; 8],
    then_values: [i16; 8],
    else_values: [i16; 8],
) -> [i16; 8] {
    core::array::from_fn(|lane| {
        if narrow_i16_cmp_matches(op, lhs[lane], rhs[lane]) {
            then_values[lane]
        } else {
            else_values[lane]
        }
    })
}

fn expected_v16i8_select_from_mask_bits(
    true_bits: u32,
    then_values: [i8; 16],
    else_values: [i8; 16],
) -> [i8; 16] {
    core::array::from_fn(|lane| {
        if (true_bits & (1_u32 << lane)) != 0 {
            then_values[lane]
        } else {
            else_values[lane]
        }
    })
}

fn expected_v8i16_select_from_mask_bits(
    true_bits: u32,
    then_values: [i16; 8],
    else_values: [i16; 8],
) -> [i16; 8] {
    core::array::from_fn(|lane| {
        if (true_bits & (1_u32 << lane)) != 0 {
            then_values[lane]
        } else {
            else_values[lane]
        }
    })
}

fn build_v128_i32_binop_store_function(name: &str, opcode: Opcode) -> LirFunction {
    let mut func = LirFunction::new(
        name,
        Signature {
            params: vec![Type::I64, Type::I64, Type::I64],
            returns: vec![],
        },
    );
    let entry = Block(0);
    func.entry_block = entry;
    func.block_order.push(entry);
    func.blocks.insert(
        entry,
        BasicBlock {
            params: vec![],
            instructions: vec![
                Instruction {
                    opcode: Opcode::Load {
                        ty: Type::V128,
                        align: None,
                    },
                    args: vec![Value(0)],
                    results: vec![Value(3)],
                },
                Instruction {
                    opcode: Opcode::Load {
                        ty: Type::V128,
                        align: None,
                    },
                    args: vec![Value(1)],
                    results: vec![Value(4)],
                },
                Instruction {
                    opcode,
                    args: vec![Value(3), Value(4)],
                    results: vec![Value(5)],
                },
                Instruction {
                    opcode: Opcode::Store {
                        ty: Type::V128,
                        align: None,
                    },
                    args: vec![Value(5), Value(2)],
                    results: vec![],
                },
                Instruction {
                    opcode: Opcode::Return,
                    args: vec![],
                    results: vec![],
                },
            ],
            source_locs: vec![],
        },
    );
    func
}

fn build_narrow_bitwise_store_module(
    func_id: u32,
    name: &str,
    vector_ty: TrustIrTy,
    op: BinOp,
) -> TrustIrModule {
    single_function_module(
        func_id,
        name,
        func_ty(vec![TrustIrTy::Ptr, TrustIrTy::Ptr, TrustIrTy::Ptr], vec![]),
        vec![TrustIrBlock {
            id: b(0),
            params: vec![
                (v(0), TrustIrTy::Ptr),
                (v(1), TrustIrTy::Ptr),
                (v(2), TrustIrTy::Ptr),
            ],
            body: vec![
                InstrNode::new(Inst::Load {
                    ty: vector_ty.clone(),
                    ptr: v(0),
                    align: None,
                    volatile: false,
                })
                .with_result(v(10)),
                InstrNode::new(Inst::Load {
                    ty: vector_ty.clone(),
                    ptr: v(1),
                    align: None,
                    volatile: false,
                })
                .with_result(v(11)),
                InstrNode::new(Inst::BinOp {
                    op,
                    ty: vector_ty.clone(),
                    lhs: v(10),
                    rhs: v(11),
                })
                .with_result(v(12)),
                InstrNode::new(Inst::Store {
                    ty: vector_ty,
                    ptr: v(2),
                    value: v(12),
                    align: None,
                    volatile: false,
                }),
                InstrNode::new(Inst::Return { values: vec![] }),
            ],
        }],
    )
}

fn build_v4i32_uniform_const_shift_module(
    func_id: u32,
    name: &str,
    op: BinOp,
    count: i128,
) -> TrustIrModule {
    let v4i32 = v4i32_ty();
    single_function_module(
        func_id,
        name,
        func_ty(vec![TrustIrTy::Ptr, TrustIrTy::Ptr], vec![]),
        vec![TrustIrBlock {
            id: b(0),
            params: vec![(v(0), TrustIrTy::Ptr), (v(1), TrustIrTy::Ptr)],
            body: vec![
                InstrNode::new(Inst::Load {
                    ty: v4i32.clone(),
                    ptr: v(0),
                    align: None,
                    volatile: false,
                })
                .with_result(v(10)),
                InstrNode::new(Inst::Const {
                    ty: TrustIrTy::I32,
                    value: Constant::Int(count),
                })
                .with_result(v(11)),
                InstrNode::new(Inst::DialectOp(Box::new(
                    trust_ir::dialect::vector::pack_lanes(
                        v4i32.clone(),
                        [v(11), v(11), v(11), v(11)],
                    ),
                )))
                .with_result(v(12)),
                InstrNode::new(Inst::BinOp {
                    op,
                    ty: v4i32.clone(),
                    lhs: v(10),
                    rhs: v(12),
                })
                .with_result(v(13)),
                InstrNode::new(Inst::Store {
                    ty: v4i32,
                    ptr: v(1),
                    value: v(13),
                    align: None,
                    volatile: false,
                }),
                InstrNode::new(Inst::Return { values: vec![] }),
            ],
        }],
    )
}

fn build_v2i64_binop_store_function(name: &str, opcode: Opcode) -> LirFunction {
    let mut func = LirFunction::new(
        name,
        Signature {
            params: vec![Type::I64, Type::I64, Type::I64],
            returns: vec![],
        },
    );
    let entry = Block(0);
    func.entry_block = entry;
    func.block_order.push(entry);
    func.blocks.insert(
        entry,
        BasicBlock {
            params: vec![],
            instructions: vec![
                Instruction {
                    opcode: Opcode::Load {
                        ty: Type::V128,
                        align: None,
                    },
                    args: vec![Value(0)],
                    results: vec![Value(3)],
                },
                Instruction {
                    opcode: Opcode::Load {
                        ty: Type::V128,
                        align: None,
                    },
                    args: vec![Value(1)],
                    results: vec![Value(4)],
                },
                Instruction {
                    opcode,
                    args: vec![Value(3), Value(4)],
                    results: vec![Value(5)],
                },
                Instruction {
                    opcode: Opcode::Store {
                        ty: Type::V128,
                        align: None,
                    },
                    args: vec![Value(5), Value(2)],
                    results: vec![],
                },
                Instruction {
                    opcode: Opcode::Return,
                    args: vec![],
                    results: vec![],
                },
            ],
            source_locs: vec![],
        },
    );
    func
}

// ---------------------------------------------------------------------------
// Test: return constant — the simplest JIT-executable smoke.
//
// Compiles `fn const42() -> i64 { 42 }`, mmap+mprotect-RX, invokes it,
// asserts the return value.
// ---------------------------------------------------------------------------

#[test]
fn test_x86_64_jit_const42() {
    let func = build_x86_const_test_function();
    let code = compile_leaf(&func);

    assert!(
        !code.is_empty(),
        "x86-64 compile_function should produce nonempty code bytes"
    );

    let page = ExecPage::new(&code);

    // SAFETY: `page.as_ptr()` points at an RX page containing an x86-64
    // leaf function matching the System V AMD64 ABI `extern "C" fn() -> i64`
    // signature produced by `build_x86_const_test_function`. The `ExecPage`
    // outlives the call.
    let f: extern "C" fn() -> i64 = unsafe { core::mem::transmute(page.as_ptr()) };

    assert_eq!(f(), 42);
}

// ---------------------------------------------------------------------------
// Test: two-argument add — exercises the two-address fixup path.
//
// Compiles `fn add(a: i64, b: i64) -> i64 { a + b }`. The ISel emits
// three-address `ADD v2, v0, v1` and the pipeline's `fixup_two_address`
// pass (between regalloc and prologue/epilogue) inserts a `MOV` to match
// x86-64's two-address `ADD dst, src` form. Without that pass the
// returned value would be wrong — this smoke test therefore also
// indirectly exercises #305's fix.
// ---------------------------------------------------------------------------

#[test]
fn test_x86_64_jit_add() {
    let func = build_x86_add_test_function();
    let code = compile_leaf(&func);

    assert!(
        !code.is_empty(),
        "x86-64 add should compile to nonempty bytes"
    );

    let page = ExecPage::new(&code);

    // SAFETY: see `test_x86_64_jit_const42`. System V AMD64 passes first
    // two i64 args in RDI/RSI; `build_x86_add_test_function` is built
    // against that ABI.
    let f: extern "C" fn(i64, i64) -> i64 = unsafe { core::mem::transmute(page.as_ptr()) };

    assert_eq!(f(3, 4), 7);
    assert_eq!(f(0, 0), 0);
    assert_eq!(f(-1, 1), 0);
    assert_eq!(f(100, 200), 300);
    assert_eq!(f(i64::MAX, 0), i64::MAX);
    assert_eq!(f(-100, -200), -300);
}

#[test]
fn test_x86_64_jit_v128_bnot_flips_all_i32_lanes() {
    let mut func = LirFunction::new(
        "v128_bnot_flips_all_i32_lanes",
        Signature {
            params: vec![Type::I64, Type::I64],
            returns: vec![],
        },
    );
    let entry = Block(0);
    func.entry_block = entry;
    func.block_order.push(entry);
    func.blocks.insert(
        entry,
        BasicBlock {
            params: vec![],
            instructions: vec![
                Instruction {
                    opcode: Opcode::Load {
                        ty: Type::V128,
                        align: None,
                    },
                    args: vec![Value(0)],
                    results: vec![Value(2)],
                },
                Instruction {
                    opcode: Opcode::Bnot,
                    args: vec![Value(2)],
                    results: vec![Value(3)],
                },
                Instruction {
                    opcode: Opcode::Store {
                        ty: Type::V128,
                        align: None,
                    },
                    args: vec![Value(3), Value(1)],
                    results: vec![],
                },
                Instruction {
                    opcode: Opcode::Return,
                    args: vec![],
                    results: vec![],
                },
            ],
            source_locs: vec![],
        },
    );

    let code = compile_lir_leaf(&func);
    assert!(!code.is_empty(), "V128 Bnot function must compile");

    let page = ExecPage::new(&code);
    // SAFETY: `page` contains a leaf System V function taking two pointer-sized
    // integer arguments and returning void. The mapping outlives the call.
    let f: extern "C" fn(*const i32, *mut i32) = unsafe { core::mem::transmute(page.as_ptr()) };

    let input = [0i32, -1, 0, 0];
    let mut output = [0i32; 4];
    f(input.as_ptr(), output.as_mut_ptr());

    assert_eq!(output, [-1, 0, -1, -1]);
}

#[test]
fn test_x86_64_jit_v2i64_signed_icmp_boundary_masks() {
    let predicates = [
        ("eq", ICmpOp::Eq),
        ("ne", ICmpOp::Ne),
        ("slt", ICmpOp::Slt),
        ("sle", ICmpOp::Sle),
        ("sgt", ICmpOp::Sgt),
        ("sge", ICmpOp::Sge),
    ];
    let cases = [
        ([i64::MIN, i64::MAX], [i64::MAX, i64::MIN]),
        ([i64::MIN, -1], [i64::MIN, 0]),
        ([-1, 0], [0, -1]),
        ([0, 1], [0, -1]),
        ([1, i64::MAX], [0, i64::MAX]),
    ];

    for (index, (suffix, op)) in predicates.into_iter().enumerate() {
        let name = format!("v2i64_{}_boundary_masks", suffix);
        let module = build_v2i64_cmp_mask_module(8800 + index as u32, &name, op);
        let result = host_jit_o0_compiler()
            .compile_module_to_jit(&module, &HashMap::new())
            .unwrap_or_else(|err| panic!("x86-64 host JIT should compile {name}: {err}"));
        let metrics = result
            .per_function_metrics
            .iter()
            .find(|metrics| metrics.name == name)
            .unwrap_or_else(|| panic!("{name} per-function metrics should be present"));
        assert!(
            metrics.code_size_bytes > 0,
            "{name} should report per-symbol code size"
        );
        assert!(
            metrics.x86_machine_code.pcmpeqd_count >= 1,
            "{name} should report all-ones qword mask materialization evidence: {:?}",
            metrics.x86_machine_code
        );
        assert_eq!(
            metrics.x86_machine_code.pinsrq_count, 0,
            "{name} should not rebuild canonical v2i64 mask lanes with PINSRQ: {:?}",
            metrics.x86_machine_code
        );

        let run: extern "C" fn(*const i64, *const i64, *mut i64) = unsafe {
            result
                .buffer
                .get_fn_bound(&name)
                .unwrap_or_else(|| panic!("{name} symbol must be present"))
                .into_inner()
        };

        for (lhs, rhs) in cases {
            let mut output = [123i64, 456i64];
            run(lhs.as_ptr(), rhs.as_ptr(), output.as_mut_ptr());

            assert_eq!(
                output,
                [
                    expected_i64_mask(op, lhs[0], rhs[0]),
                    expected_i64_mask(op, lhs[1], rhs[1]),
                ],
                "{name} lhs={lhs:?} rhs={rhs:?} must return exact i64 mask lanes"
            );
        }
    }
}

#[test]
fn test_x86_64_jit_v4i32_ne_mask_extract_semantics_and_direct_sse_evidence() {
    let name = "v4i32_ne_mask_extract_direct_sse";
    let module = build_v4i32_ne_mask_extract_return_module(8790, name);
    let result = host_jit_o0_compiler()
        .compile_module_to_jit(&module, &HashMap::new())
        .unwrap_or_else(|err| panic!("x86-64 host JIT should compile {name}: {err}"));

    assert_metrics_code_size_matches_replay(&result, name);
    let metrics = metrics_for(&result, name);
    assert_eq!(
        metrics.x86_machine_code.pmovmskb_count, 1,
        "{name} should pack the v4i32 mask with one PMOVMSKB: {:?}",
        metrics.x86_machine_code
    );
    assert!(
        metrics.x86_machine_code.pcmpeqd_count >= 2,
        "{name} should use packed PCMPEQD for compare plus mask inversion: {:?}",
        metrics.x86_machine_code
    );
    assert_eq!(
        metrics.x86_machine_code.pinsrd_count, 0,
        "{name} should not scalarize mask lanes through PINSRD: {:?}",
        metrics.x86_machine_code
    );
    assert_eq!(
        metrics.x86_machine_code.pextrd_count, 0,
        "{name} should not scalarize mask lanes through PEXTRD: {:?}",
        metrics.x86_machine_code
    );

    let run: extern "C" fn(*const i32, *const i32) -> u32 = unsafe {
        result
            .buffer
            .get_fn_bound(name)
            .unwrap_or_else(|| panic!("{name} symbol must be present"))
            .into_inner()
    };

    for (lhs, rhs) in [
        ([0, 0, 0, 0], [0, 0, 0, 0]),
        ([1, 2, 3, 4], [0, 2, 0, 4]),
        ([1, -2, 3, -4], [1, 0, 3, 0]),
        ([i32::MIN, -1, 0, i32::MAX], [0, -1, 1, i32::MAX]),
        ([9, 8, 7, 6], [0, 0, 0, 0]),
    ] {
        let actual = run(lhs.as_ptr(), rhs.as_ptr());
        let expected = expected_v4i32_ne_lane_bits(lhs, rhs);
        assert_eq!(
            actual, expected,
            "{name} lhs={lhs:?} rhs={rhs:?} must return bitN for laneN NotEqual"
        );
    }
}

#[test]
fn test_x86_64_jit_chc_v4i32_pack_mask_extract_exposes_code_size_and_simd_counts() {
    let name = "chc_v4i32_pack_mask_extract_evidence";
    let module = build_chc_v4i32_pack_mask_extract_module(8791, name);
    let result = host_jit_o0_compiler()
        .compile_module_to_jit(&module, &HashMap::new())
        .unwrap_or_else(|err| panic!("x86-64 host JIT should compile {name}: {err}"));

    assert_metrics_code_size_matches_replay(&result, name);
    assert_eq!(
        result.metrics.code_size_bytes,
        metrics_for(&result, name).code_size_bytes,
        "{name} is a single-function module, so aggregate code size should match per-symbol bytes"
    );

    let metrics = metrics_for(&result, name);
    eprintln!(
        "x86 CHC v4i32 pack/mask metrics: code_size={}, movd_to_xmm={}, punpckldq={}, punpcklqdq={}, pinsrd={}, pblendvb={}, pmovmskb={}, pcmpeqd={}",
        metrics.code_size_bytes,
        metrics.x86_machine_code.movd_to_xmm_count,
        metrics.x86_machine_code.punpckldq_count,
        metrics.x86_machine_code.punpcklqdq_count,
        metrics.x86_machine_code.pinsrd_count,
        metrics.x86_machine_code.pblendvb_count,
        metrics.x86_machine_code.pmovmskb_count,
        metrics.x86_machine_code.pcmpeqd_count
    );
    assert_eq!(
        metrics.x86_machine_code.movd_to_xmm_count, 4,
        "{name} should seed each distinct i32 lane with MOVD-to-XMM: {:?}",
        metrics.x86_machine_code
    );
    assert_eq!(
        metrics.x86_machine_code.punpckldq_count, 2,
        "{name} should build two ordered dword lane pairs with PUNPCKLDQ: {:?}",
        metrics.x86_machine_code
    );
    assert_eq!(
        metrics.x86_machine_code.punpcklqdq_count, 1,
        "{name} should join ordered lane pairs with PUNPCKLQDQ: {:?}",
        metrics.x86_machine_code
    );
    assert_eq!(
        metrics.x86_machine_code.pinsrd_count, 0,
        "{name} should avoid SSE4.1 PINSRD in the distinct-lane pack: {:?}",
        metrics.x86_machine_code
    );
    assert_eq!(
        metrics.x86_machine_code.pblendvb_count, 0,
        "{name} should fold canonical mask selection instead of relying on SSE4.1 PBLENDVB: {:?}",
        metrics.x86_machine_code
    );
    assert!(
        metrics.code_size_bytes <= 100,
        "{name} should keep the SSE2 pack/mask path close to the 91-byte PINSRD baseline by folding canonical mask selection: {}",
        metrics.code_size_bytes
    );
    assert_eq!(
        metrics.x86_machine_code.pmovmskb_count, 1,
        "{name} should compact the mask with one PMOVMSKB: {:?}",
        metrics.x86_machine_code
    );
    assert!(
        metrics.x86_machine_code.pcmpeqd_count >= 2,
        "{name} should use packed compares for NE plus canonical mask selection: {:?}",
        metrics.x86_machine_code
    );
    assert_eq!(
        metrics.x86_machine_code.pextrd_count, 0,
        "{name} should not scalarize mask extraction with PEXTRD: {:?}",
        metrics.x86_machine_code
    );
    assert!(
        metrics.x86_machine_code.total_tracked_opcodes() >= 7,
        "{name} should expose the full pack/mask SIMD opcode surface: {:?}",
        metrics.x86_machine_code
    );

    let run: extern "C" fn(i32, i32, i32, i32, *const i32) -> u32 = unsafe {
        result
            .buffer
            .get_fn_bound(name)
            .unwrap_or_else(|| panic!("{name} symbol must be present"))
            .into_inner()
    };

    for (lhs, rhs) in [
        ([0, 0, 0, 0], [0, 0, 0, 0]),
        ([1, 2, 3, 4], [1, 0, 3, 0]),
        ([i32::MIN, -1, 0, i32::MAX], [0, -1, 1, i32::MAX]),
        ([9, 8, 7, 6], [0, 0, 0, 0]),
    ] {
        let actual = run(lhs[0], lhs[1], lhs[2], lhs[3], rhs.as_ptr());
        let expected = expected_v4i32_ne_lane_bits(lhs, rhs);
        assert_eq!(
            actual, expected,
            "{name} lhs={lhs:?} rhs={rhs:?} must return bitN for packed laneN NotEqual"
        );
    }
}

#[test]
fn test_x86_64_jit_sysv_v4i32_vector_args_arrive_in_xmm_registers() {
    let name = "sysv_v4i32_vector_arg_eq_mask";
    let module = build_sysv_v4i32_vector_arg_eq_mask_module(8890, name);
    let result = host_jit_o0_compiler()
        .compile_module_to_jit(&module, &HashMap::new())
        .unwrap_or_else(|err| panic!("x86-64 host JIT should compile {name}: {err}"));

    assert_metrics_code_size_matches_replay(&result, name);
    let metrics = metrics_for(&result, name);
    eprintln!(
        "x86 SysV V128 arg metrics: code_size={}, movdqa={}, movdqu_load={}, movdqu_store={}, pcmpeqd={}, pmovmskb={}, spill_slots={}",
        metrics.code_size_bytes,
        metrics.x86_machine_code.movdqa_count,
        metrics.x86_machine_code.movdqu_load_count,
        metrics.x86_machine_code.movdqu_store_count,
        metrics.x86_machine_code.pcmpeqd_count,
        metrics.x86_machine_code.pmovmskb_count,
        metrics.spill_slot_count
    );
    assert!(
        metrics.x86_machine_code.movdqa_count >= 1,
        "{name} should expose XMM formal preservation copies: {:?}",
        metrics.x86_machine_code
    );
    assert_eq!(
        metrics.x86_machine_code.movdqu_load_count, 0,
        "{name} should not materialize vector formals through stack-local loads: {:?}",
        metrics.x86_machine_code
    );
    assert_eq!(
        metrics.x86_machine_code.movdqu_store_count, 0,
        "{name} should not materialize vector formals through stack-local stores: {:?}",
        metrics.x86_machine_code
    );
    assert_eq!(
        metrics.spill_slot_count, 0,
        "{name} should not require spill slots for two incoming V128 arguments"
    );
    assert_eq!(
        metrics.x86_machine_code.pcmpeqd_count, 1,
        "{name} should compare vector argument lanes with one PCMPEQD: {:?}",
        metrics.x86_machine_code
    );
    assert_eq!(
        metrics.x86_machine_code.pmovmskb_count, 1,
        "{name} should compact the vector compare mask with one PMOVMSKB: {:?}",
        metrics.x86_machine_code
    );

    #[allow(improper_ctypes_definitions)]
    type Run = extern "C" fn(__m128i, __m128i) -> u32;
    let run: Run = unsafe {
        result
            .buffer
            .get_fn_bound(name)
            .unwrap_or_else(|| panic!("{name} symbol must be present"))
            .into_inner()
    };

    for (lhs, rhs) in [
        ([0, 0, 0, 0], [0, 0, 0, 0]),
        ([1, 2, 3, 4], [1, 0, 3, 0]),
        ([i32::MIN, -1, 0, i32::MAX], [0, -1, 1, i32::MAX]),
        ([9, 8, 7, 6], [0, 0, 0, 0]),
    ] {
        let actual = run(m128i_from_i32x4(lhs), m128i_from_i32x4(rhs));
        let expected = expected_v4i32_eq_lane_bits(lhs, rhs);
        assert_eq!(
            actual, expected,
            "{name} lhs={lhs:?} rhs={rhs:?} must return bitN for vector arg laneN equality"
        );
    }
}

#[test]
fn test_x86_64_jit_sysv_v4i32_ninth_vector_arg_arrives_from_aligned_stack_slot() {
    let name = "sysv_v4i32_ninth_vector_stack_arg_add";
    let module = build_sysv_v4i32_vector_stack_arg_add_module(8892, name);
    let lir_func = single_translated_lir_function(&module);
    let raw_code = compile_lir_host_jit_o0_raw(&lir_func);
    assert!(
        contains_rbp_disp8_movdqa_load(&raw_code, 16),
        "{name} should load the ninth V128 formal from the first 16-byte-aligned SysV stack slot at [rbp+16], code={raw_code:02X?}"
    );
    assert!(
        !contains_rbp_relative_local_lea(&raw_code),
        "{name} should not materialize stack-local adapter storage, code={raw_code:02X?}"
    );

    let result = host_jit_o0_compiler()
        .compile_module_to_jit(&module, &HashMap::new())
        .unwrap_or_else(|err| panic!("x86-64 host JIT should compile {name}: {err}"));

    assert_metrics_code_size_matches_replay(&result, name);
    let metrics = metrics_for(&result, name);
    eprintln!(
        "x86 SysV V128 stack arg metrics: code_size={}, movdqa={}, movdqu_load={}, movdqu_store={}, paddd={}, spill_slots={}",
        metrics.code_size_bytes,
        metrics.x86_machine_code.movdqa_count,
        metrics.x86_machine_code.movdqu_load_count,
        metrics.x86_machine_code.movdqu_store_count,
        metrics.x86_machine_code.paddd_count,
        metrics.spill_slot_count
    );
    assert!(
        metrics.x86_machine_code.movdqa_count >= 9,
        "{name} should expose eight XMM formal copies plus one aligned V128 stack-formal load: {:?}",
        metrics.x86_machine_code
    );
    assert_eq!(
        metrics.x86_machine_code.movdqu_load_count, 0,
        "{name} should not use unaligned MOVDQU loads for an ABI-aligned V128 stack formal: {:?}",
        metrics.x86_machine_code
    );
    assert_eq!(
        metrics.x86_machine_code.movdqu_store_count, 0,
        "{name} should not use stack-local MOVDQU stores for V128 formals: {:?}",
        metrics.x86_machine_code
    );
    assert_eq!(
        metrics.spill_slot_count, 0,
        "{name} should not require spill slots for this V128 stack-argument canary"
    );
    assert_eq!(
        metrics.x86_machine_code.paddd_count, 1,
        "{name} should execute the vector add through one PADDD: {:?}",
        metrics.x86_machine_code
    );

    #[allow(improper_ctypes_definitions)]
    type Run = extern "C" fn(
        __m128i,
        __m128i,
        __m128i,
        __m128i,
        __m128i,
        __m128i,
        __m128i,
        __m128i,
        __m128i,
    ) -> __m128i;
    let run: Run = unsafe {
        result
            .buffer
            .get_fn_bound(name)
            .unwrap_or_else(|| panic!("{name} symbol must be present"))
            .into_inner()
    };

    let first = [1i32, -2, i32::MAX, i32::MIN];
    let ninth = [10i32, -20, 1, -1];
    let filler = [
        [101, 102, 103, 104],
        [201, 202, 203, 204],
        [301, 302, 303, 304],
        [401, 402, 403, 404],
        [501, 502, 503, 504],
        [601, 602, 603, 604],
        [701, 702, 703, 704],
    ];
    let actual = i32x4_from_m128i(run(
        m128i_from_i32x4(first),
        m128i_from_i32x4(filler[0]),
        m128i_from_i32x4(filler[1]),
        m128i_from_i32x4(filler[2]),
        m128i_from_i32x4(filler[3]),
        m128i_from_i32x4(filler[4]),
        m128i_from_i32x4(filler[5]),
        m128i_from_i32x4(filler[6]),
        m128i_from_i32x4(ninth),
    ));
    let expected = core::array::from_fn(|lane| first[lane].wrapping_add(ninth[lane]));
    assert_eq!(
        actual, expected,
        "{name} must add the register V128 arg to the ninth stack-passed V128 arg lane-wise"
    );
}

#[test]
fn test_x86_64_jit_sysv_v128_mixed_scalar_stack_arg_canary() {
    let name = "sysv_mixed_i32_v128_stack_arg_canary";
    let module = build_sysv_mixed_i32_v128_stack_arg_canary_module(8893, name);
    let lir_func = single_translated_lir_function(&module);
    let raw_code = compile_lir_host_jit_o0_raw(&lir_func);
    assert!(
        contains_rbp_disp8_i32_load(&raw_code, 16),
        "{name} should load the seventh i32 formal from [rbp+16], immediately before the aligned V128 stack slot, code={raw_code:02X?}"
    );
    assert!(
        contains_rbp_disp8_movdqa_load(&raw_code, 32),
        "{name} should align the ninth V128 formal to [rbp+32] after the preceding stack i32 slot, code={raw_code:02X?}"
    );
    assert!(
        contains_rbp_disp8_i32_load(&raw_code, 48),
        "{name} should load the following i32 formal from [rbp+48], immediately after the V128 stack slot, code={raw_code:02X?}"
    );
    assert!(
        !contains_rbp_relative_local_lea(&raw_code),
        "{name} should not materialize stack-local adapter storage, code={raw_code:02X?}"
    );

    let result = host_jit_o0_compiler()
        .compile_module_to_jit(&module, &HashMap::new())
        .unwrap_or_else(|err| panic!("x86-64 host JIT should compile {name}: {err}"));

    assert_metrics_code_size_matches_replay(&result, name);
    let metrics = metrics_for(&result, name);
    eprintln!(
        "x86 SysV mixed scalar/V128 stack arg metrics: code_size={}, movdqa={}, movdqu_load={}, movdqu_store={}, paddd={}, spill_slots={}",
        metrics.code_size_bytes,
        metrics.x86_machine_code.movdqa_count,
        metrics.x86_machine_code.movdqu_load_count,
        metrics.x86_machine_code.movdqu_store_count,
        metrics.x86_machine_code.paddd_count,
        metrics.spill_slot_count
    );
    assert!(
        metrics.x86_machine_code.movdqa_count >= 9,
        "{name} should expose independent XMM assignment plus one aligned V128 stack-formal load: {:?}",
        metrics.x86_machine_code
    );
    assert_eq!(
        metrics.x86_machine_code.movdqu_load_count, 0,
        "{name} should not use unaligned MOVDQU loads for V128 ABI formals: {:?}",
        metrics.x86_machine_code
    );
    assert_eq!(
        metrics.x86_machine_code.movdqu_store_count, 0,
        "{name} should not use stack-local MOVDQU stores for V128 ABI formals: {:?}",
        metrics.x86_machine_code
    );
    assert_eq!(
        metrics.spill_slot_count, 0,
        "{name} should not require spill slots for mixed scalar/vector ABI canary"
    );
    assert_eq!(
        metrics.x86_machine_code.paddd_count, 1,
        "{name} should execute the vector lane contribution through one PADDD: {:?}",
        metrics.x86_machine_code
    );

    #[allow(improper_ctypes_definitions)]
    type Run = extern "C" fn(
        i32,
        i32,
        i32,
        i32,
        i32,
        i32,
        i32,
        __m128i,
        __m128i,
        __m128i,
        __m128i,
        __m128i,
        __m128i,
        __m128i,
        __m128i,
        __m128i,
        i32,
    ) -> i32;
    let run: Run = unsafe {
        result
            .buffer
            .get_fn_bound(name)
            .unwrap_or_else(|| panic!("{name} symbol must be present"))
            .into_inner()
    };

    let reg_vector = [11i32, 22, 33, 44];
    let stack_vector = [100i32, 200, 300, 400];
    let filler = [
        [1001, 1002, 1003, 1004],
        [2001, 2002, 2003, 2004],
        [3001, 3002, 3003, 3004],
        [4001, 4002, 4003, 4004],
        [5001, 5002, 5003, 5004],
        [6001, 6002, 6003, 6004],
        [7001, 7002, 7003, 7004],
    ];
    let stack_i32_before = 70i32;
    let stack_i32_after = -900i32;
    let actual = run(
        10,
        20,
        30,
        40,
        50,
        60,
        stack_i32_before,
        m128i_from_i32x4(reg_vector),
        m128i_from_i32x4(filler[0]),
        m128i_from_i32x4(filler[1]),
        m128i_from_i32x4(filler[2]),
        m128i_from_i32x4(filler[3]),
        m128i_from_i32x4(filler[4]),
        m128i_from_i32x4(filler[5]),
        m128i_from_i32x4(filler[6]),
        m128i_from_i32x4(stack_vector),
        stack_i32_after,
    );
    let expected = stack_i32_before
        .wrapping_add(stack_i32_after)
        .wrapping_add(reg_vector[2].wrapping_add(stack_vector[2]));
    assert_eq!(
        actual, expected,
        "{name} should preserve adjacent stack i32 formals while using independent XMM assignment and the aligned V128 stack formal"
    );
}

#[test]
fn test_x86_64_jit_sysv_v2i64_vector_return_leaves_xmm0() {
    let name = "sysv_v2i64_vector_return_pack";
    let module = build_sysv_v2i64_vector_return_pack_module(8891, name);
    let result = host_jit_o0_compiler()
        .compile_module_to_jit(&module, &HashMap::new())
        .unwrap_or_else(|err| panic!("x86-64 host JIT should compile {name}: {err}"));

    assert_metrics_code_size_matches_replay(&result, name);
    let metrics = metrics_for(&result, name);
    eprintln!(
        "x86 SysV V128 return metrics: code_size={}, movdqa={}, movdqu_load={}, movdqu_store={}, movq_to_xmm={}, punpcklqdq={}, spill_slots={}",
        metrics.code_size_bytes,
        metrics.x86_machine_code.movdqa_count,
        metrics.x86_machine_code.movdqu_load_count,
        metrics.x86_machine_code.movdqu_store_count,
        metrics.x86_machine_code.movq_to_xmm_count,
        metrics.x86_machine_code.punpcklqdq_count,
        metrics.spill_slot_count
    );
    assert_eq!(
        metrics.x86_machine_code.movdqu_load_count, 0,
        "{name} should not use a stack-local adapter load for the vector return: {:?}",
        metrics.x86_machine_code
    );
    assert_eq!(
        metrics.x86_machine_code.movdqu_store_count, 0,
        "{name} should not use a stack-local adapter store for the vector return: {:?}",
        metrics.x86_machine_code
    );
    assert_eq!(
        metrics.spill_slot_count, 0,
        "{name} should not require spill slots for a packed V128 return"
    );
    assert_eq!(
        metrics.x86_machine_code.movq_to_xmm_count, 2,
        "{name} should seed both i64 lanes through MOVQ-to-XMM: {:?}",
        metrics.x86_machine_code
    );
    assert_eq!(
        metrics.x86_machine_code.punpcklqdq_count, 1,
        "{name} should combine the two qword lanes with PUNPCKLQDQ: {:?}",
        metrics.x86_machine_code
    );

    #[allow(improper_ctypes_definitions)]
    type Run = extern "C" fn(i64, i64) -> __m128i;
    let run: Run = unsafe {
        result
            .buffer
            .get_fn_bound(name)
            .unwrap_or_else(|| panic!("{name} symbol must be present"))
            .into_inner()
    };

    for lanes in [
        [0i64, 0i64],
        [1, -1],
        [i64::MIN, i64::MAX],
        [0x1122_3344_5566_7788i64, -0x0102_0304_0506_0708i64],
    ] {
        let actual = i64x2_from_m128i(run(lanes[0], lanes[1]));
        assert_eq!(
            actual, lanes,
            "{name} should return both scalar lanes through XMM0"
        );
    }
}

#[test]
fn test_x86_64_jit_v2i64_bool_mask_extract_i32_semantics_and_lane_order() {
    let predicates = [
        ("eq", ICmpOp::Eq),
        ("ne", ICmpOp::Ne),
        ("slt", ICmpOp::Slt),
        ("sle", ICmpOp::Sle),
        ("sgt", ICmpOp::Sgt),
        ("sge", ICmpOp::Sge),
    ];
    let cases = [
        ([0, 0], [0, 0]),
        ([0, 1], [0, 0]),
        ([0, 0], [1, 0]),
        ([1, 0], [0, 1]),
        ([0, 0], [1, 1]),
        ([1, 1], [0, 0]),
    ];

    for (index, (suffix, op)) in predicates.into_iter().enumerate() {
        let name = format!("v2i64_bool_mask_extract_{suffix}_i32");
        let module = build_v2i64_cmp_bool_extract_return_module(
            8830 + index as u32,
            &name,
            op,
            TrustIrTy::I32,
        );
        let result = host_jit_o0_compiler()
            .compile_module_to_jit(&module, &HashMap::new())
            .unwrap_or_else(|err| panic!("x86-64 host JIT should compile {name}: {err}"));
        assert_metrics_code_size_matches_replay(&result, &name);
        let metrics = metrics_for(&result, &name);
        assert_eq!(
            metrics.x86_machine_code.pmovmskb_count, 1,
            "{name} should use the direct PMOVMSKB mask extraction path: {:?}",
            metrics.x86_machine_code
        );
        assert_eq!(
            metrics.x86_machine_code.pinsrq_count, 0,
            "{name} should not materialize select(-1,0) lanes before extraction: {:?}",
            metrics.x86_machine_code
        );

        let run: extern "C" fn(*const i64, *const i64) -> u32 = unsafe {
            result
                .buffer
                .get_fn_bound(&name)
                .unwrap_or_else(|| panic!("{name} symbol must be present"))
                .into_inner()
        };

        let mut seen_masks = [false; 4];
        for (lhs, rhs) in cases {
            let expected = expected_v2i64_cmp_lane_bits(op, lhs, rhs);
            let actual = run(lhs.as_ptr(), rhs.as_ptr());
            assert_eq!(
                actual, expected,
                "{name} lhs={lhs:?} rhs={rhs:?} must return bit0=lane0, bit1=lane1"
            );
            seen_masks[actual as usize] = true;
        }

        assert_eq!(
            seen_masks, [true; 4],
            "{name} cases should cover all four lane-bit masks"
        );
    }
}

#[test]
fn test_x86_64_jit_v2i64_bool_mask_extract_i64_zero_extends_high_bits() {
    let name = "v2i64_bool_mask_extract_eq_i64";
    let module = build_v2i64_cmp_bool_extract_return_module(8840, name, ICmpOp::Eq, TrustIrTy::I64);
    let result = host_jit_o0_compiler()
        .compile_module_to_jit(&module, &HashMap::new())
        .unwrap_or_else(|err| panic!("x86-64 host JIT should compile {name}: {err}"));
    assert_metrics_code_size_matches_replay(&result, name);
    let metrics = metrics_for(&result, name);
    assert_eq!(
        metrics.x86_machine_code.pmovmskb_count, 1,
        "{name} should use the direct PMOVMSKB mask extraction path: {:?}",
        metrics.x86_machine_code
    );

    let run: extern "C" fn(*const i64, *const i64) -> u64 = unsafe {
        result
            .buffer
            .get_fn_bound(name)
            .unwrap_or_else(|| panic!("{name} symbol must be present"))
            .into_inner()
    };

    for (lhs, rhs) in [
        ([0, 1], [2, 3]), // 0b00
        ([7, 1], [7, 3]), // 0b01
        ([0, 9], [2, 9]), // 0b10
        ([4, 5], [4, 5]), // 0b11
    ] {
        let expected = u64::from(expected_v2i64_cmp_lane_bits(ICmpOp::Eq, lhs, rhs));
        let actual = run(lhs.as_ptr(), rhs.as_ptr());
        assert_eq!(
            actual, expected,
            "{name} lhs={lhs:?} rhs={rhs:?} must zero-extend i64 result high bits"
        );
        assert_eq!(
            actual & !0x3,
            0,
            "{name} must keep all bits above lane mask bits zero"
        );
    }
}

#[test]
fn test_x86_64_jit_v2i64_compare_code_size_no_local_frame_matches_raw_pipeline() {
    let name = "v2i64_slt_code_size_helper";
    let module = build_v2i64_cmp_pointer_select_module(8810, name, ICmpOp::Slt);
    let lir_func = single_translated_lir_function(&module);
    let raw_code = compile_lir_host_jit_o0_raw(&lir_func);

    // Both the raw pipeline and the public JIT now emit the same 41-byte
    // PCMPGTQ+PTEST+CMOV select with a single MOVDQA staging copy; the prior
    // 44-byte golden predated the redundant-move cleanup in the x86 pipeline.
    // The point of this test is that the two paths agree (asserted below), and
    // they do: raw == public == 41 bytes.
    assert_eq!(
        raw_code.len(),
        41,
        "native v2i64 compare helper code size changed, code={raw_code:02X?}"
    );
    assert!(
        contains_sse41_0f38_opcode(&raw_code, 0x37),
        "native v2i64 signed less-than should encode PCMPGTQ, code={raw_code:02X?}"
    );
    assert!(
        !contains_rbp_relative_local_lea(&raw_code),
        "native v2i64 compare helper should not materialize an RBP-relative local temp frame, code={raw_code:02X?}"
    );

    let result = host_jit_o0_compiler()
        .compile_module_to_jit(&module, &HashMap::new())
        .expect("public x86-64 host JIT should compile native v2i64 compare helper");
    let run: extern "C" fn(*const i64, *const i64) -> *const i64 = unsafe {
        result
            .buffer
            .get_fn_bound(name)
            .unwrap_or_else(|| panic!("{name} symbol must be present"))
            .into_inner()
    };
    let lhs_selected = [0i64, 9i64];
    let rhs_selected = [1i64, -3i64];
    let lhs_not_selected = [2i64, 9i64];
    let rhs_not_selected = [1i64, 7i64];
    assert_eq!(
        run(lhs_selected.as_ptr(), rhs_selected.as_ptr()),
        lhs_selected.as_ptr(),
        "helper should select lhs when any v2i64 signed-lt lane is true"
    );
    assert_eq!(
        run(lhs_not_selected.as_ptr(), rhs_not_selected.as_ptr()),
        rhs_not_selected.as_ptr(),
        "helper should select rhs when all v2i64 signed-lt lanes are false"
    );

    let replay = result.buffer.replay_report_metadata();
    let symbol = replay
        .symbols
        .iter()
        .find(|symbol| symbol.name == name)
        .unwrap_or_else(|| panic!("{name} replay symbol should be present"));
    let symbol_size = usize::try_from(symbol.range.end_offset - symbol.range.start_offset)
        .expect("symbol range should fit usize");
    let metrics = result
        .per_function_metrics
        .iter()
        .find(|metrics| metrics.name == name)
        .unwrap_or_else(|| panic!("{name} per-function metrics should be present"));

    assert_eq!(result.metrics.function_count, 1);
    assert_eq!(
        metrics.code_size_bytes,
        raw_code.len(),
        "per-symbol metrics should expose the helper byte size"
    );
    assert!(
        metrics.x86_machine_code.ptest_count >= 1,
        "per-symbol metrics should expose PTEST evidence: {:?}",
        metrics.x86_machine_code
    );
    assert_eq!(
        result.metrics.code_size_bytes,
        raw_code.len(),
        "public JIT code_size_bytes should match the same raw x86 pipeline"
    );
    assert_eq!(
        replay.code_size,
        raw_code.len() as u64,
        "public replay code_size should match the same raw x86 pipeline"
    );
    assert_eq!(
        symbol_size,
        raw_code.len(),
        "public replay symbol range should cover exactly the helper bytes"
    );
}

#[test]
fn test_x86_64_public_jit_v2i64_all_ones_const_avoids_pinsrq() {
    let name = "jit_evidence_v2_all_ones_const";
    let module = build_v2i64_repeated_const_store_module(8840, name, -1);
    let result = host_jit_o0_compiler()
        .compile_module_to_jit(&module, &HashMap::new())
        .expect("JIT compilation should accept v2i64 all-ones const store");

    assert_metrics_code_size_matches_replay(&result, name);
    let metrics = metrics_for(&result, name);
    assert_eq!(
        metrics.x86_machine_code.pcmpeqd_count, 1,
        "repeated v2i64 all-ones const should use one PCMPEQD self-compare: {:?}",
        metrics.x86_machine_code
    );
    assert_eq!(
        metrics.x86_machine_code.pinsrq_count, 0,
        "repeated v2i64 all-ones const should avoid lane-by-lane PINSRQ construction: {:?}",
        metrics.x86_machine_code
    );

    let run: extern "C" fn(*mut i64) = unsafe {
        result
            .buffer
            .get_fn_bound(name)
            .unwrap_or_else(|| panic!("{name} symbol must be present"))
            .into_inner()
    };
    let mut output = [0i64; 2];
    run(output.as_mut_ptr());
    assert_eq!(
        output,
        [-1, -1],
        "JIT helper should materialize both v2i64 lanes as all ones"
    );
}

#[test]
fn test_x86_64_public_jit_v2i64_repeated_const_broadcasts_without_pinsrq() {
    for (index, value) in [42_i64, i64::MIN, i64::MAX].into_iter().enumerate() {
        let name = format!("jit_evidence_v2_repeated_const_{index}");
        let module =
            build_v2i64_repeated_const_store_module(8841 + index as u32, &name, value.into());
        let result = host_jit_o0_compiler()
            .compile_module_to_jit(&module, &HashMap::new())
            .unwrap_or_else(|err| panic!("JIT compilation should accept {name}: {err}"));

        assert_metrics_code_size_matches_replay(&result, &name);
        let metrics = metrics_for(&result, &name);
        assert_eq!(
            metrics.x86_machine_code.movq_to_xmm_count, 1,
            "{name} should seed the low qword with one MOVQ-to-XMM: {:?}",
            metrics.x86_machine_code
        );
        assert_eq!(
            metrics.x86_machine_code.pshufd_count, 1,
            "{name} should broadcast the low qword with one PSHUFD: {:?}",
            metrics.x86_machine_code
        );
        assert_eq!(
            metrics.x86_machine_code.pinsrq_count, 0,
            "{name} should avoid lane-by-lane PINSRQ construction: {:?}",
            metrics.x86_machine_code
        );

        let run: extern "C" fn(*mut i64) = unsafe {
            result
                .buffer
                .get_fn_bound(&name)
                .unwrap_or_else(|| panic!("{name} symbol must be present"))
                .into_inner()
        };
        let mut output = [0i64; 2];
        run(output.as_mut_ptr());
        assert_eq!(
            output,
            [value, value],
            "{name} should materialize both v2i64 lanes from the repeated constant"
        );
    }
}

#[test]
fn test_x86_64_jit_feature_chc() {
    let host = X86TargetFeatures::host();
    let sse2_name = "jit_feature_chc_v4i32_ne_mask_extract";
    let sse2_lir =
        single_translated_lir_function(&build_v4i32_ne_mask_extract_return_module(8920, sse2_name));
    let (sse2_code, sse2_evidence) = compile_lir_o0_raw_with_features(&sse2_lir, host)
        .expect("host x86-64 should compile the SSE2 V128 mask-extract canary");
    eprintln!(
        "x86 JIT feature CHC SSE2 canary: profile={}, evidence={:?}",
        sse2_evidence
            .machine_code
            .target_features
            .metadata_feature_list(),
        sse2_evidence.machine_code
    );
    assert_eq!(sse2_evidence.machine_code.target_features, host);
    assert!(sse2_evidence.machine_code.pcmpeqd_count >= 1);
    assert_eq!(sse2_evidence.machine_code.pmovmskb_count, 1);
    assert_eq!(sse2_evidence.machine_code.pcmpeqq_count, 0);
    assert_eq!(sse2_evidence.machine_code.pcmpgtq_count, 0);
    assert!(!sse2_code.is_empty());

    let sse4_name = "jit_feature_chc_v2i64_slt_bool_extract";
    let sse4_lir = single_translated_lir_function(&build_v2i64_cmp_bool_extract_return_module(
        8921,
        sse4_name,
        ICmpOp::Slt,
        TrustIrTy::I32,
    ));
    let sse4_raw = compile_lir_o0_raw_with_features(&sse4_lir, host);
    let jit_module = build_v2i64_cmp_bool_extract_return_module(
        8922,
        "jit_feature_chc_public_jit_v2i64_slt",
        ICmpOp::Slt,
        TrustIrTy::I32,
    );

    if !host.contains(X86TargetFeature::Sse42) {
        sse4_raw.expect_err("host without SSE4.2 must fail closed for PCMPGTQ");
        host_jit_o0_compiler()
            .compile_module_to_jit(&jit_module, &HashMap::new())
            .expect_err("public host JIT without SSE4.2 must reject the CHC canary");
        return;
    }

    let (sse4_code, sse4_evidence) =
        sse4_raw.expect("host SSE4.2 profile should compile the CHC compare canary");
    eprintln!(
        "x86 JIT feature CHC SSE4 canary: profile={}, evidence={:?}",
        sse4_evidence
            .machine_code
            .target_features
            .metadata_feature_list(),
        sse4_evidence.machine_code
    );
    assert_eq!(sse4_evidence.machine_code.target_features, host);
    assert_eq!(sse4_evidence.machine_code.pcmpgtq_count, 1);
    assert!(
        !contains_vex_prefix_byte(&sse4_code),
        "SSE4 canary must not emit VEX/YMM lowering even when AVX is detected: {sse4_code:02X?}"
    );

    let jit_result = host_jit_o0_compiler()
        .compile_module_to_jit(&jit_module, &HashMap::new())
        .expect("public host JIT should compile the SSE4.2 CHC canary");
    let jit_metrics = metrics_for(&jit_result, "jit_feature_chc_public_jit_v2i64_slt");
    assert_eq!(jit_metrics.x86_machine_code.target_features, host);
    assert_eq!(jit_metrics.x86_machine_code.pcmpgtq_count, 1);
    assert!(
        jit_result
            .buffer
            .get_fn_ptr_bound("jit_feature_chc_public_jit_v2i64_slt")
            .is_some()
    );
}

#[test]
fn test_x86_64_public_jit_opcode_evidence_metrics_cover_sse_lane_ops() {
    let module = build_jit_opcode_evidence_module();
    let result = host_jit_o0_compiler()
        .compile_module_to_jit(&module, &HashMap::new())
        .expect("public x86-64 host JIT should compile opcode evidence module");

    for name in [
        "jit_evidence_v4_mask_extract",
        "jit_evidence_v2_mask_extract",
        "jit_evidence_v2_zero_lane0_insert",
        "jit_evidence_v2_all_ones_const_store",
        "jit_evidence_v2_repeated_const_store",
        "jit_evidence_v4_lane_ops",
        "jit_evidence_v2_lane_ops",
        "jit_evidence_v2_ptest_select",
        "jit_evidence_v4_same_lane_pack",
        "jit_evidence_v4_distinct_lane_pack",
        "jit_evidence_v2_same_lane_pack",
        "jit_evidence_v4_pack_extract_forward",
        "jit_evidence_v2_pack_extract_forward",
        "jit_evidence_v4_mask_select",
        "jit_evidence_v4_i32_arith_logic",
        "jit_evidence_v4_i32_bitselect",
        "jit_evidence_v4_i32_lane_shift_ishl",
        "jit_evidence_v4_i32_lane_shift_ushr",
        "jit_evidence_v4_i32_lane_shift_sshr",
        "jit_evidence_v2_i64_eq_mask_store",
        "jit_evidence_v2_i64_gt_mask_store",
    ] {
        assert_metrics_code_size_matches_replay(&result, name);
    }

    let v4_mask_extract = metrics_for(&result, "jit_evidence_v4_mask_extract");
    let v2_mask_extract = metrics_for(&result, "jit_evidence_v2_mask_extract");
    let v2_zero_lane0_insert = metrics_for(&result, "jit_evidence_v2_zero_lane0_insert");
    let v2_all_ones_const = metrics_for(&result, "jit_evidence_v2_all_ones_const_store");
    let v2_repeated_const = metrics_for(&result, "jit_evidence_v2_repeated_const_store");
    let v4_lane_ops = metrics_for(&result, "jit_evidence_v4_lane_ops");
    let v2_lane_ops = metrics_for(&result, "jit_evidence_v2_lane_ops");
    let ptest_select = metrics_for(&result, "jit_evidence_v2_ptest_select");
    let v4_same_lane_pack = metrics_for(&result, "jit_evidence_v4_same_lane_pack");
    let v4_distinct_lane_pack = metrics_for(&result, "jit_evidence_v4_distinct_lane_pack");
    let v2_same_lane_pack = metrics_for(&result, "jit_evidence_v2_same_lane_pack");
    let v4_pack_extract = metrics_for(&result, "jit_evidence_v4_pack_extract_forward");
    let v2_pack_extract = metrics_for(&result, "jit_evidence_v2_pack_extract_forward");
    let v4_mask_select = metrics_for(&result, "jit_evidence_v4_mask_select");
    let v4_arith_logic = metrics_for(&result, "jit_evidence_v4_i32_arith_logic");
    let v4_bitselect = metrics_for(&result, "jit_evidence_v4_i32_bitselect");
    let v4_shift_metrics = [
        (
            "ishl",
            metrics_for(&result, "jit_evidence_v4_i32_lane_shift_ishl"),
        ),
        (
            "ushr",
            metrics_for(&result, "jit_evidence_v4_i32_lane_shift_ushr"),
        ),
        (
            "sshr",
            metrics_for(&result, "jit_evidence_v4_i32_lane_shift_sshr"),
        ),
    ];
    let v2_eq_mask = metrics_for(&result, "jit_evidence_v2_i64_eq_mask_store");
    let v2_gt_mask = metrics_for(&result, "jit_evidence_v2_i64_gt_mask_store");

    eprintln!(
        "x86 direct v2i64 mask extract metrics: code_size={}, pmovmskb={}, pinsrq={}, pextrq={}",
        v2_mask_extract.code_size_bytes,
        v2_mask_extract.x86_machine_code.pmovmskb_count,
        v2_mask_extract.x86_machine_code.pinsrq_count,
        v2_mask_extract.x86_machine_code.pextrq_count
    );
    eprintln!(
        "x86 CHC v4i32 evidence metrics: \
         mask_extract(code_size={}, pmovmskb={}, pinsrd={}, pextrd={}), \
         lane_ops(code_size={}, pinsrd={}, pextrd={}), \
         same_lane_pack(code_size={}, movd_to_xmm={}, pshufd={}, pinsrd={}), \
         distinct_lane_pack(code_size={}, movd_to_xmm={}, punpckldq={}, punpcklqdq={}, pinsrd={}), \
         pack_extract(code_size={}, movd_to_xmm={}, movq_to_xmm={}, pinsrd={}, pinsrq={}, \
         pextrd={}, pextrq={}), \
         mask_select(code_size={}, pblendvb={}, pmovmskb={}, pinsrd={}, pextrd={})",
        v4_mask_extract.code_size_bytes,
        v4_mask_extract.x86_machine_code.pmovmskb_count,
        v4_mask_extract.x86_machine_code.pinsrd_count,
        v4_mask_extract.x86_machine_code.pextrd_count,
        v4_lane_ops.code_size_bytes,
        v4_lane_ops.x86_machine_code.pinsrd_count,
        v4_lane_ops.x86_machine_code.pextrd_count,
        v4_same_lane_pack.code_size_bytes,
        v4_same_lane_pack.x86_machine_code.movd_to_xmm_count,
        v4_same_lane_pack.x86_machine_code.pshufd_count,
        v4_same_lane_pack.x86_machine_code.pinsrd_count,
        v4_distinct_lane_pack.code_size_bytes,
        v4_distinct_lane_pack.x86_machine_code.movd_to_xmm_count,
        v4_distinct_lane_pack.x86_machine_code.punpckldq_count,
        v4_distinct_lane_pack.x86_machine_code.punpcklqdq_count,
        v4_distinct_lane_pack.x86_machine_code.pinsrd_count,
        v4_pack_extract.code_size_bytes,
        v4_pack_extract.x86_machine_code.movd_to_xmm_count,
        v2_pack_extract.x86_machine_code.movq_to_xmm_count,
        v4_pack_extract.x86_machine_code.pinsrd_count,
        v2_pack_extract.x86_machine_code.pinsrq_count,
        v4_pack_extract.x86_machine_code.pextrd_count,
        v2_pack_extract.x86_machine_code.pextrq_count,
        v4_mask_select.code_size_bytes,
        v4_mask_select.x86_machine_code.pblendvb_count,
        v4_mask_select.x86_machine_code.pmovmskb_count,
        v4_mask_select.x86_machine_code.pinsrd_count,
        v4_mask_select.x86_machine_code.pextrd_count
    );
    eprintln!(
        "x86 SAT/PB SIMD evidence metrics: \
         arith_logic(code_size={}, paddd={}, psubd={}, pmulld={}, pcmpgtd={}, pand={}, por={}, pxor={}, movdqu_load={}, movdqu_store={}), \
         bitselect(code_size={}, pand={}, pandn={}, por={}, movdqu_load={}, movdqu_store={}), \
         v2_eq(code_size={}, pcmpeqq={}, movdqu_load={}, movdqu_store={}), \
         v2_gt(code_size={}, pcmpgtq={}, movdqu_load={}, movdqu_store={})",
        v4_arith_logic.code_size_bytes,
        v4_arith_logic.x86_machine_code.paddd_count,
        v4_arith_logic.x86_machine_code.psubd_count,
        v4_arith_logic.x86_machine_code.pmulld_count,
        v4_arith_logic.x86_machine_code.pcmpgtd_count,
        v4_arith_logic.x86_machine_code.pand_count,
        v4_arith_logic.x86_machine_code.por_count,
        v4_arith_logic.x86_machine_code.pxor_count,
        v4_arith_logic.x86_machine_code.movdqu_load_count,
        v4_arith_logic.x86_machine_code.movdqu_store_count,
        v4_bitselect.code_size_bytes,
        v4_bitselect.x86_machine_code.pand_count,
        v4_bitselect.x86_machine_code.pandn_count,
        v4_bitselect.x86_machine_code.por_count,
        v4_bitselect.x86_machine_code.movdqu_load_count,
        v4_bitselect.x86_machine_code.movdqu_store_count,
        v2_eq_mask.code_size_bytes,
        v2_eq_mask.x86_machine_code.pcmpeqq_count,
        v2_eq_mask.x86_machine_code.movdqu_load_count,
        v2_eq_mask.x86_machine_code.movdqu_store_count,
        v2_gt_mask.code_size_bytes,
        v2_gt_mask.x86_machine_code.pcmpgtq_count,
        v2_gt_mask.x86_machine_code.movdqu_load_count,
        v2_gt_mask.x86_machine_code.movdqu_store_count
    );
    for (name, metrics) in v4_shift_metrics.iter().copied() {
        eprintln!(
            "x86 v4i32 lane shift {name} metrics: code_size={}, punpckldq={}, punpcklqdq={}, pinsrd={}, pextrd={}",
            metrics.code_size_bytes,
            metrics.x86_machine_code.punpckldq_count,
            metrics.x86_machine_code.punpcklqdq_count,
            metrics.x86_machine_code.pinsrd_count,
            metrics.x86_machine_code.pextrd_count
        );
    }

    assert_eq!(
        v4_mask_extract.x86_machine_code.pmovmskb_count, 1,
        "v4i32 mask extract should expose exactly one PMOVMSKB: {:?}",
        v4_mask_extract.x86_machine_code
    );
    assert_eq!(
        v4_mask_extract.x86_machine_code.pinsrd_count, 0,
        "v4i32 mask extract should not rebuild lanes with PINSRD: {:?}",
        v4_mask_extract.x86_machine_code
    );
    assert_eq!(
        v4_mask_extract.x86_machine_code.pextrd_count, 0,
        "v4i32 mask extract should not scalarize lanes with PEXTRD: {:?}",
        v4_mask_extract.x86_machine_code
    );
    assert_eq!(
        v2_mask_extract.x86_machine_code.pmovmskb_count, 1,
        "direct v2i64 mask extract should expose exactly one PMOVMSKB: {:?}",
        v2_mask_extract.x86_machine_code
    );
    assert_eq!(
        v2_mask_extract.x86_machine_code.pinsrq_count, 0,
        "direct v2i64 mask extract should not pack lanes with PINSRQ: {:?}",
        v2_mask_extract.x86_machine_code
    );
    assert_eq!(
        v2_mask_extract.x86_machine_code.pextrq_count, 0,
        "direct v2i64 mask extract should not scalarize lanes with PEXTRQ: {:?}",
        v2_mask_extract.x86_machine_code
    );
    assert_eq!(
        v2_mask_extract.code_size_bytes, 25,
        "direct v2i64 mask extract public-JIT code size changed: {:?}",
        v2_mask_extract.x86_machine_code
    );
    assert!(
        v2_mask_extract.code_size_bytes < v2_lane_ops.code_size_bytes,
        "direct v2i64 mask extract should stay smaller than explicit qword lane ops: \
         direct={} lane_ops={}",
        v2_mask_extract.code_size_bytes,
        v2_lane_ops.code_size_bytes
    );
    assert_eq!(
        v2_zero_lane0_insert.x86_machine_code.movq_to_xmm_count, 1,
        "v2i64 zero lane-0 insert should expose one MOVQ-to-XMM fold: {:?}",
        v2_zero_lane0_insert.x86_machine_code
    );
    assert_eq!(
        v2_zero_lane0_insert.x86_machine_code.pinsrq_count, 0,
        "v2i64 zero lane-0 insert should not fall back to PINSRQ: {:?}",
        v2_zero_lane0_insert.x86_machine_code
    );
    assert_eq!(
        v2_all_ones_const.x86_machine_code.pcmpeqd_count, 1,
        "v2i64 all-ones constant should use one PCMPEQD self-compare: {:?}",
        v2_all_ones_const.x86_machine_code
    );
    assert_eq!(
        v2_all_ones_const.x86_machine_code.pinsrq_count, 0,
        "v2i64 all-ones constant should not pack the high qword with PINSRQ: {:?}",
        v2_all_ones_const.x86_machine_code
    );
    assert_eq!(
        v2_repeated_const.x86_machine_code.movq_to_xmm_count, 1,
        "v2i64 repeated constant should seed from one MOVQ-to-XMM: {:?}",
        v2_repeated_const.x86_machine_code
    );
    assert_eq!(
        v2_repeated_const.x86_machine_code.pshufd_count, 1,
        "v2i64 repeated constant should broadcast through one PSHUFD: {:?}",
        v2_repeated_const.x86_machine_code
    );
    assert_eq!(
        v2_repeated_const.x86_machine_code.pinsrq_count, 0,
        "v2i64 repeated constant should avoid PINSRQ: {:?}",
        v2_repeated_const.x86_machine_code
    );
    assert!(
        ptest_select.x86_machine_code.ptest_count >= 1,
        "v2i64 pointer select should expose PTEST evidence: {:?}",
        ptest_select.x86_machine_code
    );
    assert_eq!(
        v4_lane_ops.x86_machine_code.movd_to_xmm_count, 4,
        "v4i32 single-lane ops should seed lanes through MOVD-to-XMM: {:?}",
        v4_lane_ops.x86_machine_code
    );
    assert_eq!(
        v4_lane_ops.x86_machine_code.punpckldq_count, 2,
        "v4i32 single-lane ops should form dword pairs with PUNPCKLDQ: {:?}",
        v4_lane_ops.x86_machine_code
    );
    assert_eq!(
        v4_lane_ops.x86_machine_code.punpcklqdq_count, 1,
        "v4i32 single-lane ops should preserve lane order with PUNPCKLQDQ: {:?}",
        v4_lane_ops.x86_machine_code
    );
    assert_eq!(
        v4_lane_ops.x86_machine_code.pinsrd_count, 0,
        "v4i32 single-lane ops should avoid SSE4 PINSRD insertion: {:?}",
        v4_lane_ops.x86_machine_code
    );
    assert_eq!(
        v4_lane_ops.x86_machine_code.pextrd_count, 0,
        "v4i32 single-lane ops should avoid scalar PEXTRD extraction: {:?}",
        v4_lane_ops.x86_machine_code
    );
    assert_eq!(
        v2_lane_ops.x86_machine_code.movq_to_xmm_count, 1,
        "v2i64 single-lane ops should seed through one MOVQ-to-XMM: {:?}",
        v2_lane_ops.x86_machine_code
    );
    assert_eq!(
        v2_lane_ops.x86_machine_code.punpcklqdq_count, 1,
        "v2i64 single-lane ops should rebuild qword lanes with one PUNPCKLQDQ: {:?}",
        v2_lane_ops.x86_machine_code
    );
    assert_eq!(
        v2_lane_ops.x86_machine_code.pinsrq_count, 0,
        "v2i64 single-lane ops should avoid scalar PINSRQ insertion: {:?}",
        v2_lane_ops.x86_machine_code
    );
    assert_eq!(
        v2_lane_ops.x86_machine_code.pextrq_count, 0,
        "v2i64 single-lane ops should avoid scalar PEXTRQ extraction: {:?}",
        v2_lane_ops.x86_machine_code
    );
    assert_eq!(
        v4_same_lane_pack.x86_machine_code.movd_to_xmm_count, 1,
        "same-lane v4i32 pack should seed through one MOVD-to-XMM: {:?}",
        v4_same_lane_pack.x86_machine_code
    );
    assert_eq!(
        v4_same_lane_pack.x86_machine_code.pshufd_count, 1,
        "same-lane v4i32 pack should broadcast through one PSHUFD: {:?}",
        v4_same_lane_pack.x86_machine_code
    );
    assert_eq!(
        v4_same_lane_pack.x86_machine_code.pinsrd_count, 0,
        "same-lane v4i32 pack should avoid scalar PINSRD lane inserts: {:?}",
        v4_same_lane_pack.x86_machine_code
    );
    assert_eq!(
        v4_distinct_lane_pack.x86_machine_code.movd_to_xmm_count, 4,
        "distinct-lane v4i32 pack should seed each lane through MOVD-to-XMM: {:?}",
        v4_distinct_lane_pack.x86_machine_code
    );
    assert_eq!(
        v4_distinct_lane_pack.x86_machine_code.punpckldq_count, 2,
        "distinct-lane v4i32 pack should form two dword pairs with PUNPCKLDQ: {:?}",
        v4_distinct_lane_pack.x86_machine_code
    );
    assert_eq!(
        v4_distinct_lane_pack.x86_machine_code.punpcklqdq_count, 1,
        "distinct-lane v4i32 pack should preserve lane order with PUNPCKLQDQ: {:?}",
        v4_distinct_lane_pack.x86_machine_code
    );
    assert_eq!(
        v4_distinct_lane_pack.x86_machine_code.pinsrd_count, 0,
        "distinct-lane v4i32 pack should avoid scalar PINSRD lane inserts: {:?}",
        v4_distinct_lane_pack.x86_machine_code
    );
    assert!(
        v4_distinct_lane_pack.code_size_bytes <= 64,
        "distinct-lane v4i32 pack helper should stay code-size bounded: {}",
        v4_distinct_lane_pack.code_size_bytes
    );
    assert_eq!(
        v2_same_lane_pack.x86_machine_code.movq_to_xmm_count, 1,
        "same-lane v2i64 pack should seed through one MOVQ-to-XMM: {:?}",
        v2_same_lane_pack.x86_machine_code
    );
    assert_eq!(
        v2_same_lane_pack.x86_machine_code.pshufd_count, 1,
        "same-lane v2i64 pack should broadcast through one PSHUFD: {:?}",
        v2_same_lane_pack.x86_machine_code
    );
    assert_eq!(
        v2_same_lane_pack.x86_machine_code.pinsrq_count, 0,
        "same-lane v2i64 pack should avoid scalar PINSRQ lane insert: {:?}",
        v2_same_lane_pack.x86_machine_code
    );
    assert_eq!(
        v4_pack_extract.x86_machine_code.movd_to_xmm_count, 0,
        "single-use v4i32 pack/extract should not materialize the vector: {:?}",
        v4_pack_extract.x86_machine_code
    );
    assert_eq!(
        v4_pack_extract.x86_machine_code.pinsrd_count, 0,
        "single-use v4i32 pack/extract should avoid PINSRD: {:?}",
        v4_pack_extract.x86_machine_code
    );
    assert_eq!(
        v4_pack_extract.x86_machine_code.pextrd_count, 0,
        "single-use v4i32 pack/extract should avoid PEXTRD: {:?}",
        v4_pack_extract.x86_machine_code
    );
    assert_eq!(
        v2_pack_extract.x86_machine_code.movq_to_xmm_count, 0,
        "single-use v2i64 pack/extract should not materialize the vector: {:?}",
        v2_pack_extract.x86_machine_code
    );
    assert_eq!(
        v2_pack_extract.x86_machine_code.pinsrq_count, 0,
        "single-use v2i64 pack/extract should avoid PINSRQ: {:?}",
        v2_pack_extract.x86_machine_code
    );
    assert_eq!(
        v2_pack_extract.x86_machine_code.pextrq_count, 0,
        "single-use v2i64 pack/extract should avoid PEXTRQ: {:?}",
        v2_pack_extract.x86_machine_code
    );
    assert_eq!(
        v4_mask_select.x86_machine_code.pblendvb_count, 1,
        "v4i32 vector mask select should expose one PBLENDVB on the host SSE4.1 path: {:?}",
        v4_mask_select.x86_machine_code
    );
    assert_eq!(
        v4_mask_select.x86_machine_code.pmovmskb_count, 0,
        "v4i32 vector mask select should not extract the mask with PMOVMSKB: {:?}",
        v4_mask_select.x86_machine_code
    );
    assert_eq!(
        v4_mask_select.x86_machine_code.pinsrd_count, 0,
        "v4i32 vector mask select should not rebuild selected lanes with PINSRD: {:?}",
        v4_mask_select.x86_machine_code
    );
    assert_eq!(
        v4_mask_select.x86_machine_code.pextrd_count, 0,
        "v4i32 vector mask select should not scalarize selected lanes with PEXTRD: {:?}",
        v4_mask_select.x86_machine_code
    );
    assert_eq!(
        v4_arith_logic.x86_machine_code.paddd_count, 1,
        "v4i32 arith/logic evidence should expose PADDD: {:?}",
        v4_arith_logic.x86_machine_code
    );
    assert_eq!(
        v4_arith_logic.x86_machine_code.psubd_count, 1,
        "v4i32 arith/logic evidence should expose PSUBD: {:?}",
        v4_arith_logic.x86_machine_code
    );
    assert_eq!(
        v4_arith_logic.x86_machine_code.pmulld_count, 1,
        "v4i32 arith/logic evidence should expose PMULLD: {:?}",
        v4_arith_logic.x86_machine_code
    );
    assert_eq!(
        v4_arith_logic.x86_machine_code.pcmpgtd_count, 1,
        "v4i32 arith/logic evidence should expose PCMPGTD: {:?}",
        v4_arith_logic.x86_machine_code
    );
    assert!(
        v4_arith_logic.x86_machine_code.pand_count >= 1
            && v4_arith_logic.x86_machine_code.por_count >= 1
            && v4_arith_logic.x86_machine_code.pxor_count >= 1,
        "v4i32 arith/logic evidence should expose PAND/POR/PXOR: {:?}",
        v4_arith_logic.x86_machine_code
    );
    assert!(
        v4_arith_logic.x86_machine_code.movdqu_load_count >= 2
            && v4_arith_logic.x86_machine_code.movdqu_store_count >= 1,
        "v4i32 arith/logic evidence should expose final MOVDQU load/store counts: {:?}",
        v4_arith_logic.x86_machine_code
    );
    assert!(
        v4_bitselect.x86_machine_code.pand_count >= 1
            && v4_bitselect.x86_machine_code.pandn_count >= 1
            && v4_bitselect.x86_machine_code.por_count >= 1,
        "loaded-mask v4i32 select should expose SSE2 bitselect PAND/PANDN/POR: {:?}",
        v4_bitselect.x86_machine_code
    );
    assert!(
        v4_bitselect.x86_machine_code.movdqu_load_count >= 3
            && v4_bitselect.x86_machine_code.movdqu_store_count >= 1,
        "loaded-mask v4i32 select should expose final MOVDQU load/store counts: {:?}",
        v4_bitselect.x86_machine_code
    );
    for (name, metrics) in v4_shift_metrics.iter().copied() {
        assert_eq!(
            metrics.x86_machine_code.punpckldq_count, 2,
            "v4i32 {name} scalarized shift should form two dword pairs with PUNPCKLDQ: {:?}",
            metrics.x86_machine_code
        );
        assert_eq!(
            metrics.x86_machine_code.punpcklqdq_count, 1,
            "v4i32 {name} scalarized shift should join dword pairs with PUNPCKLQDQ: {:?}",
            metrics.x86_machine_code
        );
        assert_eq!(
            metrics.x86_machine_code.pinsrd_count, 0,
            "v4i32 {name} scalarized shift should avoid PINSRD reassembly: {:?}",
            metrics.x86_machine_code
        );
        assert_eq!(
            metrics.x86_machine_code.pextrd_count, 0,
            "v4i32 {name} scalarized shift should avoid PEXTRD extraction: {:?}",
            metrics.x86_machine_code
        );
    }
    assert_eq!(
        v2_eq_mask.x86_machine_code.pcmpeqq_count, 1,
        "v2i64 equality mask evidence should expose PCMPEQQ: {:?}",
        v2_eq_mask.x86_machine_code
    );
    assert_eq!(
        v2_gt_mask.x86_machine_code.pcmpgtq_count, 1,
        "v2i64 signed greater-than mask evidence should expose PCMPGTQ: {:?}",
        v2_gt_mask.x86_machine_code
    );
    assert!(
        v2_eq_mask.x86_machine_code.movdqu_load_count >= 2
            && v2_eq_mask.x86_machine_code.movdqu_store_count >= 1
            && v2_gt_mask.x86_machine_code.movdqu_load_count >= 2
            && v2_gt_mask.x86_machine_code.movdqu_store_count >= 1,
        "v2i64 compare-mask evidence should expose final MOVDQU load/store counts: eq={:?} gt={:?}",
        v2_eq_mask.x86_machine_code,
        v2_gt_mask.x86_machine_code
    );

    let movdqa_count: usize = result
        .per_function_metrics
        .iter()
        .map(|metrics| metrics.x86_machine_code.movdqa_count)
        .sum();
    assert!(
        movdqa_count >= 1,
        "real JIT compile should expose MOVDQA evidence: {:?}",
        result
            .per_function_metrics
            .iter()
            .map(|metrics| (&metrics.name, metrics.x86_machine_code))
            .collect::<Vec<_>>()
    );

    let run_v4_lane_ops: extern "C" fn(*mut i32, i32) -> i32 = unsafe {
        result
            .buffer
            .get_fn_bound("jit_evidence_v4_lane_ops")
            .expect("jit_evidence_v4_lane_ops symbol must be present")
            .into_inner()
    };
    let mut v4_lanes = [11i32, -22, 33, -44];
    let old_v4_lane = run_v4_lane_ops(v4_lanes.as_mut_ptr(), 99);
    assert_eq!(
        old_v4_lane, 33,
        "v4i32 extract must return the original lane 2 value"
    );
    assert_eq!(
        v4_lanes,
        [11, -22, 99, -44],
        "v4i32 insert must replace lane 2 while preserving lane order"
    );

    let run_v2_lane_ops: extern "C" fn(*mut i64, i64) -> i64 = unsafe {
        result
            .buffer
            .get_fn_bound("jit_evidence_v2_lane_ops")
            .expect("jit_evidence_v2_lane_ops symbol must be present")
            .into_inner()
    };
    let mut v2_lanes = [0x1122_3344_5566_7788i64, -9];
    let old_v2_lane = run_v2_lane_ops(v2_lanes.as_mut_ptr(), i64::MIN);
    assert_eq!(
        old_v2_lane, -9,
        "v2i64 extract must return the original lane 1 value"
    );
    assert_eq!(
        v2_lanes,
        [0x1122_3344_5566_7788i64, i64::MIN],
        "v2i64 insert must replace lane 1 while preserving lane order"
    );
}

#[test]
fn test_x86_64_jit_packed_compare_multiply_rhs_spill_fold_canary() {
    let host = X86TargetFeatures::host();
    if !host.contains(X86TargetFeature::Sse41) {
        eprintln!("skipping packed RHS spill-fold canary on host without SSE4.1");
        return;
    }

    let lhs = [7i32, -3, 0x4000, i32::MIN];
    let rhs = [7i32, 9, -2, -1];

    for (name, opcode) in [
        ("pcmpeqd", X86Opcode::Pcmpeqd),
        ("pmulld", X86Opcode::Pmulld),
    ] {
        let folded = build_packed_rhs_spill_canary_function(
            &format!("packed_rhs_spill_{name}_folded"),
            opcode,
            true,
        );
        let explicit = build_packed_rhs_spill_canary_function(
            &format!("packed_rhs_spill_{name}_explicit_reload"),
            opcode,
            false,
        );
        let (folded_code, folded_evidence) = compile_isel_o0_raw_with_features(&folded, host);
        let (explicit_code, explicit_evidence) = compile_isel_o0_raw_with_features(&explicit, host);

        eprintln!(
            "x86 packed RHS spill-fold {name} canary: \
             folded(code_size={}, movdqu_load={}, evidence={:?}), \
             explicit(code_size={}, movdqu_load={}, evidence={:?})",
            folded_evidence.code_size_bytes,
            folded_evidence.machine_code.movdqu_load_count,
            folded_evidence.machine_code,
            explicit_evidence.code_size_bytes,
            explicit_evidence.machine_code.movdqu_load_count,
            explicit_evidence.machine_code
        );

        assert_eq!(folded_evidence.code_size_bytes, folded_code.len());
        assert_eq!(explicit_evidence.code_size_bytes, explicit_code.len());
        assert!(
            folded_code.len() < explicit_code.len(),
            "{name} folded memory-RHS code should be smaller: folded={folded_code:02X?} explicit={explicit_code:02X?}"
        );
        assert_eq!(
            explicit_evidence.machine_code.movdqu_load_count,
            folded_evidence.machine_code.movdqu_load_count + 1,
            "{name} folded memory-RHS code should remove the explicit MOVDQU reload"
        );
        assert!(
            !contains_vex_instruction_prefix(&folded_code),
            "{name} folded canary must stay on legacy SSE encodings: {folded_code:02X?}"
        );

        match opcode {
            X86Opcode::Pcmpeqd => {
                assert_eq!(folded_evidence.machine_code.pcmpeqd_count, 1);
                assert_eq!(explicit_evidence.machine_code.pcmpeqd_count, 1);
            }
            X86Opcode::Pmulld => {
                assert_eq!(folded_evidence.machine_code.pmulld_count, 1);
                assert_eq!(explicit_evidence.machine_code.pmulld_count, 1);
            }
            _ => unreachable!("canary covers only packed compare/multiply"),
        }

        let folded_page = ExecPage::new(&folded_code);
        let explicit_page = ExecPage::new(&explicit_code);
        let run_folded: extern "C" fn(*const i32, *const i32, *mut i32) =
            unsafe { core::mem::transmute(folded_page.as_ptr()) };
        let run_explicit: extern "C" fn(*const i32, *const i32, *mut i32) =
            unsafe { core::mem::transmute(explicit_page.as_ptr()) };

        let mut folded_output = [0i32; 4];
        let mut explicit_output = [0i32; 4];
        run_folded(lhs.as_ptr(), rhs.as_ptr(), folded_output.as_mut_ptr());
        run_explicit(lhs.as_ptr(), rhs.as_ptr(), explicit_output.as_mut_ptr());

        let expected = core::array::from_fn(|lane| match opcode {
            X86Opcode::Pcmpeqd => {
                if lhs[lane] == rhs[lane] {
                    -1
                } else {
                    0
                }
            }
            X86Opcode::Pmulld => lhs[lane].wrapping_mul(rhs[lane]),
            _ => unreachable!("canary covers only packed compare/multiply"),
        });
        assert_eq!(
            folded_output, expected,
            "{name} folded memory-RHS code should preserve native results"
        );
        assert_eq!(
            explicit_output, expected,
            "{name} explicit-reload baseline should preserve native results"
        );
    }
}

#[test]
fn test_x86_64_jit_pshufd_rhs_spill_fold_preserves_lane_shuffle_result() {
    let host = X86TargetFeatures::host();
    let folded = build_pshufd_rhs_spill_canary_function("pshufd_rhs_spill_folded", true);
    let explicit =
        build_pshufd_rhs_spill_canary_function("pshufd_rhs_spill_explicit_reload", false);
    let (folded_code, folded_evidence) = compile_isel_o0_raw_with_features(&folded, host);
    let (explicit_code, explicit_evidence) = compile_isel_o0_raw_with_features(&explicit, host);

    eprintln!(
        "x86 PSHUFD RHS spill-fold canary: \
         folded(code_size={}, movdqu_load={}, pshufd={}, evidence={:?}), \
         explicit(code_size={}, movdqu_load={}, pshufd={}, evidence={:?})",
        folded_evidence.code_size_bytes,
        folded_evidence.machine_code.movdqu_load_count,
        folded_evidence.machine_code.pshufd_count,
        folded_evidence.machine_code,
        explicit_evidence.code_size_bytes,
        explicit_evidence.machine_code.movdqu_load_count,
        explicit_evidence.machine_code.pshufd_count,
        explicit_evidence.machine_code
    );

    assert_eq!(folded_evidence.code_size_bytes, folded_code.len());
    assert_eq!(explicit_evidence.code_size_bytes, explicit_code.len());
    assert!(
        folded_code.len() < explicit_code.len(),
        "PSHUFD folded memory-source code should be smaller: folded={folded_code:02X?} explicit={explicit_code:02X?}"
    );
    assert_eq!(
        explicit_evidence.machine_code.movdqu_load_count,
        folded_evidence.machine_code.movdqu_load_count + 1,
        "PSHUFD folded memory source should remove the explicit MOVDQU reload"
    );
    assert_eq!(folded_evidence.machine_code.pshufd_count, 1);
    assert_eq!(explicit_evidence.machine_code.pshufd_count, 1);
    assert!(
        contains_sse2_opcode(&folded_code, 0x70),
        "folded PSHUFD canary must encode legacy 66 0F 70 bytes: {folded_code:02X?}"
    );
    assert!(
        !contains_vex_instruction_prefix(&folded_code),
        "folded PSHUFD canary must stay on legacy SSE encodings: {folded_code:02X?}"
    );

    let folded_page = ExecPage::new(&folded_code);
    let explicit_page = ExecPage::new(&explicit_code);
    let run_folded: extern "C" fn(*const i32, *mut i32) =
        unsafe { core::mem::transmute(folded_page.as_ptr()) };
    let run_explicit: extern "C" fn(*const i32, *mut i32) =
        unsafe { core::mem::transmute(explicit_page.as_ptr()) };

    let input = [0x1111_1111i32, 0x2222_2222, 0x3333_3333, 0x4444_4444];
    let expected = [input[3], input[2], input[1], input[0]];
    let mut folded_output = [0i32; 4];
    let mut explicit_output = [0i32; 4];
    run_folded(input.as_ptr(), folded_output.as_mut_ptr());
    run_explicit(input.as_ptr(), explicit_output.as_mut_ptr());

    assert_eq!(
        folded_output, expected,
        "folded PSHUFD memory-source code should preserve the lane-reversal result"
    );
    assert_eq!(
        explicit_output, expected,
        "explicit PSHUFD reload baseline should preserve the lane-reversal result"
    );
}

#[test]
fn test_x86_64_jit_v128_i32_iadd_uses_paddd_for_all_lanes() {
    let func = build_v128_i32_binop_store_function("v128_i32_iadd_all_lanes", Opcode::Iadd);
    let code = compile_lir_leaf(&func);
    assert!(
        contains_sse2_opcode(&code, 0xFE),
        "V128 Iadd must encode native PADDD bytes, code={code:02X?}"
    );

    let page = ExecPage::new(&code);
    // SAFETY: `page` contains a leaf System V function taking three
    // pointer-sized integer arguments and returning void.
    let f: extern "C" fn(*const i32, *const i32, *mut i32) =
        unsafe { core::mem::transmute(page.as_ptr()) };

    let lhs = [1i32, -2, i32::MAX, i32::MIN];
    let rhs = [10i32, -20, 1, -1];
    let mut output = [0i32; 4];
    f(lhs.as_ptr(), rhs.as_ptr(), output.as_mut_ptr());

    assert_eq!(
        output,
        [
            lhs[0].wrapping_add(rhs[0]),
            lhs[1].wrapping_add(rhs[1]),
            lhs[2].wrapping_add(rhs[2]),
            lhs[3].wrapping_add(rhs[3]),
        ]
    );
}

#[test]
fn test_x86_64_jit_v128_i32_isub_uses_psubd_for_all_lanes() {
    let func = build_v128_i32_binop_store_function("v128_i32_isub_all_lanes", Opcode::Isub);
    let code = compile_lir_leaf(&func);
    assert!(
        contains_sse2_opcode(&code, 0xFA),
        "V128 Isub must encode native PSUBD bytes, code={code:02X?}"
    );

    let page = ExecPage::new(&code);
    // SAFETY: `page` contains a leaf System V function taking three
    // pointer-sized integer arguments and returning void.
    let f: extern "C" fn(*const i32, *const i32, *mut i32) =
        unsafe { core::mem::transmute(page.as_ptr()) };

    let lhs = [1i32, -2, i32::MAX, i32::MIN];
    let rhs = [10i32, -20, 1, -1];
    let mut output = [0i32; 4];
    f(lhs.as_ptr(), rhs.as_ptr(), output.as_mut_ptr());

    assert_eq!(
        output,
        [
            lhs[0].wrapping_sub(rhs[0]),
            lhs[1].wrapping_sub(rhs[1]),
            lhs[2].wrapping_sub(rhs[2]),
            lhs[3].wrapping_sub(rhs[3]),
        ]
    );
}

#[test]
fn test_x86_64_jit_narrow_i8_i16_add_sub_mul_use_legacy_sse2_without_vex() {
    for (name, opcode, sse2_opcode) in [
        ("v16i8_add_paddb", Opcode::V16I8Add, 0xFC),
        ("v16i8_sub_psubb", Opcode::V16I8Sub, 0xF8),
        ("v16i8_mul_packuswb", Opcode::V16I8Mul, 0x67),
    ] {
        let func = build_v128_i32_binop_store_function(name, opcode.clone());
        let code = compile_lir_leaf(&func);
        assert!(
            contains_sse2_opcode(&code, sse2_opcode),
            "{name} must encode legacy SSE2 packed byte arithmetic, code={code:02X?}"
        );
        assert!(
            !code.contains(&0xC4) && !code.contains(&0xC5),
            "{name} must not require VEX/YMM encoding, code={code:02X?}"
        );

        let page = ExecPage::new(&code);
        // SAFETY: `page` contains a leaf System V function taking three
        // pointer-sized arguments and returning void.
        let run: extern "C" fn(*const i8, *const i8, *mut i8) =
            unsafe { core::mem::transmute(page.as_ptr()) };

        let lhs: [i8; 16] = [
            120, 127, -128, -1, 0, 1, 2, 3, 10, 20, 30, 40, 50, 60, 70, 80,
        ];
        let rhs: [i8; 16] = [
            10, 1, -1, 2, -1, -2, 100, -100, 90, -90, 31, -31, 77, -77, 5, -5,
        ];
        let mut output = [0i8; 16];
        run(lhs.as_ptr(), rhs.as_ptr(), output.as_mut_ptr());
        let expected = core::array::from_fn(|lane| match opcode {
            Opcode::V16I8Add => lhs[lane].wrapping_add(rhs[lane]),
            Opcode::V16I8Sub => lhs[lane].wrapping_sub(rhs[lane]),
            Opcode::V16I8Mul => lhs[lane].wrapping_mul(rhs[lane]),
            _ => unreachable!("test cases contain only v16i8 add/sub/mul"),
        });
        assert_eq!(output, expected, "{name} should wrap each i8 lane");
    }

    for (name, opcode, sse2_opcode) in [
        ("v8i16_add_paddw", Opcode::V8I16Add, 0xFD),
        ("v8i16_sub_psubw", Opcode::V8I16Sub, 0xF9),
        ("v8i16_mul_pmullw", Opcode::V8I16Mul, 0xD5),
    ] {
        let func = build_v128_i32_binop_store_function(name, opcode.clone());
        let code = compile_lir_leaf(&func);
        assert!(
            contains_sse2_opcode(&code, sse2_opcode),
            "{name} must encode legacy SSE2 packed word arithmetic, code={code:02X?}"
        );
        assert!(
            !code.contains(&0xC4) && !code.contains(&0xC5),
            "{name} must not require VEX/YMM encoding, code={code:02X?}"
        );

        let page = ExecPage::new(&code);
        // SAFETY: `page` contains a leaf System V function taking three
        // pointer-sized arguments and returning void.
        let run: extern "C" fn(*const i16, *const i16, *mut i16) =
            unsafe { core::mem::transmute(page.as_ptr()) };

        let lhs: [i16; 8] = [32760, 32767, -32768, -1, 0, 1, 12345, -23456];
        let rhs: [i16; 8] = [10, 1, -1, 2, -1, -2, 23456, -12345];
        let mut output = [0i16; 8];
        run(lhs.as_ptr(), rhs.as_ptr(), output.as_mut_ptr());
        let expected = core::array::from_fn(|lane| match opcode {
            Opcode::V8I16Add => lhs[lane].wrapping_add(rhs[lane]),
            Opcode::V8I16Sub => lhs[lane].wrapping_sub(rhs[lane]),
            Opcode::V8I16Mul => lhs[lane].wrapping_mul(rhs[lane]),
            _ => unreachable!("test cases contain only v8i16 add/sub/mul"),
        });
        assert_eq!(output, expected, "{name} should wrap each i16 lane");
    }
}

#[test]
fn test_x86_64_jit_narrow_i8_i16_bitwise_ops_preserve_lane_values() {
    let host = X86TargetFeatures::host();
    let i8_lhs: [i8; 16] = [
        0x55,
        -1,
        i8::MIN,
        0x12,
        0,
        1,
        2,
        3,
        0x7F,
        -0x40,
        0x33,
        -0x22,
        0x0F,
        -0x10,
        0x24,
        -0x25,
    ];
    let i8_rhs: [i8; 16] = [
        0x33, 0, -1, 0x0F, -1, -2, 0x55, -0x56, 0x70, 0x3C, -0x34, 0x21, -0x10, 0x0F, -0x25, 0x24,
    ];

    for (index, (suffix, op, sse2_opcode)) in [
        ("and", BinOp::And, 0xDB),
        ("or", BinOp::Or, 0xEB),
        ("xor", BinOp::Xor, 0xEF),
    ]
    .into_iter()
    .enumerate()
    {
        let name = format!("v16i8_{suffix}_bitwise_lane_values");
        let module =
            build_narrow_bitwise_store_module(8920 + index as u32, &name, v16i8_ty(), op.clone());
        let result = host_jit_o0_compiler()
            .compile_module_to_jit(&module, &HashMap::new())
            .unwrap_or_else(|err| panic!("x86-64 host JIT should compile {name}: {err}"));
        assert_metrics_code_size_matches_replay(&result, &name);
        let metrics = metrics_for(&result, &name);
        let code = jit_symbol_code_bytes(&result, &name);
        assert_eq!(metrics.x86_machine_code.target_features, host);
        assert_eq!(
            metrics.x86_machine_code.pand_count,
            usize::from(op == BinOp::And),
            "{name}: {:?}",
            metrics.x86_machine_code
        );
        assert_eq!(
            metrics.x86_machine_code.por_count,
            usize::from(op == BinOp::Or),
            "{name}: {:?}",
            metrics.x86_machine_code
        );
        assert_eq!(
            metrics.x86_machine_code.pxor_count,
            usize::from(op == BinOp::Xor),
            "{name}: {:?}",
            metrics.x86_machine_code
        );
        assert_no_scalar_lane_fallback(&metrics.x86_machine_code, &name);
        assert_eq!(metrics.x86_machine_code.movd_to_xmm_count, 0, "{name}");
        assert_eq!(metrics.x86_machine_code.movq_to_xmm_count, 0, "{name}");
        assert!(
            contains_sse2_opcode(code, sse2_opcode),
            "{name} must encode legacy SSE2 bitwise opcode {sse2_opcode:#04x}: {code:02X?}"
        );
        assert!(
            !contains_vex_instruction_prefix(code),
            "{name} must stay on legacy XMM/SSE encodings without VEX/YMM lowering: {code:02X?}"
        );

        let run: extern "C" fn(*const i8, *const i8, *mut i8) = unsafe {
            result
                .buffer
                .get_fn_bound(&name)
                .unwrap_or_else(|| panic!("{name} symbol must be present"))
                .into_inner()
        };
        let mut output = [0i8; 16];
        run(i8_lhs.as_ptr(), i8_rhs.as_ptr(), output.as_mut_ptr());
        let expected = core::array::from_fn(|lane| match op {
            BinOp::And => i8_lhs[lane] & i8_rhs[lane],
            BinOp::Or => i8_lhs[lane] | i8_rhs[lane],
            BinOp::Xor => i8_lhs[lane] ^ i8_rhs[lane],
            _ => unreachable!("narrow bitwise canaries only use And/Or/Xor"),
        });
        assert_eq!(
            output, expected,
            "{name} should preserve all <16 x i8> trust_ir bitwise lanes"
        );
    }

    let i16_lhs: [i16; 8] = [0x5555, -1, i16::MIN, 0x1234, 0, 1, 0x7F00, -0x2100];
    let i16_rhs: [i16; 8] = [0x3333, 0, -1, 0x0F0F, -1, -2, 0x70F0, 0x20FF];

    for (index, (suffix, op, sse2_opcode)) in [
        ("and", BinOp::And, 0xDB),
        ("or", BinOp::Or, 0xEB),
        ("xor", BinOp::Xor, 0xEF),
    ]
    .into_iter()
    .enumerate()
    {
        let name = format!("v8i16_{suffix}_bitwise_lane_values");
        let module =
            build_narrow_bitwise_store_module(8923 + index as u32, &name, v8i16_ty(), op.clone());
        let result = host_jit_o0_compiler()
            .compile_module_to_jit(&module, &HashMap::new())
            .unwrap_or_else(|err| panic!("x86-64 host JIT should compile {name}: {err}"));
        assert_metrics_code_size_matches_replay(&result, &name);
        let metrics = metrics_for(&result, &name);
        let code = jit_symbol_code_bytes(&result, &name);
        assert_eq!(metrics.x86_machine_code.target_features, host);
        assert_eq!(
            metrics.x86_machine_code.pand_count,
            usize::from(op == BinOp::And),
            "{name}: {:?}",
            metrics.x86_machine_code
        );
        assert_eq!(
            metrics.x86_machine_code.por_count,
            usize::from(op == BinOp::Or),
            "{name}: {:?}",
            metrics.x86_machine_code
        );
        assert_eq!(
            metrics.x86_machine_code.pxor_count,
            usize::from(op == BinOp::Xor),
            "{name}: {:?}",
            metrics.x86_machine_code
        );
        assert_no_scalar_lane_fallback(&metrics.x86_machine_code, &name);
        assert_eq!(metrics.x86_machine_code.movd_to_xmm_count, 0, "{name}");
        assert_eq!(metrics.x86_machine_code.movq_to_xmm_count, 0, "{name}");
        assert!(
            contains_sse2_opcode(code, sse2_opcode),
            "{name} must encode legacy SSE2 bitwise opcode {sse2_opcode:#04x}: {code:02X?}"
        );
        assert!(
            !contains_vex_instruction_prefix(code),
            "{name} must stay on legacy XMM/SSE encodings without VEX/YMM lowering: {code:02X?}"
        );

        let run: extern "C" fn(*const i16, *const i16, *mut i16) = unsafe {
            result
                .buffer
                .get_fn_bound(&name)
                .unwrap_or_else(|| panic!("{name} symbol must be present"))
                .into_inner()
        };
        let mut output = [0i16; 8];
        run(i16_lhs.as_ptr(), i16_rhs.as_ptr(), output.as_mut_ptr());
        let expected = core::array::from_fn(|lane| match op {
            BinOp::And => i16_lhs[lane] & i16_rhs[lane],
            BinOp::Or => i16_lhs[lane] | i16_rhs[lane],
            BinOp::Xor => i16_lhs[lane] ^ i16_rhs[lane],
            _ => unreachable!("narrow bitwise canaries only use And/Or/Xor"),
        });
        assert_eq!(
            output, expected,
            "{name} should preserve all <8 x i16> trust_ir bitwise lanes"
        );
    }
}

#[test]
fn test_x86_64_jit_narrow_i8_i16_eq_ne_masks_use_pcmpeq_legacy_sse2() {
    let generic_sse2 = X86TargetFeatures::generic_x86_64();

    for (name, opcode, expected_pcmpeq_opcode, expected_pcmp_count) in [
        (
            "v16i8_eq_pcmpeqb",
            Opcode::V16I8Icmp { cond: IntCC::Equal },
            0x74,
            (1, 0),
        ),
        (
            "v16i8_ne_pcmpeqb",
            Opcode::V16I8Icmp {
                cond: IntCC::NotEqual,
            },
            0x74,
            (1, 0),
        ),
        (
            "v8i16_eq_pcmpeqw",
            Opcode::V8I16Icmp { cond: IntCC::Equal },
            0x75,
            (0, 1),
        ),
        (
            "v8i16_ne_pcmpeqw",
            Opcode::V8I16Icmp {
                cond: IntCC::NotEqual,
            },
            0x75,
            (0, 1),
        ),
    ] {
        let func = build_v128_i32_binop_store_function(name, opcode.clone());
        let (code, evidence) = compile_lir_o0_raw_with_features(&func, generic_sse2)
            .unwrap_or_else(|err| panic!("{name} should compile under generic SSE2: {err}"));
        assert_eq!(evidence.machine_code.target_features, generic_sse2);
        assert_eq!(evidence.machine_code.pcmpeqb_count, expected_pcmp_count.0);
        assert_eq!(evidence.machine_code.pcmpeqw_count, expected_pcmp_count.1);
        if matches!(
            opcode,
            Opcode::V16I8Icmp {
                cond: IntCC::NotEqual
            } | Opcode::V8I16Icmp {
                cond: IntCC::NotEqual
            }
        ) {
            assert!(
                evidence.machine_code.pcmpeqd_count >= 1 && evidence.machine_code.pxor_count >= 1,
                "{name} NotEqual must invert the Eq mask with all-ones PCMPEQD plus PXOR: {:?}",
                evidence.machine_code
            );
        }
        assert!(
            contains_sse2_opcode(&code, expected_pcmpeq_opcode),
            "{name} must encode legacy PCMPEQB/PCMPEQW bytes, code={code:02X?}"
        );
        assert!(
            !contains_vex_instruction_prefix(&code),
            "{name} must not emit VEX/YMM instructions under generic SSE2, code={code:02X?}"
        );

        match opcode {
            Opcode::V16I8Icmp { cond } => {
                let page = ExecPage::new(&code);
                // SAFETY: `page` contains a System V function taking three
                // pointer-sized arguments and returning void.
                let run: extern "C" fn(*const i8, *const i8, *mut i8) =
                    unsafe { core::mem::transmute(page.as_ptr()) };

                for (lhs, rhs) in [
                    (
                        [
                            0,
                            1,
                            -1,
                            i8::MIN,
                            i8::MAX,
                            5,
                            6,
                            7,
                            8,
                            9,
                            10,
                            11,
                            12,
                            13,
                            14,
                            15,
                        ],
                        [
                            0,
                            0,
                            -1,
                            i8::MAX,
                            i8::MAX,
                            4,
                            6,
                            -7,
                            8,
                            -9,
                            99,
                            11,
                            -12,
                            13,
                            0,
                            15,
                        ],
                    ),
                    (
                        [
                            42, -42, 0, 1, 2, 3, 4, 5, -1, -2, -3, -4, 100, 101, 102, 103,
                        ],
                        [41, -42, 1, 1, -2, 3, 0, 5, -1, 2, -3, 4, 100, 0, 102, -103],
                    ),
                ] {
                    let mut output = [0i8; 16];
                    run(lhs.as_ptr(), rhs.as_ptr(), output.as_mut_ptr());
                    let expected = core::array::from_fn(|lane| {
                        let equal = lhs[lane] == rhs[lane];
                        if matches!(cond, IntCC::Equal) == equal {
                            -1
                        } else {
                            0
                        }
                    });
                    assert_eq!(
                        output, expected,
                        "{name} should produce all-ones/zero i8 mask lanes"
                    );
                }
            }
            Opcode::V8I16Icmp { cond } => {
                let page = ExecPage::new(&code);
                // SAFETY: `page` contains a System V function taking three
                // pointer-sized arguments and returning void.
                let run: extern "C" fn(*const i16, *const i16, *mut i16) =
                    unsafe { core::mem::transmute(page.as_ptr()) };

                for (lhs, rhs) in [
                    (
                        [0, 1, -1, i16::MIN, i16::MAX, 123, -456, 789],
                        [0, 0, -1, i16::MAX, i16::MAX, -123, -456, -789],
                    ),
                    (
                        [32760, -32760, 0, 1, 2, 3, 4, 5],
                        [32760, 32760, 1, 1, -2, 3, 0, 5],
                    ),
                ] {
                    let mut output = [0i16; 8];
                    run(lhs.as_ptr(), rhs.as_ptr(), output.as_mut_ptr());
                    let expected = core::array::from_fn(|lane| {
                        let equal = lhs[lane] == rhs[lane];
                        if matches!(cond, IntCC::Equal) == equal {
                            -1
                        } else {
                            0
                        }
                    });
                    assert_eq!(
                        output, expected,
                        "{name} should produce all-ones/zero i16 mask lanes"
                    );
                }
            }
            _ => unreachable!("narrow compare cases only"),
        }
    }
}

#[test]
fn test_x86_64_jit_narrow_i8_i16_eq_ne_mask_to_bits_lane_order_and_upper_zero() {
    let host = X86TargetFeatures::host();
    let i8_cases: [([i8; 16], [i8; 16], u32); 2] = [
        (
            [
                0,
                1,
                -1,
                i8::MIN,
                i8::MAX,
                5,
                6,
                7,
                8,
                9,
                10,
                11,
                12,
                13,
                14,
                15,
            ],
            [
                0,
                0,
                -1,
                i8::MAX,
                i8::MAX,
                4,
                6,
                -7,
                8,
                -9,
                99,
                11,
                -12,
                13,
                0,
                15,
            ],
            0xA955,
        ),
        (
            [
                42, -42, 0, 1, 2, 3, 4, 5, -1, -2, -3, -4, 100, 101, 102, 103,
            ],
            [41, -42, 1, 1, -2, 3, 0, 5, -1, 2, -3, 4, 100, 0, 102, -103],
            0x55AA,
        ),
    ];

    for (index, (suffix, op)) in [(0, ("eq", ICmpOp::Eq)), (1, ("ne", ICmpOp::Ne))] {
        let name = format!("v16i8_{suffix}_mask_to_bits_lane_order");
        let module = build_narrow_cmp_mask_to_bits_return_module(
            8850 + index,
            &name,
            v16i8_ty(),
            v16_bool_ty(),
            op,
        );
        let lir_func = single_translated_lir_function(&module);
        let (raw_code, raw_evidence) = compile_lir_o0_raw_with_features(&lir_func, host)
            .unwrap_or_else(|err| panic!("{name} should compile as host raw code: {err}"));
        assert_eq!(raw_evidence.machine_code.target_features, host);
        assert_eq!(raw_evidence.machine_code.pcmpeqb_count, 1);
        assert_eq!(raw_evidence.machine_code.pmovmskb_count, 1);
        assert_eq!(raw_evidence.machine_code.pinsrd_count, 0);
        assert_eq!(raw_evidence.machine_code.pextrd_count, 0);
        assert!(
            contains_sse2_opcode(&raw_code, 0x74) && contains_sse2_opcode(&raw_code, 0xD7),
            "{name} must encode legacy PCMPEQB plus PMOVMSKB bytes: {raw_code:02X?}"
        );
        assert!(
            !contains_vex_instruction_prefix(&raw_code),
            "{name} raw mask_to_bits path must stay on legacy XMM/SSE encodings: {raw_code:02X?}"
        );

        let result = host_jit_o0_compiler()
            .compile_module_to_jit(&module, &HashMap::new())
            .unwrap_or_else(|err| panic!("x86-64 host JIT should compile {name}: {err}"));
        assert_metrics_code_size_matches_replay(&result, &name);
        let metrics = metrics_for(&result, &name);
        let jit_code = jit_symbol_code_bytes(&result, &name);
        assert_eq!(metrics.x86_machine_code.pcmpeqb_count, 1);
        assert_eq!(
            metrics.x86_machine_code.pmovmskb_count, 1,
            "{name} should compact <16 x bool> with exactly one PMOVMSKB: {:?}",
            metrics.x86_machine_code
        );
        assert_eq!(metrics.x86_machine_code.pinsrd_count, 0);
        assert_eq!(metrics.x86_machine_code.pinsrq_count, 0);
        assert_eq!(metrics.x86_machine_code.pextrd_count, 0);
        assert_eq!(metrics.x86_machine_code.pextrq_count, 0);
        assert!(
            !contains_vex_instruction_prefix(jit_code),
            "{name} JIT mask_to_bits path must stay on legacy XMM/SSE encodings: {jit_code:02X?}"
        );

        let run: extern "C" fn(*const i8, *const i8) -> u32 = unsafe {
            result
                .buffer
                .get_fn_bound(&name)
                .unwrap_or_else(|| panic!("{name} symbol must be present"))
                .into_inner()
        };

        for (lhs, rhs, eq_mask) in i8_cases {
            assert_eq!(
                expected_v16i8_cmp_lane_bits(ICmpOp::Eq, lhs, rhs),
                eq_mask,
                "{name} fixture should keep the handoff eq mask literal honest"
            );
            let expected = if op == ICmpOp::Eq {
                eq_mask
            } else {
                (!eq_mask) & 0xFFFF
            };
            let actual = run(lhs.as_ptr(), rhs.as_ptr());
            assert_eq!(
                actual, expected,
                "{name} lhs={lhs:?} rhs={rhs:?} must return bitN for laneN"
            );
            assert_eq!(
                actual & !0xFFFF,
                0,
                "{name} must zero all bits above the 16 lane bits"
            );
        }
    }

    let i16_cases: [([i16; 8], [i16; 8], u32); 2] = [
        (
            [0, 1, -1, i16::MIN, i16::MAX, 123, -456, 789],
            [0, 0, -1, i16::MAX, i16::MAX, -123, -456, -789],
            0x55,
        ),
        (
            [32760, -32760, 0, 1, 2, 3, 4, 5],
            [32760, 32760, 1, 1, -2, 3, 0, 5],
            0xA9,
        ),
    ];

    for (index, (suffix, op)) in [(0, ("eq", ICmpOp::Eq)), (1, ("ne", ICmpOp::Ne))] {
        let name = format!("v8i16_{suffix}_mask_to_bits_lane_order");
        let module = build_narrow_cmp_mask_to_bits_return_module(
            8860 + index,
            &name,
            v8i16_ty(),
            v8_bool_ty(),
            op,
        );
        let lir_func = single_translated_lir_function(&module);
        let (raw_code, raw_evidence) = compile_lir_o0_raw_with_features(&lir_func, host)
            .unwrap_or_else(|err| panic!("{name} should compile as host raw code: {err}"));
        assert_eq!(raw_evidence.machine_code.target_features, host);
        assert_eq!(raw_evidence.machine_code.pcmpeqw_count, 1);
        assert_eq!(raw_evidence.machine_code.pmovmskb_count, 1);
        assert_eq!(raw_evidence.machine_code.pinsrd_count, 0);
        assert_eq!(raw_evidence.machine_code.pextrd_count, 0);
        assert!(
            contains_sse2_opcode(&raw_code, 0x75) && contains_sse2_opcode(&raw_code, 0xD7),
            "{name} must encode legacy PCMPEQW plus PMOVMSKB bytes: {raw_code:02X?}"
        );
        assert!(
            !contains_vex_instruction_prefix(&raw_code),
            "{name} raw mask_to_bits path must stay on legacy XMM/SSE encodings: {raw_code:02X?}"
        );

        let result = host_jit_o0_compiler()
            .compile_module_to_jit(&module, &HashMap::new())
            .unwrap_or_else(|err| panic!("x86-64 host JIT should compile {name}: {err}"));
        assert_metrics_code_size_matches_replay(&result, &name);
        let metrics = metrics_for(&result, &name);
        let jit_code = jit_symbol_code_bytes(&result, &name);
        assert_eq!(metrics.x86_machine_code.pcmpeqw_count, 1);
        assert_eq!(
            metrics.x86_machine_code.pmovmskb_count, 1,
            "{name} should compact <8 x bool> with exactly one PMOVMSKB: {:?}",
            metrics.x86_machine_code
        );
        assert_eq!(metrics.x86_machine_code.pinsrd_count, 0);
        assert_eq!(metrics.x86_machine_code.pinsrq_count, 0);
        assert_eq!(metrics.x86_machine_code.pextrd_count, 0);
        assert_eq!(metrics.x86_machine_code.pextrq_count, 0);
        assert!(
            !contains_vex_instruction_prefix(jit_code),
            "{name} JIT mask_to_bits path must stay on legacy XMM/SSE encodings: {jit_code:02X?}"
        );

        let run: extern "C" fn(*const i16, *const i16) -> u32 = unsafe {
            result
                .buffer
                .get_fn_bound(&name)
                .unwrap_or_else(|| panic!("{name} symbol must be present"))
                .into_inner()
        };

        for (lhs, rhs, eq_mask) in i16_cases {
            assert_eq!(
                expected_v8i16_cmp_lane_bits(ICmpOp::Eq, lhs, rhs),
                eq_mask,
                "{name} fixture should keep the handoff eq mask literal honest"
            );
            let expected = if op == ICmpOp::Eq {
                eq_mask
            } else {
                (!eq_mask) & 0xFF
            };
            let actual = run(lhs.as_ptr(), rhs.as_ptr());
            assert_eq!(
                actual, expected,
                "{name} lhs={lhs:?} rhs={rhs:?} must return bitN for laneN"
            );
            assert_eq!(
                actual & !0xFF,
                0,
                "{name} must zero all bits above the 8 lane bits"
            );
        }
    }
}

#[test]
fn test_x86_64_jit_canonical_bool_constant_mask_to_bits_lane_order_and_upper_zero() {
    let host = X86TargetFeatures::host();
    for (func_id, name, mask_ty, lanes, true_bits, lane_mask) in [
        (
            8900,
            "v16_bool_canonical_constant_mask_to_bits",
            v16_bool_ty(),
            16,
            0xCA69,
            0xFFFF,
        ),
        (
            8901,
            "v8_bool_canonical_constant_mask_to_bits",
            v8_bool_ty(),
            8,
            0x96,
            0xFF,
        ),
    ] {
        let module =
            build_bool_const_mask_to_bits_return_module(func_id, name, mask_ty, lanes, true_bits);
        let lir_func = single_translated_lir_function(&module);
        let (raw_code, raw_evidence) = compile_lir_o0_raw_with_features(&lir_func, host)
            .unwrap_or_else(|err| panic!("{name} should compile as host raw code: {err}"));
        assert_eq!(raw_evidence.machine_code.target_features, host);
        assert_eq!(
            raw_evidence.machine_code.pmovmskb_count, 1,
            "{name} raw path should compact the canonical bool constant with PMOVMSKB: {:?}",
            raw_evidence.machine_code
        );
        assert_eq!(raw_evidence.machine_code.pcmpeqb_count, 0, "{name}");
        assert_eq!(raw_evidence.machine_code.pcmpeqw_count, 0, "{name}");
        assert_eq!(raw_evidence.machine_code.pcmpgtb_count, 0, "{name}");
        assert_eq!(raw_evidence.machine_code.pcmpgtw_count, 0, "{name}");
        assert_eq!(raw_evidence.machine_code.ptest_count, 0, "{name}");
        assert_eq!(raw_evidence.machine_code.pinsrd_count, 0, "{name}");
        assert_eq!(raw_evidence.machine_code.pinsrq_count, 0, "{name}");
        assert_eq!(raw_evidence.machine_code.pextrd_count, 0, "{name}");
        assert_eq!(raw_evidence.machine_code.pextrq_count, 0, "{name}");
        assert!(
            contains_sse2_opcode(&raw_code, 0xD7),
            "{name} raw path must encode legacy PMOVMSKB bytes: {raw_code:02X?}"
        );
        assert!(
            !contains_vex_instruction_prefix(&raw_code),
            "{name} raw path must stay on legacy XMM/SSE encodings without VEX/YMM lowering: {raw_code:02X?}"
        );

        let result = host_jit_o0_compiler()
            .compile_module_to_jit(&module, &HashMap::new())
            .unwrap_or_else(|err| panic!("x86-64 host JIT should compile {name}: {err}"));
        assert_metrics_code_size_matches_replay(&result, name);
        let metrics = metrics_for(&result, name);
        let jit_code = jit_symbol_code_bytes(&result, name);
        assert_eq!(metrics.x86_machine_code.target_features, host);
        assert_eq!(
            metrics.x86_machine_code.pmovmskb_count, 1,
            "{name} should compact the canonical bool constant with PMOVMSKB: {:?}",
            metrics.x86_machine_code
        );
        assert_eq!(metrics.x86_machine_code.pcmpeqb_count, 0, "{name}");
        assert_eq!(metrics.x86_machine_code.pcmpeqw_count, 0, "{name}");
        assert_eq!(metrics.x86_machine_code.pcmpgtb_count, 0, "{name}");
        assert_eq!(metrics.x86_machine_code.pcmpgtw_count, 0, "{name}");
        assert_eq!(metrics.x86_machine_code.ptest_count, 0, "{name}");
        assert_eq!(metrics.x86_machine_code.pinsrd_count, 0, "{name}");
        assert_eq!(metrics.x86_machine_code.pinsrq_count, 0, "{name}");
        assert_eq!(metrics.x86_machine_code.pextrd_count, 0, "{name}");
        assert_eq!(metrics.x86_machine_code.pextrq_count, 0, "{name}");
        assert_eq!(metrics.x86_machine_code.movd_to_xmm_count, 0, "{name}");
        assert_eq!(metrics.x86_machine_code.movq_to_xmm_count, 0, "{name}");
        assert!(
            contains_sse2_opcode(jit_code, 0xD7),
            "{name} must encode legacy PMOVMSKB bytes: {jit_code:02X?}"
        );
        assert!(
            !contains_vex_instruction_prefix(jit_code),
            "{name} must stay on legacy XMM/SSE encodings without VEX/YMM lowering: {jit_code:02X?}"
        );

        let run: extern "C" fn() -> u32 = unsafe {
            result
                .buffer
                .get_fn_bound(name)
                .unwrap_or_else(|| panic!("{name} symbol must be present"))
                .into_inner()
        };
        let actual = run();
        assert_eq!(
            actual, true_bits,
            "{name} must return bitN for canonical bool constant laneN"
        );
        assert_eq!(
            actual & !lane_mask,
            0,
            "{name} must zero all bits above the canonical bool lanes"
        );
    }
}

#[test]
fn test_x86_64_jit_v4_v2_canonical_bool_constant_mask_to_bits_lane_order_and_upper_zero() {
    let host = X86TargetFeatures::host();
    for (func_id, name, mask_ty, lanes, true_bits, lane_mask) in [
        (
            8912,
            "v4_bool_canonical_constant_mask_to_bits",
            v4_bool_ty(),
            4,
            0b1010,
            0xF,
        ),
        (
            8913,
            "v2_bool_canonical_constant_mask_to_bits",
            v2_bool_ty(),
            2,
            0b10,
            0x3,
        ),
    ] {
        let module =
            build_bool_const_mask_to_bits_return_module(func_id, name, mask_ty, lanes, true_bits);
        let lir_func = single_translated_lir_function(&module);
        let (raw_code, raw_evidence) = compile_lir_o0_raw_with_features(&lir_func, host)
            .unwrap_or_else(|err| panic!("{name} should compile as host raw code: {err}"));
        assert_eq!(raw_evidence.machine_code.target_features, host);
        assert_eq!(
            raw_evidence.machine_code.pmovmskb_count, 1,
            "{name} raw path should compact the canonical V4/V2 bool constant with PMOVMSKB: {:?}",
            raw_evidence.machine_code
        );
        assert_eq!(raw_evidence.machine_code.ptest_count, 0, "{name}");
        assert_eq!(raw_evidence.machine_code.pblendvb_count, 0, "{name}");
        assert_no_scalar_lane_fallback(&raw_evidence.machine_code, name);
        assert!(
            contains_sse2_opcode(&raw_code, 0xD7),
            "{name} raw path must encode legacy PMOVMSKB bytes: {raw_code:02X?}"
        );
        assert!(
            !contains_vex_instruction_prefix(&raw_code),
            "{name} raw path must stay on legacy XMM/SSE encodings without VEX/YMM lowering: {raw_code:02X?}"
        );

        let result = host_jit_o0_compiler()
            .compile_module_to_jit(&module, &HashMap::new())
            .unwrap_or_else(|err| panic!("x86-64 host JIT should compile {name}: {err}"));
        assert_metrics_code_size_matches_replay(&result, name);
        let metrics = metrics_for(&result, name);
        let jit_code = jit_symbol_code_bytes(&result, name);
        assert_eq!(metrics.x86_machine_code.target_features, host);
        assert_eq!(
            metrics.x86_machine_code.pmovmskb_count, 1,
            "{name} should compact the canonical V4/V2 bool constant with PMOVMSKB: {:?}",
            metrics.x86_machine_code
        );
        assert_eq!(metrics.x86_machine_code.ptest_count, 0, "{name}");
        assert_eq!(metrics.x86_machine_code.pblendvb_count, 0, "{name}");
        assert_no_scalar_lane_fallback(&metrics.x86_machine_code, name);
        assert!(
            contains_sse2_opcode(jit_code, 0xD7),
            "{name} must encode legacy PMOVMSKB bytes: {jit_code:02X?}"
        );
        assert!(
            !contains_vex_instruction_prefix(jit_code),
            "{name} must stay on legacy XMM/SSE encodings without VEX/YMM lowering: {jit_code:02X?}"
        );

        let run: extern "C" fn() -> u32 = unsafe {
            result
                .buffer
                .get_fn_bound(name)
                .unwrap_or_else(|| panic!("{name} symbol must be present"))
                .into_inner()
        };
        let actual = run();
        assert_eq!(
            actual, true_bits,
            "{name} must return bitN for canonical bool constant laneN"
        );
        assert_eq!(
            actual & !lane_mask,
            0,
            "{name} must zero all bits above the canonical bool lanes"
        );
    }
}

#[test]
fn test_x86_64_jit_canonical_bool_constant_select_lane_values() {
    let host = X86TargetFeatures::host();
    let host_has_sse41 = host.contains(X86TargetFeature::Sse41);

    let v16_bits = 0xCA69;
    let v16_name = "v16i8_canonical_bool_constant_select_lane_values";
    let v16_module = build_bool_const_select_store_module(
        8902,
        v16_name,
        v16i8_ty(),
        v16_bool_ty(),
        16,
        v16_bits,
    );
    let v16_result = host_jit_o0_compiler()
        .compile_module_to_jit(&v16_module, &HashMap::new())
        .unwrap_or_else(|err| panic!("x86-64 host JIT should compile {v16_name}: {err}"));
    assert_metrics_code_size_matches_replay(&v16_result, v16_name);
    let v16_metrics = metrics_for(&v16_result, v16_name);
    let v16_code = jit_symbol_code_bytes(&v16_result, v16_name);
    assert_eq!(v16_metrics.x86_machine_code.target_features, host);
    assert_eq!(
        v16_metrics.x86_machine_code.pmovmskb_count, 0,
        "{v16_name} should select from the vector mask without PMOVMSKB extraction: {:?}",
        v16_metrics.x86_machine_code
    );
    assert_eq!(v16_metrics.x86_machine_code.pcmpeqb_count, 0, "{v16_name}");
    assert_eq!(v16_metrics.x86_machine_code.pcmpgtb_count, 0, "{v16_name}");
    assert_eq!(v16_metrics.x86_machine_code.pinsrd_count, 0, "{v16_name}");
    assert_eq!(v16_metrics.x86_machine_code.pinsrq_count, 0, "{v16_name}");
    assert_eq!(v16_metrics.x86_machine_code.pextrd_count, 0, "{v16_name}");
    assert_eq!(v16_metrics.x86_machine_code.pextrq_count, 0, "{v16_name}");
    assert_eq!(
        v16_metrics.x86_machine_code.movd_to_xmm_count, 0,
        "{v16_name}"
    );
    assert_eq!(
        v16_metrics.x86_machine_code.movq_to_xmm_count, 0,
        "{v16_name}"
    );
    if host_has_sse41 {
        assert_eq!(v16_metrics.x86_machine_code.pblendvb_count, 1, "{v16_name}");
        assert_eq!(v16_metrics.x86_machine_code.pand_count, 0, "{v16_name}");
        assert_eq!(v16_metrics.x86_machine_code.pandn_count, 0, "{v16_name}");
        assert_eq!(v16_metrics.x86_machine_code.por_count, 0, "{v16_name}");
        assert!(
            contains_sse41_0f38_opcode(v16_code, 0x10),
            "{v16_name} should encode legacy SSE4.1 PBLENDVB: {v16_code:02X?}"
        );
    } else {
        assert_eq!(v16_metrics.x86_machine_code.pblendvb_count, 0, "{v16_name}");
        assert!(
            v16_metrics.x86_machine_code.pand_count >= 1
                && v16_metrics.x86_machine_code.pandn_count >= 1
                && v16_metrics.x86_machine_code.por_count >= 1,
            "{v16_name} should lower through SSE2 PAND/PANDN/POR bitselect: {:?}",
            v16_metrics.x86_machine_code
        );
        assert!(
            contains_sse2_opcode(v16_code, 0xDB)
                && contains_sse2_opcode(v16_code, 0xDF)
                && contains_sse2_opcode(v16_code, 0xEB),
            "{v16_name} should encode legacy SSE2 PAND/PANDN/POR: {v16_code:02X?}"
        );
    }
    assert!(
        !contains_vex_instruction_prefix(v16_code),
        "{v16_name} must stay on legacy XMM/SSE encodings without VEX/YMM lowering: {v16_code:02X?}"
    );

    let run_v16: extern "C" fn(*const i8, *const i8, *mut i8) = unsafe {
        v16_result
            .buffer
            .get_fn_bound(v16_name)
            .unwrap_or_else(|| panic!("{v16_name} symbol must be present"))
            .into_inner()
    };
    let v16_then: [i8; 16] = [
        -120, -110, -100, -90, -80, -70, -60, -50, 50, 60, 70, 80, 90, 100, 110, 120,
    ];
    let v16_else: [i8; 16] = [
        7, 17, 27, 37, 47, 57, 67, 77, -7, -17, -27, -37, -47, -57, -67, -77,
    ];
    let mut v16_output = [0i8; 16];
    run_v16(
        v16_then.as_ptr(),
        v16_else.as_ptr(),
        v16_output.as_mut_ptr(),
    );
    assert_eq!(
        v16_output,
        expected_v16i8_select_from_mask_bits(v16_bits, v16_then, v16_else),
        "{v16_name} should choose unique i8 payload lanes from the canonical bool constant mask"
    );

    let v8_bits = 0x96;
    let v8_name = "v8i16_canonical_bool_constant_select_lane_values";
    let v8_module =
        build_bool_const_select_store_module(8903, v8_name, v8i16_ty(), v8_bool_ty(), 8, v8_bits);
    let v8_result = host_jit_o0_compiler()
        .compile_module_to_jit(&v8_module, &HashMap::new())
        .unwrap_or_else(|err| panic!("x86-64 host JIT should compile {v8_name}: {err}"));
    assert_metrics_code_size_matches_replay(&v8_result, v8_name);
    let v8_metrics = metrics_for(&v8_result, v8_name);
    let v8_code = jit_symbol_code_bytes(&v8_result, v8_name);
    assert_eq!(v8_metrics.x86_machine_code.target_features, host);
    assert_eq!(
        v8_metrics.x86_machine_code.pmovmskb_count, 0,
        "{v8_name} should select from the vector mask without PMOVMSKB extraction: {:?}",
        v8_metrics.x86_machine_code
    );
    assert_eq!(v8_metrics.x86_machine_code.pcmpeqw_count, 0, "{v8_name}");
    assert_eq!(v8_metrics.x86_machine_code.pcmpgtw_count, 0, "{v8_name}");
    assert_eq!(v8_metrics.x86_machine_code.pinsrd_count, 0, "{v8_name}");
    assert_eq!(v8_metrics.x86_machine_code.pinsrq_count, 0, "{v8_name}");
    assert_eq!(v8_metrics.x86_machine_code.pextrd_count, 0, "{v8_name}");
    assert_eq!(v8_metrics.x86_machine_code.pextrq_count, 0, "{v8_name}");
    assert_eq!(
        v8_metrics.x86_machine_code.movd_to_xmm_count, 0,
        "{v8_name}"
    );
    assert_eq!(
        v8_metrics.x86_machine_code.movq_to_xmm_count, 0,
        "{v8_name}"
    );
    if host_has_sse41 {
        assert_eq!(v8_metrics.x86_machine_code.pblendvb_count, 1, "{v8_name}");
        assert_eq!(v8_metrics.x86_machine_code.pand_count, 0, "{v8_name}");
        assert_eq!(v8_metrics.x86_machine_code.pandn_count, 0, "{v8_name}");
        assert_eq!(v8_metrics.x86_machine_code.por_count, 0, "{v8_name}");
        assert!(
            contains_sse41_0f38_opcode(v8_code, 0x10),
            "{v8_name} should encode legacy SSE4.1 PBLENDVB: {v8_code:02X?}"
        );
    } else {
        assert_eq!(v8_metrics.x86_machine_code.pblendvb_count, 0, "{v8_name}");
        assert!(
            v8_metrics.x86_machine_code.pand_count >= 1
                && v8_metrics.x86_machine_code.pandn_count >= 1
                && v8_metrics.x86_machine_code.por_count >= 1,
            "{v8_name} should lower through SSE2 PAND/PANDN/POR bitselect: {:?}",
            v8_metrics.x86_machine_code
        );
        assert!(
            contains_sse2_opcode(v8_code, 0xDB)
                && contains_sse2_opcode(v8_code, 0xDF)
                && contains_sse2_opcode(v8_code, 0xEB),
            "{v8_name} should encode legacy SSE2 PAND/PANDN/POR: {v8_code:02X?}"
        );
    }
    assert!(
        !contains_vex_instruction_prefix(v8_code),
        "{v8_name} must stay on legacy XMM/SSE encodings without VEX/YMM lowering: {v8_code:02X?}"
    );

    let run_v8: extern "C" fn(*const i16, *const i16, *mut i16) = unsafe {
        v8_result
            .buffer
            .get_fn_bound(v8_name)
            .unwrap_or_else(|| panic!("{v8_name} symbol must be present"))
            .into_inner()
    };
    let v8_then: [i16; 8] = [-30000, -21000, -12000, -3000, 3000, 12000, 21000, 30000];
    let v8_else: [i16; 8] = [101, 202, 303, 404, -101, -202, -303, -404];
    let mut v8_output = [0i16; 8];
    run_v8(v8_then.as_ptr(), v8_else.as_ptr(), v8_output.as_mut_ptr());
    assert_eq!(
        v8_output,
        expected_v8i16_select_from_mask_bits(v8_bits, v8_then, v8_else),
        "{v8_name} should choose unique i16 payload lanes from the canonical bool constant mask"
    );
}

#[test]
fn test_x86_64_jit_narrow_i8_i16_compare_mask_select_lane_values() {
    let i8_cmp_lhs: [i8; 16] = [
        0,
        1,
        -1,
        i8::MIN,
        i8::MAX,
        5,
        6,
        7,
        8,
        9,
        10,
        11,
        12,
        13,
        14,
        15,
    ];
    let i8_cmp_rhs: [i8; 16] = [
        0,
        0,
        -1,
        i8::MAX,
        i8::MAX,
        4,
        6,
        -7,
        8,
        -9,
        99,
        11,
        -12,
        13,
        0,
        15,
    ];
    let i8_then: [i8; 16] = [
        -101, -102, -103, -104, -105, -106, -107, -108, 101, 102, 103, 104, 105, 106, 107, 108,
    ];
    let i8_else: [i8; 16] = [
        11, 12, 13, 14, 15, 16, 17, 18, -11, -12, -13, -14, -15, -16, -17, -18,
    ];

    for (index, (suffix, op)) in [("eq", ICmpOp::Eq), ("ne", ICmpOp::Ne), ("slt", ICmpOp::Slt)]
        .into_iter()
        .enumerate()
    {
        let name = format!("v16i8_{suffix}_cmp_mask_select_lane_values");
        let module =
            build_narrow_cmp_select_store_module(8870 + index as u32, &name, v16i8_ty(), op);
        let result = host_jit_o0_compiler()
            .compile_module_to_jit(&module, &HashMap::new())
            .unwrap_or_else(|err| panic!("x86-64 host JIT should compile {name}: {err}"));
        assert_metrics_code_size_matches_replay(&result, &name);
        let metrics = metrics_for(&result, &name);
        match op {
            ICmpOp::Eq | ICmpOp::Ne => assert_eq!(metrics.x86_machine_code.pcmpeqb_count, 1),
            ICmpOp::Slt => assert_eq!(metrics.x86_machine_code.pcmpgtb_count, 1),
            _ => unreachable!("narrow select canary predicates are fixed"),
        }
        assert_eq!(
            metrics.x86_machine_code.pmovmskb_count, 0,
            "{name} should select from the vector mask without PMOVMSKB extraction: {:?}",
            metrics.x86_machine_code
        );
        assert_eq!(metrics.x86_machine_code.pinsrd_count, 0, "{name}");
        assert_eq!(metrics.x86_machine_code.pinsrq_count, 0, "{name}");
        assert_eq!(metrics.x86_machine_code.pextrd_count, 0, "{name}");
        assert_eq!(metrics.x86_machine_code.pextrq_count, 0, "{name}");
        assert!(
            metrics.x86_machine_code.pblendvb_count == 1
                || (metrics.x86_machine_code.pand_count >= 1
                    && metrics.x86_machine_code.pandn_count >= 1
                    && metrics.x86_machine_code.por_count >= 1),
            "{name} should lower vector select through PBLENDVB or SSE2 bitselect: {:?}",
            metrics.x86_machine_code
        );

        let run: extern "C" fn(*const i8, *const i8, *const i8, *const i8, *mut i8) = unsafe {
            result
                .buffer
                .get_fn_bound(&name)
                .unwrap_or_else(|| panic!("{name} symbol must be present"))
                .into_inner()
        };
        let mut output = [0i8; 16];
        run(
            i8_cmp_lhs.as_ptr(),
            i8_cmp_rhs.as_ptr(),
            i8_then.as_ptr(),
            i8_else.as_ptr(),
            output.as_mut_ptr(),
        );
        assert_eq!(
            output,
            expected_v16i8_select(op, i8_cmp_lhs, i8_cmp_rhs, i8_then, i8_else),
            "{name} should choose then/else i8 payload lanes from the compare mask"
        );
    }

    let i16_cmp_lhs: [i16; 8] = [0, 1, -1, i16::MIN, i16::MAX, 123, -456, 789];
    let i16_cmp_rhs: [i16; 8] = [0, 0, -1, i16::MAX, i16::MAX, -123, -456, -789];
    let i16_then: [i16; 8] = [-30001, -30002, -30003, -30004, 30001, 30002, 30003, 30004];
    let i16_else: [i16; 8] = [201, 202, 203, 204, -201, -202, -203, -204];

    for (index, (suffix, op)) in [("eq", ICmpOp::Eq), ("ne", ICmpOp::Ne), ("slt", ICmpOp::Slt)]
        .into_iter()
        .enumerate()
    {
        let name = format!("v8i16_{suffix}_cmp_mask_select_lane_values");
        let module =
            build_narrow_cmp_select_store_module(8880 + index as u32, &name, v8i16_ty(), op);
        let result = host_jit_o0_compiler()
            .compile_module_to_jit(&module, &HashMap::new())
            .unwrap_or_else(|err| panic!("x86-64 host JIT should compile {name}: {err}"));
        assert_metrics_code_size_matches_replay(&result, &name);
        let metrics = metrics_for(&result, &name);
        match op {
            ICmpOp::Eq | ICmpOp::Ne => assert_eq!(metrics.x86_machine_code.pcmpeqw_count, 1),
            ICmpOp::Slt => assert_eq!(metrics.x86_machine_code.pcmpgtw_count, 1),
            _ => unreachable!("narrow select canary predicates are fixed"),
        }
        assert_eq!(
            metrics.x86_machine_code.pmovmskb_count, 0,
            "{name} should select from the vector mask without PMOVMSKB extraction: {:?}",
            metrics.x86_machine_code
        );
        assert_eq!(metrics.x86_machine_code.pinsrd_count, 0, "{name}");
        assert_eq!(metrics.x86_machine_code.pinsrq_count, 0, "{name}");
        assert_eq!(metrics.x86_machine_code.pextrd_count, 0, "{name}");
        assert_eq!(metrics.x86_machine_code.pextrq_count, 0, "{name}");
        assert!(
            metrics.x86_machine_code.pblendvb_count == 1
                || (metrics.x86_machine_code.pand_count >= 1
                    && metrics.x86_machine_code.pandn_count >= 1
                    && metrics.x86_machine_code.por_count >= 1),
            "{name} should lower vector select through PBLENDVB or SSE2 bitselect: {:?}",
            metrics.x86_machine_code
        );

        let run: extern "C" fn(*const i16, *const i16, *const i16, *const i16, *mut i16) = unsafe {
            result
                .buffer
                .get_fn_bound(&name)
                .unwrap_or_else(|| panic!("{name} symbol must be present"))
                .into_inner()
        };
        let mut output = [0i16; 8];
        run(
            i16_cmp_lhs.as_ptr(),
            i16_cmp_rhs.as_ptr(),
            i16_then.as_ptr(),
            i16_else.as_ptr(),
            output.as_mut_ptr(),
        );
        assert_eq!(
            output,
            expected_v8i16_select(op, i16_cmp_lhs, i16_cmp_rhs, i16_then, i16_else),
            "{name} should choose then/else i16 payload lanes from the compare mask"
        );
    }
}

#[test]
fn test_x86_64_jit_v4_v2_compare_vector_select_lane_values() {
    let host = X86TargetFeatures::host();

    let v4_name = "v4i32_slt_cmp_vector_select_lane_values";
    let v4_module = build_narrow_cmp_select_store_module(8914, v4_name, v4i32_ty(), ICmpOp::Slt);
    let v4_result = host_jit_o0_compiler()
        .compile_module_to_jit(&v4_module, &HashMap::new())
        .unwrap_or_else(|err| panic!("x86-64 host JIT should compile {v4_name}: {err}"));
    assert_metrics_code_size_matches_replay(&v4_result, v4_name);
    let v4_metrics = metrics_for(&v4_result, v4_name);
    let v4_code = jit_symbol_code_bytes(&v4_result, v4_name);
    assert_eq!(v4_metrics.x86_machine_code.target_features, host);
    assert_eq!(v4_metrics.x86_machine_code.pcmpgtd_count, 1);
    assert_eq!(
        v4_metrics.x86_machine_code.pmovmskb_count, 0,
        "{v4_name} should select vector payload lanes without mask extraction: {:?}",
        v4_metrics.x86_machine_code
    );
    assert!(
        v4_metrics.x86_machine_code.pblendvb_count == 1
            || (v4_metrics.x86_machine_code.pand_count >= 1
                && v4_metrics.x86_machine_code.pandn_count >= 1
                && v4_metrics.x86_machine_code.por_count >= 1),
        "{v4_name} should lower vector select through PBLENDVB or SSE2 bitselect: {:?}",
        v4_metrics.x86_machine_code
    );
    assert_no_scalar_lane_fallback(&v4_metrics.x86_machine_code, v4_name);
    assert!(
        !contains_vex_instruction_prefix(v4_code),
        "{v4_name} must stay on legacy XMM/SSE encodings without VEX/YMM lowering: {v4_code:02X?}"
    );

    let run_v4: extern "C" fn(*const i32, *const i32, *const i32, *const i32, *mut i32) = unsafe {
        v4_result
            .buffer
            .get_fn_bound(v4_name)
            .unwrap_or_else(|| panic!("{v4_name} symbol must be present"))
            .into_inner()
    };
    let v4_then = [-101, -202, -303, -404];
    let v4_else = [101, 202, 303, 404];
    for (lhs, rhs) in [
        ([0, -5, 7, i32::MIN], [1, -6, 0, i32::MAX]),
        ([9, -20, 30, -40], [1, -10, 20, -50]),
    ] {
        let mut output = [0i32; 4];
        run_v4(
            lhs.as_ptr(),
            rhs.as_ptr(),
            v4_then.as_ptr(),
            v4_else.as_ptr(),
            output.as_mut_ptr(),
        );
        assert_eq!(
            output,
            expected_v4i32_select(ICmpOp::Slt, lhs, rhs, v4_then, v4_else),
            "{v4_name} lhs={lhs:?} rhs={rhs:?} should choose unique i32 payload lanes"
        );
    }

    let v2_name = "v2i64_slt_cmp_vector_select_lane_values";
    let v2_module = build_narrow_cmp_select_store_module(8915, v2_name, v2i64_ty(), ICmpOp::Slt);
    let v2_result = host_jit_o0_compiler()
        .compile_module_to_jit(&v2_module, &HashMap::new())
        .unwrap_or_else(|err| panic!("x86-64 host JIT should compile {v2_name}: {err}"));
    assert_metrics_code_size_matches_replay(&v2_result, v2_name);
    let v2_metrics = metrics_for(&v2_result, v2_name);
    let v2_code = jit_symbol_code_bytes(&v2_result, v2_name);
    assert_eq!(v2_metrics.x86_machine_code.target_features, host);
    assert_eq!(v2_metrics.x86_machine_code.pcmpgtq_count, 1);
    assert_eq!(
        v2_metrics.x86_machine_code.pmovmskb_count, 0,
        "{v2_name} should select vector payload lanes without mask extraction: {:?}",
        v2_metrics.x86_machine_code
    );
    assert!(
        v2_metrics.x86_machine_code.pblendvb_count == 1
            || (v2_metrics.x86_machine_code.pand_count >= 1
                && v2_metrics.x86_machine_code.pandn_count >= 1
                && v2_metrics.x86_machine_code.por_count >= 1),
        "{v2_name} should lower vector select through PBLENDVB or SSE2 bitselect: {:?}",
        v2_metrics.x86_machine_code
    );
    assert_no_scalar_lane_fallback(&v2_metrics.x86_machine_code, v2_name);
    assert!(
        !contains_vex_instruction_prefix(v2_code),
        "{v2_name} must stay on legacy XMM/SSE encodings without VEX/YMM lowering: {v2_code:02X?}"
    );

    let run_v2: extern "C" fn(*const i64, *const i64, *const i64, *const i64, *mut i64) = unsafe {
        v2_result
            .buffer
            .get_fn_bound(v2_name)
            .unwrap_or_else(|| panic!("{v2_name} symbol must be present"))
            .into_inner()
    };
    let v2_then = [i64::MIN + 17, 0x1122_3344_5566_7788];
    let v2_else = [-0x0102_0304_0506_0708, i64::MAX - 9];
    for (lhs, rhs) in [([-10, 9], [0, -1]), ([99, -50], [0, 20])] {
        let mut output = [0i64; 2];
        run_v2(
            lhs.as_ptr(),
            rhs.as_ptr(),
            v2_then.as_ptr(),
            v2_else.as_ptr(),
            output.as_mut_ptr(),
        );
        assert_eq!(
            output,
            expected_v2i64_select(ICmpOp::Slt, lhs, rhs, v2_then, v2_else),
            "{v2_name} lhs={lhs:?} rhs={rhs:?} should choose unique i64 payload lanes"
        );
    }
}

#[test]
fn test_x86_64_jit_narrow_i8_i16_signed_ordered_masks_use_pcmpgt_legacy_sse2() {
    let generic_sse2 = X86TargetFeatures::generic_x86_64();

    for (name, cond, inclusive) in [
        ("v16i8_slt_pcmpgtb", IntCC::SignedLessThan, false),
        ("v16i8_sgt_pcmpgtb", IntCC::SignedGreaterThan, false),
        (
            "v16i8_sle_pcmpgtb_pcmpeqb_por",
            IntCC::SignedLessThanOrEqual,
            true,
        ),
        (
            "v16i8_sge_pcmpgtb_pcmpeqb_por",
            IntCC::SignedGreaterThanOrEqual,
            true,
        ),
    ] {
        let func = build_v128_i32_binop_store_function(name, Opcode::V16I8Icmp { cond });
        let (code, evidence) = compile_lir_o0_raw_with_features(&func, generic_sse2)
            .unwrap_or_else(|err| panic!("{name} should compile under generic SSE2: {err}"));
        assert_eq!(evidence.machine_code.target_features, generic_sse2);
        assert_eq!(evidence.machine_code.pcmpgtb_count, 1, "{name}");
        assert_eq!(
            evidence.machine_code.pcmpeqb_count,
            usize::from(inclusive),
            "{name}"
        );
        assert_eq!(
            evidence.machine_code.por_count,
            usize::from(inclusive),
            "{name}"
        );
        assert_eq!(evidence.machine_code.pcmpgtw_count, 0, "{name}");
        assert_eq!(evidence.machine_code.pcmpeqw_count, 0, "{name}");
        assert!(
            contains_sse2_opcode(&code, 0x64),
            "{name} must encode legacy PCMPGTB bytes, code={code:02X?}"
        );
        if inclusive {
            assert!(
                contains_sse2_opcode(&code, 0x74) && contains_sse2_opcode(&code, 0xEB),
                "{name} must encode PCMPGTB + PCMPEQB + POR, code={code:02X?}"
            );
        }
        assert!(
            !contains_vex_instruction_prefix(&code),
            "{name} must not emit VEX/YMM instructions under generic SSE2, code={code:02X?}"
        );

        let page = ExecPage::new(&code);
        // SAFETY: `page` contains a System V function taking three
        // pointer-sized arguments and returning void.
        let run: extern "C" fn(*const i8, *const i8, *mut i8) =
            unsafe { core::mem::transmute(page.as_ptr()) };

        let lhs: [i8; 16] = [
            i8::MIN,
            i8::MIN,
            -1,
            -1,
            0,
            0,
            1,
            1,
            i8::MAX,
            i8::MAX,
            -1,
            1,
            0,
            i8::MAX,
            i8::MIN,
            1,
        ];
        let rhs: [i8; 16] = [
            i8::MIN,
            -1,
            i8::MIN,
            0,
            -1,
            0,
            0,
            i8::MAX,
            1,
            i8::MAX,
            1,
            -1,
            i8::MIN,
            i8::MIN,
            i8::MAX,
            1,
        ];
        let mut output = [0i8; 16];
        run(lhs.as_ptr(), rhs.as_ptr(), output.as_mut_ptr());
        let expected =
            core::array::from_fn(|lane| expected_i8_signed_mask(cond, lhs[lane], rhs[lane]));
        assert_eq!(
            output, expected,
            "{name} should produce all-ones/zero signed i8 mask lanes"
        );
    }

    for (name, cond, inclusive) in [
        ("v8i16_slt_pcmpgtw", IntCC::SignedLessThan, false),
        ("v8i16_sgt_pcmpgtw", IntCC::SignedGreaterThan, false),
        (
            "v8i16_sle_pcmpgtw_pcmpeqw_por",
            IntCC::SignedLessThanOrEqual,
            true,
        ),
        (
            "v8i16_sge_pcmpgtw_pcmpeqw_por",
            IntCC::SignedGreaterThanOrEqual,
            true,
        ),
    ] {
        let func = build_v128_i32_binop_store_function(name, Opcode::V8I16Icmp { cond });
        let (code, evidence) = compile_lir_o0_raw_with_features(&func, generic_sse2)
            .unwrap_or_else(|err| panic!("{name} should compile under generic SSE2: {err}"));
        assert_eq!(evidence.machine_code.target_features, generic_sse2);
        assert_eq!(evidence.machine_code.pcmpgtw_count, 1, "{name}");
        assert_eq!(
            evidence.machine_code.pcmpeqw_count,
            usize::from(inclusive),
            "{name}"
        );
        assert_eq!(
            evidence.machine_code.por_count,
            usize::from(inclusive),
            "{name}"
        );
        assert_eq!(evidence.machine_code.pcmpgtb_count, 0, "{name}");
        assert_eq!(evidence.machine_code.pcmpeqb_count, 0, "{name}");
        assert!(
            contains_sse2_opcode(&code, 0x65),
            "{name} must encode legacy PCMPGTW bytes, code={code:02X?}"
        );
        if inclusive {
            assert!(
                contains_sse2_opcode(&code, 0x75) && contains_sse2_opcode(&code, 0xEB),
                "{name} must encode PCMPGTW + PCMPEQW + POR, code={code:02X?}"
            );
        }
        assert!(
            !contains_vex_instruction_prefix(&code),
            "{name} must not emit VEX/YMM instructions under generic SSE2, code={code:02X?}"
        );

        let page = ExecPage::new(&code);
        // SAFETY: `page` contains a System V function taking three
        // pointer-sized arguments and returning void.
        let run: extern "C" fn(*const i16, *const i16, *mut i16) =
            unsafe { core::mem::transmute(page.as_ptr()) };

        let lhs: [i16; 8] = [i16::MIN, i16::MIN, -1, 0, 1, i16::MAX, i16::MAX, 1];
        let rhs: [i16; 8] = [i16::MIN, -1, i16::MIN, 0, 0, 1, i16::MAX, i16::MAX];
        let mut output = [0i16; 8];
        run(lhs.as_ptr(), rhs.as_ptr(), output.as_mut_ptr());
        let expected =
            core::array::from_fn(|lane| expected_i16_signed_mask(cond, lhs[lane], rhs[lane]));
        assert_eq!(
            output, expected,
            "{name} should produce all-ones/zero signed i16 mask lanes"
        );
    }
}

#[test]
fn test_x86_64_jit_narrow_i8_i16_unsigned_ordered_masks_use_sse2_sign_bias() {
    let generic_sse2 = X86TargetFeatures::generic_x86_64();

    for (name, cond, inclusive) in [
        ("v16i8_ult_bias_pcmpgtb", IntCC::UnsignedLessThan, false),
        ("v16i8_ugt_bias_pcmpgtb", IntCC::UnsignedGreaterThan, false),
        (
            "v16i8_ule_bias_pcmpgtb_pcmpeqb_por",
            IntCC::UnsignedLessThanOrEqual,
            true,
        ),
        (
            "v16i8_uge_bias_pcmpgtb_pcmpeqb_por",
            IntCC::UnsignedGreaterThanOrEqual,
            true,
        ),
    ] {
        let func = build_v128_i32_binop_store_function(name, Opcode::V16I8Icmp { cond });
        let (code, evidence) = compile_lir_o0_raw_with_features(&func, generic_sse2)
            .unwrap_or_else(|err| panic!("{name} should compile under generic SSE2: {err}"));
        assert_eq!(evidence.machine_code.target_features, generic_sse2);
        assert_eq!(evidence.machine_code.movd_to_xmm_count, 1, "{name}");
        assert_eq!(evidence.machine_code.pshufd_count, 1, "{name}");
        assert_eq!(evidence.machine_code.pxor_count, 2, "{name}");
        assert_eq!(evidence.machine_code.pcmpgtb_count, 1, "{name}");
        assert_eq!(
            evidence.machine_code.pcmpeqb_count,
            usize::from(inclusive),
            "{name}"
        );
        assert_eq!(
            evidence.machine_code.por_count,
            usize::from(inclusive),
            "{name}"
        );
        assert_eq!(evidence.machine_code.pcmpgtw_count, 0, "{name}");
        assert_eq!(evidence.machine_code.pcmpeqw_count, 0, "{name}");
        assert!(
            contains_sse2_opcode(&code, 0x64) && contains_sse2_opcode(&code, 0xEF),
            "{name} must encode legacy PCMPGTB plus PXOR sign-bias bytes, code={code:02X?}"
        );
        assert!(
            !contains_vex_instruction_prefix(&code),
            "{name} must not emit VEX/YMM instructions under generic SSE2, code={code:02X?}"
        );

        let page = ExecPage::new(&code);
        // SAFETY: `page` contains a System V function taking three
        // pointer-sized arguments and returning void.
        let run: extern "C" fn(*const i8, *const i8, *mut i8) =
            unsafe { core::mem::transmute(page.as_ptr()) };

        let lhs: [i8; 16] = [
            i8::MIN,
            i8::MIN,
            -1,
            -1,
            0,
            0,
            1,
            1,
            i8::MAX,
            i8::MAX,
            -128,
            127,
            -1,
            0,
            42,
            -42,
        ];
        let rhs: [i8; 16] = [
            i8::MIN,
            -1,
            i8::MIN,
            0,
            -1,
            0,
            0,
            i8::MAX,
            1,
            i8::MAX,
            127,
            -128,
            0,
            -1,
            -42,
            42,
        ];
        let mut output = [0i8; 16];
        run(lhs.as_ptr(), rhs.as_ptr(), output.as_mut_ptr());
        let expected =
            core::array::from_fn(|lane| expected_i8_unsigned_mask(cond, lhs[lane], rhs[lane]));
        assert_eq!(
            output, expected,
            "{name} should produce all-ones/zero unsigned i8 mask lanes"
        );
    }

    for (name, cond, inclusive) in [
        ("v8i16_ult_bias_pcmpgtw", IntCC::UnsignedLessThan, false),
        ("v8i16_ugt_bias_pcmpgtw", IntCC::UnsignedGreaterThan, false),
        (
            "v8i16_ule_bias_pcmpgtw_pcmpeqw_por",
            IntCC::UnsignedLessThanOrEqual,
            true,
        ),
        (
            "v8i16_uge_bias_pcmpgtw_pcmpeqw_por",
            IntCC::UnsignedGreaterThanOrEqual,
            true,
        ),
    ] {
        let func = build_v128_i32_binop_store_function(name, Opcode::V8I16Icmp { cond });
        let (code, evidence) = compile_lir_o0_raw_with_features(&func, generic_sse2)
            .unwrap_or_else(|err| panic!("{name} should compile under generic SSE2: {err}"));
        assert_eq!(evidence.machine_code.target_features, generic_sse2);
        assert_eq!(evidence.machine_code.movd_to_xmm_count, 1, "{name}");
        assert_eq!(evidence.machine_code.pshufd_count, 1, "{name}");
        assert_eq!(evidence.machine_code.pxor_count, 2, "{name}");
        assert_eq!(evidence.machine_code.pcmpgtw_count, 1, "{name}");
        assert_eq!(
            evidence.machine_code.pcmpeqw_count,
            usize::from(inclusive),
            "{name}"
        );
        assert_eq!(
            evidence.machine_code.por_count,
            usize::from(inclusive),
            "{name}"
        );
        assert_eq!(evidence.machine_code.pcmpgtb_count, 0, "{name}");
        assert_eq!(evidence.machine_code.pcmpeqb_count, 0, "{name}");
        assert!(
            contains_sse2_opcode(&code, 0x65) && contains_sse2_opcode(&code, 0xEF),
            "{name} must encode legacy PCMPGTW plus PXOR sign-bias bytes, code={code:02X?}"
        );
        assert!(
            !contains_vex_instruction_prefix(&code),
            "{name} must not emit VEX/YMM instructions under generic SSE2, code={code:02X?}"
        );

        let page = ExecPage::new(&code);
        // SAFETY: `page` contains a System V function taking three
        // pointer-sized arguments and returning void.
        let run: extern "C" fn(*const i16, *const i16, *mut i16) =
            unsafe { core::mem::transmute(page.as_ptr()) };

        let lhs: [i16; 8] = [i16::MIN, i16::MIN, -1, 0, 1, i16::MAX, i16::MAX, -12345];
        let rhs: [i16; 8] = [i16::MIN, -1, i16::MIN, 0, 0, 1, i16::MAX, 12345];
        let mut output = [0i16; 8];
        run(lhs.as_ptr(), rhs.as_ptr(), output.as_mut_ptr());
        let expected =
            core::array::from_fn(|lane| expected_i16_unsigned_mask(cond, lhs[lane], rhs[lane]));
        assert_eq!(
            output, expected,
            "{name} should produce all-ones/zero unsigned i16 mask lanes"
        );
    }
}

#[test]
fn test_x86_64_jit_v128_i32_imul_uses_pmulld_for_all_lanes() {
    let func = build_v128_i32_binop_store_function("v128_i32_imul_all_lanes", Opcode::Imul);
    let code = compile_lir_leaf(&func);
    assert!(
        contains_sse41_0f38_opcode(&code, 0x40),
        "V128 Imul must encode native PMULLD bytes, code={code:02X?}"
    );

    let page = ExecPage::new(&code);
    // SAFETY: `page` contains a leaf System V function taking three
    // pointer-sized integer arguments and returning void.
    let f: extern "C" fn(*const i32, *const i32, *mut i32) =
        unsafe { core::mem::transmute(page.as_ptr()) };

    let lhs = [1i32, -2, 46341, i32::MIN];
    let rhs = [10i32, -20, 46341, -1];
    let mut output = [0i32; 4];
    f(lhs.as_ptr(), rhs.as_ptr(), output.as_mut_ptr());

    assert_eq!(
        output,
        [
            lhs[0].wrapping_mul(rhs[0]),
            lhs[1].wrapping_mul(rhs[1]),
            lhs[2].wrapping_mul(rhs[2]),
            lhs[3].wrapping_mul(rhs[3]),
        ]
    );
}

#[test]
fn test_x86_64_jit_v128_i32_bitwise_ops_use_legacy_sse2_without_vex() {
    let lhs = [0x5555_5555i32, -1, i32::MIN, 0x1234_5678];
    let rhs = [0x3333_3333i32, 0, -1, 0x0F0F_0F0F];
    let cases = [
        ("pand", Opcode::Band, 0xDB),
        ("por", Opcode::Bor, 0xEB),
        ("pxor", Opcode::Bxor, 0xEF),
    ];

    for (name, opcode, sse2_opcode) in cases {
        let func =
            build_v128_i32_binop_store_function(&format!("v128_i32_{name}_all_lanes"), opcode);
        let code = compile_lir_leaf(&func);
        assert!(
            contains_sse2_opcode(&code, sse2_opcode),
            "V128 {name} must encode native legacy SSE2 bytes, code={code:02X?}"
        );
        assert!(
            !code.contains(&0xC4) && !code.contains(&0xC5),
            "V128 {name} should not require VEX/YMM encoding, code={code:02X?}"
        );

        let page = ExecPage::new(&code);
        // SAFETY: `page` contains a leaf System V function taking three
        // pointer-sized integer arguments and returning void.
        let run: extern "C" fn(*const i32, *const i32, *mut i32) =
            unsafe { core::mem::transmute(page.as_ptr()) };

        let mut output = [0i32; 4];
        run(lhs.as_ptr(), rhs.as_ptr(), output.as_mut_ptr());
        let expected = core::array::from_fn(|lane| match name {
            "pand" => lhs[lane] & rhs[lane],
            "por" => lhs[lane] | rhs[lane],
            "pxor" => lhs[lane] ^ rhs[lane],
            other => panic!("unknown packed bitwise op {other}"),
        });
        assert_eq!(
            output, expected,
            "V128 {name} should compute each i32 lane independently"
        );
    }
}

#[test]
fn test_x86_64_jit_v4i32_uniform_const_shifts_use_sse2_immediates_counts_0_1_7_31() {
    let lhs = [1i32, -1, i32::MIN, 0x4000_0001];
    let cases = [
        ("ishl", BinOp::Shl, 6),
        ("ushr", BinOp::LShr, 2),
        ("sshr", BinOp::AShr, 4),
    ];

    for count in [0, 1, 7, 31] {
        for (op_name, op, subopcode) in &cases {
            let name = format!("v4i32_uniform_const_shift_{op_name}_{count}");
            let module = build_v4i32_uniform_const_shift_module(
                8920 + count as u32,
                &name,
                op.clone(),
                count,
            );
            let result = host_jit_o0_compiler()
                .compile_module_to_jit(&module, &HashMap::new())
                .unwrap_or_else(|err| panic!("x86-64 host JIT should compile {name}: {err}"));

            assert_metrics_code_size_matches_replay(&result, &name);
            let metrics = metrics_for(&result, &name);
            let code = jit_symbol_code_bytes(&result, &name);
            eprintln!(
                "x86 JIT uniform v4i32 shift canary op={op_name} count={count}: code_size={}, metrics={:?}",
                metrics.code_size_bytes, metrics.x86_machine_code
            );
            assert!(
                contains_packed_dword_shift_imm(code, *subopcode, count as u8),
                "{name} should encode 66 0F 72 /{subopcode} ib: {code:02X?}"
            );
            assert!(
                !code.contains(&0xD3),
                "{name} should not use scalar D3 shifts for a uniform constant count: {code:02X?}"
            );
            assert_eq!(
                metrics.x86_machine_code.movd_to_xmm_count, 0,
                "{name} should not materialize scalar dword lanes through MOVD: {:?}",
                metrics.x86_machine_code
            );
            assert_eq!(
                metrics.x86_machine_code.punpckldq_count, 0,
                "{name} should not reassemble dword pairs with PUNPCKLDQ: {:?}",
                metrics.x86_machine_code
            );
            assert_eq!(
                metrics.x86_machine_code.punpcklqdq_count, 0,
                "{name} should not reassemble qword pairs with PUNPCKLQDQ: {:?}",
                metrics.x86_machine_code
            );
            assert!(
                !contains_vex_instruction_prefix(code),
                "{name} should stay on legacy SSE encodings without VEX/YMM lowering: {code:02X?}"
            );

            let run: extern "C" fn(*const i32, *mut i32) = unsafe {
                result
                    .buffer
                    .get_fn_bound(&name)
                    .unwrap_or_else(|| panic!("{name} symbol must be present"))
                    .into_inner()
            };
            let mut output = [0i32; 4];
            run(lhs.as_ptr(), output.as_mut_ptr());
            let expected = core::array::from_fn(|lane| {
                expected_v4i32_shift_lane(op_name, lhs[lane], count as i32)
            });
            assert_eq!(
                output, expected,
                "{name} should shift every lane by the same immediate count"
            );
        }
    }
}

#[test]
fn test_x86_64_jit_v4i32_scalarized_lane_shifts_execute_counts_0_to_31() {
    let lhs = [1i32, -1, i32::MIN, 0x4000_0001];
    let opcodes = [
        ("ishl", Opcode::Ishl),
        ("ushr", Opcode::Ushr),
        ("sshr", Opcode::Sshr),
    ];

    for (name, opcode) in opcodes {
        let func = build_v128_i32_binop_store_function(
            &format!("v4i32_scalarized_lane_shift_{name}"),
            opcode,
        );
        let code = compile_lir_leaf(&func);
        assert!(
            contains_sse2_opcode(&code, 0x62),
            "{name} should reassemble dword pairs with PUNPCKLDQ, code={code:02X?}"
        );
        assert!(
            contains_sse2_opcode(&code, 0x6C),
            "{name} should join dword pairs with PUNPCKLQDQ, code={code:02X?}"
        );
        assert!(
            !contains_sse41_0f3a_opcode(&code, 0x22),
            "{name} should not reassemble lanes with PINSRD, code={code:02X?}"
        );
        assert!(
            !contains_sse41_0f3a_opcode(&code, 0x16),
            "{name} should not extract lanes with PEXTRD, code={code:02X?}"
        );
        assert!(
            code.contains(&0xD3),
            "{name} should preserve scalar D3 variable-count shifts for lane-wise counts, code={code:02X?}"
        );
        assert!(
            !contains_any_packed_dword_shift_imm(&code),
            "{name} should not use a packed immediate shift for lane-wise variable counts, code={code:02X?}"
        );

        let page = ExecPage::new(&code);
        // SAFETY: `page` contains a leaf System V function taking three
        // pointer-sized integer arguments and returning void.
        let run: extern "C" fn(*const i32, *const i32, *mut i32) =
            unsafe { core::mem::transmute(page.as_ptr()) };

        for base_count in (0i32..32).step_by(4) {
            let counts = [base_count, base_count + 1, base_count + 2, base_count + 3];
            let mut output = [0i32; 4];
            run(lhs.as_ptr(), counts.as_ptr(), output.as_mut_ptr());

            let expected = [
                expected_v4i32_shift_lane(name, lhs[0], counts[0]),
                expected_v4i32_shift_lane(name, lhs[1], counts[1]),
                expected_v4i32_shift_lane(name, lhs[2], counts[2]),
                expected_v4i32_shift_lane(name, lhs[3], counts[3]),
            ];
            assert_eq!(
                output, expected,
                "{name} counts {counts:?} should shift each lane independently"
            );
        }
    }
}

fn expected_v4i32_shift_lane(op: &str, value: i32, count: i32) -> i32 {
    let count = u32::try_from(count).expect("test shift count must be nonnegative");
    match op {
        "ishl" => value.wrapping_shl(count),
        "ushr" => ((value as u32) >> count) as i32,
        "sshr" => value >> count,
        other => panic!("unknown v4i32 shift op {other}"),
    }
}

#[test]
fn test_x86_64_jit_v2i64_add_uses_paddq_with_wrapping_lanes() {
    let func = build_v2i64_binop_store_function("v2i64_add_wrapping_lanes", Opcode::V2I64Add);
    let code = compile_lir_leaf(&func);
    assert!(
        contains_sse2_opcode(&code, 0xD4),
        "V2I64Add must encode native PADDQ bytes, code={code:02X?}"
    );

    let page = ExecPage::new(&code);
    // SAFETY: `page` contains a leaf System V function taking three
    // pointer-sized integer arguments and returning void.
    let f: extern "C" fn(*const i64, *const i64, *mut i64) =
        unsafe { core::mem::transmute(page.as_ptr()) };

    let lhs = [1i64, i64::MAX];
    let rhs = [-7i64, 1];
    let mut output = [0i64; 2];
    f(lhs.as_ptr(), rhs.as_ptr(), output.as_mut_ptr());

    assert_eq!(
        output,
        [lhs[0].wrapping_add(rhs[0]), lhs[1].wrapping_add(rhs[1]),]
    );
}

#[test]
fn test_x86_64_jit_v2i64_sub_uses_psubq_with_wrapping_lanes() {
    let func = build_v2i64_binop_store_function("v2i64_sub_wrapping_lanes", Opcode::V2I64Sub);
    let code = compile_lir_leaf(&func);
    assert!(
        contains_sse2_opcode(&code, 0xFB),
        "V2I64Sub must encode native PSUBQ bytes, code={code:02X?}"
    );

    let page = ExecPage::new(&code);
    // SAFETY: `page` contains a leaf System V function taking three
    // pointer-sized integer arguments and returning void.
    let f: extern "C" fn(*const i64, *const i64, *mut i64) =
        unsafe { core::mem::transmute(page.as_ptr()) };

    let lhs = [1i64, i64::MIN];
    let rhs = [7i64, 1];
    let mut output = [0i64; 2];
    f(lhs.as_ptr(), rhs.as_ptr(), output.as_mut_ptr());

    assert_eq!(
        output,
        [lhs[0].wrapping_sub(rhs[0]), lhs[1].wrapping_sub(rhs[1]),]
    );
}
