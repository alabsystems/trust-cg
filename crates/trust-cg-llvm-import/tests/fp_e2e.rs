#![cfg(feature = "driver")]

// trust-cg-llvm-import / tests / fp_e2e.rs
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// End-to-end test for expansion item #3 (floating-point types + ops):
// take clang-O0-shaped LL snippets that use `half` / `float` / `double`
// and drive them through the full codegen pipeline to AArch64 objects.
//
// Goals:
//   LL -> trust_ir (this crate)
//     -> trust-cg-lower MachIR (FP BinOp / FCmp / FP casts)
//       -> trust-cg-opt / trust-cg-regalloc / trust-cg-codegen
//         -> Mach-O bytes (aarch64-apple-darwin) and ELF bytes
//            (aarch64-unknown-linux-gnu).
//
// Every compile names its target triple, so the object container, calling
// convention and optional-ISA contract never depend on the host running the
// test (`Compiler::new` would derive all three from the host). FEAT_FP16
// scalar arithmetic is part of Apple's AOT contract but refused by name on
// the generic Linux baseline; the f16 rows compile under the explicit
// `AArch64IsaProfile::FP16` profile and pin both contracts.
//
// Hermetic: the `.ll` is embedded as a string constant (verified by
// hand against Apple clang 17.0.0 on 2026-04-20, arm64-apple-macosx).
// These embedded import/object tests do not require a system `clang`,
// and nothing here runs the emitted code.

use trust_cg_codegen::compiler::{CompileError, Compiler, CompilerConfig, CompilerTraceLevel};
use trust_cg_codegen::macho::linker::MachOParser;
use trust_cg_codegen::pipeline::{OptLevel, PipelineError};
use trust_cg_codegen::target::{AArch64IsaProfile, TargetSpec};
use trust_cg_llvm_import::import_text;

/// Apple arm64: Mach-O, DarwinPCS, and an AOT contract that admits FEAT_FP16.
const APPLE: &str = "aarch64-apple-darwin";
/// Generic Linux AArch64: ELF, AAPCS64, and a baseline without FEAT_FP16.
const LINUX: &str = "aarch64-unknown-linux-gnu";
/// Every program below is compiled for both explicit targets.
const TARGETS: [&str; 2] = [APPLE, LINUX];

/// The generic-baseline refusal for the binary16 constant that
/// `LL_ADD_F16_CONST` materializes (FMOV Hd, #imm or FMOV Hd, Wn).
const FP16_CONSTANT_REFUSAL: &str = "AArch64 FEAT_FP16 is not admitted for FMOV-immediate/GPR-to-H \
     f16 constant; the generic AArch64 baseline may only transport f16 values and convert f16 \
     <-> f32/f64";

/// The f32 program: `float add(float a, float b) { return a + b; }`.
/// Clang -O0 spills params to alloca + reloads before the fadd — we
/// preserve that shape to exercise the real load/store/fadd sequence.
const LL_ADD_F32: &str = r#"
define float @add_f(float %0, float %1) {
  %3 = alloca float, align 4
  %4 = alloca float, align 4
  store float %0, ptr %3, align 4
  store float %1, ptr %4, align 4
  %5 = load float, ptr %3, align 4
  %6 = load float, ptr %4, align 4
  %7 = fadd float %5, %6
  ret float %7
}
"#;

/// The f64 program: `double add(double a, double b) { return a + b; }`.
const LL_ADD_F64: &str = r#"
define double @add_d(double %0, double %1) {
  %3 = alloca double, align 8
  %4 = alloca double, align 8
  store double %0, ptr %3, align 8
  store double %1, ptr %4, align 8
  %5 = load double, ptr %3, align 8
  %6 = load double, ptr %4, align 8
  %7 = fadd double %5, %6
  ret double %7
}
"#;

/// The f16 program: `half add_one(half a) { return a + (half)1.0; }`.
///
/// LLVM textual IR spells half-precision bit-pattern constants as
/// `0xH....`; `0xH3C00` is binary16 1.0.
const LL_ADD_F16_CONST: &str = r#"
define half @add_h_one(half %0) {
entry:
  %1 = fadd half %0, 0xH3C00
  ret half %1
}
"#;

/// The fcmp-branch program:
///   `int cmp_lt(double x, double y) { if (x < y) return 1; else return 2; }`.
///
/// This is the hand-simplified shape of clang -O0 output with the
/// result alloca dropped: the select between the two return values is
/// instead expressed as distinct basic blocks reached by a `br i1`
/// predicated on `fcmp olt`. That matches the semantics exactly and
/// isolates the floating-point comparison from phi lowering, which has its
/// own end-to-end coverage in `switch_e2e.rs`.
const LL_CMP_LT: &str = r#"
define i32 @cmp_lt(double %x, double %y) {
entry:
  %c = fcmp olt double %x, %y
  br i1 %c, label %lt, label %ge
lt:
  ret i32 1
ge:
  ret i32 2
}
"#;

/// Simple FP-cast round-trip: integer-to-double then double-to-integer
/// via separate instructions. Exercises `sitofp` + `fptosi` in the
/// adapter's cast path.
const LL_INT_DOUBLE_ROUNDTRIP: &str = r#"
define i32 @roundtrip(i32 %x) {
entry:
  %d = sitofp i32 %x to double
  %r = fptosi double %d to i32
  ret i32 %r
}
"#;

/// `fneg` on f64 through the full pipeline.
const LL_FNEG_F64: &str = r#"
define double @neg(double %x) {
entry:
  %n = fneg double %x
  ret double %n
}
"#;

/// Compile `src` at O0 for the explicit `triple`. `isa_profile` is
/// [`CompilerConfig::aarch64_isa_profile`]; `None` keeps the target's AOT
/// contract.
fn try_compile(
    src: &str,
    module_name: &str,
    triple: &str,
    isa_profile: Option<AArch64IsaProfile>,
) -> Result<Vec<u8>, Box<CompileError>> {
    let module = import_text(src, module_name).expect("import");
    let target_spec = TargetSpec::parse(triple).expect("target spec");
    let cfg = CompilerConfig {
        opt_level: OptLevel::O0,
        target: target_spec.architecture,
        emit_proofs: false,
        trace_level: CompilerTraceLevel::None,
        emit_debug: false,
        parallel: false,
        cegis_superopt_budget_sec: None,
        enable_fsym_trust_ir_preflight: false,
        enable_jit_fast_regalloc: false,
        jit_validation_mode_override: None,
        jit_external_symbol_resolution: Default::default(),
        panic_unwind: false,
        aarch64_isa_profile: isa_profile,
        ..CompilerConfig::default()
    };
    Compiler::new_for_target_spec(cfg, target_spec)
        .with_codegen_license(permit_unlicensed())
        .compile(&module)
        .map(|result| result.object_code)
        .map_err(Box::new)
}

/// [`try_compile`] that must yield a non-empty object in `triple`'s
/// container: Mach-O arm64 for Apple, ELF AArch64 for Linux.
fn compile_for(
    src: &str,
    module_name: &str,
    triple: &str,
    isa_profile: Option<AArch64IsaProfile>,
) -> Vec<u8> {
    let object = try_compile(src, module_name, triple, isa_profile)
        .unwrap_or_else(|e| panic!("compile `{module_name}` for `{triple}` failed: {e}"));
    assert!(
        !object.is_empty(),
        "pipeline returned an empty object for `{module_name}` on `{triple}`"
    );
    let word = |at: usize| u32::from_le_bytes(object[at..at + 4].try_into().unwrap());
    if triple == APPLE {
        // MH_MAGIC_64, CPU_TYPE_ARM64.
        assert_eq!(
            (word(0), word(4)),
            (0xfeed_facf, 0x0100_000c),
            "`{module_name}` on `{triple}` is not a Mach-O arm64 object"
        );
    } else {
        // ELF magic, EM_AARCH64.
        assert!(
            object.starts_with(b"\x7fELF") && u16::from_le_bytes([object[18], object[19]]) == 183,
            "`{module_name}` on `{triple}` is not an ELF AArch64 object"
        );
    }
    object
}

/// Every program reaches an object on both explicit targets.
fn compile_to_aarch64(src: &str, module_name: &str) {
    for triple in TARGETS {
        compile_for(src, module_name, triple, None);
    }
}

/// The little-endian instruction words of the object's code section
/// (`__TEXT,__text` or `.text`).
fn text_words(object: &[u8]) -> Vec<u32> {
    let text = if object.starts_with(b"\x7fELF") {
        elf_text(object).to_vec()
    } else {
        MachOParser::parse(object)
            .expect("parse Mach-O object")
            .sections
            .into_iter()
            .find(|section| section.segment == "__TEXT" && section.name == "__text")
            .expect("__TEXT,__text section")
            .data
    };
    assert_eq!(text.len() % 4, 0, "code section is not word sized");
    text.as_chunks::<4>()
        .0
        .iter()
        .map(|word| u32::from_le_bytes(*word))
        .collect()
}

/// The `.text` bytes of an ELF64 little-endian relocatable object.
fn elf_text(object: &[u8]) -> &[u8] {
    let u16_at = |at: usize| usize::from(u16::from_le_bytes([object[at], object[at + 1]]));
    let u32_at = |at: usize| u32::from_le_bytes(object[at..at + 4].try_into().unwrap()) as usize;
    let u64_at = |at: usize| {
        usize::try_from(u64::from_le_bytes(object[at..at + 8].try_into().unwrap())).unwrap()
    };
    // e_shoff, e_shentsize, e_shnum, e_shstrndx; sh_name, sh_offset, sh_size.
    let (table, entry_size, count) = (u64_at(0x28), u16_at(0x3a), u16_at(0x3c));
    let names_header = table + u16_at(0x3e) * entry_size;
    let names = &object[u64_at(names_header + 0x18)..][..u64_at(names_header + 0x20)];
    let text = (0..count)
        .map(|index| table + index * entry_size)
        .find(|&header| names[u32_at(header)..].split(|byte| *byte == 0).next() == Some(b".text"))
        .expect("ELF .text section");
    &object[u64_at(text + 0x18)..][..u64_at(text + 0x20)]
}

/// The object contains `FADD Hd, Hn, Hm` (scalar half precision, FEAT_FP16).
fn assert_has_fp16_fadd(object: &[u8], triple: &str, lane: &str) {
    assert!(
        text_words(object)
            .into_iter()
            .any(|word| word & 0xffe0_fc00 == 0x1ee0_2800),
        "`{triple}` {lane}: `add_h_one` lacks FADD Hd, Hn, Hm"
    );
}

#[test]
fn fadd_f32_import_to_trust_ir() {
    let m = import_text(LL_ADD_F32, "add_f").expect("import f32 add");
    assert_eq!(m.functions.len(), 1);
    assert_eq!(m.functions[0].name, "add_f");
    // Every block must have a terminator.
    for (i, b) in m.functions[0].blocks.iter().enumerate() {
        assert!(b.terminator().is_some(), "block {} missing terminator", i);
    }
}

#[test]
fn fadd_f32_full_pipeline_aarch64_o0() {
    compile_to_aarch64(LL_ADD_F32, "add_f");
}

#[test]
fn fadd_f64_full_pipeline_aarch64_o0() {
    compile_to_aarch64(LL_ADD_F64, "add_d");
}

/// FEAT_FP16 is intended here: `fadd half` with a binary16 constant selects
/// FMOV Hd, #1.0 and FADD Hd, Hn, Hm. The explicit FP16 profile admits them
/// on both targets. Apple's AOT contract admits them without a profile,
/// which is what this row compiled when it took the Apple host's target.
#[test]
fn fadd_f16_const_full_pipeline_aarch64_o0() {
    for triple in TARGETS {
        let object = compile_for(
            LL_ADD_F16_CONST,
            "add_h_one",
            triple,
            Some(AArch64IsaProfile::FP16),
        );
        assert_has_fp16_fadd(&object, triple, "explicit FP16 profile");
    }
    let object = compile_for(LL_ADD_F16_CONST, "add_h_one", APPLE, None);
    assert_has_fp16_fadd(&object, APPLE, "Apple AOT contract");
}

/// Twin: without the explicit profile the generic Linux baseline refuses the
/// FEAT_FP16 constant by name. It does not emit FP16 instructions that a
/// baseline CPU might not implement.
#[test]
fn fadd_f16_const_generic_linux_baseline_refuses_fp16_by_name() {
    let error = try_compile(LL_ADD_F16_CONST, "add_h_one", LINUX, None)
        .expect_err("the generic Linux baseline must refuse FEAT_FP16");
    match error.as_ref() {
        CompileError::Pipeline(PipelineError::ISel(message)) => {
            assert_eq!(message, FP16_CONSTANT_REFUSAL);
        }
        other => panic!("expected the named FEAT_FP16 refusal, got {other:?}"),
    }
}

#[test]
fn fcmp_olt_branch_full_pipeline_aarch64_o0() {
    compile_to_aarch64(LL_CMP_LT, "cmp_lt");
}

#[test]
fn sitofp_fptosi_roundtrip_full_pipeline_aarch64_o0() {
    compile_to_aarch64(LL_INT_DOUBLE_ROUNDTRIP, "roundtrip");
}

#[test]
fn fneg_f64_full_pipeline_aarch64_o0() {
    compile_to_aarch64(LL_FNEG_F64, "neg");
}

/// Exhaustive smoke test: every FP binop reaches an object file.
#[test]
fn all_fbinops_full_pipeline_aarch64_o0() {
    for (op_ll, op_name) in [
        ("fadd", "fadd"),
        ("fsub", "fsub"),
        ("fmul", "fmul"),
        ("fdiv", "fdiv"),
    ] {
        let src = format!(
            r#"
define double @{op_name}(double %a, double %b) {{
entry:
  %r = {op_ll} double %a, %b
  ret double %r
}}
"#
        );
        compile_to_aarch64(&src, op_name);
    }
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes because it was silently refused.
fn permit_unlicensed() -> trust_cg_lower::CodegenLicensePolicy {
    trust_cg_lower::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit)
}
