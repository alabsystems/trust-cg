#![cfg(feature = "driver")]

// trust-cg-llvm-import / tests / ws2_stack_protector_target.rs
//
// Regression coverage for WS2 stack-protected benchmark object emission. The
// Mach-O (aarch64-apple-darwin) and ELF (aarch64-unknown-linux-gnu) object
// checks compile for explicit triples and run on every host; the linked
// program compiles for this host's triple and runs natively.

mod common;

use std::collections::BTreeSet;
use std::fs;
use std::process::Command;

use common::{
    LINUX, compile_for, compile_for_host, describe_status, elf_section_index, elf_symbol_index,
    elf_text_relocation_kinds, link_with_cc, native_host_or_skip, unique_temp_dir,
};
use trust_cg_codegen::compiler::{
    CompileError, Compiler, CompilerConfig, CompilerTargetSelection, CompilerTraceLevel,
    TargetSelectionOrigin,
};
use trust_cg_codegen::elf::constants::{
    R_AARCH64_ADD_ABS_LO12_NC, R_AARCH64_ADR_GOT_PAGE, R_AARCH64_ADR_PREL_PG_HI21,
    R_AARCH64_CALL26, R_AARCH64_LD64_GOT_LO12_NC, SHF_ALLOC, SHF_EXECINSTR, SHF_WRITE, SHT_NOBITS,
    STB_GLOBAL, STB_LOCAL, STT_OBJECT,
};
use trust_cg_codegen::elf::reparse::read_object_records;
use trust_cg_codegen::lower::LowerError;
use trust_cg_codegen::macho::linker::{MachOParser, ParsedObject};
use trust_cg_codegen::pipeline::{OptLevel, PipelineError, stack_protector_target_abi};
use trust_cg_codegen::target::TargetSpec;
use trust_cg_llvm_import::import_text;
use trust_cg_lower::abi::AArch64AbiTargetError;

const LL_STACK_PROTECTED_SIEVE_SHAPE: &str = r#"
target triple = "arm64-apple-macosx26.0.0"

@main.flags = internal global [8 x i8] zeroinitializer, align 1

define i32 @main(i32 noundef %idx) #0 {
entry:
  %idx64 = sext i32 %idx to i64
  %p = getelementptr inbounds [8 x i8], ptr @main.flags, i64 0, i64 %idx64
  store i8 1, ptr %p, align 1
  ret i32 0
}

attributes #0 = { noinline nounwind optnone sspreq uwtable "frame-pointer"="non-leaf" }
"#;

const LL_TRIVIAL_SSP_LEAF: &str = r#"
target triple = "arm64-apple-macosx26.0.0"

define i32 @main() #0 {
entry:
  ret i32 0
}

attributes #0 = { noinline nounwind optnone ssp uwtable "stack-protector-buffer-size"="8" }
"#;

fn compile_for_target(src: &str, module_name: &str, target: &str) -> Vec<u8> {
    let module = import_text(src, module_name).expect("import");
    let target_spec = TargetSpec::parse(target).expect("target spec");
    let compiler = Compiler::new_for_target_spec(
        CompilerConfig {
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
            ..CompilerConfig::default()
        },
        target_spec,
    )
    .with_codegen_license(permit_unlicensed());
    compiler
        .compile(&module)
        .unwrap_or_else(|e| panic!("compile `{module_name}` for `{target}` failed: {e}"))
        .object_code
}

fn undefined_symbols(parsed: &ParsedObject) -> BTreeSet<&str> {
    parsed
        .symbols
        .iter()
        .filter(|symbol| symbol.is_undefined())
        .map(|symbol| symbol.name.as_str())
        .collect()
}

#[test]
fn apple_aarch64_trivial_ssp_leaf_does_not_emit_stack_guard_symbols() {
    let object = compile_for_target(
        LL_TRIVIAL_SSP_LEAF,
        "ws2_trivial_ssp_leaf",
        "aarch64-apple-darwin",
    );
    let parsed = MachOParser::parse(&object).expect("parse Mach-O object");
    let undefined = undefined_symbols(&parsed);
    assert!(
        !undefined.contains("___stack_chk_guard"),
        "trivial ssp leaf should not reference stack guard: {undefined:?}"
    );
    assert!(
        !undefined.contains("___stack_chk_fail"),
        "trivial ssp leaf should not reference stack check failure: {undefined:?}"
    );
}

#[test]
fn apple_aarch64_target_emits_stack_protected_sieve_shape_as_object() {
    let object = compile_for_target(
        LL_STACK_PROTECTED_SIEVE_SHAPE,
        "ws2_stack_protected_sieve",
        "aarch64-apple-darwin",
    );
    let parsed = MachOParser::parse(&object).expect("parse Mach-O object");

    let data_section_idx = parsed
        .sections
        .iter()
        .position(|section| section.segment == "__DATA" && section.name == "__data")
        .expect("__DATA,__data section");
    let data = &parsed.sections[data_section_idx];
    assert_eq!(data.data, &[0; 8]);

    let flags_symbol_idx = parsed
        .symbols
        .iter()
        .position(|symbol| symbol.name == "_main.flags")
        .expect("_main.flags symbol");
    let flags_symbol = &parsed.symbols[flags_symbol_idx];
    assert_eq!(flags_symbol.section, (data_section_idx + 1) as u8);
    assert_eq!(flags_symbol.value, data.addr);

    let undefined = undefined_symbols(&parsed);
    assert!(undefined.contains("___stack_chk_guard"));
    assert!(undefined.contains("___stack_chk_fail"));

    let text = parsed
        .sections
        .iter()
        .find(|section| section.segment == "__TEXT" && section.name == "__text")
        .expect("__TEXT,__text section");
    let guard_relocation_kinds: Vec<_> = text
        .relocations
        .iter()
        .filter(|relocation| {
            parsed
                .symbols
                .get(relocation.symbol_index as usize)
                .is_some_and(|symbol| symbol.name == "___stack_chk_guard")
        })
        .map(|relocation| relocation.kind)
        .collect();
    assert_eq!(
        guard_relocation_kinds
            .iter()
            .filter(|kind| {
                **kind == trust_cg_codegen::macho::reloc::AArch64RelocKind::GotLoadPage21
            })
            .count(),
        2,
        "stack guard ADRP sites should use GOT page relocations: {guard_relocation_kinds:?}"
    );
    assert_eq!(
        guard_relocation_kinds
            .iter()
            .filter(|kind| {
                **kind == trust_cg_codegen::macho::reloc::AArch64RelocKind::GotLoadPageoff12
            })
            .count(),
        2,
        "stack guard LDR sites should use GOT pageoff relocations: {guard_relocation_kinds:?}"
    );
    assert!(
        !guard_relocation_kinds.contains(&trust_cg_codegen::macho::reloc::AArch64RelocKind::Page21)
            && !guard_relocation_kinds
                .contains(&trust_cg_codegen::macho::reloc::AArch64RelocKind::Pageoff12),
        "stack guard should not use direct page relocations: {guard_relocation_kinds:?}"
    );
}

/// ELF twin of the trivial-leaf check: a stack-protector-eligible leaf with no
/// buffer references neither glibc guard symbol.
#[test]
fn linux_aarch64_trivial_ssp_leaf_does_not_emit_stack_guard_symbols() {
    let object = compile_for(
        LL_TRIVIAL_SSP_LEAF,
        "ws2_trivial_ssp_leaf",
        LINUX,
        OptLevel::O0,
    );
    let undefined = common::undefined_symbols(&object);
    assert!(
        !undefined.contains("__stack_chk_guard"),
        "trivial ssp leaf should not reference stack guard: {undefined:?}"
    );
    assert!(
        !undefined.contains("__stack_chk_fail"),
        "trivial ssp leaf should not reference stack check failure: {undefined:?}"
    );
}

/// ELF twin of the Mach-O sieve-shape check. The zero-initialized
/// `main.flags` is a local object at the start of writable `.bss`; the frame
/// reads glibc's global `__stack_chk_guard` through the GOT
/// (`R_AARCH64_ADR_GOT_PAGE` then `R_AARCH64_LD64_GOT_LO12_NC`, once in the
/// prologue and once in the epilogue check, never a direct page relocation)
/// and calls `__stack_chk_fail` with `R_AARCH64_CALL26`.
#[test]
fn linux_aarch64_target_emits_stack_protected_sieve_shape_as_object() {
    let object = compile_for(
        LL_STACK_PROTECTED_SIEVE_SHAPE,
        "ws2_stack_protected_sieve",
        LINUX,
        OptLevel::O0,
    );
    let records = read_object_records(&object).expect("read ELF object records");

    let bss_idx = elf_section_index(&records, ".bss");
    let bss = &records.sections[bss_idx];
    assert_eq!(bss.sh_type, SHT_NOBITS);
    assert_eq!(
        bss.sh_flags & (SHF_ALLOC | SHF_WRITE | SHF_EXECINSTR),
        SHF_ALLOC | SHF_WRITE
    );
    assert_eq!(bss.size, 8);

    let flags_symbol_idx = elf_symbol_index(&records, "main.flags");
    let flags_symbol = &records.symbols[flags_symbol_idx];
    assert_eq!(
        (
            flags_symbol.section_index as usize,
            flags_symbol.value,
            flags_symbol.size,
            flags_symbol.binding,
            flags_symbol.symbol_type
        ),
        (bss_idx, 0, 8, STB_LOCAL, STT_OBJECT),
        "internal flags global: {flags_symbol:?}"
    );
    let flags_kinds = elf_text_relocation_kinds(&records, flags_symbol_idx);
    assert!(
        flags_kinds.contains(&R_AARCH64_ADR_PREL_PG_HI21)
            && flags_kinds.contains(&R_AARCH64_ADD_ABS_LO12_NC),
        "text should address main.flags with the ADRP/ADD pair: {flags_kinds:?}"
    );

    let undefined = common::undefined_symbols(&object);
    assert!(undefined.contains("__stack_chk_guard"), "{undefined:?}");
    assert!(undefined.contains("__stack_chk_fail"), "{undefined:?}");
    for name in ["__stack_chk_guard", "__stack_chk_fail"] {
        let symbol = &records.symbols[elf_symbol_index(&records, name)];
        assert_eq!(
            symbol.binding, STB_GLOBAL,
            "{name} must be a global reference: {symbol:?}"
        );
    }

    let guard_relocation_kinds =
        elf_text_relocation_kinds(&records, elf_symbol_index(&records, "__stack_chk_guard"));
    assert_eq!(
        guard_relocation_kinds
            .iter()
            .filter(|kind| **kind == R_AARCH64_ADR_GOT_PAGE)
            .count(),
        2,
        "stack guard ADRP sites should use GOT page relocations: {guard_relocation_kinds:?}"
    );
    assert_eq!(
        guard_relocation_kinds
            .iter()
            .filter(|kind| **kind == R_AARCH64_LD64_GOT_LO12_NC)
            .count(),
        2,
        "stack guard LDR sites should use GOT lo12 relocations: {guard_relocation_kinds:?}"
    );
    assert_eq!(
        guard_relocation_kinds.len(),
        4,
        "stack guard should not use direct page relocations: {guard_relocation_kinds:?}"
    );
    for pair in guard_relocation_kinds.chunks(2) {
        assert_eq!(
            pair,
            [R_AARCH64_ADR_GOT_PAGE, R_AARCH64_LD64_GOT_LO12_NC],
            "each guard load is an ADRP/LDR GOT pair: {guard_relocation_kinds:?}"
        );
    }

    let fail_kinds =
        elf_text_relocation_kinds(&records, elf_symbol_index(&records, "__stack_chk_fail"));
    assert_eq!(
        fail_kinds,
        [R_AARCH64_CALL26],
        "the failure path calls __stack_chk_fail once"
    );
}

/// The stack-protected sieve shape compiled for this host's triple links with
/// `cc` against the host C library's guard and runs to a clean exit.
#[test]
fn stack_protected_sieve_shape_links_and_runs_natively() {
    if !native_host_or_skip("stack_protected_sieve_shape_links_and_runs_natively") {
        return;
    }

    let object = compile_for_host(
        LL_STACK_PROTECTED_SIEVE_SHAPE,
        "ws2_stack_protected_sieve_link",
        OptLevel::O0,
    );
    let dir = unique_temp_dir("stack-protector-link");
    let obj_path = dir.join("stack_protected.o");
    let bin_path = dir.join("stack_protected");
    fs::write(&obj_path, object).expect("write object");

    link_with_cc(&obj_path, &bin_path);
    let output = Command::new(&bin_path).output().expect("run linked binary");
    assert!(
        output.status.success(),
        "linked binary failed with {}\nstdout:\n{}\nstderr:\n{}",
        describe_status(output.status),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

/// `aarch64-unknown-unknown` names no operating system, so it selects neither
/// DarwinPCS/Mach-O nor AAPCS64/ELF. The compiler keeps the spelled-out
/// triple (it never inherits the host's OS/ABI) and refuses it when resolving
/// the AArch64 calling convention, before frame lowering decides canary
/// support. Every step is a function of the triple alone, so the refusal is
/// the same on every host. The canary classifier itself also refuses the
/// triple, naming its object format as unsupported rather than Mach-O. That
/// refusal is typed by the layer that raises it (trust-core AD-8 / E0.3): the
/// canary prologue/epilogue is a frame-lowering sequence and no object writer
/// has run, so it is `FrameLowering(LowerError::FrameLowering)`, never
/// `TargetObjectUnsupported`, which the rustc bridge would file under a
/// different layer code.
#[test]
fn explicit_unknown_aarch64_target_still_fails_closed_for_stack_protector() {
    const TRIPLE: &str = "aarch64-unknown-unknown";
    let module =
        import_text(LL_STACK_PROTECTED_SIEVE_SHAPE, "ws2_stack_protector_fail").expect("import");
    let target_spec = TargetSpec::parse(TRIPLE).expect("target spec");
    let compiler = Compiler::new_for_target_spec(
        CompilerConfig {
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
            ..CompilerConfig::default()
        },
        target_spec,
    )
    .with_codegen_license(permit_unlicensed());

    assert_eq!(
        compiler.target_selection(),
        CompilerTargetSelection {
            triple: TRIPLE.to_string(),
            origin: TargetSelectionOrigin::Explicit,
        }
    );

    let error = compiler
        .compile(&module)
        .expect_err("unsupported explicit target should fail closed");
    match &error {
        CompileError::Pipeline(PipelineError::TargetAbiUnresolved(
            AArch64AbiTargetError::Unrecognized(triple),
        )) => assert_eq!(triple, TRIPLE),
        other => panic!("expected the [TCG-TARGET-ABI] refusal for {TRIPLE}, got {other:?}"),
    }
    assert_eq!(
        error.to_string(),
        "pipeline error: AArch64 target unresolved: [TCG-TARGET-ABI] target triple \
         `aarch64-unknown-unknown` selects no modeled AArch64 calling convention: only Apple \
         triples (DarwinPCS, Mach-O) and Linux/Android/BSD/illumos/Solaris triples (AAPCS64, \
         ELF) are lowered"
    );

    // The whole reason is pinned, so the target, the object format and why
    // the triple is refused are each checked exactly.
    match stack_protector_target_abi(TRIPLE) {
        Err(PipelineError::FrameLowering(LowerError::FrameLowering(reason))) => assert_eq!(
            reason,
            "stack canary lowering supports only AArch64 Apple Mach-O and AArch64 Linux ELF \
             with a global __stack_chk_guard; the triple names no supported object format \
             (target `aarch64-unknown-unknown`, native object format)"
        ),
        other => panic!(
            "expected the canary classifier to refuse {TRIPLE} as a frame-lowering refusal, \
             got {other:?}"
        ),
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
