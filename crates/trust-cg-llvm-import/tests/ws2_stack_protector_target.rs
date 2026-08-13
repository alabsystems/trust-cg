#![cfg(feature = "driver")]

// trust-cg-llvm-import / tests / ws2_stack_protector_target.rs
//
// Regression coverage for WS2 stack-protected benchmark object emission.

use std::collections::BTreeSet;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::{SystemTime, UNIX_EPOCH};

use trust_cg_codegen::compiler::{Compiler, CompilerConfig, CompilerTraceLevel};
use trust_cg_codegen::macho::linker::{MachOParser, ParsedObject};
use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::target::TargetSpec;
use trust_cg_llvm_import::import_text;

fn unique_temp_dir(name: &str) -> PathBuf {
    let nanos = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("system time before unix epoch")
        .as_nanos();
    let dir = std::env::temp_dir().join(format!(
        "trust-cg-import-{name}-{}-{nanos}",
        std::process::id()
    ));
    fs::create_dir_all(&dir).expect("create temp dir");
    dir
}

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
            panic_unwind: false,
        },
        target_spec,
    );
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

fn link_with_cc(obj_path: &Path, bin_path: &Path) {
    let output = Command::new("cc")
        .arg(obj_path)
        .arg("-o")
        .arg(bin_path)
        .output()
        .expect("run cc");
    assert!(
        output.status.success(),
        "cc failed with status {:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
fn apple_aarch64_stack_protected_sieve_shape_links_and_runs() {
    if !cfg!(all(target_os = "macos", target_arch = "aarch64")) {
        eprintln!(
            "skipping: test requires aarch64-apple-darwin (host is {} / {})",
            std::env::consts::OS,
            std::env::consts::ARCH
        );
        return;
    }

    let object = compile_for_target(
        LL_STACK_PROTECTED_SIEVE_SHAPE,
        "ws2_stack_protected_sieve_link",
        "aarch64-apple-darwin",
    );
    let dir = unique_temp_dir("stack-protector-link");
    let obj_path = dir.join("stack_protected.o");
    let bin_path = dir.join("stack_protected");
    fs::write(&obj_path, object).expect("write object");

    link_with_cc(&obj_path, &bin_path);
    let output = Command::new(&bin_path).output().expect("run linked binary");
    assert!(
        output.status.success(),
        "linked binary failed with status {:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
fn explicit_unknown_aarch64_target_still_fails_closed_for_stack_protector() {
    let module =
        import_text(LL_STACK_PROTECTED_SIEVE_SHAPE, "ws2_stack_protector_fail").expect("import");
    let target_spec = TargetSpec::parse("aarch64-unknown-unknown").expect("target spec");
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
            panic_unwind: false,
        },
        target_spec,
    );

    let error = compiler
        .compile(&module)
        .expect_err("unsupported explicit target should fail closed");
    let message = error.to_string();
    assert!(message.contains("aarch64-unknown-unknown Mach-O"));
    assert!(message.contains("stack canary lowering"));
}
