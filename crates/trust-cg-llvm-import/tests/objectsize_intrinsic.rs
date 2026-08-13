#![cfg(feature = "driver")]

// trust-cg-llvm-import / tests / objectsize_intrinsic.rs
//
// Regression coverage for clang -O0 llvm.objectsize calls imported from LLVM IR.

use std::fs;
use std::path::PathBuf;
use std::process::Command;
use std::time::{SystemTime, UNIX_EPOCH};

use trust_cg_codegen::compiler::{Compiler, CompilerConfig, CompilerTraceLevel};
use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::target::Target;
use trust_cg_llvm_import::import_text;

const LL_OBJECTSIZE_INTRINSIC: &str = r#"
target triple = "arm64-apple-macosx26.0.0"

declare i64 @llvm.objectsize.i64.p0(ptr, i1 immarg, i1 immarg, i1 immarg)

define i32 @main() {
entry:
  %buf = alloca i8, i64 16, align 1
  %size = call i64 @llvm.objectsize.i64.p0(ptr %buf, i1 false, i1 true, i1 false)
  %trunc = trunc i64 %size to i32
  ret i32 %trunc
}
"#;

fn compile_to_aarch64_object(src: &str, module_name: &str) -> Vec<u8> {
    let module = import_text(src, module_name).expect("import");
    let compiler = Compiler::new(CompilerConfig {
        opt_level: OptLevel::O0,
        target: Target::Aarch64,
        emit_proofs: false,
        trace_level: CompilerTraceLevel::None,
        emit_debug: false,
        parallel: false,
        cegis_superopt_budget_sec: None,
        enable_fsym_trust_ir_preflight: false,
        enable_jit_fast_regalloc: false,
        jit_validation_mode_override: None,
        panic_unwind: false,
    });
    compiler
        .compile(&module)
        .unwrap_or_else(|e| panic!("compile `{module_name}` failed: {e}"))
        .object_code
}

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

#[test]
fn objectsize_i64_p0_does_not_emit_runtime_symbol() {
    if !cfg!(all(target_os = "macos", target_arch = "aarch64")) {
        eprintln!(
            "skipping: test requires aarch64-apple-darwin (host is {} / {})",
            std::env::consts::OS,
            std::env::consts::ARCH
        );
        return;
    }

    let object = compile_to_aarch64_object(LL_OBJECTSIZE_INTRINSIC, "objectsize_intrinsic");
    let dir = unique_temp_dir("objectsize");
    let obj_path = dir.join("objectsize.o");
    fs::write(&obj_path, object).expect("write object");

    let nm = Command::new("nm")
        .arg("-u")
        .arg(&obj_path)
        .output()
        .expect("run nm");
    assert!(
        nm.status.success(),
        "nm failed with status {:?}\nstdout:\n{}\nstderr:\n{}",
        nm.status.code(),
        String::from_utf8_lossy(&nm.stdout),
        String::from_utf8_lossy(&nm.stderr)
    );
    let undefined = String::from_utf8_lossy(&nm.stdout);
    assert!(
        !undefined.contains("llvm.objectsize"),
        "objectsize intrinsic was left as an unresolved symbol:\n{undefined}"
    );
}
