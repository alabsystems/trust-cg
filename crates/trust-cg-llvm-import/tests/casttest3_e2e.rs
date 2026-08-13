#![cfg(feature = "driver")]

// Regression coverage for llvm-test-suite 2002-05-02-CastTest3.

#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
mod macos_aarch64 {
    use std::fs;
    use std::process::Command;

    use trust_cg_codegen::compiler::{Compiler, CompilerConfig, CompilerTraceLevel};
    use trust_cg_codegen::pipeline::OptLevel;
    use trust_cg_codegen::target::Target;
    use trust_cg_llvm_import::import_text;

    const CASTTEST3_LL: &str = r#"
@.str = private unnamed_addr constant [11 x i8] c"s1   = %d\0A\00", align 1
@.str.1 = private unnamed_addr constant [11 x i8] c"us2  = %u\0A\00", align 1

declare i32 @printf(ptr noundef, ...)

define i32 @main(i32 noundef %argc, ptr noundef %argv) {
entry:
  %ret_slot = alloca i32, align 4
  %argc_slot = alloca i32, align 4
  %argv_slot = alloca ptr, align 8
  %s1_slot = alloca i16, align 2
  %us2_slot = alloca i16, align 2
  store i32 0, ptr %ret_slot, align 4
  store i32 %argc, ptr %argc_slot, align 4
  store ptr %argv, ptr %argv_slot, align 8
  %argc_value = load i32, ptr %argc_slot, align 4
  %cond = icmp sge i32 %argc_value, 3
  br i1 %cond, label %argc_ge_3, label %argc_lt_3

argc_ge_3:
  %selected_argc = load i32, ptr %argc_slot, align 4
  br label %select_end

argc_lt_3:
  br label %select_end

select_end:
  %selected = phi i32 [ %selected_argc, %argc_ge_3 ], [ -769, %argc_lt_3 ]
  %s1_trunc = trunc i32 %selected to i16
  store i16 %s1_trunc, ptr %s1_slot, align 2
  %s1_for_us2 = load i16, ptr %s1_slot, align 2
  store i16 %s1_for_us2, ptr %us2_slot, align 2
  %s1_print_raw = load i16, ptr %s1_slot, align 2
  %s1_print = sext i16 %s1_print_raw to i32
  %print_s1 = call i32 (ptr, ...) @printf(ptr noundef @.str, i32 noundef %s1_print)
  %us2_print_raw = load i16, ptr %us2_slot, align 2
  %us2_print = zext i16 %us2_print_raw to i32
  %print_us2 = call i32 (ptr, ...) @printf(ptr noundef @.str.1, i32 noundef %us2_print)
  ret i32 0
}
"#;

    #[test]
    fn casttest3_imported_program_links_and_runs() {
        if Command::new("cc")
            .arg("--version")
            .output()
            .map(|out| !out.status.success())
            .unwrap_or(true)
        {
            return;
        }

        let module = import_text(CASTTEST3_LL, "casttest3").expect("import CastTest3 LL");
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
        let result = compiler.compile(&module).expect("compile CastTest3");

        let dir = std::env::temp_dir().join(format!("trust-cg-casttest3-{}", std::process::id()));
        let _ = fs::remove_dir_all(&dir);
        fs::create_dir_all(&dir).expect("create temp dir");
        let obj = dir.join("casttest3.o");
        let bin = dir.join("casttest3");
        fs::write(&obj, result.object_code).expect("write object");

        let link = Command::new("cc")
            .arg(&obj)
            .arg("-o")
            .arg(&bin)
            .output()
            .expect("link CastTest3");
        assert!(
            link.status.success(),
            "link failed: {}",
            String::from_utf8_lossy(&link.stderr)
        );

        let run = Command::new(&bin).output().expect("run CastTest3");
        assert!(
            run.status.success(),
            "CastTest3 exited with {:?}; stdout=`{}` stderr=`{}`",
            run.status.code(),
            String::from_utf8_lossy(&run.stdout),
            String::from_utf8_lossy(&run.stderr)
        );
        assert_eq!(
            String::from_utf8_lossy(&run.stdout),
            "s1   = -769\nus2  = 64767\n"
        );
    }
}
