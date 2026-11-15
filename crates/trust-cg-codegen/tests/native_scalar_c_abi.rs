// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0
//! Exercises the real AOT compiler path. Object emission is test evidence,
//! not native interoperability or formal ABI evidence.

#[path = "../../trust-cg-lower/tests/common/native_scalar_c_abi.rs"]
mod fixtures;

use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::target::TargetSpec;
use trust_cg_codegen::{Compiler, CompilerConfig};
use trust_cg_lower::{CodegenLicensePolicy, UnlicensedBodyPolicy};
use trust_ir::Ty;

fn compiler(triple: &str) -> Compiler {
    Compiler::new_for_target_spec(
        CompilerConfig {
            opt_level: OptLevel::O0,
            ..CompilerConfig::default()
        },
        TargetSpec::parse(triple).unwrap(),
    )
    .with_codegen_license(
        CodegenLicensePolicy::default().with_unlicensed(UnlicensedBodyPolicy::Permit),
    )
}

#[test]
fn recorded_scalar_calls_reach_real_objects_on_each_native_abi() {
    for triple in [
        "aarch64-apple-darwin",
        "aarch64-unknown-linux-gnu",
        "x86_64-apple-darwin",
        "x86_64-unknown-linux-gnu",
    ] {
        for variadic in [false, true] {
            let fixed = if variadic {
                vec![Ty::I32]
            } else {
                vec![Ty::I8, Ty::Ptr, Ty::F64]
            };
            let actual = if variadic {
                vec![Ty::I32, Ty::I64, Ty::F64]
            } else {
                fixed.clone()
            };
            let module = fixtures::fixture(triple, fixed, actual, Some(Ty::I8), variadic);
            let before = module.clone();
            assert!(
                compiler(triple).preflight(&module).is_empty(),
                "{triple}: native preflight"
            );
            let result = compiler(triple)
                .compile(&module)
                .unwrap_or_else(|e| panic!("{triple}: {e}"));
            assert!(!result.object_code.is_empty());
            assert_eq!(module, before);
            let mut legacy = module.clone();
            legacy.func_types[0].abi = None;
            let legacy = compiler(triple).compile(&legacy).unwrap();
            assert_eq!(
                result.object_code, legacy.object_code,
                "recorded ABI must select the existing physical scalar marshalling"
            );
        }
    }
}

#[test]
fn compiler_target_cannot_borrow_the_modules_recorded_abi() {
    let module = fixtures::fixture(
        "aarch64-apple-darwin",
        vec![Ty::I64],
        vec![Ty::I64],
        Some(Ty::I64),
        false,
    );
    for triple in [
        "aarch64-unknown-linux-gnu",
        "x86_64-unknown-linux-gnu",
        "x86_64-pc-windows-msvc",
        "riscv64-unknown-linux-gnu",
    ] {
        assert!(compiler(triple).compile(&module).is_err(), "{triple}");
    }
    let mut unsupported = module;
    unsupported.func_types[0].abi.as_mut().unwrap().can_unwind = true;
    assert!(
        compiler("aarch64-apple-darwin")
            .compile(&unsupported)
            .is_err()
    );
}

/// Compile the caller through Compiler::compile and let the host C compiler
/// supply the foreign implementation and driver. Only the test's caller uses
/// TrustCG; matching two TrustCG halves cannot conceal a placement defect.
#[test]
fn recorded_fixed_and_variadic_callers_interoperate_with_native_c() {
    let triple = match (std::env::consts::ARCH, std::env::consts::OS) {
        ("aarch64", "macos") => "aarch64-apple-darwin",
        ("aarch64", "linux") => "aarch64-unknown-linux-gnu",
        ("x86_64", "macos") => "x86_64-apple-darwin",
        ("x86_64", "linux") => "x86_64-unknown-linux-gnu",
        _ => return,
    };
    let stamp = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    let directory = std::env::temp_dir().join(format!(
        "trust-cg-recorded-c-{}-{stamp}",
        std::process::id()
    ));
    std::fs::create_dir(&directory).unwrap();
    for variadic in [false, true] {
        let (fixed, actual, driver) = if variadic {
            (
                vec![Ty::I32],
                vec![Ty::I32, Ty::I64, Ty::F64],
                r#"
#include <stdarg.h>
signed char foreign_scalar(int n, ...) {
    va_list ap; va_start(ap, n);
    long long i = va_arg(ap, long long);
    double f = va_arg(ap, double);
    va_end(ap);
    return (signed char)(n + i + (long long)f);
}
extern signed char call_foreign_scalar(int, long long, double);
int main(void) { return call_foreign_scalar(1, 44, 3.0) == 48 ? 0 : 1; }
"#,
            )
        } else {
            let parameters = vec![Ty::I8, Ty::U16, Ty::Ptr, Ty::F64];
            (
                parameters.clone(),
                parameters,
                r#"
signed char foreign_scalar(signed char a, unsigned short b, const unsigned char *p, double f) {
    return (signed char)(a + b + *p + (int)f);
}
extern signed char call_foreign_scalar(signed char, unsigned short, const unsigned char *, double);
int main(void) {
    const unsigned char value = 3;
    return call_foreign_scalar(-20, 7, &value, 2.0) == -8 ? 0 : 1;
}
"#,
            )
        };
        let module = fixtures::fixture(triple, fixed, actual, Some(Ty::I8), variadic);
        let object = compiler(triple).compile(&module).unwrap().object_code;
        let object_path = directory.join("caller.o");
        let driver_path = directory.join("driver.c");
        let executable = directory.join("driver");
        std::fs::write(&object_path, object).unwrap();
        std::fs::write(&driver_path, driver).unwrap();
        let linked = std::process::Command::new("cc")
            .arg("-O2")
            .arg(&driver_path)
            .arg(&object_path)
            .arg("-o")
            .arg(&executable)
            .output()
            .expect("native C compiler is required for scalar C interoperability");
        assert!(
            linked.status.success(),
            "{}",
            String::from_utf8_lossy(&linked.stderr)
        );
        let result = std::process::Command::new(&executable).output().unwrap();
        assert!(
            result.status.success(),
            "recorded scalar C interoperability: variadic={variadic}, {result:?}"
        );
    }
    std::fs::remove_dir_all(directory).unwrap();
}
