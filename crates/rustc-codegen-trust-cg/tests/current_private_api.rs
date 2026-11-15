//! Current compiler validity operations must not become ordinary casts.
//! Host target: aarch64-apple-darwin.
//! Positive execution below checks API/lowering behavior with certificates off;
//! it grants no independent proof or default certificates-on acceptance.
//! Author: Andrew Yates | Copyright 2026 | License: Apache-2.0
#![cfg(all(target_os = "macos", target_arch = "aarch64", rustc_session_split))]

#[path = "support/backend_artifact.rs"]
mod backend_artifact_support;
#[path = "support/darwin_native_prerequisites.rs"]
mod darwin_native;
#[path = "support/positive_evidence.rs"]
mod positive_evidence;
#[path = "support/toolchain.rs"]
mod toolchain_support;

#[test]
fn actual_box_deref_mir_refuses_before_object_emission() {
    darwin_native::require("current_private_api", &[]);
    let unique = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    let directory =
        std::env::temp_dir().join(format!("tcg-current-api-{}-{unique}", std::process::id()));
    std::fs::create_dir(&directory).expect("create owned fixture directory");
    let source = directory.join("source.rs");
    std::fs::write(
        &source,
        r#"
#[unsafe(no_mangle)]
#[inline(never)]
pub fn dereference_box(value: &Box<u8>) -> u8 { **value }
"#,
    )
    .expect("write actual Rust fixture");
    let oracle_mir = directory.join("oracle.mir");
    let oracle = toolchain_support::rustc_command()
        .args(["--crate-type=lib", "-Zmir-opt-level=0", "--emit=mir"])
        .arg(&source)
        .arg("-o")
        .arg(&oracle_mir)
        .output()
        .expect("run actual compiler oracle");
    assert!(
        oracle.status.success(),
        "{}",
        String::from_utf8_lossy(&oracle.stderr)
    );
    let mir = std::fs::read_to_string(&oracle_mir).expect("read actual emitted MIR");
    assert!(
        mir.contains("BoxDerefTransmute"),
        "fixture did not exercise the current operation: {mir}"
    );
    let dylib = backend_artifact_support::current_test_backend();
    let object = directory.join("refused.o");
    let output = toolchain_support::rustc_command()
        .arg(format!("-Zcodegen-backend={}", dylib.display()))
        .args([
            "--crate-type=lib",
            "-Cpanic=abort",
            "-Zmir-opt-level=0",
            "--emit=obj",
        ])
        .arg(&source)
        .arg("-o")
        .arg(&object)
        .output()
        .expect("run current backend");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        !output.status.success(),
        "an unmodeled Box validity obligation was admitted: {stderr}"
    );
    assert!(
        stderr.contains("[TCG-BOX-DEREF]"),
        "wrong refusal: {stderr}"
    );
    assert!(
        !object.exists(),
        "refused program emitted an object at {}",
        object.display()
    );
    // Retain the exact source, oracle and diagnostics for failed-run inspection.
    std::fs::write(directory.join("backend.stderr"), &output.stderr).expect("retain diagnostic");
    positive_evidence::record(
        positive_evidence::Evidence::ExpectedRefusal,
        positive_evidence::Certs::On,
    );
}

#[test]
fn scalar_widths_and_allocation_provenance_execute_against_c_driver() {
    darwin_native::require("current_private_api", &[]);
    let stamp = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    let directory = std::env::temp_dir().join(format!(
        "tcg-scalar-provenance-{}-{stamp}",
        std::process::id()
    ));
    std::fs::create_dir(&directory).unwrap();
    let source = directory.join("constants.rs");
    std::fs::write(
        &source,
        r#"
#![no_std]
#[unsafe(no_mangle)] pub extern "C" fn byte_constant() -> u8 { 173 }
#[unsafe(no_mangle)] pub extern "C" fn half_constant() -> u16 { 0xbeef }
#[unsafe(no_mangle)] pub extern "C" fn word_constant() -> u32 { 0x89abcdef }
#[unsafe(no_mangle)] pub extern "C" fn wide_constant() -> u64 { 0xfedcba9876543210 }
#[unsafe(no_mangle)] pub extern "C" fn double_wide_constant() -> u128 {
    0x0123456789abcdef_fedcba9876543210
}
#[unsafe(no_mangle)] pub extern "C" fn boolean_constant() -> bool { true }
#[unsafe(no_mangle)] pub extern "C" fn float_constant() -> f32 { 1.5 }
#[unsafe(no_mangle)] pub extern "C" fn double_constant() -> f64 { -2.5 }
#[repr(transparent)] pub struct Small(u8);
#[unsafe(no_mangle)] pub extern "C" fn aggregate_constant() -> Small { Small(173) }
#[unsafe(no_mangle)] pub static MARKER: u32 = 0x76543210;
#[unsafe(no_mangle)] pub extern "C" fn allocation_constant() -> *const u32 { &MARKER }
#[unsafe(no_mangle)] pub extern "C" fn address_constant() -> *const u8 { 0usize as *const u8 }
#[unsafe(no_mangle)] pub extern "C" fn function_constant() -> extern "C" fn() -> u8 {
    byte_constant
}
"#,
    )
    .unwrap();
    let driver = directory.join("driver.c");
    std::fs::write(&driver, r#"
#include <stdint.h>
extern uint8_t byte_constant(void);
extern uint16_t half_constant(void);
extern uint32_t word_constant(void);
extern uint64_t wide_constant(void);
extern unsigned __int128 double_wide_constant(void);
extern _Bool boolean_constant(void);
extern float float_constant(void);
extern double double_constant(void);
extern uint8_t aggregate_constant(void);
extern const uint32_t *allocation_constant(void);
extern const uint8_t *address_constant(void);
typedef uint8_t (*byte_function)(void);
extern byte_function function_constant(void);
extern const uint32_t MARKER;
int main(void) {
    if (byte_constant() != 173 || half_constant() != 0xbeef) return 1;
    if (word_constant() != UINT32_C(0x89abcdef)) return 2;
    if (wide_constant() != UINT64_C(0xfedcba9876543210)) return 3;
    unsigned __int128 expected = ((unsigned __int128)UINT64_C(0x0123456789abcdef) << 64)
        | UINT64_C(0xfedcba9876543210);
    if (double_wide_constant() != expected) return 4;
    if (!boolean_constant() || float_constant() != 1.5f || double_constant() != -2.5) return 5;
    if (aggregate_constant() != 173) return 6;
    if (allocation_constant() != &MARKER || *allocation_constant() != UINT32_C(0x76543210)) return 7;
    if (address_constant() != 0 || function_constant()() != 173) return 8;
    return 0;
}
"#).unwrap();
    let backend = backend_artifact_support::current_test_backend();
    for lane in ["llvm", "bridge"] {
        // The bridge emits separate code and data CGU objects, including the
        // immutable MARKER. Isolate each compiler's outputs and link all of
        // its actual objects, as the existing object-emission tests do.
        let object_directory = directory.join(lane);
        std::fs::create_dir(&object_directory).unwrap();
        let object = object_directory.join("constants.o");
        let mut compiler = toolchain_support::rustc_command();
        if lane == "bridge" {
            // This is ordinary API/lowering execution evidence. Keep the
            // original certificates-on hello_loop obligation unchanged.
            compiler
                .arg(format!("-Zcodegen-backend={}", backend.display()))
                .arg(toolchain_support::backend_knobs_arg(&["no-proof-certs"]));
        }
        compiler
            .args([
                "--crate-type=lib",
                "--emit=obj",
                "-Cpanic=abort",
                "-Copt-level=0",
                "-Zmir-opt-level=0",
            ])
            .arg(&source)
            .arg("-o")
            .arg(&object);
        std::fs::write(
            directory.join(format!("{lane}.command.txt")),
            format!("{compiler:?}\n"),
        )
        .unwrap();
        let output = compiler.output().unwrap();
        std::fs::write(directory.join(format!("{lane}.stdout")), &output.stdout).unwrap();
        std::fs::write(directory.join(format!("{lane}.stderr")), &output.stderr).unwrap();
        assert!(
            output.status.success(),
            "{lane}: {}",
            String::from_utf8_lossy(&output.stderr)
        );
        let mut objects: Vec<_> = std::fs::read_dir(&object_directory)
            .unwrap()
            .map(|entry| entry.unwrap().path())
            .filter(|path| path.extension().is_some_and(|extension| extension == "o"))
            .collect();
        objects.sort();
        assert!(!objects.is_empty(), "{lane}: compiler emitted no objects");
        for path in &objects {
            let metadata = path.symlink_metadata().unwrap();
            assert!(metadata.is_file() && metadata.len() > 0, "{lane}: {path:?}");
        }
        std::fs::write(
            directory.join(format!("{lane}.objects.txt")),
            objects
                .iter()
                .map(|path| format!("{}\n", path.display()))
                .collect::<String>(),
        )
        .unwrap();
        let executable = directory.join(format!("{lane}-caller"));
        let mut linker = std::process::Command::new("/usr/bin/cc");
        linker
            .arg(&driver)
            .args(&objects)
            .arg("-o")
            .arg(&executable);
        std::fs::write(
            directory.join(format!("{lane}.link-command.txt")),
            format!("{linker:?}\n"),
        )
        .unwrap();
        let linked = linker.output().unwrap();
        std::fs::write(
            directory.join(format!("{lane}.link-stderr")),
            &linked.stderr,
        )
        .unwrap();
        assert!(
            linked.status.success(),
            "{lane}: {}",
            String::from_utf8_lossy(&linked.stderr)
        );
        let result = std::process::Command::new(&executable).output().unwrap();
        assert!(
            result.status.success(),
            "{lane}: {:?}, {}",
            result.status,
            String::from_utf8_lossy(&result.stderr)
        );
        assert!(result.stdout.is_empty());
        std::fs::write(
            directory.join(format!("{lane}.native-status.txt")),
            format!("status={:?}\n", result.status),
        )
        .unwrap();
    }
    eprintln!(
        "TCG_CURRENT_PRIVATE_API native_lanes=2 certificates=off frontend_verify=off retained={}",
        directory.display()
    );
    positive_evidence::record(
        positive_evidence::Evidence::NativeRun,
        positive_evidence::Certs::Off,
    );
}
