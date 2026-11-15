// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0
//! Native ABI/runtime checks of actual CG object output. C/C++ entries exercise
//! payload, location and unwind delivery; they do not certify Rust lang items.
#[path = "common/aarch64_native.rs"]
mod native;
use trust_cg_codegen::pipeline::OptLevel;
use trust_ir::AssertKind;
#[path = "common/panic_delivery_fixture.rs"]
mod fixture;

const DRIVER: &str = r#"
#include <stdint.h>
#include <stdbool.h>
#include <unistd.h>
#include <sys/wait.h>
#include <signal.h>
extern uintptr_t tc_check(bool, uintptr_t, uintptr_t, const void *);
static int return_from_entry;
void panic_delivery_entry(uintptr_t index, uintptr_t len, const void *loc) {
    if (index != 101 || len != 37 || !loc || *(const uint64_t *)loc != 0x12345678) _exit(91);
    if (return_from_entry) return;
    _exit(0);
}
int main(void) {
    uint64_t loc = 0x12345678;
    /* No failure location/payload may be touched on the passing path. */
    if (tc_check(true, 999, 37, 0) != 37) return 92;
    for (int returning = 0; returning != 2; ++returning) {
        pid_t child = fork();
        if (child == -1) return 93;
        if (!child) {
            return_from_entry = returning;
            tc_check(false, 101, 37, &loc);
            _exit(94); /* returning entry must be followed by a trap */
        }
        int status;
        if (waitpid(child, &status, 0) != child) return 95;
        if (!returning && (!WIFEXITED(status) || WEXITSTATUS(status))) return 96;
        if (returning && (!WIFSIGNALED(status) ||
            (WTERMSIG(status) != SIGILL && WTERMSIG(status) != SIGTRAP))) return 97;
    }
    return 0;
}
"#;

#[test]
fn native_value_and_global_location_payloads_call_runtime_and_trap_if_it_returns() {
    for global in [false, true] {
        let m = fixture::module(
            AssertKind::BoundsCheck {
                index: fixture::v(1),
                len: fixture::v(2),
            },
            false,
            global,
        );
        for opt in [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3] {
            let object = native::compile(&m, opt);
            if let Some(code) = native::link_run("sited-panic-delivery", &object, DRIVER) {
                assert_eq!(code, 0, "{opt:?}/global={global}");
            }
        }
    }
}

// The existing native subprocess helper gives the C++ linker/run finite bounds.
#[path = "common/native_host.rs"]
mod native_host;
use std::{fs, process::Command};

#[test]
fn native_assert_invoke_preserves_original_cleanup_and_rethrows_to_outer_catch() {
    if !native_host::NATIVE {
        return;
    }
    let m = fixture::module(
        AssertKind::BoundsCheck {
            index: fixture::v(1),
            len: fixture::v(2),
        },
        true,
        false,
    );
    let driver = r#"
#include <stdint.h>
extern "C" uintptr_t tc_check(bool, uintptr_t, uintptr_t, const void *);
extern "C" void panic_delivery_entry(uintptr_t index, uintptr_t len, const void *loc) {
    if (index != 101 || len != 37 || !loc || *(const uint64_t *)loc != 0x12345678) throw 91;
    throw 107;
}
int main() {
    uint64_t loc = 0x12345678;
    if (tc_check(true, 999, 37, nullptr) != 37) return 92;
    try { tc_check(false, 101, 37, &loc); return 93; }
    catch (int v) { return v == 107 ? 0 : 94; }
}
"#;
    for opt in [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3] {
        let object = native::compile(&m, opt);
        let dir =
            std::env::temp_dir().join(format!("trust-cg-sited-eh-{}-{opt:?}", std::process::id()));
        fs::create_dir(&dir).expect("fresh native EH output");
        let object_path = dir.join("module.o");
        let source_path = dir.join("driver.cpp");
        let binary = dir.join("driver");
        fs::write(&object_path, object).unwrap();
        fs::write(&source_path, driver).unwrap();
        let link = native::process::command_output_with_timeout(
            Command::new("c++")
                .arg("-O2")
                .arg(&source_path)
                .arg(&object_path)
                .arg("-o")
                .arg(&binary),
            native::process::codegen_link_timeout(),
        )
        .expect("C++ native ABI reference");
        assert!(
            !link.timed_out && link.output.status.success(),
            "{:?}",
            link.output
        );
        let run = native::process::run_executable_with_timeout(
            &binary,
            native::process::codegen_run_timeout(),
        )
        .expect("native unwind delivery");
        assert!(
            !run.timed_out && run.output.status.success(),
            "{:?}",
            run.output
        );
        fs::remove_dir_all(&dir).unwrap();
    }
}
