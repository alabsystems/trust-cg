// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Link the selected compiler's real Rust panic runtime into the C executable.
//! LLVM O0 pointer helpers retain core's precondition checks. Their panic calls
//! need core, std's panic-abort runtime and its native dependencies even though
//! the positive ABI callers themselves are `no_std` object files.

use super::{TARGET, checked, run_bounded, rustc_command, sha256};
use std::os::unix::process::ExitStatusExt;
use std::path::{Path, PathBuf};
use std::process::Command;

pub(super) struct Runtime {
    archive: PathBuf,
    digest: String,
    native_libraries: Vec<String>,
}

impl Runtime {
    pub(super) fn build(artifacts: &Path) -> Self {
        let source = artifacts.join("scalar_cell_runtime.rs");
        let archive = artifacts.join("libscalar_cell_runtime.a");
        // The exported function is a negative control, not a replacement for
        // any core or std symbol. The selected compiler supplies those bodies.
        std::fs::write(
            &source,
            "#[unsafe(no_mangle)]\npub extern \"C\" fn scalar_cell_runtime_panic_control() -> ! { panic!(\"scalar-cell runtime control\"); }\n",
        )
        .unwrap();
        let output = checked(
            rustc_command()
                .args([
                    "--crate-type=staticlib",
                    "-Cpanic=abort",
                    "--target",
                    TARGET,
                    "--color=never",
                    "--print=native-static-libs",
                ])
                .arg(&source)
                .arg("-o")
                .arg(&archive),
            60,
            &artifacts.join("scalar_cell_runtime.compile.log"),
        );
        let diagnostics = String::from_utf8(output.stderr).unwrap();
        let native_libraries = diagnostics
            .lines()
            .filter_map(|line| line.strip_prefix("note: native-static-libs: "))
            .collect::<Vec<_>>();
        assert_eq!(native_libraries.len(), 1, "{diagnostics}");
        let native_libraries = native_libraries[0]
            .split_whitespace()
            .map(str::to_owned)
            .collect::<Vec<_>>();
        assert!(!native_libraries.is_empty());
        // Preserve the compiler's order and duplicates. No panic stubs, core
        // replacements or disabled debug/precondition checks are introduced.
        let runtime = Self {
            digest: sha256(&archive),
            archive,
            native_libraries,
        };
        let control_source = artifacts.join("scalar_cell_runtime_control.c");
        let control = artifacts.join("scalar_cell_runtime_control.elf");
        std::fs::write(
            &control_source,
            "#include <sys/resource.h>\nvoid scalar_cell_runtime_panic_control(void);\nint main(void) { struct rlimit limit = {0,0}; if (setrlimit(RLIMIT_CORE,&limit)) return 3; scalar_cell_runtime_panic_control(); return 0; }\n",
        )
        .unwrap();
        let mut linker = Command::new("cc");
        linker.arg(&control_source);
        runtime.link_into(&mut linker);
        checked(
            linker.arg("-o").arg(&control),
            60,
            &artifacts.join("scalar_cell_runtime_control.link.log"),
        );
        let (output, transcript) = run_bounded(
            &mut Command::new(&control),
            20,
            &artifacts.join("scalar_cell_runtime_control.native.log"),
        );
        assert_eq!(output.status.signal(), Some(6), "{transcript}");
        assert!(
            String::from_utf8_lossy(&output.stderr).contains("scalar-cell runtime control"),
            "{transcript}"
        );
        println!(
            "TCG_SCALAR_CELL_RUNTIME sha256={} native_libraries={:?} panic_control=SIGABRT",
            runtime.digest, runtime.native_libraries
        );
        runtime
    }

    pub(super) fn link_into(&self, command: &mut Command) {
        assert_eq!(
            sha256(&self.archive),
            self.digest,
            "runtime archive changed"
        );
        command.arg(&self.archive).args(&self.native_libraries);
    }
}
