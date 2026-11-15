//! A foreign `#[thread_local]` static declared with an import `#[linkage]` is
//! refused by name, never emitted as a strong thread-local reference.
//!
//! rustc's LLVM backend (`check_and_apply_linkage`) declares such a symbol
//! with the requested linkage as a NON-TLS reference and reads a thread-local
//! cell initialized with its address: for `extern_weak`, null when nothing
//! defines it. The native control runs that LLVM object against a C driver
//! that defines no `tls_weak` and requires the null fallback (`7`). The bridge
//! must refuse both import linkages with `[TCG-EXTERN-STATIC-LINKAGE]` naming
//! the static, at O0 and O2, under the target-default and `pie` relocation
//! models, and leave no object behind that defines the reader. The refusal
//! is the evidence; nothing here claims a TLS weak-reference lowering.
use super::{Artifacts, TARGET, backend, checked, run_bounded, rustc_command, sha256};
use std::path::{Path, PathBuf};
use std::process::Command;

const SOURCE: &str = r#"#![no_std]
#![feature(linkage, thread_local)]

unsafe extern "C" {
    #[linkage = "LINKAGE"]
    #[thread_local]
    static tls_weak: Option<unsafe extern "C" fn() -> u64>;
}

#[unsafe(no_mangle)]
pub extern "C" fn read_tls_weak() -> u64 {
    match unsafe { tls_weak } {
        Some(f) => unsafe { f() },
        None => 7,
    }
}

#[panic_handler]
fn panic(_: &core::panic::PanicInfo<'_>) -> ! {
    loop {}
}
"#;

const DRIVER: &str = r#"#include <stdint.h>
#include <stdio.h>
uint64_t read_tls_weak(void);
int main(void) {
  printf("%llu\n", (unsigned long long)read_tls_weak());
  return 0;
}
"#;

fn objects(dir: &Path) -> Vec<PathBuf> {
    let mut objects: Vec<_> = std::fs::read_dir(dir)
        .map(|entries| {
            entries
                .map(|entry| entry.unwrap().path())
                .filter(|path| path.extension().is_some_and(|ext| ext == "o"))
                .collect()
        })
        .unwrap_or_default();
    objects.sort();
    objects
}

/// `readelf --wide --syms` rows naming `symbol`: (type, bind, section index).
fn symbol_rows(objects: &[PathBuf], symbol: &str, log: &Path) -> Vec<(String, String, String)> {
    let listing = checked(
        Command::new("readelf")
            .args(["--wide", "--syms"])
            .args(objects),
        30,
        log,
    );
    String::from_utf8(listing.stdout)
        .unwrap()
        .lines()
        .filter_map(|line| {
            let fields: Vec<&str> = line.split_whitespace().collect();
            (fields.len() >= 8 && fields[fields.len() - 1] == symbol).then(|| {
                (
                    fields[3].to_owned(),
                    fields[4].to_owned(),
                    fields[fields.len() - 2].to_owned(),
                )
            })
        })
        .collect()
}

fn compile(
    source: &Path,
    dir: &Path,
    opt: u32,
    model: Option<&str>,
    backend: Option<&Path>,
) -> (std::process::Output, String) {
    std::fs::create_dir(dir).unwrap();
    let mut command = rustc_command();
    command.args([
        "--crate-type=lib",
        "--crate-name=foreign_tls_linkage",
        "--emit=obj",
        "-Ccodegen-units=1",
        "-Cpanic=abort",
        // No `core` is linked: keep the O0 pointer-alignment check (a call
        // of `panic_misaligned_pointer_dereference`) out of the reader.
        "-Cdebug-assertions=off",
        "--target",
        TARGET,
    ]);
    command.arg(format!("-Copt-level={opt}"));
    if let Some(model) = model {
        command.arg(format!("-Crelocation-model={model}"));
    }
    if let Some(backend) = backend {
        command
            .arg(format!("-Zcodegen-backend={}", backend.display()))
            .arg("-Ztrust-ir-cg-args=diag-json no-proof-certs");
    }
    command.arg(source).arg("--out-dir").arg(dir);
    run_bounded(&mut command, 180, &dir.join("compile.log"))
}

#[test]
fn no_proof_foreign_thread_local_import_linkage_is_refused_by_name() {
    let temp = checked(
        Command::new("mktemp").args(["-d", "-t", "trust-cg-foreign-tls-linkage.XXXXXX"]),
        10,
        &std::env::temp_dir().join("trust-cg-foreign-tls-linkage-mktemp.log"),
    );
    let artifacts = Artifacts(PathBuf::from(
        String::from_utf8(temp.stdout).unwrap().trim(),
    ));
    let root = &artifacts.0;
    let (backend, digest) = backend(root);
    let driver = root.join("driver.c");
    std::fs::write(&driver, DRIVER).unwrap();
    let mut llvm_runs = 0;
    let mut refusals = 0;
    for linkage in ["extern_weak", "external"] {
        let source = root.join(format!("{linkage}.rs"));
        std::fs::write(&source, SOURCE.replace("LINKAGE", linkage)).unwrap();
        for opt in [0, 2] {
            if linkage == "extern_weak" {
                // LLVM: the weak symbol is a non-TLS weak undefined reference
                // and the reader sees null when the driver defines nothing.
                let dir = root.join(format!("llvm-{linkage}-O{opt}"));
                let (output, transcript) = compile(&source, &dir, opt, None, None);
                assert!(output.status.success(), "LLVM control failed: {transcript}");
                let objects = objects(&dir);
                assert_eq!(objects.len(), 1, "{transcript}");
                let rows = symbol_rows(&objects, "tls_weak", &dir.join("symbols.log"));
                assert!(
                    !rows.is_empty()
                        && rows.iter().all(|(kind, bind, ndx)| kind != "TLS"
                            && bind == "WEAK"
                            && ndx == "UND"),
                    "LLVM's `tls_weak` must be a non-TLS weak undefined reference: {rows:?}"
                );
                let executable = dir.join("absent.elf");
                checked(
                    Command::new("cc")
                        .arg(&driver)
                        .args(&objects)
                        .arg("-o")
                        .arg(&executable),
                    60,
                    &dir.join("link.log"),
                );
                let run = checked(&mut Command::new(&executable), 20, &dir.join("run.log"));
                assert_eq!(run.stdout, b"7\n", "LLVM must read the null fallback");
                assert!(run.stderr.is_empty());
                llvm_runs += 1;
            }
            for model in [None, Some("pie")] {
                let dir = root.join(format!(
                    "cg-{linkage}-O{opt}-{}",
                    model.unwrap_or("default")
                ));
                let (output, transcript) = compile(&source, &dir, opt, model, Some(&backend));
                assert_eq!(
                    output.status.code(),
                    Some(1),
                    "the bridge must refuse, not crash or compile: {transcript}"
                );
                let stderr = String::from_utf8_lossy(&output.stderr);
                assert!(
                    stderr.contains("[TCG-EXTERN-STATIC-LINKAGE] the `extern` static `tls_weak`")
                        && stderr.contains("and `#[thread_local]`")
                        && stderr.contains("read_tls_weak"),
                    "the refusal must name the static, its thread-local import and the reader: \
                     {transcript}"
                );
                let left = objects(&dir);
                if !left.is_empty() {
                    let rows = symbol_rows(&left, "read_tls_weak", &dir.join("symbols.log"));
                    assert!(
                        rows.iter().all(|(_, _, ndx)| ndx == "UND"),
                        "a refused compile left an object defining the reader: {rows:?}"
                    );
                }
                refusals += 1;
            }
        }
        assert_eq!(sha256(&backend), digest, "backend changed during {linkage}");
    }
    assert_eq!((llvm_runs, refusals), (2, 8));
    println!(
        "TCG_FOREIGN_TLS_LINKAGE llvm_null_fallback_runs={llvm_runs} cg_refusals={refusals} \
         backend_sha256={digest}"
    );
}
