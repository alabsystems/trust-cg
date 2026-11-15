//! On `x86_64-unknown-linux-gnu` the bridge refuses by name every function
//! binding its function emission cannot spell, and compiles the one it can.
//!
//! There every function definition is emitted under rustc's name as a
//! strong, default-visible global (no CGU-private namespace, no function
//! visibility), so a rustc `Internal` function and a hidden or protected one
//! would be exported and preemptible where rustc's LLVM backend keeps them
//! out of the dynamic symbol table (ruling
//! OD-BRIDGE-UNSPELLED-BINDING-20261024). For each shape, at O0 and O2, the
//! LLVM twin's object shows the binding rustc asked for, and the bridge either
//! refuses with the named code and binding or, for the default-visible
//! `External` control, writes exactly LLVM's binding.
//!
//! Link-level evidence only: this host has no x86-64 sysroot or executor, so
//! the crates are `#![no_core]` objects and nothing runs.
use super::{Artifacts, backend, checked, run_bounded, rustc_command, sha256};
use std::path::{Path, PathBuf};
use std::process::Command;

const X86_64: &str = "x86_64-unknown-linux-gnu";

const PRELUDE: &str = r#"#![feature(no_core, lang_items)]
#![no_core]
#![allow(internal_features)]

#[lang = "pointee_sized"]
pub trait PointeeSized {}
#[lang = "meta_sized"]
pub trait MetaSized: PointeeSized {}
#[lang = "sized"]
pub trait Sized: MetaSized {}
#[lang = "copy"]
pub trait Copy {}
impl Copy for u64 {}
"#;

/// A crate-private helper: rustc binds it `Internal` at one codegen unit. Its
/// address escapes, so LLVM keeps the local body at O2 too (an identity
/// function only called would be folded away).
const PRIVATE_HELPER: &str = r#"
#[inline(never)]
fn helper(x: u64) -> u64 {
    x
}

#[unsafe(no_mangle)]
pub extern "C" fn xu_c_api(x: u64) -> u64 {
    helper(x)
}

#[inline(never)]
pub fn helper_address() -> fn(u64) -> u64 {
    helper
}
"#;

/// Only exported functions: a Rust-level one (rustc gives it the session's
/// default visibility) and a C-level one (always default-visible).
const EXPORTED_ONLY: &str = r#"
#[inline(never)]
pub fn rust_api(x: u64) -> u64 {
    x
}

#[unsafe(no_mangle)]
pub extern "C" fn xu_c_api(x: u64) -> u64 {
    x
}
"#;

struct Shape {
    name: &'static str,
    body: &'static str,
    visibility: &'static str,
    /// The function the shape is about, by a fragment of its symbol.
    subject: &'static str,
    /// LLVM's (bind, visibility) for the subject.
    llvm: (&'static str, &'static str),
    /// The bridge's refusal (code, binding text), or `None` when it compiles.
    refusal: Option<(&'static str, &'static str)>,
}

const SHAPES: [Shape; 4] = [
    Shape {
        name: "internal",
        body: PRIVATE_HELPER,
        visibility: "interposable",
        subject: "6helper",
        llvm: ("LOCAL", "DEFAULT"),
        refusal: Some((
            "[TCG-LINKAGE]",
            "has rustc linkage Internal (local to its codegen unit)",
        )),
    },
    Shape {
        name: "hidden",
        body: EXPORTED_ONLY,
        visibility: "hidden",
        subject: "8rust_api",
        llvm: ("GLOBAL", "HIDDEN"),
        refusal: Some(("[TCG-VISIBILITY]", "has rustc visibility hidden")),
    },
    Shape {
        name: "protected",
        body: EXPORTED_ONLY,
        visibility: "protected",
        subject: "8rust_api",
        llvm: ("GLOBAL", "PROTECTED"),
        refusal: Some(("[TCG-VISIBILITY]", "has rustc visibility protected")),
    },
    Shape {
        name: "spelled",
        body: EXPORTED_ONLY,
        visibility: "interposable",
        subject: "8rust_api",
        llvm: ("GLOBAL", "DEFAULT"),
        refusal: None,
    },
];

/// (name, type, bind, visibility) of every defined function row.
fn function_rows(dir: &Path) -> Vec<(String, String, String, String)> {
    let mut objects: Vec<PathBuf> = std::fs::read_dir(dir)
        .unwrap()
        .map(|entry| entry.unwrap().path())
        .filter(|path| path.extension().is_some_and(|ext| ext == "o"))
        .collect();
    objects.sort();
    assert!(!objects.is_empty(), "no object in {}", dir.display());
    let listing = checked(
        Command::new("readelf")
            .args(["--wide", "--syms"])
            .args(&objects),
        30,
        &dir.join("symbols.log"),
    );
    String::from_utf8(listing.stdout)
        .unwrap()
        .lines()
        .filter_map(|line| {
            let fields: Vec<&str> = line.split_whitespace().collect();
            (fields.len() >= 8 && fields[3] == "FUNC" && fields[fields.len() - 2] != "UND").then(
                || {
                    (
                        fields[fields.len() - 1].to_owned(),
                        fields[3].to_owned(),
                        fields[4].to_owned(),
                        fields[5].to_owned(),
                    )
                },
            )
        })
        .collect()
}

#[test]
fn x86_64_linux_bridge_refuses_unspelled_function_bindings_by_name() {
    let temp = checked(
        Command::new("mktemp").args(["-d", "-t", "trust-cg-x86-64-binding.XXXXXX"]),
        10,
        &std::env::temp_dir().join("trust-cg-x86-64-binding-mktemp.log"),
    );
    let artifacts = Artifacts(PathBuf::from(
        String::from_utf8(temp.stdout).unwrap().trim(),
    ));
    let root = &artifacts.0;
    let (backend, digest) = backend(root);
    let (mut refusals, mut spelled) = (0, 0);
    for shape in &SHAPES {
        let source = root.join(format!("{}.rs", shape.name));
        std::fs::write(&source, format!("{PRELUDE}{}", shape.body)).unwrap();
        for opt in [0, 2] {
            let mut rows = Vec::new();
            for compiler in ["llvm", "cg"] {
                let dir = root.join(format!("{}-{compiler}-O{opt}", shape.name));
                std::fs::create_dir(&dir).unwrap();
                let mut command = rustc_command();
                command.args([
                    "--crate-type=lib",
                    "--crate-name=xu",
                    "--emit=obj",
                    "-Ccodegen-units=1",
                    "-Cpanic=abort",
                    "--target",
                    X86_64,
                ]);
                command
                    .arg(format!("-Copt-level={opt}"))
                    .arg(format!("-Zdefault-visibility={}", shape.visibility));
                if compiler == "cg" {
                    command
                        .arg(format!("-Zcodegen-backend={}", backend.display()))
                        .arg("-Ztrust-ir-cg-args=diag-json no-proof-certs");
                }
                command.arg(&source).arg("--out-dir").arg(&dir);
                let (output, transcript) = run_bounded(&mut command, 180, &dir.join("compile.log"));
                if let (Some((code, binding)), "cg") = (shape.refusal, compiler) {
                    assert_eq!(
                        output.status.code(),
                        Some(1),
                        "{}: the bridge must refuse, not crash or compile: {transcript}",
                        shape.name
                    );
                    let stderr = String::from_utf8_lossy(&output.stderr);
                    let named = stderr.lines().any(|line| {
                        line.contains(&format!("{code} function `"))
                            && line.contains(shape.subject)
                            && line.contains(binding)
                            && line.contains(X86_64)
                    });
                    assert!(
                        named,
                        "{}: the refusal must name {code}, the function and its binding: \
                         {transcript}",
                        shape.name
                    );
                    refusals += 1;
                    continue;
                }
                assert!(
                    output.status.success(),
                    "{} {compiler} O{opt} failed: {transcript}",
                    shape.name
                );
                rows.push(function_rows(&dir));
            }
            let subject: Vec<_> = rows[0]
                .iter()
                .filter(|(name, ..)| name.contains(shape.subject))
                .collect();
            assert_eq!(
                subject.len(),
                1,
                "{}: LLVM subject rows {:?}",
                shape.name,
                rows[0]
            );
            assert_eq!(
                (subject[0].2.as_str(), subject[0].3.as_str()),
                shape.llvm,
                "{}: LLVM's binding for {}",
                shape.name,
                shape.subject
            );
            if shape.refusal.is_none() {
                // The bridge writes exactly LLVM's binding for every
                // function both compilers define under the same name.
                for row in &rows[0] {
                    assert!(
                        rows[1].contains(row),
                        "{} O{opt}: the bridge lacks LLVM's row {row:?}: {:?}",
                        shape.name,
                        rows[1]
                    );
                }
                spelled += 1;
            }
        }
        assert_eq!(
            sha256(&backend),
            digest,
            "backend changed during {}",
            shape.name
        );
    }
    assert_eq!((refusals, spelled), (6, 2));
    println!(
        "TCG_X86_64_UNSPELLED_BINDING refusals={refusals} spelled_controls={spelled} \
         backend_sha256={digest}"
    );
}
