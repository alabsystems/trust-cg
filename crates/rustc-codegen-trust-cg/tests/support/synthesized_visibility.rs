//! The functions the bridge synthesizes (the allocator shim and the C `main`)
//! carry the visibility rustc's LLVM backend gives them, so a C shared object
//! over a bridge staticlib exports and interposes exactly what LLVM's does.
//!
//! rustc's LLVM backend defines each `__rust_*` allocator wrapper, the
//! `__rust_no_alloc_shim_is_unstable_v2` marker and `main` with the session's
//! default visibility (`-Zdefault-visibility`) and declares every `__rdl_*`
//! callee hidden (`create_wrapper_function`, `declare_entry_fn`). For each
//! default visibility (interposable, hidden, protected) at O0 and O2 this
//! test builds the same Box-allocating staticlib with LLVM and with the
//! bridge, compares the shim object's symbol rows for those names, links it
//! into a C shared object with GNU ld, gold and LLD, compares the exported
//! names, and runs an executable over that object plain and under an
//! `LD_PRELOAD` interposer of `__rdl_alloc` and of `__rust_alloc`: the bridge
//! must interpose exactly as often as LLVM does, which is never for
//! `__rdl_alloc` and never for `__rust_alloc` under hidden or protected. A bin
//! of the same visibilities must define `main` with LLVM's binding and run.
//!
//! Evidence boundary: native testing on this host with
//! `-Ztrust-verify=off` and the `no-proof-certs` knob; gcc, the three linkers
//! and the glibc loader are trusted. No loader or proof claim.
use super::{Artifacts, TARGET, backend, checked, rustc_command, sha256};
use std::collections::BTreeSet;
use std::path::{Path, PathBuf};
use std::process::Command;

const STATICLIB: &str = r#"#[unsafe(no_mangle)]
pub extern "C" fn sv_box(x: u64) -> u64 {
    // black_box keeps the allocation (LLVM removes an unobserved one).
    let b = std::hint::black_box(Box::new(x));
    *b + 1
}
"#;

const BIN: &str = r#"fn main() {
    let b = std::hint::black_box(Box::new(41u64));
    println!("sv main {}", *b + 1);
}
"#;

const LIBRARY: &str = r#"#include <stdint.h>
uint64_t sv_box(uint64_t);
uint64_t drv_box(uint64_t x) { return sv_box(x); }
"#;

const MAIN: &str = r#"#include <stdint.h>
#include <stdio.h>
uint64_t drv_box(uint64_t);
int main(void) {
  printf("box=%llu\n", (unsigned long long)drv_box(5));
  return 0;
}
"#;

/// The shim names rustc's LLVM backend gives a visibility, by suffix of the
/// mangled `__rustc`-crate symbol.
const WRAPPERS: [&str; 6] = [
    "___rust_alloc",
    "___rust_dealloc",
    "___rust_realloc",
    "___rust_alloc_zeroed",
    "___rust_alloc_error_handler",
    "___rust_no_alloc_shim_is_unstable_v2",
];
const CALLEES: [&str; 5] = [
    "___rdl_alloc",
    "___rdl_dealloc",
    "___rdl_realloc",
    "___rdl_alloc_zeroed",
    "___rdl_alloc_error_handler",
];
const VISIBILITIES: [(&str, &str); 3] = [
    ("interposable", "DEFAULT"),
    ("hidden", "HIDDEN"),
    ("protected", "PROTECTED"),
];
const LINKERS: [&str; 3] = ["bfd", "gold", "lld"];

fn is_shim_name(name: &str) -> bool {
    WRAPPERS
        .iter()
        .chain(&CALLEES)
        .any(|suffix| name.ends_with(suffix))
}

/// One `readelf --wide --syms` row of an archive member: (member, name, type,
/// bind, visibility, section index).
type Row = (String, String, String, String, String, String);

fn archive_rows(archive: &Path, log: &Path) -> Vec<Row> {
    let listing = checked(
        Command::new("readelf")
            .args(["--wide", "--syms"])
            .arg(archive),
        60,
        log,
    );
    let mut member = String::new();
    let mut rows = Vec::new();
    for line in String::from_utf8(listing.stdout).unwrap().lines() {
        if let Some(name) = line.strip_prefix("File: ") {
            member = name.trim().to_owned();
            continue;
        }
        let fields: Vec<&str> = line.split_whitespace().collect();
        let numbered = fields
            .first()
            .and_then(|n| n.strip_suffix(':'))
            .is_some_and(|n| n.parse::<usize>().is_ok());
        if numbered && fields.len() >= 8 {
            rows.push((
                member.clone(),
                fields[fields.len() - 1].to_owned(),
                fields[3].to_owned(),
                fields[4].to_owned(),
                fields[5].to_owned(),
                fields[fields.len() - 2].to_owned(),
            ));
        }
    }
    rows
}

/// The allocator shim's symbol rows: the one archive member that defines
/// `__rust_alloc`, restricted to the shim names, as (name, bind, visibility,
/// defined).
fn shim_rows(archive: &Path, log: &Path) -> BTreeSet<(String, String, String, bool)> {
    let rows = archive_rows(archive, log);
    let members: BTreeSet<&str> = rows
        .iter()
        .filter(|(_, name, kind, _, _, ndx)| {
            name.ends_with("___rust_alloc") && kind == "FUNC" && ndx != "UND"
        })
        .map(|(member, ..)| member.as_str())
        .collect();
    assert_eq!(
        members.len(),
        1,
        "exactly one member of {} must define __rust_alloc: {members:?}",
        archive.display()
    );
    let member = members.into_iter().next().unwrap();
    // Symbol rows only: LLVM's function sections give each wrapper's
    // `.text.<name>` section a section symbol readelf prints by that name.
    rows.iter()
        .filter(|(m, name, kind, ..)| {
            m == member && is_shim_name(name) && kind != "SECTION" && kind != "FILE"
        })
        .map(|(_, name, _, bind, vis, ndx)| (name.clone(), bind.clone(), vis.clone(), ndx != "UND"))
        .collect()
}

/// The shim names a shared object exports (defined in `.dynsym`).
fn exported_shim_names(object: &Path, log: &Path) -> BTreeSet<String> {
    let listing = checked(
        Command::new("readelf")
            .args(["--wide", "--dyn-syms"])
            .arg(object),
        30,
        log,
    );
    String::from_utf8(listing.stdout)
        .unwrap()
        .lines()
        .filter_map(|line| {
            let fields: Vec<&str> = line.split_whitespace().collect();
            (fields.len() >= 8 && fields[fields.len() - 2] != "UND").then(|| {
                fields[fields.len() - 1]
                    .split('@')
                    .next()
                    .unwrap()
                    .to_owned()
            })
        })
        .filter(|name| is_shim_name(name))
        .collect()
}

/// An `LD_PRELOAD` library defining `symbol` as an allocator that reports
/// each call on stderr.
fn interposer(root: &Path, tag: &str, symbol: &str) -> PathBuf {
    let source = root.join(format!("interpose_{tag}.c"));
    std::fs::write(
        &source,
        format!(
            "#include <stdio.h>\n#include <stdlib.h>\n#include <stddef.h>\n\
             void *tcg_hook(size_t s, size_t a) __asm__(\"{symbol}\");\n\
             void *tcg_hook(size_t s, size_t a) {{\n\
             \x20 fprintf(stderr, \"INTERPOSED {tag}\\n\");\n\
             \x20 return aligned_alloc(a, (s + a - 1) / a * a);\n}}\n"
        ),
    )
    .unwrap();
    // Shared objects here are named `.dso`: a `.so` literal is reserved for the
    // backend library by the backend-selection lint, and the loader needs no suffix.
    let library = root.join(format!("interpose_{tag}.dso"));
    checked(
        Command::new("cc")
            .args(["-shared", "-fPIC", "-O1"])
            .arg(&source)
            .arg("-o")
            .arg(&library),
        60,
        &root.join(format!("interpose_{tag}.log")),
    );
    library
}

fn compile_staticlib(source: &Path, dir: &Path, vis: &str, opt: u32, backend: Option<&Path>) {
    std::fs::create_dir(dir).unwrap();
    let mut command = rustc_command();
    command.args([
        "--crate-type=staticlib",
        "--crate-name=sv",
        "-Ccodegen-units=1",
        "-Cpanic=abort",
        "--target",
        TARGET,
    ]);
    command
        .arg(format!("-Copt-level={opt}"))
        .arg(format!("-Zdefault-visibility={vis}"));
    if let Some(backend) = backend {
        command
            .arg(format!("-Zcodegen-backend={}", backend.display()))
            .arg("-Ztrust-ir-cg-args=diag-json no-proof-certs");
    }
    command.arg(source).arg("-o").arg(dir.join("libsv.a"));
    checked(&mut command, 300, &dir.join("compile.log"));
}

#[test]
fn no_proof_synthesized_function_visibility_matches_llvm() {
    let temp = checked(
        Command::new("mktemp").args(["-d", "-t", "trust-cg-synthesized-visibility.XXXXXX"]),
        10,
        &std::env::temp_dir().join("trust-cg-synthesized-visibility-mktemp.log"),
    );
    let artifacts = Artifacts(PathBuf::from(
        String::from_utf8(temp.stdout).unwrap().trim(),
    ));
    let root = &artifacts.0;
    let (backend, digest) = backend(root);
    for (name, text) in [
        ("sv.rs", STATICLIB),
        ("sv_main.rs", BIN),
        ("library.c", LIBRARY),
        ("main.c", MAIN),
    ] {
        std::fs::write(root.join(name), text).unwrap();
    }
    for linker in LINKERS {
        checked(
            Command::new("cc")
                .arg(format!("-fuse-ld={linker}"))
                .arg("-Wl,--version"),
            30,
            &root.join(format!("linker-{linker}.log")),
        );
    }
    let mut interposers: Option<[(PathBuf, &str); 2]> = None;
    let (mut shared_links, mut executions, mut interposed_runs) = (0, 0, 0);
    for (vis, readelf_vis) in VISIBILITIES {
        for opt in [0, 2] {
            let mut lanes = Vec::new();
            for compiler in ["llvm", "cg"] {
                let dir = root.join(format!("{compiler}-{vis}-O{opt}"));
                compile_staticlib(
                    &root.join("sv.rs"),
                    &dir,
                    vis,
                    opt,
                    (compiler == "cg").then_some(backend.as_path()),
                );
                let archive = dir.join("libsv.a");
                let shim = shim_rows(&archive, &dir.join("symbols.log"));
                let interposers = interposers.get_or_insert_with(|| {
                    let name = |suffix: &str| {
                        shim.iter()
                            .map(|(name, ..)| name.as_str())
                            .find(|name| name.ends_with(suffix))
                            .unwrap_or_else(|| panic!("no {suffix} in the LLVM shim: {shim:?}"))
                            .to_owned()
                    };
                    [
                        (
                            interposer(root, "rdl", &name("___rdl_alloc")),
                            "INTERPOSED rdl",
                        ),
                        (
                            interposer(root, "rust_alloc", &name("___rust_alloc")),
                            "INTERPOSED rust_alloc",
                        ),
                    ]
                });
                let mut exported = Vec::new();
                let mut counts = Vec::new();
                for linker in LINKERS {
                    let library = dir.join(format!("libdrv-{linker}.dso"));
                    checked(
                        Command::new("cc")
                            .args(["-shared", "-fPIC"])
                            .arg(format!("-fuse-ld={linker}"))
                            .arg(root.join("library.c"))
                            .arg(&archive)
                            .arg("-o")
                            .arg(&library),
                        120,
                        &dir.join(format!("library-{linker}.log")),
                    );
                    shared_links += 1;
                    exported.push(exported_shim_names(
                        &library,
                        &dir.join(format!("dynsym-{linker}.log")),
                    ));
                    let executable = dir.join(format!("main-{linker}.elf"));
                    checked(
                        Command::new("cc")
                            .arg(format!("-fuse-ld={linker}"))
                            .arg(root.join("main.c"))
                            .arg(&library)
                            .arg(format!("-Wl,-rpath,{}", dir.display()))
                            .arg("-o")
                            .arg(&executable),
                        60,
                        &dir.join(format!("main-{linker}.log")),
                    );
                    let plain = checked(
                        &mut Command::new(&executable),
                        20,
                        &dir.join(format!("run-{linker}.log")),
                    );
                    assert_eq!(plain.stdout, b"box=6\n");
                    assert!(plain.stderr.is_empty());
                    executions += 1;
                    for (index, (preload, marker)) in interposers.iter().enumerate() {
                        let run = checked(
                            Command::new(&executable).env("LD_PRELOAD", preload),
                            20,
                            &dir.join(format!("run-{linker}-preload{index}.log")),
                        );
                        assert_eq!(run.stdout, b"box=6\n");
                        let count = String::from_utf8_lossy(&run.stderr)
                            .lines()
                            .filter(|line| line.trim() == *marker)
                            .count();
                        counts.push(count);
                        executions += 1;
                        interposed_runs += usize::from(count > 0);
                    }
                }
                lanes.push((shim, exported, counts));
            }
            let (llvm, cg) = (&lanes[0], &lanes[1]);
            // Every name but the allocation-error handler pair, which the
            // shim carries only when no crate supplies the handler (std does).
            for suffix in WRAPPERS
                .iter()
                .chain(&CALLEES)
                .filter(|suffix| !suffix.ends_with("_alloc_error_handler"))
            {
                assert_eq!(
                    llvm.0
                        .iter()
                        .filter(|(name, ..)| name.ends_with(suffix))
                        .count(),
                    1,
                    "{vis} O{opt}: LLVM's shim has no single {suffix} row: {:?}",
                    llvm.0
                );
            }
            assert_eq!(
                cg.0, llvm.0,
                "{vis} O{opt}: the shim's symbol rows differ from LLVM's"
            );
            for (name, bind, row_vis, defined) in &llvm.0 {
                let wrapper = WRAPPERS.iter().any(|suffix| name.ends_with(suffix));
                assert_eq!(bind, "GLOBAL", "{name}");
                assert_eq!(*defined, wrapper, "{name}");
                let expected = if wrapper { readelf_vis } else { "HIDDEN" };
                assert_eq!(row_vis, expected, "{vis} O{opt}: LLVM's {name}");
            }
            assert_eq!(
                cg.1, llvm.1,
                "{vis} O{opt}: the shared objects export different shim names"
            );
            assert_eq!(
                cg.2, llvm.2,
                "{vis} O{opt}: LD_PRELOAD interposes the bridge's shim differently from LLVM's \
                 (per linker: rdl, rust_alloc)"
            );
            for (index, linker) in LINKERS.iter().enumerate() {
                // The callees the shim declares hidden stay out of `.dynsym`
                // (std's other `__rdl_*` definitions, such as the allocation
                // error handler the shim does not forward to, may be exported).
                for (name, ..) in llvm.0.iter().filter(|(_, _, _, defined)| !defined) {
                    assert!(
                        !llvm.1[index].contains(name),
                        "{vis} O{opt} {linker}: the shim's hidden callee {name} is exported"
                    );
                }
                assert_eq!(
                    llvm.2[2 * index],
                    0,
                    "{vis} O{opt} {linker}: __rdl_alloc interposed"
                );
                if vis != "interposable" {
                    assert_eq!(
                        llvm.2[2 * index + 1],
                        0,
                        "{vis} O{opt} {linker}: __rust_alloc interposed"
                    );
                }
            }
        }
        // The bin: `main` takes the default visibility, and the program runs.
        let mut mains = Vec::new();
        for compiler in ["llvm", "cg"] {
            let dir = root.join(format!("{compiler}-{vis}-bin"));
            std::fs::create_dir(&dir).unwrap();
            let mut command = rustc_command();
            command.args([
                "--crate-type=bin",
                "--crate-name=sv_main",
                "--emit=obj,link",
                "-Ccodegen-units=1",
                "-Cpanic=abort",
                "-Copt-level=0",
                "--target",
                TARGET,
            ]);
            command.arg(format!("-Zdefault-visibility={vis}"));
            if compiler == "cg" {
                command
                    .arg(format!("-Zcodegen-backend={}", backend.display()))
                    .arg("-Ztrust-ir-cg-args=diag-json no-proof-certs");
            }
            command
                .arg(root.join("sv_main.rs"))
                .arg("--out-dir")
                .arg(&dir);
            checked(&mut command, 300, &dir.join("compile.log"));
            let listing = checked(
                Command::new("readelf")
                    .args(["--wide", "--syms"])
                    .arg(dir.join("sv_main.o")),
                30,
                &dir.join("symbols.log"),
            );
            let rows: Vec<(String, String, String)> = String::from_utf8(listing.stdout)
                .unwrap()
                .lines()
                .filter_map(|line| {
                    let fields: Vec<&str> = line.split_whitespace().collect();
                    (fields.len() >= 8 && fields[fields.len() - 1] == "main").then(|| {
                        (
                            fields[3].to_owned(),
                            fields[4].to_owned(),
                            fields[5].to_owned(),
                        )
                    })
                })
                .collect();
            assert_eq!(rows.len(), 1, "{compiler} {vis}: `main` rows {rows:?}");
            let run = checked(
                &mut Command::new(dir.join("sv_main")),
                20,
                &dir.join("run.log"),
            );
            assert_eq!(run.stdout, b"sv main 42\n");
            executions += 1;
            mains.push(rows[0].clone());
        }
        assert_eq!(
            mains[0],
            (
                "FUNC".to_owned(),
                "GLOBAL".to_owned(),
                readelf_vis.to_owned()
            ),
            "{vis}: LLVM's main"
        );
        assert_eq!(
            mains[1], mains[0],
            "{vis}: the bridge's main differs from LLVM's"
        );
        assert_eq!(sha256(&backend), digest, "backend changed during {vis}");
    }
    assert_eq!(shared_links, 36);
    println!(
        "TCG_SYNTHESIZED_VISIBILITY shared_links={shared_links} executions={executions} \
         interposed_runs={interposed_runs} backend_sha256={digest}"
    );
}
