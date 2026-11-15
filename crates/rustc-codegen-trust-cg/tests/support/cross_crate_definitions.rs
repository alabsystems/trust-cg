//! Two bridge-built crates in one link keep rustc's per-crate local copies
//! apart, and every other function symbol keeps the binding and visibility of
//! rustc's own LLVM objects.
//!
//! rustc gives every crate that instantiates a non-generic `#[inline]` core
//! function, or (from O2) a cross-crate-inlinable trait method, its own
//! `Internal` copy under ONE mangled name that names no instantiating crate
//! (`cross_crate_definitions/fixture.rs`). A bridge that emits those copies as
//! strong global definitions under that name cannot link a bridge-built binary
//! against a bridge-built library: "multiple definition of `<u64 as
//! core::convert::From<u16>>::from'", `<i128>::wrapping_mul` and `<fixture::TA
//! as fixture::Tr>::t` (all three measured with the bridge at f0ccd49b0; the
//! first and last also at 13a7b0ad9 with both of its linkage layers disabled,
//! whose binary emits no `wrapping_mul` copy). Every backend pairing
//! runs at O0-O3 against an independently computed expectation, and each
//! crate's defined ELF symbols are compared with the LLVM objects of the same
//! crate. Diagnostic native execution under `no-proof-certs`; it does not
//! qualify mandatory machine proof.
use super::{Artifacts, TARGET, backend, checked, rustc_command, sha256};
use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};
use std::process::Command;

const LANES: [&str; 2] = ["llvm", "cg"];
/// (library backend, binary backend); the first pairing is the LLVM oracle.
const PAIRINGS: [(&str, &str); 4] = [
    ("llvm", "llvm"),
    ("cg", "cg"),
    ("cg", "llvm"),
    ("llvm", "cg"),
];

/// Every defined ELF symbol of one crate's objects, by name:
/// (type, binding, visibility) per definition.
type Definitions = BTreeMap<String, Vec<(String, String, String)>>;

/// The driver's output, computed here rather than read off any compiled
/// program.
fn expected_stdout() -> String {
    let fold = |x: i128| (x as u64) ^ ((x >> 64) as u64);
    let h: i128 = -0x1234_5678_9abc_def0_1122_3344_5566_7788;
    format!(
        "41 43\n124 127\n{} {}\n",
        fold(h.wrapping_mul(3).wrapping_add(0x11)),
        fold(h.wrapping_mul(5).wrapping_sub(0x22))
    )
}

fn objects(dir: &Path) -> Vec<PathBuf> {
    let mut objects: Vec<_> = std::fs::read_dir(dir)
        .unwrap()
        .map(|entry| entry.unwrap().path())
        .filter(|path| path.extension().is_some_and(|ext| ext == "o"))
        .collect();
    objects.sort();
    assert!(!objects.is_empty(), "missing objects in {}", dir.display());
    objects
}

fn definitions(objects: &[PathBuf], log: &Path) -> Definitions {
    let output = checked(
        Command::new("readelf")
            .args(["--wide", "--syms"])
            .args(objects),
        60,
        log,
    );
    let mut definitions = Definitions::new();
    for line in String::from_utf8(output.stdout).unwrap().lines() {
        let fields: Vec<&str> = line.split_whitespace().collect();
        if fields.len() < 7
            || !fields[0]
                .strip_suffix(':')
                .is_some_and(|n| n.parse::<usize>().is_ok())
        {
            continue;
        }
        // Annotations such as `[VARIANT_PCS]` sit between visibility and index.
        let rest: Vec<&str> = fields[6..]
            .iter()
            .copied()
            .filter(|field| !field.starts_with('['))
            .collect();
        let (Some(&index), Some(&name)) = (rest.first(), rest.get(1)) else {
            continue;
        };
        let (ty, bind, vis) = (fields[3], fields[4], fields[5]);
        if index == "UND" || matches!(ty, "SECTION" | "FILE") || name.starts_with('$') {
            continue;
        }
        definitions.entry(name.to_owned()).or_default().push((
            ty.to_owned(),
            bind.to_owned(),
            vis.to_owned(),
        ));
    }
    definitions
}

/// This crate's v0 `Cs<disambiguator>_<len><name>` token, read off one of its
/// own LLVM-defined symbols.
fn crate_tag(crate_name: &str, llvm: &Definitions) -> String {
    let ident = format!("_{}{crate_name}", crate_name.len());
    llvm.keys()
        .find_map(|symbol| {
            let end = symbol.find(&ident)? + ident.len();
            let start = symbol[..end].rfind("Cs")?;
            Some(symbol[start..end].to_owned())
        })
        .unwrap_or_else(|| panic!("no v0 symbol of `{crate_name}` in its LLVM objects"))
}

/// Whether rustc's mono-item listing places a function naming `item` in this
/// crate with `Internal` linkage.
fn placed_internal(mono: &str, item: &str) -> bool {
    mono.lines().any(|line| {
        line.starts_with("MONO_ITEM fn ") && line.contains(item) && line.ends_with("[Internal]")
    })
}

/// Compare one crate's bridge definitions with the LLVM objects of the same
/// crate; returns how many CGU-private definitions the bridge emitted.
fn check_crate(opt: u32, crate_name: &str, cg: &Definitions, llvm: &Definitions) -> usize {
    let tag = crate_tag(crate_name, llvm);
    let private_prefix = format!("__trust_cg_private.{crate_name}.");
    let mut private = 0;
    for (name, rows) in cg {
        for (ty, bind, vis) in rows {
            if bind == "LOCAL" {
                continue;
            }
            let what =
                format!("O{opt} {crate_name}: the bridge defines `{name}` {ty} {bind} {vis}");
            if let Some(llvm_rows) = llvm.get(name) {
                let nonlocal: Vec<_> = llvm_rows.iter().filter(|(_, b, _)| b != "LOCAL").collect();
                // The defect: an `Internal` copy (local in rustc's own object)
                // defined under rustc's name where another crate can see it.
                assert!(
                    !nonlocal.is_empty(),
                    "{what}, which rustc's LLVM object binds LOCAL (an Internal copy)"
                );
                assert!(
                    nonlocal.iter().any(|(_, b, v)| b == bind && v == vis),
                    "{what}; LLVM defines it {nonlocal:?}"
                );
            } else if name.starts_with("__trust_cg_private.") {
                // An `Internal` copy under its CGU-qualified name: hidden, and
                // qualified by this crate's own codegen unit.
                assert!(
                    ty == "FUNC"
                        && bind == "GLOBAL"
                        && vis == "HIDDEN"
                        && name.starts_with(&private_prefix),
                    "{what}; a CGU-private copy must be a hidden global function of a `{crate_name}` CGU"
                );
                private += 1;
            } else {
                // Backend-owned runtime helpers and the EH personality
                // reference; anything else must name this crate, so that no
                // other crate's object can define the same symbol.
                assert!(
                    name.starts_with("__trustcg_")
                        || name == "DW.ref.rust_eh_personality"
                        || name.contains(&tag),
                    "{what}, which LLVM does not define and which does not name `{crate_name}` ({tag})"
                );
            }
        }
    }
    private
}

fn strong(definitions: &Definitions) -> BTreeSet<&str> {
    definitions
        .iter()
        .filter(|(_, rows)| rows.iter().any(|(_, bind, _)| bind == "GLOBAL"))
        .map(|(name, _)| name.as_str())
        .collect()
}

/// One compile; returns rustc's `-Zprint-mono-items=yes` listing.
fn compile(backend: &Path, lane: &str, opt: u32, dir: &Path, args: &[String]) -> String {
    let mut command = rustc_command();
    command
        .args([
            "--target",
            TARGET,
            "-Ccodegen-units=1",
            "-Zprint-mono-items=yes",
        ])
        .arg(format!("-Copt-level={opt}"))
        .args(args);
    if lane == "cg" {
        command
            .arg(format!("-Zcodegen-backend={}", backend.display()))
            .arg("-Ztrust-ir-cg-args=diag-json no-proof-certs");
    }
    let output = checked(&mut command, 600, &dir.join("compile.log"));
    String::from_utf8_lossy(&output.stdout).into_owned()
}

#[test]
fn no_proof_cross_crate_local_copies_link_and_match_llvm() {
    let temp = checked(
        Command::new("mktemp").args(["-d", "-t", "trust-cg-cross-crate-definitions.XXXXXX"]),
        10,
        &std::env::temp_dir().join("trust-cg-cross-crate-definitions-mktemp.log"),
    );
    let artifacts = Artifacts(PathBuf::from(
        String::from_utf8(temp.stdout).unwrap().trim(),
    ));
    let root = &artifacts.0;
    let (backend, digest) = backend(root);
    for (name, source) in [
        (
            "fixture.rs",
            include_str!("cross_crate_definitions/fixture.rs"),
        ),
        (
            "driver.rs",
            include_str!("cross_crate_definitions/driver.rs"),
        ),
    ] {
        std::fs::write(root.join(name), source).unwrap();
    }
    let expected = expected_stdout();
    let (mut runs, mut private_definitions) = (0, 0);
    for opt in 0..=3 {
        let level = root.join(format!("O{opt}"));
        std::fs::create_dir(&level).unwrap();
        // The class under test: rustc copies each item into BOTH crates as an
        // `Internal` mono item under one crate-agnostic name. Without it the
        // test would pass vacuously.
        let copied: &[&str] = if opt < 2 {
            &["From<u16> for u64>::from", "<impl i128>::wrapping_mul"]
        } else {
            &["From<u16> for u64>::from", "Tr>::t"]
        };
        let mut libraries = BTreeMap::new();
        for lane in LANES {
            let dir = level.join(format!("library-{lane}"));
            std::fs::create_dir(&dir).unwrap();
            let rlib = dir.join("libfixture.rlib");
            let mono = compile(
                &backend,
                lane,
                opt,
                &dir,
                &[
                    "--crate-type=rlib".into(),
                    "--crate-name=fixture".into(),
                    "-o".into(),
                    rlib.display().to_string(),
                    root.join("fixture.rs").display().to_string(),
                ],
            );
            for item in copied {
                assert!(
                    placed_internal(&mono, item),
                    "O{opt} {lane}: rustc no longer places `{item}` in the library as an Internal copy"
                );
            }
            let members = dir.join("members");
            std::fs::create_dir(&members).unwrap();
            checked(
                Command::new("ar").arg("x").arg(&rlib).current_dir(&members),
                30,
                &dir.join("extract.log"),
            );
            let symbols = definitions(&objects(&members), &dir.join("symbols.log"));
            libraries.insert(lane, (rlib, symbols));
        }
        let mut binaries = BTreeMap::new();
        for (library, binary) in PAIRINGS {
            let dir = level.join(format!("{library}-{binary}"));
            std::fs::create_dir(&dir).unwrap();
            let program = dir.join("program");
            let mono = compile(
                &backend,
                binary,
                opt,
                &dir,
                &[
                    "--crate-type=bin".into(),
                    "--crate-name=driver".into(),
                    "-Csave-temps".into(),
                    format!("--extern=fixture={}", libraries[library].0.display()),
                    "-o".into(),
                    program.display().to_string(),
                    root.join("driver.rs").display().to_string(),
                ],
            );
            for item in copied {
                assert!(
                    placed_internal(&mono, item),
                    "O{opt} {binary}: rustc no longer places `{item}` in the binary as an Internal copy"
                );
            }
            let output = checked(&mut Command::new(&program), 60, &dir.join("run.log"));
            assert_eq!(
                String::from_utf8_lossy(&output.stdout),
                expected,
                "O{opt}: {library} library with {binary} binary"
            );
            assert!(
                output.stderr.is_empty(),
                "O{opt}: {library} library with {binary} binary wrote stderr"
            );
            runs += 1;
            if library == binary {
                binaries.insert(
                    binary,
                    definitions(&objects(&dir), &dir.join("symbols.log")),
                );
            }
        }
        for (crate_name, cg, llvm) in [
            ("fixture", &libraries["cg"].1, &libraries["llvm"].1),
            ("driver", &binaries["cg"], &binaries["llvm"]),
        ] {
            let private = check_crate(opt, crate_name, cg, llvm);
            assert!(
                private > 0,
                "O{opt} {crate_name}: no CGU-private copy was emitted"
            );
            private_definitions += private;
        }
        let library = strong(&libraries["cg"].1);
        let binary = strong(&binaries["cg"]);
        let both: Vec<_> = library.intersection(&binary).collect();
        assert!(
            both.is_empty(),
            "O{opt}: both bridge-built crates define the strong symbols {both:?}"
        );
    }
    assert_eq!(sha256(&backend), digest);
    eprintln!(
        "cross-crate local copies: {runs} native runs over 4 pairings at O0-O3, \
         {private_definitions} CGU-private definitions checked against LLVM's objects"
    );
}
