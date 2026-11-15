//! A `FnOnce` closure body that another crate calls BY SYMBOL because it
//! compiles its own copy of the closure's cross-crate-inlinable defining
//! function, at `-Copt-level=0`, where the defining crate exports the body
//! (`-Zshare-generics`). Stable code, no feature gate.
//!
//! `#[inline(always)] fn mk(b, k) -> u64 { run(move |x| ..) }` with an
//! `#[inline(always)] run<F: FnOnce(u64) -> u64>` is compiled by every crate
//! that calls `mk`, and at O0 that copy calls the defining crate's exported
//! closure body. While the bridge declared every closure environment as a
//! pointer to the closure, rustc passed an environment of at most 16 bytes of
//! scalars in registers: measured 2026-10-02 at `13a7b0ad9` (AArch64 Linux,
//! O0), oracle `v 70 63`, a bridge library with an LLVM binary SIGSEGV'd and an
//! LLVM library with a bridge binary printed pointer-like values that changed
//! between runs (`v 281474917006775 63`); the same held for a closure capturing
//! by reference (a 16-byte environment of two pointers). That was then refused
//! by name at O0 (`closure_defining_copy_reaches_body`). The bridge now declares
//! a by-value environment as argument 0 by rustc's own mode
//! (`closure_body_env_by_value`, round 10), so no crate's view of the body can
//! disagree with another's: every variant, the two controls included (an
//! `#[inline(never)]` defining function, and a closure handed only to std's
//! `Option::map`), must compile and print the oracle in all four
//! LLVM/bridge pairings at O0-O3.
//!
//! The L06-P16 verifier rounds (2026-10-03, AArch64 Linux, against the
//! refusal line `main` kept until round 10 met it) added three routes by which
//! another crate reaches such a body by symbol, each a variant or a binary
//! flag here: an LLVM binary at O0 built with `-Zinline-mir=yes` inlines
//! `Option::map::<closure>` into its copy of an `#[inline(always)]` `mk` and
//! calls the body by symbol (`std_map`; measured at `874934cbc`: SIGSEGV
//! against `v 70 63` while the environment was a pointer); an
//! `#[inline(always)]` `mk` handing the closure only to an `#[inline(never)]`
//! consumer, whose body rustc exports though every crate links that consumer
//! (`never_consumer`); and an `#[inline(never)]` defining function calling
//! `Option::map` (`std_map_not_inlined`). Under one rule (rustc's own `FnAbi`,
//! judged per signature; docs/decision-record.md
//! OD-RUST-CALL-ONE-RULE-20261008, LD-26) each must compile and print the
//! oracle in every pairing, at O0 also with the binary's MIR inliner.
//! Both backends use `-Ztrust-ir-lower=on` so rustc keeps its canonical
//! generic export list. Otherwise an unverified CG library withholds that
//! list, and an LLVM caller can instantiate its own closure body instead of
//! exercising the CG body. Verification and machine proof certificates stay
//! off; this is diagnostic native execution.
use super::{Artifacts, TARGET, backend, checked, run_bounded, rustc_command, sha256};
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

/// (library backend, binary backend); the first pairing is the LLVM oracle.
const PAIRINGS: [(&str, &str); 4] = [
    ("llvm", "llvm"),
    ("cg", "cg"),
    ("cg", "llvm"),
    ("llvm", "cg"),
];

/// `driver.rs`'s output: `mk(2, 41)` and `mk(1, 41)` with `mk(b, k) = 5 * 3 + b
/// * 7 + k`.
const ORACLE: &str = "v 70 63\n";

/// One library variant: its `mk`.
struct Variant {
    name: &'static str,
    source: &'static str,
}

const VARIANTS: [Variant; 6] = [
    Variant {
        name: "moved",
        source: "#[inline(always)]\npub fn run<F: FnOnce(u64) -> u64>(f: F) -> u64 {\n    f(5)\n}\n\
                 #[inline(always)]\npub fn mk(b: u64, k: u64) -> u64 {\n    let s = b * 7 + k;\n    \
                 run(move |x| x * 3 + s)\n}\n",
    },
    Variant {
        name: "borrowed",
        source: "#[inline(always)]\npub fn run<F: FnOnce(u64) -> u64>(f: F) -> u64 {\n    f(5)\n}\n\
                 #[inline(always)]\npub fn mk(b: u64, k: u64) -> u64 {\n    \
                 run(|x| x * 3 + b * 7 + k)\n}\n",
    },
    Variant {
        name: "not_inlined",
        source: "#[inline(always)]\npub fn run<F: FnOnce(u64) -> u64>(f: F) -> u64 {\n    f(5)\n}\n\
                 #[inline(never)]\npub fn mk(b: u64, k: u64) -> u64 {\n    let s = b * 7 + k;\n    \
                 run(move |x| x * 3 + s)\n}\n",
    },
    Variant {
        name: "std_map",
        source: "#[inline(always)]\npub fn mk(b: u64, k: u64) -> u64 {\n    \
                 Some(5u64).map(|x| x * 3 + b * 7 + k).unwrap_or(0)\n}\n",
    },
    Variant {
        name: "std_map_not_inlined",
        source: "#[inline(never)]\npub fn mk(b: u64, k: u64) -> u64 {\n    \
                 Some(5u64).map(|x| x * 3 + b * 7 + k).unwrap_or(0)\n}\n",
    },
    // The binary links `run::<closure>` from the library and never names the
    // body, while rustc exports the body at O0.
    Variant {
        name: "never_consumer",
        source: "#[inline(never)]\npub fn run<F: FnOnce(u64) -> u64>(f: F) -> u64 {\n    f(5)\n}\n\
                 #[inline(always)]\npub fn mk(b: u64, k: u64) -> u64 {\n    let s = b * 7 + k;\n    \
                 run(move |x| x * 3 + s)\n}\n",
    },
];

/// The binary's extra flags: none, and rustc's MIR inliner, which inlines the
/// library's cross-crate-inlinable and generic functions whatever their export
/// status.
const BINARY_FLAGS: [&[&str]; 2] = [&[], &["-Zinline-mir=yes"]];

const LIB_USE: &str = "#[inline(never)]\npub fn lib_use(k: u64) -> u64 {\n    mk(1, k)\n}\n";

const DRIVER: &str = "extern crate inlined;\nuse std::hint::black_box as bb;\n\nfn main() {\n    \
                      let k: u64 = bb(41);\n    \
                      println!(\"v {} {}\", inlined::mk(bb(2), k), inlined::lib_use(k));\n}\n";

fn compile(
    backend: &Path,
    lane: &str,
    opt: u32,
    dir: &Path,
    args: &[String],
    log: &str,
) -> (Output, String) {
    let mut command = rustc_command();
    command
        .args([
            "--target",
            TARGET,
            "-Ccodegen-units=1",
            "-Ztrust-ir-lower=on",
        ])
        .arg(format!("-Copt-level={opt}"))
        .args(args);
    if lane == "cg" {
        command
            .arg(format!("-Zcodegen-backend={}", backend.display()))
            .arg(super::cg_knobs());
    }
    run_bounded(&mut command, 600, &dir.join(log))
}

/// The check; each host's `#[test]` calls it (Linux AArch64 and Darwin AArch64,
/// each for its own native target).
pub(super) fn no_proof_inlined_closure_bodies_match_llvm() {
    let temp = checked(
        Command::new("mktemp").args(["-d", "-t", "trust-cg-inlined-closures.XXXXXX"]),
        10,
        &std::env::temp_dir().join("trust-cg-inlined-closures-mktemp.log"),
    );
    let artifacts = Artifacts(PathBuf::from(
        String::from_utf8(temp.stdout).unwrap().trim(),
    ));
    let root = &artifacts.0;
    let (backend, digest) = backend(root);
    std::fs::write(root.join("driver.rs"), DRIVER).unwrap();
    let mut runs = 0;
    for variant in &VARIANTS {
        let source = root.join(format!("{}.rs", variant.name));
        std::fs::write(&source, format!("{}{LIB_USE}", variant.source)).unwrap();
        for opt in 0..=3 {
            let level = root.join(variant.name).join(format!("O{opt}"));
            let mut libraries = std::collections::BTreeMap::new();
            for lane in ["llvm", "cg"] {
                let dir = level.join(format!("lib-{lane}"));
                std::fs::create_dir_all(&dir).unwrap();
                let rlib = dir.join("libinlined.rlib");
                let (output, transcript) = compile(
                    &backend,
                    lane,
                    opt,
                    &dir,
                    &[
                        "--crate-type=rlib".to_owned(),
                        "--crate-name=inlined".to_owned(),
                        "-o".to_owned(),
                        rlib.display().to_string(),
                        source.display().to_string(),
                    ],
                    "compile.log",
                );
                let what = format!("{} O{opt} ({lane} library)", variant.name);
                assert!(output.status.success(), "{what}: {transcript}");
                libraries.insert(lane, rlib);
            }
            // At O1-O3 no closure body here is exported (rustc gives a
            // cross-crate-inlinable instance a local copy), so the binary's
            // inliner is exercised at O0 only.
            let flag_sets = if opt == 0 {
                &BINARY_FLAGS[..]
            } else {
                &BINARY_FLAGS[..1]
            };
            for (inliner, flags) in flag_sets.iter().enumerate() {
                for (library, binary_lane) in PAIRINGS {
                    let rlib = &libraries[library];
                    let dir = level.join(format!("{library}-{binary_lane}-{inliner}"));
                    std::fs::create_dir_all(&dir).unwrap();
                    let program = dir.join("program");
                    let mut args = vec![
                        "--crate-type=bin".to_owned(),
                        "--crate-name=driver".to_owned(),
                        format!("--extern=inlined={}", rlib.display()),
                        "-o".to_owned(),
                        program.display().to_string(),
                    ];
                    args.extend(flags.iter().map(|flag| (*flag).to_owned()));
                    args.push(root.join("driver.rs").display().to_string());
                    let (output, transcript) =
                        compile(&backend, binary_lane, opt, &dir, &args, "compile.log");
                    let what = format!(
                        "{} O{opt}: {library} library with {binary_lane} binary {flags:?}",
                        variant.name
                    );
                    assert!(output.status.success(), "{what}: {transcript}");
                    let ran = checked(&mut Command::new(&program), 60, &dir.join("run.log"));
                    assert!(ran.stderr.is_empty(), "{what} wrote stderr");
                    assert_eq!(String::from_utf8(ran.stdout).unwrap(), ORACLE, "{what}");
                    runs += 1;
                }
            }
        }
    }
    assert_eq!(sha256(&backend), digest);
    // Four levels with the plain binary, and O0 again with the MIR inliner.
    assert_eq!(runs, VARIANTS.len() * 5 * PAIRINGS.len());
    eprintln!(
        "inlined closure bodies: {runs} native runs over 4 pairings at O0-O3 (and with the \
         binary's MIR inliner at O0), none refused"
    );
}
