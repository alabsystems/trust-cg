// Compiled only on an aarch64-apple-darwin host: another host builds this
// target with no test in it, never one that passes without running (L06-P10).
#![cfg(all(target_os = "macos", target_arch = "aarch64"))]

#[path = "support/backend_artifact.rs"]
mod backend_artifact_support;
#[path = "support/darwin_native_prerequisites.rs"]
mod darwin_native;
#[path = "support/positive_evidence.rs"]
mod positive_evidence;
#[path = "support/toolchain.rs"]
mod toolchain_support;

// E2E (aarch64-apple-darwin): a crate built with several codegen units links.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// WHY THIS FILE EXISTS. rustc instantiates an `#[inline]` item
// (`<u64 as PartialOrd>::le`, `<i64 as From<i8>>::from`, `Ord::max::<u64>`, a
// library's `#[inline] pub fn`) as a `LocalCopy`: one `Internal` copy in EVERY
// CGU that uses it, all under one mangled name. On Mach-O the bridge emitted
// each copy under that name as an ordinary global definition, so any crate
// built with more than one codegen unit (cargo's default profiles use many)
// failed to link: `ld: 3 duplicate symbols` for `bridge_corpus/
// multi_cgu_inline_core.rs` at -Ccodegen-units=4, -O0 and -O1. The same
// collision crossed crates (an rlib's copy and its downstream binary's copy)
// and reached a separate per-function object whose file name is derived from
// the symbol, so two CGUs' copies wrote one path. Every other bridge test pins
// -Ccodegen-units=1, which is why nothing caught it.
//
// THE FIX. Apple AArch64 now uses the bridge's CGU-private function namespace
// (`src/function_linkage.rs`, `PrivateSymbolFormat::MachO`): an `Internal`
// function is emitted as `__trust_cg_private.<cgu>.<index>.<rustc symbol>`, a
// private-extern (`N_EXT | N_PEXT`) definition the objects of its own CGU call
// by name and the final link demotes to a local. The Mach-O module emitter admits exactly that
// hidden-`External` definition (trust-cg-lower
// `FunctionSymbolFactPolicy::AdmitMachOHiddenDefinitions`); a sibling object
// references it by a plain undefined symbol (Mach-O has no undefined-symbol
// visibility). Every non-`Internal` function keeps its rustc name, linkage and
// visibility, so an exported item's identity is unchanged: the downstream
// binary below links the rlib by those names.
//
// THE GATE. Each fixture is built by LLVM and by the bridge from the same
// flags, run, and compared on exit status and stdout. The bridge must COMPILE,
// LINK and MATCH at every opt level (-O0..-O3) and every codegen-unit count in
// `CGUS` — for an executable, for an rlib with a downstream binary (both
// multi-CGU), and for a staticlib linked into a C driver. A refusal fails: the
// fixtures are chosen so every row compiles on this backend. One more test
// reads the objects back: no name is defined globally by two objects, every
// private copy is a private extern (never exported) whose name ends in the
// rustc symbol it stands for, and the copies come from at least two CGUs (so
// the fixture still exercises the collision).
//
// PROOFS-OFF DIAGNOSTIC: every bridge compile passes `no-proof-certs`; this
// pins link identity and native semantics, never certified objects.
//
// FALSIFIED: see `MUTATION RESULTS` at the bottom of this file.

use std::collections::{BTreeMap, BTreeSet};
use std::ffi::OsString;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

const OPT_LEVELS: [&str; 4] = ["0", "1", "2", "3"];
const CGUS: [&str; 3] = ["2", "4", "16"];
/// The CGU count of the LLVM oracle builds (its output does not depend on it).
const ORACLE_CGUS: &str = "16";

const INLINE_CORE: (&str, &str) = (
    "multi_cgu_inline_core",
    include_str!("bridge_corpus/multi_cgu_inline_core.rs"),
);
const PROGRAM: (&str, &str) = (
    "multi_cgu_program",
    include_str!("bridge_corpus/multi_cgu_program.rs"),
);
const RLIB: &str = include_str!("bridge_corpus/multi_cgu_rlib.rs");
const RLIB_BIN: &str = include_str!("bridge_corpus/multi_cgu_rlib_bin.rs");
const RLIB_CRATE: &str = "multi_cgu_rlib";

const STATICLIB: &str = "\
mod a { #[inline(never)] pub fn f(x: u64, y: u64) -> u64 { (PartialOrd::le(&x, &y) as u64) * 10 + PartialOrd::lt(&y, &x) as u64 } }
mod b { #[inline(never)] pub fn g(x: u64, y: u64) -> u64 { (PartialOrd::le(&y, &x) as u64) * 100 + Ord::max(x, y) } }
mod c { #[inline(never)] pub fn h(x: i8) -> i64 { i64::from(x) * 3 } }
mod d { #[inline(never)] pub fn k(x: i8) -> i64 { i64::from(x) + 7 + Ord::min(x, 3) as i64 } }
#[no_mangle]
pub extern \"C\" fn tcg_multi_cgu_entry(x: u64, y: u64, z: i8) -> i64 {
    (a::f(x, y) + b::g(x, y)) as i64 * 1000 + c::h(z) + d::k(z)
}
";
const STATICLIB_DRIVER: &str = "\
#include <stdio.h>
extern long tcg_multi_cgu_entry(unsigned long x, unsigned long y, signed char z);
int main(void) {
    printf(\"%ld %ld\\n\", tcg_multi_cgu_entry(3, 9, -4), tcg_multi_cgu_entry(9, 3, 100));
    return 0;
}
";

#[derive(Debug, PartialEq, Eq)]
struct Ending {
    code: Option<i32>,
    signal: Option<i32>,
    stdout: String,
}

fn workdir(stem: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("tcg_multi_cgu_{stem}_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create workdir");
    dir
}

/// One compile, LLVM (`backend: None`) or bridge, from the shared constructor.
fn compile(backend: Option<&Path>, opt: &str, cgus: &str, args: &[OsString]) -> Output {
    let mut cmd = toolchain_support::rustc_command();
    cmd.arg(format!("-Copt-level={opt}"));
    cmd.arg(format!("-Ccodegen-units={cgus}"));
    if let Some(dylib) = backend {
        let mut backend_arg = OsString::from("-Zcodegen-backend=");
        backend_arg.push(dylib);
        cmd.arg(backend_arg);
        cmd.arg(toolchain_support::backend_knobs_arg(&["no-proof-certs"]));
    }
    cmd.args(args);
    cmd.output().expect("spawn the compiler")
}

fn args(items: &[&dyn AsRef<std::ffi::OsStr>]) -> Vec<OsString> {
    items.iter().map(|item| item.as_ref().to_owned()).collect()
}

/// What a failed compile or link says, led by the duplicate-symbol lines this
/// file exists to keep out.
fn failure(what: &str, output: &Output) -> String {
    let stderr = String::from_utf8_lossy(&output.stderr);
    let duplicates: Vec<&str> = stderr
        .lines()
        .filter(|line| line.contains("duplicate symbol"))
        .map(str::trim)
        .collect();
    if duplicates.is_empty() {
        format!("{what} failed ({}): <<<{stderr}>>>", output.status)
    } else {
        format!("{what} failed to LINK: {}", duplicates.join("; "))
    }
}

fn run(bin: &Path) -> Ending {
    use std::os::unix::process::ExitStatusExt;
    let out = Command::new(bin).output().expect("run the compiled binary");
    Ending {
        code: out.status.code(),
        signal: out.status.signal(),
        stdout: String::from_utf8_lossy(&out.stdout).into_owned(),
    }
}

/// Build `src` as an executable and run it.
fn build_bin(
    dir: &Path,
    name: &str,
    src: &str,
    backend: Option<&Path>,
    opt: &str,
    cgus: &str,
) -> Result<Ending, String> {
    let src_path = dir.join(format!("{name}.rs"));
    std::fs::write(&src_path, src).expect("write source");
    let bin = dir.join(format!(
        "{name}_{}_O{opt}_c{cgus}",
        if backend.is_some() { "cg" } else { "llvm" }
    ));
    let output = compile(
        backend,
        opt,
        cgus,
        &args(&[&"--crate-type", &"bin", &"-o", &bin, &src_path]),
    );
    if !output.status.success() {
        return Err(failure("the executable", &output));
    }
    Ok(run(&bin))
}

/// Build the rlib, then the downstream binary against it, both with `cgus`
/// codegen units and the same backend, and run the binary.
fn build_rlib_pair(
    dir: &Path,
    backend: Option<&Path>,
    opt: &str,
    cgus: &str,
) -> Result<Ending, String> {
    let out = dir.join(format!(
        "pair_{}_O{opt}_c{cgus}",
        if backend.is_some() { "cg" } else { "llvm" }
    ));
    std::fs::create_dir_all(&out).expect("create pair dir");
    let lib_src = out.join("lib.rs");
    let bin_src = out.join("bin.rs");
    std::fs::write(&lib_src, RLIB).expect("write rlib source");
    std::fs::write(&bin_src, RLIB_BIN).expect("write bin source");
    let lib = compile(
        backend,
        opt,
        cgus,
        &args(&[
            &"--crate-type",
            &"rlib",
            &"--crate-name",
            &RLIB_CRATE,
            &"--out-dir",
            &out,
            &lib_src,
        ]),
    );
    if !lib.status.success() {
        return Err(failure("the rlib", &lib));
    }
    let rlib = out.join(format!("lib{RLIB_CRATE}.rlib"));
    let mut extern_arg = OsString::from(format!("{RLIB_CRATE}="));
    extern_arg.push(&rlib);
    let mut search = OsString::from("dependency=");
    search.push(&out);
    let bin = out.join("bin");
    let output = compile(
        backend,
        opt,
        cgus,
        &args(&[
            &"--crate-type",
            &"bin",
            &"--extern",
            &extern_arg,
            &"-L",
            &search,
            &"-o",
            &bin,
            &bin_src,
        ]),
    );
    if !output.status.success() {
        return Err(failure("the downstream binary", &output));
    }
    Ok(run(&bin))
}

/// Build the staticlib, link it into the C driver with the host `cc`, and run.
fn build_staticlib(
    dir: &Path,
    backend: Option<&Path>,
    opt: &str,
    cgus: &str,
) -> Result<Ending, String> {
    let out = dir.join(format!(
        "slib_{}_O{opt}_c{cgus}",
        if backend.is_some() { "cg" } else { "llvm" }
    ));
    std::fs::create_dir_all(&out).expect("create staticlib dir");
    let src = out.join("slib.rs");
    std::fs::write(&src, STATICLIB).expect("write staticlib source");
    let driver = out.join("driver.c");
    std::fs::write(&driver, STATICLIB_DRIVER).expect("write driver");
    let output = compile(
        backend,
        opt,
        cgus,
        &args(&[
            &"--crate-type",
            &"staticlib",
            &"--crate-name",
            &"multi_cgu_slib",
            &"--out-dir",
            &out,
            &src,
        ]),
    );
    if !output.status.success() {
        return Err(failure("the staticlib", &output));
    }
    let bin = out.join("prog");
    let link = Command::new("cc")
        .arg("-o")
        .arg(&bin)
        .arg(&driver)
        .arg(out.join("libmulti_cgu_slib.a"))
        .output()
        .expect("spawn cc");
    if !link.status.success() {
        return Err(failure("the C driver link", &link));
    }
    Ok(run(&bin))
}

/// Compare the bridge with LLVM over `OPT_LEVELS` x `CGUS`; returns the
/// number of rows and fails with every diverging row.
fn differential(
    label: &str,
    build: &mut dyn FnMut(Option<&Path>, &str, &str) -> Result<Ending, String>,
    dylib: &Path,
) -> usize {
    let mut rows = 0;
    let mut failures = Vec::new();
    for opt in OPT_LEVELS {
        let oracle = build(None, opt, ORACLE_CGUS)
            .unwrap_or_else(|error| panic!("{label} -O{opt}: the LLVM oracle: {error}"));
        assert_eq!(
            (oracle.code, oracle.signal),
            (Some(0), None),
            "{label} -O{opt}: the LLVM oracle did not exit cleanly: {oracle:?}"
        );
        assert!(
            !oracle.stdout.trim().is_empty(),
            "{label} -O{opt}: the LLVM oracle printed nothing"
        );
        for cgus in CGUS {
            rows += 1;
            match build(Some(dylib), opt, cgus) {
                Ok(bridge) if bridge == oracle => {
                    eprintln!("{label} -O{opt} -Ccodegen-units={cgus}: MATCH");
                }
                Ok(bridge) => failures.push(format!(
                    "{label} -O{opt} -Ccodegen-units={cgus}: DIVERGES — LLVM {oracle:?}, \
                     trust-cg {bridge:?}"
                )),
                Err(error) => {
                    failures.push(format!("{label} -O{opt} -Ccodegen-units={cgus}: {error}"))
                }
            }
        }
    }
    assert!(
        failures.is_empty(),
        "{} of {rows} multi-CGU {label} row(s) failed:\n  {}",
        failures.len(),
        failures.join("\n  ")
    );
    rows
}

#[test]
fn multi_cgu_executables_link_and_match_llvm_aarch64() {
    const TEST: &str = "multi_cgu_executables_link_and_match_llvm_aarch64";
    darwin_native::require(TEST, &[]);
    let dylib = backend_artifact_support::current_test_backend();
    let mut rows = 0;
    for (name, src) in [INLINE_CORE, PROGRAM] {
        let dir = workdir(name);
        rows += differential(
            name,
            &mut |backend, opt, cgus| build_bin(&dir, name, src, backend, opt, cgus),
            &dylib,
        );
        let _ = std::fs::remove_dir_all(&dir);
    }
    assert_eq!(rows, 24, "the executable row denominator changed");
    eprintln!("MULTI_CGU_EXECUTABLES rows=24 matched=24");
    positive_evidence::record(
        positive_evidence::Evidence::NativeRun,
        positive_evidence::Certs::Off,
    );
}

#[test]
fn multi_cgu_rlib_and_downstream_bin_link_and_match_llvm_aarch64() {
    const TEST: &str = "multi_cgu_rlib_and_downstream_bin_link_and_match_llvm_aarch64";
    darwin_native::require(TEST, &[]);
    let dylib = backend_artifact_support::current_test_backend();
    let dir = workdir("rlib_pair");
    let rows = differential(
        "rlib+bin",
        &mut |backend, opt, cgus| build_rlib_pair(&dir, backend, opt, cgus),
        &dylib,
    );
    let _ = std::fs::remove_dir_all(&dir);
    assert_eq!(rows, 12, "the rlib-pair row denominator changed");
    eprintln!("MULTI_CGU_RLIB_PAIR rows=12 matched=12");
    positive_evidence::record(
        positive_evidence::Evidence::NativeRun,
        positive_evidence::Certs::Off,
    );
}

#[test]
fn multi_cgu_staticlib_links_into_a_c_driver_and_matches_llvm_aarch64() {
    const TEST: &str = "multi_cgu_staticlib_links_into_a_c_driver_and_matches_llvm_aarch64";
    darwin_native::require(TEST, &["cc"]);
    let dylib = backend_artifact_support::current_test_backend();
    let dir = workdir("staticlib");
    let rows = differential(
        "staticlib",
        &mut |backend, opt, cgus| build_staticlib(&dir, backend, opt, cgus),
        &dylib,
    );
    let _ = std::fs::remove_dir_all(&dir);
    assert_eq!(rows, 12, "the staticlib row denominator changed");
    eprintln!("MULTI_CGU_STATICLIB rows=12 matched=12");
    positive_evidence::record(
        positive_evidence::Evidence::NativeRun,
        positive_evidence::Certs::Off,
    );
}

/// `(binding, name)` of every DEFINED symbol `nm -m` lists, where binding is
/// `"private external"`, `"external"` or `"non-external"`.
fn defined_symbols(path: &Path) -> Vec<(&'static str, String)> {
    let listing = Command::new("nm")
        .arg("-m")
        .arg(path)
        .output()
        .expect("nm -m");
    assert!(listing.status.success(), "nm -m {path:?} failed");
    String::from_utf8_lossy(&listing.stdout)
        .lines()
        .filter(|line| !line.contains("(undefined)"))
        .filter_map(|line| {
            let name = line.split_whitespace().last()?.to_owned();
            let binding = if line.contains(" non-external") {
                "non-external"
            } else if line.contains(" private external ") {
                "private external"
            } else if line.contains(" external ") {
                "external"
            } else {
                return None;
            };
            Some((binding, name))
        })
        .collect()
}

/// Split `<cgu>.<index>.<rustc symbol>` (a private name without its
/// `___trust_cg_private.` prefix) into the CGU and the rustc symbol.
fn split_private_name(rest: &str) -> Option<(&str, &str)> {
    let marker = rest.find("-cgu.")? + "-cgu.".len();
    let cgu_end = marker
        + rest[marker..]
            .bytes()
            .take_while(u8::is_ascii_digit)
            .count();
    let index = rest[cgu_end..].strip_prefix('.')?;
    let digits = index.bytes().take_while(u8::is_ascii_digit).count();
    let symbol = index[digits..].strip_prefix('.')?;
    (cgu_end > marker && digits > 0).then_some((&rest[..cgu_end], symbol))
}

#[test]
fn multi_cgu_private_copies_are_cgu_qualified_private_externs_aarch64() {
    const TEST: &str = "multi_cgu_private_copies_are_cgu_qualified_private_externs_aarch64";
    darwin_native::require(TEST, &["nm"]);
    let dylib = backend_artifact_support::current_test_backend();
    let (name, src) = INLINE_CORE;
    let dir = workdir("objects");
    let oracle = build_bin(&dir, name, src, None, "0", "4").expect("the LLVM oracle");
    let src_path = dir.join(format!("{name}.rs"));
    let out = dir.join("cg");
    std::fs::create_dir_all(&out).expect("create object dir");
    let bin = out.join(name);
    let output = compile(
        Some(&dylib),
        "0",
        "4",
        &args(&[
            &"--crate-type",
            &"bin",
            &"-Csave-temps",
            &"-o",
            &bin,
            &src_path,
        ]),
    );
    assert!(
        output.status.success(),
        "{}",
        failure("the executable", &output)
    );
    assert_eq!(
        run(&bin),
        oracle,
        "the -O0 -Ccodegen-units=4 build diverges from LLVM"
    );

    // Every object the bridge emitted for the crate (`-Csave-temps` keeps them).
    let objects: Vec<PathBuf> = std::fs::read_dir(&out)
        .expect("read object dir")
        .filter_map(|entry| entry.ok().map(|entry| entry.path()))
        .filter(|path| path.extension().is_some_and(|ext| ext == "o"))
        .collect();
    assert!(
        objects.len() >= 4,
        "expected a split crate, got {objects:?}"
    );
    let mut definers: BTreeMap<String, Vec<String>> = BTreeMap::new();
    let mut private_cgus = BTreeSet::new();
    let mut private = 0;
    for object in &objects {
        let file = object.file_name().unwrap().to_string_lossy().into_owned();
        for (binding, symbol) in defined_symbols(object) {
            if binding == "non-external" {
                continue;
            }
            if let Some(rest) = symbol.strip_prefix("___trust_cg_private.") {
                assert_eq!(
                    binding, "private external",
                    "{file}: CGU-private `{symbol}` must be a private extern (N_PEXT), never exported"
                );
                // `<cgu>.<index>.<rustc symbol>`: the CGU (`<crate>.<hash>-cgu.<n>`)
                // makes it unique, the rustc symbol keeps it readable.
                let (cgu, rustc_symbol) = split_private_name(rest).unwrap_or_else(|| {
                    panic!("{file}: `{symbol}` is not `<cgu>.<index>.<rustc symbol>`")
                });
                assert!(
                    rustc_symbol.starts_with("_R") || rustc_symbol.starts_with("_ZN"),
                    "{file}: `{symbol}` does not end in the rustc symbol it stands for"
                );
                private_cgus.insert(cgu.to_owned());
                private += 1;
            }
            definers.entry(symbol).or_default().push(file.clone());
        }
    }
    let duplicated: Vec<String> = definers
        .iter()
        .filter(|(_, files)| files.len() > 1)
        .map(|(symbol, files)| format!("{symbol} in {files:?}"))
        .collect();
    assert!(
        duplicated.is_empty(),
        "global symbols defined by more than one object (a duplicate-symbol link): {duplicated:#?}"
    );
    // The fixture must still give two CGUs their own copy, or this test would
    // pass without exercising the collision.
    assert!(
        private_cgus.len() >= 2,
        "expected CGU-private copies from at least two CGUs, found {private} in {private_cgus:?}"
    );
    // The final link demotes every private extern to a local symbol.
    let exported: Vec<String> = defined_symbols(&bin)
        .into_iter()
        .filter(|(binding, symbol)| {
            symbol.starts_with("___trust_cg_private.") && *binding != "non-external"
        })
        .map(|(binding, symbol)| format!("{binding} {symbol}"))
        .collect();
    assert!(
        exported.is_empty(),
        "the linked executable exports CGU-private symbols: {exported:?}"
    );
    let _ = std::fs::remove_dir_all(&dir);
    eprintln!(
        "private copies: {private} from {} CGUs: {private_cgus:?}",
        private_cgus.len()
    );
    eprintln!("MULTI_CGU_PRIVATE_EXTERNS cgus>=2 duplicated=0 exported=0");
    positive_evidence::record(
        positive_evidence::Evidence::NativeRun,
        positive_evidence::Certs::Off,
    );
}

// MUTATION RESULTS (2026-10-01, aarch64-apple-darwin, backend built by
// `targo --unverified test --release` with the atpkg Trust pack 9192):
//
//   * fixed tree: 4/4 tests pass (24 + 12 + 12 rows match LLVM; the -O0
//     4-CGU build carries 9 private copies from 3 CGUs, all private externs).
//   * `cgu_private_symbol_format` (src/lib.rs) answering `None` for Apple
//     targets again, i.e. the pre-fix spelling: 0/4. Every test fails with
//     `ld: N duplicate symbols` naming `<u64 as PartialOrd>::le`/`lt` and
//     `<i64 as From<i8>>::from`: `multi_cgu_inline_core` at -O0/-O1 for every
//     CGU count (6 of 12 rows), the staticlib at -O0/-O1 (6 of 12), the rlib
//     pair at every opt level with 4 and 16 CGUs (8 of 12, also
//     `Ord::max`/`Ord::min` and the library's `#[inline]` `spread`, i.e.
//     copies colliding ACROSS the two crates), and the object test's own link.
//   * the Mach-O private definition emitted with DEFAULT visibility instead of
//     hidden (`PrivateSymbolFormat::MachO` in src/function_linkage.rs): the
//     three link differentials still pass (unique names link) and the object
//     test fails: `___trust_cg_private.<cgu>.5._RNC...` "must be a private
//     extern (N_PEXT), never exported", left: "external". Only that test pins
//     the symbol's visibility, which no link or run can observe.
//   * the Mach-O private name without its rustc-symbol suffix (the ELF
//     spelling `__trust_cg_private.<cgu>.<index>`): the link differentials
//     pass and the object test fails on the name. That spelling also fails
//     `opt_loop_state_run`'s aarch64 controls, which find their kernels in
//     the linked image by rustc's symbol ("no symbol for count_only::<1024>",
//     8 rows at O2/O3).
