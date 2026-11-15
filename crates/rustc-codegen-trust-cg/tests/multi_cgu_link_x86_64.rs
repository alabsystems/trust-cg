// Compiled only on a macOS host: the objects this file links and reads back
// are x86_64-apple-darwin Mach-O, linked by the host's `cc` (ld64), which
// links an x86-64 image on Apple silicon too. Another host builds this target
// with no test in it, never one that passes without running.
#![cfg(target_os = "macos")]

#[path = "support/backend_artifact.rs"]
mod backend_artifact_support;
#[path = "support/toolchain.rs"]
mod toolchain_support;
#[path = "support/x86_rosetta.rs"]
mod x86_rosetta_support;

// E2E (x86_64-apple-darwin): a crate built with several codegen units links,
// and every CGU-private copy is a private extern.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// WHY THIS FILE EXISTS. The x86-64 twin of `multi_cgu_link_aarch64.rs`.
// rustc instantiates an `#[inline]` item (`<u64 as PartialOrd>::le`,
// `<i64 as From<i8>>::from`, `Ord::max::<u64>`) as a `LocalCopy`: one
// `Internal` copy in EVERY CGU that uses it, all under one mangled name. The
// x86-64 Mach-O object writer bound every function definition global, so on
// x86_64-apple-darwin each CGU's copy was a global definition of that one name
// and a crate built with several codegen units failed to link: `ld: 3
// duplicate symbols` (`<u64 as PartialOrd>::le`/`lt`, `<i64 as From<i8>>::from`)
// for `bridge_corpus/multi_cgu_inline_core.rs` at -Ccodegen-units=4, -O0 and
// -O1 (measured 2026-10-01 at trust-cg 684c20020, link only).
//
// THE FIX. Apple x86-64 now uses the bridge's CGU-private namespace exactly as
// Apple AArch64 does (`src/function_linkage.rs`, `PrivateSymbolFormat::MachO`):
// an `Internal` function is emitted as
// `__trust_cg_private.<cgu>.<index>.<rustc symbol>`, a hidden `External`
// definition that the x86-64 Mach-O module emitter now writes as a private
// extern (`N_EXT | N_PEXT`, trust-cg-codegen `X86FunctionSymbolFacts`,
// admitted by trust-cg-lower `ObjectSymbolPolicy::X86_64_MACHO_MODULE`). The
// objects of its own CGU call it by name and the final link demotes it to a
// local. Every non-`Internal` function keeps its rustc name, linkage and
// visibility; nothing is weak or coalesced.
//
// THE GATE. Two routes, so that the link and the object read-back run on every
// macOS host:
//   * `#![no_std]` (every macOS host): a program over the same `core` items,
//     against an x86-64 `core` + `compiler_builtins` built from the compiler's
//     own library source (`support/x86_rosetta.rs`, `x86_link_core`), is
//     built by the bridge at -O0..-O3 x -Ccodegen-units 2/4/16 and LINKED;
//     every row's objects and image are read back.
//   * `std` (a host whose Trust sysroot ships x86_64-apple-darwin `rust-std`):
//     the aarch64 twin's fixtures — the repro and a multi-module program as
//     executables, an rlib with a multi-CGU downstream binary, and a
//     staticlib linked into a C driver — at the same rows, plus the read-back
//     of the executables. Without that `rust-std` this route SKIPS and says
//     so (the installed Darwin Trust package ships the host's only).
// The read-back: no name is defined globally by two objects of the link,
// every private copy is a private extern whose name ends in the rustc symbol
// it stands for, copies come from at least two CGUs at -O0 (so the fixture
// still exercises the collision), and the linked image exports none of them.
//
// EXECUTION. Only on an x86-64 host are the binaries RUN, against the LLVM
// oracle built from the same flags (exit status and stdout). On Apple silicon
// nothing here executes x86-64 code: these rows establish that the bridge's
// objects link and carry the intended symbol table, not what they compute.
//
// PROOFS-OFF DIAGNOSTIC: every bridge compile passes `no-proof-certs`.
//
// FALSIFIED: see `MUTATION RESULTS` at the bottom of this file.

use std::collections::{BTreeMap, BTreeSet};
use std::ffi::OsString;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

const TARGET: &str = x86_rosetta_support::X86_TARGET;
const OPT_LEVELS: [&str; 4] = ["0", "1", "2", "3"];
const CGUS: [&str; 3] = ["2", "4", "16"];
/// The CGU count of the LLVM oracle builds (its output does not depend on it).
const ORACLE_CGUS: &str = "16";
/// Whether this host executes the x86-64 binaries the rows link.
const RUNS_X86_64: bool = cfg!(target_arch = "x86_64");

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

/// The `#![no_std]` body (`x86_rosetta_support::no_std_caller` supplies the
/// prelude): the staticlib fixture's `#[inline]` `core` items, one module per
/// CGU, the result as the exit status.
const NO_STD_BODY: &str = "\
mod a { #[inline(never)] pub fn f(x: u64, y: u64) -> u64 { (PartialOrd::le(&x, &y) as u64) * 10 + PartialOrd::lt(&y, &x) as u64 } }
mod b { #[inline(never)] pub fn g(x: u64, y: u64) -> u64 { (PartialOrd::le(&y, &x) as u64) * 100 + Ord::max(x, y) } }
mod c { #[inline(never)] pub fn h(x: i8) -> i64 { i64::from(x) * 3 } }
mod d { #[inline(never)] pub fn k(x: i8) -> i64 { i64::from(x) + 7 + Ord::min(x, 3) as i64 } }
fn main() {
    let v = (a::f(black_box(3), black_box(9)) + b::g(black_box(3), black_box(9))) as i64 * 1000
        + c::h(black_box(-4)) + d::k(black_box(100));
    exit(v as u64)
}
";

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

/// What a row built: the linked artifact and the objects kept beside it.
struct Built {
    /// The linked executable.
    bin: PathBuf,
    /// The directory `-Csave-temps` kept this crate's objects in.
    objects: PathBuf,
}

fn workdir(stem: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("tcg_multi_cgu_x86_{stem}_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create workdir");
    dir
}

/// One compile for `TARGET`, LLVM (`backend: None`) or bridge, from the shared
/// constructor. `target_args` carries the target (and, for `#![no_std]`, the
/// `core` it links against).
fn compile(
    backend: Option<&Path>,
    opt: &str,
    cgus: &str,
    target_args: &[OsString],
    args: &[OsString],
) -> Output {
    let mut cmd = toolchain_support::rustc_command();
    cmd.env("MACOSX_DEPLOYMENT_TARGET", "13.0");
    cmd.arg(format!("-Copt-level={opt}"));
    cmd.arg(format!("-Ccodegen-units={cgus}"));
    cmd.args(target_args);
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

fn std_target_args() -> Vec<OsString> {
    args(&[&"--target", &TARGET])
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
    assert!(
        RUNS_X86_64,
        "x86-64 binaries are run only on an x86-64 host"
    );
    let out = Command::new(bin).output().expect("run the compiled binary");
    Ending {
        code: out.status.code(),
        signal: out.status.signal(),
        stdout: String::from_utf8_lossy(&out.stdout).into_owned(),
    }
}

/// Build `src` as an executable for `TARGET` into its own directory, keeping
/// the crate's objects (`-Csave-temps`).
fn build_bin(
    dir: &Path,
    name: &str,
    src: &str,
    target_args: &[OsString],
    backend: Option<&Path>,
    opt: &str,
    cgus: &str,
) -> Result<Built, String> {
    let out = dir.join(format!(
        "{name}_{}_O{opt}_c{cgus}",
        if backend.is_some() { "cg" } else { "llvm" }
    ));
    std::fs::create_dir_all(&out).expect("create row dir");
    let src_path = out.join(format!("{name}.rs"));
    std::fs::write(&src_path, src).expect("write source");
    let bin = out.join(name);
    let output = compile(
        backend,
        opt,
        cgus,
        target_args,
        &args(&[
            &"--crate-type",
            &"bin",
            &"-Csave-temps",
            &"-o",
            &bin,
            &src_path,
        ]),
    );
    if !output.status.success() {
        return Err(failure("the executable", &output));
    }
    Ok(Built { bin, objects: out })
}

/// Build the rlib, then the downstream binary against it, both with `cgus`
/// codegen units and the same backend.
fn build_rlib_pair(
    dir: &Path,
    backend: Option<&Path>,
    opt: &str,
    cgus: &str,
) -> Result<PathBuf, String> {
    let out = dir.join(format!(
        "pair_{}_O{opt}_c{cgus}",
        if backend.is_some() { "cg" } else { "llvm" }
    ));
    std::fs::create_dir_all(&out).expect("create pair dir");
    let lib_src = out.join("lib.rs");
    let bin_src = out.join("bin.rs");
    std::fs::write(&lib_src, RLIB).expect("write rlib source");
    std::fs::write(&bin_src, RLIB_BIN).expect("write bin source");
    let target = std_target_args();
    let lib = compile(
        backend,
        opt,
        cgus,
        &target,
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
        &target,
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
    Ok(bin)
}

/// Build the staticlib and link it into the C driver with the host `cc`
/// for x86-64.
fn build_staticlib(
    dir: &Path,
    backend: Option<&Path>,
    opt: &str,
    cgus: &str,
) -> Result<PathBuf, String> {
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
        &std_target_args(),
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
        .args(["-arch", "x86_64", "-mmacosx-version-min=13.0", "-o"])
        .arg(&bin)
        .arg(&driver)
        .arg(out.join("libmulti_cgu_slib.a"))
        .output()
        .expect("spawn cc");
    if !link.status.success() {
        return Err(failure("the C driver link", &link));
    }
    Ok(bin)
}

/// Build every `OPT_LEVELS` x `CGUS` row with the bridge; on an x86-64 host
/// also run each against the LLVM oracle, which must exit with `oracle_code`.
/// `inspect` sees every bridge row that linked. Returns the number of rows and
/// fails with every failing row.
fn rows<T>(
    label: &str,
    oracle_code: i32,
    build: &mut dyn FnMut(Option<&Path>, &str, &str) -> Result<T, String>,
    bin_of: &dyn Fn(&T) -> &Path,
    inspect: &mut dyn FnMut(&str, &str, &T) -> Result<(), String>,
    dylib: &Path,
) -> usize {
    let mut rows = 0;
    let mut failures = Vec::new();
    for opt in OPT_LEVELS {
        let oracle = RUNS_X86_64.then(|| {
            let built = build(None, opt, ORACLE_CGUS)
                .unwrap_or_else(|error| panic!("{label} -O{opt}: the LLVM oracle: {error}"));
            let ending = run(bin_of(&built));
            assert_eq!(
                (ending.code, ending.signal),
                (Some(oracle_code), None),
                "{label} -O{opt}: the LLVM oracle did not exit as expected: {ending:?}"
            );
            ending
        });
        for cgus in CGUS {
            rows += 1;
            let row = format!("{label} -O{opt} -Ccodegen-units={cgus}");
            let built = match build(Some(dylib), opt, cgus) {
                Ok(built) => built,
                Err(error) => {
                    failures.push(format!("{row}: {error}"));
                    continue;
                }
            };
            if let Err(error) = inspect(opt, cgus, &built) {
                failures.push(format!("{row}: {error}"));
                continue;
            }
            match &oracle {
                Some(oracle) => {
                    let bridge = run(bin_of(&built));
                    if bridge == *oracle {
                        eprintln!("{row}: LINKED, MATCH");
                    } else {
                        failures.push(format!(
                            "{row}: DIVERGES — LLVM {oracle:?}, trust-cg {bridge:?}"
                        ));
                    }
                }
                None => eprintln!("{row}: LINKED (not run: no x86-64 execution on this host)"),
            }
        }
    }
    assert!(
        failures.is_empty(),
        "{} of {rows} multi-CGU x86-64 {label} row(s) failed:\n  {}",
        failures.len(),
        failures.join("\n  ")
    );
    rows
}

/// `(binding, name)` of every DEFINED symbol `nm -m` lists, where binding is
/// `"private external"`, `"external"` or `"non-external"`.
fn defined_symbols(path: &Path) -> Result<Vec<(&'static str, String)>, String> {
    let listing = Command::new("nm")
        .arg("-m")
        .arg(path)
        .output()
        .expect("nm -m");
    if !listing.status.success() {
        return Err(format!(
            "nm -m {path:?} failed: {}",
            String::from_utf8_lossy(&listing.stderr)
        ));
    }
    Ok(String::from_utf8_lossy(&listing.stdout)
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
        .collect())
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

/// What the read-back of one bridge row found.
#[derive(Debug, Default)]
struct ReadBack {
    private: usize,
    private_cgus: BTreeSet<String>,
}

/// Read back one bridge row: the crate's objects (`built.objects`) and the
/// linked image. No name may be defined globally by two objects, every
/// CGU-private copy must be a private extern (`N_EXT | N_PEXT`) named
/// `<cgu>.<index>.<rustc symbol>`, and the image may export none of them.
fn read_back(built: &Built) -> Result<ReadBack, String> {
    let objects: Vec<PathBuf> = std::fs::read_dir(&built.objects)
        .expect("read object dir")
        .filter_map(|entry| entry.ok().map(|entry| entry.path()))
        .filter(|path| path.extension().is_some_and(|ext| ext == "o"))
        .collect();
    if objects.len() < 2 {
        return Err(format!("expected a split crate, got objects {objects:?}"));
    }
    let mut definers: BTreeMap<String, Vec<String>> = BTreeMap::new();
    let mut found = ReadBack::default();
    for object in &objects {
        let file = object.file_name().unwrap().to_string_lossy().into_owned();
        for (binding, symbol) in defined_symbols(object)? {
            if binding == "non-external" {
                continue;
            }
            if let Some(rest) = symbol.strip_prefix("___trust_cg_private.") {
                if binding != "private external" {
                    return Err(format!(
                        "{file}: CGU-private `{symbol}` is {binding}; it must be a private extern \
                         (N_PEXT), never exported"
                    ));
                }
                let Some((cgu, rustc_symbol)) = split_private_name(rest) else {
                    return Err(format!(
                        "{file}: `{symbol}` is not `<cgu>.<index>.<rustc symbol>`"
                    ));
                };
                if !(rustc_symbol.starts_with("_R") || rustc_symbol.starts_with("_ZN")) {
                    return Err(format!(
                        "{file}: `{symbol}` does not end in the rustc symbol it stands for"
                    ));
                }
                found.private_cgus.insert(cgu.to_owned());
                found.private += 1;
            }
            definers.entry(symbol).or_default().push(file.clone());
        }
    }
    let duplicated: Vec<String> = definers
        .iter()
        .filter(|(_, files)| files.len() > 1)
        .map(|(symbol, files)| format!("{symbol} in {files:?}"))
        .collect();
    if !duplicated.is_empty() {
        return Err(format!(
            "global symbols defined by more than one object (a duplicate-symbol link): \
             {duplicated:?}"
        ));
    }
    // The final link demotes every private extern to a local symbol.
    let exported: Vec<String> = defined_symbols(&built.bin)?
        .into_iter()
        .filter(|(binding, symbol)| {
            symbol.starts_with("___trust_cg_private.") && *binding != "non-external"
        })
        .map(|(binding, symbol)| format!("{binding} {symbol}"))
        .collect();
    if !exported.is_empty() {
        return Err(format!(
            "the linked image exports CGU-private symbols: {exported:?}"
        ));
    }
    Ok(found)
}

/// Read back a row and, at -O0 (where nothing inlines the copies away),
/// require copies from at least two CGUs, so the fixture still exercises the
/// collision. Returns the number of private copies read.
fn read_back_row(opt: &str, built: &Built) -> Result<usize, String> {
    let found = read_back(built)?;
    if opt == "0" && found.private_cgus.len() < 2 {
        return Err(format!(
            "expected CGU-private copies from at least two CGUs at -O0, found {} in {:?}",
            found.private, found.private_cgus
        ));
    }
    Ok(found.private)
}

#[test]
fn multi_cgu_no_std_x86_64_links_with_cgu_private_externs() {
    assert!(
        toolchain_support::backend_knobs_supported(),
        "the build compiler lists no `{}` in `-Z help`, so `no-proof-certs` cannot be passed",
        toolchain_support::BACKEND_KNOBS_OPTION
    );
    let dylib = backend_artifact_support::current_test_backend();
    let name = "multi_cgu_no_std";
    let src = x86_rosetta_support::no_std_caller(NO_STD_BODY);
    let dir = workdir(name);
    let mut private = 0;
    // (3 <= 9) * 10 + 9 = 19, 19 * 1000 - 12 + 110 = 19098, 19098 % 251 = 22.
    let rows = rows(
        name,
        22,
        &mut |backend, opt, cgus| {
            let core = x86_rosetta_support::x86_link_core(opt);
            // The `core` was built `-Cpanic=abort`, and a `#![no_std]`
            // binary cannot unwind.
            let mut target_args = x86_rosetta_support::no_std_compile_args(&core);
            target_args.push("-Cpanic=abort".into());
            build_bin(&dir, name, &src, &target_args, backend, opt, cgus)
        },
        &|built: &Built| built.bin.as_path(),
        &mut |opt, _, built| {
            private += read_back_row(opt, built)?;
            Ok(())
        },
        &dylib,
    );
    let _ = std::fs::remove_dir_all(&dir);
    assert_eq!(rows, 12, "the no_std row denominator changed");
    assert!(private > 0, "no row carried a CGU-private copy");
    eprintln!(
        "MULTI_CGU_X86_64_NO_STD rows=12 linked=12 private_copies={private} ran={RUNS_X86_64}"
    );
}

/// Whether this host's Trust sysroot ships `rust-std` for `TARGET`; prints why
/// the caller skips when it does not.
fn x86_64_std_or_skip(test: &str) -> bool {
    if toolchain_support::target_std_available(TARGET) {
        return true;
    }
    eprintln!(
        "{test}: SKIPPED — the build compiler's sysroot ships no rust-std for {TARGET}, so the \
         std fixtures cannot be linked here; `multi_cgu_no_std_x86_64_links_with_cgu_private_externs` \
         still links and reads back the x86-64 objects against a `core` built from source"
    );
    false
}

#[test]
fn multi_cgu_std_x86_64_executables_link_with_cgu_private_externs() {
    const TEST: &str = "multi_cgu_std_x86_64_executables_link_with_cgu_private_externs";
    if !x86_64_std_or_skip(TEST) {
        return;
    }
    let dylib = backend_artifact_support::current_test_backend();
    let mut total = 0;
    let mut private = 0;
    for (name, src) in [INLINE_CORE, PROGRAM] {
        let dir = workdir(name);
        total += rows(
            name,
            0,
            &mut |backend, opt, cgus| {
                build_bin(&dir, name, src, &std_target_args(), backend, opt, cgus)
            },
            &|built: &Built| built.bin.as_path(),
            &mut |opt, _, built| {
                private += read_back_row(opt, built)?;
                Ok(())
            },
            &dylib,
        );
        let _ = std::fs::remove_dir_all(&dir);
    }
    assert_eq!(total, 24, "the executable row denominator changed");
    assert!(private > 0, "no row carried a CGU-private copy");
    eprintln!(
        "MULTI_CGU_X86_64_EXECUTABLES rows=24 linked=24 private_copies={private} ran={RUNS_X86_64}"
    );
}

#[test]
fn multi_cgu_std_x86_64_rlib_pair_and_staticlib_link() {
    const TEST: &str = "multi_cgu_std_x86_64_rlib_pair_and_staticlib_link";
    if !x86_64_std_or_skip(TEST) {
        return;
    }
    let dylib = backend_artifact_support::current_test_backend();
    let dir = workdir("rlib_pair");
    let pair = rows(
        "rlib+bin",
        0,
        &mut |backend, opt, cgus| build_rlib_pair(&dir, backend, opt, cgus),
        &|bin: &PathBuf| bin.as_path(),
        &mut |_, _, _| Ok(()),
        &dylib,
    );
    let _ = std::fs::remove_dir_all(&dir);
    let dir = workdir("staticlib");
    let staticlib = rows(
        "staticlib",
        0,
        &mut |backend, opt, cgus| build_staticlib(&dir, backend, opt, cgus),
        &|bin: &PathBuf| bin.as_path(),
        &mut |_, _, _| Ok(()),
        &dylib,
    );
    let _ = std::fs::remove_dir_all(&dir);
    assert_eq!((pair, staticlib), (12, 12), "the row denominators changed");
    eprintln!("MULTI_CGU_X86_64_RLIB_PAIR_STATICLIB rows=24 linked=24 ran={RUNS_X86_64}");
}

// MUTATION RESULTS (2026-10-01, aarch64-apple-darwin host without Rosetta,
// backend built by `targo --unverified test --release` with the atpkg Trust
// pack 9192, whose sysroot ships no x86_64-apple-darwin `rust-std`: the two
// `std` tests SKIP there and only the `#![no_std]` test runs; nothing x86-64
// was executed):
//
//   * fixed tree: the `#![no_std]` test passes, 12/12 rows link, 80 private
//     copies read back as private externs, from >= 2 CGUs at -O0.
//   * `PrivateSymbolFormat::for_target` (src/function_linkage.rs) answering
//     `None` for Apple x86-64 again, i.e. the pre-fix spelling: 6 of 12 rows
//     fail to LINK (-O0 and -O1 at 2, 4 and 16 CGUs), `ld: N duplicate
//     symbols` naming `<u64 as PartialOrd>::le`/`lt` and
//     `<i64 as From<i8>>::from` (and `tests/function_linkage.rs`'s target
//     table fails).
//   * the x86-64 Mach-O emitter binding a hidden definition `N_EXT` instead of
//     `N_EXT | N_PEXT` (trust-cg-codegen `emit_module_macho`): every row still
//     links (the names are unique) and 12/12 fail the read-back:
//     "CGU-private `___trust_cg_private.<cgu>.<n>.<rustc symbol>` is external;
//     it must be a private extern (N_PEXT), never exported". Only the
//     read-back pins the visibility, which no link can observe.
//   * `Compiler::compile` keeping the default adapter policy for x86-64
//     Mach-O (`aot_object_symbol_policy`): 12/12 rows refuse to compile
//     ("function `__trust_cg_private.…` states trust-ir v45 `visibility` =
//     hidden, which this backend has no emitter for"), fail-closed.
//   The emitter and policy mutations also fail trust-cg-codegen's
//   `x86_macho_hidden_function_definition_is_a_private_extern` (unit),
//   `function_visibility_the_emitters_cannot_spell_is_refused_by_name`
//   (`tests/aarch64_elf_symbol_binding.rs`) and, for the policy,
//   `module_local_binding_exemption_is_aarch64_elf_and_macho_and_x86_64_elf`
//   (unit).
//
// The `std` rows were measured outside this harness with a stage1 `trustc`
// whose sysroot has the x86_64-apple-darwin `rust-std` (same fixtures, link
// and read-back only): see the commit that added this file.
