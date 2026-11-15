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

// E2E (aarch64-apple-darwin): rustc's symbol linkage carried faithfully onto
// Mach-O symbols by the bridge, through ld64 (ledger L06-P7).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// WHAT THIS PINS. Main's multi-CGU fix (cee8dc937) already renamed the
// `Internal` copies on Darwin, so two codegen units' copies of one inline
// function link; this change (L06-P7) carries the rest of rustc's linkage.
// Before it, on main, an `External` + hidden function was a default-visible
// `external`, a `#[linkage = "weak"]` function was a strong `external`, a weak
// or link-once static was refused, and `available_externally` had no
// handling of its own. Now (`function_linkage`):
//
// * `Internal` -> `__trust_cg_private.<cgu>.<n>.<rustc symbol>`, `N_EXT |
//   N_PEXT` (private external: linkable across the CGU's split objects, local
//   in the linked image), so per-CGU copies never collide (main's fix, kept);
// * `External` + hidden -> `N_EXT | N_PEXT`, as LLVM spells it;
// * `WeakAny` / `WeakODR` / `LinkOnce*` -> `N_WEAK_DEF`: copies coalesce, a
//   strong definition wins, and the bridge's own callers bind through a
//   relocation, so the winner is what they call;
// * `available_externally` -> no definition, as in LLVM; `common`, a weak
//   thread-local and `extern_weak` definitions -> refused as `[TCG-LINKAGE]`.
//
// The first test retains per-CGU inputs with `-Csave-temps`: the bridge's
// requested `cgu.o` is a combined published object, not a per-CGU input. It
// also links that published object separately against the same driver.
// The refusal control uses `extern_weak`, which current Trust accepts as an
// attribute but the bridge rejects as a definition. `common` is rejected by
// the current frontend before the bridge; the pure function_linkage tests
// still cover its definition policy.
//
// The first test is a differential against rustc's LLVM backend for its one
// crate: the bridge's objects bind every non-local symbol LLVM's objects
// define for it exactly as LLVM does (`external`, `private external`, `weak
// external`), and the linked programs agree. That crate has no link-once
// function, and there the two differ (an open row): LLVM binds a
// `linkonce_odr` function `weak external automatically hidden`, which the
// linked image demotes to a local, while the bridge binds it plain `weak
// external` and the image keeps exporting it. The second links weak
// functions, an immutable weak static and a mutable one (`static mut`, which
// the bridge's static path would otherwise make a strong export) from two
// crates and against strong C definitions. The third links a `cdylib` through
// rustc and ld64's export list and checks it exports only its `#[no_mangle]`
// interface: that is export-list evidence (the export list hides everything
// else whatever the objects bind), not evidence for the object bindings,
// which the first test checks.
//
// PROOFS-OFF DIAGNOSTIC. The bridge compiles that link pass the backend's
// `no-proof-certs` knob: with certificates on, these function bodies are
// refused at proof promotion (`[TCG-PROOF-465]`, the proof wall of ledger
// L07-P2), independently of linkage. The refusal test compiles with
// certificates on: `[TCG-LINKAGE]` is decided for each item before its
// object is compiled, so no proof work is involved.

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

use darwin_native::TARGET;

/// Two modules share an `#[inline]` helper, so at `-Copt-level=1` with four
/// codegen units rustc gives each user CGU its own `Internal` copy; `run_a`
/// and `run_b` are `External` + hidden; `weak_hook` is `WeakAny`.
const CGU_CRATE: &str = "\
#![feature(linkage)]
#![crate_type = \"staticlib\"]
mod a {
    #[inline]
    pub fn helper(x: u32) -> u32 { x.wrapping_mul(3).wrapping_add(1) }
    #[inline(never)]
    pub fn run_a(x: u32) -> u32 { helper(x).wrapping_add(1) }
}
mod b {
    #[inline(never)]
    pub fn run_b(x: u32) -> u32 { crate::a::helper(x) ^ 0x55 }
}
#[no_mangle]
#[linkage = \"weak\"]
pub extern \"C\" fn weak_hook(x: u32) -> u32 { x.wrapping_add(100) }
#[no_mangle]
pub extern \"C\" fn entry(x: u32) -> u32 {
    a::run_a(x).wrapping_add(b::run_b(x)).wrapping_add(weak_hook(x))
}
";
const CGU_DRIVER: &str = "\
#include <stdio.h>
unsigned entry(unsigned);
int main(void) { printf(\"%u %u\\n\", entry(5), entry(77)); return 0; }
";

/// A `no_std` library with a weak function, an immutable and a mutable weak
/// static, and exported callers that reach them. `{tag}` names the callers,
/// `{value}` the definitions' values. The mutable static is the case the
/// static path's own export policy (a mutable static is a strong export)
/// must not strengthen.
fn weak_crate(tag: &str, value: i32) -> String {
    format!(
        "#![feature(linkage)]
#![crate_type = \"lib\"]
#![no_std]
#[no_mangle]
#[linkage = \"weak\"]
pub extern \"C\" fn tcg_hook() -> i32 {{ {value} }}
#[no_mangle]
#[linkage = \"weak\"]
pub static TCG_WEAK_DATA: i32 = {data};
#[no_mangle]
#[linkage = \"weak\"]
pub static mut TCG_WEAK_MUT: i32 = {cell};
#[no_mangle]
pub extern \"C\" fn {tag}_calls_hook() -> i32 {{ tcg_hook() }}
#[no_mangle]
pub extern \"C\" fn {tag}_reads_data() -> i32 {{ TCG_WEAK_DATA }}
#[no_mangle]
pub extern \"C\" fn {tag}_bumps_cell() -> i32 {{
    unsafe {{ TCG_WEAK_MUT = TCG_WEAK_MUT.wrapping_add(1); TCG_WEAK_MUT }}
}}
",
        data = value * 10,
        cell = value * 100
    )
}
const WEAK_PAIR_DRIVER: &str = "\
#include <stdio.h>
int a_calls_hook(void); int b_calls_hook(void); int a_reads_data(void); int b_reads_data(void);
int a_bumps_cell(void); int b_bumps_cell(void);
int main(void) {
    int a = a_bumps_cell();
    int b = b_bumps_cell();
    printf(\"%d %d %d %d %d %d\\n\", a_calls_hook(), b_calls_hook(), a_reads_data(), b_reads_data(),
           a, b);
    return 0;
}
";
const STRONG_DRIVER: &str = "\
#include <stdio.h>
int a_calls_hook(void); int a_reads_data(void); int a_bumps_cell(void);
int tcg_hook(void) { return 3; }
const int TCG_WEAK_DATA = 30;
int TCG_WEAK_MUT = 300;
int main(void) {
    int bumped = a_bumps_cell();
    printf(\"%d %d %d %d\\n\", a_calls_hook(), a_reads_data(), bumped, TCG_WEAK_MUT);
    return 0;
}
";

const DYLIB_CRATE: &str = "\
#![crate_type = \"cdylib\"]
mod inner {
    #[inline(never)]
    pub fn scale(x: i32) -> i32 { x.wrapping_mul(3) }
}
#[no_mangle]
pub extern \"C\" fn tcg_dylib_scale(x: i32) -> i32 { inner::scale(x).wrapping_add(1) }
pub fn not_exported(x: i32) -> i32 { inner::scale(x) }
";
const DYLIB_DRIVER: &str = "\
#include <stdio.h>
int tcg_dylib_scale(int);
int main(void) { printf(\"%d\\n\", tcg_dylib_scale(14)); return 0; }
";

/// A scratch directory, removed when the test that made it succeeds.
struct Scratch(PathBuf);

impl Scratch {
    fn new(stem: &str) -> Self {
        let path =
            std::env::temp_dir().join(format!("tcg_linkage_macho_{stem}_{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&path);
        std::fs::create_dir_all(&path).expect("create scratch directory");
        Self(path)
    }

    fn sub(&self, name: &str) -> PathBuf {
        let path = self.0.join(name);
        std::fs::create_dir_all(&path).expect("create scratch subdirectory");
        path
    }
}

impl Drop for Scratch {
    fn drop(&mut self) {
        if !std::thread::panicking() {
            let _ = std::fs::remove_dir_all(&self.0);
        }
    }
}

fn text(output: &Output) -> String {
    format!(
        "{}{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    )
}

fn backend_arg() -> std::ffi::OsString {
    let mut arg = std::ffi::OsString::from("-Zcodegen-backend=");
    arg.push(backend_artifact_support::current_test_backend());
    arg
}

/// Compile `source` (written to `dir/<stem>.rs`) into `dir` with `options`,
/// through the bridge (proofs off) or, with `bridge` false, rustc's LLVM
/// backend. Returns the compile output.
fn compile(dir: &Path, stem: &str, source: &str, options: &[&str], bridge: bool) -> Output {
    let path = dir.join(format!("{stem}.rs"));
    std::fs::write(&path, source).expect("write crate source");
    let mut command = toolchain_support::rustc_command();
    command.current_dir(dir);
    if bridge {
        command
            .arg(backend_arg())
            .arg(toolchain_support::backend_knobs_arg(&["no-proof-certs"]));
    }
    command
        .args(["--target", TARGET, "-Cpanic=abort", "--out-dir"])
        .arg(dir)
        .args(options)
        .arg(&path)
        .output()
        .expect("spawn trustc")
}

fn compile_ok(dir: &Path, stem: &str, source: &str, options: &[&str], bridge: bool) {
    let output = compile(dir, stem, source, options, bridge);
    assert!(
        output.status.success(),
        "{} compile of {stem} with {options:?} failed:\n{}",
        if bridge { "bridge" } else { "LLVM" },
        text(&output)
    );
}

/// The crate's code objects in `dir` (rustc's `<crate>.<cgu>.rcgu.o` names;
/// the allocator shim, which a no-std C link cannot satisfy, is left out).
fn crate_objects(dir: &Path) -> Vec<PathBuf> {
    let mut objects: Vec<PathBuf> = std::fs::read_dir(dir)
        .expect("read object directory")
        .filter_map(|entry| entry.ok().map(|entry| entry.path()))
        .filter(|path| {
            path.extension().is_some_and(|ext| ext == "o")
                && !path
                    .file_name()
                    .is_some_and(|name| name.to_string_lossy().contains("allocator_shim"))
        })
        .collect();
    objects.sort();
    objects
}

/// Every symbol `object` DEFINES in a section, with `nm -m`'s binding words
/// (`external`, `private external`, `weak external`, `non-external`, ...).
fn defined_symbols(object: &Path) -> Vec<(String, String)> {
    let output = Command::new("nm")
        .arg("-m")
        .arg(object)
        .output()
        .expect("run nm -m");
    assert!(
        output.status.success(),
        "nm -m {object:?}:\n{}",
        text(&output)
    );
    String::from_utf8_lossy(&output.stdout)
        .lines()
        .filter_map(|line| {
            // `<address> (<segment>,<section>) <binding words> <name>`
            let after_section = line.split_once(") ")?.1;
            if line.contains("(undefined)") {
                return None;
            }
            let (binding, name) = after_section.rsplit_once(' ')?;
            Some((name.to_owned(), binding.to_owned()))
        })
        .collect()
}

fn link_and_run(dir: &Path, name: &str, driver: &str, objects: &[PathBuf]) -> String {
    let driver_path = dir.join(format!("{name}.c"));
    std::fs::write(&driver_path, driver).expect("write C driver");
    let exe = dir.join(name);
    let link = Command::new("cc")
        .arg("-o")
        .arg(&exe)
        .arg(&driver_path)
        .args(objects)
        .output()
        .expect("spawn cc");
    assert!(link.status.success(), "link {name}:\n{}", text(&link));
    let run = Command::new(&exe).output().expect("run linked program");
    assert!(run.status.success(), "run {name}:\n{}", text(&run));
    String::from_utf8_lossy(&run.stdout).trim().to_owned()
}

#[test]
fn cgu_local_copies_and_hidden_definitions_bind_as_llvm_binds_them() {
    darwin_native::require("linkage_macho_aarch64", &["cc", "nm"]);
    let scratch = Scratch::new("cgu");
    let options = [
        "--crate-type",
        "staticlib",
        "--emit=obj",
        "-Csave-temps",
        "-Copt-level=1",
        "-Ccodegen-units=4",
    ];
    let bridge_dir = scratch.sub("bridge");
    compile_ok(&bridge_dir, "cgu", CGU_CRATE, &options, true);
    let llvm_dir = scratch.sub("llvm");
    compile_ok(&llvm_dir, "cgu", CGU_CRATE, &options, false);
    // Inspect only saved CGU inputs. Including the bridge's combined `cgu.o`
    // would count each definition twice and link it alongside its own inputs.
    let saved_objects = |dir: &Path| {
        crate_objects(dir)
            .into_iter()
            .filter(|path| {
                path.file_name()
                    .is_some_and(|name| name.to_string_lossy().ends_with(".rcgu.o"))
            })
            .collect::<Vec<_>>()
    };
    let bridge_objects = saved_objects(&bridge_dir);
    let llvm_objects = saved_objects(&llvm_dir);
    assert!(
        bridge_objects.len() >= 2,
        "four codegen units must give several objects: {bridge_objects:?}"
    );

    // Every symbol each bridge object defines, by name.
    let mut bridge: BTreeMap<String, Vec<String>> = BTreeMap::new();
    for object in &bridge_objects {
        for (name, binding) in defined_symbols(object) {
            bridge.entry(name).or_default().push(binding);
        }
    }
    // No two objects define one symbol unless it is weak: the link below
    // would otherwise fail with "duplicate symbol" (as it did before main's
    // multi-CGU fix, cee8dc937).
    for (name, bindings) in &bridge {
        assert!(
            bindings.len() == 1 || bindings.iter().all(|binding| binding.contains("weak")),
            "`{name}` is defined {} times: {bindings:?}",
            bindings.len()
        );
    }
    // The CGU-local copies are private externals under distinct names, each
    // ending in its rustc symbol.
    let private: Vec<_> = bridge
        .iter()
        .filter(|(name, _)| name.starts_with("___trust_cg_private."))
        .collect();
    assert!(
        private.len() >= 2,
        "the per-CGU `Internal` copies must be renamed CGU-local symbols: {bridge:?}"
    );
    for (name, bindings) in &private {
        assert_eq!(*bindings, &vec!["private external".to_owned()], "{name}");
    }

    // Differential: every non-local symbol LLVM's objects define, the bridge's
    // objects define with the same binding.
    let mut compared = BTreeSet::new();
    for object in &llvm_objects {
        for (name, binding) in defined_symbols(object) {
            if binding == "non-external" {
                continue;
            }
            let ours = bridge
                .get(&name)
                .unwrap_or_else(|| panic!("the bridge does not define `{name}` ({binding})"));
            assert!(
                ours.iter().all(|our| *our == binding),
                "`{name}`: LLVM binds it {binding:?}, the bridge {ours:?}"
            );
            compared.insert(binding);
        }
    }
    for binding in ["external", "private external", "weak external"] {
        assert!(
            compared.contains(binding),
            "the differential compared no {binding:?} symbol: {compared:?}"
        );
    }

    // Both programs link (no duplicate symbol) and agree.
    let ours = link_and_run(&bridge_dir, "cgu_bridge", CGU_DRIVER, &bridge_objects);
    let theirs = link_and_run(&llvm_dir, "cgu_llvm", CGU_DRIVER, &llvm_objects);
    assert_eq!(ours, theirs, "bridge and LLVM programs disagree");
    assert_eq!(ours, "191 599", "entry(5), entry(77)");
    // The exact requested output must also be a usable object on its own.
    let published = bridge_dir.join("cgu.o");
    assert!(
        published.is_file(),
        "missing published object: {published:?}"
    );
    assert_eq!(
        link_and_run(&bridge_dir, "cgu_published", CGU_DRIVER, &[published]),
        theirs,
        "the published object must agree with the per-CGU inputs and LLVM"
    );
    positive_evidence::record(
        positive_evidence::Evidence::NativeRun,
        positive_evidence::Certs::Off,
    );
}

#[test]
fn weak_definitions_coalesce_across_crates_and_yield_to_a_strong_one() {
    darwin_native::require("linkage_macho_aarch64", &["cc", "nm"]);
    let scratch = Scratch::new("weak");
    // `-Copt-level=0`: from O1 rustc's MIR folds a read of an immutable static
    // to its initializer before any backend sees it (LLVM's objects do the
    // same), and this test observes which definition a read binds to.
    let options = ["--emit=obj", "-Copt-level=0"];
    let a_dir = scratch.sub("a");
    compile_ok(&a_dir, "weak_a", &weak_crate("a", 1), &options, true);
    let b_dir = scratch.sub("b");
    compile_ok(&b_dir, "weak_b", &weak_crate("b", 2), &options, true);
    let a_objects = crate_objects(&a_dir);
    let b_objects = crate_objects(&b_dir);
    for object in a_objects.iter().chain(&b_objects) {
        for (name, binding) in defined_symbols(object) {
            if ["_tcg_hook", "_TCG_WEAK_DATA", "_TCG_WEAK_MUT"].contains(&name.as_str()) {
                assert_eq!(binding, "weak external", "{object:?} `{name}`");
            }
        }
    }

    // Two weak definitions of each symbol: ld64 keeps one (the first in link
    // order), and both crates' callers reach it, the mutable one's writes
    // included (one cell: the second increment sees the first).
    let pair_dir = scratch.sub("pair");
    let ab: Vec<PathBuf> = a_objects.iter().chain(&b_objects).cloned().collect();
    assert_eq!(
        link_and_run(&pair_dir, "weak_ab", WEAK_PAIR_DRIVER, &ab),
        "1 1 10 10 101 102"
    );
    let ba: Vec<PathBuf> = b_objects.iter().chain(&a_objects).cloned().collect();
    assert_eq!(
        link_and_run(&pair_dir, "weak_ba", WEAK_PAIR_DRIVER, &ba),
        "2 2 20 20 201 202"
    );
    // A strong definition wins over the weak one, and the bridge's write
    // lands in the C definition.
    assert_eq!(
        link_and_run(&pair_dir, "weak_strong", STRONG_DRIVER, &a_objects),
        "3 30 301 301"
    );
    positive_evidence::record(
        positive_evidence::Evidence::NativeRun,
        positive_evidence::Certs::Off,
    );
}

#[test]
fn a_cdylib_exports_only_its_no_mangle_interface() {
    darwin_native::require("linkage_macho_aarch64", &["cc", "nm"]);
    let scratch = Scratch::new("cdylib");
    let dir = scratch.sub("dylib");
    // `-Csave-temps` keeps the bridge objects rustc linked.
    compile_ok(
        &dir,
        "dy",
        DYLIB_CRATE,
        &["-Copt-level=0", "-Csave-temps"],
        true,
    );
    let dylib = dir.join("libdy.dylib");
    let exports = Command::new("nm")
        .args(["-gU"])
        .arg(&dylib)
        .output()
        .expect("run nm -gU");
    assert!(exports.status.success(), "{}", text(&exports));
    let exported: Vec<String> = String::from_utf8_lossy(&exports.stdout)
        .lines()
        .filter_map(|line| line.split_whitespace().last().map(str::to_owned))
        .collect();
    assert_eq!(
        exported,
        ["_tcg_dylib_scale"],
        "the cdylib must export exactly its #[no_mangle] interface"
    );
    // The crate-internal function is hidden in the object rustc linked.
    let mut hidden = 0;
    for object in crate_objects(&dir) {
        for (name, binding) in defined_symbols(&object) {
            if name.starts_with("___trust_cg_private.") {
                assert_eq!(binding, "private external", "{object:?} `{name}`");
                hidden += 1;
            }
        }
    }
    assert!(hidden >= 1, "no CGU-local function in the kept objects");

    let driver = dir.join("drv.c");
    std::fs::write(&driver, DYLIB_DRIVER).expect("write driver");
    let exe = dir.join("drv");
    let link = Command::new("cc")
        .arg("-o")
        .arg(&exe)
        .arg(&driver)
        .arg(format!("-L{}", dir.display()))
        .arg("-ldy")
        .output()
        .expect("spawn cc");
    assert!(link.status.success(), "{}", text(&link));
    let run = Command::new(&exe)
        .env("DYLD_LIBRARY_PATH", &dir)
        .output()
        .expect("run dylib driver");
    assert!(run.status.success(), "{}", text(&run));
    assert_eq!(String::from_utf8_lossy(&run.stdout).trim(), "43");
    positive_evidence::record(
        positive_evidence::Evidence::NativeRun,
        positive_evidence::Certs::Off,
    );
}

#[test]
fn linkages_without_a_faithful_mach_o_spelling_are_refused_by_name() {
    darwin_native::require("linkage_macho_aarch64", &[]);
    let scratch = Scratch::new("refusals");
    for (stem, source, needle) in [
        (
            "extern_weak",
            "#![feature(linkage)]\n#![crate_type = \"lib\"]\n#[no_mangle]\n#[linkage = \"extern_weak\"]\n\
             pub static TCG_EXTERN_WEAK: i32 = 0;\n",
            "[TCG-LINKAGE] static `TCG_EXTERN_WEAK` has rustc linkage ExternalWeak",
        ),
        (
            "weak_tls",
            "#![feature(linkage, thread_local)]\n#![crate_type = \"lib\"]\n#[no_mangle]\n\
             #[thread_local]\n#[linkage = \"weak\"]\npub static mut TCG_WEAK_TLS: i32 = 3;\n",
            "[TCG-LINKAGE] thread-local static `TCG_WEAK_TLS` has rustc linkage WeakAny",
        ),
    ] {
        let dir = scratch.sub(stem);
        let path = dir.join(format!("{stem}.rs"));
        std::fs::write(&path, source).expect("write crate source");
        let output = toolchain_support::rustc_command()
            .arg(backend_arg())
            .args([
                "--target",
                TARGET,
                "-Cpanic=abort",
                "--emit=obj",
                "--out-dir",
            ])
            .arg(&dir)
            .arg(&path)
            .output()
            .expect("spawn trustc");
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(
            !output.status.success(),
            "{stem} must be refused:\n{stderr}"
        );
        assert!(
            stderr.contains(needle),
            "{stem} lacks {needle:?}:\n{stderr}"
        );
    }
    positive_evidence::record(
        positive_evidence::Evidence::ExpectedRefusal,
        positive_evidence::Certs::On,
    );
}
