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

// E2E (aarch64-apple-darwin): the MIR families ledger L06-P8 names, compiled
// by the bridge against rustc's LLVM backend on the same programs.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// WHAT THIS PINS
//
// * `SetDiscriminant` for every layout class (Direct tag, Direct over a
//   payload, Direct tags whose discriminants are not the variant index:
//   negative, wide and above-127 explicit `repr` values with payloads,
//   fieldless enums whose value is the tag, a niche in a `NonZeroU32` to
//   either variant, a niche in a `bool`, a niche in an explicit tag, a
//   single-variant layout) and every place class (through a reference, a
//   field or variant field through a reference, a field of a memory-backed
//   local, a bare local), as custom MIR at -O0..-O3 (`set_discriminant.rs`).
//   Before this change a projected place, and a fieldless enum through a
//   reference, were refused (`SetDiscriminant on unsupported place`,
//   `SetDiscriminant on non-memory pointee`).
// * `Rvalue::Discriminant` over the same layout classes plus niches in a
//   `char`, a reference, a `NonZeroU64` and a nested `Option<Option<bool>>`,
//   through a reference, a field, a variant field, a by-value argument and an
//   array element at a runtime index (refused before: `Rvalue::Discriminant
//   projected source`), as custom MIR at -O0..-O3 (`discriminant.rs`).
// * User `Drop` impls reached through rustc's own drop glue, with cleanup
//   edges taken by real panics caught in an LLVM-built harness: a boxed
//   linked list with a user `Drop` (refused before: `Drop of Box<Rec> whose
//   payload needs drop`), a node whose `Drop` panics mid-chain, `Vec<E>` with
//   an element whose `Drop` panics (refused before: `[TCG-EH-CLEANUP-LOOP]` in
//   `drop_in_place::<[E]>`), a guard live across a loop when a call unwinds
//   (refused before: the guard's pad needed a block argument from an unwind
//   edge), boxes dropped through a projection, and an enum cons list and
//   tree whose glue calls itself on each `Box<Self>` (refused before:
//   `Drop of Box<List> whose payload needs drop`), at -O0..-O3, with every
//   allocation counted (`drop_harness.rs`, `drop_guest.rs`); and indirect calls
//   with a live cleanup edge (a `thread_local!` access, a `Box<dyn Fn>` call, a
//   `Box<dyn Trait>` drop), refused on Darwin before ("indirect call with
//   cleanup unwind edge (EH active) not yet lowered").
// * `#[link_section]` statics in their Mach-O sections, and a
//   `__mod_init_func` constructor dyld runs (refused before:
//   `static with explicit #[link_section]`), at -O0 and -O2 (`link_section.rs`).
// * The families that stay unmodeled, refused by name with certificates on:
//   `become` (`[TCG-TAIL-CALL]`), `asm!` (`[TCG-INLINE-ASM]`), `global_asm!`
//   (`[TCG-GLOBAL-ASM]`), a function's `#[link_section]` and a Mach-O section
//   the emitter does not place (`[TCG-SECTION-*]`), a thread-local's
//   `#[link_section]`, and `wrap_binder!` (`[TCG-UNSAFE-BINDER]`).
//
// PROOFS-OFF DIAGNOSTIC. The native compiles pass the backend's
// `no-proof-certs` knob: with certificates on, these bodies are refused at
// proof promotion (`[TCG-PROOF-465]`, ledger L07-P2) independently of the
// families pinned here. A pass is testing evidence for the named programs
// against LLVM, not certified-object evidence. The refusal test compiles with
// certificates on: every refusal it names is decided before any proof work.

use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::time::Duration;

use darwin_native::TARGET;

const SET_DISCRIMINANT: &str = include_str!("support/mir_families/set_discriminant.rs");
const DISCRIMINANT: &str = include_str!("support/mir_families/discriminant.rs");
const DROP_HARNESS: &str = include_str!("support/mir_families/drop_harness.rs");
const DROP_GUEST: &str = include_str!("support/mir_families/drop_guest.rs");
const LINK_SECTION: &str = include_str!("support/mir_families/link_section.rs");
// The Linux FP-asm fixture's corpus and its hardware-checked C driver (GCC-style
// inline asm under every FPCR rounding mode), reused unchanged.
const FP_ASM_CORPUS: &str = include_str!("support/aarch64_fp_asm/corpus.rs");
const FP_ASM_DRIVER: &str = include_str!("support/aarch64_fp_asm/driver.c");

const RUN_LIMIT: Duration = Duration::from_secs(60);

/// A scratch directory, removed when the test that made it succeeds.
struct Scratch(PathBuf);

impl Scratch {
    fn new(stem: &str) -> Self {
        let path =
            std::env::temp_dir().join(format!("tcg_mir_families_{stem}_{}", std::process::id()));
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

#[derive(Clone, Copy, PartialEq)]
enum Backend {
    Bridge,
    Llvm,
}

impl Backend {
    fn name(self) -> &'static str {
        match self {
            Backend::Bridge => "bridge",
            Backend::Llvm => "llvm",
        }
    }
}

/// Compile `source` (written to `dir/<stem>.rs`) into `dir/<output>` with
/// `options`; the bridge compile passes the `no-proof-certs` knob. Panics with
/// the compiler's output on failure.
fn compile(
    dir: &Path,
    stem: &str,
    source: &str,
    output: &str,
    options: &[&str],
    backend: Backend,
) -> PathBuf {
    let path = dir.join(format!("{stem}.rs"));
    std::fs::write(&path, source).expect("write crate source");
    let out = dir.join(output);
    let mut command = toolchain_support::rustc_command();
    command.current_dir(dir);
    if backend == Backend::Bridge {
        command
            .arg(backend_arg())
            .arg(toolchain_support::backend_knobs_arg(&["no-proof-certs"]));
    }
    let result = command
        .args(["--target", TARGET])
        .args(options)
        .arg("-o")
        .arg(&out)
        .arg(&path)
        .output()
        .expect("spawn trustc");
    assert!(
        result.status.success(),
        "{} compile of {stem} with {options:?} failed:\n{}",
        backend.name(),
        text(&result)
    );
    out
}

/// Run `program` under the shared deadline; its stdout, or a panic naming the
/// failure.
fn run(program: &Path) -> String {
    match darwin_native::run_with_deadline(&mut Command::new(program), RUN_LIMIT) {
        Ok(output) if output.status.success() => {
            String::from_utf8_lossy(&output.stdout).trim().to_owned()
        }
        Ok(output) | Err(output) => panic!(
            "{} failed ({:?}):\n{}",
            program.display(),
            output.status,
            text(&output)
        ),
    }
}

#[test]
fn set_discriminant_writes_every_enum_layout_as_llvm_does() {
    darwin_native::require("mir_families_aarch64", &[]);
    let scratch = Scratch::new("setdisc");
    for opt in ["0", "1", "2", "3"] {
        let dir = scratch.sub(&format!("o{opt}"));
        let level = format!("-Copt-level={opt}");
        let options = ["-Cpanic=abort", level.as_str()];
        let llvm = compile(
            &dir,
            "setdisc",
            SET_DISCRIMINANT,
            "llvm",
            &options,
            Backend::Llvm,
        );
        let bridge = compile(
            &dir,
            "setdisc",
            SET_DISCRIMINANT,
            "bridge",
            &options,
            Backend::Bridge,
        );
        let theirs = run(&llvm);
        let ours = run(&bridge);
        assert_eq!(ours, theirs, "-Copt-level={opt}: bridge and LLVM disagree");
        // Each slot is one shape (see the guest's `main`); a changed program
        // must update this line deliberately.
        assert_eq!(
            ours, "1 9 1 8 1 300014 300012 42 77 2 100516 70200 300114 109114 713 200 1092345 1",
            "-Copt-level={opt}"
        );
    }
    println!("SET_DISCRIMINANT_LAYOUTS slots=18 writes=19 opts=0,1,2,3 matched=4");
    positive_evidence::record(
        positive_evidence::Evidence::NativeRun,
        positive_evidence::Certs::Off,
    );
}

#[test]
fn discriminant_reads_every_enum_layout_as_llvm_does() {
    darwin_native::require("mir_families_aarch64", &[]);
    let scratch = Scratch::new("discr");
    for opt in ["0", "1", "2", "3"] {
        let dir = scratch.sub(&format!("o{opt}"));
        let level = format!("-Copt-level={opt}");
        let options = ["-Cpanic=abort", level.as_str()];
        let llvm = compile(&dir, "discr", DISCRIMINANT, "llvm", &options, Backend::Llvm);
        let bridge = compile(
            &dir,
            "discr",
            DISCRIMINANT,
            "bridge",
            &options,
            Backend::Bridge,
        );
        let theirs = run(&llvm);
        let ours = run(&bridge);
        assert_eq!(ours, theirs, "-Copt-level={opt}: bridge and LLVM disagree");
        // The count, then each read in the guest's order; a changed program
        // must update this line deliberately.
        assert_eq!(
            ours,
            "43 -1 -1 -300 -300 7 7 10 7 200 -1 3 -300 -300 -1 7 -1 -300 7 10 200 3 \
             0 1 1 1 0 1 1 0 1 1 0 1 0 1 0 1 0 1 1 1 1 0",
            "-Copt-level={opt}"
        );
    }
    println!("DISCRIMINANT_READS values=43 opts=0,1,2,3 matched=4");
    positive_evidence::record(
        positive_evidence::Evidence::NativeRun,
        positive_evidence::Certs::Off,
    );
}

#[test]
fn user_drop_glue_and_cleanup_edges_match_llvm_through_real_panics() {
    darwin_native::require("mir_families_aarch64", &[]);
    let scratch = Scratch::new("drops");
    // The harness (allocation counter, catch_unwind boundary) is always LLVM's.
    let host = scratch.sub("host");
    let harness = compile(
        &host,
        "drop_harness",
        DROP_HARNESS,
        "libdrop_harness.rlib",
        &["--crate-type", "rlib", "-Copt-level=2"],
        Backend::Llvm,
    );
    let extern_arg = format!("drop_harness={}", harness.display());
    let mut panicked_rows = 0;
    for opt in ["0", "1", "2", "3"] {
        let dir = scratch.sub(&format!("o{opt}"));
        let level = format!("-Copt-level={opt}");
        let options = ["--extern", extern_arg.as_str(), level.as_str()];
        let llvm = compile(
            &dir,
            "drop_guest",
            DROP_GUEST,
            "llvm",
            &options,
            Backend::Llvm,
        );
        let bridge = compile(
            &dir,
            "drop_guest",
            DROP_GUEST,
            "bridge",
            &options,
            Backend::Bridge,
        );
        let theirs = run(&llvm);
        let ours = run(&bridge);
        assert_eq!(ours, theirs, "-Copt-level={opt}: bridge and LLVM disagree");
        let rows: Vec<Vec<i128>> = ours
            .lines()
            .map(|line| {
                line.split_whitespace()
                    .map(|field| field.parse().expect("numeric field"))
                    .collect()
            })
            .collect();
        assert_eq!(
            rows.len(),
            16,
            "-Copt-level={opt}: one row per scenario:\n{ours}"
        );
        // The panicking scenarios are exactly the seven that raise.
        let panicked: Vec<i128> = rows.iter().map(|row| row[0]).collect();
        assert_eq!(
            panicked,
            [0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 0, 1],
            "-Copt-level={opt}:\n{ours}"
        );
        // Every allocation a scenario made is freed by the time it returns or
        // its panic is caught (rows are recorded before anything is printed).
        assert!(
            rows.iter().all(|row| row[1] == 0),
            "-Copt-level={opt}: a scenario leaked or double-freed:\n{ours}"
        );
        panicked_rows += panicked.iter().filter(|p| **p == 1).count();
    }
    println!("USER_DROP_CLEANUP scenarios=16 opts=0,1,2,3 matched=4 caught_panics={panicked_rows}");
    positive_evidence::record(
        positive_evidence::Evidence::NativeRun,
        positive_evidence::Certs::Off,
    );
}

/// `(segment,section)` of `symbol` in `program`, from `nm -m`.
fn symbol_section(program: &Path, symbol: &str) -> String {
    let output = Command::new("nm")
        .arg("-m")
        .arg(program)
        .output()
        .expect("run nm -m");
    assert!(output.status.success(), "nm -m:\n{}", text(&output));
    let listing = String::from_utf8_lossy(&output.stdout);
    listing
        .lines()
        .find(|line| line.split_whitespace().last() == Some(symbol))
        .and_then(|line| {
            let start = line.find('(')?;
            let end = line[start..].find(')')? + start;
            Some(line[start + 1..end].to_owned())
        })
        .unwrap_or_else(|| panic!("{} defines no `{symbol}`:\n{listing}", program.display()))
}

#[test]
fn link_section_statics_land_in_their_mach_o_sections() {
    darwin_native::require("mir_families_aarch64", &["nm"]);
    let scratch = Scratch::new("link_section");
    for opt in ["0", "2"] {
        let dir = scratch.sub(&format!("o{opt}"));
        let level = format!("-Copt-level={opt}");
        let options = ["-Cpanic=abort", level.as_str()];
        let llvm = compile(&dir, "lsec", LINK_SECTION, "llvm", &options, Backend::Llvm);
        let bridge = compile(
            &dir,
            "lsec",
            LINK_SECTION,
            "bridge",
            &options,
            Backend::Bridge,
        );
        let theirs = run(&llvm);
        let ours = run(&bridge);
        assert_eq!(ours, theirs, "-Copt-level={opt}: bridge and LLVM disagree");
        // The constructor ran before `main` (40), the counter starts at 5.
        assert_eq!(ours, "6 7 3 77 40", "-Copt-level={opt}");
        for (symbol, section) in [
            ("_TCG_COUNTER", "__DATA,__tcg_data"),
            ("_TCG_TABLE", "__TEXT,__tcg_const"),
            ("_TCG_RO", "__DATA_CONST,__tcg_ro"),
        ] {
            assert_eq!(symbol_section(&llvm, symbol), section, "LLVM `{symbol}`");
            assert_eq!(
                symbol_section(&bridge, symbol),
                section,
                "-Copt-level={opt}: the bridge placed `{symbol}`"
            );
        }
    }
    println!("LINK_SECTION_STATICS sections=3 ctor=ran opts=0,2 matched=2");
    positive_evidence::record(
        positive_evidence::Evidence::NativeRun,
        positive_evidence::Certs::Off,
    );
}

/// Compile `source` with `--emit=obj` into `dir` and return every object the
/// compile wrote (the bridge may split a crate into several).
fn compile_objects(
    dir: &Path,
    stem: &str,
    source: &str,
    options: &[&str],
    backend: Backend,
) -> Vec<PathBuf> {
    let path = dir.join(format!("{stem}.rs"));
    std::fs::write(&path, source).expect("write crate source");
    let mut command = toolchain_support::rustc_command();
    command.current_dir(dir);
    if backend == Backend::Bridge {
        command
            .arg(backend_arg())
            .arg(toolchain_support::backend_knobs_arg(&["no-proof-certs"]));
    }
    let result = command
        .args(["--target", TARGET])
        .args(options)
        .arg("--out-dir")
        .arg(dir)
        .arg(&path)
        .output()
        .expect("spawn trustc");
    assert!(
        result.status.success(),
        "{} compile of {stem} with {options:?} failed:\n{}",
        backend.name(),
        text(&result)
    );
    let mut objects: Vec<PathBuf> = std::fs::read_dir(dir)
        .expect("read object directory")
        .filter_map(|entry| entry.ok().map(|entry| entry.path()))
        .filter(|path| path.extension().is_some_and(|ext| ext == "o"))
        .collect();
    objects.sort();
    assert!(
        !objects.is_empty(),
        "{} compile of {stem} wrote no object",
        backend.name()
    );
    objects
}

/// Link `objects` with the C `driver` into `dir/<name>` and run it.
fn link_driver_and_run(dir: &Path, name: &str, driver: &Path, objects: &[PathBuf]) -> String {
    let exe = dir.join(name);
    let link = Command::new("cc")
        .args([
            "-std=c11",
            "-O2",
            "-Wall",
            "-Wextra",
            "-Werror",
            "-frounding-math",
            "-ffp-contract=off",
        ])
        .arg(driver)
        .args(objects)
        .arg("-o")
        .arg(&exe)
        .output()
        .expect("spawn cc");
    assert!(link.status.success(), "link {name}:\n{}", text(&link));
    run(&exe)
}

#[test]
fn bounded_fp_asm_matches_the_hardware_like_llvm() {
    darwin_native::require("mir_families_aarch64", &["cc"]);
    let scratch = Scratch::new("fp_asm");
    let driver = scratch.0.join("driver.c");
    std::fs::write(&driver, FP_ASM_DRIVER).expect("write C driver");
    for opt in ["0", "1", "2", "3"] {
        let level = format!("-Copt-level={opt}");
        let options = [
            "--crate-type=lib",
            "--emit=obj",
            "-Cpanic=abort",
            "-Ccodegen-units=1",
            level.as_str(),
        ];
        for backend in [Backend::Llvm, Backend::Bridge] {
            let dir = scratch.sub(&format!("{}-o{opt}", backend.name()));
            let objects = compile_objects(&dir, "corpus", FP_ASM_CORPUS, &options, backend);
            // Every asm! block checked against GCC-style inline asm in the
            // driver, under every FPCR rounding mode, result bits and FPSR.
            assert_eq!(
                link_driver_and_run(&dir, "fp_asm", &driver, &objects),
                "PASS aarch64_fp_asm checks=2359296",
                "{} -Copt-level={opt}",
                backend.name()
            );
        }
    }
    println!("BOUNDED_FP_ASM checks=2359296 opts=0,1,2,3 llvm=4 bridge=4");
    positive_evidence::record(
        positive_evidence::Evidence::NativeRun,
        positive_evidence::Certs::Off,
    );
}

#[test]
fn unmodeled_families_are_refused_by_name() {
    darwin_native::require("mir_families_aarch64", &[]);
    let scratch = Scratch::new("refusals");
    for (stem, source, needle) in [
        (
            "tail_call",
            "#![feature(explicit_tail_calls)]\n#![allow(incomplete_features)]\n\
             #[no_mangle]\npub fn tcg_count(n: u64, acc: u64) -> u64 {\n\
             if n == 0 { acc } else { become tcg_count(n - 1, acc + n) }\n}\n",
            "[TCG-TAIL-CALL] TerminatorKind::TailCall",
        ),
        (
            "inline_asm",
            "#[no_mangle]\npub fn tcg_add3(a: u64) -> u64 {\n let r: u64;\n\
             unsafe { core::arch::asm!(\"add {r}, {a}, #3\", a = in(reg) a, r = out(reg) r, \
             options(pure, nomem, nostack)); }\n r\n}\n",
            "[TCG-INLINE-ASM] TerminatorKind::InlineAsm",
        ),
        (
            "global_asm",
            "core::arch::global_asm!(\".globl _tcg_forty_two\", \"_tcg_forty_two:\", \
             \"mov w0, #42\", \"ret\");\n",
            "[TCG-GLOBAL-ASM]",
        ),
        (
            "function_section",
            "#[no_mangle]\n#[link_section = \"__TEXT,__tcg_fn\"]\n\
             pub extern \"C\" fn tcg_placed(x: u32) -> u32 { x + 1 }\n",
            "[TCG-SECTION-TARGET] function `tcg_placed`",
        ),
        (
            "reserved_section",
            "#[no_mangle]\n#[link_section = \"__DATA,__bss\"]\npub static TCG_RES: u32 = 1;\n",
            "[TCG-SECTION-RESERVED] global `TCG_RES` requests Mach-O section `__DATA,__bss`",
        ),
        (
            "thread_local_section",
            "#![feature(thread_local)]\n#[no_mangle]\n#[thread_local]\n\
             #[link_section = \"__DATA,__tcg_tls\"]\npub static mut TCG_TLS: u32 = 1;\n",
            "thread-local static with explicit #[link_section = \"__DATA,__tcg_tls\"]",
        ),
        (
            "unsafe_binder",
            "#![feature(unsafe_binders)]\n#![allow(incomplete_features)]\n\
             use std::unsafe_binder::{unwrap_binder, wrap_binder};\n#[no_mangle]\n\
             pub fn tcg_binder(x: &u32) -> u32 {\n\
             let b: unsafe<'a> &'a u32 = unsafe { wrap_binder!(x) };\n\
             unsafe { *unwrap_binder!(b) }\n}\n",
            "[TCG-UNSAFE-BINDER] Rvalue::WrapUnsafeBinder",
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
                "--crate-type",
                "lib",
                "-Cpanic=abort",
                "--emit=obj",
                "--out-dir",
            ])
            .arg(&dir)
            .arg(&path)
            .output()
            .expect("spawn trustc");
        let transcript = text(&output);
        assert!(
            !output.status.success(),
            "{stem} must be refused:\n{transcript}"
        );
        assert!(
            transcript.contains(needle),
            "{stem} lacks {needle:?}:\n{transcript}"
        );
    }
    println!("UNMODELED_MIR_FAMILIES refused=7");
    positive_evidence::record(
        positive_evidence::Evidence::ExpectedRefusal,
        positive_evidence::Certs::On,
    );
}
