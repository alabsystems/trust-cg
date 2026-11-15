#[path = "support/backend_artifact.rs"]
mod backend_artifact_support;
#[path = "support/toolchain.rs"]
mod toolchain_support;

// wasm32 execution differential for rustc_codegen_trust_cg.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// Every `*.rs` crate in `support/wasm32_differential/` is compiled for
// `wasm32-unknown-unknown` twice from the one shared frontend command: by
// rustc's LLVM backend (the oracle) and by this backend's wasm32 object lane,
// both linked by `wasm-ld`; a crate's `//@ compile-flags:` lines add the same
// flags to both compiles. `compare.mjs` reads each export's signature from
// the oracle module, runs every export of both modules in node over a fixed
// input grid, and requires identical results, traps included. This is execution evidence for the corpus, not a proof: the wasm
// lane attaches no per-instruction certificates, so the compile passes
// `no-proof-certs`.
//
// Prerequisites; each missing one SKIPS with its reason:
// * `WASM32_SYSROOT`: a sysroot whose `lib/rustlib/wasm32-unknown-unknown/lib`
//   holds `core` and `compiler_builtins` built by this test's build compiler
//   (`scripts/build_wasm32_sysroot.sh` builds one from that compiler's own
//   library sources);
// * `wasm-ld`: `WASM_LD`, else `wasm-ld` on `PATH`;
// * `node` on `PATH`;
// * the build compiler's `-Ztrust-ir-cg-args` option.
//
// Every crate is compared in the default (debug) configuration. A crate may add
// configurations with lines of the form
// `// wasm32-differential-flags: -Copt-level=2 -Coverflow-checks=on`: each such
// line compiles and compares the crate once more with those codegen flags on
// both sides.
//
// A crate may depend on library crates from `extern/` with lines of the form
// `// wasm32-differential-extern: NAME FILE.rs [FLAGS...]`: in every
// configuration each side first compiles `extern/FILE.rs` as the `rlib` NAME
// with the same backend, the configuration's flags and then FLAGS (so a
// dependency can be built under different session flags from its user), and
// passes it to the crate as `--extern NAME`. A line of the form
// `// wasm32-differential-extern-llvm: NAME FILE.rs [FLAGS...]` declares a
// dependency both sides build with LLVM: this backend's module then links an
// LLVM-built library, so every call between the two crossing the ABI boundary
// in either direction (direct calls, `fn` pointers and vtables handed across)
// is compared against LLVM on both sides of the same boundary.
//
// `wasm32_in_bounds_addresses_are_geps_only_at_o1_and_above` drives the
// bridge knob `no-wasm32-place-gep`, a provisional surface pending owner
// sign-off (docs/wasm32_perf_roadmap.md, "Pending owner sign-off"); it
// follows that knob if it changes and is not a contract for its shape.

use std::ffi::OsString;
use std::path::{Path, PathBuf};
use std::process::Command;

const TARGET: &str = "wasm32-unknown-unknown";
/// The corpus exports and grid size; a run below either compared too little.
const MIN_EXPORTS: usize = 36;
const MIN_CHECKS: usize = 10_000;

fn fixture(name: &str) -> PathBuf {
    fixture_dir().join(name)
}

fn fixture_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/support/wasm32_differential")
}

/// The line prefix that declares one extra compile configuration of a crate.
const FLAGS_PREFIX: &str = "// wasm32-differential-flags:";

/// The compile configurations of `source`: the default (no extra flags), then
/// one per `FLAGS_PREFIX` line, in file order.
fn configurations(source: &Path) -> Vec<Vec<String>> {
    let text = std::fs::read_to_string(source).expect("corpus source");
    let mut configurations = vec![Vec::new()];
    for line in text.lines() {
        if let Some(flags) = line.trim().strip_prefix(FLAGS_PREFIX) {
            let flags: Vec<String> = flags.split_whitespace().map(str::to_owned).collect();
            assert!(
                !flags.is_empty(),
                "{}: an empty `{FLAGS_PREFIX}` line",
                source.display()
            );
            configurations.push(flags);
        }
    }
    configurations
}

/// The corpus crates, in name order.
fn corpus_files() -> Vec<PathBuf> {
    let mut files: Vec<PathBuf> = std::fs::read_dir(fixture_dir())
        .expect("corpus directory")
        .map(|entry| entry.expect("corpus entry").path())
        .filter(|path| path.extension().is_some_and(|ext| ext == "rs"))
        .collect();
    files.sort();
    files
}

fn on_path(tool: &str) -> Option<PathBuf> {
    std::env::split_paths(&std::env::var_os("PATH")?)
        .map(|dir| dir.join(tool))
        .find(|candidate| candidate.is_file())
}

struct Tools {
    sysroot: PathBuf,
    wasm_ld: PathBuf,
    node: PathBuf,
}

fn tools(test: &str) -> Option<Tools> {
    if toolchain_support::skip_without_backend_knobs(test) {
        return None;
    }
    let skip = |why: String| {
        eprintln!("{test}: SKIPPED — {why}");
        None
    };
    let Some(sysroot) = std::env::var_os("WASM32_SYSROOT").map(PathBuf::from) else {
        return skip(
            "WASM32_SYSROOT is unset; build one with scripts/build_wasm32_sysroot.sh".to_owned(),
        );
    };
    let core = sysroot.join(format!("lib/rustlib/{TARGET}/lib/libcore.rlib"));
    if !core.is_file() {
        return skip(format!("WASM32_SYSROOT has no {}", core.display()));
    }
    let wasm_ld = match std::env::var_os("WASM_LD") {
        Some(path) => PathBuf::from(path),
        None => match on_path("wasm-ld") {
            Some(path) => path,
            None => return skip("no wasm-ld (set WASM_LD or put wasm-ld on PATH)".to_owned()),
        },
    };
    let Some(node) = on_path("node") else {
        return skip("no node on PATH to execute the modules".to_owned());
    };
    Some(Tools {
        sysroot,
        wasm_ld,
        node,
    })
}

/// The line prefix that declares one library crate a corpus crate links,
/// built by the same backend as its user.
const EXTERN_PREFIX: &str = "// wasm32-differential-extern:";
/// The line prefix that declares one library crate a corpus crate links,
/// built by LLVM on both sides.
const EXTERN_LLVM_PREFIX: &str = "// wasm32-differential-extern-llvm:";

/// One `EXTERN_PREFIX` / `EXTERN_LLVM_PREFIX` dependency: its crate name, its
/// source under `extern/`, the flags added after the configuration's, and
/// whether LLVM builds it on both sides.
struct ExternCrate {
    name: String,
    source: PathBuf,
    flags: Vec<String>,
    llvm_only: bool,
}

/// The dependencies of `source`, in file order.
fn extern_crates(source: &Path) -> Vec<ExternCrate> {
    let text = std::fs::read_to_string(source).expect("corpus source");
    text.lines()
        .filter_map(|line| {
            let line = line.trim();
            line.strip_prefix(EXTERN_PREFIX)
                .map(|spec| (spec, false, EXTERN_PREFIX))
                .or_else(|| {
                    line.strip_prefix(EXTERN_LLVM_PREFIX)
                        .map(|spec| (spec, true, EXTERN_LLVM_PREFIX))
                })
        })
        .map(|(spec, llvm_only, prefix)| {
            let mut words = spec.split_whitespace().map(str::to_owned);
            let (Some(name), Some(file)) = (words.next(), words.next()) else {
                panic!("{}: `{prefix}` needs NAME FILE.rs", source.display());
            };
            let source = fixture_dir().join("extern").join(file);
            assert!(source.is_file(), "no extern crate {}", source.display());
            ExternCrate {
                name,
                source,
                flags: words.collect(),
                llvm_only,
            }
        })
        .collect()
}

/// Compile the dependencies of `source` for one side and configuration into
/// `dir`, returning the rustc arguments that link them.
fn compile_externs(
    tools: &Tools,
    source: &Path,
    flags: &[String],
    backend: Option<&Path>,
    dir: &Path,
) -> Vec<OsString> {
    let mut args = Vec::new();
    for dependency in extern_crates(source) {
        std::fs::create_dir_all(dir).expect("extern dir");
        let rlib = dir.join(format!("lib{}.rlib", dependency.name));
        let mut dependency_flags = flags.to_vec();
        dependency_flags.extend(dependency.flags.iter().cloned());
        dependency_flags.extend(["--crate-name".to_owned(), dependency.name.clone()]);
        compile(
            tools,
            &dependency.source,
            "rlib",
            &dependency_flags,
            &[],
            backend.filter(|_| !dependency.llvm_only),
            &rlib,
        );
        let mut extern_arg = OsString::from(format!("{}=", dependency.name));
        extern_arg.push(&rlib);
        let mut search = OsString::from("dependency=");
        search.push(dir);
        args.extend([
            OsString::from("--extern"),
            extern_arg,
            OsString::from("-L"),
            search,
        ]);
    }
    args
}

/// The base flags a corpus crate asks for on its `//@ compile-flags:` lines,
/// given to both compiles of that crate in every configuration.
fn corpus_flags(source: &Path) -> Vec<String> {
    std::fs::read_to_string(source)
        .expect("corpus source")
        .lines()
        .filter_map(|line| line.trim().strip_prefix("//@ compile-flags:"))
        .flat_map(|flags| flags.split_whitespace().map(str::to_owned))
        .collect()
}

/// Compile `source` as a `crate_type` to `out` with its base flags, one
/// configuration's extra codegen `flags` and the dependency arguments
/// `externs`, through this backend when `backend` is set.
fn compile(
    tools: &Tools,
    source: &Path,
    crate_type: &str,
    flags: &[String],
    externs: &[OsString],
    backend: Option<&Path>,
    out: &Path,
) {
    compile_with_knobs(
        tools,
        source,
        crate_type,
        flags,
        externs,
        backend,
        &["no-proof-certs"],
        out,
    );
}

/// [`compile`] with this backend's `knobs` in place of `no-proof-certs`
/// alone; `knobs` is ignored on the LLVM side.
#[allow(clippy::too_many_arguments)]
fn compile_with_knobs(
    tools: &Tools,
    source: &Path,
    crate_type: &str,
    flags: &[String],
    externs: &[OsString],
    backend: Option<&Path>,
    knobs: &[&str],
    out: &Path,
) {
    let mut cmd = toolchain_support::rustc_command();
    cmd.args(corpus_flags(source));
    if let Some(dylib) = backend {
        let mut arg = OsString::from("-Zcodegen-backend=");
        arg.push(dylib);
        cmd.arg(arg)
            .arg(toolchain_support::backend_knobs_arg(knobs));
    }
    let mut linker = OsString::from("linker=");
    linker.push(&tools.wasm_ld);
    let output = cmd
        .arg("--sysroot")
        .arg(&tools.sysroot)
        .args([
            "--target",
            TARGET,
            "--crate-type",
            crate_type,
            "-Cpanic=abort",
            "-C",
        ])
        .arg(linker)
        .args(flags)
        .args(externs)
        .arg("-o")
        .arg(out)
        .arg(source)
        .output()
        .expect("failed to spawn the build compiler");
    let side = if backend.is_some() {
        "trust-cg"
    } else {
        "LLVM"
    };
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "{side} wasm32 compile of {} {flags:?} failed:\n{stderr}",
        source.display(),
    );
    // wasm-ld links a call whose declared signature differs from the
    // definition's to a trapping stub, with only this warning.
    assert!(
        !stderr.contains("signature mismatch"),
        "{side} wasm32 link of {} {flags:?} bound a mismatched signature:\n{stderr}",
        source.display(),
    );
}

/// Compile `text` as a cdylib with LLVM and with this backend and require
/// every export to have the same wasm signature in both modules
/// (`compare.mjs --signatures`): the signature an object built by another
/// backend links against.
fn assert_wasm32_signatures_match_llvm(tools: &Tools, label: &str, text: &str) {
    let dir = std::env::temp_dir().join(format!("rcl2_wasm32_{label}_{}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("temp dir");
    let source = dir.join(format!("{label}.rs"));
    std::fs::write(&source, text).expect("write source");
    let backend = backend_artifact_support::current_test_backend();
    let (oracle, candidate) = (dir.join("llvm.wasm"), dir.join("trust_cg.wasm"));
    compile(tools, &source, "cdylib", &[], &[], None, &oracle);
    compile(
        tools,
        &source,
        "cdylib",
        &[],
        &[],
        Some(backend.as_path()),
        &candidate,
    );
    let output = Command::new(&tools.node)
        .arg(fixture("compare.mjs"))
        .arg("--signatures")
        .arg(&oracle)
        .arg(&candidate)
        .output()
        .expect("failed to spawn node");
    let _ = std::fs::remove_dir_all(&dir);
    assert!(
        output.status.success(),
        "{label}: export signatures differ from LLVM's:\n{}{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
fn wasm32_corpus_agrees_with_llvm() {
    let Some(tools) = tools("wasm32_corpus_agrees_with_llvm") else {
        return;
    };
    let dir = std::env::temp_dir().join(format!("rcl2_wasm32_diff_{}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("temp dir");
    let backend = backend_artifact_support::current_test_backend();
    let (mut exports, mut checks) = (0usize, 0usize);
    let mut failures = Vec::new();
    for (source, (index, flags)) in corpus_files().into_iter().flat_map(|source| {
        let configurations = configurations(&source);
        configurations
            .into_iter()
            .enumerate()
            .map(move |configuration| (source.clone(), configuration))
    }) {
        let file_stem = source
            .file_stem()
            .expect("stem")
            .to_string_lossy()
            .into_owned();
        let stem = if flags.is_empty() {
            file_stem.clone()
        } else {
            format!("{file_stem} {flags:?}")
        };
        let (oracle, candidate) = (
            dir.join(format!("{file_stem}.{index}.llvm.wasm")),
            dir.join(format!("{file_stem}.{index}.trust_cg.wasm")),
        );
        for (backend, side, out) in [
            (None, "llvm", &oracle),
            (Some(backend.as_path()), "trust_cg", &candidate),
        ] {
            let externs = compile_externs(
                &tools,
                &source,
                &flags,
                backend,
                &dir.join(format!("{file_stem}.{index}.{side}.deps")),
            );
            compile(&tools, &source, "cdylib", &flags, &externs, backend, out);
        }
        assert_ne!(
            std::fs::read(&oracle).expect("oracle module"),
            std::fs::read(&candidate).expect("candidate module"),
            "{stem}: the two compiles produced identical modules; the backend was not used"
        );
        let output = Command::new(&tools.node)
            .arg(fixture("compare.mjs"))
            .arg(&oracle)
            .arg(&candidate)
            .output()
            .expect("failed to spawn node");
        let stdout = String::from_utf8_lossy(&output.stdout);
        if !output.status.success() {
            failures.push(format!(
                "{stem}:\n{stdout}{}",
                String::from_utf8_lossy(&output.stderr)
            ));
            continue;
        }
        let summary = stdout.lines().last().expect("compare.mjs printed nothing");
        let field = |key: &str| -> usize {
            summary
                .split_whitespace()
                .find_map(|kv| kv.strip_prefix(key)?.strip_prefix('='))
                .and_then(|v| v.parse().ok())
                .unwrap_or_else(|| panic!("{stem}: no {key}= in `{summary}`"))
        };
        assert!(field("exports") > 0, "{stem}: no export was compared");
        exports += field("exports");
        checks += field("checks");
    }
    let _ = std::fs::remove_dir_all(&dir);
    assert!(
        failures.is_empty(),
        "wasm32 modules disagree:\n{}",
        failures.join("\n")
    );
    assert!(
        exports >= MIN_EXPORTS,
        "too few exports compared: {exports}"
    );
    assert!(checks >= MIN_CHECKS, "too few checks: {checks}");
}

/// Compile one wasm32 case with this backend; `Ok(())` on success, the
/// compiler's stderr otherwise.
fn compile_wasm32_case(
    tools: &Tools,
    dir: &std::path::Path,
    name: &str,
    text: &str,
    extra: &[&str],
) -> Result<(), String> {
    let source = dir.join(format!("{name}.rs"));
    std::fs::write(&source, text).expect("write source");
    let mut backend_arg = OsString::from("-Zcodegen-backend=");
    backend_arg.push(backend_artifact_support::current_test_backend());
    let mut linker = OsString::from("linker=");
    linker.push(&tools.wasm_ld);
    let output = toolchain_support::rustc_command()
        .arg(backend_arg)
        .arg(toolchain_support::backend_knobs_arg(&["no-proof-certs"]))
        .arg("--sysroot")
        .arg(&tools.sysroot)
        .args([
            "--target",
            TARGET,
            "--crate-type",
            "cdylib",
            "-Cpanic=abort",
            "-C",
        ])
        .arg(linker)
        .args(extra)
        .arg("-o")
        .arg(dir.join(format!("{name}.wasm")))
        .arg(&source)
        .output()
        .expect("failed to spawn the build compiler");
    if output.status.success() {
        Ok(())
    } else {
        Err(String::from_utf8_lossy(&output.stderr).into_owned())
    }
}

/// Each case either compiles (`None`) or is refused naming `Some(code)`,
/// never with an ICE.
fn assert_wasm32_cases(
    tools: &Tools,
    label: &str,
    prelude: &str,
    cases: &[(&str, &str, &[&str], Option<&str>)],
) {
    let dir = std::env::temp_dir().join(format!("rcl2_wasm32_{label}_{}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("temp dir");
    for &(name, item, extra, refusal) in cases {
        let result = compile_wasm32_case(tools, &dir, name, &format!("{prelude}{item}\n"), extra);
        match (refusal, result) {
            (None, Ok(())) => {}
            (None, Err(stderr)) => panic!("{name}: the control must compile:\n{stderr}"),
            (Some(code), Ok(())) => panic!("{name}: expected a {code} refusal, but it compiled"),
            (Some(code), Err(stderr)) => {
                assert!(
                    stderr.contains(code),
                    "{name}: expected a {code} refusal:\n{stderr}"
                );
                assert!(
                    !stderr.contains("internal compiler error"),
                    "{name}: ICE:\n{stderr}"
                );
            }
        }
    }
    let _ = std::fs::remove_dir_all(&dir);
}

/// rustc's wasm32 C ABI passes and returns a heterogeneous `#[repr(C)]` union
/// through memory (`PassMode::Indirect`: a pointer to a caller-made copy, an
/// `sret` buffer), and its Rust ABI every `Memory` value wider than a pointer
/// it does not cast — a one-lane array or union, a padded over-aligned scalar
/// newtype (`#[repr(align(64))] struct(u64)`), `AtomicU64`. Both ABIs follow
/// that convention (the by-memory plan `Wasm32IndirectCarrier`) for direct
/// calls, calls through `fn` pointers and exported definitions alike: the
/// exported signatures here are LLVM's, and `r5-bridge-align-abi.rs` /
/// `r6-bridge-wasm32.rs` run the convention against callers and callees LLVM
/// built. A closure body returning such a carrier by value keeps its
/// one-value return, which departs from rustc's `FnAbi` and is refused by
/// name. The controls keep compiling: a homogeneous union, a two-field
/// struct, and Rust-ABI functions taking and returning by-memory single-lane
/// values.
#[test]
fn wasm32_by_memory_union_abi_follows_rustc_or_is_refused_by_name() {
    let Some(tools) = tools("wasm32_by_memory_union_abi_follows_rustc_or_is_refused_by_name")
    else {
        return;
    };
    let prelude = "#![no_std]\n\
        #[panic_handler]\n\
        fn panic(_: &core::panic::PanicInfo) -> ! { core::arch::wasm32::unreachable() }\n\
        #[repr(C)] #[derive(Clone, Copy)] pub union U4 { pub a: u32, pub c: u16 }\n\
        #[repr(C)] #[derive(Clone, Copy)] pub union U8 { pub a: u64, pub b: [u8; 8] }\n\
        #[repr(C)] #[derive(Clone, Copy)] pub union Same { pub a: u32, pub b: i32 }\n\
        #[repr(C)] #[derive(Clone, Copy)] pub struct S6 { pub a: u32, pub b: u16 }\n\
        #[derive(Clone, Copy)] pub struct A1(pub [u64; 1]);\n";
    const BYVAL: Option<&str> = Some("[TCG-WASM32-BYVAL-ABI]");
    assert_wasm32_cases(
        &tools,
        "union",
        prelude,
        &[
            (
                "take_u4",
                "#[no_mangle] pub extern \"C\" fn take_u4(x: U4) -> u32 { unsafe { x.a } }",
                &[],
                None,
            ),
            (
                "take_u8",
                "#[no_mangle] pub extern \"C\" fn take_u8(x: U8) -> u64 { unsafe { x.a } }",
                &[],
                None,
            ),
            (
                "ret_u4",
                "#[no_mangle] pub extern \"C\" fn ret_u4(k: u32) -> U4 { U4 { a: k } }",
                &[],
                None,
            ),
            (
                "rust_fn_pointer",
                "#[inline(never)] fn u8v(x: U8) -> u64 { unsafe { x.a } }\n\
                 #[no_mangle] pub extern \"C\" fn e(k: u64) -> u64 { \
                 let f: fn(U8) -> u64 = core::hint::black_box(u8v); f(U8 { a: k }) }",
                &[],
                None,
            ),
            (
                "rust_closure_carrier_return",
                "#[no_mangle] pub extern \"C\" fn e(k: u64) -> u64 { \
                 let f = core::hint::black_box(|v: u64| core::sync::atomic::AtomicU64::new(v)); \
                 f(k).into_inner() }",
                &[],
                BYVAL,
            ),
            (
                "take_same",
                "#[no_mangle] pub extern \"C\" fn take_same(x: Same) -> u32 { unsafe { x.a } }",
                &[],
                None,
            ),
            (
                "take_s6",
                "#[no_mangle] pub extern \"C\" fn take_s6(x: S6) -> u32 { x.a ^ x.b as u32 }",
                &[],
                None,
            ),
            (
                "rust_over_aligned_fn_pointer",
                "#[repr(align(64))] #[derive(Clone, Copy)] pub struct A64(pub u64, pub u32);\n\
                 #[inline(never)] fn a64(x: A64) -> u64 { x.0 }\n\
                 #[no_mangle] pub extern \"C\" fn e(k: u64) -> u64 { \
                 let f: fn(A64) -> u64 = core::hint::black_box(a64); f(A64(k, 1)) }",
                &[],
                None,
            ),
            (
                "rust_over_aligned_carrier_fn_pointer",
                "#[repr(align(64))] #[derive(Clone, Copy)] pub struct P64(pub u64);\n\
                 #[inline(never)] fn p64(x: P64) -> u64 { x.0 }\n\
                 #[no_mangle] pub extern \"C\" fn e(k: u64) -> u64 { \
                 let f: fn(P64) -> u64 = core::hint::black_box(p64); f(P64(k)) }",
                &[],
                None,
            ),
            (
                "rust_internal",
                "#[inline(never)] fn a1(x: A1) -> u64 { x.0[0] }\n\
                 #[inline(never)] fn u8v(x: U8) -> u64 { unsafe { x.a } }\n\
                 #[inline(never)] fn mk(k: u64) -> A1 { A1([k]) }\n\
                 #[no_mangle] pub extern \"C\" fn e(k: u64) -> u64 { \
                 a1(core::hint::black_box(mk(k))) ^ u8v(core::hint::black_box(U8 { a: k })) }",
                &[],
                None,
            ),
        ],
    );
    assert_wasm32_signatures_match_llvm(
        &tools,
        "union_signatures",
        &format!(
            "{prelude}\
             #[repr(C, align(8))] #[derive(Clone, Copy)] pub struct S8 {{ pub a: u32 }}\n\
             #[repr(C, align(32))] #[derive(Clone, Copy)] pub struct C32 {{ pub a: u32, pub b: u64 }}\n\
             #[repr(C, align(64))] #[derive(Clone, Copy)] pub union UA {{ pub a: u32, pub c: u16 }}\n\
             #[repr(align(64))] #[derive(Clone, Copy)] pub struct A64 {{ pub a: u64, pub b: u32 }}\n\
             #[no_mangle] pub extern \"C\" fn take_u4(x: U4) -> u32 {{ unsafe {{ x.a }} }}\n\
             #[no_mangle] pub extern \"C\" fn take_u8(x: U8) -> u64 {{ unsafe {{ x.a }} }}\n\
             #[no_mangle] pub extern \"C\" fn ret_u4(k: u32) -> U4 {{ U4 {{ a: k }} }}\n\
             #[no_mangle] pub extern \"C\" fn ret_u8(k: u64) -> U8 {{ U8 {{ a: k }} }}\n\
             #[no_mangle] pub extern \"C\" fn take_s8(x: S8, k: u32) -> u32 {{ x.a ^ k }}\n\
             #[no_mangle] pub extern \"C\" fn ret_s8(k: u32) -> S8 {{ S8 {{ a: k }} }}\n\
             #[no_mangle] pub extern \"C\" fn take_c32(x: C32) -> u64 {{ x.b }}\n\
             #[no_mangle] pub extern \"C\" fn ret_c32(k: u32) -> C32 {{ C32 {{ a: k, b: 3 }} }}\n\
             #[no_mangle] pub extern \"C\" fn take_ua(x: UA) -> u32 {{ unsafe {{ x.a }} }}\n\
             #[no_mangle] pub fn take_a64(x: A64, k: u32) -> u64 {{ x.a ^ k as u64 }}\n\
             #[no_mangle] pub fn ret_a64(k: u32) -> A64 {{ A64 {{ a: k as u64, b: k }} }}\n"
        ),
    );
    // Exported Rust-ABI definitions of one-wasm-value by-memory types: every
    // caller outside this module binds rustc's signature.
    assert_wasm32_signatures_match_llvm(
        &tools,
        "rust_abi_signatures",
        &format!(
            "{prelude}\
             use core::sync::atomic::{{AtomicI64, AtomicU64}};\n\
             #[repr(align(8))] #[derive(Clone, Copy)] pub struct A8(pub u32);\n\
             #[derive(Clone, Copy)] pub struct F1(pub [f64; 1]);\n\
             #[derive(Clone, Copy)] pub union V {{ pub a: u64, pub b: f32 }}\n\
             #[no_mangle] pub fn take_arr64(a: [u64; 1], k: u64) -> u64 {{ a[0] ^ k }}\n\
             #[no_mangle] pub fn ret_arr64(k: u64) -> [u64; 1] {{ [k] }}\n\
             #[no_mangle] pub fn take_i128a(a: [i128; 1]) -> i64 {{ a[0] as i64 }}\n\
             #[no_mangle] pub fn take_f1(a: F1) -> f64 {{ a.0[0] }}\n\
             #[no_mangle] pub fn take_a8(a: A8, k: u32) -> A8 {{ A8(a.0 ^ k) }}\n\
             #[no_mangle] pub fn take_v(v: V) -> V {{ v }}\n\
             #[no_mangle] pub fn take_u8(x: U8, k: u64) -> U8 {{ U8 {{ a: unsafe {{ x.a }} ^ k }} }}\n\
             #[no_mangle] pub fn take_a1(x: A1) -> A1 {{ x }}\n\
             #[no_mangle] pub fn new_atomic(v: u64) -> AtomicU64 {{ AtomicU64::new(v) }}\n\
             #[no_mangle] pub fn take_atomic(a: AtomicI64) -> i64 {{ a.into_inner() }}\n"
        ),
    );
}

/// The object lane reserves every `__tcg_divmod128_` name for its weak hidden
/// 128-bit division helper. A crate that defines such a name is refused by
/// name in EVERY object, whether or not that object divides: when the merged
/// CGU compile fails, the bridge compiles the CGU function by function, which
/// puts the definition and the division into different objects, and a strong
/// user definition would then replace the helper at link time (each division
/// silently returning the user's result). An object at O0 carries the baseline
/// helper and an object at O1 and above the estimate helper, under names that
/// differ by their template digests; each hijack case defines the name its own
/// level's object binds its divisions to, and the test first checks, on a
/// linked division module of every level, that this is the helper the module
/// carries.
#[test]
fn wasm32_reserved_division_helper_symbol_is_refused_by_name() {
    let Some(tools) = tools("wasm32_reserved_division_helper_symbol_is_refused_by_name") else {
        return;
    };
    let prelude = "#![no_std]\n\
        #[panic_handler]\n\
        fn panic(_: &core::panic::PanicInfo) -> ! { core::arch::wasm32::unreachable() }\n\
        mod b {\n\
            #[inline(never)]\n\
            pub fn d(x: u64, y: u64) -> u128 { ((x as u128) << 64 | 77) / ((y as u128) | 1) }\n\
        }\n";
    let division = "#[no_mangle] pub extern \"C\" fn e(x: u64, y: u64) -> u64 { \
         let r = b::d(x, y); (r as u64) ^ (r >> 64) as u64 }";
    // The helper names of the baseline (O0) and estimate (O1 and above)
    // templates: `__tcg_divmod128_` and the first 16 hex digits of the
    // template's SHA-256 (`trust_cg_codegen::wasm::divmod128_helper_name`).
    const BASELINE: &str = "__tcg_divmod128_7b90c2514708d153";
    const ESTIMATE: &str = "__tcg_divmod128_5af6f467d6747164";
    let levels: [(&str, &[&str], &str); 4] = [
        ("o0", &[], BASELINE),
        ("o1", &["-Copt-level=1"], ESTIMATE),
        ("o2", &["-Copt-level=2"], ESTIMATE),
        ("o3", &["-Copt-level=3"], ESTIMATE),
    ];
    let dir = std::env::temp_dir().join(format!(
        "rcl2_wasm32_reserved_divmod_names_{}",
        std::process::id()
    ));
    std::fs::create_dir_all(&dir).expect("temp dir");
    for &(level, flags, helper) in &levels {
        let name = format!("division_{level}");
        if let Err(stderr) = compile_wasm32_case(
            &tools,
            &dir,
            &name,
            &format!("{prelude}{division}\n"),
            flags,
        ) {
            panic!("{name}: the division module must compile:\n{stderr}");
        }
        let module = std::fs::read(dir.join(format!("{name}.wasm"))).expect("division module");
        let carries = |symbol: &str| {
            module
                .windows(symbol.len())
                .any(|window| window == symbol.as_bytes())
        };
        let other = if helper == BASELINE {
            ESTIMATE
        } else {
            BASELINE
        };
        assert!(
            carries(helper) && !carries(other),
            "{name}: the module must carry {helper} and not {other}"
        );
    }
    let _ = std::fs::remove_dir_all(&dir);
    let hijack_of = |helper: &str| {
        format!(
            "mod a {{\n\
                #[no_mangle]\n\
                pub extern \"C\" fn {helper}(\n\
                    nlo: u64, nhi: u64, _dlo: u64, _dhi: u64, out: *mut u64, _m: u32) {{\n\
                    unsafe {{ *out = nlo ^ 0x5555; *out.add(1) = nhi; }}\n\
                }}\n\
            }}\n\
            {division}"
        )
    };
    let hijack_baseline = hijack_of(BASELINE);
    let hijack_estimate = hijack_of(ESTIMATE);
    let other_digest =
        "#[no_mangle] pub extern \"C\" fn __tcg_divmod128_0000000000000000(x: u64) -> u64 { x }";
    const SYMBOL: Option<&str> = Some("[TCG-WASM-SYMBOL]");
    assert_wasm32_cases(
        &tools,
        "reserved_divmod_symbol",
        prelude,
        &[
            (
                "hijack_o0_cgu1",
                &hijack_baseline,
                &["-Ccodegen-units=1"],
                SYMBOL,
            ),
            (
                "hijack_o0_cgu16",
                &hijack_baseline,
                &["-Ccodegen-units=16"],
                SYMBOL,
            ),
            (
                "hijack_o1_cgu16",
                &hijack_estimate,
                &["-Copt-level=1", "-Ccodegen-units=16"],
                SYMBOL,
            ),
            (
                "hijack_o2_cgu1",
                &hijack_estimate,
                &["-Copt-level=2", "-Ccodegen-units=1"],
                SYMBOL,
            ),
            (
                "hijack_o2_cgu16",
                &hijack_estimate,
                &["-Copt-level=2", "-Ccodegen-units=16"],
                SYMBOL,
            ),
            (
                "hijack_o3_cgu16",
                &hijack_estimate,
                &["-Copt-level=3", "-Ccodegen-units=16"],
                SYMBOL,
            ),
            ("other_digest", other_digest, &[], SYMBOL),
            ("division_control", division, &["-Copt-level=2"], None),
        ],
    );
}

/// The LLVM intrinsics `core::arch::wasm32` declares as foreign functions
/// (`memory_size` / `memory_grow`: `llvm.wasm.memory.size.i32` /
/// `llvm.wasm.memory.grow.i32`) have no trust-ir construct; a call is refused
/// by name at compile time instead of leaving an import no object defines.
#[test]
fn wasm32_llvm_intrinsics_are_refused_by_name() {
    let Some(tools) = tools("wasm32_llvm_intrinsics_are_refused_by_name") else {
        return;
    };
    let prelude = "#![no_std]\n\
        #[panic_handler]\n\
        fn panic(_: &core::panic::PanicInfo) -> ! { core::arch::wasm32::unreachable() }\n";
    const INTRINSIC: Option<&str> = Some("[TCG-WASM32-LLVM-INTRINSIC]");
    assert_wasm32_cases(
        &tools,
        "llvm_intrinsics",
        prelude,
        &[
            (
                "memory_size",
                "#[no_mangle] pub extern \"C\" fn pages() -> u32 { \
                 core::arch::wasm32::memory_size(0) as u32 }",
                &[],
                INTRINSIC,
            ),
            (
                "memory_grow",
                "#[no_mangle] pub extern \"C\" fn grow(n: u32) -> u32 { \
                 core::arch::wasm32::memory_grow(0, n as usize & 1) as u32 }",
                &["-Copt-level=2"],
                INTRINSIC,
            ),
            (
                "unreachable_control",
                "#[no_mangle] pub extern \"C\" fn f(x: u32) -> u32 { \
                 if x == 7 { core::arch::wasm32::unreachable() } x }",
                &[],
                None,
            ),
        ],
    );
}

/// A reversed `RangeInclusive` fold with a CAPTURING closure. Unoptimized,
/// the caller's `rfold` route drives it, so std's own `rfold` body is dead;
/// that body's `spec_try_rfold` call, whose wasm32 back-to-front route refuses
/// a capturing closure, keeps the general path inside a std body, and the
/// crate compiles (once it was refused by that dead body). At `-O2` rustc
/// inlines `rfold` into the caller, the live `spec_try_rfold` call cannot be
/// driven, and it is refused by name rather than reaching std's body, which
/// this backend does not lower (it used to trap at run time). The shapes are
/// not in the execution corpus: the dead body's call binds the trapping stub
/// with a mismatched signature, which the corpus compile refuses to accept.
#[test]
fn wasm32_rev_range_inclusive_capturing_folds_compile_or_are_refused_by_name() {
    let Some(tools) =
        tools("wasm32_rev_range_inclusive_capturing_folds_compile_or_are_refused_by_name")
    else {
        return;
    };
    let prelude = "#![no_std]\n\
        #[panic_handler]\n\
        fn panic(_: &core::panic::PanicInfo) -> ! { core::arch::wasm32::unreachable() }\n\
        #[inline(never)] fn fold_capture(a: u32, b: u32, k: u32) -> u32 { \
        (a..=b).rev().fold(1u32, |acc, x| acc.wrapping_mul(k).wrapping_add(x)) }\n\
        #[inline(never)] fn map_sum_capture_ref(a: u64, b: u64, k: &u64) -> u64 { \
        (a..=b).rev().map(|x| x ^ *k).sum() }\n";
    const ITEM: &str = "#[no_mangle] pub extern \"C\" fn f(a: u32, b: u32) -> u64 { \
        let k = u64::from(a) << 3; \
        u64::from(fold_capture(a % 50, b % 50, a ^ b)) \
        ^ map_sum_capture_ref(u64::from(a % 50), u64::from(b % 50), &k) }";
    assert_wasm32_cases(
        &tools,
        "rev_incl_capture",
        prelude,
        &[
            ("o0", ITEM, &[], None),
            ("o1", ITEM, &["-Copt-level=1"], None),
            ("o2", ITEM, &["-Copt-level=2"], Some("[TCG-ITER-UNMODELED]")),
        ],
    );
}

/// Reversed `RangeInclusive` folds outside the wasm32 back-to-front
/// `spec_try_rfold` route: a `char` range (std steps over the surrogate gap)
/// and a `bool`, `char` or one-field newtype accumulator. At `-O2`/`-O3` rustc
/// inlines `rfold` into the caller, the live `spec_try_rfold` call keeps the
/// general path, and std's body (`[TCG-RET-UNBOUND]`) became a dead-iterator
/// trap stub: every call trapped where LLVM computes a value. The crate is now
/// refused by name once the reference graph shows this crate's own code reaches
/// the stub. A primitive accumulator over an integer range is the control: the
/// route drives it, and it compiles.
#[test]
fn wasm32_rev_range_inclusive_folds_reaching_a_trap_stub_are_refused_by_name() {
    let Some(tools) =
        tools("wasm32_rev_range_inclusive_folds_reaching_a_trap_stub_are_refused_by_name")
    else {
        return;
    };
    let prelude = "#![no_std]\n\
        #[panic_handler]\n\
        fn panic(_: &core::panic::PanicInfo) -> ! { core::arch::wasm32::unreachable() }\n\
        #[derive(Clone, Copy)] pub struct W(pub u32);\n";
    const REACHED: Option<&str> = Some("[TCG-ITER-STUB-REACHABLE]");
    const CHAR_RANGE: &str = "#[inline(never)] fn h(lo: char, hi: char) -> u64 { \
        (lo..=hi).rev().fold(3u64, |a, c| a.wrapping_mul(131).wrapping_add(c as u64)) }\n\
        #[no_mangle] pub extern \"C\" fn f(a: u32, b: u32) -> u64 { \
        h(char::from_u32(0xD7F0 + a % 32).unwrap_or('a'), \
        char::from_u32(0xE000 + b % 20).unwrap_or('z')) }";
    const BOOL_ACC: &str = "#[inline(never)] fn h(lo: u32, hi: u32) -> bool { \
        (lo..=hi).rev().fold(false, |a, x| a ^ (x % 3 == 0)) }\n\
        #[no_mangle] pub extern \"C\" fn f(a: u32, b: u32) -> u32 { h(a % 100, b % 100) as u32 }";
    const CHAR_ACC: &str = "#[inline(never)] fn h(lo: u32, hi: u32) -> char { \
        (lo..=hi).rev().fold('a', |c, x| if x % 2 == 0 { \
        char::from_u32(c as u32 + 1).unwrap_or('a') } else { c }) }\n\
        #[no_mangle] pub extern \"C\" fn f(a: u32, b: u32) -> u32 { h(a % 60, b % 60) as u32 }";
    const NEWTYPE_ACC: &str = "#[inline(never)] fn h(lo: u32, hi: u32) -> W { \
        (lo..=hi).rev().fold(W(5), |W(c), x| W(c.wrapping_mul(7) ^ x)) }\n\
        #[no_mangle] pub extern \"C\" fn f(a: u32, b: u32) -> u32 { h(a % 60, b % 60).0 }";
    const CONTROL: &str = "#[inline(never)] fn h(lo: u32, hi: u32) -> u32 { \
        (lo..=hi).rev().fold(5u32, |c, x| c.wrapping_mul(7) ^ x) }\n\
        #[no_mangle] pub extern \"C\" fn f(a: u32, b: u32) -> u32 { h(a % 60, b % 60) }";
    assert_wasm32_cases(
        &tools,
        "rev_incl_stub_reached",
        prelude,
        &[
            ("char_range_o2", CHAR_RANGE, &["-Copt-level=2"], REACHED),
            ("char_range_o3", CHAR_RANGE, &["-Copt-level=3"], REACHED),
            ("bool_acc_o2", BOOL_ACC, &["-Copt-level=2"], REACHED),
            ("char_acc_o2", CHAR_ACC, &["-Copt-level=2"], REACHED),
            ("newtype_acc_o2", NEWTYPE_ACC, &["-Copt-level=2"], REACHED),
            ("newtype_acc_o3", NEWTYPE_ACC, &["-Copt-level=3"], REACHED),
            ("control_o2", CONTROL, &["-Copt-level=2"], None),
            ("control_o0", CONTROL, &[], None),
        ],
    );
}

/// rustc gives a `#[track_caller]` instance a trailing `&'static Location`
/// parameter, and this backend's declarations, definitions and calls follow
/// it on every target (`r6-bridge-wasm32-caller.rs` runs them against LLVM's
/// on wasm32). A `#[track_caller]` closure (`closure_track_caller`) is declared
/// with the parameter too, and the MIR closure-call lane passes the Location
/// of its call (`r6-bridge-wasm32-caller.rs`'s `lc_closure` runs it against
/// LLVM); the hand-built iterator lanes, which pass none, still refuse it by
/// name ([TCG-TRACK-CALLER-ABI]). These all compile: the closure through a
/// generic `Fn` bound, and a `#[track_caller]` function through a generic `Fn`
/// bound (its `Fn` shim passes the Location) and through a `fn` pointer (its
/// reify shim takes none).
#[test]
fn wasm32_track_caller_closures_and_shims_compile() {
    let Some(tools) = tools("wasm32_track_caller_closures_and_shims_compile") else {
        return;
    };
    let prelude = "#![no_std]\n\
        #![feature(closure_track_caller)]\n\
        #[panic_handler]\n\
        fn panic(_: &core::panic::PanicInfo) -> ! { core::arch::wasm32::unreachable() }\n\
        use core::panic::Location;\n\
        #[inline(never)] fn app<F: Fn(u32) -> u32>(f: F, x: u32) -> u32 { f(x) }\n\
        #[track_caller] fn tc(v: u32) -> u32 { v ^ Location::caller().line() }\n";
    const CLOSURE: Option<&str> = None;
    assert_wasm32_cases(
        &tools,
        "track_caller",
        prelude,
        &[
            (
                "closure",
                "#[no_mangle] pub extern \"C\" fn c(x: u32) -> u32 { \
                 app(#[track_caller] |v| v ^ Location::caller().column(), x) }",
                &[],
                CLOSURE,
            ),
            (
                "closure_opt",
                "#[no_mangle] pub extern \"C\" fn c(x: u32) -> u32 { \
                 app(#[track_caller] |v| v ^ Location::caller().column(), x) }",
                &["-Copt-level=2"],
                CLOSURE,
            ),
            (
                "fn_item_through_fn_bound",
                "#[no_mangle] pub extern \"C\" fn f(x: u32) -> u32 { app(tc, x) }",
                &[],
                None,
            ),
            (
                "fn_pointer",
                "#[no_mangle] pub extern \"C\" fn p(x: u32) -> u32 { \
                 let f: fn(u32) -> u32 = core::hint::black_box(tc); f(x) }",
                &[],
                None,
            ),
        ],
    );
}

/// Statics and thread-locals this backend cannot place are refused by name: an
/// `extern` static declared with `#[linkage]` (rustc makes it a private cell
/// holding the symbol's address), and a `#[thread_local]` in a session that
/// may run several threads (`+atomics`, or a CPU such as `bleeding-edge` that
/// implies it). The same thread-local compiles as a plain static on the
/// atomics-free CPUs.
#[test]
fn wasm32_static_placements_are_refused_by_name() {
    let Some(tools) = tools("wasm32_static_placements_are_refused_by_name") else {
        return;
    };
    let prelude = "#![no_std]\n\
        #![feature(linkage, thread_local)]\n\
        #[panic_handler]\n\
        fn panic(_: &core::panic::PanicInfo) -> ! { core::arch::wasm32::unreachable() }\n";
    const WEAK: &str = "extern \"C\" { #[linkage = \"extern_weak\"] static TCG_WEAK_UNDEF: *const u32; }\n\
        #[no_mangle] pub extern \"C\" fn w(x: u32) -> u32 { unsafe { \
        let p = TCG_WEAK_UNDEF; if p.is_null() { x } else { *p } } }";
    const TLS: &str = "#[thread_local] static mut T: u32 = 5;\n\
        #[no_mangle] pub extern \"C\" fn t(x: u32) -> u32 { unsafe { T = T.wrapping_add(x); T } }";
    const TLS_REFUSED: Option<&str> = Some("[TCG-WASM32-TLS]");
    assert_wasm32_cases(
        &tools,
        "statics",
        prelude,
        &[
            (
                "extern_weak",
                WEAK,
                &[],
                Some("[TCG-EXTERN-STATIC-LINKAGE]"),
            ),
            (
                "tls_atomics",
                TLS,
                &["-Ctarget-feature=+atomics"],
                TLS_REFUSED,
            ),
            (
                "tls_bleeding_edge",
                TLS,
                &["-Ctarget-cpu=bleeding-edge"],
                TLS_REFUSED,
            ),
            ("tls_generic", TLS, &[], None),
            ("tls_mvp", TLS, &["-Ctarget-cpu=mvp"], None),
        ],
    );
}

/// A crate-private helper placed in one codegen unit is a strong definition
/// the wasm lane analyses, so a check inside it that passes only for one
/// address must count as exposing it. Here `check` bounds-checks
/// `T[p - k]` (an `assert` under `panic=abort`), which passes only when `k`
/// is `a`'s address; `b` lives in a later scope; the word at `k` is then read
/// back. The only non-panicking result is `7 * 100 + 7 + v`: `b` may never
/// take `a`'s bytes. The fixed-grid comparison above cannot see this (the
/// oracle's frame differs, so both sides panic at every grid input), so `k`
/// is swept over the top of the stack, one fresh instance per call (a trap
/// leaves the stack pointer lowered).
#[test]
fn wasm32_an_address_checked_in_a_helper_keeps_its_allocation() {
    let Some(tools) = tools("wasm32_an_address_checked_in_a_helper_keeps_its_allocation") else {
        return;
    };
    const SOURCE: &str = "#![no_std]\n\
        #[panic_handler]\n\
        fn panic(_: &core::panic::PanicInfo) -> ! { core::arch::wasm32::unreachable() }\n\
        static T: [u8; 1] = [1];\n\
        #[inline(never)]\n\
        fn fill(a: &mut [u32; 4], v: u32) -> u32 {\n\
            let mut i = 0;\n\
            while i < 4 { a[i] = v; i += 1; }\n\
            a[(v & 3) as usize]\n\
        }\n\
        #[inline(never)]\n\
        fn check(p: usize, k: usize) { let _t = T[p.wrapping_sub(k)]; }\n\
        #[no_mangle]\n\
        pub extern \"C\" fn bc_probe(k: u32, v: u32) -> u32 {\n\
            let mut a = [0u32; 4];\n\
            let n = fill(&mut a, 7);\n\
            check(a.as_mut_ptr() as usize, k as usize);\n\
            let m = { let mut b = [0u32; 4]; fill(&mut b, v) };\n\
            let back = unsafe { *(k as usize as *const u32) };\n\
            back * 100 + n + m\n\
        }\n\
        #[no_mangle]\n\
        pub extern \"C\" fn stack_top(_k: u32, _v: u32) -> u32 {\n\
            let x = 0u32;\n\
            core::hint::black_box(&x) as *const u32 as u32\n\
        }\n";
    const SWEEP: &str = "const fs = require('fs');\n\
        const m = new WebAssembly.Module(fs.readFileSync(process.argv[2]));\n\
        const top = new WebAssembly.Instance(m, {}).exports.stack_top(0, 0);\n\
        const out = [];\n\
        for (let k = Math.max(0, top - 16384); k < top + 4096; k += 4) {\n\
          const f = new WebAssembly.Instance(m, {}).exports.bc_probe;\n\
          try { out.push([k, f(k, 9)]); }\n\
          catch (e) { if (!(e instanceof WebAssembly.RuntimeError)) throw e; }\n\
        }\n\
        process.stdout.write(JSON.stringify(out));\n";
    let dir = std::env::temp_dir().join(format!("rcl2_wasm32_bits_{}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("temp dir");
    std::fs::write(dir.join("sweep.js"), SWEEP).expect("write sweep");
    for opt in ["0", "1", "2", "3"] {
        let name = format!("bc_o{opt}");
        let level = format!("-Copt-level={opt}");
        compile_wasm32_case(&tools, &dir, &name, SOURCE, &[&level])
            .unwrap_or_else(|stderr| panic!("{name}: compile failed:\n{stderr}"));
        let output = Command::new(&tools.node)
            .arg(dir.join("sweep.js"))
            .arg(dir.join(format!("{name}.wasm")))
            .output()
            .expect("failed to spawn node");
        assert!(
            output.status.success(),
            "{name}: sweep failed: {}",
            String::from_utf8_lossy(&output.stderr)
        );
        let passed: Vec<(u32, u32)> = serde_json::from_slice(&output.stdout).expect("sweep JSON");
        assert!(
            !passed.is_empty(),
            "{name}: no k near the stack top passed the check; the sweep missed `a`"
        );
        for (k, r) in passed {
            assert_eq!(
                r, 716,
                "{name}: bc_probe({k}, 9) = {r}; `b` took `a`'s bytes"
            );
        }
    }
    let _ = std::fs::remove_dir_all(&dir);
}

/// A canonical MIR bounds check whose failure would trap (`panic=abort`)
/// runs the program's `#[panic_handler]` with core's real
/// `panic_bounds_check(index, len)` payload and caller location, as LLVM's
/// module does: the handler in `support/wasm32_bounds_panic/hook.rs` records
/// the location, the message's kind and an FNV-1a hash of its formatted
/// text, and `drive.mjs` replays one call sequence on both modules, comparing
/// every result and observation. A generic trap would skip the handler (every
/// observation stays zero), which is why the native lanes refuse this edge
/// as `[TCG-ASSERT-PANIC]`; wasm32 lowers it to the genuine raise instead.
#[test]
fn wasm32_bounds_check_panic_runs_the_handler_like_llvm() {
    let Some(tools) = tools("wasm32_bounds_check_panic_runs_the_handler_like_llvm") else {
        return;
    };
    let support = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/support/wasm32_bounds_panic");
    let source = support.join("hook.rs");
    let dir = std::env::temp_dir().join(format!("rcl2_wasm32_bounds_{}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("temp dir");
    let backend = backend_artifact_support::current_test_backend();
    for opt in ["0", "1", "2", "3"] {
        let flags = vec![format!("-Copt-level={opt}")];
        let (oracle, candidate) = (
            dir.join(format!("o{opt}.llvm.wasm")),
            dir.join(format!("o{opt}.trust_cg.wasm")),
        );
        compile(&tools, &source, "cdylib", &flags, &[], None, &oracle);
        compile(
            &tools,
            &source,
            "cdylib",
            &flags,
            &[],
            Some(backend.as_path()),
            &candidate,
        );
        let output = Command::new(&tools.node)
            .arg(support.join("drive.mjs"))
            .arg(&oracle)
            .arg(&candidate)
            .output()
            .expect("failed to spawn node");
        let stdout = String::from_utf8_lossy(&output.stdout);
        assert!(
            output.status.success(),
            "-Copt-level={opt}: the panic handler's observations differ from LLVM's:\n{stdout}{}",
            String::from_utf8_lossy(&output.stderr)
        );
        // The oracle's handler ran once per failed check: the comparison
        // observed real panics, not an all-zero state.
        assert!(
            stdout.contains("disagreements=0 handler_runs=6"),
            "-Copt-level={opt}: unexpected handler runs:\n{stdout}"
        );
    }
    let _ = std::fs::remove_dir_all(&dir);
}

/// The number of functions `module` DEFINES whose wasm type has more than one
/// result. LLVM's wasm32 modules define none; this backend's object lane
/// defines one per internal entry it kept (`support/wasm32_internal_abi`).
fn multi_value_definitions(module: &[u8]) -> usize {
    fn uleb(b: &[u8], at: &mut usize) -> usize {
        let (mut value, mut shift) = (0usize, 0);
        loop {
            let byte = b[*at];
            *at += 1;
            value |= usize::from(byte & 0x7f) << shift;
            if byte & 0x80 == 0 {
                return value;
            }
            shift += 7;
        }
    }
    fn skip_limits(b: &[u8], at: &mut usize) {
        let flags = b[*at];
        *at += 1;
        uleb(b, at);
        if flags & 1 != 0 {
            uleb(b, at);
        }
    }
    assert_eq!(&module[..8], b"\0asm\x01\0\0\0", "not a wasm module");
    let mut at = 8;
    let mut results: Vec<usize> = Vec::new();
    let mut multi = 0;
    while at < module.len() {
        let id = module[at];
        at += 1;
        let size = uleb(module, &mut at);
        let end = at + size;
        match id {
            1 => {
                for _ in 0..uleb(module, &mut at) {
                    assert_eq!(module[at], 0x60, "a non-function type");
                    at += 1;
                    let params = uleb(module, &mut at);
                    at += params;
                    let count = uleb(module, &mut at);
                    at += count;
                    results.push(count);
                }
            }
            // Imported functions take indices but define nothing.
            2 => {
                for _ in 0..uleb(module, &mut at) {
                    let len = uleb(module, &mut at);
                    at += len;
                    let len = uleb(module, &mut at);
                    at += len;
                    let kind = module[at];
                    at += 1;
                    match kind {
                        0 => {
                            uleb(module, &mut at);
                        }
                        1 => {
                            at += 1;
                            skip_limits(module, &mut at);
                        }
                        2 => skip_limits(module, &mut at),
                        3 => at += 2,
                        other => panic!("unknown import kind {other}"),
                    }
                }
            }
            3 => {
                for _ in 0..uleb(module, &mut at) {
                    let ty = uleb(module, &mut at);
                    multi += usize::from(results[ty] > 1);
                }
            }
            _ => {}
        }
        at = end;
    }
    multi
}

/// The internal multi-value ABI against LLVM. `support/wasm32_internal_abi/
/// probe.rs` returns pairs and `i128`s from crate-private functions reached
/// by direct calls, mutual recursion, function pointers (a static's, a
/// `black_box`ed one, one compared by address), a `dyn` trait call and a
/// closure. Every configuration agrees with LLVM's module export by export
/// (`compare.mjs`), and the linked module of this backend defines
/// multi-value functions exactly where the internal ABI applies: at `-O2` in
/// one object, and at `-O2` with one object per function (`batch-cgu=0`,
/// whose calls cross objects), but not at `-O0` or in a session that
/// withholds the `multivalue` feature (`-C target-cpu=mvp`,
/// `-C target-feature=-multivalue`). LLVM's module defines none in any
/// configuration, so the count is this backend's internal entries.
#[test]
fn wasm32_internal_abi_agrees_with_llvm_and_is_used_where_admitted() {
    let Some(tools) = tools("wasm32_internal_abi_agrees_with_llvm_and_is_used_where_admitted")
    else {
        return;
    };
    let source =
        Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/support/wasm32_internal_abi/probe.rs");
    let dir = std::env::temp_dir().join(format!("rcl2_wasm32_mv_{}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("temp dir");
    let backend = backend_artifact_support::current_test_backend();
    // (label, codegen flags, backend knobs, internal entries expected:
    // `None` leaves the count to rustc's partitioning, as calls between
    // codegen units keep the C form).
    let configurations: [(&str, &[&str], &[&str], Option<bool>); 7] = [
        ("o0", &["-Copt-level=0"], &["no-proof-certs"], Some(false)),
        ("o1", &["-Copt-level=1"], &["no-proof-certs"], Some(true)),
        ("o2", &["-Copt-level=2"], &["no-proof-certs"], Some(true)),
        (
            "o2-per-function",
            &["-Copt-level=2"],
            &["no-proof-certs", "batch-cgu=0"],
            Some(true),
        ),
        (
            "o3-cgu4",
            &["-Copt-level=3", "-Ccodegen-units=4"],
            &["no-proof-certs"],
            None,
        ),
        (
            "o2-mvp",
            &["-Copt-level=2", "-Ctarget-cpu=mvp"],
            &["no-proof-certs"],
            Some(false),
        ),
        (
            "o2-no-multivalue",
            &["-Copt-level=2", "-Ctarget-feature=-multivalue"],
            &["no-proof-certs"],
            Some(false),
        ),
    ];
    for (label, flags, knobs, used) in configurations {
        let flags: Vec<String> = flags.iter().map(|f| (*f).to_owned()).collect();
        let (oracle, candidate) = (
            dir.join(format!("{label}.llvm.wasm")),
            dir.join(format!("{label}.trust_cg.wasm")),
        );
        compile(&tools, &source, "cdylib", &flags, &[], None, &oracle);
        compile_with_knobs(
            &tools,
            &source,
            "cdylib",
            &flags,
            &[],
            Some(backend.as_path()),
            knobs,
            &candidate,
        );
        let output = Command::new(&tools.node)
            .arg(fixture("compare.mjs"))
            .arg(&oracle)
            .arg(&candidate)
            .output()
            .expect("failed to spawn node");
        let stdout = String::from_utf8_lossy(&output.stdout);
        assert!(
            output.status.success(),
            "{label}: the internal-ABI probe disagrees with LLVM:\n{stdout}{}",
            String::from_utf8_lossy(&output.stderr)
        );
        assert!(
            stdout.contains("exports=3 "),
            "{label}: expected all three exports compared:\n{stdout}"
        );
        let llvm = multi_value_definitions(&std::fs::read(&oracle).expect("oracle module"));
        let ours = multi_value_definitions(&std::fs::read(&candidate).expect("candidate module"));
        assert_eq!(
            llvm, 0,
            "{label}: LLVM's module defines multi-value functions"
        );
        match used {
            Some(true) => assert!(
                ours > 0,
                "{label}: no internal entry in the linked module; the internal ABI was not used"
            ),
            Some(false) => assert_eq!(
                ours, 0,
                "{label}: the linked module defines {ours} multi-value functions"
            ),
            None => {}
        }
    }
    let _ = std::fs::remove_dir_all(&dir);
}

/// The trust-ir module the wasm32 lane receives for `source` (the
/// `trace-ty` print after word legalization), with this backend's `knobs`
/// and the codegen `flags`.
fn wasm32_lane_ir(
    tools: &Tools,
    source: &Path,
    flags: &[&str],
    knobs: &[&str],
    out: &Path,
) -> String {
    let mut backend_arg = OsString::from("-Zcodegen-backend=");
    backend_arg.push(backend_artifact_support::current_test_backend());
    let mut linker = OsString::from("linker=");
    linker.push(&tools.wasm_ld);
    let output = toolchain_support::rustc_command()
        .arg(backend_arg)
        .arg(toolchain_support::backend_knobs_arg(knobs))
        .arg("--sysroot")
        .arg(&tools.sysroot)
        .args([
            "--target",
            TARGET,
            "--crate-type",
            "cdylib",
            "-Cpanic=abort",
            "-C",
        ])
        .arg(linker)
        .args(flags)
        .arg("-o")
        .arg(out)
        .arg(source)
        .output()
        .expect("failed to spawn the build compiler");
    let stderr = String::from_utf8_lossy(&output.stderr).into_owned();
    assert!(
        output.status.success(),
        "wasm32 compile of {} {flags:?} {knobs:?} failed:\n{stderr}",
        source.display()
    );
    stderr
}

/// One GEP of a `trace-ty` print: its text after `gep ` and the constant its
/// index is (when a `const` of the same function defines it).
type TracedGep = (String, Option<i128>);

/// The GEPs of each function of a `trace-ty` print, by the function's
/// symbol.
fn geps_by_function(ir: &str) -> Vec<(String, Vec<TracedGep>)> {
    let mut functions: Vec<(String, Vec<&str>)> = Vec::new();
    for line in ir.lines() {
        if let Some(rest) = line.strip_prefix("fn @") {
            let name = rest.split('(').next().unwrap_or(rest).to_owned();
            functions.push((name, Vec::new()));
        } else if let Some((_, body)) = functions.last_mut() {
            body.push(line.trim());
        }
    }
    functions
        .into_iter()
        .map(|(name, body)| {
            let constant = |value: &str| {
                body.iter().find_map(|line| {
                    let rest = line.strip_prefix(value)?.strip_prefix(" = const ")?;
                    rest.split_whitespace().nth(1)?.parse::<i128>().ok()
                })
            };
            let geps = body
                .iter()
                .filter_map(|line| {
                    let (_, gep) = line.split_once(" = gep ")?;
                    let index = gep.rsplit(", ").next()?.trim();
                    Some((gep.to_owned(), constant(index)))
                })
                .collect();
            (name, geps)
        })
        .collect()
}

/// At O1 and above the bridge spells exactly the constant-offset addresses
/// Rust guarantees in bounds as `gep inbounds u8 base, [k]` with a constant
/// `k >= 0` (`src/wasm32_inbounds.rs`), so the lane may fold `k` into a
/// memarg offset under the GEP's no-wrap premise: each kind the projection
/// corpus exercises gets one, and `wrapping_add`, integer address
/// arithmetic and `ptr::add` keep their integer chains. At O0, and with the
/// `no-wasm32-place-gep` kill switch, the bridge emits no GEP at all (native
/// targets never take the path; their identity is checked on the built
/// objects, not here). The level is the one the wasm lane runs at: the
/// bridge's `opt-level` knob overrides `-C opt-level` for the GEPs exactly as
/// it does for the lane, so `-Copt-level=2` with `opt-level=0` emits none and
/// `-Copt-level=0` with `opt-level=2` emits them.
#[test]
fn wasm32_in_bounds_addresses_are_geps_only_at_o1_and_above() {
    let Some(tools) = tools("wasm32_in_bounds_addresses_are_geps_only_at_o1_and_above") else {
        return;
    };
    let source = fixture("r15-bridge-place-projections.rs");
    let dir = std::env::temp_dir().join(format!("rcl2_wasm32_geps_{}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("temp dir");
    let traced = ["no-proof-certs", "trace-ty"];
    for (label, flags, knobs) in [
        ("o0", &["-Copt-level=0"][..], &traced[..]),
        (
            "o2-kill-switch",
            &["-Copt-level=2"][..],
            &["no-proof-certs", "trace-ty", "no-wasm32-place-gep"][..],
        ),
        (
            "o2-backend-o0",
            &["-Copt-level=2"][..],
            &["no-proof-certs", "trace-ty", "opt-level=0"][..],
        ),
    ] {
        let ir = wasm32_lane_ir(
            &tools,
            &source,
            flags,
            knobs,
            &dir.join(format!("{label}.wasm")),
        );
        assert!(ir.contains("fn @"), "{label}: no trace-ty module print");
        let geps: usize = geps_by_function(&ir).iter().map(|(_, g)| g.len()).sum();
        assert_eq!(geps, 0, "{label}: the bridge emitted {geps} GEPs");
    }
    let backend_o2 = ["no-proof-certs", "trace-ty", "opt-level=2"];
    for (level, knobs) in [
        ("-Copt-level=1", &traced[..]),
        ("-Copt-level=2", &traced[..]),
        ("-Copt-level=3", &traced[..]),
        ("-Copt-level=0", &backend_o2[..]),
    ] {
        let ir = wasm32_lane_ir(&tools, &source, &[level], knobs, &dir.join("on.wasm"));
        let level = format!("{level} with knobs `{}`", knobs.join(" "));
        let functions = geps_by_function(&ir);
        let geps_of = |needle: &str| -> Vec<&TracedGep> {
            functions
                .iter()
                .filter(|(name, _)| name.contains(needle))
                .flat_map(|(_, geps)| geps)
                .collect()
        };
        for (name, geps) in &functions {
            for (gep, constant) in geps {
                assert!(
                    gep.starts_with("inbounds u8, "),
                    "{level}: `{name}` has a GEP that is not a byte GEP: {gep}"
                );
                assert!(
                    constant.is_some_and(|k| (1..=i128::from(i32::MAX)).contains(&k)),
                    "{level}: `{name}`'s GEP index is not a constant in 1..=i32::MAX: {gep}"
                );
            }
        }
        // Where the corpus keeps a kind in a function of its own, that
        // function gets a GEP: fields through `&`, `&mut` and a raw pointer,
        // nested fields, front `ConstantIndex` projections of an array place
        // through `&`, `&mut` and a raw pointer, enum variant fields, packed
        // and zero-sized fields, a field after a runtime index, a hidden
        // return buffer's and a reference's whole-aggregate copy, and a
        // vtable slot.
        for kind in [
            "read_ref",
            "4bump",
            "read_raw",
            "6nested",
            "nested_mut",
            "11const_elems",
            "const_elem_field",
            "const_elem_mut",
            "const_elem_raw",
            "7variant",
            "packed_ref",
            "packed_raw",
            "zst_fields",
            "4pick",
            "make_big",
            "copy_through",
            "dyn_call",
        ] {
            assert!(
                !geps_of(kind).is_empty(),
                "{level}: no GEP in the function `{kind}`"
            );
        }
        // The negative controls keep their integer chains.
        for control in ["wrapping_round_trip", "integer_address", "pointer_add"] {
            assert!(
                geps_of(control).is_empty(),
                "{level}: `{control}` must keep its integer chain, got {:?}",
                geps_of(control)
            );
        }
    }
    let _ = std::fs::remove_dir_all(&dir);
}

/// What a linked wasm32 module's sections say, read with this test's own
/// decoder: the defined function bodies (local declarations through `end`),
/// the number of imported functions, the function exports and the `name`
/// section's function names.
#[derive(Default)]
struct LinkedSections {
    func_imports: usize,
    bodies: Vec<Vec<u8>>,
    exports: std::collections::BTreeMap<String, usize>,
    names: std::collections::BTreeMap<usize, String>,
}

fn linked_sections(module: &[u8]) -> LinkedSections {
    fn uleb(b: &[u8], at: &mut usize) -> usize {
        let (mut value, mut shift) = (0usize, 0);
        loop {
            let byte = b[*at];
            *at += 1;
            value |= usize::from(byte & 0x7f) << shift;
            if byte & 0x80 == 0 {
                return value;
            }
            shift += 7;
        }
    }
    fn name(b: &[u8], at: &mut usize) -> String {
        let len = uleb(b, at);
        let s = String::from_utf8(b[*at..*at + len].to_vec()).expect("UTF-8 name");
        *at += len;
        s
    }
    fn skip_limits(b: &[u8], at: &mut usize) {
        let flags = b[*at];
        *at += 1;
        uleb(b, at);
        if flags & 1 != 0 {
            uleb(b, at);
        }
    }
    assert_eq!(&module[..8], b"\0asm\x01\0\0\0", "not a wasm module");
    let mut out = LinkedSections::default();
    let mut at = 8;
    while at < module.len() {
        let id = module[at];
        at += 1;
        let size = uleb(module, &mut at);
        let end = at + size;
        match id {
            0 if name(module, &mut at) == "name" => {
                while at < end {
                    let sub = module[at];
                    at += 1;
                    let len = uleb(module, &mut at);
                    let sub_end = at + len;
                    if sub == 1 {
                        for _ in 0..uleb(module, &mut at) {
                            let index = uleb(module, &mut at);
                            out.names.insert(index, name(module, &mut at));
                        }
                    }
                    at = sub_end;
                }
            }
            2 => {
                for _ in 0..uleb(module, &mut at) {
                    name(module, &mut at);
                    name(module, &mut at);
                    let kind = module[at];
                    at += 1;
                    match kind {
                        0 => {
                            uleb(module, &mut at);
                            out.func_imports += 1;
                        }
                        1 => {
                            at += 1;
                            skip_limits(module, &mut at);
                        }
                        2 => skip_limits(module, &mut at),
                        3 => at += 2,
                        other => panic!("unknown import kind {other}"),
                    }
                }
            }
            7 => {
                for _ in 0..uleb(module, &mut at) {
                    let export = name(module, &mut at);
                    let kind = module[at];
                    at += 1;
                    let index = uleb(module, &mut at);
                    if kind == 0 {
                        out.exports.insert(export, index);
                    }
                }
            }
            10 => {
                for _ in 0..uleb(module, &mut at) {
                    let len = uleb(module, &mut at);
                    out.bodies.push(module[at..at + len].to_vec());
                    at += len;
                }
            }
            _ => {}
        }
        at = end;
    }
    out
}

/// The object composition of the wasm32 lane at O1 and above, on the
/// corpus crate `r16-bridge-sections.rs` (whose execution the corpus
/// differential compares with LLVM at O0 to O3), linked by `wasm-ld`, at O0
/// and O2:
///
/// * the functions of one codegen unit share the global of each constant
///   allocation they reference: the byte-string table three functions read
///   is in the O2 module once and in the O0 module (one copy per function)
///   more often;
/// * the objects name crate-private functions for the debugger without the
///   crate mark: the O2 module's `name` section has no `.tcg.crate.`, the O0
///   module's does, and both modules export exactly the crate's
///   `#[no_mangle]` functions under their own names, each a distinct function;
/// * identical bodies fold: at O2 the body the macro stamps out for `isize`
///   is exactly a forwarder (`local.get 0; local.get 1; call; end`) to the
///   one it stamps out for `i32`, named for the debugger, and at O0 no body
///   is a forwarder.
///
/// The debug names, the forwarder shape and the constant sharing are
/// provisional surfaces pending owner sign-off (docs/wasm32_perf_roadmap.md,
/// "Pending owner sign-off", round 16 stage B); this test follows them if
/// they change and is not a contract for their shape.
#[test]
fn wasm32_object_composition_shares_constants_names_and_folds_at_o1_and_above() {
    let test = "wasm32_object_composition_shares_constants_names_and_folds_at_o1_and_above";
    let Some(tools) = tools(test) else {
        return;
    };
    let source = std::fs::read_to_string(fixture("r16-bridge-sections.rs")).expect("corpus crate");
    let dir = std::env::temp_dir().join(format!("rcl2_wasm32_sections_{}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("temp dir");
    let exports: std::collections::BTreeSet<String> = source
        .lines()
        .filter_map(|l| l.trim().strip_prefix("pub extern \"C\" fn "))
        .filter_map(|l| l.split('(').next())
        .filter(|n| !n.starts_with('$'))
        .map(str::to_owned)
        .chain(
            ["sweep_i32", "sweep_isize", "sweep_u32", "sweep_usize"]
                .into_iter()
                .map(str::to_owned),
        )
        .collect();
    let table: &[u8] = b"tcg-shared-constant: ";
    let copies = |m: &[u8]| m.windows(table.len()).filter(|w| *w == table).count();
    let mut linked = Vec::new();
    for (level, flags) in [
        ("o0", &["-Copt-level=0"][..]),
        ("o2", &["-Copt-level=2"][..]),
    ] {
        let name = format!("sections_{level}");
        if let Err(stderr) = compile_wasm32_case(&tools, &dir, &name, &source, flags) {
            panic!("{name}: the crate must compile:\n{stderr}");
        }
        let module = std::fs::read(dir.join(format!("{name}.wasm"))).expect("module");
        let sections = linked_sections(&module);
        let got: std::collections::BTreeSet<String> = sections.exports.keys().cloned().collect();
        assert_eq!(got, exports, "{level}: the exports");
        let distinct: std::collections::BTreeSet<usize> =
            sections.exports.values().copied().collect();
        assert_eq!(
            distinct.len(),
            exports.len(),
            "{level}: two exports share a function"
        );
        let marked = sections.names.values().any(|n| n.contains(".tcg.crate."));
        assert_eq!(marked, level == "o0", "{level}: names {:?}", sections.names);
        linked.push((level, copies(&module), sections));
    }
    let _ = std::fs::remove_dir_all(&dir);
    let (o0, o2) = (&linked[0], &linked[1]);
    assert_eq!(o2.1, 1, "O2: the shared table is in the module once");
    assert!(o0.1 > 1, "O0: one copy per function ({} copies)", o0.1);
    // The callee of a body that is exactly `local.get 0; local.get 1;
    // call <callee>; end` with no locals.
    let forwarder_to = |body: &[u8]| -> Option<usize> {
        let [0, 0x20, 0, 0x20, 1, 0x10, imm @ .., 0x0b] = body else {
            return None;
        };
        let (mut value, mut shift) = (0usize, 0);
        for (i, byte) in imm.iter().enumerate() {
            value |= usize::from(byte & 0x7f) << shift;
            shift += 7;
            if byte & 0x80 == 0 {
                return (i + 1 == imm.len()).then_some(value);
            }
        }
        None
    };
    let index_named = |s: &LinkedSections, suffix: &str| -> usize {
        *s.names
            .iter()
            .find(|(_, n)| n.ends_with(suffix))
            .unwrap_or_else(|| panic!("no function named *{suffix}: {:?}", s.names))
            .0
    };
    let sections = &o2.2;
    let isize_helper = index_named(sections, "9mix_isize");
    let i32_helper = index_named(sections, "7mix_i32");
    let body = &sections.bodies[isize_helper - sections.func_imports];
    assert_eq!(
        forwarder_to(body),
        Some(i32_helper),
        "O2: mix_isize must forward to mix_i32: {body:02x?}"
    );
    assert!(
        o0.2.bodies.iter().all(|b| forwarder_to(b).is_none()),
        "O0: no body is a forwarder"
    );
}
