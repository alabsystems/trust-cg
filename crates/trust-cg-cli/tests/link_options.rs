// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! CLI link options, classified link failures and runtime-dependency output.
//!
//! Refusal and manifest tests run on every host. Link-and-inspect tests need
//! a host C driver that links native AArch64 objects, so they run only on
//! AArch64 macOS and Linux.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

use trust_cg_codegen::pipeline::encode_tmbc;
use trust_ir::{BinOp, Module, Ty};
use trust_ir_build::ModuleBuilder;

fn trust_cg(directory: &Path, args: &[&str]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_trust-cg"))
        .arg("--permit-unlicensed")
        .current_dir(directory)
        .args(args)
        .output()
        .expect("run trust-cg")
}

/// Write `module` as TMBC. A module with an FFI boundary must pin the
/// target it is linked for (`TargetInfoRequired`, the WS7.3 ingestion
/// admission); one that pins none is given the host's AArch64 target here,
/// the one every link test below links for. A module without a boundary,
/// or one that pins its own target, is written as it is.
fn write_module(directory: &Path, name: &str, module: &Module) -> PathBuf {
    let path = directory.join(name);
    let mut module = module.clone();
    if module.target_info.is_none() && module.requires_target_info() {
        module.target_info = Some(trust_ir::TargetInfo {
            triple: if cfg!(target_os = "macos") {
                "aarch64-apple-darwin"
            } else {
                "aarch64-unknown-linux-gnu"
            }
            .into(),
            pointer_size: 8,
            endianness: trust_ir::Endianness::Little,
            abi: None,
            struct_passing: trust_ir::StructPassingPolicy::NativeC,
        });
    }
    fs::write(&path, encode_tmbc(&module).unwrap()).unwrap();
    path
}

/// `tcg_cli_div(a, b) = a / b` on i128: lowers to the `__divti3` helper.
fn divide_module() -> Module {
    let mut mb = ModuleBuilder::new("tcg_cli_divide");
    let ty = mb.add_func_type(vec![Ty::I128, Ty::I128], vec![Ty::I128]);
    let mut fb = mb.function("tcg_cli_div", ty);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let a = fb.add_block_param(entry, Ty::I128);
    let b = fb.add_block_param(entry, Ty::I128);
    let quotient = fb.binop(BinOp::SDiv, Ty::I128, a, b);
    fb.ret(vec![quotient]);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

fn stderr(output: &Output) -> String {
    String::from_utf8_lossy(&output.stderr).into_owned()
}

#[test]
fn link_options_under_compile_only_are_refused_before_any_output() {
    let directory = tempfile::tempdir().unwrap();
    write_module(directory.path(), "a.tmbc", &divide_module());
    for (flags, named) in [
        (vec!["--shared"], "--shared"),
        (vec!["-static"], "--static"),
        (vec!["--rpath", "/opt/lib"], "--rpath"),
        (vec!["-Wl,-z,text"], "-Wl"),
    ] {
        let mut args = vec!["-c"];
        args.extend(flags.iter().copied());
        args.push("a.tmbc");
        let output = trust_cg(directory.path(), &args);
        assert!(!output.status.success(), "{args:?}");
        let text = stderr(&output);
        assert!(
            text.contains(&format!("{named}: -c compiles objects only")),
            "{args:?}: {text}"
        );
        assert!(!directory.path().join("a.o").exists(), "{args:?}");
    }
}

#[test]
fn invalid_link_options_are_refused_before_inputs_are_read() {
    let directory = tempfile::tempdir().unwrap();
    fs::write(directory.path().join("a.tmbc"), b"not bitcode").unwrap();
    for (args, diagnostic) in [
        (
            vec!["--soname", "libx.so", "a.tmbc"],
            "--soname: only a shared object",
        ),
        (
            vec!["-shared", "-static", "a.tmbc"],
            "--static: a shared object cannot be linked statically",
        ),
        (
            vec!["--pie", "--static", "a.tmbc"],
            "--pie: a static position-independent",
        ),
        (
            vec!["-Wl,-soname,libx.so", "a.tmbc"],
            "is controlled by the trust-cg option `--soname`",
        ),
        (vec!["-Wall", "a.tmbc"], "-Wall: only the -Wl"),
        (
            vec![
                "--target",
                "aarch64-unknown-linux-gnu",
                "-Wl,-z,execstack",
                "a.tmbc",
            ],
            "-Wl,-z,execstack: an executable stack is refused",
        ),
        (
            vec![
                "--target",
                "aarch64-unknown-linux-gnu",
                "-Wl,-z,force-bti",
                "a.tmbc",
            ],
            "-Wl,-z,force-bti: [TCG-LINK-BTI-PAC] `-z force-bti` is refused",
        ),
        (
            vec![
                "--target",
                "aarch64-unknown-linux-gnu",
                "-shared",
                "-Wl,-zpac-plt",
                "a.tmbc",
            ],
            "-Wl,-zpac-plt: [TCG-LINK-BTI-PAC] `-z pac-plt` is refused",
        ),
        (
            vec![
                "--target",
                "aarch64-unknown-linux-gnu",
                "-Wl,-z,bti-report=error",
                "a.tmbc",
            ],
            "-Wl,-z,bti-report=error: [TCG-LINK-BTI-PAC] `-z bti-report=error` is refused",
        ),
        (
            vec!["-Wl,--gc-sections,-z", "a.tmbc"],
            "`-z` needs its keyword in the same -Wl group",
        ),
        (
            vec!["--target", "aarch64-apple-darwin", "--static", "a.tmbc"],
            "--static: Darwin does not support static executables",
        ),
    ] {
        let output = trust_cg(directory.path(), &args);
        let text = stderr(&output);
        assert!(!output.status.success(), "{args:?}");
        assert!(text.contains(diagnostic), "{args:?}: {text}");
        assert!(
            !text.contains("failed to read"),
            "{args:?} validated too late: {text}"
        );
    }
}

#[test]
fn emit_runtime_deps_writes_one_classified_manifest_per_object() {
    let directory = tempfile::tempdir().unwrap();
    write_module(directory.path(), "a.tmbc", &divide_module());
    let output = trust_cg(
        directory.path(),
        &[
            "-c",
            "--target",
            "aarch64-unknown-linux-gnu",
            "--emit-runtime-deps",
            "deps.json",
            "-o",
            "a.o",
            "a.tmbc",
        ],
    );
    assert!(output.status.success(), "{}", stderr(&output));
    let report: serde_json::Value =
        serde_json::from_slice(&fs::read(directory.path().join("deps.json")).unwrap()).unwrap();
    assert_eq!(report["schema"], "trust-cg.runtime-dependencies.v1");
    let objects = report["objects"].as_array().unwrap();
    assert_eq!(objects.len(), 1);
    assert_eq!(objects[0]["input"], "a.tmbc");
    assert_eq!(objects[0]["object"], "a.o");
    let manifest = &objects[0]["manifest"];
    assert_eq!(manifest["format"], "elf");
    assert_eq!(manifest["undefined_symbol_count"], 1);
    assert_eq!(manifest["providers"][0]["provider"], "compiler_runtime");
    assert_eq!(manifest["providers"][0]["symbols"][0]["name"], "__divti3");
}

#[test]
fn metrics_include_the_runtime_manifest() {
    let directory = tempfile::tempdir().unwrap();
    write_module(directory.path(), "a.tmbc", &divide_module());
    let output = trust_cg(
        directory.path(),
        &[
            "-c",
            "--target",
            "aarch64-apple-darwin",
            "--metrics",
            "a.tmbc",
        ],
    );
    assert!(output.status.success(), "{}", stderr(&output));
    let text = stderr(&output);
    assert!(text.contains("\"runtime_dependencies\""), "{text}");
    assert!(text.contains("\"___divti3\""), "{text}");
    assert!(text.contains("\"c_name\": \"__divti3\""), "{text}");
}

#[test]
fn wasm_lane_refuses_link_and_runtime_manifest_options() {
    let directory = tempfile::tempdir().unwrap();
    write_module(directory.path(), "a.tmbc", &divide_module());
    let output = trust_cg(
        directory.path(),
        &[
            "--target",
            "wasm32",
            "--shared",
            "--emit-runtime-deps",
            "deps.json",
            "a.tmbc",
        ],
    );
    assert!(!output.status.success());
    let text = stderr(&output);
    assert!(
        text.contains("--shared: system-link options do not apply"),
        "{text}"
    );
    assert!(text.contains("--emit-runtime-deps:"), "{text}");
    assert!(!directory.path().join("deps.json").exists());
}

#[cfg(all(
    target_arch = "aarch64",
    any(target_os = "macos", all(target_os = "linux", target_env = "gnu"))
))]
mod native {
    use super::*;

    /// `main` returns the result of an undefined `tcg_cli_missing`.
    fn calls_missing_module() -> Module {
        // `tcg_cli_missing` is an FFI boundary: the module pins the host
        // target it is linked for (`TargetInfoRequired`; WS7.3 admission).
        let mut mb = ModuleBuilder::new_with_target_info(
            "tcg_cli_missing_ref",
            trust_ir::TargetInfo {
                triple: if cfg!(target_os = "macos") {
                    "aarch64-apple-darwin"
                } else {
                    "aarch64-unknown-linux-gnu"
                }
                .into(),
                pointer_size: 8,
                endianness: trust_ir::Endianness::Little,
                abi: None,
                struct_passing: trust_ir::StructPassingPolicy::NativeC,
            },
        );
        let ty = mb.add_func_type(vec![], vec![Ty::I32]);
        let missing = mb.declare_function("tcg_cli_missing", ty);
        let mut fb = mb.function("main", ty);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        let value = fb.call(missing, vec![]);
        fb.ret(vec![value]);
        fb.build();
        mb.build().expect("ModuleBuilder::build: test fixture")
    }

    /// A strong `tcg_cli_dup`, plus `main` calling it when `with_main`.
    fn duplicate_module(with_main: bool) -> Module {
        let mut mb = ModuleBuilder::new("tcg_cli_dup");
        let ty = mb.add_func_type(vec![], vec![Ty::I32]);
        let dup = {
            let mut fb = mb.function("tcg_cli_dup", ty);
            let entry = fb.create_block();
            fb.switch_to_block(entry);
            let value = fb.iconst(Ty::I32, 3);
            fb.ret(vec![value]);
            fb.build()
        };
        if with_main {
            let mut fb = mb.function("main", ty);
            let entry = fb.create_block();
            fb.switch_to_block(entry);
            let value = fb.call(dup, vec![]);
            fb.ret(vec![value]);
            fb.build();
        }
        mb.build().expect("ModuleBuilder::build: test fixture")
    }

    #[test]
    fn undefined_symbol_link_failure_is_classified() {
        let directory = tempfile::tempdir().unwrap();
        write_module(directory.path(), "a.tmbc", &calls_missing_module());
        let output = trust_cg(directory.path(), &["-o", "prog", "a.tmbc"]);
        assert!(!output.status.success());
        let text = stderr(&output);
        assert!(text.contains("error[link:undefined-symbol]"), "{text}");
        assert!(text.contains("tcg_cli_missing`"), "{text}");
        assert!(
            text.contains("trust-cg: error: linker exited with status"),
            "{text}"
        );
        assert!(!directory.path().join("prog").exists());
    }

    #[test]
    fn duplicate_definition_across_inputs_is_classified() {
        let directory = tempfile::tempdir().unwrap();
        write_module(directory.path(), "a.tmbc", &duplicate_module(true));
        write_module(directory.path(), "b.tmbc", &duplicate_module(false));
        let output = trust_cg(directory.path(), &["-o", "prog", "a.tmbc", "b.tmbc"]);
        assert!(!output.status.success());
        let text = stderr(&output);
        assert!(text.contains("error[link:duplicate-symbol]"), "{text}");
        assert!(text.contains("tcg_cli_dup`"), "{text}");

        // Positive twin: the single definition links and runs.
        let output = trust_cg(directory.path(), &["-o", "prog", "a.tmbc"]);
        assert!(output.status.success(), "{}", stderr(&output));
        let status = Command::new(directory.path().join("prog"))
            .status()
            .unwrap();
        assert_eq!(status.code(), Some(3));
    }

    /// `--shared` produces a shared object (Mach-O MH_DYLIB / ELF ET_DYN).
    #[test]
    fn shared_output_is_a_shared_object() {
        let directory = tempfile::tempdir().unwrap();
        write_module(directory.path(), "a.tmbc", &divide_module());
        let (name, soname) = if cfg!(target_os = "macos") {
            ("libtcgcli.dylib", "@rpath/libtcgcli.dylib")
        } else {
            ("libtcgcli.so", "libtcgcli.so.1")
        };
        let output = trust_cg(
            directory.path(),
            &["-shared", "-soname", soname, "-o", name, "a.tmbc"],
        );
        assert!(output.status.success(), "{}", stderr(&output));
        assert!(stderr(&output).contains("(shared object)"));
        let bytes = fs::read(directory.path().join(name)).unwrap();
        if cfg!(target_os = "macos") {
            assert_eq!(&bytes[0..4], &[0xcf, 0xfa, 0xed, 0xfe]);
            assert_eq!(
                u32::from_le_bytes(bytes[12..16].try_into().unwrap()),
                6,
                "MH_DYLIB"
            );
        } else {
            assert_eq!(&bytes[0..4], b"\x7fELF");
            assert_eq!(u16::from_le_bytes([bytes[16], bytes[17]]), 3, "ET_DYN");
        }
        let embedded = String::from_utf8_lossy(&bytes);
        assert!(
            embedded.contains(soname),
            "the soname/install name is recorded"
        );
    }

    /// ld64 ad-hoc signs every arm64 output, and the CLI checks the result
    /// with the independent verifier before reporting success.
    #[cfg(target_os = "macos")]
    #[test]
    fn darwin_ld64_outputs_carry_a_verified_ad_hoc_signature() {
        use trust_cg_codegen::macho::codesign::{
            CS_ADHOC, CS_EXECSEG_MAIN_BINARY, CS_LINKER_SIGNED, verify_ad_hoc_signature,
        };
        let directory = tempfile::tempdir().unwrap();
        write_module(directory.path(), "a.tmbc", &duplicate_module(true));
        write_module(directory.path(), "b.tmbc", &divide_module());
        for (args, name, main_binary) in [
            (vec!["-o", "prog", "a.tmbc"], "prog", true),
            (
                vec!["-shared", "-o", "libtcgsig.dylib", "b.tmbc"],
                "libtcgsig.dylib",
                false,
            ),
        ] {
            let output = trust_cg(directory.path(), &args);
            assert!(output.status.success(), "{}", stderr(&output));
            let path = directory.path().join(name);
            let signature = verify_ad_hoc_signature(&fs::read(&path).unwrap()).unwrap();
            let code_directory = &signature.code_directory;
            assert_eq!(code_directory.flags, CS_ADHOC | CS_LINKER_SIGNED, "{name}");
            assert_eq!(code_directory.identifier, name);
            assert_eq!(
                code_directory.exec_segment.unwrap().flags & CS_EXECSEG_MAIN_BINARY != 0,
                main_binary,
                "{name}"
            );
            let verify = Command::new("codesign")
                .args(["--verify", "--strict"])
                .arg(&path)
                .output()
                .unwrap();
            assert!(verify.status.success(), "{}", stderr(&verify));
        }
        let status = Command::new(directory.path().join("prog"))
            .status()
            .unwrap();
        assert_eq!(status.code(), Some(3));
    }

    /// An ld64 output without its ad-hoc signature is refused by name and
    /// removed rather than left for Apple Silicon to kill at exec.
    #[cfg(target_os = "macos")]
    #[test]
    fn darwin_unsigned_ld64_output_is_refused_and_removed() {
        let directory = tempfile::tempdir().unwrap();
        write_module(directory.path(), "a.tmbc", &duplicate_module(true));
        let output = trust_cg(
            directory.path(),
            &["-Wl,-no_adhoc_codesign", "-o", "prog", "a.tmbc"],
        );
        assert!(!output.status.success());
        let text = stderr(&output);
        assert!(text.contains("error[link:code-signature]"), "{text}");
        assert!(text.contains("has no LC_CODE_SIGNATURE"), "{text}");
        assert!(text.contains("so it was removed"), "{text}");
        assert!(
            text.contains("the linked output failed its code-signature check"),
            "{text}"
        );
        assert!(!directory.path().join("prog").exists());
    }
}

/// Thread-local link controls. Local-exec TLS and GNU ld's TLS/non-TLS
/// symbol-type check are ELF concerns (Darwin reaches every thread-local
/// through a TLV descriptor), so these run on Linux AArch64 GNU hosts only.
#[cfg(all(target_arch = "aarch64", target_os = "linux", target_env = "gnu"))]
mod linux_tls {
    use super::*;
    use trust_ir::value::GlobalId;
    use trust_ir::{Constant, Global, Linkage, TlsModel, Visibility};

    /// An `i32` thread-local this module defines, holding `value`.
    fn thread_local(name: &str, value: i128) -> Global {
        Global {
            name: name.into(),
            ty: Ty::I32,
            mutable: true,
            initializer: Some(Constant::Int(value)),
            linkage: Linkage::External,
            tls: Some(TlsModel::LocalExec),
            align: None,
            section: None,
            visibility: Visibility::Default,
            retained: false,
        }
    }

    /// `tcg_cli_tls_bump()` adds 2 to the thread-local `tcg_cli_tls`
    /// (initially 40) and returns the new value, plus `main` returning
    /// `tcg_cli_tls_bump()` (42) when `with_main`. The module DEFINES the
    /// thread-local, so the executable relocation models (`static`, `pie`)
    /// address it with local-exec TLS (`R_AARCH64_TLSLE_ADD_TPREL_*`).
    pub(super) fn tls_counter_module(with_main: bool) -> Module {
        let mut mb = ModuleBuilder::new("tcg_cli_tls");
        mb.add_global(thread_local("tcg_cli_tls", 40));
        let ty = mb.add_func_type(vec![], vec![Ty::I32]);
        let bump = {
            let mut fb = mb.function("tcg_cli_tls_bump", ty);
            let entry = fb.create_block();
            fb.switch_to_block(entry);
            let address = fb.global_addr(GlobalId::new(0));
            let value = fb.load(Ty::I32, address);
            let two = fb.iconst(Ty::I32, 2);
            let bumped = fb.binop(BinOp::Add, Ty::I32, value, two);
            fb.store(Ty::I32, address, bumped);
            fb.ret(vec![bumped]);
            fb.build()
        };
        if with_main {
            let mut fb = mb.function("main", ty);
            let entry = fb.create_block();
            fb.switch_to_block(entry);
            let value = fb.call(bump, vec![]);
            fb.ret(vec![value]);
            fb.build();
        }
        mb.build().expect("ModuleBuilder::build: test fixture")
    }

    /// `main` returns `tcg_cli_tls_bump() + (tcg_cli_main_tls - 1000)` for an
    /// imported `tcg_cli_tls_bump` and its own thread-local
    /// `tcg_cli_main_tls` (1000): 42 when the library's thread-local and the
    /// executable's are distinct objects. A library that addressed its
    /// thread-local as if it lived in the executable's TLS block would read
    /// and bump `tcg_cli_main_tls` instead (1002 + 2 = 1004, exit 236).
    fn tls_user_module() -> Module {
        tls_user_module_calling("tcg_cli_tls_bump")
    }

    /// [`tls_user_module`] importing `bump` in place of `tcg_cli_tls_bump`.
    fn tls_user_module_calling(bump: &str) -> Module {
        let mut mb = ModuleBuilder::new("tcg_cli_tls_user");
        mb.add_global(thread_local("tcg_cli_main_tls", 1000));
        let ty = mb.add_func_type(vec![], vec![Ty::I32]);
        let bump = mb.declare_function(bump, ty);
        let mut fb = mb.function("main", ty);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        let bumped = fb.call(bump, vec![]);
        let address = fb.global_addr(GlobalId::new(0));
        let own = fb.load(Ty::I32, address);
        let sum = fb.binop(BinOp::Add, Ty::I32, bumped, own);
        let base = fb.iconst(Ty::I32, 1000);
        let result = fb.binop(BinOp::Sub, Ty::I32, sum, base);
        fb.ret(vec![result]);
        fb.build();
        mb.build().expect("ModuleBuilder::build: test fixture")
    }

    /// Local-exec TLS cannot be linked into a shared object. The `static`
    /// and `pie` relocation models address the thread-local this module
    /// defines with local-exec, and the CLI refuses that `-shared` link by
    /// name before the linker runs (GNU ld 2.42 would write the library; see
    /// `link_driver::local_exec_tls_refusals`); the module's two
    /// default-visibility definitions are refused beside it
    /// (`[TCG-LINK-PREEMPTIBLE-DEFINITION]`, ruling
    /// OD-SHARED-NON-PIC-DEFINITION-20261024). Positive twins: the same
    /// module linked as an executable runs, and compiled with the `pic`
    /// model (TLS descriptors) it links `-shared` and runs from an
    /// executable that has its own thread-local.
    #[test]
    fn local_exec_tls_in_a_shared_object_is_refused_by_name() {
        let directory = tempfile::tempdir().unwrap();
        let dir = directory.path();
        write_module(dir, "tls.tmbc", &tls_counter_module(false));
        for model in ["static", "pie"] {
            let output = trust_cg(
                dir,
                &[
                    "-shared",
                    "--relocation-model",
                    model,
                    "-o",
                    "libtcgtls.so",
                    "tls.tmbc",
                ],
            );
            assert!(!output.status.success(), "{model}");
            let text = stderr(&output);
            assert!(
                text.contains(
                    "trust-cg: error[link:tls-model-mismatch] `tcg_cli_tls` \
                     (R_AARCH64_TLSLE_ADD_TPREL_HI12): [TCG-LINK-TLS-MODEL] "
                ),
                "{model}: {text}"
            );
            for definition in ["tcg_cli_tls", "tcg_cli_tls_bump"] {
                assert!(
                    text.contains(&format!(
                        "trust-cg: error[link:non-pic-definition] `{definition}`: \
                         [TCG-LINK-PREEMPTIBLE-DEFINITION] "
                    )),
                    "{model} {definition}: {text}"
                );
            }
            assert_eq!(text.matches("error[link:").count(), 3, "{model}: {text}");
            assert!(
                text.contains("trust-cg: error: link inputs refused before the linker ran"),
                "{model}: {text}"
            );
            assert!(!text.contains("ld returned"), "{model}: {text}");
            assert!(!dir.join("libtcgtls.so").exists(), "{model}");
        }

        // Positive twin: local-exec is the executable's own model.
        write_module(dir, "prog.tmbc", &tls_counter_module(true));
        let output = trust_cg(dir, &["-o", "prog", "prog.tmbc"]);
        assert!(output.status.success(), "{}", stderr(&output));
        let status = Command::new(dir.join("prog")).status().unwrap();
        assert_eq!(status.code(), Some(42));

        // Positive twin: the shared-object model links and keeps the
        // library's thread-local distinct from the executable's.
        let output = trust_cg(
            dir,
            &[
                "-shared",
                "--relocation-model",
                "pic",
                "-o",
                "libtcgtls.so",
                "tls.tmbc",
            ],
        );
        assert!(output.status.success(), "{}", stderr(&output));
        write_module(dir, "user.tmbc", &tls_user_module());
        let rpath = dir.display().to_string();
        let output = trust_cg(
            dir,
            &[
                "-o",
                "user",
                "-L",
                ".",
                "-l",
                "tcgtls",
                "--rpath",
                &rpath,
                "user.tmbc",
            ],
        );
        assert!(output.status.success(), "{}", stderr(&output));
        let status = Command::new(dir.join("user")).status().unwrap();
        assert_eq!(status.code(), Some(42));
    }

    /// Names in `dir`, sorted: a refused link leaves nothing behind, neither
    /// a staging directory nor an output at another path.
    pub(super) fn listing(dir: &Path) -> Vec<String> {
        let mut names: Vec<String> = fs::read_dir(dir)
            .unwrap()
            .map(|entry| entry.unwrap().file_name().into_string().unwrap())
            .collect();
        names.sort();
        names
    }

    /// No `-Wl` spelling of the shared-object option makes a local-exec
    /// library through the CLI. (A local-exec object named as a `-Wl` or
    /// `-l:` operand, or reaching the link any other way, is examined after
    /// the link; see `local_exec_objects_on_every_link_route_are_refused_by_name`.) Every
    /// spelling GNU ld 2.42 reads as `--shared` is refused as driver-owned
    /// before anything runs: the full `-shared`, `--shared`, `-Bshareable`
    /// and `--Bshareable`, their abbreviations (`--shar`, `-shar`, `-Bshar`,
    /// `--Bshare`, `-sh`), and a bare `-G`, which GNU ld reads as
    /// `--shared`. The `pic` model is refused the same spellings, and its
    /// library links through the typed `-shared`; an executable with its own
    /// thread-local runs against that library and returns 42.
    #[test]
    fn wl_shared_spellings_cannot_make_a_local_exec_library() {
        let directory = tempfile::tempdir().unwrap();
        let dir = directory.path();
        write_module(dir, "tls.tmbc", &tls_counter_module(false));
        let before = listing(dir);
        for spelling in [
            "-shared",
            "--shared",
            "-Bshareable",
            "--Bshareable",
            "--shar",
            "-shar",
            "-Bshar",
            "--Bshare",
            "-sh",
            "-G",
        ] {
            let wl = format!("-Wl,{spelling}");
            for model in ["static", "pic"] {
                let output = trust_cg(
                    dir,
                    &[
                        &wl,
                        "--relocation-model",
                        model,
                        "-o",
                        "libtcgtls.so",
                        "tls.tmbc",
                    ],
                );
                assert!(!output.status.success(), "{spelling} {model}");
                let text = stderr(&output);
                assert!(
                    text.contains(&format!(
                        "trust-cg: error: {wl}: `{spelling}` is controlled by the trust-cg \
                         option `--shared`"
                    )),
                    "{spelling} {model}: {text}"
                );
                assert!(!text.contains("trust-cg: linking"), "{spelling}: {text}");
                assert!(!text.contains("error[link:"), "{spelling}: {text}");
                assert_eq!(listing(dir), before, "{spelling} {model}");
            }
        }

        let output = trust_cg(
            dir,
            &[
                "-shared",
                "--relocation-model",
                "pic",
                "-o",
                "libtcgtls.so",
                "tls.tmbc",
            ],
        );
        assert!(output.status.success(), "{}", stderr(&output));
        write_module(dir, "user.tmbc", &tls_user_module());
        let rpath = dir.display().to_string();
        let output = trust_cg(
            dir,
            &[
                "-o",
                "user",
                "-L",
                ".",
                "-l",
                "tcgtls",
                "--rpath",
                &rpath,
                "user.tmbc",
            ],
        );
        assert!(output.status.success(), "{}", stderr(&output));
        let status = Command::new(dir.join("user")).status().unwrap();
        assert_eq!(status.code(), Some(42));
    }

    /// An output redirection cannot escape the local-exec output check.
    /// GNU ld 2.42 reads `--outp=<file>` as `--output` and `-o<file>` as
    /// `-o <file>` (and `-outp=<file>` as `-o utp=<file>`), so each is
    /// refused as driver-owned before anything runs. That includes the
    /// review's `-Wl,-shar,--outp=libtcgb.so` against an existing `-o` file.
    /// The `-o` file keeps its bytes, and no library is written at either
    /// path.
    #[test]
    fn wl_output_redirection_is_refused_by_name() {
        let directory = tempfile::tempdir().unwrap();
        let dir = directory.path();
        write_module(dir, "tls.tmbc", &tls_counter_module(false));
        let preexisting = b"\x7fELF an executable that was here first\n";
        fs::write(dir.join("preexist"), preexisting).unwrap();
        let before = listing(dir);
        for (group, refused, typed) in [
            ("--outp=libtcgb.so", "--outp", "-o"),
            ("-olibtcgb.so", "-olibtcgb.so", "-o"),
            ("-shar,--outp=libtcgb.so", "-shar", "--shared"),
            ("--output=libtcgb.so", "--output", "-o"),
            ("-outp=libtcgb.so", "-outp=libtcgb.so", "-o"),
            ("--outpu,libtcgb.so", "--outpu", "-o"),
        ] {
            let wl = format!("-Wl,{group}");
            for target in ["preexist", "fresh"] {
                let output = trust_cg(dir, &[&wl, "-o", target, "tls.tmbc"]);
                assert!(!output.status.success(), "{group} {target}");
                let text = stderr(&output);
                assert!(
                    text.contains(&format!(
                        "trust-cg: error: {wl}: `{refused}` is controlled by the trust-cg \
                         option `{typed}`"
                    )),
                    "{group} {target}: {text}"
                );
                assert!(!text.contains("trust-cg: linking"), "{group}: {text}");
                assert_eq!(fs::read(dir.join("preexist")).unwrap(), preexisting);
                assert_eq!(listing(dir), before, "{group} {target}");
            }
        }
    }

    /// A successful link that writes no output is refused and leaves the
    /// file at the `-o` path alone. `-Wl,--version` makes GNU ld print its
    /// version and exit 0 without linking. The executable's local-exec link
    /// is staged, so trust-cg reports `[TCG-LINK-NO-OUTPUT]`; it neither reads
    /// the existing file as the link's output nor removes it. The `pic`
    /// model has no local-exec input, but its TLS descriptor access is a
    /// GOT-page `ADRP` (`R_AARCH64_TLSDESC_ADR_PAGE21`), so its link is
    /// staged for the GOT-page window check and refused the same way.
    /// Twins: an object with neither kind of relocation keeps the unchecked
    /// behaviour (exit 0, file untouched). The ordinary staged link replaces
    /// the file with an executable that returns 42 and leaves no staging
    /// directory behind.
    #[test]
    fn a_link_that_writes_no_output_leaves_the_output_file_alone() {
        let directory = tempfile::tempdir().unwrap();
        let dir = directory.path();
        write_module(dir, "prog.tmbc", &tls_counter_module(true));
        fs::write(dir.join("keep2.txt"), b"precious\n").unwrap();
        let before = listing(dir);
        let output = trust_cg(dir, &["-Wl,--version", "-o", "keep2.txt", "prog.tmbc"]);
        assert!(!output.status.success());
        let text = stderr(&output);
        assert!(
            text.contains("trust-cg: error: [TCG-LINK-NO-OUTPUT] the linker exited successfully but wrote nothing at"),
            "{text}"
        );
        assert!(
            text.contains("the link is refused; keep2.txt was not touched"),
            "{text}"
        );
        assert!(!text.contains("error[link:"), "{text}");
        assert_eq!(fs::read(dir.join("keep2.txt")).unwrap(), b"precious\n");
        assert_eq!(listing(dir), before);

        let output = trust_cg(
            dir,
            &[
                "-Wl,--version",
                "--relocation-model",
                "pic",
                "-o",
                "keep2.txt",
                "prog.tmbc",
            ],
        );
        assert!(!output.status.success());
        let text = stderr(&output);
        assert!(
            text.contains("trust-cg: error: [TCG-LINK-NO-OUTPUT] the linker exited successfully but wrote nothing at"),
            "{text}"
        );
        assert!(
            text.contains("the link has GOT-addressing inputs (")
                && !text.contains("local-exec TLS inputs"),
            "{text}"
        );
        assert!(
            text.contains("the link is refused; keep2.txt was not touched"),
            "{text}"
        );
        assert_eq!(fs::read(dir.join("keep2.txt")).unwrap(), b"precious\n");
        assert_eq!(listing(dir), before);

        write_module(dir, "div.tmbc", &divide_module());
        let before = listing(dir);
        let output = trust_cg(dir, &["-Wl,--version", "-o", "keep2.txt", "div.tmbc"]);
        assert!(output.status.success(), "{}", stderr(&output));
        assert_eq!(fs::read(dir.join("keep2.txt")).unwrap(), b"precious\n");
        assert_eq!(listing(dir), before);

        let output = trust_cg(dir, &["-o", "keep2.txt", "prog.tmbc"]);
        assert!(output.status.success(), "{}", stderr(&output));
        assert_eq!(listing(dir), before);
        let status = Command::new(dir.join("keep2.txt")).status().unwrap();
        assert_eq!(status.code(), Some(42));
    }

    /// A forwarded value that begins with `@` is refused by name before
    /// anything runs (`[TCG-LINK-RESPONSE-FILE]`): gcc, collect2 and GNU ld
    /// would expand it as a response file of unchecked link arguments. The
    /// rows replay the independent verifier's commands. `--rpath @resp` with
    /// `resp` holding `/x --shared -o libevil.so` wrote a local-exec
    /// `libevil.so` (its user exited 236). `--shared --soname @resp2` with
    /// `resp2` holding `libq.so.1 le.o` linked a local-exec object into a
    /// library. `-o @resp3` with `resp3` holding `libredir.so -shared` was
    /// expanded by gcc. The rows also cover an input path and `-L`/`-l`
    /// values. No file is written anywhere, and the existing files keep their
    /// bytes. Positive twin: `./@name` spellings link and run (42).
    #[test]
    fn response_files_in_forwarded_values_are_refused_by_name() {
        let directory = tempfile::tempdir().unwrap();
        let dir = directory.path();
        write_module(dir, "tls.tmbc", &tls_counter_module(false));
        write_module(dir, "prog.tmbc", &tls_counter_module(true));
        fs::copy(dir.join("prog.tmbc"), dir.join("@inp")).unwrap();
        let output = trust_cg(dir, &["-c", "-o", "le.o", "tls.tmbc"]);
        assert!(output.status.success(), "{}", stderr(&output));
        fs::write(dir.join("resp"), "/x --shared -o libevil.so\n").unwrap();
        fs::write(dir.join("resp2"), "libq.so.1 le.o\n").unwrap();
        fs::write(dir.join("resp3"), "libredir.so -shared\n").unwrap();
        let preexisting = b"\x7fELF an executable that was here first\n";
        fs::write(dir.join("preexist"), preexisting).unwrap();
        let before = listing(dir);
        let hashes = |names: &[&str]| -> Vec<Vec<u8>> {
            names
                .iter()
                .map(|name| fs::read(dir.join(name)).unwrap())
                .collect()
        };
        let kept = ["preexist", "resp", "resp2", "resp3", "le.o", "@inp"];
        let kept_bytes = hashes(&kept);
        for (args, flag, what) in [
            (
                vec!["--rpath", "@resp", "-o", "preexist", "tls.tmbc"],
                "--rpath",
                "the run-time search path `@resp`",
            ),
            (
                vec![
                    "--shared",
                    "--relocation-model",
                    "pic",
                    "--soname",
                    "@resp2",
                    "-o",
                    "libtcgq.so",
                    "tls.tmbc",
                ],
                "--soname",
                "the soname `@resp2`",
            ),
            (
                vec!["-o", "@resp3", "prog.tmbc"],
                "-o",
                "the output path `@resp3`",
            ),
            (
                vec!["-o", "prog", "@inp"],
                "<INPUT>...",
                "the input path `@inp`",
            ),
            (
                vec!["-L", "@resp", "-o", "prog", "prog.tmbc"],
                "-L",
                "the library search path `@resp`",
            ),
            (
                vec!["-l", "@resp", "-o", "prog", "prog.tmbc"],
                "-l",
                "the library name `@resp`",
            ),
        ] {
            let output = trust_cg(dir, &args);
            assert!(!output.status.success(), "{args:?}");
            let text = stderr(&output);
            assert!(
                text.contains(&format!(
                    "trust-cg: error: {flag}: [TCG-LINK-RESPONSE-FILE] {what} begins with `@`"
                )),
                "{args:?}: {text}"
            );
            assert!(!text.contains("trust-cg: linking"), "{args:?}: {text}");
            assert!(!text.contains("error[link:"), "{args:?}: {text}");
            assert!(!dir.join("libevil.so").exists(), "{args:?}");
            assert_eq!(listing(dir), before, "{args:?}");
            assert_eq!(hashes(&kept), kept_bytes, "{args:?}");
        }

        let output = trust_cg(dir, &["-o", "./@out", "./@inp"]);
        assert!(output.status.success(), "{}", stderr(&output));
        let status = Command::new(dir.join("@out")).status().unwrap();
        assert_eq!(status.code(), Some(42));
    }

    /// `tcg_cli_call_bump()` returns `tcg_cli_tls_bump()`, which it imports:
    /// linked with an archive that holds `tcg_cli_tls_bump`, it makes the
    /// linker take that member.
    fn tls_caller_module() -> Module {
        let mut mb = ModuleBuilder::new("tcg_cli_tls_caller");
        let ty = mb.add_func_type(vec![], vec![Ty::I32]);
        let bump = mb.declare_function("tcg_cli_tls_bump", ty);
        let mut fb = mb.function("tcg_cli_call_bump", ty);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        let value = fb.call(bump, vec![]);
        fb.ret(vec![value]);
        fb.build();
        mb.build().expect("ModuleBuilder::build: test fixture")
    }

    /// Run `program` with `args` in `dir` and require success.
    fn run_tool(dir: &Path, program: &str, args: &[&str]) {
        let output = Command::new(program)
            .current_dir(dir)
            .args(args)
            .output()
            .unwrap_or_else(|error| panic!("{program}: {error}"));
        assert!(output.status.success(), "{program} {args:?}: {output:?}");
    }

    /// One non-positional route by which an object reaches the linker, for
    /// the object built in the directory `flavor` (`le`: the default
    /// `static` model, whose thread-local access is local-exec; `pic`: TLS
    /// descriptors). `named` is how the refusal names the loaded input.
    struct Route {
        name: &'static str,
        args: Vec<String>,
        positional: &'static str,
        named: String,
    }

    fn routes(dir: &Path, flavor: &str) -> Vec<Route> {
        let absolute = dir.join(flavor).display().to_string();
        let object = format!("{flavor}/tcgtls.o");
        let member = format!("{flavor}/libtcgarc.a(tcgtls.o)");
        vec![
            Route {
                name: "wl",
                args: vec![format!("-Wl,{object}")],
                positional: "div.tmbc",
                named: object.clone(),
            },
            Route {
                name: "colon",
                args: vec!["-L".into(), flavor.into(), "-l".into(), ":tcgtls.o".into()],
                positional: "div.tmbc",
                named: object.clone(),
            },
            Route {
                name: "member",
                args: vec!["-L".into(), flavor.into(), "-l".into(), "tcgarc".into()],
                positional: "caller.tmbc",
                named: member.clone(),
            },
            Route {
                name: "whole",
                args: vec![format!(
                    "-Wl,--whole-archive,{flavor}/libtcgarc.a,--no-whole-archive"
                )],
                positional: "div.tmbc",
                named: member.clone(),
            },
            Route {
                name: "thin",
                args: vec![format!(
                    "-Wl,--whole-archive,{flavor}/libtcgthin.a,--no-whole-archive"
                )],
                positional: "div.tmbc",
                // GNU ld names a thin archive's member by its own path.
                named: object.clone(),
            },
            Route {
                name: "input",
                args: vec![format!("-Wl,{flavor}/input.ld")],
                positional: "div.tmbc",
                named: format!("{absolute}/tcgtls.o"),
            },
            Route {
                name: "group",
                args: vec![format!("-Wl,{flavor}/group.ld")],
                positional: "caller.tmbc",
                named: format!("{absolute}/libtcgarc.a(tcgtls.o)"),
            },
            Route {
                name: "startgroup",
                args: vec![format!("-Wl,--start-group,{object},--end-group")],
                positional: "div.tmbc",
                named: object,
            },
        ]
    }

    /// Every route by which an object can reach a `--shared` link through
    /// the driver's own options is examined: the link runs with the
    /// linker's input trace, and the library is refused when any AArch64
    /// ELF relocatable object the linker loaded carries local-exec TLS. Each
    /// route puts the local-exec object `le/tcgtls.o` (the `static` model's
    /// `tcg_cli_tls` access) into a `pic` library: as a `-Wl` operand, as
    /// `-l :tcgtls.o`, as an archive member taken by reference (`-l tcgarc`)
    /// or whole (`--whole-archive`), as a thin archive's member, through a
    /// linker script's `INPUT()` or `GROUP()`, and inside `--start-group`.
    /// GNU ld 2.42 links every one without a diagnostic (the earlier
    /// boundary test pinned the `-Wl` and `-l:` routes: their library made a
    /// user exit 236 instead of 42). Each is refused with exactly one
    /// `error[link:tls-model-mismatch]` naming the loaded input, leaves no
    /// output (and no staging directory) behind, and leaves a file already
    /// at the output path as it was. Pic twins: the same routes with the
    /// `pic` object `pic/tcgtls.o` link, and a user with its own
    /// thread-local runs against each library and returns 42.
    #[test]
    fn local_exec_objects_on_every_link_route_are_refused_by_name() {
        let directory = tempfile::tempdir().unwrap();
        let dir = directory.path();
        write_module(dir, "tls.tmbc", &tls_counter_module(false));
        write_module(dir, "div.tmbc", &divide_module());
        write_module(dir, "caller.tmbc", &tls_caller_module());
        write_module(dir, "user.tmbc", &tls_user_module());
        for (flavor, model) in [("le", "static"), ("pic", "pic")] {
            fs::create_dir(dir.join(flavor)).unwrap();
            let object = format!("{flavor}/tcgtls.o");
            let output = trust_cg(
                dir,
                &["-c", "--relocation-model", model, "-o", &object, "tls.tmbc"],
            );
            assert!(output.status.success(), "{}", stderr(&output));
            run_tool(
                dir,
                "ar",
                &["rcs", &format!("{flavor}/libtcgarc.a"), &object],
            );
            run_tool(
                dir,
                "ar",
                &["rcsT", &format!("{flavor}/libtcgthin.a"), &object],
            );
            let absolute = dir.join(flavor);
            fs::write(
                absolute.join("input.ld"),
                format!("INPUT({}/tcgtls.o)\n", absolute.display()),
            )
            .unwrap();
            fs::write(
                absolute.join("group.ld"),
                format!("GROUP({}/libtcgarc.a)\n", absolute.display()),
            )
            .unwrap();
        }

        let link = |route: &Route, library: &str| {
            let mut args = vec![
                "--shared",
                "--relocation-model",
                "pic",
                "-o",
                library,
                route.positional,
            ];
            args.extend(route.args.iter().map(String::as_str));
            trust_cg(dir, &args)
        };
        for route in routes(dir, "le") {
            let library = format!("libtcg_{}.so", route.name);
            let expected = format!(
                "trust-cg: error[link:tls-model-mismatch] `tcg_cli_tls` \
                 (R_AARCH64_TLSLE_ADD_TPREL_HI12): [TCG-LINK-TLS-MODEL] {}: local-exec TLS \
                 relocation R_AARCH64_TLSLE_ADD_TPREL_HI12 against `tcg_cli_tls` was linked \
                 into the output for {library}, which is an ELF shared object (ET_DYN \
                 without DF_1_PIE); the linker loaded this input although it is not a \
                 positional input of the link",
                route.named
            );
            for preexisting in [None, Some(&b"precious\n"[..])] {
                if let Some(bytes) = preexisting {
                    fs::write(dir.join(&library), bytes).unwrap();
                }
                let before = listing(dir);
                let output = link(&route, &library);
                let text = stderr(&output);
                assert!(!output.status.success(), "{}: {text}", route.name);
                assert!(text.contains(&expected), "{}: {text}", route.name);
                assert_eq!(
                    text.matches("error[link:").count(),
                    1,
                    "{}: {text}",
                    route.name
                );
                assert!(
                    text.contains(&format!(
                        "trust-cg: error: the linked output for {library} was refused and not \
                         installed; the linker's image was removed"
                    )),
                    "{}: {text}",
                    route.name
                );
                assert_eq!(listing(dir), before, "{}", route.name);
                match preexisting {
                    None => assert!(!dir.join(&library).exists(), "{}", route.name),
                    Some(bytes) => {
                        assert_eq!(
                            fs::read(dir.join(&library)).unwrap(),
                            bytes,
                            "{}",
                            route.name
                        );
                        fs::remove_file(dir.join(&library)).unwrap();
                    }
                }
            }
        }

        let rpath = dir.display().to_string();
        for route in routes(dir, "pic") {
            let library = format!("libtcg_{}.so", route.name);
            let output = link(&route, &library);
            assert!(
                output.status.success(),
                "{}: {}",
                route.name,
                stderr(&output)
            );
            let user = format!("user_{}", route.name);
            let named = format!("tcg_{}", route.name);
            let output = trust_cg(
                dir,
                &[
                    "-o",
                    &user,
                    "-L",
                    ".",
                    "-l",
                    &named,
                    "--rpath",
                    &rpath,
                    "user.tmbc",
                ],
            );
            assert!(
                output.status.success(),
                "{}: {}",
                route.name,
                stderr(&output)
            );
            let status = Command::new(dir.join(&user)).status().unwrap();
            assert_eq!(status.code(), Some(42), "{}", route.name);
        }
    }

    /// A shared-object link whose input trace cannot be read is refused by
    /// name, since what the linker loaded into the library is unknown. A
    /// passthrough that prints to standard output (`-Wl,--verbose` prints
    /// the linker script and search attempts; `-Wl,-M` the link map) mixes
    /// other text into the trace: exactly one
    /// `error[link:unclassified]: [TCG-LINK-INPUT-TRACE]`, no output, and a
    /// file already at the output keeps its bytes. `-Wl,-M` also sends the
    /// map to standard output in place of the driver's map file, so one
    /// `[TCG-LINK-EH-FRAME-UNPROVEN]` line follows. Twins: the same link
    /// without the passthrough installs the library, and `-Wl,--version`
    /// (which links nothing) succeeds without touching the output.
    #[test]
    fn an_unreadable_input_trace_refuses_a_shared_object_by_name() {
        let directory = tempfile::tempdir().unwrap();
        let dir = directory.path();
        write_module(dir, "div.tmbc", &divide_module());
        let shared = |extra: &[&str]| {
            let mut args = vec![
                "--shared",
                "--relocation-model",
                "pic",
                "-o",
                "libtcgtrace.so",
                "div.tmbc",
            ];
            args.extend(extra);
            trust_cg(dir, &args)
        };
        fs::write(dir.join("libtcgtrace.so"), b"precious\n").unwrap();
        let before = listing(dir);
        for noisy in ["-Wl,--verbose", "-Wl,-M"] {
            let output = shared(&[noisy]);
            let text = stderr(&output);
            assert!(!output.status.success(), "{noisy}: {text}");
            assert!(
                text.contains(
                    "trust-cg: error[link:unclassified]: [TCG-LINK-INPUT-TRACE] the linked \
                     output for libtcgtrace.so, which is an ELF shared object (ET_DYN without \
                     DF_1_PIE), is refused because the linker's input trace does not show what \
                     it loaded: the trace line `"
                ),
                "{noisy}: {text}"
            );
            let unproven = text.contains(
                "trust-cg: error[link:unclassified]: [TCG-LINK-EH-FRAME-UNPROVEN] the linked \
                 output for libtcgtrace.so is refused because the check cannot show that every \
                 .eh_frame pointer in it",
            ) && text.contains(
                "the driver's link map, which locates that input, was not written: the -Wl \
                 option `-M` sent the link map to standard output in place of ",
            );
            assert_eq!(unproven, noisy == "-Wl,-M", "{noisy}: {text}");
            assert_eq!(
                text.matches("error[link:").count(),
                1 + usize::from(unproven),
                "{noisy}: {text}"
            );
            assert_eq!(fs::read(dir.join("libtcgtrace.so")).unwrap(), b"precious\n");
            assert_eq!(listing(dir), before, "{noisy}");
        }

        let output = shared(&["-Wl,--version"]);
        assert!(output.status.success(), "{}", stderr(&output));
        assert_eq!(fs::read(dir.join("libtcgtrace.so")).unwrap(), b"precious\n");
        assert_eq!(listing(dir), before);

        let output = shared(&[]);
        assert!(output.status.success(), "{}", stderr(&output));
        let bytes = fs::read(dir.join("libtcgtrace.so")).unwrap();
        assert_eq!(u16::from_le_bytes([bytes[16], bytes[17]]), 3, "ET_DYN");
        assert_eq!(listing(dir), before);
    }

    /// A shared library contributes no relocation to a link: the linker
    /// binds against its dynamic symbols, so a shared-library input carries
    /// no local-exec relocation into the output and is not scanned. A
    /// `--shared` link of `libtcgcaller.so` against the `pic` library
    /// `libtcgdso.so` links, and a user calling `tcg_cli_call_bump` runs
    /// through both libraries (42). The executable side of the
    /// mismatch is the linker's own refusal, classified by name: a
    /// local-exec reference (`cc -ftls-model=local-exec`, reaching the link
    /// as `-Wl,ext_local-exec.o,./libtcgdef.so`) to `tcg_cli_ext_tls`, which
    /// only the shared library `libtcgdef.so` defines, makes GNU ld 2.42
    /// report a truncated
    /// `R_AARCH64_TLSLE_ADD_TPREL_HI12` against the library's `.tdata`
    /// (the executable has a TLS segment of its own), and trust-cg prints
    /// exactly one `error[link:tls-model-mismatch]` naming the symbol, with
    /// no executable written. Twin: the initial-exec reference links and
    /// returns 42.
    #[test]
    fn shared_library_inputs_are_not_scanned_and_executable_mismatches_are_named() {
        let directory = tempfile::tempdir().unwrap();
        let dir = directory.path();
        write_module(dir, "tls.tmbc", &tls_counter_module(false));
        write_module(dir, "caller.tmbc", &tls_caller_module());
        write_module(dir, "user.tmbc", &tls_user_module());
        write_module(
            dir,
            "caller_user.tmbc",
            &tls_user_module_calling("tcg_cli_call_bump"),
        );
        let rpath = dir.display().to_string();
        let output = trust_cg(
            dir,
            &[
                "--shared",
                "--relocation-model",
                "pic",
                "-o",
                "libtcgdso.so",
                "tls.tmbc",
            ],
        );
        assert!(output.status.success(), "{}", stderr(&output));
        let output = trust_cg(
            dir,
            &[
                "--shared",
                "--relocation-model",
                "pic",
                "-o",
                "libtcgcaller.so",
                "caller.tmbc",
                "-L",
                ".",
                "-l",
                "tcgdso",
                "--rpath",
                &rpath,
            ],
        );
        assert!(output.status.success(), "{}", stderr(&output));
        let output = trust_cg(
            dir,
            &[
                "-o",
                "caller_user",
                "-L",
                ".",
                "-l",
                "tcgcaller",
                "--rpath",
                &rpath,
                "caller_user.tmbc",
            ],
        );
        assert!(output.status.success(), "{}", stderr(&output));
        let status = Command::new(dir.join("caller_user")).status().unwrap();
        assert_eq!(status.code(), Some(42));

        // The executable side: local-exec against a shared library's
        // thread-local.
        fs::write(dir.join("def.c"), "__thread int tcg_cli_ext_tls = 40;\n").unwrap();
        run_tool(
            dir,
            "cc",
            &[
                "-O1",
                "-fPIC",
                "-shared",
                "-Wl,-soname,libtcgdef.so",
                "-o",
                "libtcgdef.so",
                "def.c",
            ],
        );
        fs::write(
            dir.join("ext.c"),
            "extern __thread int tcg_cli_ext_tls;\n\
             int tcg_cli_tls_bump(void) { return tcg_cli_ext_tls += 2; }\n",
        )
        .unwrap();
        for model in ["local-exec", "initial-exec"] {
            let object = format!("ext_{model}.o");
            run_tool(
                dir,
                "cc",
                &[
                    "-O1",
                    &format!("-ftls-model={model}"),
                    "-c",
                    "-o",
                    &object,
                    "ext.c",
                ],
            );
            let program = format!("ext_{model}");
            let output = trust_cg(
                dir,
                &[
                    "-o",
                    &program,
                    // One group keeps the object before the library it
                    // needs (`-l` libraries precede every `-Wl` group, and
                    // the host links `--as-needed`).
                    &format!("-Wl,{object},./libtcgdef.so"),
                    "--rpath",
                    &rpath,
                    "user.tmbc",
                ],
            );
            let text = stderr(&output);
            if model == "local-exec" {
                assert!(!output.status.success(), "{text}");
                assert!(
                    text.contains(
                        "trust-cg: error[link:tls-model-mismatch] `tcg_cli_ext_tls` \
                         (R_AARCH64_TLSLE_ADD_TPREL_HI12): "
                    ) && text.contains("defined in .tdata section in ./libtcgdef.so"),
                    "{text}"
                );
                assert_eq!(text.matches("error[link:").count(), 1, "{text}");
                assert!(!dir.join(&program).exists());
            } else {
                assert!(output.status.success(), "{text}");
                let status = Command::new(dir.join(&program)).status().unwrap();
                assert_eq!(status.code(), Some(42), "{model}");
            }
        }
    }

    /// The installed `cc` from PATH, which the shim below wraps.
    fn host_cc() -> PathBuf {
        std::env::split_paths(&std::env::var_os("PATH").unwrap())
            .map(|dir| dir.join("cc"))
            .find(|path| path.is_file())
            .expect("cc on PATH")
    }

    /// The local-exec output check reads what the linker wrote. A C driver
    /// that links every request as a shared object (a `cc` shim first on
    /// PATH, running the host `cc -shared`) makes GNU ld write a local-exec
    /// library for an executable request. trust-cg reads the staged image,
    /// names the relocation with exactly one
    /// `error[link:tls-model-mismatch]` (and the module's two
    /// default-visibility `static` definitions with
    /// `error[link:non-pic-definition]`), and removes the image. The file
    /// already at the `-o` path keeps its bytes. Positive twin: the `pic`
    /// model links through the same shim into a library that is installed,
    /// and an executable with its own thread-local runs against it and
    /// returns 42.
    #[test]
    fn a_shared_object_the_driver_writes_for_an_executable_is_refused() {
        let directory = tempfile::tempdir().unwrap();
        let dir = directory.path();
        let shim = tempfile::tempdir().unwrap();
        let cc = shim.path().join("cc");
        write_executable_script(
            &cc,
            &format!("#!/bin/sh\nexec '{}' -shared \"$@\"\n", host_cc().display()),
        );
        let mut search = vec![shim.path().to_path_buf()];
        search.extend(std::env::split_paths(&std::env::var_os("PATH").unwrap()));
        let shimmed_path = std::env::join_paths(search).unwrap();
        let shimmed = |args: &[&str]| {
            Command::new(env!("CARGO_BIN_EXE_trust-cg"))
                .arg("--permit-unlicensed")
                .current_dir(dir)
                .env("PATH", &shimmed_path)
                .args(args)
                .output()
                .expect("run trust-cg")
        };

        write_module(dir, "tls.tmbc", &tls_counter_module(false));
        fs::write(dir.join("libtcgshim.so"), b"precious\n").unwrap();
        let before = listing(dir);
        let output = shimmed(&["-o", "libtcgshim.so", "tls.tmbc"]);
        assert!(!output.status.success());
        let text = stderr(&output);
        assert!(
            text.contains(
                "trust-cg: error[link:tls-model-mismatch] `tcg_cli_tls` \
                 (R_AARCH64_TLSLE_ADD_TPREL_HI12): [TCG-LINK-TLS-MODEL] "
            ),
            "{text}"
        );
        assert!(
            text.contains("was linked into the output for libtcgshim.so, which is an ELF shared object (ET_DYN without DF_1_PIE)"),
            "{text}"
        );
        // The module's two default-visibility definitions, compiled
        // `static`, are refused in that image too
        // (OD-SHARED-NON-PIC-DEFINITION-20261024).
        for definition in ["tcg_cli_tls", "tcg_cli_tls_bump"] {
            assert!(
                text.contains(&format!(
                    "trust-cg: error[link:non-pic-definition] `{definition}`: \
                     [TCG-LINK-PREEMPTIBLE-DEFINITION] "
                )) && text.contains(
                    "cannot be linked into the output for libtcgshim.so (an ELF shared object \
                     (ET_DYN without DF_1_PIE))"
                ),
                "{definition}: {text}"
            );
        }
        assert_eq!(text.matches("error[link:").count(), 3, "{text}");
        assert!(
            text.contains(
                "trust-cg: error: the linked output for libtcgshim.so was refused and not \
                 installed; the linker's image was removed"
            ),
            "{text}"
        );
        assert_eq!(fs::read(dir.join("libtcgshim.so")).unwrap(), b"precious\n");
        assert_eq!(listing(dir), before);

        let output = shimmed(&[
            "--relocation-model",
            "pic",
            "-o",
            "libtcgshim.so",
            "tls.tmbc",
        ]);
        assert!(output.status.success(), "{}", stderr(&output));
        assert_eq!(listing(dir), before);
        write_module(dir, "user.tmbc", &tls_user_module());
        let rpath = dir.display().to_string();
        let output = trust_cg(
            dir,
            &[
                "-o",
                "user",
                "-L",
                ".",
                "-l",
                "tcgshim",
                "--rpath",
                &rpath,
                "user.tmbc",
            ],
        );
        assert!(output.status.success(), "{}", stderr(&output));
        let status = Command::new(dir.join("user")).status().unwrap();
        assert_eq!(status.code(), Some(42));
    }

    /// `main` returns `tcg_cli_tls_bump() + tcg_cli_tls - 42` for a
    /// `tcg_cli_tls` it imports as a thread-local (`as_thread_local`) or, the
    /// clash, as an ordinary global.
    fn tls_reader_module(as_thread_local: bool) -> Module {
        let mut mb = ModuleBuilder::new("tcg_cli_tls_reader");
        mb.add_global(Global {
            initializer: None,
            tls: as_thread_local.then_some(TlsModel::InitialExec),
            ..thread_local("tcg_cli_tls", 0)
        });
        let ty = mb.add_func_type(vec![], vec![Ty::I32]);
        let bump = mb.declare_function("tcg_cli_tls_bump", ty);
        let mut fb = mb.function("main", ty);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        let bumped = fb.call(bump, vec![]);
        let address = fb.global_addr(GlobalId::new(0));
        let value = fb.load(Ty::I32, address);
        let sum = fb.binop(BinOp::Add, Ty::I32, bumped, value);
        let base = fb.iconst(Ty::I32, 42);
        let result = fb.binop(BinOp::Sub, Ty::I32, sum, base);
        fb.ret(vec![result]);
        fb.build();
        mb.build().expect("ModuleBuilder::build: test fixture")
    }

    /// One input defines `tcg_cli_tls` as a thread-local and the other reads
    /// it as an ordinary global: the link fails with GNU ld's named
    /// TLS/non-TLS symbol-type clash. The positive twin imports it as a
    /// thread-local and runs.
    #[test]
    fn thread_local_symbol_type_clash_is_classified() {
        let directory = tempfile::tempdir().unwrap();
        let dir = directory.path();
        write_module(dir, "tls.tmbc", &tls_counter_module(false));
        write_module(dir, "plain.tmbc", &tls_reader_module(false));
        let output = trust_cg(dir, &["-o", "prog", "tls.tmbc", "plain.tmbc"]);
        assert!(!output.status.success());
        let text = stderr(&output);
        assert!(
            text.contains("trust-cg: error[link:tls-symbol-type-mismatch] `tcg_cli_tls`"),
            "{text}"
        );
        assert!(text.contains("mismatches non-TLS reference in"), "{text}");
        assert!(!dir.join("prog").exists());

        write_module(dir, "thread.tmbc", &tls_reader_module(true));
        let output = trust_cg(dir, &["-o", "prog", "tls.tmbc", "thread.tmbc"]);
        assert!(output.status.success(), "{}", stderr(&output));
        let status = Command::new(dir.join("prog")).status().unwrap();
        assert_eq!(status.code(), Some(42));
    }
}

/// Executable link modes through the CLI binary itself, on the Linux
/// AArch64 GNU host: `--pie`, `--no-pie`, `--static` and `--nostdlib` each
/// link and run, and the image is the kind the mode asks for. The kind is
/// read twice: by the link driver's own reader (`elf_linked_kind`, which
/// reads `e_type` and `DT_FLAGS_1`) and by the host `readelf` (binutils).
#[cfg(all(target_arch = "aarch64", target_os = "linux", target_env = "gnu"))]
mod linux_link_modes {
    use super::linux_tls::listing;
    use super::*;
    use trust_cg_codegen::link_driver::{ElfLinkedKind, elf_linked_kind};

    /// `main` returns 42.
    fn answer_module() -> Module {
        let mut mb = ModuleBuilder::new("tcg_cli_answer_main");
        let ty = mb.add_func_type(vec![], vec![Ty::I32]);
        let mut fb = mb.function("main", ty);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        let value = fb.iconst(Ty::I32, 42);
        fb.ret(vec![value]);
        fb.build();
        mb.build().expect("ModuleBuilder::build: test fixture")
    }

    /// `main` returns `tcg_cli_div(84, 2)` (from [`divide_module`], whose
    /// `i128` division needs libgcc's `__divti3`) truncated to `i32`.
    fn divide_main_module() -> Module {
        let mut mb = ModuleBuilder::new("tcg_cli_divide_main");
        let div_ty = mb.add_func_type(vec![Ty::I128, Ty::I128], vec![Ty::I128]);
        let div = mb.declare_function("tcg_cli_div", div_ty);
        let ty = mb.add_func_type(vec![], vec![Ty::I32]);
        let mut fb = mb.function("main", ty);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        let a = fb.iconst(Ty::I128, 84);
        let b = fb.iconst(Ty::I128, 2);
        let quotient = fb.call(div, vec![a, b]);
        let value = fb.trunc(Ty::I128, Ty::I32, quotient);
        fb.ret(vec![value]);
        fb.build();
        mb.build().expect("ModuleBuilder::build: test fixture")
    }

    /// `tcg_cli_answer()` returns 42 (a library routine).
    fn answer_library_module() -> Module {
        let mut mb = ModuleBuilder::new("tcg_cli_answer_lib");
        let ty = mb.add_func_type(vec![], vec![Ty::I32]);
        let mut fb = mb.function("tcg_cli_answer", ty);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        let value = fb.iconst(Ty::I32, 42);
        fb.ret(vec![value]);
        fb.build();
        mb.build().expect("ModuleBuilder::build: test fixture")
    }

    /// `main` returns `tcg_cli_answer()`, which it imports.
    fn answer_caller_module() -> Module {
        let mut mb = ModuleBuilder::new("tcg_cli_answer_caller");
        let ty = mb.add_func_type(vec![], vec![Ty::I32]);
        let answer = mb.declare_function("tcg_cli_answer", ty);
        let mut fb = mb.function("main", ty);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        let value = fb.call(answer, vec![]);
        fb.ret(vec![value]);
        fb.build();
        mb.build().expect("ModuleBuilder::build: test fixture")
    }

    /// A `_start` for `--nostdlib` links: it calls `main` and exits with its
    /// result through the `exit` system call (93), with no C runtime.
    const START: &str = "    .text\n    .globl _start\n    .type _start, %function\n_start:\n    bl main\n    mov x8, #93\n    svc #0\n";

    const PT_DYNAMIC: u32 = 2;
    const PT_INTERP: u32 = 3;

    /// The `p_type` of every program header of the ELF64 image `bytes`.
    fn program_header_types(bytes: &[u8]) -> Vec<u32> {
        let u16_at = |at: usize| u16::from_le_bytes(bytes[at..at + 2].try_into().unwrap());
        let phoff = u64::from_le_bytes(bytes[32..40].try_into().unwrap()) as usize;
        let (size, count) = (usize::from(u16_at(54)), usize::from(u16_at(56)));
        (0..count)
            .map(|index| {
                let at = phoff + index * size;
                u32::from_le_bytes(bytes[at..at + 4].try_into().unwrap())
            })
            .collect()
    }

    /// `readelf <flag> <path>` output.
    fn readelf(flag: &str, path: &Path) -> String {
        let output = Command::new("readelf")
            .args([flag, "-W"])
            .arg(path)
            .output()
            .expect("run readelf");
        assert!(output.status.success(), "{output:?}");
        String::from_utf8_lossy(&output.stdout).into_owned()
    }

    /// The kind of the linked image at `path`, checked against `readelf`:
    /// what the driver's reader says, whether it has a `PT_INTERP` and
    /// whether it has a `PT_DYNAMIC`.
    fn image_kind(path: &Path) -> (ElfLinkedKind, bool, bool) {
        let bytes = fs::read(path).unwrap();
        let kind = elf_linked_kind(&bytes).unwrap();
        let headers = program_header_types(&bytes);
        let interp = headers.contains(&PT_INTERP);
        let dynamic = headers.contains(&PT_DYNAMIC);
        let header = readelf("-h", path);
        let expected_type = match kind {
            ElfLinkedKind::PositionIndependentExecutable => {
                "DYN (Position-Independent Executable file)"
            }
            ElfLinkedKind::Executable => "EXEC (Executable file)",
            other => panic!("{}: not an executable: {other:?}", path.display()),
        };
        assert!(
            header.lines().any(|line| {
                line.trim_start().starts_with("Type:") && line.trim_end().ends_with(expected_type)
            }),
            "{}: {header}",
            path.display()
        );
        let segments = readelf("-l", path);
        assert_eq!(
            segments
                .lines()
                .any(|line| line.trim_start().starts_with("INTERP ")),
            interp,
            "{}: {segments}",
            path.display()
        );
        assert_eq!(
            segments
                .lines()
                .any(|line| line.trim_start().starts_with("DYNAMIC ")),
            dynamic,
            "{}: {segments}",
            path.display()
        );
        (kind, interp, dynamic)
    }

    fn status(path: &Path) -> Option<i32> {
        Command::new(path).status().unwrap().code()
    }

    /// Each mode links through the CLI binary and runs (42): the default
    /// and `--pie` give a PIE (`ET_DYN` with `DF_1_PIE`) with a `PT_INTERP`,
    /// `--no-pie` an `ET_EXEC` with a `PT_INTERP`, `--static` an `ET_EXEC`
    /// with neither `PT_INTERP` nor `PT_DYNAMIC`. The host C driver links a
    /// PIE by default, so `--pie` is also checked under a C driver whose
    /// default is `-no-pie` (a shim running `cc -no-pie "$@"`): there the
    /// default gives an `ET_EXEC` and `--pie` a PIE, so the option reaches
    /// the driver. Each mode also links the local-exec TLS program (the
    /// staged read-back path), which returns 42 in every executable kind.
    /// Negative twins: `--pie` and `--no-pie` with `--shared` are refused by
    /// name before anything runs and write nothing, and a `--static` link
    /// against a library that exists only as a shared object fails with
    /// exactly one `error[link:library-not-found]` naming it, while the same
    /// link without `--static` runs.
    #[test]
    fn pie_no_pie_and_static_links_have_the_requested_kind_and_run() {
        let directory = tempfile::tempdir().unwrap();
        let dir = directory.path();
        write_module(dir, "answer.tmbc", &answer_module());
        write_module(dir, "tls.tmbc", &super::linux_tls::tls_counter_module(true));
        use ElfLinkedKind::{Executable, PositionIndependentExecutable as Pie};
        for (name, flags, expected) in [
            ("default", vec![], (Pie, true, true)),
            ("pie", vec!["--pie"], (Pie, true, true)),
            ("no_pie", vec!["--no-pie"], (Executable, true, true)),
            ("static", vec!["--static"], (Executable, false, false)),
        ] {
            for program in ["answer", "tls"] {
                let output_name = format!("{program}_{name}");
                let input = format!("{program}.tmbc");
                let mut args = flags.clone();
                args.extend(["-o", &output_name, &input]);
                let output = trust_cg(dir, &args);
                assert!(
                    output.status.success(),
                    "{name} {program}: {}",
                    stderr(&output)
                );
                let path = dir.join(&output_name);
                assert_eq!(image_kind(&path), expected, "{name} {program}");
                assert_eq!(status(&path), Some(42), "{name} {program}");
            }
        }

        // `--pie` under a C driver that defaults to position-dependent.
        let shim = tempfile::tempdir().unwrap();
        let cc = shim.path().join("cc");
        write_executable_script(&cc, "#!/bin/sh\nexec /usr/bin/cc -no-pie \"$@\"\n");
        let mut search = vec![shim.path().to_path_buf()];
        search.extend(std::env::split_paths(&std::env::var_os("PATH").unwrap()));
        let shimmed_path = std::env::join_paths(search).unwrap();
        for (name, flags, expected) in [
            ("shim_default", vec![], Executable),
            ("shim_pie", vec!["--pie"], Pie),
        ] {
            let mut args = flags.clone();
            args.extend(["-o", name, "answer.tmbc"]);
            let output = Command::new(env!("CARGO_BIN_EXE_trust-cg"))
                .arg("--permit-unlicensed")
                .current_dir(dir)
                .env("PATH", &shimmed_path)
                .args(&args)
                .output()
                .unwrap();
            assert!(output.status.success(), "{name}: {}", stderr(&output));
            assert_eq!(image_kind(&dir.join(name)).0, expected, "{name}");
            assert_eq!(status(&dir.join(name)), Some(42), "{name}");
        }

        // Position independence selects an executable.
        let before = listing(dir);
        for flag in ["--pie", "--no-pie"] {
            let output = trust_cg(dir, &["--shared", flag, "-o", "libmode.so", "answer.tmbc"]);
            assert!(!output.status.success(), "{flag}");
            let text = stderr(&output);
            assert!(
                text.contains(&format!(
                    "trust-cg: error: {flag}: position independence selects an executable; a \
                     shared object is always position-independent"
                )),
                "{flag}: {text}"
            );
            assert!(!text.contains("trust-cg: linking"), "{flag}: {text}");
            assert_eq!(listing(dir), before, "{flag}");
        }

        // `--static` takes only static libraries.
        fs::create_dir(dir.join("dyn")).unwrap();
        write_module(dir, "answer_lib.tmbc", &answer_library_module());
        write_module(dir, "answer_caller.tmbc", &answer_caller_module());
        let output = trust_cg(
            dir,
            &[
                "--shared",
                "--relocation-model",
                "pic",
                "-o",
                "dyn/libtcgdynonly.so",
                "answer_lib.tmbc",
            ],
        );
        assert!(output.status.success(), "{}", stderr(&output));
        let before = listing(dir);
        let output = trust_cg(
            dir,
            &[
                "--static",
                "-o",
                "static_dyn",
                "-L",
                "dyn",
                "-l",
                "tcgdynonly",
                "answer_caller.tmbc",
            ],
        );
        assert!(!output.status.success());
        let text = stderr(&output);
        assert!(
            text.contains("trust-cg: error[link:library-not-found] `tcgdynonly`: "),
            "{text}"
        );
        assert_eq!(text.matches("error[link:").count(), 1, "{text}");
        assert_eq!(listing(dir), before);
        let rpath = dir.join("dyn").display().to_string();
        let output = trust_cg(
            dir,
            &[
                "-o",
                "dynamic_dyn",
                "-L",
                "dyn",
                "-l",
                "tcgdynonly",
                "--rpath",
                &rpath,
                "answer_caller.tmbc",
            ],
        );
        assert!(output.status.success(), "{}", stderr(&output));
        assert_eq!(status(&dir.join("dynamic_dyn")), Some(42));
    }

    /// `--nostdlib` links no C runtime, C library or libgcc: a program with
    /// its own `_start` (`-Wl,start.o`, assembled by the host C driver) links
    /// and returns 42, as a PIE with a `PT_INTERP` by default and as an
    /// `ET_EXEC` without one with `--static`. Negative twin: a program whose
    /// `i128` division needs libgcc's `__divti3` fails with exactly one
    /// `error[link:undefined-symbol]` naming it and writes nothing; adding
    /// `-l gcc` links it (42), and without `--nostdlib` it links as usual.
    #[test]
    fn nostdlib_links_only_what_the_command_line_names() {
        let directory = tempfile::tempdir().unwrap();
        let dir = directory.path();
        write_module(dir, "answer.tmbc", &answer_module());
        write_module(dir, "div.tmbc", &divide_module());
        write_module(dir, "div_main.tmbc", &divide_main_module());
        fs::write(dir.join("start.s"), START).unwrap();
        let assembled = Command::new("cc")
            .current_dir(dir)
            .args(["-c", "-o", "start.o", "start.s"])
            .output()
            .unwrap();
        assert!(assembled.status.success(), "{assembled:?}");

        use ElfLinkedKind::{Executable, PositionIndependentExecutable as Pie};
        for (name, flags, expected) in [
            ("nostdlib", vec!["--nostdlib"], (Pie, true, true)),
            (
                "nostdlib_static",
                vec!["--nostdlib", "--static"],
                (Executable, false, false),
            ),
        ] {
            let mut args = flags.clone();
            args.extend(["-o", name, "-Wl,start.o", "answer.tmbc"]);
            let output = trust_cg(dir, &args);
            assert!(output.status.success(), "{name}: {}", stderr(&output));
            assert_eq!(image_kind(&dir.join(name)), expected, "{name}");
            assert_eq!(status(&dir.join(name)), Some(42), "{name}");
        }

        let before = listing(dir);
        let output = trust_cg(
            dir,
            &[
                "--nostdlib",
                "-o",
                "div_nostdlib",
                "-Wl,start.o",
                "div_main.tmbc",
                "div.tmbc",
            ],
        );
        assert!(!output.status.success());
        let text = stderr(&output);
        assert!(
            text.contains("trust-cg: error[link:undefined-symbol] `__divti3`: "),
            "{text}"
        );
        assert_eq!(text.matches("error[link:").count(), 1, "{text}");
        assert_eq!(listing(dir), before);

        for (name, args) in [
            (
                "div_nostdlib_gcc",
                vec![
                    "--nostdlib",
                    "-o",
                    "div_nostdlib_gcc",
                    "-Wl,start.o",
                    "div_main.tmbc",
                    "div.tmbc",
                    "-l",
                    "gcc",
                ],
            ),
            (
                "div_default",
                vec!["-o", "div_default", "div_main.tmbc", "div.tmbc"],
            ),
        ] {
            let output = trust_cg(dir, &args);
            assert!(output.status.success(), "{name}: {}", stderr(&output));
            assert_eq!(status(&dir.join(name)), Some(42), "{name}");
        }
    }
}

/// The GOT-page `ADRP` window on every route by which an object reaches the
/// linker, through the CLI binary on the Linux AArch64 GNU host. GNU ld 2.42
/// does not check the page window of `R_AARCH64_ADR_GOT_PAGE`,
/// `R_AARCH64_TLSIE_ADR_GOTTPREL_PAGE21` and `R_AARCH64_TLSDESC_ADR_PAGE21`:
/// with the GOT placed 8 GiB from the code it links and writes each page
/// delta truncated. The driver's image check therefore reads every AArch64
/// ELF relocatable object the linker's input trace names, not only the
/// positional inputs.
#[cfg(all(target_arch = "aarch64", target_os = "linux", target_env = "gnu"))]
mod linux_got_page {
    use super::linux_tls::listing;
    use super::*;
    use std::os::unix::process::ExitStatusExt;
    use trust_ir::value::GlobalId;
    use trust_ir::{Constant, Global, Linkage, TlsModel, Visibility};

    /// SIGSEGV on Linux.
    const SIGSEGV: i32 = 11;

    /// SIGABRT on Linux.
    const SIGABRT: i32 = 6;

    /// `tcg_desc_bump()` adds 2 to the thread-local `tcg_desc_tls` (40) and
    /// returns it plus the preemptible word `tcg_desc_word` (100) minus 100.
    /// Compiled with the `pic` model, the thread-local is reached through a
    /// TLS descriptor (`R_AARCH64_TLSDESC_ADR_PAGE21`) and the word through
    /// its GOT slot (`R_AARCH64_ADR_GOT_PAGE`): the `got_page_module` of
    /// `e2e_aarch64_link_runtime`.
    fn got_page_module() -> Module {
        let global = |name: &str, value: i128, tls| Global {
            name: name.into(),
            ty: Ty::I32,
            mutable: true,
            initializer: Some(Constant::Int(value)),
            linkage: Linkage::External,
            tls,
            align: None,
            section: None,
            visibility: Visibility::Default,
            retained: false,
        };
        let mut mb = ModuleBuilder::new("tcg_desc");
        mb.add_global(global("tcg_desc_tls", 40, Some(TlsModel::LocalExec)));
        mb.add_global(global("tcg_desc_word", 100, None));
        let ty = mb.add_func_type(vec![], vec![Ty::I32]);
        let mut fb = mb.function("tcg_desc_bump", ty);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        let tls = fb.global_addr(GlobalId::new(0));
        let value = fb.load(Ty::I32, tls);
        let two = fb.iconst(Ty::I32, 2);
        let bumped = fb.binop(BinOp::Add, Ty::I32, value, two);
        fb.store(Ty::I32, tls, bumped);
        let word = fb.global_addr(GlobalId::new(1));
        let word = fb.load(Ty::I32, word);
        let sum = fb.binop(BinOp::Add, Ty::I32, bumped, word);
        let hundred = fb.iconst(Ty::I32, 100);
        let result = fb.binop(BinOp::Sub, Ty::I32, sum, hundred);
        fb.ret(vec![result]);
        fb.build();
        mb.build().expect("ModuleBuilder::build: test fixture")
    }

    /// `tcg_call_desc()` returns `tcg_desc_bump()`, which it imports: linked
    /// with an archive that holds `tcg_desc_bump`, it makes the linker take
    /// that member.
    fn caller_module() -> Module {
        let mut mb = ModuleBuilder::new("tcg_desc_caller");
        let ty = mb.add_func_type(vec![], vec![Ty::I32]);
        let bump = mb.declare_function("tcg_desc_bump", ty);
        let mut fb = mb.function("tcg_call_desc", ty);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        let value = fb.call(bump, vec![]);
        fb.ret(vec![value]);
        fb.build();
        mb.build().expect("ModuleBuilder::build: test fixture")
    }

    /// The user of a library: exits 0 when two calls of `tcg_desc_bump`
    /// return 42 and 44.
    const DESC_MAIN: &str = "extern int tcg_desc_bump(void);\nint main(void) { return tcg_desc_bump() == 42 && tcg_desc_bump() == 44 ? 0 : 1; }\n";

    /// A `-Wl` group placing `.got` at `got` and `.got.plt` 64 KiB above it.
    fn placement(got: u64) -> String {
        format!(
            "-Wl,--section-start=.got={got:#x},--section-start=.got.plt={:#x}",
            got + 0x10000
        )
    }

    /// Run `program` with `args` in `dir` and require success.
    fn run_tool(dir: &Path, program: &str, args: &[&str]) {
        let output = Command::new(program)
            .current_dir(dir)
            .args(args)
            .output()
            .unwrap_or_else(|error| panic!("{program}: {error}"));
        assert!(output.status.success(), "{program} {args:?}: {output:?}");
    }

    /// Link [`DESC_MAIN`] against `dir/library` with the host `cc` and run
    /// the program.
    fn user_status(dir: &Path, library: &str, name: &str) -> std::process::ExitStatus {
        let library = dir.join(library).display().to_string();
        let rpath = format!("-Wl,-rpath,{}", dir.display());
        run_tool(dir, "cc", &["-o", name, "desc_main.c", &library, &rpath]);
        Command::new(dir.join(name)).status().unwrap()
    }

    /// Compile `module` into `object` in `dir` with the `pic` model.
    fn compile_pic(dir: &Path, module: &str, object: &str) {
        let output = trust_cg(
            dir,
            &["-c", "--relocation-model", "pic", "-o", object, module],
        );
        assert!(output.status.success(), "{}", stderr(&output));
    }

    /// One non-positional route by which `gp/got_page.o` reaches the
    /// linker; `named` is how a refusal names the loaded input.
    struct Route {
        name: &'static str,
        args: Vec<String>,
        named: String,
    }

    fn routes(dir: &Path) -> Vec<Route> {
        let absolute = dir.join("gp").display().to_string();
        let object = "gp/got_page.o".to_string();
        let member = "gp/libtcggot.a(got_page.o)".to_string();
        vec![
            Route {
                name: "wl",
                args: vec![format!("-Wl,{object}")],
                named: object.clone(),
            },
            Route {
                name: "colon",
                args: vec!["-L".into(), "gp".into(), "-l".into(), ":got_page.o".into()],
                named: object.clone(),
            },
            Route {
                name: "member",
                args: vec!["-L".into(), "gp".into(), "-l".into(), "tcggot".into()],
                named: member.clone(),
            },
            Route {
                name: "whole",
                args: vec!["-Wl,--whole-archive,gp/libtcggot.a,--no-whole-archive".into()],
                named: member,
            },
            Route {
                name: "thin",
                args: vec!["-Wl,--whole-archive,gp/libtcggotthin.a,--no-whole-archive".into()],
                // GNU ld names a thin archive's member by its own path.
                named: object.clone(),
            },
            Route {
                name: "input",
                args: vec!["-Wl,gp/input.ld".into()],
                named: format!("{absolute}/got_page.o"),
            },
            Route {
                name: "group",
                args: vec!["-Wl,gp/group.ld".into()],
                named: format!("{absolute}/libtcggot.a(got_page.o)"),
            },
            Route {
                name: "startgroup",
                args: vec![format!("-Wl,--start-group,{object},--end-group")],
                named: object,
            },
        ]
    }

    /// The GOT-page window check reads every input the linker loads. Each
    /// route puts the `pic` object `gp/got_page.o` into a `--shared
    /// --nostdlib` library of `caller.tmbc` whose `.got` is placed 8 GiB
    /// from its code: as a `-Wl` operand, as `-l :got_page.o`, as an archive
    /// member taken by reference (`-l tcggot`) or whole (`--whole-archive`),
    /// as a thin archive's member, through a linker script's `INPUT()` or
    /// `GROUP()`, and inside `--start-group`. None of them is a positional
    /// input, and before the check read the input trace each was installed
    /// (the closure audit ran the `-Wl`, `-l:` and `--whole-archive`
    /// routes). Each is now refused with exactly two
    /// `error[link:relocation-out-of-range]` lines, `[TCG-LINK-GOT-PAGE-WINDOW]`
    /// for the descriptor and the word, naming the loaded input and saying
    /// it is not a positional input; no output (and no staging directory)
    /// is left, and a file already at the output keeps its bytes. Without
    /// the driver, GNU ld links every route and the library's user dies with
    /// SIGSEGV. Twin: with `.got` at 2 GiB each route links through the
    /// driver and the user exits 0.
    #[test]
    fn got_page_objects_on_every_link_route_are_refused_by_name() {
        let directory = tempfile::tempdir().unwrap();
        let dir = directory.path();
        write_module(dir, "got_page.tmbc", &got_page_module());
        write_module(dir, "caller.tmbc", &caller_module());
        fs::write(dir.join("desc_main.c"), DESC_MAIN).unwrap();
        fs::create_dir(dir.join("gp")).unwrap();
        compile_pic(dir, "got_page.tmbc", "gp/got_page.o");
        compile_pic(dir, "caller.tmbc", "caller.o");
        run_tool(dir, "ar", &["rcs", "gp/libtcggot.a", "gp/got_page.o"]);
        run_tool(dir, "ar", &["rcsT", "gp/libtcggotthin.a", "gp/got_page.o"]);
        let absolute = dir.join("gp");
        fs::write(
            absolute.join("input.ld"),
            format!("INPUT({}/got_page.o)\n", absolute.display()),
        )
        .unwrap();
        fs::write(
            absolute.join("group.ld"),
            format!("GROUP({}/libtcggot.a)\n", absolute.display()),
        )
        .unwrap();

        let (far, near) = (placement(0x2_0000_0000), placement(0x8000_0000));
        let link = |route: &Route, library: &str, placed: &str| {
            let mut args = vec![
                "--shared",
                "--nostdlib",
                "--relocation-model",
                "pic",
                "-o",
                library,
                "caller.tmbc",
            ];
            args.extend(route.args.iter().map(String::as_str));
            args.push(placed);
            trust_cg(dir, &args)
        };
        for route in routes(dir) {
            let library = format!("libgp_{}.so", route.name);
            for preexisting in [None, Some(&b"precious\n"[..])] {
                if let Some(bytes) = preexisting {
                    fs::write(dir.join(&library), bytes).unwrap();
                }
                let before = listing(dir);
                let output = link(&route, &library, &far);
                let text = stderr(&output);
                assert!(!output.status.success(), "{}: {text}", route.name);
                for (symbol, relocation, slot) in [
                    (
                        "tcg_desc_tls",
                        "R_AARCH64_TLSDESC_ADR_PAGE21",
                        "R_AARCH64_TLSDESC",
                    ),
                    (
                        "tcg_desc_word",
                        "R_AARCH64_ADR_GOT_PAGE",
                        "R_AARCH64_GLOB_DAT",
                    ),
                ] {
                    let expected = format!(
                        "trust-cg: error[link:relocation-out-of-range] `{symbol}` \
                         ({relocation}): [TCG-LINK-GOT-PAGE-WINDOW] {}: {relocation} against \
                         `{symbol}` addresses a GOT slot through an ADRP page delta, and the \
                         linked output for {library} is refused: its {slot} slot at 0x2000",
                        route.named
                    );
                    assert!(text.contains(&expected), "{}: {text}", route.name);
                }
                // The code the linker wrote itself addresses slots 8 GiB
                // away as well: the PLT entry of `tcg_desc_bump` (which
                // `caller.tmbc` calls through R_AARCH64_CALL26 alone) and
                // the lazy TLS descriptor trampoline.
                for expected in [
                    format!(
                        "trust-cg: error[link:relocation-out-of-range] `tcg_desc_bump` \
                         (R_AARCH64_JUMP_SLOT): [TCG-LINK-GOT-PAGE-WINDOW] linker-generated PLT \
                         (1 R_AARCH64_JUMP_SLOT slot(s), DT_JMPREL, an executable `.plt` \
                         section): the PLT entry the linker wrote for `tcg_desc_bump` addresses \
                         its slot through an ADRP page delta that no input relocation describes, \
                         and the linked output for {library} is refused: its \
                         R_AARCH64_JUMP_SLOT slot at 0x2000"
                    ),
                    "trust-cg: error[link:relocation-out-of-range]: [TCG-LINK-GOT-PAGE-WINDOW] \
                     linker-generated TLS descriptor trampoline (DT_TLSDESC_PLT at "
                        .to_string(),
                ] {
                    assert!(text.contains(&expected), "{}: {text}", route.name);
                }
                assert_eq!(
                    text.matches("error[link:").count(),
                    4,
                    "{}: {text}",
                    route.name
                );
                assert_eq!(
                    text.matches(
                        "the linker loaded this input although it is not a positional input \
                         of the link"
                    )
                    .count(),
                    2,
                    "{}: {text}",
                    route.name
                );
                assert!(
                    text.contains(&format!(
                        "trust-cg: error: the linked output for {library} was refused and not \
                         installed; the linker's image was removed"
                    )),
                    "{}: {text}",
                    route.name
                );
                assert_eq!(listing(dir), before, "{}", route.name);
                match preexisting {
                    None => assert!(!dir.join(&library).exists(), "{}", route.name),
                    Some(bytes) => {
                        assert_eq!(
                            fs::read(dir.join(&library)).unwrap(),
                            bytes,
                            "{}",
                            route.name
                        );
                        fs::remove_file(dir.join(&library)).unwrap();
                    }
                }
            }

            // Without the driver GNU ld links the route, and the truncated
            // page deltas make the user read the wrong words.
            let raw = format!("libgpraw_{}.so", route.name);
            let mut args = vec![
                "-shared",
                "-nostdlib",
                "-Wl,-z,noexecstack",
                "-o",
                raw.as_str(),
                "caller.o",
            ];
            args.extend(route.args.iter().map(String::as_str));
            args.push(&far);
            run_tool(dir, "cc", &args);
            let status = user_status(dir, &raw, &format!("user_raw_{}", route.name));
            assert_eq!(status.signal(), Some(SIGSEGV), "{}: {status:?}", route.name);

            let near_library = format!("libgpnear_{}.so", route.name);
            let output = link(&route, &near_library, &near);
            assert!(
                output.status.success(),
                "{}: {}",
                route.name,
                stderr(&output)
            );
            let status = user_status(dir, &near_library, &format!("user_near_{}", route.name));
            assert_eq!(status.code(), Some(0), "{}: {status:?}", route.name);
        }
    }

    /// The closure audit's reproducer, as it ran: `trust-cg -shared
    /// -nostdlib --relocation-model pic -Wl,got_page.o
    /// -Wl,--section-start=.got=0x200000000,--section-start=.got.plt=0x200010000
    /// -o libbypass.so b1_scalars.tmbc` (the conformance fixture) exited 0
    /// and installed a library whose user died with SIGSEGV. It is refused
    /// by name, no `libbypass.so` is written, and with the GOT at 2 GiB the
    /// same command links and the user exits 0.
    #[test]
    fn the_closure_audit_reproducer_is_refused_and_its_near_twin_runs() {
        let directory = tempfile::tempdir().unwrap();
        let dir = directory.path();
        write_module(dir, "got_page.tmbc", &got_page_module());
        compile_pic(dir, "got_page.tmbc", "got_page.o");
        fs::write(dir.join("desc_main.c"), DESC_MAIN).unwrap();
        fs::copy(
            Path::new(env!("CARGO_MANIFEST_DIR"))
                .join("../../tests/fixtures/trust_ir_binary_container/conformance/b1_scalars.tmbc"),
            dir.join("b1_scalars.tmbc"),
        )
        .unwrap();
        let command = |library: &str, got: u64| {
            trust_cg(
                dir,
                &[
                    "-shared",
                    "-nostdlib",
                    "--relocation-model",
                    "pic",
                    "-Wl,got_page.o",
                    &placement(got),
                    "-o",
                    library,
                    "b1_scalars.tmbc",
                ],
            )
        };
        let before = listing(dir);
        let output = command("libbypass.so", 0x2_0000_0000);
        let text = stderr(&output);
        assert!(!output.status.success(), "{text}");
        for (symbol, relocation) in [
            ("tcg_desc_tls", "R_AARCH64_TLSDESC_ADR_PAGE21"),
            ("tcg_desc_word", "R_AARCH64_ADR_GOT_PAGE"),
        ] {
            assert!(
                text.contains(&format!(
                    "trust-cg: error[link:relocation-out-of-range] `{symbol}` ({relocation}): \
                     [TCG-LINK-GOT-PAGE-WINDOW] got_page.o: {relocation} against `{symbol}`"
                )),
                "{symbol}: {text}"
            );
        }
        // `b1_scalars.tmbc` calls nothing, but the lazy descriptor gives
        // the library a PLT header (whose slots are named by no relocation:
        // a conservative refusal) and the TLS descriptor trampoline (whose
        // DT_TLSDESC_GOT word is 8 GiB away: observed).
        assert!(
            text.contains(
                "trust-cg: error[link:unclassified]: [TCG-LINK-GOT-PAGE-UNPROVEN] \
                 linker-generated PLT (DT_JMPREL, an executable `.plt` section): the linker \
                 wrote ADRP instructions that address GOT slots and that no input relocation \
                 describes, and the linked output for libbypass.so is refused"
            ),
            "{text}"
        );
        assert!(
            text.contains(
                "trust-cg: error[link:relocation-out-of-range]: [TCG-LINK-GOT-PAGE-WINDOW] \
                 linker-generated TLS descriptor trampoline (DT_TLSDESC_PLT at "
            ),
            "{text}"
        );
        assert_eq!(text.matches("error[link:").count(), 4, "{text}");
        assert_eq!(listing(dir), before);

        let output = command("libnear.so", 0x8000_0000);
        assert!(output.status.success(), "{}", stderr(&output));
        assert_eq!(user_status(dir, "libnear.so", "user_near").code(), Some(0));
    }

    /// A library user that defines `tcg_desc_bump` (so the library's PLT
    /// entry binds to it) and exits 0 when `tcg_call_desc` returns its 7.
    const DEFS_MAIN: &str = "int tcg_desc_bump(void) { return 7; }\nextern int tcg_call_desc(void);\nint main(void) { return tcg_call_desc() == 7 ? 0 : 1; }\n";

    /// Link [`DEFS_MAIN`] with `-rdynamic` against `dir/library` with the
    /// host `cc` and run the program.
    fn defs_user_status(dir: &Path, library: &str, name: &str) -> std::process::ExitStatus {
        let library = dir.join(library).display().to_string();
        let rpath = format!("-Wl,-rpath,{}", dir.display());
        run_tool(
            dir,
            "cc",
            &["-rdynamic", "-o", name, "defs_main.c", &library, &rpath],
        );
        Command::new(dir.join(name)).status().unwrap()
    }

    /// The closure audit's PLT reproducer: `trust-cg -shared -nostdlib
    /// --relocation-model pic -o libplt.so caller.tmbc
    /// -Wl,--section-start=.got.plt=0x200010000`. No input carries a
    /// GOT-page `ADRP` (the call of the imported `tcg_desc_bump` is an
    /// `R_AARCH64_CALL26`), but GNU ld writes a PLT entry `adrp x16` to the
    /// `R_AARCH64_JUMP_SLOT` slot 8 GiB away without checking the window,
    /// and the library was installed; its user died with SIGSEGV. It is now
    /// refused with exactly one `[TCG-LINK-GOT-PAGE-WINDOW]` naming the PLT
    /// entry, alone and with `.got` placed 8 GiB away too; nothing is
    /// written and a file at the output keeps its bytes. GNU ld links the
    /// same library outside the driver, and the user dies with SIGSEGV.
    /// Twin: with `.got.plt` at 2 GiB the library links through the driver
    /// and the user exits 0.
    #[test]
    fn a_linker_generated_plt_entry_out_of_reach_is_refused_and_its_near_twin_runs() {
        let directory = tempfile::tempdir().unwrap();
        let dir = directory.path();
        write_module(dir, "caller.tmbc", &caller_module());
        compile_pic(dir, "caller.tmbc", "caller.o");
        fs::write(dir.join("defs_main.c"), DEFS_MAIN).unwrap();
        let far_plt = "-Wl,--section-start=.got.plt=0x200010000";
        let far_both = placement(0x2_0000_0000);
        let link = |library: &str, placed: &str| {
            trust_cg(
                dir,
                &[
                    "--shared",
                    "--nostdlib",
                    "--relocation-model",
                    "pic",
                    "-o",
                    library,
                    "caller.tmbc",
                    placed,
                ],
            )
        };
        for (name, placed) in [("plt", far_plt), ("both", far_both.as_str())] {
            let library = format!("lib{name}.so");
            for preexisting in [None, Some(&b"precious\n"[..])] {
                if let Some(bytes) = preexisting {
                    fs::write(dir.join(&library), bytes).unwrap();
                }
                let before = listing(dir);
                let output = link(&library, placed);
                let text = stderr(&output);
                assert!(!output.status.success(), "{name}: {text}");
                assert!(
                    text.contains(&format!(
                        "trust-cg: error[link:relocation-out-of-range] `tcg_desc_bump` \
                         (R_AARCH64_JUMP_SLOT): [TCG-LINK-GOT-PAGE-WINDOW] linker-generated PLT \
                         (1 R_AARCH64_JUMP_SLOT slot(s), DT_JMPREL, an executable `.plt` \
                         section): the PLT entry the linker wrote for `tcg_desc_bump` addresses \
                         its slot through an ADRP page delta that no input relocation describes, \
                         and the linked output for {library} is refused: its \
                         R_AARCH64_JUMP_SLOT slot at 0x200010018"
                    )),
                    "{name}: {text}"
                );
                assert_eq!(text.matches("error[link:").count(), 1, "{name}: {text}");
                assert!(
                    text.contains(&format!(
                        "trust-cg: error: the linked output for {library} was refused and not \
                         installed; the linker's image was removed"
                    )),
                    "{name}: {text}"
                );
                assert_eq!(listing(dir), before, "{name}");
                match preexisting {
                    None => assert!(!dir.join(&library).exists(), "{name}"),
                    Some(bytes) => {
                        assert_eq!(fs::read(dir.join(&library)).unwrap(), bytes, "{name}");
                        fs::remove_file(dir.join(&library)).unwrap();
                    }
                }
            }

            // Without the driver GNU ld links it, and the truncated PLT
            // page delta makes the call jump through the wrong word.
            let raw = format!("lib{name}raw.so");
            run_tool(
                dir,
                "cc",
                &[
                    "-shared",
                    "-nostdlib",
                    "-Wl,-z,noexecstack",
                    "-o",
                    raw.as_str(),
                    "caller.o",
                    placed,
                ],
            );
            let status = defs_user_status(dir, &raw, &format!("user_{name}_raw"));
            assert_eq!(status.signal(), Some(SIGSEGV), "{name}: {status:?}");
        }

        let output = link("libnear.so", "-Wl,--section-start=.got.plt=0x80010000");
        assert!(output.status.success(), "{}", stderr(&output));
        assert_eq!(
            defs_user_status(dir, "libnear.so", "user_near").code(),
            Some(0)
        );
    }

    /// The C driver's own start files carry GOT-page `ADRP`s (on this host
    /// `Scrt1.o`'s against `main`, `crti.o`'s against `__gmon_start__` and
    /// `crtbeginS.o`'s), and no positional input does. An executable with
    /// the C runtime whose `.got` is placed 8 GiB from its code (with
    /// `.data` at 2 GiB, so that GNU ld's own check of the start files'
    /// direct `ADRP`s to `.data` passes) is linked by GNU ld outside the
    /// driver, and it dies with SIGSEGV. Through the CLI it is refused by
    /// name, naming the start files, and nothing is written. With `.got` at
    /// 2 GiB it links and returns 42.
    #[test]
    fn c_runtime_got_page_adrps_are_checked_in_an_executable() {
        let directory = tempfile::tempdir().unwrap();
        let dir = directory.path();
        let answer = {
            let mut mb = ModuleBuilder::new("tcg_got_answer");
            let ty = mb.add_func_type(vec![], vec![Ty::I32]);
            let mut fb = mb.function("main", ty);
            let entry = fb.create_block();
            fb.switch_to_block(entry);
            let value = fb.iconst(Ty::I32, 42);
            fb.ret(vec![value]);
            fb.build();
            mb.build().expect("ModuleBuilder::build: test fixture")
        };
        write_module(dir, "answer.tmbc", &answer);
        let output = trust_cg(dir, &["-c", "-o", "answer.o", "answer.tmbc"]);
        assert!(output.status.success(), "{}", stderr(&output));
        let far = "-Wl,--section-start=.got=0x200000000,--section-start=.data=0x80000000";

        run_tool(
            dir,
            "cc",
            &["-o", "raw", "answer.o", "-Wl,-z,noexecstack", far],
        );
        let status = Command::new(dir.join("raw")).status().unwrap();
        assert_eq!(status.signal(), Some(SIGSEGV), "{status:?}");

        let before = listing(dir);
        let output = trust_cg(dir, &["-o", "prog", "answer.tmbc", far]);
        let text = stderr(&output);
        assert!(!output.status.success(), "{text}");
        // `main` is defined in the executable, so no dynamic relocation names
        // its slot (a conservative refusal); `__gmon_start__`'s slot is named
        // by its `R_AARCH64_GLOB_DAT` (an observed overflow).
        for (code, file, symbol) in [
            ("[TCG-LINK-GOT-PAGE-UNPROVEN]", "Scrt1.o", "main"),
            ("[TCG-LINK-GOT-PAGE-WINDOW]", "crti.o", "__gmon_start__"),
        ] {
            let named = text.lines().any(|line| {
                line.contains(code)
                    && line.contains(&format!(
                        "/{file}: R_AARCH64_ADR_GOT_PAGE against `{symbol}` "
                    ))
                    && line.contains(
                        "the linker loaded this input although it is not a positional input",
                    )
            });
            assert!(named, "{file}: {text}");
        }
        assert!(
            text.contains(
                "trust-cg: error: the linked output for prog was refused and not installed; the \
                 linker's image was removed"
            ),
            "{text}"
        );
        assert_eq!(listing(dir), before);

        let output = trust_cg(
            dir,
            &[
                "-o",
                "prog",
                "answer.tmbc",
                "-Wl,--section-start=.got=0x80000000",
            ],
        );
        assert!(output.status.success(), "{}", stderr(&output));
        assert_eq!(
            Command::new(dir.join("prog")).status().unwrap().code(),
            Some(42)
        );
    }

    /// The b1 conformance fixture, the `--shared` module of the closure
    /// audit's reproducers, copied into `dir`.
    fn copy_b1(dir: &Path) {
        fs::copy(
            Path::new(env!("CARGO_MANIFEST_DIR"))
                .join("../../tests/fixtures/trust_ir_binary_container/conformance/b1_scalars.tmbc"),
            dir.join("b1_scalars.tmbc"),
        )
        .unwrap();
    }

    /// Assemble `source` as `dir/name.s` into `dir/name.o`.
    fn assemble(dir: &Path, name: &str, source: &str) {
        fs::write(dir.join(format!("{name}.s")), source).unwrap();
        run_tool(
            dir,
            "as",
            &["-o", &format!("{name}.o"), &format!("{name}.s")],
        );
    }

    /// A thread-local `name` holding 42 in `.tdata`.
    fn tdata(name: &str) -> String {
        format!(
            "\t.section .tdata,\"awT\",%progbits\n\t.globl {name}\n\t.type {name}, %object\n\t.size \
             {name}, 4\n{name}:\n\t.word 42\n"
        )
    }

    /// A global function `name` with `body` (instructions, one per line).
    fn function(name: &str, body: &str) -> String {
        format!(
            "\t.text\n\t.globl {name}\n\t.type {name}, %function\n{name}:\n{body}\t.size {name}, \
             .-{name}\n"
        )
    }

    /// Link a user of `dir/library` from `source` with the host `cc` and
    /// run it.
    fn c_user_status(
        dir: &Path,
        library: &str,
        name: &str,
        source: &str,
    ) -> std::process::ExitStatus {
        let c = format!("{name}.c");
        fs::write(dir.join(&c), source).unwrap();
        let library = dir.join(library).display().to_string();
        let rpath = format!("-Wl,-rpath,{}", dir.display());
        run_tool(dir, "cc", &["-o", name, &c, &library, &rpath]);
        Command::new(dir.join(name)).output().unwrap().status
    }

    /// One GOT-addressing route the third L02-P10 closure audit found
    /// installed, or its `+-1 MiB` twin: an assembler object linked into
    /// `b1_scalars.tmbc`'s `--shared --nostdlib` library as a `-Wl` operand.
    struct GotKindRoute {
        name: &'static str,
        /// The object refused at the far placement.
        far_source: String,
        /// The object linked at the near placement (`far_source` when the
        /// placement alone differs).
        near_source: String,
        /// `-Wl` placements, far and near (none: the object's own size
        /// places its slots).
        far: Option<&'static str>,
        near: Option<&'static str>,
        /// Each expected refusal: the relocation and the diagnostic prefix
        /// after `trust-cg: error[link:`.
        refusals: Vec<(&'static str, &'static str)>,
        /// The user program, which exits 0 when the access is right.
        user: &'static str,
        /// How GNU ld's own far library's user ends.
        raw_status: fn(std::process::ExitStatus) -> bool,
    }

    /// The closure audit's GOT-addressing routes outside the three page
    /// kinds, through the CLI on GNU ld 2.42: (1) `R_AARCH64_TLSGD_ADR_PAGE21`
    /// (`adrp x0, :tlsgd:gdvar`) with `.got` 8 GiB away, whose library GNU
    /// ld writes with `adrp x0, 0` and whose user reads module 0 and exits
    /// 1; (2) the tiny-model initial-exec load literal
    /// (`R_AARCH64_TLSIE_LD_GOTTPREL_PREL19`) followed by 1.5 MiB of text,
    /// whose user dies with SIGSEGV; and, found with them, (3) the
    /// general-dynamic `ADR` (`TLSGD_ADR_PREL21`, then `__tls_get_addr`) and
    /// (4) the descriptor load literal and `ADR` (`TLSDESC_LD_PREL19`,
    /// `TLSDESC_ADR_PREL21`) with `.got` 16 MiB away, whose users die with
    /// SIGSEGV. Each was installed before this check modeled its kind. Each
    /// is now refused by name, nothing is written and a file already at the
    /// output keeps its bytes; its near twin (the GOT at 2 GiB, 64 KiB of
    /// text, the default placement) links through the CLI and its user
    /// exits 0.
    #[test]
    fn general_dynamic_and_tiny_model_got_accesses_are_refused_and_their_near_twins_run() {
        let directory = tempfile::tempdir().unwrap();
        let dir = directory.path();
        copy_b1(dir);
        let page_gd = function(
            "get_gd",
            "\tadrp x0, :tlsgd:gdvar\n\tadd x0, x0, :tlsgd_lo12:gdvar\n\tldr x0, [x0]\n\tret\n",
        ) + &tdata("gdvar");
        let tiny = |skip: u32| {
            function(
                "get_ie",
                &format!(
                    "\tldr x0, :gottprel:ievar\n\tmrs x1, tpidr_el0\n\tldr w0, [x1, x0]\n\tret\n\t\
                     .skip {skip:#x}\n"
                ),
            ) + &tdata("ievar")
        };
        let adr_gd = function(
            "get_gd21",
            "\tstp x29, x30, [sp, -16]!\n\tmov x29, sp\n\tadr x0, :tlsgd:gdvar21\n\tbl \
             __tls_get_addr\n\tldr w0, [x0]\n\tldp x29, x30, [sp], 16\n\tret\n",
        ) + &tdata("gdvar21");
        let desc = function(
            "get_desc21",
            "\tstp x29, x30, [sp, -16]!\n\tmov x29, sp\n\tldr x1, :tlsdesc:dvar21\n\tadr x0, \
             :tlsdesc:dvar21\n\t.tlsdesccall dvar21\n\tblr x1\n\tmrs x1, tpidr_el0\n\tldr w0, [x1, \
             x0]\n\tldp x29, x30, [sp], 16\n\tret\n",
        ) + &tdata("dvar21");
        let sigsegv = |status: std::process::ExitStatus| status.signal() == Some(SIGSEGV);
        let routes = [
            GotKindRoute {
                name: "gd",
                far_source: page_gd.clone(),
                near_source: page_gd,
                far: Some("-Wl,--section-start=.got=0x200000000"),
                near: Some("-Wl,--section-start=.got=0x80000000"),
                refusals: vec![(
                    "R_AARCH64_TLSGD_ADR_PAGE21",
                    "relocation-out-of-range] `gdvar` (R_AARCH64_TLSGD_ADR_PAGE21): \
                     [TCG-LINK-GOT-PAGE-WINDOW] gd.o: R_AARCH64_TLSGD_ADR_PAGE21 against `gdvar` \
                     addresses a GOT slot through an ADRP page delta, and the linked output for \
                     libgd.so is refused: its R_AARCH64_TLS_DTPMOD64 slot at 0x200000008",
                )],
                user: "#include <stdio.h>\nextern long get_gd(void);\nint main(void) { long m = \
                       get_gd(); printf(\"module=%ld\\n\", m); return m == 0 ? 1 : 0; }\n",
                raw_status: |status| status.code() == Some(1),
            },
            GotKindRoute {
                name: "tie",
                far_source: tiny(0x18_0000),
                near_source: tiny(0x1_0000),
                far: None,
                near: None,
                refusals: vec![(
                    "R_AARCH64_TLSIE_LD_GOTTPREL_PREL19",
                    "unclassified] `ievar` (R_AARCH64_TLSIE_LD_GOTTPREL_PREL19): \
                     [TCG-LINK-GOT-PAGE-UNPROVEN] tie.o: R_AARCH64_TLSIE_LD_GOTTPREL_PREL19 \
                     against `ievar` is a GOT-addressing relocation through a load-literal (LDR) \
                     offset, and the linked output for libtie.so is refused because the check \
                     cannot show that every such access in it is within the +-1 MiB load-literal \
                     window of its GOT slot: ",
                )],
                user: "#include <stdio.h>\nextern int get_ie(void);\nint main(void) { int v = \
                       get_ie(); printf(\"ievar=%d\\n\", v); return v == 42 ? 0 : 1; }\n",
                raw_status: sigsegv,
            },
            GotKindRoute {
                name: "gd21",
                far_source: adr_gd.clone(),
                near_source: adr_gd,
                far: Some("-Wl,--section-start=.got=0x1000000"),
                near: None,
                refusals: vec![(
                    "R_AARCH64_TLSGD_ADR_PREL21",
                    "relocation-out-of-range] `gdvar21` (R_AARCH64_TLSGD_ADR_PREL21): \
                     [TCG-LINK-GOT-PAGE-WINDOW] gd21.o: R_AARCH64_TLSGD_ADR_PREL21 against \
                     `gdvar21` addresses a GOT slot through an ADR offset, and the linked output \
                     for libgd21.so is refused: its R_AARCH64_TLS_DTPMOD64 slot at 0x1000008",
                )],
                user: "#include <stdio.h>\nextern int get_gd21(void);\nint main(void) { int v = \
                       get_gd21(); printf(\"gdvar21=%d\\n\", v); return v == 42 ? 0 : 1; }\n",
                raw_status: sigsegv,
            },
            GotKindRoute {
                name: "desc21",
                far_source: desc.clone(),
                near_source: desc,
                far: Some("-Wl,--section-start=.got=0x1000000"),
                near: None,
                refusals: vec![
                    (
                        "R_AARCH64_TLSDESC_LD_PREL19",
                        "relocation-out-of-range] `dvar21` (R_AARCH64_TLSDESC_LD_PREL19): \
                         [TCG-LINK-GOT-PAGE-WINDOW] desc21.o: R_AARCH64_TLSDESC_LD_PREL19 \
                         against `dvar21` addresses a GOT slot through a load-literal (LDR) \
                         offset, and the linked output for libdesc21.so is refused: its \
                         R_AARCH64_TLSDESC slot at 0x10",
                    ),
                    (
                        "R_AARCH64_TLSDESC_ADR_PREL21",
                        "relocation-out-of-range] `dvar21` (R_AARCH64_TLSDESC_ADR_PREL21): \
                         [TCG-LINK-GOT-PAGE-WINDOW] desc21.o: R_AARCH64_TLSDESC_ADR_PREL21 \
                         against `dvar21` addresses a GOT slot through an ADR offset, and the \
                         linked output for libdesc21.so is refused: its R_AARCH64_TLSDESC slot \
                         at 0x10",
                    ),
                ],
                user: "#include <stdio.h>\nextern int get_desc21(void);\nint main(void) { int v = \
                       get_desc21(); printf(\"dvar21=%d\\n\", v); return v == 42 ? 0 : 1; }\n",
                raw_status: sigsegv,
            },
        ];
        for route in routes {
            let name = route.name;
            let near_name = format!("{name}_near");
            assemble(dir, name, &route.far_source);
            assemble(dir, &near_name, &route.near_source);
            let link = |object: &str, library: &str, placed: Option<&str>| {
                let operand = format!("-Wl,{object}.o");
                let mut args = vec![
                    "-shared",
                    "-nostdlib",
                    "--relocation-model",
                    "pic",
                    operand.as_str(),
                    "-o",
                    library,
                    "b1_scalars.tmbc",
                ];
                args.extend(placed);
                trust_cg(dir, &args)
            };
            let library = format!("lib{name}.so");
            for preexisting in [None, Some(&b"precious\n"[..])] {
                if let Some(bytes) = preexisting {
                    fs::write(dir.join(&library), bytes).unwrap();
                }
                let before = listing(dir);
                let output = link(name, &library, route.far);
                let text = stderr(&output);
                assert!(!output.status.success(), "{name}: {text}");
                for (relocation, prefix) in &route.refusals {
                    assert!(
                        text.contains(&format!("trust-cg: error[link:{prefix}")),
                        "{name} {relocation}: {text}"
                    );
                }
                assert_eq!(
                    text.matches("error[link:").count(),
                    route.refusals.len(),
                    "{name}: {text}"
                );
                assert!(
                    text.contains(&format!(
                        "trust-cg: error: the linked output for {library} was refused and not \
                         installed; the linker's image was removed"
                    )),
                    "{name}: {text}"
                );
                assert_eq!(listing(dir), before, "{name}");
                match preexisting {
                    None => assert!(!dir.join(&library).exists(), "{name}"),
                    Some(bytes) => {
                        assert_eq!(fs::read(dir.join(&library)).unwrap(), bytes, "{name}");
                        fs::remove_file(dir.join(&library)).unwrap();
                    }
                }
            }

            // GNU ld links the same object outside the driver and truncates
            // the access.
            let raw = format!("lib{name}raw.so");
            let object = format!("{name}.o");
            let mut args = vec![
                "-shared",
                "-nostdlib",
                "-Wl,-z,noexecstack",
                "-o",
                raw.as_str(),
                object.as_str(),
            ];
            args.extend(route.far);
            run_tool(dir, "cc", &args);
            let status = c_user_status(dir, &raw, &format!("user_{name}_raw"), route.user);
            assert!((route.raw_status)(status), "{name}: {status:?}");

            let near_library = format!("lib{near_name}.so");
            let output = link(&near_name, &near_library, route.near);
            assert!(output.status.success(), "{name}: {}", stderr(&output));
            let status =
                c_user_status(dir, &near_library, &format!("user_{near_name}"), route.user);
            assert_eq!(status.code(), Some(0), "{name}: {status:?}");
        }
    }

    /// `_start` applies the static image's `IRELATIVE` relocations between
    /// `__rela_iplt_start` and `__rela_iplt_end` itself, then calls the IFUNC
    /// `myfunc` (whose resolver returns `impl`, which returns 42) through
    /// the IPLT and exits with its value.
    const IFUNC_SOURCE: &str = "\t.text\n\t.globl _start\n\t.type _start, %function\n_start:\n\t\
        adrp x19, __rela_iplt_start\n\tadd x19, x19, :lo12:__rela_iplt_start\n\tadrp x20, \
        __rela_iplt_end\n\tadd x20, x20, :lo12:__rela_iplt_end\n1:\tcmp x19, x20\n\tb.hs 2f\n\tldr \
        x21, [x19]\n\tldr x0, [x19, #16]\n\tblr x0\n\tstr x0, [x21]\n\tadd x19, x19, #24\n\tb 1b\n2:\t\
        bl myfunc\n\tmov x8, #93\n\tsvc #0\n\t.size _start, .-_start\n\t.globl myfunc\n\t.type myfunc, \
        %gnu_indirect_function\nmyfunc:\n\tadr x0, impl\n\tret\nimpl:\n\tmov x0, #42\n\tret\n\t\
        .section .rodata\n\t.globl ro_word\nro_word:\n\t.xword 0x1234\n";

    /// A linker script that merges `.iplt` into `.text` and `.rela.iplt`
    /// into the `PROGBITS` `.rodata` (so the image shows neither), and
    /// places the GOT and data at `data`.
    fn merging_script(data: u64) -> String {
        format!(
            "ENTRY(_start)\nSECTIONS {{\n  . = 0x400000;\n  .text : {{ *(.text*) *(.iplt) }}\n  \
             .rodata : {{ *(.rodata*) PROVIDE_HIDDEN(__rela_iplt_start = .); *(.rela.iplt) \
             PROVIDE_HIDDEN(__rela_iplt_end = .); }}\n  .eh_frame : {{ *(.eh_frame) }}\n  . = \
             {data:#x};\n  .data : {{ *(.got.plt) *(.igot.plt) *(.got) *(.data*) }}\n  .bss : {{ \
             *(.bss*) }}\n}}\n"
        )
    }

    /// The closure audit's hidden-IPLT routes: a static `--nostdlib` program
    /// with the IFUNC object `ifunc.o` as a `-Wl` operand, whose GOT slot GNU
    /// ld places 8 GiB from its IPLT and reaches with `adrp x16, 0`. With a
    /// script that merges `.iplt` into `.text` and `.rela.iplt` into a
    /// `PROGBITS` `.rodata`, and with `-z nosectionheader`, the image shows
    /// no linker-written code, and both were installed. The IFUNC definition
    /// now refuses each (one `[TCG-LINK-GOT-PAGE-UNPROVEN]` naming `myfunc`),
    /// nothing is written, and GNU ld's own programs die with SIGSEGV. With
    /// section headers and the default script the IPLT is visible too
    /// (three refusals). Twins: with the slots at 2 GiB, the script and the
    /// default placement are shown in reach (no GOT-page refusal), and
    /// outside the driver GNU ld's programs return 42; without a section
    /// header table the program is refused at 2 GiB as well (no image
    /// without one is shown in reach). Since the v5 verifier's repair every
    /// one of these images is also refused as
    /// `[TCG-LINK-IRELATIVE-UNAPPLIED]`, the twins by that alone: its
    /// `_start` applies its own `IRELATIVE` relocations, and only glibc's
    /// applier from the C driver's own `libc.a`, with its own start file, is
    /// taken to (a conservative refusal).
    #[test]
    fn a_hidden_iplt_is_refused_through_its_ifunc_definition_and_its_near_twins_run() {
        let directory = tempfile::tempdir().unwrap();
        let dir = directory.path();
        fs::write(dir.join("ifunc.s"), IFUNC_SOURCE).unwrap();
        run_tool(dir, "as", &["-o", "ifunc.o", "ifunc.s"]);
        let helper = {
            let mut mb = ModuleBuilder::new("tcg_helper");
            let ty = mb.add_func_type(vec![], vec![Ty::I32]);
            let mut fb = mb.function("tcg_helper", ty);
            let entry = fb.create_block();
            fb.switch_to_block(entry);
            let value = fb.iconst(Ty::I32, 1);
            fb.ret(vec![value]);
            fb.build();
            mb.build().expect("ModuleBuilder::build: test fixture")
        };
        write_module(dir, "helper.tmbc", &helper);
        for data in [0x2_0000_0000u64, 0x8000_0000] {
            fs::write(
                dir.join(format!("script_{data:#x}.ld")),
                merging_script(data),
            )
            .unwrap();
        }
        let link = |program: &str, placed: &[String]| {
            let mut args = vec![
                "--static",
                "--nostdlib",
                "--no-pie",
                "-Wl,ifunc.o",
                "-o",
                program,
                "helper.tmbc",
            ];
            args.extend(placed.iter().map(String::as_str));
            trust_cg(dir, &args)
        };
        let script = |data: u64| vec![format!("-Wl,-T,script_{data:#x}.ld")];
        let placed = |got_plt: u64, headers: bool| {
            let mut args = vec![format!("-Wl,--section-start=.got.plt={got_plt:#x}")];
            if !headers {
                args.push("-Wl,-z,nosectionheader".to_string());
            }
            args
        };
        let irelative = |program: &str| {
            format!(
                "trust-cg: error[link:unclassified] (R_AARCH64_IRELATIVE): \
                 [TCG-LINK-IRELATIVE-UNAPPLIED] the linked output for {program} is refused \
                 because it is a static executable with IFUNC relocations ("
            )
        };
        let ifunc_refusal = |program: &str| {
            format!(
                "trust-cg: error[link:unclassified] `myfunc` (STT_GNU_IFUNC): \
                 [TCG-LINK-GOT-PAGE-UNPROVEN] ifunc.o: `myfunc` is an IFUNC (STT_GNU_IFUNC) it \
                 defines, whose PLT or IPLT entry the linker writes with an ADRP to the entry's \
                 GOT slot, and the linked output for {program} is refused because the check \
                 cannot show that every GOT-page ADRP in it is within the +-4 GiB page window of \
                 its GOT slot: "
            )
        };
        for (name, far, count) in [
            ("script", script(0x2_0000_0000), 1),
            ("nsh", placed(0x2_0000_0000, false), 1),
            ("sh", placed(0x2_0000_0000, true), 3),
        ] {
            let program = format!("prog_{name}");
            for preexisting in [None, Some(&b"precious\n"[..])] {
                if let Some(bytes) = preexisting {
                    fs::write(dir.join(&program), bytes).unwrap();
                }
                let before = listing(dir);
                let output = link(&program, &far);
                let text = stderr(&output);
                assert!(!output.status.success(), "{name}: {text}");
                assert!(text.contains(&ifunc_refusal(&program)), "{name}: {text}");
                assert!(text.contains(&irelative(&program)), "{name}: {text}");
                assert_eq!(
                    text.matches("error[link:").count(),
                    count + 1,
                    "{name}: {text}"
                );
                if name == "sh" {
                    for code in [
                        "[TCG-LINK-GOT-PAGE-UNPROVEN] linker-generated PLT (an executable \
                         `.plt` section)",
                        "[TCG-LINK-GOT-PAGE-UNPROVEN] linker-generated IFUNC PLT (IPLT) (1 \
                         R_AARCH64_IRELATIVE slot(s))",
                    ] {
                        assert!(text.contains(code), "{name}: {text}");
                    }
                }
                assert_eq!(listing(dir), before, "{name}");
                match preexisting {
                    None => assert!(!dir.join(&program).exists(), "{name}"),
                    Some(bytes) => {
                        assert_eq!(fs::read(dir.join(&program)).unwrap(), bytes, "{name}");
                        fs::remove_file(dir.join(&program)).unwrap();
                    }
                }
            }
            // GNU ld links it outside the driver, and the IPLT's truncated
            // `adrp x16` jumps through the wrong word.
            let raw = format!("raw_{name}");
            let mut args = vec![
                "-static",
                "-nostdlib",
                "-no-pie",
                "-Wl,-z,noexecstack",
                "-o",
                raw.as_str(),
                "ifunc.o",
            ];
            args.extend(far.iter().map(String::as_str));
            run_tool(dir, "cc", &args);
            let status = Command::new(dir.join(&raw)).status().unwrap();
            assert_eq!(status.signal(), Some(SIGSEGV), "{name}: {status:?}");
        }

        // The near twins: shown in reach, refused only because the program
        // applies its own IFUNC relocations; GNU ld's run.
        for (name, near) in [
            ("script_near", script(0x8000_0000)),
            ("sh_near", placed(0x8000_0000, true)),
        ] {
            let before = listing(dir);
            let output = link(name, &near);
            let text = stderr(&output);
            assert!(!output.status.success(), "{name}: {text}");
            let lines: Vec<&str> = text
                .lines()
                .filter(|line| line.contains("error[link:"))
                .collect();
            assert!(
                lines.len() == 1 && lines[0].starts_with(&irelative(name)),
                "{name}: {text}"
            );
            assert_eq!(listing(dir), before, "{name}");
            let raw = format!("raw_{name}");
            let mut args = vec![
                "-static",
                "-nostdlib",
                "-no-pie",
                "-Wl,-z,noexecstack",
                "-o",
                raw.as_str(),
                "ifunc.o",
            ];
            args.extend(near.iter().map(String::as_str));
            run_tool(dir, "cc", &args);
            let status = Command::new(dir.join(&raw)).status().unwrap();
            assert_eq!(status.code(), Some(42), "{raw}: {status:?}");
        }
        // Without a section header table no image is shown in reach.
        let output = link("nsh_near", &placed(0x8000_0000, false));
        let text = stderr(&output);
        assert!(!output.status.success(), "{text}");
        assert!(
            text.contains(&ifunc_refusal("nsh_near"))
                && text.contains("it has no section header table"),
            "{text}"
        );
        assert!(!dir.join("nsh_near").exists());
    }

    /// The directory holding `ld.lld` for `cc -fuse-ld=lld -B<dir>`:
    /// `TCG_LLD_DIR`, else `~/.local/bin`, else the first `PATH` entry with
    /// one (the convention of `e2e_aarch64_elf_tlsie`). `TCG_REQUIRE_LLD`
    /// turns a missing LLD into a failure; otherwise the LLD legs are
    /// skipped with a `SKIP:` line and the GNU ld legs still run.
    fn lld_dir() -> Option<PathBuf> {
        let found = std::env::var_os("TCG_LLD_DIR")
            .map(PathBuf::from)
            .or_else(|| std::env::var_os("HOME").map(|home| Path::new(&home).join(".local/bin")))
            .filter(|dir| dir.join("ld.lld").is_file())
            .or_else(|| {
                std::env::var_os("PATH").and_then(|paths| {
                    std::env::split_paths(&paths).find(|dir| dir.join("ld.lld").is_file())
                })
            });
        if found.is_none() {
            assert!(
                std::env::var_os("TCG_REQUIRE_LLD").is_none(),
                "TCG_REQUIRE_LLD is set but no ld.lld was found"
            );
            eprintln!(
                "SKIP: no ld.lld (TCG_LLD_DIR, ~/.local/bin, PATH); the LLD legs of the GOT-base \
                 control did not run"
            );
        }
        found
    }

    /// A directory holding a `cc` that runs the host `cc` with
    /// `-fuse-ld=lld`, for a `PATH` the CLI's link step (which runs `cc`)
    /// then links with LLD through; `ld.lld` is linked into a private
    /// directory for `-B`, so no other tool in `lld` is picked up.
    fn lld_cc(dir: &Path, lld: &Path) -> PathBuf {
        let host_cc = std::env::var_os("PATH")
            .and_then(|paths| {
                std::env::split_paths(&paths)
                    .map(|dir| dir.join("cc"))
                    .find(|cc| cc.is_file())
            })
            .expect("a host cc on PATH");
        let tools = dir.join("lld-tools");
        let bin = dir.join("lld-cc");
        fs::create_dir(&tools).unwrap();
        fs::create_dir(&bin).unwrap();
        std::os::unix::fs::symlink(lld.join("ld.lld"), tools.join("ld.lld")).unwrap();
        let cc = bin.join("cc");
        write_executable_script(
            &cc,
            &format!(
                "#!/bin/sh\nexec '{}' -fuse-ld=lld -B'{}/' \"$@\"\n",
                host_cc.display(),
                tools.display()
            ),
        );
        bin
    }

    /// Run the CLI in `dir` with `bin` first on `PATH` (so its link step's
    /// `cc` is the one in `bin`).
    fn trust_cg_on(bin: Option<&Path>, dir: &Path, args: &[&str]) -> Output {
        let mut command = Command::new(env!("CARGO_BIN_EXE_trust-cg"));
        command.arg("--permit-unlicensed"); // Claim-less fixtures: refused by default since WS7.5 (DG-73).
        command.current_dir(dir).args(args);
        if let Some(bin) = bin {
            let mut paths = vec![bin.to_path_buf()];
            paths.extend(std::env::split_paths(
                &std::env::var_os("PATH").unwrap_or_default(),
            ));
            command.env("PATH", std::env::join_paths(paths).unwrap());
        }
        command.output().expect("run trust-cg")
    }

    /// `touch` loads `count` GOT slots (`adrp :got:`, `ldr :got_lo12:` against
    /// `dv_0`..), then `f_gb` loads `dv_last` (4242) through its GOT slot the
    /// way GCC's small-PIC model (`-fpic`) does: `adrp x28,
    /// _GLOBAL_OFFSET_TABLE_` and `ldr x0, [x28, #:gotpage_lo15:dv_last]`
    /// (`R_AARCH64_LD64_GOTPAGE_LO15`, `G(GDAT(S)) - Page(GOT)`, `0 <= X <
    /// 2^15`). The verifier's `gb.s` is the 6,000-slot one.
    fn got_page_lo15_source(count: usize) -> String {
        let mut source =
            String::from("\t.text\n\t.globl touch\n\t.type touch, %function\ntouch:\n");
        for index in 0..count {
            source +=
                &format!("\tadrp x1, :got:dv_{index}\n\tldr x1, [x1, #:got_lo12:dv_{index}]\n");
        }
        source += "\tret\n\t.size touch, .-touch\n\t.globl f_gb\n\t.type f_gb, %function\nf_gb:\n\t\
                   adrp x28, _GLOBAL_OFFSET_TABLE_\n\tldr x0, [x28, #:gotpage_lo15:dv_last]\n\tldr \
                   x0, [x0]\n\tret\n\t.size f_gb, .-f_gb\n\t.data\n";
        for index in 0..count {
            source += &format!("\t.globl dv_{index}\ndv_{index}:\n\t.xword {index}\n");
        }
        source + "\t.globl dv_last\ndv_last:\n\t.xword 4242\n"
    }

    /// The user of `f_gb`: prints its value and exits 0 when it is 4242.
    const GB_USER: &str = "#include <stdio.h>\nextern long f_gb(void);\nint main(void) { long v = \
                           f_gb(); printf(\"f_gb=%ld\\n\", v); return v == 4242 ? 0 : 1; }\n";

    /// A static `-nostdlib` program: `_start` applies the `IRELATIVE`
    /// relocations between `__rela_iplt_start` and `__rela_iplt_end`, then
    /// loads the IFUNC `myfunc`'s GOT slot through
    /// `R_AARCH64_LD64_GOTPAGE_LO15`, calls it (its resolver returns `impl`,
    /// which returns 42) and exits with its value. LLD 22 gives the GOT
    /// reference a slot in `.got.plt`, 64 KiB above `.got`, and writes its
    /// offset truncated; GNU ld 2.42 gives it a slot next to `.got`.
    const IFUNC_GOTPAGE_SOURCE: &str = "\t.text\n\t.globl _start\n\t.type _start, %function\n\
        _start:\n\tadrp x19, __rela_iplt_start\n\tadd x19, x19, :lo12:__rela_iplt_start\n\tadrp \
        x20, __rela_iplt_end\n\tadd x20, x20, :lo12:__rela_iplt_end\n1:\tcmp x19, x20\n\tb.hs 2f\n\t\
        ldr x21, [x19]\n\tldr x0, [x19, #16]\n\tblr x0\n\tstr x0, [x21]\n\tadd x19, x19, #24\n\tb \
        1b\n2:\tadrp x28, _GLOBAL_OFFSET_TABLE_\n\tldr x1, [x28, #:gotpage_lo15:myfunc]\n\tblr x1\n\t\
        mov x8, #93\n\tsvc #0\n\t.size _start, .-_start\n\t.globl myfunc\n\t.type myfunc, \
        %gnu_indirect_function\nmyfunc:\n\tadr x0, impl\n\tret\nimpl:\n\tmov x0, #42\n\tret\n";

    /// Run `program` and return its exit code and standard output.
    fn run_program(program: &Path) -> (Option<i32>, String) {
        let output = Command::new(program).output().unwrap();
        (
            output.status.code(),
            String::from_utf8_lossy(&output.stdout).into_owned(),
        )
    }

    /// The independent verifier's L02-P10 GOT-base finding:
    /// `R_AARCH64_LD64_GOTPAGE_LO15` was exempted as a GOT-base form the
    /// linker checks, but LLD 22 writes it truncated to 15 bits. With 6,000
    /// GOT slots `dv_last`'s slot is `X = 48528` above the page of
    /// `_GLOBAL_OFFSET_TABLE_`, and LLD's library (`trust-cg -shared
    /// -nostdlib --relocation-model pic -Wl,gb.o -o libgb.so
    /// b1_scalars.tmbc` with LLD's `cc` first on `PATH`) and PIE (`-Wl,gb.o,
    /// gb_user.o`) were installed; their user read another slot and exited
    /// with status 1. Now LLD's library is refused as an observed overflow (the slot's
    /// `GLOB_DAT` names it, one `[TCG-LINK-GOT-PAGE-WINDOW]`) and its PIE as
    /// unproven (a `RELATIVE` slot names no symbol,
    /// `[TCG-LINK-GOT-PAGE-UNPROVEN]`); nothing is written and a file at the
    /// output keeps its bytes. LLD outside the driver links both and their
    /// users print a value other than 4242. GNU ld 2.42 checks the window:
    /// it refuses such a link or writes the slot in range (its library's
    /// user prints 4242); the driver refused its 48 KiB-GOT library
    /// conservatively until the tenth closure audit, and now installs what
    /// GNU ld links (its user prints 4242). Twin: with 100 slots each
    /// linker's library and PIE link through the driver and print 4242. A static program's GOT
    /// reference to an IFUNC (`IFUNC_GOTPAGE_SOURCE`) is refused through
    /// LLD (its `IRELATIVE` slot is 64 KiB above the page of the GOT base;
    /// LLD's own program dies with SIGSEGV), and GNU ld, which keeps the
    /// slot in reach, links a program that returns 42 outside the driver.
    /// Since the v5 verifier's repair each is also refused as
    /// `[TCG-LINK-IRELATIVE-UNAPPLIED]` (GNU ld's by that alone): its
    /// `_start` applies its own `IRELATIVE` relocations, and only glibc's
    /// applier is taken to (a conservative refusal). Without LLD the LLD
    /// legs are skipped (`SKIP:`) and the GNU ld legs run.
    #[test]
    fn an_ld64_gotpage_lo15_access_out_of_the_got_window_is_refused_and_its_near_twin_runs() {
        let directory = tempfile::tempdir().unwrap();
        let dir = directory.path();
        copy_b1(dir);
        let helper = {
            let mut mb = ModuleBuilder::new("tcg_helper");
            let ty = mb.add_func_type(vec![], vec![Ty::I32]);
            let mut fb = mb.function("tcg_helper", ty);
            let entry = fb.create_block();
            fb.switch_to_block(entry);
            let value = fb.iconst(Ty::I32, 1);
            fb.ret(vec![value]);
            fb.build();
            mb.build().expect("ModuleBuilder::build: test fixture")
        };
        write_module(dir, "helper.tmbc", &helper);
        fs::write(dir.join("gb.s"), got_page_lo15_source(6000)).unwrap();
        fs::write(dir.join("gb_near.s"), got_page_lo15_source(100)).unwrap();
        run_tool(dir, "as", &["-o", "gb.o", "gb.s"]);
        run_tool(dir, "as", &["-o", "gb_near.o", "gb_near.s"]);
        fs::write(dir.join("gb_user.c"), GB_USER).unwrap();
        run_tool(dir, "cc", &["-c", "-O1", "-o", "gb_user.o", "gb_user.c"]);
        fs::write(dir.join("ifunc_gotpage.s"), IFUNC_GOTPAGE_SOURCE).unwrap();
        run_tool(dir, "as", &["-o", "ifunc_gotpage.o", "ifunc_gotpage.s"]);
        let lld = lld_dir().map(|lld| lld_cc(dir, &lld));
        let irelative = |program: &str| {
            format!(
                "trust-cg: error[link:unclassified] (R_AARCH64_IRELATIVE): \
                 [TCG-LINK-IRELATIVE-UNAPPLIED] the linked output for {program} is refused \
                 because it is a static executable with IFUNC relocations (it holds 1 \
                 R_AARCH64_IRELATIVE relocation) and no member of the C driver's own libc.a"
            )
        };
        let ifunc_static = |program: &str| {
            vec![
                "--static".to_string(),
                "--nostdlib".into(),
                "--no-pie".into(),
                "-Wl,ifunc_gotpage.o".into(),
                "-o".into(),
                program.to_string(),
                "helper.tmbc".into(),
            ]
        };
        let shared = |object: &str, library: &str| {
            vec![
                "-shared".to_string(),
                "-nostdlib".into(),
                "--relocation-model".into(),
                "pic".into(),
                format!("-Wl,{object}"),
                "-o".into(),
                library.to_string(),
                "b1_scalars.tmbc".into(),
            ]
        };
        let pie = |object: &str, program: &str| {
            vec![
                format!("-Wl,{object},gb_user.o"),
                "-o".to_string(),
                program.to_string(),
                "helper.tmbc".into(),
            ]
        };
        let cli = |bin: Option<&Path>, args: &[String]| {
            trust_cg_on(
                bin,
                dir,
                &args.iter().map(String::as_str).collect::<Vec<_>>(),
            )
        };
        let user_of = |library: &str, name: &str| {
            let library = dir.join(library).display().to_string();
            let rpath = format!("-Wl,-rpath,{}", dir.display());
            run_tool(dir, "cc", &["-o", name, "gb_user.o", &library, &rpath]);
            run_program(&dir.join(name))
        };
        // Refused with nothing written, with and without a file at the
        // output; `expect` is each whole `error[link:` line's prefix.
        let refused = |bin: Option<&Path>, args: &[String], output: &str, expect: &[&str]| {
            for preexisting in [None, Some(&b"precious\n"[..])] {
                if let Some(bytes) = preexisting {
                    fs::write(dir.join(output), bytes).unwrap();
                }
                let before = listing(dir);
                let result = cli(bin, args);
                let text = stderr(&result);
                assert!(!result.status.success(), "{output}: {text}");
                assert_eq!(
                    text.matches("error[link:").count(),
                    expect.len(),
                    "{output}: {text}"
                );
                for prefix in expect {
                    assert!(
                        text.lines().any(|line| line.starts_with(prefix)),
                        "{output}: {prefix}\n{text}"
                    );
                }
                assert_eq!(listing(dir), before, "{output}");
                match preexisting {
                    None => assert!(!dir.join(output).exists(), "{output}"),
                    Some(bytes) => {
                        assert_eq!(fs::read(dir.join(output)).unwrap(), bytes, "{output}");
                        fs::remove_file(dir.join(output)).unwrap();
                    }
                }
            }
        };
        let window = |library: &str| {
            format!(
                "trust-cg: error[link:relocation-out-of-range] `dv_last` \
                 (R_AARCH64_LD64_GOTPAGE_LO15): [TCG-LINK-GOT-PAGE-WINDOW] gb.o: \
                 R_AARCH64_LD64_GOTPAGE_LO15 against `dv_last` addresses a GOT slot through an \
                 LDR offset from the page of the GOT base, and the linked output for {library} is \
                 refused: the GOT base `_GLOBAL_OFFSET_TABLE_` is at "
            )
        };
        let unproven = |output: &str| {
            format!(
                "trust-cg: error[link:unclassified] `dv_last` (R_AARCH64_LD64_GOTPAGE_LO15): \
                 [TCG-LINK-GOT-PAGE-UNPROVEN] gb.o: R_AARCH64_LD64_GOTPAGE_LO15 against `dv_last` \
                 is a GOT-addressing relocation through an LDR offset from the page of the GOT \
                 base, and the linked output for {output} is refused because the check cannot \
                 show that every such access in it addresses a GOT slot within the 32 KiB window \
                 above the page of the GOT base: the GOT base `_GLOBAL_OFFSET_TABLE_` is at "
            )
        };

        if let Some(bin) = lld.as_deref() {
            // The verifier's library and PIE through LLD.
            let window_line = window("libgb_lld.so");
            refused(
                Some(bin),
                &shared("gb.o", "libgb_lld.so"),
                "libgb_lld.so",
                &[&window_line],
            );
            let unproven_line = unproven("gb_pie_lld");
            refused(
                Some(bin),
                &pie("gb.o", "gb_pie_lld"),
                "gb_pie_lld",
                &[&unproven_line],
            );
            // LLD outside the driver writes the offset truncated.
            let lld_cc = bin.join("cc").display().to_string();
            run_tool(
                dir,
                &lld_cc,
                &[
                    "-shared",
                    "-nostdlib",
                    "-Wl,-z,noexecstack",
                    "-o",
                    "libgb_raw.so",
                    "gb.o",
                ],
            );
            let (code, stdout) = user_of("libgb_raw.so", "user_raw_lld");
            assert_eq!(code, Some(1), "{stdout}");
            assert!(
                stdout.starts_with("f_gb=") && stdout != "f_gb=4242\n",
                "{stdout}"
            );
            run_tool(dir, &lld_cc, &["-o", "gb_raw_pie", "gb.o", "gb_user.o"]);
            let (code, stdout) = run_program(&dir.join("gb_raw_pie"));
            assert_eq!(code, Some(1), "{stdout}");
            assert!(
                stdout.starts_with("f_gb=") && stdout != "f_gb=4242\n",
                "{stdout}"
            );
            // A static program's GOT reference to an IFUNC: LLD puts the
            // slot in `.got.plt`, 64 KiB above `.got`.
            let ifunc_line = format!(
                "trust-cg: error[link:unclassified] `myfunc` (R_AARCH64_LD64_GOTPAGE_LO15): \
                 [TCG-LINK-GOT-PAGE-UNPROVEN] ifunc_gotpage.o: R_AARCH64_LD64_GOTPAGE_LO15 \
                 against `myfunc` is a GOT-addressing relocation through an LDR offset from the \
                 page of the GOT base, and the linked output for {} is refused because the \
                 check cannot show that every such access in it addresses a GOT slot within the \
                 32 KiB window above the page of the GOT base: the GOT base \
                 `_GLOBAL_OFFSET_TABLE_` is at ",
                "ifunc_lld"
            );
            refused(
                Some(bin),
                &ifunc_static("ifunc_lld"),
                "ifunc_lld",
                &[&ifunc_line, &irelative("ifunc_lld")],
            );
            run_tool(
                dir,
                &lld_cc,
                &[
                    "-static",
                    "-nostdlib",
                    "-no-pie",
                    "-Wl,-z,noexecstack",
                    "-o",
                    "ifunc_raw_lld",
                    "ifunc_gotpage.o",
                ],
            );
            let status = Command::new(dir.join("ifunc_raw_lld")).status().unwrap();
            assert_eq!(status.signal(), Some(SIGSEGV), "{status:?}");
            // The twin links through LLD and runs.
            let output = cli(Some(bin), &shared("gb_near.o", "libgb_near_lld.so"));
            assert!(output.status.success(), "{}", stderr(&output));
            assert_eq!(
                user_of("libgb_near_lld.so", "user_near_lld"),
                (Some(0), "f_gb=4242\n".to_string())
            );
            let output = cli(Some(bin), &pie("gb_near.o", "gb_near_pie_lld"));
            assert!(output.status.success(), "{}", stderr(&output));
            assert_eq!(
                run_program(&dir.join("gb_near_pie_lld")),
                (Some(0), "f_gb=4242\n".to_string())
            );
        }

        // GNU ld checks the window: it refuses the link, or writes the slot
        // in range, and never installs a truncated offset. Since the tenth
        // closure audit the driver leaves that window to GNU ld (as it does
        // a direct ADRP's): a library or PIE GNU ld links is installed and
        // its user prints 4242, and one it refuses is refused by name.
        let raw = Command::new("cc")
            .current_dir(dir)
            .args([
                "-shared",
                "-nostdlib",
                "-Wl,-z,noexecstack",
                "-o",
                "libgb_gnu_raw.so",
                "gb.o",
            ])
            .output()
            .unwrap();
        if raw.status.success() {
            assert_eq!(
                user_of("libgb_gnu_raw.so", "user_raw_gnu"),
                (Some(0), "f_gb=4242\n".to_string())
            );
        } else {
            assert!(
                stderr(&raw).contains("relocation truncated to fit: R_AARCH64_LD64_GOTPAGE_LO15"),
                "{}",
                stderr(&raw)
            );
        }
        for (args, output) in [
            (shared("gb.o", "libgb_gnu.so"), "libgb_gnu.so"),
            (pie("gb.o", "gb_pie_gnu"), "gb_pie_gnu"),
        ] {
            let before = listing(dir);
            let result = cli(None, &args);
            let text = stderr(&result);
            if result.status.success() {
                let (code, stdout) = if output.ends_with(".so") {
                    user_of(output, "user_gnu_installed")
                } else {
                    run_program(&dir.join(output))
                };
                assert_eq!(
                    (code, stdout.as_str()),
                    (Some(0), "f_gb=4242\n"),
                    "{output}"
                );
                continue;
            }
            assert!(
                text.contains(
                    "error[link:relocation-out-of-range] `dv_last` \
                     (R_AARCH64_LD64_GOTPAGE_LO15): "
                ) && text.contains("relocation truncated to fit: R_AARCH64_LD64_GOTPAGE_LO15"),
                "{output}: {text}"
            );
            assert_eq!(listing(dir), before, "{output}");
        }
        // The twin links through GNU ld and runs.
        let output = cli(None, &shared("gb_near.o", "libgb_near_gnu.so"));
        assert!(output.status.success(), "{}", stderr(&output));
        assert_eq!(
            user_of("libgb_near_gnu.so", "user_near_gnu"),
            (Some(0), "f_gb=4242\n".to_string())
        );
        let output = cli(None, &pie("gb_near.o", "gb_near_pie_gnu"));
        assert!(output.status.success(), "{}", stderr(&output));
        assert_eq!(
            run_program(&dir.join("gb_near_pie_gnu")),
            (Some(0), "f_gb=4242\n".to_string())
        );
        // GNU ld keeps the static IFUNC slot next to `.got`: no GOT-page
        // refusal; the program applies its own IFUNC relocations, and GNU
        // ld's program outside the driver returns 42.
        refused(
            None,
            &ifunc_static("ifunc_gnu"),
            "ifunc_gnu",
            &[&irelative("ifunc_gnu")],
        );
        run_tool(
            dir,
            "cc",
            &[
                "-static",
                "-nostdlib",
                "-no-pie",
                "-Wl,-z,noexecstack",
                "-o",
                "ifunc_raw_gnu",
                "ifunc_gotpage.o",
            ],
        );
        assert_eq!(
            Command::new(dir.join("ifunc_raw_gnu"))
                .status()
                .unwrap()
                .code(),
            Some(42)
        );
    }

    /// A directory holding a `cc` that runs the host `cc` with
    /// `-fuse-ld=gold`, or `None` (with a `SKIP:` line) when gold 2.42 is
    /// not installed as `ld.gold` on `PATH` or in `/usr/bin`.
    /// `TCG_REQUIRE_GOLD` turns a missing gold into a failure.
    fn gold_cc(dir: &Path) -> Option<PathBuf> {
        let found = std::env::var_os("PATH")
            .and_then(|paths| {
                std::env::split_paths(&paths).find(|dir| dir.join("ld.gold").is_file())
            })
            .or_else(|| {
                Some(PathBuf::from("/usr/bin")).filter(|dir| dir.join("ld.gold").is_file())
            });
        if found.is_none() {
            assert!(
                std::env::var_os("TCG_REQUIRE_GOLD").is_none(),
                "TCG_REQUIRE_GOLD is set but no ld.gold was found"
            );
            eprintln!(
                "SKIP: no ld.gold (PATH, /usr/bin); the gold legs of the .eh_frame control did \
                 not run"
            );
            return None;
        }
        let host_cc = std::env::var_os("PATH")
            .and_then(|paths| {
                std::env::split_paths(&paths)
                    .map(|dir| dir.join("cc"))
                    .find(|cc| cc.is_file())
            })
            .expect("a host cc on PATH");
        let bin = dir.join("gold-cc");
        fs::create_dir(&bin).unwrap();
        write_executable_script(
            &bin.join("cc"),
            &format!(
                "#!/bin/sh\nexec '{}' -fuse-ld=gold \"$@\"\n",
                host_cc.display()
            ),
        );
        Some(bin)
    }

    /// `main` adds one with `isize_add_one` (the b1 fixture) and calls the
    /// trust-cg function `tcg_bt_through`, which calls `bt_depth`, which
    /// records a `backtrace()`. It prints the sum, where `main` was loaded
    /// and each frame's return address.
    const BT_SOURCE: &str = "#include <execinfo.h>\n#include <stdio.h>\nextern long \
        isize_add_one(long);\nextern int tcg_bt_through(void);\nstatic void *frames[64];\nstatic \
        int count;\n__attribute__((noinline)) int bt_depth(void) { count = backtrace(frames, \
        64); return count; }\nint main(void) {\n  long v = isize_add_one(41);\n  \
        tcg_bt_through();\n  printf(\"v=%ld main_at=%p\\n\", v, (void *)main);\n  for (int i = 0; \
        i < count; i++) printf(\"pc=%p\\n\", frames[i]);\n  return v == 42 ? 0 : 1;\n}\n";

    /// `tcg_bt_through() = bt_depth() + 1`: a trust-cg frame between
    /// `bt_depth` and `main`.
    fn through_module() -> Module {
        let mut mb = ModuleBuilder::new("tcg_bt");
        let ty = mb.add_func_type(vec![], vec![Ty::I32]);
        let depth = mb.declare_function("bt_depth", ty);
        let mut fb = mb.function("tcg_bt_through", ty);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        let frames = fb.call(depth, vec![]);
        let one = fb.iconst(Ty::I32, 1);
        let sum = fb.binop(BinOp::Add, Ty::I32, frames, one);
        fb.ret(vec![sum]);
        fb.build();
        mb.build().expect("ModuleBuilder::build: test fixture")
    }

    /// The function each `backtrace()` frame of a program built from
    /// [`BT_SOURCE`] returns into, after it exits 0 having printed 42: each
    /// return address, moved by the load bias `main_at` gives, is placed
    /// in the extent `nm -S` gives a defined symbol (`?` outside every one).
    fn backtrace_of(program: &Path) -> Vec<String> {
        let (code, stdout) = run_program(program);
        assert_eq!(code, Some(0), "{}: {stdout}", program.display());
        let hex = |text: &str| u64::from_str_radix(text.trim_start_matches("0x"), 16).unwrap();
        let word = |name: &str| {
            stdout
                .split_whitespace()
                .find_map(|word| word.strip_prefix(name))
                .unwrap_or_else(|| panic!("{name} in {stdout}"))
        };
        assert_eq!(word("v="), "42", "{stdout}");
        let symbols = Command::new("nm")
            .args(["-S", "--defined-only"])
            .arg(program)
            .output()
            .unwrap();
        let symbols: Vec<(u64, u64, String)> = String::from_utf8_lossy(&symbols.stdout)
            .lines()
            .filter_map(
                |line| match line.split_whitespace().collect::<Vec<_>>()[..] {
                    [address, size, _, name] => Some((hex(address), hex(size), name.to_string())),
                    _ => None,
                },
            )
            .collect();
        let main = symbols
            .iter()
            .find(|(_, _, name)| name == "main")
            .expect("main in nm")
            .0;
        let bias = hex(word("main_at=")).wrapping_sub(main);
        stdout
            .split_whitespace()
            .filter_map(|word| word.strip_prefix("pc="))
            .map(|pc| {
                let at = hex(pc).wrapping_sub(bias);
                symbols
                    .iter()
                    .find(|(address, size, _)| *address < at && at <= address + size)
                    .map_or("?".to_string(), |(_, _, name)| name.clone())
            })
            .collect()
    }

    /// The L02-P10 closure audit at `5ddb13664`: trust-cg writes `.eh_frame`
    /// pointers (each FDE's `pc_begin`) as `DW_EH_PE_pcrel|sdata4` through
    /// `R_AARCH64_PREL32` (aaelf64 2026Q2: `-2^31 <= X < 2^31`) and left the
    /// window to the linker. GNU ld 2.42 refuses such a link, but LLD
    /// 22.1.6 and gold 2.42 write `2^31 <= X < 2^32`, which unwinders read
    /// as negative: `trust-cg -o btfar b1_scalars.tmbc -Wl,bt.o
    /// -Wl,--section-start=.eh_frame=0x10000000,--section-start=.eh_frame_hdr=0x0fff0000,--section-start=.text=0xd0000000`
    /// with LLD's (or gold's) `cc` first on `PATH` exited 0 and installed a
    /// program whose FDEs begin at `0xffffffffd00000..` and whose
    /// `backtrace()` stops after one frame. Now, with this module's
    /// `through.tmbc` added so a trust-cg frame lies between the
    /// backtrace and `main`: through LLD and gold the far placement is
    /// refused with exactly one `[TCG-LINK-EH-FRAME-WINDOW]` line
    /// (`relocation-out-of-range`), nothing is written and a file at the
    /// output keeps its bytes; GNU ld refuses it itself and the refusal is
    /// classified; the same objects linked by LLD or gold outside the
    /// driver backtrace one frame. The edge twin (`.text` at `0x8ffe0000`,
    /// every FDE 128 KiB inside the window) and the near twin (default
    /// placement) link through every linker, and their `backtrace()`
    /// crosses the trust-cg frame into `main`. Without LLD or gold their
    /// legs are skipped (`SKIP:`).
    #[test]
    fn an_eh_frame_pointer_out_of_the_prel32_window_is_refused_and_its_near_twin_backtraces() {
        let directory = tempfile::tempdir().unwrap();
        let dir = directory.path();
        copy_b1(dir);
        write_module(dir, "through.tmbc", &through_module());
        fs::write(dir.join("bt.c"), BT_SOURCE).unwrap();
        run_tool(dir, "cc", &["-c", "-O1", "-o", "bt.o", "bt.c"]);
        let lld = lld_dir().map(|lld| lld_cc(dir, &lld));
        let gold = gold_cc(dir);
        let placement = |text: &str| {
            format!(
                "-Wl,--section-start=.eh_frame=0x10000000,--section-start=.eh_frame_hdr=0x0fff0000,\
                 --section-start=.text={text}"
            )
        };
        let (far, edge) = (placement("0xd0000000"), placement("0x8ffe0000"));
        let args = |output: &str, placed: Option<&str>| {
            let mut args = vec![
                "-o".to_string(),
                output.to_string(),
                "b1_scalars.tmbc".into(),
                "through.tmbc".into(),
                "-Wl,bt.o".into(),
            ];
            args.extend(placed.map(str::to_string));
            args
        };
        let cli = |bin: Option<&Path>, args: &[String]| {
            trust_cg_on(
                bin,
                dir,
                &args.iter().map(String::as_str).collect::<Vec<_>>(),
            )
        };
        let linkers: Vec<(&str, Option<&Path>)> = [
            ("lld", lld.as_deref()),
            ("gold", gold.as_deref()),
            ("gnu", None),
        ]
        .into_iter()
        .filter(|(name, bin)| *name == "gnu" || bin.is_some())
        .collect();
        for (name, bin) in &linkers {
            // The far placement: refused with nothing written, with and
            // without a file at the output.
            let output = format!("btfar_{name}");
            for preexisting in [None, Some(&b"precious\n"[..])] {
                if let Some(bytes) = preexisting {
                    fs::write(dir.join(&output), bytes).unwrap();
                }
                let before = listing(dir);
                let result = cli(*bin, &args(&output, Some(&far)));
                let text = stderr(&result);
                assert!(!result.status.success(), "{output}: {text}");
                let lines: Vec<&str> = text.lines().filter(|l| l.contains("error[link:")).collect();
                if *name == "gnu" {
                    assert!(
                        text.contains("relocation truncated to fit: R_AARCH64_PREL32")
                            && lines.len() == 1
                            && lines[0].starts_with(
                                "trust-cg: error[link:relocation-out-of-range] `.text` \
                                 (R_AARCH64_PREL32): "
                            ),
                        "{output}: {text}"
                    );
                } else {
                    assert_eq!(lines.len(), 1, "{output}: {text}");
                    assert!(
                        lines[0].starts_with(&format!(
                            "trust-cg: error[link:relocation-out-of-range] `_start` \
                             (R_AARCH64_PREL32): [TCG-LINK-EH-FRAME-WINDOW] the linked output \
                             for {output} is refused: "
                        )) && lines[0].contains(" FDEs describe code outside executable memory (")
                            && lines[0].contains(
                                "the same 32 bits read as unsigned would give 0xd0000000, the \
                                 function `_start`; the field is written by R_AARCH64_PREL32"
                            ),
                        "{output}: {text}"
                    );
                }
                assert_eq!(listing(dir), before, "{output}");
                match preexisting {
                    None => assert!(!dir.join(&output).exists(), "{output}"),
                    Some(bytes) => {
                        assert_eq!(fs::read(dir.join(&output)).unwrap(), bytes, "{output}");
                        fs::remove_file(dir.join(&output)).unwrap();
                    }
                }
            }
            // The edge and near twins link, run and backtrace into `main`.
            for (twin, placed) in [("edge", Some(edge.as_str())), ("near", None)] {
                let output = format!("bt{twin}_{name}");
                let result = cli(*bin, &args(&output, placed));
                assert!(result.status.success(), "{output}: {}", stderr(&result));
                let frames = backtrace_of(&dir.join(&output));
                assert!(
                    frames.len() >= 4 && frames[..3] == ["bt_depth", "tcg_bt_through", "main"],
                    "{output}: {frames:?}"
                );
            }
        }
        // LLD and gold outside the driver install the far program, and its
        // backtrace stops at the first frame.
        let checked: Vec<(&str, &Path)> = linkers
            .iter()
            .filter_map(|(name, bin)| bin.map(|bin| (*name, bin)))
            .collect();
        if !checked.is_empty() {
            for module in ["b1_scalars", "through"] {
                let output = cli(
                    None,
                    &[
                        "-c".into(),
                        "-o".into(),
                        format!("{module}.o"),
                        format!("{module}.tmbc"),
                    ],
                );
                assert!(output.status.success(), "{}", stderr(&output));
            }
        }
        for (name, bin) in checked {
            let raw = format!("btraw_{name}");
            let cc = bin.join("cc").display().to_string();
            run_tool(
                dir,
                &cc,
                &[
                    "-o",
                    &raw,
                    "b1_scalars.o",
                    "through.o",
                    "bt.o",
                    "-Wl,-z,noexecstack",
                    &far,
                ],
            );
            assert_eq!(backtrace_of(&dir.join(&raw)), ["bt_depth"], "{raw}");
        }
    }

    /// A 256 KiB `tcg_pad` function in `.text`, the code an FDE written
    /// 2^32 short of its function lands in.
    const PAD_SOURCE: &str = "\t.text\n\t.globl tcg_pad\n\t.type tcg_pad, %function\ntcg_pad:\n\t\
                              .space 0x40000\n\t.size tcg_pad, 0x40000\n";

    /// `_start` exits 0 when `isize_add_one(41)` (the b1 fixture) is 42.
    const ADD_ONE_START: &str = "\t.text\n\t.globl _start\n\t.type _start, %function\n_start:\n\t\
                                 mov x0, #41\n\tbl isize_add_one\n\tcmp x0, #42\n\tcset w0, ne\n\t\
                                 mov x8, #93\n\tsvc #0\n";

    /// The L02-P10 closure audit at `43de0bebe`: the image check refused an
    /// FDE only when its `pc_begin` fell outside executable memory, but a
    /// `PREL32` value in `[2^31, 2^32)` that LLD 22.1.6 or gold 2.42 writes
    /// truncated can land in other code. With [`PAD_SOURCE`]'s `tcg_pad`
    /// at `0x10000000`, `.eh_frame` at `0x90000000` and the b1 fixture's
    /// `.text` moved by a linker script to `0x110010000`, both installed a
    /// `-nostdlib` program whose three trust-cg FDEs describe `tcg_pad`.
    /// Now, through LLD (an `INSERT AFTER .eh_frame` script) and gold (a
    /// full `SECTIONS` script), the placement is refused with exactly one
    /// `[TCG-LINK-EH-FRAME-UNPROVEN]` line (`unclassified`) naming the
    /// other address, `0x110010000`, and nothing is written; GNU ld refuses
    /// it itself and the refusal is classified. The same objects linked by
    /// LLD or gold outside the driver run, but their FDEs begin at
    /// `0x10010000` while `isize_add_one` is at `0x110010000`. The near
    /// twin (`.tcgtext` at `0x50010000`, 1 GiB below `.eh_frame`) links
    /// through every linker and exits 0. Without LLD or gold their legs
    /// are skipped (`SKIP:`).
    #[test]
    fn an_eh_frame_pointer_whose_bits_also_give_other_code_is_refused_and_its_near_twin_runs() {
        let directory = tempfile::tempdir().unwrap();
        let dir = directory.path();
        copy_b1(dir);
        assemble(dir, "pad", PAD_SOURCE);
        assemble(dir, "start", ADD_ONE_START);
        let lld = lld_dir().map(|lld| lld_cc(dir, &lld));
        let gold = gold_cc(dir);
        let (far, near) = (0x1_1001_0000u64, 0x5001_0000u64);
        // The placement for `linker`, with the b1 code (`object`) at
        // `tcgtext`: gold reads no `INSERT`, so it takes a full script.
        let placement = |linker: &str, object: &str, tcgtext: u64| -> Vec<String> {
            let path = format!("{linker}_{object}_{tcgtext:#x}.ld");
            let script = if linker == "gold" {
                format!(
                    "SECTIONS {{\n  .tcgtext {tcgtext:#x} : {{ *{object}(.text .text.*) }}\n  \
                     .text 0x10000000 : {{ *(.text .text.*) }}\n  .eh_frame_hdr 0x8fff0000 : {{ \
                     *(.eh_frame_hdr) }}\n  .eh_frame 0x90000000 : {{ *(.eh_frame) }}\n}}\n"
                )
            } else {
                format!(
                    "SECTIONS {{ .tcgtext {tcgtext:#x} : {{ *{object}(.text .text.*) }} }} \
                     INSERT AFTER .eh_frame;\n"
                )
            };
            fs::write(dir.join(&path), script).unwrap();
            let mut args = Vec::new();
            if linker != "gold" {
                args.push(
                    "-Wl,--section-start=.text=0x10000000,--section-start=.eh_frame=0x90000000,\
                     --section-start=.eh_frame_hdr=0x8fff0000,--no-dynamic-linker"
                        .to_string(),
                );
            }
            args.push(format!("-Wl,-T,{path}"));
            args
        };
        let cli_args = |linker: &str, output: &str, tcgtext: u64| {
            let mut args: Vec<String> = [
                "--nostdlib",
                "--no-pie",
                "-o",
                output,
                "b1_scalars.tmbc",
                "-Wl,start.o,pad.o",
            ]
            .map(str::to_string)
            .to_vec();
            args.extend(placement(linker, "input_0.o", tcgtext));
            args
        };
        let cli = |bin: Option<&Path>, args: &[String]| {
            trust_cg_on(
                bin,
                dir,
                &args.iter().map(String::as_str).collect::<Vec<_>>(),
            )
        };
        let linkers: Vec<(&str, Option<&Path>)> = [
            ("lld", lld.as_deref()),
            ("gold", gold.as_deref()),
            ("gnu", None),
        ]
        .into_iter()
        .filter(|(name, bin)| *name == "gnu" || bin.is_some())
        .collect();
        for (name, bin) in &linkers {
            let output = format!("alias_far_{name}");
            let args = cli_args(name, &output, far);
            let before = listing(dir);
            let result = cli(*bin, &args);
            let text = stderr(&result);
            assert!(!result.status.success(), "{output}: {text}");
            let lines: Vec<&str> = text.lines().filter(|l| l.contains("error[link:")).collect();
            assert_eq!(lines.len(), 1, "{output}: {text}");
            if *name == "gnu" {
                assert!(
                    text.contains("relocation truncated to fit: R_AARCH64_PREL32")
                        && lines[0].starts_with(
                            "trust-cg: error[link:relocation-out-of-range] `.text` \
                                          (R_AARCH64_PREL32): "
                        ),
                    "{output}: {text}"
                );
            } else {
                assert!(
                    lines[0].starts_with(&format!(
                        "trust-cg: error[link:unclassified] (R_AARCH64_PREL32): \
                         [TCG-LINK-EH-FRAME-UNPROVEN] the linked output for {output} is refused \
                         because the check cannot show that 3 of its .eh_frame pointers name the \
                         address their linker was given: the first, the pc_begin of the FDE at "
                    )) && lines[0].contains(
                        "and so gives 0x10010000, but a linker writes the same bits truncated \
                         for 0x110010000, and both are in executable memory; the field is \
                         written by R_AARCH64_PREL32"
                    ) && lines[0]
                        .ends_with("this is a conservative refusal, not an observed overflow"),
                    "{output}: {text}"
                );
            }
            assert_eq!(listing(dir), before, "{output}");
            assert!(!dir.join(&output).exists(), "{output}");
            // The near twin links and runs.
            let output = format!("alias_near_{name}");
            let result = cli(*bin, &cli_args(name, &output, near));
            assert!(result.status.success(), "{output}: {}", stderr(&result));
            assert_eq!(run_program(&dir.join(&output)).0, Some(0), "{output}");
        }
        // LLD and gold outside the driver install the far program: it
        // runs, and its FDEs describe `tcg_pad`, not `isize_add_one`.
        let checked: Vec<(&str, &Path)> = linkers
            .iter()
            .filter_map(|(name, bin)| bin.map(|bin| (*name, bin)))
            .collect();
        if !checked.is_empty() {
            let object = trust_cg_on(None, dir, &["-c", "-o", "b1_scalars.o", "b1_scalars.tmbc"]);
            assert!(object.status.success(), "{}", stderr(&object));
        }
        for (name, bin) in checked {
            let raw = format!("alias_raw_{name}");
            let cc = bin.join("cc").display().to_string();
            let mut args: Vec<String> = [
                "-nostdlib",
                "-no-pie",
                "-o",
                raw.as_str(),
                "b1_scalars.o",
                "start.o",
                "pad.o",
                "-Wl,-z,noexecstack",
            ]
            .map(str::to_string)
            .to_vec();
            args.extend(placement(name, "b1_scalars.o", far));
            run_tool(
                dir,
                &cc,
                &args.iter().map(String::as_str).collect::<Vec<_>>(),
            );
            assert_eq!(run_program(&dir.join(&raw)).0, Some(0), "{raw}");
            let symbols = Command::new("nm").arg(dir.join(&raw)).output().unwrap();
            let symbols = String::from_utf8_lossy(&symbols.stdout).into_owned();
            assert!(
                symbols.contains("0000000110010000 T isize_add_one"),
                "{raw}: {symbols}"
            );
            let frames = Command::new("readelf")
                .args(["--debug-dump=frames"])
                .arg(dir.join(&raw))
                .output()
                .unwrap();
            let frames = String::from_utf8_lossy(&frames.stdout).into_owned();
            let begins: Vec<&str> = frames
                .lines()
                .filter(|line| line.contains(" FDE "))
                .filter_map(|line| line.split("pc=").nth(1))
                .filter_map(|range| range.split("..").next())
                .collect();
            assert!(
                begins.len() == 3 && begins.iter().all(|pc| pc.starts_with("00000000100100")),
                "{raw}: {frames}"
            );
        }
    }

    /// `thrower` throws 7 through `middle` to `main`, which prints it and
    /// the last byte of a `.bss` of `BSS` bytes (set to 2), and exits 42.
    fn throw_source(bss: u64) -> String {
        format!(
            "#include <cstdio>\nstatic char big[{bss}ULL];\n__attribute__((noinline)) void \
             thrower() {{ throw 7; }}\n__attribute__((noinline)) int middle(int x) {{ thrower(); \
             return x + 1; }}\nint main() {{\n  big[{bss}ULL - 1] = 2;\n  try {{ middle(1); }} \
             catch (int v) {{ printf(\"caught %d big=%d\\n\", v, big[{bss}ULL - 1]); return 42; \
             }}\n  return 1;\n}}\n"
        )
    }

    /// The independent verifier of the wrap-alias refusal found two
    /// defects, both repaired here.
    ///
    /// - A zero-range FDE, as GCC emits for an empty function
    ///   (`__builtin_unreachable()`), has no code for another address to
    ///   lie in. Placed by an `INSERT AFTER .bss` script 2^32 + 0x10 above
    ///   `middle`, LLD writes its `pc_begin` truncated into `middle`, and its
    ///   table entry hides `middle`'s FDE: the installed program terminates
    ///   at its throw. The CLI now refuses the image with one
    ///   `[TCG-LINK-EH-FRAME-WINDOW]` line naming both FDEs; GNU ld drops
    ///   the empty section's FDE and its program runs; the same program
    ///   without the empty function links through LLD and runs.
    /// - A correct C++ program with a 5 GiB `.bss` was refused through GNU
    ///   ld, LLD and gold, PIE and not: its personality slot's other address
    ///   2^32 away lay in the `.bss`. An LSDA or a personality slot has
    ///   contents, so only file-backed memory is an alias now, and all six
    ///   links run.
    ///
    /// Without LLD or gold their legs are skipped (`SKIP:`).
    #[test]
    fn a_hidden_zero_range_fde_is_refused_and_a_5_gib_bss_program_links() {
        let directory = tempfile::tempdir().unwrap();
        let dir = directory.path();
        copy_b1(dir);
        fs::write(dir.join("prog.cc"), throw_source(16)).unwrap();
        fs::write(dir.join("big.cc"), throw_source(5 << 30)).unwrap();
        fs::write(
            dir.join("far.c"),
            "__attribute__((section(\".tcgfar\"))) void tcg_empty(void) { \
             __builtin_unreachable(); }\n",
        )
        .unwrap();
        run_tool(dir, "c++", &["-c", "-O2", "-o", "prog.o", "prog.cc"]);
        run_tool(dir, "c++", &["-c", "-O2", "-o", "big.o", "big.cc"]);
        run_tool(dir, "cc", &["-c", "-O2", "-o", "far.o", "far.c"]);
        let lld = lld_dir().map(|lld| lld_cc(dir, &lld));
        let gold = gold_cc(dir);
        let cli = |bin: Option<&Path>, args: &[&str]| trust_cg_on(bin, dir, args);
        let placed = "-Wl,--section-start=.eh_frame_hdr=0x0f000000,--section-start=.text=0x10000000,\
                      --section-start=.eh_frame=0x80000000";

        // The near twin without the empty function fixes `middle`.
        let mut near_args = vec![
            "--no-pie",
            "-o",
            "zr_near",
            "b1_scalars.tmbc",
            "-Wl,prog.o,-lstdc++",
        ];
        near_args.push(placed);
        let linked = cli(lld.as_deref(), &near_args);
        assert!(linked.status.success(), "{}", stderr(&linked));
        let (code, stdout) = run_program(&dir.join("zr_near"));
        assert_eq!((code, stdout.as_str()), (Some(42), "caught 7 big=2\n"));
        let symbols = Command::new("nm")
            .arg(dir.join("zr_near"))
            .output()
            .unwrap();
        let middle = String::from_utf8_lossy(&symbols.stdout)
            .lines()
            .find(|line| line.ends_with(" _Z6middlei"))
            .and_then(|line| u64::from_str_radix(line.split(' ').next()?, 16).ok())
            .expect("middle in nm");
        let far = (1u64 << 32) + (middle + 0x10).next_multiple_of(16);
        fs::write(
            dir.join("far.ld"),
            format!("SECTIONS {{ .tcgfar {far:#x} : {{ *(.tcgfar) }} }} INSERT AFTER .bss;\n"),
        )
        .unwrap();
        for (name, bin) in [("lld", lld.as_deref()), ("gnu", None)] {
            if name == "lld" && bin.is_none() {
                continue;
            }
            let output = format!("zr_far_{name}");
            let args = [
                "--no-pie",
                "-o",
                output.as_str(),
                "b1_scalars.tmbc",
                "-Wl,prog.o,far.o,-lstdc++",
                placed,
                "-Wl,-T,far.ld",
            ];
            let result = cli(bin, &args);
            let text = stderr(&result);
            if name == "gnu" {
                assert!(result.status.success(), "{output}: {text}");
                assert_eq!(run_program(&dir.join(&output)).0, Some(42), "{output}");
                continue;
            }
            assert!(!result.status.success(), "{output}: {text}");
            let lines: Vec<&str> = text.lines().filter(|l| l.contains("error[link:")).collect();
            assert!(
                lines.len() == 1
                    && lines[0].starts_with(&format!(
                        "trust-cg: error[link:relocation-out-of-range]: \
                         [TCG-LINK-EH-FRAME-WINDOW] the linked output for {output} is refused: 1 \
                         of its "
                    ))
                    && lines[0].contains(
                        "live FDEs are hidden from an unwinder's lookup by another; the first, \
                         the FDE at "
                    )
                    && lines[0].contains(&format!(
                        "which describes {:#x}..{:#x}, for a pc from {:#x} on",
                        far - (1 << 32),
                        far - (1 << 32),
                        far - (1 << 32)
                    )),
                "{output}: {text}"
            );
            assert!(!dir.join(&output).exists(), "{output}");
            // LLD outside the driver installs it, and the throw terminates.
            let raw = format!("zr_raw_{name}");
            let cc = bin.unwrap().join("cc").display().to_string();
            let object = trust_cg_on(None, dir, &["-c", "-o", "b1_scalars.o", "b1_scalars.tmbc"]);
            assert!(object.status.success(), "{}", stderr(&object));
            run_tool(
                dir,
                &cc,
                &[
                    "-no-pie",
                    "-o",
                    &raw,
                    "b1_scalars.o",
                    "prog.o",
                    "far.o",
                    "-lstdc++",
                    "-Wl,-z,noexecstack",
                    placed,
                    "-Wl,-T,far.ld",
                ],
            );
            assert_eq!(run_program(&dir.join(&raw)).0, None, "{raw}");
        }

        // A 5 GiB `.bss` with a personality links and runs everywhere.
        for (name, bin) in [
            ("gnu", None),
            ("lld", lld.as_deref()),
            ("gold", gold.as_deref()),
        ] {
            if name != "gnu" && bin.is_none() {
                continue;
            }
            for pie in ["--pie", "--no-pie"] {
                let output = format!("big_{name}{pie}");
                let result = cli(
                    bin,
                    &[pie, "-o", &output, "b1_scalars.tmbc", "-Wl,big.o,-lstdc++"],
                );
                assert!(result.status.success(), "{output}: {}", stderr(&result));
                let (code, stdout) = run_program(&dir.join(&output));
                assert_eq!(
                    (code, stdout.as_str()),
                    (Some(42), "caught 7 big=2\n"),
                    "{output}"
                );
                fs::remove_file(dir.join(&output)).unwrap();
            }
        }
    }

    /// An empty function (`__builtin_unreachable()`, a zero-range FDE) and
    /// `read_data`, which calls back into its caller, in one section: LLD's
    /// `.eh_frame_hdr` keeps one entry per start, the first in `.eh_frame`
    /// order, so it names the zero-range FDE for `read_data`'s start.
    const EMPTY_THEN_READ_DATA: &str = "typedef void (*cb_t)(void);\n__attribute__((noinline, \
        section(\".text.qt\"))) void setup_empty(void) { __builtin_unreachable(); \
        }\n__attribute__((noinline, section(\".text.qt\"))) int read_data(cb_t cb, int x) { \
        cb(); return x + 1; }\n";

    /// `dlopen`s `argv[1]` and throws 7 through its `read_data`; exits 42
    /// when the throw is caught.
    const DLOPEN_THROW: &str = "#include <cstdio>\n#include <dlfcn.h>\nstatic void thr() { \
        throw 7; }\nint main(int argc, char **argv) {\n  void *h = dlopen(argv[1], RTLD_NOW);\n  \
        if (!h) { printf(\"dlopen: %s\\n\", dlerror()); return 2; }\n  auto rd = (int \
        (*)(void (*)(), int))dlsym(h, \"read_data\");\n  if (!rd) return 3;\n  try { rd(thr, 1); } \
        catch (int v) { printf(\"caught %d\\n\", v); return 42; }\n  return 1;\n}\n";

    /// The second independent verifier of the `.eh_frame` refusals found:
    ///
    /// - `-z nosectionheader` bypassed the hidden-FDE rule: without section
    ///   headers only the FDEs the table names were read, so the FDE LLD's
    ///   table drops was never seen. A library built from
    ///   [`EMPTY_THEN_READ_DATA`] through LLD is now refused with and
    ///   without section headers; LLD's own library makes a throw through
    ///   `read_data` terminate; GNU ld's is installed and catches it.
    /// - gold 2.42's static C++ programs registered no unwind information
    ///   (`crtbeginT.o`'s `__EH_FRAME_BEGIN__` resolved to 0) and every
    ///   throw aborted. A static link now asks for `--eh-frame-hdr`, and the
    ///   static throw program catches through GNU ld, LLD and gold, while
    ///   gold's own static link without it still aborts.
    /// - In a static executable a search of the FDEs `crtbeginT.o`
    ///   registers may run before the table and find an FDE the table hides,
    ///   so LLD's static program, whose table names the empty function's FDE
    ///   for `read_data`'s start, is refused as unproven (`unclassified`),
    ///   not as an observed failure. GNU ld and gold drop the zero-range FDE,
    ///   and their static programs catch.
    ///
    /// Without LLD or gold their legs are skipped (`SKIP:`).
    #[test]
    fn a_table_that_drops_an_fde_is_refused_without_section_headers_and_static_throws_run() {
        let directory = tempfile::tempdir().unwrap();
        let dir = directory.path();
        copy_b1(dir);
        fs::write(dir.join("libq.c"), EMPTY_THEN_READ_DATA).unwrap();
        fs::write(dir.join("mainqd.cc"), DLOPEN_THROW).unwrap();
        fs::write(dir.join("throw.cc"), throw_source(16)).unwrap();
        fs::write(
            dir.join("tie.cc"),
            format!(
                "extern \"C\" {{\n{EMPTY_THEN_READ_DATA}}}\n#include <cstdio>\nstatic void thr() \
                 {{ throw 7; }}\nint main() {{ try {{ read_data(thr, 1); }} catch (int v) {{ \
                 printf(\"caught %d big=2\\n\", v); return 42; }} return 1; }}\n"
            ),
        )
        .unwrap();
        run_tool(dir, "cc", &["-c", "-O2", "-fPIC", "-o", "libq.o", "libq.c"]);
        run_tool(dir, "c++", &["-O2", "-o", "mqd", "mainqd.cc", "-ldl"]);
        run_tool(dir, "c++", &["-c", "-O2", "-o", "throw.o", "throw.cc"]);
        run_tool(dir, "c++", &["-c", "-O2", "-o", "tie.o", "tie.cc"]);
        let object = trust_cg_on(None, dir, &["-c", "-o", "b1_scalars.o", "b1_scalars.tmbc"]);
        assert!(object.status.success(), "{}", stderr(&object));
        let lld = lld_dir().map(|lld| lld_cc(dir, &lld));
        let gold = gold_cc(dir);
        let cli = |bin: Option<&Path>, args: &[&str]| trust_cg_on(bin, dir, args);
        let error_lines = |text: &str| -> Vec<String> {
            text.lines()
                .filter(|line| line.contains("error[link:"))
                .map(str::to_string)
                .collect()
        };
        let throw_through = |library: &str| {
            let output = Command::new(dir.join("mqd"))
                .arg(dir.join(library))
                .output()
                .unwrap();
            (
                output.status.code(),
                String::from_utf8_lossy(&output.stdout).into_owned(),
            )
        };

        // The table that drops `read_data`'s FDE, with and without section
        // headers.
        for (suffix, group) in [
            ("", "-Wl,libq.o"),
            ("_nsh", "-Wl,libq.o,-z,nosectionheader"),
        ] {
            if let Some(bin) = lld.as_deref() {
                let output = format!("libq_lld{suffix}.so");
                let result = cli(
                    Some(bin),
                    &[
                        "--shared",
                        "--nostdlib",
                        "--relocation-model",
                        "pic",
                        "-o",
                        &output,
                        "b1_scalars.tmbc",
                        group,
                    ],
                );
                let text = stderr(&result);
                let lines = error_lines(&text);
                assert!(
                    !result.status.success()
                        && lines.len() == 1
                        && lines[0].contains("[TCG-LINK-EH-FRAME-WINDOW]")
                        && lines[0]
                            .contains("live FDEs are hidden from an unwinder's lookup by another"),
                    "{output}: {text}"
                );
                assert!(!dir.join(&output).exists(), "{output}");
                // LLD's own library: the throw through `read_data` terminates.
                let raw = format!("libq_raw{suffix}.so");
                let mut args = vec!["-shared", "-nostdlib", "-o", &raw, "b1_scalars.o", "libq.o"];
                if !suffix.is_empty() {
                    args.push("-Wl,-z,nosectionheader");
                }
                run_tool(dir, &bin.join("cc").display().to_string(), &args);
                assert_eq!(throw_through(&raw).0, None, "{raw}");
            }
            // GNU ld drops the zero-range FDE: installed, and the throw is caught.
            let output = format!("libq_gnu{suffix}.so");
            let result = cli(
                None,
                &[
                    "--shared",
                    "--nostdlib",
                    "--relocation-model",
                    "pic",
                    "-o",
                    &output,
                    "b1_scalars.tmbc",
                    group,
                ],
            );
            assert!(result.status.success(), "{output}: {}", stderr(&result));
            assert_eq!(
                throw_through(&output),
                (Some(42), "caught 7\n".to_string()),
                "{output}"
            );
        }

        // Static C++ throws catch through every linker; gold's own static
        // link without `--eh-frame-hdr` aborts.
        for (name, bin) in [
            ("gnu", None),
            ("lld", lld.as_deref()),
            ("gold", gold.as_deref()),
        ] {
            if name != "gnu" && bin.is_none() {
                continue;
            }
            let output = format!("static_{name}");
            let result = cli(
                bin,
                &[
                    "--static",
                    "-o",
                    &output,
                    "b1_scalars.tmbc",
                    "-Wl,throw.o,-lstdc++",
                ],
            );
            assert!(result.status.success(), "{output}: {}", stderr(&result));
            let (code, stdout) = run_program(&dir.join(&output));
            assert_eq!(
                (code, stdout.as_str()),
                (Some(42), "caught 7 big=2\n"),
                "{output}"
            );
        }
        if let Some(bin) = gold.as_deref() {
            let cc = bin.join("cc").display().to_string();
            run_tool(
                dir,
                &cc,
                &[
                    "-static",
                    "-o",
                    "static_gold_raw",
                    "b1_scalars.o",
                    "throw.o",
                    "-lstdc++",
                ],
            );
            assert_eq!(
                run_program(&dir.join("static_gold_raw")).0,
                None,
                "static_gold_raw"
            );
        }

        // A static tie: undecided through LLD, caught through GNU ld and gold.
        for (name, bin) in [
            ("gnu", None),
            ("lld", lld.as_deref()),
            ("gold", gold.as_deref()),
        ] {
            if name != "gnu" && bin.is_none() {
                continue;
            }
            let output = format!("tie_{name}");
            let result = cli(
                bin,
                &[
                    "--static",
                    "-o",
                    &output,
                    "b1_scalars.tmbc",
                    "-Wl,tie.o,-lstdc++",
                ],
            );
            let text = stderr(&result);
            if name == "lld" {
                let lines = error_lines(&text);
                assert!(
                    !result.status.success()
                        && lines.len() == 1
                        && lines[0].starts_with(
                            "trust-cg: error[link:unclassified]: [TCG-LINK-EH-FRAME-UNPROVEN] the \
                             linked output for tie_lld is refused because the check cannot show \
                             that libgcc finds the FDE of every function: 1 of its "
                        ),
                    "{output}: {text}"
                );
                assert!(!dir.join(&output).exists(), "{output}");
            } else {
                assert!(result.status.success(), "{output}: {text}");
                let (code, stdout) = run_program(&dir.join(&output));
                assert_eq!(
                    (code, stdout.as_str()),
                    (Some(42), "caught 7 big=2\n"),
                    "{output}"
                );
            }
        }
    }

    /// The third independent verifier of the `.eh_frame` refusals found
    /// three false refusals the second repair introduced, all repaired here:
    ///
    /// - GNU ld's default script puts `.gcc_except_table` (or `.sframe`)
    ///   right after `.eh_frame` in its segment, and writes no terminator
    ///   for a `-nostdlib` link. A `-nostdlib` program whose `work` has a
    ///   cleanup (an LSDA) linked with `-z nosectionheader` was refused
    ///   because the walk read `.gcc_except_table` as a record. The walk now
    ///   ends at the first record that is not `.eh_frame`'s, and the program
    ///   links and exits 42.
    /// - A static tie whose table names the function's own FDE (an empty
    ///   `f_empty` ordered at `g_mid`'s start with `-ffunction-sections`,
    ///   `g_mid`'s FDE first) was refused, although libgcc's registered
    ///   search never takes a zero-range FDE and falls back to the table on
    ///   a miss. The table decides now; LLD's static program links and
    ///   catches.
    /// - LLD writes a zero-filled `.eh_frame_hdr` and no `PT_GNU_EH_FRAME`
    ///   when a linker script discards `.eh_frame` under `--eh-frame-hdr`,
    ///   which a static link now passes. That placeholder is ignored, and
    ///   the bare-metal program links and exits 42.
    ///
    /// Without LLD the LLD legs are skipped (`SKIP:`).
    #[test]
    fn eh_frame_layouts_the_second_repair_refused_link_and_run() {
        let directory = tempfile::tempdir().unwrap();
        let dir = directory.path();
        copy_b1(dir);
        fs::write(
            dir.join("start.c"),
            "extern long isize_add_one(long);\n__attribute__((noreturn)) static void \
             sys_exit(long code) {\n  register long x0 asm(\"x0\") = code; register long x8 \
             asm(\"x8\") = 93;\n  asm volatile(\"svc 0\" :: \"r\"(x0), \"r\"(x8) : \"memory\"); \
             __builtin_unreachable();\n}\n__attribute__((noipa)) void cl(int *p) { (void)p; \
             }\n__attribute__((noipa)) void maybe(void) {}\n__attribute__((noipa)) int work(int \
             x) { int __attribute__((cleanup(cl))) v = x; maybe(); return v + 1; }\nvoid \
             _Unwind_Resume(void *e) { (void)e; sys_exit(99); }\nint __gcc_personality_v0(void) \
             { return 0; }\nvoid _start(void) { sys_exit(work(40) == 41 ? isize_add_one(41) : \
             1); }\n",
        )
        .unwrap();
        fs::write(
            dir.join("bare.c"),
            "extern long isize_add_one(long);\n__attribute__((noreturn)) static void \
             sys_exit(long code) {\n  register long x0 asm(\"x0\") = code; register long x8 \
             asm(\"x8\") = 93;\n  asm volatile(\"svc 0\" :: \"r\"(x0), \"r\"(x8) : \"memory\"); \
             __builtin_unreachable();\n}\nvoid _start(void) { sys_exit(isize_add_one(41)); }\n",
        )
        .unwrap();
        fs::write(
            dir.join("discard.ld"),
            "ENTRY(_start)\nSECTIONS {\n  . = 0x400000;\n  .text : { *(.text .text.*) }\n  \
             .rodata : { *(.rodata .rodata.*) }\n  .data : { *(.data .data.*) }\n  .bss : { \
             *(.bss .bss.*) }\n  /DISCARD/ : { *(.eh_frame) *(.comment) *(.note.*) }\n}\n",
        )
        .unwrap();
        fs::write(
            dir.join("tie2.cc"),
            "#include <cstdio>\nextern \"C\" __attribute__((noinline)) void thrower() { throw 7; \
             }\nextern \"C\" __attribute__((noinline)) int g_mid(int x) { thrower(); return x + \
             1; }\nextern \"C\" __attribute__((noinline)) void f_empty() { \
             __builtin_unreachable(); }\nint main() {\n  try { g_mid(1); } catch (int v) { \
             printf(\"caught %d\\n\", v); return 42; }\n  return 1;\n}\n",
        )
        .unwrap();
        fs::write(dir.join("order.txt"), "f_empty\ng_mid\n").unwrap();
        run_tool(
            dir,
            "cc",
            &[
                "-c",
                "-O2",
                "-fno-pic",
                "-fexceptions",
                "-fno-stack-protector",
                "-o",
                "start.o",
                "start.c",
            ],
        );
        run_tool(
            dir,
            "cc",
            &["-c", "-O2", "-fno-pic", "-o", "bare.o", "bare.c"],
        );
        run_tool(
            dir,
            "c++",
            &[
                "-c",
                "-O2",
                "-ffunction-sections",
                "-o",
                "tie2.o",
                "tie2.cc",
            ],
        );
        let lld = lld_dir().map(|lld| lld_cc(dir, &lld));

        // GNU ld, `-nostdlib`, no section headers, `.gcc_except_table`
        // right after `.eh_frame`.
        let result = trust_cg_on(
            None,
            dir,
            &[
                "--nostdlib",
                "--no-pie",
                "-o",
                "lsda_nsh",
                "b1_scalars.tmbc",
                "-Wl,start.o,-z,nosectionheader",
            ],
        );
        assert!(result.status.success(), "{}", stderr(&result));
        assert_eq!(run_program(&dir.join("lsda_nsh")).0, Some(42));
        let Some(lld) = lld.as_deref() else {
            return;
        };
        // A static tie the table decides for the function.
        let result = trust_cg_on(
            Some(lld),
            dir,
            &[
                "--static",
                "-o",
                "tie2_lld",
                "b1_scalars.tmbc",
                "-Wl,tie2.o,-lstdc++,--symbol-ordering-file=order.txt",
            ],
        );
        assert!(result.status.success(), "{}", stderr(&result));
        let (code, stdout) = run_program(&dir.join("tie2_lld"));
        assert_eq!((code, stdout.as_str()), (Some(42), "caught 7\n"));
        // LLD's placeholder `.eh_frame_hdr` for a discarded `.eh_frame`.
        let result = trust_cg_on(
            Some(lld),
            dir,
            &[
                "--static",
                "--nostdlib",
                "--no-pie",
                "-o",
                "bare_lld",
                "b1_scalars.tmbc",
                "-Wl,bare.o,-T,discard.ld",
            ],
        );
        assert!(result.status.success(), "{}", stderr(&result));
        assert_eq!(run_program(&dir.join("bare_lld")).0, Some(42));
    }

    /// A CIE and an FDE of `y_mid` with range 0x18 (of `y_mid`'s 0x34 bytes)
    /// whose rule leaves the return address undefined, appended to
    /// `g++ -O1 -S` output: a narrower FDE with a range at `y_mid`'s start.
    const NARROW_FDE_ASM: &str = "\t.section .eh_frame,\"a\",@progbits\n\t.p2align 3\nncie:\n\t\
        .4byte ncie_end - ncie_id\nncie_id:\n\t.4byte 0\n\t.byte 1\n\t.asciz \"zR\"\n\t.uleb128 \
        4\n\t.sleb128 -8\n\t.uleb128 30\n\t.uleb128 1\n\t.byte 0x1b\n\t.byte 0x0c, 31, 0\n\t.byte \
        0x07, 30\n\t.p2align 3\nncie_end:\nnfde:\n\t.4byte nfde_end - nfde_id\nnfde_id:\n\t.4byte \
        nfde_id - ncie\n\t.4byte y_mid - .\n\t.4byte 0x18\n\t.uleb128 0\n\t.p2align 3\nnfde_end:\n";

    /// The fourth independent verifier of the `.eh_frame` refusals found two
    /// soundness regressions in the third repair, both repaired here:
    ///
    /// - Without section headers and without a table, the walk stopped at
    ///   the first record it took as not `.eh_frame`'s and accepted the
    ///   image, but libgcc reads on to a zero length. GNU ld writes no table
    ///   when it cannot parse an input `.eh_frame`: a `-nostdlib` library
    ///   holding a 64-bit length record, linked with `-z nosectionheader`,
    ///   was installed, and a throw through its `call_cb` aborts. Such a
    ///   walk must now end at a terminator, and the library is refused as
    ///   unproven (with section headers it is refused too).
    /// - In a static executable libgcc's registered search returns any FDE
    ///   that covers the pc, so a narrower FDE with a range can be taken
    ///   whatever the table names. LLD's static program with
    ///   [`NARROW_FDE_ASM`] after 22 padding functions was installed and
    ///   terminates at its throw; it is now refused as undecided. The same
    ///   objects in a position-dependent dynamic executable, where the table
    ///   decides unless the program registers its frames (any program can,
    ///   and the driver does not read whether one does), are refused as
    ///   undecided too, a conservative refusal: LLD's own dynamic program
    ///   catches.
    ///
    /// Without LLD the LLD legs are skipped (`SKIP:`).
    #[test]
    fn eh_frame_walks_without_a_table_and_static_narrow_fdes_are_refused() {
        let directory = tempfile::tempdir().unwrap();
        let dir = directory.path();
        copy_b1(dir);
        fs::write(
            dir.join("libcb.c"),
            "static volatile int sink;\n__attribute__((noinline)) void call_cb(void (*cb)(void)) \
             { cb(); sink = 2; }\n",
        )
        .unwrap();
        fs::write(
            dir.join("raw64.s"),
            "\t.section .eh_frame,\"a\",@progbits\n\t.p2align 3\n\t.4byte 0xffffffff\n\t.8byte \
             16\n\t.8byte 0\n\t.8byte 0\n",
        )
        .unwrap();
        fs::write(
            dir.join("maincb.cc"),
            "#include <cstdio>\nextern \"C\" void call_cb(void (*)(void));\nstatic void thr() { \
             throw 7; }\nint main() { try { call_cb(thr); } catch (int v) { printf(\"caught \
             %d\\n\", v); return 42; } return 1; }\n",
        )
        .unwrap();
        fs::write(
            dir.join("y.cc"),
            "#include <cstdio>\nvolatile int sink;\nextern \"C\" __attribute__((noipa)) void \
             thrower() { throw 7; }\nextern \"C\" __attribute__((noipa)) int y_mid(int x) { \
             thrower(); sink = x; sink = x + 2; return x + 1; }\nint main() {\n  try { y_mid(1); \
             } catch (int v) { printf(\"caught %d\\n\", v); return 42; }\n  return 1;\n}\n",
        )
        .unwrap();
        let pads: String = (1..=22)
            .map(|n| format!("int pad_sink{n};\nvoid pad{n}(void) {{ pad_sink{n}++; }}\n"))
            .collect();
        fs::write(dir.join("pad22.c"), pads).unwrap();
        run_tool(
            dir,
            "cc",
            &["-c", "-O2", "-fPIC", "-o", "libcb.o", "libcb.c"],
        );
        run_tool(dir, "cc", &["-c", "-o", "raw64.o", "raw64.s"]);
        run_tool(dir, "c++", &["-O1", "-S", "-o", "y.s", "y.cc"]);
        let mut asm = fs::read_to_string(dir.join("y.s")).unwrap();
        asm.push_str(NARROW_FDE_ASM);
        fs::write(dir.join("yn.s"), asm).unwrap();
        run_tool(dir, "cc", &["-c", "-o", "yn.o", "yn.s"]);
        run_tool(dir, "cc", &["-c", "-O2", "-o", "pad22.o", "pad22.c"]);
        let error_lines = |text: &str| -> Vec<String> {
            text.lines()
                .filter(|line| line.contains("error[link:"))
                .map(str::to_string)
                .collect()
        };

        // GNU ld writes no table for the 64-bit record; without section
        // headers the walk cannot reach a terminator.
        for (output, group) in [
            ("lib64_nsh.so", "-Wl,raw64.o,libcb.o,-z,nosectionheader"),
            ("lib64.so", "-Wl,raw64.o,libcb.o"),
        ] {
            let result = trust_cg_on(
                None,
                dir,
                &[
                    "--shared",
                    "--nostdlib",
                    "--relocation-model",
                    "pic",
                    "-o",
                    output,
                    "b1_scalars.tmbc",
                    group,
                ],
            );
            let text = stderr(&result);
            let lines = error_lines(&text);
            assert!(
                !result.status.success()
                    && lines.len() == 1
                    && lines[0].contains("[TCG-LINK-EH-FRAME-UNPROVEN]"),
                "{output}: {text}"
            );
            assert!(!dir.join(output).exists(), "{output}");
        }
        let object = trust_cg_on(None, dir, &["-c", "-o", "b1_scalars.o", "b1_scalars.tmbc"]);
        assert!(object.status.success(), "{}", stderr(&object));
        // GNU ld's own library (no section headers), swapped in at run
        // time for a normal `libcb.so` the program was linked against: the
        // throw through `call_cb` aborts; with the normal one it is caught.
        fs::create_dir(dir.join("run64")).unwrap();
        run_tool(
            dir,
            "cc",
            &[
                "-shared",
                "-o",
                "libcb.so",
                "-Wl,-soname,libcb.so",
                "libcb.o",
            ],
        );
        run_tool(
            dir,
            "cc",
            &[
                "-shared",
                "-nostdlib",
                "-o",
                "run64/libcb.so",
                "-Wl,-soname,libcb.so",
                "b1_scalars.o",
                "raw64.o",
                "libcb.o",
                "-Wl,-z,nosectionheader",
            ],
        );
        run_tool(dir, "c++", &["-o", "maincb", "maincb.cc", "-L.", "-lcb"]);
        let throw_with = |library_dir: &str| {
            Command::new(dir.join("maincb"))
                .env("LD_LIBRARY_PATH", dir.join(library_dir))
                .output()
                .unwrap()
                .status
                .code()
        };
        assert_eq!(throw_with("."), Some(42), "the normal library");
        assert_eq!(
            throw_with("run64"),
            None,
            "GNU ld's library without section headers"
        );

        let Some(lld) = lld_dir().map(|lld| lld_cc(dir, &lld)) else {
            return;
        };
        // LLD static: the narrower FDE with a range is undecided.
        let args = |mode: &'static str, output: &'static str| {
            [
                mode,
                "-o",
                output,
                "b1_scalars.tmbc",
                "-Wl,yn.o,pad22.o,-lstdc++,-lm",
            ]
        };
        let result = trust_cg_on(Some(&lld), dir, &args("--static", "yn_static"));
        let text = stderr(&result);
        let lines = error_lines(&text);
        assert!(
            !result.status.success()
                && lines.len() == 1
                && lines[0].contains(
                    "[TCG-LINK-EH-FRAME-UNPROVEN] the linked output for yn_static is refused \
                     because the check cannot show which FDE libgcc takes where live FDEs begin \
                     together (1 starts)"
                ),
            "{text}"
        );
        run_tool(
            dir,
            &lld.join("cc").display().to_string(),
            &[
                "-static",
                "-o",
                "yn_static_raw",
                "-Wl,--eh-frame-hdr",
                "b1_scalars.o",
                "yn.o",
                "pad22.o",
                "-lstdc++",
                "-lm",
            ],
        );
        assert_eq!(
            run_program(&dir.join("yn_static_raw")).0,
            None,
            "the raw static throw"
        );
        // A dynamic executable: refused as undecided too, and LLD's own
        // program, whose table decides, catches the throw.
        let result = trust_cg_on(Some(&lld), dir, &args("--no-pie", "yn_dynamic"));
        let text = stderr(&result);
        let lines = error_lines(&text);
        assert!(
            !result.status.success()
                && lines.len() == 1
                && lines[0].contains(
                    "[TCG-LINK-EH-FRAME-UNPROVEN] the linked output for yn_dynamic is refused \
                     because the check cannot show which FDE libgcc takes where live FDEs begin \
                     together (1 starts)"
                ),
            "{text}"
        );
        assert!(!dir.join("yn_dynamic").exists());
        run_tool(
            dir,
            &lld.join("cc").display().to_string(),
            &[
                "-no-pie",
                "-o",
                "yn_dynamic_raw",
                "b1_scalars.o",
                "yn.o",
                "pad22.o",
                "-lstdc++",
                "-lm",
            ],
        );
        let (code, stdout) = run_program(&dir.join("yn_dynamic_raw"));
        assert_eq!((code, stdout.as_str()), (Some(42), "caught 7\n"));
    }

    /// A static `-nostdlib` program: `_start` calls `isize_add_one(41)`
    /// (`b1_scalars.tmbc`) and exits with its value through syscall 93; a
    /// read-only `.far` section holds one word, and placed at
    /// `0x2000000000` it makes LLD extend the first `PT_LOAD` (the ELF
    /// header's) to it: the file is a 128 GiB sparse image.
    const FAR_START_SOURCE: &str = "\t.text\n\t.globl _start\n\t.type _start, %function\n\
        _start:\n\tmov x0, #41\n\tbl isize_add_one\n\tmov x8, #93\n\tsvc #0\n\t.size _start, \
        .-_start\n\t.section .far,\"a\",%progbits\n\t.globl far_word\nfar_word:\n\t.xword 42\n";

    /// The closure audit's read-back finding: `trust-cg --static --nostdlib
    /// --no-pie -Wl,start.o -Wl,--section-start=.far=0x2000000000 -o far
    /// b1_scalars.tmbc` with LLD's `cc` first on `PATH` made LLD write a
    /// 128 GiB sparse image, which the driver read back whole for its image
    /// checks: the CLI was killed for memory (exit 137) and left its
    /// `.tcg-link-*` staging directory. The image is now read back as the
    /// ranges its checks read. Under a 16 GiB address-space limit (a whole
    /// read of the image cannot fit it, so a regression is refused as
    /// unreadable instead of exhausting the host; the `cc` wrapper lifts the
    /// limit for LLD) the link completes, the peak RSS of the CLI and every
    /// process it waited for stays below 512 MiB, nothing is left next to
    /// the output, and the program exits 42. LLD's `--build-id` is turned
    /// off: hashing the image would read all 128 GiB of it. The peak RSS is
    /// `wait4`'s `ru_maxrss` for the shell that execs the CLI ([`peak_rss`]),
    /// so no `/usr/bin/time` is needed. Without LLD the test is skipped
    /// (`SKIP:`).
    #[test]
    fn an_image_placed_far_from_its_elf_header_is_checked_without_reading_its_hole() {
        let directory = tempfile::tempdir().unwrap();
        let dir = directory.path();
        copy_b1(dir);
        assemble(dir, "start", FAR_START_SOURCE);
        let Some(lld) = lld_dir() else {
            return;
        };
        let lld = lld_cc(dir, &lld);
        let unlimited = dir.join("unlimited-cc");
        fs::create_dir(&unlimited).unwrap();
        write_executable_script(
            &unlimited.join("cc"),
            &format!(
                "#!/bin/sh\nulimit -S -v unlimited\nexec '{}' \"$@\"\n",
                lld.join("cc").display()
            ),
        );
        let path = std::env::var_os("PATH").unwrap_or_default();
        let paths = std::iter::once(unlimited).chain(std::env::split_paths(&path));
        let mut command = Command::new("/bin/sh");
        command
            .current_dir(dir)
            .env("PATH", std::env::join_paths(paths).unwrap())
            .arg("-c")
            .arg("ulimit -S -v 16777216 && exec \"$@\"")
            .arg("sh");
        let before = listing(dir);
        command.arg(env!("CARGO_BIN_EXE_trust-cg")).args([
            // Claim-less fixture: refused by default since WS7.5 (DG-73).
            "--permit-unlicensed",
            "--static",
            "--nostdlib",
            "--no-pie",
            "-Wl,start.o",
            "-Wl,--section-start=.far=0x2000000000",
            "-Wl,--build-id=none",
            "-o",
            "far",
            "b1_scalars.tmbc",
        ]);
        let scratch = tempfile::tempdir().unwrap();
        let (output, rss) = peak_rss(&mut command, scratch.path());
        let far = dir.join("far");
        let length = fs::metadata(&far).map(|metadata| metadata.len());
        // The program maps 128 GiB: an inherited soft address-space limit
        // would kill it at exec.
        let status = Command::new("/bin/sh")
            .arg("-c")
            .arg("ulimit -S -v unlimited 2>/dev/null; exec \"$0\"")
            .arg(&far)
            .status();
        let _ = fs::remove_file(&far);
        assert!(output.status.success(), "{}", stderr(&output));
        assert!(
            length.as_ref().is_ok_and(|length| *length > 1 << 36),
            "{length:?}"
        );
        assert_eq!(status.unwrap().code(), Some(42));
        assert_eq!(listing(dir), before);
        eprintln!("peak RSS of the CLI and the processes it waited for: {rss} KiB");
        assert!(rss > 0 && rss < 512 << 10, "peak RSS {rss} KiB");
    }

    /// Renames the output `.eh_frame` (the eighth closure audit's `renb.ld`).
    const RENAMED_EH_FRAME: &str =
        "SECTIONS { .ehx : { KEEP(*(.eh_frame)) } } INSERT BEFORE .text;\n";

    /// Merges the `.eh_frame` input into `.rodata`.
    const MERGED_EH_FRAME: &str =
        "SECTIONS { .rodata : { *(.rodata .rodata.*) *(.eh_frame) } } INSERT AFTER .init;\n";

    /// Renames the output `.eh_frame` and discards `.eh_frame_hdr` (so the
    /// image has no `PT_GNU_EH_FRAME`).
    const RENAMED_WITHOUT_HDR: &str = "SECTIONS { .ehx : { KEEP(*(.eh_frame)) } /DISCARD/ : { \
                                       *(.eh_frame_hdr) } } INSERT BEFORE .text;\n";

    /// The eighth closure audit at `9a9eda112`: `trust-cg --static --no-pie
    /// -o c_far b1_scalars.tmbc -Wl,bt2.o -Wl,-T,renb.ld
    /// -Wl,--no-eh-frame-hdr
    /// -Wl,--section-start=.ehx=0x10000000,--section-start=.text=0xd0000000`
    /// with LLD's `cc` first on `PATH` installed a static executable whose
    /// 916 FDEs, in the renamed output section `.ehx`, were all written
    /// truncated, and which aborted in `_Unwind_Backtrace`: the `.eh_frame`
    /// check found `.eh_frame` by name or through `PT_GNU_EH_FRAME`, but
    /// libgcc reads a static executable's frames where `crtbeginT.o`
    /// registers them, whatever the section is called. The driver now reads
    /// the link map and decodes every `.eh_frame` input wherever it lies.
    /// Through LLD the far placement, with [`BT_SOURCE`] and a trust-cg
    /// frame, is refused with `[TCG-LINK-EH-FRAME-WINDOW]` with and without
    /// `-s`, with a `-Map` of the user's (which the driver writes from its
    /// own map, which it reads; a `-Map` naming the output is not written,
    /// and the output keeps its bytes),
    /// and with `.eh_frame_hdr` discarded by the script instead of
    /// `--no-eh-frame-hdr`; nothing is written, a file at the output keeps its bytes, and
    /// the same objects linked by LLD outside the driver do not backtrace.
    /// GNU ld refuses the far placement itself (classified). Since the v4
    /// verifier's repair a static executable with a linker script and no
    /// `.eh_frame_hdr` table is refused as unproven (the check does not read
    /// scripts, which can bind another name to a registration function):
    /// the near twins without a table (renamed, stripped, with
    /// `.eh_frame_hdr` discarded, and for GNU ld merged into `.rodata`, or
    /// renamed with the flag, since GNU ld writes no table for a renamed
    /// section) are refused, although GNU ld's runs outside the driver; the
    /// user's map is still written. LLD writes a table for its renamed
    /// section, and those near twins link, run and backtrace through the
    /// trust-cg frame into `main`, stripped or not; so do gold's
    /// (which keeps `.eh_frame` named whatever the script says, so its row
    /// is a plain static link with and without a user map). LLD's map
    /// prints pieces from the start of their output section, so a
    /// `.rodata` holding them and other input does not show where they lie,
    /// and `-Wl,-M` sends the map to standard output: both static images
    /// are refused as unproven, by name. Since the v6 verifier's repair a
    /// static glibc link with a linker script is also refused as
    /// `[TCG-LINK-IRELATIVE-UNAPPLIED]` (a script can move glibc's start-up
    /// code), so LLD's renamed table twins, which linked and backtraced, are
    /// refused whatever their table. Without LLD or gold their legs are
    /// skipped (`SKIP:`).
    #[test]
    fn a_static_executables_eh_frame_input_is_read_whatever_its_section_name() {
        let directory = tempfile::tempdir().unwrap();
        let dir = directory.path();
        copy_b1(dir);
        write_module(dir, "through.tmbc", &through_module());
        fs::write(dir.join("bt.c"), BT_SOURCE).unwrap();
        run_tool(dir, "cc", &["-c", "-O1", "-o", "bt.o", "bt.c"]);
        fs::write(dir.join("renamed.ld"), RENAMED_EH_FRAME).unwrap();
        fs::write(dir.join("merged.ld"), MERGED_EH_FRAME).unwrap();
        fs::write(dir.join("nohdr.ld"), RENAMED_WITHOUT_HDR).unwrap();
        let lld = lld_dir().map(|lld| lld_cc(dir, &lld));
        let gold = gold_cc(dir);
        let args = |output: &str, extra: &[&str]| -> Vec<String> {
            let mut args: Vec<String> = [
                "--static",
                "--no-pie",
                "-o",
                output,
                "b1_scalars.tmbc",
                "through.tmbc",
                "-Wl,bt.o",
            ]
            .iter()
            .map(|arg| arg.to_string())
            .collect();
            args.extend(extra.iter().map(|arg| arg.to_string()));
            args
        };
        let cli = |bin: Option<&Path>, args: &[String]| {
            trust_cg_on(
                bin,
                dir,
                &args.iter().map(String::as_str).collect::<Vec<_>>(),
            )
        };
        // The `error[link:` lines, but for a static glibc image's refusal as
        // [`IRELATIVE`] where a script leaves glibc's start-up code unknown.
        let error_lines = |text: &str| -> Vec<String> {
            text.lines()
                .filter(|line| line.contains("error[link:") && !line.contains(IRELATIVE))
                .map(str::to_string)
                .collect()
        };
        // Refused with nothing written, with and without a file at the
        // output; `check` reads the `error[link:` lines.
        let refused = |bin: Option<&Path>, args: &[String], output: &str, check: &dyn Fn(&str)| {
            for preexisting in [None, Some(&b"precious\n"[..])] {
                if let Some(bytes) = preexisting {
                    fs::write(dir.join(output), bytes).unwrap();
                }
                let mut before = listing(dir);
                before.retain(|name| !name.starts_with("user"));
                let result = cli(bin, args);
                let text = stderr(&result);
                assert!(!result.status.success(), "{output}: {text}");
                check(&text);
                let mut after = listing(dir);
                after.retain(|name| !name.starts_with("user"));
                assert_eq!(after, before, "{output}");
                match preexisting {
                    None => assert!(!dir.join(output).exists(), "{output}"),
                    Some(bytes) => {
                        assert_eq!(fs::read(dir.join(output)).unwrap(), bytes, "{output}");
                        fs::remove_file(dir.join(output)).unwrap();
                    }
                }
            }
        };
        // A static executable with a linker script and no table is also
        // unproven: the check does not read scripts, which can bind another
        // name to a registration function.
        let scripted = "and the -Wl option `-T` can bind another name to a registration \
                        function, redirect a reference to one";
        let window = |output: &str| {
            let output = output.to_string();
            move |text: &str| {
                let lines = error_lines(text);
                assert!(
                    lines.iter().any(|line| line.contains(&format!(
                        "[TCG-LINK-EH-FRAME-WINDOW] the linked output for {output} is refused: "
                    )) && line
                        .contains(" FDEs describe code outside executable memory")
                        && line.starts_with("trust-cg: error[link:relocation-out-of-range] ")),
                    "{output}: {text}"
                );
                assert!(
                    lines
                        .iter()
                        .all(|line| line.contains("[TCG-LINK-EH-FRAME-WINDOW]")
                            || line.contains(scripted)),
                    "{output}: {text}"
                );
            }
        };
        let script_unproven = |output: &str| {
            let output = output.to_string();
            move |text: &str| {
                let lines = error_lines(text);
                assert!(
                    !lines.is_empty()
                        && lines.iter().all(|line| line.starts_with(&format!(
                            "trust-cg: error[link:unclassified]: [TCG-LINK-EH-FRAME-UNPROVEN] the \
                             linked output for {output} is refused because the check cannot show \
                             that libgcc finds the FDE of every function: it is a static \
                             executable, "
                        )) && line.contains(scripted)),
                    "{output}: {text}"
                );
            }
        };
        // A static glibc image with a script, refused only because glibc's
        // start-up code is not shown to apply its IFUNC relocations.
        let script_irelative = |output: &str| {
            let output = output.to_string();
            move |text: &str| {
                let lines: Vec<&str> = text
                    .lines()
                    .filter(|line| line.contains("error[link:"))
                    .collect();
                assert!(
                    !lines.is_empty()
                        && lines.iter().all(|line| line.contains(&format!(
                            "{IRELATIVE} the linked output for {output} is refused because it is \
                             a static executable with IFUNC relocations"
                        )) && line
                            .contains("and the -Wl option `-T` can bind")),
                    "{output}: {text}"
                );
            }
        };
        let unproven = |output: &str, why: &str| {
            let (output, why) = (output.to_string(), why.to_string());
            move |text: &str| {
                assert!(
                    error_lines(text).iter().any(|line| line.starts_with(
                        "trust-cg: error[link:unclassified]: [TCG-LINK-EH-FRAME-UNPROVEN] the \
                         linked output for "
                    ) && line.contains(&output)
                        && line.contains(
                            "libgcc first searches the frames a program registers, in the \
                             .eh_frame input wherever the linker placed it"
                        )
                        && line.contains(
                            "and any program can register them (crtbeginT.o does in a static \
                             executable"
                        )
                        && line.contains(&why)),
                    "{output}: {text}"
                );
            }
        };
        // A near twin links and runs; unless stripped, its backtrace crosses
        // the trust-cg frame into `main`.
        let backtraces = |bin: Option<&Path>, args: &[String], output: &str, stripped: bool| {
            let result = cli(bin, args);
            assert!(result.status.success(), "{output}: {}", stderr(&result));
            if stripped {
                let (code, stdout) = run_program(&dir.join(output));
                assert_eq!(code, Some(0), "{output}: {stdout}");
                assert!(stdout.starts_with("v=42 "), "{output}: {stdout}");
                assert!(stdout.matches("pc=").count() >= 4, "{output}: {stdout}");
            } else {
                let frames = backtrace_of(&dir.join(output));
                assert!(
                    frames.len() >= 4 && frames[..3] == ["bt_depth", "tcg_bt_through", "main"],
                    "{output}: {frames:?}"
                );
            }
            fs::remove_file(dir.join(output)).unwrap();
        };
        let far = [
            "-Wl,-T,renamed.ld",
            "-Wl,--no-eh-frame-hdr",
            "-Wl,--section-start=.ehx=0x10000000,--section-start=.text=0xd0000000",
        ];

        if let Some(bin) = lld.as_deref() {
            for (output, extra) in [
                ("far_lld", &[][..]),
                ("far_lld_s", &["-Wl,-s"][..]),
                ("far_lld_map", &["-Wl,-Map=user_lld.map"][..]),
                ("far_lld_self_map", &["-Wl,-Map=far_lld_self_map"][..]),
            ] {
                let mut extra = extra.to_vec();
                extra.extend(far);
                refused(Some(bin), &args(output, &extra), output, &window(output));
            }
            // The user's map, written from the driver's, which was read.
            let map = fs::read_to_string(dir.join("user_lld.map")).unwrap();
            assert!(map.contains(" .ehx\n"), "{map}");
            // `.eh_frame_hdr` discarded by the script, not by the flag.
            let discarded = [
                "-Wl,-T,nohdr.ld",
                "-Wl,--section-start=.ehx=0x10000000,--section-start=.text=0xd0000000",
            ];
            refused(
                Some(bin),
                &args("far_lld_discard", &discarded),
                "far_lld_discard",
                &window("far_lld_discard"),
            );
            // The near layouts without a table are refused as scripts; with
            // the table LLD writes for the renamed section they link and
            // backtrace.
            let discarded = [
                "-Wl,-T,nohdr.ld",
                "-Wl,--section-start=.ehx=0x10000000,--section-start=.text=0x20000000",
            ];
            refused(
                Some(bin),
                &args("near_lld_discard", &discarded),
                "near_lld_discard",
                &script_unproven("near_lld_discard"),
            );
            let near = [
                "-Wl,-T,renamed.ld",
                "-Wl,--no-eh-frame-hdr",
                "-Wl,--section-start=.ehx=0x10000000,--section-start=.text=0x20000000",
            ];
            refused(
                Some(bin),
                &args("near_lld", &near),
                "near_lld",
                &script_unproven("near_lld"),
            );
            let mut stripped = near.to_vec();
            stripped.push("-Wl,-s");
            refused(
                Some(bin),
                &args("near_lld_s", &stripped),
                "near_lld_s",
                &script_unproven("near_lld_s"),
            );
            // Its table twins: the script can move glibc's start-up code,
            // so each is refused whatever its table (the v6 verifier's
            // repair).
            let tabled = [near[0], near[2]];
            refused(
                Some(bin),
                &args("near_lld_table", &tabled),
                "near_lld_table",
                &script_irelative("near_lld_table"),
            );
            let mut stripped = tabled.to_vec();
            stripped.push("-Wl,-s");
            refused(
                Some(bin),
                &args("near_lld_table_s", &stripped),
                "near_lld_table_s",
                &script_irelative("near_lld_table_s"),
            );
            let merged = ["-Wl,-T,merged.ld", "-Wl,--no-eh-frame-hdr"];
            refused(
                Some(bin),
                &args("merged_lld", &merged),
                "merged_lld",
                &unproven(
                    "merged_lld",
                    "LLD's map gives the addresses of the .eh_frame pieces in the output section \
                     `.rodata` from the start of that section, which also holds other input",
                ),
            );
            let mut printed = near.to_vec();
            printed.push("-Wl,-M");
            refused(
                Some(bin),
                &args("printed_lld", &printed),
                "printed_lld",
                &unproven(
                    "printed_lld",
                    "the -Wl option `-M` sent the link map to standard output",
                ),
            );
            // LLD outside the driver installs the far program, and it does
            // not backtrace into `main`.
            for module in ["b1_scalars", "through"] {
                let output = cli(
                    None,
                    &[
                        "-c".into(),
                        "-o".into(),
                        format!("{module}.o"),
                        format!("{module}.tmbc"),
                    ],
                );
                assert!(output.status.success(), "{}", stderr(&output));
            }
            run_tool(
                dir,
                &bin.join("cc").display().to_string(),
                &[
                    "-static",
                    "-no-pie",
                    "-o",
                    "raw_lld",
                    "b1_scalars.o",
                    "through.o",
                    "bt.o",
                    "-Wl,-z,noexecstack",
                    far[0],
                    far[1],
                    far[2],
                ],
            );
            let (code, stdout) = run_program(&dir.join("raw_lld"));
            eprintln!("raw_lld, linked by LLD without the driver: exit {code:?}, {stdout}");
            assert!(
                code != Some(0) || stdout.matches("pc=").count() < 3,
                "{code:?} {stdout}"
            );
        }

        // GNU ld refuses the far placement itself.
        let result = cli(None, &args("far_gnu", &far));
        let text = stderr(&result);
        assert!(
            !result.status.success()
                && text.contains("relocation truncated to fit: R_AARCH64_PREL32")
                && error_lines(&text).iter().any(|line| line
                    .starts_with("trust-cg: error[link:relocation-out-of-range] ")
                    && line.contains(" (R_AARCH64_PREL32): ")),
            "{text}"
        );
        assert!(!dir.join("far_gnu").exists());
        // GNU ld writes no table for a renamed or merged `.eh_frame`: its
        // near layouts, which run, are refused as scripts without a table.
        let renamed = ["-Wl,-T,renamed.ld", "-Wl,--no-eh-frame-hdr"];
        let mut stripped = renamed.to_vec();
        stripped.push("-Wl,-s");
        let merged = ["-Wl,-T,merged.ld", "-Wl,--no-eh-frame-hdr"];
        let mut mapped = renamed.to_vec();
        mapped.push("-Wl,-Map=user_gnu.map");
        for (output, extra) in [
            ("near_gnu", &renamed[..]),
            ("near_gnu_s", &stripped[..]),
            ("merged_gnu", &merged[..]),
            ("discard_gnu", &["-Wl,-T,nohdr.ld"][..]),
            ("renamed_gnu_hdr", &["-Wl,-T,renamed.ld"][..]),
            ("mapped_gnu", &mapped[..]),
        ] {
            refused(None, &args(output, extra), output, &script_unproven(output));
        }
        assert!(
            fs::read_to_string(dir.join("user_gnu.map"))
                .unwrap()
                .contains("Linker script and memory map")
        );
        // GNU ld outside the driver: the near layout runs and backtraces.
        compile_bt_modules(dir);
        run_tool(
            dir,
            "cc",
            &[
                "-static",
                "-no-pie",
                "-o",
                "raw_near_gnu",
                "b1_scalars.o",
                "through.o",
                "bt.o",
                "-Wl,-z,noexecstack",
                renamed[0],
                renamed[1],
            ],
        );
        assert!(backtrace_of(&dir.join("raw_near_gnu")).len() >= 4);

        // gold keeps `.eh_frame` named; its static programs read their map.
        if let Some(bin) = gold.as_deref() {
            backtraces(Some(bin), &args("static_gold", &[]), "static_gold", false);
            backtraces(
                Some(bin),
                &args("mapped_gold", &["-Wl,-Map=user_gold.map"]),
                "mapped_gold",
                false,
            );
            assert!(
                fs::read_to_string(dir.join("user_gold.map"))
                    .unwrap()
                    .contains("\nMemory map\n")
            );
        }
    }

    /// A foreign assembly object whose `.eh_frame` (a CIE and FDEs for
    /// `odd_one` and `odd_two`) is 4-byte aligned and 60 bytes long, 4 short
    /// of a multiple of 8: an 8-byte-aligned input after it starts 4 bytes
    /// later, and GNU ld fills them with zeros in an output section not named
    /// `.eh_frame`.
    const ODD_EH_FRAME_ASM: &str = "\t.text\n\t.globl odd_one\n\t.type odd_one, %function\n\
        odd_one:\n\tret\n\t.size odd_one, .-odd_one\n\t.globl odd_two\n\t.type odd_two, \
        %function\nodd_two:\n\tret\n\t.size odd_two, .-odd_two\n\t.section \
        .eh_frame,\"a\",@progbits\n\t.p2align 2\nocie:\n\t.4byte ocie_end - ocie_id\nocie_id:\n\t\
        .4byte 0\n\t.byte 1\n\t.asciz \"zR\"\n\t.uleb128 4\n\t.sleb128 -8\n\t.uleb128 30\n\t\
        .uleb128 1\n\t.byte 0x1b\n\t.byte 0x0c, 31, 0\n\t.p2align 2\nocie_end:\n\t.4byte \
        ofde1_end - ofde1_id\nofde1_id:\n\t.4byte ofde1_id - ocie\n\t.4byte odd_one - .\n\t\
        .4byte 4\n\t.uleb128 0\n\t.p2align 2\nofde1_end:\n\t.4byte ofde2_end - ofde2_id\n\
        ofde2_id:\n\t.4byte ofde2_id - ocie\n\t.4byte odd_two - .\n\t.4byte 4\n\t.uleb128 0\n\t\
        .p2align 2\nofde2_end:\n";

    /// Keeps `.eh_frame` named, with `bt.o`'s input placed before every
    /// other, `crtbeginT.o`'s included.
    const FRONT_EH_FRAME: &str = "SECTIONS { .eh_frame : { KEEP(*bt.o(.eh_frame)) \
                                  KEEP(*(.eh_frame)) } } INSERT AFTER .rodata;\n";

    /// The padding finding of the second repair, closed: a static
    /// executable's `crtbeginT.o` registers its frames, and libgcc's walk of
    /// them ends at the first zero length. Through GNU ld with [`ODD_EH_FRAME_ASM`] before
    /// `bt.o` in a renamed (`.ehx`) or `.rodata`-merged `.eh_frame`, the 4
    /// bytes of padding after it end the walk, 907 of 916 FDEs are missed
    /// (libgcc's own among them), GNU ld writes no table for such a section,
    /// and the program aborts in `_Unwind_Backtrace` (134) outside the
    /// driver. Each such `--static` link is refused as
    /// `[TCG-LINK-EH-FRAME-UNPROVEN]`, with and without `--no-eh-frame-hdr`,
    /// naming where the walk stops, with nothing written; so is `bt.o`'s input
    /// placed before `crtbeginT.o`'s with `--no-eh-frame-hdr` (outside the
    /// driver its backtrace stops after one frame). Twins that install and
    /// backtrace through the trust-cg frame into `main`: the renamed section
    /// without the odd input, the odd input in a section named `.eh_frame`
    /// (GNU ld pads by record), and `bt.o`'s input before `crtbeginT.o`'s
    /// with the table the driver asks for (the registered walk misses its
    /// FDEs, and static glibc answers libgcc's `dl_iterate_phdr` fallback to
    /// the table). gold's static `crtbeginT.o` registers nothing: its odd
    /// link unwinds through the table alone. Through LLD the odd and front
    /// layouts' scripts without a table are refused (the check does not read
    /// scripts, which can bind another name to a registration function), and
    /// their table twins install and unwind.
    ///
    /// The round-3 verifier's LLD layout: a `--static --nostdlib` link whose
    /// trust-cg objects come first and whose start files follow as `-Wl`
    /// operands, `crtbeginT.o` first. LLD writes each CIE with the FDEs that
    /// name it; trust-cg's CIE heads the section, `crtbeginT.o`'s own CIE
    /// (the first of its kind) comes after it, and `frame_dummy` registers
    /// from that CIE, so trust-cg's FDEs lie before the walk. Without a table
    /// it is refused through LLD and GNU ld, and with the table the driver
    /// asks for it installs and backtraces into `main` through each.
    ///
    /// The v4 verifier: a copy of `crtbeginT.o` under another name, and one
    /// repacked with `ld -r`, were installed without a table through GNU ld
    /// and LLD, and their programs stop after 2 frames (GNU ld's, outside the
    /// driver, here). Each is refused now: registrants are read by the
    /// registration functions they reference, and only the C driver's own
    /// `crtbeginT.o` is shown where it registers; each table twin installs.
    /// LLD's standard order, `bt.o` before `crtbeginT.o` and `--gc-sections`
    /// were refused, but `crtbeginT.o`'s CIE merges into `crt1.o`'s and it
    /// registers from the synthetic `.eh_frame`'s start (gdb, `x0` at
    /// `__register_frame_info`): each installs without a table and
    /// backtraces into `main`. A symbol assignment or `. += 0x38` in LLD's
    /// `.eh_frame` output section (`sym.ld`, `zero38.ld`) left no start and
    /// was installed; without a table each is refused, and `sym.ld`'s table
    /// twin installs (LLD's own `sym.ld` program stops after 2 frames).
    ///
    /// The v6 verifier: a script or `-z muldefs` can also move glibc's
    /// start-up code, so every static glibc link with one is refused as
    /// `[TCG-LINK-IRELATIVE-UNAPPLIED]` whatever its table, and the script
    /// table twins above (GNU ld's `front`, LLD's `odd_renamed_lld_table`,
    /// `front_lld` and `sym_lld`), which installed and backtraced, are
    /// refused. Without LLD or gold their legs are skipped (`SKIP:`).
    #[test]
    fn a_static_executables_registered_frames_must_reach_every_fde() {
        let directory = tempfile::tempdir().unwrap();
        let dir = directory.path();
        copy_b1(dir);
        write_module(dir, "through.tmbc", &through_module());
        fs::write(dir.join("bt.c"), UNWIND_BT_SOURCE).unwrap();
        run_tool(dir, "cc", &["-c", "-O1", "-o", "bt.o", "bt.c"]);
        fs::write(dir.join("odd.s"), ODD_EH_FRAME_ASM).unwrap();
        run_tool(dir, "cc", &["-c", "-o", "odd.o", "odd.s"]);
        fs::write(dir.join("renamed.ld"), RENAMED_EH_FRAME).unwrap();
        fs::write(dir.join("merged.ld"), MERGED_EH_FRAME).unwrap();
        fs::write(dir.join("front.ld"), FRONT_EH_FRAME).unwrap();
        let lld = lld_dir().map(|lld| lld_cc(dir, &lld));
        let gold = gold_cc(dir);
        let args = |output: &str, extra: &[&str]| -> Vec<String> {
            [
                "--static",
                "--no-pie",
                "-o",
                output,
                "b1_scalars.tmbc",
                "through.tmbc",
            ]
            .iter()
            .chain(extra)
            .map(|arg| arg.to_string())
            .collect()
        };
        let odd = "-Wl,odd.o,bt.o";
        let nohdr = "-Wl,--no-eh-frame-hdr";
        let stops = "it is a static executable, whose crtbeginT.o registers the frames from ";
        let walk = "and libgcc's walk of them, which ends at the first zero length, stops at ";
        // A linker script without a table (GNU ld writes none for a renamed
        // or merged section) is refused: the check does not read scripts,
        // which can bind another name to a registration function.
        let scripted = "the -Wl option `-T` can bind another name to a registration function";
        for (output, extra) in [
            ("odd_renamed", &[odd, "-Wl,-T,renamed.ld"][..]),
            ("odd_renamed_nohdr", &[odd, "-Wl,-T,renamed.ld", nohdr][..]),
            ("odd_merged", &[odd, "-Wl,-T,merged.ld", nohdr][..]),
            ("front_nohdr", &["-Wl,bt.o", "-Wl,-T,front.ld", nohdr][..]),
            ("renamed", &["-Wl,bt.o", "-Wl,-T,renamed.ld"][..]),
        ] {
            refused_by_cli(
                dir,
                None,
                &args(output, extra),
                "[TCG-LINK-EH-FRAME-UNPROVEN]",
                &[scripted],
            );
        }
        installed_by_cli(dir, None, &args("odd_named", &[odd]));
        // Its table twin with a script: the script can move glibc's start-up
        // code, so the image is refused whatever its table (the v6
        // verifier's repair).
        let script_start_up = "the -Wl option `-T` can bind another name to a registration \
                               function, redirect a reference to one or let a second definition \
                               of one stand, and so to any function of the C runtime's start-up \
                               or unwinding code";
        refused_by_cli(
            dir,
            None,
            &args("front", &["-Wl,bt.o", "-Wl,-T,front.ld"]),
            IRELATIVE,
            &[script_start_up],
        );
        // GNU ld outside the driver.
        compile_bt_modules(dir);
        let raw = |output: &str, extra: &[&str]| {
            let mut arguments = vec![
                "-static",
                "-no-pie",
                "-o",
                output,
                "b1_scalars.o",
                "through.o",
                "-Wl,-z,noexecstack",
            ];
            arguments.extend(extra);
            run_tool(dir, "cc", &arguments);
            let (code, stdout) = run_program(&dir.join(output));
            eprintln!("{output}, linked by GNU ld without the driver: exit {code:?}, {stdout}");
            (code, stdout.matches("pc=").count())
        };
        assert_eq!(
            raw("raw_odd_renamed", &["odd.o", "bt.o", "-Wl,-T,renamed.ld"]).0,
            None,
            "raw_odd_renamed"
        );
        let (code, frames) = raw("raw_front_nohdr", &["bt.o", "-Wl,-T,front.ld", nohdr]);
        assert!(code == Some(0) && frames < 3, "{code:?} {frames}");
        if let Some(bin) = gold.as_deref() {
            installed_by_cli(dir, Some(bin), &args("odd_named_gold", &[odd]));
        }
        // LLD: a linker script without a table is refused too; the table
        // twin links and runs.
        if let Some(bin) = lld.as_deref() {
            for (output, extra) in [
                ("odd_renamed_lld", &[odd, "-Wl,-T,renamed.ld", nohdr][..]),
                (
                    "front_nohdr_lld",
                    &["-Wl,bt.o", "-Wl,-T,front.ld", nohdr][..],
                ),
            ] {
                refused_by_cli(
                    dir,
                    Some(bin),
                    &args(output, extra),
                    "[TCG-LINK-EH-FRAME-UNPROVEN]",
                    &[scripted],
                );
            }
            for (output, extra) in [
                ("odd_renamed_lld_table", &[odd, "-Wl,-T,renamed.ld"][..]),
                ("front_lld", &["-Wl,bt.o", "-Wl,-T,front.ld"][..]),
            ] {
                refused_by_cli(
                    dir,
                    Some(bin),
                    &args(output, extra),
                    IRELATIVE,
                    &[script_start_up],
                );
            }
        }
        // The round-3 verifier's layout.
        let file = |name: &str| {
            let printed = Command::new("cc")
                .arg(format!("-print-file-name={name}"))
                .output()
                .unwrap();
            String::from_utf8(printed.stdout)
                .unwrap()
                .trim()
                .to_string()
        };
        let start_files = format!(
            "-Wl,{},{},{},bt.o,--start-group,-lgcc,-lgcc_eh,-lc,--end-group,{},{}",
            file("crtbeginT.o"),
            file("crt1.o"),
            file("crti.o"),
            file("crtend.o"),
            file("crtn.o")
        );
        let first = |output: &str, extra: &[&str]| -> Vec<String> {
            [
                "--static",
                "--nostdlib",
                "-o",
                output,
                "b1_scalars.tmbc",
                "through.tmbc",
                start_files.as_str(),
            ]
            .iter()
            .chain(extra)
            .map(|arg| arg.to_string())
            .collect()
        };
        let mut linkers: Vec<(&str, Option<&Path>)> = vec![("gnu", None)];
        linkers.extend(lld.as_deref().map(|lld| ("lld", Some(lld))));
        for (linker, bin) in &linkers {
            refused_by_cli(
                dir,
                *bin,
                &first(&format!("first_cie_{linker}_nohdr"), &[nohdr]),
                "[TCG-LINK-EH-FRAME-UNPROVEN]",
                &[stops, walk],
            );
            installed_by_cli(dir, *bin, &first(&format!("first_cie_{linker}"), &[]));
        }
        if let Some(lld) = lld.as_deref() {
            let mut arguments = vec![
                "-static".to_string(),
                "-nostdlib".into(),
                "-o".into(),
                "raw_first_cie".into(),
                "b1_scalars.o".into(),
                "through.o".into(),
            ];
            arguments.extend(
                start_files
                    .strip_prefix("-Wl,")
                    .unwrap()
                    .split(',')
                    .map(|piece| {
                        if piece.starts_with('-') {
                            format!("-Wl,{piece}")
                        } else {
                            piece.to_string()
                        }
                    }),
            );
            arguments.extend([nohdr.to_string(), "-Wl,-z,noexecstack".into()]);
            run_tool(
                dir,
                &lld.join("cc").display().to_string(),
                &arguments.iter().map(String::as_str).collect::<Vec<_>>(),
            );
            let (code, stdout) = run_program(&dir.join("raw_first_cie"));
            eprintln!("raw_first_cie, linked by LLD without the driver: exit {code:?}, {stdout}");
            assert!(stdout.matches("pc=").count() < 3, "{code:?} {stdout}");
        }

        // The v4 verifier. Registrants are read by behaviour: an input that
        // references a registration function and is not the C driver's own
        // `crtbeginT.o` (a copy of it under another name, or one repacked
        // with `ld -r`) registers from where the check does not show, and
        // without a table the image is unproven, through GNU ld and LLD; the
        // table twin links and runs.
        let (crt1, crti, crtbegint) = (file("crt1.o"), file("crti.o"), file("crtbeginT.o"));
        fs::copy(&crtbegint, dir.join("cbt_copy.o")).unwrap();
        run_tool(dir, "ld", &["-r", "-o", "cbt_r.o", crtbegint.as_str()]);
        let ordered = |output: &str, order: &[&str], extra: &[&str]| -> Vec<String> {
            let inputs = format!(
                "-Wl,{},--start-group,-lgcc,-lgcc_eh,-lc,--end-group,{},{}",
                order.join(","),
                file("crtend.o"),
                file("crtn.o")
            );
            [
                "--static",
                "--nostdlib",
                "-o",
                output,
                "b1_scalars.tmbc",
                "through.tmbc",
                inputs.as_str(),
            ]
            .iter()
            .chain(extra)
            .map(|arg| arg.to_string())
            .collect()
        };
        for (linker, bin) in &linkers {
            for copy in ["cbt_copy.o", "cbt_r.o"] {
                let order = [copy, crt1.as_str(), crti.as_str(), "bt.o"];
                let why = format!(
                    "the input {copy} references __register_frame_info, and the check shows where \
                     only the C driver's own crtbeginT.o"
                );
                refused_by_cli(
                    dir,
                    *bin,
                    &ordered(&format!("{copy}_{linker}_nohdr"), &order, &[nohdr]),
                    "[TCG-LINK-EH-FRAME-UNPROVEN]",
                    &[why.as_str()],
                );
                installed_by_cli(
                    dir,
                    *bin,
                    &ordered(&format!("{copy}_{linker}"), &order, &[]),
                );
            }
        }
        // GNU ld outside the driver: the copy registers from its own input,
        // after trust-cg's FDE, and the program does not backtrace into
        // `main`.
        let mut raw_copy: Vec<String> = [
            "-static",
            "-nostdlib",
            "-o",
            "raw_copy",
            "b1_scalars.o",
            "through.o",
            "cbt_copy.o",
        ]
        .iter()
        .map(|arg| arg.to_string())
        .collect();
        raw_copy.extend([
            crt1.clone(),
            crti.clone(),
            "bt.o".into(),
            "-Wl,--start-group,-lgcc,-lgcc_eh,-lc,--end-group".into(),
            file("crtend.o"),
            file("crtn.o"),
            nohdr.into(),
            "-Wl,-z,noexecstack".into(),
        ]);
        run_tool(
            dir,
            "cc",
            &raw_copy.iter().map(String::as_str).collect::<Vec<_>>(),
        );
        let (code, stdout) = run_program(&dir.join("raw_copy"));
        eprintln!("raw_copy, linked by GNU ld without the driver: exit {code:?}, {stdout}");
        assert!(stdout.matches("pc=").count() < 3, "{code:?} {stdout}");
        if let Some(lld) = lld.as_deref() {
            // LLD merges `crtbeginT.o`'s CIE into `crt1.o`'s equal one before
            // it, and `__EH_FRAME_BEGIN__` resolves to the start of its
            // synthetic `.eh_frame`: without a table the walk from there
            // reaches every FDE, in the standard order, with `bt.o` before
            // `crtbeginT.o`, and with `--gc-sections`.
            let standard = [crt1.as_str(), crti.as_str(), crtbegint.as_str(), "bt.o"];
            let bt_first = [crt1.as_str(), crti.as_str(), "bt.o", crtbegint.as_str()];
            for (output, order, extra) in [
                ("standard_lld_nohdr", &standard, &[nohdr][..]),
                ("bt_first_lld_nohdr", &bt_first, &[nohdr][..]),
                (
                    "standard_lld_gc_nohdr",
                    &standard,
                    &[nohdr, "-Wl,--gc-sections"][..],
                ),
            ] {
                installed_by_cli(dir, Some(lld), &ordered(output, order, extra));
            }
            // A script command in the `.eh_frame` output section keeps LLD's
            // map from placing its synthetic section: without a table the
            // image is refused, and the table twin links and runs.
            fs::write(dir.join("sym.ld"), SYMBOL_IN_EH_FRAME).unwrap();
            fs::write(dir.join("zero38.ld"), SKIP_IN_EH_FRAME).unwrap();
            let first_cie = [crtbegint.as_str(), crt1.as_str(), crti.as_str(), "bt.o"];
            for script in ["sym.ld", "zero38.ld"] {
                let t = format!("-Wl,-T,{script}");
                for order in [&first_cie, &standard] {
                    refused_by_cli(
                        dir,
                        Some(lld),
                        &ordered(&format!("{script}_lld_nohdr"), order, &[t.as_str(), nohdr]),
                        "[TCG-LINK-EH-FRAME-UNPROVEN]",
                        &[scripted],
                    );
                }
            }
            refused_by_cli(
                dir,
                Some(lld),
                &ordered("sym_lld", &first_cie, &["-Wl,-T,sym.ld"]),
                IRELATIVE,
                &[script_start_up],
            );
            // LLD outside the driver: the `sym.ld` program without a table
            // registers from `crtbeginT.o`'s own CIE, after trust-cg's FDE,
            // and does not backtrace into `main`.
            let mut raw_sym: Vec<String> = [
                "-static",
                "-nostdlib",
                "-o",
                "raw_sym",
                "b1_scalars.o",
                "through.o",
            ]
            .iter()
            .map(|arg| arg.to_string())
            .collect();
            raw_sym.extend([
                crtbegint.clone(),
                crt1.clone(),
                crti.clone(),
                "bt.o".into(),
                "-Wl,--start-group,-lgcc,-lgcc_eh,-lc,--end-group".into(),
                file("crtend.o"),
                file("crtn.o"),
                "-Wl,-T,sym.ld".into(),
                nohdr.into(),
                "-Wl,-z,noexecstack".into(),
            ]);
            run_tool(
                dir,
                &lld.join("cc").display().to_string(),
                &raw_sym.iter().map(String::as_str).collect::<Vec<_>>(),
            );
            let (code, stdout) = run_program(&dir.join("raw_sym"));
            eprintln!("raw_sym, linked by LLD without the driver: exit {code:?}, {stdout}");
            assert!(stdout.matches("pc=").count() < 3, "{code:?} {stdout}");
        }
    }

    /// A symbol assignment inside the `.eh_frame` output section, inserted
    /// after `.rodata` (the v4 verifier's `sym.ld`).
    const SYMBOL_IN_EH_FRAME: &str =
        "SECTIONS { .eh_frame : { __eh_start = .; KEEP(*(.eh_frame)) } } INSERT AFTER .rodata;\n";

    /// 0x38 bytes skipped at the start of the `.eh_frame` output section
    /// (the v4 verifier's `zero38.ld`).
    const SKIP_IN_EH_FRAME: &str =
        "SECTIONS { .eh_frame : { . += 0x38; *(.eh_frame) } } INSERT AFTER .rodata;\n";

    /// [`BT_SOURCE`] with the frames recorded by libgcc's `_Unwind_Backtrace`,
    /// which a `-Wl,-Bdynamic` static link takes from `libgcc_eh.a` into the
    /// image: that copy searches the frames `crtbeginT.o` registered, while
    /// glibc's `backtrace()` loads `libgcc_s.so.1`, which does not.
    const UNWIND_BT_SOURCE: &str = "#include <unwind.h>\n#include <stdio.h>\nextern long \
        isize_add_one(long);\nextern int tcg_bt_through(void);\nstatic void *frames[64];\nstatic \
        int count;\nstatic _Unwind_Reason_Code step(struct _Unwind_Context *ctx, void *arg) {\n  \
        (void)arg;\n  if (count < 64 && _Unwind_GetIP(ctx)) frames[count++] = (void \
        *)_Unwind_GetIP(ctx);\n  return \
        _URC_NO_REASON;\n}\n__attribute__((noinline)) int bt_depth(void) { count = 0; \
        _Unwind_Backtrace(step, 0); return count; }\nint main(void) {\n  long v = \
        isize_add_one(41);\n  tcg_bt_through();\n  printf(\"v=%ld main_at=%p\\n\", v, (void \
        *)main);\n  for (int i = 0; i < count; i++) printf(\"pc=%p\\n\", frames[i]);\n  return v \
        == 42 ? 0 : 1;\n}\n";

    /// The verifier's finding on `84ceb2eb7`: `--static` loads `crtbeginT.o`,
    /// whose `frame_dummy` registers its frames with libgcc, and a later
    /// `-Wl,-Bdynamic` (with LLD also `--dynamic-linker`) links libc
    /// dynamically, so the image is an `ET_EXEC` with a `PT_INTERP`. Only a
    /// static executable (no `PT_INTERP`) needed a readable link map, so
    /// through LLD route A (`.eh_frame` merged into `.rodata` at `0x10000000`,
    /// `.text` at `0xd0000000`, pieces LLD's map cannot place) and route B
    /// (the renamed `.ehx`, with `-Wl,-Map=/dev/null`, no readable map) were
    /// installed with every registered FDE truncated, and aborted in
    /// `_Unwind_Backtrace`. Such a link breaks the `--static` promise, and
    /// every one is now refused as `[TCG-LINK-STATIC-DYNAMIC]` with nothing
    /// written, through each linker, near twins included (they ran before).
    /// The image is still read through the driver's map: route A adds
    /// `[TCG-LINK-EH-FRAME-UNPROVEN]` (LLD's map cannot place the pieces, far
    /// and near), and far route B, with and without `-Wl,-Map=/dev/null`,
    /// `[TCG-LINK-EH-FRAME-WINDOW]`. GNU ld's `-Wl,--M=<file>` user map is
    /// written from the driver's although the image is refused. LLD's own
    /// route A program, which records its frames with [`UNWIND_BT_SOURCE`],
    /// dies in its backtrace. Without LLD or gold their legs are skipped
    /// (`SKIP:`).
    #[test]
    fn a_static_link_with_an_interpreter_is_refused_and_its_frames_read() {
        const DYNAMIC_LINKER: &str = "-Wl,--dynamic-linker=/lib/ld-linux-aarch64.so.1";
        let directory = tempfile::tempdir().unwrap();
        let dir = directory.path();
        copy_b1(dir);
        write_module(dir, "through.tmbc", &through_module());
        fs::write(dir.join("bt.c"), UNWIND_BT_SOURCE).unwrap();
        run_tool(dir, "cc", &["-c", "-O1", "-o", "bt.o", "bt.c"]);
        fs::write(dir.join("renamed.ld"), RENAMED_EH_FRAME).unwrap();
        fs::write(dir.join("merged.ld"), MERGED_EH_FRAME).unwrap();
        let lld = lld_dir().map(|lld| lld_cc(dir, &lld));
        let gold = gold_cc(dir);
        let args = |output: &str, extra: &[&str]| -> Vec<String> {
            [
                "--static",
                "--no-pie",
                "-o",
                output,
                "b1_scalars.tmbc",
                "through.tmbc",
                "-Wl,bt.o",
                "-Wl,-Bdynamic",
            ]
            .iter()
            .chain(extra)
            .map(|arg| arg.to_string())
            .collect()
        };
        // Refused with nothing written: every `error[link:` line holds one of
        // `tags`, and each tag is on one.
        let refused = |bin: Option<&Path>, args: &[String], output: &str, tags: &[&str]| {
            let mut before = listing(dir);
            before.retain(|name| !name.starts_with("user"));
            let result = trust_cg_on(
                bin,
                dir,
                &args.iter().map(String::as_str).collect::<Vec<_>>(),
            );
            let text = stderr(&result);
            assert!(!result.status.success(), "{output}: {text}");
            let lines: Vec<&str> = text.lines().filter(|l| l.contains("error[link:")).collect();
            assert!(
                lines
                    .iter()
                    .all(|line| tags.iter().any(|tag| line.contains(tag)))
                    && tags
                        .iter()
                        .all(|tag| lines.iter().any(|line| line.contains(tag))),
                "{output}: {text}"
            );
            let mut after = listing(dir);
            after.retain(|name| !name.starts_with("user"));
            assert_eq!(after, before, "{output}");
            assert!(!dir.join(output).exists(), "{output}");
        };
        const STATIC: &str = "[TCG-LINK-STATIC-DYNAMIC] ";
        const UNPROVEN: &str = "[TCG-LINK-EH-FRAME-UNPROVEN] ";
        const WINDOW: &str = "[TCG-LINK-EH-FRAME-WINDOW] ";
        let devnull = "-Wl,-Map=/dev/null";

        if let Some(bin) = lld.as_deref() {
            let route_a = |text: &str| {
                vec![
                    DYNAMIC_LINKER.to_string(),
                    "-Wl,-T,merged.ld".into(),
                    "-Wl,--no-eh-frame-hdr".into(),
                    format!("-Wl,--section-start=.rodata=0x10000000,--section-start=.text={text}"),
                ]
            };
            let route_b = |text: &str| {
                vec![
                    DYNAMIC_LINKER.to_string(),
                    "-Wl,-T,renamed.ld".into(),
                    "-Wl,--no-eh-frame-hdr".into(),
                    format!("-Wl,--section-start=.ehx=0x10000000,--section-start=.text={text}"),
                ]
            };
            let with = |mut extra: Vec<String>, more: &str| {
                extra.push(more.to_string());
                extra
            };
            fn refs(extra: &[String]) -> Vec<&str> {
                extra.iter().map(String::as_str).collect()
            }
            let far_a = route_a("0xd0000000");
            for (output, extra, tags) in [
                ("route_a", far_a.clone(), &[STATIC, UNPROVEN][..]),
                ("near_a_lld", route_a("0x20000000"), &[STATIC, UNPROVEN][..]),
                (
                    "route_b_devnull",
                    with(route_b("0xd0000000"), devnull),
                    &[STATIC, WINDOW][..],
                ),
                ("route_b", route_b("0xd0000000"), &[STATIC, WINDOW][..]),
                ("near_b_lld", route_b("0x20000000"), &[STATIC][..]),
                (
                    "near_b_devnull",
                    with(route_b("0x20000000"), devnull),
                    &[STATIC][..],
                ),
            ] {
                refused(Some(bin), &args(output, &refs(&extra)), output, tags);
            }
            // LLD outside the driver installs route A, and its program does
            // not backtrace into `main`.
            for module in ["b1_scalars", "through"] {
                let output = trust_cg_on(
                    None,
                    dir,
                    &[
                        "-c",
                        "-o",
                        &format!("{module}.o"),
                        &format!("{module}.tmbc"),
                    ],
                );
                assert!(output.status.success(), "{}", stderr(&output));
            }
            let mut raw = vec![
                "-static",
                "-no-pie",
                "-o",
                "raw_a",
                "b1_scalars.o",
                "through.o",
                "bt.o",
                "-Wl,-z,noexecstack",
                "-Wl,-Bdynamic",
            ];
            raw.extend(refs(&far_a));
            run_tool(dir, &bin.join("cc").display().to_string(), &raw);
            let (code, stdout) = run_program(&dir.join("raw_a"));
            eprintln!("raw_a, linked by LLD without the driver: exit {code:?}, {stdout}");
            // It dies in its backtrace, before printing anything.
            assert_eq!((code, stdout.as_str()), (None, ""));
        }

        // GNU ld: the renamed and merged near layouts, one with GNU ld's
        // `--M=<file>` spelling of `-Map` (written from the driver's map
        // although the image is refused), and one with `-Map=/dev/null`.
        for (output, extra) in [
            ("near_gnu", &["-Wl,-T,renamed.ld"][..]),
            (
                "near_gnu_merged",
                &["-Wl,-T,merged.ld", "-Wl,--no-eh-frame-hdr"][..],
            ),
            (
                "near_gnu_user",
                &[
                    "-Wl,-T,renamed.ld",
                    "-Wl,--no-eh-frame-hdr",
                    "-Wl,--M=user_gnu.map",
                ][..],
            ),
            ("near_gnu_devnull", &["-Wl,-T,renamed.ld", devnull][..]),
        ] {
            refused(None, &args(output, extra), output, &[STATIC]);
        }
        assert!(
            fs::read_to_string(dir.join("user_gnu.map"))
                .unwrap()
                .contains("Linker script and memory map")
        );

        // gold keeps `.eh_frame` named, and names its own interpreter.
        if let Some(bin) = gold.as_deref() {
            for (output, extra) in [
                ("near_gold", &[DYNAMIC_LINKER][..]),
                ("near_gold_devnull", &[DYNAMIC_LINKER, devnull][..]),
            ] {
                refused(Some(bin), &args(output, extra), output, &[STATIC]);
            }
        }
    }

    /// A library constructor that registers the main program's `.eh_frame`
    /// with libgcc (located through its `PT_GNU_EH_FRAME` header's
    /// `eh_frame_ptr`, `DW_EH_PE_pcrel|sdata4`), as the round-3 verifier's
    /// `regmain.c` does, and says so on standard error.
    const REGISTERING_LIBRARY_SOURCE: &str = "#define _GNU_SOURCE\n#include <link.h>\n#include \
        <stdint.h>\n#include <unistd.h>\nextern void __register_frame_info(const void *, void \
        *);\nstatic char object[64];\nstatic int first(struct dl_phdr_info *info, size_t size, \
        void *data) {\n  (void)size;\n  for (int i = 0; i < info->dlpi_phnum; i++)\n    if \
        (info->dlpi_phdr[i].p_type == PT_GNU_EH_FRAME) {\n      const unsigned char *header = \
        (const unsigned char *)(info->dlpi_addr + info->dlpi_phdr[i].p_vaddr);\n      if \
        (header[1] == 0x1b)\n        *(const void **)data = header + 4 + *(const int32_t \
        *)(header + 4);\n    }\n  return 1;\n}\n__attribute__((constructor)) static void \
        reg(void) {\n  const void *frames = 0;\n  dl_iterate_phdr(first, &frames);\n  if \
        (frames) {\n    __register_frame_info(frames, object);\n    static const char said[] = \
        \"tcg-reg: registered the main program's .eh_frame\\n\";\n    write(2, said, sizeof said \
        - 1);\n  }\n}\n";

    /// The round-2 verifier's finding on `824fb7980`: the input trace was read
    /// only for AArch64 ELF relocatable objects, so a shared object whose
    /// constructor calls `__register_frame_info`, linked into a dynamic
    /// executable with `-Wl,-Map=/dev/null`, was taken to register nothing
    /// and the image was installed. The driver now reads its own map whatever
    /// map the `-Wl` groups ask for, and does not read whether any input
    /// registers frames. Through GNU ld, with `--no-as-needed` so that each
    /// library named is a `DT_NEEDED` of the output and is loaded, each link
    /// is checked through the driver's map and installed, with and without
    /// `-Wl,-Map=/dev/null`, and backtraces into `main`:
    /// - `libreg.so`, whose constructor registers the main program's
    ///   `.eh_frame` ([`REGISTERING_LIBRARY_SOURCE`]): the output names it in
    ///   `DT_NEEDED`, and at run time the constructor registers the frames;
    /// - a library that imports none (`libplain.so`);
    /// - `libreg.so` under the `--as-needed` that Ubuntu's GCC passes, which
    ///   leaves it out of `DT_NEEDED`: the refusal the registration reading
    ///   made of it without a readable map is gone.
    ///
    /// A GCC `-flto` object ([`BT_SOURCE`] compiled with `-flto`) is no
    /// longer refused by the `.eh_frame` check for its LTO IR, and since the
    /// tenth closure audit no longer by `[TCG-LINK-INPUT-TRACE]` either: the
    /// trace named the objects GCC's LTO plugin compiled the IR into, which
    /// it deleted after the link, and the driver now links such a link
    /// again with the plugin keeping them in the stage
    /// (`-Wl,-plugin-opt=-save-temps`, `TMPDIR` in the stage). It is
    /// installed, backtraces into `main`, and leaves no LTO object in the
    /// output's directory.
    #[test]
    fn registering_libraries_and_lto_inputs_link_through_the_drivers_map() {
        const REGISTERED: &str = "tcg-reg: registered the main program's .eh_frame";
        let directory = tempfile::tempdir().unwrap();
        let dir = directory.path();
        copy_b1(dir);
        write_module(dir, "through.tmbc", &through_module());
        fs::write(dir.join("bt.c"), BT_SOURCE).unwrap();
        run_tool(dir, "cc", &["-c", "-O1", "-o", "bt.o", "bt.c"]);
        fs::write(dir.join("reg.c"), REGISTERING_LIBRARY_SOURCE).unwrap();
        fs::write(dir.join("plain.c"), "int tcg_plain(void) { return 1; }\n").unwrap();
        run_tool(dir, "cc", &["-shared", "-fPIC", "-o", "libreg.so", "reg.c"]);
        run_tool(
            dir,
            "cc",
            &["-shared", "-fPIC", "-o", "libplain.so", "plain.c"],
        );
        run_tool(dir, "cc", &["-c", "-O1", "-flto", "-o", "bt_lto.o", "bt.c"]);
        let rpath = dir.display().to_string();
        let args = |output: &str, group: &str, map: bool| {
            let mut args = vec![
                "-o".to_string(),
                output.to_string(),
                "--rpath".into(),
                rpath.clone(),
                "b1_scalars.tmbc".into(),
                "through.tmbc".into(),
                group.to_string(),
            ];
            if !map {
                args.push("-Wl,-Map=/dev/null".into());
            }
            args
        };
        // Installed: the libraries the output needs, whether its constructor
        // registered the frames, and that `backtrace()` returns into `main`.
        let installed = |output: &str, group: &str, map: bool| {
            let result = trust_cg_on(
                None,
                dir,
                &args(output, group, map)
                    .iter()
                    .map(String::as_str)
                    .collect::<Vec<_>>(),
            );
            assert!(result.status.success(), "{output}: {}", stderr(&result));
            let program = dir.join(output);
            let dynamic = Command::new("readelf")
                .arg("-d")
                .arg(&program)
                .output()
                .unwrap();
            assert!(dynamic.status.success(), "{output}: {dynamic:?}");
            let needed: Vec<String> = String::from_utf8_lossy(&dynamic.stdout)
                .lines()
                .filter_map(|line| {
                    let (_, rest) = line.split_once("Shared library: [")?;
                    Some(rest.trim_end_matches(']').to_string())
                })
                .collect();
            let run = Command::new(&program).output().unwrap();
            assert!(run.status.success(), "{output}: {run:?}");
            let registered = stderr(&run).lines().any(|line| line == REGISTERED);
            let frames = backtrace_of(&program);
            assert!(
                frames.len() >= 4 && frames[..3] == ["bt_depth", "tcg_bt_through", "main"],
                "{output}: {frames:?}"
            );
            fs::remove_file(&program).unwrap();
            (needed, registered)
        };
        for map in [false, true] {
            let (needed, registered) = installed("reg", "-Wl,--no-as-needed,bt.o,libreg.so", map);
            assert!(needed.iter().any(|name| name == "libreg.so"), "{needed:?}");
            assert!(
                registered,
                "reg (map {map}): the constructor did not register"
            );
            let (needed, registered) =
                installed("plain", "-Wl,--no-as-needed,bt.o,libplain.so", map);
            assert!(
                needed.iter().any(|name| name == "libplain.so"),
                "{needed:?}"
            );
            assert!(!registered);
            let (_, registered) = installed("lto", "-Wl,bt_lto.o", map);
            assert!(!registered);
            assert!(
                !fs::read_dir(dir).unwrap().any(|entry| entry
                    .unwrap()
                    .file_name()
                    .to_string_lossy()
                    .contains("ltrans")),
                "lto (map {map}): an LTO object was left in the output's directory"
            );
            let (needed, registered) = installed("reg_as_needed", "-Wl,bt.o,libreg.so", map);
            assert!(!needed.iter().any(|name| name == "libreg.so"), "{needed:?}");
            assert!(!registered, "reg_as_needed: libreg.so was loaded");
        }
    }

    /// A constructor that registers the renamed `.eh_frame` its program's
    /// script names (`tcg_ehx_start`) with libgcc through `REG`, and says so
    /// on standard error. The variants spell `REG` as the audit's did: a
    /// versioned reference (`SYMVER`), a `--wrap` alias, or a symbol a
    /// `--defsym` or a script's `PROVIDE` binds to the function.
    const SPELLED_REGISTRATION_SOURCE: &str = "#include <stdio.h>\nextern void REG(const void *, \
        void *);\nSYMVER\nextern char tcg_ehx_start[];\nstatic char object[256];\n\
        __attribute__((constructor)) static void reg(void) {\n  REG(tcg_ehx_start, object);\n  \
        fprintf(stderr, \"tcg-reg: registered\\n\");\n}\n";

    /// A library constructor that registers `tcg_ehx_start` through
    /// `__register_frame_info` (so it imports the function), as the ninth
    /// audit's `regd.c` does.
    const NEEDED_REGISTRATION_SOURCE: &str = "#include <stdio.h>\nextern void \
        __register_frame_info(const void *, void *);\nextern char tcg_ehx_start[];\nstatic char \
        object[256];\n__attribute__((constructor)) static void reg(void) {\n  \
        __register_frame_info(tcg_ehx_start, object);\n  fprintf(stderr, \"tcg-reg: \
        registered\\n\");\n}\n";

    /// A library constructor that finds `tcg_ehx_start` and
    /// `__register_frame_info` through `dlsym` (so it imports neither), as
    /// the ninth audit's `regx.c` does.
    const DLSYM_REGISTRATION_SOURCE: &str = "#define _GNU_SOURCE\n#include <dlfcn.h>\n#include \
        <stdio.h>\nstatic char object[256];\n__attribute__((constructor)) static void reg(void) \
        {\n  void *start = dlsym(RTLD_DEFAULT, \"tcg_ehx_start\");\n  void (*r)(const void *, \
        void *) = (void (*)(const void *, void *))dlsym(RTLD_DEFAULT, \
        \"__register_frame_info\");\n  if (start && r) {\n    r(start, object);\n    \
        fprintf(stderr, \"tcg-reg: registered\\n\");\n  }\n}\n";

    /// Renames the output `.eh_frame` to `.ehx` and names its start
    /// `tcg_ehx_start` outside the section, which LLD's map places.
    const RENAMED_WITH_START: &str = "SECTIONS { .ehx : { KEEP(*(.eh_frame)) } } INSERT BEFORE \
                                      .text;\ntcg_ehx_start = ADDR(.ehx);\n";

    /// The same with `tcg_ehx_start` assigned inside the section: LLD's map
    /// then prints the assignment beside the pieces and cannot place them.
    const RENAMED_WITH_START_INSIDE: &str = "SECTIONS { .ehx : { tcg_ehx_start = .; \
                                             KEEP(*(.eh_frame)) } } INSERT BEFORE .text;\n";

    /// The same assignment in an output section still named `.eh_frame`.
    const NAMED_WITH_START_INSIDE: &str = "SECTIONS { .eh_frame : { tcg_ehx_start = .; \
                                           KEEP(*(.eh_frame)) } } INSERT BEFORE .text;\n";

    /// `.ehx` (the renamed `.eh_frame`) at 256 MiB and `.text` 3 GiB above
    /// it: each `pc_begin` is a `PREL32` of `2^31 <= X < 2^32`, which LLD
    /// 22.1.6 writes and every unwinder reads as negative.
    const FAR_EHX: &str = "-Wl,--section-start=.ehx=0x10000000,--section-start=.text=0xd0000000";

    /// libgcc's unwinder linked from `libgcc_eh.a` into a dynamic program,
    /// so an alias of a registration function binds to the image's own
    /// definition, and the image imports none.
    const STATIC_UNWINDER: &str = "-Wl,-Bstatic,-lgcc_eh,-Bdynamic";

    /// The code of the refusal of a static executable whose IFUNC
    /// relocations glibc's own start-up code is not shown to apply.
    const IRELATIVE: &str = "[TCG-LINK-IRELATIVE-UNAPPLIED]";

    /// Link with the CLI in `dir` with `bin` first on `PATH` and require a
    /// refusal with nothing written: every `error[link:` line holds `tag`,
    /// and each of `texts` is in one of them. A static glibc image that is
    /// also refused as [`IRELATIVE`] (a script or `-z muldefs`, or an
    /// `IRELATIVE` bracket that holds other relocations) may add that line.
    fn refused_by_cli(dir: &Path, bin: Option<&Path>, args: &[String], tag: &str, texts: &[&str]) {
        let output = &args[args.iter().position(|arg| arg == "-o").unwrap() + 1];
        let before = listing(dir);
        let result = trust_cg_on(
            bin,
            dir,
            &args.iter().map(String::as_str).collect::<Vec<_>>(),
        );
        let text = stderr(&result);
        assert!(!result.status.success(), "{output}: {text}");
        let lines: Vec<&str> = text
            .lines()
            .filter(|line| {
                line.contains("error[link:") && (tag == IRELATIVE || !line.contains(IRELATIVE))
            })
            .collect();
        assert!(
            !lines.is_empty()
                && lines.iter().all(|line| line.contains(tag))
                && texts
                    .iter()
                    .all(|wanted| lines.iter().any(|line| line.contains(wanted))),
            "{output}: {text}"
        );
        assert_eq!(listing(dir), before, "{output}");
        assert!(!dir.join(output).exists(), "{output}");
    }

    /// Link with the CLI in `dir` with `bin` first on `PATH`, run the program
    /// (a [`UNWIND_BT_SOURCE`] or [`BT_SOURCE`] one), and require that it
    /// backtraces through the trust-cg frame into `main`; whether it printed
    /// `tcg-reg: registered` on standard error. The program is removed.
    fn installed_by_cli(dir: &Path, bin: Option<&Path>, args: &[String]) -> bool {
        let output = &args[args.iter().position(|arg| arg == "-o").unwrap() + 1];
        let result = trust_cg_on(
            bin,
            dir,
            &args.iter().map(String::as_str).collect::<Vec<_>>(),
        );
        assert!(result.status.success(), "{output}: {}", stderr(&result));
        let program = dir.join(output);
        let run = Command::new(&program)
            .env("LD_LIBRARY_PATH", dir)
            .output()
            .unwrap();
        assert!(run.status.success(), "{output}: {run:?}");
        let registered = stderr(&run)
            .lines()
            .any(|line| line == "tcg-reg: registered");
        let frames = backtrace_of(&program);
        assert!(
            frames.len() >= 4 && frames[..3] == ["bt_depth", "tcg_bt_through", "main"],
            "{output}: {frames:?}"
        );
        fs::remove_file(&program).unwrap();
        registered
    }

    /// Compile the b1 and `through` modules to `b1_scalars.o` and
    /// `through.o` in `dir`, for links outside the driver.
    fn compile_bt_modules(dir: &Path) {
        for module in ["b1_scalars", "through"] {
            let output = trust_cg_on(
                None,
                dir,
                &[
                    "-c",
                    "-o",
                    &format!("{module}.o"),
                    &format!("{module}.tmbc"),
                ],
            );
            assert!(output.status.success(), "{}", stderr(&output));
        }
    }

    /// The ninth closure audit at `0996df987`: an input that registers the
    /// program's frames through a spelling other than the function's name
    /// was taken to register nothing. Through LLD, a `--no-pie` program whose
    /// script renames `.eh_frame` to `.ehx` at 256 MiB, with `.text` at
    /// `0xd0000000` and `-Wl,--no-eh-frame-hdr`, linked with an object that
    /// calls `__register_frame_info@GLIBC_2.0` (a `.symver`) or
    /// `__real___register_frame_info` (`--wrap`) and `-Wl,-Map=/dev/null`,
    /// was installed with every FDE truncated; its program registered them
    /// and backtraced one frame. The driver now reads its own map whatever
    /// map the `-Wl` groups ask for, so each spelling (the versioned
    /// reference, the `--wrap` alias through `libgcc_s.so.1` and, with
    /// libgcc's unwinder linked from `libgcc_eh.a`, the `--wrap` alias, a
    /// `--defsym` alias and a script operand's `PROVIDE`) is refused as a
    /// window, its truncated FDEs decoded, with and without
    /// `-Wl,-Map=/dev/null`, with nothing written. Each near layout links,
    /// registers its frames at run time and backtraces through the trust-cg
    /// frame into `main`, with and without `-Wl,-Map=/dev/null`. LLD's own
    /// versioned program registers the truncated frames and does not
    /// backtrace into `main`. Without LLD the row is skipped (`SKIP:`).
    #[test]
    fn a_registration_spelled_otherwise_than_the_function_is_checked_through_the_drivers_map() {
        let directory = tempfile::tempdir().unwrap();
        let dir = directory.path();
        let Some(lld) = lld_dir().map(|lld| lld_cc(dir, &lld)) else {
            return;
        };
        copy_b1(dir);
        write_module(dir, "through.tmbc", &through_module());
        fs::write(dir.join("bt.c"), UNWIND_BT_SOURCE).unwrap();
        run_tool(dir, "cc", &["-c", "-O1", "-o", "bt.o", "bt.c"]);
        for (name, spelled, symver) in [
            (
                "vreg",
                "reg_v",
                "__asm__(\".symver reg_v, __register_frame_info@GLIBC_2.0\");",
            ),
            ("wreg", "__real___register_frame_info", ""),
            ("areg", "myreg", ""),
        ] {
            fs::write(
                dir.join(format!("{name}.c")),
                SPELLED_REGISTRATION_SOURCE
                    .replace("REG", spelled)
                    .replace("SYMVER", symver),
            )
            .unwrap();
            run_tool(
                dir,
                "cc",
                &[
                    "-c",
                    "-O1",
                    "-o",
                    &format!("{name}.o"),
                    &format!("{name}.c"),
                ],
            );
        }
        fs::write(dir.join("start.ld"), RENAMED_WITH_START).unwrap();
        fs::write(
            dir.join("prov.ld"),
            "PROVIDE(myreg = __register_frame_info);\n",
        )
        .unwrap();
        let args = |output: &str, extra: &[&str]| -> Vec<String> {
            [
                "--no-pie",
                "-o",
                output,
                "b1_scalars.tmbc",
                "through.tmbc",
                "-Wl,bt.o",
                "-Wl,-T,start.ld",
                "-Wl,--no-eh-frame-hdr",
            ]
            .iter()
            .chain(extra)
            .map(|arg| arg.to_string())
            .collect()
        };
        let devnull = "-Wl,-Map=/dev/null";
        let routes: [(&str, Vec<&'static str>); 5] = [
            ("versioned", vec!["-Wl,vreg.o"]),
            ("wrapped", vec!["-Wl,wreg.o,--wrap=__register_frame_info"]),
            (
                "wrapped_static",
                vec!["-Wl,wreg.o,--wrap=__register_frame_info", STATIC_UNWINDER],
            ),
            (
                "defsym_static",
                vec![
                    "-Wl,areg.o,--defsym=myreg=__register_frame_info",
                    STATIC_UNWINDER,
                ],
            ),
            (
                "provide_static",
                vec!["-Wl,areg.o,prov.ld", STATIC_UNWINDER],
            ),
        ];
        for (name, inputs) in &routes {
            let with = |more: &[&'static str]| -> Vec<&'static str> {
                inputs.iter().copied().chain(more.iter().copied()).collect()
            };
            // The far layout's pieces are decoded and refused, and the near
            // one registers and backtraces into `main`, whatever the user's
            // map.
            for (suffix, map) in [("", &[][..]), ("_devnull", &[devnull][..])] {
                let mut far = with(map);
                far.push(FAR_EHX);
                refused_by_cli(
                    dir,
                    Some(&lld),
                    &args(&format!("{name}_far{suffix}"), &far),
                    "[TCG-LINK-EH-FRAME-WINDOW]",
                    &[" FDEs describe code outside executable memory"],
                );
                assert!(
                    installed_by_cli(
                        dir,
                        Some(&lld),
                        &args(&format!("{name}_near{suffix}"), &with(map))
                    ),
                    "{name}{suffix}: the near program did not register its frames"
                );
            }
        }
        // LLD outside the driver: the versioned program registers the
        // truncated frames and does not backtrace into `main`.
        compile_bt_modules(dir);
        let (far_ehx, far_text) = (
            "-Wl,--section-start=.ehx=0x10000000",
            "-Wl,--section-start=.text=0xd0000000",
        );
        run_tool(
            dir,
            &lld.join("cc").display().to_string(),
            &[
                "-no-pie",
                "-o",
                "raw_versioned",
                "b1_scalars.o",
                "through.o",
                "bt.o",
                "vreg.o",
                "-Wl,-T,start.ld",
                "-Wl,--no-eh-frame-hdr",
                far_ehx,
                far_text,
                "-Wl,-z,noexecstack",
            ],
        );
        let run = Command::new(dir.join("raw_versioned")).output().unwrap();
        let text = String::from_utf8_lossy(&run.stdout).into_owned();
        eprintln!(
            "raw_versioned, linked by LLD without the driver: {:?}, {text}",
            run.status
        );
        assert!(stderr(&run).contains("tcg-reg: registered"), "{run:?}");
        assert!(
            text.split_whitespace()
                .filter(|word| word.starts_with("pc="))
                .count()
                < 3,
            "{text}"
        );
    }

    /// `object` (an ELF64 relocatable object) with the section `name` given
    /// the type `kind`.
    fn with_section_type(object: &[u8], name: &str, kind: u32) -> Vec<u8> {
        let mut bytes = object.to_vec();
        let read = |bytes: &[u8], at: usize, width: usize| {
            let mut value = [0u8; 8];
            value[..width].copy_from_slice(&bytes[at..at + width]);
            u64::from_le_bytes(value) as usize
        };
        let (shoff, shentsize, shnum, shstrndx) = (
            read(&bytes, 0x28, 8),
            read(&bytes, 0x3a, 2),
            read(&bytes, 0x3c, 2),
            read(&bytes, 0x3e, 2),
        );
        let names = read(&bytes, shoff + shstrndx * shentsize + 0x18, 8);
        let mut found = false;
        for index in 0..shnum {
            let header = shoff + index * shentsize;
            let at = names + read(&bytes, header, 4);
            let end = at + bytes[at..].iter().position(|byte| *byte == 0).unwrap();
            if &bytes[at..end] == name.as_bytes() {
                bytes[header + 4..header + 8].copy_from_slice(&kind.to_le_bytes());
                found = true;
            }
        }
        assert!(found, "no section {name}");
        bytes
    }

    /// The verifiers of the ninth-audit repair found aliases of
    /// `__register_frame_info` in linker scripts LLD reads that the driver's
    /// script reading missed, and LLD programs whose renamed `.eh_frame`
    /// their constructor registered were installed with every FDE truncated
    /// (82 of 82) and aborted. Round 1: a `-Wl` script operand whose comment
    /// holds a control byte, and a `-T alias.ld` read from a `-L` directory
    /// after the `-L=<dir>` one LLD used (and `INPUT(alias.ld)` of a `-T`
    /// script, `-lalias` whose `libalias.so` is a script). Round 2: a
    /// `.deplibs` section naming the library, a script's `INPUT` found in the
    /// script's own directory, `-sysroot=` with one dash, `-L=<dir>` joined
    /// with a sysroot, a relative `=dA` under a sysroot, a `#` comment
    /// holding `/*`, a `/*` inside a quoted name, and `-T =<file>`. Modelling
    /// every linker's script search is an unbounded surface, and each route
    /// needed `-Wl,-Map=/dev/null` to keep the driver's map from it; the
    /// driver now always writes and reads its own map. Through LLD, with
    /// libgcc's unwinder linked from `libgcc_eh.a` (the image imports
    /// nothing), each route's far layout is refused as
    /// `[TCG-LINK-EH-FRAME-WINDOW]` with nothing written, with and without
    /// `-Wl,-Map=/dev/null`, and each near layout links, registers its frames
    /// through the script's alias and backtraces through the trust-cg frame
    /// into `main`. GNU ld 2.42 reads `-dT=`, `--dT=` and `--dT <file>`
    /// scripts too, and refuses each far placement itself. Its near layout
    /// (`.ehx` after `.rodata`) links, as GNU ld links it outside the driver,
    /// and its program registers `.ehx` from its start and aborts in
    /// `_Unwind_Backtrace`, inside and outside the driver alike: GNU ld keeps
    /// the zero padding between the `.eh_frame` inputs of an output section
    /// not named `.eh_frame`, libgcc's walk of the registered frames stops at
    /// the first zero word (after 4 records), and libgcc finds no FDE for its
    /// own frame. The truncation check reads a run past such padding; that
    /// the registered walk reaches every FDE is not checked (a documented
    /// boundary). LLD's own control-byte program registers its truncated
    /// frames and aborts. Without LLD the LLD rows are skipped (`SKIP:`).
    #[test]
    fn every_route_a_script_can_register_frames_by_is_checked_through_the_drivers_map() {
        let directory = tempfile::tempdir().unwrap();
        let dir = directory.path();
        copy_b1(dir);
        write_module(dir, "through.tmbc", &through_module());
        fs::write(dir.join("bt.c"), UNWIND_BT_SOURCE).unwrap();
        run_tool(dir, "cc", &["-c", "-O1", "-o", "bt.o", "bt.c"]);
        fs::write(
            dir.join("areg.c"),
            SPELLED_REGISTRATION_SOURCE
                .replace("REG", "myreg")
                .replace("SYMVER", ""),
        )
        .unwrap();
        run_tool(dir, "cc", &["-c", "-O1", "-o", "areg.o", "areg.c"]);
        fs::write(dir.join("start.ld"), RENAMED_WITH_START).unwrap();
        const PROVIDE: &str = "PROVIDE(myreg = __register_frame_info);\n";
        const DECOY: &str = "PROVIDE(tcg_unused_alias = 0);\n";
        for sub in ["dA", "dB", "dE", "sub", "S", "S/dA"] {
            fs::create_dir(dir.join(sub)).unwrap();
        }
        fs::write(
            dir.join("provc.ld"),
            b"/*\x01*/ PROVIDE(myreg = __register_frame_info);\n",
        )
        .unwrap();
        fs::write(dir.join("dA/alias.ld"), PROVIDE).unwrap();
        fs::write(dir.join("dB/alias.ld"), DECOY).unwrap();
        fs::write(dir.join("dA/libalias.so"), PROVIDE).unwrap();
        fs::write(dir.join("top.ld"), "INPUT(alias.ld)\n").unwrap();
        // Round 2.
        fs::write(
            dir.join("dep.s"),
            ".section .deplibs,\"MS\",@progbits,1\n.asciz \"alias\"\n",
        )
        .unwrap();
        run_tool(dir, "cc", &["-c", "-o", "dep0.o", "dep.s"]);
        // `SHT_LLVM_DEPENDENT_LIBRARIES`, which GNU as does not name.
        let dep = with_section_type(
            &fs::read(dir.join("dep0.o")).unwrap(),
            ".deplibs",
            0x6fff_4c04,
        );
        fs::write(dir.join("dep.o"), dep).unwrap();
        fs::write(dir.join("sub/top.ld"), "INPUT(salias.ld)\n").unwrap();
        fs::write(dir.join("sub/salias.ld"), PROVIDE).unwrap();
        fs::write(dir.join("salias.ld"), DECOY).unwrap();
        fs::write(dir.join("S/dA/ralias.ld"), PROVIDE).unwrap();
        fs::write(dir.join("dB/ralias.ld"), DECOY).unwrap();
        fs::write(dir.join("dE/=ealias.ld"), PROVIDE).unwrap();
        fs::write(dir.join("ealias.ld"), DECOY).unwrap();
        let (d_a, d_b, root) = (
            dir.join("dA").display().to_string(),
            dir.join("dB").display().to_string(),
            dir.join("S").display().to_string(),
        );
        fs::write(
            dir.join("hash.ld"),
            format!("# /*\nINCLUDE {d_a}/alias.ld\n/* */\n"),
        )
        .unwrap();
        fs::write(
            dir.join("str.ld"),
            format!("\"tcg_q1/*\" = 0;\nINCLUDE {d_a}/alias.ld\n\"tcg_q2*/\" = 0;\n"),
        )
        .unwrap();
        let args = |output: &str, extra: &[String]| -> Vec<String> {
            [
                "--no-pie",
                "-o",
                output,
                "b1_scalars.tmbc",
                "through.tmbc",
                "-Wl,bt.o,areg.o",
                "-Wl,-T,start.ld",
                "-Wl,--no-eh-frame-hdr",
                STATIC_UNWINDER,
            ]
            .iter()
            .map(|arg| arg.to_string())
            .chain(extra.iter().cloned())
            .collect()
        };
        let devnull = "-Wl,-Map=/dev/null";
        if let Some(lld) = lld_dir().map(|lld| lld_cc(dir, &lld)) {
            let routes: [(&str, String); 12] = [
                ("control_byte", "-Wl,provc.ld".to_string()),
                (
                    "equals_directory",
                    format!("-Wl,-L,={d_a},-L,{d_b},-T,alias.ld"),
                ),
                ("input", format!("-Wl,-L,{d_a},-T,top.ld")),
                ("library", format!("-Wl,-L,{d_a},-lalias")),
                ("deplibs", "-Wl,dep.o,-L,dA".to_string()),
                ("script_directory", "-Wl,-T,sub/top.ld".to_string()),
                (
                    "sysroot_one_dash",
                    format!("-Wl,-sysroot={root},-L,=/dA,-L,dB,-T,ralias.ld"),
                ),
                (
                    "joined_equals_directory",
                    format!("-Wl,--sysroot={root},-L=/dA,-L,dB,-T,ralias.ld"),
                ),
                (
                    "relative_equals_directory",
                    format!("-Wl,--sysroot={root},-L,=dA,-L,dB,-T,ralias.ld"),
                ),
                ("hash_comment", "-Wl,hash.ld".to_string()),
                ("quoted_comment_opener", "-Wl,str.ld".to_string()),
                ("equals_script", "-Wl,-L,dE,-T,=ealias.ld".to_string()),
            ];
            for (name, route) in &routes {
                for (suffix, map) in [("", None), ("_devnull", Some(devnull))] {
                    let with = |more: Option<&str>| -> Vec<String> {
                        std::iter::once(route.clone())
                            .chain(map.map(str::to_string))
                            .chain(more.map(str::to_string))
                            .collect()
                    };
                    refused_by_cli(
                        dir,
                        Some(&lld),
                        &args(&format!("{name}_far{suffix}"), &with(Some(FAR_EHX))),
                        "[TCG-LINK-EH-FRAME-WINDOW]",
                        &[" FDEs describe code outside executable memory"],
                    );
                    assert!(
                        installed_by_cli(
                            dir,
                            Some(&lld),
                            &args(&format!("{name}_near{suffix}"), &with(None))
                        ),
                        "{name}{suffix}: the near program did not register its frames"
                    );
                }
            }
            // LLD outside the driver: the control-byte program registers its
            // truncated frames and aborts.
            compile_bt_modules(dir);
            run_tool(
                dir,
                &lld.join("cc").display().to_string(),
                &[
                    "-no-pie",
                    "-o",
                    "raw_control_byte",
                    "b1_scalars.o",
                    "through.o",
                    "bt.o",
                    "areg.o",
                    "provc.ld",
                    "-Wl,-T,start.ld",
                    "-Wl,--no-eh-frame-hdr",
                    "-Wl,-Bstatic,-lgcc_eh,-Bdynamic",
                    "-Wl,--section-start=.ehx=0x10000000",
                    "-Wl,--section-start=.text=0xd0000000",
                    "-Wl,-z,noexecstack",
                ],
            );
            let run = Command::new(dir.join("raw_control_byte")).output().unwrap();
            let text = String::from_utf8_lossy(&run.stdout).into_owned();
            eprintln!(
                "raw_control_byte, linked by LLD without the driver: {:?}, {text}",
                run.status
            );
            assert!(stderr(&run).contains("tcg-reg: registered"), "{run:?}");
            assert!(!run.status.success(), "{run:?}");
        }
        // GNU ld's `-dT` spellings of a script that renames `.eh_frame` and
        // aliases the registration function.
        fs::write(
            dir.join("dA/galias.ld"),
            format!(
                "SECTIONS {{ .ehx : {{ KEEP(*(.eh_frame)) }} }} INSERT AFTER .rodata;\n\
                 tcg_ehx_start = ADDR(.ehx);\n{PROVIDE}"
            ),
        )
        .unwrap();
        let gnu_args = |output: &str, route: &str, more: &[&str]| -> Vec<String> {
            [
                "--no-pie",
                "-o",
                output,
                "b1_scalars.tmbc",
                "through.tmbc",
                "-Wl,bt.o,areg.o",
                "-Wl,--no-eh-frame-hdr",
                STATIC_UNWINDER,
                route,
            ]
            .iter()
            .chain(more)
            .map(|arg| arg.to_string())
            .collect()
        };
        let aborts_registered = |program: &Path| {
            let run = Command::new(program).output().unwrap();
            assert!(
                run.status.signal() == Some(SIGABRT)
                    && stderr(&run).contains("tcg-reg: registered"),
                "{}: {run:?}",
                program.display()
            );
        };
        // The one-dash `-dT=<file>` is a group of short options to gold
        // (`-d -T=<file>`), refused before any process runs.
        refused_with(
            dir,
            None,
            &gnu_args("gnu_dt_equals", "-Wl,-L,dA,-dT=galias.ld", &[devnull])
                .iter()
                .map(String::as_str)
                .collect::<Vec<_>>(),
            "[TCG-LINK-OPTION-GROUP]",
            &["-dT=galias.ld"],
        );
        for (name, route) in [
            ("gnu_dt_long_equals", "-Wl,-L,dA,--dT=galias.ld"),
            ("gnu_dt_long", "-Wl,-L,dA,--dT,galias.ld"),
        ] {
            let result = trust_cg_on(
                None,
                dir,
                &gnu_args(name, route, &[devnull])
                    .iter()
                    .map(String::as_str)
                    .collect::<Vec<_>>(),
            );
            assert!(result.status.success(), "{name}: {}", stderr(&result));
            aborts_registered(&dir.join(name));
            let far = format!("{name}_far");
            let result = trust_cg_on(
                None,
                dir,
                &gnu_args(
                    &far,
                    route,
                    &[
                        devnull,
                        "-Wl,--section-start=.ehx=0x10000000,--section-start=.text=0xd0000000",
                    ],
                )
                .iter()
                .map(String::as_str)
                .collect::<Vec<_>>(),
            );
            assert!(
                !result.status.success()
                    && stderr(&result).contains("relocation truncated to fit: R_AARCH64_PREL32"),
                "{far}: {}",
                stderr(&result)
            );
            assert!(!dir.join(&far).exists(), "{far}");
        }
        // GNU ld outside the driver: the same program aborts the same way.
        let raw_dir = dir.join("gnu_raw");
        fs::create_dir(&raw_dir).unwrap();
        for module in ["b1_scalars", "through"] {
            let object = raw_dir.join(format!("{module}.o"));
            let output = trust_cg_on(
                None,
                dir,
                &[
                    "-c",
                    "-o",
                    object.to_str().unwrap(),
                    &format!("{module}.tmbc"),
                ],
            );
            assert!(output.status.success(), "{}", stderr(&output));
        }
        run_tool(
            dir,
            "cc",
            &[
                "-no-pie",
                "-o",
                "gnu_raw/prog",
                "gnu_raw/b1_scalars.o",
                "gnu_raw/through.o",
                "bt.o",
                "areg.o",
                "-Wl,--no-eh-frame-hdr",
                STATIC_UNWINDER,
                "-Wl,-L,dA,-dT=galias.ld",
                "-Wl,-z,noexecstack",
            ],
        );
        aborts_registered(&raw_dir.join("prog"));
    }

    /// `main` prints what `isize_add_one(41)` (the b1 fixture) returns and
    /// exits 0 when it is 42.
    const STATIC_BDYNAMIC_MAIN: &str = "#include <stdio.h>\nextern long isize_add_one(long);\nint \
                                        main(void) { long v = isize_add_one(41); printf(\"v=%ld\\n\", \
                                        v); return v == 42 ? 0 : 1; }\n";

    /// A `-nostdlib` program's own `_start` (the v4 verifier's `start.c`):
    /// it calls `isize_add_one` through a function pointer in `.data` (an
    /// `R_AARCH64_RELATIVE` in a PIE) and exits 0 when it returns 42.
    const PIE_START_SOURCE: &str = "extern long isize_add_one(long);\nlong (*volatile fp)(long) = \
                                    isize_add_one;\nstatic void sys_exit(long code) {\n  register \
                                    long x0 __asm__(\"x0\") = code;\n  register long x8 \
                                    __asm__(\"x8\") = 93;\n  __asm__ volatile(\"svc 0\" : : \
                                    \"r\"(x0), \"r\"(x8) : \"memory\");\n  \
                                    __builtin_unreachable();\n}\nvoid _start(void) { \
                                    sys_exit(fp(41) == 42 ? 0 : 1); }\n";

    /// [`STATIC_BDYNAMIC_MAIN`] that also calls `libm`'s `sqrt`.
    const STATIC_LIBM_MAIN: &str = "#include <math.h>\n#include <stdio.h>\nextern long \
                                    isize_add_one(long);\nint main(int argc, char **argv) { \
                                    (void)argv; long v = isize_add_one(41); printf(\"v=%ld \
                                    %g\\n\", v, sqrt((double)argc + 3)); return v == 42 ? 0 : 1; \
                                    }\n";

    /// A `--static` link given `-Wl,-Bdynamic` links a shared library
    /// dynamically into a program whose start-up code is static glibc's.
    /// Through LLD 22.1.6 the image names no interpreter: with
    /// `-Wl,-Bstatic,-lgcc_eh,-Bdynamic` it needs `libc.so.6` (`DT_NEEDED`,
    /// the ninth audit's verifier), and with
    /// `-Wl,-Bdynamic,--as-needed,-lm,--no-as-needed,-Bstatic` and `libm`
    /// unused it holds a `DT_DEBUG` and relocations alone (its round-2
    /// verifier); both die with SIGSEGV and are refused as
    /// `[TCG-LINK-DYNAMIC-NO-INTERP]`, and so is a dynamic `--no-pie
    /// -Wl,--no-dynamic-linker` link through GNU ld and LLD (gold refuses the
    /// option). GNU ld 2.42 names its interpreter: its image of the `-lm`
    /// route for a program that calls `sqrt` ([`STATIC_LIBM_MAIN`]) needs
    /// `libm.so.6` and dies with SIGSEGV outside the driver, and gold 2.42
    /// names `/lib/ld.so.1`, which the host lacks. Every `--static` image that
    /// names an interpreter or needs a library is now refused as
    /// `[TCG-LINK-STATIC-DYNAMIC]`, through each linker, with nothing written:
    /// GNU ld's and gold's `-Bdynamic` images, each linker's image with
    /// `-Wl,--dynamic-linker=/lib/ld-linux-aarch64.so.1` (which ran before),
    /// gold's `--as-needed` image and GNU ld's and gold's `libm` images. A
    /// plain `--static` link, and GNU ld's `--as-needed` link that drops the
    /// unused `libm` (a static executable), run. The round-3 verifier's PIE:
    /// a default or `--pie` link given `-Wl,--no-dynamic-linker` gives GNU ld
    /// and LLD a PIE that needs `libc.so.6` and names no interpreter, and GNU
    /// ld's dies with SIGSEGV outside the driver; each is refused as
    /// `[TCG-LINK-DYNAMIC-NO-INTERP]`. The v4 verifier's PIE needs no library:
    /// `--pie --nostdlib -Wl,start.o,--no-dynamic-linker` ([`PIE_START_SOURCE`])
    /// holds an `R_AARCH64_RELATIVE` nothing applies, and dies with SIGSEGV
    /// outside the driver; it, and a PIE whose `crt1.o` defines a stub
    /// `_dl_relocate_static_pie`, are refused through GNU ld and LLD, while
    /// glibc's static PIE (`rcrt1.o` and `libc.a`) installs and runs. The
    /// promise refusal names the options in effect (`-Bdyn`, not a `-Bdynamic`
    /// a `-Bstatic` cancels, and not a `-Bdyn` a `--pop-state` cancels).
    /// Without LLD or gold their legs are skipped (`SKIP:`).
    #[test]
    fn a_static_link_that_is_not_static_is_refused() {
        const DYNAMIC_LINKER: &str = "-Wl,--dynamic-linker=/lib/ld-linux-aarch64.so.1";
        let directory = tempfile::tempdir().unwrap();
        let dir = directory.path();
        copy_b1(dir);
        fs::write(dir.join("main.c"), STATIC_BDYNAMIC_MAIN).unwrap();
        run_tool(dir, "cc", &["-c", "-O1", "-o", "main.o", "main.c"]);
        fs::write(dir.join("libm_main.c"), STATIC_LIBM_MAIN).unwrap();
        run_tool(
            dir,
            "cc",
            &["-c", "-O1", "-o", "libm_main.o", "libm_main.c"],
        );
        let lld = lld_dir().map(|lld| lld_cc(dir, &lld));
        let gold = gold_cc(dir);
        let interpreter = |program: &Path| {
            let output = Command::new("readelf")
                .args(["-lW"])
                .arg(program)
                .output()
                .unwrap();
            let text = String::from_utf8_lossy(&output.stdout).into_owned();
            text.lines()
                .find_map(|line| {
                    line.split_once("[Requesting program interpreter: ")
                        .map(|(_, rest)| rest.trim_end_matches(']').to_string())
                })
                .unwrap_or_default()
        };
        let args = |output: &str, main: &str, extra: &[&str]| -> Vec<String> {
            let main = format!("-Wl,{main}");
            ["--static", "-o", output, "b1_scalars.tmbc", main.as_str()]
                .iter()
                .chain(extra)
                .map(|arg| arg.to_string())
                .collect()
        };
        let runs = |bin: Option<&Path>, args: &[String], output: &str| {
            let result = trust_cg_on(
                bin,
                dir,
                &args.iter().map(String::as_str).collect::<Vec<_>>(),
            );
            assert!(result.status.success(), "{output}: {}", stderr(&result));
            let program = dir.join(output);
            assert_eq!(interpreter(&program), "", "{output}");
            let run = Command::new(&program).output().unwrap();
            assert!(
                run.status.success() && String::from_utf8_lossy(&run.stdout).contains("v=42"),
                "{output}: {run:?}"
            );
        };
        const STATIC: &str = "[TCG-LINK-STATIC-DYNAMIC]";
        const NO_INTERP: &str = "[TCG-LINK-DYNAMIC-NO-INTERP]";
        let interp_and_needed = "the image names a program interpreter (PT_INTERP) and names 1 \
                                 shared library (DT_NEEDED)";
        let interp_only = "the image names a program interpreter (PT_INTERP):";
        let mut linkers: Vec<(&str, Option<PathBuf>)> = vec![("gnu", None)];
        linkers.extend(gold.map(|gold| ("gold", Some(gold))));
        linkers.extend(lld.clone().map(|lld| ("lld", Some(lld))));
        let bdynamic = "-Wl,-Bstatic,-lgcc_eh,-Bdynamic";
        let as_needed = "-Wl,-Bdynamic,--as-needed,-lm,--no-as-needed,-Bstatic";
        for (linker, bin) in &linkers {
            let bin = bin.as_deref();
            let lld = *linker == "lld";
            // `-Bdynamic` for libc.
            let (tag, text) = if lld {
                (
                    NO_INTERP,
                    "an ET_EXEC whose dynamic section names 1 shared library (DT_NEEDED)",
                )
            } else {
                (STATIC, interp_and_needed)
            };
            refused_by_cli(
                dir,
                bin,
                &args(&format!("bdynamic_{linker}"), "main.o", &[bdynamic]),
                tag,
                &[text],
            );
            // Naming the loader.
            refused_by_cli(
                dir,
                bin,
                &args(
                    &format!("named_{linker}"),
                    "main.o",
                    &[bdynamic, DYNAMIC_LINKER],
                ),
                STATIC,
                &[interp_and_needed],
            );
            // A plain static link runs.
            runs(
                bin,
                &args(&format!("plain_{linker}"), "main.o", &[]),
                &format!("plain_{linker}"),
            );
            // An unused library `--as-needed` drops.
            let dropped = format!("as_needed_{linker}");
            match *linker {
                "gnu" => runs(bin, &args(&dropped, "main.o", &[as_needed]), &dropped),
                "gold" => refused_by_cli(
                    dir,
                    bin,
                    &args(&dropped, "main.o", &[as_needed]),
                    STATIC,
                    &[interp_only],
                ),
                _ => refused_by_cli(
                    dir,
                    bin,
                    &args(&dropped, "main.o", &[as_needed]),
                    NO_INTERP,
                    &[
                        "an ET_EXEC whose dynamic section holds relocations the dynamic loader \
                       applies (DT_",
                    ],
                ),
            }
            // A program that calls `libm`.
            let (tag, text) = if lld {
                (
                    NO_INTERP,
                    "an ET_EXEC whose dynamic section names 1 shared library (DT_NEEDED) and \
                     holds relocations",
                )
            } else {
                (STATIC, interp_and_needed)
            };
            refused_by_cli(
                dir,
                bin,
                &args(&format!("libm_{linker}"), "libm_main.o", &[as_needed]),
                tag,
                &[text],
            );
            // A dynamic link that names no loader.
            let unnamed: Vec<String> = [
                "--no-pie",
                "-o",
                &format!("no_loader_{linker}"),
                "b1_scalars.tmbc",
                "-Wl,main.o",
                "-Wl,--no-dynamic-linker",
            ]
            .iter()
            .map(|arg| arg.to_string())
            .collect();
            if *linker != "gold" {
                refused_by_cli(dir, bin, &unnamed, NO_INTERP, &["shared librar"]);
                // A PIE, by default or asked for, that names no loader.
                for (mode, output) in [
                    (None, "no_loader_default"),
                    (Some("--pie"), "no_loader_pie"),
                ] {
                    let output = format!("{output}_{linker}");
                    let pie: Vec<String> = mode
                        .into_iter()
                        .chain([
                            "-o",
                            &output,
                            "b1_scalars.tmbc",
                            "-Wl,main.o",
                            "-Wl,--no-dynamic-linker",
                        ])
                        .map(|arg| arg.to_string())
                        .collect();
                    refused_by_cli(
                        dir,
                        bin,
                        &pie,
                        NO_INTERP,
                        &[
                            "is a position-independent executable (ET_DYN with DF_1_PIE) whose \
                           dynamic section names 1 shared library (DT_NEEDED)",
                        ],
                    );
                }
            }
        }
        // The refusal names the options in effect as spelled: GNU ld reads
        // `-Bdyn` as `-Bdynamic`, and an earlier `-Bdynamic` that a
        // `-Bstatic` cancels before any library is not named.
        let why = "the -Wl option `-Bdyn` linked it dynamically, around static glibc's";
        refused_by_cli(
            dir,
            None,
            &args("bdyn_gnu", "main.o", &["-Wl,-Bdynamic,-Bstatic,-Bdyn"]),
            STATIC,
            &[why],
        );
        // `--push-state` saves the switch and `--pop-state` restores it (the
        // v5 verifier): a `-Bdyn` the `--pop-state` cancels before any
        // library is not named, and each option in effect is named once.
        refused_by_cli(
            dir,
            None,
            &args(
                "pop_gnu",
                "libm_main.o",
                &["-Wl,-Bdynamic,-lm,-Bstatic,--push-state,-Bdyn,--pop-state"],
            ),
            STATIC,
            &["the -Wl option `-Bdynamic` linked it dynamically, around static glibc's"],
        );
        // The v4 verifier's PIE without an interpreter that needs no library
        // and holds a dynamic relocation (`_start` calls through a function
        // pointer in `.data`), and one linked with `crt1.o`, whose
        // `_dl_relocate_static_pie` is a stub: nothing relocates them, and
        // each is refused through GNU ld and LLD. glibc's static PIE
        // (`rcrt1.o`, `libc.a`'s `_dl_relocate_static_pie`) installs and
        // runs.
        fs::write(dir.join("start.c"), PIE_START_SOURCE).unwrap();
        run_tool(
            dir,
            "cc",
            &["-c", "-O1", "-fPIE", "-o", "start.o", "start.c"],
        );
        let file = |name: &str| {
            let printed = Command::new("cc")
                .arg(format!("-print-file-name={name}"))
                .output()
                .unwrap();
            String::from_utf8(printed.stdout)
                .unwrap()
                .trim()
                .to_string()
        };
        let static_pie = |output: &str, start: &str| -> Vec<String> {
            vec![
                "--pie".to_string(),
                "--nostdlib".into(),
                "-o".into(),
                output.into(),
                "b1_scalars.tmbc".into(),
                format!(
                    "-Wl,--no-dynamic-linker,{},{},{},main.o,-Bstatic,--start-group,-lgcc,\
                     -lgcc_eh,-lc,--end-group,{},{}",
                    file(start),
                    file("crti.o"),
                    file("crtbeginS.o"),
                    file("crtendS.o"),
                    file("crtn.o")
                ),
            ]
        };
        for (linker, bin) in &linkers {
            if *linker == "gold" {
                continue;
            }
            let bin = bin.as_deref();
            let own_start: Vec<String> = [
                "--pie",
                "--nostdlib",
                "-o",
                &format!("own_start_{linker}"),
                "b1_scalars.tmbc",
                "-Wl,start.o,--no-dynamic-linker",
            ]
            .iter()
            .map(|arg| arg.to_string())
            .collect();
            refused_by_cli(
                dir,
                bin,
                &own_start,
                NO_INTERP,
                &[
                    "is a position-independent executable (ET_DYN with DF_1_PIE) that names no \
                     program interpreter (PT_INTERP) and holds dynamic relocations (",
                    "no loaded input defines _dl_relocate_static_pie",
                ],
            );
            refused_by_cli(
                dir,
                bin,
                &static_pie(&format!("stub_pie_{linker}"), "crt1.o"),
                NO_INTERP,
                &["crt1.o defines _dl_relocate_static_pie, and only the C driver's own libc.a's"],
            );
            let output = format!("static_pie_{linker}");
            runs(bin, &static_pie(&output, "rcrt1.o"), &output);
        }
        let output = trust_cg_on(None, dir, &["-c", "-o", "b1_scalars.o", "b1_scalars.tmbc"]);
        assert!(output.status.success(), "{}", stderr(&output));
        // GNU ld outside the driver: the own-start PIE dies with SIGSEGV.
        run_tool(
            dir,
            "cc",
            &[
                "-pie",
                "-nostdlib",
                "-o",
                "raw_own_start",
                "b1_scalars.o",
                "start.o",
                "-Wl,--no-dynamic-linker",
                "-Wl,-z,noexecstack",
            ],
        );
        assert_eq!(interpreter(&dir.join("raw_own_start")), "");
        let status = Command::new(dir.join("raw_own_start")).status().unwrap();
        eprintln!("raw_own_start, linked by GNU ld without the driver: {status:?}");
        assert_eq!(status.signal(), Some(SIGSEGV), "{status:?}");
        // GNU ld outside the driver: the `libm` image names its interpreter
        // and dies with SIGSEGV.
        run_tool(
            dir,
            "cc",
            &[
                "-static",
                "-o",
                "raw_gnu_libm",
                "libm_main.o",
                "b1_scalars.o",
                as_needed,
                "-Wl,-z,noexecstack",
            ],
        );
        assert_eq!(
            interpreter(&dir.join("raw_gnu_libm")),
            "/lib/ld-linux-aarch64.so.1"
        );
        let status = Command::new(dir.join("raw_gnu_libm")).status().unwrap();
        eprintln!("raw_gnu_libm, linked by GNU ld without the driver: {status:?}");
        assert_eq!(status.signal(), Some(SIGSEGV), "{status:?}");
        // GNU ld outside the driver: the PIE without an interpreter dies.
        run_tool(
            dir,
            "cc",
            &[
                "-o",
                "raw_gnu_pie",
                "main.o",
                "b1_scalars.o",
                "-Wl,--no-dynamic-linker",
                "-Wl,-z,noexecstack",
            ],
        );
        assert_eq!(interpreter(&dir.join("raw_gnu_pie")), "");
        let status = Command::new(dir.join("raw_gnu_pie")).status().unwrap();
        eprintln!("raw_gnu_pie, linked by GNU ld without the driver: {status:?}");
        assert_eq!(status.signal(), Some(SIGSEGV), "{status:?}");
        // LLD outside the driver: no `PT_INTERP`, SIGSEGV.
        if let Some(lld) = &lld {
            for (name, extra) in [("raw_lld", bdynamic), ("raw_lld_as_needed", as_needed)] {
                run_tool(
                    dir,
                    &lld.join("cc").display().to_string(),
                    &[
                        "-static",
                        "-o",
                        name,
                        "main.o",
                        "b1_scalars.o",
                        extra,
                        "-Wl,-z,noexecstack",
                    ],
                );
                assert_eq!(interpreter(&dir.join(name)), "", "{name}");
                let status = Command::new(dir.join(name)).status().unwrap();
                eprintln!("{name}, linked by LLD without the driver: {status:?}");
                assert_eq!(status.signal(), Some(SIGSEGV), "{name}: {status:?}");
            }
        }
    }

    /// No-op libgcc registration functions (the v5 verifier's `override.c`):
    /// defined in place of libgcc's, `crtbeginT.o`'s call registers nothing.
    const OVERRIDE_SOURCE: &str = "struct object;\nvoid __register_frame_info(const void *b, \
                                   struct object *o) { (void)b; (void)o; }\nvoid \
                                   __register_frame_info_bases(const void *b, struct object *o, \
                                   void *t, void *d) { (void)b; (void)o; (void)t; (void)d; }\nvoid \
                                   __deregister_frame_info(const void *b) { (void)b; }\n";

    /// [`OVERRIDE_SOURCE`] with libgcc's FDE lookup too, so no libgcc member
    /// that defines them is linked and no `-z muldefs` is needed.
    const OVERRIDE_ALL_SOURCE: &str = "struct object;\nvoid __register_frame_info(const void *b, \
                                       struct object *o) { (void)b; (void)o; }\nvoid \
                                       __register_frame_info_bases(const void *b, struct object \
                                       *o, void *t, void *d) { (void)b; (void)o; (void)t; \
                                       (void)d; }\nvoid *__deregister_frame_info(const void *b) { \
                                       (void)b; return 0; }\nconst void *_Unwind_Find_FDE(void \
                                       *pc, void *bases) { (void)pc; (void)bases; return 0; }\n";

    /// The v5 verifier's registration finding: an input that defines
    /// libgcc's registration functions as no-ops ([`OVERRIDE_SOURCE`]) takes
    /// the place of libgcc's under `-z muldefs`, so `crtbeginT.o`'s call
    /// registers nothing, and a `--static` link of it with
    /// `-Wl,--no-eh-frame-hdr` was installed through GNU ld and LLD (the check
    /// read only references to the functions); outside the driver GNU ld's
    /// program does not backtrace into `main`. Every spelling of multiple
    /// definitions (`-z muldefs`, `-zmuldefs`, `--allow-multiple-definition`,
    /// GNU ld's `--allow-m`) now leaves the registrations unknown, and so
    /// does an input that defines a registration function or libgcc's FDE
    /// lookup and is not a member of the C driver's own `libgcc_eh.a` or
    /// `libgcc.a` ([`OVERRIDE_ALL_SOURCE`], which needs no `-z muldefs`):
    /// without a table each is refused as `[TCG-LINK-EH-FRAME-UNPROVEN]`
    /// through GNU ld, gold and LLD, with nothing written. The table twin
    /// (`-z muldefs` and the no-op functions, with the table the driver asks
    /// for) installed and backtraced; since the v6 verifier's repair
    /// `-z muldefs` also leaves glibc's start-up code unknown, and it is
    /// refused as `[TCG-LINK-IRELATIVE-UNAPPLIED]`, while the plain link
    /// installs and backtraces into `main` through each. Without LLD or
    /// gold their legs are skipped (`SKIP:`).
    #[test]
    fn a_registration_function_defined_outside_libgcc_leaves_the_registrations_unknown() {
        let directory = tempfile::tempdir().unwrap();
        let dir = directory.path();
        copy_b1(dir);
        write_module(dir, "through.tmbc", &through_module());
        fs::write(dir.join("bt.c"), UNWIND_BT_SOURCE).unwrap();
        run_tool(dir, "cc", &["-c", "-O1", "-o", "bt.o", "bt.c"]);
        fs::write(dir.join("override.c"), OVERRIDE_SOURCE).unwrap();
        run_tool(dir, "cc", &["-c", "-O1", "-o", "override.o", "override.c"]);
        fs::write(dir.join("override_all.c"), OVERRIDE_ALL_SOURCE).unwrap();
        run_tool(
            dir,
            "cc",
            &["-c", "-O1", "-o", "override_all.o", "override_all.c"],
        );
        let args = |output: &str, wl: &str| -> Vec<String> {
            [
                "--static",
                "--no-pie",
                "-o",
                output,
                "b1_scalars.tmbc",
                "through.tmbc",
                wl,
            ]
            .iter()
            .map(|arg| arg.to_string())
            .collect()
        };
        let mut linkers: Vec<(&str, Option<PathBuf>)> = vec![("gnu", None)];
        linkers.extend(gold_cc(dir).map(|gold| ("gold", Some(gold))));
        linkers.extend(lld_dir().map(|lld| ("lld", Some(lld_cc(dir, &lld)))));
        let unknown = |spelling: &str| {
            format!(
                "the -Wl option `{spelling}` can bind another name to a registration function, \
                 redirect a reference to one or let a second definition of one stand"
            )
        };
        for (linker, bin) in &linkers {
            let bin = bin.as_deref();
            let mut spellings = vec![
                ("z", "-z muldefs", "-z,muldefs"),
                ("zjoined", "-zmuldefs", "-zmuldefs"),
                (
                    "allow",
                    "--allow-multiple-definition",
                    "--allow-multiple-definition",
                ),
            ];
            if *linker == "gnu" {
                spellings.push(("allow_m", "--allow-m", "--allow-m"));
            }
            for (name, spelling, pieces) in spellings {
                refused_by_cli(
                    dir,
                    bin,
                    &args(
                        &format!("{name}_{linker}"),
                        &format!("-Wl,bt.o,override.o,--no-eh-frame-hdr,{pieces}"),
                    ),
                    "[TCG-LINK-EH-FRAME-UNPROVEN]",
                    &[&unknown(spelling)],
                );
            }
            refused_by_cli(
                dir,
                bin,
                &args(
                    &format!("all_{linker}"),
                    "-Wl,bt.o,override_all.o,--no-eh-frame-hdr",
                ),
                "[TCG-LINK-EH-FRAME-UNPROVEN]",
                &[
                    "the input override_all.o defines _Unwind_Find_FDE, through which the C \
                     runtime's own start-up or unwinding code is reached",
                ],
            );
            // The table twin: `-z muldefs` also leaves glibc's start-up code
            // unknown, so it is refused whatever its table (the v6
            // verifier's repair); without the stand-in the program links.
            refused_by_cli(
                dir,
                bin,
                &args(&format!("table_{linker}"), "-Wl,bt.o,override.o,-z,muldefs"),
                IRELATIVE,
                &[&unknown("-z muldefs")],
            );
            installed_by_cli(dir, bin, &args(&format!("plain_{linker}"), "-Wl,bt.o"));
        }
        // GNU ld outside the driver: the program does not backtrace into
        // `main`.
        compile_bt_modules(dir);
        run_tool(
            dir,
            "cc",
            &[
                "-static",
                "-no-pie",
                "-o",
                "raw_override",
                "b1_scalars.o",
                "through.o",
                "bt.o",
                "override.o",
                "-Wl,--no-eh-frame-hdr",
                "-Wl,-z,muldefs",
                "-Wl,-z,noexecstack",
            ],
        );
        let (code, stdout) = run_program(&dir.join("raw_override"));
        let frames = stdout.matches("pc=").count();
        eprintln!(
            "raw_override, linked by GNU ld without the driver: exit {code:?}, {frames} frames"
        );
        assert!(code != Some(0) || frames < 3, "{code:?} {stdout}");
    }

    /// A `--nostdlib` program's own `_start` that calls an IFUNC it defines
    /// (the v5 verifier's `ifs.c`) and exits 0 when it returns 42.
    const IFUNC_START_SOURCE: &str = "extern long isize_add_one(long);\nstatic long impl(long x) { \
                                      return isize_add_one(x); }\nstatic void *resolve(void) { \
                                      return (void *)impl; }\nlong pick(long) \
                                      __attribute__((ifunc(\"resolve\")));\nstatic void \
                                      sys_exit(long code) {\n  register long x0 __asm__(\"x0\") = \
                                      code;\n  register long x8 __asm__(\"x8\") = 93;\n  __asm__ \
                                      volatile(\"svc 0\" : : \"r\"(x0), \"r\"(x8) : \
                                      \"memory\");\n  __builtin_unreachable();\n}\nvoid \
                                      _start(void) { sys_exit(pick(41) == 42 ? 0 : 1); }\n";

    /// `main` calls an IFUNC it defines, with glibc's start-up code, and
    /// prints what it returns.
    const IFUNC_MAIN_SOURCE: &str = "#include <stdio.h>\nextern long isize_add_one(long);\nstatic \
                                     long impl(long x) { return isize_add_one(x); }\nstatic void \
                                     *resolve(void) { return (void *)impl; }\nlong pick(long) \
                                     __attribute__((ifunc(\"resolve\")));\nint main(void) { long \
                                     v = pick(41); printf(\"v=%ld\\n\", v); return v == 42 ? 0 : \
                                     1; }\n";

    /// A stand-in for glibc's static-PIE relocator (the v5 verifier's
    /// `norel.c`): it reads `_DYNAMIC` and relocates nothing.
    const NOREL_SOURCE: &str = "extern char _DYNAMIC[] __attribute__((visibility(\"hidden\")));\n\
                                void *volatile dynamic_seen;\nvoid _dl_relocate_static_pie(void) \
                                { dynamic_seen = _DYNAMIC; }\n";

    /// [`PIE_START_SOURCE`] whose `_start` calls `_dl_relocate_static_pie`
    /// first (the v5 verifier's `start2.c`).
    const RELOCATING_START_SOURCE: &str = "extern long isize_add_one(long);\nextern void \
                                           _dl_relocate_static_pie(void);\nlong (*volatile \
                                           fp)(long) = isize_add_one;\nstatic void \
                                           sys_exit(long code) {\n  register long x0 \
                                           __asm__(\"x0\") = code;\n  register long x8 \
                                           __asm__(\"x8\") = 93;\n  __asm__ volatile(\"svc 0\" \
                                           : : \"r\"(x0), \"r\"(x8) : \"memory\");\n  \
                                           __builtin_unreachable();\n}\nvoid _start(void) { \
                                           _dl_relocate_static_pie(); sys_exit(fp(41) == 42 ? 0 \
                                           : 1); }\n";

    /// The v5 verifier's start-up findings. A `--static --nostdlib` program
    /// whose own `_start` calls an IFUNC ([`IFUNC_START_SOURCE`]) links with
    /// an `R_AARCH64_IRELATIVE` that nothing applies (only glibc's start-up
    /// code does, `apply_irel` in `libc.a`'s `libc-start.o`, run by
    /// `__libc_start_main`), and it was installed through GNU ld, gold and
    /// LLD, and `--no-pie --nostdlib` through GNU ld and gold; outside the
    /// driver gold's and LLD's programs die with SIGSEGV (GNU ld's hangs).
    /// Each is now refused as `[TCG-LINK-IRELATIVE-UNAPPLIED]` with nothing
    /// written, and so is the program linked with `libc.a` whose `_start` is
    /// still its own (no `libc-start.o` is linked); LLD's `--no-pie` image
    /// names an interpreter and is refused as
    /// `[TCG-LINK-INTERP-NO-DYNAMIC]`. A glibc static program that calls an
    /// IFUNC ([`IFUNC_MAIN_SOURCE`]) installs and runs through each. A static
    /// PIE relocated by a `_dl_relocate_static_pie` of another input (the
    /// verifier's `norel.o`, which reads `_DYNAMIC` and applies nothing, with
    /// its own `_start`) was taken as glibc's, by name, and installed; it,
    /// and glibc's relocator from `libc.a` called from a `_start` of the
    /// program's own, are refused as `[TCG-LINK-DYNAMIC-NO-INTERP]` through
    /// GNU ld and LLD: only a member of the C driver's own `libc.a`, with
    /// `_start` from its own `rcrt1.o`, is taken to relocate the image
    /// (glibc's static PIE installs and runs in
    /// [`a_static_link_that_is_not_static_is_refused`]); outside the driver
    /// GNU ld's `norel` program dies with SIGSEGV. Without LLD or gold their
    /// legs are skipped (`SKIP:`).
    #[test]
    fn a_static_image_without_glibcs_start_up_code_is_refused() {
        const IRELATIVE: &str = "[TCG-LINK-IRELATIVE-UNAPPLIED]";
        const NO_INTERP: &str = "[TCG-LINK-DYNAMIC-NO-INTERP]";
        let directory = tempfile::tempdir().unwrap();
        let dir = directory.path();
        copy_b1(dir);
        for (name, source) in [
            ("ifs", IFUNC_START_SOURCE),
            ("ifs_main", IFUNC_MAIN_SOURCE),
            ("norel", NOREL_SOURCE),
            ("start2", RELOCATING_START_SOURCE),
        ] {
            fs::write(dir.join(format!("{name}.c")), source).unwrap();
            run_tool(
                dir,
                "cc",
                &[
                    "-c",
                    "-O1",
                    "-fPIE",
                    "-o",
                    &format!("{name}.o"),
                    &format!("{name}.c"),
                ],
            );
        }
        let file = |name: &str| {
            let printed = Command::new("cc")
                .arg(format!("-print-file-name={name}"))
                .output()
                .unwrap();
            String::from_utf8(printed.stdout)
                .unwrap()
                .trim()
                .to_string()
        };
        let libc = "-Bstatic,--start-group,-lgcc,-lgcc_eh,-lc,--end-group";
        let owned =
            |args: &[&str]| -> Vec<String> { args.iter().map(|arg| arg.to_string()).collect() };
        let unapplied = "is a static executable with IFUNC relocations (it holds 1 \
                         R_AARCH64_IRELATIVE relocation) and no member of the C driver's own \
                         libc.a";
        let lld = lld_dir().map(|lld| lld_cc(dir, &lld));
        let gold = gold_cc(dir);
        let mut linkers: Vec<(&str, Option<PathBuf>)> = vec![("gnu", None)];
        linkers.extend(gold.clone().map(|gold| ("gold", Some(gold))));
        linkers.extend(lld.clone().map(|lld| ("lld", Some(lld))));
        for (linker, bin) in &linkers {
            let bin = bin.as_deref();
            refused_by_cli(
                dir,
                bin,
                &owned(&[
                    "--static",
                    "--nostdlib",
                    "-o",
                    &format!("ifs_static_{linker}"),
                    "b1_scalars.tmbc",
                    "-Wl,ifs.o",
                ]),
                IRELATIVE,
                &[unapplied],
            );
            refused_by_cli(
                dir,
                bin,
                &owned(&[
                    "--static",
                    "--nostdlib",
                    "-o",
                    &format!("ifs_libc_{linker}"),
                    "b1_scalars.tmbc",
                    &format!("-Wl,ifs.o,{libc}"),
                ]),
                IRELATIVE,
                &[unapplied],
            );
            let no_pie = owned(&[
                "--no-pie",
                "--nostdlib",
                "-o",
                &format!("ifs_no_pie_{linker}"),
                "b1_scalars.tmbc",
                "-Wl,ifs.o",
            ]);
            if *linker == "lld" {
                refused_by_cli(dir, bin, &no_pie, "[TCG-LINK-INTERP-NO-DYNAMIC]", &[]);
            } else {
                refused_by_cli(dir, bin, &no_pie, IRELATIVE, &[unapplied]);
            }
            // glibc's static program that calls an IFUNC runs.
            let output = format!("ifs_glibc_{linker}");
            let result = trust_cg_on(
                bin,
                dir,
                &[
                    "--static",
                    "-o",
                    &output,
                    "b1_scalars.tmbc",
                    "-Wl,ifs_main.o",
                ],
            );
            assert!(result.status.success(), "{output}: {}", stderr(&result));
            let run = Command::new(dir.join(&output)).output().unwrap();
            assert!(
                run.status.success() && String::from_utf8_lossy(&run.stdout).contains("v=42"),
                "{output}: {run:?}"
            );
            // gold refuses `--no-dynamic-linker`.
            if *linker == "gold" {
                continue;
            }
            refused_by_cli(
                dir,
                bin,
                &owned(&[
                    "--pie",
                    "--nostdlib",
                    "-o",
                    &format!("norel_{linker}"),
                    "b1_scalars.tmbc",
                    "-Wl,norel.o,start2.o,--no-dynamic-linker",
                ]),
                NO_INTERP,
                &["norel.o defines _dl_relocate_static_pie, and only the C driver's own libc.a's"],
            );
            refused_by_cli(
                dir,
                bin,
                &owned(&[
                    "--pie",
                    "--nostdlib",
                    "-o",
                    &format!("own_start_glibc_relocator_{linker}"),
                    "b1_scalars.tmbc",
                    &format!(
                        "-Wl,--no-dynamic-linker,{},start2.o,{libc},{}",
                        file("crti.o"),
                        file("crtn.o")
                    ),
                ]),
                NO_INTERP,
                &[
                    "_start is defined by start2.o, and only the C driver's own static-PIE start \
                   files",
                ],
            );
        }
        // Outside the driver.
        let output = trust_cg_on(None, dir, &["-c", "-o", "b1_scalars.o", "b1_scalars.tmbc"]);
        assert!(output.status.success(), "{}", stderr(&output));
        run_tool(
            dir,
            "cc",
            &[
                "-pie",
                "-nostdlib",
                "-o",
                "raw_norel",
                "b1_scalars.o",
                "norel.o",
                "start2.o",
                "-Wl,--no-dynamic-linker",
                "-Wl,-z,noexecstack",
            ],
        );
        let status = Command::new(dir.join("raw_norel")).status().unwrap();
        eprintln!("raw_norel, linked by GNU ld without the driver: {status:?}");
        assert_eq!(status.signal(), Some(SIGSEGV), "{status:?}");
        for (linker, bin) in [("gold", &gold), ("lld", &lld)] {
            let Some(bin) = bin else {
                continue;
            };
            let name = format!("raw_ifs_{linker}");
            run_tool(
                dir,
                &bin.join("cc").display().to_string(),
                &[
                    "-static",
                    "-nostdlib",
                    "-o",
                    &name,
                    "b1_scalars.o",
                    "ifs.o",
                    "-Wl,-z,noexecstack",
                ],
            );
            let status = Command::new(dir.join(&name)).status().unwrap();
            eprintln!("{name}, linked by {linker} without the driver: {status:?}");
            assert_eq!(status.signal(), Some(SIGSEGV), "{name}: {status:?}");
        }
    }

    /// A `__libc_start_main` of the program's own (the v6 verifier's
    /// `mystart.c`): it calls `main` and exits, and applies no IFUNC
    /// relocation.
    const MYSTART_SOURCE: &str = "extern int main(int, char **, char **);\nstatic void \
                                  sys_exit(long code) {\n  register long x0 __asm__(\"x0\") = \
                                  code;\n  register long x8 __asm__(\"x8\") = 93;\n  __asm__ \
                                  volatile(\"svc 0\" : : \"r\"(x0), \"r\"(x8) : \"memory\");\n  \
                                  __builtin_unreachable();\n}\nint __libc_start_main(int \
                                  (*m)(int, char **, char **), int argc, char **argv, void *i, \
                                  void *f, void *r, void *se) {\n  (void)i; (void)f; (void)r; \
                                  (void)se; char *e[] = {0};\n  sys_exit(m(argc, argv, e));\n}\n";

    /// The v6 verifier's start-up finding: the static-PIE relocator and the
    /// IFUNC applier were checked to be linked from the C driver's own
    /// `libc.a`, not to be the definitions that win. A static glibc program
    /// that calls an IFUNC ([`IFUNC_MAIN_SOURCE`]) linked with
    /// `-Wl,--defsym=__rela_iplt_start=0` was installed through GNU ld, gold
    /// and LLD (GNU ld's program dies with SIGSEGV outside the driver), and
    /// so was one with a `__libc_start_main` of its own ([`MYSTART_SOURCE`])
    /// under `-z muldefs` (it hangs); a glibc static PIE given
    /// `--defsym=_dl_relocate_static_pie=0` was installed through GNU ld and
    /// LLD. Each is now refused, as are a script operand and a `-l` library
    /// that is a script (`__libc_start_main = main;`, which gold's trace and
    /// map do not show): one rule ([`c_runtime_stand_ins`] in the driver) for
    /// the relocator, the applier and the frame registration. Twins: the
    /// same program, one with a `--defsym` and a `--wrap` of names the C
    /// runtime does not reach, and one that calls `libm` (glibc's own
    /// `libm.a` is a script) install and run through each linker; a static
    /// executable without a table given an inert `--defsym`, refused before,
    /// installs and backtraces into `main` through GNU ld and LLD. Without
    /// LLD or gold their legs are skipped (`SKIP:`).
    #[test]
    fn a_definition_that_takes_the_place_of_glibcs_start_up_code_is_refused() {
        const NO_INTERP: &str = "[TCG-LINK-DYNAMIC-NO-INTERP]";
        let directory = tempfile::tempdir().unwrap();
        let dir = directory.path();
        copy_b1(dir);
        write_module(dir, "through.tmbc", &through_module());
        for (name, source) in [
            ("ifs_main", IFUNC_MAIN_SOURCE),
            ("mystart", MYSTART_SOURCE),
            ("libm_main", STATIC_LIBM_MAIN),
            ("main", STATIC_BDYNAMIC_MAIN),
            ("bt", UNWIND_BT_SOURCE),
        ] {
            fs::write(dir.join(format!("{name}.c")), source).unwrap();
            run_tool(
                dir,
                "cc",
                &[
                    "-c",
                    "-O1",
                    "-fPIE",
                    "-o",
                    &format!("{name}.o"),
                    &format!("{name}.c"),
                ],
            );
        }
        fs::write(dir.join("redirect.ld"), "__libc_start_main = main;\n").unwrap();
        fs::write(dir.join("libredir.a"), "__libc_start_main = main;\n").unwrap();
        let file = |name: &str| {
            let printed = Command::new("cc")
                .arg(format!("-print-file-name={name}"))
                .output()
                .unwrap();
            String::from_utf8(printed.stdout)
                .unwrap()
                .trim()
                .to_string()
        };
        let static_args = |output: &str, wl: &str| -> Vec<String> {
            ["--static", "-o", output, "b1_scalars.tmbc", wl]
                .iter()
                .map(|arg| arg.to_string())
                .collect()
        };
        let static_pie = |output: &str, extra: &str| -> Vec<String> {
            vec![
                "--pie".to_string(),
                "--nostdlib".into(),
                "-o".into(),
                output.into(),
                "b1_scalars.tmbc".into(),
                format!(
                    "-Wl,--no-dynamic-linker,{},{},{},main.o,-Bstatic,--start-group,-lgcc,\
                     -lgcc_eh,-lc,--end-group,{},{}{extra}",
                    file("rcrt1.o"),
                    file("crti.o"),
                    file("crtbeginS.o"),
                    file("crtendS.o"),
                    file("crtn.o")
                ),
            ]
        };
        let runs = |bin: Option<&Path>, args: &[String], output: &str, text: &str| {
            let result = trust_cg_on(
                bin,
                dir,
                &args.iter().map(String::as_str).collect::<Vec<_>>(),
            );
            assert!(result.status.success(), "{output}: {}", stderr(&result));
            let run = Command::new(dir.join(output)).output().unwrap();
            assert!(
                run.status.success() && String::from_utf8_lossy(&run.stdout).contains(text),
                "{output}: {run:?}"
            );
        };
        let bound = |name: &str| {
            format!("binds or redirects {name}, through which the C runtime's own start-up")
        };
        let mut linkers: Vec<(&str, Option<PathBuf>)> = vec![("gnu", None)];
        linkers.extend(gold_cc(dir).map(|gold| ("gold", Some(gold))));
        linkers.extend(lld_dir().map(|lld| ("lld", Some(lld_cc(dir, &lld)))));
        for (linker, bin) in &linkers {
            let bin = bin.as_deref();
            refused_by_cli(
                dir,
                bin,
                &static_args(
                    &format!("defsym_irel_{linker}"),
                    "-Wl,ifs_main.o,--defsym=__rela_iplt_start=0",
                ),
                IRELATIVE,
                &[&bound("__rela_iplt_start")],
            );
            refused_by_cli(
                dir,
                bin,
                &static_args(
                    &format!("muldefs_start_{linker}"),
                    "-Wl,ifs_main.o,mystart.o,-z,muldefs",
                ),
                IRELATIVE,
                &["the -Wl option `-z muldefs` can bind another name"],
            );
            refused_by_cli(
                dir,
                bin,
                &static_args(
                    &format!("script_redirect_{linker}"),
                    "-Wl,ifs_main.o,redirect.ld",
                ),
                IRELATIVE,
                &["the linker input redirect.ld is neither an ELF file nor an archive"],
            );
            refused_by_cli(
                dir,
                bin,
                &static_args(
                    &format!("library_redirect_{linker}"),
                    "-Wl,ifs_main.o,-L.,-lredir",
                ),
                IRELATIVE,
                &["the library -lredir (./libredir.a) is neither an ELF file nor an archive"],
            );
            // Twins.
            for (output, wl) in [
                ("glibc_ifunc", "-Wl,ifs_main.o"),
                (
                    "defsym_inert",
                    "-Wl,ifs_main.o,--defsym=tcg_unrelated=isize_add_one",
                ),
                ("wrap_inert", "-Wl,ifs_main.o,--wrap=tcg_nothing"),
            ] {
                let output = format!("{output}_{linker}");
                runs(bin, &static_args(&output, wl), &output, "v=42");
            }
            let output = format!("libm_{linker}");
            runs(
                bin,
                &static_args(&output, "-Wl,libm_main.o,-lm"),
                &output,
                "v=42",
            );
            if *linker != "gold" {
                // An inert `--defsym` in a static executable without a table.
                installed_by_cli(
                    dir,
                    bin,
                    &[
                        "--static",
                        "--no-pie",
                        "-o",
                        &format!("eh_defsym_inert_{linker}"),
                        "b1_scalars.tmbc",
                        "through.tmbc",
                        "-Wl,bt.o,--no-eh-frame-hdr,--defsym=tcg_inert=0",
                    ]
                    .iter()
                    .map(|arg| arg.to_string())
                    .collect::<Vec<_>>(),
                );
                // gold refuses `--no-dynamic-linker`.
                refused_by_cli(
                    dir,
                    bin,
                    &static_pie(
                        &format!("spie_defsym_{linker}"),
                        ",--defsym=_dl_relocate_static_pie=0",
                    ),
                    NO_INTERP,
                    &[&bound("_dl_relocate_static_pie")],
                );
                let output = format!("spie_{linker}");
                runs(bin, &static_pie(&output, ""), &output, "v=42");
            }
        }
        // GNU ld outside the driver.
        let output = trust_cg_on(None, dir, &["-c", "-o", "b1_scalars.o", "b1_scalars.tmbc"]);
        assert!(output.status.success(), "{}", stderr(&output));
        run_tool(
            dir,
            "cc",
            &[
                "-static",
                "-o",
                "raw_defsym_irel",
                "ifs_main.o",
                "b1_scalars.o",
                "-Wl,--defsym=__rela_iplt_start=0",
                "-Wl,-z,noexecstack",
            ],
        );
        let status = Command::new(dir.join("raw_defsym_irel")).status().unwrap();
        eprintln!("raw_defsym_irel, linked by GNU ld without the driver: {status:?}");
        assert_eq!(status.signal(), Some(SIGSEGV), "{status:?}");
    }

    /// The v7 verifier's findings. A separate value of an option the
    /// driver's short list did not name was read as an input and, being
    /// neither ELF nor an archive, as a linker script: static links with
    /// LLD's `--symbol-ordering-file order.txt`, gold's
    /// `--section-ordering-file`, `--export-dynamic-symbol-list`, one-dash
    /// `-version-script` and `-dynamic-list`, or `--error-handling-script`
    /// were refused as `[TCG-LINK-IRELATIVE-UNAPPLIED]` (CMake's `LINKER:`
    /// syntax writes that spelling). Options are now read as the three
    /// linkers were measured to read them (`linker_options`, generated
    /// natively by `scripts/generate_linker_options.py`): each such link
    /// installs and runs through every linker that has the option, while a
    /// script input, after a flag or not, stays refused. And in a `--static` link gold
    /// found a `.so` script after `-Wl,-Bdynamic`
    /// (`libredir2.so`: `__libc_start_main = main;`), which its trace and map
    /// do not show, and installed a program that dies with SIGSEGV; the
    /// driver looked `-l` libraries up as `.a` alone in a static link. A
    /// library is now looked up as `.so` too while a dynamic lookup is in
    /// effect (`-Bdynamic`, `-dy`, `-call_shared`, up to `-Bstatic` or
    /// `--pop-state`), and the link is refused through each linker. Without
    /// LLD or gold their legs are skipped (`SKIP:`).
    #[test]
    fn wl_option_values_and_library_lookups_are_read_as_each_linker_reads_them() {
        let directory = tempfile::tempdir().unwrap();
        let dir = directory.path();
        copy_b1(dir);
        fs::write(dir.join("ifs_main.c"), IFUNC_MAIN_SOURCE).unwrap();
        run_tool(
            dir,
            "cc",
            &["-c", "-O1", "-fPIE", "-o", "ifs_main.o", "ifs_main.c"],
        );
        for (name, text) in [
            ("order.txt", "main\nisize_add_one\n"),
            ("sorder.txt", ".text.main\n"),
            ("dl.list", "{ isize_add_one; };\n"),
            ("vs.map", "{ global: main; isize_add_one; local: *; };\n"),
            ("on_error.sh", "#!/bin/sh\nexit 0\n"),
            ("redir.ld", "__libc_start_main = main;\n"),
        ] {
            fs::write(dir.join(name), text).unwrap();
        }
        fs::create_dir(dir.join("d1")).unwrap();
        fs::write(dir.join("d1/libredir2.so"), "__libc_start_main = main;\n").unwrap();
        let static_args = |output: &str, wl: &str| -> Vec<String> {
            ["--static", "-o", output, "b1_scalars.tmbc", wl]
                .iter()
                .map(|arg| arg.to_string())
                .collect()
        };
        let runs = |bin: Option<&Path>, output: &str, wl: &str| {
            let result = trust_cg_on(
                bin,
                dir,
                &static_args(output, wl)
                    .iter()
                    .map(String::as_str)
                    .collect::<Vec<_>>(),
            );
            assert!(result.status.success(), "{output}: {}", stderr(&result));
            let run = Command::new(dir.join(output)).output().unwrap();
            assert!(
                run.status.success() && String::from_utf8_lossy(&run.stdout).contains("v=42"),
                "{output}: {run:?}"
            );
        };
        let gold = gold_cc(dir);
        let lld = lld_dir().map(|lld| lld_cc(dir, &lld));
        let mut linkers: Vec<(&str, Option<PathBuf>)> = vec![("gnu", None)];
        linkers.extend(gold.clone().map(|gold| ("gold", Some(gold))));
        linkers.extend(lld.clone().map(|lld| ("lld", Some(lld))));
        for (linker, bin) in &linkers {
            let bin = bin.as_deref();
            let mut installs = vec![
                ("version_script", "-Wl,ifs_main.o,-version-script,vs.map"),
                ("dynamic_list", "-Wl,ifs_main.o,-dynamic-list,dl.list"),
            ];
            match *linker {
                "gnu" => installs.extend([
                    (
                        "symbol_list",
                        "-Wl,ifs_main.o,--export-dynamic-symbol-list,dl.list",
                    ),
                    (
                        "error_script",
                        "-Wl,ifs_main.o,--error-handling-script,on_error.sh",
                    ),
                    ("abbreviated", "-Wl,ifs_main.o,--version-scr,vs.map"),
                ]),
                "gold" => installs.push((
                    "section_order",
                    "-Wl,ifs_main.o,--section-ordering-file,sorder.txt",
                )),
                _ => installs.extend([
                    (
                        "symbol_order",
                        "-Wl,ifs_main.o,--symbol-ordering-file,order.txt",
                    ),
                    (
                        "symbol_list",
                        "-Wl,ifs_main.o,--export-dynamic-symbol-list,dl.list",
                    ),
                    (
                        "error_script",
                        "-Wl,ifs_main.o,--error-handling-script,on_error.sh",
                    ),
                ]),
            }
            for (name, wl) in installs {
                runs(bin, &format!("{name}_{linker}"), wl);
            }
            // A script input stays refused, after a flag or not.
            for (name, wl) in [
                ("script", "-Wl,ifs_main.o,redir.ld"),
                ("script_after_flag", "-Wl,ifs_main.o,--gc-sections,redir.ld"),
            ] {
                refused_by_cli(
                    dir,
                    bin,
                    &static_args(&format!("{name}_{linker}"), wl),
                    IRELATIVE,
                    &["the linker input redir.ld is neither an ELF file nor an archive"],
                );
            }
            // A `.so` script found after `-Bdynamic`.
            for (name, wl) in [
                (
                    "bdynamic",
                    "-Wl,ifs_main.o,-Bdynamic,-Ld1,-lredir2,-Bstatic",
                ),
                ("dy", "-Wl,ifs_main.o,-dy,-Ld1,-lredir2,-dn"),
            ] {
                refused_by_cli(
                    dir,
                    bin,
                    &static_args(&format!("{name}_{linker}"), wl),
                    IRELATIVE,
                    &[
                        "the library -lredir2 (d1/libredir2.so) is neither an ELF file nor an \
                       archive",
                    ],
                );
            }
        }
        // gold outside the driver: its `-Bdynamic` program dies with SIGSEGV.
        if let Some(gold) = &gold {
            let output = trust_cg_on(None, dir, &["-c", "-o", "b1_scalars.o", "b1_scalars.tmbc"]);
            assert!(output.status.success(), "{}", stderr(&output));
            run_tool(
                dir,
                &gold.join("cc").display().to_string(),
                &[
                    "-static",
                    "-o",
                    "raw_bdynamic_gold",
                    "ifs_main.o",
                    "b1_scalars.o",
                    "-Wl,-Bdynamic,-Ld1,-lredir2,-Bstatic",
                    "-Wl,-z,noexecstack",
                ],
            );
            let status = Command::new(dir.join("raw_bdynamic_gold"))
                .status()
                .unwrap();
            eprintln!("raw_bdynamic_gold, linked by gold without the driver: {status:?}");
            assert_eq!(status.signal(), Some(SIGSEGV), "{status:?}");
        }
    }

    /// The v8 verifier's findings. The option table parsed from `--help`
    /// read a flag whose description is one space from its name as taking
    /// a value, so the driver skipped the piece after
    /// `--no-copy-dt-needed-entries` or `--dynamic-list-cpp-typeinfo`: a
    /// script input there (`redir.ld`: `__libc_start_main = main;`), or a
    /// `-l` script library, was not refused, and gold (whose trace and map
    /// name no script) installed a program that dies with SIGSEGV. The
    /// table is now measured natively (each spelling followed by a script
    /// input, through each linker), and those links are refused through
    /// every linker that accepts the flag. Gold also found scripts the
    /// driver's library lookup did not model: under `-Wl,--sysroot=DIR`
    /// (`DIR/usr/lib/libredir9.a`, and `libredir8.so` after `-Bdynamic`),
    /// and the C driver's own `-lc` in a typed `-L` directory (`d5/libc.a`:
    /// `INPUT` of glibc's `libc.a` and `__libc_start_main = main;`). The
    /// lookup now reads a sysroot and the C driver's own libraries, and a
    /// gold link also runs again with `--debug=files`, whose record of every
    /// file gold opened is checked as GNU ld's trace is. Each is refused
    /// through each linker that links it; a `libc.a` script that only
    /// forwards to glibc's (`d5c`) is refused too, since the check does
    /// not read scripts. A flag followed by an ELF input, a script-like
    /// option value, and a sysroot alone install and run. A linker whose
    /// `--version` is not one the table was measured on (a driver that
    /// answers `-Wl,--version` itself) is refused for an option's
    /// script-like value only. Without LLD or gold their legs are skipped
    /// (`SKIP:`).
    #[test]
    fn flags_are_read_as_measured_and_gold_library_routes_are_refused() {
        let directory = tempfile::tempdir().unwrap();
        let dir = directory.path();
        copy_b1(dir);
        fs::write(dir.join("ifs_main.c"), IFUNC_MAIN_SOURCE).unwrap();
        run_tool(
            dir,
            "cc",
            &["-c", "-O1", "-fPIE", "-o", "ifs_main.o", "ifs_main.c"],
        );
        let redirect = "__libc_start_main = main;\n";
        let forward = "INPUT ( /usr/lib/aarch64-linux-gnu/libc.a )\n";
        for sub in ["d1", "d5", "d5c", "sr/usr/lib"] {
            fs::create_dir_all(dir.join(sub)).unwrap();
        }
        for (name, text) in [
            ("redir.ld", redirect.to_string()),
            (
                "vs.map",
                "{ global: main; isize_add_one; local: *; };\n".to_string(),
            ),
            ("d1/libredir.a", redirect.to_string()),
            ("d1/libredir2.so", redirect.to_string()),
            ("sr/usr/lib/libredir9.a", redirect.to_string()),
            ("sr/usr/lib/libredir8.so", redirect.to_string()),
            ("d5/libc.a", format!("{forward}{redirect}")),
            ("d5c/libc.a", forward.to_string()),
        ] {
            fs::write(dir.join(name), text).unwrap();
        }
        let absolute = |name: &str| dir.join(name).display().to_string();
        let sysroot = format!("--sysroot={}", absolute("sr"));
        let (d5, d5c) = (absolute("d5"), absolute("d5c"));
        let args = |output: &str, extra: &[&str]| -> Vec<String> {
            ["--static", "-o", output, "b1_scalars.tmbc"]
                .iter()
                .chain(extra)
                .map(|arg| arg.to_string())
                .collect()
        };
        let runs = |bin: Option<&Path>, output: &str, extra: &[&str]| {
            let result = trust_cg_on(
                bin,
                dir,
                &args(output, extra)
                    .iter()
                    .map(String::as_str)
                    .collect::<Vec<_>>(),
            );
            assert!(result.status.success(), "{output}: {}", stderr(&result));
            let run = Command::new(dir.join(output)).output().unwrap();
            assert!(
                run.status.success() && String::from_utf8_lossy(&run.stdout).contains("v=42"),
                "{output}: {run:?}"
            );
        };
        let script_input = "the linker input redir.ld is neither an ELF file nor an archive";
        let gold = gold_cc(dir);
        let lld = lld_dir().map(|lld| lld_cc(dir, &lld));
        let mut linkers: Vec<(&str, Option<PathBuf>)> = vec![("gnu", None)];
        linkers.extend(gold.clone().map(|gold| ("gold", Some(gold))));
        linkers.extend(lld.clone().map(|lld| ("lld", Some(lld))));
        for (linker, bin) in &linkers {
            let bin = bin.as_deref();
            let sysroot_so = format!("-Wl,ifs_main.o,{sysroot},-Bdynamic,-lredir8,-Bstatic");
            let sysroot_a = format!("-Wl,ifs_main.o,{sysroot},-lredir9");
            let libc = format!("the library -lc ({}) is neither", absolute("d5/libc.a"));
            let libc_forward = format!("the library -lc ({}) is neither", absolute("d5c/libc.a"));
            let redir9 = format!(
                "the library -lredir9 ({}) is neither",
                absolute("sr/usr/lib/libredir9.a")
            );
            let redir8 = format!(
                "the library -lredir8 ({}) is neither",
                absolute("sr/usr/lib/libredir8.so")
            );
            let mut refused: Vec<(&str, Vec<&str>, &str)> = vec![
                (
                    "nocopy",
                    vec!["-Wl,ifs_main.o,--no-copy-dt-needed-entries,redir.ld"],
                    script_input,
                ),
                (
                    "nocopy_lib",
                    vec!["-Wl,ifs_main.o,-Ld1,--no-copy-dt-needed-entries,-lredir"],
                    "the library -lredir (d1/libredir.a) is neither",
                ),
                (
                    "nocopy_so",
                    vec![
                        "-Wl,ifs_main.o,-Bdynamic,-Ld1,--no-copy-dt-needed-entries,-lredir2,\
                         -Bstatic",
                    ],
                    "the library -lredir2 (d1/libredir2.so) is neither",
                ),
                ("typed_l", vec!["-L", &d5, "-Wl,ifs_main.o"], &libc),
                (
                    "typed_l_forward",
                    vec!["-L", &d5c, "-Wl,ifs_main.o"],
                    &libc_forward,
                ),
            ];
            // LLD has no `--dynamic-list-cpp-typeinfo`, and no default
            // directories for a sysroot to move.
            if *linker != "lld" {
                refused.extend([
                    (
                        "cpptypeinfo",
                        vec!["-Wl,ifs_main.o,--dynamic-list-cpp-typeinfo,redir.ld"],
                        script_input,
                    ),
                    (
                        "cpptypeinfo_one_dash",
                        vec!["-Wl,ifs_main.o,-dynamic-list-cpp-typeinfo,redir.ld"],
                        script_input,
                    ),
                    ("sysroot", vec![sysroot_a.as_str()], redir9.as_str()),
                    ("sysroot_so", vec![sysroot_so.as_str()], redir8.as_str()),
                ]);
            }
            for (name, extra, text) in refused {
                refused_by_cli(
                    dir,
                    bin,
                    &args(&format!("{name}_{linker}"), &extra),
                    IRELATIVE,
                    &[text],
                );
            }
            // A flag followed by an ELF input, an option's script-like
            // value, and a sysroot alone.
            let sysroot_alone = format!("-Wl,ifs_main.o,{sysroot}");
            for (name, extra) in [
                ("nocopy_elf", "-Wl,--no-copy-dt-needed-entries,ifs_main.o"),
                ("version_script", "-Wl,ifs_main.o,--version-script,vs.map"),
                ("sysroot_alone", sysroot_alone.as_str()),
            ] {
                runs(bin, &format!("{name}_{linker}"), &[extra]);
            }
        }
        // A driver whose linker names itself as no linker the table was
        // measured on: an option's script-like value is refused, and the
        // link without one installs.
        let other = dir.join("other-cc");
        fs::create_dir(&other).unwrap();
        write_executable_script(
            &other.join("cc"),
            "#!/bin/sh\nif [ \"$#\" = 1 ] && [ \"$1\" = -Wl,--version ]; then\n  echo 'GNU ld \
             (other) 9.99'\n  exit 0\nfi\nexec /usr/bin/cc \"$@\"\n",
        );
        refused_by_cli(
            dir,
            Some(&other),
            &args(
                "other_version_script",
                &["-Wl,ifs_main.o,--version-script,vs.map"],
            ),
            IRELATIVE,
            &[
                "vs.map, which is neither an ELF file nor an archive, is the value of the -Wl \
                 option `--version-script` for the linkers the option table was measured on, but \
                 the linker names itself `GNU ld (other) 9.99`",
            ],
        );
        runs(Some(&other), "other_plain", &["-Wl,ifs_main.o"]);
        // gold outside the driver: the flag's and the typed `-L`'s programs
        // die with SIGSEGV.
        if let Some(gold) = &gold {
            let output = trust_cg_on(None, dir, &["-c", "-o", "b1_scalars.o", "b1_scalars.tmbc"]);
            assert!(output.status.success(), "{}", stderr(&output));
            for (name, extra) in [
                (
                    "raw_nocopy_gold",
                    vec!["-Wl,--no-copy-dt-needed-entries,redir.ld"],
                ),
                ("raw_typed_l_gold", vec!["-L", d5.as_str()]),
            ] {
                let mut raw = vec!["-static", "-o", name, "ifs_main.o", "b1_scalars.o"];
                raw.extend(extra);
                raw.push("-Wl,-z,noexecstack");
                run_tool(dir, &gold.join("cc").display().to_string(), &raw);
                let status = Command::new(dir.join(name)).status().unwrap();
                eprintln!("{name}, linked by gold without the driver: {status:?}");
                assert_eq!(status.signal(), Some(SIGSEGV), "{status:?}");
            }
        }
    }

    /// The v4 verifier's map findings: gold wrote the map of
    /// `-Wl,-Map=prog,-M` (and `--print-map`, `-print-map`, `-Mx`, a group
    /// of short options refused as such since the tenth closure audit)
    /// itself over `prog`, the output of a refused or failed link, because a later
    /// `-M` put the driver's `-Map` first; a `-Map=maplink` whose dangling
    /// link names the absent output, `-Map=./prog` and `-Map=target` for an
    /// output `prog -> target` each created the output's file with the map;
    /// and the warning that the map was not written went to the discarded
    /// standard error of a refused link. Now the linker is given no map path
    /// of the user's, and through GNU ld, gold and LLD, for a refused and a
    /// failed link, no file the output names is written, and each warning is
    /// printed. A map elsewhere is written, and a link that installs puts its
    /// image at the output. Without LLD or gold their legs are skipped
    /// (`SKIP:`).
    #[test]
    fn a_user_map_never_writes_the_file_the_output_names() {
        use std::os::unix::fs::symlink;
        let directory = tempfile::tempdir().unwrap();
        let dir = directory.path();
        copy_b1(dir);
        write_module(dir, "through.tmbc", &through_module());
        fs::write(dir.join("bt.c"), UNWIND_BT_SOURCE).unwrap();
        run_tool(dir, "cc", &["-c", "-O1", "-o", "bt.o", "bt.c"]);
        fs::write(
            dir.join("undef.c"),
            "extern int nosuch(void);\nint tcg_undef(void) { return nosuch(); }\n",
        )
        .unwrap();
        run_tool(dir, "cc", &["-c", "-o", "undef.o", "undef.c"]);
        let file = |name: &str| {
            let printed = Command::new("cc")
                .arg(format!("-print-file-name={name}"))
                .output()
                .unwrap();
            String::from_utf8(printed.stdout)
                .unwrap()
                .trim()
                .to_string()
        };
        // Refused through every linker: without a table the walk from
        // `crtbeginT.o`'s own CIE misses trust-cg's FDE (GNU ld, LLD), and
        // gold's map does not show where `crtbeginT.o` registers.
        let start_files = format!(
            "-Wl,{},{},{},bt.o,--start-group,-lgcc,-lgcc_eh,-lc,--end-group,{},{},\
             --no-eh-frame-hdr",
            file("crtbeginT.o"),
            file("crt1.o"),
            file("crti.o"),
            file("crtend.o"),
            file("crtn.o")
        );
        let link = |outcome: &str, map: &str| -> Vec<String> {
            let mut args: Vec<String> = ["-o", "prog", "b1_scalars.tmbc", "through.tmbc"]
                .iter()
                .map(|arg| arg.to_string())
                .collect();
            match outcome {
                "refused" => {
                    args.extend(["--static".into(), "--nostdlib".into(), start_files.clone()])
                }
                "failed" => args.push("-Wl,bt.o,undef.o".into()),
                _ => args.push("-Wl,bt.o".into()),
            }
            args.push(format!("-Wl,{map}"));
            args
        };
        let mut linkers: Vec<(&str, Option<PathBuf>)> = vec![("gnu", None)];
        linkers.extend(gold_cc(dir).map(|gold| ("gold", Some(gold))));
        linkers.extend(lld_dir().map(|lld| ("lld", Some(lld_cc(dir, &lld)))));
        let clear = |names: &[&str]| {
            for name in names {
                let _ = fs::remove_file(dir.join(name));
            }
        };
        let state = |name: &str| -> String {
            let path = dir.join(name);
            match fs::symlink_metadata(&path) {
                Ok(metadata) if metadata.is_symlink() => {
                    format!("-> {}", fs::read_link(&path).unwrap().display())
                }
                Ok(_) => {
                    let bytes = fs::read(&path).unwrap();
                    if bytes.starts_with(b"\x7fELF") {
                        "image".to_string()
                    } else {
                        String::from_utf8_lossy(&bytes[..bytes.len().min(9)]).into_owned()
                    }
                }
                Err(_) => "absent".to_string(),
            }
        };
        let warned = "trust-cg: warning: the link map the -Wl option";
        for (linker, bin) in &linkers {
            let bin = bin.as_deref();
            for outcome in ["refused", "failed", "installed"] {
                let ran = |map: &str| {
                    let result = trust_cg_on(
                        bin,
                        dir,
                        &link(outcome, map)
                            .iter()
                            .map(String::as_str)
                            .collect::<Vec<_>>(),
                    );
                    (result.status.success(), stderr(&result))
                };
                let what = |case: &str| format!("{linker} {outcome} {case}");
                // A map option before -M on the output's own file.
                // `-Mx` is a group of short options (`-M -x`), refused
                // before any process runs.
                clear(&["prog"]);
                fs::write(dir.join("prog"), b"precious\n").unwrap();
                let (installed, text) = ran("-Map=prog,-Mx");
                assert!(
                    !installed
                        && text.contains("[TCG-LINK-OPTION-GROUP] `-Mx`")
                        && state("prog") == "precious\n",
                    "{}: {text}",
                    what("-Map=prog,-Mx")
                );
                for map in [
                    "-Map=prog,-M",
                    "-Map=prog,--print-map",
                    "-Map=prog,-print-map",
                    "-Map=prog",
                ] {
                    clear(&["prog"]);
                    fs::write(dir.join("prog"), b"precious\n").unwrap();
                    let (installed, text) = ran(map);
                    let gold_or_last = *linker == "gold" || map == "-Map=prog";
                    let expected = if installed { "image" } else { "precious\n" };
                    assert_eq!(state("prog"), expected, "{}: {text}", what(map));
                    assert_eq!(
                        installed,
                        outcome == "installed" && gold_or_last,
                        "{}: {text}",
                        what(map)
                    );
                    // The map the linker would have written over the output
                    // is not, and the driver says so on every path.
                    if gold_or_last && (outcome != "failed" || *linker != "lld") {
                        assert!(text.contains(warned), "{}: {text}", what(map));
                    }
                }
                // Links, dangling or not, to the output's file, and paths
                // that name it otherwise.
                for (map, links) in [
                    ("-Map=maplink", &[("maplink", "prog")][..]),
                    (
                        "-Map=chain",
                        &[("chain", "maplink"), ("maplink", "prog")][..],
                    ),
                    ("-Map=symdir/prog", &[("symdir", ".")][..]),
                    ("-Map=./prog", &[][..]),
                    ("-Map,sub/../prog", &[][..]),
                ] {
                    clear(&["prog", "maplink", "chain", "symdir"]);
                    let _ = fs::create_dir(dir.join("sub"));
                    for (name, target) in links {
                        symlink(target, dir.join(name)).unwrap();
                    }
                    let (installed, text) = ran(map);
                    assert_eq!(installed, outcome == "installed", "{}: {text}", what(map));
                    let expected = if installed { "image" } else { "absent" };
                    assert_eq!(state("prog"), expected, "{}: {text}", what(map));
                    if outcome != "failed" || *linker != "lld" {
                        assert!(text.contains(warned), "{}: {text}", what(map));
                    }
                }
                clear(&["maplink", "chain", "symdir"]);
                // An output that is a link to an absent file, and the map on
                // that file.
                clear(&["prog", "target"]);
                symlink("target", dir.join("prog")).unwrap();
                let (installed, text) = ran("-Map=target");
                assert_eq!(state("target"), "absent", "{}: {text}", what("target"));
                let expected = if installed { "image" } else { "-> target" };
                assert_eq!(state("prog"), expected, "{}: {text}", what("target"));
                // A map elsewhere is written, as the linker writes it (LLD
                // writes one for a failed link only when it wrote its own).
                clear(&["prog", "user.map"]);
                let (_, text) = ran("-Map=user.map");
                let map = fs::read_to_string(dir.join("user.map")).unwrap_or_default();
                if !(outcome == "failed" && *linker == "lld") {
                    assert!(!map.is_empty(), "{}: {text}", what("user.map"));
                }
                clear(&["prog", "user.map"]);
            }
        }
        let _ = fs::remove_dir(dir.join("sub"));
    }

    /// The v5 verifier's map findings. When the output's directory and
    /// `TMPDIR` each held `,`, the driver had no map path of its own and gave
    /// the linker the user's `-Wl,-Map=prog`, which GNU ld, gold and LLD
    /// wrote over `prog`, the output of a refused link. The driver's map now
    /// goes to a fresh directory in `/tmp` when neither can hold it (with no
    /// path at all the link is refused before the linker runs,
    /// `[TCG-LINK-MAP-UNSTAGED]`, a unit row): through each linker a refused
    /// link leaves `prog` as it was and writes nothing in its directory or
    /// in `TMPDIR`, the warning that the map was not written is printed, a
    /// link that installs puts its image at `prog`, and a map elsewhere in
    /// that directory is written. And `-Wl,-Map=/dev/stdout` (or
    /// `/dev/fd/1`) into a pipe, which gold 2.42 and LLD 22 write, was
    /// refused as a map the driver could not write: through gold and LLD it
    /// is now written to the pipe, and GNU ld 2.42, which writes no map to a
    /// file that is not regular, links with a warning. Without LLD or gold
    /// their legs are skipped (`SKIP:`).
    #[test]
    fn a_map_is_staged_whatever_the_output_directory_and_written_to_a_pipe() {
        let directory = tempfile::tempdir().unwrap();
        let root = directory.path();
        let dir = root.join("a,b");
        let tmp = root.join("t,mp");
        fs::create_dir(&dir).unwrap();
        fs::create_dir(&tmp).unwrap();
        copy_b1(&dir);
        write_module(&dir, "through.tmbc", &through_module());
        fs::write(dir.join("bt.c"), UNWIND_BT_SOURCE).unwrap();
        run_tool(&dir, "cc", &["-c", "-O1", "-o", "bt.o", "bt.c"]);
        let file = |name: &str| {
            let printed = Command::new("cc")
                .arg(format!("-print-file-name={name}"))
                .output()
                .unwrap();
            String::from_utf8(printed.stdout)
                .unwrap()
                .trim()
                .to_string()
        };
        // Refused through every linker (see
        // `a_user_map_never_writes_the_file_the_output_names`).
        let start_files = format!(
            "-Wl,{},{},{},bt.o,--start-group,-lgcc,-lgcc_eh,-lc,--end-group,{},{},\
             --no-eh-frame-hdr",
            file("crtbeginT.o"),
            file("crt1.o"),
            file("crti.o"),
            file("crtend.o"),
            file("crtn.o")
        );
        let mut linkers: Vec<(&str, Option<PathBuf>)> = vec![("gnu", None)];
        linkers.extend(gold_cc(root).map(|gold| ("gold", Some(gold))));
        linkers.extend(lld_dir().map(|lld| ("lld", Some(lld_cc(root, &lld)))));
        let run = |bin: Option<&Path>, args: &[&str]| -> Output {
            let mut command = Command::new(env!("CARGO_BIN_EXE_trust-cg"));
            command.arg("--permit-unlicensed"); // Claim-less fixtures: refused by default since WS7.5 (DG-73).
            command.current_dir(&dir).args(args).env("TMPDIR", &tmp);
            if let Some(bin) = bin {
                let mut paths = vec![bin.to_path_buf()];
                paths.extend(std::env::split_paths(
                    &std::env::var_os("PATH").unwrap_or_default(),
                ));
                command.env("PATH", std::env::join_paths(paths).unwrap());
            }
            command.output().expect("run trust-cg")
        };
        let warned = "trust-cg: warning: the link map the -Wl option";
        for (linker, bin) in &linkers {
            let bin = bin.as_deref();
            for map in ["-Wl,-Map=prog", "-Wl,-Map,prog"] {
                let what = format!("{linker} {map}");
                fs::write(dir.join("prog"), b"precious\n").unwrap();
                let before = listing(&dir);
                let refused = run(
                    bin,
                    &[
                        "--static",
                        "--nostdlib",
                        "-o",
                        "prog",
                        "b1_scalars.tmbc",
                        "through.tmbc",
                        &start_files,
                        map,
                    ],
                );
                let text = stderr(&refused);
                assert!(
                    !refused.status.success()
                        && text.contains("was refused and not installed")
                        && text.contains(warned),
                    "{what}: {text}"
                );
                assert_eq!(fs::read(dir.join("prog")).unwrap(), b"precious\n", "{what}");
                assert_eq!(listing(&dir), before, "{what}");
                assert!(listing(&tmp).is_empty(), "{what}");
                let installed = run(
                    bin,
                    &[
                        "-o",
                        "prog",
                        "b1_scalars.tmbc",
                        "through.tmbc",
                        "-Wl,bt.o",
                        map,
                    ],
                );
                let text = stderr(&installed);
                assert!(
                    installed.status.success() && text.contains(warned),
                    "{what}: {text}"
                );
                assert!(
                    fs::read(dir.join("prog")).unwrap().starts_with(b"\x7fELF"),
                    "{what}"
                );
            }
            let mapped = run(
                bin,
                &[
                    "-o",
                    "prog",
                    "b1_scalars.tmbc",
                    "through.tmbc",
                    "-Wl,bt.o",
                    "-Wl,-Map=user.map",
                ],
            );
            assert!(mapped.status.success(), "{linker}: {}", stderr(&mapped));
            assert!(
                fs::metadata(dir.join("user.map")).unwrap().len() > 0,
                "{linker}"
            );
            fs::remove_file(dir.join("user.map")).unwrap();
            assert!(listing(&tmp).is_empty(), "{linker}");
            // A map into a pipe.
            for path in ["/dev/stdout", "/dev/fd/1"] {
                let what = format!("{linker} {path}");
                let map = format!("-Wl,-Map={path}");
                let piped = run(
                    bin,
                    &[
                        "-o",
                        "piped",
                        "b1_scalars.tmbc",
                        "through.tmbc",
                        "-Wl,bt.o",
                        &map,
                    ],
                );
                let text = stderr(&piped);
                assert!(piped.status.success(), "{what}: {text}");
                let written = String::from_utf8_lossy(&piped.stdout);
                if *linker == "gnu" {
                    assert!(
                        written.is_empty()
                            && text.contains(&format!("GNU ld 2.42 writes no map to {path}")),
                        "{what}: {text}"
                    );
                } else {
                    assert!(written.contains("bt.o"), "{what}: {written}");
                }
                fs::remove_file(dir.join("piped")).unwrap();
            }
        }
    }

    /// The ninth closure audit at `0996df987`: an in-section symbol
    /// assignment (`.ehx : { tcg_ehx_start = .; KEEP(*(.eh_frame)) }`) is
    /// enough to make LLD's map unable to place the `.eh_frame` pieces, and
    /// an image whose inputs register no frames then had them neither
    /// decoded nor refused. Through LLD, two `--no-pie` programs with that
    /// script, `.ehx` at 256 MiB, `.text` at `0xd0000000` and
    /// `-Wl,--no-eh-frame-hdr` were installed with every FDE truncated,
    /// their frames registered at run time by code the driver does not read:
    /// `libregd.so`, reached only as the input `libneed.so`'s `DT_NEEDED`,
    /// and `libregx.so`, which finds `__register_frame_info` through
    /// `dlsym`. Each is now refused as unproven with nothing written,
    /// whatever its inputs (any program can register its frames); so is its
    /// near layout with that script (a conservative refusal). The near twin whose script names the start
    /// outside the section (placed by the map) links, registers its frames
    /// and backtraces into `main`; its far layout is refused as a window.
    /// The same assignment in an output section still named `.eh_frame` is
    /// read whole: the far layout is refused as a window and the near one
    /// runs. LLD's own far program registers its truncated frames and does
    /// not backtrace into `main`. Without LLD the row is skipped (`SKIP:`).
    #[test]
    fn an_eh_frame_output_section_the_map_cannot_place_is_refused_whatever_the_inputs() {
        let directory = tempfile::tempdir().unwrap();
        let dir = directory.path();
        let Some(lld) = lld_dir().map(|lld| lld_cc(dir, &lld)) else {
            return;
        };
        copy_b1(dir);
        write_module(dir, "through.tmbc", &through_module());
        fs::write(dir.join("bt.c"), UNWIND_BT_SOURCE).unwrap();
        run_tool(dir, "cc", &["-c", "-O1", "-o", "bt.o", "bt.c"]);
        fs::write(dir.join("regd.c"), NEEDED_REGISTRATION_SOURCE).unwrap();
        fs::write(dir.join("regx.c"), DLSYM_REGISTRATION_SOURCE).unwrap();
        fs::write(dir.join("need.c"), "int tcg_need(void) { return 0; }\n").unwrap();
        run_tool(
            dir,
            "cc",
            &["-shared", "-fPIC", "-o", "libregd.so", "regd.c"],
        );
        run_tool(
            dir,
            "cc",
            &["-shared", "-fPIC", "-o", "libregx.so", "regx.c"],
        );
        let rpath = dir.display().to_string();
        // `libneed.so` finds `libregd.so` through its own run path: a
        // program's `DT_RUNPATH` does not reach its libraries' dependencies.
        run_tool(
            dir,
            "cc",
            &[
                "-shared",
                "-fPIC",
                "-o",
                "libneed.so",
                "need.c",
                "-Wl,--no-as-needed",
                "-L.",
                &format!("-Wl,-rpath,{rpath}"),
                "-lregd",
            ],
        );
        fs::write(dir.join("inside.ld"), RENAMED_WITH_START_INSIDE).unwrap();
        fs::write(dir.join("start.ld"), RENAMED_WITH_START).unwrap();
        fs::write(dir.join("named.ld"), NAMED_WITH_START_INSIDE).unwrap();
        let rpath_link = format!("-Wl,-rpath-link,{rpath}");
        let args = |output: &str, library: &str, script: &str, extra: &[&str]| -> Vec<String> {
            let mut args: Vec<String> = [
                "--no-pie",
                "-o",
                output,
                "--rpath",
                &rpath,
                "b1_scalars.tmbc",
                "through.tmbc",
                "-Wl,bt.o",
                &format!("-Wl,--no-as-needed,{library}"),
                &rpath_link,
                "-Wl,-E",
                &format!("-Wl,-T,{script}"),
                "-Wl,--no-eh-frame-hdr",
            ]
            .iter()
            .map(|arg| arg.to_string())
            .collect();
            args.extend(extra.iter().map(|arg| arg.to_string()));
            args
        };
        let unplaced = [
            "and any program can register them",
            "does not place them: LLD's map gives the addresses of the .eh_frame pieces in the \
             output section `.ehx` from the start of that section",
            "is not read whole as .eh_frame",
        ];
        for (route, library) in [("needed", "libneed.so"), ("dlsym", "libregx.so")] {
            for (output, extra) in [
                (format!("{route}_far"), vec![FAR_EHX]),
                (format!("{route}_near_inside"), vec![]),
            ] {
                refused_by_cli(
                    dir,
                    Some(&lld),
                    &args(&output, library, "inside.ld", &extra),
                    "[TCG-LINK-EH-FRAME-UNPROVEN]",
                    &unplaced,
                );
            }
            refused_by_cli(
                dir,
                Some(&lld),
                &args(
                    &format!("{route}_far_start"),
                    library,
                    "start.ld",
                    &[FAR_EHX],
                ),
                "[TCG-LINK-EH-FRAME-WINDOW]",
                &[" FDEs describe code outside executable memory"],
            );
            assert!(
                installed_by_cli(
                    dir,
                    Some(&lld),
                    &args(&format!("{route}_near"), library, "start.ld", &[])
                ),
                "{route}: the near program did not register its frames"
            );
        }
        // The assignment in an output section named `.eh_frame`.
        refused_by_cli(
            dir,
            Some(&lld),
            &args(
                "named_far",
                "libneed.so",
                "named.ld",
                &["-Wl,--section-start=.eh_frame=0x10000000,--section-start=.text=0xd0000000"],
            ),
            "[TCG-LINK-EH-FRAME-WINDOW]",
            &[" FDEs describe code outside executable memory"],
        );
        assert!(installed_by_cli(
            dir,
            Some(&lld),
            &args("named_near", "libneed.so", "named.ld", &[])
        ));
        // LLD outside the driver installs the far `DT_NEEDED` program, which
        // registers its truncated frames and does not backtrace into `main`.
        compile_bt_modules(dir);
        run_tool(
            dir,
            &lld.join("cc").display().to_string(),
            &[
                "-no-pie",
                "-o",
                "raw_needed",
                "b1_scalars.o",
                "through.o",
                "bt.o",
                "-Wl,--no-as-needed,libneed.so",
                &rpath_link,
                &format!("-Wl,-rpath,{rpath}"),
                "-Wl,-E",
                "-Wl,-T,inside.ld",
                "-Wl,--no-eh-frame-hdr",
                "-Wl,--section-start=.ehx=0x10000000",
                "-Wl,--section-start=.text=0xd0000000",
                "-Wl,-z,noexecstack",
            ],
        );
        let run = Command::new(dir.join("raw_needed")).output().unwrap();
        let text = String::from_utf8_lossy(&run.stdout).into_owned();
        eprintln!(
            "raw_needed, linked by LLD without the driver: {:?}, {text}",
            run.status
        );
        assert!(stderr(&run).contains("tcg-reg: registered"), "{run:?}");
        assert!(
            text.split_whitespace()
                .filter(|word| word.starts_with("pc="))
                .count()
                < 3,
            "{text}"
        );
    }

    /// The ninth closure audit's false refusals of `--static` links: an
    /// output whose name or directory holds `%` (the driver asked for no map,
    /// since GNU ld 2.42 replaces `%` in a `-Map` path) and an output name of
    /// 252 to 255 bytes (`<name>.map` exceeds the file-name limit) were
    /// refused as unproven. The map is now a fixed short name in the stage
    /// (or, when the output's directory holds `%`, in a directory of the
    /// system temporary directory). Through GNU ld 2.42 and gold 2.42 each
    /// such static link, and one to an output named `link.map`, is installed
    /// and backtraces through the trust-cg frame into `main`, with no
    /// staging directory left. LLD 22.1.6 writes an output through a
    /// temporary file whose name adds 11 bytes to the output's and whose
    /// `%` characters it replaces, so it cannot write an output whose name
    /// is longer than 244 bytes or whose directory holds `%`, inside or
    /// outside the driver; its other such links are installed and run.
    /// Without LLD or gold their legs are skipped (`SKIP:`).
    #[test]
    fn static_links_to_output_paths_holding_percent_or_long_names_are_installed() {
        let directory = tempfile::tempdir().unwrap();
        let dir = directory.path();
        copy_b1(dir);
        write_module(dir, "through.tmbc", &through_module());
        fs::write(dir.join("bt.c"), BT_SOURCE).unwrap();
        run_tool(dir, "cc", &["-c", "-O1", "-o", "bt.o", "bt.c"]);
        fs::create_dir(dir.join("pct%dir")).unwrap();
        let lld = lld_dir().map(|lld| lld_cc(dir, &lld));
        let gold = gold_cc(dir);
        let args = |output: &str| -> Vec<String> {
            [
                "--static",
                "-o",
                output,
                "b1_scalars.tmbc",
                "through.tmbc",
                "-Wl,bt.o",
            ]
            .iter()
            .map(|arg| arg.to_string())
            .collect()
        };
        let long = |length: usize| "n".repeat(length);
        let common = ["p%1".to_string(), "link.map".to_string()];
        type LinkerCases<'a> = (&'a str, Option<PathBuf>, Vec<String>, Vec<String>);
        let mut linkers: Vec<LinkerCases<'_>> = vec![(
            "gnu",
            None,
            [
                "pct%dir/prog".to_string(),
                long(252),
                long(255),
                format!("pct%dir/{}", long(255)),
            ]
            .into_iter()
            .chain(common.clone())
            .collect(),
            Vec::new(),
        )];
        if let Some(gold) = gold {
            linkers.push((
                "gold",
                Some(gold),
                ["pct%dir/prog".to_string(), long(252), long(255)]
                    .into_iter()
                    .chain(common.clone())
                    .collect(),
                Vec::new(),
            ));
        }
        if let Some(lld) = lld {
            linkers.push((
                "lld",
                Some(lld),
                [long(244)].into_iter().chain(common.clone()).collect(),
                vec!["pct%dir/prog".to_string(), long(245)],
            ));
        }
        if linkers.iter().any(|(_, _, _, limits)| !limits.is_empty()) {
            compile_bt_modules(dir);
        }
        for (linker, bin, installed, lld_limits) in &linkers {
            for output in installed {
                let registered = installed_by_cli(dir, bin.as_deref(), &args(output));
                assert!(!registered, "{linker} {output}");
            }
            for output in lld_limits {
                let result = trust_cg_on(
                    bin.as_deref(),
                    dir,
                    &args(output).iter().map(String::as_str).collect::<Vec<_>>(),
                );
                let text = stderr(&result);
                assert!(
                    !result.status.success()
                        && text.contains("cannot open output file")
                        && !text.contains("[TCG-LINK-"),
                    "{linker} {output}: {text}"
                );
                // The same link outside the driver fails the same way.
                let raw = Command::new(bin.as_ref().unwrap().join("cc"))
                    .current_dir(dir)
                    .args(["-static", "-o", output, "b1_scalars.o", "through.o", "bt.o"])
                    .output()
                    .unwrap();
                assert!(
                    !raw.status.success() && stderr(&raw).contains("cannot open output file"),
                    "{linker} {output}: {raw:?}"
                );
            }
        }
        for parent in [dir.to_path_buf(), dir.join("pct%dir")] {
            let left: Vec<String> = listing(&parent)
                .into_iter()
                .filter(|name| name.starts_with(".tcg-link"))
                .collect();
            assert!(left.is_empty(), "{left:?}");
        }
    }

    /// `_start` calls `main` and exits with what it returns.
    const NOSTDLIB_START: &str = "    .text\n    .globl _start\n_start:\n    bl main\n    mov x8, \
                                  #93\n    svc #0\n";

    /// `main` returns `isize_add_one(41)` (the b1 fixture): 42.
    const NOSTDLIB_MAIN: &str =
        "extern long isize_add_one(long);\nint main(void) { return (int)isize_add_one(41); }\n";

    /// The ninth closure audit's loader crash: LLD 22.1.6 writes a dynamic
    /// `-nostdlib --no-pie` executable that needs no shared library with a
    /// `PT_INTERP` and no `PT_DYNAMIC`, and glibc's loader faults on it
    /// (SIGSEGV in `audit_list_add_dynamic_tag`) before the program runs.
    /// Through the CLI that link is refused by name,
    /// `[TCG-LINK-INTERP-NO-DYNAMIC]`, with nothing written; LLD's own image
    /// dies with SIGSEGV. GNU ld 2.42 and gold 2.42 write no `PT_INTERP` for
    /// it, and their programs exit 42, as do the `--pie` and `--static`
    /// twins through all three linkers. Without LLD or gold their legs are
    /// skipped (`SKIP:`).
    #[test]
    fn a_dynamic_nostdlib_image_without_a_dynamic_section_is_refused() {
        let directory = tempfile::tempdir().unwrap();
        let dir = directory.path();
        copy_b1(dir);
        fs::write(dir.join("start.s"), NOSTDLIB_START).unwrap();
        fs::write(dir.join("main.c"), NOSTDLIB_MAIN).unwrap();
        run_tool(dir, "cc", &["-c", "-o", "start.o", "start.s"]);
        run_tool(dir, "cc", &["-c", "-O1", "-o", "main.o", "main.c"]);
        let lld = lld_dir().map(|lld| lld_cc(dir, &lld));
        let gold = gold_cc(dir);
        let segments = |program: &Path| {
            let output = Command::new("readelf")
                .args(["-lW"])
                .arg(program)
                .output()
                .unwrap();
            let text = String::from_utf8_lossy(&output.stdout).into_owned();
            (text.contains("INTERP"), text.contains("DYNAMIC"))
        };
        let mut linkers: Vec<(&str, Option<PathBuf>)> = vec![("gnu", None)];
        linkers.extend(gold.map(|gold| ("gold", Some(gold))));
        linkers.extend(lld.clone().map(|lld| ("lld", Some(lld))));
        for (linker, bin) in &linkers {
            for mode in ["--no-pie", "--pie", "--static"] {
                let output = format!("{linker}{mode}");
                let args: Vec<String> = [
                    mode,
                    "--nostdlib",
                    "-o",
                    &output,
                    "b1_scalars.tmbc",
                    "-Wl,start.o,main.o",
                ]
                .iter()
                .map(|arg| arg.to_string())
                .collect();
                if *linker == "lld" && mode == "--no-pie" {
                    refused_by_cli(
                        dir,
                        bin.as_deref(),
                        &args,
                        "[TCG-LINK-INTERP-NO-DYNAMIC]",
                        &["names a program interpreter (PT_INTERP) and has no dynamic section"],
                    );
                    continue;
                }
                let result = trust_cg_on(
                    bin.as_deref(),
                    dir,
                    &args.iter().map(String::as_str).collect::<Vec<_>>(),
                );
                assert!(result.status.success(), "{output}: {}", stderr(&result));
                let program = dir.join(&output);
                let (interp, dynamic) = segments(&program);
                assert!(!interp || dynamic, "{output}");
                assert_eq!(
                    Command::new(&program).status().unwrap().code(),
                    Some(42),
                    "{output}"
                );
            }
        }
        // LLD outside the driver: `PT_INTERP`, no `PT_DYNAMIC`, SIGSEGV.
        if let Some(lld) = &lld {
            let output = trust_cg_on(None, dir, &["-c", "-o", "b1_scalars.o", "b1_scalars.tmbc"]);
            assert!(output.status.success(), "{}", stderr(&output));
            run_tool(
                dir,
                &lld.join("cc").display().to_string(),
                &[
                    "-no-pie",
                    "-nostdlib",
                    "-o",
                    "raw_lld",
                    "start.o",
                    "main.o",
                    "b1_scalars.o",
                    "-Wl,-z,noexecstack",
                ],
            );
            assert_eq!(segments(&dir.join("raw_lld")), (true, false));
            let status = Command::new(dir.join("raw_lld")).status().unwrap();
            eprintln!("raw_lld, linked by LLD without the driver: {status:?}");
            assert_eq!(status.signal(), Some(SIGSEGV), "{status:?}");
        }
    }

    /// Run `command` to completion, its standard output and error written to
    /// files in `scratch`, and return what it printed and its peak resident
    /// set size in KiB: `ru_maxrss` of the `rusage` `wait4` gives for it,
    /// which on Linux is the larger of the child's own and that of every
    /// descendant it waited for (`RUSAGE_BOTH`), as GNU time's `%M` reads it.
    /// `wait4` is glibc's, which the test binary already links.
    fn peak_rss(command: &mut Command, scratch: &Path) -> (Output, u64) {
        use std::os::unix::process::ExitStatusExt;
        /// `struct rusage` on AArch64 Linux: two `timeval`s, then fourteen
        /// `long`s, the first `ru_maxrss`.
        #[repr(C)]
        struct Rusage([i64; 18]);
        unsafe extern "C" {
            fn wait4(pid: i32, status: *mut i32, options: i32, usage: *mut Rusage) -> i32;
        }
        let (out, err) = (scratch.join("stdout"), scratch.join("stderr"));
        let child = command
            .stdin(std::process::Stdio::null())
            .stdout(fs::File::create(&out).unwrap())
            .stderr(fs::File::create(&err).unwrap())
            .spawn()
            .unwrap();
        let pid = i32::try_from(child.id()).unwrap();
        let mut status = 0i32;
        let mut usage = Rusage([0; 18]);
        // SAFETY: `status` and `usage` are valid for writes of the sizes
        // `wait4` writes, and `pid` is this process's own unreaped child,
        // which `child` never waits for after this.
        let reaped = loop {
            let reaped = unsafe { wait4(pid, &mut status, 0, &mut usage) };
            if reaped != -1
                || std::io::Error::last_os_error().kind() != std::io::ErrorKind::Interrupted
            {
                break reaped;
            }
        };
        assert_eq!(reaped, pid, "wait4: {}", std::io::Error::last_os_error());
        drop(child);
        let output = Output {
            status: std::process::ExitStatus::from_raw(status),
            stdout: fs::read(&out).unwrap(),
            stderr: fs::read(&err).unwrap(),
        };
        (output, u64::try_from(usage.0[4]).unwrap())
    }

    /// A trust-cg thread-local `tcg_le_v` (local exec, `.tbss`) that
    /// `tcg_le_get` adds 42 to and returns: its access is an
    /// `R_AARCH64_TLSLE_ADD_TPREL_HI12`/`_LO12_NC` pair.
    const LE_IR: &str = "; TrustIr text format v1\nmodule \"tcg_le\"\n\nfuncty.0 = () -> \
        (u64)\n\nglobal tls(local_exec) mut align(8) @tcg_le_v u64 = 0\n\nfn \
        @tcg_le_get(functy.0) {\nbb0:\n    %0 = global_addr @global.0\n    %1 = load u64, ptr \
        %0\n    %2 = const u64 42\n    %3 = add u64 %1, %2\n    store u64 %3, ptr %0\n    ret \
        %3\n}\n";

    /// Calls `tcg_le_get` twice around a write to the C thread-local
    /// `pad_tls`; exits 0 when the trust-cg thread-local read 42 then 84.
    const LE_MAIN: &str = "#include <stdio.h>\nextern unsigned long tcg_le_get(void);\nextern \
        __thread unsigned char pad_tls[];\nint main(void) { unsigned long v = tcg_le_get(); \
        pad_tls[0] = 7; unsigned long w = tcg_le_get(); printf(\"v=%lu w=%lu\\n\", v, w); \
        return v == 42 && w == 84 ? 0 : 1; }\n";

    /// A `.tdata` thread-local `pad_tls` of `size` bytes, placed before the
    /// trust-cg one: at 16 MiB the trust-cg `TPREL` is past `2^24`.
    fn tdata_pad(size: u64) -> String {
        format!(
            "\t.section .tdata,\"awT\",%progbits\n\t.p2align 3\n\t.globl pad_tls\npad_tls:\n\t\
             .zero {size}\n"
        )
    }

    /// A trust-cg global `tcg_val` (42) in `.data` that `tcg_get` loads.
    const VAL_IR: &str = "; TrustIr text format v1\nmodule \"tcg_val\"\n\nfuncty.0 = () -> \
        (u64)\n\nglobal mut align(8) @tcg_val u64 = 42\n\nfn @tcg_get(functy.0) {\nbb0:\n    %0 = \
        global_addr @global.0\n    %1 = load u64, ptr %0\n    ret %1\n}\n";

    /// A C global in its own section `.ovl`; exits 0 when both values are
    /// right.
    const OVL_MAIN: &str = "#include <stdio.h>\nextern unsigned long tcg_get(void);\n\
        __attribute__((section(\".ovl\"), used)) unsigned long ovl = 7;\nint main(void) { \
        unsigned long v = tcg_get(); printf(\"tcg_val=%lu ovl=%lu\\n\", v, ovl); return v == 42 && \
        ovl == 7 ? 0 : 1; }\n";

    /// `main` returns 42 (the whole program: glibc's start files and
    /// libraries around it).
    const RET_IR: &str = "; TrustIr text format v1\nmodule \"ret42\"\n\nfuncty.0 = () -> \
        (i32)\n\nfn @main(functy.0) {\nbb0:\n    %0 = const i32 42\n    ret %0\n}\n";

    /// `tcg_ret42` returns 42.
    const RET42_IR: &str = "; TrustIr text format v1\nmodule \"tcg_ret42\"\n\nfuncty.0 = () -> \
        (i64)\n\nfn @tcg_ret42(functy.0) {\nbb0:\n    %0 = const i64 42\n    ret %0\n}\n";

    /// A static glibc `main` that calls `memcpy` (an IFUNC there) and returns
    /// `tcg_ret42()`.
    const IFUNC_MAIN: &str = "#include <string.h>\nextern long tcg_ret42(void);\nstatic char \
        src[64] = \"abcdefghijklmnopqrstuvwxyz0123456789\";\nstatic char dst[64];\nvolatile int \
        n = 40;\nint main(void) {\n  memcpy(dst, src, n);\n  return dst[0] == 'a' ? \
        (int)tcg_ret42() : 1;\n}\n";

    /// An entry point of the user's: calls `main`, then `exit_group`.
    const MY_ENTRY: &str = "\t.text\n\t.globl _mystart\n\t.type _mystart,%function\n_mystart:\n\t\
        mov x29, #0\n\tmov x30, #0\n\tbl main\n\tmov x8, #94\n\tsvc #0\n";

    /// A directory holding a `cc` that runs `cc` from `bin` (the host `cc`
    /// when `None`) with `extra` after the request's arguments: a linker
    /// option the driver never saw, for the image checks alone.
    fn appending_cc(dir: &Path, name: &str, bin: Option<&Path>, extra: &str) -> PathBuf {
        // The host `cc` by its path: the wrapper is first on `PATH`.
        let host_cc = || {
            std::env::var_os("PATH")
                .and_then(|paths| {
                    std::env::split_paths(&paths)
                        .map(|dir| dir.join("cc"))
                        .find(|cc| cc.is_file())
                })
                .expect("a host cc on PATH")
        };
        let base = bin
            .map_or_else(host_cc, |bin| bin.join("cc"))
            .display()
            .to_string();
        let wrapper = dir.join(name);
        fs::create_dir(&wrapper).unwrap();
        write_executable_script(
            &wrapper.join("cc"),
            &format!("#!/bin/sh\nexec '{base}' \"$@\" '{extra}'\n"),
        );
        wrapper
    }

    /// The linkers present: `("gnu", None)`, and LLD and gold `cc`
    /// directories when installed (`TCG_REQUIRE_LLD`, `TCG_REQUIRE_GOLD`).
    fn linkers(dir: &Path) -> Vec<(&'static str, Option<PathBuf>)> {
        let mut linkers = vec![("gnu", None)];
        if let Some(lld) = lld_dir() {
            linkers.push(("lld", Some(lld_cc(dir, &lld))));
        }
        if let Some(gold) = gold_cc(dir) {
            linkers.push(("gold", Some(gold)));
        }
        linkers
    }

    /// Run the CLI in `dir` with `bin` first on `PATH` and require a refusal
    /// with nothing written: `tag` in the output and each of `texts`.
    fn refused_with(dir: &Path, bin: Option<&Path>, args: &[&str], tag: &str, texts: &[&str]) {
        let output = args[args.iter().position(|arg| *arg == "-o").unwrap() + 1];
        let before = listing(dir);
        let result = trust_cg_on(bin, dir, args);
        let text = stderr(&result);
        assert!(!result.status.success(), "{output}: {text}");
        assert!(
            text.contains(tag) && texts.iter().all(|wanted| text.contains(wanted)),
            "{output}: {text}"
        );
        assert_eq!(listing(dir), before, "{output}");
        assert!(!dir.join(output).exists(), "{output}");
    }

    /// Run the CLI in `dir` with `bin` first on `PATH`, require the program
    /// installed, run it and return its exit code and standard output; the
    /// program is removed.
    fn installed_and_run(dir: &Path, bin: Option<&Path>, args: &[&str]) -> (Option<i32>, String) {
        let output = args[args.iter().position(|arg| *arg == "-o").unwrap() + 1];
        let result = trust_cg_on(bin, dir, args);
        assert!(result.status.success(), "{output}: {}", stderr(&result));
        let program = dir.join(output);
        let run = run_program(&program);
        fs::remove_file(&program).unwrap();
        run
    }

    /// trust-cg globals `tcg_val` (42, `.data`) and `tcg_z` (0, `.bss`),
    /// and their getters.
    const VAL2_IR: &str = "; TrustIr text format v1\nmodule \"tcg_val2\"\n\nfuncty.0 = () -> \
        (u64)\n\nglobal mut align(8) @tcg_val u64 = 42\nglobal mut align(8) @tcg_z u64 = 0\n\nfn \
        @tcg_get(functy.0) {\nbb0:\n    %0 = global_addr @global.0\n    %1 = load u64, ptr %0\n    \
        ret %1\n}\n\nfn @tcg_get_z(functy.0) {\nbb0:\n    %0 = global_addr @global.1\n    %1 = \
        load u64, ptr %0\n    ret %1\n}\n";

    /// A C `.ovl` word (7) and a 0x10700-byte `.pad` of 0x5a bytes, for the
    /// eleventh closure audit's `AT()` scripts.
    const PAD_SECTIONS: &str = "__attribute__((section(\".ovl\"), used)) unsigned long ovl = 7;\n\
        __attribute__((section(\".pad\"), used)) unsigned char pad[0x10700] = {[0 ... 0x106ff] = \
        0x5a};\n";

    /// `main` prints the trust-cg globals and `ovl`; exits 0 when they are 42,
    /// 0 and 7.
    const PAD_MAIN: &str = "#include <stdio.h>\nextern unsigned long tcg_get(void), \
        tcg_get_z(void);\nextern unsigned long ovl;\nint main(void) { unsigned long a = tcg_get(), \
        z = tcg_get_z(); printf(\"tcg_val=%#lx tcg_z=%#lx ovl=%lu\\n\", a, z, ovl); return a == 42 \
        && z == 0 && ovl == 7 ? 0 : 1; }\n";

    /// A `_start` without the C runtime: exits 0 when the trust-cg globals
    /// read 42 and 0, 90 when `tcg_val` reads the `.pad` bytes, 1 otherwise.
    const PAD_START: &str = "extern unsigned long tcg_get(void), tcg_get_z(void);\nvoid \
        _start(void) { unsigned long a = tcg_get(), z = tcg_get_z(); long code = (a == 42 && z == \
        0) ? 0 : (a == 0x5a5a5a5a5a5a5a5aUL ? 90 : 1);\n  register long x0 __asm__(\"x0\") = code; \
        register long x8 __asm__(\"x8\") = 93; __asm__ volatile(\"svc 0\" :: \"r\"(x0), \"r\"(x8)); \
        for (;;); }\n";

    /// The user of a library with the trust-cg globals: exits 0 when they
    /// read 42 and 0.
    const PAD_USER: &str = "#include <stdio.h>\nextern unsigned long tcg_get(void), \
        tcg_get_z(void);\nint main(void) { unsigned long a = tcg_get(), z = tcg_get_z(); \
        printf(\"tcg_val=%#lx tcg_z=%#lx\\n\", a, z); return a == 42 && z == 0 ? 0 : 1; }\n";

    /// The audit's script: `.ovl` at 0x500800 (the page of trust-cg's `.data`
    /// at 0x500000 and `.bss` at 0x500400) with its load address after a
    /// `.pad` at 0x600000, so both linkers write its `PT_LOAD` after `.pad`'s
    /// and map the page from another file page.
    const OVL_AT: &str = "SECTIONS { .pad 0x600000 : AT(0x700000) { KEEP(*(.pad)) } .ovl 0x500800 \
        : AT(0x800000) { KEEP(*(.ovl)) } } INSERT AFTER .bss;\n";

    /// The audit's next-page twin: `.ovl` at 0x501000, apart from `.data`
    /// with 4 KiB pages, in its 64 KiB page, and still after `.pad`.
    const OVL_NEXT_PAGE: &str = "SECTIONS { .pad 0x600000 : AT(0x700000) { KEEP(*(.pad)) } .ovl \
        0x501000 : AT(0x800000) { KEEP(*(.ovl)) } } INSERT AFTER .bss;\n";

    /// The next-64 KiB-page twin: `.ovl` at 0x510000, before `.pad` in
    /// address and load order.
    const OVL_NEXT_64K: &str = "SECTIONS { .ovl 0x510000 : AT(0x700000) { KEEP(*(.ovl)) } .pad \
        0x600000 : AT(0x800000) { KEEP(*(.pad)) } } INSERT AFTER .bss;\n";

    /// Where the audit put trust-cg's `.data` and `.bss`.
    const DATA_BSS_START: &str = "--section-start=.data=0x500000,--section-start=.bss=0x500400";

    /// A `_start` that exits 0 when `rz`, a read-only zero-fill section of
    /// eight words after file bytes in one read-only `PT_LOAD`, reads zero,
    /// 2 when it does not, and 1 when `tcg_get` does not return 42.
    const RODATA_ZERO_FILL: &str = "\t.text\n\t.globl _start\n\t.type _start, %function\n_start:\n\t\
        bl tcg_get\n\tcmp x0, #42\n\tb.ne 2f\n\tadrp x2, rz\n\tadd x2, x2, :lo12:rz\n\tmov x3, \
        #0\n\tmov x4, #8\n1:\tldr x5, [x2], #8\n\torr x3, x3, x5\n\tsubs x4, x4, #1\n\tb.ne 1b\n\t\
        cbnz x3, 3f\n\tmov x0, #0\n\tb 4f\n2:\tmov x0, #1\n\tb 4f\n3:\tmov x0, #2\n4:\tmov x8, \
        #93\n\tsvc #0\n\t.section .rodata.rz,\"a\",%progbits\n\t.p2align 3\n\t.xword 7\n\t.section \
        .rbss,\"a\",%nobits\n\t.p2align 3\n\t.globl rz\nrz:\t.zero 64\n";

    /// Places [`RODATA_ZERO_FILL`]'s sections in a read-only segment of
    /// their own.
    const RZ_SCRIPT: &str = "SECTIONS { .rz 0x700000 : { KEEP(*(.rodata.rz)) } .rbss : { KEEP(*(.rbss)) } } INSERT \
         AFTER .bss;\n";

    /// Run the CLI in `dir` with `bin` first on `PATH` over an output that
    /// holds sentinel bytes, and require a refusal that leaves them: `tag`
    /// in the output and each of `texts`, the directory listing unchanged.
    fn refused_leaving_output(
        dir: &Path,
        bin: Option<&Path>,
        args: &[&str],
        tag: &str,
        texts: &[&str],
    ) {
        let output = args[args.iter().position(|arg| *arg == "-o").unwrap() + 1];
        let sentinel = format!("sentinel {output}\n");
        fs::write(dir.join(output), &sentinel).unwrap();
        let before = listing(dir);
        let result = trust_cg_on(bin, dir, args);
        let text = stderr(&result);
        assert!(!result.status.success(), "{output}: {text}");
        assert!(
            text.contains(tag) && texts.iter().all(|wanted| text.contains(wanted)),
            "{output}: {text}"
        );
        assert_eq!(listing(dir), before, "{output}");
        assert_eq!(fs::read_to_string(dir.join(output)).unwrap(), sentinel);
        fs::remove_file(dir.join(output)).unwrap();
    }

    /// The eleventh closure audit's page-granular finding: an admitted
    /// linker script with `AT()` load addresses made GNU ld 2.42 and LLD
    /// 22.1.6 write a `PT_LOAD` for a C section at 0x500800 after one for a
    /// 0x10700-byte `.pad`, so the loader mapped the page of trust-cg's
    /// `.data` and `.bss` (0x500000) from a file page inside `.pad`, and the
    /// driver installed programs (no-PIE, PIE, static `-nostdlib`) and a
    /// shared library whose trust-cg globals read 0x5a5a5a5a5a5a5a5a. Each
    /// is refused now by the page model of the loaded-bytes check
    /// (`[TCG-LINK-LOADED-BYTES]`, segments out of order), with the output's
    /// bytes left as they were; the audit's next-page twin (0x501000, the
    /// same 64 KiB page, its `p_align`) is refused too, and the next-64
    /// KiB-page twin is installed in every form and reads 42 and 0. The
    /// raw audit image outside the driver reads the `.pad` bytes. Script-free
    /// members of the class, through all three linkers: `-z
    /// max-page-size=16` (p_vaddr - p_offset not a multiple of the page;
    /// SIGSEGV outside the driver) and LLD's `-n` (an executable and a
    /// writable segment in one page; SIGSEGV) are refused, GNU ld's `-n` and
    /// every linker's `-N` (one segment) are installed and run. A read-only
    /// zero-fill section after file bytes in a read-only `PT_LOAD`, which
    /// the kernel does not clear, is refused (it read the `.symtab` bytes
    /// after it outside the driver) and its writable twin runs.
    #[test]
    fn pages_the_loaders_map_from_other_file_bytes_are_never_installed() {
        let directory = tempfile::tempdir().unwrap();
        let dir = directory.path();
        for (name, text) in [
            ("val2.trust_ir", VAL2_IR),
            ("pad.c", PAD_SECTIONS),
            ("padmain.c", PAD_MAIN),
            ("padstart.c", PAD_START),
            ("paduser.c", PAD_USER),
            ("at.ld", OVL_AT),
            ("next.ld", OVL_NEXT_PAGE),
            ("next64k.ld", OVL_NEXT_64K),
            ("rz.s", RODATA_ZERO_FILL),
            ("rz.ld", RZ_SCRIPT),
        ] {
            fs::write(dir.join(name), text).unwrap();
        }
        fs::write(
            dir.join("rzw.s"),
            RODATA_ZERO_FILL.replace(".rbss,\"a\",%nobits", ".rbss,\"aw\",%nobits"),
        )
        .unwrap();
        run_tool(dir, "cc", &["-c", "-O1", "-fpic", "-o", "pad.o", "pad.c"]);
        run_tool(dir, "cc", &["-c", "-O1", "-o", "padmain.o", "padmain.c"]);
        run_tool(dir, "ld", &["-r", "-o", "padprog.o", "padmain.o", "pad.o"]);
        run_tool(
            dir,
            "cc",
            &[
                "-c",
                "-O1",
                "-fno-pic",
                "-ffreestanding",
                "-o",
                "padstart.o",
                "padstart.c",
            ],
        );
        run_tool(
            dir,
            "ld",
            &["-r", "-o", "padstatic.o", "padstart.o", "pad.o"],
        );
        run_tool(dir, "cc", &["-c", "-O1", "-o", "paduser.o", "paduser.c"]);
        run_tool(dir, "cc", &["-c", "-o", "rz.o", "rz.s"]);
        run_tool(dir, "cc", &["-c", "-o", "rzw.o", "rzw.s"]);
        let object = trust_cg_on(
            None,
            dir,
            &["--format=text", "-c", "-o", "val2.o", "val2.trust_ir"],
        );
        assert!(object.status.success(), "{}", stderr(&object));
        let with =
            |objects: &str, script: &str| format!("-Wl,{objects},-T,{script},{DATA_BSS_START}");
        for (linker, bin) in linkers(dir) {
            let bin = bin.as_deref();
            let cc = bin.map_or_else(
                || "cc".to_string(),
                |bin| bin.join("cc").display().to_string(),
            );
            if linker != "gold" {
                // The audit's image outside the driver reads the `.pad` bytes.
                let raw = format!("raw_{linker}");
                run_tool(
                    dir,
                    &cc,
                    &[
                        "-no-pie",
                        "-o",
                        &raw,
                        "padprog.o",
                        "val2.o",
                        "-Wl,-T,at.ld",
                        &format!("-Wl,{DATA_BSS_START}"),
                    ],
                );
                let (code, stdout) = run_program(&dir.join(&raw));
                assert_eq!(
                    (code, stdout.as_str()),
                    (
                        Some(1),
                        "tcg_val=0x5a5a5a5a5a5a5a5a tcg_z=0x5a5a5a5a5a5a5a5a ovl=7\n"
                    ),
                    "{linker}"
                );
                // An `ET_EXEC` whose out-of-order `.ovl` shares the page of
                // `.data`; a PIE or shared object out of order.
                let shared_page = "share the 0x10000-byte page at 0x500000, and its program \
                                   headers are not in ascending p_vaddr order";
                for (script, address) in [("at.ld", "0x500800"), ("next.ld", "0x501000")] {
                    let program = with("padprog.o", script);
                    let follows = format!("its PT_LOAD segment at [{address}, ");
                    let refused_as = |name: &str, extra: &[&str], group: &str, texts: &[&str]| {
                        let mut args = vec!["--format=text"];
                        args.extend(extra);
                        args.extend(["-o", name, "val2.trust_ir", group]);
                        refused_leaving_output(dir, bin, &args, "[TCG-LINK-LOADED-BYTES]", texts);
                    };
                    refused_as(
                        &format!("np_{linker}"),
                        &["--no-pie"],
                        &program,
                        &[shared_page],
                    );
                    refused_as(
                        &format!("pie_{linker}"),
                        &[],
                        &program,
                        &[&follows, "in the program headers"],
                    );
                    refused_as(
                        &format!("st_{linker}"),
                        &["--static", "--nostdlib"],
                        &with("padstatic.o", script),
                        &[shared_page],
                    );
                    refused_as(
                        &format!("libat_{linker}.so"),
                        &["--shared", "--relocation-model", "pic"],
                        &with("pad.o", script),
                        &[&follows, "in the program headers"],
                    );
                }
                // The next-64 KiB-page twin runs in every form.
                let twin = with("padprog.o", "next64k.ld");
                for (name, extra) in [
                    (format!("np64_{linker}"), &["--no-pie"][..]),
                    (format!("pie64_{linker}"), &[]),
                ] {
                    let mut args = vec!["--format=text"];
                    args.extend(extra);
                    args.extend(["-o", name.as_str(), "val2.trust_ir", twin.as_str()]);
                    assert_eq!(
                        installed_and_run(dir, bin, &args),
                        (Some(0), "tcg_val=0x2a tcg_z=0 ovl=7\n".to_string()),
                        "{name}"
                    );
                }
                let static_twin = with("padstatic.o", "next64k.ld");
                let name = format!("st64_{linker}");
                assert_eq!(
                    installed_and_run(
                        dir,
                        bin,
                        &[
                            "--format=text",
                            "--static",
                            "--nostdlib",
                            "-o",
                            &name,
                            "val2.trust_ir",
                            &static_twin,
                        ],
                    )
                    .0,
                    Some(0),
                    "{name}"
                );
                let library = format!("lib64{linker}.so");
                let shared_twin = with("pad.o", "next64k.ld");
                let result = trust_cg_on(
                    bin,
                    dir,
                    &[
                        "--format=text",
                        "--shared",
                        "--relocation-model",
                        "pic",
                        "-o",
                        &library,
                        "val2.trust_ir",
                        &shared_twin,
                    ],
                );
                assert!(result.status.success(), "{library}: {}", stderr(&result));
                let user = format!("user64_{linker}");
                run_tool(
                    dir,
                    &cc,
                    &[
                        "-o",
                        &user,
                        "paduser.o",
                        &library,
                        &format!("-Wl,-rpath,{}", dir.display()),
                    ],
                );
                assert_eq!(
                    run_program(&dir.join(&user)),
                    (Some(0), "tcg_val=0x2a tcg_z=0\n".to_string()),
                    "{user}"
                );
            }
            // `-z max-page-size=16`: the writable segment's p_vaddr - p_offset
            // is not a multiple of the page.
            let name = format!("mp16_{linker}");
            refused_leaving_output(
                dir,
                bin,
                &[
                    "--format=text",
                    "--static",
                    "--nostdlib",
                    "-o",
                    &name,
                    "val2.trust_ir",
                    "-Wl,padstart.o,-z,max-page-size=16,-z,common-page-size=16",
                ],
                "[TCG-LINK-LOADED-BYTES]",
                &["is not a multiple of the 0x1000-byte page"],
            );
            let raw = format!("mp16_raw_{linker}");
            run_tool(
                dir,
                &cc,
                &[
                    "-static",
                    "-nostdlib",
                    "-o",
                    &raw,
                    "padstart.o",
                    "val2.o",
                    "-Wl,-z,max-page-size=16,-z,common-page-size=16,-z,noexecstack",
                ],
            );
            let status = Command::new(dir.join(&raw)).status().unwrap();
            assert_eq!(status.signal(), Some(SIGSEGV), "{raw}: {status:?}");
            // `-n` (nmagic) and `-N` (omagic).
            let nmagic = format!("nmagic_{linker}");
            let args = [
                "--format=text",
                "--static",
                "--nostdlib",
                "-o",
                &nmagic,
                "val2.trust_ir",
                "-Wl,padstart.o,-n",
            ];
            match linker {
                "lld" => {
                    refused_leaving_output(
                        dir,
                        bin,
                        &args,
                        "[TCG-LINK-LOADED-BYTES]",
                        &["which lack the earlier segment's `E`"],
                    );
                    let raw = "nmagic_raw_lld";
                    run_tool(
                        dir,
                        &cc,
                        &[
                            "-static",
                            "-nostdlib",
                            "-o",
                            raw,
                            "padstart.o",
                            "val2.o",
                            "-Wl,-n,-z,noexecstack",
                        ],
                    );
                    let status = Command::new(dir.join(raw)).status().unwrap();
                    assert_eq!(status.signal(), Some(SIGSEGV), "{raw}: {status:?}");
                }
                "gnu" => assert_eq!(installed_and_run(dir, bin, &args).0, Some(0), "{nmagic}"),
                // gold refuses a relocation of the `-n` layout itself.
                _ => {}
            }
            let omagic = format!("omagic_{linker}");
            assert_eq!(
                installed_and_run(
                    dir,
                    bin,
                    &[
                        "--format=text",
                        "--static",
                        "--nostdlib",
                        "-o",
                        &omagic,
                        "val2.trust_ir",
                        "-Wl,padstart.o,-N",
                    ],
                )
                .0,
                Some(0),
                "{omagic}"
            );
            if linker == "gold" {
                // gold rejects the `INSERT` scripts.
                continue;
            }
            // A read-only zero fill the kernel does not clear.
            let name = format!("rz_{linker}");
            refused_leaving_output(
                dir,
                bin,
                &[
                    "--format=text",
                    "--static",
                    "--nostdlib",
                    "-o",
                    &name,
                    "val2.trust_ir",
                    "-Wl,rz.o,-T,rz.ld",
                ],
                "[TCG-LINK-LOADED-BYTES]",
                &["is not writable, and the kernel does not clear its zero fill from 0x700008"],
            );
            let raw = format!("rz_raw_{linker}");
            run_tool(
                dir,
                &cc,
                &[
                    "-static",
                    "-nostdlib",
                    "-o",
                    &raw,
                    "rz.o",
                    "val2.o",
                    "-Wl,-T,rz.ld,-z,noexecstack",
                ],
            );
            assert_eq!(run_program(&dir.join(&raw)).0, Some(2), "{raw}");
            let name = format!("rzw_{linker}");
            assert_eq!(
                installed_and_run(
                    dir,
                    bin,
                    &[
                        "--format=text",
                        "--static",
                        "--nostdlib",
                        "-o",
                        &name,
                        "val2.trust_ir",
                        "-Wl,rzw.o,-T,rz.ld",
                    ],
                )
                .0,
                Some(0),
                "{name}"
            );
        }
    }

    /// A `_start` without the C runtime: exits 0 when the trust-cg globals
    /// read 42 and 0, 50 when `tcg_val` reads 0, 60 when `tcg_z` reads
    /// another value, 1 otherwise.
    const VAL_START: &str = "extern unsigned long tcg_get(void), tcg_get_z(void);\nvoid \
        _start(void) { unsigned long a = tcg_get(), z = tcg_get_z(); long code = (a == 42 && z == \
        0) ? 0 : (a == 0 ? 50 : (a == 42 ? 60 : 1));\n  register long x0 __asm__(\"x0\") = code; \
        register long x8 __asm__(\"x8\") = 93; __asm__ volatile(\"svc 0\" :: \"r\"(x0), \"r\"(x8)); \
        for (;;); }\n";

    /// A `_start` without the C runtime that reads only `tcg_z`: exits 0 when
    /// it reads 0, 42 when it reads 42, 1 otherwise.
    const ZERO_START: &str = "extern unsigned long tcg_get_z(void);\nvoid _start(void) { unsigned \
        long z = tcg_get_z(); long code = z == 0 ? 0 : (z == 42 ? 42 : 1);\n  register long x0 \
        __asm__(\"x0\") = code; register long x8 __asm__(\"x8\") = 93; __asm__ volatile(\"svc 0\" \
        :: \"r\"(x0), \"r\"(x8)); for (;;); }\n";

    /// `tcg_bump` adds 1 to the trust-cg global `tcg_val` (42) and returns it.
    const BUMP_IR: &str = "; TrustIr text format v1\nmodule \"tcg_wv\"\n\nfuncty.0 = () -> (u64)\n\n\
        global mut align(8) @tcg_val u64 = 42\n\nfn @tcg_bump(functy.0) {\nbb0:\n    %0 = \
        global_addr @global.0\n    %1 = load u64, ptr %0\n    %2 = const u64 1\n    %3 = add u64 \
        %1, %2\n    store u64 %3, ptr %0\n    ret %3\n}\n";

    /// An immutable trust-cg table `tcg_tab` that holds `tcg_get`'s address
    /// (a relocated pointer: trust-cg's `.data.rel.ro`), and `tcg_call`,
    /// which calls through it and returns `tcg_val` (42).
    const TABLE_IR: &str = "; TrustIr text format v1\nmodule \"tcg_tab\"\n\nfuncty.0 = () -> \
        (u64)\n\nglobal mut align(8) @tcg_val u64 = 42\nglobal @tcg_tab ptr = \
        symaddr<tcg_get>\n\nfn @tcg_get(functy.0) {\nbb0:\n    %0 = global_addr @global.0\n    \
        %1 = load u64, ptr %0\n    ret %1\n}\n\nfn @tcg_call(functy.0) {\nbb0:\n    %0 = \
        global_addr @global.1\n    %1 = load ptr, ptr %0\n    %2 = call_indirect \
        %1(functy.0)()\n    ret %2\n}\n";

    /// `main` calls through [`TABLE_IR`]'s table: exits 0 when it returns 42.
    const TABLE_MAIN: &str = "#include <stdio.h>\nextern unsigned long tcg_call(void);\nint \
        main(void) { unsigned long v = tcg_call(); printf(\"v=%lu\\n\", v); return v == 42 ? 0 : \
        1; }\n";

    /// `main` stores through `tcg_bump`: exits 0 when it returns 43.
    const BUMP_MAIN: &str = "#include <stdio.h>\nextern unsigned long tcg_bump(void);\nint \
        main(void) { unsigned long v = tcg_bump(); printf(\"v=%lu\\n\", v); return v == 43 ? 0 : \
        1; }\n";

    /// A `_start` without the C runtime that stores through `tcg_bump`:
    /// exits 0 when it returns 43.
    const BUMP_START: &str = "extern unsigned long tcg_bump(void);\nvoid _start(void) { unsigned \
        long v = tcg_bump();\n  register long x0 __asm__(\"x0\") = v == 43 ? 0 : 1; register long \
        x8 __asm__(\"x8\") = 93; __asm__ volatile(\"svc 0\" :: \"r\"(x0), \"r\"(x8)); for (;;); }\n";

    /// The C sections of the twelfth round's scripts: `.zz` (no file bytes),
    /// `.dd` and `.late` (file bytes), `.rr` (read-only), `.cdata` (four
    /// words that are not zero) and an empty `.mark`.
    const ROUND12_SECTIONS: [(&str, &str); 6] = [
        (
            "zz.c",
            "__attribute__((section(\".zz\"), used)) unsigned long zz[16];\n",
        ),
        (
            "dd.c",
            "__attribute__((section(\".dd\"), used)) unsigned long dd = 5;\n",
        ),
        (
            "late.c",
            "__attribute__((section(\".late\"), used)) unsigned long late = 3;\n",
        ),
        (
            "cdata.c",
            "__attribute__((section(\".cdata\"), used)) unsigned long cdata[4] = {0x1111, 0x2222, \
             0x3333, 0x4444};\n",
        ),
        (
            "rr.s",
            "\t.section .rr,\"a\",%progbits\n\t.p2align 3\n\t.xword 9\n",
        ),
        (
            "mark.s",
            "\t.section .mark,\"a\",%progbits\n\t.globl tcg_mark\ntcg_mark:\n",
        ),
    ];

    /// The twelfth round's linker scripts (`INSERT` scripts beside
    /// [`DATA_BSS_START`], and `PHDRS` scripts).
    const ROUND12_SCRIPTS: [(&str, &str); 11] = [
        // trust-cg's `.data` in no segment, in a gap of the data segment.
        (
            "gap.ld",
            "ENTRY(_start)\nPHDRS { text PT_LOAD FILEHDR PHDRS; data PT_LOAD; }\nSECTIONS {\n  . = \
             0x400000 + SIZEOF_HEADERS;\n  .text : { *(.text*) } :text\n  .rodata : { \
             *(.rodata*) } :text\n  . = 0x500000;\n  .cdata : { *(.cdata) } :data\n  .data \
             0x500030 : { *(.data*) } :NONE\n  .late 0x500040 : { *(.late) } :data\n}\n",
        ),
        // trust-cg's `.data` in a read-only segment.
        (
            "readonly.ld",
            "ENTRY(_start)\nPHDRS { text PT_LOAD FILEHDR PHDRS FLAGS(5); data PT_LOAD FLAGS(4); \
             }\nSECTIONS {\n  . = 0x400000 + SIZEOF_HEADERS;\n  .text : { *(.text*) } :text\n  \
             .rodata : { *(.rodata*) } :text\n  .eh_frame : { KEEP(*(.eh_frame)) } :text\n  . = \
             0x500000;\n  .data : { *(.data*) } :data\n  .bss : { *(.bss*) *(COMMON) } :data\n}\n",
        ),
        // `.zz` without file bytes in the 4 KiB page of trust-cg's `.data`,
        // `.dd` later in its 64 KiB page.
        (
            "zzdd.ld",
            "SECTIONS { .zz 0x500800 (NOLOAD) : AT(0x900000) { KEEP(*(.zz)) } .dd 0x502000 : \
             AT(0xa00000) { KEEP(*(.dd)) } } INSERT AFTER .bss;\n",
        ),
        // Its twin: `.zz` after `.dd`, in the next 64 KiB page.
        (
            "twin.ld",
            "SECTIONS { .dd 0x502000 : AT(0x900000) { KEEP(*(.dd)) } .zz 0x510800 (NOLOAD) : \
             AT(0xa00000) { KEEP(*(.zz)) } } INSERT AFTER .bss;\n",
        ),
        // A read-only `.rr` in the 4 KiB page of `.data`, `.dd` later.
        (
            "rrdd.ld",
            "SECTIONS { .rr 0x500800 : AT(0x900000) { KEEP(*(.rr)) } .dd 0x502000 : AT(0xa00000) \
             { KEEP(*(.dd)) } } INSERT AFTER .bss;\n",
        ),
        // trust-cg's `.data` in no segment, after `.bss` in the data page.
        (
            "none.ld",
            "ENTRY(_start)\nPHDRS { text PT_LOAD FILEHDR PHDRS; data PT_LOAD; }\nSECTIONS {\n  . = \
             0x400000 + SIZEOF_HEADERS;\n  .text : { *(.text*) } :text\n  .rodata : { \
             *(.rodata*) } :text\n  . = 0x500000;\n  .cdata : { *(.cdata) } :data\n  .bss : { \
             *(.bss*) *(COMMON) } :data\n  .data : { *(.data*) } :NONE\n}\n",
        ),
        // The same in a shared object.
        (
            "noneshared.ld",
            "PHDRS { text PT_LOAD FILEHDR PHDRS; data PT_LOAD; dyn PT_DYNAMIC; }\nSECTIONS {\n  . \
             = SIZEOF_HEADERS;\n  .hash : { *(.hash) } :text\n  .gnu.hash : { *(.gnu.hash) } \
             :text\n  .dynsym : { *(.dynsym) } :text\n  .dynstr : { *(.dynstr) } :text\n  \
             .gnu.version : { *(.gnu.version) } :text\n  .gnu.version_r : { *(.gnu.version_r) } \
             :text\n  .rela.dyn : { *(.rela.dyn) *(.rela.*) } :text\n  .text : { *(.text*) } \
             :text\n  .eh_frame : { KEEP(*(.eh_frame)) } :text\n  . = ALIGN(0x10000);\n  \
             .dynamic : { *(.dynamic) } :data :dyn\n  .got : { *(.got) *(.got.plt) } :data\n  \
             .cdata : { *(.cdata) } :data\n  .bss : { *(.bss*) *(COMMON) } :data\n  .data : { \
             *(.data*) } :NONE\n}\n",
        ),
        // trust-cg's `.bss` between two sections of the data segment, and
        // `.data` in no segment (LLD gives it the file offset under `.bss`).
        (
            "nobits.ld",
            "ENTRY(_start)\nPHDRS { text PT_LOAD FILEHDR PHDRS; data PT_LOAD; }\nSECTIONS {\n  . = \
             0x400000 + SIZEOF_HEADERS;\n  .text : { *(.text*) } :text\n  .rodata : { \
             *(.rodata*) } :text\n  . = 0x500000;\n  .cdata : { *(.cdata) } :data\n  .bss : { \
             *(.bss*) *(COMMON) } :data\n  .data 0x600000 : { *(.data*) } :NONE\n  .late \
             0x500040 : { *(.late) } :data\n}\n",
        ),
        // `.cdata` in no segment (LLD gives it the file offset under
        // `.bss`), and a later segment in the page of `.data`.
        (
            "fill.ld",
            "ENTRY(_start)\nPHDRS { text PT_LOAD FILEHDR PHDRS; data PT_LOAD; late PT_LOAD; \
             }\nSECTIONS {\n  . = 0x400000 + SIZEOF_HEADERS;\n  .text : { *(.text*) } :text\n  \
             .rodata : { *(.rodata*) } :text\n  .eh_frame : { KEEP(*(.eh_frame)) } :text\n  . = \
             0x500000;\n  .data : { *(.data*) } :data\n  .bss : { *(.bss*) *(COMMON) } :data\n  \
             .cdata 0x600010 : { *(.cdata) } :NONE\n  .late 0x500800 : { KEEP(*(.late)) } \
             :late\n}\n",
        ),
        // An empty read-only `PT_LOAD` in the page of `.data`.
        (
            "empty.ld",
            "ENTRY(_start)\nPHDRS { text PT_LOAD FILEHDR PHDRS; data PT_LOAD; empty PT_LOAD \
             FLAGS(4); }\nSECTIONS {\n  . = 0x400000 + SIZEOF_HEADERS;\n  .note.gnu.build-id : { \
             *(.note.gnu.build-id) } :text\n  .text : { *(.text*) } :text\n  .rodata : { \
             *(.rodata*) } :text\n  .eh_frame : { KEEP(*(.eh_frame)) } :text\n  . = 0x500000;\n  \
             .data : { *(.data*) } :data\n  .bss : { *(.bss*) *(COMMON) } :data\n  .mark : { \
             KEEP(*(.mark)) } :empty\n}\n",
        ),
        // A PIE whose data page ends with a read-only segment and an empty
        // writable one.
        (
            "tail.ld",
            "ENTRY(_start)\nPHDRS { headers PT_PHDR PHDRS; interp PT_INTERP; text PT_LOAD FILEHDR \
             PHDRS; data PT_LOAD; rr PT_LOAD FLAGS(4); tail PT_LOAD FLAGS(6); dyn PT_DYNAMIC; \
             }\nSECTIONS {\n  . = SIZEOF_HEADERS;\n  .interp : { *(.interp) } :text :interp\n  \
             .note.gnu.build-id : { *(.note.gnu.build-id) } :text\n  .dynsym : { *(.dynsym) } \
             :text\n  .dynstr : { *(.dynstr) } :text\n  .gnu.hash : { *(.gnu.hash) } :text\n  \
             .hash : { *(.hash) } :text\n  .gnu.version : { *(.gnu.version) } :text\n  \
             .gnu.version_r : { *(.gnu.version_r) } :text\n  .rela.dyn : { *(.rela.*) } :text\n  \
             .text : { *(.text*) } :text\n  .rodata : { *(.rodata*) } :text\n  .eh_frame : { \
             KEEP(*(.eh_frame)) } :text\n  . = 0x100000;\n  .dynamic : { *(.dynamic) } :data \
             :dyn\n  .got : { *(.got) *(.got.plt) } :data\n  .data : { *(.data*) } :data\n  .bss \
             : { *(.bss*) *(COMMON) } :data\n  .rr : { KEEP(*(.rr)) } :rr\n  .mark : { \
             KEEP(*(.mark)) } :tail\n}\n",
        ),
    ];

    /// The twelfth closure round's verifier findings, through GNU ld 2.42
    /// and LLD 22.1.6 (gold 2.42 rejects the `INSERT` scripts), each
    /// refused with the output's bytes left as they were, and each raw link
    /// outside the driver run to show the defect:
    /// - F3: the page model held at 64 KiB only. With `.zz` (no file bytes)
    ///   at 0x500800 and `.dd` at 0x502000, LLD's no-PIE, PIE and static
    ///   programs read `tcg_val` 0 on the 4 KiB host (the kernel's zero
    ///   page): refused at the 4 KiB page, and GNU ld's (which gave `.dd`
    ///   another file page) at the 64 KiB one; a read-only `.rr` at
    ///   0x500800 made the store die with SIGSEGV through both: refused by
    ///   its permissions at the 4 KiB page. LLD's twin with `.zz` in the next
    ///   64 KiB page runs in every form.
    /// - F1: a `PHDRS` script's `:NONE` `.data` after `.bss` in the data
    ///   page: static programs read 0 (both linkers), and LLD's shared
    ///   object's user read `.comment` bytes; refused as outside every
    ///   segment's memory. In a gap of the data segment's memory, LLD's
    ///   `:NONE` `.data` is loaded from other file bytes (`tcg_val` read 0):
    ///   refused by the file-part rule.
    /// - F2: LLD gave `:NONE` `.data` the file offset under `.bss`, which lay
    ///   in the data segment's file part, and `tcg_z` read 42: refused as a
    ///   zero-fill section over file bytes that are not zero.
    /// - F4: an `INSERT BEFORE .init_array` script put trust-cg's `.data` in
    ///   GNU ld's `PT_GNU_RELRO`, and PIE and no-PIE programs died with
    ///   SIGSEGV on the first store: refused as `[TCG-LINK-WRITE-PROTECTED]`,
    ///   as is GNU ld's shared object (its user died the same way; the
    ///   plain library's runs), and so is LLD's static program whose `PHDRS`
    ///   script gave `.data` a
    ///   read-only segment (SIGSEGV); GNU ld's `--nostdlib` static program,
    ///   whose `PT_GNU_RELRO` covers its `.data` and which nothing applies,
    ///   runs, and so do trust-cg's immutable pointer tables
    ///   (`.data.rel.ro`) inside every linker's `PT_GNU_RELRO` (gold's too),
    ///   in PIE and no-PIE programs.
    /// - Controls for each page-model clause a linker reaches: GNU ld's
    ///   `.dd` from another file page (`p_vaddr - p_offset`), LLD's `.late`
    ///   segment mapping `.cdata`'s bytes over `.bss` (the later mapping
    ///   under a zero fill; `tcg_z` read `.cdata`'s word), GNU ld's
    ///   overlapping segments (its orphan build-id note in the last program
    ///   header; SIGSEGV), GNU ld's empty `PT_LOAD` in the page of `.data` of
    ///   a static program (the kernel ignores it: installed, runs), and GNU
    ///   ld's PIE whose data page ends with a read-only segment and an empty
    ///   writable one (`ld.so` would give the page the empty one's
    ///   permissions, the kernel gives it the read-only one's: SIGSEGV;
    ///   LLD's twin, whose last segment holds bytes, runs).
    #[test]
    fn pages_at_every_size_unloaded_sections_and_relro_stores_are_never_installed() {
        let directory = tempfile::tempdir().unwrap();
        let dir = directory.path();
        for (name, text) in [
            ("val2.trust_ir", VAL2_IR),
            ("bump.trust_ir", BUMP_IR),
            ("tab.trust_ir", TABLE_IR),
            ("tabmain.c", TABLE_MAIN),
            ("valstart.c", VAL_START),
            ("zerostart.c", ZERO_START),
            ("valmain.c", PAD_USER),
            ("bumpmain.c", BUMP_MAIN),
            ("bumpstart.c", BUMP_START),
            (
                "early.ld",
                "SECTIONS { .early : { *(.data) } } INSERT BEFORE .init_array;\n",
            ),
        ]
        .into_iter()
        .chain(ROUND12_SECTIONS)
        .chain(ROUND12_SCRIPTS)
        {
            fs::write(dir.join(name), text).unwrap();
        }
        for (flags, object, source) in [
            (&["-O1", "-fPIE"][..], "zz.o", "zz.c"),
            (&["-O1", "-fPIE"], "dd.o", "dd.c"),
            (&["-O1", "-fPIE"], "late.o", "late.c"),
            (&["-O1", "-fpic"], "cdata.o", "cdata.c"),
            (&[], "rr.o", "rr.s"),
            (&[], "mark.o", "mark.s"),
            (&["-O1"], "valmain.o", "valmain.c"),
            (&["-O1"], "bumpmain.o", "bumpmain.c"),
            (&["-O1"], "tabmain.o", "tabmain.c"),
            (
                &["-O1", "-fno-pic", "-ffreestanding"],
                "valstart.o",
                "valstart.c",
            ),
            (
                &["-O1", "-fno-pic", "-ffreestanding"],
                "zerostart.o",
                "zerostart.c",
            ),
            (
                &["-O1", "-fPIE", "-ffreestanding"],
                "bumpstart.o",
                "bumpstart.c",
            ),
            (
                &["-O1", "-fno-pic", "-ffreestanding"],
                "bumpstatic.o",
                "bumpstart.c",
            ),
        ] {
            let mut args = vec!["-c"];
            args.extend(flags);
            args.extend(["-o", object, source]);
            run_tool(dir, "cc", &args);
        }
        for (object, module, pic) in [
            ("val2.o", "val2.trust_ir", false),
            ("val2pic.o", "val2.trust_ir", true),
            ("bump.o", "bump.trust_ir", false),
            ("bumppic.o", "bump.trust_ir", true),
        ] {
            let mut args = vec!["--format=text", "-c", "-o", object, module];
            if pic {
                args.extend(["--relocation-model", "pic"]);
            }
            let result = trust_cg_on(None, dir, &args);
            assert!(result.status.success(), "{}", stderr(&result));
        }
        let loaded = "[TCG-LINK-LOADED-BYTES]";
        let segv = |program: &str| {
            let status = Command::new(dir.join(program)).status().unwrap();
            assert_eq!(status.signal(), Some(SIGSEGV), "{program}: {status:?}");
        };
        // Whether the image's `.data.rel.ro` lies inside its `PT_GNU_RELRO`.
        let table_in_relro = |path: &Path| {
            let read = |flag: &str| {
                let output = Command::new("readelf")
                    .arg(flag)
                    .arg(path)
                    .output()
                    .unwrap();
                String::from_utf8_lossy(&output.stdout).into_owned()
            };
            let hex = |word: &str| u64::from_str_radix(word.trim_start_matches("0x"), 16).ok();
            let table = read("-SW").lines().find_map(|line| {
                let words: Vec<&str> = line.split_whitespace().collect();
                let at = words.iter().position(|word| *word == ".data.rel.ro")?;
                hex(words.get(at + 2)?)
            });
            let relro = read("-lW").lines().find_map(|line| {
                let words: Vec<&str> = line.split_whitespace().collect();
                if words.first() != Some(&"GNU_RELRO") {
                    return None;
                }
                Some((hex(words.get(2)?)?, hex(words.get(5)?)?))
            });
            matches!((table, relro), (Some(at), Some((start, size))) if at >= start && at < start + size)
        };
        for (linker, bin) in linkers(dir) {
            let bin = bin.as_deref();
            let cc = bin.map_or_else(
                || "cc".to_string(),
                |bin| bin.join("cc").display().to_string(),
            );
            // trust-cg's immutable pointer table (`.data.rel.ro`) inside
            // `PT_GNU_RELRO`, where it belongs: installed and run.
            for (output, extra) in [("tab_pie", &[][..]), ("tab_np", &["--no-pie"])] {
                let output = format!("{output}_{linker}");
                let mut args = vec!["--format=text"];
                args.extend(extra);
                args.extend(["-o", output.as_str(), "tab.trust_ir", "-Wl,tabmain.o"]);
                let result = trust_cg_on(bin, dir, &args);
                assert!(result.status.success(), "{output}: {}", stderr(&result));
                assert!(table_in_relro(&dir.join(&output)), "{output}");
                assert_eq!(
                    run_program(&dir.join(&output)),
                    (Some(0), "v=42\n".to_string()),
                    "{output}"
                );
            }
            if linker == "gold" {
                // gold rejects the `INSERT` scripts.
                continue;
            }
            let lld = linker == "lld";
            let name = |stem: &str| format!("{stem}_{linker}");
            let refused = |output: &str, extra: &[&str], module: &str, group: &str, text: &str| {
                let mut args = vec!["--format=text"];
                args.extend(extra);
                args.extend(["-o", output, module, group]);
                let texts: Vec<&str> = [text].into_iter().filter(|text| !text.is_empty()).collect();
                let tag = if text.contains("PT_GNU_RELRO") || text.contains("is not writable") {
                    "[TCG-LINK-WRITE-PROTECTED]"
                } else {
                    loaded
                };
                refused_leaving_output(dir, bin, &args, tag, &texts);
            };
            let installed = |output: &str, extra: &[&str], module: &str, group: &str| {
                let mut args = vec!["--format=text"];
                args.extend(extra);
                args.extend(["-o", output, module, group]);
                installed_and_run(dir, bin, &args)
            };
            // F3: the 4 KiB page of `.data` ends with `.zz`, its 64 KiB page
            // with `.dd`.
            let zz = if lld {
                "its PT_LOAD segment at [0x500800, 0x500880) holds no file bytes, so the kernel \
                 maps the 0x1000-byte page at 0x500000 it begins in as zero fill, over the file \
                 bytes the PT_LOAD segment at [0x500000, 0x5004"
            } else {
                "share the 0x10000-byte page at 0x500000 and map it from different file pages"
            };
            for (output, extra, objects) in [
                ("zz_np", &["--no-pie"][..], "valmain.o,zz.o,dd.o"),
                ("zz_pie", &[], "valmain.o,zz.o,dd.o"),
                ("zz_st", &["--static", "--nostdlib"], "valstart.o,zz.o,dd.o"),
            ] {
                let group = format!("-Wl,{objects},-T,zzdd.ld,{DATA_BSS_START}");
                refused(&name(output), extra, "val2.trust_ir", &group, zz);
            }
            if lld {
                let raw = name("zz_raw");
                run_tool(
                    dir,
                    &cc,
                    &[
                        "-no-pie",
                        "-o",
                        &raw,
                        "valmain.o",
                        "zz.o",
                        "dd.o",
                        "val2.o",
                        "-Wl,-T,zzdd.ld",
                        &format!("-Wl,{DATA_BSS_START}"),
                    ],
                );
                assert_eq!(
                    run_program(&dir.join(&raw)),
                    (Some(1), "tcg_val=0 tcg_z=0\n".to_string()),
                    "{raw}"
                );
                // The twin runs in every form.
                for (output, extra, objects) in [
                    ("twin_np", &["--no-pie"][..], "valmain.o,zz.o,dd.o"),
                    ("twin_pie", &[], "valmain.o,zz.o,dd.o"),
                ] {
                    let group = format!("-Wl,{objects},-T,twin.ld,{DATA_BSS_START}");
                    assert_eq!(
                        installed(&name(output), extra, "val2.trust_ir", &group),
                        (Some(0), "tcg_val=0x2a tcg_z=0\n".to_string()),
                        "{output}"
                    );
                }
                let group = format!("-Wl,valstart.o,zz.o,dd.o,-T,twin.ld,{DATA_BSS_START}");
                assert_eq!(
                    installed(
                        &name("twin_st"),
                        &["--static", "--nostdlib"],
                        "val2.trust_ir",
                        &group
                    )
                    .0,
                    Some(0)
                );
            }
            // F3b: a read-only `.rr` in the 4 KiB page of `.data`.
            let group = format!("-Wl,bumpmain.o,rr.o,dd.o,-T,rrdd.ld,{DATA_BSS_START}");
            refused(
                &name("rr_np"),
                &["--no-pie"],
                "bump.trust_ir",
                &group,
                "(R) share the 0x1000-byte page at 0x500000: the later mapping gives the whole \
                 page its permissions, which lack the earlier segment's `W`",
            );
            let raw = name("rr_raw");
            run_tool(
                dir,
                &cc,
                &[
                    "-no-pie",
                    "-o",
                    &raw,
                    "bumpmain.o",
                    "rr.o",
                    "dd.o",
                    "bump.o",
                    "-Wl,-T,rrdd.ld",
                    &format!("-Wl,{DATA_BSS_START}"),
                ],
            );
            segv(&raw);
            // F1: `.data` in no segment, in the page of the data segment.
            let outside = "its allocated section `.data` at [";
            let unloaded = "does not lie in the memory of one PT_LOAD segment";
            refused(
                &name("none_st"),
                &["--static", "--nostdlib"],
                "val2.trust_ir",
                "-Wl,valstart.o,cdata.o,-T,none.ld",
                unloaded,
            );
            let raw = name("none_raw");
            run_tool(
                dir,
                &cc,
                &[
                    "-static",
                    "-nostdlib",
                    "-o",
                    &raw,
                    "valstart.o",
                    "cdata.o",
                    "val2.o",
                    "-Wl,-T,none.ld",
                ],
            );
            assert_eq!(run_program(&dir.join(&raw)).0, Some(50), "{raw}");
            let library = format!("libnone_{linker}.so");
            refused(
                &library,
                &["--shared", "--relocation-model", "pic"],
                "val2.trust_ir",
                "-Wl,cdata.o,-T,noneshared.ld",
                outside,
            );
            if lld {
                let raw = "libnone_raw_lld.so";
                run_tool(
                    dir,
                    &cc,
                    &[
                        "-shared",
                        "-o",
                        raw,
                        "cdata.o",
                        "val2pic.o",
                        "-Wl,-T,noneshared.ld",
                    ],
                );
                let user = "none_user_lld";
                run_tool(
                    dir,
                    &cc,
                    &[
                        "-o",
                        user,
                        "valmain.o",
                        raw,
                        &format!("-Wl,-rpath,{}", dir.display()),
                    ],
                );
                let (code, stdout) = run_program(&dir.join(user));
                assert!(
                    code == Some(1) && !stdout.starts_with("tcg_val=0x2a "),
                    "{user}: {code:?} {stdout}"
                );
                // F2: `.bss` in the file part of the data segment, over the
                // bytes of `.data`, which has no segment.
                refused(
                    "nobits_st_lld",
                    &["--static", "--nostdlib"],
                    "val2.trust_ir",
                    "-Wl,zerostart.o,cdata.o,late.o,-T,nobits.ld",
                    "its zero-fill section `.bss` at [0x500020, 0x500028) lies in the file part of \
                     the PT_LOAD segment at [0x500000, 0x500048)",
                );
                let raw = "nobits_raw_lld";
                run_tool(
                    dir,
                    &cc,
                    &[
                        "-static",
                        "-nostdlib",
                        "-o",
                        raw,
                        "zerostart.o",
                        "cdata.o",
                        "late.o",
                        "val2.o",
                        "-Wl,-T,nobits.ld",
                    ],
                );
                assert_eq!(run_program(&dir.join(raw)).0, Some(42), "{raw}");
                // trust-cg's `.data` in a read-only segment.
                refused(
                    "readonly_st_lld",
                    &["--static", "--nostdlib"],
                    "bump.trust_ir",
                    "-Wl,bumpstatic.o,-T,readonly.ld",
                    "lies in the PT_LOAD segment at [0x500000, 0x500008) (R), which is not writable",
                );
                run_tool(
                    dir,
                    &cc,
                    &[
                        "-static",
                        "-nostdlib",
                        "-o",
                        "readonly_raw_lld",
                        "bumpstatic.o",
                        "bump.o",
                        "-Wl,-T,readonly.ld",
                    ],
                );
                segv("readonly_raw_lld");
                // trust-cg's `.data` in a gap of the data segment's memory,
                // its file bytes elsewhere: the segment loads others there.
                refused(
                    "gap_st_lld",
                    &["--static", "--nostdlib"],
                    "bump.trust_ir",
                    "-Wl,bumpstatic.o,cdata.o,late.o,-T,gap.ld",
                    "its allocated section `.data` at [0x500030, 0x500038) holds the file bytes at \
                     offset",
                );
                run_tool(
                    dir,
                    &cc,
                    &[
                        "-static",
                        "-nostdlib",
                        "-o",
                        "gap_raw_lld",
                        "bumpstatic.o",
                        "cdata.o",
                        "late.o",
                        "bump.o",
                        "-Wl,-T,gap.ld",
                    ],
                );
                assert_eq!(run_program(&dir.join("gap_raw_lld")).0, Some(1));
            }
            // A later segment in the page of `.data`: LLD maps `.cdata`'s
            // bytes over `.bss`; GNU ld's segments overlap.
            refused(
                &name("fill_st"),
                &["--static", "--nostdlib"],
                "val2.trust_ir",
                "-Wl,valstart.o,cdata.o,late.o,-T,fill.ld,--build-id",
                if lld {
                    "its PT_LOAD segment at [0x500000, 0x500010) is zero fill from 0x500008, and \
                     the later PT_LOAD segment at [0x500800, 0x500808) maps the 0x10000-byte page \
                     at 0x500000 from the file"
                } else {
                    "overlap in memory, so the later mapping replaces the earlier one's bytes"
                },
            );
            let raw = name("fill_raw");
            run_tool(
                dir,
                &cc,
                &[
                    "-static",
                    "-nostdlib",
                    "-o",
                    &raw,
                    "valstart.o",
                    "cdata.o",
                    "late.o",
                    "val2.o",
                    "-Wl,-T,fill.ld,--build-id",
                ],
            );
            if lld {
                assert_eq!(run_program(&dir.join(&raw)).0, Some(60), "{raw}");
            } else {
                segv(&raw);
            }
            if !lld {
                // An empty `PT_LOAD` in the page of `.data`, which the kernel
                // ignores.
                assert_eq!(
                    installed(
                        "empty_st_gnu",
                        &["--static", "--nostdlib"],
                        "val2.trust_ir",
                        "-Wl,valstart.o,mark.o,-T,empty.ld",
                    )
                    .0,
                    Some(0)
                );
            }
            // A PIE whose data page ends with a read-only segment and an
            // empty writable one.
            let group = "-Wl,bumpstart.o,rr.o,mark.o,-T,tail.ld,\
                         --dynamic-linker=/lib/ld-linux-aarch64.so.1";
            if lld {
                assert_eq!(
                    installed("tail_lld", &["--nostdlib"], "bump.trust_ir", group).0,
                    Some(0)
                );
            } else {
                refused(
                    "tail_gnu",
                    &["--nostdlib"],
                    "bump.trust_ir",
                    group,
                    "its PT_LOAD segments at [0x100000, 0x100108) (RW) and [0x100108, 0x100110) \
                     (R) share the 0x10000-byte page at 0x100000: the later mapping gives the \
                     whole page its permissions, which lack the earlier segment's `W`",
                );
                run_tool(
                    dir,
                    &cc,
                    &[
                        "-pie",
                        "-nostdlib",
                        "-o",
                        "tail_raw_gnu",
                        "bumpstart.o",
                        "rr.o",
                        "mark.o",
                        "bumppic.o",
                        "-Wl,-T,tail.ld,--dynamic-linker=/lib/ld-linux-aarch64.so.1",
                    ],
                );
                segv("tail_raw_gnu");
                // F4: trust-cg's `.data` in `PT_GNU_RELRO`.
                for (output, extra) in [("early_pie_gnu", &[][..]), ("early_np_gnu", &["--no-pie"])]
                {
                    refused(
                        output,
                        extra,
                        "bump.trust_ir",
                        "-Wl,bumpmain.o,-T,early.ld",
                        "PT_GNU_RELRO segment at [",
                    );
                }
                run_tool(
                    dir,
                    "cc",
                    &[
                        "-o",
                        "early_raw_gnu",
                        "bumpmain.o",
                        "bumppic.o",
                        "-Wl,-T,early.ld",
                    ],
                );
                segv("early_raw_gnu");
                // A shared object: `ld.so` applies its `PT_GNU_RELRO` too.
                refused(
                    "libearly_gnu.so",
                    &["--shared", "--relocation-model", "pic"],
                    "bump.trust_ir",
                    "-Wl,-T,early.ld",
                    "PT_GNU_RELRO segment at [",
                );
                let rpath = format!("-Wl,-rpath,{}", dir.display());
                for (library, user, script) in [
                    ("libearly_raw_gnu.so", "early_user_gnu", "-Wl,-T,early.ld"),
                    ("libplain_raw_gnu.so", "plain_user_gnu", "-Wl,-z,relro"),
                ] {
                    run_tool(dir, "cc", &["-shared", "-o", library, "bumppic.o", script]);
                    run_tool(dir, "cc", &["-o", user, "bumpmain.o", library, &rpath]);
                }
                segv("early_user_gnu");
                assert_eq!(
                    run_program(&dir.join("plain_user_gnu")),
                    (Some(0), "v=43\n".to_string())
                );
                // GNU ld's `PT_GNU_RELRO` over the `.data` of a `--nostdlib`
                // static program, which nothing applies.
                assert_eq!(
                    installed(
                        "relro_st_gnu",
                        &["--static", "--nostdlib"],
                        "bump.trust_ir",
                        "-Wl,bumpstart.o"
                    )
                    .0,
                    Some(0)
                );
                let raw = "relro_st_raw_gnu";
                run_tool(
                    dir,
                    "cc",
                    &["-static", "-nostdlib", "-o", raw, "bumpstart.o", "bump.o"],
                );
                let headers = Command::new("readelf")
                    .args(["-lW"])
                    .arg(dir.join(raw))
                    .output()
                    .unwrap();
                assert!(
                    String::from_utf8_lossy(&headers.stdout).contains("GNU_RELRO"),
                    "{headers:?}"
                );
            }
        }
    }

    /// trust-cg thread-locals `tcg_t` (42, `.tdata`) and `tcg_tz` (0,
    /// `.tbss`), local exec, and their getters.
    const TLS_IR: &str = "; TrustIr text format v1\nmodule \"tcg_tls\"\n\nfuncty.0 = () -> \
        (u64)\n\nglobal tls(local_exec) mut align(8) @tcg_t u64 = 42\nglobal tls(local_exec) mut \
        align(8) @tcg_tz u64 = 0\n\nfn @tcg_tls_get(functy.0) {\nbb0:\n    %0 = global_addr \
        @global.0\n    %1 = load u64, ptr %0\n    ret %1\n}\n\nfn @tcg_tls_get_z(functy.0) {\nbb0:\n    \
        %0 = global_addr @global.1\n    %1 = load u64, ptr %0\n    ret %1\n}\n";

    /// `main` prints the trust-cg thread-locals and its own `c_t` (7); exits 0
    /// when they read 42, 0 and 7.
    const TLS_MAIN: &str = "#include <stdio.h>\nextern unsigned long tcg_tls_get(void), \
        tcg_tls_get_z(void);\n__thread unsigned long c_t = 7;\nint main(void) { unsigned long a = \
        tcg_tls_get(), z = tcg_tls_get_z(); printf(\"tcg_t=%#lx tcg_tz=%#lx c_t=%lu\\n\", a, z, c_t); \
        return a == 42 && z == 0 && c_t == 7 ? 0 : 1; }\n";

    /// The user of a library with the trust-cg thread-locals: exits 0 when
    /// they read 42 and 0.
    const TLS_USER: &str = "#include <stdio.h>\nextern unsigned long tcg_tls_get(void), \
        tcg_tls_get_z(void);\nint main(void) { unsigned long a = tcg_tls_get(), z = \
        tcg_tls_get_z(); printf(\"tcg_t=%#lx tcg_tz=%#lx\\n\", a, z); return a == 42 && z == 0 ? 0 : \
        1; }\n";

    /// More C thread-locals, in `.tdata` and `.tbss`: a second object with
    /// thread-locals in an ordinary link.
    const TLS_MORE: &str = "__thread unsigned long more_t = 5;\n__thread unsigned long \
        more_z[4];\nunsigned long more_sum(void) { more_z[1] += 2; return more_t + more_z[1]; }\n";

    /// [`TLS_MAIN`] with [`TLS_MORE`]'s thread-locals too.
    const TLS_MORE_MAIN: &str = "#include <stdio.h>\nextern unsigned long tcg_tls_get(void), \
        tcg_tls_get_z(void), more_sum(void);\n__thread unsigned long c_t = 7;\nint main(void) { \
        unsigned long a = tcg_tls_get(), z = tcg_tls_get_z(), m = more_sum(); \
        printf(\"tcg_t=%#lx tcg_tz=%#lx c_t=%lu m=%lu\\n\", a, z, c_t, m); return a == 42 && z == 0 \
        && c_t == 7 && m == 7 ? 0 : 1; }\n";

    /// A C++ program with `thread_local`s, one with a dynamic initializer.
    const TLS_CXX: &str = "#include <cstdio>\n#include <string>\nextern \"C\" unsigned long \
        tcg_tls_get(void), tcg_tls_get_z(void);\nthread_local std::string s = std::string(\"thr\") + \
        \"ead\";\nthread_local unsigned long n = 3;\nint main() { unsigned long a = tcg_tls_get(), z \
        = tcg_tls_get_z(); std::printf(\"tcg_t=%#lx tcg_tz=%#lx s=%s n=%lu\\n\", a, z, s.c_str(), \
        n); return a == 42 && z == 0 && s == \"thread\" && n == 3 ? 0 : 1; }\n";

    /// Two words of C data, for a library whose `.tdata` a script moves past
    /// `.data`.
    const CDAT: &str = "__attribute__((used)) unsigned long cdat[2] = {0x1111111111111111UL, \
        0x2222222222222222UL};\n";

    /// LLD's `INSERT` script moving the `.tdata` of an object named `*tls*`
    /// (the C `main`'s) past `.data`.
    const TLS_SPLIT: &str = "SECTIONS { .tcgtdata : { *tls*.o(.tdata*) } } INSERT AFTER .data;\n";

    /// The same, for every `.tdata`.
    const TLS_SPLIT_ALL: &str = "SECTIONS { .tcgtdata : { *(.tdata*) } } INSERT AFTER .data;\n";

    /// A `_start` without the C runtime, for a `--nostdlib` PIE that
    /// `ld.so` starts (it sets up the thread-local block): exits with the low
    /// byte of trust-cg's `tcg_tz` (0 when it reads right), or 200 when
    /// `tcg_t` does not read 42 (the first verifier's `cstart3.c`).
    const TLS_START: &str = "extern unsigned long tcg_tls_get(void), tcg_tls_get_z(void);\nvoid \
        _start(void) { unsigned long a = tcg_tls_get(), z = tcg_tls_get_z(); long code = a != 42 ? \
        200 : (long)(z & 0xff);\n  register long x0 __asm__(\"x0\") = code; register long x8 \
        __asm__(\"x8\") = 93; __asm__ volatile(\"svc 0\" :: \"r\"(x0), \"r\"(x8)); for (;;); }\n";

    /// `script` ([`tls_phdrs_script`]) with its `.tbss` statement moved
    /// before `.tdata`: GNU ld 2.42 then gives both the same address in one
    /// `PT_TLS` (the first verifier's `tbssfirst_pie.ld`).
    fn tbss_first(script: &str) -> String {
        let start = script.find("\n  .tbss").expect(".tbss in the script");
        let end = start + 1 + script[start + 1..].find('\n').unwrap();
        let line = script[start..end].to_string();
        let without = format!("{}{}", &script[..start], &script[end..]);
        let at = without.find("\n  .tdata").expect(".tdata in the script");
        format!("{}{line}{}", &without[..at], &without[at..])
    }

    /// GNU ld 2.42's default script for an AArch64 executable (`ld
    /// --verbose`, with `-pie` for a PIE) with program headers of its own: a
    /// `PT_TLS` over `.tdata` and `.tbss` (`full`, the linker's own layout),
    /// or over `.tbss` alone, `.tdata` in the data segment and in no
    /// `PT_TLS` (the twelfth closure audit's reproducer, after its
    /// `mkphdrs.py`). An output section without program headers named takes
    /// the previous section's, so `.preinit_array` returns to the data
    /// segment alone.
    fn tls_phdrs_script(pie: bool, full: bool) -> String {
        const RULE: &str = "==================================================";
        let mut command = Command::new("ld");
        if pie {
            command.arg("-pie");
        }
        let output = command.arg("--verbose").output().unwrap();
        let text = String::from_utf8(output.stdout).unwrap();
        let mut script = text
            .split(RULE)
            .nth(1)
            .expect("ld --verbose prints its script between rules")
            .trim()
            .replacen(
                "SECTIONS\n{",
                "PHDRS\n{\n  phdr PT_PHDR PHDRS;\n  interp PT_INTERP;\n  text PT_LOAD FILEHDR \
                 PHDRS;\n  data PT_LOAD;\n  dynamic PT_DYNAMIC;\n  tls PT_TLS;\n  ehframe \
                 PT_GNU_EH_FRAME;\n  stack PT_GNU_STACK FLAGS(6);\n}\nSECTIONS\n{",
                1,
            );
        let tdata = if full { ":data :tls" } else { ":data" };
        for (section, phdrs) in [
            (".interp", ":text :interp"),
            (".note.gnu.build-id", ":text"),
            (".eh_frame_hdr", ":text :ehframe"),
            (".eh_frame", ":text"),
            (".tdata", tdata),
            (".tbss", ":data :tls"),
            (".preinit_array", ":data"),
            (".dynamic", ":data :dynamic"),
            (".got", ":data"),
        ] {
            // The first output section statement of that name, through its
            // closing brace.
            let start = format!("\n  {section}");
            let at = script
                .match_indices(&start)
                .map(|(at, _)| at)
                .find(|at| script[at + start.len()..].starts_with([' ', '\t', ':']))
                .unwrap_or_else(|| panic!("{section} in the default script"));
            let open = at + script[at..].find('{').unwrap();
            let mut depth = 0;
            let close = script[open..]
                .char_indices()
                .find_map(|(index, c)| {
                    match c {
                        '{' => depth += 1,
                        '}' => {
                            depth -= 1;
                            if depth == 0 {
                                return Some(open + index);
                            }
                        }
                        _ => {}
                    }
                    None
                })
                .unwrap();
            script.insert_str(close + 1, &format!(" {phdrs}"));
        }
        script
    }

    /// The twelfth closure audit's thread-local template finding: no rule
    /// related `PT_TLS`, from which each thread's block is initialized, to
    /// trust-cg's `.tdata` and `.tbss`, and the driver installed programs and
    /// a library whose trust-cg thread-locals read wrong values without a
    /// crash. Each is refused now as `[TCG-LINK-TLS-TEMPLATE]` with the
    /// output's bytes left as they were, and each raw link outside the
    /// driver is run to show the defect:
    /// - GNU ld 2.42 given a `PHDRS` script whose `PT_TLS` holds `.tbss`
    ///   alone (no-PIE and PIE): the `PT_TLS` does not begin at `.tdata`;
    ///   its `full` twin, the linker's own layout, is installed and runs;
    /// - LLD 22.1.6 given an `INSERT` script that moves the C `main`'s
    ///   `.tdata` past `.data`, with `-z norelro`: `.data` lies in the
    ///   template's file part; and a shared object whose every `.tdata` moved
    ///   so, whose user read 0;
    /// - LLD given `--section-start=.tbss=0x700000` (no script), no-PIE and
    ///   PIE: its `PT_TLS` runs from `.tbss`, laid over `.interp`, to
    ///   `.tdata`, and its file part is in no `PT_LOAD`'s (a trust-cg
    ///   thread-local read the bytes `/lib/ld-`);
    /// - (the first verifier) GNU ld given `-z nosectionheader` and a
    ///   `PHDRS` script that puts `.tbss` before `.tdata`, a `--nostdlib`
    ///   PIE: both sections at one address, and trust-cg's zero-fill
    ///   thread-local reads 42. An image without section headers and a
    ///   `PT_TLS` with memory is refused (its sections are not shown), the
    ///   linker's own layout too (GNU ld and LLD), conservatively; with
    ///   section headers the `.tbss`-first layout is refused by its overlap.
    ///
    /// Ordinary thread-local links through GNU ld, gold and LLD are installed
    /// and run: PIE, no-PIE, static, `-z relro -z now`, a C object with more
    /// thread-locals, a C++ program with `thread_local`s (one with a dynamic
    /// initializer), and a shared object with its user.
    #[test]
    fn tls_templates_that_do_not_hold_trust_cgs_thread_locals_are_never_installed() {
        let directory = tempfile::tempdir().unwrap();
        let dir = directory.path();
        let general_dynamic = TLS_IR.replace("tls(local_exec)", "tls(general_dynamic)");
        for (name, text) in [
            ("vars.trust_ir", TLS_IR),
            ("vars_gd.trust_ir", general_dynamic.as_str()),
            ("tlsmain.c", TLS_MAIN),
            ("tlsuser.c", TLS_USER),
            ("more.c", TLS_MORE),
            ("moremain.c", TLS_MORE_MAIN),
            ("tlscxx.cc", TLS_CXX),
            ("cdat.c", CDAT),
            ("split.ld", TLS_SPLIT),
            ("splitall.ld", TLS_SPLIT_ALL),
            ("tlsstart.c", TLS_START),
        ] {
            fs::write(dir.join(name), text).unwrap();
        }
        fs::write(
            dir.join("tbssfirst_pie.ld"),
            tbss_first(&tls_phdrs_script(true, true)),
        )
        .unwrap();
        for (pie, full, name) in [
            (false, true, "ph_full.ld"),
            (false, false, "ph_tbss.ld"),
            (true, true, "phpie_full.ld"),
            (true, false, "phpie_tbss.ld"),
        ] {
            fs::write(dir.join(name), tls_phdrs_script(pie, full)).unwrap();
        }
        for (compiler, flags, object, source) in [
            ("cc", &["-O1"][..], "tlsmain.o", "tlsmain.c"),
            ("cc", &["-O1"], "tlsuser.o", "tlsuser.c"),
            ("cc", &["-O1"], "more.o", "more.c"),
            ("cc", &["-O1"], "moremain.o", "moremain.c"),
            ("c++", &["-O1"], "tlscxx.o", "tlscxx.cc"),
            ("cc", &["-O1", "-fpic"], "cdat.o", "cdat.c"),
            (
                "cc",
                &["-O1", "-fPIE", "-fno-stack-protector", "-ffreestanding"],
                "tlsstart.o",
                "tlsstart.c",
            ),
        ] {
            let mut args = vec!["-c"];
            args.extend(flags);
            args.extend(["-o", object, source]);
            run_tool(dir, compiler, &args);
        }
        for (object, module, pic) in [
            ("vars.o", "vars.trust_ir", false),
            ("vars_gd.o", "vars_gd.trust_ir", true),
        ] {
            let mut args = vec!["--format=text", "-c", "-o", object, module];
            if pic {
                args.extend(["--relocation-model", "pic"]);
            }
            let result = trust_cg_on(None, dir, &args);
            assert!(result.status.success(), "{}", stderr(&result));
        }
        let tag = "[TCG-LINK-TLS-TEMPLATE]";
        let right = (Some(0), "tcg_t=0x2a tcg_tz=0 c_t=7\n".to_string());
        // A raw program reads some thread-local wrong and exits 1.
        let wrong = |program: &str| {
            let (code, stdout) = run_program(&dir.join(program));
            assert!(
                code == Some(1) && stdout != right.1 && stdout != "tcg_t=0x2a tcg_tz=0\n",
                "{program}: {code:?} {stdout}"
            );
        };
        let rpath = format!("-Wl,-rpath,{}", dir.display());
        for (linker, bin) in linkers(dir) {
            let bin = bin.as_deref();
            let cc = bin.map_or_else(
                || "cc".to_string(),
                |bin| bin.join("cc").display().to_string(),
            );
            let name = |stem: &str| format!("{stem}_{linker}");
            let installed = |output: &str, extra: &[&str], module: &str, group: &str| {
                let mut args = vec!["--format=text"];
                args.extend(extra);
                args.extend(["-o", output, module, group]);
                installed_and_run(dir, bin, &args)
            };
            // Ordinary thread-local links.
            for (output, extra) in [
                ("tls_pie", &[][..]),
                ("tls_np", &["--no-pie"]),
                ("tls_st", &["--static"]),
            ] {
                assert_eq!(
                    installed(&name(output), extra, "vars.trust_ir", "-Wl,tlsmain.o"),
                    right,
                    "{output} {linker}"
                );
            }
            assert_eq!(
                installed(
                    &name("tls_now"),
                    &[],
                    "vars.trust_ir",
                    "-Wl,tlsmain.o,-z,relro,-z,now"
                ),
                right
            );
            for extra in [&[][..], &["--static"]] {
                assert_eq!(
                    installed(
                        &name("tls_more"),
                        extra,
                        "vars.trust_ir",
                        "-Wl,moremain.o,more.o"
                    ),
                    (Some(0), "tcg_t=0x2a tcg_tz=0 c_t=7 m=7\n".to_string()),
                    "{linker} {extra:?}"
                );
                assert_eq!(
                    installed(
                        &name("tls_cxx"),
                        extra,
                        "vars.trust_ir",
                        "-Wl,tlscxx.o,-lstdc++,-lm"
                    ),
                    (Some(0), "tcg_t=0x2a tcg_tz=0 s=thread n=3\n".to_string()),
                    "{linker} {extra:?}"
                );
            }
            let library = format!("libtls_{linker}.so");
            let result = trust_cg_on(
                bin,
                dir,
                &[
                    "--format=text",
                    "--shared",
                    "--relocation-model",
                    "pic",
                    "-o",
                    &library,
                    "vars_gd.trust_ir",
                ],
            );
            assert!(result.status.success(), "{library}: {}", stderr(&result));
            let user = name("tls_user");
            run_tool(dir, &cc, &["-o", &user, "tlsuser.o", &library, &rpath]);
            assert_eq!(
                run_program(&dir.join(&user)),
                (Some(0), "tcg_t=0x2a tcg_tz=0\n".to_string())
            );
            let refused = |output: &str, extra: &[&str], module: &str, group: &str, text: &str| {
                let mut args = vec!["--format=text"];
                args.extend(extra);
                args.extend(["-o", output, module, group]);
                refused_leaving_output(dir, bin, &args, tag, &[text]);
            };
            match linker {
                "gnu" => {
                    // The linker's own layout, written by a script.
                    for (output, extra, script) in [
                        ("full_np_gnu", &["--no-pie"][..], "ph_full.ld"),
                        ("full_pie_gnu", &[], "phpie_full.ld"),
                    ] {
                        let group = format!("-Wl,tlsmain.o,-T,{script}");
                        assert_eq!(
                            installed(output, extra, "vars.trust_ir", &group),
                            right,
                            "{output}"
                        );
                    }
                    // `PT_TLS` over `.tbss` alone.
                    for (output, extra, script, raw, pie) in [
                        (
                            "tbss_np_gnu",
                            &["--no-pie"][..],
                            "ph_tbss.ld",
                            "tbss_np_raw",
                            "-no-pie",
                        ),
                        ("tbss_pie_gnu", &[], "phpie_tbss.ld", "tbss_pie_raw", "-pie"),
                    ] {
                        refused(
                            output,
                            extra,
                            "vars.trust_ir",
                            &format!("-Wl,tlsmain.o,-T,{script}"),
                            "does not begin at its first thread-local section `.tdata`",
                        );
                        run_tool(
                            dir,
                            "cc",
                            &[
                                pie,
                                "-o",
                                raw,
                                "tlsmain.o",
                                "vars.o",
                                &format!("-Wl,-T,{script}"),
                            ],
                        );
                        wrong(raw);
                    }
                    // Without a section header table (`-z nosectionheader`),
                    // a `PT_TLS` whose sections the image does not show is
                    // refused: the `.tbss`-first layout, whose two sections
                    // share their bytes (outside the driver trust-cg's
                    // zero-fill `tcg_tz` reads 42), and the linker's own
                    // layout alike. With section headers the `.tbss`-first
                    // layout is refused by its overlap, and the linker's own
                    // is installed and runs.
                    for (output, group, text) in [
                        (
                            "first_nsh_gnu",
                            "-Wl,tlsstart.o,-T,tbssfirst_pie.ld,-z,nosectionheader",
                            "it has no section header table, so where its thread-local sections \
                             lie in its PT_TLS segment",
                        ),
                        (
                            "plain_nsh_gnu",
                            "-Wl,tlsstart.o,-z,nosectionheader",
                            "it has no section header table",
                        ),
                        (
                            "first_gnu",
                            "-Wl,tlsstart.o,-T,tbssfirst_pie.ld",
                            "overlap in the thread-local block",
                        ),
                    ] {
                        refused(output, &["--nostdlib"], "vars.trust_ir", group, text);
                    }
                    assert_eq!(
                        installed(
                            "tls_start_gnu",
                            &["--nostdlib"],
                            "vars.trust_ir",
                            "-Wl,tlsstart.o"
                        )
                        .0,
                        Some(0)
                    );
                    for (raw, options, code) in [
                        (
                            "first_nsh_raw",
                            "-Wl,-T,tbssfirst_pie.ld,-z,nosectionheader",
                            42,
                        ),
                        ("first_raw", "-Wl,-T,tbssfirst_pie.ld", 42),
                        ("plain_nsh_raw", "-Wl,-z,nosectionheader", 0),
                    ] {
                        run_tool(
                            dir,
                            "cc",
                            &["-nostdlib", "-o", raw, "tlsstart.o", "vars.o", options],
                        );
                        assert_eq!(run_program(&dir.join(raw)).0, Some(code), "{raw}");
                    }
                    let headers = Command::new("readelf")
                        .args(["-hW"])
                        .arg(dir.join("first_nsh_raw"))
                        .output()
                        .unwrap();
                    assert!(
                        String::from_utf8_lossy(&headers.stdout)
                            .contains("Number of section headers:         0"),
                        "{headers:?}"
                    );
                }
                "lld" => {
                    // LLD writes an image without section headers too: its
                    // own layout is refused, conservatively, and runs.
                    refused(
                        "plain_nsh_lld",
                        &["--nostdlib"],
                        "vars.trust_ir",
                        "-Wl,tlsstart.o,-z,nosectionheader",
                        "it has no section header table",
                    );
                    run_tool(
                        dir,
                        &cc,
                        &[
                            "-nostdlib",
                            "-o",
                            "plain_nsh_raw_lld",
                            "tlsstart.o",
                            "vars.o",
                            "-Wl,-z,nosectionheader",
                        ],
                    );
                    assert_eq!(run_program(&dir.join("plain_nsh_raw_lld")).0, Some(0));
                    // C's `.tdata` moved past `.data`, which then lies in
                    // the template.
                    refused(
                        "split_pie_lld",
                        &[],
                        "vars.trust_ir",
                        "-Wl,tlsmain.o,-z,norelro,-T,split.ld",
                        "of its PT_TLS segment, which each thread's block copies, hold its \
                         section `.data`",
                    );
                    run_tool(
                        dir,
                        &cc,
                        &[
                            "-o",
                            "split_raw_lld",
                            "tlsmain.o",
                            "vars.o",
                            "-Wl,-z,norelro,-T,split.ld",
                        ],
                    );
                    wrong("split_raw_lld");
                    // A shared object whose every `.tdata` moved so.
                    refused(
                        "libsplit_lld.so",
                        &["--shared", "--relocation-model", "pic"],
                        "vars_gd.trust_ir",
                        "-Wl,cdat.o,-z,norelro,-T,splitall.ld",
                        "initial bytes of its PT_TLS segment at",
                    );
                    run_tool(
                        dir,
                        &cc,
                        &[
                            "-shared",
                            "-o",
                            "libsplit_raw_lld.so",
                            "cdat.o",
                            "vars_gd.o",
                            "-Wl,-z,norelro,-T,splitall.ld",
                        ],
                    );
                    run_tool(
                        dir,
                        &cc,
                        &[
                            "-o",
                            "split_user_lld",
                            "tlsuser.o",
                            "libsplit_raw_lld.so",
                            &rpath,
                        ],
                    );
                    wrong("split_user_lld");
                    // `.tbss` placed by an address, no script.
                    for (output, extra, raw, pie) in [
                        ("start_np_lld", &["--no-pie"][..], "start_np_raw", "-no-pie"),
                        ("start_pie_lld", &[], "start_pie_raw", "-pie"),
                    ] {
                        refused(
                            output,
                            extra,
                            "vars.trust_ir",
                            "-Wl,tlsmain.o,--section-start=.tbss=0x700000",
                            "initial bytes of its PT_TLS segment at",
                        );
                        run_tool(
                            dir,
                            &cc,
                            &[
                                pie,
                                "-o",
                                raw,
                                "tlsmain.o",
                                "vars.o",
                                "-Wl,--section-start=.tbss=0x700000",
                            ],
                        );
                        wrong(raw);
                    }
                }
                _ => {}
            }
        }
    }

    /// A trust-cg constant `tcg_c` (42) in `.rodata` that `tcg_get` loads, and
    /// `tcg_get_z`, which returns 0 ([`VAL_START`]'s getters).
    const CONST_IR: &str = "; TrustIr text format v1\nmodule \"tcg_const\"\n\nfuncty.0 = () -> \
        (u64)\n\nglobal align(8) @tcg_c u64 = 42\n\nfn @tcg_get(functy.0) {\nbb0:\n    %0 = \
        global_addr @global.0\n    %1 = load u64, ptr %0\n    ret %1\n}\n\nfn @tcg_get_z(functy.0) \
        {\nbb0:\n    %0 = const u64 0\n    ret %0\n}\n";

    /// A `PHDRS` script that gives `.rodata` a `PT_LOAD` of its own with the
    /// permissions `flags`.
    fn rodata_script(flags: u32) -> String {
        format!(
            "ENTRY(_start)\nPHDRS {{ text PT_LOAD FILEHDR PHDRS FLAGS(5); ro PT_LOAD FLAGS({flags}); \
             data PT_LOAD FLAGS(6); }}\nSECTIONS {{\n  . = 0x400000 + SIZEOF_HEADERS;\n  \
             .note.gnu.build-id : {{ *(.note.gnu.build-id) }} :text\n  .text : {{ *(.text*) }} \
             :text\n  .eh_frame : {{ KEEP(*(.eh_frame)) }} :text\n  .eh_frame_hdr : {{ \
             *(.eh_frame_hdr) }} :text\n  . = 0x500000;\n  .rodata : {{ *(.rodata*) }} :ro\n  . = \
             0x600000;\n  .data : {{ *(.data*) }} :data\n  .bss : {{ *(.bss*) *(COMMON) }} :data\n}}\n"
        )
    }

    /// A `PHDRS` script that gives trust-cg's `.text` (every `.text` but
    /// `valstart.o`'s) a read-only `PT_LOAD` of its own.
    const TEXT_READ_ONLY: &str = "ENTRY(_start)\nPHDRS { text PT_LOAD FILEHDR PHDRS FLAGS(5); tcg \
        PT_LOAD FLAGS(4); data PT_LOAD FLAGS(6); }\nSECTIONS {\n  . = 0x400000 + SIZEOF_HEADERS;\n  \
        .note.gnu.build-id : { *(.note.gnu.build-id) } :text\n  .text : { valstart.o(.text*) } \
        :text\n  .rodata : { *(.rodata*) } :text\n  .eh_frame : { KEEP(*(.eh_frame)) } :text\n  . = \
        0x500000;\n  .tcgtext : { *(.text*) } :tcg\n  . = 0x600000;\n  .data : { *(.data*) } :data\n  \
        .bss : { *(.bss*) *(COMMON) } :data\n}\n";

    /// `main` calls trust-cg's `tcg_get` (42), then `backtrace`, whose
    /// unwinder reads `.eh_frame`: exits 0 when it reads 42 and finds frames.
    const BACKTRACE_MAIN: &str = "#include <execinfo.h>\n#include <stdio.h>\nextern unsigned long \
        tcg_get(void);\nint main(void) { void *frames[16]; unsigned long v = tcg_get(); int n = \
        backtrace(frames, 16); printf(\"v=%lu frames=%d\\n\", v, n); return v == 42 && n > 0 ? 0 : \
        1; }\n";

    /// A dynamic no-PIE `PHDRS` script that gives `.eh_frame` a `PT_LOAD` of
    /// its own with the permissions `flags`, `.eh_frame_hdr` staying in the
    /// readable text segment (the first verifier's `dyneh0.ld`).
    fn eh_frame_script(flags: u32) -> String {
        format!(
            "ENTRY(_start)\nPHDRS {{ phdr PT_PHDR PHDRS; interp PT_INTERP; text PT_LOAD FILEHDR \
             PHDRS FLAGS(5); eh PT_LOAD FLAGS({flags}); data PT_LOAD FLAGS(6); dynamic \
             PT_DYNAMIC; ehhdr PT_GNU_EH_FRAME; stack PT_GNU_STACK FLAGS(6); }}\nSECTIONS {{\n  \
             . = 0x400000 + SIZEOF_HEADERS;\n  .interp : {{ *(.interp) }} :text :interp\n  \
             .note.gnu.build-id : {{ *(.note.gnu.build-id) }} :text\n  .note.ABI-tag : {{ \
             *(.note.ABI-tag) }} :text\n  .hash : {{ *(.hash) }} :text\n  .gnu.hash : {{ \
             *(.gnu.hash) }} :text\n  .dynsym : {{ *(.dynsym) }} :text\n  .dynstr : {{ \
             *(.dynstr) }} :text\n  .gnu.version : {{ *(.gnu.version) }} :text\n  \
             .gnu.version_r : {{ *(.gnu.version_r) }} :text\n  .rela.dyn : {{ *(.rela.dyn) \
             *(.rela.got) }} :text\n  .rela.plt : {{ *(.rela.plt) }} :text\n  .init : {{ \
             KEEP(*(.init)) }} :text\n  .plt : {{ *(.plt) }} :text\n  .text : {{ *(.text \
             .text.*) }} :text\n  .fini : {{ KEEP(*(.fini)) }} :text\n  .rodata : {{ *(.rodata \
             .rodata.*) }} :text\n  .eh_frame_hdr : {{ *(.eh_frame_hdr) }} :text :ehhdr\n  . = \
             0x500000;\n  .eh_frame : {{ KEEP(*(.eh_frame)) }} :eh\n  . = 0x600000;\n  \
             .init_array : {{ KEEP(*(.init_array .init_array.*)) }} :data\n  .fini_array : {{ \
             KEEP(*(.fini_array .fini_array.*)) }} :data\n  .dynamic : {{ *(.dynamic) }} :data \
             :dynamic\n  .got : {{ *(.got) }} :data\n  .got.plt : {{ *(.got.plt) }} :data\n  \
             .data : {{ *(.data .data.*) }} :data\n  .bss : {{ *(.bss .bss.*) *(COMMON) }} \
             :data\n}}\n"
        )
    }

    /// trust-cg's `.data` in no segment (`:NONE`), after `.bss` in the page
    /// of the data segment, in a static layout with `.eh_frame_hdr`.
    const DATA_NONE: &str = "ENTRY(_start)\nPHDRS { text PT_LOAD FILEHDR PHDRS; data PT_LOAD; hdr \
        PT_GNU_EH_FRAME; }\nSECTIONS {\n  . = 0x400000 + SIZEOF_HEADERS;\n  .text : { *(.text*) } \
        :text\n  .rodata : { *(.rodata*) } :text\n  .eh_frame_hdr : { *(.eh_frame_hdr) } :text \
        :hdr\n  .eh_frame : { KEEP(*(.eh_frame)) } :text\n  . = 0x500000;\n  .bss : { *(.bss*) \
        *(COMMON) } :data\n  .data : { *(.data*) } :NONE\n}\n";

    /// The twelfth closure audit's permission finding: only `PF_W` was
    /// checked for trust-cg's sections. A `PHDRS` script that gave trust-cg's
    /// `.rodata` a `PT_LOAD` without permissions (`FLAGS(0)`), and one that
    /// gave its `.text` a read-only one (`FLAGS(4)`), made GNU ld 2.42, LLD
    /// 22.1.6 and gold 2.42 write static programs that died with SIGSEGV on
    /// the first load or instruction, and the driver installed them. Both are
    /// refused now as `[TCG-LINK-SEGMENT-PERMISSIONS]` through each linker,
    /// with the output's bytes left as they were (gold prints trust-cg's
    /// `.text`, the last code input of its output section, at no address in
    /// its map, and it is placed by its symbols); each raw link outside the
    /// driver dies with SIGSEGV. The readable twin (`FLAGS(4)` for
    /// `.rodata`) is installed and runs.
    ///
    /// The first verifier: a dynamic no-PIE script that gave `.eh_frame` a
    /// segment without permissions was refused through GNU ld, whose map
    /// lists trust-cg's `.eh_frame` input, and installed through LLD (whose
    /// map prints it as pieces) and gold (which prints its merged `**
    /// eh_frame` data with no file); each program died with SIGSEGV in
    /// `_Unwind_Find_FDE` at its first `backtrace`. All three are refused
    /// now, each raw link dies with SIGSEGV, and the `FLAGS(4)` twin is
    /// installed and runs through each linker.
    ///
    /// The same round's repair: trust-cg's sections must be loaded where the
    /// map places them (`[TCG-LINK-LOADED-BYTES]`). A script marking its
    /// `.rodata` `(NOLOAD)` made GNU ld and LLD write it as zero fill, and
    /// the driver installed programs whose constant read 0 (exit 50); they
    /// are refused now, and gold, which loads the bytes, is installed. With
    /// `-z nosectionheader`, GNU ld and LLD placed trust-cg's `.data` in no
    /// segment (`:NONE`) and the driver installed programs whose global read
    /// 0 (the section rule read the section headers); they are refused.
    #[test]
    fn segments_without_the_permissions_trust_cgs_sections_need_are_never_installed() {
        let directory = tempfile::tempdir().unwrap();
        let dir = directory.path();
        for (name, text) in [
            ("const.trust_ir", CONST_IR.to_string()),
            ("valstart.c", VAL_START.to_string()),
            ("ro0.ld", rodata_script(0)),
            ("ro4.ld", rodata_script(4)),
            ("textro.ld", TEXT_READ_ONLY.to_string()),
            ("btmain.c", BACKTRACE_MAIN.to_string()),
            ("eh0.ld", eh_frame_script(0)),
            ("eh4.ld", eh_frame_script(4)),
            (
                "ronl.ld",
                rodata_script(4).replace(".rodata : {", ".rodata (NOLOAD) : {"),
            ),
            ("val2.trust_ir", VAL2_IR.to_string()),
            ("datanone.ld", DATA_NONE.to_string()),
        ] {
            fs::write(dir.join(name), text).unwrap();
        }
        run_tool(dir, "cc", &["-c", "-O1", "-o", "btmain.o", "btmain.c"]);
        let result = trust_cg_on(
            None,
            dir,
            &["--format=text", "-c", "-o", "val2.o", "val2.trust_ir"],
        );
        assert!(result.status.success(), "{}", stderr(&result));
        run_tool(
            dir,
            "cc",
            &[
                "-c",
                "-O1",
                "-fno-pic",
                "-ffreestanding",
                "-o",
                "valstart.o",
                "valstart.c",
            ],
        );
        let result = trust_cg_on(
            None,
            dir,
            &["--format=text", "-c", "-o", "const.o", "const.trust_ir"],
        );
        assert!(result.status.success(), "{}", stderr(&result));
        let tag = "[TCG-LINK-SEGMENT-PERMISSIONS]";
        for (linker, bin) in linkers(dir) {
            let bin = bin.as_deref();
            let cc = bin.map_or_else(
                || "cc".to_string(),
                |bin| bin.join("cc").display().to_string(),
            );
            let args = |output: &str, script: &str| -> Vec<String> {
                [
                    "--format=text",
                    "--static",
                    "--nostdlib",
                    "-o",
                    output,
                    "const.trust_ir",
                ]
                .into_iter()
                .map(str::to_string)
                .chain([format!("-Wl,valstart.o,-T,{script}")])
                .collect()
            };
            fn strs(args: &[String]) -> Vec<&str> {
                args.iter().map(String::as_str).collect()
            }
            for (script, text) in [
                ("ro0.ld", "trust-cg's input section `.rodata` of"),
                ("textro.ld", "(R), which is not executable (it lacks `E`)"),
            ] {
                let output = format!("{}_{linker}", script.trim_end_matches(".ld"));
                refused_leaving_output(dir, bin, &strs(&args(&output, script)), tag, &[text]);
                let raw = format!("{output}_raw");
                run_tool(
                    dir,
                    &cc,
                    &[
                        "-static",
                        "-nostdlib",
                        "-o",
                        &raw,
                        "valstart.o",
                        "const.o",
                        &format!("-Wl,-T,{script}"),
                    ],
                );
                let status = Command::new(dir.join(&raw)).status().unwrap();
                assert_eq!(status.signal(), Some(SIGSEGV), "{raw}: {status:?}");
            }
            let output = format!("ro4_{linker}");
            assert_eq!(
                installed_and_run(dir, bin, &strs(&args(&output, "ro4.ld"))).0,
                Some(0),
                "{output}"
            );
            // `.eh_frame` in a segment without permissions: GNU ld's and
            // LLD's maps place trust-cg's input, gold's merged data holds it.
            let text = if linker == "gold" {
                "trust-cg's `.eh_frame` input of"
            } else {
                "trust-cg's input section `.eh_frame` of"
            };
            let output = format!("eh0_{linker}");
            refused_leaving_output(
                dir,
                bin,
                &[
                    "--format=text",
                    "--no-pie",
                    "-o",
                    &output,
                    "const.trust_ir",
                    "-Wl,btmain.o,-T,eh0.ld",
                ],
                tag,
                &[text, "(no permissions), which is not readable"],
            );
            let raw = format!("{output}_raw");
            run_tool(
                dir,
                &cc,
                &[
                    "-no-pie",
                    "-o",
                    &raw,
                    "btmain.o",
                    "const.o",
                    "-Wl,-T,eh0.ld",
                ],
            );
            let status = Command::new(dir.join(&raw)).status().unwrap();
            assert_eq!(status.signal(), Some(SIGSEGV), "{raw}: {status:?}");
            let output = format!("eh4_{linker}");
            let (code, stdout) = installed_and_run(
                dir,
                bin,
                &[
                    "--format=text",
                    "--no-pie",
                    "-o",
                    &output,
                    "const.trust_ir",
                    "-Wl,btmain.o,-T,eh4.ld",
                ],
            );
            assert!(
                code == Some(0) && stdout.starts_with("v=42 frames="),
                "{output}: {code:?} {stdout}"
            );
            // trust-cg's sections not loaded where the map places them:
            // `(NOLOAD)` `.rodata` (GNU ld and LLD make it zero fill, gold
            // loads it), and `.data` in no segment in an image without
            // section headers (GNU ld and LLD).
            let loaded = "[TCG-LINK-LOADED-BYTES]";
            let output = format!("ronl_{linker}");
            let raw = format!("{output}_raw");
            run_tool(
                dir,
                &cc,
                &[
                    "-static",
                    "-nostdlib",
                    "-o",
                    &raw,
                    "valstart.o",
                    "const.o",
                    "-Wl,-T,ronl.ld",
                ],
            );
            let raw_code = run_program(&dir.join(&raw)).0;
            if linker == "gold" {
                assert_eq!(raw_code, Some(0), "{raw}");
                assert_eq!(
                    installed_and_run(dir, bin, &strs(&args(&output, "ronl.ld"))).0,
                    Some(0),
                    "{output}"
                );
                continue;
            }
            assert_eq!(raw_code, Some(50), "{raw}");
            refused_leaving_output(
                dir,
                bin,
                &strs(&args(&output, "ronl.ld")),
                loaded,
                &[
                    "trust-cg's input section `.rodata` of",
                    "which has contents in its object, does not lie in the 0x0 file bytes",
                ],
            );
            let output = format!("none_nsh_{linker}");
            refused_leaving_output(
                dir,
                bin,
                &[
                    "--format=text",
                    "--static",
                    "--nostdlib",
                    "-o",
                    &output,
                    "val2.trust_ir",
                    "-Wl,valstart.o,--eh-frame-hdr,-T,datanone.ld,-z,nosectionheader",
                ],
                loaded,
                &[
                    "trust-cg's input section `.data` of",
                    "lies in the memory of no PT_LOAD segment",
                ],
            );
            let raw = format!("{output}_raw");
            run_tool(
                dir,
                &cc,
                &[
                    "-static",
                    "-nostdlib",
                    "-o",
                    &raw,
                    "valstart.o",
                    "val2.o",
                    "-Wl,--eh-frame-hdr,-T,datanone.ld,-z,nosectionheader",
                ],
            );
            assert_eq!(run_program(&dir.join(&raw)).0, Some(50), "{raw}");
        }
    }

    /// `main` calls the trust-cg functions of [`LTO_IR`]: exits 0 when they
    /// return 10 and 1000.
    const LTO_MAIN: &str = "#include <stdio.h>\nextern unsigned long tcg_cb(void), \
        tcg_cword(void);\nint main(void) { unsigned long e = tcg_cb(), f = tcg_cword(); \
        printf(\"e=%lu f=%lu\\n\", e, f); return e == 10 && f == 1000 ? 0 : 1; }\n";

    /// trust-cg's `tcg_cb` returns `c_cb(5)`, and `tcg_cword` the external
    /// `c_word`, both defined in LLVM bitcode ([`LTO_BITCODE`]); the
    /// module pins the host target its FFI boundary is linked for
    /// (`TargetInfoRequired`).
    const LTO_IR: &str = "; TrustIr text format v1\nmodule \"tcg_lto\"\ntarget \
        \"aarch64-unknown-linux-gnu\" 8 little\n\nfuncty.0 = () -> \
        (u64)\nfuncty.1 = (u64) -> (u64)\n\nglobal external mut @c_word u64\n\nfn \
        @c_cb(functy.1) {\n}\n\nfn @tcg_cb(functy.0) {\nbb0:\n    %0 = const u64 5\n    %1 = call \
        @func.0(%0)\n    ret %1\n}\n\nfn @tcg_cword(functy.0) {\nbb0:\n    %0 = global_addr \
        @global.0\n    %1 = load u64, ptr %0\n    ret %1\n}\n";

    /// LLVM bitcode (`llvm-as` of the Trust toolchain's LLVM 22.1.2) of
    /// `@c_word = global i64 1000` and `define i64 @c_cb(i64 %x)`, which
    /// returns `2 * x`, in hexadecimal.
    const LTO_BITCODE: &str = "4243c0de351400000d000000620c301cc1c60aac600bad200772e00671e00672d006f2500ff3400f6d00076e\
        10076e00076d400ff2500ff3400f421420530000210c0000a70100000b022100020000002200000007812391\
        41c80449061032399201840c250508191e048b62800c450242920b42641032143808184b0a32328848b06421\
        43868804471c32422471c80811242940868c104b0132648408921c20234388e50019194204192a282a90515c\
        2023b940860c19c307cb1519328c8c24071932622c39c8901123c812880e1d3a644447c81022434602191a00\
        892000000a00000022660410b24282c910524282c99071c250480a092643c605423226080a9a230085222403\
        0123000013b270080779180774b0033a68837a708775708777b80777680376480777a8077c68837370877ad8\
        900be5d006eda007e5d006f020077700077a300772a0077320076d000f72700771a0077320077a300772d006\
        f020077720077a600774a0077640076d900e78a00778a0077320076d900e7160077a100776a0077320076d90\
        0e7640077a600774d006e910077280077a10077280076de00e7320077a600774d006b310077280076d600aee\
        300772a0f48010210964c8489111402384618d6572fc6521804161001c521984000000000000000000000000\
        a000121b040acf06000064810000000005000000321e980819114c908c092647c604434a413f0000b1180000\
        e10000003308801cc4e11c6614013d88433884c38c4280077978077398710ce6000fed100ef4800e330c421e\
        c2c11dcea11c6630053d88433884831bcc033dc8433d8c033dcc788c7470077b08077948877070077a700376\
        788770208719cc110eec900ee1300f6e300fe3f00ef0500e3310c41dde211cd8211dc2611e6630893bbc833b\
        d04339b4033cbc833c84033bccf0147660077b680737688772680737808770908770600776280776f8057678\
        877780875f08877118877298877998812ceef00eeee00ef5c00eec300362c8a11ce4a11ccca11ce4a11cdc61\
        1cca211cc4811dca6106d6904339c84339984339c84339b8c33894433888033b94c32fbc833cfc823bd4033b\
        b0c30cc7698770588772708374680778608774188774a08719ce530fee000ff2500ee4900ee3400fe1200eec\
        500e3320281ddcc11ec2411ed2211cdc811edce01ce4e11dea011e66185138b0433a9c833bcc50247660077b\
        68073760877778077898514cf4900ff0500e331e6a1eca611ce8211ddec11d7e011ee4a11ccc211df0610654\
        858338ccc33bb0433dd04339fcc23ce4433b88c33bb0c38cc50a877998877718877408077a28077298815ce3\
        100eecc00ee5500ef33023c1d2411ee4e117d8e11dde011e6648193bb0833db4831b84c3388c4339ccc33cb8\
        c139c8c33bd4033ccc48b471080776600771088771588719dbc60eec600fede006f0200fe5300fe5200ff650\
        0e6e100ee3300ee5300ff3e006e9e00ee4500ef83023e2ec611cc2811dd8e117ec211de6211dc4211dd8211d\
        e8211f66209d3bbc433db80339948339cc58bc7070077778077a08077a488777708719cbe70eef300fe1e00e\
        e9400fe9a00fe530c3010373a8077718875f988770708774a08774d087729881844139e0c338b0433d904339\
        cc40c4a01dcaa11de0411edec11c662463300ee1c00eec300fe9400fe5304321837518077348875fa0877c80\
        877298b194013c8cc33c94c338d0433abc833bccc38cc50c48211542611ee6211dcec11d528114664c67300e\
        ef200fefe006ef500ff4300fe9400ee5e006e6200fe1d00ee530a3408376680779088719521ab8c33b84033b\
        a44338cc831b84033990833ccc033c84c33894c30c460dc6211cd8811dcaa11c7e811ef2011eca61c6b106ee\
        f00ee6200fe5500e33123618877080077aa8077928877998c1b44138b0033bbcc338fc023dbcc33a94833bcc\
        68dc201dda011ed8211dc6211de8c10de4a11ccc01000000a9180000370000000b0a7228877780077a587098\
        433db8c338b04339d0c382e61cc6a10de8411ec2c11de6211de8211ddec11d1634e3600ee7500fe1200fe440\
        0fe1200fe7500ef4b08081077928877060077678877108077a28077258709cc338b4013ba4833d94c3026b1c\
        d8211cdce11cdc201ce4611cdc201ce8811ec2611cd0a11cc8611cc2811dd861c1010ff4200fe1500ff4800e\
        0b8875180773488705cf38bc833bd84339c8c33994833b8c43398c033dc8033b2c28c2811dd2e11cdc61c144\
        0ee5100ee3400fe9600fe1400fe9f00eeed006f3900fed200eefc00e00000000d11000000600000007cc3ca4\
        833b9c033b94033da0833c94433890c301000000612800000a000000230882b0400000000100000094220000\
        4808a405c18100000200000036105c5610440000000000007120000003000000320e10228401a70300000000\
        00000000650c0000250000001203942801000000030000000a000000400000004c0000000100000058000000\
        00000000580000000200000088000000000000004a0000001900000063000000060000000a00000000000000\
        880000000000000000000000020000000000000006000000040000000600000004000000ffffffff00240000\
        00000000060000000000000006000000ffffffff00040000000000005d0c00001e000000120394e900000000\
        635f776f7264635f636232322e312e322d727573742d302e312e302d74727573742066613933383931313434\
        303036356566346466633363613439333038346434343733353263306434616172636836342d756e6b6e6f77\
        6e2d6c696e75782d676e756c746f2e6c6c00000000000000";

    /// The same module as ThinLTO bitcode (`opt --thinlto-bc`).
    const THIN_BITCODE: &str = "4243c0de351400000d000000620c301cc1c60aac600bad200772e00671e00672d006f2500ff3400f6d00076e\
        10076e00076d400ff2500ff3400f421420530000210c0000e30100000b022100020000002200000007812391\
        41c80449061032399201840c250508191e048b62800c450242920b42641032143808184b0a32328848b06421\
        43868804471c32422471c80811242940868c104b0132648408921c20234388e50019194204192a282a90515c\
        2023b940860c19c307cb1519328c8c24071932622c39c8901123c812880e1d3a644447c81022434602191a00\
        892000000b00000022660410b24282c910524282c99071c250480a092643c605423226080c9a230085222403\
        017304603002000013b270080779180774b0033a68837a708775708777b80777680376480777a8077c688373\
        70877ad8900be5d006eda007e5d006f020077700077a300772a0077320076d000f72700771a0077320077a30\
        0772d006f020077720077a600774a0077640076d900e78a00778a0077320076d900e7160077a100776a00773\
        20076d900e7640077a600774d006e910077280077a10077280076de00e7320077a600774d006b31007728007\
        6d600aee300772a0f48010210964c8489111402384618d6572fc6521804161001c5219840000000000000000\
        00000000a000121b040aa707000064810000000006000000321e980c19114c908c092647c604434a413f104b\
        60040000b1180000e10000003308801cc4e11c6614013d88433884c38c4280077978077398710ce6000fed10\
        0ef4800e330c421ec2c11dcea11c6630053d88433884831bcc033dc8433d8c033dcc788c7470077b08077948\
        877070077a700376788770208719cc110eec900ee1300f6e300fe3f00ef0500e3310c41dde211cd8211dc261\
        1e6630893bbc833bd04339b4033cbc833c84033bccf0147660077b6807376887726807378087709087706007\
        76280776f8057678877780875f08877118877298877998812ceef00eeee00ef5c00eec300362c8a11ce4a11c\
        cca11ce4a11cdc611cca211cc4811dca6106d6904339c84339984339c84339b8c33894433888033b94c32fbc\
        833cfc823bd4033bb0c30cc7698770588772708374680778608774188774a08719ce530fee000ff2500ee490\
        0ee3400fe1200eec500e3320281ddcc11ec2411ed2211cdc811edce01ce4e11dea011e66185138b0433a9c83\
        3bcc50247660077b68073760877778077898514cf4900ff0500e331e6a1eca611ce8211ddec11d7e011ee4a1\
        1ccc211df0610654858338ccc33bb0433dd04339fcc23ce4433b88c33bb0c38cc50a87799887771887740807\
        7a28077298815ce3100eecc00ee5500ef33023c1d2411ee4e117d8e11dde011e6648193bb0833db4831b84c3\
        388c4339ccc33cb8c139c8c33bd4033ccc48b471080776600771088771588719dbc60eec600fede006f0200f\
        e5300fe5200ff6500e6e100ee3300ee5300ff3e006e9e00ee4500ef83023e2ec611cc2811dd8e117ec211de6\
        211dc4211dd8211de8211f66209d3bbc433db80339948339cc58bc7070077778077a08077a488777708719cb\
        e70eef300fe1e00ee9400fe9a00fe530c3010373a8077718875f988770708774a08774d087729881844139e0\
        c338b0433d904339cc40c4a01dcaa11de0411edec11c662463300ee1c00eec300fe9400fe530432183751807\
        7348875fa0877c80877298b194013c8cc33c94c338d0433abc833bccc38cc50c48211542611ee6211dcec11d\
        528114664c67300eef200fefe006ef500ff4300fe9400ee5e006e6200fe1d00ee530a3408376680779088719\
        521ab8c33b84033ba44338cc831b84033990833ccc033c84c33894c30c460dc6211cd8811dcaa11c7e811ef2\
        011eca61c6b106eef00ee6200fe5500e33123618877080077aa8077928877998c1b44138b0033bbcc338fc02\
        3dbcc33a94833bcc68dc201dda011ed8211dc6211de8c10de4a11ccc01000000792000001a000000921e4820\
        43880c19096464c8c920818c0432464646138142a090f1c4c8083942868c62405800000012000000456e6162\
        6c6553706c69744c544f556e697400002308c430824010330c4230c8486082326263b36b73697b23ab632b73\
        31630b3b9b1b251800000000a9180000370000000b0a7228877780077a587098433db8c338b04339d0c382e6\
        1cc6a10de8411ec2c11de6211de8211ddec11d1634e3600ee7500fe1200fe4400fe1200fe7500ef4b0808107\
        7928877060077678877108077a28077258709cc338b4013ba4833d94c3026b1cd8211cdce11cdc201ce4611c\
        dc201ce8811ec2611cd0a11cc8611cc2811dd861c1010ff4200fe1500ff4800e0b8875180773488705cf38bc\
        833bd84339c8c33994833b8c43398c033dc8033b2c28c2811dd2e11cdc61c1440ee5100ee3400fe9600fe140\
        0fe9f00eeed006f3900fed200eefc00e00000000d11000000600000007cc3ca4833b9c033b94033da0833c94\
        433890c301000000612800000a000000230882b04000000001000000942200004808a405c181000002000000\
        56105c761044000000000000a120000016000000a304cc5001202404198142a0105580102142448810216284\
        449d20448610112244881821290708913142625e102243c408097940880c21292d08113242426a103242426e\
        103142328218a10a00100000000e0008060000007120000003000000320e10228401c503000000008b8abed7\
        cdde53f7d274f5e057d35bfdf2d165ebea5edfdf16070000650c000025000000120394280100000003000000\
        0a000000400000004c000000010000005800000000000000580000000200000088000000000000004a000000\
        1900000063000000060000000a00000000000000880000000000000000000000020000000000000006000000\
        040000000600000004000000ffffffff0024000000000000060000000000000006000000ffffffff00040000\
        000000005d0c00001e000000120394e900000000635f776f7264635f636232322e312e322d727573742d302e\
        312e302d74727573742066613933383931313434303036356566346466633363613439333038346434343733\
        353263306434616172636836342d756e6b6e6f776e2d6c696e75782d676e756c746f2e6c6c00000000000000";

    /// [`LTO_BITCODE`]'s module with libgcc's outline-atomics helpers
    /// `__aarch64_cas8_acq_rel`, `__aarch64_cas4_acq` and
    /// `__aarch64_swp8_acq_rel` defined too: its compare-and-swap never
    /// stores and returns a value other than the expected one, so a lock
    /// taken through it is never taken (the second verifier's `evil2.ll`).
    const EVIL_BITCODE: &str = "4243c0de351400000d000000620c301cc1c60aac600bad200772e00671e00672d006f2500ff3400f6d00076e\
        10076e00076d400ff2500ff3400f421420530000210c0000ed0100000b022100020000002200000007812391\
        41c80449061032399201840c250508191e048b628010450242920b42841032143808184b0a32428848b06421\
        43868804471c32422471c80811242940868c104b0132648408921c20234488e50019214204192a282a90515c\
        2023b940860c19c307cb1519428c8c24071932622c39c8901123c812880e1d3a644447c81022434602191a00\
        892000000e00000022660410b242820911524282099171c250480a092644c60542422608129a230085224414\
        2222608e000c0a4144508608180818010000000013b270080779180774b0033a68837a708775708777b80777\
        680376480777a8077c68837370877ad8900be5d006eda007e5d006f020077700077a300772a0077320076d00\
        0f72700771a0077320077a300772d006f020077720077a600774a0077640076d900e78a00778a0077320076d\
        900e7160077a100776a0077320076d900e7640077a600774d006e910077280077a10077280076de00e732007\
        7a600774d006b310077280076d600aee300772a0f48010210964c84891114023846111a24216db5f16021814\
        0cc0219541080000000000000000000000000a30a452ac010000000000000000000000400186546020150000\
        000000000000000000000a30a49203cb0000000000000000000000005000890d0285ef030000b24005000000\
        321e980c19114c908c092647c604438a827e0000b1180000e10000003308801cc4e11c6614013d88433884c3\
        8c4280077978077398710ce6000fed100ef4800e330c421ec2c11dcea11c6630053d88433884831bcc033dc8\
        433d8c033dcc788c7470077b08077948877070077a700376788770208719cc110eec900ee1300f6e300fe3f0\
        0ef0500e3310c41dde211cd8211dc2611e6630893bbc833bd04339b4033cbc833c84033bccf0147660077b68\
        0737688772680737808770908770600776280776f8057678877780875f08877118877298877998812ceef00e\
        eee00ef5c00eec300362c8a11ce4a11ccca11ce4a11cdc611cca211cc4811dca6106d6904339c84339984339\
        c84339b8c33894433888033b94c32fbc833cfc823bd4033bb0c30cc769877058877270837468077860877418\
        8774a08719ce530fee000ff2500ee4900ee3400fe1200eec500e3320281ddcc11ec2411ed2211cdc811edce0\
        1ce4e11dea011e66185138b0433a9c833bcc50247660077b68073760877778077898514cf4900ff0500e331e\
        6a1eca611ce8211ddec11d7e011ee4a11ccc211df0610654858338ccc33bb0433dd04339fcc23ce4433b88c3\
        3bb0c38cc50a877998877718877408077a28077298815ce3100eecc00ee5500ef33023c1d2411ee4e117d8e1\
        1dde011e6648193bb0833db4831b84c3388c4339ccc33cb8c139c8c33bd4033ccc48b4710807766007710887\
        71588719dbc60eec600fede006f0200fe5300fe5200ff6500e6e100ee3300ee5300ff3e006e9e00ee4500ef8\
        3023e2ec611cc2811dd8e117ec211de6211dc4211dd8211de8211f66209d3bbc433db80339948339cc58bc70\
        70077778077a08077a488777708719cbe70eef300fe1e00ee9400fe9a00fe530c3010373a8077718875f9887\
        70708774a08774d087729881844139e0c338b0433d904339cc40c4a01dcaa11de0411edec11c662463300ee1\
        c00eec300fe9400fe5304321837518077348875fa0877c80877298b194013c8cc33c94c338d0433abc833bcc\
        c38cc50c48211542611ee6211dcec11d528114664c67300eef200fefe006ef500ff4300fe9400ee5e006e620\
        0fe1d00ee530a3408376680779088719521ab8c33b84033ba44338cc831b84033990833ccc033c84c33894c3\
        0c460dc6211cd8811dcaa11c7e811ef2011eca61c6b106eef00ee6200fe5500e33123618877080077aa80779\
        28877998c1b44138b0033bbcc338fc023dbcc33a94833bcc68dc201dda011ed8211dc6211de8c10de4a11ccc\
        01000000a9180000370000000b0a7228877780077a587098433db8c338b04339d0c382e61cc6a10de8411ec2\
        c11de6211de8211ddec11d1634e3600ee7500fe1200fe4400fe1200fe7500ef4b08081077928877060077678\
        877108077a28077258709cc338b4013ba4833d94c3026b1cd8211cdce11cdc201ce4611cdc201ce8811ec261\
        1cd0a11cc8611cc2811dd861c1010ff4200fe1500ff4800e0b8875180773488705cf38bc833bd84339c8c339\
        94833b8c43398c033dc8033b2c28c2811dd2e11cdc61c1440ee5100ee3400fe9600fe1400fe9f00eeed006f3\
        900fed200eefc00e00000000d11000000600000007cc3ca4833b9c033b94033da0833c94433890c301000000\
        612800000a000000230882b04000000001000000144500004808a405c18100000200000066105c8610440000\
        000000006128000012000000230882b0400000000100000014250000230d0c212000234085c02d080e040000\
        08000000a63038cb600608713d8430118321048f1d1c0321211131d8c2100003000000000000000061280000\
        12000000230882b0400000000100000044250000230d0c811800234085c02d080e04000008000000a63038cb\
        600608713d8430118321048f1d1c0321211131d8c210000300000000000000006128000009000000230882b1\
        074720008011102d080e040003000000863038cb6006416507c10300000000007120000005000000320e1022\
        8401b80328403c8003d80348c03e000000000000650c000037000000120394b0010000000300000048000000\
        400000004c0000000100000058000000000000005800000005000000d0000000000000008800000019000000\
        a1000000080000000a00000000000000d0000000000000000000000005000000000000000600000004000000\
        0600000004000000ffffffff002400000a000000160000000a00000016000000ffffffff8024000020000000\
        120000002000000012000000ffffffff8024000032000000160000003200000016000000ffffffff80240000\
        00000000060000000000000006000000ffffffff00040000000000005d0c00002e0000001203946901000000\
        635f776f7264635f63625f5f616172636836345f636173385f6163715f72656c5f5f616172636836345f6361\
        73345f6163715f5f616172636836345f737770385f6163715f72656c32322e312e322d727573742d302e312e\
        302d747275737420666139333839313134343030363565663464666333636134393330383464343437333532\
        63306434616172636836342d756e6b6e6f776e2d6c696e75782d676e756576696c322e6c6c00000000000000";

    /// [`EVIL_BITCODE`]'s module as ThinLTO bitcode (`opt --thinlto-bc` of
    /// the Trust toolchain's LLVM 22.1.2).
    const EVIL_THIN_BITCODE: &str = "4243c0de351400000d000000620c301cc1c60aac600bad200772e00671e00672d006f2500ff3400f6d00076e\
        10076e00076d400ff2500ff3400f421420530000210c00002a0200000b022100020000002200000007812391\
        41c80449061032399201840c250508191e048b628010450242920b42841032143808184b0a32428848b06421\
        43868804471c32422471c80811242940868c104b0132648408921c20234488e50019214204192a282a90515c\
        2023b940860c19c307cb1519428c8c24071932622c39c8901123c812880e1d3a644447c81022434602191a00\
        892000000e00000022660410b242820911524282099171c250480a092644c60542422608129a230085224414\
        2222608e000c0a4144508608180818010000000013b270080779180774b0033a68837a708775708777b80777\
        680376480777a8077c68837370877ad8900be5d006eda007e5d006f020077700077a300772a0077320076d00\
        0f72700771a0077320077a300772d006f020077720077a600774a0077640076d900e78a00778a0077320076d\
        900e7160077a100776a0077320076d900e7640077a600774d006e910077280077a10077280076de00e732007\
        7a600774d006b310077280076d600aee300772a0f48010210964c84891114023846111a24216db5f16021814\
        0cc0219541080000000000000000000000000a30a452ac010000000000000000000000400186546020150000\
        000000000000000000000a30a49203cb0000000000000000000000005000890d02855d040000b24006000000\
        321e981019114c908c092647c604438a827e202a81110000b1180000e10000003308801cc4e11c6614013d88\
        433884c38c4280077978077398710ce6000fed100ef4800e330c421ec2c11dcea11c6630053d88433884831b\
        cc033dc8433d8c033dcc788c7470077b08077948877070077a700376788770208719cc110eec900ee1300f6e\
        300fe3f00ef0500e3310c41dde211cd8211dc2611e6630893bbc833bd04339b4033cbc833c84033bccf01476\
        60077b680737688772680737808770908770600776280776f8057678877780875f0887711887729887799881\
        2ceef00eeee00ef5c00eec300362c8a11ce4a11ccca11ce4a11cdc611cca211cc4811dca6106d6904339c843\
        39984339c84339b8c33894433888033b94c32fbc833cfc823bd4033bb0c30cc7698770588772708374680778\
        608774188774a08719ce530fee000ff2500ee4900ee3400fe1200eec500e3320281ddcc11ec2411ed2211cdc\
        811edce01ce4e11dea011e66185138b0433a9c833bcc50247660077b68073760877778077898514cf4900ff0\
        500e331e6a1eca611ce8211ddec11d7e011ee4a11ccc211df0610654858338ccc33bb0433dd04339fcc23ce4\
        433b88c33bb0c38cc50a877998877718877408077a28077298815ce3100eecc00ee5500ef33023c1d2411ee4\
        e117d8e11dde011e6648193bb0833db4831b84c3388c4339ccc33cb8c139c8c33bd4033ccc48b47108077660\
        0771088771588719dbc60eec600fede006f0200fe5300fe5200ff6500e6e100ee3300ee5300ff3e006e9e00e\
        e4500ef83023e2ec611cc2811dd8e117ec211de6211dc4211dd8211de8211f66209d3bbc433db80339948339\
        cc58bc7070077778077a08077a488777708719cbe70eef300fe1e00ee9400fe9a00fe530c3010373a8077718\
        875f988770708774a08774d087729881844139e0c338b0433d904339cc40c4a01dcaa11de0411edec11c6624\
        63300ee1c00eec300fe9400fe5304321837518077348875fa0877c80877298b194013c8cc33c94c338d0433a\
        bc833bccc38cc50c48211542611ee6211dcec11d528114664c67300eef200fefe006ef500ff4300fe9400ee5\
        e006e6200fe1d00ee530a3408376680779088719521ab8c33b84033ba44338cc831b84033990833ccc033c84\
        c33894c30c460dc6211cd8811dcaa11c7e811ef2011eca61c6b106eef00ee6200fe5500e3312361887708007\
        7aa8077928877998c1b44138b0033bbcc338fc023dbcc33a94833bcc68dc201dda011ed8211dc6211de8c10d\
        e4a11ccc01000000792000001a000000921e482043880c19096464c8c920818c0432464646138142a090f1c4\
        c8083942868c62405800000012000000456e61626c6553706c69744c544f556e697400002308843182401c33\
        0c4230c8486082326263b36b73697b23ab632b7331630b3b9b1b251800000000a9180000370000000b0a7228\
        877780077a587098433db8c338b04339d0c382e61cc6a10de8411ec2c11de6211de8211ddec11d1634e3600e\
        e7500fe1200fe4400fe1200fe7500ef4b08081077928877060077678877108077a28077258709cc338b4013b\
        a4833d94c3026b1cd8211cdce11cdc201ce4611cdc201ce8811ec2611cd0a11cc8611cc2811dd861c1010ff4\
        200fe1500ff4800e0b8875180773488705cf38bc833bd84339c8c33994833b8c43398c033dc8033b2c28c281\
        1dd2e11cdc61c1440ee5100ee3400fe9600fe1400fe9f00eeed006f3900fed200eefc00e00000000d1100000\
        0600000007cc3ca4833b9c033b94033da0833c94433890c301000000612800000a000000230882b040000000\
        01000000144500004808a405c18100000200000086105ca610440000000000006128000012000000230882b0\
        400000000100000014250000230d0c212000234085c02d080e04000008000000c63038cb600808713d843011\
        8329048f251c032121113158c31000030000000000000000612800000f000000230882910646400c801120c2\
        e01604070200000008000000b63038cb600808713d8430118329048f251c032121113118c310000300000000\
        000000006128000009000000230882b1074720008011102d080e040003000000a63038cb6008416509c10300\
        00000000a12000001b000000a304cc5001202404198142a0105580102142448810216284449d204486101122\
        44881821290708913142625e102243c408097940880c21292d08113242426a103242426e103142328218a10a\
        00100000004a0060000000a80180010000a008000400008003008201000000007120000005000000320e1022\
        8401d50328103e8003f50348604800008b0a99e77950aafd7af6eb619d797a9d05b5a57f780ee0daa6c35c00\
        650c000037000000120394b0010000000300000048000000400000004c000000010000005800000000000000\
        5800000005000000d0000000000000008800000019000000a1000000080000000a00000000000000d0000000\
        0000000000000000050000000000000006000000040000000600000004000000ffffffff002400000a000000\
        160000000a00000016000000ffffffff8024000020000000120000002000000012000000ffffffff80240000\
        32000000160000003200000016000000ffffffff8024000000000000060000000000000006000000ffffffff\
        00040000000000005d0c00002e0000001203946901000000635f776f7264635f63625f5f616172636836345f\
        636173385f6163715f72656c5f5f616172636836345f636173345f6163715f5f616172636836345f73777038\
        5f6163715f72656c32322e312e322d727573742d302e312e302d747275737420666139333839313134343030\
        36356566346466633363613439333038346434343733353263306434616172636836342d756e6b6e6f776e2d\
        6c696e75782d676e756576696c322e6c6c00000000000000";

    /// Decode a hexadecimal string.
    fn unhex(text: &str) -> Vec<u8> {
        (0..text.len())
            .step_by(2)
            .map(|at| u8::from_str_radix(&text[at..at + 2], 16).unwrap())
            .collect()
    }

    /// The twelfth closure audit's LLVM bitcode findings, through LLD 22.1.6
    /// (GNU ld 2.42 and gold 2.42 read no bitcode without an LTO plugin):
    /// - a static image whose bitcode archive member defined libgcc's
    ///   outline-atomics helpers (`__aarch64_cas8_acq_rel`, which the C
    ///   runtime's frame registration calls) was installed and hung in
    ///   `__register_frame_info`, while its ELF twin was refused: the driver
    ///   read no bitcode input. Now the link that names bitcode runs again
    ///   keeping the objects LLD compiles from it (`--lto-obj-path`), and
    ///   that link's image is checked and installed: this one is refused as
    ///   `[TCG-LINK-IRELATIVE-UNAPPLIED]`, naming the object LLD compiled and
    ///   the helper it defines; the raw link outside the driver hangs;
    /// - every static link with a direct bitcode input was refused as if the
    ///   bitcode were a linker script. Static links with full and ThinLTO
    ///   bitcode, a bitcode archive, and a PIE with bitcode are installed
    ///   and run now.
    ///
    /// Since the thirteenth closure audit the link the driver checks puts
    /// its own `--lto-obj-path` and an empty `--thinlto-cache-dir=` after
    /// the user's options, so links with a ThinLTO cache (cold and warm)
    /// and with an object path of the user's (which still receives the
    /// first link's objects) are read and installed instead of refused, and
    /// the outline-atomics member is refused by name through such a path
    /// too; shared objects of full and ThinLTO bitcode run under their C
    /// user; and with `--fat-lto-objects` the object LLD compiles from a fat
    /// LTO object's `.llvm.lto` bitcode is what is read and run (without
    /// the option, the object's own code runs).
    #[test]
    fn llvm_bitcode_inputs_are_read_through_the_objects_lld_compiles() {
        let Some(lld) = lld_dir() else {
            return;
        };
        let directory = tempfile::tempdir().unwrap();
        let dir = directory.path();
        let lld_bin = lld_cc(dir, &lld);
        let bin = Some(lld_bin.as_path());
        for (name, bytes) in [
            ("lto.bc", unhex(LTO_BITCODE)),
            ("thin.bc", unhex(THIN_BITCODE)),
            ("evil.bc", unhex(EVIL_BITCODE)),
            ("lto.trust_ir", LTO_IR.as_bytes().to_vec()),
            ("ltomain.c", LTO_MAIN.as_bytes().to_vec()),
        ] {
            fs::write(dir.join(name), bytes).unwrap();
        }
        run_tool(dir, "cc", &["-c", "-O1", "-o", "ltomain.o", "ltomain.c"]);
        run_tool(dir, "ar", &["rcs", "libbc.a", "lto.bc"]);
        run_tool(dir, "ar", &["rcs", "libevil.a", "evil.bc"]);
        let result = trust_cg_on(
            None,
            dir,
            &["--format=text", "-c", "-o", "lto.o", "lto.trust_ir"],
        );
        assert!(result.status.success(), "{}", stderr(&result));
        let right = (Some(0), "e=10 f=1000\n".to_string());
        for (output, extra, group) in [
            ("bc_st", &["--static"][..], "-Wl,ltomain.o,lto.bc"),
            ("thin_st", &["--static"], "-Wl,ltomain.o,thin.bc"),
            ("ar_st", &["--static"], "-Wl,ltomain.o,libbc.a"),
            ("bc_pie", &[], "-Wl,ltomain.o,lto.bc"),
            ("thin_np", &["--no-pie"], "-Wl,ltomain.o,thin.bc"),
        ] {
            let mut args = vec!["--format=text"];
            args.extend(extra);
            args.extend(["-o", output, "lto.trust_ir", group]);
            assert_eq!(installed_and_run(dir, bin, &args), right, "{output}");
        }
        let tag = "[TCG-LINK-IRELATIVE-UNAPPLIED]";
        let refused = |output: &str, group: &str, texts: &[&str]| {
            let args = [
                "--format=text",
                "--static",
                "-o",
                output,
                "lto.trust_ir",
                group,
            ];
            refused_leaving_output(dir, bin, &args, tag, texts);
        };
        refused(
            "evil_st",
            "-Wl,ltomain.o,libevil.a",
            &[
                "(an object LLD compiled from the LLVM bitcode input",
                "libevil.a(evil.bc)",
                "defines __aarch64_cas",
            ],
        );
        let cc = lld_bin.join("cc").display().to_string();
        run_tool(
            dir,
            &cc,
            &[
                "-static",
                "-o",
                "evil_raw",
                "ltomain.o",
                "lto.o",
                "libevil.a",
            ],
        );
        let hung = Command::new("timeout")
            .args(["10"])
            .arg(dir.join("evil_raw"))
            .status()
            .unwrap();
        assert_eq!(hung.code(), Some(124), "{hung:?}");
        // A ThinLTO cache, and an object path of the user's: the driver's
        // own `--lto-obj-path` and an empty `--thinlto-cache-dir=` come
        // after them in the link it checks, so it reads every object LLD
        // compiles, and these links are installed and run (a cold and then
        // a warm cache). The user's path holds the objects the first link
        // wrote.
        fs::create_dir(dir.join("cache")).unwrap();
        fs::create_dir(dir.join("objs")).unwrap();
        let cache = "-Wl,ltomain.o,thin.bc,--thinlto-cache-dir=cache";
        for (output, extra, group) in [
            ("cache_st", &["--static"][..], cache),
            ("cache_st_warm", &["--static"], cache),
            ("cache_pie", &[], cache),
            (
                "own_st",
                &["--static"],
                "-Wl,ltomain.o,lto.bc,--lto-obj-path=objs/mine.o",
            ),
            (
                "own_thin_np",
                &["--no-pie"],
                "-Wl,ltomain.o,thin.bc,--plugin-opt=obj-path=objs/thin.o",
            ),
        ] {
            let mut args = vec!["--format=text"];
            args.extend(extra);
            args.extend(["-o", output, "lto.trust_ir", group]);
            assert_eq!(installed_and_run(dir, bin, &args), right, "{output}");
        }
        assert!(fs::read_dir(dir.join("cache")).unwrap().next().is_some());
        for object in ["mine.o", "thin.o1"] {
            let bytes = fs::read(dir.join("objs").join(object)).unwrap();
            assert!(bytes.starts_with(b"\x7fELF"), "{object}");
        }
        // The outline-atomics member through the user's object path: its
        // object is read, and the link refused by name.
        refused(
            "evil_own_st",
            "-Wl,ltomain.o,libevil.a,--lto-obj-path=objs/evil.o",
            &[
                "(an object LLD compiled from the LLVM bitcode input",
                "libevil.a(evil.bc)",
                "defines __aarch64_cas",
            ],
        );
        // A shared object of trust-cg's code and the bitcode, full and
        // ThinLTO (with the cache), whose C user runs.
        for (library, group) in [
            ("libbc.so", "-Wl,lto.bc"),
            ("libthin.so", "-Wl,thin.bc,--thinlto-cache-dir=cache"),
        ] {
            let result = trust_cg_on(
                bin,
                dir,
                &[
                    "--format=text",
                    "-shared",
                    "--relocation-model",
                    "pic",
                    "-o",
                    library,
                    "lto.trust_ir",
                    group,
                ],
            );
            assert!(result.status.success(), "{library}: {}", stderr(&result));
            let user = format!("user_{library}");
            let path = dir.join(library).display().to_string();
            let rpath = format!("-Wl,-rpath,{}", dir.display());
            run_tool(dir, "cc", &["-o", &user, "ltomain.o", &path, &rpath]);
            assert_eq!(run_program(&dir.join(&user)), right, "{library}");
        }
        // LLVM's fat LTO object: its own code returns other values (`c_cb`
        // triples, `c_word` is 7); with `--fat-lto-objects` LLD links what
        // it compiles from the object's `.llvm.lto` bitcode instead, which
        // the driver reads, and the program prints the bitcode's values.
        fs::write(dir.join("fat.c"), LTO_FAT_NATIVE).unwrap();
        run_tool(
            dir,
            "cc",
            &["-c", "-O1", "-fPIC", "-o", "fat_native.o", "fat.c"],
        );
        run_tool(
            dir,
            "objcopy",
            &[
                "--add-section",
                ".llvm.lto=lto.bc",
                "--set-section-flags",
                ".llvm.lto=exclude",
                "fat_native.o",
                "fat.o",
            ],
        );
        for (output, extra) in [("fat_pie", &[][..]), ("fat_st", &["--static"])] {
            let mut args = vec!["--format=text"];
            args.extend(extra);
            args.extend([
                "-o",
                output,
                "lto.trust_ir",
                "-Wl,ltomain.o,fat.o,--fat-lto-objects",
            ]);
            assert_eq!(installed_and_run(dir, bin, &args), right, "{output}");
        }
        let args = [
            "--format=text",
            "-o",
            "fat_off",
            "lto.trust_ir",
            "-Wl,ltomain.o,fat.o",
        ];
        assert_eq!(
            installed_and_run(dir, bin, &args),
            (Some(1), "e=15 f=7\n".to_string())
        );
    }

    /// [`LTO_BITCODE`]'s `c_cb` and `c_word` with other values (`c_cb`
    /// triples, `c_word` is 7): the native code of a fat LTO object whose
    /// `.llvm.lto` section holds [`LTO_BITCODE`].
    const LTO_FAT_NATIVE: &str =
        "unsigned long c_word = 7;\nunsigned long c_cb(unsigned long x) { return 3 * x; }\n";

    /// LLVM bitcode (`llvm-as` of the Trust toolchain's LLVM 22.1.2) whose
    /// module asm defines `f_gb`, which loads `dv_last` through its GOT slot
    /// as GCC's small-PIC model does (`adrp x28, _GLOBAL_OFFSET_TABLE_`,
    /// `ldr x0, [x28, #:gotpage_lo15:dv_last]`, `R_AARCH64_LD64_GOTPAGE_LO15`)
    /// and returns the word there, beside `gb_marker`, which returns 7.
    /// `dv_last` (4242) and the slots before it come from
    /// [`gb_slots_source`]'s object.
    const GB_BITCODE: &str = "4243c0de351400000d000000620c301cc1c60aac600bad200772e00671e00672d006f2500ff3400f6d00076e\
        10076e00076d400ff2500ff3400f421420530000210c0000c40100000b022100020000002200000007812391\
        41c80449061032399201840c250508191e048b62800c450242920b42641032143808184b0a32328848b06421\
        43868804471c32422471c80811242940868c104b0132648408921c20234388e50019194204192a282a90515c\
        2023b940860c19c307cb1519328c8c24071932622c39c8901123c812880e1d3a644447c81022434602191a00\
        892000000a00000022660410b24282c910524282c99071c250480a092643c605423226080a9a230083126420\
        6004000013b270080779180774b0033a68837a708775708777b80777680376480777a8077c68837370877ad8\
        8007e5d006eda007e5d006e980077a80077a300772d006e9100776a0077160077a300772d006e9600774a007\
        7640076d900e71200778a00771200778d006ee300772a0077640076d300b71200778d006a6e00e73200723c0\
        2271037a28077ca00725718373608777100776000373f8857310072571037ac8077828073030875f38077160\
        0330280373a8077718077a4887777007c51c7ee11cc4410f94241cc8411ee0010cf0410ef0800dc0e0174e81\
        155e41144281157ee1154cc11466a11468e1176821144481154ae11794841dc8411ec0001fe0800dc06017f0\
        410ef0800dc0600cf4e01cde811ee0211ccea11c7e811dde210eea400fc8c11e7e811dc2611ee8a11794841d\
        c8411ec0001fe0800dc06017f0010e7a4149e4a11ce84149dc601ed2411fca010ccce117ce411cd8000cdca0\
        0dcce117ce411c148d1086548c40628065f197654805240200000000000000000000004002486c10280a1d00\
        00108b01e10000003308801cc4e11c6614013d88433884c38c4280077978077398710ce6000fed100ef4800e\
        330c421ec2c11dcea11c6630053d88433884831bcc033dc8433d8c033dcc788c7470077b0807794887707007\
        7a700376788770208719cc110eec900ee1300f6e300fe3f00ef0500e3310c41dde211cd8211dc2611e663089\
        3bbc833bd04339b4033cbc833c84033bccf0147660077b680737688772680737808770908770600776280776\
        f8057678877780875f08877118877298877998812ceef00eeee00ef5c00eec300362c8a11ce4a11ccca11ce4\
        a11cdc611cca211cc4811dca6106d6904339c84339984339c84339b8c33894433888033b94c32fbc833cfc82\
        3bd4033bb0c30cc7698770588772708374680778608774188774a08719ce530fee000ff2500ee4900ee3400f\
        e1200eec500e3320281ddcc11ec2411ed2211cdc811edce01ce4e11dea011e66185138b0433a9c833bcc5024\
        7660077b68073760877778077898514cf4900ff0500e331e6a1eca611ce8211ddec11d7e011ee4a11ccc211d\
        f0610654858338ccc33bb0433dd04339fcc23ce4433b88c33bb0c38cc50a877998877718877408077a280772\
        98815ce3100eecc00ee5500ef33023c1d2411ee4e117d8e11dde011e6648193bb0833db4831b84c3388c4339\
        ccc33cb8c139c8c33bd4033ccc48b471080776600771088771588719dbc60eec600fede006f0200fe5300fe5\
        200ff6500e6e100ee3300ee5300ff3e006e9e00ee4500ef83023e2ec611cc2811dd8e117ec211de6211dc421\
        1dd8211de8211f66209d3bbc433db80339948339cc58bc7070077778077a08077a488777708719cbe70eef30\
        0fe1e00ee9400fe9a00fe530c3010373a8077718875f988770708774a08774d087729881844139e0c338b043\
        3d904339cc40c4a01dcaa11de0411edec11c662463300ee1c00eec300fe9400fe5304321837518077348875f\
        a0877c80877298b194013c8cc33c94c338d0433abc833bccc38cc50c48211542611ee6211dcec11d52811466\
        4c67300eef200fefe006ef500ff4300fe9400ee5e006e6200fe1d00ee530a3408376680779088719521ab8c3\
        3b84033ba44338cc831b84033990833ccc033c84c33894c30c460dc6211cd8811dcaa11c7e811ef2011eca61\
        c6b106eef00ee6200fe5500e33123618877080077aa8077928877998c1b44138b0033bbcc338fc023dbcc33a\
        94833bcc68dc201dda011ed8211dc6211de8c10de4a11ccc01000000a9180000370000000b0a722887778007\
        7a587098433db8c338b04339d0c382e61cc6a10de8411ec2c11de6211de8211ddec11d1634e3600ee7500fe1\
        200fe4400fe1200fe7500ef4b08081077928877060077678877108077a28077258709cc338b4013ba4833d94\
        c3026b1cd8211cdce11cdc201ce4611cdc201ce8811ec2611cd0a11cc8611cc2811dd861c1010ff4200fe150\
        0ff4800e0b8875180773488705cf38bc833bd84339c8c33994833b8c43398c033dc8033b2c28c2811dd2e11c\
        dc61c1440ee5100ee3400fe9600fe1400fe9f00eeed006f3900fed200eefc00e00000000d110000006000000\
        07cc3ca4833b9c033b94033da0833c94433890c3010000006128000005000000230882b04000000001000000\
        947200002d0000007120000003000000320e10228400c90300000000000000005d0c00000500000012039409\
        67625f6d61726b657200000000000000";

    /// The same module as ThinLTO bitcode (`opt --thinlto-bc`).
    const GB_THIN_BITCODE: &str = "4243c0de351400000d000000620c301cc1c60aac600bad200772e00671e00672d006f2500ff3400f6d00076e\
        10076e00076d400ff2500ff3400f421420530000210c0000050200000b022100020000002200000007812391\
        41c80449061032399201840c250508191e048b62800c450242920b42641032143808184b0a32328848b06421\
        43868804471c32422471c80811242940868c104b0132648408921c20234388e50019194204192a282a90515c\
        2023b940860c19c307cb1519328c8c24071932622c39c8901123c812880e1d3a644447c81022434602191a00\
        892000000a00000022660410b24282c910524282c99071c250480a092643c605423226080a9a230083126420\
        6004000013b270080779180774b0033a68837a708775708777b80777680376480777a8077c68837370877ad8\
        8007e5d006eda007e5d006e980077a80077a300772d006e9100776a0077160077a300772d006e9600774a007\
        7640076d900e71200778a00771200778d006ee300772a0077640076d300b71200778d006a6e00e73200723c0\
        2271037a28077ca00725718373608777100776000373f8857310072571037ac8077828073030875f38077160\
        0330280373a8077718077a4887777007c51c7ee11cc4410f94241cc8411ee0010cf0410ef0800dc0e0174e81\
        155e41144281157ee1154cc11466a11468e1176821144481154ae11794841dc8411ec0001fe0800dc06017f0\
        410ef0800dc0600cf4e01cde811ee0211ccea11c7e811dde210eea400fc8c11e7e811dc2611ee8a11794841d\
        c8411ec0001fe0800dc06017f0010e7a4149e4a11ce84149dc601ed2411fca010ccce117ce411cd8000cdca0\
        0dcce117ce411c148d1086548c40628065f197654805240200000000000000000000004002486c1028aa2000\
        0090050205000000321e980819114c908c092647c604434a098c0000b1180000e10000003308801cc4e11c66\
        14013d88433884c38c4280077978077398710ce6000fed100ef4800e330c421ec2c11dcea11c6630053d8843\
        3884831bcc033dc8433d8c033dcc788c7470077b08077948877070077a700376788770208719cc110eec900e\
        e1300f6e300fe3f00ef0500e3310c41dde211cd8211dc2611e6630893bbc833bd04339b4033cbc833c84033b\
        ccf0147660077b680737688772680737808770908770600776280776f8057678877780875f08877118877298\
        877998812ceef00eeee00ef5c00eec300362c8a11ce4a11ccca11ce4a11cdc611cca211cc4811dca6106d690\
        4339c84339984339c84339b8c33894433888033b94c32fbc833cfc823bd4033bb0c30cc76987705887727083\
        74680778608774188774a08719ce530fee000ff2500ee4900ee3400fe1200eec500e3320281ddcc11ec2411e\
        d2211cdc811edce01ce4e11dea011e66185138b0433a9c833bcc50247660077b68073760877778077898514c\
        f4900ff0500e331e6a1eca611ce8211ddec11d7e011ee4a11ccc211df0610654858338ccc33bb0433dd04339\
        fcc23ce4433b88c33bb0c38cc50a877998877718877408077a28077298815ce3100eecc00ee5500ef33023c1\
        d2411ee4e117d8e11dde011e6648193bb0833db4831b84c3388c4339ccc33cb8c139c8c33bd4033ccc48b471\
        080776600771088771588719dbc60eec600fede006f0200fe5300fe5200ff6500e6e100ee3300ee5300ff3e0\
        06e9e00ee4500ef83023e2ec611cc2811dd8e117ec211de6211dc4211dd8211de8211f66209d3bbc433db803\
        39948339cc58bc7070077778077a08077a488777708719cbe70eef300fe1e00ee9400fe9a00fe530c3010373\
        a8077718875f988770708774a08774d087729881844139e0c338b0433d904339cc40c4a01dcaa11de0411ede\
        c11c662463300ee1c00eec300fe9400fe5304321837518077348875fa0877c80877298b194013c8cc33c94c3\
        38d0433abc833bccc38cc50c48211542611ee6211dcec11d528114664c67300eef200fefe006ef500ff4300f\
        e9400ee5e006e6200fe1d00ee530a3408376680779088719521ab8c33b84033ba44338cc831b84033990833c\
        cc033c84c33894c30c460dc6211cd8811dcaa11c7e811ef2011eca61c6b106eef00ee6200fe5500e33123618\
        877080077aa8077928877998c1b44138b0033bbcc338fc023dbcc33a94833bcc68dc201dda011ed8211dc621\
        1de8c10de4a11ccc01000000792000001a000000921e482043880c19096464c8c920818c0432464646138142\
        a090f1c4c8083942868c62405800000012000000456e61626c6553706c69744c544f556e6974000023084130\
        821008330c4230c8486082326263b36b73697b23ab632b7331630b3b9b1b251800000000a918000037000000\
        0b0a7228877780077a587098433db8c338b04339d0c382e61cc6a10de8411ec2c11de6211de8211ddec11d16\
        34e3600ee7500fe1200fe4400fe1200fe7500ef4b08081077928877060077678877108077a28077258709cc3\
        38b4013ba4833d94c3026b1cd8211cdce11cdc201ce4611cdc201ce8811ec2611cd0a11cc8611cc2811dd861\
        c1010ff4200fe1500ff4800e0b8875180773488705cf38bc833bd84339c8c33994833b8c43398c033dc8033b\
        2c28c2811dd2e11cdc61c1440ee5100ee3400fe9600fe1400fe9f00eeed006f3900fed200eefc00e00000000\
        d11000000600000007cc3ca4833b9c033b94033da0833c94433890c3010000006128000005000000230882b0\
        4000000001000000947200002d000000a120000015000000a304cc5001202404198142a01055801021424488\
        10216284449d20448610112244881821290708913142625e102243c408097940880c21292d08113242426a10\
        3242426e103142328218a10200080000000000007120000003000000320e10228400ec03000000008b8a99b5\
        cd9e15d23b17ff702063123563213c5fb79607d42fdd511500000000650c000037000000120394b001000000\
        0300000009000000400000004c0000000100000058000000000000005800000005000000d000000000000000\
        4900000019000000620000000a0000000900000000000000d000000000000000000000000500000000000000\
        00000000090000000000000009000000ffffffff002400006c000000040000000900000000000000ffffffff\
        0024000009000000000000000900000000000000ffffffff0020000070000000070000000900000000000000\
        ffffffff8824000077000000150000000900000000000000ffffffff88240000000000005d0c000026000000\
        1203942c0100000067625f6d61726b657232322e312e322d727573742d302e312e302d747275737420666139\
        3338393131343430303635656634646663336361343933303834643434373335326330643461617263683634\
        2d756e6b6e6f776e2d6c696e75782d676e756762736d616c6c2e6c6c665f676264765f6c6173745f474c4f42\
        414c5f4f46465345545f5441424c455f00000000";

    /// `touch` loads `count` GOT slots (`adrp :got:`, `ldr :got_lo12:`
    /// against `dv_0`..), and `dv_0`.. and `dv_last` (4242) are defined: the
    /// object LLD links before the code it compiles from [`GB_BITCODE`], so
    /// the slot of `dv_last` that code loads lies after the others.
    fn gb_slots_source(count: usize) -> String {
        let mut source =
            String::from("\t.text\n\t.globl touch\n\t.type touch, %function\ntouch:\n");
        for index in 0..count {
            source +=
                &format!("\tadrp x1, :got:dv_{index}\n\tldr x1, [x1, #:got_lo12:dv_{index}]\n");
        }
        source += "\tret\n\t.size touch, .-touch\n\t.data\n";
        for index in 0..count {
            source += &format!("\t.globl dv_{index}\ndv_{index}:\n\t.xword {index}\n");
        }
        source + "\t.globl dv_last\ndv_last:\n\t.xword 4242\n"
    }

    /// The native code of the fat LTO object whose `.llvm.lto` section
    /// holds [`GB_BITCODE`]: an `f_gb` that returns 4242 without the GOT.
    const GB_FAT_NATIVE: &str =
        "long f_gb(void) { return 4242; }\nint gb_marker(void) { return 7; }\n";

    /// The thirteenth closure audit's fail-open: the GOT-base window check
    /// read only the uses of the objects LLD compiles from LLVM bitcode
    /// that the driver could read. A ThinLTO link with
    /// `--thinlto-cache-dir` (LLD writes 0 bytes for an object it takes
    /// from the cache, which its own first link fills) and a link that
    /// names its own `--lto-obj-path` (LLD writes the objects there, not in
    /// the stage) left them unread, and shared objects and PIEs whose
    /// compiled `f_gb` loads `dv_last` through `R_AARCH64_LD64_GOTPAGE_LO15`
    /// 48 KiB above the GOT base were installed: LLD wrote the offset
    /// truncated and the user read another slot. A fat LTO object linked
    /// with `--fat-lto-objects` is the same class: LLD links what it
    /// compiles from the object's `.llvm.lto` bitcode, and the driver read
    /// the object's own code.
    ///
    /// Now the link the driver checks puts its own `--lto-obj-path` and an
    /// empty `--thinlto-cache-dir=` after every option of the user's, and
    /// counts a fat LTO object's bitcode as a bitcode input, so each of
    /// these links (a cold and a warm cache; the user's path for full and
    /// ThinLTO; fat LTO; shared object and PIE) is read and refused by name
    /// for the use in the object LLD compiled, its output's bytes left as
    /// they were. LLD outside the driver writes them wrong, and without
    /// `--fat-lto-objects` the fat object's own `f_gb` runs. A later
    /// `--no-fat-lto-objects` that LLD takes as the value of the option
    /// before it (`-library-path`, which the measured tables read
    /// differently) leaves fat LTO on, and that PIE is refused too (LLD
    /// outside the driver writes it wrong); after `--as-needed`, which takes
    /// no value, it turns fat LTO off, and the PIE is installed and runs the
    /// object's own `f_gb`.
    ///
    /// When the objects cannot be read at all (here, an LLD whose
    /// `--version` is not the one the driver measured, whose objects the
    /// driver does not keep), every check that must read the loaded inputs'
    /// uses refuses the image by name (`[TCG-LINK-LTO-OBJECTS-UNREAD]`): the
    /// local-exec check of every shared object, and the GOT checks of an
    /// image not shown in reach. A PIE whose GOT is shown in reach needs no
    /// such read, and is installed and runs.
    ///
    /// The third verification of the repair found two more routes, each
    /// installed at `05097cc57` with wrong slots: a fat object whose ELF
    /// class, byte order or machine is not AArch64 LP64 (LLD takes the
    /// bitcode of any ELF relocatable object's `.llvm.lto` section), and a
    /// C driver that adds `--fat-lto-objects` itself. Now the fat object
    /// with `e_machine` patched to x86-64 counts as bitcode, as a file and as
    /// an archive member, and is refused for the use in the object LLD
    /// compiled (LLD outside the driver writes it wrong). Through the C
    /// driver that adds the option, LLD's map shows it linked code from a
    /// file the trace does not name, so the link runs again and the
    /// compiled object is read: the fat object's library and PIE are refused
    /// for its use, and an ordinary fat object is installed (PIE and static)
    /// and runs its bitcode's code. Where the driver cannot read what LLD
    /// compiled (the unmeasured LLD, or a C driver that also sends the
    /// objects elsewhere with a later `--lto-obj-path`), the checked link's
    /// map refuses the PIE by name.
    #[test]
    fn got_base_code_lld_compiles_from_bitcode_is_read_on_every_lto_route() {
        let Some(lld) = lld_dir() else {
            return;
        };
        let directory = tempfile::tempdir().unwrap();
        let dir = directory.path();
        let lld_bin = lld_cc(dir, &lld);
        let bin = Some(lld_bin.as_path());
        for (name, bytes) in [
            ("gb.bc", unhex(GB_BITCODE)),
            ("gb_thin.bc", unhex(GB_THIN_BITCODE)),
            ("lto.bc", unhex(LTO_BITCODE)),
            ("val2.trust_ir", VAL2_IR.as_bytes().to_vec()),
            ("lto.trust_ir", LTO_IR.as_bytes().to_vec()),
            ("gb_slots.s", gb_slots_source(6000).into_bytes()),
            ("gb_user.c", GB_USER.as_bytes().to_vec()),
            ("gb_fat.c", GB_FAT_NATIVE.as_bytes().to_vec()),
            ("ltomain.c", LTO_MAIN.as_bytes().to_vec()),
        ] {
            fs::write(dir.join(name), bytes).unwrap();
        }
        run_tool(dir, "as", &["-o", "gb_slots.o", "gb_slots.s"]);
        run_tool(dir, "cc", &["-c", "-O1", "-o", "gb_user.o", "gb_user.c"]);
        run_tool(dir, "cc", &["-c", "-O1", "-o", "ltomain.o", "ltomain.c"]);
        run_tool(
            dir,
            "cc",
            &["-c", "-O1", "-fPIC", "-o", "gb_fat_native.o", "gb_fat.c"],
        );
        run_tool(
            dir,
            "objcopy",
            &[
                "--add-section",
                ".llvm.lto=gb.bc",
                "--set-section-flags",
                ".llvm.lto=exclude",
                "gb_fat_native.o",
                "gb_fat.o",
            ],
        );
        for name in ["cache", "objs"] {
            fs::create_dir(dir.join(name)).unwrap();
        }
        let shared = |output: &'static str, group: &'static str| {
            vec![
                "--format=text",
                "-shared",
                "-nostdlib",
                "--relocation-model",
                "pic",
                "-o",
                output,
                "val2.trust_ir",
                group,
            ]
        };
        let pie = |output: &'static str, group: &'static str| {
            vec!["--format=text", "-o", output, "val2.trust_ir", group]
        };
        let window = "[TCG-LINK-GOT-PAGE-WINDOW]";
        let unproven = "[TCG-LINK-GOT-PAGE-UNPROVEN]";
        let compiled = |object: &str, input: &str| {
            format!(
                "{object} (an object LLD compiled from the LLVM bitcode input {input} at link \
                 time): R_AARCH64_LD64_GOTPAGE_LO15 against `dv_last`"
            )
        };
        let thin = compiled("lto.o1", "gb_thin.bc");
        let full = compiled("lto.o", "gb.bc");
        let fat = compiled("lto.o", "gb_fat.o's `.llvm.lto` section");
        for (args, tag, text) in [
            (
                shared(
                    "libgb_cache.so",
                    "-Wl,gb_slots.o,gb_thin.bc,--thinlto-cache-dir=cache",
                ),
                window,
                &thin,
            ),
            // The cache is warm now.
            (
                shared(
                    "libgb_cache.so",
                    "-Wl,gb_slots.o,gb_thin.bc,--thinlto-cache-dir=cache",
                ),
                window,
                &thin,
            ),
            (
                pie(
                    "gb_cache_pie",
                    "-Wl,gb_slots.o,gb_thin.bc,gb_user.o,--thinlto-cache-dir=cache",
                ),
                unproven,
                &thin,
            ),
            (
                shared(
                    "libgb_own.so",
                    "-Wl,gb_slots.o,gb.bc,--lto-obj-path=objs/mine.o",
                ),
                window,
                &full,
            ),
            (
                pie(
                    "gb_own_pie",
                    "-Wl,gb_slots.o,gb_thin.bc,gb_user.o,--plugin-opt=obj-path=objs/thin.o",
                ),
                unproven,
                &thin,
            ),
            (
                shared("libgb_fat.so", "-Wl,gb_slots.o,gb_fat.o,--fat-lto-objects"),
                window,
                &fat,
            ),
            (
                pie(
                    "gb_fat_pie",
                    "-Wl,gb_slots.o,gb_fat.o,gb_user.o,--fat-lto-objects",
                ),
                unproven,
                &fat,
            ),
            // `-library-path` takes `--no-fat-lto-objects` as its value in
            // LLD (the measured tables read the option differently), so fat
            // LTO stays on.
            (
                pie(
                    "gb_fat_libpath",
                    "-Wl,gb_slots.o,gb_fat.o,gb_user.o,--fat-lto-objects,-library-path,\
                     --no-fat-lto-objects",
                ),
                unproven,
                &fat,
            ),
        ] {
            refused_leaving_output(dir, bin, &args, tag, &[text.as_str()]);
        }
        assert!(fs::read_dir(dir.join("cache")).unwrap().next().is_some());
        assert!(dir.join("objs/mine.o").is_file() && dir.join("objs/thin.o1").is_file());
        // LLD outside the driver: the user of the cached library and the
        // fat PIE read another slot.
        let lld_cc = lld_bin.join("cc").display().to_string();
        run_tool(
            dir,
            &lld_cc,
            &[
                "-shared",
                "-o",
                "libgb_raw.so",
                "gb_slots.o",
                "gb_thin.bc",
                "-Wl,--thinlto-cache-dir=cache",
            ],
        );
        let raw = dir.join("libgb_raw.so").display().to_string();
        let rpath = format!("-Wl,-rpath,{}", dir.display());
        run_tool(dir, "cc", &["-o", "user_raw", "gb_user.o", &raw, &rpath]);
        run_tool(
            dir,
            &lld_cc,
            &[
                "-o",
                "gb_fat_raw",
                "gb_slots.o",
                "gb_fat.o",
                "gb_user.o",
                "-Wl,--fat-lto-objects",
            ],
        );
        run_tool(
            dir,
            &lld_cc,
            &[
                "-o",
                "gb_fat_libpath_raw",
                "gb_slots.o",
                "gb_fat.o",
                "gb_user.o",
                "-Wl,--fat-lto-objects,-library-path,--no-fat-lto-objects",
            ],
        );
        for program in ["user_raw", "gb_fat_raw", "gb_fat_libpath_raw"] {
            let (code, stdout) = run_program(&dir.join(program));
            assert!(
                code == Some(1) && stdout.starts_with("f_gb=") && stdout != "f_gb=4242\n",
                "{program}: {code:?} {stdout}"
            );
        }
        // Without `--fat-lto-objects` LLD links the fat object's own code,
        // and so it does when `--no-fat-lto-objects` follows `--as-needed`,
        // which takes no value.
        for args in [
            pie("gb_fat_off", "-Wl,gb_slots.o,gb_fat.o,gb_user.o"),
            pie(
                "gb_fat_as_needed",
                "-Wl,gb_slots.o,gb_fat.o,gb_user.o,--fat-lto-objects,--as-needed,\
                 --no-fat-lto-objects",
            ),
        ] {
            assert_eq!(
                installed_and_run(dir, bin, &args),
                (Some(0), "f_gb=4242\n".to_string()),
                "{args:?}"
            );
        }

        // An LLD that names itself otherwise than the one the driver
        // measured: the driver keeps none of the objects it compiles.
        let other_tools = dir.join("other-lld-tools");
        let other_bin = dir.join("other-lld-cc");
        fs::create_dir(&other_tools).unwrap();
        fs::create_dir(&other_bin).unwrap();
        write_executable_script(
            &other_tools.join("ld.lld"),
            &format!(
                "#!/bin/sh\nfor arg in \"$@\"; do case \"$arg\" in --version) echo 'LLD 22.1.6 \
                 (another build)'; exit 0;; esac; done\nexec '{}' \"$@\"\n",
                lld.join("ld.lld").display()
            ),
        );
        let host_cc = std::env::split_paths(&std::env::var_os("PATH").unwrap_or_default())
            .map(|dir| dir.join("cc"))
            .find(|cc| cc.is_file())
            .expect("a host cc on PATH");
        write_executable_script(
            &other_bin.join("cc"),
            &format!(
                "#!/bin/sh\nexec '{}' -fuse-ld=lld -B'{}/' \"$@\"\n",
                host_cc.display(),
                other_tools.display()
            ),
        );
        let other = Some(other_bin.as_path());
        let unread = "[TCG-LINK-LTO-OBJECTS-UNREAD]";
        let kept = "those objects are not read (the driver keeps only the objects LLD 22.1.6 \
                    compiles, and the linker is `LLD 22.1.6 (another build)`)";
        for (args, reads) in [
            (
                shared("libgb_other.so", "-Wl,gb_slots.o,gb_thin.bc"),
                "the image is not shown to keep every GOT slot",
            ),
            (
                pie("gb_other_pie", "-Wl,gb_slots.o,gb_thin.bc,gb_user.o"),
                "the image is not shown to keep every GOT slot",
            ),
            (
                vec![
                    "--format=text",
                    "-shared",
                    "--relocation-model",
                    "pic",
                    "-o",
                    "liblto_other.so",
                    "lto.trust_ir",
                    "-Wl,lto.bc",
                ],
                "a non-executable image is linked from must be read for local-exec TLS",
            ),
        ] {
            refused_leaving_output(dir, other, &args, unread, &[kept, reads]);
        }
        let args = [
            "--format=text",
            "-o",
            "lto_other_pie",
            "lto.trust_ir",
            "-Wl,ltomain.o,lto.bc",
        ];
        assert_eq!(
            installed_and_run(dir, other, &args),
            (Some(0), "e=10 f=1000\n".to_string())
        );

        // The third verification: what LLD linked decides, not the `-Wl`
        // groups alone. The fat object with `e_machine` patched to x86-64:
        // LLD links such an object only through its `.llvm.lto` bitcode, so
        // it counts as bitcode as a file and as an archive member.
        let mut foreign = fs::read(dir.join("gb_fat.o")).unwrap();
        foreign[18..20].copy_from_slice(&62u16.to_le_bytes());
        fs::write(dir.join("gb_fat_x86.o"), &foreign).unwrap();
        run_tool(dir, "ar", &["rcs", "libgbfx.a", "gb_fat_x86.o"]);
        let other_container = "(an ELF relocatable object of another class, byte order or \
                               machine, which LLD links only through that bitcode)";
        let foreign_file = compiled(
            "lto.o",
            &format!("gb_fat_x86.o's `.llvm.lto` section {other_container}"),
        );
        let foreign_member = compiled(
            "lto.o",
            &format!("libgbfx.a(gb_fat_x86.o)'s `.llvm.lto` section {other_container}"),
        );
        for (args, tag, text) in [
            (
                shared(
                    "libgb_fat_x86.so",
                    "-Wl,gb_slots.o,gb_fat_x86.o,--fat-lto-objects",
                ),
                window,
                &foreign_file,
            ),
            (
                pie(
                    "gb_fat_x86_pie",
                    "-Wl,gb_slots.o,gb_user.o,libgbfx.a,--fat-lto-objects",
                ),
                unproven,
                &foreign_member,
            ),
        ] {
            refused_leaving_output(dir, bin, &args, tag, &[text.as_str()]);
        }
        run_tool(
            dir,
            &lld_cc,
            &[
                "-o",
                "gb_fat_x86_raw",
                "gb_slots.o",
                "gb_fat_x86.o",
                "gb_user.o",
                "-Wl,--fat-lto-objects",
            ],
        );
        let (code, stdout) = run_program(&dir.join("gb_fat_x86_raw"));
        assert!(
            code == Some(1) && stdout.starts_with("f_gb=") && stdout != "f_gb=4242\n",
            "gb_fat_x86_raw: {code:?} {stdout}"
        );
        // A C driver that adds `--fat-lto-objects` itself, which no `-Wl`
        // group shows: LLD's map shows it linked code from a file the trace
        // does not name, so the link runs again and what LLD compiled is
        // read, as when the group names the option.
        let wrapper = |name: &str, tools: &Path, extra: &str| -> PathBuf {
            let bin = dir.join(name);
            fs::create_dir(&bin).unwrap();
            write_executable_script(
                &bin.join("cc"),
                &format!(
                    "#!/bin/sh\nexec '{}' -fuse-ld=lld -B'{}/' \"$@\" {extra}\n",
                    host_cc.display(),
                    tools.display()
                ),
            );
            bin
        };
        let hidden_bin = wrapper(
            "fatflag-cc",
            &dir.join("lld-tools"),
            "-Wl,--fat-lto-objects",
        );
        let hidden = Some(hidden_bin.as_path());
        for (args, tag) in [
            (shared("libgb_hidden.so", "-Wl,gb_slots.o,gb_fat.o"), window),
            (
                pie("gb_hidden_pie", "-Wl,gb_slots.o,gb_fat.o,gb_user.o"),
                unproven,
            ),
        ] {
            refused_leaving_output(dir, hidden, &args, tag, &[fat.as_str()]);
        }
        // Through that driver an ordinary fat object (its own `c_cb`
        // triples, its bitcode's doubles) is installed and runs the
        // bitcode's code, as a PIE and as a static program.
        fs::write(
            dir.join("cb_fat.c"),
            "long c_word = 1000;\nunsigned long c_cb(unsigned long x) { return 3 * x; }\n",
        )
        .unwrap();
        run_tool(
            dir,
            "cc",
            &["-c", "-O1", "-fPIC", "-o", "cb_fat_native.o", "cb_fat.c"],
        );
        run_tool(
            dir,
            "objcopy",
            &[
                "--add-section",
                ".llvm.lto=lto.bc",
                "--set-section-flags",
                ".llvm.lto=exclude",
                "cb_fat_native.o",
                "cb_fat.o",
            ],
        );
        for extra in [&[][..], &["--static"][..]] {
            let mut args = vec!["--format=text"];
            args.extend(extra);
            args.extend([
                "-o",
                "lto_hidden_fat",
                "lto.trust_ir",
                "-Wl,ltomain.o,cb_fat.o",
            ]);
            assert_eq!(
                installed_and_run(dir, hidden, &args),
                (Some(0), "e=10 f=1000\n".to_string()),
                "{args:?}"
            );
        }
        // Where the driver cannot read what LLD compiled, the checked link's
        // map refuses the image by name: an LLD whose identity the driver
        // did not measure, and a C driver that also sends LLD's objects
        // elsewhere with a later `--lto-obj-path`.
        fs::create_dir(dir.join("elsewhere")).unwrap();
        let other_hidden_bin = wrapper("other-fatflag-cc", &other_tools, "-Wl,--fat-lto-objects");
        let elsewhere_bin = wrapper(
            "elsewhere-cc",
            &dir.join("lld-tools"),
            &format!(
                "-Wl,--fat-lto-objects,--lto-obj-path={}/lto.o",
                dir.join("elsewhere").display()
            ),
        );
        for (bin, output) in [
            (&other_hidden_bin, "gb_hidden_other_pie"),
            (&elsewhere_bin, "gb_elsewhere_pie"),
        ] {
            let map = format!(
                "{output}.lto.o (with 0 more such file(s)), which its input trace does not name"
            );
            refused_leaving_output(
                dir,
                Some(bin.as_path()),
                &pie(output, "-Wl,gb_slots.o,gb_fat.o,gb_user.o"),
                unread,
                &[
                    "is refused because the code its linker compiled from LLVM bitcode is not \
                     read: LLD's link map places input sections of ",
                    map.as_str(),
                    "and the driver read 0 object(s) LLD compiled for the link",
                ],
            );
        }
        assert!(dir.join("elsewhere/lto.o").is_file());
    }

    /// The fourteenth closure audit's finding: LLD 22.1.6 names the object
    /// it compiles from a fat object's ThinLTO bitcode `<input
    /// dir>/<output>.lto.<stem>.o` (`<output>.lto.<archive>(<member> at
    /// <offset>).o` for an archive member), a name the user can predict and
    /// that does not depend on the driver's stage. With an input of that
    /// name in the link, LLD's map placed the compiled object under a name
    /// the trace names, so the map rule saw no compiled code, no second link
    /// ran, and through a C driver that adds `--fat-lto-objects` itself the
    /// driver installed a PIE and a shared object whose GOT-base load read
    /// another slot (`f_gb=1904`) and a static program whose outline-atomics
    /// helpers hung it. An LLD whose identity the driver did not measure
    /// installed the PIE the same way.
    ///
    /// Now every link that loads an object embedding bitcode runs again to
    /// keep what LLD compiled, whatever the inputs are named, and what LLD
    /// wrote is read in full or the image is refused by name. Each decoy
    /// link is refused with its control's tag (the use in the object LLD
    /// compiled, for the file and for the archive member; the helpers LLD
    /// compiled for the static program), and the unmeasured LLD
    /// is refused as `[TCG-LINK-LTO-OBJECTS-UNREAD]`, with and without the
    /// option (conservative without it: that LLD then links the object's own
    /// code). The decoy PIE outside the driver reads another slot. Ordinary
    /// links with the decoys are installed and run: an ordinary fat object
    /// through the C driver (static and PIE, the bitcode's code), the GOT
    /// fat object through LLD without the option (an empty `lto.o` alone
    /// shows LLD compiled nothing, the object's own code), and through GNU
    /// ld and gold (a PIE through GNU ld, a shared object through each; the
    /// object's own code; both reject the option).
    #[test]
    fn compiled_code_lld_wrote_is_read_whatever_the_inputs_are_named() {
        let Some(lld) = lld_dir() else {
            return;
        };
        let directory = tempfile::tempdir().unwrap();
        let dir = directory.path();
        let lld_bin = lld_cc(dir, &lld);
        for (name, bytes) in [
            ("gb_thin.bc", unhex(GB_THIN_BITCODE)),
            ("evil_thin.bc", unhex(EVIL_THIN_BITCODE)),
            ("thin.bc", unhex(THIN_BITCODE)),
            ("val2.trust_ir", VAL2_IR.as_bytes().to_vec()),
            ("lto.trust_ir", LTO_IR.as_bytes().to_vec()),
            ("gb_slots.s", gb_slots_source(6000).into_bytes()),
            ("gb_user.c", GB_USER.as_bytes().to_vec()),
            ("gb_fat.c", GB_FAT_NATIVE.as_bytes().to_vec()),
            ("ltomain.c", LTO_MAIN.as_bytes().to_vec()),
            (
                "cb_fat.c",
                b"long c_word = 1000;\nunsigned long c_cb(unsigned long x) { return 3 * x; }\n"
                    .to_vec(),
            ),
            ("decoy.c", b"int decoy_value(void) { return 5; }\n".to_vec()),
        ] {
            fs::write(dir.join(name), bytes).unwrap();
        }
        run_tool(dir, "as", &["-o", "gb_slots.o", "gb_slots.s"]);
        run_tool(dir, "cc", &["-c", "-O1", "-o", "gb_user.o", "gb_user.c"]);
        run_tool(dir, "cc", &["-c", "-O1", "-o", "ltomain.o", "ltomain.c"]);
        run_tool(dir, "cc", &["-c", "-O1", "-o", "decoy.o", "decoy.c"]);
        // Fat objects: the GOT-base `f_gb`, the outline-atomics helpers and
        // an ordinary `c_cb` (its own code triples, its bitcode's doubles),
        // each with ThinLTO bitcode in `.llvm.lto`.
        for (native, source, bitcode, fat) in [
            ("gb_fat_native.o", "gb_fat.c", "gb_thin.bc", "gb_fat.o"),
            ("cb_fat_native.o", "cb_fat.c", "evil_thin.bc", "evil_fat.o"),
            ("cb_fat_native.o", "cb_fat.c", "thin.bc", "good_fat.o"),
        ] {
            run_tool(dir, "cc", &["-c", "-O1", "-fPIC", "-o", native, source]);
            let section = format!(".llvm.lto={bitcode}");
            run_tool(
                dir,
                "objcopy",
                &[
                    "--add-section",
                    &section,
                    "--set-section-flags",
                    ".llvm.lto=exclude",
                    native,
                    fat,
                ],
            );
        }
        run_tool(dir, "ar", &["rcs", "libgbf.a", "gb_fat.o"]);
        // Each decoy: the plain object under LLD's name for the object it
        // compiles for that output.
        let decoys = [
            "gb_decoy_pie.lto.gb_fat.o",
            "libgb_decoy.so.lto.gb_fat.o",
            "evil_decoy_st.lto.evil_fat.o",
            "gb_decoy_raw.lto.gb_fat.o",
            "gb_other_pie.lto.gb_fat.o",
            "gb_other_off_pie.lto.gb_fat.o",
            "good_decoy_st.lto.good_fat.o",
            "good_decoy_pie.lto.good_fat.o",
            "gb_off_decoy_pie.lto.gb_fat.o",
            "gb_gnu_decoy_pie.lto.gb_fat.o",
        ];
        for decoy in decoys {
            fs::copy(dir.join("decoy.o"), dir.join(decoy)).unwrap();
        }
        let host_cc = std::env::split_paths(&std::env::var_os("PATH").unwrap_or_default())
            .map(|dir| dir.join("cc"))
            .find(|cc| cc.is_file())
            .expect("a host cc on PATH");
        // C drivers that add `--fat-lto-objects` themselves, through the
        // measured LLD and through one that names itself otherwise.
        let other_tools = dir.join("other-lld-tools");
        fs::create_dir(&other_tools).unwrap();
        write_executable_script(
            &other_tools.join("ld.lld"),
            &format!(
                "#!/bin/sh\nfor arg in \"$@\"; do case \"$arg\" in --version) echo 'LLD 22.1.6 \
                 (another build)'; exit 0;; esac; done\nexec '{}' \"$@\"\n",
                lld.join("ld.lld").display()
            ),
        );
        let wrapper = |name: &str, tools: &Path, extra: &str| -> PathBuf {
            let bin = dir.join(name);
            fs::create_dir(&bin).unwrap();
            write_executable_script(
                &bin.join("cc"),
                &format!(
                    "#!/bin/sh\nexec '{}' -fuse-ld=lld -B'{}/' \"$@\" {extra}\n",
                    host_cc.display(),
                    tools.display()
                ),
            );
            bin
        };
        let fat_bin = wrapper(
            "fatflag-cc",
            &dir.join("lld-tools"),
            "-Wl,--fat-lto-objects",
        );
        let other_fat_bin = wrapper("other-fatflag-cc", &other_tools, "-Wl,--fat-lto-objects");
        let other_bin = wrapper("other-cc", &other_tools, "");
        let fat = Some(fat_bin.as_path());
        let pie = |output: &'static str, group: &'static str| {
            vec!["--format=text", "-o", output, "val2.trust_ir", group]
        };
        let compiled = |input: &str| {
            format!(
                "lto.o1 (an object LLD compiled from the LLVM bitcode input {input}'s \
                 `.llvm.lto` section at link time)"
            )
        };
        let use_in = |input: &str| {
            format!(
                "{}: R_AARCH64_LD64_GOTPAGE_LO15 against `dv_last`",
                compiled(input)
            )
        };
        // Each decoy link is refused with its control's tag, for the same
        // use (`gb_decoy_ctl` is the PIE's control, without a decoy).
        for (args, tag, text) in [
            (
                pie("gb_decoy_ctl", "-Wl,gb_slots.o,gb_fat.o,gb_user.o"),
                "[TCG-LINK-GOT-PAGE-UNPROVEN]",
                use_in("gb_fat.o"),
            ),
            (
                pie(
                    "gb_decoy_pie",
                    "-Wl,gb_slots.o,gb_fat.o,gb_user.o,gb_decoy_pie.lto.gb_fat.o",
                ),
                "[TCG-LINK-GOT-PAGE-UNPROVEN]",
                use_in("gb_fat.o"),
            ),
            (
                vec![
                    "--format=text",
                    "-shared",
                    "-nostdlib",
                    "--relocation-model",
                    "pic",
                    "-o",
                    "libgb_decoy.so",
                    "val2.trust_ir",
                    "-Wl,gb_slots.o,gb_fat.o,libgb_decoy.so.lto.gb_fat.o",
                ],
                "[TCG-LINK-GOT-PAGE-WINDOW]",
                use_in("gb_fat.o"),
            ),
            (
                vec![
                    "--format=text",
                    "--static",
                    "-o",
                    "evil_decoy_st",
                    "lto.trust_ir",
                    "-Wl,ltomain.o,evil_fat.o,evil_decoy_st.lto.evil_fat.o",
                ],
                "[TCG-LINK-IRELATIVE-UNAPPLIED]",
                format!("the input {} defines __aarch64_", compiled("evil_fat.o")),
            ),
        ] {
            refused_leaving_output(dir, fat, &args, tag, &[text.as_str()]);
        }
        // The unmeasured LLD keeps no object the driver reads, with the
        // option and without it.
        let unread = "[TCG-LINK-LTO-OBJECTS-UNREAD]";
        let not_read = "the loaded input gb_fat.o's `.llvm.lto` section is LLVM bitcode (with 0 \
                        more such input(s)) that LLD 22.1.6 links in place of its object's own \
                        code given --fat-lto-objects (which a C driver can add), and what LLD \
                        wrote where the driver had it keep the objects it compiles is not read \
                        (the driver keeps only the objects LLD 22.1.6 compiles, and the linker \
                        is `LLD 22.1.6 (another build)`)";
        for (bin, output, group) in [
            (
                &other_fat_bin,
                "gb_other_pie",
                "-Wl,gb_slots.o,gb_fat.o,gb_user.o,gb_other_pie.lto.gb_fat.o",
            ),
            (
                &other_bin,
                "gb_other_off_pie",
                "-Wl,gb_slots.o,gb_fat.o,gb_user.o,gb_other_off_pie.lto.gb_fat.o",
            ),
        ] {
            refused_leaving_output(
                dir,
                Some(bin.as_path()),
                &pie(output, group),
                unread,
                &[not_read],
            );
        }
        // LLD outside the driver: its map places the decoy and the object
        // it compiled under one name, and the decoy PIE reads another slot.
        // So it does with an archive member's decoy, named after the
        // member's header offset; through the driver that PIE is refused
        // for the use in the member's compiled object.
        let fat_cc = fat_bin.join("cc").display().to_string();
        let at = fs::read(dir.join("libgbf.a"))
            .unwrap()
            .windows(9)
            .position(|bytes| bytes == b"gb_fat.o/")
            .expect("the member's header");
        let member_raw = format!("gb_member_raw.lto.libgbf.a(gb_fat.o at {at}).o");
        let member_pie = format!("gb_member_pie.lto.libgbf.a(gb_fat.o at {at}).o");
        for decoy in [&member_raw, &member_pie] {
            fs::copy(dir.join("decoy.o"), dir.join(decoy)).unwrap();
        }
        for (output, inputs, decoy) in [
            (
                "gb_decoy_raw",
                &["gb_fat.o", "gb_user.o", "gb_decoy_raw.lto.gb_fat.o"][..],
                "gb_decoy_raw.lto.gb_fat.o",
            ),
            (
                "gb_member_raw",
                &["gb_user.o", "libgbf.a", member_raw.as_str()][..],
                member_raw.as_str(),
            ),
        ] {
            let map = format!("-Wl,-Map={output}.map");
            let mut args = vec!["-o", output, "gb_slots.o"];
            args.extend(inputs);
            args.push(&map);
            run_tool(dir, &fat_cc, &args);
            let placed = fs::read_to_string(dir.join(format!("{output}.map")))
                .unwrap()
                .lines()
                .filter(|line| line.trim_end().ends_with(&format!("{decoy}:(.text)")))
                .count();
            assert_eq!(placed, 2, "{output}");
            let (code, stdout) = run_program(&dir.join(output));
            assert!(
                code == Some(1) && stdout.starts_with("f_gb=") && stdout != "f_gb=4242\n",
                "{output}: {code:?} {stdout}"
            );
        }
        let group = format!("-Wl,gb_slots.o,gb_user.o,libgbf.a,{member_pie}");
        refused_leaving_output(
            dir,
            fat,
            &[
                "--format=text",
                "-o",
                "gb_member_pie",
                "val2.trust_ir",
                &group,
            ],
            "[TCG-LINK-GOT-PAGE-UNPROVEN]",
            &[use_in("libgbf.a(gb_fat.o)").as_str()],
        );
        // Ordinary links with a decoy are installed and run: the ordinary
        // fat object through the C driver runs its bitcode's `c_cb`; the GOT
        // fat object through LLD without the option and through GNU ld runs
        // its own `f_gb`.
        for extra in [&["--static"][..], &[][..]] {
            let output = if extra.is_empty() {
                "good_decoy_pie"
            } else {
                "good_decoy_st"
            };
            let group = format!("-Wl,ltomain.o,good_fat.o,{output}.lto.good_fat.o");
            let mut args = vec!["--format=text"];
            args.extend(extra);
            args.extend(["-o", output, "lto.trust_ir", group.as_str()]);
            assert_eq!(
                installed_and_run(dir, fat, &args),
                (Some(0), "e=10 f=1000\n".to_string()),
                "{args:?}"
            );
        }
        for (bin, output, group) in [
            (
                Some(lld_bin.as_path()),
                "gb_off_decoy_pie",
                "-Wl,gb_slots.o,gb_fat.o,gb_user.o,gb_off_decoy_pie.lto.gb_fat.o",
            ),
            (
                None,
                "gb_gnu_decoy_pie",
                "-Wl,gb_slots.o,gb_fat.o,gb_user.o,gb_gnu_decoy_pie.lto.gb_fat.o",
            ),
        ] {
            assert_eq!(
                installed_and_run(dir, bin, &pie(output, group)),
                (Some(0), "f_gb=4242\n".to_string()),
                "{output}"
            );
        }
        // So are its shared objects through GNU ld and gold, whose maps show
        // a link LLD did not make; a shared object's local-exec check reads
        // every loaded input, so each would be refused were its compiled
        // code taken as unread. Their user runs the object's own `f_gb`.
        let gold_bin = gold_cc(dir);
        let rpath = format!("-Wl,-rpath,{}", dir.display());
        for (bin, output) in [
            (None, "libgb_gnu_decoy.so"),
            (gold_bin.as_deref(), "libgb_gold_decoy.so"),
        ] {
            if output.contains("gold") && bin.is_none() {
                continue;
            }
            let decoy = format!("{output}.lto.gb_fat.o");
            fs::copy(dir.join("decoy.o"), dir.join(&decoy)).unwrap();
            let group = format!("-Wl,gb_slots.o,gb_fat.o,{decoy}");
            let args = [
                "--format=text",
                "-shared",
                "-nostdlib",
                "--relocation-model",
                "pic",
                "-o",
                output,
                "val2.trust_ir",
                group.as_str(),
            ];
            let result = trust_cg_on(bin, dir, &args);
            assert!(result.status.success(), "{output}: {}", stderr(&result));
            let library = dir.join(output).display().to_string();
            let user = format!("user_{output}");
            run_tool(dir, "cc", &["-o", &user, "gb_user.o", &library, &rpath]);
            assert_eq!(
                run_program(&dir.join(&user)),
                (Some(0), "f_gb=4242\n".to_string()),
                "{output}"
            );
        }
    }

    /// The fifteenth closure audit's finding: under `--lto-partitions=<N>`
    /// LLD 22.1.6 writes one file per task where the driver has it keep its
    /// objects even when it compiles nothing, `lto.o` to `lto.o<N-1>`, each
    /// empty. The fourteenth audit's repair read only an empty `lto.o` alone
    /// as "LLD compiled nothing", so a link that loaded a fat object without
    /// `--fat-lto-objects` and passed `--lto-partitions=2` (or more) was
    /// refused as `[TCG-LINK-LTO-OBJECTS-UNREAD]`, though LLD links the
    /// object's own code. Now only empty files, one per task, read as
    /// "nothing compiled", and these links are installed and run the
    /// object's own code: the GOT-base fat object as a PIE (`f_gb=4242`) and
    /// as a shared object, an ordinary fat object as a static program
    /// (`e=15`, its own `c_cb`), in each spelling LLD accepts, and with the
    /// option added by a C driver after the driver's own.
    ///
    /// What is compiled is still read or refused: through a C driver that
    /// adds `--fat-lto-objects` and `--lto-partitions=3`, LLD writes three
    /// partition objects and the module's `lto.o3`, all read, so the
    /// GOT-base PIE is refused for the use in `lto.o3` and the ordinary fat
    /// object is installed running its bitcode's code (`e=10`); with a later
    /// `--thinlto-cache-dir` as well, LLD writes 0 bytes for the module
    /// beside the partitions, and the PIE is refused as unread; with
    /// `-plugin-opt=emit-llvm` every file is empty but LLD writes LLVM
    /// bitcode where the image belongs, which is not installed. A link that
    /// loads a counted ThinLTO input and the uncounted fat object (the C
    /// driver adds the option) names the compiled object after both.
    #[test]
    fn lld_links_that_compile_nothing_are_installed_under_lto_partitions() {
        let Some(lld) = lld_dir() else {
            return;
        };
        let directory = tempfile::tempdir().unwrap();
        let dir = directory.path();
        let lld_bin = lld_cc(dir, &lld);
        for (name, bytes) in [
            ("gb_thin.bc", unhex(GB_THIN_BITCODE)),
            ("thin.bc", unhex(THIN_BITCODE)),
            ("val2.trust_ir", VAL2_IR.as_bytes().to_vec()),
            ("lto.trust_ir", LTO_IR.as_bytes().to_vec()),
            ("gb_slots.s", gb_slots_source(6000).into_bytes()),
            ("gb_user.c", GB_USER.as_bytes().to_vec()),
            ("gb_fat.c", GB_FAT_NATIVE.as_bytes().to_vec()),
            ("ltomain.c", LTO_MAIN.as_bytes().to_vec()),
            (
                "cb_fat.c",
                b"long c_word = 1000;\nunsigned long c_cb(unsigned long x) { return 3 * x; }\n"
                    .to_vec(),
            ),
        ] {
            fs::write(dir.join(name), bytes).unwrap();
        }
        run_tool(dir, "as", &["-o", "gb_slots.o", "gb_slots.s"]);
        run_tool(dir, "cc", &["-c", "-O1", "-o", "gb_user.o", "gb_user.c"]);
        run_tool(dir, "cc", &["-c", "-O1", "-o", "ltomain.o", "ltomain.c"]);
        // Fat objects with ThinLTO bitcode in `.llvm.lto`: the GOT-base
        // `f_gb` (its own code returns 4242 without the GOT), and an
        // ordinary `c_cb` (its own code triples, its bitcode's doubles).
        for (native, source, bitcode, fat) in [
            ("gb_fat_native.o", "gb_fat.c", "gb_thin.bc", "gb_fat.o"),
            ("cb_fat_native.o", "cb_fat.c", "thin.bc", "good_fat.o"),
        ] {
            run_tool(dir, "cc", &["-c", "-O1", "-fPIC", "-o", native, source]);
            let section = format!(".llvm.lto={bitcode}");
            run_tool(
                dir,
                "objcopy",
                &[
                    "--add-section",
                    &section,
                    "--set-section-flags",
                    ".llvm.lto=exclude",
                    native,
                    fat,
                ],
            );
        }
        let host_cc = std::env::split_paths(&std::env::var_os("PATH").unwrap_or_default())
            .map(|dir| dir.join("cc"))
            .find(|cc| cc.is_file())
            .expect("a host cc on PATH");
        // C drivers that add LLD options after every argument, the driver's
        // own included.
        let wrapper = |name: &str, extra: &str| -> PathBuf {
            let bin = dir.join(name);
            fs::create_dir(&bin).unwrap();
            write_executable_script(
                &bin.join("cc"),
                &format!(
                    "#!/bin/sh\nexec '{}' -fuse-ld=lld -B'{}/' \"$@\" {extra}\n",
                    host_cc.display(),
                    dir.join("lld-tools").display()
                ),
            );
            bin
        };
        fs::create_dir(dir.join("cache")).unwrap();
        let partitions_bin = wrapper("partitions-cc", "-Wl,--lto-partitions=3");
        let fat_partitions_bin = wrapper(
            "fat-partitions-cc",
            "-Wl,--fat-lto-objects,--lto-partitions=3",
        );
        let cached_bin = wrapper(
            "fat-cached-cc",
            &format!(
                "-Wl,--fat-lto-objects,--lto-partitions=2,--thinlto-cache-dir={}",
                dir.join("cache").display()
            ),
        );
        let emit_llvm_bin = wrapper(
            "fat-emit-llvm-cc",
            "-Wl,--fat-lto-objects,-plugin-opt=emit-llvm,--lto-partitions=2",
        );
        let fat_bin = wrapper("fat-cc", "-Wl,--fat-lto-objects");
        let plain_lld = Some(lld_bin.as_path());
        let pie = |output: &'static str, group: &'static str| {
            vec!["--format=text", "-o", output, "val2.trust_ir", group]
        };
        // LLD compiles nothing: installed, running the objects' own code.
        for (bin, output, group) in [
            (
                plain_lld,
                "gb_p2_pie",
                "-Wl,gb_slots.o,gb_fat.o,gb_user.o,--lto-partitions=2",
            ),
            (
                plain_lld,
                "gb_p4_pie",
                "-Wl,gb_slots.o,gb_fat.o,gb_user.o,-plugin-opt=lto-partitions=4",
            ),
            (
                Some(partitions_bin.as_path()),
                "gb_cc_p3_pie",
                "-Wl,gb_slots.o,gb_fat.o,gb_user.o",
            ),
        ] {
            assert_eq!(
                installed_and_run(dir, bin, &pie(output, group)),
                (Some(0), "f_gb=4242\n".to_string()),
                "{output}"
            );
        }
        let rpath = format!("-Wl,-rpath,{}", dir.display());
        for group in [
            "-Wl,gb_slots.o,gb_fat.o,--plugin-opt=lto-partitions=3",
            "-Wl,gb_slots.o,gb_fat.o,-plugin-opt,lto-partitions=2",
        ] {
            let args = [
                "--format=text",
                "-shared",
                "-nostdlib",
                "--relocation-model",
                "pic",
                "-o",
                "libgb_parts.so",
                "val2.trust_ir",
                group,
            ];
            let result = trust_cg_on(plain_lld, dir, &args);
            assert!(result.status.success(), "{group}: {}", stderr(&result));
            let library = dir.join("libgb_parts.so").display().to_string();
            run_tool(
                dir,
                "cc",
                &["-o", "user_parts", "gb_user.o", &library, &rpath],
            );
            assert_eq!(
                run_program(&dir.join("user_parts")),
                (Some(0), "f_gb=4242\n".to_string()),
                "{group}"
            );
            fs::remove_file(dir.join("libgb_parts.so")).unwrap();
        }
        let args = [
            "--format=text",
            "--static",
            "-o",
            "good_p4_st",
            "lto.trust_ir",
            "-Wl,ltomain.o,good_fat.o,--lto-partitions=4",
        ];
        assert_eq!(
            installed_and_run(dir, plain_lld, &args),
            (Some(1), "e=15 f=1000\n".to_string())
        );
        // LLD compiles the fat objects' bitcode under three partitions:
        // `lto.o` to `lto.o2` and the module's `lto.o3`, each read.
        refused_leaving_output(
            dir,
            Some(fat_partitions_bin.as_path()),
            &pie("gb_fat_p3_pie", "-Wl,gb_slots.o,gb_fat.o,gb_user.o"),
            "[TCG-LINK-GOT-PAGE-UNPROVEN]",
            &[
                "lto.o3 (an object LLD compiled from the LLVM bitcode input gb_fat.o's \
               `.llvm.lto` section at link time): R_AARCH64_LD64_GOTPAGE_LO15 against \
               `dv_last`",
            ],
        );
        for extra in [&["--static"][..], &[][..]] {
            let mut args = vec!["--format=text"];
            args.extend(extra);
            args.extend([
                "-o",
                "good_fat_p3",
                "lto.trust_ir",
                "-Wl,ltomain.o,good_fat.o",
            ]);
            assert_eq!(
                installed_and_run(dir, Some(fat_partitions_bin.as_path()), &args),
                (Some(0), "e=10 f=1000\n".to_string()),
                "{args:?}"
            );
        }
        // A ThinLTO cache after the driver's empty one: LLD writes 0 bytes
        // for the module it takes from the cache, beside the partitions'
        // objects, cold and warm. The counted ThinLTO input's objects are
        // not read; for the fat object, the map's compiled files outnumber
        // the objects read (none).
        for _ in 0..2 {
            refused_leaving_output(
                dir,
                Some(cached_bin.as_path()),
                &pie("gb_cached_bc_pie", "-Wl,gb_slots.o,gb_thin.bc,gb_user.o"),
                "[TCG-LINK-LTO-OBJECTS-UNREAD]",
                &[
                    "beside a non-empty object it compiled, as LLD 22.1.6 does for a task whose \
                   object it takes from elsewhere (its ThinLTO cache)",
                ],
            );
            refused_leaving_output(
                dir,
                Some(cached_bin.as_path()),
                &pie("gb_cached_pie", "-Wl,gb_slots.o,gb_fat.o,gb_user.o"),
                "[TCG-LINK-LTO-OBJECTS-UNREAD]",
                &["and the driver read 0 object(s) LLD compiled for the link"],
            );
        }
        assert!(fs::read_dir(dir.join("cache")).unwrap().next().is_some());
        // `-plugin-opt=emit-llvm`: every file empty, and LLVM bitcode where
        // the image belongs, which every Linux link's `.eh_frame` check
        // refuses; nothing is installed.
        refused_leaving_output(
            dir,
            Some(emit_llvm_bin.as_path()),
            &pie("gb_llvm_pie", "-Wl,gb_slots.o,gb_fat.o,gb_user.o"),
            "[TCG-LINK-EH-FRAME-UNPROVEN]",
            &["the image cannot be read as an ELF image (not an ELF64 little-endian image)"],
        );
        // A counted ThinLTO input beside the uncounted fat object: the
        // compiled object is named after both.
        refused_leaving_output(
            dir,
            Some(fat_bin.as_path()),
            &pie("gb_mixed_pie", "-Wl,gb_slots.o,thin.bc,gb_fat.o,gb_user.o"),
            "[TCG-LINK-GOT-PAGE-UNPROVEN]",
            &[
                "(an object LLD compiled from the LLVM bitcode input thin.bc or the LLVM bitcode \
               input gb_fat.o's `.llvm.lto` section at link time): R_AARCH64_LD64_GOTPAGE_LO15 \
               against `dv_last`",
            ],
        );
    }

    /// `main` prints `isize_add_one(41)` (the b1 fixture's `tm` module) and
    /// exits 0 when it is 42.
    const TM_IR: &str = "; TrustIr text format v1\nmodule \"tm\"\n\nfuncty.0 = (i64) -> (i64)\n\n\
        fn @isize_add_one(functy.0) {\nbb0(%0: i64):\n    %1 = const i64 1\n    %2 = add i64 %0, \
        %1\n    ret %2\n}\n";

    /// Calls `isize_add_one` and prints its value.
    const TM_MAIN: &str = "#include <stdio.h>\nextern long isize_add_one(long);\nint main(void) { \
        long v = isize_add_one(41); printf(\"v=%ld\\n\", v); return v == 42 ? 0 : 1; }\n";

    /// Calls `f65999` (the last function of [`extended_numbering_source`])
    /// too: exits 0 when it returns 65999 % 4096.
    const XNUM_MAIN: &str = "#include <stdio.h>\nextern long isize_add_one(long);\nextern int \
        f65999(void);\nint main(void) { long v = isize_add_one(41); int f = f65999(); \
        printf(\"v=%ld f=%d\\n\", v, f); return v == 42 && f == 65999 % 4096 ? 0 : 1; }\n";

    /// An assembly source of 66,000 functions, each in its own section: the
    /// object uses ELF extended section numbering (`e_shnum` 0,
    /// `e_shstrndx` `SHN_XINDEX`, `f65999` in section 66,003).
    fn extended_numbering_source() -> String {
        let mut source = String::new();
        for index in 0..66_000 {
            source += &format!(
                "\t.section .text.f{index},\"ax\",%progbits\n\t.globl f{index}\n\t.type f{index}, \
                 %function\nf{index}:\n\tmov w0, #{}\n\tret\n",
                index % 4096
            );
        }
        source
    }

    /// `main` adds `one_only(1)` (6) and `isize_add_one(41)`: exits 0 on 48.
    const THIN_MAIN: &str = "#include <stdio.h>\nextern long one_only(long), isize_add_one(long);\n\
        int main(void) { long r = one_only(1) + isize_add_one(41); printf(\"r=%ld\\n\", r); return \
        r == 48 ? 0 : 1; }\n";

    /// A static glibc program that looks a user up: GNU ld 2.42 warns about
    /// `getpwuid` and, with `--gc-sections`, prints a note on standard
    /// output.
    const NSS_MAIN: &str = "#include <pwd.h>\n#include <stdio.h>\n#include <unistd.h>\nextern long \
        isize_add_one(long);\nint main(void) { struct passwd *p = getpwuid(getuid()); \
        printf(\"user=%s\\n\", p ? p->pw_name : \"?\"); return isize_add_one(41) == 42 ? 0 : 1; }\n";

    /// libgcc's outline-atomics helpers that libgcc_eh's frame registration
    /// takes its lock through, as a compiler-rt or compiler_builtins object
    /// defines them (load-exclusive/store-exclusive loops).
    const ATOMICS_HELPERS: &str = "\t.text\n\t.globl __aarch64_cas8_acq_rel\n\t.type \
        __aarch64_cas8_acq_rel, %function\n__aarch64_cas8_acq_rel:\n\tmov x16, x0\n0:\tldaxr x0, \
        [x2]\n\tcmp x0, x16\n\tb.ne 1f\n\tstlxr w17, x1, [x2]\n\tcbnz w17, 0b\n1:\tret\n\t.globl \
        __aarch64_swp8_acq_rel\n\t.type __aarch64_swp8_acq_rel, \
        %function\n__aarch64_swp8_acq_rel:\n\tmov x16, x0\n0:\tldaxr x0, [x1]\n\tstlxr w17, x16, \
        [x1]\n\tcbnz w17, 0b\n\tret\n";

    /// Fedora's package note, a GNU ld `INSERT` script (`-dT` in its
    /// `LDFLAGS`).
    const PACKAGE_NOTE: &str = "SECTIONS\n{\n  .note.package (READONLY) : ALIGN(4) {\n    \
        BYTE(0x04) BYTE(0x00) BYTE(0x00) BYTE(0x00)\n    BYTE(0x04) BYTE(0x00) BYTE(0x00) \
        BYTE(0x00)\n    BYTE(0x7e) BYTE(0x1a) BYTE(0xfe) BYTE(0xca)\n    BYTE(0x46) BYTE(0x44) \
        BYTE(0x4f) BYTE(0x00)\n    BYTE(0x74) BYTE(0x63) BYTE(0x67) BYTE(0x00)\n  }\n}\nINSERT \
        AFTER .note.gnu.build-id;\n";

    /// A library function that calls `host_provided`, which the library's
    /// user defines.
    const UNDEF_LIB: &str =
        "extern int host_provided(void);\nint lib_fn(void) { return host_provided() + 1; }\n";

    /// The ordinary links the eleventh closure audit found refused, through
    /// GNU ld 2.42, LLD 22.1.6 and gold 2.42, each installed and run now:
    /// an input with ELF extended section numbering (66,000 sections; the
    /// reader could not read `e_shnum` 0 and was refused as unreadable) in
    /// dynamic, static and `--gc-sections` links; gold's thin-archive
    /// members, which it names by the path it opened (static, `-L`/`-l`, in
    /// the working directory, a whole-archive shared object); a static NSS
    /// program with `--gc-sections`, whose GNU ld note on standard output
    /// the trace reader skips; `-dT <script>` (GNU ld's and LLD's alias of
    /// `--default-script`, gold's `-d -T`); `-z undefs` in a shared object's
    /// link, which GNU ld and LLD write the same bytes with (it stays
    /// refused in an executable's); the one-dash `-hash-style=sysv`, which
    /// all three read as `--hash-style` (a prefix of it stays refused); and
    /// `--dependency-file`, whose file now names the output instead of the
    /// staged image, is not written over the output, and is left alone by a
    /// refused link. A static link whose input defines libgcc's
    /// outline-atomics helpers (as a Rust staticlib's compiler_builtins
    /// does) stays refused, as a named conservative class: libgcc_eh's frame
    /// registration takes its lock through them, and the driver does not
    /// read whether a definition does the same; the same link outside the
    /// driver runs.
    #[test]
    fn ordinary_links_the_eleventh_audit_found_refused_are_installed() {
        let directory = tempfile::tempdir().unwrap();
        let dir = directory.path();
        fs::create_dir_all(dir.join("dup/sub")).unwrap();
        for (name, text) in [
            ("tm.trust_ir", TM_IR),
            ("main.c", TM_MAIN),
            ("xmain.c", XNUM_MAIN),
            ("xbig.s", extended_numbering_source().as_str()),
            ("dup/om.c", THIN_MAIN),
            ("dup/sub/one.c", "long one_only(long x) { return x + 5; }\n"),
            ("nss.c", NSS_MAIN),
            ("atomics.s", ATOMICS_HELPERS),
            ("pkgnote.ld", PACKAGE_NOTE),
            ("undef_lib.c", UNDEF_LIB),
        ] {
            fs::write(dir.join(name), text).unwrap();
        }
        for (flags, object, source) in [
            (&["-O1"][..], "main.o", "main.c"),
            (&["-O1"], "xmain.o", "xmain.c"),
            (&[], "xbig.o", "xbig.s"),
            (&["-O1"], "dup/om.o", "dup/om.c"),
            (&["-O1", "-fpic"], "dup/sub/one.o", "dup/sub/one.c"),
            (&["-O1"], "nss.o", "nss.c"),
            (&[], "atomics.o", "atomics.s"),
            (&["-O1", "-fpic"], "undef_lib.o", "undef_lib.c"),
        ] {
            let mut args = vec!["-c"];
            args.extend(flags);
            args.extend(["-o", object, source]);
            run_tool(dir, "cc", &args);
        }
        let header = Command::new("readelf")
            .args(["-h"])
            .arg(dir.join("xbig.o"))
            .output()
            .unwrap();
        assert!(
            String::from_utf8_lossy(&header.stdout)
                .contains("Number of section headers:         0 ("),
            "{header:?}"
        );
        // Thin archives: the member's recorded name is relative to the
        // archive's directory.
        run_tool(dir, "ar", &["qcT", "dup/libthin_sub.a", "dup/sub/one.o"]);
        let object = trust_cg_on(
            None,
            dir,
            &["--format=text", "-c", "-o", "tm.o", "tm.trust_ir"],
        );
        assert!(object.status.success(), "{}", stderr(&object));
        let run = |bin: Option<&Path>, name: &str, extra: &[&str], group: &str| {
            let mut args = vec!["--format=text"];
            args.extend(extra);
            args.extend(["-o", name, "tm.trust_ir", group]);
            installed_and_run(dir, bin, &args)
        };
        for (linker, bin) in linkers(dir) {
            let bin = bin.as_deref();
            let cc = bin.map_or_else(
                || "cc".to_string(),
                |bin| bin.join("cc").display().to_string(),
            );
            // Extended section numbering.
            for (name, extra, group) in [
                ("xnum", &[][..], "-Wl,xmain.o,xbig.o"),
                ("xnum_static", &["--static"], "-Wl,xmain.o,xbig.o"),
                ("xnum_gc", &[], "-Wl,xmain.o,xbig.o,--gc-sections"),
            ] {
                let name = format!("{name}_{linker}");
                assert_eq!(
                    run(bin, &name, extra, group),
                    (Some(0), "v=42 f=463\n".to_string()),
                    "{name}"
                );
            }
            // Thin archives, named by gold by the member's opened path.
            for (name, extra, group) in [
                (
                    "thin_static",
                    &["--static"][..],
                    "-Wl,dup/om.o,dup/libthin_sub.a",
                ),
                ("thin_l", &["--static"], "-Wl,dup/om.o,-Ldup,-lthin_sub"),
                ("thin", &[], "-Wl,dup/om.o,dup/libthin_sub.a"),
            ] {
                let name = format!("{name}_{linker}");
                assert_eq!(
                    run(bin, &name, extra, group),
                    (Some(0), "r=48\n".to_string()),
                    "{name}"
                );
            }
            let library = format!("libthin_{linker}.so");
            let result = trust_cg_on(
                bin,
                dir,
                &[
                    "--format=text",
                    "--shared",
                    "--relocation-model",
                    "pic",
                    "-o",
                    &library,
                    "tm.trust_ir",
                    "-Wl,--whole-archive,dup/libthin_sub.a,--no-whole-archive",
                ],
            );
            assert!(result.status.success(), "{library}: {}", stderr(&result));
            // A static NSS program with `--gc-sections`.
            let name = format!("nss_gc_{linker}");
            let (code, stdout) = run(bin, &name, &["--static"], "-Wl,nss.o,--gc-sections");
            assert!(
                code == Some(0) && stdout.starts_with("user="),
                "{name}: {stdout}"
            );
            // libgcc's outline-atomics helpers defined by another input.
            let name = format!("atomics_{linker}");
            refused_with(
                dir,
                bin,
                &[
                    "--format=text",
                    "--static",
                    "-o",
                    &name,
                    "tm.trust_ir",
                    "-Wl,main.o,atomics.o",
                ],
                "[TCG-LINK-IRELATIVE-UNAPPLIED]",
                &["a compiler support routine of the C driver's own libgcc.a"],
            );
            let raw = format!("atomics_raw_{linker}");
            run_tool(
                dir,
                &cc,
                &["-static", "-o", &raw, "main.o", "atomics.o", "tm.o"],
            );
            assert_eq!(
                run_program(&dir.join(&raw)),
                (Some(0), "v=42\n".to_string()),
                "{raw}"
            );
            // `-hash-style=sysv` with one dash is `--hash-style=sysv`.
            let name = format!("hash_{linker}");
            let result = trust_cg_on(
                bin,
                dir,
                &[
                    "--format=text",
                    "-o",
                    &name,
                    "tm.trust_ir",
                    "-Wl,main.o,-hash-style=sysv",
                ],
            );
            assert!(result.status.success(), "{name}: {}", stderr(&result));
            let dynamic = Command::new("readelf")
                .args(["-dW"])
                .arg(dir.join(&name))
                .output()
                .unwrap();
            let dynamic = String::from_utf8_lossy(&dynamic.stdout);
            assert!(
                dynamic.contains("(HASH)")
                    && !dynamic.contains("GNU_HASH")
                    && !dynamic.contains("SONAME"),
                "{name}: {dynamic}"
            );
            assert_eq!(
                run_program(&dir.join(&name)),
                (Some(0), "v=42\n".to_string())
            );
            refused_with(
                dir,
                bin,
                &[
                    "--format=text",
                    "-o",
                    "hash_prefix",
                    "tm.trust_ir",
                    "-Wl,main.o,-hash-st=sysv",
                ],
                "is controlled by the trust-cg option `--soname`",
                &[],
            );
            // `--dependency-file`: named for the output, never over it, not
            // written by a refused link.
            let name = format!("dep_{linker}");
            let depfile = format!("dep_{linker}.d");
            assert_eq!(
                run(
                    bin,
                    &name,
                    &[],
                    &format!("-Wl,main.o,--dependency-file={depfile}")
                ),
                (Some(0), "v=42\n".to_string())
            );
            let written = fs::read_to_string(dir.join(&depfile)).unwrap();
            assert!(written.starts_with(&format!("{name}:")), "{written}");
            let name = format!("dep_self_{linker}");
            let result = trust_cg_on(
                bin,
                dir,
                &[
                    "--format=text",
                    "-o",
                    &name,
                    "tm.trust_ir",
                    &format!("-Wl,main.o,--dependency-file={name}"),
                ],
            );
            assert!(
                result.status.success()
                    && stderr(&result).contains("is not written: its file")
                    && run_program(&dir.join(&name)) == (Some(0), "v=42\n".to_string()),
                "{name}: {}",
                stderr(&result)
            );
            let name = format!("dep_refused_{linker}");
            refused_leaving_output(
                dir,
                bin,
                &[
                    "--format=text",
                    "-o",
                    &name,
                    "tm.trust_ir",
                    &format!("-Wl,main.o,-z,max-page-size=16,--dependency-file={name}"),
                ],
                "[TCG-LINK-LOADED-BYTES]",
                &[],
            );
            if linker == "gold" {
                // gold rejects the package note's `INSERT` and `-z undefs`.
                continue;
            }
            // `-z undefs` in a shared object's link: the same bytes.
            let libraries: Vec<Vec<u8>> = ["", ",-z,undefs", ",-z,defs,-z,undefs"]
                .iter()
                .enumerate()
                .map(|(index, extra)| {
                    let library = format!("libu{index}_{linker}.so");
                    let result = trust_cg_on(
                        bin,
                        dir,
                        &[
                            "--format=text",
                            "--shared",
                            "--relocation-model",
                            "pic",
                            "-o",
                            &library,
                            "tm.trust_ir",
                            &format!("-Wl,undef_lib.o{extra}"),
                        ],
                    );
                    assert!(result.status.success(), "{library}: {}", stderr(&result));
                    fs::read(dir.join(&library)).unwrap()
                })
                .collect();
            assert!(
                libraries[1] == libraries[0] && libraries[2] == libraries[0],
                "{linker}"
            );
            refused_with(
                dir,
                bin,
                &[
                    "--format=text",
                    "-o",
                    "undefs_exe",
                    "tm.trust_ir",
                    "-Wl,main.o,-z,undefs",
                ],
                "[TCG-LINK-UNRESOLVED-SYMBOLS] `-z undefs` is refused in an executable link",
                &[],
            );
            if linker == "gnu" {
                // `-dT <script>`: GNU ld's `--default-script`.
                for (name, extra) in [("dT", &[][..]), ("dT_nopie", &["--no-pie"])] {
                    assert_eq!(
                        run(bin, name, extra, "-Wl,main.o,-dT,pkgnote.ld"),
                        (Some(0), "v=42\n".to_string()),
                        "{name}"
                    );
                }
                let result = trust_cg_on(
                    bin,
                    dir,
                    &[
                        "--format=text",
                        "-o",
                        "dT_note",
                        "tm.trust_ir",
                        "-Wl,main.o,-dT,pkgnote.ld",
                    ],
                );
                assert!(result.status.success(), "{}", stderr(&result));
                let sections = Command::new("readelf")
                    .args(["-SW"])
                    .arg(dir.join("dT_note"))
                    .output()
                    .unwrap();
                assert!(String::from_utf8_lossy(&sections.stdout).contains(".note.package"));
            }
        }
    }

    /// The tenth closure audit's fail-open options, through GNU ld 2.42,
    /// LLD 22.1.6 and gold 2.42: with `-Wl,--noinhibit-exec` each linker
    /// wrote trust-cg's `R_AARCH64_TLSLE_ADD_TPREL_HI12` behind a 16 MiB
    /// `.tdata` truncated and exited 0, and the driver installed a program
    /// that wrote the C thread-local instead of its own (`w=49`, exit 1).
    /// Each spelling is refused by name before any process runs
    /// (`[TCG-LINK-NOINHIBIT-EXEC]`), GNU ld's hidden `--noinhibit_exec`
    /// among them. A `cc` that adds the option behind the driver's back
    /// shows the second defense: the linker's report of the value is
    /// refused (`[TCG-LINK-RANGE-WARNING]`), nothing is written, and the
    /// same `cc` links the 16-byte-pad twin, which runs. The raw far image
    /// outside the driver misbehaves as the audit saw.
    #[test]
    fn a_link_the_linker_would_refuse_is_never_made_to_succeed() {
        let directory = tempfile::tempdir().unwrap();
        let dir = directory.path();
        fs::write(dir.join("le.trust_ir"), LE_IR).unwrap();
        fs::write(dir.join("lemain.c"), LE_MAIN).unwrap();
        run_tool(dir, "cc", &["-c", "-O1", "-o", "lemain.o", "lemain.c"]);
        assemble(dir, "padt", &tdata_pad(16 << 20));
        assemble(dir, "padn", &tdata_pad(16));
        for (spelling, code) in [
            ("--noinhibit-exec", "[TCG-LINK-NOINHIBIT-EXEC]"),
            ("-noinhibit-exec", "[TCG-LINK-NOINHIBIT-EXEC]"),
            ("--noinhibit_exec", "[TCG-LINK-NOINHIBIT-EXEC]"),
            ("--noinhibit-", "[TCG-LINK-NOINHIBIT-EXEC]"),
            ("-w", "[TCG-LINK-NO-WARNINGS]"),
            ("--no-warnings", "[TCG-LINK-NO-WARNINGS]"),
            ("-no-warnings", "[TCG-LINK-NO-WARNINGS]"),
            ("--no-warni", "[TCG-LINK-NO-WARNINGS]"),
            ("-ws", "[TCG-LINK-OPTION-GROUP]"),
            ("-sw", "[TCG-LINK-OPTION-GROUP]"),
            ("-wx", "[TCG-LINK-OPTION-GROUP]"),
        ] {
            let group = format!("-Wl,lemain.o,padt.o,{spelling}");
            refused_with(
                dir,
                None,
                &["--format=text", "-o", "le_opt", "le.trust_ir", &group],
                code,
                &[spelling],
            );
        }
        for (linker, bin) in linkers(dir) {
            let failing = appending_cc(
                dir,
                &format!("{linker}-noinhibit"),
                bin.as_deref(),
                "-Wl,--noinhibit-exec",
            );
            // Without the option the linker refuses; with it the driver does.
            let far = format!("le_far_{linker}");
            refused_with(
                dir,
                bin.as_deref(),
                &[
                    "--format=text",
                    "-o",
                    &far,
                    "le.trust_ir",
                    "-Wl,lemain.o,padt.o",
                ],
                "error[link:relocation-out-of-range]",
                &["R_AARCH64_TLSLE_ADD_TPREL_HI12"],
            );
            refused_with(
                dir,
                Some(&failing),
                &[
                    "--format=text",
                    "-o",
                    &far,
                    "le.trust_ir",
                    "-Wl,lemain.o,padt.o",
                ],
                "[TCG-LINK-RANGE-WARNING]",
                &["R_AARCH64_TLSLE_ADD_TPREL_HI12"],
            );
            let near = format!("le_near_{linker}");
            assert_eq!(
                installed_and_run(
                    dir,
                    Some(&failing),
                    &[
                        "--format=text",
                        "-o",
                        &near,
                        "le.trust_ir",
                        "-Wl,lemain.o,padn.o"
                    ],
                ),
                (Some(0), "v=42 w=84\n".to_string()),
                "{linker}"
            );
        }
        // The far image outside the driver: truncated, it misbehaves.
        let object = trust_cg_on(
            None,
            dir,
            &["--format=text", "-c", "-o", "le.o", "le.trust_ir"],
        );
        assert!(object.status.success(), "{}", stderr(&object));
        run_tool(
            dir,
            "cc",
            &[
                "-o",
                "le_raw",
                "le.o",
                "lemain.o",
                "padt.o",
                "-Wl,--noinhibit-exec",
            ],
        );
        let (code, stdout) = run_program(&dir.join("le_raw"));
        assert_eq!(code, Some(1), "{stdout}");
        // GNU ld's `-w` and its groups say nothing and exit 0: no range
        // warning is left for the driver to read, so only the refusal by
        // name keeps them out.
        for spelling in ["-w", "-sw"] {
            let raw = Command::new("cc")
                .current_dir(dir)
                .args(["-o", "le_raw_w", "le.o", "lemain.o", "padt.o"])
                .arg(format!("-Wl,{spelling}"))
                .output()
                .unwrap();
            assert!(
                raw.status.success() && !stderr(&raw).contains("R_AARCH64_TLSLE_ADD_TPREL_HI12"),
                "{spelling}: {raw:?}"
            );
            let (code, stdout) = run_program(&dir.join("le_raw_w"));
            assert_eq!(code, Some(1), "{spelling}: {stdout}");
        }
    }

    /// `-Wl,--no-check-sections` let GNU ld 2.42 and LLD 22.1.6 place a C
    /// section 16 bytes into trust-cg's `.data`; GNU ld printed nothing and
    /// its program read 0 for the trust-cg global whose file bytes held 42.
    /// The option is refused by name in each spelling
    /// (`[TCG-LINK-NO-CHECK-SECTIONS]`); a `cc` that adds it behind the
    /// driver's back has its image refused because its loaded memory is not
    /// what its sections hold (`[TCG-LINK-LOADED-BYTES]`), and the same `cc`
    /// links the twin whose `.ovl` does not overlap, which runs.
    #[test]
    fn overlapping_sections_are_never_installed() {
        let directory = tempfile::tempdir().unwrap();
        let dir = directory.path();
        fs::write(dir.join("val.trust_ir"), VAL_IR).unwrap();
        fs::write(dir.join("vmainovl.c"), OVL_MAIN).unwrap();
        run_tool(dir, "cc", &["-c", "-O1", "-o", "vmainovl.o", "vmainovl.c"]);
        let over = "-Wl,vmainovl.o,--section-start=.data=0x500000,--section-start=.ovl=0x500010";
        let apart = "-Wl,vmainovl.o,--section-start=.data=0x500000,--section-start=.ovl=0x500020";
        for spelling in ["--no-check-sections", "-no-check-sections", "--no-ch"] {
            let group = format!("{over},{spelling}");
            refused_with(
                dir,
                None,
                &[
                    "--format=text",
                    "--no-pie",
                    "-o",
                    "ov_opt",
                    "val.trust_ir",
                    &group,
                ],
                "[TCG-LINK-NO-CHECK-SECTIONS]",
                &[spelling],
            );
        }
        for (linker, bin) in linkers(dir) {
            if linker == "gold" {
                // gold 2.42 fails such a link itself.
                continue;
            }
            let failing = appending_cc(
                dir,
                &format!("{linker}-nocheck"),
                bin.as_deref(),
                "-Wl,--no-check-sections",
            );
            let output = format!("ov_{linker}");
            refused_with(
                dir,
                Some(&failing),
                &[
                    "--format=text",
                    "--no-pie",
                    "-o",
                    &output,
                    "val.trust_ir",
                    over,
                ],
                "[TCG-LINK-LOADED-BYTES]",
                &["overlap in memory"],
            );
            let twin = format!("ov_apart_{linker}");
            assert_eq!(
                installed_and_run(
                    dir,
                    Some(&failing),
                    &[
                        "--format=text",
                        "--no-pie",
                        "-o",
                        &twin,
                        "val.trust_ir",
                        apart
                    ],
                ),
                (Some(0), "tcg_val=42 ovl=7\n".to_string()),
                "{linker}"
            );
        }
    }

    /// LLD 22.1.6 writes relocations glibc's AArch64 port never applies on
    /// request, and the driver installed each (the tenth closure audit):
    /// `--static -Wl,-z,rel` (`IRELATIVE` in an `SHT_REL` `.rel.dyn`,
    /// SIGSEGV), a static PIE with `-z rel` (SIGSEGV), a PIE with
    /// `--pack-dyn-relocs=android` (SIGSEGV) or with `-z rel` or
    /// `--pack-dyn-relocs=relr` (`ld.so` refuses to load it, 127). `-z rel`
    /// is refused by name; behind the driver's back each image is refused as
    /// `[TCG-LINK-RELOCATION-FORMAT]`. LLD's and GNU ld's `-z
    /// pack-relative-relocs` (which add the `GLIBC_ABI_DT_RELR` dependency),
    /// a static PIE with `DT_RELR` and the plain twins run.
    #[test]
    fn relocation_formats_glibc_does_not_apply_are_never_installed() {
        let directory = tempfile::tempdir().unwrap();
        let dir = directory.path();
        fs::write(dir.join("ret.trust_ir"), RET_IR).unwrap();
        refused_with(
            dir,
            None,
            &[
                "--format=text",
                "--static",
                "-o",
                "zrel",
                "ret.trust_ir",
                "-Wl,-z,rel",
            ],
            "[TCG-LINK-RELOCATION-FORMAT] `-z rel` is refused",
            &[],
        );
        let gcc = String::from_utf8(
            Command::new("cc")
                .arg("-print-libgcc-file-name")
                .output()
                .unwrap()
                .stdout,
        )
        .unwrap();
        let gcc = Path::new(gcc.trim()).parent().unwrap().to_path_buf();
        let file = |name: &str| {
            let found = Command::new("cc")
                .arg(format!("-print-file-name={name}"))
                .output()
                .unwrap()
                .stdout;
            String::from_utf8(found).unwrap().trim().to_string()
        };
        let static_pie = format!(
            "-Wl,--no-dynamic-linker,-z,text,{},{},{},-Bstatic,--start-group,-lgcc,-lgcc_eh,-lc,\
             --end-group,{},{}",
            file("rcrt1.o"),
            file("crti.o"),
            gcc.join("crtbeginS.o").display(),
            gcc.join("crtendS.o").display(),
            file("crtn.o")
        );
        let plain = |bin: Option<&Path>, name: &str, extra: &[&str]| {
            let mut args = vec!["--format=text", "-o", name, "ret.trust_ir"];
            args.extend(extra);
            assert_eq!(installed_and_run(dir, bin, &args).0, Some(42), "{name}");
        };
        plain(None, "gnu_packed", &["-Wl,-z,pack-relative-relocs"]);
        let Some(lld) = lld_dir() else {
            return;
        };
        let lld = lld_cc(dir, &lld);
        let static_pie_args = ["--pie", "--nostdlib", static_pie.as_str()];
        plain(Some(&lld), "lld_static", &["--static"]);
        plain(Some(&lld), "lld_pie", &[]);
        plain(Some(&lld), "lld_static_pie", &static_pie_args);
        plain(Some(&lld), "lld_packed", &["-Wl,-z,pack-relative-relocs"]);
        let relr_static_pie = format!("{static_pie},--pack-dyn-relocs=relr");
        plain(
            Some(&lld),
            "lld_static_pie_relr",
            &["--pie", "--nostdlib", relr_static_pie.as_str()],
        );
        for (name, option, extra, text) in [
            (
                "zrel_static",
                "-Wl,-z,rel",
                &["--static"][..],
                "SHT_REL relocations",
            ),
            (
                "zrel_static_pie",
                "-Wl,-z,rel",
                &static_pie_args[..],
                "SHT_REL relocations",
            ),
            ("zrel_pie", "-Wl,-z,rel", &[][..], "SHT_REL relocations"),
            (
                "android_pie",
                "-Wl,--pack-dyn-relocs=android",
                &[][..],
                "SHT_ANDROID_REL",
            ),
            (
                "relr_pie",
                "-Wl,--pack-dyn-relocs=relr",
                &[][..],
                "no version its DT_VERNEED entries need is GLIBC_ABI_DT_RELR",
            ),
        ] {
            let failing = appending_cc(dir, &format!("lld-{name}"), Some(&lld), option);
            let mut args = vec!["--format=text", "-o", name, "ret.trust_ir"];
            args.extend(extra);
            refused_with(
                dir,
                Some(&failing),
                &args,
                "[TCG-LINK-RELOCATION-FORMAT]",
                &[text],
            );
        }
    }

    /// A static glibc program starts where the start file's `_start` is,
    /// or glibc's start-up code does not apply its IFUNC relocations: the
    /// tenth closure audit's `--static -Wl,main_ifunc.o,myentry.o,-e,_mystart`
    /// hung through GNU ld 2.42 and died with SIGSEGV through LLD 22.1.6 and
    /// gold 2.42. Every way to name another entry (`-e`, `--entry=`, a
    /// `--defsym` of `_start`, a script's `ENTRY`), stripped or not, is
    /// refused as `[TCG-LINK-IRELATIVE-UNAPPLIED]` naming the entry point and
    /// the start file's `_start`, through each linker; the programs without
    /// one, stripped or not, run and return 42. A static PIE (glibc's
    /// `rcrt1.o` route) that starts at `_mystart` skips its self-relocation
    /// (GNU ld's image outside the driver dies with SIGSEGV) and is refused
    /// as `[TCG-LINK-DYNAMIC-NO-INTERP]` naming the entry point, through GNU
    /// ld and LLD; its twin runs.
    #[test]
    fn a_static_program_that_does_not_start_at_the_start_file_is_refused() {
        let directory = tempfile::tempdir().unwrap();
        let dir = directory.path();
        fs::write(dir.join("ret42.trust_ir"), RET42_IR).unwrap();
        fs::write(dir.join("main_ifunc.c"), IFUNC_MAIN).unwrap();
        run_tool(
            dir,
            "cc",
            &["-c", "-O1", "-o", "main_ifunc.o", "main_ifunc.c"],
        );
        assemble(dir, "myentry", MY_ENTRY);
        fs::write(dir.join("entry.ld"), "ENTRY(_mystart)\n").unwrap();
        for (linker, bin) in linkers(dir) {
            let bin = bin.as_deref();
            for strip in ["", ",-s"] {
                let group = format!("-Wl,main_ifunc.o,myentry.o{strip}");
                let name = format!("entry_ctl_{linker}{}", strip.len());
                assert_eq!(
                    installed_and_run(
                        dir,
                        bin,
                        &[
                            "--format=text",
                            "--static",
                            "-o",
                            &name,
                            "ret42.trust_ir",
                            &group
                        ],
                    )
                    .0,
                    Some(42),
                    "{name}"
                );
                for (index, route) in [
                    "-e,_mystart",
                    "--entry=_mystart",
                    "--defsym=_start=_mystart",
                    "entry.ld",
                ]
                .iter()
                .enumerate()
                {
                    let group = format!("{group},{route}");
                    let name = format!("entry_{linker}{}_{index}", strip.len());
                    // A script is refused for the start-up code it can
                    // redirect before the entry point is read.
                    let texts: &[&str] = if route.ends_with(".ld") {
                        &[]
                    } else {
                        &["the image's entry point is", "crt1.o's _start"]
                    };
                    refused_with(
                        dir,
                        bin,
                        &[
                            "--format=text",
                            "--static",
                            "-o",
                            &name,
                            "ret42.trust_ir",
                            &group,
                        ],
                        "[TCG-LINK-IRELATIVE-UNAPPLIED]",
                        texts,
                    );
                }
            }
            if linker == "gold" {
                // gold 2.42 writes no static PIE.
                continue;
            }
            let file = |name: &str| {
                let found = Command::new("cc")
                    .arg(format!("-print-file-name={name}"))
                    .output()
                    .unwrap()
                    .stdout;
                String::from_utf8(found).unwrap().trim().to_string()
            };
            let static_pie = format!(
                "-Wl,--no-dynamic-linker,-z,text,main_ifunc.o,myentry.o,{},{},{},-Bstatic,\
                 --start-group,-lgcc,-lgcc_eh,-lc,--end-group,{},{}",
                file("rcrt1.o"),
                file("crti.o"),
                file("crtbeginS.o"),
                file("crtendS.o"),
                file("crtn.o")
            );
            let name = format!("entry_pie_ctl_{linker}");
            let args = [
                "--format=text",
                "--pie",
                "--nostdlib",
                "-o",
                &name,
                "ret42.trust_ir",
            ];
            let mut control = args.to_vec();
            control.push(&static_pie);
            assert_eq!(installed_and_run(dir, bin, &control).0, Some(42), "{name}");
            let entry = format!("{static_pie},-e,_mystart");
            let name = format!("entry_pie_{linker}");
            let args = [
                "--format=text",
                "--pie",
                "--nostdlib",
                "-o",
                &name,
                "ret42.trust_ir",
            ];
            let mut refused = args.to_vec();
            refused.push(&entry);
            refused_with(
                dir,
                bin,
                &refused,
                "[TCG-LINK-DYNAMIC-NO-INTERP]",
                &["the image's entry point is", "rcrt1.o's _start"],
            );
        }
    }

    /// GNU ld's address options are not linker scripts: the tenth closure
    /// audit's static glibc links with `-Ttext-segment=`, `-Tbss=`,
    /// `-Tdata=`, `-Ttext=` (each linker that accepts it), `-check-sections`
    /// and `-compress-debug-sections=zlib` were refused as
    /// `[TCG-LINK-IRELATIVE-UNAPPLIED]` because every `-T` or one-dash `-c`
    /// piece was taken to name a script. Each is now read by the measured
    /// table of the link's linker, installed and run; a real `-T` script is
    /// still refused.
    #[test]
    fn static_links_with_address_options_are_installed() {
        let directory = tempfile::tempdir().unwrap();
        let dir = directory.path();
        fs::write(dir.join("ret42.trust_ir"), RET42_IR).unwrap();
        fs::write(dir.join("main_ifunc.c"), IFUNC_MAIN).unwrap();
        run_tool(
            dir,
            "cc",
            &["-c", "-O1", "-o", "main_ifunc.o", "main_ifunc.c"],
        );
        // A script each linker links with: GNU ld and LLD insert a section
        // rule, gold (which reads no `INSERT`) takes one that says nothing.
        fs::write(
            dir.join("insert.ld"),
            "SECTIONS { .text : { *(.text .text.*) } }\nINSERT AFTER .init;\n",
        )
        .unwrap();
        fs::write(dir.join("empty.ld"), "/* a script */\n").unwrap();
        for (linker, bin) in linkers(dir) {
            let bin = bin.as_deref();
            let options: &[&str] = match linker {
                "gnu" => &[
                    "-Ttext-segment=0x10000000",
                    "-Ttext-segment,0x10000000",
                    "-Tbss=0x20000000",
                    "-Tdata=0x20000000",
                    "-check-sections",
                    "-compress-debug-sections=zlib",
                ],
                "lld" => &[
                    "-Tbss=0x20000000",
                    "-Tdata=0x20000000",
                    "-Ttext=0x10000000",
                    "-Ttext,0x10000000",
                    "-check-sections",
                    "-compress-debug-sections=zlib",
                ],
                _ => &[
                    "-Tdata=0x20000000",
                    "-check-sections",
                    "-compress-debug-sections=zlib",
                ],
            };
            for (index, option) in options.iter().enumerate() {
                let group = format!("-Wl,main_ifunc.o,{option}");
                let name = format!("addr_{linker}_{index}");
                assert_eq!(
                    installed_and_run(
                        dir,
                        bin,
                        &[
                            "--format=text",
                            "--static",
                            "-o",
                            &name,
                            "ret42.trust_ir",
                            &group
                        ],
                    )
                    .0,
                    Some(42),
                    "{linker} {option}"
                );
            }
            let name = format!("script_{linker}");
            let script = if linker == "gold" {
                "-Wl,main_ifunc.o,-T,empty.ld"
            } else {
                "-Wl,main_ifunc.o,-T,insert.ld"
            };
            refused_with(
                dir,
                bin,
                &[
                    "--format=text",
                    "--static",
                    "-o",
                    &name,
                    "ret42.trust_ir",
                    script,
                ],
                "[TCG-LINK-IRELATIVE-UNAPPLIED]",
                &[],
            );
        }
    }

    /// GCC small-PIC (`-fpic`) objects carry `R_AARCH64_LD64_GOTPAGE_LO15`.
    /// GNU ld 2.42 and gold 2.42 refuse such a value out of its window
    /// themselves, so their stripped links, which have no symbol table to
    /// locate the GOT base in, are installed and run (the tenth closure
    /// audit found every one refused). LLD 22.1.6 writes the value
    /// truncated: its stripped dynamic links take the base from LLD's map,
    /// and its unstripped static link, whose IPLT slots lie 74 KiB above the
    /// base, is installed because the uses' symbol (`__stack_chk_guard`) is
    /// no IFUNC; each runs. LLD's stripped static link (no symbol table to
    /// type the symbol in) and a static program whose small-PIC GOT load of
    /// an IFUNC LLD writes truncated (its own program dies with SIGSEGV) are
    /// refused as `[TCG-LINK-GOT-PAGE-UNPROVEN]`; the program that also
    /// takes the IFUNC's address directly (LLD then puts its slot in `.got`)
    /// runs.
    #[test]
    fn small_pic_objects_link_where_their_got_window_is_shown() {
        let directory = tempfile::tempdir().unwrap();
        let dir = directory.path();
        fs::write(dir.join("ret42.trust_ir"), RET42_IR).unwrap();
        fs::write(
            dir.join("sp.c"),
            "#include <stdio.h>\n#include <string.h>\nextern long tcg_ret42(void);\nint \
             main(int argc, char **argv) { char b[64]; (void)argv; snprintf(b, sizeof b, \"%d\", \
             argc); return strlen(b) == 1 ? (int)tcg_ret42() : 1; }\n",
        )
        .unwrap();
        run_tool(
            dir,
            "cc",
            &[
                "-c",
                "-O1",
                "-fpic",
                "-fstack-protector-all",
                "-o",
                "sp.o",
                "sp.c",
            ],
        );
        let relocations = Command::new("readelf")
            .args(["-rW", "sp.o"])
            .current_dir(dir)
            .output()
            .unwrap();
        assert!(
            String::from_utf8_lossy(&relocations.stdout).contains("R_AARCH64_LD64_GOTPAGE_LO15"),
            "sp.o carries no small-PIC GOT load"
        );
        let linkers = linkers(dir);
        for (linker, bin) in &linkers {
            let (linker, bin) = (*linker, bin.as_deref());
            for mode in ["", "--pie", "--no-pie", "--static"] {
                for strip in ["", ",-s"] {
                    let name = format!("sp_{linker}{}{}", mode.len(), strip.len());
                    let group = format!("-Wl,sp.o{strip}");
                    let mut args = vec!["--format=text", "-o", &name, "ret42.trust_ir", &group];
                    if !mode.is_empty() {
                        args.push(mode);
                    }
                    if linker == "lld" && mode == "--static" && !strip.is_empty() {
                        refused_with(dir, bin, &args, "[TCG-LINK-GOT-PAGE-UNPROVEN]", &[]);
                        continue;
                    }
                    assert_eq!(installed_and_run(dir, bin, &args).0, Some(42), "{name}");
                }
            }
        }
        let Some(lld) = linkers
            .iter()
            .find_map(|(linker, bin)| bin.clone().filter(|_| *linker == "lld"))
        else {
            return;
        };
        fs::write(
            dir.join("def.c"),
            "static int impl(void) { return 7; }\nstatic void *resolve(void) { return (void \
             *)impl; }\nint myf(void) __attribute__((ifunc(\"resolve\")));\n",
        )
        .unwrap();
        fs::write(
            dir.join("gotuse.c"),
            "extern int myf(void);\nvoid *got_addr(void) { return (void *)myf; }\n",
        )
        .unwrap();
        fs::write(
            dir.join("direct.c"),
            "extern int myf(void);\nextern void *got_addr(void);\nextern long \
             tcg_ret42(void);\nint main(void) { void *d = (void *)myf; return d == got_addr() && \
             myf() == 7 ? (int)tcg_ret42() : 1; }\n",
        )
        .unwrap();
        fs::write(
            dir.join("called.c"),
            "extern int myf(void);\nextern void *got_addr(void);\nextern long \
             tcg_ret42(void);\nint main(void) { int (*f)(void) = (int (*)(void))got_addr(); \
             return f() == 7 && myf() == 7 ? (int)tcg_ret42() : 1; }\n",
        )
        .unwrap();
        run_tool(dir, "cc", &["-c", "-O1", "-o", "def.o", "def.c"]);
        run_tool(
            dir,
            "cc",
            &["-c", "-O1", "-fpic", "-o", "gotuse.o", "gotuse.c"],
        );
        run_tool(
            dir,
            "cc",
            &["-c", "-O1", "-fno-pic", "-o", "direct.o", "direct.c"],
        );
        run_tool(
            dir,
            "cc",
            &["-c", "-O1", "-fno-pic", "-o", "called.o", "called.c"],
        );
        refused_with(
            dir,
            Some(&lld),
            &[
                "--format=text",
                "--static",
                "-o",
                "ifunc_got",
                "ret42.trust_ir",
                "-Wl,def.o,gotuse.o,called.o",
            ],
            "[TCG-LINK-GOT-PAGE-UNPROVEN]",
            &["against `myf`"],
        );
        assert_eq!(
            installed_and_run(
                dir,
                Some(&lld),
                &[
                    "--format=text",
                    "--static",
                    "-o",
                    "ifunc_canonical",
                    "ret42.trust_ir",
                    "-Wl,def.o,gotuse.o,direct.o",
                ],
            )
            .0,
            Some(42)
        );
        // LLD's own program with the IFUNC's GOT load truncated.
        let lld_host = lld.join("cc").display().to_string();
        let object = trust_cg_on(
            None,
            dir,
            &["--format=text", "-c", "-o", "ret42.o", "ret42.trust_ir"],
        );
        assert!(object.status.success(), "{}", stderr(&object));
        run_tool(
            dir,
            &lld_host,
            &[
                "-static",
                "-o",
                "ifunc_raw",
                "def.o",
                "gotuse.o",
                "called.o",
                "ret42.o",
            ],
        );
        let status = Command::new(dir.join("ifunc_raw")).status().unwrap();
        assert_eq!(status.signal(), Some(SIGSEGV), "{status:?}");
    }

    /// A C program that calls `missing_fn` and reads `missing_var`, neither
    /// defined anywhere; exits 42 when both are found.
    const UNDEFINED_MAIN: &str = "extern int missing_var;\nextern int missing_fn(void);\nextern \
        long tcg_ret42(void);\nint main(int argc, char **argv) { (void)argv; if (argc > 5) return \
        missing_var + missing_fn(); return (int)tcg_ret42(); }\n";

    /// The options the tenth closure audit's verifier and the fail-open scan
    /// found turning an undefined reference of the linked objects into a
    /// successful link, through GNU ld 2.42, LLD 22.1.6 and gold 2.42:
    /// `--unresolved-symbols=ignore-all` and `=ignore-in-object-files`,
    /// `--warn-unresolved-symbols`, `-z undefs` (GNU ld, LLD) and gold's
    /// `--weak-unresolved-symbols`. Outside the driver each links the
    /// program; through it each is refused by name
    /// (`[TCG-LINK-UNRESOLVED-SYMBOLS]`) and nothing is written. Without an
    /// option every linker refuses the link (`undefined-symbol`), and
    /// `report-all` and `ignore-in-shared-libs` are admitted: those links
    /// fail as the plain one does.
    #[test]
    fn undefined_references_are_never_made_to_link() {
        let directory = tempfile::tempdir().unwrap();
        let dir = directory.path();
        fs::write(dir.join("ret42.trust_ir"), RET42_IR).unwrap();
        fs::write(dir.join("undef.c"), UNDEFINED_MAIN).unwrap();
        run_tool(dir, "cc", &["-c", "-O1", "-o", "undef.o", "undef.c"]);
        let object = trust_cg_on(
            None,
            dir,
            &["--format=text", "-c", "-o", "ret42.o", "ret42.trust_ir"],
        );
        assert!(object.status.success(), "{}", stderr(&object));
        for (linker, bin) in linkers(dir) {
            let bin = bin.as_deref();
            let cc = bin.map_or_else(
                || "cc".to_string(),
                |bin| bin.join("cc").display().to_string(),
            );
            let mut options = vec![
                "--unresolved-symbols=ignore-all",
                "--unresolved-symbols,ignore-in-object-files",
                "--warn-unresolved-symbols",
            ];
            match linker {
                "gold" => options.push("--weak-unresolved-symbols"),
                _ => options.push("-z,undefs"),
            }
            for (index, option) in options.iter().enumerate() {
                let group = format!("-Wl,undef.o,{option}");
                let raw = Command::new(&cc)
                    .current_dir(dir)
                    .args(["-o", "undef_raw", "ret42.o", "undef.o"])
                    .arg(format!("-Wl,{option}"))
                    .output()
                    .unwrap();
                assert!(raw.status.success(), "{linker} {option}: {raw:?}");
                let name = format!("undef_{linker}_{index}");
                refused_with(
                    dir,
                    bin,
                    &["--format=text", "-o", &name, "ret42.trust_ir", &group],
                    "[TCG-LINK-UNRESOLVED-SYMBOLS]",
                    &[],
                );
            }
            for (index, group) in [
                "-Wl,undef.o",
                "-Wl,undef.o,--unresolved-symbols=report-all",
                "-Wl,undef.o,--unresolved-symbols=ignore-in-shared-libs",
            ]
            .iter()
            .enumerate()
            {
                let name = format!("undef_kept_{linker}_{index}");
                refused_with(
                    dir,
                    bin,
                    &["--format=text", "-o", &name, "ret42.trust_ir", group],
                    "error[link:undefined-symbol]",
                    &[],
                );
            }
        }
    }

    /// A one-dash piece gold 2.42 reads as a group of short options is
    /// refused (`[TCG-LINK-OPTION-GROUP]`): outside the driver gold links
    /// `-sofoo` into `foo` (outside any stage) and `-szexecstack` with an
    /// executable stack, and GNU ld links `-sw` as `-s -w`. Through the
    /// driver each is refused with nothing written. The rule is measured
    /// here: no letter outside the group letters starts a group (gold's
    /// `-<letter>ofoo` writes no `foo`, GNU ld's `-<letter>w` keeps its
    /// overflow error), and every one-dash long option a linker's `--help`
    /// names that the driver admits links through gold exactly as its
    /// two-dash spelling (the same exit status, files, bytes and messages)
    /// or is one gold rejects as unknown, but `-dT`, GNU ld's and LLD's
    /// `--default-script`, which gold reads as `-d -T` and links with a
    /// script into the same bytes as `-T`.
    #[test]
    fn short_option_groups_are_refused_and_one_dash_long_options_are_read_as_such() {
        use trust_cg_codegen::link_driver::parse_wl_group;
        use trust_cg_codegen::target::TargetSpec;
        let directory = tempfile::tempdir().unwrap();
        let dir = directory.path();
        fs::write(dir.join("ret.trust_ir"), RET_IR).unwrap();
        fs::write(dir.join("m.c"), "int main(void) { return 0; }\n").unwrap();
        run_tool(dir, "cc", &["-c", "-o", "m.o", "m.c"]);
        assemble(
            dir,
            "far",
            "\t.text\n\t.globl _start\n_start:\n\tadrp x0, far\n\tmov x8, #93\n\tsvc \
             #0\n\t.section .far,\"aw\"\nfar:\t.quad 1\n",
        );
        let linux = TargetSpec::parse("aarch64-unknown-linux-gnu").unwrap();
        let Some(gold) = gold_cc(dir) else {
            return;
        };
        let gold_cc = gold.join("cc").display().to_string();
        let gold_link = |work: &Path, pieces: &str| {
            Command::new(&gold_cc)
                .current_dir(work)
                .args(["-o", "out"])
                .arg(dir.join("m.o"))
                .arg(format!("-Wl,{pieces}"))
                .stdin(std::process::Stdio::null())
                .output()
                .unwrap()
        };
        // gold's groups outside the driver, then through it.
        let work = dir.join("raw");
        fs::create_dir(&work).unwrap();
        assert!(gold_link(&work, "-sofoo").status.success());
        assert!(work.join("foo").exists());
        assert!(gold_link(&work, "-szexecstack").status.success());
        let stack = Command::new("readelf")
            .args(["-lW", "out"])
            .current_dir(&work)
            .output()
            .unwrap();
        assert!(
            String::from_utf8_lossy(&stack.stdout)
                .lines()
                .any(|line| line.contains("GNU_STACK") && line.contains("RWE")),
            "{stack:?}"
        );
        for (bin, piece) in [
            (Some(&gold), "-sofoo"),
            (Some(&gold), "-szexecstack"),
            (Some(&gold), "-no-dynamic-linker"),
            (None, "-sw"),
            (None, "-wx"),
        ] {
            let group = format!("-Wl,{piece}");
            refused_with(
                dir,
                bin.map(PathBuf::as_path),
                &["--format=text", "-o", "grouped", "ret.trust_ir", &group],
                "[TCG-LINK-OPTION-GROUP]",
                &[piece],
            );
            assert!(!dir.join("foo").exists());
        }
        // No other letter starts a group.
        const GROUP_LETTERS: &str = "EGMNSVXdginpqrstvwx";
        for letter in ('A'..='Z').chain('a'..='z') {
            if GROUP_LETTERS.contains(letter) {
                continue;
            }
            let work = dir.join(format!("letter_{}{letter}", u32::from(letter)));
            fs::create_dir(&work).unwrap();
            let _ = gold_link(&work, &format!("-{letter}ofoo"));
            assert!(!work.join("foo").exists(), "gold -{letter}ofoo");
            let far = Command::new("cc")
                .current_dir(&work)
                .args(["-nostdlib", "-static", "-o", "far"])
                .arg(dir.join("far.o"))
                .arg(format!(
                    "-Wl,--section-start=.text=0x800000,--section-start=.far=0x200000000,-{letter}w"
                ))
                .output()
                .unwrap();
            assert!(!far.status.success(), "GNU ld -{letter}w: {far:?}");
        }
        // The one-dash long options the driver admits, from the linkers'
        // --help, read through gold as their two-dash spellings.
        let mut names = std::collections::BTreeSet::new();
        let lld = lld_dir().map(|lld| lld.join("ld.lld"));
        let helps: Vec<PathBuf> = [
            Some(PathBuf::from("ld.gold")),
            Some(PathBuf::from("ld.bfd")),
            lld,
        ]
        .into_iter()
        .flatten()
        .collect();
        for help in helps {
            let text = Command::new(&help).arg("--help").output().unwrap().stdout;
            for word in
                String::from_utf8_lossy(&text).split(|c: char| c.is_whitespace() || c == ',')
            {
                let Some(name) = word.trim_start_matches('-').split(['=', '[']).next() else {
                    continue;
                };
                if word.starts_with('-')
                    && name.len() >= 2
                    && name
                        .chars()
                        .all(|c| c.is_ascii_alphanumeric() || c == '-' || c == '_')
                    && name
                        .chars()
                        .next()
                        .is_some_and(|first| GROUP_LETTERS.contains(first))
                    && parse_wl_group(&format!("-{name}"), linux).is_ok()
                {
                    names.insert(name.to_string());
                }
            }
        }
        assert!(names.len() >= 150, "{names:?}");
        // `-dT` is admitted as GNU ld's and LLD's `--default-script`, which
        // gold reads as `-d -T`: the next piece is a linker script to each,
        // and gold writes the same bytes as with `-T` (a common symbol
        // too, which `-d` allocates as a final link does anyway).
        assert!(names.remove("dT"), "{names:?}");
        let work = dir.join("dT");
        fs::create_dir(&work).unwrap();
        fs::write(work.join("sym.ld"), "tcg_dt_marker = 42;\n").unwrap();
        let dt = gold_link(&work, "-dT,sym.ld");
        assert!(dt.status.success(), "{dt:?}");
        let with_dt = fs::read(work.join("out")).unwrap();
        assert!(gold_link(&work, "-T,sym.ld").status.success());
        assert_eq!(with_dt, fs::read(work.join("out")).unwrap());
        let compared = std::sync::Mutex::new(Vec::new());
        let names: Vec<String> = names.into_iter().collect();
        std::thread::scope(|scope| {
            for chunk in names.chunks(names.len().div_ceil(8)) {
                let (gold_link, compared, dir) = (&gold_link, &compared, dir);
                scope.spawn(move || {
                    for name in chunk {
                        let read = |dashes: &str| {
                            let work = dir.join(format!("long{dashes}{name}"));
                            fs::create_dir(&work).unwrap();
                            let run = gold_link(&work, &format!("{dashes}{name}"));
                            let mut files: Vec<String> = fs::read_dir(&work)
                                .unwrap()
                                .map(|entry| entry.unwrap().file_name().to_string_lossy().into())
                                .collect();
                            files.sort();
                            let bytes = fs::read(work.join("out")).ok();
                            let messages: Vec<String> = stderr(&run)
                                .replace(&format!("--{name}"), &format!("-{name}"))
                                .lines()
                                .filter(|line| !line.contains("time:"))
                                .map(str::to_string)
                                .collect();
                            (run.status.code(), files, bytes, messages)
                        };
                        let (one, two) = (read("-"), read("--"));
                        let unknown = one
                            .3
                            .iter()
                            .any(|line| line.ends_with(&format!("-{name}: unknown option")));
                        compared
                            .lock()
                            .unwrap()
                            .push((name.clone(), one == two || (one.0 != Some(0) && unknown)));
                    }
                });
            }
        });
        let compared = compared.into_inner().unwrap();
        let differing: Vec<&String> = compared
            .iter()
            .filter(|(_, same)| !same)
            .map(|(name, _)| name)
            .collect();
        assert!(
            differing.is_empty() && compared.len() == names.len(),
            "gold reads these admitted one-dash spellings otherwise: {differing:?}"
        );
    }

    /// An LLD shared object with `DT_RELR` and no version needs
    /// (`DT_VERNEED`) is loaded by glibc 2.39, which checks the
    /// `GLIBC_ABI_DT_RELR` dependency only for an image with version needs:
    /// the verifier's `--pack-dyn-relocs=relr` and `-z pack-relative-relocs`
    /// libraries that import nothing were refused and are installed, and a
    /// program `dlopen`s each and reads 42 through its packed relocations.
    /// One that needs `getpid` from `libc.so.6` with `--pack-dyn-relocs=relr`
    /// has no such dependency, `ld.so` refuses it, and it is refused
    /// (`[TCG-LINK-RELOCATION-FORMAT]`). glibc checks only an image that
    /// needs libc (`DT_NEEDED`): one whose version needs name only a
    /// library of the user's (`libv.so`, `VERS_1`) is installed and loads;
    /// the same with `libc.so.6` needed too is refused, as `ld.so` refuses
    /// it.
    #[test]
    fn relr_shared_objects_are_refused_only_when_glibc_refuses_them() {
        let directory = tempfile::tempdir().unwrap();
        let dir = directory.path();
        let Some(lld) = lld_dir() else {
            return;
        };
        let lld = lld_cc(dir, &lld);
        fs::write(dir.join("ret.trust_ir"), RET42_IR).unwrap();
        fs::write(
            dir.join("so.c"),
            "static int x = 42; int *p = &x; int *q = &x;\nint get(void) { return *p + *q - 42; \
             }\n",
        )
        .unwrap();
        fs::write(
            dir.join("so_libc.c"),
            "#include <unistd.h>\nstatic int x = 42; int *p = &x; int *q = &x;\nint get(void) { \
             return *p + *q - 42 + (getpid() < 0); }\n",
        )
        .unwrap();
        fs::write(
            dir.join("dl.c"),
            "#include <dlfcn.h>\n#include <stdio.h>\nint main(int argc, char **argv) { void *h = \
             dlopen(argv[1], RTLD_NOW); if (!h) { printf(\"%s\\n\", dlerror()); return 2; } int \
             (*g)(void) = (int (*)(void))dlsym(h, \"get\"); return g(); }\n",
        )
        .unwrap();
        run_tool(dir, "cc", &["-c", "-O1", "-fPIC", "-o", "so.o", "so.c"]);
        run_tool(
            dir,
            "cc",
            &["-c", "-O1", "-fPIC", "-o", "so_libc.o", "so_libc.c"],
        );
        run_tool(dir, "cc", &["-o", "dl", "dl.c"]);
        for (name, packing) in [
            ("librelr.so", "--pack-dyn-relocs=relr"),
            ("libpacked.so", "-z,pack-relative-relocs"),
        ] {
            let group = format!("-Wl,so.o,{packing}");
            let result = trust_cg_on(
                Some(&lld),
                dir,
                &[
                    "--format=text",
                    "--shared",
                    "--nostdlib",
                    "--relocation-model",
                    "pic",
                    "-o",
                    name,
                    "ret.trust_ir",
                    &group,
                ],
            );
            assert!(result.status.success(), "{name}: {}", stderr(&result));
            let dynamic = Command::new("readelf")
                .args(["-dW", name])
                .current_dir(dir)
                .output()
                .unwrap();
            let dynamic = String::from_utf8_lossy(&dynamic.stdout).into_owned();
            assert!(
                dynamic.contains("(RELR)") && !dynamic.contains("(VERNEED)"),
                "{name}: {dynamic}"
            );
            let run = Command::new(dir.join("dl"))
                .arg(dir.join(name))
                .output()
                .unwrap();
            assert_eq!(run.status.code(), Some(42), "{name}: {run:?}");
        }
        refused_with(
            dir,
            Some(&lld),
            &[
                "--format=text",
                "--shared",
                "--relocation-model",
                "pic",
                "-o",
                "libc_relr.so",
                "ret.trust_ir",
                "-Wl,so_libc.o,--pack-dyn-relocs=relr",
            ],
            "[TCG-LINK-RELOCATION-FORMAT]",
            &["GLIBC_ABI_DT_RELR"],
        );
        // Version needs of a library of the user's alone.
        fs::write(dir.join("v.c"), "int vfun(void) { return 1; }\n").unwrap();
        fs::write(dir.join("v.map"), "VERS_1 { global: vfun; local: *; };\n").unwrap();
        run_tool(
            dir,
            "cc",
            &[
                "-fPIC",
                "-shared",
                "-o",
                "libv.so",
                "v.c",
                "-Wl,--version-script=v.map",
            ],
        );
        fs::write(
            dir.join("so_v.c"),
            "int vfun(void);\nstatic int x = 42; int *p = &x; int *q = &x;\nint get(void) { \
             return *p + *q - 42 + vfun() - 1; }\n",
        )
        .unwrap();
        run_tool(dir, "cc", &["-c", "-O1", "-fPIC", "-o", "so_v.o", "so_v.c"]);
        let result = trust_cg_on(
            Some(&lld),
            dir,
            &[
                "--format=text",
                "--shared",
                "--nostdlib",
                "--relocation-model",
                "pic",
                "-o",
                "libuses_v.so",
                "ret.trust_ir",
                "-Wl,so_v.o,--pack-dyn-relocs=relr,-L.,-lv",
            ],
        );
        assert!(result.status.success(), "{}", stderr(&result));
        let run = Command::new(dir.join("dl"))
            .arg(dir.join("libuses_v.so"))
            .env("LD_LIBRARY_PATH", dir)
            .output()
            .unwrap();
        assert_eq!(run.status.code(), Some(42), "{run:?}");
        refused_with(
            dir,
            Some(&lld),
            &[
                "--format=text",
                "--shared",
                "--nostdlib",
                "--relocation-model",
                "pic",
                "-o",
                "libuses_v_c.so",
                "ret.trust_ir",
                "-Wl,so_v.o,--pack-dyn-relocs=relr,--no-as-needed,-L.,-lv,-lc",
            ],
            "[TCG-LINK-RELOCATION-FORMAT]",
            &["GLIBC_ABI_DT_RELR"],
        );
    }

    /// A `-fno-pic` program that stores 9 in a shared library's variable
    /// and returns it times 10 plus what the library reads back (99 when
    /// both see one word).
    const COPY_MAIN: &str = "extern int dv; int lib_getd(void);\nextern long \
        tcg_ret42(void);\nint main(void) { dv = 9; return (int)(dv * 10 + lib_getd()) + \
        (int)tcg_ret42() - 42; }\n";

    /// The second verifier of the tenth closure audit's repair, and the
    /// scan of every flag against links whose refusal or value trust-cg's
    /// code relies on:
    /// - gold's `-z nocopyreloc` resolves a `--no-pie` program's
    ///   position-dependent reference to a library's variable to 0 (outside
    ///   the driver the program dies with SIGSEGV); it is refused by name
    ///   through each linker (`[TCG-LINK-COPY-RELOCATION]`), and the plain
    ///   program runs (99);
    /// - LLD's `--ignore-data-address-equality` makes a copy relocation of a
    ///   library's protected variable (97 outside the driver) and
    ///   `--ignore-function-address-equality` a non-canonical address for a
    ///   protected function (the addresses differ); each is refused by name;
    /// - gold and LLD read `-export-dyn` as `-e xport-dyn` and write
    ///   `e_entry` 0: the dynamic programs are refused
    ///   (`[TCG-LINK-ENTRY-POINT]`), and GNU ld's, which reads it as
    ///   `--export-dynamic`, runs;
    /// - LLD's `--unique` and an unclosed `--start-lib` split or drop the C
    ///   runtime's `.init` (SIGILL outside the driver); both are refused
    ///   (`[TCG-LINK-C-RUNTIME-LAYOUT]`), and a closed `--start-lib` runs.
    #[test]
    fn options_that_let_a_relied_on_refusal_or_the_entry_go_are_refused() {
        let directory = tempfile::tempdir().unwrap();
        let dir = directory.path();
        fs::write(dir.join("ret42.trust_ir"), RET42_IR).unwrap();
        fs::write(
            dir.join("dflt_lib.c"),
            "int dv = 7;\nint lib_getd(void) { return dv; }\n",
        )
        .unwrap();
        fs::write(
            dir.join("prot_lib.c"),
            "__attribute__((visibility(\"protected\"))) int dv = 7;\nint lib_getd(void) { \
             return dv; }\n",
        )
        .unwrap();
        fs::write(
            dir.join("protfn_lib.c"),
            "__attribute__((visibility(\"protected\"))) int pf(void) { return 7; }\nvoid \
             *lib_pf(void) { return (void *)pf; }\n",
        )
        .unwrap();
        fs::write(dir.join("copy_main.c"), COPY_MAIN).unwrap();
        fs::write(
            dir.join("plain_main.c"),
            "extern long tcg_ret42(void);\nint main(void) { return (int)tcg_ret42(); }\n",
        )
        .unwrap();
        fs::write(
            dir.join("protfn_main.c"),
            "int pf(void); void *lib_pf(void);\nextern long tcg_ret42(void);\nint main(void) \
             { return (void *)pf == lib_pf() ? (int)tcg_ret42() : 1; }\n",
        )
        .unwrap();
        for (library, source) in [
            ("libdflt.so", "dflt_lib.c"),
            ("libprot.so", "prot_lib.c"),
            ("libprotfn.so", "protfn_lib.c"),
        ] {
            run_tool(
                dir,
                "cc",
                &["-O1", "-fPIC", "-shared", "-o", library, source],
            );
        }
        for (object, source) in [
            ("copy_main.o", "copy_main.c"),
            ("plain_main.o", "plain_main.c"),
        ] {
            run_tool(dir, "cc", &["-c", "-O1", "-fno-pic", "-o", object, source]);
        }
        run_tool(
            dir,
            "cc",
            &[
                "-c",
                "-O1",
                "-fno-pic",
                "-o",
                "protfn_main.o",
                "protfn_main.c",
            ],
        );
        let object = trust_cg_on(
            None,
            dir,
            &["--format=text", "-c", "-o", "ret42.o", "ret42.trust_ir"],
        );
        assert!(object.status.success(), "{}", stderr(&object));
        fn strs(args: &[String]) -> Vec<&str> {
            args.iter().map(String::as_str).collect()
        }
        let rpath = dir.display().to_string();
        let cli = |name: &str, group: &str, extra: &[&str]| {
            let mut args = vec![
                "--format=text",
                "-o",
                name,
                "ret42.trust_ir",
                "--rpath",
                rpath.as_str(),
                group,
            ];
            args.extend(extra);
            args.iter().map(|arg| arg.to_string()).collect::<Vec<_>>()
        };
        let raw = |cc: &str, args: &[&str]| {
            Command::new(cc)
                .current_dir(dir)
                .args(args)
                .arg(format!("-Wl,-rpath,{rpath}"))
                .output()
                .unwrap()
        };
        for (linker, bin) in linkers(dir) {
            let bin = bin.as_deref();
            let cc = bin.map_or_else(
                || "cc".to_string(),
                |bin| bin.join("cc").display().to_string(),
            );
            // -z nocopyreloc.
            let args = cli(
                &format!("ncr_{linker}"),
                "-Wl,copy_main.o,-L.,-ldflt,-z,nocopyreloc",
                &["--no-pie"],
            );
            refused_with(
                dir,
                bin,
                &strs(&args),
                "[TCG-LINK-COPY-RELOCATION]",
                &["-z nocopyreloc"],
            );
            let plain = cli(
                &format!("copy_{linker}"),
                "-Wl,copy_main.o,-L.,-ldflt",
                &["--no-pie"],
            );
            assert_eq!(
                installed_and_run(dir, bin, &strs(&plain)).0,
                Some(99),
                "{linker}"
            );
            // -export-dyn.
            let args = cli(
                &format!("xdyn_{linker}"),
                "-Wl,plain_main.o,-export-dyn",
                &[],
            );
            if linker == "gnu" {
                assert_eq!(installed_and_run(dir, bin, &strs(&args)).0, Some(42));
            } else {
                let raw_run = raw(
                    &cc,
                    &[
                        "-o",
                        "xdyn_raw",
                        "plain_main.o",
                        "ret42.o",
                        "-Wl,-export-dyn",
                    ],
                );
                assert!(raw_run.status.success(), "{linker}: {raw_run:?}");
                let status = Command::new(dir.join("xdyn_raw")).status().unwrap();
                assert!(status.signal().is_some(), "{linker}: {status:?}");
                refused_with(
                    dir,
                    bin,
                    &strs(&args),
                    "[TCG-LINK-ENTRY-POINT]",
                    &["its entry point (e_entry) is 0"],
                );
            }
            if linker == "gold" {
                let ncr = raw(
                    &cc,
                    &[
                        "-no-pie",
                        "-o",
                        "ncr_raw",
                        "copy_main.o",
                        "ret42.o",
                        "-L.",
                        "-ldflt",
                        "-Wl,-z,nocopyreloc",
                    ],
                );
                assert!(ncr.status.success(), "{ncr:?}");
                let status = Command::new(dir.join("ncr_raw")).status().unwrap();
                assert_eq!(status.signal(), Some(SIGSEGV), "{status:?}");
            }
            if linker != "lld" {
                continue;
            }
            // LLD's address-equality options, outside and through the driver.
            let prot = raw(
                &cc,
                &[
                    "-no-pie",
                    "-o",
                    "prot_raw",
                    "copy_main.o",
                    "ret42.o",
                    "-L.",
                    "-lprot",
                    "-Wl,--ignore-data-address-equality",
                ],
            );
            assert!(prot.status.success(), "{prot:?}");
            assert_eq!(run_program(&dir.join("prot_raw")).0, Some(97));
            let protfn = raw(
                &cc,
                &[
                    "-no-pie",
                    "-o",
                    "protfn_raw",
                    "protfn_main.o",
                    "ret42.o",
                    "-L.",
                    "-lprotfn",
                    "-Wl,--ignore-function-address-equality",
                ],
            );
            assert!(protfn.status.success(), "{protfn:?}");
            assert_eq!(run_program(&dir.join("protfn_raw")).0, Some(1));
            for (name, group) in [
                (
                    "prot_ide",
                    "-Wl,copy_main.o,-L.,-lprot,--ignore-data-address-equality",
                ),
                (
                    "protfn_ife",
                    "-Wl,protfn_main.o,-L.,-lprotfn,--ignore-function-address-equality",
                ),
            ] {
                refused_with(
                    dir,
                    bin,
                    &strs(&cli(name, group, &["--no-pie"])),
                    "[TCG-LINK-COPY-RELOCATION]",
                    &[],
                );
            }
            // The C runtime's `.init`.
            let unique = raw(
                &cc,
                &[
                    "-o",
                    "unique_raw",
                    "plain_main.o",
                    "ret42.o",
                    "-Wl,--unique",
                ],
            );
            assert!(unique.status.success(), "{unique:?}");
            assert_eq!(
                Command::new(dir.join("unique_raw"))
                    .status()
                    .unwrap()
                    .signal(),
                Some(4)
            );
            for (name, group) in [
                ("unique", "-Wl,plain_main.o,--unique"),
                ("start_lib", "-Wl,--start-lib,plain_main.o"),
            ] {
                refused_with(
                    dir,
                    bin,
                    &strs(&cli(name, group, &[])),
                    "[TCG-LINK-C-RUNTIME-LAYOUT]",
                    &[],
                );
            }
            let closed = cli(
                "start_lib_closed",
                "-Wl,--start-lib,copy_main.o,--end-lib,-L.,-ldflt",
                &["--no-pie"],
            );
            assert_eq!(installed_and_run(dir, bin, &strs(&closed)).0, Some(99));
        }
    }

    /// GCC `-flto` objects (slim and fat): the tenth closure audit found them
    /// refused in GNU ld's default PIE link and in every GNU ld and gold
    /// static link, because the trace named the objects GCC's LTO plugin
    /// compiled and deleted. Each now links again with the plugin keeping
    /// them in the stage, is installed and runs, and no LTO object is left
    /// in the output's directory or the system temporary directory's
    /// entries the link made.
    #[test]
    fn lto_objects_link_through_gnu_ld_and_gold() {
        let directory = tempfile::tempdir().unwrap();
        let dir = directory.path();
        fs::write(dir.join("ret42.trust_ir"), RET42_IR).unwrap();
        fs::write(dir.join("main_ifunc.c"), IFUNC_MAIN).unwrap();
        run_tool(
            dir,
            "cc",
            &["-c", "-O2", "-flto", "-o", "slim.o", "main_ifunc.c"],
        );
        run_tool(
            dir,
            "cc",
            &[
                "-c",
                "-O2",
                "-flto",
                "-ffat-lto-objects",
                "-o",
                "fat.o",
                "main_ifunc.c",
            ],
        );
        for (linker, bin) in linkers(dir) {
            if linker == "lld" {
                // LLD reads no GCC LTO IR.
                continue;
            }
            let bin = bin.as_deref();
            for object in ["slim.o", "fat.o"] {
                for mode in ["", "--static", "--no-pie"] {
                    let name = format!("lto_{linker}_{}{}", &object[..1], mode.len());
                    let group = format!("-Wl,{object}");
                    let mut args = vec!["--format=text", "-o", &name, "ret42.trust_ir", &group];
                    if !mode.is_empty() {
                        args.push(mode);
                    }
                    assert_eq!(installed_and_run(dir, bin, &args).0, Some(42), "{name}");
                }
            }
        }
        assert!(
            !fs::read_dir(dir).unwrap().any(|entry| entry
                .unwrap()
                .file_name()
                .to_string_lossy()
                .contains("ltrans")),
            "an LTO object was left in the output's directory"
        );
    }

    /// The L02-P2 audit's library (2026-10-24): default-visibility data
    /// `rp_data` (1111) with its reader and address, and the function
    /// `rp_fn` (7) with its address.
    const RPD: &str = r#"module "rpd"
functy.0 = () -> (u64)
functy.1 = () -> (ptr)
functy.2 = () -> (functy.0)
global mut align(8) @rp_data u64 = 1111
fn @rp_read_data(functy.0) {
bb0:
    %0 = global_addr @global.0
    %1 = load u64, ptr %0
    ret %1
}
fn @rp_addr_data(functy.1) {
bb0:
    %0 = global_addr @global.0
    ret %0
}
fn @rp_fn(functy.0) {
bb0:
    %0 = const u64 7
    ret %0
}
fn @rp_addr_fn(functy.2) {
bb0:
    %0 = const functy.0 fndef<func.2>
    ret %0
}
"#;

    /// A non-PIE executable that writes `rp_data` through its copy
    /// relocation and checks the library sees that one copy, and that its
    /// `rp_fn` is the library's `rp_addr_fn()` (the audit's `copyuser.c`).
    const RPD_COPY_USER: &str = "#include <stdint.h>\n#include <stdio.h>\nextern uint64_t \
        rp_data;\nextern uint64_t rp_read_data(void);\nextern uint64_t *rp_addr_data(void);\n\
        extern uint64_t rp_fn(void);\nextern void *rp_addr_fn(void);\nint main(void) {\n  int \
        bad = 0;\n  rp_data = 99;\n  if (rp_addr_data() != &rp_data) bad |= 1;\n  if \
        (rp_read_data() != 99) bad |= 2;\n  if ((void *)&rp_fn != rp_addr_fn()) bad |= 4;\n  \
        printf(\"bad=%d\\n\", bad);\n  return bad;\n}\n";

    /// L02-P2 (2026-10-24 closure audit): a `--shared` link without a
    /// relocation model compiles `pic` (OD-SHARED-PIC-DEFAULT-20261024), and
    /// the library it installs through GNU ld, gold and LLD keeps one
    /// `rp_data` and one `rp_fn` with a copy-relocating non-PIE executable
    /// (linked by GNU ld). An explicit `static` or `pie` model is kept,
    /// and its direct addresses of `rp_data` and `rp_fn` are refused by name
    /// before the linker runs, on every linker
    /// (`[TCG-LINK-PREEMPTIBLE-DIRECT]`), with nothing written: before the
    /// repair gold installed that library, which read its own 1111 after the
    /// executable wrote 99 (exit 7), while GNU ld and LLD refused it
    /// themselves.
    #[test]
    fn shared_links_compile_pic_and_refuse_direct_addresses_of_preemptible_symbols() {
        let directory = tempfile::tempdir().unwrap();
        let dir = directory.path();
        fs::write(dir.join("rpd.trust_ir"), RPD).unwrap();
        fs::write(dir.join("copyuser.c"), RPD_COPY_USER).unwrap();
        for (linker, bin) in linkers(dir) {
            let bin = bin.as_deref();
            let library = format!("librpd_{linker}.so");
            let output = trust_cg_on(
                bin,
                dir,
                &["--format=text", "--shared", "-o", &library, "rpd.trust_ir"],
            );
            assert!(output.status.success(), "{linker}: {}", stderr(&output));
            // The executable is linked by GNU ld whatever linked the
            // library: gold 2.42 gives a non-PIE executable no canonical
            // address for a function a shared library defines (LIMITATIONS),
            // so its `&rp_fn` and the library's would differ whatever either
            // object does.
            let program = format!("copyuser_{linker}");
            run_tool(
                dir,
                "cc",
                &[
                    "-fno-pic",
                    "-no-pie",
                    "-o",
                    &program,
                    "copyuser.c",
                    &library,
                    &format!("-Wl,-rpath,{}", dir.display()),
                ],
            );
            let (code, stdout) = run_program(&dir.join(&program));
            assert_eq!((code, stdout.trim()), (Some(0), "bad=0"), "{linker}");

            for model in ["static", "pie"] {
                let name = format!("librpd_{linker}_{model}.so");
                refused_with(
                    dir,
                    bin,
                    &[
                        "--format=text",
                        "--shared",
                        "--relocation-model",
                        model,
                        "-o",
                        &name,
                        "rpd.trust_ir",
                    ],
                    "[TCG-LINK-PREEMPTIBLE-DIRECT]",
                    &[
                        "error[link:non-pic-relocation] `rp_data` (R_AARCH64_ADR_PREL_PG_HI21)",
                        "error[link:non-pic-relocation] `rp_fn` (R_AARCH64_ADR_PREL_PG_HI21)",
                        "error[link:non-pic-definition] `rp_data`: [TCG-LINK-PREEMPTIBLE-DEFINITION]",
                        "error[link:non-pic-definition] `rp_fn`: [TCG-LINK-PREEMPTIBLE-DEFINITION]",
                        "link inputs refused before the linker ran",
                    ],
                );
            }
        }
    }

    /// The L02-P2 round-2 verifier's library (2026-10-24): a hidden datum
    /// `cp_hidden` (3), a default-visibility `rp_fn` (7) and a
    /// default-visibility `cp_call` returning `rp_fn() + cp_hidden`.
    const CALLPRE: &str = r#"module "callpre"
functy.0 = () -> (u64)
global mut visibility(hidden) @cp_hidden u64 = 3
fn @rp_fn(functy.0) {
bb0:
    %0 = const u64 7
    ret %0
}
fn @cp_call(functy.0) {
bb0:
    %0 = call @func.0()
    %1 = global_addr @global.0
    %2 = load u64, ptr %1
    %3 = add u64 %0, %2
    ret %3
}
"#;

    /// [`CALLPRE`] with both functions `protected`: the library's own calls
    /// bind to its own definitions whatever another object defines.
    const CALLPROT: &str = r#"module "callprot"
functy.0 = () -> (u64)
global mut visibility(hidden) @cp_hidden u64 = 3
fn @rp_fn(functy.0) {
    ; #visibility: protected
bb0:
    %0 = const u64 7
    ret %0
}
fn @cp_call(functy.0) {
    ; #visibility: protected
bb0:
    %0 = call @func.0()
    %1 = global_addr @global.0
    %2 = load u64, ptr %1
    %3 = add u64 %0, %2
    ret %3
}
"#;

    /// Prints `cp_call()` and exits 0 when it is `CP_WANT`.
    const CALLPRE_MAIN: &str = "#include <stdint.h>\n#include <stdio.h>\n#include <stdlib.h>\n\
        extern uint64_t cp_call(void);\nint main(void) {\n  uint64_t got = cp_call();\n  \
        uint64_t want = strtoull(getenv(\"CP_WANT\"), 0, 10);\n  printf(\"cp_call=%llu\\n\", \
        (unsigned long long)got);\n  return got == want ? 0 : 1;\n}\n";

    /// An `LD_PRELOAD` interposer of `rp_fn`, returning 77.
    const RP_FN_INTERPOSER: &str = "#include <stdint.h>\nuint64_t rp_fn(void) { return 77; }\n";

    /// L02-P2 round 2 (2026-10-24, ruling
    /// OD-SHARED-NON-PIC-DEFINITION-20261024): under an explicit `static` or
    /// `pie` model the module inliner treats `rp_fn` as non-preemptible and
    /// splices it into `cp_call`, leaving no relocation for
    /// `[TCG-LINK-PREEMPTIBLE-DIRECT]` to refuse; GNU ld, gold and LLD all
    /// installed that library, and an `LD_PRELOAD` interposer of `rp_fn`
    /// (77) was ignored by `cp_call` (10 where 80 is expected, O1 to O3).
    /// Now every such `--shared` link is refused by name before the linker
    /// runs, at O0 and O2, on every linker, naming the two default-visibility
    /// definitions and not the hidden datum, and nothing is written. Positive
    /// twins on every linker: without a model (`pic`) and with an explicit
    /// `pic` the library installs and `cp_call` reaches the interposer (80;
    /// 10 without it), and the `protected` twin [`CALLPROT`] installs under
    /// `static` and `pie`, where its own call keeps its own `rp_fn` (10 with
    /// or without the interposer, as `protected` means).
    #[test]
    fn shared_links_of_static_or_pie_modules_refuse_default_visibility_definitions() {
        let directory = tempfile::tempdir().unwrap();
        let dir = directory.path();
        fs::write(dir.join("callpre.trust_ir"), CALLPRE).unwrap();
        fs::write(dir.join("callprot.trust_ir"), CALLPROT).unwrap();
        fs::write(dir.join("cp_main.c"), CALLPRE_MAIN).unwrap();
        fs::write(dir.join("ip.c"), RP_FN_INTERPOSER).unwrap();
        run_tool(
            dir,
            "cc",
            &["-O2", "-fPIC", "-shared", "-o", "libip.so", "ip.c"],
        );
        let interposer = dir.join("libip.so");
        // Link `cp_main.c` against `library` and return what it prints
        // without and with the interposer, each checked against its wanted
        // value.
        let run_against = |library: &str, plain: u64, preloaded: u64| {
            let program = format!("{library}.main");
            run_tool(
                dir,
                "cc",
                &[
                    "-O0",
                    "-o",
                    &program,
                    "cp_main.c",
                    library,
                    &format!("-Wl,-rpath,{}", dir.display()),
                ],
            );
            for (preload, want) in [(false, plain), (true, preloaded)] {
                let mut command = Command::new(dir.join(&program));
                command.env("CP_WANT", want.to_string());
                if preload {
                    command.env("LD_PRELOAD", &interposer);
                }
                let output = command.output().unwrap();
                assert_eq!(
                    (
                        output.status.code(),
                        String::from_utf8_lossy(&output.stdout).trim()
                    ),
                    (Some(0), format!("cp_call={want}").as_str()),
                    "{library} preload={preload}"
                );
            }
        };
        for (linker, bin) in linkers(dir) {
            let bin = bin.as_deref();
            for model in ["static", "pie"] {
                for opt in ["-O0", "-O2"] {
                    let name = format!("libcp_{linker}_{model}{opt}.so");
                    let before = listing(dir);
                    let result = trust_cg_on(
                        bin,
                        dir,
                        &[
                            "--format=text",
                            "--shared",
                            "--relocation-model",
                            model,
                            opt,
                            "-o",
                            &name,
                            "callpre.trust_ir",
                        ],
                    );
                    let text = stderr(&result);
                    let what = format!("{linker} {model} {opt}");
                    assert!(!result.status.success(), "{what}: {text}");
                    for definition in ["rp_fn", "cp_call"] {
                        assert!(
                            text.contains(&format!(
                                "trust-cg: error[link:non-pic-definition] `{definition}`: \
                                 [TCG-LINK-PREEMPTIBLE-DEFINITION] "
                            )),
                            "{what} {definition}: {text}"
                        );
                    }
                    assert!(!text.contains("`cp_hidden`"), "{what}: {text}");
                    assert!(
                        text.contains("link inputs refused before the linker ran")
                            && !text.contains("ld returned")
                            && !text.contains("recompile with -fPIC"),
                        "{what}: {text}"
                    );
                    assert_eq!(listing(dir), before, "{what}");
                }
            }
            for model in [None, Some("pic")] {
                let name = format!("libcp_{linker}_{}.so", model.unwrap_or("default"));
                let mut args = vec!["--format=text", "--shared", "-O2", "-o", name.as_str()];
                if let Some(model) = model {
                    args.extend(["--relocation-model", model]);
                }
                args.push("callpre.trust_ir");
                let result = trust_cg_on(bin, dir, &args);
                assert!(result.status.success(), "{name}: {}", stderr(&result));
                run_against(&name, 10, 80);
            }
            for model in ["static", "pie"] {
                let name = format!("libcpprot_{linker}_{model}.so");
                let result = trust_cg_on(
                    bin,
                    dir,
                    &[
                        "--format=text",
                        "--shared",
                        "--relocation-model",
                        model,
                        "-O2",
                        "-o",
                        &name,
                        "callprot.trust_ir",
                    ],
                );
                assert!(result.status.success(), "{name}: {}", stderr(&result));
                run_against(&name, 10, 10);
            }
        }
    }
}

/// Writes an executable script from a child shell. A script this process
/// opened for writing can fail to exec with ETXTBSY ("Text file busy"): a
/// test thread that forks while the write descriptor is open hands a copy to
/// its child, which holds it until that child execs. Writing through a child
/// process leaves no writable descriptor to the script in this process.
#[cfg(all(target_arch = "aarch64", target_os = "linux", target_env = "gnu"))]
fn write_executable_script(path: &std::path::Path, contents: &str) {
    use std::io::Write;
    let mut child = std::process::Command::new("/bin/sh")
        .arg("-c")
        .arg("cat > \"$1\" && chmod 755 \"$1\"")
        .arg("sh")
        .arg(path)
        .stdin(std::process::Stdio::piped())
        .spawn()
        .expect("spawn /bin/sh to write the script");
    child
        .stdin
        .take()
        .expect("script writer stdin")
        .write_all(contents.as_bytes())
        .expect("write the script");
    assert!(
        child.wait().expect("wait for the script writer").success(),
        "writing {}",
        path.display()
    );
}
