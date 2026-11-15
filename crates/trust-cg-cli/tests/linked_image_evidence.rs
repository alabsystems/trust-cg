// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! L02-P5: `trust-cg --linked-image-evidence` writes the linked-image
//! evidence record next to an aarch64-apple-darwin executable or dylib, and
//! removes the output when the replay disagrees (including an image with
//! content from a `-Wl` object, an unused dylib or the flat namespace). No
//! record outlives the image it describes.
//!
//! The refusals run on every host. The links run the host C driver (ld64)
//! and the programs natively, so they run on AArch64 macOS only.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

use trust_cg_codegen::pipeline::encode_tmbc;
use trust_ir::value::GlobalId;
use trust_ir::{Constant, Global, ICmpOp, Linkage, Module, Ty, Visibility};
use trust_ir_build::ModuleBuilder;

fn trust_cg(directory: &Path, args: &[&str]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_trust-cg"))
        .arg("--permit-unlicensed") // Claim-less fixtures: refused by default since WS7.5 (DG-73).
        .current_dir(directory)
        .args(args)
        .output()
        .expect("run trust-cg")
}

fn stderr(output: &Output) -> String {
    String::from_utf8_lossy(&output.stderr).into_owned()
}

fn write_module(directory: &Path, name: &str, module: &Module) -> PathBuf {
    let path = directory.join(name);
    fs::write(&path, encode_tmbc(module).unwrap()).unwrap();
    path
}

fn global(name: &str, ty: Ty, mutable: bool, init: Constant) -> Global {
    Global {
        name: name.into(),
        ty,
        mutable,
        initializer: Some(init),
        linkage: Linkage::External,
        tls: None,
        align: Some(8),
        section: None,
        visibility: Visibility::Default,
        retained: false,
    }
}

/// `main` calls `tcg_leaf` (5) through a relocated constant table
/// (`__DATA,__const`), reads `tcg_data` (37) and calls libSystem's `labs`
/// (0): it exits 42 when every relocation resolved.
fn program() -> Module {
    // `labs` is a bodyless declaration: an FFI boundary trust-ir refuses
    // without a pinned target (`TargetInfoRequired`; WS7.3 ingestion
    // admission). The image is an aarch64-apple-darwin executable.
    let mut mb = ModuleBuilder::new_with_target_info(
        "tcg_linked_image",
        trust_ir::TargetInfo {
            triple: "aarch64-apple-darwin".into(),
            pointer_size: 8,
            endianness: trust_ir::Endianness::Little,
            abi: None,
            struct_passing: trust_ir::StructPassingPolicy::NativeC,
        },
    );
    let nullary = mb.add_func_type(vec![], vec![Ty::I64]);
    let unary = mb.add_func_type(vec![Ty::I64], vec![Ty::I64]);
    let main_ty = mb.add_func_type(vec![], vec![Ty::I32]);
    let ptr = mb.add_type(Ty::Ptr);
    mb.add_global(global("tcg_data", Ty::I64, true, Constant::Int(37)));
    mb.add_global(global(
        "tcg_table",
        Ty::Array(ptr, 1),
        false,
        Constant::Aggregate(vec![Constant::SymbolAddr {
            symbol: "tcg_leaf".into(),
            addend: 0,
        }]),
    ));
    let mut fb = mb.function("tcg_leaf", nullary);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let five = fb.iconst(Ty::I64, 5);
    fb.ret(vec![five]);
    fb.build();
    let labs = mb.declare_function("labs", unary);
    let mut fb = mb.function("main", main_ty);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let table = fb.global_addr(GlobalId::new(1));
    let leaf = fb.load(Ty::Ptr, table);
    let a = fb.call_indirect(leaf, nullary, vec![]);
    let data = fb.global_addr(GlobalId::new(0));
    let b = fb.load(Ty::I64, data);
    let zero = fb.iconst(Ty::I64, 0);
    let c = fb.call(labs, vec![zero]);
    let ab = fb.add(Ty::I64, a, b);
    let sum = fb.add(Ty::I64, ab, c);
    let want = fb.iconst(Ty::I64, 42);
    let ok = fb.icmp(ICmpOp::Eq, Ty::I64, sum, want);
    let pass = fb.iconst(Ty::I32, 42);
    let fail = fb.iconst(Ty::I32, 1);
    let status = fb.select(Ty::I32, ok, pass, fail);
    fb.ret(vec![status]);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

#[test]
fn linked_image_evidence_is_refused_without_a_darwin_arm64_link() {
    let directory = tempfile::tempdir().unwrap();
    let dir = directory.path();
    write_module(dir, "a.tmbc", &program());
    let output = trust_cg(dir, &["-c", "--linked-image-evidence", "a.tmbc"]);
    assert!(!output.status.success());
    assert!(
        stderr(&output).contains("--linked-image-evidence: -c compiles objects only"),
        "{}",
        stderr(&output)
    );
    assert!(!dir.join("a.o").exists());

    let output = trust_cg(
        dir,
        &[
            "--target",
            "aarch64-unknown-linux-gnu",
            "--linked-image-evidence",
            "-o",
            "prog",
            "a.tmbc",
        ],
    );
    assert!(!output.status.success());
    assert!(
        stderr(&output).contains(
            "--linked-image-evidence: only aarch64-apple-darwin Mach-O images are replayed"
        ),
        "{}",
        stderr(&output)
    );
    assert!(!dir.join("prog").exists());
}

#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
mod native {
    use super::*;

    fn record(path: &Path) -> serde_json::Value {
        serde_json::from_str(&fs::read_to_string(path).unwrap()).unwrap()
    }

    #[test]
    fn executables_and_dylibs_get_a_record_next_to_the_output() {
        let directory = tempfile::tempdir().unwrap();
        let dir = directory.path();
        write_module(dir, "a.tmbc", &program());
        let output = trust_cg(
            dir,
            &[
                "--target",
                "aarch64-apple-darwin",
                "-O2",
                "-o",
                "prog",
                "--linked-image-evidence",
                "a.tmbc",
            ],
        );
        assert!(output.status.success(), "{}", stderr(&output));
        assert!(stderr(&output).contains("linked-image evidence record -> prog.linked-image.json"));
        let json = record(&dir.join("prog.linked-image.json"));
        assert_eq!(json["schema"], "trust-cg.macho-linked-image/v1");
        assert_eq!(json["image"]["filetype"], "MH_EXECUTE");
        assert_eq!(
            json["image"]["size"].as_u64().unwrap(),
            fs::metadata(dir.join("prog")).unwrap().len()
        );
        let imports = json["imports"].as_array().unwrap();
        assert!(
            imports.iter().any(|import| import["symbol"] == "_labs"
                && import["library"] == "/usr/lib/libSystem.B.dylib"
                && import["provider"]
                    .as_str()
                    .unwrap()
                    .contains("libSystem.B.tbd")),
            "{imports:?}"
        );
        let relocations = json["relocations"].as_array().unwrap();
        assert!(
            relocations
                .iter()
                .any(|row| row["kind"] == "ARM64_RELOC_UNSIGNED"
                    && row["section"] == "__DATA,__const"
                    && row["resolution"].as_str().unwrap().starts_with("rebase")),
            "{relocations:?}"
        );
        assert!(json["linker"]["declared"].as_str().unwrap().contains("ld"));
        let status = Command::new(dir.join("prog")).status().unwrap();
        assert_eq!(status.code(), Some(42));

        let output = trust_cg(
            dir,
            &[
                "--target",
                "aarch64-apple-darwin",
                "--shared",
                "--soname",
                "@rpath/libtcg.dylib",
                "-o",
                "libtcg.dylib",
                "--linked-image-evidence",
                "a.tmbc",
            ],
        );
        assert!(output.status.success(), "{}", stderr(&output));
        let json = record(&dir.join("libtcg.dylib.linked-image.json"));
        assert_eq!(json["image"]["filetype"], "MH_DYLIB");
        assert_eq!(json["image"]["install_name"], "@rpath/libtcg.dylib");
    }

    /// ld64 links `-no_data_const` without a diagnostic; the replay refuses
    /// the relocated table left in writable `__DATA`, and the output goes.
    #[test]
    fn a_replay_disagreement_removes_the_output() {
        let directory = tempfile::tempdir().unwrap();
        let dir = directory.path();
        write_module(dir, "a.tmbc", &program());
        let output = trust_cg(
            dir,
            &[
                "--target",
                "aarch64-apple-darwin",
                "-o",
                "prog",
                "--linked-image-evidence",
                "-Wl,-no_data_const",
                "a.tmbc",
            ],
        );
        assert!(!output.status.success());
        let text = stderr(&output);
        assert!(text.contains("error[link:image-evidence]"), "{text}");
        assert!(text.contains("[TCG-IMAGE-CONST-WRITABLE]"), "{text}");
        assert!(text.contains("the linked output was removed"), "{text}");
        assert!(!dir.join("prog").exists());
        assert!(!dir.join("prog.linked-image.json").exists());
    }

    fn darwin_link(dir: &Path, extra: &[&str]) -> Output {
        let mut args = vec!["--target", "aarch64-apple-darwin", "-o", "prog"];
        args.extend_from_slice(extra);
        args.push("a.tmbc");
        trust_cg(dir, &args)
    }

    /// A record never outlives the image it describes: a refused
    /// `--linked-image-evidence` relink and a later relink without the flag
    /// both leave no record next to the output.
    #[test]
    fn a_stale_record_never_sits_next_to_another_image() {
        let directory = tempfile::tempdir().unwrap();
        let dir = directory.path();
        write_module(dir, "a.tmbc", &program());
        let record_path = dir.join("prog.linked-image.json");
        let recorded = darwin_link(dir, &["--linked-image-evidence"]);
        assert!(recorded.status.success(), "{}", stderr(&recorded));
        assert!(dir.join("prog").exists() && record_path.exists());

        let refused = darwin_link(dir, &["--linked-image-evidence", "-Wl,-no_data_const"]);
        assert!(!refused.status.success());
        assert!(
            stderr(&refused).contains("[TCG-IMAGE-CONST-WRITABLE]"),
            "{}",
            stderr(&refused)
        );
        assert!(!dir.join("prog").exists());
        assert!(
            !record_path.exists(),
            "the earlier record went with the refusal"
        );

        let recorded = darwin_link(dir, &["--linked-image-evidence"]);
        assert!(recorded.status.success(), "{}", stderr(&recorded));
        assert!(record_path.exists());
        let plain = darwin_link(dir, &[]);
        assert!(plain.status.success(), "{}", stderr(&plain));
        assert!(dir.join("prog").exists());
        assert!(
            !record_path.exists(),
            "a relink without the flag removes the record of the image it replaced"
        );
    }

    /// Links the record cannot bind to the CG objects are refused and the
    /// output removed: code and data from an object passed through `-Wl`,
    /// a dependent dylib no bind uses, and the flat namespace.
    #[test]
    fn unnamed_inputs_unused_dylibs_and_the_flat_namespace_are_refused() {
        let directory = tempfile::tempdir().unwrap();
        let dir = directory.path();
        write_module(dir, "a.tmbc", &program());
        let source = dir.join("foreign.c");
        fs::write(
            &source,
            "__attribute__((visibility(\"hidden\"))) long foreign_counter = 3;\n\
             __attribute__((visibility(\"hidden\"))) long *foreign_ptr = &foreign_counter;\n\
             __attribute__((visibility(\"hidden\"))) long foreign_fn(long x) { return x + *foreign_ptr; }\n",
        )
        .unwrap();
        let foreign = dir.join("foreign.o");
        let compiled = Command::new("/usr/bin/clang")
            .args(["-arch", "arm64", "-O0", "-c"])
            .arg(&source)
            .arg("-o")
            .arg(&foreign)
            .output()
            .unwrap();
        assert!(compiled.status.success(), "{}", stderr(&compiled));
        let passthrough = format!("-Wl,{}", foreign.display());
        for (extra, code) in [
            (passthrough.as_str(), "[TCG-IMAGE-UNACCOUNTED-CONTENT]"),
            ("-Wl,-needed-lz", "[TCG-IMAGE-UNUSED-DYLIB]"),
            ("-Wl,-flat_namespace", "[TCG-IMAGE-UNSUPPORTED]"),
        ] {
            let output = darwin_link(dir, &["--linked-image-evidence", extra]);
            let text = stderr(&output);
            assert!(!output.status.success(), "{extra}: {text}");
            assert!(text.contains(code), "{extra}: {text}");
            assert!(
                text.contains("the linked output was removed"),
                "{extra}: {text}"
            );
            assert!(!dir.join("prog").exists(), "{extra}");
            assert!(!dir.join("prog.linked-image.json").exists(), "{extra}");
        }
    }
}
