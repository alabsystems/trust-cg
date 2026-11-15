// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Output planning must reject aliases before writing any requested artifact.

use std::fs;
use std::path::Path;
use std::process::Command;

fn command(directory: &Path) -> Command {
    let mut command = Command::new(env!("CARGO_BIN_EXE_trust-cg"));
    command.arg("--permit-unlicensed"); // Claim-less fixtures: refused by default since WS7.5 (DG-73).
    command.current_dir(directory);
    command
}

#[test]
fn native_outputs_cannot_overwrite_inputs_or_each_other() {
    let directory = tempfile::tempdir().unwrap();
    let input = directory.path().join("module.tmbc");
    let original = b"source must survive even if it is not valid bitcode";
    fs::write(&input, original).unwrap();
    let cases: &[(&[&str], &str)] = &[
        (&["-c", "-o", "./module.tmbc"], "-o/--output"),
        (&["--emit-json", "./module.tmbc"], "--emit-json"),
        (&["--emit-trust_ir", "module.tmbc"], "--emit-trust_ir"),
        (
            &["--fsym=warn", "--fsym-report-json", "module.tmbc"],
            "--fsym-report-json",
        ),
        (&["--profile-generate", "module.tmbc"], "--profile-generate"),
        (&["--emit-json", "out", "-o", "./out"], "also written by"),
        (
            &["--emit-json", "out", "--profile-use", "./out"],
            "--emit-json",
        ),
    ];
    for (args, diagnostic) in cases {
        let output = command(directory.path())
            .args(*args)
            .arg("module.tmbc")
            .output()
            .unwrap();
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(!output.status.success(), "{args:?}");
        assert!(stderr.contains(diagnostic), "{args:?}: {stderr}");
        assert!(
            !stderr.contains("failed to read"),
            "alias validation ran too late: {stderr}"
        );
        assert_eq!(fs::read(&input).unwrap(), original);
        assert!(!directory.path().join("out").exists());
    }
}

#[test]
fn failed_compilation_cleans_its_temporary_directory() {
    let directory = tempfile::tempdir().unwrap();
    let scratch = directory.path().join("scratch");
    fs::create_dir(&scratch).unwrap();
    fs::write(directory.path().join("module.tmbc"), b"invalid bitcode").unwrap();
    let output = command(directory.path())
        .env("TMPDIR", &scratch)
        .env("TMP", &scratch)
        .env("TEMP", &scratch)
        .arg("module.tmbc")
        .output()
        .unwrap();
    assert!(!output.status.success());
    assert!(String::from_utf8_lossy(&output.stderr).contains("failed to read"));
    assert_eq!(fs::read_dir(&scratch).unwrap().count(), 0);
}

#[test]
fn compile_only_rejects_ambiguous_multi_input_destinations() {
    let directory = tempfile::tempdir().unwrap();
    for (args, diagnostic) in [
        (
            vec!["-c", "-o", "out.o", "a.tmbc", "b.tmbc"],
            "requires exactly one input",
        ),
        (vec!["-c", "module.tmbc", "module.json"], "also written by"),
        (vec!["-c", "module.o"], "input module"),
    ] {
        let output = command(directory.path()).args(args).output().unwrap();
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(!output.status.success());
        assert!(stderr.contains(diagnostic), "{stderr}");
        assert_eq!(fs::read_dir(directory.path()).unwrap().count(), 0);
    }
}

#[cfg(any(target_os = "macos", windows))]
#[test]
fn new_output_paths_cannot_differ_only_by_case() {
    let directory = tempfile::tempdir().unwrap();
    let output = command(directory.path())
        .args([
            "--emit-json",
            "Out.json",
            "--emit-trust_ir",
            "out.json",
            "module.tmbc",
        ])
        .output()
        .unwrap();
    assert!(!output.status.success());
    assert!(String::from_utf8_lossy(&output.stderr).contains("also written by"));
    assert_eq!(fs::read_dir(directory.path()).unwrap().count(), 0);
}

#[test]
fn native_and_wasm_outputs_reject_hard_links_to_inputs() {
    let directory = tempfile::tempdir().unwrap();
    let input = directory.path().join("module.tmbc");
    fs::write(&input, b"original input").unwrap();
    fs::hard_link(&input, directory.path().join("output")).unwrap();
    for target in ["aarch64", "wasm32"] {
        let output = command(directory.path())
            .args(["-c", "--target", target, "-o", "output", "module.tmbc"])
            .output()
            .unwrap();
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(!output.status.success());
        assert!(stderr.contains("input module"), "{stderr}");
        assert_eq!(fs::read(&input).unwrap(), b"original input");
    }
}

#[cfg(unix)]
#[test]
fn native_output_rejects_symlink_to_input() {
    let directory = tempfile::tempdir().unwrap();
    let input = directory.path().join("module.tmbc");
    fs::write(&input, b"original input").unwrap();
    std::os::unix::fs::symlink(&input, directory.path().join("output.o")).unwrap();
    let output = command(directory.path())
        .args(["-c", "-o", "output.o", "module.tmbc"])
        .output()
        .unwrap();
    assert!(!output.status.success());
    assert!(String::from_utf8_lossy(&output.stderr).contains("input module"));
    assert_eq!(fs::read(&input).unwrap(), b"original input");
}

fn proof_output_module() -> trust_ir::Module {
    // Identity lowers to a fully covered RET. Its structural and object
    // certificates exercise publication without claiming SMT lowering proof.
    use trust_ir::Ty;
    let mut module = trust_ir_build::ModuleBuilder::new("proof_output_paths");
    let signature = module.add_func_type(vec![Ty::I64], vec![Ty::I64]);
    let mut function = module.function("_identity", signature);
    let entry = function.create_block();
    let argument = function.add_block_param(entry, Ty::I64);
    function.switch_to_block(entry);
    function.ret(vec![argument]);
    function.build();
    module.build().expect("ModuleBuilder::build: test fixture")
}

#[test]
fn generated_proof_files_cannot_overwrite_source_or_object_files() {
    let directory = tempfile::tempdir().unwrap();
    let source = serde_json::to_vec(&proof_output_module()).unwrap();
    fs::create_dir(directory.path().join("relocation_inventory")).unwrap();
    let input = directory
        .path()
        .join("relocation_inventory/object_relocation_inventory.cert");
    fs::write(&input, &source).unwrap();
    let output = command(directory.path())
        .args(["--target", "aarch64-apple-darwin"])
        .args([
            "-c",
            "-O2",
            "--format=json",
            "--emit-proofs",
            ".",
            "-o",
            "module.o",
            "relocation_inventory/object_relocation_inventory.cert",
        ])
        .output()
        .unwrap();
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(!output.status.success());
    assert!(
        stderr.contains("--emit-proofs:") && stderr.contains("input module"),
        "{stderr}"
    );
    assert_eq!(fs::read(&input).unwrap(), source);

    // Place the object at the generated sidecar destination instead.
    let second = tempfile::tempdir().unwrap();
    fs::create_dir(second.path().join("relocation_inventory")).unwrap();
    let object_path = second
        .path()
        .join("relocation_inventory/object_relocation_inventory.cert");
    fs::write(&object_path, b"previous object bytes").unwrap();
    fs::write(second.path().join("module.json"), &source).unwrap();
    let output = command(second.path())
        .args(["--target", "aarch64-apple-darwin"])
        .args([
            "-c",
            "-O2",
            "--format=json",
            "--emit-proofs",
            ".",
            "-o",
            "relocation_inventory/object_relocation_inventory.cert",
            "module.json",
        ])
        .output()
        .unwrap();
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(!output.status.success());
    assert!(
        stderr.contains("--emit-proofs:") && stderr.contains("input module"),
        "{stderr}"
    );
    assert_eq!(fs::read(&object_path).unwrap(), b"previous object bytes");
}

#[test]
fn multiple_modules_keep_distinct_proof_directories() {
    let directory = tempfile::tempdir().unwrap();
    let input = trust_cg_codegen::pipeline::encode_tmbc(&proof_output_module()).unwrap();
    fs::write(directory.path().join("first.tmbc"), &input).unwrap();
    fs::write(directory.path().join("second.tmbc"), &input).unwrap();
    let output = command(directory.path())
        .args(["--target", "aarch64-apple-darwin"])
        .args([
            "-c",
            "-O2",
            "--emit-proofs",
            "proofs",
            "first.tmbc",
            "second.tmbc",
        ])
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    for index in 0..2 {
        let sidecar = directory.path().join(format!(
            "proofs/input_{index}/relocation_inventory/object_relocation_inventory.cert"
        ));
        assert!(sidecar.exists(), "missing {}", sidecar.display());
    }
}

#[cfg(unix)]
#[test]
fn linking_preserves_distinct_modules_with_the_same_basename() {
    use std::os::unix::fs::PermissionsExt;
    use trust_ir::Ty;
    use trust_ir_build::ModuleBuilder;

    let directory = tempfile::tempdir().unwrap();
    for name in ["first", "second"] {
        let input_dir = directory.path().join(name);
        fs::create_dir(&input_dir).unwrap();
        let mut module = ModuleBuilder::new(name);
        let signature = module.add_func_type(vec![], vec![Ty::I64]);
        let mut function = module.function(name, signature);
        let entry = function.create_block();
        function.switch_to_block(entry);
        let value = function.iconst(Ty::I64, 42);
        function.ret(vec![value]);
        function.build();
        fs::write(
            input_dir.join("module.tmbc"),
            trust_cg_codegen::pipeline::encode_tmbc(
                &module.build().expect("ModuleBuilder::build: test fixture"),
            )
            .unwrap(),
        )
        .unwrap();
    }
    // Capture the actual linker inputs before the driver cleans them up. The
    // driver verifies an arm64 Darwin output's ad-hoc signature after the
    // link, so on macOS the fake linker leaves a real signed stub executable
    // at the `-o` path (built by the system driver from a trivial C file).
    let linker = directory.path().join("cc");
    fs::write(
        &linker,
        concat!(
            "#!/bin/sh\nset -eu\nindex=0\nout=\nprevious=\n",
            "for arg in \"$@\"; do\n",
            "  case \"$arg\" in\n",
            "    *.o)\n",
            "      printf '%s\\n' \"$arg\" >> \"$CLI_TEST_CAPTURE/paths\"\n",
            "      cp \"$arg\" \"$CLI_TEST_CAPTURE/object_$index.o\"\n",
            "      index=$((index + 1))\n",
            "      ;;\n",
            "  esac\n",
            "  if [ \"$previous\" = -o ]; then out=\"$arg\"; fi\n",
            "  previous=\"$arg\"\n",
            "done\n",
            "test \"$index\" = 2\n",
            "if [ \"$(uname -s)\" = Darwin ]; then\n",
            "  printf 'int main(void) { return 0; }\\n' > \"$CLI_TEST_CAPTURE/stub.c\"\n",
            "  /usr/bin/cc -o \"$out\" \"$CLI_TEST_CAPTURE/stub.c\"\n",
            "fi\n",
        ),
    )
    .unwrap();
    fs::set_permissions(&linker, fs::Permissions::from_mode(0o700)).unwrap();
    let mut paths = vec![directory.path().to_path_buf()];
    paths.extend(std::env::split_paths(
        &std::env::var_os("PATH").unwrap_or_default(),
    ));
    let output = command(directory.path())
        .env("PATH", std::env::join_paths(paths).unwrap())
        .env("CLI_TEST_CAPTURE", directory.path())
        .args(["-O0", "first/module.tmbc", "second/module.tmbc"])
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let captured = fs::read_to_string(directory.path().join("paths")).unwrap();
    let paths: Vec<_> = captured.lines().collect();
    assert_eq!(paths.len(), 2);
    assert_ne!(paths[0], paths[1], "same-basename objects collided");
    assert_ne!(
        fs::read(directory.path().join("object_0.o")).unwrap(),
        fs::read(directory.path().join("object_1.o")).unwrap()
    );
    for path in paths {
        assert!(
            !Path::new(path).exists(),
            "temporary object was not cleaned up"
        );
        assert!(
            !Path::new(path).parent().unwrap().exists(),
            "temporary directory was not cleaned up"
        );
    }

    // A linker error must also unwind the driver's temporary directory.
    fs::write(&linker, b"#!/bin/sh\nexit 42\n").unwrap();
    let scratch = directory.path().join("scratch");
    fs::create_dir(&scratch).unwrap();
    let output = command(directory.path())
        .env("PATH", directory.path())
        .env("TMPDIR", &scratch)
        .env("TMP", &scratch)
        .env("TEMP", &scratch)
        .args(["-O0", "first/module.tmbc", "second/module.tmbc"])
        .output()
        .unwrap();
    assert!(!output.status.success());
    assert!(String::from_utf8_lossy(&output.stderr).contains("linker exited"));
    assert_eq!(fs::read_dir(&scratch).unwrap().count(), 0);
}
