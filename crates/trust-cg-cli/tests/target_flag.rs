// trust-cg-cli/tests/target_flag.rs - CLI target parsing boundary tests
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use std::path::PathBuf;
use std::process::Command;

/// Path to the compiled `trust-cg` binary for this test run.
fn trust_cg_bin() -> PathBuf {
    PathBuf::from(env!("CARGO_BIN_EXE_trust-cg"))
}

#[test]
fn cli_rejects_unsupported_x86_32_targets_before_compilation() {
    for target in [
        "x86",
        "i386",
        "i486",
        "i586",
        "i686",
        "i686-unknown-linux-gnu",
        "i686-pc-windows-msvc",
        "i386-apple-darwin",
    ] {
        let output = Command::new(trust_cg_bin())
            .arg("--permit-unlicensed")
            .arg("-c")
            .arg("--target")
            .arg(target)
            .arg("unused.tmbc")
            .output()
            .unwrap_or_else(|error| panic!("run trust-cg for target {target}: {error}"));

        assert!(
            !output.status.success(),
            "unsupported 32-bit x86 target {target} should fail"
        );
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(
            stderr.contains("unsupported 32-bit x86 target"),
            "{target} error should explicitly reject 32-bit x86. stderr:\n{stderr}"
        );
        assert!(
            stderr.contains("x86 support is x86_64 only") && stderr.contains("x86_64 triple"),
            "{target} error should point users at x86_64-only support. stderr:\n{stderr}"
        );
        assert!(
            !stderr.contains("failed to read trust_ir module"),
            "{target} should fail while parsing --target, before input loading. stderr:\n{stderr}"
        );
    }
}

#[test]
fn cli_help_says_x86_support_is_x86_64_only() {
    let output = Command::new(trust_cg_bin())
        .arg("--permit-unlicensed")
        .arg("--help")
        .output()
        .expect("run trust-cg --help");

    assert!(output.status.success(), "--help should succeed");
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("x86_64 only") && stdout.contains("32-bit x86"),
        "--help should document the x86_64-only boundary. stdout:\n{stdout}"
    );
}

/// `fn _f16_add(a: f16, b: f16) -> f16 { a + b }` as tMBC.
fn f16_add_tmbc() -> Vec<u8> {
    use trust_ir::{
        BinOp, Block, BlockId, FuncId, FuncTy, Function, Inst, InstrNode, Module, Ty, ValueId,
    };
    let mut module = Module::new("cli_aarch64_isa_features");
    let ty = module
        .add_func_type(FuncTy {
            params: vec![Ty::F16, Ty::F16],
            returns: vec![Ty::F16],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut function = Function::new(FuncId::new(0), "_f16_add", ty, BlockId::new(0));
    function.blocks = vec![Block {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), Ty::F16), (ValueId::new(1), Ty::F16)],
        body: vec![
            InstrNode::new(Inst::BinOp {
                op: BinOp::FAdd,
                ty: Ty::F16,
                lhs: ValueId::new(0),
                rhs: ValueId::new(1),
            })
            .with_result(ValueId::new(2)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(2)],
            }),
        ],
    }];
    module
        .try_add_function(function)
        .expect("Module::try_add_function: test fixture");
    trust_cg_codegen::pipeline::encode_tmbc(&module).expect("encode tMBC")
}

/// L04-P9: generic Linux AArch64 admits FEAT_FP16 arithmetic only through the
/// explicit `--aarch64-isa-features` list; malformed lists and non-AArch64
/// targets are refused before compilation.
#[test]
fn cli_aarch64_isa_features_is_the_explicit_fp16_admission() {
    // Removed when the test ends, passed or failed.
    let dir = scratch::create("trust_cg_cli_isa_");
    let input = dir.join("f16_add.tmbc");
    std::fs::write(&input, f16_add_tmbc()).unwrap();
    let run = |target: &str, features: Option<&str>, output: &str| {
        let mut command = Command::new(trust_cg_bin());
        command.arg("--permit-unlicensed"); // Claim-less fixtures: refused by default since WS7.5 (DG-73).
        command.arg("-c").arg("--target").arg(target);
        if let Some(features) = features {
            command.arg("--aarch64-isa-features").arg(features);
        }
        command
            .arg("-o")
            .arg(dir.join(output))
            .arg(&input)
            .output()
            .expect("run trust-cg")
    };
    let stderr =
        |output: &std::process::Output| String::from_utf8_lossy(&output.stderr).into_owned();

    let refused = run("aarch64-unknown-linux-gnu", None, "contract.o");
    assert!(!refused.status.success());
    assert!(
        stderr(&refused).contains("FEAT_FP16 is not admitted"),
        "{}",
        stderr(&refused)
    );

    let admitted = run("aarch64-unknown-linux-gnu", Some("fp16"), "explicit.o");
    assert!(admitted.status.success(), "{}", stderr(&admitted));
    let object = std::fs::read(dir.join("explicit.o")).unwrap();
    assert_eq!(&object[..4], b"\x7fELF");
    let fadd_h = object
        .as_chunks::<4>()
        .0
        .iter()
        .map(|word| u32::from_le_bytes(*word))
        .any(|word| word & 0xffe0_fc00 == 0x1ee0_2800);
    assert!(fadd_h, "the explicit-profile object lacks FADD Hd, Hn, Hm");

    let unknown = run("aarch64-unknown-linux-gnu", Some("fp17"), "unknown.o");
    assert!(!unknown.status.success());
    assert!(
        stderr(&unknown).contains("unknown AArch64 ISA feature `fp17`"),
        "{}",
        stderr(&unknown)
    );

    let x86 = run("x86_64-unknown-linux-gnu", Some("fp16"), "x86.o");
    assert!(!x86.status.success());
    assert!(
        stderr(&x86).contains("explicit AArch64 ISA profile"),
        "{}",
        stderr(&x86)
    );
    let _ = std::fs::remove_dir_all(&dir);
}

#[path = "common/scratch.rs"]
mod scratch;
