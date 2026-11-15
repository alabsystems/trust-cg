// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

use super::*;

#[test]
fn tracked_directory_is_first_or_equal_and_empty_never_means_cwd() {
    let cell = OnceLock::new();
    assert!(install(&cell, Some(PathBuf::new())));
    assert!(install(&cell, None));
    assert!(!install(&cell, Some(PathBuf::from("other"))));
    assert_eq!(resolve(cell.get(), Some("ambient".into())), None);
    assert_eq!(resolve(None, Some(OsString::new())), None);
    assert_eq!(resolve(None, None), None);
    assert_eq!(
        resolve(None, Some("ambient".into())),
        Some("ambient".into())
    );
    let cell = OnceLock::new();
    assert!(install(&cell, Some("recorded".into())));
    assert!(install(&cell, Some("recorded".into())));
    assert!(!install(&cell, None));
    assert_eq!(
        resolve(cell.get(), Some("ambient".into())),
        Some("recorded".into())
    );
}

#[test]
fn snapshots_keep_complete_borrowed_metadata_and_publish_together() {
    use trust_cg_ir::{AArch64Opcode, MachFunction, MachInst, Signature};
    use trust_cg_lower::instructions::{Block, Value};

    let dir = tempfile::tempdir().unwrap();
    let module = trust_ir::Module::new("../module-name-is-not-a-path");
    let mut lir = trust_cg_lower::Function::new(
        "../../callee-name-is-not-a-path",
        trust_cg_lower::function::Signature {
            params: vec![],
            returns: vec![],
        },
    );
    lir.pure_callees
        .insert("metadata-retained-not-authorized".into());
    lir.trust_ir_origins.insert(Block(0), vec![None]);
    lir.value_types.insert(Value(8), trust_cg_lower::Type::F32);
    let lir = vec![(lir, trust_cg_lower::ProofContext::default())];
    let mut machine = MachFunction::new(lir[0].0.name.clone(), Signature::new(vec![], vec![]));
    machine
        .insts
        .push(MachInst::new(AArch64Opcode::Ret, vec![]));
    machine.insts[0].implicit_uses = &[trust_cg_ir::regs::X19];
    let machine = vec![machine];
    let metrics = vec![PreparationMetrics::default()];
    let config = CompilerConfig::default();
    let target = TargetSpec::parse("aarch64-unknown-linux-gnu").unwrap();
    let make_view = || PreparedModule {
        module: &module,
        lir: &lir,
        machine: &machine,
        metrics: &metrics,
        config: &config,
        target: &target,
    };
    let before = format!("{module:?}{lir:?}{machine:?}{metrics:?}");
    for _ in 0..2 {
        let path = write(dir.path(), make_view()).unwrap();
        assert_eq!(path.parent(), Some(dir.path()));
        assert!(
            path.file_name()
                .unwrap()
                .to_str()
                .unwrap()
                .starts_with("capture-")
        );
        let manifest: serde_json::Value =
            serde_json::from_slice(&std::fs::read(path.join("snapshot.json")).unwrap()).unwrap();
        assert_eq!(manifest["proof_or_encoding_authority"], false);
        assert_eq!(manifest["stage"], "prepared-before-certificate-generation");
        let bytes = std::fs::read(path.join("source.trust_irbin")).unwrap();
        let decoded = trust_ir::binary::deserialize_module(&bytes).unwrap();
        assert_eq!(format!("{decoded:?}"), format!("{module:?}"));
        assert_eq!(manifest["source_sha256"], sha256_hex(&bytes));
        for (suffix, expected, field) in [
            ("lir.txt", format!("{:#?}", lir[0].0), "lir_sha256"),
            (
                "machine.txt",
                format!("{:#?}", machine[0]),
                "machine_sha256",
            ),
            (
                "proof-context.txt",
                format!("{:#?}", lir[0].1),
                "proof_context_sha256",
            ),
            (
                "frame.txt",
                format!("{:#?}", metrics[0].frame_layout),
                "frame_sha256",
            ),
        ] {
            let bytes = std::fs::read(path.join(format!("function-0.{suffix}"))).unwrap();
            assert_eq!(bytes, expected.as_bytes());
            assert_eq!(manifest["functions"][0][field], sha256_hex(&bytes));
        }
        assert_eq!(manifest["functions"][0]["name"], machine[0].name);
    }
    assert_eq!(before, format!("{module:?}{lir:?}{machine:?}{metrics:?}"));
    assert!(dir.path().read_dir().unwrap().all(|p| {
        !p.unwrap()
            .file_name()
            .to_str()
            .unwrap()
            .starts_with(".pending-")
    }));
}

#[test]
fn distinct_nan_payloads_survive_when_debug_text_is_identical() {
    use trust_cg_ir::{AArch64Opcode, MachFunction, MachInst, MachOperand, Signature};
    use trust_cg_lower::instructions::{Block, Instruction, Opcode, Value};
    let dir = tempfile::tempdir().unwrap();
    let module = trust_ir::Module::new("nan-serialization");
    let config = CompilerConfig::default();
    let target = TargetSpec::parse("aarch64-unknown-linux-gnu").unwrap();
    let metrics = [PreparationMetrics::default()];
    let mut manifests = Vec::new();
    for bits in [0x7ff8_0000_0000_1234, 0x7ff8_0000_0000_abcd] {
        let value = f64::from_bits(bits);
        let mut lir = trust_cg_lower::Function::new(
            "f",
            trust_cg_lower::function::Signature {
                params: vec![],
                returns: vec![],
            },
        );
        lir.blocks.insert(
            Block(0),
            trust_cg_lower::function::BasicBlock {
                instructions: vec![Instruction {
                    opcode: Opcode::Fconst {
                        ty: trust_cg_lower::Type::F64,
                        imm: value,
                    },
                    args: vec![],
                    results: vec![Value(0)],
                }],
                ..Default::default()
            },
        );
        let lir = [(lir, trust_cg_lower::ProofContext::default())];
        let mut machine = MachFunction::new("f".into(), Signature::new(vec![], vec![]));
        // A raw serialization control, not an admitted executable program.
        machine.insts.push(MachInst::new(
            AArch64Opcode::Ret,
            vec![MachOperand::FImm(value)],
        ));
        let machine = [machine];
        let path = write(
            dir.path(),
            PreparedModule {
                module: &module,
                lir: &lir,
                machine: &machine,
                metrics: &metrics,
                config: &config,
                target: &target,
            },
        )
        .unwrap();
        for suffix in ["lir-identity.txt", "machine-identity.txt"] {
            assert!(
                std::fs::read_to_string(path.join(format!("function-0.{suffix}")))
                    .unwrap()
                    .contains(&format!("{bits:016x}"))
            );
        }
        manifests.push(
            serde_json::from_slice::<serde_json::Value>(
                &std::fs::read(path.join("snapshot.json")).unwrap(),
            )
            .unwrap(),
        );
    }
    let (a, b) = (&manifests[0]["functions"][0], &manifests[1]["functions"][0]);
    assert_eq!(a["machine_sha256"], b["machine_sha256"]);
    assert_eq!(a["lir_sha256"], b["lir_sha256"]);
    assert_ne!(a["machine_identity_sha256"], b["machine_identity_sha256"]);
    assert_ne!(a["lir_identity_sha256"], b["lir_identity_sha256"]);
}

#[test]
fn incomplete_pairing_and_bad_destinations_do_not_publish_a_snapshot() {
    let dir = tempfile::tempdir().unwrap();
    let module = trust_ir::Module::new("empty");
    let config = CompilerConfig::default();
    let target = TargetSpec::parse("aarch64-unknown-linux-gnu").unwrap();
    let metrics = vec![PreparationMetrics::default()];
    let bad = PreparedModule {
        module: &module,
        lir: &[],
        machine: &[],
        metrics: &metrics,
        config: &config,
        target: &target,
    };
    assert!(write(dir.path(), bad).is_err());
    assert_eq!(dir.path().read_dir().unwrap().count(), 0);
    let file = dir.path().join("sentinel");
    std::fs::write(&file, b"keep").unwrap();
    let view = PreparedModule {
        module: &module,
        lir: &[],
        machine: &[],
        metrics: &[],
        config: &config,
        target: &target,
    };
    assert!(write(&file, view).is_err());
    assert_eq!(std::fs::read(&file).unwrap(), b"keep");
}
