// trust-cg-cli/tests/codegen_license_flags.rs — the trust-ir v41 codegen
// license at the CLI front door.
//
// `--recognize-authority <NAME>` (repeatable) widens the recognized gate set.
// A claim-less (`body_gate` absent) body is REFUSED by default (roadmap WS7.5,
// decision gate DG-73); `--permit-unlicensed` compiles one for a legacy
// pre-v41 corpus and prints a disclosure line naming it, and
// `--refuse-unlicensed` is accepted as an explicit spelling of the default.
// An `ungated` body is refused whatever the flags say, and the evidence-bound
// `clean-kernel-tv` compiles only with its kernel-replayed certificate
// (WS7.5(b)). Each case writes a module with exactly one licensing state and
// drives the real binary.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use std::path::{Path, PathBuf};
use std::process::Command;

use trust_ir::{
    Block, BlockId, BodyGate, Constant, FuncId, FuncTy, Function, Inst, InstrNode, Module, Ty,
    ValueId,
};

fn trust_cg_bin() -> PathBuf {
    PathBuf::from(env!("CARGO_BIN_EXE_trust-cg"))
}

fn module(gate: Option<BodyGate>) -> Module {
    let mut m = Module::new("cli_license");
    let sig = m
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![Ty::I64],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut entry = Function::new(FuncId::new(0), "entry", sig, BlockId::new(0));
    entry.blocks.push(Block {
        id: BlockId::new(0),
        params: vec![],
        body: vec![
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(7),
            })
            .with_result(ValueId::new(0)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(0)],
            }),
        ],
    });
    entry.body_gate = gate;
    m.functions.push(entry);
    m
}

fn write_module(dir: &Path, name: &str, gate: Option<BodyGate>) -> PathBuf {
    let bytes = trust_cg_codegen::pipeline::encode_tmbc(&module(gate)).expect("encode tMBC");
    let path = dir.join(format!("{name}.tmbc"));
    std::fs::write(&path, bytes).expect("write tMBC");
    path
}

/// Run `trust-cg -c --target aarch64 -o <out> [flags] <input>`; returns
/// (success, stderr).
fn run(dir: &Path, input: &Path, flags: &[&str]) -> (bool, String) {
    let out = dir.join(format!(
        "{}.o",
        input.file_stem().unwrap().to_string_lossy()
    ));
    let output = Command::new(trust_cg_bin())
        .arg("-c")
        .arg("--target")
        .arg("aarch64")
        .arg("-o")
        .arg(&out)
        .args(flags)
        .arg(input)
        .output()
        .expect("run trust-cg");
    (
        output.status.success(),
        String::from_utf8_lossy(&output.stderr).to_string(),
    )
}

fn gated(authority: &str) -> Option<BodyGate> {
    Some(BodyGate::gated(authority.to_string()))
}

#[test]
fn ungated_body_is_refused_whatever_the_flags_say() {
    let dir = tempfile::tempdir().expect("tempdir");
    let input = write_module(dir.path(), "ungated", Some(BodyGate::Ungated));
    for flags in [
        &[][..],
        &["--recognize-authority", "ungated"][..],
        &["--refuse-unlicensed"][..],
        &["--permit-unlicensed"][..],
    ] {
        let (ok, stderr) = run(dir.path(), &input, flags);
        assert!(!ok, "flags {flags:?}: must fail");
        assert!(
            stderr.contains("affirmatively ungated"),
            "flags {flags:?}: stderr:\n{stderr}"
        );
    }
}

#[test]
fn recognize_authority_widens_the_recognized_gate_set() {
    let dir = tempfile::tempdir().expect("tempdir");
    let input = write_module(dir.path(), "vendor", gated("vendor-gate"));
    let (ok, stderr) = run(dir.path(), &input, &[]);
    assert!(!ok, "unrecognized authority must fail");
    assert!(
        stderr.contains("does not recognize") && stderr.contains("vendor-gate"),
        "stderr:\n{stderr}"
    );
    let (ok, stderr) = run(
        dir.path(),
        &input,
        &[
            "--recognize-authority",
            "other",
            "--recognize-authority",
            "vendor-gate",
        ],
    );
    assert!(ok, "recognized authority must compile. stderr:\n{stderr}");

    // The Clean kernel TV gate needs no flag — and it is EVIDENCE-BOUND
    // (trust-ir WS1.5): worn with no kernel-rechecked TranslationValidation
    // certificate it is refused before any policy is consulted, as trust-ir's
    // `GatedWithoutEvidence`, and no `--recognize-authority` can stand in for
    // the certificate (KIND 4, 2026-09-24; corpus row
    // `body_gate_kernel_tv_without_certificate`).
    let clean = write_module(dir.path(), "clean", gated("clean-kernel-tv"));
    for flags in [&[][..], &["--recognize-authority", "clean-kernel-tv"][..]] {
        let (ok, stderr) = run(dir.path(), &clean, flags);
        assert!(
            !ok,
            "flags {flags:?}: an evidence-bound license without its evidence must fail"
        );
        assert!(
            stderr.contains("without the evidence it names") && stderr.contains("clean-kernel-tv"),
            "flags {flags:?}: stderr:\n{stderr}"
        );
    }
}

/// The disclosure line `--permit-unlicensed` prints.
const DISCLOSURE: &str = "trust-cg: note: --permit-unlicensed:";

/// DG-73: a claim-less body is refused by default and by the explicit
/// `--refuse-unlicensed`; `--permit-unlicensed` compiles it and DISCLOSES the
/// bodies it admitted by name.
#[test]
fn claim_less_bodies_are_refused_by_default_and_permitted_only_when_disclosed() {
    let dir = tempfile::tempdir().expect("tempdir");
    let unlicensed = write_module(dir.path(), "unlicensed", None);
    for flags in [&[][..], &["--refuse-unlicensed"][..]] {
        let (ok, stderr) = run(dir.path(), &unlicensed, flags);
        assert!(!ok, "flags {flags:?}: a claim-less body must be refused");
        assert!(
            stderr.contains("function `entry` carries no codegen license")
                && stderr.contains("--permit-unlicensed"),
            "flags {flags:?}: stderr:\n{stderr}"
        );
        assert!(
            !stderr.contains(DISCLOSURE),
            "flags {flags:?}: stderr:\n{stderr}"
        );
    }
    let (ok, stderr) = run(dir.path(), &unlicensed, &["--permit-unlicensed"]);
    assert!(
        ok,
        "--permit-unlicensed compiles a claim-less body. stderr:\n{stderr}"
    );
    let disclosure = stderr
        .lines()
        .find(|line| line.starts_with(DISCLOSURE))
        .unwrap_or_else(|| panic!("--permit-unlicensed must disclose. stderr:\n{stderr}"));
    assert!(
        disclosure.contains("compiling 1 function body with NO codegen license")
            && disclosure.ends_with(": entry"),
        "{disclosure}"
    );

    // The two spellings contradict each other: a usage error, never a guess.
    let (ok, stderr) = run(
        dir.path(),
        &unlicensed,
        &["--permit-unlicensed", "--refuse-unlicensed"],
    );
    assert!(!ok, "contradictory flags must fail");
    assert!(stderr.contains("cannot be used with"), "stderr:\n{stderr}");

    // A body licensed by a RECOGNIZED authority outside trust-ir's evidence
    // table (recognition is the whole decision there) compiles by default,
    // with nothing to disclose; `clean-kernel-tv` would need its certificate
    // (see `recognize_authority_widens_the_recognized_gate_set`).
    let licensed = write_module(dir.path(), "licensed", gated("vendor-gate"));
    for flags in [
        &["--recognize-authority", "vendor-gate"][..],
        &[
            "--permit-unlicensed",
            "--recognize-authority",
            "vendor-gate",
        ][..],
    ] {
        let (ok, stderr) = run(dir.path(), &licensed, flags);
        assert!(
            ok,
            "flags {flags:?}: a licensed body compiles. stderr:\n{stderr}"
        );
        assert!(
            !stderr.contains(DISCLOSURE),
            "flags {flags:?}: stderr:\n{stderr}"
        );
    }
}

/// A vendored trust-ir conformance fixture, decoded from its tMBC.
fn conformance(name: &str) -> Module {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/fixtures/trust_ir_binary_container/conformance")
        .join(format!("{name}.tmbc"));
    let bytes =
        std::fs::read(&path).unwrap_or_else(|error| panic!("read {}: {error}", path.display()));
    trust_ir::binary::deserialize_module(&bytes)
        .unwrap_or_else(|error| panic!("decode {name}: {error:?}"))
}

/// The vendored Lean-envelope conformance fixture: the Clean Fragment-2
/// `addmul`, `Gated{"clean-kernel-tv"}` with its kernel-certified TV row. Its
/// license predates trust-ir v61 and records no `GateEvidence`.
fn envelope() -> Module {
    conformance("lean_library_envelope")
}

fn write_json(dir: &Path, name: &str, module: &Module) -> PathBuf {
    let path = dir.join(format!("{name}.json"));
    std::fs::write(&path, serde_json::to_string(module).expect("JSON")).expect("write JSON");
    path
}

/// The flag sets no `clean-kernel-tv` license may lean on in place of its
/// evidence.
const KERNEL_TV_FLAGS: [&[&str]; 3] = [
    &["--format=json"],
    &["--format=json", "--permit-unlicensed"],
    &["--format=json", "--recognize-authority", "clean-kernel-tv"],
];

/// Row `consumer.cg.kernel_tv_license_bound` at the CLI.
///
/// The positive arm is `certificate_binding`, whose two `clean-kernel-tv`
/// licenses (`double`, `quad`) carry the `GateEvidence` trust-ir v61
/// requires, each naming its function's `Certified` TranslationValidation
/// row and the body's digest, and whose certificates the pinned kernel
/// replays: it compiles with NO flag and writes an object, with nothing
/// permitted and nothing disclosed. The negative arms are refused by name
/// whatever the flags:
///
/// * the same module without its certificates: the licenses still cite their
///   rows, but the kernel-replayed certificate each rests on is gone
///   (`GatedWithoutEvidence`). trust-ir's structural validation refuses it
///   too (`CertifiedWithoutCleanCic`: its rows stay `Certified` with no
///   certificate), so the refusal is pinned by the license rule's message
///   with its certificate-specific detail, which is what this row measures;
/// * `lean_library_envelope`, whose pre-v61 license records no `GateEvidence`
///   at all (`UnevidencedGate`, OD-V61-GATE-EVIDENCE-20261014), although its
///   certificate is present. Before v61 it was this test's positive arm
///   (DR-KERNEL-TV-CLI-ARMS-20261017).
#[test]
fn kernel_tv_license_compiles_only_with_its_certificate() {
    let dir = tempfile::tempdir().expect("tempdir");
    let certified = conformance("certificate_binding");
    assert!(
        certified.functions.iter().all(|function| matches!(
            &function.body_gate,
            Some(BodyGate::Gated { authority, evidence: Some(_) }) if authority == "clean-kernel-tv"
        )),
        "the positive arm's licenses are clean-kernel-tv licenses that carry their evidence"
    );
    assert!(!certified.proof_certificates.is_empty());
    let input = write_json(dir.path(), "certified", &certified);
    let (ok, stderr) = run(dir.path(), &input, &["--format=json"]);
    assert!(
        ok,
        "the certified module compiles by default. stderr:\n{stderr}"
    );
    assert!(!stderr.contains(DISCLOSURE), "stderr:\n{stderr}");
    let object = dir.path().join("certified.o");
    assert!(
        std::fs::metadata(&object).is_ok_and(|meta| meta.len() > 0),
        "the certified module writes an object: {}",
        object.display()
    );

    // The cause pinned is the certificate's absence: the license rule's
    // detail for the row `double`'s evidence cites, not another of its
    // `GatedWithoutEvidence` causes (no TV row in scope, two rows, a row not
    // `certified`, an anchored certificate that was not kernel-replayed).
    let double_row = match &certified
        .function_by_name("double")
        .expect("the positive arm licenses `double`")
        .body_gate
    {
        Some(BodyGate::Gated {
            evidence: Some(evidence),
            ..
        }) => evidence.obligation,
        other => panic!("`double`'s license carries its evidence: {other:?}"),
    };
    let no_certificate = format!(
        "function `double` claims codegen license `Gated{{\"clean-kernel-tv\"}}` without the \
         evidence it names: TranslationValidation obligation {double_row} carries no CleanCic \
         certificate under the clean_backend_tv kernel anchor"
    );
    let mut twin = conformance("certificate_binding");
    twin.proof_certificates.clear();
    let twin = write_json(dir.path(), "twin", &twin);
    for flags in KERNEL_TV_FLAGS {
        let (ok, stderr) = run(dir.path(), &twin, flags);
        assert!(
            !ok,
            "flags {flags:?}: a license whose certificate is gone must be refused"
        );
        assert!(
            stderr.contains(&no_certificate),
            "flags {flags:?}: stderr:\n{stderr}"
        );
    }

    let unevidenced = write_json(dir.path(), "unevidenced", &envelope());
    for flags in KERNEL_TV_FLAGS {
        let (ok, stderr) = run(dir.path(), &unevidenced, flags);
        assert!(
            !ok,
            "flags {flags:?}: a license with no GateEvidence must be refused"
        );
        assert!(
            stderr.contains(
                "function `addmul` is licensed by the evidence-bound gate authority \
                 \"clean-kernel-tv\" with no GateEvidence (trust-ir v61)"
            ),
            "flags {flags:?}: stderr:\n{stderr}"
        );
    }
}

/// Row `LEAN.consumer.ungated_codegen` (F-116), ported from Part A-Lean
/// (`parta-lean/run.py`): the envelope module with EVERY function re-stamped
/// `Ungated` ("native_codegen=unavailable"), handed to `trust-cg
/// --format=json -c`, must be REFUSED (the row's PASS), and the refusal must
/// name the body. The row's residue (F-116: "trust-cg's DEFAULT policy still
/// permits body_gate None") is closed too: the same module with the stamp
/// DELETED is refused by default, not compiled.
#[test]
fn lean_consumer_ungated_codegen() {
    let dir = tempfile::tempdir().expect("tempdir");
    let mut ungated = envelope();
    for function in &mut ungated.functions {
        function.body_gate = Some(BodyGate::Ungated);
    }
    assert_eq!(
        trust_ir_build::validate_module(&ungated),
        [],
        "the row: it validates"
    );
    let input = write_json(dir.path(), "home_ungated", &ungated);
    for flags in [
        &["--format=json"][..],
        &["--format=json", "--permit-unlicensed"][..],
    ] {
        let (ok, stderr) = run(dir.path(), &input, flags);
        assert!(!ok, "flags {flags:?}: the Ungated envelope must be refused");
        assert!(
            stderr.contains("function `addmul` is affirmatively ungated"),
            "flags {flags:?}: stderr:\n{stderr}"
        );
    }

    let mut stripped = envelope();
    stripped.proof_obligations.clear();
    stripped.proof_certificates.clear();
    for function in &mut stripped.functions {
        function.body_gate = None;
    }
    let input = write_json(dir.path(), "home_stripped", &stripped);
    let (ok, stderr) = run(dir.path(), &input, &["--format=json"]);
    assert!(!ok, "a stripped license must not be a bypass");
    assert!(
        stderr.contains("function `addmul` carries no codegen license"),
        "stderr:\n{stderr}"
    );
}

#[test]
fn help_documents_the_license_flags() {
    let output = Command::new(trust_cg_bin())
        .arg("--help")
        .output()
        .expect("run trust-cg --help");
    assert!(output.status.success());
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(stdout.contains("--recognize-authority"), "{stdout}");
    assert!(stdout.contains("--permit-unlicensed"), "{stdout}");
    assert!(stdout.contains("--refuse-unlicensed"), "{stdout}");
}

/// WS7.3 (F-064 / F-065 / F-072): the `.trust_ir` TEXT codec cannot carry
/// function summaries, clause bindings, every layout fact or `global_asm` at
/// this trust-ir pin. Text input is therefore REFUSED on the strict license
/// path (`--refuse-unlicensed`) and the proof path (`--emit-proofs`), naming
/// `TEXT_INPUT_NOT_TOTAL`, and compiles with that named warning by default.
/// The same module as tMBC compiles under `--refuse-unlicensed` (the control).
#[test]
fn text_input_is_refused_on_strict_paths_and_warned_on_the_default_path() {
    let dir = tempfile::tempdir().expect("tempdir");
    let module = module(gated("vendor-gate"));
    let text = dir.path().join("licensed.trust_ir");
    std::fs::write(&text, module.to_string()).expect("write .trust_ir");
    let strict = [
        "--refuse-unlicensed",
        "--recognize-authority",
        "vendor-gate",
    ];
    let text_strict = [
        "--format=text",
        "--refuse-unlicensed",
        "--recognize-authority",
        "vendor-gate",
    ];

    let (ok, stderr) = run(
        dir.path(),
        &text,
        &["--format=text", "--recognize-authority", "vendor-gate"],
    );
    assert!(
        ok,
        "text input compiles on the default path. stderr:\n{stderr}"
    );
    assert!(
        stderr.contains("warning") && stderr.contains("TEXT_INPUT_NOT_TOTAL"),
        "the default path names the text codec's gap. stderr:\n{stderr}"
    );

    let (ok, stderr) = run(dir.path(), &text, &text_strict);
    assert!(!ok, "text input must be refused under --refuse-unlicensed");
    assert!(
        stderr.contains("refused under --refuse-unlicensed")
            && stderr.contains("TEXT_INPUT_NOT_TOTAL"),
        "stderr:\n{stderr}"
    );

    let proofs = dir.path().join("proofs");
    let emit = format!("--emit-proofs={}", proofs.display());
    let (ok, stderr) = run(
        dir.path(),
        &text,
        &[
            "--format=text",
            &emit,
            "--recognize-authority",
            "vendor-gate",
        ],
    );
    assert!(!ok, "text input must be refused under --emit-proofs");
    assert!(
        stderr.contains("refused under --emit-proofs") && stderr.contains("TEXT_INPUT_NOT_TOTAL"),
        "stderr:\n{stderr}"
    );
    assert!(!proofs.exists(), "nothing is published for a refused input");

    // Control: the binary twin of the same module compiles on the strict path.
    let binary = write_module(dir.path(), "licensed_bin", gated("vendor-gate"));
    let (ok, stderr) = run(dir.path(), &binary, &strict);
    assert!(
        ok,
        "the tMBC twin compiles under --refuse-unlicensed. stderr:\n{stderr}"
    );
    assert!(
        !stderr.contains("TEXT_INPUT_NOT_TOTAL"),
        "stderr:\n{stderr}"
    );
}
