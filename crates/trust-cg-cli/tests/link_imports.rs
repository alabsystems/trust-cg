// trust-cg-cli/tests/link_imports.rs — `--link <dep>` (roadmap WS7.9).
//
// A trust-ir module whose proof certificate inherits a dependency's
// discharged obligation (`InheritedFromCallee { external: Some(_) }`) is
// refused by a single-module compile. `--link` hands the dependency modules to
// trust-ir's linked validator; only a clean walk lets the backend admit
// exactly the inheritances it authenticated. Each case writes real tMBC files
// and drives the real binary.
//
// Fixture shape: the dependency `dep` defines `f(x: i64) -> i64 { x + 1 }`
// with a `proved` contract `ensures (= 1 1)` backed by a kernel-CERTIFIED
// Postcondition (the Clean kernel really discharges it, and trust-ir's
// validator really re-checks it in-process). The client `client` records
// `dep` in its import table, declares `f`, calls it from `caller`, and
// discharges its own Postcondition about `f` by inheriting `dep`'s #0 — the
// shape of clean's `emit_trust_ir_link` client plus its dependency.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use std::path::{Path, PathBuf};
use std::process::Command;

use trust_ir::clean_expr_lowering::contract::contract_clean_cic_certificate;
use trust_ir::proof::{
    ObligationKind, ProofCertificate, ProofEvidence, ProofFormula, ProofObligation, ProofStatus,
};
use trust_ir::ty::Ty;
use trust_ir::value::{FuncId, ImportId, ProofId};
use trust_ir::{
    BodyGate, Endianness, ExternRef, FunctionSummary, Module, ModuleImport, Producer, TargetInfo,
};
use trust_ir_build::{ModuleBuilder, validate_module};

fn trust_cg_bin() -> PathBuf {
    PathBuf::from(env!("CARGO_BIN_EXE_trust-cg"))
}

fn target() -> TargetInfo {
    TargetInfo {
        triple: "aarch64-apple-darwin".into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: None,
        struct_passing: Default::default(),
    }
}

/// The gate authority stamped on every fixture body: a v41+ blob must
/// license each body, and `run` recognizes exactly this authority.
const FIXTURE_AUTHORITY: &str = "ws7-9-link-fixture";

fn fixture_license() -> Option<BodyGate> {
    Some(BodyGate::Gated {
        authority: FIXTURE_AUTHORITY.to_string(),
        evidence: None,
    })
}

fn clause() -> ProofFormula {
    ProofFormula::smtlib2("(= 1 1)", "Bool")
}

fn contract() -> FunctionSummary {
    FunctionSummary::new()
        .with_params(vec!["x".to_string()])
        .ensuring(clause())
}

/// The dependency: `f(x: param) -> i64 { x + increment }` (the parameter is
/// `param`, so a `u64` twin gives the signature-skew case), with a proved
/// contract backed by a kernel-certified Postcondition #0.
fn dependency_with(param: Ty, increment: i128) -> Module {
    let mut mb = ModuleBuilder::new_with_target_info("dep", target());
    mb.set_default_producer(Producer::TRust);
    let ft = mb.add_func_type(vec![param.clone()], vec![param.clone()]);
    let mut fb = mb.function("f", ft);
    let entry = fb.create_block();
    let x = fb.add_block_param(entry, param.clone());
    fb.switch_to_block(entry);
    let k = fb.iconst(param.clone(), increment);
    let r = fb.add(param, x, k);
    fb.ret(vec![r]);
    fb.build();
    let mut module = mb.build().expect("ModuleBuilder::build: test fixture");
    let f = module.functions[0].id;
    module.functions[0].body_gate = fixture_license();
    module.functions[0].summary = Some(contract().proved());
    let obligation = ProofObligation::new(
        ProofId::new(0),
        ObligationKind::Postcondition,
        ProofStatus::Certified,
        "ensures (= 1 1)",
    )
    .with_function(f)
    .with_formula(clause());
    let certificate = contract_clean_cic_certificate(&obligation, "contract-prover")
        .expect("(= 1 1) is genuinely kernel-provable");
    module.proof_obligations.push(obligation);
    module.proof_certificates.push(certificate);
    assert!(
        validate_module(&module).is_empty(),
        "the dependency fixture must validate on its own: {:?}",
        validate_module(&module)
    );
    module
}

fn dependency() -> Module {
    dependency_with(Ty::I64, 1)
}

/// The client: imports `dep` by digest, declares `f(i64) -> i64`, defines
/// `caller(x) = f(x)`, and discharges Postcondition #0 about `f` by
/// inheriting `dep`'s #0.
fn client(dep: &Module) -> Module {
    client_with(dep, true)
}

/// [`client`], whose `caller` either calls `f` (`calls`) or is the empty
/// leaf `fn()` — the one body a proof-required (`--emit-proofs`) compile
/// promotes without solver evidence, so the sidecar can be observed.
fn client_with(dep: &Module, calls: bool) -> Module {
    let mut mb = ModuleBuilder::new_with_target_info("client", target());
    mb.set_default_producer(Producer::TRust);
    let ft = mb.add_func_type(vec![Ty::I64], vec![Ty::I64]);
    let leaf = mb.add_func_type(vec![], vec![]);
    {
        // Body-less declaration of the dependency's `f` (FuncId 0).
        let fb = mb.function("f", ft);
        fb.build();
    }
    if calls {
        let mut fb = mb.function("caller", ft);
        let entry = fb.create_block();
        let x = fb.add_block_param(entry, Ty::I64);
        fb.switch_to_block(entry);
        let r = fb.call(FuncId::new(0), vec![x]);
        fb.ret(vec![r]);
        fb.build();
    } else {
        let mut fb = mb.function("caller", leaf);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        fb.ret(vec![]);
        fb.build();
    }
    let mut m = mb.build().expect("ModuleBuilder::build: test fixture");
    m.functions[1].body_gate = fixture_license();
    let f = m.functions[0].id;
    m.functions[0].summary = Some(contract());
    let import = m
        .intern_import(
            ModuleImport::new(dep.name.clone(), dep.stable_digest()).with_producer(Producer::TRust),
        )
        .expect("id space");
    m.proof_obligations.push(
        ProofObligation::new(
            ProofId::new(0),
            ObligationKind::Postcondition,
            ProofStatus::Discharged,
            "inherited ensures (= 1 1)",
        )
        .with_function(f)
        .with_formula(clause()),
    );
    m.proof_certificates
        .push(inheritance_certificate(f, far(import)));
    m
}

fn far(import: ImportId) -> ExternRef {
    ExternRef::new(import, "f").relying_on(ProofId::new(0))
}

fn inheritance_certificate(callee: FuncId, external: ExternRef) -> ProofCertificate {
    ProofCertificate {
        obligation: ProofId::new(0),
        prover: "compose".to_string(),
        evidence: ProofEvidence::InheritedFromCallee {
            callee,
            obligation: ProofId::new(0),
            external: Some(external),
        },
        assurance: None,
    }
}

fn write(dir: &Path, name: &str, module: &Module) -> PathBuf {
    let bytes = trust_cg_codegen::pipeline::encode_tmbc(module).expect("encode tMBC");
    let path = dir.join(format!("{name}.tmbc"));
    std::fs::write(&path, bytes).expect("write tMBC");
    path
}

/// Run `trust-cg -c --target aarch64-apple-darwin -o <input>.o [flags] <input>`; returns
/// (success, stderr).
fn run(dir: &Path, input: &Path, flags: &[&str]) -> (bool, String) {
    let out = dir.join(format!(
        "{}.o",
        input.file_stem().unwrap().to_string_lossy()
    ));
    let output = Command::new(trust_cg_bin())
        .arg("-c")
        .arg("--target")
        .arg("aarch64-apple-darwin")
        .arg("-o")
        .arg(&out)
        .arg("--recognize-authority")
        .arg(FIXTURE_AUTHORITY)
        .args(flags)
        .arg(input)
        .output()
        .expect("run trust-cg");
    (
        output.status.success(),
        String::from_utf8_lossy(&output.stderr).to_string(),
    )
}

fn link_flags(deps: &[&Path]) -> Vec<String> {
    deps.iter()
        .flat_map(|dep| ["--link".to_string(), dep.display().to_string()])
        .collect()
}

fn run_linked(dir: &Path, input: &Path, deps: &[&Path], extra: &[&str]) -> (bool, String) {
    let mut flags = link_flags(deps);
    flags.extend(extra.iter().map(|flag| (*flag).to_string()));
    let flags: Vec<&str> = flags.iter().map(String::as_str).collect();
    run(dir, input, &flags)
}

/// Positive: the client plus its dependency compiles under `--link`.
#[test]
fn a_linked_client_with_its_dependency_compiles() {
    let dir = tempfile::tempdir().expect("tempdir");
    let dep = dependency();
    let dep_path = write(dir.path(), "dep", &dep);
    let client_path = write(dir.path(), "client", &client(&dep));
    let (ok, stderr) = run_linked(dir.path(), &client_path, &[&dep_path], &[]);
    assert!(ok, "the linked client must compile:\n{stderr}");
    assert!(dir.path().join("client.o").is_file());
}

/// `--emit-proofs` under `--link` records every authenticated dependency
/// MODULE (name, digest, producer) in `linked_dependencies.json`.
#[test]
fn emit_proofs_records_the_authenticated_dependency_modules() {
    let dir = tempfile::tempdir().expect("tempdir");
    let dep = dependency();
    let dep_path = write(dir.path(), "dep", &dep);
    let client_path = write(dir.path(), "client", &client_with(&dep, false));
    let proofs = dir.path().join("proofs");
    let proofs_flag = format!("--emit-proofs={}", proofs.display());
    let (ok, stderr) = run_linked(dir.path(), &client_path, &[&dep_path], &[&proofs_flag]);
    assert!(ok, "the linked leaf client must compile:\n{stderr}");
    let sidecar = std::fs::read_to_string(proofs.join("linked_dependencies.json"))
        .expect("--emit-proofs writes the linked dependency sidecar");
    let sidecar: serde_json::Value = serde_json::from_str(&sidecar).expect("sidecar JSON");
    assert_eq!(sidecar["schema"], "trust-cg.linked_dependencies.v1");
    let rows = sidecar["linked_dependencies"].as_array().expect("rows");
    assert_eq!(rows.len(), 1, "{sidecar}");
    assert_eq!(rows[0]["name"], "dep");
    assert_eq!(rows[0]["digest"], dep.stable_digest().to_string());
    assert_eq!(rows[0]["producer"], "TRust");
}

/// Adversarial: without `--link` the cross-crate inheritance stays refused.
#[test]
fn without_link_the_external_inheritance_stays_refused() {
    let dir = tempfile::tempdir().expect("tempdir");
    let dep = dependency();
    let client_path = write(dir.path(), "client", &client(&dep));
    let (ok, stderr) = run(dir.path(), &client_path, &[]);
    assert!(!ok, "an unlinked compile must refuse:\n{stderr}");
    assert!(
        stderr.contains("UnauthenticatedImport")
            && stderr.contains("cross-crate proof claim not authenticated"),
        "stderr:\n{stderr}"
    );
}

/// Negative twin: the same client against a REBUILT dependency (same symbol,
/// same signature, different body) is a digest mismatch.
#[test]
fn a_rebuilt_dependency_is_refused_with_digest_mismatch() {
    let dir = tempfile::tempdir().expect("tempdir");
    let dep = dependency();
    let client_path = write(dir.path(), "client", &client(&dep));
    let rebuilt = dependency_with(Ty::I64, 2);
    assert_ne!(rebuilt.stable_digest(), dep.stable_digest());
    let rebuilt_path = write(dir.path(), "dep_rebuilt", &rebuilt);
    let (ok, stderr) = run_linked(dir.path(), &client_path, &[&rebuilt_path], &[]);
    assert!(!ok, "a rebuilt dependency must be refused:\n{stderr}");
    assert!(stderr.contains("--link"), "stderr:\n{stderr}");
    assert!(stderr.contains("DigestMismatch"), "stderr:\n{stderr}");
    assert!(
        !dir.path().join("client.o").exists(),
        "no object on refusal"
    );
}

/// Adversarial: a duplicate import row (the table is content-interned).
#[test]
fn a_duplicate_import_row_is_refused_under_link() {
    let dir = tempfile::tempdir().expect("tempdir");
    let dep = dependency();
    let dep_path = write(dir.path(), "dep", &dep);
    let mut module = client(&dep);
    let row = module.imports[0].clone();
    module.imports.push(row);
    let client_path = write(dir.path(), "client", &module);
    let (ok, stderr) = run_linked(dir.path(), &client_path, &[&dep_path], &[]);
    assert!(!ok, "a duplicate import row must be refused:\n{stderr}");
    assert!(
        stderr.contains("ImportTableNotInterned"),
        "stderr:\n{stderr}"
    );
}

/// Adversarial: the client declares `f(i64)` while the dependency it names
/// defines `f(u64)` — the call edge's signature does not match.
#[test]
fn a_skewed_declaration_signature_is_refused_under_link() {
    let dir = tempfile::tempdir().expect("tempdir");
    let dep = dependency_with(Ty::U64, 1);
    let dep_path = write(dir.path(), "dep", &dep);
    let client_path = write(dir.path(), "client", &client(&dep));
    let (ok, stderr) = run_linked(dir.path(), &client_path, &[&dep_path], &[]);
    assert!(!ok, "a signature skew must be refused:\n{stderr}");
    assert!(stderr.contains("signature mismatch"), "stderr:\n{stderr}");
}

/// Adversarial: an import row nothing cites, with a garbage digest, is still
/// authenticated (and refused) under `--link`.
#[test]
fn an_uncited_import_row_with_a_garbage_digest_is_refused_under_link() {
    let dir = tempfile::tempdir().expect("tempdir");
    let dep = dependency();
    let dep_path = write(dir.path(), "dep", &dep);
    let mut module = client(&dep);
    module
        .intern_import(
            ModuleImport::new("ghost", Module::new("never-supplied").stable_digest())
                .with_producer(Producer::TRust),
        )
        .expect("id space");
    let client_path = write(dir.path(), "client", &module);
    let (ok, stderr) = run_linked(dir.path(), &client_path, &[&dep_path], &[]);
    assert!(
        !ok,
        "an uncited unauthenticated row must be refused:\n{stderr}"
    );
    assert!(stderr.contains("ghost"), "stderr:\n{stderr}");
    assert!(stderr.contains("ImportUnavailable"), "stderr:\n{stderr}");
}

/// [`client`] plus `rsum(v: <4 x i32>) -> i32`, a `vector.reduce` dialect op
/// the backend LEGALIZES (rewrites into the trust-ir lane fold) before the
/// adapter runs, so the module the adapter lowers is not byte-identical to
/// the module `--link` authenticated.
fn client_with_legalized_dialect_op(dep: &Module) -> Module {
    use trust_ir::dialect::vector::{self as vector, ReduceKind};
    use trust_ir::{Block, BlockId, FuncTy, Function, Inst, InstrNode, ValueId};
    let mut m = client(dep);
    let vty = Ty::Vector(Box::new(Ty::I32), 4);
    let ty = m
        .add_func_type(FuncTy {
            params: vec![vty.clone()],
            returns: vec![Ty::I32],
            is_vararg: false,
            abi: None,
        })
        .expect("func type id space");
    let id = FuncId::new(u32::try_from(m.functions.len()).expect("small module"));
    let mut function = Function::new(id, "rsum", ty, BlockId::new(0));
    let mut block = Block::new(BlockId::new(0));
    block.params = vec![(ValueId::new(0), vty.clone())];
    block.body = vec![
        InstrNode::new(Inst::DialectOp(Box::new(vector::reduce(
            vty,
            ValueId::new(0),
            ReduceKind::Add,
        ))))
        .with_result(ValueId::new(1)),
        InstrNode::new(Inst::Return {
            values: vec![ValueId::new(1)],
        }),
    ];
    function.blocks.push(block);
    function.body_gate = fixture_license();
    function.producer = Some(Producer::TRust);
    m.functions.push(function);
    m
}

/// Review (WS7.9): a legitimate linked client whose dialect op the backend
/// legalizes must still compile. The authentication was bound to the
/// caller's module digest and re-checked inside the adapter against the
/// LEGALIZED module, so every such client was refused with
/// `AuthenticatedImportsBoundElsewhere`. Its twin without `--link` is still
/// refused, so the success is the authentication's.
#[test]
fn a_linked_client_whose_dialect_op_is_legalized_compiles() {
    let dir = tempfile::tempdir().expect("tempdir");
    let dep = dependency();
    let dep_path = write(dir.path(), "dep", &dep);
    let client_path = write(
        dir.path(),
        "client",
        &client_with_legalized_dialect_op(&dep),
    );
    let (ok, stderr) = run_linked(dir.path(), &client_path, &[&dep_path], &[]);
    assert!(
        ok,
        "the linked client with a legalized dialect op must compile:\n{stderr}"
    );
    assert!(
        !stderr.contains("AuthenticatedImportsBoundElsewhere"),
        "{stderr}"
    );
    std::fs::remove_file(dir.path().join("client.o")).expect("object written");
    let (ok, stderr) = run(dir.path(), &client_path, &[]);
    assert!(!ok, "without --link it stays refused:\n{stderr}");
    assert!(
        stderr.contains("UnauthenticatedImport")
            && stderr.contains("cross-crate proof claim not authenticated"),
        "stderr:\n{stderr}"
    );
}

/// `--link` is refused by name on the wasm32 lane, never silently dropped.
#[test]
fn link_is_refused_on_the_wasm32_lane() {
    let dir = tempfile::tempdir().expect("tempdir");
    let dep = dependency();
    let dep_path = write(dir.path(), "dep", &dep);
    let client_path = write(dir.path(), "client", &client(&dep));
    let output = Command::new(trust_cg_bin())
        .arg("--target")
        .arg("wasm32")
        .arg("-o")
        .arg(dir.path().join("client.wasm"))
        .arg("--link")
        .arg(&dep_path)
        .arg(&client_path)
        .output()
        .expect("run trust-cg");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(!output.status.success(), "stderr:\n{stderr}");
    assert!(stderr.contains("--link"), "stderr:\n{stderr}");
}
