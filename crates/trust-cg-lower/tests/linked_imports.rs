// trust-cg-lower/tests/linked_imports.rs — the library half of `--link`
// (roadmap WS7.9): `authenticate_linked_imports`, the floor that admits only
// what it authenticated, and the license binding to one root module.
//
// The fixtures mirror trust-cg-cli's `tests/link_imports.rs`: `dep` defines
// `f` with a kernel-certified proved contract, `client` imports `dep` by
// digest, calls `f`, and discharges its own Postcondition about `f` by
// inheriting `dep`'s #0 (`InheritedFromCallee { external: Some(_) }`).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use trust_cg_lower::{
    AdapterError, AuthenticatedImportSet, CodegenLicensePolicy, LinkedImportRefusal,
    UnlicensedBodyPolicy, WeakUndefinedReferencePolicy, authenticate_linked_imports,
    reject_unconsumed_v41_target_neutral_surface_with_imports,
};
use trust_ir::clean_expr_lowering::contract::contract_clean_cic_certificate;
use trust_ir::proof::{
    ObligationKind, ProofCertificate, ProofEvidence, ProofFormula, ProofObligation, ProofStatus,
};
use trust_ir::ty::Ty;
use trust_ir::value::{FuncId, ImportId, ProofId};
use trust_ir::{
    Endianness, ExternRef, FunctionSummary, Module, ModuleImport, Producer, TargetInfo,
};
use trust_ir_build::{ModuleBuilder, validate_module};

fn target() -> TargetInfo {
    TargetInfo {
        triple: "aarch64-apple-darwin".into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: None,
        struct_passing: Default::default(),
    }
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
    let mut mb = ModuleBuilder::new_with_target_info("client", target());
    mb.set_default_producer(Producer::TRust);
    let ft = mb.add_func_type(vec![Ty::I64], vec![Ty::I64]);
    {
        // Body-less declaration of the dependency's `f` (FuncId 0).
        let fb = mb.function("f", ft);
        fb.build();
    }
    {
        let mut fb = mb.function("caller", ft);
        let entry = fb.create_block();
        let x = fb.add_block_param(entry, Ty::I64);
        fb.switch_to_block(entry);
        let r = fb.call(FuncId::new(0), vec![x]);
        fb.ret(vec![r]);
        fb.build();
    }
    let mut m = mb.build().expect("ModuleBuilder::build: test fixture");
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

/// The `skip_import_authentication` knob is process-global, so every test
/// that authenticates holds this lock: the mutation test must never overlap
/// a test that expects the real walk.
static AUTHENTICATION: std::sync::Mutex<()> = std::sync::Mutex::new(());

fn authenticate(
    root: &Module,
    dependency: &Module,
) -> Result<AuthenticatedImportSet, LinkedImportRefusal> {
    let _guard = AUTHENTICATION
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    authenticate_linked_imports(root, std::slice::from_ref(dependency))
}

fn floor(module: &Module, imports: Option<&AuthenticatedImportSet>) -> Result<(), AdapterError> {
    reject_unconsumed_v41_target_neutral_surface_with_imports(
        module,
        WeakUndefinedReferencePolicy::Refuse,
        imports,
    )
}

fn refused_with(refusal: &LinkedImportRefusal, needle: &str) -> bool {
    matches!(refusal, LinkedImportRefusal::Refused { .. }) && refusal.to_string().contains(needle)
}

#[test]
fn an_authenticated_inheritance_is_admitted_and_only_with_the_set() {
    let dep = dependency();
    let client = client(&dep);
    let set = authenticate(&client, &dep)
        .unwrap_or_else(|refusal| panic!("the linked walk must accept the client: {refusal}"));
    assert_eq!(set.root_digest(), &client.stable_digest());
    assert_eq!(set.dependencies().len(), 1);
    assert_eq!(set.dependencies()[0].row, client.imports[0]);
    assert_eq!(
        set.admitted_certificates().iter().collect::<Vec<_>>(),
        [&client.proof_certificates[0].lineage_ref()]
    );
    assert!(floor(&client, Some(&set)).is_ok());
    // Without the set the floor keeps its unconditional refusal.
    assert!(matches!(
        floor(&client, None),
        Err(AdapterError::ExternalEvidenceInheritance { certificate: 0, .. })
    ));
}

#[test]
fn the_negative_twin_a_rebuilt_dependency_is_a_digest_mismatch() {
    let dep = dependency();
    let client = client(&dep);
    let rebuilt = dependency_with(Ty::I64, 2);
    let refusal =
        authenticate(&client, &rebuilt).expect_err("a rebuilt dependency must not authenticate");
    assert!(refused_with(&refusal, "DigestMismatch"), "{refusal}");
    let LinkedImportRefusal::Refused { rows, .. } = &refusal else {
        panic!("{refusal}");
    };
    assert!(
        matches!(
            rows.as_slice(),
            [(0, trust_ir::ImportVerificationError::DigestMismatch { .. })]
        ),
        "{refusal}"
    );
}

#[test]
fn a_skewed_declaration_signature_is_refused() {
    let dep = dependency_with(Ty::U64, 1);
    let client = client(&dep);
    let refusal =
        authenticate(&client, &dep).expect_err("i64 declaration against a u64 definition");
    assert!(refused_with(&refusal, "signature mismatch"), "{refusal}");
}

#[test]
fn a_duplicate_import_row_is_refused() {
    let dep = dependency();
    let mut client = client(&dep);
    let row = client.imports[0].clone();
    client.imports.push(row);
    let refusal = authenticate(&client, &dep).expect_err("a non-interned import table");
    assert!(
        refused_with(&refusal, "ImportTableNotInterned"),
        "{refusal}"
    );
}

#[test]
fn an_uncited_import_row_with_a_garbage_digest_is_refused() {
    let dep = dependency();
    let mut client = client(&dep);
    client
        .intern_import(
            ModuleImport::new("ghost", Module::new("never-supplied").stable_digest())
                .with_producer(Producer::TRust),
        )
        .expect("id space");
    let refusal = authenticate(&client, &dep).expect_err("an uncited row is still authenticated");
    assert!(refused_with(&refusal, "ImportUnavailable"), "{refusal}");
    assert!(refused_with(&refusal, "ghost"), "{refusal}");
}

/// The license carrying `set`. The client is hand-built and its `caller`
/// carries no codegen license (`body_gate: None`), which the default policy
/// refuses (DG-73). What these tests exercise is the import binding, so the
/// policy states the test permit for claim-less bodies explicitly; the binding
/// refusals below are `bind_root`'s, which runs before any body verdict.
fn linked_license(set: AuthenticatedImportSet) -> CodegenLicensePolicy {
    CodegenLicensePolicy::default()
        .with_unlicensed(UnlicensedBodyPolicy::Permit)
        .with_authenticated_imports(set)
}

#[test]
fn a_set_binds_one_root_module_through_the_license() {
    let dep = dependency();
    let client = client(&dep);
    let set = authenticate(&client, &dep).expect("linked");
    let license = linked_license(set);
    let verdict = license.enforce_module(&client);
    assert!(verdict.is_ok(), "{verdict:?}");
    assert!(
        license.canonical_identity().contains(";linked="),
        "{}",
        license.canonical_identity()
    );
    let mut other = client.clone();
    other.name = "client_renamed".into();
    assert!(matches!(
        license.enforce_module(&other),
        Err(AdapterError::AuthenticatedImportsBoundElsewhere { .. })
    ));
}

#[test]
fn ingestion_uses_only_the_exact_authenticated_linked_context() {
    use trust_cg_lower::ingest::admit_module;

    let dep = dependency();
    let client = client(&dep);
    let set = authenticate(&client, &dep).expect("linked");
    let unlinked = CodegenLicensePolicy::default().with_unlicensed(UnlicensedBodyPolicy::Permit);
    assert!(admit_module(&client, &unlinked, &[]).is_err());
    let linked = linked_license(set);
    let admitted =
        admit_module(&client, &linked, &[]).expect("authenticated inheritance reaches ingestion");
    trust_cg_lower::translate_admitted_module_for_arch_with_tls_and_validation(
        &admitted,
        trust_cg_lower::GuardCarrierArch::AArch64,
        trust_cg_lower::TlsDialect::MachOTlv,
        false,
    )
    .expect("the adapter keeps the admitted linked context");

    let mut forged = client.clone();
    forged.proof_obligations[0].formula = Some(ProofFormula::smtlib2("(= 1 2)", "Bool"));
    assert!(matches!(
        admit_module(&forged, &linked, &[]),
        Err(AdapterError::AuthenticatedImportsBoundElsewhere { .. })
    ));
    let mut renamed = client.clone();
    renamed.name = "another_client".into();
    assert!(matches!(
        admit_module(&renamed, &linked, &[]),
        Err(AdapterError::AuthenticatedImportsBoundElsewhere { .. })
    ));

    let mut malformed = client.clone();
    malformed.functions.push(malformed.functions[0].clone());
    let rebound = linked
        .for_backend_rewrite(&client, &malformed)
        .expect("a backend rewrite can retain the proof surface but be structurally invalid");
    assert!(matches!(
        admit_module(&malformed, &rebound, &[]),
        Err(AdapterError::InvalidTrustIrModule(_))
    ));
}

/// The floor's second clause: a look-alike certificate whose `ImportId`
/// names a DIFFERENT row than the authenticated one is not admitted, even
/// though its lineage reference matches.
#[test]
fn the_floor_admits_only_the_authenticated_row() {
    let dep = dependency();
    let client = client(&dep);
    let set = authenticate(&client, &dep).expect("linked");
    let mut swapped = client.clone();
    swapped.imports[0] = ModuleImport::new("dep", Module::new("elsewhere").stable_digest())
        .with_producer(Producer::TRust);
    assert_eq!(
        swapped.proof_certificates[0].lineage_ref(),
        client.proof_certificates[0].lineage_ref()
    );
    assert!(matches!(
        floor(&swapped, Some(&set)),
        Err(AdapterError::ExternalEvidenceInheritance { .. })
    ));
}

/// Review (WS7.9): `lineage_ref` digests the certificate alone, so a module
/// that kept the inheritance certificate byte-for-byte but REWROTE the claim
/// it discharges (`ensures (= 1 2)`, which the dependency never proved) has
/// the same lineage reference and the same import row. A set authenticated
/// for the honest client must not admit it at the floor — the linked walk
/// itself refuses it, which is what makes it a false claim.
#[test]
fn the_floor_refuses_a_lookalike_that_rewrote_the_inherited_claim() {
    let dep = dependency();
    let client = client(&dep);
    let set = authenticate(&client, &dep).expect("linked");
    let mut forged = client.clone();
    forged.proof_obligations[0].formula = Some(ProofFormula::smtlib2("(= 1 2)", "Bool"));
    forged.proof_obligations[0].description = "inherited ensures (= 1 2)".to_string();
    assert_eq!(
        forged.proof_certificates[0].lineage_ref(),
        client.proof_certificates[0].lineage_ref()
    );
    assert_eq!(forged.imports, client.imports);
    assert!(
        authenticate(&forged, &dep).is_err(),
        "the rewritten claim is false: the linked walk refuses it"
    );
    assert!(matches!(
        floor(&forged, Some(&set)),
        Err(AdapterError::ExternalEvidenceInheritance { certificate: 0, .. })
    ));
}

/// Review (WS7.9): the same look-alike with the inheritance's local callee
/// renamed — the evidence names `FuncId` 0, which is now a different symbol.
#[test]
fn the_floor_refuses_a_lookalike_whose_callee_is_another_symbol() {
    let dep = dependency();
    let client = client(&dep);
    let set = authenticate(&client, &dep).expect("linked");
    let mut forged = client.clone();
    forged.functions[0].name = "g".to_string();
    assert_eq!(
        forged.proof_certificates[0].lineage_ref(),
        client.proof_certificates[0].lineage_ref()
    );
    assert!(matches!(
        floor(&forged, Some(&set)),
        Err(AdapterError::ExternalEvidenceInheritance { certificate: 0, .. })
    ));
}

/// Review (WS7.9): the adapter lowers the backend's DIALECT-LEGALIZED module,
/// not the caller's, so a set bound to the caller's digest refused every
/// linked module whose dialect ops were rewritten. The set moves onto a
/// rewrite that keeps the name, the import table and both proof tables
/// (here: a body edit stands in for a legalization rewrite), and nowhere
/// else.
#[test]
fn a_set_moves_onto_a_backend_rewrite_that_keeps_the_proof_surface() {
    let dep = dependency();
    let client = client(&dep);
    let set = authenticate(&client, &dep).expect("linked");
    let license = linked_license(set);

    let mut rewritten = client.clone();
    rewritten.functions[1].blocks[0].body.insert(
        0,
        trust_ir::InstrNode::new(trust_ir::Inst::Const {
            ty: Ty::I64,
            value: trust_ir::Constant::Int(7),
        })
        .with_result(trust_ir::ValueId::new(900)),
    );
    assert_ne!(rewritten.stable_digest(), client.stable_digest());
    assert!(
        matches!(
            license.enforce_module(&rewritten),
            Err(AdapterError::AuthenticatedImportsBoundElsewhere { .. })
        ),
        "the caller's binding alone refuses the rewrite"
    );
    let moved = license
        .for_backend_rewrite(&client, &rewritten)
        .expect("a rewrite keeping every admission table moves the set");
    let verdict = moved.enforce_module(&rewritten);
    assert!(verdict.is_ok(), "{verdict:?}");
    assert!(
        matches!(
            moved.enforce_module(&client),
            Err(AdapterError::AuthenticatedImportsBoundElsewhere { .. })
        ),
        "a moved set binds the rewrite alone"
    );
    let imports = moved.authenticated_imports().expect("set kept");
    assert!(floor(&rewritten, Some(imports)).is_ok());
    // Identity: the same module needs no move and keeps the root.
    let same = license
        .for_backend_rewrite(&client, &client)
        .expect("identity");
    assert_eq!(same, license);

    // A rewrite that changed a table an admission reads is refused.
    let mut retabled = rewritten.clone();
    retabled.proof_obligations[0].description = "changed".to_string();
    let error = license
        .for_backend_rewrite(&client, &retabled)
        .expect_err("a rewrite that changed the proof obligations");
    assert!(
        matches!(&error, AdapterError::AuthenticatedImportsBoundElsewhere { detail, .. }
            if detail.contains("proof obligations")),
        "{error}"
    );
    // And a "source" that is not the authenticated root moves nothing.
    let mut other = client.clone();
    other.name = "client_renamed".into();
    assert!(matches!(
        license.for_backend_rewrite(&other, &rewritten),
        Err(AdapterError::AuthenticatedImportsBoundElsewhere { .. })
    ));
}

/// Mutation control: with trust-ir's linked walk (and so every
/// `verify_import`) skipped, the negative twin IS admitted — the refusal
/// above comes from the authentication, not from anything else.
#[cfg(feature = "mutation-knobs")]
#[test]
fn mutation_skipping_authentication_admits_the_negative_twin() {
    use trust_cg_lower::mutation_knobs::set_skip_import_authentication;
    let dep = dependency();
    let client = client(&dep);
    let rebuilt = dependency_with(Ty::I64, 2);
    let result = {
        let _guard = AUTHENTICATION
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        set_skip_import_authentication(true);
        let result = authenticate_linked_imports(&client, std::slice::from_ref(&rebuilt));
        set_skip_import_authentication(false);
        result
    };
    let set = result.expect("with authentication skipped the rebuilt dependency is accepted");
    assert!(floor(&client, Some(&set)).is_ok());
}

#[test]
fn default_build_has_no_mutation_knobs() {
    assert_eq!(
        trust_cg_lower::MUTATION_KNOBS,
        cfg!(feature = "mutation-knobs")
    );
}
