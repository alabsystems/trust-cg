// trust-cg-lower/tests/codegen_license_evidence.rs — roadmap WS7.5(b): the
// codegen license `Gated{"clean-kernel-tv"}` is bound to EVIDENCE on every
// adapter entry, not to a string.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Closes, on the trust-cg consumer side, finding F-006 (rows
//! `consumer-trust-cg/04-gate-authority-binding` and `verify.c05.L1` part (b))
//! and adds the consumer ratchet row `consumer.cg.kernel_tv_license_bound`.
//!
//! Until WS7.5 `CodegenLicensePolicy::verdict` admitted a recognized authority
//! by byte-exact string equality alone, so any producer could wear
//! `Gated{"clean-kernel-tv"}` with no certificate at all. Now trust-ir's own
//! license layer (`trust_ir_build::codegen_license_errors`, WS1.5) decides the
//! evidence, and trust-cg refuses by NAME:
//!
//! * `AdapterError::GatedWithoutEvidence` — the evidence-bound authority is
//!   worn without exactly one `Certified` TranslationValidation row scoped to
//!   the function whose `clean_backend_tv` certificate was kernel-REPLAYED
//!   against the current body;
//! * `AdapterError::GatedFunctionRefuted` — a `Failed` TranslationValidation
//!   row about the body revokes any `Gated` license.
//!
//! Fixtures:
//!
//! * POSITIVE (real producer output): trust-ir's `lean_library_envelope`
//!   conformance fixture, vendored byte-identical at the trust-ir pin
//!   (`tests/fixtures/trust_ir_binary_container/conformance/`, see
//!   `SOURCE.txt`): the Fragment-2 `addmul(a, b) = a*b + a` a Clean producer
//!   emits, `Gated{"clean-kernel-tv"}`, with its `Certified` TranslationValidation
//!   row and `clean_backend_tv` CleanCic certificate.
//! * POSITIVE (minted here): `add7(x) = x + 7`, certified with trust-ir's
//!   public identity minter `certify_identity_lineage_rung` — the fixture the
//!   "body edited after mint" twin mutates.
//! * NEGATIVE TWIN: the envelope with its obligations and certificates
//!   removed — exactly the `verify.c05.L1` baseline shape, which trust-cg
//!   compiled before WS7.5.
//!
//! Every verdict is taken on EVERY adapter entry (the `verdicts` harness), so
//! no path can become a bypass. Mutation-enabled builds retain the same
//! mandatory evidence floor; their negative twins must remain refused.

use trust_cg_lower::adapter::AdapterError;
use trust_cg_lower::{
    CLEAN_KERNEL_TV_AUTHORITY, CodegenLicensePolicy, GuardCarrierArch, ObjectAccessModel,
    TlsDialect, UnlicensedBodyPolicy, prepare_module_for_lir, translate_body_template,
    translate_function, translate_function_with_license, translate_inline_only_bodies,
    translate_module, translate_module_for_arch_with_tls_and_stats_and_validation_with_license,
    translate_module_for_arch_with_tls_and_stats_with_license,
    translate_module_for_arch_with_tls_and_validation_with_license,
    translate_module_for_arch_with_tls_with_license,
    translate_module_strict_for_arch_with_tls_and_validation_with_license,
    translate_validated_module_strict_for_arch_with_tls_and_validation_with_license,
    validate_codegen_metadata, validate_function_codegen_metadata,
};
use trust_ir::proof::{
    ObligationKind, ProofEvidence, ProofLineageId, ProofObligation, ProofStatus, ProofTransform,
    ProofTransformStage,
};
use trust_ir::{
    BinOp, BodyGate, FuncId, GateEvidence, Inst, Linkage, Module, Producer, ProofId, Ty,
};
use trust_ir_build::{ModuleBuilder, certify_identity_lineage_rung};

/// Serialize the producer-envelope and evidence exercises across entries.
static SERIAL: std::sync::Mutex<()> = std::sync::Mutex::new(());

fn serial() -> std::sync::MutexGuard<'static, ()> {
    SERIAL
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner)
}

/// The vendored Lean-envelope conformance fixture (bare TRUST_IR binary).
const ENVELOPE: &str = concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/../../tests/fixtures/trust_ir_binary_container/conformance/lean_library_envelope.tmbc"
);

/// The envelope as decoded, required VALID and kernel-certified at the pinned
/// trust-ir: a finding about the consumer is only meaningful on input the
/// format itself admits for codegen.
fn envelope() -> Module {
    let bytes = std::fs::read(ENVELOPE).unwrap_or_else(|e| panic!("read {ENVELOPE}: {e}"));
    let module = trust_ir::binary::deserialize_module(&bytes).expect("decode the envelope");
    assert_eq!(trust_ir_build::validate_module(&module), []);
    assert_eq!(trust_ir_build::validate_module_for_codegen(&module), []);
    assert_eq!(
        trust_ir_build::validate_module_report(&module)
            .replayed_certificate_refs()
            .map(|refs| refs.len()),
        Some(1),
        "the envelope's TV certificate is kernel-replayed at the pin"
    );
    module
}

fn addmul(module: &Module) -> FuncId {
    module.function_by_name("addmul").expect("addmul").id
}

/// The index of the envelope's TranslationValidation obligation.
fn tv_row(module: &Module) -> usize {
    module
        .proof_obligations
        .iter()
        .position(|o| o.kind == ObligationKind::TranslationValidation)
        .expect("the envelope carries its TV row")
}

/// `module` with `func`'s `clean-kernel-tv` license carrying the trust-ir v61
/// `GateEvidence` that holds for it: the `Certified` TranslationValidation
/// row scoped to `func` and the digest of the body as it stands. Since v61 an
/// evidence-bound license with no `GateEvidence` is `UnevidencedGate` at
/// admission, so a fixture that must LOWER binds it; the negative fixtures
/// keep the evidence-free license as decoded or built, whose refusal is named
/// by trust-ir's certificate rule first (`GatedWithoutEvidence`).
fn bind_gate_evidence(mut module: Module, func: FuncId) -> Module {
    let obligation = module
        .proof_obligations
        .iter()
        .find(|o| o.kind == ObligationKind::TranslationValidation && o.function == Some(func))
        .expect("the TV row scoped to the function")
        .id;
    let body_digest = module
        .function_body_digest(func)
        .expect("the licensed body has a digest");
    let function = module
        .functions
        .iter_mut()
        .find(|f| f.id == func)
        .expect("the licensed function");
    function.body_gate = Some(BodyGate::Gated {
        authority: CLEAN_KERNEL_TV_AUTHORITY.to_string(),
        evidence: Some(GateEvidence {
            obligation,
            body_digest,
        }),
    });
    module
}

/// `add7(x: u64) -> u64 { x + 7 }`, a Clean body stamped
/// `Gated{"clean-kernel-tv"}` and certified by trust-ir's public minter.
fn minted_add7() -> Module {
    let mut mb = ModuleBuilder::new("ws7_5_minted");
    mb.set_default_producer(Producer::Clean);
    let sig = mb.add_func_type(vec![Ty::U64], vec![Ty::U64]);
    let mut fb = mb.function("add7", sig);
    fb.set_body_gate(BodyGate::gated(CLEAN_KERNEL_TV_AUTHORITY));
    let entry = fb.create_block();
    let x = fb.add_block_param(entry, Ty::U64);
    fb.switch_to_block(entry);
    let seven = fb.uconst(Ty::U64, 7);
    let sum = fb.add(Ty::U64, x, seven);
    fb.ret(vec![sum]);
    let func = fb.build();
    let mut module = mb.build().expect("ModuleBuilder::build: test fixture");
    let (_node, obligation, certificate) = certify_identity_lineage_rung(
        &module,
        ProofLineageId::new(0),
        ProofId::new(0),
        ProofTransform::new(
            ProofTransformStage::Frontend,
            "identity",
            "trust-cg-ws7.5",
            "1.0.0",
        ),
        func,
    )
    .expect("add7 is in the clean_backend_tv fragment");
    module.proof_obligations.push(obligation);
    module.proof_certificates.push(certificate);
    assert_eq!(trust_ir_build::validate_module_for_codegen(&module), []);
    module
}

/// Rewrite the one `BinOp` `from` of `func` to `to` (a body edit AFTER the
/// certificate was minted).
fn edit_binop(module: &mut Module, func: FuncId, from: BinOp, to: BinOp) {
    let function = module.function_by_id_mut(func).expect("function");
    let mut hits = 0;
    for node in function.blocks.iter_mut().flat_map(|b| b.body.iter_mut()) {
        if let Inst::BinOp { op, .. } = &mut node.inst
            && *op == from
        {
            *op = to;
            hits += 1;
        }
    }
    assert_eq!(hits, 1, "the edit hits exactly one instruction");
}

/// Every adapter entry's verdict on `module` under `policy`, exactly as
/// `tests/v41_codegen_license.rs` drives them, plus the default-policy
/// entries and the metadata entries.
fn verdicts(
    module: &Module,
    policy: &CodegenLicensePolicy,
) -> Vec<(&'static str, Option<AdapterError>)> {
    let arch = GuardCarrierArch::AArch64;
    let tls = TlsDialect::default();
    let first = &module.functions[0];
    let mut out = vec![
        (
            "with_tls",
            translate_module_for_arch_with_tls_with_license(module, arch, tls, policy).err(),
        ),
        (
            "with_tls_and_validation",
            translate_module_for_arch_with_tls_and_validation_with_license(
                module, arch, tls, policy,
            )
            .err(),
        ),
        (
            "with_tls_and_stats",
            translate_module_for_arch_with_tls_and_stats_with_license(module, arch, tls, policy)
                .err(),
        ),
        (
            "with_tls_and_stats_and_validation",
            translate_module_for_arch_with_tls_and_stats_and_validation_with_license(
                module, arch, tls, policy,
            )
            .err(),
        ),
        (
            "strict",
            translate_module_strict_for_arch_with_tls_and_validation_with_license(
                module, arch, tls, policy,
            )
            .err(),
        ),
        (
            "single_function",
            translate_function_with_license(first, module, policy).err(),
        ),
        ("policy_enforce_module", policy.enforce_module(module).err()),
        ("policy_verdict", policy.verdict(module, first.id).err()),
    ];
    match prepare_module_for_lir(module, arch) {
        Ok(prepared) => out.push((
            "prepared",
            prepared
                .translate_with_tls_and_validation_with_license(tls, policy)
                .err(),
        )),
        Err(error) => out.push(("prepared", Some(error))),
    }
    // The validated strict entry reuses a successful full validation report;
    // a module the structural validator rejects has no such leg.
    let report = trust_ir_build::validate_module_report(module);
    if report.is_ok() {
        out.push((
            "validated_strict",
            translate_validated_module_strict_for_arch_with_tls_and_validation_with_license(
                &report, arch, tls, policy,
            )
            .err(),
        ));
    }
    if *policy == CodegenLicensePolicy::default() {
        out.push(("default_translate_module", translate_module(module).err()));
        out.push((
            "default_translate_function",
            translate_function(first, module).err(),
        ));
        out.push((
            "default_metadata_module",
            validate_codegen_metadata(module).err(),
        ));
        out.push((
            "default_metadata_function",
            validate_function_codegen_metadata(first, module).err(),
        ));
    }
    out
}

fn assert_all_permitted(module: &Module, policy: &CodegenLicensePolicy, what: &str) {
    for (entry, verdict) in verdicts(module, policy) {
        assert!(
            verdict.is_none(),
            "{what}: entry `{entry}` must permit: {verdict:?}"
        );
    }
}

fn assert_all_refused(
    module: &Module,
    policy: &CodegenLicensePolicy,
    what: &str,
    check: impl Fn(&AdapterError) -> bool,
) {
    for (entry, verdict) in verdicts(module, policy) {
        match verdict {
            Some(error) => assert!(
                check(&error),
                "{what}: entry `{entry}`: wrong refusal {error:?}"
            ),
            None => panic!("{what}: entry `{entry}` must refuse"),
        }
    }
}

/// `GatedWithoutEvidence` for `function`, whose `missing` contains `needle`.
fn without_evidence(function: &str, needle: &str) -> impl Fn(&AdapterError) -> bool {
    move |error| {
        matches!(
            error,
            AdapterError::GatedWithoutEvidence { function: f, authority, missing }
                if f == function
                    && authority == CLEAN_KERNEL_TV_AUTHORITY
                    && missing.contains(needle)
        )
    }
}

// ---------------------------------------------------------------------------
// Positive and negative twin (row consumer.cg.kernel_tv_license_bound)
// ---------------------------------------------------------------------------

/// Row `consumer.cg.kernel_tv_license_bound` (positive): the real Clean
/// `addmul`, licensed `Gated{"clean-kernel-tv"}` and carrying its kernel-
/// replayed TV certificate, lowers on every entry under the DEFAULT policy
/// (which refuses claim-less bodies, so nothing here is admitted by a Permit).
#[test]
fn consumer_cg_kernel_tv_license_bound_positive_envelope_lowers_on_every_entry() {
    let _serial = serial();
    let module = envelope();
    let addmul = addmul(&module);
    let module = bind_gate_evidence(module, addmul);
    assert_all_permitted(&module, &CodegenLicensePolicy::default(), "envelope");
}

/// The minted positive lowers the same way.
#[test]
fn consumer_cg_kernel_tv_license_bound_positive_minted_certificate_lowers() {
    let _serial = serial();
    let module = minted_add7();
    let add7 = module.function_by_name("add7").expect("add7").id;
    let module = bind_gate_evidence(module, add7);
    assert_all_permitted(&module, &CodegenLicensePolicy::default(), "minted add7");
}

/// Row `consumer.cg.kernel_tv_license_bound` (negative twin) = row
/// `verify.c05.L1` part (b): the same module with ZERO obligations and ZERO
/// certificates is refused on every entry, by name, under every policy —
/// recognition never stands in for the evidence.
#[test]
fn consumer_cg_kernel_tv_license_bound_negative_twin_without_evidence_is_refused() {
    let _serial = serial();
    let mut module = envelope();
    module.proof_obligations.clear();
    module.proof_certificates.clear();
    assert_eq!(
        trust_ir_build::validate_module(&module),
        [],
        "the twin is structurally valid: only the license refuses it"
    );
    for policy in [
        CodegenLicensePolicy::default(),
        CodegenLicensePolicy::recognizing_nothing(),
        CodegenLicensePolicy::default().with_recognized_authority("someone-elses-gate"),
    ] {
        assert_all_refused(
            &module,
            &policy,
            "no evidence",
            without_evidence("addmul", "no TranslationValidation obligation"),
        );
    }
}

// ---------------------------------------------------------------------------
// Ported rows
// ---------------------------------------------------------------------------

/// Row `consumer-trust-cg/04-gate-authority-binding` (F-006): "A positive
/// license must be bindable to checkable evidence for THIS function ... so
/// that Gated{authority} is not a free string." The row's test idea verbatim:
/// a builder module whose function wears `Gated{"clean-kernel-tv"}` with NO
/// TranslationValidation obligation or certificate scoped to it. Before WS7.5
/// trust-cg accepted it (`codegen_license.rs` checked the string only); every
/// entry now refuses it as `GatedWithoutEvidence`.
#[test]
fn consumer_trust_cg_04_gate_authority_binding() {
    let _serial = serial();
    let mut mb = ModuleBuilder::new("consumer_trust_cg_04");
    mb.set_default_producer(Producer::Clean);
    let sig = mb.add_func_type(vec![Ty::U64], vec![Ty::U64]);
    let mut fb = mb.function("f", sig);
    fb.set_body_gate(BodyGate::gated(CLEAN_KERNEL_TV_AUTHORITY));
    let entry = fb.create_block();
    let x = fb.add_block_param(entry, Ty::U64);
    fb.switch_to_block(entry);
    fb.ret(vec![x]);
    fb.build();
    let module = mb.build().expect("ModuleBuilder::build: test fixture");
    assert_eq!(trust_ir_build::validate_module(&module), []);
    assert_all_refused(
        &module,
        &CodegenLicensePolicy::default(),
        "consumer-trust-cg/04",
        without_evidence("f", "no TranslationValidation obligation"),
    );
}

/// Row `verify.c05.L1` part (b) (F-006), ported from the proof program's
/// `verify/c05_gate_license_unbound` baseline: one Clean body
/// `clean_f() -> u64 { load @G + 2 }`, `Gated{"clean-kernel-tv"}`, ZERO
/// obligations and certificates. trust-ir refuses it for codegen since WS1.5;
/// trust-cg compiled it until WS7.5 and now refuses it on every entry, by
/// name.
#[test]
fn verify_c05_l1_kernel_tv_license_without_certificate_is_refused_by_trust_cg() {
    let _serial = serial();
    use trust_ir::value::GlobalId;
    use trust_ir::{Constant, Global, Linkage, Visibility};
    let mut mb = ModuleBuilder::new("c05_lic");
    mb.add_global(Global {
        name: "G".into(),
        ty: Ty::U64,
        mutable: false,
        initializer: Some(Constant::Int(40)),
        linkage: Linkage::Internal,
        tls: None,
        align: None,
        section: None,
        visibility: Visibility::Default,
        retained: false,
    });
    let sig = mb.add_func_type(vec![], vec![Ty::U64]);
    let mut fb = mb.function("clean_f", sig);
    fb.set_producer(Producer::Clean);
    fb.set_body_gate(BodyGate::gated(CLEAN_KERNEL_TV_AUTHORITY));
    fb.set_display_path("Demo.cleanF");
    let bb = fb.create_block();
    fb.switch_to_block(bb);
    let p = fb.global_addr(GlobalId::new(0));
    let v = fb.load(Ty::U64, p);
    let two = fb.uconst(Ty::U64, 2);
    let r = fb.add(Ty::U64, v, two);
    fb.ret(vec![r]);
    fb.build();
    let module = mb.build().expect("ModuleBuilder::build: test fixture");
    assert!(module.proof_obligations.is_empty() && module.proof_certificates.is_empty());
    assert_eq!(trust_ir_build::validate_module(&module), []);
    assert_all_refused(
        &module,
        &CodegenLicensePolicy::default(),
        "verify.c05.L1",
        without_evidence("clean_f", "no TranslationValidation obligation"),
    );
}

// ---------------------------------------------------------------------------
// Adversarials: each is refused on every entry by its SPECIFIC name.
// ---------------------------------------------------------------------------

/// A `Failed` TranslationValidation row about the body REVOKES the license
/// (`GatedFunctionRefuted`), whatever the certificate says.
#[test]
fn a_failed_tv_row_revokes_the_license() {
    let _serial = serial();
    let mut module = envelope();
    let row = tv_row(&module);
    module.proof_obligations[row].status = ProofStatus::Failed;
    let obligation = module.proof_obligations[row].id.index();
    assert_all_refused(
        &module,
        &CodegenLicensePolicy::default(),
        "Failed TV",
        |error| {
            matches!(
                error,
                AdapterError::GatedFunctionRefuted { function, obligation: o }
                    if function == "addmul" && *o == obligation
            )
        },
    );
}

/// A `Pending` TV row is not the evidence the authority names.
#[test]
fn a_pending_tv_row_is_not_evidence() {
    let _serial = serial();
    let mut module = envelope();
    let row = tv_row(&module);
    module.proof_obligations[row].status = ProofStatus::Pending;
    assert_all_refused(
        &module,
        &CodegenLicensePolicy::default(),
        "Pending TV",
        without_evidence("addmul", "not `certified`"),
    );
}

/// A second, `Pending` TV row beside the `Certified` one makes the license
/// ambiguous: a license cites exactly one TV row.
#[test]
fn a_second_pending_tv_row_beside_the_certified_one_is_ambiguous() {
    let _serial = serial();
    let mut module = envelope();
    let func = addmul(&module);
    let next = module
        .proof_obligations
        .iter()
        .map(|o| o.id.index())
        .max()
        .expect("rows")
        + 1;
    module.proof_obligations.push(
        ProofObligation::new(
            ProofId::new(next),
            ObligationKind::TranslationValidation,
            ProofStatus::Pending,
            "a second TV claim about addmul",
        )
        .with_function(func),
    );
    assert_all_refused(
        &module,
        &CodegenLicensePolicy::default(),
        "second TV row",
        without_evidence("addmul", "ambiguous"),
    );
}

/// A corrupted certificate term fails the in-process kernel re-check, so the
/// certificate is not replayed and the license has no evidence.
#[test]
fn a_corrupted_certificate_term_is_not_evidence() {
    let _serial = serial();
    let mut module = envelope();
    let ProofEvidence::CleanCic { term, .. } = &mut module.proof_certificates[0].evidence else {
        panic!("the envelope's certificate is CleanCic");
    };
    let last = term.len() - 1;
    term[last] ^= 0xff;
    assert_ne!(
        trust_ir_build::validate_module(&module),
        [],
        "the kernel refuses the corrupted term"
    );
    assert_all_refused(
        &module,
        &CodegenLicensePolicy::default(),
        "corrupted term",
        without_evidence("addmul", "not kernel-replayed"),
    );
}

/// The TV row scoped to ANOTHER function licenses nothing about this one.
#[test]
fn a_tv_row_scoped_to_another_function_is_not_this_bodys_evidence() {
    let _serial = serial();
    let mut module = envelope();
    let sig = module.functions[0].ty;
    let mut other =
        trust_ir::Function::new(FuncId::new(1), "other", sig, trust_ir::BlockId::new(0));
    other.body_gate = Some(BodyGate::Ungated);
    // A declaration: no body, so it is not a codegen subject itself.
    module.functions.push(other);
    let row = tv_row(&module);
    module.proof_obligations[row].function = Some(FuncId::new(1));
    assert_all_refused(
        &module,
        &CodegenLicensePolicy::default(),
        "TV row scoped elsewhere",
        without_evidence("addmul", "no TranslationValidation obligation"),
    );
}

/// A case/space variant of the authority is a DIFFERENT, unbound authority:
/// not evidence-bound (so trust-ir asks nothing of it) and not recognized, so
/// it is refused as `UnrecognizedGateAuthority` — never admitted as the real
/// one.
#[test]
fn a_case_or_space_variant_of_the_authority_is_unrecognized() {
    let _serial = serial();
    for authority in ["CLEAN-KERNEL-TV ", "clean-kernel-tv ", "Clean-Kernel-TV"] {
        let mut module = envelope();
        module.functions[0].body_gate = Some(BodyGate::gated(authority));
        assert_all_refused(
            &module,
            &CodegenLicensePolicy::default(),
            authority,
            |error| {
                matches!(
                    error,
                    AdapterError::UnrecognizedGateAuthority { function, authority: a }
                        if function == "addmul" && a == authority
                )
            },
        );
    }
}

/// The body edited AFTER the certificate was minted keeps its `body_gate`
/// but loses its license: the kernel re-derives the emitted side from the
/// CURRENT body, so the certificate no longer replays. Both the envelope
/// (`a*b + a` -> `a+b + a`) and the minted `add7` (`x + 7` -> `x * 7`).
#[test]
fn a_body_edited_after_mint_loses_its_license() {
    let _serial = serial();
    let mut module = envelope();
    let func = addmul(&module);
    edit_binop(&mut module, func, BinOp::Mul, BinOp::Add);
    assert_all_refused(
        &module,
        &CodegenLicensePolicy::default(),
        "envelope edited after mint",
        without_evidence("addmul", "not kernel-replayed"),
    );

    let mut module = minted_add7();
    let func = module.function_by_name("add7").expect("add7").id;
    edit_binop(&mut module, func, BinOp::Add, BinOp::Mul);
    assert_all_refused(
        &module,
        &CodegenLicensePolicy::default(),
        "add7 edited after mint",
        without_evidence("add7", "not kernel-replayed"),
    );
}

// ---------------------------------------------------------------------------
// Review adversarials (WS7.5 review): the rest of the rule, by its own names.
// ---------------------------------------------------------------------------

/// The next free obligation id of `module`.
fn next_obligation_id(module: &Module) -> u32 {
    module
        .proof_obligations
        .iter()
        .map(|o| o.id.index() + 1)
        .max()
        .unwrap_or(0)
}

/// Revocation is not only a TV row: a `Failed` Postcondition or Precondition
/// row scoped to the body revokes its license too (roadmap WS7.5(a): "No
/// `Failed` TranslationValidation, Precondition or Postcondition row may be
/// scoped to F"), refused by that row's id — the certificate beside it is
/// intact and replays, so the refusal cannot be the evidence rule's.
#[test]
fn a_failed_contract_row_revokes_the_license() {
    let _serial = serial();
    for kind in [ObligationKind::Postcondition, ObligationKind::Precondition] {
        let mut module = envelope();
        let func = addmul(&module);
        let id = next_obligation_id(&module);
        module.proof_obligations.push(
            ProofObligation::new(
                ProofId::new(id),
                kind.clone(),
                ProofStatus::Failed,
                "a refuted contract clause about addmul",
            )
            .with_function(func),
        );
        assert_all_refused(
            &module,
            &CodegenLicensePolicy::default(),
            "Failed contract row",
            |error| {
                matches!(
                    error,
                    AdapterError::GatedFunctionRefuted { function, obligation }
                        if function == "addmul" && *obligation == id
                )
            },
        );
    }
}

/// A `Failed` TV row that names the body only through its IR `site` (no
/// `function` scope) is a claim about that body all the same, and revokes
/// its license by that row's id.
#[test]
fn a_site_only_failed_tv_row_revokes_the_license() {
    let _serial = serial();
    let mut module = envelope();
    let func = addmul(&module);
    let block = module.function_by_id_mut(func).expect("addmul").blocks[0].id;
    let id = next_obligation_id(&module);
    let mut row = ProofObligation::new(
        ProofId::new(id),
        ObligationKind::TranslationValidation,
        ProofStatus::Failed,
        "a refuted TV claim naming addmul by site only",
    );
    row.site = Some(trust_ir::proof::ObligationSite::new(func, block, 0));
    assert_eq!(row.function, None);
    module.proof_obligations.push(row);
    assert_all_refused(
        &module,
        &CodegenLicensePolicy::default(),
        "site-only Failed TV",
        |error| {
            matches!(
                error,
                AdapterError::GatedFunctionRefuted { function, obligation }
                    if function == "addmul" && *obligation == id
            )
        },
    );
}

/// A `CleanCic` certificate re-anchored to ANOTHER kernel anchor is not the
/// `clean_backend_tv` evidence the authority names (the final-critic
/// addition to WS7.5(a)): refused as `GatedWithoutEvidence`, never admitted
/// because the row is still `Certified`.
#[test]
fn a_certificate_under_another_kernel_anchor_is_not_evidence() {
    let _serial = serial();
    let mut module = envelope();
    let ProofEvidence::CleanCic {
        kernel_recheck: Some(recheck),
        ..
    } = &mut module.proof_certificates[0].evidence
    else {
        panic!("the envelope's certificate carries a kernel recheck directive");
    };
    assert_eq!(
        recheck.anchor,
        trust_ir::proof::KERNEL_ANCHOR_CLEAN_BACKEND_TV
    );
    recheck.anchor = trust_ir::proof::KERNEL_ANCHOR_TRUST_IR_CONTRACT.to_string();
    let row = tv_row(&module);
    assert_eq!(module.proof_obligations[row].status, ProofStatus::Certified);
    assert_all_refused(
        &module,
        &CodegenLicensePolicy::default(),
        "re-anchored certificate",
        without_evidence("addmul", "clean_backend_tv kernel anchor"),
    );
}

/// Evidence is necessary, never sufficient: the certified envelope, its
/// license carrying v61 `GateEvidence` that holds, under a
/// policy that recognizes NO authority is refused as
/// `UnrecognizedGateAuthority` on every entry — the certificate does not
/// stand in for the consumer's recognition either.
#[test]
fn certified_evidence_does_not_stand_in_for_recognition() {
    let _serial = serial();
    let module = envelope();
    let addmul = addmul(&module);
    let module = bind_gate_evidence(module, addmul);
    assert_all_refused(
        &module,
        &CodegenLicensePolicy::recognizing_nothing(),
        "certified, unrecognized",
        |error| {
            matches!(
                error,
                AdapterError::UnrecognizedGateAuthority { function, authority }
                    if function == "addmul" && authority == CLEAN_KERNEL_TV_AUTHORITY
            )
        },
    );
}

/// trust-ir attributes its license findings by `FuncId`, and so does this
/// backend. A second body that REUSES the certified `addmul`'s id (edited,
/// renamed, same `Gated{"clean-kernel-tv"}`) must not borrow its
/// certificate, whichever of the two comes first in the module and whether
/// or not its body differs: every entry refuses the module, and the policy's
/// own `enforce_module` / `verdict` refuse it as an ambiguous id — never
/// clearing one body on the other's evidence, and never depending on which
/// body a by-id lookup happens to resolve.
#[test]
fn a_second_body_reusing_a_certified_id_cannot_borrow_its_certificate() {
    let _serial = serial();
    for (smuggled_first, edit) in [(false, true), (true, true), (false, false), (true, false)] {
        let mut module = envelope();
        let func = addmul(&module);
        let mut smuggled = module.function_by_id_mut(func).expect("addmul").clone();
        smuggled.name = "addmul_smuggled".to_string();
        if edit {
            for node in smuggled.blocks.iter_mut().flat_map(|b| b.body.iter_mut()) {
                if let Inst::BinOp { op, .. } = &mut node.inst
                    && *op == BinOp::Mul
                {
                    *op = BinOp::Add;
                }
            }
        }
        if smuggled_first {
            module.functions.insert(0, smuggled);
        } else {
            module.functions.push(smuggled);
        }
        let what = format!("smuggled_first={smuggled_first} edited={edit}");
        let policy = CodegenLicensePolicy::default();
        for (entry, verdict) in verdicts(&module, &policy) {
            assert!(
                verdict.is_some(),
                "{what}: entry `{entry}` must refuse the reused id"
            );
        }
        for (lane, verdict) in [
            ("enforce_module", policy.enforce_module(&module).err()),
            ("verdict", policy.verdict(&module, func).err()),
        ] {
            match verdict {
                Some(AdapterError::InvalidTrustIr(message)) => assert!(
                    message.contains("ambiguous")
                        && message.contains(&format!("FuncId({})", func.index())),
                    "{what}: {lane}: {message}"
                ),
                other => {
                    panic!("{what}: {lane}: the reused id must be refused as ambiguous: {other:?}")
                }
            }
        }
    }
}

/// The Rust producer's structural stamp is not recognized by default
/// (decision gate DG-22): only a consumer that names it admits it.
#[test]
fn the_structural_authority_is_not_recognized_by_default() {
    let _serial = serial();
    let mut module = envelope();
    module.proof_obligations.clear();
    module.proof_certificates.clear();
    module.functions[0].body_gate = Some(BodyGate::gated("trust-direct-lane-structural"));
    assert_all_refused(
        &module,
        &CodegenLicensePolicy::default(),
        "structural",
        |error| {
            matches!(error, AdapterError::UnrecognizedGateAuthority { authority, .. }
            if authority == "trust-direct-lane-structural")
        },
    );
    assert_all_permitted(
        &module,
        &CodegenLicensePolicy::default().with_recognized_authority("trust-direct-lane-structural"),
        "structural, named by the consumer",
    );
}

// ---------------------------------------------------------------------------
// The inline-only lane (review): `translate_inline_only_bodies` and
// `translate_body_template` are adapter entries too, and decide the license
// on the MODULE, where the evidence lives. Each verdict below has its twin.
// ---------------------------------------------------------------------------

/// `add7` as an INLINE-ONLY body (`AvailableExternally` with a body), minted
/// with that linkage so the certificate is about exactly this function.
fn minted_inline_only_add7() -> Module {
    let mut mb = ModuleBuilder::new("ws7_5_minted_inline_only");
    mb.set_default_producer(Producer::Clean);
    let sig = mb.add_func_type(vec![Ty::U64], vec![Ty::U64]);
    let mut fb = mb.function("add7", sig);
    fb.set_linkage(Linkage::AvailableExternally);
    fb.set_body_gate(BodyGate::gated(CLEAN_KERNEL_TV_AUTHORITY));
    let entry = fb.create_block();
    let x = fb.add_block_param(entry, Ty::U64);
    fb.switch_to_block(entry);
    let seven = fb.uconst(Ty::U64, 7);
    let sum = fb.add(Ty::U64, x, seven);
    fb.ret(vec![sum]);
    let func = fb.build();
    let mut module = mb.build().expect("ModuleBuilder::build: test fixture");
    let (_node, obligation, certificate) = certify_identity_lineage_rung(
        &module,
        ProofLineageId::new(0),
        ProofId::new(0),
        ProofTransform::new(
            ProofTransformStage::Frontend,
            "identity",
            "trust-cg-ws7.5",
            "1.0.0",
        ),
        func,
    )
    .expect("the inline-only add7 is in the clean_backend_tv fragment");
    module.proof_obligations.push(obligation);
    module.proof_certificates.push(certificate);
    assert_eq!(trust_ir_build::validate_module_for_codegen(&module), []);
    assert_eq!(
        trust_ir_build::validate_module_report(&module)
            .replayed_certificate_refs()
            .map(|refs| refs.len()),
        Some(1),
        "the inline-only add7's TV certificate is kernel-replayed at the pin"
    );
    module
}

/// The inline-only lane's verdict on `module` under `policy`: the names it
/// keeps and the `(name, reason)` pairs it withholds.
fn inline_only_lane(
    module: &Module,
    policy: &CodegenLicensePolicy,
) -> (Vec<String>, Vec<(String, String)>) {
    let out = translate_inline_only_bodies(
        module,
        GuardCarrierArch::AArch64,
        ObjectAccessModel::from(TlsDialect::default()),
        policy,
    );
    (
        out.bodies.iter().map(|(f, _)| f.name.clone()).collect(),
        out.withheld
            .iter()
            .map(|w| (w.name.clone(), w.reason.clone()))
            .collect(),
    )
}

/// The body template's verdict on `func` against `module` under `policy`.
fn body_template(
    module: &Module,
    func: &trust_ir::Function,
    policy: &CodegenLicensePolicy,
) -> Result<(), String> {
    translate_body_template(
        module,
        func,
        GuardCarrierArch::AArch64,
        ObjectAccessModel::from(TlsDialect::default()),
        policy,
    )
    .map(|_| ())
}

/// Positive: the certified inline-only body is KEPT by the lane and
/// translated by the template under the DEFAULT policy (which refuses
/// claim-less bodies, so no Permit admits it).
#[test]
fn an_inline_only_body_with_its_certificate_is_kept_under_the_default() {
    let _serial = serial();
    let module = minted_inline_only_add7();
    let policy = CodegenLicensePolicy::default();
    assert_eq!(
        inline_only_lane(&module, &policy),
        (vec!["add7".to_string()], vec![])
    );
    let add7 = module.function_by_name("add7").expect("add7");
    assert_eq!(body_template(&module, add7, &policy), Ok(()));
}

/// Negative twin: the same module with ZERO obligations and ZERO
/// certificates is withheld by the lane and refused by the template, by the
/// evidence refusal, under every policy — the claim-less Permit and a policy
/// recognizing another authority included.
#[test]
fn an_inline_only_body_without_its_certificate_is_withheld_on_every_policy() {
    let _serial = serial();
    let mut module = minted_inline_only_add7();
    module.proof_obligations.clear();
    module.proof_certificates.clear();
    let add7 = module.function_by_name("add7").expect("add7").clone();
    for policy in [
        CodegenLicensePolicy::default(),
        CodegenLicensePolicy::default().with_unlicensed(UnlicensedBodyPolicy::Permit),
        CodegenLicensePolicy::default().with_recognized_authority("someone-elses-gate"),
    ] {
        let what = policy.canonical_identity();
        let (kept, withheld) = inline_only_lane(&module, &policy);
        assert!(kept.is_empty(), "{what}: {kept:?}");
        assert_eq!(withheld.len(), 1, "{what}: {withheld:?}");
        let (name, reason) = &withheld[0];
        assert_eq!(name, "add7", "{what}");
        assert!(
            reason.starts_with("codegen license: ")
                && reason.contains("without the evidence it names")
                && reason.contains("no TranslationValidation obligation"),
            "{what}: {reason}"
        );
        let refused = body_template(&module, &add7, &policy).expect_err("the template refuses");
        assert!(
            refused.contains("without the evidence it names")
                && refused.contains("no TranslationValidation obligation"),
            "{what}: {refused}"
        );
    }
}

/// Adversarial: a body edited after its certificate was minted (`x + 7` ->
/// `x * 7`) is withheld as not kernel-replayed; and a template handed a
/// STALE-EDITED clone of the function while the module still holds the
/// certified original is refused the same way — the template judges the
/// module as it holds exactly `func`, never `func` by its original's
/// certificate. The module's own original still translates (control).
#[test]
fn an_inline_only_body_edited_after_mint_is_withheld_and_a_stale_clone_is_not_licensed() {
    let _serial = serial();
    let policy = CodegenLicensePolicy::default();
    let mut edited = minted_inline_only_add7();
    let func = edited.function_by_name("add7").expect("add7").id;
    edit_binop(&mut edited, func, BinOp::Add, BinOp::Mul);
    let (kept, withheld) = inline_only_lane(&edited, &policy);
    assert!(kept.is_empty(), "{kept:?}");
    assert!(
        withheld.len() == 1 && withheld[0].1.contains("not kernel-replayed"),
        "{withheld:?}"
    );

    let certified = minted_inline_only_add7();
    let stale = edited.function_by_id(func).expect("edited add7").clone();
    let refused =
        body_template(&certified, &stale, &policy).expect_err("the stale clone is refused");
    assert!(refused.contains("not kernel-replayed"), "{refused}");
    let original = certified.function_by_id(func).expect("add7");
    assert_eq!(body_template(&certified, original, &policy), Ok(()));
}

/// Adversarial: the template handed the CERTIFIED body under an id the module
/// does not hold (a byte-identical clone, re-identified and renamed so no
/// symbol or id collides) is refused by the evidence refusal: the template
/// judges the module holding exactly `func`, so the certificate scoped to the
/// original's id never licenses the clone's. The original still translates.
#[test]
fn a_template_handed_a_certified_body_under_another_id_is_not_licensed() {
    let _serial = serial();
    let policy = CodegenLicensePolicy::default();
    let module = minted_inline_only_add7();
    let original = module.function_by_name("add7").expect("add7");
    let mut clone = original.clone();
    clone.id = FuncId::new(7);
    clone.name = "add7_clone".to_string();
    assert!(module.function_by_id(clone.id).is_none());
    let refused =
        body_template(&module, &clone, &policy).expect_err("the re-identified clone is refused");
    assert!(
        refused.contains("without the evidence it names")
            && refused.contains("no TranslationValidation obligation"),
        "{refused}"
    );
    assert_eq!(body_template(&module, original, &policy), Ok(()));
}

/// Adversarial: a `Failed` TV row about the body revokes the inline-only
/// license too, by that row's id, although the certificate beside it replays.
#[test]
fn a_failed_tv_row_withholds_an_inline_only_body() {
    let _serial = serial();
    let mut module = minted_inline_only_add7();
    let row = tv_row(&module);
    module.proof_obligations[row].status = ProofStatus::Failed;
    let obligation = module.proof_obligations[row].id.index();
    let (kept, withheld) = inline_only_lane(&module, &CodegenLicensePolicy::default());
    assert!(kept.is_empty(), "{kept:?}");
    assert!(
        withheld.len() == 1
            && withheld[0].1.contains("REFUTED in-module")
            && withheld[0].1.contains(&format!("obligation {obligation} ")),
        "{withheld:?}"
    );
}

// ---------------------------------------------------------------------------
// Mutation control
// ---------------------------------------------------------------------------

/// A default build carries no mutation knob.
#[test]
fn default_build_has_no_mutation_knobs() {
    let _serial = serial();
    assert_eq!(
        trust_cg_lower::MUTATION_KNOBS,
        cfg!(feature = "mutation-knobs")
    );
}

/// Compiling other mutation controls must not disable the evidence floor.
#[cfg(feature = "mutation-knobs")]
#[test]
fn mutation_build_keeps_the_mandatory_evidence_floor() {
    let _serial = serial();
    let mut module = envelope();
    module.proof_obligations.clear();
    module.proof_certificates.clear();
    let mut inline_only = minted_inline_only_add7();
    inline_only.proof_obligations.clear();
    inline_only.proof_certificates.clear();
    assert_all_refused(
        &module,
        &CodegenLicensePolicy::default(),
        "mutation-enabled negative twin",
        without_evidence("addmul", "no TranslationValidation obligation"),
    );
    let (kept, withheld) = inline_only_lane(&inline_only, &CodegenLicensePolicy::default());
    assert!(
        kept.is_empty() && withheld.len() == 1,
        "the inline-only negative twin stays refused: {kept:?} {withheld:?}"
    );
}
