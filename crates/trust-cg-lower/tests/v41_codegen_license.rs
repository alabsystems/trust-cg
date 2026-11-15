// trust-ir v41 CODEGEN LICENSE (`Function.body_gate`): the consumer half.
//
// Every lowering entry — compatibility, validated compatibility, prepared,
// strict, validated-strict (Core admission), and single-function — must reach
// the same verdict for the same function under the same policy:
//
//   * `Some(Ungated)`            -> refused under EVERY policy.
//   * `Some(Gated { authority })` -> permitted iff the authority is recognized
//                                   AND trust-ir's license layer has no finding
//                                   for the body (an evidence-bound authority
//                                   needs its certificate — WS7.5(b), pinned in
//                                   `tests/codegen_license_evidence.rs`).
//   * `None`                     -> REFUSED by default (DG-73, WS7.5), permitted
//                                   only under an explicit `Permit`.
//   * a DECLARATION              -> never a codegen subject; its gate is ignored.
//
// Each case is built by hand so exactly one construct varies, and the
// refusal is checked on every entry so no path can become a bypass.

#[path = "../../trust-cg-codegen/tests/common/panic_delivery_fixture.rs"]
mod panic_delivery_fixture;

use trust_cg_lower::adapter::AdapterError;
use trust_cg_lower::{
    CLEAN_KERNEL_TV_AUTHORITY, CodegenLicensePolicy, GuardCarrierArch, TlsDialect,
    UnlicensedBodyPolicy, prepare_module_for_lir, translate_function,
    translate_function_with_license, translate_module,
    translate_module_for_arch_with_tls_and_stats_and_validation_with_license,
    translate_module_for_arch_with_tls_and_stats_with_license,
    translate_module_for_arch_with_tls_and_validation_with_license,
    translate_module_for_arch_with_tls_with_license,
    translate_module_strict_for_arch_with_tls_and_validation_with_license,
    translate_validated_module_strict_for_arch_with_tls_and_validation,
    translate_validated_module_strict_for_arch_with_tls_and_validation_with_license,
};
use trust_ir::{
    AssertKind, Block, BlockId, BodyGate, Constant, Endianness, FuncId, FuncTy, Function, Inst,
    InstrNode, Module, StructPassingPolicy, TargetInfo, Ty, ValueId,
};

/// One defined function `entry: () -> i64` returning the constant 7.
fn defined_module() -> Module {
    let mut module = Module::new("v41_codegen_license");
    let sig = module
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![Ty::I64],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut entry = Function::new(FuncId::new(0), "entry", sig, BlockId::new(0));
    let mut block = Block::new(BlockId::new(0));
    block.body.push(
        InstrNode::new(Inst::Const {
            ty: Ty::I64,
            value: Constant::Int(7),
        })
        .with_result(ValueId::new(0)),
    );
    block.body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(0)],
    }));
    entry.blocks.push(block);
    module.functions.push(entry);
    module
}

fn gated(authority: &str) -> Option<BodyGate> {
    Some(BodyGate::gated(authority.to_string()))
}

/// Run every module entry under `policy` and return each verdict.
fn verdicts(
    module: &Module,
    policy: &CodegenLicensePolicy,
) -> Vec<(&'static str, Option<AdapterError>)> {
    let arch = GuardCarrierArch::AArch64;
    let tls = TlsDialect::default();
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
    ];
    // Preparation is license-neutral, but it runs the codegen prerequisites,
    // and trust-ir's license-EVIDENCE rule lives there (KIND 4): a body
    // wearing an evidence-bound authority without its certificate is refused
    // before any policy is consulted, so that refusal is the entry's verdict.
    match prepare_module_for_lir(module, arch) {
        Ok(prepared) => out.push((
            "prepared",
            prepared
                .translate_with_tls_and_validation_with_license(tls, policy)
                .err(),
        )),
        Err(error) => out.push(("prepared", Some(error))),
    }
    out.push((
        "single_function",
        translate_function_with_license(&module.functions[0], module, policy).err(),
    ));
    // The validated strict entry (Core admission) reuses a successful full
    // validation report. `validate_module` deliberately lets a module CARRY an
    // ungated body (legal to inspect), so the report succeeds and the
    // license verdict is the adapter's alone.
    // (The full validator asks a module that declares an import for
    // `TargetInfo`; a shape it rejects simply has no validated-strict leg.)
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
    out
}

fn assert_all_refused(
    module: &Module,
    policy: &CodegenLicensePolicy,
    check: impl Fn(&AdapterError) -> bool,
) {
    for (entry, verdict) in verdicts(module, policy) {
        match verdict {
            Some(error) => assert!(
                check(&error),
                "entry `{entry}`: unexpected refusal {error:?}"
            ),
            None => panic!("entry `{entry}` must refuse"),
        }
    }
}

fn assert_all_permitted(module: &Module, policy: &CodegenLicensePolicy) {
    for (entry, verdict) in verdicts(module, policy) {
        assert!(
            verdict.is_none(),
            "entry `{entry}` must permit: {verdict:?}"
        );
    }
}

#[test]
fn ungated_body_is_refused_under_every_policy_on_every_entry() {
    let mut module = defined_module();
    module.functions[0].body_gate = Some(BodyGate::Ungated);
    for policy in [
        CodegenLicensePolicy::default(),
        CodegenLicensePolicy::recognizing_nothing(),
        CodegenLicensePolicy::default().with_unlicensed(UnlicensedBodyPolicy::Refuse),
        CodegenLicensePolicy::default().with_recognized_authority("ungated"),
    ] {
        assert_all_refused(
            &module,
            &policy,
            |error| matches!(error, AdapterError::UngatedBody { function } if function == "entry"),
        );
    }
    // The default-policy entries agree.
    assert!(matches!(
        translate_module(&module),
        Err(AdapterError::UngatedBody { .. })
    ));
    assert!(matches!(
        translate_function(&module.functions[0], &module),
        Err(AdapterError::UngatedBody { .. })
    ));
    let report = trust_ir_build::validate_module_report(&module);
    assert!(matches!(
        translate_validated_module_strict_for_arch_with_tls_and_validation(
            &report,
            GuardCarrierArch::AArch64,
            TlsDialect::default()
        ),
        Err(AdapterError::UngatedBody { .. })
    ));
}

#[test]
fn unrecognized_gate_authority_is_refused_and_recognized_is_permitted() {
    let mut module = defined_module();
    module.functions[0].body_gate = gated("someone-elses-gate");
    assert_all_refused(&module, &CodegenLicensePolicy::default(), |error| {
        matches!(
            error,
            AdapterError::UnrecognizedGateAuthority { function, authority }
                if function == "entry" && authority == "someone-elses-gate"
        )
    });
    // Recognizing the authority flips every entry to permit.
    let widened = CodegenLicensePolicy::default().with_recognized_authority("someone-elses-gate");
    assert_all_permitted(&module, &widened);

    // The Clean kernel TV gate is recognized by default — and it is
    // EVIDENCE-BOUND (trust-ir WS1.5, `EVIDENCE_BOUND_GATE_AUTHORITIES`):
    // worn with no kernel-rechecked TranslationValidation certificate it is
    // refused on every entry, under every policy, by NAME
    // (`AdapterError::GatedWithoutEvidence`, WS7.5(b); corpus row
    // `body_gate_kernel_tv_without_certificate`). Recognition never stands
    // in for the evidence, so a policy recognizing nothing gets the same
    // refusal, not `UnrecognizedGateAuthority`.
    let mut clean = defined_module();
    clean.functions[0].body_gate = gated(CLEAN_KERNEL_TV_AUTHORITY);
    for policy in [
        CodegenLicensePolicy::default(),
        CodegenLicensePolicy::recognizing_nothing(),
    ] {
        assert_all_refused(&clean, &policy, |error| {
            matches!(
                error,
                AdapterError::GatedWithoutEvidence { function, authority, missing }
                    if function == "entry"
                        && authority == CLEAN_KERNEL_TV_AUTHORITY
                        && missing.contains("no TranslationValidation obligation")
            ) && error.to_string().contains("without the evidence it names")
        });
    }
    assert!(matches!(
        translate_module(&clean),
        Err(AdapterError::GatedWithoutEvidence { .. })
    ));
}

/// DG-73 (roadmap WS7.5 DECIDE 1): a claim-less body is REFUSED by default on
/// every entry — the default-policy entries included — and compiled only
/// under an explicit `Permit`. Rows `LEAN.consumer.ungated_codegen` /
/// `rerun.moved04` residue (F-116: "trust-cg's DEFAULT policy still permits
/// body_gate None").
#[test]
fn claim_less_body_is_refused_by_default_and_permitted_only_under_permit() {
    let module = defined_module();
    assert_eq!(module.functions[0].body_gate, None);
    for refusing in [
        CodegenLicensePolicy::default(),
        CodegenLicensePolicy::default().with_unlicensed(UnlicensedBodyPolicy::Refuse),
    ] {
        assert_all_refused(
            &module,
            &refusing,
            |error| matches!(error, AdapterError::UnlicensedBody { function } if function == "entry"),
        );
    }
    assert!(matches!(
        translate_module(&module),
        Err(AdapterError::UnlicensedBody { .. })
    ));
    assert!(matches!(
        translate_function(&module.functions[0], &module),
        Err(AdapterError::UnlicensedBody { .. })
    ));
    let permitting = CodegenLicensePolicy::default().with_unlicensed(UnlicensedBodyPolicy::Permit);
    assert_all_permitted(&module, &permitting);

    let refusing = CodegenLicensePolicy::default();
    // Under `Refuse`, a recognized gate still licenses the body — an
    // authority outside trust-ir's evidence table, so recognition is the
    // whole decision (`clean-kernel-tv` would need its certificate).
    let refusing_but_recognizing = refusing.with_recognized_authority("someone-elses-gate");
    let mut licensed = defined_module();
    licensed.functions[0].body_gate = gated("someone-elses-gate");
    assert_all_permitted(&licensed, &refusing_but_recognizing);
}

#[test]
fn declarations_are_never_codegen_subjects() {
    // A bodyless declaration carrying `Ungated` — or nothing, under `Refuse`
    // — is not a codegen subject: exactly trust-ir-build's codegen-intent rule.
    let mut module = defined_module();
    let sig = module.functions[0].ty;
    let mut import = Function::new(FuncId::new(1), "imported", sig, BlockId::new(0));
    import.body_gate = Some(BodyGate::Ungated);
    module.functions.push(import);
    // The defined `entry` is claim-less, so its own license needs `Permit`;
    // the `Ungated` DECLARATION beside it is never consulted.
    assert_all_permitted(
        &module,
        &CodegenLicensePolicy::default().with_unlicensed(UnlicensedBodyPolicy::Permit),
    );

    let mut module = defined_module();
    let sig = module.functions[0].ty;
    module.functions[0].body_gate = gated("someone-elses-gate");
    let import = Function::new(FuncId::new(1), "imported", sig, BlockId::new(0));
    assert_eq!(import.body_gate, None);
    module.functions.push(import);
    let refusing = CodegenLicensePolicy::default()
        .with_unlicensed(UnlicensedBodyPolicy::Refuse)
        .with_recognized_authority("someone-elses-gate");
    assert_all_permitted(&module, &refusing);
}

#[test]
fn the_first_refusal_names_the_offending_function_not_a_wildcard() {
    // Two functions: a licensed one first, an ungated one second. The
    // refusal must name the second — never a blanket module verdict.
    // The licensed one wears a recognized authority outside trust-ir's
    // evidence table (`clean-kernel-tv` would need its certificate), under
    // a policy that recognizes it.
    let recognizing =
        CodegenLicensePolicy::default().with_recognized_authority("someone-elses-gate");
    let mut module = defined_module();
    module.functions[0].body_gate = gated("someone-elses-gate");
    let sig = module.functions[0].ty;
    let mut second = Function::new(FuncId::new(1), "second", sig, BlockId::new(0));
    let mut block = Block::new(BlockId::new(0));
    block.body.push(
        InstrNode::new(Inst::Const {
            ty: Ty::I64,
            value: Constant::Int(1),
        })
        .with_result(ValueId::new(0)),
    );
    block.body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(0)],
    }));
    second.blocks.push(block);
    second.body_gate = Some(BodyGate::Ungated);
    module.functions.push(second);
    match translate_module_for_arch_with_tls_and_validation_with_license(
        &module,
        GuardCarrierArch::AArch64,
        TlsDialect::default(),
        &recognizing,
    ) {
        Err(AdapterError::UngatedBody { function }) => assert_eq!(function, "second"),
        other => panic!("expected UngatedBody for `second`, got {other:?}"),
    }
    // Single-function lowering judges only the function it lowers.
    assert!(
        translate_function_with_license(&module.functions[0], &module, &recognizing).is_ok(),
        "the licensed function lowers on its own"
    );
    assert!(matches!(
        translate_function_with_license(&module.functions[1], &module, &recognizing),
        Err(AdapterError::UngatedBody { .. })
    ));
}

/// A body that carries a panic delivery (a sited `Inst::Assert`) gets the
/// same license verdict, under the same names, as a body without one. For
/// such a body the codegen prerequisites refuse trust-ir's whole verdict,
/// except the findings this policy decides on every entry right after them
/// (decision LD-W7-8). Otherwise trust-ir's `UngatedBodyForCodegen` text
/// would arrive first as a generic `TrustIrAdmissionRefused` on every entry
/// that runs the prerequisites before the license.
#[test]
fn a_panic_delivery_body_keeps_the_license_refusals_by_name() {
    // The panic entry is `extern "Rust"` called from a C body: an FFI
    // boundary, which needs the pinned target the entries lower for.
    let delivery = || {
        let mut module = panic_delivery_fixture::module(
            AssertKind::BoundsCheck {
                index: ValueId::new(1),
                len: ValueId::new(2),
            },
            false,
            false,
        );
        module.target_info = Some(TargetInfo {
            triple: "aarch64-apple-darwin".into(),
            pointer_size: 8,
            endianness: Endianness::Little,
            abi: None,
            struct_passing: StructPassingPolicy::NativeC,
        });
        module
    };
    let mut ungated = delivery();
    assert_eq!(ungated.functions[0].name, "tc_check");
    assert!(
        ungated.functions[0]
            .blocks
            .iter()
            .flat_map(|block| &block.body)
            .any(|node| node.inst.panic_site().is_some()),
        "fixture: the body carries a panic delivery"
    );
    ungated.functions[0].body_gate = Some(BodyGate::Ungated);
    for policy in [
        CodegenLicensePolicy::default(),
        CodegenLicensePolicy::default().with_unlicensed(UnlicensedBodyPolicy::Permit),
        CodegenLicensePolicy::default().with_recognized_authority("ungated"),
    ] {
        assert_all_refused(
            &ungated,
            &policy,
            |error| matches!(error, AdapterError::UngatedBody { function } if function == "tc_check"),
        );
    }

    let claim_less = delivery();
    assert_eq!(claim_less.functions[0].body_gate, None);
    assert_all_refused(
        &claim_less,
        &CodegenLicensePolicy::default(),
        |error| matches!(error, AdapterError::UnlicensedBody { function } if function == "tc_check"),
    );

    let mut unrecognized = delivery();
    unrecognized.functions[0].body_gate = gated("someone-elses-gate");
    assert_all_refused(&unrecognized, &CodegenLicensePolicy::default(), |error| {
        matches!(
            error,
            AdapterError::UnrecognizedGateAuthority { function, authority }
                if function == "tc_check" && authority == "someone-elses-gate"
        )
    });
}
