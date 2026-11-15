// Inline-only bodies: trust-ir `AvailableExternally` functions WITH a body.
//
// The module entries keep treating such a function as a codegen declaration
// (no body emitted, every call routed to the symbol). `translate_inline_only_
// bodies` translates the body as a template for a module inliner, withholding
// every candidate this backend must not use.

use trust_cg_lower::instructions::{DirectCallBinding, Opcode};
use trust_cg_lower::{
    CodegenLicensePolicy, GuardCarrierArch, ObjectAccessModel, RelocationModel, TlsDialect,
    translate_body_template, translate_inline_only_bodies,
    translate_module_for_arch_with_tls_and_validation_with_license,
};
use trust_ir::{
    BinOp, Block, BlockId, BodyGate, CallingConv, Constant, FuncId, FuncTy, Function, Inst,
    InstrNode, Linkage, Module, Ty, ValueId, Visibility,
};

/// `add_one(x) = x + 1` as an `AvailableExternally` function with a body, and
/// `entry(x) = add_one(x)`.
fn module_with_inline_only(configure: impl FnOnce(&mut Function)) -> Module {
    let mut module = Module::new("inline_only_bodies");
    let sig = module
        .add_func_type(FuncTy {
            params: vec![Ty::I64],
            returns: vec![Ty::I64],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");

    let mut target = Function::new(FuncId::new(0), "add_one", sig, BlockId::new(0));
    target.linkage = Linkage::AvailableExternally;
    let mut target_entry = Block::new(BlockId::new(0));
    target_entry.params.push((ValueId::new(0), Ty::I64));
    target_entry.body.push(
        InstrNode::new(Inst::Const {
            ty: Ty::I64,
            value: Constant::Int(1),
        })
        .with_result(ValueId::new(1)),
    );
    target_entry.body.push(
        InstrNode::new(Inst::BinOp {
            op: BinOp::Add,
            ty: Ty::I64,
            lhs: ValueId::new(0),
            rhs: ValueId::new(1),
        })
        .with_result(ValueId::new(2)),
    );
    target_entry.body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(2)],
    }));
    target.blocks.push(target_entry);
    configure(&mut target);
    module.functions.push(target);

    let mut caller = Function::new(FuncId::new(1), "entry", sig, BlockId::new(0));
    let mut caller_entry = Block::new(BlockId::new(0));
    caller_entry.params.push((ValueId::new(0), Ty::I64));
    caller_entry.body.push(
        InstrNode::new(Inst::Call {
            callee: FuncId::new(0),
            args: vec![ValueId::new(0)],
        })
        .with_result(ValueId::new(1)),
    );
    caller_entry.body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(1)],
    }));
    caller.blocks.push(caller_entry);
    module.functions.push(caller);
    module
}

fn static_model() -> ObjectAccessModel {
    ObjectAccessModel::from(TlsDialect::default())
}

#[test]
fn the_module_entries_still_treat_the_body_as_a_declaration() {
    let module = module_with_inline_only(|_| {});
    let (functions, validation) = translate_module_for_arch_with_tls_and_validation_with_license(
        &module,
        GuardCarrierArch::AArch64,
        TlsDialect::default(),
        &permit_unlicensed(),
    )
    .expect("translate");
    validation
        .replay_exact_module_bindings(&functions)
        .expect("replay");
    let names: Vec<_> = functions.iter().map(|(f, _)| f.name.as_str()).collect();
    assert_eq!(
        names,
        vec!["entry"],
        "an inline-only body is never a codegen unit"
    );
    let call = functions[0]
        .0
        .blocks
        .values()
        .flat_map(|block| &block.instructions)
        .find_map(|instruction| match &instruction.opcode {
            Opcode::Call { name, binding } => Some((name.clone(), *binding)),
            _ => None,
        })
        .expect("the caller keeps its call");
    assert_eq!(
        call,
        ("add_one".to_string(), DirectCallBinding::Interposable),
        "a call to an inline-only function is an ordinary by-name call"
    );
}

#[test]
fn a_bodied_available_externally_function_translates_as_an_inline_only_body() {
    let module = module_with_inline_only(|_| {});
    let out = translate_inline_only_bodies(
        &module,
        GuardCarrierArch::AArch64,
        static_model(),
        &permit_unlicensed(),
    );
    assert!(out.withheld.is_empty(), "{:?}", out.withheld);
    let names: Vec<_> = out.bodies.iter().map(|(f, _)| f.name.as_str()).collect();
    assert_eq!(names, vec!["add_one"]);
    assert!(
        out.bodies[0]
            .0
            .blocks
            .values()
            .flat_map(|block| &block.instructions)
            .any(|instruction| matches!(instruction.opcode, Opcode::Iadd)),
        "the body is the function's own"
    );
}

#[test]
fn a_module_without_inline_only_bodies_has_none() {
    let module = module_with_inline_only(|target| target.linkage = Linkage::Internal);
    let out = translate_inline_only_bodies(
        &module,
        GuardCarrierArch::AArch64,
        static_model(),
        &permit_unlicensed(),
    );
    assert!(out.bodies.is_empty() && out.withheld.is_empty());
}

#[test]
fn a_preemptible_symbol_under_pic_is_withheld_and_hidden_or_protected_is_not() {
    let pic = ObjectAccessModel::elf(RelocationModel::Pic);
    let module = module_with_inline_only(|_| {});
    let out = translate_inline_only_bodies(
        &module,
        GuardCarrierArch::AArch64,
        pic,
        &permit_unlicensed(),
    );
    assert!(out.bodies.is_empty());
    assert_eq!(out.withheld.len(), 1);
    assert_eq!(out.withheld[0].name, "add_one");
    assert!(
        out.withheld[0].reason.contains("preemptible"),
        "{:?}",
        out.withheld
    );

    for visibility in [Visibility::Hidden, Visibility::Protected] {
        let module = module_with_inline_only(|target| target.visibility = visibility);
        let out = translate_inline_only_bodies(
            &module,
            GuardCarrierArch::AArch64,
            pic,
            &permit_unlicensed(),
        );
        assert!(
            out.withheld.is_empty(),
            "{visibility:?}: {:?}",
            out.withheld
        );
        assert_eq!(out.bodies.len(), 1, "{visibility:?}");
    }
    for model in [RelocationModel::Static, RelocationModel::Pie] {
        let module = module_with_inline_only(|_| {});
        let out = translate_inline_only_bodies(
            &module,
            GuardCarrierArch::AArch64,
            ObjectAccessModel::elf(model),
            &permit_unlicensed(),
        );
        assert_eq!(out.bodies.len(), 1, "{model:?}");
    }
}

#[test]
fn a_swiftcc_body_is_withheld() {
    let module = module_with_inline_only(|target| target.calling_conv = CallingConv::Swift);
    let out = translate_inline_only_bodies(
        &module,
        GuardCarrierArch::AArch64,
        static_model(),
        &permit_unlicensed(),
    );
    assert!(out.bodies.is_empty());
    assert!(
        out.withheld[0].reason.contains("swiftcc"),
        "{:?}",
        out.withheld
    );
}

#[test]
fn a_body_the_license_refuses_is_withheld() {
    // `Ungated` is refused under EVERY policy, the permitting one included.
    let module = module_with_inline_only(|target| target.body_gate = Some(BodyGate::Ungated));
    let out = translate_inline_only_bodies(
        &module,
        GuardCarrierArch::AArch64,
        static_model(),
        &permit_unlicensed(),
    );
    assert!(out.bodies.is_empty());
    assert!(
        out.withheld[0].reason.contains("codegen license"),
        "{:?}",
        out.withheld
    );
}

#[test]
fn a_body_naming_a_module_local_symbol_is_withheld() {
    // The inline-only body calls this module's Internal `helper`: that name is
    // this module's, not the defining object's.
    let mut module = module_with_inline_only(|_| {});
    let sig = module.functions[0].ty;
    let helper_id = FuncId::new(module.functions.len() as u32);
    let mut helper = Function::new(helper_id, "helper", sig, BlockId::new(0));
    helper.linkage = Linkage::Internal;
    let mut helper_entry = Block::new(BlockId::new(0));
    helper_entry.params.push((ValueId::new(0), Ty::I64));
    helper_entry.body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(0)],
    }));
    helper.blocks.push(helper_entry);
    module.functions.push(helper);
    let body = &mut module.functions[0].blocks[0].body;
    let ret = body.pop().expect("return");
    body.push(
        InstrNode::new(Inst::Call {
            callee: helper_id,
            args: vec![ValueId::new(2)],
        })
        .with_result(ValueId::new(3)),
    );
    drop(ret);
    body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(3)],
    }));
    let out = translate_inline_only_bodies(
        &module,
        GuardCarrierArch::AArch64,
        static_model(),
        &permit_unlicensed(),
    );
    assert!(out.bodies.is_empty(), "{:?}", out.withheld);
    assert!(
        out.withheld[0]
            .reason
            .contains("module-local symbol `helper`"),
        "{:?}",
        out.withheld
    );
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). The tests about inline-only mechanics state `Permit`
/// explicitly, so no candidate is withheld (or kept) because the license
/// silently refused it; the tests about the license use the default.
fn permit_unlicensed() -> CodegenLicensePolicy {
    CodegenLicensePolicy::default().with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit)
}

// ---------------------------------------------------------------------------
// WS7.5: the codegen license reaches the inline-only lane
// ---------------------------------------------------------------------------

/// Under the DEFAULT policy a claim-less (`body_gate: None`) inline-only body
/// is withheld by the license (DG-73), exactly as the module entries refuse a
/// claim-less definition; the permitting twin keeps it (the tests above).
#[test]
fn a_claim_less_body_is_withheld_under_the_default_license() {
    let module = module_with_inline_only(|_| {});
    let out = translate_inline_only_bodies(
        &module,
        GuardCarrierArch::AArch64,
        static_model(),
        &CodegenLicensePolicy::default(),
    );
    assert!(out.bodies.is_empty(), "{:?}", out.bodies.len());
    assert_eq!(out.withheld.len(), 1, "{:?}", out.withheld);
    assert_eq!(out.withheld[0].name, "add_one");
    assert!(
        out.withheld[0].reason.contains("codegen license")
            && out.withheld[0]
                .reason
                .contains("carries no codegen license"),
        "{:?}",
        out.withheld
    );
    // The negative twin: the same module under the stated Permit keeps it.
    let permitted = translate_inline_only_bodies(
        &module,
        GuardCarrierArch::AArch64,
        static_model(),
        &permit_unlicensed(),
    );
    assert_eq!(permitted.bodies.len(), 1, "{:?}", permitted.withheld);
}

/// An inline-only body gated by the EVIDENCE-BOUND authority
/// (`clean-kernel-tv`) without its kernel-replayed TranslationValidation
/// certificate is withheld with the evidence refusal — under the default
/// policy and under the permitting one alike (Permit concerns `None` only).
/// The license is decided on the MODULE, where the evidence would live.
#[test]
fn a_gated_body_without_its_evidence_is_withheld_on_every_policy() {
    let module = module_with_inline_only(|target| {
        target.body_gate = Some(BodyGate::gated(trust_cg_lower::CLEAN_KERNEL_TV_AUTHORITY))
    });
    for (label, policy) in [
        ("default", CodegenLicensePolicy::default()),
        ("permit", permit_unlicensed()),
    ] {
        let out = translate_inline_only_bodies(
            &module,
            GuardCarrierArch::AArch64,
            static_model(),
            &policy,
        );
        assert!(out.bodies.is_empty(), "{label}");
        assert_eq!(out.withheld.len(), 1, "{label}: {:?}", out.withheld);
        assert!(
            out.withheld[0]
                .reason
                .contains("without the evidence it names"),
            "{label}: {:?}",
            out.withheld
        );
    }
}

/// `translate_body_template` (the defining module's side of an authenticated
/// inline-only body) applies the same license: a claim-less definition is
/// refused under the default and translated under the stated Permit; an
/// `Ungated` one is refused under both.
#[test]
fn the_body_template_applies_the_same_license() {
    let module = module_with_inline_only(|_| {});
    let definition = &module.functions[0];
    let refused = translate_body_template(
        &module,
        definition,
        GuardCarrierArch::AArch64,
        static_model(),
        &CodegenLicensePolicy::default(),
    )
    .expect_err("the default refuses a claim-less definition");
    assert!(
        refused.contains("codegen license") && refused.contains("carries no codegen license"),
        "{refused}"
    );
    let (translated, _) = translate_body_template(
        &module,
        definition,
        GuardCarrierArch::AArch64,
        static_model(),
        &permit_unlicensed(),
    )
    .expect("the stated Permit translates it");
    assert_eq!(translated.name, "add_one");

    let ungated = module_with_inline_only(|target| target.body_gate = Some(BodyGate::Ungated));
    let refused = translate_body_template(
        &ungated,
        &ungated.functions[0],
        GuardCarrierArch::AArch64,
        static_model(),
        &permit_unlicensed(),
    )
    .expect_err("Ungated is refused under every policy");
    assert!(refused.contains("codegen license"), "{refused}");
}
