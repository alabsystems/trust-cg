//! Exact module function addresses, owner preparation, and sparse replay.

use trust_cg_lower::{
    GuardCarrierArch, TlsDialect,
    instructions::{Opcode, Value},
    prepare_module_for_lir,
};
use trust_ir::{BinOp, Constant, FuncId, Inst, Linkage, Module, Ty};
use trust_ir_build::{ModuleBuilder, validate_module};

#[path = "common/typed_refusal.rs"]
mod typed_refusal;
use typed_refusal::assert_typed_const_refusal;

fn module(closure: bool, div: bool) -> Module {
    let mut builder = ModuleBuilder::new("function_addresses");
    let sig = builder.add_func_type(vec![Ty::I64], vec![Ty::I64]);
    let mut target = builder.function("exact_target", sig);
    let entry = target.create_block();
    let value = target.add_block_param(entry, Ty::I64);
    target.switch_to_block(entry);
    target.ret(vec![value]);
    let target_id = target.build();
    let address_sig = builder.add_func_type(vec![Ty::I64], vec![Ty::Func(sig)]);
    let mut caller = builder.function("address", address_sig);
    let entry = caller.create_block();
    let value = caller.add_block_param(entry, Ty::I64);
    caller.switch_to_block(entry);
    if div {
        let two = caller.iconst(Ty::I64, 2);
        caller.binop(BinOp::UDiv, Ty::I64, value, two);
    }
    let constant = if closure {
        Constant::Closure {
            func: target_id,
            captures: vec![],
        }
    } else {
        Constant::FnDef(target_id)
    };
    let address = caller.const_value(Ty::Func(sig), constant);
    caller.ret(vec![address]);
    caller.build();
    let mut module = builder.build().expect("ModuleBuilder::build: test fixture");
    // Sparse, non-positional identities and reverse storage order.
    module.functions[0].id = FuncId::new(7001);
    module.functions[0].linkage = Linkage::Internal;
    module.functions[1].id = FuncId::new(9009);
    for node in &mut module.functions[1].blocks[0].body {
        match &mut node.inst {
            Inst::Const {
                value: Constant::FnDef(id),
                ..
            }
            | Inst::Const {
                value: Constant::Closure { func: id, .. },
                ..
            } => *id = FuncId::new(7001),
            _ => {}
        }
    }
    module.functions.reverse();
    if !closure {
        assert_eq!(validate_module(&module), []);
    } else {
        // The capture-free Closure-as-Ty::Func legacy spelling is not valid
        // TrustIR, and the adapter's public entry now consumes TrustIR's
        // typed admission first: the spelling is refused end to end, never
        // given an exact (or any) binding.
        assert!(!validate_module(&module).is_empty());
    }
    module
}

#[test]
fn exact_addresses_replay_sparse_identity_and_reject_all_carrier_tampering() {
    let legacy = trust_cg_lower::translate_module_for_arch_with_tls_and_validation_with_license(
        &module(true, false),
        GuardCarrierArch::AArch64,
        TlsDialect::default(),
        &permit_unlicensed(),
    )
    .unwrap_err();
    assert_typed_const_refusal(
        &legacy,
        "function 'address' bb0",
        "functy.0",
        "closure<func.7001>[0]",
    );
    {
        let source = module(false, false);
        let (lir, report) =
            trust_cg_lower::translate_module_for_arch_with_tls_and_validation_with_license(
                &source,
                GuardCarrierArch::AArch64,
                TlsDialect::default(),
                &permit_unlicensed(),
            )
            .unwrap();
        assert_eq!(report.exact_module_call_count(), 0);
        assert_eq!(report.exact_module_address_count(), 1);
        report.replay_exact_module_bindings(&lir).unwrap();
        report.replay_exact_module_calls(&lir).unwrap();
        report.replay_exact_module_calls_exhaustive(&lir).unwrap();
        let (block, index) = lir[0]
            .0
            .blocks
            .iter()
            .find_map(|(id, block)| {
                block.instructions.iter().position(|inst| matches!(inst.opcode,
                Opcode::FunctionAddr { function: 7001, ref name } if name == "exact_target"
            )).map(|index| (*id, index))
            })
            .unwrap();
        for mutation in 0..6 {
            let mut altered = lir.clone();
            let function = &mut altered[0].0;
            let inst = &mut function.blocks.get_mut(&block).unwrap().instructions[index];
            match mutation {
                0 => {
                    inst.opcode = Opcode::GlobalRef {
                        name: "exact_target".into(),
                    }
                }
                1 => {
                    inst.opcode = Opcode::FunctionAddr {
                        name: "renamed".into(),
                        function: 7001,
                    }
                }
                2 => {
                    inst.opcode = Opcode::FunctionAddr {
                        name: "exact_target".into(),
                        function: 9009,
                    }
                }
                3 => inst.results[0] = Value(123456),
                4 => inst.args.push(Value(123456)),
                _ => function.trust_ir_origins.get_mut(&block).unwrap()[index] = None,
            }
            assert!(
                report.replay_exact_module_bindings(&altered).is_err(),
                "mutation {mutation}"
            );
        }
    }
}

#[test]
fn caller_owned_preparation_is_borrowed_or_idempotent_without_weakening_clone_gate() {
    let unchanged = module(false, false);
    let prepared = prepare_module_for_lir(&unchanged, GuardCarrierArch::AArch64).unwrap();
    assert!(std::ptr::eq(prepared.as_ref(), &unchanged));
    assert_eq!(prepared.architecture(), GuardCarrierArch::AArch64);

    let source = module(false, true);
    let before = source.stable_digest();
    let error = trust_cg_lower::translate_module_for_arch_with_tls_and_validation_with_license(
        &source,
        GuardCarrierArch::AArch64,
        TlsDialect::default(),
        &permit_unlicensed(),
    )
    .unwrap_err();
    assert!(error.to_string().contains("adapter-owned module clone"));
    let prepared = prepare_module_for_lir(&source, GuardCarrierArch::AArch64).unwrap();
    assert!(!std::ptr::eq(prepared.as_ref(), &source));
    assert_eq!(source.stable_digest(), before);
    let again = prepare_module_for_lir(prepared.as_ref(), GuardCarrierArch::AArch64).unwrap();
    assert!(std::ptr::eq(again.as_ref(), prepared.as_ref()));
    let (lir, report) = prepared
        .translate_with_tls_and_validation_with_license(TlsDialect::default(), &permit_unlicensed())
        .unwrap();
    assert_eq!(report.exact_module_address_count(), 1);
    report.replay_exact_module_bindings(&lir).unwrap();
}

#[test]
fn legacy_and_interposable_function_addresses_do_not_gain_exact_binding() {
    let source = module(false, false);
    let legacy = trust_cg_lower::translate_module_for_arch_with_tls_with_license(
        &source,
        GuardCarrierArch::AArch64,
        TlsDialect::default(),
        &permit_unlicensed(),
    )
    .unwrap();
    assert!(
        legacy[0]
            .0
            .blocks
            .values()
            .flat_map(|block| &block.instructions)
            .any(|inst| matches!(inst.opcode, Opcode::GlobalRef { .. }))
    );
    for bodyless in [false, true] {
        let mut source = module(false, false);
        let target = &mut source.functions[1];
        target.linkage = Linkage::External;
        if bodyless {
            target.blocks.clear();
        }
        let (lir, report) =
            trust_cg_lower::translate_module_for_arch_with_tls_and_validation_with_license(
                &source,
                GuardCarrierArch::AArch64,
                TlsDialect::default(),
                &permit_unlicensed(),
            )
            .unwrap();
        assert_eq!(report.exact_module_address_count(), 0);
        report.replay_exact_module_bindings(&lir).unwrap();
        assert!(
            lir[0]
                .0
                .blocks
                .values()
                .flat_map(|block| &block.instructions)
                .any(|inst| matches!(
                    inst.opcode,
                    Opcode::GlobalRef { .. } | Opcode::ExternRef { .. }
                ))
        );
    }
}

/// The exact-address route compares a function item's declared `Ty::Func`
/// signature with its target's actual one ("has a missing or mismatched target
/// signature"). A MISMATCH is refused first by TrustIR's typed admission: its
/// `FnDef` rule requires the item's `FuncTyId` to be its target's. The
/// MISSING half is this route's own refusal, pinned by
/// `exact_address_with_a_shared_dangling_signature_is_refused_by_the_route`.
#[test]
fn exact_address_requires_actual_structural_target_signature() {
    for closure in [false, true] {
        let mut source = module(closure, false);
        let wrong = source
            .add_func_type(trust_ir::FuncTy {
                params: vec![],
                returns: vec![Ty::I64],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        for node in &mut source.functions[0].blocks[0].body {
            if let Inst::Const {
                ty,
                value: Constant::FnDef(_) | Constant::Closure { .. },
            } = &mut node.inst
            {
                *ty = Ty::Func(wrong);
            }
        }
        let error = trust_cg_lower::translate_module_for_arch_with_tls_and_validation_with_license(
            &source,
            GuardCarrierArch::AArch64,
            TlsDialect::default(),
            &permit_unlicensed(),
        )
        .unwrap_err();
        // TrustIR's typed admission checks the item against its target's
        // actual signature before the exact-address route is reached.
        let (expected, actual) = if closure {
            ("functy.2", "closure<func.7001>[0]")
        } else {
            ("functy.0 for func.7001", "functy.2")
        };
        assert_typed_const_refusal(&error, "function 'address' bb0", expected, actual);
        // Do not broaden the canonical validator's acceptance or quietly emit
        // an interposable carrier in the new checked identity route.
        assert!(!validate_module(&source).is_empty());
    }
}

/// A function item and its target that share a `FuncTyId` naming no function
/// type. TrustIR's `FnDef` rule compares only the ids, and the codegen
/// admission refuses a named list of validation errors that leaves out
/// `FuncTypeNotFound`, `DanglingTypeReference` and `ReturnTypeMismatch`, so
/// the exact-address route's missing-signature check is the first refusal on
/// both the module entry and the prepared entry, whether or not the caller's
/// return type also names the dangling id.
#[test]
fn exact_address_with_a_shared_dangling_signature_is_refused_by_the_route() {
    const REFUSAL: &str = "unsupported trust_ir instruction: exact function address \
                           FuncId(7001) has a missing or mismatched target signature";
    let dangling = trust_ir::FuncTyId::new(99);
    for caller_returns_it in [false, true] {
        let mut source = module(false, false);
        source.functions[1].ty = dangling;
        for node in &mut source.functions[0].blocks[0].body {
            if let Inst::Const {
                ty,
                value: Constant::FnDef(_),
            } = &mut node.inst
            {
                *ty = Ty::Func(dangling);
            }
        }
        if caller_returns_it {
            source.func_types[1].returns = vec![Ty::Func(dangling)];
        }
        let errors = validate_module(&source);
        assert!(!errors.is_empty());
        for error in &errors {
            let shape = format!("{error:?}");
            assert!(
                [
                    "FuncTypeNotFound",
                    "DanglingTypeReference",
                    "ReturnTypeMismatch"
                ]
                .iter()
                .any(|kind| shape.starts_with(kind)),
                "only errors the codegen admission tolerates: {shape}"
            );
        }
        let error = trust_cg_lower::translate_module_for_arch_with_tls_and_validation_with_license(
            &source,
            GuardCarrierArch::AArch64,
            TlsDialect::default(),
            &permit_unlicensed(),
        )
        .unwrap_err();
        assert_eq!(
            error.to_string(),
            REFUSAL,
            "module entry, {caller_returns_it}"
        );
        let error = prepare_module_for_lir(&source, GuardCarrierArch::AArch64)
            .expect("the preparation admits the dangling id")
            .translate_with_tls_and_validation_with_license(
                TlsDialect::default(),
                &permit_unlicensed(),
            )
            .unwrap_err();
        assert_eq!(
            error.to_string(),
            REFUSAL,
            "prepared entry, {caller_returns_it}"
        );
    }
}

#[test]
fn mixed_exact_call_and_address_census_counts_each_binding_once() {
    let mut source = module(false, false);
    source.functions[0].blocks[0].body.insert(
        0,
        trust_ir::InstrNode::new(Inst::Call {
            callee: FuncId::new(7001),
            args: vec![trust_ir::ValueId::new(0)],
        })
        .with_result(trust_ir::ValueId::new(50001)),
    );
    assert_eq!(validate_module(&source), []);
    let prepared = prepare_module_for_lir(&source, GuardCarrierArch::AArch64).unwrap();
    let (lir, report) = prepared
        .translate_with_tls_and_validation_with_license(TlsDialect::default(), &permit_unlicensed())
        .unwrap();
    assert_eq!(report.exact_module_call_count(), 1);
    assert_eq!(report.exact_module_address_count(), 1);
    report.replay_exact_module_calls_exhaustive(&lir).unwrap();
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes because it was silently refused.
fn permit_unlicensed() -> trust_cg_lower::CodegenLicensePolicy {
    trust_cg_lower::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit)
}
