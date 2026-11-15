// Copyright 2026 Andrew Yates | Apache-2.0

//! Ownership controls for the actual adapter output boundary. Seeded metadata
//! here tests transfer, not the validity of a synthetic function or authority.

use super::*;
use crate::function::{EhCallSite, EhLandingPad};

#[test]
fn output_handoff_moves_owned_allocations_and_retains_pending_call_rows() {
    let mut adapter = TrustIrAdapter::new(&[], HashMap::new());
    adapter.stack_slots.push(StackSlotInfo::new(16, 8));
    adapter.debug_local_variables.push(DebugLocalVariable {
        name: "owned_local".into(),
        ty: DebugBaseType::I64,
        storage: DebugVariableStorage::ConstantInt(17),
        decl_line: 12,
    });
    adapter.debug_value_bindings.push(DebugValueBinding {
        var_id: TrustIrVarId(3),
        value: Value(7),
    });
    adapter
        .value_types
        .insert(Value(7), Type::Struct(vec![Type::I64, Type::I32]));
    adapter.pure_callees.insert("pure_target".into());
    adapter.libm_pure_callees.insert("libm_target".into());
    adapter.eh_info.personality = Some("personality".into());
    adapter.eh_info.call_sites.push(EhCallSite {
        call_block: Block(0),
        landing_pad_block: Block(1),
    });
    adapter.eh_info.landing_pads.push(EhLandingPad {
        block: Block(1),
        catch_type_indices: vec![0, 2],
        is_cleanup: true,
    });
    adapter
        .proof_ctx
        .value_proofs
        .insert(Value(7), vec![Proof::Associative]);
    adapter.proof_ctx.function_proofs.push(Proof::Commutative);
    adapter
        .proof_ctx
        .value_facts
        .insert(Value(7), vec![ProofFact::NoUndef]);
    adapter.proof_ctx.function_facts.push(ProofFact::NoPanic);
    adapter.proof_ctx.noalias_param_indices.push(0);
    adapter
        .proof_ctx
        .diagnostics
        .push(ProofDropDiagnostic::no_carrier(ProofFact::NoPanic));
    let obligation = adapter
        .proof_ctx
        .synthesize_discharged_obligation()
        .unwrap();
    adapter.proof_ctx.record_synthesized_obligation_formula(
        obligation,
        trust_ir::proof::ProofFormula::smtlib2("true", "Bool"),
    );
    let mut source = TrustIrModule::new("retained_refinement");
    source
        .intern_pred(trust_ir::Pred::Top)
        .expect("Module::intern_pred: test fixture")
        .unwrap();
    adapter.proof_ctx.refinement_env = RefinementEnv::from_module(&source);
    adapter.exact_module_calls_lowered = 1;
    adapter
        .exact_module_call_authorizations
        .push(PendingExactModuleCallAuthorization::new(
            Block(0),
            2,
            TrustIrInstId(5),
            FuncId::new(4),
        ));
    adapter.declared_external_calls_lowered = 1;
    adapter.declared_external_call_authorizations.push(
        PendingDeclaredExternalCallAuthorization::new(
            Block(0),
            3,
            TrustIrInstId(6),
            FuncId::new(8),
        ),
    );

    // Already compact buffers must transfer without reallocating. A separate
    // control below covers slack: compaction may move an outer allocation.
    adapter.compact_output_metadata();
    // Save allocation identities, not references that would prevent transfer.
    let slots = adapter.stack_slots.as_ptr();
    let locals = adapter.debug_local_variables.as_ptr();
    let bindings = adapter.debug_value_bindings.as_ptr();
    let types = &adapter.value_types[&Value(7)] as *const Type;
    let pure = adapter.pure_callees.get("pure_target").unwrap() as *const String;
    let libm = adapter.libm_pure_callees.get("libm_target").unwrap() as *const String;
    let calls = adapter.eh_info.call_sites.as_ptr();
    let pads = adapter.eh_info.landing_pads.as_ptr();
    let proofs = adapter.proof_ctx.value_proofs[&Value(7)].as_ptr();
    let facts = adapter.proof_ctx.function_facts.as_ptr();
    let predicates = adapter
        .proof_ctx
        .refinement_env
        .retained_identity_view()
        .predicates
        .as_ptr();
    let exact = adapter.exact_module_call_authorizations.as_ptr();
    let external = adapter.declared_external_call_authorizations.as_ptr();
    let expected_proofs = format!("{:?}", adapter.proof_ctx);
    let expected_eh = adapter.eh_info.clone();

    let mut function = Function::new("ownership_boundary", Signature::default());
    let result = adapter.take_output_metadata(&mut function);
    assert_eq!(function.stack_slots.as_ptr(), slots);
    assert_eq!(function.debug_meta.local_variables.as_ptr(), locals);
    assert_eq!(function.debug_value_bindings.as_ptr(), bindings);
    assert_eq!(&function.value_types[&Value(7)] as *const Type, types);
    assert_eq!(
        function.pure_callees.get("pure_target").unwrap() as *const String,
        pure
    );
    assert_eq!(
        function.libm_pure_callees.get("libm_target").unwrap() as *const String,
        libm
    );
    assert_eq!(function.eh_info.call_sites.as_ptr(), calls);
    assert_eq!(function.eh_info.landing_pads.as_ptr(), pads);
    assert_eq!(result.value_proofs[&Value(7)].as_ptr(), proofs);
    assert_eq!(result.function_facts.as_ptr(), facts);
    assert_eq!(
        result
            .refinement_env
            .retained_identity_view()
            .predicates
            .as_ptr(),
        predicates
    );
    assert_eq!(format!("{result:?}"), expected_proofs);
    assert_eq!(function.eh_info, expected_eh);
    assert_eq!(function.stack_slots, [StackSlotInfo::new(16, 8)]);
    assert_eq!(function.debug_meta.local_variables[0].name, "owned_local");
    assert_eq!(function.debug_value_bindings[0].value, Value(7));
    assert_eq!(
        function.value_types[&Value(7)],
        Type::Struct(vec![Type::I64, Type::I32])
    );

    assert!(adapter.stack_slots.is_empty());
    assert!(adapter.debug_local_variables.is_empty());
    assert!(adapter.debug_value_bindings.is_empty());
    assert!(adapter.value_types.is_empty());
    assert!(adapter.pure_callees.is_empty());
    assert!(adapter.libm_pure_callees.is_empty());
    assert!(adapter.eh_info.is_empty());
    assert_eq!(
        format!("{:?}", adapter.proof_ctx),
        format!("{:?}", ProofContext::default())
    );
    assert_eq!(adapter.exact_module_calls_lowered, 1);
    assert_eq!(adapter.declared_external_calls_lowered, 1);
    assert_eq!(adapter.exact_module_call_authorizations.len(), 1);
    assert_eq!(adapter.declared_external_call_authorizations.len(), 1);
    assert_eq!(adapter.exact_module_call_authorizations.as_ptr(), exact);
    assert_eq!(
        adapter.declared_external_call_authorizations.as_ptr(),
        external
    );
    drop(adapter);
    assert_eq!(result.function_facts, [ProofFact::NoPanic]);
    assert_eq!(function.eh_info, expected_eh);
}

#[test]
fn actual_translation_hands_off_final_refinement_and_debug_metadata() {
    let mut builder = trust_ir_build::ModuleBuilder::new("output_handoff");
    let signature = builder.add_func_type(vec![Ty::I64], vec![Ty::I64]);
    let mut function = builder.function("identity", signature);
    let entry = function.create_block();
    let input = function.add_block_param(entry, Ty::I64);
    function.switch_to_block(entry);
    function.ret(vec![input]);
    function.build();
    let mut module = builder.build().expect("ModuleBuilder::build: test fixture");
    let base = module
        .add_type(Ty::I64)
        .expect("Module::add_type: test fixture");
    let predicate = module
        .intern_pred(trust_ir::Pred::Top)
        .expect("Module::intern_pred: test fixture")
        .unwrap();
    let refined = Ty::Refine(base, predicate);
    module.func_types[0].params[0] = refined.clone();
    module.func_types[0].returns[0] = refined.clone();
    module.functions[0].blocks[0].params[0].1 = refined;
    let catalog = Rc::new(ModuleFunctionCatalog::new(&module));
    let mut adapter = TrustIrAdapter::new_with_types(&module.structs, &module.types, catalog);
    adapter.module = Some(&module);
    let (lir, proofs) = adapter.translate(&module.functions[0]).unwrap();
    assert_eq!(
        proofs.proofs_for(&Value(0)),
        &[Proof::Refinement { pred: predicate }]
    );
    assert_eq!(proofs.refinement_env, RefinementEnv::from_module(&module));
    assert_eq!(lir.signature.params, [Type::I64]);
    assert_eq!(lir.signature.returns, [Type::I64]);
    assert_eq!(
        lir.debug_meta.source_file.as_deref(),
        Some("output_handoff.rs")
    );
    assert!(adapter.proof_ctx.value_proofs.is_empty());
    assert_eq!(adapter.proof_ctx.refinement_env, RefinementEnv::default());
    // The public validated wrapper reaches the same completion path, too.
    let (_, wrapped) =
        crate::translate_function_with_license(&module.functions[0], &module, &permit_unlicensed())
            .unwrap();
    assert_eq!(wrapped.proofs_for(&Value(0)), proofs.proofs_for(&Value(0)));
}

#[test]
fn output_compaction_moves_nonclone_payloads_and_releases_row_slack() {
    use std::cell::Cell;
    struct NotClone(Rc<Cell<usize>>);
    impl Drop for NotClone {
        fn drop(&mut self) {
            self.0.set(self.0.get() + 1);
        }
    }
    let drops = Rc::new(Cell::new(0));
    let mut values = Vec::with_capacity(4096);
    for _ in 0..3 {
        values.push(NotClone(drops.clone()));
    }
    compact_output_vec(&mut values);
    assert_eq!(values.capacity(), 3);
    assert_eq!(drops.get(), 0);
    drop(values);
    assert_eq!(drops.get(), 3);
    let mut empty = Vec::<NotClone>::with_capacity(512);
    compact_output_vec(&mut empty);
    assert_eq!(empty.capacity(), 0);

    let mut adapter = TrustIrAdapter::new(&[], HashMap::new());
    adapter.stack_slots = Vec::with_capacity(512);
    adapter.stack_slots.push(StackSlotInfo::new(8, 8));
    let mut row = Vec::with_capacity(512);
    row.push(Proof::Associative);
    adapter.proof_ctx.value_proofs.insert(Value(0), row);
    let mut facts = Vec::with_capacity(512);
    facts.push(ProofFact::NoPanic);
    adapter.proof_ctx.value_facts.insert(Value(0), facts);
    adapter.proof_ctx.function_proofs = Vec::with_capacity(512);
    adapter.proof_ctx.function_proofs.push(Proof::Commutative);
    let mut catches = Vec::with_capacity(512);
    catches.push(0);
    adapter.eh_info.landing_pads = Vec::with_capacity(512);
    adapter.eh_info.landing_pads.push(EhLandingPad {
        block: Block(0),
        catch_type_indices: catches,
        is_cleanup: true,
    });
    let mut function = Function::new("compact_boundary", Signature::default());
    let result = adapter.take_output_metadata(&mut function);
    assert_eq!(function.stack_slots.capacity(), 1);
    assert_eq!(result.value_proofs[&Value(0)].capacity(), 1);
    assert_eq!(result.value_facts[&Value(0)].capacity(), 1);
    assert_eq!(result.function_proofs.capacity(), 1);
    assert_eq!(function.eh_info.landing_pads.capacity(), 1);
    assert_eq!(
        function.eh_info.landing_pads[0]
            .catch_type_indices
            .capacity(),
        1
    );
    assert_eq!(result.value_proofs[&Value(0)], [Proof::Associative]);
    assert_eq!(result.value_facts[&Value(0)], [ProofFact::NoPanic]);
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes because it was silently refused.
fn permit_unlicensed() -> crate::CodegenLicensePolicy {
    crate::CodegenLicensePolicy::default().with_unlicensed(crate::UnlicensedBodyPolicy::Permit)
}
