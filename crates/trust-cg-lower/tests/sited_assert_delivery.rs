// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0
//! Actual source-to-LIR panic ABI/CFG controls; runtime and Rust fidelity are separate.
#[path = "../../trust-cg-codegen/tests/common/panic_delivery_fixture.rs"]
mod fixture;
use fixture::{b, v};
use trust_cg_lower::function::Function;
use trust_cg_lower::instructions::Opcode;
use trust_cg_lower::{CodegenLicensePolicy, UnlicensedBodyPolicy, translate_function_with_license};
use trust_ir::value::GlobalId;
use trust_ir::{
    AssertKind, AssertOverflowOp, CallingConv, Endianness, FuncId, Inst, InstrNode, Module,
    PanicLocation, StructPassingPolicy, TargetInfo, Ty,
};

/// The shared fixture pinned to the target these controls lower for. Its
/// C-convention `tc_check` fails into the `extern "Rust"` entry: a
/// cross-convention panic-site edge, which trust-ir counts as an FFI boundary
/// and refuses without a pinned target (`TargetInfoRequired`). The controls
/// select AArch64 with the default Mach-O TLS dialect, so the pin is
/// `aarch64-apple-darwin`.
fn module(kind: AssertKind, invoke: bool, global: bool) -> Module {
    let mut m = fixture::module(kind, invoke, global);
    m.target_info = Some(TargetInfo {
        triple: "aarch64-apple-darwin".into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: None,
        struct_passing: StructPassingPolicy::NativeC,
    });
    m
}

fn bounds() -> AssertKind {
    AssertKind::BoundsCheck {
        index: v(1),
        len: v(2),
    }
}
/// The fixture is hand-built and carries no codegen license (`body_gate:
/// None`), which the default policy refuses (DG-73; `v41_codegen_license.rs`
/// keeps that refusal for this very fixture). These controls state the test
/// policy explicitly, so every refusal below is the panic-delivery rule's,
/// never the license's.
fn permit_unlicensed() -> CodegenLicensePolicy {
    CodegenLicensePolicy::default().with_unlicensed(UnlicensedBodyPolicy::Permit)
}
fn lower(m: &Module) -> Function {
    let before = m.clone();
    let errors = trust_ir_build::validate_module(m);
    assert!(
        errors.is_empty(),
        "the fixture must be valid TrustIR: {errors:?}"
    );
    let lir = translate_function_with_license(&m.functions[0], m, &permit_unlicensed())
        .expect("valid panic delivery")
        .0;
    assert_eq!(m, &before, "lowering cannot restamp source authority");
    lir
}
fn refuse(m: &Module) {
    let before = m.clone();
    assert!(translate_function_with_license(&m.functions[0], m, &permit_unlicensed()).is_err());
    assert_eq!(m, &before);
}

#[test]
fn failure_uses_exact_ordered_payload_and_location_only_after_brif() {
    let m = module(bounds(), false, false);
    let lir = lower(&m);
    let entry = &lir.blocks[&lir.entry_block];
    let Opcode::Brif {
        cond,
        then_dest,
        else_dest,
    } = entry.instructions[0].opcode
    else {
        panic!("source assertion must branch")
    };
    assert_eq!(cond, entry.params[0].0);
    assert_eq!(
        entry.instructions.len(),
        1,
        "no passing-path call/location access"
    );
    let failure = &lir.blocks[&else_dest];
    assert!(
        matches!(&failure.instructions[0].opcode, Opcode::Call { name, .. }
        if name == "panic_delivery_entry")
    );
    assert_eq!(
        failure.instructions[0].args,
        vec![entry.params[1].0, entry.params[2].0, entry.params[3].0]
    );
    assert!(matches!(failure.instructions[1].opcode, Opcode::Trap));
    assert!(matches!(
        lir.blocks[&then_dest].instructions[0].opcode,
        Opcode::Return
    ));
    assert!(!lir.pure_callees.contains("panic_delivery_entry"));
}

#[test]
fn immutable_global_location_resolves_in_failure_block_not_passing_block() {
    let lir = lower(&module(bounds(), false, true));
    let entry = &lir.blocks[&lir.entry_block];
    let Opcode::Brif { else_dest, .. } = entry.instructions[0].opcode else {
        panic!()
    };
    let fail = &lir.blocks[&else_dest];
    assert_eq!(entry.instructions.len(), 1);
    assert!(
        matches!(&fail.instructions[0].opcode, Opcode::GlobalRef { name, .. }
        if name == "panic_delivery_location")
    );
    assert!(matches!(fail.instructions[1].opcode, Opcode::Call { .. }));
    assert_eq!(
        fail.instructions[1].args[2],
        fail.instructions[0].results[0]
    );
    assert!(matches!(fail.instructions[2].opcode, Opcode::Trap));
}

#[test]
fn zero_payload_kinds_keep_exact_entry_and_one_location_argument() {
    for kind in [
        AssertKind::DivByZero,
        AssertKind::RemByZero,
        AssertKind::NullPtr,
        AssertKind::Overflow(AssertOverflowOp::Add),
        AssertKind::Overflow(AssertOverflowOp::Sub),
        AssertKind::Overflow(AssertOverflowOp::Mul),
    ] {
        let lir = lower(&module(kind, false, false));
        let calls: Vec<_> = lir
            .blocks
            .values()
            .flat_map(|b| &b.instructions)
            .filter(|i| matches!(i.opcode, Opcode::Call { .. }))
            .collect();
        assert_eq!(calls.len(), 1);
        assert_eq!(
            calls[0].args,
            vec![lir.blocks[&lir.entry_block].params[3].0]
        );
    }
}

#[test]
fn misalignment_operand_order_and_rust_scalar_call_convention_are_retained() {
    let lir = lower(&module(
        AssertKind::MisalignedPtr {
            required: v(2),
            found: v(1),
        },
        false,
        false,
    ));
    let entry = &lir.blocks[&lir.entry_block];
    let call = lir
        .blocks
        .values()
        .flat_map(|b| &b.instructions)
        .find(|i| matches!(i.opcode, Opcode::Call { .. }))
        .unwrap();
    assert_eq!(
        call.args,
        vec![entry.params[2].0, entry.params[1].0, entry.params[3].0]
    );
}

#[test]
fn assert_invoke_isolated_failure_retains_pad_and_passing_phi_edge() {
    let lir = lower(&module(bounds(), true, false));
    let entry = &lir.blocks[&lir.entry_block];
    let Opcode::Brif {
        then_dest,
        else_dest,
        ..
    } = entry.instructions[0].opcode
    else {
        panic!()
    };
    let fail = &lir.blocks[&else_dest];
    let Opcode::Invoke {
        normal_dest,
        unwind_dest,
        binding: _,
        ref name,
    } = fail.instructions[0].opcode
    else {
        panic!()
    };
    assert_eq!(name, "panic_delivery_entry");
    assert_eq!(
        fail.instructions[0].args,
        vec![entry.params[1].0, entry.params[2].0, entry.params[3].0]
    );
    assert!(matches!(
        lir.blocks[&normal_dest].instructions[0].opcode,
        Opcode::Trap
    ));
    assert!(matches!(
        lir.blocks[&unwind_dest].instructions[0].opcode,
        Opcode::LandingPad { .. }
    ));
    assert_eq!(lir.eh_info.call_sites.len(), 1);
    assert_eq!(lir.eh_info.call_sites[0].call_block, else_dest);
    assert_eq!(lir.eh_info.call_sites[0].landing_pad_block, unwind_dest);
    let pass = &lir.blocks[&then_dest];
    assert!(matches!(pass.instructions[0].opcode, Opcode::Copy));
    assert_eq!(pass.instructions[0].args, vec![entry.params[2].0]);
    assert!(matches!(
        pass.instructions.last().unwrap().opcode,
        Opcode::Jump { .. }
    ));
}

#[test]
fn missing_or_duplicate_entry_and_undefined_location_refuse() {
    let mut m = module(bounds(), false, false);
    m.functions.pop();
    refuse(&m);
    let mut m = module(bounds(), false, false);
    m.functions.push(m.functions[1].clone());
    refuse(&m);
    let mut m = module(bounds(), false, false);
    if let Inst::Assert {
        site: Some(site), ..
    } = &mut m.functions[0].blocks[0].body[0].inst
    {
        site.location = PanicLocation::Value(v(999));
    }
    refuse(&m);
}

#[test]
fn entry_returns_variadic_wrong_payload_and_wrong_location_types_refuse() {
    for mutate in 0..4 {
        let mut m = module(bounds(), false, false);
        let ty = m.functions[1].ty.as_usize();
        match mutate {
            0 => m.func_types[ty].returns.push(Ty::Usize),
            1 => m.func_types[ty].is_vararg = true,
            2 => m.func_types[ty].params[0] = Ty::U64,
            3 => m.func_types[ty].params[2] = Ty::Usize,
            _ => unreachable!(),
        }
        refuse(&m);
    }
}

#[test]
fn mutable_tls_and_missing_location_globals_refuse() {
    let mut m = module(bounds(), false, true);
    m.globals[0].mutable = true;
    refuse(&m);
    let mut m = module(bounds(), false, true);
    m.globals[0].tls = Some(trust_ir::TlsModel::GeneralDynamic);
    refuse(&m);
    let mut m = module(bounds(), false, true);
    m.globals.clear();
    refuse(&m);
}

#[test]
fn direct_globaladdr_must_use_canonical_global_site_instead_of_value() {
    let mut m = module(bounds(), false, true);
    if let Inst::Assert {
        site: Some(site), ..
    } = &mut m.functions[0].blocks[0].body[0].inst
    {
        site.location = PanicLocation::Value(v(8));
    }
    m.functions[0].blocks[0].body.insert(
        0,
        InstrNode::new(Inst::GlobalAddr {
            global: GlobalId::new(0),
        })
        .with_result(v(8)),
    );
    refuse(&m);
}

#[test]
fn arbitrary_intrinsic_name_cannot_replace_panic_runtime_call() {
    let mut m = module(bounds(), false, false);
    m.functions[1].name = "memset".into();
    refuse(&m);
}

#[test]
fn unsited_unspecified_byval_and_sret_cannot_acquire_panic_delivery() {
    let mut m = module(bounds(), false, false);
    if let Inst::Assert { site, .. } = &mut m.functions[0].blocks[0].body[0].inst {
        *site = None;
    }
    refuse(&m);
    refuse(&module(AssertKind::Unspecified, false, false));
    for sret in [false, true] {
        let mut m = module(bounds(), false, false);
        m.functions[1].attrs.params = vec![trust_ir::ParamAttrs::default(); 3];
        if sret {
            m.functions[1].attrs.params[2].sret = true;
        } else {
            m.functions[1].attrs.params[2].byval = true;
        }
        refuse(&m);
    }
}

#[test]
fn wrong_condition_payload_dominance_and_unwind_edges_refuse() {
    let mut m = module(bounds(), false, false);
    if let Inst::Assert { cond, .. } = &mut m.functions[0].blocks[0].body[0].inst {
        *cond = v(1);
    }
    refuse(&m);
    let mut m = module(
        AssertKind::BoundsCheck {
            index: v(99),
            len: v(2),
        },
        false,
        false,
    );
    refuse(&m);
    m = module(bounds(), true, false);
    if let Inst::AssertInvoke { unwind_dest, .. } = &mut m.functions[0].blocks[0].body[0].inst {
        *unwind_dest = b(1);
    }
    refuse(&m);
}

#[test]
fn unsupported_entry_convention_and_weak_binding_fail_closed() {
    let mut m = module(bounds(), false, false);
    m.functions[1].calling_conv = CallingConv::RustCold;
    refuse(&m);
    let mut m = module(bounds(), false, false);
    m.functions[1].linkage = trust_ir::Linkage::ExternalWeak;
    refuse(&m);
}

#[test]
fn multiple_assertions_have_distinct_terminal_failure_and_continuation_blocks() {
    let mut m = module(bounds(), false, false);
    let check = m.functions[0].blocks[0].body[0].clone();
    m.functions[0].blocks[0].body.insert(1, check);
    let lir = lower(&m);
    assert_eq!(
        lir.blocks
            .values()
            .flat_map(|b| &b.instructions)
            .filter(|i| matches!(i.opcode, Opcode::Call { .. }))
            .count(),
        2
    );
    assert_eq!(
        lir.blocks
            .values()
            .flat_map(|b| &b.instructions)
            .filter(|i| matches!(i.opcode, Opcode::Brif { .. }))
            .count(),
        2
    );
}

#[test]
fn genuine_direct_slot_fact_agrees_only_on_actual_panic_scalar_pointer_signature() {
    let mut m = module(bounds(), false, false);
    m.functions[1].attrs.params = vec![
        trust_ir::ParamAttrs {
            pass: Some(trust_ir::PassMode::Direct),
            ..Default::default()
        };
        3
    ];
    lower(&m);
    m.functions[1].attrs.params[2].pass = Some(trust_ir::PassMode::Pair);
    refuse(&m);
    m.functions[1].attrs.params[2].pass = Some(trust_ir::PassMode::Ignore);
    refuse(&m);
    m.functions[1].attrs.params[2].pass = Some(trust_ir::PassMode::Direct);
    m.functions[0].blocks[0].body[0] = InstrNode::new(Inst::Call {
        callee: FuncId::new(1),
        args: vec![v(1), v(2), v(3)],
    });
    refuse(&m); // The unrelated ordinary stated-pass floor stays unchanged.
}

#[test]
fn strict_invoke_cannot_erase_authenticated_external_call_binding() {
    let m = module(bounds(), true, false);
    let report = trust_ir_build::validate_module_report(&m);
    assert!(report.is_ok());
    let (functions, receipt) =
        trust_cg_lower::translate_validated_module_strict_for_arch_with_tls_and_validation_with_license(
            &report,
            trust_cg_lower::GuardCarrierArch::AArch64,
            trust_cg_lower::TlsDialect::default(),
            &permit_unlicensed(),
        )
        .expect("strict Invoke retains the authenticated carrier");
    assert_eq!(receipt.declared_external_call_count(), 1);
    receipt
        .replay_strict_call_bindings_exhaustive(&functions)
        .unwrap();
    let invoke = functions
        .iter()
        .flat_map(|(f, _)| f.blocks.values())
        .flat_map(|b| &b.instructions)
        .find(|i| matches!(i.opcode, Opcode::Invoke { .. }))
        .unwrap();
    assert!(matches!(
        invoke.opcode,
        Opcode::Invoke {
            binding: trust_cg_lower::instructions::DirectCallBinding::DeclaredExternalFunction {
                function: 1
            },
            ..
        }
    ));
    let mut selector = trust_cg_lower::isel::InstructionSelector::new(
        "unclosed imported invoke".into(),
        functions[0].0.signature.clone(),
    );
    selector.set_abi_variant(trust_cg_lower::abi::AArch64AbiVariant::Aapcs64);
    let entry = trust_cg_lower::instructions::Block(0);
    assert!(
        selector
            .select_block(entry, std::slice::from_ref(invoke))
            .is_err(),
        "an identity carrier alone cannot authorize runtime resolution"
    );
}
