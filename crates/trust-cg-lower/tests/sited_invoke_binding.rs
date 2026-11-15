// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0
//! Exact Invoke carrier/replay controls; these do not certify runtime or Rust fidelity.
#[path = "../../trust-cg-codegen/tests/common/panic_delivery_fixture.rs"]
mod fixture;
use trust_cg_lower::adapter::ProofContext;
use trust_cg_lower::function::{Function, Signature};
use trust_cg_lower::instructions::{Block, DirectCallBinding, Instruction, Opcode};
use trust_cg_lower::static_call_devirtualization::ModuleTranslationValidationReport;
use trust_cg_lower::{CodegenLicensePolicy, GuardCarrierArch, TlsDialect, UnlicensedBodyPolicy};
use trust_ir::{
    AssertKind, Endianness, Inst, InstrNode, Linkage, Module, StructPassingPolicy, TargetInfo,
};

type Lowered = Vec<(Function, ProofContext)>;
/// The shared fixture, pinned: its C-convention `tc_check` fails into the
/// `extern "Rust"` entry, a cross-convention panic-site edge that trust-ir
/// counts as an FFI boundary and refuses without a pinned target
/// (`TargetInfoRequired`). These controls select AArch64 with the default
/// Mach-O TLS dialect, so the pin is `aarch64-apple-darwin`.
fn source(local: bool, global: bool) -> Module {
    let mut m = fixture::module(
        AssertKind::BoundsCheck {
            index: fixture::v(1),
            len: fixture::v(2),
        },
        true,
        global,
    );
    m.target_info = Some(TargetInfo {
        triple: "aarch64-apple-darwin".into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: None,
        struct_passing: StructPassingPolicy::NativeC,
    });
    if local {
        m.functions[1].linkage = Linkage::Internal;
        let mut block = trust_ir::Block::new(fixture::b(0));
        block.params = vec![
            (fixture::v(10), trust_ir::Ty::Usize),
            (fixture::v(11), trust_ir::Ty::Usize),
            (fixture::v(12), trust_ir::Ty::Ptr),
        ];
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        m.functions[1].blocks.push(block);
    }
    m
}
/// The fixture is hand-built and carries no codegen license (`body_gate:
/// None`), which the default policy refuses (DG-73). These controls state the
/// test policy explicitly, so a refusal below is never the license's.
fn permit_unlicensed() -> CodegenLicensePolicy {
    CodegenLicensePolicy::default().with_unlicensed(UnlicensedBodyPolicy::Permit)
}
fn strict(m: &Module) -> (Lowered, ModuleTranslationValidationReport<'_>) {
    let errors = trust_ir_build::validate_module(m);
    assert!(
        errors.is_empty(),
        "the fixture must be valid TrustIR: {errors:?}"
    );
    trust_cg_lower::translate_module_strict_for_arch_with_tls_and_validation_with_license(
        m,
        GuardCarrierArch::AArch64,
        TlsDialect::default(),
        &permit_unlicensed(),
    )
    .unwrap()
}
fn invoke_mut(functions: &mut Lowered) -> &mut Instruction {
    functions
        .iter_mut()
        .flat_map(|(f, _)| f.blocks.values_mut())
        .flat_map(|b| &mut b.instructions)
        .find(|i| matches!(i.opcode, Opcode::Invoke { .. }))
        .unwrap()
}

#[test]
fn strict_panic_invoke_retains_exact_local_entry_and_failure_only_global_location() {
    let m = source(true, true);
    let before = m.clone();
    let (mut functions, receipt) = strict(&m);
    assert_eq!(m, before);
    assert_eq!(receipt.exact_module_call_count(), 1);
    receipt
        .replay_strict_call_bindings_exhaustive(&functions)
        .unwrap();
    let invoke = invoke_mut(&mut functions);
    assert!(matches!(&invoke.opcode, Opcode::Invoke { name, binding:
        DirectCallBinding::ExactModuleFunction { function: 1 }, .. }
        if name == "panic_delivery_entry"));
    let caller = &functions[0].0;
    let entry = &caller.blocks[&caller.entry_block];
    assert_eq!(entry.instructions.len(), 1);
    let Opcode::Brif { else_dest, .. } = entry.instructions[0].opcode else {
        panic!();
    };
    let fail = &caller.blocks[&else_dest];
    assert!(matches!(
        fail.instructions[0].opcode,
        Opcode::GlobalRef { .. }
    ));
    assert_eq!(
        fail.instructions[1].args[2],
        fail.instructions[0].results[0]
    );
    let Opcode::Invoke {
        unwind_dest,
        normal_dest,
        ..
    } = fail.instructions[1].opcode
    else {
        panic!();
    };
    assert!(matches!(
        caller.blocks[&normal_dest].instructions[0].opcode,
        Opcode::Trap
    ));
    assert_eq!(caller.eh_info.call_sites[0].landing_pad_block, unwind_dest);
}

#[test]
fn local_invoke_binding_name_operands_and_both_eh_edges_are_receipt_authenticated() {
    let m = source(true, false);
    for mutation in 0..6 {
        let (mut functions, receipt) = strict(&m);
        receipt
            .replay_strict_call_bindings_exhaustive(&functions)
            .unwrap();
        let invoke = invoke_mut(&mut functions);
        let Opcode::Invoke {
            binding,
            name,
            normal_dest,
            unwind_dest,
        } = &mut invoke.opcode
        else {
            panic!();
        };
        match mutation {
            0 => *binding = DirectCallBinding::Interposable,
            1 => *binding = DirectCallBinding::ExactModuleFunction { function: 0 },
            2 => *name = "same_leaf_foreign_entry".into(),
            3 => *normal_dest = Block(999),
            4 => *unwind_dest = Block(999),
            _ => invoke.args.swap(0, 1),
        }
        assert!(
            receipt
                .replay_strict_call_bindings_exhaustive(&functions)
                .is_err()
        );
    }
}

#[test]
fn strict_imported_invoke_pending_identity_and_source_origin_cannot_be_rewritten() {
    let m = source(false, false);
    for mutation in 0..4 {
        let (mut functions, receipt) = strict(&m);
        assert_eq!(receipt.declared_external_call_count(), 1);
        receipt
            .replay_strict_call_bindings_exhaustive(&functions)
            .unwrap();
        if mutation == 3 {
            for (f, _) in &mut functions {
                for origins in f.trust_ir_origins.values_mut() {
                    origins.fill(None);
                }
            }
        } else {
            let invoke = invoke_mut(&mut functions);
            let Opcode::Invoke { binding, .. } = &mut invoke.opcode else {
                panic!();
            };
            *binding = match mutation {
                0 => DirectCallBinding::Interposable,
                1 => DirectCallBinding::DeclaredExternalFunction { function: 0 },
                _ => DirectCallBinding::NativeDependency {
                    function: 1,
                    dependency: trust_cg_ir::NativeDependencyId::new(9),
                },
            };
        }
        assert!(
            receipt
                .replay_strict_call_bindings_exhaustive(&functions)
                .is_err()
        );
    }
}

#[test]
fn extra_unreported_strict_invoke_is_not_authenticated_by_another_receipt() {
    let m = source(true, false);
    let (mut functions, receipt) = strict(&m);
    let extra = invoke_mut(&mut functions).clone();
    let caller = &mut functions[0].0;
    let entry = caller.entry_block;
    caller
        .blocks
        .get_mut(&entry)
        .unwrap()
        .instructions
        .insert(0, extra);
    assert!(
        receipt
            .replay_strict_call_bindings_exhaustive(&functions)
            .is_err()
    );
}

fn bare(binding: DirectCallBinding) -> Instruction {
    Instruction {
        opcode: Opcode::Invoke {
            name: "owned_entry".into(),
            binding,
            normal_dest: Block(1),
            unwind_dest: Block(2),
        },
        args: vec![],
        results: vec![],
    }
}
fn signature() -> Signature {
    Signature {
        params: vec![],
        returns: vec![],
    }
}

/// Both selectors spell the exact binding of an Invoke the way they spell an
/// exact plain `Call`: the direct call names the plain symbol and carries the
/// exact-module-call bit (AArch64 `BL` with `exact_module_call`, which
/// `to_ir_func` turns into `InstFlags::EXACT_MODULE_CALL`; x86-64 `CALL` with
/// that flag). `ExactModuleSymbol` is the operand of a function ADDRESS
/// (`FunctionAddr`), never of a call. Returns, per selector, whether the
/// selected `owned_entry` call carries the bit, after checking both EH
/// successors and the landing pad.
fn exact_call_bit_after_both_selectors(binding: DirectCallBinding) -> (bool, bool) {
    let i = bare(binding);
    let mut a = trust_cg_lower::isel::InstructionSelector::new("caller".into(), signature());
    a.set_abi_variant(trust_cg_lower::abi::AArch64AbiVariant::Aapcs64);
    a.select_block(Block(0), std::slice::from_ref(&i)).unwrap();
    let a = a.finalize();
    let a_calls: Vec<_> = a.blocks[&Block(0)]
        .insts
        .iter()
        .filter(|inst| inst.opcode == trust_cg_lower::isel::AArch64Opcode::Bl)
        .collect();
    assert!(
        matches!(a_calls.as_slice(), [call] if matches!(call.operands.as_slice(),
            [trust_cg_lower::isel::ISelOperand::Symbol(s)] if s == "owned_entry")),
        "{a_calls:?}"
    );
    assert!(a.blocks[&Block(0)].successors.contains(&Block(1)));
    assert!(a.blocks[&Block(0)].successors.contains(&Block(2)));
    assert_eq!(a.eh_info.call_sites[0].landing_pad_block, Block(2));
    let mut x =
        trust_cg_lower::x86_64_isel::X86InstructionSelector::new("caller".into(), signature());
    x.select_block(Block(0), std::slice::from_ref(&i)).unwrap();
    let x = x.finalize();
    let x_calls: Vec<_> = x.blocks[&Block(0)]
        .insts
        .iter()
        .filter(|inst| inst.opcode == trust_cg_ir::x86_64_ops::X86Opcode::Call)
        .collect();
    assert!(
        matches!(x_calls.as_slice(), [call] if matches!(call.operands.as_slice(),
            [trust_cg_lower::x86_64_isel::X86ISelOperand::Symbol(s)] if s == "owned_entry")),
        "{x_calls:?}"
    );
    assert!(x.blocks[&Block(0)].successors.contains(&Block(1)));
    assert!(x.blocks[&Block(0)].successors.contains(&Block(2)));
    assert_eq!(x.eh_info.call_sites[0].landing_pad_block, Block(2));
    (
        a_calls[0].exact_module_call,
        x_calls[0]
            .flags
            .contains(trust_cg_ir::InstFlags::EXACT_MODULE_CALL),
    )
}

#[test]
fn both_selectors_keep_exact_symbol_binding_and_original_eh_successors() {
    assert_eq!(
        exact_call_bit_after_both_selectors(DirectCallBinding::ExactModuleFunction {
            function: 17
        }),
        (true, true),
        "an exact module binding reaches both selected calls"
    );
    assert_eq!(
        exact_call_bit_after_both_selectors(DirectCallBinding::Interposable),
        (false, false),
        "the negative twin: an interposable Invoke carries no exact binding"
    );
}

#[test]
fn pending_or_premature_native_invoke_never_selects_an_interposable_call() {
    for binding in [
        DirectCallBinding::DeclaredExternalFunction { function: 17 },
        DirectCallBinding::NativeDependency {
            function: 17,
            dependency: trust_cg_ir::NativeDependencyId::new(2),
        },
    ] {
        let i = bare(binding);
        let mut a = trust_cg_lower::isel::InstructionSelector::new("caller".into(), signature());
        a.set_abi_variant(trust_cg_lower::abi::AArch64AbiVariant::Aapcs64);
        assert!(a.select_block(Block(0), std::slice::from_ref(&i)).is_err());
        let mut x =
            trust_cg_lower::x86_64_isel::X86InstructionSelector::new("caller".into(), signature());
        assert!(x.select_block(Block(0), std::slice::from_ref(&i)).is_err());
    }
}

#[test]
fn malformed_actual_entry_abi_and_missing_site_still_refuse_strict_panic_invoke() {
    for mutation in 0..3 {
        let mut m = source(false, false);
        match mutation {
            0 => m.functions[1].calling_conv = trust_ir::CallingConv::RustCold,
            1 => m.func_types[m.functions[1].ty.index() as usize]
                .returns
                .push(trust_ir::Ty::Usize),
            _ => {
                let Inst::AssertInvoke { site, .. } = &mut m.functions[0].blocks[0].body[0].inst
                else {
                    panic!();
                };
                // At this trust-ir pin `AssertInvoke.site` is not optional (a
                // missing site is unrepresentable); the nearest malformed
                // site names an entry the module does not define.
                site.entry = trust_ir::FuncId::new(99);
            }
        }
        assert!(
            trust_cg_lower::translate_module_strict_for_arch_with_tls_and_validation_with_license(
                &m,
                GuardCarrierArch::AArch64,
                TlsDialect::default(),
                &permit_unlicensed(),
            )
            .is_err()
        );
    }
}
