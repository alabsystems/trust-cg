// trust-ir v43 NOMINAL OPAQUE RUNTIME HANDLES at the adapter boundary.
//
// A `Ty::Handle(HandleTy { name, runtime })` is ONE POINTER WORD that is
// deliberately NOT pointer-like and never equal to `Ty::Ptr`. trust-ir-build
// permits exact-typed TRANSPORT only, with the bodyless `External` C
// declarations in `TRUSTED_HANDLE_RUNTIMES` as the ONLY origins. This backend
// admits a strict subset: the transport that reaches a PINNED entry point.
//
// One module shape is the POSITIVE control — two pinned `trust_bignum::Nat`
// declarations and a local body that calls them and returns the handle, which
// must lower on every native entry. Every other test takes that exact module
// and changes ONE thing, so each refusal is attributed to one construct.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use std::collections::HashMap;

use trust_cg_lower::adapter::AdapterError;
use trust_cg_lower::instructions::Opcode;
use trust_cg_lower::{
    GuardCarrierArch, TlsDialect, prepare_module_for_lir, refuse_handle_surface,
    reject_unconsumed_v41_surface, reject_unconsumed_v41_target_neutral_surface, translate_type,
    translate_type_with_tables,
};
use trust_ir::{
    Block, BlockId, CallingConv, Constant, FieldDef, FuncId, FuncTy, Function, Global, Inst,
    InstrNode, Linkage, Module, StructDef, StructId, Ty, ValueId, Visibility,
};

#[path = "common/typed_refusal.rs"]
mod typed_refusal;
use typed_refusal::assert_typed_const_refusal;

/// The pinned `trust_bignum::Nat` handle — the one trusted runtime row at this
/// trust-ir pin (`trust_ir_build::validate::TRUSTED_HANDLE_RUNTIMES`).
fn nat() -> Ty {
    Ty::handle("Nat", "trust_bignum::Nat")
}

const FROM_U64: &str = "trust_bignum_nat_from_u64";
const ADD: &str = "trust_bignum_nat_add";

/// A bodyless `External` C declaration: the only shape a handle origin has.
fn declaration(id: u32, name: &str, ty: trust_ir::FuncTyId) -> Function {
    let mut function = Function::new(FuncId::new(id), name, ty, BlockId::new(0));
    function.linkage = Linkage::External;
    function.calling_conv = CallingConv::C;
    function.blocks.clear();
    function
}

/// THE POSITIVE CONTROL.
///
/// ```text
/// declare C fn trust_bignum_nat_from_u64(u64)  -> handle<Nat>
/// declare C fn trust_bignum_nat_add(handle<Nat>, handle<Nat>) -> handle<Nat>
/// fn sum(a: u64, b: u64) -> handle<Nat> {
///   %2 = call from_u64(a); %3 = call from_u64(b); %4 = call add(%2, %3); ret %4
/// }
/// ```
fn pinned_runtime_module() -> Module {
    let mut module = Module::new("v43_opaque_handle");
    // trust-ir requires target info at a bodyless external declaration
    // boundary (`TargetInfoRequired`), and every handle origin IS one.
    module.target_info = Some(trust_ir::TargetInfo {
        triple: "aarch64-apple-darwin".into(),
        pointer_size: 8,
        endianness: trust_ir::Endianness::Little,
        abi: None,
        struct_passing: Default::default(),
    });
    let from_u64_ty = module
        .add_func_type(FuncTy {
            params: vec![Ty::U64],
            returns: vec![nat()],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let add_ty = module
        .add_func_type(FuncTy {
            params: vec![nat(), nat()],
            returns: vec![nat()],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let sum_ty = module
        .add_func_type(FuncTy {
            params: vec![Ty::U64, Ty::U64],
            returns: vec![nat()],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    module.functions.push(declaration(0, FROM_U64, from_u64_ty));
    module.functions.push(declaration(1, ADD, add_ty));

    let mut sum = Function::new(FuncId::new(2), "sum", sum_ty, BlockId::new(0));
    let mut block = Block::new(BlockId::new(0));
    block.params.push((ValueId::new(0), Ty::U64));
    block.params.push((ValueId::new(1), Ty::U64));
    block.body.push(
        InstrNode::new(Inst::Call {
            callee: FuncId::new(0),
            args: vec![ValueId::new(0)],
        })
        .with_result(ValueId::new(2)),
    );
    block.body.push(
        InstrNode::new(Inst::Call {
            callee: FuncId::new(0),
            args: vec![ValueId::new(1)],
        })
        .with_result(ValueId::new(3)),
    );
    block.body.push(
        InstrNode::new(Inst::Call {
            callee: FuncId::new(1),
            args: vec![ValueId::new(2), ValueId::new(3)],
        })
        .with_result(ValueId::new(4)),
    );
    block.body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(4)],
    }));
    sum.blocks.push(block);
    module.functions.push(sum);
    module
}

/// Every module entry point must agree; a refusal only one of them enforces is
/// a bypass. Returns the compatibility entry's error.
fn refuse_everywhere(module: &Module) -> AdapterError {
    let compat = permit_translate_module(module).expect_err("translate_module must refuse");
    trust_cg_lower::translate_module_for_arch_with_tls_and_validation_with_license(
        module,
        GuardCarrierArch::AArch64,
        TlsDialect::default(),
        &permit_unlicensed(),
    )
    .expect_err("validated compatibility entry must refuse");
    prepare_module_for_lir(module, GuardCarrierArch::AArch64)
        .expect_err("prepare_module_for_lir must refuse");
    reject_unconsumed_v41_target_neutral_surface(module).expect_err("the shared floor must refuse");
    for arch in [
        GuardCarrierArch::AArch64,
        GuardCarrierArch::X86_64,
        GuardCarrierArch::Riscv64,
    ] {
        reject_unconsumed_v41_surface(module, arch).expect_err("every arch floor must refuse");
    }
    trust_cg_lower::validate_codegen_metadata_with_license(module, &permit_unlicensed())
        .expect_err("the codegen-metadata entry must refuse");
    if let Some(function) = module.functions.iter().find(|f| !f.blocks.is_empty()) {
        trust_cg_lower::translate_function_with_license(function, module, &permit_unlicensed())
            .expect_err("translate_function must refuse");
        trust_cg_lower::translate_function_with_names_and_license(
            function,
            module,
            &HashMap::new(),
            &permit_unlicensed(),
        )
        .expect_err("the named single-function entry must refuse");
    }
    // The strict, already-validated entry (Core admission) reuses the full
    // validation report and skips the compatibility prerequisites, so it has to
    // run this gate itself.
    let report = trust_ir_build::validate_module_report(module);
    if report.is_ok() {
        trust_cg_lower::translate_validated_module_strict_for_arch_with_tls_and_validation_with_license(
            &report,
            GuardCarrierArch::AArch64,
            TlsDialect::default(),
            &permit_unlicensed(),
        )
        .expect_err("validated strict entry must refuse");
    }
    compat
}

fn accept_everywhere(module: &Module) {
    permit_translate_module(module).expect("translate_module must accept the control");
    prepare_module_for_lir(module, GuardCarrierArch::AArch64)
        .expect("prepare_module_for_lir must accept the control");
    reject_unconsumed_v41_target_neutral_surface(module)
        .expect("the shared floor must accept the control");
    trust_cg_lower::validate_codegen_metadata_with_license(module, &permit_unlicensed())
        .expect("the codegen-metadata entry must accept the control");
}

// ---------------------------------------------------------------------------
// POSITIVE: transport to a pinned runtime lowers
// ---------------------------------------------------------------------------

/// The control is valid trust-ir under the PRODUCER's own v43 rules, so a
/// refusal below can never be generic IR invalidity wearing a handle message.
#[test]
fn the_pinned_runtime_control_is_valid_trust_ir() {
    let module = pinned_runtime_module();
    let report = trust_ir_build::validate_module_report(&module);
    assert!(
        report.is_ok(),
        "the positive control must satisfy trust-ir-build's own handle rules: {:?}",
        report.into_errors()
    );
}

#[test]
fn a_pinned_runtime_call_over_a_handle_lowers_on_every_native_entry() {
    let module = pinned_runtime_module();
    accept_everywhere(&module);

    let lowered = permit_translate_module_for_arch(&module, GuardCarrierArch::AArch64)
        .expect("the pinned-runtime transport lowers");
    // Only the body is lowered; the two declarations are not codegen subjects.
    assert_eq!(lowered.len(), 1, "one body, two declarations");
    let (function, _) = &lowered[0];
    assert_eq!(function.name, "sum");
    assert_eq!(function.blocks.len(), 1, "the control body is one block");
    let calls: Vec<&String> = function
        .blocks
        .values()
        .flat_map(|block| &block.instructions)
        .filter_map(|inst| match &inst.opcode {
            Opcode::Call { name, .. } => Some(name),
            _ => None,
        })
        .collect();
    assert_eq!(
        calls,
        vec![FROM_U64, FROM_U64, ADD],
        "every handle edge is a direct call to the pinned runtime symbol"
    );
}

/// The REST of the admitted transport set, all in one body so a single lowering
/// proves every admitted opcode emits: `Copy`, `Select` on a `Bool`, a branch
/// edge into a handle-typed block parameter, and `Return`. trust-ir-build's
/// rule 7 permits exactly these alongside the call edge; a backend that
/// admitted the call but refused the rest would not be able to lower any real
/// runtime body.
#[test]
fn copy_select_and_a_branch_edge_over_a_handle_all_lower() {
    let mut module = pinned_runtime_module();
    let pick_ty = module
        .add_func_type(FuncTy {
            params: vec![nat(), nat(), Ty::Bool],
            returns: vec![nat()],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut pick = Function::new(FuncId::new(3), "pick", pick_ty, BlockId::new(0));
    let mut entry = Block::new(BlockId::new(0));
    entry.params.push((ValueId::new(0), nat()));
    entry.params.push((ValueId::new(1), nat()));
    entry.params.push((ValueId::new(2), Ty::Bool));
    entry.body.push(
        InstrNode::new(Inst::Copy {
            ty: nat(),
            operand: ValueId::new(0),
        })
        .with_result(ValueId::new(3)),
    );
    entry.body.push(
        InstrNode::new(Inst::Select {
            ty: nat(),
            cond: ValueId::new(2),
            then_val: ValueId::new(3),
            else_val: ValueId::new(1),
        })
        .with_result(ValueId::new(4)),
    );
    entry.body.push(InstrNode::new(Inst::Br {
        target: BlockId::new(1),
        args: vec![ValueId::new(4)],
    }));
    let mut join = Block::new(BlockId::new(1));
    join.params.push((ValueId::new(5), nat()));
    join.body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(5)],
    }));
    pick.blocks.push(entry);
    pick.blocks.push(join);
    module.functions.push(pick);

    let report = trust_ir_build::validate_module_report(&module);
    assert!(
        report.is_ok(),
        "the transport body must satisfy trust-ir-build's rule 7: {:?}",
        report.into_errors()
    );
    accept_everywhere(&module);
    let lowered = permit_translate_module_for_arch(&module, GuardCarrierArch::AArch64)
        .expect("copy/select/branch transport lowers");
    let pick = lowered
        .iter()
        .find(|(function, _)| function.name == "pick")
        .map(|(function, _)| function)
        .expect("the transport body is lowered");
    assert_eq!(
        pick.blocks.len(),
        2,
        "the branch edge into a handle-typed block parameter survives"
    );
}

/// The one pointer-word carrier, and the fact that it is only that in a VALUE
/// slot. An interior occurrence is refused by the type funnel itself.
#[test]
fn a_handle_is_a_pointer_word_in_a_value_slot_and_nothing_in_an_interior_one() {
    assert_eq!(
        translate_type(&nat()).expect("a handle in a value slot is one pointer word"),
        trust_cg_lower::types::Type::I64
    );
    for interior in [
        Ty::Tuple(vec![Ty::I64, nat()]),
        Ty::Ref(Box::new(nat())),
        Ty::PtrMut(Box::new(nat())),
        Ty::Vector(Box::new(nat()), 2),
    ] {
        let error = translate_type_with_tables(&interior, &[], &[])
            .expect_err("an interior handle has no representation");
        assert!(
            matches!(
                error,
                AdapterError::OpaqueHandleNotAdmitted { ref name, ref runtime, .. }
                    if name == "Nat" && runtime == "trust_bignum::Nat"
            ),
            "{interior:?} must be refused by identity, got {error}"
        );
    }
}

// ---------------------------------------------------------------------------
// REFUSALS: one construct at a time
// ---------------------------------------------------------------------------

/// The pin is re-derived from `TRUSTED_HANDLE_RUNTIMES`, never taken from the
/// module: an unpinned runtime has no trusted producer for its words.
#[test]
fn an_unpinned_runtime_identity_is_refused() {
    let mut module = pinned_runtime_module();
    module.types.push(Ty::handle("Nat", "attacker::Nat"));
    let error = refuse_everywhere(&module);
    assert!(
        matches!(
            error,
            AdapterError::UntrustedOpaqueHandleRuntime { ref name, ref runtime, .. }
                if name == "Nat" && runtime == "attacker::Nat"
        ),
        "got {error}"
    );
}

/// A lexically malformed pair is refused before anything else looks at it; the
/// wire accepts only valid pairs, so this can only arrive from an in-process
/// producer.
#[test]
fn a_malformed_handle_identity_is_refused() {
    let mut module = pinned_runtime_module();
    module.types.push(Ty::handle("Nat", "trust_bignum::"));
    let error = refuse_everywhere(&module);
    assert!(
        matches!(
            error,
            AdapterError::UntrustedOpaqueHandleRuntime { ref runtime, .. }
                if runtime == "trust_bignum::"
        ),
        "got {error}"
    );
}

/// A struct field has an OFFSET: the word becomes addressable, so it can be
/// stored and re-read as an ordinary pointer. This is the refusal that keeps
/// `translate_type`'s one-word carrier from becoming a layout.
#[test]
fn a_handle_in_an_aggregate_field_is_refused() {
    let mut module = pinned_runtime_module();
    module.structs.push(StructDef {
        origin: None,
        id: StructId::new(0),
        name: "Boxed".to_string(),
        fields: vec![FieldDef {
            name: "inner".to_string(),
            ty: nat(),
            offset: Some(0),
        }],
        size: Some(8),
        align: Some(8),
        repr: Default::default(),
    });
    let error = refuse_everywhere(&module);
    assert!(
        matches!(
            error,
            AdapterError::OpaqueHandleNotAdmitted { ref name, ref location, .. }
                if name == "Nat" && location.contains("struct `Boxed`")
        ),
        "got {error}"
    );
}

#[test]
fn a_recursive_named_handle_is_refused_without_losing_its_identity() {
    let control = pinned_runtime_module();
    accept_everywhere(&control);
    let mut module = control.clone();
    module.structs.push(StructDef {
        origin: None,
        id: StructId::new(0),
        name: "Recursive".to_string(),
        fields: vec![
            // Visit the recursive edge before the direct handle: constructing
            // this refusal's identity used to expand the same struct forever.
            FieldDef {
                name: "next".to_string(),
                ty: Ty::PtrConst(Box::new(Ty::Struct(StructId::new(0)))),
                offset: Some(0),
            },
            FieldDef {
                name: "value".to_string(),
                ty: nat(),
                offset: Some(8),
            },
        ],
        size: Some(16),
        align: Some(8),
        repr: Default::default(),
    });
    let error = refuse_everywhere(&module);
    assert!(
        matches!(
            error,
            AdapterError::OpaqueHandleNotAdmitted {
                ref name, ref runtime, ref location, ..
            } if name == "Nat" && runtime == "trust_bignum::Nat"
                && location == "field `next` of struct `Recursive`"
        ),
        "got {error}"
    );
    accept_everywhere(&control);
}

/// Static storage with a link-time address is the same hazard as a field.
#[test]
fn a_handle_typed_global_is_refused() {
    let mut module = pinned_runtime_module();
    module.globals.push(Global {
        name: "CACHED".to_string(),
        ty: nat(),
        mutable: true,
        initializer: None,
        linkage: Linkage::Internal,
        tls: None,
        align: None,
        section: None,
        visibility: Visibility::Default,
        retained: false,
    });
    let error = refuse_everywhere(&module);
    assert!(
        matches!(
            error,
            AdapterError::OpaqueHandleNotAdmitted { ref location, .. }
                if location.contains("global `CACHED`")
        ),
        "got {error}"
    );
}

/// A pointee is an address a handle can be loaded from and stored to.
#[test]
fn a_pointer_to_a_handle_in_a_signature_is_refused() {
    let mut module = pinned_runtime_module();
    module
        .add_func_type(FuncTy {
            params: vec![Ty::PtrConst(Box::new(nat()))],
            returns: vec![Ty::Unit],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let error = refuse_everywhere(&module);
    assert!(
        matches!(
            error,
            AdapterError::OpaqueHandleNotAdmitted { ref location, .. }
                if location.contains("signature functy.")
        ),
        "got {error}"
    );
}

/// Memory. A `Load` at a handle type reconstitutes the word from bytes — the
/// origin guarantee is exactly what that erases.
#[test]
fn loading_a_handle_from_memory_is_refused() {
    let mut module = pinned_runtime_module();
    let body = module.functions[2].blocks[0].body.len() - 1;
    module.functions[2].blocks[0].body.insert(
        body,
        InstrNode::new(Inst::Load {
            ty: nat(),
            ptr: ValueId::new(0),
            volatile: false,
            align: None,
        })
        .with_result(ValueId::new(5)),
    );
    let error = refuse_everywhere(&module);
    assert!(
        matches!(
            error,
            AdapterError::OpaqueHandleNotAdmitted { ref detail, .. }
                if detail.contains("`Load` is not exact-typed transport")
        ),
        "got {error}"
    );
}

/// A cast. Both a handle and a `Ptr` are one pointer word, so a width-equal
/// `Bitcast` is exactly the forgery the type exists to exclude.
#[test]
fn bitcasting_a_pointer_to_a_handle_is_refused() {
    let mut module = pinned_runtime_module();
    let body = module.functions[2].blocks[0].body.len() - 1;
    module.functions[2].blocks[0].body.insert(
        body,
        InstrNode::new(Inst::Cast {
            op: trust_ir::CastOp::Bitcast,
            src_ty: Ty::Ptr,
            dst_ty: nat(),
            operand: ValueId::new(0),
        })
        .with_result(ValueId::new(5)),
    );
    let error = refuse_everywhere(&module);
    assert!(
        matches!(
            error,
            AdapterError::OpaqueHandleNotAdmitted { ref detail, .. }
                if detail.contains("`Cast` is not exact-typed transport")
        ),
        "got {error}"
    );
}

/// A structural comparison of two handles claims their representation is
/// meaningful. Nothing in the format says two distinct words denote distinct
/// values, or that equal words denote the same one.
#[test]
fn comparing_two_handles_structurally_is_refused() {
    let mut module = pinned_runtime_module();
    let body = module.functions[2].blocks[0].body.len() - 1;
    module.functions[2].blocks[0].body.insert(
        body,
        InstrNode::new(Inst::ICmp {
            op: trust_ir::ICmpOp::Eq,
            ty: nat(),
            lhs: ValueId::new(2),
            rhs: ValueId::new(3),
        })
        .with_result(ValueId::new(5)),
    );
    let error = refuse_everywhere(&module);
    assert!(
        matches!(
            error,
            AdapterError::OpaqueHandleNotAdmitted { ref detail, .. }
                if detail.contains("`ICmp` is not exact-typed transport")
        ),
        "got {error}"
    );
}

/// Forgery from nothing: a constant of handle type. No constant spelling
/// inhabits a handle type, so TrustIR's typed admission refuses it on every
/// codegen entry before the adapter's handle transport check is reached. The
/// shared v41 floor runs no typed admission, and there the transport check
/// refuses the `Const` by name.
#[test]
fn constructing_a_handle_from_a_constant_is_refused() {
    let mut module = pinned_runtime_module();
    let body = module.functions[2].blocks[0].body.len() - 1;
    module.functions[2].blocks[0].body.insert(
        body,
        InstrNode::new(Inst::Const {
            ty: nat(),
            value: Constant::Int(0x1000),
        })
        .with_result(ValueId::new(5)),
    );
    let error = refuse_everywhere(&module);
    assert_typed_const_refusal(&error, "function 'sum' bb0", &nat().to_string(), "int");
    assert_eq!(
        reject_unconsumed_v41_target_neutral_surface(&module)
            .expect_err("the shared floor refuses the forged handle")
            .to_string(),
        "opaque runtime handle `handle<Nat, trust_bignum::Nat>` (trust-ir v43) is not admitted \
         at function `sum` bb0#3: `Const` is not exact-typed transport: a handle may only be \
         copied, selected, passed to or returned from a call whose callee is pinned or \
         module-local, or carried across a branch edge (type Handle(HandleTy { name: \"Nat\", \
         runtime: \"trust_bignum::Nat\" }) reaches handle<\"Nat\", \"trust_bignum::Nat\">)"
    );
}

/// An indirect callee is resolved at run time, so this backend cannot
/// establish that the handle's origin is pinned. trust-ir admits an
/// exact-signature indirect call; this backend is deliberately narrower.
#[test]
fn an_indirect_call_over_a_handle_is_refused() {
    let mut module = pinned_runtime_module();
    let sig = module.func_types.len() as u32 - 2; // the `add` signature
    let body = module.functions[2].blocks[0].body.len() - 1;
    module.functions[2].blocks[0].body.insert(
        body,
        InstrNode::new(Inst::CallIndirect {
            callee: ValueId::new(0),
            sig: trust_ir::FuncTyId::new(sig),
            args: vec![ValueId::new(2), ValueId::new(3)],
            calling_conv: CallingConv::C,
        })
        .with_result(ValueId::new(5)),
    );
    let error = refuse_everywhere(&module);
    assert!(
        matches!(
            error,
            AdapterError::OpaqueHandleNotAdmitted { ref detail, .. }
                if detail.contains("resolved at run time")
                    || detail.contains("not exact-typed transport")
        ),
        "got {error}"
    );
}

/// Declarations are the ONLY handle origins, so an unpinned one is an
/// untrusted origin — even with a perfectly well-typed signature.
#[test]
fn an_unpinned_foreign_declaration_over_a_handle_is_refused() {
    let mut module = pinned_runtime_module();
    let ty = module.functions[1].ty;
    module
        .functions
        .push(declaration(3, "attacker_forge_nat", ty));
    let error = refuse_everywhere(&module);
    assert!(
        matches!(
            error,
            AdapterError::OpaqueHandleNotAdmitted { ref location, .. }
                if location.contains("declaration `attacker_forge_nat`")
        ),
        "got {error}"
    );
}

/// The `trust_bignum_nat_add(Ptr, Ptr) -> Ptr` forgery: a module that links the
/// REAL runtime under the pinned symbol while spelling ordinary pointers, so
/// nothing in it is ever type-checked as a handle. Refused on a module with no
/// handle in sight — which is why the symbol clause runs unconditionally.
#[test]
fn a_pinned_symbol_declared_with_pointer_types_is_refused_with_no_handle_present() {
    let mut module = Module::new("v43_symbol_impostor");
    let ty = module
        .add_func_type(FuncTy {
            params: vec![Ty::Ptr, Ty::Ptr],
            returns: vec![Ty::Ptr],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    module.functions.push(declaration(0, ADD, ty));
    assert!(
        !trust_cg_lower::module_spells_a_handle(&module),
        "the impostor spells no handle at all — that is the point"
    );
    let error = reject_unconsumed_v41_target_neutral_surface(&module)
        .expect_err("the shared floor must refuse the impostor");
    assert!(
        matches!(
            error,
            AdapterError::OpaqueHandleNotAdmitted { ref name, ref detail, .. }
                if name == "Nat" && detail.contains("not its pinned contract")
        ),
        "got {error}"
    );
}

/// A local DEFINITION of a pinned entry point would let the module forge every
/// word the symbol produces. trust-ir-build refuses it
/// (`HandleEntryPointDefinedLocally`) and so does this backend, independently.
#[test]
fn locally_defining_a_pinned_entry_point_is_refused() {
    let mut module = pinned_runtime_module();
    let mut block = Block::new(BlockId::new(0));
    block.params.push((ValueId::new(0), Ty::U64));
    block.body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(0)],
    }));
    module.functions[0].blocks.push(block);
    let error = refuse_everywhere(&module);
    assert!(
        matches!(
            error,
            AdapterError::OpaqueHandleNotAdmitted { ref detail, .. }
                if detail.contains("the runtime's own C symbol")
                    || detail.contains("not its pinned contract")
        ),
        "got {error}"
    );
}

/// A global may not wear a pinned entry-point symbol: it would shadow the
/// declaration every origin has to go through.
#[test]
fn a_global_shadowing_a_pinned_entry_point_is_refused() {
    let mut module = pinned_runtime_module();
    module.globals.push(Global {
        name: ADD.to_string(),
        ty: Ty::I64,
        mutable: false,
        initializer: Some(Constant::Int(0)),
        linkage: Linkage::Internal,
        tls: None,
        align: None,
        section: None,
        visibility: Visibility::Default,
        retained: false,
    });
    let error = refuse_everywhere(&module);
    assert!(
        matches!(
            error,
            AdapterError::OpaqueHandleNotAdmitted { ref location, .. }
                if location.contains("global `trust_bignum_nat_add`")
        ),
        "got {error}"
    );
}

/// The wasm lane refuses what the native lane admits: it has no channel to a
/// pinned native C runtime, so an imported symbol under that name is whatever
/// the embedder supplies.
#[test]
fn the_wasm_lane_refuses_the_transport_the_native_lane_admits() {
    let module = pinned_runtime_module();
    accept_everywhere(&module);
    let error =
        refuse_handle_surface(&module, "wasm").expect_err("the wasm lane admits no handle at all");
    assert!(
        matches!(
            error,
            AdapterError::OpaqueHandleNotAdmitted { ref name, ref location, .. }
                if name == "Nat" && location.contains("wasm")
        ),
        "got {error}"
    );
    // A handle-free module is untouched by that lane clause.
    refuse_handle_surface(&Module::new("empty"), "wasm").expect("no handle, no refusal");
}

/// The clause the inline-type walk structurally CANNOT cover, and therefore
/// the proof that deferring to trust-ir-build's own rule last is load-bearing:
/// a `Store` that DECLARES `Ptr` while storing a handle-typed value. Every
/// inline type in that instruction is handle-free; only the complete SSA
/// value-type map shows the lie.
#[test]
fn a_store_that_lies_about_its_type_is_caught_by_the_producer_side_rule() {
    let mut module = pinned_runtime_module();
    let body = module.functions[2].blocks[0].body.len() - 1;
    module.functions[2].blocks[0].body.insert(
        body,
        InstrNode::new(Inst::Store {
            ty: Ty::Ptr,
            ptr: ValueId::new(0),
            value: ValueId::new(2),
            volatile: false,
            align: None,
        }),
    );
    let error = reject_unconsumed_v41_target_neutral_surface(&module)
        .expect_err("the shared floor must refuse the mistyped store");
    assert!(
        matches!(
            error,
            AdapterError::OpaqueHandleModuleInvalid { ref detail, .. }
                if detail.contains("Store")
        ),
        "got {error}"
    );
    refuse_everywhere(&module);
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes because it was silently refused.
fn permit_unlicensed() -> trust_cg_lower::CodegenLicensePolicy {
    trust_cg_lower::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit)
}

/// `translate_module` under [`permit_unlicensed`].
fn permit_translate_module(
    module: &trust_ir::Module,
) -> Result<
    Vec<(trust_cg_lower::Function, trust_cg_lower::ProofContext)>,
    trust_cg_lower::AdapterError,
> {
    trust_cg_lower::translate_module_for_arch_with_tls_with_license(
        module,
        trust_cg_lower::GuardCarrierArch::default(),
        trust_cg_lower::TlsDialect::default(),
        &permit_unlicensed(),
    )
}

/// `translate_module_for_arch` under [`permit_unlicensed`].
fn permit_translate_module_for_arch(
    module: &trust_ir::Module,
    arch: trust_cg_lower::GuardCarrierArch,
) -> Result<
    Vec<(trust_cg_lower::Function, trust_cg_lower::ProofContext)>,
    trust_cg_lower::AdapterError,
> {
    trust_cg_lower::translate_module_for_arch_with_tls_with_license(
        module,
        arch,
        trust_cg_lower::TlsDialect::default(),
        &permit_unlicensed(),
    )
}
