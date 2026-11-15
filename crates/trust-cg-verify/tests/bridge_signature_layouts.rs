// Copyright 2026 Andrew Yates | Apache-2.0

#[path = "../../rustc-codegen-trust-cg/src/canonicalize_copies.rs"]
mod canonicalize_copies;
#[allow(dead_code)]
#[path = "../../rustc-codegen-trust-cg/src/pointer_casts.rs"]
mod pointer_casts;
#[path = "../../rustc-codegen-trust-cg/src/signature_layouts.rs"]
mod signature_layouts;

use signature_layouts::{PointeeLayout, install};

/// The session pointer width `pointer_casts` reads from its crate root
/// (the bridge's `session_pointer_bits`); every module here is 64-bit.
fn session_pointer_bits() -> u32 {
    64
}

/// `canonicalize_reinterpret_copies` over `function`, minting each new value id
/// past every id the function defines (`Function::fresh_value_ids`).
fn canonicalize(function: &mut Function) {
    let mut fresh = function.fresh_value_ids();
    canonicalize_copies::canonicalize_reinterpret_copies(function, None, || {
        fresh.take().expect("value id space exhausted")
    });
}
use trust_ir::{
    Block, BlockId, CastOp, FuncId, FuncTy, Function, Inst, InstrNode, Module, Ty, ValueId,
};

fn target() -> trust_ir::TargetInfo {
    trust_ir::TargetInfo {
        triple: "aarch64-unknown-linux-gnu".into(),
        pointer_size: 8,
        endianness: trust_ir::Endianness::Little,
        abi: None,
        struct_passing: trust_ir::StructPassingPolicy::Unclassified,
    }
}

fn module(pointees: &[Ty]) -> Module {
    let mut module = Module::new("declared_signature_layout");
    module.target_info = Some(target());
    let params: Vec<_> = pointees
        .iter()
        .map(|ty| Ty::RefMut(Box::new(ty.clone())))
        .collect();
    let sig = module
        .add_func_type(FuncTy {
            params: params.clone(),
            returns: vec![],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut function = Function::new(FuncId::new(0), "layout", sig, BlockId::new(0));
    let mut entry = Block::new(BlockId::new(0));
    for (i, ty) in params.into_iter().enumerate() {
        let id = ValueId::new(i as u32);
        entry.params.push((id, ty.clone()));
        entry.body.push(
            InstrNode::new(Inst::Cast {
                op: CastOp::PtrToPtr,
                src_ty: ty,
                dst_ty: Ty::Ptr,
                operand: id,
            })
            .with_result(ValueId::new((i + pointees.len()) as u32)),
        );
    }
    entry
        .body
        .push(InstrNode::new(Inst::Return { values: vec![] }));
    function.blocks.push(entry);
    module
        .try_add_function(function)
        .expect("Module::try_add_function: test fixture");
    module
}

fn reordered() -> PointeeLayout {
    PointeeLayout {
        ty: Ty::Tuple(vec![Ty::U8, Ty::U64]),
        size: 16,
        align: 8,
        offsets: vec![8, 0],
    }
}

#[test]
fn real_writer_keeps_instructions_and_proof_claims_with_explicit_pointee_layout() {
    for text in [
        include_str!("fixtures/output_memory_writer-O0.trust-ir.json"),
        include_str!("fixtures/output_memory_writer-O1.trust-ir.json"),
    ] {
        let mut m: Module = serde_json::from_str(text).unwrap();
        canonicalize(&mut m.functions[0]);
        m.target_info = Some(target());
        let original = m.clone();
        let layout = PointeeLayout {
            ty: Ty::Tuple(vec![Ty::U64; 5]),
            size: 40,
            align: 8,
            offsets: vec![0, 8, 16, 24, 32],
        };
        assert!(install(&mut m, std::slice::from_ref(&layout)));
        assert_eq!(m.functions, original.functions);
        assert_eq!(m.proof_obligations, original.proof_obligations);
        assert_eq!(m.proof_certificates, original.proof_certificates);
        let actual_lir = trust_cg_lower::translate_function_with_license(
            &m.functions[0],
            &m,
            &permit_unlicensed(),
        )
        .unwrap();
        let original_lir = trust_cg_lower::translate_function_with_license(
            &original.functions[0],
            &original,
            &permit_unlicensed(),
        )
        .unwrap();
        assert_eq!(
            serde_json::to_value(&actual_lir.0).unwrap(),
            serde_json::to_value(&original_lir.0).unwrap()
        );
        assert_eq!(
            m.tuple_layout_descriptor(&layout.ty).unwrap().unwrap().size,
            40
        );
        let errors = trust_ir_build::validate_module(&m);
        assert_eq!(errors, trust_ir_build::validate_module(&original));
        assert_eq!(
            errors.len(),
            if m.proof_obligations.is_empty() {
                0
            } else {
                15
            }
        );
    }
}

#[test]
fn retains_reordered_offsets_and_deduplicates_identical_declarations() {
    let layout = reordered();
    let mut m = module(&[layout.ty.clone(), layout.ty.clone()]);
    assert!(install(&mut m, &[layout.clone(), layout.clone()]));
    assert_eq!(m.types, vec![layout.ty.clone()]);
    assert_eq!(m.tuple_layouts.len(), 1);
    assert_eq!(m.tuple_layouts[0].field_offsets, vec![8, 0]);
    assert_eq!(m.tuple_layouts[0].tuple_type.index(), 0);
    assert!(trust_ir_build::validate_module(&m).is_empty());
}

#[test]
fn refuses_conflicts_invalid_offsets_and_missing_origins_without_partial_metadata() {
    let layout = reordered();
    let mut wrongs = vec![vec![]];
    for offsets in [vec![0, 8], vec![0, 0], vec![8, 1], vec![16, 0], vec![8]] {
        let mut changed = layout.clone();
        changed.offsets = offsets;
        wrongs.push(vec![layout.clone(), changed]);
    }
    let mut invalid = layout.clone();
    invalid.align = 3;
    wrongs.push(vec![invalid]);
    let mut invalid = layout.clone();
    invalid.size = 8;
    wrongs.push(vec![invalid]);
    let mut invalid = layout.clone();
    invalid.offsets = vec![0, 0];
    wrongs.push(vec![invalid]);
    for layouts in wrongs {
        let mut m = module(std::slice::from_ref(&layout.ty));
        let before = m.clone();
        assert!(!install(&mut m, &layouts), "{layouts:?}");
        assert_eq!(m, before);
    }
}

#[test]
fn refuses_untracked_tuple_uses_and_keeps_caller_metadata() {
    let layout = reordered();
    let source = module(std::slice::from_ref(&layout.ty));
    let mut variants = Vec::new();
    let mut m = source.clone();
    m.functions[0].blocks[0].body.insert(
        0,
        InstrNode::new(Inst::Alloca {
            ty: layout.ty.clone(),
            count: None,
            align: None,
        })
        .with_result(ValueId::new(50)),
    );
    variants.push(m);
    let mut m = source.clone();
    if let Inst::Cast { operand, .. } = &mut m.functions[0].blocks[0].body[0].inst {
        *operand = ValueId::new(50);
    }
    variants.push(m);
    let mut m = source.clone();
    m.types.push(layout.ty.clone());
    variants.push(m);
    let mut m = source.clone();
    m.target_info = None;
    variants.push(m);
    let mut m = source.clone();
    m.functions[0].calling_conv = trust_ir::CallingConv::Rust;
    variants.push(m);
    let mut m = source.clone();
    m.functions[0].blocks[0].params[0].1 = Ty::Ptr;
    variants.push(m);
    let mut m = source.clone();
    m.func_types[0].returns = vec![layout.ty.clone()];
    variants.push(m);
    for mut m in variants {
        let before = m.clone();
        assert!(!install(&mut m, std::slice::from_ref(&layout)));
        assert_eq!(m, before);
    }
}

#[test]
fn adapter_retains_pointer_descriptors_and_refuses_layout_sensitive_uses() {
    use trust_cg_lower::adapter::{AdapterError, reject_unconsumed_v41_target_neutral_surface};
    let layout = reordered();
    let mut m = module(std::slice::from_ref(&layout.ty));
    assert!(install(&mut m, std::slice::from_ref(&layout)));
    let original = m.clone();
    permit_translate_module(&m).unwrap();
    let report = trust_ir_build::validate_module_report(&m);
    trust_cg_lower::translate_validated_module_strict_for_arch_with_tls_and_validation_with_license(
        &report,
        trust_cg_lower::GuardCarrierArch::AArch64,
        trust_cg_lower::TlsDialect::default(),
    &permit_unlicensed(),)
    .unwrap();
    assert_eq!(m, original);
    let tuple_id = m.tuple_layouts[0].tuple_type;
    for ty in [
        layout.ty.clone(),
        Ty::Array(tuple_id, 2),
        Ty::Vector(Box::new(layout.ty.clone()), 2),
    ] {
        let mut bad = m.clone();
        bad.functions[0].blocks[0].body.insert(
            0,
            InstrNode::new(Inst::Alloca {
                ty,
                count: None,
                align: None,
            })
            .with_result(ValueId::new(50)),
        );
        // A by-value use leaves the pointer-transport profile; the reordered
        // row then disagrees with the declaration-order layout (WS7.7).
        assert!(matches!(
            reject_unconsumed_v41_target_neutral_surface(&bad),
            Err(AdapterError::DeclaredTupleLayoutDisagrees { .. })
        ));
    }
    for offsets in [vec![0, 0], vec![16, 0], vec![0, 1]] {
        let mut bad = m.clone();
        bad.tuple_layouts[0].field_offsets = offsets;
        assert!(matches!(
            reject_unconsumed_v41_target_neutral_surface(&bad),
            Err(AdapterError::DeclaredTupleLayoutMalformed { .. })
        ));
    }
}

#[cfg(feature = "core-byte-replay")]
#[test]
fn canonical_reflection_preserves_the_complete_writer_and_its_actual_layout() {
    use trust_ir_build::core_reflection::reflect_core_module_v1;
    let mut m: Module = serde_json::from_str(include_str!(
        "fixtures/output_memory_writer-O1.trust-ir.json"
    ))
    .unwrap();
    canonicalize(&mut m.functions[0]);
    m.target_info = Some(target());
    let layout = PointeeLayout {
        ty: Ty::Tuple(vec![Ty::U64; 5]),
        size: 40,
        align: 8,
        offsets: vec![0, 8, 16, 24, 32],
    };
    assert!(install(&mut m, std::slice::from_ref(&layout)));
    let reflected = reflect_core_module_v1(&m, &[(FuncId::new(0), 4096)]).unwrap();
    assert!(std::ptr::eq(reflected.module(), &m));
    assert!(std::ptr::eq(
        reflected.function(FuncId::new(0)).unwrap(),
        &m.functions[0]
    ));
    for (pc, node) in m.functions[0].blocks[0].body.iter().enumerate() {
        assert!(std::ptr::eq(
            reflected.node(FuncId::new(0), BlockId::new(0), pc).unwrap(),
            node
        ));
    }
    // A different coherent physical layout changes the reflected context.
    let mut changed = m.clone();
    changed.tuple_layouts[0].field_offsets.swap(0, 1);
    let other = reflect_core_module_v1(&changed, &[(FuncId::new(0), 4096)]).unwrap();
    assert_ne!(reflected.context_term(), other.context_term());
    for mutation in 0..3 {
        let mut bad = m.clone();
        match mutation {
            0 => bad.target_info = None,
            1 => bad.tuple_layouts.clear(),
            _ => bad.tuple_layouts[0].field_offsets[1] = 0,
        }
        assert!(reflect_core_module_v1(&bad, &[(FuncId::new(0), 4096)]).is_err());
    }
    // Discharged labels with no transported certificate stay outside Core.
    let mut o0: Module = serde_json::from_str(include_str!(
        "fixtures/output_memory_writer-O0.trust-ir.json"
    ))
    .unwrap();
    canonicalize(&mut o0.functions[0]);
    o0.target_info = Some(target());
    assert!(install(&mut o0, &[layout]));
    assert!(reflect_core_module_v1(&o0, &[(FuncId::new(0), 4096)]).is_err());
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
