// Copyright 2026 Andrew Yates | Apache-2.0
//! Refinement erasure must preserve ABI decisions and required refusals.

use std::collections::HashMap;
use trust_cg_lower::{
    GuardCarrierArch, TlsDialect, adapter::AdapterError, prepare_module_for_lir,
    translate_module_for_arch_with_tls_and_stats_and_validation_with_license,
    translate_module_for_arch_with_tls_and_stats_with_license,
    translate_module_for_arch_with_tls_and_validation_with_license,
    translate_module_strict_for_arch_with_tls_and_validation_with_license,
    translate_validated_module_strict_for_arch_with_tls_and_validation_with_license,
};
use trust_ir::{
    Block, BlockId, CallingConv, FuncId, FuncTy, Function, Inst, InstrNode, Module, ParamAttrs,
    Pred, PredId, Ty, TyId, ValueId,
};

fn target(dialect: TlsDialect) -> trust_ir::TargetInfo {
    trust_ir::TargetInfo {
        triple: if dialect == TlsDialect::MachOTlv {
            "aarch64-apple-darwin"
        } else {
            "aarch64-unknown-linux-gnu"
        }
        .into(),
        pointer_size: 8,
        endianness: trust_ir::Endianness::Little,
        abi: Some("aapcs64".into()),
        struct_passing: trust_ir::StructPassingPolicy::NativeC,
    }
}

fn caller(narrow: Ty, trailing_wide: usize, indirect: bool) -> Module {
    let mut module = Module::new("adapter_target_abi");
    module.target_info = Some(target(TlsDialect::ElfExecutable));
    let mut parameters = vec![Ty::I64, Ty::I128];
    parameters.extend(vec![Ty::I64; trailing_wide]);
    parameters.push(narrow);
    let callee_ty = module
        .add_func_type(FuncTy {
            params: parameters.clone(),
            returns: vec![],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut declaration = Function::new(FuncId::new(0), "observe", callee_ty, BlockId::new(0));
    declaration.blocks.clear();
    module
        .try_add_function(declaration)
        .expect("Module::try_add_function: test fixture");
    if indirect {
        parameters.insert(0, Ty::Func(callee_ty));
    }
    let caller_ty = module
        .add_func_type(FuncTy {
            params: parameters.clone(),
            returns: vec![],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut function = Function::new(FuncId::new(1), "caller", caller_ty, BlockId::new(0));
    let arguments = (usize::from(indirect)..parameters.len())
        .map(|index| ValueId::new(index as u32))
        .collect();
    let call = if indirect {
        Inst::CallIndirect {
            callee: ValueId::new(0),
            sig: callee_ty,
            args: arguments,
            calling_conv: CallingConv::C,
        }
    } else {
        Inst::Call {
            callee: FuncId::new(0),
            args: arguments,
        }
    };
    function.blocks = vec![Block {
        id: BlockId::new(0),
        params: parameters
            .into_iter()
            .enumerate()
            .map(|(index, ty)| (ValueId::new(index as u32), ty))
            .collect(),
        body: vec![
            InstrNode::new(call),
            InstrNode::new(Inst::Return { values: vec![] }),
        ],
    }];
    module
        .try_add_function(function)
        .expect("Module::try_add_function: test fixture");
    module
}

fn refined() -> Ty {
    Ty::Refine(TyId::new(0), PredId::new(0))
}

fn install_refinement(module: &mut Module, base: Ty) {
    assert_eq!(
        module
            .add_type(base)
            .expect("Module::add_type: test fixture"),
        TyId::new(0)
    );
    assert_eq!(
        module
            .intern_pred(Pred::Top)
            .expect("Module::intern_pred: test fixture"),
        Some(PredId::new(0))
    );
}

fn body_module(ty: Ty, returns: Vec<Ty>, body: Vec<InstrNode>) -> Module {
    let mut module = Module::new("refine_erasure_hazards");
    module.target_info = Some(target(TlsDialect::ElfExecutable));
    let signature = module
        .add_func_type(FuncTy {
            params: vec![Ty::Ptr, ty.clone()],
            returns,
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut function = Function::new(FuncId::new(0), "entry", signature, BlockId::new(0));
    function.blocks = vec![Block {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), Ty::Ptr), (ValueId::new(1), ty)],
        body,
    }];
    module
        .try_add_function(function)
        .expect("Module::try_add_function: test fixture");
    module
}

fn verdicts(module: &Module) -> Vec<(&'static str, Option<AdapterError>)> {
    let arch = GuardCarrierArch::AArch64;
    let tls = TlsDialect::ElfExecutable;
    // One policy for every route. These fixtures are synthetic, claim-less
    // bodies (`body_gate: None`), which the DEFAULT policy refuses by design
    // (DG-73, `UnlicensedBodyPolicy::Refuse`). Five of the routes below used
    // the default while the rest used `permit_unlicensed()`, so a fixture the
    // row expects every route to ADMIT was refused `UnlicensedBody` on those
    // five — a license verdict standing in for the refinement verdict this
    // file measures. The license rule is not weakened here; it has its own
    // tests (`codegen_license_flags`, `codegen_license_evidence`), and this
    // helper's job is route agreement on a refinement hazard.
    let policy = permit_unlicensed();
    let report = trust_ir_build::validate_module_report(module);
    let function = module
        .functions
        .iter()
        .find(|f| !f.is_declaration())
        .unwrap();
    let mut entries = vec![
        (
            "module",
            trust_cg_lower::translate_module_for_arch_with_tls_with_license(
                module,
                trust_cg_lower::GuardCarrierArch::default(),
                trust_cg_lower::TlsDialect::default(),
                &permit_unlicensed(),
            )
            .err(),
        ),
        (
            "target",
            trust_cg_lower::translate_module_for_arch_with_tls_with_license(
                module,
                arch,
                tls,
                &permit_unlicensed(),
            )
            .err(),
        ),
        (
            "validation",
            translate_module_for_arch_with_tls_and_validation_with_license(
                module, arch, tls, &policy,
            )
            .err(),
        ),
        (
            "stats",
            translate_module_for_arch_with_tls_and_stats_with_license(module, arch, tls, &policy)
                .err(),
        ),
        (
            "stats_validation",
            translate_module_for_arch_with_tls_and_stats_and_validation_with_license(
                module, arch, tls, &policy,
            )
            .err(),
        ),
        (
            "strict",
            translate_module_strict_for_arch_with_tls_and_validation_with_license(
                module, arch, tls, &policy,
            )
            .err(),
        ),
        // Always exercise this route, including a refused report.
        (
            "validated_strict",
            translate_validated_module_strict_for_arch_with_tls_and_validation_with_license(
                &report, arch, tls, &policy,
            )
            .err(),
        ),
        (
            "function",
            trust_cg_lower::translate_function_with_license(function, module, &permit_unlicensed())
                .err(),
        ),
        (
            "function_names",
            trust_cg_lower::translate_function_with_names_and_license(
                function,
                module,
                &HashMap::new(),
                &permit_unlicensed(),
            )
            .err(),
        ),
    ];
    entries.push((
        "prepared",
        match prepare_module_for_lir(module, arch) {
            Ok(prepared) => prepared
                .translate_with_tls_and_validation_with_license(tls, &policy)
                .err(),
            Err(error) => Some(error),
        },
    ));
    entries
}

fn assert_same_lir(bare: &Module, refined: &Module, dialect: TlsDialect) {
    for module in [bare, refined] {
        let errors = trust_ir_build::validate_module(module);
        assert!(
            errors.is_empty(),
            "fixture must be valid TrustIR: {errors:?}"
        );
    }
    let lower = |module| {
        trust_cg_lower::translate_module_for_arch_with_tls_with_license(
            module,
            GuardCarrierArch::AArch64,
            dialect,
            &permit_unlicensed(),
        )
        .unwrap()
    };
    let bare_lir = lower(bare);
    let refined_lir = lower(refined);
    assert_eq!(bare_lir.len(), refined_lir.len());
    for ((bare, _), (refined, _)) in bare_lir.iter().zip(&refined_lir) {
        assert_eq!(bare.signature.params, refined.signature.params);
        assert_eq!(bare.signature.returns, refined.signature.returns);
        assert_eq!(
            format!("{:?}", bare.blocks),
            format!("{:?}", refined.blocks),
            "representation erasure changed instructions for {}",
            bare.name
        );
        assert_eq!(bare.value_types, refined.value_types);
    }
}

fn caller_twins(indirect: bool) {
    for narrow in [Ty::I8, Ty::U8, Ty::I16, Ty::U16] {
        for trailing in [3, 4] {
            for dialect in [TlsDialect::MachOTlv, TlsDialect::ElfExecutable] {
                let mut bare = caller(narrow.clone(), trailing, indirect);
                let mut wrapped = caller(refined(), trailing, indirect);
                install_refinement(&mut wrapped, narrow.clone());
                bare.target_info = Some(target(dialect));
                wrapped.target_info = Some(target(dialect));
                assert_same_lir(&bare, &wrapped, dialect);
            }
        }
    }
}

#[test]
fn refined_direct_call_narrow_extensions_match_bare_at_register_exhaustion() {
    caller_twins(false);
}

#[test]
fn refined_indirect_call_narrow_extensions_match_bare_at_register_exhaustion() {
    caller_twins(true);
}

#[test]
fn refined_narrow_returns_match_bare_extension_instructions() {
    for narrow in [Ty::I8, Ty::U8, Ty::I16, Ty::U16] {
        for dialect in [TlsDialect::MachOTlv, TlsDialect::ElfExecutable] {
            let body = vec![InstrNode::new(Inst::Return {
                values: vec![ValueId::new(1)],
            })];
            let mut bare = body_module(narrow.clone(), vec![narrow.clone()], body.clone());
            let ty = refined();
            let mut wrapped = body_module(ty.clone(), vec![ty], body);
            install_refinement(&mut wrapped, narrow.clone());
            bare.target_info = Some(target(dialect));
            wrapped.target_info = Some(target(dialect));
            assert_same_lir(&bare, &wrapped, dialect);
        }
    }
}

#[test]
fn refined_gep_index_preserves_pinned_trust_ir_refusal_on_every_entry() {
    let body = vec![
        InstrNode::new(Inst::GEP {
            pointee_ty: Ty::I64,
            base: ValueId::new(0),
            indices: vec![ValueId::new(1)],
            inbounds: false,
        })
        .with_result(ValueId::new(2)),
        InstrNode::new(Inst::Return {
            values: vec![ValueId::new(2)],
        }),
    ];
    let bare = body_module(Ty::I32, vec![Ty::Ptr], body.clone());
    assert!(trust_ir_build::validate_module(&bare).is_empty());
    for (entry, verdict) in verdicts(&bare) {
        assert!(verdict.is_none(), "bare index {entry}: {verdict:?}");
    }
    let mut wrapped = body_module(refined(), vec![Ty::Ptr], body);
    install_refinement(&mut wrapped, Ty::I32);
    let errors = trust_ir_build::validate_module(&wrapped);
    let reason = errors
        .iter()
        .find(|e| {
            matches!(
                e,
                trust_ir_build::ValidationError::GepIndexNotInteger { .. }
            )
        })
        .expect("pin must refuse refined GEP index")
        .to_string();
    for (entry, verdict) in verdicts(&wrapped) {
        let error =
            verdict.unwrap_or_else(|| panic!("{entry} admitted a GEP index the pin refuses"));
        assert!(
            error.to_string().contains(&reason),
            "{entry} lost TrustIR class: {error}"
        );
    }
}

#[test]
fn refined_volatile_i128_load_store_preserve_bare_adapter_refusal() {
    for wide in [Ty::I128, Ty::U128] {
        for store in [false, true] {
            let build = |ty: Ty| {
                let instruction = if store {
                    InstrNode::new(Inst::Store {
                        ty: ty.clone(),
                        ptr: ValueId::new(0),
                        value: ValueId::new(1),
                        volatile: true,
                        align: None,
                    })
                } else {
                    InstrNode::new(Inst::Load {
                        ty: ty.clone(),
                        ptr: ValueId::new(0),
                        volatile: true,
                        align: None,
                    })
                    .with_result(ValueId::new(2))
                };
                body_module(
                    ty,
                    vec![],
                    vec![instruction, InstrNode::new(Inst::Return { values: vec![] })],
                )
            };
            let bare = build(wide.clone());
            let mut wrapped = build(refined());
            install_refinement(&mut wrapped, wide.clone());
            for module in [&bare, &wrapped] {
                assert!(trust_ir_build::validate_module(module).is_empty());
            }
            for ((entry, bare), (refined_entry, wrapped)) in
                verdicts(&bare).into_iter().zip(verdicts(&wrapped))
            {
                assert_eq!(entry, refined_entry);
                let bare = bare.expect("bare volatile i128 must refuse");
                let wrapped = wrapped.unwrap_or_else(|| {
                    panic!("{entry} admitted refined volatile {wide:?}, store={store}")
                });
                assert_eq!(bare.to_string(), wrapped.to_string(), "{entry}");
            }
        }
    }
}

#[test]
fn refined_narrow_darwin_import_cannot_bypass_recorded_none_extension() {
    for narrow in [Ty::I8, Ty::U8, Ty::I16, Ty::U16] {
        let mut bare = caller(narrow.clone(), 3, false);
        let mut wrapped = caller(refined(), 3, false);
        install_refinement(&mut wrapped, narrow);
        for module in [&mut bare, &mut wrapped] {
            module.target_info = Some(target(TlsDialect::MachOTlv));
            module.functions[0].attrs.params = vec![ParamAttrs::default(); 6];
        }
        let lower = |module| {
            trust_cg_lower::translate_module_for_arch_with_tls_with_license(
                module,
                GuardCarrierArch::AArch64,
                TlsDialect::MachOTlv,
                &permit_unlicensed(),
            )
        };
        let bare = lower(&bare).expect_err("bare import with recorded None must refuse");
        let wrapped = lower(&wrapped).expect_err("refined import with recorded None must refuse");
        assert_eq!(bare.to_string(), wrapped.to_string());
    }
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes (or is refused) because the license silently refused it.
fn permit_unlicensed() -> trust_cg_lower::CodegenLicensePolicy {
    trust_cg_lower::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit)
}
