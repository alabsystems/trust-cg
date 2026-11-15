// trust-ir v41 contract surface at the adapter boundary: every construct is
// either CONSUMED (accepted here, honored by the object emitters — pinned at
// the object level in trust-cg-codegen's `v41_abi_residue_objects.rs`) or
// REFUSED through the adapter's typed error channel, on every entry point
// (compatibility, validated, prepared, single-function, and the validated
// strict path Core admission uses). Nothing falls through a wildcard onto a
// pre-v41 meaning. Each test builds the module by hand so the verdict is
// exercised on exactly one construct at a time, with the accepted neighbour of
// that construct as the positive control.

use std::collections::HashMap;
use trust_cg_lower::adapter::AdapterError;
use trust_cg_lower::declared_tuple_layout::TupleLayoutComponent;
use trust_cg_lower::instructions::Opcode;

use trust_cg_lower::{
    FunctionSymbolFactPolicy, GuardCarrierArch, ObjectSymbolPolicy, TlsDialect,
    WeakUndefinedReferencePolicy, function_declaration_linkage_is_admitted, known_target_features,
    prepare_module_for_lir, reject_unconsumed_v41_surface,
    reject_unconsumed_v41_surface_with_weak_references,
    reject_unconsumed_v41_target_neutral_surface,
    translate_module_for_arch_with_tls_and_stats_with_license_and_weak_references,
};
use trust_ir::proof::{
    ObligationKind, ProofCertificate, ProofEvidence, ProofObligation, ProofStatus,
};
use trust_ir::value::GlobalId;
use trust_ir::{
    BinOp, Block, BlockId, Constant, ExternRef, FuncId, FuncTy, Function, Global, Inst, InstrNode,
    Linkage, Module, ModuleImport, ProofId, Ty, ValueId, Visibility,
};

/// One defined function `entry: () -> i64` returning the constant 7.
fn defined_module() -> Module {
    let mut module = Module::new("v41_contract_surface");
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

fn data_global(name: &str) -> Global {
    Global {
        name: name.to_string(),
        ty: Ty::I64,
        mutable: false,
        initializer: Some(Constant::Int(1)),
        linkage: Linkage::Internal,
        tls: None,
        align: None,
        section: None,
        visibility: Visibility::Default,
        retained: false,
    }
}

fn obligation(id: u32, kind: ObligationKind, status: ProofStatus) -> ProofObligation {
    ProofObligation {
        id: ProofId::new(id),
        kind,
        status,
        description: "hand-built".to_string(),
        formula: None,
        function: Some(FuncId::new(0)),
        source: None,
        site: None,
        spec: None,
    }
}

/// Every module entry point must agree; a refusal that only one of them
/// enforces is a bypass. Returns the error from the compatibility entry.
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
    if let Some(function) = module.functions.first() {
        trust_cg_lower::translate_function_with_license(function, module, &permit_unlicensed())
            .expect_err("translate_function must refuse");
    }
    // The strict, already-validated entry (Core admission) reuses the full
    // validation report and skips the compatibility prerequisites — it has
    // to run the v41 gate on its own. `validate_module` lets a module CARRY
    // these constructs, so the report succeeds and the refusal is ours.
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
    trust_cg_lower::translate_function_with_license(
        &module.functions[0],
        module,
        &permit_unlicensed(),
    )
    .expect("translate_function must accept the control");
}

#[test]
fn control_module_is_accepted() {
    accept_everywhere(&defined_module());
}

fn tuple_pointer_with_primitive_array() -> Module {
    let mut module = defined_module();
    module.target_info = Some(trust_ir::TargetInfo {
        triple: "aarch64-unknown-linux-gnu".into(),
        pointer_size: 8,
        endianness: trust_ir::Endianness::Little,
        abi: None,
        struct_passing: Default::default(),
    });
    let tuple = Ty::Tuple(vec![Ty::U8, Ty::U32]);
    let tuple_type = module
        .add_type(tuple.clone())
        .expect("Module::add_type: test fixture");
    module.tuple_layouts.push(trust_ir::TupleLayoutDescriptor {
        tuple_type,
        size: 8,
        align: 4,
        field_offsets: vec![4, 0],
    });
    let pointer = Ty::PtrConst(Box::new(tuple));
    module.func_types[0].params.push(pointer.clone());
    let byte = module
        .add_type(Ty::I8)
        .expect("Module::add_type: test fixture");
    let block = &mut module.functions[0].blocks[0];
    block.params.push((ValueId::new(1), pointer));
    block.body.pop();
    block.body.push(
        InstrNode::new(Inst::Alloca {
            ty: Ty::Array(byte, 8),
            count: None,
            align: Some(1),
        })
        .with_result(ValueId::new(2)),
    );
    block.body.push(InstrNode::new(Inst::Store {
        ty: Ty::I64,
        ptr: ValueId::new(2),
        value: ValueId::new(0),
        volatile: false,
        align: Some(1),
    }));
    block.body.push(
        InstrNode::new(Inst::Load {
            ty: Ty::I64,
            ptr: ValueId::new(2),
            volatile: false,
            align: Some(1),
        })
        .with_result(ValueId::new(3)),
    );
    block.body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(3)],
    }));
    module
}

#[test]
fn v42_tuple_pointer_transport_allows_independent_primitive_array_storage() {
    let module = tuple_pointer_with_primitive_array();
    let report = trust_ir_build::validate_module_report(&module);
    assert!(
        report.is_ok(),
        "valid tuple-pointer and primitive-array module"
    );
    accept_everywhere(&module);
    for arch in [
        GuardCarrierArch::AArch64,
        GuardCarrierArch::X86_64,
        GuardCarrierArch::Riscv64,
    ] {
        reject_unconsumed_v41_surface(&module, arch).unwrap();
    }
    let prepared = prepare_module_for_lir(&module, GuardCarrierArch::AArch64).unwrap();
    assert_eq!(prepared.module().tuple_layouts, module.tuple_layouts);
}

#[test]
fn v42_tuple_pointer_transport_cannot_hide_tuple_access_in_an_array() {
    for nested in [false, true] {
        let mut module = tuple_pointer_with_primitive_array();
        let tuple = module.tuple_layouts[0].tuple_type;
        let element = if nested {
            module
                .add_type(Ty::Array(tuple, 1))
                .expect("Module::add_type: test fixture")
        } else {
            tuple
        };
        // Remove unrelated stores so rejection cannot be a type/width mismatch.
        module.functions[0].blocks[0].body.truncate(1);
        module.functions[0].blocks[0].body.push(
            InstrNode::new(Inst::Alloca {
                ty: Ty::Array(element, 1),
                count: None,
                align: Some(4),
            })
            .with_result(ValueId::new(2)),
        );
        module.functions[0].blocks[0]
            .body
            .push(InstrNode::new(Inst::Return {
                values: vec![ValueId::new(0)],
            }));
        assert!(trust_ir_build::validate_module_report(&module).is_ok());
        // The row is reordered (`u32@0 u8@4`), so it disagrees with the
        // declaration-order layout the by-value array element is laid out at.
        assert!(matches!(
            refuse_everywhere(&module),
            AdapterError::DeclaredTupleLayoutDisagrees {
                field: TupleLayoutComponent::FieldOffset(0),
                declared: 4,
                emitted: 0,
                ..
            }
        ));
        // WS7.7 twin: the same by-value use under a row that EQUALS the
        // declaration-order layout is admitted — it is honoured by
        // construction.
        module.tuple_layouts[0].field_offsets = vec![0, 4];
        assert!(trust_ir_build::validate_module_report(&module).is_ok());
        accept_everywhere(&module);
    }
}

#[test]
fn v42_unused_disagreeing_declared_tuple_layout_is_refused_on_every_native_entry() {
    let mut module = defined_module();
    module.target_info = Some(trust_ir::TargetInfo {
        triple: "aarch64-apple-darwin".into(),
        pointer_size: 8,
        endianness: trust_ir::Endianness::Little,
        abi: None,
        struct_passing: Default::default(),
    });
    let tuple_type = module
        .add_type(Ty::Tuple(vec![Ty::U8, Ty::U8]))
        .expect("Module::add_type: test fixture");
    module.tuple_layouts.push(trust_ir::TupleLayoutDescriptor {
        tuple_type,
        size: 2,
        align: 1,
        field_offsets: vec![1, 0],
    });
    module
        .validate_tuple_layouts()
        .expect("valid reordered layout");
    let report = trust_ir_build::validate_module_report(&module);
    assert!(report.is_ok(), "refusal must not be generic IR invalidity");
    // WS7.7: an unused row is still a statement about the tuple's memory, and
    // a reordered one disagrees with the declaration-order layout.
    let disagrees = |error: &AdapterError| {
        matches!(
            error,
            AdapterError::DeclaredTupleLayoutDisagrees {
                tuple_type: 0,
                field: TupleLayoutComponent::FieldOffset(0),
                declared: 1,
                emitted: 0,
                ..
            }
        )
    };
    assert!(disagrees(&refuse_everywhere(&module)));
    for arch in [
        GuardCarrierArch::AArch64,
        GuardCarrierArch::X86_64,
        GuardCarrierArch::Riscv64,
    ] {
        assert!(disagrees(
            &reject_unconsumed_v41_surface(&module, arch).expect_err("refused")
        ));
    }
    assert!(disagrees(
        &trust_cg_lower::validate_codegen_metadata(&module).expect_err("refused")
    ));
    assert!(disagrees(
        &trust_cg_lower::translate_function_with_names_and_license(
            &module.functions[0],
            &module,
            &HashMap::new(),
            &permit_unlicensed()
        )
        .expect_err("refused")
    ));

    // The same row in declaration order is admitted on every native entry.
    module.tuple_layouts[0].field_offsets = vec![0, 1];
    accept_everywhere(&module);
    for arch in [
        GuardCarrierArch::AArch64,
        GuardCarrierArch::X86_64,
        GuardCarrierArch::Riscv64,
    ] {
        reject_unconsumed_v41_surface(&module, arch).expect("agreeing row");
    }

    // The identical ordinary body and unused type remain accepted when no
    // physical layout contract is declared. Do not change the legacy lane.
    module.tuple_layouts.clear();
    accept_everywhere(&module);
}

#[test]
fn v42_malformed_declared_tuple_layout_cannot_bypass_the_shared_floor() {
    let mut module = defined_module();
    module.tuple_layouts.push(trust_ir::TupleLayoutDescriptor {
        tuple_type: trust_ir::TyId::new(999),
        size: 0,
        align: 0,
        field_offsets: vec![],
    });
    assert!(module.validate_tuple_layouts().is_err());
    assert!(matches!(
        reject_unconsumed_v41_target_neutral_surface(&module),
        Err(AdapterError::DeclaredTupleLayoutMalformed { .. })
    ));
    refuse_everywhere(&module);
}

// ---------------------------------------------------------------------------
// Linkage
// ---------------------------------------------------------------------------

#[test]
fn external_weak_is_refused_on_functions_and_globals() {
    let mut module = defined_module();
    module.functions[0].linkage = Linkage::ExternalWeak;
    match refuse_everywhere(&module) {
        AdapterError::UnsupportedLinkage {
            symbol, linkage, ..
        } => {
            assert_eq!(symbol, "entry");
            assert_eq!(linkage, Linkage::ExternalWeak);
        }
        other => panic!("expected UnsupportedLinkage, got {other:?}"),
    }
    let mut module = defined_module();
    let mut global = data_global("TABLE");
    global.linkage = Linkage::ExternalWeak;
    global.initializer = None;
    module.globals.push(global);
    match refuse_everywhere(&module) {
        AdapterError::UnsupportedLinkage { symbol, .. } => assert_eq!(symbol, "TABLE"),
        other => panic!("expected UnsupportedLinkage, got {other:?}"),
    }
}

/// A body-less function whose linkage names a definition (`internal`,
/// `private`, `weak`, `linkonce` and their ODR forms) is refused by name on
/// every entry, where trust-ir's validator reports it empty; before, the
/// routes that do not run the validator failed on an unnamed block reference.
#[test]
fn bodyless_functions_whose_linkage_names_a_definition_are_refused_by_name() {
    for linkage in [
        Linkage::Internal,
        Linkage::Private,
        Linkage::Weak,
        Linkage::LinkOnce,
        Linkage::WeakOdr,
        Linkage::LinkOnceOdr,
    ] {
        let mut module = defined_module();
        let sig = module.functions[0].ty;
        let mut missing = Function::new(FuncId::new(1), "missing", sig, BlockId::new(0));
        missing.linkage = linkage;
        module.functions.push(missing);
        match refuse_everywhere(&module) {
            AdapterError::BodylessDefinition {
                function,
                linkage: refused,
            } => {
                assert_eq!(function, "missing");
                assert_eq!(refused, linkage);
            }
            other => panic!("{linkage}: expected BodylessDefinition, got {other:?}"),
        }
    }
    // The predicate classifies every linkage explicitly.
    for (linkage, admitted) in [
        (Linkage::External, true),
        (Linkage::ExternalWeak, true),
        (Linkage::AvailableExternally, true),
        (Linkage::Internal, false),
        (Linkage::Private, false),
        (Linkage::Weak, false),
        (Linkage::LinkOnce, false),
        (Linkage::WeakOdr, false),
        (Linkage::LinkOnceOdr, false),
    ] {
        assert_eq!(
            function_declaration_linkage_is_admitted(linkage),
            admitted,
            "{linkage}"
        );
    }
}

// ---------------------------------------------------------------------------
// ExternalWeak under an object path that carries weak undefined references
// ---------------------------------------------------------------------------

/// `entry: () -> i64` returning `maybe() + *maybe_data`, where `maybe` is a
/// bodyless `ExternalWeak` function and `maybe_data` an initializer-less
/// `ExternalWeak` global.
fn weak_reference_module() -> Module {
    let mut module = defined_module();
    let sig = module.functions[0].ty;
    let mut maybe = Function::new(FuncId::new(1), "maybe", sig, BlockId::new(0));
    maybe.linkage = Linkage::ExternalWeak;
    module.functions.push(maybe);
    let mut data = data_global("maybe_data");
    data.linkage = Linkage::ExternalWeak;
    data.initializer = None;
    module.globals.push(data);
    module.functions[0].blocks[0].body = vec![
        InstrNode::new(Inst::Call {
            callee: FuncId::new(1),
            args: vec![],
        })
        .with_result(ValueId::new(0)),
        InstrNode::new(Inst::GlobalAddr {
            global: GlobalId::new(0),
        })
        .with_result(ValueId::new(1)),
        InstrNode::new(Inst::Load {
            ty: Ty::I64,
            ptr: ValueId::new(1),
            volatile: false,
            align: Some(8),
        })
        .with_result(ValueId::new(2)),
        InstrNode::new(Inst::BinOp {
            op: BinOp::Add,
            ty: Ty::I64,
            lhs: ValueId::new(0),
            rhs: ValueId::new(2),
        })
        .with_result(ValueId::new(3)),
        InstrNode::new(Inst::Return {
            values: vec![ValueId::new(3)],
        }),
    ];
    module
}

fn translate_admitting_weak_references(
    module: &Module,
) -> Result<Vec<trust_cg_lower::function::Function>, AdapterError> {
    translate_module_for_arch_with_tls_and_stats_with_license_and_weak_references(
        module,
        GuardCarrierArch::AArch64,
        TlsDialect::ElfLocalExec,
        &permit_unlicensed(),
        WeakUndefinedReferencePolicy::AdmitDeclarations,
    )
    .map(|(functions, _)| {
        functions
            .into_iter()
            .map(|(function, _)| function)
            .collect()
    })
}

#[test]
fn external_weak_declarations_are_admitted_only_by_the_weak_reference_policy() {
    let module = weak_reference_module();
    // Every default entry keeps refusing: only an object path that spells a
    // weak undefined symbol may opt in.
    assert!(matches!(
        refuse_everywhere(&module),
        AdapterError::UnsupportedLinkage {
            linkage: Linkage::ExternalWeak,
            ..
        }
    ));
    for arch in [GuardCarrierArch::AArch64, GuardCarrierArch::X86_64] {
        assert!(
            reject_unconsumed_v41_surface_with_weak_references(
                &module,
                arch,
                WeakUndefinedReferencePolicy::Refuse,
            )
            .is_err()
        );
        reject_unconsumed_v41_surface_with_weak_references(
            &module,
            arch,
            WeakUndefinedReferencePolicy::AdmitDeclarations,
        )
        .expect("bodyless function and initializer-less global are weak declarations");
    }
    assert_eq!(
        WeakUndefinedReferencePolicy::default(),
        WeakUndefinedReferencePolicy::Refuse
    );

    // Admitted, the declaration is never lowered as a body, the call names
    // the weak symbol, and the data address is GOT-indirect (a direct page
    // reference to an undefined weak symbol has no null-on-missing meaning).
    let functions = translate_admitting_weak_references(&module).expect("admitted");
    assert_eq!(
        functions
            .iter()
            .map(|f| f.name.as_str())
            .collect::<Vec<_>>(),
        ["entry"]
    );
    let opcodes: Vec<&Opcode> = functions[0]
        .blocks
        .values()
        .flat_map(|block| &block.instructions)
        .map(|instruction| &instruction.opcode)
        .collect();
    assert!(
        opcodes
            .iter()
            .any(|opcode| matches!(opcode, Opcode::Call { name, .. } if name == "maybe")),
        "{opcodes:?}"
    );
    assert!(
        opcodes
            .iter()
            .any(|opcode| matches!(opcode, Opcode::ExternRef { name } if name == "maybe_data")),
        "{opcodes:?}"
    );
    assert!(
        !opcodes
            .iter()
            .any(|opcode| matches!(opcode, Opcode::GlobalRef { name } if name == "maybe_data")),
        "{opcodes:?}"
    );
}

#[test]
fn admitted_external_weak_still_refuses_what_is_not_a_weak_declaration() {
    let refused = |module: &Module| {
        translate_admitting_weak_references(module)
            .expect_err("not a weak declaration")
            .to_string()
    };

    // A body cannot become a weak undefined reference.
    let mut bodied = defined_module();
    bodied.functions[0].linkage = Linkage::ExternalWeak;
    let error = refused(&bodied);
    assert!(
        error.contains("external_weak") && error.contains("body"),
        "{error}"
    );

    let with_global = |edit: fn(&mut Global)| {
        let mut module = weak_reference_module();
        edit(&mut module.globals[0]);
        module
    };
    let error = refused(&with_global(|global| {
        global.initializer = Some(Constant::Int(3));
    }));
    assert!(error.contains("initializer"), "{error}");
    let error = refused(&with_global(|global| {
        global.tls = Some(trust_ir::TlsModel::LocalExec);
    }));
    assert!(error.contains("thread-local"), "{error}");
    // Admitting weak references alone admits no import visibility; only the
    // AArch64 ELF module policy does (see
    // `visibility_is_consumed_on_definitions_and_on_imports_only_by_the_elf_module_policy`).
    assert!(matches!(
        translate_admitting_weak_references(&with_global(|global| {
            global.visibility = Visibility::Hidden;
        })),
        Err(AdapterError::ImportVisibilityUnsupported { .. })
    ));
}

fn translate_admitting_elf_function_facts(
    module: &Module,
) -> Result<Vec<trust_cg_lower::function::Function>, AdapterError> {
    translate_module_for_arch_with_tls_and_stats_with_license_and_weak_references(
        module,
        GuardCarrierArch::AArch64,
        TlsDialect::ElfLocalExec,
        &permit_unlicensed(),
        ObjectSymbolPolicy::AARCH64_ELF_MODULE,
    )
    .map(|(functions, _)| {
        functions
            .into_iter()
            .map(|(function, _)| function)
            .collect()
    })
}

/// v45 `Function.visibility` and `Function.section` on a definition are
/// refused on every default entry under their own facet, and by the
/// weak-reference-only policy on every architecture; only the AArch64 ELF
/// module policy admits them, for every linkage that is a global or weak
/// definition. The admitted function is still lowered.
#[test]
fn v45_function_visibility_and_sections_are_admitted_only_by_the_elf_module_policy() {
    assert_eq!(
        FunctionSymbolFactPolicy::default(),
        FunctionSymbolFactPolicy::Refuse
    );
    assert_eq!(
        ObjectSymbolPolicy::default(),
        ObjectSymbolPolicy::from(WeakUndefinedReferencePolicy::Refuse)
    );
    type FunctionEdit = fn(&mut Function);
    let rows: [(&str, FunctionEdit); 3] = [
        ("visibility", |f| f.visibility = Visibility::Hidden),
        ("visibility", |f| f.visibility = Visibility::Protected),
        ("section", |f| f.section = Some(".text.hot".into())),
    ];
    for (facet, edit) in rows {
        let mut module = defined_module();
        edit(&mut module.functions[0]);
        match refuse_everywhere(&module) {
            AdapterError::UnsupportedV45FunctionSurface {
                function,
                facet: refused,
                ..
            } => assert_eq!((function.as_str(), refused), ("entry", facet)),
            other => panic!("{facet}: refused under another name: {other:?}"),
        }
        for arch in [
            GuardCarrierArch::AArch64,
            GuardCarrierArch::X86_64,
            GuardCarrierArch::Riscv64,
        ] {
            assert!(
                matches!(
                    reject_unconsumed_v41_surface_with_weak_references(
                        &module,
                        arch,
                        WeakUndefinedReferencePolicy::AdmitDeclarations,
                    ),
                    Err(AdapterError::UnsupportedV45FunctionSurface { .. })
                ),
                "{facet} {arch:?}: the weak-reference policy alone admits no function fact"
            );
        }
        let functions = translate_admitting_elf_function_facts(&module)
            .unwrap_or_else(|error| panic!("{facet}: {error}"));
        assert_eq!(
            functions
                .iter()
                .map(|f| f.name.as_str())
                .collect::<Vec<_>>(),
            ["entry"]
        );
    }
    for linkage in [
        Linkage::External,
        Linkage::Weak,
        Linkage::LinkOnce,
        Linkage::WeakOdr,
        Linkage::LinkOnceOdr,
    ] {
        for visibility in [Visibility::Hidden, Visibility::Protected] {
            let mut module = defined_module();
            module.functions[0].linkage = linkage;
            module.functions[0].visibility = visibility;
            module.functions[0].section = Some("tcg_code".into());
            translate_admitting_elf_function_facts(&module)
                .unwrap_or_else(|error| panic!("{linkage} {visibility}: {error}"));
        }
    }
}

/// The AArch64 ELF module policy still refuses, by name, every function
/// fact no emitter spells: visibility on a module-local function, a section
/// on a codegen declaration, and `retained`. It admits hidden and protected
/// visibility on a codegen declaration (the emitters spell it on the
/// undefined symbol), which every other policy refuses under its facet. A
/// malformed section name is refused on every lane under every policy,
/// before the policy is consulted.
#[test]
fn admitted_function_facts_still_refuse_what_no_emitter_spells() {
    for linkage in [Linkage::Internal, Linkage::Private] {
        for visibility in [Visibility::Hidden, Visibility::Protected] {
            let mut module = defined_module();
            module.functions[0].linkage = linkage;
            module.functions[0].visibility = visibility;
            let error = translate_admitting_elf_function_facts(&module)
                .expect_err("local + non-default visibility");
            assert!(
                matches!(
                    &error,
                    AdapterError::FunctionVisibilityUnsupported {
                        function,
                        linkage: refused,
                        visibility: stated,
                        reason,
                    } if function == "entry"
                        && *refused == linkage
                        && *stated == visibility
                        && reason.contains("contradictory")
                ),
                "{linkage} {visibility}: {error:?}"
            );
            assert!(
                error.to_string().starts_with("[TCG-FUNCTION-VISIBILITY]"),
                "{error}"
            );
        }
    }

    // Three codegen declarations: a bodyless `External` import, an
    // `available_externally` function WITH a body (never emitted here), and
    // a bodyless `ExternalWeak` reference.
    let declaration = |linkage: Linkage, bodied: bool| {
        let mut module = defined_module();
        let sig = module.functions[0].ty;
        let mut import = Function::new(FuncId::new(1), "imported", sig, BlockId::new(0));
        import.linkage = linkage;
        if bodied {
            import.blocks = module.functions[0].blocks.clone();
        }
        module.functions.push(import);
        module
    };
    for (linkage, bodied) in [
        (Linkage::External, false),
        (Linkage::AvailableExternally, true),
        (Linkage::ExternalWeak, false),
    ] {
        for visibility in [Visibility::Hidden, Visibility::Protected] {
            let mut visible = declaration(linkage, bodied);
            visible.functions[1].visibility = visibility;
            let functions = translate_admitting_elf_function_facts(&visible)
                .unwrap_or_else(|error| panic!("{linkage} {visibility}: {error}"));
            assert_eq!(
                functions
                    .iter()
                    .map(|f| f.name.as_str())
                    .collect::<Vec<_>>(),
                ["entry"],
                "{linkage} {visibility}: a declaration emits no body"
            );
            match reject_unconsumed_v41_surface_with_weak_references(
                &visible,
                GuardCarrierArch::AArch64,
                WeakUndefinedReferencePolicy::AdmitDeclarations,
            ) {
                Err(AdapterError::UnsupportedV45FunctionSurface {
                    function,
                    facet: "visibility",
                    ..
                }) => assert_eq!(function, "imported"),
                other => panic!(
                    "{linkage} {visibility}: only the ELF module policy admits it: {other:?}"
                ),
            }
        }
        let mut sectioned = declaration(linkage, bodied);
        sectioned.functions[1].section = Some(".text.hot".into());
        match translate_admitting_elf_function_facts(&sectioned) {
            Err(AdapterError::FunctionSectionOnDeclaration { function, section }) => {
                assert_eq!(
                    (function.as_str(), section.as_str()),
                    ("imported", ".text.hot")
                );
            }
            other => panic!("{linkage}: a declaration's section must be refused: {other:?}"),
        }
        // Default visibility and no section: the admitted control.
        translate_admitting_elf_function_facts(&declaration(linkage, bodied))
            .unwrap_or_else(|error| panic!("{linkage}: plain declaration: {error}"));
    }

    for bad in ["", "has space", "tab\there", "nul\0byte"] {
        let mut module = defined_module();
        module.functions[0].section = Some(bad.to_string());
        let admitted = translate_admitting_elf_function_facts(&module).expect_err(bad);
        assert!(
            matches!(&admitted, AdapterError::MalformedFunctionSection { function, section, .. }
                if function == "entry" && section == bad),
            "{bad:?}: {admitted:?}"
        );
        assert!(admitted.to_string().starts_with("[TCG-SECTION-NAME]"));
        for arch in [
            GuardCarrierArch::AArch64,
            GuardCarrierArch::X86_64,
            GuardCarrierArch::Riscv64,
        ] {
            assert!(
                matches!(
                    reject_unconsumed_v41_surface(&module, arch),
                    Err(AdapterError::MalformedFunctionSection { .. })
                ),
                "{bad:?} {arch:?}"
            );
        }
    }

    let mut retained = defined_module();
    retained.functions[0].retained = true;
    assert!(matches!(
        translate_admitting_elf_function_facts(&retained),
        Err(AdapterError::UnsupportedV45FunctionSurface {
            facet: "retained",
            ..
        })
    ));
}

fn translate_admitting_macho_hidden_definitions(
    module: &Module,
    arch: GuardCarrierArch,
    policy: ObjectSymbolPolicy,
) -> Result<Vec<trust_cg_lower::function::Function>, AdapterError> {
    translate_module_for_arch_with_tls_and_stats_with_license_and_weak_references(
        module,
        arch,
        TlsDialect::MachOTlv,
        &permit_unlicensed(),
        policy,
    )
    .map(|(functions, _)| {
        functions
            .into_iter()
            .map(|(function, _)| function)
            .collect()
    })
}

/// The Mach-O module policies (AArch64 and x86-64) admit exactly one v45
/// function fact: `Hidden` on an `External` DEFINITION, which both Mach-O
/// module emitters spell `N_EXT | N_PEXT` (the rustc bridge's CGU-private
/// functions). Every shape Mach-O cannot spell is still refused, under the
/// same facet as on every default entry: protected visibility, hidden on a
/// weak/link-once or module-local definition, any visibility on a codegen
/// declaration (an undefined Mach-O symbol carries none), and a section; a
/// weak undefined reference stays refused by its linkage. The default policy
/// (every other x86-64 object path) still refuses the admitted shape.
#[test]
fn macho_module_policy_admits_hidden_external_definitions_only() {
    let macho_only = ObjectSymbolPolicy {
        weak_references: WeakUndefinedReferencePolicy::Refuse,
        function_symbol_facts: FunctionSymbolFactPolicy::AdmitMachOHiddenDefinitions,
        data_import_visibility: trust_cg_lower::DataImportVisibilityPolicy::Refuse,
    };
    assert_eq!(ObjectSymbolPolicy::AARCH64_MACHO_MODULE, macho_only);
    assert_eq!(ObjectSymbolPolicy::X86_64_MACHO_MODULE, macho_only);
    for (arch, policy) in [
        (
            GuardCarrierArch::AArch64,
            ObjectSymbolPolicy::AARCH64_MACHO_MODULE,
        ),
        (
            GuardCarrierArch::X86_64,
            ObjectSymbolPolicy::X86_64_MACHO_MODULE,
        ),
    ] {
        macho_policy_admits_hidden_external_definitions_only(arch, policy);
    }
    // The admitted shape is the Mach-O policies' alone among these: the
    // DEFAULT policy refuses it on every arch. (`Compiler::compile` gives
    // x86-64 ELF `X86_64_ELF_MODULE` rather than the default since ruling
    // OD-X86-ELF-DEFINITION-VISIBILITY-20261027; COFF and RISC-V keep the
    // default.)
    let mut hidden = defined_module();
    hidden.functions[0].visibility = Visibility::Hidden;
    for arch in [
        GuardCarrierArch::AArch64,
        GuardCarrierArch::X86_64,
        GuardCarrierArch::Riscv64,
    ] {
        match translate_admitting_macho_hidden_definitions(
            &hidden,
            arch,
            ObjectSymbolPolicy::default(),
        ) {
            Err(AdapterError::UnsupportedV45FunctionSurface {
                function,
                facet: "visibility",
                ..
            }) => assert_eq!(function, "entry", "{arch:?}"),
            other => panic!("{arch:?}: the default policy must refuse it: {other:?}"),
        }
    }
}

/// `ObjectSymbolPolicy::X86_64_ELF_MODULE` admits hidden and protected
/// visibility on a function DEFINITION and on a codegen DECLARATION, and
/// nothing else: the x86-64 ELF module emitter writes
/// `STV_HIDDEN`/`STV_PROTECTED` to the definition's `st_other` (ruling
/// OD-X86-ELF-DEFINITION-VISIBILITY-20261027) and to an undefined symbol's
/// (ruling OD-X86-ELF-UNDEFINED-REFERENCE-20261106), but spells no weak
/// undefined reference and no explicit function section. A module-local
/// definition's visibility stays refused as on every entry (trust-ir calls
/// the pair contradictory), and the BINDING of such a definition is not one
/// of these facts — it travels on trust-cg-codegen's
/// `aot_object_binds_module_local_functions`.
#[test]
fn x86_64_elf_module_policy_admits_definition_and_declaration_visibility() {
    let policy = ObjectSymbolPolicy::X86_64_ELF_MODULE;
    assert_eq!(
        policy,
        ObjectSymbolPolicy {
            weak_references: WeakUndefinedReferencePolicy::Refuse,
            function_symbol_facts: FunctionSymbolFactPolicy::AdmitElfSymbolVisibility,
            data_import_visibility: trust_cg_lower::DataImportVisibilityPolicy::Refuse,
        }
    );
    let translate = |module: &Module| {
        translate_admitting_macho_hidden_definitions(module, GuardCarrierArch::X86_64, policy)
    };
    // Admitted: both visibilities on a DEFINITION, with the default-visible
    // control.
    for visibility in [
        Visibility::Default,
        Visibility::Hidden,
        Visibility::Protected,
    ] {
        let mut module = defined_module();
        module.functions[0].visibility = visibility;
        let functions =
            translate(&module).unwrap_or_else(|error| panic!("external {visibility}: {error}"));
        assert_eq!(
            functions
                .iter()
                .map(|f| f.name.as_str())
                .collect::<Vec<_>>(),
            ["entry"]
        );
    }
    // Admitted since OD-X86-ELF-UNDEFINED-REFERENCE-20261106: a
    // DECLARATION's visibility, which that writer now spells on the undefined
    // symbol's `st_other` through one funnel.
    for visibility in [Visibility::Hidden, Visibility::Protected] {
        let mut module = defined_module();
        let sig = module.functions[0].ty;
        let mut declared = Function::new(FuncId::new(1), "declared", sig, BlockId::new(0));
        declared.visibility = visibility;
        module.functions.push(declared);
        let functions =
            translate(&module).unwrap_or_else(|error| panic!("declaration {visibility}: {error}"));
        // A codegen declaration lowers to no function, so the emitted list is
        // the definition alone — asserted exactly, as the definition loop
        // above does.
        assert_eq!(
            functions
                .iter()
                .map(|f| f.name.as_str())
                .collect::<Vec<_>>(),
            ["entry"],
            "{visibility}"
        );
        // The control that makes the line above evidence rather than a
        // tautology: translation of this very module still REFUSES under the
        // narrower facet, so what admitted it is
        // `AdmitElfSymbolVisibility`, not merely reaching the floor.
        let definition_only = ObjectSymbolPolicy {
            function_symbol_facts: FunctionSymbolFactPolicy::AdmitElfDefinitionFacts,
            ..policy
        };
        match translate_admitting_macho_hidden_definitions(
            &module,
            GuardCarrierArch::X86_64,
            definition_only,
        ) {
            Err(AdapterError::UnsupportedV45FunctionSurface {
                function,
                facet: "visibility",
                ..
            }) => assert_eq!(function, "declared", "{visibility}"),
            other => panic!(
                "{visibility} on a declaration must still be refused under \
                 AdmitElfDefinitionFacts: {other:?}"
            ),
        }
    }
    // Refused: a module-local definition's visibility, by its own facet.
    for linkage in [Linkage::Internal, Linkage::Private] {
        let mut module = defined_module();
        module.functions[0].linkage = linkage;
        module.functions[0].visibility = Visibility::Hidden;
        match translate(&module) {
            Err(AdapterError::FunctionVisibilityUnsupported { function, .. }) => {
                assert_eq!(function, "entry", "{linkage}")
            }
            other => panic!("{linkage} + hidden must be refused: {other:?}"),
        }
    }
    // Refused: an explicit function section.
    let mut sectioned = defined_module();
    sectioned.functions[0].section = Some(".text.hot".to_string());
    match translate(&sectioned) {
        Err(AdapterError::UnsupportedV45FunctionSurface {
            function,
            facet: "section",
            ..
        }) => assert_eq!(function, "entry"),
        other => panic!("an explicit function section must be refused: {other:?}"),
    }
}

fn macho_policy_admits_hidden_external_definitions_only(
    arch: GuardCarrierArch,
    policy: ObjectSymbolPolicy,
) {
    let translate =
        |module: &Module| translate_admitting_macho_hidden_definitions(module, arch, policy);
    // The admitted shape, and its default-visibility control.
    for visibility in [Visibility::Hidden, Visibility::Default] {
        let mut module = defined_module();
        module.functions[0].visibility = visibility;
        let functions = translate(&module)
            .unwrap_or_else(|error| panic!("{arch:?} external {visibility}: {error}"));
        assert_eq!(
            functions
                .iter()
                .map(|f| f.name.as_str())
                .collect::<Vec<_>>(),
            ["entry"],
            "{arch:?}"
        );
    }
    let refused =
        |module: &Module, function: &str, facet: &str, value: &str| match translate(module) {
            Err(AdapterError::UnsupportedV45FunctionSurface {
                function: refused,
                facet: stated,
                value: shown,
            }) => assert_eq!(
                (refused.as_str(), stated, shown.as_str()),
                (function, facet, value),
                "{arch:?}"
            ),
            other => panic!(
                "{arch:?} {function} {facet}={value}: expected the v45 refusal, got {other:?}"
            ),
        };
    let mut protected = defined_module();
    protected.functions[0].visibility = Visibility::Protected;
    refused(&protected, "entry", "visibility", "protected");
    for linkage in [
        Linkage::Weak,
        Linkage::LinkOnce,
        Linkage::WeakOdr,
        Linkage::LinkOnceOdr,
        Linkage::Internal,
        Linkage::Private,
    ] {
        let mut module = defined_module();
        module.functions[0].linkage = linkage;
        module.functions[0].visibility = Visibility::Hidden;
        refused(&module, "entry", "visibility", "hidden");
    }
    // A sibling object's reference to a hidden definition must be a plain
    // undefined symbol: a stated visibility on the declaration is refused.
    let mut declaration = defined_module();
    let sig = declaration.functions[0].ty;
    let mut import = Function::new(FuncId::new(1), "imported", sig, BlockId::new(0));
    import.visibility = Visibility::Hidden;
    declaration.functions.push(import);
    refused(&declaration, "imported", "visibility", "hidden");
    declaration.functions[1].visibility = Visibility::Default;
    translate(&declaration).unwrap_or_else(|error| panic!("{arch:?} plain declaration: {error}"));
    let mut sectioned = defined_module();
    sectioned.functions[0].section = Some("__TEXT,__hot".into());
    refused(&sectioned, "entry", "section", "\"__TEXT,__hot\"");
    let mut weak_reference = defined_module();
    let mut weak = Function::new(FuncId::new(1), "maybe", sig, BlockId::new(0));
    weak.linkage = Linkage::ExternalWeak;
    weak_reference.functions.push(weak);
    assert!(
        matches!(
            translate(&weak_reference),
            Err(AdapterError::UnsupportedLinkage { .. })
        ),
        "{arch:?}"
    );
}

#[test]
fn odr_linkages_and_available_externally_are_consumed() {
    // The ODR twins classify exactly like `Weak` / `LinkOnce`.
    for linkage in [
        Linkage::External,
        Linkage::Internal,
        Linkage::Private,
        Linkage::Weak,
        Linkage::LinkOnce,
        Linkage::WeakOdr,
        Linkage::LinkOnceOdr,
    ] {
        let mut module = defined_module();
        module.functions[0].linkage = linkage;
        accept_everywhere(&module);
        let mut module = defined_module();
        let mut global = data_global("TABLE");
        global.linkage = linkage;
        module.globals.push(global);
        accept_everywhere(&module);
    }
}

#[test]
fn available_externally_function_is_a_declaration_for_codegen() {
    // `entry` calls `helper`; `helper` carries a BODY but `available_externally`
    // linkage. The definition lives elsewhere, so the adapter lowers NO body for
    // it and the call resolves to the external symbol — exactly one LIR
    // function comes back.
    let mut module = defined_module();
    let sig = module.functions[0].ty;
    let mut helper = Function::new(FuncId::new(1), "helper", sig, BlockId::new(0));
    let mut block = Block::new(BlockId::new(0));
    block.body.push(
        InstrNode::new(Inst::Const {
            ty: Ty::I64,
            value: Constant::Int(9),
        })
        .with_result(ValueId::new(0)),
    );
    block.body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(0)],
    }));
    helper.blocks.push(block);
    helper.linkage = Linkage::AvailableExternally;
    module.functions.push(helper);
    // Rewrite `entry` to call `helper` and return its result.
    module.functions[0].blocks[0].body = vec![
        InstrNode::new(Inst::Call {
            callee: FuncId::new(1),
            args: vec![],
        })
        .with_result(ValueId::new(0)),
        InstrNode::new(Inst::Return {
            values: vec![ValueId::new(0)],
        }),
    ];
    let lowered =
        permit_translate_module(&module).expect("available_externally callee is accepted");
    assert_eq!(
        lowered.len(),
        1,
        "no body is emitted for an available_externally function"
    );
    assert_eq!(lowered[0].0.name, "entry");

    // The SINGLE-FUNCTION entries must agree with the module entries: what
    // they skip, these refuse. Handing `helper` itself to `translate_function`
    // must not produce a LIR body for a symbol another object defines.
    let names: HashMap<FuncId, String> = module
        .functions
        .iter()
        .map(|f| (f.id, f.name.clone()))
        .collect();
    for (entry_name, result) in [
        (
            "translate_function",
            trust_cg_lower::translate_function_with_license(
                &module.functions[1],
                &module,
                &permit_unlicensed(),
            )
            .map(|_| ()),
        ),
        (
            "translate_function_with_names",
            trust_cg_lower::translate_function_with_names_and_license(
                &module.functions[1],
                &module,
                &names,
                &permit_unlicensed(),
            )
            .map(|_| ()),
        ),
    ] {
        assert!(
            matches!(
                result,
                Err(AdapterError::DeclarationNotLowerable { ref function, linkage })
                    if function == "helper" && linkage == Linkage::AvailableExternally
            ),
            "{entry_name} must refuse an available_externally body: {result:?}"
        );
    }
    // The caller is still lowerable through the single-function entry.
    trust_cg_lower::translate_function_with_license(
        &module.functions[0],
        &module,
        &permit_unlicensed(),
    )
    .expect("the caller is a definition");

    // The same shape with an `External` helper lowers BOTH bodies: the control,
    // through the module entry and the single-function entry alike.
    module.functions[1].linkage = Linkage::External;
    let lowered = permit_translate_module(&module).expect("external helper is accepted");
    assert_eq!(lowered.len(), 2);
    trust_cg_lower::translate_function_with_license(
        &module.functions[1],
        &module,
        &permit_unlicensed(),
    )
    .expect("an external body is lowered");
    trust_cg_lower::translate_function_with_names_and_license(
        &module.functions[1],
        &module,
        &names,
        &permit_unlicensed(),
    )
    .expect("an external body is lowered with names");

    // A bodyless `External` declaration is the other codegen-declaration shape,
    // and the single-function entries refuse it the same way.
    module.functions[1].blocks.clear();
    assert!(matches!(
        trust_cg_lower::translate_function_with_license(&module.functions[1], &module, &permit_unlicensed()),
        Err(AdapterError::DeclarationNotLowerable { function, linkage })
            if function == "helper" && linkage == Linkage::External
    ));
}

#[test]
fn target_neutral_gate_is_the_arch_gate_minus_the_feature_clause() {
    // The wasm lane shares the target-neutral half of the gate. It must carry
    // every refusal that does not depend on the target, and ONLY those: the
    // feature vocabulary and per-target section placement are the arch
    // entry's business.
    let control = defined_module();
    reject_unconsumed_v41_target_neutral_surface(&control).expect("control is accepted");
    reject_unconsumed_v41_surface(&control, GuardCarrierArch::AArch64)
        .expect("control is accepted by the arch gate");

    let mut featured = defined_module();
    featured.functions[0].attrs.target_features = vec!["not-a-feature".to_string()];
    reject_unconsumed_v41_target_neutral_surface(&featured)
        .expect("the feature clause is target-dependent and not part of the neutral gate");
    assert!(matches!(
        reject_unconsumed_v41_surface(&featured, GuardCarrierArch::AArch64),
        Err(AdapterError::UnknownTargetFeature { feature, .. }) if feature == "not-a-feature"
    ));

    let mut asm = defined_module();
    asm.global_asm.push(".globl nothing".to_string());
    let mut naked = defined_module();
    naked.functions[0].attrs.naked = true;
    let mut weak_undef = defined_module();
    weak_undef.functions[0].linkage = Linkage::ExternalWeak;
    // A MALFORMED section is a neutral refusal; a well-formed one is a
    // target-dependent placement decision (see
    // `well_formed_global_section_reaches_aarch64_and_is_refused_elsewhere`).
    let mut sectioned = defined_module();
    let mut global = data_global("TABLE");
    global.section = Some("bad name".to_string());
    sectioned.globals.push(global);
    let mut hidden_import = defined_module();
    let mut global = data_global("EXTERN");
    global.linkage = Linkage::External;
    global.initializer = None;
    global.visibility = Visibility::Hidden;
    hidden_import.globals.push(global);
    let mut terminated = defined_module();
    terminated.proof_obligations.push(obligation(
        0,
        ObligationKind::Termination,
        ProofStatus::Certified,
    ));
    for (what, module) in [
        ("global_asm", asm),
        ("naked", naked),
        ("external_weak", weak_undef),
        ("malformed section", sectioned),
        ("import visibility", hidden_import),
        ("completed Termination obligation", terminated),
    ] {
        let neutral = reject_unconsumed_v41_target_neutral_surface(&module)
            .expect_err(what)
            .to_string();
        let arch = reject_unconsumed_v41_surface(&module, GuardCarrierArch::X86_64)
            .expect_err(what)
            .to_string();
        assert_eq!(
            neutral, arch,
            "{what}: both gates must give the same refusal"
        );
    }
}

// ---------------------------------------------------------------------------
// Function attributes
// ---------------------------------------------------------------------------

#[test]
fn naked_function_is_refused() {
    let mut module = defined_module();
    module.functions[0].attrs.naked = true;
    assert!(matches!(
        refuse_everywhere(&module),
        AdapterError::NakedFunction { function } if function == "entry"
    ));
}

#[test]
fn target_features_are_validated_against_the_arch_vocabulary() {
    // Every modeled aarch64 feature is accepted on the aarch64 carrier arch.
    let mut module = defined_module();
    module.functions[0].attrs.target_features = known_target_features(GuardCarrierArch::AArch64)
        .iter()
        .map(|feature| feature.to_string())
        .collect();
    assert!(!module.functions[0].attrs.target_features.is_empty());
    accept_everywhere(&module);
    permit_translate_module_for_arch(&module, GuardCarrierArch::AArch64)
        .expect("aarch64 vocabulary");

    // An x86 feature is refused on aarch64 and accepted on x86-64, and vice
    // versa: the vocabulary is per target, never a union.
    let mut module = defined_module();
    module.functions[0].attrs.target_features = vec!["avx2".to_string()];
    match permit_translate_module_for_arch(&module, GuardCarrierArch::AArch64) {
        Err(AdapterError::UnknownTargetFeature {
            function,
            feature,
            arch,
        }) => {
            assert_eq!(function, "entry");
            assert_eq!(feature, "avx2");
            assert_eq!(arch, GuardCarrierArch::AArch64);
        }
        other => panic!("expected UnknownTargetFeature, got {other:?}"),
    }
    permit_translate_module_for_arch(&module, GuardCarrierArch::X86_64)
        .expect("avx2 is an x86 feature");
    let mut module = defined_module();
    module.functions[0].attrs.target_features = vec!["lse".to_string()];
    assert!(matches!(
        permit_translate_module_for_arch(&module, GuardCarrierArch::X86_64),
        Err(AdapterError::UnknownTargetFeature { feature, arch: GuardCarrierArch::X86_64, .. })
            if feature == "lse"
    ));

    // A name outside every vocabulary — including a `+`-prefixed spelling —
    // is refused on every entry.
    for unknown in ["mmx-nonsense", "+neon", ""] {
        let mut module = defined_module();
        module.functions[0].attrs.target_features = vec!["neon".to_string(), unknown.to_string()];
        assert!(
            matches!(
                refuse_everywhere(&module),
                AdapterError::UnknownTargetFeature { feature, .. } if feature == unknown
            ),
            "{unknown:?}"
        );
    }
    // RISC-V models no optional feature yet: nothing may be assumed.
    assert!(known_target_features(GuardCarrierArch::Riscv64).is_empty());
}

#[test]
fn display_path_is_accepted_as_metadata() {
    let mut module = defined_module();
    module.functions[0].display_path = Some("crate::entry".to_string());
    accept_everywhere(&module);
}

// ---------------------------------------------------------------------------
// Module and global residue
// ---------------------------------------------------------------------------

#[test]
fn global_asm_is_refused_not_dropped() {
    let mut module = defined_module();
    module
        .global_asm
        .push(".globl marker\nmarker:\n  ret".to_string());
    match refuse_everywhere(&module) {
        AdapterError::GlobalAsmUnsupported { module, blocks } => {
            assert_eq!(module, "v41_contract_surface");
            assert_eq!(blocks, 1);
        }
        other => panic!("expected GlobalAsmUnsupported, got {other:?}"),
    }
}

#[test]
fn malformed_global_section_is_refused_everywhere() {
    for name in ["", "has space", "nul\0byte", "tab\tname"] {
        let mut sectioned = defined_module();
        let mut global = data_global("TABLE");
        global.section = Some(name.to_string());
        sectioned.globals.push(global);
        match refuse_everywhere(&sectioned) {
            AdapterError::MalformedGlobalSection {
                global, section, ..
            } => {
                assert_eq!(global, "TABLE");
                assert_eq!(section, name);
            }
            other => panic!("{name:?}: expected MalformedGlobalSection, got {other:?}"),
        }
    }
    let mut long = defined_module();
    let mut global = data_global("TABLE");
    global.section = Some("x".repeat(1025));
    long.globals.push(global);
    assert!(matches!(
        refuse_everywhere(&long),
        AdapterError::MalformedGlobalSection { .. }
    ));
}

/// A well-formed name is CONSUMED on AArch64 (the object emitter places or
/// refuses it by format, pinned in trust-cg-codegen) and refused before ISel
/// on the targets whose emitters have no placement.
#[test]
fn well_formed_global_section_reaches_aarch64_and_is_refused_elsewhere() {
    for name in [".init_array", "__DATA,__mod_init_func", ".text.startup"] {
        let mut sectioned = defined_module();
        let mut global = data_global("TABLE");
        global.section = Some(name.to_string());
        sectioned.globals.push(global);
        reject_unconsumed_v41_target_neutral_surface(&sectioned)
            .unwrap_or_else(|error| panic!("{name}: shared floor must pass: {error}"));
        reject_unconsumed_v41_surface(&sectioned, GuardCarrierArch::AArch64)
            .unwrap_or_else(|error| panic!("{name}: AArch64 must pass: {error}"));
        accept_everywhere(&sectioned);
        for arch in [GuardCarrierArch::X86_64, GuardCarrierArch::Riscv64] {
            match reject_unconsumed_v41_surface(&sectioned, arch) {
                Err(AdapterError::UnsupportedGlobalSection {
                    global,
                    section,
                    arch: refused_arch,
                }) => {
                    assert_eq!((global.as_str(), section.as_str()), ("TABLE", name));
                    assert_eq!(refused_arch, arch);
                }
                other => {
                    panic!("{name} on {arch:?}: expected UnsupportedGlobalSection, got {other:?}")
                }
            }
        }
    }
}

/// A definition's visibility is consumed on every entry. An import's is
/// refused by name on every default entry and admitted only by the AArch64
/// ELF module policy (L02-P6), which spells it on the undefined symbol:
/// an initializer-less `External` import, an `AvailableExternally` global
/// with or without an initializer, and an `ExternalWeak` reference.
#[test]
fn visibility_is_consumed_on_definitions_and_on_imports_only_by_the_elf_module_policy() {
    for visibility in [Visibility::Hidden, Visibility::Protected] {
        // A DEFINITION (initializer present) carries its visibility through
        // to the object emitters.
        for linkage in [Linkage::External, Linkage::Internal, Linkage::WeakOdr] {
            let mut module = defined_module();
            let mut global = data_global("TABLE");
            global.linkage = linkage;
            global.visibility = visibility;
            module.globals.push(global);
            accept_everywhere(&module);
        }
        // An IMPORT (no initializer, external linkage): refused rather than
        // widened to default on every default entry, admitted by the ELF
        // module policy.
        let mut module = defined_module();
        let mut global = data_global("TABLE");
        global.linkage = Linkage::External;
        global.initializer = None;
        global.visibility = visibility;
        module.globals.push(global);
        match refuse_everywhere(&module) {
            AdapterError::ImportVisibilityUnsupported {
                global,
                visibility: refused,
            } => {
                assert_eq!(global, "TABLE");
                assert_eq!(refused, visibility);
            }
            other => panic!("{visibility}: expected ImportVisibilityUnsupported, got {other:?}"),
        }
        translate_admitting_elf_function_facts(&module)
            .unwrap_or_else(|error| panic!("{visibility} import: {error}"));
        // `available_externally` is an import WHATEVER its initializer.
        for initialized in [true, false] {
            let mut module = defined_module();
            let mut global = data_global("TABLE");
            global.linkage = Linkage::AvailableExternally;
            global.visibility = visibility;
            if !initialized {
                global.initializer = None;
            }
            module.globals.push(global);
            assert!(matches!(
                refuse_everywhere(&module),
                AdapterError::ImportVisibilityUnsupported { .. }
            ));
            translate_admitting_elf_function_facts(&module).unwrap_or_else(|error| {
                panic!("{visibility} available_externally {initialized}: {error}")
            });
        }
        // A weak reference: the weak-reference policy alone refuses its
        // visibility; the ELF module policy admits it.
        let mut module = defined_module();
        let mut global = data_global("TABLE");
        global.linkage = Linkage::ExternalWeak;
        global.initializer = None;
        global.visibility = visibility;
        module.globals.push(global);
        assert!(matches!(
            translate_admitting_weak_references(&module),
            Err(AdapterError::ImportVisibilityUnsupported { .. })
        ));
        translate_admitting_elf_function_facts(&module)
            .unwrap_or_else(|error| panic!("{visibility} external_weak: {error}"));
    }
}

#[test]
fn retained_definition_is_accepted() {
    let mut retained = defined_module();
    let mut global = data_global("TABLE");
    global.retained = true;
    retained.globals.push(global);
    accept_everywhere(&retained);
}

// ---------------------------------------------------------------------------
// Proof surface
// ---------------------------------------------------------------------------

#[test]
fn unrecognized_obligation_kinds_grant_no_authority() {
    // `Discharged` for the first claim, not `Certified`: a `Certified` row
    // with no CleanCic certificate is refused first by trust-ir's structural
    // pass (`CertifiedWithoutCleanCic`, consumed by name since KIND 4), so it
    // would never reach the kind arm this test pins.
    let claims = [
        (ObligationKind::Termination, ProofStatus::Discharged),
        (ObligationKind::Ownership, ProofStatus::Trusted),
        // A PINNED namespace (`trust.vc`, one of trust-ir-build's
        // `ADMITTED_OBLIGATION_NAMESPACES`): an unpinned one is refused first
        // by trust-ir's structural pass (`UnpinnedCustomObligationNamespace`,
        // consumed by name since KIND 4) and would never reach the kind arm
        // this test pins.
        (
            ObligationKind::Custom {
                namespace: "trust.vc".to_string(),
                name: "audited".to_string(),
            },
            ProofStatus::Discharged,
        ),
    ];
    for (kind, status) in claims {
        let mut module = defined_module();
        module
            .proof_obligations
            .push(obligation(0, kind.clone(), status));
        match refuse_everywhere(&module) {
            AdapterError::UnrecognizedObligationKind {
                obligation,
                kind: refused,
                status: refused_status,
            } => {
                assert_eq!(obligation, 0);
                assert_eq!(refused, kind.to_string());
                assert_eq!(refused_status, status);
            }
            other => panic!("{kind}: expected UnrecognizedObligationKind, got {other:?}"),
        }
    }

    // Pending / failed obligations of these kinds claim nothing and pass
    // through as data (the census reports them as unfinished).
    for status in [ProofStatus::Pending, ProofStatus::Failed] {
        let mut module = defined_module();
        module
            .proof_obligations
            .push(obligation(0, ObligationKind::Termination, status));
        accept_everywhere(&module);
    }

    // A recognized kind with a completed status is still accepted here; the
    // guard kernel separately refuses to turn it into authority.
    let mut module = defined_module();
    module.proof_obligations.push(obligation(
        0,
        ObligationKind::MemorySafety,
        ProofStatus::Discharged,
    ));
    accept_everywhere(&module);
}

#[test]
fn external_evidence_inheritance_is_refused_local_is_accepted() {
    let mut module = defined_module();
    module.proof_obligations.push(obligation(
        0,
        ObligationKind::MemorySafety,
        ProofStatus::Pending,
    ));
    module.proof_obligations.push(obligation(
        1,
        ObligationKind::MemorySafety,
        ProofStatus::Discharged,
    ));
    let import = module
        .intern_import(ModuleImport::new(
            "sibling",
            trust_ir::proof::ProofDigest::zero(),
        ))
        .expect("Module::intern_import: test fixture");
    module.proof_certificates.push(ProofCertificate {
        obligation: ProofId::new(0),
        prover: "hand".to_string(),
        evidence: ProofEvidence::InheritedFromCallee {
            callee: FuncId::new(0),
            obligation: ProofId::new(1),
            external: Some(ExternRef::new(import, "sibling_fn")),
        },
        assurance: None,
    });
    match refuse_everywhere(&module) {
        AdapterError::ExternalEvidenceInheritance {
            certificate,
            obligation,
            import: refused_import,
            symbol,
        } => {
            assert_eq!(certificate, 0);
            assert_eq!(obligation, 0);
            assert_eq!(refused_import, import.index());
            assert_eq!(symbol, "sibling_fn");
        }
        other => panic!("expected ExternalEvidenceInheritance, got {other:?}"),
    }

    // Module-local inheritance (`external: None`) keeps its pre-v41 meaning.
    let mut local = defined_module();
    local.proof_obligations.push(obligation(
        0,
        ObligationKind::MemorySafety,
        ProofStatus::Pending,
    ));
    local.proof_obligations.push(obligation(
        1,
        ObligationKind::MemorySafety,
        ProofStatus::Discharged,
    ));
    local.proof_certificates.push(ProofCertificate {
        obligation: ProofId::new(0),
        prover: "hand".to_string(),
        evidence: ProofEvidence::InheritedFromCallee {
            callee: FuncId::new(0),
            obligation: ProofId::new(1),
            external: None,
        },
        assurance: None,
    });
    accept_everywhere(&local);

    // The imports TABLE alone is accepted; only a reference into it from
    // proof evidence is refused.
    let mut table_only = defined_module();
    table_only
        .intern_import(ModuleImport::new(
            "sibling",
            trust_ir::proof::ProofDigest::zero(),
        ))
        .expect("Module::intern_import: test fixture");
    accept_everywhere(&table_only);
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
