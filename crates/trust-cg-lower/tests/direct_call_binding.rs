// Exact module binding for ordinary direct TrustIR calls.

use trust_cg_lower::instructions::{DirectCallBinding, Opcode};
use trust_cg_lower::{GuardCarrierArch, TlsDialect};
use trust_ir::{
    BinOp, Block, BlockId, CallingConv, Constant, FieldDef, FuncId, FuncTy, Function, Inst,
    InstrNode, Linkage, Module, StructDef, StructId, StructRepr, Ty, ValueId,
};

fn direct_call_module(linkage: Linkage) -> Module {
    let mut module = Module::new("ordinary_direct_binding");
    let sig = module
        .add_func_type(FuncTy {
            params: vec![Ty::I64],
            returns: vec![Ty::I64],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");

    let mut target = Function::new(FuncId::new(0), "add_one", sig, BlockId::new(0));
    target.linkage = linkage;
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

fn caller_binding(
    functions: &[(trust_cg_lower::Function, trust_cg_lower::ProofContext)],
) -> DirectCallBinding {
    functions
        .iter()
        .find(|(function, _)| function.name == "entry")
        .expect("caller lowers")
        .0
        .blocks
        .values()
        .flat_map(|block| &block.instructions)
        .find_map(|instruction| match &instruction.opcode {
            Opcode::Call { binding, .. } => Some(*binding),
            _ => None,
        })
        .expect("caller contains one direct call")
}

/// Put a real natural loop in front of a single-block function's body:
/// `entry -> header(i) -> { latch -> header | exit: the original body }`,
/// counting `i` from 0 to 3. Values defined in the entry block (the
/// parameters) dominate every other block, so the original body moves
/// unchanged into the exit block. Returns the loop header.
fn wrap_body_in_counting_loop(function: &mut Function) -> BlockId {
    assert_eq!(function.blocks.len(), 1, "wraps single-block bodies");
    let mut entry = function.blocks.remove(0);
    let original_body = std::mem::take(&mut entry.body);
    let (header, latch, exit) = (BlockId::new(1), BlockId::new(2), BlockId::new(3));
    let (zero, i, bound, cond, one, next) = (
        ValueId::new(900),
        ValueId::new(901),
        ValueId::new(902),
        ValueId::new(903),
        ValueId::new(904),
        ValueId::new(905),
    );
    entry.body.push(
        InstrNode::new(Inst::Const {
            ty: Ty::I64,
            value: Constant::Int(0),
        })
        .with_result(zero),
    );
    entry.body.push(InstrNode::new(Inst::Br {
        target: header,
        args: vec![zero],
    }));
    let mut header_block = Block::new(header);
    header_block.params.push((i, Ty::I64));
    header_block.body.push(
        InstrNode::new(Inst::Const {
            ty: Ty::I64,
            value: Constant::Int(3),
        })
        .with_result(bound),
    );
    header_block.body.push(
        InstrNode::new(Inst::ICmp {
            op: trust_ir::ICmpOp::Ult,
            ty: Ty::I64,
            lhs: i,
            rhs: bound,
        })
        .with_result(cond),
    );
    header_block.body.push(InstrNode::new(Inst::CondBr {
        cond,
        then_target: latch,
        then_args: vec![],
        else_target: exit,
        else_args: vec![],
    }));
    let mut latch_block = Block::new(latch);
    latch_block.body.push(
        InstrNode::new(Inst::Const {
            ty: Ty::I64,
            value: Constant::Int(1),
        })
        .with_result(one),
    );
    latch_block.body.push(
        InstrNode::new(Inst::BinOp {
            op: BinOp::Add,
            ty: Ty::I64,
            lhs: i,
            rhs: one,
        })
        .with_result(next),
    );
    latch_block.body.push(InstrNode::new(Inst::Br {
        target: header,
        args: vec![next],
    }));
    let mut exit_block = Block::new(exit);
    exit_block.body = original_body;
    function.blocks = vec![entry, header_block, latch_block, exit_block];
    header
}

fn add_div_annotation_clone_trigger(module: &mut Module) {
    let caller = module
        .functions
        .iter_mut()
        .find(|function| function.name == "entry")
        .expect("entry function");
    caller.blocks[0].body.splice(
        0..0,
        [
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(84),
            })
            .with_result(ValueId::new(100)),
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(2),
            })
            .with_result(ValueId::new(101)),
            InstrNode::new(Inst::BinOp {
                op: BinOp::UDiv,
                ty: Ty::I64,
                lhs: ValueId::new(100),
                rhs: ValueId::new(101),
            })
            .with_result(ValueId::new(102)),
        ],
    );
}

fn add_swift_aggregate_clone_trigger(module: &mut Module) {
    let struct_id = StructId::new(99);
    module.structs.push(StructDef {
        origin: None,
        id: struct_id,
        name: "SwiftPair".to_string(),
        fields: vec![
            FieldDef {
                name: "left".to_string(),
                ty: Ty::I64,
                offset: None,
            },
            FieldDef {
                name: "right".to_string(),
                ty: Ty::I64,
                offset: None,
            },
        ],
        size: None,
        align: None,
        repr: StructRepr::C,
    });
    let aggregate = Ty::Struct(struct_id);
    let signature = module
        .add_func_type(FuncTy {
            params: vec![aggregate.clone()],
            returns: vec![aggregate.clone()],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut function = Function::new(
        FuncId::new(99),
        "swift_clone_trigger",
        signature,
        BlockId::new(0),
    );
    function.calling_conv = CallingConv::Swift;
    let mut entry = Block::new(BlockId::new(0));
    entry.params.push((ValueId::new(0), aggregate));
    entry.body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(0)],
    }));
    function.blocks.push(entry);
    module.functions.push(function);
}

#[test]
fn prepared_compatibility_transforms_invalidate_only_changed_source_manifests() {
    for swift in [false, true] {
        let mut module = direct_call_module(Linkage::Internal);
        let changed = if swift {
            add_swift_aggregate_clone_trigger(&mut module);
            FuncId::new(99)
        } else {
            add_div_annotation_clone_trigger(&mut module);
            FuncId::new(1)
        };
        // trust-ir admits a `SourceProvenance` carrier only on a function with
        // at least one natural loop, and since KIND 4 the adapter's
        // prerequisites refuse an invalid carrier by name
        // (`InvalidSourceProvenance`), so every body is wrapped in a real
        // counting loop FIRST — a function's semantic digest covers the bodies
        // it reaches, so no digest is taken until every body is final — and
        // each carrier then names its own header.
        let headers: Vec<BlockId> = module
            .functions
            .iter_mut()
            .map(wrap_body_in_counting_loop)
            .collect();
        for (index, header) in headers.into_iter().enumerate() {
            let digest = module
                .source_provenance_semantic_digest(module.functions[index].id)
                .unwrap();
            module.functions[index].source_provenance = Some(trust_ir::SourceProvenance::new(
                trust_ir::proof::ProofDigest::sha256([1; 32]),
                digest,
                vec![trust_ir::SourceLoopProvenance {
                    source_loop_id: 0,
                    hir_local_id: 1,
                    header,
                    bindings: vec![],
                }],
            ));
        }
        let prepared =
            trust_cg_lower::prepare_module_for_lir(&module, GuardCarrierArch::AArch64).unwrap();
        assert!(!std::ptr::eq(prepared.as_ref(), &module));
        // The prepared module carries no carrier trust-ir would refuse: a
        // manifest survives only while its semantic digest is still the
        // digest of its function IN THE PREPARED MODULE. The changed function
        // always loses its manifest; an untouched function keeps it exactly
        // when the transform left the module image it was hashed over alone
        // (the div annotation does; the Swift scalarization registers a new
        // signature, so it stales every carrier, and every carrier goes).
        let structural = trust_ir_build::validate_module(prepared.module());
        assert!(
            !structural.iter().any(|error| {
                matches!(
                    error,
                    trust_ir_build::ValidationError::InvalidSourceProvenance { .. }
                )
            }),
            "prepared module carries a stale source manifest: {structural:?}"
        );
        for (original, prepared_fn) in module.functions.iter().zip(&prepared.module().functions) {
            assert!(
                original.source_provenance.is_some(),
                "input owner is untouched"
            );
            let stored = original
                .source_provenance
                .as_ref()
                .map(|carrier| carrier.semantic_body_digest);
            let still_bound = prepared
                .module()
                .source_provenance_semantic_digest(prepared_fn.id)
                .ok()
                == stored;
            if prepared_fn.id == changed {
                assert!(
                    prepared_fn.source_provenance.is_none(),
                    "changed function loses old manifest"
                );
            } else if still_bound {
                assert_eq!(prepared_fn.source_provenance, original.source_provenance);
            } else {
                assert!(
                    swift && prepared_fn.source_provenance.is_none(),
                    "an untouched function keeps its manifest unless the transform changed \
                     the module image it was hashed over (only the Swift rewrite does)"
                );
            }
        }
        // Idempotent preparation does not erase untouched metadata on another
        // pass. These infallible helpers have no partial-Err return path.
        let again =
            trust_cg_lower::prepare_module_for_lir(prepared.as_ref(), GuardCarrierArch::AArch64)
                .unwrap();
        assert!(std::ptr::eq(again.as_ref(), prepared.as_ref()));
    }
}

#[test]
fn swift_preparation_drops_old_summary_and_remaps_only_scalar_parameter_attributes() {
    let mut source = direct_call_module(Linkage::Internal);
    add_swift_aggregate_clone_trigger(&mut source);
    let signature = source.functions[2].ty;
    source.func_types[signature.as_usize()].params.push(Ty::Ptr);
    let scalar = trust_ir::ParamAttrs {
        noalias: true,
        nonnull: true,
        align: Some(8),
        ..Default::default()
    };
    source.functions[2].blocks[0]
        .params
        .push((ValueId::new(1), Ty::Ptr));
    source.functions[2].attrs.params = vec![
        trust_ir::ParamAttrs {
            nonnull: true,
            ..Default::default()
        },
        scalar.clone(),
    ];
    source.functions[2].summary = Some(trust_ir::FunctionSummary {
        proved: true,
        params: vec!["old_aggregate".into(), "pointer".into()],
        ..Default::default()
    });
    let prepared =
        trust_cg_lower::prepare_module_for_lir(&source, GuardCarrierArch::AArch64).unwrap();
    let target = &prepared.module().functions[2];
    assert!(target.summary.is_none());
    assert_eq!(
        target.attrs.params,
        [
            trust_ir::ParamAttrs::default(),
            trust_ir::ParamAttrs::default(),
            scalar
        ]
    );
    assert!(source.functions[2].summary.is_some());
    assert_eq!(source.functions[2].attrs.params.len(), 2);

    for sret in [false, true] {
        let mut input = source.clone();
        input.functions[2].attrs.params[0].byval = !sret;
        input.functions[2].attrs.params[0].sret = sret;
        let before = input.clone();
        let error =
            trust_cg_lower::prepare_module_for_lir(&input, GuardCarrierArch::AArch64).unwrap_err();
        assert!(error.to_string().contains("byval/sret ABI attributes"));
        assert_eq!(
            input, before,
            "unsupported ABI preparation must not mutate input"
        );
    }
}

fn vararg_direct_call_module() -> Module {
    let mut module = direct_call_module(Linkage::Internal);
    let signature = module.functions[0].ty;
    module.func_types[signature.as_usize()].is_vararg = true;
    module
}

fn assert_validated_clone_refuses_local_identity(label: &str, module: &Module) {
    let error = trust_cg_lower::translate_module_for_arch_with_tls_and_validation_with_license(
        module,
        GuardCarrierArch::AArch64,
        TlsDialect::default(),
        &permit_unlicensed(),
    )
    .expect_err("a validated adapter-owned clone must not retain local identity");
    let diagnostic = error.to_string();
    assert!(
        diagnostic.contains("adapter-owned module clone")
            && diagnostic.contains("1 direct edge(s)"),
        "{label}: {diagnostic}"
    );
}

#[test]
fn validated_translation_seals_internal_and_private_direct_calls() {
    for linkage in [Linkage::Internal, Linkage::Private] {
        let module = direct_call_module(linkage);
        let (mut functions, receipt) =
            trust_cg_lower::translate_module_for_arch_with_tls_and_validation_with_license(
                &module,
                GuardCarrierArch::default(),
                TlsDialect::default(),
                &permit_unlicensed(),
            )
            .expect("validated direct module lowers");
        assert_eq!(receipt.exact_module_call_count(), 1, "{linkage}");
        assert_eq!(
            caller_binding(&functions),
            DirectCallBinding::ExactModuleFunction { function: 0 },
            "{linkage}"
        );
        receipt
            .replay_exact_module_calls(&functions)
            .expect("source-owned exact direct binding replays");

        let caller = functions
            .iter_mut()
            .find(|(function, _)| function.name == "entry")
            .expect("caller lowers");
        let call = caller
            .0
            .blocks
            .values_mut()
            .flat_map(|block| &mut block.instructions)
            .find(|instruction| matches!(instruction.opcode, Opcode::Call { .. }))
            .expect("caller contains call");
        let Opcode::Call { binding, .. } = &mut call.opcode else {
            unreachable!()
        };
        *binding = DirectCallBinding::Interposable;
        receipt
            .replay_exact_module_calls(&functions)
            .expect_err("binding mutation must invalidate the sealed receipt");
    }
}

#[test]
fn legacy_or_external_direct_calls_do_not_gain_exact_authority() {
    let internal = direct_call_module(Linkage::Internal);
    let legacy = trust_cg_lower::translate_module_for_arch_with_tls_with_license(
        &internal,
        GuardCarrierArch::default(),
        TlsDialect::default(),
        &permit_unlicensed(),
    )
    .expect("legacy translation remains diagnostic-only");
    assert_eq!(caller_binding(&legacy), DirectCallBinding::Interposable);

    let external = direct_call_module(Linkage::External);
    let (validated_external, receipt) =
        trust_cg_lower::translate_module_for_arch_with_tls_and_validation_with_license(
            &external,
            GuardCarrierArch::default(),
            TlsDialect::default(),
            &permit_unlicensed(),
        )
        .expect("external direct call lowers");
    assert_eq!(receipt.exact_module_call_count(), 0);
    assert_eq!(
        caller_binding(&validated_external),
        DirectCallBinding::Interposable
    );
}

#[test]
fn internal_intrinsic_like_name_keeps_its_module_body_and_exact_binding() {
    let mut module = direct_call_module(Linkage::Internal);
    module.functions[0].name = "llvm.bitreverse.i64".to_string();
    let (functions, receipt) =
        trust_cg_lower::translate_module_for_arch_with_tls_and_validation_with_license(
            &module,
            GuardCarrierArch::default(),
            TlsDialect::default(),
            &permit_unlicensed(),
        )
        .expect("module-local body must not be replaced by name-only intrinsic recognition");
    assert_eq!(receipt.exact_module_call_count(), 1);
    assert_eq!(
        caller_binding(&functions),
        DirectCallBinding::ExactModuleFunction { function: 0 }
    );
    receipt
        .replay_exact_module_calls(&functions)
        .expect("intrinsic-like module-local target replays by exact identity");
}

fn internal_invoke_module() -> Module {
    let mut module = Module::new("internal_invoke_binding");
    let sig = module
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut target = Function::new(FuncId::new(0), "may_throw", sig, BlockId::new(0));
    target.linkage = Linkage::Internal;
    let mut target_entry = Block::new(BlockId::new(0));
    target_entry
        .body
        .push(InstrNode::new(Inst::Return { values: vec![] }));
    target.blocks.push(target_entry);
    module.functions.push(target);

    let mut caller = Function::new(FuncId::new(1), "entry", sig, BlockId::new(0));
    let mut entry = Block::new(BlockId::new(0));
    entry.body.push(InstrNode::new(Inst::Invoke {
        callee: FuncId::new(0),
        args: vec![],
        normal_dest: BlockId::new(1),
        normal_args: vec![],
        unwind_dest: BlockId::new(2),
    }));
    let mut normal = Block::new(BlockId::new(1));
    normal
        .body
        .push(InstrNode::new(Inst::Return { values: vec![] }));
    let mut unwind = Block::new(BlockId::new(2));
    unwind.body.push(
        InstrNode::new(Inst::LandingPad {
            is_cleanup: true,
            catch_type_indices: vec![],
        })
        .with_results(vec![ValueId::new(10), ValueId::new(11)]),
    );
    unwind.body.push(InstrNode::new(Inst::Resume {
        exn: ValueId::new(10),
    }));
    caller.blocks = vec![entry, normal, unwind];
    module.functions.push(caller);
    module
}

#[test]
fn unsupported_exact_invoke_and_variadic_carriers_fail_closed() {
    let invoke_error =
        trust_cg_lower::translate_module_for_arch_with_tls_and_validation_with_license(
            &internal_invoke_module(),
            GuardCarrierArch::default(),
            TlsDialect::default(),
            &permit_unlicensed(),
        )
        .expect_err("Opcode::Invoke has no exact-module binding carrier");
    assert!(
        invoke_error
            .to_string()
            .contains("cannot carry exact-module binding through Opcode::Invoke"),
        "{invoke_error}"
    );

    // A non-preemptible variadic module function is a variadic DEFINITION,
    // which no lowering implements; the definition refusal fires before the
    // call edge's exact-binding carrier check (which stays in place behind it).
    let mut variadic = direct_call_module(Linkage::Internal);
    let target_ty = variadic.functions[0].ty;
    variadic.func_types[target_ty.as_usize()].is_vararg = true;
    let variadic_error =
        trust_cg_lower::translate_module_for_arch_with_tls_and_validation_with_license(
            &variadic,
            GuardCarrierArch::default(),
            TlsDialect::default(),
            &permit_unlicensed(),
        )
        .expect_err("a variadic module definition must not lower");
    assert!(
        variadic_error
            .to_string()
            .contains("[TCG-VARIADIC-DEFINITION]"),
        "{variadic_error}"
    );
}

#[test]
fn validated_div_and_swift_clones_fail_closed_for_every_direct_edge_carrier() {
    let edge_modules = [
        ("Call", direct_call_module(Linkage::Internal)),
        ("Invoke", internal_invoke_module()),
        ("CallVariadic", vararg_direct_call_module()),
    ];

    for (edge, module) in edge_modules {
        let mut div_clone = module.clone();
        add_div_annotation_clone_trigger(&mut div_clone);
        assert_validated_clone_refuses_local_identity(&format!("div/{edge}"), &div_clone);

        let mut swift_clone = module;
        add_swift_aggregate_clone_trigger(&mut swift_clone);
        assert_validated_clone_refuses_local_identity(&format!("swift/{edge}"), &swift_clone);
    }
}

#[test]
fn validated_adapter_clones_remain_available_without_local_identity() {
    for trigger in [
        add_div_annotation_clone_trigger as fn(&mut Module),
        add_swift_aggregate_clone_trigger,
    ] {
        let mut module = direct_call_module(Linkage::External);
        trigger(&mut module);
        let (functions, receipt) =
            trust_cg_lower::translate_module_for_arch_with_tls_and_validation_with_license(
                &module,
                GuardCarrierArch::AArch64,
                TlsDialect::default(),
                &permit_unlicensed(),
            )
            .expect("an adapter clone without local identity remains supported");
        assert_eq!(receipt.exact_module_call_count(), 0);
        assert_eq!(caller_binding(&functions), DirectCallBinding::Interposable);
        receipt
            .replay_exact_module_calls(&functions)
            .expect("an empty receipt remains replayable");
    }
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes because it was silently refused.
fn permit_unlicensed() -> trust_cg_lower::CodegenLicensePolicy {
    trust_cg_lower::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit)
}
