// Copyright 2026 Andrew Yates | Apache-2.0
//! Exact signed C call results can reach the existing tail pass without a
//! second extension. These are lowering controls, not proof-grade authority.
use trust_cg_lower::{GuardCarrierArch, TlsDialect, instructions::Opcode, types::Type};
use trust_ir::{
    Block, BlockId, CallingConv, FuncId, FuncTy, Function, Inst, InstrNode, Module, Ty, ValueId,
};

fn node(inst: Inst, results: &[u32]) -> InstrNode {
    let mut node = InstrNode::new(inst);
    node.results = results.iter().copied().map(ValueId::new).collect();
    node
}
fn module(ty: Ty, callee_conv: CallingConv, caller_conv: CallingConv) -> Module {
    let mut module = Module::new("signed_tail");
    module.target_info = Some(trust_ir::TargetInfo {
        triple: "aarch64-apple-darwin".into(),
        pointer_size: 8,
        endianness: trust_ir::Endianness::Little,
        abi: None,
        struct_passing: trust_ir::StructPassingPolicy::NativeC,
    });
    let sig = module
        .add_func_type(FuncTy {
            params: vec![ty.clone()],
            returns: vec![ty.clone()],
            abi: None,
            is_vararg: false,
        })
        .unwrap();
    let mut callee = Function::new(FuncId::new(0), "callee", sig, BlockId::new(0));
    callee.calling_conv = callee_conv;
    callee.blocks = vec![Block {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), ty.clone())],
        body: vec![node(
            Inst::Return {
                values: vec![ValueId::new(0)],
            },
            &[],
        )],
    }];
    module.try_add_function(callee).unwrap();
    let mut caller = Function::new(FuncId::new(1), "caller", sig, BlockId::new(0));
    caller.calling_conv = caller_conv;
    caller.blocks = vec![Block {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), ty)],
        body: vec![
            node(
                Inst::Call {
                    callee: FuncId::new(0),
                    args: vec![ValueId::new(0)],
                },
                &[1],
            ),
            node(
                Inst::Return {
                    values: vec![ValueId::new(1)],
                },
                &[],
            ),
        ],
    }];
    module.try_add_function(caller).unwrap();
    module
}
fn post_call_extensions(module: &Module, arch: GuardCarrierArch, dialect: TlsDialect) -> usize {
    let functions = trust_cg_lower::translate_module_for_arch_with_tls_with_license(
        module,
        arch,
        dialect,
        &trust_cg_lower::CodegenLicensePolicy::default()
            .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit),
    )
    .unwrap();
    let caller = &functions
        .iter()
        .find(|(f, _)| f.name == "caller")
        .unwrap()
        .0;
    let instructions: Vec<_> = caller
        .blocks
        .values()
        .flat_map(|b| &b.instructions)
        .collect();
    let call = instructions
        .iter()
        .position(|i| matches!(i.opcode, Opcode::Call { .. } | Opcode::CallIndirect))
        .unwrap();
    instructions[call + 1..]
        .iter()
        .filter(|i| {
            matches!(
                i.opcode,
                Opcode::Sextend {
                    to_ty: Type::I32,
                    ..
                }
            )
        })
        .count()
}
#[test]
fn adjacent_single_use_darwin_c_results_do_not_get_a_second_extension() {
    for ty in [Ty::I8, Ty::I16] {
        let module = module(ty.clone(), CallingConv::C, CallingConv::C);
        assert_eq!(
            post_call_extensions(&module, GuardCarrierArch::AArch64, TlsDialect::MachOTlv),
            0
        );
        let lowered = trust_cg_lower::translate_module_for_arch_with_tls_with_license(
            &module,
            GuardCarrierArch::AArch64,
            TlsDialect::MachOTlv,
            &trust_cg_lower::CodegenLicensePolicy::default()
                .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit),
        )
        .unwrap();
        let callee = &lowered.iter().find(|(f, _)| f.name == "callee").unwrap().0;
        assert!(
            callee
                .blocks
                .values()
                .flat_map(|b| &b.instructions)
                .any(|i| matches!(
                    i.opcode,
                    Opcode::Sextend {
                        to_ty: Type::I32,
                        ..
                    }
                )),
            "callee must retain its own C ABI extension"
        );
        let caller = &lowered.iter().find(|(f, _)| f.name == "caller").unwrap().0;
        assert_eq!(
            caller.signature.returns,
            vec![Type::I32],
            "the forwarded physical ABI word is W32"
        );
        assert_eq!(
            callee.signature.returns[0],
            if ty == Ty::I8 { Type::I8 } else { Type::I16 },
            "callee source representation is retained"
        );
        let instructions: Vec<_> = caller
            .blocks
            .values()
            .flat_map(|b| &b.instructions)
            .collect();
        let call = instructions
            .iter()
            .position(|i| matches!(i.opcode, Opcode::Call { .. }))
            .unwrap();
        assert!(
            instructions[..call].iter().any(|i| matches!(
                i.opcode,
                Opcode::Sextend {
                    to_ty: Type::I32,
                    ..
                }
            )),
            "argument extension is still required"
        );
    }
}
#[test]
fn weak_abi_external_and_non_darwin_results_keep_the_extension() {
    for ty in [Ty::I8, Ty::I16] {
        for (callee, caller) in [
            (CallingConv::Rust, CallingConv::C),
            (CallingConv::C, CallingConv::Rust),
        ] {
            assert_eq!(
                post_call_extensions(
                    &module(ty.clone(), callee, caller),
                    GuardCarrierArch::AArch64,
                    TlsDialect::MachOTlv
                ),
                1
            );
        }
        let mut external = module(ty.clone(), CallingConv::C, CallingConv::C);
        external.functions[0].blocks.clear();
        assert_eq!(
            post_call_extensions(&external, GuardCarrierArch::AArch64, TlsDialect::MachOTlv),
            1
        );
        let mut linux = module(ty.clone(), CallingConv::C, CallingConv::C);
        linux.target_info.as_mut().unwrap().triple = "aarch64-unknown-linux-gnu".into();
        assert_eq!(
            post_call_extensions(&linux, GuardCarrierArch::AArch64, TlsDialect::ElfExecutable),
            1
        );
        let mut absent = module(ty, CallingConv::C, CallingConv::C);
        absent.target_info = None;
        assert_eq!(
            post_call_extensions(&absent, GuardCarrierArch::AArch64, TlsDialect::MachOTlv),
            1
        );
    }
}
#[test]
fn intervening_work_and_multiple_uses_keep_the_extension() {
    for ty in [Ty::I8, Ty::I16] {
        let mut changed = module(ty.clone(), CallingConv::C, CallingConv::C);
        changed.functions[1].blocks[0].body.insert(
            1,
            node(
                Inst::Copy {
                    ty: ty.clone(),
                    operand: ValueId::new(0),
                },
                &[2],
            ),
        );
        assert_eq!(
            post_call_extensions(&changed, GuardCarrierArch::AArch64, TlsDialect::MachOTlv),
            1
        );
        let mut extra = module(ty.clone(), CallingConv::C, CallingConv::C);
        extra.functions[1].blocks[0].body.insert(
            1,
            node(
                Inst::Copy {
                    ty,
                    operand: ValueId::new(1),
                },
                &[2],
            ),
        );
        assert_eq!(
            post_call_extensions(&extra, GuardCarrierArch::AArch64, TlsDialect::MachOTlv),
            1,
            "an additional result use is not forwarding authority"
        );
    }
}
