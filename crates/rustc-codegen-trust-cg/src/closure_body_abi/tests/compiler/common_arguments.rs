// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Positive source-owned wide/receiver plans, not old architecture exclusions.

use super::*;

fn entry_matches<'tcx>(
    tcx: TyCtxt<'tcx>,
    instance: Instance<'tcx>,
    name: &str,
    params: &[TrustIrTy],
) {
    let lowered = mir_to_trust_ir(tcx, instance, name, &mut CrateRefineMemo::default())
        .unwrap_or_else(|error| panic!("{name}: actual closure body: {error}"));
    let function = lowered
        .module
        .functions
        .iter()
        .find(|f| f.name == name)
        .expect("original lowered body");
    let entry = function.blocks.first().expect("original entry block");
    assert_eq!(
        entry
            .params
            .iter()
            .map(|(_, ty)| ty.clone())
            .collect::<Vec<_>>(),
        params
    );
}

/// The byte offsets `k` of every `Load` of the pointer-width lane in `block`
/// whose address is `slot + k`, evaluated through the `Copy` / `PtrToInt` /
/// `IntToPtr` / constant `Add` / `Mul` chain `slot_byte_ptr` emits. A load whose
/// address is anything else is not a lane read of `slot` and is not listed.
fn slot_lane_load_offsets(block: &Block, slot: ValueId) -> Vec<u64> {
    #[derive(Clone, Copy)]
    enum Sym {
        Slot(i128),
        Konst(i128),
    }
    let mut sym: std::collections::HashMap<ValueId, Sym> =
        std::collections::HashMap::from([(slot, Sym::Slot(0))]);
    let mut offsets = Vec::new();
    for node in &block.body {
        let result = node.results.first().copied();
        let value = match &node.inst {
            Inst::Const {
                value: trust_ir::Constant::Int(c),
                ..
            } => Some(Sym::Konst(*c)),
            Inst::Copy { operand, .. }
            | Inst::Cast {
                op: CastOp::PtrToInt | CastOp::IntToPtr | CastOp::PtrToPtr,
                operand,
                ..
            } => sym.get(operand).copied(),
            Inst::BinOp { op, lhs, rhs, .. } => match (op, sym.get(lhs), sym.get(rhs)) {
                (TrustIrBinOp::Add, Some(Sym::Slot(a)), Some(Sym::Konst(b)))
                | (TrustIrBinOp::Add, Some(Sym::Konst(b)), Some(Sym::Slot(a))) => {
                    Some(Sym::Slot(a + b))
                }
                (TrustIrBinOp::Mul, Some(Sym::Konst(a)), Some(Sym::Konst(b))) => {
                    Some(Sym::Konst(a * b))
                }
                _ => None,
            },
            Inst::Load { ty, ptr, .. } => {
                if let (Some(Sym::Slot(k)), true) = (sym.get(ptr), *ty == pointer_lane_ty()) {
                    offsets.push(u64::try_from(*k).expect("a non-negative slot offset"));
                }
                None
            }
            _ => None,
        };
        if let (Some(result), Some(value)) = (result, value) {
            sym.insert(result, value);
        }
    }
    offsets
}

pub(super) fn check_actual_wide_and_value_environments(tcx: TyCtxt<'_>) {
    let (mut ctx, instance) = closure(tcx, "wide_input");
    let abi = RustcFnAbiSource::Instance(instance).query(tcx).unwrap();
    let input = ctx.normalize_ty(abi.args[1].layout.ty);
    assert!(matches!(input.kind(), ty::Ref(_, inner, _) if matches!(inner.kind(), ty::Slice(..))));
    let pair = ctx
        .scalar_pair_param_plan(input, 1, RustcFnAbiSource::Instance(instance))
        .unwrap()
        .expect("actual slice Pair");
    assert_eq!(pair.declared(), [TrustIrTy::Ptr, pointer_lane_ty()]);
    assert_eq!(pair.offsets(), [0, 8]);
    let signature = ctx.func_ty_for_instance(instance).unwrap();
    let params = ctx.module.func_types[signature.index() as usize]
        .params
        .clone();
    assert_eq!(&params[1..], &pair.declared());
    let mut block = Block::new(BlockId::new(0));
    let env = ValueId::new(800);
    let slot = ValueId::new(801);
    let values =
        closure_body_call_args_from_values(&mut ctx, &mut block, instance, Some(env), vec![slot])
            .unwrap();
    assert_eq!(values.len(), params.len());
    assert_eq!(values[0], env);
    // The two `Pair` lanes are read out of the slot's `fat_ptr_slot_ty()`
    // words 0 and 1: since WS7.3-pre a slot read is the word's byte address
    // (`slot_byte_ptr`) and a typed `Load` of the pointer-width lane, not an
    // `ExtractField` over the slot POINTER, which trust-ir refuses
    // (`FieldAccessInvalid`). Evaluate each `Load`'s address as `slot + k`.
    assert_eq!(
        slot_lane_load_offsets(&block, slot),
        [0, session_pointer_bytes()]
    );
    assert!(block.body.iter().any(|n| matches!(
        n.inst,
        Inst::Cast {
            op: CastOp::IntToPtr,
            ..
        }
    )));
    entry_matches(tcx, instance, "wide_input", &params);

    // Both receiver0 shapes are genuine parsed FnOnce bodies. The common
    // builder must use their original FnAbi, not prepend an assumed Ptr.
    for name in ["value_environment", "pair_environment"] {
        let (mut ctx, instance) = closure(tcx, name);
        assert!(closure_body_env_by_value(tcx, instance));
        let abi = RustcFnAbiSource::Instance(instance).query(tcx).unwrap();
        let environment = ctx.normalize_ty(abi.args[0].layout.ty);
        assert_eq!(
            environment,
            instance.ty(tcx, ty::TypingEnv::fully_monomorphized())
        );
        let receiver_pair = ctx
            .scalar_pair_param_plan(environment, 0, RustcFnAbiSource::Instance(instance))
            .unwrap();
        if name == "pair_environment" {
            assert!(matches!(
                abi.args[0].mode,
                rustc_target::callconv::PassMode::Pair(..)
            ));
            assert!(
                receiver_pair.is_some(),
                "receiver0 uses its actual checked Pair"
            );
        } else {
            assert!(matches!(
                abi.args[0].mode,
                rustc_target::callconv::PassMode::Direct(..)
            ));
            assert!(
                receiver_pair.is_none(),
                "the scalar receiver is not a fabricated Pair"
            );
        }
        let signature = ctx.func_ty_for_instance(instance).unwrap();
        let params = ctx.module.func_types[signature.index() as usize]
            .params
            .clone();
        let mut block = Block::new(BlockId::new(0));
        let values = closure_body_call_args_from_values(
            &mut ctx,
            &mut block,
            instance,
            Some(env),
            vec![slot],
        )
        .unwrap();
        assert_eq!(values.len(), params.len());
        if let Some(pair) = receiver_pair {
            assert_eq!(&params[..2], &pair.declared());
            let expected: Vec<_> = pair
                .plan
                .lanes
                .iter()
                .map(|(ty, _)| ty.clone())
                .chain([TrustIrTy::I32, TrustIrTy::I32])
                .collect();
            assert_eq!(loads(&block), expected);
            let expected_origins: Vec<_> = pair
                .offsets()
                .into_iter()
                .map(|offset| (env, offset))
                .chain([0, 4].into_iter().map(|offset| (slot, offset)))
                .collect();
            assert_eq!(load_origins(&block), expected_origins);
            assert_ne!(
                values[0], env,
                "receiver bytes are loaded, not passed as one pointer"
            );
        } else {
            let layout = fat_ptr_or_memory_aggregate_layout(tcx, environment)
                .unwrap()
                .expect("actual scalar receiver slot");
            assert_eq!(params[0], layout.slot_ty);
            assert_eq!(
                values[0], env,
                "a by-value slot is classified by its real declared type"
            );
        }
        entry_matches(tcx, instance, name, &params);
    }
}
