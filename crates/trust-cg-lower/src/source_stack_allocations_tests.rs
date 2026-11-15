// Copyright 2026 Andrew Yates | Apache-2.0
use super::*;
use crate::{CodegenLicensePolicy, ProofContext, UnlicensedBodyPolicy};
use trust_ir_build::ModuleBuilder;

fn fixture() -> (Module, Function, ProofContext) {
    let mut m = ModuleBuilder::new("alloca_identity");
    let sig = m.add_func_type(vec![], vec![Ty::I64]);
    let mut f = m.function("two_allocations", sig);
    let b = f.create_block();
    f.switch_to_block(b);
    let a = f.alloca(Ty::I64);
    let c = f.alloca(Ty::I64);
    let n = f.iconst(Ty::I64, 42);
    f.store(Ty::I64, a, n);
    f.store(Ty::I64, c, n);
    let x = f.load(Ty::I64, a);
    let y = f.load(Ty::I64, c);
    let z = f.add(Ty::I64, x, y);
    f.ret(vec![z]);
    f.build();
    let m = m.build().unwrap();
    let (lir, ctx) = crate::adapter::translate_function_with_license(
        &m.functions[0],
        &m,
        &CodegenLicensePolicy::default().with_unlicensed(UnlicensedBodyPolicy::Permit),
    )
    .unwrap();
    (m, lir, ctx)
}

#[test]
fn actual_same_sized_allocas_retain_distinct_source_and_slot_identities() {
    let (m, lir, ctx) = fixture();
    let input = &ctx.source_stack_allocations;
    input.validate_source(&m).unwrap();
    input.validate_lir(&lir).unwrap();
    let [a, b] = input.records() else {
        panic!("complete census")
    };
    assert_ne!(a.source_result(), b.source_result());
    assert_ne!(a.stack_slot(), b.stack_slot());
    assert_eq!(a.geometry(), b.geometry());
    assert_eq!(a.source_type(), &Ty::I64);
    assert_eq!(a.element_bytes(), 8);
    assert_eq!(a.extent(), AllocationExtent::One);
}

#[test]
fn swapping_same_sized_allocation_homes_fails_the_actual_source_origin() {
    let (m, lir, ctx) = fixture();
    let mut changed = ctx.source_stack_allocations;
    let a = changed.records[0].clone();
    let b = changed.records[1].clone();
    changed.records[0].slot = b.slot;
    changed.records[0].result = b.result;
    changed.records[1].slot = a.slot;
    changed.records[1].result = a.result;
    changed.validate_source(&m).unwrap();
    assert!(
        changed
            .validate_lir(&lir)
            .unwrap_err()
            .contains("identity differs")
    );
}

#[test]
fn changed_source_type_count_or_slot_layout_cannot_reuse_the_mapping() {
    let (m, lir, ctx) = fixture();
    let input = ctx.source_stack_allocations;
    let mut source = m.clone();
    let Inst::Alloca { ty, .. } = &mut source.functions[0].blocks[0].body[0].inst else {
        panic!()
    };
    *ty = Ty::U64; // Same eight-byte layout, distinct source type.
    assert!(input.validate_source(&source).is_err());
    let mut changed = lir.clone();
    changed.stack_slots[input.records[0].slot as usize].align *= 2;
    assert!(input.validate_lir(&changed).is_err());
    let mut count = input.clone();
    count.records[0].extent = AllocationExtent::Constant(1);
    assert!(count.validate_source(&m).is_err());
    let mut missing = input;
    missing.records.pop();
    assert!(missing.validate_source(&m).is_err());
}

#[test]
fn source_identity_type_extent_and_layout_enter_retained_lir_identity() {
    let (_, lir, ctx) = fixture();
    let digest =
        |context| crate::retained_lir_proof_context_digest(&[(lir.clone(), context)]).unwrap();
    let original = digest(ctx.clone());
    let mut variants = Vec::new();
    let mut x = ctx.clone();
    x.source_stack_allocations.records[0].source = ValueId::new(999);
    variants.push(x);
    let mut x = ctx.clone();
    x.source_stack_allocations.records[0].ty = Ty::U64;
    variants.push(x);
    let mut x = ctx.clone();
    x.source_stack_allocations.records[0].slot = 1;
    variants.push(x);
    let mut x = ctx.clone();
    x.source_stack_allocations.records[0].geometry.align = 16;
    variants.push(x);
    let mut x = ctx.clone();
    x.source_stack_allocations.records[0].extent = AllocationExtent::BoundedUses;
    variants.push(x);
    for changed in variants {
        assert_ne!(digest(changed), original);
    }
}

#[test]
fn folded_constant_counts_use_the_existing_adapter_folder_and_keep_exact_alignment() {
    let mut m = ModuleBuilder::new("folded_count");
    let sig = m.add_func_type(vec![], vec![Ty::I64]);
    let mut f = m.function("folded", sig);
    let b = f.create_block();
    f.switch_to_block(b);
    let x = f.iconst(Ty::U64, 2);
    let y = f.iconst(Ty::U64, 3);
    let count = f.add(Ty::U64, x, y);
    let ptr = f.alloca_aligned(Ty::I64, 32);
    let value = f.iconst(Ty::I64, 42);
    f.store(Ty::I64, ptr, value);
    let value = f.load(Ty::I64, ptr);
    f.ret(vec![value]);
    f.build();
    let mut m = m.build().unwrap();
    let node = m.functions[0].blocks[0]
        .body
        .iter_mut()
        .find(|n| matches!(n.inst, Inst::Alloca { .. }))
        .unwrap();
    let Inst::Alloca {
        count: source_count,
        ..
    } = &mut node.inst
    else {
        unreachable!()
    };
    *source_count = Some(count);
    let (lir, context) = crate::adapter::translate_function_with_license(
        &m.functions[0],
        &m,
        &CodegenLicensePolicy::default().with_unlicensed(UnlicensedBodyPolicy::Permit),
    )
    .unwrap();
    let input = context.source_stack_allocations;
    input.validate_source(&m).unwrap();
    input.validate_lir(&lir).unwrap();
    assert_eq!(input.records()[0].extent(), AllocationExtent::Constant(5));
    assert_eq!(input.records()[0].source_count(), Some(count));
    assert_eq!(input.records()[0].geometry(), StackSlotInfo::new(40, 32));
    // Keep the count SSA identity and site but change a defining literal.
    let Inst::Const { value, .. } = &mut m.functions[0].blocks[0].body[0].inst else {
        panic!()
    };
    *value = trust_ir::Constant::Int(4);
    assert!(input.validate_source(&m).is_err());
}

#[test]
fn runtime_and_bounded_use_extents_are_not_constant_count_facts() {
    for used in [false, true] {
        let mut m = ModuleBuilder::new("dynamic_count");
        let sig = m.add_func_type(vec![Ty::U64], vec![Ty::I64]);
        let mut f = m.function("dynamic", sig);
        let b = f.create_block();
        let count = f.add_block_param(b, Ty::U64);
        f.switch_to_block(b);
        let ptr = f.alloca(Ty::I64);
        let value = f.iconst(Ty::I64, 42);
        let result = if used {
            f.store(Ty::I64, ptr, value);
            f.load(Ty::I64, ptr)
        } else {
            value
        };
        f.ret(vec![result]);
        f.build();
        let mut m = m.build().unwrap();
        let Inst::Alloca {
            count: source_count,
            ..
        } = &mut m.functions[0].blocks[0].body[0].inst
        else {
            panic!()
        };
        *source_count = Some(count);
        let (lir, context) = crate::adapter::translate_function_with_license(
            &m.functions[0],
            &m,
            &CodegenLicensePolicy::default().with_unlicensed(UnlicensedBodyPolicy::Permit),
        )
        .unwrap();
        let input = context.source_stack_allocations;
        input.validate_source(&m).unwrap();
        input.validate_lir(&lir).unwrap();
        let allocation = &input.records()[0];
        assert_eq!(
            allocation.extent(),
            if used {
                AllocationExtent::BoundedUses
            } else {
                AllocationExtent::Runtime
            }
        );
        assert_eq!(allocation.geometry().is_runtime_sized(), !used);
    }
}
