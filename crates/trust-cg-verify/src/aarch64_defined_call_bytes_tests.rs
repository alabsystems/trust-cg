// Copyright 2026 Andrew Yates | Apache-2.0

use super::super::{Affine, integer};
use super::*;
use trust_ir_build::ModuleBuilder;

fn words(instructions: &[u32]) -> Vec<u8> {
    instructions.iter().flat_map(|w| w.to_le_bytes()).collect()
}

fn constant(value: u64) -> ScalarValue {
    integer(64, Affine::constant(value, u64::MAX))
}

#[test]
fn finite_walk_composes_actual_bl_and_returns_the_checked_result() {
    // Caller at 0, leaf at 20: STP; MOV FP,SP; BL +12; LDP; RET.
    let caller = words(&[0xa9bf7bfd, 0x910003fd, 0x94000003, 0xa8c17bfd, 0xd65f03c0]);
    for value in [0, 1, 42, 43, u64::MAX] {
        call_result(&caller, 0, 20, constant(value)).unwrap();
    }
    // A backwards call uses the signed actual immediate, relative to BL PC.
    let backwards = words(&[0xa9bf7bfd, 0x910003fd, 0x97fffffc, 0xa8c17bfd, 0xd65f03c0]);
    call_result(&backwards, 8, 0, constant(43)).unwrap();
}

#[test]
fn target_return_frame_and_extra_effect_mutations_refuse() {
    let good = [0xa9bf7bfd, 0x910003fd, 0x94000003, 0xa8c17bfd, 0xd65f03c0];
    for (index, mutation) in [
        (0, 0xa9bf7bfc), // Wrong saved register.
        (1, 0x910007fd), // FP no longer denotes current SP.
        (2, 0x94000004), // Wrong callee address.
        (2, 0x14000003), // B is not BL/normal continuation.
        (2, 0xd63f0000), // Indirect call has no attached endpoint.
        (2, 0xd503201f), // Missing call.
        (3, 0xa8c27bfd), // Wrong restore writeback.
        (4, 0xd65f0000), // RET X0 is not restored entry LR.
    ] {
        let mut altered = good;
        altered[index] = mutation;
        assert!(call_result(&words(&altered), 0, 20, constant(42)).is_err());
    }
    assert!(call_result(&words(&[0x94000002, 0xd65f03c0]), 0, 8, constant(42)).is_err());
    for suffix in [
        0xd2800560, // MOV X0,43 changes checked result.
        0xaa0103e0, // X1 is unknown after call.
        0xaa0003f3, // Unsaved X19 write.
        0x910043ff, // SP adjustment in body.
        0xf90003e0, // Store into saved frame.
        0xd65f03c0, // Early RET.
        0x94000003, // Second call.
    ] {
        let altered = words(&[
            0xa9bf7bfd, 0x910003fd, 0x94000004, suffix, 0xa8c17bfd, 0xd65f03c0,
        ]);
        assert!(
            call_result(&altered, 0, 24, constant(42)).is_err(),
            "{suffix:08x}"
        );
    }
}

fn source_pair() -> (Module, Vec<Function>) {
    let mut builder = ModuleBuilder::new("defined_call_byte_controls");
    let signature = builder.add_func_type(vec![], vec![Ty::U64]);
    let mut leaf = builder.function("leaf", signature);
    leaf.set_linkage(trust_ir::Linkage::Internal);
    let entry = leaf.create_block();
    leaf.switch_to_block(entry);
    let result = leaf.iconst(Ty::U64, 43);
    leaf.ret(vec![result]);
    let leaf = leaf.build();
    let mut caller = builder.function("caller", signature);
    let entry = caller.create_block();
    caller.switch_to_block(entry);
    let result = caller.call(leaf, vec![]);
    caller.ret(vec![result]);
    caller.build();
    let module = builder.build().unwrap();
    let (lir, _) =
        trust_cg_lower::translate_module_strict_for_arch_with_tls_and_validation_with_license(
            &module,
            trust_cg_lower::GuardCarrierArch::AArch64,
            trust_cg_lower::TlsDialect::MachOTlv,
            &crate::license_test_support::permit_unlicensed(),
        )
        .unwrap();
    let lir = lir.into_iter().map(|(f, _)| f).collect();
    (module, lir)
}

#[test]
fn source_and_lir_keep_actual_call_return_identities() {
    let (module, lir) = source_pair();
    source_call(&module, 1, &lir[1], &module.functions[0]).unwrap();
    let foreign = module.clone();
    assert!(source_call(&module, 1, &lir[1], &foreign.functions[0]).is_err());
    let mut changed = lir[1].clone();
    let block = changed.blocks.get_mut(&changed.entry_block).unwrap();
    block.instructions[1].args.clear();
    assert!(source_call(&module, 1, &changed, &module.functions[0]).is_err());
    let mut changed = lir[1].clone();
    let call = &mut changed
        .blocks
        .get_mut(&changed.entry_block)
        .unwrap()
        .instructions[0];
    if let Opcode::Call { binding, .. } = &mut call.opcode {
        *binding = DirectCallBinding::Interposable;
    }
    assert!(source_call(&module, 1, &changed, &module.functions[0]).is_err());
    let mut changed = module.clone();
    changed.functions[0].linkage = trust_ir::Linkage::External;
    assert!(source_call(&changed, 1, &lir[1], &changed.functions[0]).is_err());
    let mut changed = module.clone();
    changed.functions[1].attrs.readnone = true;
    assert!(source_call(&changed, 1, &lir[1], &changed.functions[0]).is_err());
    let mut changed = module.clone();
    changed.functions[1].blocks[0].body[1].inst = Inst::Return { values: vec![] };
    assert!(source_call(&changed, 1, &lir[1], &changed.functions[0]).is_err());
    let mut changed = module.clone();
    changed.functions[1].blocks[0].body[0].inst = Inst::Call {
        callee: changed.functions[1].id,
        args: vec![],
    };
    assert!(source_call(&changed, 1, &lir[1], &changed.functions[0]).is_err());
    let mut changed = module.clone();
    changed.functions[1].blocks[0]
        .body
        .insert(1, module.functions[1].blocks[0].body[0].clone());
    assert!(source_call(&changed, 1, &lir[1], &changed.functions[0]).is_err());
}

#[test]
fn real_leaf_byte_comparison_rejects_result_and_return_mutations() {
    let (module, lir) = source_pair();
    let check = |code: &[u8]| {
        crate::aarch64_affine_lowering::check_aarch64_trust_ir_affine_bytes(
            &module, 0, &lir[0], code,
        )
        .map(|_| ())
    };
    check(&words(&[0xd2800560, 0xd65f03c0])).unwrap(); // Actual source constant43.
    for altered in [
        [0xd2800540, 0xd65f03c0], // Substituted42.
        [0xd2800561, 0xd65f03c0], // Result written to X1.
        [0xd2800560, 0xd65f0000], // Return register differs.
        [0x94000000, 0xd65f03c0], // Recursive leaf is not affine.
    ] {
        assert!(check(&words(&altered)).is_err());
    }
}
