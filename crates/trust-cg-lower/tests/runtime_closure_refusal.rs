// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#[path = "common/runtime_closure.rs"]
mod fixture;

use trust_cg_lower::{
    AdapterError, GuardCarrierArch, prepare_module_for_lir,
    reject_unconsumed_v41_target_neutral_surface,
};
use trust_ir::interpret::{InterpretValue, Interpreter};
use trust_ir::{FuncId, Ty};

#[test]
fn runtime_closure_refuses_before_native_lowering_even_when_unused() {
    let module = fixture::runtime_closure_module(true);
    assert!(trust_ir_build::validate_module(&module).is_empty());
    let run = Interpreter::with_module(&module)
        .execute_func(FuncId::new(0), [InterpretValue::int(Ty::I64, 21).unwrap()])
        .unwrap();
    assert_eq!(run.returns[0].as_int().unwrap().as_signed(), 21);
    for result in [
        reject_unconsumed_v41_target_neutral_surface(&module),
        prepare_module_for_lir(&module, GuardCarrierArch::AArch64).map(drop),
        prepare_module_for_lir(&module, GuardCarrierArch::X86_64).map(drop),
        prepare_module_for_lir(&module, GuardCarrierArch::Riscv64).map(drop),
    ] {
        let error = result.unwrap_err();
        let AdapterError::UnmodeledTrustIrConstruct {
            construct, reason, ..
        } = error
        else {
            panic!("the unused constructor needs its typed refusal: {error:?}");
        };
        assert_eq!(construct, "Inst::MakeClosure");
        assert!(reason.contains("runtime closure ABI"), "{reason}");
    }
    let scalar = fixture::runtime_closure_module(false);
    assert!(trust_ir_build::validate_module(&scalar).is_empty());
    reject_unconsumed_v41_target_neutral_surface(&scalar).unwrap();
    prepare_module_for_lir(&scalar, GuardCarrierArch::AArch64).unwrap();
}
