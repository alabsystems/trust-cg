use super::*;
use crate::eh_call_custody::tests::{bind_exact, bind_legacy, snapshot};

fn call() -> MachInst {
    MachInst::new(AArch64Opcode::Bl, vec![MachOperand::Symbol("leaf".into())])
}

fn leaf() -> MachFunction {
    make_callee("leaf", vec![MachInst::new(AArch64Opcode::Nop, vec![])], 0)
}

#[test]
fn inlining_preserves_selected_invoke_but_inlines_same_callee_companion() {
    let mut caller = make_func_with_insts(
        "caller",
        vec![call(), call(), MachInst::new(AArch64Opcode::Ret, vec![])],
    );
    let entry = caller.entry;
    let calls = caller.block(entry).insts[..2].to_vec();
    bind_exact(&mut caller, calls[0], entry);
    let binding = caller.eh_metadata.call_site_bindings.clone();
    let mut pass = FunctionInlining::new().with_callee("leaf".into(), leaf());
    assert!(pass.run(&mut caller));
    assert!(caller.block(entry).insts.contains(&calls[0]));
    assert!(!caller.block(entry).insts.contains(&calls[1]));
    assert_eq!(caller.inst(calls[0]).opcode, AArch64Opcode::Bl);
    assert_eq!(caller.inst(calls[0]).operands, call().operands);
    assert_eq!(caller.eh_metadata.call_site_bindings, binding);
}

#[test]
fn legacy_inlining_handler_declines_without_partial_machine_mutation() {
    let mut caller = make_func_with_insts("caller", vec![call(), call()]);
    let entry = caller.entry;
    bind_legacy(&mut caller, entry);
    let before = snapshot(&caller);
    let mut pass = FunctionInlining::new().with_callee("leaf".into(), leaf());
    assert!(!pass.run(&mut caller));
    assert_eq!(snapshot(&caller), before);
}

#[test]
fn inlining_does_not_import_untransported_callee_eh_metadata() {
    let mut callee = leaf();
    // A single-block body still may own an EH personality: body copying alone
    // cannot transport the associated exception contract.
    callee.eh_metadata.personality = Some("personality".into());
    let mut caller = make_func_with_insts("caller", vec![call()]);
    let before = snapshot(&caller);
    let mut pass = FunctionInlining::new().with_callee("leaf".into(), callee);
    assert!(!pass.run(&mut caller));
    assert_eq!(snapshot(&caller), before);
}
