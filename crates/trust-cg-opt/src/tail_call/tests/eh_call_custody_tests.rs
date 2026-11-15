use super::*;
use crate::eh_call_custody::tests::{bind_exact, bind_legacy, snapshot};

fn tail() -> MachFunction {
    let mut func = make_func("caller", vec![Type::I64], vec![Type::I64]);
    let entry = func.entry;
    append_insts(
        &mut func,
        entry,
        vec![
            MachInst::new(AArch64Opcode::Bl, vec![sym("callee")]),
            MachInst::new(AArch64Opcode::Ret, vec![]),
        ],
    );
    func
}

#[test]
fn protected_tail_call_retains_bl_and_exception_identity_before_abi_rewrites() {
    for legacy in [false, true] {
        let mut func = tail();
        let entry = func.entry;
        let call = call_id(&func);
        if legacy {
            bind_legacy(&mut func, entry);
        } else {
            bind_exact(&mut func, call, entry);
        }
        let before = snapshot(&func);
        assert!(!TailCallOptimization.run(&mut func));
        assert_eq!(snapshot(&func), before);
    }
    let mut ordinary = tail();
    let call = call_id(&ordinary);
    assert!(TailCallOptimization.run(&mut ordinary));
    assert_eq!(ordinary.inst(call).opcode, AArch64Opcode::TailCall);
    assert_eq!(ordinary.inst(call).operands, vec![sym("callee")]);
    assert_eq!(ordinary.block(ordinary.entry).insts, vec![call]);
}
