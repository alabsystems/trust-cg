use super::*;
use crate::eh_call_custody::tests::{bind_exact, bind_legacy, snapshot};

#[test]
fn licensed_libm_call_cannot_be_cloned_or_deleted_when_it_owns_an_invoke() {
    for legacy in [false, true] {
        let mut func = make_nest(true);
        let block = BlockId(2);
        let call = *func
            .block(block)
            .insts
            .iter()
            .find(|&&id| func.inst(id).opcode == AArch64Opcode::Bl)
            .unwrap();
        if legacy {
            bind_legacy(&mut func, block);
        } else {
            bind_exact(&mut func, call, block);
        }
        let before = snapshot(&func);
        assert!(!run_pass(&mut func));
        assert_eq!(snapshot(&func), before);
    }
    let mut ordinary = make_nest(true);
    assert!(run_pass(&mut ordinary));
}
