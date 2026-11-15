use super::*;
use crate::eh_call_custody::tests::{bind_exact, bind_legacy, snapshot};

fn bind_loop_call(func: &mut MachFunction, legacy: bool) {
    let call = *func
        .block(PL_HEADER)
        .insts
        .iter()
        .find(|&&id| func.inst(id).is_call())
        .unwrap();
    if legacy {
        bind_legacy(func, PL_HEADER);
    } else {
        bind_exact(func, call, PL_HEADER);
    }
}

#[test]
fn general_full_unroll_does_not_clone_a_protected_call() {
    for legacy in [false, true] {
        let mut func = make_call_bearing_loop(0, 1, 2);
        bind_loop_call(&mut func, legacy);
        let before = snapshot(&func);
        assert!(!LoopUnroll::default().run(&mut func));
        assert_eq!(snapshot(&func), before);
    }
    let mut ordinary = make_call_bearing_loop(0, 1, 2);
    assert!(LoopUnroll::default().run(&mut ordinary));
    let calls = ordinary
        .block_order
        .iter()
        .flat_map(|&b| &ordinary.block(b).insts)
        .filter(|&&id| ordinary.inst(id).is_call())
        .count();
    assert_eq!(calls, 2);
}

#[test]
fn late_call_unroll_keeps_exact_and_legacy_invoke_identities_uncloned() {
    for legacy in [false, true] {
        let mut func = make_call_bearing_loop(0, 1, 4);
        bind_loop_call(&mut func, legacy);
        let before = snapshot(&func);
        let mut pass = CallUnroll::new();
        assert!(!pass.run(&mut func));
        assert_eq!(pass.fired(), 0);
        assert_eq!(snapshot(&func), before);
    }
    let mut ordinary = make_call_bearing_loop(0, 1, 4);
    let mut pass = CallUnroll::new();
    assert!(pass.run(&mut ordinary));
    assert_eq!(pass.fired(), 1);
    let calls = ordinary
        .block_order
        .iter()
        .flat_map(|&b| &ordinary.block(b).insts)
        .filter(|&&id| ordinary.inst(id).is_call())
        .count();
    assert_eq!(calls, 4);
}
