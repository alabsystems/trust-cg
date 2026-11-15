use super::*;
use crate::eh_call_custody::tests::{bind_exact, bind_legacy, snapshot};

fn pair() -> MachFunction {
    make_func(vec![
        arg_setup(0),
        bl("sin"),
        result_read(1),
        arg_setup(0),
        bl("cos"),
        result_read(2),
    ])
}

#[test]
fn protected_sincos_anchor_or_deleted_endpoint_keeps_exact_call_and_handler() {
    for index in [1, 4] {
        let mut func = pair();
        let block = func.entry;
        let call = func.block(block).insts[index];
        bind_exact(&mut func, call, block);
        let before = snapshot(&func);
        assert!(!run_pass(&mut func));
        assert_eq!(snapshot(&func), before);
    }
}

#[test]
fn legacy_sincos_handler_is_conservative_but_unrelated_exact_call_does_not_disable_merge() {
    let mut func = pair();
    let block = func.entry;
    bind_legacy(&mut func, block);
    let before = snapshot(&func);
    assert!(!run_pass(&mut func));
    assert_eq!(snapshot(&func), before);

    let mut func = pair();
    let block = func.entry;
    let unrelated = func.push_inst(bl("other"));
    func.append_inst(block, unrelated);
    bind_exact(&mut func, unrelated, block);
    let binding = func.eh_metadata.call_site_bindings.clone();
    assert!(run_pass(&mut func));
    assert_eq!(block_syms(&func, block), [SINCOS_STRET_SYMBOL, "other"]);
    assert_eq!(func.eh_metadata.call_site_bindings, binding);
    assert!(func.block(block).insts.contains(&unrelated));
}
