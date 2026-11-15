use super::*;
use crate::eh_call_custody::tests::{bind_exact, bind_legacy, snapshot};

fn call_loop() -> (MachFunction, InstId) {
    let mut func = make_unswitchable_loop();
    let call = func.push_inst(MachInst::new(
        AArch64Opcode::Bl,
        vec![MachOperand::Symbol("leaf".into())],
    ));
    func.block_mut(BlockId(3)).insts.insert(0, call);
    (func, call)
}

fn direct_unswitch(func: &mut MachFunction) -> bool {
    let dom = DomTree::compute(func);
    let analysis = LoopAnalysis::compute(func, &dom);
    run_unswitch(func, &analysis, &dom)
}

#[test]
fn unswitch_does_not_clone_a_selected_call_into_an_unbound_loop_version() {
    for legacy in [false, true] {
        let (mut func, call) = call_loop();
        if legacy {
            bind_legacy(&mut func, BlockId(3));
        } else {
            bind_exact(&mut func, call, BlockId(3));
        }
        let before = snapshot(&func);
        assert!(!direct_unswitch(&mut func));
        assert_eq!(snapshot(&func), before);
    }
    let (mut ordinary, _) = call_loop();
    assert!(direct_unswitch(&mut ordinary));
    let calls = ordinary
        .block_order
        .iter()
        .flat_map(|&b| &ordinary.block(b).insts)
        .filter(|&&id| ordinary.inst(id).is_call())
        .count();
    assert_eq!(calls, 2);
}
