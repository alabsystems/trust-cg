use super::*;
use crate::eh_call_custody::tests::{bind_exact, bind_legacy, snapshot};

#[test]
fn pure_call_proof_does_not_allow_hoisting_a_selected_invoke() {
    for legacy in [false, true] {
        let (mut func, cluster, [_, _, body, _]) = make_pure_call_loop(true, true);
        if legacy {
            bind_legacy(&mut func, body);
        } else {
            bind_exact(&mut func, cluster[1], body);
        }
        let before = snapshot(&func);
        assert!(!pc_run(&mut func));
        assert_eq!(snapshot(&func), before);
    }
    let (mut ordinary, _, _) = make_pure_call_loop(true, true);
    assert!(pc_run(&mut ordinary));
}
