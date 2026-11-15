use super::*;
use trust_cg_lower::function::EhCallSite;

fn run_call_tier(func: &mut X86ISelFunction) -> bool {
    let preds = mach_view::predecessor_map(func);
    let idom = compute_idom(func, &preds);
    let loops = find_natural_loops(func, &preds, &idom);
    assert_eq!(loops.len(), 1);
    let def_counts = build_def_counts(func);
    let protected = func
        .eh_info
        .call_sites
        .iter()
        .map(|site| site.call_block)
        .collect();
    hoist_pure_call_clusters(func, &loops[0], &def_counts, &idom, &protected)
}

#[test]
fn legacy_x86_invoke_block_keeps_a_pure_hoistable_call_and_its_handler() {
    let mut func = make_pure_call_loop(false);
    func.eh_info.call_sites.push(EhCallSite {
        call_block: Block(1),
        landing_pad_block: Block(2),
    });
    let before = format!("{func:?}");
    assert!(!run_call_tier(&mut func));
    assert_eq!(format!("{func:?}"), before);
    assert_eq!(call_count(&func, Block(0)), 0);
    assert_eq!(call_count(&func, Block(1)), 1);
}

#[test]
fn unrelated_x86_handler_block_does_not_disable_ordinary_pure_call_hoisting() {
    let mut func = make_pure_call_loop(false);
    let other = Block(3);
    func.ensure_block(other);
    func.push_inst(
        other,
        X86ISelInst::new(
            X86Opcode::Call,
            vec![X86ISelOperand::Symbol("other".into())],
        ),
    );
    func.push_inst(other, X86ISelInst::new(X86Opcode::Ret, vec![]));
    func.eh_info.call_sites.push(EhCallSite {
        call_block: other,
        landing_pad_block: Block(2),
    });
    let other_before = format!("{:?}", func.blocks[&other]);
    let eh_before = format!("{:?}", func.eh_info);
    assert!(run_call_tier(&mut func));
    assert_eq!(call_count(&func, Block(0)), 1);
    assert_eq!(call_count(&func, Block(1)), 0);
    assert_eq!(format!("{:?}", func.blocks[&other]), other_before);
    assert_eq!(format!("{:?}", func.eh_info), eh_before);
}
