#[path = "../src/cleanup_params.rs"]
mod cleanup_params;

use trust_cg_verify::ssa_loop_complete::{SsaViolation, check_function};
use trust_ir::{
    Block, BlockId, Constant, FuncId, FuncTyId, Function, Inst, InstrNode, Ty, ValueId,
};

fn fixture() -> Function {
    let mut f = Function::new(FuncId::new(0), "cleanup", FuncTyId::new(0), BlockId::new(0));
    let mut entry = Block::new(BlockId::new(0));
    entry.body.push(
        InstrNode::new(Inst::Const {
            ty: Ty::I64,
            value: Constant::Int(7),
        })
        .with_result(ValueId::new(1)),
    );
    entry.body.push(InstrNode::new(Inst::Invoke {
        callee: FuncId::new(1),
        args: vec![],
        normal_dest: BlockId::new(1),
        normal_args: vec![],
        unwind_dest: BlockId::new(2),
    }));
    let mut normal = Block::new(BlockId::new(1));
    normal
        .body
        .push(InstrNode::new(Inst::Return { values: vec![] }));
    let mut pad = Block::new(BlockId::new(2));
    pad.params.push((ValueId::new(10), Ty::I64));
    pad.body.push(
        InstrNode::new(Inst::LandingPad {
            is_cleanup: true,
            catch_type_indices: vec![],
        })
        .with_results(vec![ValueId::new(20), ValueId::new(21)]),
    );
    pad.body.push(InstrNode::new(Inst::Resume {
        exn: ValueId::new(20),
    }));
    f.blocks = vec![entry, normal, pad];
    f
}

fn has_arity_error(f: &Function) -> bool {
    check_function(f)
        .unwrap_err()
        .iter()
        .any(|v| matches!(v, SsaViolation::EdgeArgArityMismatch { .. }))
}

#[test]
fn removes_only_unused_unwinder_parameters_and_keeps_cleanup() {
    let mut f = fixture();
    assert!(has_arity_error(&f));
    let original = format!("{:?}", f.blocks[2].body);
    cleanup_params::remove_unused_unwind_params(&mut f);
    assert!(f.blocks[2].params.is_empty());
    assert_eq!(format!("{:?}", f.blocks[2].body), original);
    assert!(check_function(&f).is_ok());
}

#[test]
fn live_cleanup_parameter_still_fails_validation() {
    let mut f = fixture();
    f.blocks[2].body[1] = InstrNode::new(Inst::Resume {
        exn: ValueId::new(10),
    });
    cleanup_params::remove_unused_unwind_params(&mut f);
    assert_eq!(f.blocks[2].params.len(), 1);
    assert!(has_arity_error(&f));
}

#[test]
fn an_edge_argument_is_a_live_use() {
    let mut f = fixture();
    f.blocks[2].body[1] = InstrNode::new(Inst::Br {
        target: BlockId::new(3),
        args: vec![ValueId::new(10)],
    });
    let mut tail = Block::new(BlockId::new(3));
    tail.params.push((ValueId::new(30), Ty::I64));
    tail.body.push(InstrNode::new(Inst::Resume {
        exn: ValueId::new(30),
    }));
    f.blocks.push(tail);
    cleanup_params::remove_unused_unwind_params(&mut f);
    assert_eq!(f.blocks[2].params.len(), 1);
    assert!(has_arity_error(&f));
}

#[test]
fn preserves_parameters_with_normal_incoming_edges() {
    let mut f = fixture();
    if let Inst::Invoke {
        normal_dest,
        normal_args,
        ..
    } = &mut f.blocks[0].body[1].inst
    {
        *normal_dest = BlockId::new(2);
        normal_args.push(ValueId::new(1));
    }
    cleanup_params::remove_unused_unwind_params(&mut f);
    assert_eq!(f.blocks[2].params.len(), 1);
    assert!(has_arity_error(&f));
}

#[test]
fn preserves_the_function_entry_signature() {
    let mut f = fixture();
    f.entry = BlockId::new(2);
    cleanup_params::remove_unused_unwind_params(&mut f);
    assert_eq!(f.blocks[2].params.len(), 1);
}
