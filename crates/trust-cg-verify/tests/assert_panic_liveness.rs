// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Panic payloads remain SSA uses; runtime failure-only evaluation does not
//! make their definitions disappear from dominance and liveness checking.

use trust_cg_verify::ssa_loop_complete::{
    SsaViolation, check_function, non_terminator_value_uses, value_is_dead,
};
use trust_ir::{
    AssertKind, AssertOverflowOp, Block, BlockId, FuncId, FuncTyId, Function, Inst, InstrNode, Ty,
    ValueId,
};

fn v(index: u32) -> ValueId {
    ValueId::new(index)
}

#[test]
fn every_assert_kind_uses_its_condition_and_its_actual_panic_payload() {
    let mut kinds = vec![AssertKind::Unspecified];
    kinds.extend(AssertOverflowOp::ALL.map(AssertKind::Overflow));
    kinds.extend([
        AssertKind::DivByZero,
        AssertKind::RemByZero,
        AssertKind::NullPtr,
        AssertKind::BoundsCheck {
            index: v(11),
            len: v(12),
        },
        AssertKind::MisalignedPtr {
            required: v(11),
            found: v(12),
        },
    ]);
    for kind in kinds {
        let inst = Inst::Assert {
            cond: v(10),
            kind,
            site: None,
        };
        let mut shared = Vec::new();
        inst.visit_value_operands(|value| shared.push(value));
        assert_eq!(non_terminator_value_uses(&inst), shared);
        assert_eq!(shared.first(), Some(&v(10)));
        assert_eq!(shared.len(), if kind.operands().is_some() { 3 } else { 1 });
    }
}

#[test]
fn panic_operand_multiplicity_and_existing_edge_scope_remain_exact() {
    let inst = Inst::Assert {
        cond: v(1),
        kind: AssertKind::BoundsCheck {
            index: v(2),
            len: v(2),
        },
        site: None,
    };
    assert_eq!(non_terminator_value_uses(&inst), [v(1), v(2), v(2)]);
    let edge = Inst::CondBr {
        cond: v(1),
        then_target: BlockId::new(1),
        then_args: vec![v(2)],
        else_target: BlockId::new(2),
        else_args: vec![v(3)],
    };
    assert_eq!(non_terminator_value_uses(&edge), [v(1)]);
    assert!(
        non_terminator_value_uses(&Inst::Br {
            target: BlockId::new(1),
            args: vec![v(2)],
        })
        .is_empty()
    );
}

#[test]
fn real_ssa_and_dead_value_checks_see_failure_only_panic_operands() {
    for kind in [
        AssertKind::BoundsCheck {
            index: v(1),
            len: v(2),
        },
        AssertKind::MisalignedPtr {
            required: v(1),
            found: v(2),
        },
    ] {
        let mut function =
            Function::new(FuncId::new(0), "checked", FuncTyId::new(0), BlockId::new(0));
        let mut block = Block::new(BlockId::new(0));
        block.params = vec![
            (v(0), Ty::Bool),
            (v(1), Ty::Usize),
            (v(2), Ty::Usize),
            (v(3), Ty::Usize),
        ];
        block.body = vec![
            InstrNode::new(Inst::Assert {
                cond: v(0),
                kind,
                site: None,
            }),
            InstrNode::new(Inst::Return { values: vec![] }),
        ];
        function.blocks.push(block);
        check_function(&function).unwrap();
        assert!(!value_is_dead(&function, v(1)));
        assert!(!value_is_dead(&function, v(2)));
        assert!(value_is_dead(&function, v(3)));
        let Inst::Assert {
            cond: _,
            kind,
            site: _,
        } = &mut function.blocks[0].body[0].inst
        else {
            unreachable!()
        };
        *kind.operands_mut().unwrap()[0] = v(99);
        let violations = check_function(&function).unwrap_err();
        assert!(violations.iter().any(|violation| matches!(violation,
            SsaViolation::UndefinedValue { value, .. } if *value == v(99))));
    }
}
