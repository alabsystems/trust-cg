// crates/trust-cg-eqsat/src/remap/tests.rs - the mutable operand walk agrees with visit_value_operands
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! For one instance of every `Inst` variant (with every optional operand
//! present where a variant has one), the mutable walk visits exactly the
//! positions `Inst::visit_value_operands` reports, in the same order, and
//! replacing through it is seen by the read-only walk.

use trust_ir::inst::{AllocOrigin, BindingFrameDef, BindingSlot};
use trust_ir::value::{BindingFrameId, ClosureTyId, GlobalId};
use trust_ir::{
    AssertKind, AssertOverflowOp, AtomicRMWOp, BinOp, BlockId, CallingConv, CastOp, Constant,
    DialectInst, FCmpOp, FuncId, FuncTyId, ICmpOp, Inst, Ordering, OverflowOp, PanicLocation,
    PanicSite, SwitchCase, Ty, UnOp, ValueId,
};

use super::{for_each_operand_mut, operands, replace_operands};

fn v(n: u32) -> ValueId {
    ValueId(n)
}

fn vs(range: std::ops::Range<u32>) -> Vec<ValueId> {
    range.map(ValueId).collect()
}

#[allow(clippy::too_many_lines)]
fn every_variant() -> Vec<Inst> {
    let b = BlockId(1);
    let frame = BindingFrameDef::new(
        BindingFrameId::new(0),
        "f",
        vec![BindingSlot::new("i", Ty::I64)],
    );
    let mut dialect = DialectInst::new("verif", "op");
    dialect.operands = vs(1..4);
    vec![
        Inst::BinOp {
            op: BinOp::Add,
            ty: Ty::I32,
            lhs: v(1),
            rhs: v(2),
        },
        Inst::UnOp {
            op: UnOp::Neg,
            ty: Ty::I32,
            operand: v(1),
        },
        Inst::Overflow {
            op: OverflowOp::AddOverflow,
            ty: Ty::I32,
            lhs: v(1),
            rhs: v(2),
        },
        Inst::ICmp {
            op: ICmpOp::Eq,
            ty: Ty::I32,
            lhs: v(1),
            rhs: v(2),
        },
        Inst::FCmp {
            op: FCmpOp::OEq,
            ty: Ty::F64,
            lhs: v(1),
            rhs: v(2),
        },
        Inst::Cast {
            op: CastOp::ZExt,
            src_ty: Ty::I8,
            dst_ty: Ty::I32,
            operand: v(1),
        },
        Inst::Load {
            ty: Ty::I32,
            ptr: v(1),
            volatile: false,
            align: None,
        },
        Inst::Store {
            ty: Ty::I32,
            ptr: v(1),
            value: v(2),
            volatile: false,
            align: None,
        },
        Inst::Alloca {
            ty: Ty::I32,
            count: Some(v(1)),
            align: None,
        },
        Inst::Alloca {
            ty: Ty::I32,
            count: None,
            align: None,
        },
        Inst::Drop {
            ty: Ty::I32,
            ptr: v(1),
        },
        Inst::HeapAlloc {
            ty: Ty::I32,
            count: Some(v(1)),
            align: None,
            origin: AllocOrigin::RustHeap,
        },
        Inst::GEP {
            pointee_ty: Ty::I32,
            base: v(1),
            indices: vs(2..5),
            inbounds: true,
        },
        Inst::PtrData {
            ptr_ty: Ty::Ptr,
            ptr: v(1),
        },
        Inst::PtrMetadata {
            ptr_ty: Ty::Ptr,
            metadata_ty: Ty::Usize,
            ptr: v(1),
        },
        Inst::PtrFromParts {
            ptr_ty: Ty::Ptr,
            metadata_ty: Ty::Usize,
            data: v(1),
            metadata: v(2),
        },
        Inst::AtomicLoad {
            ty: Ty::I32,
            ptr: v(1),
            ordering: Ordering::SeqCst,
        },
        Inst::AtomicStore {
            ty: Ty::I32,
            ptr: v(1),
            value: v(2),
            ordering: Ordering::SeqCst,
        },
        Inst::AtomicRMW {
            op: AtomicRMWOp::Add,
            ty: Ty::I32,
            ptr: v(1),
            value: v(2),
            ordering: Ordering::SeqCst,
        },
        Inst::CmpXchg {
            ty: Ty::I32,
            ptr: v(1),
            expected: v(2),
            desired: v(3),
            success: Ordering::SeqCst,
            failure: Ordering::SeqCst,
            weak: false,
        },
        Inst::Fence {
            ordering: Ordering::SeqCst,
        },
        Inst::Br {
            target: b,
            args: vs(1..4),
        },
        Inst::CondBr {
            cond: v(1),
            then_target: b,
            then_args: vs(2..4),
            else_target: b,
            else_args: vs(4..7),
        },
        Inst::Switch {
            value: v(1),
            default: b,
            default_args: vs(2..4),
            cases: vec![
                SwitchCase {
                    value: Constant::Int(0),
                    target: b,
                    args: vs(4..6),
                },
                SwitchCase {
                    value: Constant::Int(1),
                    target: b,
                    args: vs(6..8),
                },
            ],
            exhaustive_enum_unreachable: false,
        },
        Inst::Call {
            callee: FuncId(0),
            args: vs(1..4),
        },
        Inst::CallIndirect {
            callee: v(1),
            sig: FuncTyId(0),
            args: vs(2..5),
            calling_conv: CallingConv::default(),
        },
        Inst::Return { values: vs(1..4) },
        Inst::ExtractField {
            ty: Ty::I32,
            aggregate: v(1),
            field: 0,
        },
        Inst::InsertField {
            ty: Ty::I32,
            aggregate: v(1),
            field: 0,
            value: v(2),
        },
        Inst::ExtractElement {
            ty: Ty::I32,
            array: v(1),
            index: v(2),
        },
        Inst::InsertElement {
            ty: Ty::I32,
            array: v(1),
            index: v(2),
            value: v(3),
        },
        Inst::Const {
            ty: Ty::I32,
            value: Constant::Int(3),
        },
        Inst::NullPtr,
        Inst::GlobalAddr {
            global: GlobalId::new(0),
        },
        Inst::Undef { ty: Ty::I32 },
        Inst::Assume { cond: v(1) },
        Inst::Assert {
            cond: v(1),
            kind: AssertKind::Unspecified,
            site: None,
        },
        Inst::Assert {
            cond: v(1),
            kind: AssertKind::BoundsCheck {
                index: v(2),
                len: v(3),
            },
            site: Some(PanicSite {
                entry: FuncId(0),
                location: PanicLocation::Value(v(4)),
            }),
        },
        Inst::Assert {
            cond: v(1),
            kind: AssertKind::MisalignedPtr {
                required: v(2),
                found: v(3),
            },
            site: Some(PanicSite {
                entry: FuncId(0),
                location: PanicLocation::Global(GlobalId::new(0)),
            }),
        },
        Inst::Assert {
            cond: v(1),
            kind: AssertKind::Overflow(AssertOverflowOp::Add),
            site: None,
        },
        Inst::Unreachable,
        Inst::Copy {
            ty: Ty::I32,
            operand: v(1),
        },
        Inst::Select {
            ty: Ty::I32,
            cond: v(1),
            then_val: v(2),
            else_val: v(3),
        },
        Inst::SeqMapAddK {
            ty: Ty::I32,
            seq: v(1),
            k: 2,
        },
        Inst::SeqMapNot {
            ty: Ty::I32,
            seq: v(1),
        },
        Inst::SeqMap {
            ty: Ty::I32,
            seq: v(1),
            fwd: FuncId(0),
        },
        Inst::Borrow { ptr: v(1) },
        Inst::BorrowMut { ptr: v(1) },
        Inst::EndBorrow { borrow_ptr: v(1) },
        Inst::Retain { ptr: v(1) },
        Inst::Release { ptr: v(1) },
        Inst::IsUnique { ptr: v(1) },
        Inst::Dealloc { ptr: v(1) },
        Inst::MemCopy {
            dst: v(1),
            src: v(2),
            bytes: v(3),
            overlap: false,
        },
        Inst::MemSet {
            dst: v(1),
            byte: v(2),
            bytes: v(3),
        },
        Inst::OpenFrame { def: frame },
        Inst::BindSlot {
            frame: v(1),
            slot: 0,
            value: v(2),
        },
        Inst::LoadSlot {
            frame: v(1),
            slot: 0,
            ty: Ty::I64,
        },
        Inst::CloseFrame { frame: v(1) },
        Inst::CoroSuspend {
            frame: v(1),
            state_slot: 0,
            next_state: 1,
            value: v(2),
        },
        Inst::Invoke {
            callee: FuncId(0),
            args: vs(1..3),
            normal_dest: b,
            normal_args: vs(3..5),
            unwind_dest: b,
        },
        Inst::LandingPad {
            is_cleanup: true,
            catch_type_indices: vec![0],
        },
        Inst::Resume { exn: v(1) },
        Inst::AssertInvoke {
            cond: v(1),
            kind: AssertKind::BoundsCheck {
                index: v(2),
                len: v(3),
            },
            site: PanicSite {
                entry: FuncId(0),
                location: PanicLocation::Value(v(4)),
            },
            normal_dest: b,
            normal_args: vs(5..7),
            unwind_dest: b,
        },
        Inst::DialectOp(Box::new(dialect)),
        Inst::TensorContract {
            ty: Ty::Tensor(Box::new(Ty::I32), 1),
            lhs: v(1),
            rhs: v(2),
            batch: vec![(0, 0)],
            contract: vec![(1, 1)],
        },
        Inst::TensorMap {
            ty: Ty::Tensor(Box::new(Ty::I32), 1),
            args: vs(1..4),
            body: vec![trust_ir::TensorMapNode::BinOp {
                op: trust_ir::BinOp::Add,
                ty: Ty::I32,
                lhs: 0,
                rhs: 1,
            }],
        },
        Inst::TensorReduce {
            ty: Ty::Tensor(Box::new(Ty::I32), 1),
            src: v(1),
            op: trust_ir::TensorReduceOp::Add,
            axes: vec![1],
            order: trust_ir::TensorReduceOrder::RowMajor,
        },
        // The source, the parameters, then the fill: every operand position.
        Inst::TensorView {
            ty: Ty::Tensor(Box::new(Ty::I32), 1),
            src: v(1),
            params: vs(2..4),
            exprs: vec![trust_ir::TensorIndexExpr::Param(0)],
            shape: vec![0],
            index: vec![0],
            fill: Some(v(4)),
        },
        // No fill: the optional operand is absent, not a placeholder.
        Inst::TensorView {
            ty: Ty::Tensor(Box::new(Ty::I32), 1),
            src: v(1),
            params: vec![],
            exprs: vec![trust_ir::TensorIndexExpr::Coord(0)],
            shape: vec![0],
            index: vec![0],
            fill: None,
        },
        Inst::TensorGather {
            ty: Ty::Tensor(Box::new(Ty::I32), 1),
            data: v(1),
            coords: vs(2..4),
        },
        Inst::TensorScatter {
            ty: Ty::Tensor(Box::new(Ty::I32), 1),
            init: v(1),
            src: v(2),
            coords: vs(3..5),
        },
        Inst::MakeAggregate {
            ty: Ty::I32,
            variant: None,
            fields: vs(1..4),
        },
        Inst::ArraySplat {
            ty: Ty::I32,
            value: v(1),
        },
        Inst::CallCannotUnwind {
            callee: FuncId(0),
            args: vs(1..3),
        },
        Inst::CallIndirectCannotUnwind {
            callee: v(1),
            sig: FuncTyId(0),
            args: vs(2..4),
            calling_conv: CallingConv::default(),
        },
        Inst::DropInvoke {
            ty: Ty::I32,
            ptr: v(1),
            normal_dest: b,
            normal_args: vs(2..4),
            unwind_dest: b,
        },
        Inst::InvokeIndirect {
            callee: v(1),
            sig: FuncTyId(0),
            args: vs(2..4),
            calling_conv: CallingConv::default(),
            normal_dest: b,
            normal_args: vs(4..6),
            unwind_dest: b,
        },
        Inst::MakeClosure {
            ty: ClosureTyId::new(0),
            func: FuncId(0),
            captures: vs(1..3),
        },
    ]
}

#[test]
fn mutable_walk_matches_visit_value_operands_on_every_variant() {
    let all = every_variant();
    let mut shapes = std::collections::BTreeSet::new();
    for inst in all {
        shapes.insert(format!("{:?}", inst.shape()));
        let expected = operands(&inst);
        let mut seen = Vec::new();
        let mut copy = inst.clone();
        for_each_operand_mut(&mut copy, &mut |slot| seen.push(*slot));
        assert_eq!(seen, expected, "{inst:?}");
        // Replacing through the mutable walk is what the read-only walk sees.
        let replaced: Vec<ValueId> = expected
            .iter()
            .map(|value| ValueId(value.0 + 1000))
            .collect();
        let mut target = inst.clone();
        assert!(replace_operands(&mut target, &replaced), "{inst:?}");
        assert_eq!(operands(&target), replaced, "{inst:?}");
        // Nothing but operands changed: undoing the replacement restores it.
        assert!(replace_operands(&mut target, &expected));
        assert_eq!(target, inst);
        // A count mismatch is reported.
        if !expected.is_empty() {
            let mut short = inst.clone();
            assert!(!replace_operands(&mut short, &replaced[1..]));
        }
        let mut long = inst.clone();
        let mut extra = replaced.clone();
        extra.push(ValueId(9999));
        assert!(!replace_operands(&mut long, &extra));
    }
    // Every variant of the pinned `Inst` was built at least once.
    assert_eq!(shapes.len(), 74, "variant shapes built");
}
