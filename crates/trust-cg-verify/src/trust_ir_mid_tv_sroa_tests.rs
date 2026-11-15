// trust-cg-verify/trust_ir_mid_tv_sroa_tests.rs - the scalar-replacement checker
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! The checker accepts a promotion through a join, a loop, a signedness
//! reinterpretation, a pointer field (carried as an integer, or as the
//! pointer itself when it holds an address inside a fresh allocation), a
//! struct `gep`/`ptrtoptr`, the bridge's field writes and reads through the
//! slot, a word copied over narrower fields (its parts merged into and
//! extracted from one unsigned integer) and an initial zero for a read only
//! the `alloca` reaches (each also agreeing with the source in the reference
//! interpreter, or in its view of the lane's forms), and refuses a named
//! wrong one for each failure class (the negative controls): a pointer
//! carrier of an address of unknown provenance or one past the end of its
//! allocation, an integer view of a pointer carrier, a field read through
//! the slot at the wrong lane, a write-through kept in the target or whose
//! result is used, a lane written with a value of another type or missing
//! from its aggregate, a part of a field carried as a signed integer, read
//! from a value other than the field's, or with too few or too many values,
//! a value that may be poison stored into part of a field, an initial value
//! of a float field or not fresh, an
//! undefined read, a wrong reaching value, a missing or wrong incoming value,
//! a mixed width, a partial overlap, a volatile or atomic access, an escape
//! through a call, a `ptrtoint`, a stored address or a return, a conversion
//! of a value that may be poison, a stored `undef`, an irreducible CFG, a
//! parameter on the entry block, an access left unrewritten, and a target
//! that is not the claimed rewrite. A `bool` field also read and written as
//! a one-byte integer is carried as the byte (`zext` of a stored `bool`,
//! the nonzero test against a fresh zero for a `bool` read); a read without
//! that zero, with a zero that is not fresh, at a carrier of another width,
//! of a byte some store may leave poison, or spelled as a truncation (the
//! byte 2, which the differential also tells apart) is refused. A converted
//! store of a value computed from a read of the slot itself (a loop's step
//! of an iterator field) is accepted when every value stored into the slot
//! is never poison, and refused beside a store of a load of another slot.

use super::*;
use crate::trust_ir_mid_tv::{
    DifferentialBudget, PassWitness, check_pass, compare_samples, run_samples, seeded_inputs,
};

const HEADER: &str = "; TrustIr text format v1\nmodule \"sroa\"\n\
                      target \"wasm32-unknown-unknown\" 4 little\n\n";

fn module(body: &str) -> Module {
    trust_ir::parser::parse_module(&format!("{HEADER}{body}"))
        .unwrap_or_else(|e| panic!("test module failed to parse: {e}\n{body}"))
}

fn func<'m>(module: &'m Module, name: &str) -> &'m Function {
    module
        .functions
        .iter()
        .find(|f| f.name == name)
        .expect("function")
}

fn v(n: u32) -> ValueId {
    ValueId::new(n)
}

fn b(n: u32) -> BlockId {
    BlockId::new(n)
}

/// Where `value` is defined: (block id, node index).
fn at(func: &Function, value: u32) -> (BlockId, usize) {
    for block in &func.blocks {
        for (i, node) in block.body.iter().enumerate() {
            if node.results.contains(&v(value)) {
                return (block.id, i);
            }
        }
    }
    panic!("%{value} is not defined");
}

/// The node index of the `nth` store of block `block`.
fn store_at(func: &Function, block: u32, nth: usize) -> (BlockId, usize) {
    let bl = func.blocks.iter().find(|bl| bl.id == b(block)).unwrap();
    let index = bl
        .body
        .iter()
        .enumerate()
        .filter(|(_, n)| matches!(n.inst, Inst::Store { .. }))
        .nth(nth)
        .expect("store")
        .0;
    (bl.id, index)
}

fn store(
    func: &Function,
    block: u32,
    nth: usize,
    field: usize,
    converted: Option<u32>,
) -> SroaStore {
    let (block, index) = store_at(func, block, nth);
    SroaStore {
        block,
        index,
        field,
        converted: converted.map(v),
        via: None,
        merge: None,
    }
}

fn load(func: &Function, result: u32, field: usize, value: u32) -> SroaLoad {
    let (block, index) = at(func, result);
    SroaLoad {
        block,
        index,
        result: v(result),
        field,
        value: v(value),
        via: None,
        extract: Vec::new(),
    }
}

fn incoming(pred: u32, edge: usize, value: u32) -> SroaIncoming {
    SroaIncoming {
        pred: b(pred),
        edge,
        value: v(value),
    }
}

fn field(offset: u64, size: u64, carrier: Ty) -> SroaField {
    SroaField {
        offset,
        size,
        carrier,
        init: None,
    }
}

/// The checker's own rebuild of `slot` on `name` of `src`, then the full
/// check of that target.
fn check(src: &Module, name: &str, slot: SroaSlot) -> Result<Function, MidTvError> {
    let f = func(src, name);
    let witness = SroaWitness { slots: vec![slot] };
    let (target, verdict) = rebuild_sroa(src, 32, f, &witness)?;
    assert_eq!(verdict.refinements, witness.rewrite_count());
    check_pass(src, 32, f, &target, &PassWitness::Sroa(witness))?;
    Ok(target)
}

/// No load or store of the function goes through `alloca` any more, and the
/// source and the target agree on every seeded input the interpreter
/// finishes (at least one).
fn assert_promoted_and_equivalent(src: &Module, name: &str, target: &Function, alloca: u32) {
    let f = func(src, name);
    let index = Defs::of(target);
    for node in target.blocks.iter().flat_map(|bl| &bl.body) {
        if let Inst::Load { ptr, .. } | Inst::Store { ptr, .. } = &node.inst {
            let mut root = *ptr;
            while let Some(Inst::GEP { base, .. } | Inst::Cast { operand: base, .. }) =
                index.inst(root)
            {
                root = *base;
            }
            assert_ne!(root, v(alloca), "an access through the slot remains");
        }
    }
    let inputs = seeded_inputs(src, f, 32, 16, 7).expect("synthesizable parameters");
    let mut tgt = src.clone();
    let position = tgt.functions.iter().position(|g| g.name == name).unwrap();
    tgt.functions[position] = target.clone();
    // trust-ir's validator finds nothing in the target it does not find in
    // the source (the wasm32 lane emits a mid-end output only then).
    let findings = |m: &Module| -> Vec<String> {
        trust_ir_build::validate_module(m)
            .iter()
            .map(|e| format!("{e:?}"))
            .collect()
    };
    let before = findings(src);
    let new: Vec<String> = findings(&tgt)
        .into_iter()
        .filter(|e| !before.contains(e))
        .collect();
    assert!(new.is_empty(), "new validation findings: {new:?}");
    let budget = DifferentialBudget::default();
    let (source_runs, _) = run_samples(src, f, &inputs, budget);
    let (target_runs, _) = run_samples(&tgt, target, &inputs, budget);
    let report = compare_samples(&source_runs, &target_runs);
    assert!(report.mismatch.is_none(), "{:?}", report.mismatch);
    assert!(report.compared > 0, "{report:?}");
}

// ---------------------------------------------------------------------------
// Accepted promotions
// ---------------------------------------------------------------------------

/// Two `i32` fields; field 0 is written on one arm of a diamond and read at
/// the join, then copied into field 1 and read back.
const DIAMOND: &str = "type ty.0 = i32\n\nfuncty.0 = (i32, i32) -> (i32)\n\n\
    fn @f(functy.0) {\n\
    bb0(%0: i32, %1: i32):\n\
    \x20   %2 = alloca [ty.0 x 2], align 4\n\
    \x20   %3 = const i32 4\n\
    \x20   %4 = gep inbounds u8, ptr %2, %3\n\
    \x20   store i32 %0, ptr %2\n\
    \x20   %5 = icmp slt i32 %0, %1\n\
    \x20   condbr %5, bb1, bb2\n\
    bb1:\n\
    \x20   store i32 %1, ptr %2\n\
    \x20   br bb3\n\
    bb2:\n\
    \x20   br bb3\n\
    bb3:\n\
    \x20   %6 = load i32, ptr %2\n\
    \x20   store i32 %6, ptr %4\n\
    \x20   %7 = load i32, ptr %4\n\
    \x20   %8 = add i32 %6, %7\n\
    \x20   ret %8\n\
    }\n";

fn diamond_slot(f: &Function) -> SroaSlot {
    SroaSlot {
        alloca: v(2),
        fields: vec![field(0, 4, Ty::I32), field(4, 4, Ty::I32)],
        stores: vec![
            store(f, 0, 0, 0, None),
            store(f, 1, 0, 0, None),
            store(f, 3, 0, 1, None),
        ],
        loads: vec![load(f, 6, 0, 100), load(f, 7, 1, 6)],
        params: vec![SroaParam {
            block: b(3),
            field: 0,
            value: v(100),
            incoming: vec![incoming(1, 0, 1), incoming(2, 0, 0)],
        }],
    }
}

#[test]
fn a_join_of_two_stores_becomes_a_block_parameter() {
    let src = module(DIAMOND);
    let f = func(&src, "f");
    let target = check(&src, "f", diamond_slot(f)).unwrap_or_else(|e| panic!("{e}"));
    let join = target.blocks.iter().find(|bl| bl.id == b(3)).unwrap();
    assert_eq!(join.params, vec![(v(100), Ty::I32)]);
    assert_promoted_and_equivalent(&src, "f", &target, 2);
}

/// A loop-carried accumulator in a slot: stored before the loop and in its
/// body, read in the body and after the loop.
const LOOP: &str = "functy.0 = (i32, i32) -> (i32)\n\n\
    fn @f(functy.0) {\n\
    bb0(%0: i32, %1: i32):\n\
    \x20   %2 = alloca i32\n\
    \x20   %3 = const i32 0\n\
    \x20   store i32 %3, ptr %2\n\
    \x20   br bb1(%3)\n\
    bb1(%4: i32):\n\
    \x20   %20 = const i32 9\n\
    \x20   %21 = and i32 %1, %20\n\
    \x20   %5 = icmp slt i32 %4, %21\n\
    \x20   condbr %5, bb2, bb3\n\
    bb2:\n\
    \x20   %6 = load i32, ptr %2\n\
    \x20   %7 = add i32 %6, %0\n\
    \x20   store i32 %7, ptr %2\n\
    \x20   %8 = const i32 1\n\
    \x20   %9 = add i32 %4, %8\n\
    \x20   br bb1(%9)\n\
    bb3:\n\
    \x20   %10 = load i32, ptr %2\n\
    \x20   ret %10\n\
    }\n";

fn loop_slot(f: &Function) -> SroaSlot {
    SroaSlot {
        alloca: v(2),
        fields: vec![field(0, 4, Ty::I32)],
        stores: vec![store(f, 0, 0, 0, None), store(f, 2, 0, 0, None)],
        loads: vec![load(f, 6, 0, 100), load(f, 10, 0, 100)],
        params: vec![SroaParam {
            block: b(1),
            field: 0,
            value: v(100),
            incoming: vec![incoming(0, 0, 3), incoming(2, 0, 7)],
        }],
    }
}

#[test]
fn a_loop_carried_slot_becomes_a_header_parameter() {
    let src = module(LOOP);
    let f = func(&src, "f");
    let target = check(&src, "f", loop_slot(f)).unwrap_or_else(|e| panic!("{e}"));
    let header = target.blocks.iter().find(|bl| bl.id == b(1)).unwrap();
    assert_eq!(header.params.len(), 2);
    assert_promoted_and_equivalent(&src, "f", &target, 2);
}

#[test]
fn a_signedness_view_is_a_bitcast_of_a_full_value() {
    let text = "functy.0 = (u32) -> (i32)\n\n\
        fn @f(functy.0) {\n\
        bb0(%0: u32):\n\
        \x20   %1 = alloca i32\n\
        \x20   store u32 %0, ptr %1\n\
        \x20   %2 = load i32, ptr %1\n\
        \x20   ret %2\n\
        }\n";
    let src = module(text);
    let f = func(&src, "f");
    let slot = SroaSlot {
        alloca: v(1),
        fields: vec![field(0, 4, Ty::U32)],
        stores: vec![store(f, 0, 0, 0, None)],
        loads: vec![load(f, 2, 0, 0)],
        params: vec![],
    };
    let target = check(&src, "f", slot).unwrap_or_else(|e| panic!("{e}"));
    assert!(target.blocks[0].body.iter().any(|n| matches!(
        n.inst,
        Inst::Cast {
            op: CastOp::Bitcast,
            ..
        }
    )));
    assert_promoted_and_equivalent(&src, "f", &target, 1);
}

#[test]
fn a_pointer_field_is_carried_as_its_address() {
    let text = "functy.0 = (i32) -> (i32)\n\n\
        fn @f(functy.0) {\n\
        bb0(%0: i32):\n\
        \x20   %1 = alloca i32\n\
        \x20   %2 = alloca ptr\n\
        \x20   store i32 %0, ptr %1\n\
        \x20   store ptr %1, ptr %2\n\
        \x20   %3 = load ptr, ptr %2\n\
        \x20   %4 = load i32, ptr %3\n\
        \x20   ret %4\n\
        }\n";
    let src = module(text);
    let f = func(&src, "f");
    let slot = SroaSlot {
        alloca: v(2),
        fields: vec![field(0, 4, Ty::I32)],
        stores: vec![store(f, 0, 1, 0, Some(100))],
        loads: vec![load(f, 3, 0, 100)],
        params: vec![],
    };
    let target = check(&src, "f", slot).unwrap_or_else(|e| panic!("{e}"));
    let ops: Vec<CastOp> = target.blocks[0]
        .body
        .iter()
        .filter_map(|n| match n.inst {
            Inst::Cast { op, .. } => Some(op),
            _ => None,
        })
        .collect();
    assert_eq!(ops, vec![CastOp::PtrToInt, CastOp::IntToPtr]);
    assert_promoted_and_equivalent(&src, "f", &target, 2);

    // The stored pointer is `%1`'s address, inside a fresh allocation: a
    // reload resolves it to the same allocation and offset, so the field is
    // carried as the pointer itself, and the load becomes its copy.
    let slot = SroaSlot {
        alloca: v(2),
        fields: vec![field(0, 4, Ty::Ptr)],
        stores: vec![store(f, 0, 1, 0, None)],
        loads: vec![load(f, 3, 0, 1)],
        params: vec![],
    };
    let target = check(&src, "f", slot).unwrap_or_else(|e| panic!("{e}"));
    assert!(
        !target.blocks[0]
            .body
            .iter()
            .any(|n| matches!(n.inst, Inst::Cast { .. })),
        "{target:#?}"
    );
    assert_promoted_and_equivalent(&src, "f", &target, 2);
}

/// A pointer reload is the stored pointer only when the address names the
/// same allocation again: a pointer of unknown provenance, an address one
/// past the end of its allocation, and an integer view of the field are
/// refused for a `ptr` carrier.
#[test]
fn negative_control_a_pointer_carrier_of_an_unstable_address_is_refused() {
    let base = "type ty.0 = i32\n\nfuncty.0 = (i32) -> (i32)\n\n\
        fn @f(functy.0) {\n\
        bb0(%0: i32):\n\
        \x20   %1 = alloca [ty.0 x 2]\n\
        \x20   %2 = alloca ptr\n\
        \x20   store i32 %0, ptr %1\n\
        \x20   %6 = const i32 4\n\
        \x20   %7 = gep inbounds u8, ptr %1, %6\n\
        \x20   %8 = copy ptr %7\n\
        \x20   store ptr %8, ptr %2\n\
        \x20   %3 = load ptr, ptr %2\n\
        \x20   %4 = ptrtoint ptr %3 to i32\n\
        \x20   ret %4\n\
        }\n";
    let pointer_slot = |text: &str| {
        let src = module(text);
        let f = func(&src, "f");
        let slot = SroaSlot {
            alloca: v(2),
            fields: vec![field(0, 4, Ty::Ptr)],
            stores: vec![store(f, 0, 1, 0, None)],
            loads: vec![load(f, 3, 0, 8)],
            params: vec![],
        };
        check(&src, "f", slot)
    };
    // In bounds (4 bytes into 8): accepted.
    let target = pointer_slot(base).unwrap_or_else(|e| panic!("{e}"));
    assert_promoted_and_equivalent(&module(base), "f", &target, 2);
    let not_fresh = |err: &MidTvError| matches!(err, MidTvError::NotScalarizable { why, .. } if why.contains("fresh allocation"));
    // A parameter's provenance is unknown.
    let param = base
        .replace("(i32) -> (i32)", "(i32, ptr) -> (i32)")
        .replace("bb0(%0: i32):", "bb0(%0: i32, %9: ptr):")
        .replace("store ptr %8, ptr %2", "store ptr %9, ptr %2");
    let src = module(&param);
    let f = func(&src, "f");
    let err = check(
        &src,
        "f",
        SroaSlot {
            alloca: v(2),
            fields: vec![field(0, 4, Ty::Ptr)],
            stores: vec![store(f, 0, 1, 0, None)],
            loads: vec![load(f, 3, 0, 9)],
            params: vec![],
        },
    )
    .unwrap_err();
    assert!(not_fresh(&err), "{err}");
    // One past the end (8 bytes into 8): a reload may name a neighbour.
    let past = base.replace("%6 = const i32 4", "%6 = const i32 8");
    let err = pointer_slot(&past).unwrap_err();
    assert!(not_fresh(&err), "{err}");
    // An integer view of a pointer-carried field.
    let int_view = base.replace(
        "    %3 = load ptr, ptr %2\n    %4 = ptrtoint ptr %3 to i32\n",
        "    %3 = load i32, ptr %2\n    %4 = copy i32 %3\n",
    );
    let err = pointer_slot(&int_view).unwrap_err();
    assert!(
        matches!(err, MidTvError::NotScalarizable { why, .. } if why.contains("non-pointer")),
        "{err}"
    );
}

/// The bridge's field access through a pointer: lanes 1 and 0 written
/// through the slot (the results unused), lane 1 read through the slot and
/// by a plain load, lane 0 by a plain load.
const THROUGH: &str = "type ty.0 = i64\n\nfuncty.0 = (i64) -> (i64)\n\n\
    fn @f(functy.0) {\n\
    bb0(%0: i64):\n\
    \x20   %1 = alloca [ty.0 x 2], align 8\n\
    \x20   %2 = insertfield [ty.0 x 2] %1, 1, %0\n\
    \x20   %10 = const i64 3\n\
    \x20   %11 = mul i64 %0, %10\n\
    \x20   %3 = insertfield [ty.0 x 2] %1, 0, %11\n\
    \x20   %4 = extractfield [ty.0 x 2] %1, 1\n\
    \x20   %5 = const i32 8\n\
    \x20   %6 = gep inbounds u8, ptr %1, %5\n\
    \x20   %7 = load i64, ptr %6\n\
    \x20   %8 = load i64, ptr %1\n\
    \x20   %9 = add i64 %4, %7\n\
    \x20   %12 = add i64 %9, %8\n\
    \x20   ret %12\n\
    }\n";

fn through_slot(f: &Function) -> SroaSlot {
    let insert_at = |result: u32| {
        let (block, index) = at(f, result);
        SroaStore {
            block,
            index,
            field: 0,
            converted: None,
            via: None,
            merge: None,
        }
    };
    SroaSlot {
        alloca: v(1),
        fields: vec![field(0, 8, Ty::I64), field(8, 8, Ty::I64)],
        stores: vec![
            SroaStore {
                field: 1,
                ..insert_at(2)
            },
            insert_at(3),
        ],
        loads: vec![load(f, 4, 1, 0), load(f, 7, 1, 0), load(f, 8, 0, 11)],
        params: vec![],
    }
}

/// The source and `target` agree on every seeded input in the lane's view
/// (the interpreter refuses the bridge's forms over a pointer as type
/// errors; the view spells them as the stores and loads the lane emits).
fn assert_equivalent_in_view(src: &Module, name: &str, target: &Function) {
    let f = func(src, name);
    let viewed = crate::trust_ir_mid_tv::interpretable(src, f).expect("the view rewrites them");
    let mut view = src.clone();
    let position = view.functions.iter().position(|g| g.name == name).unwrap();
    view.functions[position] = viewed.clone();
    let mut tgt = src.clone();
    tgt.functions[position] = target.clone();
    let inputs = seeded_inputs(src, f, 32, 16, 7).expect("synthesizable parameters");
    let budget = DifferentialBudget::default();
    let (source_runs, _) = run_samples(&view, &viewed, &inputs, budget);
    let (target_runs, _) = run_samples(&tgt, target, &inputs, budget);
    let report = compare_samples(&source_runs, &target_runs);
    assert!(report.mismatch.is_none(), "{:?}", report.mismatch);
    assert!(report.compared > 0, "{report:?}");
}

#[test]
fn fields_written_and_read_through_the_slot_are_promoted() {
    let src = module(THROUGH);
    let f = func(&src, "f");
    let target = check(&src, "f", through_slot(f)).unwrap_or_else(|e| panic!("{e}"));
    // Each write-through `insertfield` goes with its unused result; no field
    // access through the slot is left.
    assert!(!target.blocks[0].body.iter().any(|n| matches!(
        n.inst,
        Inst::InsertField { .. } | Inst::ExtractField { .. } | Inst::Load { .. }
    )));
    assert_equivalent_in_view(&src, "f", &target);
}

#[test]
fn negative_control_a_wrong_field_access_through_the_slot_is_refused() {
    let src = module(THROUGH);
    let f = func(&src, "f");
    // The read-through `extractfield` reads lane 1 (bytes 8..16), not field 0.
    let mut slot = through_slot(f);
    slot.loads[0].field = 0;
    let err = check(&src, "f", slot).unwrap_err();
    assert!(
        matches!(err, MidTvError::NotScalarizable { why, .. } if why.contains("cover exactly")),
        "{err}"
    );
    // A target that keeps a write-through (the store it is) is not the
    // rewrite.
    let slot = through_slot(f);
    let (mut target, _) = rebuild_sroa(
        &src,
        32,
        f,
        &SroaWitness {
            slots: vec![slot.clone()],
        },
    )
    .unwrap_or_else(|e| panic!("{e}"));
    target.blocks[0].body.insert(1, f.blocks[0].body[1].clone());
    let err = check_pass(
        &src,
        32,
        f,
        &target,
        &PassWitness::Sroa(SroaWitness { slots: vec![slot] }),
    )
    .unwrap_err();
    assert!(matches!(err, MidTvError::TargetDiffers { .. }), "{err}");
    // A write-through whose result is used: the lane types that result as
    // the record, so the access through it is no access through the slot.
    let used = module(&THROUGH.replace("%8 = load i64, ptr %1", "%8 = load i64, ptr %3"));
    let f = func(&used, "f");
    let err = check(&used, "f", through_slot(f)).unwrap_err();
    assert!(
        matches!(err, MidTvError::SlotObservable { why, .. } if why.contains("result is used")),
        "{err}"
    );
    // A lane written with a value of another type (the lane would
    // reinterpret it).
    let narrow = THROUGH
        .replace("(i64) -> (i64)", "(i64, i32) -> (i64)")
        .replace("bb0(%0: i64):", "bb0(%0: i64, %20: i32):")
        .replace(
            "insertfield [ty.0 x 2] %1, 1, %0",
            "insertfield [ty.0 x 2] %1, 1, %20",
        );
    let src = module(&narrow);
    let f = func(&src, "f");
    let err = check(&src, "f", through_slot(f)).unwrap_err();
    assert!(
        matches!(err, MidTvError::NotScalarizable { why, .. } if why.contains("type")),
        "{err}"
    );
    // A lane the aggregate does not have leaves the slot observable.
    let no_lane = THROUGH.replace(
        "insertfield [ty.0 x 2] %1, 0, %11",
        "insertfield [ty.0 x 2] %1, 2, %11",
    );
    let src = module(&no_lane);
    let f = func(&src, "f");
    let err = check(&src, "f", through_slot(f)).unwrap_err();
    assert!(
        matches!(err, MidTvError::SlotObservable { why, .. } if why.contains("no lane")),
        "{err}"
    );
}

#[test]
fn a_typed_pointer_field_goes_through_ptr() {
    let text = "functy.0 = (i32) -> (i32)\n\n\
        fn @f(functy.0) {\n\
        bb0(%0: i32):\n\
        \x20   %1 = alloca i32\n\
        \x20   %2 = alloca ptr\n\
        \x20   store i32 %0, ptr %1\n\
        \x20   %5 = ptrtoptr ptr %1 to &i32\n\
        \x20   store &i32 %5, ptr %2\n\
        \x20   %3 = load &i32, ptr %2\n\
        \x20   %4 = load i32, ptr %3\n\
        \x20   ret %4\n\
        }\n";
    let src = module(text);
    let f = func(&src, "f");
    let slot = |store_via: Option<u32>, load_via: Option<u32>| SroaSlot {
        alloca: v(2),
        fields: vec![field(0, 4, Ty::I32)],
        stores: vec![SroaStore {
            via: store_via.map(v),
            ..store(f, 0, 1, 0, Some(100))
        }],
        loads: vec![SroaLoad {
            via: load_via.map(v),
            ..load(f, 3, 0, 100)
        }],
        params: vec![],
    };
    let target = check(&src, "f", slot(Some(101), Some(102))).unwrap_or_else(|e| panic!("{e}"));
    let ops: Vec<CastOp> = target.blocks[0]
        .body
        .iter()
        .filter_map(|n| match n.inst {
            Inst::Cast { op, .. } => Some(op),
            _ => None,
        })
        .collect();
    assert_eq!(
        ops,
        vec![
            CastOp::PtrToPtr,
            CastOp::PtrToPtr,
            CastOp::PtrToInt,
            CastOp::IntToPtr,
            CastOp::PtrToPtr
        ]
    );
    assert_promoted_and_equivalent(&src, "f", &target, 2);
    // `ptrtoint` and `inttoptr` take and give only `ptr`: the cast through it
    // is required, and only there.
    for (store_via, load_via) in [(None, Some(102)), (Some(101), None)] {
        let err = check(&src, "f", slot(store_via, load_via)).unwrap_err();
        assert!(
            matches!(err, MidTvError::NotScalarizable { why, .. } if why.contains("pointer cast")),
            "{err}"
        );
    }
}

#[test]
fn a_struct_gep_and_a_pointer_cast_reach_their_fields() {
    let text = "functy.0 = (i64, i64) -> (i64)\n\n\
        fn @f(functy.0) {\n\
        bb0(%0: i64, %1: i64):\n\
        \x20   %2 = alloca (i64, i64)\n\
        \x20   %3 = const i32 1\n\
        \x20   %4 = gep inbounds i64, ptr %2, %3\n\
        \x20   %5 = ptrtoptr ptr %2 to &i64\n\
        \x20   store i64 %0, ptr %5\n\
        \x20   store i64 %1, ptr %4\n\
        \x20   %6 = load i64, ptr %2\n\
        \x20   %7 = load i64, ptr %4\n\
        \x20   %8 = sub i64 %6, %7\n\
        \x20   ret %8\n\
        }\n";
    let src = module(text);
    let f = func(&src, "f");
    let slot = SroaSlot {
        alloca: v(2),
        fields: vec![field(0, 8, Ty::I64), field(8, 8, Ty::I64)],
        stores: vec![store(f, 0, 0, 0, None), store(f, 0, 1, 1, None)],
        loads: vec![load(f, 6, 0, 0), load(f, 7, 1, 1)],
        params: vec![],
    };
    let target = check(&src, "f", slot).unwrap_or_else(|e| panic!("{e}"));
    assert_promoted_and_equivalent(&src, "f", &target, 2);
}

// ---------------------------------------------------------------------------
// Negative controls
// ---------------------------------------------------------------------------

/// A word copy over narrower fields (the bridge's): two `i32` halves stored,
/// the `i64` word loaded, then the high half read back as an `f32`'s bits.
const PARTS: &str = "functy.0 = (i32, i32) -> (i64)\n\n\
    fn @f(functy.0) {\n\
    bb0(%0: i32, %1: i32):\n\
    \x20   %2 = alloca i64, align 8\n\
    \x20   store i32 %0, ptr %2\n\
    \x20   %3 = const i32 4\n\
    \x20   %4 = gep inbounds u8, ptr %2, %3\n\
    \x20   store i32 %1, ptr %4\n\
    \x20   %5 = load i64, ptr %2\n\
    \x20   %6 = load f32, ptr %4\n\
    \x20   %7 = fptosi f32 %6 to i64\n\
    \x20   %8 = add i64 %5, %7\n\
    \x20   ret %8\n\
    }\n";

/// The witness of `PARTS`: one `u64` field from a zero, each half merged in,
/// the word read whole (a bitcast) and the high half read as its part.
fn parts_slot(f: &Function) -> SroaSlot {
    let merge = |prev: u32, values: std::ops::Range<u32>| SroaMerge {
        prev: v(prev),
        values: values.map(v).collect(),
    };
    SroaSlot {
        alloca: v(2),
        fields: vec![SroaField {
            init: Some(v(100)),
            ..field(0, 8, Ty::U64)
        }],
        stores: vec![
            // bits (i32 -> u32), zext, mask, and, or.
            SroaStore {
                merge: Some(merge(100, 101..106)),
                ..store(f, 0, 0, 0, None)
            },
            // bits, zext, shift amount, shl, mask, and, or.
            SroaStore {
                merge: Some(merge(105, 110..117)),
                ..store(f, 0, 1, 0, None)
            },
        ],
        loads: vec![
            SroaLoad {
                ..load(f, 5, 0, 116)
            },
            // shift amount, lshr, trunc.
            SroaLoad {
                extract: vec![v(120), v(121), v(122)],
                ..load(f, 6, 0, 116)
            },
        ],
        params: vec![],
    }
}

#[test]
fn a_field_accessed_in_parts_is_carried_as_its_word() {
    let src = module(PARTS);
    let f = func(&src, "f");
    let target = check(&src, "f", parts_slot(f)).unwrap_or_else(|e| panic!("{e}"));
    // The halves are merged with masks and a shift, the word is a bitcast
    // of the carrier, and the high half is shifted down and truncated.
    let ops: Vec<String> = target.blocks[0]
        .body
        .iter()
        .filter_map(|n| match &n.inst {
            Inst::BinOp { op, .. } => Some(format!("{op:?}")),
            Inst::Cast { op, .. } => Some(format!("{op:?}")),
            _ => None,
        })
        .collect();
    assert_eq!(
        ops,
        [
            "Bitcast", "ZExt", "And", "Or", "Bitcast", "ZExt", "Shl", "And", "Or", "Bitcast",
            "LShr", "Trunc", "Bitcast", "FPToSI", "Add"
        ]
    );
    assert_promoted_and_equivalent(&src, "f", &target, 2);
}

#[test]
fn negative_control_a_wrong_part_access_is_refused() {
    let src = module(PARTS);
    let f = func(&src, "f");
    let refused = |slot: SroaSlot, needle: &str| {
        let err = check(&src, "f", slot).unwrap_err();
        assert!(
            matches!(&err, MidTvError::NotScalarizable { why, .. } if why.contains(needle))
                || matches!(&err, MidTvError::NoUniqueReachingStore { why, .. } if why.contains(needle)),
            "{needle}: {err}"
        );
    };
    // A field accessed in parts carried as a signed integer.
    let mut slot = parts_slot(f);
    slot.fields[0].carrier = Ty::I64;
    refused(slot, "unsigned integer");
    // A part store whose merge reads another value than the field's.
    let mut slot = parts_slot(f);
    slot.stores[1].merge.as_mut().unwrap().prev = v(100);
    refused(slot, "another store of the field");
    // Without the initial zero the first part store reads fresh bytes.
    let mut slot = parts_slot(f);
    slot.fields[0].init = None;
    refused(slot, "undefined read");
    // A part store or load naming the wrong number of values.
    let mut slot = parts_slot(f);
    slot.stores[1].merge.as_mut().unwrap().values.pop();
    refused(slot, "too few values");
    let mut slot = parts_slot(f);
    slot.loads[1].extract.push(v(123));
    refused(slot, "too many values");
    // A part store claiming a conversion.
    let mut slot = parts_slot(f);
    slot.stores[0].converted = Some(v(130));
    refused(slot, "claims a conversion");
    // An initial value that is not fresh.
    let mut slot = parts_slot(f);
    slot.fields[0].init = Some(v(0));
    refused(slot, "fresh");
    // A value stored into part of the field that may be poison (a load).
    let poison = PARTS.replace(
        "    store i32 %0, ptr %2\n",
        "    %20 = alloca i32\n    store i32 %0, ptr %20\n    %21 = load i32, ptr %20\n    store i32 %21, ptr %2\n",
    );
    let src = module(&poison);
    let f = func(&src, "f");
    let mut slot = parts_slot(f);
    slot.stores[0] = SroaStore {
        merge: Some(SroaMerge {
            prev: v(100),
            values: (101..106).map(v).collect(),
        }),
        ..store(f, 0, 1, 0, None)
    };
    slot.stores[1] = SroaStore {
        merge: Some(SroaMerge {
            prev: v(105),
            values: (110..117).map(v).collect(),
        }),
        ..store(f, 0, 2, 0, None)
    };
    let err = check(&src, "f", slot).unwrap_err();
    assert!(
        matches!(&err, MidTvError::NotScalarizable { why, .. } if why.contains("poison")),
        "{err}"
    );
}

/// A read where only the `alloca` reaches: the fresh bytes are poison in
/// the source, refined by the initial zero.
#[test]
fn an_initial_zero_refines_an_undefined_read() {
    let text = "functy.0 = (i32, bool) -> (i32)\n\n\
        fn @f(functy.0) {\n\
        bb0(%0: i32, %1: bool):\n\
        \x20   %2 = alloca i32\n\
        \x20   condbr %1, bb1, bb2\n\
        bb1:\n\
        \x20   store i32 %0, ptr %2\n\
        \x20   br bb2\n\
        bb2:\n\
        \x20   %3 = load i32, ptr %2\n\
        \x20   ret %3\n\
        }\n";
    let src = module(text);
    let f = func(&src, "f");
    let slot = |init: Option<u32>, entry_value: u32| SroaSlot {
        alloca: v(2),
        fields: vec![SroaField {
            init: init.map(v),
            ..field(0, 4, Ty::I32)
        }],
        stores: vec![store(f, 1, 0, 0, None)],
        loads: vec![load(f, 3, 0, 101)],
        params: vec![SroaParam {
            block: b(2),
            field: 0,
            value: v(101),
            incoming: vec![incoming(0, 1, entry_value), incoming(1, 0, 0)],
        }],
    };
    let target = check(&src, "f", slot(Some(100), 100)).unwrap_or_else(|e| panic!("{e}"));
    assert!(matches!(
        &target.blocks[0].body[1],
        n if n.results == [v(100)]
            && n.inst == Inst::Const { ty: Ty::I32, value: Constant::Int(0) }
    ));
    assert_promoted_and_equivalent(&src, "f", &target, 2);
    // Without it, the path from the entry reads fresh bytes.
    let err = check(&src, "f", slot(None, 100)).unwrap_err();
    assert_unique_store_refused(&err, "undefined read");
    // A float field has no integer zero.
    let float = module(
        &text
            .replace(
                "store i32 %0",
                "%9 = sitofp i32 %0 to f32\n    store f32 %9",
            )
            .replace("load i32", "load f32"),
    );
    let f = func(&float, "f");
    let err = check(
        &float,
        "f",
        SroaSlot {
            alloca: v(2),
            fields: vec![SroaField {
                init: Some(v(100)),
                ..field(0, 4, Ty::F32)
            }],
            stores: vec![store(f, 1, 0, 0, None)],
            loads: vec![load(f, 3, 0, 101)],
            params: vec![SroaParam {
                block: b(2),
                field: 0,
                value: v(101),
                incoming: vec![incoming(0, 1, 100), incoming(1, 0, 9)],
            }],
        },
    )
    .unwrap_err();
    assert!(
        matches!(&err, MidTvError::NotScalarizable { why, .. } if why.contains("integer zero")),
        "{err}"
    );
}

fn assert_unique_store_refused(err: &MidTvError, needle: &str) {
    assert!(
        matches!(err, MidTvError::NoUniqueReachingStore { why, .. } if why.contains(needle)),
        "{err}"
    );
}

#[test]
fn negative_control_an_undefined_read_is_refused() {
    // Field 1 is read before anything writes it.
    let text = DIAMOND.replace(
        "    store i32 %6, ptr %4\n    %7 = load i32, ptr %4\n",
        "    %7 = load i32, ptr %4\n    store i32 %6, ptr %4\n",
    );
    let src = module(&text);
    let f = func(&src, "f");
    let mut slot = diamond_slot(f);
    slot.loads[1] = load(f, 7, 1, 0);
    slot.stores[2] = store(f, 3, 0, 1, None);
    let err = check(&src, "f", slot).unwrap_err();
    assert_unique_store_refused(&err, "undefined read");
}

#[test]
fn negative_control_a_wrong_reaching_value_is_refused() {
    let src = module(DIAMOND);
    let f = func(&src, "f");
    // The join's value is not the entry's store alone.
    let mut slot = diamond_slot(f);
    slot.loads[0] = load(f, 6, 0, 0);
    slot.params.clear();
    let err = check(&src, "f", slot).unwrap_err();
    assert_unique_store_refused(&err, "another store");
}

#[test]
fn negative_control_a_wrong_or_missing_incoming_value_is_refused() {
    let src = module(DIAMOND);
    let f = func(&src, "f");
    let mut wrong = diamond_slot(f);
    wrong.params[0].incoming = vec![incoming(1, 0, 0), incoming(2, 0, 0)];
    let err = check(&src, "f", wrong).unwrap_err();
    assert_unique_store_refused(&err, "another store");

    let mut missing = diamond_slot(f);
    missing.params[0].incoming.pop();
    let err = check(&src, "f", missing).unwrap_err();
    assert!(
        matches!(err, MidTvError::NotScalarizable { why, .. } if why.contains("passes no value")),
        "{err}"
    );

    // The loop's back edge must carry the body's store, not the entry's.
    let src = module(LOOP);
    let f = func(&src, "f");
    let mut stale = loop_slot(f);
    stale.params[0].incoming[1] = incoming(2, 0, 3);
    let err = check(&src, "f", stale).unwrap_err();
    assert_unique_store_refused(&err, "");
}

#[test]
fn negative_control_a_mixed_width_or_partial_overlap_is_refused() {
    let wide = "functy.0 = (i64) -> (i32)\n\n\
        fn @f(functy.0) {\n\
        bb0(%0: i64):\n\
        \x20   %1 = alloca i64\n\
        \x20   store i64 %0, ptr %1\n\
        \x20   %2 = load i32, ptr %1\n\
        \x20   ret %2\n\
        }\n";
    let src = module(wide);
    let f = func(&src, "f");
    // A load of part of the word is promoted only as a part of a field
    // carried as the word's unsigned integer, through its own extraction:
    // not as a field of its own width, not under a signed carrier, and not
    // as a plain copy of the word.
    for (carrier, extract, needle) in [
        (Ty::I32, vec![], "exactly its field"),
        (Ty::I64, vec![v(101)], "unsigned integer"),
        (Ty::U64, vec![], "too few values"),
    ] {
        let size = if carrier == Ty::I32 { 4 } else { 8 };
        let slot = SroaSlot {
            alloca: v(1),
            fields: vec![field(0, size, carrier)],
            stores: vec![store(f, 0, 0, 0, if size == 8 { Some(100) } else { None })],
            loads: vec![SroaLoad {
                extract,
                ..load(f, 2, 0, if size == 8 { 100 } else { 0 })
            }],
            params: vec![],
        };
        let err = check(&src, "f", slot).unwrap_err();
        assert!(
            matches!(err, MidTvError::NotScalarizable { why, .. } if why.contains(needle)),
            "{needle}: {err}"
        );
    }
    // With its extraction it is the word's low half.
    let slot = SroaSlot {
        alloca: v(1),
        fields: vec![field(0, 8, Ty::U64)],
        stores: vec![store(f, 0, 0, 0, Some(100))],
        loads: vec![SroaLoad {
            extract: vec![v(101)],
            ..load(f, 2, 0, 100)
        }],
        params: vec![],
    };
    let target = check(&src, "f", slot).unwrap_or_else(|e| panic!("{e}"));
    assert_promoted_and_equivalent(&src, "f", &target, 1);
    let overlap = "functy.0 = (i32) -> (i32)\n\n\
        fn @f(functy.0) {\n\
        bb0(%0: i32):\n\
        \x20   %1 = alloca i64\n\
        \x20   %2 = const i32 2\n\
        \x20   %3 = gep inbounds u8, ptr %1, %2\n\
        \x20   store i32 %0, ptr %1\n\
        \x20   store i32 %0, ptr %3\n\
        \x20   %4 = load i32, ptr %1\n\
        \x20   ret %4\n\
        }\n";
    let src = module(overlap);
    let f = func(&src, "f");
    let slot = SroaSlot {
        alloca: v(1),
        fields: vec![field(0, 4, Ty::I32), field(2, 4, Ty::I32)],
        stores: vec![store(f, 0, 0, 0, None), store(f, 0, 1, 1, None)],
        loads: vec![load(f, 4, 0, 0)],
        params: vec![],
    };
    let err = check(&src, "f", slot).unwrap_err();
    assert!(
        matches!(err, MidTvError::NotScalarizable { why, .. } if why.contains("overlap")),
        "{err}"
    );
}

/// The one-field slot of `%1` in `text`: a store of `%0` and a load `%2`.
fn single(text: &str) -> Result<Function, MidTvError> {
    let src = module(text);
    let f = func(&src, "f");
    let slot = SroaSlot {
        alloca: v(1),
        fields: vec![field(0, 4, Ty::I32)],
        stores: vec![store(f, 0, 0, 0, None)],
        loads: vec![load(f, 2, 0, 0)],
        params: vec![],
    };
    check(&src, "f", slot)
}

const SINGLE: &str = "functy.0 = (i32) -> (i32)\n\nfuncty.1 = (ptr) -> ()\n\n\
    fn @f(functy.0) {\n\
    bb0(%0: i32):\n\
    \x20   %1 = alloca i32\n\
    \x20   store i32 %0, ptr %1\n\
    \x20   %2 = load i32, ptr %1\n\
    \x20   ret %2\n\
    }\n\n\
    fn @g(functy.1) {\n\
    }\n";

#[test]
fn negative_control_an_observable_slot_is_refused() {
    single(SINGLE).unwrap_or_else(|e| panic!("{e}"));
    let observed = [
        // volatile and atomic accesses
        SINGLE.replace("%2 = load i32", "%2 = volatile load i32"),
        SINGLE.replace(
            "    %2 = load i32, ptr %1\n",
            "    %2 = load i32, ptr %1\n    %3 = atomic_load seq_cst i32, ptr %1\n",
        ),
        // an escape through a call, address bits, a stored address
        SINGLE.replace(
            "    %2 = load i32, ptr %1\n",
            "    %2 = load i32, ptr %1\n    call @func.1(%1)\n",
        ),
        SINGLE.replace(
            "    %2 = load i32, ptr %1\n",
            "    %2 = load i32, ptr %1\n    %3 = ptrtoint ptr %1 to i32\n",
        ),
        SINGLE.replace(
            "    %2 = load i32, ptr %1\n",
            "    %2 = load i32, ptr %1\n    %3 = alloca ptr\n    store ptr %1, ptr %3\n",
        ),
    ];
    for text in observed {
        let err = single(&text).unwrap_err();
        assert!(
            matches!(err, MidTvError::SlotObservable { .. }),
            "{text}\n{err}"
        );
    }
}

#[test]
fn negative_control_a_conversion_of_a_possible_poison_value_is_refused() {
    // The stored value is a load from another slot (it may be poison); a
    // `bitcast` of it would fault where the source only moves it.
    let text = "functy.0 = (u32) -> (i32)\n\n\
        fn @f(functy.0) {\n\
        bb0(%0: u32):\n\
        \x20   %1 = alloca i32\n\
        \x20   %3 = alloca u32\n\
        \x20   %4 = load u32, ptr %3\n\
        \x20   store u32 %4, ptr %1\n\
        \x20   %2 = load i32, ptr %1\n\
        \x20   ret %2\n\
        }\n";
    let src = module(text);
    let f = func(&src, "f");
    let slot = SroaSlot {
        alloca: v(1),
        fields: vec![field(0, 4, Ty::U32)],
        stores: vec![store(f, 0, 0, 0, None)],
        loads: vec![load(f, 2, 0, 4)],
        params: vec![],
    };
    let err = check(&src, "f", slot).unwrap_err();
    assert!(
        matches!(err, MidTvError::NotForwardable { why, .. } if why.contains("poison")),
        "{err}"
    );
    // The same view of a parameter (never poison) is accepted.
    let ok = text.replace("    %4 = load u32, ptr %3\n", "    %4 = copy u32 %0\n");
    let src = module(&ok);
    let f = func(&src, "f");
    let slot = SroaSlot {
        alloca: v(1),
        fields: vec![field(0, 4, Ty::U32)],
        stores: vec![store(f, 0, 0, 0, None)],
        loads: vec![load(f, 2, 0, 4)],
        params: vec![],
    };
    check(&src, "f", slot).unwrap_or_else(|e| panic!("{e}"));
}

#[test]
fn negative_control_a_stored_undef_is_refused() {
    let text = SINGLE.replace(
        "    store i32 %0, ptr %1\n",
        "    %5 = undef i32\n    store i32 %5, ptr %1\n",
    );
    let src = module(&text);
    let f = func(&src, "f");
    let slot = SroaSlot {
        alloca: v(1),
        fields: vec![field(0, 4, Ty::I32)],
        stores: vec![store(f, 0, 0, 0, None)],
        loads: vec![load(f, 2, 0, 5)],
        params: vec![],
    };
    let err = check(&src, "f", slot).unwrap_err();
    assert!(
        matches!(err, MidTvError::NotScalarizable { why, .. } if why.contains("undef")),
        "{err}"
    );
}

#[test]
fn negative_control_an_irreducible_cfg_is_refused() {
    // bb1 and bb2 enter each other, and the entry enters both.
    let text = "functy.0 = (i32, bool) -> (i32)\n\n\
        fn @f(functy.0) {\n\
        bb0(%0: i32, %3: bool):\n\
        \x20   %1 = alloca i32\n\
        \x20   store i32 %0, ptr %1\n\
        \x20   condbr %3, bb1, bb2\n\
        bb1:\n\
        \x20   %2 = load i32, ptr %1\n\
        \x20   condbr %3, bb2, bb3\n\
        bb2:\n\
        \x20   br bb1\n\
        bb3:\n\
        \x20   ret %2\n\
        }\n";
    let src = module(text);
    let f = func(&src, "f");
    let slot = SroaSlot {
        alloca: v(1),
        fields: vec![field(0, 4, Ty::I32)],
        stores: vec![store(f, 0, 0, 0, None)],
        loads: vec![load(f, 2, 0, 0)],
        params: vec![],
    };
    let err = check(&src, "f", slot).unwrap_err();
    assert!(
        matches!(err, MidTvError::NotScalarizable { why, .. } if why.contains("irreducible")),
        "{err}"
    );
}

#[test]
fn negative_control_a_parameter_on_the_entry_or_an_unrewritten_access_is_refused() {
    let src = module(LOOP);
    let f = func(&src, "f");
    let mut entry = loop_slot(f);
    entry.params[0].block = b(0);
    let err = check(&src, "f", entry).unwrap_err();
    assert!(
        matches!(err, MidTvError::NotScalarizable { why, .. } if why.contains("entry")),
        "{err}"
    );
    let mut partial = loop_slot(f);
    partial.loads.pop();
    let err = check(&src, "f", partial).unwrap_err();
    assert!(
        matches!(err, MidTvError::NotScalarizable { why, .. } if why.contains("not rewritten")),
        "{err}"
    );
}

#[test]
fn negative_control_a_target_beyond_the_rewrite_is_refused() {
    let src = module(DIAMOND);
    let f = func(&src, "f");
    let witness = SroaWitness {
        slots: vec![diamond_slot(f)],
    };
    let (mut target, _) = rebuild_sroa(&src, 32, f, &witness).unwrap();
    // Pass the wrong value on one edge, behind the checker's back.
    let pred = target.blocks.iter_mut().find(|bl| bl.id == b(2)).unwrap();
    let Inst::Br { args, .. } = &mut pred.body.last_mut().unwrap().inst else {
        unreachable!()
    };
    args[0] = v(1);
    let err = check_pass(&src, 32, f, &target, &PassWitness::Sroa(witness)).unwrap_err();
    assert!(matches!(err, MidTvError::TargetDiffers { .. }), "{err}");
}

#[test]
fn negative_control_a_refined_access_or_carrier_is_refused() {
    // A refinement is not a carrier type and a refined access has no layout
    // the checker models: the slot is left alone.
    let header = "type ty.0 = i32\n\npred pred.0 = top\n\n";
    let read = format!(
        "{header}{}",
        SINGLE
            .replace(
                "functy.0 = (i32) -> (i32)",
                "functy.0 = (i32) -> (refine<ty.0, pred.0>)"
            )
            .replace("%2 = load i32", "%2 = load refine<ty.0, pred.0>")
    );
    let written = format!(
        "{header}{}",
        SINGLE
            .replace(
                "functy.0 = (i32) -> (i32)",
                "functy.0 = (refine<ty.0, pred.0>) -> (i32)"
            )
            .replace("bb0(%0: i32)", "bb0(%0: refine<ty.0, pred.0>)")
            .replace("store i32 %0", "store refine<ty.0, pred.0> %0")
    );
    for text in [&read, &written] {
        let src = module(text);
        let f = func(&src, "f");
        for carrier in [
            Ty::I32,
            Ty::Refine(trust_ir::TyId::new(0), trust_ir::PredId::new(0)),
        ] {
            let slot = SroaSlot {
                alloca: v(1),
                fields: vec![field(0, 4, carrier.clone())],
                stores: vec![store(f, 0, 0, 0, None)],
                loads: vec![load(f, 2, 0, 0)],
                params: vec![],
            };
            let err = check(&src, "f", slot)
                .expect_err(&format!("{carrier:?}: a refined slot was promoted\n{text}"));
            assert!(
                matches!(
                    err,
                    MidTvError::SlotObservable { .. }
                        | MidTvError::NotScalarizable { .. }
                        | MidTvError::NotForwardable { .. }
                ),
                "{carrier:?}\n{text}\n{err}"
            );
        }
    }
}

// ---------------------------------------------------------------------------
// A `bool` field also accessed as a one-byte integer (round 15, provisional)
// ---------------------------------------------------------------------------

/// One byte written as the low byte of the argument (so 2..=255 occur) and
/// read as `bool` and as `i8`, then written as a `bool` and read as `i8`:
/// the bridge's whole-lane copy of a record's `bool` field
/// (`RangeInclusive::exhausted`) reads it as `i8`.
const BOOL_BYTE: &str = "functy.0 = (u32) -> (u32)\n\n\
    fn @f(functy.0) {\n\
    bb0(%0: u32):\n\
    \x20   %1 = alloca i8\n\
    \x20   %2 = trunc u32 %0 to i8\n\
    \x20   store i8 %2, ptr %1\n\
    \x20   %3 = load bool, ptr %1\n\
    \x20   %4 = load i8, ptr %1\n\
    \x20   %5 = const u32 100\n\
    \x20   %6 = icmp ult u32 %0, %5\n\
    \x20   store bool %6, ptr %1\n\
    \x20   %7 = load i8, ptr %1\n\
    \x20   %8 = zext bool %3 to u32\n\
    \x20   %9 = sext i8 %4 to u32\n\
    \x20   %10 = sext i8 %7 to u32\n\
    \x20   %11 = const u32 8\n\
    \x20   %12 = shl u32 %9, %11\n\
    \x20   %13 = const u32 16\n\
    \x20   %14 = shl u32 %10, %13\n\
    \x20   %15 = xor u32 %8, %12\n\
    \x20   %16 = xor u32 %15, %14\n\
    \x20   ret %16\n\
    }\n";

fn bool_byte_slot(f: &Function, carrier: Ty, zero: Option<u32>) -> SroaSlot {
    let mut read = load(f, 3, 0, 2);
    read.via = zero.map(v);
    SroaSlot {
        alloca: v(1),
        fields: vec![field(0, 1, carrier)],
        stores: vec![store(f, 0, 0, 0, None), store(f, 0, 1, 0, Some(101))],
        loads: vec![read, load(f, 4, 0, 2), load(f, 7, 0, 101)],
        params: vec![],
    }
}

#[test]
fn a_bool_field_read_as_a_byte_is_carried_as_the_byte() {
    let src = module(BOOL_BYTE);
    let f = func(&src, "f");
    let target =
        check(&src, "f", bool_byte_slot(f, Ty::I8, Some(100))).unwrap_or_else(|e| panic!("{e}"));
    let body = &target.blocks[0].body;
    // The bool store is its `zext`, the bool read the nonzero test.
    assert!(body.iter().any(|n| matches!(
        &n.inst,
        Inst::Cast {
            op: CastOp::ZExt,
            src_ty: Ty::Bool,
            ..
        }
    )));
    assert!(body.iter().any(|n| matches!(
        &n.inst,
        Inst::ICmp {
            op: ICmpOp::Ne,
            ty: Ty::I8,
            ..
        }
    )));
    assert_promoted_and_equivalent(&src, "f", &target, 1);
}

#[test]
fn a_bool_view_of_a_byte_off_its_rule_is_refused() {
    let src = module(BOOL_BYTE);
    let f = func(&src, "f");
    // The nonzero test names no fresh zero.
    assert!(check(&src, "f", bool_byte_slot(f, Ty::I8, None)).is_err());
    // A zero that is not fresh.
    assert!(check(&src, "f", bool_byte_slot(f, Ty::I8, Some(2))).is_err());
    // A carrier of another width.
    assert!(check(&src, "f", bool_byte_slot(f, Ty::U16, Some(100))).is_err());
    // A byte some store may leave poison: the stored byte is a load of
    // another, fresh slot.
    let poison = module(&BOOL_BYTE.replace(
        "%2 = trunc u32 %0 to i8",
        "%20 = alloca i8\n\x20   %2 = load i8, ptr %20",
    ));
    let f = func(&poison, "f");
    assert!(matches!(
        check(&poison, "f", bool_byte_slot(f, Ty::I8, Some(100))),
        Err(MidTvError::NotForwardable { .. })
    ));
}

#[test]
fn a_bool_view_spelled_as_a_truncation_disagrees() {
    // `trunc` keeps the low bit: the byte 2 reads as `false`, where the
    // interpreter's `bool` load reads it as `true`. The checker rebuilds the
    // nonzero test, so such a target is not the claimed rewrite, and the
    // differential tells the two apart.
    let src = module(BOOL_BYTE);
    let f = func(&src, "f");
    let slot = bool_byte_slot(f, Ty::I8, Some(100));
    let witness = SroaWitness { slots: vec![slot] };
    let (mut target, _) = rebuild_sroa(&src, 32, f, &witness).expect("accepted");
    let body = &mut target.blocks[0].body;
    let at = body
        .iter()
        .position(|n| matches!(n.inst, Inst::ICmp { op: ICmpOp::Ne, .. }))
        .expect("the nonzero test");
    body[at].inst = Inst::Cast {
        op: CastOp::Trunc,
        src_ty: Ty::I8,
        dst_ty: Ty::Bool,
        operand: v(2),
    };
    assert!(matches!(
        check_pass(&src, 32, f, &target, &PassWitness::Sroa(witness)),
        Err(MidTvError::TargetDiffers { .. })
    ));
    let two = trust_ir::interpret::InterpretValue::int(Ty::U32, 2).expect("u32");
    let inputs = vec![vec![two]];
    let budget = DifferentialBudget::default();
    let (a, _) = run_samples(&src, f, &inputs, budget);
    let mut tgt = src.clone();
    tgt.functions[0] = target.clone();
    let (t, _) = run_samples(&tgt, &target, &inputs, budget);
    assert!(compare_samples(&a, &t).mismatch.is_some());
}

/// A loop that reloads the slot, steps the value and stores back a
/// `select` of the step and the reload (an iterator's index), through
/// `i32` views of a `u32` field: the store converts a value computed from a
/// read of the slot itself.
const RELOAD: &str = "functy.0 = (i32, i32) -> (i32)\n\n\
    fn @f(functy.0) {\n\
    bb0(%0: i32, %1: i32):\n\
    \x20   %2 = alloca u32\n\
    \x20   %3 = bitcast i32 %0 to u32\n\
    \x20   store u32 %3, ptr %2\n\
    \x20   %20 = const i32 0\n\
    \x20   br bb1(%20)\n\
    bb1(%4: i32):\n\
    \x20   %21 = const i32 7\n\
    \x20   %22 = and i32 %1, %21\n\
    \x20   %5 = icmp slt i32 %4, %22\n\
    \x20   condbr %5, bb2, bb3\n\
    bb2:\n\
    \x20   %6 = load i32, ptr %2\n\
    \x20   %7 = add i32 %6, %1\n\
    \x20   %12 = icmp slt i32 %7, %0\n\
    \x20   %13 = select i32 %12, %6, %7\n\
    \x20   store i32 %13, ptr %2\n\
    \x20   %8 = const i32 1\n\
    \x20   %9 = add i32 %4, %8\n\
    \x20   br bb1(%9)\n\
    bb3:\n\
    \x20   %10 = load i32, ptr %2\n\
    \x20   ret %10\n\
    }\n";

fn reload_slot(f: &Function) -> SroaSlot {
    SroaSlot {
        alloca: v(2),
        fields: vec![field(0, 4, Ty::U32)],
        stores: vec![store(f, 0, 0, 0, None), store(f, 2, 0, 0, Some(200))],
        loads: vec![load(f, 6, 0, 100), load(f, 10, 0, 100)],
        params: vec![SroaParam {
            block: b(1),
            field: 0,
            value: v(100),
            incoming: vec![incoming(0, 0, 3), incoming(2, 0, 200)],
        }],
    }
}

#[test]
fn a_store_of_a_value_computed_from_a_reload_of_the_slot_converts() {
    // Every value stored into the slot is a cast or a `select` of a step and
    // a read of the slot: by induction the field is never poison, so the
    // `bitcast` of the stored `select` cannot fault.
    let src = module(RELOAD);
    let f = func(&src, "f");
    let target = check(&src, "f", reload_slot(f)).unwrap_or_else(|e| panic!("{e}"));
    assert_promoted_and_equivalent(&src, "f", &target, 2);
}

#[test]
fn negative_control_a_reload_feeding_a_store_beside_a_possibly_poison_store_is_refused() {
    // The entry's store now writes a load of another slot (it may be
    // poison), so a read of the slot may be poison and the converted store of
    // the `select` over it is refused.
    let text = RELOAD.replace(
        "    %3 = bitcast i32 %0 to u32\n",
        "    %30 = alloca u32\n    %3 = load u32, ptr %30\n",
    );
    let src = module(&text);
    let f = func(&src, "f");
    let err = check(&src, "f", reload_slot(f)).unwrap_err();
    assert!(
        matches!(&err, MidTvError::NotScalarizable { why, .. } if why.contains("poison")),
        "{err}"
    );
}
