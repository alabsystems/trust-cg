// trust-cg-verify/trust_ir_mid_tv_addr_tests.rs - tests of the cleanup checkers
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Address folding is accepted for an integer chain that reads as a slot
//! plus an offset inside it, through a pointer one past the end and a
//! negative step, and refused for an offset at or past the end, a claimed
//! offset or base that the chain does not read as, a root that is no
//! allocation, a value that is no `inttoptr`, and an index that is not
//! fresh. Dead block parameters are removed when they compute nothing, and
//! refused when an instruction reads one, for the entry block, and for an
//! argument of another type. Block merging is accepted along a lone `br`
//! edge and as a forwarding along a lone `condbr` edge, and refused for a
//! block two edges enter, a claimed predecessor that is not the edge's, a
//! merge along a `condbr`, and an argument of another type. A field access
//! through a pointer becomes the load or store the lane reads it as (the
//! source run in the differential's view), and a value that is no field
//! access, a write whose result is used, a stored value of another type
//! than the lane's, an access over a record value and a name that is not
//! fresh are refused. Accepted rewrites agree with their sources in the
//! interpreter.
//!
//! The witness types (`AddrFoldWitness`, `DeadParamWitness`,
//! `BlockMergeWitness`, `FieldAccessWitness`, their elements and their
//! `PassWitness` variants) are
//! provisional surfaces pending the owner's sign-off
//! (`docs/wasm32_perf_roadmap.md`, "Pending owner sign-off").

use super::super::{
    DifferentialBudget, MidTvError, PassWitness, check_pass, compare_samples, interpretable,
    run_samples, seeded_inputs,
};
use super::*;

const HEADER: &str = "; TrustIr text format v1\nmodule \"addr\"\n\
                      target \"wasm32-unknown-unknown\" 4 little\n\n";

fn module(body: &str) -> Module {
    trust_ir::parser::parse_module(&format!("{HEADER}{body}"))
        .unwrap_or_else(|e| panic!("test module failed to parse: {e}\n{body}"))
}

fn f(m: &Module) -> &Function {
    m.functions.iter().find(|f| f.name == "f").expect("f")
}

fn v(n: u32) -> ValueId {
    ValueId::new(n)
}

fn b(n: u32) -> BlockId {
    BlockId::new(n)
}

fn check(m: &Module, w: &PassWitness) -> Result<Function, MidTvError> {
    let src = f(m);
    let (out, _) = match w {
        PassWitness::AddrFold(w) => rebuild_addr_fold(m, 32, src, w)?,
        PassWitness::DeadParam(w) => rebuild_dead_param(src, w)?,
        PassWitness::BlockMerge(w) => rebuild_block_merge(src, w)?,
        _ => unreachable!(),
    };
    check_pass(m, 32, src, &out, w)?;
    Ok(out)
}

fn agree(m: &Module, target: &Function) {
    let source = f(m);
    let inputs = seeded_inputs(m, source, 32, 64, 3).expect("scalar parameters");
    let (a, _) = run_samples(m, source, &inputs, DifferentialBudget::default());
    let (t, _) = run_samples(m, target, &inputs, DifferentialBudget::default());
    let report = compare_samples(&a, &t);
    assert!(report.mismatch.is_none(), "{:?}", report.mismatch);
    assert!(report.compared > 0, "some inputs are compared");
}

fn fold(value: u32, base: u32, offset: u64, index: Option<u32>) -> PassWitness {
    PassWitness::AddrFold(AddrFoldWitness {
        folds: vec![AddrFold {
            value: v(value),
            base: v(base),
            offset,
            index: index.map(v),
        }],
    })
}

/// The copy of an unrolled slice loop: the end pointer one past the slot,
/// stepped back by 8 twice through integer round trips.
const CHAIN: &str = "functy.0 = (u64) -> (u64)\n\n\
type ty.0 = u64\n\n\
fn @f(functy.0) {\n\
bb0(%0: u64):\n\
\x20   %1 = alloca [ty.0 x 3], align 8\n\
\x20   store u64 %0, ptr %1\n\
\x20   %2 = const i32 8\n\
\x20   %3 = gep inbounds u8, ptr %1, %2\n\
\x20   store u64 %0, ptr %3\n\
\x20   %4 = const i32 16\n\
\x20   %5 = gep inbounds u8, ptr %1, %4\n\
\x20   store u64 %0, ptr %5\n\
\x20   %6 = ptrtoint ptr %1 to i32\n\
\x20   %7 = const i32 24\n\
\x20   %8 = add i32 %6, %7\n\
\x20   %9 = inttoptr i32 %8 to ptr\n\
\x20   %10 = ptrtoptr ptr %9 to *const u64\n\
\x20   %11 = ptrtoptr *const u64 %10 to ptr\n\
\x20   %12 = ptrtoint ptr %11 to i32\n\
\x20   %13 = const i32 -8\n\
\x20   %14 = add i32 %12, %13\n\
\x20   %15 = inttoptr i32 %14 to ptr\n\
\x20   %16 = load u64, ptr %15\n\
\x20   %17 = ptrtoint ptr %15 to i32\n\
\x20   %18 = sub i32 %17, %2\n\
\x20   %19 = inttoptr i32 %18 to ptr\n\
\x20   %20 = load u64, ptr %19\n\
\x20   %21 = add u64 %16, %20\n\
\x20   ret %21\n\
}\n";

#[test]
fn a_chain_through_a_pointer_past_the_end_folds_to_the_slot() {
    let m = module(CHAIN);
    let w = PassWitness::AddrFold(AddrFoldWitness {
        folds: vec![
            AddrFold {
                value: v(15),
                base: v(1),
                offset: 16,
                index: Some(v(100)),
            },
            AddrFold {
                value: v(19),
                base: v(1),
                offset: 8,
                index: Some(v(101)),
            },
        ],
    });
    let out = check(&m, &w).expect("accepted");
    agree(&m, &out);
}

fn refused_fold(m: &Module, w: &PassWitness) {
    match check(m, w) {
        Err(MidTvError::NotAddressFold { .. } | MidTvError::OffsetOutOfBounds { .. }) => {}
        other => panic!("expected a refusal, got {other:?}"),
    }
}

#[test]
fn folds_off_the_chain_or_outside_the_slot_are_refused() {
    let m = module(CHAIN);
    // One past the end: not inside the allocation.
    refused_fold(&m, &fold(9, 1, 24, Some(100)));
    // Another offset or another base than the chain reads.
    refused_fold(&m, &fold(15, 1, 8, Some(100)));
    refused_fold(&m, &fold(15, 3, 8, Some(100)));
    // A zero offset that names an index, a nonzero one without.
    refused_fold(&m, &fold(15, 1, 16, None));
    // An index that is not fresh.
    refused_fold(&m, &fold(15, 1, 16, Some(2)));
    // A root that is no allocation: the entry parameter's bits.
    let p = module(
        "functy.0 = (ptr) -> (u64)\n\n\
fn @f(functy.0) {\n\
bb0(%0: ptr):\n\
\x20   %1 = ptrtoint ptr %0 to i32\n\
\x20   %2 = const i32 8\n\
\x20   %3 = add i32 %1, %2\n\
\x20   %4 = inttoptr i32 %3 to ptr\n\
\x20   %5 = load u64, ptr %4\n\
\x20   ret %5\n\
}\n",
    );
    refused_fold(&p, &fold(4, 0, 8, Some(100)));
}

#[test]
fn a_value_that_is_no_inttoptr_is_refused() {
    // `%4` is the slot's address bits, not an `inttoptr` of them.
    let m = module(
        "functy.0 = (u32) -> (u32)\n\n\
fn @f(functy.0) {\n\
bb0(%0: u32):\n\
\x20   %1 = const u32 0\n\
\x20   %2 = icmp eq u32 %0, %1\n\
\x20   condbr %2, bb1, bb2\n\
bb1:\n\
\x20   %3 = alloca u32, align 4\n\
\x20   store u32 %0, ptr %3\n\
\x20   %4 = ptrtoint ptr %3 to i32\n\
\x20   br bb2\n\
bb2:\n\
\x20   ret %0\n\
}\n",
    );
    refused_fold(&m, &fold(4, 3, 0, None));
}

#[test]
fn dead_parameters_go_with_their_arguments() {
    let m = module(
        "functy.0 = (u32) -> (u32)\n\n\
fn @f(functy.0) {\n\
bb0(%0: u32):\n\
\x20   %1 = const u32 1\n\
\x20   %2 = add u32 %0, %1\n\
\x20   br bb1(%2, %0)\n\
bb1(%3: u32, %4: u32):\n\
\x20   %5 = icmp ult u32 %4, %1\n\
\x20   condbr %5, bb2(%3), bb3\n\
bb2(%6: u32):\n\
\x20   br bb3\n\
bb3:\n\
\x20   ret %4\n\
}\n",
    );
    let w = PassWitness::DeadParam(DeadParamWitness {
        params: vec![
            DeadParam {
                block: b(1),
                param: v(3),
            },
            DeadParam {
                block: b(2),
                param: v(6),
            },
        ],
    });
    let out = check(&m, &w).expect("accepted");
    agree(&m, &out);
    // `%3` alone is still passed on to `%6`, which stays: refused.
    let w = PassWitness::DeadParam(DeadParamWitness {
        params: vec![DeadParam {
            block: b(1),
            param: v(3),
        }],
    });
    assert!(matches!(
        check(&m, &w),
        Err(MidTvError::NotDeadParam { .. })
    ));
    // `%4` is read.
    let w = PassWitness::DeadParam(DeadParamWitness {
        params: vec![DeadParam {
            block: b(1),
            param: v(4),
        }],
    });
    assert!(matches!(
        check(&m, &w),
        Err(MidTvError::NotDeadParam { .. })
    ));
    // The entry block's parameter.
    let w = PassWitness::DeadParam(DeadParamWitness {
        params: vec![DeadParam {
            block: b(0),
            param: v(0),
        }],
    });
    assert!(matches!(
        check(&m, &w),
        Err(MidTvError::NotDeadParam { .. })
    ));
}

#[test]
fn a_dead_parameter_bound_from_another_type_is_refused() {
    let m = module(
        "functy.0 = (u32) -> (u32)\n\n\
fn @f(functy.0) {\n\
bb0(%0: u32):\n\
\x20   %1 = bitcast u32 %0 to i32\n\
\x20   br bb1(%1)\n\
bb1(%2: u32):\n\
\x20   ret %0\n\
}\n",
    );
    let w = PassWitness::DeadParam(DeadParamWitness {
        params: vec![DeadParam {
            block: b(1),
            param: v(2),
        }],
    });
    assert!(matches!(
        check(&m, &w),
        Err(MidTvError::NotDeadParam { .. })
    ));
}

const MERGE: &str = "functy.0 = (u32) -> (u32)\n\n\
fn @f(functy.0) {\n\
bb0(%0: u32):\n\
\x20   %1 = const u32 3\n\
\x20   br bb1(%1)\n\
bb1(%2: u32):\n\
\x20   %3 = mul u32 %0, %2\n\
\x20   %4 = icmp ult u32 %3, %0\n\
\x20   condbr %4, bb2(%3), bb3\n\
bb2(%5: u32):\n\
\x20   %6 = add u32 %5, %1\n\
\x20   br bb4(%6)\n\
bb3:\n\
\x20   br bb4(%0)\n\
bb4(%7: u32):\n\
\x20   ret %7\n\
}\n";

fn merge(steps: &[(u32, Option<u32>)]) -> PassWitness {
    PassWitness::BlockMerge(BlockMergeWitness {
        merges: steps
            .iter()
            .map(|(block, into)| BlockMerge {
                block: b(*block),
                into: into.map(b),
            })
            .collect(),
    })
}

#[test]
fn blocks_merge_along_a_lone_br_and_forward_along_a_lone_condbr() {
    let m = module(MERGE);
    let out = check(&m, &merge(&[(1, Some(0)), (2, None)])).expect("accepted");
    assert_eq!(out.blocks.len(), 4);
    assert!(out.blocks.iter().all(|blk| blk.id != b(1)));
    agree(&m, &out);
}

#[test]
fn merges_off_a_lone_edge_are_refused() {
    let m = module(MERGE);
    let refused = |w: &PassWitness| {
        assert!(
            matches!(check(&m, w), Err(MidTvError::NotBlockMerge { .. })),
            "{w:?}"
        );
    };
    // Two edges enter `bb4`.
    refused(&merge(&[(4, None)]));
    // `bb2` is entered along a `condbr`: forwarding only.
    refused(&merge(&[(2, Some(1))]));
    // Another predecessor than the edge's.
    refused(&merge(&[(1, Some(3))]));
    // The entry block.
    refused(&merge(&[(0, None)]));
    // An argument of another type.
    let m2 = module(
        &MERGE
            .replace("%1 = const u32 3", "%1 = const i32 3")
            .replace("%6 = add u32 %5, %1", "%6 = add u32 %5, %5"),
    );
    assert!(matches!(
        check(&m2, &merge(&[(1, Some(0))])),
        Err(MidTvError::NotBlockMerge { .. })
    ));
}

/// A tuple slot written and read through the bridge's field accesses over
/// a pointer to it.
const FIELDS: &str = "functy.0 = (u32, u64) -> (u64)\n\n\
fn @f(functy.0) {\n\
bb0(%0: u32, %1: u64):\n\
\x20   %2 = alloca (u32, u64), align 8\n\
\x20   %3 = ptrtoptr ptr %2 to &mut (u32, u64)\n\
\x20   %4 = insertfield (u32, u64) %3, 0, %0\n\
\x20   %5 = insertfield (u32, u64) %3, 1, %1\n\
\x20   %6 = extractfield (u32, u64) %3, 1\n\
\x20   %7 = extractfield (u32, u64) %3, 0\n\
\x20   %8 = zext u32 %7 to u64\n\
\x20   %9 = add u64 %6, %8\n\
\x20   ret %9\n\
}\n";

fn access(rewrites: &[(u32, u32, u32)]) -> PassWitness {
    PassWitness::FieldAccess(FieldAccessWitness {
        rewrites: rewrites
            .iter()
            .map(|(value, index, address)| FieldAccess {
                value: v(*value),
                index: v(*index),
                address: v(*address),
            })
            .collect(),
    })
}

#[test]
fn field_accesses_through_a_pointer_become_loads_and_stores() {
    let m = module(FIELDS);
    let src = f(&m);
    let PassWitness::FieldAccess(w) =
        access(&[(4, 100, 101), (5, 102, 103), (6, 104, 105), (7, 106, 107)])
    else {
        unreachable!()
    };
    let (out, _) = rebuild_field_access(&m, src, &w).expect("accepted");
    // No field access is left: the target runs in the raw interpreter.
    assert!(
        !out.blocks
            .iter()
            .flat_map(|b| &b.body)
            .any(|n| matches!(n.inst, Inst::ExtractField { .. } | Inst::InsertField { .. }))
    );
    // The source runs in the differential's view of the lane's idioms.
    let view = interpretable(&m, src).expect("the source has lane idioms");
    let inputs = seeded_inputs(&m, src, 32, 64, 5).expect("scalar parameters");
    let (a, _) = run_samples(&m, &view, &inputs, DifferentialBudget::default());
    let (t, _) = run_samples(&m, &out, &inputs, DifferentialBudget::default());
    let report = compare_samples(&a, &t);
    assert!(report.mismatch.is_none(), "{:?}", report.mismatch);
    assert!(report.compared > 0);
}

#[test]
fn field_accesses_off_their_form_are_refused() {
    let m = module(FIELDS);
    let refused = |w: &PassWitness| {
        let PassWitness::FieldAccess(fw) = w else {
            unreachable!()
        };
        assert!(
            matches!(
                rebuild_field_access(&m, f(&m), fw),
                Err(MidTvError::NotFieldAccess { .. })
            ),
            "{w:?}"
        );
    };
    // Not a field access.
    refused(&access(&[(8, 100, 101)]));
    // A name that is not fresh.
    refused(&access(&[(6, 2, 101)]));
    // A write whose result is used.
    let m2 = module(&FIELDS.replace(
        "ret %9",
        "%10 = ptrtoptr &mut (u32, u64) %5 to ptr\n\x20   ret %9",
    ));
    let PassWitness::FieldAccess(w) = access(&[(5, 100, 101)]) else {
        unreachable!()
    };
    assert!(matches!(
        rebuild_field_access(&m2, f(&m2), &w),
        Err(MidTvError::NotFieldAccess { .. })
    ));
    // A stored value of another type than the lane's.
    let m3 = module(&FIELDS.replace(
        "%4 = insertfield (u32, u64) %3, 0, %0",
        "%20 = bitcast u32 %0 to i32\n\x20   %4 = insertfield (u32, u64) %3, 0, %20",
    ));
    let PassWitness::FieldAccess(w) = access(&[(4, 100, 101)]) else {
        unreachable!()
    };
    assert!(matches!(
        rebuild_field_access(&m3, f(&m3), &w),
        Err(MidTvError::NotFieldAccess { .. })
    ));
    // A field access over a value of the record type (not through a pointer).
    let m4 = module(
        "functy.0 = (u32, u64) -> (u64)\n\n\
fn @f(functy.0) {\n\
bb0(%0: u32, %1: u64):\n\
\x20   %2 = make_aggregate (u32, u64) (%0, %1)\n\
\x20   %3 = extractfield (u32, u64) %2, 1\n\
\x20   ret %3\n\
}\n",
    );
    let PassWitness::FieldAccess(w) = access(&[(3, 100, 101)]) else {
        unreachable!()
    };
    assert!(matches!(
        rebuild_field_access(&m4, f(&m4), &w),
        Err(MidTvError::NotFieldAccess { .. })
    ));
}
