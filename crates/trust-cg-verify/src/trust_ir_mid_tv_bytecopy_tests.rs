// trust-cg-verify/trust_ir_mid_tv_bytecopy_tests.rs - tests of the byte-copy checker
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! The packed-struct shape the rustc bridge emits (four typed stores into a
//! 15-byte frame slot, then fifteen byte loads and stores copying it into
//! another allocation) becomes one `memcopy` (a run), and then the four
//! stores made into the destination (a forward); each step agrees with the
//! source in the reference interpreter. Refused (the negative controls):
//! for a run, overlapping ranges, two parameter bases, a loaded byte with
//! another use, an instruction with an effect inside the run, a gap in the
//! copied bytes, a destination that changes base, a run not ending with a
//! store, and a count that is not fresh; for a forward, stores that do not
//! cover the copied bytes, another write into the slot before the copy, a
//! slot whose address escapes, a named store into another allocation, a
//! source that is not a frame slot, and a name that is not fresh. A target
//! that stores a field one byte off is not the claimed rewrite, and the
//! differential tells it apart.
//!
//! The witness types (`ByteCopyWitness`, `ByteCopyRun`, `ByteCopyForward`,
//! `ForwardedStore` and the `PassWitness` variant) are provisional surfaces
//! pending the owner's sign-off (`docs/wasm32_perf_roadmap.md`, "Pending
//! owner sign-off").

use super::super::{
    DifferentialBudget, MidTvError, PassWitness, check_pass, compare_samples, interpretable,
    interpretable_module, run_samples, seeded_inputs,
};
use super::*;

const HEADER: &str = "; TrustIr text format v1\nmodule \"bytecopy\"\n\
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

/// The four field stores into the 15-byte slot `%2` (`a: u8` at 0, `x: f64`
/// at 1, `b: u16` at 9, `y: f32` at 11).
const FIELDS: &str = "\x20   %4 = trunc u32 %0 to u8\n\
\x20   store u8 %4, ptr %2\n\
\x20   %5 = const usize 1\n\
\x20   %6 = gep u8, ptr %2, %5\n\
\x20   store f64 %1, ptr %6\n\
\x20   %7 = const usize 9\n\
\x20   %8 = gep u8, ptr %2, %7\n\
\x20   %9 = trunc u32 %0 to u16\n\
\x20   store u16 %9, ptr %8\n\
\x20   %10 = const usize 11\n\
\x20   %11 = gep u8, ptr %2, %10\n\
\x20   %12 = fptrunc f64 %1 to f32\n\
\x20   store f32 %12, ptr %11\n";

/// Byte `i` of the copy: `src[from + i]` into `dst[to + i]`.
fn byte(i: u32, src: &str, from: u32, dst: &str, to: u32) -> String {
    let n = 100 + 5 * i;
    format!(
        "\x20   %{n} = const usize {s}\n\x20   %{a} = gep u8, ptr {src}, %{n}\n\
         \x20   %{l} = load i8, ptr %{a}\n\x20   %{k} = const usize {d}\n\
         \x20   %{b} = gep u8, ptr {dst}, %{k}\n\x20   store i8 %{l}, ptr %{b}\n",
        s = from + i,
        d = to + i,
        a = n + 1,
        l = n + 2,
        k = n + 3,
        b = n + 4,
    )
}

/// `f(a, x)`: the fields into `%2`, the copy `bytes` into `%3` (16 bytes,
/// its last byte set to 0x5a first), and the result `%3`'s two words xored.
fn program(fields: &str, bytes: &str, extra: &str) -> String {
    format!(
        "type ty.0 = u8\n\n\
functy.0 = (u32, f64) -> (u64)\n\n\
fn @f(functy.0) {{\n\
bb0(%0: u32, %1: f64):\n\
\x20   %2 = alloca [ty.0 x 15], align 1\n\
\x20   %3 = alloca [ty.0 x 16], align 8\n\
\x20   %13 = const u8 90\n\
\x20   %14 = const usize 15\n\
\x20   %15 = gep u8, ptr %3, %14\n\
\x20   store u8 %13, ptr %15\n\
{fields}{bytes}{extra}\
\x20   %20 = load u64, ptr %3\n\
\x20   %21 = const usize 8\n\
\x20   %22 = gep u8, ptr %3, %21\n\
\x20   %23 = load u64, ptr %22\n\
\x20   %24 = xor u64 %20, %23\n\
\x20   ret %24\n\
}}\n"
    )
}

fn copy_all() -> String {
    (0..15).map(|i| byte(i, "%2", 0, "%3", 0)).collect()
}

/// `(first, last)`: the first byte load and the last byte store of the
/// entry block.
fn run_bounds(func: &Function) -> (usize, usize) {
    let body = &func.blocks[0].body;
    let first = body
        .iter()
        .position(|n| matches!(&n.inst, Inst::Load { ty: Ty::I8, .. }))
        .expect("a byte load");
    let last = body
        .iter()
        .rposition(|n| matches!(&n.inst, Inst::Store { ty: Ty::I8, .. }))
        .expect("a byte store");
    (first, last)
}

fn run_witness(func: &Function, count: u32) -> ByteCopyRun {
    let (first, last) = run_bounds(func);
    ByteCopyRun {
        block: func.blocks[0].id,
        first,
        last,
        count: v(count),
    }
}

/// The forward of the `memcopy` the run leaves, naming the four field
/// stores, with fresh values from 600.
fn forward_witness(func: &Function) -> ByteCopyForward {
    let (first, last) = run_bounds(func);
    let body = &func.blocks[0].body;
    let removed = body[first..=last]
        .iter()
        .filter(|n| matches!(n.inst, Inst::Load { .. } | Inst::Store { .. }))
        .count();
    // The run keeps its inert instructions and puts the count and the copy
    // at `last`.
    let copy = last + 1 - removed + 1;
    let stores: Vec<usize> = body[..first]
        .iter()
        .enumerate()
        .filter(|(_, n)| {
            matches!(&n.inst, Inst::Store { value, .. } if [v(4), v(1), v(9), v(12)].contains(value))
        })
        .map(|(i, _)| i)
        .collect();
    assert_eq!(stores.len(), 4, "the four field stores");
    ByteCopyForward {
        block: func.blocks[0].id,
        copy,
        stores: stores
            .iter()
            .enumerate()
            .map(|(k, &store)| ForwardedStore {
                store,
                offset: v(600 + 2 * k as u32),
                address: v(601 + 2 * k as u32),
            })
            .collect(),
    }
}

/// The source and `out` run in the differential's view (plain loads and
/// stores at alignment 1, as the wasm32 lane executes them).
fn runs(
    m: &Module,
    out: &Function,
) -> (
    Vec<super::super::SampleOutcome>,
    Vec<super::super::SampleOutcome>,
) {
    let src = f(m);
    let view = interpretable_module(m);
    let inputs = seeded_inputs(m, src, 32, 48, 11).expect("scalar parameters");
    let sv = interpretable(&view, src).unwrap_or_else(|| src.clone());
    let tv = interpretable(&view, out).unwrap_or_else(|| out.clone());
    let (a, _) = run_samples(&view, &sv, &inputs, DifferentialBudget::default());
    let (t, _) = run_samples(&view, &tv, &inputs, DifferentialBudget::default());
    (a, t)
}

fn agrees(m: &Module, out: &Function) {
    let (a, t) = runs(m, out);
    let report = compare_samples(&a, &t);
    assert!(report.mismatch.is_none(), "{:?}", report.mismatch);
    assert!(report.compared > 0, "some inputs are compared");
}

fn refused(m: &Module, w: &ByteCopyWitness) {
    assert!(
        matches!(
            rebuild_byte_copy(m, f(m), w),
            Err(MidTvError::NotByteCopy { .. })
        ),
        "{w:?}"
    );
}

#[test]
fn a_run_becomes_memcopy_and_agrees() {
    let m = module(&program(FIELDS, &copy_all(), ""));
    let src = f(&m);
    let w = ByteCopyWitness {
        runs: vec![run_witness(src, 500)],
        forwards: Vec::new(),
    };
    let (out, verdict) = rebuild_byte_copy(&m, src, &w).expect("accepted");
    assert_eq!(verdict.refinements, 1);
    check_pass(&m, 32, src, &out, &PassWitness::ByteCopy(w)).expect("check_pass");
    let body = &out.blocks[0].body;
    assert!(
        !body
            .iter()
            .any(|n| matches!(&n.inst, Inst::Load { ty: Ty::I8, .. }))
    );
    assert!(
        body.iter()
            .any(|n| matches!(n.inst, Inst::MemCopy { overlap: false, .. }))
    );
    agrees(&m, &out);
}

#[test]
fn a_forward_stores_the_fields_into_the_destination_and_agrees() {
    let m = module(&program(FIELDS, &copy_all(), ""));
    let src = f(&m);
    let w = ByteCopyWitness {
        runs: vec![run_witness(src, 500)],
        forwards: vec![forward_witness(src)],
    };
    let (out, verdict) = rebuild_byte_copy(&m, src, &w).expect("accepted");
    assert_eq!((verdict.exact, verdict.refinements), (1, 1));
    check_pass(&m, 32, src, &out, &PassWitness::ByteCopy(w)).expect("check_pass");
    let body = &out.blocks[0].body;
    assert!(!body.iter().any(|n| matches!(n.inst, Inst::MemCopy { .. })));
    let into_dst = body
        .iter()
        .filter(
            |n| matches!(&n.inst, Inst::Store { ptr, align: Some(1), .. } if ptr.index() >= 600),
        )
        .count();
    assert_eq!(into_dst, 4, "the four fields stored into the destination");
    agrees(&m, &out);
}

#[test]
fn runs_off_the_copy_form_are_refused() {
    let run_only = |m: &Module, count: u32| ByteCopyWitness {
        runs: vec![run_witness(f(m), count)],
        forwards: Vec::new(),
    };
    // The control.
    let m = module(&program(FIELDS, &copy_all(), ""));
    rebuild_byte_copy(&m, f(&m), &run_only(&m, 500)).expect("control");
    // Overlapping ranges of one slot: bytes 0..8 of %2 into 1..9.
    let overlap: String = (0..8).map(|i| byte(i, "%2", 0, "%2", 1)).collect();
    let m = module(&program(FIELDS, &overlap, ""));
    refused(&m, &run_only(&m, 500));
    // Two parameter bases (which may alias).
    let params: String = (0..4).map(|i| byte(i, "%0", 0, "%1", 0)).collect();
    let m = module(&format!(
        "functy.0 = (ptr, ptr) -> ()\n\nfn @f(functy.0) {{\nbb0(%0: ptr, %1: ptr):\n{params}\x20   ret\n}}\n"
    ));
    refused(&m, &run_only(&m, 500));
    // A loaded byte with another use.
    let m = module(&program(
        FIELDS,
        &copy_all(),
        "\x20   %30 = zext i8 %102 to u64\n",
    ));
    refused(&m, &run_only(&m, 500));
    // An instruction with an effect inside the run.
    let mut effect = copy_all();
    effect.insert_str(
        effect.find("\x20   %110").expect("byte 2"),
        "\x20   store u8 %13, ptr %3\n",
    );
    let m = module(&program(FIELDS, &effect, ""));
    refused(&m, &run_only(&m, 500));
    // A gap: bytes 0..4 and 5..9.
    let gap: String = (0..4)
        .chain(5..9)
        .map(|i| byte(i, "%2", 0, "%3", 0))
        .collect();
    let m = module(&program(FIELDS, &gap, ""));
    refused(&m, &run_only(&m, 500));
    // The destination changes base halfway.
    let switched: String = (0..4)
        .map(|i| byte(i, "%2", 0, "%3", 0))
        .chain((4..8).map(|i| byte(i, "%2", 0, "%2", 7)))
        .collect();
    let m = module(&program(FIELDS, &switched, ""));
    refused(&m, &run_only(&m, 500));
    let m = module(&program(FIELDS, &copy_all(), ""));
    // Not ending with a store.
    let mut short = run_only(&m, 500);
    short.runs[0].last -= 1;
    refused(&m, &short);
    // A count that is not fresh.
    refused(&m, &run_only(&m, 2));
}

#[test]
fn forwards_off_the_covered_form_are_refused() {
    let with = |m: &Module, edit: &dyn Fn(&mut ByteCopyForward)| {
        let src = f(m);
        let mut fwd = forward_witness(src);
        edit(&mut fwd);
        ByteCopyWitness {
            runs: vec![run_witness(src, 500)],
            forwards: vec![fwd],
        }
    };
    let m = module(&program(FIELDS, &copy_all(), ""));
    rebuild_byte_copy(&m, f(&m), &with(&m, &|_| {})).expect("control");
    // The named stores do not cover the copied bytes (the `u16` left out).
    refused(
        &m,
        &with(&m, &|fwd| {
            fwd.stores.remove(2);
        }),
    );
    // A named value that is not fresh.
    refused(&m, &with(&m, &|fwd| fwd.stores[0].offset = v(2)));
    // A named store into another allocation: the guard byte's store into %3.
    refused(&m, &with(&m, &|fwd| fwd.stores[0].store = 5));
    // Another write into the slot between the stores and the copy.
    let rewrite = format!("{FIELDS}\x20   store u8 %13, ptr %2\n");
    let m = module(&program(&rewrite, &copy_all(), ""));
    refused(&m, &with(&m, &|_| {}));
    // The slot's address escapes.
    let m = module(&program(
        FIELDS,
        &copy_all(),
        "\x20   %31 = ptrtoint ptr %2 to usize\n",
    ));
    refused(&m, &with(&m, &|_| {}));
    // A source that is not a frame slot: a copy out of a parameter.
    let m = module(
        "type ty.0 = u8\n\nfuncty.0 = (ptr) -> ()\n\nfn @f(functy.0) {\nbb0(%0: ptr):\n\
         \x20   %1 = alloca [ty.0 x 4], align 1\n\x20   %2 = const usize 4\n\
         \x20   memcopy ptr %1, ptr %0, %2\n\x20   ret\n}\n",
    );
    refused(
        &m,
        &ByteCopyWitness {
            runs: Vec::new(),
            forwards: vec![ByteCopyForward {
                block: f(&m).blocks[0].id,
                copy: 2,
                stores: Vec::new(),
            }],
        },
    );
}

#[test]
fn a_field_stored_one_byte_off_is_not_the_claimed_rewrite() {
    let m = module(&program(FIELDS, &copy_all(), ""));
    let src = f(&m);
    let w = ByteCopyWitness {
        runs: vec![run_witness(src, 500)],
        forwards: vec![forward_witness(src)],
    };
    let (mut out, _) = rebuild_byte_copy(&m, src, &w).expect("accepted");
    // The `f64` field's offset constant, 1, made 2.
    for node in out.blocks[0].body.iter_mut() {
        if node.results == [v(602)] {
            node.inst = Inst::Const {
                ty: Ty::Usize,
                value: Constant::Int(2),
            };
        }
    }
    assert!(matches!(
        check_pass(&m, 32, src, &out, &PassWitness::ByteCopy(w)),
        Err(MidTvError::TargetDiffers { .. })
    ));
    let (a, t) = runs(&m, &out);
    assert!(compare_samples(&a, &t).mismatch.is_some());
}
