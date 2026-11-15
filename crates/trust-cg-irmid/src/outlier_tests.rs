// trust-cg-irmid/outlier_tests.rs - the round-17 rewrites over the pipeline
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Over the wasm32 pipeline, each kept by its checker and compared by the
//! interpreter differential: `min_zip2`'s zip of a `k % 5`-element prefix
//! with a 4-element array (its length a pointer difference, its trip count
//! the minimum, its exit test `Zip::next`'s niche) loses its loop, its
//! arrays and its exit selects, leaving the four results LLVM computes; a
//! bit-serial CRC step over one byte becomes a load from a 256-entry table
//! (two steps in one function share it); and a `RangeInclusive` loop's
//! `switch` on its exhausted-flag `select` becomes a branch on the select's
//! condition. Controls: a bit loop xoring two constants keeps its branches,
//! a loop whose trip count the intervals do not bound stays a loop, and
//! neither the interval of an entry block's parameter nor a guard into the
//! entry block counts the edges back into the entry alone (the call enters
//! it too): the loop over `0..n` with `n` that parameter stays a loop, and a
//! `select` stays where only an edge into the entry fixes its condition; and
//! a loop whose header is the entry block, entered from outside only by an
//! unreachable block, has no preheader (the call enters the entry with any
//! arguments), so interval-bounded unrolling, full unrolling and the closed
//! form leave it a loop. The
//! pass names `bounded_unroll`, `select_branch` and `crc_table`, the rule
//! `pointer_difference` and the witness types are provisional surfaces
//! pending the owner's sign-off (`docs/wasm32_perf_roadmap.md`, "Pending
//! owner sign-off").

use trust_ir::{
    Constant, Function, Inst, InterpretOptions, InterpretValue, InterpretValueKind, Interpreter,
    Module, Ty,
};

use crate::{IrmidReport, MidConfig, PassStats, optimize_module};

const HEADER: &str = "; TrustIr text format v1\nmodule \"irmid\"\n\
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

fn stats(report: &IrmidReport, name: &str) -> PassStats {
    report
        .passes
        .iter()
        .find(|p| p.name == name)
        .cloned()
        .unwrap_or_default()
}

fn compared(report: &IrmidReport, name: &str) -> usize {
    report.tv.by_pass.get(name).map_or(0, |c| c.compared)
}

fn count(f: &Function, pred: impl Fn(&Inst) -> bool) -> usize {
    f.blocks
        .iter()
        .flat_map(|b| &b.body)
        .filter(|n| pred(&n.inst))
        .count()
}

/// Whether some block of `f` branches to a block before it in layout order
/// (a loop: every block the pipeline leaves is in reverse postorder).
fn loops_back(f: &Function) -> bool {
    f.blocks.iter().enumerate().any(|(i, b)| {
        b.body.last().is_some_and(|t| {
            t.inst
                .successor_edges()
                .iter()
                .any(|e| f.blocks[..=i].iter().any(|p| p.id == e.target))
        })
    })
}

/// `z(k)`: `a = [1u16, 2, 3, 4]`, `b = [10u64, 20, 30, 40]`, and
/// `acc = acc * 100 + a[i] + b[i]` over `zip(a[..k % 5], b)`, as the rustc
/// bridge leaves it once the `Zip`'s state is in values: the prefix's
/// length a difference of its end and start addresses, the trip count
/// their minimum, and the exit test `Zip::next`'s niche (`select` of the
/// element address and `null`, compared with zero).
const ZIP: &str = "type ty.0 = u16\n\n\
type ty.1 = u64\n\n\
functy.0 = (u32) -> (u32)\n\n\
fn @z(functy.0) {\n\
bb0(%1: u32):\n\
\x20   %47 = alloca [ty.0 x 4], align 2\n\
\x20   %48 = alloca [ty.1 x 4], align 8\n\
\x20   %64 = const u16 1\n\
\x20   store u16 %64, ptr %47\n\
\x20   %65 = const u16 2\n\
\x20   %66 = const i32 2\n\
\x20   %71 = gep inbounds u8, ptr %47, %66\n\
\x20   store u16 %65, ptr %71\n\
\x20   %72 = const u16 3\n\
\x20   %73 = const i32 4\n\
\x20   %78 = gep inbounds u8, ptr %47, %73\n\
\x20   store u16 %72, ptr %78\n\
\x20   %79 = const u16 4\n\
\x20   %80 = const i32 6\n\
\x20   %85 = gep inbounds u8, ptr %47, %80\n\
\x20   store u16 %79, ptr %85\n\
\x20   %86 = const u64 10\n\
\x20   store u64 %86, ptr %48\n\
\x20   %87 = const u64 20\n\
\x20   %88 = const i32 8\n\
\x20   %93 = gep inbounds u8, ptr %48, %88\n\
\x20   store u64 %87, ptr %93\n\
\x20   %94 = const u64 30\n\
\x20   %95 = const i32 16\n\
\x20   %100 = gep inbounds u8, ptr %48, %95\n\
\x20   store u64 %94, ptr %100\n\
\x20   %101 = const u64 40\n\
\x20   %102 = const i32 24\n\
\x20   %107 = gep inbounds u8, ptr %48, %102\n\
\x20   store u64 %101, ptr %107\n\
\x20   %108 = const u32 0\n\
\x20   %111 = const u32 5\n\
\x20   %110 = urem u32 %1, %111\n\
\x20   %173 = ptrtoptr ptr %47 to *mut u16\n\
\x20   %174 = ptrtoint *mut u16 %173 to i32\n\
\x20   %175 = bitcast u32 %110 to i32\n\
\x20   %176 = const i32 2\n\
\x20   %177 = mul i32 %175, %176\n\
\x20   %178 = add i32 %174, %177\n\
\x20   %179 = inttoptr i32 %178 to ptr\n\
\x20   %180 = ptrtoptr ptr %179 to *const u16\n\
\x20   %483 = ptrtoint *const u16 %180 to i32\n\
\x20   %481 = ptrtoptr ptr %47 to *const u16\n\
\x20   %485 = ptrtoint *const u16 %481 to i32\n\
\x20   %486 = sub i32 %483, %485\n\
\x20   %487 = const i32 2\n\
\x20   %488 = udiv i32 %486, %487\n\
\x20   %498 = bitcast i32 %488 to u32\n\
\x20   %228 = ptrtoint ptr %48 to i32\n\
\x20   %231 = const i32 32\n\
\x20   %232 = add i32 %228, %231\n\
\x20   %233 = inttoptr i32 %232 to ptr\n\
\x20   %509 = ptrtoint ptr %233 to i32\n\
\x20   %511 = ptrtoint ptr %48 to i32\n\
\x20   %512 = sub i32 %509, %511\n\
\x20   %513 = const i32 8\n\
\x20   %514 = udiv i32 %512, %513\n\
\x20   %524 = bitcast i32 %514 to u32\n\
\x20   %526 = icmp ult u32 %524, %498\n\
\x20   condbr %526, bb37, bb36\n\
bb36:\n\
\x20   br bb38(%498)\n\
bb37:\n\
\x20   br bb38(%524)\n\
bb38(%528: u32):\n\
\x20   %544 = const i32 0\n\
\x20   %547 = bitcast u32 %528 to i32\n\
\x20   br bb1(%108, %544)\n\
bb1(%369: u32, %557: i32):\n\
\x20   %385 = icmp ult i32 %557, %547\n\
\x20   %388 = ptrtoint ptr %47 to i32\n\
\x20   %390 = const i32 2\n\
\x20   %391 = mul i32 %557, %390\n\
\x20   %392 = add i32 %388, %391\n\
\x20   %393 = inttoptr i32 %392 to ptr\n\
\x20   %402 = ptrtoint ptr %48 to i32\n\
\x20   %404 = const i32 8\n\
\x20   %405 = mul i32 %557, %404\n\
\x20   %406 = add i32 %402, %405\n\
\x20   %407 = inttoptr i32 %406 to ptr\n\
\x20   %408 = const i32 1\n\
\x20   %409 = add i32 %557, %408\n\
\x20   %410 = select i32 %385, %409, %557\n\
\x20   %411 = const i32 0\n\
\x20   %412 = inttoptr i32 %411 to ptr\n\
\x20   %413 = select ptr %385, %393, %412\n\
\x20   %464 = ptrtoint ptr %413 to i32\n\
\x20   %467 = ptrtoint ptr %407 to i32\n\
\x20   %421 = inttoptr i32 %464 to ptr\n\
\x20   %422 = ptrtoint ptr %421 to u64\n\
\x20   %423 = const u64 0\n\
\x20   %425 = icmp eq u64 %422, %423\n\
\x20   %426 = trunc u64 %422 to i32\n\
\x20   %429 = const i32 1\n\
\x20   %430 = select i32 %425, %426, %429\n\
\x20   switch %430 [ 0: bb4 1: bb3 default: bb2 ]\n\
bb4:\n\
\x20   ret %369\n\
bb3:\n\
\x20   %465 = inttoptr i32 %464 to ptr\n\
\x20   %466 = inttoptr i32 %467 to ptr\n\
\x20   %437 = const u32 100\n\
\x20   %436 = mul u32 %369, %437\n\
\x20   %438 = load u16, ptr %465\n\
\x20   %439 = zext u16 %438 to u32\n\
\x20   %440 = add u32 %436, %439\n\
\x20   %441 = load u64, ptr %466\n\
\x20   %442 = trunc u64 %441 to u32\n\
\x20   %443 = add u32 %440, %442\n\
\x20   br bb1(%443, %410)\n\
bb2:\n\
\x20   %444 = const u32 0\n\
\x20   ret %444\n\
}\n";

#[test]
fn a_zip_over_a_bounded_prefix_loses_its_loop_and_its_arrays() {
    let m = module(ZIP);
    let (out, report) = optimize_module(&m, &MidConfig::wasm32());
    assert_eq!(report.rollback_count(), 0, "{:?}", report.rollbacks);
    for pass in ["bounded_unroll", "select_branch"] {
        assert!(stats(&report, pass).functions_changed >= 1, "{pass}");
        assert!(compared(&report, pass) >= 1, "{pass} compared");
    }
    assert!(
        report
            .passes
            .iter()
            .find(|p| p.name == "simplify")
            .is_some_and(|p| p.functions_changed >= 1),
        "the pointer differences are simplified"
    );
    let z = func(&out, "z");
    assert!(!loops_back(z), "{z}");
    assert_eq!(count(z, |i| matches!(i, Inst::Alloca { .. })), 0, "{z}");
    assert_eq!(count(z, |i| matches!(i, Inst::Load { .. })), 0, "{z}");
    assert_eq!(count(z, |i| matches!(i, Inst::Select { .. })), 0, "{z}");
    // The four results LLVM folds the function to.
    for k in [11, 1122, 112_233, 11_223_344] {
        assert_eq!(
            count(z, |i| matches!(
                i,
                Inst::Const {
                    ty: Ty::U32,
                    value: Constant::Int(v)
                } if *v == k
            )),
            1,
            "{k}\n{z}"
        );
    }
}

#[test]
fn a_zip_whose_prefix_is_not_bounded_stays_a_loop() {
    // `k % 5` becomes `k | 5` and the minimum with the array's 4 is
    // dropped: the trip count is `k | 5`, which no interval bounds.
    let text = ZIP
        .replace("%110 = urem u32 %1, %111", "%110 = or u32 %1, %111")
        .replace("condbr %526, bb37, bb36", "condbr %526, bb36, bb36");
    let m = module(&text);
    let (out, report) = optimize_module(&m, &MidConfig::wasm32());
    assert_eq!(report.rollback_count(), 0, "{:?}", report.rollbacks);
    assert_eq!(stats(&report, "bounded_unroll").functions_changed, 0);
    assert!(loops_back(func(&out, "z")));
}

/// `f(state, byte)`: one CRC-32 step, `c = (state ^ byte) & 255`, eight
/// rounds of `c = if c & 1 != 0 { P ^ (c >> 1) } else { c >> 1 }` in a
/// loop, then `c ^ (state >> 8)`; `{second}` may run a second byte.
fn crc(poly2: u32, second: bool) -> String {
    let step = |n: u32, state: &str, byte: &str, poly: u32, out: &str| {
        let b = 100 * n;
        format!(
            "\x20   %{z} = zext u8 {byte} to u32\n\
             \x20   %{x} = xor u32 {state}, %{z}\n\
             \x20   %{m} = const u32 255\n\
             \x20   %{c} = and u32 %{x}, %{m}\n\
             \x20   %{k} = const u32 0\n\
             \x20   br bb{h}(%{c}, %{k})\n\
             bb{h}(%{p}: u32, %{i}: u32):\n\
             \x20   %{e} = const u32 8\n\
             \x20   %{t} = icmp ult u32 %{i}, %{e}\n\
             \x20   condbr %{t}, bb{body}, bb{done}\n\
             bb{body}:\n\
             \x20   %{one} = const u32 1\n\
             \x20   %{bit} = and u32 %{p}, %{one}\n\
             \x20   %{sh} = lshr u32 %{p}, %{one}\n\
             \x20   %{pc} = const u32 {poly}\n\
             \x20   %{xo} = xor u32 %{pc}, %{sh}\n\
             \x20   %{zero} = const u32 0\n\
             \x20   %{odd} = icmp ne u32 %{bit}, %{zero}\n\
             \x20   condbr %{odd}, bb{odd_b}, bb{even_b}\n\
             bb{odd_b}:\n\
             \x20   br bb{join}(%{xo})\n\
             bb{even_b}:\n\
             \x20   br bb{join}(%{sh})\n\
             bb{join}(%{q}: u32):\n\
             \x20   %{inc} = add u32 %{i}, %{one}\n\
             \x20   br bb{h}(%{q}, %{inc})\n\
             bb{done}:\n\
             \x20   %{eight} = const u32 8\n\
             \x20   %{hi} = lshr u32 {state}, %{eight}\n\
             \x20   %{out} = xor u32 %{p}, %{hi}\n",
            z = b + 100,
            x = b + 101,
            m = b + 102,
            c = b + 103,
            k = b + 104,
            p = b + 105,
            i = b + 106,
            e = b + 107,
            t = b + 108,
            one = b + 109,
            bit = b + 110,
            sh = b + 111,
            pc = b + 112,
            xo = b + 113,
            zero = b + 114,
            odd = b + 115,
            q = b + 116,
            inc = b + 117,
            eight = b + 118,
            hi = b + 119,
            out = out,
            h = 10 * n + 2,
            body = 10 * n + 3,
            odd_b = 10 * n + 4,
            even_b = 10 * n + 5,
            join = 10 * n + 6,
            done = 10 * n + 7,
        )
    };
    let first = step(0, "%0", "%1", 0xEDB8_8320, "300");
    let (second_step, result) = if second {
        (step(1, "%300", "%2", poly2, "301"), "%301")
    } else {
        (String::new(), "%300")
    };
    format!(
        "functy.0 = (u32, u8, u8) -> (u32)\n\n\
fn @f(functy.0) {{\n\
bb0(%0: u32, %1: u8, %2: u8):\n\
\x20   br bb1\n\
bb1:\n\
{first}{second_step}\
\x20   ret {result}\n\
}}\n"
    )
}

fn crc32(state: u32, byte: u8) -> u32 {
    let mut c = (state ^ u32::from(byte)) & 0xff;
    for _ in 0..8 {
        c = if c & 1 != 0 {
            0xEDB8_8320 ^ (c >> 1)
        } else {
            c >> 1
        };
    }
    c ^ (state >> 8)
}

#[test]
fn a_bit_serial_crc_step_becomes_a_table_lookup() {
    let m = module(&crc(0xEDB8_8320, false));
    let (out, report) = optimize_module(&m, &MidConfig::wasm32());
    assert_eq!(report.rollback_count(), 0, "{:?}", report.rollbacks);
    assert_eq!(stats(&report, "crc_table").functions_changed, 1);
    assert_eq!(compared(&report, "crc_table"), 1);
    assert_eq!(report.globals_added, 1);
    let f = func(&out, "f");
    assert!(!loops_back(f), "{f}");
    assert_eq!(count(f, |i| matches!(i, Inst::Load { .. })), 1, "{f}");
    assert_eq!(count(f, |i| matches!(i, Inst::CondBr { .. })), 0, "{f}");
    // The table is the CRC-32 table: entry `b` is the step on state 0.
    let table = out.globals.last().expect("the table");
    let Some(Constant::Bytes { data, .. }) = &table.initializer else {
        panic!("bytes");
    };
    assert_eq!(data.len(), 1024);
    for b in [0u8, 1, 0x80, 0xff] {
        let entry = u32::from_le_bytes(
            data[4 * usize::from(b)..4 * usize::from(b) + 4]
                .try_into()
                .expect("4 bytes"),
        );
        assert_eq!(entry, crc32(0, b), "entry {b}");
    }
}

#[test]
fn two_crc_steps_share_one_table_and_two_polynomials_do_not() {
    // Two steps of one polynomial: one table.
    let m = module(&crc(0xEDB8_8320, true));
    let (out, report) = optimize_module(&m, &MidConfig::wasm32());
    assert_eq!(report.rollback_count(), 0, "{:?}", report.rollbacks);
    assert_eq!(report.globals_added, 1);
    let f = func(&out, "f");
    assert_eq!(count(f, |i| matches!(i, Inst::Load { .. })), 2, "{f}");
    // Two polynomials: two tables, each its own.
    let m = module(&crc(0x82F6_3B78, true));
    let (_, report) = optimize_module(&m, &MidConfig::wasm32());
    assert_eq!(report.rollback_count(), 0, "{:?}", report.rollbacks);
    assert_eq!(report.globals_added, 2);
    // Switched off with constant-table promotion.
    let config = MidConfig {
        promote_constant_tables: false,
        ..MidConfig::wasm32()
    };
    let (_, report) = optimize_module(&module(&crc(0xEDB8_8320, false)), &config);
    assert_eq!(report.globals_added, 0);
    assert!(report.passes_withheld.contains_key("crc_table"));
}

#[test]
fn a_bit_loop_of_two_constants_keeps_its_branches() {
    // Rounds xoring alternating constants are not one polynomial's.
    let text = crc(0xEDB8_8320, false).replace(
        "%113 = xor u32 %112, %111",
        "%120 = and u32 %106, %109\n\x20   %121 = const u32 79764919\n\
         \x20   %122 = icmp ne u32 %120, %114\n\x20   %123 = select u32 %122, %121, %112\n\
         \x20   %113 = xor u32 %123, %111",
    );
    let m = module(&text);
    let (out, report) = optimize_module(&m, &MidConfig::wasm32());
    assert_eq!(report.rollback_count(), 0, "{:?}", report.rollbacks);
    assert_eq!(stats(&report, "crc_table").functions_changed, 0);
    assert_eq!(report.globals_added, 0);
    assert_eq!(
        count(func(&out, "f"), |i| matches!(i, Inst::Load { .. })),
        0
    );
}

/// `ri(a)`: `acc = acc * 3 + i` over `i` in `(a as u8).saturating_sub(3)
/// ..= a as u8`, as scalar replacement leaves `RangeInclusive<u8>`'s state:
/// the exhausted flag and the start as the loop's parameters, and the test
/// a `switch` on the `zext` of a `select` of 1 and 0.
const RANGE_INCLUSIVE: &str = "functy.0 = (u32) -> (u32)\n\n\
fn @ri(functy.0) {\n\
bb0(%1: u32):\n\
\x20   %15 = trunc u32 %1 to u8\n\
\x20   %16 = const u8 3\n\
\x20   %17, %18 = sub.overflow u8 %15, %16\n\
\x20   %20 = const u8 0\n\
\x20   %19 = select u8 %18, %20, %17\n\
\x20   %22 = const u32 0\n\
\x20   %121 = const i8 0\n\
\x20   br bb1(%22, %121, %19)\n\
bb1(%63: u32, %122: i8, %123: u8):\n\
\x20   %80 = const i8 0\n\
\x20   %81 = icmp ne i8 %122, %80\n\
\x20   %82 = icmp ule u8 %123, %15\n\
\x20   %83 = const bool false\n\
\x20   %84 = select bool %81, %83, %82\n\
\x20   %85 = icmp ult u8 %123, %15\n\
\x20   %86 = const u8 1\n\
\x20   %87 = add u8 %123, %86\n\
\x20   %88 = select u8 %85, %87, %123\n\
\x20   %89 = select u8 %84, %88, %123\n\
\x20   %90 = const i8 1\n\
\x20   %91 = select bool %85, %83, %84\n\
\x20   %92 = select i8 %91, %90, %122\n\
\x20   %93 = const u8 1\n\
\x20   %94 = const u8 0\n\
\x20   %95 = select u8 %84, %93, %94\n\
\x20   %104 = zext u8 %95 to i32\n\
\x20   switch %104 [ 0: bb4 default: bb3 ]\n\
bb4:\n\
\x20   ret %63\n\
bb3:\n\
\x20   %110 = const u32 3\n\
\x20   %109 = mul u32 %63, %110\n\
\x20   %111 = zext u8 %123 to u32\n\
\x20   %112 = add u32 %109, %111\n\
\x20   br bb1(%112, %92, %89)\n\
}\n";

#[test]
fn a_range_inclusive_switch_on_its_flag_select_becomes_a_branch() {
    let m = module(RANGE_INCLUSIVE);
    let (out, report) = optimize_module(&m, &MidConfig::wasm32());
    assert_eq!(report.rollback_count(), 0, "{:?}", report.rollbacks);
    assert!(stats(&report, "select_branch").functions_changed >= 1);
    assert!(compared(&report, "select_branch") >= 1);
    let ri = func(&out, "ri");
    assert_eq!(count(ri, |i| matches!(i, Inst::Switch { .. })), 0, "{ri}");
    assert_eq!(count(ri, |i| matches!(i, Inst::CondBr { .. })), 1, "{ri}");
    // The start the body passes back is the stepped one: the `select` on the
    // branch's condition is forwarded under it.
    assert_eq!(
        count(ri, |i| matches!(i, Inst::Select { ty: Ty::U8, .. })),
        2,
        "{ri}"
    );
}

/// `f(x)` on the `u32` input in the reference interpreter.
fn run_u32(m: &Module, x: u32) -> u32 {
    let f = m.function_by_name("f").expect("f");
    let arg = InterpretValue::int(Ty::U32, i128::from(x)).expect("u32");
    let out = Interpreter::with_module(m)
        .with_options(InterpretOptions {
            fuel: 1_000_000,
            max_call_depth: 16,
            panic_strategy: trust_ir::interpret::PanicStrategy::Abort,
        })
        .execute_func(f.id, [arg])
        .expect("f runs");
    match &out.returns[0].kind {
        InterpretValueKind::Int(i) => u32::try_from(i.as_signed() & 0xffff_ffff).expect("u32"),
        other => panic!("f returned {other:?}"),
    }
}

/// `f(n)`: a loop over `i < n` mixing `acc = acc * 3 ^ i`, left from its
/// body once `i + 1 >= 2` unless `n == 40`, whose exit re-enters the ENTRY
/// block as `f(2)` when `acc == 100000`. The edge into the entry passes
/// `2`, but the call passes any `n`: `n`'s interval is its type's.
const ENTRY_LOOP: &str = "functy.0 = (u32) -> (u32)\n\n\
fn @f(functy.0) {\n\
bb0(%1: u32):\n\
\x20   %2 = const u32 0\n\
\x20   br bb1(%2, %2)\n\
bb1(%3: u32, %4: u32):\n\
\x20   %5 = icmp ult u32 %3, %1\n\
\x20   condbr %5, bb2, bb3(%4)\n\
bb2:\n\
\x20   %6 = const u32 1\n\
\x20   %7 = add u32 %3, %6\n\
\x20   %30 = const u32 3\n\
\x20   %31 = mul u32 %4, %30\n\
\x20   %8 = xor u32 %31, %3\n\
\x20   %32 = const u32 2\n\
\x20   %33 = icmp uge u32 %7, %32\n\
\x20   %34 = const u32 40\n\
\x20   %35 = icmp ne u32 %1, %34\n\
\x20   %36 = and bool %33, %35\n\
\x20   condbr %36, bb3(%8), bb1(%7, %8)\n\
bb3(%12: u32):\n\
\x20   %9 = const u32 100000\n\
\x20   %10 = icmp eq u32 %12, %9\n\
\x20   condbr %10, bb4, bb5\n\
bb4:\n\
\x20   %11 = const u32 2\n\
\x20   br bb0(%11)\n\
bb5:\n\
\x20   ret %12\n\
}\n";

#[test]
fn an_entry_parameter_bound_is_not_read_from_the_edges_into_the_entry() {
    let m = module(ENTRY_LOOP);
    let (out, report) = optimize_module(&m, &MidConfig::wasm32());
    assert_eq!(report.rollback_count(), 0, "{:?}", report.rollbacks);
    assert_eq!(stats(&report, "bounded_unroll").functions_changed, 0);
    assert!(loops_back(func(&out, "f")));
    for x in [0, 1, 2, 3, 39, 40, 41, 1000] {
        assert_eq!(run_u32(&out, x), run_u32(&m, x), "f({x})");
    }
    assert_eq!(run_u32(&out, 40), 2_035_617_040);
}

/// `f(x)`: `select x == 0, x, (select x == 77, 0, x)` returned through the
/// `else` edge of `condbr x == 0` whose `then` edge re-enters the entry: only
/// the edge into the entry fixes `x == 0`, and the call enters it with any
/// `x`.
const ENTRY_GUARD: &str = "functy.0 = (u32) -> (u32)\n\n\
fn @f(functy.0) {\n\
bb0(%1: u32):\n\
\x20   %2 = const u32 0\n\
\x20   %3 = icmp eq u32 %1, %2\n\
\x20   %20 = const u32 77\n\
\x20   %21 = icmp eq u32 %1, %20\n\
\x20   %22 = select u32 %21, %2, %1\n\
\x20   %6 = select u32 %3, %1, %22\n\
\x20   %9 = const u32 1\n\
\x20   %10 = add u32 %6, %2\n\
\x20   condbr %3, bb0(%9), bb1(%10)\n\
bb1(%11: u32):\n\
\x20   ret %11\n\
}\n";

#[test]
fn an_edge_into_the_entry_guards_nothing() {
    let m = module(ENTRY_GUARD);
    let (out, report) = optimize_module(&m, &MidConfig::wasm32());
    assert_eq!(report.rollback_count(), 0, "{:?}", report.rollbacks);
    for x in [0, 1, 76, 77, 78] {
        assert_eq!(run_u32(&out, x), run_u32(&m, x), "f({x})");
    }
    assert_eq!(run_u32(&out, 77), 0);
}

/// `f(args)` on `u32` inputs in the reference interpreter.
fn run_u32s(m: &Module, args: &[u32]) -> u32 {
    let f = m.function_by_name("f").expect("f");
    let args = args
        .iter()
        .map(|&x| InterpretValue::int(Ty::U32, i128::from(x)).expect("u32"));
    let out = Interpreter::with_module(m)
        .with_options(InterpretOptions {
            fuel: 1_000_000,
            max_call_depth: 16,
            panic_strategy: trust_ir::interpret::PanicStrategy::Abort,
        })
        .execute_func(f.id, args)
        .expect("f runs");
    match &out.returns[0].kind {
        InterpretValueKind::Int(i) => u32::try_from(i.as_signed() & 0xffff_ffff).expect("u32"),
        other => panic!("f returned {other:?}"),
    }
}

/// `C`, the value the dead edges below pass as the loop's start.
const DEAD_START: u32 = 1_515_870_810;

/// Whole-pipeline: `m` keeps its loop, no loop pass changes it, nothing is
/// rolled back, and every input in `inputs` agrees.
fn entry_headed_loop_stays(m: &Module, inputs: &[&[u32]]) {
    let (out, report) = optimize_module(m, &MidConfig::wasm32());
    assert_eq!(report.rollback_count(), 0, "{:?}", report.rollbacks);
    for pass in ["bounded_unroll", "unroll", "loop_cf", "licm", "iv_sr"] {
        assert_eq!(stats(&report, pass).functions_changed, 0, "{pass}");
    }
    assert!(loops_back(func(&out, "f")), "{}", func(&out, "f"));
    for args in inputs {
        assert_eq!(run_u32s(&out, args), run_u32s(m, args), "f{args:?}");
    }
}

/// `x == C` (the double negation hides it from the seeded inputs' common
/// values) keeps `x + 7` in the loop at the ENTRY `bb0`; the unreachable
/// `bb9` alone enters it from outside, passing `C`.
const ENTRY_HEADER_BOUNDED: &str = "functy.0 = (u32) -> (u32)\n\n\
fn @f(functy.0) {\n\
bb0(%1: u32):\n\
\x20   %2 = const u32 1515870810\n\
\x20   %8 = const u32 4294967295\n\
\x20   %9 = xor u32 %1, %8\n\
\x20   %10 = xor u32 %9, %8\n\
\x20   %3 = icmp eq u32 %10, %2\n\
\x20   condbr %3, bb1, bb2\n\
bb1:\n\
\x20   %4 = const u32 7\n\
\x20   %5 = add u32 %1, %4\n\
\x20   br bb0(%5)\n\
bb2:\n\
\x20   ret %1\n\
bb9:\n\
\x20   %6 = const u32 1515870810\n\
\x20   br bb0(%6)\n\
}\n";

#[test]
fn an_unreachable_block_into_an_entry_header_is_no_preheader_for_bounded_unrolling() {
    let m = module(ENTRY_HEADER_BOUNDED);
    entry_headed_loop_stays(&m, &[&[0], &[DEAD_START], &[DEAD_START + 7]]);
    assert_eq!(run_u32s(&m, &[DEAD_START]), DEAD_START + 7);
}

#[test]
fn an_unreachable_block_into_an_entry_header_is_no_preheader_for_full_unrolling() {
    for test in [
        "\x20   %3 = icmp eq u32 %1, %2\n\x20   condbr %3, bb1, bb2\n",
        "\x20   %3 = icmp ne u32 %1, %2\n\x20   condbr %3, bb2, bb1\n",
    ] {
        let m = module(&format!(
            "functy.0 = (u32) -> (u32)\n\n\
fn @f(functy.0) {{\n\
bb0(%1: u32):\n\
\x20   %2 = const u32 1515870810\n\
{test}\
bb1:\n\
\x20   %4 = const u32 7\n\
\x20   %5 = add u32 %1, %4\n\
\x20   br bb0(%5)\n\
bb2:\n\
\x20   ret %1\n\
bb9:\n\
\x20   %6 = const u32 1515870810\n\
\x20   br bb0(%6)\n\
}}\n"
        ));
        entry_headed_loop_stays(&m, &[&[0], &[DEAD_START], &[DEAD_START + 7]]);
        assert_eq!(run_u32s(&m, &[DEAD_START]), DEAD_START + 7);
    }
}

#[test]
fn an_unreachable_block_into_an_entry_header_is_no_preheader_for_the_closed_form() {
    // `i < n` from the call's `i`, with `y` passed back unchanged; the dead
    // `bb9` passes `(0, C, 5)`. `f(0, C, 9)` counts to 9.
    let m = module(
        "functy.0 = (u32, u32, u32) -> (u32)\n\n\
fn @f(functy.0) {\n\
bb0(%1: u32, %2: u32, %3: u32):\n\
\x20   %4 = icmp ult u32 %1, %3\n\
\x20   condbr %4, bb1, bb2\n\
bb1:\n\
\x20   %5 = const u32 1\n\
\x20   %6 = add u32 %1, %5\n\
\x20   br bb0(%6, %2, %3)\n\
bb2:\n\
\x20   %7 = const u32 1515870810\n\
\x20   %8 = icmp eq u32 %2, %7\n\
\x20   %9 = select u32 %8, %1, %2\n\
\x20   ret %9\n\
bb9:\n\
\x20   %10 = const u32 0\n\
\x20   %11 = const u32 1515870810\n\
\x20   %12 = const u32 5\n\
\x20   br bb0(%10, %11, %12)\n\
}\n",
    );
    entry_headed_loop_stays(
        &m,
        &[
            &[0, 0, 5],
            &[0, DEAD_START, 5],
            &[0, DEAD_START, 9],
            &[3, 5, 9],
        ],
    );
    assert_eq!(run_u32s(&m, &[0, DEAD_START, 9]), 9);
}
