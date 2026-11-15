// trust-cg-verify/trust_ir_mid_tv_byaddr_tests.rs - tests of the by-address checker
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! A call passing a pointer for a packed `[u8 x 7]` parameter, which the
//! callee copies into a slot lane by lane and reads three fields of,
//! calls a clone reading the fields from the caller's bytes (the slot and
//! its copies gone), and the target with the clone appended agrees with
//! the source run in the differential's view; so does a clone without the
//! slot (lane reads become loads), and a call whose argument is a typed
//! pointer (cast to `ptr` first). Refused: a slot in a callee that writes
//! through another pointer or calls, a slot missing a lane or written
//! twice, a slot whose address escapes, a parameter read after the
//! prologue, an argument that is not a pointer, a callee that is not
//! crate-private and hidden, a clone body other than the derivation (a
//! field read one byte off, which the view's run also tells apart), a
//! clone under another plan's name, cast values that are not the fresh
//! ones, and an empty claim. A callee with an effect the allowlist does not
//! name (`dealloc`, `drop`, `retain`, `release` through a second pointer
//! parameter the caller gives the argument's own storage) between the
//! prologue's lane copies and the slot's loads is refused; the view's run
//! tells the `dealloc` clone apart from the source. So is one that writes
//! the caller's bytes through an `i64`, `u64` or thin-pointer carrier
//! there, and one that builds an `insertfield` there over an `i32`, `usize`
//! or `fatptr<str>` operand (a type the allowlist does not name), while an
//! `insertfield` into an array value is admitted. The pass's own copy of
//! this module's typing and prologue (`trust-cg-irmid`'s
//! `passes/byaddr_reading.rs`, compiled here) agrees with this module's
//! over a corpus of shapes.
//!
//! The witness types (`ByAddrWitness`, `ByAddrSite`, `ByAddrParam`,
//! `byaddr_clone_name`, `PassWitness::ByAddr`, `MidTvError::NotByAddr`) are
//! provisional surfaces pending the owner's sign-off
//! (`docs/wasm32_perf_roadmap.md`, "Pending owner sign-off").

use super::super::{
    DifferentialBudget, PassWitness, check_pass, compare_samples, interpretable,
    interpretable_module, run_samples, seeded_inputs,
};
use super::*;

const HEADER: &str = "; TrustIr text format v1\nmodule \"byaddr\"\n\
                      target \"wasm32-unknown-unknown\" 4 little\n\n";

const CALLEE: &str = "sum.tcg.crate.0123456789abcdef";

fn module(body: &str) -> Module {
    trust_ir::parser::parse_module(&format!("{HEADER}{body}"))
        .unwrap_or_else(|e| panic!("test module failed to parse: {e}\n{body}"))
}

fn func<'m>(m: &'m Module, name: &str) -> &'m Function {
    m.functions
        .iter()
        .find(|f| f.name == name)
        .expect("function")
}

fn v(n: u32) -> ValueId {
    ValueId::new(n)
}

/// `sum(p: [u8 x 7]) = u32 at 1 + u16 at 5 + u8 at 0` as the rustc bridge
/// spells a packed by-value parameter: a slot `%10` filled lane by lane in
/// the prologue, then the field loads. `{extra}` follows the loads. `f(a,
/// b)` stores the seven bytes of `a` and `b` into a slot `%2` and calls
/// `sum(%2)` (the argument `{arg}`).
fn program(extra: &str, arg: &str) -> String {
    let mut copy = String::new();
    for j in 0..7 {
        copy.push_str(&format!(
            "\x20   %{x} = extractfield [ty.0 x 7] %0, {j}\n\
             \x20   %{y} = insertfield [ty.0 x 7] %10, {j}, %{x}\n",
            x = 20 + 2 * j,
            y = 21 + 2 * j,
        ));
    }
    format!(
        "type ty.0 = u8\n\n\
functy.0 = ([ty.0 x 7]) -> (u32)\n\
functy.1 = (u32, u32) -> (u32)\n\n\
fn @{CALLEE}(functy.0) {{\n\
\x20   ; #visibility: hidden\n\
bb0(%0: [ty.0 x 7]):\n\
\x20   %10 = alloca [ty.0 x 7], align 1\n\
{copy}\
\x20   %40 = const i32 1\n\
\x20   %41 = gep inbounds u8, ptr %10, %40\n\
\x20   %42 = load u32, ptr %41\n\
\x20   %43 = const i32 5\n\
\x20   %44 = gep inbounds u8, ptr %10, %43\n\
\x20   %45 = load u16, ptr %44\n\
\x20   %46 = load u8, ptr %10\n\
\x20   %47 = zext u16 %45 to u32\n\
\x20   %48 = zext u8 %46 to u32\n\
\x20   %49 = add u32 %42, %47\n\
\x20   %50 = add u32 %49, %48\n\
{extra}\
\x20   ret %50\n\
}}\n\n\
fn @f(functy.1) {{\n\
bb0(%0: u32, %1: u32):\n\
\x20   %2 = alloca [ty.0 x 7], align 1\n\
\x20   store u32 %0, ptr %2\n\
\x20   %3 = const usize 3\n\
\x20   %4 = gep u8, ptr %2, %3\n\
\x20   store u32 %1, ptr %4\n\
\x20   %5 = {arg}\n\
\x20   %6 = call @func.0(%5)\n\
\x20   %7 = xor u32 %6, %0\n\
\x20   ret %7\n\
}}\n"
    )
}

fn default_program() -> Module {
    module(&program("", "copy ptr %2"))
}

/// The witness for the call in `f` under `params`, with the clone derived
/// by this module's own `derive_clone` (the claim a correct pass makes).
fn witness(m: &Module, params: Vec<ByAddrParam>, casts: Vec<ValueId>) -> ByAddrWitness {
    let callee = func(m, CALLEE);
    let sig = m.func_type(callee.ty).unwrap();
    let csig = clone_sig(sig, &params);
    let ty = trust_ir::FuncTyId::new(m.func_types.len() as u32);
    let id = FuncId::new(m.functions.iter().map(|f| f.id.index()).max().unwrap() + 1);
    let name = byaddr_clone_name(CALLEE, &params).unwrap();
    let lanes: Vec<(Ty, u64)> = params.iter().map(|_| (Ty::U8, 1)).collect();
    let clone = derive_clone(m, callee, &params, &lanes, id, name, ty);
    ByAddrWitness {
        sites: vec![ByAddrSite {
            block: BlockId::new(0),
            index: 6,
            callee: callee.id,
            clone: id,
            params,
            casts,
        }],
        new_func_types: vec![csig],
        new_functions: vec![clone],
    }
}

fn slot_plan() -> Vec<ByAddrParam> {
    vec![ByAddrParam {
        index: 0,
        slot: Some(v(10)),
    }]
}

/// The module after the rewrite: the caller replaced, the clone appended.
fn target_module(m: &Module, out: &Function, w: &ByAddrWitness) -> Module {
    let mut t = m.clone();
    let at = t.functions.iter().position(|g| g.name == "f").unwrap();
    t.functions[at] = out.clone();
    t.functions.extend(w.new_functions.iter().cloned());
    t.func_types.extend(w.new_func_types.iter().cloned());
    t
}

/// `f` of the source and of `t` run in the view on seeded inputs.
fn runs(
    m: &Module,
    t: &Module,
) -> (
    Vec<super::super::SampleOutcome>,
    Vec<super::super::SampleOutcome>,
) {
    let inputs = seeded_inputs(m, func(m, "f"), 32, 32, 9).expect("scalar parameters");
    let run = |module: &Module| {
        let view = interpretable_module(module);
        let f = func(module, "f");
        let viewed = interpretable(&view, f).unwrap_or_else(|| f.clone());
        run_samples(&view, &viewed, &inputs, DifferentialBudget::default()).0
    };
    (run(m), run(t))
}

fn accepted_and_agrees(m: &Module, w: &ByAddrWitness) -> Function {
    let src = func(m, "f");
    let (out, verdict) = rebuild_byaddr(m, src, w).expect("accepted");
    assert_eq!(verdict.refinements, 1);
    check_pass(m, 32, src, &out, &PassWitness::ByAddr(w.clone())).expect("check_pass");
    let (a, t) = runs(m, &target_module(m, &out, w));
    let report = compare_samples(&a, &t);
    assert!(report.mismatch.is_none(), "{:?}", report.mismatch);
    assert!(report.compared > 0, "{report:?}");
    out
}

#[test]
fn a_packed_parameter_copied_into_a_slot_is_read_through_its_address() {
    let m = default_program();
    let w = witness(&m, slot_plan(), Vec::new());
    accepted_and_agrees(&m, &w);
    let clone = &w.new_functions[0];
    let body: Vec<&Inst> = clone
        .blocks
        .iter()
        .flat_map(|b| &b.body)
        .map(|n| &n.inst)
        .collect();
    assert!(
        !body
            .iter()
            .any(|i| matches!(i, Inst::Alloca { .. } | Inst::InsertField { .. }))
    );
    assert_eq!(
        body.iter()
            .filter(|i| matches!(i, Inst::Load { .. }))
            .count(),
        3,
        "only the three field loads: {clone}"
    );
    assert_eq!(clone.blocks[0].params[0].1, Ty::Ptr);
}

#[test]
fn a_clone_without_the_slot_and_a_typed_argument_agree() {
    let m = default_program();
    let plain = vec![ByAddrParam {
        index: 0,
        slot: None,
    }];
    let w = witness(&m, plain, Vec::new());
    accepted_and_agrees(&m, &w);
    assert_eq!(
        w.new_functions[0]
            .blocks
            .iter()
            .flat_map(|b| &b.body)
            .filter(|n| matches!(n.inst, Inst::Load { align: Some(1), .. }))
            .count(),
        7,
        "each lane read is a load"
    );
    // A typed pointer argument is cast to `ptr` first.
    let m = module(&program("", "ptrtoptr ptr %2 to *const u8"));
    let w = witness(&m, slot_plan(), vec![v(8)]);
    let out = accepted_and_agrees(&m, &w);
    assert!(out.blocks[0].body.iter().any(|n| n.results == [v(8)]
        && matches!(
            n.inst,
            Inst::Cast {
                op: CastOp::PtrToPtr,
                dst_ty: Ty::Ptr,
                ..
            }
        )));
}

fn refused(m: &Module, w: &ByAddrWitness) {
    assert!(
        matches!(
            rebuild_byaddr(m, func(m, "f"), w),
            Err(MidTvError::NotByAddr { .. })
        ),
        "{w:?}"
    );
}

#[test]
fn slots_and_parameters_off_the_form_are_refused() {
    // The callee also writes through a pointer it loads (not its own slot).
    let writes = module(&program(
        "\x20   %60 = load ptr, ptr %10\n\x20   store u32 %50, ptr %60\n",
        "copy ptr %2",
    ));
    refused(&writes, &witness(&writes, slot_plan(), Vec::new()));
    // The callee calls something.
    let calls = module(&program(
        "\x20   %61 = call @func.1(%50, %50)\n",
        "copy ptr %2",
    ));
    refused(&calls, &witness(&calls, slot_plan(), Vec::new()));
    // A lane missing, and a lane written twice.
    let missing = module(
        &program("", "copy ptr %2").replace("%33 = insertfield [ty.0 x 7] %10, 6, %32\n", ""),
    );
    refused(&missing, &witness(&missing, slot_plan(), Vec::new()));
    let twice = module(&program("", "copy ptr %2").replace(
        "%33 = insertfield [ty.0 x 7] %10, 6, %32",
        "%33 = insertfield [ty.0 x 7] %10, 5, %30",
    ));
    refused(&twice, &witness(&twice, slot_plan(), Vec::new()));
    // The slot's address escapes (stored into another slot).
    let escapes = module(&program(
        "\x20   %62 = alloca ptr\n\x20   store ptr %10, ptr %62\n",
        "copy ptr %2",
    ));
    refused(&escapes, &witness(&escapes, slot_plan(), Vec::new()));
    // The parameter read after the prologue (behind a load of another
    // pointer the prologue does not allow: a volatile one).
    let late = module(
        &program(
            "\x20   %63 = extractfield [ty.0 x 7] %0, 2\n",
            "copy ptr %2",
        )
        .replace(
            "%40 = const i32 1",
            "%64 = volatile load u8, ptr %10\n\x20   %40 = const i32 1",
        ),
    );
    let plain = vec![ByAddrParam {
        index: 0,
        slot: None,
    }];
    refused(&late, &witness(&late, plain, Vec::new()));
    // An argument that is not a pointer.
    let integer = module(&program("", "copy u32 %0"));
    refused(&integer, &witness(&integer, slot_plan(), Vec::new()));
    // A callee that is not hidden, or not crate-private.
    let exported =
        module(&program("", "copy ptr %2").replace("\x20   ; #visibility: hidden\n", ""));
    refused(&exported, &witness(&exported, slot_plan(), Vec::new()));
    let m = default_program();
    let mut w = witness(&m, slot_plan(), Vec::new());
    w.new_functions[0].name = "other.tcg.ap00000000.tcg.crate.0123456789abcdef".to_string();
    refused(&m, &w);
    // Cast values that are not the fresh ones, and an empty claim.
    let typed = module(&program("", "ptrtoptr ptr %2 to *const u8"));
    refused(&typed, &witness(&typed, slot_plan(), Vec::new()));
    refused(&typed, &witness(&typed, slot_plan(), vec![v(2)]));
    refused(&m, &ByAddrWitness::default());
}

#[test]
fn a_clone_reading_a_field_one_byte_off_is_refused_and_disagrees() {
    let m = default_program();
    let mut w = witness(&m, slot_plan(), Vec::new());
    for node in w.new_functions[0]
        .blocks
        .iter_mut()
        .flat_map(|b| &mut b.body)
    {
        if let Inst::Const {
            value: Constant::Int(k @ 5),
            ..
        } = &mut node.inst
        {
            *k = 4;
        }
    }
    refused(&m, &w);
    let src = func(&m, "f");
    let (out, _) = rebuild_byaddr(&m, src, &witness(&m, slot_plan(), Vec::new())).expect("ok");
    let (a, t) = runs(&m, &target_module(&m, &out, &w));
    assert!(compare_samples(&a, &t).mismatch.is_some());
}

/// `sum` of [`program`] with a second `ptr` parameter `%1` and `{effect}`
/// between the prologue's lane copies and the slot's loads; `f` passes the
/// argument's own storage `%2` for both.
fn effect_program(effect: &str) -> Module {
    module(
        &program("", "copy ptr %2")
            .replace(
                "functy.0 = ([ty.0 x 7]) -> (u32)",
                "functy.0 = ([ty.0 x 7], ptr) -> (u32)",
            )
            .replace("bb0(%0: [ty.0 x 7]):", "bb0(%0: [ty.0 x 7], %1: ptr):")
            .replace(
                "\x20   %40 = const i32 1\n",
                &format!("{effect}\x20   %40 = const i32 1\n"),
            )
            .replace("call @func.0(%5)", "call @func.0(%5, %2)"),
    )
}

#[test]
fn effects_the_allowlist_does_not_name_are_refused() {
    // Control: the same shape without the effect is accepted and agrees.
    let control = effect_program("");
    let w = witness(&control, slot_plan(), Vec::new());
    let out = accepted_and_agrees(&control, &w);
    for effect in [
        "\x20   dealloc %1\n",
        "\x20   drop [ty.0 x 7], %1\n",
        "\x20   retain %1\n",
        "\x20   release %1\n",
    ] {
        let m = effect_program(effect);
        assert!(
            func(&m, CALLEE)
                .blocks
                .iter()
                .flat_map(|b| &b.body)
                .any(|n| matches!(
                    n.inst,
                    Inst::Dealloc { .. }
                        | Inst::Drop { .. }
                        | Inst::Retain { .. }
                        | Inst::Release { .. }
                )),
            "{effect}"
        );
        refused(&m, &witness(&m, slot_plan(), Vec::new()));
    }
    // The claimed clone of the deallocating callee reads the caller's
    // freed bytes: the view's run tells it apart from the source (whose
    // slot holds a copy). `f`'s rewritten body is the control's.
    let m = effect_program("\x20   dealloc %1\n");
    let w = witness(&m, slot_plan(), Vec::new());
    let (a, t) = runs(&m, &target_module(&m, &out, &w));
    assert!(compare_samples(&a, &t).mismatch.is_some());
}

/// `sum` of [`program`] with a second parameter `%1: {carrier}` and
/// `{effect}` between the prologue's lane copies and the slot's loads; `f`
/// passes the argument's own storage `%2` for both, the second spelled
/// `%8 = {carry}` just before the call (which is then at index 7).
fn carrier_program(carrier: &str, carry: &str, effect: &str) -> Module {
    module(
        &program("", "copy ptr %2")
            .replace(
                "functy.0 = ([ty.0 x 7]) -> (u32)",
                &format!("functy.0 = ([ty.0 x 7], {carrier}) -> (u32)"),
            )
            .replace(
                "bb0(%0: [ty.0 x 7]):",
                &format!("bb0(%0: [ty.0 x 7], %1: {carrier}):"),
            )
            .replace(
                "\x20   %40 = const i32 1\n",
                &format!("{effect}\x20   %40 = const i32 1\n"),
            )
            .replace(
                "\x20   %6 = call @func.0(%5)\n",
                &format!("\x20   %8 = {carry}\n\x20   %6 = call @func.0(%5, %8)\n"),
            ),
    )
}

/// The byte the callee writes through its second parameter: lane 0 of the
/// array (the byte the slot's `u8` load reads) set to 99.
const WRITE_THROUGH: &str =
    "\x20   %60 = const u8 99\n\x20   %61 = insertfield [ty.0 x 7] %1, 0, %60\n";

/// The rustc bridge's integer pointer carriers: the wasm32 lane (and
/// `trust-cg-irmid`'s `escape::is_pointer_carrier`) reads an `i64`/`u64`
/// aggregate operand as the address of the aggregate's bytes and writes the
/// field through it, as it does a thin pointer. A callee that writes the
/// caller's bytes through one between its lane copies and the slot's loads
/// is refused: its clone would read the byte after the write, the source
/// the copy the call saw. The witness is the clone the pass made while the
/// allowlist admitted any `insertfield` over a type other than a thin
/// pointer (OD-166's 2026-10-10 correction). The differential's view does
/// not model an integer carrier's write (its runs of such a module stop as
/// type errors and compare nothing), so the checker itself must refuse it.
/// Controls:
/// the thin-pointer carrier is refused too, and an `insertfield` into an
/// array VALUE (the slot's bytes loaded whole) is admitted.
#[test]
fn a_write_through_an_integer_pointer_carrier_is_refused() {
    let mut admitted = Vec::new();
    for (carrier, carry) in [
        ("ptr", "copy ptr %2"),
        ("i64", "ptrtoint ptr %2 to i64"),
        ("u64", "ptrtoint ptr %2 to u64"),
    ] {
        let m = carrier_program(carrier, carry, WRITE_THROUGH);
        let src = func(&m, "f");
        let mut w = witness(&m, slot_plan(), Vec::new());
        w.sites[0].index = 7;
        // The clone the pass made: the slot gone, the write kept, the
        // byte read from the caller's storage after it.
        let clone = &w.new_functions[0];
        let body: Vec<&Inst> = clone
            .blocks
            .iter()
            .flat_map(|b| &b.body)
            .map(|n| &n.inst)
            .collect();
        assert!(
            body.iter().any(|i| matches!(
                i,
                Inst::InsertField { aggregate, field: 0, .. } if *aggregate == v(1)
            )) && !body.iter().any(|i| matches!(i, Inst::Alloca { .. })),
            "{carrier}: {clone}"
        );
        // The caller redirected to it.
        let mut out = src.clone();
        let Inst::Call { callee, .. } = &mut out.blocks[0].body[7].inst else {
            panic!("{carrier}: the call is at index 7: {src}");
        };
        *callee = w.sites[0].clone;
        let verdict = check_pass(&m, 32, src, &out, &PassWitness::ByAddr(w.clone()));
        if !matches!(&verdict, Err(MidTvError::NotByAddr { site: 0, why })
            if why.contains("writes memory other than its own slots"))
        {
            admitted.push(format!("{carrier}: {verdict:?}"));
        }
    }
    assert!(admitted.is_empty(), "{admitted:#?}");
    // Control: a value `insertfield` (over the slot's bytes loaded as the
    // array) writes no memory and is admitted.
    let value = carrier_program(
        "i64",
        "ptrtoint ptr %2 to i64",
        "\x20   %60 = const u8 99\n\x20   %62 = load [ty.0 x 7], ptr %10\n\
         \x20   %61 = insertfield [ty.0 x 7] %62, 0, %60\n",
    );
    let mut w = witness(&value, slot_plan(), Vec::new());
    w.sites[0].index = 7;
    let (_, verdict) = rebuild_byaddr(&value, func(&value, "f"), &w).expect("a value insert");
    assert_eq!(verdict.refinements, 1);
}

/// [`program`] with `%58 = {operand}` and an `insertfield [ty.0 x 7]` over
/// `%58` between the prologue's lane copies and the slot's loads.
fn insert_over_program(operand: &str) -> Module {
    module(&program("", "copy ptr %2").replace(
        "\x20   %40 = const i32 1\n",
        &format!(
            "\x20   %58 = {operand}\n\
             \x20   %59 = const u8 1\n\
             \x20   %61 = insertfield [ty.0 x 7] %58, 0, %59\n\
             \x20   %40 = const i32 1\n"
        ),
    ))
}

/// The allowlist names the aggregate VALUE types an `insertfield` may build
/// over (struct, tuple, array, record, enum); every other operand type
/// refuses, not only the pointer carriers. Rows: an `i32`, a `usize` and a
/// `fatptr<str>` operand, none of them a carrier (a thin pointer, `i64` or
/// `u64`), so a deny list of the carriers would admit each; the checker
/// refuses each as a write of memory other than the callee's own slots.
/// Control: the same `insertfield` over the slot's bytes loaded as the
/// array is admitted.
#[test]
fn an_insert_over_a_type_the_allowlist_does_not_name_is_refused() {
    let mut admitted = Vec::new();
    for operand in ["const i32 0", "const usize 0", "load fatptr<str>, ptr %10"] {
        let m = insert_over_program(operand);
        let w = witness(&m, slot_plan(), Vec::new());
        match rebuild_byaddr(&m, func(&m, "f"), &w) {
            Err(MidTvError::NotByAddr { site: 0, why })
                if why.contains("writes memory other than its own slots") => {}
            Err(e) => admitted.push(format!("{operand}: {e:?}")),
            Ok((_, verdict)) => admitted.push(format!("{operand}: {verdict:?}")),
        }
    }
    assert!(admitted.is_empty(), "{admitted:#?}");
    let value = insert_over_program("load [ty.0 x 7], ptr %10");
    let w = witness(&value, slot_plan(), Vec::new());
    let (_, verdict) = rebuild_byaddr(&value, func(&value, "f"), &w).expect("a value insert");
    assert_eq!(verdict.refinements, 1);
}

/// By-address cloning's own typing and prologue (`trust-cg-irmid`'s
/// `passes/byaddr_reading.rs`), compiled here: `trust-cg-irmid` depends on
/// this crate, so this crate cannot name the pass, and the pass keeps its own
/// copy of this module's rules (OD-117).
#[path = "../../trust-cg-irmid/src/passes/byaddr_reading.rs"]
mod pass_reading;

/// The forms the drift corpus places in a callee's entry block (each line
/// defines `%60`.. from values the template defines first).
const DRIFT_FORMS: &[&str] = &[
    "%60 = const u32 7",
    "%60 = null ptr",
    "%60 = undef u32",
    "%60 = global_addr @global.0",
    "%60 = add u32 %3, %3",
    "%60 = fadd f64 %4, %4",
    "%60 = not u32 %3",
    "%60 = fneg f64 %4",
    "%60, %61 = add.overflow u32 %3, %3",
    "%60 = icmp ult u32 %3, %3",
    "%60 = fcmp olt f64 %4, %4",
    "%60 = zext u32 %3 to u64",
    "%60 = ptrtoptr ptr %2 to *mut u8",
    "%60 = copy u32 %3",
    "%60 = select u32 %12, %3, %3",
    "%60 = select ptr %12, %2, %10",
    "%60 = gep u8, ptr %10, %11",
    "%60 = gep u8, ptr %2, %11",
    "%60 = load u32, ptr %2",
    "%60 = volatile load u32, ptr %2",
    "%60 = load [ty.0 x 7], ptr %10",
    "store u8 %13, ptr %10",
    "store u8 %13, ptr %2",
    "volatile store u8 %13, ptr %10",
    "%60 = gep u8, ptr %10, %11\n    store u8 %13, ptr %60",
    "%60 = gep u8, ptr %10, %3\n    store u8 %13, ptr %60",
    "%60 = alloca u32, align 4",
    "%60 = alloca u32, %3, align 4",
    "%60 = alloca u32, align 4\n    store u32 %3, ptr %60",
    "%60 = alloca u32, align 4\n    memset ptr %60, %13, %11",
    "memcopy ptr %10, ptr %2, %11",
    "%60 = extractfield [ty.0 x 7] %0, 6",
    "%60 = extractfield [ty.1 x 2] %1, 1",
    "%60 = insertfield [ty.0 x 7] %10, 0, %13",
    "%60 = load [ty.0 x 7], ptr %10\n    %61 = insertfield [ty.0 x 7] %60, 0, %13",
    "%60 = undef [ty.0 x 7]\n    %61 = insertfield [ty.0 x 7] %60, 0, %13\n    \
     %62 = insertfield [ty.0 x 7] %61, 1, %13",
    "%60 = make_aggregate [ty.1 x 2] (%3, %3)",
    "%60 = array_splat [ty.0 x 7] %13",
    "%60 = call @func.0(%3)",
    "dealloc %2",
    "drop [ty.0 x 7], %2",
    "retain %2",
    "release %2",
    "assume %12",
    "%60 = atomic_load seq_cst u32, ptr %2",
    "fence seq_cst",
];

/// A callee with array parameters `%0: [u8 x 7]` (copied into its slot
/// `%10`, lanes 0..3 then 3..7) and `%1: [u32 x 2]` (one lane read between
/// the two halves), a `ptr`, a `u32` and an `f64`, `{form}` at position
/// `at` (0: before the copies, 1: between their halves, 2: after them), a
/// second block taking a parameter; and a caller passing arguments defined
/// by several forms.
fn drift_shape(form: &str, at: usize) -> Module {
    let lanes = |range: std::ops::Range<u32>| {
        range
            .map(|j| {
                format!(
                    "    %{x} = extractfield [ty.0 x 7] %0, {j}\n    \
                     %{y} = insertfield [ty.0 x 7] %10, {j}, %{x}\n",
                    x = 20 + 2 * j,
                    y = 21 + 2 * j,
                )
            })
            .collect::<String>()
    };
    let probe = |k: usize| {
        if k == at {
            format!("    {form}\n")
        } else {
            String::new()
        }
    };
    module(&format!(
        "type ty.0 = u8\n\
         type ty.1 = u32\n\n\
         global internal align(1) @K [ty.0 x 8] = bytes<0102030405060708>\n\n\
         functy.0 = (u32) -> (u32)\n\
         functy.1 = ([ty.0 x 7], [ty.1 x 2], ptr, u32, f64) -> (u32)\n\
         functy.2 = (u32, u32) -> (u32)\n\n\
         fn @ext(functy.0) {{\n}}\n\n\
         fn @{CALLEE}(functy.1) {{\n\
         \x20   ; #visibility: hidden\n\
         bb0(%0: [ty.0 x 7], %1: [ty.1 x 2], %2: ptr, %3: u32, %4: f64):\n\
         \x20   %10 = alloca [ty.0 x 7], align 1\n\
         \x20   %11 = const usize 1\n\
         \x20   %12 = const bool true\n\
         \x20   %13 = const u8 0\n\
         {p0}{first}{p1}\
         \x20   %90 = extractfield [ty.1 x 2] %1, 0\n\
         {second}{p2}\
         \x20   %40 = const i32 1\n\
         \x20   %41 = gep inbounds u8, ptr %10, %40\n\
         \x20   %42 = load u32, ptr %41\n\
         \x20   %43 = add u32 %42, %90\n\
         \x20   br bb1(%43)\n\
         bb1(%44: u32):\n\
         \x20   %45 = add u32 %44, %3\n\
         \x20   ret %45\n\
         }}\n\n\
         fn @f(functy.2) {{\n\
         bb0(%0: u32, %1: u32):\n\
         \x20   %2 = alloca [ty.0 x 7], align 1\n\
         \x20   %3 = alloca [ty.1 x 2], align 4\n\
         \x20   %4 = icmp ult u32 %0, %1\n\
         \x20   %5 = select ptr %4, %2, %3\n\
         \x20   %6 = null ptr\n\
         \x20   %7 = ptrtoptr ptr %2 to *mut u8\n\
         \x20   %8 = copy ptr %3\n\
         \x20   %9 = global_addr @global.0\n\
         \x20   %11 = undef ptr\n\
         \x20   %12 = uitofp u32 %0 to f64\n\
         \x20   %13 = call @func.1(%2, %3, %5, %0, %12)\n\
         \x20   %14 = call @func.1(%7, %8, %6, %1, %12)\n\
         \x20   %15 = call @func.1(%9, %11, %2, %13, %12)\n\
         \x20   %16 = add u32 %13, %14\n\
         \x20   %17 = add u32 %16, %15\n\
         \x20   ret %17\n\
         }}\n",
        p0 = probe(0),
        first = lanes(0..3),
        p1 = probe(1),
        second = lanes(3..7),
        p2 = probe(2),
    ))
}

/// The pass's typing and prologue (its own copy) agree with this module's
/// over a corpus of shapes: each form of [`DRIFT_FORMS`] at each of three
/// positions of a callee's prologue, each function's typing compared value
/// by value, and the callee's prologue compared under every set of promoted
/// entry parameters. A change to either side alone that a form here
/// observes (the pass typing `nullptr` or an `insertfield`'s result, the
/// checker admitting `globaladdr` into the prologue, ...) fails here. The
/// corpus is checked to reach both outcomes of each rule.
#[test]
fn the_pass_reads_a_callee_as_the_checker_does() {
    let (mut shapes, mut typed, mut untyped, mut ended, mut passed) = (0, 0, 0, 0, 0);
    for form in DRIFT_FORMS {
        for at in 0..3 {
            let m = drift_shape(form, at);
            shapes += 1;
            for f in &m.functions {
                let ours = types_of(f);
                assert_eq!(
                    pass_reading::types_of(f),
                    ours,
                    "{form} at {at}: {}",
                    f.name
                );
                for node in f.blocks.iter().flat_map(|b| &b.body) {
                    if let [r] = node.results.as_slice() {
                        if ours.contains_key(r) {
                            typed += 1;
                        } else {
                            untyped += 1;
                        }
                    }
                }
            }
            let callee = func(&m, CALLEE);
            let params: Vec<ValueId> = callee.blocks[0].params.iter().map(|(p, _)| *p).collect();
            // Where the form sits in the entry block.
            let first = 4 + if at == 0 { 0 } else { 6 } + if at == 2 { 9 } else { 0 };
            for mask in 0..1u32 << params.len() {
                let promoted: HashSet<ValueId> = params
                    .iter()
                    .enumerate()
                    .filter(|(i, _)| mask & (1 << i) != 0)
                    .map(|(_, p)| *p)
                    .collect();
                let (len, _) = prologue(callee, &promoted);
                assert_eq!(
                    pass_reading::prologue(callee, &promoted),
                    len,
                    "{form} at {at}, promoted {promoted:?}"
                );
                if len == first {
                    ended += 1;
                } else if len > first {
                    passed += 1;
                }
            }
        }
    }
    assert_eq!(shapes, DRIFT_FORMS.len() * 3);
    assert!(typed > 0 && untyped > 0, "typed {typed}, untyped {untyped}");
    assert!(ended > 0 && passed > 0, "ended {ended}, passed {passed}");
}

#[test]
fn typed_packed_snapshot_copies_are_rechecked_and_stale_snapshots_refused() {
    let mut text = program("", "load [ty.0 x 7], ptr %2");
    for j in 0..7 {
        text = text.replace(
            &format!("%{x} = extractfield [ty.0 x 7] %0, {j}\n    %{y} = insertfield [ty.0 x 7] %10, {j}, %{x}", x=20+2*j, y=21+2*j),
            &format!("%{i} = const usize {j}\n    %{x} = extractelement u8 %0, %{i}\n    %{a} = gep u8, ptr %10, %{i}\n    store u8 %{x}, ptr %{a}", x=20+2*j, i=100+2*j, a=101+2*j),
        );
    }
    let m = module(&text);
    assert!(trust_ir_build::validate_module(&m).is_empty());
    let w = witness(&m, slot_plan(), vec![]);
    let out = accepted_and_agrees(&m, &w);
    assert!(trust_ir_build::validate_module(&target_module(&m, &out, &w)).is_empty());
    let clone = &w.new_functions[0];
    assert_eq!(
        clone
            .blocks
            .iter()
            .flat_map(|b| &b.body)
            .filter(|n| matches!(n.inst, Inst::Load { .. }))
            .count(),
        3
    );
    assert!(
        !clone
            .blocks
            .iter()
            .flat_map(|b| &b.body)
            .any(|n| matches!(n.inst, Inst::Alloca { .. } | Inst::Store { .. }))
    );
    // Moving a write between the snapshot and call is a real semantic
    // difference. The borrowed-address rewrite must refuse it.
    let stale = module(&text.replace(
        "    %6 = call @func.0(%5)",
        "    store u32 %1, ptr %2\n    %6 = call @func.0(%5)",
    ));
    let mut sw = witness(&stale, slot_plan(), vec![]);
    sw.sites[0].index += 1;
    assert!(rebuild_byaddr(&stale, func(&stale, "f"), &sw).is_err());
    for bad in [
        text.replace("%5 = load [ty.0 x 7]", "%5 = volatile load [ty.0 x 7]"),
        text.replace("%100 = const usize 0", "%100 = const usize 7"),
        text.replace("%20 = extractelement u8", "%20 = extractelement i8"),
        text.replace("store u8 %20, ptr %101", "store u8 %22, ptr %101"),
        text.replace(
            "%101 = gep u8, ptr %10, %100",
            "%101 = gep u8, ptr %10, %102",
        ),
    ] {
        let bad = module(&bad);
        let w = witness(&bad, slot_plan(), vec![]);
        assert!(rebuild_byaddr(&bad, func(&bad, "f"), &w).is_err());
    }
}
