// trust-cg-fuzz/tests/sweep3_cmp_branch_fusion.rs
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Sweep3 surface: "cmp_branch_fusion" — the compare/branch fusion path and the
// idioms that feed it. Specifically:
//   * icmp feeding condbr (the fusion path): a comparison whose Bool result is
//     consumed DIRECTLY by a conditional branch, where the branch's two arms
//     return distinct values. This is the canonical "fuse cmp into the branch"
//     shape that a backend lowers to a compare-and-branch (cbz/cbnz/b.cc).
//   * chained comparisons: cmp -> condbr -> (in a successor) cmp -> condbr,
//     forming short-circuit && / || ladders and diamonds with block-param phis.
//   * compare-and-select: select(cmp, a, b) — fusion into a conditional move.
//   * overflow-flag idioms: overflow(Add/Sub/Mul) producing a (result, flag)
//     pair, then condbr / select on the flag (add-then-check, sub-then-check).
//   * boolean materialization to i64 stored and reloaded: zext/sext(cmp) -> i64,
//     stored to an alloca slot and reloaded before use, optionally then branched.
//
// ============================== ORACLE CONTRACT ==============================
// Verified against trust-cg-codegen/src/interpreter.rs:
//
//  (A) eval_icmp compares FULL i128 values: signed via `<`, unsigned via
//      `as u128`. It never masks to operand width, and ZExt/SExt/Trunc are
//      no-ops at the i128 level (eval_cast). Therefore:
//        - SIGNED compares are oracle-valid iff every operand's stored i128 is
//          already its canonical signed value at the compare width. We guarantee
//          this by deriving dynamic operands as `param & 0xffff` (small, non-
//          negative, bit-identical in i32/i64/i128) and only using in-range
//          signed constants.
//        - UNSIGNED compares are oracle-valid only when operands are
//          non-negative AND fit the width (so `as u128` == width-w unsigned).
//          Our masked operands (& 0xffff) and the constants we feed unsigned
//          compares satisfy this. Wide/high-bit-set unsigned operands would NOT
//          be oracle-comparable; we simply do not feed them to the oracle here.
//
//  (B) Overflow flag is HARD-CODED to false in the interpreter (see the
//      `Inst::Overflow` arm: "Overflow flag (simplified: always false for
//      now)"). The interpreter is therefore NOT a valid oracle for the overflow
//      FLAG. A divergence "oracle flag=false vs JIT flag=true" is an interpreter
//      simplification, NOT a codegen defect. So for every overflow-flag idiom we
//      DO NOT consult the interpreter; instead we use:
//        - cross-config JIT agreement (all 8 configs must agree), and
//        - a native-Rust ground truth (overflowing_add/sub/mul at the width).
//      The overflow RESULT word (wrapping_add/sub/mul) *is* faithfully modeled,
//      but we keep flag idioms entirely on the JIT-agreement + Rust-truth path to
//      avoid any ambiguity.
//
//  (C) The interpreter's widthless cast model leaves `sext Bool -> i64` true as
//      raw `1`, while native one-bit sign extension yields `-1`. Such shapes use
//      the shared domain-checked projection for native truth. A direct self-check
//      below pins raw interpreter false/true to 0/1 and native projection to
//      0/-1. Modules that combine Bool SExt with unsupported memory operations
//      remain on the cross-JIT + native-truth lane rather than claiming oracle
//      comparability.
//
// ============================ ANTI-FALSE-POSITIVE ===========================
//   * All arithmetic is wrapping (Rust ground truth uses wrapping_*).
//   * Divisors, if any, are forced nonzero (none used here).
//   * Shift amounts are constants in 0..width (none dynamic here).
//   * No floats.
//   * Memory: a single i64 alloca slot, written before read, never OOB.
//   * Every narrow / Bool result is widened to i64 before `ret`, so the compared
//     value is always fully defined.
//
// Entry is always `fuzz_fn` : (i64,i64,i64,i64) -> i64. We compile each module
// at O0/O1/O2/O3 x {jit_fast(host), for_host_jit w/ fast_regalloc=false} = 8
// configs. A DEFECT is any disagreement among DEFINED values (oracle vs any JIT,
// or JIT vs JIT) or a compile-error / panic on an oracle-accepted module.

#![cfg(target_arch = "aarch64")]

use std::collections::HashMap;
use std::panic;

use trust_cg_codegen::Target;
use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_fuzz::jit_diff::{project_widthless_bool_sext_i64, run_oracle_one};
use trust_ir::{BinOp, ICmpOp, OverflowOp, Ty};
use trust_ir_build::{FunctionBuilder, ModuleBuilder};

const ENTRY: &str = "fuzz_fn";

const OPTS: [OptLevel; 4] = [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3];

const ALL_CMPS: [ICmpOp; 10] = [
    ICmpOp::Eq,
    ICmpOp::Ne,
    ICmpOp::Ult,
    ICmpOp::Ule,
    ICmpOp::Ugt,
    ICmpOp::Uge,
    ICmpOp::Slt,
    ICmpOp::Sle,
    ICmpOp::Sgt,
    ICmpOp::Sge,
];

// ---------------------------------------------------------------------------
// JIT execution: 8 configs (4 opt levels x 2 regalloc modes).
// ---------------------------------------------------------------------------

#[derive(Clone, Copy, Debug, PartialEq)]
enum Run {
    Value(i64),
    CompileErr,
    SymbolMissing,
    Panic,
}

fn jit_run(module: &trust_ir::Module, opt: OptLevel, jit_fast: bool, row: &[i64; 4]) -> Run {
    let res = panic::catch_unwind(panic::AssertUnwindSafe(|| {
        let externs: HashMap<String, *const u8> = HashMap::new();
        let mut config = if jit_fast {
            CompilerConfig::jit_fast(Target::host())
        } else {
            let mut c = CompilerConfig::for_host_jit();
            c.enable_jit_fast_regalloc = false;
            c
        };
        config.opt_level = opt;
        let compiler = Compiler::new(config);
        let buf = match compiler.compile_module_to_jit(module, &externs) {
            Ok(r) => r.buffer,
            Err(_) => return Run::CompileErr,
        };
        type Fn4 = extern "C" fn(i64, i64, i64, i64) -> i64;
        let fptr = match unsafe { buf.get_fn_bound::<Fn4>(ENTRY) } {
            Some(p) => p.into_inner(),
            None => return Run::SymbolMissing,
        };
        let v = fptr(row[0], row[1], row[2], row[3]);
        drop(buf);
        Run::Value(v)
    }));
    res.unwrap_or(Run::Panic)
}

/// Run a module across all 8 JIT configs, collecting compile/panic defects.
fn run_all_jit(
    module: &trust_ir::Module,
    row: &[i64; 4],
    label: &str,
    defects: &mut Vec<String>,
) -> Vec<((bool, OptLevel), i64)> {
    let mut out = Vec::new();
    for jit_fast in [true, false] {
        for opt in OPTS {
            match jit_run(module, opt, jit_fast, row) {
                Run::Value(v) => out.push(((jit_fast, opt), v)),
                Run::CompileErr => defects.push(format!(
                    "COMPILE_ERR {label} row={row:?} fast={jit_fast} opt={opt:?}"
                )),
                Run::SymbolMissing => defects.push(format!(
                    "SYMBOL_MISSING {label} row={row:?} fast={jit_fast} opt={opt:?}"
                )),
                Run::Panic => defects.push(format!(
                    "PANIC {label} row={row:?} fast={jit_fast} opt={opt:?}"
                )),
            }
        }
    }
    out
}

/// Full differential check: cross-JIT agreement always; oracle and/or a
/// native-Rust ground truth when supplied.
fn check(
    module: &trust_ir::Module,
    row: &[i64; 4],
    label: &str,
    consult_oracle: bool,
    rust_truth: Option<i64>,
    defects: &mut Vec<String>,
) {
    let jits = run_all_jit(module, row, label, defects);
    if jits.is_empty() {
        return;
    }
    // Cross-JIT agreement (oracle-free): all 8 configs must agree.
    let (ref_key, ref_val) = jits[0];
    for &(key, val) in &jits[1..] {
        if val != ref_val {
            defects.push(format!(
                "JIT_DISAGREE {label} row={row:?}: {ref_key:?}={ref_val} vs {key:?}={val}"
            ));
        }
    }
    // Native-Rust ground truth (always valid; independent of the interpreter).
    if let Some(want) = rust_truth {
        for &(key, val) in &jits {
            if val != want {
                defects.push(format!(
                    "RUST_TRUTH {label} row={row:?} {key:?}: jit={val} rust={want}"
                ));
            }
        }
    }
    // Interpreter-oracle agreement (only when provably comparable).
    if consult_oracle && let Ok(ov) = run_oracle_one(module, row) {
        for &(key, val) in &jits {
            if val != ov {
                defects.push(format!(
                    "MISCOMPILE {label} row={row:?} {key:?}: jit={val} oracle={ov}"
                ));
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Module-builder helper: 4 x i64 entry params, body returns one i64.
// The closure receives the FunctionBuilder, the entry block, and the 4 params.
// ---------------------------------------------------------------------------

fn build_module<F>(name: &str, body: F) -> trust_ir::Module
where
    F: FnOnce(&mut FunctionBuilder, trust_ir::BlockId, [trust_ir::ValueId; 4]),
{
    let mut mb = ModuleBuilder::new(name);
    let ty = mb.add_func_type(vec![Ty::I64; 4], vec![Ty::I64]);
    let mut fb = mb.function(ENTRY, ty);
    let entry = fb.create_block(); // BlockId(0) == default entry
    let a = fb.add_block_param(entry, Ty::I64);
    let b = fb.add_block_param(entry, Ty::I64);
    let c = fb.add_block_param(entry, Ty::I64);
    let d = fb.add_block_param(entry, Ty::I64);
    fb.switch_to_block(entry);
    body(&mut fb, entry, [a, b, c, d]);
    fb.build();
    mb.build()
}

/// Mask an i64 param down to a small non-negative value (0..=0xffff) that is
/// bit-identical in i32/i64/i128, hence oracle-valid for BOTH signed and
/// unsigned compares.
fn canon(fb: &mut FunctionBuilder, p: trust_ir::ValueId) -> trust_ir::ValueId {
    let mask = fb.iconst(Ty::I64, 0xffff);
    fb.binop(BinOp::And, Ty::I64, p, mask)
}

const ROWS: &[[i64; 4]] = &[
    [0, 0, 0, 0],
    [1, 1, 1, 1],
    [1, 2, 3, 4],
    [4, 3, 2, 1],
    [0, 1, 0, 1],
    [1, 0, 1, 0],
    [0xffff, 0, 0xffff, 0],
    [0x1234, 0x4321, 0x7fff, 0x8000],
    [5, 5, 7, 7],
    [0xabcd, 0x1234, 0x0001, 0xfffe],
    [-1, -1, -1, -1],
    [i64::MAX, i64::MIN, 0, -1],
    [i64::MIN, i64::MAX, -1, 0],
    [0x7fff_ffff, 0x8000_0000, 0xffff_ffff, 7],
    [100, 200, 300, 400],
];

// Native-Rust width-w canonicalization mirroring `canon` (param & 0xffff).
fn r_canon(p: i64) -> i64 {
    p & 0xffff
}

// ===========================================================================
// SELF-CHECK: prove the oracle is live, correct, and sensitive (no vacuous
// passes), and that the JITs agree with it on a representative fusion shape.
// ===========================================================================

#[test]
fn selfcheck_oracle_live_and_sensitive() {
    // r = if (a < b) signed { c } else { d }, via icmp + condbr to two return
    // blocks (the canonical fusion shape).
    let m = build_module("sc_condbr", |fb, _e, p| {
        let av = canon(fb, p[0]);
        let bv = canon(fb, p[1]);
        let cmp = fb.icmp(ICmpOp::Slt, Ty::I64, av, bv);
        let tb = fb.create_block();
        let eb = fb.create_block();
        fb.condbr(cmp, tb, vec![], eb, vec![]);
        fb.switch_to_block(tb);
        fb.ret(vec![p[2]]);
        fb.switch_to_block(eb);
        fb.ret(vec![p[3]]);
    });
    // a=1<b=2 -> true -> return c(=10).
    let row = [1i64, 2, 10, 20];
    let ov = run_oracle_one(&m, &row).expect("oracle must accept condbr-fusion module");
    assert_eq!(ov, 10, "1<2 -> then-arm c, got {ov}");
    let jits = run_all_jit(&m, &row, "selfcheck", &mut Vec::new());
    assert_eq!(jits.len(), 8, "all 8 JIT configs should produce a value");
    for (k, v) in &jits {
        assert_eq!(*v, 10, "JIT {k:?} should agree with oracle (10), got {v}");
    }
    // Sensitivity: flip so the comparison is false -> else-arm d(=20).
    let row2 = [5i64, 2, 10, 20];
    assert_eq!(
        run_oracle_one(&m, &row2).unwrap(),
        20,
        "5<2 false -> else-arm d"
    );
    let jits2 = run_all_jit(&m, &row2, "selfcheck2", &mut Vec::new());
    for (k, v) in &jits2 {
        assert_eq!(*v, 20, "JIT {k:?} should return else-arm (20), got {v}");
    }
}

#[test]
fn bool_sext_oracle_model_is_live_and_projected() {
    // Keep this module memory-free so the interpreter actually executes the
    // Bool SExt. The store/reload sweep below is intentionally oracle-free
    // because the lightweight interpreter does not implement alloca memory.
    let m = build_module("sc_bool_sext", |fb, _e, p| {
        let av = canon(fb, p[0]);
        let bv = canon(fb, p[1]);
        let cmp = fb.icmp(ICmpOp::Slt, Ty::I64, av, bv);
        let w = fb.sext(Ty::Bool, Ty::I64, cmp);
        fb.ret(vec![w]);
    });

    let true_row = [1i64, 2, 0, 0];
    let raw_true =
        run_oracle_one(&m, &true_row).expect("widthless interpreter must accept true Bool SExt");
    assert_eq!(raw_true, 1, "widthless interpreter true changed");
    assert_eq!(project_widthless_bool_sext_i64(raw_true), Some(-1));

    let false_row = [2i64, 1, 0, 0];
    let raw_false =
        run_oracle_one(&m, &false_row).expect("widthless interpreter must accept false Bool SExt");
    assert_eq!(raw_false, 0, "widthless interpreter false changed");
    assert_eq!(project_widthless_bool_sext_i64(raw_false), Some(0));

    for (label, row, want) in [
        ("bool-sext-true", true_row, -1),
        ("bool-sext-false", false_row, 0),
    ] {
        let mut defects = Vec::new();
        let jits = run_all_jit(&m, &row, label, &mut defects);
        assert!(defects.is_empty(), "{defects:?}");
        assert_eq!(jits.len(), 8, "all 8 JIT configs must execute {label}");
        for (key, got) in jits {
            assert_eq!(got, want, "JIT {key:?} disagrees for {label}");
        }
    }
}

// ===========================================================================
// 1. icmp -> condbr fusion: each predicate, then-arm returns A, else-arm B.
//    Sweeps both "return a value picked per-arm" and "return a value computed
//    per-arm" so the branch is not trivially foldable.
// ===========================================================================

#[test]
fn icmp_condbr_fusion_simple() {
    let mut defects = Vec::new();
    let mut configs = 0usize;
    for &op in &ALL_CMPS {
        // r = if (a <op> b) { c+1 } else { d^7 }  (wrapping, distinct arms)
        let m = build_module("condbr_fuse", |fb, _e, p| {
            let av = canon(fb, p[0]);
            let bv = canon(fb, p[1]);
            let cmp = fb.icmp(op, Ty::I64, av, bv);
            let tb = fb.create_block();
            let eb = fb.create_block();
            fb.condbr(cmp, tb, vec![], eb, vec![]);
            fb.switch_to_block(tb);
            let one = fb.iconst(Ty::I64, 1);
            let t = fb.binop(BinOp::Add, Ty::I64, p[2], one);
            fb.ret(vec![t]);
            fb.switch_to_block(eb);
            let seven = fb.iconst(Ty::I64, 7);
            let e = fb.binop(BinOp::Xor, Ty::I64, p[3], seven);
            fb.ret(vec![e]);
        });
        let label = format!("condbr_fuse {op:?}");
        configs += 1;
        for row in ROWS {
            let av = r_canon(row[0]);
            let bv = r_canon(row[1]);
            let taken = eval_icmp_rs(op, av, bv);
            let want = if taken {
                row[2].wrapping_add(1)
            } else {
                row[3] ^ 7
            };
            check(&m, row, &label, true, Some(want), &mut defects);
        }
    }
    report("icmp_condbr_fusion_simple", configs, &defects);
}

// ===========================================================================
// 2. compare-and-select: select(cmp, then, else). Both value-select and the
//    arithmetic-on-each-side variant.
// ===========================================================================

#[test]
fn compare_and_select() {
    let mut defects = Vec::new();
    let mut configs = 0usize;
    for &op in &ALL_CMPS {
        // r = select(a <op> b, c, d)
        let m_val = build_module("sel_val", |fb, _e, p| {
            let av = canon(fb, p[0]);
            let bv = canon(fb, p[1]);
            let cmp = fb.icmp(op, Ty::I64, av, bv);
            let r = fb.select(Ty::I64, cmp, p[2], p[3]);
            fb.ret(vec![r]);
        });
        // r = select(a <op> b, c+d, c-d) (wrapping)
        let m_arith = build_module("sel_arith", |fb, _e, p| {
            let av = canon(fb, p[0]);
            let bv = canon(fb, p[1]);
            let cmp = fb.icmp(op, Ty::I64, av, bv);
            let sum = fb.binop(BinOp::Add, Ty::I64, p[2], p[3]);
            let dif = fb.binop(BinOp::Sub, Ty::I64, p[2], p[3]);
            let r = fb.select(Ty::I64, cmp, sum, dif);
            fb.ret(vec![r]);
        });
        configs += 2;
        for row in ROWS {
            let taken = eval_icmp_rs(op, r_canon(row[0]), r_canon(row[1]));
            let want_val = if taken { row[2] } else { row[3] };
            check(
                &m_val,
                row,
                &format!("sel_val {op:?}"),
                true,
                Some(want_val),
                &mut defects,
            );
            let want_arith = if taken {
                row[2].wrapping_add(row[3])
            } else {
                row[2].wrapping_sub(row[3])
            };
            check(
                &m_arith,
                row,
                &format!("sel_arith {op:?}"),
                true,
                Some(want_arith),
                &mut defects,
            );
        }
    }
    report("compare_and_select", configs, &defects);
}

// ===========================================================================
// 3. chained comparisons: short-circuit && / || as cmp -> condbr -> cmp ->
//    condbr, plus a diamond that merges via a block param (phi). Exercises the
//    fusion path across multiple basic blocks.
// ===========================================================================

#[test]
fn chained_short_circuit_and() {
    // r = if (a < b) && (c < d) { 111 } else { 222 }
    // Implemented: cmp1; condbr -> [check2 | else]; in check2: cmp2; condbr ->
    // [then | else]; then returns 111, else returns 222.
    let mut defects = Vec::new();
    let mut configs = 0usize;
    for &op1 in &ALL_CMPS {
        for &op2 in &[ICmpOp::Slt, ICmpOp::Ugt, ICmpOp::Eq, ICmpOp::Ne] {
            let m = build_module("and_chain", |fb, _e, p| {
                let av = canon(fb, p[0]);
                let bv = canon(fb, p[1]);
                let cv = canon(fb, p[2]);
                let dv = canon(fb, p[3]);
                let c1 = fb.icmp(op1, Ty::I64, av, bv);
                let check2 = fb.create_block();
                let then_b = fb.create_block();
                let else_b = fb.create_block();
                // if !c1 go straight to else (short-circuit).
                fb.condbr(c1, check2, vec![], else_b, vec![]);
                fb.switch_to_block(check2);
                let c2 = fb.icmp(op2, Ty::I64, cv, dv);
                fb.condbr(c2, then_b, vec![], else_b, vec![]);
                fb.switch_to_block(then_b);
                let t = fb.iconst(Ty::I64, 111);
                fb.ret(vec![t]);
                fb.switch_to_block(else_b);
                let e = fb.iconst(Ty::I64, 222);
                fb.ret(vec![e]);
            });
            configs += 1;
            let label = format!("and_chain {op1:?}&&{op2:?}");
            for row in ROWS {
                let lhs = eval_icmp_rs(op1, r_canon(row[0]), r_canon(row[1]));
                let rhs = eval_icmp_rs(op2, r_canon(row[2]), r_canon(row[3]));
                let want = if lhs && rhs { 111 } else { 222 };
                check(&m, row, &label, true, Some(want), &mut defects);
            }
        }
    }
    report("chained_short_circuit_and", configs, &defects);
}

#[test]
fn chained_short_circuit_or_diamond() {
    // r = if (a < b) || (c < d) { e1 } else { e2 }, but the two arms MERGE at a
    // join block that takes an i64 block param (phi), then returns it. Exercises
    // condbr feeding a join with block-param argument passing.
    let mut defects = Vec::new();
    let mut configs = 0usize;
    for &op1 in &ALL_CMPS {
        for &op2 in &[ICmpOp::Slt, ICmpOp::Uge, ICmpOp::Ne] {
            let m = build_module("or_diamond", |fb, _e, p| {
                let av = canon(fb, p[0]);
                let bv = canon(fb, p[1]);
                let cv = canon(fb, p[2]);
                let dv = canon(fb, p[3]);
                let c1 = fb.icmp(op1, Ty::I64, av, bv);
                let check2 = fb.create_block();
                let then_b = fb.create_block();
                let else_b = fb.create_block();
                let join = fb.create_block();
                let jp = fb.add_block_param(join, Ty::I64);
                // if c1 short-circuit straight to then.
                fb.condbr(c1, then_b, vec![], check2, vec![]);
                fb.switch_to_block(check2);
                let c2 = fb.icmp(op2, Ty::I64, cv, dv);
                fb.condbr(c2, then_b, vec![], else_b, vec![]);
                fb.switch_to_block(then_b);
                // then value = a+c (wrapping), passed to join.
                let tv = fb.binop(BinOp::Add, Ty::I64, p[0], p[2]);
                fb.br(join, vec![tv]);
                fb.switch_to_block(else_b);
                // else value = b-d (wrapping), passed to join.
                let ev = fb.binop(BinOp::Sub, Ty::I64, p[1], p[3]);
                fb.br(join, vec![ev]);
                fb.switch_to_block(join);
                fb.ret(vec![jp]);
            });
            configs += 1;
            let label = format!("or_diamond {op1:?}||{op2:?}");
            for row in ROWS {
                let lhs = eval_icmp_rs(op1, r_canon(row[0]), r_canon(row[1]));
                let rhs = eval_icmp_rs(op2, r_canon(row[2]), r_canon(row[3]));
                let want = if lhs || rhs {
                    row[0].wrapping_add(row[2])
                } else {
                    row[1].wrapping_sub(row[3])
                };
                check(&m, row, &label, true, Some(want), &mut defects);
            }
        }
    }
    report("chained_short_circuit_or_diamond", configs, &defects);
}

// ===========================================================================
// 4. boolean materialization to i64, STORED and RELOADED, then branched/used.
//    zext/sext(cmp) -> i64 -> store to alloca -> load -> consume.
// ===========================================================================

// `zext Bool -> i64` materializes 0/1; `sext Bool -> i64` materializes 0/-1.
// The slot store/load are full-width I64 operations, so that distinction must
// survive memory and the following arithmetic under every allocator/opt level.
#[test]
fn bool_materialize_store_reload() {
    let mut defects = Vec::new();
    let mut configs = 0usize;
    for &op in &ALL_CMPS {
        for sext in [false, true] {
            // w = (zext|sext)(a<op>b); store w; reload w; return reload + c
            let module = build_bool_store(op, sext);
            configs += 1;
            let label = format!("bool_store {op:?} sext={sext}");
            for row in ROWS {
                let taken = eval_icmp_rs(op, r_canon(row[0]), r_canon(row[1]));
                let raw_bool = i64::from(taken);
                let w = if sext {
                    project_widthless_bool_sext_i64(raw_bool)
                        .expect("comparison truth must remain in the Bool domain")
                } else {
                    raw_bool
                };
                let want = w.wrapping_add(row[2]);
                // The lightweight interpreter does not implement the alloca
                // used by this shape. Cross-JIT agreement plus independent
                // native truth is the authoritative lane here; the memory-free
                // self-check above separately pins the raw oracle contract.
                check(&module, row, &label, false, Some(want), &mut defects);
            }
        }
    }
    report("bool_materialize_store_reload", configs, &defects);
}

/// Build the bool-store-reload module: w = (zext|sext)(a<op>b); store w to an
/// i64 slot; reload; return reload + c.
fn build_bool_store(op: ICmpOp, sext: bool) -> trust_ir::Module {
    build_module("bool_store", |fb, _e, p| {
        let av = canon(fb, p[0]);
        let bv = canon(fb, p[1]);
        let cmp = fb.icmp(op, Ty::I64, av, bv);
        let w = if sext {
            fb.sext(Ty::Bool, Ty::I64, cmp)
        } else {
            fb.zext(Ty::Bool, Ty::I64, cmp)
        };
        let slot = fb.alloca(Ty::I64);
        fb.store(Ty::I64, slot, w);
        let r = fb.load(Ty::I64, slot);
        let out = fb.binop(BinOp::Add, Ty::I64, r, p[2]);
        fb.ret(vec![out]);
    })
}

#[test]
fn bool_stored_then_branched() {
    // Materialize the bool to i64, store, reload, then condbr on the reloaded
    // word being nonzero (icmp ne 0) — bool round-trips through memory and back
    // into the fusion path.
    let mut defects = Vec::new();
    let mut configs = 0usize;
    for &op in &ALL_CMPS {
        let m = build_module("store_then_branch", |fb, _e, p| {
            let av = canon(fb, p[0]);
            let bv = canon(fb, p[1]);
            let cmp = fb.icmp(op, Ty::I64, av, bv);
            let w = fb.zext(Ty::Bool, Ty::I64, cmp);
            let slot = fb.alloca(Ty::I64);
            fb.store(Ty::I64, slot, w);
            let r = fb.load(Ty::I64, slot);
            let zero = fb.iconst(Ty::I64, 0);
            let nz = fb.icmp(ICmpOp::Ne, Ty::I64, r, zero);
            let tb = fb.create_block();
            let eb = fb.create_block();
            fb.condbr(nz, tb, vec![], eb, vec![]);
            fb.switch_to_block(tb);
            fb.ret(vec![p[2]]);
            fb.switch_to_block(eb);
            fb.ret(vec![p[3]]);
        });
        configs += 1;
        let label = format!("store_then_branch {op:?}");
        for row in ROWS {
            let taken = eval_icmp_rs(op, r_canon(row[0]), r_canon(row[1]));
            let want = if taken { row[2] } else { row[3] };
            check(&m, row, &label, true, Some(want), &mut defects);
        }
    }
    report("bool_stored_then_branched", configs, &defects);
}

// ===========================================================================
// 5. overflow-flag idioms: add/sub/mul-then-check. ORACLE-FREE (interpreter
//    hard-codes the flag to false; see ORACLE CONTRACT (B)). We use cross-JIT
//    agreement + native-Rust overflowing_* ground truth at the operand width.
//    Both the RESULT word and the FLAG-driven branch/select are checked.
// ===========================================================================

#[derive(Clone, Copy)]
enum OfWidth {
    I32,
    I64,
}

fn of_ty(w: OfWidth) -> Ty {
    match w {
        OfWidth::I32 => Ty::I32,
        OfWidth::I64 => Ty::I64,
    }
}

/// Native-Rust overflowing op at the chosen width. Returns (result_word_as_i64,
/// overflow_flag). The result word is the wrapping result re-widened to i64 the
/// same way the lowering would (i32 results sign-extended to i64 on return is
/// not assumed; instead the module itself zero/sign-extends explicitly, see the
/// builder — here we mirror that explicit extension).
fn rust_overflow(op: OverflowOp, w: OfWidth, a: i64, b: i64) -> (i64, bool) {
    match w {
        OfWidth::I32 => {
            let x = a as i32;
            let y = b as i32;
            let (r, o) = match op {
                OverflowOp::AddOverflow => x.overflowing_add(y),
                OverflowOp::SubOverflow => x.overflowing_sub(y),
                OverflowOp::MulOverflow => x.overflowing_mul(y),
            };
            // module sign-extends the i32 result to i64 before use.
            (r as i64, o)
        }
        OfWidth::I64 => {
            let (r, o) = match op {
                OverflowOp::AddOverflow => a.overflowing_add(b),
                OverflowOp::SubOverflow => a.overflowing_sub(b),
                OverflowOp::MulOverflow => a.overflowing_mul(b),
            };
            (r, o)
        }
    }
}

/// Operands for the overflow probes. For i32 we feed the low 32 bits of each row
/// value (so the i32 op sees a real i32). For i64 we feed the full value.
fn of_operands(w: OfWidth, row: &[i64; 4]) -> (i64, i64) {
    match w {
        OfWidth::I32 => (row[0] as i32 as i64, row[1] as i32 as i64),
        OfWidth::I64 => (row[0], row[1]),
    }
}

#[test]
fn overflow_flag_branch_idiom() {
    // r = { let (v, ovf) = op(a, b); if ovf { sat_const } else { v } }
    // The flag drives a condbr; the result word flows into the then/else arms.
    let mut defects = Vec::new();
    let mut configs = 0usize;
    let sat: i64 = 0x7abc_def0_1234_5678; // arbitrary saturation marker
    for &op in &[
        OverflowOp::AddOverflow,
        OverflowOp::SubOverflow,
        OverflowOp::MulOverflow,
    ] {
        for &w in &[OfWidth::I32, OfWidth::I64] {
            let m = build_module("ovf_branch", |fb, _e, p| {
                let ty = of_ty(w);
                // Build width-correct operands: for i32, truncate the i64 param.
                let (la, lb) = match w {
                    OfWidth::I32 => (
                        fb.trunc(Ty::I64, Ty::I32, p[0]),
                        fb.trunc(Ty::I64, Ty::I32, p[1]),
                    ),
                    OfWidth::I64 => (p[0], p[1]),
                };
                let (res, flag) = fb.overflow(op, ty.clone(), la, lb);
                // widen the result word to i64 (sext for signed overflow ops).
                let res64 = match w {
                    OfWidth::I32 => fb.sext(Ty::I32, Ty::I64, res),
                    OfWidth::I64 => res,
                };
                let tb = fb.create_block();
                let eb = fb.create_block();
                fb.condbr(flag, tb, vec![], eb, vec![]);
                fb.switch_to_block(tb);
                let s = fb.iconst(Ty::I64, sat as i128);
                fb.ret(vec![s]);
                fb.switch_to_block(eb);
                fb.ret(vec![res64]);
            });
            configs += 1;
            let label = format!("ovf_branch {op:?} {}", width_name(w));
            for row in ROWS {
                let (a, b) = of_operands(w, row);
                let (res64, ovf) = rust_overflow(op, w, a, b);
                let want = if ovf { sat } else { res64 };
                // ORACLE-FREE: flag is not modeled by the interpreter.
                check(&m, row, &label, false, Some(want), &mut defects);
            }
        }
    }
    report("overflow_flag_branch_idiom", configs, &defects);
}

#[test]
fn overflow_flag_select_idiom() {
    // r = select(ovf_flag, c, result_word). select fed by the overflow flag.
    let mut defects = Vec::new();
    let mut configs = 0usize;
    for &op in &[
        OverflowOp::AddOverflow,
        OverflowOp::SubOverflow,
        OverflowOp::MulOverflow,
    ] {
        for &w in &[OfWidth::I32, OfWidth::I64] {
            let m = build_module("ovf_select", |fb, _e, p| {
                let ty = of_ty(w);
                let (la, lb) = match w {
                    OfWidth::I32 => (
                        fb.trunc(Ty::I64, Ty::I32, p[0]),
                        fb.trunc(Ty::I64, Ty::I32, p[1]),
                    ),
                    OfWidth::I64 => (p[0], p[1]),
                };
                let (res, flag) = fb.overflow(op, ty.clone(), la, lb);
                let res64 = match w {
                    OfWidth::I32 => fb.sext(Ty::I32, Ty::I64, res),
                    OfWidth::I64 => res,
                };
                let r = fb.select(Ty::I64, flag, p[2], res64);
                fb.ret(vec![r]);
            });
            configs += 1;
            let label = format!("ovf_select {op:?} {}", width_name(w));
            for row in ROWS {
                let (a, b) = of_operands(w, row);
                let (res64, ovf) = rust_overflow(op, w, a, b);
                let want = if ovf { row[2] } else { res64 };
                check(&m, row, &label, false, Some(want), &mut defects);
            }
        }
    }
    report("overflow_flag_select_idiom", configs, &defects);
}

#[test]
fn overflow_flag_materialized_to_i64() {
    // r = zext(ovf_flag) -> i64 (0/1), stored and reloaded, then returned. Pure
    // flag round-trip through memory. ORACLE-FREE.
    let mut defects = Vec::new();
    let mut configs = 0usize;
    for &op in &[
        OverflowOp::AddOverflow,
        OverflowOp::SubOverflow,
        OverflowOp::MulOverflow,
    ] {
        for &w in &[OfWidth::I32, OfWidth::I64] {
            let m = build_module("ovf_flag_word", |fb, _e, p| {
                let ty = of_ty(w);
                let (la, lb) = match w {
                    OfWidth::I32 => (
                        fb.trunc(Ty::I64, Ty::I32, p[0]),
                        fb.trunc(Ty::I64, Ty::I32, p[1]),
                    ),
                    OfWidth::I64 => (p[0], p[1]),
                };
                let (_res, flag) = fb.overflow(op, ty.clone(), la, lb);
                let word = fb.zext(Ty::Bool, Ty::I64, flag);
                let slot = fb.alloca(Ty::I64);
                fb.store(Ty::I64, slot, word);
                let r = fb.load(Ty::I64, slot);
                fb.ret(vec![r]);
            });
            configs += 1;
            let label = format!("ovf_flag_word {op:?} {}", width_name(w));
            for row in ROWS {
                let (a, b) = of_operands(w, row);
                let (_res, ovf) = rust_overflow(op, w, a, b);
                let want = if ovf { 1 } else { 0 };
                check(&m, row, &label, false, Some(want), &mut defects);
            }
        }
    }
    report("overflow_flag_materialized_to_i64", configs, &defects);
}

fn width_name(w: OfWidth) -> &'static str {
    match w {
        OfWidth::I32 => "i32",
        OfWidth::I64 => "i64",
    }
}

// ===========================================================================
// 6. The canonical i128-WIDENED signed-overflow idiom feeding a condbr / select.
//
//    sum      = add|sub(I64,  a, b)
//    sa       = sext(I64 -> I128, a)
//    sb       = sext(I64 -> I128, b)
//    true_sum = add|sub(I128, sa, sb)
//    ssum     = sext(I64 -> I128, sum)
//    overflow = icmp Ne(I128, ssum, true_sum)     // true iff signed overflow
//    condbr overflow -> ... | ...                 (or: select(overflow, ...))
//
// This is EXACTLY the pattern `trust-cg-lower/src/overflow_idiom.rs` recognises
// and fuses into a single flag-setting `ADDS/SUBS` + `B.VS` (branch) or
// `ADDS/SUBS` + `CSET VS` (materialise) on aarch64. It is the highest-value
// fusion shape on this surface and is NOT covered by the OverflowOp-instruction
// tests above (which the interpreter cannot model — its flag is hard-coded
// false). This idiom, in contrast, IS oracle-comparable: the interpreter does
// full i128 add/sub and an exact i128 Ne compare, so `sext(sum) != sext(a)±sext(b)`
// evaluates to the true signed-overflow predicate. We therefore get a THREE-way
// cross-check — interpreter oracle, native-Rust `overflowing_*`, and all 8 JIT
// configs — on the fused compare/branch path. A mis-detected idiom, a wrong V
// flag, or a wrong branch target shows up immediately as a defect.
//
// Inputs are the FULL i64 range (no masking), so the operands actually exercise
// real signed overflow at the i64 boundary (i64::MAX + 1, i64::MIN - 1, etc.).
// The i128 ops and the i128 Ne compare are oracle-exact for any i64 operand, so
// consult_oracle = true is sound here even with high-bit-set operands.
// ===========================================================================

#[derive(Clone, Copy, Debug)]
enum WideKind {
    Add,
    Sub,
}

fn wide_binop(k: WideKind) -> BinOp {
    match k {
        WideKind::Add => BinOp::Add,
        WideKind::Sub => BinOp::Sub,
    }
}

/// Emit the i128-widened signed-overflow idiom for `op(a, b)`, returning
/// `(sum_i64, overflow_bool)`.
fn emit_widened_overflow(
    fb: &mut FunctionBuilder,
    k: WideKind,
    a: trust_ir::ValueId,
    b: trust_ir::ValueId,
) -> (trust_ir::ValueId, trust_ir::ValueId) {
    let bin = wide_binop(k);
    let sum = fb.binop(bin, Ty::I64, a, b);
    let sa = fb.sext(Ty::I64, Ty::I128, a);
    let sb = fb.sext(Ty::I64, Ty::I128, b);
    let true_sum = fb.binop(bin, Ty::I128, sa, sb);
    let ssum = fb.sext(Ty::I64, Ty::I128, sum);
    let overflow = fb.icmp(ICmpOp::Ne, Ty::I128, ssum, true_sum);
    (sum, overflow)
}

/// Native-Rust ground truth for the widened overflow idiom: (sum, overflow).
fn rust_widened_overflow(k: WideKind, a: i64, b: i64) -> (i64, bool) {
    match k {
        WideKind::Add => a.overflowing_add(b),
        WideKind::Sub => a.overflowing_sub(b),
    }
}

#[test]
fn widened_overflow_idiom_condbr_fusion() {
    // r = if signed_overflow(a op b) { sum ^ c } else { sum + d }
    // The fused ADDS/SUBS + B.VS path must pick the right arm AND keep `sum`
    // live (the narrow result is consumed in both arms).
    let mut defects = Vec::new();
    let mut configs = 0usize;
    for k in [WideKind::Add, WideKind::Sub] {
        let m = build_module("widened_ovf_condbr", |fb, _e, p| {
            let (sum, overflow) = emit_widened_overflow(fb, k, p[0], p[1]);
            let tb = fb.create_block();
            let eb = fb.create_block();
            fb.condbr(overflow, tb, vec![], eb, vec![]);
            fb.switch_to_block(tb);
            let t = fb.binop(BinOp::Xor, Ty::I64, sum, p[2]);
            fb.ret(vec![t]);
            fb.switch_to_block(eb);
            let e = fb.binop(BinOp::Add, Ty::I64, sum, p[3]);
            fb.ret(vec![e]);
        });
        configs += 1;
        let label = format!("widened_ovf_condbr {k:?}");
        for row in ROWS {
            let (sum, ovf) = rust_widened_overflow(k, row[0], row[1]);
            let want = if ovf {
                sum ^ row[2]
            } else {
                sum.wrapping_add(row[3])
            };
            // ORACLE-COMPARABLE: the idiom is pure i128 arithmetic + i128 Ne.
            check(&m, row, &label, true, Some(want), &mut defects);
        }
    }
    report("widened_overflow_idiom_condbr_fusion", configs, &defects);
}

#[test]
fn widened_overflow_idiom_select_and_materialize() {
    // Two non-branch consumers of the idiom's overflow boolean, which force the
    // selector down the `needs_cset_fallback` path (V flag materialised via
    // CSET VS rather than consumed directly by a Brif):
    //   (a) r = select(overflow, sum ^ c, sum + d)
    //   (b) r = zext(overflow) -> i64, returned directly (0/1 flag word).
    let mut defects = Vec::new();
    let mut configs = 0usize;
    for k in [WideKind::Add, WideKind::Sub] {
        // (a) select on the flag.
        let m_sel = build_module("widened_ovf_select", |fb, _e, p| {
            let (sum, overflow) = emit_widened_overflow(fb, k, p[0], p[1]);
            let t = fb.binop(BinOp::Xor, Ty::I64, sum, p[2]);
            let e = fb.binop(BinOp::Add, Ty::I64, sum, p[3]);
            let r = fb.select(Ty::I64, overflow, t, e);
            fb.ret(vec![r]);
        });
        // (b) materialise the flag to a 0/1 i64 word.
        let m_mat = build_module("widened_ovf_word", |fb, _e, p| {
            let (_sum, overflow) = emit_widened_overflow(fb, k, p[0], p[1]);
            let w = fb.zext(Ty::Bool, Ty::I64, overflow);
            fb.ret(vec![w]);
        });
        configs += 2;
        let sel_label = format!("widened_ovf_select {k:?}");
        let mat_label = format!("widened_ovf_word {k:?}");
        for row in ROWS {
            let (sum, ovf) = rust_widened_overflow(k, row[0], row[1]);
            let want_sel = if ovf {
                sum ^ row[2]
            } else {
                sum.wrapping_add(row[3])
            };
            check(&m_sel, row, &sel_label, true, Some(want_sel), &mut defects);
            let want_mat = if ovf { 1 } else { 0 };
            check(&m_mat, row, &mat_label, true, Some(want_mat), &mut defects);
        }
    }
    report(
        "widened_overflow_idiom_select_and_materialize",
        configs,
        &defects,
    );
}

/// Self-check: the interpreter oracle must observe a TRUE signed overflow for
/// the widened idiom (guards against a vacuous "overflow never fires" pass) and
/// the JITs must agree with it.
#[test]
fn widened_overflow_selfcheck() {
    let m = build_module("widened_ovf_sc", |fb, _e, p| {
        let (sum, overflow) = emit_widened_overflow(fb, WideKind::Add, p[0], p[1]);
        // return zext(overflow)*1000 + sum, so both the flag AND the sum are
        // observable in one i64.
        let w = fb.zext(Ty::Bool, Ty::I64, overflow);
        let k = fb.iconst(Ty::I64, 1000);
        let wk = fb.binop(BinOp::Mul, Ty::I64, w, k);
        let out = fb.binop(BinOp::Add, Ty::I64, wk, sum);
        fb.ret(vec![out]);
    });
    // i64::MAX + 1 overflows: flag=1, sum = i64::MIN.
    let row = [i64::MAX, 1, 0, 0];
    let ov = run_oracle_one(&m, &row).expect("oracle must accept the widened idiom");
    assert_eq!(
        ov,
        1000i64.wrapping_add(i64::MIN),
        "MAX+1 must signal overflow in the oracle"
    );
    let jits = run_all_jit(&m, &row, "widened_sc", &mut Vec::new());
    assert_eq!(jits.len(), 8, "all 8 JIT configs should produce a value");
    for (kkey, v) in &jits {
        assert_eq!(
            *v,
            1000i64.wrapping_add(i64::MIN),
            "JIT {kkey:?} must agree the idiom overflowed"
        );
    }
    // No-overflow case: flag=0, sum = 3.
    let row0 = [1i64, 2, 0, 0];
    assert_eq!(run_oracle_one(&m, &row0).unwrap(), 3, "1+2 no overflow");
}

// ===========================================================================
// Helpers: native-Rust icmp ground truth (mirrors interpreter eval_icmp on the
// already-canonical small operands) and the defect reporter.
// ===========================================================================

fn eval_icmp_rs(op: ICmpOp, lhs: i64, rhs: i64) -> bool {
    match op {
        ICmpOp::Eq => lhs == rhs,
        ICmpOp::Ne => lhs != rhs,
        ICmpOp::Slt => lhs < rhs,
        ICmpOp::Sle => lhs <= rhs,
        ICmpOp::Sgt => lhs > rhs,
        ICmpOp::Sge => lhs >= rhs,
        ICmpOp::Ult => (lhs as u64) < (rhs as u64),
        ICmpOp::Ule => (lhs as u64) <= (rhs as u64),
        ICmpOp::Ugt => (lhs as u64) > (rhs as u64),
        ICmpOp::Uge => (lhs as u64) >= (rhs as u64),
    }
}

fn report(name: &str, configs: usize, defects: &[String]) {
    eprintln!("{name}: {configs} configs, {} defects", defects.len());
    assert!(
        defects.is_empty(),
        "{}",
        defects
            .iter()
            .take(50)
            .cloned()
            .collect::<Vec<_>>()
            .join("\n")
    );
}
