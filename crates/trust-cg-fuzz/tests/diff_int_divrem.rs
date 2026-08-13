// trust-cg-fuzz/tests/diff_int_divrem.rs
//
// Differential testing of integer division/remainder lowering.
// Surface: int_divrem — UDiv/SDiv/URem/SRem at i32 and i64.
//
// Oracle: trust-ir interpreter (run_oracle_one). Native: 4 opt levels x 2
// register allocators (jit_fast vs non-fast). A defect is any disagreement
// among defined values, or a compile error / missing symbol / panic on a
// module the oracle accepts.

#![cfg(target_arch = "aarch64")]

use std::collections::HashMap;
use std::panic;

use trust_cg_codegen::Target;
use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_fuzz::jit_diff::run_oracle_one;
use trust_ir::{BinOp, Ty};
use trust_ir_build::ModuleBuilder;

const ENTRY: &str = "fuzz_fn";

// ---------------------------------------------------------------------------
// Run abstraction
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, PartialEq, Eq)]
enum Run {
    Value(i64),
    CompileErr,
    SymbolMissing,
    Panic,
}

fn jit_run(m: &trust_ir::Module, opt: OptLevel, fast: bool, row: &[i64; 4]) -> Run {
    let ext: HashMap<String, *const u8> = HashMap::new();
    let mut cfg = if fast {
        CompilerConfig::jit_fast(Target::host())
    } else {
        let mut c = CompilerConfig::for_host_jit();
        c.enable_jit_fast_regalloc = false;
        c
    };
    cfg.opt_level = opt;

    let compile = panic::catch_unwind(panic::AssertUnwindSafe(|| {
        Compiler::new(cfg)
            .compile_module_to_jit(m, &ext)
            .map_err(Box::new)
    }));
    let buf = match compile {
        Ok(Ok(r)) => r.buffer,
        Ok(Err(_)) => return Run::CompileErr,
        Err(_) => return Run::Panic,
    };
    let f = match unsafe { buf.get_fn_bound::<extern "C" fn(i64, i64, i64, i64) -> i64>(ENTRY) } {
        Some(p) => p.into_inner(),
        None => return Run::SymbolMissing,
    };
    let row = *row;
    let call = panic::catch_unwind(panic::AssertUnwindSafe(|| {
        f(row[0], row[1], row[2], row[3])
    }));
    let out = match call {
        Ok(v) => Run::Value(v),
        Err(_) => Run::Panic,
    };
    drop(buf);
    out
}

const OPTS: [OptLevel; 4] = [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3];

/// Run all 8 configs (4 opt x 2 alloc). Returns Vec of (label, Run).
fn all_configs(m: &trust_ir::Module, row: &[i64; 4]) -> Vec<(String, Run)> {
    let mut out = Vec::new();
    for &opt in &OPTS {
        for &fast in &[false, true] {
            let label = format!("{:?}/{}", opt, if fast { "fast" } else { "std" });
            out.push((label, jit_run(m, opt, fast, row)));
        }
    }
    out
}

// ---------------------------------------------------------------------------
// Module builders for many divrem shapes.
// Each shape takes args (a,b,c,d) and returns one i64.
// Divisors are made safe nonzero via |1 unless the shape is a labeled edge.
// ---------------------------------------------------------------------------

/// op kind selector
#[derive(Copy, Clone)]
enum DOp {
    UDiv,
    SDiv,
    URem,
    SRem,
}

impl DOp {
    fn binop(self) -> BinOp {
        match self {
            DOp::UDiv => BinOp::UDiv,
            DOp::SDiv => BinOp::SDiv,
            DOp::URem => BinOp::URem,
            DOp::SRem => BinOp::SRem,
        }
    }
    fn name(self) -> &'static str {
        match self {
            DOp::UDiv => "UDiv",
            DOp::SDiv => "SDiv",
            DOp::URem => "URem",
            DOp::SRem => "SRem",
        }
    }
}

const ALL_DOPS: [DOp; 4] = [DOp::UDiv, DOp::SDiv, DOp::URem, DOp::SRem];

/// Make a divisor safe-nonzero: (v | 1). Works for any signed/unsigned width.
fn safe_div_i64(
    fb: &mut trust_ir_build::FunctionBuilder,
    v: trust_ir::ValueId,
) -> trust_ir::ValueId {
    let one = fb.iconst(Ty::I64, 1);
    fb.binop(BinOp::Or, Ty::I64, v, one)
}
fn safe_div_i32(
    fb: &mut trust_ir_build::FunctionBuilder,
    v: trust_ir::ValueId,
) -> trust_ir::ValueId {
    let one = fb.iconst(Ty::I32, 1);
    fb.binop(BinOp::Or, Ty::I32, v, one)
}

/// Shape 1: simple i64 divrem, dynamic numerator, dynamic divisor (safe).
fn shape_i64_dyn_dyn(op: DOp) -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("m");
    let entry_ty = mb.add_func_type(vec![Ty::I64; 4], vec![Ty::I64]);
    let mut fb = mb.function(ENTRY, entry_ty);
    let e = fb.create_block();
    let a = fb.add_block_param(e, Ty::I64);
    let b = fb.add_block_param(e, Ty::I64);
    let _c = fb.add_block_param(e, Ty::I64);
    let _d = fb.add_block_param(e, Ty::I64);
    fb.switch_to_block(e);
    let div = safe_div_i64(&mut fb, b);
    let r = fb.binop(op.binop(), Ty::I64, a, div);
    fb.ret(vec![r]);
    fb.build();
    mb.build()
}

/// Shape 2: i64 divrem with constant divisor (varied constants).
fn shape_i64_const_div(op: DOp, divisor: i64) -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("m");
    let entry_ty = mb.add_func_type(vec![Ty::I64; 4], vec![Ty::I64]);
    let mut fb = mb.function(ENTRY, entry_ty);
    let e = fb.create_block();
    let a = fb.add_block_param(e, Ty::I64);
    let _b = fb.add_block_param(e, Ty::I64);
    let _c = fb.add_block_param(e, Ty::I64);
    let _d = fb.add_block_param(e, Ty::I64);
    fb.switch_to_block(e);
    let k = fb.iconst(Ty::I64, divisor as i128);
    let r = fb.binop(op.binop(), Ty::I64, a, k);
    fb.ret(vec![r]);
    fb.build();
    mb.build()
}

/// Shape 3: i64 divrem with constant numerator, dynamic divisor (safe).
fn shape_i64_const_num(op: DOp, num: i64) -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("m");
    let entry_ty = mb.add_func_type(vec![Ty::I64; 4], vec![Ty::I64]);
    let mut fb = mb.function(ENTRY, entry_ty);
    let e = fb.create_block();
    let _a = fb.add_block_param(e, Ty::I64);
    let b = fb.add_block_param(e, Ty::I64);
    let _c = fb.add_block_param(e, Ty::I64);
    let _d = fb.add_block_param(e, Ty::I64);
    fb.switch_to_block(e);
    let k = fb.iconst(Ty::I64, num as i128);
    let div = safe_div_i64(&mut fb, b);
    let r = fb.binop(op.binop(), Ty::I64, k, div);
    fb.ret(vec![r]);
    fb.build();
    mb.build()
}

/// Shape 4: i32 divrem, dynamic operands (truncated from i64 args), result sext to i64.
fn shape_i32_dyn_dyn(op: DOp) -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("m");
    let entry_ty = mb.add_func_type(vec![Ty::I64; 4], vec![Ty::I64]);
    let mut fb = mb.function(ENTRY, entry_ty);
    let e = fb.create_block();
    let a = fb.add_block_param(e, Ty::I64);
    let b = fb.add_block_param(e, Ty::I64);
    let _c = fb.add_block_param(e, Ty::I64);
    let _d = fb.add_block_param(e, Ty::I64);
    fb.switch_to_block(e);
    let a32 = fb.trunc(Ty::I64, Ty::I32, a);
    let b32 = fb.trunc(Ty::I64, Ty::I32, b);
    let div = safe_div_i32(&mut fb, b32);
    let r = fb.binop(op.binop(), Ty::I32, a32, div);
    // sext result back to i64 so compared value is well-defined.
    let r64 = fb.sext(Ty::I32, Ty::I64, r);
    fb.ret(vec![r64]);
    fb.build();
    mb.build()
}

/// Shape 5: i32 divrem with constant divisor, result zext to i64.
fn shape_i32_const_div(op: DOp, divisor: i32) -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("m");
    let entry_ty = mb.add_func_type(vec![Ty::I64; 4], vec![Ty::I64]);
    let mut fb = mb.function(ENTRY, entry_ty);
    let e = fb.create_block();
    let a = fb.add_block_param(e, Ty::I64);
    let _b = fb.add_block_param(e, Ty::I64);
    let _c = fb.add_block_param(e, Ty::I64);
    let _d = fb.add_block_param(e, Ty::I64);
    fb.switch_to_block(e);
    let a32 = fb.trunc(Ty::I64, Ty::I32, a);
    let k = fb.iconst(Ty::I32, divisor as i128);
    let r = fb.binop(op.binop(), Ty::I32, a32, k);
    let r64 = fb.zext(Ty::I32, Ty::I64, r);
    fb.ret(vec![r64]);
    fb.build();
    mb.build()
}

/// Shape 6: divrem nested in a loop. accumulator += (a / (i|1)) over c iterations (bounded).
/// Keeps quotient live across loop back-edge.
fn shape_i64_loop(op: DOp) -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("m");
    let entry_ty = mb.add_func_type(vec![Ty::I64; 4], vec![Ty::I64]);
    let mut fb = mb.function(ENTRY, entry_ty);
    let e = fb.create_block();
    let a = fb.add_block_param(e, Ty::I64);
    let _b = fb.add_block_param(e, Ty::I64);
    let c = fb.add_block_param(e, Ty::I64);
    let _d = fb.add_block_param(e, Ty::I64);

    let header = fb.create_block();
    let acc0 = fb.add_block_param(header, Ty::I64);
    let i0 = fb.add_block_param(header, Ty::I64);

    let body = fb.create_block();
    let exit = fb.create_block();
    let res = fb.add_block_param(exit, Ty::I64);

    fb.switch_to_block(e);
    // bound iterations: n = (c & 7) + 1  -> 1..=8 iterations
    let mask = fb.iconst(Ty::I64, 7);
    let cm = fb.binop(BinOp::And, Ty::I64, c, mask);
    let one = fb.iconst(Ty::I64, 1);
    let n = fb.binop(BinOp::Add, Ty::I64, cm, one);
    let zero = fb.iconst(Ty::I64, 0);
    fb.br(header, vec![zero, zero]); // acc=0, i=0

    fb.switch_to_block(header);
    let cond = fb.icmp(trust_ir::ICmpOp::Slt, Ty::I64, i0, n);
    fb.condbr(cond, body, vec![], exit, vec![acc0]);

    fb.switch_to_block(body);
    // divisor = (i+1) (always nonzero, 1..=8)
    let div = fb.binop(BinOp::Add, Ty::I64, i0, one);
    let q = fb.binop(op.binop(), Ty::I64, a, div);
    let acc1 = fb.binop(BinOp::Add, Ty::I64, acc0, q);
    let i1 = fb.binop(BinOp::Add, Ty::I64, i0, one);
    fb.br(header, vec![acc1, i1]);

    fb.switch_to_block(exit);
    fb.ret(vec![res]);
    fb.build();
    mb.build()
}

/// Shape 7: quotient kept live across a call. q = a/(b|1); helper(q) = q*3; return q + helper(q).
fn shape_i64_quotient_across_call(op: DOp) -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("m");
    // declare callee FIRST (FuncId 0), entry second (FuncId 1).
    let callee_ty = mb.add_func_type(vec![Ty::I64], vec![Ty::I64]);
    let entry_ty = mb.add_func_type(vec![Ty::I64; 4], vec![Ty::I64]);

    // callee: x -> x*3
    {
        let mut cb = mb.function("triple", callee_ty);
        let cbk = cb.create_block();
        let x = cb.add_block_param(cbk, Ty::I64);
        cb.switch_to_block(cbk);
        let three = cb.iconst(Ty::I64, 3);
        let r = cb.binop(BinOp::Mul, Ty::I64, x, three);
        cb.ret(vec![r]);
        cb.build();
    }

    let mut fb = mb.function(ENTRY, entry_ty);
    let e = fb.create_block();
    let a = fb.add_block_param(e, Ty::I64);
    let b = fb.add_block_param(e, Ty::I64);
    let _c = fb.add_block_param(e, Ty::I64);
    let _d = fb.add_block_param(e, Ty::I64);
    fb.switch_to_block(e);
    let div = safe_div_i64(&mut fb, b);
    let q = fb.binop(op.binop(), Ty::I64, a, div);
    // FuncId 0 is "triple"
    let h = fb.call(trust_ir::FuncId(0), vec![q]);
    let r = fb.binop(BinOp::Add, Ty::I64, q, h);
    fb.ret(vec![r]);
    fb.build();
    mb.build()
}

/// Shape 8: chained divrem — combine two ops: (a / (b|1)) % ((c|1)) at i64.
fn shape_i64_chained(op1: DOp, op2: DOp) -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("m");
    let entry_ty = mb.add_func_type(vec![Ty::I64; 4], vec![Ty::I64]);
    let mut fb = mb.function(ENTRY, entry_ty);
    let e = fb.create_block();
    let a = fb.add_block_param(e, Ty::I64);
    let b = fb.add_block_param(e, Ty::I64);
    let c = fb.add_block_param(e, Ty::I64);
    let _d = fb.add_block_param(e, Ty::I64);
    fb.switch_to_block(e);
    let div1 = safe_div_i64(&mut fb, b);
    let t = fb.binop(op1.binop(), Ty::I64, a, div1);
    let div2 = safe_div_i64(&mut fb, c);
    let r = fb.binop(op2.binop(), Ty::I64, t, div2);
    fb.ret(vec![r]);
    fb.build();
    mb.build()
}

/// Shape 9: high register pressure — many simultaneous divrem ops summed.
/// Stresses register allocation around div instructions (which use fixed regs).
fn shape_i64_pressure(op: DOp) -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("m");
    let entry_ty = mb.add_func_type(vec![Ty::I64; 4], vec![Ty::I64]);
    let mut fb = mb.function(ENTRY, entry_ty);
    let e = fb.create_block();
    let a = fb.add_block_param(e, Ty::I64);
    let b = fb.add_block_param(e, Ty::I64);
    let c = fb.add_block_param(e, Ty::I64);
    let d = fb.add_block_param(e, Ty::I64);
    fb.switch_to_block(e);
    // Build many divisors and quotients, all live, then sum.
    let mut acc = fb.iconst(Ty::I64, 0);
    let params = [a, b, c, d];
    for i in 0..params.len() {
        for j in 0..params.len() {
            let num = params[i];
            let den = safe_div_i64(&mut fb, params[j]);
            let q = fb.binop(op.binop(), Ty::I64, num, den);
            acc = fb.binop(BinOp::Add, Ty::I64, acc, q);
        }
    }
    fb.ret(vec![acc]);
    fb.build();
    mb.build()
}

/// Shape 10 (EDGE): div-by-zero / INT_MIN-by-(-1) probe WITHOUT |1 guard.
/// i64, dynamic numerator and divisor. Compared via cross-opt JIT agreement only.
fn shape_i64_raw(op: DOp) -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("m");
    let entry_ty = mb.add_func_type(vec![Ty::I64; 4], vec![Ty::I64]);
    let mut fb = mb.function(ENTRY, entry_ty);
    let e = fb.create_block();
    let a = fb.add_block_param(e, Ty::I64);
    let b = fb.add_block_param(e, Ty::I64);
    let _c = fb.add_block_param(e, Ty::I64);
    let _d = fb.add_block_param(e, Ty::I64);
    fb.switch_to_block(e);
    let r = fb.binop(op.binop(), Ty::I64, a, b);
    fb.ret(vec![r]);
    fb.build();
    mb.build()
}

/// Shape 11 (EDGE): i32 raw div without guard, sext result.
fn shape_i32_raw(op: DOp) -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("m");
    let entry_ty = mb.add_func_type(vec![Ty::I64; 4], vec![Ty::I64]);
    let mut fb = mb.function(ENTRY, entry_ty);
    let e = fb.create_block();
    let a = fb.add_block_param(e, Ty::I64);
    let b = fb.add_block_param(e, Ty::I64);
    let _c = fb.add_block_param(e, Ty::I64);
    let _d = fb.add_block_param(e, Ty::I64);
    fb.switch_to_block(e);
    let a32 = fb.trunc(Ty::I64, Ty::I32, a);
    let b32 = fb.trunc(Ty::I64, Ty::I32, b);
    let r = fb.binop(op.binop(), Ty::I32, a32, b32);
    let r64 = fb.sext(Ty::I32, Ty::I64, r);
    fb.ret(vec![r64]);
    fb.build();
    mb.build()
}

/// Shape 12 (ORACLE-COMPARABLE narrow div): i32 UDiv/URem with operands masked
/// to a small positive range (& 0xffff), so the i32 result is always in
/// [0, 0xffff] -> high bit clear -> zext == oracle's no-op cast. This gives
/// genuine oracle-backed coverage of the i32 division *machinery* (the
/// fixed-register / widening lowering on aarch64) even though the oracle does
/// not model cast width: the masking makes the width-correct and no-op-cast
/// results provably coincide.
fn shape_i32_masked_oracle(op: DOp) -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("m");
    let entry_ty = mb.add_func_type(vec![Ty::I64; 4], vec![Ty::I64]);
    let mut fb = mb.function(ENTRY, entry_ty);
    let e = fb.create_block();
    let a = fb.add_block_param(e, Ty::I64);
    let b = fb.add_block_param(e, Ty::I64);
    let _c = fb.add_block_param(e, Ty::I64);
    let _d = fb.add_block_param(e, Ty::I64);
    fb.switch_to_block(e);
    // Mask both operands to 16 bits at i64 width: value in [0, 0xffff].
    let mask = fb.iconst(Ty::I64, 0xffff);
    let am = fb.binop(BinOp::And, Ty::I64, a, mask);
    let bm = fb.binop(BinOp::And, Ty::I64, b, mask);
    // Truncate to i32; values are identical small positive ints.
    let a32 = fb.trunc(Ty::I64, Ty::I32, am);
    let b32 = fb.trunc(Ty::I64, Ty::I32, bm);
    // Safe nonzero divisor in [1, 0xffff] (still high bit clear after |1).
    let div = safe_div_i32(&mut fb, b32);
    let r = fb.binop(op.binop(), Ty::I32, a32, div);
    // Result in [0, 0xffff]: zext == sext == oracle no-op. Use zext for clarity.
    let r64 = fb.zext(Ty::I32, Ty::I64, r);
    fb.ret(vec![r64]);
    fb.build();
    mb.build()
}

// ---------------------------------------------------------------------------
// Input rows: include 0, 1, -1, INT_MIN, INT_MAX, large constants, mixed.
// ---------------------------------------------------------------------------

fn input_rows() -> Vec<[i64; 4]> {
    let i64_min = i64::MIN;
    let i64_max = i64::MAX;
    let i32_min = i32::MIN as i64;
    let i32_max = i32::MAX as i64;
    vec![
        [0, 0, 0, 0],
        [1, 1, 1, 1],
        [-1, -1, -1, -1],
        [100, 7, 3, 13],
        [-100, 7, -3, 13],
        [100, -7, 3, -13],
        [i64_min, -1, i64_min, -1],
        [i64_max, 2, i64_max, 3],
        [i64_min, 3, 7, 5],
        [i32_min, -1, i32_min, -1],
        [i32_max, 2, i32_max, 3],
        [0x7fff_ffff_ffff_ffff, 0x1234_5678, -42, 999],
        [i64_min, 2, -3, 100000],
        [123456789, 1000, -987654321, 17],
        [-1, i64_min, i64_max, 1],
        [42, 0, 0, 0], // numerator nonzero, raw-divisor-zero edge
        [i64_min, 0, -1, 0],
    ]
}

// ---------------------------------------------------------------------------
// Comparison helpers
// ---------------------------------------------------------------------------

/// Compare oracle (if Ok) with all configs; also cross-check configs amongst
/// themselves. Returns list of defect strings.
fn check_with_oracle(label: &str, m: &trust_ir::Module, row: &[i64; 4], defects: &mut Vec<String>) {
    let oracle = run_oracle_one(m, row);
    let configs = all_configs(m, row);

    // Reference for cross-config agreement: first Value among configs.
    let first_val = configs.iter().find_map(|(_, r)| match r {
        Run::Value(v) => Some(*v),
        _ => None,
    });

    // Non-value runs (compile err / symbol missing / panic) are defects only if
    // the oracle accepted the module (produced a value).
    let oracle_ok = oracle.is_ok();

    for (clabel, run) in &configs {
        match run {
            Run::Value(v) => {
                if let Ok(ov) = &oracle
                    && *v != *ov
                {
                    defects.push(format!(
                        "{} row={:?}: ORACLE_MISMATCH config={} jit={} oracle={}",
                        label, row, clabel, v, ov
                    ));
                }
            }
            Run::CompileErr => {
                if oracle_ok {
                    defects.push(format!(
                        "{} row={:?}: COMPILE_ERR config={} but oracle ok",
                        label, row, clabel
                    ));
                }
            }
            Run::SymbolMissing => {
                if oracle_ok {
                    defects.push(format!(
                        "{} row={:?}: SYMBOL_MISSING config={} but oracle ok",
                        label, row, clabel
                    ));
                }
            }
            Run::Panic => {
                if oracle_ok {
                    defects.push(format!(
                        "{} row={:?}: PANIC config={} but oracle ok",
                        label, row, clabel
                    ));
                }
            }
        }
    }

    // Cross-config agreement among all Value results (catches O0-vs-O3 etc.).
    if let Some(fv) = first_val {
        for (clabel, run) in &configs {
            if let Run::Value(v) = run
                && *v != fv
            {
                defects.push(format!(
                    "{} row={:?}: CROSS_CONFIG_DISAGREE config={}={} first={}",
                    label, row, clabel, v, fv
                ));
            }
        }
    }
}

/// Oracle-free checker: all defined (Value) configs must agree among
/// themselves. Used for two situations:
///   1. Labeled div-by-zero / INT_MIN-by-(-1) edges (UB; oracle silent).
///   2. Sub-i64 (i32) shapes whose final value depends on zext/sext/trunc of a
///      narrow value. The trust-cg interpreter (the oracle) deliberately treats
///      ZExt/SExt/Trunc as NO-OPS on its i128 internal representation
///      (see trust-cg-codegen/src/interpreter.rs eval_cast: lines ~823-828),
///      so it cannot model the width-correct result of a narrow op zero/sign
///      extended back to i64. The JIT IS width-correct; comparing it to the
///      oracle here would be a false positive. So for narrow shapes we verify
///      codegen correctness via cross-opt/cross-allocator JIT agreement only
///      (oracle_comparable=false for these).
fn check_edge(label: &str, m: &trust_ir::Module, row: &[i64; 4], defects: &mut Vec<String>) {
    let configs = all_configs(m, row);
    let first_val = configs.iter().find_map(|(_, r)| match r {
        Run::Value(v) => Some(*v),
        _ => None,
    });
    if let Some(fv) = first_val {
        for (clabel, run) in &configs {
            if let Run::Value(v) = run
                && *v != fv
            {
                defects.push(format!(
                    "[EDGE] {} row={:?}: CROSS_CONFIG_DISAGREE config={}={} first={}",
                    label, row, clabel, v, fv
                ));
            }
        }
    }
    // Note: compile-err/panic on raw edge is NOT a defect (UB), so we do not
    // record those. A trap on div-by-zero is acceptable hardware behavior.
}

// ---------------------------------------------------------------------------
// Test
// ---------------------------------------------------------------------------

#[test]
fn diff_int_divrem_sweep() {
    let rows = input_rows();
    let mut defects: Vec<String> = Vec::new();
    let mut configs_tested: u64 = 0;
    let configs_per_check = 8u64; // 4 opt x 2 alloc

    // --- Oracle-comparable shapes (safe nonzero divisors) ---

    // Shape 1: i64 dyn/dyn
    for op in ALL_DOPS {
        let m = shape_i64_dyn_dyn(op);
        for row in &rows {
            check_with_oracle(
                &format!("i64_dyn_dyn[{}]", op.name()),
                &m,
                row,
                &mut defects,
            );
            configs_tested += configs_per_check;
        }
    }

    // Shape 2: i64 const divisor (varied constants incl. powers of two, neg, large)
    let i64_divs: [i64; 9] = [1, 2, 3, 7, 8, -1, -7, 1000000007, i64::MIN];
    for op in ALL_DOPS {
        for &dv in &i64_divs {
            let m = shape_i64_const_div(op, dv);
            for row in &rows {
                check_with_oracle(
                    &format!("i64_const_div[{}][d={}]", op.name(), dv),
                    &m,
                    row,
                    &mut defects,
                );
                configs_tested += configs_per_check;
            }
        }
    }

    // Shape 3: i64 const numerator (incl INT_MIN, INT_MAX), dynamic safe divisor
    let i64_nums: [i64; 5] = [0, 1, -1, i64::MIN, i64::MAX];
    for op in ALL_DOPS {
        for &nv in &i64_nums {
            let m = shape_i64_const_num(op, nv);
            for row in &rows {
                check_with_oracle(
                    &format!("i64_const_num[{}][n={}]", op.name(), nv),
                    &m,
                    row,
                    &mut defects,
                );
                configs_tested += configs_per_check;
            }
        }
    }

    // Shape 4: i32 dyn/dyn. Oracle-free (narrow-cast width not modeled by oracle).
    for op in ALL_DOPS {
        let m = shape_i32_dyn_dyn(op);
        for row in &rows {
            check_edge(
                &format!("i32_dyn_dyn[{}]", op.name()),
                &m,
                row,
                &mut defects,
            );
            configs_tested += configs_per_check;
        }
    }

    // Shape 5: i32 const divisor. Oracle-free (narrow-cast width not modeled by oracle).
    let i32_divs: [i32; 7] = [1, 2, 3, 7, -1, -7, i32::MIN];
    for op in ALL_DOPS {
        for &dv in &i32_divs {
            let m = shape_i32_const_div(op, dv);
            for row in &rows {
                check_edge(
                    &format!("i32_const_div[{}][d={}]", op.name(), dv),
                    &m,
                    row,
                    &mut defects,
                );
                configs_tested += configs_per_check;
            }
        }
    }

    // Shape 6: i64 in loop
    for op in ALL_DOPS {
        let m = shape_i64_loop(op);
        for row in &rows {
            check_with_oracle(&format!("i64_loop[{}]", op.name()), &m, row, &mut defects);
            configs_tested += configs_per_check;
        }
    }

    // Shape 7: quotient across call
    for op in ALL_DOPS {
        let m = shape_i64_quotient_across_call(op);
        for row in &rows {
            check_with_oracle(
                &format!("i64_q_across_call[{}]", op.name()),
                &m,
                row,
                &mut defects,
            );
            configs_tested += configs_per_check;
        }
    }

    // Shape 8: chained (cartesian of a couple of combos)
    for op1 in ALL_DOPS {
        for op2 in [DOp::SDiv, DOp::URem] {
            let m = shape_i64_chained(op1, op2);
            for row in &rows {
                check_with_oracle(
                    &format!("i64_chained[{}->{}]", op1.name(), op2.name()),
                    &m,
                    row,
                    &mut defects,
                );
                configs_tested += configs_per_check;
            }
        }
    }

    // Shape 9: high pressure
    for op in ALL_DOPS {
        let m = shape_i64_pressure(op);
        for row in &rows {
            check_with_oracle(
                &format!("i64_pressure[{}]", op.name()),
                &m,
                row,
                &mut defects,
            );
            configs_tested += configs_per_check;
        }
    }

    // Shape 12: oracle-comparable narrow (i32) UDiv/URem with masked operands.
    // This is the ONLY narrow shape that is sound to compare to the oracle,
    // because operands are masked so width-correct zext and the oracle's no-op
    // cast provably coincide. Gives real oracle coverage of i32 div lowering.
    for op in [DOp::UDiv, DOp::URem, DOp::SDiv, DOp::SRem] {
        let m = shape_i32_masked_oracle(op);
        for row in &rows {
            check_with_oracle(
                &format!("i32_masked_oracle[{}]", op.name()),
                &m,
                row,
                &mut defects,
            );
            configs_tested += configs_per_check;
        }
    }

    // --- Labeled EDGE shapes: div-by-zero & INT_MIN/-1 (oracle-free, cross-config only) ---

    for op in ALL_DOPS {
        let m = shape_i64_raw(op);
        for row in &rows {
            check_edge(&format!("i64_raw[{}]", op.name()), &m, row, &mut defects);
            configs_tested += configs_per_check;
        }
    }
    for op in ALL_DOPS {
        let m = shape_i32_raw(op);
        for row in &rows {
            check_edge(&format!("i32_raw[{}]", op.name()), &m, row, &mut defects);
            configs_tested += configs_per_check;
        }
    }

    eprintln!(
        "int_divrem: {} configs, {} defects",
        configs_tested,
        defects.len()
    );
    for d in &defects {
        eprintln!("DEFECT: {}", d);
    }

    assert!(
        defects.is_empty(),
        "int_divrem found {} defects:\n{}",
        defects.len(),
        defects.join("\n")
    );
}
