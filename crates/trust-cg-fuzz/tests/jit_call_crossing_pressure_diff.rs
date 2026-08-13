// trust-cg-fuzz/tests/jit_call_crossing_pressure_diff.rs
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Differential reproduction harness for the native fused-loop codegen defect:
// values that are LIVE ACROSS A CALL must survive the call. The existing
// jit_diff fuzzer only exercises call-free arithmetic, so the call-crossing
// register-allocation path (especially under the `jit_fast` single-pass
// allocator that `for_host_jit`/`jit_fast` profiles use in production) is never
// differentially tested. This harness builds self-contained modules where the
// entry keeps N independent values (GPR and/or FP) live across an in-module
// call (which clobbers the caller-saved registers), with a configurable callee
// arity (>8 forces stack-passed args / SP-16 alignment), then compares the
// trust-ir interpreter oracle against the JIT at O0/O1/O2/O3 under both
// register allocators.

#![cfg(target_arch = "aarch64")]

use std::collections::HashMap;
use std::panic;

use trust_cg_codegen::Target;
use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_fuzz::jit_diff::run_oracle_one;
use trust_ir::{BinOp, CastOp, Ty};
use trust_ir_build::ModuleBuilder;

const ENTRY: &str = "fuzz_fn";

#[derive(Clone, Copy, Debug)]
struct Cfg {
    pressure: u32,
    calls: u32,
    loop_iters: u32,
    use_memory: bool,
    indirect: bool,
    callee_args: u32,
    fp_carries: u32,
}

impl Cfg {
    fn gpr(pressure: u32, calls: u32, loop_iters: u32, use_memory: bool) -> Self {
        Cfg {
            pressure,
            calls,
            loop_iters,
            use_memory,
            indirect: false,
            callee_args: 8,
            fp_carries: 0,
        }
    }
}

fn build_module(cfg: Cfg) -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("call_crossing");

    let nargs = cfg.callee_args.max(1) as usize;
    let callee_ty = mb.add_func_type(vec![Ty::I64; nargs], vec![Ty::I64]);

    // Declare the callee FIRST so its FuncId is stable (0). The callee mixes
    // all its integer args AND scribbles on FP registers, so a call clobbers
    // both the caller-saved GPRs and FPRs.
    let callee_id = {
        let mut fb = mb.function("clobber", callee_ty);
        let blk = fb.create_block();
        let p: Vec<_> = (0..nargs)
            .map(|_| fb.add_block_param(blk, Ty::I64))
            .collect();
        fb.switch_to_block(blk);
        let mut acc = p[0];
        for i in 0..nargs {
            let k = fb.iconst(Ty::I64, 0x9e3779b1_i128 + (i as i128) * 0x1000_0193);
            let m = fb.binop(BinOp::Mul, Ty::I64, p[i], k);
            acc = fb.binop(BinOp::Add, Ty::I64, acc, m);
            acc = fb.binop(BinOp::Xor, Ty::I64, acc, p[(i + 3) % nargs]);
            let s = fb.iconst(Ty::I64, ((i as i128) % 13) + 1);
            let sh = fb.binop(BinOp::Shl, Ty::I64, acc, s);
            acc = fb.binop(BinOp::Add, Ty::I64, acc, sh);
        }
        // FP scribble: forces the callee to allocate FP registers, clobbering
        // caller-saved FPRs. Values are masked small so int<->float round-trips
        // are EXACT and identical between interpreter and hardware (keeps the
        // test focused on call-crossing, not conversion semantics).
        let mask = fb.iconst(Ty::I64, 0xffff);
        let acc_small = fb.binop(BinOp::And, Ty::I64, acc, mask);
        let f = fb.cast(CastOp::SIToFP, Ty::I64, Ty::F64, acc_small);
        let fk = fb.fconst(Ty::F64, 3.0);
        let fm = fb.binop(BinOp::FMul, Ty::F64, f, fk);
        let fa = fb.binop(BinOp::FAdd, Ty::F64, fm, f);
        let back = fb.cast(CastOp::FPToSI, Ty::F64, Ty::I64, fa);
        acc = fb.binop(BinOp::Add, Ty::I64, acc, back);
        fb.ret(vec![acc]);
        fb.build()
    };

    let entry_ty = if cfg.indirect {
        let mut ps = vec![Ty::Func(callee_ty)];
        ps.extend(vec![Ty::I64; 4]);
        mb.add_func_type(ps, vec![Ty::I64])
    } else {
        mb.add_func_type(vec![Ty::I64; 4], vec![Ty::I64])
    };

    {
        let mut fb = mb.function(ENTRY, entry_ty);
        let entry = fb.create_block();
        let (callee_ptr, a, b, c, d) = if cfg.indirect {
            let cp = fb.add_block_param(entry, Ty::Func(callee_ty));
            let a = fb.add_block_param(entry, Ty::I64);
            let b = fb.add_block_param(entry, Ty::I64);
            let c = fb.add_block_param(entry, Ty::I64);
            let d = fb.add_block_param(entry, Ty::I64);
            (Some(cp), a, b, c, d)
        } else {
            let a = fb.add_block_param(entry, Ty::I64);
            let b = fb.add_block_param(entry, Ty::I64);
            let c = fb.add_block_param(entry, Ty::I64);
            let d = fb.add_block_param(entry, Ty::I64);
            (None, a, b, c, d)
        };

        fb.switch_to_block(entry);

        let buf = if cfg.use_memory {
            Some(fb.alloca(Ty::I64))
        } else {
            None
        };

        let seeds = [a, b, c, d];
        let mut carries = Vec::new();
        for i in 0..cfg.pressure {
            let base = seeds[(i as usize) % 4];
            let k = fb.iconst(Ty::I64, 0x100_0001 * (i as i128 + 1) + 7);
            let m = fb.binop(BinOp::Mul, Ty::I64, base, k);
            let k2 = fb.iconst(Ty::I64, (i as i128) * 0x1357 + 0x9e37);
            let v = fb.binop(BinOp::Xor, Ty::I64, m, k2);
            carries.push(v);
        }

        // FP carries kept live across the call. Masked-small and integer
        // multipliers so the int<->float round-trip is exact.
        let fmask = fb.iconst(Ty::I64, 0xffff);
        let mut fp_carries = Vec::new();
        for i in 0..cfg.fp_carries {
            let base = seeds[(i as usize) % 4];
            let base_small = fb.binop(BinOp::And, Ty::I64, base, fmask);
            let f = fb.cast(CastOp::SIToFP, Ty::I64, Ty::F64, base_small);
            let fk = fb.fconst(Ty::F64, (i + 1) as f64);
            let fv = fb.binop(BinOp::FMul, Ty::F64, f, fk);
            fp_carries.push(fv);
        }

        let header = fb.create_block();
        let h_iter = fb.add_block_param(header, Ty::I64);
        let h_acc = fb.add_block_param(header, Ty::I64);
        let body = fb.create_block();
        let b_iter = fb.add_block_param(body, Ty::I64);
        let b_acc = fb.add_block_param(body, Ty::I64);
        let done = fb.create_block();
        let d_acc = fb.add_block_param(done, Ty::I64);

        let zero = fb.iconst(Ty::I64, 0);
        let one = fb.iconst(Ty::I64, 1);
        let total_iters = fb.iconst(Ty::I64, i128::from(cfg.loop_iters.max(1)));
        fb.br(header, vec![zero, zero]);

        fb.switch_to_block(header);
        let cont = fb.icmp(trust_ir::ICmpOp::Ult, Ty::I64, h_iter, total_iters);
        fb.condbr(cont, body, vec![h_iter, h_acc], done, vec![h_acc]);

        fb.switch_to_block(body);
        let mut acc = b_acc;
        for call_i in 0..cfg.calls.max(1) {
            let mut args = Vec::new();
            for j in 0..nargs as u32 {
                let idx = ((call_i * nargs as u32 + j) as usize) % carries.len();
                let mixed = fb.binop(BinOp::Add, Ty::I64, carries[idx], acc);
                let mixed = fb.binop(BinOp::Xor, Ty::I64, mixed, b_iter);
                args.push(mixed);
            }
            if let Some(buf) = buf {
                fb.store(Ty::I64, buf, args[0]);
                let reloaded = fb.load(Ty::I64, buf);
                args[0] = reloaded;
            }
            let ret = if let Some(cp) = callee_ptr {
                fb.call_indirect(cp, callee_ty, args)
            } else {
                fb.call(callee_id, args)
            };
            acc = fb.binop(BinOp::Add, Ty::I64, acc, ret);
            for &carry in &carries {
                acc = fb.binop(BinOp::Xor, Ty::I64, acc, carry);
            }
            // Fold FP carries (live across the call) back into acc.
            for &fc in &fp_carries {
                let back = fb.cast(CastOp::FPToSI, Ty::F64, Ty::I64, fc);
                acc = fb.binop(BinOp::Add, Ty::I64, acc, back);
            }
        }
        let next_iter = fb.binop(BinOp::Add, Ty::I64, b_iter, one);
        fb.br(header, vec![next_iter, acc]);

        fb.switch_to_block(done);
        let mut out = d_acc;
        for &carry in &carries {
            out = fb.binop(BinOp::Add, Ty::I64, out, carry);
        }
        fb.ret(vec![out]);
        fb.build();
    }

    mb.build()
}

#[derive(Clone, Copy)]
enum Run {
    Value(i64),
    CompileErr,
    SymbolMissing,
}

fn jit_run(module: &trust_ir::Module, opt: OptLevel, jit_fast: bool, row: &[i64]) -> Run {
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
}

/// Run the indirect-call entry natively, passing the JIT'd `clobber` address
/// (looked up from the same buffer) as the function-pointer argument. Returns
/// None if compilation/lookup fails.
fn jit_run_indirect(
    module: &trust_ir::Module,
    opt: OptLevel,
    jit_fast: bool,
    row: &[i64],
) -> Option<i64> {
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
    let buf = compiler
        .compile_module_to_jit(module, &externs)
        .ok()?
        .buffer;
    let clobber_ptr = buf.get_fn_ptr_bound("clobber")?;
    type FnInd = extern "C" fn(*const u8, i64, i64, i64, i64) -> i64;
    let fptr = unsafe { buf.get_fn_bound::<FnInd>(ENTRY) }?.into_inner();
    let v = fptr(clobber_ptr.as_ptr(), row[0], row[1], row[2], row[3]);
    drop(buf);
    Some(v)
}

#[test]
fn call_crossing_indirect_matches_direct() {
    // Build identical computations as direct-call and indirect-call modules.
    // The direct form is already proven == interpreter, so any divergence here
    // isolates the call_indirect lowering (x16/x17 IP scratch, blr ABI).
    let mut configs = Vec::new();
    for pressure in [4u32, 8, 12, 16, 20, 24, 32] {
        for callee_args in [8u32, 10, 12, 16] {
            for loop_iters in [0u32, 2, 4] {
                for calls in [1u32, 2, 3] {
                    configs.push((pressure, callee_args, loop_iters, calls));
                }
            }
        }
    }
    let rows = rows();
    let mut defects = Vec::new();
    let mut n = 0usize;
    for (pressure, callee_args, loop_iters, calls) in configs {
        let base = Cfg {
            pressure,
            calls,
            loop_iters,
            use_memory: false,
            indirect: false,
            callee_args,
            fp_carries: 2,
        };
        let direct_mod = build_module(base);
        let indirect_mod = build_module(Cfg {
            indirect: true,
            ..base
        });
        n += 1;
        for row in &rows {
            let oracle = run_oracle_one(&direct_mod, row).ok();
            for jit_fast in [true, false] {
                for opt in [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3] {
                    let direct = panic::catch_unwind(panic::AssertUnwindSafe(|| {
                        jit_run(&direct_mod, opt, jit_fast, row)
                    }));
                    let indirect = panic::catch_unwind(panic::AssertUnwindSafe(|| {
                        jit_run_indirect(&indirect_mod, opt, jit_fast, row)
                    }));
                    let dval = match direct {
                        Ok(Run::Value(v)) => Some(v),
                        _ => None,
                    };
                    let ival = match indirect {
                        Ok(Some(v)) => Some(v),
                        Ok(None) => {
                            defects.push(format!(
                                "INDIRECT_COMPILE_FAIL p={pressure} args={callee_args} loop={loop_iters} calls={calls} fast={jit_fast} opt={opt:?}"
                            ));
                            None
                        }
                        Err(_) => {
                            defects.push(format!(
                                "INDIRECT_PANIC p={pressure} args={callee_args} loop={loop_iters} calls={calls} row={row:?} fast={jit_fast} opt={opt:?}"
                            ));
                            None
                        }
                    };
                    if let (Some(dv), Some(iv)) = (dval, ival)
                        && dv != iv
                    {
                        defects.push(format!(
                                "INDIRECT!=DIRECT p={pressure} args={callee_args} loop={loop_iters} calls={calls} row={row:?} fast={jit_fast} opt={opt:?}: direct={dv} indirect={iv} oracle={oracle:?}"
                            ));
                    }
                }
            }
        }
    }
    eprintln!("indirect: {n} configs, {} defects", defects.len());
    assert!(
        defects.is_empty(),
        "{}",
        defects
            .iter()
            .take(40)
            .cloned()
            .collect::<Vec<_>>()
            .join("\n")
    );
}

fn sweep(configs: &[Cfg], rows: &[[i64; 4]], defects: &mut Vec<String>) -> usize {
    let mut n = 0;
    for &cfg in configs {
        // Indirect variant can't be run natively here (no host callee ptr).
        if cfg.indirect {
            continue;
        }
        let module = build_module(cfg);
        n += 1;
        for row in rows {
            let oracle_val = match run_oracle_one(&module, row) {
                Ok(v) => v,
                Err(_) => continue,
            };
            for jit_fast in [true, false] {
                for opt in [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3] {
                    let got = panic::catch_unwind(panic::AssertUnwindSafe(|| {
                        jit_run(&module, opt, jit_fast, row)
                    }));
                    match got {
                        Ok(Run::Value(v)) if v != oracle_val => defects.push(format!(
                            "MISCOMPILE cfg={:?} row={:?} fast={} opt={:?}: interp={} jit={}",
                            cfg, row, jit_fast, opt, oracle_val, v
                        )),
                        Ok(Run::Value(_)) => {}
                        Ok(Run::CompileErr) => defects.push(format!(
                            "COMPILE_ERR cfg={:?} fast={} opt={:?}",
                            cfg, jit_fast, opt
                        )),
                        Ok(Run::SymbolMissing) => defects.push(format!(
                            "SYMBOL_MISSING cfg={:?} fast={} opt={:?}",
                            cfg, jit_fast, opt
                        )),
                        Err(_) => defects.push(format!(
                            "PANIC cfg={:?} row={:?} fast={} opt={:?}",
                            cfg, row, jit_fast, opt
                        )),
                    }
                }
            }
        }
    }
    n
}

fn rows() -> Vec<[i64; 4]> {
    vec![
        [1, 2, 3, 4],
        [0, 0, 0, 0],
        [-1, -2, -3, -4],
        [0x1122_3344, 0x5566_7788, 0x12345, 0x9abc],
        [i64::MAX, i64::MIN, 7, -7],
        [0xdead_beef, 0xfeed_face, 0x1000_0001, 0x7fff_ffff],
    ]
}

#[test]
fn call_crossing_gpr_pressure_matches_oracle() {
    let mut configs = Vec::new();
    for pressure in [8u32, 12, 16, 20, 24, 32] {
        for calls in [1u32, 2, 3] {
            for loop_iters in [0u32, 2, 4] {
                for use_memory in [false, true] {
                    configs.push(Cfg::gpr(pressure, calls, loop_iters, use_memory));
                }
            }
        }
    }
    let mut defects = Vec::new();
    let n = sweep(&configs, &rows(), &mut defects);
    eprintln!("gpr: {n} configs, {} defects", defects.len());
    assert!(
        defects.is_empty(),
        "{}",
        defects
            .iter()
            .take(40)
            .cloned()
            .collect::<Vec<_>>()
            .join("\n")
    );
}

#[test]
fn call_crossing_stack_args_matches_oracle() {
    // >8 callee args -> stack-passed args + SP-16 alignment.
    let mut configs = Vec::new();
    for callee_args in [9u32, 10, 12, 14, 16, 20] {
        for pressure in [8u32, 16, 24] {
            for loop_iters in [0u32, 2] {
                configs.push(Cfg {
                    callee_args,
                    pressure,
                    calls: 2,
                    loop_iters,
                    use_memory: false,
                    indirect: false,
                    fp_carries: 0,
                });
            }
        }
    }
    let mut defects = Vec::new();
    let n = sweep(&configs, &rows(), &mut defects);
    eprintln!("stack-args: {n} configs, {} defects", defects.len());
    assert!(
        defects.is_empty(),
        "{}",
        defects
            .iter()
            .take(40)
            .cloned()
            .collect::<Vec<_>>()
            .join("\n")
    );
}

#[test]
fn call_crossing_fp_matches_oracle() {
    let mut configs = Vec::new();
    for fp_carries in [1u32, 2, 4, 8, 12, 16] {
        for pressure in [4u32, 12, 20] {
            for loop_iters in [0u32, 2] {
                configs.push(Cfg {
                    fp_carries,
                    pressure,
                    calls: 2,
                    loop_iters,
                    use_memory: false,
                    indirect: false,
                    callee_args: 8,
                });
            }
        }
    }
    let mut defects = Vec::new();
    let n = sweep(&configs, &rows(), &mut defects);
    eprintln!("fp: {n} configs, {} defects", defects.len());
    assert!(
        defects.is_empty(),
        "{}",
        defects
            .iter()
            .take(40)
            .cloned()
            .collect::<Vec<_>>()
            .join("\n")
    );
}
