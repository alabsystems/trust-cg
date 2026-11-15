// trust-cg-fuzz/tests/jit_call_crossing_pressure_diff.rs
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Differential reproduction harness for the native fused-loop codegen defect:
// values that are LIVE ACROSS A CALL must survive the call. The existing
// jit_diff fuzzer only exercises call-free arithmetic, so the call-crossing
// register-allocation path (especially under the `jit_fast` single-pass
// allocator that `for_host_jit`/`jit_fast` profiles use in production) needs
// separate differential coverage. This harness builds self-contained modules where the
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

    mb.build().expect("ModuleBuilder::build: test fixture")
}

type RunResult = Result<i64, String>;

fn capture<T>(operation: impl FnOnce() -> Result<T, String>) -> Result<T, String> {
    panic::catch_unwind(panic::AssertUnwindSafe(operation)).unwrap_or_else(|payload| {
        let message = payload
            .downcast_ref::<String>()
            .map(String::as_str)
            .or_else(|| payload.downcast_ref::<&str>().copied())
            .unwrap_or("non-string panic payload");
        Err(format!("PANIC: {message}"))
    })
}

/// Compile each module/configuration once, keeping its owned executable alive
/// for every input row. Compile, lookup, execution, and panic failures remain
/// results to compare, never missing comparisons. Signals and hangs are bounded
/// by the matrix's process-group runner, not caught by Rust's unwind handler.
fn run_rows<T>(
    rows: &[[i64; 4]],
    compile: impl FnOnce() -> Result<T, String>,
    mut run: impl FnMut(&T, &[i64; 4]) -> RunResult,
) -> Vec<RunResult> {
    assert!(!rows.is_empty(), "a differential run needs input rows");
    let compiled = capture(compile);
    rows.iter()
        .map(|row| match &compiled {
            Ok(artifact) => capture(|| run(artifact, row)),
            Err(error) => Err(error.clone()),
        })
        .collect()
}

fn jit_rows(
    module: &trust_ir::Module,
    opt: OptLevel,
    jit_fast: bool,
    indirect: bool,
    rows: &[[i64; 4]],
) -> Vec<RunResult> {
    run_rows(
        rows,
        || {
            let externs: HashMap<String, *const u8> = HashMap::new();
            let mut config = if jit_fast {
                CompilerConfig::jit_fast(Target::host())
            } else {
                let mut config = CompilerConfig::for_host_jit();
                config.enable_jit_fast_regalloc = false;
                config
            };
            config.opt_level = opt;
            Compiler::new(config)
                .with_codegen_license(permit_unlicensed())
                .compile_module_to_jit(module, &externs)
                .map(|result| result.buffer)
                .map_err(|error| format!("COMPILE_ERR: {error}"))
        },
        |buffer, row| {
            if indirect {
                let clobber = buffer
                    .get_fn_ptr_bound("clobber")
                    .ok_or_else(|| "SYMBOL_MISSING: clobber".to_owned())?;
                type FnInd = extern "C" fn(*const u8, i64, i64, i64, i64) -> i64;
                // build_module's indirect entry has this exact signature; the
                // entry and clobber both belong to the still-live buffer.
                let entry = unsafe { buffer.get_fn_bound::<FnInd>(ENTRY) }
                    .ok_or_else(|| format!("SYMBOL_MISSING: {ENTRY}"))?;
                Ok(entry.into_inner()(
                    clobber.as_ptr(),
                    row[0],
                    row[1],
                    row[2],
                    row[3],
                ))
            } else {
                type Fn4 = extern "C" fn(i64, i64, i64, i64) -> i64;
                // build_module's direct entry has this exact signature and the
                // borrowed buffer outlives the call.
                let entry = unsafe { buffer.get_fn_bound::<Fn4>(ENTRY) }
                    .ok_or_else(|| format!("SYMBOL_MISSING: {ENTRY}"))?;
                Ok(entry.into_inner()(row[0], row[1], row[2], row[3]))
            }
        },
    )
}

fn oracle_rows(module: &trust_ir::Module, rows: &[[i64; 4]]) -> Vec<RunResult> {
    rows.iter()
        .map(|row| {
            capture(|| {
                run_oracle_one(module, row).map_err(|error| format!("ORACLE_ERR: {error:?}"))
            })
        })
        .collect()
}

fn reference_module(cfg: Cfg) -> trust_ir::Module {
    // This fixture's only memory operation is a store of args[0] immediately
    // followed by an I64 load from the same private alloca. Its address never
    // escapes, and no call or other write intervenes. The register-only shape
    // therefore computes the same expected value without asking the interpreter
    // to model Alloca. Keep memory enabled in the JIT module under test. This is
    // a generator-specific reference, never an error-triggered oracle fallback
    // or a general permission to erase memory operations from arbitrary IR.
    build_module(Cfg {
        use_memory: false,
        ..cfg
    })
}

fn compare_results(expected: &RunResult, actual: &RunResult) -> Result<(), String> {
    match (expected, actual) {
        (Ok(expected), Ok(actual)) if expected == actual => Ok(()),
        _ => Err(format!("expected={expected:?}, actual={actual:?}")),
    }
}

#[test]
fn harness_missing_results_and_equal_failures_are_not_agreement() {
    let values = [
        Ok(1),
        Ok(2),
        Err("compile failure".to_owned()),
        Err("oracle failure".to_owned()),
    ];
    for expected in &values {
        for actual in &values {
            let real_agreement = matches!((expected, actual), (Ok(a), Ok(b)) if a == b);
            assert_eq!(compare_results(expected, actual).is_ok(), real_agreement);
        }
    }
}

#[test]
fn harness_compiles_once_and_executes_every_input_row() {
    let rows = rows();
    let mut compilations = 0;
    let mut executions = 0;
    let actual = run_rows(
        &rows,
        || {
            compilations += 1;
            Ok(42_i64)
        },
        |artifact, row| {
            executions += 1;
            Ok(artifact.wrapping_add(row[0]))
        },
    );
    assert_eq!(compilations, 1);
    assert_eq!(executions, rows.len());
    assert_eq!(
        actual,
        rows.iter()
            .map(|row| Ok(42_i64.wrapping_add(row[0])))
            .collect::<Vec<_>>()
    );
}

#[test]
fn harness_compile_and_execution_failures_preserve_all_rows() {
    let rows = rows();
    for panics in [false, true] {
        let actual = run_rows::<()>(
            &rows,
            || {
                if panics {
                    panic!("compile panic control");
                }
                Err("compile error control".to_owned())
            },
            |_, _| panic!("failed compilation must never execute"),
        );
        assert_eq!(actual.len(), rows.len());
        assert!(actual.iter().all(Result::is_err));
    }
    let mut executions = 0;
    let actual = run_rows(
        &rows,
        || Ok(()),
        |_, _| {
            executions += 1;
            match executions {
                1 => panic!("execution panic control"),
                2 => Err("missing symbol control".to_owned()),
                _ => Ok(42),
            }
        },
    );
    assert_eq!(executions, rows.len());
    assert!(actual[0].is_err());
    assert!(actual[1].is_err());
    assert!(actual[2..].iter().all(|result| result == &Ok(42)));
}

#[test]
fn harness_memory_reference_executes_and_compares_every_row() {
    let cfg = Cfg::gpr(8, 1, 0, true);
    let rows = rows();
    let expected = oracle_rows(&reference_module(cfg), &rows);
    let actual = jit_rows(&build_module(cfg), OptLevel::O0, true, false, &rows);
    assert_eq!(actual.len(), rows.len());
    assert_eq!(expected.len(), rows.len());
    assert!(expected.iter().all(Result::is_ok));
    for (expected, actual) in expected.iter().zip(&actual) {
        compare_results(expected, actual)
            .expect("private store/load fixture must match its reference");
    }
}

#[test]
fn call_crossing_indirect_matches_direct() {
    // Build identical computations as direct-call and indirect-call modules.
    // Check both forms against the interpreter for each exact configuration,
    // as well as against each other. Agreement of two JIT paths is not proof,
    // and another sweep is not an oracle for this sweep's different shapes.
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
        let oracle = oracle_rows(&direct_mod, &rows);
        for jit_fast in [true, false] {
            for opt in [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3] {
                let direct = jit_rows(&direct_mod, opt, jit_fast, false, &rows);
                let indirect = jit_rows(&indirect_mod, opt, jit_fast, true, &rows);
                assert_eq!(direct.len(), rows.len());
                assert_eq!(indirect.len(), rows.len());
                for (index, row) in rows.iter().enumerate() {
                    for (label, expected, actual) in [
                        ("DIRECT/ORACLE", &oracle[index], &direct[index]),
                        ("INDIRECT/ORACLE", &oracle[index], &indirect[index]),
                        ("INDIRECT/DIRECT", &direct[index], &indirect[index]),
                    ] {
                        if let Err(error) = compare_results(expected, actual) {
                            defects.push(format!(
                                "{label} cfg={base:?} row={row:?} fast={jit_fast} opt={opt:?}: {error}"
                            ));
                        }
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
    assert!(
        !configs.is_empty(),
        "a differential sweep needs configurations"
    );
    let mut n = 0;
    for &cfg in configs {
        // Indirect configurations belong to the paired sweep, not a silently
        // skipped request in this direct-only helper.
        if cfg.indirect {
            defects.push(format!("INVALID_DIRECT_SWEEP_CONFIG: {cfg:?}"));
            continue;
        }
        let module = build_module(cfg);
        n += 1;
        let oracle = oracle_rows(&reference_module(cfg), rows);
        for jit_fast in [true, false] {
            for opt in [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3] {
                let actual = jit_rows(&module, opt, jit_fast, false, rows);
                assert_eq!(actual.len(), rows.len());
                for (index, row) in rows.iter().enumerate() {
                    if let Err(error) = compare_results(&oracle[index], &actual[index]) {
                        defects.push(format!(
                            "DIRECT/ORACLE cfg={cfg:?} row={row:?} fast={jit_fast} opt={opt:?}: {error}"
                        ));
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

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes because it was silently refused.
fn permit_unlicensed() -> trust_cg_lower::CodegenLicensePolicy {
    trust_cg_lower::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit)
}
