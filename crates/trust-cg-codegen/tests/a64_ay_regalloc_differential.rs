// a64_ay_regalloc_differential.rs — AY-PBO optimal register allocator, 2nd-platform
// EXECUTION-differential on AArch64 via the on-host a64 interpreter [task #11].
//
// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
//
// # What this is (and why the aarch64 EXECUTION evidence matters)
//
// trust-cg's AY-PBO (Pseudo-Boolean-Optimization) register allocator is a
// WHOLE-VREG optimal allocator: it competes against the production LinearScan
// baseline and is KEPT under a lexicographic (spills, copies) keep-better
// criterion, gated by the always-on translation validator. The capability is
// proven end-to-end on x86 by an EXECUTION differential; the code is
// target-agnostic but native aarch64 execution is hardware-blocked on this x86
// box.
//
// This harness closes the aarch64 half of the both-platforms EXECUTION-evidence
// story WITHOUT ARM silicon: it compiles high-register-pressure trust-ir
// functions TWICE (greedy/LinearScan baseline vs the AY-PBO allocator), DECODES
// the emitted aarch64 `__text` with the repo's real leaf disassembler, and
// EXECUTES both streams under the faithful ARM-ARM-semantics interpreter
// (`common/a64_interp.rs`), asserting:
//
//   * AY-on == AY-off(greedy) == the trust-ir oracle, BIT-IDENTICALLY, at
//     O0/O2/O3 over several argument vectors (the correctness differential);
//   * the AY stream for the PRESSURED function is DISTINCT from greedy and was
//     KEPT (kept == AY, ENGAGED — NOT a silent greedy fallback): compiled with
//     FORCE_KEEP, a difference in the caller's OWN `__text` byte span from greedy
//     can ONLY arise when `allocate()` returned AY's VALIDATED allocation for that
//     function (a decline/reject restores greedy and the span MATCHES). Comparing
//     the caller SPAN (not the whole object) rules out distinctness being carried
//     by an unrelated function such as the trivial inlined helper. The reliably-
//     engaging class is the MUL-fed carriers (add/select tie the whole-vreg
//     assignment to greedy at O2/O3; the i128 caller declines at O2/O3 as its
//     doubled vreg count exceeds the anytime solve cap — engagement is asserted
//     only where deterministic; correctness is asserted everywhere);
//   * TEETH: corrupting one instruction word of the AY-on object makes the
//     differential FAIL (fail-closed teeth on the AY path).
//
// # HONEST FINDING: AY does NOT strictly beat LinearScan on these shapes
//
// The corpus is the SPILL-ACROSS-CALL family (carriers live across a helper call
// that clobbers the caller-saved registers). This is the shape where the
// WHOLE-VREG AY-PBO RELIABLY ENGAGES with a DISTINCT validated stream: greedy /
// LinearScan can SPLIT a carrier's live range (save/reload only around the call),
// whereas the whole-vreg PBO must keep-or-spill each carrier for its WHOLE range,
// so the two allocators structurally diverge. But that same structural fact means
// AY here has MORE-or-EQUAL spills than greedy, so the lexicographic keep-better
// criterion CORRECTLY keeps greedy under natural selection — FORCE_KEEP is what
// materializes AY's distinct stream for the differential (see
// `natural_keep_better_does_not_keep_worse_whole_vreg_ay`). Empirically, through
// the full aarch64 backend, whole-vreg AY-PBO does NOT strictly reduce spills vs
// LinearScan: single-block functions form INTERVAL graphs (linear scan is already
// optimal -> a tie), and larger instances TIME OUT the anytime PBO solver (a
// worse feasible incumbent). The strict AY spill-win is demonstrated only at the
// allocator-unit level (small K, no ABI/splitting overhead) by
// `trust-cg-regalloc`'s `ay_min_policy_never_worse_than_greedy_randomized`. The
// VALUE HERE is the EXECUTION evidence: AY's DISTINCT, VALIDATED aarch64 machine
// code executes correctly on-host across O0/O2/O3 — the same KIND of evidence x86
// has — exercising the 0cebdda-fixed validator's aarch64 path.
//
// # Why the EXECUTION differential is NOT ceremony (the validator blind spot)
//
// LRSPLIT-2 found + VALIDATOR-1 (0cebdda) FIXED an AY-PBO validator blind spot:
// the always-on validator PASSED a wrong whole-vreg AY allocation until 0cebdda
// added `check_physreg_interference` + incoming-arg reservations. That proved the
// validator is NOT a complete gate on its own -> the EXECUTION differential is the
// true backstop that catches what per-instruction certs + the validator can miss.
// This harness runs AY's emitted aarch64 machine code, exercising the FIXED
// validator's aarch64 path.
//
// # Honest ceiling (what this does NOT prove)
//
// This is ON-HOST execution of the emitted BYTES under an architectural
// interpreter, NOT execution on real ARM silicon (that needs qemu/native). The
// interpreter models architectural ISA semantics, not a concrete CPU; it shares
// the leaf decoder with the emitter (a common-mode decode bug would not be
// caught). The spill delta is a STATIC proxy, not a wall-clock speedup. Per
// DECODE-OR-REJECT, any spill/frame instruction the AY stream emits that the
// interpreter does not model fails CLOSED (`A64Error::Unsupported`), never a
// silent pass.

#![cfg(feature = "ay-regalloc")]

mod common;

use common::a64_interp::{A64Error, A64Interp, extract_text, symbol_addrs, text_branch_relocs};

use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::env_lock;
use trust_cg_codegen::interpreter::{InterpreterValue, interpret};
use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::target::{Target, TargetSpec};

use trust_cg_lift::disasm::aarch64::decode;
use trust_ir::{
    BinOp, Block as B, Constant, FuncTy, Function as F, Inst, InstrNode, Module as M, Ty,
};
use trust_ir::{BlockId, FuncId, ValueId};

use std::sync::Mutex;

const OPTS: [OptLevel; 3] = [OptLevel::O0, OptLevel::O2, OptLevel::O3];

// All three tests in this binary invoke the bounded anytime solver. Running
// them on separate libtest threads makes their wall-clock caps contend with one
// another and can turn a valid proof into `Unknown` on a loaded machine.
static AY_DIFFERENTIAL_TEST_LOCK: Mutex<()> = Mutex::new(());

/// Raw compile of `m` for aarch64 at `opt` with the CURRENT environment.
/// Callers run inside an `env_lock::with_env_edits` scope that establishes the
/// thread-local AY env overrides and restores them on exit.
fn compile_raw(m: &M, opt: OptLevel) -> Vec<u8> {
    // Explicit Darwin spec: the a64 interp harness parses Mach-O, and the
    // default target spec is host-OS-aware (ELF on a Linux host).
    // Cross-emission only; same pattern as a64_abi_probe.
    let c = Compiler::new_for_target_spec(
        CompilerConfig {
            opt_level: opt,
            target: Target::Aarch64,
            // Thread-local allocator overrides are intentionally consumed on this
            // test thread rather than propagated into a rayon pool.
            parallel: false,
            ..CompilerConfig::default()
        },
        TargetSpec::parse("aarch64-apple-darwin").expect("parse aarch64-apple-darwin target spec"),
    );
    c.compile(m).expect("aarch64 compile").object_code
}

/// Compile with the AY-PBO allocator DISABLED (the production LinearScan
/// baseline) — byte-identical to origin codegen.
fn compile_greedy(m: &M, opt: OptLevel) -> Vec<u8> {
    env_lock::with_env_edits(|env| {
        env.remove("TCG_AY_REGALLOC");
        env.remove("TCG_AY_REGALLOC_FORCE_KEEP");
        env.remove("TCG_AY_REGALLOC_STATS");
        compile_raw(m, opt)
    })
}

// Tractability bounds for the AY-PBO anytime solve. The DEFAULTS
// (max_vregs=64, max_pairs=4000, ms=200) keep the shipped allocator tractable on
// a small box; this harness RAISES them so the PBO can MODEL a deliberately
// high-pressure function (>26 simultaneously-live vregs on the 26-GPR aarch64
// set). The allocator ITSELF is unchanged — only its per-instance size/time
// budget is lifted so it engages on the stress corpus; the greedy/LinearScan
// baseline never consults these bounds, so the comparison stays fair.
fn set_ay_caps(env: &mut env_lock::EnvEditor<'_>) {
    env.set("TCG_AY_REGALLOC_MAX_VREGS", "400");
    env.set("TCG_AY_REGALLOC_MAX_PAIRS", "200000");
    env.set("TCG_AY_REGALLOC_MS", "1500");
}

/// Compile with the AY-PBO allocator ENABLED and FORCE_KEEP ON: AY's validated
/// allocation is materialized whenever it validates (backstop), so the emitted
/// stream is guaranteed to be AY's for the execution differential. STATS on so
/// the `[ay-regalloc] keep: ...` line prints under `--nocapture`.
fn compile_ay_forcekeep(m: &M, opt: OptLevel) -> Vec<u8> {
    env_lock::with_env_edits(|env| {
        env.set("TCG_AY_REGALLOC", "1");
        env.set("TCG_AY_REGALLOC_FORCE_KEEP", "1");
        env.set("TCG_AY_REGALLOC_STATS", "1");
        set_ay_caps(env);
        compile_raw(m, opt)
    })
}

/// Compile with AY ENABLED but FORCE_KEEP OFF: AY's stream is materialized ONLY
/// when it strictly WINS the lexicographic keep-better criterion. A `__text`
/// byte difference from greedy under this profile therefore PROVES AY beat greedy
/// (kept == AY, engaged, not a silent fallback).
fn compile_ay_natural(m: &M, opt: OptLevel) -> Vec<u8> {
    env_lock::with_env_edits(|env| {
        env.set("TCG_AY_REGALLOC", "1");
        env.remove("TCG_AY_REGALLOC_FORCE_KEEP");
        env.set("TCG_AY_REGALLOC_STATS", "1");
        set_ay_caps(env);
        compile_raw(m, opt)
    })
}

/// The faithful trust_ir interpreter oracle: single integer return as i128.
fn oracle(m: &M, func: &str, args: &[i128]) -> i128 {
    let iargs: Vec<InterpreterValue> = args.iter().map(|&a| InterpreterValue::Int(a)).collect();
    let out = interpret(m, func, &iargs).unwrap_or_else(|e| panic!("oracle {func}{args:?}: {e}"));
    out[0].as_int().expect("int oracle result")
}

/// The `__text` byte span of function `sym` — from its symbol address to the
/// next-higher defined `__text` symbol (or the section end). Comparing THIS span
/// (not the whole object) proves the SPECIFIC pressured function's stream
/// engaged AY, so a byte difference cannot be carried by an unrelated function
/// (e.g. the trivial helper).
fn func_span(obj: &[u8], sym: &str) -> Vec<u8> {
    let text = extract_text(obj);
    let addrs = symbol_addrs(obj);
    let start_va = *addrs
        .get(sym)
        .unwrap_or_else(|| panic!("symbol {sym} missing"));
    let text_end = text.addr + text.bytes.len() as u64;
    // Smallest symbol address strictly greater than start, within __text.
    let end_va = addrs
        .values()
        .copied()
        .filter(|&va| va > start_va && va <= text_end)
        .min()
        .unwrap_or(text_end);
    let s = (start_va - text.addr) as usize;
    let e = (end_va - text.addr) as usize;
    text.bytes[s..e].to_vec()
}

/// Run the emitted AArch64 `sym`, placing `regs` in x0.. , returning x0.
fn run_x0(obj: &[u8], sym: &str, regs: &[u64]) -> Result<u64, A64Error> {
    let text = extract_text(obj);
    let addrs = symbol_addrs(obj);
    let n_value = *addrs
        .get(sym)
        .unwrap_or_else(|| panic!("symbol {sym} missing"));
    let entry = (n_value - text.addr) as usize;
    let mut it = A64Interp::new(text.bytes).with_branch_relocs(text_branch_relocs(obj));
    for (i, &r) in regs.iter().enumerate() {
        it.set_x(i, r);
    }
    it.run(entry)
}

/// Run the emitted AArch64 `sym`, returning (x0, x1) for i128 results.
fn run_pair(obj: &[u8], sym: &str, regs: &[u64]) -> Result<(u64, u64), A64Error> {
    let text = extract_text(obj);
    let addrs = symbol_addrs(obj);
    let n_value = *addrs
        .get(sym)
        .unwrap_or_else(|| panic!("symbol {sym} missing"));
    let entry = (n_value - text.addr) as usize;
    let mut it = A64Interp::new(text.bytes).with_branch_relocs(text_branch_relocs(obj));
    for (i, &r) in regs.iter().enumerate() {
        it.set_x(i, r);
    }
    let x0 = it.run(entry)?;
    Ok((x0, it.x[1]))
}

// ===========================================================================
// High-register-pressure trust-ir builders (the SPILL-ACROSS-CALL family). Each
// forces `n` carriers live across a caller-saved-clobbering call on the 26-GPR
// aarch64 set (X0-X15, X19-X28), so the WHOLE-VREG AY-PBO reliably ENGAGES with a
// stream structurally DISTINCT from the split-capable LinearScan baseline.
// ===========================================================================

/// Emit the standard `helper(x) = x*3 + 1` leaf (FuncId 0) into `m`.
fn push_helper(m: &mut M, helper: &str) {
    let ft1 = m.add_func_type(FuncTy {
        params: vec![Ty::I64],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let mut h = F::new(FuncId::new(0), helper, ft1, BlockId::new(0));
    h.blocks = vec![B {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), Ty::I64)],
        body: vec![
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(3),
            })
            .with_result(ValueId::new(1)),
            InstrNode::new(Inst::BinOp {
                op: BinOp::Mul,
                ty: Ty::I64,
                lhs: ValueId::new(0),
                rhs: ValueId::new(1),
            })
            .with_result(ValueId::new(2)),
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(1),
            })
            .with_result(ValueId::new(3)),
            InstrNode::new(Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: ValueId::new(2),
                rhs: ValueId::new(3),
            })
            .with_result(ValueId::new(4)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(4)],
            }),
        ],
    }];
    m.add_function(h);
}

/// The per-carrier pre-call computation shape.
#[derive(Clone, Copy)]
enum PreOp {
    /// `v_i = a_(i%8) + K_i` (ADD-fed wide accumulator).
    Add,
    /// `v_i = a_(i%8) * K_i` (MUL/MADD-fed — the wide-multiply flavor; this is the
    /// class where the whole-vreg AY-PBO reliably engages a distinct caller
    /// stream, since the multiply keeps carriers live rather than simplified away).
    Mul,
}

/// A many-arg + spill-across-call function: define `n` i64 carriers from the args
/// (via `pre`), call the helper (clobbering the caller-saved registers), then sum
/// all `n` carriers + the call result — so ALL `n` carriers are live ACROSS the
/// call. Greedy/LinearScan can SPLIT a carrier's live range (save/reload only
/// around the call); the WHOLE-VREG AY-PBO cannot, so the two allocators produce
/// a STRUCTURALLY DISTINCT stream here (STP/LDP callee-save frames + spill slots)
/// — the reliable AY-engagement shape. `helper`=FuncId 0, `caller`=FuncId 1.
fn build_spill_across_call(helper: &str, caller: &str, n: u32, pre: PreOp) -> M {
    let mut m = M::new("spillcall");
    push_helper(&mut m, helper);

    let ft2 = m.add_func_type(FuncTy {
        params: vec![Ty::I64; 8],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let mut c = F::new(FuncId::new(1), caller, ft2, BlockId::new(0));
    let mut body = Vec::new();
    let mut id = 100u32;
    let mut fresh = move || {
        let v = ValueId::new(id);
        id += 1;
        v
    };
    let mut vals = Vec::new();
    for i in 0..n {
        let k = fresh();
        body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: Constant::Int((i as i128) * 2654435761 + 7),
            })
            .with_result(k),
        );
        let v = match pre {
            PreOp::Add => {
                let v = fresh();
                body.push(
                    InstrNode::new(Inst::BinOp {
                        op: BinOp::Add,
                        ty: Ty::I64,
                        lhs: ValueId::new(i % 8),
                        rhs: k,
                    })
                    .with_result(v),
                );
                v
            }
            PreOp::Mul => {
                let v = fresh();
                body.push(
                    InstrNode::new(Inst::BinOp {
                        op: BinOp::Mul,
                        ty: Ty::I64,
                        lhs: ValueId::new(i % 8),
                        rhs: k,
                    })
                    .with_result(v),
                );
                v
            }
        };
        vals.push(v);
    }
    // h = helper(a0) — clobbers caller-saved; all vals must survive.
    let hres = fresh();
    body.push(
        InstrNode::new(Inst::Call {
            callee: FuncId::new(0),
            args: vec![ValueId::new(0)],
        })
        .with_result(hres),
    );
    let mut acc = vals[0];
    for &v in &vals[1..] {
        let next = fresh();
        body.push(
            InstrNode::new(Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: acc,
                rhs: v,
            })
            .with_result(next),
        );
        acc = next;
    }
    let fin = fresh();
    body.push(
        InstrNode::new(Inst::BinOp {
            op: BinOp::Add,
            ty: Ty::I64,
            lhs: acc,
            rhs: hres,
        })
        .with_result(fin),
    );
    body.push(InstrNode::new(Inst::Return { values: vec![fin] }));
    c.blocks = vec![B {
        id: BlockId::new(0),
        params: (0..8u32).map(|i| (ValueId::new(i), Ty::I64)).collect(),
        body,
    }];
    m.add_function(c);
    m
}

/// i128 register pressure ACROSS a call: `n` i128 carriers `t_i = (x + K_i)`,
/// all live across a `helper` call, summed after. Each i128 occupies a PAIR of
/// i64 vregs contending for x0-x7 / the callee-saved set (the ADC/paired-limb
/// spill-across-call case). `helper`=FuncId 0, `caller`=FuncId 1.
fn build_i128_spill_across_call(helper: &str, caller: &str, n: u32) -> M {
    let mut m = M::new("i128spillcall");
    push_helper(&mut m, helper);

    let ft2 = m.add_func_type(FuncTy {
        params: vec![Ty::I128, Ty::I64],
        returns: vec![Ty::I128],
        is_vararg: false,
    });
    let mut c = F::new(FuncId::new(1), caller, ft2, BlockId::new(0));
    let x = ValueId::new(0); // i128 in x0:x1
    let y = ValueId::new(1); // i64 in x2
    let mut body = Vec::new();
    let mut id = 100u32;
    let mut fresh = move || {
        let v = ValueId::new(id);
        id += 1;
        v
    };
    let mut temps = Vec::new();
    for i in 0..n {
        let k = fresh();
        body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::I128,
                value: Constant::Int((i as i128) * 1099511628211 + 1),
            })
            .with_result(k),
        );
        let t = fresh();
        body.push(
            InstrNode::new(Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I128,
                lhs: x,
                rhs: k,
            })
            .with_result(t),
        );
        temps.push(t);
    }
    // h = helper(y) — clobbers caller-saved; all i128 temps must survive.
    let hres = fresh();
    body.push(
        InstrNode::new(Inst::Call {
            callee: FuncId::new(0),
            args: vec![y],
        })
        .with_result(hres),
    );
    // widen the i64 call result to i128 and fold everything together.
    let hres128 = fresh();
    body.push(
        InstrNode::new(Inst::Cast {
            op: trust_ir::CastOp::SExt,
            src_ty: Ty::I64,
            dst_ty: Ty::I128,
            operand: hres,
        })
        .with_result(hres128),
    );
    let mut acc = temps[0];
    for &t in &temps[1..] {
        let next = fresh();
        body.push(
            InstrNode::new(Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I128,
                lhs: acc,
                rhs: t,
            })
            .with_result(next),
        );
        acc = next;
    }
    let fin = fresh();
    body.push(
        InstrNode::new(Inst::BinOp {
            op: BinOp::Add,
            ty: Ty::I128,
            lhs: acc,
            rhs: hres128,
        })
        .with_result(fin),
    );
    body.push(InstrNode::new(Inst::Return { values: vec![fin] }));
    c.blocks = vec![B {
        id: BlockId::new(0),
        params: vec![(x, Ty::I128), (y, Ty::I64)],
        body,
    }];
    m.add_function(c);
    m
}

// ===========================================================================
// The 2nd-platform EXECUTION differential. For each pressure function x
// {O0,O2,O3}: compile GREEDY (AY off) and AY-FORCE_KEEP (AY's validated whole-
// vreg allocation materialized), DECODE + EXECUTE both on-host, and assert
//   * AY-on == AY-off(greedy) == the trust-ir oracle, BIT-IDENTICALLY, over
//     several argument vectors (the correctness differential);
//   * AY's stream is DISTINCT from greedy (kept == AY, ENGAGED — not a silent
//     greedy fallback): under FORCE_KEEP a byte difference can ONLY arise when
//     `allocate()` returned AY's validated allocation; a decline/reject would
//     restore greedy and the bytes would MATCH. This is the kept==AY gate.
// ===========================================================================

const SCALAR_ARGVECS: [[i64; 8]; 5] = [
    [3, 9, 2, 7, 5, 1, 8, 4],
    [0, 0, 0, 0, 0, 0, 0, 0],
    [-1, -2, -3, -4, -5, -6, -7, -8],
    [i64::MAX, i64::MIN, 1, -1, 100, -100, 7, 3],
    [1_000_000, 999, -1, i64::MIN, i64::MAX, 0, 42, -42],
];

/// Mismatch collector — accumulate the full blast radius, not just the first.
#[derive(Default)]
struct Deliv {
    programs: usize,
    runs: usize,
    engaged: usize,
    engage_checks: usize,
    mismatches: Vec<String>,
}

impl Deliv {
    fn mask64(v: i128) -> u128 {
        (v as u128) & u128::from(u64::MAX)
    }

    /// ENGAGEMENT gate: AY's validated stream for THIS pressured function (its own
    /// __text byte span, not the whole object) must be DISTINCT from greedy
    /// (kept==AY, not a silent fallback) at every opt in `engage_opts`. Comparing
    /// the caller's SPAN rules out distinctness being carried by an unrelated
    /// function (e.g. the trivial inlined helper). At opts NOT in `engage_opts` the
    /// correctness differential still runs (AY may validly fall back to greedy).
    fn check_engage(
        &mut self,
        tag: &str,
        sym: &str,
        opt: OptLevel,
        engage_opts: &[OptLevel],
        g: &[u8],
        ay: &[u8],
    ) {
        if !engage_opts.contains(&opt) {
            return;
        }
        self.engage_checks += 1;
        if func_span(ay, sym) != func_span(g, sym) {
            self.engaged += 1;
        } else {
            self.mismatches.push(format!(
                "NOT-ENGAGED {tag} @ {opt:?}: AY caller span byte-identical to greedy \
                 (silent fallback / AY declined — kept!=AY)"
            ));
        }
    }

    /// A scalar-i64-return spill-across-call function across O0/O2/O3.
    fn scalar(&mut self, tag: &str, m: &M, func: &str, sym: &str, engage_opts: &[OptLevel]) {
        self.programs += 1;
        for &opt in &OPTS {
            let g = compile_greedy(m, opt);
            let ay = compile_ay_forcekeep(m, opt);
            self.check_engage(tag, sym, opt, engage_opts, &g, &ay);
            for args in &SCALAR_ARGVECS {
                self.runs += 1;
                let regs: Vec<u64> = args.iter().map(|&a| a as u64).collect();
                let want = Self::mask64(oracle(
                    m,
                    func,
                    &args.iter().map(|&a| a as i128).collect::<Vec<_>>(),
                ));
                let rg = run_x0(&g, sym, &regs);
                let ra = run_x0(&ay, sym, &regs);
                match (rg, ra) {
                    (Ok(gx), Ok(ax)) => {
                        let (gv, av) = (gx as u128, ax as u128);
                        if gv != want || av != want || gv != av {
                            self.mismatches.push(format!(
                                "MISCOMPILE {tag}{args:?} @ {opt:?}: greedy={} ay={} want={}",
                                gv as i64, av as i64, want as i64
                            ));
                        }
                    }
                    (rg, ra) => self.mismatches.push(format!(
                        "INTERP-ERR {tag}{args:?} @ {opt:?}: greedy={rg:?} ay={ra:?}"
                    )),
                }
            }
        }
    }

    /// The i128-return spill-across-call function across O0/O2/O3.
    fn i128(
        &mut self,
        tag: &str,
        m: &M,
        func: &str,
        sym: &str,
        engage_opts: &[OptLevel],
        cases: &[(i128, i64)],
    ) {
        self.programs += 1;
        for &opt in &OPTS {
            let g = compile_greedy(m, opt);
            let ay = compile_ay_forcekeep(m, opt);
            self.check_engage(tag, sym, opt, engage_opts, &g, &ay);
            for &(x, y) in cases {
                self.runs += 1;
                let want = oracle(m, func, &[x, y as i128]) as u128;
                let regs = [x as u64, (x >> 64) as u64, y as u64];
                let rg = run_pair(&g, sym, &regs);
                let ra = run_pair(&ay, sym, &regs);
                match (rg, ra) {
                    (Ok((gx0, gx1)), Ok((ax0, ax1))) => {
                        let gv = (gx0 as u128) | ((gx1 as u128) << 64);
                        let av = (ax0 as u128) | ((ax1 as u128) << 64);
                        if gv != want || av != want || gv != av {
                            self.mismatches.push(format!(
                                "MISCOMPILE(i128) {tag}({x},{y}) @ {opt:?}: greedy={} ay={} want={}",
                                gv as i128, av as i128, want as i128
                            ));
                        }
                    }
                    (rg, ra) => self.mismatches.push(format!(
                        "INTERP-ERR(i128) {tag}({x},{y}) @ {opt:?}: greedy={rg:?} ay={ra:?}"
                    )),
                }
            }
        }
    }

    fn finish(self) {
        eprintln!(
            "[AY-A64] {} programs, {} O0/O2/O3 runs, AY engaged on {}/{} (fn,opt) cells, {} mismatches",
            self.programs,
            self.runs,
            self.engaged,
            self.engage_checks,
            self.mismatches.len()
        );
        assert!(
            self.mismatches.is_empty(),
            "AArch64 AY-PBO execution differential found {} issue(s):\n{}",
            self.mismatches.len(),
            self.mismatches.join("\n")
        );
        assert_eq!(
            self.engaged, self.engage_checks,
            "AY must ENGAGE (produce a DISTINCT validated stream, kept==AY) on every \
             (fn,opt) cell — a byte-identical stream means a silent greedy fallback"
        );
    }
}

#[test]
fn ay_pbo_aarch64_execution_differential() {
    let _guard = AY_DIFFERENTIAL_TEST_LOCK
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);

    let mut d = Deliv::default();
    const ALL: [OptLevel; 3] = [OptLevel::O0, OptLevel::O2, OptLevel::O3];
    const O0_ONLY: [OptLevel; 1] = [OptLevel::O0];

    // MUL/MADD-fed wide accumulator + many-arg, all live across a call. The
    // multiply keeps the carriers genuinely live (not simplified/inlined away), so
    // the whole-vreg AY-PBO RELIABLY produces a DISTINCT validated caller stream at
    // O0/O2/O3 (verified deterministic across passes). Three sizes.
    for n in [12u32, 14, 16] {
        let tag = format!("sc_mul{n}");
        let m =
            build_spill_across_call(&format!("_h_mul{n}"), &format!("_sc_mul{n}"), n, PreOp::Mul);
        d.scalar(
            &tag,
            &m,
            &format!("_sc_mul{n}"),
            &format!("__sc_mul{n}"),
            &ALL,
        );
    }

    // i128 paired-limb pressure across a call. The i128 lowering DOUBLES the vreg
    // count; the whole-vreg PBO reaches a distinct validated caller stream at O0,
    // but at O2/O3 the doubled instance declines within the solve cap (validly
    // falling back to greedy) — so engagement is REQUIRED only at O0 while the
    // FULL 128-bit correctness differential runs at O0/O2/O3.
    let i128m = build_i128_spill_across_call("_h_i128", "_sc_i128", 8);
    let big: i128 = 0x0123_4567_89AB_CDEF_1122_3344_5566_7788u128 as i128;
    let neg: i128 = -0x0000_0000_0000_0007_0000_0000_0000_0003i128;
    d.i128(
        "sc_i128",
        &i128m,
        "_sc_i128",
        "__sc_i128",
        &O0_ONLY,
        &[(big, 5), (neg, -3), (0, 0), (i128::MAX, 7), (-1, 1)],
    );

    d.finish();
}

/// HONEST complement: the whole-vreg AY-PBO does NOT strictly beat the LinearScan
/// baseline on these across-call shapes — greedy can SPLIT a carrier's live range
/// (save/reload only around the call) whereas the whole-vreg PBO must keep or
/// spill each carrier for its WHOLE range, so AY's validated allocation here has
/// MORE (or equal) spills. The lexicographic run-both-keep-better criterion
/// therefore correctly KEEPS GREEDY under natural (non-FORCE_KEEP) selection: AY
/// is materialized ONLY because FORCE_KEEP requests it. This documents that
/// FORCE_KEEP is load-bearing for this corpus (the execution differential still
/// proves AY's distinct validated stream runs correctly — the point of the test).
#[test]
fn natural_keep_better_does_not_keep_worse_whole_vreg_ay() {
    let _guard = AY_DIFFERENTIAL_TEST_LOCK
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);

    // On a representative mul-fed across-call shape, the natural (keep-better) AY
    // selection returns the GREEDY caller stream (whole-vreg AY not better),
    // proving the keep-better gate never regresses quality — while FORCE_KEEP
    // still materializes AY's DISTINCT validated caller stream for the
    // differential. (Comparing the caller SPAN isolates the pressured function.)
    let m = build_spill_across_call("_h_nat", "_sc_nat", 16, PreOp::Mul);
    let sym = "__sc_nat";
    let g = compile_greedy(&m, OptLevel::O0);
    let ay_natural = compile_ay_natural(&m, OptLevel::O0);
    let ay_forced = compile_ay_forcekeep(&m, OptLevel::O0);
    assert_eq!(
        func_span(&ay_natural, sym),
        func_span(&g, sym),
        "keep-better must return the greedy caller stream when whole-vreg AY is not better"
    );
    assert_ne!(
        func_span(&ay_forced, sym),
        func_span(&g, sym),
        "FORCE_KEEP must materialize AY's distinct validated caller stream"
    );
}

// ===========================================================================
// TEETH: prove the AY-path differential DETECTS a miscompile — corrupt one
// instruction word of the AY-on object and assert the interpreter now disagrees
// with the oracle. Symmetric to the corpus TEETH; fail-closed on the AY path.
// ===========================================================================

use trust_cg_lift::disasm::aarch64::Instruction as A64Instr;

/// Locate the first instruction word matching `pred` in `bytes` and rewrite it
/// with `mangle`; false if none matched. Located by DECODING, so robust to
/// register allocation.
fn corrupt_first(
    bytes: &mut [u8],
    pred: impl Fn(&A64Instr) -> bool,
    mangle: impl Fn(u32) -> u32,
) -> bool {
    let mut i = 0;
    while i + 4 <= bytes.len() {
        let w = u32::from_le_bytes([bytes[i], bytes[i + 1], bytes[i + 2], bytes[i + 3]]);
        if let Ok(ins) = decode(w)
            && pred(&ins)
        {
            bytes[i..i + 4].copy_from_slice(&mangle(w).to_le_bytes());
            return true;
        }
        i += 4;
    }
    false
}

#[test]
fn teeth_ay_path_detects_a_corrupted_instruction() {
    let _guard = AY_DIFFERENTIAL_TEST_LOCK
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);

    // Compile the add-fed spill-across-call with AY FORCE_KEEP, corrupt the first
    // ADD (shifted-register) in the AY stream into a SUB (flip bit 30, op=1), and
    // assert the AY differential now DIVERGES from the oracle — the harness has
    // teeth on the AY-emitted machine code.
    let m = build_spill_across_call("_h_teeth", "_sc_teeth", 14, PreOp::Add);
    let args = SCALAR_ARGVECS[0];
    let regs: Vec<u64> = args.iter().map(|&a| a as u64).collect();
    let want = (oracle(
        &m,
        "_sc_teeth",
        &args.iter().map(|&a| a as i128).collect::<Vec<_>>(),
    ) as u128)
        & u128::from(u64::MAX);

    let ay = compile_ay_forcekeep(&m, OptLevel::O0);
    // Sanity: pristine AY stream matches the oracle.
    let pristine = run_x0(&ay, "__sc_teeth", &regs).expect("pristine AY runs") as u128;
    assert_eq!(pristine, want, "pristine AY stream must match the oracle");

    // Corrupt one ADD (shifted-register, op==0, set_flags==false) -> SUB (op=1).
    let text = extract_text(&ay);
    let addrs = symbol_addrs(&ay);
    let entry = (*addrs.get("__sc_teeth").expect("sym") - text.addr) as usize;
    let mut bytes = text.bytes;
    let corrupted = corrupt_first(
        &mut bytes,
        |ins| matches!(ins, A64Instr::AddSubShiftedReg(a) if a.op == 0 && !a.set_flags),
        |w| w | (1u32 << 30), // ADD -> SUB (bit 30 = op)
    );
    assert!(
        corrupted,
        "teeth: no ADD (shifted-reg) found in the AY stream to corrupt"
    );

    let mut it = A64Interp::new(bytes).with_branch_relocs(text_branch_relocs(&ay));
    for (i, &r) in regs.iter().enumerate() {
        it.set_x(i, r);
    }
    let got = it.run(entry).expect("corrupted AY body still decodes+runs") as u128;
    assert_ne!(
        got, want,
        "TEETH: corrupting an ADD->SUB in the AY-emitted stream must change the result; \
         the AY-path differential fails closed on a corrupted instruction"
    );
}
