// a64_corpus_sweep.rs — on-host AArch64 CORRECTNESS SWEEP of the differential
// corpus [A64HARNESS-2].
//
// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
//
// # What this is
//
// A64HARNESS-1 stood up a decode-and-interpret AArch64 machine model
// (`common/a64_interp.rs`) and used it to convert the fail-OPEN "skip on x86"
// AArch64 e2e tests into fail-CLOSED on-host assertions for the narrow-compare
// and FP-compare classes. This harness EXTENDS that model (div/rem, multiply,
// long/high multiply, add-with-carry, variable + immediate shifts, memory
// load/store + STP/LDP frames, ADR/BR jump tables, and real `bl`/`ret` calls
// resolved through the object's ARM64_RELOC_BRANCH26 relocations) and runs a
// broad slice of the differential corpus THROUGH THE AARCH64 BACKEND — the
// separate `isel.rs` + LinearScan allocator that has historically hidden
// AArch64-only miscompiles — decoding and interpreting the emitted machine code
// on this x86 box and diffing every result against the faithful
// `trust_cg_codegen::interpreter` oracle at O0/O2/O3.
//
// qemu-aarch64 is not installed on this box, so real AArch64 EXECUTION is
// unavailable; the decode+interpret path is the broadest correctness coverage
// achievable on-host. Per the DECODE-OR-REJECT mandate neither `decode()` nor
// the interpreter SKIPS a word: an unmodeled word is an error, never a NOP.
//
// The strength of that mandate is bounded by the DECODER'S ALLOCATION FIDELITY,
// and that bound is measured, not assumed. A word the decoder accepts under the
// WRONG NAME is executed with the wrong semantics, and no amount of fail-closed
// discipline downstream catches it. As of 2026-08-10 the decoder is differential-
// tested against Apple/LLVM 21 objdump over 5,078,879 words (uniform-random,
// exhaustive field sweeps, and mutations of assembler-derived bases): GHOST 0
// (words it names that the reference calls undefined) and MISMATCH 0 (words it
// resolves onto a different allocated instruction). Before 2026-08-10 those
// counts were 127,678 and 72,236 respectively, and this comment claimed the
// mandate made a false PASS impossible — it did not. See
// `trust-cg-lift/tests/aarch64_allocation.rs` for the regression pins.
//
// Residual, and deliberately unclaimed: the differential compares MNEMONICS, so
// it is structurally blind to operand-level CONSTRAINED UNPREDICTABLE aliasing,
// and the reference itself decodes with the full feature set (making GHOST a
// lower bound). This harness is strong evidence, not a proof.
//
// # Covered corpus zones (all historically AArch64-buggy)
//
//   * arithmetic / logic / abs / max            (add, sub, mul, and/or/xor, neg)
//   * signed & unsigned div / rem               (incl. INT_MIN/-1 and /-ve)
//   * variable & immediate shifts (32 and 64)   (LSLV/LSRV/ASRV, UBFM/SBFM)
//   * narrow int (i8/i16/u8/u16) op + extension  (trunc → op → sext/zext)
//   * checked overflow (add/sub/mul, u32 & i8)   (ADDS/SUBS/MUL + flag)
//   * select / cmov chains + clamp               (CSEL/CSINC, deep live ranges)
//   * loops & control flow                       (gcd, collatz, sum, ipow, fib)
//   * calls, recursion, spills across calls      (bl/ret + STP/LDP frames)
//   * stack-passed arguments (>8 params)         (caller stores, callee loads)
//   * dense switch → ADR/LDRSW/BR jump table      (the switch/BST bug zone)
//   * i128 add/sub/mul/and/or/xor/shl, compare, mulhi (ADC/UMULH/SMULH pairs)

mod common;
use common::a64_interp::A64Error;
use common::x86_64_corpus as corpus;

use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::interpreter::{InterpreterValue, interpret};
use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::target::Target;

use trust_ir::{
    BinOp, Block as B, CastOp, Constant, FuncTy, Function as F, ICmpOp, Inst, InstrNode,
    Module as M, OverflowOp, SwitchCase, Ty,
};
use trust_ir::{BlockId, FuncId, ValueId};

const OPTS: [OptLevel; 3] = [OptLevel::O0, OptLevel::O2, OptLevel::O3];

fn compile(m: &M, opt: OptLevel) -> Vec<u8> {
    let c = Compiler::new(CompilerConfig {
        opt_level: opt,
        target: Target::Aarch64,
        ..CompilerConfig::default()
    });
    c.compile(m).expect("aarch64 compile").object_code
}

/// The faithful trust_ir interpreter oracle: single integer return as i128.
fn oracle(m: &M, func: &str, args: &[i128]) -> i128 {
    let iargs: Vec<InterpreterValue> = args.iter().map(|&a| InterpreterValue::Int(a)).collect();
    let out = interpret(m, func, &iargs).unwrap_or_else(|e| panic!("oracle {func}{args:?}: {e}"));
    out[0].as_int().expect("int oracle result")
}

/// Run the emitted AArch64 `sym`, placing `regs` in x0.. , returning (x0, x1).
fn run_pair(obj: &[u8], sym: &str, regs: &[u64]) -> Result<(u64, u64), A64Error> {
    // `run_func` installs the branch-relocation map and returns x0; we also want
    // x1 for i128 returns, so re-run capturing the whole register file is not
    // exposed — instead we thread x1 via a second call is unnecessary: the model
    // is deterministic, so a single run through `run_func` with a side channel is
    // avoided by reading x1 directly here.
    // run_func gives x0; for the high half we re-interpret with the same setup
    // and read x1 from the interpreter directly.
    use common::a64_interp::{A64Interp, extract_text, symbol_addrs, text_branch_relocs};
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

/// Mismatch collector — accumulate ALL disagreements so a sweep reports the full
/// blast radius, not just the first failure.
#[derive(Default)]
struct Sweep {
    programs: usize,
    runs: usize,
    mismatches: Vec<String>,
}

impl Sweep {
    fn mask(bits: u32) -> u128 {
        if bits >= 128 {
            u128::MAX
        } else {
            (1u128 << bits) - 1
        }
    }

    /// A scalar-integer function: `args` (i64 each) placed in x0.. , result read
    /// from x0 and compared low-`ret_bits` against the oracle.
    fn scalar(&mut self, m: &M, func: &str, sym: &str, ret_bits: u32, cases: &[Vec<i64>]) {
        self.programs += 1;
        for args in cases {
            let want = oracle(
                m,
                func,
                &args.iter().map(|&a| a as i128).collect::<Vec<_>>(),
            );
            let want_low = (want as u128) & Self::mask(ret_bits);
            let regs: Vec<u64> = args.iter().map(|&a| a as u64).collect();
            for &opt in &OPTS {
                self.runs += 1;
                let obj = compile(m, opt);
                match run_pair(&obj, sym, &regs) {
                    Ok((x0, _)) => {
                        let got = (x0 as u128) & Self::mask(ret_bits);
                        if got != want_low {
                            self.mismatches.push(format!(
                                "MISCOMPILE {func}{args:?} @ {opt:?}: got {}, want {} (ret {ret_bits}b)",
                                got as i128, want_low as i128
                            ));
                        }
                    }
                    Err(e) => self
                        .mismatches
                        .push(format!("INTERP-ERR {func}{args:?} @ {opt:?}: {e:?}")),
                }
            }
        }
    }

    /// An i128×i128→i128 function: args split lo/hi across x0..x3, result read
    /// from x0:x1.
    fn i128_binop(&mut self, m: &M, func: &str, sym: &str, cases: &[(i128, i128)]) {
        self.programs += 1;
        for &(a, b) in cases {
            let want = oracle(m, func, &[a, b]) as u128;
            let regs = [a as u64, (a >> 64) as u64, b as u64, (b >> 64) as u64];
            for &opt in &OPTS {
                self.runs += 1;
                let obj = compile(m, opt);
                match run_pair(&obj, sym, &regs) {
                    Ok((x0, x1)) => {
                        let got = (x0 as u128) | ((x1 as u128) << 64);
                        if got != want {
                            self.mismatches.push(format!(
                                "MISCOMPILE(i128) {func}({a},{b}) @ {opt:?}: got {}, want {}",
                                got as i128, want as i128
                            ));
                        }
                    }
                    Err(e) => self
                        .mismatches
                        .push(format!("INTERP-ERR(i128) {func}({a},{b}) @ {opt:?}: {e:?}")),
                }
            }
        }
    }

    /// An i128×i128→i64 function (e.g. compare): args lo/hi across x0..x3, i64
    /// result from x0.
    fn i128_to_i64(&mut self, m: &M, func: &str, sym: &str, cases: &[(i128, i128)]) {
        self.programs += 1;
        for &(a, b) in cases {
            let want = oracle(m, func, &[a, b]) as u64;
            let regs = [a as u64, (a >> 64) as u64, b as u64, (b >> 64) as u64];
            for &opt in &OPTS {
                self.runs += 1;
                let obj = compile(m, opt);
                match run_pair(&obj, sym, &regs) {
                    Ok((x0, _)) => {
                        if x0 != want {
                            self.mismatches.push(format!(
                                "MISCOMPILE(i128cmp) {func}({a},{b}) @ {opt:?}: got {x0}, want {want}"
                            ));
                        }
                    }
                    Err(e) => self
                        .mismatches
                        .push(format!("INTERP-ERR {func}({a},{b}) @ {opt:?}: {e:?}")),
                }
            }
        }
    }

    fn finish(self, label: &str) {
        eprintln!(
            "[A64HARNESS-2] {label}: {} programs, {} O0/O2/O3 runs, {} mismatches",
            self.programs,
            self.runs,
            self.mismatches.len()
        );
        assert!(
            self.mismatches.is_empty(),
            "AArch64 corpus sweep found {} mismatch(es):\n{}",
            self.mismatches.len(),
            self.mismatches.join("\n")
        );

        // TV-6 (a64 post-RA reaching-definition net, f29676f2) soundness gate.
        // The net runs at WARN on every a64 compile in this sweep; on this KNOWN-
        // CORRECT corpus it must NEVER report a violation. A non-zero hit count is
        // a FALSE-WARN regression in the reaching-def def/use model (e.g. a new
        // opcode whose def-role the validator misclassifies) — catch it here so
        // the model stays sound before the WARN->Enforce ratchet. This turns the
        // ad-hoc ~2984-function soak into a standing gate.
        {
            use trust_cg_verify::post_ra_reaching_def as prd;
            let (analyzed, declined) = prd::coverage_counts();
            eprintln!(
                "[TV-6] reaching-def net over this sweep: {analyzed} analyzed, {declined} declined, {} hits",
                prd::reaching_def_hit_count()
            );
            assert_eq!(
                prd::reaching_def_hit_count(),
                0,
                "TV-6 a64 reaching-def net FALSE-WARNed on the correct corpus — a def/use-model regression"
            );
        }

        // TV-6 (a64 post-RA spill-SLOT reaching-store net) soundness gate. The
        // net runs at WARN on every a64 compile in this sweep; on this KNOWN-
        // CORRECT corpus it must NEVER report a violation. A non-zero hit count is
        // a FALSE-WARN regression in the SP-relative spill-slot model (e.g. a new
        // frameless spill shape the tracker mis-classifies) — catch it here before
        // the WARN->Enforce ratchet. Most functions DECLINE (their spills are
        // FP-relative); the analyzed set is the frameless / red-zone-leaf lane.
        {
            use trust_cg_verify::post_ra_spill_slots as pss;
            let (analyzed, declined) = pss::coverage_counts();
            eprintln!(
                "[TV-6] spill-slot net over this sweep: {analyzed} analyzed, {declined} declined, {} hits",
                pss::spill_slot_hit_count()
            );
            assert_eq!(
                pss::spill_slot_hit_count(),
                0,
                "TV-6 a64 spill-slot net FALSE-WARNed on the correct corpus — an SP-slot-model regression"
            );
        }
    }
}

// ===========================================================================
// Local trust_ir builders for zones the shared corpus does not cover
// ===========================================================================

/// `fn _f(a: TY, b: TY) -> TY { a <op> b }` — a straight-line binary op.
fn build_bin(name: &str, ty: Ty, op: BinOp) -> M {
    let mut m = M::new("bin");
    let ft = m.add_func_type(FuncTy {
        params: vec![ty.clone(), ty.clone()],
        returns: vec![ty.clone()],
        is_vararg: false,
    });
    let mut f = F::new(FuncId::new(0), name, ft, BlockId::new(0));
    f.blocks = vec![B {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), ty.clone()), (ValueId::new(1), ty.clone())],
        body: vec![
            InstrNode::new(Inst::BinOp {
                op,
                ty,
                lhs: ValueId::new(0),
                rhs: ValueId::new(1),
            })
            .with_result(ValueId::new(2)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(2)],
            }),
        ],
    }];
    m.add_function(f);
    m
}

/// `fn _f(a: i32, b: i32) -> i32 { ((a as N) <op> (b as N)) as i32 }` where the
/// final widening is SExt for a signed narrow type and ZExt for an unsigned one.
fn build_narrow_bin(name: &str, narrow: Ty, op: BinOp, signed: bool) -> M {
    let mut m = M::new("nbin");
    let ft = m.add_func_type(FuncTy {
        params: vec![Ty::I32, Ty::I32],
        returns: vec![Ty::I32],
        is_vararg: false,
    });
    let mut f = F::new(FuncId::new(0), name, ft, BlockId::new(0));
    f.blocks = vec![B {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), Ty::I32), (ValueId::new(1), Ty::I32)],
        body: vec![
            InstrNode::new(Inst::Cast {
                op: CastOp::Trunc,
                src_ty: Ty::I32,
                dst_ty: narrow.clone(),
                operand: ValueId::new(0),
            })
            .with_result(ValueId::new(2)),
            InstrNode::new(Inst::Cast {
                op: CastOp::Trunc,
                src_ty: Ty::I32,
                dst_ty: narrow.clone(),
                operand: ValueId::new(1),
            })
            .with_result(ValueId::new(3)),
            InstrNode::new(Inst::BinOp {
                op,
                ty: narrow.clone(),
                lhs: ValueId::new(2),
                rhs: ValueId::new(3),
            })
            .with_result(ValueId::new(4)),
            InstrNode::new(Inst::Cast {
                op: if signed { CastOp::SExt } else { CastOp::ZExt },
                src_ty: narrow,
                dst_ty: Ty::I32,
                operand: ValueId::new(4),
            })
            .with_result(ValueId::new(5)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(5)],
            }),
        ],
    }];
    m.add_function(f);
    m
}

/// `fn _f(a: TY) -> TY { a <op> IMM }` — an immediate shift (UBFM/SBFM path).
fn build_shift_imm(name: &str, ty: Ty, op: BinOp, amount: i128) -> M {
    let mut m = M::new("shimm");
    let ft = m.add_func_type(FuncTy {
        params: vec![ty.clone()],
        returns: vec![ty.clone()],
        is_vararg: false,
    });
    let mut f = F::new(FuncId::new(0), name, ft, BlockId::new(0));
    f.blocks = vec![B {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), ty.clone())],
        body: vec![
            InstrNode::new(Inst::Const {
                ty: ty.clone(),
                value: Constant::Int(amount),
            })
            .with_result(ValueId::new(1)),
            InstrNode::new(Inst::BinOp {
                op,
                ty,
                lhs: ValueId::new(0),
                rhs: ValueId::new(1),
            })
            .with_result(ValueId::new(2)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(2)],
            }),
        ],
    }];
    m.add_function(f);
    m
}

/// `fn _f(a: TY, b: TY) -> i32 { a.<op>_overflow(b).1 as i32 }` — the checked
/// overflow FLAG, zero-extended to i32.
fn build_overflow(name: &str, ty: Ty, op: OverflowOp) -> M {
    let mut m = M::new("ovf");
    let ft = m.add_func_type(FuncTy {
        params: vec![ty.clone(), ty.clone()],
        returns: vec![Ty::I32],
        is_vararg: false,
    });
    let mut f = F::new(FuncId::new(0), name, ft, BlockId::new(0));
    f.blocks = vec![B {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), ty.clone()), (ValueId::new(1), ty.clone())],
        body: vec![
            InstrNode::new(Inst::Overflow {
                op,
                ty: ty.clone(),
                lhs: ValueId::new(0),
                rhs: ValueId::new(1),
            })
            .with_results([ValueId::new(2), ValueId::new(3)]),
            InstrNode::new(Inst::Cast {
                op: CastOp::ZExt,
                src_ty: Ty::Bool,
                dst_ty: Ty::I32,
                operand: ValueId::new(3),
            })
            .with_result(ValueId::new(4)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(4)],
            }),
        ],
    }];
    m.add_function(f);
    m
}

/// `fn _clamp(x, lo, hi) { max(lo, min(x, hi)) }` — nested selects (CSEL chain).
fn build_clamp(name: &str) -> M {
    let mut m = M::new("clamp");
    let ft = m.add_func_type(FuncTy {
        params: vec![Ty::I64, Ty::I64, Ty::I64],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let mut f = F::new(FuncId::new(0), name, ft, BlockId::new(0));
    let x = ValueId::new(0);
    let lo = ValueId::new(1);
    let hi = ValueId::new(2);
    f.blocks = vec![B {
        id: BlockId::new(0),
        params: vec![(x, Ty::I64), (lo, Ty::I64), (hi, Ty::I64)],
        body: vec![
            // t = (x > hi) ? hi : x
            InstrNode::new(Inst::ICmp {
                op: ICmpOp::Sgt,
                ty: Ty::I64,
                lhs: x,
                rhs: hi,
            })
            .with_result(ValueId::new(10)),
            InstrNode::new(Inst::Select {
                ty: Ty::I64,
                cond: ValueId::new(10),
                then_val: hi,
                else_val: x,
            })
            .with_result(ValueId::new(11)),
            // r = (t < lo) ? lo : t
            InstrNode::new(Inst::ICmp {
                op: ICmpOp::Slt,
                ty: Ty::I64,
                lhs: ValueId::new(11),
                rhs: lo,
            })
            .with_result(ValueId::new(12)),
            InstrNode::new(Inst::Select {
                ty: Ty::I64,
                cond: ValueId::new(12),
                then_val: lo,
                else_val: ValueId::new(11),
            })
            .with_result(ValueId::new(13)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(13)],
            }),
        ],
    }];
    m.add_function(f);
    m
}

/// A dense contiguous switch `0..ncases` (each case returns `(i+1)*10`, default
/// 99). The AArch64 backend lowers this to an ADR/LDRSW/BR jump table with the
/// table baked into `__text`.
fn build_switch(name: &str, ncases: u32) -> M {
    let mut m = M::new("sw");
    let ft = m.add_func_type(FuncTy {
        params: vec![Ty::I32],
        returns: vec![Ty::I32],
        is_vararg: false,
    });
    let mut f = F::new(FuncId::new(0), name, ft, BlockId::new(0));
    let mut cases = vec![];
    let mut arms = vec![];
    for i in 0..ncases {
        cases.push(SwitchCase {
            value: Constant::Int(i as i128),
            target: BlockId::new(i + 1),
            args: vec![],
        });
        arms.push(B {
            id: BlockId::new(i + 1),
            params: vec![],
            body: vec![
                InstrNode::new(Inst::Const {
                    ty: Ty::I32,
                    value: Constant::Int((i as i128 + 1) * 10),
                })
                .with_result(ValueId::new(100 + i)),
                InstrNode::new(Inst::Return {
                    values: vec![ValueId::new(100 + i)],
                }),
            ],
        });
    }
    let deflt = BlockId::new(ncases + 1);
    arms.push(B {
        id: deflt,
        params: vec![],
        body: vec![
            InstrNode::new(Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(99),
            })
            .with_result(ValueId::new(9000)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(9000)],
            }),
        ],
    });
    let mut blocks = vec![B {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), Ty::I32)],
        body: vec![InstrNode::new(Inst::Switch {
            value: ValueId::new(0),
            default: deflt,
            default_args: vec![],
            cases,
            exhaustive_enum_unreachable: false,
        })],
    }];
    blocks.extend(arms);
    f.blocks = blocks;
    m.add_function(f);
    m
}

/// Two functions: `_sum10(a0..a9)` sums ten i64 args (two arrive on the stack),
/// and `_caller(n)` computes `_sum10(n, n+1, ..., n+9)` — so a single-register
/// top-level entry drives the stack-argument SETUP (caller stores) and the
/// callee's stack-argument LOADS.
fn build_stack_args(caller: &str, callee: &str) -> M {
    let mut m = M::new("stackargs");
    // callee: fn(i64 x10) -> i64
    let ft10 = m.add_func_type(FuncTy {
        params: vec![Ty::I64; 10],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let mut sum = F::new(FuncId::new(0), callee, ft10, BlockId::new(0));
    let mut body = vec![];
    // acc = a0; acc += a1; ... acc += a9
    body.push(
        InstrNode::new(Inst::BinOp {
            op: BinOp::Add,
            ty: Ty::I64,
            lhs: ValueId::new(0),
            rhs: ValueId::new(1),
        })
        .with_result(ValueId::new(100)),
    );
    for i in 2..10u32 {
        body.push(
            InstrNode::new(Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: ValueId::new(99 + i - 1),
                rhs: ValueId::new(i),
            })
            .with_result(ValueId::new(99 + i)),
        );
    }
    body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(108)],
    }));
    sum.blocks = vec![B {
        id: BlockId::new(0),
        params: (0..10u32).map(|i| (ValueId::new(i), Ty::I64)).collect(),
        body,
    }];

    // caller: fn(i64 n) -> i64 { _sum10(n, n+1, ..., n+9) }
    let ft1 = m.add_func_type(FuncTy {
        params: vec![Ty::I64],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let mut call = F::new(FuncId::new(1), caller, ft1, BlockId::new(0));
    let mut cbody = vec![];
    let mut call_args = vec![ValueId::new(0)];
    for k in 1..10i128 {
        cbody.push(
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(k),
            })
            .with_result(ValueId::new(200 + k as u32)),
        );
        cbody.push(
            InstrNode::new(Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: ValueId::new(0),
                rhs: ValueId::new(200 + k as u32),
            })
            .with_result(ValueId::new(300 + k as u32)),
        );
        call_args.push(ValueId::new(300 + k as u32));
    }
    cbody.push(
        InstrNode::new(Inst::Call {
            callee: FuncId::new(0),
            args: call_args,
        })
        .with_result(ValueId::new(400)),
    );
    cbody.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(400)],
    }));
    call.blocks = vec![B {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), Ty::I64)],
        body: cbody,
    }];
    m.add_function(sum);
    m.add_function(call);
    m
}

/// `_helper(a) = a*2`; `_spill(x)` defines five values, calls `_helper` in the
/// middle, and sums them all — the five must survive a caller-clobbering call.
fn build_spill_across_call(helper: &str, spill: &str) -> M {
    let mut m = M::new("spill");
    let ft = m.add_func_type(FuncTy {
        params: vec![Ty::I64],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let mut h = F::new(FuncId::new(0), helper, ft, BlockId::new(0));
    h.blocks = vec![B {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), Ty::I64)],
        body: vec![
            InstrNode::new(Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: ValueId::new(0),
                rhs: ValueId::new(0),
            })
            .with_result(ValueId::new(1)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(1)],
            }),
        ],
    }];

    let ft2 = m.add_func_type(FuncTy {
        params: vec![Ty::I64],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let mut s = F::new(FuncId::new(1), spill, ft2, BlockId::new(0));
    let mut body = vec![];
    // v_k = x + k, for k in 1..=5
    for k in 1..=5i128 {
        body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(k),
            })
            .with_result(ValueId::new(10 + k as u32)),
        );
        body.push(
            InstrNode::new(Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: ValueId::new(0),
                rhs: ValueId::new(10 + k as u32),
            })
            .with_result(ValueId::new(20 + k as u32)),
        );
    }
    // h = _helper(x)
    body.push(
        InstrNode::new(Inst::Call {
            callee: FuncId::new(0),
            args: vec![ValueId::new(0)],
        })
        .with_result(ValueId::new(30)),
    );
    // acc = v1+v2+v3+v4+v5+h
    body.push(
        InstrNode::new(Inst::BinOp {
            op: BinOp::Add,
            ty: Ty::I64,
            lhs: ValueId::new(21),
            rhs: ValueId::new(22),
        })
        .with_result(ValueId::new(40)),
    );
    body.push(
        InstrNode::new(Inst::BinOp {
            op: BinOp::Add,
            ty: Ty::I64,
            lhs: ValueId::new(40),
            rhs: ValueId::new(23),
        })
        .with_result(ValueId::new(41)),
    );
    body.push(
        InstrNode::new(Inst::BinOp {
            op: BinOp::Add,
            ty: Ty::I64,
            lhs: ValueId::new(41),
            rhs: ValueId::new(24),
        })
        .with_result(ValueId::new(42)),
    );
    body.push(
        InstrNode::new(Inst::BinOp {
            op: BinOp::Add,
            ty: Ty::I64,
            lhs: ValueId::new(42),
            rhs: ValueId::new(25),
        })
        .with_result(ValueId::new(43)),
    );
    body.push(
        InstrNode::new(Inst::BinOp {
            op: BinOp::Add,
            ty: Ty::I64,
            lhs: ValueId::new(43),
            rhs: ValueId::new(30),
        })
        .with_result(ValueId::new(44)),
    );
    body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(44)],
    }));
    s.blocks = vec![B {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), Ty::I64)],
        body,
    }];
    m.add_function(h);
    m.add_function(s);
    m
}

// ===========================================================================
// The sweep, grouped by zone. Each #[test] asserts zero mismatches.
// ===========================================================================

#[test]
fn sweep_arithmetic_logic_abs_max() {
    let mut s = Sweep::default();
    let add = corpus::build_add_module();
    s.scalar(
        &add,
        "_add_two",
        "__add_two",
        32,
        &[
            vec![3, 4],
            vec![-5, 9],
            vec![i32::MAX as i64, 1],
            vec![i32::MIN as i64, -1],
        ],
    );
    let max = corpus::build_max_module();
    s.scalar(
        &max,
        "_max_val",
        "__max_val",
        64,
        &[
            vec![3, 4],
            vec![9, -5],
            vec![-1, -2],
            vec![i64::MIN, i64::MAX],
        ],
    );
    let abs = corpus::build_abs_module();
    s.scalar(
        &abs,
        "_abs_val",
        "__abs_val",
        64,
        &[vec![5], vec![-5], vec![0], vec![i64::MIN], vec![-1]],
    );
    for (nm, op) in [
        ("_and", BinOp::And),
        ("_or", BinOp::Or),
        ("_xor", BinOp::Xor),
    ] {
        let m = build_bin(nm, Ty::I64, op);
        s.scalar(
            &m,
            nm,
            &format!("_{nm}"),
            64,
            &[
                vec![0xF0F0, 0x0FF0],
                vec![-1, 0x1234],
                vec![0, 0],
                vec![i64::MIN, -1],
            ],
        );
    }
    let sub = build_bin("_sub", Ty::I64, BinOp::Sub);
    s.scalar(
        &sub,
        "_sub",
        "__sub",
        64,
        &[vec![10, 3], vec![3, 10], vec![i64::MIN, 1]],
    );
    let mul = build_bin("_mul32", Ty::I32, BinOp::Mul);
    s.scalar(
        &mul,
        "_mul32",
        "__mul32",
        32,
        &[vec![6, 7], vec![-3, 5], vec![0x10000, 0x10000]],
    );
    let mul64 = build_bin("_mul64", Ty::I64, BinOp::Mul);
    s.scalar(
        &mul64,
        "_mul64",
        "__mul64",
        64,
        &[vec![6, 7], vec![-3, 5], vec![i64::MAX, 2]],
    );
    s.finish("arithmetic/logic/abs/max");
}

#[test]
fn sweep_div_rem() {
    let mut s = Sweep::default();
    let cases_i = vec![
        vec![20, 3],
        vec![-20, 3],
        vec![20, -3],
        vec![-20, -3],
        vec![i64::MIN, -1],
        vec![i64::MIN, 1],
        vec![7, 7],
        vec![0, 5],
    ];
    let cases_u: Vec<Vec<i64>> = vec![
        vec![20, 3],
        vec![255, 4],
        vec![0, 5],
        vec![u32::MAX as i64, 2],
    ];
    for (nm, ty, op, signed) in [
        ("_sdiv64", Ty::I64, BinOp::SDiv, true),
        ("_srem64", Ty::I64, BinOp::SRem, true),
        ("_sdiv32", Ty::I32, BinOp::SDiv, true),
        ("_srem32", Ty::I32, BinOp::SRem, true),
    ] {
        let m = build_bin(nm, ty.clone(), op);
        let rb = if ty == Ty::I64 { 64 } else { 32 };
        let _ = signed;
        s.scalar(&m, nm, &format!("_{nm}"), rb, &cases_i);
    }
    for (nm, ty, op) in [
        ("_udiv64", Ty::I64, BinOp::UDiv),
        ("_urem64", Ty::I64, BinOp::URem),
        ("_udiv32", Ty::I32, BinOp::UDiv),
        ("_urem32", Ty::I32, BinOp::URem),
    ] {
        let m = build_bin(nm, ty.clone(), op);
        let rb = if ty == Ty::I64 { 64 } else { 32 };
        s.scalar(&m, nm, &format!("_{nm}"), rb, &cases_u);
    }
    s.finish("div/rem");
}

#[test]
fn sweep_shifts() {
    let mut s = Sweep::default();
    // variable shifts (LSLV/LSRV/ASRV)
    let vcases = vec![
        vec![1, 0],
        vec![1, 63],
        vec![-1, 1],
        vec![i64::MIN, 4],
        vec![0x1234, 8],
        vec![-256, 3],
    ];
    for (nm, op) in [
        ("_shl", BinOp::Shl),
        ("_lshr", BinOp::LShr),
        ("_ashr", BinOp::AShr),
    ] {
        let m = build_bin(nm, Ty::I64, op);
        s.scalar(&m, nm, &format!("_{nm}"), 64, &vcases);
        let m32 = build_bin(&format!("{nm}32"), Ty::I32, op);
        s.scalar(
            &m32,
            &format!("{nm}32"),
            &format!("_{nm}32"),
            32,
            &[
                vec![1, 0],
                vec![1, 31],
                vec![-1, 1],
                vec![i32::MIN as i64, 4],
            ],
        );
    }
    // immediate shifts (UBFM/SBFM path)
    for (nm, op, amt) in [
        ("_shli", BinOp::Shl, 5),
        ("_lshri", BinOp::LShr, 5),
        ("_ashri", BinOp::AShr, 5),
        ("_ashri63", BinOp::AShr, 63),
    ] {
        let m = build_shift_imm(nm, Ty::I64, op, amt);
        s.scalar(
            &m,
            nm,
            &format!("_{nm}"),
            64,
            &[vec![-1], vec![0x1234_5678], vec![i64::MIN], vec![255]],
        );
    }
    s.finish("shifts");
}

#[test]
fn sweep_narrow_int() {
    let mut s = Sweep::default();
    let cases = vec![
        vec![0xFF, 0x01],
        vec![0x7F, 0x01],
        vec![0x80, 0x01],
        vec![0xFFFF, 0x0001],
        vec![0x1234, 0x00FF],
        vec![-1, -1],
        vec![100, 200],
    ];
    for (nm, ty, signed) in [
        ("_i8_add", Ty::I8, true),
        ("_u8_add", Ty::U8, false),
        ("_i16_add", Ty::I16, true),
        ("_u16_add", Ty::U16, false),
    ] {
        let m = build_narrow_bin(nm, ty.clone(), BinOp::Add, signed);
        s.scalar(&m, nm, &format!("_{nm}"), 32, &cases);
        let mm = build_narrow_bin(&format!("{nm}_mul"), ty.clone(), BinOp::Mul, signed);
        s.scalar(&mm, &format!("{nm}_mul"), &format!("_{nm}_mul"), 32, &cases);
        let ms = build_narrow_bin(&format!("{nm}_sub"), ty, BinOp::Sub, signed);
        s.scalar(&ms, &format!("{nm}_sub"), &format!("_{nm}_sub"), 32, &cases);
    }
    s.finish("narrow-int");
}

#[test]
fn sweep_overflow_checked() {
    let mut s = Sweep::default();
    for (nm, op) in [
        ("_ovf_add", OverflowOp::AddOverflow),
        ("_ovf_sub", OverflowOp::SubOverflow),
        ("_ovf_mul", OverflowOp::MulOverflow),
    ] {
        // u32 form
        let mu = build_overflow(&format!("{nm}_u32"), Ty::U32, op);
        s.scalar(
            &mu,
            &format!("{nm}_u32"),
            &format!("_{nm}_u32"),
            32,
            &[
                vec![u32::MAX as i64, 1],
                vec![10, 20],
                vec![0x1_0000, 0x1_0000],
                vec![u32::MAX as i64, u32::MAX as i64],
                vec![5, 3],
            ],
        );
        // i32 form
        let mi = build_overflow(&format!("{nm}_i32"), Ty::I32, op);
        s.scalar(
            &mi,
            &format!("{nm}_i32"),
            &format!("_{nm}_i32"),
            32,
            &[
                vec![i32::MAX as i64, 1],
                vec![i32::MIN as i64, -1],
                vec![10, 20],
                vec![i32::MIN as i64, 2],
                vec![100, 100],
            ],
        );
        // i8 narrow form
        let m8 = build_overflow(&format!("{nm}_i8"), Ty::I8, op);
        s.scalar(
            &m8,
            &format!("{nm}_i8"),
            &format!("_{nm}_i8"),
            32,
            &[
                vec![127, 1],
                vec![-128, -1],
                vec![10, 20],
                vec![64, 2],
                vec![-1, -1],
            ],
        );
    }
    s.finish("overflow-checked");
}

#[test]
fn sweep_select_cmov() {
    let mut s = Sweep::default();
    let clamp = build_clamp("_clamp");
    s.scalar(
        &clamp,
        "_clamp",
        "__clamp",
        64,
        &[
            vec![5, 0, 10],
            vec![-3, 0, 10],
            vec![50, 0, 10],
            vec![7, 7, 7],
            vec![i64::MIN, -5, 5],
        ],
    );
    // deep 7-select chain (long live-range predicate — the SAT keep/drop shape)
    let ds = corpus::build_deep_select_chain_module();
    s.scalar(
        &ds,
        "_deep_select_chain",
        "__deep_select_chain",
        32,
        &[
            vec![1, 2, 3, 4, 5, 6, 7],
            vec![0, 0, 0, 0, 0, 0, 0],
            vec![-1, 5, -3, 9, 0, 2, -8],
            vec![10, 10, 10, 10, 10, 10, 10],
        ],
    );
    s.finish("select/cmov");
}

#[test]
fn sweep_loops_control_flow() {
    let mut s = Sweep::default();
    let sum = corpus::build_sum_1_to_n_module();
    s.scalar(
        &sum,
        "_sum_1_to_n",
        "__sum_1_to_n",
        64,
        &[vec![0], vec![1], vec![10], vec![100], vec![-5]],
    );
    let fact = corpus::build_factorial_module();
    s.scalar(
        &fact,
        "_factorial",
        "__factorial",
        64,
        &[vec![0], vec![1], vec![5], vec![10], vec![20]],
    );
    let fib = corpus::build_fibonacci_module();
    s.scalar(
        &fib,
        "_fibonacci",
        "__fibonacci",
        64,
        &[vec![0], vec![1], vec![10], vec![20], vec![30]],
    );
    let ipow = corpus::build_ipow_module();
    s.scalar(
        &ipow,
        "_ipow",
        "__ipow",
        64,
        &[
            vec![2, 10],
            vec![3, 5],
            vec![5, 0],
            vec![10, 3],
            vec![-2, 5],
        ],
    );
    let gcd = corpus::build_gcd_module();
    s.scalar(
        &gcd,
        "_gcd",
        "__gcd",
        64,
        &[
            vec![48, 36],
            vec![17, 5],
            vec![100, 25],
            vec![0, 7],
            vec![81, 27],
        ],
    );
    let coll = corpus::build_collatz_steps_module();
    s.scalar(
        &coll,
        "_collatz_steps",
        "__collatz_steps",
        64,
        &[vec![1], vec![6], vec![7], vec![27], vec![97]],
    );
    s.finish("loops/control-flow");
}

#[test]
fn sweep_calls_recursion_spills() {
    let mut s = Sweep::default();
    let rec = corpus::build_recursive_fact_double_module();
    s.scalar(
        &rec,
        "_fact_double",
        "__fact_double",
        64,
        &[vec![1], vec![3], vec![5], vec![8], vec![10]],
    );
    // recursion also drives the helper directly
    s.scalar(
        &rec,
        "_fact_helper",
        "__fact_helper",
        64,
        &[vec![5, 1], vec![6, 1], vec![10, 1]],
    );
    let spill = build_spill_across_call("_helper", "_spill");
    s.scalar(
        &spill,
        "_spill",
        "__spill",
        64,
        &[vec![0], vec![10], vec![-4], vec![1000]],
    );
    let sa = build_stack_args("_caller", "_sum10");
    s.scalar(
        &sa,
        "_caller",
        "__caller",
        64,
        &[vec![0], vec![5], vec![-10], vec![100]],
    );
    // and the 10-arg callee directly (top-level entry needs 8 regs; args 9,10
    // would be stack — driven here only through the caller above)
    s.finish("calls/recursion/spills");
}

#[test]
fn sweep_switch_jump_table() {
    let mut s = Sweep::default();
    for ncases in [4u32, 8, 16] {
        let nm = format!("_sw{ncases}");
        let m = build_switch(&nm, ncases);
        // include in-range, boundary, and out-of-range (default) selectors
        let mut cases: Vec<Vec<i64>> = (0..ncases as i64).map(|i| vec![i]).collect();
        cases.push(vec![-1]);
        cases.push(vec![ncases as i64]);
        cases.push(vec![1000]);
        s.scalar(&m, &nm, &format!("_{nm}"), 32, &cases);
    }
    s.finish("switch/jump-table");
}

#[test]
fn sweep_i128() {
    let mut s = Sweep::default();
    let big: i128 = 0x0123_4567_89AB_CDEF_FEDC_BA98_7654_3210u128 as i128;
    let neg: i128 = -0x0000_0000_0000_0001_0000_0000_0000_0002i128;
    let cases = [
        (1i128, 2i128),
        (big, 7),
        (neg, 3),
        (i128::MAX, 1),
        (i128::MIN, -1),
        (big, neg),
        (0xFFFF_FFFF_FFFF_FFFF, 1),
        (-1, -1),
    ];
    for (nm, op) in [
        ("_i128_add", BinOp::Add),
        ("_i128_sub", BinOp::Sub),
        ("_i128_mul", BinOp::Mul),
        ("_i128_and", BinOp::And),
        ("_i128_or", BinOp::Or),
        ("_i128_xor", BinOp::Xor),
    ] {
        let m = corpus::build_i128_binop_module(nm, op);
        s.i128_binop(&m, nm, &format!("_{nm}"), &cases);
    }
    // i128 compares — all signed/unsigned predicates
    for (nm, op) in [
        ("_i128_slt", ICmpOp::Slt),
        ("_i128_sgt", ICmpOp::Sgt),
        ("_i128_sle", ICmpOp::Sle),
        ("_i128_sge", ICmpOp::Sge),
        ("_i128_ult", ICmpOp::Ult),
        ("_i128_ugt", ICmpOp::Ugt),
        ("_i128_eq", ICmpOp::Eq),
        ("_i128_ne", ICmpOp::Ne),
    ] {
        let m = corpus::build_i128_cmp_module(nm, op);
        s.i128_to_i64(&m, nm, &format!("_{nm}"), &cases);
    }
    // mulhi: i64×i64 high 64 bits of the 128-bit signed product
    let mh = corpus::build_i128_mulhi_i64_module("_mulhi");
    s.scalar(
        &mh,
        "_mulhi",
        "__mulhi",
        64,
        &[
            vec![1_000_000_000, 1_000_000_000],
            vec![-1_000_000_000, 1_000_000_000],
            vec![i64::MAX, i64::MAX],
            vec![i64::MIN, i64::MIN],
            vec![-1, -1],
        ],
    );
    s.finish("i128");
}

// ===========================================================================
// TEETH: prove the harness DETECTS a miscompile in each newly-modeled class,
// so a green sweep is a real signal and not a silent skip. Each corrupts the
// emitted machine code (located by DECODING, robust to register allocation)
// into a different-but-valid instruction and asserts the interpreter now
// disagrees with the oracle.
// ===========================================================================

use common::a64_interp::{A64Interp, extract_text, symbol_addrs, text_branch_relocs};
use trust_cg_lift::disasm::aarch64::{Instruction, decode};

/// Compile at O0, apply `patch` to the emitted `__text`, run `sym(regs)` and
/// return (x0, x1). `patch` returns false if its target instruction is absent.
fn run_patched(
    m: &M,
    sym: &str,
    regs: &[u64],
    patch: impl FnOnce(&mut [u8]) -> bool,
) -> (u64, u64) {
    let obj = compile(m, OptLevel::O0);
    let text = extract_text(&obj);
    let addrs = symbol_addrs(&obj);
    let entry = (*addrs.get(sym).expect("sym") - text.addr) as usize;
    let mut bytes = text.bytes;
    assert!(
        patch(&mut bytes),
        "teeth: target instruction not found to corrupt"
    );
    let mut it = A64Interp::new(bytes).with_branch_relocs(text_branch_relocs(&obj));
    for (i, &r) in regs.iter().enumerate() {
        it.set_x(i, r);
    }
    let x0 = it.run(entry).expect("corrupted body still decodes+runs");
    (x0, it.x[1])
}

/// Locate the first instruction word matching `pred` and rewrite it with
/// `mangle`; returns false if none matched. Located by decoding, so it is robust
/// to register allocation and instruction scheduling.
fn corrupt_first(
    bytes: &mut [u8],
    pred: impl Fn(&Instruction) -> bool,
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
fn teeth_detects_sdiv_to_udiv_miscompile() {
    // fn _sdiv(a,b) = a / b (signed). SDIV is DP2 opcode 0b000011; clearing the
    // opcode LSB (bit 10) turns it into UDIV (0b000010) — a signed→unsigned
    // division miscompile that only differs on negative operands.
    let m = build_bin("_sdiv", Ty::I64, BinOp::SDiv);
    let want = oracle(&m, "_sdiv", &[-20, 3]) as i64; // -6
    let regs = [(-20i64) as u64, 3];
    let (pristine, _) = run_patched(&m, "__sdiv", &regs, |_| true);
    assert_eq!(pristine as i64, want, "pristine SDIV must match the oracle");

    let (corrupt, _) = run_patched(&m, "__sdiv", &regs, |bytes| {
        corrupt_first(
            bytes,
            |ins| matches!(ins, Instruction::DataProcessing2Source(d) if d.opcode == 0b000011),
            |w| w & !(1u32 << 10), // SDIV -> UDIV
        )
    });
    assert_ne!(
        corrupt as i64, want,
        "TEETH: SDIV->UDIV corruption must change _sdiv(-20,3); harness has teeth on the DP2 div class"
    );
}

#[test]
fn teeth_detects_i128_umulh_to_smulh_miscompile() {
    // The i128 low×low product's HIGH half is UMULH (DP3 op31=0b110). Clearing
    // op31 bit 23 turns it into SMULH (0b010), corrupting the unsigned partial
    // product — a classic wide-multiply signedness miscompile.
    let m = corpus::build_i128_binop_module("_i128_mul", BinOp::Mul);
    // a.lo has its MSB set so UMULH and SMULH of the low limb diverge.
    let a: i128 = 0xFFFF_FFFF_FFFF_FFFFu128 as i128; // lo=0xFFFF.., hi=0
    let b: i128 = 3;
    let want = oracle(&m, "_i128_mul", &[a, b]) as u128;
    let regs = [a as u64, (a >> 64) as u64, b as u64, (b >> 64) as u64];

    let (pristine_lo, pristine_hi) = run_patched(&m, "__i128_mul", &regs, |_| true);
    assert_eq!(
        (pristine_lo as u128) | ((pristine_hi as u128) << 64),
        want,
        "pristine i128 mul must match the oracle"
    );

    let (lo, hi) = run_patched(&m, "__i128_mul", &regs, |bytes| {
        corrupt_first(
            bytes,
            |ins| matches!(ins, Instruction::DataProcessing3Source(d) if d.op31 == 0b110),
            |w| w & !(1u32 << 23), // UMULH -> SMULH
        )
    });
    assert_ne!(
        (lo as u128) | ((hi as u128) << 64),
        want,
        "TEETH: UMULH->SMULH corruption must change the i128 product; harness has teeth on the DP3 high-multiply class"
    );
}

/// Locate the baked jump table (the maximal run of words that do not decode as
/// instructions, which follows the case blocks) and return its `__text` offset.
fn find_jump_table(bytes: &[u8]) -> Option<usize> {
    let mut table_start = None;
    let mut i = 0;
    while i + 4 <= bytes.len() {
        let w = u32::from_le_bytes([bytes[i], bytes[i + 1], bytes[i + 2], bytes[i + 3]]);
        if decode(w).is_err() {
            if table_start.is_none() {
                table_start = Some(i);
            }
        } else {
            table_start = None;
        }
        i += 4;
    }
    table_start
}

#[test]
fn teeth_detects_jump_table_entry_miscompile() {
    // The dense switch lowers to an ADR/LDRSW/BR jump table with the table baked
    // into __text. Perturbing one table entry must send that case to the wrong
    // block — proving the harness actually reads the table and follows the
    // indirect BR (the switch/BST bug zone).
    let m = build_switch("_sw8", 8);
    let want = oracle(&m, "_sw8", &[3]); // case 3 -> 40

    let (pristine, _) = run_patched(&m, "__sw8", &[3], |_| true);
    assert_eq!(
        pristine as u32 as i32 as i128, want,
        "pristine switch case 3 must match the oracle"
    );

    // Add 4 to entry[3]'s signed offset so case 3 targets a different block.
    let (corrupt, _) = run_patched(&m, "__sw8", &[3], |bytes| {
        let Some(ts) = find_jump_table(bytes) else {
            return false;
        };
        let e3 = ts + 3 * 4;
        let orig = i32::from_le_bytes([bytes[e3], bytes[e3 + 1], bytes[e3 + 2], bytes[e3 + 3]]);
        bytes[e3..e3 + 4].copy_from_slice(&(orig + 4).to_le_bytes());
        true
    });
    assert_ne!(
        corrupt as u32 as i32 as i128, want,
        "TEETH: perturbing jump-table entry[3] must change case 3; harness has teeth on the switch jump-table path"
    );
}
