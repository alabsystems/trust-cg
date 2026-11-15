// trust-cg-lower/adapter_i128_mulo_tests.rs - the I128 checked multiply's
// per-target expansions (OD-224), run on a width-scaled LIR interpreter.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! The adapter expands `Inst::Overflow { MulOverflow, U128 | I128 }` per
//! target (`translate_overflow`): the division-free limb check on x86-64
//! (OD-224), the guarded division of the low product everywhere else. These
//! tests translate a real trust-ir function for each target and run the
//! adapter's ACTUAL output on a small LIR interpreter that knows only the
//! opcodes these expansions use (any other opcode panics by name).
//!
//! **Scaled analogs.** The interpreter can run an expansion at a smaller
//! width: `I128` becomes `W` bits, `I64` becomes `H = W / 2` bits, the shift
//! constant `Iconst{I128, 64}` becomes `H`, and a 128-bit constant is scaled
//! limb by limb (0, 1, all ones, the sign bit; anything else refuses). At `W =
//! 8` every pair is checked (65,536 pairs), at `W = 16` too (2^32 pairs, an
//! `#[ignore]`d test, about minutes on two threads). That is exhaustive
//! evidence for THOSE widths only: it says nothing about the 128-bit circuit by
//! itself. At `W = 128` the same interpreter runs the real circuit on a
//! directed edge battery and random pairs against Rust's native
//! `checked_mul`: statistical, regression-only evidence.
//!
//! **Negative controls.** The design's mutants (`~/tcg-scratch/i128-mulo-design`
//! §3.4, its `lir_model.py`) are applied to the adapter's output; each
//! non-equivalent mutant must be refuted at `W = 8` with exactly the mismatch
//! count the design's independent Python model measured, and at `W = 128` at
//! the design's replayed counterexample.

use super::*;
use trust_ir::FuncTy;

/// Which of the two I128 checked multiplies.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Sign {
    Unsigned,
    Signed,
}

/// `fn mulo(a: T, b: T) -> bool { a.overflowing_mul(b).1 }`, T = u128 / i128.
fn checked_mul_module(sign: Sign) -> TrustIrModule {
    let ty = match sign {
        Sign::Unsigned => Ty::U128,
        Sign::Signed => Ty::I128,
    };
    let mut module = TrustIrModule::new("i128_mulo");
    let sig = module
        .add_func_type(FuncTy {
            params: vec![ty.clone(), ty.clone()],
            returns: vec![Ty::Bool],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut func = TrustIrFunction::new(FuncId::new(0), "mulo", sig, BlockId::new(0));
    let mut block = TrustIrBlock::new(BlockId::new(0));
    block.params = vec![(ValueId::new(0), ty.clone()), (ValueId::new(1), ty.clone())];
    block.body.push(
        InstrNode::new(Inst::Overflow {
            op: OverflowOp::MulOverflow,
            ty,
            lhs: ValueId::new(0),
            rhs: ValueId::new(1),
        })
        .with_results(vec![ValueId::new(2), ValueId::new(3)]),
    );
    block.body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(3)],
    }));
    func.blocks.push(block);
    module.functions.push(func);
    module
}

/// The LIR the adapter translates [`checked_mul_module`] to for `arch`.
fn translated(sign: Sign, arch: GuardCarrierArch) -> Function {
    let license =
        crate::CodegenLicensePolicy::default().with_unlicensed(crate::UnlicensedBodyPolicy::Permit);
    crate::translate_module_for_arch_with_tls_with_license(
        &checked_mul_module(sign),
        arch,
        TlsDialect::default(),
        &license,
    )
    .unwrap_or_else(|error| panic!("{sign:?} {arch:?}: fixture translates: {error:?}"))
    .into_iter()
    .map(|(function, _)| function)
    .find(|function| function.name == "mulo")
    .expect("the translated module has `mulo`")
}

/// The entry block of [`translated`]: its two `I128` parameters and its
/// instructions (the function is one block).
fn entry(sign: Sign, arch: GuardCarrierArch) -> (Value, Value, Vec<Instruction>) {
    let function = translated(sign, arch);
    assert_eq!(function.blocks.len(), 1, "{sign:?} {arch:?}: one block");
    let block = &function.blocks[&function.entry_block];
    let params: Vec<Value> = block
        .params
        .iter()
        .map(|(value, ty)| {
            assert_eq!(*ty, Type::I128, "{sign:?} {arch:?}: I128 parameters");
            *value
        })
        .collect();
    let [a, b] = params[..] else {
        panic!("{sign:?} {arch:?}: two parameters, got {params:?}")
    };
    (a, b, block.instructions.clone())
}

// ---------------------------------------------------------------------------
// The interpreter
// ---------------------------------------------------------------------------

fn mask(bits: u32) -> u128 {
    if bits >= 128 {
        u128::MAX
    } else {
        (1u128 << bits) - 1
    }
}

/// `x` (a `bits`-bit pattern) read as a two's-complement integer.
fn signed(x: u128, bits: u32) -> i128 {
    if bits >= 128 {
        x as i128
    } else if (x >> (bits - 1)) & 1 == 1 {
        x as i128 - (1i128 << bits)
    } else {
        x as i128
    }
}

/// One interpreted operation; operands are slot indices.
#[derive(Debug, Clone)]
enum Op {
    Const(u128),
    Copy(usize),
    Imul(usize, usize),
    Iadd(usize, usize),
    Isub(usize, usize),
    Ineg(usize),
    Ushr(usize, usize),
    Sshr(usize, usize),
    /// Truncate or zero-extend: the value masked to the result width.
    Resize(usize),
    Icmp(IntCC, usize, usize),
    And(usize, usize),
    Or(usize, usize),
    Xor(usize, usize),
    /// `[c, then, else]` of `Select{cond: NotEqual}`.
    Select(usize, usize, usize),
    /// `[low, overflow]` of `CheckedUmul` / `CheckedSmul` at the operand width.
    CheckedMul {
        signed: bool,
        x: usize,
        y: usize,
    },
    Udiv(usize, usize),
    Sdiv(usize, usize),
}

/// One step: `op` writes `dst` (and `dst + 1`, the overflow, for a checked
/// multiply).
#[derive(Debug, Clone)]
struct Step {
    op: Op,
    dst: usize,
}

/// A compiled expansion at the scaled widths `(w, h)`.
#[derive(Debug, Clone)]
struct Program {
    w: u32,
    steps: Vec<Step>,
    widths: Vec<u32>,
    ret: usize,
}

impl Program {
    /// Compile `instrs` (one block: parameters `a`, `b` in slots 0 and 1, a
    /// final `Return` of one value) at `I128 = w` bits.
    fn compile(a: Value, b: Value, instrs: &[Instruction], w: u32) -> Self {
        assert!(w % 2 == 0 && (4..=128).contains(&w));
        let h = w / 2;
        let width_of = |ty: &Type| -> u32 {
            match ty {
                Type::I128 => w,
                Type::I64 => h,
                Type::B1 => 1,
                Type::I8 => 8,
                other => panic!("type {other:?} outside the interpreter's set"),
            }
        };
        // A 64-bit limb constant at H bits: exact at full width, else only the
        // patterns whose meaning survives scaling.
        let limb = |l: i64| -> u128 {
            if h == 64 {
                l as u64 as u128
            } else {
                match l {
                    0 => 0,
                    1 => 1,
                    -1 => mask(h),
                    i64::MIN => 1 << (h - 1),
                    other => panic!("limb constant {other:#x} does not scale to {h} bits"),
                }
            }
        };
        let mut slots: HashMap<Value, usize> = HashMap::from([(a, 0), (b, 1)]);
        let mut widths = vec![w, w];
        let mut steps = Vec::new();
        let mut ret = None;
        for inst in instrs {
            let arg = |i: usize| -> usize {
                *slots
                    .get(&inst.args[i])
                    .unwrap_or_else(|| panic!("{inst:?}: argument {i} undefined"))
            };
            let width_arg = |widths: &[u32], i: usize| widths[arg(i)];
            let (op, width) = match &inst.opcode {
                Opcode::Return => {
                    assert_eq!(inst.args.len(), 1, "{inst:?}");
                    ret = Some(arg(0));
                    continue;
                }
                Opcode::Iconst { ty, imm } => {
                    let bits = width_of(ty);
                    let value = match (ty, *imm) {
                        // The half-width shift amount of an I128 limb split.
                        (Type::I128, 64) => u128::from(h),
                        // The sign-bit shift amount of an I64 limb.
                        (Type::I64, 63) => u128::from(h - 1),
                        (_, 0) => 0,
                        (_, 1) => 1,
                        (_, imm) if w == 128 => (imm as i128 as u128) & mask(bits),
                        (ty, imm) => panic!("Iconst {ty:?} {imm} does not scale to W={w}"),
                    };
                    (Op::Const(value), bits)
                }
                Opcode::Iconst128 { lo, hi } => (Op::Const(limb(*lo) | (limb(*hi) << h)), w),
                Opcode::Copy => (Op::Copy(arg(0)), width_arg(&widths, 0)),
                Opcode::Imul => (Op::Imul(arg(0), arg(1)), width_arg(&widths, 0)),
                Opcode::Iadd => (Op::Iadd(arg(0), arg(1)), width_arg(&widths, 0)),
                Opcode::Isub => (Op::Isub(arg(0), arg(1)), width_arg(&widths, 0)),
                Opcode::Sshr => (Op::Sshr(arg(0), arg(1)), width_arg(&widths, 0)),
                Opcode::Ineg => (Op::Ineg(arg(0)), width_arg(&widths, 0)),
                Opcode::Ushr => (Op::Ushr(arg(0), arg(1)), width_arg(&widths, 0)),
                Opcode::Trunc { to_ty } | Opcode::Uextend { to_ty, .. } => {
                    (Op::Resize(arg(0)), width_of(to_ty))
                }
                Opcode::Icmp { cond } => (Op::Icmp(*cond, arg(0), arg(1)), 1),
                Opcode::Band => (Op::And(arg(0), arg(1)), width_arg(&widths, 0)),
                Opcode::Bor => (Op::Or(arg(0), arg(1)), width_arg(&widths, 0)),
                Opcode::Bxor => (Op::Xor(arg(0), arg(1)), width_arg(&widths, 0)),
                Opcode::Select {
                    cond: IntCC::NotEqual,
                } => (Op::Select(arg(0), arg(1), arg(2)), width_arg(&widths, 1)),
                Opcode::CheckedUmul | Opcode::CheckedSmul => (
                    Op::CheckedMul {
                        signed: matches!(inst.opcode, Opcode::CheckedSmul),
                        x: arg(0),
                        y: arg(1),
                    },
                    width_arg(&widths, 0),
                ),
                Opcode::Udiv => (Op::Udiv(arg(0), arg(1)), width_arg(&widths, 0)),
                Opcode::Sdiv => (Op::Sdiv(arg(0), arg(1)), width_arg(&widths, 0)),
                other => panic!("opcode {other:?} is outside the interpreter's set"),
            };
            let dst = widths.len();
            widths.push(width);
            if matches!(op, Op::CheckedMul { .. }) {
                assert_eq!(inst.results.len(), 2, "{inst:?}");
                widths.push(1);
                slots.insert(inst.results[0], dst);
                slots.insert(inst.results[1], dst + 1);
            } else {
                assert_eq!(inst.results.len(), 1, "{inst:?}");
                slots.insert(inst.results[0], dst);
            }
            steps.push(Step { op, dst });
        }
        Self {
            w,
            steps,
            widths,
            ret: ret.expect("the block returns"),
        }
    }

    /// The returned value for one pair `(a, b)` of `w`-bit patterns.
    fn run(&self, a: u128, b: u128) -> u128 {
        let mut v = vec![0u128; self.widths.len()];
        v[0] = a & mask(self.w);
        v[1] = b & mask(self.w);
        for step in &self.steps {
            let bits = self.widths[step.dst];
            let m = mask(bits);
            let out = match step.op {
                Op::Const(c) => c,
                Op::Copy(x) | Op::Resize(x) => v[x] & m,
                Op::Imul(x, y) => v[x].wrapping_mul(v[y]) & m,
                Op::Iadd(x, y) => v[x].wrapping_add(v[y]) & m,
                Op::Isub(x, y) => v[x].wrapping_sub(v[y]) & m,
                Op::Ineg(x) => v[x].wrapping_neg() & m,
                Op::Ushr(x, y) => {
                    assert!(v[y] < u128::from(bits), "shift by {} at {bits} bits", v[y]);
                    v[x] >> v[y]
                }
                Op::Sshr(x, y) => {
                    assert!(v[y] < u128::from(bits), "shift by {} at {bits} bits", v[y]);
                    ((signed(v[x], bits) >> v[y]) as u128) & m
                }
                Op::Icmp(cond, x, y) => {
                    let wx = self.widths[x];
                    let (ux, uy) = (v[x], v[y]);
                    let (sx, sy) = (signed(ux, wx), signed(uy, wx));
                    u128::from(match cond {
                        IntCC::Equal => ux == uy,
                        IntCC::NotEqual => ux != uy,
                        IntCC::UnsignedLessThan => ux < uy,
                        IntCC::UnsignedLessThanOrEqual => ux <= uy,
                        IntCC::UnsignedGreaterThan => ux > uy,
                        IntCC::UnsignedGreaterThanOrEqual => ux >= uy,
                        IntCC::SignedLessThan => sx < sy,
                        IntCC::SignedLessThanOrEqual => sx <= sy,
                        IntCC::SignedGreaterThan => sx > sy,
                        IntCC::SignedGreaterThanOrEqual => sx >= sy,
                    })
                }
                Op::And(x, y) => v[x] & v[y],
                Op::Or(x, y) => v[x] | v[y],
                Op::Xor(x, y) => v[x] ^ v[y],
                Op::Select(c, t, e) => {
                    if v[c] != 0 {
                        v[t]
                    } else {
                        v[e]
                    }
                }
                Op::CheckedMul { signed: s, x, y } => {
                    assert!(bits <= 64, "checked multiply at {bits} bits");
                    let (low, overflow) = if s {
                        let p = signed(v[x], bits) * signed(v[y], bits);
                        let limit = 1i128 << (bits - 1);
                        ((p as u128) & m, !(-limit..limit).contains(&p))
                    } else {
                        let p = v[x] * v[y];
                        (p & m, (p >> bits) != 0)
                    };
                    v[step.dst + 1] = u128::from(overflow);
                    low
                }
                Op::Udiv(x, y) => {
                    assert_ne!(v[y], 0, "Udiv by zero reached: trust-ir UB");
                    v[x] / v[y]
                }
                Op::Sdiv(x, y) => {
                    let (sx, sy) = (signed(v[x], bits), signed(v[y], bits));
                    let min = if bits >= 128 {
                        i128::MIN
                    } else {
                        -(1i128 << (bits - 1))
                    };
                    assert!(
                        sy != 0 && !(sx == min && sy == -1),
                        "Sdiv off trust-ir's domain reached"
                    );
                    (sx.wrapping_div(sy) as u128) & m
                }
            };
            v[step.dst] = out;
        }
        v[self.ret]
    }

    /// The returned value for `a` and every `b` in `0..2^w`, lane by lane
    /// (`w <= 16`): the same semantics as [`Self::run`], batched so a `W = 16`
    /// sweep is affordable. `scratch` holds one lane vector per slot.
    fn run_row(&self, a: u32, scratch: &mut Vec<Vec<u32>>) -> Vec<u32> {
        assert!(self.w <= 16, "the batched evaluator holds products in u32");
        let n = 1usize << self.w;
        scratch.resize_with(self.widths.len(), Vec::new);
        for lane in scratch.iter_mut() {
            lane.resize(n, 0);
        }
        scratch[0].iter_mut().for_each(|x| *x = a);
        for (i, x) in scratch[1].iter_mut().enumerate() {
            *x = i as u32;
        }
        for step in &self.steps {
            let bits = self.widths[step.dst];
            let m = mask(bits) as u32;
            let mut out = std::mem::take(&mut scratch[step.dst]);
            match step.op {
                Op::Const(c) => out.iter_mut().for_each(|o| *o = c as u32),
                Op::Copy(x) | Op::Resize(x) => {
                    for (o, &x) in out.iter_mut().zip(&scratch[x]) {
                        *o = x & m;
                    }
                }
                Op::Imul(x, y) => {
                    for ((o, &x), &y) in out.iter_mut().zip(&scratch[x]).zip(&scratch[y]) {
                        *o = x.wrapping_mul(y) & m;
                    }
                }
                Op::Iadd(x, y) => {
                    for ((o, &x), &y) in out.iter_mut().zip(&scratch[x]).zip(&scratch[y]) {
                        *o = x.wrapping_add(y) & m;
                    }
                }
                Op::Isub(x, y) => {
                    for ((o, &x), &y) in out.iter_mut().zip(&scratch[x]).zip(&scratch[y]) {
                        *o = x.wrapping_sub(y) & m;
                    }
                }
                Op::Ineg(x) => {
                    for (o, &x) in out.iter_mut().zip(&scratch[x]) {
                        *o = x.wrapping_neg() & m;
                    }
                }
                Op::Sshr(x, y) => {
                    for ((o, &x), &y) in out.iter_mut().zip(&scratch[x]).zip(&scratch[y]) {
                        assert!(y < bits, "shift by {y} at {bits} bits");
                        *o = ((signed(u128::from(x), bits) >> y) as u32) & m;
                    }
                }
                Op::Ushr(x, y) => {
                    for ((o, &x), &y) in out.iter_mut().zip(&scratch[x]).zip(&scratch[y]) {
                        assert!(y < bits, "shift by {y} at {bits} bits");
                        *o = x >> y;
                    }
                }
                Op::Icmp(cond, x, y) => {
                    let wx = self.widths[x];
                    let sign = |v: u32| signed(u128::from(v), wx);
                    for ((o, &x), &y) in out.iter_mut().zip(&scratch[x]).zip(&scratch[y]) {
                        *o = u32::from(match cond {
                            IntCC::Equal => x == y,
                            IntCC::NotEqual => x != y,
                            IntCC::UnsignedLessThan => x < y,
                            IntCC::UnsignedLessThanOrEqual => x <= y,
                            IntCC::UnsignedGreaterThan => x > y,
                            IntCC::UnsignedGreaterThanOrEqual => x >= y,
                            IntCC::SignedLessThan => sign(x) < sign(y),
                            IntCC::SignedLessThanOrEqual => sign(x) <= sign(y),
                            IntCC::SignedGreaterThan => sign(x) > sign(y),
                            IntCC::SignedGreaterThanOrEqual => sign(x) >= sign(y),
                        });
                    }
                }
                Op::And(x, y) => {
                    for ((o, &x), &y) in out.iter_mut().zip(&scratch[x]).zip(&scratch[y]) {
                        *o = x & y;
                    }
                }
                Op::Or(x, y) => {
                    for ((o, &x), &y) in out.iter_mut().zip(&scratch[x]).zip(&scratch[y]) {
                        *o = x | y;
                    }
                }
                Op::Xor(x, y) => {
                    for ((o, &x), &y) in out.iter_mut().zip(&scratch[x]).zip(&scratch[y]) {
                        *o = x ^ y;
                    }
                }
                Op::Select(c, t, e) => {
                    for (i, o) in out.iter_mut().enumerate() {
                        *o = if scratch[c][i] != 0 {
                            scratch[t][i]
                        } else {
                            scratch[e][i]
                        };
                    }
                }
                Op::CheckedMul { signed: s, x, y } => {
                    let mut flags = std::mem::take(&mut scratch[step.dst + 1]);
                    let limit = 1i64 << (bits - 1);
                    for (i, (o, f)) in out.iter_mut().zip(flags.iter_mut()).enumerate() {
                        let (x, y) = (scratch[x][i], scratch[y][i]);
                        if s {
                            let p = signed(u128::from(x), bits) as i64
                                * signed(u128::from(y), bits) as i64;
                            *o = (p as u32) & m;
                            *f = u32::from(!(-limit..limit).contains(&p));
                        } else {
                            let p = x * y;
                            *o = p & m;
                            *f = u32::from((p >> bits) != 0);
                        }
                    }
                    scratch[step.dst + 1] = flags;
                }
                Op::Udiv(..) | Op::Sdiv(..) => {
                    panic!("the batched evaluator runs the division-free expansions only")
                }
            }
            scratch[step.dst] = out;
        }
        scratch[self.ret].clone()
    }
}

/// trust-ir's flag: the exact product of two `w`-bit operands does not fit.
fn spec(sign: Sign, a: u128, b: u128, w: u32) -> bool {
    match sign {
        Sign::Unsigned => {
            if w == 128 {
                a.checked_mul(b).is_none()
            } else {
                a * b > mask(w)
            }
        }
        Sign::Signed => {
            if w == 128 {
                (a as i128).checked_mul(b as i128).is_none()
            } else {
                let p = signed(a, w) * signed(b, w);
                let limit = 1i128 << (w - 1);
                !(-limit..limit).contains(&p)
            }
        }
    }
}

/// Mismatches of `program` (judged as `sign`) over every pair at `w <= 8`.
fn mismatches_all_pairs(program: &Program, sign: Sign) -> usize {
    let n = 1u128 << program.w;
    let mut bad = 0;
    for a in 0..n {
        for b in 0..n {
            if (program.run(a, b) != 0) != spec(sign, a, b, program.w) {
                bad += 1;
            }
        }
    }
    bad
}

// ---------------------------------------------------------------------------
// Mutants of the adapter's output (the design's §3.4)
// ---------------------------------------------------------------------------

/// The index of the `n`-th (0-based) instruction matching `pick`.
fn nth(instrs: &[Instruction], n: usize, pick: impl Fn(&Opcode) -> bool) -> usize {
    instrs
        .iter()
        .enumerate()
        .filter(|(_, inst)| pick(&inst.opcode))
        .map(|(i, _)| i)
        .nth(n)
        .unwrap_or_else(|| panic!("no instruction #{n} of the requested kind"))
}

fn is_bor(op: &Opcode) -> bool {
    matches!(op, Opcode::Bor)
}

fn is_band(op: &Opcode) -> bool {
    matches!(op, Opcode::Band)
}

/// The index of the last instruction matching `pick`.
fn last(instrs: &[Instruction], pick: impl Fn(&Opcode) -> bool) -> usize {
    instrs
        .iter()
        .rposition(|inst| pick(&inst.opcode))
        .expect("an instruction of the requested kind")
}

/// The single result of the one instruction with `opcode` and `args`.
fn result_of(instrs: &[Instruction], opcode: &Opcode, args: &[Value]) -> Value {
    let hits: Vec<Value> = instrs
        .iter()
        .filter(|inst| &inst.opcode == opcode && inst.args == args)
        .map(|inst| inst.results[0])
        .collect();
    let [only] = hits[..] else {
        panic!("{opcode:?} {args:?}: {} matches", hits.len())
    };
    only
}

/// The limbs `[lo, hi]` of the `I128` value `x`, as the expansion splits it
/// (`Trunc x`, `Trunc (Ushr x k64)`).
fn limbs_in(instrs: &[Instruction], x: Value) -> [Value; 2] {
    let trunc = Opcode::Trunc { to_ty: Type::I64 };
    let shifted = instrs
        .iter()
        .find(|inst| inst.opcode == Opcode::Ushr && inst.args[0] == x)
        .expect("the limb split's shift")
        .results[0];
    [
        result_of(instrs, &trunc, &[x]),
        result_of(instrs, &trunc, &[shifted]),
    ]
}

/// `instrs` with every read of a key of `map` reading its value instead.
fn substitute(instrs: &mut [Instruction], map: &HashMap<Value, Value>) {
    for inst in instrs {
        for arg in &mut inst.args {
            if let Some(&to) = map.get(arg) {
                *arg = to;
            }
        }
    }
}

/// `instrs` with the named mutant applied. The unsigned mutants address the
/// unsigned expansion's core (its three `Bor`s, its one unsigned compare, its
/// `CheckedUmul`s and its `Iadd`); the signed ones the signed expansion's
/// sign check (its last `Band` and `Bor`), its product-sign mask (the `Bxor`
/// of the two sign masks) and the core's operands.
fn mutate(instrs: &[Instruction], mutant: &str) -> Vec<Instruction> {
    /// Instruction `n` of kind `pick` reads its argument `from` in place of `to`.
    fn set_arg(m: &mut [Instruction], pick: fn(&Opcode) -> bool, n: usize, to: usize, from: usize) {
        let i = nth(m, n, pick);
        m[i].args[to] = m[i].args[from];
    }
    /// Every instruction of kind `pick` becomes `to`.
    fn retarget(m: &mut [Instruction], pick: fn(&Opcode) -> bool, to: Opcode) {
        let hits: Vec<usize> = (0..m.len()).filter(|&i| pick(&m[i].opcode)).collect();
        assert!(!hits.is_empty(), "nothing to retarget to {to:?}");
        for i in hits {
            m[i].opcode = to.clone();
        }
    }
    fn is_carry_compare(op: &Opcode) -> bool {
        matches!(
            op,
            Opcode::Icmp {
                cond: IntCC::UnsignedLessThan
            }
        )
    }
    let mut m = instrs.to_vec();
    match mutant {
        // core: f1 = o1 | o2; f2 = f1 | c; dst = f2 | both
        "drop_o1" => set_arg(&mut m, is_bor, 0, 0, 1),
        "drop_o2" => set_arg(&mut m, is_bor, 0, 1, 0),
        "drop_carry" => set_arg(&mut m, is_bor, 1, 1, 0),
        "drop_both" => set_arg(&mut m, is_bor, 2, 1, 0),
        "carry_signed" => retarget(
            &mut m,
            is_carry_compare,
            Opcode::Icmp {
                cond: IntCC::SignedLessThan,
            },
        ),
        "carry_ule" => retarget(
            &mut m,
            is_carry_compare,
            Opcode::Icmp {
                cond: IntCC::UnsignedLessThanOrEqual,
            },
        ),
        "smul_cross" => retarget(
            &mut m,
            |op| matches!(op, Opcode::CheckedUmul),
            Opcode::CheckedSmul,
        ),
        "t_or" => retarget(&mut m, |op| matches!(op, Opcode::Iadd), Opcode::Bor),
        // signed: bad = sign & r_nz (the last Band); flag = ou | bad (the last Bor)
        "no_zero_guard" => {
            let i = last(&m, is_band);
            m[i].args[1] = m[i].args[0];
        }
        "no_sign_check" => {
            let i = last(&m, is_bor);
            m[i].args[1] = m[i].args[0];
        }
        "no_ou" => {
            let i = last(&m, is_bor);
            m[i].args[0] = m[i].args[1];
        }
        // signed: mn = ma ^ mb, the Bxor of two Sshr results, as an or
        "neg_or" => {
            let shifted: Vec<Value> = m
                .iter()
                .filter(|inst| inst.opcode == Opcode::Sshr)
                .map(|inst| inst.results[0])
                .collect();
            let i = m
                .iter()
                .position(|inst| {
                    inst.opcode == Opcode::Bxor && inst.args.iter().all(|a| shifted.contains(a))
                })
                .expect("the product-sign mask");
            m[i].opcode = Opcode::Bor;
        }
        // signed: the core reads the wrapped product's high limb (pu_eq_r),
        // or every operand raw (unsigned_core_raw)
        "pu_eq_r" | "unsigned_core_raw" => {
            let imul = &m[0];
            assert_eq!(imul.opcode, Opcode::Imul);
            let (a, b, r) = (imul.args[0], imul.args[1], imul.results[0]);
            let (a_limbs, b_limbs, r_limbs) = (limbs_in(&m, a), limbs_in(&m, b), limbs_in(&m, r));
            let first = nth(&m, 0, |op| matches!(op, Opcode::CheckedUmul));
            let second = nth(&m, 1, |op| matches!(op, Opcode::CheckedUmul));
            let carry = nth(&m, 0, is_carry_compare);
            let mut map = HashMap::from([(m[carry].args[0], r_limbs[1])]);
            if mutant == "unsigned_core_raw" {
                // core(x, y): CheckedUmul x1, y0 then CheckedUmul x0, y1
                map.insert(m[first].args[0], a_limbs[1]);
                map.insert(m[first].args[1], b_limbs[0]);
                map.insert(m[second].args[0], a_limbs[0]);
                map.insert(m[second].args[1], b_limbs[1]);
            }
            substitute(&mut m[first..], &map);
        }
        other => panic!("unknown mutant {other}"),
    }
    m
}

/// The design's unsigned mutants and their `W = 8` mismatch counts
/// (`sweep_w8.json`); `t_or` is equivalent (0).
const U_MUTANTS: [(&str, usize); 8] = [
    ("drop_carry", 208),
    ("drop_both", 3521),
    ("drop_o1", 2324),
    ("drop_o2", 2324),
    ("carry_signed", 284),
    ("carry_ule", 1312),
    ("smul_cross", 1292),
    ("t_or", 0),
];

/// The design's signed mutants and their `W = 8` mismatch counts.
const S_MUTANTS: [(&str, usize); 6] = [
    ("no_zero_guard", 256),
    ("no_sign_check", 2246),
    ("no_ou", 30815),
    ("neg_or", 713),
    ("pu_eq_r", 184),
    ("unsigned_core_raw", 1669),
];

/// The design's replayed 128-bit counterexamples (`z3_mutants_w128.jsonl`,
/// `w128_witnesses.json`): `(mutant, a, b)` at which the mutant's flag is
/// wrong and the expansion's is right.
const W128_WITNESSES: [(Sign, &str, u128, u128); 13] = [
    (
        Sign::Unsigned,
        "drop_carry",
        0x2_0000_0000_0000_0005,
        0x7fff_ffff_ffff_ffff,
    ),
    (Sign::Unsigned, "drop_both", 1 << 65, 1 << 64),
    (
        Sign::Unsigned,
        "drop_o1",
        0x2_5555_5555_5555_5558,
        0xaaaa_aaaa_aaaa_aaab,
    ),
    (Sign::Unsigned, "drop_o2", 0x8000_0000_0000_0000, 1 << 66),
    (
        Sign::Unsigned,
        "carry_signed",
        0x8000_0000_0000_0002,
        0x1_ffff_ffff_ffff_fff9,
    ),
    (Sign::Unsigned, "carry_ule", 0, 0xffff_ffff_ffff_ffff),
    (Sign::Unsigned, "smul_cross", (1 << 127) - 1, 2),
    (Sign::Signed, "no_zero_guard", 1 << 127, 0),
    (Sign::Signed, "no_sign_check", u128::MAX, 1 << 127),
    (
        Sign::Signed,
        "no_ou",
        3,
        0x5555_5555_5555_5555_5555_5555_5555_5556,
    ),
    (Sign::Signed, "neg_or", 1 << 127, u128::MAX),
    (
        Sign::Signed,
        "pu_eq_r",
        0xffff_ffff_ffff_ffff_c682_f89a_f6c0_2260,
        0x4_d2ed_c029_572a_6118,
    ),
    (Sign::Signed, "unsigned_core_raw", 2, 0xc0 << 120),
];

/// A directed 128-bit battery: every pair of these patterns (both signs'
/// edges: 0, 1, -1, MIN, MAX, 2^64 and its neighbours, products just under
/// and just over 2^128 and 2^127).
fn edge_values() -> Vec<u128> {
    let mut v: Vec<u128> = vec![
        0,
        1,
        2,
        3,
        u128::MAX,
        u128::MAX - 1,
        1 << 127,
        (1 << 127) - 1,
        (1 << 127) + 1,
        1 << 126,
        1 << 64,
        (1 << 64) - 1,
        (1 << 64) + 1,
        1 << 63,
        (1 << 63) - 1,
        1 << 65,
        u128::MAX / 3,
        u128::MAX / 3 + 1,
        0xffff_ffff_ffff_ffff_0000_0000_0000_0000,
        0x0000_0000_ffff_ffff_ffff_ffff_ffff_ffff,
        0xdead_beef_cafe_f00d_0123_4567_89ab_cdef,
    ];
    // Negations of everything above (the signed edges).
    let negated: Vec<u128> = v.iter().map(|x| x.wrapping_neg()).collect();
    v.extend(negated);
    v.sort_unstable();
    v.dedup();
    v
}

/// xorshift64*: a fixed, dependency-free pseudo-random stream.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 >> 12;
        self.0 ^= self.0 << 25;
        self.0 ^= self.0 >> 27;
        self.0.wrapping_mul(0x2545_f491_4f6c_dd1d)
    }

    /// A 128-bit pattern with a random bit length (so small, limb-sized and
    /// full operands all occur), sign included.
    fn operand(&mut self) -> u128 {
        let x = (u128::from(self.next()) << 64) | u128::from(self.next());
        let bits = (self.next() % 129) as u32;
        let x = if bits == 128 { x } else { x & mask(bits) };
        if self.next() % 2 == 0 {
            x
        } else {
            x.wrapping_neg()
        }
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

/// A canonical rendering of an instruction list: values numbered in order of
/// first appearance, so two translations compare by structure.
fn render(a: Value, b: Value, instrs: &[Instruction]) -> Vec<String> {
    let mut names: HashMap<Value, usize> = HashMap::from([(a, 0), (b, 1)]);
    let name = |v: Value, names: &mut HashMap<Value, usize>| {
        let next = names.len();
        format!("v{}", *names.entry(v).or_insert(next))
    };
    instrs
        .iter()
        .map(|inst| {
            let args: Vec<String> = inst.args.iter().map(|&v| name(v, &mut names)).collect();
            let results: Vec<String> = inst.results.iter().map(|&v| name(v, &mut names)).collect();
            format!(
                "{} = {:?} {}",
                results.join(","),
                inst.opcode,
                args.join(",")
            )
        })
        .collect()
}

/// The expansion is chosen per target: x86-64 gets the division-free form
/// (no `Udiv`/`Sdiv`, hence no `__udivti3`/`__divti3` at selection), every
/// other target — the default AArch64 and RISC-V included — the division form.
/// The value is the same `Imul a, b` first instruction on every target.
#[test]
fn the_expansion_is_chosen_per_target() {
    for sign in [Sign::Unsigned, Sign::Signed] {
        let division = if sign == Sign::Unsigned {
            Opcode::Udiv
        } else {
            Opcode::Sdiv
        };
        let mut firsts = Vec::new();
        for arch in [GuardCarrierArch::X86_64, GuardCarrierArch::AArch64] {
            let (a, b, instrs) = entry(sign, arch);
            let divides = instrs.iter().any(|inst| inst.opcode == division);
            assert_eq!(
                divides,
                arch != GuardCarrierArch::X86_64,
                "{sign:?} {arch:?}: {:#?}",
                render(a, b, &instrs)
            );
            assert!(
                !instrs
                    .iter()
                    .any(|inst| matches!(inst.opcode, Opcode::Call { .. })),
                "{sign:?} {arch:?}: the adapter emits no call"
            );
            assert_eq!(instrs[0].opcode, Opcode::Imul, "{sign:?} {arch:?}");
            assert_eq!(instrs[0].args, vec![a, b], "{sign:?} {arch:?}");
            firsts.push(render(a, b, &instrs[..1]));
        }
        assert!(firsts.windows(2).all(|w| w[0] == w[1]), "{firsts:?}");
        // RISC-V keeps the division form (its selector refuses every I128 op
        // and every `Checked*` anyway, design section 1).
        let (a, b, riscv) = entry(sign, GuardCarrierArch::Riscv64);
        assert!(
            riscv.iter().any(|inst| inst.opcode == division),
            "{sign:?} Riscv64: {:#?}",
            render(a, b, &riscv)
        );
        // The default target is AArch64.
        let (a, b, default) = entry(sign, GuardCarrierArch::default());
        let (a64, b64, aarch64) = entry(sign, GuardCarrierArch::AArch64);
        assert_eq!(render(a, b, &default), render(a64, b64, &aarch64));
    }
}

/// The two expansions op for op: the division-free form's 21 (unsigned) and
/// 58 (signed) instructions on x86-64, and the division form kept on AArch64
/// byte for byte (its rendering pinned as before OD-224).
#[test]
fn both_expansions_are_pinned_op_for_op() {
    let shape = |sign: Sign, arch: GuardCarrierArch| -> Vec<String> {
        let (a, b, instrs) = entry(sign, arch);
        let ret = instrs.len() - 1;
        assert_eq!(instrs[ret].opcode, Opcode::Return);
        render(a, b, &instrs[..ret])
    };
    let x86_u = shape(Sign::Unsigned, GuardCarrierArch::X86_64);
    let x86_s = shape(Sign::Signed, GuardCarrierArch::X86_64);
    assert_eq!(x86_u.len(), 21, "{x86_u:#?}");
    assert_eq!(x86_s.len(), 58, "{x86_s:#?}");
    let expected_u = [
        "v2 = Imul v0,v1",
        "v3 = Iconst { ty: I128, imm: 64 } ",
        "v4 = Iconst { ty: I64, imm: 0 } ",
        "v5 = Trunc { to_ty: I64 } v0",
        "v6 = Ushr v0,v3",
        "v7 = Trunc { to_ty: I64 } v6",
        "v8 = Trunc { to_ty: I64 } v1",
        "v9 = Ushr v1,v3",
        "v10 = Trunc { to_ty: I64 } v9",
        "v11 = Ushr v2,v3",
        "v12 = Trunc { to_ty: I64 } v11",
        "v13,v14 = CheckedUmul v7,v8",
        "v15,v16 = CheckedUmul v5,v10",
        "v17 = Iadd v13,v15",
        "v18 = Icmp { cond: UnsignedLessThan } v12,v17",
        "v19 = Icmp { cond: NotEqual } v7,v4",
        "v20 = Icmp { cond: NotEqual } v10,v4",
        "v21 = Band v19,v20",
        "v22 = Bor v14,v16",
        "v23 = Bor v22,v18",
        "v24 = Bor v23,v21",
    ];
    assert_eq!(x86_u, expected_u, "{x86_u:#?}");
    let expected_s = [
        "v2 = Imul v0,v1",
        "v3 = Iconst { ty: I128, imm: 64 } ",
        "v4 = Iconst { ty: I64, imm: 0 } ",
        "v5 = Iconst { ty: I64, imm: 63 } ",
        // the limbs of a, b and the product
        "v6 = Trunc { to_ty: I64 } v0",
        "v7 = Ushr v0,v3",
        "v8 = Trunc { to_ty: I64 } v7",
        "v9 = Trunc { to_ty: I64 } v1",
        "v10 = Ushr v1,v3",
        "v11 = Trunc { to_ty: I64 } v10",
        "v12 = Trunc { to_ty: I64 } v2",
        "v13 = Ushr v2,v3",
        "v14 = Trunc { to_ty: I64 } v13",
        // the sign masks
        "v15 = Sshr v8,v5",
        "v16 = Sshr v11,v5",
        // |a| = (v18, v25)
        "v17 = Bxor v6,v15",
        "v18 = Isub v17,v15",
        "v19 = Isub v4,v6",
        "v20 = Bor v6,v19",
        "v21 = Ushr v20,v5",
        "v22 = Band v21,v15",
        "v23 = Bxor v8,v15",
        "v24 = Isub v23,v15",
        "v25 = Isub v24,v22",
        // |b| = (v27, v34)
        "v26 = Bxor v9,v16",
        "v27 = Isub v26,v16",
        "v28 = Isub v4,v9",
        "v29 = Bor v9,v28",
        "v30 = Ushr v29,v5",
        "v31 = Band v30,v16",
        "v32 = Bxor v11,v16",
        "v33 = Isub v32,v16",
        "v34 = Isub v33,v31",
        // the product's sign mask, and pu1 = hi(|a| * |b| mod 2^128)
        "v35 = Bxor v15,v16",
        "v36 = Isub v4,v12",
        "v37 = Bor v12,v36",
        "v38 = Ushr v37,v5",
        "v39 = Band v38,v35",
        "v40 = Bxor v14,v35",
        "v41 = Isub v40,v35",
        "v42 = Isub v41,v39",
        // the unsigned core on (|a|, |b|, pu1) -> ou = v54
        "v43,v44 = CheckedUmul v25,v27",
        "v45,v46 = CheckedUmul v18,v34",
        "v47 = Iadd v43,v45",
        "v48 = Icmp { cond: UnsignedLessThan } v42,v47",
        "v49 = Icmp { cond: NotEqual } v25,v4",
        "v50 = Icmp { cond: NotEqual } v34,v4",
        "v51 = Band v49,v50",
        "v52 = Bor v44,v46",
        "v53 = Bor v52,v48",
        "v54 = Bor v53,v51",
        // the sign check
        "v55 = Sshr v14,v5",
        "v56 = Bxor v55,v35",
        "v57 = Icmp { cond: NotEqual } v56,v4",
        "v58 = Bor v12,v14",
        "v59 = Icmp { cond: NotEqual } v58,v4",
        "v60 = Band v57,v59",
        "v61 = Bor v54,v60",
    ];
    assert_eq!(x86_s, expected_s, "{x86_s:#?}");

    let a64_u = shape(Sign::Unsigned, GuardCarrierArch::AArch64);
    let expected_a64_u = [
        "v2 = Imul v0,v1",
        "v3 = Iconst128 { lo: 0, hi: 0 } ",
        "v4 = Iconst128 { lo: 1, hi: 0 } ",
        "v5 = Icmp { cond: Equal } v0,v3",
        "v6 = Select { cond: NotEqual } v5,v4,v0",
        "v7 = Udiv v2,v6",
        "v8 = Icmp { cond: NotEqual } v0,v3",
        "v9 = Icmp { cond: NotEqual } v7,v1",
        "v10 = Band v8,v9",
    ];
    assert_eq!(a64_u, expected_a64_u, "{a64_u:#?}");
    let a64_s = shape(Sign::Signed, GuardCarrierArch::AArch64);
    let expected_a64_s = [
        "v2 = Imul v0,v1",
        "v3 = Iconst128 { lo: 0, hi: 0 } ",
        "v4 = Iconst128 { lo: 1, hi: 0 } ",
        "v5 = Iconst128 { lo: 0, hi: -9223372036854775808 } ",
        "v6 = Iconst128 { lo: -1, hi: -1 } ",
        "v7 = Icmp { cond: Equal } v1,v3",
        "v8 = Icmp { cond: Equal } v0,v5",
        "v9 = Icmp { cond: Equal } v1,v6",
        "v10 = Band v8,v9",
        "v11 = Bor v7,v10",
        "v12 = Select { cond: NotEqual } v11,v4,v1",
        "v13 = Sdiv v2,v12",
        "v14 = Icmp { cond: NotEqual } v1,v3",
        "v15 = Icmp { cond: NotEqual } v13,v0",
        "v16 = Band v14,v15",
        "v17 = Bor v16,v10",
    ];
    assert_eq!(a64_s, expected_a64_s, "{a64_s:#?}");
}

/// Exhaustive at the scaled analog `W = 8` (4-bit limbs), every one of the
/// 65,536 pairs: both expansions' flags equal trust-ir's, for both signs.
/// Evidence for this width only.
#[test]
fn every_expansion_is_exact_on_every_pair_at_eight_bits() {
    for sign in [Sign::Unsigned, Sign::Signed] {
        for arch in [GuardCarrierArch::X86_64, GuardCarrierArch::AArch64] {
            let (a, b, instrs) = entry(sign, arch);
            let program = Program::compile(a, b, &instrs, 8);
            assert_eq!(
                mismatches_all_pairs(&program, sign),
                0,
                "{sign:?} {arch:?} at W=8"
            );
        }
    }
}

/// The batched evaluator the `W = 16` sweep uses equals the per-pair one on
/// every pair at `W = 8`, and on a spread of `W = 16` rows.
#[test]
fn the_batched_evaluator_equals_the_per_pair_one() {
    for sign in [Sign::Unsigned, Sign::Signed] {
        let (a, b, instrs) = entry(sign, GuardCarrierArch::X86_64);
        for (w, rows) in [
            (8, (0..256u32).collect::<Vec<_>>()),
            (
                16,
                vec![
                    0, 1, 2, 0xff, 0x100, 0x101, 0x7fff, 0x8000, 0x8001, 0xfffe, 0xffff,
                ],
            ),
        ] {
            let program = Program::compile(a, b, &instrs, w);
            let mut scratch = Vec::new();
            for &row in &rows {
                let lanes = program.run_row(row, &mut scratch);
                let step = if w == 8 { 1 } else { 97 };
                for col in (0..lanes.len()).step_by(step) {
                    assert_eq!(
                        u128::from(lanes[col]),
                        program.run(u128::from(row), col as u128),
                        "{sign:?} W={w} ({row:#x}, {col:#x})"
                    );
                }
            }
        }
    }
}

/// Exhaustive at the scaled analog `W = 16` (8-bit limbs): all 2^32 pairs of
/// each division-free expansion, on two threads. Evidence for this width only.
/// `#[ignore]`d for its cost (minutes); run with `--ignored`.
#[test]
#[ignore = "exhaustive 2^32-pair sweep per sign: run with --ignored --exact"]
fn the_division_free_expansions_are_exact_on_every_pair_at_sixteen_bits() {
    for sign in [Sign::Unsigned, Sign::Signed] {
        let (a, b, instrs) = entry(sign, GuardCarrierArch::X86_64);
        let program = Program::compile(a, b, &instrs, 16);
        let start = std::time::Instant::now();
        let halves: Vec<(u64, Option<(u32, u32)>)> = std::thread::scope(|scope| {
            let handles: Vec<_> = [0u32..0x8000, 0x8000..0x1_0000]
                .into_iter()
                .map(|rows| {
                    let program = &program;
                    scope.spawn(move || {
                        let mut scratch = Vec::new();
                        let mut bad = 0u64;
                        let mut first = None;
                        for row in rows {
                            let lanes = program.run_row(row, &mut scratch);
                            for (col, &flag) in lanes.iter().enumerate() {
                                let want = spec(sign, u128::from(row), col as u128, 16);
                                if (flag != 0) != want {
                                    bad += 1;
                                    first.get_or_insert((row, col as u32));
                                }
                            }
                        }
                        (bad, first)
                    })
                })
                .collect();
            handles
                .into_iter()
                .map(|h| h.join().expect("sweep thread"))
                .collect()
        });
        let bad: u64 = halves.iter().map(|(bad, _)| bad).sum();
        eprintln!(
            "I128_MULO_W16 {sign:?}: 4294967296 pairs, {bad} mismatches, {:.1} s",
            start.elapsed().as_secs_f64()
        );
        assert_eq!(bad, 0, "{sign:?} at W=16: first {:?}", halves);
    }
}

/// The design's mutants of the adapter's output are refuted at `W = 8`, each
/// with exactly the mismatch count the design's independent model measured
/// (`t_or` is the one equivalent mutant: 0, as the design found), and the
/// dispatch swaps (each sign's expansion judged as the other) are refuted.
#[test]
fn every_design_mutant_is_refuted_at_eight_bits() {
    let (ua, ub, u_instrs) = entry(Sign::Unsigned, GuardCarrierArch::X86_64);
    let (sa, sb, s_instrs) = entry(Sign::Signed, GuardCarrierArch::X86_64);
    for (mutant, want) in U_MUTANTS {
        let program = Program::compile(ua, ub, &mutate(&u_instrs, mutant), 8);
        let got = mismatches_all_pairs(&program, Sign::Unsigned);
        assert_eq!(got, want, "unsigned mutant {mutant}");
    }
    for (mutant, want) in S_MUTANTS {
        let program = Program::compile(sa, sb, &mutate(&s_instrs, mutant), 8);
        let got = mismatches_all_pairs(&program, Sign::Signed);
        assert_eq!(got, want, "signed mutant {mutant}");
    }
    let u_program = Program::compile(ua, ub, &u_instrs, 8);
    let s_program = Program::compile(sa, sb, &s_instrs, 8);
    assert_eq!(mismatches_all_pairs(&u_program, Sign::Signed), 2233);
    assert_eq!(mismatches_all_pairs(&s_program, Sign::Unsigned), 2233);
}

/// At the real width, on the directed battery (every pair of
/// [`edge_values`]) and 200,000 random pairs: both targets' expansions agree
/// with Rust's native `checked_mul` (statistical, regression-only evidence),
/// and every non-equivalent mutant is wrong at the design's replayed 128-bit
/// counterexample while the expansion is right there.
#[test]
fn the_expansions_match_native_checked_mul_at_128_bits() {
    let edges = edge_values();
    for sign in [Sign::Unsigned, Sign::Signed] {
        for arch in [GuardCarrierArch::X86_64, GuardCarrierArch::AArch64] {
            let (a, b, instrs) = entry(sign, arch);
            let program = Program::compile(a, b, &instrs, 128);
            let check = |x: u128, y: u128| {
                assert_eq!(
                    program.run(x, y) != 0,
                    spec(sign, x, y, 128),
                    "{sign:?} {arch:?} ({x:#x}, {y:#x})"
                );
            };
            for &x in &edges {
                for &y in &edges {
                    check(x, y);
                }
            }
            let mut rng = Rng(0x9e37_79b9_7f4a_7c15);
            for _ in 0..200_000 {
                check(rng.operand(), rng.operand());
            }
        }
    }
    for (sign, mutant, x, y) in W128_WITNESSES {
        let (a, b, instrs) = entry(sign, GuardCarrierArch::X86_64);
        let real = Program::compile(a, b, &instrs, 128);
        let wrong = Program::compile(a, b, &mutate(&instrs, mutant), 128);
        let truth = spec(sign, x, y, 128);
        assert_eq!(real.run(x, y) != 0, truth, "{mutant}: the expansion");
        assert_ne!(
            wrong.run(x, y) != 0,
            truth,
            "{mutant} SURVIVES at ({x:#x}, {y:#x})"
        );
    }
}

/// The scaled interpreter refuses a constant whose meaning does not survive
/// scaling, so a change of the expansion's constants cannot pass the analog
/// sweeps silently.
#[test]
#[should_panic(expected = "does not scale")]
fn an_unscalable_constant_is_refused() {
    let (a, b, mut instrs) = entry(Sign::Unsigned, GuardCarrierArch::X86_64);
    let i = nth(&instrs, 0, |op| matches!(op, Opcode::Iconst { .. }));
    instrs[i].opcode = Opcode::Iconst {
        ty: Type::I128,
        imm: 63,
    };
    Program::compile(a, b, &instrs, 8);
}

/// The OD-224 seam: inside [`with_x86_i128_mulo_division_form`]`(true, ..)`
/// x86-64 translates the division form, op for op AArch64's; outside it (and
/// after it, the setting restored) the division-free form; AArch64 is the
/// division form either way.
#[test]
fn the_division_form_seam_is_scoped_to_its_closure() {
    for sign in [Sign::Unsigned, Sign::Signed] {
        let rendered = |arch| {
            let (a, b, instrs) = entry(sign, arch);
            render(a, b, &instrs)
        };
        let division_free = rendered(GuardCarrierArch::X86_64);
        let aarch64 = rendered(GuardCarrierArch::AArch64);
        assert_ne!(division_free, aarch64, "{sign:?}");
        let (x86_old, aarch64_old) = with_x86_i128_mulo_division_form(true, || {
            (
                rendered(GuardCarrierArch::X86_64),
                rendered(GuardCarrierArch::AArch64),
            )
        });
        assert_eq!(
            x86_old, aarch64,
            "{sign:?}: the old x86-64 form is AArch64's"
        );
        assert_eq!(aarch64_old, aarch64, "{sign:?}");
        assert_eq!(
            rendered(GuardCarrierArch::X86_64),
            division_free,
            "{sign:?}: restored"
        );
        let nested = with_x86_i128_mulo_division_form(true, || {
            with_x86_i128_mulo_division_form(false, || rendered(GuardCarrierArch::X86_64))
        });
        assert_eq!(nested, division_free, "{sign:?}: the inner setting wins");
    }
}

// ---------------------------------------------------------------------------
// A constant operand: `x >u floor((2^128 - 1) / C)`
// ---------------------------------------------------------------------------

/// `fn mulo_c(a: u128) -> bool { a.checked_mul(C).is_none() }`, or `C * a`
/// when `left`, with `C` spelled canonically (`Int` up to `i128::MAX`).
fn constant_module(c: u128, left: bool) -> TrustIrModule {
    let mut module = TrustIrModule::new("i128_mulo_const");
    let sig = module
        .add_func_type(FuncTy {
            params: vec![Ty::U128],
            returns: vec![Ty::Bool],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut func = TrustIrFunction::new(FuncId::new(0), "mulo", sig, BlockId::new(0));
    let mut block = TrustIrBlock::new(BlockId::new(0));
    block.params = vec![(ValueId::new(0), Ty::U128)];
    let value = if c <= i128::MAX as u128 {
        Constant::Int(c as i128)
    } else {
        Constant::U128(c)
    };
    block.body.push(
        InstrNode::new(Inst::Const {
            ty: Ty::U128,
            value,
        })
        .with_result(ValueId::new(1)),
    );
    let (lhs, rhs) = if left {
        (ValueId::new(1), ValueId::new(0))
    } else {
        (ValueId::new(0), ValueId::new(1))
    };
    block.body.push(
        InstrNode::new(Inst::Overflow {
            op: OverflowOp::MulOverflow,
            ty: Ty::U128,
            lhs,
            rhs,
        })
        .with_results(vec![ValueId::new(2), ValueId::new(3)]),
    );
    block.body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(3)],
    }));
    func.blocks.push(block);
    module.functions.push(func);
    module
}

/// The constants the constant-operand tests multiply by.
fn constants() -> Vec<u128> {
    let mut v = vec![
        0,
        1,
        2,
        3,
        7,
        10,
        10_000_000_000_000_000,
        (1 << 64) - 1,
        1 << 64,
        (1 << 64) + 1,
        1 << 127,
        (1 << 127) - 1,
        u128::MAX,
        u128::MAX - 1,
        u128::MAX / 3,
    ];
    let mut rng = Rng(0x0123_4567_89ab_cdef);
    v.extend((0..40).map(|_| rng.operand()));
    v
}

/// x86-64 translates an unsigned multiply by a constant `C` (either side) to
/// `x >u floor((2^128 - 1) / C)`: no product in the flag, no division. Its
/// flag equals Rust's native `checked_mul` at 128 bits for every constant of
/// [`constants`] and every operand of [`edge_values`] and a random stream
/// (statistical, regression-only evidence for the 128-bit circuit); AArch64
/// keeps the division form.
#[test]
fn a_constant_operand_is_compared_with_its_limit() {
    let license =
        crate::CodegenLicensePolicy::default().with_unlicensed(crate::UnlicensedBodyPolicy::Permit);
    let translate = |c: u128, left: bool, arch: GuardCarrierArch| {
        let function = crate::translate_module_for_arch_with_tls_with_license(
            &constant_module(c, left),
            arch,
            TlsDialect::default(),
            &license,
        )
        .unwrap_or_else(|error| panic!("C={c:#x}: {error:?}"))
        .into_iter()
        .map(|(function, _)| function)
        .find(|function| function.name == "mulo")
        .expect("mulo");
        let block = &function.blocks[&function.entry_block];
        (block.params[0].0, block.instructions.clone())
    };
    let mut operands = edge_values();
    let mut rng = Rng(0x5555_aaaa_5555_aaaa);
    operands.extend((0..2_000).map(|_| rng.operand()));
    for c in constants() {
        for left in [false, true] {
            let (a, instrs) = translate(c, left, GuardCarrierArch::X86_64);
            let compares: Vec<&Instruction> = instrs
                .iter()
                .filter(|inst| {
                    inst.opcode
                        == Opcode::Icmp {
                            cond: IntCC::UnsignedGreaterThan,
                        }
                })
                .collect();
            assert_eq!(compares.len(), 1, "C={c:#x} left={left}: {instrs:#?}");
            assert_eq!(compares[0].args[0], a, "C={c:#x}: the other operand");
            assert!(
                !instrs.iter().any(|inst| matches!(
                    inst.opcode,
                    Opcode::Udiv | Opcode::CheckedUmul | Opcode::Call { .. }
                )),
                "C={c:#x}: {instrs:#?}"
            );
            let program = Program::compile(a, Value(u32::MAX), &instrs, 128);
            for &x in &operands {
                assert_eq!(
                    program.run(x, 0) != 0,
                    x.checked_mul(c).is_none(),
                    "({x:#x}) * {c:#x}, left={left}"
                );
            }
            let (_, aarch64) = translate(c, left, GuardCarrierArch::AArch64);
            assert!(
                aarch64.iter().any(|inst| inst.opcode == Opcode::Udiv),
                "C={c:#x}: AArch64 keeps the division form"
            );
        }
    }
}

/// The limit's identity, `x * C < 2^W` iff `x <= floor((2^W - 1) / C)` (no
/// limit for `C = 0`), on every pair at `W = 8`: the arithmetic fact the
/// constant form rests on, exhaustive at that width (the adapter computes
/// the same limit at 128 bits, tested above).
#[test]
fn the_constant_limit_identity_holds_on_every_pair_at_eight_bits() {
    for c in 0u32..256 {
        let limit = 255u32.checked_div(c).unwrap_or(255);
        for x in 0u32..256 {
            assert_eq!(x * c > 255, x > limit, "{x} * {c}");
        }
    }
}
