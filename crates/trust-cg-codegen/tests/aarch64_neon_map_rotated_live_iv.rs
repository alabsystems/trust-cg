// trust-cg-codegen - rotated map loops whose exit reads the induction
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Rotated (bottom-tested) map loops that return their induction `i`, run
//! through the JIT at every optimization level against a scalar Rust
//! reference:
//!
//! * forward: `i = 20; loop { y[i] += t; if i + 1 >= n { return i } i += 1 }`
//!   on `.4S` (`i32` elements, index and bound), `.2D` (`i64` throughout) and
//!   mixed width (`i32` elements, `i64` index, `i32` bound sign- or
//!   zero-extended to `i64`);
//! * reverse: `i = n; loop { y[i - 1] += t; if !(i > 1) { return i } i -= 1 }`
//!   with an `i64` count, or an `i32` count sign- or zero-extended to `i64`.
//!
//! `t` is `5` (one array) or `x[i]` / `x[i - 1]` (two arrays). The exit reads
//! `i`, the value BEFORE the step, so a forward loop entered below its bound
//! returns `n - 1` and a reverse loop entered at `n >= 1` returns `1`. These
//! are the rotated shapes the NEON map vectorizer (`neon_map`) recognizes
//! when the exit does not read `i` (see `aarch64_neon_map_rotated_entry` and
//! `aarch64_neon_map_rotated_reverse_entry`). Its vector code leaves `i` one
//! step past that value (`n`, or `0`) when it consumes every element and
//! branches straight to the exit. The cases are bounded executions on the
//! host, not a proof of the transform.
#![cfg(target_arch = "aarch64")]

use std::collections::HashMap;
use std::fmt::Debug;

use trust_cg_codegen::compiler::{Compiler, CompilerConfig, JitCompilationResult};
use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::target::Target;
use trust_ir::{BinOp, ICmpOp, Ty, ValueId};
use trust_ir_build::{FunctionBuilder, ModuleBuilder};

const LEVELS: [OptLevel; 4] = [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3];
const ENTRY: &str = "rotated_live_iv";
/// The forward loop's constant entry index.
const START: i64 = 20;
/// Elements of each buffer below `y` and `x`; the lowest reverse count's one
/// iteration touches `y[-41]`.
const OFF: usize = 64;
/// Elements of each buffer; the highest bound touches up to `y[179]`.
const LEN: usize = OFF + 192;
/// Forward bounds below, at and past the entry index. `n - START` is a
/// multiple of the `.2D` width (8) at 28, 36, 44 and 100, and of the `.4S`
/// width (16) at 36, 52, 100 and 180, where the vector code consumes every
/// element.
const BOUNDS: [i64; 16] = [
    -5, 0, 20, 21, 22, 27, 28, 29, 35, 36, 37, 44, 52, 99, 100, 180,
];
/// Reverse counts at and below zero, then across and at multiples of the
/// `.4S` width.
const COUNTS: [i64; 15] = [-40, -1, 0, 1, 2, 15, 16, 17, 32, 33, 48, 64, 100, 127, 128];

/// How the count or bound parameter reaches the induction's width.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Widen {
    Same,
    Sext,
    Zext,
}

impl Widen {
    /// The parameter's value as the loop reads it, from the `i64` a case is
    /// written in.
    fn widened(self, n: i64) -> i64 {
        match self {
            Widen::Same => n,
            Widen::Sext => i64::from(n as i32),
            Widen::Zext => i64::from(n as i32 as u32),
        }
    }
}

/// An element type the cases store.
trait Elem: Copy + PartialEq + Debug {
    fn of(value: i64) -> Self;
    fn plus(self, other: Self) -> Self;
}

impl Elem for i32 {
    fn of(value: i64) -> Self {
        value as i32
    }
    fn plus(self, other: Self) -> Self {
        self.wrapping_add(other)
    }
}

impl Elem for i64 {
    fn of(value: i64) -> Self {
        value
    }
    fn plus(self, other: Self) -> Self {
        self.wrapping_add(other)
    }
}

/// One loop: its direction, element and index types, the count or bound
/// parameter's type and widening, and whether it reads a second array.
#[derive(Debug, Clone)]
struct Shape {
    label: &'static str,
    reverse: bool,
    elem: Ty,
    idx: Ty,
    param: Ty,
    widen: Widen,
    two_arrays: bool,
}

fn forward(label: &'static str, elem: Ty, idx: Ty, param: Ty, widen: Widen) -> Shape {
    Shape {
        label,
        reverse: false,
        elem,
        idx,
        param,
        widen,
        two_arrays: false,
    }
}

fn reverse(label: &'static str, param: Ty, widen: Widen) -> Shape {
    Shape {
        label,
        reverse: true,
        elem: Ty::I32,
        idx: Ty::I64,
        param,
        widen,
        two_arrays: false,
    }
}

impl Shape {
    fn with_two_arrays(self) -> Shape {
        Shape {
            two_arrays: true,
            ..self
        }
    }

    /// The trust-ir module: `(y, [x,] n) -> i`.
    fn module(&self) -> trust_ir::Module {
        let mut mb = ModuleBuilder::new("aarch64_neon_map_rotated_live_iv");
        let mut params = vec![Ty::Ptr];
        if self.two_arrays {
            params.push(Ty::Ptr);
        }
        params.push(self.param.clone());
        let sig = mb.add_func_type(params, vec![self.idx.clone()]);
        let mut fb = mb.function(ENTRY, sig);
        let entry = fb.create_block();
        let y = fb.add_block_param(entry, Ty::Ptr);
        let x = self.two_arrays.then(|| fb.add_block_param(entry, Ty::Ptr));
        let n_param = fb.add_block_param(entry, self.param.clone());
        let head = fb.create_block();
        let i = fb.add_block_param(head, self.idx.clone());
        let exit = fb.create_block();

        fb.switch_to_block(entry);
        let n = match self.widen {
            Widen::Same => n_param,
            Widen::Sext => fb.sext(self.param.clone(), self.idx.clone(), n_param),
            Widen::Zext => fb.zext(self.param.clone(), self.idx.clone(), n_param),
        };
        let one = fb.iconst(self.idx.clone(), 1);
        if self.reverse {
            fb.br(head, vec![n]);
            fb.switch_to_block(head);
            let next = fb.binop(BinOp::Sub, self.idx.clone(), i, one);
            self.bump(&mut fb, y, x, next);
            let more = fb.icmp(ICmpOp::Sgt, self.idx.clone(), i, one);
            fb.condbr(more, head, vec![next], exit, vec![]);
        } else {
            let start = fb.iconst(self.idx.clone(), i128::from(START));
            fb.br(head, vec![start]);
            fb.switch_to_block(head);
            self.bump(&mut fb, y, x, i);
            let next = fb.binop(BinOp::Add, self.idx.clone(), i, one);
            let done = fb.icmp(ICmpOp::Sge, self.idx.clone(), next, n);
            fb.condbr(done, exit, vec![], head, vec![next]);
        }

        fb.switch_to_block(exit);
        fb.ret(vec![i]);
        fb.build();
        mb.build().expect("ModuleBuilder::build: test fixture")
    }

    /// `y[at] += x[at]` with two arrays, else `y[at] += 5`.
    fn bump(&self, fb: &mut FunctionBuilder<'_>, y: ValueId, x: Option<ValueId>, at: ValueId) {
        let term = match x {
            Some(x) => {
                let px = fb.gep(self.elem.clone(), x, vec![at]);
                fb.load(self.elem.clone(), px)
            }
            None => fb.iconst(self.elem.clone(), 5),
        };
        let py = fb.gep(self.elem.clone(), y, vec![at]);
        let v = fb.load(self.elem.clone(), py);
        let bumped = fb.binop(BinOp::Add, self.elem.clone(), v, term);
        fb.store(self.elem.clone(), py, bumped);
    }

    /// The parameters a case runs: the bounds or counts, less the negative
    /// ones a zero extension turns into a count of about 2^32.
    fn cases(&self) -> Vec<i64> {
        let all: &[i64] = if self.reverse { &COUNTS } else { &BOUNDS };
        all.iter()
            .copied()
            .filter(|&n| self.widen != Widen::Zext || n >= 0)
            .collect()
    }

    /// The scalar reference over `y` and `x` (each [`OFF`] into its buffer):
    /// the memory it leaves and the `i` it returns.
    fn reference<T: Elem>(&self, y: &mut [T], x: &[T], n: i64) -> i64 {
        let n = self.widen.widened(n);
        let mut i = if self.reverse { n } else { START };
        loop {
            let at = (OFF as i64 + if self.reverse { i - 1 } else { i }) as usize;
            y[at] = y[at].plus(if self.two_arrays { x[at] } else { T::of(5) });
            let done = if self.reverse { i <= 1 } else { i + 1 >= n };
            if done {
                return i;
            }
            i += if self.reverse { -1 } else { 1 };
        }
    }
}

fn jit(module: &trust_ir::Module, opt_level: OptLevel) -> JitCompilationResult {
    let mut config = CompilerConfig::jit_fast(Target::Aarch64);
    config.opt_level = opt_level;
    Compiler::new(config)
        .with_codegen_license(permit_unlicensed())
        .compile_module_to_jit(module, &HashMap::new())
        .unwrap_or_else(|error| panic!("{opt_level:?}: {error}"))
}

/// Call the kernel `result` holds for `shape` on `(y, x, n)`, where the
/// parameter and return types are `P` and `R`, and widen its return to `i64`.
fn call<T, P, R>(result: &JitCompilationResult, shape: &Shape, y: *mut T, x: *const T, n: P) -> R {
    if shape.two_arrays {
        // SAFETY: the trust-ir signature is (ptr, ptr, P) -> R, and `result`
        // outlives the call.
        let kernel = unsafe {
            result
                .buffer
                .get_fn_bound::<extern "C" fn(*mut T, *const T, P) -> R>(ENTRY)
        }
        .expect("entry symbol");
        kernel.as_ref()(y, x, n)
    } else {
        // SAFETY: the trust-ir signature is (ptr, P) -> R, and `result`
        // outlives the call.
        let kernel = unsafe {
            result
                .buffer
                .get_fn_bound::<extern "C" fn(*mut T, P) -> R>(ENTRY)
        }
        .expect("entry symbol");
        kernel.as_ref()(y, n)
    }
}

/// Run `shape` at every level on each of its cases and return one line per
/// wrong return value or element.
fn mismatches<T: Elem>(shape: &Shape) -> Vec<String> {
    let module = shape.module();
    let label = if shape.two_arrays {
        format!("{} two arrays", shape.label)
    } else {
        shape.label.to_string()
    };
    let mut wrong = Vec::new();
    for opt_level in LEVELS {
        let result = jit(&module, opt_level);
        for n in shape.cases() {
            let mut y: Vec<T> = (0..LEN as i64).map(T::of).collect();
            let x: Vec<T> = (0..LEN as i64).map(|v| T::of(3 * v + 1)).collect();
            let mut want = y.clone();
            let want_ret = shape.reference(&mut want, &x, n);
            // SAFETY: `y` and `x` hold LEN elements. The forward loop touches
            // `[OFF + START, OFF + max(n, START + 1))` and the reverse loop
            // `[OFF + min(n, 1) - 1, OFF + max(n, 1))`, both inside them.
            let (yp, xp) = unsafe { (y.as_mut_ptr().add(OFF), x.as_ptr().add(OFF)) };
            let got_ret = match (&shape.param, &shape.idx) {
                (Ty::I32, Ty::I32) => {
                    i64::from(call::<T, i32, i32>(&result, shape, yp, xp, n as i32))
                }
                (Ty::I32, _) => call::<T, i32, i64>(&result, shape, yp, xp, n as i32),
                _ => call::<T, i64, i64>(&result, shape, yp, xp, n),
            };
            if got_ret != want_ret {
                wrong.push(format!(
                    "{label} {opt_level:?} n={n}: returned {got_ret} (want {want_ret})"
                ));
            }
            if y != want {
                let first = (0..LEN).find(|&at| y[at] != want[at]).unwrap();
                wrong.push(format!(
                    "{label} {opt_level:?} n={n}: y[{}] = {:?} (want {:?})",
                    first as i64 - OFF as i64,
                    y[first],
                    want[first]
                ));
            }
        }
    }
    wrong
}

#[test]
fn a_rotated_forward_map_returns_its_last_index() {
    let i32_shapes = [
        forward(".4S", Ty::I32, Ty::I32, Ty::I32, Widen::Same),
        forward("mixed sext", Ty::I32, Ty::I64, Ty::I32, Widen::Sext),
        forward("mixed zext", Ty::I32, Ty::I64, Ty::I32, Widen::Zext),
    ];
    let i64_shapes = [forward(".2D", Ty::I64, Ty::I64, Ty::I64, Widen::Same)];
    let mut wrong = Vec::new();
    for shape in i32_shapes {
        wrong.extend(mismatches::<i32>(&shape));
        wrong.extend(mismatches::<i32>(&shape.with_two_arrays()));
    }
    for shape in i64_shapes {
        wrong.extend(mismatches::<i64>(&shape));
        wrong.extend(mismatches::<i64>(&shape.with_two_arrays()));
    }
    assert!(wrong.is_empty(), "\n  {}", wrong.join("\n  "));
}

#[test]
fn a_rotated_reverse_map_returns_one() {
    let shapes = [
        reverse("i64 count", Ty::I64, Widen::Same),
        reverse("sext i32 count", Ty::I32, Widen::Sext),
        reverse("zext i32 count", Ty::I32, Widen::Zext),
    ];
    let mut wrong = Vec::new();
    for shape in shapes {
        wrong.extend(mismatches::<i32>(&shape));
        wrong.extend(mismatches::<i32>(&shape.with_two_arrays()));
    }
    assert!(wrong.is_empty(), "\n  {}", wrong.join("\n  "));
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes (or is refused) because the license silently refused it.
fn permit_unlicensed() -> trust_cg_codegen::CodegenLicensePolicy {
    trust_cg_codegen::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_codegen::UnlicensedBodyPolicy::Permit)
}
