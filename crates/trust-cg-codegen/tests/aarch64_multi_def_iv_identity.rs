// trust-cg-codegen - induction identity through a register an outer loop copies from the induction
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Induction identity and bound substitution through a register an outer
//! loop writes on two paths, one of them a copy of the inner induction.
//!
//! The invariant these rows pin: a register written with different values on
//! different paths is not one value: not one constant, and not a copy of the
//! induction. Machine IR is not SSA. An outer loop's carried register `x` is
//! written once on the outer entry edge and once on the outer latch edge, and
//! when the outer latch copies the inner induction (`x = i` after the inner
//! loop), the layout-last def of `x` is `MovR x, i`; inside the inner loop
//! `x` holds the previous round's value. A recognizer that decides a register
//! "is the induction" by following copies through the last-wins def map
//! (`same_as_iv`, `resolves_to_iv`, `reaches_reg`) takes `x` for `i`. A copy
//! is followed only when it is the copied register's ONLY definition
//! (`mach_util::sole_copy_source`), so the outer-latch copy is not taken for
//! the induction.
//!
//! The shapes, one module per pass, each an inner loop over `i` inside an
//! outer loop that sets `x = i`:
//!
//! * `array`: a reduction `s += a[x]` or `s ^= a[x]` over `i32` and `i64`;
//! * `find`: a search comparing `a[x]` with the key;
//! * `iota_fill`: a fill whose stored value (`trunc32(x) + inv`) or store
//!   index (`a[x]`) reads `x`, under a signed and an unsigned loop test;
//! * `map`: a native, a rotated and a chain map reading `a[x]` or `b[x]`, and
//!   a chain whose body guard compares `x` (the guard's bound substitution).
//!
//! Every row JIT-runs at O2 and O3 and compares with a plain Rust model of
//! the same loops. A test's doc names what a recognizer that takes `x` for
//! the induction does with its shape: the misreading the row pins against.
//! The rows are bounded host executions; they are tests, not a proof.
#![cfg(target_arch = "aarch64")]

use std::collections::HashMap;

use trust_cg_codegen::compiler::{Compiler, CompilerConfig, JitCompilationResult};
use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::target::Target;

/// Elements of every array.
const LEN: usize = 256;

/// `module` compiled for the AArch64 JIT at `opt_level`, or the refusal.
fn jit(module: &trust_ir::Module, opt_level: OptLevel) -> Result<JitCompilationResult, String> {
    let mut config = CompilerConfig::jit_fast(Target::Aarch64);
    config.opt_level = opt_level;
    Compiler::new(config)
        .with_codegen_license(permit_unlicensed())
        .compile_module_to_jit(module, &HashMap::new())
        .map_err(|error| error.to_string())
}

/// Fails the test with every collected mismatch.
fn assert_no_failures(failures: &[String]) {
    assert!(failures.is_empty(), "\n  {}", failures.join("\n  "));
}

mod array {
    //! `neon_array` (the array-reduction vectorizer) decides that a load index
    //! "is the induction" by following its def through value-preserving copies
    //! (`same_as_iv`). Machine IR is not SSA: an outer loop's carried register
    //! `x` is written once on the outer entry edge and once on the outer latch
    //! edge, and when the outer latch copies the inner induction (`x = i` after
    //! the inner loop) the layout-last def of `x` is `MovR x, i`. Inside the
    //! inner loop `x` holds the previous round's value, so `a[x]` is one
    //! loop-invariant element, not `a[i]`. These tests JIT-run, at O2 and O3,
    //! inner reductions over `a[x]`, and compare with a plain Rust model of the
    //! same loops.

    use super::*;
    use trust_ir::{BinOp, ICmpOp, Ty};
    use trust_ir_build::ModuleBuilder;

    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    enum Term {
        /// `s += a[x]`.
        Sum,
        /// `s ^= a[x]`.
        Xor,
    }

    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    enum Elem {
        I32,
        I64,
    }

    impl Elem {
        fn ty(self) -> Ty {
            match self {
                Elem::I32 => Ty::I32,
                Elem::I64 => Ty::I64,
            }
        }

        fn wrap(self, v: i64) -> i64 {
            match self {
                Elem::I32 => i64::from(v as i32),
                Elem::I64 => v,
            }
        }
    }

    #[derive(Clone, Copy, Debug)]
    struct Shape {
        name: &'static str,
        elem: Elem,
        term: Term,
    }

    /// `fn(a: *const T, n: u64, rounds: u64, x0: u64) -> i64`:
    ///
    /// ```text
    /// x = x0; total = 0
    /// for _ in 0..rounds {
    ///     s = 0; i = 0
    ///     while i <s n { s = TERM(s, a[x]); i += 1 }
    ///     total += s
    ///     x = i            // the inner induction at the inner loop's exit
    /// }
    /// return total
    /// ```
    fn build_module(shape: Shape) -> trust_ir::Module {
        let elem = shape.elem.ty();
        let name = shape.name;
        // The loop test's type is the induction's: a signed `<s` compares
        // `i64` values (trust-ir refuses an `icmp` whose operands are not of
        // its type, `OperandTypeMismatch`, at every ingestion entry since
        // WS7.3). Same register width, so the machine shape under test is
        // unchanged.
        let iv = Ty::I64;
        let mut mb = ModuleBuilder::new(name);
        let fty = mb.add_func_type(
            vec![Ty::Ptr, iv.clone(), Ty::U64, iv.clone()],
            vec![Ty::I64],
        );
        let mut fb = mb.function(name, fty);
        let entry = fb.create_block();
        let a = fb.add_block_param(entry, Ty::Ptr);
        let n = fb.add_block_param(entry, iv.clone());
        let rounds = fb.add_block_param(entry, Ty::U64);
        let x0 = fb.add_block_param(entry, iv.clone());
        let outer = fb.create_block();
        let t = fb.add_block_param(outer, Ty::U64);
        let x = fb.add_block_param(outer, iv.clone());
        let total = fb.add_block_param(outer, elem.clone());
        let ipre = fb.create_block();
        let ihead = fb.create_block();
        let i = fb.add_block_param(ihead, iv.clone());
        let s = fb.add_block_param(ihead, elem.clone());
        let ibody = fb.create_block();
        let olatch = fb.create_block();
        let exit = fb.create_block();

        fb.switch_to_block(entry);
        let zero = fb.iconst(Ty::U64, 0);
        let total0 = fb.iconst(elem.clone(), 0);
        fb.br(outer, vec![zero, x0, total0]);

        fb.switch_to_block(outer);
        let more = fb.icmp(ICmpOp::Ult, Ty::U64, t, rounds);
        fb.condbr(more, ipre, vec![], exit, vec![]);

        fb.switch_to_block(ipre);
        let i0 = fb.iconst(iv.clone(), 0);
        let s0 = fb.iconst(elem.clone(), 0);
        fb.br(ihead, vec![i0, s0]);

        fb.switch_to_block(ihead);
        let c = fb.icmp(ICmpOp::Slt, Ty::I64, i, n);
        fb.condbr(c, ibody, vec![], olatch, vec![]);

        fb.switch_to_block(ibody);
        let p = fb.gep(elem.clone(), a, vec![x]);
        let v = fb.load(elem.clone(), p);
        let s_next = match shape.term {
            Term::Sum => fb.binop(BinOp::Add, elem.clone(), s, v),
            Term::Xor => fb.binop(BinOp::Xor, elem.clone(), s, v),
        };
        let one = fb.iconst(iv.clone(), 1);
        let next = fb.add(iv.clone(), i, one);
        fb.br(ihead, vec![next, s_next]);

        fb.switch_to_block(olatch);
        let total_next = fb.binop(BinOp::Add, elem.clone(), total, s);
        let one = fb.iconst(Ty::U64, 1);
        let t_next = fb.add(Ty::U64, t, one);
        fb.br(outer, vec![t_next, i, total_next]);

        fb.switch_to_block(exit);
        let ret = if shape.elem == Elem::I32 {
            fb.sext(Ty::I32, Ty::I64, total)
        } else {
            total
        };
        fb.ret(vec![ret]);
        fb.build();
        mb.build().expect("ModuleBuilder::build: test fixture")
    }

    /// Plain-Rust model of the module.
    fn model(shape: Shape, a: &[i64], n: u64, rounds: u64, x0: u64) -> i64 {
        let w = |v: i64| shape.elem.wrap(v);
        let (mut x, mut total) = (x0, 0i64);
        for _ in 0..rounds {
            let mut s = 0i64;
            let mut i = 0u64;
            while (i as i64) < n as i64 {
                let v = a[x as usize];
                s = match shape.term {
                    Term::Sum => w(s.wrapping_add(v)),
                    Term::Xor => s ^ v,
                };
                i += 1;
            }
            total = w(total.wrapping_add(s));
            x = i;
        }
        total
    }

    /// `(n, rounds, x0)`. Every index stays below `LEN`.
    const CASES: [(u64, u64, u64); 6] = [
        (64, 1, 3),
        (64, 2, 200),
        (100, 1, 7),
        (32, 3, 0),
        (48, 1, 250),
        (17, 2, 31),
    ];

    fn probe(shape: Shape) -> Vec<String> {
        let name = shape.name;
        let module = build_module(shape);
        let mut failures = Vec::new();
        for opt_level in [OptLevel::O2, OptLevel::O3] {
            let result = match jit(&module, opt_level) {
                Ok(result) => result,
                Err(error) => {
                    failures.push(format!("{name} {opt_level:?}: compile refused: {error}"));
                    continue;
                }
            };
            // SAFETY: the trust-ir signature is (ptr, u64, u64, u64) -> i64; every
            // index the loops read (x0, or an inner exit index n) stays below LEN,
            // and `result` outlives the calls.
            let entry = unsafe {
                result
                    .buffer
                    .get_fn_bound::<extern "C" fn(*const u8, u64, u64, u64) -> i64>(name)
            }
            .expect("entry symbol");
            // Distinct values with both signs, so a read of `a[i]` for `a[x]`
            // changes every term.
            let a64: Vec<i64> = (0..LEN as i64)
                .map(|v| shape.elem.wrap((v * 7919) % 2003 - 1000))
                .collect();
            let a32: Vec<i32> = a64.iter().map(|&v| v as i32).collect();
            for (n, rounds, x0) in CASES {
                let want = model(shape, &a64, n, rounds, x0);
                let ptr: *const u8 = match shape.elem {
                    Elem::I32 => a32.as_ptr().cast(),
                    Elem::I64 => a64.as_ptr().cast(),
                };
                let got = entry.as_ref()(ptr, n, rounds, x0);
                if got != want {
                    failures.push(format!(
                        "{name} {opt_level:?} n={n} rounds={rounds} x0={x0}: got {got}, want {want}"
                    ));
                }
            }
        }
        failures
    }

    fn run(shapes: &[Shape]) {
        let mut failures = Vec::new();
        for &shape in shapes {
            failures.extend(probe(shape));
        }
        assert_no_failures(&failures);
    }

    /// `s += a[x]` over `i32` and `i64`: the vector loop sums `a[0..n)` where
    /// the scalar loop adds the one element `a[x]` `n` times.
    #[test]
    fn sum_of_a_at_an_outer_copy_of_the_induction_reads_x() {
        run(&[
            Shape {
                name: "rx_sum_i32",
                elem: Elem::I32,
                term: Term::Sum,
            },
            Shape {
                name: "rx_sum_i64",
                elem: Elem::I64,
                term: Term::Sum,
            },
        ]);
    }

    /// `s ^= a[x]` over `i32` and `i64`.
    #[test]
    fn xor_of_a_at_an_outer_copy_of_the_induction_reads_x() {
        run(&[
            Shape {
                name: "rx_xor_i32",
                elem: Elem::I32,
                term: Term::Xor,
            },
            Shape {
                name: "rx_xor_i64",
                elem: Elem::I64,
                term: Term::Xor,
            },
        ]);
    }
}

mod find {
    //! `neon_find` vectorizes `for i in 0..n { if a[i] == key { return i } }`
    //! with a block filter and decides that the load index "is the induction"
    //! by following its def through value-preserving copies (`resolves_to_iv`).
    //! Machine IR is not SSA: an outer loop's carried register `x` is written
    //! once on the outer entry edge and once on the outer latch edge, and when
    //! the outer latch copies the inner induction (`x = i` after the inner loop)
    //! the layout-last def of `x` is `MovR x, i`. Inside the inner loop `x`
    //! holds the previous round's value, so `a[x]` is one loop-invariant element.
    //! These tests JIT-run, at O2 and O3, searches that compare `a[x]`, and
    //! compare with a plain Rust model of the same loops.

    use super::*;
    use trust_ir::{BinOp, ICmpOp, Ty};
    use trust_ir_build::ModuleBuilder;

    /// `fn(a: *const i32, n: i32, rounds: i32, x0: i32, key: i32) -> i32`:
    ///
    /// ```text
    /// x = x0
    /// for _ in 0..rounds {
    ///     i = 0
    ///     while i < n { if a[x] == key { return i } i += 1 }
    ///     x = i            // the inner induction at the inner loop's exit
    /// }
    /// return -1
    /// ```
    fn build_module(name: &str) -> trust_ir::Module {
        let mut mb = ModuleBuilder::new(name);
        let fty = mb.add_func_type(
            vec![Ty::Ptr, Ty::I32, Ty::I32, Ty::I32, Ty::I32],
            vec![Ty::I32],
        );
        let mut fb = mb.function(name, fty);
        let entry = fb.create_block();
        let a = fb.add_block_param(entry, Ty::Ptr);
        let n = fb.add_block_param(entry, Ty::I32);
        let rounds = fb.add_block_param(entry, Ty::I32);
        let x0 = fb.add_block_param(entry, Ty::I32);
        let key = fb.add_block_param(entry, Ty::I32);
        let outer = fb.create_block();
        let t = fb.add_block_param(outer, Ty::I32);
        let x = fb.add_block_param(outer, Ty::I32);
        let ipre = fb.create_block();
        let ihead = fb.create_block();
        let i = fb.add_block_param(ihead, Ty::I32);
        let ibody = fb.create_block();
        let ilatch = fb.create_block();
        let found = fb.create_block();
        let olatch = fb.create_block();
        let none = fb.create_block();

        fb.switch_to_block(entry);
        let zero = fb.iconst(Ty::I32, 0);
        fb.br(outer, vec![zero, x0]);

        fb.switch_to_block(outer);
        let more = fb.icmp(ICmpOp::Slt, Ty::I32, t, rounds);
        fb.condbr(more, ipre, vec![], none, vec![]);

        fb.switch_to_block(ipre);
        let i0 = fb.iconst(Ty::I32, 0);
        fb.br(ihead, vec![i0]);

        fb.switch_to_block(ihead);
        let c = fb.icmp(ICmpOp::Slt, Ty::I32, i, n);
        fb.condbr(c, ibody, vec![], olatch, vec![]);

        fb.switch_to_block(ibody);
        let idx = fb.sext(Ty::I32, Ty::I64, x);
        let p = fb.gep(Ty::I32, a, vec![idx]);
        let v = fb.load(Ty::I32, p);
        let hit = fb.icmp(ICmpOp::Eq, Ty::I32, v, key);
        fb.condbr(hit, found, vec![], ilatch, vec![]);

        fb.switch_to_block(ilatch);
        let one = fb.iconst(Ty::I32, 1);
        let next = fb.binop(BinOp::Add, Ty::I32, i, one);
        fb.br(ihead, vec![next]);

        fb.switch_to_block(found);
        fb.ret(vec![i]);

        fb.switch_to_block(olatch);
        let one = fb.iconst(Ty::I32, 1);
        let t_next = fb.binop(BinOp::Add, Ty::I32, t, one);
        fb.br(outer, vec![t_next, i]);

        fb.switch_to_block(none);
        let minus_one = fb.iconst(Ty::I32, -1);
        fb.ret(vec![minus_one]);
        fb.build();
        mb.build().expect("ModuleBuilder::build: test fixture")
    }

    /// Plain-Rust model of the module.
    fn model(a: &[i32], n: i32, rounds: i32, x0: i32, key: i32) -> i32 {
        let mut x = x0;
        for _ in 0..rounds {
            let mut i = 0;
            while i < n {
                if a[x as usize] == key {
                    return i;
                }
                i += 1;
            }
            x = i;
        }
        -1
    }

    #[test]
    fn search_comparing_an_outer_copy_of_the_induction_returns_the_first_index() {
        let name = "find_at_x";
        let module = build_module(name);
        // Distinct values: `a[k] == key` holds for exactly one `k`.
        let a: Vec<i32> = (0..LEN as i32).map(|v| v * 3 + 11).collect();
        let mut failures = Vec::new();
        for opt_level in [OptLevel::O2, OptLevel::O3] {
            let result = match jit(&module, opt_level) {
                Ok(result) => result,
                Err(error) => {
                    failures.push(format!("{name} {opt_level:?}: compile refused: {error}"));
                    continue;
                }
            };
            // SAFETY: the trust-ir signature is (ptr, i32, i32, i32, i32) -> i32;
            // the scalar loop reads `a[x]` with `x` = x0 or n, both below LEN, a
            // vector filter reads at most `a[0..n)`, and `result` outlives the
            // calls.
            let entry = unsafe {
                result
                    .buffer
                    .get_fn_bound::<extern "C" fn(*const i32, i32, i32, i32, i32) -> i32>(name)
            }
            .expect("entry symbol");
            // `(n, rounds, x0, key)`: `key = a[k]` puts the only match at `k`.
            for (n, rounds, x0, k) in [
                (64, 1, 3, 3),
                (64, 1, 200, 200),
                (100, 2, 7, 100),
                (64, 1, 5, 40),
                (128, 1, 250, 250),
                (48, 3, 0, 48),
            ] {
                let key = a[k];
                let want = model(&a, n, rounds, x0, key);
                let got = entry.as_ref()(a.as_ptr(), n, rounds, x0, key);
                if got != want {
                    failures.push(format!(
                    "{name} {opt_level:?} n={n} rounds={rounds} x0={x0} key=a[{k}]: got {got}, want {want}"
                ));
                }
            }
        }
        assert_no_failures(&failures);
    }
}

mod iota_fill {
    //! `neon_iota_fill` vectorizes `for i in 0..n { a[i] = trunc32(i) + inv }`
    //! and decides that the stored value and the store index "are the induction"
    //! by following their defs through value-preserving copies (`reaches_reg`,
    //! `reaches_reg64`). Machine IR is not SSA: an outer loop's carried register
    //! `x` is written once on the outer entry edge and once on the outer latch
    //! edge, and when the outer latch copies the inner induction (`x = i` after
    //! the inner loop) the layout-last def of `x` is `MovR x, i`. Inside the
    //! inner loop `x` holds the previous round's value. These tests JIT-run, at
    //! O2 and O3, inner loops that store through such an `x`, and compare with a
    //! plain Rust model of the same loops.

    use super::*;
    use trust_ir::{BinOp, ICmpOp, Ty};
    use trust_ir_build::ModuleBuilder;

    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    enum Through {
        /// `a[i] = trunc32(x) + inv`: the stored value is read through `x`.
        Value,
        /// `a[x] = trunc32(i) + inv`: the store index is `x`.
        Index,
    }

    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    enum Test {
        /// `while i <s n`.
        Signed,
        /// `while i <u n`.
        Unsigned,
    }

    /// `fn(a: *mut i32, n: u64, rounds: u64, x0: u64, inv: u32)`:
    ///
    /// ```text
    /// x = x0
    /// for _ in 0..rounds {
    ///     i = 0
    ///     while i < n { a[i or x] = trunc32(x or i) + inv; i += 1 }
    ///     x = i            // the inner induction at the inner loop's exit
    /// }
    /// ```
    fn build_module(name: &str, through: Through, test: Test) -> trust_ir::Module {
        // The loop test's type is the induction's: a signed `<s` compares
        // `i64` values (trust-ir refuses an `icmp` whose operands are not of
        // its type, `OperandTypeMismatch`, at every ingestion entry since
        // WS7.3). Same register width, so the machine shape under test is
        // unchanged.
        let iv = match test {
            Test::Signed => Ty::I64,
            Test::Unsigned => Ty::U64,
        };
        let mut mb = ModuleBuilder::new(name);
        let fty = mb.add_func_type(
            vec![Ty::Ptr, iv.clone(), Ty::U64, iv.clone(), Ty::U32],
            vec![],
        );
        let mut fb = mb.function(name, fty);
        let entry = fb.create_block();
        let a = fb.add_block_param(entry, Ty::Ptr);
        let n = fb.add_block_param(entry, iv.clone());
        let rounds = fb.add_block_param(entry, Ty::U64);
        let x0 = fb.add_block_param(entry, iv.clone());
        let inv = fb.add_block_param(entry, Ty::U32);
        let outer = fb.create_block();
        let t = fb.add_block_param(outer, Ty::U64);
        let x = fb.add_block_param(outer, iv.clone());
        let ipre = fb.create_block();
        let ihead = fb.create_block();
        let i = fb.add_block_param(ihead, iv.clone());
        let ibody = fb.create_block();
        let olatch = fb.create_block();
        let exit = fb.create_block();

        fb.switch_to_block(entry);
        let zero = fb.iconst(Ty::U64, 0);
        fb.br(outer, vec![zero, x0]);

        fb.switch_to_block(outer);
        let more = fb.icmp(ICmpOp::Ult, Ty::U64, t, rounds);
        fb.condbr(more, ipre, vec![], exit, vec![]);

        fb.switch_to_block(ipre);
        let i0 = fb.iconst(iv.clone(), 0);
        fb.br(ihead, vec![i0]);

        // The store address and value are computed in the header, ahead of the
        // loop test. A header that is more than its test keeps `loop-latch-layout`
        // from moving the test into the latch, so the loop reaches
        // `neon_iota_fill` in its test-first shape.
        fb.switch_to_block(ihead);
        let (index, value_src) = match through {
            Through::Value => (i, x),
            Through::Index => (x, i),
        };
        let p = fb.gep(Ty::U32, a, vec![index]);
        let v32 = fb.trunc(iv.clone(), Ty::U32, value_src);
        let v = fb.binop(BinOp::Add, Ty::U32, v32, inv);
        let c = match test {
            Test::Signed => fb.icmp(ICmpOp::Slt, iv.clone(), i, n),
            Test::Unsigned => fb.icmp(ICmpOp::Ult, iv.clone(), i, n),
        };
        fb.condbr(c, ibody, vec![], olatch, vec![]);

        fb.switch_to_block(ibody);
        fb.store(Ty::U32, p, v);
        let one = fb.iconst(iv.clone(), 1);
        let next = fb.add(iv.clone(), i, one);
        fb.br(ihead, vec![next]);

        fb.switch_to_block(olatch);
        let one = fb.iconst(Ty::U64, 1);
        let t_next = fb.add(Ty::U64, t, one);
        fb.br(outer, vec![t_next, i]);

        fb.switch_to_block(exit);
        fb.ret(vec![]);
        fb.build();
        mb.build().expect("ModuleBuilder::build: test fixture")
    }

    /// Plain-Rust model of the module.
    fn model(through: Through, test: Test, a: &mut [u32], n: u64, rounds: u64, x0: u64, inv: u32) {
        let mut x = x0;
        for _ in 0..rounds {
            let mut i = 0u64;
            loop {
                let go = match test {
                    Test::Signed => (i as i64) < n as i64,
                    Test::Unsigned => i < n,
                };
                if !go {
                    break;
                }
                match through {
                    Through::Value => a[i as usize] = (x as u32).wrapping_add(inv),
                    Through::Index => a[x as usize] = (i as u32).wrapping_add(inv),
                }
                i += 1;
            }
            x = i;
        }
    }

    /// `(n, rounds, x0, inv)`. Every index stays below `LEN`.
    const CASES: [(u64, u64, u64, u32); 6] = [
        (64, 1, 3, 1000),
        (64, 2, 200, 7),
        (100, 1, 7, 0xFFFF_FFF0),
        (32, 3, 0, 0),
        (48, 1, 250, 5),
        (17, 2, 31, 99),
    ];

    fn probe(name: &str, through: Through, test: Test) -> Vec<String> {
        let module = build_module(name, through, test);
        let mut failures = Vec::new();
        for opt_level in [OptLevel::O2, OptLevel::O3] {
            let result = match jit(&module, opt_level) {
                Ok(result) => result,
                Err(error) => {
                    failures.push(format!("{name} {opt_level:?}: compile refused: {error}"));
                    continue;
                }
            };
            // SAFETY: the trust-ir signature is (ptr, u64, u64, u64, u32) -> ();
            // every index the scalar loops store to (i < n <= LEN, or x < LEN)
            // stays below LEN, and `result` outlives the calls.
            let entry = unsafe {
                result
                    .buffer
                    .get_fn_bound::<extern "C" fn(*mut u32, u64, u64, u64, u32)>(name)
            }
            .expect("entry symbol");
            for (n, rounds, x0, inv) in CASES {
                let a0: Vec<u32> = (0..LEN as u32)
                    .map(|v| v.wrapping_mul(0x9E37_79B9))
                    .collect();
                let mut want = a0.clone();
                model(through, test, &mut want, n, rounds, x0, inv);
                let mut got = a0.clone();
                entry.as_ref()(got.as_mut_ptr(), n, rounds, x0, inv);
                if let Some(first) = (0..LEN).find(|&k| got[k] != want[k]) {
                    failures.push(format!(
                    "{name} {opt_level:?} n={n} rounds={rounds} x0={x0} inv={inv:#x}: a[{first}] = {:#x} (want {:#x})",
                    got[first], want[first]
                ));
                }
            }
        }
        failures
    }

    /// The stored value `trunc32(x) + inv` is taken for the iota
    /// `trunc32(i) + inv`: the vector loop stores `i + inv` where the scalar loop
    /// stores the same `x + inv` to every element.
    #[test]
    fn fill_of_an_outer_copy_of_the_induction_stores_x() {
        let mut failures = probe("iota_value_x_s", Through::Value, Test::Signed);
        failures.extend(probe("iota_value_x_u", Through::Value, Test::Unsigned));
        assert_no_failures(&failures);
    }

    /// The store index `x` is taken for `i`: the vector loop stores to
    /// `a[0..n)` where the scalar loop stores only `a[x]`.
    #[test]
    fn iota_stored_at_an_outer_copy_of_the_induction_stores_only_a_x() {
        let mut failures = probe("iota_index_x_s", Through::Index, Test::Signed);
        failures.extend(probe("iota_index_x_u", Through::Index, Test::Unsigned));
        assert_no_failures(&failures);
    }
}

mod map {
    //! `neon_map` decides that a register "is the induction" by following its
    //! def through value-preserving copies (`same_as_iv`). Machine IR is not SSA:
    //! an outer loop's carried register `x` is written once on the outer entry
    //! edge and once on the outer latch edge, and when the outer latch copies the
    //! inner induction (`x = i` after the inner loop) the layout-last def of `x`
    //! is `MovR x, i`. Inside the inner loop `x` holds the previous round's
    //! value, not `i`. These tests JIT-run, at O2 and O3, inner map loops that
    //! address or bounds-check through such an `x`, and compare with a plain Rust
    //! model of the same loops.

    use super::*;
    use trust_ir::{BinOp, ICmpOp, Ty};
    use trust_ir_build::{FunctionBuilder, ModuleBuilder};

    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    enum Shape {
        /// Test-first `while i <s n { a[i] = a[x] + 1; i += 1 }` over `i64`, in
        /// place (the native shape once the loop test moves to the latch).
        TestFirstInPlace,
        /// Bottom-tested `do { a[i] = a[x] + 1; i += 1 } while i + 1 != n` over
        /// `i64`, in place (the rotated shape). The outer latch copies the inner
        /// induction's last value `i`.
        RotatedInPlace,
        /// Test-first unsigned `while i <u n { a[i] = b[x] + 1; i += 1 }` over
        /// `i32` elements with a `u64` index, the addresses computed in the
        /// header ahead of the loop test (the bounds-guard chain shape; distinct
        /// arrays under runtime alias versioning).
        ChainReadX,
        /// Test-first unsigned `while i <u n { if !(x <u n) { return } a[i] += 5;
        /// i += 1 }` over `i32` (the bounds-guard chain): the body guard compares
        /// `x`, not `i`.
        GuardOnX,
    }

    impl Shape {
        fn elem(self) -> Ty {
            match self {
                Shape::TestFirstInPlace | Shape::RotatedInPlace => Ty::I64,
                Shape::ChainReadX | Shape::GuardOnX => Ty::I32,
            }
        }
    }

    /// `fn(a: *mut T, b: *const T, n: u64, rounds: u64, x0: u64)`:
    ///
    /// ```text
    /// x = x0
    /// for _ in 0..rounds {
    ///     <inner loop over i in 0..n reading through x>
    ///     x = i            // the inner induction at the inner loop's exit
    /// }
    /// ```
    fn build_module(name: &str, shape: Shape) -> trust_ir::Module {
        let elem = shape.elem();
        // The loop test's type is the induction's: a signed `<s` compares
        // `i64` values (trust-ir refuses an `icmp` whose operands are not of
        // its type, `OperandTypeMismatch`, at every ingestion entry since
        // WS7.3). Same register width, so the machine shape under test is
        // unchanged.
        let iv = if shape == Shape::TestFirstInPlace {
            Ty::I64
        } else {
            Ty::U64
        };
        let mut mb = ModuleBuilder::new(name);
        let fty = mb.add_func_type(
            vec![Ty::Ptr, Ty::Ptr, iv.clone(), Ty::U64, iv.clone()],
            vec![],
        );
        let mut fb = mb.function(name, fty);
        let entry = fb.create_block();
        let a = fb.add_block_param(entry, Ty::Ptr);
        let b = fb.add_block_param(entry, Ty::Ptr);
        let n = fb.add_block_param(entry, iv.clone());
        let rounds = fb.add_block_param(entry, Ty::U64);
        let x0 = fb.add_block_param(entry, iv.clone());
        let outer = fb.create_block();
        let t = fb.add_block_param(outer, Ty::U64);
        let x = fb.add_block_param(outer, iv.clone());
        let ipre = fb.create_block();
        let ihead = fb.create_block();
        let i = fb.add_block_param(ihead, iv.clone());
        let ibody = (shape != Shape::RotatedInPlace).then(|| fb.create_block());
        let iguard = (shape == Shape::GuardOnX).then(|| fb.create_block());
        let olatch = fb.create_block();
        let exit = fb.create_block();

        fb.switch_to_block(entry);
        let zero = fb.iconst(Ty::U64, 0);
        fb.br(outer, vec![zero, x0]);

        fb.switch_to_block(outer);
        let more = fb.icmp(ICmpOp::Ult, Ty::U64, t, rounds);
        if shape == Shape::RotatedInPlace {
            // The do-while needs a non-empty trip.
            let z = fb.iconst(Ty::U64, 0);
            let nonempty = fb.icmp(ICmpOp::Ne, Ty::U64, n, z);
            let go = fb.binop(BinOp::And, Ty::Bool, more, nonempty);
            fb.condbr(go, ipre, vec![], exit, vec![]);
        } else {
            fb.condbr(more, ipre, vec![], exit, vec![]);
        }

        fb.switch_to_block(ipre);
        let i0 = fb.iconst(iv.clone(), 0);
        fb.br(ihead, vec![i0]);

        // `a[i] = src[x] + 1`.
        let map_through_x = |fb: &mut FunctionBuilder<'_>, src| {
            let pa = fb.gep(elem.clone(), a, vec![i]);
            let ps = fb.gep(elem.clone(), src, vec![x]);
            let v = fb.load(elem.clone(), ps);
            let one = fb.iconst(elem.clone(), 1);
            let r = fb.binop(BinOp::Add, elem.clone(), v, one);
            fb.store(elem.clone(), pa, r);
        };
        let step_to_head = |fb: &mut FunctionBuilder<'_>| {
            let one = fb.iconst(iv.clone(), 1);
            let next = fb.add(iv.clone(), i, one);
            fb.br(ihead, vec![next]);
        };

        match shape {
            Shape::TestFirstInPlace => {
                let ibody = ibody.expect("body");
                fb.switch_to_block(ihead);
                let c = fb.icmp(ICmpOp::Slt, iv.clone(), i, n);
                fb.condbr(c, ibody, vec![], olatch, vec![]);

                fb.switch_to_block(ibody);
                map_through_x(&mut fb, a);
                step_to_head(&mut fb);
            }
            Shape::RotatedInPlace => {
                fb.switch_to_block(ihead);
                map_through_x(&mut fb, a);
                let one = fb.iconst(Ty::U64, 1);
                let next = fb.add(Ty::U64, i, one);
                let done = fb.icmp(ICmpOp::Eq, Ty::U64, next, n);
                fb.condbr(done, olatch, vec![], ihead, vec![next]);
            }
            Shape::ChainReadX => {
                let ibody = ibody.expect("body");
                fb.switch_to_block(ihead);
                let pa = fb.gep(Ty::I32, a, vec![i]);
                let pb = fb.gep(Ty::I32, b, vec![x]);
                let c = fb.icmp(ICmpOp::Ult, Ty::U64, i, n);
                fb.condbr(c, ibody, vec![], olatch, vec![]);

                fb.switch_to_block(ibody);
                let v = fb.load(Ty::I32, pb);
                let one = fb.iconst(Ty::I32, 1);
                let r = fb.binop(BinOp::Add, Ty::I32, v, one);
                fb.store(Ty::I32, pa, r);
                step_to_head(&mut fb);
            }
            Shape::GuardOnX => {
                let (ibody, iguard) = (ibody.expect("body"), iguard.expect("guard"));
                fb.switch_to_block(ihead);
                let c = fb.icmp(ICmpOp::Ult, Ty::U64, i, n);
                fb.condbr(c, iguard, vec![], olatch, vec![]);

                fb.switch_to_block(iguard);
                let g = fb.icmp(ICmpOp::Ult, Ty::U64, x, n);
                fb.condbr(g, ibody, vec![], exit, vec![]);

                fb.switch_to_block(ibody);
                let pa = fb.gep(Ty::I32, a, vec![i]);
                let v = fb.load(Ty::I32, pa);
                let five = fb.iconst(Ty::I32, 5);
                let r = fb.binop(BinOp::Add, Ty::I32, v, five);
                fb.store(Ty::I32, pa, r);
                step_to_head(&mut fb);
            }
        }

        fb.switch_to_block(olatch);
        let one = fb.iconst(Ty::U64, 1);
        let t_next = fb.add(Ty::U64, t, one);
        fb.br(outer, vec![t_next, i]);

        fb.switch_to_block(exit);
        fb.ret(vec![]);
        fb.build();
        mb.build().expect("ModuleBuilder::build: test fixture")
    }

    /// Plain-Rust model of the module. `a` and `b` hold the elements as `i64`
    /// (the `i32` shapes wrap at 32 bits).
    fn model(shape: Shape, a: &mut [i64], b: &[i64], n: u64, rounds: u64, x0: u64) {
        let wrap = |v: i64| match shape.elem() {
            Ty::I32 => i64::from(v as i32),
            _ => v,
        };
        let mut x = x0;
        for _ in 0..rounds {
            match shape {
                Shape::TestFirstInPlace => {
                    let mut i = 0u64;
                    while (i as i64) < n as i64 {
                        a[i as usize] = wrap(a[x as usize].wrapping_add(1));
                        i += 1;
                    }
                    x = i;
                }
                Shape::RotatedInPlace => {
                    if n == 0 {
                        return;
                    }
                    let mut i = 0u64;
                    loop {
                        a[i as usize] = wrap(a[x as usize].wrapping_add(1));
                        if i + 1 == n {
                            break;
                        }
                        i += 1;
                    }
                    x = i;
                }
                Shape::ChainReadX => {
                    let mut i = 0u64;
                    while i < n {
                        a[i as usize] = wrap(b[x as usize].wrapping_add(1));
                        i += 1;
                    }
                    x = i;
                }
                Shape::GuardOnX => {
                    let mut i = 0u64;
                    while i < n {
                        if x >= n {
                            return;
                        }
                        a[i as usize] = wrap(a[i as usize].wrapping_add(5));
                        i += 1;
                    }
                    x = i;
                }
            }
        }
    }

    /// `(n, rounds, x0)` cases. Every `x` the loops read through stays below
    /// `LEN`.
    const CASES: [(u64, u64, u64); 6] = [
        (64, 1, 3),
        (64, 2, 200),
        (100, 1, 7),
        (32, 3, 0),
        (48, 1, 250),
        (16, 2, 31),
    ];

    fn probe(name: &str, shape: Shape) -> Vec<String> {
        let module = build_module(name, shape);
        let mut failures = Vec::new();
        for opt_level in [OptLevel::O2, OptLevel::O3] {
            let result = match jit(&module, opt_level) {
                Ok(result) => result,
                Err(error) => {
                    failures.push(format!("{name} {opt_level:?}: compile refused: {error}"));
                    continue;
                }
            };
            // SAFETY: the trust-ir signature is (ptr, ptr, u64, u64, u64) -> ();
            // every index the loops touch stays below LEN (n <= LEN, and x is x0
            // or an exit value of i, both < LEN), and `result` outlives the calls.
            let entry = unsafe {
                result
                    .buffer
                    .get_fn_bound::<extern "C" fn(*mut u8, *const u8, u64, u64, u64)>(name)
            }
            .expect("entry symbol");
            for (n, rounds, x0) in CASES {
                let b: Vec<i64> = (0..LEN as i64).map(|v| v * 1009 - 77).collect();
                let a0: Vec<i64> = (0..LEN as i64).map(|v| (v ^ 0x5A5A) - 4000).collect();
                let mut want = a0.clone();
                model(shape, &mut want, &b, n, rounds, x0);
                let got: Vec<i64> = if shape.elem() == Ty::I32 {
                    let mut a32: Vec<i32> = a0.iter().map(|&v| v as i32).collect();
                    let b32: Vec<i32> = b.iter().map(|&v| v as i32).collect();
                    entry.as_ref()(a32.as_mut_ptr().cast(), b32.as_ptr().cast(), n, rounds, x0);
                    a32.into_iter().map(i64::from).collect()
                } else {
                    let mut a64 = a0.clone();
                    entry.as_ref()(a64.as_mut_ptr().cast(), b.as_ptr().cast(), n, rounds, x0);
                    a64
                };
                if let Some(first) = (0..LEN).find(|&k| got[k] != want[k]) {
                    failures.push(format!(
                    "{name} {opt_level:?} n={n} rounds={rounds} x0={x0}: a[{first}] = {} (want {})",
                    got[first], want[first]
                ));
                }
            }
        }
        failures
    }

    /// Native shape (`recognize_two_block`, latch test; `resolve_ai_base`'s
    /// `i64` index check): the in-place load `a[x]` is addressed through `x`,
    /// whose layout-last def copies the inner induction. The vector loop must
    /// not read `a[i]` for it.
    #[test]
    fn native_map_reading_through_an_outer_copy_of_the_induction_reads_x() {
        let failures = probe("ivcopy_native_in_place", Shape::TestFirstInPlace);
        assert_no_failures(&failures);
    }

    /// Rotated shape (`recognize_two_block`, header test), `i64` in place.
    #[test]
    fn rotated_map_reading_through_an_outer_copy_of_the_induction_reads_x() {
        let failures = probe("ivcopy_rotated_in_place", Shape::RotatedInPlace);
        assert_no_failures(&failures);
    }

    /// Bounds-guard chain (`recognize_forward_chain`; `resolve_ai_base`'s mixed
    /// `i32` element / `u64` index check): `b[x]` from a distinct array.
    #[test]
    fn chain_map_reading_another_array_through_an_outer_copy_of_the_induction_reads_x() {
        let failures = probe("ivcopy_chain_read_x", Shape::ChainReadX);
        assert_no_failures(&failures);
    }

    /// Bounds-guard chain (`recognize_forward_chain`): the body guard
    /// `x <u n` is taken for the induction's own bounds check (`same_as_iv`,
    /// then `ExitPlan` admits it as proved not taken), so the vector loop runs
    /// iterations the scalar loop leaves through that guard.
    #[test]
    fn chain_guard_on_an_outer_copy_of_the_induction_is_kept() {
        let failures = probe("ivcopy_guard_on_x", Shape::GuardOnX);
        assert_no_failures(&failures);
    }
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes (or is refused) because the license silently refused it.
fn permit_unlicensed() -> trust_cg_codegen::CodegenLicensePolicy {
    trust_cg_codegen::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_codegen::UnlicensedBodyPolicy::Permit)
}
