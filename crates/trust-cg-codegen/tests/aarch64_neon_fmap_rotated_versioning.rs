// trust-cg-codegen - runtime alias versioning of rotated FP maps from any start
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! `i = start; do { y[i] = x[i] * 2.0; i += 1 } while !(i >= n)` with `x`
//! and `y` plain pointer parameters, run through the JIT at every
//! optimization level against a scalar Rust reference. `x` is `y` shifted by
//! `d` elements, so for `0 < d` below the vector width a vector block reads
//! elements the scalar loop has already overwritten.
//!
//! Neither pointer is `noalias`, so the NEON FP map vectorizer (`neon_fmap`)
//! versions the loop on a runtime check that the stored and read ranges are
//! disjoint (its regime C). The loop accesses `[start, n)` of both arrays,
//! which reaches below the base pointers when `start < 0`. The widths are the
//! ones it lowers: `f32` and `f64` elements with an `i32` index, with an
//! `i64` index and an `i32` bound sign- or zero-extended (MIXED), and with an
//! `i64` index and bound. The cases are bounded executions on the host, not a
//! proof of the transform.
#![cfg(target_arch = "aarch64")]

use std::collections::HashMap;

use trust_cg_codegen::compiler::{Compiler, CompilerConfig, JitCompilationResult};
use trust_cg_codegen::pipeline::{OptLevel, Pipeline, PipelineConfig};
use trust_cg_codegen::target::Target;
use trust_ir::{BinOp, ICmpOp, Ty};
use trust_ir_build::ModuleBuilder;

const LEVELS: [OptLevel; 4] = [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3];
const ENTRY: &str = "rotated_scale";
/// Starts below, at and above zero.
const STARTS: [i64; 5] = [-40, -17, -1, 0, 20];
/// Bounds relative to the start, across the vector widths.
const TRIPS: [i64; 8] = [1, 2, 5, 16, 17, 23, 40, 64];
/// Absolute bounds near zero, where a negative start runs past them.
const ABSOLUTE: [i64; 3] = [0, 2, 5];
/// `x = y - d` elements.
const SHIFTS: [i64; 10] = [-8, -1, 1, 2, 3, 7, 8, 15, 16, 40];
/// Room below the lowest read and above the highest store.
const MARGIN: i64 = 64;
const SPAN: usize = 256;

/// How the bound reaches the loop's `i64` compare.
#[derive(Clone, Copy, Debug, PartialEq)]
enum Shape {
    /// `i32` index and bound.
    I32,
    /// `i64` index, `i32` bound sign-extended.
    MixedSext,
    /// `i64` index, `i32` bound zero-extended.
    MixedZext,
    /// `i64` index and bound.
    I64,
}

impl Shape {
    fn idx(self) -> Ty {
        if self == Shape::I32 { Ty::I32 } else { Ty::I64 }
    }
    fn bound(self) -> Ty {
        if self == Shape::I64 { Ty::I64 } else { Ty::I32 }
    }
}

fn scale_module(elem: Ty, shape: Shape) -> trust_ir::Module {
    let idx = shape.idx();
    let bound = shape.bound();
    let mut mb = ModuleBuilder::new("aarch64_neon_fmap_rotated_versioning");
    let sig = mb.add_func_type(vec![Ty::Ptr, Ty::Ptr, idx.clone(), bound.clone()], vec![]);
    let mut fb = mb.function(ENTRY, sig);
    let entry = fb.create_block();
    let y = fb.add_block_param(entry, Ty::Ptr);
    let x = fb.add_block_param(entry, Ty::Ptr);
    let start = fb.add_block_param(entry, idx.clone());
    let n_param = fb.add_block_param(entry, bound.clone());
    let head = fb.create_block();
    let i = fb.add_block_param(head, idx.clone());
    let exit = fb.create_block();

    fb.switch_to_block(entry);
    let n = match shape {
        Shape::MixedSext => fb.sext(Ty::I32, Ty::I64, n_param),
        Shape::MixedZext => fb.zext(Ty::I32, Ty::I64, n_param),
        Shape::I32 | Shape::I64 => n_param,
    };
    fb.br(head, vec![start]);

    fb.switch_to_block(head);
    let src = fb.gep(elem.clone(), x, vec![i]);
    let v = fb.load(elem.clone(), src);
    let two = fb.fconst(elem.clone(), 2.0);
    let scaled = fb.binop(BinOp::FMul, elem.clone(), v, two);
    let dst = fb.gep(elem.clone(), y, vec![i]);
    fb.store(elem, dst, scaled);
    let one = fb.iconst(idx.clone(), 1);
    let next = fb.binop(BinOp::Add, idx.clone(), i, one);
    let done = fb.icmp(ICmpOp::Sge, idx, next, n);
    fb.condbr(done, exit, vec![], head, vec![next]);

    fb.switch_to_block(exit);
    fb.ret(vec![]);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

/// Changing runs of `neon-fmap` over `module` in the `opt_level` pipeline.
fn neon_fmap_changes(module: &trust_ir::Module, opt_level: OptLevel) -> u32 {
    let lowered = trust_cg_lower::translate_module_for_arch_with_tls_with_license(
        module,
        trust_cg_lower::GuardCarrierArch::default(),
        trust_cg_lower::TlsDialect::default(),
        &permit_unlicensed(),
    )
    .expect("lowering");
    let pipeline = Pipeline::new(PipelineConfig {
        opt_level,
        ..PipelineConfig::for_target("aarch64-apple-darwin")
    });
    let mut changes = 0;
    for (function, _) in &lowered {
        let (_, metrics) = pipeline
            .prepare_function_with_metrics(function, None)
            .unwrap_or_else(|error| panic!("{opt_level:?}: {error}"));
        changes += metrics
            .optimization_pass_changes
            .iter()
            .filter(|(name, _)| name == "neon-fmap")
            .map(|(_, count)| count)
            .sum::<u32>();
    }
    changes
}

fn jit(module: &trust_ir::Module, opt_level: OptLevel) -> JitCompilationResult {
    let mut config = CompilerConfig::jit_fast(Target::Aarch64);
    config.opt_level = opt_level;
    Compiler::new(config)
        .with_codegen_license(permit_unlicensed())
        .compile_module_to_jit(module, &HashMap::new())
        .unwrap_or_else(|error| panic!("{opt_level:?}: {error}"))
}

trait Float: Copy {
    fn of(value: i64) -> Self;
    fn scaled(self) -> Self;
    fn bits(self) -> u64;
}

impl Float for f32 {
    fn of(value: i64) -> Self {
        value as f32 * 0.75 + 1.0
    }
    fn scaled(self) -> Self {
        self * 2.0
    }
    fn bits(self) -> u64 {
        u64::from(self.to_bits())
    }
}

impl Float for f64 {
    fn of(value: i64) -> Self {
        value as f64 * 0.75 + 1.0
    }
    fn scaled(self) -> Self {
        self * 2.0
    }
    fn bits(self) -> u64 {
        self.to_bits()
    }
}

/// An integer argument type.
trait Arg: Copy {
    fn of(value: i64) -> Self;
}

impl Arg for i32 {
    fn of(value: i64) -> Self {
        value as i32
    }
}

impl Arg for i64 {
    fn of(value: i64) -> Self {
        value
    }
}

/// The `(start, n, d)` cases. A negative bound zero-extends past `2^31`,
/// a trip the buffers do not hold, so the zero-extended shape skips it.
fn cases(shape: Shape) -> Vec<(i64, i64, i64)> {
    let mut cases = Vec::new();
    for start in STARTS {
        let bounds = TRIPS.iter().map(|trip| start + trip).chain(ABSOLUTE);
        for n in bounds.filter(|&n| shape != Shape::MixedZext || n >= 0) {
            for d in SHIFTS {
                cases.push((start, n, d));
            }
        }
    }
    cases
}

/// Run `shape`'s module at every level and return one line per wrong
/// element. `I` is the index type, `N` the bound parameter type.
fn mismatches<T: Float, I: Arg, N: Arg>(elem: Ty, shape: Shape) -> Vec<String> {
    let module = scale_module(elem.clone(), shape);
    let mut wrong = Vec::new();
    for opt_level in LEVELS {
        let result = jit(&module, opt_level);
        // SAFETY: the trust-ir signature is (ptr, ptr, I, N) -> (), and
        // `result` outlives every call.
        let kernel = unsafe {
            result
                .buffer
                .get_fn_bound::<extern "C" fn(*mut T, *mut T, I, N)>(ENTRY)
        }
        .expect("entry symbol");
        for (start, n, d) in cases(shape) {
            // The do-while runs its body once even at or past the bound.
            let end = n.max(start + 1);
            // Index `i` of `y` is slot `i - start + MARGIN`.
            let slot = |i: i64| (i - start + MARGIN) as usize;
            assert!(slot(end) <= SPAN && slot(start - d) < SPAN);
            let mut buffer: Vec<T> = (0..SPAN as i64).map(T::of).collect();
            let mut want = buffer.clone();
            for i in start..end {
                want[slot(i)] = want[slot(i - d)].scaled();
            }
            // `y[i]` and `x[i] = y[i - d]` stay inside `buffer` for every `i`
            // the scalar loop runs.
            let y = buffer
                .as_mut_ptr()
                .wrapping_offset((MARGIN - start) as isize);
            let x = y.wrapping_offset(-(d as isize));
            kernel.as_ref()(y, x, I::of(start), N::of(n));
            if let Some(at) = (0..SPAN).find(|&at| buffer[at].bits() != want[at].bits()) {
                wrong.push(format!(
                    "{elem:?}/{shape:?} {opt_level:?} start={start} n={n} d={d}: \
                     y[{}] bits {:#x} (want {:#x})",
                    at as i64 - MARGIN + start,
                    buffer[at].bits(),
                    want[at].bits()
                ));
            }
        }
    }
    wrong
}

/// The cases below run the versioned vector code: `neon-fmap` rewrites every
/// width's loop at O2 and O3.
#[test]
fn every_width_is_vectorized_at_o2_and_o3() {
    for elem in [Ty::F32, Ty::F64] {
        for shape in [Shape::I32, Shape::MixedSext, Shape::MixedZext, Shape::I64] {
            let module = scale_module(elem.clone(), shape);
            for opt_level in [OptLevel::O2, OptLevel::O3] {
                assert!(
                    neon_fmap_changes(&module, opt_level) > 0,
                    "{elem:?}/{shape:?} {opt_level:?}: neon-fmap did not fire"
                );
            }
        }
    }
}

#[test]
fn an_i32_indexed_map_reads_what_the_scalar_loop_wrote_from_any_start() {
    let mut wrong = mismatches::<f32, i32, i32>(Ty::F32, Shape::I32);
    wrong.extend(mismatches::<f64, i32, i32>(Ty::F64, Shape::I32));
    assert!(wrong.is_empty(), "\n  {}", wrong.join("\n  "));
}

#[test]
fn a_mixed_width_map_reads_what_the_scalar_loop_wrote_from_any_start() {
    let mut wrong = mismatches::<f32, i64, i32>(Ty::F32, Shape::MixedSext);
    wrong.extend(mismatches::<f64, i64, i32>(Ty::F64, Shape::MixedSext));
    wrong.extend(mismatches::<f32, i64, i32>(Ty::F32, Shape::MixedZext));
    wrong.extend(mismatches::<f64, i64, i32>(Ty::F64, Shape::MixedZext));
    assert!(wrong.is_empty(), "\n  {}", wrong.join("\n  "));
}

#[test]
fn an_i64_indexed_map_reads_what_the_scalar_loop_wrote_from_any_start() {
    let mut wrong = mismatches::<f32, i64, i64>(Ty::F32, Shape::I64);
    wrong.extend(mismatches::<f64, i64, i64>(Ty::F64, Shape::I64));
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
