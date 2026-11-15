// trust-cg-codegen - a rotated FP map whose bound is a zero-extended i32
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! `i = start; do { y[i] = y[i] + 1.0; i += 1 } while !(i >= zext(n))` over
//! `f32` elements with an `i64` index and start and an `i32` bound
//! zero-extended to `i64`: the MIXED shape the NEON FP map vectorizer
//! (`neon_fmap`) lowers through the `i32` bound itself, run through the JIT
//! against an exact reference.
//!
//! For `n >= 0` the zero- and sign-extensions agree and the loop stays
//! vectorized. For `n < 0` the scalar loop runs up to `zext(n) = 2^32 + n`,
//! while `sext(n) = n`. From `start = -17` with `n = -1` that is `2^32 + 16`
//! iterations. To run them cheaply, `y` is virtual memory backed by one
//! 48 MiB file mapped again and again: element `x` lives at physical slot
//! `x mod P` with `P = 3 * 2^22`, so each slot is updated once per element
//! that lands on it, about 342 times. The case is a bounded execution on the
//! host, not a proof of the transform.
#![cfg(all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux")))]

use std::collections::HashMap;
use std::ffi::{c_int, c_void};
use std::os::fd::AsRawFd;

use trust_cg_codegen::compiler::{Compiler, CompilerConfig, JitCompilationResult};
use trust_cg_codegen::pipeline::{OptLevel, Pipeline, PipelineConfig};
use trust_cg_codegen::target::Target;
use trust_ir::{BinOp, ICmpOp, Ty};
use trust_ir_build::ModuleBuilder;

const ENTRY: &str = "bump_to_zext_bound";
/// The wide case: `[START, 2^32 + N)`.
const START: i64 = -17;
const N: i32 = -1;
/// Elements per physical copy (48 MiB, a whole number of 16 KiB pages).
const P: usize = 3 << 22;
const CHUNK_BYTES: usize = P * 4;
/// Copies below `y`: enough for `[START, 0)`.
const BELOW: usize = (START.unsigned_abs() as usize * 4).div_ceil(CHUNK_BYTES) + 1;
/// Copies from `y` up: `[0, 2^32 + N)` plus one.
const ABOVE: usize = ((1usize << 32) * 4).div_ceil(CHUNK_BYTES) + 1;

const PROT_NONE: c_int = 0;
const PROT_READ: c_int = 1;
const PROT_WRITE: c_int = 2;
const MAP_SHARED: c_int = 0x1;
const MAP_PRIVATE: c_int = 0x2;
const MAP_FIXED: c_int = 0x10;
#[cfg(target_os = "macos")]
const MAP_ANON: c_int = 0x1000;
#[cfg(target_os = "linux")]
const MAP_ANON: c_int = 0x20;

unsafe extern "C" {
    fn mmap(
        addr: *mut c_void,
        len: usize,
        prot: c_int,
        flags: c_int,
        fd: c_int,
        offset: i64,
    ) -> *mut c_void;
    fn munmap(addr: *mut c_void, len: usize) -> c_int;
}

/// `BELOW + ABOVE` contiguous views of one `P`-element file.
struct Aliased {
    base: *mut u8,
    len: usize,
    _file: std::fs::File,
}

impl Aliased {
    fn new() -> Self {
        let file = tempfile::tempfile().expect("backing file");
        file.set_len(CHUNK_BYTES as u64).expect("size backing file");
        let len = (BELOW + ABOVE) * CHUNK_BYTES;
        // SAFETY: a fresh PROT_NONE anonymous reservation; nothing aliases it.
        let base = unsafe {
            mmap(
                std::ptr::null_mut(),
                len,
                PROT_NONE,
                MAP_PRIVATE | MAP_ANON,
                -1,
                0,
            )
        };
        assert_ne!(base as isize, -1, "reserve {len} bytes");
        for chunk in 0..BELOW + ABOVE {
            // SAFETY: each fixed mapping replaces one CHUNK_BYTES slice of the
            // reservation made above with a shared view of the backing file.
            let at = unsafe {
                let addr = base.cast::<u8>().add(chunk * CHUNK_BYTES).cast();
                mmap(
                    addr,
                    CHUNK_BYTES,
                    PROT_READ | PROT_WRITE,
                    MAP_SHARED | MAP_FIXED,
                    file.as_raw_fd(),
                    0,
                )
            };
            assert_ne!(at as isize, -1, "map copy {chunk}");
        }
        Self {
            base: base.cast(),
            len,
            _file: file,
        }
    }

    /// Element 0 of the loop's array: the start of copy `BELOW`.
    fn y(&self) -> *mut f32 {
        // SAFETY: BELOW < BELOW + ABOVE copies were mapped.
        unsafe { self.base.add(BELOW * CHUNK_BYTES).cast() }
    }

    /// The `P` physical slots, through copy `BELOW`.
    fn slots(&mut self) -> &mut [f32] {
        // SAFETY: copy BELOW is a mapped, writable P-element view.
        unsafe { std::slice::from_raw_parts_mut(self.y(), P) }
    }
}

impl Drop for Aliased {
    fn drop(&mut self) {
        // SAFETY: `base..base+len` is the reservation made in `new`.
        unsafe { munmap(self.base.cast(), self.len) };
    }
}

/// The do-while above.
fn zext_bound_module() -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("aarch64_neon_fmap_zext_bound");
    let sig = mb.add_func_type(vec![Ty::Ptr, Ty::I64, Ty::I32], vec![]);
    let mut fb = mb.function(ENTRY, sig);
    let entry = fb.create_block();
    let y = fb.add_block_param(entry, Ty::Ptr);
    let start = fb.add_block_param(entry, Ty::I64);
    let n_param = fb.add_block_param(entry, Ty::I32);
    let head = fb.create_block();
    let i = fb.add_block_param(head, Ty::I64);
    let exit = fb.create_block();

    fb.switch_to_block(entry);
    let n = fb.zext(Ty::I32, Ty::I64, n_param);
    fb.br(head, vec![start]);

    fb.switch_to_block(head);
    let p = fb.gep(Ty::F32, y, vec![i]);
    let v = fb.load(Ty::F32, p);
    let one_f = fb.fconst(Ty::F32, 1.0);
    let bumped = fb.binop(BinOp::FAdd, Ty::F32, v, one_f);
    fb.store(Ty::F32, p, bumped);
    let one = fb.iconst(Ty::I64, 1);
    let next = fb.binop(BinOp::Add, Ty::I64, i, one);
    let done = fb.icmp(ICmpOp::Sge, Ty::I64, next, n);
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

type Kernel = extern "C" fn(*mut f32, i64, i32);

/// Non-negative bounds, where `zext(n) == sext(n)`: below, at and past the
/// start, across the vector widths.
const IN_RANGE: [(i64, i32); 6] = [(-17, 40), (0, 64), (3, 19), (5, 3), (0, 0), (-40, 0)];

/// The in-range cases are vectorized at O2 and O3 and exact at every level.
#[test]
fn a_zext_bound_in_i32_range_is_vectorized_and_exact() {
    const SPAN: usize = 128;
    let module = zext_bound_module();
    for opt_level in [OptLevel::O2, OptLevel::O3] {
        assert!(
            neon_fmap_changes(&module, opt_level) > 0,
            "{opt_level:?}: neon-fmap did not fire"
        );
    }
    let mut wrong = Vec::new();
    for opt_level in [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3] {
        let result = jit(&module, opt_level);
        // SAFETY: the trust-ir signature is (ptr, i64, i32) -> (), and
        // `result` outlives every call.
        let kernel = unsafe { result.buffer.get_fn_bound::<Kernel>(ENTRY) }.expect("entry symbol");
        for (start, n) in IN_RANGE {
            // The do-while runs its body once even at or past the bound.
            let trip = (i64::from(n) - start).max(1) as usize;
            assert!(trip <= SPAN, "case ({start}, {n}) leaves the span");
            let mut y: Vec<f32> = (0..SPAN).map(|x| x as f32 * 0.5).collect();
            let mut want = y.clone();
            for slot in want.iter_mut().take(trip) {
                *slot += 1.0;
            }
            // `base + i * 4` for `i` in `[start, start + trip)` is `y[0..trip)`.
            let base = y.as_mut_ptr().wrapping_offset(-(start as isize));
            kernel.as_ref()(base, start, n);
            if let Some(at) = (0..SPAN).find(|&at| y[at].to_bits() != want[at].to_bits()) {
                wrong.push(format!(
                    "{opt_level:?} start={start} n={n}: y[{}] = {} (want {})",
                    start + at as i64,
                    y[at],
                    want[at]
                ));
            }
        }
    }
    assert!(wrong.is_empty(), "\n  {}", wrong.join("\n  "));
}

/// A negative `n` bounds the scalar loop at `2^32 + n`. Every element of
/// `[START, 2^32 + N)` is updated once.
#[test]
fn a_negative_zext_bound_runs_to_its_unsigned_value() {
    let module = zext_bound_module();
    let hi = (1i64 << 32) + i64::from(N);
    let p = P as i64;
    // Elements of `[START, hi)` landing on slot `s`.
    let updates = |s: i64| (hi - 1 - s).div_euclid(p) - (START - 1 - s).div_euclid(p);
    let initial = |s: usize| (s % 1000) as f32;
    let mut memory = Aliased::new();
    let mut wrong = Vec::new();
    for opt_level in [OptLevel::O2, OptLevel::O3] {
        let result = jit(&module, opt_level);
        // SAFETY: the trust-ir signature is (ptr, i64, i32) -> (), and
        // `result` outlives the call.
        let kernel = unsafe { result.buffer.get_fn_bound::<Kernel>(ENTRY) }.expect("entry symbol");
        for (slot, value) in memory.slots().iter_mut().enumerate() {
            *value = initial(slot);
        }
        // `y[START..hi)` is mapped and writable.
        kernel.as_ref()(memory.y(), START, N);
        let slots = memory.slots();
        // Each update adds 1.0 to a small integer, so every count is exact.
        if let Some(slot) =
            (0..P).find(|&slot| slots[slot] != initial(slot) + updates(slot as i64) as f32)
        {
            wrong.push(format!(
                "{opt_level:?}: slot {slot} = {} (want {}, {} updates)",
                slots[slot],
                initial(slot) + updates(slot as i64) as f32,
                updates(slot as i64)
            ));
        }
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
