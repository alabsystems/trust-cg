// trust-cg-codegen - a reverse map over more than 2^31 elements
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Two descending maps over `i32` elements with an `i64` induction, which the
//! NEON map vectorizer (`neon_map`) lowers on its `.4S` path (MIXED), run
//! through the JIT at O2 and O3 with `n = 2^31 + 21`:
//!
//! * rotated: `i = n; do { a[i-1] += 5; i -= 1 } while i > 1`;
//! * native (top-tested): `i = n - 1; while i >= 0 { a[i] += 5; i -= 1 }`.
//!
//! An `i32` view of an induction past `2^31` is negative, so a vector block
//! addressed from it lands `2^32` elements below the scalar loop's. To run
//! that count cheaply, `a` is `2^31 + 21` elements of virtual memory backed by
//! one 48 MiB file mapped again and again: element `x` lives at physical slot
//! `x mod P` with `P = 3 * 2^22`, which does not divide `2^32`, so a block
//! displaced by `2^32` elements updates different slots than the scalar loop.
//! The region below `a` is mapped the same way, so a displaced block corrupts
//! slot counts instead of faulting. The case is a bounded execution on the
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

const ENTRY: &str = "reverse_bump";
/// The element count: past `i32::MAX`, with a 5-element scalar remainder.
const N: i64 = (1 << 31) + 21;
/// Elements per physical copy (48 MiB, a whole number of 16 KiB pages).
const P: usize = 3 << 22;
const CHUNK_BYTES: usize = P * 4;
/// Copies below `a`: enough to hold an index `2^32` below any index in `[0, N)`.
const BELOW: usize = (1usize << 33).div_ceil(CHUNK_BYTES) + 1;
/// Copies from `a` up: `[0, N)` plus one.
const ABOVE: usize = (N as usize * 4).div_ceil(CHUNK_BYTES) + 1;

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
    fn a(&self) -> *mut i32 {
        // SAFETY: BELOW < BELOW + ABOVE copies were mapped.
        unsafe { self.base.add(BELOW * CHUNK_BYTES).cast() }
    }

    /// The `P` physical slots, through copy `BELOW`.
    fn slots(&mut self) -> &mut [i32] {
        // SAFETY: copy BELOW is a mapped, writable P-element view.
        unsafe { std::slice::from_raw_parts_mut(self.a(), P) }
    }
}

impl Drop for Aliased {
    fn drop(&mut self) {
        // SAFETY: `base..base+len` is the reservation made in `new`.
        unsafe { munmap(self.base.cast(), self.len) };
    }
}

/// The rotated form: `i = n; do { a[i-1] += 5; i -= 1 } while i > 1`.
fn rotated_module() -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("aarch64_neon_map_reverse_wide_count");
    let sig = mb.add_func_type(vec![Ty::Ptr, Ty::I64], vec![]);
    let mut fb = mb.function(ENTRY, sig);
    let entry = fb.create_block();
    let a = fb.add_block_param(entry, Ty::Ptr);
    let n = fb.add_block_param(entry, Ty::I64);
    let head = fb.create_block();
    let i = fb.add_block_param(head, Ty::I64);
    let exit = fb.create_block();

    fb.switch_to_block(entry);
    fb.br(head, vec![n]);

    fb.switch_to_block(head);
    let one = fb.iconst(Ty::I64, 1);
    let index = fb.binop(BinOp::Sub, Ty::I64, i, one);
    let p = fb.gep(Ty::I32, a, vec![index]);
    let v = fb.load(Ty::I32, p);
    let five = fb.iconst(Ty::I32, 5);
    let bumped = fb.binop(BinOp::Add, Ty::I32, v, five);
    fb.store(Ty::I32, p, bumped);
    let more = fb.icmp(ICmpOp::Sgt, Ty::I64, i, one);
    fb.condbr(more, head, vec![index], exit, vec![]);

    fb.switch_to_block(exit);
    fb.ret(vec![]);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

/// The native form: `i = n - 1; while i >= 0 { a[i] += 5; i -= 1 }`.
fn native_module() -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("aarch64_neon_map_reverse_wide_count");
    let sig = mb.add_func_type(vec![Ty::Ptr, Ty::I64], vec![]);
    let mut fb = mb.function(ENTRY, sig);
    let entry = fb.create_block();
    let a = fb.add_block_param(entry, Ty::Ptr);
    let n = fb.add_block_param(entry, Ty::I64);
    let head = fb.create_block();
    let i = fb.add_block_param(head, Ty::I64);
    let body = fb.create_block();
    let exit = fb.create_block();

    fb.switch_to_block(entry);
    let one = fb.iconst(Ty::I64, 1);
    let top = fb.binop(BinOp::Sub, Ty::I64, n, one);
    fb.br(head, vec![top]);

    fb.switch_to_block(head);
    let zero = fb.iconst(Ty::I64, 0);
    let more = fb.icmp(ICmpOp::Sge, Ty::I64, i, zero);
    fb.condbr(more, body, vec![], exit, vec![]);

    fb.switch_to_block(body);
    let p = fb.gep(Ty::I32, a, vec![i]);
    let v = fb.load(Ty::I32, p);
    let five = fb.iconst(Ty::I32, 5);
    let bumped = fb.binop(BinOp::Add, Ty::I32, v, five);
    fb.store(Ty::I32, p, bumped);
    let step = fb.iconst(Ty::I64, 1);
    let next = fb.binop(BinOp::Sub, Ty::I64, i, step);
    fb.br(head, vec![next]);

    fb.switch_to_block(exit);
    fb.ret(vec![]);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

/// Changing runs of `neon-map` over `module` in the `opt_level` pipeline.
fn neon_map_changes(module: &trust_ir::Module, opt_level: OptLevel) -> u32 {
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
            .filter(|(name, _)| name == "neon-map")
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

/// Run `module` over `[0, N)` at O2 and O3 and return one line per level
/// that leaves a slot with the wrong number of updates.
fn wide_count_mismatches(label: &str, module: &trust_ir::Module) -> Vec<String> {
    let mut memory = Aliased::new();
    // Element x of [0, N) is slot x mod P: N = q*P + r.
    let (q, r) = (N as usize / P, N as usize % P);
    let initial = |slot: usize| (slot as i32).wrapping_mul(7);
    let mut wrong = Vec::new();
    for opt_level in [OptLevel::O2, OptLevel::O3] {
        assert!(
            neon_map_changes(module, opt_level) > 0,
            "{label} {opt_level:?}: neon-map did not fire"
        );
        let result = jit(module, opt_level);
        // SAFETY: the trust-ir signature is (ptr, i64) -> (), and `result`
        // outlives the call.
        let kernel = unsafe {
            result
                .buffer
                .get_fn_bound::<extern "C" fn(*mut i32, i64)>(ENTRY)
        }
        .expect("entry symbol");
        for (slot, value) in memory.slots().iter_mut().enumerate() {
            *value = initial(slot);
        }
        // `a[0..N)` and `2^33` bytes below `a` are mapped and writable.
        kernel.as_ref()(memory.a(), N);
        let slots = memory.slots();
        if let Some(slot) = (0..P).find(|&slot| {
            let updates = (q + usize::from(slot < r)) as i32;
            slots[slot] != initial(slot).wrapping_add(5 * updates)
        }) {
            let updates = (q + usize::from(slot < r)) as i32;
            wrong.push(format!(
                "{label} {opt_level:?}: slot {slot} = {} (want {}, {updates} updates)",
                slots[slot],
                initial(slot).wrapping_add(5 * updates)
            ));
        }
    }
    wrong
}

#[test]
fn a_reverse_map_past_i32_range_updates_every_element_once() {
    let wrong = wide_count_mismatches("rotated", &rotated_module());
    assert!(wrong.is_empty(), "\n  {}", wrong.join("\n  "));
}

/// The top-tested form indexes with `i` itself, not `i - 1`; the entry check
/// keeps it scalar for the same start range.
#[test]
fn a_native_reverse_map_past_i32_range_updates_every_element_once() {
    let wrong = wide_count_mismatches("native", &native_module());
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
