// trust-cg-codegen - rotated FP map loops entered at or past their bound
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! `i = 20; do { y[i] = y[i] * 2.0; i += 1 } while !(i >= n)` — a
//! bottom-tested FP map with no entry guard and a signed `>=` exit — run
//! through the JIT at every optimization level against a scalar Rust
//! reference, in the element and index widths the NEON FP map vectorizer
//! (`neon_fmap`) lowers:
//!
//! * `f32` and `f64` elements with an `i32` index and bound;
//! * `f32` and `f64` elements with an `i64` index and bound;
//! * mixed: `f32` elements, `i64` index, `i32` bound sign-extended to `i64`.
//!
//! The body runs once whatever `n` is, so an `n <= 20` still doubles `y[20]`.
//! The vector plan covers only the range `[20, n)`, so at or past the bound
//! the scalar do-while must run.
//!
//! The mixed shape also runs `y[i] = x[i] * 2.0` from an `i64` start
//! parameter below `i32::MIN`, with `Sge` and `Eq` exits and both bases inside
//! one large reservation. The vector code compares and addresses through the
//! low 32 bits of the induction, which from such a start read as a large
//! positive index, so that start must take the scalar do-while too. The cases
//! are bounded executions on the host, not a proof of the transform.
#![cfg(all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux")))]

use std::collections::HashMap;
use std::ffi::{c_int, c_void};

use trust_cg_codegen::compiler::{Compiler, CompilerConfig, JitCompilationResult};
use trust_cg_codegen::pipeline::{OptLevel, Pipeline, PipelineConfig};
use trust_cg_codegen::target::Target;
use trust_ir::{BinOp, ICmpOp, Ty};
use trust_ir_build::ModuleBuilder;

const LEVELS: [OptLevel; 4] = [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3];
const ENTRY: &str = "rotated_double";
/// The constant entry index.
const START: i64 = 20;
/// Elements of `y`; every case keeps `[START, max(n, START + 1))` inside it.
const LEN: usize = 160;
/// Bounds below, at, just past and well past the entry index.
const BOUNDS: [i64; 12] = [-5, 0, 1, 10, 20, 21, 22, 35, 36, 37, 100, 150];

/// The do-while above over `elem` elements with an `idx` index. The bound
/// parameter has type `bound`; when it is narrower than `idx` it is
/// sign-extended in the entry block.
fn rotated_module(elem: Ty, idx: Ty, bound: Ty) -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("aarch64_neon_fmap_rotated_entry");
    let sig = mb.add_func_type(vec![Ty::Ptr, bound.clone()], vec![]);
    let mut fb = mb.function(ENTRY, sig);
    let entry = fb.create_block();
    let y = fb.add_block_param(entry, Ty::Ptr);
    let n_param = fb.add_block_param(entry, bound.clone());
    let head = fb.create_block();
    let i = fb.add_block_param(head, idx.clone());
    let exit = fb.create_block();

    fb.switch_to_block(entry);
    let n = if bound == idx {
        n_param
    } else {
        fb.sext(bound, idx.clone(), n_param)
    };
    let start = fb.iconst(idx.clone(), i128::from(START));
    fb.br(head, vec![start]);

    fb.switch_to_block(head);
    let p = fb.gep(elem.clone(), y, vec![i]);
    let v = fb.load(elem.clone(), p);
    let two = fb.fconst(elem.clone(), 2.0);
    let doubled = fb.binop(BinOp::FMul, elem.clone(), v, two);
    fb.store(elem, p, doubled);
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

/// The element types the cases store, compared by bit pattern.
trait Float: Copy {
    fn of(value: i64) -> Self;
    fn doubled(self) -> Self;
    fn bits(self) -> u64;
}

impl Float for f32 {
    fn of(value: i64) -> Self {
        value as f32 * 0.75
    }
    fn doubled(self) -> Self {
        self * 2.0
    }
    fn bits(self) -> u64 {
        u64::from(self.to_bits())
    }
}

impl Float for f64 {
    fn of(value: i64) -> Self {
        value as f64 * 0.75
    }
    fn doubled(self) -> Self {
        self * 2.0
    }
    fn bits(self) -> u64 {
        self.to_bits()
    }
}

/// Run `module` at every level on every bound in [`BOUNDS`] and return one
/// line per wrong element. `N` is the bound parameter's type.
fn mismatches<T: Float, N>(module: &trust_ir::Module, bound: fn(i64) -> N) -> Vec<String> {
    let mut wrong = Vec::new();
    for opt_level in LEVELS {
        let result = jit(module, opt_level);
        // SAFETY: the trust-ir signature is (ptr, N) -> (), matching the
        // pointer and `N` arguments, and `result` outlives every call.
        let kernel = unsafe {
            result
                .buffer
                .get_fn_bound::<extern "C" fn(*mut T, N)>(ENTRY)
        }
        .expect("entry symbol");
        for n in BOUNDS {
            let mut y: Vec<T> = (0..LEN as i64).map(T::of).collect();
            let mut want = y.clone();
            let mut i = START;
            loop {
                want[i as usize] = want[i as usize].doubled();
                i += 1;
                if i >= n {
                    break;
                }
            }
            // `y` holds LEN elements and the scalar loop stores only
            // `[START, max(n, START + 1)) ⊆ [0, LEN)`.
            kernel.as_ref()(y.as_mut_ptr(), bound(n));
            if let Some(at) = (0..LEN).find(|&at| y[at].bits() != want[at].bits()) {
                wrong.push(format!(
                    "{opt_level:?} n={n}: y[{at}] bits {:#x} (want {:#x})",
                    y[at].bits(),
                    want[at].bits()
                ));
            }
        }
    }
    wrong
}

/// The cases below exercise the vector code: `neon-fmap` rewrites every
/// width's loop at O2 and O3.
#[test]
fn every_width_is_vectorized_at_o2_and_o3() {
    for (label, module) in [
        ("f32/i32", rotated_module(Ty::F32, Ty::I32, Ty::I32)),
        ("f64/i32", rotated_module(Ty::F64, Ty::I32, Ty::I32)),
        ("f32/i64", rotated_module(Ty::F32, Ty::I64, Ty::I64)),
        ("f64/i64", rotated_module(Ty::F64, Ty::I64, Ty::I64)),
        ("mixed", rotated_module(Ty::F32, Ty::I64, Ty::I32)),
    ] {
        for opt_level in [OptLevel::O2, OptLevel::O3] {
            assert!(
                neon_fmap_changes(&module, opt_level) > 0,
                "{label} {opt_level:?}: neon-fmap did not fire"
            );
        }
    }
}

#[test]
fn an_i32_indexed_rotated_fp_map_entered_at_its_bound_runs_its_one_iteration() {
    let mut wrong = Vec::new();
    for (label, elem) in [("f32", Ty::F32), ("f64", Ty::F64)] {
        let module = rotated_module(elem.clone(), Ty::I32, Ty::I32);
        let found = if elem == Ty::F32 {
            mismatches::<f32, i32>(&module, |n| n as i32)
        } else {
            mismatches::<f64, i32>(&module, |n| n as i32)
        };
        wrong.extend(found.into_iter().map(|line| format!("{label}: {line}")));
    }
    assert!(wrong.is_empty(), "\n  {}", wrong.join("\n  "));
}

#[test]
fn an_i64_indexed_rotated_fp_map_entered_at_its_bound_runs_its_one_iteration() {
    let mut wrong = Vec::new();
    for (label, elem) in [("f32", Ty::F32), ("f64", Ty::F64)] {
        let module = rotated_module(elem.clone(), Ty::I64, Ty::I64);
        let found = if elem == Ty::F32 {
            mismatches::<f32, i64>(&module, |n| n)
        } else {
            mismatches::<f64, i64>(&module, |n| n)
        };
        wrong.extend(found.into_iter().map(|line| format!("{label}: {line}")));
    }
    assert!(wrong.is_empty(), "\n  {}", wrong.join("\n  "));
}

#[test]
fn a_mixed_width_rotated_fp_map_entered_at_its_bound_runs_its_one_iteration() {
    let module = rotated_module(Ty::F32, Ty::I64, Ty::I32);
    let wrong = mismatches::<f32, i32>(&module, |n| n as i32);
    assert!(wrong.is_empty(), "\n  {}", wrong.join("\n  "));
}

// ---------------------------------------------------------------------------
// MIXED from an `i64` start below `i32` range, on interior bases
// ---------------------------------------------------------------------------

const START_ENTRY: &str = "rotated_double_from";
/// Bytes reserved for the cases: room for a base `2^31 + MARGIN` `f64`
/// elements above the span.
const RESERVE: usize = 18 << 30;
/// The readable and writable bytes at the start of the reservation, which
/// hold the span; the rest stays `PROT_NONE`.
const WRITABLE: usize = 1 << 20;
/// Elements at the start of the reservation that the cases read and write.
const SPAN: usize = 1024;
/// The span element holding `y[start]`.
const MARGIN: i64 = 256;
/// `x = y - d` elements: `x` is `y` itself, below it and above it.
const SHIFTS: [i64; 4] = [0, 64, -64, 200];

/// Start and bound pairs for the MIXED shape. The first five start below
/// `i32::MIN`, where the low 32 bits of the induction read as a large
/// positive index; the rest are in range and stay vectorized.
const MIXED_RANGES: [(i64, i32); 9] = [
    (-(1 << 31) - 100, i32::MIN),
    (-(1 << 31) - 5, i32::MIN + 30),
    (-(1 << 31) - 1, i32::MIN + 1),
    (-(1 << 31) - 17, i32::MIN + 100),
    (-(1 << 31) - 40, i32::MIN + 160),
    (-(1 << 31), i32::MIN + 100),
    (-17, 3),
    (0, 40),
    (20, 180),
];

const PROT_NONE: c_int = 0;
const PROT_READ: c_int = 1;
const PROT_WRITE: c_int = 2;
const MAP_PRIVATE: c_int = 0x2;
#[cfg(target_os = "macos")]
const MAP_ANON: c_int = 0x1000;
#[cfg(target_os = "linux")]
const MAP_ANON: c_int = 0x20;
#[cfg(target_os = "macos")]
const MAP_NORESERVE: c_int = 0x40;
#[cfg(target_os = "linux")]
const MAP_NORESERVE: c_int = 0x4000;

unsafe extern "C" {
    fn mmap(
        addr: *mut c_void,
        len: usize,
        prot: c_int,
        flags: c_int,
        fd: c_int,
        offset: i64,
    ) -> *mut c_void;
    fn mprotect(addr: *mut c_void, len: usize, prot: c_int) -> c_int;
    fn munmap(addr: *mut c_void, len: usize) -> c_int;
}

/// One `RESERVE`-byte anonymous mapping whose first `WRITABLE` bytes are
/// readable and writable.
struct Reservation {
    base: *mut u8,
}

impl Reservation {
    fn new() -> Self {
        // SAFETY: a fresh anonymous PROT_NONE reservation; nothing aliases it.
        let base = unsafe {
            mmap(
                std::ptr::null_mut(),
                RESERVE,
                PROT_NONE,
                MAP_PRIVATE | MAP_ANON | MAP_NORESERVE,
                -1,
                0,
            )
        };
        assert_ne!(base as isize, -1, "reserve {RESERVE} bytes");
        // SAFETY: the first WRITABLE bytes of the reservation made above.
        let made = unsafe { mprotect(base, WRITABLE, PROT_READ | PROT_WRITE) };
        assert_eq!(made, 0, "make {WRITABLE} bytes writable");
        Self { base: base.cast() }
    }

    /// The pointer `bytes` past the start of the reservation.
    fn at<T>(&self, bytes: i64) -> *mut T {
        let bytes = usize::try_from(bytes).expect("a base below the reservation");
        assert!(bytes < RESERVE, "a base past the reservation");
        // SAFETY: `bytes < RESERVE`, so the pointer stays inside the mapping.
        unsafe { self.base.add(bytes).cast() }
    }

    /// The `SPAN` elements at the start of the reservation.
    fn span<T>(&mut self) -> &mut [T] {
        assert!(SPAN * size_of::<T>() <= WRITABLE);
        // SAFETY: the first WRITABLE bytes are mapped readable and writable,
        // page-aligned, and borrowed only through `self`.
        unsafe { std::slice::from_raw_parts_mut(self.base.cast(), SPAN) }
    }
}

impl Drop for Reservation {
    fn drop(&mut self) {
        // SAFETY: `base..base+RESERVE` is the mapping made in `new`.
        unsafe { munmap(self.base.cast(), RESERVE) };
    }
}

/// `i = start; do { y[i] = x[i] * 2.0; i += 1 } while !(i OP n)` over `elem`
/// elements with an `i64` index, an `i64` start parameter and an `i32` bound
/// sign-extended to `i64`: `OP` is `Sge` or `Eq`.
fn mixed_from_module(elem: Ty, exit_op: ICmpOp) -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("aarch64_neon_fmap_rotated_entry_from");
    let sig = mb.add_func_type(vec![Ty::Ptr, Ty::Ptr, Ty::I64, Ty::I32], vec![]);
    let mut fb = mb.function(START_ENTRY, sig);
    let entry = fb.create_block();
    let y = fb.add_block_param(entry, Ty::Ptr);
    let x = fb.add_block_param(entry, Ty::Ptr);
    let start = fb.add_block_param(entry, Ty::I64);
    let n_param = fb.add_block_param(entry, Ty::I32);
    let head = fb.create_block();
    let i = fb.add_block_param(head, Ty::I64);
    let exit = fb.create_block();

    fb.switch_to_block(entry);
    let n = fb.sext(Ty::I32, Ty::I64, n_param);
    fb.br(head, vec![start]);

    fb.switch_to_block(head);
    let src = fb.gep(elem.clone(), x, vec![i]);
    let v = fb.load(elem.clone(), src);
    let two = fb.fconst(elem.clone(), 2.0);
    let doubled = fb.binop(BinOp::FMul, elem.clone(), v, two);
    let dst = fb.gep(elem.clone(), y, vec![i]);
    fb.store(elem, dst, doubled);
    let one = fb.iconst(Ty::I64, 1);
    let next = fb.binop(BinOp::Add, Ty::I64, i, one);
    let done = fb.icmp(exit_op, Ty::I64, next, n);
    fb.condbr(done, exit, vec![], head, vec![next]);

    fb.switch_to_block(exit);
    fb.ret(vec![]);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

/// Run `module` at every level over [`MIXED_RANGES`] and [`SHIFTS`] and
/// return one line per wrong run. `y[start]` is span element `MARGIN`, so
/// `y` lies `(MARGIN - start) * size` bytes into the reservation, and
/// `x = y - d` elements.
fn mixed_from_mismatches<T: Float>(label: &str, module: &trust_ir::Module) -> Vec<String> {
    let mut memory = Reservation::new();
    let size = size_of::<T>() as i64;
    let mut wrong = Vec::new();
    for opt_level in LEVELS {
        let result = jit(module, opt_level);
        // SAFETY: the trust-ir signature is (ptr, ptr, i64, i32) -> (), and
        // `result` outlives every call.
        let kernel = unsafe {
            result
                .buffer
                .get_fn_bound::<extern "C" fn(*mut T, *mut T, i64, i32)>(START_ENTRY)
        }
        .expect("entry symbol");
        for (start, n) in MIXED_RANGES {
            let trip = i64::from(n) - start;
            for d in SHIFTS {
                // Both exits run exactly `[start, n)` from a start below `n`;
                // `y[i]` is span element `MARGIN + i - start`, `x[i]` is `y[i - d]`.
                assert!(
                    trip > 0 && MARGIN - d >= 0 && MARGIN + trip - d.min(0) <= SPAN as i64,
                    "case ({start}, {n}, {d}) leaves the span"
                );
                let slot = |i: i64| (MARGIN + i - start) as usize;
                let span = memory.span::<T>();
                for (k, v) in span.iter_mut().enumerate() {
                    *v = T::of(k as i64);
                }
                let mut want = span.to_vec();
                for i in start..i64::from(n) {
                    want[slot(i)] = want[slot(i - d)].doubled();
                }
                let y = memory.at::<T>((MARGIN - start) * size);
                let x = memory.at::<T>((MARGIN - start - d) * size);
                kernel.as_ref()(y, x, start, n);
                let span = memory.span::<T>();
                if let Some(at) = (0..SPAN).find(|&at| span[at].bits() != want[at].bits()) {
                    wrong.push(format!(
                        "{label} {opt_level:?} start={start} n={n} d={d}: y[{}] bits {:#x} (want {:#x})",
                        start + at as i64 - MARGIN,
                        span[at].bits(),
                        want[at].bits()
                    ));
                }
            }
        }
    }
    wrong
}

/// The MIXED shape with a start parameter is vectorized at O2 and O3, so the
/// in-range cases whose runtime alias check passes run the vector code.
#[test]
fn a_mixed_width_rotated_fp_map_from_a_start_parameter_is_vectorized() {
    for (label, elem) in [("f32", Ty::F32), ("f64", Ty::F64)] {
        for exit_op in [ICmpOp::Sge, ICmpOp::Eq] {
            let module = mixed_from_module(elem.clone(), exit_op);
            for opt_level in [OptLevel::O2, OptLevel::O3] {
                assert!(
                    neon_fmap_changes(&module, opt_level) > 0,
                    "{label} {exit_op:?} {opt_level:?}: neon-fmap did not fire"
                );
            }
        }
    }
}

/// An `i64` start below `i32::MIN` with the bound in range runs every
/// iteration of `[start, n)`. The vector code reads the induction through its
/// low 32 bits, which from such a start read as a large positive index, so
/// the start must take the scalar do-while.
///
/// The bases are interior. Indexed from a start near `-2^31`, a base lies
/// more than 8 GiB (`f32`) or 16 GiB (`f64`) above the elements the loop
/// touches, so the cases reserve one 18 GiB mapping, keep those elements in
/// its first MiB and put both bases inside it: every base and every address
/// `base + i * size` the loop forms lies inside that one allocation. A base
/// derived from a short buffer would lie gigabytes past the buffer's end,
/// and the loop would reach the buffer only by pointer arithmetic outside
/// any allocation. trust-ir's GEP takes no negative index from any base (its
/// reference interpreter raises UB on one), so each run exercises the lowered
/// machine loop, which addresses `base + iv * size` with a signed `iv`, not a
/// UB-free trust-ir execution.
#[test]
fn a_mixed_width_rotated_fp_map_from_below_i32_range_runs_every_iteration() {
    let mut wrong = Vec::new();
    for exit_op in [ICmpOp::Sge, ICmpOp::Eq] {
        let f32_module = mixed_from_module(Ty::F32, exit_op);
        wrong.extend(mixed_from_mismatches::<f32>(
            &format!("f32 {exit_op:?}"),
            &f32_module,
        ));
        let f64_module = mixed_from_module(Ty::F64, exit_op);
        wrong.extend(mixed_from_mismatches::<f64>(
            &format!("f64 {exit_op:?}"),
            &f64_module,
        ));
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
