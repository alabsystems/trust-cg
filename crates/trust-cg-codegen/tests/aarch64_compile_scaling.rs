// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Compile cost grows linearly with module size (ledger row L14-P6).
//!
//! `benchmarks/beat-llvm/scale_gate.py` measured the Darwin arm64 bridge at
//! 12x LLVM's compile time and 25x its peak RSS on a 2,400-function crate,
//! with compile time growing 8.6x and memory 10x when the crate tripled. The
//! crate's `main` is one basic block of 2,400 calls. Two backend loops were
//! quadratic in that block's call count:
//!
//! * the pre-RA scheduler materialized an edge from every instruction to
//!   every later call and from every call to every later instruction, so one
//!   block held `O(calls * instructions)` edges (`trust-cg-opt` scheduler,
//!   `build_scheduling_dag_for_insts`);
//! * register allocation asked every live interval about every call site
//!   (`find_call_crossings_in`, the linear-scan reservation checks and the
//!   validator's physical-register interference check).
//!
//! The emitted objects are byte-identical before and after those fixes.
//!
//! This target keeps the growth linear. It compiles generated trust-ir modules
//! at 1x, 4x and 16x size through the production AOT compiler (-O3,
//! `aarch64-apple-darwin`, proofs off, serial preparation) and bounds the
//! growth of deterministic or load-robust metrics: heap bytes allocated, heap
//! allocations and peak live heap bytes (a counting global allocator), plus
//! instructions retired on macOS (`proc_pid_rusage`). Wall time is never
//! asserted. Each 4x step may grow a metric by at most [`MAX_STEP_RATIO`]; a
//! quadratic term makes that step approach 16x. The native test links the
//! call-heavy module against a C reference and compares results.
//!
//! This is a regression test of cost growth, not a proof of a complexity
//! bound: it covers the module shapes below at these sizes. Instructions
//! retired are read on macOS only, so on other hosts the register-allocation
//! scans are guarded by the unit tests below, not by this target.
//!
//! The target runs in the test (debug) profile, so a debug-only check that
//! re-derives function-wide state after every mutation fails it too: the
//! provenance reverse-index check did (14.5x, then 15.6x allocated bytes per
//! 4x step on the call block) until it moved to an amortized schedule.
//!
//! Two probes follow the second L14-P6 round (the stack-tuple block and the
//! compile-scaling `loops` shape), each with the bound it can hold today:
//!
//! * the stack-tuple block is probed only in its spilled regime (640 to
//!   2,560 pairs, `-O1`); below that the step into spilling is not linear.
//!   Its x5 step bound alone would also pass the linear scan's replaced
//!   holdings search (x4.98), so on macOS it also has instructions-retired
//!   ceilings ([`STACK_TUPLE_MAX_INSTRUCTIONS`]) that search exceeds; on
//!   every host the holdings are bounded in `trust-cg-regalloc`
//!   (`blocked_allocation_cost_grows_linearly`);
//! * the fill-loop chain (4, 16, 64 loops) keeps its heap metrics within x5
//!   and its instructions within [`FILL_LOOP_CHAIN_INSTRUCTION_STEP`]: the
//!   loop-latch-layout driver and the allocation validator's value-flow still
//!   grow faster than the loop count (LIMITATIONS.md names them).
//!
//! A third bounds the fixed cost of the smallest compile.
//!
//! Each fix is also
//! guarded in its own crate, on every host, by a differential against
//! the scan it replaced and by a deterministic work-count bound over the same
//! 1x/4x/16x steps. Forcing the replaced scan fails the bound:
//!
//! * scheduler memory-order and call edges:
//!   `scheduling_dag_of_a_store_block_is_linear`,
//!   `scheduling_dag_of_a_call_chain_is_linear` (`trust-cg-opt`);
//! * frame-index scratch liveness: `scratch_liveness_cost_grows_linearly`
//!   (`trust-cg-codegen` lib);
//! * call crossings, reservation checks, the validator's interference check,
//!   spill-slot coloring and post-RA reload elimination: the
//!   `*_cost_grows_linearly` tests over `trust-cg-regalloc`'s `scan_work`
//!   counters. The counters charge the primitive probes of the replaced scans
//!   (`is_live_at`, `overlaps`, the forward def scan and the per-position
//!   rewrite loop), so a caller routed back through them is counted too.
//!   Reload elimination's `retain` over the active slots has no fallback left
//!   to charge; its differential checks results only;
//! * the linear scan's active holdings: `blocked_allocation_cost_grows_linearly`
//!   and `indexed_linear_scan_matches_the_reference_allocator`
//!   (`trust-cg-regalloc`);
//! * the per-loop whole-function scans removed from neon-fill, LICM,
//!   loop-unswitch and post-RA coalescing have differentials against the
//!   scans they replaced (`trust-cg-opt`, `trust-cg-regalloc`); their growth is
//!   bounded here, by the fill-loop chain;
//! * the loop-state contract's liveness walks, which a recognition sweep ran
//!   once per loop over the rest of the function:
//!   `liveness_work_of_a_recognition_sweep_grows_linearly` and the
//!   `an_amortized_index_answers_what_the_walks_answer*` differentials
//!   (`trust-cg-opt`, L14-P6, 2026-10-01).

#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
#[path = "common/aarch64_native.rs"]
mod native;

use std::alloc::{GlobalAlloc, Layout, System};
use std::fmt::Write as _;
use std::sync::Mutex;
use std::sync::atomic::{AtomicI64, AtomicU64, Ordering};

use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::target::TargetSpec;
use trust_cg_codegen::{Compiler, CompilerConfig};

/// The largest growth of any metric across one 4x size step. Linear growth
/// with a fixed per-compile cost stays at or below 4x; a quadratic term drives
/// the step toward 16x.
const MAX_STEP_RATIO: f64 = 5.0;

// ---------------------------------------------------------------------------
// Counting allocator
// ---------------------------------------------------------------------------

struct CountingAllocator;

static ALLOCATIONS: AtomicU64 = AtomicU64::new(0);
static ALLOCATED_BYTES: AtomicU64 = AtomicU64::new(0);
static LIVE_BYTES: AtomicI64 = AtomicI64::new(0);
static PEAK_LIVE_BYTES: AtomicI64 = AtomicI64::new(0);

fn note_allocation(size: usize) {
    ALLOCATIONS.fetch_add(1, Ordering::Relaxed);
    ALLOCATED_BYTES.fetch_add(size as u64, Ordering::Relaxed);
    let live = LIVE_BYTES.fetch_add(size as i64, Ordering::Relaxed) + size as i64;
    PEAK_LIVE_BYTES.fetch_max(live, Ordering::Relaxed);
}

// SAFETY: every method forwards to `System` with the caller's arguments
// unchanged and only updates counters.
unsafe impl GlobalAlloc for CountingAllocator {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        // SAFETY: forwarded unchanged under the caller's `alloc` contract.
        let ptr = unsafe { System.alloc(layout) };
        if !ptr.is_null() {
            note_allocation(layout.size());
        }
        ptr
    }

    unsafe fn alloc_zeroed(&self, layout: Layout) -> *mut u8 {
        // SAFETY: forwarded unchanged under the caller's `alloc_zeroed` contract.
        let ptr = unsafe { System.alloc_zeroed(layout) };
        if !ptr.is_null() {
            note_allocation(layout.size());
        }
        ptr
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        // SAFETY: forwarded unchanged under the caller's `dealloc` contract.
        unsafe { System.dealloc(ptr, layout) };
        LIVE_BYTES.fetch_sub(layout.size() as i64, Ordering::Relaxed);
    }

    unsafe fn realloc(&self, ptr: *mut u8, layout: Layout, new_size: usize) -> *mut u8 {
        // SAFETY: forwarded unchanged under the caller's `realloc` contract.
        let new_ptr = unsafe { System.realloc(ptr, layout, new_size) };
        if !new_ptr.is_null() {
            LIVE_BYTES.fetch_sub(layout.size() as i64, Ordering::Relaxed);
            note_allocation(new_size);
        }
        new_ptr
    }
}

#[global_allocator]
static GLOBAL: CountingAllocator = CountingAllocator;

/// The counters are process-wide, so every test in this binary runs under
/// this lock and the measured compile is the only work in flight.
static SERIAL: Mutex<()> = Mutex::new(());

// ---------------------------------------------------------------------------
// Instructions retired (macOS)
// ---------------------------------------------------------------------------

#[cfg(target_os = "macos")]
mod instructions {
    /// `struct rusage_info_v4` from `<sys/resource.h>` as 37 `u64` words: the
    /// 16-byte `ri_uuid` (words 0-1), 29 counters from `ri_user_time` to
    /// `ri_lifetime_max_phys_footprint` (words 2-30), `ri_instructions`
    /// (word 31), then `ri_cycles` to `ri_runnable_time` (words 32-36).
    #[repr(C)]
    struct RusageInfoV4([u64; 37]);

    const RI_INSTRUCTIONS: usize = 31;
    const RUSAGE_INFO_V4: i32 = 4;

    unsafe extern "C" {
        fn proc_pid_rusage(pid: i32, flavor: i32, buffer: *mut RusageInfoV4) -> i32;
    }

    /// Instructions this process has retired, or `None` if the kernel does not
    /// report them.
    pub fn retired() -> Option<u64> {
        let mut info = RusageInfoV4([0; 37]);
        let pid = i32::try_from(std::process::id()).ok()?;
        // SAFETY: `info` is a writable `rusage_info_v4`, the flavor requested.
        let status = unsafe { proc_pid_rusage(pid, RUSAGE_INFO_V4, &mut info) };
        let instructions = info.0[RI_INSTRUCTIONS];
        (status == 0 && instructions != 0).then_some(instructions)
    }
}

#[cfg(not(target_os = "macos"))]
mod instructions {
    pub fn retired() -> Option<u64> {
        None
    }
}

// ---------------------------------------------------------------------------
// Generated modules
// ---------------------------------------------------------------------------

/// `f{i}(a, b)`: the scale_gate function body, a 64-iteration loop over
/// mul/xor/shift/rotate with a branch. The rotate amount stays in `1..=62`.
fn loop_function(i: u64) -> String {
    let seed = (i * 2_654_435_761) % (1 << 32);
    let k = 1 + i % 62;
    format!(
        "fn @f{i}(functy.0) {{
bb0(%0: u64, %1: u64):
    %2 = const u64 {seed}
    %3 = xor u64 %0, %2
    %4 = const u64 0
    br bb1(%0, %3, %4)
bb1(%5: u64, %6: u64, %7: u64):
    %8 = const u64 64
    %9 = icmp ult u64 %7, %8
    condbr %9, bb2, bb6(%6)
bb2:
    %10 = const u64 6364136223846793005
    %11 = mul u64 %6, %10
    %12 = xor u64 %7, %1
    %13 = add u64 %11, %12
    %14 = const u64 29
    %15 = lshr u64 %13, %14
    %16 = xor u64 %13, %15
    %17 = const u64 7
    %18 = urem u64 %16, %17
    %19 = const u64 0
    %20 = icmp eq u64 %18, %19
    condbr %20, bb3, bb4
bb3:
    %21 = add u64 %16, %5
    br bb5(%21)
bb4:
    %22 = xor u64 %16, %7
    br bb5(%22)
bb5(%23: u64):
    %24 = const u64 {k}
    %25 = shl u64 %5, %24
    %26 = const u64 {}
    %27 = lshr u64 %5, %26
    %28 = or u64 %25, %27
    %29 = const u64 1
    %30 = add u64 %7, %29
    br bb1(%28, %23, %30)
bb6(%31: u64):
    ret %31
}}
",
        64 - k
    )
}

/// `entry(s)`: ONE basic block calling functions `0..calls` in order as
/// `f(s, i)` and xoring the results, the shape of scale_gate's `main`.
fn call_block_entry(calls: usize) -> String {
    let mut text = String::from("fn @entry(functy.1) {\nbb0(%0: u64):\n");
    let mut next = 1usize;
    let mut accumulator = None;
    for callee in 0..calls {
        let index = next;
        let result = next + 1;
        next += 2;
        writeln!(text, "    %{index} = const u64 {callee}").unwrap();
        writeln!(text, "    %{result} = call @func.{callee}(%0, %{index})").unwrap();
        accumulator = Some(match accumulator {
            None => result,
            Some(previous) => {
                writeln!(text, "    %{next} = xor u64 %{previous}, %{result}").unwrap();
                next += 1;
                next - 1
            }
        });
    }
    writeln!(text, "    ret %{}\n}}", accumulator.unwrap_or(0)).unwrap();
    text
}

const HEADER: &str = "; TrustIr text format v1
module \"compile_scaling\"

functy.0 = (u64, u64) -> (u64)

functy.1 = (u64) -> (u64)

";

/// `functions` scale_gate loop functions and the entry block calling each.
fn loop_functions_module(functions: usize) -> String {
    let mut text = String::from(HEADER);
    for i in 0..functions {
        text.push_str(&loop_function(i as u64));
        text.push('\n');
    }
    text.push_str(&call_block_entry(functions));
    text
}

/// One entry block of `calls` calls to distinct bodyless external
/// declarations: the call-block cost with no per-callee compile.
fn external_calls_module(calls: usize) -> String {
    let mut text = String::from(HEADER);
    for i in 0..calls {
        writeln!(text, "fn @ext{i}(functy.0) {{\n}}\n").unwrap();
    }
    text.push_str(&call_block_entry(calls));
    text
}

/// `entry(p, s)`: `loops` sequential byte fills through the pointer argument.
/// Loop `k` stores a constant into bytes `[64k, 64k + 64)` of `p`, then one
/// byte is read back and xored into an accumulator, so only `p` and the
/// accumulator live from one loop to the next. The fills are the `neon-fill`
/// shape; the constants and the bounds are LICM candidates; each loop is
/// offered to loop unswitching; the loop-carried copies reach post-RA
/// coalescing.
fn fill_loop_chain_module(loops: usize) -> String {
    let mut text = String::from(
        "; TrustIr text format v1
module \"fill_chain\"

functy.0 = (ptr, u64) -> (u64)

fn @entry(functy.0) {
bb0(%0: ptr, %1: u64):
",
    );
    let mut v = 2usize;
    let mut accumulator = 1usize;
    let mut block = 1usize;
    for k in 0..loops {
        let (header, body, exit) = (block, block + 1, block + 2);
        block += 3;
        let (offset, base, zero) = (v, v + 1, v + 2);
        v += 3;
        writeln!(text, "    %{offset} = const i64 {}", 64 * k).unwrap();
        writeln!(text, "    %{base} = gep i8, ptr %0, %{offset}").unwrap();
        writeln!(text, "    %{zero} = const u64 0").unwrap();
        writeln!(text, "    br bb{header}(%{zero})").unwrap();
        let (i, limit, compare) = (v, v + 1, v + 2);
        v += 3;
        writeln!(text, "bb{header}(%{i}: u64):").unwrap();
        writeln!(text, "    %{limit} = const u64 64").unwrap();
        writeln!(text, "    %{compare} = icmp ult u64 %{i}, %{limit}").unwrap();
        writeln!(text, "    condbr %{compare}, bb{body}, bb{exit}").unwrap();
        let (address, value, one, next) = (v, v + 1, v + 2, v + 3);
        v += 4;
        writeln!(text, "bb{body}:").unwrap();
        writeln!(text, "    %{address} = gep i8, ptr %{base}, %{i}").unwrap();
        writeln!(text, "    %{value} = const u8 {}", (k * 37) % 251 + 1).unwrap();
        writeln!(text, "    store u8 %{value}, ptr %{address}").unwrap();
        writeln!(text, "    %{one} = const u64 1").unwrap();
        writeln!(text, "    %{next} = add u64 %{i}, %{one}").unwrap();
        writeln!(text, "    br bb{header}(%{next})").unwrap();
        let (read, byte, wide, folded) = (v, v + 1, v + 2, v + 3);
        v += 4;
        writeln!(text, "bb{exit}:").unwrap();
        writeln!(text, "    %{read} = gep i8, ptr %{base}, %{zero}").unwrap();
        writeln!(text, "    %{byte} = load u8, ptr %{read}").unwrap();
        writeln!(text, "    %{wide} = zext u8 %{byte} to u64").unwrap();
        writeln!(text, "    %{folded} = xor u64 %{accumulator}, %{wide}").unwrap();
        accumulator = folded;
    }
    writeln!(text, "    ret %{accumulator}\n}}").unwrap();
    text
}

/// SROA promotes a stack tuple of at most this many fields to registers; the
/// stack-tuple probe keeps its tuple above it at every size.
const STACK_TUPLE_MIN_FIELDS: usize = 600;

/// `entry(s)`: ONE basic block of `pairs` store/load pairs through a stack
/// tuple of `max(pairs, STACK_TUPLE_MIN_FIELDS)` u64 fields, threading an
/// accumulator through every pair: the L14-P6 stack-tuple block, whose
/// constants the scheduler lifts and register allocation spills.
fn stack_tuple_block_module(pairs: usize) -> String {
    let fields = pairs.max(STACK_TUPLE_MIN_FIELDS);
    let mut text = String::from(
        "; TrustIr text format v1
module \"stack_tuple\"

functy.0 = (u64) -> (u64)

fn @entry(functy.0) {
bb0(%0: u64):
",
    );
    writeln!(
        text,
        "    %1 = alloca ({}), align 8",
        vec!["u64"; fields].join(", ")
    )
    .unwrap();
    let mut accumulator = 0usize;
    let mut v = 2usize;
    for i in 0..pairs {
        writeln!(text, "    %{v} = const i64 {}", 8 * i).unwrap();
        writeln!(text, "    %{} = gep i8, ptr %1, %{v}", v + 1).unwrap();
        writeln!(text, "    %{} = const u64 {}", v + 2, i + 1).unwrap();
        writeln!(text, "    %{} = xor u64 %{accumulator}, %{}", v + 3, v + 2).unwrap();
        writeln!(text, "    store u64 %{}, ptr %{}", v + 3, v + 1).unwrap();
        writeln!(text, "    %{} = load u64, ptr %{}", v + 4, v + 1).unwrap();
        writeln!(text, "    %{} = add u64 %{accumulator}, %{}", v + 5, v + 4).unwrap();
        accumulator = v + 5;
        v += 6;
    }
    writeln!(text, "    ret %{accumulator}\n}}").unwrap();
    text
}

/// The smallest compile: one function returning its argument.
fn trivial_module() -> String {
    String::from(
        "; TrustIr text format v1
module \"trivial\"

functy.0 = (u64) -> (u64)

fn @entry(functy.0) {
bb0(%0: u64):
    ret %0
}
",
    )
}

fn parse(text: &str) -> trust_ir::Module {
    let mut module = trust_ir::parser::parse_module(text).expect("generated module parses");
    module.target_info = Some(trust_ir::TargetInfo {
        triple: "aarch64-apple-darwin".into(),
        pointer_size: 8,
        endianness: trust_ir::Endianness::Little,
        abi: Some("aapcs64".into()),
        struct_passing: trust_ir::StructPassingPolicy::NativeC,
    });
    module
}

// ---------------------------------------------------------------------------
// Measurement
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, Copy)]
struct Cost {
    allocated_bytes: u64,
    allocations: u64,
    peak_live_bytes: u64,
    instructions: Option<u64>,
}

fn compiler(opt_level: OptLevel) -> Compiler {
    Compiler::new_for_target_spec(
        CompilerConfig {
            opt_level,
            parallel: false,
            ..CompilerConfig::default()
        },
        TargetSpec::parse("aarch64-apple-darwin").expect("Darwin arm64 target"),
    )
    .with_codegen_license(permit_unlicensed())
}

/// Compile `module` once at `-O3` and return what the compile cost.
fn measure(module: &trust_ir::Module) -> Cost {
    measure_at(module, OptLevel::O3)
}

/// Compile `module` once at `opt_level` and return what the compile cost.
fn measure_at(module: &trust_ir::Module, opt_level: OptLevel) -> Cost {
    let compiler = compiler(opt_level);
    let allocations = ALLOCATIONS.load(Ordering::Relaxed);
    let allocated = ALLOCATED_BYTES.load(Ordering::Relaxed);
    let live = LIVE_BYTES.load(Ordering::Relaxed);
    PEAK_LIVE_BYTES.store(live, Ordering::Relaxed);
    let instructions = instructions::retired();
    let result = compiler.compile(module).expect("generated module compiles");
    let instructions_after = instructions::retired();
    let cost = Cost {
        allocated_bytes: ALLOCATED_BYTES.load(Ordering::Relaxed) - allocated,
        allocations: ALLOCATIONS.load(Ordering::Relaxed) - allocations,
        peak_live_bytes: (PEAK_LIVE_BYTES.load(Ordering::Relaxed) - live).max(0) as u64,
        instructions: instructions.zip(instructions_after).map(|(a, b)| b - a),
    };
    assert!(!result.object_code.is_empty());
    assert_eq!(
        &result.object_code[..4],
        &[0xcf, 0xfa, 0xed, 0xfe],
        "Mach-O 64"
    );
    cost
}

/// The largest growth per 4x step a probe allows: for the three heap metrics
/// and for instructions retired (macOS).
#[derive(Clone, Copy)]
struct StepLimits {
    memory: f64,
    instructions: f64,
}

/// The default: every metric within [`MAX_STEP_RATIO`].
const LINEAR: StepLimits = StepLimits {
    memory: MAX_STEP_RATIO,
    instructions: MAX_STEP_RATIO,
};

/// Measure `generate` at `base`, `4 * base` and `16 * base` units and bound
/// the growth of every metric across each 4x step.
fn assert_linear_growth(probe: &str, base: usize, generate: fn(usize) -> String) {
    assert_growth(
        probe,
        &[base, 4 * base, 16 * base],
        generate,
        OptLevel::O3,
        LINEAR,
    );
}

/// Measure `generate` at each of `sizes` (each 4x the one before) at
/// `opt_level`, bound the growth of every metric across each step, and
/// return what each size cost.
fn assert_growth(
    probe: &str,
    sizes: &[usize],
    generate: fn(usize) -> String,
    opt_level: OptLevel,
    limits: StepLimits,
) -> Vec<Cost> {
    // One warm-up compile pays every process-lifetime cost (lazy tables,
    // thread-local caches) outside the measured steps.
    measure_at(&parse(&generate(sizes[0])), opt_level);
    let costs: Vec<Cost> = sizes
        .iter()
        .map(|&size| measure_at(&parse(&generate(size)), opt_level))
        .collect();
    for (size, cost) in sizes.iter().zip(&costs) {
        eprintln!("{probe} size={size}: {cost:?}");
    }
    for step in 0..sizes.len() - 1 {
        assert_eq!(sizes[step + 1], 4 * sizes[step], "{probe}: steps are 4x");
        let (small, large) = (&costs[step], &costs[step + 1]);
        let ratios = [
            (
                "allocated bytes",
                large.allocated_bytes,
                small.allocated_bytes,
                limits.memory,
            ),
            (
                "allocations",
                large.allocations,
                small.allocations,
                limits.memory,
            ),
            (
                "peak live bytes",
                large.peak_live_bytes,
                small.peak_live_bytes,
                limits.memory,
            ),
        ]
        .into_iter()
        .chain(
            large
                .instructions
                .zip(small.instructions)
                .map(|(large, small)| ("instructions retired", large, small, limits.instructions)),
        );
        for (metric, large_value, small_value, limit) in ratios {
            assert!(
                small_value > 0,
                "{probe}: no {metric} measured at size {}",
                sizes[step]
            );
            let ratio = large_value as f64 / small_value as f64;
            eprintln!(
                "{probe} {}->{}: {metric} x{ratio:.2}",
                sizes[step],
                sizes[step + 1]
            );
            assert!(
                ratio <= limit,
                "{probe}: {metric} grew x{ratio:.2} from size {} to {} ({small_value} -> \
                 {large_value}); a 4x larger module may cost at most x{limit}",
                sizes[step],
                sizes[step + 1]
            );
        }
    }
    costs
}

#[test]
fn call_block_compile_cost_grows_linearly() {
    let _serial = SERIAL.lock().unwrap_or_else(|poison| poison.into_inner());
    assert_linear_growth("external-call block", 128, external_calls_module);
}

#[test]
fn function_count_compile_cost_grows_linearly() {
    let _serial = SERIAL.lock().unwrap_or_else(|poison| poison.into_inner());
    assert_linear_growth("loop functions + call block", 8, loop_functions_module);
}

/// Instructions-retired ceilings of the stack-tuple probe (macOS, test
/// profile), by pair count. Its growth bound does not by itself separate the
/// linear scan's indexed holdings from the scan they replaced: across the
/// probe's step the replaced scan also stayed inside x5 (x4.98). It did cost
/// 13.93 G and 69.40 G instructions at 640 and 2,560 pairs, against 7.88 G
/// and 38.53 G with the holdings (2026-09-29, Trust 9192). A ceiling about
/// 1.35x above today's count fails the replaced scan, which is about 1.8x
/// above it. These are regression ceilings for this build profile, not a
/// complexity bound; a toolchain or pipeline change that moves them moves
/// them with a measurement.
const STACK_TUPLE_MAX_INSTRUCTIONS: [(usize, u64); 2] =
    [(640, 10_500_000_000), (2_560, 52_000_000_000)];

/// The L14-P6 stack-tuple block in its spilled regime (a tuple above the
/// SROA limit, 640 and 2,560 store/load pairs, `-O1`). Below about 640 pairs
/// the block leaves registers free and the step into spilling is not
/// linear, so the probe starts there. Every metric stays within x5 per step,
/// and on macOS instructions retired stay under
/// [`STACK_TUPLE_MAX_INSTRUCTIONS`], which is what fails the linear scan's
/// replaced holdings search here. `trust-cg-regalloc`'s
/// `blocked_allocation_cost_grows_linearly` bounds that search's work units
/// on every host.
#[test]
fn stack_tuple_block_compile_cost_grows_linearly() {
    let _serial = SERIAL.lock().unwrap_or_else(|poison| poison.into_inner());
    let sizes: Vec<usize> = STACK_TUPLE_MAX_INSTRUCTIONS
        .iter()
        .map(|&(pairs, _)| pairs)
        .collect();
    let costs = assert_growth(
        "stack-tuple block",
        &sizes,
        stack_tuple_block_module,
        OptLevel::O1,
        LINEAR,
    );
    for (&(pairs, ceiling), cost) in STACK_TUPLE_MAX_INSTRUCTIONS.iter().zip(&costs) {
        if let Some(instructions) = cost.instructions {
            assert!(
                instructions <= ceiling,
                "stack-tuple block, {pairs} pairs: {instructions} instructions retired, above \
                 the ceiling of {ceiling}"
            );
        }
    }
}

/// The instruction-growth ceiling of the fill-loop chain. Its heap metrics
/// stay within [`MAX_STEP_RATIO`], but its CPU keeps a superlinear term (the
/// loop-latch-layout driver re-derives every analysis after each rewritten
/// loop, and the allocation validator's value-flow grows with the values live
/// across loops): x5.05 from 16 to 64 loops (2026-10-01). Before L14-P6's
/// neon-fill, LICM, loop-unswitch and post-RA coalescing changes the same step
/// read x6.46 instructions and x7.46 allocated bytes, and x5.22 after them;
/// with neon-fill's loop-state checks walking the function once per loop
/// again (the shared index disabled) it reads x5.32. That term is bounded
/// exactly, on every host, by trust-cg-opt's
/// `liveness_work_of_a_recognition_sweep_grows_linearly` (x15.7 per step
/// without the index).
const FILL_LOOP_CHAIN_INSTRUCTION_STEP: f64 = 5.5;

/// A function of 4, 16 and 64 sequential byte-fill loops (the compile-scaling
/// `loops` shape reduced to trust-ir): heap metrics within x5 per 4x step,
/// instructions within [`FILL_LOOP_CHAIN_INSTRUCTION_STEP`].
#[test]
fn fill_loop_chain_compile_cost_grows_linearly() {
    let _serial = SERIAL.lock().unwrap_or_else(|poison| poison.into_inner());
    assert_growth(
        "fill-loop chain",
        &[4, 16, 64],
        fill_loop_chain_module,
        OptLevel::O3,
        StepLimits {
            memory: MAX_STEP_RATIO,
            instructions: FILL_LOOP_CHAIN_INSTRUCTION_STEP,
        },
    );
}

/// The fixed-cost budget of the smallest compile (one function returning its
/// argument, `-O3`, after a warm-up compile): heap allocations, bytes
/// allocated and, on macOS, instructions retired. Measured at L14-P6: 1,391
/// allocations, 163,266 bytes and 5.5 M instructions in the test profile. A
/// budget about 1.5x (2x for instructions) above that catches per-compile
/// set-up work that grows with nothing the module contains.
const TRIVIAL_COMPILE_MAX_ALLOCATIONS: u64 = 2_100;
const TRIVIAL_COMPILE_MAX_ALLOCATED_BYTES: u64 = 245_000;
const TRIVIAL_COMPILE_MAX_INSTRUCTIONS: u64 = 11_000_000;

#[test]
fn a_trivial_compile_stays_within_its_fixed_cost_budget() {
    let _serial = SERIAL.lock().unwrap_or_else(|poison| poison.into_inner());
    let module = parse(&trivial_module());
    measure(&module);
    let cost = measure(&module);
    eprintln!("trivial compile: {cost:?}");
    assert!(
        cost.allocations <= TRIVIAL_COMPILE_MAX_ALLOCATIONS,
        "{cost:?}: more than {TRIVIAL_COMPILE_MAX_ALLOCATIONS} allocations"
    );
    assert!(
        cost.allocated_bytes <= TRIVIAL_COMPILE_MAX_ALLOCATED_BYTES,
        "{cost:?}: more than {TRIVIAL_COMPILE_MAX_ALLOCATED_BYTES} bytes allocated"
    );
    if let Some(instructions) = cost.instructions {
        assert!(
            instructions <= TRIVIAL_COMPILE_MAX_INSTRUCTIONS,
            "{cost:?}: more than {TRIVIAL_COMPILE_MAX_INSTRUCTIONS} instructions retired"
        );
    }
}

/// The counters observe a compile at all: a larger module costs more.
#[test]
fn cost_metrics_observe_the_compile() {
    let _serial = SERIAL.lock().unwrap_or_else(|poison| poison.into_inner());
    let small = measure(&parse(&external_calls_module(8)));
    let large = measure(&parse(&external_calls_module(256)));
    assert!(large.allocated_bytes > small.allocated_bytes);
    assert!(large.allocations > small.allocations);
    assert!(large.peak_live_bytes > small.peak_live_bytes);
    if cfg!(target_os = "macos") {
        let (Some(small), Some(large)) = (small.instructions, large.instructions) else {
            panic!("proc_pid_rusage reported no instructions retired on macOS");
        };
        assert!(large > small);
    }
}

/// The call-heavy module the scaling probes compile computes what a C
/// reference computes, linked and run natively.
#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
#[test]
fn call_block_module_matches_c_reference() {
    let _serial = SERIAL.lock().unwrap_or_else(|poison| poison.into_inner());
    const FUNCTIONS: usize = 48;
    let object = native::compile(&parse(&loop_functions_module(FUNCTIONS)), OptLevel::O3);
    let driver = format!(
        r#"#include <stdint.h>
#include <stdio.h>
uint64_t entry(uint64_t);
static uint64_t reference_f(uint64_t i, uint64_t a, uint64_t b) {{
    uint64_t acc = a ^ ((i * 2654435761ULL) % (1ULL << 32));
    uint64_t k = 1 + i % 62;
    for (uint64_t j = 0; j < 64; j++) {{
        uint64_t t = acc * 6364136223846793005ULL + (j ^ b);
        t ^= t >> 29;
        acc = (t % 7 == 0) ? t + a : t ^ j;
        a = (a << k) | (a >> (64 - k));
    }}
    return acc;
}}
static uint64_t reference_entry(uint64_t s) {{
    uint64_t r = 0;
    for (uint64_t i = 0; i < {FUNCTIONS}; i++) r ^= reference_f(i, s, i);
    return r;
}}
int main(void) {{
    const uint64_t seeds[] = {{0, 1, 0x9E3779B97F4A7C15ULL, 0xFFFFFFFFFFFFFFFFULL, 12345}};
    for (unsigned n = 0; n < sizeof seeds / sizeof seeds[0]; n++) {{
        uint64_t got = entry(seeds[n]), want = reference_entry(seeds[n]);
        if (got != want) {{
            printf("seed %llu: got %llx want %llx\n", (unsigned long long)seeds[n],
                   (unsigned long long)got, (unsigned long long)want);
            return 1;
        }}
    }}
    printf("ok\n");
    return 0;
}}
"#
    );
    native::link_run("call_block_module_matches_c_reference", &object, &driver);
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes (or is refused) because the license silently refused it.
fn permit_unlicensed() -> trust_cg_lower::CodegenLicensePolicy {
    trust_cg_lower::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit)
}
