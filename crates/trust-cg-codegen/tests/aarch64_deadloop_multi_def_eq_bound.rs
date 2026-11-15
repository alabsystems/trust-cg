// trust-cg-codegen - deadloop must not delete an EQ-exit loop whose bound varies per trip
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! `i = s; loop { sel = (i & 1) + base; r = search(sel); if i == r { break }
//! i += 1 }; 7`, run through the JIT at every optimization level.
//!
//! `search(sel)` is `j = 5; loop { j -= 1; if j == 1 || j == sel { break } }`,
//! which O2/O3 unroll fully, so the outer loop's exit compare `cmp i, r` reads
//! a register written by FOUR `Movz r, #4/#3/#2/#1` on different in-loop
//! paths. The `b.eq exit` termination argument of `deadloop` ("a `+1` counter
//! visits a fixed bound within `2^bits` trips") needs `r` to be one value for
//! the whole loop; a check that accepts any all-`Movz` definition set, without
//! requiring the definitions to write the SAME value, lets the pass delete
//! this pure, possibly non-terminating loop.
//!
//! With `base = 1` the bound is `1` on even trips and `2` on odd ones, and `i`
//! never equals it: the source spins forever. Neither Rust nor trust-ir assumes
//! forward progress, so the non-termination is the program's behavior, and a
//! build that returns 7 is a miscompile. With `base = 2` the loop stops at
//! `i == 2` (the control rows).
//!
//! The invariant this row pins: an `EQ`-exit bound is loop-invariant only when
//! every definition reaching the compare writes one value; several constant
//! definitions are a loop-variant bound, and `deadloop` keeps the loop.
//!
//! Each non-terminating run is a child process. The parent waits for the child
//! to report that it is about to call the kernel, then requires the child to be
//! still running after [`SPIN_WINDOW`]: tested on this host, not proved.
#![cfg(target_arch = "aarch64")]

use std::collections::HashMap;
use std::io::{BufRead, BufReader};
use std::os::unix::process::{CommandExt, ExitStatusExt};
use std::process::{Command, Stdio};
use std::sync::mpsc;
use std::time::{Duration, Instant};

use trust_cg_codegen::compiler::{Compiler, CompilerConfig, JitCompilationResult};
use trust_cg_codegen::pipeline::{OptLevel, Pipeline, PipelineConfig};
use trust_cg_codegen::target::Target;
use trust_ir::{BinOp, ICmpOp, Ty};
use trust_ir_build::ModuleBuilder;

const LEVELS: [OptLevel; 4] = [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3];
const ENTRY: &str = "eq_exit_against_search_stop";
const PASS: &str = "deadloop";
/// Names the level a child process runs.
const CHILD: &str = "TCG_TEST_DEADLOOP_EQ_BOUND_CHILD";
/// Printed by the child right before it calls the kernel.
const CALLING: &str = "deadloop-eq-bound-child: calling the kernel";
/// How long a child must keep spinning after it reports [`CALLING`].
const SPIN_WINDOW: Duration = Duration::from_secs(3);
/// Upper bound on the child's start-up and compile time before [`CALLING`].
const COMPILE_DEADLINE: Duration = Duration::from_secs(120);
/// `sel = (i & 1) + SPINNING_BASE` never meets `i`.
const SPINNING_BASE: i128 = 1;
/// `sel = (i & 1) + STOPPING_BASE` meets `i` at `i == 2`.
const STOPPING_BASE: i128 = 2;
/// Where the inner search starts (its first value is `SEARCH_START - 1`).
const SEARCH_START: i128 = 5;
const TRIPLE: &str = if cfg!(target_os = "linux") {
    "aarch64-unknown-linux-gnu"
} else {
    "aarch64-apple-darwin"
};

type Kernel = extern "C" fn(u64) -> u64;

/// The kernel of the doc comment for `base`.
fn module(base: i128) -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("aarch64_deadloop_multi_def_eq_bound");
    let ty = mb.add_func_type(vec![Ty::U64], vec![Ty::U64]);
    let mut fb = mb.function(ENTRY, ty);
    let entry = fb.create_block();
    let s = fb.add_block_param(entry, Ty::U64);
    let header = fb.create_block();
    let i = fb.add_block_param(header, Ty::U64);
    let search = fb.create_block();
    let j = fb.add_block_param(search, Ty::U64);
    let search_test = fb.create_block();
    let join = fb.create_block();
    let r = fb.add_block_param(join, Ty::U64);
    let latch = fb.create_block();
    let exit = fb.create_block();

    fb.switch_to_block(entry);
    fb.br(header, vec![s]);

    fb.switch_to_block(header);
    let one = fb.iconst(Ty::U64, 1);
    let low = fb.binop(BinOp::And, Ty::U64, i, one);
    let base = fb.iconst(Ty::U64, base);
    let sel = fb.binop(BinOp::Add, Ty::U64, low, base);
    let first = fb.iconst(Ty::U64, SEARCH_START);
    fb.br(search, vec![first]);

    fb.switch_to_block(search);
    let one = fb.iconst(Ty::U64, 1);
    let next = fb.sub(Ty::U64, j, one);
    fb.br(search_test, vec![]);

    fb.switch_to_block(search_test);
    let last = fb.iconst(Ty::U64, 1);
    let trip = fb.icmp(ICmpOp::Ne, Ty::U64, next, last);
    let not_found = fb.icmp(ICmpOp::Ne, Ty::U64, next, sel);
    let more = fb.binop(BinOp::And, Ty::Bool, trip, not_found);
    fb.condbr(more, search, vec![next], join, vec![next]);

    fb.switch_to_block(join);
    let hit = fb.icmp(ICmpOp::Eq, Ty::U64, i, r);
    fb.condbr(hit, exit, vec![], latch, vec![]);

    fb.switch_to_block(latch);
    let one = fb.iconst(Ty::U64, 1);
    let i2 = fb.binop(BinOp::Add, Ty::U64, i, one);
    fb.br(header, vec![i2]);

    fb.switch_to_block(exit);
    let seven = fb.iconst(Ty::U64, 7);
    fb.ret(vec![seven]);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

/// Where the source loop stops for `base` from `start`, or `None` when it
/// does not stop within `cap` trips.
fn source_stop(base: u64, start: u64, cap: u64) -> Option<u64> {
    let search = |sel: u64| {
        let mut j = SEARCH_START as u64;
        loop {
            j -= 1;
            if j == 1 || j == sel {
                return j;
            }
        }
    };
    let mut i = start;
    for _ in 0..cap {
        if i == search((i & 1) + base) {
            return Some(i);
        }
        i = i.wrapping_add(1);
    }
    None
}

/// How many times `pass` changed the function at `opt_level`, with an explicit
/// empty disable list so the ambient `TRUST_CG_DISABLE_PASSES` cannot hide it.
fn pass_changes(module: &trust_ir::Module, opt_level: OptLevel, pass: &str) -> u32 {
    let lowered = trust_cg_lower::translate_module_for_arch_with_tls_with_license(
        module,
        trust_cg_lower::GuardCarrierArch::default(),
        trust_cg_lower::TlsDialect::default(),
        &permit_unlicensed(),
    )
    .expect("lowering");
    let pipeline = Pipeline::new(PipelineConfig {
        opt_level,
        target_triple: TRIPLE.into(),
        disabled_passes_override: Some(String::new()),
        ..PipelineConfig::default()
    });
    let mut changes = 0;
    for (function, _) in &lowered {
        let (_, metrics) = pipeline
            .prepare_function_with_metrics(function, None)
            .expect("prepare");
        for (name, count) in &metrics.optimization_pass_changes {
            if name == pass {
                changes += count;
            }
        }
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

fn level_name(opt_level: OptLevel) -> &'static str {
    match opt_level {
        OptLevel::O0 => "O0",
        OptLevel::O1 => "O1",
        OptLevel::O2 => "O2",
        OptLevel::O3 => "O3",
    }
}

fn parse_level(name: &str) -> OptLevel {
    LEVELS
        .into_iter()
        .find(|&level| level_name(level) == name)
        .unwrap_or_else(|| panic!("unknown level {name}"))
}

/// The child half: compile the spinning kernel at `level` and call it. It
/// never returns in the source semantics; the parent kills it.
fn run_child(level: &str) -> ! {
    let result = jit(&module(SPINNING_BASE), parse_level(level));
    // SAFETY: the signature matches the trust-ir type (u64) -> u64 and
    // `result` outlives the call.
    let entry = unsafe { result.buffer.get_fn_bound::<Kernel>(ENTRY) }.expect("entry symbol");
    eprintln!("{CALLING}");
    let r = entry.as_ref()(0);
    eprintln!("deadloop-eq-bound-child: the kernel returned {r}");
    std::process::exit(3);
}

fn spins_through_the_window(test_name: &str, level: &str) -> Result<(), String> {
    let mut child = Command::new(std::env::current_exe().expect("test binary"))
        .args(["--exact", test_name, "--nocapture", "--test-threads=1"])
        .env(CHILD, level)
        .stdout(Stdio::null())
        .stderr(Stdio::piped())
        .process_group(0)
        .spawn()
        .map_err(|error| format!("spawn: {error}"))?;
    let stderr = child.stderr.take().expect("piped stderr");
    let (lines_tx, lines_rx) = mpsc::channel::<String>();
    let reader = std::thread::spawn(move || {
        for line in BufReader::new(stderr).lines().map_while(Result::ok) {
            if lines_tx.send(line).is_err() {
                break;
            }
        }
    });
    let mut transcript = Vec::new();
    let outcome = watch(&mut child, &lines_rx, &mut transcript);
    kill_process_group(child.id());
    let _ = child.kill();
    let reaped = child.wait();
    let _ = reader.join();
    transcript.extend(lines_rx.try_iter());
    outcome.map_err(|failure| {
        format!(
            "{failure}; reaped {reaped:?}; child stderr:\n{}",
            transcript.join("\n")
        )
    })
}

fn watch(
    child: &mut std::process::Child,
    lines: &mpsc::Receiver<String>,
    transcript: &mut Vec<String>,
) -> Result<(), String> {
    let compile_deadline = Instant::now() + COMPILE_DEADLINE;
    loop {
        let now = Instant::now();
        if now >= compile_deadline {
            return Err("the child did not call the kernel before the compile deadline".into());
        }
        match lines.recv_timeout(compile_deadline - now) {
            Ok(line) => {
                let calling = line == CALLING;
                transcript.push(line);
                if calling {
                    break;
                }
            }
            Err(_) => {
                let status = child.try_wait().ok().flatten();
                return Err(format!(
                    "the child ended before it called the kernel ({status:?})"
                ));
            }
        }
    }
    let spin_deadline = Instant::now() + SPIN_WINDOW;
    while Instant::now() < spin_deadline {
        match child.try_wait() {
            Ok(Some(status)) => {
                return Err(format!(
                    "the kernel ended the process within the spin window: {status} \
                     (signal {:?}); the source spins forever",
                    status.signal()
                ));
            }
            Ok(None) => std::thread::sleep(Duration::from_millis(20)),
            Err(error) => return Err(format!("try_wait: {error}")),
        }
    }
    Ok(())
}

unsafe extern "C" {
    fn kill(pid: i32, sig: i32) -> i32;
}

/// SIGKILL the child's process group (the child called `setpgid(0, 0)` through
/// `process_group(0)`). IDs 0 and 1 and values outside the PID range are never
/// signaled.
fn kill_process_group(pgid: u32) {
    if pgid > 1 && pgid <= i32::MAX as u32 {
        // SAFETY: `kill(2)` with a negative pid signals one process group; the
        // guard excludes -1 (every process) and 0 (this test's own group).
        unsafe {
            let _ = kill(-(pgid as i32), 9);
        }
    }
}

#[test]
fn the_source_model_spins_for_the_spinning_base_and_stops_for_the_control() {
    for start in 0..64 {
        assert_eq!(
            source_stop(SPINNING_BASE as u64, start, 1 << 16),
            None,
            "start = {start}"
        );
    }
    assert_eq!(source_stop(STOPPING_BASE as u64, 0, 1 << 16), Some(2));
}

/// `deadloop` must keep the outer loop for both bases: its termination proof
/// does not cover a bound written with different constants, whether or not
/// this particular loop happens to stop.
#[test]
fn deadloop_keeps_the_eq_exit_loop() {
    for base in [SPINNING_BASE, STOPPING_BASE] {
        let module = module(base);
        for opt_level in [OptLevel::O2, OptLevel::O3] {
            assert_eq!(
                pass_changes(&module, opt_level, PASS),
                0,
                "{opt_level:?}, base {base}: {PASS} deleted a loop with a per-trip bound"
            );
        }
    }
}

#[test]
fn the_stopping_control_returns_seven_at_every_level() {
    let module = module(STOPPING_BASE);
    for opt_level in LEVELS {
        let result = jit(&module, opt_level);
        // SAFETY: the signature matches the trust-ir type (u64) -> u64 and
        // `result` outlives the call.
        let entry = unsafe { result.buffer.get_fn_bound::<Kernel>(ENTRY) }.expect("entry symbol");
        for start in [0, 1, 2] {
            assert_eq!(entry.as_ref()(start), 7, "{opt_level:?}: start = {start}");
        }
    }
}

#[test]
fn an_eq_exit_against_a_per_trip_constant_bound_keeps_spinning() {
    const TEST: &str = "an_eq_exit_against_a_per_trip_constant_bound_keeps_spinning";
    if let Some(level) = std::env::var_os(CHILD) {
        run_child(level.to_str().expect("utf-8 child level"));
    }
    let mut failures = Vec::new();
    for opt_level in LEVELS {
        let level = level_name(opt_level);
        if let Err(failure) = spins_through_the_window(TEST, level) {
            failures.push(format!("{level}: {failure}"));
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes (or is refused) because the license silently refused it.
fn permit_unlicensed() -> trust_cg_codegen::CodegenLicensePolicy {
    trust_cg_codegen::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_codegen::UnlicensedBodyPolicy::Permit)
}
