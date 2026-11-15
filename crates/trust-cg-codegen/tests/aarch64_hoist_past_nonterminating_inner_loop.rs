// trust-cg-codegen - no invariant load hoists above an inner loop that may spin
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! `loop { [a[i] = 7;] while c != 0 {} v = *q; ... }`, run through the JIT at
//! every optimization level with `c = 1` and `q = 0x10` (inside the unmapped
//! zero page).
//!
//! The source never reaches the load: the inner loop spins forever. Neither
//! Rust nor trust-ir assumes forward progress, so that non-termination is the
//! program's behavior, and an optimized build that dereferences `q` first
//! turns it into a fault. The store-free kernel exercises LICM's
//! guaranteed-to-execute load tier, the `a[i]`-store kernel the alias-versioned
//! load hoist; both share `licm::load_guaranteed_to_execute`.
//!
//! Each run is a child process. The parent waits for the child to report that
//! it is about to call the kernel, then requires the child to be still running
//! after [`SPIN_WINDOW`]. This observes the absence of a fault within that
//! window on this host: tested, not proved. The `c = 0` controls check that
//! both kernels still compute the source result.
#![cfg(target_arch = "aarch64")]

use std::collections::HashMap;
use std::io::{BufRead, BufReader};
use std::os::unix::process::{CommandExt, ExitStatusExt};
use std::process::{Command, Stdio};
use std::sync::mpsc;
use std::time::{Duration, Instant};

use trust_cg_codegen::compiler::{Compiler, CompilerConfig, JitCompilationResult};
use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::target::Target;
use trust_ir::{BinOp, ICmpOp, Ty};
use trust_ir_build::ModuleBuilder;

const LEVELS: [OptLevel; 4] = [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3];
const LICM_ENTRY: &str = "spin_then_load";
const ALIAS_ENTRY: &str = "store_spin_then_load";
/// Names the kernel and level a child process runs, as `<kernel>:<level>`.
const CHILD: &str = "TCG_TEST_HOIST_NONTERMINATION_CHILD";
/// Printed by the child right before it calls the kernel.
const CALLING: &str = "hoist-nontermination-child: calling the kernel";
/// How long a child must keep spinning after it reports [`CALLING`].
const SPIN_WINDOW: Duration = Duration::from_secs(3);
/// Upper bound on the child's start-up and compile time before [`CALLING`].
const COMPILE_DEADLINE: Duration = Duration::from_secs(120);
/// Inside the unmapped zero page on Darwin and Linux.
const UNMAPPED: usize = 0x10;

/// `spin_then_load(c, q, n)`: `s = 0; i = 0; loop { while c != 0 {}
/// s += *q; i += 1; if i >= n { break } }; s`. No store, no call.
fn spin_then_load_module() -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("aarch64_hoist_nontermination_licm");
    let ty = mb.add_func_type(vec![Ty::U64, Ty::Ptr, Ty::U64], vec![Ty::U64]);
    let mut fb = mb.function(LICM_ENTRY, ty);
    let entry = fb.create_block();
    let c = fb.add_block_param(entry, Ty::U64);
    let q = fb.add_block_param(entry, Ty::Ptr);
    let n = fb.add_block_param(entry, Ty::U64);
    let header = fb.create_block();
    let i = fb.add_block_param(header, Ty::U64);
    let s = fb.add_block_param(header, Ty::U64);
    let spin = fb.create_block();
    let after = fb.create_block();
    let exit = fb.create_block();
    let result = fb.add_block_param(exit, Ty::U64);

    fb.switch_to_block(entry);
    let zero = fb.iconst(Ty::U64, 0);
    fb.br(header, vec![zero, zero]);

    fb.switch_to_block(header);
    fb.br(spin, vec![]);

    fb.switch_to_block(spin);
    let zero = fb.iconst(Ty::U64, 0);
    let spinning = fb.icmp(ICmpOp::Ne, Ty::U64, c, zero);
    fb.condbr(spinning, spin, vec![], after, vec![]);

    fb.switch_to_block(after);
    let v = fb.load(Ty::U64, q);
    let sum = fb.binop(BinOp::Add, Ty::U64, s, v);
    let one = fb.iconst(Ty::U64, 1);
    let next = fb.binop(BinOp::Add, Ty::U64, i, one);
    let done = fb.icmp(ICmpOp::Uge, Ty::U64, next, n);
    fb.condbr(done, exit, vec![sum], header, vec![next, sum]);

    fb.switch_to_block(exit);
    fb.ret(vec![result]);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

/// `store_spin_then_load(a, c, q, out, n)`: `i = 0; loop { a[i] = 7;
/// while c != 0 {} *out = *q; i += 1; if i >= n { break } }`.
fn store_spin_then_load_module() -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("aarch64_hoist_nontermination_alias");
    let ty = mb.add_func_type(vec![Ty::Ptr, Ty::U64, Ty::Ptr, Ty::Ptr, Ty::U64], vec![]);
    let mut fb = mb.function(ALIAS_ENTRY, ty);
    let entry = fb.create_block();
    let a = fb.add_block_param(entry, Ty::Ptr);
    let c = fb.add_block_param(entry, Ty::U64);
    let q = fb.add_block_param(entry, Ty::Ptr);
    let out = fb.add_block_param(entry, Ty::Ptr);
    let n = fb.add_block_param(entry, Ty::U64);
    let header = fb.create_block();
    let i = fb.add_block_param(header, Ty::U64);
    let spin = fb.create_block();
    let after = fb.create_block();
    let done = fb.create_block();

    fb.switch_to_block(entry);
    let zero = fb.iconst(Ty::U64, 0);
    fb.br(header, vec![zero]);

    fb.switch_to_block(header);
    let slot = fb.gep(Ty::U64, a, vec![i]);
    let seven = fb.iconst(Ty::U64, 7);
    fb.store(Ty::U64, slot, seven);
    fb.br(spin, vec![]);

    fb.switch_to_block(spin);
    let zero = fb.iconst(Ty::U64, 0);
    let spinning = fb.icmp(ICmpOp::Ne, Ty::U64, c, zero);
    fb.condbr(spinning, spin, vec![], after, vec![]);

    fb.switch_to_block(after);
    let v = fb.load(Ty::U64, q);
    fb.store(Ty::U64, out, v);
    let one = fb.iconst(Ty::U64, 1);
    let next = fb.binop(BinOp::Add, Ty::U64, i, one);
    let stop = fb.icmp(ICmpOp::Uge, Ty::U64, next, n);
    fb.condbr(stop, done, vec![], header, vec![next]);

    fb.switch_to_block(done);
    fb.ret(vec![]);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

type LicmKernel = extern "C" fn(u64, *const u64, u64) -> u64;
type AliasKernel = extern "C" fn(*mut u64, u64, *const u64, *mut u64, u64);

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

/// The child half: compile `kernel` at `level` and call it with the inner loop
/// spinning (`c = 1`) and the load address unmapped. It never returns from the
/// call in the source semantics; the parent kills it.
fn run_child(spec: &str) -> ! {
    let (kernel, level) = spec.split_once(':').expect("<kernel>:<level>");
    let opt_level = parse_level(level);
    let q = UNMAPPED as *const u64;
    match kernel {
        "licm" => {
            let result = jit(&spin_then_load_module(), opt_level);
            // SAFETY: the signature matches the trust-ir type (u64, ptr, u64)
            // -> u64 and `result` outlives the call. `q` is never dereferenced
            // by the source program while `c != 0`.
            let entry = unsafe { result.buffer.get_fn_bound::<LicmKernel>(LICM_ENTRY) }
                .expect("entry symbol");
            eprintln!("{CALLING}");
            let s = entry.as_ref()(1, q, 4);
            eprintln!("hoist-nontermination-child: the kernel returned {s}");
        }
        "alias" => {
            let result = jit(&store_spin_then_load_module(), opt_level);
            let mut a = [0u64; 8];
            let mut out = 0u64;
            // SAFETY: the signature matches the trust-ir type (ptr, u64, ptr,
            // ptr, u64) -> () and `result`, `a` and `out` outlive the call.
            // The source stores only `a[0]` before spinning.
            let entry = unsafe { result.buffer.get_fn_bound::<AliasKernel>(ALIAS_ENTRY) }
                .expect("entry symbol");
            eprintln!("{CALLING}");
            entry.as_ref()(a.as_mut_ptr(), 1, q, &mut out, 4);
            eprintln!("hoist-nontermination-child: the kernel returned, out = {out}");
        }
        other => panic!("unknown kernel {other}"),
    }
    std::process::exit(3);
}

/// The parent half: run `test_name` again as a child on `kernel` at every
/// level and require each child to keep spinning for [`SPIN_WINDOW`] after it
/// calls the kernel.
fn require_every_level_spins(test_name: &str, kernel: &str) {
    if let Some(spec) = std::env::var_os(CHILD) {
        run_child(spec.to_str().expect("utf-8 child spec"));
    }
    let mut failures = Vec::new();
    for opt_level in LEVELS {
        let spec = format!("{kernel}:{}", level_name(opt_level));
        if let Err(failure) = spins_through_the_window(test_name, &spec) {
            failures.push(format!("{spec}: {failure}"));
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

fn spins_through_the_window(test_name: &str, spec: &str) -> Result<(), String> {
    let mut child = Command::new(std::env::current_exe().expect("test binary"))
        .args(["--exact", test_name, "--nocapture", "--test-threads=1"])
        .env(CHILD, spec)
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
    // SIGKILL the child's own process group, then reap it: a spinning child
    // is in user mode and dies promptly.
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
fn an_invariant_load_after_a_spinning_inner_loop_is_not_hoisted_by_licm() {
    require_every_level_spins(
        "an_invariant_load_after_a_spinning_inner_loop_is_not_hoisted_by_licm",
        "licm",
    );
}

#[test]
fn an_invariant_load_after_a_spinning_inner_loop_is_not_alias_hoisted() {
    require_every_level_spins(
        "an_invariant_load_after_a_spinning_inner_loop_is_not_alias_hoisted",
        "alias",
    );
}

#[test]
fn both_kernels_compute_the_source_result_when_the_inner_loop_exits() {
    let licm = spin_then_load_module();
    let alias = store_spin_then_load_module();
    for opt_level in LEVELS {
        let result = jit(&licm, opt_level);
        // SAFETY: the signature matches the trust-ir type and `result` and
        // `value` outlive the call.
        let entry =
            unsafe { result.buffer.get_fn_bound::<LicmKernel>(LICM_ENTRY) }.expect("entry symbol");
        let value = 11u64;
        for (n, want) in [(0, 11), (1, 11), (4, 44)] {
            assert_eq!(entry.as_ref()(0, &value, n), want, "{opt_level:?}: n = {n}");
        }

        let result = jit(&alias, opt_level);
        // SAFETY: the signature matches the trust-ir type; the kernel stores
        // `a[0..max(n, 1)]` with `max(n, 1) <= 8` and reads `a[p_index]`.
        let entry = unsafe { result.buffer.get_fn_bound::<AliasKernel>(ALIAS_ENTRY) }
            .expect("entry symbol");
        for (p_index, n, want) in [(0, 1, 7), (3, 4, 7), (4, 4, 0), (7, 8, 7)] {
            let mut a = [0u64; 8];
            let mut out = u64::MAX;
            let base = a.as_mut_ptr();
            entry.as_ref()(base, 0, unsafe { base.add(p_index) }, &mut out, n);
            assert_eq!(out, want, "{opt_level:?}: p = a + {p_index}, n = {n}");
            assert_eq!(a[0], 7, "{opt_level:?}: iteration 0 stores a[0]");
        }
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
