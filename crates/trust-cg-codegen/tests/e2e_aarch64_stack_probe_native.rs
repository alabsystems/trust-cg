// Copyright 2026 Andrew Yates | Apache-2.0
//! Native AArch64 stack-probe execution and guard-page controls.
//!
//! Two backend functions are compiled at O0-O3 for the host object format
//! (Mach-O on Darwin, ELF on Linux) and linked with a C driver:
//!
//! * `cg_probe_static(x)` owns a 1.5 MiB stack array and stores `x` at both
//!   ends, including the far end at the final SP;
//! * `cg_probe_dynamic(n)` allocates an `n`-byte runtime array and does the
//!   same.
//!
//! The driver runs both on the main thread and on an 8 MiB thread and checks
//! their results. It then runs each on a 256 KiB thread with a 64 KiB guard,
//! catches SIGSEGV/SIGBUS on an alternate signal stack and requires the fault
//! address to lie in the first 4 KiB below the thread stack, i.e. the first
//! touch past the stack is a probe inside the guard. A hand-written unprobed
//! control that reads 2 MiB below SP must not produce that result. The raw
//! JIT installs the same prepared functions and executes them in-process.
//!
//! The Linux arm runs only on an aarch64 GNU/Linux host (registered in
//! `scripts/check_linux_aarch64.py`); it has not been executed on Darwin.

#![cfg(all(
    target_arch = "aarch64",
    any(target_os = "macos", all(target_os = "linux", target_env = "gnu"))
))]

#[path = "common/rosetta.rs"]
mod process;

#[path = "common/fresh_dir.rs"]
mod fresh_dir;

use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

use trust_cg_codegen::pipeline::{OptLevel, Pipeline, PipelineConfig};
use trust_cg_ir::function::StackSlotSizeSource;
use trust_cg_lower::function::{
    BasicBlock, Function as LirFunction, Signature as LirSignature, StackSlotInfo,
};
use trust_cg_lower::instructions::{Block, Instruction, Opcode, Value};
use trust_cg_lower::types::Type as LirType;

const STATIC_BYTES: u32 = 3 << 19; // 1.5 MiB

fn triple() -> &'static str {
    if cfg!(target_os = "macos") {
        "aarch64-apple-darwin"
    } else {
        "aarch64-unknown-linux-gnu"
    }
}

fn inst(opcode: Opcode, args: Vec<u32>, results: Vec<u32>) -> Instruction {
    Instruction {
        opcode,
        args: args.into_iter().map(Value).collect(),
        results: results.into_iter().map(Value).collect(),
    }
}

/// `f(x) = x + x` through volatile stores at both ends of a `bytes` slot, or
/// of an `x`-byte runtime slot when `bytes` is `None` (x >= 8).
fn far_end_function(name: &str, bytes: Option<u32>) -> LirFunction {
    let mut func = LirFunction::new(
        name,
        LirSignature {
            params: vec![LirType::I64],
            returns: vec![LirType::I64],
        },
    );
    func.stack_slots.push(match bytes {
        Some(bytes) => StackSlotInfo::new(bytes, 16),
        None => StackSlotInfo::new_dynamic_with_unit(StackSlotSizeSource::Value(0), 1, 16),
    });
    let constant = |imm, value| {
        inst(
            Opcode::Iconst {
                ty: LirType::I64,
                imm,
            },
            vec![],
            vec![value],
        )
    };
    let store = || Opcode::VolatileStore {
        ty: LirType::I64,
        align: None,
    };
    let load = || Opcode::VolatileLoad {
        ty: LirType::I64,
        align: None,
    };
    let mut instructions = vec![inst(Opcode::StackAddr { slot: 0 }, vec![], vec![1])];
    match bytes {
        Some(bytes) => instructions.push(constant(i64::from(bytes) - 8, 3)),
        None => instructions.extend([constant(-8, 2), inst(Opcode::Iadd, vec![2, 0], vec![3])]),
    }
    instructions.extend([
        inst(Opcode::Iadd, vec![1, 3], vec![4]),
        inst(store(), vec![0, 1], vec![]),
        inst(store(), vec![0, 4], vec![]),
        inst(load(), vec![1], vec![5]),
        inst(load(), vec![4], vec![6]),
        inst(Opcode::Iadd, vec![5, 6], vec![7]),
        inst(Opcode::Return, vec![7], vec![]),
    ]);
    func.blocks.insert(
        Block(0),
        BasicBlock {
            params: vec![(Value(0), LirType::I64)],
            instructions,
            source_locs: vec![],
        },
    );
    func
}

const DRIVER: &str = r#"
#define _GNU_SOURCE
#include <pthread.h>
#include <signal.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

extern int64_t cg_probe_static(int64_t);
extern int64_t cg_probe_dynamic(int64_t);

#define GUARD (64u * 1024u)
static volatile uintptr_t stack_low, guard_low;
static char alternate[256 * 1024];

static void put(const char *s) { (void)!write(1, s, strlen(s)); }
static void put_hex(const char *label, uintptr_t v) {
  char b[40];
  size_t n = strlen(label);
  memcpy(b, label, n);
  b[n++] = '0'; b[n++] = 'x';
  for (int i = 0; i < 16; i++) { int d = (v >> (60 - 4 * i)) & 15; b[n++] = d < 10 ? '0' + d : 'a' + d - 10; }
  b[n++] = '\n';
  (void)!write(1, b, n);
}

static void on_fault(int sig, siginfo_t *info, void *context) {
  (void)context;
  uintptr_t address = (uintptr_t)info->si_addr;
  put(sig == SIGBUS ? "signal SIGBUS\n" : "signal SIGSEGV\n");
  put_hex("fault ", address);
  put_hex("stack_low ", stack_low);
  put_hex("guard_low ", guard_low);
  if (address >= guard_low && address < stack_low && stack_low - address <= 4096) {
    put("GUARD_FIRST_PAGE\n");
    _exit(0);
  }
  put(address >= guard_low && address < stack_low ? "GUARD_DEEP\n" : "OUTSIDE_GUARD\n");
  _exit(2);
}

static void record_stack_bounds(void) {
#ifdef __APPLE__
  pthread_t self = pthread_self();
  uintptr_t top = (uintptr_t)pthread_get_stackaddr_np(self);
  stack_low = top - pthread_get_stacksize_np(self);
#else
  pthread_attr_t attr;
  void *address;
  size_t size;
  if (pthread_getattr_np(pthread_self(), &attr) || pthread_attr_getstack(&attr, &address, &size)) {
    put("stack bounds unavailable\n");
    _exit(4);
  }
  pthread_attr_destroy(&attr);
  stack_low = (uintptr_t)address;
#endif
  guard_low = stack_low - GUARD;
}

/* Unprobed control: read 2 MiB below SP without touching anything between. */
__attribute__((noinline)) static void unprobed_read(void) {
  __asm__ volatile("mov x9, sp\n\tsub x9, x9, #0x200, lsl #12\n\tldr x10, [x9]\n" ::: "x9", "x10", "memory");
}

static void *overflow_worker(void *argument) {
  const char *mode = argument;
  stack_t stack = {0};
  stack.ss_sp = alternate;
  stack.ss_size = sizeof alternate;
  if (sigaltstack(&stack, NULL)) { put("sigaltstack failed\n"); _exit(4); }
  record_stack_bounds();
  if (!strcmp(mode, "static")) {
    volatile int64_t r = cg_probe_static(7);
    (void)r;
  } else if (!strcmp(mode, "dynamic")) {
    volatile int64_t r = cg_probe_dynamic(2 << 20);
    (void)r;
  } else {
    unprobed_read();
  }
  put("NO_FAULT\n");
  _exit(3);
}

static int checks, failures;
static void check(const char *what, int64_t got, int64_t expected) {
  checks++;
  if (got != expected) {
    failures++;
    fprintf(stderr, "%s: got %lld expected %lld\n", what, (long long)got, (long long)expected);
  }
}

static void run_values(void) {
  check("static", cg_probe_static(21), 42);
  const int64_t sizes[] = {8, 16, 4096, 4104, 65536, (1 << 20) + 8, 3 << 20};
  for (unsigned i = 0; i < sizeof sizes / sizeof *sizes; i++)
    check("dynamic", cg_probe_dynamic(sizes[i]), 2 * sizes[i]);
}

static void *value_worker(void *argument) {
  (void)argument;
  run_values();
  return NULL;
}

static pthread_t start(void *(*body)(void *), void *argument, size_t stack_size) {
  pthread_attr_t attr;
  pthread_t thread;
  pthread_attr_init(&attr);
  if (pthread_attr_setstacksize(&attr, stack_size) || pthread_attr_setguardsize(&attr, GUARD) ||
      pthread_create(&thread, &attr, body, argument)) {
    put("thread creation failed\n");
    exit(4);
  }
  pthread_attr_destroy(&attr);
  return thread;
}

int main(int argc, char **argv) {
  if (argc != 2) return 5;
  if (!strcmp(argv[1], "values")) {
    run_values();
    pthread_join(start(value_worker, NULL, 8u << 20), NULL);
    if (failures || checks != 16) { fprintf(stderr, "checks=%d failures=%d\n", checks, failures); return 1; }
    printf("PASS %d value checks on the main thread and an 8 MiB thread\n", checks);
    return 0;
  }
  struct sigaction action;
  memset(&action, 0, sizeof action);
  action.sa_sigaction = on_fault;
  action.sa_flags = SA_SIGINFO | SA_ONSTACK;
  sigemptyset(&action.sa_mask);
  if (sigaction(SIGSEGV, &action, NULL) || sigaction(SIGBUS, &action, NULL)) return 4;
  pthread_join(start(overflow_worker, argv[1], 256u << 10), NULL);
  return 6;
}
"#;

fn scratch(tag: &str) -> fresh_dir::ScratchDir {
    fresh_dir::create(&format!("trust-cg-stack-probe-{tag}-"))
}

fn build(dir: &Path, level: OptLevel) -> PathBuf {
    let pipeline = Pipeline::new(PipelineConfig {
        opt_level: level,
        target_triple: triple().into(),
        emit_debug: false,
        ..Default::default()
    });
    let mut objects = Vec::new();
    for (name, bytes) in [
        ("cg_probe_static", Some(STATIC_BYTES)),
        ("cg_probe_dynamic", None),
    ] {
        let object = pipeline
            .compile_function(&far_end_function(name, bytes))
            .unwrap_or_else(|e| panic!("{level:?} {name}: {e:?}"));
        let path = dir.join(format!("{name}.o"));
        fs::write(&path, object).unwrap();
        objects.push(path);
    }
    fs::write(dir.join("driver.c"), DRIVER).unwrap();
    let binary = dir.join("probe");
    let mut link = Command::new("cc");
    link.arg("-O1").arg(dir.join("driver.c")).args(&objects);
    if cfg!(target_os = "linux") {
        link.arg("-Wl,-z,noexecstack").arg("-lpthread");
    }
    link.arg("-o").arg(&binary);
    let linked = process::command_output_with_timeout(&mut link, process::codegen_link_timeout())
        .expect("cc must be available on a native AArch64 host");
    assert!(
        !linked.timed_out && linked.output.status.success(),
        "{level:?} link in {dir:?}: {}",
        String::from_utf8_lossy(&linked.output.stderr)
    );
    binary
}

fn run(binary: &Path, mode: &str) -> (Option<i32>, String) {
    let mut command = Command::new(binary);
    command.arg(mode);
    let result = process::command_output_with_timeout(&mut command, process::codegen_run_timeout())
        .expect("run probe driver");
    assert!(!result.timed_out, "{mode}: timed out");
    let stdout = String::from_utf8_lossy(&result.output.stdout).into_owned();
    let stderr = String::from_utf8_lossy(&result.output.stderr);
    (result.output.status.code(), format!("{stdout}{stderr}"))
}

const LEVELS: [OptLevel; 4] = [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3];

#[test]
fn far_end_stack_arrays_execute_at_every_level() {
    for level in LEVELS {
        let dir = scratch("values");
        let binary = build(&dir, level);
        let (code, output) = run(&binary, "values");
        assert_eq!(code, Some(0), "{level:?}: {output}");
        assert!(
            output.contains("PASS 16 value checks"),
            "{level:?}: {output}"
        );
        let _ = fs::remove_dir_all(&dir);
    }
}

/// The in-process JIT executes the same frame lowering output: prepare each
/// function through the production pipeline, install it and call it on a
/// thread whose stack holds the frames.
#[test]
fn jit_installed_probed_frames_execute_at_every_level() {
    use std::collections::HashMap;
    use trust_cg_codegen::jit::{JitCompiler, JitConfig};

    type Probe = extern "C" fn(i64) -> i64;
    std::thread::Builder::new()
        .stack_size(64 << 20)
        .spawn(|| {
            for level in LEVELS {
                let pipeline = Pipeline::new(PipelineConfig {
                    opt_level: level,
                    target_triple: triple().into(),
                    emit_debug: false,
                    ..Default::default()
                });
                let prepared = [
                    ("jit_probe_static", Some(STATIC_BYTES)),
                    ("jit_probe_dynamic", None),
                ]
                .map(|(name, bytes)| {
                    pipeline
                        .prepare_function(&far_end_function(name, bytes))
                        .unwrap_or_else(|e| panic!("{level:?} {name}: {e:?}"))
                });
                let buffer = JitCompiler::new(JitConfig::default())
                    .compile_raw(&prepared, &HashMap::new())
                    .unwrap_or_else(|e| panic!("{level:?}: {e:?}"));
                let static_probe: Probe = unsafe { buffer.get_fn_bound("jit_probe_static") }
                    .expect("static symbol")
                    .into_inner();
                let dynamic_probe: Probe = unsafe { buffer.get_fn_bound("jit_probe_dynamic") }
                    .expect("dynamic symbol")
                    .into_inner();
                assert_eq!(static_probe(21), 42, "{level:?}");
                for n in [8i64, 4096, 4104, (1 << 20) + 8, 3 << 20] {
                    assert_eq!(dynamic_probe(n), 2 * n, "{level:?} n {n}");
                }
            }
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn stack_overflow_faults_in_the_first_guard_page() {
    let mut controls = 0;
    for level in LEVELS {
        let dir = scratch("guard");
        let binary = build(&dir, level);
        for mode in ["static", "dynamic"] {
            let (code, output) = run(&binary, mode);
            eprintln!("{level:?} {mode}: {code:?}\n{output}");
            assert_eq!(code, Some(0), "{level:?} {mode}: {output}");
            assert!(
                output.contains("GUARD_FIRST_PAGE"),
                "{level:?} {mode}: {output}"
            );
        }
        // The same guard check refuses an allocation that skips the guard.
        let (code, output) = run(&binary, "unprobed");
        eprintln!("{level:?} unprobed control: {code:?}\n{output}");
        assert!(
            matches!(code, Some(2 | 3)) && !output.contains("GUARD_FIRST_PAGE"),
            "{level:?} unprobed control: {code:?} {output}"
        );
        controls += 1;
        let _ = fs::remove_dir_all(&dir);
    }
    assert_eq!(controls, LEVELS.len());
}
