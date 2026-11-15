// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Every trap carrier's expansion, executed on aarch64-apple-darwin (ledger
//! L04-P12).
//!
//! Each case is a virtual-register function that guards an operation with one
//! carrier (`TrapNullIfZero`, `TrapDivZeroIfZero`, `TrapBoundsCheckExact` with
//! an immediate, wide-immediate and register bound, `TrapShiftRangeIfOOB`,
//! `TrapOverflowExact` for every overflow tag at both widths). It goes
//! through the O0 pipeline with function verification on (so the carrier's
//! stated expansion is judged before allocation and a refutation fails the
//! compile), register allocation, the late expansion, the final encoder (ENC-5
//! and the trap-expansion binding) and the JIT. Inputs just inside the guard
//! return the operation's value in this process; inputs just outside it, and
//! far outside it, run in a child process that must die of SIGTRAP raised by
//! the expansion's `BRK #1`: its signal handler reads the exception syndrome
//! (EC 0x3C, ISS = the BRK immediate) and the word at the faulting PC, prints
//! them, restores the default disposition and returns, so the BRK re-executes
//! and the child is killed by the signal. W cases are called with garbage in
//! the upper half of every argument register: their guards must read the low
//! 32 bits only.
//!
//! These are executions on this host: tested, not proved.
#![cfg(all(target_arch = "aarch64", target_os = "macos"))]

use std::collections::HashMap;
use std::ffi::{c_int, c_void};
use std::process::Command;

use trust_cg_codegen::jit::{JitCompiler, JitConfig};
use trust_cg_codegen::pipeline::{OptLevel, Pipeline, PipelineConfig};
use trust_cg_ir::aarch64_regs::{W0, W1, X0, X1};
use trust_cg_ir::overflow_tag::{OverflowOp, pack_overflow_tag};
use trust_cg_ir::regs::{RegClass, VReg};
use trust_cg_ir::{AArch64Opcode as O, MachFunction, MachInst, MachOperand, Signature, Type};

const CHILD_ENV: &str = "TCG_TRAP_EXPANSION_NATIVE_CHILD";
const TEST_NAME: &str = "every_trap_expansion_traps_exactly_outside_its_guard";
const SIGTRAP: c_int = 5;
const RETURNED_EXIT: i32 = 77;
/// Upper-half garbage for the arguments of a W case.
const GARBAGE: u64 = 0xDEAD_BEEF_0000_0000;

#[derive(Clone, Copy)]
enum Guard {
    Null,
    DivZero,
    BoundsImm(u64),
    BoundsReg,
    Shift(u32),
    Overflow(OverflowOp),
}

struct Case {
    name: String,
    width: u32,
    guard: Guard,
    /// Inputs inside the guard, with the value the function returns.
    passes: Vec<([u64; 2], u64)>,
    /// Inputs outside the guard: each must trap.
    traps: Vec<[u64; 2]>,
}

fn mask(width: u32) -> u64 {
    if width == 64 {
        u64::MAX
    } else {
        (1 << width) - 1
    }
}

fn cases() -> Vec<Case> {
    let mut out = Vec::new();
    for width in [32u32, 64] {
        let m = mask(width);
        let smax = m >> 1;
        let smin = smax + 1;
        let w = |name: &str| format!("{name}_w{width}");
        out.push(Case {
            name: w("div_zero"),
            width,
            guard: Guard::DivZero,
            passes: vec![([100, 7], 14), ([m, 1], m), ([5, m], 0)],
            traps: vec![[100, 0], [0, 0]],
        });
        out.push(Case {
            name: w("shift_range"),
            width,
            guard: Guard::Shift(width),
            passes: vec![([1, u64::from(width) - 1], 1 << (width - 1)), ([3, 0], 3)],
            traps: vec![[1, u64::from(width)], [1, m]],
        });
        for (label, k) in [("bounds_imm_10", 10u64), ("bounds_imm_4095", 0xFFF)] {
            out.push(Case {
                name: w(label),
                width,
                guard: Guard::BoundsImm(k),
                passes: vec![([k - 1, 0], k - 1), ([0, 0], 0)],
                traps: vec![[k, 0], [m, 0]],
            });
        }
        out.push(Case {
            name: w("bounds_reg"),
            width,
            guard: Guard::BoundsReg,
            passes: vec![([4, 5], 4), ([m - 1, m], m - 1)],
            traps: vec![[5, 5], [m, 0], [0, 0]],
        });
        let add_sub = [
            (
                "sadd",
                OverflowOp::SignedAdd,
                vec![([smax, 0], smax), ([smin, smax], m)],
                vec![[smax, 1], [smin, smin]],
            ),
            (
                "ssub",
                OverflowOp::SignedSub,
                vec![([smin, 0], smin), ([smax, smax], 0)],
                vec![[smin, 1], [smax, m]],
            ),
            (
                "uadd",
                OverflowOp::UnsignedAdd,
                vec![([m - 1, 1], m), ([0, 0], 0)],
                vec![[m, 1], [m, m]],
            ),
            (
                "usub",
                OverflowOp::UnsignedSub,
                vec![([1, 1], 0), ([m, m - 1], 1)],
                vec![[0, 1], [m - 1, m]],
            ),
        ];
        for (label, op, passes, traps) in add_sub {
            out.push(Case {
                name: w(label),
                width,
                guard: Guard::Overflow(op),
                passes,
                traps,
            });
        }
    }
    out.push(Case {
        name: "null_w64".into(),
        width: 64,
        guard: Guard::Null,
        passes: vec![([0x1000, 0], 0x1000), ([u64::MAX, 0], u64::MAX)],
        traps: vec![[0, 0]],
    });
    for (label, k) in [
        ("bounds_movz", 0x1234u64),
        ("bounds_movz_movk", 0x12_3456),
        ("bounds_movk_zero_low", 0x1_0000),
        ("bounds_i32_max", i32::MAX as u64),
    ] {
        out.push(Case {
            name: format!("{label}_w64"),
            width: 64,
            guard: Guard::BoundsImm(k),
            passes: vec![([k - 1, 0], k - 1)],
            traps: vec![[k, 0], [1 << 40, 0]],
        });
    }
    out.push(Case {
        name: "smul_w64".into(),
        width: 64,
        guard: Guard::Overflow(OverflowOp::SignedMul),
        passes: vec![
            ([1 << 31, 1 << 31], 1 << 62),
            ([u64::MAX, 1], u64::MAX),
            ([i64::MIN as u64, 1], i64::MIN as u64),
        ],
        traps: vec![
            [1 << 32, 1 << 31],
            [i64::MIN as u64, u64::MAX],
            [1 << 48, 1 << 48],
        ],
    });
    out.push(Case {
        name: "umul_w64".into(),
        width: 64,
        guard: Guard::Overflow(OverflowOp::UnsignedMul),
        passes: vec![
            ([1 << 32, (1 << 32) - 1], 0xFFFF_FFFF_0000_0000),
            ([u64::MAX, 1], u64::MAX),
        ],
        traps: vec![[1 << 32, 1 << 32], [u64::MAX, 2]],
    });
    out
}

/// The function a case compiles: `r = op(a, b)` behind the case's carrier.
fn function(case: &Case) -> MachFunction {
    let (class, ty, a_reg, b_reg) = if case.width == 32 {
        (RegClass::Gpr32, Type::I32, W0, W1)
    } else {
        (RegClass::Gpr64, Type::I64, X0, X1)
    };
    let sig = Signature::new(vec![ty.clone(), ty.clone()], vec![ty]);
    let mut func = MachFunction::new(case.name.clone(), sig);
    let entry = func.entry;
    let (a, b, r) = (func.alloc_vreg(), func.alloc_vreg(), func.alloc_vreg());
    let v = |id| MachOperand::VReg(VReg::new(id, class));
    let push = |func: &mut MachFunction, inst: MachInst| {
        let id = func.push_inst(inst);
        func.append_inst(entry, id);
    };
    push(
        &mut func,
        MachInst::new(O::MovR, vec![v(a), MachOperand::PReg(a_reg)]),
    );
    push(
        &mut func,
        MachInst::new(O::MovR, vec![v(b), MachOperand::PReg(b_reg)]),
    );
    let tag = |op| MachOperand::Imm(pack_overflow_tag(op, case.width as u16));
    let (carrier, value) = match case.guard {
        Guard::Null => (MachInst::new(O::TrapNullIfZero, vec![v(a)]), None),
        Guard::DivZero => (
            MachInst::new(O::TrapDivZeroIfZero, vec![v(b)]),
            Some(O::UDiv),
        ),
        Guard::BoundsImm(k) => (
            MachInst::new(
                O::TrapBoundsCheckExact,
                vec![v(a), v(a), MachOperand::Imm(k as i64)],
            ),
            None,
        ),
        Guard::BoundsReg => (
            MachInst::new(O::TrapBoundsCheckExact, vec![v(a), v(a), v(b)]),
            None,
        ),
        Guard::Shift(bits) => (
            MachInst::new(
                O::TrapShiftRangeIfOOB,
                vec![v(b), MachOperand::Imm(i64::from(bits))],
            ),
            Some(O::LslRR),
        ),
        Guard::Overflow(op) => (
            MachInst::new(O::TrapOverflowExact, vec![v(a), v(b), tag(op)]),
            Some(match op {
                OverflowOp::SignedAdd | OverflowOp::UnsignedAdd => O::AddRR,
                OverflowOp::SignedSub | OverflowOp::UnsignedSub => O::SubRR,
                OverflowOp::SignedMul | OverflowOp::UnsignedMul => O::MulRR,
            }),
        ),
    };
    push(&mut func, carrier);
    let result = match value {
        Some(opcode) => {
            push(&mut func, MachInst::new(opcode, vec![v(r), v(a), v(b)]));
            r
        }
        None => a,
    };
    push(
        &mut func,
        MachInst::new(O::MovR, vec![MachOperand::PReg(a_reg), v(result)]),
    );
    push(
        &mut func,
        MachInst::new(O::Ret, vec![]).with_implicit_uses(&[X0]),
    );
    func
}

fn compile(case: &Case) -> trust_cg_codegen::ExecutableBuffer {
    let pipeline = Pipeline::new(PipelineConfig {
        opt_level: OptLevel::O0,
        verify: true,
        target_triple: "aarch64-apple-darwin".into(),
        ..PipelineConfig::default()
    });
    let mut func = function(case);
    pipeline
        .prepare_ir_function(&mut func)
        .unwrap_or_else(|error| panic!("{}: {error}", case.name));
    assert_eq!(
        func.trap_expansions.len(),
        1,
        "{}: the carrier must survive to its expansion",
        case.name
    );
    JitCompiler::new(JitConfig::default())
        .compile_raw(&[func], &HashMap::new())
        .unwrap_or_else(|error| panic!("{}: {error}", case.name))
}

fn argument(case: &Case, value: u64) -> u64 {
    if case.width == 32 {
        GARBAGE | (value & mask(32))
    } else {
        value
    }
}

fn call(case: &Case, buffer: &trust_cg_codegen::ExecutableBuffer, inputs: [u64; 2]) -> u64 {
    // SAFETY: every case is `(i64|i32, i64|i32) -> i64|i32`; the AAPCS64
    // passes both in X0/X1 (a W argument's upper half is unspecified, which
    // the garbage exercises) and returns in X0. `buffer` outlives the call.
    let f = unsafe { buffer.get_fn_bound::<extern "C" fn(u64, u64) -> u64>(&case.name) }
        .unwrap_or_else(|| panic!("{}: symbol", case.name));
    (*f.as_ref())(argument(case, inputs[0]), argument(case, inputs[1])) & mask(case.width)
}

// ---------------------------------------------------------------------------
// The child: a SIGTRAP handler that reports the syndrome and re-raises.
// ---------------------------------------------------------------------------

unsafe extern "C" {
    fn sigaction(signum: c_int, act: *const DarwinSigAction, oldact: *mut DarwinSigAction)
    -> c_int;
    fn write(fd: c_int, buf: *const c_void, count: usize) -> isize;
    fn _exit(status: c_int) -> !;
}

#[repr(C)]
struct DarwinSigAction {
    sa_sigaction: usize,
    sa_mask: u32,
    sa_flags: c_int,
}

#[repr(C)]
struct DarwinStack {
    ss_sp: *mut c_void,
    ss_size: usize,
    ss_flags: c_int,
}

#[repr(C)]
struct DarwinUContext {
    uc_onstack: c_int,
    uc_sigmask: u32,
    uc_stack: DarwinStack,
    uc_link: *mut DarwinUContext,
    uc_mcsize: usize,
    uc_mcontext: *mut DarwinMContext64,
}

#[repr(C)]
struct DarwinMContext64 {
    es: DarwinExceptionState64,
    ss: DarwinThreadState64,
}

#[repr(C)]
struct DarwinExceptionState64 {
    far: u64,
    esr: u32,
    exception: u32,
}

#[repr(C)]
struct DarwinThreadState64 {
    x: [u64; 29],
    fp: u64,
    lr: u64,
    sp: u64,
    pc: u64,
    cpsr: u32,
    flags: u32,
}

/// `TRAP esr=<16 hex> word=<16 hex>\n`, without allocating.
fn report(esr: u64, word: u64) {
    let mut line = *b"TRAP esr=0000000000000000 word=0000000000000000\n";
    let hex = b"0123456789abcdef";
    for (offset, value) in [(9usize, esr), (31, word)] {
        for i in 0..16 {
            line[offset + i] = hex[((value >> (60 - 4 * i)) & 0xF) as usize];
        }
    }
    // SAFETY: a valid buffer on stdout.
    unsafe {
        let _ = write(1, line.as_ptr().cast(), line.len());
    }
}

extern "C" fn on_trap(_signal: c_int, _info: *mut c_void, context: *mut c_void) {
    // SAFETY: the kernel passes a valid Darwin arm64 ucontext.
    let (esr, word) = unsafe {
        let mcontext = (*context.cast::<DarwinUContext>()).uc_mcontext;
        let pc = (*mcontext).ss.pc;
        (
            u64::from((*mcontext).es.esr),
            u64::from(std::ptr::read_volatile(pc as *const u32)),
        )
    };
    report(esr, word);
    let default = DarwinSigAction {
        sa_sigaction: 0,
        sa_mask: 0,
        sa_flags: 0,
    };
    // SAFETY: restore SIG_DFL; returning re-executes the BRK, which now kills
    // the process with SIGTRAP.
    unsafe {
        if sigaction(SIGTRAP, &default, std::ptr::null_mut()) != 0 {
            _exit(90);
        }
    }
}

fn run_child(spec: &str) {
    let (name, index) = spec.split_once(':').expect("case:index");
    let cases = cases();
    let case = cases.iter().find(|c| c.name == name).expect("a case");
    let inputs = case.traps[index.parse::<usize>().expect("an index")];
    let buffer = compile(case);
    const SA_SIGINFO: c_int = 0x0040;
    let action = DarwinSigAction {
        sa_sigaction: on_trap as *const () as usize,
        sa_mask: 0,
        sa_flags: SA_SIGINFO,
    };
    // SAFETY: installing a handler in this single-purpose child.
    assert_eq!(
        unsafe { sigaction(SIGTRAP, &action, std::ptr::null_mut()) },
        0
    );
    let value = call(case, &buffer, inputs);
    println!("RETURNED {value:#x}");
    std::process::exit(RETURNED_EXIT);
}

#[test]
fn every_trap_expansion_traps_exactly_outside_its_guard() {
    if let Ok(spec) = std::env::var(CHILD_ENV) {
        run_child(&spec);
        return;
    }
    use std::os::unix::process::ExitStatusExt;
    let cases = cases();
    let (mut passes, mut traps) = (0usize, 0usize);
    for case in &cases {
        let buffer = compile(case);
        for (inputs, expected) in &case.passes {
            assert_eq!(
                call(case, &buffer, *inputs),
                *expected,
                "{}: {inputs:#x?} must return",
                case.name
            );
            passes += 1;
        }
        for index in 0..case.traps.len() {
            let output = Command::new(std::env::current_exe().expect("the test binary"))
                .args(["--exact", TEST_NAME, "--nocapture", "--test-threads=1"])
                .env(CHILD_ENV, format!("{}:{index}", case.name))
                .output()
                .expect("spawn the child");
            let stdout = String::from_utf8_lossy(&output.stdout);
            assert_eq!(
                output.status.signal(),
                Some(SIGTRAP),
                "{} {:#x?}: the child must die of SIGTRAP; status {:?}, stdout {stdout}, \
                 stderr {}",
                case.name,
                case.traps[index],
                output.status,
                String::from_utf8_lossy(&output.stderr)
            );
            // libtest leaves its `test ... ` prefix on the same line.
            let line = stdout
                .find("TRAP esr=")
                .map(|start| &stdout[start..])
                .unwrap_or_else(|| panic!("{}: no syndrome report in {stdout}", case.name));
            let field = |key: &str| {
                let start = line.find(key).expect("a field") + key.len();
                u64::from_str_radix(&line[start..start + 16], 16).expect("hex")
            };
            let (esr, word) = (field("esr="), field("word="));
            assert_eq!(
                esr >> 26,
                0x3C,
                "{}: ESR {esr:#x} is not a BRK exception",
                case.name
            );
            assert_eq!(
                esr & 0xFFFF,
                1,
                "{}: BRK immediate in ESR {esr:#x}",
                case.name
            );
            assert_eq!(
                word, 0xD420_0020,
                "{}: the faulting word is not BRK #1",
                case.name
            );
            traps += 1;
        }
    }
    assert_eq!(
        (cases.len(), passes, traps),
        (25, 49, 52),
        "cases, returning inputs, trapping inputs"
    );
    eprintln!(
        "TRAP_EXPANSION_NATIVE cases={} returns={passes} traps={traps}",
        cases.len()
    );
}
