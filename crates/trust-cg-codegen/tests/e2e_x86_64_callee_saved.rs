// trust-cg-codegen/tests/e2e_x86_64_callee_saved.rs
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// ===========================================================================
// x86-64 CALLEE-SAVED REGISTER PRESERVATION ACROSS CALLS
// ===========================================================================
//
// AArch64 carries `e2e_aarch64_callee_saved_fpr.rs`, which pins a confirmed P0:
// a function holding an FP value in a callee-saved register across a call did
// not save/restore it and silently clobbered the caller. x86-64 had NO
// equivalent evidence for its callee-saved set. This file supplies it.
//
// The saved set, read out of the tree rather than assumed:
//   * System V AMD64 — `trust_cg_ir::x86_64_regs::X86_CALLEE_SAVED_GPRS`
//     = RBX, RBP, R12, R13, R14, R15. NO callee-saved XMM.
//   * Windows x64 — `x86_abi_callee_saved_gprs(WindowsX64)`
//     = RBX, RBP, RSI, RDI, R12..R15, plus `x86_abi_callee_saved_xmms`
//     = XMM6..XMM15.
// RBP is never allocatable (it is the frame pointer), so it is preserved
// structurally by the unconditional `PUSH RBP` / `POP RBP` of every frame. The
// rest are pushed only when the allocation actually uses them
// (`x86_used_callee_saved_from_allocation` -> `generate_prologue` /
// `generate_epilogue`, `x86_64/pipeline.rs`).
//
// THREE KINDS OF EVIDENCE, and they are NOT of equal strength:
//
//  (E1) EXECUTION — the real oracle. Needs an x86-64 host with `cc -arch
//       x86_64`; SYSTEM V ONLY. A hand-written assembly probe pins a distinct
//       64-bit sentinel in EACH of RBX, RBP, R12, R13, R14, R15, calls the
//       function under test, and returns a bitmask of the registers whose
//       sentinel did not survive. The probe's teeth are established FIRST by a
//       battery of eight negative controls — seven assembly callees that
//       clobber a KNOWN subset of the callee-saved set, one that clobbers none
//       — each of which must produce EXACTLY its own mask AND its own distinct
//       return value, so a control cannot be repointed at a different callee
//       while still counting itself. The driver refuses to report success
//       unless all eight ran, and the Rust side pins ALL EIGHT printed lines.
//       Execution alone cannot show that the SUBJECT exercised the hazard (a
//       function that spilled everything to the stack also returns mask 0), so
//       every executed object additionally carries a HAZARD WITNESS read off
//       its own disassembly — see (P5).
//
//  (E2) INDEPENDENT STRUCTURAL REFUTATION — runs for BOTH ABIs, on any host
//       with an `objdump` that decodes BOTH (E2) formats. The emitted object is decoded by that
//       EXTERNAL disassembler, and two structurally distinct sides are
//       compared:
//         SOURCE side  — the set of callee-saved registers the function BODY
//                        mentions, read off the disassembly text with no
//                        reference to the frame's decision.
//         MACHINE side — the set the PROLOGUE pushes (and the XMM slots it
//                        stores), plus the mirrored epilogue at EVERY return.
//       The obligation is `body-touched ⊆ prologue-saved`, with the epilogue
//       an exact mirror. Direction matters: a body MENTION is used as a proxy
//       for a body WRITE, and the proxy is conservative in the safe direction
//       — a mention that is only a read would demand a save that was not
//       needed, which FAILS LOUDLY rather than passing. (The literal premise
//       also holds in this tree: no callee-saved register is an incoming
//       argument under either ABI — SysV args RDI/RSI/RDX/RCX/R8/R9, Win64
//       args RCX/RDX/R8/R9 with the 7th+ read RBP-relative.) This is what
//       gives the Windows x64 lane teeth without executing it.
//
//  (E3) ENCODER-FAITHFULNESS FLOOR — always runs, no external tools. An
//       in-file SDM decode of the `PUSH r64` / `POP r64` / `MOVDQU` forms over
//       the raw emitted bytes, compared against
//       `X86RegallocPressureEvidence::callee_saved_{gpr,xmm}_save_count`.
//       ⚠ This comparison is NOT independent: both sides descend from the same
//       `assignment.used_callee_saved`. It proves the ENCODER emits what the
//       frame decided; it CANNOT catch a frame that decided the wrong set.
//       It is labelled as such rather than counted as a refutation. Its value
//       is non-vacuity (it names the saved set) and a NOP-tolerant mirrored
//       restore check, once per exit. It carries its own negative-control
//       battery.
//
// THE OBLIGATION IS SEVEN NAMED FACETS, and each one is pinned per (subject,
// ABI, opt level) by a `FrameObligation` that states the DESIGNED strength of
// the lane rather than a floor of one:
//   (P0) SOURCE-side non-vacuity — the BODY must mention at least the stated
//        number of callee-saved registers. Without this, `body_touched ∩
//        callee_saved = {}` makes (P1) a loop over an empty set and the whole
//        lane passes having compared nothing.
//   (P1) body-touched ⊆ prologue-saved, for GPRs and for XMMs.
//   (P2) every save has a mirrored restore in exactly reverse order at EVERY
//        return, and each XMM is reloaded from the SAME frame slot it was
//        stored to.
//   (P3) nothing outside the ABI's callee-saved set is pushed as one.
//   (P4) MACHINE-side designed strength — the prologue must save every
//        register the lane was built to reach, not merely one of them.
//   (P5) HAZARD WITNESS — the body must mention at least the stated number of
//        callee-saved GPRs BOTH before and after the call, i.e. it really does
//        park values in callee-saved registers across a call rather than
//        spilling them to the stack.
//   (P6) the exit count the reader assumed is the exit count the function has.
//
// WHAT THIS FILE DOES NOT PROVE — stated plainly:
//   * The Windows x64 lane is NEVER EXECUTED. This is a Darwin/SysV host;
//     Win64 code cannot be linked or run here, every `jit_windows_*` target in
//     this crate is `#[cfg(target_os = "windows")]` for the same reason, and
//     this crate has no mmap/`libc` dependency with which to publish raw bytes
//     and call them through a hand-written SysV->Win64 thunk. Win64 rests on
//     (E2) + (E3): an XMM save that stores the wrong 128-bit lane would
//     survive this file. A wrong save-slot ADDRESS no longer does — (P2) pins
//     the save and the reload to the same printed slot.
//   * Nothing here is a machine-checked proof obligation. It is testing
//     evidence: an execution oracle plus two decodes.
//   * The CLAIM IS CALLEE-SAVED PRESERVATION, not a full ABI lane. The
//     executed (E1) subject passes six register-class integer/pointer
//     arguments and returns an i64. No stack-passed argument (SysV 7th+), no
//     FP argument in XMM0-7 and no FP return is ever EXECUTED; the f64-returning
//     subject is Win64-only, and Win64 is never run here. (Checked, and the
//     reason the push count is nevertheless harmless for the unexecuted case:
//     incoming stack arguments are addressed RBP-relative, at +16 and
//     +16+shadow, `x86_64_isel.rs`, so the number of callee-saved pushes does
//     not move them.)
//   * When the x86-64 execution oracle or an `objdump` that decodes BOTH (E2) formats is missing,
//     the affected lane cannot run. The test then prints a conforming
//     `SKIP: ` line, which `scripts/matrix_results.py` counts as a runtime
//     SKIP and which turns the named Cargo gate NON-PASS. Degradation to the
//     (E3) floor alone — which this file labels NOT independent — is therefore
//     never recorded as a green gate.
//
// WHAT IT FOUND (2026-09-18, x86-64 Darwin host):
//   * NO MISCOMPILE in the backend. System V preservation of RBX/RBP/R12-R15
//     across a call holds at O0, O1, O2 and O3 under the execution oracle,
//     with all eight probe controls refuting; both ABIs satisfy the
//     independent obligation at every opt level, for a single-exit and for a
//     two-exit subject; the Win64 XMM6..XMM15 save/restore pairs are all ten
//     present, mirrored and slot-identical at every opt level.
//   * ONE REAL DEFECT, in the test infrastructure, found by running the target
//     45 times: `common/disasm.rs` built its scratch directory from
//     `SystemTime::now().as_nanos()`, which is MICROSECOND-resolution on this
//     host, so two concurrent decodes collided on one path and each decoded
//     the OTHER's object. ~11% of runs then reported a violation ABOUT THE
//     WRONG SUBJECT (the SysV lane seeing a Win64 `pushq %rsi`, the Win64 lane
//     seeing a SysV argument sequence). Fixed at the source with a process-wide
//     counter plus a read-back provenance check.
//   * One benign asymmetry, recorded so a reader does not mistake it for a bug:
//     under Windows x64 the single-exit GPR frame saves RSI although the body
//     never mentions it. `used_callee_saved` is computed from the allocation
//     map BEFORE the post-regalloc `MovRR` coalescer deletes the copy that used
//     that register, so the frame OVER-saves. That is a code-size/latency cost,
//     never a correctness one, and the obligation here is a SUBSET relation
//     (`body-touched subset-of prologue-saved`) precisely because the safe
//     direction is to save too much.
//   * The regalloc call-clobber model
//     (`trust_cg_regalloc::x86_64_caller_saved_regs`) is hard-wired to the
//     System V volatile set for BOTH ABIs. Under Win64 that is a strict
//     over-approximation — sound, but it means no value can be held in
//     XMM6..XMM15 (or RSI/RDI) across a call under Win64, which is why the XMM
//     subject reaches them through pressure instead.

#![allow(clippy::too_many_arguments)]

mod common;

#[path = "common/fresh_dir.rs"]
mod fresh_dir;

use std::collections::BTreeSet;
use std::fs;
use std::panic::{AssertUnwindSafe, catch_unwind};
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::Mutex;

use common::disasm::{
    DisasmInsn, ObjFormat, disasm_has_llvm_family_objdump, disasm_scratch_dir,
    disassemble_x86_text, has_objdump_for, has_objdump_for_all,
};

/// The two container formats (E2) decodes: the host default that `sysv_object`
/// emits, and the PE/COFF that `win64_object` emits for
/// `x86_64-pc-windows-msvc`. Both must be decodable or the obligation would run
/// on a partial set of subjects.
#[cfg(target_os = "macos")]
const E2_FORMATS: &[ObjFormat] = &[ObjFormat::MachO, ObjFormat::Coff];
#[cfg(not(target_os = "macos"))]
const E2_FORMATS: &[ObjFormat] = &[ObjFormat::Elf, ObjFormat::Coff];

/// The format probe must answer per FORMAT, not per vendor and not per host OS.
///
/// Regression pin for a defect this target caught twice. Gating the probe on the
/// VENDOR ("accept only an objdump whose `--version` says LLVM") made every (E2)
/// control below SKIP on a GNU-only host, which the Linux x86-64 floor recorded
/// as a vacuous pass. Gating it on the HOST OS instead (`!cfg!(target_os =
/// "macos")`) broke `guard_kernel_gate_x86_divzero_e2e` and
/// `..._shiftrange_e2e`, which decode a `x86_64-apple-darwin` object even on
/// Linux: they entered their objdump branch and their `expect(..)` panicked.
///
/// So this asserts the two halves that make the probe honest, on whatever host
/// runs it: the formats THIS target decodes are decodable (or its own (E2)
/// asserts would be unreachable), and a host whose only objdump is GNU binutils
/// must refuse Mach-O, because binutils is built with a chosen set of BFD targets
/// and this project's Linux hosts ship no Mach-O among them.
#[test]
fn e2_format_probe_answers_per_format_not_per_vendor_or_host() {
    let gnu_only = !disasm_has_llvm_family_objdump();
    if gnu_only {
        assert!(
            !has_objdump_for(ObjFormat::MachO),
            "a host whose only objdump is GNU binutils must not claim it can decode Mach-O;              claiming it sends the Mach-O guard-kernel gates into a decode that cannot work"
        );
        assert!(
            has_objdump_for(ObjFormat::Elf),
            "GNU binutils lists elf64-x86-64 and must satisfy the ELF probe; without this the              (E2) controls skip and the floor reads the skip as a vacuous pass"
        );
    }
    // Whatever the host, the two formats (E2) reads agree between the probe and a
    // real decode: if the probe says yes, the subjects really decode.
    if has_objdump_for_all(E2_FORMATS) {
        let module = build_gpr_stress_module();
        for (label, object) in [
            ("sysv", sysv_object(&module, OptLevel::O2)),
            ("win64", win64_object(&module, OptLevel::O2)),
        ] {
            assert!(
                disassemble_x86_text(&object).is_some_and(|insns| !insns.is_empty()),
                "the probe admitted every (E2) format, so the {label} subject must really decode"
            );
        }
    }
}
use common::rosetta::{
    codegen_link_timeout, codegen_run_timeout, command_output_with_timeout,
    run_executable_with_timeout,
};
use common::x86_64_corpus::x86_64_oracle_enabled;

use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::target::{Target, TargetSpec};
use trust_cg_codegen::x86_64::{X86OutputFormat, X86Pipeline, X86PipelineConfig};
use trust_cg_lower::function::Function as LirFunction;
use trust_cg_lower::x86_64_isel::X86CallAbi;
use trust_cg_opt::OptLevel as X86OptLevel;
use trust_ir::{ICmpOp, Ty};
use trust_ir_build::ModuleBuilder;

/// One heavy cargo/cc lane at a time: this file links and runs native binaries.
static SERIAL: Mutex<()> = Mutex::new(());

const GPR_SUBJECT: &str = "tcg_cs_stress";
const XMM_SUBJECT: &str = "tcg_cs_xmm_pressure";
const TWO_EXIT_SUBJECT: &str = "tcg_cs_two_exit";

const ALL_OPT: [OptLevel; 4] = [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3];
const ALL_X86_OPT: [X86OptLevel; 4] = [
    X86OptLevel::O0,
    X86OptLevel::O1,
    X86OptLevel::O2,
    X86OptLevel::O3,
];

// ===========================================================================
// The trust_ir subjects
// ===========================================================================

/// ```c
/// long tcg_cs_stress(long (*sink)(long), long a1, long a2, long a3,
///                    long a4, long a5) {
///     long s = sink(a1);              /* clobbers every caller-saved reg */
///     return s + a1 + a2 + a3 + a4 + a5;
/// }
/// ```
///
/// `a1..a5` arrive in caller-saved argument registers and are ALL live across
/// the call. Every caller-saved register is an implicit def of the call
/// (`x86_isel_to_regalloc`), so the allocator must park them in the ABI's
/// allocatable callee-saved GPRs — under SysV exactly RBX, R12, R13, R14, R15
/// — or spill. That is the reachable trigger for the frame's save/restore path.
///
/// The call is INDIRECT on purpose: a direct symbolic call needs relocation
/// emission, which the single-function raw-bytes API refuses
/// (`SymbolicDirectCallRequiresRelocationEmission`). An indirect call lets the
/// SAME function be executed, emitted as an object for (E2), and emitted as
/// raw bytes for (E3).
fn build_gpr_stress_module() -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("x86_64_callee_saved_gpr");
    let sink_ty = mb.add_func_type(vec![Ty::I64], vec![Ty::I64]);
    let stress_ty = mb.add_func_type(
        vec![Ty::Ptr, Ty::I64, Ty::I64, Ty::I64, Ty::I64, Ty::I64],
        vec![Ty::I64],
    );

    let mut fb = mb.function(GPR_SUBJECT, stress_ty);
    let entry = fb.create_block();
    let sink = fb.add_block_param(entry, Ty::Ptr);
    let a1 = fb.add_block_param(entry, Ty::I64);
    let a2 = fb.add_block_param(entry, Ty::I64);
    let a3 = fb.add_block_param(entry, Ty::I64);
    let a4 = fb.add_block_param(entry, Ty::I64);
    let a5 = fb.add_block_param(entry, Ty::I64);
    fb.switch_to_block(entry);

    let s = fb.call_indirect(sink, sink_ty, vec![a1]);
    let mut acc = s;
    for value in [a1, a2, a3, a4, a5] {
        acc = fb.add(Ty::I64, acc, value);
    }
    fb.ret(vec![acc]);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

/// The same hazard with TWO RETURNS.
///
/// ```c
/// long tcg_cs_two_exit(long (*sink)(long), long a1, ..., long a5) {
///     long s = sink(a1);
///     if (s < 0) return s + a1 + a2 + a3 + a4 + a5;
///     return s - a5 - a4 - a3 - a2 - a1;
/// }
/// ```
///
/// This exists because the single-exit shape lets a reader assume there is
/// exactly one epilogue. Production inserts an epilogue before EVERY `Ret`
/// (`x86_64/pipeline.rs`, "Insert epilogue before every RET instruction"), so
/// a missing or misordered restore on ONE path is the most plausible shape of
/// the bug — and a reader that walked back only from the final `retq` could
/// not see it even if the subject existed. `frame_view` therefore checks the
/// mirrored restore at every exit, and this subject is what makes that check
/// non-vacuous.
fn build_two_exit_module() -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("x86_64_callee_saved_two_exit");
    let sink_ty = mb.add_func_type(vec![Ty::I64], vec![Ty::I64]);
    let ty = mb.add_func_type(
        vec![Ty::Ptr, Ty::I64, Ty::I64, Ty::I64, Ty::I64, Ty::I64],
        vec![Ty::I64],
    );

    let mut fb = mb.function(TWO_EXIT_SUBJECT, ty);
    let entry = fb.create_block();
    let neg = fb.create_block();
    let pos = fb.create_block();
    let sink = fb.add_block_param(entry, Ty::Ptr);
    let a1 = fb.add_block_param(entry, Ty::I64);
    let a2 = fb.add_block_param(entry, Ty::I64);
    let a3 = fb.add_block_param(entry, Ty::I64);
    let a4 = fb.add_block_param(entry, Ty::I64);
    let a5 = fb.add_block_param(entry, Ty::I64);
    fb.switch_to_block(entry);

    let s = fb.call_indirect(sink, sink_ty, vec![a1]);
    let zero = fb.iconst(Ty::I64, 0);
    let cond = fb.icmp(ICmpOp::Slt, Ty::I64, s, zero);
    fb.condbr(cond, neg, vec![], pos, vec![]);

    fb.switch_to_block(neg);
    let mut acc = s;
    for value in [a1, a2, a3, a4, a5] {
        acc = fb.add(Ty::I64, acc, value);
    }
    fb.ret(vec![acc]);

    fb.switch_to_block(pos);
    let mut acc = s;
    for value in [a5, a4, a3, a2, a1] {
        acc = fb.sub(Ty::I64, acc, value);
    }
    fb.ret(vec![acc]);

    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

/// The arguments the driver passes to [`GPR_SUBJECT`]. Stated here as well as
/// in `DRIVER_C` on purpose: the Rust side recomputes the expected value and
/// asserts it against the value the native binary PRINTS, so a drift between
/// the two statements fails the test instead of hiding.
const GPR_ARGS: [i64; 5] = [0x0123_4567_89ab_cdef, -7, 1_000_000_007, -1, 42];

/// The oracle for [`build_gpr_stress_module`] with `sink(n) = n + 1`.
fn gpr_stress_oracle(a: [i64; 5]) -> i64 {
    a[0].wrapping_add(1)
        .wrapping_add(a[0])
        .wrapping_add(a[1])
        .wrapping_add(a[2])
        .wrapping_add(a[3])
        .wrapping_add(a[4])
}

/// `double tcg_cs_xmm_pressure(const double *p)`: `XMM_LANES` loaded values,
/// each scaled, ALL live simultaneously, then summed.
///
/// This is the Windows x64 callee-saved-XMM trigger, and it deliberately
/// contains NO call. The regalloc clobber model
/// (`trust_cg_regalloc::x86_64_caller_saved_regs`, consumed by
/// `x86_isel_to_regalloc`) is hard-wired to the System V volatile set — every
/// XMM, plus RSI and RDI — for BOTH ABIs. Under Win64 that is a strict
/// OVER-approximation (Win64's volatile GPRs {RAX,RCX,RDX,R8..R11} and
/// XMM0..XMM5 are subsets of the modelled clobber set), so it is SOUND but
/// incomplete: no XMM can ever be chosen for a value live across a call under
/// Win64. Simultaneous XMM PRESSURE, not a call, is therefore what reaches
/// XMM6..XMM15.
const XMM_LANES: usize = 12;

fn build_xmm_pressure_module() -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("x86_64_callee_saved_xmm");
    let ty = mb.add_func_type(vec![Ty::Ptr], vec![Ty::F64]);
    let mut fb = mb.function(XMM_SUBJECT, ty);
    let entry = fb.create_block();
    let base = fb.add_block_param(entry, Ty::Ptr);
    fb.switch_to_block(entry);

    let mut live = Vec::with_capacity(XMM_LANES);
    for lane in 0..XMM_LANES {
        let index = fb.iconst(Ty::I64, lane as i128);
        let addr = fb.gep(Ty::F64, base, vec![index]);
        let loaded = fb.load(Ty::F64, addr);
        let scale = fb.fconst(Ty::F64, (lane as f64) + 1.5);
        live.push(fb.fmul(Ty::F64, loaded, scale));
    }
    let mut acc = live[0];
    for &value in &live[1..] {
        acc = fb.fadd(Ty::F64, acc, value);
    }
    fb.ret(vec![acc]);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

// ===========================================================================
// The ABI's callee-saved sets, as register NAMES
// ===========================================================================

/// SysV callee-saved GPRs the allocator may actually hand out. RBP is the
/// frame pointer and is never allocatable, so it never appears in the pushed
/// set — the unconditional PUSH/POP RBP preserves it instead.
const SYSV_ALLOCATABLE_CALLEE_SAVED: [&str; 5] = ["rbx", "r12", "r13", "r14", "r15"];

/// Windows x64 additionally makes RSI and RDI callee-saved.
const WIN64_ALLOCATABLE_CALLEE_SAVED: [&str; 7] = ["rbx", "rsi", "rdi", "r12", "r13", "r14", "r15"];

/// Windows x64 callee-saved XMM registers. Empty under SysV.
const WIN64_CALLEE_SAVED_XMMS: [&str; 10] = [
    "xmm6", "xmm7", "xmm8", "xmm9", "xmm10", "xmm11", "xmm12", "xmm13", "xmm14", "xmm15",
];

fn callee_saved_gprs(abi: X86CallAbi) -> &'static [&'static str] {
    match abi {
        X86CallAbi::SystemV => &SYSV_ALLOCATABLE_CALLEE_SAVED,
        X86CallAbi::WindowsX64 => &WIN64_ALLOCATABLE_CALLEE_SAVED,
    }
}

fn callee_saved_xmms(abi: X86CallAbi) -> &'static [&'static str] {
    match abi {
        X86CallAbi::SystemV => &[],
        X86CallAbi::WindowsX64 => &WIN64_CALLEE_SAVED_XMMS,
    }
}

/// Map any width of an x86-64 register name onto its 64-bit root. Returns
/// `None` for anything that is not a register this file reasons about.
///
/// Sub-register widths matter: an allocation to `EBX`/`BX`/`BL` writes RBX
/// (and the 32-bit form zero-extends the whole 64-bit register), so a body
/// that only ever mentions `%ebx` still clobbers the caller's RBX.
fn register_root(name: &str) -> Option<&'static str> {
    Some(match name {
        "rax" | "eax" | "ax" | "al" | "ah" => "rax",
        "rcx" | "ecx" | "cx" | "cl" | "ch" => "rcx",
        "rdx" | "edx" | "dx" | "dl" | "dh" => "rdx",
        "rbx" | "ebx" | "bx" | "bl" | "bh" => "rbx",
        "rsp" | "esp" | "sp" | "spl" => "rsp",
        "rbp" | "ebp" | "bp" | "bpl" => "rbp",
        "rsi" | "esi" | "si" | "sil" => "rsi",
        "rdi" | "edi" | "di" | "dil" => "rdi",
        "r8" | "r8d" | "r8w" | "r8b" => "r8",
        "r9" | "r9d" | "r9w" | "r9b" => "r9",
        "r10" | "r10d" | "r10w" | "r10b" => "r10",
        "r11" | "r11d" | "r11w" | "r11b" => "r11",
        "r12" | "r12d" | "r12w" | "r12b" => "r12",
        "r13" | "r13d" | "r13w" | "r13b" => "r13",
        "r14" | "r14d" | "r14w" | "r14b" => "r14",
        "r15" | "r15d" | "r15w" | "r15b" => "r15",
        "xmm0" => "xmm0",
        "xmm1" => "xmm1",
        "xmm2" => "xmm2",
        "xmm3" => "xmm3",
        "xmm4" => "xmm4",
        "xmm5" => "xmm5",
        "xmm6" => "xmm6",
        "xmm7" => "xmm7",
        "xmm8" => "xmm8",
        "xmm9" => "xmm9",
        "xmm10" => "xmm10",
        "xmm11" => "xmm11",
        "xmm12" => "xmm12",
        "xmm13" => "xmm13",
        "xmm14" => "xmm14",
        "xmm15" => "xmm15",
        _ => return None,
    })
}

/// Every register root mentioned in an AT&T operand string (`%rax`, `%ebx`,
/// `(%rcx,%rbx,8)`, `%xmm6` ...). Reads and writes alike — see the soundness
/// argument for (E2) in the file header.
fn mentioned_registers(operands: &str) -> BTreeSet<&'static str> {
    let mut found = BTreeSet::new();
    let bytes: Vec<char> = operands.chars().collect();
    let mut i = 0usize;
    while i < bytes.len() {
        if bytes[i] == '%' {
            let start = i + 1;
            let mut end = start;
            while end < bytes.len() && bytes[end].is_ascii_alphanumeric() {
                end += 1;
            }
            let name: String = bytes[start..end].iter().collect();
            if let Some(root) = register_root(&name) {
                found.insert(root);
            }
            i = end;
        } else {
            i += 1;
        }
    }
    found
}

// ===========================================================================
// (E2) The independent structural refutation, over an EXTERNAL disassembly
// ===========================================================================

/// An AT&T MEMORY operand (`-80(%rbp)`, `48(%rbp)`, `(%rcx,%rbx,8)`), or
/// `None` for a bare register, an immediate or a branch target.
///
/// This exists because "the prologue stores an XMM to a frame SLOT" is a claim
/// about a MEMORY destination. Without it, `movdqu %xmm6, %xmm7` — which
/// stores nothing anywhere — reads as a callee-saved XMM save.
fn memory_operand(text: &str) -> Option<&str> {
    let t = text.trim();
    if t.starts_with('%') || t.starts_with('$') {
        return None;
    }
    let open = t.find('(')?;
    if !t.ends_with(')') {
        return None;
    }
    let inside = &t[open + 1..t.len() - 1];
    let base = inside.split(',').next()?.trim();
    register_root(base.strip_prefix('%')?)?;
    Some(t)
}

/// A `movdqu` that moves a whole XMM register to or from a MEMORY operand:
/// `(register, is_prologue_store, the memory operand's printed text)`.
///
/// `None` for anything else, including a register-to-register `movdqu`, which
/// touches no frame slot and must never be credited as a save or a restore.
fn movdqu_pair(insn: &DisasmInsn) -> Option<(&'static str, bool, String)> {
    if insn.mnemonic != "movdqu" {
        return None;
    }
    let (first, second) = insn.operands.split_once(',')?;
    let first = first.trim();
    let second = second.trim();
    // `movdqu %xmm6, -80(%rbp)` is a STORE (the prologue save);
    // `movdqu -80(%rbp), %xmm6` is a LOAD (the epilogue restore).
    if let Some(reg) = first.strip_prefix('%').and_then(register_root)
        && reg.starts_with("xmm")
    {
        let slot = memory_operand(second)?;
        return Some((reg, true, slot.to_string()));
    }
    if let Some(reg) = second.strip_prefix('%').and_then(register_root)
        && reg.starts_with("xmm")
    {
        let slot = memory_operand(first)?;
        return Some((reg, false, slot.to_string()));
    }
    None
}

/// One `retq` and the restore run that precedes it.
#[derive(Debug, Clone)]
struct ExitView {
    /// Byte offset of the `retq`, for diagnostics.
    at: u64,
    /// Callee-saved GPRs popped before the final `popq %rbp`, in pop order.
    restored_gprs: Vec<&'static str>,
    /// `(register, frame slot)` for each XMM this exit reloads, in reload order.
    restored_xmms: Vec<(&'static str, String)>,
}

/// What an external disassembler says about a frame.
#[derive(Debug, Clone)]
struct FrameView {
    /// Callee-saved GPRs pushed after the mandatory `pushq %rbp`, in push order.
    saved_gprs: Vec<&'static str>,
    /// `(register, frame slot)` the prologue STORES to, in store order.
    saved_xmms: Vec<(&'static str, String)>,
    /// One entry per `retq` in the function, in offset order.
    exits: Vec<ExitView>,
    /// Every register root the BODY mentions — the independent SOURCE side.
    body_touched: BTreeSet<&'static str>,
    /// Body registers mentioned strictly BEFORE the first call.
    before_call: BTreeSet<&'static str>,
    /// Body registers mentioned strictly AFTER the last call.
    after_call: BTreeSet<&'static str>,
    /// How many call instructions the body contains.
    calls: usize,
}

impl FrameView {
    fn saved_xmm_regs(&self) -> Vec<&'static str> {
        self.saved_xmms.iter().map(|(r, _)| *r).collect()
    }

    /// Callee-saved GPRs the body mentions on BOTH sides of a call: the
    /// structural witness that a value really was parked in a callee-saved
    /// register across the call rather than spilled to the stack.
    fn held_across_call(&self, cs: &[&str]) -> Vec<&'static str> {
        self.before_call
            .iter()
            .filter(|r| self.after_call.contains(*r) && cs.contains(*r))
            .copied()
            .collect()
    }
}

fn is_ret(insn: &DisasmInsn) -> bool {
    insn.mnemonic == "retq" || insn.mnemonic == "ret"
}

/// Split a disassembled single-function stream into prologue / body /
/// epilogues and read both sides of the obligation off it.
///
/// The epilogue walk-back is performed at EVERY `retq`, not only the last one:
/// production emits an epilogue before every `Ret`, and a reader that only
/// inspected the final one could not see a missing restore on another path.
fn frame_view(insns: &[DisasmInsn]) -> Result<FrameView, String> {
    if insns.len() < 3 {
        return Err(format!("only {} instruction(s) decoded", insns.len()));
    }
    if insns[0].mnemonic != "pushq" || mentioned_registers(&insns[0].operands) != once("rbp") {
        return Err(format!(
            "function does not start with `pushq %rbp`: {} {}",
            insns[0].mnemonic, insns[0].operands
        ));
    }
    if insns[1].mnemonic != "movq" || insns[1].operands.replace(' ', "") != "%rsp,%rbp" {
        return Err(format!(
            "`pushq %rbp` is not followed by `movq %rsp, %rbp`: {} {}",
            insns[1].mnemonic, insns[1].operands
        ));
    }

    // --- prologue: the run of callee-saved pushes ---
    let mut i = 2usize;
    let mut saved_gprs = Vec::new();
    while i < insns.len() && insns[i].mnemonic == "pushq" {
        let regs = mentioned_registers(&insns[i].operands);
        let reg = *regs
            .iter()
            .next()
            .ok_or_else(|| format!("`pushq {}` names no register", insns[i].operands))?;
        saved_gprs.push(reg);
        i += 1;
    }
    // Optional frame allocation.
    if i < insns.len()
        && (insns[i].mnemonic == "subq" || insns[i].mnemonic == "subl")
        && insns[i].operands.ends_with("%rsp")
    {
        i += 1;
    }
    // Optional Win64 callee-saved XMM saves.
    let mut saved_xmms = Vec::new();
    while i < insns.len() {
        match movdqu_pair(&insns[i]) {
            Some((reg, true, slot)) => {
                saved_xmms.push((reg, slot));
                i += 1;
            }
            _ => break,
        }
    }
    let body_start = i;

    // --- epilogues: walk back from EVERY `retq` ---
    let ret_indices: Vec<usize> = (body_start..insns.len())
        .filter(|&k| is_ret(&insns[k]))
        .collect();
    if ret_indices.is_empty() {
        return Err("function contains no `retq`".to_string());
    }
    if !is_ret(&insns[insns.len() - 1]) {
        return Err(format!(
            "function does not end with `retq`: {} {}",
            insns[insns.len() - 1].mnemonic,
            insns[insns.len() - 1].operands
        ));
    }

    let mut exits = Vec::new();
    // `in_epilogue[k]` marks every instruction that belongs to some epilogue,
    // so the body is exactly what is left over.
    let mut in_epilogue = vec![false; insns.len()];
    for &k in &ret_indices {
        let mut j = k;
        in_epilogue[k] = true;
        // Tolerate alignment `nop`s immediately before the return.
        while j > body_start && insns[j - 1].mnemonic.starts_with("nop") {
            j -= 1;
            in_epilogue[j] = true;
        }
        let mut restored_rev = Vec::new();
        while j > body_start && insns[j - 1].mnemonic == "popq" {
            let regs = mentioned_registers(&insns[j - 1].operands);
            let reg = *regs
                .iter()
                .next()
                .ok_or_else(|| format!("`popq {}` names no register", insns[j - 1].operands))?;
            restored_rev.push(reg);
            j -= 1;
            in_epilogue[j] = true;
        }
        restored_rev.reverse(); // now in POP order
        let last = restored_rev
            .pop()
            .ok_or_else(|| format!("the epilogue at {:x} has no `popq %rbp`", insns[k].offset))?;
        if last != "rbp" {
            return Err(format!(
                "the epilogue at {:x} ends its pop run with `{last}`, not `rbp`",
                insns[k].offset
            ));
        }
        // Optional frame deallocation.
        if j > body_start
            && (insns[j - 1].mnemonic == "addq" || insns[j - 1].mnemonic == "leaq")
            && insns[j - 1].operands.ends_with("%rsp")
        {
            j -= 1;
            in_epilogue[j] = true;
        }
        // Optional Win64 callee-saved XMM restores.
        let mut restored_xmms_rev = Vec::new();
        while j > body_start {
            match movdqu_pair(&insns[j - 1]) {
                Some((reg, false, slot)) => {
                    restored_xmms_rev.push((reg, slot));
                    j -= 1;
                    in_epilogue[j] = true;
                }
                _ => break,
            }
        }
        restored_xmms_rev.reverse();
        exits.push(ExitView {
            at: insns[k].offset,
            restored_gprs: restored_rev,
            restored_xmms: restored_xmms_rev,
        });
    }

    // --- the INDEPENDENT source side: what the body mentions ---
    let body: Vec<&DisasmInsn> = (body_start..insns.len())
        .filter(|&k| !in_epilogue[k])
        .map(|k| &insns[k])
        .collect();
    let mut body_touched = BTreeSet::new();
    for insn in &body {
        body_touched.extend(mentioned_registers(&insn.operands));
    }
    let call_positions: Vec<usize> = body
        .iter()
        .enumerate()
        .filter(|(_, insn)| insn.mnemonic.starts_with("call"))
        .map(|(idx, _)| idx)
        .collect();
    let mut before_call = BTreeSet::new();
    let mut after_call = BTreeSet::new();
    if let (Some(&first), Some(&last)) = (call_positions.first(), call_positions.last()) {
        for insn in &body[..first] {
            before_call.extend(mentioned_registers(&insn.operands));
        }
        for insn in &body[last + 1..] {
            after_call.extend(mentioned_registers(&insn.operands));
        }
    }

    Ok(FrameView {
        saved_gprs,
        saved_xmms,
        exits,
        body_touched,
        before_call,
        after_call,
        calls: call_positions.len(),
    })
}

fn once(name: &'static str) -> BTreeSet<&'static str> {
    let mut set = BTreeSet::new();
    set.insert(name);
    set
}

// ===========================================================================
// The obligation, as a per-lane statement of DESIGNED strength
// ===========================================================================

/// What one (subject, ABI, opt level) lane must show.
///
/// Every field exists because a floor of "at least one" is satisfiable by
/// evidence that exercises nothing. `min_body_cs_*` pins the SOURCE side (the
/// side (P1) quantifies over); `require_saved_*` pins the MACHINE side at the
/// strength the subject was BUILT to reach, so a regalloc change that quietly
/// stopped using four of five callee-saved registers turns the lane RED
/// instead of shrinking the evidence silently.
#[derive(Debug, Clone, Copy)]
struct FrameObligation {
    /// Callee-saved GPRs the prologue MUST save.
    require_saved_gprs: &'static [&'static str],
    /// Callee-saved XMMs the prologue MUST save.
    require_saved_xmms: &'static [&'static str],
    /// The body must MENTION at least this many callee-saved GPRs.
    min_body_cs_gprs: usize,
    /// The body must MENTION at least this many callee-saved XMMs.
    min_body_cs_xmms: usize,
    /// Callee-saved GPRs the body must mention on BOTH sides of a call.
    min_held_across_call: usize,
    /// How many `retq`s this subject has. Checked, never assumed.
    exits: usize,
}

const SYSV_GPR_OBLIGATION: FrameObligation = FrameObligation {
    require_saved_gprs: &SYSV_ALLOCATABLE_CALLEE_SAVED,
    require_saved_xmms: &[],
    min_body_cs_gprs: 5,
    min_body_cs_xmms: 0,
    min_held_across_call: 4,
    exits: 1,
};

/// RBX/R12..R15 are callee-saved under Win64 as well; RSI/RDI additionally so,
/// but the frame reaches them only by over-saving (see the header), which is
/// not a strength this lane may rest on.
const WIN64_GPR_OBLIGATION: FrameObligation = FrameObligation {
    require_saved_gprs: &SYSV_ALLOCATABLE_CALLEE_SAVED,
    require_saved_xmms: &[],
    min_body_cs_gprs: 5,
    min_body_cs_xmms: 0,
    min_held_across_call: 4,
    exits: 1,
};

/// ALL TEN of XMM6..XMM15 — the range the header names. Anything weaker
/// would let nine of the ten stop appearing with the lane still green.
const WIN64_XMM_OBLIGATION: FrameObligation = FrameObligation {
    require_saved_gprs: &[],
    require_saved_xmms: &WIN64_CALLEE_SAVED_XMMS,
    min_body_cs_gprs: 0,
    min_body_cs_xmms: 10,
    min_held_across_call: 0,
    exits: 1,
};

const SYSV_TWO_EXIT_OBLIGATION: FrameObligation = FrameObligation {
    exits: 2,
    ..SYSV_GPR_OBLIGATION
};

const WIN64_TWO_EXIT_OBLIGATION: FrameObligation = FrameObligation {
    exits: 2,
    ..WIN64_GPR_OBLIGATION
};

/// Apply the obligation to one decoded instruction stream. Panics — with the
/// facet's own name — on any violation.
///
/// This is a pure function over `&[DisasmInsn]` so that the negative-control
/// battery can DRIVE IT with refuting inputs. A control battery that only
/// exercised the extraction helpers would leave every one of (P0)-(P6) free to
/// be inverted, weakened or deleted with all controls still green.
fn check_frame_obligation(
    subject: &str,
    abi: X86CallAbi,
    opt: OptLevel,
    insns: &[DisasmInsn],
    ob: FrameObligation,
) -> FrameView {
    let view = frame_view(insns).unwrap_or_else(|e| {
        panic!(
            "{subject} {abi:?} {opt:?}: cannot read the frame off the external disassembly: {e}\n{}",
            render(insns)
        )
    });

    let cs_gprs = callee_saved_gprs(abi);
    let cs_xmms = callee_saved_xmms(abi);
    let body_cs_gprs: Vec<&str> = view
        .body_touched
        .iter()
        .filter(|r| cs_gprs.contains(*r))
        .copied()
        .collect();
    let body_cs_xmms: Vec<&str> = view
        .body_touched
        .iter()
        .filter(|r| cs_xmms.contains(*r))
        .copied()
        .collect();

    // (P0) SOURCE-SIDE NON-VACUITY. (P1) quantifies over the callee-saved
    // registers the BODY mentions. If that set is empty the loop asserts
    // NOTHING and the lane passes having compared nothing at all — the exact
    // "true by construction" shape this file exists to avoid. The non-vacuity
    // guard therefore pins the side the obligation ranges over, not the side
    // it concludes about.
    assert!(
        body_cs_gprs.len() >= ob.min_body_cs_gprs,
        "{subject} {abi:?} {opt:?}: VACUOUS OBLIGATION — the body mentions only {} callee-saved \
         GPR(s) {body_cs_gprs:?} but this lane must exercise at least {}. The subset check below \
         would quantify over an (almost) empty set and pass having compared nothing.\n{}",
        body_cs_gprs.len(),
        ob.min_body_cs_gprs,
        render(insns)
    );
    assert!(
        body_cs_xmms.len() >= ob.min_body_cs_xmms,
        "{subject} {abi:?} {opt:?}: VACUOUS OBLIGATION — the body mentions only {} callee-saved \
         XMM(s) {body_cs_xmms:?} but this lane must exercise at least {}.\n{}",
        body_cs_xmms.len(),
        ob.min_body_cs_xmms,
        render(insns)
    );

    // (P1) THE OBLIGATION. Every callee-saved register the BODY mentions must
    // be in the set the PROLOGUE saved. The two sides are read from different
    // regions of the disassembly and neither is derived from the other.
    let saved_xmm_regs = view.saved_xmm_regs();
    for reg in &view.body_touched {
        if cs_gprs.contains(reg) {
            assert!(
                view.saved_gprs.contains(reg),
                "{subject} {abi:?} {opt:?}: MISCOMPILE — the body uses callee-saved {reg} but the \
                 prologue saves only {:?}. The caller's {reg} is destroyed.\n{}",
                view.saved_gprs,
                render(insns)
            );
        }
        if cs_xmms.contains(reg) {
            assert!(
                saved_xmm_regs.contains(reg),
                "{subject} {abi:?} {opt:?}: MISCOMPILE — the body uses callee-saved {reg} but the \
                 prologue saves only {saved_xmm_regs:?}.\n{}",
                render(insns)
            );
        }
    }

    // (P6) The exit count the reader assumed is the exit count the function
    // has. Checked BEFORE (P2) so that "every exit was checked" means
    // something: a subject that silently collapsed to one return would make a
    // multi-exit lane's mirror check cover a shape it was not built for.
    assert_eq!(
        view.exits.len(),
        ob.exits,
        "{subject} {abi:?} {opt:?}: the function has {} return(s), not the {} this lane states; \
         the epilogue evidence would not cover the shape under test.\n{}",
        view.exits.len(),
        ob.exits,
        render(insns)
    );

    // (P2) Every save has a mirrored restore, in exactly reverse order, at
    // EVERY return — and every XMM is reloaded from the SAME frame slot it was
    // stored to. Without the slot comparison an epilogue that reloaded all ten
    // XMMs from the wrong displacement would pass.
    let mut expect: Vec<&'static str> = view.saved_gprs.clone();
    expect.reverse();
    let mut expect_xmm: Vec<(&'static str, String)> = view.saved_xmms.clone();
    expect_xmm.reverse();
    for exit in &view.exits {
        assert_eq!(
            exit.restored_gprs,
            expect,
            "{subject} {abi:?} {opt:?}: the epilogue at {:x} restores {:?} but the prologue saved \
             {:?}; the restore must be the exact reverse, at EVERY return.\n{}",
            exit.at,
            exit.restored_gprs,
            view.saved_gprs,
            render(insns)
        );
        assert_eq!(
            exit.restored_xmms,
            expect_xmm,
            "{subject} {abi:?} {opt:?}: the epilogue at {:x} reloads {:?} but the prologue saved \
             {:?}; each callee-saved XMM must be reloaded from the SAME frame slot it was stored \
             to, in reverse order.\n{}",
            exit.at,
            exit.restored_xmms,
            view.saved_xmms,
            render(insns)
        );
    }

    // (P3) Nothing outside the ABI's callee-saved set is pushed as one.
    for reg in &view.saved_gprs {
        assert!(
            cs_gprs.contains(reg),
            "{subject} {abi:?} {opt:?}: the prologue saves {reg}, which is NOT an allocatable \
             callee-saved register under this ABI ({cs_gprs:?})"
        );
    }
    for (reg, _) in &view.saved_xmms {
        assert!(
            cs_xmms.contains(reg),
            "{subject} {abi:?} {opt:?}: the prologue saves {reg}, which is NOT a callee-saved XMM \
             under this ABI ({cs_xmms:?})"
        );
    }

    // (P4) MACHINE-SIDE DESIGNED STRENGTH. Not "at least one save" — the exact
    // set this subject was built to drive into the frame. A subject or an
    // allocator change that quietly stopped parking values in four of the five
    // callee-saved GPRs would otherwise shrink the evidence from five
    // registers to one and stay green.
    for reg in ob.require_saved_gprs {
        assert!(
            view.saved_gprs.contains(reg),
            "{subject} {abi:?} {opt:?}: the prologue does NOT save {reg}; this lane is built to \
             drive {:?} into the frame and currently saves only {:?}, so the evidence is weaker \
             than it claims.\n{}",
            ob.require_saved_gprs,
            view.saved_gprs,
            render(insns)
        );
    }
    for reg in ob.require_saved_xmms {
        assert!(
            saved_xmm_regs.contains(reg),
            "{subject} {abi:?} {opt:?}: the prologue does NOT save {reg}; this lane is built to \
             drive {:?} into the frame and currently saves only {saved_xmm_regs:?}.\n{}",
            ob.require_saved_xmms,
            render(insns)
        );
    }

    // (P5) HAZARD WITNESS. A subject that spilled every live value to the
    // stack instead of parking it in a callee-saved register across the call
    // produces a correct result and a zero clobber mask — a green run with the
    // hazard NEVER EXECUTED. This reads, off the same disassembly, the
    // callee-saved GPRs the body mentions on BOTH sides of the call.
    let held = view.held_across_call(cs_gprs);
    assert!(
        held.len() >= ob.min_held_across_call,
        "{subject} {abi:?} {opt:?}: NO HAZARD EXERCISED — only {} callee-saved GPR(s) {held:?} are \
         mentioned both before and after the call, but this lane must hold at least {} across it. \
         A subject that parks nothing in a callee-saved register across a call satisfies the \
         execution oracle trivially.\n{}",
        held.len(),
        ob.min_held_across_call,
        render(insns)
    );

    eprintln!(
        "[E2 {subject} {abi:?} {opt:?}] saved GPRs {:?} | saved XMMs {:?} | body touches \
         callee-saved {:?}/{:?} | held across the call {:?} | {} exit(s), {} call(s)",
        view.saved_gprs,
        saved_xmm_regs,
        body_cs_gprs,
        body_cs_xmms,
        held,
        view.exits.len(),
        view.calls,
    );
    view
}

/// Run (E2) over one emitted object. Returns the view, or `None` when no
/// a capable `objdump` is available (reported LOUDLY by the caller).
fn independent_frame_check(
    subject: &str,
    abi: X86CallAbi,
    opt: OptLevel,
    object: &[u8],
    ob: FrameObligation,
) -> Option<FrameView> {
    let insns = disassemble_x86_text(object)?;
    Some(check_frame_obligation(subject, abi, opt, &insns, ob))
}

fn render(insns: &[DisasmInsn]) -> String {
    insns
        .iter()
        .map(|i| format!("  {:>4x}: {} {}", i.offset, i.mnemonic, i.operands))
        .collect::<Vec<_>>()
        .join("\n")
}

// ===========================================================================
// (E3) The always-available encoder-faithfulness floor
// ===========================================================================
//
// Intel SDM Vol. 2:
//   PUSH r64 = 50+rd, REX.B (41) for r8..r15;  POP r64 = 58+rd / 41 58+rd.
//   MOVDQU m128, xmm = F3 [REX] 0F 7F /r  (store — the prologue's XMM save)
//   MOVDQU xmm, m128 = F3 [REX] 0F 6F /r  (load  — the epilogue's restore)
//
// ⚠ The comparison this half makes is NOT independent (see the file header).

const HW_RAX: u8 = 0;
const HW_RBX: u8 = 3;
const HW_RBP: u8 = 5;
const HW_R12: u8 = 12;
const HW_R13: u8 = 13;
const HW_R14: u8 = 14;
const HW_R15: u8 = 15;

fn hw_name(reg: u8) -> &'static str {
    [
        "rax", "rcx", "rdx", "rbx", "rsp", "rbp", "rsi", "rdi", "r8", "r9", "r10", "r11", "r12",
        "r13", "r14", "r15",
    ]
    .get(reg as usize)
    .copied()
    .unwrap_or("?")
}

// NOTE: these two decoders use explicit `if`s rather than
// `cond.then_some(b - 0x50)`. `Option::then_some` takes its value EAGERLY, so
// the subtraction would be evaluated for every byte, including the ones the
// range test rejects — `attempt to subtract with overflow` on any byte below
// the opcode base. Release builds wrap and discard the value, so the bug is
// invisible there and only a debug build (which is how `soundness_check.sh`
// runs this target) fails. Keep the branch, not the combinator.

fn decode_push_r64(code: &[u8], at: usize) -> Option<(u8, usize)> {
    let b0 = *code.get(at)?;
    if b0 == 0x41 {
        let b1 = *code.get(at + 1)?;
        if (0x50..=0x57).contains(&b1) {
            return Some((8 + (b1 - 0x50), 2));
        }
        return None;
    }
    if (0x50..=0x57).contains(&b0) {
        return Some((b0 - 0x50, 1));
    }
    None
}

fn decode_pop_r64(code: &[u8], at: usize) -> Option<(u8, usize)> {
    let b0 = *code.get(at)?;
    if b0 == 0x41 {
        let b1 = *code.get(at + 1)?;
        if (0x58..=0x5F).contains(&b1) {
            return Some((8 + (b1 - 0x58), 2));
        }
        return None;
    }
    if (0x58..=0x5F).contains(&b0) {
        return Some((b0 - 0x58, 1));
    }
    None
}

fn encode_push_r64(reg: u8) -> Vec<u8> {
    if reg >= 8 {
        vec![0x41, 0x50 + (reg - 8)]
    } else {
        vec![0x50 + reg]
    }
}

fn encode_pop_r64(reg: u8) -> Vec<u8> {
    if reg >= 8 {
        vec![0x41, 0x58 + (reg - 8)]
    } else {
        vec![0x58 + reg]
    }
}

/// Decode a MOVDQU at `at`: `Some((is_store, encoded_len))`.
///
/// A REGISTER-DIRECT form (ModRM.mod == 0b11, i.e. `movdqu %xmm6, %xmm7`) is
/// REFUSED. It moves nothing to or from a frame slot, so counting it as a
/// callee-saved save or restore would credit a store that never happened.
fn movdqu_at(code: &[u8], at: usize) -> Option<(bool, usize)> {
    let mut i = at;
    if *code.get(i)? != 0xF3 {
        return None;
    }
    i += 1;
    if (0x40..=0x4F).contains(code.get(i)?) {
        i += 1;
    }
    if *code.get(i)? != 0x0F {
        return None;
    }
    i += 1;
    let is_store = match *code.get(i)? {
        0x7F => true,
        0x6F => false,
        _ => return None,
    };
    i += 1;
    let modrm = *code.get(i)?;
    i += 1;
    let md = modrm >> 6;
    let rm = modrm & 0x7;
    if md == 0b11 {
        // Register-direct: not a frame-slot access at all.
        return None;
    }
    if rm == 0b100 {
        i += 1; // SIB
    }
    match md {
        0b00 if rm == 0b101 => i += 4, // RIP-relative disp32
        0b01 => i += 1,
        0b10 => i += 4,
        _ => {}
    }
    (i <= code.len()).then_some((is_store, i - at))
}

fn is_movdqu_store(code: &[u8], at: usize) -> bool {
    movdqu_at(code, at).is_some_and(|(is_store, _)| is_store)
}

fn count_movdqu_loads(code: &[u8]) -> usize {
    let mut count = 0usize;
    let mut at = 0usize;
    while at < code.len() {
        if let Some((is_store, len)) = movdqu_at(code, at) {
            count += usize::from(!is_store);
            at += len;
        } else {
            at += 1;
        }
    }
    count
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct DecodedPrologue {
    pushed: Vec<u8>,
    xmm_stores: usize,
}

fn decode_prologue(code: &[u8]) -> Result<DecodedPrologue, String> {
    if code.first() != Some(&0x55) {
        return Err(format!(
            "prologue does not begin with PUSH RBP (0x55); first byte {:02x?}",
            code.first()
        ));
    }
    if code.get(1..4) != Some(&[0x48, 0x89, 0xE5][..]) {
        return Err(format!(
            "PUSH RBP is not followed by MOV RBP, RSP (48 89 E5); got {:02x?}",
            code.get(1..4)
        ));
    }
    let mut at = 4usize;
    let mut pushed = Vec::new();
    while let Some((reg, len)) = decode_push_r64(code, at) {
        pushed.push(reg);
        at += len;
    }
    if code.get(at..at + 3) == Some(&[0x48, 0x83, 0xEC][..]) {
        at += 4; // SUB RSP, imm8
    } else if code.get(at..at + 3) == Some(&[0x48, 0x81, 0xEC][..]) {
        at += 7; // SUB RSP, imm32
    }
    let mut xmm_stores = 0usize;
    while is_movdqu_store(code, at) {
        let (_, len) = movdqu_at(code, at).expect("just matched");
        xmm_stores += 1;
        at += len;
    }
    Ok(DecodedPrologue { pushed, xmm_stores })
}

/// The mirrored restore run: pops in reverse push order, then `POP RBP`.
fn expected_restore_run(pushed: &[u8]) -> Vec<u8> {
    let mut run = Vec::new();
    for &reg in pushed.iter().rev() {
        run.extend(encode_pop_r64(reg));
    }
    run.extend(encode_pop_r64(HW_RBP));
    run
}

/// How many times `code` contains the mirrored restore run immediately
/// followed by `RET`, allowing alignment NOPs (`0x90`) between the final
/// `POP RBP` and the `RET`. Occurrences are counted without overlap.
///
/// It is a CONTAINMENT scan, not `ends_with`: the raw-bytes emission appends
/// the function's constant pool after the code, so the last byte of the buffer
/// is generally pool data, not the return.
fn count_mirrored_restore_then_ret(code: &[u8], pushed: &[u8]) -> usize {
    let run = expected_restore_run(pushed);
    if run.is_empty() || code.len() < run.len() {
        return 0;
    }
    let mut found = 0usize;
    let mut start = 0usize;
    while start + run.len() <= code.len() {
        if &code[start..start + run.len()] != run.as_slice() {
            start += 1;
            continue;
        }
        let mut at = start + run.len();
        while code.get(at) == Some(&0x90) {
            at += 1;
        }
        if code.get(at) == Some(&0xC3) {
            found += 1;
            start = at + 1;
        } else {
            start += 1;
        }
    }
    found
}

fn has_mirrored_restore_then_ret(code: &[u8], pushed: &[u8]) -> bool {
    count_mirrored_restore_then_ret(code, pushed) > 0
}

fn find_subslice(haystack: &[u8], needle: &[u8]) -> Option<usize> {
    haystack.windows(needle.len()).position(|w| w == needle)
}

fn rfind_subslice(haystack: &[u8], needle: &[u8]) -> Option<usize> {
    haystack.windows(needle.len()).rposition(|w| w == needle)
}

fn pipeline_for(abi: X86CallAbi, opt: X86OptLevel) -> X86Pipeline {
    X86Pipeline::new(X86PipelineConfig {
        opt_level: opt,
        output_format: X86OutputFormat::RawBytes,
        emit_frame: true,
        call_abi: abi,
        ..X86PipelineConfig::default()
    })
}

fn single_lir_function(module: &trust_ir::Module, name: &str) -> LirFunction {
    permit_translate_module(module)
        .expect("callee-saved subject must lower to LIR")
        .into_iter()
        .map(|(f, _)| f)
        .find(|f| f.name == name)
        .unwrap_or_else(|| panic!("LIR function {name} not found"))
}

/// (E3): the encoder emits exactly the frame's claim, and the restore mirrors
/// the save once per exit. NOT an independent refutation — see the header.
fn encoder_faithfulness_floor(
    subject: &str,
    module: &trust_ir::Module,
    abi: X86CallAbi,
    opt: X86OptLevel,
    min_gpr_saves: usize,
    exits: usize,
) {
    let lir = single_lir_function(module, subject);
    let (code, evidence) = pipeline_for(abi, opt)
        .compile_trust_ir_function_with_regalloc_pressure_evidence(&lir)
        .unwrap_or_else(|e| panic!("{subject} must compile for {abi:?} at {opt:?}: {e:?}"));
    let decoded = decode_prologue(&code)
        .unwrap_or_else(|e| panic!("{subject} {abi:?} {opt:?}: {e}\ncode={code:02x?}"));

    assert_eq!(
        decoded.pushed.len(),
        evidence.callee_saved_gpr_save_count,
        "{subject} {abi:?} {opt:?}: the encoder emitted {} callee-saved push(es) ({:?}) but the \
         frame claims callee_saved_gpr_save_count={}",
        decoded.pushed.len(),
        decoded
            .pushed
            .iter()
            .copied()
            .map(hw_name)
            .collect::<Vec<_>>(),
        evidence.callee_saved_gpr_save_count,
    );
    assert_eq!(
        decoded.xmm_stores, evidence.callee_saved_xmm_save_count,
        "{subject} {abi:?} {opt:?}: the encoder emitted {} MOVDQU XMM save(s) but the frame claims \
         callee_saved_xmm_save_count={}",
        decoded.xmm_stores, evidence.callee_saved_xmm_save_count,
    );
    assert_eq!(
        count_movdqu_loads(&code),
        decoded.xmm_stores * exits,
        "{subject} {abi:?} {opt:?}: {} MOVDQU save(s) across {exits} exit(s) but {} MOVDQU \
         restore(s) — a saved callee-saved XMM that is never reloaded is a clobber",
        decoded.xmm_stores,
        count_movdqu_loads(&code),
    );
    let mut seen = decoded.pushed.clone();
    seen.sort_unstable();
    let before = seen.len();
    seen.dedup();
    assert_eq!(
        before,
        seen.len(),
        "{subject} {abi:?} {opt:?}: a register is pushed twice: {:?}",
        decoded
            .pushed
            .iter()
            .copied()
            .map(hw_name)
            .collect::<Vec<_>>(),
    );
    assert!(
        decoded.pushed.len() >= min_gpr_saves,
        "{subject} {abi:?} {opt:?}: only {} callee-saved GPR(s) saved ({:?}); the subject no \
         longer exercises the save/restore path",
        decoded.pushed.len(),
        decoded
            .pushed
            .iter()
            .copied()
            .map(hw_name)
            .collect::<Vec<_>>(),
    );
    let mirrored = count_mirrored_restore_then_ret(&code, &decoded.pushed);
    assert!(
        mirrored >= exits,
        "{subject} {abi:?} {opt:?}: the emitted code contains the mirrored restore run {:02x?} \
         (pops of {:?} in reverse, then POP RBP, then RET) {mirrored} time(s), but the function \
         has {exits} exit(s) and production emits an epilogue before EVERY return.\ncode={code:02x?}",
        expected_restore_run(&decoded.pushed),
        decoded
            .pushed
            .iter()
            .copied()
            .map(hw_name)
            .collect::<Vec<_>>(),
    );
    eprintln!(
        "[E3 {subject} {abi:?} {opt:?}] {} raw bytes, saved {:?}, {} XMM save(s), {mirrored} \
         mirrored restore(s) for {exits} exit(s)",
        code.len(),
        decoded
            .pushed
            .iter()
            .copied()
            .map(hw_name)
            .collect::<Vec<_>>(),
        decoded.xmm_stores,
    );
}

// ===========================================================================
// Object emission for (E2)
// ===========================================================================

fn sysv_object(module: &trust_ir::Module, opt: OptLevel) -> Vec<u8> {
    let result = Compiler::new(CompilerConfig {
        opt_level: opt,
        target: Target::X86_64,
        ..CompilerConfig::default()
    })
    .with_codegen_license(permit_unlicensed())
    .compile(module)
    .unwrap_or_else(|e| panic!("SysV x86-64 object must compile at {opt:?}: {e:?}"));
    assert!(!result.object_code.is_empty());
    result.object_code
}

/// A Windows x64 COFF object. Emitted purely as a DECODE VEHICLE: it is never
/// linked or executed on this host (see the file header).
fn win64_object(module: &trust_ir::Module, opt: OptLevel) -> Vec<u8> {
    let spec = TargetSpec::parse("x86_64-pc-windows-msvc").expect("Win64 target spec");
    let result = Compiler::new_for_target_spec(
        CompilerConfig {
            opt_level: opt,
            ..CompilerConfig::default()
        },
        spec,
    )
    .with_codegen_license(permit_unlicensed())
    .compile(module)
    .unwrap_or_else(|e| panic!("Win64 x86-64 COFF must compile at {opt:?}: {e:?}"));
    assert!(!result.object_code.is_empty());
    result.object_code
}

// ===========================================================================
// (E2)/(E3) tests
// ===========================================================================

/// A missing disassembler is a DEGRADATION, not a pass.
///
/// `SKIP: ` is the spelling `scripts/matrix_results.py` recognises (its `SKIP`
/// regex); `check_cargo_gate` fails a named gate with any runtime SKIP.
/// Without this the gate would record PASS on a host where the only comparison
/// that actually ran is the (E3) floor, which this file labels NOT independent
/// and which cannot catch a wrong saved set.
fn report_missing_objdump(what: &str) {
    eprintln!(
        "SKIP: (E2) NOT RUN for {what}: no `objdump` on this host decodes both (E2) container formats, so the INDEPENDENT \
         body-touches-vs-prologue-saves refutation could not be evaluated. Only the (E3) \
         encoder-faithfulness floor ran, and it CANNOT catch a wrong saved set."
    );
}

/// Every (E2) lane runs at every opt level, or the gate degrades loudly.
fn require_all_lanes_ran(independent_runs: usize, what: &str) {
    if independent_runs == 0 {
        report_missing_objdump(what);
        assert!(
            !has_objdump_for_all(E2_FORMATS),
            "(E2) produced no result for the {what} subject even though an `objdump` that decodes BOTH (E2) formats \
             IS present — the decode itself failed and must not be swallowed"
        );
    } else {
        assert_eq!(
            independent_runs,
            ALL_OPT.len(),
            "(E2) ran for only {independent_runs} of {} opt levels for the {what} subject; a \
             partially-evaluated obligation must not read as a pass",
            ALL_OPT.len()
        );
    }
}

#[test]
fn x86_64_sysv_frame_saves_every_callee_saved_register_the_body_uses() {
    let module = build_gpr_stress_module();
    let mut independent_runs = 0usize;
    for opt in ALL_OPT {
        if independent_frame_check(
            GPR_SUBJECT,
            X86CallAbi::SystemV,
            opt,
            &sysv_object(&module, opt),
            SYSV_GPR_OBLIGATION,
        )
        .is_some()
        {
            independent_runs += 1;
        }
    }
    for opt in ALL_X86_OPT {
        encoder_faithfulness_floor(GPR_SUBJECT, &module, X86CallAbi::SystemV, opt, 5, 1);
    }
    require_all_lanes_ran(independent_runs, "SysV GPR");
}

#[test]
fn x86_64_windows_frame_saves_every_callee_saved_register_the_body_uses() {
    // NOT EXECUTED on this host — see the file header. (E2) + (E3) only.
    let module = build_gpr_stress_module();
    let mut independent_runs = 0usize;
    for opt in ALL_OPT {
        if independent_frame_check(
            GPR_SUBJECT,
            X86CallAbi::WindowsX64,
            opt,
            &win64_object(&module, opt),
            WIN64_GPR_OBLIGATION,
        )
        .is_some()
        {
            independent_runs += 1;
        }
    }
    for opt in ALL_X86_OPT {
        encoder_faithfulness_floor(GPR_SUBJECT, &module, X86CallAbi::WindowsX64, opt, 5, 1);
    }
    require_all_lanes_ran(independent_runs, "Windows x64 GPR");
}

#[test]
fn x86_64_windows_frame_saves_every_callee_saved_xmm_the_body_uses() {
    // NOT EXECUTED on this host — see the file header. (E2) + (E3) only.
    //
    // The obligation requires ALL TEN of XMM6..XMM15 at EVERY opt level, so
    // this lane can no longer be satisfied by one callee-saved XMM save at one
    // arbitrary opt level while the other three are wholly vacuous.
    let module = build_xmm_pressure_module();
    let mut independent_runs = 0usize;
    for opt in ALL_OPT {
        if independent_frame_check(
            XMM_SUBJECT,
            X86CallAbi::WindowsX64,
            opt,
            &win64_object(&module, opt),
            WIN64_XMM_OBLIGATION,
        )
        .is_some()
        {
            independent_runs += 1;
        }
    }
    for opt in ALL_X86_OPT {
        encoder_faithfulness_floor(XMM_SUBJECT, &module, X86CallAbi::WindowsX64, opt, 0, 1);
    }
    require_all_lanes_ran(independent_runs, "Windows x64 XMM");
}

/// A function with TWO returns: production emits an epilogue before every
/// `Ret`, and a missing or misordered restore on ONE path is the most
/// plausible shape of the bug.
#[test]
fn x86_64_frame_restores_at_every_return_not_just_the_last() {
    let module = build_two_exit_module();
    let mut independent_runs = 0usize;
    for opt in ALL_OPT {
        if independent_frame_check(
            TWO_EXIT_SUBJECT,
            X86CallAbi::SystemV,
            opt,
            &sysv_object(&module, opt),
            SYSV_TWO_EXIT_OBLIGATION,
        )
        .is_some()
        {
            independent_runs += 1;
        }
        if independent_frame_check(
            TWO_EXIT_SUBJECT,
            X86CallAbi::WindowsX64,
            opt,
            &win64_object(&module, opt),
            WIN64_TWO_EXIT_OBLIGATION,
        )
        .is_some()
        {
            independent_runs += 1;
        }
    }
    for opt in ALL_X86_OPT {
        encoder_faithfulness_floor(TWO_EXIT_SUBJECT, &module, X86CallAbi::SystemV, opt, 5, 2);
        encoder_faithfulness_floor(TWO_EXIT_SUBJECT, &module, X86CallAbi::WindowsX64, opt, 5, 2);
    }
    if independent_runs == 0 {
        report_missing_objdump("two-exit");
        assert!(
            !has_objdump_for_all(E2_FORMATS),
            "(E2) produced no result for the two-exit subject even though a capable \
             `objdump` IS present"
        );
    } else {
        assert_eq!(
            independent_runs,
            2 * ALL_OPT.len(),
            "(E2) ran for only {independent_runs} of {} two-exit lanes",
            2 * ALL_OPT.len()
        );
    }
}

// ===========================================================================
// Negative controls for the DECODERS
// ===========================================================================
//
// A decoder that cannot be made to disagree is not evidence. Each control
// REFUTES for its own stated reason, and every control is COUNTED so a
// silently skipped arm cannot hide.

#[test]
fn x86_64_callee_saved_decoder_negative_controls() {
    let mut ran = 0usize;

    // ---- (E3) byte-level decoder ----
    let build = |pushes: &[u8], trailing_nop: bool| -> Vec<u8> {
        let mut code = vec![0x55, 0x48, 0x89, 0xE5];
        for &r in pushes {
            code.extend(encode_push_r64(r));
        }
        code.extend([0x48, 0x83, 0xEC, 0x20]); // SUB RSP, 0x20
        code.extend([0x48, 0x31, 0xC0]); // body: XOR RAX, RAX
        code.extend([0x48, 0x83, 0xC4, 0x20]); // ADD RSP, 0x20
        for &r in pushes.iter().rev() {
            code.extend(encode_pop_r64(r));
        }
        code.extend(encode_pop_r64(HW_RBP));
        if trailing_nop {
            code.push(0x90);
        }
        code.push(0xC3);
        code
    };
    // The full SysV allocatable callee-saved set, so the controls exercise both
    // the one-byte (RBX) and the REX.B two-byte (R12..R15) push/pop forms.
    let saved = [HW_RBX, HW_R12, HW_R13, HW_R14, HW_R15];
    let good = build(&saved, false);

    // (C0) POSITIVE anchor: a well-formed stream decodes to exactly the set,
    // with and without alignment padding before the RET.
    let decoded = decode_prologue(&good).expect("well-formed prologue must decode");
    assert_eq!(decoded.pushed, saved.to_vec());
    assert!(has_mirrored_restore_then_ret(&good, &decoded.pushed));
    assert!(has_mirrored_restore_then_ret(
        &build(&saved, true),
        &decoded.pushed
    ));
    ran += 1;

    // (C1) A DROPPED save — the shape of the AArch64 P0 on x86. The decoded
    // set shrinks, so the (E3) count comparison and (E2)'s P1 both refute.
    let mut dropped = good.clone();
    let push_r13 = encode_push_r64(HW_R13);
    let at = find_subslice(&dropped, &push_r13).expect("PUSH R13 present");
    dropped.drain(at..at + push_r13.len());
    let d = decode_prologue(&dropped).expect("still decodes");
    assert_eq!(
        d.pushed,
        vec![HW_RBX, HW_R12, HW_R14, HW_R15],
        "C1: saved set must shrink"
    );
    assert_ne!(d.pushed, saved.to_vec(), "C1 must refute the good set");
    ran += 1;

    // (C2) A save of the WRONG register: PUSH RAX (caller-saved) for PUSH RBX.
    let mut wrong = good.clone();
    let at = find_subslice(&wrong, &encode_push_r64(HW_RBX)).expect("PUSH RBX present");
    wrong[at] = 0x50 + HW_RAX;
    let d = decode_prologue(&wrong).expect("still decodes");
    assert_eq!(d.pushed[0], HW_RAX, "C2: decoder must read the swapped reg");
    assert!(
        !SYSV_ALLOCATABLE_CALLEE_SAVED.contains(&hw_name(d.pushed[0])),
        "C2: PUSH RAX must NOT be accepted as a callee-saved save"
    );
    ran += 1;

    // (C3) A restore in the WRONG ORDER. The prologue still decodes
    // identically, so only the mirrored-restore check can catch it.
    let mut misordered = good.clone();
    let n = misordered.len();
    misordered.swap(n - 3, n - 2); // POP RBX <-> POP RBP
    let d = decode_prologue(&misordered).expect("prologue unchanged");
    assert_eq!(d.pushed, saved.to_vec(), "C3: prologue is untouched");
    assert!(
        !has_mirrored_restore_then_ret(&misordered, &d.pushed),
        "C3: the mirrored-restore check must refute a restore in the wrong order"
    );
    ran += 1;

    // (C4) A MISSING restore.
    let mut no_restore = good.clone();
    let pop_r13 = encode_pop_r64(HW_R13);
    let at = rfind_subslice(&no_restore, &pop_r13).expect("POP R13 present");
    no_restore.drain(at..at + pop_r13.len());
    let d = decode_prologue(&no_restore).expect("prologue unchanged");
    assert!(
        !has_mirrored_restore_then_ret(&no_restore, &d.pushed),
        "C4: dropping a POP must refute the mirrored-restore check"
    );
    ran += 1;

    // (C5) NOT a prologue: the decoder must refuse, not invent a frame.
    assert!(
        decode_prologue(&[0x90, 0x90, 0xC3]).is_err(),
        "C5: a NOP body must not decode as a frame prologue"
    );
    assert!(
        decode_prologue(&[0x55, 0x90, 0x90, 0xC3]).is_err(),
        "C5: PUSH RBP without MOV RBP,RSP must not decode as a frame prologue"
    );
    ran += 1;

    // (C6) A MOVDQU *load* must never count as a save: the save and the restore
    // differ by exactly one opcode byte (0F 7F vs 0F 6F).
    let store = [0xF3u8, 0x0F, 0x7F, 0x45, 0xF0]; // movdqu [rbp-16], xmm0
    let load = [0xF3u8, 0x0F, 0x6F, 0x45, 0xF0]; // movdqu xmm0, [rbp-16]
    assert!(is_movdqu_store(&store, 0), "C6: the store form must decode");
    assert!(
        !is_movdqu_store(&load, 0),
        "C6: the LOAD form must NOT be accepted as a callee-saved XMM save"
    );
    assert_eq!(count_movdqu_loads(&load), 1);
    assert_eq!(count_movdqu_loads(&store), 0);
    ran += 1;

    // (C7) Push-shaped bytes that are not pushes.
    assert!(decode_push_r64(&[0x5B], 0).is_none(), "C7: POP is not PUSH");
    assert!(decode_push_r64(&[0x90], 0).is_none(), "C7: NOP is not PUSH");
    assert!(decode_pop_r64(&[0x53], 0).is_none(), "C7: PUSH is not POP");
    assert_eq!(decode_push_r64(&[0x41, 0x54], 0), Some((HW_R12, 2)));
    assert_eq!(decode_pop_r64(&[0x41, 0x5C], 0), Some((HW_R12, 2)));
    ran += 1;

    // ---- (E2) disassembly-text reader ----

    let frame = |body: Vec<DisasmInsn>, pushes: &[&str]| -> Vec<DisasmInsn> {
        control_frame(body, pushes, 1)
    };

    // (C8) POSITIVE anchor: a well-formed frame parses, and the body's
    // callee-saved mentions are exactly the ones it names.
    let body = vec![
        insn("movq", "%rdi, %rbx"),
        insn("movq", "%rsi, %r12"),
        insn("leaq", "(%rbx,%r12), %rax"),
    ];
    let view = frame_view(&frame(body.clone(), &["rbx", "r12"])).expect("well-formed frame");
    assert_eq!(view.saved_gprs, vec!["rbx", "r12"]);
    assert_eq!(view.exits.len(), 1);
    assert_eq!(view.exits[0].restored_gprs, vec!["r12", "rbx"]);
    assert!(view.body_touched.contains("rbx") && view.body_touched.contains("r12"));
    assert!(
        !view.body_touched.contains("r13"),
        "C8: the body must not be credited with a register it never mentions"
    );
    ran += 1;

    // (C9) THE OBLIGATION REFUTES. A body that uses R12 under a prologue that
    // saves only RBX: `body_touched` names a callee-saved register that
    // `saved_gprs` does not carry. This is the exact miscompile shape, and it
    // is the check the (E3) floor CANNOT make.
    let view = frame_view(&frame(body.clone(), &["rbx"])).expect("parses");
    assert!(
        view.body_touched.contains("r12") && !view.saved_gprs.contains(&"r12"),
        "C9: the independent obligation must refute a body that uses an unsaved callee-saved \
         register (touched={:?}, saved={:?})",
        view.body_touched,
        view.saved_gprs
    );
    ran += 1;

    // (C10) SUB-REGISTER WIDTH. A body that only ever writes `%r12d` still
    // clobbers R12 (a 32-bit write zero-extends the full register), so the
    // reader must fold it onto the 64-bit root rather than miss it.
    let narrow = vec![insn("movl", "%edi, %r12d"), insn("movl", "%ebx, %eax")];
    let view = frame_view(&frame(narrow, &["rbx"])).expect("parses");
    assert!(
        view.body_touched.contains("r12"),
        "C10: `%r12d` must fold onto R12"
    );
    assert!(
        view.body_touched.contains("rbx"),
        "C10: `%ebx` must fold onto RBX"
    );
    ran += 1;

    // (C11) The reader must REFUSE a stream that is not a framed function
    // rather than report an empty saved set (which would read as "nothing to
    // preserve" and pass everything).
    assert!(
        frame_view(&[insn("movq", "%rdi, %rax"), insn("retq", "")]).is_err(),
        "C11: a frameless stream must be refused, not parsed as an empty frame"
    );
    assert!(
        frame_view(&frame(body.clone(), &["rbx"])[..2]).is_err(),
        "C11: a truncated stream must be refused"
    );
    let mut no_ret = frame(body.clone(), &["rbx"]);
    no_ret.pop();
    assert!(
        frame_view(&no_ret).is_err(),
        "C11: a stream with no `retq` must be refused"
    );
    ran += 1;

    // (C12) MOVDQU direction, in disassembly text. The prologue store and the
    // epilogue load print with the operands in opposite order; conflating them
    // would let a restore-only frame read as fully saved.
    assert_eq!(
        movdqu_pair(&insn("movdqu", "%xmm6, -80(%rbp)")),
        Some(("xmm6", true, "-80(%rbp)".to_string()))
    );
    assert_eq!(
        movdqu_pair(&insn("movdqu", "-80(%rbp), %xmm6")),
        Some(("xmm6", false, "-80(%rbp)".to_string()))
    );
    assert_eq!(movdqu_pair(&insn("movaps", "%xmm6, %xmm7")), None);
    let mut with_xmm = vec![insn("pushq", "%rbp"), insn("movq", "%rsp, %rbp")];
    with_xmm.push(insn("pushq", "%rbx"));
    with_xmm.push(insn("subq", "$96, %rsp"));
    with_xmm.push(insn("movdqu", "%xmm6, -80(%rbp)"));
    with_xmm.push(insn("movdqu", "%xmm7, -96(%rbp)"));
    with_xmm.push(insn("mulsd", "%xmm1, %xmm6"));
    with_xmm.push(insn("movdqu", "-96(%rbp), %xmm7"));
    with_xmm.push(insn("movdqu", "-80(%rbp), %xmm6"));
    with_xmm.push(insn("addq", "$96, %rsp"));
    with_xmm.push(insn("popq", "%rbx"));
    with_xmm.push(insn("popq", "%rbp"));
    with_xmm.push(insn("retq", ""));
    let view = frame_view(&with_xmm).expect("XMM frame parses");
    assert_eq!(view.saved_xmm_regs(), vec!["xmm6", "xmm7"]);
    assert_eq!(
        view.exits[0]
            .restored_xmms
            .iter()
            .map(|(r, _)| *r)
            .collect::<Vec<_>>(),
        vec!["xmm7", "xmm6"]
    );
    assert!(
        view.body_touched.contains("xmm6") && !view.body_touched.contains("xmm7"),
        "C12: the save/restore instructions themselves must not be counted as body uses \
         (touched={:?})",
        view.body_touched
    );
    ran += 1;

    // (C13) TOTALITY. Every decoder must answer for EVERY byte without
    // panicking, and must accept EXACTLY the encodings the SDM assigns. This
    // control exists because the first version of `decode_push_r64` used
    // `cond.then_some(b - 0x50)`: `then_some` is EAGER, so the subtraction ran
    // for rejected bytes too and underflowed. Release builds wrap and discard
    // it — the battery was green — while a debug build (the profile
    // `soundness_check.sh` uses) panicked in all four consumers.
    let mut accepted_push: Vec<u8> = Vec::new();
    let mut accepted_pop: Vec<u8> = Vec::new();
    for b in 0u16..=0xFF {
        let byte = b as u8;
        // One-byte forms.
        if let Some((reg, len)) = decode_push_r64(&[byte, 0x00], 0) {
            assert_eq!(len, if byte == 0x41 { 2 } else { 1 });
            if byte != 0x41 {
                accepted_push.push(reg);
            }
        }
        if let Some((reg, len)) = decode_pop_r64(&[byte, 0x00], 0) {
            assert_eq!(len, if byte == 0x41 { 2 } else { 1 });
            if byte != 0x41 {
                accepted_pop.push(reg);
            }
        }
        // REX.B two-byte forms, and the empty/truncated inputs.
        let _ = decode_push_r64(&[0x41, byte], 0);
        let _ = decode_pop_r64(&[0x41, byte], 0);
        let _ = decode_push_r64(&[byte], 0);
        let _ = decode_pop_r64(&[byte], 0);
        let _ = movdqu_at(&[byte], 0);
        let _ = movdqu_at(&[0xF3, byte], 0);
        let _ = movdqu_at(&[0xF3, 0x0F, byte, 0x45, 0xF0], 0);
        let _ = movdqu_at(&[0xF3, 0x0F, 0x7F, byte], 0);
        let _ = decode_prologue(&[byte]);
        let _ = count_movdqu_loads(&[byte, 0xF3, 0x0F]);
        let _ = memory_operand(&format!("{byte}(%rbp)"));
    }
    assert!(decode_push_r64(&[], 0).is_none(), "C13: empty input");
    assert!(decode_pop_r64(&[], 0).is_none(), "C13: empty input");
    assert!(decode_push_r64(&[0x41], 0).is_none(), "C13: truncated REX");
    assert!(decode_pop_r64(&[0x41], 0).is_none(), "C13: truncated REX");
    assert_eq!(
        accepted_push,
        (0u8..=7).collect::<Vec<_>>(),
        "C13: PUSH r64 must accept EXACTLY 50+rd for rax..rdi and nothing else"
    );
    assert_eq!(
        accepted_pop,
        (0u8..=7).collect::<Vec<_>>(),
        "C13: POP r64 must accept EXACTLY 58+rd for rax..rdi and nothing else"
    );
    for reg in 8u8..=15 {
        assert_eq!(
            decode_push_r64(&encode_push_r64(reg), 0),
            Some((reg, 2)),
            "C13: the REX.B PUSH form must round-trip for {}",
            hw_name(reg)
        );
        assert_eq!(
            decode_pop_r64(&encode_pop_r64(reg), 0),
            Some((reg, 2)),
            "C13: the REX.B POP form must round-trip for {}",
            hw_name(reg)
        );
    }
    ran += 1;

    // (C14) A REGISTER-DIRECT MOVDQU STORES NOTHING. Both recognizers claim to
    // report a store to, or a reload from, a frame SLOT. `movdqu %xmm6, %xmm7`
    // writes no memory at all, so crediting it would count a callee-saved save
    // that never happened — and a prologue made entirely of such moves would
    // read as fully saved.
    assert_eq!(
        movdqu_pair(&insn("movdqu", "%xmm6, %xmm7")),
        None,
        "C14: a register-to-register `movdqu` must not be read as an XMM frame save"
    );
    assert_eq!(
        movdqu_pair(&insn("movdqu", "%xmm7, %xmm6")),
        None,
        "C14: nor in the other operand order"
    );
    // The byte decoder, at ModRM.mod = 0b11 (`F3 0F 7F F7` = movdqu xmm7, xmm6).
    assert_eq!(
        movdqu_at(&[0xF3, 0x0F, 0x7F, 0xF7], 0),
        None,
        "C14: ModRM.mod=11 is register-direct and must not decode as a MOVDQU frame store"
    );
    assert_eq!(
        movdqu_at(&[0xF3, 0x0F, 0x6F, 0xF7], 0),
        None,
        "C14: nor as a MOVDQU frame reload"
    );
    assert!(
        !is_movdqu_store(&[0xF3, 0x0F, 0x7F, 0xF7], 0),
        "C14: is_movdqu_store must refuse the register-direct form"
    );
    assert_eq!(
        count_movdqu_loads(&[0xF3, 0x0F, 0x6F, 0xF7]),
        0,
        "C14: count_movdqu_loads must refuse the register-direct form"
    );
    // A prologue whose only "XMM save" is register-direct must decode as ZERO
    // saves, not as one.
    let mut reg_direct = vec![0x55u8, 0x48, 0x89, 0xE5, 0x48, 0x83, 0xEC, 0x20];
    reg_direct.extend([0xF3, 0x0F, 0x7F, 0xF7]);
    assert_eq!(
        decode_prologue(&reg_direct).expect("decodes").xmm_stores,
        0,
        "C14: a register-direct `movdqu` in the prologue must not be counted as a frame save"
    );
    // ... and neither must a non-memory second operand in disassembly text.
    assert_eq!(memory_operand("%xmm7"), None);
    assert_eq!(memory_operand("$32"), None);
    assert_eq!(memory_operand("-80(%rbp)"), Some("-80(%rbp)"));
    ran += 1;

    // (C15) MULTI-EXIT. The reader must inspect the epilogue at EVERY return,
    // not only the last one. A frame that restores correctly at its final exit
    // and drops a pop at the first one is exactly the bug the two-exit subject
    // exists for, and the single-epilogue reader could not see it.
    let two = control_frame(body.clone(), &["rbx", "r12"], 2);
    let view = frame_view(&two).expect("two-exit frame parses");
    assert_eq!(view.exits.len(), 2, "C15: both returns must be found");
    assert!(
        view.exits
            .iter()
            .all(|e| e.restored_gprs == vec!["r12", "rbx"]),
        "C15: both epilogues must be read"
    );
    // Drop `popq %r12` from the FIRST epilogue only.
    let mut broken = two.clone();
    let first_pop = broken
        .iter()
        .position(|i| i.mnemonic == "popq" && i.operands.contains("r12"))
        .expect("first epilogue pops r12");
    broken.remove(first_pop);
    let view = frame_view(&broken).expect("still parses");
    assert_ne!(
        view.exits[0].restored_gprs, view.exits[1].restored_gprs,
        "C15: a dropped pop at the FIRST exit must be visible; exits read {:?}",
        view.exits
    );
    assert_eq!(
        view.exits[1].restored_gprs,
        vec!["r12", "rbx"],
        "C15: the LAST exit is still correct, which is why a last-exit-only reader is blind"
    );
    ran += 1;

    // (C16) XMM SAVE-SLOT IDENTITY. A restore from the wrong displacement
    // reloads the wrong 16 bytes into a callee-saved register. The reader must
    // carry the printed slot, not just the register name.
    let mut wrong_slot = with_xmm.clone();
    for i in wrong_slot.iter_mut() {
        if i.mnemonic == "movdqu" && i.operands.starts_with("-80(") {
            i.operands = "-112(%rbp), %xmm6".to_string();
        }
    }
    let view = frame_view(&wrong_slot).expect("parses");
    assert_eq!(
        view.saved_xmms,
        vec![
            ("xmm6", "-80(%rbp)".to_string()),
            ("xmm7", "-96(%rbp)".to_string())
        ]
    );
    assert_eq!(
        view.exits[0].restored_xmms,
        vec![
            ("xmm7", "-96(%rbp)".to_string()),
            ("xmm6", "-112(%rbp)".to_string())
        ],
        "C16: the reader must report the slot the epilogue actually reloads from"
    );
    ran += 1;

    assert_eq!(
        ran, 17,
        "the decoder control battery must run all 17 controls; ran {ran}"
    );
}

fn insn(mnemonic: &str, operands: &str) -> DisasmInsn {
    DisasmInsn {
        offset: 0,
        mnemonic: mnemonic.to_string(),
        operands: operands.to_string(),
    }
}

/// A synthetic framed function with `exits` mirrored epilogues, used by the
/// control batteries.
fn control_frame(body: Vec<DisasmInsn>, pushes: &[&str], exits: usize) -> Vec<DisasmInsn> {
    let mut v = vec![insn("pushq", "%rbp"), insn("movq", "%rsp, %rbp")];
    for p in pushes {
        v.push(insn("pushq", &format!("%{p}")));
    }
    v.push(insn("subq", "$32, %rsp"));
    v.extend(body);
    for _ in 0..exits {
        v.push(insn("addq", "$32, %rsp"));
        for p in pushes.iter().rev() {
            v.push(insn("popq", &format!("%{p}")));
        }
        v.push(insn("popq", "%rbp"));
        v.push(insn("retq", ""));
    }
    v
}

// ===========================================================================
// The DECODE'S PROVENANCE: every (E2) verdict is about the object it names
// ===========================================================================
//
// These two tests exist because the previous landing shipped a ~11% flake whose
// cause was NOT a compiler defect: `common/disasm.rs` built its scratch
// directory from `SystemTime::now().as_nanos()`, which is MICROSECOND-resolution
// on this host, so two concurrent decodes could land on one path and each
// `objdump` could read the OTHER's object. The failures that produced
// ("SystemV saves rsi", "the Win64 body reads RDI") were TRUE STATEMENTS ABOUT
// THE WRONG SUBJECT. An obligation evaluated against someone else's object is
// not weak evidence — it is evidence about nothing.

/// The scratch path is unique PER CALL. Before the fix it was unique only per
/// process and wall-clock instant.
#[test]
fn x86_64_disassembly_scratch_paths_are_unique_per_call() {
    const N: usize = 4096;
    let paths: BTreeSet<PathBuf> = (0..N).map(|_| disasm_scratch_dir()).collect();
    assert_eq!(
        paths.len(),
        N,
        "the disassembly scratch path is NOT unique per call ({} distinct of {N}); two concurrent \
         decodes can then write their objects to the same file and read each other's",
        paths.len()
    );

    // Why the clock alone was not enough, measured rather than asserted from
    // memory: rapid `SystemTime::now()` readings repeat on this host.
    let mut clock: Vec<u128> = Vec::with_capacity(N);
    for _ in 0..N {
        clock.push(
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap_or_default()
                .as_nanos(),
        );
    }
    let distinct: BTreeSet<u128> = clock.iter().copied().collect();
    eprintln!(
        "[provenance] {N} rapid SystemTime readings produced {} distinct values — the \
         pid+clock-only path would have collided {} time(s)",
        distinct.len(),
        N - distinct.len()
    );
}

/// CONCURRENT decodes of DIFFERENT objects never report each other's frame.
///
/// This is the skeptic's observed failure reproduced as an assertion: the SysV
/// and Win64 objects of the same subject differ in a way the reader can name
/// (Win64 saves RSI, SysV cannot), so a swapped decode is detected rather than
/// merely improbable.
#[test]
fn x86_64_concurrent_disassembly_never_decodes_another_subjects_object() {
    if !has_objdump_for_all(E2_FORMATS) {
        eprintln!(
            "SKIP: the decode-provenance control needs an `objdump` that decodes BOTH (E2) formats; without it (E2) \
             does not run at all and this control has nothing to guard."
        );
        return;
    }
    let module = build_gpr_stress_module();
    let sysv = sysv_object(&module, OptLevel::O2);
    let win64 = win64_object(&module, OptLevel::O2);
    assert_ne!(sysv, win64, "the two lanes must emit different objects");

    let sysv_ref = disassemble_x86_text(&sysv).expect("SysV decode");
    let win64_ref = disassemble_x86_text(&win64).expect("Win64 decode");
    let sysv_saved = frame_view(&sysv_ref).expect("SysV frame").saved_gprs;
    let win64_saved = frame_view(&win64_ref).expect("Win64 frame").saved_gprs;
    assert!(
        win64_saved.contains(&"rsi") && !sysv_saved.contains(&"rsi"),
        "the control needs the two objects to be DISTINGUISHABLE by the reader; SysV saved {:?}, \
         Win64 saved {:?}",
        sysv_saved,
        win64_saved
    );

    // Four threads, alternating lanes, decoding at the same time. Under the old
    // pid+clock path this reported the wrong frame in roughly 1 run in 10.
    const ROUNDS: usize = 24;
    let mut handles = Vec::new();
    for thread in 0..4usize {
        let sysv = sysv.clone();
        let win64 = win64.clone();
        let want_sysv = thread % 2 == 0;
        handles.push(std::thread::spawn(move || {
            for round in 0..ROUNDS {
                let object = if want_sysv { &sysv } else { &win64 };
                let insns = disassemble_x86_text(object).expect("decode");
                let saved = frame_view(&insns).expect("frame").saved_gprs;
                assert_eq!(
                    saved.contains(&"rsi"),
                    !want_sysv,
                    "thread {thread} round {round} decoded the OTHER lane's object: it asked for \
                     the {} frame and read {saved:?}",
                    if want_sysv { "SysV" } else { "Win64" }
                );
            }
        }));
    }
    for handle in handles {
        handle
            .join()
            .expect("a concurrent decode reported the wrong subject's frame");
    }
    eprintln!(
        "[provenance] {} concurrent decodes, none crossed lanes",
        4 * ROUNDS
    );
}

// ===========================================================================
// Negative controls for the ENFORCING OBLIGATION ITSELF
// ===========================================================================
//
// The battery above exercises the extraction helpers. This one DRIVES
// `check_frame_obligation` — the function that actually decides whether a lane
// is green — with inputs that must refute, and checks the refusal names the
// right facet. Without it, (P0)-(P6) could be inverted, weakened or deleted
// with every decoder control still passing.

fn panic_text(err: &(dyn std::any::Any + Send)) -> String {
    if let Some(s) = err.downcast_ref::<&str>() {
        (*s).to_string()
    } else if let Some(s) = err.downcast_ref::<String>() {
        s.clone()
    } else {
        "<non-string panic payload>".to_string()
    }
}

/// The obligation must REFUSE `insns`, and the refusal must name `because`.
fn obligation_refutes(
    control: &str,
    abi: X86CallAbi,
    insns: &[DisasmInsn],
    ob: FrameObligation,
    because: &str,
) {
    let outcome = catch_unwind(AssertUnwindSafe(|| {
        check_frame_obligation("control-subject", abi, OptLevel::O0, insns, ob)
    }));
    let err = match outcome {
        Ok(view) => panic!(
            "{control}: the OBLIGATION DID NOT REFUTE — it accepted a frame it must reject \
             (saved={:?}, body={:?}). The teeth of (E2) are gone.",
            view.saved_gprs, view.body_touched
        ),
        Err(err) => err,
    };
    let message = panic_text(err.as_ref());
    assert!(
        message.contains(because),
        "{control}: the obligation refuted for the WRONG reason. Expected a refusal naming \
         `{because}`, got:\n{message}"
    );
}

/// The obligation must ACCEPT `insns`. A battery in which everything refutes
/// proves nothing — this is the positive anchor that keeps the others honest.
fn obligation_accepts(control: &str, abi: X86CallAbi, insns: &[DisasmInsn], ob: FrameObligation) {
    let outcome = catch_unwind(AssertUnwindSafe(|| {
        check_frame_obligation("control-subject", abi, OptLevel::O0, insns, ob)
    }));
    if let Err(err) = outcome {
        panic!(
            "{control}: the obligation REFUSED a frame that satisfies it:\n{}",
            panic_text(err.as_ref())
        );
    }
}

#[test]
fn x86_64_callee_saved_obligation_negative_controls() {
    eprintln!(
        "[obligation controls] the panic messages printed below are EXPECTED refutations: each \
         control drives `check_frame_obligation` with an input that MUST be rejected."
    );
    let mut ran = 0usize;

    // A frame that satisfies every facet: five callee-saved GPRs saved, all
    // five mentioned in the body, four of them on both sides of the call.
    let five = ["rbx", "r12", "r13", "r14", "r15"];
    let good_body = || {
        vec![
            insn("movq", "%rdi, %rbx"),
            insn("movq", "%rsi, %r12"),
            insn("movq", "%rdx, %r13"),
            insn("movq", "%rcx, %r14"),
            insn("movq", "%r8, %r15"),
            insn("callq", "*%rbx"),
            insn("leaq", "(%rax,%r12), %rcx"),
            insn("addq", "%r13, %rcx"),
            insn("addq", "%r14, %rcx"),
            insn("addq", "%r15, %rax"),
        ]
    };
    let ob = FrameObligation {
        require_saved_gprs: &SYSV_ALLOCATABLE_CALLEE_SAVED,
        require_saved_xmms: &[],
        min_body_cs_gprs: 5,
        min_body_cs_xmms: 0,
        min_held_across_call: 4,
        exits: 1,
    };

    // (O0) POSITIVE ANCHOR.
    obligation_accepts(
        "O0",
        X86CallAbi::SystemV,
        &control_frame(good_body(), &five, 1),
        ob,
    );
    ran += 1;

    // (O1) (P0) SOURCE-SIDE VACUITY — the skeptics' primary attack. A frame
    // that saves all five callee-saved GPRs while the body mentions NONE makes
    // (P1)'s loop range over an empty set. The old check passed; this one must
    // not.
    let vacuous_body = vec![
        insn("movq", "%rdi, %rax"),
        insn("callq", "*%rax"),
        insn("addq", "%rcx, %rax"),
    ];
    obligation_refutes(
        "O1",
        X86CallAbi::SystemV,
        &control_frame(vacuous_body, &five, 1),
        ob,
        "VACUOUS OBLIGATION",
    );
    ran += 1;

    // (O2) (P1) the miscompile itself: a body that uses R12 under a prologue
    // that does not save it.
    let mut unsaved = good_body();
    unsaved.push(insn("movq", "%r12, %rax"));
    obligation_refutes(
        "O2",
        X86CallAbi::SystemV,
        &control_frame(unsaved, &["rbx", "r13", "r14", "r15"], 1),
        FrameObligation {
            require_saved_gprs: &["rbx", "r13", "r14", "r15"],
            ..ob
        },
        "MISCOMPILE — the body uses callee-saved",
    );
    ran += 1;

    // (O3) (P2) a restore that is not the exact reverse. Two callee-saved pops
    // are transposed (`popq %r12` <-> `popq %rbx`), so the run is still a
    // well-formed pop run ending in `popq %rbp` — the reader parses it happily
    // and only the mirror comparison can refuse it.
    let mut misordered = control_frame(good_body(), &five, 1);
    let n = misordered.len();
    misordered.swap(n - 4, n - 3);
    obligation_refutes(
        "O3",
        X86CallAbi::SystemV,
        &misordered,
        ob,
        "the restore must be the exact reverse",
    );
    ran += 1;

    // (O4) (P3) a push of a register that is NOT callee-saved under this ABI.
    // RSI is callee-saved under Win64 and caller-saved under SysV, so the SAME
    // frame is accepted for one ABI and refused for the other — the check is
    // reading the ABI, not a constant.
    //
    // The body takes its arguments from the WIN64 argument registers
    // (RCX/RDX/R8/R9 plus an RBP-relative 5th), because RDI and RSI are
    // callee-saved under Win64: a body written in SysV argument registers
    // would be refused by (P1) for mentioning an unsaved RDI, and this control
    // is about (P3).
    let with_rsi = vec![
        insn("movq", "%rcx, %rbx"),
        insn("movq", "%rdx, %r12"),
        insn("movq", "%r8, %r13"),
        insn("movq", "%r9, %r14"),
        insn("movq", "48(%rbp), %r15"),
        insn("callq", "*%rbx"),
        insn("leaq", "(%rax,%r12), %rcx"),
        insn("addq", "%r13, %rcx"),
        insn("addq", "%r14, %rcx"),
        insn("addq", "%r15, %rax"),
        insn("movq", "%rsi, %rax"),
    ];
    let rsi_frame = control_frame(with_rsi, &["rbx", "rsi", "r12", "r13", "r14", "r15"], 1);
    obligation_refutes(
        "O4",
        X86CallAbi::SystemV,
        &rsi_frame,
        ob,
        "which is NOT an allocatable callee-saved register under this ABI",
    );
    obligation_accepts("O4-win64", X86CallAbi::WindowsX64, &rsi_frame, ob);
    ran += 1;

    // (O5) (P4) DESIGNED STRENGTH. The mutation "make the subject stop holding
    // values across the call" collapsed the saved set from five registers to
    // two and every structural test stayed green, because each one asked only
    // for `>= 1`. A lane built for five must refuse four.
    //
    // The shrunken frame is internally CONSISTENT — the body mentions exactly
    // the four registers the prologue saves, so (P0), (P1), (P2), (P3) and
    // (P5) are all satisfied. Only the statement of the lane's designed
    // strength can tell that R15 has dropped out of the exercised set.
    let four_body = vec![
        insn("movq", "%rdi, %rbx"),
        insn("movq", "%rsi, %r12"),
        insn("movq", "%rdx, %r13"),
        insn("movq", "%rcx, %r14"),
        insn("callq", "*%rbx"),
        insn("leaq", "(%rax,%r12), %rcx"),
        insn("addq", "%r13, %rcx"),
        insn("addq", "%r14, %rax"),
    ];
    let four = ["rbx", "r12", "r13", "r14"];
    let ob_four = FrameObligation {
        min_body_cs_gprs: 4,
        min_held_across_call: 3,
        ..ob
    };
    obligation_accepts(
        "O5-anchor",
        X86CallAbi::SystemV,
        &control_frame(four_body.clone(), &four, 1),
        FrameObligation {
            require_saved_gprs: &["rbx", "r12", "r13", "r14"],
            ..ob_four
        },
    );
    obligation_refutes(
        "O5",
        X86CallAbi::SystemV,
        &control_frame(four_body, &four, 1),
        ob_four,
        "the prologue does NOT save",
    );
    ran += 1;

    // (O6) (P5) HAZARD WITNESS. Every callee-saved register is written BEFORE
    // the call and never read after it: the subject parks nothing across the
    // call, so the execution oracle's `mask == 0` would be trivially true.
    let no_hazard = vec![
        insn("movq", "%rdi, %rbx"),
        insn("movq", "%rsi, %r12"),
        insn("movq", "%rdx, %r13"),
        insn("movq", "%rcx, %r14"),
        insn("movq", "%r8, %r15"),
        insn("callq", "*%rax"),
        insn("addq", "%rcx, %rax"),
    ];
    obligation_refutes(
        "O6",
        X86CallAbi::SystemV,
        &control_frame(no_hazard, &five, 1),
        ob,
        "NO HAZARD EXERCISED",
    );
    ran += 1;

    // (O7) (P6) the exit count is CHECKED. A two-exit frame judged under a
    // one-exit statement must refuse rather than quietly cover less.
    obligation_refutes(
        "O7",
        X86CallAbi::SystemV,
        &control_frame(good_body(), &five, 2),
        ob,
        "return(s), not the 1 this lane states",
    );
    obligation_accepts(
        "O7-two-exit",
        X86CallAbi::SystemV,
        &control_frame(good_body(), &five, 2),
        FrameObligation { exits: 2, ..ob },
    );
    ran += 1;

    // (O8) (P2) MULTI-EXIT teeth: a pop dropped from the FIRST epilogue only.
    // The last exit is still perfect, so a reader that walked back from the
    // final `retq` would pass this.
    let mut broken = control_frame(good_body(), &five, 2);
    let first_pop = broken
        .iter()
        .position(|i| i.mnemonic == "popq" && i.operands.contains("r12"))
        .expect("first epilogue pops r12");
    broken.remove(first_pop);
    obligation_refutes(
        "O8",
        X86CallAbi::SystemV,
        &broken,
        FrameObligation { exits: 2, ..ob },
        "the restore must be the exact reverse",
    );
    ran += 1;

    // (O9) (P2) XMM SAVE-SLOT IDENTITY — the mutation "add 16 to the Win64 XMM
    // epilogue reload displacement", which the previous landing DECLARED would
    // survive. It no longer does.
    let xmm_body = vec![insn("mulsd", "%xmm1, %xmm6"), insn("addsd", "%xmm7, %xmm6")];
    let xmm_frame = |restore_slot_6: &str| -> Vec<DisasmInsn> {
        let mut v = vec![insn("pushq", "%rbp"), insn("movq", "%rsp, %rbp")];
        v.push(insn("subq", "$96, %rsp"));
        v.push(insn("movdqu", "%xmm6, -80(%rbp)"));
        v.push(insn("movdqu", "%xmm7, -96(%rbp)"));
        v.extend(xmm_body.clone());
        v.push(insn("movdqu", "-96(%rbp), %xmm7"));
        v.push(insn("movdqu", &format!("{restore_slot_6}, %xmm6")));
        v.push(insn("addq", "$96, %rsp"));
        v.push(insn("popq", "%rbp"));
        v.push(insn("retq", ""));
        v
    };
    let xmm_ob = FrameObligation {
        require_saved_gprs: &[],
        require_saved_xmms: &["xmm6", "xmm7"],
        min_body_cs_gprs: 0,
        min_body_cs_xmms: 2,
        min_held_across_call: 0,
        exits: 1,
    };
    obligation_accepts(
        "O9-anchor",
        X86CallAbi::WindowsX64,
        &xmm_frame("-80(%rbp)"),
        xmm_ob,
    );
    obligation_refutes(
        "O9",
        X86CallAbi::WindowsX64,
        &xmm_frame("-64(%rbp)"),
        xmm_ob,
        "must be reloaded from the SAME frame slot",
    );
    ran += 1;

    // (O10) (P0)/(P4) for the XMM lane: a frame that saves ONE callee-saved
    // XMM cannot satisfy a lane that claims XMM6..XMM15. This is the shape the
    // old `saw_xmm_save |= ...` flag accepted for the whole test.
    let one_xmm = {
        let mut v = vec![insn("pushq", "%rbp"), insn("movq", "%rsp, %rbp")];
        v.push(insn("subq", "$32, %rsp"));
        v.push(insn("movdqu", "%xmm6, -16(%rbp)"));
        v.push(insn("mulsd", "%xmm1, %xmm6"));
        v.push(insn("movdqu", "-16(%rbp), %xmm6"));
        v.push(insn("addq", "$32, %rsp"));
        v.push(insn("popq", "%rbp"));
        v.push(insn("retq", ""));
        v
    };
    obligation_refutes(
        "O10",
        X86CallAbi::WindowsX64,
        &one_xmm,
        WIN64_XMM_OBLIGATION,
        "VACUOUS OBLIGATION",
    );
    ran += 1;

    assert_eq!(
        ran, 11,
        "the obligation control battery must run all 11 controls; ran {ran}"
    );
}

// ===========================================================================
// (E1) Execution — the real oracle
// ===========================================================================

/// The assembly probe plus its negative-control callees.
///
/// Both an underscore-prefixed (Mach-O) and a bare (ELF) label is defined for
/// every symbol so the same source assembles on either object format.
///
/// `tcg_cs_probe(fn, args, out)`:
///   * saves the six System V callee-saved GPRs,
///   * loads `args[0..6]` into RDI, RSI, RDX, RCX, R8, R9,
///   * pins a distinct sentinel in RBX, RBP, R12, R13, R14, R15,
///   * calls `fn`,
///   * stores the i64 return value through `out`,
///   * returns a bitmask — bit0 RBX, bit1 RBP, bit2 R12, bit3 R13, bit4 R14,
///     bit5 R15 — set when that register's sentinel did NOT survive.
///
/// Every control callee returns its OWN distinct value. The control harness
/// checks that value, so a control cannot be silently repointed at a different
/// callee while still counting itself and comparing a mask.
///
/// Stack alignment: at entry RSP = 8 (mod 16); six pushes preserve that, and
/// `subq $40` brings RSP to 0 (mod 16) for the call, as System V requires. The
/// probe deliberately uses NO frame pointer, because it overwrites RBP.
const PROBE_ASM: &str = r#"
    .text

    .p2align 4
    .globl _tcg_cs_probe
    .globl tcg_cs_probe
_tcg_cs_probe:
tcg_cs_probe:
    pushq   %rbp
    pushq   %rbx
    pushq   %r12
    pushq   %r13
    pushq   %r14
    pushq   %r15
    subq    $40, %rsp
    movq    %rdi, 0(%rsp)          /* fn  */
    movq    %rdx, 8(%rsp)          /* out */
    movq    40(%rsi), %r9
    movq    32(%rsi), %r8
    movq    24(%rsi), %rcx
    movq    16(%rsi), %rdx
    movq    0(%rsi), %rdi
    movq    8(%rsi), %rsi
    movabsq $0x5EC0DE0000000001, %rbx
    movabsq $0x5EC0DE0000000002, %rbp
    movabsq $0x5EC0DE0000000003, %r12
    movabsq $0x5EC0DE0000000004, %r13
    movabsq $0x5EC0DE0000000005, %r14
    movabsq $0x5EC0DE0000000006, %r15
    callq   *(%rsp)
    movq    8(%rsp), %rcx
    movq    %rax, (%rcx)
    xorl    %eax, %eax
    movabsq $0x5EC0DE0000000001, %rdx
    cmpq    %rdx, %rbx
    je      1f
    orl     $1, %eax
1:
    movabsq $0x5EC0DE0000000002, %rdx
    cmpq    %rdx, %rbp
    je      2f
    orl     $2, %eax
2:
    movabsq $0x5EC0DE0000000003, %rdx
    cmpq    %rdx, %r12
    je      3f
    orl     $4, %eax
3:
    movabsq $0x5EC0DE0000000004, %rdx
    cmpq    %rdx, %r13
    je      4f
    orl     $8, %eax
4:
    movabsq $0x5EC0DE0000000005, %rdx
    cmpq    %rdx, %r14
    je      5f
    orl     $16, %eax
5:
    movabsq $0x5EC0DE0000000006, %rdx
    cmpq    %rdx, %r15
    je      6f
    orl     $32, %eax
6:
    addq    $40, %rsp
    popq    %r15
    popq    %r14
    popq    %r13
    popq    %r12
    popq    %rbx
    popq    %rbp
    retq

/* The sink the trust-cg subject calls: returns n+1 and then DIRTIES every
   System V caller-saved register, so a value the subject wrongly parked in a
   volatile register across the call is destroyed. It preserves
   RBX/RBP/R12-R15/RSP — it is a CONFORMING SysV callee. */
    .p2align 4
    .globl _tcg_cs_sink
    .globl tcg_cs_sink
_tcg_cs_sink:
tcg_cs_sink:
    leaq    1(%rdi), %rax
    movabsq $0xDEADBEEFDEADBEEF, %rcx
    movq    %rcx, %rdx
    movq    %rcx, %rsi
    movq    %rcx, %rdi
    movq    %rcx, %r8
    movq    %rcx, %r9
    movq    %rcx, %r10
    movq    %rcx, %r11
    movq    %rcx, %xmm0
    movapd  %xmm0, %xmm1
    movapd  %xmm0, %xmm2
    movapd  %xmm0, %xmm3
    movapd  %xmm0, %xmm4
    movapd  %xmm0, %xmm5
    movapd  %xmm0, %xmm6
    movapd  %xmm0, %xmm7
    movapd  %xmm0, %xmm8
    movapd  %xmm0, %xmm9
    movapd  %xmm0, %xmm10
    movapd  %xmm0, %xmm11
    movapd  %xmm0, %xmm12
    movapd  %xmm0, %xmm13
    movapd  %xmm0, %xmm14
    movapd  %xmm0, %xmm15
    retq

/* NEGATIVE CONTROLS: callees that clobber a KNOWN callee-saved subset. Each
   must make the probe report EXACTLY its own mask, AND return its own distinct
   value, so a control repointed at a different callee is caught even when its
   expected mask is edited to match. Without these the probe could be blind and
   every run would be a green lie. */

    .p2align 4
    .globl _tcg_cs_clean
    .globl tcg_cs_clean
_tcg_cs_clean:
tcg_cs_clean:
    movq    $0xC1EA0, %rax
    retq

    .p2align 4
    .globl _tcg_cs_bad_rbx
    .globl tcg_cs_bad_rbx
_tcg_cs_bad_rbx:
tcg_cs_bad_rbx:
    xorl    %ebx, %ebx
    movq    $0xBAD01, %rax
    retq

    .p2align 4
    .globl _tcg_cs_bad_rbp
    .globl tcg_cs_bad_rbp
_tcg_cs_bad_rbp:
tcg_cs_bad_rbp:
    xorl    %ebp, %ebp
    movq    $0xBAD02, %rax
    retq

    .p2align 4
    .globl _tcg_cs_bad_r12
    .globl tcg_cs_bad_r12
_tcg_cs_bad_r12:
tcg_cs_bad_r12:
    xorl    %r12d, %r12d
    movq    $0xBAD04, %rax
    retq

    .p2align 4
    .globl _tcg_cs_bad_r13
    .globl tcg_cs_bad_r13
_tcg_cs_bad_r13:
tcg_cs_bad_r13:
    xorl    %r13d, %r13d
    movq    $0xBAD08, %rax
    retq

    .p2align 4
    .globl _tcg_cs_bad_r14
    .globl tcg_cs_bad_r14
_tcg_cs_bad_r14:
tcg_cs_bad_r14:
    xorl    %r14d, %r14d
    movq    $0xBAD10, %rax
    retq

    .p2align 4
    .globl _tcg_cs_bad_r15
    .globl tcg_cs_bad_r15
_tcg_cs_bad_r15:
tcg_cs_bad_r15:
    xorl    %r15d, %r15d
    movq    $0xBAD20, %rax
    retq

    .p2align 4
    .globl _tcg_cs_bad_all
    .globl tcg_cs_bad_all
_tcg_cs_bad_all:
tcg_cs_bad_all:
    xorl    %ebx, %ebx
    xorl    %ebp, %ebp
    xorl    %r12d, %r12d
    xorl    %r13d, %r13d
    xorl    %r14d, %r14d
    xorl    %r15d, %r15d
    movq    $0xBAD3F, %rax
    retq
"#;

/// Driver exit codes, so a failure names itself:
///   1 = the trust-cg subject clobbered a callee-saved GPR (the miscompile)
///   2 = the trust-cg subject returned the wrong value
///   3 = the negative-control battery did not run to completion
///   4 = a negative control did not refute for its stated reason
const DRIVER_C: &str = r#"
#include <stdio.h>
#include <stdint.h>

extern long tcg_cs_probe(void *fn, const long *args, long *out);
extern long tcg_cs_sink(long);
extern long tcg_cs_stress(long (*)(long), long, long, long, long, long);

extern long tcg_cs_clean(void);
extern long tcg_cs_bad_rbx(void);
extern long tcg_cs_bad_rbp(void);
extern long tcg_cs_bad_r12(void);
extern long tcg_cs_bad_r13(void);
extern long tcg_cs_bad_r14(void);
extern long tcg_cs_bad_r15(void);
extern long tcg_cs_bad_all(void);

static int controls_run = 0;
static int control_failures = 0;

/* `want_ret` is the callee's OWN identifying value. Checking it is what stops
   a control from being silently repointed at a different callee: matching the
   mask alone is satisfied by `tcg_cs_clean` for any control whose expected
   mask is edited to 0. */
static void control(const char *name, void *fn, long want_mask, long want_ret) {
    long args[6] = { 0, 0, 0, 0, 0, 0 };
    long out = 0;
    long mask = tcg_cs_probe(fn, args, &out);
    controls_run++;
    if (mask != want_mask) {
        printf("*** CONTROL %s DID NOT REFUTE: mask=0x%lx want=0x%lx\n",
               name, mask, want_mask);
        control_failures++;
        return;
    }
    if (out != want_ret) {
        printf("*** CONTROL %s CALLED THE WRONG CALLEE: ret=0x%lx want=0x%lx\n",
               name, out, want_ret);
        control_failures++;
        return;
    }
    printf("control %s: mask=0x%lx ret=0x%lx (as stated)\n", name, mask, out);
}

int main(void) {
    /* The probe's teeth, one register at a time. */
    control("clean(no clobber)", (void *) tcg_cs_clean,   0x00, 0xC1EA0);
    control("clobbers rbx",      (void *) tcg_cs_bad_rbx, 0x01, 0xBAD01);
    control("clobbers rbp",      (void *) tcg_cs_bad_rbp, 0x02, 0xBAD02);
    control("clobbers r12",      (void *) tcg_cs_bad_r12, 0x04, 0xBAD04);
    control("clobbers r13",      (void *) tcg_cs_bad_r13, 0x08, 0xBAD08);
    control("clobbers r14",      (void *) tcg_cs_bad_r14, 0x10, 0xBAD10);
    control("clobbers r15",      (void *) tcg_cs_bad_r15, 0x20, 0xBAD20);
    control("clobbers all six",  (void *) tcg_cs_bad_all, 0x3f, 0xBAD3F);

    if (controls_run != 8) {
        printf("*** the control battery registered %d of 8 controls\n", controls_run);
        return 3;
    }
    if (control_failures != 0) {
        printf("*** %d control(s) failed to refute; the probe is not evidence\n",
               control_failures);
        return 4;
    }

    /* The subject. */
    long a1 = 0x0123456789abcdefL, a2 = -7L, a3 = 1000000007L, a4 = -1L, a5 = 42L;
    long args[6] = { (long) (uintptr_t) tcg_cs_sink, a1, a2, a3, a4, a5 };
    long out = 0;
    long mask = tcg_cs_probe((void *) tcg_cs_stress, args, &out);
    long ref = (a1 + 1) + a1 + a2 + a3 + a4 + a5;

    if (mask != 0) {
        printf("*** MISCOMPILE: tcg_cs_stress clobbered callee-saved GPR(s), mask=0x%lx"
               " (bit0 rbx, bit1 rbp, bit2 r12, bit3 r13, bit4 r14, bit5 r15)\n", mask);
        return 1;
    }
    if (out != ref) {
        printf("*** WRONG RESULT: got %ld want %ld\n", out, ref);
        return 2;
    }
    printf("x86-64 SysV callee-saved GPRs preserved across a trust-cg call; result=%ld\n", out);
    return 0;
}
"#;

/// Every line the control battery must print, verbatim. Pinning all eight —
/// not just the last — is what makes a repointed or disarmed control visible
/// from the Rust side: the mask AND the callee's identifying return value are
/// both part of the expected text.
const EXPECTED_CONTROL_LINES: [&str; 8] = [
    "control clean(no clobber): mask=0x0 ret=0xc1ea0 (as stated)",
    "control clobbers rbx: mask=0x1 ret=0xbad01 (as stated)",
    "control clobbers rbp: mask=0x2 ret=0xbad02 (as stated)",
    "control clobbers r12: mask=0x4 ret=0xbad04 (as stated)",
    "control clobbers r13: mask=0x8 ret=0xbad08 (as stated)",
    "control clobbers r14: mask=0x10 ret=0xbad10 (as stated)",
    "control clobbers r15: mask=0x20 ret=0xbad20 (as stated)",
    "control clobbers all six: mask=0x3f ret=0xbad3f (as stated)",
];

fn cc_x86_64(args: &[&str]) -> (bool, String) {
    let mut cmd = Command::new("cc");
    // Apple's driver flag only: GNU `cc` rejects `-arch` outright
    // ("unrecognized command-line option '-arch'"), which fails the link and
    // takes the (E1) execution oracle with it on every Linux host.
    if cfg!(target_os = "macos") {
        cmd.arg("-arch").arg("x86_64");
    }
    for a in args {
        cmd.arg(a);
    }
    let out = command_output_with_timeout(&mut cmd, codegen_link_timeout())
        .expect("cc -arch x86_64 must spawn");
    let stderr = String::from_utf8_lossy(&out.output.stderr).to_string();
    (!out.timed_out && out.output.status.success(), stderr)
}

fn link_and_run(dir: &Path, object: &[u8]) -> (i32, String) {
    let obj = dir.join("subject.o");
    let asm = dir.join("probe.s");
    let drv = dir.join("driver.c");
    let bin = dir.join("driver");
    fs::write(&obj, object).expect("write subject object");
    fs::write(&asm, PROBE_ASM).expect("write probe.s");
    fs::write(&drv, DRIVER_C).expect("write driver.c");

    let (ok, stderr) = cc_x86_64(&[
        "-O2",
        "-o",
        bin.to_str().unwrap(),
        drv.to_str().unwrap(),
        asm.to_str().unwrap(),
        obj.to_str().unwrap(),
    ]);
    assert!(ok, "link failed; files={dir:?}\n{stderr}");

    let run =
        run_executable_with_timeout(&bin, codegen_run_timeout()).expect("run callee-saved probe");
    assert!(
        !run.timed_out,
        "callee-saved probe timed out; files={dir:?}"
    );
    let stdout = String::from_utf8_lossy(&run.output.stdout).to_string();
    (run.output.status.code().unwrap_or(-1), stdout)
}

fn scratch_dir(tag: &str) -> fresh_dir::ScratchDir {
    fresh_dir::create(&format!("trust_cg_x86_callee_saved_{tag}_"))
}

#[test]
fn e2e_x86_64_sysv_callee_saved_gprs_preserved_across_call() {
    if !x86_64_oracle_enabled("e2e_x86_64_sysv_callee_saved_gprs_preserved_across_call") {
        eprintln!(
            "SKIP: (E1) NOT RUN — the x86-64 EXECUTION oracle is unavailable on this host, so the \
             only real oracle for callee-saved preservation did not run. The (E2) independent \
             structural refutation and the (E3) floor still ran."
        );
        return;
    }
    let _guard = SERIAL.lock().unwrap_or_else(|p| p.into_inner());

    let module = build_gpr_stress_module();
    let mut hazard_witnesses = 0usize;
    for opt in ALL_OPT {
        let object = sysv_object(&module, opt);
        let dir = scratch_dir(&format!("{opt:?}"));
        let (code, stdout) = link_and_run(&dir, &object);
        eprintln!("[E1 {GPR_SUBJECT} SystemV {opt:?}]\n{stdout}");
        assert_eq!(
            code, 0,
            "x86-64 SysV callee-saved preservation failed at {opt:?} (exit {code}); \
             files={dir:?}\n{stdout}"
        );
        // ALL EIGHT probe controls, verbatim. Counting them in C is not enough:
        // a control repointed at a different callee still counts itself.
        for line in EXPECTED_CONTROL_LINES {
            assert!(
                stdout.contains(line),
                "the negative-control battery did not print `{line}` at {opt:?}; a probe control \
                 has been disarmed or repointed:\n{stdout}"
            );
        }
        assert_eq!(
            stdout.matches("(as stated)").count(),
            EXPECTED_CONTROL_LINES.len(),
            "the probe printed {} control lines, not {}:\n{stdout}",
            stdout.matches("(as stated)").count(),
            EXPECTED_CONTROL_LINES.len(),
        );
        let want = format!("result={}", gpr_stress_oracle(GPR_ARGS));
        assert!(
            stdout.contains(&want),
            "at {opt:?} the native run did not print the independently computed `{want}`:\n{stdout}"
        );

        // THE HAZARD WITNESS. `mask == 0` plus a correct result is ALSO what a
        // subject that spilled every live value to the stack would produce, so
        // the execution result on its own never shows the hazard was executed.
        // Read it off the disassembly of the SAME object that just ran.
        if let Some(insns) = disassemble_x86_text(&object) {
            check_frame_obligation(
                GPR_SUBJECT,
                X86CallAbi::SystemV,
                opt,
                &insns,
                SYSV_GPR_OBLIGATION,
            );
            hazard_witnesses += 1;
        }
        let _ = fs::remove_dir_all(&dir);
    }
    if hazard_witnesses != ALL_OPT.len() {
        assert!(
            !has_objdump_for_all(E2_FORMATS),
            "the HAZARD WITNESS could not be read for every opt level even though a capable \
             `objdump` IS present — the decode failed and must not be swallowed"
        );
        eprintln!(
            "SKIP: (E1) the HAZARD WITNESS did not run for every opt level ({hazard_witnesses} of \
             {}): no `objdump` on this host decodes both (E2) container formats. A zero clobber mask alone does not show \
             that the executed subject held anything in a callee-saved register across the call.",
            ALL_OPT.len()
        );
    }
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes because it was silently refused.
fn permit_unlicensed() -> trust_cg_lower::CodegenLicensePolicy {
    trust_cg_lower::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit)
}

/// `translate_module` under [`permit_unlicensed`].
fn permit_translate_module(
    module: &trust_ir::Module,
) -> Result<
    Vec<(trust_cg_lower::Function, trust_cg_lower::ProofContext)>,
    trust_cg_lower::AdapterError,
> {
    trust_cg_lower::translate_module_for_arch_with_tls_with_license(
        module,
        trust_cg_lower::GuardCarrierArch::default(),
        trust_cg_lower::TlsDialect::default(),
        &permit_unlicensed(),
    )
}
