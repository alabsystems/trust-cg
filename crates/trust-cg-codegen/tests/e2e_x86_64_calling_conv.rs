// trust-cg-codegen/tests/e2e_x86_64_calling_conv.rs
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// ===========================================================================
// x86-64 NON-C CALLING CONVENTIONS — ADMIT OR FAIL CLOSED
// ===========================================================================
//
// WHAT THIS TREE DID BEFORE THIS FILE EXISTED, measured rather than assumed:
//
//   * A trust-ir `CallingConv` NEVER reaches x86-64 lowering. `X86PipelineConfig`
//     has a `call_abi` field, but it is set from `target_spec.operating_system`
//     alone (`compiler.rs`, "let call_abi = match target_spec.operating_system"),
//     so it selects SysV vs Windows x64 and knows nothing about the convention.
//     No file under `src/x86_64/` or `x86_64_isel.rs` reads `calling_conv`.
//
//   * The ONLY thing a convention does anywhere in the backend is the ADMISSION
//     decision in `trust-cg-lower/src/adapter.rs`
//     (`conv_sig_uses_c_register_abi`, applied at the function definition, the
//     direct call and the indirect call). That predicate was ARCHITECTURE-BLIND.
//
//   * Consequence, confirmed by compiling: `C`, `Rust`, `Fast`, `Cold` and
//     scalar `Swift` all produced the BYTE-IDENTICAL x86-64 object for the same
//     body. The convention is dropped on the floor after admission.
//
// WAS THAT A WRONG-CODE HAZARD? For the signatures that actually reach machine
// code, NO — and the reason is worth stating exactly, because it is not the
// reason the code gave:
//
//   * `Fast` / `Cold` are LLVM optimization-hint conventions with no mandated
//     register layout, so lowering them as C is valid on any target, and
//     trust-cg compiles every edge of such a call itself.
//   * `Rust` uses the platform C register sequence for scalars/pointers on
//     x86-64 exactly as it does on aarch64.
//   * `Swift` genuinely differs from C on x86-64 in its RETURN file: `swiftcc`
//     returns in RAX,RDX,RCX,R8 + XMM0-XMM3, while trust-cg's own multi-scalar
//     return placement stops at RAX,RDX + XMM0,XMM1. The admission guard's
//     Swift budget was AAPCS64's — "at most 4 COMBINED components" — which
//     admits a 3-integer return that x86-64 cannot place. Nothing wrong was
//     emitted only because `classify_x86_scalar_return_locations` then refused
//     it, deep in ISel, with "integer result register capacity is exhausted" —
//     the SAME message a plain `extern "C"` multi-return gets. The safety was
//     incidental (it came from the narrowness of `X86_RET_GPRS`, not from any
//     statement about Swift) and the diagnostic never named the convention, so
//     a reader could not distinguish an ABI-divergence refusal from ordinary
//     incompleteness.
//     (2026-09-28: the multi-scalar placement now continues past RAX,RDX /
//     XMM0,XMM1 into TrustCG's internal multi-result registers, admitted on
//     Fast/Cold edges only — `tests/e2e_x86_64_internal_multi_result.rs`. The
//     Swift budget below still stops at 2 + 2, and a C-convention 3-integer
//     return is now refused by name, `[TCG-X86-MULTI-RESULT]`.)
//
// WHAT CHANGED: `swift_return_budget(arch)` indexes the budget by target —
// `Combined(4)` for AAPCS64, `PerClass { int: 2, fp: 2 }` for SysV, and
// `Unwitnessed` for riscv64, which has no swiftcc definition in this tree and
// was never measured. The x86-64 accept/reject PARTITION is unchanged; what
// moves is WHERE and WHY a divergent signature is refused: at the adapter, by a
// diagnostic that names the convention, the target and the target's own budget.
//
// TWO CORRECTIONS, both found by building the evidence that was missing:
//
//   1. The budget is keyed on the ISA but DERIVED from an ABI. `x86_64` alone
//      answered the question, so `x86_64-pc-windows-msvc` — a different C ABI
//      on the same ISA, with no measured swiftcc placement anywhere in this
//      tree — was ADMITTED on System V's numbers. That is precisely the
//      failure `Unwitnessed` exists to prevent for riscv64, applied one level
//      too coarsely. Underneath it sat a wrong-code path for EVERY convention:
//      `classify_x86_scalar_return_locations` indexed System V's return file
//      under both ABIs, so a Win64 compile of a two-`i64` return emitted a
//      second `mov` into RDX that no Win64 caller reads (verified by
//      disassembling the emitted COFF). Both now fail closed — see
//      `e3_swift_fails_closed_on_the_unwitnessed_windows_x64_abi` and
//      `e3_windows_x64_has_no_second_scalar_return_register`.
//
//   2. "SysV C returns in RAX,RDX plus XMM0,XMM1" is true only up to TWO
//      EIGHTBYTES IN TOTAL. A `{i64,i64,double,double}` return is 32 bytes and
//      is MEMORY class under System V — measured by (E4)'s `sc_c_sret_mix`.
//      The agreement that actually licenses the budget's upper corner is
//      between trust-cg's OWN multi-scalar return placement (two independent
//      class counters over RAX,RDX / XMM0,XMM1) and `swiftcc`'s (the same two
//      counters over RAX,RDX,RCX,R8 / XMM0-XMM3), both of which (E4) measures.
//      C's register return file coincides with it only for the shapes C can
//      express — which is why the two-integer and two-FP readings are taken
//      through BOTH conventions and the 2+2 one is not.
//
// THE EVIDENCE HERE, and its honest strength:
//
//  (E1) EXECUTION — the real oracle, and the only one that can catch a wrong
//       register assignment. The C side of every call is provided by the HOST
//       TOOLCHAIN (`cc -arch x86_64`), never by trust-cg, in BOTH directions:
//         - clang CALLS trust-cg functions declared `Rust`/`Fast`/`Cold`/`C`
//           (callee-side argument reads and return writes), and
//         - trust-cg functions declared at each convention CALL a clang-defined
//           `extern "C"` reference (caller-side argument writes and return
//           reads).
//       The subjects are position-sensitive by construction: every parameter
//       carries a distinct power-of-three weight, so ANY permutation, drop or
//       misplacement of ANY argument changes the result. The signatures reach
//       all six SysV integer argument registers PLUS two stack-passed
//       arguments, ALL EIGHT XMM argument registers PLUS two SSE stack
//       arguments, both `F32` and `F64`, and both return registers (RAX and
//       XMM0).
//
//       HOW MUCH OF THIS IS ABOUT CONVENTIONS, stated plainly: by this file's
//       own measurement (`e3_the_c_equivalent_conventions_compile_to_the_identical_object`)
//       the four conventions produce the BYTE-IDENTICAL object, so the `rust`,
//       `fast` and `cold` quarters of (E1) are a RE-RUN of the `c` quarter and
//       cannot fail unless it does. They are evidence that those conventions
//       are ADMITTED and that the admitted code is correct — not discriminating
//       evidence about register layout, which no execution lane could give
//       while lowering ignores the convention. The byte-identity test is what
//       keeps that honest: the day a convention does reach lowering, it turns
//       red and those three quarters become load-bearing.
//
//  (E2) NEGATIVE CONTROLS on (E1) — NINETEEN hand-written ASSEMBLY routines,
//       each a REAL wrong-register-assignment of the SysV ABI (not merely wrong
//       arithmetic), covering BOTH edges and every lane:
//         - CALLEE controls read an argument from the wrong GPR, the wrong
//           stack slot, the wrong XMM (including XMM6/XMM7 and the SSE stack
//           boundary, at both `F32` and `F64` width), or narrow the return
//           register to 32 bits;
//         - CALLER controls are assembly CALLERS that forward their arguments
//           to a clang-defined callee with one OUTGOING register or stack word
//           wrong — the edge the `cc_*_caller` subjects exercise and that no
//           control previously covered;
//         - MIXED controls perturb one class counter while the other is
//           correct, which is the "two INDEPENDENT counters" facet the
//           interleaved lane exists for.
//       Each is declared as a SOURCE ORDER — which argument carries which
//       weight — and both the assembly and an independent Rust prediction are
//       generated from that order, by DIFFERENT arithmetic (the hardware vs.
//       Rust). Five controls carry the IDENTITY order and must MATCH the
//       reference, which anchors the generator; the rest are defective and must
//       each produce their OWN predicted value, asserted to DIFFER from the
//       reference so a no-op cannot pose as a control. The Rust side pins every
//       printed line verbatim and the driver reports how many ran.
//
//  (E3) ADMISSION CONTROLS — always run, no linker and no host toolchain
//       needed. They pin the fail-closed boundary itself, including an
//       ARCHITECTURE DIFFERENTIAL: the SAME module must be REFUSED for
//       x86-64 and ACCEPTED for aarch64. Without that differential the new
//       `arch` argument could be ignored entirely and every other check would
//       still pass.
//
//  (E4) THE SWIFTCC SOURCE SIDE — the half of the premise that used to be
//       prose. Hand-written assembly deposits known values in NAMED registers;
//       clang reads the SAME symbol back through `__attribute__((swiftcall))`
//       and through the plain C convention. Thirteen readings plus two sret
//       witnesses measure where each convention takes each return component
//       from, with controls that must be read WRONG. This lane lives in its
//       own target, `e2e_x86_64_swiftcc`, because it needs a clang driver;
//       see that file's header for what it establishes and how a GCC-only
//       host records it (XD-03).
//
// WHAT IS NOT PROVEN HERE:
//   * Nothing about executing Windows x64 code — this host cannot. What IS
//     established is that both Win64 paths now FAIL CLOSED: `Swift` because
//     that ABI's swiftcc placement was never measured, and any two-component
//     scalar return because Win64 has no second return register in either
//     class. Neither is a claim that the rest of the Win64 path is correct.
//   * Nothing about swiftself / swifterror / swiftasync. trust-ir's `ParamAttrs`
//     cannot express them, so they are unreachable from this IR rather than
//     handled.
//   * Nothing about `F16`. An `F16` PARAMETER panics in x86 ISel
//     ("unsupported x86 XMM lane type: F16") under EVERY convention including
//     `C`, so it is a pre-existing x86 F16 lowering gap, not a convention
//     defect, and it is out of this lane.
//   * ARGUMENT classes not exercised by (E1), though the guard admits them for
//     C/Rust/Fast/Cold on ANY signature: by-value AGGREGATES (System V's
//     MEMORY vs INTEGER/SSE eightbyte classification, and sret), VARIADIC
//     signatures (System V's `AL` vector-register-count rule), sub-64-bit
//     integer scalars `I8`/`I16`/`I32`/`Bool` (the upper bits of a narrow
//     argument register), `Ptr`, and a STACK-passed `F32`. These are stated as
//     unexercised, not as proven.
//   * Nothing about riscv64 swiftcc. It is marked `Unwitnessed` — fail-closed
//     because it was never measured, which is the honest state, not a claim
//     that it diverges. `e3_riscv64_swift_is_unwitnessed_end_to_end` witnesses
//     that fail-closed behaviour through the adapter rather than only as
//     budget arithmetic.

#![allow(clippy::too_many_arguments)]

mod common;

use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::Mutex;

use common::rosetta::{
    codegen_link_timeout, codegen_run_timeout, command_output_with_timeout,
    run_executable_with_timeout,
};
use common::x86_64_corpus::x86_64_oracle_enabled;

use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::target::{Target, TargetSpec};
use trust_ir::{BinOp, CallingConv, CastOp, Ty};
use trust_ir_build::ModuleBuilder;

/// One global lock: the (E1) lane links and runs several native binaries and
/// this box has four cores.
static SERIAL: Mutex<()> = Mutex::new(());

/// The assembler-level spelling of a C symbol on this host: Mach-O prefixes
/// every C symbol with `_`; ELF carries the bare name. The hand-written
/// control assembly defines its callees through this so the same source links
/// against the C driver on both hosts.
fn host_sym(name: &str) -> String {
    let prefix = if cfg!(target_os = "macos") { "_" } else { "" };
    format!("{prefix}{name}")
}

const ALL_OPT: [OptLevel; 4] = [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3];

/// The conventions whose x86-64 register ABI is claimed to EQUAL System V, and
/// the reason each one is claimed. `Swift` is deliberately absent: it is
/// handled by the admission controls, not by execution, because the subset
/// SysV places identically to `swiftcc` is exactly the subset `extern "C"`
/// already covers, so an execution lane for it could not distinguish the two.
const C_EQUIVALENT: [(&str, CallingConv, &str); 4] = [
    ("c", CallingConv::C, "the C ABI itself"),
    (
        "rust",
        CallingConv::Rust,
        "extern \"Rust\" uses the SysV register sequence for scalars/pointers; \
         aggregate layout is carried by StructRepr, not the convention",
    ),
    (
        "fast",
        CallingConv::Fast,
        "an LLVM optimization-hint convention: the LangRef mandates no layout \
         different from C, and trust-cg compiles every edge of the call itself",
    ),
    (
        "cold",
        CallingConv::Cold,
        "an LLVM optimization-hint convention, same reasoning as Fast",
    ),
];

// ---------------------------------------------------------------------------
// The subjects. Every parameter carries a distinct power-of-three weight, so
// the result is a positional fingerprint: no permutation, drop or misplacement
// of any argument can leave it unchanged.
// ---------------------------------------------------------------------------

/// Weights for the eight integer parameters. Under SysV the first six land in
/// RDI, RSI, RDX, RCX, R8, R9 and the last two are STACK-passed, so this one
/// signature covers the whole integer argument file and the register/stack
/// boundary.
/// The last weight is deliberately large: it pushes the reference value past
/// `i32::MAX`, without which `ctl_int_trunc32` — the control for the RETURN
/// register's width — would compute the reference exactly and refute nothing.
const INT_WEIGHTS: [i64; 8] = [1, 3, 9, 27, 81, 243, 729, 500_000_003];

/// Weights for the six floating-point parameters (XMM0..XMM5).
const FP_WEIGHTS: [i64; 6] = [1, 3, 9, 27, 81, 243];

/// Weights for the mixed signature's four FP parameters (XMM0..XMM3). The
/// integer parameters of that signature reuse `INT_WEIGHTS`.
const MIX_FP_WEIGHTS: [i64; 4] = [6561, 19683, 59049, 177147];

/// The integer arguments every lane is exercised with. Small and distinct so
/// that every weighted product, and the whole sum, is exact in `f64` too.
const INT_ARGS: [i64; 8] = [2, -5, 11, 7, -13, 23, 31, -17];

/// The floating-point arguments. Integral values, so the `f64` reference is
/// exact and a bit-for-bit comparison is meaningful.
const FP_ARGS: [f64; 6] = [4.0, -6.0, 10.0, 3.0, -8.0, 21.0];

/// The SSE-file lane. The `fp` lane above stops at XMM5, so the last two SSE
/// argument registers and the SSE register/stack boundary were admitted but
/// never exercised — and every subject in this file was `I64` or `F64`, so
/// `F32` was not either.
///
/// This signature is ten SSE arguments: eight fill XMM0..XMM7 and the last two
/// are STACK-passed, and four of the register ones are `F32`. System V assigns
/// SSE arguments in declaration order regardless of width, so one signature
/// covers the whole SSE argument file, the boundary past it, and both widths.
/// (The two STACK slots are deliberately `F64`: a stack-passed `F32` is a
/// narrower question — see WHAT IS NOT PROVEN.)
const SSE_IS_F32: [bool; 10] = [
    false, true, false, true, false, true, false, true, false, false,
];
const SSE_WEIGHTS: [i64; 10] = [1, 3, 9, 27, 81, 243, 729, 2187, 6561, 19683];
/// Small integral values: exact in `f32` AND in `f64`, and every weighted
/// product and partial sum stays well inside 2^24, so widening an `F32`
/// argument to `F64` loses nothing and the comparison is bit-for-bit.
const SSE_ARGS: [f64; 10] = [4.0, -6.0, 10.0, 3.0, -8.0, 21.0, 5.0, -9.0, 12.0, -2.0];

fn ref_int(args: [i64; 8]) -> i64 {
    let mut acc = 0i64;
    for (a, w) in args.iter().zip(INT_WEIGHTS.iter()) {
        acc = acc.wrapping_add(a.wrapping_mul(*w));
    }
    acc
}

fn ref_fp(args: [f64; 6]) -> f64 {
    let mut acc = 0f64;
    for (a, w) in args.iter().zip(FP_WEIGHTS.iter()) {
        acc += a * (*w as f64);
    }
    acc
}

fn ref_mix(ints: [i64; 8], fps: [f64; 4]) -> f64 {
    let mut acc = 0f64;
    for (a, w) in ints.iter().zip(INT_WEIGHTS.iter()) {
        acc += (*a as f64) * (*w as f64);
    }
    for (x, w) in fps.iter().zip(MIX_FP_WEIGHTS.iter()) {
        acc += x * (*w as f64);
    }
    acc
}

fn mix_fp_args() -> [f64; 4] {
    [FP_ARGS[0], FP_ARGS[1], FP_ARGS[2], FP_ARGS[3]]
}

fn ref_sse(args: [f64; 10]) -> f64 {
    let mut acc = 0f64;
    for (a, w) in args.iter().zip(SSE_WEIGHTS.iter()) {
        acc += a * (*w as f64);
    }
    acc
}

/// The CALLEE edge: for each C-equivalent convention, an integer lane (six
/// GPR arguments + two stack arguments -> RAX), a floating-point lane
/// (XMM0..XMM5 -> XMM0) and a mixed lane with an interleaved declaration.
/// clang calls these, so trust-cg READS the argument registers and WRITES the
/// return register. No FFI boundary, so this module needs no `target_info` and
/// can be compiled for admission on any host.
fn build_subject_module() -> trust_ir::Module {
    let mut m = ModuleBuilder::new("x86_64_calling_conv");

    let int_sig = m.add_func_type(vec![Ty::I64; 8], vec![Ty::I64]);
    let fp_sig = m.add_func_type(vec![Ty::F64; 6], vec![Ty::F64]);
    let sse_sig = m.add_func_type(
        SSE_IS_F32
            .iter()
            .map(|is_f32| if *is_f32 { Ty::F32 } else { Ty::F64 })
            .collect(),
        vec![Ty::F64],
    );
    // Interleaved on purpose: SysV assigns integer and FP arguments from two
    // INDEPENDENT counters, so an interleaved declaration is what catches a
    // lowering that walks one shared counter.
    let mix_sig = m.add_func_type(
        vec![
            Ty::I64,
            Ty::F64,
            Ty::I64,
            Ty::F64,
            Ty::I64,
            Ty::F64,
            Ty::I64,
            Ty::F64,
            Ty::I64,
            Ty::I64,
            Ty::I64,
            Ty::I64,
        ],
        vec![Ty::F64],
    );

    for (tag, _, _) in C_EQUIVALENT.iter() {
        // --- integer lane: 6 GPR args + 2 stack args -> RAX ---
        {
            let mut f = m.function(format!("cc_{tag}_int"), int_sig);
            let entry = f.create_block();
            let params: Vec<_> = (0..8).map(|_| f.add_block_param(entry, Ty::I64)).collect();
            f.switch_to_block(entry);
            let mut acc = None;
            for (p, w) in params.iter().zip(INT_WEIGHTS.iter()) {
                let weight = f.iconst(Ty::I64, *w as i128);
                let term = f.binop(BinOp::Mul, Ty::I64, *p, weight);
                acc = Some(match acc {
                    None => term,
                    Some(a) => f.binop(BinOp::Add, Ty::I64, a, term),
                });
            }
            f.ret(vec![acc.expect("eight integer terms")]);
            f.build();
        }

        // --- floating-point lane: XMM0..XMM5 -> XMM0 ---
        {
            let mut f = m.function(format!("cc_{tag}_fp"), fp_sig);
            let entry = f.create_block();
            let params: Vec<_> = (0..6).map(|_| f.add_block_param(entry, Ty::F64)).collect();
            f.switch_to_block(entry);
            let mut acc = None;
            for (p, w) in params.iter().zip(FP_WEIGHTS.iter()) {
                let weight = f.fconst(Ty::F64, *w as f64);
                let term = f.binop(BinOp::FMul, Ty::F64, *p, weight);
                acc = Some(match acc {
                    None => term,
                    Some(a) => f.binop(BinOp::FAdd, Ty::F64, a, term),
                });
            }
            f.ret(vec![acc.expect("six FP terms")]);
            f.build();
        }

        // --- SSE-file lane: XMM0..XMM7 + 2 stack, F32 and F64 -> XMM0 ---
        {
            let mut f = m.function(format!("cc_{tag}_sse"), sse_sig);
            let entry = f.create_block();
            let params: Vec<_> = SSE_IS_F32
                .iter()
                .map(|is_f32| f.add_block_param(entry, if *is_f32 { Ty::F32 } else { Ty::F64 }))
                .collect();
            f.switch_to_block(entry);
            let mut acc = None;
            for (index, (p, w)) in params.iter().zip(SSE_WEIGHTS.iter()).enumerate() {
                let widened = if SSE_IS_F32[index] {
                    f.cast(CastOp::FPExt, Ty::F32, Ty::F64, *p)
                } else {
                    *p
                };
                let weight = f.fconst(Ty::F64, *w as f64);
                let term = f.binop(BinOp::FMul, Ty::F64, widened, weight);
                acc = Some(match acc {
                    None => term,
                    Some(a) => f.binop(BinOp::FAdd, Ty::F64, a, term),
                });
            }
            f.ret(vec![acc.expect("ten SSE terms")]);
            f.build();
        }

        // --- mixed lane: interleaved integer/FP declaration -> XMM0 ---
        {
            let mut f = m.function(format!("cc_{tag}_mix"), mix_sig);
            let entry = f.create_block();
            let mut ints = Vec::new();
            let mut fps = Vec::new();
            for _ in 0..4 {
                ints.push(f.add_block_param(entry, Ty::I64));
                fps.push(f.add_block_param(entry, Ty::F64));
            }
            for _ in 0..4 {
                ints.push(f.add_block_param(entry, Ty::I64));
            }
            f.switch_to_block(entry);
            let mut acc = None;
            for (p, w) in ints.iter().zip(INT_WEIGHTS.iter()) {
                let as_fp = f.cast(CastOp::SIToFP, Ty::I64, Ty::F64, *p);
                let weight = f.fconst(Ty::F64, *w as f64);
                let term = f.binop(BinOp::FMul, Ty::F64, as_fp, weight);
                acc = Some(match acc {
                    None => term,
                    Some(a) => f.binop(BinOp::FAdd, Ty::F64, a, term),
                });
            }
            for (p, w) in fps.iter().zip(MIX_FP_WEIGHTS.iter()) {
                let weight = f.fconst(Ty::F64, *w as f64);
                let term = f.binop(BinOp::FMul, Ty::F64, *p, weight);
                acc = Some(match acc {
                    None => term,
                    Some(a) => f.binop(BinOp::FAdd, Ty::F64, a, term),
                });
            }
            f.ret(vec![acc.expect("twelve mixed terms")]);
            f.build();
        }
    }

    stamp_conventions(m.build().expect("ModuleBuilder::build: test fixture"))
}

/// Stamp the convention onto every function a module owns, definitions and
/// bodyless declarations alike, so BOTH edges of a call carry it: the adapter's
/// direct-call guard reads the CALLEE's `calling_conv`, and its per-function
/// guard reads the definition's.
fn stamp_conventions(mut module: trust_ir::Module) -> trust_ir::Module {
    for function in &mut module.functions {
        for (tag, conv, _) in C_EQUIVALENT {
            if function.name.contains(&format!("_{tag}_"))
                || function.name == format!("host_int_{tag}")
            {
                function.calling_conv = conv;
            }
        }
    }
    module
}

/// The CALLER edge: trust-cg functions, one per convention, that call a
/// clang-defined `extern "C"` reference. trust-cg WRITES the argument
/// registers here, which the three callee lanes never exercise.
///
/// This module carries a bodyless external declaration, which is an FFI
/// boundary, so trust-ir requires `target_info` on it. It is therefore pinned
/// to `x86_64-apple-darwin` and compiled through the matching `TargetSpec` —
/// which is also why it is built only inside the (E1) lane, where an x86-64
/// host is already required, and never in the always-run admission lane.
fn build_caller_module() -> trust_ir::Module {
    let mut m = ModuleBuilder::new_with_target_info(
        "x86_64_calling_conv_caller",
        trust_ir::TargetInfo {
            triple: X86_SUBJECT_TRIPLE.into(),
            pointer_size: 8,
            endianness: trust_ir::Endianness::Little,
            // `None` means "derived from the triple", the documented legacy
            // state; this lane makes no claim beyond the triple's own ABI.
            abi: None,
            struct_passing: trust_ir::StructPassingPolicy::NativeC,
        },
    );
    let int_sig = m.add_func_type(vec![Ty::I64; 8], vec![Ty::I64]);
    let hosts: Vec<_> = C_EQUIVALENT
        .iter()
        .map(|(tag, _, _)| m.declare_function(format!("host_int_{tag}"), int_sig))
        .collect();
    for (index, (tag, _, _)) in C_EQUIVALENT.iter().enumerate() {
        let mut f = m.function(format!("cc_{tag}_caller"), int_sig);
        let entry = f.create_block();
        let params: Vec<_> = (0..8).map(|_| f.add_block_param(entry, Ty::I64)).collect();
        f.switch_to_block(entry);
        let [result] = f.call_results::<1>(hosts[index], params);
        f.ret(vec![result]);
        f.build();
    }
    stamp_conventions(m.build().expect("ModuleBuilder::build: test fixture"))
}

/// The exact triple the (E1) subject objects are produced for.
/// The x86-64 triple this host links and executes natively: the Darwin one on
/// macOS, the GNU/Linux one elsewhere. The System V ABI under test is the same
/// on both; only the object format and the C driver's link differ.
const X86_SUBJECT_TRIPLE: &str = if cfg!(target_os = "macos") {
    "x86_64-apple-darwin"
} else {
    "x86_64-unknown-linux-gnu"
};

/// Compile for the exact x86-64 Darwin spec, which is what a module carrying
/// `target_info` must be compiled against.
fn compile_x86_subject(module: &trust_ir::Module, opt: OptLevel) -> Result<Vec<u8>, String> {
    Compiler::new_for_target_spec(
        CompilerConfig {
            opt_level: opt,
            ..CompilerConfig::default()
        },
        TargetSpec::parse(X86_SUBJECT_TRIPLE).expect("the host x86-64 triple is a known triple"),
    )
    .with_codegen_license(permit_unlicensed())
    .compile(module)
    .map(|r| r.object_code)
    .map_err(|e| format!("{e:?}"))
}

fn compile_for(
    module: &trust_ir::Module,
    target: Target,
    opt: OptLevel,
) -> Result<Vec<u8>, String> {
    Compiler::new(CompilerConfig {
        opt_level: opt,
        target,
        ..CompilerConfig::default()
    })
    .with_codegen_license(permit_unlicensed())
    .compile(module)
    .map(|r| r.object_code)
    .map_err(|e| format!("{e:?}"))
}

// ===========================================================================
// (E1) + (E2): the native lane
// ===========================================================================

/// The eight assembly controls. Each is a REAL System V wrong-register or
/// wrong-stack-slot assignment, not wrong arithmetic: it computes the SAME
/// weighted sum but takes one or more of its terms out of a register or stack
/// slot the ABI did not put that argument in, or narrows the return register.
/// Two are CORRECT and must MATCH the reference, so the battery cannot pass by
/// the comparison always failing.
///
/// A control is declared as a SOURCE ORDER: `order[k]` is the incoming
/// argument whose value ends up carrying weight `k`. The identity order is the
/// correct SysV reading. The assembly and the Rust prediction are generated
/// from the SAME order — which is the definition of the defect — but from
/// DIFFERENT arithmetic: the assembly is executed on the hardware, the
/// prediction is computed in Rust. The generator itself is anchored by the two
/// identity-order controls, which must reproduce the independent reference.
///
/// Integer source indices name the SysV integer argument sequence: 0..=5 are
/// RDI, RSI, RDX, RCX, R8, R9 and 6..=8 are the stack words at 8(%rsp),
/// 16(%rsp), 24(%rsp) — the return address sits at (%rsp) on entry.
const INT_SOURCE_REGS: [&str; 6] = ["%rdi", "%rsi", "%rdx", "%rcx", "%r8", "%r9"];

/// `(name, source order, narrow the return register to 32 bits)`.
const INT_CONTROLS: [(&str, [usize; 8], bool); 5] = [
    // The CORRECT SysV reading. Anchors the generator.
    ("ctl_int_correct", [0, 1, 2, 3, 4, 5, 6, 7], false),
    // Arguments 0 and 1 exchanged: RDI and RSI read the other's value.
    ("ctl_int_swap01", [1, 0, 2, 3, 4, 5, 6, 7], false),
    // Every argument read ONE POSITION LATER — the classic "an extra leading
    // register argument was assumed" defect. Every term is still a real
    // incoming value, so the result is deterministic.
    ("ctl_int_argshift", [1, 2, 3, 4, 5, 6, 7, 8], false),
    // Register arguments correct, both STACK arguments read one word too high.
    // Fires only if the oracle reaches past the six GPR argument registers.
    ("ctl_int_stackslot", [0, 1, 2, 3, 4, 5, 7, 8], false),
    // The CORRECT sum, then the return register narrowed to 32 bits. Fires
    // only if the oracle observes the full width of RAX.
    ("ctl_int_trunc32", [0, 1, 2, 3, 4, 5, 6, 7], true),
];

/// `(name, source order)` over the XMM argument registers XMM0..XMM5.
const FP_CONTROLS: [(&str, [usize; 6]); 3] = [
    ("ctl_fp_correct", [0, 1, 2, 3, 4, 5]),
    ("ctl_fp_swap01", [1, 0, 2, 3, 4, 5]),
    // The whole XMM argument file read in REVERSE: weight 1 taken from XMM5,
    // the largest weight from XMM0.
    ("ctl_fp_reverse", [5, 4, 3, 2, 1, 0]),
];

/// Controls for the SSE-FILE lane. The `fp` controls above only reach XMM5, so
/// nothing established that the oracle can see a defect in XMM6, XMM7 or the
/// two SSE STACK words — the registers the `cc_*_sse` subjects newly cover.
///
/// `order[k]` is the argument whose value carries weight `k`, exactly as for
/// the other tables. Every swap here is between positions of the SAME declared
/// WIDTH, so a control never reinterprets an `F32` argument as an `F64` one;
/// the generator asserts that rather than trusting it.
const SSE_CONTROLS: [(&str, [usize; 10]); 4] = [
    ("ctl_sse_correct", [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]),
    // XMM4 and XMM6 exchanged (both F64): fires only if the read reaches XMM6.
    ("ctl_sse_swap46", [0, 1, 2, 3, 6, 5, 4, 7, 8, 9]),
    // XMM5 and XMM7 exchanged (both F32): fires only if the read reaches XMM7,
    // and only if the F32 lane is read at its own width.
    ("ctl_sse_swap57", [0, 1, 2, 3, 4, 7, 6, 5, 8, 9]),
    // The two SSE STACK words exchanged: the SSE register/stack boundary,
    // which the integer lane's `ctl_int_stackslot` says nothing about.
    ("ctl_sse_swap89", [0, 1, 2, 3, 4, 5, 6, 7, 9, 8]),
];

/// THE CALLER DIRECTION. Every control above is a CALLEE — it establishes that
/// the oracle can see a wrong argument READ. The `cc_*_caller` subjects exercise
/// the opposite edge, trust-cg WRITING the outgoing argument registers and the
/// two outgoing stack words, and nothing established that the oracle could see a
/// defect there.
///
/// These are assembly CALLERS: each reads its nine incoming arguments, places
/// them into the OUTGOING argument sequence in its declared order, and calls the
/// same C-defined `host_int_ctl` the subject lane's callees use. `order[k]` is
/// the incoming argument placed in outgoing slot `k`, and the C callee weights
/// slot `k` by `INT_WEIGHTS[k]` — so the prediction is the same arithmetic as a
/// callee control's, computed about the other edge.
///
/// (A symmetric defect in a SHARED register table cancels on these subjects —
/// a forwarding function reads and writes the same wrong register — so the
/// caller direction adds discrimination only for defects asymmetric between the
/// incoming and outgoing paths. That is exactly what these controls are: the
/// outgoing placement is wrong while the incoming read is right.)
const CALLER_CONTROLS: [(&str, [usize; 8]); 4] = [
    // The CORRECT forwarding. Anchors the generator on this edge.
    ("ctl_caller_correct", [0, 1, 2, 3, 4, 5, 6, 7]),
    // Outgoing slots 0 and 1 exchanged: RDI and RSI are written with each
    // other's value while the incoming read is correct.
    ("ctl_caller_swap01", [1, 0, 2, 3, 4, 5, 6, 7]),
    // Register slots correct, both outgoing STACK words written one position
    // late. Fires only if the oracle reaches past the six outgoing GPRs.
    ("ctl_caller_stackslot", [0, 1, 2, 3, 4, 5, 7, 8]),
    // The last REGISTER slot (R9) and the first STACK word exchanged: the
    // register/stack boundary itself, on the writing side.
    ("ctl_caller_boundary", [0, 1, 2, 3, 4, 6, 5, 7]),
];

/// THE MIXED LANE's own controls. The `cc_*_mix` subjects exist because System V
/// assigns integer and FP arguments from two INDEPENDENT counters, and an
/// interleaved declaration is what catches a lowering that walks one shared
/// counter. That facet had no control of its own: nothing established that the
/// mixed oracle could SEE a class-counter defect.
///
/// `(name, integer source order, FP source order)` over the mixed prototype —
/// eight integers (RDI,RSI,RDX,RCX,R8,R9 then two stack words) and four doubles
/// (XMM0..XMM3). One control perturbs the integer counter while the FP one is
/// correct, the other perturbs the FP counter while the integer one is correct;
/// together they say each class is read position-sensitively IN THE PRESENCE of
/// the other, which is what "two independent counters" means.
const MIX_CONTROLS: [(&str, [usize; 8], [usize; 4]); 3] = [
    ("ctl_mix_correct", [0, 1, 2, 3, 4, 5, 6, 7], [0, 1, 2, 3]),
    ("ctl_mix_int_swap01", [1, 0, 2, 3, 4, 5, 6, 7], [0, 1, 2, 3]),
    ("ctl_mix_fp_reverse", [0, 1, 2, 3, 4, 5, 6, 7], [3, 2, 1, 0]),
];

/// Load integer source `src` into `dst`.
fn int_load(src: usize, dst: &str) -> String {
    if src < INT_SOURCE_REGS.len() {
        format!("    movq    {}, {dst}\n", INT_SOURCE_REGS[src])
    } else {
        // Stack argument n (n >= 6) sits at 8*(n-5)(%rsp) on entry, the return
        // address occupying (%rsp).
        format!("    movq    {}(%rsp), {dst}\n", 8 * (src - 5))
    }
}

fn controls_asm() -> String {
    let mut out = String::from("    .text\n");
    for (name, order, narrow) in INT_CONTROLS {
        out.push_str(&format!("\n    .globl {0}\n{0}:\n", host_sym(name)));
        out.push_str(&int_load(order[0], "%rax"));
        for slot in 1..8 {
            out.push_str(&int_load(order[slot], "%r11"));
            out.push_str(&format!(
                "    imulq   ${}, %r11, %r10\n    addq    %r10, %rax\n",
                INT_WEIGHTS[slot]
            ));
        }
        if narrow {
            out.push_str("    movslq  %eax, %rax\n");
        }
        out.push_str("    ret\n");
    }
    for (name, order) in FP_CONTROLS {
        out.push_str(&format!("\n    .globl {0}\n{0}:\n", host_sym(name)));
        // XMM6/7/8 are scratch: System V has NO callee-saved XMM register.
        out.push_str(&format!("    movapd  %xmm{}, %xmm7\n", order[0]));
        for slot in 1..6 {
            out.push_str(&format!(
                "    movq    ${}, %rax\n    cvtsi2sdq %rax, %xmm6\n    movapd  %xmm{}, %xmm8\n    \
                 mulsd   %xmm6, %xmm8\n    addsd   %xmm8, %xmm7\n",
                FP_WEIGHTS[slot], order[slot]
            ));
        }
        out.push_str("    movapd  %xmm7, %xmm0\n    ret\n");
    }
    for (name, order) in SSE_CONTROLS {
        out.push_str(&sse_control_asm(name, order));
    }
    for (name, order) in CALLER_CONTROLS {
        out.push_str(&caller_control_asm(name, order));
    }
    for (name, int_order, fp_order) in MIX_CONTROLS {
        out.push_str(&mix_control_asm(name, int_order, fp_order));
    }
    out
}

/// One assembly callee control over the SSE argument file (see
/// [`SSE_CONTROLS`]): eight SSE registers XMM0..XMM7 then two stack words, with
/// `F32` and `F64` positions read at their declared widths.
fn sse_control_asm(name: &str, order: [usize; 10]) -> String {
    let mut out = format!("\n    .globl {0}\n{0}:\n", host_sym(name));
    // SCRATCH IS XMM9..XMM11, not XMM6..XMM8 as in the six-argument `fp`
    // controls: this prototype fills XMM0..XMM7, so XMM7 is an INCOMING
    // ARGUMENT here. (The identity-order anchor caught exactly that: zeroing
    // XMM7 as an accumulator dropped the eighth argument's term.)
    out.push_str("    pxor    %xmm11, %xmm11\n");
    for (slot, source) in order.iter().enumerate() {
        assert_eq!(
            SSE_IS_F32[slot], SSE_IS_F32[*source],
            "SSE control `{name}` maps slot {slot} to source {source} across a WIDTH boundary; a \
             control must be a wrong-REGISTER defect, not a reinterpretation"
        );
        if *source < 8 {
            if SSE_IS_F32[*source] {
                out.push_str(&format!("    cvtss2sd %xmm{source}, %xmm9\n"));
            } else {
                out.push_str(&format!("    movapd  %xmm{source}, %xmm9\n"));
            }
        } else {
            // SSE stack argument n (n >= 8) sits at 8*(n-7)(%rsp) on entry, the
            // return address occupying (%rsp). Both are F64 here.
            out.push_str(&format!("    movsd   {}(%rsp), %xmm9\n", 8 * (*source - 7)));
        }
        out.push_str(&format!(
            "    movq    ${}, %rax\n    cvtsi2sdq %rax, %xmm10\n    mulsd   %xmm10, %xmm9\n    \
             addsd   %xmm9, %xmm11\n",
            SSE_WEIGHTS[slot]
        ));
    }
    out.push_str("    movapd  %xmm11, %xmm0\n    ret\n");
    out
}

/// One assembly CALLER control (see [`CALLER_CONTROLS`]).
///
/// It copies all nine incoming arguments into a local frame FIRST, so placing
/// them into the outgoing sequence cannot clobber a value it has not read yet,
/// then writes the outgoing sequence in the declared order and calls
/// `host_int_ctl`. `%rsp` is 16-byte aligned at the call, and the two outgoing
/// stack words occupy the bottom of the frame, below the locals.
fn caller_control_asm(name: &str, order: [usize; 8]) -> String {
    let mut out = format!("\n    .globl {0}\n{0}:\n", host_sym(name));
    out.push_str("    pushq   %rbp\n    movq    %rsp, %rbp\n");
    // 96 keeps %rsp 16-aligned (%rbp is 16-aligned after the push) and leaves
    // room for nine 8-byte locals at -8(%rbp)..-72(%rbp) plus the two outgoing
    // stack words at 0(%rsp),8(%rsp).
    out.push_str("    subq    $96, %rsp\n");
    for (index, reg) in INT_SOURCE_REGS.iter().enumerate() {
        out.push_str(&format!(
            "    movq    {reg}, {}(%rbp)\n",
            -8 - 8 * index as i64
        ));
    }
    for index in 6..9usize {
        // Incoming stack argument n (n >= 6) sits at 8*(n-5) past the return
        // address, which `pushq %rbp` moved to 8(%rbp).
        out.push_str(&format!(
            "    movq    {}(%rbp), %r10\n    movq    %r10, {}(%rbp)\n",
            8 + 8 * (index as i64 - 5),
            -8 - 8 * index as i64
        ));
    }
    let local = |slot: usize| format!("{}(%rbp)", -8 - 8 * slot as i64);
    for (slot, reg) in INT_SOURCE_REGS.iter().enumerate() {
        out.push_str(&format!("    movq    {}, {reg}\n", local(order[slot])));
    }
    for (index, &slot) in order[6..8].iter().enumerate() {
        out.push_str(&format!(
            "    movq    {}, %r10\n    movq    %r10, {}(%rsp)\n",
            local(slot),
            8 * index
        ));
    }
    out.push_str(&format!("    callq   {}\n", host_sym("host_int_ctl")));
    out.push_str("    movq    %rbp, %rsp\n    popq    %rbp\n    ret\n");
    out
}

/// One assembly callee control for the MIXED prototype (see [`MIX_CONTROLS`]).
///
/// Eight integer arguments (six registers then two stack words) and four
/// doubles (XMM0..XMM3), accumulated in `f64` in the SAME order the Rust and C
/// references use — integers first, then the FP terms. Every value here is an
/// exact integer well inside 2^53, so the accumulation is exact and a
/// bit-for-bit comparison is meaningful.
fn mix_control_asm(name: &str, int_order: [usize; 8], fp_order: [usize; 4]) -> String {
    let mut out = format!("\n    .globl {0}\n{0}:\n", host_sym(name));
    // XMM6..XMM9 are scratch; XMM0..XMM3 carry the incoming doubles and are
    // only ever read.
    out.push_str("    pxor    %xmm7, %xmm7\n");
    for (slot, source) in int_order.iter().enumerate() {
        out.push_str(&int_load(*source, "%r10"));
        out.push_str("    cvtsi2sdq %r10, %xmm6\n");
        out.push_str(&format!(
            "    movq    ${}, %rax\n    cvtsi2sdq %rax, %xmm8\n    mulsd   %xmm8, %xmm6\n    \
             addsd   %xmm6, %xmm7\n",
            INT_WEIGHTS[slot]
        ));
    }
    for (slot, source) in fp_order.iter().enumerate() {
        out.push_str(&format!("    movapd  %xmm{source}, %xmm9\n"));
        out.push_str(&format!(
            "    movq    ${}, %rax\n    cvtsi2sdq %rax, %xmm8\n    mulsd   %xmm8, %xmm9\n    \
             addsd   %xmm9, %xmm7\n",
            MIX_FP_WEIGHTS[slot]
        ));
    }
    out.push_str("    movapd  %xmm7, %xmm0\n    ret\n");
    out
}

/// `ctl_int_argshift` and `ctl_int_stackslot` read one word PAST the eighth
/// argument. The driver therefore calls the integer controls through a
/// NINE-argument prototype so that word is a known value rather than
/// unspecified stack — otherwise those two controls would be nondeterministic
/// and their predictions unfalsifiable.
const NINTH_ARG: i64 = 41;

fn int_args_with_ninth() -> [i64; 9] {
    [
        INT_ARGS[0],
        INT_ARGS[1],
        INT_ARGS[2],
        INT_ARGS[3],
        INT_ARGS[4],
        INT_ARGS[5],
        INT_ARGS[6],
        INT_ARGS[7],
        NINTH_ARG,
    ]
}

/// Rust-side prediction for a control, computed from its declared SOURCE ORDER
/// by ORDINARY RUST ARITHMETIC — the other side of the comparison from the
/// assembly, which evaluates the same order on the hardware. A control whose
/// order is the identity is CORRECT and its prediction must equal the
/// independent reference; every other prediction is asserted to DIFFER from it.
fn control_prediction(name: &str) -> f64 {
    let src = int_args_with_ninth();
    if let Some((_, order, narrow)) = INT_CONTROLS.iter().find(|(n, _, _)| *n == name) {
        let mut acc = 0i64;
        for (slot, source) in order.iter().enumerate() {
            acc = acc.wrapping_add(src[*source].wrapping_mul(INT_WEIGHTS[slot]));
        }
        return if *narrow {
            ((acc as i32) as i64) as f64
        } else {
            acc as f64
        };
    }
    if let Some((_, order)) = FP_CONTROLS.iter().find(|(n, _)| *n == name) {
        let mut acc = 0f64;
        for (slot, source) in order.iter().enumerate() {
            acc += FP_ARGS[*source] * (FP_WEIGHTS[slot] as f64);
        }
        return acc;
    }
    if let Some((_, order)) = SSE_CONTROLS.iter().find(|(n, _)| *n == name) {
        let mut acc = 0f64;
        for (slot, source) in order.iter().enumerate() {
            acc += SSE_ARGS[*source] * (SSE_WEIGHTS[slot] as f64);
        }
        return acc;
    }
    // A CALLER control places incoming argument `order[k]` into OUTGOING slot
    // `k`, and the C callee weights slot `k` by `INT_WEIGHTS[k]` — the same
    // arithmetic as a callee control, stated about the other edge.
    if let Some((_, order)) = CALLER_CONTROLS.iter().find(|(n, _)| *n == name) {
        let mut acc = 0i64;
        for (slot, source) in order.iter().enumerate() {
            acc = acc.wrapping_add(src[*source].wrapping_mul(INT_WEIGHTS[slot]));
        }
        return acc as f64;
    }
    if let Some((_, int_order, fp_order)) = MIX_CONTROLS.iter().find(|(n, _, _)| *n == name) {
        let mut acc = 0f64;
        for (slot, source) in int_order.iter().enumerate() {
            acc += (INT_ARGS[*source] as f64) * (INT_WEIGHTS[slot] as f64);
        }
        for (slot, source) in fp_order.iter().enumerate() {
            acc += mix_fp_args()[*source] * (MIX_FP_WEIGHTS[slot] as f64);
        }
        return acc;
    }
    panic!("no Rust model for control `{name}`");
}

/// Which prototype the driver must call a control through, and which reference
/// it is compared against.
#[derive(Clone, Copy, PartialEq, Eq)]
enum ControlKind {
    /// Nine integer arguments, integer result — the callee edge.
    Int,
    /// Six doubles, double result — the callee edge.
    Fp,
    /// Ten SSE arguments (XMM0..XMM7 then two stack words, F32 and F64 mixed),
    /// double result — the callee edge.
    Sse,
    /// Nine integer arguments, integer result — the CALLER edge: the control
    /// forwards them to the C-defined `host_int_ctl`.
    Caller,
    /// The interleaved mixed prototype, double result.
    Mix,
}

fn control_kind(name: &str) -> ControlKind {
    if INT_CONTROLS.iter().any(|(n, _, _)| *n == name) {
        return ControlKind::Int;
    }
    if FP_CONTROLS.iter().any(|(n, _)| *n == name) {
        return ControlKind::Fp;
    }
    if SSE_CONTROLS.iter().any(|(n, _)| *n == name) {
        return ControlKind::Sse;
    }
    if CALLER_CONTROLS.iter().any(|(n, _)| *n == name) {
        return ControlKind::Caller;
    }
    if MIX_CONTROLS.iter().any(|(n, _, _)| *n == name) {
        return ControlKind::Mix;
    }
    panic!("unknown control `{name}`");
}

/// Every control, in the order the driver calls them. Derived from the two
/// tables so a control can never be defined but left uncalled.
fn control_names() -> Vec<&'static str> {
    INT_CONTROLS
        .iter()
        .map(|(n, _, _)| *n)
        .chain(FP_CONTROLS.iter().map(|(n, _)| *n))
        .chain(SSE_CONTROLS.iter().map(|(n, _)| *n))
        .chain(CALLER_CONTROLS.iter().map(|(n, _)| *n))
        .chain(MIX_CONTROLS.iter().map(|(n, _, _)| *n))
        .collect()
}

/// A control is CORRECT exactly when its source order is the identity and it
/// does not narrow the return register — read off the table rather than listed
/// by hand, so a renamed or re-ordered control cannot silently change sides.
fn control_is_correct(name: &str) -> bool {
    let identity = |order: &[usize]| order.iter().enumerate().all(|(i, s)| i == *s);
    if let Some((_, order, narrow)) = INT_CONTROLS.iter().find(|(n, _, _)| *n == name) {
        return !*narrow && identity(order);
    }
    if let Some((_, order)) = FP_CONTROLS.iter().find(|(n, _)| *n == name) {
        return identity(order);
    }
    if let Some((_, order)) = SSE_CONTROLS.iter().find(|(n, _)| *n == name) {
        return identity(order);
    }
    if let Some((_, order)) = CALLER_CONTROLS.iter().find(|(n, _)| *n == name) {
        return identity(order);
    }
    if let Some((_, int_order, fp_order)) = MIX_CONTROLS.iter().find(|(n, _, _)| *n == name) {
        return identity(int_order) && identity(fp_order);
    }
    panic!("unknown control `{name}`");
}

/// The C driver. It provides BOTH sides that must not come from trust-cg: the
/// `extern "C"` reference the trust-cg caller lane calls, and the reference
/// arithmetic every subject is compared against.
fn driver_c() -> String {
    let a = INT_ARGS;
    let x = FP_ARGS;
    let w = INT_WEIGHTS;
    let fw = FP_WEIGHTS;
    let mfw = MIX_FP_WEIGHTS;
    let mut externs = String::new();
    let mut calls = String::new();
    for (tag, _, _) in C_EQUIVALENT {
        externs.push_str(&format!(
            "extern int64_t cc_{tag}_int(int64_t,int64_t,int64_t,int64_t,int64_t,int64_t,int64_t,int64_t);\n\
             extern double  cc_{tag}_fp(double,double,double,double,double,double);\n\
             extern double  cc_{tag}_sse(double,float,double,float,double,float,double,float,double,double);\n\
             extern double  cc_{tag}_mix(int64_t,double,int64_t,double,int64_t,double,int64_t,double,int64_t,int64_t,int64_t,int64_t);\n\
             extern int64_t cc_{tag}_caller(int64_t,int64_t,int64_t,int64_t,int64_t,int64_t,int64_t,int64_t);\n"
        ));
        externs.push_str(&format!(
            "int64_t host_int_{tag}(int64_t a0,int64_t a1,int64_t a2,int64_t a3,int64_t a4,int64_t a5,int64_t a6,int64_t a7)\n\
             {{ return ref_int(a0,a1,a2,a3,a4,a5,a6,a7); }}\n"
        ));
        calls.push_str(&format!(
            "  check_i(\"cc_{tag}_int\", cc_{tag}_int(A0,A1,A2,A3,A4,A5,A6,A7), want_int);\n\
               check_d(\"cc_{tag}_fp\", cc_{tag}_fp(X0,X1,X2,X3,X4,X5), want_fp);\n\
               check_d(\"cc_{tag}_sse\", cc_{tag}_sse(S0,S1,S2,S3,S4,S5,S6,S7,S8,S9), want_sse);\n\
               check_d(\"cc_{tag}_mix\", cc_{tag}_mix(A0,X0,A1,X1,A2,X2,A3,X3,A4,A5,A6,A7), want_mix);\n\
               check_i(\"cc_{tag}_caller\", cc_{tag}_caller(A0,A1,A2,A3,A4,A5,A6,A7), want_int);\n"
        ));
    }
    format!(
        r#"
#include <stdio.h>
#include <stdint.h>

#define A0 ((int64_t){a0})
#define A1 ((int64_t){a1})
#define A2 ((int64_t){a2})
#define A3 ((int64_t){a3})
#define A4 ((int64_t){a4})
#define A5 ((int64_t){a5})
#define A6 ((int64_t){a6})
#define A7 ((int64_t){a7})
#define X0 (({x0}))
#define X1 (({x1}))
#define X2 (({x2}))
#define X3 (({x3}))
#define X4 (({x4}))
#define X5 (({x5}))
#define S0 (({s0}))
#define S1 (({s1}f))
#define S2 (({s2}))
#define S3 (({s3}f))
#define S4 (({s4}))
#define S5 (({s5}f))
#define S6 (({s6}))
#define S7 (({s7}f))
#define S8 (({s8}))
#define S9 (({s9}))

static int failures = 0;

static int64_t ref_int(int64_t a0,int64_t a1,int64_t a2,int64_t a3,
                       int64_t a4,int64_t a5,int64_t a6,int64_t a7) {{
    return a0*{w0} + a1*{w1} + a2*{w2} + a3*{w3}
         + a4*{w4} + a5*{w5} + a6*{w6} + a7*{w7};
}}

{externs}

static void check_i(const char *name, int64_t got, int64_t want) {{
    if (got != want) {{ printf("MISMATCH %s got=%lld want=%lld\n", name,
                               (long long)got, (long long)want); failures++; }}
    else printf("ok %s\n", name);
}}
static void check_d(const char *name, double got, double want) {{
    if (got != want) {{ printf("MISMATCH %s got=%.17g want=%.17g\n", name, got, want); failures++; }}
    else printf("ok %s\n", name);
}}

int main(void) {{
    int64_t want_int = ref_int(A0,A1,A2,A3,A4,A5,A6,A7);
    double want_fp = X0*{fw0} + X1*{fw1} + X2*{fw2} + X3*{fw3} + X4*{fw4} + X5*{fw5};
    double want_mix = (double)A0*{w0} + (double)A1*{w1} + (double)A2*{w2} + (double)A3*{w3}
                    + (double)A4*{w4} + (double)A5*{w5} + (double)A6*{w6} + (double)A7*{w7}
                    + X0*{mfw0} + X1*{mfw1} + X2*{mfw2} + X3*{mfw3};
    double want_sse = (double)S0*{sw0} + (double)S1*{sw1} + (double)S2*{sw2} + (double)S3*{sw3}
                    + (double)S4*{sw4} + (double)S5*{sw5} + (double)S6*{sw6} + (double)S7*{sw7}
                    + (double)S8*{sw8} + (double)S9*{sw9};
    printf("want_int=%lld\n", (long long)want_int);
    printf("want_fp=%.17g\n", want_fp);
    printf("want_mix=%.17g\n", want_mix);
    printf("want_sse=%.17g\n", want_sse);
{calls}
    if (failures) return 1;
    printf("SUBJECTS_OK={n}\n");
    return 0;
}}
"#,
        a0 = a[0],
        a1 = a[1],
        a2 = a[2],
        a3 = a[3],
        a4 = a[4],
        a5 = a[5],
        a6 = a[6],
        a7 = a[7],
        x0 = fmt_f64(x[0]),
        x1 = fmt_f64(x[1]),
        x2 = fmt_f64(x[2]),
        x3 = fmt_f64(x[3]),
        x4 = fmt_f64(x[4]),
        x5 = fmt_f64(x[5]),
        w0 = w[0],
        w1 = w[1],
        w2 = w[2],
        w3 = w[3],
        w4 = w[4],
        w5 = w[5],
        w6 = w[6],
        w7 = w[7],
        fw0 = fw[0],
        fw1 = fw[1],
        fw2 = fw[2],
        fw3 = fw[3],
        fw4 = fw[4],
        fw5 = fw[5],
        mfw0 = mfw[0],
        mfw1 = mfw[1],
        mfw2 = mfw[2],
        mfw3 = mfw[3],
        s0 = fmt_f64(SSE_ARGS[0]),
        s1 = fmt_f64(SSE_ARGS[1]),
        s2 = fmt_f64(SSE_ARGS[2]),
        s3 = fmt_f64(SSE_ARGS[3]),
        s4 = fmt_f64(SSE_ARGS[4]),
        s5 = fmt_f64(SSE_ARGS[5]),
        s6 = fmt_f64(SSE_ARGS[6]),
        s7 = fmt_f64(SSE_ARGS[7]),
        s8 = fmt_f64(SSE_ARGS[8]),
        s9 = fmt_f64(SSE_ARGS[9]),
        sw0 = SSE_WEIGHTS[0],
        sw1 = SSE_WEIGHTS[1],
        sw2 = SSE_WEIGHTS[2],
        sw3 = SSE_WEIGHTS[3],
        sw4 = SSE_WEIGHTS[4],
        sw5 = SSE_WEIGHTS[5],
        sw6 = SSE_WEIGHTS[6],
        sw7 = SSE_WEIGHTS[7],
        sw8 = SSE_WEIGHTS[8],
        sw9 = SSE_WEIGHTS[9],
        externs = externs,
        calls = calls,
        n = C_EQUIVALENT.len() * 5,
    )
}

fn fmt_f64(v: f64) -> String {
    format!("{v:.1}")
}

/// The control driver. It calls the eight assembly controls and prints one
/// line each, in a form the Rust side pins verbatim.
fn control_driver_c() -> String {
    let a = int_args_with_ninth();
    let x = FP_ARGS;
    let mut decls = String::new();
    let mut calls = String::new();
    for name in control_names() {
        match control_kind(name) {
            ControlKind::Int | ControlKind::Caller => {
                decls.push_str(&format!(
                    "extern int64_t {name}(int64_t,int64_t,int64_t,int64_t,int64_t,int64_t,int64_t,int64_t,int64_t);\n"
                ));
                calls.push_str(&format!(
                    "  printf(\"control {name}: got=%.17g (as stated)\\n\", (double){name}(A0,A1,A2,A3,A4,A5,A6,A7,A8)); ran++;\n"
                ));
            }
            ControlKind::Fp => {
                decls.push_str(&format!(
                    "extern double {name}(double,double,double,double,double,double);\n"
                ));
                calls.push_str(&format!(
                    "  printf(\"control {name}: got=%.17g (as stated)\\n\", {name}(X0,X1,X2,X3,X4,X5)); ran++;\n"
                ));
            }
            ControlKind::Sse => {
                decls.push_str(&format!(
                    "extern double {name}(double,float,double,float,double,float,double,float,double,double);\n"
                ));
                calls.push_str(&format!(
                    "  printf(\"control {name}: got=%.17g (as stated)\\n\", {name}(S0,S1,S2,S3,S4,S5,S6,S7,S8,S9)); ran++;\n"
                ));
            }
            ControlKind::Mix => {
                decls.push_str(&format!(
                    "extern double {name}(int64_t,double,int64_t,double,int64_t,double,int64_t,double,int64_t,int64_t,int64_t,int64_t);\n"
                ));
                calls.push_str(&format!(
                    "  printf(\"control {name}: got=%.17g (as stated)\\n\", {name}(A0,X0,A1,X1,A2,X2,A3,X3,A4,A5,A6,A7)); ran++;\n"
                ));
            }
        }
    }
    format!(
        r#"
#include <stdio.h>
#include <stdint.h>

#define A0 ((int64_t){a0})
#define A1 ((int64_t){a1})
#define A2 ((int64_t){a2})
#define A3 ((int64_t){a3})
#define A4 ((int64_t){a4})
#define A5 ((int64_t){a5})
#define A6 ((int64_t){a6})
#define A7 ((int64_t){a7})
#define A8 ((int64_t){a8})
#define X0 (({x0}))
#define X1 (({x1}))
#define X2 (({x2}))
#define X3 (({x3}))
#define X4 (({x4}))
#define X5 (({x5}))
#define S0 (({s0}))
#define S1 (({s1}f))
#define S2 (({s2}))
#define S3 (({s3}f))
#define S4 (({s4}))
#define S5 (({s5}f))
#define S6 (({s6}))
#define S7 (({s7}f))
#define S8 (({s8}))
#define S9 (({s9}))

/// The far side of the CALLER controls' outgoing edge: the C function they
/// forward their arguments to. It is compiled by the host toolchain, so the
/// argument REGISTERS and stack slots it reads from are clang's, not
/// trust-cg's.
int64_t host_int_ctl(int64_t a0,int64_t a1,int64_t a2,int64_t a3,
                     int64_t a4,int64_t a5,int64_t a6,int64_t a7) {{
    return a0*{w0} + a1*{w1} + a2*{w2} + a3*{w3}
         + a4*{w4} + a5*{w5} + a6*{w6} + a7*{w7};
}}

{decls}

int main(void) {{
    int ran = 0;
{calls}
    printf("CONTROLS_RUN=%d\n", ran);
    return 0;
}}
"#,
        a0 = a[0],
        a1 = a[1],
        a2 = a[2],
        a3 = a[3],
        a4 = a[4],
        a5 = a[5],
        a6 = a[6],
        a7 = a[7],
        a8 = a[8],
        x0 = fmt_f64(x[0]),
        x1 = fmt_f64(x[1]),
        x2 = fmt_f64(x[2]),
        x3 = fmt_f64(x[3]),
        x4 = fmt_f64(x[4]),
        x5 = fmt_f64(x[5]),
        w0 = INT_WEIGHTS[0],
        w1 = INT_WEIGHTS[1],
        w2 = INT_WEIGHTS[2],
        w3 = INT_WEIGHTS[3],
        w4 = INT_WEIGHTS[4],
        w5 = INT_WEIGHTS[5],
        w6 = INT_WEIGHTS[6],
        w7 = INT_WEIGHTS[7],
        s0 = fmt_f64(SSE_ARGS[0]),
        s1 = fmt_f64(SSE_ARGS[1]),
        s2 = fmt_f64(SSE_ARGS[2]),
        s3 = fmt_f64(SSE_ARGS[3]),
        s4 = fmt_f64(SSE_ARGS[4]),
        s5 = fmt_f64(SSE_ARGS[5]),
        s6 = fmt_f64(SSE_ARGS[6]),
        s7 = fmt_f64(SSE_ARGS[7]),
        s8 = fmt_f64(SSE_ARGS[8]),
        s9 = fmt_f64(SSE_ARGS[9]),
        decls = decls,
        calls = calls,
    )
}

fn cc_x86_64(args: &[&str]) -> (bool, String) {
    let mut cmd = Command::new("cc");
    // Apple's driver flag only; GNU/Linux `cc` rejects `-arch`.
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

fn scratch_dir(tag: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!(
        "trust_cg_x86_calling_conv_{tag}_{}",
        std::process::id()
    ));
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).expect("create scratch dir");
    dir
}

fn build_and_run(
    dir: &Path,
    sources: &[(&str, String)],
    objects: &[(&str, &[u8])],
) -> (i32, String) {
    let mut args: Vec<String> = vec![
        "-O2".into(),
        "-o".into(),
        dir.join("bin").to_string_lossy().into_owned(),
    ];
    for (name, text) in sources {
        let path = dir.join(name);
        fs::write(&path, text).expect("write source");
        args.push(path.to_string_lossy().into_owned());
    }
    for (name, bytes) in objects {
        let path = dir.join(name);
        fs::write(&path, bytes).expect("write object");
        args.push(path.to_string_lossy().into_owned());
    }
    let refs: Vec<&str> = args.iter().map(String::as_str).collect();
    let (ok, stderr) = cc_x86_64(&refs);
    assert!(ok, "link failed; files={dir:?}\n{stderr}");
    let run = run_executable_with_timeout(&dir.join("bin"), codegen_run_timeout())
        .expect("run calling-convention oracle");
    assert!(
        !run.timed_out,
        "calling-convention oracle timed out; files={dir:?}"
    );
    let stdout = String::from_utf8_lossy(&run.output.stdout).to_string();
    (run.output.status.code().unwrap_or(-1), stdout)
}

// ===========================================================================
// (E2) The control battery — establishes that the oracle can SEE a wrong
// register assignment. It runs first, and its failure is reported as a control
// failure, never as a subject result.
// ===========================================================================

#[test]
fn x86_64_calling_conv_control_battery_refutes_every_abi_defect() {
    if !x86_64_oracle_enabled("x86_64_calling_conv_control_battery") {
        eprintln!(
            "SKIP: (E2) NOT RUN — the x86-64 execution oracle is unavailable on this host, so \
             the wrong-register-assignment control battery did not run and the (E1) subject lane \
             has no established discriminating power. The (E3) admission controls still ran."
        );
        return;
    }
    let _guard = SERIAL.lock().unwrap_or_else(|p| p.into_inner());

    let dir = scratch_dir("controls");
    let (code, stdout) = build_and_run(
        &dir,
        &[
            ("controls.s", controls_asm()),
            ("control_driver.c", control_driver_c()),
        ],
        &[],
    );
    eprintln!("[E2 control battery]\n{stdout}");
    assert_eq!(
        code, 0,
        "the control driver itself failed; files={dir:?}\n{stdout}"
    );

    let want_int = ref_int(INT_ARGS) as f64;
    let want_fp = ref_fp(FP_ARGS);
    let want_mix = ref_mix(INT_ARGS, mix_fp_args());
    let want_sse = ref_sse(SSE_ARGS);
    let mut checked = 0usize;
    for name in control_names() {
        let predicted = control_prediction(name);
        // The C driver prints with %.17g; format the prediction the same way.
        assert!(
            stdout.contains(&format!(
                "control {name}: got={} (as stated)",
                format_g17(predicted)
            )),
            "control `{name}` did not print its INDEPENDENTLY PREDICTED value {}. Either the \
             control was disarmed, repointed at a different callee, or the Rust model of the \
             defect is wrong — all three must fail here:\n{stdout}",
            format_g17(predicted)
        );
        // Each control is compared against the reference for ITS OWN lane:
        // the integer and caller lanes against the integer reference, the FP
        // lane against the FP one, the mixed lane against the mixed one.
        let reference = match control_kind(name) {
            ControlKind::Int | ControlKind::Caller => want_int,
            ControlKind::Fp => want_fp,
            ControlKind::Sse => want_sse,
            ControlKind::Mix => want_mix,
        };
        if control_is_correct(name) {
            assert_eq!(
                predicted, reference,
                "control `{name}` is declared CORRECT but its model does not reproduce the \
                 reference — the battery's non-vacuity anchor is broken"
            );
        } else {
            assert_ne!(
                predicted, reference,
                "control `{name}` is declared DEFECTIVE but produces the reference value, so it \
                 refutes nothing: a no-op dressed as a control"
            );
        }
        checked += 1;
    }
    assert_eq!(checked, control_names().len());
    assert!(
        stdout.contains(&format!("CONTROLS_RUN={}", control_names().len())),
        "the control driver did not report all {} controls as RUN; a control that never executed \
         cannot be counted:\n{stdout}",
        control_names().len()
    );
    let _ = fs::remove_dir_all(&dir);
}

/// `%.17g`, matching the C driver's printf.
fn format_g17(v: f64) -> String {
    // A `%.17g` of an exactly-representable integral double prints the integer
    // with no exponent as long as its magnitude is below 1e17, which every
    // value in this file is.
    if v == v.trunc() && v.abs() < 1e17 {
        format!("{}", v as i64)
    } else {
        format!("{v:.17e}")
    }
}

// ===========================================================================
// (E1) The subject lane
// ===========================================================================

#[test]
fn x86_64_c_compatible_conventions_match_clang_in_both_directions() {
    if !x86_64_oracle_enabled("x86_64_c_compatible_conventions") {
        eprintln!(
            "SKIP: (E1) NOT RUN — the x86-64 EXECUTION oracle is unavailable on this host, so the \
             only oracle that can catch a wrong register assignment for a non-C convention did \
             not run. The (E3) admission controls still ran."
        );
        return;
    }
    let _guard = SERIAL.lock().unwrap_or_else(|p| p.into_inner());

    let callees = build_subject_module();
    let callers = build_caller_module();
    for opt in ALL_OPT {
        let callee_object = compile_x86_subject(&callees, opt)
            .unwrap_or_else(|e| panic!("x86-64 callee lanes must compile at {opt:?}: {e}"));
        let caller_object = compile_x86_subject(&callers, opt)
            .unwrap_or_else(|e| panic!("x86-64 caller lanes must compile at {opt:?}: {e}"));
        let dir = scratch_dir(&format!("subject_{opt:?}"));
        let (code, stdout) = build_and_run(
            &dir,
            &[("driver.c", driver_c())],
            &[
                ("callees.o", callee_object.as_slice()),
                ("callers.o", caller_object.as_slice()),
            ],
        );
        eprintln!("[E1 subjects {opt:?}]\n{stdout}");
        assert_eq!(
            code, 0,
            "a non-C calling convention diverged from the host C ABI at {opt:?}; files={dir:?}\n{stdout}"
        );
        assert!(
            stdout.contains(&format!("SUBJECTS_OK={}", C_EQUIVALENT.len() * 5)),
            "the driver did not report all {} subject checks at {opt:?}:\n{stdout}",
            C_EQUIVALENT.len() * 5
        );
        // The independently computed Rust references must be the ones the C
        // driver compared against; otherwise both sides could agree on a wrong
        // number.
        assert!(
            stdout.contains(&format!("want_int={}", ref_int(INT_ARGS))),
            "the C driver's integer reference differs from the Rust one:\n{stdout}"
        );
        assert!(
            stdout.contains(&format!("want_fp={}", format_g17(ref_fp(FP_ARGS)))),
            "the C driver's FP reference differs from the Rust one:\n{stdout}"
        );
        assert!(
            stdout.contains(&format!(
                "want_mix={}",
                format_g17(ref_mix(INT_ARGS, mix_fp_args()))
            )),
            "the C driver's mixed reference differs from the Rust one:\n{stdout}"
        );
        assert!(
            stdout.contains(&format!("want_sse={}", format_g17(ref_sse(SSE_ARGS)))),
            "the C driver's SSE-file reference differs from the Rust one:\n{stdout}"
        );
        let _ = fs::remove_dir_all(&dir);
    }
}

// ===========================================================================
// (E3) Admission controls — always run
// ===========================================================================

fn swift_module(tag: &str, params: Vec<Ty>, returns: Vec<Ty>) -> trust_ir::Module {
    scalar_module_with_conv(tag, CallingConv::Swift, params, returns)
}

/// A function whose body just returns constants of the requested return types,
/// so the module exercises the SIGNATURE and nothing else.
fn scalar_module_with_conv(
    tag: &str,
    conv: CallingConv,
    params: Vec<Ty>,
    returns: Vec<Ty>,
) -> trust_ir::Module {
    let mut m = ModuleBuilder::new(tag);
    let sig = m.add_func_type(params.clone(), returns.clone());
    {
        let mut f = m.function("subject", sig);
        f.set_calling_conv(conv);
        let entry = f.create_block();
        for ty in &params {
            f.add_block_param(entry, ty.clone());
        }
        f.switch_to_block(entry);
        let values: Vec<_> = returns
            .iter()
            .map(|ty| match ty {
                Ty::F16 | Ty::F32 | Ty::F64 => f.fconst(ty.clone(), 1.0),
                other => f.iconst(other.clone(), 7),
            })
            .collect();
        f.ret(values);
        f.build();
    }
    m.build().expect("ModuleBuilder::build: test fixture")
}

fn refuses_on(module: &trust_ir::Module, target: Target) -> String {
    match compile_for(module, target, OptLevel::O0) {
        Ok(_) => panic!("expected a fail-closed refusal for {target:?}, but the module compiled"),
        Err(e) => e,
    }
}

#[test]
fn e3_c_equivalent_conventions_are_admitted_on_x86_64() {
    // NON-VACUITY for every other control in this section: the guard is not
    // "reject everything".
    for (tag, conv, why) in C_EQUIVALENT {
        eprintln!("[E3 admitted] cc_{tag} ({conv:?}): {why}");
    }
    let module = build_subject_module();
    for opt in ALL_OPT {
        compile_for(&module, Target::X86_64, opt).unwrap_or_else(|e| {
            panic!("C/Rust/Fast/Cold must be admitted on x86-64 at {opt:?}: {e}")
        });
    }
}

/// THE MEASUREMENT THAT SIZES (E1). The file header states, as the reason this
/// lane is not a wrong-code hazard, that `C`, `Rust`, `Fast` and `Cold` produce
/// the BYTE-IDENTICAL x86-64 object for the same body — that a `CallingConv`
/// never reaches x86-64 lowering and only the admission decision reads it.
///
/// Nothing checked that. It matters in both directions:
///   * it is what makes the `rust` / `fast` / `cold` quarters of (E1) a RE-RUN
///     of the `c` quarter rather than independent evidence about conventions,
///     which the header must not overstate; and
///   * it is the claim that would silently become false the day a convention
///     did start reaching lowering — at which point those three quarters would
///     become load-bearing and would need their own clang oracle.
///
/// Each module here has the SAME name and the SAME function name, so only the
/// convention differs and a byte comparison is meaningful.
#[test]
fn e3_the_c_equivalent_conventions_compile_to_the_identical_object() {
    for opt in ALL_OPT {
        let mut reference: Option<(&str, Vec<u8>)> = None;
        for (tag, conv, _) in C_EQUIVALENT {
            let module = scalar_module_with_conv(
                "conv_identity",
                conv,
                vec![Ty::I64; 8],
                vec![Ty::I64, Ty::F64],
            );
            let object = compile_for(&module, Target::X86_64, opt).unwrap_or_else(|e| {
                panic!("cc_{tag} ({conv:?}) must be admitted on x86-64 at {opt:?}: {e}")
            });
            match &reference {
                None => reference = Some((tag, object)),
                Some((ref_tag, ref_object)) => assert_eq!(
                    &object, ref_object,
                    "at {opt:?} the {conv:?} convention produced a DIFFERENT x86-64 object from \
                     {ref_tag}. That contradicts this file's stated framing — that a trust-ir \
                     CallingConv never reaches x86-64 lowering and the only thing a convention \
                     does is the adapter's admission decision. If a convention now reaches \
                     lowering, the rust/fast/cold quarters of (E1) are no longer a re-run of the \
                     C quarter and need their own oracle, and the admission guard is no longer \
                     the whole story"
                ),
            }
        }
    }
}

#[test]
fn e3_swift_return_budget_is_architecture_indexed() {
    // THE control for the change itself. A 3-INTEGER-component Swift return is
    // inside AAPCS64's combined budget of 4 (x0,x1,x2) and OUTSIDE SysV's
    // integer return file (RAX,RDX). The SAME module must therefore be
    // accepted for aarch64 and refused for x86-64. If the `arch` argument were
    // ignored, one of these two assertions must fail whichever way it was
    // ignored.
    let module = swift_module("swift_three_int", vec![Ty::I64], vec![Ty::I64; 3]);
    let error = refuses_on(&module, Target::X86_64);
    assert!(
        error.contains("Swift"),
        "the x86-64 refusal does not name the CONVENTION, which is the whole point of moving it \
         out of the ISel return classifier: {error}"
    );
    assert!(
        error.contains("x86_64"),
        "the x86-64 refusal does not name the TARGET whose budget was applied: {error}"
    );
    assert!(
        error.contains("2 integer and 2 FP"),
        "the x86-64 refusal does not state the budget it applied: {error}"
    );
    assert!(
        error.contains("3 integer + 0 FP"),
        "the x86-64 refusal does not state the SHAPE it rejected: {error}"
    );
    compile_for(&module, Target::Aarch64, OptLevel::O0).expect(
        "a 3-integer-component Swift return is inside AAPCS64's combined budget of 4 and must \
         stay admitted on aarch64 — if this fails, the arch index changed aarch64 behaviour",
    );
}

#[test]
fn e3_swift_fp_return_budget_is_architecture_indexed() {
    // The FP twin: three FP components fit AAPCS64's v0-v2 and overflow SysV's
    // XMM0,XMM1 return file.
    let module = swift_module("swift_three_fp", vec![Ty::F64], vec![Ty::F64; 3]);
    let error = refuses_on(&module, Target::X86_64);
    assert!(
        error.contains("Swift") && error.contains("0 integer + 3 FP"),
        "the x86-64 FP refusal does not name the convention and the shape: {error}"
    );
    compile_for(&module, Target::Aarch64, OptLevel::O0)
        .expect("three FP return components stay admitted on aarch64");
}

#[test]
fn e3_swift_i128_counts_as_two_integer_components() {
    // i128 is an aligned GPR pair on BOTH targets, so (i128) alone is 2
    // integer components and fits SysV's RAX:RDX, while (i128, i64) is 3 and
    // does not. This control refutes "the counter treats every return as one
    // component".
    let ok = swift_module("swift_i128_only", vec![Ty::I64], vec![Ty::I128]);
    compile_for(&ok, Target::X86_64, OptLevel::O0)
        .expect("a lone i128 Swift return occupies RAX:RDX exactly as under C");

    let over = swift_module("swift_i128_plus", vec![Ty::I64], vec![Ty::I128, Ty::I64]);
    let error = refuses_on(&over, Target::X86_64);
    assert!(
        error.contains("3 integer + 0 FP"),
        "an i128 must count as TWO integer components; this refusal does not say so: {error}"
    );
}

#[test]
fn e3_swift_full_sysv_return_file_is_admitted() {
    // The upper corner of the x86-64 budget: 2 integer + 2 FP components is
    // exactly RAX,RDX,XMM0,XMM1 under C and exactly where `swiftcc` puts them
    // too (its wider file is allocated from the front). It must be ADMITTED —
    // without this, the budget could be "reject everything with more than one
    // return" and every refusal control above would still pass.
    let module = swift_module(
        "swift_full_file",
        vec![Ty::I64],
        vec![Ty::I64, Ty::I64, Ty::F64, Ty::F64],
    );
    compile_for(&module, Target::X86_64, OptLevel::O0)
        .expect("2 integer + 2 FP Swift return components are the exact SysV return file");
}

#[test]
fn e3_swift_aggregate_stays_fail_closed_on_x86_64() {
    // The aarch64 Swift aggregate SCALARIZATION (`swift_rewrite_module`)
    // reproduces the aarch64-apple-darwin swiftcall ABI and is gated to that
    // architecture, so on x86-64 an aggregate swiftcc signature keeps its
    // struct type and must be refused rather than lowered as C.
    use trust_ir::{
        Block as TrustIrBlock, BlockId, FieldDef, FuncId, FuncTy, Function as TrustIrFunction,
        Inst, InstrNode, Module as TrustIrModule, StructDef, StructId, StructRepr, ValueId,
    };
    let mut m = TrustIrModule::new("swift_agg_x86");
    m.structs.push(StructDef {
        origin: None,
        id: StructId::new(0),
        name: "Pair".to_string(),
        fields: (0..2)
            .map(|i| FieldDef {
                name: format!("f{i}"),
                ty: Ty::I64,
                offset: None,
            })
            .collect(),
        size: None,
        align: None,
        repr: StructRepr::C,
    });
    let agg = Ty::Struct(StructId::new(0));
    let ft = m
        .add_func_type(FuncTy {
            params: vec![agg.clone()],
            returns: vec![agg.clone()],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut f = TrustIrFunction::new(FuncId::new(0), "swifty", ft, BlockId::new(0));
    f.calling_conv = CallingConv::Swift;
    f.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), agg)],
        body: vec![InstrNode::new(Inst::Return {
            values: vec![ValueId::new(0)],
        })],
    }];
    m.try_add_function(f)
        .expect("Module::try_add_function: test fixture");
    let error = refuses_on(&m, Target::X86_64);
    assert!(
        error.contains("Swift") && error.contains("x86_64"),
        "the aggregate Swift refusal must name the convention and the target: {error}"
    );
    assert!(
        error.contains("parameter 0") && error.contains("aggregate"),
        "the aggregate refusal must say WHICH premise failed — here the aggregate PARAMETER, \
         which the guard reaches before it looks at the return: {error}"
    );
}

#[test]
fn e3_the_same_shape_under_c_is_refused_by_a_distinct_path() {
    // STRUCTURAL DISTINCTNESS. A 3-integer return is also unsupported under
    // `extern "C"` on x86-64 — but for a different reason: System V's C return
    // file has no third integer register, and TrustCG's internal multi-result
    // registers past it (RCX, ...) are admitted only on a Fast/Cold edge. The
    // adapter's `[TCG-X86-MULTI-RESULT]` guard refuses it and names the C
    // convention, not Swift's budget. (Before that guard existed the ISel
    // return classifier refused it, "integer result register capacity is
    // exhausted".) If both refusals were the same string, the Swift controls
    // above would be detecting the C limitation and asserting nothing about
    // Swift.
    let c_module = scalar_module_with_conv(
        "c_three_int",
        CallingConv::C,
        vec![Ty::I64],
        vec![Ty::I64; 3],
    );
    let c_error = refuses_on(&c_module, Target::X86_64);
    assert!(
        c_error.contains("[TCG-X86-MULTI-RESULT]")
            && c_error.contains("under calling convention C"),
        "the C-convention refusal is expected to come from the x86 multi-result guard: {c_error}"
    );
    assert!(
        !c_error.contains("Swift"),
        "the C-convention refusal must not mention Swift, or the two paths are not distinct: \
         {c_error}"
    );

    let swift_module = swift_module("swift_three_int_distinct", vec![Ty::I64], vec![Ty::I64; 3]);
    let swift_error = refuses_on(&swift_module, Target::X86_64);
    assert!(
        !swift_error.contains("integer result register capacity is exhausted"),
        "the Swift refusal must now come from the ADAPTER, not from ISel: {swift_error}"
    );
    assert_ne!(
        c_error, swift_error,
        "the two refusal paths produce the identical message, so neither control distinguishes \
         an ABI divergence from ordinary incompleteness"
    );
}

#[test]
fn e3_variadic_swift_stays_fail_closed_on_x86_64() {
    use trust_ir::{
        Block as TrustIrBlock, BlockId, Constant, FuncId, FuncTy, Function as TrustIrFunction,
        Inst, InstrNode, Module as TrustIrModule, ValueId,
    };
    let mut m = TrustIrModule::new("swift_vararg_x86");
    let ft = m
        .add_func_type(FuncTy {
            params: vec![Ty::I64],
            returns: vec![Ty::I64],
            abi: None,
            is_vararg: true,
        })
        .expect("Module::add_func_type: test fixture");
    let mut f = TrustIrFunction::new(FuncId::new(0), "swifty_va", ft, BlockId::new(0));
    f.calling_conv = CallingConv::Swift;
    f.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), Ty::I64)],
        body: vec![
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(1),
            })
            .with_result(ValueId::new(1)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(1)],
            }),
        ],
    }];
    m.try_add_function(f)
        .expect("Module::try_add_function: test fixture");
    let error = refuses_on(&m, Target::X86_64);
    // It fails closed. The diagnostic is the VARIADIC-DEFINITION one, not a
    // convention-specific one, because `reject_variadic_definition` runs first
    // — deliberately, so that every lowering entry reports one named refusal
    // for a variadic definition whatever its convention
    // (`abi_definition_refusals::variadic_definitions_are_refused_by_every_adapter_entry`
    // pins that for C/Fast/Cold/Swift alike).
    // (`refuses_on` renders the error with `Debug`, so this is the variant
    // name rather than the `[TCG-VARIADIC-DEFINITION]` Display tag.)
    assert!(
        error.contains("VariadicDefinitionUnsupported"),
        "a variadic swiftcc DEFINITION must fail closed: {error}"
    );
    // What must NOT be true is that this refusal is the only thing standing
    // between swiftcc varargs and the C ABI's register layout. It is not: the
    // convention guard is SHADOWED here, not absent. The unshadowed exercise
    // is the declaration case below, which this test would otherwise be
    // mistaken for.
}

/// The convention guard that a variadic swiftcc DEFINITION only SHADOWS is
/// live and refusing, exercised where nothing can shadow it.
///
/// `reject_variadic_definition` accepts bodyless declarations by construction
/// (`abi_definition_refusals` pins that too), so for a variadic `Swift`
/// DECLARATION called directly there is no variadic-definition refusal in the
/// path at all. The only thing that can refuse it is
/// `validate_direct_call_signature`'s convention guard — whose
/// `swift_signature_is_c_abi_equivalent` premise requires `!is_vararg`.
///
/// This is the test that has teeth for the durability question: if va_list
/// lowering ever lands and the variadic-definition refusal is lifted, THIS
/// guard is what keeps a swiftcc variadic from inheriting the C ABI, and it is
/// proven live here independently of the refusal ordering above.
#[test]
fn e3_variadic_swift_conv_guard_is_live_where_nothing_shadows_it() {
    let mut module = swift_direct_call_module::<1>(X86_SUBJECT_TRIPLE);
    // Make the CALLEE's signature variadic. Its return stays a single integer,
    // inside SysV's file, so the budget cannot be what refuses it — only the
    // variadic premise can.
    let callee_ty = module
        .functions
        .iter()
        .find(|f| f.name == "swifty_callee")
        .expect("swifty_callee")
        .ty;
    module.func_types[callee_ty.as_usize()].is_vararg = true;

    let error = match Compiler::new_for_target_spec(
        CompilerConfig {
            opt_level: OptLevel::O0,
            ..CompilerConfig::default()
        },
        TargetSpec::parse(X86_SUBJECT_TRIPLE).expect("the host x86-64 triple is a known triple"),
    )
    .with_codegen_license(permit_unlicensed())
    .compile(&module)
    {
        Ok(_) => panic!(
            "a direct call to a VARIADIC swiftcc declaration compiled for x86-64. No \
             variadic-definition refusal applies to a declaration, so the convention guard was \
             the only thing that could refuse it, and it did not"
        ),
        Err(e) => format!("{e:?}"),
    };
    assert!(
        error.contains("Swift") && error.contains("the signature is variadic"),
        "the refusal must come from the ADAPTER's convention guard, naming the convention and \
         the premise that failed: {error}"
    );
    assert!(
        !error.contains("[TCG-VARIADIC-DEFINITION]"),
        "a DECLARATION must not be reported as a variadic definition — that would mean the \
         shadowing refusal reaches this path too, and the guard under test is untested: {error}"
    );
}

/// A module whose ONLY Swift-convention function is a BODYLESS DECLARATION,
/// called directly by a defined function.
///
/// This is the shape that reaches the adapter's DIRECT-CALL guard
/// (`validate_direct_call_signature`) rather than its per-function definition
/// guard: the declaration has no body, so the definition guard never sees it,
/// and the only thing standing between the call and x86-64 lowering is the
/// call-site guard's own `arch` argument.
///
/// A bodyless declaration is an FFI boundary, so trust-ir requires
/// `target_info`; the module is therefore built for one exact triple.
fn swift_direct_call_module<const N: usize>(triple: &str) -> trust_ir::Module {
    let returns = vec![Ty::I64; N];
    let mut m = ModuleBuilder::new_with_target_info(
        "swift_direct_call",
        trust_ir::TargetInfo {
            triple: triple.into(),
            pointer_size: 8,
            endianness: trust_ir::Endianness::Little,
            abi: None,
            struct_passing: trust_ir::StructPassingPolicy::NativeC,
        },
    );
    let callee_sig = m.add_func_type(vec![Ty::I64], returns.clone());
    let caller_sig = m.add_func_type(vec![Ty::I64], vec![Ty::I64]);
    let callee = m.declare_function("swifty_callee", callee_sig);
    {
        let mut f = m.function("probe_caller", caller_sig);
        let entry = f.create_block();
        let p = f.add_block_param(entry, Ty::I64);
        f.switch_to_block(entry);
        let results = f.call_results::<N>(callee, vec![p]);
        f.ret(vec![results[0]]);
        f.build();
    }
    let mut module = m.build().expect("ModuleBuilder::build: test fixture");
    for function in &mut module.functions {
        if function.name == "swifty_callee" {
            function.calling_conv = CallingConv::Swift;
        }
    }
    module
}

/// A module whose only Swift edge is a `CallIndirect`, which belongs to no
/// function header at all and is therefore invisible to both the definition
/// guard and the direct-call guard.
///
/// trust-ir refuses a cross-convention indirect edge, so the enclosing function
/// must carry `Swift` too; its OWN signature is deliberately inside every
/// target's budget (one pointer parameter, one integer return) so that the
/// definition guard admits it and the refusal, when it comes, can only be the
/// indirect-call guard's.
fn swift_indirect_call_module(returns: Vec<Ty>) -> trust_ir::Module {
    use trust_ir::{
        Block as TrustIrBlock, BlockId, Constant, FuncId, FuncTy, Function as TrustIrFunction,
        Inst, InstrNode, Module as TrustIrModule, ValueId,
    };
    let mut m = TrustIrModule::new("swift_indirect_call");
    let caller_ty = m
        .add_func_type(FuncTy {
            params: vec![Ty::Ptr],
            returns: vec![Ty::I64],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let callee_ty = m
        .add_func_type(FuncTy {
            params: vec![Ty::I64],
            returns: returns.clone(),
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut f = TrustIrFunction::new(FuncId::new(0), "probe_indirect", caller_ty, BlockId::new(0));
    f.calling_conv = CallingConv::Swift;
    let mut body = vec![
        InstrNode::new(Inst::Const {
            ty: Ty::I64,
            value: Constant::Int(3),
        })
        .with_result(ValueId::new(1)),
    ];
    let mut call = InstrNode::new(Inst::CallIndirect {
        callee: ValueId::new(0),
        sig: callee_ty,
        args: vec![ValueId::new(1)],
        calling_conv: CallingConv::Swift,
    });
    for index in 0..returns.len() {
        call = call.with_result(ValueId::new(2 + index as u32));
    }
    body.push(call);
    body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(2)],
    }));
    f.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), Ty::Ptr)],
        body,
    }];
    m.try_add_function(f)
        .expect("Module::try_add_function: test fixture");
    m
}

/// (M10) THE DIRECT-CALL GUARD IS ARCHITECTURE-INDEXED TOO.
///
/// `conv_sig_uses_c_register_abi` is applied at THREE sites — the function
/// definition, the direct call and the indirect call — and every committed test
/// exercised only the first. Hardcoding `GuardCarrierArch::AArch64` at both
/// call-site guards left the whole target green while restoring exactly the
/// pre-change, architecture-blind behaviour at two of the three enforcement
/// points.
///
/// This is that mutation's refutation: the Swift signature here is reachable
/// ONLY through the direct-call guard.
#[test]
fn e3_swift_direct_call_budget_is_architecture_indexed() {
    let module = swift_direct_call_module::<3>(X86_SUBJECT_TRIPLE);
    let error = match Compiler::new_for_target_spec(
        CompilerConfig {
            opt_level: OptLevel::O0,
            ..CompilerConfig::default()
        },
        TargetSpec::parse(X86_SUBJECT_TRIPLE).expect("the host x86-64 triple is a known triple"),
    )
    .with_codegen_license(permit_unlicensed())
    .compile(&module)
    {
        Ok(_) => panic!(
            "a DIRECT CALL to a Swift callee whose return is outside SysV's file compiled for \
             x86-64; the call-site guard is not consulting this target's budget"
        ),
        Err(e) => format!("{e:?}"),
    };
    assert!(
        error.contains("Swift") && error.contains("x86_64") && error.contains("2 integer and 2 FP"),
        "the direct-call refusal must come from the ADAPTER and name the convention, the target \
         and that target's own budget — not from the ISel return classifier: {error}"
    );
    assert!(
        !error.contains("integer result register capacity is exhausted"),
        "the direct-call refusal came from ISel, which names no convention. That is the \
         incidental old safety the arch-indexed guard replaced: {error}"
    );

    // The architecture differential at the SAME site: three integer components
    // are inside AAPCS64's combined budget of 4, so the same shape must still
    // be admitted through a direct call on aarch64. Without this half, the
    // guard could ignore `arch` by refusing everywhere.
    let aarch64_module = swift_direct_call_module::<3>("aarch64-apple-darwin");
    Compiler::new_for_target_spec(
        CompilerConfig {
            opt_level: OptLevel::O0,
            ..CompilerConfig::default()
        },
        TargetSpec::parse("aarch64-apple-darwin").expect("aarch64-apple-darwin is a known triple"),
    )
    .with_codegen_license(permit_unlicensed())
    .compile(&aarch64_module)
    .expect(
        "a 3-integer-component Swift return reached through a DIRECT CALL is inside AAPCS64's \
         combined budget of 4 and must stay admitted on aarch64",
    );
}

/// (M10) The same, for the INDIRECT-call guard.
#[test]
fn e3_swift_indirect_call_budget_is_architecture_indexed() {
    let module = swift_indirect_call_module(vec![Ty::I64; 3]);
    let error = refuses_on(&module, Target::X86_64);
    assert!(
        error.contains("CallIndirect"),
        "the refusal must identify the INDIRECT call site, which is the only Swift edge in this \
         module: {error}"
    );
    assert!(
        error.contains("Swift") && error.contains("x86_64") && error.contains("2 integer and 2 FP"),
        "the indirect-call refusal must name the convention, the target and that target's budget: \
         {error}"
    );
    assert!(
        !error.contains("integer result register capacity is exhausted"),
        "the indirect-call refusal came from ISel, not the adapter: {error}"
    );

    // NON-VACUITY at this site, in two directions.
    //  * the same shape on aarch64 is inside the combined budget, and
    //  * a 2-integer return is inside SysV's file and must be admitted on
    //    x86-64, so the guard is not simply refusing every CallIndirect.
    compile_for(&module, Target::Aarch64, OptLevel::O0).expect(
        "a 3-integer Swift return through a CallIndirect is inside AAPCS64's budget and must stay \
         admitted on aarch64",
    );
    let inside = swift_indirect_call_module(vec![Ty::I64; 2]);
    compile_for(&inside, Target::X86_64, OptLevel::O0).expect(
        "a 2-integer Swift return through a CallIndirect is exactly SysV's integer return file \
         and must be admitted on x86-64",
    );
}

/// The x86-64 C register ABI is chosen by the target OS, and only ONE of the
/// two was ever measured against `swiftcc`.
///
/// `guard_carrier_arch_for_target` maps every x86-64 triple onto the single
/// `GuardCarrierArch::X86_64` variant, so the adapter's Swift return budget —
/// System V's — was also consulted for `x86_64-pc-windows-msvc`, whose C ABI is
/// different and whose `swiftcc` placement is measured nowhere in this tree.
/// `Unwitnessed` was applied to riscv64 for exactly that reason and not here.
#[test]
fn e3_swift_fails_closed_on_the_unwitnessed_windows_x64_abi() {
    let windows = TargetSpec::parse("x86_64-pc-windows-msvc").expect("a known triple");
    let darwin = TargetSpec::parse(X86_SUBJECT_TRIPLE).expect("a known triple");
    let compile = |spec: TargetSpec, module: &trust_ir::Module| {
        Compiler::new_for_target_spec(
            CompilerConfig {
                opt_level: OptLevel::O0,
                ..CompilerConfig::default()
            },
            spec,
        )
        .with_codegen_license(permit_unlicensed())
        .compile(module)
        .map(|r| r.object_code)
        .map_err(|e| format!("{e:?}"))
    };

    // Every Swift signature fails closed there, including ones deep INSIDE
    // System V's budget — the budget is not a statement about that ABI at all.
    for returns in [vec![Ty::I64], vec![Ty::I64, Ty::I64], vec![Ty::F64]] {
        let module = swift_module("swift_on_windows", vec![Ty::I64], returns.clone());
        let error = compile(windows, &module).expect_err(
            "a Swift-convention function compiled for x86_64-pc-windows-msvc must fail closed: \
             the x86-64 Swift return budget is System V's, and Win64 swiftcc placement was never \
             measured",
        );
        assert!(
            error.contains("Swift") && error.contains("WindowsX64"),
            "the Windows refusal must name the convention and the ABI whose placement is \
             unwitnessed, not just the ISA: {error}"
        );
        assert!(
            error.contains("no witnessed swiftcc placement")
                || error.contains("NO witnessed swiftcc placement"),
            "the refusal must say that the ABI is UNMEASURED, which is a different reason from \
             a signature being outside a measured budget: {error}"
        );

        // NON-VACUITY: the identical module on the MEASURED x86-64 ABI is
        // admitted, so this is an ABI rule, not "Swift is refused on x86-64".
        compile(darwin, &module).unwrap_or_else(|e| {
            panic!(
                "{returns:?} is inside System V's measured Swift return budget and must stay \
                 admitted on x86_64-apple-darwin: {e}"
            )
        });
    }
}

/// Windows x64 has ONE return register per class, and the refusal is not
/// Swift-specific: a plain `extern "C"` two-component scalar return has no
/// Win64 placement either.
///
/// Before this, `classify_x86_scalar_return_locations` indexed System V's
/// `X86_RET_GPRS` / `X86_RET_XMMS` under BOTH ABIs, so a Win64 compile of a
/// two-`i64` return emitted a second `mov` into RDX that no Win64 caller reads.
/// That was a wrong-code path for EVERY convention, and it was also what made
/// the Swift fail-open above reachable.
#[test]
fn e3_windows_x64_has_no_second_scalar_return_register() {
    let windows = TargetSpec::parse("x86_64-pc-windows-msvc").expect("a known triple");
    let compile = |module: &trust_ir::Module| {
        Compiler::new_for_target_spec(
            CompilerConfig {
                opt_level: OptLevel::O0,
                ..CompilerConfig::default()
            },
            windows,
        )
        .with_codegen_license(permit_unlicensed())
        .compile(module)
        .map(|r| r.object_code)
        .map_err(|e| format!("{e:?}"))
    };

    // NON-VACUITY FIRST: one integer scalar and one FP scalar DO come back in
    // registers under Win64 (RAX and XMM0), so this is a rule about the SECOND
    // component, not a blanket Windows refusal.
    for returns in [vec![Ty::I64], vec![Ty::F64]] {
        compile(&scalar_module_with_conv(
            "win_one",
            CallingConv::C,
            vec![Ty::I64],
            returns.clone(),
        ))
        .unwrap_or_else(|e| panic!("Win64 returns a single {returns:?} scalar in RAX/XMM0: {e}"));
    }

    for (returns, expected) in [
        (vec![Ty::I64, Ty::I64], "no second integer result register"),
        (vec![Ty::F64, Ty::F64], "no second XMM result register"),
    ] {
        let module =
            scalar_module_with_conv("win_two", CallingConv::C, vec![Ty::I64], returns.clone());
        let error = compile(&module).expect_err(
            "Windows x64 returns anything wider than one register through a hidden sret pointer, \
             so a two-component register return must fail closed rather than borrow System V's \
             RDX / XMM1",
        );
        assert!(
            error.contains("WindowsX64") && error.contains(expected),
            "{returns:?}: the Win64 refusal must name the ABI and its own reason: {error}"
        );

        // NON-VACUITY: System V DOES have that second register, so the same
        // module compiles for the Darwin x86-64 triple. Without this the check
        // could pass on any unrelated Windows breakage.
        compile_for(&module, Target::X86_64, OptLevel::O0).unwrap_or_else(|e| {
            panic!("{returns:?} is a real System V placement (RAX,RDX / XMM0,XMM1): {e}")
        });
    }
}

/// `SwiftReturnBudget::Unwitnessed` is witnessed END TO END for riscv64, not
/// only as an assertion on the budget value.
#[test]
fn e3_riscv64_swift_is_unwitnessed_end_to_end() {
    // NON-VACUITY: the same signature under `C` compiles for riscv64, so the
    // refusal below is about the CONVENTION and not about riscv64 rejecting
    // this shape for an unrelated reason.
    let c_module = scalar_module_with_conv("riscv_c", CallingConv::C, vec![Ty::I64], vec![Ty::I64]);
    compile_for(&c_module, Target::Riscv64, OptLevel::O0)
        .expect("a one-integer C return is inside riscv64's supported shape");

    let module = swift_module("riscv_swift", vec![Ty::I64], vec![Ty::I64]);
    let error = refuses_on(&module, Target::Riscv64);
    assert!(
        error.contains("Swift") && error.contains("riscv64"),
        "the riscv64 refusal must name the convention and the target: {error}"
    );
    assert!(
        error.contains("no witnessed swiftcc return placement for this target"),
        "riscv64 must fail closed because nothing was MEASURED there, which is a different \
         statement from a signature exceeding a measured budget: {error}"
    );
}

/// TRIPWIRE. The x86-64 Swift return budget (2 integer, 2 FP) is licensed by
/// the AGREEMENT between two register files: SysV's C return file
/// (`X86_RET_GPRS` = RAX,RDX and `X86_RET_XMMS` = XMM0,XMM1) is a prefix of
/// `swiftcc`'s (RAX,RDX,RCX,R8 and XMM0-XMM3), and both allocate in order from
/// the front. The budget is therefore deliberately NOT derived from
/// `X86_RET_GPRS.len()`: if the C return file is ever widened — which the
/// internal multi-scalar return convention already wants on aarch64, see
/// `tests/multi_result_call_abi.rs` — the Swift budget must NOT silently
/// follow it, because widening C's file does not widen the region where the
/// two files AGREE at the same index.
///
/// This check fires the moment either file moves, forcing the budget to be
/// re-derived by hand instead of drifting.
#[test]
fn e3_tripwire_sysv_return_file_has_not_moved() {
    use trust_cg_ir::x86_64_regs::{RAX, RDX, X86_RET_GPRS, X86_RET_XMMS, XMM0, XMM1};
    assert_eq!(
        X86_RET_GPRS.len(),
        2,
        "the SysV C integer return file changed. The x86-64 Swift return budget in \
         `TrustIrAdapter::swift_return_budget` is 2 because C's file (RAX,RDX) is a same-index \
         prefix of swiftcc's (RAX,RDX,RCX,R8). Re-derive it against swiftcc; do NOT just widen it \
         to match this length."
    );
    assert_eq!(
        X86_RET_XMMS.len(),
        2,
        "the SysV C FP return file changed; same reasoning"
    );
    // `X86PReg` carries no `Debug`, so compare as booleans rather than with
    // `assert_eq!`: the IDENTITY of the two registers matters as much as the
    // count, since the budget's licence is that C's file is a SAME-INDEX
    // prefix of swiftcc's (RAX,RDX,RCX,R8 / XMM0-XMM3).
    assert!(
        X86_RET_GPRS[0] == RAX && X86_RET_GPRS[1] == RDX,
        "the SysV integer return registers are no longer RAX,RDX, so they are no longer the \
         leading two of swiftcc's RAX,RDX,RCX,R8 and the Swift budget must be re-derived"
    );
    assert!(
        X86_RET_XMMS[0] == XMM0 && X86_RET_XMMS[1] == XMM1,
        "the SysV FP return registers are no longer XMM0,XMM1, so they are no longer the \
         leading two of swiftcc's XMM0-XMM3 and the Swift budget must be re-derived"
    );
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes because it was silently refused.
fn permit_unlicensed() -> trust_cg_lower::CodegenLicensePolicy {
    trust_cg_lower::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit)
}
