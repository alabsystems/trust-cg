// guard_kernel_gate_x86_linkrun.rs — compile + link + RUN proof of fail-closed x86 guards.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Runtime and object-code proof that public proof metadata cannot delete hardware guards.
//!
//! `InBounds`, `ProofRef`, and `ProofStatus::Discharged` are report metadata. Until exact validator
//! replay is wired, the production kernel receives empty evidence and bindings. Consequently both
//! legacy `TRUST_CG_GUARD_KERNEL_GATE` settings and the unset default retain the same runtime check:
//!
//!   (A) in-bounds access still computes the correct result; and
//!   (B) out-of-bounds access traps even when public status says Discharged.
//!
//! # Why this is an object-level + cross-arch-RUN oracle, not an x86 RUN
//!
//! The primary intent is a real x86 compile+link+RUN binary (`x86_inbounds_returns_value_and_oob_traps`),
//! gated behind the SAME Rosetta health check the rest of the x86 link/run corpus uses
//! (`has_cc_x86_64_link_run`). On a healthy x86 / Rosetta host it links the emitted Mach-O against a C
//! driver and runs it: in-bounds index returns the correct element, OOB index traps (SIGILL from UD2).
//!
//! On this repository's primary dev host — Apple Silicon (arm64 macOS) — Rosetta cannot execute the
//! emitted x86-64 binary ("bad CPU type in executable"), so that test SKIPs (it prints a SKIP line).
//! To keep the flip GATED by a proof that ALWAYS runs here, this file pairs the (host-gated) x86 RUN
//! with two oracles that run on every host:
//!
//!   1. `x86_object_public_proof_metadata_keeps_hardware_guard` disassembles real emitted x86-64
//!      Mach-O and proves that both environment settings retain `cmpq $8, idx ; jae trap ; ud2` and
//!      the result-computing indexed load. Raw-byte checks keep the floor meaningful without objdump.
//!
//!   2. `aarch64_linkrun_inbounds_returns_value_and_oob_traps` — the cross-arch RUNTIME mirror. The
//!      fail-closed authority policy is arch-neutral, so AArch64 — which runs natively here — proves
//!      that Discharged and Pending fixtures both compute in-bounds values and trap out of bounds.
//!
//! Together these give a runnable-here proof of both (A) and (B); the x86 RUN upgrades (B)+(A) to a
//! literal x86 execution wherever Rosetta/an x86 host is healthy.

use std::fs;
use std::path::Path;
use std::process::Command;

mod common;
use common::disasm::{
    DisasmInsn, disassemble_x86_text, has_bounds_guard,
    has_indexed_load_access as has_split_indexed_load_access, has_objdump, has_ud2,
};
use common::rosetta::{
    codegen_link_timeout, codegen_run_timeout, command_output_with_timeout, has_cc_x86_64_link_run,
    run_executable_with_timeout,
};
use common::x86_interp::{
    Outcome, X86ByteInterp, count_op_classes, decode_all, extract_macho_text,
    normalize_objdump_mnemonic, objdump_mnemonics,
};

use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::env_lock;
use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::target::{Target, TargetSpec};

use trust_ir::proof::{ObligationKind, ProofObligation, ProofStatus};
use trust_ir::value::ProofId;
use trust_ir::{
    Block as TrustIrBlock, BlockId, FuncId, FuncTy, Function as TrustIrFunction, Inst, InstrNode,
    Module, ProofAnnotation, Ty, ValueId,
};

const OBLIGATION_ID: u32 = 7;
const ARRAY_LEN: u64 = 8;
/// The element values the C drivers initialize the array with: `arr[i] = 100 + i`.
const BASE_VALUE: i64 = 100;

// Every test that overrides `TRUST_CG_GUARD_KERNEL_GATE` uses the shared
// thread-local adapter. `cargo test` may run this binary's tests in parallel,
// but sibling tests cannot observe one another's override. The `ScopedEnvVar`
// guards below restore the prior logical value on scope exit, even on panic.

/// Build a trust-ir module with one function `fn <name>(arr: [i64; 8], idx: i64) -> i64 { arr[idx] }`,
/// where the `array[index]` is `InBounds`-annotated (so a `GuardBoundsCheck` carrier is produced) and
/// backed by a single module obligation of the given `status`.
///
/// Both statuses are non-authoritative without exact replay; both retain the runtime bounds check.
fn build_module(name: &str, status: ProofStatus) -> Module {
    let mut module = Module::new("guard_kernel_gate_x86_linkrun");
    let elem_ty = module.add_type(Ty::I64);
    let array_ty = Ty::Array(elem_ty, ARRAY_LEN);
    let ft = module.add_func_type(FuncTy {
        params: vec![array_ty.clone(), Ty::I64],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let mut func = TrustIrFunction::new(FuncId::new(0), name, ft, BlockId::new(0));
    let node = InstrNode::new(Inst::ExtractElement {
        ty: Ty::I64,
        array: ValueId::new(0),
        index: ValueId::new(1),
    })
    .with_result(ValueId::new(2))
    .with_proof(ProofAnnotation::InBounds)
    .with_proof(ProofAnnotation::ProofRef(ProofId::new(OBLIGATION_ID)));
    func.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), array_ty), (ValueId::new(1), Ty::I64)],
        body: vec![
            node,
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(2)],
            }),
        ],
    }];
    module.proof_obligations.push(ProofObligation::new(
        ProofId::new(OBLIGATION_ID),
        ObligationKind::MemorySafety,
        status,
        "array index is in bounds",
    ));
    module.add_function(func);
    module
}

fn compile_x86_object(module: &Module) -> Vec<u8> {
    let spec = TargetSpec::parse("x86_64-apple-darwin").expect("parse x86_64-apple-darwin");
    let compiler = Compiler::new_for_target_spec(
        CompilerConfig {
            opt_level: OptLevel::O2,
            target: Target::X86_64,
            ..CompilerConfig::default()
        },
        spec,
    );
    compiler.compile(module).expect("x86 compile").object_code
}

fn compile_aarch64_object(module: &Module) -> Vec<u8> {
    let compiler = Compiler::new(CompilerConfig {
        opt_level: OptLevel::O2,
        target: Target::Aarch64,
        ..CompilerConfig::default()
    });
    compiler
        .compile(module)
        .expect("aarch64 compile")
        .object_code
}

/// Count `UD2` (`0F 0B`) occurrences in raw object bytes. A surviving x86 bounds-check carrier expands
/// to a `UD2` trap block, so its presence is the observable for "guard kept". These tiny functions
/// emit no other `UD2`, so this is a faithful proxy.
fn ud2_count(bytes: &[u8]) -> usize {
    bytes.windows(2).filter(|w| w == b"\x0F\x0B").count()
}

/// True on AArch64 macOS hosts where native `cc` can link+run the emitted Mach-O object.
fn can_link_and_run_aarch64() -> bool {
    cfg!(all(target_os = "macos", target_arch = "aarch64"))
}

// ===========================================================================
// (1) ALWAYS-ON x86 OBJECT-LEVEL ORACLE — public metadata keeps hardware traps.
//
// Runs on every host (no execution required). DISASSEMBLES the REAL emitted
// x86-64 machine code with an independent decoder (LLVM `objdump`) and proves
// that both legacy environment values and both public statuses retain the
// complete bounds-check guard and the indexed-load access.
// The same facts are pinned on the raw bytes too, so coverage survives even if
// `objdump` is missing.
// ===========================================================================

/// Disassemble an emitted x86 object, asserting the decode succeeded when
/// `objdump` is present. Returns `None` only when `objdump` is unavailable (the
/// raw-byte floor then carries the proof).
fn disasm_or_none(label: &str, obj: &[u8]) -> Option<Vec<DisasmInsn>> {
    if !has_objdump() {
        return None;
    }
    Some(
        disassemble_x86_text(obj)
            .unwrap_or_else(|| panic!("objdump failed to disassemble emitted x86 object: {label}")),
    )
}

/// Accept both codegen shapes for `arr[idx]`: a scaled LEA followed by a plain load, or the more
/// efficient direct SIB-addressed load currently selected at O2.
fn has_indexed_load_access(insns: &[DisasmInsn]) -> bool {
    has_split_indexed_load_access(insns)
        || insns.iter().any(|i| {
            let Some((source, _destination)) = i.operands.split_once("),") else {
                return false;
            };
            i.mnemonic.starts_with("mov") && source.contains('(') && source.contains(",8")
        })
}

#[test]
fn x86_object_public_proof_metadata_keeps_hardware_guard() {
    let env_scope = env_lock::override_scope();
    let objdump = has_objdump();

    // Public Discharged status is deliberately non-authoritative.
    let discharged = build_module("x86_proven", ProofStatus::Discharged);

    // Legacy value 0 retains the runtime guard.
    let off = {
        let _g = env_lock::ScopedEnvVar::set(&env_scope, "TRUST_CG_GUARD_KERNEL_GATE", "0");
        compile_x86_object(&discharged)
    };
    let off_ud2 = ud2_count(&off);
    assert!(
        off_ud2 >= 1,
        "legacy value 0 retains the UD2 bounds-check trap"
    );

    // Unset/default policy also retains it because production replay authority is empty.
    let on_default = {
        let _g = env_lock::ScopedEnvVar::unset(&env_scope, "TRUST_CG_GUARD_KERNEL_GATE");
        compile_x86_object(&discharged)
    };
    let on_default_ud2 = ud2_count(&on_default);
    assert!(
        on_default_ud2 >= 1,
        "unset/default policy retains the UD2 trap"
    );
    assert_eq!(
        on_default_ud2, off_ud2,
        "environment cannot change guard retention"
    );
    assert_eq!(
        on_default, off,
        "environment cannot change emitted object authority policy"
    );

    // ---- AIRTIGHT DISASSEMBLY ORACLE (primary; runs wherever objdump is present) ----
    // Reason over decoded instructions, not fixed byte windows, so the proof is robust to whichever
    // registers regalloc chose. We assert, on the REAL decoded stream:
    // Both streams must contain the complete guard and result-computing access.
    if objdump {
        let off_d = disasm_or_none("off/discharged", &off).expect("objdump present");
        let on_d = disasm_or_none("on/discharged", &on_default).expect("objdump present");

        assert!(
            has_bounds_guard(&off_d, ARRAY_LEN),
            "gate OFF: decoded stream must contain the full bounds-check guard \
             `cmpq $0x{ARRAY_LEN:x}, idx ; jae <trap> ; <trap>: ud2`"
        );
        assert!(
            has_indexed_load_access(&off_d),
            "gate OFF: decoded stream must contain the result-computing indexed load \
             (scaled address + dereference); decoded stream: {off_d:#?}"
        );

        assert!(
            has_ud2(&on_d) && has_bounds_guard(&on_d, ARRAY_LEN),
            "unset/default: decoded stream retains the complete bounds-check trap"
        );
        assert!(
            has_indexed_load_access(&on_d),
            "unset/default: indexed load remains present behind the hardware guard"
        );
    }

    // ---- RAW-BYTE FLOOR (always runs; keeps the proof meaningful without objdump) ----
    // Pins the same facts on the emitted bytes for these specific tiny functions.
    let contains = |b: &[u8], pat: &[u8]| b.windows(pat.len()).any(|w| w == pat);
    // `movq (%rax),%rcx; movq %rcx,%rax` — the load that materializes arr[idx] into the return reg.
    let deref_and_return = b"\x48\x8b\x08\x48\x89\xc8";
    // `leaq (base,idx,8),%rax` SIB-scaled address — base register byte (d8|d9|da..) differs by
    // regalloc, so match the 3-byte opcode + ModRM/SIB prefix `48 8d 04`.
    let scaled_lea = b"\x48\x8d\x04";
    // Current O2 directly emits `movq (%rdx,%rdi,8),%rcx`; retain compatibility with the older
    // scaled-LEA + plain-load shape so the oracle tracks semantics rather than a single optimization.
    let direct_indexed_load = b"\x48\x8b\x0c\xfa";
    let has_direct_scaled_load = |b: &[u8]| {
        b.windows(4).any(|w| {
            let rex_w = w[0] & 0xf8 == 0x48;
            let mov_load = w[1] == 0x8b;
            let modrm = w[2];
            let memory_sib = modrm >> 6 != 0b11 && modrm & 0b111 == 0b100;
            let sib = w[3];
            let scale_8 = sib >> 6 == 0b11;
            let has_index = (sib >> 3) & 0b111 != 0b100;
            rex_w && mov_load && memory_sib && scale_8 && has_index
        })
    };
    let has_access = |b: &[u8]| {
        contains(b, direct_indexed_load)
            || has_direct_scaled_load(b)
            || (contains(b, scaled_lea) && contains(b, deref_and_return))
    };
    assert!(
        has_access(&off) && has_access(&on_default),
        "the result-computing indexed load survives in both guarded objects"
    );
    // The guard's CMP + UD2 are present under both environment states.
    let has_guard_cmp = |b: &[u8]| {
        // `48 83 /7 ib`: cmpq $8, r64. Accept whichever argument register regalloc selects.
        b.windows(4).any(|w| {
            w[0] == 0x48 && w[1] == 0x83 && (w[2] & 0xf8) == 0xf8 && w[3] == ARRAY_LEN as u8
        })
    };
    assert!(
        has_guard_cmp(&off),
        "legacy value 0 keeps the bounds-check compare"
    );
    assert!(
        has_guard_cmp(&on_default) && contains(&on_default, b"\x0f\x0b"),
        "unset/default retains the bounds-check compare and UD2 trap"
    );

    // Pending status follows the same fail-closed policy.
    let pending = build_module("x86_unproven", ProofStatus::Pending);
    let on_pending = {
        let _g = env_lock::ScopedEnvVar::unset(&env_scope, "TRUST_CG_GUARD_KERNEL_GATE");
        compile_x86_object(&pending)
    };
    assert!(
        ud2_count(&on_pending) >= 1,
        "Pending bounds-check carrier is kept and expands to a UD2 trap"
    );
    // Airtight: the KEPT pending carrier must decode to the COMPLETE guard AND still preserve the
    // access — i.e. it is byte-for-instruction the same guarded shape as the legacy (gate-off) path,
    // so an out-of-bounds index genuinely traps and an in-bounds index still computes arr[idx].
    if objdump {
        let on_p = disasm_or_none("on/pending", &on_pending).expect("objdump present");
        assert!(
            has_bounds_guard(&on_p, ARRAY_LEN),
            "default-on + UNPROVEN: decoded stream KEEPS the full guard \
             `cmpq $0x{ARRAY_LEN:x}, idx ; jae <trap> ; <trap>: ud2` (fail-closed — OOB traps)"
        );
        assert!(
            has_indexed_load_access(&on_p),
            "default-on + UNPROVEN: the indexed load is still present (in-bounds returns arr[idx])"
        );
    }

    // No manual cleanup needed: the block-scoped `ScopedEnvVar` guards above each
    // restored the flag's prior (unset) state, and `_env` releases the lock on
    // return.
}

// ===========================================================================
// (2) PRIMARY x86 COMPILE + LINK + RUN (host-gated on a healthy x86 / Rosetta host).
//
// On an x86-64 host (or a healthy Rosetta 2 aarch64 host with
// TRUST_CG_RUN_ROSETTA_LINKRUN=1) this links the emitted x86-64 Mach-O against a
// C driver and RUNS it:
//   * Discharged and Pending statuses both return the correct in-bounds element;
//   * both trap out of bounds because neither public status is replay authority.
//
// On the arm64 dev host Rosetta cannot run x86-64 binaries, so this SKIPs.
// ===========================================================================

#[test]
fn x86_inbounds_returns_value_and_oob_traps() {
    if !has_cc_x86_64_link_run() {
        eprintln!(
            "SKIP: x86 compile+link+RUN proof — no healthy x86-64 / Rosetta host (this arm64 macOS \
             host cannot execute x86-64 binaries: 'bad CPU type'). The always-on x86 OBJECT proof \
             `x86_object_public_proof_metadata_keeps_hardware_guard` and the AArch64 link+RUN \
             mirror `aarch64_linkrun_inbounds_returns_value_and_oob_traps` cover correctness here."
        );
        return;
    }

    // Unset/default selects the unconditional fail-closed production policy.
    // The thread-local gate stays logically absent for the whole body and is
    // restored on scope exit.
    let env_scope = env_lock::override_scope();
    let _gate_guard = env_lock::ScopedEnvVar::unset(&env_scope, "TRUST_CG_GUARD_KERNEL_GATE");

    // (A) Public Discharged status keeps the bounds check and computes in-bounds values correctly.
    let proven = build_module("x86rt_proven", ProofStatus::Discharged);
    let proven_obj = compile_x86_object(&proven);
    // ABI: the emitted Trust function takes the `[i64;8]` array BY VALUE. Per the
    // System V x86-64 ABI a 64-byte aggregate is MEMORY class, so the array is
    // passed on the stack (the emitted prologue reads it from 0x10(%rbp)) and `idx`
    // arrives in %rdi. The C driver must therefore pass a by-value STRUCT wrapping
    // the array (a 64-byte struct is MEMORY class -> stack), NOT a `long *` pointer
    // (which would put a pointer in %rdi and mismatch the callee, failing loudly on
    // a Rosetta/x86 host). NOTE: this test SKIPs on the arm64/no-Rosetta dev host,
    // so this driver is compile-correct + ABI-correct by analysis but its runtime
    // is confirmed only on a Rosetta/x86 host; the host-independent `x86_interp_*`
    // tests below are the faithful literal-execution oracle here. (The AArch64
    // `aa_*` drivers below correctly keep `long *arr`: AAPCS64 passes a >16-byte
    // aggregate by REFERENCE, and those tests run + pass natively on this host.)
    let driver = r#"
#include <stdio.h>
#include <stdlib.h>
typedef struct { long a[8]; } arr8_t;
extern long x86rt_proven(arr8_t arr, long idx);
int main(int argc, char **argv) {
    arr8_t arr = {{100,101,102,103,104,105,106,107}};
    long idx = atol(argv[1]);
    printf("%ld\n", x86rt_proven(arr, idx));
    return 0;
}
"#;
    for idx in [0i64, 3, 7] {
        let (code, out) = link_and_run_x86("x86rt_proven", &proven_obj, driver, &idx.to_string());
        assert_eq!(
            code, 0,
            "proven in-bounds access idx={idx} must run cleanly (got exit {code}, stdout {out:?})"
        );
        assert_eq!(
            out.trim().parse::<i64>().ok(),
            Some(BASE_VALUE + idx),
            "Discharged-status in-bounds access idx={idx} must return arr[idx] = {}",
            BASE_VALUE + idx
        );
    }
    let (proven_oob, _) = link_and_run_x86("x86rt_proven", &proven_obj, driver, "100");
    assert!(
        proven_oob >= 128,
        "public Discharged status must not suppress the OOB hardware trap; got exit {proven_oob}"
    );

    // (B) Pending follows the same runtime-safe behavior.
    let unproven = build_module("x86rt_unproven", ProofStatus::Pending);
    let unproven_obj = compile_x86_object(&unproven);
    let driver2 = r#"
#include <stdio.h>
#include <stdlib.h>
typedef struct { long a[8]; } arr8_t;
extern long x86rt_unproven(arr8_t arr, long idx);
int main(int argc, char **argv) {
    arr8_t arr = {{100,101,102,103,104,105,106,107}};
    long idx = atol(argv[1]);
    printf("%ld\n", x86rt_unproven(arr, idx));
    return 0;
}
"#;
    // in-bounds still correct
    let (code, out) = link_and_run_x86("x86rt_unproven", &unproven_obj, driver2, "5");
    assert_eq!(
        code, 0,
        "unproven in-bounds idx=5 must run cleanly (exit {code})"
    );
    assert_eq!(out.trim().parse::<i64>().ok(), Some(BASE_VALUE + 5));
    // out-of-bounds must TRAP (killed by signal => non-zero, >= 128)
    let (code_oob, _out_oob) = link_and_run_x86("x86rt_unproven", &unproven_obj, driver2, "100");
    assert!(
        code_oob != 0 && code_oob >= 128,
        "unproven OUT-OF-BOUNDS access must TRAP (signal-killed), got exit {code_oob}"
    );
}

// ===========================================================================
// (3) CROSS-ARCH RUNTIME MIRROR — AArch64 link + RUN (runs natively on this host).
//
// The fail-closed policy is arch-neutral. AArch64 runs natively here, so it
// proves both public statuses retain a runtime guard while preserving in-bounds
// computation.
// ===========================================================================

#[test]
fn aarch64_linkrun_inbounds_returns_value_and_oob_traps() {
    if !can_link_and_run_aarch64() {
        eprintln!("SKIP: AArch64 link+run mirror requires an aarch64 macOS host");
        return;
    }

    // Unset/default fail-closed policy under test. The thread-local gate stays
    // logically absent for the whole body and is restored on scope exit.
    let env_scope = env_lock::override_scope();
    let _gate_guard = env_lock::ScopedEnvVar::unset(&env_scope, "TRUST_CG_GUARD_KERNEL_GATE");

    // (A) Public Discharged status retains the check.
    let proven = build_module("aa_proven", ProofStatus::Discharged);
    let proven_obj = compile_aarch64_object(&proven);
    assert!(
        ud2_count_brk(&proven_obj) >= 1,
        "AArch64 public Discharged status must retain the bounds-check BRK"
    );
    let driver = r#"
#include <stdio.h>
#include <stdlib.h>
extern long aa_proven(long *arr, long idx);
int main(int argc, char **argv) {
    long arr[8] = {100,101,102,103,104,105,106,107};
    printf("%ld\n", aa_proven(arr, atol(argv[1])));
    return 0;
}
"#;
    for idx in [0i64, 4, 7] {
        let (code, out) = link_and_run_aarch64("aa_proven", &proven_obj, driver, &idx.to_string());
        assert_eq!(
            code, 0,
            "AArch64 proven in-bounds idx={idx} must run cleanly (exit {code}, stdout {out:?})"
        );
        assert_eq!(
            out.trim().parse::<i64>().ok(),
            Some(BASE_VALUE + idx),
            "AArch64 Discharged-status in-bounds idx={idx} returns arr[idx] = {}",
            BASE_VALUE + idx
        );
    }
    let (proven_oob, _) = link_and_run_aarch64("aa_proven", &proven_obj, driver, "100");
    assert!(
        proven_oob >= 128,
        "AArch64 public Discharged status must not suppress the OOB trap; got exit {proven_oob}"
    );

    // (B) Pending (unproven): the kernel keeps the check; in-bounds returns the right value at
    //     runtime, out-of-bounds TRAPS.
    let unproven = build_module("aa_unproven", ProofStatus::Pending);
    let unproven_obj = compile_aarch64_object(&unproven);
    let driver2 = r#"
#include <stdio.h>
#include <stdlib.h>
extern long aa_unproven(long *arr, long idx);
int main(int argc, char **argv) {
    long arr[8] = {100,101,102,103,104,105,106,107};
    printf("%ld\n", aa_unproven(arr, atol(argv[1])));
    return 0;
}
"#;
    let (code, out) = link_and_run_aarch64("aa_unproven", &unproven_obj, driver2, "6");
    assert_eq!(
        code, 0,
        "AArch64 unproven in-bounds idx=6 must run cleanly (exit {code})"
    );
    assert_eq!(
        out.trim().parse::<i64>().ok(),
        Some(BASE_VALUE + 6),
        "AArch64 unproven in-bounds returns the correct element"
    );
    let (code_oob, _) = link_and_run_aarch64("aa_unproven", &unproven_obj, driver2, "100");
    assert!(
        code_oob != 0 && code_oob >= 128,
        "AArch64 unproven OUT-OF-BOUNDS access must TRAP (signal-killed), got exit {code_oob}"
    );
}

// ===========================================================================
// (4) HOST-INDEPENDENT LITERAL x86 EXECUTION — in-process x86-64 interpreter.
//
// This runs on EVERY host (no skip, no Rosetta, no link). It DECODES + EXECUTES
// the emitted x86-64 `__text` bytes in-process — exactly like the RISC-V backend
// does with `RiscVByteInterp` — proving on this arm64 host that:
//   (A) legacy value 0 / Discharged: in-bounds returns arr[idx], OOB traps;
//   (B) unset/default / Discharged: identical fail-closed behavior;
//   (C) unset/default / Pending: identical fail-closed behavior.
//
// The interpreter is fail-closed: any opcode/ModRM/SIB byte it does not recognize
// returns a typed error (never a silent NOP), and UD2 is a DISTINCT Trapped
// outcome (never normal completion). It is cross-checked against the objdump
// oracle on the SAME bytes so a decoder bug is caught.
//
// ABI note: `[i64;8]` is 64 bytes (> 16) => System V MEMORY class => the array is
// passed BY VALUE on the stack (read by the prologue from `0x10(%rbp)`), and only
// `idx` arrives in `%rdi`. The interpreter sets up the call frame accordingly.
// ===========================================================================

/// The 8 array elements the proof uses: `arr[i] = BASE_VALUE + i`, matching the
/// C drivers (`{100,101,..,107}`).
fn proof_array() -> [i64; 8] {
    let mut a = [0i64; 8];
    for (i, slot) in a.iter_mut().enumerate() {
        *slot = BASE_VALUE + i as i64;
    }
    a
}

/// Compile the module default-ON or gate-OFF, extract the `__text` bytes, and run
/// the in-process interpreter with `idx`. Returns the interpreter outcome.
fn interp_run(module: &Module, idx: i64) -> Outcome {
    let obj = compile_x86_object(module);
    let text = extract_macho_text(&obj);
    let mut interp = X86ByteInterp::new(text);
    interp.setup_call(&proof_array(), idx);
    interp
        .run(0)
        .unwrap_or_else(|e| panic!("x86 interpreter decode/exec error (idx={idx}): {e:?}"))
}

/// Cross-check: decode the WHOLE `__text` with our in-house decoder and assert it
/// agrees, instruction-for-instruction (offset + operation class), with objdump's
/// independent decode of the same bytes. Catches any decoder length/opcode bug.
fn cross_check_against_objdump(label: &str, obj: &[u8]) {
    let Some(objdump_stream) = objdump_mnemonics(obj) else {
        // objdump unavailable: the raw-byte floor + the in-house decode itself
        // still carry coverage; nothing to cross-check against.
        return;
    };
    let text = extract_macho_text(obj);
    let ours =
        decode_all(&text).unwrap_or_else(|e| panic!("in-house decode failed for {label}: {e:?}"));

    let objdump_norm: Vec<(u64, String)> = objdump_stream
        .iter()
        .map(|(off, m)| (*off, normalize_objdump_mnemonic(m)))
        .collect();

    assert_eq!(
        ours.len(),
        objdump_norm.len(),
        "{label}: in-house decoder saw {} instructions but objdump saw {} \
         (a decoder length/opcode bug would desync the count)\nours={ours:?}\nobjdump={objdump_norm:?}",
        ours.len(),
        objdump_norm.len()
    );
    for (a, b) in ours.iter().zip(objdump_norm.iter()) {
        assert_eq!(
            a.0, b.0,
            "{label}: instruction boundary mismatch — in-house offset {:#x} ({}) vs objdump \
             offset {:#x} ({}); a wrong decoded length would shift every following offset",
            a.0, a.1, b.0, b.1
        );
        assert_eq!(
            a.1, b.1,
            "{label}: mnemonic mismatch at offset {:#x}: in-house {} vs objdump {}",
            a.0, a.1, b.1
        );
    }
}

#[test]
fn x86_interp_inbounds_returns_value_and_oob_traps() {
    let env_scope = env_lock::override_scope();
    let array = proof_array();

    // ---------------------------------------------------------------------
    // (A) legacy value 0 / Discharged: production KEEPS the guard. In-bounds
    //     returns arr[idx]; OOB reaches the kept UD2 => Trapped.
    // ---------------------------------------------------------------------
    let gate_var = env_lock::ScopedEnvVar::set(&env_scope, "TRUST_CG_GUARD_KERNEL_GATE", "0");
    let off_mod = build_module("interp_off", ProofStatus::Discharged);
    // Cross-check the decoder against objdump on the SAME emitted bytes.
    cross_check_against_objdump("gate-off/discharged", &compile_x86_object(&off_mod));
    for idx in [0i64, 3, 7] {
        assert_eq!(
            interp_run(&off_mod, idx),
            Outcome::Returned((BASE_VALUE + idx) as u64),
            "gate-OFF in-bounds idx={idx}: literal x86 execution must return arr[idx]={}",
            BASE_VALUE + idx
        );
    }
    // OOB index: the kept `cmp $8 ; jae ud2` must TRAP (distinct outcome).
    assert_eq!(
        interp_run(&off_mod, 100),
        Outcome::Trapped,
        "gate-OFF out-of-bounds idx=100: the kept guard's UD2 must be reached (TRAPPED)"
    );
    // A negative index also reads as a huge u64 => CF=0 => jae taken => TRAP.
    assert_eq!(
        interp_run(&off_mod, -1),
        Outcome::Trapped,
        "gate-OFF negative idx=-1 (huge unsigned): the kept guard must TRAP"
    );

    // ---------------------------------------------------------------------
    // (B) unset/default / Discharged: public status remains non-authoritative.
    // ---------------------------------------------------------------------
    // End the value-0 scope (restores the flag's prior/unset state) and hold an
    // unset guard for the rest of the body.
    drop(gate_var);
    let _gate_var = env_lock::ScopedEnvVar::unset(&env_scope, "TRUST_CG_GUARD_KERNEL_GATE");
    let on_mod = build_module("interp_on", ProofStatus::Discharged);
    cross_check_against_objdump("default-on/discharged", &compile_x86_object(&on_mod));
    for idx in [0i64, 3, 7] {
        assert_eq!(
            interp_run(&on_mod, idx),
            Outcome::Returned((BASE_VALUE + idx) as u64),
            "unset/default Discharged in-bounds idx={idx}: access returns arr[idx]={}",
            BASE_VALUE + idx
        );
    }
    assert_eq!(
        interp_run(&on_mod, 8),
        Outcome::Trapped,
        "public Discharged status must not suppress the idx=8 hardware trap"
    );

    // ---------------------------------------------------------------------
    // (C) default-ON / pending (undischarged): the kernel KEEPS the guard
    //     (fail-closed). In-bounds returns arr[idx]; OOB => Trapped.
    // ---------------------------------------------------------------------
    let pending_mod = build_module("interp_pending", ProofStatus::Pending);
    cross_check_against_objdump("default-on/pending", &compile_x86_object(&pending_mod));
    for idx in [0i64, 5, 7] {
        assert_eq!(
            interp_run(&pending_mod, idx),
            Outcome::Returned((BASE_VALUE + idx) as u64),
            "default-ON pending in-bounds idx={idx}: kept guard passes, returns arr[idx]={}",
            BASE_VALUE + idx
        );
    }
    assert_eq!(
        interp_run(&pending_mod, 100),
        Outcome::Trapped,
        "default-ON pending out-of-bounds idx=100: the kept UD2 must TRAP (fail-closed)"
    );

    let _ = array; // silence unused if asserts ever change

    // No manual cleanup needed: `_gate_var` restores the flag's prior (unset)
    // state and `_env` releases the lock on return.
}

#[test]
fn x86_interp_negative_controls_cannot_false_pass() {
    // The interpreter must be able to FAIL — these controls prove it is genuinely
    // decoding and executing, not rubber-stamping a PASS.
    let env_scope = env_lock::override_scope();
    let _gate_var = env_lock::ScopedEnvVar::unset(&env_scope, "TRUST_CG_GUARD_KERNEL_GATE");
    let on_mod = build_module("interp_neg", ProofStatus::Discharged);

    // (1) The load-address math is genuinely exercised: different in-bounds
    //     indices must return DIFFERENT correct elements (not a fixed value).
    let r0 = interp_run(&on_mod, 0);
    let r5 = interp_run(&on_mod, 5);
    assert_eq!(r0, Outcome::Returned(BASE_VALUE as u64));
    assert_eq!(r5, Outcome::Returned((BASE_VALUE + 5) as u64));
    assert_ne!(
        r0, r5,
        "different in-bounds indices must yield different elements — proves the SIB \
         scaled-index address `lea (base,idx,8)` + load is actually computed, not faked"
    );

    // (2) An unknown opcode fed to the interpreter must be REJECTED (fail-closed),
    //     never silently NOP'd into a false PASS. 0x06 (PUSH ES, invalid in long
    //     mode) is outside the supported subset.
    let bogus = vec![0x06u8, 0xC3];
    let mut interp = X86ByteInterp::new(bogus);
    interp.setup_call(&proof_array(), 0);
    let err = interp.run(0);
    assert!(
        err.is_err(),
        "an unknown opcode (0x06) must be rejected with a typed error, never skipped/NOP'd \
         into a false PASS; got {err:?}"
    );

    // (3) A REX with an extension bit set (would select r8-r15, which the corpus
    //     never emits) must also fail closed rather than mis-decode a register.
    //     0x49 = REX.W|REX.B, then 0x89 mov, then a ModRM — rejected at the REX.
    let rex_ext = vec![0x49u8, 0x89, 0xC0, 0xC3];
    let mut interp2 = X86ByteInterp::new(rex_ext);
    interp2.setup_call(&proof_array(), 0);
    assert!(
        interp2.run(0).is_err(),
        "a REX with REX.B set must fail closed (it would reference r8-r15)"
    );

    // (4) Sanity on the cross-check itself: our linear decode of the real text
    //     must match objdump's instruction count exactly (catches length bugs).
    let obj = compile_x86_object(&on_mod);
    if let Some(objdump_stream) = objdump_mnemonics(&obj) {
        let text = extract_macho_text(&obj);
        let ours = decode_all(&text).expect("in-house decode of real text");
        assert_eq!(
            ours.len(),
            objdump_stream.len(),
            "in-house decoder and objdump must agree on instruction count"
        );
        // The op-class histogram must also match (e.g. exactly one ret, the
        // expected number of movs/leas), proving structural agreement.
        let ours_hist = count_op_classes(&ours);
        let obj_hist = count_op_classes(
            &objdump_stream
                .iter()
                .map(|(o, m)| (*o, normalize_objdump_mnemonic(m)))
                .collect::<Vec<_>>(),
        );
        assert_eq!(
            ours_hist, obj_hist,
            "in-house op-class histogram must match objdump's"
        );
    }
}

// ===========================================================================
// Link + run helpers
// ===========================================================================

fn make_dir(test_name: &str) -> std::path::PathBuf {
    let dir = std::env::temp_dir().join(format!("trust_cg_guard_linkrun_{test_name}"));
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).expect("create test dir");
    dir
}

/// Link an x86-64 object + C driver with `cc -arch x86_64`, run with `arg`, return (exit_code, stdout).
fn link_and_run_x86(test_name: &str, obj: &[u8], driver_src: &str, arg: &str) -> (i32, String) {
    let dir = make_dir(&format!("x86_{test_name}"));
    let obj_path = dir.join("g.o");
    fs::write(&obj_path, obj).expect("write obj");
    let driver_path = dir.join("driver.c");
    fs::write(&driver_path, driver_src).expect("write driver");
    let binary = dir.join("g");

    let mut link = Command::new("cc");
    link.args(if cfg!(target_os = "macos") {
        &["-arch", "x86_64"][..]
    } else {
        &[][..]
    })
    .args([
        "-o",
        binary.to_str().unwrap(),
        driver_path.to_str().unwrap(),
        obj_path.to_str().unwrap(),
    ]);
    let link_res = command_output_with_timeout(&mut link, codegen_link_timeout()).expect("cc x86");
    assert!(
        !link_res.timed_out && link_res.output.status.success(),
        "x86 link failed for {test_name}: {}",
        String::from_utf8_lossy(&link_res.output.stderr)
    );

    let res = run_with_arg(&binary, arg);
    let _ = fs::remove_dir_all(&dir);
    res
}

/// Link an AArch64 object + C driver with native `cc`, run with `arg`, return (exit_code, stdout).
fn link_and_run_aarch64(test_name: &str, obj: &[u8], driver_src: &str, arg: &str) -> (i32, String) {
    let dir = make_dir(&format!("aa_{test_name}"));
    let obj_path = dir.join("g.o");
    fs::write(&obj_path, obj).expect("write obj");
    let driver_path = dir.join("driver.c");
    fs::write(&driver_path, driver_src).expect("write driver");
    let binary = dir.join("g");

    let mut link = Command::new("cc");
    link.args([
        "-o",
        binary.to_str().unwrap(),
        driver_path.to_str().unwrap(),
        obj_path.to_str().unwrap(),
    ]);
    let link_res = command_output_with_timeout(&mut link, codegen_link_timeout()).expect("cc aa64");
    assert!(
        !link_res.timed_out && link_res.output.status.success(),
        "aarch64 link failed for {test_name}: {}",
        String::from_utf8_lossy(&link_res.output.stderr)
    );

    let res = run_with_arg(&binary, arg);
    let _ = fs::remove_dir_all(&dir);
    res
}

/// Run `binary arg` under the shared timeout-guarded runner. The runner reports the shell `$?`, so a
/// signal-killed process (a guard trap) shows up as exit code `128 + signum` (>= 128). Returns
/// (exit_code, stdout).
fn run_with_arg(binary: &Path, arg: &str) -> (i32, String) {
    // `run_executable_with_timeout` runs the program with no args; pass the arg via a tiny wrapper
    // script so the timeout/process-group machinery (and signal-aware `$?`) is reused verbatim.
    let wrapper = binary.with_extension("sh");
    fs::write(
        &wrapper,
        format!("#!/bin/sh\nexec '{}' '{}'\n", binary.display(), arg),
    )
    .expect("write wrapper");
    let mut perms = fs::metadata(&wrapper).expect("stat wrapper").permissions();
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        perms.set_mode(0o755);
    }
    fs::set_permissions(&wrapper, perms).expect("chmod wrapper");

    let result = run_executable_with_timeout(&wrapper, codegen_run_timeout()).expect("run binary");
    if result.timed_out {
        panic!(
            "running {} {arg} timed out after {:?}",
            binary.display(),
            codegen_run_timeout()
        );
    }
    let stdout = String::from_utf8_lossy(&result.output.stdout).to_string();
    (result.output.status.code().unwrap_or(-1), stdout)
}

/// Count AArch64 `BRK #imm` (`0xD4200000` masked) — the AArch64 trap a surviving bounds-check carrier
/// expands to. Used only as the AArch64 analogue of `ud2_count`.
fn ud2_count_brk(bytes: &[u8]) -> usize {
    bytes
        .chunks_exact(4)
        .filter(|w| {
            let word = u32::from_le_bytes([w[0], w[1], w[2], w[3]]);
            // BRK #imm16: 1101 0100 001 imm16 000 00  => top byte 0xD4, bits[23:21]=001, low5=0.
            (word & 0xFFE0_001F) == 0xD420_0000
        })
        .count()
}
