// trust-cg-codegen/tests/aarch64_shrink_wrap_region_exit.rs
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Pinned regression: Darwin shrink-wrapping admitted a save block whose frame
//! region is LEFT through an edge that is neither a return nor an edge
//! epilogue, so one path ran the sunk prologue and then returned through a
//! bare `ret`.
//!
//! The shape is `char::is_whitespace` (`' ' | '\t'..='\r' => true,
//! '\0'..='\u{84}' => false, _ => White_Space(c)`), measured on 2026-09-28 as
//! the last `library/core` G4 root, and `core::ptr::align_offset` showed the
//! same defect with X19/X20 saved. The shared `true` arm is reached from the entry guard (frameless)
//! AND from the second guard, which is inside the frame region the sunk
//! prologue opens. Every block outside the region was frame-clean and every
//! frame-side predecessor of the return carried an epilogue, so the old
//! admission accepted it; `c in '\t'..='\r'` then returned with SP 16 bytes
//! low and X29 pointing into the dead frame. The final-stream frame net
//! refused it as `[TCG-A64-SPILL-SLOT] callee-saved-not-restored` (X29 at the
//! `ret`), which is correct: the fix is in the admission, not the net.
//!
//! Two controls, both of which fail on the old admission:
//! * the prepared Darwin stream at O0-O3 is modeled by the frame net and has
//!   no violation (the old stream failed the pipeline's own enforced net);
//! * natively, compiled with the net forced OFF so the old code would reach
//!   the machine, every path preserves SP, X29 and X19-X28 across the call and
//!   returns the right value (the old code moved SP and X29 on the
//!   `'\t'..='\r'` path).
//!
//! The fix this guards is `frame.rs`'s `shrink_wrap_regions`: returns are
//! classified by the frame and leaf regions, not by dominance at their
//! predecessors, and a frame-only edge into a block a leaf path also reaches
//! must be cut by an edge epilogue or the candidate is declined. With that
//! change reverted, both tests here fail at O0: `prepare` is refused with
//! `[TCG-A64-SPILL-SLOT] ... callee-saved-not-restored ... x29`, and the
//! native run reports `REGION_EXIT_FRAME_BROKEN c=0x9 mask=0x3` (SP and X29).
//!
//! Run: `targo --unverified test --release -p trust-cg-codegen --test
//! aarch64_shrink_wrap_region_exit`. The native test needs an AArch64 macOS or
//! Linux GNU host and prints `SKIP:` and returns elsewhere.

#[path = "common/aarch64_native.rs"]
mod native;

use trust_cg_codegen::pipeline::{OptLevel, Pipeline, PipelineConfig};
use trust_cg_verify::post_ra_spill_slots::{FrameNetOutcome, analyze_frame};
use trust_ir::{ICmpOp, Module, Ty};
use trust_ir_build::ModuleBuilder;

const OPT_LEVELS: [OptLevel; 4] = [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3];

const DARWIN: &str = "aarch64-apple-darwin";

/// The triple `native::compile` lowers for. It asserts that a fixture's
/// pinned `target_info` matches the one it would set, so a drift here fails
/// loudly rather than testing a different ABI.
fn native_triple() -> &'static str {
    if cfg!(all(
        target_arch = "aarch64",
        target_os = "linux",
        target_env = "gnu"
    )) {
        "aarch64-unknown-linux-gnu"
    } else {
        DARWIN
    }
}

/// `ws(c) = c == ' ' || c - 9 <= 4 ? 1 : c <= 0x84 ? 0 : table(c)`, with the
/// block structure of `char::is_whitespace` at O0: two guards feeding one
/// shared `true` arm, a `false` arm, a call arm, and one shared return.
///
/// The bodyless `ws_table` declaration is an FFI boundary, so the module must
/// pin its target (`ValidationError::TargetInfoRequired` otherwise).
fn region_exit_module(triple: &str) -> Module {
    let mut builder = ModuleBuilder::new_with_target_info(
        "shrink_wrap_region_exit",
        trust_ir::TargetInfo {
            triple: triple.into(),
            pointer_size: 8,
            endianness: trust_ir::Endianness::Little,
            abi: Some("aapcs64".into()),
            struct_passing: trust_ir::StructPassingPolicy::NativeC,
        },
    );
    let signature = builder.add_func_type(vec![Ty::I32], vec![Ty::I32]);
    let table = builder.declare_function("ws_table", signature);
    let mut function = builder.function("ws", signature);
    let entry = function.create_block();
    let second_guard = function.create_block();
    let third_guard = function.create_block();
    let true_arm = function.create_block();
    let false_arm = function.create_block();
    let call_arm = function.create_block();
    let exit = function.create_block();
    let c = function.add_block_param(entry, Ty::I32);
    let result = function.add_block_param(exit, Ty::I32);

    function.switch_to_block(entry);
    let space = function.iconst(Ty::I32, 0x20);
    let is_space = function.icmp(ICmpOp::Eq, Ty::I32, c, space);
    function.condbr(is_space, true_arm, vec![], second_guard, vec![]);

    function.switch_to_block(second_guard);
    let tab = function.iconst(Ty::I32, 9);
    let from_tab = function.sub(Ty::I32, c, tab);
    let four = function.iconst(Ty::I32, 4);
    let is_control_space = function.icmp(ICmpOp::Ule, Ty::I32, from_tab, four);
    function.condbr(is_control_space, true_arm, vec![], third_guard, vec![]);

    function.switch_to_block(third_guard);
    let ascii_limit = function.iconst(Ty::I32, 0x84);
    let is_low = function.icmp(ICmpOp::Ule, Ty::I32, c, ascii_limit);
    function.condbr(is_low, false_arm, vec![], call_arm, vec![]);

    function.switch_to_block(true_arm);
    let yes = function.iconst(Ty::I32, 1);
    function.br(exit, vec![yes]);

    function.switch_to_block(false_arm);
    let no = function.iconst(Ty::I32, 0);
    function.br(exit, vec![no]);

    function.switch_to_block(call_arm);
    let looked_up = function.call(table, vec![c]);
    function.br(exit, vec![looked_up]);

    function.switch_to_block(exit);
    function.ret(vec![result]);
    function.build();
    let module = builder.build().expect("ModuleBuilder::build: test fixture");
    let errors = trust_ir_build::validate_module(&module);
    assert!(errors.is_empty(), "region-exit module: {errors:?}");
    module
}

#[test]
fn darwin_region_exit_shape_restores_the_frame_on_every_path() {
    let module = region_exit_module(DARWIN);
    let function = module
        .functions
        .iter()
        .find(|function| function.name == "ws")
        .unwrap();
    let (lir, context) =
        trust_cg_lower::translate_function_with_license(function, &module, &permit_unlicensed())
            .unwrap();
    for level in OPT_LEVELS {
        // The pipeline enforces the frame net itself: on the old admission
        // this `prepare` failed with `[TCG-A64-SPILL-SLOT]
        // callee-saved-not-restored` for X29.
        let prepared = Pipeline::new(PipelineConfig {
            opt_level: level,
            verify: false,
            ..PipelineConfig::for_target(DARWIN)
        })
        .prepare_function_with_metrics(&lir, Some(&context))
        .unwrap_or_else(|error| panic!("{level:?}: {error:?}"))
        .0;
        assert!(
            prepared.insts.iter().any(|inst| inst.is_call()),
            "{level:?}: the call arm must survive, or the fixture no longer needs a frame"
        );
        match analyze_frame(&prepared) {
            FrameNetOutcome::Analyzed { violations, stats } => {
                assert!(violations.is_empty(), "{level:?}: {violations:?}");
                assert!(
                    stats.framed && stats.exits_checked > 0,
                    "{level:?}: {stats:?}"
                );
            }
            other => panic!("{level:?}: the frame net must model this stream: {other:?}"),
        }
    }
}

/// C driver plus an AArch64 shim: `ws_check(c, &out)` pins sentinels in
/// X19-X28, records SP and X29, calls `ws(c)`, and returns a bit mask of
/// everything the call failed to preserve (bit 0 SP, bit 1 X29, bits 2-11
/// X19-X28). The shim re-establishes its own SP from the record before it
/// touches its frame, so a callee that returns with SP moved is REPORTED
/// rather than crashing the harness.
const DRIVER: &str = r#"
#include <stdint.h>
#include <stdio.h>

#if defined(__APPLE__)
#define SYM(name) "_" #name
#define PAGE(name) "_" #name "@PAGE"
#define PAGEOFF(name) "_" #name "@PAGEOFF"
#else
#define SYM(name) #name
#define PAGE(name) #name
#define PAGEOFF(name) ":lo12:" #name
#endif

uint64_t ws_saved[2];
extern int32_t ws(int32_t);
extern uint64_t ws_check(int32_t c, int32_t *out);

int32_t ws_table(int32_t c) {
    return c == 0x85 || c == 0xa0 || c == 0x1680 || (c >= 0x2000 && c <= 0x200a) ||
           c == 0x2028 || c == 0x2029 || c == 0x202f || c == 0x205f || c == 0x3000;
}

__asm__(
    ".text\n"
    ".p2align 2\n"
    ".globl " SYM(ws_check) "\n"
    SYM(ws_check) ":\n"
    "    stp x29, x30, [sp, #-16]!\n"
    "    mov x29, sp\n"
    "    stp x19, x20, [sp, #-16]!\n"
    "    stp x21, x22, [sp, #-16]!\n"
    "    stp x23, x24, [sp, #-16]!\n"
    "    stp x25, x26, [sp, #-16]!\n"
    "    stp x27, x28, [sp, #-16]!\n"
    "    stp x1, xzr, [sp, #-16]!\n"
    "    mov x19, #0x1919\n"
    "    mov x20, #0x2020\n"
    "    mov x21, #0x2121\n"
    "    mov x22, #0x2222\n"
    "    mov x23, #0x2323\n"
    "    mov x24, #0x2424\n"
    "    mov x25, #0x2525\n"
    "    mov x26, #0x2626\n"
    "    mov x27, #0x2727\n"
    "    mov x28, #0x2828\n"
    "    adrp x9, " PAGE(ws_saved) "\n"
    "    add x9, x9, " PAGEOFF(ws_saved) "\n"
    "    mov x10, sp\n"
    "    str x10, [x9]\n"
    "    str x29, [x9, #8]\n"
    "    bl " SYM(ws) "\n"
    "    adrp x9, " PAGE(ws_saved) "\n"
    "    add x9, x9, " PAGEOFF(ws_saved) "\n"
    "    mov x12, #0\n"
    "    mov x10, sp\n"
    "    ldr x11, [x9]\n"
    "    cmp x10, x11\n"
    "    cset x13, ne\n"
    "    orr x12, x12, x13\n"
    "    ldr x11, [x9, #8]\n"
    "    cmp x29, x11\n"
    "    cset x13, ne\n"
    "    orr x12, x12, x13, lsl #1\n"
    "    mov x11, #0x1919\n cmp x19, x11\n cset x13, ne\n orr x12, x12, x13, lsl #2\n"
    "    mov x11, #0x2020\n cmp x20, x11\n cset x13, ne\n orr x12, x12, x13, lsl #3\n"
    "    mov x11, #0x2121\n cmp x21, x11\n cset x13, ne\n orr x12, x12, x13, lsl #4\n"
    "    mov x11, #0x2222\n cmp x22, x11\n cset x13, ne\n orr x12, x12, x13, lsl #5\n"
    "    mov x11, #0x2323\n cmp x23, x11\n cset x13, ne\n orr x12, x12, x13, lsl #6\n"
    "    mov x11, #0x2424\n cmp x24, x11\n cset x13, ne\n orr x12, x12, x13, lsl #7\n"
    "    mov x11, #0x2525\n cmp x25, x11\n cset x13, ne\n orr x12, x12, x13, lsl #8\n"
    "    mov x11, #0x2626\n cmp x26, x11\n cset x13, ne\n orr x12, x12, x13, lsl #9\n"
    "    mov x11, #0x2727\n cmp x27, x11\n cset x13, ne\n orr x12, x12, x13, lsl #10\n"
    "    mov x11, #0x2828\n cmp x28, x11\n cset x13, ne\n orr x12, x12, x13, lsl #11\n"
    "    ldr x10, [x9]\n"
    "    mov sp, x10\n"
    "    ldr x1, [sp], #16\n"
    "    str w0, [x1]\n"
    "    mov x0, x12\n"
    "    ldp x27, x28, [sp], #16\n"
    "    ldp x25, x26, [sp], #16\n"
    "    ldp x23, x24, [sp], #16\n"
    "    ldp x21, x22, [sp], #16\n"
    "    ldp x19, x20, [sp], #16\n"
    "    ldp x29, x30, [sp], #16\n"
    "    ret\n");

static int32_t oracle(int32_t c) {
    if (c == 0x20 || (uint32_t)(c - 9) <= 4) return 1;
    if ((uint32_t)c <= 0x84) return 0;
    return ws_table(c);
}

int main(void) {
    /* Every arm: ' ', each of '\t'..='\r' (the path that ran the sunk
       prologue and returned bare), the rest of the low range, and the table
       call with hits and misses. */
    static const int32_t inputs[] = {
        0x20, 0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x00, 0x08, 0x0e, 0x1f, 0x21,
        0x41, 0x7f, 0x84, 0x85, 0x86, 0xa0, 0x1680, 0x2000, 0x200a, 0x200b,
        0x2028, 0x3000, 0x10ffff,
    };
    unsigned checked = 0;
    for (unsigned i = 0; i != sizeof inputs / sizeof *inputs; ++i) {
        int32_t got = -1;
        uint64_t broken = ws_check(inputs[i], &got);
        if (broken) {
            printf("REGION_EXIT_FRAME_BROKEN c=0x%x mask=0x%llx\n", inputs[i],
                   (unsigned long long)broken);
            return 1;
        }
        if (got != oracle(inputs[i])) {
            printf("REGION_EXIT_WRONG c=0x%x got=%d want=%d\n", inputs[i], got,
                   oracle(inputs[i]));
            return 2;
        }
        /* The plain call, from a C frame that reads its locals after it. */
        volatile int32_t guard = 0x5a5a;
        int32_t direct = ws(inputs[i]);
        if (guard != 0x5a5a || direct != got) return 3;
        ++checked;
    }
    printf("REGION_EXIT_NATIVE checked=%u\n", checked);
    return 0;
}
"#;

#[test]
fn region_exit_shape_preserves_sp_fp_and_callee_saves_natively() {
    let module = region_exit_module(native_triple());
    for level in OPT_LEVELS {
        // Net OFF, so what executes is what the frame lowering emitted: the
        // old admission's object reached the machine and moved SP and X29.
        let object = trust_cg_codegen::env_lock::with_env_overrides(
            &[("TCG_AARCH64_POST_RA_SPILL_SLOTS", "off")],
            || native::compile(&module, level),
        );
        let Some(code) = native::link_run("shrink_wrap_region_exit", &object, DRIVER) else {
            return;
        };
        assert_eq!(code, 0, "{level:?}");
    }
    eprintln!("SHRINK_WRAP_REGION_EXIT_NATIVE levels=4 checked_per_level=24");
}

/// This file's fixture is hand-built and carries no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes (or fails by name) because it was silently refused.
fn permit_unlicensed() -> trust_cg_lower::CodegenLicensePolicy {
    trust_cg_lower::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit)
}
