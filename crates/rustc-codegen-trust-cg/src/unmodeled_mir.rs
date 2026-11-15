//! The named refusals of the MIR families this frontend does not lower
//! (ledger L06-P8, `rustc-mir-coverage-inventory.md`).
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache-2.0
//!
//! Each refusal keeps the `TerminatorKind::<Variant>` / `Rvalue::<Variant>`
//! name the inventory promises and adds a stable code with the reason:
//!
//! * `[TCG-TAIL-CALL]` `TerminatorKind::TailCall` (`become`). trust-ir has no
//!   tail-call instruction, and the AArch64 backend's tail-call pass is an
//!   optimization, not a guarantee. `become` promises that the caller's frame
//!   is gone before the callee runs, so a call followed by a return would grow
//!   the stack where rustc's LLVM backend does not.
//! * `[TCG-INLINE-ASM]` `TerminatorKind::InlineAsm`, outside the bounded
//!   scalar floating-point grammar `aarch64_fp_asm` lowers to dialect
//!   operations: trust-ir carries no assembly, and an `asm!` block's
//!   instructions, operands, clobbers and options are not modeled.
//! * `[TCG-MIR-NOT-RUNTIME]` `TerminatorKind::Yield`, `CoroutineDrop`,
//!   `FalseEdge`, `FalseUnwind` and `Rvalue::CopyForDeref`. None of these is a
//!   runtime-MIR construct on the pinned compiler: the coroutine transform
//!   replaces `Yield`/`CoroutineDrop`, borrowck cleanup removes the false
//!   edges, the required `EraseDerefTemps` pass rewrites every `CopyForDeref`
//!   into a plain copy, and the MIR validator rejects them in runtime MIR
//!   (`rustc_codegen_ssa` treats each as a compiler bug). One reaching this
//!   backend is refused, never guessed at.
//! * `[TCG-UNSAFE-BINDER]` `Rvalue::WrapUnsafeBinder` (the incomplete
//!   `unsafe_binders` feature): the binder type has no trust-ir mapping.

use super::*;

/// The refusal for a terminator `lower_terminator_kind` has no arm for.
pub(super) fn terminator_refusal(kind: &TerminatorKind<'_>) -> String {
    let name = terminator_kind_name(kind);
    match kind {
        TerminatorKind::TailCall { .. } => format!(
            "[TCG-TAIL-CALL] TerminatorKind::{name}: `become` requires a guaranteed tail call \
             (the caller's frame released before the callee runs); trust-ir has no tail-call \
             instruction and the backend's tail-call pass is an optimization, not a guarantee, \
             so a call+return lowering could overflow the stack where LLVM does not"
        ),
        TerminatorKind::Yield { .. }
        | TerminatorKind::CoroutineDrop
        | TerminatorKind::FalseEdge { .. }
        | TerminatorKind::FalseUnwind { .. } => not_runtime(&format!("TerminatorKind::{name}")),
        _ => format!("TerminatorKind::{name}"),
    }
}

/// The refusal for an rvalue `lower_assign` has no arm for.
pub(super) fn rvalue_refusal(rvalue: &Rvalue<'_>) -> String {
    let name = rvalue_kind_name(rvalue);
    match rvalue {
        Rvalue::CopyForDeref(_) => not_runtime(&format!("Rvalue::{name}")),
        Rvalue::WrapUnsafeBinder(..) => format!(
            "[TCG-UNSAFE-BINDER] Rvalue::{name}: unsafe-binder types (`unsafe_binders`) have no \
             trust-ir mapping"
        ),
        _ => format!("Rvalue::{name}"),
    }
}

/// The refusal for an `asm!` block the bounded FP grammar does not admit.
pub(super) fn inline_asm_refusal(reason: &str) -> String {
    format!(
        "[TCG-INLINE-ASM] TerminatorKind::InlineAsm: {reason} (trust-ir carries no assembly; \
         only the bounded scalar FP grammar of `aarch64_fp_asm` is lowered)"
    )
}

fn not_runtime(what: &str) -> String {
    format!(
        "[TCG-MIR-NOT-RUNTIME] {what} is not a runtime-MIR construct on this compiler (the MIR \
         validator rejects it after the runtime lowering passes, and rustc_codegen_ssa treats \
         it as a compiler bug); refusing it rather than guessing its semantics"
    )
}
