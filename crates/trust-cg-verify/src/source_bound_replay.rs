// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! The capability that reaches per-compile live formal replay.
//!
//! Only a source-bound owner may be replayed live: the AArch64 frame, ALU,
//! constant, raw body, frameless whole-body and scalar-cell caller owners,
//! the parts of an
//! AArch64 memory row bound to a source-bound owner
//! ([`crate::aarch64_memory_source_binding`]), the x86-64 body owner (slice
//! 16: or the parts of its theorem stated in parts) and the
//! parts of the x86-64 ABI envelope owner, and the parts of the original-Core
//! read-only/scalar-memory inventories.
//! The AArch64 trap-expansion capability
//! ([`crate::aarch64_trap_expansion::TrapExpansionReplay`]) takes the same
//! route, although its intent side is the machine-IR carrier's trap
//! condition rather than a source instruction (instruction selection's
//! choice of carrier is trusted, as for every machine-IR row): it is built
//! only from an obligation decided to hold in process, and its replay is
//! bound to the request exactly as a source-bound owner's is.
//! The trait is sealed, so no other type in this crate can implement
//! it, and each owner type has no public constructor, so the owner value
//! itself is the capability (an envelope part is handed out only by its
//! built owner). Replay serializes
//! the owner's obligation raw (no arithmetic simplifier inside the
//! source-to-proof boundary) and credits only a refutation that Clean/Carcara
//! independently accepted against that original problem (`AYResult::Verified`).
//! Constructive closed-definition proofs retain explicit producer/checker
//! attribution; they do not claim an AY run or receive AY reuse receipts.

use crate::lowering_proof::ProofObligation;

mod sealed {
    pub trait Sealed {}
    impl Sealed for crate::source_bound_defined_call::DefinedCallTraceReplay<'_> {}
    impl Sealed for crate::aarch64_affine_lowering::CheckedDefinedPeerCall<'_> {}
    impl Sealed for crate::source_bound_frame::SourceBoundFrame<'_> {}
    impl Sealed for crate::source_bound_alu::SourceBoundAlu<'_, '_> {}
    impl Sealed for crate::aarch64_memory_source_binding::SourceBoundMemoryPart {}
    impl Sealed for crate::source_bound_constant::SourceBoundConstant<'_, '_> {}
    impl Sealed for crate::source_bound_body::SourceBoundBody<'_, '_> {}
    impl Sealed for crate::source_bound_a64_control::SourceBoundA64Control<'_, '_> {}
    impl Sealed for crate::source_bound_a64_body::SourceBoundA64Body<'_> {}
    impl Sealed for crate::source_bound_frame::ScalarCellCallerPart<'_> {}
    impl Sealed for crate::x86_source_bound_body::SourceBoundX86Body<'_> {}
    impl Sealed for crate::x86_source_bound_body::X86BodyPart<'_> {}
    impl Sealed for crate::x86_source_bound_body::X86BodyClaim {}
    impl Sealed for crate::x86_source_bound_body::X86BodyGeneralized {}
    impl Sealed for crate::x86_source_bound_envelope::X86EnvelopePart<'_> {}
    impl Sealed for crate::read_only_replay::ReadOnlyReplayPart<'_> {}
    impl Sealed for crate::read_only_replay::ScalarMemoryReplayPart<'_> {}
    impl Sealed for crate::read_only_replay::ScalarReturnReplayPart<'_> {}
    impl Sealed for crate::aarch64_trap_expansion::TrapExpansionReplay {}
}

/// A source-bound owner whose exact obligation may be replayed live.
pub(crate) trait SourceBoundReplay: sealed::Sealed {
    /// The obligation exactly as the owner constructed it.
    fn replayed_obligation(&self) -> &ProofObligation;

    /// Slice 19 (OD-197): whether a resident AY deadline is followed by one
    /// fresh, proof-producing replay of the same query under the same
    /// budget (the x86-64 body owner, its parts and its claims); every
    /// other owner takes a resident deadline as its conclusive timeout.
    fn fresh_after_resident_timeout(&self) -> bool {
        false
    }

    /// Slice 23 (OD-206): whether the obligation is the generalization of an
    /// x86-64 body obligation over its arithmetic leaves (its replay route,
    /// which the negative memo's key carries).
    fn generalized(&self) -> bool {
        false
    }
}

impl SourceBoundReplay for crate::source_bound_frame::SourceBoundFrame<'_> {
    fn replayed_obligation(&self) -> &ProofObligation {
        self.obligation()
    }
}

impl SourceBoundReplay for crate::source_bound_alu::SourceBoundAlu<'_, '_> {
    fn replayed_obligation(&self) -> &ProofObligation {
        self.obligation()
    }
}

/// A part of a memory row a source-bound owner bound
/// ([`crate::aarch64_memory_source_binding::SourceBoundMemoryRow`]): minted
/// only by that binding, so an unbound word's part cannot reach this route
/// (it takes [`WordBoundReplay`], whose verdicts credit nothing).
impl SourceBoundReplay for crate::aarch64_memory_source_binding::SourceBoundMemoryPart {
    fn replayed_obligation(&self) -> &ProofObligation {
        self.obligation()
    }
}

impl SourceBoundReplay for crate::source_bound_constant::SourceBoundConstant<'_, '_> {
    fn replayed_obligation(&self) -> &ProofObligation {
        self.obligation()
    }
}

impl SourceBoundReplay for crate::source_bound_body::SourceBoundBody<'_, '_> {
    fn replayed_obligation(&self) -> &ProofObligation {
        self.obligation()
    }
}

impl SourceBoundReplay for crate::source_bound_a64_control::SourceBoundA64Control<'_, '_> {
    fn replayed_obligation(&self) -> &ProofObligation {
        self.obligation()
    }
}

impl SourceBoundReplay for crate::source_bound_a64_body::SourceBoundA64Body<'_> {
    fn replayed_obligation(&self) -> &ProofObligation {
        self.obligation()
    }
}

/// A part of the AArch64 scalar-cell caller's whole-call theorem
/// ([`crate::source_bound_frame::source_bound_scalar_cell_caller`]), stated
/// in parts: handed out only by its built owner
/// ([`crate::source_bound_frame::SourceBoundScalarCellCaller::replay_parts`]).
impl SourceBoundReplay for crate::source_bound_frame::ScalarCellCallerPart<'_> {
    fn replayed_obligation(&self) -> &ProofObligation {
        self.obligation()
    }
}

impl SourceBoundReplay for crate::x86_source_bound_body::SourceBoundX86Body<'_> {
    fn replayed_obligation(&self) -> &ProofObligation {
        self.obligation()
    }

    fn fresh_after_resident_timeout(&self) -> bool {
        true
    }
}

/// A part of an x86-64 body theorem stated in parts (slice 16): handed out
/// only by its built owner ([`crate::x86_source_bound_body::SourceBoundX86Body::replay_parts`]).
impl SourceBoundReplay for crate::x86_source_bound_body::X86BodyPart<'_> {
    fn replayed_obligation(&self) -> &ProofObligation {
        self.obligation()
    }

    fn fresh_after_resident_timeout(&self) -> bool {
        true
    }
}

/// Slice 19 (OD-197): one claim of an x86-64 body theorem or part, replayed
/// on its own: handed out only by its built owner
/// ([`crate::x86_source_bound_body::SourceBoundX86Body::replay_claims`]).
impl SourceBoundReplay for crate::x86_source_bound_body::X86BodyClaim {
    fn replayed_obligation(&self) -> &ProofObligation {
        self.obligation()
    }

    fn fresh_after_resident_timeout(&self) -> bool {
        true
    }
}

/// Slice 23 (OD-206): the generalization of an x86-64 body theorem, part or
/// claim over its arithmetic leaves, replayed once after the exact
/// obligation's replay was neither Valid nor refuted: handed out only by its
/// built owner ([`crate::x86_source_bound_body::SourceBoundX86Body::replay_generalized`],
/// [`crate::x86_source_bound_body::X86BodyClaim::generalized`]).
impl SourceBoundReplay for crate::x86_source_bound_body::X86BodyGeneralized {
    fn replayed_obligation(&self) -> &ProofObligation {
        self.obligation()
    }

    fn fresh_after_resident_timeout(&self) -> bool {
        true
    }

    fn generalized(&self) -> bool {
        true
    }
}

impl SourceBoundReplay for crate::x86_source_bound_envelope::X86EnvelopePart<'_> {
    fn replayed_obligation(&self) -> &ProofObligation {
        self.obligation()
    }
}

impl SourceBoundReplay for crate::read_only_replay::ReadOnlyReplayPart<'_> {
    fn replayed_obligation(&self) -> &ProofObligation {
        self.obligation()
    }
}

impl SourceBoundReplay for crate::read_only_replay::ScalarMemoryReplayPart<'_> {
    fn replayed_obligation(&self) -> &ProofObligation {
        self.obligation()
    }
}

impl SourceBoundReplay for crate::read_only_replay::ScalarReturnReplayPart<'_> {
    fn replayed_obligation(&self) -> &ProofObligation {
        self.obligation()
    }
}

impl SourceBoundReplay for crate::aarch64_trap_expansion::TrapExpansionReplay {
    fn replayed_obligation(&self) -> &ProofObligation {
        self.obligation()
    }
}

mod word_bound_sealed {
    pub trait Sealed {}
    impl Sealed for crate::aarch64_memory_effect::MemoryEffectObligation {}
}

/// A word-bound obligation that may be replayed live to RECORD whether its
/// exact query has a Clean-checked certificate: the parts of an AArch64
/// memory-effect decomposition ([`crate::aarch64_memory_effect`]).
///
/// Replay is the same as a source-bound owner's (the raw query, AY's proof,
/// Clean's independent check, `Valid` only for `AYResult::Verified`), but the
/// capability is distinct and a `Valid` verdict of these credits nothing: the
/// obligation binds a word to machine-IR operands, not to a source, so for an
/// UNBOUND row the only evidence that credits it is the Formal-only
/// bound-memory rule's (a committed, replayed certificate of its form
/// theorem), and the function verifier records the count
/// ([`crate::function_verifier::MEMORY_EFFECT_IS_NOT_CREDIT`]) whatever the
/// certificates say. Sealed separately from [`SourceBoundReplay`] so that no
/// word-bound type can reach a source-bound credit path: a part reaches that
/// path only as a [`crate::aarch64_memory_source_binding::SourceBoundMemoryPart`],
/// which only a source binding mints.
pub(crate) trait WordBoundReplay: word_bound_sealed::Sealed {
    /// The obligation exactly as the decomposition built it.
    fn replayed_obligation(&self) -> &ProofObligation;
}

impl WordBoundReplay for crate::aarch64_memory_effect::MemoryEffectObligation {
    fn replayed_obligation(&self) -> &ProofObligation {
        &self.obligation
    }
}

impl SourceBoundReplay for crate::source_bound_defined_call::DefinedCallTraceReplay<'_> {
    fn replayed_obligation(&self) -> &ProofObligation {
        self.obligation()
    }
}

impl SourceBoundReplay for crate::aarch64_affine_lowering::CheckedDefinedPeerCall<'_> {
    fn replayed_obligation(&self) -> &ProofObligation {
        self.obligation()
    }
}
