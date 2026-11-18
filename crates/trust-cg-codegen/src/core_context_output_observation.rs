// Copyright 2026 Andrew Yates | Apache-2.0
//! A historical physical word observation, with an explicit current-state check.

use super::*;
use trust_cg_verify::read_only_replay::{ReplayedVoidWordMemoryClaim, VoidWordMemoryClaim};

/// One actual successful call on retained initialized storage, followed by
/// independent replay of its original Core normal return and all sixteen
/// post bytes. The exact installed image and allocations remain alive.
/// Getters describe that historical call. Only `check_current` authenticates
/// the same entry's still-current bytes; every later call invalidates it.
pub struct CoreWordMemoryObservation {
    installed: Arc<InstalledArtifact>,
    owner: Arc<CoreBoundContextOutputProof>,
    generation: u64,
    proof: ReplayedVoidWordMemoryClaim,
    proof_time: std::time::Duration,
}

impl std::fmt::Debug for CoreWordMemoryObservation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("CoreWordMemoryObservation")
            .field("function", &self.owner.function)
            .field("generation", &self.generation)
            .field("claim", &self.proof.claim())
            .finish_non_exhaustive()
    }
}

impl CoreWordMemoryObservation {
    pub(super) fn new(
        installed: Arc<InstalledArtifact>,
        owner: Arc<CoreBoundContextOutputProof>,
        generation: u64,
        claim: VoidWordMemoryClaim,
        proof: ReplayedVoidWordMemoryClaim,
        proof_time: std::time::Duration,
    ) -> Result<Self, EntryStackError> {
        if proof.claim() != claim
            || !owner.replay.owns_word_memory_claim(&proof)
            || u64::try_from(owner.context_extent.0).ok() != Some(claim.context_address)
            || u64::try_from(owner.output_extent.0).ok() != Some(claim.output_address)
        {
            return Err(EntryStackError::Source(
                "word observation proof/source/physical addresses differ".into(),
            ));
        }
        Ok(Self {
            installed,
            owner,
            generation,
            proof,
            proof_time,
        })
    }

    /// The exact immutable Core allocation retained by the compiler replay.
    pub fn core_module(&self) -> &Arc<trust_ir::Module> {
        self.owner.replay.module()
    }
    /// The actual source function in that immutable Core.
    pub fn source_function(&self) -> trust_ir::FuncId {
        self.owner.replay.function()
    }
    /// Historical physical addresses and before/after words, never permissions.
    pub fn historical_words(&self) -> VoidWordMemoryClaim {
        self.proof.claim()
    }
    /// Actual context-readable and separately output-writable extents retained
    /// through the call. This does not grant another caller access to them.
    pub fn historical_extents(&self) -> [(usize, usize); 2] {
        [self.owner.context_extent, self.owner.output_extent]
    }
    /// Exact whole compiler/source/machine/final-byte replay identity.
    pub fn compilation_statement(&self) -> trust_ir::proof::ProofDigest {
        self.owner.replay.statement_digest()
    }
    /// Exact independently replayed concrete post-memory proposition inventory.
    pub fn post_memory_statement(&self) -> trust_ir::proof::ProofDigest {
        self.proof.statement_digest()
    }
    /// Elapsed concrete proof replay, separate from compilation/native dispatch.
    pub fn proof_replay_time(&self) -> std::time::Duration {
        self.proof_time
    }
    /// Original query digests and existing Clean/formal replay attribution.
    pub fn proof_replay_diagnostics(&self) -> &[(String, Option<String>)] {
        self.proof.replay_diagnostics()
    }
    /// Owner memory epoch captured by this call; calls and host word updates
    /// advance it even when the resulting bytes are unchanged.
    pub fn invocation_generation(&self) -> u64 {
        self.generation
    }

    /// Authenticate current bytes only for this same live Core/image/storage
    /// owner and exact invocation epoch. Historical observations stay readable
    /// after a later call, but cannot authenticate the later memory state.
    pub fn check_current(
        &self,
        entry: &CoreOwnedContextOutputEntry,
    ) -> Result<(), EntryStackError> {
        if !Arc::ptr_eq(&self.owner, &entry.owner)
            || !Arc::ptr_eq(&self.installed, &entry.installed)
        {
            return Err(EntryStackError::StaleInvocation);
        }
        entry.check_installed()?;
        let storage = self
            .owner
            .storage
            .lock()
            .map_err(|_| EntryStackError::Source("context storage mutex poisoned".into()))?;
        let claim = self.proof.claim();
        if self.owner.invocation_generation.load(Ordering::Relaxed) != self.generation
            || storage.context.extent()? != self.owner.context_extent
            || storage.output.extent()? != self.owner.output_extent
            || storage.stack.allocation().identity != self.owner.stack_identity
            || storage.context.value() != [claim.context_after]
            || storage.output.words() != [claim.output_after]
        {
            return Err(EntryStackError::StaleInvocation);
        }
        Ok(())
    }
}

#[cfg(all(test, target_arch = "aarch64", target_os = "macos"))]
#[path = "../tests/common/private_word_memory_observation.rs"]
mod tests;
