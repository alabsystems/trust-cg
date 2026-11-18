// Copyright 2026 Andrew Yates | Licensed under the Apache License, Version 2.0

//! Retained inputs from actual AArch64 AOT frame preparation.
//!
//! These are producer observations, not an allocation, ABI, lifetime or
//! execution certificate. A consumer must bind them to the independently
//! decoded object and source inputs before using them in a frame proof.

use crate::{frame::FrameLayout, pipeline::PreparationMetrics};
use sha2::{Digest, Sha256};
use std::{borrow::Cow, sync::Arc};
use trust_cg_ir::function::{MachFunction, StackSlot};
use trust_cg_lower::{Function, ProofContext, source_stack_allocations::SourceStackAllocations};

/// Fresh caller inputs, hashed/indexed once per complete object/module request.
/// Construction grants no source, allocation, codegen or proof authority.
pub struct AotSourceAllocationRequest<'a> {
    object_sha256: [u8; 32],
    source_module: trust_ir::proof::ProofDigest,
    original_module: Option<trust_ir::proof::ProofDigest>,
    functions: std::collections::BTreeMap<u32, &'a trust_ir::Function>,
    adapter_input: &'a trust_ir::Module,
}
impl<'a> AotSourceAllocationRequest<'a> {
    pub fn new(object: &[u8], actual_adapter_input: &'a trust_ir::Module) -> Result<Self, String> {
        Self::with_digest(
            object,
            actual_adapter_input,
            actual_adapter_input.stable_digest_under(trust_ir::imports::IdentityScheme::V3),
        )
    }

    fn with_digest(
        object: &[u8],
        actual_adapter_input: &'a trust_ir::Module,
        source_module: trust_ir::proof::ProofDigest,
    ) -> Result<Self, String> {
        let mut functions = std::collections::BTreeMap::new();
        for function in &actual_adapter_input.functions {
            if functions.insert(function.id.index(), function).is_some() {
                return Err("AOT source allocation function identity is ambiguous".into());
            }
        }
        Ok(Self {
            object_sha256: Sha256::digest(object).into(),
            source_module,
            original_module: None,
            functions,
            adapter_input: actual_adapter_input,
        })
    }

    /// The exact canonical module whose allocation census is being checked.
    /// This is an endpoint observation, not a proof of preparation semantics.
    pub fn adapter_input(&self) -> &'a trust_ir::Module {
        self.adapter_input
    }

    pub fn adapter_input_digest(&self) -> trust_ir::proof::ProofDigest {
        self.source_module
    }

    /// Present only after rebinding a Compiler observation to its fresh
    /// original input. It records an endpoint, not a transformation proof.
    pub fn original_input_digest(&self) -> Option<trust_ir::proof::ProofDigest> {
        self.original_module
    }
    fn function(
        &self,
        allocations: &SourceStackAllocations,
    ) -> Result<&trust_ir::Function, String> {
        let id = allocations
            .source_function()
            .ok_or("AOT source allocation owner missing")?;
        self.functions
            .get(&id.index())
            .copied()
            .ok_or_else(|| "AOT source allocation function missing".into())
    }
}

/// The frame inputs used while preparing one actual AArch64 object function.
///
/// Slot indices are those of the prepared machine function. A fixed slot is
/// not thereby compiler-private: its source allocation/provenance relation is
/// a separate required input. Likewise a saved-register pair's legacy layout
/// offset is not an independently decoded memory address.
#[derive(Debug, Clone)]
pub struct AotFrameLayoutObservation {
    /// Exact symbol in the prepared function population.
    pub symbol: String,
    /// The actual retained frame-lowering input. Missing means unknown.
    pub layout: Option<FrameLayout>,
    /// Complete prepared slot population, including dynamic/unknown sizes.
    pub stack_slots: Vec<StackSlot>,
    /// A source/slot input bound to this actual object and preparation, or an
    /// explicit refusal. This is never an allocation or machine proof.
    pub source_stack_allocations: Result<AotSourceStackAllocations, String>,
}

/// Created only after checking the adapter's actual source/StackAddr census.
/// No Deserialize implementation or public minting constructor exists.
#[derive(Debug, Clone)]
pub struct AotSourceStackAllocations {
    object_sha256: [u8; 32],
    source_module: trust_ir::proof::ProofDigest,
    symbol: String,
    layout: Option<FrameLayout>,
    slots: Vec<StackSlot>,
    allocations: SourceStackAllocations,
    input: Arc<AotAdapterInput>,
}

/// Preserve an owned legalization result once, shared by every function. The
/// ordinary no-rewrite path retains only the original module's identity.
#[derive(Clone)]
struct AotAdapterInput {
    original_module: trust_ir::proof::ProofDigest,
    prepared_module: Option<Arc<trust_ir::Module>>,
}

impl std::fmt::Debug for AotAdapterInput {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("AotAdapterInput")
            .field("original_module", &self.original_module)
            .field("retains_prepared_module", &self.prepared_module.is_some())
            .finish()
    }
}

impl AotAdapterInput {
    fn retain(
        original: &trust_ir::Module,
        prepared: Cow<'_, trust_ir::Module>,
        adapter_digest: trust_ir::proof::ProofDigest,
    ) -> Self {
        let original_module = if std::ptr::eq(prepared.as_ref(), original) {
            adapter_digest
        } else {
            original.stable_digest_under(trust_ir::imports::IdentityScheme::V3)
        };
        let prepared_module = match prepared {
            Cow::Borrowed(module) if std::ptr::eq(module, original) => None,
            Cow::Borrowed(module) => Some(Arc::new(module.clone())),
            Cow::Owned(module) => Some(Arc::new(module)),
        };
        Self {
            original_module,
            prepared_module,
        }
    }

    fn adapter_input<'a>(
        &'a self,
        original: &'a trust_ir::Module,
    ) -> Result<&'a trust_ir::Module, String> {
        if original.stable_digest_under(trust_ir::imports::IdentityScheme::V3)
            != self.original_module
        {
            return Err("AOT source allocation original input differs".into());
        }
        Ok(self.prepared_module.as_deref().unwrap_or(original))
    }
}

impl AotSourceStackAllocations {
    /// Identity DATA only; use the observation's binding check before reading
    /// allocation inputs. A digest supplies no source/ownership/proof license.
    pub fn object_sha256(&self) -> [u8; 32] {
        self.object_sha256
    }
    pub fn adapter_input_digest(&self) -> trust_ir::proof::ProofDigest {
        self.source_module
    }
}

impl AotFrameLayoutObservation {
    /// Reconstruct a batch request from the actual Compiler's original input.
    /// A rewritten adapter module is owned by this observation, so the caller
    /// never has to substitute the original module for that distinct endpoint.
    /// Both endpoint identities, actual object and complete frame binding are
    /// checked. No transformation, allocation, lifetime or frame proof follows.
    pub fn source_allocation_request_from_original<'a>(
        &'a self,
        object: &[u8],
        original: &'a trust_ir::Module,
    ) -> Result<AotSourceAllocationRequest<'a>, String> {
        let binding = self
            .source_stack_allocations
            .as_ref()
            .map_err(Clone::clone)?;
        let adapter_input = binding.input.adapter_input(original)?;
        let mut request = AotSourceAllocationRequest::new(object, adapter_input)?;
        request.original_module = Some(binding.input.original_module);
        self.bound_source_stack_allocations_for(&request)?;
        Ok(request)
    }

    /// Rebind to actual request bytes, the precise backend adapter input module
    /// and this complete layout. `source` is the compiler's `lowered_module`,
    /// after any existing dialect/ABI preparation, not automatically the
    /// original Rust/THIR/Core input. Prior transformation custody is separate.
    /// Equal object symbols or allocation sizes cannot transfer this input.
    pub fn bound_source_stack_allocations<'a>(
        &'a self,
        object: &[u8],
        source: &trust_ir::Module,
    ) -> Result<&'a SourceStackAllocations, String> {
        self.bound_source_stack_allocations_for(&AotSourceAllocationRequest::new(object, source)?)
    }

    /// Batch form: reuse one fresh request for every function, without hashing
    /// the entire module/object or scanning its function population per row.
    pub fn bound_source_stack_allocations_for<'a>(
        &'a self,
        request: &AotSourceAllocationRequest<'_>,
    ) -> Result<&'a SourceStackAllocations, String> {
        let binding = self
            .source_stack_allocations
            .as_ref()
            .map_err(Clone::clone)?;
        if binding.object_sha256 != request.object_sha256
            || binding.source_module != request.source_module
            || request
                .original_module
                .is_some_and(|original| original != binding.input.original_module)
            || binding.symbol != self.symbol
            || binding.layout != self.layout
            || binding.slots != self.stack_slots
        {
            return Err("AOT source allocation object/source/layout binding differs".into());
        }
        binding
            .allocations
            .validate_source_function(request.function(&binding.allocations)?)?;
        Ok(&binding.allocations)
    }
}

pub(crate) fn observe_aarch64_frames(
    functions: &[MachFunction],
    metrics: &[PreparationMetrics],
    original: &trust_ir::Module,
    source: Cow<'_, trust_ir::Module>,
    lir: &[(Function, ProofContext)],
    object: &[u8],
) -> Vec<AotFrameLayoutObservation> {
    let source_digest = source.stable_digest_under(trust_ir::imports::IdentityScheme::V3);
    let input = Arc::new(AotAdapterInput::retain(original, source, source_digest));
    let source = input.prepared_module.as_deref().unwrap_or(original);
    let request = AotSourceAllocationRequest::with_digest(object, source, source_digest);
    // Preserve every function even if a future producer fails to retain a
    // metric row. No zip truncation and no absent-layout => zero-frame rule.
    functions
        .iter()
        .enumerate()
        .map(|(index, function)| AotFrameLayoutObservation {
            symbol: function.name.clone(),
            layout: metrics.get(index).and_then(|row| row.frame_layout.clone()),
            stack_slots: function.stack_slots.clone(),
            source_stack_allocations: (|| {
                let (lowered, context) = lir
                    .get(index)
                    .ok_or("AOT source allocation LIR row missing")?;
                let allocations = &context.source_stack_allocations;
                let request = request.as_ref().map_err(Clone::clone)?;
                allocations.validate_source_function(request.function(allocations)?)?;
                allocations.validate_lir(lowered)?;
                if lowered.name != function.name || allocations.symbol() != function.name {
                    return Err("AOT source allocation prepared function differs".into());
                }
                for allocation in allocations.records() {
                    let slot = function
                        .stack_slots
                        .get(allocation.stack_slot() as usize)
                        .ok_or("AOT source allocation prepared slot missing")?;
                    let expected = allocation.geometry();
                    if slot.size != expected.size
                        || slot.align != expected.align
                        || slot.allocation != expected.allocation
                    {
                        return Err("AOT source allocation prepared slot geometry differs".into());
                    }
                }
                Ok(AotSourceStackAllocations {
                    object_sha256: request.object_sha256,
                    source_module: request.source_module,
                    symbol: function.name.clone(),
                    layout: metrics.get(index).and_then(|row| row.frame_layout.clone()),
                    slots: function.stack_slots.clone(),
                    allocations: allocations.clone(),
                    input: Arc::clone(&input),
                })
            })(),
        })
        .collect()
}
