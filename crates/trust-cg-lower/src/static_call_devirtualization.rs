// trust-cg-lower/static_call_devirtualization.rs - exact static-call contracts
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Fail-closed contracts used by adapter-fused static call devirtualization.
//!
//! Provenance discovery lives in `trust_ir::analysis`; this module adds the
//! module-level identity and exact call-edge checks TrustCG needs before it may
//! emit a named LIR call. It never rewrites or clones TrustIR; the compact
//! identity/name catalog is shared by every lowering path that resolves a
//! `FuncId`, so ordinary programs also avoid repeated module scans.

use std::collections::{HashMap, hash_map::Entry};

use crate::adapter::AdapterError;
use crate::function::Function as LirFunction;
use crate::instructions::{Block, DirectCallBinding, Opcode};
use crate::types::Type;
use trust_ir::analysis::{
    StaticFunctionPointerCacheState, StaticFunctionPointerCarrier,
    StaticFunctionPointerQueryCensus, StaticFunctionPointerResolution,
};
use trust_ir::{BlockId, CallingConv, FuncId, FuncTyId, Function, Linkage, Module, Ty, ValueId};

#[derive(Debug, Clone, Copy)]
pub(crate) struct PendingExactModuleCallAuthorization {
    block: Block,
    instruction: usize,
    source_origin: trust_cg_ir::TrustIrInstId,
    target: FuncId,
}

impl PendingExactModuleCallAuthorization {
    pub(crate) fn new(
        block: Block,
        instruction: usize,
        source_origin: trust_cg_ir::TrustIrInstId,
        target: FuncId,
    ) -> Self {
        Self {
            block,
            instruction,
            source_origin,
            target,
        }
    }
}

/// One strict-lowering census row for a direct call to a bodyless External
/// declaration. This is source-identity authentication only; native catalog
/// authority is joined later by the Core planning transaction.
#[derive(Debug, Clone, Copy)]
pub(crate) struct PendingDeclaredExternalCallAuthorization {
    block: Block,
    instruction: usize,
    source_origin: trust_cg_ir::TrustIrInstId,
    target: FuncId,
}

impl PendingDeclaredExternalCallAuthorization {
    pub(crate) fn new(
        block: Block,
        instruction: usize,
        source_origin: trust_cg_ir::TrustIrInstId,
        target: FuncId,
    ) -> Self {
        Self {
            block,
            instruction,
            source_origin,
            target,
        }
    }
}

/// Fused per-function call-identity census transferred from the adapter's
/// mandatory provenance walk into module-level replay.
pub(crate) struct PendingDirectCallAuthorizations {
    exact_count: usize,
    exact_sites: Vec<PendingExactModuleCallAuthorization>,
    declared_external_count: usize,
    declared_external_sites: Vec<PendingDeclaredExternalCallAuthorization>,
}

impl PendingDirectCallAuthorizations {
    pub(crate) fn new(
        exact_count: usize,
        exact_sites: Vec<PendingExactModuleCallAuthorization>,
        declared_external_count: usize,
        declared_external_sites: Vec<PendingDeclaredExternalCallAuthorization>,
    ) -> Self {
        Self {
            exact_count,
            exact_sites,
            declared_external_count,
            declared_external_sites,
        }
    }
}

#[derive(Debug, Clone, Copy)]
struct ExactModuleCallAuthorization {
    lir_function: usize,
    caller: FuncId,
    target: FuncId,
    block: Block,
    instruction: usize,
    source_origin: trust_cg_ir::TrustIrInstId,
    edge_digest: trust_ir::proof::ProofDigest,
}

#[derive(Debug, Clone, Copy)]
struct DeclaredExternalCallAuthorization {
    lir_function: usize,
    caller: FuncId,
    target: FuncId,
    block: Block,
    instruction: usize,
    source_origin: trust_cg_ir::TrustIrInstId,
    edge_digest: trust_ir::proof::ProofDigest,
}

/// Sparse, lowering-owned authentication of local calls, function addresses,
/// and imported call identity (not a source-to-machine proof).
///
/// The report has no public constructor and records only successful exact
/// recoveries. Ordinary modules retain an empty `Vec` (no heap allocation), so
/// compiler replay is O(1) when this feature is dormant. When entries exist,
/// replay touches just the authorized LIR coordinates and the one shared module
/// catalog rather than rescanning every instruction.
#[derive(Debug)]
pub struct ModuleTranslationValidationReport<'module> {
    module: &'module Module,
    exact_module_calls: Vec<ExactModuleCallAuthorization>,
    exact_module_addresses: usize,
    declared_external_calls: Vec<DeclaredExternalCallAuthorization>,
}

impl<'module> ModuleTranslationValidationReport<'module> {
    pub(crate) const fn new(module: &'module Module) -> Self {
        Self {
            module,
            exact_module_calls: Vec::new(),
            exact_module_addresses: 0,
            declared_external_calls: Vec::new(),
        }
    }

    pub(crate) fn record_translated_function(
        &mut self,
        lir_function: usize,
        caller: FuncId,
        function: &LirFunction,
        census: PendingDirectCallAuthorizations,
    ) -> Result<(), crate::adapter::AdapterError> {
        let PendingDirectCallAuthorizations {
            exact_count: expected_exact_calls,
            exact_sites: sites,
            declared_external_count: expected_declared_external_calls,
            declared_external_sites,
        } = census;
        if sites.len() != expected_exact_calls {
            return Err(crate::adapter::AdapterError::UnsupportedInstruction(
                format!(
                    "lowering recorded {expected_exact_calls} exact call(s) in `{}`, but its fused carrier census contains {}",
                    function.name,
                    sites.len()
                ),
            ));
        }

        if declared_external_sites.len() != expected_declared_external_calls {
            return Err(AdapterError::UnsupportedInstruction(format!(
                "lowering recorded {expected_declared_external_calls} declared-external call(s) in `{}`, but its fused carrier census contains {}",
                function.name,
                declared_external_sites.len()
            )));
        }
        // Both carrier kinds authenticate the same caller. Avoid hashing dormant
        // functions, and retain a concrete context for every nonempty census.
        if sites.is_empty() && declared_external_sites.is_empty() {
            return Ok(());
        }
        let caller_context = exact_call_context_digest(caller, function)?;
        let mut edge_bytes = Vec::new();
        for site in sites {
            let block = function.blocks.get(&site.block).ok_or_else(|| {
                crate::adapter::AdapterError::UnsupportedInstruction(format!(
                    "exact-call census for `{}` references missing LIR block {:?}",
                    function.name, site.block
                ))
            })?;
            let instruction = block.instructions.get(site.instruction).ok_or_else(|| {
                crate::adapter::AdapterError::UnsupportedInstruction(format!(
                    "exact-call census for `{}` references missing LIR block {:?} instruction {}",
                    function.name, site.block, site.instruction
                ))
            })?;
            let source_origin = function
                .trust_ir_origins
                .get(&site.block)
                .and_then(|origins| origins.get(site.instruction))
                .copied()
                .flatten();
            if source_origin != Some(site.source_origin) {
                return Err(crate::adapter::AdapterError::UnsupportedInstruction(
                    format!(
                        "exact-call census for `{}` does not match its completed source-edge provenance",
                        function.name
                    ),
                ));
            }
            let target = match &instruction.opcode {
                Opcode::Call {
                    binding: DirectCallBinding::ExactModuleFunction { function },
                    ..
                }
                | Opcode::Invoke {
                    binding: DirectCallBinding::ExactModuleFunction { function },
                    ..
                }
                | Opcode::FunctionAddr { function, .. } => FuncId::new(*function),
                _ => {
                    return Err(crate::adapter::AdapterError::UnsupportedInstruction(
                        format!(
                            "exact-call census for `{}` does not point at an exact call",
                            function.name
                        ),
                    ));
                }
            };
            if target != site.target {
                return Err(crate::adapter::AdapterError::UnsupportedInstruction(
                    format!(
                        "exact-call census for `{}` expected FuncId({}), but its completed LIR carrier names FuncId({})",
                        function.name,
                        site.target.index(),
                        target.index()
                    ),
                ));
            }
            let edge_digest = exact_call_edge_digest(
                caller_context,
                function,
                site.block,
                site.instruction,
                instruction,
                &mut edge_bytes,
            )?;
            self.exact_module_addresses +=
                usize::from(matches!(instruction.opcode, Opcode::FunctionAddr { .. }));
            self.exact_module_calls.push(ExactModuleCallAuthorization {
                lir_function,
                caller,
                target,
                block: site.block,
                instruction: site.instruction,
                source_origin: site.source_origin,
                edge_digest,
            });
        }
        for site in declared_external_sites {
            let block = function.blocks.get(&site.block).ok_or_else(|| {
                crate::adapter::AdapterError::UnsupportedInstruction(format!(
                    "declared-external-call census for `{}` references missing LIR block {:?}",
                    function.name, site.block
                ))
            })?;
            let instruction = block.instructions.get(site.instruction).ok_or_else(|| {
                crate::adapter::AdapterError::UnsupportedInstruction(format!(
                    "declared-external-call census for `{}` references missing LIR block {:?} instruction {}",
                    function.name, site.block, site.instruction
                ))
            })?;
            let source_origin = function
                .trust_ir_origins
                .get(&site.block)
                .and_then(|origins| origins.get(site.instruction))
                .copied()
                .flatten();
            if source_origin != Some(site.source_origin) {
                return Err(crate::adapter::AdapterError::UnsupportedInstruction(
                    format!(
                        "declared-external-call census for `{}` does not match its completed source-edge provenance",
                        function.name
                    ),
                ));
            }
            let target = match &instruction.opcode {
                Opcode::Call {
                    binding: DirectCallBinding::DeclaredExternalFunction { function },
                    ..
                }
                | Opcode::Invoke {
                    binding: DirectCallBinding::DeclaredExternalFunction { function },
                    ..
                } => FuncId::new(*function),
                _ => {
                    return Err(crate::adapter::AdapterError::UnsupportedInstruction(
                        format!(
                            "declared-external-call census for `{}` does not point at a pending imported call",
                            function.name
                        ),
                    ));
                }
            };
            if target != site.target {
                return Err(crate::adapter::AdapterError::UnsupportedInstruction(
                    format!(
                        "declared-external-call census for `{}` expected FuncId({}), but its completed LIR carrier names FuncId({})",
                        function.name,
                        site.target.index(),
                        target.index()
                    ),
                ));
            }
            let edge_digest = exact_call_edge_digest(
                caller_context,
                function,
                site.block,
                site.instruction,
                instruction,
                &mut edge_bytes,
            )?;
            self.declared_external_calls
                .push(DeclaredExternalCallAuthorization {
                    lir_function,
                    caller,
                    target,
                    block: site.block,
                    instruction: site.instruction,
                    source_origin: site.source_origin,
                    edge_digest,
                });
        }
        Ok(())
    }

    /// Compatibility alias for [`Self::replay_exact_module_bindings`].
    /// Replays both calls and addresses, so older consumers cannot silently
    /// ignore a newly emitted address carrier. Public LIR flags are not authority.
    pub fn replay_exact_module_calls(
        &self,
        functions: &[(LirFunction, crate::adapter::ProofContext)],
    ) -> Result<(), crate::adapter::AdapterError> {
        self.replay_exact_module_bindings(functions)
    }

    /// Replay exact direct-call and materialized function-address bindings.
    ///
    /// This sparse source-owned check must run before LIR mutations. It binds
    /// the target identity, source coordinate and complete emitted edge; it is
    /// not a source-to-machine proof or permission to bypass Core admission.
    pub fn replay_exact_module_bindings(
        &self,
        functions: &[(LirFunction, crate::adapter::ProofContext)],
    ) -> Result<(), crate::adapter::AdapterError> {
        if self.exact_module_calls.is_empty() {
            return Ok(());
        }

        let module = self.module;
        let catalog = ModuleFunctionCatalog::new(module);
        if let Some(id) = catalog.first_ambiguous_id() {
            return Err(crate::adapter::AdapterError::UnsupportedInstruction(
                format!(
                    "cannot replay exact calls against ambiguous FuncId({})",
                    id.index()
                ),
            ));
        }
        if let Some(name) = catalog.first_ambiguous_symbol() {
            return Err(crate::adapter::AdapterError::UnsupportedInstruction(
                format!("cannot replay exact calls against ambiguous module symbol {name:?}"),
            ));
        }

        let mut caller_context = None;
        let mut edge_bytes = Vec::new();
        for authorization in &self.exact_module_calls {
            let (lir_caller, _) = functions.get(authorization.lir_function).ok_or_else(|| {
                crate::adapter::AdapterError::UnsupportedInstruction(format!(
                    "exact-call authorization references missing LIR function {}",
                    authorization.lir_function
                ))
            })?;
            let source_caller = catalog
                .unique(module, authorization.caller)
                .filter(|function| function.name == lir_caller.name)
                .ok_or_else(|| {
                    crate::adapter::AdapterError::UnsupportedInstruction(format!(
                        "exact-call authorization caller FuncId({}) no longer names LIR function {:?}",
                        authorization.caller.index(),
                        lir_caller.name
                    ))
                })?;
            if source_caller.blocks.is_empty() {
                return Err(crate::adapter::AdapterError::UnsupportedInstruction(
                    format!(
                        "exact-call authorization caller `{}` has no body",
                        source_caller.name
                    ),
                ));
            }

            let block = lir_caller.blocks.get(&authorization.block).ok_or_else(|| {
                crate::adapter::AdapterError::UnsupportedInstruction(format!(
                    "exact-call authorization for `{}` references missing LIR block {:?}",
                    lir_caller.name, authorization.block
                ))
            })?;
            let instruction = block
                .instructions
                .get(authorization.instruction)
                .ok_or_else(|| {
                    crate::adapter::AdapterError::UnsupportedInstruction(format!(
                        "exact-call authorization for `{}` references missing LIR block {:?} instruction {}",
                        lir_caller.name,
                        authorization.block,
                        authorization.instruction
                    ))
                })?;
            if lir_caller
                .trust_ir_origins
                .get(&authorization.block)
                .and_then(|origins| origins.get(authorization.instruction))
                .copied()
                .flatten()
                != Some(authorization.source_origin)
            {
                return Err(crate::adapter::AdapterError::UnsupportedInstruction(
                    format!(
                        "exact-call authorization caller `{}` has changed source-edge provenance",
                        lir_caller.name
                    ),
                ));
            }
            let (name, target_id) = match &instruction.opcode {
                Opcode::Call {
                    name,
                    binding: DirectCallBinding::ExactModuleFunction { function },
                }
                | Opcode::Invoke {
                    name,
                    binding: DirectCallBinding::ExactModuleFunction { function },
                    ..
                }
                | Opcode::FunctionAddr { name, function } => (name, FuncId::new(*function)),
                opcode => {
                    return Err(crate::adapter::AdapterError::UnsupportedInstruction(
                        format!(
                            "exact-call authorization for `{}` was replaced by {opcode:?}",
                            lir_caller.name
                        ),
                    ));
                }
            };
            if target_id != authorization.target {
                return Err(crate::adapter::AdapterError::UnsupportedInstruction(
                    format!(
                        "exact-call authorization target FuncId({}) was rewritten to FuncId({})",
                        authorization.target.index(),
                        target_id.index()
                    ),
                ));
            }
            let target = catalog
                .unique(module, target_id)
                .filter(|target| {
                    is_module_local_function_definition(target) && target.name == *name
                })
                .ok_or_else(|| {
                    crate::adapter::AdapterError::UnsupportedInstruction(format!(
                        "exact-call authorization for FuncId({}) / {name:?} no longer names one bodied Internal/Private module function",
                        target_id.index()
                    ))
            })?;
            debug_assert_eq!(target.id, authorization.target);

            let caller_context = match caller_context {
                Some((lir_function, digest)) if lir_function == authorization.lir_function => {
                    digest
                }
                _ => {
                    let digest = exact_call_context_digest(authorization.caller, lir_caller)?;
                    caller_context = Some((authorization.lir_function, digest));
                    digest
                }
            };
            let replay_digest = exact_call_edge_digest(
                caller_context,
                lir_caller,
                authorization.block,
                authorization.instruction,
                instruction,
                &mut edge_bytes,
            )?;
            if replay_digest != authorization.edge_digest {
                return Err(crate::adapter::AdapterError::UnsupportedInstruction(
                    format!(
                        "exact-call authorization for `{}` has changed signature, location, operands, results, type metadata, name, or binding",
                        lir_caller.name
                    ),
                ));
            }
        }
        Ok(())
    }

    /// Replay every authorization after proving that it exhausts the completed
    /// LIR's exact-module-call carriers.
    ///
    /// The compatibility compiler deliberately keeps [`Self::replay_exact_module_calls`]
    /// sparse and O(1) when exact calls are dormant. Core admission instead
    /// pays one final linear LIR walk: an unreported carrier must never acquire
    /// closed-image authority merely because its public enum variant was set.
    /// The historical method name also covers `FunctionAddr` carriers.
    pub fn replay_exact_module_calls_exhaustive(
        &self,
        functions: &[(LirFunction, crate::adapter::ProofContext)],
    ) -> Result<(), crate::adapter::AdapterError> {
        let carrier_count = functions
            .iter()
            .flat_map(|(function, _)| function.blocks.values())
            .flat_map(|block| block.instructions.iter())
            .filter(|instruction| {
                matches!(
                    instruction.opcode,
                    Opcode::Call {
                        binding: DirectCallBinding::ExactModuleFunction { .. },
                        ..
                    } | Opcode::Invoke {
                        binding: DirectCallBinding::ExactModuleFunction { .. },
                        ..
                    } | Opcode::FunctionAddr { .. }
                )
            })
            .count();

        if carrier_count != self.exact_module_calls.len() {
            return Err(crate::adapter::AdapterError::UnsupportedInstruction(
                format!(
                    "completed LIR contains {carrier_count} exact-module-call carrier(s), but lowering authorized {}",
                    self.exact_module_calls.len()
                ),
            ));
        }

        self.replay_exact_module_calls(functions)
    }

    /// Replay and exhaustively account for every strict call-identity carrier
    /// against the exact caller-owned TrustIR module.
    ///
    /// The mandatory walk counts exact-local and pending-import carriers
    /// together, avoiding two whole-LIR scans in Core admission, and rejects
    /// every prematurely bound native dependency. Imported-call replay
    /// authenticates the source `FuncId` and edge provenance; it does not
    /// select a runtime catalog entry, symbol address, or provider.
    pub fn replay_strict_call_bindings_exhaustive(
        &self,
        functions: &[(LirFunction, crate::adapter::ProofContext)],
    ) -> Result<(), crate::adapter::AdapterError> {
        let (exact_carrier_count, carrier_count, native_dependency_count) = functions
            .iter()
            .flat_map(|(function, _)| function.blocks.values())
            .flat_map(|block| block.instructions.iter())
            .fold(
                (0usize, 0usize, 0usize),
                |counts, instruction| match instruction.opcode {
                    Opcode::Call {
                        binding: DirectCallBinding::ExactModuleFunction { .. },
                        ..
                    }
                    | Opcode::Invoke {
                        binding: DirectCallBinding::ExactModuleFunction { .. },
                        ..
                    }
                    | Opcode::FunctionAddr { .. } => (counts.0 + 1, counts.1, counts.2),
                    Opcode::Call {
                        binding: DirectCallBinding::DeclaredExternalFunction { .. },
                        ..
                    }
                    | Opcode::Invoke {
                        binding: DirectCallBinding::DeclaredExternalFunction { .. },
                        ..
                    } => (counts.0, counts.1 + 1, counts.2),
                    Opcode::Call {
                        binding: DirectCallBinding::NativeDependency { .. },
                        ..
                    }
                    | Opcode::Invoke {
                        binding: DirectCallBinding::NativeDependency { .. },
                        ..
                    } => (counts.0, counts.1, counts.2 + 1),
                    _ => counts,
                },
            );
        if native_dependency_count != 0 {
            return Err(crate::adapter::AdapterError::UnsupportedInstruction(
                format!(
                    "completed strict LIR contains {native_dependency_count} prematurely bound native-dependency call carrier(s)"
                ),
            ));
        }
        if exact_carrier_count != self.exact_module_calls.len() {
            return Err(crate::adapter::AdapterError::UnsupportedInstruction(
                format!(
                    "completed LIR contains {exact_carrier_count} exact-module-call carrier(s), but lowering authorized {}",
                    self.exact_module_calls.len()
                ),
            ));
        }
        if carrier_count != self.declared_external_calls.len() {
            return Err(crate::adapter::AdapterError::UnsupportedInstruction(
                format!(
                    "completed LIR contains {carrier_count} declared-external-call carrier(s), but lowering authorized {}",
                    self.declared_external_calls.len()
                ),
            ));
        }
        self.replay_exact_module_calls(functions)?;
        if self.declared_external_calls.is_empty() {
            return Ok(());
        }

        let module = self.module;
        let catalog = ModuleFunctionCatalog::new(module);
        if let Some(id) = catalog.first_ambiguous_id() {
            return Err(crate::adapter::AdapterError::UnsupportedInstruction(
                format!(
                    "cannot replay declared external calls against ambiguous FuncId({})",
                    id.index()
                ),
            ));
        }
        if let Some(name) = catalog.first_ambiguous_symbol() {
            return Err(crate::adapter::AdapterError::UnsupportedInstruction(
                format!(
                    "cannot replay declared external calls against ambiguous module symbol {name:?}"
                ),
            ));
        }

        let mut caller_context = None;
        let mut edge_bytes = Vec::new();
        for authorization in &self.declared_external_calls {
            let (lir_caller, _) = functions.get(authorization.lir_function).ok_or_else(|| {
                crate::adapter::AdapterError::UnsupportedInstruction(format!(
                    "declared-external-call authorization references missing LIR function {}",
                    authorization.lir_function
                ))
            })?;
            let source_caller = catalog
                .unique(module, authorization.caller)
                .filter(|function| function.name == lir_caller.name && !function.blocks.is_empty())
                .ok_or_else(|| {
                    crate::adapter::AdapterError::UnsupportedInstruction(format!(
                        "declared-external-call caller FuncId({}) no longer names bodied LIR function {:?}",
                        authorization.caller.index(),
                        lir_caller.name
                    ))
                })?;
            debug_assert!(!source_caller.blocks.is_empty());

            let block = lir_caller.blocks.get(&authorization.block).ok_or_else(|| {
                crate::adapter::AdapterError::UnsupportedInstruction(format!(
                    "declared-external-call authorization for `{}` references missing LIR block {:?}",
                    lir_caller.name, authorization.block
                ))
            })?;
            let instruction = block
                .instructions
                .get(authorization.instruction)
                .ok_or_else(|| {
                    crate::adapter::AdapterError::UnsupportedInstruction(format!(
                        "declared-external-call authorization for `{}` references missing LIR block {:?} instruction {}",
                        lir_caller.name,
                        authorization.block,
                        authorization.instruction
                    ))
                })?;
            if lir_caller
                .trust_ir_origins
                .get(&authorization.block)
                .and_then(|origins| origins.get(authorization.instruction))
                .copied()
                .flatten()
                != Some(authorization.source_origin)
            {
                return Err(crate::adapter::AdapterError::UnsupportedInstruction(
                    format!(
                        "declared-external-call caller `{}` has changed source-edge provenance",
                        lir_caller.name
                    ),
                ));
            }
            let (name, target_id) = match &instruction.opcode {
                Opcode::Call {
                    name,
                    binding: DirectCallBinding::DeclaredExternalFunction { function },
                }
                | Opcode::Invoke {
                    name,
                    binding: DirectCallBinding::DeclaredExternalFunction { function },
                    ..
                } => (name, FuncId::new(*function)),
                opcode => {
                    return Err(crate::adapter::AdapterError::UnsupportedInstruction(
                        format!(
                            "declared-external-call authorization for `{}` was replaced by {opcode:?}",
                            lir_caller.name
                        ),
                    ));
                }
            };
            if target_id != authorization.target {
                return Err(crate::adapter::AdapterError::UnsupportedInstruction(
                    format!(
                        "declared-external-call target FuncId({}) was rewritten to FuncId({})",
                        authorization.target.index(),
                        target_id.index()
                    ),
                ));
            }
            let target = catalog
                .unique(module, target_id)
                .filter(|target| {
                    target.blocks.is_empty()
                        && target.linkage == Linkage::External
                        && target.name == *name
                })
                .ok_or_else(|| {
                    crate::adapter::AdapterError::UnsupportedInstruction(format!(
                        "declared-external-call authorization for FuncId({}) / {name:?} no longer names one bodyless External declaration",
                        target_id.index()
                    ))
                })?;
            debug_assert_eq!(target.id, authorization.target);

            let caller_context = match caller_context {
                Some((lir_function, digest)) if lir_function == authorization.lir_function => {
                    digest
                }
                _ => {
                    let digest = exact_call_context_digest(authorization.caller, lir_caller)?;
                    caller_context = Some((authorization.lir_function, digest));
                    digest
                }
            };
            let replay_digest = exact_call_edge_digest(
                caller_context,
                lir_caller,
                authorization.block,
                authorization.instruction,
                instruction,
                &mut edge_bytes,
            )?;
            if replay_digest != authorization.edge_digest {
                return Err(crate::adapter::AdapterError::UnsupportedInstruction(
                    format!(
                        "declared-external-call authorization for `{}` has changed signature, location, operands, results, type metadata, name, or binding",
                        lir_caller.name
                    ),
                ));
            }
        }
        Ok(())
    }

    /// Number of sparse exact-call authorizations, for diagnostics only.
    pub fn exact_module_call_count(&self) -> usize {
        self.exact_module_calls.len() - self.exact_module_addresses
    }

    /// Number of sparse exact function-address bindings, for diagnostics only.
    pub fn exact_module_address_count(&self) -> usize {
        self.exact_module_addresses
    }

    /// Number of exhaustively authenticated pending imported calls.
    pub fn declared_external_call_count(&self) -> usize {
        self.declared_external_calls.len()
    }
}

fn exact_call_context_digest(
    caller: FuncId,
    function: &LirFunction,
) -> Result<trust_ir::proof::ProofDigest, AdapterError> {
    let mut bytes = Vec::new();
    bytes.extend_from_slice(&caller.index().to_be_bytes());
    push_bytes(&mut bytes, function.name.as_bytes())?;
    push_types(&mut bytes, &function.signature.params)?;
    push_types(&mut bytes, &function.signature.returns)?;
    Ok(trust_ir::proof::ProofDigest::sha256_domain(
        "trust-cg-lower.exact-call-context.v1",
        &bytes,
    ))
}

fn exact_call_edge_digest(
    caller_context: trust_ir::proof::ProofDigest,
    function: &LirFunction,
    block_id: Block,
    instruction_index: usize,
    instruction: &crate::instructions::Instruction,
    bytes: &mut Vec<u8>,
) -> Result<trust_ir::proof::ProofDigest, AdapterError> {
    bytes.clear();
    bytes.extend_from_slice(&caller_context.bytes);
    bytes.extend_from_slice(&block_id.0.to_be_bytes());
    push_u64(bytes, instruction_index)?;

    let source_origin = function
        .trust_ir_origins
        .get(&block_id)
        .and_then(|origins| origins.get(instruction_index))
        .copied()
        .flatten();
    match source_origin {
        Some(origin) => {
            bytes.push(1);
            bytes.extend_from_slice(&origin.0.to_be_bytes());
        }
        None => bytes.push(0),
    }

    let source_loc = function
        .blocks
        .get(&block_id)
        .and_then(|block| block.source_locs.get(instruction_index))
        .copied()
        .flatten();
    match source_loc {
        Some(source_loc) => {
            bytes.push(1);
            bytes.extend_from_slice(&source_loc.file.to_be_bytes());
            bytes.extend_from_slice(&source_loc.line.to_be_bytes());
            bytes.extend_from_slice(&source_loc.col.to_be_bytes());
        }
        None => bytes.push(0),
    }

    match &instruction.opcode {
        Opcode::FunctionAddr { name, function } => {
            bytes.push(2);
            push_bytes(bytes, name.as_bytes())?;
            bytes.extend_from_slice(&function.to_be_bytes());
        }
        Opcode::Call { name, binding } | Opcode::Invoke { name, binding, .. } => {
            if let Opcode::Invoke {
                normal_dest,
                unwind_dest,
                ..
            } = instruction.opcode
            {
                bytes.push(3);
                bytes.extend_from_slice(&normal_dest.0.to_be_bytes());
                bytes.extend_from_slice(&unwind_dest.0.to_be_bytes());
            } else {
                bytes.push(1);
            }
            push_bytes(bytes, name.as_bytes())?;
            match binding {
                DirectCallBinding::Interposable => bytes.push(0),
                DirectCallBinding::ExactModuleFunction { function } => {
                    bytes.push(1);
                    bytes.extend_from_slice(&function.to_be_bytes());
                }
                DirectCallBinding::DeclaredExternalFunction { function } => {
                    bytes.push(2);
                    bytes.extend_from_slice(&function.to_be_bytes());
                }
                DirectCallBinding::NativeDependency {
                    function,
                    dependency,
                } => {
                    bytes.push(3);
                    bytes.extend_from_slice(&function.to_be_bytes());
                    bytes.extend_from_slice(&dependency.index().to_be_bytes());
                }
            }
        }
        _ => bytes.push(0),
    }
    push_values_and_types(bytes, &instruction.args, function)?;
    push_values_and_types(bytes, &instruction.results, function)?;

    Ok(trust_ir::proof::ProofDigest::sha256_domain(
        "trust-cg-lower.exact-call-edge.v1",
        bytes,
    ))
}

fn push_values_and_types(
    bytes: &mut Vec<u8>,
    values: &[crate::instructions::Value],
    function: &LirFunction,
) -> Result<(), AdapterError> {
    push_u64(bytes, values.len())?;
    for value in values {
        bytes.extend_from_slice(&value.0.to_be_bytes());
        match function.value_types.get(value) {
            Some(ty) => {
                bytes.push(1);
                push_type(bytes, ty)?;
            }
            None => bytes.push(0),
        }
    }
    Ok(())
}

fn push_types(bytes: &mut Vec<u8>, types: &[Type]) -> Result<(), AdapterError> {
    push_u64(bytes, types.len())?;
    for ty in types {
        push_type(bytes, ty)?;
    }
    Ok(())
}

fn push_type(bytes: &mut Vec<u8>, ty: &Type) -> Result<(), AdapterError> {
    match ty {
        Type::I8 => bytes.push(0),
        Type::I16 => bytes.push(1),
        Type::I32 => bytes.push(2),
        Type::I64 => bytes.push(3),
        Type::I128 => bytes.push(4),
        Type::F16 => bytes.push(5),
        Type::F32 => bytes.push(6),
        Type::F64 => bytes.push(7),
        Type::B1 => bytes.push(8),
        Type::V128 => bytes.push(9),
        Type::V64 => bytes.push(10),
        Type::Struct(fields) => {
            bytes.push(11);
            push_types(bytes, fields)?;
        }
        Type::Array(element, count) => {
            bytes.push(12);
            bytes.extend_from_slice(&count.to_be_bytes());
            push_type(bytes, element)?;
        }
        Type::Enum {
            tag_width,
            variants,
        } => {
            bytes.push(13);
            bytes.push(match tag_width {
                trust_cg_ir::function::EnumTagWidth::U8 => 0,
                trust_cg_ir::function::EnumTagWidth::U16 => 1,
                trust_cg_ir::function::EnumTagWidth::U32 => 2,
                trust_cg_ir::function::EnumTagWidth::U64 => 3,
            });
            push_u64(bytes, variants.len())?;
            for fields in variants {
                push_types(bytes, fields)?;
            }
        }
    }
    Ok(())
}

fn push_bytes(bytes: &mut Vec<u8>, value: &[u8]) -> Result<(), AdapterError> {
    push_u64(bytes, value.len())?;
    bytes.extend_from_slice(value);
    Ok(())
}

fn push_u64(bytes: &mut Vec<u8>, value: usize) -> Result<(), AdapterError> {
    let value = u64::try_from(value).map_err(|_| {
        AdapterError::UnsupportedInstruction(
            "LIR collection length exceeds canonical u64 framing".into(),
        )
    })?;
    bytes.extend_from_slice(&value.to_be_bytes());
    Ok(())
}

/// Census for adapter-fused static indirect-call devirtualization.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct StaticCallDevirtualizationStats {
    /// Number of `CallIndirect` nodes inspected.
    pub indirect_calls_seen: usize,
    /// Number whose dominance-safe callee provenance resolved exactly.
    pub resolved_static_targets: usize,
    /// Number lowered as named direct LIR calls after all checks passed.
    pub devirtualized_calls: usize,
    /// Compatible exact targets retained indirect because the caller selected
    /// the diagnostic-only legacy API and received no sealed validation report.
    pub authorization_withheld_calls: usize,
    /// Number left indirect because callee provenance remained dynamic.
    pub unresolved_callees: usize,
    /// Dynamic producer shapes rejected by the existing adapter index before
    /// constructing the authoritative provenance analysis.
    pub prefilter_rejections: usize,
    /// Existing producer-index probes issued by the constant-bounded
    /// rejection-only prefilter, including a final unsuccessful lookup.
    pub prefilter_producer_probes: usize,
    /// Number left indirect because a resolved edge was not exactly compatible.
    pub incompatible_calls: usize,
    /// Zero-scan function-local analysis shells constructed lazily.
    pub provenance_analyses_built: usize,
    /// TrustIR exact-use indices initialized by traced queries.
    pub use_site_indices_built: usize,
    /// TrustIR SSA-definition indices initialized by traced queries.
    pub definition_indices_built: usize,
    /// TrustIR sparse provenance-summary indices initialized by traced queries.
    pub provenance_indices_built: usize,
    /// TrustIR dominator trees initialized by traced queries.
    pub dominator_trees_built: usize,
    /// Blocks scanned while initializing TrustIR exact-use indices.
    pub use_site_blocks_indexed: usize,
    /// Block parameters scanned while initializing TrustIR exact-use indices.
    pub use_site_parameters_indexed: usize,
    /// Instructions visited by TrustIR's constant-bounded local prefilter.
    pub trust_ir_prefilter_instructions_visited: usize,
    /// SSA operands visited while authenticating exact consuming nodes.
    pub exact_use_operands_visited: usize,
    /// Blocks scanned while initializing TrustIR SSA-definition indices.
    pub definition_blocks_indexed: usize,
    /// Instructions scanned while initializing TrustIR SSA-definition indices.
    pub definition_instructions_indexed: usize,
    /// SSA declarations recorded while initializing TrustIR definition indices.
    pub definition_values_indexed: usize,
    /// Definition entries examined while building sparse provenance summaries.
    pub provenance_definitions_visited: usize,
    /// Copy/Reify links validated while building provenance summaries.
    pub provenance_links_validated: usize,
    /// Candidate-chain rows retained in sparse provenance indices.
    pub provenance_entries_stored: usize,
    /// Blocks scanned while initializing TrustIR dominance.
    pub dominator_blocks_indexed: usize,
    /// Instructions scanned while initializing TrustIR dominance.
    pub dominator_instructions_indexed: usize,
    /// CFG successor edges recorded while initializing TrustIR dominance.
    pub dominator_edges_indexed: usize,
    /// Memoized provenance summaries looked up by exact-use queries.
    pub provenance_summary_lookups: usize,
    /// Top-definition-to-use dominance checks performed by exact-use queries.
    pub exact_use_dominance_checks: usize,
    /// Synthetic direct-call nodes constructed after every proof check passed.
    pub synthetic_direct_nodes_built: usize,
}

impl StaticCallDevirtualizationStats {
    pub(crate) fn record_trust_ir_query(
        &mut self,
        before: StaticFunctionPointerCacheState,
        after: StaticFunctionPointerCacheState,
        census: StaticFunctionPointerQueryCensus,
    ) {
        self.use_site_indices_built +=
            (!before.use_site_index_built && after.use_site_index_built) as usize;
        self.definition_indices_built +=
            (!before.definition_index_built && after.definition_index_built) as usize;
        self.provenance_indices_built +=
            (!before.provenance_index_built && after.provenance_index_built) as usize;
        self.dominator_trees_built +=
            (!before.dominator_tree_built && after.dominator_tree_built) as usize;
        self.use_site_blocks_indexed += census.use_site_blocks_indexed;
        self.use_site_parameters_indexed += census.use_site_parameters_indexed;
        self.trust_ir_prefilter_instructions_visited += census.prefilter_instructions_visited;
        self.exact_use_operands_visited += census.exact_use_operands_visited;
        self.definition_blocks_indexed += census.definition_blocks_indexed;
        self.definition_instructions_indexed += census.definition_instructions_indexed;
        self.definition_values_indexed += census.definition_values_indexed;
        self.provenance_definitions_visited += census.provenance_definitions_visited;
        self.provenance_links_validated += census.provenance_links_validated;
        self.provenance_entries_stored += census.provenance_entries_stored;
        self.dominator_blocks_indexed += census.dominator_blocks_indexed;
        self.dominator_instructions_indexed += census.dominator_instructions_indexed;
        self.dominator_edges_indexed += census.dominator_edges_indexed;
        self.provenance_summary_lookups += census.provenance_summary_lookups;
        self.exact_use_dominance_checks += census.exact_use_dominance_checks;
    }

    /// Stable detail used by compiler traces for object and JIT compilation.
    pub fn trace_detail(self) -> String {
        format!(
            "{} indirect calls seen, {} static calls devirtualized, {} dynamic calls retained, {} incompatible static calls retained, {} compatible calls retained without exact-call authority",
            self.indirect_calls_seen,
            self.devirtualized_calls,
            self.unresolved_callees,
            self.incompatible_calls,
            self.authorization_withheld_calls,
        )
    }
}

#[derive(Debug, Clone)]
enum FunctionTargetState {
    Unique { index: Option<usize>, name: String },
    Ambiguous,
}

/// One exact function-identity and name catalog shared by every adapter.
///
/// Module translation already needs a `FuncId`-to-name census. Recording the
/// exact vector index in that same hash-table entry avoids both a second map
/// and the former O(functions) scan at every direct call, invoke, function
/// constant, and recovered indirect call. Name-only construction exists for
/// isolated adapter tests; exact lookup then falls back to a uniqueness scan.
pub(crate) struct ModuleFunctionCatalog {
    targets: HashMap<FuncId, FunctionTargetState>,
    default_eh_personality: &'static str,
    first_ambiguous_id: Option<FuncId>,
    first_ambiguous_symbol: Option<String>,
    /// Why the first ambiguous symbol is ambiguous, in the caller's words.
    ///
    /// "Only compatible bodyless External declarations may share a symbol" says
    /// the RULE; it does not say which of the two clauses this pair broke, and
    /// the two have OPPOSITE fixes. Two byte-identical DEFINITIONS of one
    /// non-generic item (`<[_]>::align_to_offsets::gcd`, lowered once per
    /// instantiation of its generic parent — the `library/core`
    /// `[TCG-REGALLOC-063]` adapter root measured 2026-09-14) are a PRODUCER
    /// duplicate to collapse; two definitions that DIFFER under one symbol are
    /// a producer defect that must not be collapsed at all. This records which.
    first_ambiguous_symbol_detail: Option<String>,
}

/// Repeated imports may share a symbol, but not disagree about its contract.
/// Each declaration keeps its original FuncId for source-edge authorization.
/// One line naming WHICH clause of the symbol-sharing rule a pair broke, and the
/// option that would clear it. `previous` is `None` when the earlier claimant
/// was a global rather than a function.
fn ambiguous_symbol_detail(previous: Option<&Function>, current: &Function) -> String {
    let Some(previous) = previous else {
        return "a GLOBAL already claims this symbol; functions and globals share one \
                object/JIT namespace"
            .to_owned();
    };
    let bodied = |f: &Function| !f.blocks.is_empty();
    match (bodied(previous), bodied(current)) {
        (true, true) => {
            // Compare everything a definition means, ignoring only the FuncId:
            // identical bodies under one symbol are a PRODUCER duplicate (one
            // non-generic item lowered once per instantiation of its generic
            // parent), which is collapsible at the producer. Differing bodies
            // under one symbol are a producer DEFECT and must never be
            // collapsed — one of the two would silently win at link time.
            let same_shape = previous.name == current.name
                && previous.ty == current.ty
                && previous.entry == current.entry
                && previous.blocks == current.blocks
                && previous.calling_conv == current.calling_conv
                && previous.linkage == current.linkage
                && previous.attrs == current.attrs;
            if same_shape {
                format!(
                    "two DEFINITIONS with identical bodies (FuncId({}) and FuncId({}), \
                     {} blocks each) claim it; the producer emitted the same item twice \
                     (a non-generic item lowered once per instantiation of its generic \
                     parent does this). Fix at the PRODUCER: lower each symbol once, or \
                     give the copies distinct symbols",
                    previous.id.index(),
                    current.id.index(),
                    current.blocks.len(),
                )
            } else {
                format!(
                    "two DIFFERENT definitions (FuncId({}) with {} blocks and FuncId({}) \
                     with {} blocks) claim it; exactly one would survive linking, so this \
                     cannot be collapsed. Fix at the PRODUCER: the two items need distinct \
                     symbols",
                    previous.id.index(),
                    previous.blocks.len(),
                    current.id.index(),
                    current.blocks.len(),
                )
            }
        }
        (false, false) => format!(
            "two bodyless declarations (FuncId({}) and FuncId({})) disagree about the \
             symbol's contract (linkage, signature, calling convention, visibility, \
             section, retention, or authority/proof/debug metadata), or are not both \
             `external`; repeated imports may share a symbol but not disagree about it",
            previous.id.index(),
            current.id.index(),
        ),
        _ => format!(
            "a DEFINITION and a DECLARATION claim it (FuncId({}) has {} blocks, FuncId({}) \
             has {}); only compatible BODYLESS External declarations may share a symbol",
            previous.id.index(),
            previous.blocks.len(),
            current.id.index(),
            current.blocks.len(),
        ),
    }
}

/// Whether two functions naming one symbol may share it: both are bodyless
/// `External` declarations that agree on everything but their `FuncId` (and
/// a structurally equal signature). The object spells ONE symbol for the
/// name, so any disagreement — a weak beside a strong reference, or two
/// visibilities — has no honest spelling, and the module is refused.
///
/// trust-ir's validator reports `DuplicateFunctionSymbol` for every repeated
/// name, and since WS7.3 every ingestion entry (`crate::admit_module`)
/// refuses that finding before a catalog is built, so an admitted module
/// never reaches this comparison with a repeated name. It remains the only
/// guard on the adapter's diagnostic entries, which take a module without
/// admission: `validate_codegen_prerequisites` does not enforce that finding.
/// The trust-cg-codegen floor row
/// `repeated_declarations_that_disagree_about_visibility_or_linkage_are_refused_on_every_entry`
/// (`tests/aarch64_elf_symbol_binding.rs`) pins the admission refusal of
/// every pair through the text, binary and JSON entries, and this
/// comparison's verdict on every pair through the AArch64 ELF diagnostic
/// entry; the unit tests below vary every compared field.
fn compatible_external_declarations(module: &Module, left: &Function, right: &Function) -> bool {
    if left.linkage != Linkage::External
        || right.linkage != Linkage::External
        || !left.blocks.is_empty()
        || !right.blocks.is_empty()
    {
        return false;
    }
    let (Some(left_ty), Some(right_ty)) = (
        module.func_types.get(left.ty.as_usize()),
        module.func_types.get(right.ty.as_usize()),
    ) else {
        return false;
    };
    // Exhaustive destructuring forces review when TrustIR adds declaration
    // metadata. Only FuncId and the structurally checked FuncTyId may differ;
    // debug/proof metadata is conservatively compared, never merged or dropped.
    // `body_gate` (v41) is AUTHORITY metadata: two declarations that disagree
    // about their codegen license are not the same declaration, and comparing
    // it is what keeps a `None` (no claim) from being merged with an `Ungated`.
    // `display_path` (v41) is claim-style, compared conservatively like the
    // other debug metadata.
    let Function {
        id: _,
        name,
        ty: _,
        entry,
        blocks: _,
        proofs,
        calling_conv,
        linkage: _,
        attrs,
        summary,
        producer,
        value_names,
        scopes,
        source_provenance,
        body_gate,
        display_path,
        // v45 OBJECT-AFFECTING metadata: two declarations that disagree about
        // their section, visibility or retention are not the same declaration.
        // Compared, never merged — the same discipline `body_gate` gets, and
        // for the same reason.
        section,
        visibility,
        retained,
    } = left;
    left_ty == right_ty
        && name == &right.name
        && entry == &right.entry
        && proofs == &right.proofs
        && calling_conv == &right.calling_conv
        && attrs == &right.attrs
        && summary == &right.summary
        && producer == &right.producer
        && value_names == &right.value_names
        && scopes == &right.scopes
        && source_provenance == &right.source_provenance
        && body_gate == &right.body_gate
        && display_path == &right.display_path
        && section == &right.section
        && visibility == &right.visibility
        && retained == &right.retained
}

impl ModuleFunctionCatalog {
    pub(crate) fn new(module: &Module) -> Self {
        Self::new_with_names(module, None)
    }

    pub(crate) fn new_with_names(module: &Module, names: Option<&HashMap<FuncId, String>>) -> Self {
        let mut targets = HashMap::with_capacity(module.functions.len());
        let mut first_ambiguous_id = None;
        for (index, function) in module.functions.iter().enumerate() {
            match targets.entry(function.id) {
                Entry::Vacant(entry) => {
                    entry.insert(FunctionTargetState::Unique {
                        index: Some(index),
                        name: names
                            .and_then(|names| names.get(&function.id))
                            .cloned()
                            .unwrap_or_else(|| function.name.clone()),
                    });
                }
                Entry::Occupied(mut entry) => {
                    entry.insert(FunctionTargetState::Ambiguous);
                    first_ambiguous_id.get_or_insert(function.id);
                }
            }
        }
        // Functions and globals share the object/JIT symbol namespace. Only
        // compatible repeated external declarations may share a name: separate
        // definitions or storage must never overwrite one another downstream.
        // None denotes a global, which cannot alias any function declaration.
        let mut seen_symbols: HashMap<&str, Option<&Function>> =
            HashMap::with_capacity(targets.len() + module.globals.len());
        let mut first_ambiguous_symbol = None;
        let mut first_ambiguous_symbol_detail: Option<String> = None;
        for function in &module.functions {
            let Some(FunctionTargetState::Unique { name, .. }) = targets.get(&function.id) else {
                continue;
            };
            match seen_symbols.entry(name.as_str()) {
                Entry::Vacant(entry) => {
                    entry.insert(Some(function));
                }
                Entry::Occupied(entry) => {
                    if !entry.get().is_some_and(|previous| {
                        compatible_external_declarations(module, previous, function)
                    }) {
                        if first_ambiguous_symbol.is_none() {
                            first_ambiguous_symbol_detail =
                                Some(ambiguous_symbol_detail(*entry.get(), function));
                        }
                        first_ambiguous_symbol.get_or_insert_with(|| name.clone());
                    }
                }
            }
        }
        for global in &module.globals {
            if seen_symbols.insert(global.name.as_str(), None).is_some() {
                if first_ambiguous_symbol.is_none() {
                    first_ambiguous_symbol_detail = Some(
                        "a GLOBAL and a function (or a second global) claim the same symbol; \
                         functions and globals share one object/JIT namespace"
                            .to_owned(),
                    );
                }
                first_ambiguous_symbol.get_or_insert_with(|| global.name.clone());
            }
        }
        let default_eh_personality = crate::adapter::eh_personality_for_function_names(
            targets.values().filter_map(|target| match target {
                FunctionTargetState::Unique { name, .. } => Some(name.as_str()),
                FunctionTargetState::Ambiguous => None,
            }),
        );
        Self {
            targets,
            default_eh_personality,
            first_ambiguous_id,
            first_ambiguous_symbol,
            first_ambiguous_symbol_detail,
        }
    }

    #[cfg(test)]
    pub(crate) fn from_names(names: HashMap<FuncId, String>) -> Self {
        let default_eh_personality =
            crate::adapter::eh_personality_for_function_names(names.values().map(String::as_str));
        Self {
            default_eh_personality,
            targets: names
                .into_iter()
                .map(|(id, name)| (id, FunctionTargetState::Unique { index: None, name }))
                .collect(),
            first_ambiguous_id: None,
            first_ambiguous_symbol: None,
            first_ambiguous_symbol_detail: None,
        }
    }

    pub(crate) fn first_ambiguous_id(&self) -> Option<FuncId> {
        self.first_ambiguous_id
    }

    pub(crate) fn first_ambiguous_symbol(&self) -> Option<&str> {
        self.first_ambiguous_symbol.as_deref()
    }

    /// Which clause of the sharing rule the first ambiguous symbol broke, and
    /// what the producer-side fix would be. See the field's doc.
    pub(crate) fn first_ambiguous_symbol_detail(&self) -> Option<&str> {
        self.first_ambiguous_symbol_detail.as_deref()
    }

    pub(crate) fn unique<'module>(
        &self,
        module: &'module Module,
        target: FuncId,
    ) -> Option<&'module Function> {
        let FunctionTargetState::Unique { index, .. } = self.targets.get(&target)? else {
            return None;
        };
        if let Some(index) = index {
            return module
                .functions
                .get(*index)
                .filter(|function| function.id == target);
        }

        let mut matches = module
            .functions
            .iter()
            .filter(|function| function.id == target);
        let function = matches.next()?;
        matches.next().is_none().then_some(function)
    }

    pub(crate) fn name(&self, target: FuncId) -> Option<&str> {
        match self.targets.get(&target)? {
            FunctionTargetState::Unique { name, .. } => Some(name),
            FunctionTargetState::Ambiguous => None,
        }
    }

    /// Derived once from this catalog's exact, unambiguous lowered names.
    /// Per-function producer overrides remain the adapter's responsibility.
    pub(crate) fn default_eh_personality(&self) -> &'static str {
        self.default_eh_personality
    }
}

/// Source identities whose object/JIT binding depends on one exact module.
///
/// This census is deliberately broader than static-call devirtualization.  A
/// function pointer can escape, feed a dynamically selected call, or fail an
/// edge-compatibility check and still materialize the address of a
/// non-interposable module definition.  Likewise, direct `Call`/`Invoke`
/// edges retain that definition's identity even when their eventual LIR
/// carrier is not an ordinary fixed-arity call.  Consumers that cannot keep
/// those identities local must therefore fail closed on the source census,
/// not infer safety from the subset of calls that happened to devirtualize.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct ModuleLocalFunctionIdentityCensus {
    /// Direct `Call`/`Invoke` edges to unique bodied Internal/Private targets.
    pub direct_edges: usize,
    /// Materialized `FnDef` or capture-free `Closure` identities naming such targets.
    pub materialized_identities: usize,
    /// `SymbolAddr` constants whose string names such a target (in a body or
    /// a global initializer, nested ones included). The string carries no
    /// `FuncId`, but every object writer resolves it through the object's
    /// own symbol of that name, the module-local definition, so the address
    /// it materializes is that definition's exactly when the object binds
    /// the definition locally: an object path that cannot keep module-local
    /// references local must refuse it as it refuses a `FnDef`
    /// (`Compiler::compile`'s census refusals).
    pub symbol_addresses: usize,
}

impl ModuleLocalFunctionIdentityCensus {
    /// Whether this module contains any `FuncId`-carried local identity: a
    /// direct edge or a materialized identity. String-named
    /// [`Self::symbol_addresses`] are not counted here: an identity that
    /// must not cross an adapter-owned module clone, or that closed-JIT Core
    /// admission refuses, is a `FuncId`, which a string does not carry. An
    /// object path's binding admission reads every field.
    pub const fn is_empty(self) -> bool {
        self.direct_edges == 0 && self.materialized_identities == 0
    }
}

/// Whether `function` is a module-local definition: a bodied `Internal` or
/// `Private` function (trust-ir's proved `Linkage::is_module_local`), whose
/// identity no other object may supply or replace.
///
/// This is the one classification the identity census counts references to
/// and the AArch64 ELF post-emission binding check reads its symbols from.
/// It agrees with [`crate::DefinitionBinding::for_trust_ir_linkage`] returning
/// `Local` for a definition (the codegen drift test pins that agreement).
#[must_use]
pub fn is_module_local_function_definition(function: &Function) -> bool {
    !function.blocks.is_empty() && function.linkage.is_module_local()
}

/// Whether `global` is module-local data: an `Internal` or `Private` global
/// (trust-ir's proved `Linkage::is_module_local`), which the object binds
/// `STB_LOCAL`, so a reference the same object makes by its name reaches it.
///
/// This is the one classification the compiler's and the adapter's
/// refusals of data named like a backend symbol read. It agrees with the
/// compiler's object-global mapping binding the global neither external nor
/// imported (the codegen drift test pins that agreement).
#[must_use]
pub fn is_module_local_data_definition(global: &trust_ir::Global) -> bool {
    global.linkage.is_module_local()
}

/// Why a closure value's code identity is not statically visible at a use.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ClosureIdentityBlock {
    /// The walk reached a value with no producer: a function or block
    /// parameter (or a malformed use of an undefined value).
    Parameter { at: ValueId },
    /// The exact incoming block arguments disagree on code identity or type.
    Incoming { at: ValueId },
    /// The walk reached a producer that does not preserve a closure literal's
    /// code identity (`ExtractField`, `Call`, `Load`, or a differing-code `Select`).
    Producer { at: ValueId, inst: &'static str },
    /// The producer graph is cyclic or exceeds the bounded walk.
    Exhausted,
}

/// Bound on distinct register-level producers visited by a closure identity walk.
const CLOSURE_IDENTITY_WALK_LIMIT: usize = 4096;

/// Incoming closure values of non-entry block parameters in one exact function.
/// Built lazily by consumers and shared across their application queries.
/// Incoming arguments must be available at their exact predecessor terminator.
/// Complete source validation remains separate: this is provenance discovery,
/// not a whole-function SSA validator or permission to call dynamic code.
#[derive(Default)]
pub(crate) struct ClosureBlockParameterSources {
    incoming: HashMap<ValueId, (Ty, Vec<ValueId>)>,
}

impl ClosureBlockParameterSources {
    pub(crate) fn new(function: &Function) -> Option<Self> {
        let mut blocks = HashMap::new();
        let mut values = HashMap::new();
        let mut incoming = HashMap::new();
        for block in &function.blocks {
            if blocks.insert(block.id, block).is_some() {
                return None;
            }
            for (value, ty) in &block.params {
                if values
                    .insert(
                        *value,
                        trust_ir::analysis::SsaDefinitionSite {
                            block: block.id,
                            instruction: None,
                        },
                    )
                    .is_some()
                {
                    return None;
                }
                if block.id != function.entry && matches!(ty, Ty::Closure(_)) {
                    incoming.insert(*value, (ty.clone(), Vec::new()));
                }
            }
            for (instruction, node) in block.body.iter().enumerate() {
                if matches!(
                    node.inst,
                    trust_ir::Inst::Const { .. }
                        | trust_ir::Inst::MakeClosure { .. }
                        | trust_ir::Inst::Copy { .. }
                        | trust_ir::Inst::InsertField { .. }
                        | trust_ir::Inst::Select { .. }
                ) && node.results.len() != 1
                {
                    return None;
                }
                for result in &node.results {
                    if values
                        .insert(
                            *result,
                            trust_ir::analysis::SsaDefinitionSite {
                                block: block.id,
                                instruction: Some(instruction),
                            },
                        )
                        .is_some()
                    {
                        return None;
                    }
                }
            }
        }
        if !blocks.contains_key(&function.entry) {
            return None;
        }
        let dominators = trust_ir::analysis::DominatorTree::new(function);
        if !dominators.is_well_formed() {
            return None;
        }
        let mut edge_values = 0usize;
        for block in &function.blocks {
            let (last, earlier) = block.body.split_last()?;
            if !last.inst.is_terminator() || earlier.iter().any(|node| node.inst.is_terminator()) {
                return None;
            }
            for edge in last.inst.successor_edges() {
                let target = blocks.get(&edge.target)?;
                if edge.kind != trust_ir::inst::EdgeKind::Normal
                    || edge.args.len() != target.params.len()
                {
                    return None;
                }
                for (actual, (parameter, _)) in edge.args.iter().zip(&target.params) {
                    if !values.contains_key(actual) {
                        return None;
                    }
                    if let Some((_, sources)) = incoming.get_mut(parameter) {
                        if !dominators.definition_available_at(
                            *values.get(actual)?,
                            trust_ir::analysis::SsaUseSite::BeforeInstruction {
                                block: block.id,
                                instruction: block.body.len() - 1,
                            },
                        ) {
                            return None;
                        }
                        edge_values = edge_values.checked_add(1)?;
                        if edge_values > CLOSURE_IDENTITY_WALK_LIMIT {
                            return None;
                        }
                        sources.push(*actual);
                    }
                }
            }
        }
        Some(Self { incoming })
    }

    pub(crate) fn get(&self, value: ValueId) -> Option<(&Ty, &[ValueId])> {
        let (ty, incoming) = self.incoming.get(&value)?;
        (!incoming.is_empty()).then_some((ty, incoming.as_slice()))
    }
}

/// Resolve a closure's code identity without changing its runtime environment.
/// `Copy` and closure `InsertField` retain that identity. A closure `Select`
/// retains it only when BOTH arms name the same function and closure type;
/// lowering still extracts the captures from the selected value itself.
///
/// Non-entry block parameters retain it only when every incoming argument
/// resolves to the same typed code. Entry parameters, cycles, projections,
/// calls, loads and differing-code selects remain unsupported: the closure
/// environment has no runtime code pointer. The
/// adapter and AOT binding census use this same bounded, stack-safe DAG walk.
/// Memoization prevents repeated select arms from expanding exponentially;
/// cycles and an exhausted node budget refuse rather than guessing a target.
#[cfg(test)]
fn resolve_closure_literal<'a>(
    producer: impl Fn(ValueId) -> Option<&'a trust_ir::InstrNode>,
    incoming: impl Fn(ValueId) -> Option<(&'a Ty, &'a [ValueId])>,
    value: ValueId,
) -> Result<(FuncId, Ty), ClosureIdentityBlock> {
    resolve_closure_identity(producer, incoming, |_| None, value)
}

/// The same bounded walk, with an optional checked target for a loaded
/// capture-only frame. The caller must obtain that target from the exact
/// immutable module's shared closure storage binding, never from its bytes.
pub(crate) fn resolve_closure_identity<'a>(
    producer: impl Fn(ValueId) -> Option<&'a trust_ir::InstrNode>,
    incoming: impl Fn(ValueId) -> Option<(&'a Ty, &'a [ValueId])>,
    storage: impl Fn(trust_ir::ClosureTyId) -> Option<FuncId>,
    value: ValueId,
) -> Result<(FuncId, Ty), ClosureIdentityBlock> {
    enum Frame {
        Enter(ValueId),
        Forward(ValueId, ValueId, Ty, &'static str),
        BlockParameter(ValueId, Vec<ValueId>, Ty),
        Select(ValueId, ValueId, ValueId, Ty),
    }
    // None marks an active node. Re-entering it is a malformed cyclic
    // producer graph, never a fixed-point proof of a closure identity.
    let mut identities: HashMap<ValueId, Option<(FuncId, Ty)>> = HashMap::new();
    let mut pending = vec![Frame::Enter(value)];
    let mut visited = 0;
    while let Some(frame) = pending.pop() {
        match frame {
            Frame::Enter(current) => {
                if let Some(identity) = identities.get(&current) {
                    if identity.is_none() {
                        return Err(ClosureIdentityBlock::Exhausted);
                    }
                    continue;
                }
                if visited == CLOSURE_IDENTITY_WALK_LIMIT {
                    return Err(ClosureIdentityBlock::Exhausted);
                }
                visited += 1;
                identities.insert(current, None);
                let Some(node) = producer(current) else {
                    let (ty, sources) =
                        incoming(current).ok_or(ClosureIdentityBlock::Parameter { at: current })?;
                    if sources.is_empty() || sources.len() > CLOSURE_IDENTITY_WALK_LIMIT {
                        return Err(ClosureIdentityBlock::Parameter { at: current });
                    }
                    pending.push(Frame::BlockParameter(current, sources.to_vec(), ty.clone()));
                    pending.extend(sources.iter().rev().copied().map(Frame::Enter));
                    continue;
                };
                match &node.inst {
                    trust_ir::Inst::Const {
                        ty,
                        value: trust_ir::Constant::Closure { func, .. },
                    } => {
                        identities.insert(current, Some((*func, ty.clone())));
                    }
                    trust_ir::Inst::MakeClosure { ty, func, .. } => {
                        identities.insert(current, Some((*func, Ty::Closure(*ty))));
                    }
                    trust_ir::Inst::Load {
                        ty: ty @ Ty::Closure(id),
                        ..
                    } => {
                        let target = storage(*id).ok_or(ClosureIdentityBlock::Producer {
                            at: current,
                            inst: "Load",
                        })?;
                        identities.insert(current, Some((target, ty.clone())));
                    }
                    trust_ir::Inst::Copy { ty, operand }
                    | trust_ir::Inst::InsertField {
                        ty: ty @ Ty::Closure(_),
                        aggregate: operand,
                        ..
                    } => {
                        pending.push(Frame::Forward(
                            current,
                            *operand,
                            ty.clone(),
                            crate::handle_transport::inst_name(&node.inst),
                        ));
                        pending.push(Frame::Enter(*operand));
                    }
                    trust_ir::Inst::Select {
                        ty: ty @ Ty::Closure(_),
                        then_val,
                        else_val,
                        ..
                    } => {
                        pending.push(Frame::Select(current, *then_val, *else_val, ty.clone()));
                        pending.push(Frame::Enter(*else_val));
                        pending.push(Frame::Enter(*then_val));
                    }
                    other => {
                        return Err(ClosureIdentityBlock::Producer {
                            at: current,
                            inst: crate::handle_transport::inst_name(other),
                        });
                    }
                }
            }
            Frame::Forward(current, operand, ty, inst) => {
                let identity = identities
                    .get(&operand)
                    .and_then(Option::as_ref)
                    .ok_or(ClosureIdentityBlock::Exhausted)?
                    .clone();
                if identity.1 != ty {
                    return Err(ClosureIdentityBlock::Producer { at: current, inst });
                }
                identities.insert(current, Some(identity));
            }
            Frame::BlockParameter(current, sources, ty) => {
                let first = identities
                    .get(&sources[0])
                    .and_then(Option::as_ref)
                    .ok_or(ClosureIdentityBlock::Exhausted)?;
                if first.1 != ty
                    || !sources.iter().all(|source| {
                        identities.get(source).and_then(Option::as_ref) == Some(first)
                    })
                {
                    return Err(ClosureIdentityBlock::Incoming { at: current });
                }
                let identity = first.clone();
                identities.insert(current, Some(identity));
            }
            Frame::Select(current, then_val, else_val, ty) => {
                let left = identities
                    .get(&then_val)
                    .and_then(Option::as_ref)
                    .ok_or(ClosureIdentityBlock::Exhausted)?;
                let right = identities
                    .get(&else_val)
                    .and_then(Option::as_ref)
                    .ok_or(ClosureIdentityBlock::Exhausted)?;
                if left != right || left.1 != ty {
                    return Err(ClosureIdentityBlock::Producer {
                        at: current,
                        inst: "Select",
                    });
                }
                let identity = left.clone();
                identities.insert(current, Some(identity));
            }
        }
    }
    identities
        .remove(&value)
        .flatten()
        .ok_or(ClosureIdentityBlock::Exhausted)
}

/// Count every binding-sensitive module-local function identity, and every
/// `SymbolAddr` constant that names a module-local function by string
/// ([`ModuleLocalFunctionIdentityCensus::symbol_addresses`]).
///
/// Duplicate or dangling `FuncId`s never acquire guessed authority here; the
/// mandatory module validator rejects them separately. Constants use the shared
/// stack-safe borrowed walk so an identity cannot evade an early fail-closed
/// gate merely by being nested in an aggregate, record, or closure capture.
///
/// A first-class closure applied through `CallIndirect` is lowered as the
/// direct call to its statically visible literal's code
/// (`resolve_closure_identity`), so every such application whose checked identity names
/// a local definition is a direct edge here — it must not evade the same
/// binding refusal an `Inst::Call` to that definition meets. Conversely a
/// closure literal at `Ty::Closure` materializes only its environment, never a
/// code address, so it is not a materialized identity; the capture-free
/// literal at `Ty::Func` (a bare function address) still is, and a closure
/// nested in an aggregate or global initializer is still counted because the
/// walk over nested constants carries no type context.
pub fn module_local_function_identity_census(module: &Module) -> ModuleLocalFunctionIdentityCensus {
    let functions = ModuleFunctionCatalog::new(module);
    let is_local_definition = |target| {
        functions
            .unique(module, target)
            .is_some_and(is_module_local_function_definition)
    };
    let mut census = ModuleLocalFunctionIdentityCensus::default();
    visit_source_function_references(module, |reference, _site| match reference {
        SourceFunctionReference::DirectEdge(target) if is_local_definition(target) => {
            census.direct_edges += 1;
        }
        SourceFunctionReference::Materialized(target) if is_local_definition(target) => {
            census.materialized_identities += 1;
        }
        // A string naming a module-local function: the object resolves it
        // through that definition's symbol.
        SourceFunctionReference::SymbolName(symbol)
            if module_local_function_named(module, symbol).is_some() =>
        {
            census.symbol_addresses += 1;
        }
        _ => {}
    });
    census
}

/// The bodied Internal/Private function ([`is_module_local_function_definition`])
/// that `symbol` names, when it names exactly one (module validation makes
/// function names unique; a duplicated name never acquires guessed
/// authority). This is the one by-name classification the census, its
/// attribution and the text-reference set read for a `SymbolAddr`.
fn module_local_function_named<'m>(module: &'m Module, symbol: &str) -> Option<&'m Function> {
    let mut named = module
        .functions
        .iter()
        .filter(|function| function.name == symbol);
    let function = named.next()?;
    (named.next().is_none() && is_module_local_function_definition(function)).then_some(function)
}

/// [`module_local_function_identity_census`] attributed to where each
/// reference occurs, for a diagnostic census that names every function a
/// binding refusal concerns instead of one module-wide count.
///
/// The same walk and the same classification feed both, so the per-function
/// counts sum to the module census exactly
/// (`attributed_census_sums_to_the_module_census`).
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct ModuleLocalFunctionIdentityAttribution {
    /// The references each function's own BODY makes, keyed by the
    /// referencing function's id. Only functions with at least one counted
    /// reference appear.
    pub bodies: std::collections::BTreeMap<FuncId, ModuleLocalFunctionIdentityCensus>,
    /// Materialized identities in GLOBAL INITIALIZERS, keyed by the
    /// module-local function whose identity they materialize (a global has
    /// no referencing function).
    pub global_initializer_targets: std::collections::BTreeMap<FuncId, usize>,
    /// `SymbolAddr` constants in GLOBAL INITIALIZERS that name a module-local
    /// function, keyed by the function they name
    /// ([`ModuleLocalFunctionIdentityCensus::symbol_addresses`]).
    pub global_initializer_symbol_addresses: std::collections::BTreeMap<FuncId, usize>,
}

/// Attribute every binding-sensitive module-local function identity
/// ([`module_local_function_identity_census`]) to the body that makes it, or,
/// for a global initializer, to the function it names.
#[must_use]
pub fn module_local_function_identity_attribution(
    module: &Module,
) -> ModuleLocalFunctionIdentityAttribution {
    let functions = ModuleFunctionCatalog::new(module);
    let is_local_definition = |target| {
        functions
            .unique(module, target)
            .is_some_and(is_module_local_function_definition)
    };
    let mut attribution = ModuleLocalFunctionIdentityAttribution::default();
    visit_source_function_references(module, |reference, site| {
        let (target, direct) = match reference {
            SourceFunctionReference::DirectEdge(target) => (target, true),
            SourceFunctionReference::Materialized(target) => (target, false),
            // A string naming a module-local function (as in the census).
            SourceFunctionReference::SymbolName(symbol) => {
                let Some(function) = module_local_function_named(module, symbol) else {
                    return;
                };
                match site {
                    SourceReferenceSite::Body(holder) => {
                        attribution
                            .bodies
                            .entry(holder)
                            .or_default()
                            .symbol_addresses += 1;
                    }
                    SourceReferenceSite::GlobalInitializer => {
                        *attribution
                            .global_initializer_symbol_addresses
                            .entry(function.id)
                            .or_default() += 1;
                    }
                }
                return;
            }
        };
        if !is_local_definition(target) {
            return;
        }
        match site {
            SourceReferenceSite::Body(holder) => {
                let census = attribution.bodies.entry(holder).or_default();
                if direct {
                    census.direct_edges += 1;
                } else {
                    census.materialized_identities += 1;
                }
            }
            // The walk visits a global initializer only through its constants,
            // which never form a direct edge.
            SourceReferenceSite::GlobalInitializer => {
                *attribution
                    .global_initializer_targets
                    .entry(target)
                    .or_default() += 1;
            }
        }
    });
    attribution
}

/// One reference a TrustIR module's source makes to a function.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum SourceFunctionReference<'a> {
    /// A direct `Call`/`Invoke` edge, or the application of a closure value
    /// whose statically visible literal names the target.
    DirectEdge(FuncId),
    /// A materialized `FnDef` or capture-free `Closure` identity.
    Materialized(FuncId),
    /// A `SymbolAddr` constant naming a symbol by string.
    SymbolName(&'a str),
}

/// Where a [`SourceFunctionReference`] occurs.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum SourceReferenceSite {
    /// In the body of the function with this id: its object reference is a
    /// text relocation.
    Body(FuncId),
    /// In a global initializer: its object reference is a data relocation.
    GlobalInitializer,
}

/// Visit every source reference to a function, exactly once, in bodies and
/// global initializers. The identity census and the text-reference set both
/// read this one walk, so they cannot disagree about what a module
/// references.
fn visit_source_function_references<'m>(
    module: &'m Module,
    mut visit: impl FnMut(SourceFunctionReference<'m>, SourceReferenceSite),
) {
    fn visit_constant<'m>(
        constant: &'m trust_ir::Constant,
        site: SourceReferenceSite,
        visit: &mut impl FnMut(SourceFunctionReference<'m>, SourceReferenceSite),
    ) {
        use trust_ir::Constant;
        constant.visit_constants(|constant| match constant {
            Constant::FnDef(target) => visit(SourceFunctionReference::Materialized(*target), site),
            Constant::Closure { func, captures } if captures.is_empty() => {
                visit(SourceFunctionReference::Materialized(*func), site);
            }
            Constant::SymbolAddr { symbol, .. } => {
                visit(SourceFunctionReference::SymbolName(symbol.as_str()), site);
            }
            // Child discovery is exhaustive in TrustIR, not another backend
            // container inventory. This walk does not grant type authority.
            _ => {}
        });
    }

    for function in &module.functions {
        let parameters = std::cell::OnceCell::new();
        let mut producers: HashMap<ValueId, &trust_ir::InstrNode> = HashMap::new();
        for node in function.blocks.iter().flat_map(|block| &block.body) {
            for result in &node.results {
                // First definition wins, as in the adapter's producer index.
                producers.entry(*result).or_insert(node);
            }
        }
        for node in function.blocks.iter().flat_map(|block| &block.body) {
            match &node.inst {
                trust_ir::Inst::Call { callee, .. }
                | trust_ir::Inst::CallCannotUnwind { callee, .. }
                | trust_ir::Inst::Invoke { callee, .. } => {
                    visit(
                        SourceFunctionReference::DirectEdge(*callee),
                        SourceReferenceSite::Body(function.id),
                    );
                }
                trust_ir::Inst::CallIndirect { callee, .. }
                | trust_ir::Inst::CallIndirectCannotUnwind { callee, .. }
                | trust_ir::Inst::InvokeIndirect { callee, .. } => {
                    if let Ok((func, Ty::Closure(_))) = resolve_closure_identity(
                        |value| producers.get(&value).copied(),
                        |value| {
                            parameters
                                .get_or_init(|| ClosureBlockParameterSources::new(function))
                                .as_ref()?
                                .get(value)
                        },
                        |closure| {
                            module
                                .closure_storage_binding(closure)
                                .ok()
                                .map(|binding| binding.target)
                        },
                        *callee,
                    ) {
                        visit(
                            SourceFunctionReference::DirectEdge(func),
                            SourceReferenceSite::Body(function.id),
                        );
                    }
                }
                // A closure literal at `Ty::Closure` is an environment, not an
                // address; its applications are direct edges above. Its
                // CAPTURES are ordinary constants and are still walked.
                trust_ir::Inst::Const {
                    ty: Ty::Closure(_),
                    value: trust_ir::Constant::Closure { captures, .. },
                } => {
                    for capture in captures {
                        visit_constant(capture, SourceReferenceSite::Body(function.id), &mut visit);
                    }
                }
                trust_ir::Inst::Const { value, .. } => {
                    visit_constant(value, SourceReferenceSite::Body(function.id), &mut visit);
                }
                _ => {}
            }
        }
    }
    for global in &module.globals {
        if let Some(initializer) = &global.initializer {
            visit_constant(
                initializer,
                SourceReferenceSite::GlobalInitializer,
                &mut visit,
            );
        }
    }
}

/// Names of the bodied Internal/Private functions ([`is_module_local_function_definition`])
/// that the module's function BODIES reference: direct `Call`/`Invoke` callees,
/// closure applications through a statically visible literal, `FnDef` and
/// capture-free `Closure` constants (nested ones and closure captures
/// included) and `SymbolAddr` constants whose string names such a function.
///
/// Every text relocation an object path emits that names a module-local
/// function should come from one of these. A text reference to a
/// module-local function outside this set was made by the backend on its own
/// (a runtime call by a same-spelled name), and the AArch64 ELF
/// post-emission check refuses it.
pub fn module_local_function_text_references(
    module: &Module,
) -> std::collections::BTreeSet<String> {
    let functions = ModuleFunctionCatalog::new(module);
    let local_by_id = |target| {
        functions
            .unique(module, target)
            .filter(|function| is_module_local_function_definition(function))
            .map(|function| function.name.clone())
    };
    let local_by_name = |symbol: &str| module_local_function_named(module, symbol).is_some();
    let mut names = std::collections::BTreeSet::new();
    visit_source_function_references(module, |reference, site| {
        if !matches!(site, SourceReferenceSite::Body(_)) {
            return;
        }
        match reference {
            SourceFunctionReference::DirectEdge(target)
            | SourceFunctionReference::Materialized(target) => names.extend(local_by_id(target)),
            SourceFunctionReference::SymbolName(symbol) if local_by_name(symbol) => {
                names.insert(symbol.to_string());
            }
            SourceFunctionReference::SymbolName(_) => {}
        }
    });
    names
}

/// Prove that replacing this one indirect edge by a named call is exact.
///
/// `value_types` is the adapter's existing function census. Module validation
/// has already rejected duplicate SSA definitions before this function can be
/// called, so consuming the census requires no backend-local uniqueness scan.
#[allow(clippy::too_many_arguments)]
pub(crate) fn exact_static_call_target<S: std::hash::BuildHasher>(
    module: &Module,
    functions: &ModuleFunctionCatalog,
    value_types: &std::collections::HashMap<ValueId, Ty, S>,
    resolution: StaticFunctionPointerResolution,
    containing_function: FuncId,
    callee_value: ValueId,
    edge_block: BlockId,
    edge_instruction_index: usize,
    edge_sig_id: FuncTyId,
    args: &[ValueId],
    edge_calling_conv: CallingConv,
    results: &[ValueId],
) -> Option<FuncId> {
    if resolution.containing_function() != containing_function
        || resolution.queried_value() != callee_value
        || resolution.use_block() != edge_block
        || resolution.use_instruction_index() != edge_instruction_index
    {
        return None;
    }

    // Function ids are identities, not vector positions. A malformed module
    // with duplicate ids must never acquire a guessed direct target.
    let target_function = functions.unique(module, resolution.function())?;
    // Only a bodied, non-interposable definition can become an exact module
    // call. External declarations and External/Weak/LinkOnce definitions keep
    // their original function-pointer/linker semantics as CallIndirect until
    // an interposition-aware authorization exists end to end.
    if !is_module_local_function_definition(target_function) {
        return None;
    }

    // Preserve nominal signature identity at the originating FnDef as well as
    // structural equality at the call edge. This closes signature laundering
    // through an otherwise raw pointer carrier.
    if resolution.declared_signature() != target_function.ty {
        return None;
    }
    let edge_sig = module.func_types.get(edge_sig_id.as_usize())?;
    let target_sig = module.func_types.get(target_function.ty.as_usize())?;
    if edge_sig.is_vararg
        || edge_sig != target_sig
        || edge_calling_conv != target_function.calling_conv
        || args.len() != target_sig.params.len()
        || results.len() != target_sig.returns.len()
    {
        return None;
    }

    let unique_ty = |value: ValueId| value_types.get(&value);

    // Function carriers retain their exact FuncTyId. Raw pointers are
    // signature-free until this checked edge, but must still be typed Ptr.
    let callee_ty = unique_ty(callee_value)?;
    let carrier_is_exact = match resolution.carrier() {
        StaticFunctionPointerCarrier::Function(signature) => {
            signature == edge_sig_id && callee_ty == &Ty::Func(signature)
        }
        StaticFunctionPointerCarrier::Pointer => callee_ty == &Ty::Ptr,
    };
    if !carrier_is_exact {
        return None;
    }

    // Exact types intentionally reject adapter conveniences. Declining a
    // valid edge is safe; turning an invalid edge into a valid direct call is
    // not. Missing and duplicate SSA definitions therefore fail closed.
    if !args
        .iter()
        .zip(&target_sig.params)
        .all(|(argument, expected)| unique_ty(*argument) == Some(expected))
        || !results
            .iter()
            .zip(&target_sig.returns)
            .all(|(result, expected)| unique_ty(*result) == Some(expected))
    {
        return None;
    }

    Some(resolution.function())
}

#[cfg(test)]
mod tests {
    use super::{
        ExactModuleCallAuthorization, ModuleTranslationValidationReport,
        module_local_function_identity_census, module_local_function_text_references,
    };
    use trust_ir::{
        Block, BlockId, Constant, FuncId, FuncTy, Function, Global, Inst, InstrNode, Linkage,
        Module, Ty, ValueId,
    };

    #[test]
    fn stored_closure_identity_requires_the_checked_type_binding() {
        let closure = trust_ir::ClosureTyId::new(3);
        let result = ValueId::new(1);
        let node = InstrNode::new(Inst::Load {
            ty: Ty::Closure(closure),
            ptr: ValueId::new(0),
            volatile: false,
            align: None,
        })
        .with_result(result);
        let resolve = |binding| {
            super::resolve_closure_identity(
                |value| (value == result).then_some(&node),
                |_| None,
                |id| (id == closure).then_some(binding).flatten(),
                result,
            )
        };
        assert!(resolve(None).is_err());
        assert_eq!(
            resolve(Some(FuncId::new(7))).unwrap(),
            (FuncId::new(7), Ty::Closure(closure))
        );
        assert_eq!(
            resolve(Some(FuncId::new(8))).unwrap(),
            (FuncId::new(8), Ty::Closure(closure))
        );
        // The legacy constructor-only query supplies no storage authority.
        assert!(
            super::resolve_closure_literal(
                |value| (value == result).then_some(&node),
                |_| None,
                result,
            )
            .is_err()
        );
    }

    #[test]
    fn selected_closure_identity_is_typed_bounded_and_stack_safe() {
        use super::{ClosureIdentityBlock, resolve_closure_literal};
        use trust_ir::ClosureTyId;
        let ty = Ty::Closure(ClosureTyId::new(0));
        let mut nodes = std::collections::HashMap::new();
        let literal = |func, ty| {
            InstrNode::new(Inst::Const {
                ty,
                value: Constant::Closure {
                    func: FuncId::new(func),
                    captures: vec![],
                },
            })
        };
        nodes.insert(ValueId::new(0), literal(1, ty.clone()));
        nodes.insert(ValueId::new(1), literal(1, ty.clone()));
        // Repeated shared diamonds must not spend exponential walk work.
        for index in 2..1000 {
            nodes.insert(
                ValueId::new(index),
                InstrNode::new(Inst::Select {
                    ty: ty.clone(),
                    cond: ValueId::new(9000),
                    then_val: ValueId::new(index - 1),
                    else_val: ValueId::new(index - 2),
                }),
            );
        }
        let root = ValueId::new(999);
        assert_eq!(
            resolve_closure_literal(|v| nodes.get(&v), |_| None, root),
            Ok((FuncId::new(1), ty.clone()))
        );
        nodes.insert(ValueId::new(0), literal(2, ty.clone()));
        assert!(matches!(
            resolve_closure_literal(|v| nodes.get(&v), |_| None, root),
            Err(ClosureIdentityBlock::Producer { inst: "Select", .. })
        ));
        // Matching function IDs at different closure types cannot grant identity.
        nodes.insert(
            ValueId::new(0),
            literal(1, Ty::Closure(ClosureTyId::new(1))),
        );
        assert!(matches!(
            resolve_closure_literal(|v| nodes.get(&v), |_| None, root),
            Err(ClosureIdentityBlock::Producer { inst: "Select", .. })
        ));
        nodes.remove(&ValueId::new(0));
        assert!(matches!(
            resolve_closure_literal(|v| nodes.get(&v), |_| None, root),
            Err(ClosureIdentityBlock::Parameter { .. })
        ));
        nodes.insert(
            ValueId::new(0),
            InstrNode::new(Inst::Copy {
                ty: ty.clone(),
                operand: root,
            }),
        );
        assert_eq!(
            resolve_closure_literal(|v| nodes.get(&v), |_| None, root),
            Err(ClosureIdentityBlock::Exhausted)
        );
        nodes.clear();
        for index in 0..=super::CLOSURE_IDENTITY_WALK_LIMIT as u32 {
            nodes.insert(
                ValueId::new(index),
                InstrNode::new(Inst::Copy {
                    ty: ty.clone(),
                    operand: ValueId::new(index + 1),
                }),
            );
        }
        assert_eq!(
            resolve_closure_literal(|v| nodes.get(&v), |_| None, ValueId::new(0)),
            Err(ClosureIdentityBlock::Exhausted)
        );
    }

    fn closure_block_parameter_function() -> Function {
        let ty = Ty::Closure(trust_ir::ClosureTyId::new(0));
        let literal = |result| {
            InstrNode::new(Inst::Const {
                ty: ty.clone(),
                value: Constant::Closure {
                    func: FuncId::new(7),
                    captures: vec![],
                },
            })
            .with_result(ValueId::new(result))
        };
        let mut function = Function::new(
            FuncId::new(0),
            "block_closure",
            trust_ir::FuncTyId::new(0),
            BlockId::new(0),
        );
        function.blocks = vec![
            Block {
                id: BlockId::new(0),
                params: vec![(ValueId::new(0), Ty::Bool)],
                body: vec![
                    literal(1),
                    literal(2),
                    InstrNode::new(Inst::CondBr {
                        cond: ValueId::new(0),
                        then_target: BlockId::new(1),
                        then_args: vec![ValueId::new(1)],
                        else_target: BlockId::new(2),
                        else_args: vec![ValueId::new(2)],
                    }),
                ],
            },
            Block {
                id: BlockId::new(1),
                params: vec![(ValueId::new(10), ty.clone())],
                body: vec![InstrNode::new(Inst::Br {
                    target: BlockId::new(3),
                    args: vec![ValueId::new(10)],
                })],
            },
            Block {
                id: BlockId::new(2),
                params: vec![(ValueId::new(11), ty.clone())],
                body: vec![InstrNode::new(Inst::Br {
                    target: BlockId::new(3),
                    args: vec![ValueId::new(11)],
                })],
            },
            Block {
                id: BlockId::new(3),
                params: vec![(ValueId::new(12), ty)],
                body: vec![InstrNode::new(Inst::Return {
                    values: vec![ValueId::new(12)],
                })],
            },
        ];
        function
    }

    fn block_closure_identity(
        function: &Function,
        root: ValueId,
    ) -> Result<(FuncId, Ty), super::ClosureIdentityBlock> {
        let parameters = super::ClosureBlockParameterSources::new(function);
        let mut producers = std::collections::HashMap::new();
        for node in function.blocks.iter().flat_map(|block| &block.body) {
            for result in &node.results {
                producers.insert(*result, node);
            }
        }
        super::resolve_closure_literal(
            |value| producers.get(&value).copied(),
            |value| parameters.as_ref()?.get(value),
            root,
        )
    }

    #[test]
    fn block_closure_identity_joins_all_exact_incoming_values_without_block_order_assumptions() {
        let mut function = closure_block_parameter_function();
        let expected = Ok((FuncId::new(7), Ty::Closure(trust_ir::ClosureTyId::new(0))));
        assert_eq!(
            block_closure_identity(&function, ValueId::new(12)),
            expected
        );
        function.blocks.reverse();
        assert_eq!(
            block_closure_identity(&function, ValueId::new(12)),
            expected
        );
        // Two edges from ONE terminator to the same block are distinct inputs.
        let mut function = closure_block_parameter_function();
        function.blocks[0].body[2].inst = Inst::CondBr {
            cond: ValueId::new(0),
            then_target: BlockId::new(3),
            then_args: vec![ValueId::new(1)],
            else_target: BlockId::new(3),
            else_args: vec![ValueId::new(2)],
        };
        function
            .blocks
            .retain(|block| block.id == BlockId::new(0) || block.id == BlockId::new(3));
        assert_eq!(
            block_closure_identity(&function, ValueId::new(12)),
            expected
        );
        if let Inst::Const {
            value: Constant::Closure { func, .. },
            ..
        } = &mut function.blocks[0].body[1].inst
        {
            *func = FuncId::new(8);
        }
        assert!(block_closure_identity(&function, ValueId::new(12)).is_err());
    }

    #[test]
    fn block_closure_identity_rejects_different_code_type_unknown_and_malformed_edges() {
        for mutation in 0..13 {
            let mut f = closure_block_parameter_function();
            match mutation {
                0 => {
                    if let Inst::Const {
                        value: Constant::Closure { func, .. },
                        ..
                    } = &mut f.blocks[0].body[1].inst
                    {
                        *func = FuncId::new(8);
                    }
                }
                1 => {
                    if let Inst::Const { ty, .. } = &mut f.blocks[0].body[1].inst {
                        *ty = Ty::Closure(trust_ir::ClosureTyId::new(1));
                    }
                }
                2 => {
                    f.blocks[0].body[1].inst = Inst::Load {
                        ty: Ty::Closure(trust_ir::ClosureTyId::new(0)),
                        ptr: ValueId::new(0),
                        volatile: false,
                        align: None,
                    }
                }
                3 => {
                    if let Inst::Br { args, .. } = &mut f.blocks[1].body[0].inst {
                        args.clear();
                    }
                }
                4 => {
                    if let Inst::Br { args, .. } = &mut f.blocks[1].body[0].inst {
                        args[0] = ValueId::new(999);
                    }
                }
                5 => {
                    if let Inst::Br { target, .. } = &mut f.blocks[1].body[0].inst {
                        *target = BlockId::new(999);
                    }
                }
                6 => f.blocks[1].params[0].0 = ValueId::new(11),
                7 => f.blocks[0].body[1].results = vec![ValueId::new(1)],
                8 => f.blocks[1].id = BlockId::new(2),
                9 => f.blocks[1]
                    .body
                    .push(InstrNode::new(Inst::Return { values: vec![] })),
                10 => {
                    // A forwarding Copy's DECLARED type cannot borrow its source's proof.
                    f.blocks[0].body[1].inst = Inst::Copy {
                        ty: Ty::U64,
                        operand: ValueId::new(1),
                    };
                }
                11 => f.blocks[0].body[1].results = vec![ValueId::new(2), ValueId::new(3)],
                12 => {
                    let closure = f.blocks[0].body.remove(1);
                    f.blocks[1].body.insert(0, closure);
                }
                _ => unreachable!(),
            }
            assert!(
                block_closure_identity(&f, ValueId::new(12)).is_err(),
                "mutation {mutation}"
            );
        }
    }

    #[test]
    fn block_closure_identity_rejects_entry_parameters_unanchored_values_cycles_and_budget_exhaustion()
     {
        let mut f = closure_block_parameter_function();
        f.blocks[0]
            .params
            .push((ValueId::new(20), Ty::Closure(trust_ir::ClosureTyId::new(0))));
        assert!(block_closure_identity(&f, ValueId::new(20)).is_err());
        // A parameter with no incoming edges is unknown, never vacuously same-code.
        f.blocks.push(Block {
            id: BlockId::new(4),
            params: vec![(ValueId::new(21), Ty::Closure(trust_ir::ClosureTyId::new(0)))],
            body: vec![InstrNode::new(Inst::Return { values: vec![] })],
        });
        assert!(block_closure_identity(&f, ValueId::new(21)).is_err());
        // Even an unreachable predecessor's unknown closure cannot be ignored.
        f.blocks[4].body = vec![InstrNode::new(Inst::Br {
            target: BlockId::new(3),
            args: vec![ValueId::new(21)],
        })];
        assert!(block_closure_identity(&f, ValueId::new(12)).is_err());
        f.blocks[4].body = vec![InstrNode::new(Inst::Return { values: vec![] })];
        f.blocks[3].body = vec![InstrNode::new(Inst::CondBr {
            cond: ValueId::new(0),
            then_target: BlockId::new(3),
            then_args: vec![ValueId::new(12)],
            else_target: BlockId::new(4),
            else_args: vec![ValueId::new(12)],
        })];
        assert_eq!(
            block_closure_identity(&f, ValueId::new(12)),
            Err(super::ClosureIdentityBlock::Exhausted)
        );
        let mut f = closure_block_parameter_function();
        f.blocks[2].body = vec![InstrNode::new(Inst::CondBr {
            cond: ValueId::new(0),
            then_target: BlockId::new(3),
            then_args: vec![ValueId::new(11)],
            else_target: BlockId::new(4),
            else_args: vec![],
        })];
        let last = super::CLOSURE_IDENTITY_WALK_LIMIT as u32 - 1;
        for index in 4..=last {
            let branch = if index == last {
                Inst::Br {
                    target: BlockId::new(3),
                    args: vec![ValueId::new(1)],
                }
            } else {
                Inst::CondBr {
                    cond: ValueId::new(0),
                    then_target: BlockId::new(3),
                    then_args: vec![ValueId::new(1)],
                    else_target: BlockId::new(index + 1),
                    else_args: vec![],
                }
            };
            f.blocks.push(Block {
                id: BlockId::new(index),
                params: vec![],
                body: vec![InstrNode::new(branch)],
            });
        }
        assert_eq!(
            block_closure_identity(&f, ValueId::new(12)),
            Ok((FuncId::new(7), Ty::Closure(trust_ir::ClosureTyId::new(0))))
        );
        f.blocks.last_mut().unwrap().body = vec![InstrNode::new(Inst::CondBr {
            cond: ValueId::new(0),
            then_target: BlockId::new(3),
            then_args: vec![ValueId::new(1)],
            else_target: BlockId::new(last + 1),
            else_args: vec![],
        })];
        f.blocks.push(Block {
            id: BlockId::new(last + 1),
            params: vec![],
            body: vec![InstrNode::new(Inst::Br {
                target: BlockId::new(3),
                args: vec![ValueId::new(1)],
            })],
        });
        assert!(block_closure_identity(&f, ValueId::new(12)).is_err());
    }

    fn repeated_external_declarations() -> Module {
        let mut module = Module::new("repeated_import");
        for id in [7, 11] {
            // MIR imports can allocate distinct type-table entries for the
            // same declaration. Compatibility is structural, not FuncTyId equality.
            let signature = module
                .add_func_type(FuncTy {
                    params: vec![Ty::I64],
                    returns: vec![Ty::I64],
                    abi: None,
                    is_vararg: false,
                })
                .expect("Module::add_func_type: test fixture");
            module.functions.push(Function::new(
                FuncId::new(id),
                "imported",
                signature,
                BlockId::new(0),
            ));
        }
        module
    }

    #[test]
    fn compatible_external_declarations_keep_each_exact_identity() {
        let module = repeated_external_declarations();
        let catalog = super::ModuleFunctionCatalog::new(&module);
        assert_eq!(catalog.first_ambiguous_symbol(), None);
        assert_eq!(catalog.first_ambiguous_id(), None);
        for function in &module.functions {
            assert!(std::ptr::eq(
                catalog.unique(&module, function.id).unwrap(),
                function,
            ));
            assert_eq!(catalog.name(function.id), Some("imported"));
        }
    }

    /// One declaration-incompatibility case: its label and the edit that
    /// introduces it into a freshly built module.
    type DeclarationMutation = (&'static str, fn(&mut Module));

    #[test]
    fn incompatible_external_declarations_never_share_symbol_authority() {
        let mutations: &[DeclarationMutation] = &[
            ("parameter", |m| m.func_types[1].params[0] = Ty::U64),
            ("return", |m| m.func_types[1].returns[0] = Ty::U64),
            ("varargs", |m| m.func_types[1].is_vararg = true),
            ("missing type", |m| {
                m.functions[1].ty = trust_ir::FuncTyId::new(99);
            }),
            ("both missing types", |m| {
                for f in &mut m.functions {
                    f.ty = trust_ir::FuncTyId::new(99);
                }
            }),
            ("calling convention", |m| {
                m.functions[1].calling_conv = trust_ir::CallingConv::Swift;
            }),
            ("linkage", |m| m.functions[1].linkage = Linkage::Internal),
            ("definition", |m| {
                m.functions[1].blocks.push(Block::new(BlockId::new(0)));
            }),
            ("attributes", |m| m.functions[1].attrs.readnone = true),
            ("contract", |m| {
                m.functions[1].summary = Some(trust_ir::FunctionSummary::new());
            }),
            ("proof annotation", |m| {
                m.functions[1].proofs.push(trust_ir::ProofAnnotation::Pure);
            }),
            ("producer", |m| {
                m.functions[1].producer = Some(trust_ir::Producer::TrustIr);
            }),
            ("value names", |m| m.functions[1].value_names = Some(vec![])),
            ("scopes", |m| m.functions[1].scopes = Some(vec![])),
            ("entry", |m| m.functions[1].entry = BlockId::new(1)),
            // Only `External` declarations may share a symbol: a weak one
            // beside a strong one would let the object's one undefined symbol
            // be weak (L02-P6 closure audit 6, mutant K20), and two weak ones
            // are outside the rule too.
            ("weak linkage", |m| {
                m.functions[1].linkage = Linkage::ExternalWeak;
            }),
            ("both weak", |m| {
                for f in &mut m.functions {
                    f.linkage = Linkage::ExternalWeak;
                }
            }),
            // v41 authority and claim metadata.
            ("body gate", |m| {
                m.functions[1].body_gate = Some(trust_ir::BodyGate::Ungated);
            }),
            ("display path", |m| {
                m.functions[1].display_path = Some("crate::imported".into());
            }),
            ("source provenance", |m| {
                m.functions[1].source_provenance = Some(trust_ir::SourceProvenance::new(
                    trust_ir::proof::ProofDigest::zero(),
                    trust_ir::proof::ProofDigest::zero(),
                    Vec::new(),
                ));
            }),
            // v45 object-affecting metadata: the object spells one symbol, so
            // two declarations that disagree about its section, visibility or
            // retention cannot both be honored (L02-P6 closure audit 6,
            // mutant K19: without the visibility comparison the symbol took
            // whichever declaration came last).
            ("section", |m| {
                m.functions[1].section = Some(".text.imported".into());
            }),
            ("visibility hidden", |m| {
                m.functions[1].visibility = trust_ir::Visibility::Hidden;
            }),
            ("visibility protected", |m| {
                m.functions[1].visibility = trust_ir::Visibility::Protected;
            }),
            ("visibility hidden and protected", |m| {
                m.functions[0].visibility = trust_ir::Visibility::Hidden;
                m.functions[1].visibility = trust_ir::Visibility::Protected;
            }),
            ("retained", |m| m.functions[1].retained = true),
        ];
        for (label, mutate) in mutations {
            let mut module = repeated_external_declarations();
            mutate(&mut module);
            for reverse in [false, true] {
                if reverse {
                    module.functions.reverse();
                }
                assert_eq!(
                    super::ModuleFunctionCatalog::new(&module).first_ambiguous_symbol(),
                    Some("imported"),
                    "{label}, reverse={reverse}",
                );
            }
        }
    }

    /// The v45 comparisons are equality, not a refusal of non-default
    /// metadata: two `External` declarations that state the same visibility,
    /// section and retention still share their symbol.
    #[test]
    fn agreeing_v45_declaration_metadata_still_shares_one_symbol() {
        let agreeing: &[DeclarationMutation] = &[
            ("both hidden", |m| {
                for f in &mut m.functions {
                    f.visibility = trust_ir::Visibility::Hidden;
                }
            }),
            ("both protected", |m| {
                for f in &mut m.functions {
                    f.visibility = trust_ir::Visibility::Protected;
                }
            }),
            ("both in one section", |m| {
                for f in &mut m.functions {
                    f.section = Some(".text.imported".into());
                }
            }),
            ("both retained", |m| {
                for f in &mut m.functions {
                    f.retained = true;
                }
            }),
        ];
        for (label, mutate) in agreeing {
            let mut module = repeated_external_declarations();
            mutate(&mut module);
            let catalog = super::ModuleFunctionCatalog::new(&module);
            assert_eq!(catalog.first_ambiguous_symbol(), None, "{label}");
            assert_eq!(catalog.first_ambiguous_id(), None, "{label}");
        }
    }

    #[test]
    fn compatible_external_declarations_do_not_excuse_id_or_global_collisions() {
        let mut module = repeated_external_declarations();
        module.functions[1].id = module.functions[0].id;
        assert_eq!(
            super::ModuleFunctionCatalog::new(&module).first_ambiguous_id(),
            Some(FuncId::new(7)),
        );
        let mut module = repeated_external_declarations();
        module.globals.push(Global {
            name: "imported".into(),
            ty: Ty::I64,
            mutable: false,
            initializer: None,
            linkage: Linkage::External,
            tls: None,
            align: None,
            section: None,
            visibility: trust_ir::Visibility::Default,
            retained: false,
        });
        assert_eq!(
            super::ModuleFunctionCatalog::new(&module).first_ambiguous_symbol(),
            Some("imported"),
        );
    }

    #[test]
    fn renaming_distinct_imports_to_one_symbol_is_not_redeclaration() {
        let mut module = repeated_external_declarations();
        module.functions[1].name = "different_import".into();
        let names = std::collections::HashMap::from([
            (FuncId::new(7), "lowered".into()),
            (FuncId::new(11), "lowered".into()),
        ]);
        assert_eq!(
            super::ModuleFunctionCatalog::new_with_names(&module, Some(&names))
                .first_ambiguous_symbol(),
            Some("lowered"),
        );
    }

    #[test]
    fn call_census_counts_are_validated_before_recording_either_carrier_kind() {
        use crate::function::{BasicBlock, Function as LirFunction, Signature};
        use crate::instructions::{Block as LirBlock, Instruction, Opcode};
        let module = Module::new("census_count");
        let mut report = ModuleTranslationValidationReport::new(&module);
        let mut function = LirFunction::new("caller", Signature::default());
        function.blocks.insert(
            LirBlock(0),
            BasicBlock {
                instructions: vec![Instruction {
                    opcode: Opcode::FunctionAddr {
                        name: "callee".into(),
                        function: 7,
                    },
                    args: vec![],
                    results: vec![],
                }],
                ..BasicBlock::default()
            },
        );
        let origin = trust_cg_ir::TrustIrInstId(0);
        function
            .trust_ir_origins
            .insert(LirBlock(0), vec![Some(origin)]);
        let error = report
            .record_translated_function(
                0,
                FuncId::new(0),
                &function,
                super::PendingDirectCallAuthorizations::new(
                    1,
                    vec![super::PendingExactModuleCallAuthorization::new(
                        LirBlock(0),
                        0,
                        origin,
                        FuncId::new(7),
                    )],
                    1,
                    vec![],
                ),
            )
            .unwrap_err();
        assert!(error.to_string().contains("declared-external call"));
        assert_eq!(report.exact_module_call_count(), 0);
        assert_eq!(report.exact_module_address_count(), 0);

        report
            .record_translated_function(
                0,
                FuncId::new(0),
                &function,
                super::PendingDirectCallAuthorizations::new(0, vec![], 0, vec![]),
            )
            .unwrap();
        assert_eq!(report.exact_module_call_count(), 0);
    }

    #[test]
    fn call_identity_lengths_use_exact_big_endian_u64_framing() {
        let mut bytes = Vec::new();
        super::push_u64(&mut bytes, 0).unwrap();
        super::push_u64(&mut bytes, usize::MAX).unwrap();
        assert_eq!(&bytes[..8], &0u64.to_be_bytes());
        assert_eq!(&bytes[8..], &(usize::MAX as u64).to_be_bytes());
    }

    fn constant_census_fixture(value: Constant) -> Module {
        let mut module = Module::new("constant_census");
        let signature = module
            .add_func_type(FuncTy {
                params: vec![],
                returns: vec![],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        for (id, linkage) in [
            (7, Linkage::Internal),
            (11, Linkage::Private),
            (17, Linkage::External),
        ] {
            let mut function = Function::new(
                FuncId::new(id),
                format!("target_{id}"),
                signature,
                BlockId::new(0),
            );
            function.linkage = linkage;
            let mut block = Block::new(BlockId::new(0));
            block
                .body
                .push(InstrNode::new(Inst::Return { values: vec![] }));
            function.blocks.push(block);
            module
                .try_add_function(function)
                .expect("Module::try_add_function: test fixture");
        }
        // Isolate the pre-admission identity census, not constant typing or
        // machine admission. Its contract does not assume prior validation.
        module.globals.push(Global {
            name: "nested".into(),
            ty: Ty::Unit,
            mutable: false,
            initializer: Some(value),
            linkage: Linkage::Internal,
            tls: None,
            align: None,
            section: None,
            visibility: trust_ir::Visibility::Default,
            retained: false,
        });
        module
    }

    #[test]
    fn constant_identity_census_preserves_container_and_empty_closure_rules() {
        let local = || Constant::FnDef(FuncId::new(7));
        let mut module = constant_census_fixture(Constant::Aggregate(vec![
            Constant::Array(vec![local()]),
            Constant::Vector(vec![local()]),
            Constant::Sequence(vec![local()]),
            Constant::Set(vec![local()]),
            Constant::Record(vec![("callback".into(), local())]),
            Constant::Closure {
                func: FuncId::new(7),
                captures: vec![],
            },
            // A captured closure's own target is not an empty-closure identity;
            // its nested function items are still visited exactly once.
            Constant::Closure {
                func: FuncId::new(7),
                captures: vec![local()],
            },
            Constant::FnDef(FuncId::new(11)),
            Constant::FnDef(FuncId::new(17)), // Interposable: not module-local.
            Constant::FnDef(FuncId::new(999)), // Missing: never guessed local.
        ]));
        let census = module_local_function_identity_census(&module);
        assert_eq!(census.direct_edges, 0);
        assert_eq!(census.materialized_identities, 8);
        let mut duplicate = module.functions[0].clone();
        duplicate.name = "ambiguous".into();
        module.functions.push(duplicate);
        assert_eq!(
            module_local_function_identity_census(&module).materialized_identities,
            1
        );
    }

    /// The text-reference set reads the census's own walk: body references
    /// (direct calls, nested `FnDef`s and `SymbolAddr` strings) name
    /// module-local functions; a global initializer's reference does not (it
    /// is a data relocation); an External target and a string naming no
    /// module-local function are absent.
    #[test]
    fn text_references_read_bodies_not_initializers() {
        let mut module = constant_census_fixture(Constant::FnDef(FuncId::new(11)));
        assert!(module_local_function_text_references(&module).is_empty());
        let body = |module: &mut Module, nodes: Vec<InstrNode>| {
            let entry = &mut module.functions[2].blocks[0];
            entry.body.splice(0..0, nodes);
        };
        body(
            &mut module,
            vec![
                InstrNode::new(Inst::Call {
                    callee: FuncId::new(7),
                    args: vec![],
                }),
                InstrNode::new(Inst::Const {
                    ty: Ty::Unit,
                    value: Constant::Aggregate(vec![
                        Constant::SymbolAddr {
                            symbol: "target_11".into(),
                            addend: 0,
                        },
                        Constant::SymbolAddr {
                            symbol: "not_a_function".into(),
                            addend: 0,
                        },
                        Constant::FnDef(FuncId::new(17)),
                    ]),
                })
                .with_result(ValueId::new(0)),
            ],
        );
        assert_eq!(
            module_local_function_text_references(&module),
            std::collections::BTreeSet::from(["target_11".to_string(), "target_7".to_string()])
        );
        assert_eq!(
            module_local_function_identity_census(&module).direct_edges,
            1
        );
        // The string naming the Private `target_11` is a symbol address the
        // census counts; the string naming nothing is not.
        assert_eq!(
            module_local_function_identity_census(&module).symbol_addresses,
            1
        );
    }

    /// A `SymbolAddr` naming a module-local function is counted wherever it
    /// occurs (a body, a global initializer, nested in an aggregate), once
    /// per constant, and attributed to the body that makes it or, in a
    /// global initializer, to the function it names; a string naming an
    /// External function, a declaration-only name or nothing is not, and
    /// neither changes the `FuncId` census (`is_empty`).
    #[test]
    fn symbol_addresses_naming_module_local_functions_are_counted_and_attributed() {
        let symbol = |name: &str| Constant::SymbolAddr {
            symbol: name.into(),
            addend: 0,
        };
        let mut module = constant_census_fixture(Constant::Aggregate(vec![
            symbol("target_7"),
            Constant::Array(vec![symbol("target_7"), symbol("target_11")]),
            symbol("target_17"), // External: not module-local.
            symbol("nowhere"),
        ]));
        let census = module_local_function_identity_census(&module);
        assert_eq!(census.symbol_addresses, 3);
        assert!(census.is_empty(), "no FuncId identity: {census:?}");
        module.functions[2].blocks[0].body.insert(
            0,
            InstrNode::new(Inst::Const {
                ty: Ty::Unit,
                value: symbol("target_11"),
            })
            .with_result(ValueId::new(0)),
        );
        let attribution = super::module_local_function_identity_attribution(&module);
        assert_eq!(
            attribution.global_initializer_symbol_addresses,
            std::collections::BTreeMap::from([(FuncId::new(7), 2), (FuncId::new(11), 1)])
        );
        assert_eq!(
            attribution
                .bodies
                .get(&FuncId::new(17))
                .map(|census| census.symbol_addresses),
            Some(1)
        );
        let module_census = module_local_function_identity_census(&module);
        assert_eq!(module_census.symbol_addresses, 4);
        assert_eq!(
            attribution
                .bodies
                .values()
                .map(|census| census.symbol_addresses)
                .sum::<usize>()
                + attribution
                    .global_initializer_symbol_addresses
                    .values()
                    .sum::<usize>(),
            module_census.symbol_addresses
        );
        // A duplicated name never acquires guessed authority.
        let mut duplicate = module.functions[0].clone();
        duplicate.id = FuncId::new(23);
        module.functions.push(duplicate);
        assert_eq!(
            module_local_function_identity_census(&module).symbol_addresses,
            2
        );
    }

    /// The attributed census names the body that makes each reference (and,
    /// for a global initializer, the function it materializes), and its
    /// counts sum to the module census exactly.
    #[test]
    fn attributed_census_sums_to_the_module_census() {
        let mut module = constant_census_fixture(Constant::Aggregate(vec![
            Constant::FnDef(FuncId::new(11)),
            Constant::FnDef(FuncId::new(11)),
            Constant::FnDef(FuncId::new(17)), // Interposable: not counted.
        ]));
        let call = |callee: u32| {
            InstrNode::new(Inst::Call {
                callee: FuncId::new(callee),
                args: vec![],
            })
        };
        // `target_17` (External) calls both locals and takes one's address;
        // `target_11` calls `target_7`; `target_7` references nothing local.
        module.functions[2].blocks[0].body.splice(
            0..0,
            [
                call(7),
                call(11),
                call(17),
                InstrNode::new(Inst::Const {
                    ty: Ty::Unit,
                    value: Constant::FnDef(FuncId::new(7)),
                })
                .with_result(ValueId::new(0)),
            ],
        );
        module.functions[1].blocks[0].body.insert(0, call(7));
        let attribution = super::module_local_function_identity_attribution(&module);
        let census =
            |direct_edges, materialized_identities| super::ModuleLocalFunctionIdentityCensus {
                direct_edges,
                materialized_identities,
                symbol_addresses: 0,
            };
        assert_eq!(
            attribution.bodies,
            std::collections::BTreeMap::from([
                (FuncId::new(11), census(1, 0)),
                (FuncId::new(17), census(2, 1)),
            ])
        );
        assert_eq!(
            attribution.global_initializer_targets,
            std::collections::BTreeMap::from([(FuncId::new(11), 2)])
        );
        let module_census = module_local_function_identity_census(&module);
        let bodies = attribution.bodies.values();
        assert_eq!(
            bodies.clone().map(|c| c.direct_edges).sum::<usize>(),
            module_census.direct_edges
        );
        assert_eq!(
            bodies.map(|c| c.materialized_identities).sum::<usize>()
                + attribution
                    .global_initializer_targets
                    .values()
                    .sum::<usize>(),
            module_census.materialized_identities
        );
    }

    #[test]
    fn call_boundary_identity_census_keeps_direct_and_closure_edges() {
        let mut module = constant_census_fixture(Constant::Int(0));
        let closure_type = trust_ir::ClosureTyId::new(0);
        module.closure_types.push(trust_ir::ClosureTy {
            func: module.functions[0].ty,
            captures: vec![],
        });
        let indirect_signature = module.functions[1].ty;
        module.functions[2].blocks[0].body.splice(
            0..0,
            [
                InstrNode::new(Inst::CallCannotUnwind {
                    callee: FuncId::new(7),
                    args: vec![],
                }),
                InstrNode::new(Inst::Const {
                    ty: Ty::Closure(closure_type),
                    value: Constant::Closure {
                        func: FuncId::new(11),
                        captures: vec![],
                    },
                })
                .with_result(ValueId::new(0)),
                InstrNode::new(Inst::CallIndirectCannotUnwind {
                    callee: ValueId::new(0),
                    sig: indirect_signature,
                    args: vec![],
                    calling_conv: trust_ir::CallingConv::C,
                }),
                // A boundary does not turn a dynamic parameter into a known
                // closure or give a dangling FuncId a local definition.
                InstrNode::new(Inst::CallIndirectCannotUnwind {
                    callee: ValueId::new(99),
                    sig: indirect_signature,
                    args: vec![],
                    calling_conv: trust_ir::CallingConv::C,
                }),
                InstrNode::new(Inst::CallCannotUnwind {
                    callee: FuncId::new(999),
                    args: vec![],
                }),
            ],
        );
        let census = module_local_function_identity_census(&module);
        assert_eq!(census.direct_edges, 2);
        assert_eq!(census.materialized_identities, 0);
        assert_eq!(
            module_local_function_text_references(&module),
            std::collections::BTreeSet::from(["target_11".to_string(), "target_7".to_string()])
        );
        // This census is read-only; it must not reconstruct an ordinary call.
        assert!(matches!(
            module.functions[2].blocks[0].body[2].inst,
            Inst::CallIndirectCannotUnwind { .. }
        ));
    }

    #[test]
    fn selected_closure_application_cannot_evade_local_binding_census() {
        let mut module = constant_census_fixture(Constant::Int(0));
        let closure_type = trust_ir::ClosureTyId::new(0);
        module.closure_types.push(trust_ir::ClosureTy {
            func: module.functions[0].ty,
            captures: vec![],
        });
        let ty = Ty::Closure(closure_type);
        let literal = |id| {
            InstrNode::new(Inst::Const {
                ty: ty.clone(),
                value: Constant::Closure {
                    func: FuncId::new(7),
                    captures: vec![],
                },
            })
            .with_result(ValueId::new(id))
        };
        let indirect_signature = module.functions[0].ty;
        module.functions[2].blocks[0].body.splice(
            0..0,
            [
                literal(1),
                literal(2),
                InstrNode::new(Inst::Select {
                    ty,
                    cond: ValueId::new(99),
                    then_val: ValueId::new(1),
                    else_val: ValueId::new(2),
                })
                .with_result(ValueId::new(3)),
                InstrNode::new(Inst::CallIndirect {
                    callee: ValueId::new(3),
                    sig: indirect_signature,
                    args: vec![],
                    calling_conv: trust_ir::CallingConv::C,
                }),
            ],
        );
        assert_eq!(
            module_local_function_identity_census(&module).direct_edges,
            1
        );
        assert!(module_local_function_text_references(&module).contains("target_7"));
    }

    #[test]
    fn constant_identity_census_is_stack_safe_for_deep_and_wide_values() {
        let mut value = Constant::FnDef(FuncId::new(7));
        for level in 0..50_000 {
            value = if level % 2 == 0 {
                Constant::Sequence(vec![value])
            } else {
                Constant::Record(vec![("nested".into(), value)])
            };
        }
        // Other recursive operations, including Drop, are outside this walk.
        let deep = Box::leak(Box::new(constant_census_fixture(value)));
        assert_eq!(
            module_local_function_identity_census(deep).materialized_identities,
            1
        );

        let mut values = vec![Constant::FnDef(FuncId::new(17)); 50_000];
        *values.last_mut().unwrap() = Constant::FnDef(FuncId::new(11));
        let wide = constant_census_fixture(Constant::Array(values));
        assert_eq!(
            module_local_function_identity_census(&wide).materialized_identities,
            1
        );
    }

    #[test]
    fn dormant_report_has_no_allocation_and_authorizations_are_fixed_width() {
        let module = trust_ir::Module::new("empty");
        let report = ModuleTranslationValidationReport::new(&module);

        assert_eq!(report.exact_module_calls.len(), 0);
        assert_eq!(report.exact_module_calls.capacity(), 0);
        assert!(std::mem::size_of::<ExactModuleCallAuthorization>() <= 96);
        assert!(!std::mem::needs_drop::<ExactModuleCallAuthorization>());
    }
}
