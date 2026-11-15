// Copyright 2026 Andrew Yates | Apache-2.0
//! Actual Alloca-to-slot inputs retained at the adapter boundary.
//!
//! These identities and dimensions grant no allocation validity, freshness,
//! lifetime, private-frame separation, physical placement or proof grade.
//! Recheck against the exact backend adapter input and retained LIR before
//! consumption. Earlier Core/ABI/dialect transforms and original Rust/THIR
//! source custody need independent binding; these records do not prove them.

use crate::{
    Function, StackSlotInfo,
    instructions::{Opcode, Value},
};
use trust_ir::{BlockId, FuncId, Inst, Module, Ty, ValueId};

/// How the adapter obtained the emitted slot extent. Bounded-use inference is
/// deliberately distinct from a statically constant source allocation count.
#[derive(Clone, Copy, Debug, PartialEq, Eq, serde::Serialize)]
pub enum AllocationExtent {
    One,
    Constant(i128),
    BoundedUses,
    Runtime,
}

/// Preserve the actual allocation sizing route; a natural LIR carrier can
/// over-allocate a declared packed image and is not that image's layout proof.
#[derive(Clone, Copy, Debug, PartialEq, Eq, serde::Serialize)]
pub enum AllocationGeometryBasis {
    StorageLayout,
    ValueCarrier,
}

/// A static source instruction identity, not a runtime AllocId. Re-executing
/// the instruction (for example in a loop) needs separate instance/lifetime
/// reasoning. Serialization is DATA only and cannot mint an AOT binding.
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize)]
pub struct SourceStackAllocation {
    pub(crate) block: BlockId,
    pub(crate) instruction: u32,
    pub(crate) origin: trust_cg_ir::TrustIrInstId,
    pub(crate) source: ValueId,
    pub(crate) ty: Ty,
    pub(crate) count: Option<ValueId>,
    pub(crate) explicit_align: Option<u64>,
    pub(crate) result: Value,
    pub(crate) slot: u32,
    pub(crate) element_bytes: u32,
    pub(crate) element_align: u32,
    pub(crate) extent: AllocationExtent,
    pub(crate) geometry_basis: AllocationGeometryBasis,
    pub(crate) geometry: StackSlotInfo,
}

impl SourceStackAllocation {
    pub fn source_block(&self) -> BlockId {
        self.block
    }
    pub fn source_instruction(&self) -> u32 {
        self.instruction
    }
    pub fn source_origin(&self) -> trust_cg_ir::TrustIrInstId {
        self.origin
    }
    pub fn source_result(&self) -> ValueId {
        self.source
    }
    pub fn source_type(&self) -> &Ty {
        &self.ty
    }
    pub fn source_count(&self) -> Option<ValueId> {
        self.count
    }
    pub fn explicit_align(&self) -> Option<u64> {
        self.explicit_align
    }
    pub fn lir_result(&self) -> Value {
        self.result
    }
    pub fn stack_slot(&self) -> u32 {
        self.slot
    }
    pub fn element_bytes(&self) -> u32 {
        self.element_bytes
    }
    pub fn element_align(&self) -> u32 {
        self.element_align
    }
    pub fn extent(&self) -> AllocationExtent {
        self.extent
    }
    pub fn geometry_basis(&self) -> AllocationGeometryBasis {
        self.geometry_basis
    }
    pub fn geometry(&self) -> StackSlotInfo {
        self.geometry
    }

    /// Use the owning IR's canonical codec for the exact type image, including
    /// nominal IDs. The containing source module must separately bind the
    /// definitions those IDs name; this small image supplies no layout facts.
    pub(crate) fn type_identity(&self) -> trust_ir::proof::ProofDigest {
        let mut image = Module::new("");
        image.func_types.push(trust_ir::FuncTy {
            params: vec![self.ty.clone()],
            returns: vec![],
            abi: None,
            is_vararg: false,
        });
        image.stable_digest_under(trust_ir::imports::IdentityScheme::V3)
    }
}

/// Complete source Alloca census for one adapter input function. No wire
/// deserializer or public minting constructor is provided.
#[derive(Clone, Debug, Default, PartialEq, Eq, serde::Serialize)]
pub struct SourceStackAllocations {
    pub(crate) function: Option<FuncId>,
    pub(crate) symbol: String,
    pub(crate) records: Vec<SourceStackAllocation>,
}

impl SourceStackAllocations {
    pub fn source_function(&self) -> Option<FuncId> {
        self.function
    }
    pub fn symbol(&self) -> &str {
        &self.symbol
    }
    pub fn records(&self) -> &[SourceStackAllocation] {
        &self.records
    }

    /// Reconstruct the complete source census, including unreachable blocks.
    /// Equal sizes or names cannot substitute another Alloca's actual SSA ID.
    pub fn validate_source(&self, module: &Module) -> Result<(), String> {
        let id = self
            .function
            .ok_or("source allocation owner was not retained")?;
        let mut functions = module.functions.iter().filter(|f| f.id == id);
        let function = functions
            .next()
            .ok_or("source allocation function missing")?;
        if functions.next().is_some() || function.name != self.symbol {
            return Err("source allocation function identity differs".into());
        }
        self.validate_source_function(function)
    }

    /// Check only this function's logical Alloca census and count images.
    /// This does not bind nominal definitions or target/module tables; an AOT
    /// consumer must also use the whole-module/object binding.
    pub fn validate_source_function(&self, function: &trust_ir::Function) -> Result<(), String> {
        if self.function != Some(function.id) || self.symbol != function.name {
            return Err("source allocation function identity differs".into());
        }
        let mut index = 0usize;
        let mut origin = 0u32;
        let mut results = std::collections::BTreeSet::new();
        let mut blocks = std::collections::BTreeSet::new();
        let mut values = std::collections::BTreeSet::new();
        for block in &function.blocks {
            if !blocks.insert(block.id.index()) {
                return Err("source allocation block identity is ambiguous".into());
            }
            for value in block
                .params
                .iter()
                .map(|(v, _)| v)
                .chain(block.body.iter().flat_map(|n| &n.results))
            {
                if !values.insert(value.index()) {
                    return Err("source allocation SSA identity is ambiguous".into());
                }
            }
        }
        let counts: Vec<_> = self
            .records
            .iter()
            .filter_map(|record| record.count)
            .collect();
        let constants = crate::adapter::replay_alloca_counts(function, &counts);
        for block in &function.blocks {
            for (instruction, node) in block.body.iter().enumerate() {
                let expected_origin = origin;
                origin = origin
                    .checked_add(1)
                    .ok_or("source instruction origin overflows")?;
                let Inst::Alloca { ty, count, align } = &node.inst else {
                    continue;
                };
                let record = self
                    .records
                    .get(index)
                    .ok_or("source Alloca is unrecorded")?;
                if node.results.as_slice() != [record.source]
                    || !results.insert(record.source.index())
                    || record.block != block.id
                    || usize::try_from(record.instruction).ok() != Some(instruction)
                    || record.origin.0 != expected_origin
                    || record.ty != *ty
                    || record.count != *count
                    || record.explicit_align != *align
                {
                    return Err("source Alloca identity/type/count/alignment differs".into());
                }
                let constant = count
                    .and_then(|id| constants.get(&id).copied().flatten())
                    .map(i128::from);
                let extent_matches = match (count, constant, record.extent) {
                    (None, None, AllocationExtent::One) => {
                        record.geometry.size == record.element_bytes
                    }
                    (Some(_), Some(n), AllocationExtent::Constant(actual)) if n == actual => {
                        u128::try_from(n)
                            .ok()
                            .and_then(|n| n.checked_mul(u128::from(record.element_bytes)))
                            == Some(u128::from(record.geometry.size))
                    }
                    (Some(_), None, AllocationExtent::BoundedUses | AllocationExtent::Runtime) => {
                        true
                    }
                    _ => false,
                };
                if !extent_matches {
                    return Err("source Alloca count/extent differs".into());
                }
                index += 1;
            }
        }
        if index != self.records.len() {
            return Err("source allocation census has extra records".into());
        }
        Ok(())
    }

    /// Validate actual emitted StackAddr occurrences and slot geometry after
    /// any shared LIR preparation. Unsupported/remapped transports refuse.
    pub fn validate_lir(&self, function: &Function) -> Result<(), String> {
        if function.name != self.symbol {
            return Err("source allocation LIR function differs".into());
        }
        let wanted: std::collections::BTreeSet<_> =
            self.records.iter().map(|r| r.result.0).collect();
        if wanted.len() != self.records.len() {
            return Err("source allocation LIR result identity is ambiguous".into());
        }
        let mut definitions = std::collections::BTreeMap::new();
        for (block, body) in &function.blocks {
            for (index, instruction) in body.instructions.iter().enumerate() {
                for result in &instruction.results {
                    if wanted.contains(&result.0)
                        && definitions
                            .insert(result.0, (block, index, instruction))
                            .is_some()
                    {
                        return Err("source allocation StackAddr identity differs".into());
                    }
                }
            }
        }
        let mut slots = std::collections::BTreeSet::new();
        for record in &self.records {
            if !slots.insert(record.slot)
                || function.stack_slots.get(record.slot as usize) != Some(&record.geometry)
            {
                return Err("source allocation slot identity/geometry differs".into());
            }
            let (block, index, definition) = definitions
                .get(&record.result.0)
                .copied()
                .ok_or("source allocation StackAddr missing")?;
            if definition.results.as_slice() != [record.result]
                || definition.opcode != (Opcode::StackAddr { slot: record.slot })
                || !definition.args.is_empty()
                || function
                    .trust_ir_origins
                    .get(block)
                    .and_then(|rows| rows.get(index))
                    != Some(&Some(record.origin))
            {
                return Err("source allocation StackAddr identity differs".into());
            }
        }
        Ok(())
    }
}

#[cfg(test)]
#[path = "source_stack_allocations_tests.rs"]
mod tests;
