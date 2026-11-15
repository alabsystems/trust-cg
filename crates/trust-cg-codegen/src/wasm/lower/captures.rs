// trust-cg-codegen/wasm/lower/captures.rs - which pointers outlive a bound
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Pointer-capture facts, used to decide whether an `Alloca` that executes
//! more than once per activation may keep one fixed frame slot, and which
//! fixed slots may share bytes. The analysis itself — offset and bits values,
//! displacements and their bounds, the capture walk and the per-parameter
//! facts of the callees defined here — is `trust_cg_irmid::escape`, shared
//! with the mid-end's constant-table promotion; its module documentation
//! states the facts and why they are sound. This file asks it the lane's
//! questions.

use std::collections::{HashMap, HashSet};

use trust_cg_irmid::escape::{self, Extent, FuncFacts, derive};
use trust_ir::{Constant, FuncId, Inst, Module, ValueId};

use super::WasmLowerError;

pub(super) use trust_cg_irmid::escape::ParamCaptures;

/// Compute [`ParamCaptures`] for every function defined in `module`, typed by
/// this lane's value typing (a function it cannot type derives no facts).
pub(super) fn param_captures(module: &Module, foreign: &HashSet<FuncId>) -> ParamCaptures {
    escape::param_captures(module, foreign, |func| {
        super::value_types(module, func).ok()
    })
}

impl super::Lowering<'_> {
    /// The walk's facts of this function.
    fn func_facts(&self) -> FuncFacts<'_> {
        FuncFacts::new(
            self.func,
            self.block_index.clone(),
            self.value_types.clone(),
        )
    }

    /// The extent of the allocation `Alloca` `inst` makes, when its element
    /// count is a constant (as `compute_frame` lays it out).
    fn alloca_extent(&self, facts: &FuncFacts<'_>, inst: &Inst) -> Extent {
        let Inst::Alloca { ty, count, .. } = inst else {
            return Extent::Unknown;
        };
        let count = match count {
            None => Some(1u64),
            Some(c) => match facts.def(*c) {
                Some(Inst::Const {
                    ty,
                    value: Constant::Int(n),
                }) if ty.is_integer() => u32::try_from(*n).ok().map(u64::from),
                _ => None,
            },
        };
        let size = super::layout::size_align(self.module, ty).ok().map(|s| s.0);
        match (count, size) {
            (Some(n), Some(s)) => n
                .checked_mul(u64::from(s))
                .map_or(Extent::Unknown, Extent::Bytes),
            _ => Extent::Unknown,
        }
    }

    /// The storage facts of this function's fixed-slot `Alloca`s `allocas`
    /// (see `Lowering::place_fixed_allocas`): every value derived from an
    /// allocation's pointer has that allocation among its roots, and an
    /// allocation whose pointer may be captured is pinned.
    pub(super) fn alloca_storage(
        &self,
        allocas: &[ValueId],
    ) -> Result<super::storage::Storage, WasmLowerError> {
        let facts = self.func_facts();
        let mut roots: HashMap<ValueId, Vec<ValueId>> = HashMap::new();
        let mut pinned: HashSet<ValueId> = HashSet::new();
        for &a in allocas {
            let extent = facts
                .def(a)
                .map_or(Extent::Unknown, |inst| self.alloca_extent(&facts, inst));
            let d = derive(&facts, self.captures, extent, &[a]);
            if d.captured {
                pinned.insert(a);
                continue;
            }
            for v in d.values {
                roots.entry(v).or_default().push(a);
            }
        }
        for list in roots.values_mut() {
            list.sort_unstable();
            list.dedup();
        }
        Ok(super::storage::Storage { roots, pinned })
    }

    /// The `Alloca` results that must get fresh storage on every execution:
    /// those in a block that can run more than once per activation whose
    /// pointer an earlier execution may still observe (module docs).
    pub(super) fn allocas_needing_fresh_storage(&self) -> Result<HashSet<ValueId>, WasmLowerError> {
        let mut fresh = HashSet::new();
        if !self.cyclic.iter().any(|c| *c) {
            return Ok(fresh);
        }
        let entry = self.idx(self.func.entry)?;
        let facts = self.func_facts();
        for (bi, block) in self.func.blocks.iter().enumerate() {
            if !self.cyclic[bi] {
                continue;
            }
            for node in &block.body {
                if !matches!(node.inst, Inst::Alloca { .. }) {
                    continue;
                }
                let Some(&a) = node.results.first() else {
                    continue;
                };
                let extent = self.alloca_extent(&facts, &node.inst);
                let d = derive(&facts, self.captures, extent, &[a]);
                let escapes_edge = d
                    .param_blocks
                    .iter()
                    .any(|&p| p == bi || !Self::dominates(&self.idom, bi, p, entry));
                if d.captured || escapes_edge {
                    fresh.insert(a);
                }
            }
        }
        Ok(fresh)
    }
}
