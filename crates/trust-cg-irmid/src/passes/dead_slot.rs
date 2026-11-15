// trust-cg-irmid/passes/dead_slot.rs - stores to a slot nothing reads
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! An unobservable slot (`slots.rs`) with no load left — typically after
//! store forwarding replaced every one — is written but never read, so its
//! stores go. Dead-code elimination then removes the `gep`s and the
//! `alloca`, and the frame loses the slot. Each removed store is labelled a
//! refinement: it may be undefined on some input (a misaligned address),
//! which the target no longer is.

use trust_cg_verify::trust_ir_mid_tv::{DeadSlot, DeadSlotWitness, PassWitness};
use trust_ir::Function;

use super::slots::unobservable_slots;
use super::{MidPass, PassContext};

pub(crate) struct DeadSlotRemoval;

impl MidPass for DeadSlotRemoval {
    fn name(&self) -> &'static str {
        "dead_slot"
    }

    fn run(&self, cx: &PassContext<'_>, func: &Function) -> Option<(Function, PassWitness)> {
        let mut slots = Vec::new();
        let mut doomed = std::collections::HashSet::new();
        for slot in unobservable_slots(cx.module, func) {
            if slot.accesses.is_empty() || slot.accesses.iter().any(|a| !a.store) {
                continue;
            }
            let stores: Vec<_> = slot
                .accesses
                .iter()
                .map(|a| (func.blocks[a.at.0].id, a.at.1))
                .collect();
            doomed.extend(slot.accesses.iter().map(|a| a.at));
            slots.push(DeadSlot {
                alloca: slot.alloca,
                stores,
            });
        }
        if slots.is_empty() {
            return None;
        }
        let mut out = func.clone();
        for (bi, block) in out.blocks.iter_mut().enumerate() {
            let mut ni = 0usize;
            block.body.retain(|_| {
                let keep = !doomed.contains(&(bi, ni));
                ni += 1;
                keep
            });
        }
        Some((out, PassWitness::DeadSlot(DeadSlotWitness { slots })))
    }
}
