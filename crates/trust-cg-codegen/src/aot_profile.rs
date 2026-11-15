//! AOT profile instrumentation: admit, plan, then commit code and metadata.
//!
//! Each block receives five instructions using four fresh registers, after its
//! leading PHIs. The metadata lock spans planning and commit; returned errors
//! change neither the function nor the map. Allocation failure/unwinding is not
//! a rollback contract. Runtime counters remain non-atomic load/add/store sums.

use std::collections::BTreeSet;
use std::ops::Range;
use std::sync::Mutex;

use thiserror::Error;
use trust_cg_ir::regs::{RegClass, VReg};
use trust_cg_ir::{AArch64Opcode as Opcode, InstId, MachFunction, MachInst, MachOperand};
use trust_cg_opt::pgo::{CounterMap, CounterSite, counter_symbol};

/// Module-level u64 counter array defined by a profile-generation object.
pub const PGO_COUNTER_ARRAY_SYMBOL: &str = "__tcg_pgo_counters";
/// Module-level u64 site count consumed by the profile dump runtime.
pub const PGO_NSITES_SYMBOL: &str = "__tcg_pgo_nsites";

// LDR/STR unsigned imm12 scaled by eight: indices 0 through 4095.
const MAX_COUNTER_INDEX: u128 = 4095;
const REGS_PER_BLOCK: u32 = 4;
const INSTS_PER_BLOCK: usize = 5;

/// Refusal before publishing AOT counter instructions or metadata.
#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum AotProfileError {
    #[error("AOT profile metadata lock is poisoned for `{function}`")]
    PoisonedCounterMap { function: String },
    #[error("invalid AOT profile metadata for `{function}`: {detail}")]
    InvalidCounterMap { function: String, detail: String },
    #[error("invalid AOT profile input `{function}`: {detail}")]
    InvalidFunction { function: String, detail: String },
    #[error("AOT profile register IDs exhausted for `{function}` (requires {required} fresh IDs)")]
    VirtualRegisterExhausted { function: String, required: u32 },
    #[error("AOT profile instruction IDs exhausted for `{function}`")]
    InstructionIdExhausted { function: String },
    #[error(
        "AOT profile counter index {index} for `{function}` exceeds {max} (LdrRI/StrRI scaled offset ceiling)"
    )]
    CounterIndexTooLarge {
        function: String,
        index: u128,
        max: u128,
    },
}

struct PlannedBlock {
    block: usize,
    insert_at: usize,
    ids: [InstId; INSTS_PER_BLOCK],
    instructions: [MachInst; INSTS_PER_BLOCK],
    site: CounterSite,
}

pub(crate) fn inject(
    function: &mut MachFunction,
    sink: &Mutex<CounterMap>,
) -> Result<(), AotProfileError> {
    // No instrumentation requested by this layout: preserve the previous no-op
    // behavior without reserving IDs or consulting an unused metadata sink.
    if function.block_order.is_empty() {
        return Ok(());
    }
    let mut map = sink
        .lock()
        .map_err(|_| AotProfileError::PoisonedCounterMap {
            function: function.name.clone(),
        })?;
    let count = function.block_order.len();
    let last_index = map.sites.len() as u128 + count as u128 - 1;
    if last_index > MAX_COUNTER_INDEX {
        return Err(AotProfileError::CounterIndexTooLarge {
            function: function.name.clone(),
            index: last_index,
            max: MAX_COUNTER_INDEX,
        });
    }
    validate_counter_map(&map, function)?;
    let positions = insertion_positions(function)?;

    // The admitted counter ceiling bounds count to 4096, including both
    // multiplications and all counter-index/offset casts below.
    let required = count as u32 * REGS_PER_BLOCK;
    let registers = register_range(function, required).ok_or_else(|| {
        AotProfileError::VirtualRegisterExhausted {
            function: function.name.clone(),
            required,
        }
    })?;
    let arena =
        instruction_range(function.insts.len(), count * INSTS_PER_BLOCK).ok_or_else(|| {
            AotProfileError::InstructionIdExhausted {
                function: function.name.clone(),
            }
        })?;
    let mut plan = Vec::with_capacity(count);
    for (index, (&block_id, insert_at)) in function.block_order.iter().zip(positions).enumerate() {
        // Both ranges were checked for the ENTIRE function before any edits.
        let first_reg = registers.start + index as u32 * REGS_PER_BLOCK;
        let [page, addr, cur, next] =
            std::array::from_fn(|offset| VReg::new(first_reg + offset as u32, RegClass::Gpr64));
        let counter_index = (map.sites.len() + index) as u32;
        let byte_offset = i64::from(counter_index) * 8;
        let first_inst = arena.start + index * INSTS_PER_BLOCK;
        plan.push(PlannedBlock {
            block: block_id.0 as usize,
            insert_at,
            ids: std::array::from_fn(|offset| InstId((first_inst + offset) as u32)),
            instructions: [
                MachInst::new(
                    Opcode::Adrp,
                    vec![
                        MachOperand::VReg(page),
                        MachOperand::Symbol(PGO_COUNTER_ARRAY_SYMBOL.into()),
                    ],
                ),
                MachInst::new(
                    Opcode::AddPCRel,
                    vec![
                        MachOperand::VReg(addr),
                        MachOperand::VReg(page),
                        MachOperand::Symbol(PGO_COUNTER_ARRAY_SYMBOL.into()),
                    ],
                ),
                MachInst::new(
                    Opcode::LdrRI,
                    vec![
                        MachOperand::VReg(cur),
                        MachOperand::VReg(addr),
                        MachOperand::Imm(byte_offset),
                    ],
                ),
                MachInst::new(
                    Opcode::AddRI,
                    vec![
                        MachOperand::VReg(next),
                        MachOperand::VReg(cur),
                        MachOperand::Imm(1),
                    ],
                ),
                MachInst::new(
                    Opcode::StrRI,
                    vec![
                        MachOperand::VReg(next),
                        MachOperand::VReg(addr),
                        MachOperand::Imm(byte_offset),
                    ],
                ),
            ],
            site: CounterSite {
                function: function.name.clone(),
                block_id: block_id.0,
                counter_index,
                symbol: counter_symbol(&function.name, block_id.0),
            },
        });
    }

    // No fallible admission remains. Distinct, valid blocks and positions were
    // checked against this same exclusively borrowed function; each is edited
    // once. Appending preserves old instruction IDs and their sidecars.
    for block in plan {
        function.insts.extend(block.instructions);
        function.blocks[block.block]
            .insts
            .splice(block.insert_at..block.insert_at, block.ids);
        map.sites.push(block.site);
    }
    function.next_vreg = registers.end;
    Ok(())
}

fn validate_counter_map(map: &CounterMap, function: &MachFunction) -> Result<(), AotProfileError> {
    let invalid = |detail| AotProfileError::InvalidCounterMap {
        function: function.name.clone(),
        detail,
    };
    let mut keys = BTreeSet::new();
    for (index, site) in map.sites.iter().enumerate() {
        if site.counter_index as usize != index {
            return Err(invalid(format!(
                "site {index} has non-dense counter index {}",
                site.counter_index
            )));
        }
        if !keys.insert((site.function.as_str(), site.block_id)) {
            return Err(invalid(format!(
                "duplicate site {}:bb{}",
                site.function, site.block_id
            )));
        }
    }
    for block in &function.block_order {
        if keys.contains(&(function.name.as_str(), block.0)) {
            return Err(invalid(format!(
                "site {}:bb{} already exists",
                function.name, block.0
            )));
        }
    }
    Ok(())
}

fn insertion_positions(function: &MachFunction) -> Result<Vec<usize>, AotProfileError> {
    let invalid = |detail| AotProfileError::InvalidFunction {
        function: function.name.clone(),
        detail,
    };
    if !function.block_order.contains(&function.entry) {
        return Err(invalid("entry block is absent from the layout".into()));
    }
    let mut blocks = BTreeSet::new();
    let mut instructions = BTreeSet::new();
    let mut positions = Vec::with_capacity(function.block_order.len());
    for &id in &function.block_order {
        if !blocks.insert(id) {
            return Err(invalid(format!("block {id:?} appears more than once")));
        }
        let block = function
            .blocks
            .get(id.0 as usize)
            .ok_or_else(|| invalid(format!("missing block {id:?}")))?;
        let mut insert_at = 0;
        for (position, &inst_id) in block.insts.iter().enumerate() {
            let inst = function
                .insts
                .get(inst_id.0 as usize)
                .ok_or_else(|| invalid(format!("missing instruction {inst_id:?} in {id:?}")))?;
            if !instructions.insert(inst_id) {
                return Err(invalid(format!(
                    "instruction {inst_id:?} appears more than once"
                )));
            }
            if position == insert_at && inst.opcode == Opcode::Phi {
                insert_at += 1;
            } else if inst.opcode == Opcode::Phi {
                return Err(invalid(format!("non-leading PHI {inst_id:?} in {id:?}")));
            }
        }
        positions.push(insert_at);
    }
    Ok(positions)
}

fn register_range(function: &MachFunction, count: u32) -> Option<Range<u32>> {
    let max_existing = function
        .insts
        .iter()
        .flat_map(|inst| &inst.operands)
        .filter_map(|operand| match operand {
            MachOperand::VReg(reg) => Some(reg.id),
            _ => None,
        })
        .chain(function.noalias_params.iter().copied())
        .max();
    let first = match max_existing {
        Some(id) => function.next_vreg.max(id.checked_add(1)?),
        None => function.next_vreg,
    };
    Some(first..first.checked_add(count)?)
}

fn instruction_range(first: usize, count: usize) -> Option<Range<usize>> {
    let end = first.checked_add(count)?;
    if count != 0 {
        u32::try_from(end - 1).ok()?;
    }
    Some(first..end)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn aot_counter_boundary_instruction_range_checks_last_id_without_large_allocations() {
        assert_eq!(instruction_range(7, 5), Some(7..12));
        if let Some(end) = (u32::MAX as usize).checked_add(1) {
            assert_eq!(
                instruction_range(u32::MAX as usize, 1),
                Some(u32::MAX as usize..end)
            );
            assert_eq!(instruction_range(u32::MAX as usize, 2), None);
            assert_eq!(instruction_range(end, 1), None);
        }
        assert_eq!(instruction_range(usize::MAX, 1), None);
    }
}
