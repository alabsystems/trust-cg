// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Current-memory effects in the EXISTING target observation driver. These
//! retain every access demand, including discarded loads and restored writes.
//! They neither establish at-access initialization nor caller permission.

use super::*;

fn access(address: &E, byte_width: u32, alignment: u64) -> bool {
    address.sort() == SmtSort::BitVec(64)
        && matches!(byte_width, 4 | 8)
        && alignment.is_power_of_two()
        && alignment <= u64::from(byte_width)
}

fn destination(index: usize) -> bool {
    index < 18 || index == 31
}

pub(super) fn validate(step: &Step) -> Result<(), ReadOnlyTargetError> {
    let valid = match step {
        Step::MemoryLoad {
            destination: d,
            address,
            byte_width,
            alignment,
        } => destination(*d) && access(address, *byte_width, *alignment),
        Step::MemoryStore {
            address,
            value,
            byte_width,
            alignment,
        } => {
            access(address, *byte_width, *alignment)
                && value.sort() == SmtSort::BitVec(*byte_width * 8)
        }
        Step::LoadPair {
            destinations,
            address,
            byte_width,
            alignment,
        } => {
            destinations.iter().all(|d| destination(*d))
                && destinations[0] != destinations[1]
                && access(address, *byte_width, *alignment)
        }
        _ => false,
    };
    if valid {
        Ok(())
    } else {
        Err(ReadOnlyTargetError::Control(
            "unsupported scalar-memory effect",
        ))
    }
}

fn bind(
    definitions: &mut Definitions,
    value: Term,
    sort: SmtSort,
) -> Result<Term, ReadOnlyTargetError> {
    definitions
        .bind(value.expr, value.nodes, sort)
        .map(Term::leaf)
        .map_err(definition_error)
}

fn preflight(
    state: &State,
    pending: &[State],
    definitions: &Definitions,
    definitions_extra: usize,
    destinations: &[usize],
) -> Result<(), ReadOnlyTargetError> {
    definitions
        .preflight_occurrences(destinations.iter().filter(|d| **d != 31).count())
        .map_err(definition_error)?;
    let prior = destinations
        .iter()
        .filter(|d| **d != 31)
        .map(|d| state.x[*d].as_ref().map_or(0, |t| t.nodes))
        .sum::<usize>();
    let next = bounded_sum(
        [
            state_nodes(state)? - prior,
            destinations.iter().filter(|d| **d != 31).count(),
        ],
        MAX_STATE_NODES,
    )?;
    let defs = bounded_sum([definitions.nodes, definitions_extra], MAX_STATE_NODES)?;
    live_states_with_definitions(pending, next, defs)
}

fn load_nodes(
    memory: &Term,
    address: &Term,
    byte_width: u32,
) -> Result<usize, ReadOnlyTargetError> {
    let n = byte_width as usize;
    let nodes = bounded_sum([memory.nodes, address.nodes], MAX_TERM_NODES)?
        .checked_mul(n)
        .and_then(|v| v.checked_add(7 * n - 5))
        .and_then(|v| v.checked_add(usize::from(byte_width == 4)))
        .filter(|v| *v <= MAX_TERM_NODES)
        .ok_or(ReadOnlyTargetError::Budget("current-memory load expansion"))?;
    Ok(nodes)
}

fn load(memory: &Term, address: &Term, byte_width: u32, nodes: usize) -> Term {
    let value = encode_load_le(&memory.expr, &address.expr, byte_width);
    Term {
        expr: if byte_width == 4 {
            value.zero_ext(32)
        } else {
            value
        },
        nodes,
    }
}

fn read(state: &State, address: Term, byte_width: u32, alignment: u64, lane: usize) -> Read {
    Read {
        step: state.pc,
        guard: state.guard.clone(),
        address,
        byte_width,
        alignment,
        lane,
    }
}

pub(super) fn observe(
    step: &Step,
    state: &mut State,
    pending: &[State],
    observed: &mut Observations,
    definitions: &mut Definitions,
) -> Result<(), ReadOnlyTargetError> {
    validate(step)?;
    let current = state.memory.clone().ok_or(ReadOnlyTargetError::Control(
        "missing current target memory",
    ))?;
    match step {
        Step::MemoryLoad {
            destination,
            address,
            byte_width,
            alignment,
        } => {
            if observed.reads.len() >= MAX_READS {
                return Err(ReadOnlyTargetError::Budget("target read demands"));
            }
            let address = compose(address, state)?;
            let nodes = load_nodes(&current, &address, *byte_width)?;
            preflight(
                state,
                pending,
                definitions,
                if *destination == 31 { 0 } else { nodes + 2 },
                &[*destination],
            )?;
            let value = if *destination == 31 {
                None
            } else {
                Some(bind(
                    definitions,
                    load(&current, &address, *byte_width, nodes),
                    SmtSort::BitVec(64),
                )?)
            };
            observed
                .reads
                .push(read(state, address, *byte_width, *alignment, 0));
            if let Some(value) = value {
                state.x[*destination] = Some(value);
            }
        }
        Step::LoadPair {
            destinations,
            address,
            byte_width,
            alignment,
        } => {
            if observed
                .reads
                .len()
                .checked_add(2)
                .is_none_or(|n| n > MAX_READS)
            {
                return Err(ReadOnlyTargetError::Budget("target paired read demands"));
            }
            // Compose the base ONCE from the before state. Both lane values
            // use the SAME current memory, even if a destination aliases it.
            let first = compose(address, state)?;
            let second = Term {
                nodes: bounded_sum([first.nodes, 2], MAX_TERM_NODES)?,
                expr: first
                    .expr
                    .clone()
                    .bvadd(E::bv_const(u64::from(*byte_width), 64)),
            };
            let addresses = [first, second];
            let nodes = [
                load_nodes(&current, &addresses[0], *byte_width)?,
                load_nodes(&current, &addresses[1], *byte_width)?,
            ];
            let extra = bounded_sum(
                (0..2)
                    .filter(|i| destinations[*i] != 31)
                    .map(|i| nodes[i] + 2),
                MAX_STATE_NODES,
            )?;
            preflight(state, pending, definitions, extra, destinations)?;
            let mut values = [None, None];
            for i in 0..2 {
                if destinations[i] != 31 {
                    values[i] = Some(bind(
                        definitions,
                        load(&current, &addresses[i], *byte_width, nodes[i]),
                        SmtSort::BitVec(64),
                    )?);
                }
            }
            for (lane, address) in addresses.into_iter().enumerate() {
                observed
                    .reads
                    .push(read(state, address, *byte_width, *alignment, lane));
            }
            for (destination, value) in destinations.iter().zip(values) {
                if let Some(value) = value {
                    state.x[*destination] = Some(value);
                }
            }
        }
        Step::MemoryStore {
            address,
            value,
            byte_width,
            alignment,
        } => {
            if observed.writes.len() >= MAX_READS {
                return Err(ReadOnlyTargetError::Budget("target write demands"));
            }
            // Address and data both read the BEFORE state, never a new memory
            // version or a register retired before its last use.
            let address = compose(address, state)?;
            let value = compose(value, state)?;
            let n = *byte_width as usize;
            let nodes = bounded_sum([address.nodes, value.nodes], MAX_TERM_NODES)?
                .checked_mul(n)
                .and_then(|v| v.checked_add(current.nodes))
                .and_then(|v| v.checked_add(4 * n - 2))
                .filter(|v| *v <= MAX_TERM_NODES)
                .ok_or(ReadOnlyTargetError::Budget(
                    "current-memory store expansion",
                ))?;
            preflight(state, pending, definitions, nodes + 2, &[])?;
            definitions
                .preflight_occurrences(1)
                .map_err(definition_error)?;
            let next = bind(
                definitions,
                Term {
                    expr: encode_store_le(&current.expr, &address.expr, &value.expr, *byte_width),
                    nodes,
                },
                memory_sort(),
            )?;
            observed
                .writes
                .push(read(state, address, *byte_width, *alignment, 0));
            state.memory = Some(Arc::new(next));
        }
        _ => return Err(ReadOnlyTargetError::Control("not a scalar-memory step")),
    }
    Ok(())
}
