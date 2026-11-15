// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Shared byte-interval DEMANDS, not permission or temporal initialization.
//! Splitting/coalescing may cover a union of original intervals, but matching
//! status/final bytes never erases dead reads or write-restore demands.

use crate::smt::SmtExpr as E;

pub(crate) fn valid_access(address: &E, byte_width: u32, alignment: u64) -> E {
    let nonwrapping = address
        .clone()
        .bvule(E::bv_const(u64::MAX - u64::from(byte_width - 1), 64));
    // Every byte address meets unit alignment. Keep the nonwrapping demand;
    // avoid encoding an unrelated symbolic `address & 0 = 0` theorem here.
    if alignment == 1 {
        nonwrapping
    } else {
        nonwrapping.and_expr(
            address
                .clone()
                .bvand(E::bv_const(alignment - 1, 64))
                .eq_expr(E::bv_const(0, 64)),
        )
    }
}

pub(crate) fn demand(
    target_guard: (&E, usize),
    target_address: (&E, usize),
    width: u32,
    alignment: u64,
    originals: impl Iterator<Item = (E, usize, E, usize, u32, u64)>,
    max_nodes: usize,
) -> Result<(E, usize), &'static str> {
    let observe = E::var("observe", 64);
    let in_interval = |address: &E, width: u32| {
        observe.clone().bvuge(address.clone()).and_expr(
            observe
                .clone()
                .bvsub(address.clone())
                .bvult(E::bv_const(u64::from(width), 64)),
        )
    };
    let mut coverage = E::BoolConst(false);
    let mut nodes = 1usize;
    for (guard, guard_nodes, address, address_nodes, original_width, original_alignment) in
        originals
    {
        if original_alignment < alignment {
            continue;
        }
        nodes = address_nodes
            .checked_mul(2)
            .and_then(|n| n.checked_add(9))
            .and_then(|n| n.checked_add(guard_nodes))
            .and_then(|n| n.checked_add(nodes))
            .filter(|n| *n <= max_nodes)
            .ok_or("scalar-memory access coverage")?;
        coverage = coverage.or_expr(guard.and_expr(in_interval(&address, original_width)));
    }
    nodes = target_guard
        .1
        .checked_mul(2)
        .and_then(|n| {
            target_address
                .1
                .checked_mul(4)
                .and_then(|a| a.checked_add(n))
        })
        .and_then(|n| n.checked_add(24))
        .and_then(|n| n.checked_add(nodes))
        .filter(|n| *n <= max_nodes)
        .ok_or("scalar-memory access demand")?;
    let byte_is_needed = target_guard
        .0
        .clone()
        .and_expr(in_interval(target_address.0, width));
    let valid =
        target_guard
            .0
            .clone()
            .not_expr()
            .or_expr(valid_access(target_address.0, width, alignment));
    Ok((
        valid.and_expr(byte_is_needed.not_expr().or_expr(coverage)),
        nodes,
    ))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::smt::{EvalEnv, EvalResult};

    #[test]
    fn unit_alignment_retains_full_nonwrapping_extent_and_stricter_alignment() {
        for width in [1, 4, 8] {
            for address in [0, 1, 7, 8, u64::MAX - 7, u64::MAX - 6, u64::MAX] {
                let term = E::bv_const(address, 64);
                assert_eq!(
                    valid_access(&term, width, 1)
                        .try_eval(&EvalEnv::default())
                        .unwrap(),
                    EvalResult::Bool(address <= u64::MAX - u64::from(width - 1))
                );
                assert_eq!(
                    valid_access(&term, width, 8)
                        .try_eval(&EvalEnv::default())
                        .unwrap(),
                    EvalResult::Bool(
                        address <= u64::MAX - u64::from(width - 1) && address % 8 == 0
                    )
                );
            }
        }
    }
}
