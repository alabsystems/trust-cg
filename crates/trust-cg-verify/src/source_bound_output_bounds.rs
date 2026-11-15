// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Evaluate literal bounds probes without borrowing their proof annotations.
//! The private view removes only nontrapping guards and unused comparisons;
//! the enclosing checker retains the complete original source and LIR.

use std::collections::{HashMap, HashSet};
use trust_cg_lower::{
    Function, Type,
    instructions::{IntCC, Opcode as L, Value},
};
use trust_ir::ICmpOp;

pub(super) fn compare(op: ICmpOp, left: u64, right: u64) -> bool {
    match op {
        ICmpOp::Eq => left == right,
        ICmpOp::Ne => left != right,
        ICmpOp::Ult => left < right,
        ICmpOp::Ule => left <= right,
        ICmpOp::Ugt => left > right,
        ICmpOp::Uge => left >= right,
        ICmpOp::Slt => (left as i64) < (right as i64),
        ICmpOp::Sle => (left as i64) <= (right as i64),
        ICmpOp::Sgt => (left as i64) > (right as i64),
        ICmpOp::Sge => (left as i64) >= (right as i64),
    }
}

fn comparison(cond: IntCC) -> ICmpOp {
    match cond {
        IntCC::Equal => ICmpOp::Eq,
        IntCC::NotEqual => ICmpOp::Ne,
        IntCC::UnsignedLessThan => ICmpOp::Ult,
        IntCC::UnsignedLessThanOrEqual => ICmpOp::Ule,
        IntCC::UnsignedGreaterThan => ICmpOp::Ugt,
        IntCC::UnsignedGreaterThanOrEqual => ICmpOp::Uge,
        IntCC::SignedLessThan => ICmpOp::Slt,
        IntCC::SignedLessThanOrEqual => ICmpOp::Sle,
        IntCC::SignedGreaterThan => ICmpOp::Sgt,
        IntCC::SignedGreaterThanOrEqual => ICmpOp::Sge,
    }
}

pub(super) fn view(source: &Function) -> Option<Function> {
    if source.blocks.len() != 1 {
        return None;
    }
    let block = source.blocks.get(&source.entry_block)?;
    if block.instructions.len() > 256 {
        return None;
    }
    let mut defined: HashSet<_> = (0..source.signature.params.len())
        .map(|i| Value(i as u32))
        .collect();
    let mut constants: HashMap<Value, u64> = HashMap::new();
    let mut comparisons = HashSet::new();
    let mut retained = Vec::new();
    let mut returned = false;
    for inst in &block.instructions {
        if returned
            || inst.args.iter().any(|id| !defined.contains(id))
            || inst.results.iter().any(|id| !defined.insert(*id))
        {
            return None;
        }
        returned = matches!(inst.opcode, L::Return);
        let literal = |i: usize| constants.get(inst.args.get(i)?).copied();
        match inst.opcode {
            L::Icmp { cond } => {
                let [result] = inst.results.as_slice() else {
                    return None;
                };
                // The adapter's table is sparse: Icmp itself defines B1 when
                // no explicit entry exists. A conflicting entry is invalid.
                if inst.args.len() != 2
                    || source
                        .value_types
                        .get(result)
                        .is_some_and(|ty| *ty != Type::B1)
                {
                    return None;
                }
                // Both operands must be independently evaluable 64-bit
                // literals. The value is dead, whether it is true or false.
                compare(comparison(cond), literal(0)?, literal(1)?);
                comparisons.insert(*result);
                continue;
            }
            L::GuardBoundsCheck { bound, .. } => {
                if inst.args.len() != 2
                    || !inst.results.is_empty()
                    || inst.args[0] != inst.args[1]
                    || literal(1)? >= bound
                {
                    return None;
                }
                // This frontend probe cannot trap. Its obligation ID is
                // retained in the original LIR but is not consulted here.
                continue;
            }
            _ => {}
        }
        let constant = match inst.opcode {
            L::Iconst { ty: Type::I64, imm } if inst.args.is_empty() => Some(imm as u64),
            L::Copy | L::Bitcast { to_ty: Type::I64 } if inst.args.len() == 1 => literal(0),
            L::Iadd if inst.args.len() == 2 => {
                literal(0).zip(literal(1)).map(|(a, b)| a.wrapping_add(b))
            }
            L::Imul if inst.args.len() == 2 => {
                literal(0).zip(literal(1)).map(|(a, b)| a.wrapping_mul(b))
            }
            _ => None,
        };
        if let (Some(value), [result]) = (constant, inst.results.as_slice()) {
            constants.insert(*result, value);
        }
        retained.push(inst.clone());
    }
    // Removed comparison values must be unobservable everywhere, including
    // in another removed comparison or guard. Never replace a live result.
    if block
        .instructions
        .iter()
        .flat_map(|i| &i.args)
        .any(|id| comparisons.contains(id))
    {
        return None;
    }
    let mut view = source.clone();
    view.blocks.get_mut(&source.entry_block)?.instructions = retained;
    for id in comparisons {
        view.value_types.remove(&id);
    }
    Some(view)
}
