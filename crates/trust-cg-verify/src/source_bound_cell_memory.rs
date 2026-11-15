// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Conditional public-memory composition for independently checked callers.
//! Callback effects are arbitrary array-valued functions, coupled by call
//! occurrence between source and machine. Repeated calls need not be pure or
//! deterministic across occurrences. Private memory cannot affect those
//! functions and is restored after each machine call: these are explicit
//! environment premises, not conclusions of the source correspondence check.
//! The caller correspondence additionally relies on C ABI callee-saved register
//! and SP preservation across callbacks; this memory query does not prove it.

use super::cell_source::values::Contract;
use super::output_memory::Byte;
use crate::lowering_proof::{MachineSideProvenance, ProofObligation, TransvalCheckKind};
use crate::memory_proofs::memory_sort;
use crate::smt::SmtExpr as E;

const SAVED: [(&str, u64); 4] = [
    ("entry_x20", 32),
    ("entry_x19", 24),
    ("entry_fp", 16),
    ("entry_lr", 8),
];

fn below(distance: u64) -> E {
    // Normalize modular addresses consistently, including individual bytes.
    E::var("entry_sp", 64).bvadd(E::bv_const(distance.wrapping_neg(), 64))
}

fn load(memory: &E, distance: u64, width: usize) -> E {
    let mut value = E::select(memory.clone(), below(distance - (width - 1) as u64));
    for byte in (0..width - 1).rev() {
        value = value.concat(E::select(memory.clone(), below(distance - byte as u64)));
    }
    value
}

fn project(mut memory: E) -> E {
    for distance in 1..=32 {
        memory = E::store(memory, below(distance), E::bv_const(0, 8));
    }
    memory
}

/// Fresh acyclic equalities share array terms without expanding earlier calls
/// exponentially. Every fresh symbol has exactly one definition, references
/// only previous definitions, and cannot collide with inputs or callbacks.
/// Thus these equalities are a conservative extension, not extra assumptions
/// about input memory, callback behavior, or the desired conclusion.
#[derive(Default)]
struct Definitions(Vec<E>);

impl Definitions {
    fn memory(&mut self, value: E) -> E {
        let name = E::uf(
            format!("cell_memory_{}", self.0.len()),
            vec![],
            memory_sort(),
        );
        self.0.push(name.clone().eq_expr(value));
        name
    }
}

fn bits(bytes: &[Byte], calls: &[E], width: usize) -> E {
    let byte = |identity: &Byte| match identity {
        Byte::Parameter(parameter, offset) => {
            E::var(format!("parameter_{parameter}"), (width * 8) as u32)
                .extract((offset * 8 + 7) as u32, (offset * 8) as u32)
        }
        Byte::Constant(value) => E::bv_const(u64::from(*value), 8),
        Byte::Call(call, offset) => {
            E::select(calls[*call].clone(), below((32 + width - offset) as u64))
        }
        // The private Contract constructor permits only source byte identities.
        Byte::Register(..) | Byte::Clobber(..) => {
            unreachable!("machine byte in checked source contract")
        }
    };
    let mut identities = bytes.iter().rev();
    let mut value = byte(identities.next().expect("checked scalar width"));
    for identity in identities {
        value = value.concat(byte(identity));
    }
    value
}

fn store_cell(memory: &E, bytes: &[Byte], calls: &[E], width: usize) -> E {
    let value = bits(bytes, calls, width);
    let mut result = memory.clone();
    for offset in 0..width {
        result = E::store(
            result,
            below((32 + width - offset) as u64),
            value
                .clone()
                .extract((offset * 8 + 7) as u32, (offset * 8) as u32),
        );
    }
    result
}

fn callback_name(name: &str, occurrence: usize, width: usize) -> String {
    use std::fmt::Write;
    let mut result = format!("cell_callback_{width}_{occurrence}_");
    for byte in name.bytes() {
        write!(result, "{byte:02x}").unwrap();
    }
    result
}

pub(super) fn obligation(contract: &Contract) -> ProofObligation {
    let width = contract.width;
    let sp = E::var("entry_sp", 64);
    let mut definitions = Definitions::default();
    let mut source = E::uf("entry_memory", vec![], memory_sort());
    let mut machine = source.clone();
    for (name, distance) in SAVED {
        for offset in 0..8 {
            machine = E::store(
                machine,
                below(distance - offset),
                E::var(name, 64).extract((offset * 8 + 7) as u32, (offset * 8) as u32),
            );
        }
        machine = definitions.memory(machine);
    }
    let mut source_calls = Vec::new();
    let mut machine_calls = Vec::new();
    let mut properties = Vec::new();
    for (occurrence, call) in contract.calls.iter().enumerate() {
        source = definitions.memory(store_cell(&source, &call.cell_before, &source_calls, width));
        machine = definitions.memory(store_cell(
            &machine,
            &call.cell_before,
            &machine_calls,
            width,
        ));
        let source_input = definitions.memory(project(source));
        let machine_input = definitions.memory(project(machine.clone()));
        let source_argument = bits(&call.argument, &source_calls, width);
        let machine_argument = bits(&call.argument, &machine_calls, width);
        properties.push(source_input.clone().eq_expr(machine_input.clone()));
        properties.push(source_argument.clone().eq_expr(machine_argument.clone()));
        let target = callback_name(&call.name, occurrence, width);
        let invoke = |memory, argument| {
            E::uf(
                &target,
                vec![memory, below((32 + width) as u64), argument],
                memory_sort(),
            )
        };
        source = definitions.memory(invoke(source_input, source_argument));
        let machine_post = definitions.memory(invoke(machine_input, machine_argument));
        source_calls.push(source.clone());
        machine_calls.push(machine_post.clone());
        let mut restored = machine_post;
        for distance in 1..=32 {
            restored = E::store(
                restored,
                below(distance),
                E::select(machine.clone(), below(distance)),
            );
        }
        machine = definitions.memory(restored);
    }
    source = definitions.memory(store_cell(
        &source,
        &contract.cell_after,
        &source_calls,
        width,
    ));
    machine = definitions.memory(store_cell(
        &machine,
        &contract.cell_after,
        &machine_calls,
        width,
    ));
    properties.push(bits(&contract.result, &source_calls, width).eq_expr(bits(
        &contract.result,
        &machine_calls,
        width,
    )));
    properties.push(load(&source, (32 + width) as u64, width).eq_expr(load(
        &machine,
        (32 + width) as u64,
        width,
    )));
    for (name, distance) in SAVED {
        properties.push(load(&machine, distance, 8).eq_expr(E::var(name, 64)));
    }
    let restored_sp = sp
        .clone()
        .bvsub(E::bv_const(32, 64))
        .bvsub(E::bv_const(16, 64))
        .bvadd(E::bv_const(16, 64))
        .bvadd(E::bv_const(32, 64));
    properties.push(restored_sp.eq_expr(sp.clone()));
    let observe = E::var("observe", 64);
    // Includes the scalar cell and unused frame bytes, as well as all memory
    // outside the frame. Only the 32 saved bytes are hidden from callbacks.
    let public = observe
        .clone()
        .bvult(below(32))
        .or_expr(observe.clone().bvuge(sp.clone()));
    properties.push(
        public
            .not_expr()
            .or_expr(E::select(source, observe.clone()).eq_expr(E::select(machine, observe))),
    );
    let complete = properties.into_iter().reduce(E::and_expr).unwrap();
    let mut inputs = vec![("entry_sp".into(), 64), ("observe".into(), 64)];
    inputs.extend(SAVED.map(|(name, _)| (name.into(), 64)));
    inputs.extend((0..contract.parameters).map(|p| (format!("parameter_{p}"), (width * 8) as u32)));
    let mut preconditions = vec![
        sp.clone().bvuge(E::bv_const(48, 64)),
        sp.bvand(E::bv_const(15, 64)).eq_expr(E::bv_const(0, 64)),
    ];
    preconditions.extend(definitions.0);
    ProofObligation {
        name: format!(
            "Conditional AArch64 scalar-cell public memory: {} bits, {} calls",
            width * 8,
            contract.calls.len()
        ),
        trust_ir_expr: E::bool_const(true),
        aarch64_expr: complete,
        inputs,
        preconditions,
        fp_inputs: Vec::new(),
        category: Some(TransvalCheckKind::RegisterAllocation),
        machine_side_provenance: MachineSideProvenance::StaticDb,
    }
}

#[cfg(test)]
#[path = "source_bound_cell_memory_tests.rs"]
mod tests;
