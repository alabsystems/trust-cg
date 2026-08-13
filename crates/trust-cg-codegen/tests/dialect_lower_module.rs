// trust-cg-codegen/tests/dialect_lower_module.rs - lower_module pipeline hook
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Integration test for Trust Codegen#433 / trust_ir#428. Confirms that
// `pipeline::dialect_lower_module` drives the full verif.* -> trust_ir.* ->
// machir.* -> trust_cg_ir::MachFunction pipeline with at least one dialect
// registered. Unhandled DialectOps must fail in the legality gate rather
// than leak into the resulting MachFunction.

use trust_cg_codegen::pipeline::dialect_lower_module;
use trust_cg_dialect::LowerModuleError;
use trust_cg_dialect::dialects::conversions::{
    BFS_STEP_MAGIC, FINGERPRINT_BATCH_MAGIC, register_all,
};
use trust_cg_dialect::dialects::{trust_ir, verif};
use trust_cg_dialect::id::DialectOpId;
use trust_cg_dialect::module::{DialectFunction, DialectModule};
use trust_cg_dialect::registry::DialectRegistry;
use trust_cg_ir::{AArch64Opcode, Type};

fn build_fingerprint_module() -> DialectModule {
    let mut registry = DialectRegistry::new();
    let (verif_id, trust_ir_id, _machir_id, _ay_id) = register_all(&mut registry);

    // fn fingerprint_of(states: i64, count: i64) -> i64 {
    //   verif.frontier_drain(states)
    //   return verif.fingerprint_batch(states, count)
    // }
    let mut func = DialectFunction::new(
        "fingerprint_of",
        vec![Type::I64, Type::I64],
        vec![Type::I64],
    );
    let entry = func.entry_block().unwrap();
    let states = func.params[0].0;
    let count = func.params[1].0;
    func.append_op(
        entry,
        DialectOpId::new(verif_id, verif::FRONTIER_DRAIN),
        vec![],
        vec![states],
        vec![],
        None,
    );
    let result = func.alloc_value();
    func.append_op(
        entry,
        DialectOpId::new(verif_id, verif::FINGERPRINT_BATCH),
        vec![(result, Type::I64)],
        vec![states, count],
        vec![],
        None,
    );
    // Seed a trust_ir.ret so the module returns after verif->trust_ir lowering.
    func.append_op(
        entry,
        DialectOpId::new(trust_ir_id, trust_ir::TRUST_IR_RET),
        vec![],
        vec![result],
        vec![],
        None,
    );

    let mut module = DialectModule::new("fingerprint", registry);
    module.push_function(func);
    module
}

fn build_bfs_step_module() -> DialectModule {
    let mut registry = DialectRegistry::new();
    let (verif_id, trust_ir_id, _machir_id, _ay_id) = register_all(&mut registry);

    // fn bfs_step_of(frontier: i64, seen_set: i64) -> i64 {
    //   return verif.bfs_step(frontier, seen_set)
    // }
    let mut func = DialectFunction::new("bfs_step_of", vec![Type::I64, Type::I64], vec![Type::I64]);
    let entry = func.entry_block().unwrap();
    let frontier = func.params[0].0;
    let seen_set = func.params[1].0;
    let result = func.alloc_value();
    func.append_op(
        entry,
        DialectOpId::new(verif_id, verif::BFS_STEP),
        vec![(result, Type::I64)],
        vec![frontier, seen_set],
        vec![],
        None,
    );
    func.append_op(
        entry,
        DialectOpId::new(trust_ir_id, trust_ir::TRUST_IR_RET),
        vec![],
        vec![result],
        vec![],
        None,
    );

    let mut module = DialectModule::new("bfs_step", registry);
    module.push_function(func);
    module
}

#[test]
fn pipeline_dialect_lower_module_emits_mach_function() {
    let mut module = build_fingerprint_module();
    let mach_fns = dialect_lower_module(&mut module).expect("dialect_lower_module succeeded");

    assert_eq!(mach_fns.len(), 1, "one function in, one MachFunction out");
    let mf = &mach_fns[0];

    // Signature preserved through the full pipeline.
    assert_eq!(mf.name, "fingerprint_of");
    assert_eq!(mf.signature.params, vec![Type::I64, Type::I64]);
    assert_eq!(mf.signature.returns, vec![Type::I64]);

    // Expected post-lowering sequence: Movz magic, Eor ptr^len, Eor ^magic, Ret.
    let opcodes: Vec<AArch64Opcode> = mf.insts.iter().map(|i| i.opcode).collect();
    assert_eq!(
        opcodes,
        vec![
            AArch64Opcode::Movz,
            AArch64Opcode::EorRR,
            AArch64Opcode::EorRR,
            AArch64Opcode::Ret,
        ],
        "unexpected MachInst sequence: {:?}",
        opcodes
    );

    // Magic constant survives the verif -> trust_ir -> machir -> MachInst chain.
    let movz = &mf.insts[0];
    let imm = movz
        .operands
        .iter()
        .find_map(|o| o.as_imm())
        .expect("Movz has immediate operand");
    assert_eq!(imm as u64, FINGERPRINT_BATCH_MAGIC);
}

#[test]
fn pipeline_dialect_lower_module_emits_bfs_step_machine_function() {
    let mut module = build_bfs_step_module();
    let mach_fns = dialect_lower_module(&mut module).expect("dialect_lower_module succeeded");

    assert_eq!(mach_fns.len(), 1, "one function in, one MachFunction out");
    let mf = &mach_fns[0];

    assert_eq!(mf.name, "bfs_step_of");
    assert_eq!(mf.signature.params, vec![Type::I64, Type::I64]);
    assert_eq!(mf.signature.returns, vec![Type::I64]);

    let opcodes: Vec<AArch64Opcode> = mf.insts.iter().map(|i| i.opcode).collect();
    assert_eq!(
        opcodes,
        vec![
            AArch64Opcode::Movz,
            AArch64Opcode::AddRR,
            AArch64Opcode::EorRR,
            AArch64Opcode::Ret,
        ],
        "unexpected MachInst sequence: {:?}",
        opcodes
    );

    let movz = &mf.insts[0];
    let imm = movz
        .operands
        .iter()
        .find_map(|o| o.as_imm())
        .expect("Movz has immediate operand");
    assert_eq!(imm as u64, BFS_STEP_MAGIC);
}

#[test]
fn pipeline_dialect_lower_module_rejects_missing_dialect() {
    // Build a module whose registry has none of the required dialects.
    let registry = DialectRegistry::new();
    let mut module = DialectModule::new("empty", registry);
    // Push an empty function so the module isn't trivially empty on another axis.
    module.push_function(DialectFunction::new("noop", vec![], vec![]));
    let err = dialect_lower_module(&mut module).expect_err("missing dialects must be a hard error");
    assert!(
        matches!(err, LowerModuleError::MissingDialect(_)),
        "expected MissingDialect, got: {:?}",
        err
    );
}
