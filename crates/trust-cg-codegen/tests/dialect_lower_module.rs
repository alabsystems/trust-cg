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

fn reconstructed_magic(insts: &[trust_cg_ir::MachInst]) -> u64 {
    let mut value = 0_u64;
    for inst in insts {
        let halfword = inst.operands[1].as_imm().unwrap();
        assert!((0..=0xffff).contains(&halfword));
        let shift = match inst.opcode {
            AArch64Opcode::Movz => 0,
            AArch64Opcode::Movk => inst.operands[2].as_imm().unwrap(),
            opcode => panic!("unexpected constant instruction {opcode:?}"),
        };
        assert!([0, 16, 32, 48].contains(&shift));
        let mask = 0xffff_u64 << shift;
        value = (value & !mask) | ((halfword as u64) << shift);
    }
    value
}

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
    )
    .expect("bounded test function");
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
    )
    .expect("bounded test function");
    let result = func.alloc_value().expect("bounded test function");
    func.append_op(
        entry,
        DialectOpId::new(verif_id, verif::FINGERPRINT_BATCH),
        vec![(result, Type::I64)],
        vec![states, count],
        vec![],
        None,
    )
    .expect("bounded test function");
    // Seed a trust_ir.ret so the module returns after verif->trust_ir lowering.
    func.append_op(
        entry,
        DialectOpId::new(trust_ir_id, trust_ir::TRUST_IR_RET),
        vec![],
        vec![result],
        vec![],
        None,
    )
    .expect("bounded test function");

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
    let mut func = DialectFunction::new("bfs_step_of", vec![Type::I64, Type::I64], vec![Type::I64])
        .expect("bounded test function");
    let entry = func.entry_block().unwrap();
    let frontier = func.params[0].0;
    let seen_set = func.params[1].0;
    let result = func.alloc_value().expect("bounded test function");
    func.append_op(
        entry,
        DialectOpId::new(verif_id, verif::BFS_STEP),
        vec![(result, Type::I64)],
        vec![frontier, seen_set],
        vec![],
        None,
    )
    .expect("bounded test function");
    func.append_op(
        entry,
        DialectOpId::new(trust_ir_id, trust_ir::TRUST_IR_RET),
        vec![],
        vec![result],
        vec![],
        None,
    )
    .expect("bounded test function");

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

    // Entry copies, MOVZ/MOVK magic, two XORs, X0 result transfer, then RET.
    let opcodes: Vec<AArch64Opcode> = mf.insts.iter().map(|i| i.opcode).collect();
    assert_eq!(
        opcodes,
        vec![
            AArch64Opcode::MovR,
            AArch64Opcode::MovR,
            AArch64Opcode::Movz,
            AArch64Opcode::Movk,
            AArch64Opcode::Movk,
            AArch64Opcode::Movk,
            AArch64Opcode::EorRR,
            AArch64Opcode::EorRR,
            AArch64Opcode::MovR,
            AArch64Opcode::Ret,
        ],
        "unexpected MachInst sequence: {:?}",
        opcodes
    );

    // Magic constant survives the verif -> trust_ir -> machir -> MachInst chain.
    let imm = reconstructed_magic(&mf.insts[2..6]);
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
            AArch64Opcode::MovR,
            AArch64Opcode::MovR,
            AArch64Opcode::Movz,
            AArch64Opcode::Movk,
            AArch64Opcode::Movk,
            AArch64Opcode::Movk,
            AArch64Opcode::AddRR,
            AArch64Opcode::EorRR,
            AArch64Opcode::MovR,
            AArch64Opcode::Ret,
        ],
        "unexpected MachInst sequence: {:?}",
        opcodes
    );

    let imm = reconstructed_magic(&mf.insts[2..6]);
    assert_eq!(imm as u64, BFS_STEP_MAGIC);
}

#[test]
fn pipeline_dialect_lower_module_rejects_missing_dialect() {
    // Build a module whose registry has none of the required dialects.
    let registry = DialectRegistry::new();
    let mut module = DialectModule::new("empty", registry);
    // Push an empty function so the module isn't trivially empty on another axis.
    module.push_function(
        DialectFunction::new("noop", vec![], vec![]).expect("bounded test function"),
    );
    let err = dialect_lower_module(&mut module).expect_err("missing dialects must be a hard error");
    assert!(
        matches!(err, LowerModuleError::MissingDialect(_)),
        "expected MissingDialect, got: {:?}",
        err
    );
}
