// trust-cg-dialect - End-to-end progressive lowering test
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Proof-of-concept end-to-end test: build a `verif.*` function, lower it
//! through `trust_ir.*` and `machir.*`, and emit a `MachFunction`.

use trust_cg_ir::{AArch64Opcode, Type};

use trust_cg_dialect::conversion::ConversionDriver;
use trust_cg_dialect::dialects::conversions::{
    BFS_STEP_MAGIC, FINGERPRINT_BATCH_MAGIC, register_all, trust_ir_to_machir_driver,
    verif_to_trust_ir_driver,
};
use trust_cg_dialect::dialects::{machir, trust_ir, verif};
use trust_cg_dialect::emit_mach_function;
use trust_cg_dialect::id::DialectOpId;
use trust_cg_dialect::module::{DialectFunction, DialectModule};
use trust_cg_dialect::pass::{Legality, validate_legality};
use trust_cg_dialect::registry::DialectRegistry;

fn build_verif_module() -> (
    DialectModule,
    trust_cg_dialect::id::DialectId,
    trust_cg_dialect::id::DialectId,
    trust_cg_dialect::id::DialectId,
) {
    let mut registry = DialectRegistry::new();
    let (verif_id, trust_ir_id, machir_id, _ay_id) = register_all(&mut registry);

    // fn fingerprint_of(states: i64, count: i64) -> i64 {
    //     verif.frontier_drain(states)
    //     return verif.fingerprint_batch(states, count)
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
    // Mirror trust_ir.ret so after verif->trust_ir lowering the module returns.
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
    (module, verif_id, trust_ir_id, machir_id)
}

fn build_bfs_step_module() -> (
    DialectModule,
    trust_cg_dialect::id::DialectId,
    trust_cg_dialect::id::DialectId,
    trust_cg_dialect::id::DialectId,
) {
    let mut registry = DialectRegistry::new();
    let (verif_id, trust_ir_id, machir_id, _ay_id) = register_all(&mut registry);

    // fn bfs_step_of(frontier: i64, seen_set: i64) -> i64 {
    //     return verif.bfs_step(frontier, seen_set)
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
    (module, verif_id, trust_ir_id, machir_id)
}

#[test]
fn progressive_lowering_verif_to_machine() {
    let (mut module, verif_id, trust_ir_id, machir_id) = build_verif_module();

    // --- Stage 1: verif -> trust_ir ---
    let stage1 = verif_to_trust_ir_driver(verif_id, trust_ir_id);
    stage1
        .run(&mut module)
        .expect("verif->trust_ir conversion succeeded");

    // After stage 1 no verif.* ops should remain. We assert legality against a
    // producer set of {trust_ir}. Note: the trust_ir.ret we inserted up front is in
    // trust_ir, so it's legal.
    let stage1_legality = Legality::new().produces(trust_ir_id);
    validate_legality(&module, &stage1_legality)
        .expect("stage1 output contains only trust_ir.* ops");

    // --- Stage 2: trust_ir -> machir ---
    let stage2 = trust_ir_to_machir_driver(trust_ir_id, machir_id);
    stage2
        .run(&mut module)
        .expect("trust_ir->machir conversion succeeded");

    let stage2_legality = Legality::new().produces(machir_id);
    validate_legality(&module, &stage2_legality).expect("stage2 output contains only machir.* ops");

    // --- Stage 3: machir -> MachFunction ---
    let mf = emit_mach_function(&module, 0).expect("mach function emit");

    // Assertions on the resulting MachFunction ---------------------------
    // Signature preserved.
    assert_eq!(mf.name, "fingerprint_of");
    assert_eq!(mf.signature.params, vec![Type::I64, Type::I64]);
    assert_eq!(mf.signature.returns, vec![Type::I64]);

    // We expect the following ops in order (ignoring flags, exact registers):
    //   Movz  (the magic constant)
    //   EorRR (ptr XOR len)
    //   EorRR (XOR magic)
    //   Ret
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

    // The Movz instruction should carry the fingerprint magic value.
    let movz = &mf.insts[0];
    let imm = movz
        .operands
        .iter()
        .find_map(|o| o.as_imm())
        .expect("Movz has immediate operand");
    assert_eq!(imm as u64, FINGERPRINT_BATCH_MAGIC);

    // Every instruction should be in the entry block.
    let entry = &mf.blocks[mf.entry.0 as usize];
    assert_eq!(entry.insts.len(), mf.insts.len());
}

#[test]
fn progressive_lowering_bfs_step_to_machine() {
    let (mut module, verif_id, trust_ir_id, machir_id) = build_bfs_step_module();

    let stage1 = verif_to_trust_ir_driver(verif_id, trust_ir_id);
    stage1
        .run(&mut module)
        .expect("verif->trust_ir conversion succeeded");

    let stage1_legality = Legality::new().produces(trust_ir_id);
    validate_legality(&module, &stage1_legality)
        .expect("stage1 output contains only trust_ir.* ops");

    let stage2 = trust_ir_to_machir_driver(trust_ir_id, machir_id);
    stage2
        .run(&mut module)
        .expect("trust_ir->machir conversion succeeded");

    let stage2_legality = Legality::new().produces(machir_id);
    validate_legality(&module, &stage2_legality).expect("stage2 output contains only machir.* ops");

    let mf = emit_mach_function(&module, 0).expect("mach function emit");
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
fn legality_violation_detected() {
    // Build a module that contains both verif.* and trust_ir.* ops. Verify the
    // legality checker catches both "op dialect not in produces set" and the
    // explicit-forbid path.
    let (module, verif_id, trust_ir_id, _machir_id) = build_verif_module();

    // The module mixes verif + trust_ir, so producing-only-verif fails on the
    // trust_ir.ret op.
    let legality = Legality::new().produces(verif_id);
    let err = validate_legality(&module, &legality)
        .expect_err("mixed verif+trust_ir module should fail a verif-only produces set");
    let msg = format!("{}", err);
    assert!(msg.contains("not in produces set"), "got: {}", msg);

    // Accepting both verif and trust_ir passes.
    let legality = Legality::new().produces(verif_id).produces(trust_ir_id);
    validate_legality(&module, &legality).expect("both dialects allowed");

    // Explicit forbid on the verif fingerprint op trips legality.
    let forbidden = DialectOpId::new(verif_id, verif::FINGERPRINT_BATCH);
    let legality = Legality::new()
        .produces(verif_id)
        .produces(trust_ir_id)
        .forbid(forbidden);
    let err = validate_legality(&module, &legality)
        .expect_err("explicitly forbidden op should trip legality");
    let msg = format!("{}", err);
    assert!(msg.contains("explicitly forbidden"), "got: {}", msg);
}

#[test]
fn legality_accepts_side_rejects_unexpected_source_dialect() {
    // Pass's declared accepts set must be enforced symmetrically with produces.
    // A pass that accepts only trust_ir must reject a module containing verif ops,
    // even though produces is empty (= "no output constraint").
    let (module, _verif_id, trust_ir_id, _machir_id) = build_verif_module();

    let legality = Legality::new().accepts(trust_ir_id);
    let err = validate_legality(&module, &legality)
        .expect_err("verif op should not pass an accepts: [trust_ir] gate");
    let msg = format!("{}", err);
    assert!(
        msg.contains("not in accepts set"),
        "expected accepts-side error, got: {}",
        msg
    );
}

#[test]
fn registry_roundtrip_and_ops_lookup() {
    let mut registry = DialectRegistry::new();
    let (verif_id, trust_ir_id, machir_id, _ay_id) = register_all(&mut registry);

    assert_eq!(registry.by_name("verif"), Some(verif_id));
    assert_eq!(registry.by_name("trust_ir"), Some(trust_ir_id));
    assert_eq!(registry.by_name("machir"), Some(machir_id));
    assert_eq!(registry.by_name("nope"), None);

    let batch = DialectOpId::new(verif_id, verif::FINGERPRINT_BATCH);
    let def = registry.op_def(batch).expect("op def lookup");
    assert_eq!(def.name, "verif.fingerprint_batch");
    assert!(def.capabilities.is_pure());

    let ret = DialectOpId::new(trust_ir_id, trust_ir::TRUST_IR_RET);
    let def = registry.op_def(ret).expect("ret def lookup");
    assert!(def.capabilities.is_terminator());

    let add_rr = DialectOpId::new(machir_id, machir::MACHIR_ADD_RR);
    assert_eq!(
        registry.op_def(add_rr).map(|d| d.name),
        Some("machir.add.rr")
    );
}

#[test]
fn unknown_ops_pass_through_driver() {
    // If a driver has no registered pattern for an op, the conversion driver
    // should copy it through verbatim. This enables mixed-dialect modules
    // (e.g. partial conversions where some ops are already in the destination
    // dialect).
    let (mut module, verif_id, trust_ir_id, _machir_id) = build_verif_module();

    // An empty driver leaves everything untouched.
    let empty = ConversionDriver::new();
    empty.run(&mut module).unwrap();

    // Verify we still see the original verif op present.
    let func = &module.functions[0];
    let has_verif = func.iter_ops().any(|o| o.op.dialect == verif_id);
    assert!(has_verif, "empty driver should pass verif op through");

    // And the trust_ir.ret we seeded should still be there.
    let has_ret = func
        .iter_ops()
        .any(|o| o.op == DialectOpId::new(trust_ir_id, trust_ir::TRUST_IR_RET));
    assert!(has_ret, "empty driver should pass trust_ir.ret through");
}
