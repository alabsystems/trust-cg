// cegis_payload - focused CEGIS payload failure-mode coverage (#486)
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use std::collections::HashMap;
use std::sync::{Arc, Mutex};

use trust_cg_ir::{
    AArch64Opcode, InstId, MachFunction, MachInst, MachOperand, RegClass, Signature, Type, VReg,
};
use trust_cg_opt::{CacheBackend, CacheKey, MachinePass};
use trust_cg_verify::cegis_pass::CegisSuperoptTestHooks;
use trust_cg_verify::{
    CegisCacheEntry, CegisResult, CegisSuperoptConfig, CegisSuperoptPass, RewriteLayer,
};

#[derive(Default)]
struct RecordingCache {
    entries: Mutex<HashMap<u128, Vec<u8>>>,
    last_put: Mutex<Option<Vec<u8>>>,
}

impl RecordingCache {
    fn last_entry(&self) -> CegisCacheEntry {
        let bytes = self
            .last_put
            .lock()
            .expect("last_put lock")
            .clone()
            .expect("cache put");
        CegisCacheEntry::decode(&bytes).expect("cache entry decode")
    }

    fn replace_all_with_entry(&self, entry: &CegisCacheEntry) {
        let bytes = entry.encode().expect("encode replacement cache entry");
        *self.last_put.lock().expect("last_put lock") = Some(bytes.clone());
        for value in self.entries.lock().expect("entries lock").values_mut() {
            *value = bytes.clone();
        }
    }
}

impl CacheBackend for RecordingCache {
    fn get(&self, key: &CacheKey) -> Option<Vec<u8>> {
        self.entries
            .lock()
            .expect("entries lock")
            .get(&key.digest())
            .cloned()
    }

    fn put(&self, key: &CacheKey, value: &[u8]) {
        let bytes = value.to_vec();
        self.entries
            .lock()
            .expect("entries lock")
            .insert(key.digest(), bytes.clone());
        *self.last_put.lock().expect("last_put lock") = Some(bytes);
    }
}

fn make_config(cache: Option<Arc<dyn CacheBackend>>, budget_sec: u64) -> CegisSuperoptConfig {
    CegisSuperoptConfig {
        budget_sec,
        per_query_ms: 1_000,
        target_triple: "aarch64-apple-darwin".to_string(),
        cpu: "apple-m1".to_string(),
        features: vec!["neon".to_string(), "fp-armv8".to_string()],
        opt_level: 2,
        cache,
        trace: None,
    }
}

fn equivalent_hook() -> CegisSuperoptTestHooks {
    CegisSuperoptTestHooks {
        verifier_result: Some(CegisResult::Equivalent {
            proof_hash: 0x486,
            iterations: 1,
        }),
        ..Default::default()
    }
}

fn layer_a_func(name: &str) -> (MachFunction, InstId) {
    let mut func = MachFunction::new(
        name.to_string(),
        Signature::new(vec![Type::I32], vec![Type::I32]),
    );
    let entry = func.entry;

    let v0 = VReg::new(func.alloc_vreg(), RegClass::Gpr32);
    let v1 = VReg::new(func.alloc_vreg(), RegClass::Gpr32);
    let v2 = VReg::new(func.alloc_vreg(), RegClass::Gpr32);

    let movz_zero = func.push_inst(MachInst::new(
        AArch64Opcode::Movz,
        vec![MachOperand::VReg(v0), MachOperand::Imm(0)],
    ));
    let movz_seven = func.push_inst(MachInst::new(
        AArch64Opcode::Movz,
        vec![MachOperand::VReg(v1), MachOperand::Imm(7)],
    ));
    let mul = func.push_inst(MachInst::new(
        AArch64Opcode::MulRR,
        vec![
            MachOperand::VReg(v2),
            MachOperand::VReg(v1),
            MachOperand::VReg(v0),
        ],
    ));
    let ret = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));

    func.append_inst(entry, movz_zero);
    func.append_inst(entry, movz_seven);
    func.append_inst(entry, mul);
    func.append_inst(entry, ret);

    (func, mul)
}

fn layer_c_and_mask_func(name: &str) -> (MachFunction, InstId, Vec<InstId>) {
    let mut func = MachFunction::new(
        name.to_string(),
        Signature::new(vec![Type::I32], vec![Type::I32]),
    );
    let entry = func.entry;

    let src = VReg::new(func.alloc_vreg(), RegClass::Gpr32);
    let mask = VReg::new(func.alloc_vreg(), RegClass::Gpr32);
    let dst = VReg::new(func.alloc_vreg(), RegClass::Gpr32);

    let movz = func.push_inst(MachInst::new(
        AArch64Opcode::Movz,
        vec![MachOperand::VReg(mask), MachOperand::Imm(0x5555)],
    ));
    let movk = func.push_inst(MachInst::new(
        AArch64Opcode::Movk,
        vec![
            MachOperand::VReg(mask),
            MachOperand::Imm(0x5555),
            MachOperand::Imm(16),
        ],
    ));
    let and = func.push_inst(MachInst::new(
        AArch64Opcode::AndRR,
        vec![
            MachOperand::VReg(dst),
            MachOperand::VReg(src),
            MachOperand::VReg(mask),
        ],
    ));
    let ret = func.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));

    func.append_inst(entry, movz);
    func.append_inst(entry, movk);
    func.append_inst(entry, and);
    func.append_inst(entry, ret);

    (func, and, vec![movz, movk])
}

fn scheduled_snapshot(func: &MachFunction) -> Vec<(u32, AArch64Opcode, Vec<MachOperand>)> {
    func.block(func.entry)
        .insts
        .iter()
        .map(|id| {
            let inst = func.inst(*id);
            (id.0, inst.opcode, inst.operands.clone())
        })
        .collect()
}

#[test]
fn layer_c_fuses_bitreverse_mask_materialization_to_andri() {
    let cache = Arc::new(RecordingCache::default());
    let mut pass = CegisSuperoptPass::new(make_config(Some(cache.clone()), 10))
        .with_test_hooks(equivalent_hook());
    let (mut func, and_id, materializers) = layer_c_and_mask_func("payload_layer_c_and_mask");

    let committed = pass.run(&mut func);

    assert!(committed, "Layer C should commit the AND-immediate fusion");
    assert_eq!(func.inst(and_id).opcode, AArch64Opcode::AndRI);
    assert_eq!(func.inst(and_id).operands[2].as_imm(), Some(0x5555_5555));
    for materializer in materializers {
        assert!(
            !func.block(func.entry).insts.contains(&materializer),
            "materializer {materializer:?} should be removed from the block schedule"
        );
    }
    assert_eq!(pass.stats().candidates, 1);
    assert_eq!(pass.stats().verified, 1);
    assert_eq!(pass.stats().rejected, 0);
    assert_eq!(pass.stats().layer_a_candidates, 0);
    assert_eq!(pass.stats().layer_b_candidates, 0);

    let entry = cache.last_entry();
    assert_eq!(entry.proven_rewrites.len(), 1);
    assert_eq!(entry.proven_rewrites[0].layer, RewriteLayer::C);
    assert_eq!(entry.proven_rewrites[0].window_len, 3);
}

#[test]
fn budget_exhaustion_caches_empty_plan_without_mutation() {
    let cache = Arc::new(RecordingCache::default());
    let mut pass = CegisSuperoptPass::new(make_config(Some(cache.clone()), 1)).with_test_hooks(
        CegisSuperoptTestHooks {
            force_expired_deadline: true,
            ..Default::default()
        },
    );
    let (mut func, _mul_id) = layer_a_func("payload_budget_exhaustion");
    let before = scheduled_snapshot(&func);

    let committed = pass.run(&mut func);

    assert!(!committed, "expired budget must not mutate the function");
    assert_eq!(scheduled_snapshot(&func), before);
    assert_eq!(pass.stats().cache_misses, 1);
    assert_eq!(pass.stats().cache_hits, 0);
    assert_eq!(pass.stats().cache_puts, 1);
    assert_eq!(pass.stats().budget_exhausted, 1);
    assert_eq!(pass.stats().verified, 0);

    let entry = cache.last_entry();
    assert!(entry.proven_rewrites.is_empty());
    assert_eq!(entry.attempted, 0);
    assert_eq!(entry.verified, 0);
}

#[test]
fn solver_error_is_counted_without_commit() {
    let cache = Arc::new(RecordingCache::default());
    let mut pass = CegisSuperoptPass::new(make_config(Some(cache.clone()), 10)).with_test_hooks(
        CegisSuperoptTestHooks {
            verifier_result: Some(CegisResult::Error("injected solver error".to_string())),
            ..Default::default()
        },
    );
    let (mut func, mul_id) = layer_a_func("payload_solver_error");
    let before = scheduled_snapshot(&func);

    let committed = pass.run(&mut func);

    assert!(!committed, "solver errors must not commit rewrites");
    assert_eq!(scheduled_snapshot(&func), before);
    assert_eq!(func.inst(mul_id).opcode, AArch64Opcode::MulRR);
    assert_eq!(pass.stats().candidates, 1);
    assert_eq!(pass.stats().verified, 0);
    assert_eq!(pass.stats().verifier_errors, 1);
    assert_eq!(pass.stats().rejected, 1);

    let entry = cache.last_entry();
    assert!(entry.proven_rewrites.is_empty());
    assert_eq!(entry.attempted, 1);
    assert_eq!(entry.rejected, 1);
}

#[test]
fn equal_cost_candidate_does_not_commit_or_call_solver() {
    let cache = Arc::new(RecordingCache::default());
    let mut pass = CegisSuperoptPass::new(make_config(Some(cache.clone()), 10)).with_test_hooks(
        CegisSuperoptTestHooks {
            force_layer_a_equal_cost: true,
            ..Default::default()
        },
    );
    let (mut func, mul_id) = layer_a_func("payload_equal_cost");
    let before = scheduled_snapshot(&func);

    let committed = pass.run(&mut func);

    assert!(!committed, "cost-equal rewrites must be rejected");
    assert_eq!(scheduled_snapshot(&func), before);
    assert_eq!(func.inst(mul_id).opcode, AArch64Opcode::MulRR);
    assert_eq!(pass.stats().candidates, 1);
    assert_eq!(pass.stats().layer_a_candidates, 1);
    assert_eq!(pass.stats().verified, 0);
    assert_eq!(pass.stats().rejected, 1);
    assert_eq!(pass.stats().solver_calls, 0);
    assert_eq!(pass.stats().verifier_errors, 0);

    let entry = cache.last_entry();
    assert!(entry.proven_rewrites.is_empty());
    assert_eq!(entry.attempted, 1);
    assert_eq!(entry.rejected, 1);
}

#[test]
fn drifted_cache_entry_is_discarded_and_reverified() {
    let cache = Arc::new(RecordingCache::default());
    let cfg = make_config(Some(cache.clone()), 10);

    let mut cold_pass = CegisSuperoptPass::new(cfg.clone()).with_test_hooks(equivalent_hook());
    let (mut cold_func, _cold_mul) = layer_a_func("payload_drifted_cache");
    assert!(cold_pass.run(&mut cold_func));
    assert_eq!(cold_pass.stats().cache_misses, 1);

    let mut drifted = cache.last_entry();
    assert_eq!(drifted.proven_rewrites.len(), 1);
    drifted.proven_rewrites[0].inst_index = 99_999;
    cache.replace_all_with_entry(&drifted);

    let mut hot_pass = CegisSuperoptPass::new(cfg).with_test_hooks(equivalent_hook());
    let (mut hot_func, hot_mul) = layer_a_func("payload_drifted_cache");
    let committed = hot_pass.run(&mut hot_func);

    assert!(
        committed,
        "drifted cache plans must fall back to a cold verification pass"
    );
    assert_eq!(hot_pass.stats().cache_hits, 0);
    assert_eq!(hot_pass.stats().cache_misses, 1);
    assert_eq!(hot_pass.stats().cache_puts, 1);
    assert_eq!(hot_func.inst(hot_mul).opcode, AArch64Opcode::Movz);

    let repaired = cache.last_entry();
    assert_eq!(repaired.proven_rewrites.len(), 1);
    assert_eq!(repaired.proven_rewrites[0].inst_index, hot_mul.0);
}

#[test]
fn cache_hit_replay_is_deterministic_and_solver_free() {
    let cache = Arc::new(RecordingCache::default());
    let cfg = make_config(Some(cache), 10);

    let mut cold_pass = CegisSuperoptPass::new(cfg.clone()).with_test_hooks(equivalent_hook());
    let (mut cold_func, cold_mul) = layer_a_func("payload_replay_determinism");
    assert!(cold_pass.run(&mut cold_func));
    let cold_post = scheduled_snapshot(&cold_func);
    assert_eq!(cold_func.inst(cold_mul).opcode, AArch64Opcode::Movz);
    assert_eq!(cold_pass.stats().cache_misses, 1);
    assert_eq!(cold_pass.stats().cache_hits, 0);

    let mut hot_pass = CegisSuperoptPass::new(cfg);
    let (mut hot_func, hot_mul) = layer_a_func("payload_replay_determinism");
    let committed = hot_pass.run(&mut hot_func);

    assert!(committed, "cache hit must replay the cached rewrite");
    assert_eq!(hot_pass.stats().cache_hits, 1);
    assert_eq!(hot_pass.stats().cache_misses, 0);
    assert_eq!(hot_pass.stats().cache_puts, 0);
    assert_eq!(hot_pass.stats().solver_calls, 0);
    assert_eq!(hot_pass.stats().verified, cold_pass.stats().verified);
    assert_eq!(hot_func.inst(hot_mul).opcode, AArch64Opcode::Movz);
    assert_eq!(scheduled_snapshot(&hot_func), cold_post);
}
