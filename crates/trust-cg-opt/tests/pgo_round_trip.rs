// Integration test: .profdata round-trip through the filesystem.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Reference: designs/2026-04-18-pgo-workflow.md
// Issue: #396
//
// Scenario:
//   1. Build a MachFunction with a small CFG.
//   2. Run the PGO counter-injection pass; collect the CounterMap.
//   3. Simulate a canary run by producing a counter_values vector.
//   4. Call build_profdata_from_counters to get a ProfData.
//   5. Write to a temp file with write_to_path.
//   6. Read back with read_from_path.
//   7. Verify per-block hits survive the round trip.
//   8. Verify freshness check accepts the original hash and rejects a
//      perturbed hash.

use std::env;
use std::fs;
use std::path::PathBuf;

use trust_cg_ir::{AArch64Opcode, BlockId, MachFunction, MachInst, MachOperand, Signature};

use trust_cg_opt::CacheKey;
use trust_cg_opt::MachinePass;
use trust_cg_opt::pgo::{
    CounterMap, ProfData, ProfDataError, ProfileUsePass, build_profdata_from_counters_with_key,
    enforce_fresh, inject_block_counters, merge_compatible, read_from_path, write_to_path,
};

/// Build a three-block function:
///
/// ```text
///   bb0 (entry) -> bb1 -> bb2
/// ```
fn make_three_block_function(name: &str) -> MachFunction {
    let mut f = MachFunction::new(name.to_string(), Signature::new(vec![], vec![]));
    let bb0 = f.entry;
    let bb1 = f.create_block();
    let bb2 = f.create_block();

    let br0 = f.push_inst(MachInst::new(
        AArch64Opcode::B,
        vec![MachOperand::Block(bb1)],
    ));
    f.append_inst(bb0, br0);

    let br1 = f.push_inst(MachInst::new(
        AArch64Opcode::B,
        vec![MachOperand::Block(bb2)],
    ));
    f.append_inst(bb1, br1);

    let ret = f.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
    f.append_inst(bb2, ret);

    f.add_edge(bb0, bb1);
    f.add_edge(bb1, bb2);
    f
}

/// Build a four-block diamond with explicit control transfer:
///
/// ```text
///       bb0
///      /   \
///   bb1   bb2
///      \   /
///       bb3
/// ```
///
/// `bb0` uses `BCond target; B other_target`, so the profile-use layout pass
/// can reorder blocks without changing a layout-dependent fallthrough edge.
fn make_explicit_diamond_function(name: &str) -> MachFunction {
    let mut f = MachFunction::new(name.to_string(), Signature::new(vec![], vec![]));
    let bb0 = f.entry;
    let bb1 = f.create_block();
    let bb2 = f.create_block();
    let bb3 = f.create_block();

    let cond = f.push_inst(MachInst::new(
        AArch64Opcode::BCond,
        vec![MachOperand::Block(bb1)],
    ));
    f.append_inst(bb0, cond);
    let br_hot = f.push_inst(MachInst::new(
        AArch64Opcode::B,
        vec![MachOperand::Block(bb2)],
    ));
    f.append_inst(bb0, br_hot);

    let br_cold = f.push_inst(MachInst::new(
        AArch64Opcode::B,
        vec![MachOperand::Block(bb3)],
    ));
    f.append_inst(bb1, br_cold);
    let br_hot_join = f.push_inst(MachInst::new(
        AArch64Opcode::B,
        vec![MachOperand::Block(bb3)],
    ));
    f.append_inst(bb2, br_hot_join);
    let ret = f.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
    f.append_inst(bb3, ret);

    f.add_edge(bb0, bb1);
    f.add_edge(bb0, bb2);
    f.add_edge(bb1, bb3);
    f.add_edge(bb2, bb3);
    f
}

/// Build a four-block diamond where the hot arm is the current physical
/// fallthrough from `bb0`:
///
/// ```text
///       bb0
///      /   \
///   bb1   bb2
///      \   /
///       bb3
/// ```
///
/// `bb0` starts as `BCond bb1`, with `bb2` reached by implicit fallthrough in
/// the original layout. ProfileUse should materialize `B bb2` before moving
/// blocks.
fn make_implicit_conditional_diamond_function(name: &str) -> MachFunction {
    let mut f = MachFunction::new(name.to_string(), Signature::new(vec![], vec![]));
    let bb0 = f.entry;
    let bb1 = f.create_block();
    let bb2 = f.create_block();
    let bb3 = f.create_block();

    let cond = f.push_inst(MachInst::new(
        AArch64Opcode::BCond,
        vec![MachOperand::Block(bb1)],
    ));
    f.append_inst(bb0, cond);
    let br_cold = f.push_inst(MachInst::new(
        AArch64Opcode::B,
        vec![MachOperand::Block(bb3)],
    ));
    f.append_inst(bb1, br_cold);
    let br_hot_join = f.push_inst(MachInst::new(
        AArch64Opcode::B,
        vec![MachOperand::Block(bb3)],
    ));
    f.append_inst(bb2, br_hot_join);
    let ret = f.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]));
    f.append_inst(bb3, ret);

    f.add_edge(bb0, bb1);
    f.add_edge(bb0, bb2);
    f.add_edge(bb1, bb3);
    f.add_edge(bb2, bb3);
    f.block_order = vec![bb0, bb2, bb1, bb3];
    f
}

fn tmp_profdata_path(label: &str) -> PathBuf {
    env::temp_dir().join(format!(
        "trust_cg_pgo_{}_{}.profdata",
        label,
        std::process::id()
    ))
}

fn pgo_key(module_hash: u128) -> CacheKey {
    CacheKey::new(
        module_hash,
        2,
        "aarch64-unknown-unknown".into(),
        "generic-aarch64".into(),
        vec!["+neon".into()],
    )
}

#[test]
fn round_trip_single_function() {
    let mut f = make_three_block_function("bfs_step");
    let map = inject_block_counters(&mut f);
    assert_eq!(map.len(), 3);

    // Simulated counter array: bb0 hot, bb1 warm, bb2 cold.
    let counters = vec![10_000_u64, 9_750, 250];
    let module_hash: u128 = 0xdead_beef_cafe_babe_0123_4567_89ab_cdef;

    let profile_key = pgo_key(module_hash);
    let original = build_profdata_from_counters_with_key(&profile_key, &map, &counters);
    let path = tmp_profdata_path("single");
    write_to_path(&original, &path).unwrap();
    let bytes = fs::read(&path).unwrap();
    assert_eq!(&bytes[0..8], b"trcg-pgo");
    assert_ne!(bytes[0], b'{', "writer must emit binary v1, not JSON v0");

    let loaded = read_from_path(&path).unwrap();
    assert_eq!(loaded, original, "round trip must preserve profile data");

    // Hit counts must be exactly preserved.
    let fp = loaded.function("bfs_step").unwrap();
    assert_eq!(fp.call_count, 10_000);
    assert_eq!(fp.block_hits(0), 10_000);
    assert_eq!(fp.block_hits(1), 9_750);
    assert_eq!(fp.block_hits(2), 250);

    // Full key freshness: matching key accepted, mismatched module rejected.
    enforce_fresh(&loaded, &profile_key).unwrap();
    match enforce_fresh(&loaded, &pgo_key(module_hash.wrapping_add(1))) {
        Err(ProfDataError::StaleProfileKey { reason, .. }) => {
            assert_eq!(reason, "module hash mismatch");
        }
        other => panic!("expected StaleProfileKey, got {:?}", other),
    }

    let _ = fs::remove_file(&path);
}

#[test]
fn round_trip_multi_function() {
    // Inject into two functions, simulate counters, round-trip.
    let mut f1 = make_three_block_function("hot_fn");
    let mut f2 = make_three_block_function("cold_fn");
    let mut map = CounterMap::new();
    map.extend(inject_block_counters(&mut f1));
    map.extend(inject_block_counters(&mut f2));
    assert_eq!(map.len(), 6);

    // hot_fn: steady; cold_fn: never entered.
    let counters = vec![500_000, 499_999, 498_000, 0, 0, 0];
    let module_hash: u128 = 0xfeed_face_0000_1111_2222_3333_4444_5555;

    let original = build_profdata_from_counters_with_key(&pgo_key(module_hash), &map, &counters);
    let path = tmp_profdata_path("multi");
    write_to_path(&original, &path).unwrap();

    let loaded = read_from_path(&path).unwrap();
    assert_eq!(loaded, original);

    let hot = loaded.function("hot_fn").unwrap();
    assert_eq!(hot.call_count, 500_000);
    assert_eq!(hot.block_hits(0), 500_000);
    assert_eq!(hot.block_hits(1), 499_999);
    assert_eq!(hot.block_hits(2), 498_000);

    let cold = loaded.function("cold_fn").unwrap();
    assert_eq!(cold.call_count, 0);
    assert_eq!(cold.block_hits(0), 0);
    assert_eq!(cold.block_hits(1), 0);
    assert_eq!(cold.block_hits(2), 0);

    let _ = fs::remove_file(&path);
}

#[test]
fn merge_compatible_profdata_is_deterministic_and_fresh() {
    let key = pgo_key(0x8840_0000_0000_0000_0000_0000_0000_0001);
    let mut first = ProfData::new_with_key(&key);
    let mut beta = trust_cg_opt::pgo::FunctionProfile::new("beta");
    beta.call_count = 7;
    beta.blocks.push(trust_cg_opt::pgo::BlockProfile::new(2, 3));
    beta.blocks.push(trust_cg_opt::pgo::BlockProfile::new(0, 7));
    beta.edges
        .push(trust_cg_opt::pgo::EdgeProfile::new(0, 2, 3));
    first.functions.push(beta);

    let mut second = ProfData::new_with_key(&key);
    let mut alpha = trust_cg_opt::pgo::FunctionProfile::new("alpha");
    alpha.call_count = 11;
    alpha
        .blocks
        .push(trust_cg_opt::pgo::BlockProfile::new(0, 11));
    second.functions.push(alpha);
    let mut beta = trust_cg_opt::pgo::FunctionProfile::new("beta");
    beta.call_count = 13;
    beta.blocks.push(trust_cg_opt::pgo::BlockProfile::new(2, 5));
    beta.blocks
        .push(trust_cg_opt::pgo::BlockProfile::new(1, 13));
    beta.edges
        .push(trust_cg_opt::pgo::EdgeProfile::new(0, 2, 5));
    second.functions.push(beta);

    let merged = merge_compatible(&[first.clone(), second.clone()]).unwrap();
    let merged_reversed = merge_compatible(&[second, first]).unwrap();
    assert_eq!(merged, merged_reversed);
    assert!(merged.merged);
    assert_eq!(
        merged
            .functions
            .iter()
            .map(|f| f.name.as_str())
            .collect::<Vec<_>>(),
        vec!["alpha", "beta"]
    );

    let beta = merged.function("beta").unwrap();
    assert_eq!(beta.call_count, 20);
    assert_eq!(
        beta.blocks
            .iter()
            .map(|b| (b.block_id, b.hits))
            .collect::<Vec<_>>(),
        vec![(0, 7), (1, 13), (2, 8)]
    );
    assert_eq!(
        beta.edges,
        vec![trust_cg_opt::pgo::EdgeProfile::new(0, 2, 8)]
    );

    let path = tmp_profdata_path("merged");
    write_to_path(&merged, &path).unwrap();
    let loaded = read_from_path(&path).unwrap();
    assert_eq!(loaded, merged);
    assert!(loaded.merged);
    enforce_fresh(&loaded, &key).unwrap();
    let _ = fs::remove_file(&path);
}

#[test]
fn merge_rejects_incompatible_profile_keys() {
    let left = ProfData::new_with_key(&pgo_key(0x8840_0000_0000_0000_0000_0000_0000_0002));
    let right = ProfData::new_with_key(&pgo_key(0x8840_0000_0000_0000_0000_0000_0000_0003));

    match merge_compatible(&[left, right]) {
        Err(ProfDataError::IncompatibleMerge { field, .. }) => {
            assert_eq!(field, "profile_key_digest");
        }
        other => panic!("expected IncompatibleMerge, got {:?}", other),
    }
}

#[test]
fn merge_rejects_target_cpu_feature_and_opt_mismatches() {
    let key = pgo_key(0x8840_0000_0000_0000_0000_0000_0000_0003);
    assert_incompatible_merge_field(
        ProfData::new_with_key(&key),
        {
            let mut p = ProfData::new_with_key(&key);
            p.target_triple = "x86_64-unknown-unknown".to_string();
            p
        },
        "target_triple",
    );
    assert_incompatible_merge_field(
        ProfData::new_with_key(&key),
        {
            let mut p = ProfData::new_with_key(&key);
            p.target_cpu = "apple-m2".to_string();
            p
        },
        "target_cpu",
    );
    assert_incompatible_merge_field(
        ProfData::new_with_key(&key),
        {
            let mut p = ProfData::new_with_key(&key);
            p.target_features = vec!["+fp16".to_string(), "+neon".to_string()];
            p
        },
        "target_features",
    );
    assert_incompatible_merge_field(
        ProfData::new_with_key(&key),
        {
            let mut p = ProfData::new_with_key(&key);
            p.opt_level_num = 3;
            p.opt_level = "O3".to_string();
            p
        },
        "opt_level",
    );
}

#[test]
fn merge_rejects_counter_overflow() {
    let key = pgo_key(0x8840_0000_0000_0000_0000_0000_0000_0004);
    let mut left = ProfData::new_with_key(&key);
    let mut f = trust_cg_opt::pgo::FunctionProfile::new("overflow");
    f.call_count = u64::MAX;
    f.blocks
        .push(trust_cg_opt::pgo::BlockProfile::new(0, u64::MAX));
    left.functions.push(f);

    let mut right = ProfData::new_with_key(&key);
    let mut f = trust_cg_opt::pgo::FunctionProfile::new("overflow");
    f.call_count = 1;
    f.blocks.push(trust_cg_opt::pgo::BlockProfile::new(0, 1));
    right.functions.push(f);

    match merge_compatible(&[left, right]) {
        Err(ProfDataError::CounterOverflow { field }) => assert_eq!(field, "call_count"),
        other => panic!("expected CounterOverflow, got {:?}", other),
    }
}

#[test]
fn reader_rejects_corrupt_file() {
    // Write arbitrary garbage and confirm the reader errors rather than
    // panicking.
    let path = tmp_profdata_path("corrupt");
    fs::write(&path, b"not a valid profdata").unwrap();
    let err = read_from_path(&path).unwrap_err();
    assert!(matches!(err, ProfDataError::BadMagic { .. }));
    let _ = fs::remove_file(&path);
}

#[test]
fn reader_rejects_bad_magic_file() {
    let path = tmp_profdata_path("bad_magic");
    fs::write(&path, b"NOTtrcg-pgo").unwrap();
    let err = read_from_path(&path).unwrap_err();
    assert!(matches!(err, ProfDataError::BadMagic { .. }));
    let _ = fs::remove_file(&path);
}

#[test]
fn reader_rejects_v0_json_file_with_migration_diagnostic() {
    let path = tmp_profdata_path("v0_json");
    let mut p = ProfData::new(0);
    p.version = 0;
    let bytes = serde_json::to_vec_pretty(&p).unwrap();
    fs::write(&path, bytes).unwrap();
    let err = read_from_path(&path).unwrap_err();
    assert!(matches!(err, ProfDataError::LegacyJsonUnsupported));
    let _ = fs::remove_file(&path);
}

#[test]
fn freshness_rejects_opt_target_cpu_and_feature_mismatches() {
    let module_hash: u128 = 0x0123_4567_89ab_cdef_dead_beef_cafe_babe;
    let profile_key = pgo_key(module_hash);
    let profile = ProfData::new_with_key(&profile_key);

    let opt_mismatch = CacheKey::new(
        module_hash,
        3,
        profile.target_triple.clone(),
        profile.target_cpu.clone(),
        profile.target_features.clone(),
    );
    assert_stale_reason(&profile, &opt_mismatch, "opt-level mismatch");

    let target_mismatch = CacheKey::new(
        module_hash,
        profile.opt_level_num,
        "x86_64-unknown-unknown".into(),
        profile.target_cpu.clone(),
        profile.target_features.clone(),
    );
    assert_stale_reason(&profile, &target_mismatch, "target triple mismatch");

    let cpu_mismatch = CacheKey::new(
        module_hash,
        profile.opt_level_num,
        profile.target_triple.clone(),
        "apple-m2".into(),
        profile.target_features.clone(),
    );
    assert_stale_reason(&profile, &cpu_mismatch, "target CPU mismatch");

    let feature_mismatch = CacheKey::new(
        module_hash,
        profile.opt_level_num,
        profile.target_triple.clone(),
        profile.target_cpu.clone(),
        vec!["+fp16".into(), "+neon".into()],
    );
    assert_stale_reason(&profile, &feature_mismatch, "target feature mismatch");
}

#[test]
fn profile_use_rejects_stale_mismatched_profile_key_before_layout() {
    let module_hash: u128 = 0x8320_0000_0000_0000_0000_0000_0000_0001;
    let profile = ProfData::new_with_key(&pgo_key(module_hash));

    assert_stale_reason(
        &profile,
        &pgo_key(module_hash.wrapping_add(1)),
        "module hash mismatch",
    );
}

#[test]
fn generated_profile_drives_profile_use_block_layout() {
    let mut f = make_explicit_diamond_function("bfs_step");
    let map = inject_block_counters(&mut f);
    assert_eq!(map.len(), 4);

    // Simulated canary run: bb2 is the hot branch, bb1 is a NEVER-EXECUTED guard (the zero-hit-span chain gate only permits displacing zero-hit blocks), and the join
    // executes every time either arm reaches it.
    let counters = vec![100_u64, 0, 90, 100];
    let module_hash: u128 = 0x3960_0000_0000_0000_0000_0000_0000_0001;
    let original = build_profdata_from_counters_with_key(&pgo_key(module_hash), &map, &counters);
    let path = tmp_profdata_path("profile_use_layout");
    write_to_path(&original, &path).unwrap();

    let loaded = read_from_path(&path).unwrap();
    assert_eq!(loaded, original);

    let mut pass = ProfileUsePass::new(loaded);
    assert_eq!(
        f.block_order,
        vec![BlockId(0), BlockId(1), BlockId(2), BlockId(3)]
    );
    assert!(pass.run(&mut f));
    assert_eq!(
        f.block_order,
        vec![BlockId(0), BlockId(2), BlockId(3), BlockId(1)]
    );
    assert!(!pass.run(&mut f), "profile-use layout should be stable");

    let _ = fs::remove_file(&path);
}

#[test]
fn generated_profile_materializes_conditional_fallthrough_before_layout() {
    let mut f = make_implicit_conditional_diamond_function("bfs_step");
    let map = inject_block_counters(&mut f);
    assert_eq!(map.len(), 4);

    // Counter sites are emitted in the current layout order:
    // [entry, hot fallthrough, never-executed branch target (zero-hit — the
    // chain gate only permits displacing zero-hit blocks), join].
    let counters = vec![100_u64, 90, 0, 100];
    let module_hash: u128 = 0x3960_0000_0000_0000_0000_0000_0000_0002;
    let original = build_profdata_from_counters_with_key(&pgo_key(module_hash), &map, &counters);
    let path = tmp_profdata_path("profile_use_implicit_layout");
    write_to_path(&original, &path).unwrap();

    let loaded = read_from_path(&path).unwrap();
    assert_eq!(loaded, original);

    let entry = f.entry;
    assert_eq!(
        f.block_order,
        vec![BlockId(0), BlockId(2), BlockId(1), BlockId(3)]
    );
    assert_eq!(
        f.inst(*f.block(entry).insts.last().unwrap()).opcode,
        AArch64Opcode::BCond
    );

    let mut pass = ProfileUsePass::new(loaded);
    assert!(pass.run(&mut f));
    assert_eq!(
        f.block_order,
        vec![BlockId(0), BlockId(2), BlockId(3), BlockId(1)]
    );

    let entry_tail = f.inst(*f.block(entry).insts.last().unwrap());
    assert_eq!(entry_tail.opcode, AArch64Opcode::B);
    assert_eq!(entry_tail.operands, vec![MachOperand::Block(BlockId(2))]);
    assert!(!pass.run(&mut f), "profile-use layout should be stable");

    let _ = fs::remove_file(&path);
}

fn assert_stale_reason(profile: &ProfData, key: &CacheKey, expected: &str) {
    match enforce_fresh(profile, key) {
        Err(ProfDataError::StaleProfileKey { reason, .. }) => assert_eq!(reason, expected),
        other => panic!("expected StaleProfileKey, got {:?}", other),
    }
}

fn assert_incompatible_merge_field(left: ProfData, right: ProfData, expected: &'static str) {
    match merge_compatible(&[left, right]) {
        Err(ProfDataError::IncompatibleMerge { field, .. }) => assert_eq!(field, expected),
        other => panic!("expected IncompatibleMerge for {expected}, got {:?}", other),
    }
}
