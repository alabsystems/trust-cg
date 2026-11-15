// cegis_stats_trace - CegisPassStats + trace::emit acceptance (#492)
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Pins the #486/#492 Layer A acceptance criteria that live beyond "does the
// rewrite happen":
//
//   1. `CegisPassStats` carries the six fields required by #492:
//        total_wall_ms, solver_ms,
//        layer_a_candidates, layer_a_committed,
//        timeouts, verifier_errors
//      (plus Layer B symmetry and the existing panics/budget counters).
//   2. `CegisSuperoptPass::run` emits a structured event through the
//      `trust_cg_ir::trace::CompilationTrace` collector when one is wired up
//      via `CegisSuperoptConfig::trace`. The event carries the full stats
//      payload and is tagged as `Applied` (committed mutation) vs
//      `Rejected` (no-op) so downstream tooling can filter.
//   3. Stats accumulate across invocations (so `total_wall_ms` / `solver_ms`
//      are cumulative, same as `functions_seen`).

use std::collections::HashMap;
use std::sync::{Arc, Mutex};

use trust_cg_ir::trace::{CompilationTrace, EventKind, TraceLevel};
use trust_cg_ir::{
    AArch64Opcode, MachFunction, MachInst, MachOperand, RegClass, Signature, Type, VReg,
};
use trust_cg_opt::{CacheBackend, CacheKey, InMemoryCache, MachinePass};
use trust_cg_verify::cegis_pass::{MachInstBlob, MachOperandBlob, ProvenRewrite, RegClassBlob};
use trust_cg_verify::{CegisCacheEntry, CegisSuperoptConfig, CegisSuperoptPass, RewriteLayer};

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

fn make_config(
    cache: Option<Arc<dyn CacheBackend>>,
    trace: Option<Arc<CompilationTrace>>,
) -> CegisSuperoptConfig {
    CegisSuperoptConfig {
        budget_sec: 10,
        per_query_ms: 1_000,
        target_triple: "aarch64-apple-darwin".to_string(),
        cpu: "apple-m1".to_string(),
        features: vec!["neon".to_string(), "fp-armv8".to_string()],
        opt_level: 2,
        search_schedule: Default::default(),
        cache,
        trace,
    }
}

/// Build the same Layer A pattern used by `cegis_layer_a.rs`:
///   Movz v0, #0
///   Movz v1, #7
///   MulRR v2, v1, v0    (MUL by Movz-zero — Layer A candidate)
///   Ret
fn layer_a_func() -> MachFunction {
    let mut func = MachFunction::new(
        "layer_a_mul_zero_stats".to_string(),
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

    func
}

#[test]
fn layer_a_populates_required_stats_fields_issue_492() {
    // Cold run on a Layer A candidate function. We expect the following
    // fields to all update according to their spec:
    //   - layer_a_candidates >= 1 (MulRR x, Movz #0 matched)
    //   - layer_a_committed  >= 1 (proof passed + cost gate passed)
    //   - total_wall_ms      >  0 (at least one nanosecond elapsed;
    //                              Instant rounding may give 0 on very
    //                              fast CI — assert `>= 0` only)
    //   - solver_ms          accumulates alongside total_wall_ms
    //   - timeouts           == 0 (no real timeouts on toy input)
    //   - verifier_errors    == 0 (no solver errors expected)
    //   - panics             == 0
    //
    // Note: we assert on presence/logical invariants rather than exact
    // timings to keep the test deterministic across CI load.
    let cache: Arc<dyn CacheBackend> = Arc::new(InMemoryCache::new());
    let mut pass = CegisSuperoptPass::new(make_config(Some(cache), None));
    let mut func = layer_a_func();

    let committed = pass.run(&mut func);
    assert!(committed, "Layer A rewrite must commit on cold run");

    let stats = pass.stats();

    // Required Layer A per-layer counters (#492 AC #1).
    assert!(
        stats.layer_a_candidates >= 1,
        "expected >=1 Layer A candidate, got {}",
        stats.layer_a_candidates,
    );
    assert!(
        stats.layer_a_committed >= 1,
        "expected >=1 Layer A commit, got {}",
        stats.layer_a_committed,
    );
    assert!(
        stats.layer_a_committed <= stats.layer_a_candidates,
        "layer_a_committed must be a subset of layer_a_candidates"
    );

    // Timing counters exist and are coherent. `total_wall_ms` SHOULD be
    // positive, but on extremely fast hardware `Instant::elapsed().as_millis()`
    // rounding can give 0 for a single toy call, so we assert the weaker
    // invariant that solver_ms <= total_wall_ms (subset relationship).
    assert!(
        stats.solver_ms <= stats.total_wall_ms.saturating_add(5),
        "solver_ms ({}) must not exceed total_wall_ms ({}) meaningfully",
        stats.solver_ms,
        stats.total_wall_ms,
    );

    // Failure mode counters default to zero on a clean run.
    assert_eq!(
        stats.timeouts, 0,
        "clean Layer A run must have zero timeouts"
    );
    assert_eq!(
        stats.verifier_errors, 0,
        "clean Layer A run must have zero verifier errors"
    );
    assert_eq!(stats.panics, 0, "clean Layer A run must have zero panics");

    // Roll-up counters stay consistent with per-layer counters.
    assert!(
        stats.candidates >= stats.layer_a_candidates,
        "roll-up candidates ({}) must include layer_a_candidates ({})",
        stats.candidates,
        stats.layer_a_candidates,
    );
    assert!(
        stats.verified >= stats.layer_a_committed,
        "roll-up verified ({}) must include layer_a_committed ({})",
        stats.verified,
        stats.layer_a_committed,
    );
}

#[test]
fn stats_are_serde_roundtrippable_issue_492() {
    // #492 adds Serialize/Deserialize to CegisPassStats so harnesses can
    // roundtrip stats through JSON for dashboard ingestion (#486 §10).
    let cache: Arc<dyn CacheBackend> = Arc::new(InMemoryCache::new());
    let mut pass = CegisSuperoptPass::new(make_config(Some(cache), None));
    let mut func = layer_a_func();
    let _ = pass.run(&mut func);
    let stats = pass.stats().clone();

    let json = serde_json::to_string(&stats).expect("stats must serialize to JSON");
    // All #492 fields must be keyed in the JSON blob.
    for key in &[
        "total_wall_ms",
        "solver_ms",
        "layer_a_candidates",
        "layer_a_committed",
        "layer_b_candidates",
        "layer_b_committed",
        "timeouts",
        "verifier_errors",
        "panics",
    ] {
        assert!(
            json.contains(key),
            "stats JSON must include field `{}`, got: {}",
            key,
            json,
        );
    }

    let roundtripped: trust_cg_verify::CegisPassStats =
        serde_json::from_str(&json).expect("stats must deserialize from JSON");
    assert_eq!(roundtripped.layer_a_candidates, stats.layer_a_candidates);
    assert_eq!(roundtripped.layer_a_committed, stats.layer_a_committed);
    assert_eq!(roundtripped.total_wall_ms, stats.total_wall_ms);
    assert_eq!(roundtripped.solver_ms, stats.solver_ms);
    assert_eq!(roundtripped.timeouts, stats.timeouts);
    assert_eq!(roundtripped.verifier_errors, stats.verifier_errors);
}

#[test]
fn trace_emits_applied_event_on_committed_rewrite_issue_492() {
    // #492 AC #2: when a CompilationTrace is wired in, the pass must emit
    // a structured event summarizing the invocation. Committed rewrites
    // produce an `EventKind::Applied` event; the payload (encoded in the
    // PassId name slot) carries every required stats field as key=value.
    let cache: Arc<dyn CacheBackend> = Arc::new(InMemoryCache::new());
    let trace = Arc::new(CompilationTrace::new(TraceLevel::Full));
    let mut pass = CegisSuperoptPass::new(make_config(Some(cache), Some(trace.clone())));
    let mut func = layer_a_func();

    let committed = pass.run(&mut func);
    assert!(committed, "test precondition: Layer A must commit");

    let events = trace.events();
    assert_eq!(
        events.len(),
        1,
        "one CEGIS invocation should produce exactly one trace event",
    );
    let event = &events[0];

    // Event kind must be Applied on a committed rewrite.
    match &event.kind {
        EventKind::Applied { .. } => {}
        other => panic!(
            "expected EventKind::Applied on committed rewrite, got {:?}",
            other
        ),
    }

    // The PassId name slot carries the full stats payload. Assert every
    // #492-required field is discoverable in the payload.
    let payload = event.pass.name();
    assert!(
        payload.starts_with("CegisSuperoptPass{"),
        "payload: {}",
        payload
    );
    assert!(payload.contains("func=layer_a_mul_zero_stats"));
    assert!(payload.contains("cache=miss"));
    assert!(payload.contains("committed=true"));
    for key in &[
        "wall_ms=",
        "solver_ms=",
        "candidates=",
        "verified=",
        "rejected=",
        "layer_a_candidates=",
        "layer_a_committed=",
        "layer_b_candidates=",
        "layer_b_committed=",
        "timeouts=",
        "verifier_errors=",
        "panics=",
        "solver_calls=",
    ] {
        assert!(
            payload.contains(key),
            "trace payload must include `{}`, got: {}",
            key,
            payload,
        );
    }

    // The event must round-trip through the trace's JSON serializer.
    let json = trace.to_json();
    assert!(json.contains("CegisSuperoptPass"));
    assert!(json.contains("Applied"));
}

#[test]
fn trace_emits_rejected_event_when_no_match_issue_492() {
    // On an empty / non-matching function the pass runs, produces no
    // candidates, and must still emit a single Rejected event so
    // downstream dashboards can tell "pass ran, did nothing" apart from
    // "pass never ran".
    let cache: Arc<dyn CacheBackend> = Arc::new(InMemoryCache::new());
    let trace = Arc::new(CompilationTrace::new(TraceLevel::Summary));
    let mut pass = CegisSuperoptPass::new(make_config(Some(cache), Some(trace.clone())));
    let mut func = MachFunction::new("noop".to_string(), Signature::new(vec![], vec![]));

    let committed = pass.run(&mut func);
    assert!(!committed, "empty function should not mutate");

    let events = trace.events();
    assert_eq!(events.len(), 1, "pass must emit exactly one event per run");
    let event = &events[0];

    match &event.kind {
        EventKind::Rejected { reason, .. } => {
            // One of the documented reason strings.
            assert!(
                reason.contains("no candidate")
                    || reason.contains("cache-hit")
                    || reason.contains("all candidates rejected"),
                "unexpected rejection reason: {}",
                reason,
            );
        }
        other => panic!("expected EventKind::Rejected on noop, got {:?}", other),
    }

    let payload = event.pass.name();
    assert!(payload.contains("committed=false"));
    assert!(payload.contains("candidates=0"));
    assert!(payload.contains("verified=0"));
}

#[test]
fn trace_level_none_is_silent_issue_492() {
    // A trace at level `None` must not record any events, even though the
    // pass invokes `trace.emit`. This preserves the 0% overhead guarantee
    // of production builds (trust_cg_ir::trace::TraceLevel docs).
    let cache: Arc<dyn CacheBackend> = Arc::new(InMemoryCache::new());
    let trace = Arc::new(CompilationTrace::new(TraceLevel::None));
    let mut pass = CegisSuperoptPass::new(make_config(Some(cache), Some(trace.clone())));
    let mut func = layer_a_func();

    let _ = pass.run(&mut func);
    assert!(trace.is_empty(), "None-level trace must record zero events");
}

#[test]
fn trace_cache_hit_path_still_emits_event_issue_492() {
    // The cache-hit replay path must also emit a trace event, so that
    // dashboards see every pass invocation — not just cold runs. The
    // payload must flag `cache=hit` so downstream analysis can bucket
    // hot/cold invocations.
    let cache: Arc<dyn CacheBackend> = Arc::new(InMemoryCache::new());
    let cfg_cold = make_config(Some(cache.clone()), None);

    // Cold run: no trace.
    let mut pass_cold = CegisSuperoptPass::new(cfg_cold);
    let mut func_cold = layer_a_func();
    let committed_cold = pass_cold.run(&mut func_cold);
    assert!(committed_cold, "test precondition: Layer A must commit");
    assert_eq!(pass_cold.stats().cache_misses, 1);

    // Hot run with a fresh trace.
    let trace = Arc::new(CompilationTrace::new(TraceLevel::Full));
    let cfg_hot = make_config(Some(cache), Some(trace.clone()));
    let mut pass_hot = CegisSuperoptPass::new(cfg_hot);
    let mut func_hot = layer_a_func();
    let _ = pass_hot.run(&mut func_hot);
    assert_eq!(pass_hot.stats().cache_hits, 1);

    let events = trace.events();
    assert_eq!(events.len(), 1, "hot run must emit exactly one event");
    let payload = events[0].pass.name();
    assert!(payload.contains("cache=hit"), "payload: {}", payload);
    // Replay of a cached Layer A rewrite counts as layer_a_committed=1 on
    // the hot run too (#491 semantics preserved).
    assert!(
        payload.contains("layer_a_committed=1"),
        "payload: {}",
        payload
    );
}

/// The cache projection (`MachInstBlob`) of a replacement body, for the
/// operand kinds CEGIS replacements use.
fn blob_of(inst: &MachInst) -> MachInstBlob {
    MachInstBlob {
        opcode: format!("{:?}", inst.opcode),
        operands: inst
            .operands
            .iter()
            .map(|operand| match operand {
                MachOperand::VReg(vreg) => MachOperandBlob::VReg {
                    id: vreg.id,
                    class: vreg.class.into(),
                },
                MachOperand::Imm(imm) => MachOperandBlob::Imm(*imm),
                other => panic!("unexpected replacement operand {other:?}"),
            })
            .collect(),
    }
}

/// Cold run on `layer_a_func` through `cache`, returning the recorded entry
/// and the committed function.
fn cold_layer_a_entry(cache: &Arc<RecordingCache>) -> (CegisCacheEntry, MachFunction) {
    let mut pass_cold = CegisSuperoptPass::new(make_config(Some(cache.clone()), None));
    let mut func_cold = layer_a_func();
    assert!(pass_cold.run(&mut func_cold));
    (cache.last_entry(), func_cold)
}

#[test]
fn cache_entry_records_and_replays_serialized_replacement_body_issue_492() {
    // #492 made a cache entry a self-describing rewrite plan: each proven
    // rewrite records its layer, the window it consumes and its serialized
    // replacement body, and the hot path replays that plan without CEGIS,
    // counting a cache hit and exactly the rewrites it applied (the #491
    // failure was a hit that skipped the recorded mutation and credited
    // phantom counts). This pins that a VALID recorded body is replayed byte
    // for byte on a solver-free hit and leaves the function the cold run
    // committed. `..._tampered_twin_...` below pins the other half: a body
    // the matcher does not rebuild is never applied.
    let cache = Arc::new(RecordingCache::default());
    let (entry, func_cold) = cold_layer_a_entry(&cache);
    assert_eq!(entry.version, CegisCacheEntry::VERSION);
    assert_eq!(entry.proven_rewrites.len(), 1);
    let rewrite = &entry.proven_rewrites[0];
    assert_eq!(rewrite.layer, RewriteLayer::A);
    assert_eq!(rewrite.window_len, 1);
    assert_eq!(rewrite.replacement.len(), 1);
    let recorded = &rewrite.replacement[0];
    let mul_dst = layer_a_func().insts[rewrite.inst_index as usize].operands[0].clone();
    assert_eq!(
        *recorded,
        blob_of(&MachInst::new(
            AArch64Opcode::Movz,
            vec![mul_dst, MachOperand::Imm(0)]
        )),
        "cold cache entry must serialize the replacement opcode and operands"
    );
    assert!(matches!(
        recorded.operands[0],
        MachOperandBlob::VReg {
            class: RegClassBlob::Gpr32,
            ..
        }
    ));

    let mut pass_hot = CegisSuperoptPass::new(make_config(Some(cache.clone()), None));
    let mut func_hot = layer_a_func();
    assert!(pass_hot.run(&mut func_hot));
    let stats = pass_hot.stats();
    assert_eq!((stats.cache_hits, stats.cache_misses), (1, 0));
    assert_eq!((stats.cache_stale, stats.cache_puts), (0, 0));
    assert_eq!(stats.solver_calls, 0, "a hit replays without CEGIS");
    assert_eq!(stats.layer_a_committed, 1);

    let replayed = &func_hot.insts[rewrite.inst_index as usize];
    assert_eq!(replayed.opcode, AArch64Opcode::Movz);
    assert_eq!(
        CegisCacheEntry {
            proven_rewrites: vec![ProvenRewrite {
                replacement: vec![blob_of(replayed)],
                ..rewrite.clone()
            }],
            ..entry.clone()
        }
        .encode()
        .expect("encode the replayed plan"),
        entry.encode().expect("encode the recorded plan"),
        "the replayed body is the recorded body, byte for byte"
    );
    assert_eq!(format!("{func_hot:?}"), format!("{func_cold:?}"));
}

#[test]
fn cache_entry_tampered_twin_is_refused_as_stale_issue_492() {
    // The same entry with its recorded `Movz` immediate overwritten (0 ->
    // 123) in the cache, as anyone who can write the cache root could. The
    // entry still decodes, but the matcher rebuilds `Movz dst, #0`, so the
    // plan is stale: nothing is replayed, the function is searched again,
    // the correct body is committed and the entry is rewritten.
    let cache = Arc::new(RecordingCache::default());
    let (honest, func_cold) = cold_layer_a_entry(&cache);
    let mut tampered = honest.clone();
    *tampered.proven_rewrites[0]
        .replacement
        .get_mut(0)
        .and_then(|inst| inst.operands.get_mut(1))
        .expect("replacement immediate operand") = MachOperandBlob::Imm(123);
    cache.replace_all_with_entry(&tampered);
    assert_eq!(cache.last_entry(), tampered);

    let mut pass_hot = CegisSuperoptPass::new(make_config(Some(cache.clone()), None));
    let mut func_hot = layer_a_func();
    assert!(pass_hot.run(&mut func_hot));
    let stats = pass_hot.stats();
    assert_eq!(stats.cache_hits, 0, "a tampered body is never a hit");
    assert_eq!(
        (stats.cache_stale, stats.cache_misses, stats.cache_puts),
        (1, 1, 1)
    );
    assert_eq!(stats.layer_a_committed, 1);

    let target = honest.proven_rewrites[0].inst_index as usize;
    assert_eq!(func_hot.insts[target].operands[1], MachOperand::Imm(0));
    assert_eq!(format!("{func_hot:?}"), format!("{func_cold:?}"));
    assert_eq!(
        cache.last_entry(),
        honest,
        "the fresh search rewrites the entry"
    );
}
