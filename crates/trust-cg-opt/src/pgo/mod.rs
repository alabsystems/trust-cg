// trust-cg-opt/pgo/mod.rs - Profile-guided optimization (PGO) support
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Reference: designs/2026-04-18-pgo-workflow.md
// Issue: #396
//
// Phase 1 MVP. Contents:
//   - `schema`: on-disk layout (ProfData, FunctionProfile, BlockProfile)
//   - `io`: encode/decode + file I/O + hash freshness check
//   - `inject`: the counter-injection pass (AArch64 `BL <symbol>`)
//   - this module: pipeline-facing plumbing — `PipelineConfig`,
//     `ProfileMap`, and helpers for turning raw counter arrays into a
//     `ProfData` ready to be written to disk.
//
// Phase 2 adds the ProfileUse pass as a pipeline hook. It now computes
// hotness diagnostics and applies conservative profile-guided block layout;
// bounded inline and loop-unroll consumers use the same hotness summary.
// Vectorization thresholds and CEGIS budget consumers remain future work.

//! Profile-guided optimization (PGO) support.
//!
//! Phase 1 MVP: counter-injection pass + `.profdata` schema + writer +
//! reader. See [`designs/2026-04-18-pgo-workflow.md`](../../../../designs/2026-04-18-pgo-workflow.md).

pub mod inject;
pub mod io;
pub mod profile_use;
pub mod schema;

pub use inject::{
    COUNTER_SYMBOL_PREFIX, CounterInjectionPass, CounterMap, CounterSite, counter_symbol,
    inject_block_counters,
};
pub use io::{
    ProfDataError, decode, encode, enforce_fresh, merge_compatible, merge_profdata, read_from_path,
    write_to_path,
};
pub use profile_use::{
    BlockHotness, FunctionHotness, HotnessClass, PROFILE_USE_PASS_NAME, ProfileHotness,
    ProfileUsePass, ProfileUseStats,
};
pub use schema::{
    BlockProfile, EdgeProfile, FunctionProfile, PROFDATA_MAGIC, PROFDATA_VERSION, ProfData,
};

use crate::cache::CacheKey;

/// Configuration toggles for the PGO subsystem.
///
/// Carried on the optimization pipeline. [`PipelineConfig::profile_use`]
/// schedules the [`ProfileUsePass`] at O2/O3. Runtime profile generation
/// remains separate from this configuration.
#[derive(Debug, Clone, Default)]
pub struct PipelineConfig {
    /// When true, the pipeline inserts the [`CounterInjectionPass`].
    pub profile_generate: bool,
    /// An already-loaded profile for profile-use mode. The pipeline
    /// holds this by value so downstream passes can query it.
    pub profile_use: Option<ProfData>,
}

impl PipelineConfig {
    /// Create a config with `profile_generate = true`.
    pub fn with_profile_generate() -> Self {
        Self {
            profile_generate: true,
            profile_use: None,
        }
    }

    /// Create a config with a loaded profile for use.
    pub fn with_profile_use(profile: ProfData) -> Self {
        Self {
            profile_generate: false,
            profile_use: Some(profile),
        }
    }

    /// Compute the profile-use hotness summary for callers that need
    /// diagnostics without constructing a pass manager.
    pub fn profile_hotness(&self) -> Option<ProfileHotness> {
        self.profile_use.as_ref().map(ProfileHotness::from_profile)
    }

    /// Compute aggregate profile-use stats for the loaded profile, if any.
    pub fn profile_use_stats(&self) -> Option<ProfileUseStats> {
        self.profile_hotness().map(|hotness| *hotness.stats())
    }
}

/// Build a [`ProfData`] by associating runtime counter arrays with a
/// [`CounterMap`] emitted by [`inject_block_counters`].
///
/// `counter_values[i]` is the observed hit count for
/// `map.sites[i]`. The caller is responsible for threading the indices
/// consistently through the runtime.
///
/// The returned `ProfData` uses a legacy module-hash-only default key.
/// New callers that know the compile request should use
/// [`build_profdata_from_counters_with_key`].
pub fn build_profdata_from_counters(
    module_hash: u128,
    map: &CounterMap,
    counter_values: &[u64],
) -> ProfData {
    let profile_key = CacheKey::new(module_hash, 0, String::new(), String::new(), Vec::new());
    build_profdata_from_counters_with_key(&profile_key, map, counter_values)
}

/// Build a [`ProfData`] from runtime counters and stamp it with the full PGO
/// freshness key for the compile request.
pub fn build_profdata_from_counters_with_key(
    profile_key: &CacheKey,
    map: &CounterMap,
    counter_values: &[u64],
) -> ProfData {
    assert_eq!(
        map.len(),
        counter_values.len(),
        "counter_values length must match CounterMap.len()"
    );

    let mut profile = ProfData::new_with_key(profile_key);
    for (site, hits) in map.sites.iter().zip(counter_values.iter()) {
        let f = profile.function_mut_or_insert(&site.function);
        f.blocks.push(BlockProfile::new(site.block_id, *hits));
        // The per-function call count is a sum of entry-block hits for
        // the function. In Phase 1 we treat block 0 as the entry.
        if site.block_id == 0 {
            f.call_count = *hits;
        }
    }
    profile
}

#[cfg(test)]
mod tests {
    use super::*;
    use trust_cg_ir::{MachFunction, Signature};

    fn empty_func(name: &str) -> MachFunction {
        MachFunction::new(name.to_string(), Signature::new(vec![], vec![]))
    }

    #[test]
    fn pipeline_config_default_is_off() {
        let cfg = PipelineConfig::default();
        assert!(!cfg.profile_generate);
        assert!(cfg.profile_use.is_none());
    }

    #[test]
    fn pipeline_config_with_profile_generate() {
        let cfg = PipelineConfig::with_profile_generate();
        assert!(cfg.profile_generate);
        assert!(cfg.profile_use.is_none());
    }

    #[test]
    fn pipeline_config_with_profile_use_loads_data() {
        let data = ProfData::new(42);
        let cfg = PipelineConfig::with_profile_use(data.clone());
        assert!(!cfg.profile_generate);
        assert_eq!(cfg.profile_use.as_ref().unwrap(), &data);
    }

    #[test]
    fn pipeline_config_exposes_profile_use_stats() {
        let mut data = ProfData::new(42);
        let mut function = FunctionProfile::new("bfs_step");
        function.call_count = 10_000;
        function.blocks.push(BlockProfile::new(0, 10_000));
        function.blocks.push(BlockProfile::new(1, 250));
        data.functions.push(function);

        let cfg = PipelineConfig::with_profile_use(data);
        let stats = cfg.profile_use_stats().unwrap();

        assert_eq!(stats.profiled_functions, 1);
        assert_eq!(stats.profiled_blocks, 2);
        assert_eq!(stats.hot_functions, 1);
        assert_eq!(stats.hot_blocks, 1);
        assert_eq!(stats.cold_blocks, 1);
        assert_eq!(stats.max_function_count, 10_000);
        assert_eq!(stats.total_function_count, 10_000);
        assert_eq!(stats.total_block_hits, 10_250);
    }

    #[test]
    fn build_profdata_from_counters_round_trip() {
        // Inject into two functions and simulate observed counts.
        let mut a = empty_func("alpha");
        a.create_block(); // 2 blocks total
        let mut b = empty_func("beta");
        let mut map = inject_block_counters(&mut a);
        map.extend(inject_block_counters(&mut b));
        assert_eq!(map.len(), 3);

        let counters = vec![1000, 500, 7];
        let module_hash: u128 = 0xabcd_ef01_2345_6789_abcd_ef01_2345_6789;
        let profile = build_profdata_from_counters(module_hash, &map, &counters);

        assert_eq!(profile.module_hash_u128(), Some(module_hash));
        let a_profile = profile.function("alpha").unwrap();
        assert_eq!(a_profile.blocks.len(), 2);
        assert_eq!(a_profile.block_hits(0), 1000);
        assert_eq!(a_profile.block_hits(1), 500);
        assert_eq!(a_profile.call_count, 1000);

        let b_profile = profile.function("beta").unwrap();
        assert_eq!(b_profile.block_hits(0), 7);
        assert_eq!(b_profile.call_count, 7);
    }

    #[test]
    fn end_to_end_round_trip_through_bytes() {
        // Counter injection -> simulated counters -> profdata -> bytes ->
        // parsed profdata -> per-block hit match.
        let mut f = empty_func("bfs_step");
        let bb1 = f.create_block();
        let bb2 = f.create_block();
        f.add_edge(f.entry, bb1);
        f.add_edge(bb1, bb2);

        let map = inject_block_counters(&mut f);
        assert_eq!(map.len(), 3);
        let counters = vec![10_000, 9_750, 250];
        let module_hash: u128 = 0xdead_beef_cafe_babe_0123_4567_89ab_cdef;
        let profile = build_profdata_from_counters(module_hash, &map, &counters);

        let bytes = encode(&profile).unwrap();
        let parsed = decode(&bytes).unwrap();
        assert_eq!(parsed, profile, "round trip must preserve every counter");

        let f_profile = parsed.function("bfs_step").unwrap();
        assert_eq!(f_profile.block_hits(0), 10_000);
        assert_eq!(f_profile.block_hits(1), 9_750);
        assert_eq!(f_profile.block_hits(2), 250);
        assert_eq!(f_profile.call_count, 10_000);
        let key = CacheKey::new(module_hash, 0, String::new(), String::new(), Vec::new());
        enforce_fresh(&parsed, &key).unwrap();
    }

    #[test]
    #[should_panic(expected = "counter_values length")]
    fn build_profdata_length_mismatch_panics() {
        let mut f = empty_func("x");
        let map = inject_block_counters(&mut f);
        let _ = build_profdata_from_counters(0, &map, &[]);
    }
}
