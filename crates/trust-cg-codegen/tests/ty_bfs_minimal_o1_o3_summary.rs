// Minimal TY BFS parent-loop O1/O3 summary reducer.
//
// Builds a small parent loop directly in trust_ir, runs it through the AArch64 JIT
// at O1 and O3, and compares the status summary against a Rust reference.

#![cfg(target_arch = "aarch64")]

use std::collections::HashMap;
use std::{env, fs};

use trust_cg_codegen::jit::ProfileHookMode;
use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::{Compiler, CompilerConfig, ExecutableBuffer, Target};
use trust_cg_opt::pgo::{FunctionProfile, ProfData, enforce_fresh, read_from_path};
use trust_cg_opt::{CacheKey, stable_hash};
use trust_ir::{BinOp, ICmpOp, Ty, ValueId};
use trust_ir_build::{FunctionBuilder, ModuleBuilder};

#[path = "common/ty_contract.rs"]
mod ty_contract;

use ty_contract::{abi_i64, abi_ptr, bind_ty_reducer_entry, extern_c_signature};

const ENTRY_NAME: &str = "ty_bfs_minimal_o1_o3_summary";
const SUMMARY_SLOTS: usize = 5;

type EntryFn = extern "C" fn(*const u64, u64, *mut u64) -> u64;

const FINGERPRINT_SEED: u64 = 0x6d2b_79f5_aa17_6620;
const PARENT_DIGEST_SEED: u64 = 0x9e37_79b9_6620_0001;
const IDX_PRIME: u64 = 0x0000_0000_85eb_ca6b;
const GENERATED_PRIME: u64 = 0x0000_0100_0000_01b3;
const PARENT_DIGEST_PRIME: u64 = 0x0000_0000_c2b2_ae35;
const FINGERPRINT_PARENT_PRIME: u64 = 0xff51_afd7_ed55_8ccd;
const FINGERPRINT_PRIME: u64 = 0x0000_0001_65b1_e9dd;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct ParentLoopSummary {
    state_count: u64,
    generated_count: u64,
    parent_digest: u64,
    fingerprint: u64,
    status: u64,
}

impl ParentLoopSummary {
    fn from_slots(slots: [u64; SUMMARY_SLOTS]) -> Self {
        Self {
            state_count: slots[0],
            generated_count: slots[1],
            parent_digest: slots[2],
            fingerprint: slots[3],
            status: slots[4],
        }
    }
}

fn store_summary_slot(fb: &mut FunctionBuilder<'_>, out: ValueId, slot: u64, value: ValueId) {
    let slot = fb.iconst(Ty::U64, i128::from(slot));
    let ptr = fb.gep(Ty::U64, out, vec![slot]);
    fb.store(Ty::U64, ptr, value);
}

fn build_minimal_parent_loop_module() -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("ty_bfs_minimal_o1_o3_summary");
    let entry_ty = mb.add_func_type(vec![Ty::Ptr, Ty::U64, Ty::Ptr], vec![Ty::U64]);

    {
        let mut fb = mb.function(ENTRY_NAME, entry_ty);

        let entry = fb.create_block();
        let parents = fb.add_block_param(entry, Ty::Ptr);
        let parent_count = fb.add_block_param(entry, Ty::U64);
        let summary = fb.add_block_param(entry, Ty::Ptr);

        let header = fb.create_block();
        let idx = fb.add_block_param(header, Ty::U64);
        let state_count = fb.add_block_param(header, Ty::U64);
        let generated_count = fb.add_block_param(header, Ty::U64);
        let parent_digest = fb.add_block_param(header, Ty::U64);
        let fingerprint = fb.add_block_param(header, Ty::U64);
        let status = fb.add_block_param(header, Ty::U64);

        let body = fb.create_block();

        let done = fb.create_block();
        let done_state_count = fb.add_block_param(done, Ty::U64);
        let done_generated_count = fb.add_block_param(done, Ty::U64);
        let done_parent_digest = fb.add_block_param(done, Ty::U64);
        let done_fingerprint = fb.add_block_param(done, Ty::U64);
        let done_status = fb.add_block_param(done, Ty::U64);

        fb.switch_to_block(entry);
        let zero = fb.iconst(Ty::U64, 0);
        let fingerprint_seed = fb.iconst(Ty::U64, i128::from(FINGERPRINT_SEED));
        let parent_digest_seed = fb.iconst(Ty::U64, i128::from(PARENT_DIGEST_SEED));
        fb.br(
            header,
            vec![zero, zero, zero, parent_digest_seed, fingerprint_seed, zero],
        );

        fb.switch_to_block(header);
        let has_parent = fb.icmp(ICmpOp::Ult, Ty::U64, idx, parent_count);
        fb.condbr(
            has_parent,
            body,
            vec![],
            done,
            vec![
                state_count,
                generated_count,
                parent_digest,
                fingerprint,
                status,
            ],
        );

        fb.switch_to_block(body);
        let parent_ptr = fb.gep(Ty::U64, parents, vec![idx]);
        let parent = fb.load(Ty::U64, parent_ptr);
        let one = fb.iconst(Ty::U64, 1);
        let next_idx = fb.binop(BinOp::Add, Ty::U64, idx, one);
        let next_state_count = fb.binop(BinOp::Add, Ty::U64, state_count, one);
        let next_generated_count = fb.binop(BinOp::Add, Ty::U64, generated_count, one);

        let idx_prime = fb.iconst(Ty::U64, i128::from(IDX_PRIME));
        let idx_term = fb.binop(BinOp::Mul, Ty::U64, idx, idx_prime);
        let generated_prime = fb.iconst(Ty::U64, i128::from(GENERATED_PRIME));
        let generated_term = fb.binop(BinOp::Mul, Ty::U64, next_generated_count, generated_prime);
        let parent_mix = fb.binop(BinOp::Xor, Ty::U64, parent, idx_term);
        let parent_mix = fb.binop(BinOp::Xor, Ty::U64, parent_mix, generated_term);
        let parent_xor = fb.binop(BinOp::Xor, Ty::U64, parent_digest, parent_mix);
        let parent_digest_prime = fb.iconst(Ty::U64, i128::from(PARENT_DIGEST_PRIME));
        let parent_scaled = fb.binop(BinOp::Mul, Ty::U64, parent_xor, parent_digest_prime);
        let next_parent_digest = fb.binop(BinOp::Add, Ty::U64, parent_scaled, next_state_count);

        let fingerprint_parent_prime = fb.iconst(Ty::U64, i128::from(FINGERPRINT_PARENT_PRIME));
        let parent_fingerprint_term =
            fb.binop(BinOp::Mul, Ty::U64, parent, fingerprint_parent_prime);
        let fingerprint_xor = fb.binop(BinOp::Xor, Ty::U64, fingerprint, next_parent_digest);
        let fingerprint_with_parent = fb.binop(
            BinOp::Add,
            Ty::U64,
            fingerprint_xor,
            parent_fingerprint_term,
        );
        let fingerprint_with_idx = fb.binop(BinOp::Add, Ty::U64, fingerprint_with_parent, idx);
        let fingerprint_prime = fb.iconst(Ty::U64, i128::from(FINGERPRINT_PRIME));
        let fingerprint_scaled =
            fb.binop(BinOp::Mul, Ty::U64, fingerprint_with_idx, fingerprint_prime);
        let next_fingerprint = fb.binop(
            BinOp::Add,
            Ty::U64,
            fingerprint_scaled,
            next_generated_count,
        );

        let status_delta = fb.binop(BinOp::Sub, Ty::U64, next_generated_count, next_state_count);
        let next_status = fb.binop(BinOp::Add, Ty::U64, status, status_delta);

        fb.br(
            header,
            vec![
                next_idx,
                next_state_count,
                next_generated_count,
                next_parent_digest,
                next_fingerprint,
                next_status,
            ],
        );

        fb.switch_to_block(done);
        store_summary_slot(&mut fb, summary, 0, done_state_count);
        store_summary_slot(&mut fb, summary, 1, done_generated_count);
        store_summary_slot(&mut fb, summary, 2, done_parent_digest);
        store_summary_slot(&mut fb, summary, 3, done_fingerprint);
        store_summary_slot(&mut fb, summary, 4, done_status);
        fb.ret(vec![done_status]);

        fb.build();
    }

    mb.build()
}

fn compile_to_jit(module: &trust_ir::Module, opt_level: OptLevel) -> ExecutableBuffer {
    compile_to_jit_with_profile_hooks(module, opt_level, ProfileHookMode::None)
}

fn compile_to_jit_with_profile_hooks(
    module: &trust_ir::Module,
    opt_level: OptLevel,
    profile_hooks: ProfileHookMode,
) -> ExecutableBuffer {
    let mut config = CompilerConfig::jit_fast(Target::Aarch64);
    config.opt_level = opt_level;
    Compiler::new(config)
        .compile_module_to_jit_with_profile_hooks(module, &HashMap::new(), profile_hooks)
        .unwrap_or_else(|err| {
            panic!("{opt_level:?} compile with {profile_hooks:?} hooks failed: {err}")
        })
        .buffer
}

fn compile_to_jit_with_profile_use(
    module: &trust_ir::Module,
    opt_level: OptLevel,
    profile: ProfData,
) -> ExecutableBuffer {
    let mut config = CompilerConfig::jit_fast(Target::Aarch64);
    config.opt_level = opt_level;
    Compiler::new(config)
        .with_profile_use(profile)
        .compile_module_to_jit(module, &HashMap::new())
        .unwrap_or_else(|err| panic!("{opt_level:?} profile-use compile failed: {err}"))
        .buffer
}

fn entry_signature() -> trust_cg_codegen::jit_contract::SymbolSignature {
    extern_c_signature(vec![abi_ptr(), abi_i64(), abi_ptr()], vec![abi_i64()])
}

fn run_buffer(
    buffer: &ExecutableBuffer,
    opt_level: OptLevel,
    parents: &[u64],
) -> ParentLoopSummary {
    let entry: EntryFn = bind_ty_reducer_entry(buffer, opt_level, ENTRY_NAME, entry_signature());

    let mut slots = [u64::MAX; SUMMARY_SLOTS];
    let status = entry(parents.as_ptr(), parents.len() as u64, slots.as_mut_ptr());
    assert_eq!(status, slots[4], "{opt_level:?} return/status mismatch");
    ParentLoopSummary::from_slots(slots)
}

fn run_at(opt_level: OptLevel, parents: &[u64]) -> ParentLoopSummary {
    let module = build_minimal_parent_loop_module();
    let buffer = compile_to_jit(&module, opt_level);
    run_buffer(&buffer, opt_level, parents)
}

fn reference_summary(parents: &[u64]) -> ParentLoopSummary {
    let mut summary = ParentLoopSummary {
        state_count: 0,
        generated_count: 0,
        parent_digest: PARENT_DIGEST_SEED,
        fingerprint: FINGERPRINT_SEED,
        status: 0,
    };

    for (idx, &parent) in parents.iter().enumerate() {
        let idx = idx as u64;
        summary.state_count = summary.state_count.wrapping_add(1);
        summary.generated_count = summary.generated_count.wrapping_add(1);

        let parent_mix = parent
            ^ idx.wrapping_mul(IDX_PRIME)
            ^ summary.generated_count.wrapping_mul(GENERATED_PRIME);
        summary.parent_digest = (summary.parent_digest ^ parent_mix)
            .wrapping_mul(PARENT_DIGEST_PRIME)
            .wrapping_add(summary.state_count);

        summary.fingerprint = (summary.fingerprint ^ summary.parent_digest)
            .wrapping_add(parent.wrapping_mul(FINGERPRINT_PARENT_PRIME))
            .wrapping_add(idx)
            .wrapping_mul(FINGERPRINT_PRIME)
            .wrapping_add(summary.generated_count);

        summary.status = summary
            .status
            .wrapping_add(summary.generated_count.wrapping_sub(summary.state_count));
    }

    summary
}

fn assert_summary_eq(actual: ParentLoopSummary, expected: ParentLoopSummary, context: &str) {
    assert_eq!(
        actual.state_count, expected.state_count,
        "{context} state_count mismatch"
    );
    assert_eq!(
        actual.generated_count, expected.generated_count,
        "{context} generated_count mismatch"
    );
    assert_eq!(
        actual.parent_digest, expected.parent_digest,
        "{context} parent_digest mismatch"
    );
    assert_eq!(
        actual.fingerprint, expected.fingerprint,
        "{context} fingerprint mismatch"
    );
    assert_eq!(actual.status, expected.status, "{context} status mismatch");
}

fn assert_parent_loop_o3_count_shape(counts: &[(u32, u64)], parent_count: usize) {
    let parent_count = parent_count as u64;
    let mut hits: Vec<u64> = counts.iter().map(|(_, hits)| *hits).collect();
    hits.sort_unstable();

    assert_eq!(
        counts.iter().find(|(block_id, _)| *block_id == 0),
        Some(&(0, 1)),
        "entry block should run once"
    );
    assert_eq!(
        counts.len(),
        4,
        "O3 should preserve the entry, loop test/body, and done blocks"
    );
    assert_eq!(hits, vec![1, 1, parent_count, parent_count]);
    assert_eq!(
        counts.iter().map(|(_, hits)| *hits).sum::<u64>(),
        (parent_count * 2) + 2
    );
}

fn assert_parent_loop_o3_profile_shape(profile: &FunctionProfile, parent_count: usize) {
    let counts: Vec<(u32, u64)> = profile
        .blocks
        .iter()
        .map(|block| (block.block_id, block.hits))
        .collect();
    assert_eq!(profile.call_count, 1);
    assert_parent_loop_o3_count_shape(&counts, parent_count);
}

fn opt_level_num(opt_level: OptLevel) -> u8 {
    match opt_level {
        OptLevel::O0 => 0,
        OptLevel::O1 => 1,
        OptLevel::O2 => 2,
        OptLevel::O3 => 3,
    }
}

fn parent_loop_profile_key(opt_level: OptLevel) -> CacheKey {
    let mut module_identity = Vec::new();
    module_identity.extend_from_slice(b"trust-cg.ty.parent_loop.pgo_canary.v1\0");
    module_identity.extend_from_slice(ENTRY_NAME.as_bytes());

    CacheKey::new(
        stable_hash(&module_identity),
        opt_level_num(opt_level),
        format!("{}-unknown-unknown", Target::Aarch64.name()),
        "generic-aarch64".to_owned(),
        vec!["+neon".to_owned()],
    )
}

fn tmp_profdata_path(label: &str) -> std::path::PathBuf {
    env::temp_dir().join(format!(
        "trust_cg_ty_parent_loop_{}_{}.profdata",
        label,
        std::process::id()
    ))
}

#[test]
fn ty_bfs_minimal_parent_loop_o1_o3_status_summary_matches_reference() {
    let cases: &[(&str, &[u64])] = &[
        ("empty", &[]),
        ("singleton", &[0x45]),
        ("duplicate_parent", &[0x45, 0x45]),
    ];

    for (name, parents) in cases {
        let expected = reference_summary(parents);
        let o1 = run_at(OptLevel::O1, parents);
        let o3 = run_at(OptLevel::O3, parents);

        assert_summary_eq(o1, expected, &format!("O1 {name}"));
        assert_summary_eq(o3, expected, &format!("O3 {name}"));
        assert_summary_eq(o3, o1, &format!("O3 vs O1 {name}"));
    }
}

#[test]
fn ty_bfs_minimal_parent_loop_pgo_canary_profile_round_trip() {
    let opt_level = OptLevel::O3;
    let parents = &[2, 5, 8, 13, 21, 34][..];
    let expected = reference_summary(parents);
    let module = build_minimal_parent_loop_module();

    let profiled_buffer =
        compile_to_jit_with_profile_hooks(&module, opt_level, ProfileHookMode::BlockCounts);
    let profiled_summary = run_buffer(&profiled_buffer, opt_level, parents);
    assert_summary_eq(profiled_summary, expected, "O3 profile-generate canary");

    let mut observed_counts = profiled_buffer.block_counts(ENTRY_NAME);
    observed_counts.sort_by_key(|(block_id, _)| *block_id);
    assert_parent_loop_o3_count_shape(&observed_counts, parents.len());

    let profile_key = parent_loop_profile_key(opt_level);
    let path = tmp_profdata_path("o3_canary");
    let captured = profiled_buffer
        .write_block_profdata_with_key(&profile_key, &path)
        .expect("write block profdata");
    let captured_function = captured.function(ENTRY_NAME).expect("captured profile");
    assert_parent_loop_o3_profile_shape(captured_function, parents.len());

    let loaded = read_from_path(&path).expect("read block profdata");
    assert_eq!(loaded, captured);
    enforce_fresh(&loaded, &profile_key).expect("same-opt profile key should be fresh");

    let profile_use_buffer = compile_to_jit_with_profile_use(&module, opt_level, loaded);
    let profile_use_summary = run_buffer(&profile_use_buffer, opt_level, parents);
    assert_summary_eq(profile_use_summary, expected, "O3 profile-use canary");
    assert!(
        profile_use_buffer.block_counts(ENTRY_NAME).is_empty(),
        "profile-use compile should consume counters without reinstrumenting"
    );

    let _ = fs::remove_file(path);
}
