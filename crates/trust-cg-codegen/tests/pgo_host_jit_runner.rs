// Host-JIT PGO runner integration tests.

#![cfg(any(target_arch = "aarch64", target_arch = "x86_64"))]

use std::{env, fs};

use trust_cg_codegen::pipeline::{self, OptLevel};
use trust_cg_codegen::target::TargetSpec;
use trust_cg_codegen::{
    CompilerConfig, ExecutableBuffer, HOST_JIT_PGO_ENTRY_SHAPE_CODES,
    HOST_JIT_PGO_PROFILE_AUTHORITY_MANIFEST_ROW_KEYS, HOST_JIT_PGO_PROFILE_AUTHORITY_REASON_CODES,
    HOST_JIT_PGO_PROFILE_AUTHORITY_STATUS_CODES,
    HOST_JIT_PGO_PROFILE_USE_REASON_OPT_LEVEL_BELOW_O2,
    HOST_JIT_PGO_PROFILE_USE_REASON_OPT_LEVEL_ENABLES, HOST_JIT_PGO_RUNNER_ERROR_REASON_CODES,
    HostJitPgoEntry, HostJitPgoProfileAuthorityManifestRow,
    HostJitPgoProfileAuthorityManifestRowKind, HostJitPgoProfileAuthorityReason,
    HostJitPgoRunnerError, TRUST_CG_HOST_JIT_PGO_PROFILE_AUTHORITY_EVIDENCE_SCHEMA,
    TRUST_CG_HOST_JIT_PGO_PROFILE_AUTHORITY_MANIFEST_SCHEMA,
    TRUST_CG_HOST_JIT_PGO_PROVENANCE_DESCRIPTOR_SCHEMA, TRUST_CG_PROFILE_REPORT_SCHEMA_V1, Target,
    TyParentLoopSummary, compile_host_jit_with_profile_use, host_jit_pgo_provenance_descriptor,
    pgo_cache_key, pgo_target_cpu, pgo_target_features, pgo_target_triple, run_host_jit_pgo,
};
use trust_cg_opt::pgo::{FunctionProfile, ProfDataError, enforce_fresh, read_from_path};
use trust_ir::{BinOp, ICmpOp, Ty, ValueId};
use trust_ir_build::{FunctionBuilder, ModuleBuilder};

const ENTRY_NAME: &str = "pgo_host_jit_ty_parent_loop";
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

impl From<TyParentLoopSummary> for ParentLoopSummary {
    fn from(summary: TyParentLoopSummary) -> Self {
        Self {
            state_count: summary.state_count,
            generated_count: summary.generated_count,
            parent_digest: summary.parent_digest,
            fingerprint: summary.fingerprint,
            status: summary.status,
        }
    }
}

fn store_summary_slot(fb: &mut FunctionBuilder<'_>, out: ValueId, slot: u64, value: ValueId) {
    let slot = fb.iconst(Ty::U64, i128::from(slot));
    let ptr = fb.gep(Ty::U64, out, vec![slot]);
    fb.store(Ty::U64, ptr, value);
}

fn build_parent_loop_module() -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("pgo_host_jit_runner_parent_loop");
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

fn build_unsupported_abi_module() -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("pgo_host_jit_runner_unsupported");
    let entry_ty = mb.add_func_type(vec![Ty::Ptr], vec![Ty::U64]);

    {
        let mut fb = mb.function("unsupported_parent_loop", entry_ty);
        let entry = fb.create_block();
        let _ptr = fb.add_block_param(entry, Ty::Ptr);
        fb.switch_to_block(entry);
        let zero = fb.iconst(Ty::U64, 0);
        fb.ret(vec![zero]);
        fb.build();
    }

    mb.build()
}

fn host_config(opt_level: OptLevel) -> CompilerConfig {
    let mut config = CompilerConfig::for_host_jit();
    config.opt_level = opt_level;
    config
}

fn host_target_spec() -> TargetSpec {
    TargetSpec::unknown_for_architecture(Target::host())
}

fn non_host_target() -> Target {
    match Target::host() {
        Target::Aarch64 => Target::X86_64,
        Target::X86_64 | Target::Riscv64 => Target::Aarch64,
    }
}

fn tmp_profdata_path(label: &str) -> std::path::PathBuf {
    env::temp_dir().join(format!(
        "trust_cg_pgo_host_jit_runner_{}_{}.profdata",
        label,
        std::process::id()
    ))
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

fn assert_parent_loop_o3_profile(fp: &FunctionProfile, parent_count: usize) {
    let parent_count = parent_count as u64;
    let mut hits: Vec<u64> = fp.blocks.iter().map(|block| block.hits).collect();
    hits.sort_unstable();

    assert_eq!(fp.call_count, 1);
    #[cfg(target_arch = "aarch64")]
    let (expected_block_count, expected_hits, expected_total_hits, shape) = (
        4,
        vec![1, 1, parent_count, parent_count],
        (parent_count * 2) + 2,
        "AArch64 O3 should preserve the entry, loop test/body, and done blocks",
    );
    // The x86-64 counters are injected AFTER the O2/O3 `x86_rotate` pass
    // (loop rotation via jump threading through pure-test blocks), so they
    // report the machine CFG the JIT actually executes — which is what the
    // target-keyed, block-id-keyed profile must describe for profile-use to
    // bind hotness to the recompiled function's blocks. In that rotated CFG
    // the header runs ONCE as the loop guard (the latch re-tests the bound at
    // the bottom of the body and back-edges straight to the body block), the
    // body runs once per parent, and the split exit-merge block plus done run
    // once each. Verified against the spliced-trampoline disassembly on
    // 2026-07-31: entry=1, guard=1, body=N, exit-merge=1, done=1.
    #[cfg(target_arch = "x86_64")]
    let (expected_block_count, expected_hits, expected_total_hits, shape) = (
        5,
        vec![1, 1, 1, 1, parent_count],
        parent_count + 4,
        "x86-64 O3 rotates the loop: guard runs once, bottom-tested body runs per parent",
    );
    assert_eq!(
        fp.blocks.len(),
        expected_block_count,
        "{shape}: {:?}",
        fp.blocks
    );
    assert_eq!(hits, expected_hits);
    assert_eq!(fp.block_hits(0), 1, "entry block should run once");
    assert_eq!(
        fp.blocks.iter().map(|block| block.hits).sum::<u64>(),
        expected_total_hits
    );
}

fn run_buffer(buffer: &ExecutableBuffer, parents: &[u64]) -> ParentLoopSummary {
    let func = unsafe { buffer.get_fn_bound::<EntryFn>(ENTRY_NAME) }
        .expect("parent-loop symbol should be emitted");
    let mut slots = [u64::MAX; SUMMARY_SLOTS];
    let status = (*func.as_ref())(parents.as_ptr(), parents.len() as u64, slots.as_mut_ptr());
    assert_eq!(status, slots[4], "return/status mismatch");
    ParentLoopSummary::from_slots(slots)
}

#[test]
fn host_jit_runner_generates_binary_profdata_and_compiles_profile_use() {
    let descriptor = host_jit_pgo_provenance_descriptor();
    assert_eq!(
        descriptor.schema,
        TRUST_CG_HOST_JIT_PGO_PROVENANCE_DESCRIPTOR_SCHEMA
    );
    assert_eq!(
        descriptor.profile_report_schema,
        TRUST_CG_PROFILE_REPORT_SCHEMA_V1
    );
    assert!(
        descriptor
            .profile_key_fields
            .contains(&"profile_key_digest")
    );
    assert!(descriptor.profile_key_fields.contains(&"cache_key_version"));
    assert!(
        descriptor
            .profile_use_soundness_fields
            .contains(&"scheduled")
    );
    assert!(descriptor.profile_use_fields.contains(&"summary"));
    assert!(
        descriptor
            .profile_use_reason_codes
            .contains(&HOST_JIT_PGO_PROFILE_USE_REASON_OPT_LEVEL_ENABLES)
    );
    assert!(
        descriptor
            .profile_use_reason_codes
            .contains(&HOST_JIT_PGO_PROFILE_USE_REASON_OPT_LEVEL_BELOW_O2)
    );
    assert_eq!(
        descriptor.profile_authority_evidence_schema,
        TRUST_CG_HOST_JIT_PGO_PROFILE_AUTHORITY_EVIDENCE_SCHEMA
    );
    assert_eq!(
        descriptor.profile_authority_manifest_schema,
        TRUST_CG_HOST_JIT_PGO_PROFILE_AUTHORITY_MANIFEST_SCHEMA
    );
    assert!(
        descriptor
            .profile_authority_fields
            .contains(&"authorizes_useful_native")
    );
    assert!(
        descriptor
            .profile_authority_status_codes
            .contains(&"authoritative_for_compiled_function")
    );
    assert!(
        HOST_JIT_PGO_PROFILE_AUTHORITY_STATUS_CODES
            .contains(&"not_authoritative_for_compiled_function")
    );
    assert!(
        descriptor
            .profile_authority_manifest_row_keys
            .contains(&"profile_authority.authorizes_profile_reuse")
    );
    assert!(
        HOST_JIT_PGO_PROFILE_AUTHORITY_MANIFEST_ROW_KEYS
            .contains(&"profile_authority.target_features")
    );
    assert!(HOST_JIT_PGO_PROFILE_AUTHORITY_REASON_CODES.contains(&"profile_use_not_scheduled"));
    assert!(
        descriptor
            .runner_error_reason_codes
            .contains(&"profdata_stale_profile_key")
    );
    assert!(HOST_JIT_PGO_RUNNER_ERROR_REASON_CODES.contains(&"host_target_mismatch"));
    assert!(HOST_JIT_PGO_ENTRY_SHAPE_CODES.contains(&"ty_parent_loop_u64_return"));
    assert!(!descriptor.authorizes_useful_native);

    let module = build_parent_loop_module();
    let trust_ir_bytes = pipeline::encode_tmbc(&module).expect("encode tmbc");
    let config = host_config(OptLevel::O3);
    let target_spec = host_target_spec();
    let parents = vec![2, 5, 8, 13, 21, 34];
    let expected = reference_summary(&parents);
    let path = tmp_profdata_path("round_trip");
    let generated = run_host_jit_pgo(
        &module,
        &trust_ir_bytes,
        &config,
        target_spec,
        &path,
        HostJitPgoEntry::TyParentLoopU64Return {
            entry: ENTRY_NAME.to_string(),
            parents: parents.clone(),
        },
    )
    .expect("host-JIT PGO capture should succeed");

    let observed_summary = generated
        .observation
        .ty_summary
        .map(ParentLoopSummary::from);
    assert_eq!(
        generated.observation.return_value,
        Some(expected.status),
        "observed summary: {observed_summary:?}; expected summary: {expected:?}"
    );
    assert_eq!(observed_summary, Some(expected));
    let fp = generated
        .profile
        .functions
        .iter()
        .find(|fp| fp.name == ENTRY_NAME)
        .expect("profile should contain parent-loop function");
    assert_parent_loop_o3_profile(fp, parents.len());

    let bytes = fs::read(&path).expect("profdata file should be readable");
    assert_eq!(&bytes[..8], b"trcg-pgo");
    assert_ne!(bytes[0], b'{', "runner must write binary v1 profdata");

    let loaded = read_from_path(&path).expect("binary profdata reloads");
    assert_eq!(loaded, generated.profile);
    let key = pgo_cache_key(&trust_ir_bytes, &config, target_spec);
    enforce_fresh(&loaded, &key).expect("matching full profile key is fresh");
    assert_eq!(
        loaded.module_hash,
        format!("{:032x}", trust_cg_opt::stable_hash(&trust_ir_bytes))
    );
    assert_eq!(loaded.target_triple, pgo_target_triple(target_spec));
    assert_eq!(loaded.target_cpu, pgo_target_cpu(config.target));
    assert_eq!(loaded.target_features, pgo_target_features(config.target));

    let report_json = serde_json::to_value(&generated.report).expect("serialize report");
    assert_eq!(report_json["schema"], TRUST_CG_PROFILE_REPORT_SCHEMA_V1);
    assert_eq!(report_json["mode"], "profile-generate");
    assert_eq!(report_json["capture"]["kind"], "host-jit-canary");
    assert_eq!(report_json["capture"]["hook_mode"], "block-counts");
    assert_eq!(report_json["capture"]["entry"], ENTRY_NAME);
    assert_eq!(
        report_json["capture"]["entry_shape"],
        "ty_parent_loop_u64_return"
    );
    assert_eq!(
        report_json["capture"]["window"]["kind"],
        "bounded-input-window"
    );
    assert_eq!(report_json["profile_key"]["profile_key_digest"], key.hex());

    let profile_use = compile_host_jit_with_profile_use(
        &module,
        &trust_ir_bytes,
        &config,
        target_spec,
        loaded.clone(),
        Some(&path),
    )
    .expect("profile-use compile should accept fresh runner profile");
    assert_eq!(profile_use.report.schema, TRUST_CG_PROFILE_REPORT_SCHEMA_V1);
    assert_eq!(profile_use.report.mode, "profile-use");
    assert!(profile_use.report.profile_use.fresh);
    assert!(profile_use.report.profile_use.scheduled);
    assert_eq!(
        profile_use.report.profile_use.pass.as_deref(),
        Some("profile-use")
    );
    assert_eq!(
        profile_use.report.profile_use.reason.as_deref(),
        Some(HOST_JIT_PGO_PROFILE_USE_REASON_OPT_LEVEL_ENABLES)
    );
    assert!(profile_use.profile_reuse_sound_for_compiled_function());
    assert!(
        profile_use
            .report
            .profile_reuse_sound_for_compiled_function()
    );
    assert_eq!(
        profile_use.report.profile_authority_reason(),
        HostJitPgoProfileAuthorityReason::FreshScheduledProfileUse
    );
    assert_eq!(
        HostJitPgoProfileAuthorityReason::FreshScheduledProfileUse.code(),
        "fresh_scheduled_profile_use"
    );
    let authority = profile_use.profile_authority_evidence();
    assert_eq!(
        authority.schema,
        TRUST_CG_HOST_JIT_PGO_PROFILE_AUTHORITY_EVIDENCE_SCHEMA
    );
    assert_eq!(authority.status, "authoritative_for_compiled_function");
    assert_eq!(authority.reason, "fresh_scheduled_profile_use");
    assert_eq!(authority.profile_key_digest, key.hex());
    assert!(authority.target_compatible);
    assert!(authority.compiled_function_profile_reuse_sound);
    assert!(authority.authorizes_profile_reuse);
    assert!(!authority.authorizes_useful_native);
    let authority_rows = authority.manifest_rows();
    assert_eq!(
        authority_rows[0].kind,
        HostJitPgoProfileAuthorityManifestRowKind::ManifestSchema
    );
    assert_eq!(authority_rows[0].kind_code(), "manifest.schema");
    let authority_lines = authority.manifest_lines();
    assert!(authority_lines.contains(&format!(
        "manifest.schema={}",
        TRUST_CG_HOST_JIT_PGO_PROFILE_AUTHORITY_MANIFEST_SCHEMA
    )));
    assert!(
        authority_lines
            .contains(&"profile_authority.status=authoritative_for_compiled_function".to_string())
    );
    assert!(
        authority_lines
            .contains(&"profile_authority.reason=fresh_scheduled_profile_use".to_string())
    );
    assert!(authority_lines.contains(&format!(
        "profile_authority.profile_key_digest={}",
        key.hex()
    )));
    assert!(
        authority_lines.contains(&"profile_authority.authorizes_profile_reuse=true".to_string())
    );
    assert!(
        authority_lines.contains(&"profile_authority.authorizes_useful_native=false".to_string())
    );
    let escaped = HostJitPgoProfileAuthorityManifestRow::typed(
        HostJitPgoProfileAuthorityManifestRowKind::Reason,
        "line\nwith=equals\\slash",
    );
    assert_eq!(
        escaped.to_key_value_line(),
        "profile_authority.reason=line\\nwith\\=equals\\\\slash"
    );

    let mut unscheduled = profile_use.report.clone();
    unscheduled.profile_use.scheduled = false;
    unscheduled.profile_use.pass = None;
    unscheduled.profile_use.reason =
        Some(HOST_JIT_PGO_PROFILE_USE_REASON_OPT_LEVEL_BELOW_O2.to_string());
    assert!(!unscheduled.profile_reuse_sound_for_compiled_function());
    assert_eq!(
        unscheduled.profile_authority_reason(),
        HostJitPgoProfileAuthorityReason::ProfileUseNotScheduled
    );
    let unscheduled_authority = unscheduled.profile_authority_evidence();
    assert_eq!(
        unscheduled_authority.status,
        "not_authoritative_for_compiled_function"
    );
    assert_eq!(unscheduled_authority.reason, "profile_use_not_scheduled");
    assert!(!unscheduled_authority.authorizes_profile_reuse);
    assert!(!unscheduled_authority.authorizes_useful_native);
    let unscheduled_lines = unscheduled_authority.manifest_lines();
    assert!(
        unscheduled_lines.contains(
            &"profile_authority.status=not_authoritative_for_compiled_function".to_string()
        )
    );
    assert!(
        unscheduled_lines
            .contains(&"profile_authority.reason=profile_use_not_scheduled".to_string())
    );
    assert!(
        unscheduled_lines.contains(&"profile_authority.authorizes_profile_reuse=false".to_string())
    );

    let profile_use_summary = run_buffer(&profile_use.jit.buffer, &parents);
    assert_eq!(profile_use_summary, expected);
    assert!(
        profile_use.jit.buffer.block_counts(ENTRY_NAME).is_empty(),
        "profile-use compile should consume counters without reinstrumenting"
    );

    let _ = fs::remove_file(path);
}

#[test]
fn host_jit_runner_fails_closed_for_target_mismatch_unsupported_abi_and_stale_key() {
    let module = build_parent_loop_module();
    let trust_ir_bytes = pipeline::encode_tmbc(&module).expect("encode tmbc");
    let path = tmp_profdata_path("fail_closed");
    let mut wrong_target_config = host_config(OptLevel::O3);
    wrong_target_config.target = non_host_target();
    let err = run_host_jit_pgo(
        &module,
        &trust_ir_bytes,
        &wrong_target_config,
        TargetSpec::unknown_for_architecture(wrong_target_config.target),
        &path,
        HostJitPgoEntry::TyParentLoopU64Return {
            entry: ENTRY_NAME.to_string(),
            parents: vec![1, 2, 3],
        },
    )
    .expect_err("host-target mismatch must fail closed");
    assert!(matches!(
        err,
        HostJitPgoRunnerError::HostTargetMismatch { .. }
    ));
    assert_eq!(err.reason_code(), "host_target_mismatch");
    assert!(!err.target_compatible());

    let unsupported = build_unsupported_abi_module();
    let unsupported_bytes = pipeline::encode_tmbc(&unsupported).expect("encode unsupported tmbc");
    let config = host_config(OptLevel::O3);
    let err = run_host_jit_pgo(
        &unsupported,
        &unsupported_bytes,
        &config,
        host_target_spec(),
        &path,
        HostJitPgoEntry::TyParentLoopU64Return {
            entry: "unsupported_parent_loop".to_string(),
            parents: vec![1],
        },
    )
    .expect_err("unsupported ABI shape must fail closed");
    assert!(matches!(
        err,
        HostJitPgoRunnerError::UnsupportedAbiShape { .. }
    ));
    assert_eq!(err.reason_code(), "unsupported_abi_shape");
    assert!(err.target_compatible());

    let generated = run_host_jit_pgo(
        &module,
        &trust_ir_bytes,
        &config,
        host_target_spec(),
        &path,
        HostJitPgoEntry::TyParentLoopU64Return {
            entry: ENTRY_NAME.to_string(),
            parents: vec![2, 5, 8],
        },
    )
    .expect("fresh profile generation should succeed");
    let mut stale_config = config.clone();
    stale_config.opt_level = OptLevel::O2;
    let err = compile_host_jit_with_profile_use(
        &module,
        &trust_ir_bytes,
        &stale_config,
        host_target_spec(),
        generated.profile,
        Some(&path),
    )
    .expect_err("stale profile key must fail closed");
    assert!(matches!(
        err,
        HostJitPgoRunnerError::ProfData(ProfDataError::StaleProfileKey { .. })
    ));
    assert_eq!(err.reason_code(), "profdata_stale_profile_key");
    assert!(err.target_compatible());

    let _ = fs::remove_file(path);
}
