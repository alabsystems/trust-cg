// trust-cg-cli/tests/pgo_profile_use.rs - CLI profile-use wiring tests (#396)
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use std::path::PathBuf;
use std::process::Command;
#[cfg(target_arch = "aarch64")]
use std::process::{Output, Stdio};
#[cfg(target_arch = "aarch64")]
use std::time::{Duration, Instant};

use trust_cg_codegen::pipeline::encode_tmbc;
use trust_cg_codegen::target::{Target, TargetSpec};
#[cfg(target_arch = "aarch64")]
use trust_cg_ir::{MachFunction, Signature, Type};
use trust_cg_opt::CacheKey;
use trust_cg_opt::pgo::{BlockProfile, FunctionProfile, ProfData, write_to_path};
use trust_cg_opt::stable_hash;
use trust_ir::ICmpOp;
#[cfg(target_arch = "aarch64")]
use trust_ir::{BinOp, ValueId};
use trust_ir::{Module as TrustIrModule, Ty};
#[cfg(target_arch = "aarch64")]
use trust_ir_build::FunctionBuilder;
use trust_ir_build::ModuleBuilder;

#[cfg(target_arch = "aarch64")]
const TY_PARENT_LOOP_ENTRY: &str = "ty_cli_parent_loop";
#[cfg(target_arch = "aarch64")]
const TY_PARENT_INPUTS: &[u64] = &[2, 5, 8, 13, 21, 34];
#[cfg(target_arch = "aarch64")]
const TY_PARENT_LOOP_PROFILE_GENERATE_TIMEOUT: Duration = Duration::from_secs(120);

#[cfg(target_arch = "aarch64")]
fn command_output_with_timeout(mut command: Command, timeout: Duration) -> std::io::Result<Output> {
    use std::io::Read;

    command
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());

    let mut child = command.spawn()?;
    // Drain both pipes CONCURRENTLY while waiting. The previous
    // wait-then-collect loop never read the pipes until exit, so a child
    // producing more than the ~64 KiB pipe buffer of diagnostics (the -O3
    // per-pass timing trace crossed that line) deadlocked on write(2) inside
    // its own logging and was then blamed for "timing out". Sampled stack:
    // pass_manager::log_pass_start blocked on stderr.
    let mut child_stdout = child.stdout.take().expect("piped stdout");
    let mut child_stderr = child.stderr.take().expect("piped stderr");
    let stdout_reader = std::thread::spawn(move || {
        let mut buf = Vec::new();
        let _ = child_stdout.read_to_end(&mut buf);
        buf
    });
    let stderr_reader = std::thread::spawn(move || {
        let mut buf = Vec::new();
        let _ = child_stderr.read_to_end(&mut buf);
        buf
    });
    let collect = |status,
                   stdout_reader: std::thread::JoinHandle<Vec<u8>>,
                   stderr_reader: std::thread::JoinHandle<Vec<u8>>| Output {
        status,
        stdout: stdout_reader.join().unwrap_or_default(),
        stderr: stderr_reader.join().unwrap_or_default(),
    };

    let started = Instant::now();
    loop {
        if let Some(status) = child.try_wait()? {
            return Ok(collect(status, stdout_reader, stderr_reader));
        }
        if started.elapsed() >= timeout {
            let _ = child.kill();
            let status = child.wait()?;
            let output = collect(status, stdout_reader, stderr_reader);
            panic!(
                "command timed out after {:?}; status: {}\nstdout:\n{}\nstderr:\n{}",
                timeout,
                output.status,
                String::from_utf8_lossy(&output.stdout),
                String::from_utf8_lossy(&output.stderr)
            );
        }
        std::thread::sleep(Duration::from_millis(100));
    }
}

#[cfg(target_arch = "aarch64")]
fn assert_ty_parent_loop_o3_profile(fp: &FunctionProfile, parent_count: usize) {
    let parent_count = parent_count as u64;
    let mut hits: Vec<u64> = fp.blocks.iter().map(|block| block.hits).collect();
    hits.sort_unstable();

    assert_eq!(fp.call_count, 1);
    assert_eq!(
        fp.blocks.len(),
        4,
        "O3 should preserve the entry, loop test/body, and done blocks"
    );
    assert_eq!(hits, vec![1, 1, parent_count, parent_count]);
    assert_eq!(fp.block_hits(0), 1, "entry block should run once");
    assert_eq!(
        fp.blocks.iter().map(|block| block.hits).sum::<u64>(),
        (parent_count * 2) + 2
    );
}

#[cfg(target_arch = "aarch64")]
fn write_ty_parent_loop_o3_profile(
    profile_path: &std::path::Path,
    tmbc: &[u8],
    parent_count: usize,
) {
    let parent_count = parent_count as u64;
    let mut profile = ProfData::new_with_key(&pgo_key(tmbc, 3));
    let mut function = FunctionProfile::new(TY_PARENT_LOOP_ENTRY);
    function.call_count = 1;
    function.blocks.push(BlockProfile::new(0, 1));
    function.blocks.push(BlockProfile::new(1, parent_count));
    function.blocks.push(BlockProfile::new(2, parent_count));
    function.blocks.push(BlockProfile::new(3, 1));
    profile.functions.push(function);
    write_to_path(&profile, profile_path).expect("write synthetic TY parent-loop profdata");
}

fn make_test_module() -> TrustIrModule {
    let mut mb = ModuleBuilder::new("cli_pgo_profile_use_test");
    let ty = mb.add_func_type(vec![], vec![Ty::I64]);
    let mut fb = mb.function("_return_42", ty);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let r = fb.iconst(Ty::I64, 42);
    fb.ret(vec![r]);
    fb.build();
    mb.build()
}

fn scratch_dir(test_name: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!(
        "trust_cg_cli_pgo_{}_{}",
        test_name,
        std::process::id()
    ));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create scratch dir");
    dir
}

fn trust_cg_bin() -> PathBuf {
    PathBuf::from(env!("CARGO_BIN_EXE_trust-cg"))
}

#[cfg(any(target_arch = "aarch64", target_arch = "x86_64"))]
fn profile_reports(stderr: &str) -> Vec<serde_json::Value> {
    const PREFIX: &str = "trust-cg: profile-report: ";
    stderr
        .lines()
        .filter_map(|line| line.strip_prefix(PREFIX))
        .map(|json| serde_json::from_str(json).expect("parse profile report JSON"))
        .collect()
}

/// The target triple the CLI derives for its default (architecture-only)
/// `--target aarch64` request. Post-merge, the AArch64 AOT/JIT paths resolve
/// the host OS/ABI by default (see `TargetSpec::default_for_architecture`), so
/// on this host the default triple is e.g. `aarch64-apple-darwin` rather than
/// the legacy `aarch64-unknown-unknown`. Derive it the same way the CLI does
/// (`target_triple_for` -> `with_default_os_abi().triple()`) so the profile
/// key the tests synthesize matches the compile-time key byte-for-byte.
fn default_aarch64_triple() -> String {
    TargetSpec::unknown_for_architecture(Target::Aarch64)
        .with_default_os_abi()
        .triple()
}

fn pgo_key_from_hash(module_hash: u128, opt_level: u8) -> CacheKey {
    CacheKey::new(
        module_hash,
        opt_level,
        default_aarch64_triple(),
        "generic-aarch64".into(),
        vec!["+neon".into()],
    )
}

fn pgo_key(tmbc: &[u8], opt_level: u8) -> CacheKey {
    pgo_key_from_hash(stable_hash(tmbc), opt_level)
}

fn write_module_and_profile_for_opt_level(
    dir: &std::path::Path,
    module_hash: u128,
    opt_level: u8,
) -> (PathBuf, PathBuf) {
    let module = make_test_module();
    let tmbc = encode_tmbc(&module).expect("encode tMBC");
    let tmbc_path = dir.join("module.tmbc");
    std::fs::write(&tmbc_path, &tmbc).expect("write tmbc");

    let mut profile = ProfData::new_with_key(&pgo_key_from_hash(module_hash, opt_level));
    let mut function = FunctionProfile::new("_return_42");
    function.call_count = 1;
    function.blocks.push(BlockProfile::new(0, 1));
    profile.functions.push(function);

    let profile_path = dir.join("module.profdata");
    write_to_path(&profile, &profile_path).expect("write profdata");
    (tmbc_path, profile_path)
}

fn write_module_and_profile(dir: &std::path::Path, module_hash: u128) -> (PathBuf, PathBuf) {
    write_module_and_profile_for_opt_level(dir, module_hash, 2)
}

#[cfg(target_arch = "aarch64")]
fn make_canary_module() -> TrustIrModule {
    let mut mb = ModuleBuilder::new("cli_pgo_canary_round_trip_test");
    let ty = mb.add_func_type(vec![Ty::I64], vec![Ty::I64]);
    let mut fb = mb.function("pgo_canary", ty);

    let entry = fb.create_block();
    let else_b = fb.create_block();
    let then_b = fb.create_block();
    let arg = fb.add_block_param(entry, Ty::I64);

    fb.switch_to_block(entry);
    let zero = fb.iconst(Ty::I64, 0);
    let is_zero = fb.icmp(ICmpOp::Eq, Ty::I64, arg, zero);
    fb.condbr(is_zero, then_b, vec![], else_b, vec![]);

    fb.switch_to_block(else_b);
    let v77 = fb.iconst(Ty::I64, 77);
    fb.ret(vec![v77]);

    fb.switch_to_block(then_b);
    let v11 = fb.iconst(Ty::I64, 11);
    fb.ret(vec![v11]);

    fb.build();
    mb.build()
}

#[cfg(target_arch = "aarch64")]
fn store_ty_summary_slot(fb: &mut FunctionBuilder<'_>, out: ValueId, slot: u64, value: ValueId) {
    let slot = fb.iconst(Ty::U64, i128::from(slot));
    let ptr = fb.gep(Ty::U64, out, vec![slot]);
    fb.store(Ty::U64, ptr, value);
}

#[cfg(target_arch = "aarch64")]
fn make_ty_parent_loop_module() -> TrustIrModule {
    const FINGERPRINT_SEED: u64 = 0x6d2b_79f5_aa17_6620;
    const PARENT_DIGEST_SEED: u64 = 0x9e37_79b9_6620_0001;
    const IDX_PRIME: u64 = 0x0000_0000_85eb_ca6b;
    const GENERATED_PRIME: u64 = 0x0000_0100_0000_01b3;
    const PARENT_DIGEST_PRIME: u64 = 0x0000_0000_c2b2_ae35;
    const FINGERPRINT_PARENT_PRIME: u64 = 0xff51_afd7_ed55_8ccd;
    const FINGERPRINT_PRIME: u64 = 0x0000_0001_65b1_e9dd;

    let mut mb = ModuleBuilder::new("cli_ty_parent_loop_pgo_test");
    let entry_ty = mb.add_func_type(vec![Ty::Ptr, Ty::U64, Ty::Ptr], vec![Ty::U64]);
    let mut fb = mb.function(TY_PARENT_LOOP_ENTRY, entry_ty);

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
    let parent_fingerprint_term = fb.binop(BinOp::Mul, Ty::U64, parent, fingerprint_parent_prime);
    let fingerprint_xor = fb.binop(BinOp::Xor, Ty::U64, fingerprint, next_parent_digest);
    let fingerprint_with_parent = fb.binop(
        BinOp::Add,
        Ty::U64,
        fingerprint_xor,
        parent_fingerprint_term,
    );
    let fingerprint_with_idx = fb.binop(BinOp::Add, Ty::U64, fingerprint_with_parent, idx);
    let fingerprint_prime = fb.iconst(Ty::U64, i128::from(FINGERPRINT_PRIME));
    let fingerprint_scaled = fb.binop(BinOp::Mul, Ty::U64, fingerprint_with_idx, fingerprint_prime);
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
    store_ty_summary_slot(&mut fb, summary, 0, done_state_count);
    store_ty_summary_slot(&mut fb, summary, 1, done_generated_count);
    store_ty_summary_slot(&mut fb, summary, 2, done_parent_digest);
    store_ty_summary_slot(&mut fb, summary, 3, done_fingerprint);
    store_ty_summary_slot(&mut fb, summary, 4, done_status);
    fb.ret(vec![done_status]);

    fb.build();
    mb.build()
}

#[cfg(target_arch = "x86_64")]
fn make_x86_constant_conditional_module() -> TrustIrModule {
    let mut mb = ModuleBuilder::new("cli_pgo_x86_constant_conditional_test");
    let ty = mb.add_func_type(vec![], vec![Ty::I64]);
    let mut fb = mb.function("pgo_x86_selective", ty);

    let entry = fb.create_block();
    let taken = fb.create_block();
    let skipped = fb.create_block();

    fb.switch_to_block(entry);
    let zero = fb.iconst(Ty::I64, 0);
    let is_zero = fb.icmp(ICmpOp::Eq, Ty::I64, zero, zero);
    fb.condbr(is_zero, skipped, vec![], taken, vec![]);

    fb.switch_to_block(taken);
    let v7 = fb.iconst(Ty::I64, 7);
    fb.ret(vec![v7]);

    fb.switch_to_block(skipped);
    let v9 = fb.iconst(Ty::I64, 9);
    fb.ret(vec![v9]);

    fb.build();
    mb.build()
}

#[test]
fn cli_profile_use_reaches_o2_pass_manager() {
    let dir = scratch_dir("profile_use_reaches_pass");
    let module = make_test_module();
    let tmbc = encode_tmbc(&module).expect("encode tMBC");
    let tmbc_path = dir.join("module.tmbc");
    std::fs::write(&tmbc_path, &tmbc).expect("write tmbc");

    let mut profile = ProfData::new_with_key(&pgo_key(&tmbc, 2));
    let mut function = FunctionProfile::new("_return_42");
    function.call_count = 1;
    function.blocks.push(BlockProfile::new(0, 1));
    profile.functions.push(function);
    let profile_path = dir.join("module.profdata");
    write_to_path(&profile, &profile_path).expect("write profdata");
    let profile_bytes = std::fs::read(&profile_path).expect("read profdata bytes");
    assert_eq!(&profile_bytes[0..8], b"trcg-pgo");
    assert_ne!(profile_bytes[0], b'{');

    let out_path = dir.join("module.o");
    let output = Command::new(trust_cg_bin())
        .env("TRUST_CG_TIME_PASSES", "1")
        .env_remove("TRUST_CG_DISABLE_PASSES")
        .arg("-c")
        .arg("-O2")
        .arg("--profile-use")
        .arg(&profile_path)
        .arg("-o")
        .arg(&out_path)
        .arg(&tmbc_path)
        .output()
        .expect("run trust-cg");

    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "profile-use compile should succeed. stderr:\n{}",
        stderr
    );
    assert!(
        stderr.contains("pass=profile-use"),
        "--profile-use should reach the O2 pass manager. stderr:\n{}",
        stderr
    );
    assert!(
        out_path.exists(),
        "expected object file at {}",
        out_path.display()
    );

    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn cli_profile_use_o1_warns_and_does_not_schedule_profile_use() {
    let dir = scratch_dir("profile_use_o1_warns_no_schedule");
    let module = make_test_module();
    let tmbc = encode_tmbc(&module).expect("encode tMBC");
    let tmbc_path = dir.join("module.tmbc");
    std::fs::write(&tmbc_path, &tmbc).expect("write tmbc");

    let mut profile = ProfData::new_with_key(&pgo_key(&tmbc, 1));
    let mut function = FunctionProfile::new("_return_42");
    function.call_count = 1;
    function.blocks.push(BlockProfile::new(0, 1));
    profile.functions.push(function);
    let profile_path = dir.join("module.profdata");
    write_to_path(&profile, &profile_path).expect("write profdata");

    let out_path = dir.join("module.o");
    let output = Command::new(trust_cg_bin())
        .env("TRUST_CG_TIME_PASSES", "1")
        .env_remove("TRUST_CG_DISABLE_PASSES")
        .arg("-c")
        .arg("-O1")
        .arg("--profile-use")
        .arg(&profile_path)
        .arg("-o")
        .arg(&out_path)
        .arg(&tmbc_path)
        .output()
        .expect("run trust-cg");

    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "O1 profile-use compile should succeed with fresh profdata. stderr:\n{}",
        stderr
    );
    assert!(
        stderr.contains("--profile-use: loaded 1 function(s)"),
        "O1 profile-use should still load and validate the profile. stderr:\n{}",
        stderr
    );
    assert!(
        stderr.contains("--profile-use has no optimization effect below O2"),
        "O1 profile-use should warn that PGO is inactive below O2. stderr:\n{}",
        stderr
    );
    assert!(
        stderr.contains("not scheduling profile-guided optimization at O1"),
        "O1 warning should make the no-schedule behavior explicit. stderr:\n{}",
        stderr
    );
    assert!(
        !stderr.contains("pass=profile-use"),
        "O1 profile-use should not schedule the profile-use pass. stderr:\n{}",
        stderr
    );
    assert!(
        out_path.exists(),
        "expected object file at {}",
        out_path.display()
    );

    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn cli_profile_use_rejects_multiple_inputs() {
    let dir = scratch_dir("profile_use_multiple_inputs");
    let module = make_test_module();
    let tmbc = encode_tmbc(&module).expect("encode tMBC");
    let first_tmbc_path = dir.join("module_first.tmbc");
    std::fs::write(&first_tmbc_path, &tmbc).expect("write first tmbc");
    let second_tmbc_path = dir.join("module_second.tmbc");
    std::fs::write(&second_tmbc_path, &tmbc).expect("write second tmbc");

    let mut profile = ProfData::new_with_key(&pgo_key(&tmbc, 2));
    let mut function = FunctionProfile::new("_return_42");
    function.call_count = 1;
    function.blocks.push(BlockProfile::new(0, 1));
    profile.functions.push(function);
    let profile_path = dir.join("module.profdata");
    write_to_path(&profile, &profile_path).expect("write profdata");

    let output = Command::new(trust_cg_bin())
        .env_remove("TRUST_CG_DISABLE_PASSES")
        .arg("-c")
        .arg("-O2")
        .arg("--profile-use")
        .arg(&profile_path)
        .arg(&first_tmbc_path)
        .arg(&second_tmbc_path)
        .output()
        .expect("run trust-cg");

    assert!(
        !output.status.success(),
        "profile-use with multiple inputs must fail"
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("--profile-use currently requires exactly one input file"),
        "multi-input profile-use error should mention the single-input guard. stderr:\n{}",
        stderr
    );
    assert!(
        !first_tmbc_path.with_extension("o").exists(),
        "multi-input profile-use guard should not compile the first object"
    );
    assert!(
        !second_tmbc_path.with_extension("o").exists(),
        "multi-input profile-use guard should not compile the second object"
    );

    let _ = std::fs::remove_dir_all(&dir);
}

#[cfg(target_arch = "aarch64")]
#[test]
fn cli_profile_generate_canary_dump_reloads_with_profile_use() {
    let dir = scratch_dir("profile_generate_canary_round_trip");
    let module = make_canary_module();
    let tmbc = encode_tmbc(&module).expect("encode canary tMBC");
    let tmbc_path = dir.join("canary.tmbc");
    std::fs::write(&tmbc_path, &tmbc).expect("write canary tmbc");

    let profile_path = dir.join("canary.profdata");
    let generate_obj = dir.join("canary-generate.o");
    let generate = Command::new(trust_cg_bin())
        .env_remove("TRUST_CG_DISABLE_PASSES")
        .arg("-c")
        .arg("-O2")
        .arg("--profile-generate")
        .arg(&profile_path)
        .arg("-o")
        .arg(&generate_obj)
        .arg(&tmbc_path)
        .output()
        .expect("run trust-cg --profile-generate");

    let generate_stderr = String::from_utf8_lossy(&generate.stderr);
    assert!(
        generate.status.success(),
        "profile-generate canary compile/run should succeed. stderr:\n{}",
        generate_stderr
    );
    assert!(
        generate_stderr.contains("--profile-generate: ran 10 call(s) through 'pgo_canary'"),
        "--profile-generate should report the JIT canary run. stderr:\n{}",
        generate_stderr
    );
    assert!(
        generate_obj.exists(),
        "expected generated object at {}",
        generate_obj.display()
    );

    let loaded = trust_cg_opt::pgo::read_from_path(&profile_path).expect("reload runtime profdata");
    assert_eq!(loaded.module_hash_u128(), Some(stable_hash(&tmbc)));
    assert_eq!(
        loaded.profile_key_digest_u128(),
        Some(pgo_key(&tmbc, 2).digest())
    );

    let fp = loaded
        .function("pgo_canary")
        .expect("canary function profile");
    const N: u64 = 10;
    assert_eq!(fp.call_count, N);
    assert_eq!(fp.block_hits(0), N, "entry block should be hot");
    assert_eq!(fp.block_hits(1), 3, "zero branch should be colder");
    assert_eq!(fp.block_hits(2), 7, "non-zero branch should be hotter");

    let pass = trust_cg_opt::pgo::ProfileUsePass::new(loaded.clone());
    let mach_func = MachFunction::new(
        "pgo_canary".to_string(),
        Signature::new(vec![Type::I64], vec![Type::I64]),
    );
    let pass_profile = pass
        .function_profile(&mach_func)
        .expect("profile-use pass sees canary profile");
    assert_eq!(pass_profile.block_hits(1), 3);
    assert_eq!(pass_profile.block_hits(2), 7);

    let out_path = dir.join("canary.o");
    let output = Command::new(trust_cg_bin())
        .env("TRUST_CG_TIME_PASSES", "1")
        .env_remove("TRUST_CG_DISABLE_PASSES")
        .arg("-c")
        .arg("-O2")
        .arg("--profile-use")
        .arg(&profile_path)
        .arg("-o")
        .arg(&out_path)
        .arg(&tmbc_path)
        .output()
        .expect("run trust-cg");

    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "profile-use canary compile should succeed. stderr:\n{}",
        stderr
    );
    assert!(
        stderr.contains("pass=profile-use"),
        "--profile-use should reload canary profdata into the O2 pass manager. stderr:\n{}",
        stderr
    );
    assert!(out_path.exists(), "expected {}", out_path.display());

    let _ = std::fs::remove_dir_all(&dir);
}

#[cfg(target_arch = "aarch64")]
#[test]
fn cli_profile_generate_ty_parent_loop_dump_reloads_with_profile_use() {
    let dir = scratch_dir("profile_generate_ty_parent_loop");
    let module = make_ty_parent_loop_module();
    let tmbc = encode_tmbc(&module).expect("encode TY parent-loop tMBC");
    let tmbc_path = dir.join("ty-parent-loop.tmbc");
    std::fs::write(&tmbc_path, &tmbc).expect("write TY parent-loop tmbc");

    let profile_path = dir.join("ty-parent-loop.profdata");
    let generate_obj = dir.join("ty-parent-loop-generate.o");
    let mut generate_cmd = Command::new(trust_cg_bin());
    generate_cmd
        .env_remove("TRUST_CG_DISABLE_PASSES")
        .arg("-c")
        .arg("-O3")
        .arg("--profile-generate")
        .arg(&profile_path)
        .arg("-o")
        .arg(&generate_obj)
        .arg(&tmbc_path);
    let generate =
        command_output_with_timeout(generate_cmd, TY_PARENT_LOOP_PROFILE_GENERATE_TIMEOUT)
            .expect("run trust-cg --profile-generate for TY parent loop");

    let generate_stderr = String::from_utf8_lossy(&generate.stderr);
    assert!(
        generate.status.success(),
        "TY parent-loop profile-generate should succeed. stderr:\n{}",
        generate_stderr
    );
    assert!(
        generate_stderr.contains(&format!(
            "--profile-generate: ran 1 call(s) through '{}'",
            TY_PARENT_LOOP_ENTRY
        )),
        "--profile-generate should report the TY parent-loop JIT run. stderr:\n{}",
        generate_stderr
    );
    let generate_reports = profile_reports(&generate_stderr);
    assert_eq!(
        generate_reports.len(),
        1,
        "profile-generate should emit one structured profile report. stderr:\n{}",
        generate_stderr
    );
    let generate_report = &generate_reports[0];
    assert_eq!(generate_report["schema"], "trust-cg.profile_report.v1");
    assert_eq!(generate_report["mode"], "profile-generate");
    assert_eq!(
        generate_report["capture"]["kind"], "host-jit-canary",
        "report should identify the bounded CLI JIT canary path"
    );
    assert_eq!(
        generate_report["capture"]["entry"], TY_PARENT_LOOP_ENTRY,
        "report should name the selected TY entry"
    );
    assert_eq!(
        generate_report["capture"]["entry_shape"],
        "ty_parent_loop_u64_return"
    );
    assert_eq!(generate_report["capture"]["call_count"], 1);
    assert_eq!(
        generate_report["capture"]["inputs"],
        serde_json::json!(TY_PARENT_INPUTS)
    );
    assert_eq!(
        generate_report["capture"]["window"]["count"],
        TY_PARENT_INPUTS.len()
    );
    assert_eq!(
        generate_report["profile"]["path"],
        profile_path.display().to_string()
    );
    assert_eq!(
        generate_report["profile"]["sha256"]
            .as_str()
            .expect("profile report sha256"),
        format!(
            "sha256:{}",
            trust_cg_codegen::jit_diagnostics::sha256_hex(
                &std::fs::read(&profile_path).expect("read profile bytes")
            )
        )
    );
    assert!(
        generate_obj.exists(),
        "expected generated object at {}",
        generate_obj.display()
    );

    let loaded = trust_cg_opt::pgo::read_from_path(&profile_path)
        .expect("reload TY parent-loop runtime profdata");
    let expected_key = pgo_key(&tmbc, 3);
    trust_cg_opt::pgo::enforce_fresh(&loaded, &expected_key)
        .expect("O3 TY parent-loop profile should be fresh");
    assert_eq!(loaded.module_hash_u128(), Some(stable_hash(&tmbc)));
    assert_eq!(
        loaded.profile_key_digest_u128(),
        Some(expected_key.digest())
    );
    assert_eq!(
        generate_report["profile_key"]["module_hash"],
        format!("{:032x}", stable_hash(&tmbc))
    );
    assert_eq!(
        generate_report["profile_key"]["profile_key_digest"],
        expected_key.hex()
    );
    assert_eq!(
        generate_report["profile_key"]["target_triple"],
        expected_key.target_triple()
    );
    assert_eq!(
        generate_report["profile_key"]["target_cpu"],
        expected_key.cpu()
    );
    assert_eq!(
        generate_report["profile_key"]["target_features"],
        serde_json::json!(expected_key.features())
    );
    assert_eq!(generate_report["profile_key"]["opt_level"], "O3");

    let fp = loaded
        .function(TY_PARENT_LOOP_ENTRY)
        .expect("TY parent-loop function profile");
    assert_ty_parent_loop_o3_profile(fp, TY_PARENT_INPUTS.len());

    assert_eq!(generate_report["counters"]["function_count"], 1);
    assert_eq!(generate_report["counters"]["block_count"], fp.blocks.len());
    assert_eq!(
        generate_report["counters"]["total_call_count"],
        fp.call_count
    );
    assert_eq!(
        generate_report["counters"]["total_block_hits"],
        fp.blocks.iter().map(|block| block.hits).sum::<u64>()
    );
    assert_eq!(generate_report["profile_use"]["fresh"], true);
    assert_eq!(generate_report["profile_use"]["scheduled"], false);

    let out_path = dir.join("ty-parent-loop.o");
    let mut profile_use_cmd = Command::new(trust_cg_bin());
    profile_use_cmd
        .env("TRUST_CG_TIME_PASSES", "1")
        .env_remove("TRUST_CG_DISABLE_PASSES")
        .arg("-c")
        .arg("-O3")
        .arg("--profile-use")
        .arg(&profile_path)
        .arg("-o")
        .arg(&out_path)
        .arg(&tmbc_path);
    let output =
        command_output_with_timeout(profile_use_cmd, TY_PARENT_LOOP_PROFILE_GENERATE_TIMEOUT)
            .expect("run trust-cg --profile-use for TY parent loop");

    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "TY parent-loop profile-use compile should succeed. stderr:\n{}",
        stderr
    );
    assert!(
        stderr.contains("pass=profile-use"),
        "--profile-use should reload TY parent-loop profdata into O3. stderr:\n{}",
        stderr
    );
    let use_reports = profile_reports(&stderr);
    assert_eq!(
        use_reports.len(),
        1,
        "profile-use should emit one structured profile report. stderr:\n{}",
        stderr
    );
    let use_report = &use_reports[0];
    assert_eq!(use_report["schema"], "trust-cg.profile_report.v1");
    assert_eq!(use_report["mode"], "profile-use");
    assert_eq!(use_report["profile_key"], generate_report["profile_key"]);
    assert_eq!(use_report["profile"], generate_report["profile"]);
    assert_eq!(use_report["counters"], generate_report["counters"]);
    assert_eq!(use_report["profile_use"]["fresh"], true);
    assert_eq!(
        use_report["profile_use"]["consumer"],
        "optimization-pipeline"
    );
    assert_eq!(use_report["profile_use"]["scheduled"], true);
    assert_eq!(use_report["profile_use"]["pass"], "profile-use");
    assert_eq!(
        use_report["profile_use"]["reason"],
        "opt-level-enables-profile-use"
    );
    assert_eq!(
        use_report["profile_use"]["summary"]["profiled_blocks"],
        fp.blocks.len()
    );
    assert_eq!(use_report["profile_use"]["summary"]["hot_functions"], 1);
    let expected_effective_function_count = fp
        .call_count
        .max(fp.blocks.iter().map(|block| block.hits).max().unwrap_or(0));
    assert_eq!(
        use_report["profile_use"]["summary"]["total_function_count"],
        expected_effective_function_count
    );
    assert!(out_path.exists(), "expected {}", out_path.display());

    let _ = std::fs::remove_dir_all(&dir);
}

#[cfg(target_arch = "aarch64")]
#[test]
fn cli_profile_generate_ty_parent_loop_uses_supplied_inputs() {
    let dir = scratch_dir("profile_generate_ty_parent_loop_supplied_inputs");
    let module = make_ty_parent_loop_module();
    let tmbc = encode_tmbc(&module).expect("encode TY parent-loop tMBC");
    let tmbc_path = dir.join("ty-parent-loop-custom-inputs.tmbc");
    std::fs::write(&tmbc_path, &tmbc).expect("write TY parent-loop tmbc");

    let supplied_inputs = [11_u64, 23, 37, 41];
    assert_ne!(
        supplied_inputs.len(),
        TY_PARENT_INPUTS.len(),
        "regression needs a non-default parent vector length"
    );
    let supplied_csv = supplied_inputs
        .iter()
        .map(u64::to_string)
        .collect::<Vec<_>>()
        .join(",");

    let profile_path = dir.join("ty-parent-loop-custom-inputs.profdata");
    let generate_obj = dir.join("ty-parent-loop-custom-inputs-generate.o");
    let mut generate_cmd = Command::new(trust_cg_bin());
    generate_cmd
        .env_remove("TRUST_CG_DISABLE_PASSES")
        .arg("-c")
        .arg("-O3")
        .arg("--profile-generate")
        .arg(&profile_path)
        .arg("--profile-generate-inputs")
        .arg(&supplied_csv)
        .arg("-o")
        .arg(&generate_obj)
        .arg(&tmbc_path);
    let generate =
        command_output_with_timeout(generate_cmd, TY_PARENT_LOOP_PROFILE_GENERATE_TIMEOUT)
            .expect("run trust-cg --profile-generate with supplied TY inputs");

    let generate_stderr = String::from_utf8_lossy(&generate.stderr);
    assert!(
        generate.status.success(),
        "TY parent-loop profile-generate with supplied inputs should succeed. stderr:\n{}",
        generate_stderr
    );
    assert!(
        generate_stderr.contains(&format!(
            "--profile-generate: ran 1 call(s) through '{}'",
            TY_PARENT_LOOP_ENTRY
        )),
        "--profile-generate should report the TY parent-loop JIT run. stderr:\n{}",
        generate_stderr
    );
    assert!(
        generate_obj.exists(),
        "expected generated object at {}",
        generate_obj.display()
    );

    let loaded = trust_cg_opt::pgo::read_from_path(&profile_path)
        .expect("reload TY parent-loop runtime profdata");
    let expected_key = pgo_key(&tmbc, 3);
    trust_cg_opt::pgo::enforce_fresh(&loaded, &expected_key)
        .expect("O3 TY parent-loop profile should be fresh");
    assert_eq!(loaded.module_hash_u128(), Some(stable_hash(&tmbc)));
    assert_eq!(
        loaded.profile_key_digest_u128(),
        Some(expected_key.digest())
    );

    let fp = loaded
        .function(TY_PARENT_LOOP_ENTRY)
        .expect("TY parent-loop function profile");
    assert_ty_parent_loop_o3_profile(fp, supplied_inputs.len());

    let out_path = dir.join("ty-parent-loop-custom-inputs.o");
    let mut profile_use_cmd = Command::new(trust_cg_bin());
    profile_use_cmd
        .env("TRUST_CG_TIME_PASSES", "1")
        .env_remove("TRUST_CG_DISABLE_PASSES")
        .arg("-c")
        .arg("-O3")
        .arg("--profile-use")
        .arg(&profile_path)
        .arg("-o")
        .arg(&out_path)
        .arg(&tmbc_path);
    let output =
        command_output_with_timeout(profile_use_cmd, TY_PARENT_LOOP_PROFILE_GENERATE_TIMEOUT)
            .expect("run trust-cg --profile-use for supplied TY inputs");

    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "TY parent-loop profile-use compile should succeed. stderr:\n{}",
        stderr
    );
    assert!(
        stderr.contains("pass=profile-use"),
        "--profile-use should reload supplied-input TY profdata into O3. stderr:\n{}",
        stderr
    );
    assert!(out_path.exists(), "expected {}", out_path.display());

    let _ = std::fs::remove_dir_all(&dir);
}

#[cfg(target_arch = "aarch64")]
#[test]
fn cli_profile_use_rejects_ty_parent_loop_opt_level_mismatch() {
    let dir = scratch_dir("profile_use_ty_parent_loop_opt_level_mismatch");
    let module = make_ty_parent_loop_module();
    let tmbc = encode_tmbc(&module).expect("encode TY parent-loop tMBC");
    let tmbc_path = dir.join("ty-parent-loop-opt-mismatch.tmbc");
    std::fs::write(&tmbc_path, &tmbc).expect("write TY parent-loop tmbc");

    let profile_path = dir.join("ty-parent-loop-o3.profdata");
    write_ty_parent_loop_o3_profile(&profile_path, &tmbc, TY_PARENT_INPUTS.len());
    let loaded = trust_cg_opt::pgo::read_from_path(&profile_path)
        .expect("reload synthetic O3 TY parent-loop profdata");
    trust_cg_opt::pgo::enforce_fresh(&loaded, &pgo_key(&tmbc, 3))
        .expect("synthetic O3 TY parent-loop profile should be fresh for O3");

    let stale_obj = dir.join("ty-parent-loop-o2-use.o");
    let stale = Command::new(trust_cg_bin())
        .env_remove("TRUST_CG_DISABLE_PASSES")
        .arg("-c")
        .arg("-O2")
        .arg("--profile-use")
        .arg(&profile_path)
        .arg("-o")
        .arg(&stale_obj)
        .arg(&tmbc_path)
        .output()
        .expect("run trust-cg --profile-use at O2 with O3 TY profile");

    assert!(
        !stale.status.success(),
        "O2 profile-use must reject O3 TY parent-loop profdata"
    );
    let stale_stderr = String::from_utf8_lossy(&stale.stderr);
    assert!(
        stale_stderr.contains("profdata profile key stale")
            && stale_stderr.contains("reason=opt-level mismatch"),
        "stale profile error should mention the opt-level mismatch. stderr:\n{}",
        stale_stderr
    );
    assert!(
        !stale_obj.exists(),
        "stale profile should not produce an object"
    );

    let _ = std::fs::remove_dir_all(&dir);
}

#[cfg(target_arch = "aarch64")]
#[test]
fn cli_profile_use_rejects_ty_parent_loop_target_triple_mismatch() {
    let dir = scratch_dir("profile_use_ty_parent_loop_target_triple_mismatch");
    let module = make_ty_parent_loop_module();
    let tmbc = encode_tmbc(&module).expect("encode TY parent-loop tMBC");
    let tmbc_path = dir.join("ty-parent-loop-target-mismatch.tmbc");
    std::fs::write(&tmbc_path, &tmbc).expect("write TY parent-loop tmbc");

    let profile_path = dir.join("ty-parent-loop-aarch64-default.profdata");
    write_ty_parent_loop_o3_profile(&profile_path, &tmbc, TY_PARENT_INPUTS.len());
    let loaded = trust_cg_opt::pgo::read_from_path(&profile_path)
        .expect("reload synthetic default-target TY parent-loop profdata");
    trust_cg_opt::pgo::enforce_fresh(&loaded, &pgo_key(&tmbc, 3))
        .expect("synthetic TY parent-loop profile should be fresh for default AArch64 O3");

    // The synthetic profile carries the CLI's default (host-resolved) AArch64
    // triple. Compile for an explicitly *different* triple so the freshness gate
    // rejects it. Post-merge the architecture-only default resolves to the HOST
    // triple, so the mismatch target must be a non-host OS/ABI at the same
    // architecture — and which one that is depends on the host. Picking it
    // statically only worked on macOS: on an aarch64 Linux host the former
    // hard-coded `aarch64-unknown-linux-gnu` *is* the default, so the assertion
    // below fired and the test failed for environmental reasons.
    let default_triple = default_aarch64_triple();
    let mismatch_triple = if default_triple == "aarch64-unknown-linux-gnu" {
        "aarch64-apple-darwin"
    } else {
        "aarch64-unknown-linux-gnu"
    };
    assert_ne!(
        mismatch_triple, default_triple,
        "target-triple mismatch test needs a triple distinct from the host default"
    );

    let stale_obj = dir.join("ty-parent-loop-explicit-target-use.o");
    let stale = Command::new(trust_cg_bin())
        .env_remove("TRUST_CG_DISABLE_PASSES")
        .arg("-c")
        .arg("-O3")
        .arg("--target")
        .arg(mismatch_triple)
        .arg("--profile-use")
        .arg(&profile_path)
        .arg("-o")
        .arg(&stale_obj)
        .arg(&tmbc_path)
        .output()
        .expect("run trust-cg --profile-use with mismatched explicit target triple");

    assert!(
        !stale.status.success(),
        "explicit-target profile-use must reject default-target TY parent-loop profdata"
    );
    let stale_stderr = String::from_utf8_lossy(&stale.stderr);
    assert!(
        stale_stderr.contains("profdata profile key stale")
            && stale_stderr.contains("reason=target triple mismatch"),
        "stale profile error should mention the target-triple mismatch. stderr:\n{}",
        stale_stderr
    );
    assert!(
        !stale_obj.exists(),
        "stale profile should not produce an object"
    );

    let _ = std::fs::remove_dir_all(&dir);
}

#[cfg(target_arch = "aarch64")]
#[test]
fn cli_profile_use_rejects_ty_parent_loop_target_cpu_mismatch() {
    let dir = scratch_dir("profile_use_ty_parent_loop_target_cpu_mismatch");
    let module = make_ty_parent_loop_module();
    let tmbc = encode_tmbc(&module).expect("encode TY parent-loop tMBC");
    let tmbc_path = dir.join("ty-parent-loop-cpu-mismatch.tmbc");
    std::fs::write(&tmbc_path, &tmbc).expect("write TY parent-loop tmbc");

    let profile_path = dir.join("ty-parent-loop-generic-aarch64.profdata");
    write_ty_parent_loop_o3_profile(&profile_path, &tmbc, TY_PARENT_INPUTS.len());
    let mut loaded = trust_cg_opt::pgo::read_from_path(&profile_path)
        .expect("reload synthetic generic-AArch64 TY parent-loop profdata");
    let default_key = pgo_key(&tmbc, 3);
    assert_eq!(default_key.cpu(), "generic-aarch64");
    trust_cg_opt::pgo::enforce_fresh(&loaded, &default_key)
        .expect("synthetic TY parent-loop profile should be fresh for generic AArch64 O3");

    let cpu_mismatch_key = CacheKey::new(
        default_key.module_hash(),
        default_key.opt_level(),
        default_key.target_triple().to_string(),
        "apple-m2".to_string(),
        default_key.features().to_vec(),
    );
    assert_eq!(cpu_mismatch_key.module_hash(), default_key.module_hash());
    assert_eq!(cpu_mismatch_key.opt_level(), default_key.opt_level());
    assert_eq!(
        cpu_mismatch_key.target_triple(),
        default_key.target_triple()
    );
    assert_ne!(cpu_mismatch_key.cpu(), default_key.cpu());
    assert_eq!(cpu_mismatch_key.features(), default_key.features());

    loaded.set_profile_key(&cpu_mismatch_key);
    let stale_profile_path = dir.join("ty-parent-loop-cpu-mismatch.profdata");
    write_to_path(&loaded, &stale_profile_path)
        .expect("write CPU-mismatched TY parent-loop profdata");

    let stale_obj = dir.join("ty-parent-loop-cpu-mismatch-use.o");
    let stale = Command::new(trust_cg_bin())
        .env_remove("TRUST_CG_DISABLE_PASSES")
        .arg("-c")
        .arg("-O3")
        .arg("--profile-use")
        .arg(&stale_profile_path)
        .arg("-o")
        .arg(&stale_obj)
        .arg(&tmbc_path)
        .output()
        .expect("run trust-cg --profile-use with mismatched target CPU");

    assert!(
        !stale.status.success(),
        "CPU-mismatched profile-use must reject TY parent-loop profdata"
    );
    let stale_stderr = String::from_utf8_lossy(&stale.stderr);
    assert!(
        stale_stderr.contains("profdata profile key stale")
            && stale_stderr.contains("reason=target CPU mismatch"),
        "stale profile error should mention the target-CPU mismatch. stderr:\n{}",
        stale_stderr
    );
    assert!(
        !stale_obj.exists(),
        "stale profile should not produce an object"
    );

    let _ = std::fs::remove_dir_all(&dir);
}

#[cfg(target_arch = "aarch64")]
#[test]
fn cli_profile_use_rejects_ty_parent_loop_target_feature_mismatch() {
    let dir = scratch_dir("profile_use_ty_parent_loop_target_feature_mismatch");
    let module = make_ty_parent_loop_module();
    let tmbc = encode_tmbc(&module).expect("encode TY parent-loop tMBC");
    let tmbc_path = dir.join("ty-parent-loop-feature-mismatch.tmbc");
    std::fs::write(&tmbc_path, &tmbc).expect("write TY parent-loop tmbc");

    let profile_path = dir.join("ty-parent-loop-default-features.profdata");
    write_ty_parent_loop_o3_profile(&profile_path, &tmbc, TY_PARENT_INPUTS.len());
    let mut loaded = trust_cg_opt::pgo::read_from_path(&profile_path)
        .expect("reload synthetic default-feature TY parent-loop profdata");
    let default_key = pgo_key(&tmbc, 3);
    trust_cg_opt::pgo::enforce_fresh(&loaded, &default_key)
        .expect("synthetic TY parent-loop profile should be fresh for default features");

    let feature_mismatch_key = CacheKey::new(
        default_key.module_hash(),
        default_key.opt_level(),
        default_key.target_triple().to_string(),
        default_key.cpu().to_string(),
        vec!["+fp16".to_string(), "+neon".to_string()],
    );
    assert_eq!(
        feature_mismatch_key.module_hash(),
        default_key.module_hash()
    );
    assert_eq!(feature_mismatch_key.opt_level(), default_key.opt_level());
    assert_eq!(
        feature_mismatch_key.target_triple(),
        default_key.target_triple()
    );
    assert_eq!(feature_mismatch_key.cpu(), default_key.cpu());
    assert_ne!(feature_mismatch_key.features(), default_key.features());

    loaded.set_profile_key(&feature_mismatch_key);
    let stale_profile_path = dir.join("ty-parent-loop-feature-mismatch.profdata");
    write_to_path(&loaded, &stale_profile_path)
        .expect("write feature-mismatched TY parent-loop profdata");

    let stale_obj = dir.join("ty-parent-loop-feature-mismatch-use.o");
    let stale = Command::new(trust_cg_bin())
        .env_remove("TRUST_CG_DISABLE_PASSES")
        .arg("-c")
        .arg("-O3")
        .arg("--profile-use")
        .arg(&stale_profile_path)
        .arg("-o")
        .arg(&stale_obj)
        .arg(&tmbc_path)
        .output()
        .expect("run trust-cg --profile-use with mismatched target features");

    assert!(
        !stale.status.success(),
        "feature-mismatched profile-use must reject TY parent-loop profdata"
    );
    let stale_stderr = String::from_utf8_lossy(&stale.stderr);
    assert!(
        stale_stderr.contains("profdata profile key stale")
            && stale_stderr.contains("reason=target feature mismatch"),
        "stale profile error should mention the target-feature mismatch. stderr:\n{}",
        stale_stderr
    );
    assert!(
        !stale_obj.exists(),
        "stale profile should not produce an object"
    );

    let _ = std::fs::remove_dir_all(&dir);
}

#[cfg(target_arch = "x86_64")]
#[test]
fn cli_profile_generate_x86_writes_branch_block_counts() {
    let dir = scratch_dir("profile_generate_x86_writes_branch_block_counts");
    let module = make_x86_constant_conditional_module();
    let tmbc = encode_tmbc(&module).expect("encode x86 conditional tMBC");
    let tmbc_path = dir.join("module.tmbc");
    std::fs::write(&tmbc_path, &tmbc).expect("write tmbc");

    let profile_path = dir.join("module.profdata");
    let out_path = dir.join("module.o");
    let output = Command::new(trust_cg_bin())
        .env_remove("TRUST_CG_DISABLE_PASSES")
        .arg("-c")
        .arg("--target")
        .arg("x86_64")
        .arg("--profile-generate")
        .arg(&profile_path)
        .arg("-o")
        .arg(&out_path)
        .arg(&tmbc_path)
        .output()
        .expect("run trust-cg --profile-generate --target x86_64");

    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "x86 profile-generate BlockCounts should succeed. stderr:\n{}",
        stderr
    );
    assert!(
        stderr.contains("--profile-generate: ran 1 call(s) through 'pgo_x86_selective'"),
        "profile-generate should report the x86 JIT canary run. stderr:\n{}",
        stderr
    );
    let reports = profile_reports(&stderr);
    assert_eq!(
        reports.len(),
        1,
        "profile-generate should emit one structured profile report. stderr:\n{}",
        stderr
    );
    assert_eq!(
        reports[0]["capture"]["return_value"], 9,
        "constant-true branch should return the true-target value. stderr:\n{}",
        stderr
    );
    assert!(out_path.exists(), "expected {}", out_path.display());

    let loaded = trust_cg_opt::pgo::read_from_path(&profile_path).expect("reload x86 profdata");
    let function = loaded
        .function("pgo_x86_selective")
        .expect("x86 generated profile should contain function");
    assert_eq!(function.call_count, 1);
    let mut hits: Vec<u64> = function.blocks.iter().map(|block| block.hits).collect();
    hits.sort_unstable();
    assert_eq!(
        hits,
        vec![0, 1, 1],
        "x86 profile-generate should capture multiple conditional block counts: {:?}",
        function.blocks
    );
    let mut nonzero_blocks: Vec<u32> = function
        .blocks
        .iter()
        .filter_map(|block| (block.hits == 1).then_some(block.block_id))
        .collect();
    nonzero_blocks.sort_unstable();
    // x86 BlockCounts reports lowered LIR block IDs. The adapter assigns the
    // constant-true target first when translating the condbr edge, so the hot
    // true target is LIR block 1 even though its source trust_ir block was created
    // after the cold target.
    assert_eq!(
        nonzero_blocks,
        vec![0, 1],
        "entry and the constant-true target should be hot"
    );

    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn cli_profile_use_o1_still_rejects_stale_module_hash() {
    let dir = scratch_dir("profile_use_o1_stale");
    let (tmbc_path, profile_path) =
        write_module_and_profile_for_opt_level(&dir, stable_hash(b"different"), 1);
    let out_path = dir.join("module.o");

    let output = Command::new(trust_cg_bin())
        .env("TRUST_CG_TIME_PASSES", "1")
        .env_remove("TRUST_CG_DISABLE_PASSES")
        .arg("-c")
        .arg("-O1")
        .arg("--profile-use")
        .arg(&profile_path)
        .arg("-o")
        .arg(&out_path)
        .arg(&tmbc_path)
        .output()
        .expect("run trust-cg");

    assert!(
        !output.status.success(),
        "stale O1 profile-use input must fail"
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("--profile-use has no optimization effect below O2"),
        "O1 stale profile-use should still emit the below-O2 warning. stderr:\n{}",
        stderr
    );
    assert!(
        stderr.contains("profdata profile key stale")
            && stderr.contains("reason=module hash mismatch"),
        "stale O1 profile error should mention the hash mismatch. stderr:\n{}",
        stderr
    );
    assert!(
        !stderr.contains("pass=profile-use"),
        "stale O1 profile-use should not schedule the profile-use pass. stderr:\n{}",
        stderr
    );
    assert!(
        !out_path.exists(),
        "stale O1 profile should not produce an object"
    );

    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn cli_profile_use_rejects_stale_module_hash() {
    let dir = scratch_dir("profile_use_stale");
    let (tmbc_path, profile_path) = write_module_and_profile(&dir, stable_hash(b"different"));
    let out_path = dir.join("module.o");

    let output = Command::new(trust_cg_bin())
        .env_remove("TRUST_CG_DISABLE_PASSES")
        .arg("-c")
        .arg("-O2")
        .arg("--profile-use")
        .arg(&profile_path)
        .arg("-o")
        .arg(&out_path)
        .arg(&tmbc_path)
        .output()
        .expect("run trust-cg");

    assert!(
        !output.status.success(),
        "stale profile-use input must fail"
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("profdata profile key stale")
            && stderr.contains("reason=module hash mismatch"),
        "stale profile error should mention the hash mismatch. stderr:\n{}",
        stderr
    );
    assert!(
        !out_path.exists(),
        "stale profile should not produce an object"
    );

    let _ = std::fs::remove_dir_all(&dir);
}
