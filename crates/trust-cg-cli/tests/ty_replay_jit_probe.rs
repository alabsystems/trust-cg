// trust-cg-cli/tests/ty_replay_jit_probe.rs - TY replay JIT probe tests
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

#![cfg(target_arch = "aarch64")]

use std::fs::File;
use std::io;
use std::path::{Path, PathBuf};
use std::process::{Command, ExitStatus, Stdio};
use std::thread;
use std::time::{Duration, Instant};

use trust_ir::{BinOp, ICmpOp, Module as TrustIrModule, Ty, ValueId};
use trust_ir_build::{FunctionBuilder, ModuleBuilder};

const TY_PARENT_LOOP_ENTRY: &str = "ty_cli_parent_loop";
const TY_PARENT_INPUTS: &[u64] = &[2, 5, 8, 13, 21, 34];
const PROBE_TIMEOUT: Duration = Duration::from_secs(90);
const CHILD_POLL_INTERVAL: Duration = Duration::from_millis(25);

struct TimedOutput {
    status: ExitStatus,
    stdout: Vec<u8>,
    stderr: Vec<u8>,
    timed_out: bool,
}

/// Run a child with a platform-independent wall-clock bound.
///
/// `std::process::Child::kill` maps to the native force-termination mechanism
/// on both Unix and Windows. Output goes through regular files rather than
/// pipes so a verbose child cannot fill a pipe and deadlock before the timeout
/// loop gets a chance to reap it.
fn output_with_timeout(
    command: &mut Command,
    output_dir: &Path,
    timeout: Duration,
) -> io::Result<TimedOutput> {
    let stdout_path = output_dir.join("probe.stdout");
    let stderr_path = output_dir.join("probe.stderr");
    command
        .stdout(Stdio::from(File::create(&stdout_path)?))
        .stderr(Stdio::from(File::create(&stderr_path)?));

    let mut child = command.spawn()?;
    let started = Instant::now();
    loop {
        if let Some(status) = child.try_wait()? {
            return Ok(TimedOutput {
                status,
                stdout: std::fs::read(&stdout_path)?,
                stderr: std::fs::read(&stderr_path)?,
                timed_out: false,
            });
        }

        if started.elapsed() >= timeout {
            // Check once more before killing to close the race with a child
            // that exited between the first try_wait and the deadline check.
            let status = if let Some(status) = child.try_wait()? {
                status
            } else {
                match child.kill() {
                    Ok(()) => child.wait()?,
                    Err(kill_error) => match child.try_wait()? {
                        Some(status) => status,
                        None => return Err(kill_error),
                    },
                }
            };
            return Ok(TimedOutput {
                status,
                stdout: std::fs::read(&stdout_path)?,
                stderr: std::fs::read(&stderr_path)?,
                timed_out: true,
            });
        }

        thread::sleep(CHILD_POLL_INTERVAL);
    }
}

fn scratch_dir(test_name: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!(
        "trust_cg_cli_ty_replay_{}_{}",
        test_name,
        std::process::id()
    ));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create scratch dir");
    dir
}

fn ty_replay_jit_probe_bin() -> PathBuf {
    PathBuf::from(env!("CARGO_BIN_EXE_ty_replay_jit_probe"))
}

fn write_module_json(dir: &Path, module: &TrustIrModule) -> PathBuf {
    let path = dir.join("000001-compile_module_native.linked-Request__1_1.trust_ir.json");
    let bytes = serde_json::to_vec_pretty(module).expect("serialize trust_ir module");
    std::fs::write(&path, bytes).expect("write trust_ir JSON");
    path
}

fn store_ty_summary_slot(fb: &mut FunctionBuilder<'_>, out: ValueId, slot: u64, value: ValueId) {
    let slot = fb.iconst(Ty::U64, i128::from(slot));
    let ptr = fb.gep(Ty::U64, out, vec![slot]);
    fb.store(Ty::U64, ptr, value);
}

fn make_ty_parent_loop_module() -> TrustIrModule {
    const FINGERPRINT_SEED: u64 = 0x6d2b_79f5_aa17_6620;
    const PARENT_DIGEST_SEED: u64 = 0x9e37_79b9_6620_0001;
    const IDX_PRIME: u64 = 0x0000_0000_85eb_ca6b;
    const GENERATED_PRIME: u64 = 0x0000_0100_0000_01b3;
    const PARENT_DIGEST_PRIME: u64 = 0x0000_0000_c2b2_ae35;
    const FINGERPRINT_PARENT_PRIME: u64 = 0xff51_afd7_ed55_8ccd;
    const FINGERPRINT_PRIME: u64 = 0x0000_0001_65b1_e9dd;

    let mut mb = ModuleBuilder::new("cli_ty_parent_loop_probe_test");
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

#[test]
fn ty_replay_jit_probe_invokes_parent_loop_abi() {
    let dir = scratch_dir("parent_loop_abi");
    let module_path = write_module_json(&dir, &make_ty_parent_loop_module());

    let mut command = Command::new(ty_replay_jit_probe_bin());
    command
        .arg("--trust_ir-json")
        .arg(&module_path)
        .arg("--symbol")
        .arg(TY_PARENT_LOOP_ENTRY)
        .arg("-O3")
        .arg("--invoke-ty-parent-loop")
        .arg("--parent-inputs")
        .arg(
            TY_PARENT_INPUTS
                .iter()
                .map(u64::to_string)
                .collect::<Vec<_>>()
                .join(","),
        );
    let output = output_with_timeout(&mut command, &dir, PROBE_TIMEOUT)
        .expect("run ty_replay_jit_probe with timeout");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        !output.timed_out,
        "ty_replay_jit_probe timed out after {PROBE_TIMEOUT:?}. stdout:\n{}\nstderr:\n{}",
        stdout, stderr
    );
    assert!(
        output.status.success(),
        "ty_replay_jit_probe should compile and invoke TY replay. stdout:\n{}\nstderr:\n{}",
        stdout,
        stderr
    );

    let report: serde_json::Value = serde_json::from_str(&stdout).expect("parse probe JSON");
    assert_eq!(report["symbol"], TY_PARENT_LOOP_ENTRY);
    assert_eq!(report["public_matches_proof"], true);
    assert_eq!(report["exact_symbol_match"], true);
    assert!(
        report["function_count"].as_u64().unwrap_or_default() >= 1,
        "probe should report compiled functions: {report}"
    );

    let invocation = &report["invocation"];
    assert_eq!(invocation["shape"], "ty_parent_loop_u64_return");
    assert_eq!(invocation["return_value"], 0);
    assert_eq!(invocation["parent_count"], TY_PARENT_INPUTS.len() as u64);
    assert_eq!(invocation["generated_count"], TY_PARENT_INPUTS.len() as u64);
    assert_eq!(invocation["status"], 0);

    let summary = invocation["summary"].as_array().expect("summary array");
    assert_eq!(summary.len(), 5);
    assert_eq!(summary[0], TY_PARENT_INPUTS.len() as u64);
    assert_eq!(summary[1], TY_PARENT_INPUTS.len() as u64);
    assert_eq!(summary[4], 0);

    let _ = std::fs::remove_dir_all(&dir);
}
