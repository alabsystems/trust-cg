// tier_up_bench.rs - JIT tier-up on non-TY programs: exact answers, cost, latency.
//
// Runs one workload (the ay watched-literal BCP kernel over a DIMACS formula,
// or one of this repository's scripts/fuzz kernels) through
// `trust_cg_codegen::tier_up` in one of three arms:
//
//   base   one tier at the base level (O0 by default): cheapest compile.
//   top    one tier at the top level (O2 by default): the best code, paid up
//          front.
//   tier   base now, top in the background after it; calls go through a
//          `TierEntryTable` and switch to the top tier the first time a
//          non-blocking poll between calls sees it delivered.
//   tierc  the same, but the top tier starts compiling BEFORE the base tier
//          (`TierUpSession::start_concurrent`), on another thread.
//
// Every arm compiles through the SAME `TierUpSession` + `ServiceTierBackend`
// route (a one-tier plan is an ordinary compile-service compile, byte for
// byte), and every call's result is folded into one FNV-1a checksum, which
// must be identical in all three arms: the tiers are exact.
//
// Printed (JSON): the checksum; wall time to the first result and to the
// end; the tier-0 compile bracket and the whole run as instructions retired
// and cycles elapsed (macOS proc_pid_rusage, whole process: in the `tier` arm
// the whole-run bracket includes the background compile); the call index at
// which the top tier took over; and the session's tier report.
//
// Bench tooling only: nothing here is a proof or a publication authority.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use std::cell::RefCell;
use std::collections::HashMap;
use std::path::{Path, PathBuf};
use std::sync::Arc;
use std::time::Instant;

use anyhow::{Context, anyhow, bail};
use clap::{Parser, ValueEnum};
use serde::Serialize;
use serde_json::{Value, json};

use trust_cg_codegen::compile_service::{
    ArtifactKind, CompileGeneration, CompileRequest, CompileService, InstalledArtifact, SourceKind,
};
use trust_cg_codegen::jit_contract::{
    AbiDescriptor, ArtifactManifestV1, Endianness, InvalidationKey, JitArtifactKind,
    LayoutManifest, ProofPolicy, TargetDescriptor,
};
use trust_cg_codegen::pipeline::{OptLevel, load_module_from_bytes};
use trust_cg_codegen::target::Target;
use trust_cg_codegen::tier_up::{
    ServiceTierBackend, TierEntryTable, TierPlan, TierUpPoll, TierUpSession,
};
use trust_cg_jit_matrix::bcp_module_builder::{
    BcpWatchedArena, ENTRY_NAME_WATCHED_LITERAL, build_bcp_propagate_watched_literal_module,
};
use trust_cg_jit_matrix::dimacs::read_dimacs_cnf_file;
use trust_cg_jit_matrix::solver_kernel_abi::{
    KernelCtx, KernelEntry, NO_CONFLICTING_CLAUSE, SolverKernelHandle, SolverKernelProvider,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq, ValueEnum, Serialize)]
#[serde(rename_all = "lowercase")]
enum Arm {
    Base,
    Top,
    Tier,
    Tierc,
}

#[derive(Debug, Parser)]
#[command(
    name = "tier_up_bench",
    about = "JIT tier-up on a non-TY workload: exact checksum, compile cost, latency"
)]
struct Cli {
    /// `bcp:<file.cnf>` (the ay watched-literal BCP kernel), or a kernel of
    /// scripts/fuzz: fib, trib, pc, abs, prodi64, st, crcx, mm_ijk, mm_ikj.
    #[arg(long)]
    workload: String,
    #[arg(long, value_enum)]
    arm: Arm,
    /// Kernel calls.
    #[arg(long)]
    calls: u64,
    /// Workload size: array length, matrix side, or BCP decisions per call.
    #[arg(long, default_value_t = 4096)]
    size: usize,
    #[arg(long, default_value = "O0")]
    base: String,
    #[arg(long, default_value = "O2")]
    top: String,
    /// Repository root (for scripts/fuzz). Default: this crate's workspace.
    #[arg(long)]
    repo_root: Option<PathBuf>,
}

// ---------------------------------------------------------------------------
// Counters
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, Copy, Default, Serialize)]
struct Counters {
    instructions: u64,
    cycles: u64,
}

impl Counters {
    fn since(self, start: Counters) -> Counters {
        Counters {
            instructions: self.instructions.saturating_sub(start.instructions),
            cycles: self.cycles.saturating_sub(start.cycles),
        }
    }
}

/// Whole-process instructions retired and cycles elapsed so far (every
/// thread, so the `tier` arm's run bracket includes its background compile).
#[cfg(target_os = "macos")]
fn read_counters() -> Counters {
    // SAFETY: `info` is a properly aligned, zero-initialised rusage_info_v4 and
    // the flavor RUSAGE_INFO_V4 tells the kernel to write exactly that struct.
    unsafe {
        let mut info: libc::rusage_info_v4 = std::mem::zeroed();
        let rc = libc::proc_pid_rusage(
            libc::getpid(),
            libc::RUSAGE_INFO_V4,
            (&mut info as *mut libc::rusage_info_v4).cast::<libc::rusage_info_t>(),
        );
        if rc != 0 {
            return Counters::default();
        }
        Counters {
            instructions: info.ri_instructions,
            cycles: info.ri_cycles,
        }
    }
}

#[cfg(not(target_os = "macos"))]
fn read_counters() -> Counters {
    Counters::default()
}

// ---------------------------------------------------------------------------
// Workloads
// ---------------------------------------------------------------------------

fn xorshift64(state: &mut u64) -> u64 {
    let mut x = *state;
    x ^= x << 13;
    x ^= x >> 7;
    x ^= x << 17;
    *state = x;
    x
}

const FNV_OFFSET: u64 = 0xcbf2_9ce4_8422_2325;
const FNV_PRIME: u64 = 0x0000_0100_0000_01b3;

fn fold(checksum: &mut u64, value: u64) {
    for byte in value.to_le_bytes() {
        *checksum ^= u64::from(byte);
        *checksum = checksum.wrapping_mul(FNV_PRIME);
    }
}

/// The BCP arena behind the ay kernel ABI, with the entry supplied per call.
struct BcpState {
    arena: RefCell<BcpWatchedArena>,
    num_vars: usize,
    decisions: u32,
    entry: std::cell::Cell<KernelEntry>,
}

/// Placeholder entry until the first call binds the installed tier's.
unsafe extern "C" fn unbound_entry(_ctx: *mut KernelCtx, _input: *const u32, _len: usize) -> u64 {
    u64::MAX
}

impl SolverKernelProvider for BcpState {
    fn entry(&self) -> KernelEntry {
        self.entry.get()
    }

    fn ctx_seed(&self) -> KernelCtx {
        let arena = self.arena.borrow();
        let arena_ptr = arena.header.as_ptr() as *mut u8;
        let arena_len = arena.header_byte_len();
        drop(arena);
        KernelCtx {
            arena_ptr,
            arena_len,
            formula_constants_ptr: core::ptr::null(),
            formula_constants_len: 0,
            user_data: core::ptr::null_mut(),
            status: 0,
            implied_literals_out: core::ptr::NonNull::<i32>::dangling().as_ptr(),
            implied_literals_cap: 0,
            implied_literals_len: 0,
            conflicting_clause_index: NO_CONFLICTING_CLAUSE,
            _reserved_pad: 0,
            implied_reasons_out: core::ptr::null_mut(),
            implied_reasons_cap: 0,
            clause_id_translation: core::ptr::null(),
            initial_values: core::ptr::null(),
            initial_values_len: 0,
        }
    }
}

enum Workload {
    Bcp(BcpState),
    Scalar {
        kernel: fn(*const u8, u64) -> u64,
    },
    Buffers {
        state: Buffers,
        kernel: fn(*const u8, &mut Buffers, u64) -> u64,
    },
}

struct Buffers {
    size: usize,
    words: Vec<u32>,
    wide: Vec<i64>,
    bytes: Vec<u8>,
    out: Vec<u32>,
    a: Vec<i32>,
    b: Vec<i32>,
    c: Vec<i32>,
}

impl Buffers {
    fn new(size: usize, matrix: bool) -> Self {
        let mut seed = 0x5eed_0000_0000_0001u64 ^ size as u64;
        let words: Vec<u32> = (0..size).map(|_| xorshift64(&mut seed) as u32).collect();
        let wide: Vec<i64> = (0..size)
            .map(|_| (xorshift64(&mut seed) as i64) | 1)
            .collect();
        let bytes: Vec<u8> = (0..size).map(|_| xorshift64(&mut seed) as u8).collect();
        let cells = if matrix { size * size } else { 0 };
        let mut matrix_values = |_: usize| -> i32 { (xorshift64(&mut seed) % 17) as i32 - 8 };
        let a = (0..cells).map(&mut matrix_values).collect();
        let b = (0..cells).map(&mut matrix_values).collect();
        let c = (0..cells).map(&mut matrix_values).collect();
        Self {
            size,
            words,
            wide,
            bytes,
            out: vec![0; size],
            a,
            b,
            c,
        }
    }
}

fn i32_len(len: usize) -> i32 {
    // `--size` is bounded by the buffers it allocates; saturate rather than
    // wrap if a caller ever asks for more.
    i32::try_from(len).unwrap_or(i32::MAX)
}

fn scalar_fib(entry: *const u8, call: u64) -> u64 {
    // SAFETY: `fib_kernel` is `(i32) -> i32`, C ABI, in every tier.
    let f: extern "C" fn(i32) -> i32 = unsafe { std::mem::transmute(entry) };
    f(1000 + (call % 1024) as i32) as u32 as u64
}

fn scalar_trib(entry: *const u8, call: u64) -> u64 {
    // SAFETY: `trib_kernel` is `(i32) -> i32`, C ABI, in every tier.
    let f: extern "C" fn(i32) -> i32 = unsafe { std::mem::transmute(entry) };
    f(1000 + (call % 1024) as i32) as u32 as u64
}

fn window(buffers: &Buffers, call: u64) -> (usize, usize) {
    let offset = (call % 64) as usize % buffers.size.max(1);
    (offset, buffers.size - offset)
}

fn kernel_pc(entry: *const u8, buffers: &mut Buffers, call: u64) -> u64 {
    let (offset, len) = window(buffers, call);
    // SAFETY: `pc` is `(ptr, i32) -> i32` reading `len` u32 values.
    let f: extern "C" fn(*const u32, i32) -> i32 = unsafe { std::mem::transmute(entry) };
    f(buffers.words[offset..].as_ptr(), i32_len(len)) as u32 as u64
}

fn kernel_abs(entry: *const u8, buffers: &mut Buffers, call: u64) -> u64 {
    let (offset, len) = window(buffers, call);
    // SAFETY: `abssum` is `(ptr, i32) -> i32` reading `len` i32 values.
    let f: extern "C" fn(*const u32, i32) -> i32 = unsafe { std::mem::transmute(entry) };
    f(buffers.words[offset..].as_ptr(), i32_len(len)) as u32 as u64
}

fn kernel_prodi64(entry: *const u8, buffers: &mut Buffers, call: u64) -> u64 {
    let (offset, len) = window(buffers, call);
    // SAFETY: `prod_i64` is `(ptr, i32) -> i64` reading `len` i64 values.
    let f: extern "C" fn(*const i64, i32) -> i64 = unsafe { std::mem::transmute(entry) };
    f(buffers.wide[offset..].as_ptr(), i32_len(len)) as u64
}

fn kernel_st(entry: *const u8, buffers: &mut Buffers, call: u64) -> u64 {
    let (offset, len) = window(buffers, call);
    // SAFETY: `sum3` is `(ptr out, ptr in, i32) -> i32`, writing out[1..len-1]
    // from in[0..len]; both windows hold `len` u32 values.
    let f: extern "C" fn(*mut u32, *const u32, i32) -> i32 = unsafe { std::mem::transmute(entry) };
    let returned = f(
        buffers.out[offset..].as_mut_ptr(),
        buffers.words[offset..].as_ptr(),
        i32_len(len),
    );
    let probe = buffers.out[offset + 1 + (call as usize % (len - 2).max(1))];
    (u64::from(returned as u32) << 32) | u64::from(probe)
}

fn kernel_crcx(entry: *const u8, buffers: &mut Buffers, call: u64) -> u64 {
    let (offset, len) = window(buffers, call);
    let table: Vec<i64> = if buffers.wide.len() >= 256 {
        buffers.wide[..256].to_vec()
    } else {
        (0..256).map(|i| i as i64 * 0x9e37_79b9).collect()
    };
    // SAFETY: `crc_x` is `(ptr bytes, i32, ptr table) -> i64`; it reads `len`
    // bytes and indexes a 256-entry i64 table by byte value.
    let f: extern "C" fn(*const u8, i32, *const i64) -> i64 = unsafe { std::mem::transmute(entry) };
    f(
        buffers.bytes[offset..].as_ptr(),
        i32_len(len),
        table.as_ptr(),
    ) as u64
}

fn kernel_matmul(entry: *const u8, buffers: &mut Buffers, call: u64) -> u64 {
    let n = buffers.size;
    // SAFETY: `matmul` is `(ptr a, ptr b, ptr c, i32 n) -> ()` over three
    // n x n i32 matrices, accumulating into `a`.
    let f: extern "C" fn(*mut i32, *const i32, *const i32, i32) =
        unsafe { std::mem::transmute(entry) };
    f(
        buffers.a.as_mut_ptr(),
        buffers.b.as_ptr(),
        buffers.c.as_ptr(),
        i32_len(n),
    );
    buffers.a[(call as usize * 7919) % (n * n)] as u32 as u64
}

fn call_bcp(state: &BcpState, entry: *const u8, call: u64) -> u64 {
    // SAFETY: `bcp_propagate_watched_literal` has the `KernelEntry` ABI.
    let entry: KernelEntry = unsafe { std::mem::transmute(entry) };
    state.entry.set(entry);
    state.arena.borrow_mut().reset_arena();
    let mut seed = 0x9E37_79B9_7F4A_7C15u64 ^ call.wrapping_mul(0x2545_F491_4F6C_DD1D);
    let decisions: Vec<u32> = (0..state.decisions)
        .map(|_| {
            let var = (xorshift64(&mut seed) % state.num_vars as u64) as u32 + 1;
            let polarity = (xorshift64(&mut seed) & 1) as u32;
            (var << 1) | polarity
        })
        .collect();
    let mut handle = SolverKernelHandle::from_provider(state);
    let status = handle.call(&decisions);
    let trail = state.arena.borrow().trail_len();
    (u64::from(status.result) << 48)
        ^ (u64::from(status.counters) << 16)
        ^ (status.conflicting_clause_index as u32 as u64)
        ^ trail.rotate_left(40)
}

fn load_workload(
    name: &str,
    size: usize,
    repo_root: &Path,
) -> anyhow::Result<(trust_ir::Module, &'static str, Workload)> {
    if let Some(path) = name.strip_prefix("bcp:") {
        let cnf = read_dimacs_cnf_file(Path::new(path))
            .map_err(|error| anyhow!("read {path}: {error}"))?;
        if cnf.num_vars == 0 {
            bail!("{path}: formula has no variables");
        }
        let trail_capacity = (cnf.num_vars + 1 + size).max(8);
        let arena = BcpWatchedArena::build(cnf.num_vars, &cnf.clauses, trail_capacity);
        return Ok((
            build_bcp_propagate_watched_literal_module()?,
            ENTRY_NAME_WATCHED_LITERAL,
            Workload::Bcp(BcpState {
                arena: RefCell::new(arena),
                num_vars: cnf.num_vars,
                decisions: u32::try_from(size).context("decisions fit u32")?,
                entry: std::cell::Cell::new(unbound_entry),
            }),
        ));
    }
    let (file, symbol, workload) = match name {
        "fib" => ("fib", "fib_kernel", Workload::Scalar { kernel: scalar_fib }),
        "trib" => (
            "trib",
            "trib_kernel",
            Workload::Scalar {
                kernel: scalar_trib,
            },
        ),
        other => {
            let (file, symbol, kernel, matrix): (_, _, fn(*const u8, &mut Buffers, u64) -> u64, _) =
                match other {
                    "pc" => ("pc", "pc", kernel_pc, false),
                    "abs" => ("abs", "abssum", kernel_abs, false),
                    "prodi64" => ("prodi64", "prod_i64", kernel_prodi64, false),
                    "st" => ("st", "sum3", kernel_st, false),
                    "crcx" => ("crcx", "crc_x", kernel_crcx, false),
                    "mm_ijk" => ("mm_ijk", "matmul", kernel_matmul, true),
                    "mm_ikj" => ("mm_ikj", "matmul", kernel_matmul, true),
                    unknown => bail!("unknown workload {unknown:?}"),
                };
            if !matrix && size < 70 {
                bail!("--size must be at least 70 for array kernels");
            }
            (
                file,
                symbol,
                Workload::Buffers {
                    state: Buffers::new(size, matrix),
                    kernel,
                },
            )
        }
    };
    let path = repo_root
        .join("scripts/fuzz")
        .join(format!("{file}.trust_ir"));
    let bytes = std::fs::read(&path).with_context(|| format!("read {}", path.display()))?;
    let module = load_module_from_bytes(&bytes)
        .map_err(|error| anyhow!("decode {}: {error}", path.display()))?;
    Ok((module, symbol, workload))
}

impl Workload {
    fn call(&mut self, entry: *const u8, call: u64) -> u64 {
        match self {
            Self::Bcp(state) => call_bcp(state, entry, call),
            Self::Scalar { kernel, .. } => kernel(entry, call),
            Self::Buffers { state, kernel, .. } => kernel(entry, state, call),
        }
    }
}

// ---------------------------------------------------------------------------
// The compile-service request
// ---------------------------------------------------------------------------

fn parse_level(value: &str) -> anyhow::Result<OptLevel> {
    Ok(match value {
        "O0" => OptLevel::O0,
        "O1" => OptLevel::O1,
        "O2" => OptLevel::O2,
        "O3" => OptLevel::O3,
        other => bail!("invalid opt level {other:?}"),
    })
}

/// The deterministic contract the compile service requires before it
/// exposes an executable artifact: host target, ABI and core layout.
fn request(id: &str) -> CompileRequest {
    let proof_policy = ProofPolicy::disabled();
    let target = TargetDescriptor::for_trust_cg_host_jit();
    let abi =
        AbiDescriptor::for_trust_cg_target_os(Target::host(), target.operating_system.clone());
    let layout = LayoutManifest::lp64(Endianness::Little, Target::host().stack_alignment() as u16);
    let invalidation = InvalidationKey::new(
        format!("sha256:{id}-source"),
        "trust-cg-jit-matrix:tier_up_bench",
        target.checksum(),
        abi.checksum(),
        layout.checksum(),
        proof_policy.checksum(),
        1,
    );
    let manifest = ArtifactManifestV1::new(
        id,
        JitArtifactKind::ExecutableMemory,
        target,
        abi,
        layout,
        invalidation,
        proof_policy.clone(),
    );
    let mut request =
        CompileRequest::new(id, CompileGeneration::new(1)).with_artifact_manifest(manifest);
    request.artifact_kind = ArtifactKind::ExecutableMemory;
    request.proof_policy = proof_policy;
    request.provenance.source_kind = SourceKind::TrustIrModule;
    request.provenance.source_fingerprint = Some(format!("sha256:{id}-source"));
    request
}

fn nanos(start: Instant) -> u64 {
    u64::try_from(start.elapsed().as_nanos()).unwrap_or(u64::MAX)
}

fn run(cli: &Cli) -> anyhow::Result<Value> {
    let repo_root = cli.repo_root.clone().unwrap_or_else(|| {
        Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../..")
            .to_path_buf()
    });
    let base = parse_level(&cli.base)?;
    let top = parse_level(&cli.top)?;
    let (module, symbol, mut workload) = load_workload(&cli.workload, cli.size, &repo_root)?;
    let plan = match cli.arm {
        Arm::Base => TierPlan::single(base),
        Arm::Top => TierPlan::single(top),
        Arm::Tier | Arm::Tierc => TierPlan::new([base, top]).map_err(|error| anyhow!("{error}"))?,
    };
    let id = format!(
        "tier_up_bench:{}",
        cli.workload
            .replace(|c: char| !c.is_ascii_alphanumeric(), "_")
    );
    let request = request(&id);
    // The workloads (the in-memory BCP kernel, the `scripts/fuzz` kernels)
    // carry no codegen license; they compile under the named `BenchCorpus`
    // exception, never under a default that would refuse every arm alike.
    let service = CompileService::new(trust_cg_codegen::compile_service::CompileServiceConfig {
        codegen_license: trust_cg_jit_matrix::bench_corpus_license(),
        ..trust_cg_codegen::compile_service::CompileServiceConfig::default()
    });
    let backend =
        ServiceTierBackend::for_request(service, &request, Arc::new(module), &HashMap::new());

    let wall = Instant::now();
    let start = read_counters();
    let started = if cli.arm == Arm::Tierc {
        TierUpSession::start_concurrent(backend, request, plan)
    } else {
        TierUpSession::start(backend, request, plan)
    };
    let (mut session, tier0): (TierUpSession<InstalledArtifact>, _) =
        started.map_err(|error| anyhow!("{error}"))?;
    let tier0_compile = read_counters().since(start);
    let tier0_compile_ns = nanos(wall);
    let table = TierEntryTable::new([symbol], tier0.tier, &tier0.artifact)
        .map_err(|error| anyhow!("{error}"))?;
    table.prepare_current_thread();
    let mut held = vec![tier0];

    let mut checksum = FNV_OFFSET;
    let mut first_result_ns = None;
    let mut upgraded_at_call = None;
    let mut refused = None;
    let mut polling = matches!(cli.arm, Arm::Tier | Arm::Tierc);
    for call in 0..cli.calls {
        if polling {
            match session.poll() {
                TierUpPoll::Pending => {}
                TierUpPoll::Upgraded(install) => {
                    table
                        .install(install.tier, &install.artifact)
                        .map_err(|error| anyhow!("{error}"))?;
                    upgraded_at_call = Some(call);
                    held.push(install);
                }
                TierUpPoll::Refused { refusal, .. } => {
                    refused = Some(refusal.to_string());
                    polling = false;
                }
                TierUpPoll::Complete => polling = false,
            }
        }
        let entry = table.entry(0).ok_or_else(|| anyhow!("entry 0"))?;
        let value = workload.call(entry, call);
        fold(&mut checksum, value);
        if first_result_ns.is_none() {
            first_result_ns = Some(nanos(wall));
        }
    }
    let run_counters = read_counters().since(start);
    let run_ns = nanos(wall);
    // The run is over: a top tier still compiling is not waited for (the
    // consumer's cost is what it paid), but the worker is joined so the
    // process accounts for it and exits cleanly.
    let report = session.shutdown();
    let after_shutdown = read_counters().since(start);

    Ok(json!({
        "schema": "trust-cg.tier-up-bench.v1",
        "workload": cli.workload,
        "arm": cli.arm,
        "calls": cli.calls,
        "size": cli.size,
        "levels": plan_levels(cli.arm, &cli.base, &cli.top),
        "checksum": format!("{checksum:016x}"),
        "tier0_compile": {
            "instructions": tier0_compile.instructions,
            "cycles": tier0_compile.cycles,
            "wall_ns": tier0_compile_ns,
        },
        "first_result_wall_ns": first_result_ns,
        "run": {
            "instructions": run_counters.instructions,
            "cycles": run_counters.cycles,
            "wall_ns": run_ns,
        },
        "after_shutdown": {
            "instructions": after_shutdown.instructions,
            "cycles": after_shutdown.cycles,
        },
        "installed_tier": table.installed_tier(),
        "upgraded_at_call": upgraded_at_call,
        "refused": refused,
        "tier_report": report.to_json_value(),
        "counter_source": if cfg!(target_os = "macos") {
            "proc_pid_rusage(RUSAGE_INFO_V4), whole process"
        } else {
            "unavailable"
        },
    }))
}

fn plan_levels(arm: Arm, base: &str, top: &str) -> Vec<String> {
    match arm {
        Arm::Base => vec![base.to_owned()],
        Arm::Top => vec![top.to_owned()],
        Arm::Tier | Arm::Tierc => vec![base.to_owned(), top.to_owned()],
    }
}

fn main() -> anyhow::Result<()> {
    let cli = Cli::parse();
    let result = run(&cli)?;
    println!("{}", serde_json::to_string_pretty(&result)?);
    Ok(())
}
