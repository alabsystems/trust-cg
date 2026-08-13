// trust-cg-codegen/tests/ty_request_1_1_replay_bundle_reducer.rs
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

#[path = "common/fixture_contract.rs"]
mod fixture_contract;
use fixture_contract::FixtureContractLookup;

use std::{
    collections::HashMap,
    fs,
    path::{Path, PathBuf},
    process::Command,
};

use serde_json::{Value, json};
use trust_cg_codegen::jit_contract::{ArtifactChecksum, ProofPolicy};
use trust_cg_codegen::jit_release::{
    RELEASE_TY_NATIVE_FUSED_REPLAY_GATE_PACKET_HASH_KEY,
    RELEASE_TY_NATIVE_FUSED_REPLAY_MANIFEST_CHECKSUM_KEY,
    RELEASE_TY_NATIVE_FUSED_REPLAY_PROOF_VALIDATION_SHA256_KEY,
    RELEASE_TY_NATIVE_FUSED_REPLAY_RECORD_SHA256_KEY,
    RELEASE_TY_NATIVE_FUSED_REPLAY_ROOT_SHA256_KEY, RELEASE_TY_NATIVE_FUSED_REPLAY_SCHEMA,
    RELEASE_TY_NATIVE_FUSED_REPLAY_SCHEMA_KEY, RELEASE_TY_NATIVE_FUSED_REPLAY_SCHEMA_VERSION_KEY,
    RELEASE_TY_NATIVE_FUSED_REPLAY_TELEMETRY_EVENT_ID_KEY,
    RELEASE_TY_NATIVE_FUSED_REPLAY_TELEMETRY_RECORD_SHA256_KEY, ReleaseArtifactManifestReference,
    ReleaseBundleFileReference, ReleaseProofReportReference, ReleaseReplayBundleMetadata,
    ReleaseTyNativeFusedReplayMetadata,
};
use trust_cg_codegen::{
    Compiler, CompilerConfig, CompilerTraceLevel, ExecutableBuffer, FormatMode, Target,
    load_module_as, pipeline::OptLevel,
};
use trust_ir::{Module as TrustIrModule, Ty};
use trust_ir_build::ModuleBuilder;

#[path = "common/ty_contract.rs"]
mod ty_contract;

use ty_contract::{
    TyNativeFusedEvidenceRefs, TyNativeFusedManifestIdentity, abi_i32, abi_ptr, extern_c_signature,
    ty_native_fused_parent_loop_manifest_for_symbol_with_proof_policy,
    ty_native_fused_verified_evidence, ty_reducer_lookup_contract, ty_reducer_manifest,
};

const BUNDLE_ENV: &str = "TRUST_CG_TY_REPLAY_BUNDLE";
const INVOKE_CHILD_ENV: &str = "TRUST_CG_TY_REPLAY_BUNDLE_INVOKE_CHILD";
const ENV_INVOKE_TEST_NAME: &str = "env_ty_request_replay_bundle_jit_invokes_in_child_when_present";
const REQUEST_SYMBOL: &str = "Request__1_1";
const LINKED_STAGE: &str = "compile_module_native.linked";
const TRUST_IR_JSON_NAME: &str = "000001-compile_module_native.linked-Request__1_1.trust_ir.json";
const METADATA_NAME: &str = "000001-compile_module_native.linked-Request__1_1.metadata.json";
const JIT_STATUS_OK: u8 = 0;
const JIT_RUNTIME_ERROR_DIVISION_BY_ZERO: u8 = 1;

type RequestCalloutFn = unsafe extern "C" fn(*mut JitCallOut, *const i64, *mut i64, u32);

#[repr(C)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct JitCallOut {
    status: u8,
    value: i64,
    err_kind: u8,
    err_span_start: u32,
    err_span_end: u32,
    err_file_id: u32,
    conjuncts_passed: u32,
}

impl Default for JitCallOut {
    fn default() -> Self {
        Self {
            status: JIT_STATUS_OK,
            value: 0,
            err_kind: JIT_RUNTIME_ERROR_DIVISION_BY_ZERO,
            err_span_start: 0,
            err_span_end: 0,
            err_file_id: 0,
            conjuncts_passed: 0,
        }
    }
}

#[derive(Debug)]
struct ReplayBundle {
    root: PathBuf,
    metadata_path: PathBuf,
    trust_ir_json_path: PathBuf,
    callout_path: PathBuf,
    crash_path: PathBuf,
    metadata: ReplayMetadata,
    callout: EnteringCallout,
    crash: CrashPacket,
}

#[derive(Debug)]
struct ReplayTrustIrArtifact {
    root: PathBuf,
    metadata_path: PathBuf,
    trust_ir_json_path: PathBuf,
    metadata: ReplayMetadata,
}

#[derive(Debug)]
struct ReplayMetadata {
    schema: String,
    stage: String,
    module_name: String,
    source_revisions: SourceRevisions,
    opt_level: OptLevel,
    target: Target,
    target_triple: String,
    function_count: u64,
    entry_symbol: String,
    entry_pc: Option<u64>,
    entry_block: String,
}

#[derive(Debug)]
struct SourceRevisions {
    trust_cg_pipeline_version: String,
    ty_git_commit: String,
}

#[derive(Debug)]
struct EnteringCallout {
    schema: String,
    event: String,
    kind: String,
    index: u64,
    symbol_name: String,
    function_address: Option<u64>,
    abi_signature: String,
    state_len: u64,
    state_head_len: usize,
    state_out_initial_head_len: usize,
    state_slots: Vec<i64>,
    state_out_initial_slots: Vec<i64>,
}

#[derive(Debug)]
struct CrashPacket {
    schema: String,
    fault_signal: String,
    fault_signal_code: Option<u64>,
    fault_pc: Option<u64>,
    fault_address: Option<u64>,
    jit_symbol: String,
    jit_range_start: Option<u64>,
    pc_map_offset: Option<u64>,
    pc_map_block: String,
    metadata_path: String,
    esr_description: String,
}

#[derive(Debug)]
struct CompileEvidence {
    function_count: usize,
    object_bytes: usize,
    instruction_count: usize,
}

#[derive(Debug)]
struct JitCompileEvidence {
    function_count: usize,
    instruction_count: usize,
    symbol_count: usize,
    allocated_bytes: usize,
}

#[derive(Debug)]
struct LowLevelJitCompileEvidence {
    function_count: usize,
    symbol_count: usize,
    allocated_bytes: usize,
    code_len: usize,
    proof_allocation_len: usize,
    exact_symbol_match: bool,
}

struct ReplayJit {
    buffer: ExecutableBuffer,
    evidence: JitCompileEvidence,
}

#[derive(Debug)]
struct JitInvocationEvidence {
    compile: JitCompileEvidence,
    out: JitCallOut,
    state_out_slots: Vec<i64>,
}

fn require_str(value: &Value, path: &[&str]) -> Result<String, String> {
    get_path(value, path)
        .and_then(Value::as_str)
        .map(str::to_owned)
        .ok_or_else(|| format!("missing string field {}", path.join(".")))
}

fn require_source_revision(value: &Value, name: &str) -> Result<String, String> {
    let path = ["source_revisions", name];
    let value = get_path(value, &path)
        .and_then(Value::as_str)
        .ok_or_else(|| {
            format!(
                "metadata missing non-empty source revision {}",
                path.join(".")
            )
        })?;
    if value.trim().is_empty() {
        return Err(format!(
            "metadata missing non-empty source revision {}",
            path.join(".")
        ));
    }
    Ok(value.to_owned())
}

fn optional_str(value: &Value, path: &[&str]) -> Option<String> {
    get_path(value, path)
        .and_then(Value::as_str)
        .map(str::to_owned)
}

fn optional_u64(value: &Value, path: &[&str]) -> Option<u64> {
    let value = get_path(value, path)?;
    value
        .as_u64()
        .or_else(|| value.as_str().and_then(parse_u64_value))
}

fn get_path<'a>(value: &'a Value, path: &[&str]) -> Option<&'a Value> {
    let mut cursor = value;
    for key in path {
        cursor = cursor.get(*key)?;
    }
    Some(cursor)
}

fn parse_u64_value(value: &str) -> Option<u64> {
    value
        .strip_prefix("0x")
        .map(|hex| u64::from_str_radix(hex, 16).ok())
        .unwrap_or_else(|| value.parse::<u64>().ok())
}

fn parse_i64_value(value: &str) -> Option<i64> {
    if let Some(hex) = value.strip_prefix("-0x") {
        i64::from_str_radix(hex, 16).ok().map(|parsed| -parsed)
    } else if let Some(hex) = value.strip_prefix("0x") {
        u64::from_str_radix(hex, 16)
            .ok()
            .and_then(|parsed| i64::try_from(parsed).ok())
    } else {
        value.parse::<i64>().ok()
    }
}

fn require_i64_slots(value: &Value, path: &[&str]) -> Result<Vec<i64>, String> {
    let slots = get_path(value, path)
        .and_then(Value::as_array)
        .ok_or_else(|| format!("missing i64 array field {}", path.join(".")))?;
    slots
        .iter()
        .enumerate()
        .map(|(index, value)| {
            value
                .as_i64()
                .or_else(|| value.as_u64().and_then(|value| i64::try_from(value).ok()))
                .or_else(|| value.as_str().and_then(parse_i64_value))
                .ok_or_else(|| {
                    format!(
                        "field {}[{index}] is not an i64-compatible value",
                        path.join(".")
                    )
                })
        })
        .collect()
}

fn optional_i64_slots(value: &Value, path: &[&str]) -> Result<Option<Vec<i64>>, String> {
    if get_path(value, path).is_none() {
        Ok(None)
    } else {
        require_i64_slots(value, path).map(Some)
    }
}

fn parse_head_len(
    value: &Value,
    head_path: &[&str],
    slots: &[i64],
    label: &str,
) -> Result<usize, String> {
    let Some(head) = optional_i64_slots(value, head_path)? else {
        return Ok(0);
    };
    if slots.get(..head.len()) != Some(head.as_slice()) {
        return Err(format!("{label}.head is not a prefix of {label}.slots"));
    }
    Ok(head.len())
}

fn parse_opt_level(value: &str) -> Result<OptLevel, String> {
    match value {
        "O0" | "0" => Ok(OptLevel::O0),
        "O1" | "1" => Ok(OptLevel::O1),
        "O2" | "2" => Ok(OptLevel::O2),
        "O3" | "3" => Ok(OptLevel::O3),
        other => Err(format!("unsupported replay opt level {other:?}")),
    }
}

fn target_from_triple(value: &str) -> Result<Target, String> {
    if value.starts_with("aarch64") || value.starts_with("arm64") {
        Ok(Target::Aarch64)
    } else if value.starts_with("x86_64") {
        Ok(Target::X86_64)
    } else if value.starts_with("riscv64") {
        Ok(Target::Riscv64)
    } else {
        Err(format!("unsupported replay target triple {value:?}"))
    }
}

fn first_pc_map_function<'a>(metadata: &'a Value, symbol: &str) -> Result<&'a Value, String> {
    metadata
        .get("jit_pc_map")
        .and_then(|pc_map| pc_map.get("functions"))
        .and_then(Value::as_array)
        .and_then(|functions| {
            functions
                .iter()
                .find(|function| function.get("name").and_then(Value::as_str) == Some(symbol))
                .or_else(|| functions.first())
        })
        .ok_or_else(|| "metadata missing jit_pc_map.functions".to_owned())
}

fn parse_metadata(path: &Path) -> Result<ReplayMetadata, String> {
    let bytes = fs::read(path).map_err(|err| format!("read metadata {}: {err}", path.display()))?;
    let value: Value = serde_json::from_slice(&bytes)
        .map_err(|err| format!("parse metadata {}: {err}", path.display()))?;
    let schema = require_str(&value, &["schema"])?;
    let stage = require_str(&value, &["stage"])?;
    let module_name = require_str(&value, &["module_name"])?;
    let opt_level = parse_opt_level(&require_str(&value, &["opt_level"])?)?;
    let target_triple = require_str(&value, &["target_triple"])?;
    let target = target_from_triple(&target_triple)?;
    let function_count = optional_u64(&value, &["module", "function_count"])
        .ok_or_else(|| "metadata missing module.function_count".to_owned())?;
    let source_revisions = SourceRevisions {
        trust_cg_pipeline_version: require_source_revision(&value, "trust_cg_pipeline_version")?,
        ty_git_commit: require_source_revision(&value, "ty_git_commit")?,
    };

    let entry = first_pc_map_function(&value, &module_name)?;
    let entry_symbol = require_str(entry, &["name"])?;
    let first_block = entry
        .get("blocks")
        .and_then(Value::as_array)
        .and_then(|blocks| blocks.first())
        .ok_or_else(|| "metadata pc map function has no blocks".to_owned())?;
    let entry_pc =
        optional_u64(first_block, &["pc"]).or_else(|| optional_u64(entry, &["runtime_start"]));
    let entry_block = require_str(first_block, &["block"])?;

    Ok(ReplayMetadata {
        schema,
        stage,
        module_name,
        source_revisions,
        opt_level,
        target,
        target_triple,
        function_count,
        entry_symbol,
        entry_pc,
        entry_block,
    })
}

fn parse_callout(path: &Path) -> Result<EnteringCallout, String> {
    let bytes = fs::read(path).map_err(|err| format!("read callout {}: {err}", path.display()))?;
    let value: Value = serde_json::from_slice(&bytes)
        .map_err(|err| format!("parse callout {}: {err}", path.display()))?;
    let schema = require_str(&value, &["schema"])?;
    let event = require_str(&value, &["event"])?;
    let kind = require_str(&value, &["kind"])?;
    let index =
        optional_u64(&value, &["index"]).ok_or_else(|| "callout missing index".to_owned())?;
    let symbol_name = optional_str(&value, &["symbol_name"])
        .or_else(|| optional_str(&value, &["name"]))
        .ok_or_else(|| "callout missing symbol name".to_owned())?;
    let function_address = optional_u64(&value, &["function_address"]);
    let abi_signature = require_str(&value, &["abi", "signature"])?;
    let state_len = optional_u64(&value, &["abi", "state_len"])
        .ok_or_else(|| "callout missing abi.state_len".to_owned())?;
    let state_slots = require_i64_slots(&value, &["state", "slots"])?;
    let state_out_initial_slots = require_i64_slots(&value, &["state_out_initial", "slots"])?;
    let state_head_len = parse_head_len(&value, &["state", "head"], &state_slots, "state")?;
    let state_out_initial_head_len = parse_head_len(
        &value,
        &["state_out_initial", "head"],
        &state_out_initial_slots,
        "state_out_initial",
    )?;

    Ok(EnteringCallout {
        schema,
        event,
        kind,
        index,
        symbol_name,
        function_address,
        abi_signature,
        state_len,
        state_head_len,
        state_out_initial_head_len,
        state_slots,
        state_out_initial_slots,
    })
}

fn parse_crash(path: &Path) -> Result<CrashPacket, String> {
    let bytes = fs::read(path).map_err(|err| format!("read crash {}: {err}", path.display()))?;
    let value: Value = serde_json::from_slice(&bytes)
        .map_err(|err| format!("parse crash {}: {err}", path.display()))?;
    let schema = require_str(&value, &["schema"])?;
    let fault_signal = require_str(&value, &["os_crash_report", "fault_signal"])?;
    let fault_signal_code = optional_u64(&value, &["os_crash_report", "fault_signal_code"]);
    let fault_pc = optional_u64(&value, &["os_crash_report", "fault_pc"]);
    let fault_address = optional_u64(&value, &["os_crash_report", "fault_address"]);
    let jit_symbol = require_str(&value, &["jit", "function", "name"])?;
    let jit_range_start = optional_u64(&value, &["jit", "function", "range", "start"])
        .or_else(|| optional_u64(&value, &["jit", "function", "runtime_start"]));
    let pc_map_offset = optional_u64(&value, &["jit", "pc_map_offset_decimal"])
        .or_else(|| optional_u64(&value, &["jit", "pc_map_offset"]));
    let pc_map_block = require_str(&value, &["jit", "nearest_block", "block"])?;
    let metadata_path = require_str(&value, &["jit", "metadata_path"])?;
    let esr_description = require_str(
        &value,
        &[
            "os_crash_report",
            "thread",
            "threadState",
            "esr",
            "description",
        ],
    )?;

    Ok(CrashPacket {
        schema,
        fault_signal,
        fault_signal_code,
        fault_pc,
        fault_address,
        jit_symbol,
        jit_range_start,
        pc_map_offset,
        pc_map_block,
        metadata_path,
        esr_description,
    })
}

fn collect_files(root: &Path, files: &mut Vec<PathBuf>) -> Result<(), String> {
    for entry in fs::read_dir(root).map_err(|err| format!("read dir {}: {err}", root.display()))? {
        let entry = entry.map_err(|err| format!("read dir entry in {}: {err}", root.display()))?;
        let path = entry.path();
        let metadata = entry
            .metadata()
            .map_err(|err| format!("stat {}: {err}", path.display()))?;
        if metadata.is_dir() {
            collect_files(&path, files)?;
        } else if metadata.is_file() {
            files.push(path);
        }
    }
    Ok(())
}

fn file_name(path: &Path) -> String {
    path.file_name()
        .and_then(|name| name.to_str())
        .unwrap_or_default()
        .to_owned()
}

fn find_linked_metadata(files: &[PathBuf]) -> Result<PathBuf, String> {
    files
        .iter()
        .find(|path| {
            let name = file_name(path);
            name.contains(LINKED_STAGE)
                && name.contains(REQUEST_SYMBOL)
                && name.ends_with(".metadata.json")
        })
        .or_else(|| {
            files.iter().find(|path| {
                let name = file_name(path);
                name.contains(REQUEST_SYMBOL) && name.ends_with(".metadata.json")
            })
        })
        .cloned()
        .ok_or_else(|| format!("could not find linked {REQUEST_SYMBOL} metadata JSON"))
}

fn find_callout(files: &[PathBuf]) -> Result<PathBuf, String> {
    files
        .iter()
        .find(|path| {
            let name = file_name(path);
            name.contains(REQUEST_SYMBOL) && name.contains(".entering.") && name.ends_with(".json")
        })
        .cloned()
        .ok_or_else(|| format!("could not find entering callout JSON for {REQUEST_SYMBOL}"))
}

fn find_crash(files: &[PathBuf]) -> Result<PathBuf, String> {
    let mut crash_candidates: Vec<PathBuf> = files
        .iter()
        .filter(|path| path.components().any(|part| part.as_os_str() == "crash"))
        .filter(|path| path.extension().and_then(|ext| ext.to_str()) == Some("json"))
        .cloned()
        .collect();
    crash_candidates.sort();

    crash_candidates
        .iter()
        .find(|path| {
            parse_crash(path)
                .map(|crash| crash.jit_symbol == REQUEST_SYMBOL)
                .unwrap_or(false)
        })
        .or_else(|| crash_candidates.first())
        .cloned()
        .ok_or_else(|| "could not find crash JSON".to_owned())
}

fn trust_ir_json_from_metadata(metadata_path: &Path, files: &[PathBuf]) -> Result<PathBuf, String> {
    let metadata_bytes = fs::read(metadata_path)
        .map_err(|err| format!("read metadata {}: {err}", metadata_path.display()))?;
    let metadata: Value = serde_json::from_slice(&metadata_bytes)
        .map_err(|err| format!("parse metadata {}: {err}", metadata_path.display()))?;
    if let Some(relative) = optional_str(&metadata, &["files", "serde_json_trust_ir"]) {
        let path = metadata_path
            .parent()
            .ok_or_else(|| format!("metadata has no parent: {}", metadata_path.display()))?
            .join(relative);
        if path.is_file() {
            return Ok(path);
        }
    }

    files
        .iter()
        .find(|path| {
            let name = file_name(path);
            name.contains(LINKED_STAGE)
                && name.contains(REQUEST_SYMBOL)
                && name.ends_with(".trust_ir.json")
        })
        .or_else(|| {
            files.iter().find(|path| {
                let name = file_name(path);
                name.contains(REQUEST_SYMBOL) && name.ends_with(".trust_ir.json")
            })
        })
        .cloned()
        .ok_or_else(|| format!("could not find linked {REQUEST_SYMBOL} trust_ir JSON"))
}

fn load_replay_trust_ir_artifact(root: &Path) -> Result<ReplayTrustIrArtifact, String> {
    let mut files = Vec::new();
    collect_files(root, &mut files)?;
    let metadata_path = find_linked_metadata(&files)?;
    let trust_ir_json_path = trust_ir_json_from_metadata(&metadata_path, &files)?;
    let metadata = parse_metadata(&metadata_path)?;

    let artifact = ReplayTrustIrArtifact {
        root: root.to_path_buf(),
        metadata_path,
        trust_ir_json_path,
        metadata,
    };
    validate_replay_trust_ir_artifact(&artifact)?;
    Ok(artifact)
}

fn load_replay_bundle(root: &Path) -> Result<ReplayBundle, String> {
    let mut files = Vec::new();
    collect_files(root, &mut files)?;
    let metadata_path = find_linked_metadata(&files)?;
    let trust_ir_json_path = trust_ir_json_from_metadata(&metadata_path, &files)?;
    let callout_path = find_callout(&files)?;
    let crash_path = find_crash(&files)?;
    let metadata = parse_metadata(&metadata_path)?;
    let callout = parse_callout(&callout_path)?;
    let crash = parse_crash(&crash_path)?;

    let bundle = ReplayBundle {
        root: root.to_path_buf(),
        metadata_path,
        trust_ir_json_path,
        callout_path,
        crash_path,
        metadata,
        callout,
        crash,
    };
    validate_replay_bundle(&bundle)?;
    Ok(bundle)
}

fn validate_replay_trust_ir_artifact(artifact: &ReplayTrustIrArtifact) -> Result<(), String> {
    if artifact.metadata.schema != "ty.trust-cg.native_replay_trust_ir.v1" {
        return Err(format!(
            "unexpected metadata schema {}",
            artifact.metadata.schema
        ));
    }
    if artifact.metadata.stage != LINKED_STAGE {
        return Err(format!(
            "unexpected metadata stage {}",
            artifact.metadata.stage
        ));
    }
    if artifact.metadata.module_name != REQUEST_SYMBOL
        || artifact.metadata.entry_symbol != REQUEST_SYMBOL
    {
        return Err(format!(
            "metadata does not target {REQUEST_SYMBOL}: module={} entry={}",
            artifact.metadata.module_name, artifact.metadata.entry_symbol
        ));
    }
    Ok(())
}

fn validate_replay_bundle(bundle: &ReplayBundle) -> Result<(), String> {
    if bundle.metadata.schema != "ty.trust-cg.native_replay_trust_ir.v1" {
        return Err(format!(
            "unexpected metadata schema {}",
            bundle.metadata.schema
        ));
    }
    if bundle.metadata.stage != LINKED_STAGE {
        return Err(format!(
            "unexpected metadata stage {}",
            bundle.metadata.stage
        ));
    }
    if bundle.metadata.module_name != REQUEST_SYMBOL
        || bundle.metadata.entry_symbol != REQUEST_SYMBOL
    {
        return Err(format!(
            "metadata does not target {REQUEST_SYMBOL}: module={} entry={}",
            bundle.metadata.module_name, bundle.metadata.entry_symbol
        ));
    }
    if bundle.callout.schema != "ty.trust-cg.native_callout_selftest.v1" {
        return Err(format!(
            "unexpected callout schema {}",
            bundle.callout.schema
        ));
    }
    if bundle.callout.event != "entering" {
        return Err(format!("unexpected callout event {}", bundle.callout.event));
    }
    if bundle.callout.symbol_name != REQUEST_SYMBOL {
        return Err(format!(
            "unexpected callout symbol {}",
            bundle.callout.symbol_name
        ));
    }
    if bundle.callout.abi_signature
        != r#"extern "C" fn(*mut JitCallOut, *const i64, *mut i64, u32)"#
    {
        return Err(format!(
            "unexpected callout ABI signature {}",
            bundle.callout.abi_signature
        ));
    }
    if bundle.callout.state_slots.len() as u64 != bundle.callout.state_len {
        return Err(format!(
            "callout state.slots len {} differs from abi.state_len {}",
            bundle.callout.state_slots.len(),
            bundle.callout.state_len
        ));
    }
    if bundle.callout.state_out_initial_slots.len() as u64 != bundle.callout.state_len {
        return Err(format!(
            "callout state_out_initial.slots len {} differs from abi.state_len {}",
            bundle.callout.state_out_initial_slots.len(),
            bundle.callout.state_len
        ));
    }
    if bundle.crash.fault_signal != "SIGBUS" {
        return Err(format!(
            "unexpected crash signal {}",
            bundle.crash.fault_signal
        ));
    }
    if bundle.crash.schema != "ty.trust-cg.native_crash_packet.v1" {
        return Err(format!("unexpected crash schema {}", bundle.crash.schema));
    }
    if bundle.crash.jit_symbol != REQUEST_SYMBOL {
        return Err(format!(
            "unexpected crash symbol {}",
            bundle.crash.jit_symbol
        ));
    }
    if bundle.crash.pc_map_offset != Some(0)
        || bundle.crash.pc_map_block != bundle.metadata.entry_block
    {
        return Err(format!(
            "crash is not at entry block: offset={:?} block={} metadata_entry={}",
            bundle.crash.pc_map_offset, bundle.crash.pc_map_block, bundle.metadata.entry_block
        ));
    }
    if let (Some(callout_pc), Some(fault_pc)) =
        (bundle.callout.function_address, bundle.crash.fault_pc)
        && callout_pc != fault_pc
    {
        return Err(format!(
            "callout function address 0x{callout_pc:x} differs from crash PC 0x{fault_pc:x}"
        ));
    }
    if let (Some(entry_pc), Some(fault_pc)) = (bundle.metadata.entry_pc, bundle.crash.fault_pc)
        && entry_pc != fault_pc
    {
        return Err(format!(
            "metadata entry PC 0x{entry_pc:x} differs from crash PC 0x{fault_pc:x}"
        ));
    }
    if !bundle.crash.esr_description.contains("Instruction Abort") {
        return Err(format!(
            "crash ESR is not an instruction abort: {}",
            bundle.crash.esr_description
        ));
    }
    Ok(())
}

fn load_replay_trust_ir_module(bundle: &ReplayBundle) -> Result<TrustIrModule, String> {
    load_module_as(&bundle.trust_ir_json_path, FormatMode::Json).map_err(|err| {
        format!(
            "load trust_ir JSON {}: {err}",
            bundle.trust_ir_json_path.display()
        )
    })
}

fn load_replay_trust_ir_artifact_module(
    artifact: &ReplayTrustIrArtifact,
) -> Result<TrustIrModule, String> {
    load_module_as(&artifact.trust_ir_json_path, FormatMode::Json).map_err(|err| {
        format!(
            "load trust_ir JSON {}: {err}",
            artifact.trust_ir_json_path.display()
        )
    })
}

fn compile_replay_trust_ir(bundle: &ReplayBundle) -> Result<CompileEvidence, String> {
    let module = load_replay_trust_ir_module(bundle)?;
    let result = Compiler::new(CompilerConfig {
        opt_level: bundle.metadata.opt_level,
        target: bundle.metadata.target,
        emit_proofs: false,
        trace_level: CompilerTraceLevel::None,
        emit_debug: false,
        parallel: false,
        cegis_superopt_budget_sec: None,
        enable_fsym_trust_ir_preflight: false,
        enable_jit_fast_regalloc: false,
        jit_validation_mode_override: None,
        panic_unwind: false,
    })
    .compile(&module)
    .map_err(|err| {
        format!(
            "compile trust_ir JSON {}: {err}",
            bundle.trust_ir_json_path.display()
        )
    })?;

    if result.metrics.function_count == 0 || result.object_code.is_empty() {
        return Err("replay trust_ir compiled to an empty object".to_owned());
    }
    Ok(CompileEvidence {
        function_count: result.metrics.function_count,
        object_bytes: result.object_code.len(),
        instruction_count: result.metrics.instruction_count,
    })
}

fn compile_replay_trust_ir_to_jit(bundle: &ReplayBundle) -> Result<ReplayJit, String> {
    if bundle.metadata.target != Target::Aarch64 {
        return Err(format!(
            "replay JIT reducer only supports AArch64, got {:?}",
            bundle.metadata.target
        ));
    }

    let module = load_replay_trust_ir_module(bundle)?;
    let mut config = CompilerConfig::jit_fast(Target::Aarch64);
    config.opt_level = bundle.metadata.opt_level;
    let result = Compiler::new(config)
        .compile_module_to_jit(&module, &HashMap::new())
        .map_err(|err| {
            format!(
                "compile trust_ir JSON to JIT {}: {err}",
                bundle.trust_ir_json_path.display()
            )
        })?;

    if result.metrics.function_count == 0 || result.buffer.allocated_size() == 0 {
        return Err("replay trust_ir compiled to an empty JIT buffer".to_owned());
    }
    if result.buffer.get_fn_ptr_bound(REQUEST_SYMBOL).is_none() {
        return Err(format!(
            "replay JIT buffer does not export {REQUEST_SYMBOL}"
        ));
    }

    Ok(ReplayJit {
        evidence: JitCompileEvidence {
            function_count: result.metrics.function_count,
            instruction_count: result.metrics.instruction_count,
            symbol_count: result.buffer.symbol_count(),
            allocated_bytes: result.buffer.allocated_size(),
        },
        buffer: result.buffer,
    })
}

fn compile_replay_trust_ir_through_low_level_jit(
    artifact: &ReplayTrustIrArtifact,
) -> Result<LowLevelJitCompileEvidence, String> {
    if artifact.metadata.target != Target::Aarch64 {
        return Err(format!(
            "low-level replay JIT reducer only supports AArch64, got {:?}",
            artifact.metadata.target
        ));
    }

    let mut module = load_replay_trust_ir_artifact_module(artifact)?;
    trust_cg_codegen::dialect_pipeline::lower_dialects(&mut module).map_err(|err| {
        format!(
            "lower replay trust_ir dialects {}: {err}",
            artifact.trust_ir_json_path.display()
        )
    })?;

    let lowered = trust_cg_lower::translate_module(&module).map_err(|err| {
        format!(
            "translate replay trust_ir {}: {err}",
            artifact.trust_ir_json_path.display()
        )
    })?;
    if lowered.is_empty() {
        return Err("replay trust_ir translated to no functions".to_owned());
    }

    let pipeline_config = trust_cg_codegen::PipelineConfig {
        opt_level: artifact.metadata.opt_level,
        emit_debug: false,
        verify_dispatch: trust_cg_codegen::DispatchVerifyMode::FallbackOnFailure,
        verify: false,
        cegis_superopt_budget_sec: None,
        target_triple: artifact.metadata.target_triple.clone(),
        ..trust_cg_codegen::PipelineConfig::default()
    };

    let pipeline = trust_cg_codegen::Pipeline::new(pipeline_config);
    let mut ir_functions = Vec::with_capacity(lowered.len());
    for (func, proof_ctx) in &lowered {
        let ir_func = pipeline
            .prepare_function_with_proofs(func, Some(proof_ctx))
            .map_err(|err| format!("prepare replay function '{}': {err}", func.name))?;
        ir_functions.push(ir_func);
    }

    let jit = trust_cg_codegen::JitCompiler::new(trust_cg_codegen::JitConfig {
        opt_level: artifact.metadata.opt_level,
        verify: false,
        verify_dispatch: trust_cg_codegen::DispatchVerifyMode::FallbackOnFailure,
        ..trust_cg_codegen::JitConfig::default()
    });
    let extern_symbols: HashMap<String, *const u8> = HashMap::new();
    let buffer = jit
        .compile_raw(&ir_functions, &extern_symbols)
        .map_err(|err| {
            format!(
                "low-level compile_raw replay {}: {err}",
                artifact.trust_ir_json_path.display()
            )
        })?;

    let allocated_bytes = buffer.allocated_size();
    if allocated_bytes == 0 {
        return Err("low-level replay trust_ir compiled to zero allocated_size".to_owned());
    }
    let pointer = buffer
        .get_fn_ptr_bound(REQUEST_SYMBOL)
        .ok_or_else(|| format!("low-level replay JIT buffer does not export {REQUEST_SYMBOL}"))?
        .as_ptr();
    let proof = buffer
        .diagnose_published_symbol_ptr(REQUEST_SYMBOL, pointer)
        .map_err(|err| format!("diagnose low-level replay JIT symbol {REQUEST_SYMBOL}: {err}"))?;
    if proof.allocation_len != allocated_bytes {
        return Err(format!(
            "low-level replay allocated_size/proof allocation mismatch: allocated_size={} proof_allocation_len={}",
            allocated_bytes, proof.allocation_len
        ));
    }
    if proof.code_len > proof.allocation_len {
        return Err(format!(
            "low-level replay code_len exceeds allocation_len: code_len={} allocation_len={}",
            proof.code_len, proof.allocation_len
        ));
    }

    Ok(LowLevelJitCompileEvidence {
        function_count: ir_functions.len(),
        symbol_count: buffer.symbol_count(),
        allocated_bytes,
        code_len: proof.code_len,
        proof_allocation_len: proof.allocation_len,
        exact_symbol_match: proof.exact_symbol_match,
    })
}

fn request_callout_signature() -> trust_cg_codegen::jit_contract::SymbolSignature {
    extern_c_signature(vec![abi_ptr(), abi_ptr(), abi_ptr(), abi_i32()], Vec::new())
}

fn bind_request_callout(
    buffer: &ExecutableBuffer,
    opt_level: OptLevel,
) -> Result<RequestCalloutFn, String> {
    let signature = request_callout_signature();
    let manifest = ty_reducer_manifest(buffer, opt_level, REQUEST_SYMBOL, signature.clone());
    let contract = ty_reducer_lookup_contract(&manifest, REQUEST_SYMBOL, signature.clone());
    let typed = buffer
        .get_fixture_contract_symbol_bound::<RequestCalloutFn>(&manifest, &contract)
        .map_err(|err| format!("{REQUEST_SYMBOL} contract-bound lookup failed: {err}"))?;
    if typed.symbol() != REQUEST_SYMBOL || typed.signature() != &signature {
        return Err(format!(
            "{REQUEST_SYMBOL} contract lookup returned symbol={} signature={:?}",
            typed.symbol(),
            typed.signature()
        ));
    }
    Ok(unsafe { typed.into_fn() })
}

fn invoke_replay_bundle_jit(bundle: &ReplayBundle) -> Result<JitInvocationEvidence, String> {
    if bundle.callout.state_len > u64::from(u32::MAX) {
        return Err(format!(
            "callout state_len {} does not fit u32 ABI",
            bundle.callout.state_len
        ));
    }

    let replay_jit = compile_replay_trust_ir_to_jit(bundle)?;
    let entry = bind_request_callout(&replay_jit.buffer, bundle.metadata.opt_level)?;
    let state = bundle.callout.state_slots.clone();
    let mut state_out = bundle.callout.state_out_initial_slots.clone();
    let state_len = bundle.callout.state_len as u32;
    let mut out = JitCallOut::default();

    unsafe {
        entry(&mut out, state.as_ptr(), state_out.as_mut_ptr(), state_len);
    }

    Ok(JitInvocationEvidence {
        compile: replay_jit.evidence,
        out,
        state_out_slots: state_out,
    })
}

fn build_minimal_request_module() -> TrustIrModule {
    let mut mb = ModuleBuilder::new(REQUEST_SYMBOL);
    let request_ty = mb.add_func_type(vec![Ty::Ptr, Ty::Ptr, Ty::Ptr, Ty::U32], vec![]);
    let mut fb = mb.function(REQUEST_SYMBOL, request_ty);
    let entry = fb.create_block();
    fb.add_block_param(entry, Ty::Ptr);
    fb.add_block_param(entry, Ty::Ptr);
    fb.add_block_param(entry, Ty::Ptr);
    fb.add_block_param(entry, Ty::U32);
    fb.switch_to_block(entry);
    fb.ret(vec![]);
    fb.build();
    mb.build()
}

fn fixture_metadata_path(root: &Path) -> PathBuf {
    root.join("MCLamportMutex")
        .join("trust-cg-replay")
        .join("trust_ir-modules")
        .join(METADATA_NAME)
}

fn rewrite_fixture_metadata(root: &Path, update: fn(&mut Value)) -> Result<(), String> {
    let path = fixture_metadata_path(root);
    let bytes = fs::read(&path).map_err(|err| format!("read fixture metadata: {err}"))?;
    let mut metadata: Value =
        serde_json::from_slice(&bytes).map_err(|err| format!("parse fixture metadata: {err}"))?;
    update(&mut metadata);
    fs::write(
        &path,
        serde_json::to_string_pretty(&metadata)
            .map_err(|err| format!("serialize fixture metadata: {err}"))?,
    )
    .map_err(|err| format!("write fixture metadata: {err}"))
}

fn write_fixture_bundle(root: &Path) -> Result<(), String> {
    let replay_root = root.join("MCLamportMutex").join("trust-cg-replay");
    let trust_ir_dir = replay_root.join("trust_ir-modules");
    let callout_dir = replay_root.join("callouts");
    let crash_dir = replay_root.join("crash");
    fs::create_dir_all(&trust_ir_dir)
        .map_err(|err| format!("create {}: {err}", trust_ir_dir.display()))?;
    fs::create_dir_all(&callout_dir)
        .map_err(|err| format!("create {}: {err}", callout_dir.display()))?;
    fs::create_dir_all(&crash_dir)
        .map_err(|err| format!("create {}: {err}", crash_dir.display()))?;

    let trust_ir_json = serde_json::to_string_pretty(&build_minimal_request_module())
        .map_err(|err| format!("serialize fixture trust_ir: {err}"))?;
    fs::write(trust_ir_dir.join(TRUST_IR_JSON_NAME), trust_ir_json)
        .map_err(|err| format!("write fixture trust_ir JSON: {err}"))?;

    fs::write(
        trust_ir_dir.join(METADATA_NAME),
        serde_json::to_string_pretty(&json!({
            "schema": "ty.trust-cg.native_replay_trust_ir.v1",
            "sequence": 1,
            "stage": LINKED_STAGE,
            "module_name": REQUEST_SYMBOL,
            "module": {
                "function_count": 1,
                "global_count": 0,
                "type_count": 0,
                "bodyless_external_declarations": []
            },
            "opt_level": "O3",
            "target_triple": "aarch64-apple-darwin",
            "files": {
                "serde_json_trust_ir": TRUST_IR_JSON_NAME,
                "canonical_trust_ir": "000001-compile_module_native.linked-Request__1_1.trust_ir",
                "binary_trust_ir": "000001-compile_module_native.linked-Request__1_1.trust_irbin"
            },
            "jit_pc_map": {
                "available": true,
                "functions": [
                    {
                        "name": REQUEST_SYMBOL,
                        "runtime_start": "0x100000000",
                        "symbol_offset": "0x0",
                        "code_len": 4,
                        "blocks": [
                            {
                                "block": "bb0",
                                "offset": "0x0",
                                "pc": "0x100000000"
                            }
                        ]
                    }
                ]
            },
            "source_revisions": {
                "trust_cg_pipeline_version": "fixture-trust-cg-pipeline-version",
                "ty_git_commit": "fixture-ty-git-commit"
            }
        }))
        .map_err(|err| format!("serialize fixture metadata: {err}"))?,
    )
    .map_err(|err| format!("write fixture metadata: {err}"))?;

    fs::write(
        callout_dir.join("000001-action-0-Request__1_1.entering.json"),
        serde_json::to_string_pretty(&json!({
            "schema": "ty.trust-cg.native_callout_selftest.v1",
            "sequence": 1,
            "event": "entering",
            "kind": "action",
            "index": 0,
            "name": REQUEST_SYMBOL,
            "symbol_name": REQUEST_SYMBOL,
            "function_address": "0x100000000",
            "abi": {
                "signature": r#"extern "C" fn(*mut JitCallOut, *const i64, *mut i64, u32)"#,
                "state_len": 4
            },
            "state": {
                "head": [3, 0, 0, 0],
                "slots": [3, 0, 0, 0]
            },
            "state_out_initial": {
                "head": [3, 0, 0, 0],
                "slots": [3, 0, 0, 0]
            }
        }))
        .map_err(|err| format!("serialize fixture callout: {err}"))?,
    )
    .map_err(|err| format!("write fixture callout: {err}"))?;

    fs::write(
        crash_dir.join("pid-1-signal-10-fault-0x100000000.json"),
        serde_json::to_string_pretty(&json!({
            "schema": "ty.trust-cg.native_crash_packet.v1",
            "packet_path": "fixture",
            "jit": {
                "matched": true,
                "metadata_path": format!(
                    "{}/{}",
                    trust_ir_dir.strip_prefix(root).unwrap_or(&trust_ir_dir).display(),
                    METADATA_NAME
                ),
                "module_name": REQUEST_SYMBOL,
                "stage": LINKED_STAGE,
                "pc_map_offset": "0x0",
                "pc_map_offset_decimal": 0,
                "nearest_block": {
                    "block": "bb0",
                    "offset": "0x0",
                    "pc": "0x100000000"
                },
                "function": {
                    "name": REQUEST_SYMBOL,
                    "runtime_start": "0x100000000",
                    "symbol_offset": "0x0",
                    "code_len": 4,
                    "range": {
                        "start": "0x100000000",
                        "end": "0x100000004"
                    }
                }
            },
            "os_crash_report": {
                "fault_signal": "SIGBUS",
                "fault_signal_code": 10,
                "fault_pc": "0x100000000",
                "fault_pc_decimal": 4294967296_u64,
                "fault_address": "0x100000000",
                "fault_address_decimal": 4294967296_u64,
                "exception": {
                    "type": "EXC_BAD_ACCESS",
                    "subtype": "KERN_PROTECTION_FAILURE at 0x0000000100000000",
                    "signal": "SIGBUS"
                },
                "thread": {
                    "name": "ty-main",
                    "threadState": {
                        "esr": {
                            "description": "(Instruction Abort) Permission fault",
                            "value": 2181038095_u64
                        },
                        "far": {
                            "value": 4294967296_u64
                        },
                        "pc": {
                            "value": 4294967296_u64,
                            "matchesCrashFrame": 1
                        }
                    }
                },
                "vm_region_info": "0x100000000-0x100001000 [rw-/rwx]"
            }
        }))
        .map_err(|err| format!("serialize fixture crash: {err}"))?,
    )
    .map_err(|err| format!("write fixture crash: {err}"))?;

    Ok(())
}

fn make_temp_fixture_dir(name: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!(
        "trust_cg_{name}_{}_{}",
        std::process::id(),
        std::thread::current().name().unwrap_or("test")
    ));
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).expect("create fixture temp dir");
    dir
}

fn remove_source_revisions(metadata: &mut Value) {
    metadata
        .as_object_mut()
        .expect("fixture metadata object")
        .remove("source_revisions");
}

fn remove_trust_cg_pipeline_version(metadata: &mut Value) {
    metadata["source_revisions"]
        .as_object_mut()
        .expect("fixture source_revisions object")
        .remove("trust_cg_pipeline_version");
}

fn empty_trust_cg_pipeline_version(metadata: &mut Value) {
    metadata["source_revisions"]["trust_cg_pipeline_version"] = json!("");
}

fn blank_trust_cg_pipeline_version(metadata: &mut Value) {
    metadata["source_revisions"]["trust_cg_pipeline_version"] = json!(" \t\n ");
}

fn remove_ty_git_commit(metadata: &mut Value) {
    metadata["source_revisions"]
        .as_object_mut()
        .expect("fixture source_revisions object")
        .remove("ty_git_commit");
}

fn empty_ty_git_commit(metadata: &mut Value) {
    metadata["source_revisions"]["ty_git_commit"] = json!("");
}

fn blank_ty_git_commit(metadata: &mut Value) {
    metadata["source_revisions"]["ty_git_commit"] = json!(" \t\n ");
}

fn host_supports_aarch64_jit(test_name: &str) -> bool {
    if cfg!(target_arch = "aarch64") {
        true
    } else {
        eprintln!("skipping {test_name}: AArch64 host JIT is required");
        false
    }
}

#[test]
fn minimal_ty_request_replay_bundle_parses_and_compiles() {
    let root = make_temp_fixture_dir("ty_request_replay_bundle");
    write_fixture_bundle(&root).expect("write minimal TY replay fixture");
    let bundle = load_replay_bundle(&root).expect("minimal TY replay fixture should parse");
    let evidence =
        compile_replay_trust_ir(&bundle).expect("minimal replay trust_ir should compile");

    assert_eq!(bundle.metadata.module_name, REQUEST_SYMBOL);
    assert_eq!(bundle.metadata.target_triple, "aarch64-apple-darwin");
    assert_eq!(bundle.metadata.function_count, 1);
    assert_eq!(
        bundle.metadata.source_revisions.trust_cg_pipeline_version,
        "fixture-trust-cg-pipeline-version"
    );
    assert_eq!(
        bundle.metadata.source_revisions.ty_git_commit,
        "fixture-ty-git-commit"
    );
    assert_eq!(bundle.callout.kind, "action");
    assert_eq!(bundle.callout.index, 0);
    assert_eq!(bundle.callout.state_len, 4);
    assert_eq!(bundle.callout.state_head_len, 4);
    assert_eq!(bundle.callout.state_out_initial_head_len, 4);
    assert_eq!(bundle.callout.state_slots, vec![3, 0, 0, 0]);
    assert_eq!(bundle.callout.state_out_initial_slots, vec![3, 0, 0, 0]);
    assert_eq!(bundle.crash.fault_signal_code, Some(10));
    assert_eq!(bundle.crash.fault_address, Some(0x1_0000_0000));
    assert_eq!(bundle.crash.jit_range_start, Some(0x1_0000_0000));
    assert!(
        bundle
            .crash
            .metadata_path
            .contains("Request__1_1.metadata.json")
    );
    assert_eq!(evidence.function_count, 1);
    assert!(evidence.object_bytes > 0);

    let _ = fs::remove_dir_all(&root);
}

#[test]
#[allow(clippy::type_complexity)] // Cases bind one JSON mutation to its expected diagnostic.
fn ty_request_replay_bundle_rejects_missing_or_blank_source_revisions_before_replay() {
    let cases: &[(&str, fn(&mut Value), &str)] = &[
        (
            "missing_source_revisions",
            remove_source_revisions,
            "metadata missing non-empty source revision source_revisions.trust_cg_pipeline_version",
        ),
        (
            "missing_trust_cg_pipeline_version",
            remove_trust_cg_pipeline_version,
            "metadata missing non-empty source revision source_revisions.trust_cg_pipeline_version",
        ),
        (
            "empty_trust_cg_pipeline_version",
            empty_trust_cg_pipeline_version,
            "metadata missing non-empty source revision source_revisions.trust_cg_pipeline_version",
        ),
        (
            "blank_trust_cg_pipeline_version",
            blank_trust_cg_pipeline_version,
            "metadata missing non-empty source revision source_revisions.trust_cg_pipeline_version",
        ),
        (
            "missing_ty_git_commit",
            remove_ty_git_commit,
            "metadata missing non-empty source revision source_revisions.ty_git_commit",
        ),
        (
            "empty_ty_git_commit",
            empty_ty_git_commit,
            "metadata missing non-empty source revision source_revisions.ty_git_commit",
        ),
        (
            "blank_ty_git_commit",
            blank_ty_git_commit,
            "metadata missing non-empty source revision source_revisions.ty_git_commit",
        ),
    ];

    for (name, mutate_metadata, expected_error) in cases {
        let root = make_temp_fixture_dir(&format!(
            "ty_request_replay_bundle_bad_source_revisions_{name}"
        ));
        write_fixture_bundle(&root).expect("write minimal TY replay fixture");
        rewrite_fixture_metadata(&root, *mutate_metadata)
            .expect("rewrite minimal TY replay fixture metadata");

        let mut function_count_reads = 0;
        let mut compile_attempts = 0;
        let mut jit_attempts = 0;
        let result = load_replay_bundle(&root).map(|bundle| {
            function_count_reads += 1;
            let _ = bundle.metadata.function_count;
            compile_attempts += 1;
            let _ = compile_replay_trust_ir(&bundle);
            jit_attempts += 1;
            let _ = compile_replay_trust_ir_to_jit(&bundle);
        });
        let error = result.expect_err("bad source revisions must reject before replay");

        assert_eq!(error, *expected_error, "{name}");
        assert_eq!(function_count_reads, 0, "{name} counted a replay bundle");
        assert_eq!(compile_attempts, 0, "{name} attempted compile replay");
        assert_eq!(jit_attempts, 0, "{name} attempted JIT replay");

        let _ = fs::remove_dir_all(&root);
    }
}

#[test]
fn minimal_ty_request_replay_bundle_jit_invokes_through_contract_lookup() {
    if !host_supports_aarch64_jit("minimal fixture JIT invocation") {
        return;
    }

    let root = make_temp_fixture_dir("ty_request_replay_bundle_jit");
    write_fixture_bundle(&root).expect("write minimal TY replay fixture");
    let bundle = load_replay_bundle(&root).expect("minimal TY replay fixture should parse");
    let invocation =
        invoke_replay_bundle_jit(&bundle).expect("minimal replay trust_ir should JIT and invoke");

    assert_eq!(invocation.compile.function_count, 1);
    assert!(invocation.compile.instruction_count > 0);
    assert_eq!(invocation.compile.symbol_count, 1);
    assert!(invocation.compile.allocated_bytes > 0);
    assert_eq!(invocation.out, JitCallOut::default());
    assert_eq!(invocation.state_out_slots, vec![3, 0, 0, 0]);

    let _ = fs::remove_dir_all(&root);
}

#[test]
fn request_1_1_native_fused_evidence_cites_replay_and_gate_identities() {
    let signature = request_callout_signature();
    let identity = TyNativeFusedManifestIdentity::fixture(REQUEST_SYMBOL);
    let refs = TyNativeFusedEvidenceRefs::fixture(REQUEST_SYMBOL);
    let manifest = ty_native_fused_parent_loop_manifest_for_symbol_with_proof_policy(
        OptLevel::O3,
        REQUEST_SYMBOL,
        signature.clone(),
        0,
        64,
        4096,
        identity.clone(),
        ProofPolicy::require_certificates(["ty-native-fused-parent-loop", "trust-cg-verify"]),
    );
    let manifest_checksum = manifest.checksum();
    let manifest_checksum_text = manifest_checksum.to_string();
    let evidence = ty_native_fused_verified_evidence(&manifest, &refs);

    assert_eq!(
        manifest
            .metadata
            .get("native_fused_kernel_identity")
            .map(String::as_str),
        Some(REQUEST_SYMBOL)
    );
    assert_eq!(
        manifest.metadata.get("spec_source_lock_sha256"),
        Some(&identity.spec_source_lock_sha256)
    );
    assert_eq!(
        manifest.metadata.get("trust_ir_sha256"),
        Some(&identity.trust_ir_sha256)
    );
    assert_eq!(
        manifest.metadata.get("native_payload_sha256"),
        Some(&identity.native_payload_sha256)
    );
    assert_eq!(
        evidence
            .metadata
            .get("ty.native_fused.manifest_identity")
            .map(String::as_str),
        Some(manifest_checksum_text.as_str())
    );
    assert_eq!(
        evidence
            .metadata
            .get("ty.native_fused.certificate_identity"),
        Some(&refs.certificate_identity)
    );
    assert_eq!(
        evidence.metadata.get("ty.native_fused.replay_root_sha256"),
        Some(&refs.replay_root_sha256)
    );
    assert_eq!(
        evidence.metadata.get("ty.native_fused.telemetry_event_id"),
        Some(&refs.telemetry_event_id)
    );
    assert_eq!(
        evidence.metadata.get("ty.native_fused.gate_result_sha256"),
        Some(&refs.gate_result_sha256)
    );
    assert_eq!(
        evidence
            .metadata
            .get("ty.native_fused.proof_validation_sha256"),
        Some(&refs.proof_validation_sha256)
    );
    manifest
        .verify_proof_evidence(&evidence)
        .expect("Request__1_1 evidence should bind manifest checksums");

    let contract = ty_reducer_lookup_contract(&manifest, REQUEST_SYMBOL, signature)
        .with_proof_evidence(evidence);
    assert_eq!(contract.symbol, REQUEST_SYMBOL);
    assert_eq!(contract.manifest_checksum, Some(manifest_checksum));
    assert_eq!(
        contract.invalidation_checksum,
        Some(manifest.invalidation.checksum())
    );
    assert!(
        contract.proof_evidence.is_some(),
        "Request__1_1 contract should carry proof-consumption evidence"
    );
}

#[test]
fn request_1_1_release_bundle_binds_native_fused_replay_metadata() {
    let signature = request_callout_signature();
    let identity = TyNativeFusedManifestIdentity::fixture(REQUEST_SYMBOL);
    let refs = TyNativeFusedEvidenceRefs::fixture(REQUEST_SYMBOL);
    let manifest = ty_native_fused_parent_loop_manifest_for_symbol_with_proof_policy(
        OptLevel::O3,
        REQUEST_SYMBOL,
        signature,
        0,
        64,
        4096,
        identity,
        ProofPolicy::require_certificates(["ty-native-fused-parent-loop", "trust-cg-verify"]),
    );
    let manifest_checksum = manifest.checksum();
    let replay_metadata = ReleaseTyNativeFusedReplayMetadata {
        manifest_checksum,
        replay_root_sha256: refs.replay_root_sha256.clone(),
        replay_record_sha256: format!("sha256:{REQUEST_SYMBOL}:replay-record"),
        telemetry_event_id: refs.telemetry_event_id.clone(),
        telemetry_record_sha256: refs.gate_result_sha256.clone(),
        gate_packet_hash: ArtifactChecksum::new(0x680),
        proof_validation_sha256: refs.proof_validation_sha256.clone(),
    };
    let mut bundle = ReleaseReplayBundleMetadata::new(
        "ty",
        "native-fused-parent-loop",
        format!("{REQUEST_SYMBOL}-native-fused"),
        ReleaseArtifactManifestReference::new(
            "artifact.manifest.json",
            "sha256:artifact-manifest-json",
            1,
            manifest_checksum,
        ),
        ReleaseBundleFileReference::new("source-lock.json", "sha256:source-lock"),
        ReleaseProofReportReference::new("proofs/request-1-1.json", &refs.proof_validation_sha256)
            .with_policy("ty-native-fused-parent-loop")
            .with_verdict("accepted")
            .with_solver("trust-cg-verify")
            .with_obligation_set("ty-native-fused-parent-loop")
            .with_timeout_ms(500),
        ReleaseBundleFileReference::new("telemetry/ty.json", "sha256:telemetry-file"),
        ReleaseBundleFileReference::new("release/package.json", "sha256:release-package"),
        ReleaseBundleFileReference::new("replay/request-1-1.json", "sha256:replay-bundle"),
        ReleaseBundleFileReference::new("gate-results.json", &refs.gate_result_sha256),
    );
    replay_metadata.bind_into_metadata(&mut bundle.metadata);

    let json = bundle.to_json_value();
    assert!(
        json.get("ty_native_fused_replay").is_none(),
        "TY replay/release metadata must stay in the extension metadata map"
    );
    let metadata = json["metadata"]
        .as_object()
        .expect("Request__1_1 release metadata");
    assert_eq!(
        metadata
            .get(RELEASE_TY_NATIVE_FUSED_REPLAY_SCHEMA_KEY)
            .and_then(Value::as_str),
        Some(RELEASE_TY_NATIVE_FUSED_REPLAY_SCHEMA)
    );
    assert_eq!(
        metadata
            .get(RELEASE_TY_NATIVE_FUSED_REPLAY_SCHEMA_VERSION_KEY)
            .and_then(Value::as_str),
        Some("1")
    );
    assert_eq!(
        metadata
            .get(RELEASE_TY_NATIVE_FUSED_REPLAY_MANIFEST_CHECKSUM_KEY)
            .and_then(Value::as_str)
            .expect("manifest checksum metadata"),
        manifest_checksum.to_string()
    );
    assert_eq!(
        metadata
            .get(RELEASE_TY_NATIVE_FUSED_REPLAY_ROOT_SHA256_KEY)
            .and_then(Value::as_str),
        Some(refs.replay_root_sha256.as_str())
    );
    assert_eq!(
        metadata
            .get(RELEASE_TY_NATIVE_FUSED_REPLAY_RECORD_SHA256_KEY)
            .and_then(Value::as_str),
        Some(replay_metadata.replay_record_sha256.as_str())
    );
    assert_eq!(
        metadata
            .get(RELEASE_TY_NATIVE_FUSED_REPLAY_TELEMETRY_EVENT_ID_KEY)
            .and_then(Value::as_str),
        Some(refs.telemetry_event_id.as_str())
    );
    assert_eq!(
        metadata
            .get(RELEASE_TY_NATIVE_FUSED_REPLAY_TELEMETRY_RECORD_SHA256_KEY)
            .and_then(Value::as_str),
        Some(refs.gate_result_sha256.as_str())
    );
    assert_eq!(
        metadata
            .get(RELEASE_TY_NATIVE_FUSED_REPLAY_GATE_PACKET_HASH_KEY)
            .and_then(Value::as_str)
            .expect("gate packet hash metadata"),
        replay_metadata.gate_packet_hash.to_string()
    );
    assert_eq!(
        metadata
            .get(RELEASE_TY_NATIVE_FUSED_REPLAY_PROOF_VALIDATION_SHA256_KEY)
            .and_then(Value::as_str),
        Some(refs.proof_validation_sha256.as_str())
    );

    let baseline_checksum = bundle.checksum();
    let mut changed = bundle.clone();
    changed.metadata.insert(
        RELEASE_TY_NATIVE_FUSED_REPLAY_PROOF_VALIDATION_SHA256_KEY.to_owned(),
        "sha256:changed-proof-validation".to_owned(),
    );
    assert_ne!(baseline_checksum, changed.checksum());
}

#[test]
fn env_ty_request_replay_bundle_parses_and_compiles_when_present() {
    let Some(root) = std::env::var_os(BUNDLE_ENV).map(PathBuf::from) else {
        eprintln!("skipping real TY replay bundle reducer: {BUNDLE_ENV} is not set");
        return;
    };
    let bundle = load_replay_bundle(&root)
        .unwrap_or_else(|err| panic!("failed to parse TY replay bundle {}: {err}", root.display()));
    let evidence = compile_replay_trust_ir(&bundle).unwrap_or_else(|err| {
        panic!(
            "failed to compile TY replay bundle {}: {err}",
            root.display()
        )
    });

    assert_eq!(bundle.root, root);
    assert_eq!(bundle.metadata.module_name, REQUEST_SYMBOL);
    assert_eq!(bundle.metadata.opt_level, OptLevel::O3);
    assert_eq!(bundle.metadata.target, Target::Aarch64);
    assert_eq!(bundle.metadata.stage, LINKED_STAGE);
    assert_eq!(bundle.crash.pc_map_offset, Some(0));
    assert_eq!(bundle.callout.function_address, bundle.crash.fault_pc);
    assert_eq!(bundle.metadata.entry_pc, bundle.crash.fault_pc);
    assert_eq!(bundle.callout.state_slots.len(), 89);
    assert_eq!(bundle.callout.state_out_initial_slots.len(), 89);
    assert_eq!(
        bundle.callout.state_slots.len() as u64,
        bundle.callout.state_len
    );
    assert_eq!(
        bundle.callout.state_out_initial_slots.len() as u64,
        bundle.callout.state_len
    );
    assert_eq!(
        evidence.function_count as u64,
        bundle.metadata.function_count
    );
    assert!(evidence.object_bytes > 0);
    assert!(evidence.instruction_count > 0);

    eprintln!(
        "compiled {} from {}: {} functions, {} instructions, {} object bytes",
        bundle.trust_ir_json_path.display(),
        bundle.metadata_path.display(),
        evidence.function_count,
        evidence.instruction_count,
        evidence.object_bytes
    );
    eprintln!(
        "callout={} crash={}",
        bundle.callout_path.display(),
        bundle.crash_path.display()
    );
}

#[test]
fn env_ty_request_replay_bundle_low_level_compile_raw_alloc_size_matches_proof_when_present() {
    let Some(root) = std::env::var_os(BUNDLE_ENV).map(PathBuf::from) else {
        eprintln!("skipping real TY low-level replay bundle reducer: {BUNDLE_ENV} is not set");
        return;
    };
    if !host_supports_aarch64_jit("env replay bundle low-level compile_raw") {
        return;
    }

    let artifact = load_replay_trust_ir_artifact(&root).unwrap_or_else(|err| {
        panic!(
            "failed to parse TY replay trust_ir artifact {}: {err}",
            root.display()
        )
    });
    let evidence = compile_replay_trust_ir_through_low_level_jit(&artifact).unwrap_or_else(|err| {
        panic!(
            "failed low-level compile_raw for TY replay bundle {}: {err}",
            root.display()
        )
    });

    assert_eq!(artifact.root, root);
    assert_eq!(artifact.metadata.module_name, REQUEST_SYMBOL);
    assert_eq!(artifact.metadata.target, Target::Aarch64);
    assert_eq!(artifact.metadata.stage, LINKED_STAGE);
    assert_eq!(
        evidence.function_count as u64,
        artifact.metadata.function_count
    );
    assert!(evidence.function_count > 0);
    assert!(evidence.symbol_count > 0);
    assert!(
        evidence.allocated_bytes > 0,
        "low-level compile_raw published a zero-size executable buffer"
    );
    assert_eq!(
        evidence.proof_allocation_len, evidence.allocated_bytes,
        "publication proof allocation_len must match public allocated_size"
    );
    assert!(
        evidence.code_len > 0,
        "low-level compile_raw should publish nonempty code"
    );
    assert!(
        evidence.code_len <= evidence.proof_allocation_len,
        "publication proof code_len must fit allocation_len"
    );
    assert!(
        evidence.exact_symbol_match,
        "publication proof should diagnose the exact {REQUEST_SYMBOL} symbol"
    );

    eprintln!(
        "low-level compile_raw {} from {}: {} functions, {} symbols, code_len={}, allocated_size={}, proof_allocation_len={}",
        artifact.trust_ir_json_path.display(),
        artifact.metadata_path.display(),
        evidence.function_count,
        evidence.symbol_count,
        evidence.code_len,
        evidence.allocated_bytes,
        evidence.proof_allocation_len
    );
}

#[test]
fn env_ty_request_replay_bundle_jit_invokes_in_child_when_present() {
    let Some(root) = std::env::var_os(BUNDLE_ENV).map(PathBuf::from) else {
        eprintln!("skipping real TY replay bundle JIT invocation: {BUNDLE_ENV} is not set");
        return;
    };
    if !host_supports_aarch64_jit("env replay bundle JIT invocation") {
        return;
    }

    if std::env::var_os(INVOKE_CHILD_ENV).is_some() {
        let bundle = load_replay_bundle(&root).unwrap_or_else(|err| {
            panic!("failed to parse TY replay bundle {}: {err}", root.display())
        });
        let invocation = invoke_replay_bundle_jit(&bundle).unwrap_or_else(|err| {
            panic!(
                "failed to JIT invoke TY replay bundle {}: {err}",
                root.display()
            )
        });

        assert_eq!(
            invocation.out.status, JIT_STATUS_OK,
            "action callout should return Ok: out={:?}",
            invocation.out
        );
        assert!(
            matches!(invocation.out.value, 0 | 1),
            "action callout should return a canonical boolean: out={:?}",
            invocation.out
        );
        assert_eq!(
            invocation.state_out_slots.len() as u64,
            bundle.callout.state_len
        );
        eprintln!(
            "jit-invoked {} from {}: {} functions, {} instructions, {} symbols, {} bytes, status={}, value={}, state_out_head={:?}",
            REQUEST_SYMBOL,
            bundle.trust_ir_json_path.display(),
            invocation.compile.function_count,
            invocation.compile.instruction_count,
            invocation.compile.symbol_count,
            invocation.compile.allocated_bytes,
            invocation.out.status,
            invocation.out.value,
            &invocation.state_out_slots[..invocation.state_out_slots.len().min(16)]
        );
        return;
    }

    let current_exe = std::env::current_exe().expect("current test binary");
    let output = Command::new(current_exe)
        .arg(ENV_INVOKE_TEST_NAME)
        .arg("--exact")
        .arg("--nocapture")
        .env(BUNDLE_ENV, root.as_os_str())
        .env(INVOKE_CHILD_ENV, "1")
        .output()
        .expect("run TY replay bundle JIT invocation child");

    assert!(
        output.status.success(),
        "replay bundle JIT child should execute without entry-PC SIGBUS; status={:?}\nstdout:\n{}\nstderr:\n{}",
        output.status,
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );

    eprintln!("{}", String::from_utf8_lossy(&output.stdout));
    eprintln!("{}", String::from_utf8_lossy(&output.stderr));
}
