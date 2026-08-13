// trust-cg-codegen/jit_diagnostics.rs - JIT diagnostic replay metadata
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Data model for replayable JIT diagnostics.
//!
//! This module is intentionally independent from the executable-buffer
//! implementation so frontends such as ty and ay can start emitting stable
//! replay artifacts before every runtime hook is available.

use std::{collections::BTreeMap, fmt};

use serde_json::{Value, json};
use sha2::{Digest, Sha256};

use crate::pipeline::ProofOptimizationCertificateCitation;

/// Stable schema tag for JIT replay metadata emitted by this crate.
pub const JIT_REPLAY_SCHEMA: &str = "trust-cg.codegen.jit_replay.v1";

/// Stable numeric schema version for [`JitReplayReportMetadata`].
pub const JIT_REPLAY_SCHEMA_VERSION: u32 = 1;

/// Stable schema tag for issue-ready JIT crash reports emitted by this crate.
pub const JIT_CRASH_REPORT_SCHEMA: &str = "trust-cg.codegen.jit_crash_report.v1";

/// Stable numeric schema version for [`JitCrashReportMetadata`].
pub const JIT_CRASH_REPORT_SCHEMA_VERSION: u32 = 1;

/// Return lowercase hex SHA-256 for native payload identity fields.
pub fn sha256_hex(bytes: &[u8]) -> String {
    let digest = Sha256::digest(bytes);
    let mut output = String::with_capacity(digest.len() * 2);
    for byte in digest {
        output.push(hex_nibble(byte >> 4));
        output.push(hex_nibble(byte & 0x0f));
    }
    output
}

const fn hex_nibble(nibble: u8) -> char {
    match nibble {
        0 => '0',
        1 => '1',
        2 => '2',
        3 => '3',
        4 => '4',
        5 => '5',
        6 => '6',
        7 => '7',
        8 => '8',
        9 => '9',
        10 => 'a',
        11 => 'b',
        12 => 'c',
        13 => 'd',
        14 => 'e',
        15 => 'f',
        _ => '?',
    }
}

/// Half-open byte range in an executable JIT artifact.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct JitCodeRange {
    /// Start offset from the beginning of the JIT code artifact.
    pub start_offset: u64,
    /// End offset from the beginning of the JIT code artifact.
    pub end_offset: u64,
}

impl JitCodeRange {
    /// Build a half-open code range `[start_offset, end_offset)`.
    pub const fn new(start_offset: u64, end_offset: u64) -> Self {
        Self {
            start_offset,
            end_offset,
        }
    }

    /// Return true when the range is ordered.
    pub const fn is_valid(&self) -> bool {
        self.start_offset <= self.end_offset
    }

    /// Byte length of the range. Invalid ranges report zero length.
    pub const fn byte_len(&self) -> u64 {
        self.end_offset.saturating_sub(self.start_offset)
    }

    /// Return true when `offset` is in the half-open range.
    pub const fn contains(&self, offset: u64) -> bool {
        self.start_offset <= offset && offset < self.end_offset
    }

    /// Convert to the stable replay JSON representation.
    pub fn to_json_value(&self) -> Value {
        json!({
            "byte_len": self.byte_len(),
            "end_offset": self.end_offset,
            "start_offset": self.start_offset,
            "valid": self.is_valid(),
        })
    }
}

/// Label for a symbol's byte range inside a JIT code artifact.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct JitSymbolLabel {
    /// Canonical symbol name accepted by the JIT caller.
    pub name: String,
    /// Symbol byte range in the executable artifact.
    pub range: JitCodeRange,
    /// Additional lookup names that resolve to the same code range.
    pub aliases: Vec<String>,
}

impl JitSymbolLabel {
    /// Build a symbol label without aliases.
    pub fn new(name: impl Into<String>, range: JitCodeRange) -> Self {
        Self {
            name: name.into(),
            range,
            aliases: Vec::new(),
        }
    }

    /// Attach aliases, sorted and deduplicated for deterministic artifacts.
    pub fn with_aliases<I, S>(mut self, aliases: I) -> Self
    where
        I: IntoIterator<Item = S>,
        S: Into<String>,
    {
        self.aliases = aliases.into_iter().map(Into::into).collect();
        self.aliases.sort();
        self.aliases.dedup();
        self
    }

    fn canonicalized(&self) -> Self {
        let mut label = self.clone();
        label.aliases.sort();
        label.aliases.dedup();
        label
    }

    /// Convert to the stable replay JSON representation.
    pub fn to_json_value(&self) -> Value {
        let label = self.canonicalized();
        json!({
            "aliases": label.aliases,
            "name": label.name,
            "range": label.range.to_json_value(),
        })
    }
}

/// Mapping from a code offset to frontend/proof provenance.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct JitPcMapEntry {
    /// Offset from the beginning of the JIT code artifact.
    pub pc_offset: u64,
    /// Canonical symbol containing `pc_offset`.
    pub symbol: String,
    /// Offset from the beginning of `symbol`.
    pub symbol_offset: u64,
    /// Optional machine-instruction index within the lowered function.
    pub machine_inst_index: Option<u32>,
    /// Optional frontend label such as a TY state-transition label.
    pub source_label: Option<String>,
    /// Optional trust_ir operation/proof-family label.
    pub trust_ir_op: Option<String>,
}

impl JitPcMapEntry {
    /// Build a PC map entry with no optional provenance labels.
    pub fn new(pc_offset: u64, symbol: impl Into<String>, symbol_offset: u64) -> Self {
        Self {
            pc_offset,
            symbol: symbol.into(),
            symbol_offset,
            machine_inst_index: None,
            source_label: None,
            trust_ir_op: None,
        }
    }

    /// Attach the machine-instruction index for this PC row.
    pub const fn with_machine_inst_index(mut self, machine_inst_index: u32) -> Self {
        self.machine_inst_index = Some(machine_inst_index);
        self
    }

    /// Attach a frontend source label for this PC row.
    pub fn with_source_label(mut self, source_label: impl Into<String>) -> Self {
        self.source_label = Some(source_label.into());
        self
    }

    /// Attach a trust_ir operation/proof-family label for this PC row.
    pub fn with_trust_ir_op(mut self, trust_ir_op: impl Into<String>) -> Self {
        self.trust_ir_op = Some(trust_ir_op.into());
        self
    }

    /// Convert to the stable replay JSON representation.
    pub fn to_json_value(&self) -> Value {
        json!({
            "machine_inst_index": self.machine_inst_index,
            "pc_offset": self.pc_offset,
            "source_label": self.source_label,
            "symbol": self.symbol,
            "symbol_offset": self.symbol_offset,
            "trust_ir_op": self.trust_ir_op,
        })
    }
}

/// Stable status/trap classification for replay artifacts.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum JitTrapStatusKind {
    /// Native execution returned normally.
    Ok,
    /// The verifier rejected the artifact before execution.
    VerifierRejected,
    /// Replay completed but disagreed with recorded evidence.
    ReplayMismatch,
    /// Native execution hit a target-level trap instruction or fault block.
    NativeTrap,
    /// The host surfaced a signal/exception while running JIT code.
    HostSignal,
    /// Rust or caller-side panic during compilation or replay.
    Panic,
    /// Compilation, verification, or replay exceeded its deadline.
    Timeout,
    /// Internal compiler/runtime diagnostic failure.
    InternalError,
    /// Status source did not provide a more specific classification.
    Unknown,
}

impl JitTrapStatusKind {
    /// Stable snake-case name used in JSON replay artifacts.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Ok => "ok",
            Self::VerifierRejected => "verifier_rejected",
            Self::ReplayMismatch => "replay_mismatch",
            Self::NativeTrap => "native_trap",
            Self::HostSignal => "host_signal",
            Self::Panic => "panic",
            Self::Timeout => "timeout",
            Self::InternalError => "internal_error",
            Self::Unknown => "unknown",
        }
    }
}

impl fmt::Display for JitTrapStatusKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

/// Stable issue-facing classification for a JIT crash report.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum JitCrashKind {
    /// Native execution hit a target-level trap instruction or fault block.
    NativeTrap,
    /// The host surfaced a signal/exception while running JIT code.
    HostSignal,
    /// Rust or caller-side panic during compilation or replay.
    Panic,
    /// Crash source did not provide a more specific classification.
    Unknown,
}

impl JitCrashKind {
    /// Stable snake-case name used in JSON crash artifacts.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::NativeTrap => "native_trap",
            Self::HostSignal => "host_signal",
            Self::Panic => "panic",
            Self::Unknown => "unknown",
        }
    }

    /// Convert the crash kind into the nearest replay status classification.
    pub const fn status_kind(self) -> JitTrapStatusKind {
        match self {
            Self::NativeTrap => JitTrapStatusKind::NativeTrap,
            Self::HostSignal => JitTrapStatusKind::HostSignal,
            Self::Panic => JitTrapStatusKind::Panic,
            Self::Unknown => JitTrapStatusKind::Unknown,
        }
    }
}

impl fmt::Display for JitCrashKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

/// Resolved crash location inside a JIT replay artifact.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct JitCrashLocation {
    /// Optional host/native PC captured by the crash handler.
    pub host_pc: Option<u64>,
    /// Optional offset from the beginning of the JIT code artifact.
    pub code_offset: Option<u64>,
    /// Resolved canonical symbol, when `code_offset` falls in a known range.
    pub symbol: Option<String>,
    /// Offset from the beginning of the resolved symbol.
    pub symbol_offset: Option<u64>,
    /// Resolved symbol range, when available.
    pub symbol_range: Option<JitCodeRange>,
    /// Nearest PC-map entry at or before `code_offset`, when available.
    pub pc_map_entry: Option<JitPcMapEntry>,
    /// Stable diagnostic codes for missing or incomplete location data.
    pub diagnostics: Vec<String>,
}

impl JitCrashLocation {
    /// Build an unresolved crash location.
    pub fn new(host_pc: Option<u64>, code_offset: Option<u64>) -> Self {
        Self {
            host_pc,
            code_offset,
            symbol: None,
            symbol_offset: None,
            symbol_range: None,
            pc_map_entry: None,
            diagnostics: Vec::new(),
        }
    }

    /// Resolve `code_offset` against replay symbol ranges and PC-map entries.
    pub fn resolve(
        replay_metadata: &JitReplayReportMetadata,
        host_pc: Option<u64>,
        code_offset: Option<u64>,
    ) -> Self {
        let mut location = Self::new(host_pc, code_offset);
        let Some(code_offset) = code_offset else {
            location.diagnostics.push("missing_code_offset".to_string());
            return location;
        };

        let report = replay_metadata.canonicalized();
        let matching_symbol = report
            .symbols
            .iter()
            .find(|symbol| symbol.range.contains(code_offset));

        if let Some(symbol) = matching_symbol {
            location.symbol = Some(symbol.name.clone());
            location.symbol_offset = Some(code_offset - symbol.range.start_offset);
            location.symbol_range = Some(symbol.range.clone());
        } else {
            location
                .diagnostics
                .push("missing_symbol_for_code_offset".to_string());
        }

        location.pc_map_entry = report
            .pc_map
            .iter()
            .filter(|entry| entry.pc_offset <= code_offset)
            .rev()
            .find(|entry| {
                matching_symbol
                    .map(|symbol| entry.symbol == symbol.name)
                    .unwrap_or(true)
            })
            .cloned();

        if location.pc_map_entry.is_none() {
            location
                .diagnostics
                .push("missing_pc_map_entry_for_code_offset".to_string());
        }

        location.diagnostics.sort();
        location.diagnostics.dedup();
        location
    }

    /// Convert to the stable crash JSON representation.
    pub fn to_json_value(&self) -> Value {
        json!({
            "code_offset": self.code_offset,
            "diagnostics": self.diagnostics,
            "host_pc": self.host_pc,
            "pc_map_entry": self.pc_map_entry.as_ref().map(JitPcMapEntry::to_json_value),
            "symbol": self.symbol,
            "symbol_offset": self.symbol_offset,
            "symbol_range": self.symbol_range.as_ref().map(JitCodeRange::to_json_value),
        })
    }
}

/// One ordered status/trap observation in a replay report.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct JitTrapStatusBlock {
    /// Caller-provided sequence number. Reports sort by this field.
    pub sequence: u64,
    /// Stable status/trap classification.
    pub kind: JitTrapStatusKind,
    /// Pipeline stage or replay phase that emitted this status.
    pub stage: String,
    /// Optional PC offset associated with the status.
    pub pc_offset: Option<u64>,
    /// Optional symbol associated with the status.
    pub symbol: Option<String>,
    /// Optional human-readable detail.
    pub message: Option<String>,
}

impl JitTrapStatusBlock {
    /// Build a status block without optional location/message detail.
    pub fn new(sequence: u64, kind: JitTrapStatusKind, stage: impl Into<String>) -> Self {
        Self {
            sequence,
            kind,
            stage: stage.into(),
            pc_offset: None,
            symbol: None,
            message: None,
        }
    }

    /// Attach a PC offset for this status.
    pub const fn with_pc_offset(mut self, pc_offset: u64) -> Self {
        self.pc_offset = Some(pc_offset);
        self
    }

    /// Attach a symbol name for this status.
    pub fn with_symbol(mut self, symbol: impl Into<String>) -> Self {
        self.symbol = Some(symbol.into());
        self
    }

    /// Attach human-readable status detail.
    pub fn with_message(mut self, message: impl Into<String>) -> Self {
        self.message = Some(message.into());
        self
    }

    /// Convert to the stable replay JSON representation.
    pub fn to_json_value(&self) -> Value {
        json!({
            "kind": self.kind.as_str(),
            "message": self.message,
            "pc_offset": self.pc_offset,
            "sequence": self.sequence,
            "stage": self.stage,
            "symbol": self.symbol,
        })
    }
}

/// Top-level replay artifact metadata for JIT crashes and verifier failures.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct JitReplayReportMetadata {
    /// Stable schema tag.
    pub schema: String,
    /// Stable numeric schema version.
    pub schema_version: u32,
    /// Producer name for the report.
    pub producer: String,
    /// Optional stable artifact/content identity.
    pub artifact_id: Option<String>,
    /// Optional target triple or host target description.
    pub target: Option<String>,
    /// Optional entry symbol requested by the frontend.
    pub entry_symbol: Option<String>,
    /// Total executable code size in bytes when known.
    pub code_size: u64,
    /// Deterministic extra metadata for frontend-specific replay keys.
    pub properties: BTreeMap<String, String>,
    /// Symbol labels attached to the artifact.
    pub symbols: Vec<JitSymbolLabel>,
    /// PC map entries attached to the artifact.
    pub pc_map: Vec<JitPcMapEntry>,
    /// Status/trap observations attached to the artifact.
    pub statuses: Vec<JitTrapStatusBlock>,
    /// Proof-optimization certificates cited by this replay artifact.
    pub proof_optimization_certificates: Vec<ProofOptimizationCertificateCitation>,
}

impl Default for JitReplayReportMetadata {
    fn default() -> Self {
        Self {
            schema: JIT_REPLAY_SCHEMA.to_string(),
            schema_version: JIT_REPLAY_SCHEMA_VERSION,
            producer: "trust-cg-codegen".to_string(),
            artifact_id: None,
            target: None,
            entry_symbol: None,
            code_size: 0,
            properties: BTreeMap::new(),
            symbols: Vec::new(),
            pc_map: Vec::new(),
            statuses: Vec::new(),
            proof_optimization_certificates: Vec::new(),
        }
    }
}

impl JitReplayReportMetadata {
    /// Build a replay metadata report with a known code size.
    pub fn new(code_size: u64) -> Self {
        Self {
            code_size,
            ..Self::default()
        }
    }

    /// Build a replay metadata report from explicit `(symbol, offset, size)`
    /// entries.
    ///
    /// This is the metadata-only bridge for callers that already captured the
    /// JIT layout. `ExecutableBuffer` exposes symbol offsets publicly, but not
    /// exact function byte sizes for the normal verify-off path, so callers
    /// should pass sizes from their compile-time layout metadata instead of
    /// deriving them from the executable allocation size.
    pub fn from_symbol_entries<I, S>(symbol_entries: I) -> Self
    where
        I: IntoIterator<Item = (S, u64, u64)>,
        S: Into<String>,
    {
        let mut report = Self::default();

        for (symbol, offset, size) in symbol_entries {
            let symbol = symbol.into();
            let end_offset = offset.saturating_add(size);
            report.code_size = report.code_size.max(end_offset);
            report
                .pc_map
                .push(JitPcMapEntry::new(offset, symbol.clone(), 0));
            report.symbols.push(JitSymbolLabel::new(
                symbol,
                JitCodeRange::new(offset, end_offset),
            ));
        }

        report
    }

    /// Return a clone with all unordered collections in canonical order.
    pub fn canonicalized(&self) -> Self {
        let mut report = self.clone();

        report.symbols = report
            .symbols
            .iter()
            .map(JitSymbolLabel::canonicalized)
            .collect();
        report.symbols.sort_by(|left, right| {
            (
                left.range.start_offset,
                left.range.end_offset,
                left.name.as_str(),
            )
                .cmp(&(
                    right.range.start_offset,
                    right.range.end_offset,
                    right.name.as_str(),
                ))
        });

        report.pc_map.sort_by(|left, right| {
            (
                left.pc_offset,
                left.symbol.as_str(),
                left.symbol_offset,
                left.machine_inst_index,
                left.source_label.as_deref(),
                left.trust_ir_op.as_deref(),
            )
                .cmp(&(
                    right.pc_offset,
                    right.symbol.as_str(),
                    right.symbol_offset,
                    right.machine_inst_index,
                    right.source_label.as_deref(),
                    right.trust_ir_op.as_deref(),
                ))
        });

        report.statuses.sort_by(|left, right| {
            (
                left.sequence,
                left.kind.as_str(),
                left.stage.as_str(),
                left.symbol.as_deref(),
                left.pc_offset,
                left.message.as_deref(),
            )
                .cmp(&(
                    right.sequence,
                    right.kind.as_str(),
                    right.stage.as_str(),
                    right.symbol.as_deref(),
                    right.pc_offset,
                    right.message.as_deref(),
                ))
        });
        report
            .proof_optimization_certificates
            .sort_by(|left, right| {
                (
                    left.function_name.as_str(),
                    left.certificate_id.as_str(),
                    left.proof_hash.as_str(),
                    left.validation_hash.as_str(),
                )
                    .cmp(&(
                        right.function_name.as_str(),
                        right.certificate_id.as_str(),
                        right.proof_hash.as_str(),
                        right.validation_hash.as_str(),
                    ))
            });

        report
    }

    /// Convert to the stable replay JSON representation.
    pub fn to_json_value(&self) -> Value {
        let report = self.canonicalized();
        let symbols: Vec<_> = report
            .symbols
            .iter()
            .map(JitSymbolLabel::to_json_value)
            .collect();
        let pc_map: Vec<_> = report
            .pc_map
            .iter()
            .map(JitPcMapEntry::to_json_value)
            .collect();
        let statuses: Vec<_> = report
            .statuses
            .iter()
            .map(JitTrapStatusBlock::to_json_value)
            .collect();
        let proof_optimization_certificates: Vec<_> = report
            .proof_optimization_certificates
            .iter()
            .map(ProofOptimizationCertificateCitation::to_json_value)
            .collect();

        json!({
            "artifact_id": report.artifact_id,
            "code_size": report.code_size,
            "entry_symbol": report.entry_symbol,
            "pc_map": pc_map,
            "producer": report.producer,
            "proof_optimization_certificates": proof_optimization_certificates,
            "properties": report.properties,
            "schema": report.schema,
            "schema_version": report.schema_version,
            "statuses": statuses,
            "symbols": symbols,
            "target": report.target,
        })
    }

    /// Convert to deterministic pretty JSON with a trailing newline.
    pub fn to_pretty_json(&self) -> String {
        let mut output = serde_json::to_string_pretty(&self.to_json_value())
            .expect("serializing serde_json::Value should not fail");
        output.push('\n');
        output
    }
}

/// Top-level issue-ready crash packet for JIT native/runtime failures.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct JitCrashReportMetadata {
    /// Stable schema tag.
    pub schema: String,
    /// Stable numeric schema version.
    pub schema_version: u32,
    /// Producer name for the report.
    pub producer: String,
    /// Stable crash classification.
    pub kind: JitCrashKind,
    /// Pipeline/runtime component that observed the crash.
    pub component: String,
    /// Pipeline stage or replay phase that observed the crash.
    pub stage: String,
    /// Optional human-readable crash message.
    pub message: Option<String>,
    /// Optional host signal name or number.
    pub signal: Option<String>,
    /// Optional panic payload or panic summary.
    pub panic: Option<String>,
    /// Resolved crash location inside the replay artifact.
    pub location: JitCrashLocation,
    /// Embedded replay metadata with issue-routing identity properties.
    pub replay_metadata: JitReplayReportMetadata,
    /// Deterministic extra metadata for crash consumers.
    pub properties: BTreeMap<String, String>,
}

impl JitCrashReportMetadata {
    /// Build a crash packet and resolve the optional code offset immediately.
    pub fn new(
        kind: JitCrashKind,
        component: impl Into<String>,
        stage: impl Into<String>,
        replay_metadata: JitReplayReportMetadata,
    ) -> Self {
        Self {
            schema: JIT_CRASH_REPORT_SCHEMA.to_string(),
            schema_version: JIT_CRASH_REPORT_SCHEMA_VERSION,
            producer: "trust-cg-codegen".to_string(),
            kind,
            component: component.into(),
            stage: stage.into(),
            message: None,
            signal: None,
            panic: None,
            location: JitCrashLocation::resolve(&replay_metadata, None, None),
            replay_metadata,
            properties: BTreeMap::new(),
        }
    }

    /// Attach a host/native PC and JIT code offset, resolving symbol metadata.
    pub fn with_location(mut self, host_pc: Option<u64>, code_offset: Option<u64>) -> Self {
        self.location = JitCrashLocation::resolve(&self.replay_metadata, host_pc, code_offset);
        self
    }

    /// Attach human-readable crash detail.
    pub fn with_message(mut self, message: impl Into<String>) -> Self {
        self.message = Some(message.into());
        self
    }

    /// Attach host signal detail.
    pub fn with_signal(mut self, signal: impl Into<String>) -> Self {
        self.signal = Some(signal.into());
        self
    }

    /// Attach panic detail.
    pub fn with_panic(mut self, panic: impl Into<String>) -> Self {
        self.panic = Some(panic.into());
        self
    }

    /// Return a clone with all unordered collections in canonical order.
    pub fn canonicalized(&self) -> Self {
        let mut report = self.clone();
        report.replay_metadata = report.replay_metadata.canonicalized();
        report.location.diagnostics.sort();
        report.location.diagnostics.dedup();
        report
    }

    /// Convert to the stable crash JSON representation.
    pub fn to_json_value(&self) -> Value {
        let report = self.canonicalized();

        json!({
            "component": report.component,
            "kind": report.kind.as_str(),
            "location": report.location.to_json_value(),
            "message": report.message,
            "panic": report.panic,
            "producer": report.producer,
            "properties": report.properties,
            "replay_metadata": report.replay_metadata.to_json_value(),
            "schema": report.schema,
            "schema_version": report.schema_version,
            "signal": report.signal,
            "stage": report.stage,
            "status": report.kind.status_kind().as_str(),
        })
    }

    /// Convert to deterministic pretty JSON with a trailing newline.
    pub fn to_pretty_json(&self) -> String {
        let mut output = serde_json::to_string_pretty(&self.to_json_value())
            .expect("serializing serde_json::Value should not fail");
        output.push('\n');
        output
    }
}
