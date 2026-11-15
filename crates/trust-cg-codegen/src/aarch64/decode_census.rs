//! ENC-5 emission census: a diagnostic record of which AArch64 opcode forms
//! the backend emits and what the independent decode-check concluded for each.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache-2.0
//!
//! With `TCG_DECODE_CHECK_CENSUS_DIR=<dir>` set in the process environment,
//! every AArch64 function the pipeline encodes with the decode-check on is
//! re-checked after the gate passed, and `<dir>/enc5-<pid>.tsv` receives:
//!
//! * one `P` line per process naming the executable;
//! * one `T` line per (function, opcode, integrity policy, outcome, reason)
//!   with the instruction count, the tally;
//! * `S` lines with distinct real samples: the intent's operands, its fixup
//!   hole and the emitted word, capped per (opcode, policy, outcome, reason)
//!   and process so fuzz corpora stay bounded.
//!
//! `scripts/enc5_floor_census.py` reduces a directory of these files. The
//! sink changes no emitted byte and no verdict: a write failure is ignored,
//! and a disabled census costs one cached environment read per function. Like
//! every `TCG_*` variable it still makes artifact reuse ineligible while set,
//! so it is a measurement switch, not a production setting. A census is
//! testing evidence about which forms a corpus reached; it proves nothing.

use std::collections::{BTreeMap, HashMap, HashSet};
use std::fmt::Write as _;
use std::io::Write as _;
use std::path::PathBuf;
use std::sync::{Mutex, OnceLock, PoisonError};

use trust_cg_ir::inst::MachInst;
use trust_cg_ir::operand::MachOperand;
use trust_cg_ir::regs::SpecialReg;

use super::decode_check::A64DecodeCheck;
use crate::decode_check::{DecodeCheck, DecodeCheckItem, DecodeCheckOutcome, FixupHoleKind};

/// The process-environment variable naming the census output directory.
pub const A64_DECODE_CENSUS_DIR_ENV: &str = "TCG_DECODE_CHECK_CENSUS_DIR";

/// Distinct samples kept per (opcode, policy, outcome, reason) and process.
const SAMPLES_PER_CLASS: usize = 24;

fn census_dir() -> Option<&'static PathBuf> {
    static DIR: OnceLock<Option<PathBuf>> = OnceLock::new();
    DIR.get_or_init(|| {
        std::env::var_os(A64_DECODE_CENSUS_DIR_ENV)
            .filter(|value| !value.is_empty())
            .map(PathBuf::from)
    })
    .as_ref()
}

#[derive(Default)]
struct CensusSink {
    file: Option<std::fs::File>,
    opened: bool,
    seen: HashSet<String>,
    per_class: HashMap<String, usize>,
}

fn sink() -> &'static Mutex<CensusSink> {
    static SINK: OnceLock<Mutex<CensusSink>> = OnceLock::new();
    SINK.get_or_init(|| Mutex::new(CensusSink::default()))
}

/// One operand as a census token. The decode-check never reads a symbol's
/// name or a block's identity, so those collapse to their kind.
fn operand_token(operand: &MachOperand) -> String {
    match operand {
        MachOperand::PReg(p) => format!("r{}", p.encoding()),
        MachOperand::Imm(value) => format!("#{value}"),
        MachOperand::FImm(value) => format!("f{:016x}", value.to_bits()),
        MachOperand::Special(SpecialReg::SP) => "sp".to_string(),
        MachOperand::Special(SpecialReg::XZR) => "xzr".to_string(),
        MachOperand::Special(SpecialReg::WZR) => "wzr".to_string(),
        MachOperand::Symbol(_) => "sym".to_string(),
        MachOperand::ExactModuleSymbol(_) => "esym".to_string(),
        MachOperand::Block(_) => "blk".to_string(),
        MachOperand::JumpTableIndex(_) => "jt".to_string(),
        MachOperand::MemOp { base, offset } => format!("m{}:{offset}", base.encoding()),
        MachOperand::VReg(_) => "vreg".to_string(),
        MachOperand::StackSlot(_) => "slot".to_string(),
        MachOperand::FrameIndex(_) => "fi".to_string(),
        MachOperand::IncomingArg(offset) => format!("in{offset}"),
    }
}

fn hole_kind_token(kind: FixupHoleKind) -> &'static str {
    match kind {
        FixupHoleKind::Branch => "branch",
        FixupHoleKind::Call => "call",
        FixupHoleKind::GlobalRef => "global",
        FixupHoleKind::ExternRefGot => "got",
        FixupHoleKind::TlsTlv => "tlv",
        FixupHoleKind::ConstPool => "constpool",
    }
}

/// Record `items` of one encoded function. `proof_grade` names the integrity
/// policy the function was encoded under. A no-op unless the census variable
/// is set.
pub fn record_a64_decode_census(
    items: &[DecodeCheckItem<MachInst>],
    code: &[u8],
    proof_grade: bool,
) {
    // The composed transition record's check encode re-checks bytes the
    // route publishes; counting it would census each function twice.
    if crate::decode_check::telemetry_suppressed() {
        return;
    }
    let Some(dir) = census_dir() else {
        return;
    };
    let policy = if proof_grade { "proof" } else { "compat" };
    let mut guard = sink().lock().unwrap_or_else(PoisonError::into_inner);
    let sink = &mut *guard;
    if !sink.opened {
        sink.opened = true;
        let path = dir.join(format!("enc5-{}.tsv", std::process::id()));
        sink.file = std::fs::OpenOptions::new()
            .create(true)
            .append(true)
            .open(path)
            .ok();
        let exe = std::env::current_exe()
            .map(|path| path.display().to_string())
            .unwrap_or_default();
        if let Some(file) = sink.file.as_mut() {
            let _ = file.write_all(format!("P\t{}\t{exe}\n", std::process::id()).as_bytes());
        }
    }
    let mut tally: BTreeMap<(String, &'static str, &'static str), u64> = BTreeMap::new();
    let mut out = String::new();
    for item in items {
        let Some(bytes) = code.get(item.start..item.end) else {
            continue;
        };
        let (outcome, reason) =
            match A64DecodeCheck.check_one(&item.intent, bytes, item.hole.as_ref()) {
                DecodeCheckOutcome::Match => ("match", "-"),
                DecodeCheckOutcome::Allowlisted(reason) => ("allowlisted", reason),
                DecodeCheckOutcome::Mismatch(_) => ("mismatch", "-"),
            };
        let opcode = format!("{:?}", item.intent.opcode);
        let class = format!("{opcode}\t{policy}\t{outcome}\t{reason}");
        let count = tally.entry((opcode, outcome, reason)).or_insert(0);
        *count = count.saturating_add(1);
        // Samples: only while the class is below its cap, and only new ones.
        if sink
            .per_class
            .get(&class)
            .is_some_and(|kept| *kept >= SAMPLES_PER_CLASS)
        {
            continue;
        }
        let mut word = String::new();
        for byte in bytes.iter().rev() {
            let _ = write!(word, "{byte:02x}");
        }
        let hole = item.hole.map_or_else(
            || "-".to_string(),
            |hole| {
                format!(
                    "{}:{}:{}",
                    hole_kind_token(hole.kind),
                    hole.offset_in_inst,
                    hole.width
                )
            },
        );
        let operands = item
            .intent
            .operands
            .iter()
            .map(operand_token)
            .collect::<Vec<_>>()
            .join(" ");
        let line = format!("S\t{class}\t{word}\t{hole}\t{operands}\n");
        if sink.seen.insert(line.clone()) {
            *sink.per_class.entry(class).or_insert(0) += 1;
            out.push_str(&line);
        }
    }
    for ((opcode, outcome, reason), count) in tally {
        let _ = writeln!(out, "T\t{opcode}\t{policy}\t{outcome}\t{reason}\t{count}");
    }
    if let Some(file) = sink.file.as_mut() {
        let _ = file.write_all(out.as_bytes());
    }
}
