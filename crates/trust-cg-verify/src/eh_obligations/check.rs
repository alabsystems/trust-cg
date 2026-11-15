// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! The obligation decisions over a decoded object or image.

use std::collections::{BTreeMap, BTreeSet};

use super::a64::{Word, decode};
use super::cfi::{self, EhFrame, Rows, Rule};
use super::flow::{self, FlowInput, State, Val};
use super::lsda::{Action, Lsda, SlotResolver};
use super::macho::{self, Object, Term};
use super::{
    EhClause, EhFrameIntent, EhFunctionIntent, EhImage, EhObjectIntent, EhObligationKind,
    EhObligationReport, EhReg, EhTablesIntent, Violation,
};

const UNWIND_ARM64_MODE_MASK: u32 = 0x0f00_0000;
const UNWIND_ARM64_MODE_FRAMELESS: u32 = 0x0200_0000;
const UNWIND_ARM64_MODE_DWARF: u32 = 0x0300_0000;
const UNWIND_ARM64_MODE_FRAME: u32 = 0x0400_0000;
const UNWIND_ARM64_FRAMELESS_STACK_SIZE_MASK: u32 = 0x00ff_f000;
/// `UNWIND_HAS_LSDA`: the entry names an LSDA.
const UNWIND_HAS_LSDA: u32 = 0x4000_0000;
const COMPACT_ENTRY_SIZE: usize = 32;

/// The register pairs of a FRAME-mode encoding, in the order libunwind
/// (`stepWithCompactEncodingFrame`) restores them from FP-8 downward.
const COMPACT_PAIRS: [(u32, EhReg, EhReg); 9] = [
    (0x001, EhReg::X(19), EhReg::X(20)),
    (0x002, EhReg::X(21), EhReg::X(22)),
    (0x004, EhReg::X(23), EhReg::X(24)),
    (0x008, EhReg::X(25), EhReg::X(26)),
    (0x010, EhReg::X(27), EhReg::X(28)),
    (0x100, EhReg::D(8), EhReg::D(9)),
    (0x200, EhReg::D(10), EhReg::D(11)),
    (0x400, EhReg::D(12), EhReg::D(13)),
    (0x800, EhReg::D(14), EhReg::D(15)),
];

fn violation(kind: EhObligationKind, detail: impl Into<String>) -> Violation {
    Violation::object(kind, detail)
}

/// How a function's frame is described to the unwinder.
enum Description {
    Compact(u32),
    Dwarf { rows: Rows, ra_register: u64 },
}

/// The unwinder's view of the frame at one code offset.
#[derive(Debug, Clone, PartialEq, Eq)]
struct Frame {
    cfa_register: u64,
    cfa_offset: i64,
    saved: BTreeMap<EhReg, i64>,
}

impl Description {
    fn frame_at(&self, offset: u64) -> Result<Frame, Violation> {
        match self {
            Self::Compact(encoding) => compact_frame(*encoding),
            Self::Dwarf { rows, ra_register } => {
                let row = rows.at(offset).ok_or_else(|| {
                    violation(
                        EhObligationKind::FrameDescription,
                        format!("no FDE row covers offset {offset:#x}"),
                    )
                })?;
                let mut saved = BTreeMap::new();
                for (&number, rule) in &row.rules {
                    let reg = EhReg::from_dwarf(number).ok_or_else(|| {
                        violation(
                            EhObligationKind::FrameDescription,
                            format!("rule for DWARF register {number}, which is not X0-X30/V0-V31"),
                        )
                    })?;
                    match rule {
                        Rule::Offset(slot) => {
                            saved.insert(reg, *slot);
                        }
                        Rule::SameValue => {}
                        other => {
                            return Err(violation(
                                EhObligationKind::FrameDescription,
                                format!(
                                    "rule {other:?} for {reg} at offset {offset:#x} is outside the admitted offset/same-value rules"
                                ),
                            ));
                        }
                    }
                }
                if *ra_register != 30 {
                    return Err(violation(
                        EhObligationKind::FrameDescription,
                        format!("the CIE return-address column is {ra_register}, not X30"),
                    ));
                }
                Ok(Frame {
                    cfa_register: row.cfa_register,
                    cfa_offset: row.cfa_offset,
                    saved,
                })
            }
        }
    }
}

fn compact_frame(encoding: u32) -> Result<Frame, Violation> {
    // The LSDA flag is bound to the entry's LSDA field by the caller.
    let encoding = encoding & !UNWIND_HAS_LSDA;
    let pair_bits: u32 = COMPACT_PAIRS.iter().map(|(bit, _, _)| bit).sum();
    match encoding & UNWIND_ARM64_MODE_MASK {
        UNWIND_ARM64_MODE_FRAME => {
            let stray = encoding & !(UNWIND_ARM64_MODE_MASK | pair_bits);
            if stray != 0 {
                return Err(violation(
                    EhObligationKind::UnwindEntry,
                    format!(
                        "FRAME encoding {encoding:#010x} sets bits {stray:#x} outside the mode and register pairs"
                    ),
                ));
            }
            let mut saved = BTreeMap::from([(EhReg::X(29), -16), (EhReg::X(30), -8)]);
            let mut slot = -24i64;
            for (bit, first, second) in COMPACT_PAIRS {
                if encoding & bit != 0 {
                    saved.insert(first, slot);
                    saved.insert(second, slot - 8);
                    slot -= 16;
                }
            }
            Ok(Frame {
                cfa_register: 29,
                cfa_offset: 16,
                saved,
            })
        }
        UNWIND_ARM64_MODE_FRAMELESS => {
            let stray =
                encoding & !(UNWIND_ARM64_MODE_MASK | UNWIND_ARM64_FRAMELESS_STACK_SIZE_MASK);
            if stray != 0 {
                return Err(violation(
                    EhObligationKind::UnwindEntry,
                    format!(
                        "FRAMELESS encoding {encoding:#010x} sets bits {stray:#x} (saved-register pairs are not admitted)"
                    ),
                ));
            }
            Ok(Frame {
                cfa_register: 31,
                cfa_offset: i64::from((encoding & UNWIND_ARM64_FRAMELESS_STACK_SIZE_MASK) >> 12)
                    * 16,
                saved: BTreeMap::new(),
            })
        }
        other => Err(violation(
            EhObligationKind::UnwindEntry,
            format!(
                "compact mode {other:#010x} of encoding {encoding:#010x} is not FRAME, FRAMELESS or DWARF"
            ),
        )),
    }
}

fn check_frame_intent(frame: &Frame, intent: &EhFrameIntent, at: &str) -> Result<(), Violation> {
    let (register, offset) = if intent.uses_frame_pointer {
        (29, 16)
    } else {
        (31, i64::from(intent.total_frame_size))
    };
    if (frame.cfa_register, frame.cfa_offset) != (register, offset) {
        return Err(violation(
            EhObligationKind::FrameDescription,
            format!(
                "{at}: CFA = r{} + {}, but the frame owner's frame has CFA = r{register} + {offset}",
                frame.cfa_register, frame.cfa_offset
            ),
        ));
    }
    let expected: BTreeMap<EhReg, i64> = intent.saved.iter().copied().collect();
    if frame.saved != expected {
        let describe = |map: &BTreeMap<EhReg, i64>| {
            map.iter()
                .map(|(reg, slot)| format!("{reg}@CFA{slot:+}"))
                .collect::<Vec<_>>()
                .join(" ")
        };
        return Err(violation(
            EhObligationKind::FrameDescription,
            format!(
                "{at}: the description saves [{}] but the frame owner saves [{}]",
                describe(&frame.saved),
                describe(&expected)
            ),
        ));
    }
    Ok(())
}

fn check_unwind_point(frame: &Frame, state: &State, offset: u64) -> Result<(), Violation> {
    let fail = |detail: String| {
        Err(violation(
            EhObligationKind::UnwindPointFrame,
            format!("at the call at offset {offset:#x}: {detail}"),
        ))
    };
    let base = match frame.cfa_register {
        29 => state.x[29],
        31 => state.sp,
        other => return fail(format!("CFA register {other} is not X29 or SP")),
    };
    if base != Val::Stack(-frame.cfa_offset) {
        return fail(format!(
            "CFA = r{} + {} but r{} holds {base:?}, so the CFA is not the entry stack pointer",
            frame.cfa_register, frame.cfa_offset, frame.cfa_register
        ));
    }
    if !frame.saved.contains_key(&EhReg::X(30)) {
        return fail(
            "the return address is not recovered from a stack slot (at a call, LR holds the call's own return address)"
                .to_string(),
        );
    }
    for (&reg, &slot) in &frame.saved {
        let held = state.mem.get(&slot).copied();
        if held != Some(Val::Entry(reg)) {
            return fail(format!(
                "{reg} is recovered from CFA{slot:+}, which holds {held:?}, not {reg}'s entry value"
            ));
        }
    }
    for reg in EhReg::callee_saved() {
        if !frame.saved.contains_key(&reg) && !state.holds_entry(reg) {
            return fail(format!(
                "callee-saved {reg} has no save rule, but the function changed it before this call"
            ));
        }
    }
    Ok(())
}

/// Everything the decisions need about one function, from either front end.
struct FunctionView<'a> {
    intent: &'a EhFunctionIntent,
    code: &'a [u8],
    description: Description,
    /// The personality the unwind entry (or the FDE's CIE) names.
    personality: Option<String>,
    lsda: Option<(&'a [u8], &'a SlotResolver<'a>)>,
    /// Direct calls' relocated callee symbols, by function offset.
    call_targets: BTreeMap<u64, String>,
    /// Offsets of branch words carrying a relocation to a symbol.
    external_branches: BTreeSet<u64>,
}

fn expected_chain(
    pad: &super::EhLandingPadIntent,
    tables: &EhTablesIntent,
) -> Result<Vec<Action>, Violation> {
    let catch_all = i64::try_from(tables.type_table_len)
        .ok()
        .and_then(|len| len.checked_add(1))
        .ok_or_else(|| {
            violation(
                EhObligationKind::Intent,
                format!(
                    "type table length {} overflows a filter",
                    tables.type_table_len
                ),
            )
        })?;
    let mut chain = Vec::new();
    for clause in &pad.clauses {
        chain.push(match clause {
            EhClause::Catch(0) => Action::Catch {
                filter: catch_all,
                typeinfo: None,
            },
            EhClause::Catch(index) => {
                let symbol = tables
                    .typeinfo
                    .iter()
                    .find(|(bound, _)| bound == index)
                    .map(|(_, symbol)| symbol)
                    .filter(|_| u64::from(*index) <= tables.type_table_len)
                    .ok_or_else(|| {
                        violation(
                            EhObligationKind::Intent,
                            format!(
                                "landing block {} catches type index {index}, which the {}-entry type table does not bind",
                                pad.block, tables.type_table_len
                            ),
                        )
                    })?;
                Action::Catch {
                    filter: i64::from(*index),
                    typeinfo: Some(symbol.clone()),
                }
            }
            EhClause::RustEmptyFilter => Action::Filter {
                filter: -1,
                slots: Vec::new(),
            },
        });
    }
    if pad.cleanup && !chain.is_empty() {
        chain.push(Action::Cleanup);
    }
    Ok(chain)
}

fn check_function(
    view: &FunctionView<'_>,
    report: &mut EhObligationReport,
) -> Result<(), Violation> {
    let intent = view.intent;
    let code_len = intent.code_len as u64;
    let body_len = intent.body_len as u64;
    if view.code.len() as u64 != code_len || body_len > code_len || !body_len.is_multiple_of(4) {
        return Err(violation(
            EhObligationKind::Intent,
            format!(
                "the function's bytes ({}) do not match code length {code_len} with body {body_len}",
                view.code.len()
            ),
        ));
    }

    // Personality and LSDA binding.
    match (&intent.eh, &view.personality, &view.lsda) {
        (Some(tables), personality, lsda) => {
            if personality.as_deref() != Some(tables.personality.as_str()) {
                return Err(violation(
                    EhObligationKind::Personality,
                    format!(
                        "the unwind entry names personality {personality:?}, the function names `{}`",
                        tables.personality
                    ),
                ));
            }
            if lsda.is_none() {
                return Err(violation(
                    EhObligationKind::LsdaBinding,
                    "the function has exception-handling structure but its unwind entry names no LSDA",
                ));
            }
        }
        (None, Some(personality), None) => {
            return Err(violation(
                EhObligationKind::Personality,
                format!(
                    "a function without exception-handling structure names personality `{personality}` without an LSDA"
                ),
            ));
        }
        (None, _, _) => {}
    }

    let decoded = match view.lsda {
        Some((region, _)) => Some(Lsda::decode(region)?),
        None => None,
    };
    let records = decoded
        .as_ref()
        .map_or(&[][..], |lsda| &lsda.call_sites[..]);

    // Structure of the call-site table: the personalities stop at the first
    // record past the PC, so order matters as much as disjointness.
    let mut previous_end = 0u64;
    for (index, record) in records.iter().enumerate() {
        if record.len == 0 {
            return Err(violation(
                EhObligationKind::LsdaStructure,
                format!("call-site record {index} is empty"),
            ));
        }
        if index > 0 && record.start < previous_end {
            return Err(violation(
                EhObligationKind::LsdaStructure,
                format!(
                    "call-site record {index} starts at {:#x}, before the previous record ends at {previous_end:#x} (unsorted or overlapping)",
                    record.start
                ),
            ));
        }
        previous_end = record.end();
        if previous_end > code_len {
            return Err(violation(
                EhObligationKind::LsdaStructure,
                format!(
                    "call-site record {index} [{:#x}, {previous_end:#x}) leaves the function (length {code_len:#x})",
                    record.start
                ),
            ));
        }
        if record.landing_pad != 0
            && (record.landing_pad >= body_len || !record.landing_pad.is_multiple_of(4))
        {
            return Err(violation(
                EhObligationKind::LandingPad,
                format!(
                    "call-site record {index} names landing pad {:#x}, which is not an instruction of the body",
                    record.landing_pad
                ),
            ));
        }
    }

    let landing_pad_of = |offset: u64| -> Option<u64> {
        records
            .iter()
            .find(|record| record.start <= offset + 3 && offset + 3 < record.end())
            .map(|record| record.landing_pad)
            .filter(|&pad| pad != 0)
    };
    let flow = flow::analyze(&FlowInput {
        code: view.code,
        body_len,
        external_branches: &view.external_branches,
        landing_pad: &landing_pad_of,
    })?;

    // Every call word of the body. The analysis follows every edge control
    // can take (direct branches, call fallthroughs, resolved jump tables and
    // the exceptional edges of reached calls), so a call it does not reach
    // is dead code: no exception unwinds through it, so it is not an unwind
    // point, but its call-site record must still match the IR.
    let mut decoded_calls = BTreeSet::new();
    let mut offset = 0u64;
    while offset < body_len {
        let word = u32::from_le_bytes(
            view.code[offset as usize..offset as usize + 4]
                .try_into()
                .expect("four bytes"),
        );
        if matches!(decode(word), Word::Call { .. }) {
            decoded_calls.insert(offset);
        }
        offset += 4;
    }
    report.unreached_calls += decoded_calls.len() - flow.calls.len();

    // Calls the IR declares unable to unwind are not unwind points.
    let nounwind_calls: BTreeSet<u64> = intent
        .nounwind_calls
        .iter()
        .map(|&at| u64::from(at))
        .collect();
    for &call in &nounwind_calls {
        if !decoded_calls.contains(&call) {
            return Err(violation(
                EhObligationKind::Intent,
                format!(
                    "the call the IR declares unable to unwind at offset {call:#x} is not a BL/BLR word"
                ),
            ));
        }
    }
    let unwind_points: Vec<(u64, &State)> = flow
        .calls
        .iter()
        .filter(|(call, _)| !nounwind_calls.contains(call))
        .map(|(&call, state)| (call, state))
        .collect();

    // The frame description against the frame owner and the words.
    if unwind_points.is_empty() {
        let at = match &view.description {
            Description::Compact(_) => 0,
            Description::Dwarf { .. } => body_len.saturating_sub(4),
        };
        check_frame_intent(
            &view.description.frame_at(at)?,
            &intent.frame,
            "after the prologue",
        )?;
    }
    for &(call, state) in &unwind_points {
        let frame = view.description.frame_at(call)?;
        check_frame_intent(
            &frame,
            &intent.frame,
            &format!("at the call at offset {call:#x}"),
        )?;
        check_unwind_point(&frame, state, call)?;
    }
    report.unwind_points += unwind_points.len();
    match view.description {
        Description::Compact(_) => report.compact_frames += 1,
        Description::Dwarf { .. } => report.dwarf_frames += 1,
    }
    report.functions += 1;

    let Some(tables) = &intent.eh else {
        // A filler LSDA may say "keep unwinding" and nothing else.
        if let Some(record) = records
            .iter()
            .find(|record| record.landing_pad != 0 || record.action != 0)
        {
            return Err(violation(
                EhObligationKind::LsdaBinding,
                format!(
                    "a function without exception-handling structure carries an LSDA record naming landing pad {:#x} / action {}",
                    record.landing_pad, record.action
                ),
            ));
        }
        // A personality consults a filler LSDA too: every call that can
        // unwind must lie in a record, or the unwind stops here.
        if !records.is_empty() {
            check_coverage(
                records,
                &decoded_calls,
                &BTreeMap::new(),
                &nounwind_calls,
                view,
                report,
            )?;
        }
        return Ok(());
    };
    report.eh_functions += 1;
    let lsda = decoded.as_ref().expect("an EH function has an LSDA");
    let (region, slot) = view.lsda.expect("an EH function has an LSDA");

    // The IR side must describe these bytes.
    let pads: BTreeMap<u32, &super::EhLandingPadIntent> = tables
        .landing_pads
        .iter()
        .map(|pad| (pad.block, pad))
        .collect();
    let mut invokes: BTreeMap<u64, u64> = BTreeMap::new();
    for invoke in &tables.invokes {
        let call = u64::from(invoke.call_offset);
        if !decoded_calls.contains(&call) {
            return Err(violation(
                EhObligationKind::Intent,
                format!("invoke at offset {call:#x} is not a BL/BLR word of the function"),
            ));
        }
        let pad = pads.get(&invoke.landing_block).ok_or_else(|| {
            violation(
                EhObligationKind::Intent,
                format!(
                    "invoke at offset {call:#x} unwinds to block {}, which is not a landing block",
                    invoke.landing_block
                ),
            )
        })?;
        if invokes.insert(call, u64::from(pad.offset)).is_some() {
            return Err(violation(
                EhObligationKind::Intent,
                format!("two invokes claim the call at offset {call:#x}"),
            ));
        }
    }

    // Coverage and landing pads, call by call.
    let protecting = check_coverage(
        records,
        &decoded_calls,
        &invokes,
        &nounwind_calls,
        view,
        report,
    )?;
    // Every record naming a landing pad protects an invoke, and its action
    // chain is the landing block's clause list.
    let pad_by_offset: BTreeMap<u64, &super::EhLandingPadIntent> = tables
        .landing_pads
        .iter()
        .map(|pad| (u64::from(pad.offset), pad))
        .collect();
    let mut checked_pads = BTreeSet::new();
    for (index, record) in records.iter().enumerate() {
        if record.landing_pad == 0 {
            if record.action != 0 {
                return Err(violation(
                    EhObligationKind::ActionTable,
                    format!(
                        "call-site record {index} has no landing pad but action {}",
                        record.action
                    ),
                ));
            }
            continue;
        }
        if !protecting.contains(&index) || !invokes.values().any(|&pad| pad == record.landing_pad) {
            return Err(violation(
                EhObligationKind::LandingPad,
                format!(
                    "call-site record {index} names landing pad {:#x} but protects no invoke bound to it",
                    record.landing_pad
                ),
            ));
        }
        let pad = pad_by_offset.get(&record.landing_pad).ok_or_else(|| {
            violation(
                EhObligationKind::LandingPad,
                format!(
                    "call-site record {index} names landing pad {:#x}, which is no IR landing block",
                    record.landing_pad
                ),
            )
        })?;
        let expected = expected_chain(pad, tables)?;
        let actual = lsda.chain(region, record.action, slot)?;
        if actual != expected {
            return Err(violation(
                EhObligationKind::ActionTable,
                format!(
                    "landing pad {:#x} (block {}) has actions {actual:?}, but the IR's clauses {:?} (cleanup={}) require {expected:?}",
                    record.landing_pad, pad.block, pad.clauses, pad.cleanup
                ),
            ));
        }
        checked_pads.insert(record.landing_pad);
    }
    report.landing_pads += checked_pads.len();
    Ok(())
}

/// Call-site coverage and landing pads, call by call: every call word that
/// can unwind lies in exactly one record, which contains the whole call and
/// names the IR's landing block for an invoke (`invokes`: call offset ->
/// landing-pad offset) and no landing pad for any other call. Returns the
/// indices of the records that cover a call.
fn check_coverage(
    records: &[super::lsda::CallSite],
    decoded_calls: &BTreeSet<u64>,
    invokes: &BTreeMap<u64, u64>,
    nounwind_calls: &BTreeSet<u64>,
    view: &FunctionView<'_>,
    report: &mut EhObligationReport,
) -> Result<BTreeSet<usize>, Violation> {
    let mut protecting = BTreeSet::new();
    for &call in decoded_calls {
        let ip = call + 3;
        let containing: Vec<(usize, &super::lsda::CallSite)> = records
            .iter()
            .enumerate()
            .filter(|(_, record)| record.start <= ip && ip < record.end())
            .collect();
        let expected_pad = invokes.get(&call).copied().unwrap_or(0);
        match containing.as_slice() {
            [] => {
                let exempt = expected_pad == 0 && nounwind_calls.contains(&call);
                if !exempt {
                    return Err(violation(
                        EhObligationKind::CallSiteCoverage,
                        format!(
                            "the call at offset {call:#x}{} lies outside every call-site record",
                            view.call_targets
                                .get(&call)
                                .map(|callee| format!(" (to `{callee}`)"))
                                .unwrap_or_default()
                        ),
                    ));
                }
            }
            [(index, record)] => {
                if record.start > call || call + 4 > record.end() {
                    return Err(violation(
                        EhObligationKind::CallSiteCoverage,
                        format!(
                            "call-site record {index} [{:#x}, {:#x}) splits the call at offset {call:#x}",
                            record.start,
                            record.end()
                        ),
                    ));
                }
                if record.landing_pad != expected_pad {
                    return Err(violation(
                        EhObligationKind::LandingPad,
                        format!(
                            "the call at offset {call:#x} is covered by record {index} with landing pad {:#x}, but the IR assigns {}",
                            record.landing_pad,
                            if expected_pad == 0 {
                                "none (not an invoke)".to_string()
                            } else {
                                format!("the landing block at {expected_pad:#x}")
                            }
                        ),
                    ));
                }
                protecting.insert(*index);
                report.covered_calls += 1;
                if expected_pad != 0 {
                    report.invokes += 1;
                }
            }
            many => {
                return Err(violation(
                    EhObligationKind::CallSiteCoverage,
                    format!(
                        "the call at offset {call:#x} lies in {} call-site records",
                        many.len()
                    ),
                ));
            }
        }
    }

    Ok(protecting)
}

// ---------------------------------------------------------------------------
// Mach-O objects
// ---------------------------------------------------------------------------

struct CompactEntry {
    length: u32,
    encoding: u32,
    personality: Option<Term>,
    lsda: Option<Term>,
}

/// Is the 8-byte field at `offset` empty (no relocation, zero bytes)?
fn empty_field(object: &Object, section: usize, offset: u32) -> bool {
    let section = &object.sections[section];
    section.relocs_at(offset).is_empty()
        && section.bytes[offset as usize..offset as usize + 8]
            .iter()
            .all(|&b| b == 0)
}

fn symbol_name_at(object: &Object, term: &Term, text_ordinal: u8) -> Option<String> {
    match term {
        Term::Import(name) | Term::GotOf(name) => Some(name.clone()),
        Term::Address(address) => object
            .symbols_at(text_ordinal, *address)
            .first()
            .map(|symbol| symbol.name.clone()),
    }
}

/// Decide every obligation for the AArch64 Mach-O relocatable object
/// `object`, whose functions `intent` describes in emission order.
pub fn check_macho_object(
    object: &[u8],
    intent: &EhObjectIntent,
) -> Result<EhObligationReport, Violation> {
    let object = Object::parse(object)?;
    let (text_index, text) = object.section("__TEXT", "__text").ok_or_else(|| {
        violation(
            EhObligationKind::ObjectDecode,
            "the object has no __TEXT,__text",
        )
    })?;
    let text_ordinal = (text_index + 1) as u8;
    let compact = object.section("__LD", "__compact_unwind");
    let except = object.section("__TEXT", "__gcc_except_tab");
    let eh_frame_section = object.section("__TEXT", "__eh_frame");

    // Function extents.
    let mut starts: BTreeMap<u64, usize> = BTreeMap::new();
    let mut extents = Vec::with_capacity(intent.functions.len());
    for (index, function) in intent.functions.iter().enumerate() {
        let start = function.text_offset;
        let end = start + u64::from(function.code_len);
        if end > text.bytes.len() as u64 {
            return Err(violation(
                EhObligationKind::Intent,
                format!("[{start:#x}, {end:#x}) leaves __text"),
            )
            .in_function(&function.symbol));
        }
        if starts.insert(text.addr + start, index).is_some() {
            return Err(
                violation(EhObligationKind::Intent, "two functions share one address")
                    .in_function(&function.symbol),
            );
        }
        extents.push((start, end));
    }

    // Compact-unwind entries: exactly one per function.
    let mut entries: BTreeMap<usize, CompactEntry> = BTreeMap::new();
    if let Some((cu_index, cu)) = compact {
        if cu.bytes.len() % COMPACT_ENTRY_SIZE != 0 {
            return Err(violation(
                EhObligationKind::UnwindEntry,
                "__compact_unwind is not a whole number of 32-byte entries",
            ));
        }
        for at in (0..cu.bytes.len()).step_by(COMPACT_ENTRY_SIZE) {
            let at = at as u32;
            let function = object.field(cu_index, at, 8)?;
            let address = match macho::evaluate_pointer(&function, false, 0)? {
                Term::Address(address) => address,
                other => {
                    return Err(violation(
                        EhObligationKind::UnwindEntry,
                        format!("compact entry at {at} names {other:?}, not a defined function"),
                    ));
                }
            };
            let index = *starts.get(&address).ok_or_else(|| {
                violation(
                    EhObligationKind::UnwindEntry,
                    format!("compact entry at {at} covers address {address:#x}, which starts no checked function"),
                )
            })?;
            let read_u32 = |offset: u32| {
                u32::from_le_bytes(
                    cu.bytes[offset as usize..offset as usize + 4]
                        .try_into()
                        .expect("four bytes"),
                )
            };
            let personality = if empty_field(&object, cu_index, at + 16) {
                None
            } else {
                Some(macho::evaluate_pointer(
                    &object.field(cu_index, at + 16, 8)?,
                    false,
                    0,
                )?)
            };
            let lsda = if empty_field(&object, cu_index, at + 24) {
                None
            } else {
                Some(macho::evaluate_pointer(
                    &object.field(cu_index, at + 24, 8)?,
                    false,
                    0,
                )?)
            };
            let entry = CompactEntry {
                length: read_u32(at + 8),
                encoding: read_u32(at + 12),
                personality,
                lsda,
            };
            if entries.insert(index, entry).is_some() {
                return Err(violation(
                    EhObligationKind::UnwindEntry,
                    "the function has two compact-unwind entries",
                )
                .in_function(&intent.functions[index].symbol));
            }
        }
    }

    // FDEs, by function.
    let eh_frame = match eh_frame_section {
        Some((index, section)) => {
            let resolver = |at: usize, encoding: u8| -> Result<(Term, usize), Violation> {
                let width = cfi::pointer_width(encoding)?;
                let value = object.field(index, at as u32, width)?;
                let pcrel = match encoding & 0x70 {
                    0x00 => false,
                    0x10 => true,
                    other => {
                        return Err(violation(
                            EhObligationKind::CfiStructure,
                            format!("pointer application {other:#x} is not absptr or pcrel"),
                        ));
                    }
                };
                let target = macho::evaluate_pointer(
                    &value,
                    pcrel,
                    macho::address_of(&object, index, at as u32),
                )?;
                // DW_EH_PE_indirect exactly when the field is relocated to a
                // GOT slot: an unwinder reading a direct pointer to the slot
                // would take the slot's own address for the target.
                match (encoding & 0x80 != 0, &target) {
                    (true, Term::GotOf(_)) | (false, Term::Address(_) | Term::Import(_)) => {}
                    (true, _) => {
                        return Err(violation(
                            EhObligationKind::CfiStructure,
                            format!(
                                "indirect pointer at {at} does not name a GOT slot ({target:?})"
                            ),
                        ));
                    }
                    (false, Term::GotOf(name)) => {
                        return Err(violation(
                            EhObligationKind::CfiStructure,
                            format!(
                                "pointer at {at} is relocated to the GOT slot of `{name}` but its encoding {encoding:#04x} lacks DW_EH_PE_indirect"
                            ),
                        ));
                    }
                }
                Ok((target, width))
            };
            Some(EhFrame::decode(&section.bytes, &resolver)?)
        }
        None => None,
    };
    let mut fdes: BTreeMap<usize, usize> = BTreeMap::new();
    if let Some(frame) = &eh_frame {
        for (fde_index, fde) in frame.fdes.iter().enumerate() {
            let Term::Address(address) = fde.pc_begin else {
                return Err(violation(
                    EhObligationKind::UnwindEntry,
                    format!(
                        "FDE at {} begins at {:?}, not a defined function",
                        fde.offset, fde.pc_begin
                    ),
                ));
            };
            let index = *starts.get(&address).ok_or_else(|| {
                violation(
                    EhObligationKind::UnwindEntry,
                    format!(
                        "FDE at {} begins at {address:#x}, which starts no checked function",
                        fde.offset
                    ),
                )
            })?;
            if fdes.insert(index, fde_index).is_some() {
                return Err(
                    violation(EhObligationKind::UnwindEntry, "the function has two FDEs")
                        .in_function(&intent.functions[index].symbol),
                );
            }
        }
    }

    // LSDA regions: each runs to the next LSDA or the section end.
    let mut lsda_starts = BTreeSet::new();
    for entry in entries.values() {
        if let Some(Term::Address(address)) = entry.lsda {
            lsda_starts.insert(address);
        }
    }
    if let Some(frame) = &eh_frame {
        for fde in &frame.fdes {
            if let Some(Term::Address(address)) = fde.lsda {
                lsda_starts.insert(address);
            }
        }
    }

    let mut report = EhObligationReport::default();
    for (index, function) in intent.functions.iter().enumerate() {
        let attach = |error: Violation| error.in_function(&function.symbol);
        let (start, end) = extents[index];
        let entry = entries.get(&index).ok_or_else(|| {
            attach(violation(
                EhObligationKind::UnwindEntry,
                "the function has no compact-unwind entry",
            ))
        })?;
        if entry.length != function.code_len {
            return Err(attach(violation(
                EhObligationKind::UnwindEntry,
                format!(
                    "compact entry length {} != code length {}",
                    entry.length, function.code_len
                ),
            )));
        }
        let dwarf_mode = entry.encoding & UNWIND_ARM64_MODE_MASK == UNWIND_ARM64_MODE_DWARF;
        if (entry.encoding & UNWIND_HAS_LSDA != 0) != entry.lsda.is_some() {
            return Err(attach(violation(
                EhObligationKind::LsdaBinding,
                format!(
                    "compact encoding {:#010x} {} UNWIND_HAS_LSDA but the entry {} an LSDA field",
                    entry.encoding,
                    if entry.encoding & UNWIND_HAS_LSDA != 0 {
                        "sets"
                    } else {
                        "clears"
                    },
                    if entry.lsda.is_some() {
                        "carries"
                    } else {
                        "has no"
                    }
                ),
            )));
        }
        let fde = fdes
            .get(&index)
            .map(|&i| &eh_frame.as_ref().expect("an FDE implies __eh_frame").fdes[i]);
        let (description, personality_term, lsda_term) = if dwarf_mode {
            let fde = fde.ok_or_else(|| {
                attach(violation(
                    EhObligationKind::UnwindEntry,
                    "a DWARF-mode compact entry without an FDE",
                ))
            })?;
            if entry.encoding & !UNWIND_ARM64_MODE_MASK & !0x00ff_ffff != 0 {
                return Err(attach(violation(
                    EhObligationKind::UnwindEntry,
                    format!("DWARF encoding {:#010x} sets flag bits", entry.encoding),
                )));
            }
            if entry.personality.is_some() || entry.lsda.is_some() {
                return Err(attach(violation(
                    EhObligationKind::UnwindEntry,
                    "a DWARF-mode compact entry carries a personality or LSDA field (the FDE owns both)",
                )));
            }
            if fde.pc_range != u64::from(function.code_len) {
                return Err(attach(violation(
                    EhObligationKind::UnwindEntry,
                    format!(
                        "FDE range {} != code length {}",
                        fde.pc_range, function.code_len
                    ),
                )));
            }
            let frame = eh_frame.as_ref().expect("an FDE implies __eh_frame");
            let cie = &frame.cies[fde.cie];
            let rows = cfi::run(cie, fde).map_err(attach)?;
            (
                Description::Dwarf {
                    rows,
                    ra_register: cie.ra_register,
                },
                cie.personality.clone(),
                fde.lsda.clone(),
            )
        } else {
            if fde.is_some() {
                return Err(attach(violation(
                    EhObligationKind::UnwindEntry,
                    format!(
                        "an FDE accompanies compact encoding {:#010x}; the linker would ignore one of them",
                        entry.encoding
                    ),
                )));
            }
            (
                Description::Compact(entry.encoding),
                entry.personality.clone(),
                entry.lsda.clone(),
            )
        };
        let personality = personality_term
            .as_ref()
            .map(|term| {
                symbol_name_at(&object, term, text_ordinal).ok_or_else(|| {
                    attach(violation(
                        EhObligationKind::Personality,
                        format!("personality {term:?} names no symbol"),
                    ))
                })
            })
            .transpose()?;
        // A filler FDE under a shared zPLR CIE names the CIE's personality;
        // for a function without EH structure only its LSDA matters.
        let personality = if function.eh.is_none() && lsda_term.is_some() {
            None
        } else {
            personality
        };
        let lsda_region = match &lsda_term {
            None => None,
            Some(Term::Address(address)) => {
                let (except_index, except_section) = except.ok_or_else(|| {
                    attach(violation(
                        EhObligationKind::LsdaBinding,
                        "an LSDA pointer without __gcc_except_tab",
                    ))
                })?;
                if *address < except_section.addr || *address >= except_section.end() {
                    return Err(attach(violation(
                        EhObligationKind::LsdaBinding,
                        format!("the LSDA pointer {address:#x} is outside __gcc_except_tab"),
                    )));
                }
                let next = lsda_starts
                    .range(address + 1..)
                    .next()
                    .copied()
                    .unwrap_or(except_section.end());
                let from = (address - except_section.addr) as usize;
                let to = (next - except_section.addr) as usize;
                Some((except_index, from, &except_section.bytes[from..to]))
            }
            Some(other) => {
                return Err(attach(violation(
                    EhObligationKind::LsdaBinding,
                    format!("the LSDA pointer names {other:?}, not this object's __gcc_except_tab"),
                )));
            }
        };
        let slot_resolver = |region_offset: usize| -> Result<Option<String>, Violation> {
            let Some((except_index, from, _)) = lsda_region else {
                return Err(violation(EhObligationKind::LsdaStructure, "no LSDA"));
            };
            let section_offset = (from + region_offset) as u32;
            let section = &object.sections[except_index];
            let relocs = section.relocs_at(section_offset);
            match relocs.as_slice() {
                [] => {
                    let raw = &section.bytes[section_offset as usize..section_offset as usize + 4];
                    if raw.iter().all(|&b| b == 0) {
                        Ok(None)
                    } else {
                        Err(violation(
                            EhObligationKind::ActionTable,
                            format!(
                                "type-table slot at {section_offset:#x} is neither NULL nor relocated"
                            ),
                        ))
                    }
                }
                [reloc]
                    if reloc.kind == macho::ARM64_RELOC_POINTER_TO_GOT
                        && reloc.pcrel
                        && reloc.is_extern
                        && reloc.length == 2 =>
                {
                    Ok(Some(object.symbol(reloc.symbolnum)?.name.clone()))
                }
                other => Err(violation(
                    EhObligationKind::ActionTable,
                    format!("type-table slot at {section_offset:#x} carries relocations {other:?}"),
                )),
            }
        };
        let mut call_targets = BTreeMap::new();
        let mut external_branches = BTreeSet::new();
        for reloc in &text.relocs {
            let at = u64::from(reloc.address);
            if reloc.kind != macho::ARM64_RELOC_BRANCH26 || at < start || at >= end {
                continue;
            }
            external_branches.insert(at - start);
            if reloc.is_extern {
                call_targets.insert(at - start, object.symbol(reloc.symbolnum)?.name.clone());
            }
        }
        let view = FunctionView {
            intent: function,
            code: &text.bytes[start as usize..end as usize],
            description,
            personality,
            lsda: lsda_region.map(|(_, _, region)| (region, &slot_resolver as &SlotResolver<'_>)),
            call_targets,
            external_branches,
        };
        check_function(&view, &mut report).map_err(attach)?;
    }
    if let Some((index, _)) = entries
        .keys()
        .find(|&&index| index >= intent.functions.len())
        .map(|&index| (index, ()))
    {
        return Err(violation(
            EhObligationKind::UnwindEntry,
            format!("compact entry for unchecked function {index}"),
        ));
    }
    Ok(report)
}

// ---------------------------------------------------------------------------
// JIT images
// ---------------------------------------------------------------------------

fn read_image(bytes: &[u8], offset: u64, width: usize) -> Result<u64, Violation> {
    let start = usize::try_from(offset)
        .map_err(|_| violation(EhObligationKind::ObjectDecode, "image offset overflows"))?;
    let slice = bytes
        .get(start..start.saturating_add(width))
        .ok_or_else(|| {
            violation(
                EhObligationKind::ObjectDecode,
                format!("{width}-byte read at image offset {offset:#x} leaves the image"),
            )
        })?;
    let mut value = 0u64;
    for (i, byte) in slice.iter().enumerate() {
        value |= u64::from(*byte) << (8 * i);
    }
    Ok(value)
}

/// Decide every obligation for a published JIT image: the same decisions as
/// [`check_macho_object`] over the image's FDEs (the JIT has no compact
/// unwind) and LSDAs, with pointers read at their final addresses and the
/// personality read through its indirection slot.
pub fn check_jit_image(
    image: &EhImage<'_>,
    intent: &EhObjectIntent,
) -> Result<EhObligationReport, Violation> {
    if image.functions.len() != intent.functions.len() {
        return Err(violation(
            EhObligationKind::Intent,
            format!(
                "{} image functions for {} intent functions",
                image.functions.len(),
                intent.functions.len()
            ),
        ));
    }
    let (eh_start, eh_len) = image.eh_frame;
    let eh_bytes = usize::try_from(eh_start)
        .ok()
        .and_then(|start| {
            image
                .bytes
                .get(start..start.checked_add(usize::try_from(eh_len).ok()?)?)
        })
        .ok_or_else(|| violation(EhObligationKind::ObjectDecode, ".eh_frame leaves the image"))?;
    let personality_by_address: BTreeMap<u64, &str> = image
        .personalities
        .iter()
        .map(|(name, address)| (*address, name.as_str()))
        .collect();
    let resolver = |at: usize, encoding: u8| -> Result<(Term, usize), Violation> {
        let width = cfi::pointer_width(encoding)?;
        let field = eh_start + at as u64;
        let raw = read_image(image.bytes, field, width)?;
        let signed = match width {
            8 => raw as i64,
            4 => i64::from(raw as u32 as i32),
            2 => i64::from(raw as u16 as i16),
            _ => unreachable!("pointer_width admits 2, 4 and 8"),
        };
        let target = match encoding & 0x70 {
            0x00 => signed as u64,
            0x10 => (image.base + field).wrapping_add(signed as u64),
            other => {
                return Err(violation(
                    EhObligationKind::CfiStructure,
                    format!("pointer application {other:#x} is not absptr or pcrel"),
                ));
            }
        };
        if encoding & 0x80 != 0 {
            let slot = target.checked_sub(image.base).ok_or_else(|| {
                violation(
                    EhObligationKind::CfiStructure,
                    "indirect slot below the image",
                )
            })?;
            let value = read_image(image.bytes, slot, 8)?;
            let name = personality_by_address.get(&value).ok_or_else(|| {
                violation(
                    EhObligationKind::Personality,
                    format!(
                        "the indirect slot holds {value:#x}, the address of no bound personality"
                    ),
                )
            })?;
            return Ok((Term::Import((*name).to_string()), width));
        }
        Ok((Term::Address(target), width))
    };
    let frame = EhFrame::decode(eh_bytes, &resolver)?;
    let fde_at: BTreeMap<u64, usize> = frame
        .fdes
        .iter()
        .enumerate()
        .map(|(index, fde)| (fde.offset as u64, index))
        .collect();
    let mut lsda_starts: BTreeSet<u64> = BTreeSet::new();
    for fde in &frame.fdes {
        if let Some(Term::Address(address)) = fde.lsda {
            lsda_starts.insert(address);
        }
    }
    let image_end = image.base + image.bytes.len() as u64;
    let null_slots = |region_offset: usize, region: &[u8]| -> Result<Option<String>, Violation> {
        match region.get(region_offset..region_offset + 4) {
            Some(bytes) if bytes.iter().all(|&b| b == 0) => Ok(None),
            _ => Err(violation(
                EhObligationKind::ActionTable,
                "a JIT type-table slot is not NULL (typed catches are not published by the JIT)",
            )),
        }
    };
    let mut report = EhObligationReport::default();
    for (function, placed) in intent.functions.iter().zip(&image.functions) {
        let attach = |error: Violation| error.in_function(&function.symbol);
        let fde_offset = placed.fde_offset.checked_sub(eh_start).ok_or_else(|| {
            attach(violation(
                EhObligationKind::UnwindEntry,
                "FDE before .eh_frame",
            ))
        })?;
        let fde = &frame.fdes[*fde_at.get(&fde_offset).ok_or_else(|| {
            attach(violation(
                EhObligationKind::UnwindEntry,
                format!("no FDE at .eh_frame offset {fde_offset:#x}"),
            ))
        })?];
        let entry = image.base + placed.code_offset;
        if fde.pc_begin != Term::Address(entry) || fde.pc_range != u64::from(function.code_len) {
            return Err(attach(violation(
                EhObligationKind::UnwindEntry,
                format!(
                    "FDE covers {:?}+{:#x}, the function is at {entry:#x}+{:#x}",
                    fde.pc_begin, fde.pc_range, function.code_len
                ),
            )));
        }
        let cie = &frame.cies[fde.cie];
        let rows = cfi::run(cie, fde).map_err(attach)?;
        let personality = match &cie.personality {
            Some(Term::Import(name)) => Some(name.clone()),
            Some(other) => {
                return Err(attach(violation(
                    EhObligationKind::Personality,
                    format!("the CIE personality is {other:?}, not a bound personality slot"),
                )));
            }
            None => None,
        };
        let region = match &fde.lsda {
            None => None,
            Some(Term::Address(address)) => {
                let next = lsda_starts
                    .range(address + 1..)
                    .next()
                    .copied()
                    .unwrap_or(image_end);
                let from = address.checked_sub(image.base).ok_or_else(|| {
                    attach(violation(
                        EhObligationKind::LsdaBinding,
                        "LSDA below the image",
                    ))
                })? as usize;
                let to = (next.min(image_end) - image.base) as usize;
                Some(image.bytes.get(from..to).ok_or_else(|| {
                    attach(violation(
                        EhObligationKind::LsdaBinding,
                        "LSDA leaves the image",
                    ))
                })?)
            }
            Some(other) => {
                return Err(attach(violation(
                    EhObligationKind::LsdaBinding,
                    format!("the LSDA pointer is {other:?}"),
                )));
            }
        };
        let personality = if function.eh.is_none() && region.is_some() {
            None
        } else {
            personality
        };
        let slot = |region_offset: usize| null_slots(region_offset, region.unwrap_or(&[]));
        let code_start = placed.code_offset as usize;
        let code = image
            .bytes
            .get(code_start..code_start + function.code_len as usize)
            .ok_or_else(|| {
                attach(violation(
                    EhObligationKind::ObjectDecode,
                    "function leaves the image",
                ))
            })?;
        let view = FunctionView {
            intent: function,
            code,
            description: Description::Dwarf {
                rows,
                ra_register: cie.ra_register,
            },
            personality,
            lsda: region.map(|region| (region, &slot as &SlotResolver<'_>)),
            call_targets: BTreeMap::new(),
            external_branches: BTreeSet::new(),
        };
        check_function(&view, &mut report).map_err(attach)?;
    }
    Ok(report)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn compact_frame_encodings_decode_in_libunwind_order() {
        let frame = compact_frame(0x0400_0005).expect("FRAME x19/x20 + x23/x24");
        assert_eq!((frame.cfa_register, frame.cfa_offset), (29, 16));
        assert_eq!(
            frame.saved,
            BTreeMap::from([
                (EhReg::X(19), -24),
                (EhReg::X(20), -32),
                (EhReg::X(23), -40),
                (EhReg::X(24), -48),
                (EhReg::X(29), -16),
                (EhReg::X(30), -8),
            ])
        );
        let frameless = compact_frame(0x0200_2000).expect("FRAMELESS 32 bytes");
        assert_eq!((frameless.cfa_register, frameless.cfa_offset), (31, 32));
        assert!(frameless.saved.is_empty());
        assert!(compact_frame(0x0400_1000).is_err(), "stray bits");
        assert!(compact_frame(0x0200_0001).is_err(), "frameless pairs");
        assert!(compact_frame(0x0100_0000).is_err(), "unknown mode");
    }

    #[test]
    fn an_unwind_point_needs_the_slots_the_description_names() {
        let frame = compact_frame(0x0400_0001).expect("FRAME x19/x20");
        let mut state = State {
            x: [Val::Unknown; 31],
            sp: Val::Stack(-32),
            d_entry: 0xff,
            mem: BTreeMap::new(),
        };
        state.x[29] = Val::Stack(-16);
        for (reg, slot) in &frame.saved {
            state.mem.insert(*slot, Val::Entry(*reg));
        }
        for (offset, value) in state.x[21..29].iter_mut().enumerate() {
            *value = Val::Entry(EhReg::X((21 + offset) as u8));
        }
        check_unwind_point(&frame, &state, 8).expect("holds");
        let mut missing = state.clone();
        missing.mem.remove(&-32);
        assert_eq!(
            check_unwind_point(&frame, &missing, 8)
                .expect_err("x20 slot")
                .kind,
            EhObligationKind::UnwindPointFrame
        );
        let mut clobbered = state.clone();
        clobbered.x[21] = Val::Unknown;
        assert!(
            check_unwind_point(&frame, &clobbered, 8).is_err(),
            "x21 changed"
        );
        let mut moved = state;
        moved.x[29] = Val::Stack(-32);
        assert!(check_unwind_point(&frame, &moved, 8).is_err(), "CFA");
    }

    // Whole-function decisions over hand-assembled words.
    const STP_FP_LR_PRE: u32 = 0xa9bf_7bfd; // stp x29, x30, [sp, #-16]!
    const MOV_FP_SP: u32 = 0x9100_03fd; // mov x29, sp
    const LDP_FP_LR_POST: u32 = 0xa8c1_7bfd; // ldp x29, x30, [sp], #16
    const BL: u32 = 0x9400_0000;
    const RET: u32 = 0xd65f_03c0;
    const BRK: u32 = 0xd420_0020;
    /// FRAME mode, no callee-saved pairs: CFA = FP + 16, FP/LR below it.
    const FRAME: u32 = 0x0400_0000;

    fn words(words: &[u32]) -> Vec<u8> {
        words.iter().flat_map(|word| word.to_le_bytes()).collect()
    }

    fn fp_frame() -> EhFrameIntent {
        EhFrameIntent {
            saved: vec![(EhReg::X(29), -16), (EhReg::X(30), -8)],
            uses_frame_pointer: true,
            total_frame_size: 16,
        }
    }

    /// One cleanup landing block at `pad` protecting the invoke at `call`.
    fn cleanup_tables(call: u32, pad: u32) -> EhTablesIntent {
        EhTablesIntent {
            personality: "_personality".to_string(),
            landing_pads: vec![super::super::EhLandingPadIntent {
                block: 1,
                offset: pad,
                clauses: Vec::new(),
                cleanup: true,
            }],
            invokes: vec![super::super::EhInvokeIntent {
                call_offset: call,
                landing_block: 1,
            }],
            type_table_len: 0,
            typeinfo: Vec::new(),
        }
    }

    /// An LSDA without a type table whose ULEB128 records are
    /// `(start, length, landing pad)` with action 0.
    fn cleanup_lsda(records: &[(u8, u8, u8)]) -> Vec<u8> {
        let mut lsda = vec![0xff, 0xff, 0x01, (records.len() * 4) as u8];
        for &(start, len, pad) in records {
            lsda.extend_from_slice(&[start, len, pad, 0]);
        }
        lsda
    }

    fn decide(
        code: &[u8],
        frame: EhFrameIntent,
        encoding: u32,
        eh: Option<EhTablesIntent>,
        lsda: Option<&[u8]>,
    ) -> Result<EhObligationReport, Violation> {
        let intent = EhFunctionIntent {
            symbol: "f".to_string(),
            text_offset: 0,
            body_len: code.len() as u32,
            code_len: code.len() as u32,
            frame,
            nounwind_calls: Vec::new(),
            eh,
        };
        let slot = |_: usize| -> Result<Option<String>, Violation> { Ok(None) };
        let view = FunctionView {
            intent: &intent,
            code,
            description: Description::Compact(encoding),
            personality: intent.eh.as_ref().map(|tables| tables.personality.clone()),
            lsda: lsda.map(|region| (region, &slot as &SlotResolver<'_>)),
            call_targets: BTreeMap::new(),
            external_branches: BTreeSet::new(),
        };
        let mut report = EhObligationReport::default();
        check_function(&view, &mut report).map(|()| report)
    }

    /// The call inside a landing pad is reached only through the invoke's
    /// exceptional edge (the normal path returns first). It is an unwind
    /// point all the same: counted, and its frame checked, so a pad that
    /// breaks the frame record before calling `_Unwind_Resume` is refused.
    #[test]
    fn a_landing_pad_reached_only_by_unwinding_is_checked() {
        let code = words(&[STP_FP_LR_PRE, MOV_FP_SP, BL, LDP_FP_LR_POST, RET, BL, BRK]);
        let lsda = cleanup_lsda(&[(8, 4, 20), (20, 4, 0)]);
        let report = decide(
            &code,
            fp_frame(),
            FRAME,
            Some(cleanup_tables(8, 20)),
            Some(&lsda),
        )
        .expect("holds");
        assert_eq!(
            report,
            EhObligationReport {
                functions: 1,
                eh_functions: 1,
                unwind_points: 2,
                unreached_calls: 0,
                covered_calls: 2,
                invokes: 1,
                landing_pads: 1,
                compact_frames: 1,
                dwarf_frames: 0,
            }
        );
        // The pad overwrites FP (mov x29, x0) before its call.
        let code = words(&[
            STP_FP_LR_PRE,
            MOV_FP_SP,
            BL,
            LDP_FP_LR_POST,
            RET,
            0xaa00_03fd,
            BL,
            BRK,
        ]);
        let lsda = cleanup_lsda(&[(8, 4, 20), (24, 4, 0)]);
        let error = decide(
            &code,
            fp_frame(),
            FRAME,
            Some(cleanup_tables(8, 20)),
            Some(&lsda),
        )
        .expect_err("FP clobbered in the pad");
        assert_eq!(error.kind, EhObligationKind::UnwindPointFrame, "{error}");
        assert!(error.detail.contains("offset 0x18"), "{error}");
    }

    /// A FRAMELESS description at a call: the unwinder would take the
    /// return address from LR, which the call overwrote.
    #[test]
    fn a_frameless_description_at_a_call_is_refused() {
        // sub sp, sp, #16; bl; add sp, sp, #16; ret
        let code = words(&[0xd100_43ff, BL, 0x9100_43ff, RET]);
        let frame = EhFrameIntent {
            saved: Vec::new(),
            uses_frame_pointer: false,
            total_frame_size: 16,
        };
        let error = decide(&code, frame, 0x0200_1000, None, None).expect_err("frameless call");
        assert_eq!(error.kind, EhObligationKind::UnwindPointFrame, "{error}");
        assert!(error.detail.contains("return address"), "{error}");
    }

    /// D8-D15 are tracked: one written before a call without a save rule
    /// is refused, while a write to a caller-saved V register is not.
    #[test]
    fn an_unsaved_d8_clobbered_before_a_call_is_refused() {
        let body =
            |middle: u32| words(&[STP_FP_LR_PRE, MOV_FP_SP, middle, BL, LDP_FP_LR_POST, RET]);
        // fadd d0, d0, d1
        let report = decide(&body(0x1e61_2800), fp_frame(), FRAME, None, None).expect("d0");
        assert_eq!(report.unwind_points, 1);
        // fadd d8, d0, d1
        let error =
            decide(&body(0x1e61_2808), fp_frame(), FRAME, None, None).expect_err("d8 clobbered");
        assert_eq!(error.kind, EhObligationKind::UnwindPointFrame, "{error}");
        assert!(error.detail.contains("d8"), "{error}");
    }

    /// A store into the frame record through a form other than STR/STP
    /// (release, exclusive, atomic, unprivileged, RCpc, structure) at a
    /// known CFA offset breaks the record the unwinder reads.
    #[test]
    fn a_frame_record_overwritten_by_any_store_form_is_refused() {
        for (what, store) in [
            ("stlr xzr, [x29]", 0xc89f_ffbf),
            ("stxr w0, xzr, [x29]", 0xc800_7fbf),
            ("cas x0, x1, [x29]", 0xc8a0_7fa1),
            ("ldadd x0, x1, [x29]", 0xf820_03a1),
            ("sttr xzr, [x29]", 0xf800_0bbf),
            ("stlur xzr, [x29, #8]", 0xd900_83bf),
            ("st1 {v0.2d}, [x29]", 0x4c00_7fa0),
        ] {
            let code = words(&[STP_FP_LR_PRE, MOV_FP_SP, store, BL, LDP_FP_LR_POST, RET]);
            let error = decide(&code, fp_frame(), FRAME, None, None)
                .err()
                .unwrap_or_else(|| panic!("{what}: accepted"));
            assert_eq!(
                error.kind,
                EhObligationKind::UnwindPointFrame,
                "{what}: {error}"
            );
        }
        // A load-acquire from the record leaves it intact.
        let code = words(&[
            STP_FP_LR_PRE,
            MOV_FP_SP,
            0xc8df_ffa0,
            BL,
            LDP_FP_LR_POST,
            RET,
        ]);
        decide(&code, fp_frame(), FRAME, None, None).expect("ldar x0, [x29]");
    }
}
