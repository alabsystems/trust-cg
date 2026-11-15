// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! The frame state of a function at every call, computed from its bytes.
//!
//! A forward data-flow analysis over the words of one function, following
//! the control flow the words themselves encode: direct branches, the
//! fallthrough of calls and conditional branches, jump-table dispatch
//! (`ADR` / `LDRSW [base, index, LSL #2]` / `ADD` / `BR`, with the table
//! read from the function's own appended bytes) and the exceptional edge
//! from each call to the landing pad its LSDA record names. The abstract
//! state tracks, relative to the canonical frame address (CFA, the stack
//! pointer at entry): SP, every general-purpose register, which of D8-D15
//! still hold their entry values, and the 8-byte stack slots at known
//! CFA-relative addresses together with which entry register each holds.
//!
//! Every store whose address is a known constant offset from the CFA is
//! applied to the slots it covers: an immediate-addressed `STR`/`STP`
//! records the value it writes, and every other store form the classifier
//! admits (release, exclusive, compare-and-swap, LSE atomic, unprivileged,
//! unscaled RCpc and SIMD structure stores) forgets every slot its bytes
//! overlap.
//!
//! Boundary (stated, not checked here): a store whose address is not a
//! known constant offset from the CFA (a pointer the function computed, a
//! register-offset address, SP after a runtime-sized allocation) is assumed
//! not to write the callee-saved area. That is the frame owner's slot
//! discipline, trusted base TB-13.

use std::collections::{BTreeMap, BTreeSet, VecDeque};

use super::a64::{Access, Effects, Mode, Word, decode};
use super::{EhObligationKind, EhReg, Violation};

/// An abstract value.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Val {
    /// The value register `EhReg` held at function entry.
    Entry(EhReg),
    /// The address `CFA + offset`.
    Stack(i64),
    /// The address of function offset `offset`.
    Code(u64),
    /// A sign-extended entry of the jump table at function offset `table`.
    TableEntry(u64),
    /// `table + entry`: a dispatch target of the jump table at `table`.
    TableTarget(u64),
    Unknown,
}

/// The abstract machine state before one word.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct State {
    pub(crate) x: [Val; 31],
    pub(crate) sp: Val,
    /// Bit n: D(8 + n) still holds its entry value.
    pub(crate) d_entry: u8,
    /// 8-byte stack slots at known CFA offsets.
    pub(crate) mem: BTreeMap<i64, Val>,
}

impl State {
    fn entry() -> Self {
        let mut x = [Val::Unknown; 31];
        for (n, value) in x.iter_mut().enumerate().skip(19) {
            *value = Val::Entry(EhReg::X(n as u8));
        }
        Self {
            x,
            sp: Val::Stack(0),
            d_entry: 0xff,
            mem: BTreeMap::new(),
        }
    }

    fn join(&mut self, other: &Self) -> bool {
        let before = self.clone();
        for (mine, theirs) in self.x.iter_mut().zip(other.x.iter()) {
            if mine != theirs {
                *mine = Val::Unknown;
            }
        }
        if self.sp != other.sp {
            self.sp = Val::Unknown;
        }
        self.d_entry &= other.d_entry;
        self.mem
            .retain(|offset, value| other.mem.get(offset) == Some(value));
        *self != before
    }

    /// The value of general-purpose register `n` as a base or source; 31 is
    /// SP when `sp_form`, XZR otherwise.
    fn read(&self, n: u8, sp_form: bool) -> Val {
        if n == 31 {
            if sp_form { self.sp } else { Val::Unknown }
        } else {
            self.x[n as usize]
        }
    }

    fn write(&mut self, n: u8, sp_form: bool, value: Val) {
        if n == 31 {
            if sp_form {
                self.sp = value;
            }
        } else {
            self.x[n as usize] = value;
        }
    }

    fn write_vector(&mut self, n: u8) {
        if (8..16).contains(&n) {
            self.d_entry &= !(1 << (n - 8));
        }
    }

    /// Forget every 8-byte slot overlapping `[start, start + len)`.
    fn clobber(&mut self, start: i64, len: i64) {
        let end = start.saturating_add(len);
        self.mem
            .retain(|&slot, _| slot >= end || slot.saturating_add(8) <= start);
    }

    /// The value of `reg` now, for a frame description that leaves it in
    /// place: `Entry(reg)` exactly when it still holds its entry value.
    pub(crate) fn holds_entry(&self, reg: EhReg) -> bool {
        match reg {
            EhReg::X(n) if n < 31 => self.x[n as usize] == Val::Entry(reg),
            EhReg::D(n) if (8..16).contains(&n) => self.d_entry & (1 << (n - 8)) != 0,
            _ => false,
        }
    }
}

fn flow_error(offset: u64, detail: impl Into<String>) -> Violation {
    Violation::object(
        EhObligationKind::FrameFlow,
        format!("at function offset {offset:#x}: {}", detail.into()),
    )
}

fn offset_add(base: u64, delta: i64) -> Option<u64> {
    u64::try_from(i128::from(base) + i128::from(delta)).ok()
}

fn add(value: Val, delta: i64) -> Val {
    match value {
        Val::Stack(offset) => offset.checked_add(delta).map_or(Val::Unknown, Val::Stack),
        Val::Code(offset) => offset_add(offset, delta).map_or(Val::Unknown, Val::Code),
        _ => Val::Unknown,
    }
}

/// The words of one function and how its calls leave it.
pub(crate) struct FlowInput<'a> {
    /// The function's bytes: its instructions, then its jump tables.
    pub(crate) code: &'a [u8],
    /// Bytes of instructions; jump tables occupy `[body_len, code.len())`.
    pub(crate) body_len: u64,
    /// Function offsets of words carrying a branch relocation to a symbol:
    /// a `B` there leaves the function (a tail call).
    pub(crate) external_branches: &'a BTreeSet<u64>,
    /// The landing pad a call at the given offset unwinds to, if any.
    pub(crate) landing_pad: &'a dyn Fn(u64) -> Option<u64>,
}

/// The result: the state before every reached call.
#[derive(Debug, Clone)]
pub(crate) struct Flow {
    pub(crate) calls: BTreeMap<u64, State>,
}

fn word_at(code: &[u8], offset: u64) -> Option<u32> {
    let start = usize::try_from(offset).ok()?;
    code.get(start..start.checked_add(4)?)
        .map(|bytes| u32::from_le_bytes(bytes.try_into().expect("four bytes")))
}

/// The jump tables of the function: each starts at an `ADR` target in
/// `[body_len, code_len)` and runs to the next one (the encoder appends one
/// table per dispatch, contiguously).
fn jump_tables(input: &FlowInput<'_>) -> BTreeMap<u64, u64> {
    let code_len = input.code.len() as u64;
    let mut starts = BTreeSet::new();
    let mut offset = 0u64;
    while offset + 4 <= input.body_len {
        if let Some(word) = word_at(input.code, offset)
            && let Word::Adr { displacement, .. } = decode(word)
            && let Some(target) = offset_add(offset, displacement)
            && target >= input.body_len
            && target < code_len
        {
            starts.insert(target);
        }
        offset += 4;
    }
    let starts: Vec<u64> = starts.into_iter().collect();
    starts
        .iter()
        .enumerate()
        .map(|(i, &start)| (start, starts.get(i + 1).copied().unwrap_or(code_len)))
        .collect()
}

/// Run the analysis from the function entry.
pub(crate) fn analyze(input: &FlowInput<'_>) -> Result<Flow, Violation> {
    let code_len = input.code.len() as u64;
    if input.body_len > code_len || !input.body_len.is_multiple_of(4) || !code_len.is_multiple_of(4)
    {
        return Err(flow_error(
            0,
            format!(
                "instruction body {} and code length {code_len} are not a 4-byte prefix",
                input.body_len
            ),
        ));
    }
    let tables = jump_tables(input);
    let mut states: BTreeMap<u64, State> = BTreeMap::new();
    let mut calls = BTreeMap::new();
    let mut queue = VecDeque::new();
    states.insert(0, State::entry());
    queue.push_back(0u64);
    // The lattice is finite and every transfer is monotone, so the worklist
    // terminates; this bound only turns an analysis defect into a refusal.
    let budget = (input.body_len / 4 + 1).saturating_mul(1024);
    let mut steps = 0u64;
    while let Some(offset) = queue.pop_front() {
        steps += 1;
        if steps > budget {
            return Err(flow_error(offset, "the analysis did not converge"));
        }
        if offset >= input.body_len {
            return Err(flow_error(
                offset,
                format!(
                    "control reaches past the instruction body (length {:#x})",
                    input.body_len
                ),
            ));
        }
        let word =
            word_at(input.code, offset).ok_or_else(|| flow_error(offset, "word out of bounds"))?;
        let state = states[&offset].clone();
        let mut next = state.clone();
        let mut successors: Vec<u64> = Vec::new();
        let fallthrough = offset + 4;
        match decode(word) {
            Word::Call { .. } => {
                calls.insert(offset, state.clone());
                for n in (0..19).chain([30]) {
                    next.x[n] = Val::Unknown;
                }
                successors.push(fallthrough);
                if let Some(pad) = (input.landing_pad)(offset) {
                    successors.push(pad);
                }
            }
            Word::Branch { displacement } => {
                if !input.external_branches.contains(&offset) {
                    match offset_add(offset, displacement) {
                        Some(target) if target < input.body_len => successors.push(target),
                        Some(target) if target < code_len => {
                            return Err(flow_error(
                                offset,
                                format!("branch into the jump-table bytes at {target:#x}"),
                            ));
                        }
                        // A branch outside the function without a relocation
                        // leaves it like a tail call.
                        _ => {}
                    }
                }
            }
            Word::CondBranch { displacement } => {
                let target = offset_add(offset, displacement)
                    .filter(|&target| target < input.body_len)
                    .ok_or_else(|| {
                        flow_error(offset, "conditional branch leaves the instruction body")
                    })?;
                successors.push(target);
                successors.push(fallthrough);
            }
            Word::Return | Word::Trap => {}
            Word::IndirectBranch { rn } => {
                let Val::TableTarget(table) = state.read(rn, false) else {
                    return Err(flow_error(
                        offset,
                        format!(
                            "BR X{rn} target is not a jump-table dispatch ({:?})",
                            state.read(rn, false)
                        ),
                    ));
                };
                let end = *tables.get(&table).ok_or_else(|| {
                    flow_error(offset, format!("no jump table starts at {table:#x}"))
                })?;
                let mut entry = table;
                while entry < end {
                    let delta = word_at(input.code, entry)
                        .ok_or_else(|| flow_error(offset, "jump-table entry out of bounds"))?
                        as i32;
                    let target = offset_add(table, i64::from(delta))
                        .filter(|&target| target < input.body_len && target.is_multiple_of(4))
                        .ok_or_else(|| {
                            flow_error(
                                offset,
                                format!("jump-table entry at {entry:#x} targets outside the body"),
                            )
                        })?;
                    successors.push(target);
                    entry += 4;
                }
            }
            Word::AddImm {
                rd,
                rn,
                delta,
                setflags,
            } => {
                if !(setflags && rd == 31) {
                    let value = add(state.read(rn, true), delta);
                    next.write(rd, !setflags, value);
                }
                successors.push(fallthrough);
            }
            Word::AddReg { rd, rn, rm } => {
                let value = match (state.read(rn, false), state.read(rm, false)) {
                    (Val::Code(a), Val::TableEntry(t)) | (Val::TableEntry(t), Val::Code(a))
                        if a == t =>
                    {
                        Val::TableTarget(t)
                    }
                    _ => Val::Unknown,
                };
                next.write(rd, false, value);
                successors.push(fallthrough);
            }
            Word::Adr { rd, displacement } => {
                let value = offset_add(offset, displacement).map_or(Val::Unknown, Val::Code);
                next.write(rd, false, value);
                successors.push(fallthrough);
            }
            Word::MovReg { rd, rm } => {
                let value = state.read(rm, false);
                next.write(rd, false, value);
                successors.push(fallthrough);
            }
            Word::LdrswScaled { rt, rn, .. } => {
                let value = match state.read(rn, false) {
                    Val::Code(table) => Val::TableEntry(table),
                    _ => Val::Unknown,
                };
                next.write(rt, false, value);
                successors.push(fallthrough);
            }
            Word::Access(access) => {
                apply_access(&state, &mut next, access);
                successors.push(fallthrough);
            }
            Word::Other(effects) => {
                apply_effects(&state, &mut next, effects);
                successors.push(fallthrough);
            }
            Word::Unknown => {
                return Err(flow_error(
                    offset,
                    format!("word {word:#010x} is outside the classified A64 subset"),
                ));
            }
        }
        for successor in successors {
            match states.get_mut(&successor) {
                Some(existing) => {
                    if existing.join(&next) {
                        queue.push_back(successor);
                    }
                }
                None => {
                    states.insert(successor, next.clone());
                    queue.push_back(successor);
                }
            }
        }
    }
    Ok(Flow { calls })
}

fn apply_effects(state: &State, next: &mut State, effects: Effects) {
    if let Some(store) = effects.store
        && let Val::Stack(base) = state.read(store.base, true)
        && let Some((offset, bytes)) = store.range
    {
        match base.checked_add(offset) {
            Some(start) => next.clobber(start, bytes),
            None => next.mem.clear(),
        }
    }
    for n in 0..31u8 {
        if effects.gpr & (1 << n) != 0 {
            next.x[n as usize] = Val::Unknown;
        }
    }
    if effects.sp {
        next.sp = Val::Unknown;
    }
    for n in 0..32u8 {
        if effects.vector & (1 << n) != 0 {
            next.write_vector(n);
        }
    }
}

fn apply_access(state: &State, next: &mut State, access: Access) {
    let base = state.read(access.rn, true);
    let address = match access.mode {
        Mode::Offset | Mode::Pre => add(base, access.imm),
        Mode::Post => base,
    };
    let registers: Vec<u8> = std::iter::once(access.rt).chain(access.rt2).collect();
    let size = i64::from(access.size);
    for (index, &reg) in registers.iter().enumerate() {
        let slot = match address {
            Val::Stack(at) => Some(at + size * index as i64),
            _ => None,
        };
        if access.load {
            if access.vector {
                // An exact 8-byte reload of the entry value restores it.
                let restored = access.size == 8
                    && slot.and_then(|at| next.mem.get(&at).copied())
                        == Some(Val::Entry(EhReg::D(reg)));
                if (8..16).contains(&reg) {
                    if restored {
                        next.d_entry |= 1 << (reg - 8);
                    } else {
                        next.d_entry &= !(1 << (reg - 8));
                    }
                }
            } else {
                let value = match slot {
                    Some(at) if access.size == 8 && !access.transforms => {
                        state.mem.get(&at).copied().unwrap_or(Val::Unknown)
                    }
                    _ => Val::Unknown,
                };
                next.write(reg, false, value);
            }
        } else if let Some(at) = slot {
            let value = if access.size == 8 && at % 8 == 0 {
                if access.vector {
                    if (8..16).contains(&reg) && state.d_entry & (1 << (reg - 8)) != 0 {
                        Val::Entry(EhReg::D(reg))
                    } else {
                        Val::Unknown
                    }
                } else {
                    state.read(reg, false)
                }
            } else {
                Val::Unknown
            };
            next.clobber(at, size);
            if value != Val::Unknown {
                next.mem.insert(at, value);
            }
        }
    }
    if matches!(access.mode, Mode::Pre | Mode::Post) {
        let written = add(base, access.imm);
        next.write(access.rn, true, written);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn code(words: &[u32]) -> Vec<u8> {
        words.iter().flat_map(|word| word.to_le_bytes()).collect()
    }

    fn run(words: &[u32], pad: Option<(u64, u64)>) -> Result<Flow, Violation> {
        let bytes = code(words);
        let external = BTreeSet::new();
        let landing_pad = move |offset: u64| pad.filter(|(at, _)| *at == offset).map(|(_, to)| to);
        analyze(&FlowInput {
            code: &bytes,
            body_len: bytes.len() as u64,
            external_branches: &external,
            landing_pad: &landing_pad,
        })
    }

    #[test]
    fn canonical_frame_is_tracked_to_the_call() {
        // stp x20, x19, [sp, #-32]!; stp x29, x30, [sp, #16]; add x29, sp, #16
        // bl; ldp x29, x30, [sp, #16]; ldp x20, x19, [sp], #32; ret
        let flow = run(
            &[
                0xa9be_4ff4,
                0xa901_7bfd,
                0x9100_43fd,
                0x9400_0000,
                0xa941_7bfd,
                0xa8c2_4ff4,
                0xd65f_03c0,
            ],
            None,
        )
        .expect("flow");
        let state = &flow.calls[&12];
        assert_eq!(state.x[29], Val::Stack(-16));
        assert_eq!(state.mem.get(&-16), Some(&Val::Entry(EhReg::X(29))));
        assert_eq!(state.mem.get(&-8), Some(&Val::Entry(EhReg::X(30))));
        assert_eq!(state.mem.get(&-24), Some(&Val::Entry(EhReg::X(19))));
        assert_eq!(state.mem.get(&-32), Some(&Val::Entry(EhReg::X(20))));
        assert_eq!(state.sp, Val::Stack(-32));
    }

    #[test]
    fn landing_pads_are_reached_through_the_exceptional_edge() {
        // stp x29, x30, [sp, #-16]!; mov x29, sp; bl; ldp; ret; (pad) bl; brk
        let flow = run(
            &[
                0xa9bf_7bfd,
                0x9100_03fd,
                0x9400_0000,
                0xa8c1_7bfd,
                0xd65f_03c0,
                0x9400_0000,
                0xd420_0020,
            ],
            Some((8, 20)),
        )
        .expect("flow");
        assert!(flow.calls.contains_key(&20), "{flow:?}");
        assert_eq!(flow.calls[&20].x[29], Val::Stack(-16));
    }

    #[test]
    fn a_write_to_the_frame_pointer_is_seen() {
        // stp x29, x30, [sp, #-16]!; mov x29, sp; mov x29, x0; bl
        let flow = run(
            &[
                0xa9bf_7bfd,
                0x9100_03fd,
                0xaa00_03fd,
                0x9400_0000,
                0xd65f_03c0,
            ],
            None,
        )
        .expect("flow");
        assert_eq!(flow.calls[&12].x[29], Val::Unknown);
    }

    #[test]
    fn unknown_words_are_refused() {
        let error = run(&[0x0420_0000, 0xd65f_03c0], None).expect_err("SVE word");
        assert_eq!(error.kind, EhObligationKind::FrameFlow);
    }
}
