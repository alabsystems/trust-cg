// trust-cg-verify/wasm_bulk_memory_proofs.rs - MemCopy / MemSet bodies from the emitted bytes
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Reference: WebAssembly Core Specification, Release 2.0 — §4.4.7 (Memory
//            Instructions: memory.copy, memory.fill), §4.4.1-§4.4.5 (local.get
//            / local.set / local.tee, i32.const, i32.eqz, i32.and, if / end,
//            return, unreachable), §5.4 (their encodings: `0xfc 10 0x00 0x00` and
//            `0xfc 11 0x00`).
//
// WHY A WHOLE BODY. trust-ir `MemCopy` / `MemSet` define a ZERO-byte op as a
// no-op that does not touch either pointer. wasm's `memory.copy` /
// `memory.fill` bounds-check the range END first (`d + n` and `s + n`
// against the memory size, in unbounded arithmetic) and trap when it lies past
// the memory even for `n == 0`. The lowering of a trust-ir `MemCopy` /
// `MemSet` therefore never emits the op alone: it binds the count to a local
// and emits the op inside `if (n != 0)`. (`memory.copy` is also emitted, with
// a constant nonzero size, by the aggregate moves — see the scope below.)
// A per-opcode statement of `memory.copy` would compare the wrong thing — it
// REFUTES against trust-ir at a zero-byte copy through a dangling pointer,
// correctly, because the opcode is not the lowering. The unit of evidence is
// the emitted SEQUENCE, so this module runs the REAL emitted function body.
//
// THE TWO SIDES.
//
//   * MACHINE: [`run_bulk_memory_body`] decodes the captured code entry with
//     its own spec-derived instruction table (the `0xfc` sub-indices 10 and 11
//     and their reserved zero bytes are written from the spec, not read from
//     the encoder) and executes it on a concrete two-page memory under the
//     spec's definitions: the bounds check in unbounded arithmetic BEFORE the
//     zero test, `memory.copy` as-if through a temporary (overlap is defined),
//     `memory.fill` writing the low 8 bits of its `i32` operand.
//   * SOURCE: [`trust_ir_bulk_memory_allows`] states the trust-ir contract as a
//     RELATION on (arguments, memory before, outcome), because UB admits every
//     outcome: a zero count must RETURN with the memory unchanged, whatever
//     the pointers; a nonzero count whose ranges lie in the memory must return
//     with exactly the copied (memmove) or filled image; a range that leaves
//     the memory lies outside every live allocation, so the op is UB there and
//     a trap refines it. `MemCopy` without `overlap` additionally makes
//     overlapping ranges UB (they are in one allocation, since the model
//     memory is one); `overlap` (memmove) defines them.
//
// THE OPERANDS. A battery over a finite memory observes an operand bit only
// when some defined, nonzero, in-memory case sets it and the memory image
// tells the two values apart. Two facts carry the operands:
//
//   * OBSERVED BITS: the model memory is `2^OBSERVED_OPERAND_BITS` bytes of an
//     aperiodic pattern, and the battery sets every bit below that of each
//     pointer and of the count (every bit of the fill byte) in a defined case.
//     The credit REQUIRES it: clearing any one of those bits of any operand of
//     the op ([`BulkMemoryControl::OperandMasked`]) must refute on the battery
//     ([`unobserved_operand_bits`]).
//   * PROVENANCE: a bit at or above `OBSERVED_OPERAND_BITS` addresses past the
//     model memory, where every nonzero case is UB and admits any outcome, so
//     no battery sees it. [`bulk_operand_provenance`] walks the body's
//     dataflow and requires the op's operands to BE the function's parameters
//     (`dst`, `src`, `n`; the fill byte as the parameter or its documented
//     `& 0xff` re-canonicalization) and the guard to test exactly `n`. A body
//     that masks, shifts or recomputes an operand fails it by name, whatever
//     bit it touches.
//
// NEGATIVE CONTROLS ([`BulkMemoryControl`]). Each is built from the captured
// body (or, for the copy DIRECTION, from the machine model) and must refute
// inside the credit hook: the body without its guard (the lowering before the
// guard existed) at a zero-byte out-of-memory range; an inverted guard and a
// guard on the destination instead of the count; swapped operands; a forward
// byte loop in place of memmove at an overlap with the destination above the
// source; and operand truncations (the count to 16 and to 8 bits, the copy
// source to 8 bits, bit 1 of the destination cleared, bit 31 of the count
// cleared), each of which the provenance check must refuse and, where its
// divergence lies inside the model memory, the battery must refute at its
// stated class.
//
// WHAT THIS DOES NOT ESTABLISH. It is decided on a finite battery of
// (pointer, pointer-or-byte, count) triples, every stated class present, over
// a two-page memory — not over all 2^96 inputs or every memory size; operand
// bits past the model rest on the provenance check alone, which is a fact
// about this body's dataflow, not an execution. It runs the body of the
// three-parameter functions the captures come from; the same sequence inside
// a larger function reads other local indices, which the lane differentials
// (`wasm_g1_lane_semantics`, `wasm_g3_lane_frames`) exercise, not this. It says
// nothing about the `memory.copy` the memory-carried-value layer emits for
// aggregate moves with a CONSTANT nonzero size (`emit_copy`), which has no
// trust-ir `MemCopy` behind it. A count wider than the address (a `u64` count
// in a module that pins no target) is wrapped to `i32` before the guard; on
// wasm32 the count is a `usize`, so the modelled count is the whole count.

//! Execution of the captured MemCopy / MemSet function bodies against a
//! relational statement of the trust-ir contract, with negative controls.

use std::collections::BTreeSet;
use std::fmt;

use crate::wasm_encoding_proofs::{spec_decode_signed, spec_decode_unsigned};

/// The `0xfc` sub-index of `memory.copy` (spec §5.4.7).
pub const MEMORY_COPY_SUB: u32 = 10;
/// The `0xfc` sub-index of `memory.fill` (spec §5.4.7).
pub const MEMORY_FILL_SUB: u32 = 11;

/// The operand bits the battery observes: bits `0..OBSERVED_OPERAND_BITS` of
/// each pointer and of the count. The model memory is exactly that wide, so a
/// defined nonzero case can set each of them.
pub const OBSERVED_OPERAND_BITS: u32 = 17;

/// Bytes in the model memory: two 64 KiB pages, so a copy of 2^16 bytes has
/// disjoint in-memory ranges and every pointer and count bit below
/// [`OBSERVED_OPERAND_BITS`] is set by some defined case.
pub const MODEL_MEMORY_BYTES: u64 = 1 << OBSERVED_OPERAND_BITS;

/// The trust-ir bulk-memory instruction a captured body lowers.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum BulkMemoryShape {
    /// `MemCopy { overlap: false }` (memcpy: overlapping ranges are UB).
    MemCopy,
    /// `MemCopy { overlap: true }` (memmove).
    MemMove,
    /// `MemSet`.
    MemSet,
}

impl BulkMemoryShape {
    /// Every shape.
    pub const ALL: [BulkMemoryShape; 3] = [
        BulkMemoryShape::MemCopy,
        BulkMemoryShape::MemMove,
        BulkMemoryShape::MemSet,
    ];

    /// The `0xfc` sub-index of the wasm op the shape lowers to.
    pub fn sub_opcode(self) -> u32 {
        match self {
            BulkMemoryShape::MemCopy | BulkMemoryShape::MemMove => MEMORY_COPY_SUB,
            BulkMemoryShape::MemSet => MEMORY_FILL_SUB,
        }
    }
}

/// One captured body: `(shape, the code ENTRY — locals vector and expression —
/// of the three-parameter function that performs the shape once)`.
pub type EmittedBulkMemoryBody = (BulkMemoryShape, &'static [u8]);

/// The code entries the real wasm backend emits for `(dst: ptr, src: ptr, n:
/// usize) -> () { memcopy [overlap] dst, src, n }` and `(dst: ptr, byte: u8, n:
/// usize) -> () { memset dst, byte, n }`, captured from the module's code
/// section.
///
/// Like the other captured corpora in this crate it exists because the credit
/// hook cannot compile, and it cannot rot:
/// `tests/support/wasm_bulk_memory_live_emit.rs` recompiles all three through
/// the live backend and requires byte identity, from `wasm_encoding_gate` and
/// from the ratio-pinning `coverage_gate_tests`.
pub const EMITTED_BULK_MEMORY_BODIES: &[EmittedBulkMemoryBody] = &[
    // local.get 2; if; local.get 0; local.get 1; local.get 2; memory.copy 0
    // 0; end; end. The lowering copies the count into a fresh local; the
    // emission pass coalesces that copy into parameter 2, and its control
    // cleanup deletes the final `return` and the `unreachable` after it.
    (
        BulkMemoryShape::MemCopy,
        &[
            0x00, 0x20, 0x02, 0x04, 0x40, 0x20, 0x00, 0x20, 0x01, 0x20, 0x02, 0xfc, 0x0a, 0x00,
            0x00, 0x0b, 0x0b,
        ],
    ),
    (
        BulkMemoryShape::MemMove,
        &[
            0x00, 0x20, 0x02, 0x04, 0x40, 0x20, 0x00, 0x20, 0x01, 0x20, 0x02, 0xfc, 0x0a, 0x00,
            0x00, 0x0b, 0x0b,
        ],
    ),
    // The u8 parameter's entry re-canonicalization (local.get 1; i32.const
    // 255; i32.and; local.set 1), then the memory.fill 0 guarded on
    // parameter 2.
    (
        BulkMemoryShape::MemSet,
        &[
            0x00, 0x20, 0x01, 0x41, 0xff, 0x01, 0x71, 0x21, 0x01, 0x20, 0x02, 0x04, 0x40, 0x20,
            0x00, 0x20, 0x01, 0x20, 0x02, 0xfc, 0x0b, 0x00, 0x0b, 0x0b,
        ],
    ),
];

/// The shapes whose coverage row a `0xfc` sub-index is: `memory.copy` (10)
/// lowers both `MemCopy` settings, `memory.fill` (11) lowers `MemSet`. `None`
/// for every other sub-index.
pub fn bulk_memory_row(sub: u32) -> Option<&'static [BulkMemoryShape]> {
    match sub {
        MEMORY_COPY_SUB => Some(&[BulkMemoryShape::MemCopy, BulkMemoryShape::MemMove]),
        MEMORY_FILL_SUB => Some(&[BulkMemoryShape::MemSet]),
        _ => None,
    }
}

// ===========================================================================
// The decoder: a spec-derived table of exactly the instructions a body uses
// ===========================================================================

/// One decoded instruction of a bulk-memory body.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BulkInst {
    /// `unreachable` (0x00).
    Unreachable,
    /// `nop` (0x01).
    Nop,
    /// `if` with the empty block type (0x04 0x40).
    If,
    /// `else` (0x05).
    Else,
    /// `end` (0x0b).
    End,
    /// `return` (0x0f).
    Return,
    /// `drop` (0x1a).
    Drop,
    /// `local.get` (0x20).
    LocalGet(u32),
    /// `local.set` (0x21).
    LocalSet(u32),
    /// `local.tee` (0x22).
    LocalTee(u32),
    /// `i32.const` (0x41).
    I32Const(i32),
    /// `i32.eqz` (0x45).
    I32Eqz,
    /// `i32.and` (0x71).
    I32And,
    /// `memory.copy` (0xfc 10 0x00 0x00).
    MemoryCopy,
    /// `memory.fill` (0xfc 11 0x00).
    MemoryFill,
}

/// A decoded code entry: the declared locals (after the parameters) and the
/// instruction sequence, including the function's closing `end`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DecodedBulkBody {
    /// Value type byte of every declared local, in index order.
    pub locals: Vec<u8>,
    /// The instructions, in order.
    pub insts: Vec<BulkInst>,
}

impl DecodedBulkBody {
    /// How many times the body contains the op with `0xfc` sub-index `sub`.
    pub fn count_op(&self, sub: u32) -> usize {
        let want = match sub {
            MEMORY_COPY_SUB => BulkInst::MemoryCopy,
            MEMORY_FILL_SUB => BulkInst::MemoryFill,
            _ => return 0,
        };
        self.insts.iter().filter(|i| **i == want).count()
    }
}

const VT_I32: u8 = 0x7f;

/// Decode a code entry. FAILS CLOSED on any byte outside the modelled table:
/// an unknown opcode has an unknown meaning, so no verdict may rest on the
/// part of the body that follows it.
pub fn decode_bulk_body(entry: &[u8]) -> Result<DecodedBulkBody, String> {
    let mut at = 0usize;
    let uleb = |at: &mut usize, what: &str| -> Result<u32, String> {
        let (v, used) = spec_decode_unsigned(&entry[(*at).min(entry.len())..], 32)
            .map_err(|e| format!("{what}: {e:?}"))?;
        *at += used;
        u32::try_from(v).map_err(|_| format!("{what}: {v} does not fit in u32"))
    };
    let byte = |at: &mut usize, what: &str| -> Result<u8, String> {
        let b = *entry
            .get(*at)
            .ok_or_else(|| format!("truncated while reading {what}"))?;
        *at += 1;
        Ok(b)
    };
    let mut locals = Vec::new();
    for _ in 0..uleb(&mut at, "local run count")? {
        let n = uleb(&mut at, "local run length")?;
        let vt = byte(&mut at, "local type")?;
        if n > 1024 {
            return Err(format!("a run of {n} locals is outside the modelled body"));
        }
        locals.extend(std::iter::repeat_n(vt, n as usize));
    }
    let mut insts = Vec::new();
    while at < entry.len() {
        let op = byte(&mut at, "opcode")?;
        let inst = match op {
            0x00 => BulkInst::Unreachable,
            0x01 => BulkInst::Nop,
            0x04 => match byte(&mut at, "blocktype")? {
                0x40 => BulkInst::If,
                bt => return Err(format!("`if` with block type 0x{bt:02x} is not modelled")),
            },
            0x05 => BulkInst::Else,
            0x0b => BulkInst::End,
            0x0f => BulkInst::Return,
            0x1a => BulkInst::Drop,
            0x20 => BulkInst::LocalGet(uleb(&mut at, "local.get index")?),
            0x21 => BulkInst::LocalSet(uleb(&mut at, "local.set index")?),
            0x22 => BulkInst::LocalTee(uleb(&mut at, "local.tee index")?),
            0x41 => {
                let (v, used) = spec_decode_signed(&entry[at..], 32)
                    .map_err(|e| format!("i32.const: {e:?}"))?;
                at += used;
                BulkInst::I32Const(v as i32)
            }
            0x45 => BulkInst::I32Eqz,
            0x71 => BulkInst::I32And,
            0xfc => match uleb(&mut at, "0xfc sub-index")? {
                MEMORY_COPY_SUB => {
                    let (a, b) = (byte(&mut at, "memidx")?, byte(&mut at, "memidx")?);
                    if (a, b) != (0, 0) {
                        return Err(format!("memory.copy names memories {a}/{b}, not 0/0"));
                    }
                    BulkInst::MemoryCopy
                }
                MEMORY_FILL_SUB => {
                    let a = byte(&mut at, "memidx")?;
                    if a != 0 {
                        return Err(format!("memory.fill names memory {a}, not 0"));
                    }
                    BulkInst::MemoryFill
                }
                sub => return Err(format!("0xfc sub-index {sub} is not modelled")),
            },
            other => return Err(format!("opcode 0x{other:02x} is not modelled")),
        };
        insts.push(inst);
    }
    Ok(DecodedBulkBody { locals, insts })
}

// ===========================================================================
// MACHINE side: the spec's instruction semantics on a concrete memory
// ===========================================================================

/// How the machine side executes `memory.copy`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CopyModel {
    /// The spec: as if through a temporary, so overlap is defined.
    Spec,
    /// A forward byte loop — NOT the spec; a negative control that shows the
    /// battery observes the copy direction.
    ForwardBytes,
}

/// The outcome of running a body.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BulkOutcome {
    /// The function returned; the memory after the call.
    Returned(Vec<u8>),
    /// The function trapped.
    Trapped,
}

/// Does `[p, p + n)` lie inside a memory of `len` bytes (unbounded
/// arithmetic, as the spec computes the range end)?
fn range_in(p: u32, n: u32, len: usize) -> bool {
    u64::from(p) + u64::from(n) <= len as u64
}

/// The index of the `else` or `end` closing the `if` at `at` (`want_else`
/// stops at a same-depth `else`, too).
fn skip_block(insts: &[BulkInst], at: usize, want_else: bool) -> Result<usize, String> {
    let mut depth = 0usize;
    for (k, inst) in insts.iter().enumerate().skip(at + 1) {
        match inst {
            BulkInst::If => depth += 1,
            BulkInst::Else if depth == 0 && want_else => return Ok(k),
            BulkInst::End if depth == 0 => return Ok(k),
            BulkInst::End => depth -= 1,
            _ => {}
        }
    }
    Err(format!("the `if` at instruction {at} is not closed"))
}

/// Execute a decoded body of the `(i32, i32, i32) -> ()` function on `memory`
/// with arguments `args`. `Err` when the body leaves the modelled subset (a
/// local that is not an `i32`, a stack underflow, an unclosed block) — a
/// refusal, never a verdict.
pub fn run_bulk_memory_body(
    body: &DecodedBulkBody,
    args: [u32; 3],
    memory: &[u8],
    model: CopyModel,
) -> Result<BulkOutcome, String> {
    if let Some(vt) = body.locals.iter().find(|&&vt| vt != VT_I32) {
        return Err(format!(
            "a declared local of type 0x{vt:02x} is not modelled"
        ));
    }
    let mut locals: Vec<u32> = args.to_vec();
    locals.extend(std::iter::repeat_n(0, body.locals.len()));
    let mut mem = memory.to_vec();
    let mut stack: Vec<u32> = Vec::new();
    let pop = |stack: &mut Vec<u32>, at: usize| {
        stack
            .pop()
            .ok_or_else(|| format!("stack underflow at instruction {at}"))
    };
    let nlocals = locals.len();
    let local = |k: u32, at: usize| -> Result<usize, String> {
        let k = k as usize;
        if k < nlocals {
            Ok(k)
        } else {
            Err(format!("local {k} out of range at instruction {at}"))
        }
    };
    let insts = &body.insts;
    let mut open_ifs = 0usize;
    let mut pc = 0usize;
    while pc < insts.len() {
        let at = pc;
        pc += 1;
        match insts[at] {
            BulkInst::Unreachable => return Ok(BulkOutcome::Trapped),
            BulkInst::Nop => {}
            BulkInst::If => {
                if pop(&mut stack, at)? != 0 {
                    open_ifs += 1;
                } else {
                    let k = skip_block(insts, at, true)?;
                    if insts[k] == BulkInst::Else {
                        open_ifs += 1;
                    }
                    pc = k + 1;
                }
            }
            BulkInst::Else => {
                // Reached from the taken arm: skip the other one.
                pc = skip_block(insts, at, false)? + 1;
                open_ifs = open_ifs
                    .checked_sub(1)
                    .ok_or_else(|| format!("`else` outside an `if` at {at}"))?;
            }
            BulkInst::End => {
                if open_ifs == 0 {
                    return Ok(BulkOutcome::Returned(mem));
                }
                open_ifs -= 1;
            }
            BulkInst::Return => return Ok(BulkOutcome::Returned(mem)),
            BulkInst::Drop => {
                pop(&mut stack, at)?;
            }
            BulkInst::LocalGet(k) => {
                let k = local(k, at)?;
                stack.push(locals[k]);
            }
            BulkInst::LocalSet(k) => {
                let k = local(k, at)?;
                locals[k] = pop(&mut stack, at)?;
            }
            BulkInst::LocalTee(k) => {
                let k = local(k, at)?;
                let v = *stack
                    .last()
                    .ok_or_else(|| format!("stack underflow at instruction {at}"))?;
                locals[k] = v;
            }
            BulkInst::I32Const(v) => stack.push(v as u32),
            BulkInst::I32Eqz => {
                let v = pop(&mut stack, at)?;
                stack.push(u32::from(v == 0));
            }
            BulkInst::I32And => {
                let b = pop(&mut stack, at)?;
                let a = pop(&mut stack, at)?;
                stack.push(a & b);
            }
            BulkInst::MemoryCopy => {
                let n = pop(&mut stack, at)?;
                let s = pop(&mut stack, at)?;
                let d = pop(&mut stack, at)?;
                if !range_in(s, n, mem.len()) || !range_in(d, n, mem.len()) {
                    return Ok(BulkOutcome::Trapped);
                }
                let (d, s, n) = (d as usize, s as usize, n as usize);
                match model {
                    CopyModel::Spec => mem.copy_within(s..s + n, d),
                    CopyModel::ForwardBytes => {
                        for i in 0..n {
                            mem[d + i] = mem[s + i];
                        }
                    }
                }
            }
            BulkInst::MemoryFill => {
                let n = pop(&mut stack, at)?;
                let val = pop(&mut stack, at)?;
                let d = pop(&mut stack, at)?;
                if !range_in(d, n, mem.len()) {
                    return Ok(BulkOutcome::Trapped);
                }
                let (d, n) = (d as usize, n as usize);
                mem[d..d + n].fill(val as u8);
            }
        }
    }
    Err("the body ran off its end without a closing `end`".to_string())
}

// ===========================================================================
// SOURCE side: the trust-ir contract, as a relation
// ===========================================================================

/// Does the trust-ir contract of `shape` admit `outcome` for arguments `args`
/// on memory `before`?
///
/// `args` are `(dst, src, n)` for a copy and `(dst, byte, n)` for a fill. The
/// fill byte is the trust-ir `u8` operand, so its `i32` carrier is canonical
/// (invariant N); the battery passes only canonical carriers.
pub fn trust_ir_bulk_memory_allows(
    shape: BulkMemoryShape,
    args: [u32; 3],
    before: &[u8],
    outcome: &BulkOutcome,
) -> bool {
    let [d, b, n] = args;
    if n == 0 {
        // A no-op that does not touch either pointer.
        return *outcome == BulkOutcome::Returned(before.to_vec());
    }
    let len = before.len();
    let mut want = before.to_vec();
    match shape {
        BulkMemoryShape::MemCopy | BulkMemoryShape::MemMove => {
            if !range_in(d, n, len) || !range_in(b, n, len) {
                return true; // outside every live allocation: UB
            }
            let (d, s, n) = (d as usize, b as usize, n as usize);
            let overlap = d < s + n && s < d + n;
            if overlap && shape == BulkMemoryShape::MemCopy {
                return true; // memcpy of overlapping ranges: UB
            }
            want.copy_within(s..s + n, d);
        }
        BulkMemoryShape::MemSet => {
            if !range_in(d, n, len) {
                return true;
            }
            let (d, n) = (d as usize, n as usize);
            want[d..d + n].fill(b as u8);
        }
    }
    *outcome == BulkOutcome::Returned(want)
}

// ===========================================================================
// The battery
// ===========================================================================

/// The input classes the battery reaches. Every class must be present for a
/// body to credit, and every negative control names the class it refutes at.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum BulkInputClass {
    /// `n == 0` with every range end inside the memory.
    ZeroLengthInBounds,
    /// `n == 0` with a pointer whose (empty) range ends past the memory.
    ZeroLengthOutOfBounds,
    /// `n > 0`, every range inside the memory, copy ranges disjoint.
    InBounds,
    /// `n > 0` with a range ending exactly at the memory's end.
    ExactEnd,
    /// A copy whose destination overlaps its source from above.
    OverlapDestinationAbove,
    /// A copy whose destination overlaps its source from below.
    OverlapDestinationBelow,
    /// `n > 0` with a range past the memory (UB: a trap refines it).
    OutOfBounds,
}

impl fmt::Display for BulkInputClass {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(self, f)
    }
}

/// The battery for `shape`: `(class, args)` pairs.
///
/// Besides the class representatives it sets every observed bit (below
/// [`OBSERVED_OPERAND_BITS`]) of each operand in a defined nonzero case: a
/// count of `2^b` between disjoint in-memory ranges, a destination and a
/// source (or fill byte) of `2^b` with a small count.
pub fn bulk_memory_battery(shape: BulkMemoryShape) -> Vec<(BulkInputClass, [u32; 3])> {
    use BulkInputClass as C;
    let m = MODEL_MEMORY_BYTES as u32;
    let half = m / 2;
    // A pointer far from every `2^b` with `b < OBSERVED_OPERAND_BITS - 1`
    // and from `half`, so a 4-byte range there is disjoint from theirs.
    let far = half + half / 2 + 1000;
    let mut v = Vec::new();
    match shape {
        BulkMemoryShape::MemCopy | BulkMemoryShape::MemMove => {
            for a in [[0, 0, 0], [100, 200, 0], [m - 1, 17, 0], [m, m, 0]] {
                v.push((C::ZeroLengthInBounds, a));
            }
            for a in [
                [m + 1, 0, 0],
                [0, m + 1, 0],
                [4_000_000_000, 4_000_000_000, 0],
                [u32::MAX, 5, 0],
            ] {
                v.push((C::ZeroLengthOutOfBounds, a));
            }
            for a in [[100, 300, 16], [0, m - 8, 8], [m - 8, 0, 8], [40, 7, 1]] {
                v.push((C::InBounds, a));
            }
            for b in 0..OBSERVED_OPERAND_BITS {
                let bit = 1u32 << b;
                // The count: `[0, 2^b)` from `[half, half + 2^b)`; the
                // largest ends exactly at the memory's end.
                let class = if half + bit == m {
                    C::ExactEnd
                } else {
                    C::InBounds
                };
                v.push((class, [0, half, bit]));
                // The destination, then the source, at `2^b`.
                v.push((C::InBounds, [bit, far, 4]));
                v.push((C::InBounds, [far, bit, 4]));
            }
            for a in [[m - 16, 100, 16], [100, m - 16, 16]] {
                v.push((C::ExactEnd, a));
            }
            for a in [[104, 100, 16], [1, 0, 64]] {
                v.push((C::OverlapDestinationAbove, a));
            }
            for a in [[100, 104, 16], [0, 1, 64]] {
                v.push((C::OverlapDestinationBelow, a));
            }
            for a in [
                [m - 15, 0, 16],
                [0, m - 15, 16],
                [0xffff_fff0, 0, 0x20],
                [0, 0, u32::MAX],
            ] {
                v.push((C::OutOfBounds, a));
            }
        }
        BulkMemoryShape::MemSet => {
            for a in [[0, 0x5a, 0], [m, 0xff, 0], [m - 1, 1, 0]] {
                v.push((C::ZeroLengthInBounds, a));
            }
            for a in [[m + 1, 0x5a, 0], [4_000_000_000, 0xff, 0], [u32::MAX, 1, 0]] {
                v.push((C::ZeroLengthOutOfBounds, a));
            }
            for a in [[100, 0x5a, 16], [0, 0, 8], [7, 0xff, 1], [100, 0x80, 300]] {
                v.push((C::InBounds, a));
            }
            for b in 0..OBSERVED_OPERAND_BITS {
                let bit = 1u32 << b;
                v.push((C::InBounds, [0, 0x5a, bit]));
                v.push((C::InBounds, [bit, 0xa5, 4]));
            }
            // The fill byte: every bit of the `u8` operand.
            for b in 0..8 {
                v.push((C::InBounds, [100, 1u32 << b, 4]));
            }
            for a in [[m - 16, 0xa5, 16], [m - 1, 0x01, 1], [0, 0x3c, m]] {
                v.push((C::ExactEnd, a));
            }
            for a in [[m - 15, 0x5a, 16], [0xffff_fff0, 1, 0x20], [0, 2, u32::MAX]] {
                v.push((C::OutOfBounds, a));
            }
        }
    }
    v
}

/// The memory every battery case starts from: an aperiodic byte pattern (a
/// multiplicative hash of the address), so a copy from the wrong place or of
/// the wrong length changes an observed byte — also when the wrong source is
/// a multiple of 256 away, which a pattern periodic in the address would hide.
pub fn initial_memory() -> Vec<u8> {
    (0..MODEL_MEMORY_BYTES)
        .map(|i| {
            let x = (i as u32).wrapping_mul(0x9e37_79b1);
            (x ^ (x >> 13) ^ (x >> 24)) as u8
        })
        .collect()
}

/// The verdict of running one body over the whole battery.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct BulkMemoryVerdict {
    /// Why the body could not be run at all (fail closed: no verdict).
    pub refusal: Option<String>,
    /// Classes at which some input's outcome is outside the contract.
    pub refuted_classes: BTreeSet<BulkInputClass>,
    /// The first counterexample per refuted class, for diagnostics.
    pub witnesses: Vec<String>,
    /// Classes the battery reached.
    pub classes_seen: BTreeSet<BulkInputClass>,
    /// Inputs run.
    pub cases: usize,
}

impl BulkMemoryVerdict {
    /// The body agrees with the contract on every input of every class.
    pub fn holds(&self) -> bool {
        self.refusal.is_none() && self.refuted_classes.is_empty() && self.cases > 0
    }
}

/// Run `body` as `shape` over the battery and compare with the contract.
pub fn check_bulk_memory_body(
    shape: BulkMemoryShape,
    body: &DecodedBulkBody,
    model: CopyModel,
) -> BulkMemoryVerdict {
    let before = initial_memory();
    let mut v = BulkMemoryVerdict::default();
    for (class, args) in bulk_memory_battery(shape) {
        v.classes_seen.insert(class);
        v.cases += 1;
        let outcome = match run_bulk_memory_body(body, args, &before, model) {
            Ok(o) => o,
            Err(why) => {
                v.refusal = Some(why);
                return v;
            }
        };
        if !trust_ir_bulk_memory_allows(shape, args, &before, &outcome)
            && v.refuted_classes.insert(class)
        {
            let what = match &outcome {
                BulkOutcome::Trapped => "trapped".to_string(),
                BulkOutcome::Returned(_) => "returned a memory the contract forbids".to_string(),
            };
            v.witnesses
                .push(format!("{shape:?}{args:?} [{class}]: the body {what}"));
        }
    }
    v
}

// ===========================================================================
// Negative controls
// ===========================================================================

/// A deliberately wrong variant of a captured body (or of the copy model).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum BulkMemoryControl {
    /// The body without its `if (n != 0)` guard — the lowering before the
    /// guard existed.
    Unguarded,
    /// The guard tests `n == 0` instead of `n != 0`.
    InvertedGuard,
    /// The guard tests the destination pointer instead of the count.
    GuardOnDestination,
    /// The first two operands of the op are pushed in the other order.
    SwappedOperands,
    /// `memory.copy` executed as a forward byte loop (copy shapes only; the
    /// `overlap = false` shape leaves overlap UB, so only memmove applies).
    ForwardByteCopy,
    /// Operand `operand` of the op (0 = destination, 1 = source or fill byte,
    /// 2 = count) reaches it through `i32.const mask; i32.and`: a lowering
    /// that truncates or drops bits of the operand.
    OperandMasked {
        /// The operand position on the op's stack signature.
        operand: usize,
        /// The mask applied to it.
        mask: u32,
    },
}

impl BulkMemoryControl {
    /// Every named control.
    pub const ALL: [BulkMemoryControl; 10] = [
        BulkMemoryControl::Unguarded,
        BulkMemoryControl::InvertedGuard,
        BulkMemoryControl::GuardOnDestination,
        BulkMemoryControl::SwappedOperands,
        BulkMemoryControl::ForwardByteCopy,
        // The count truncated to 16 and to 8 bits.
        BulkMemoryControl::OperandMasked {
            operand: 2,
            mask: 0xffff,
        },
        BulkMemoryControl::OperandMasked {
            operand: 2,
            mask: 0xff,
        },
        // The copy source truncated to 8 bits.
        BulkMemoryControl::OperandMasked {
            operand: 1,
            mask: 0xff,
        },
        // Bit 1 of the destination cleared.
        BulkMemoryControl::OperandMasked {
            operand: 0,
            mask: !2,
        },
        // Bit 31 of the count cleared: past every modelled memory, so only
        // the provenance check can see it.
        BulkMemoryControl::OperandMasked {
            operand: 2,
            mask: 0x7fff_ffff,
        },
    ];

    /// Whether the control is meaningful for `shape`.
    pub fn applies_to(self, shape: BulkMemoryShape) -> bool {
        match self {
            BulkMemoryControl::ForwardByteCopy => shape == BulkMemoryShape::MemMove,
            // `& 0xff` of the canonical fill byte is the identity (it is the
            // body's own re-canonicalization), so only a copy source applies.
            BulkMemoryControl::OperandMasked { operand: 1, mask } => {
                shape != BulkMemoryShape::MemSet || mask & 0xff != 0xff
            }
            _ => true,
        }
    }

    /// The class the control must refute at on the battery, or `None` for an
    /// operand mask whose divergence lies wholly past the model memory — the
    /// provenance check alone refuses it.
    pub fn stated_class(self, shape: BulkMemoryShape) -> Option<BulkInputClass> {
        let copy = shape != BulkMemoryShape::MemSet;
        Some(match self {
            BulkMemoryControl::Unguarded | BulkMemoryControl::GuardOnDestination => {
                BulkInputClass::ZeroLengthOutOfBounds
            }
            BulkMemoryControl::InvertedGuard | BulkMemoryControl::SwappedOperands => {
                BulkInputClass::InBounds
            }
            BulkMemoryControl::ForwardByteCopy => BulkInputClass::OverlapDestinationAbove,
            // A copy of 2^16 bytes between disjoint ranges fills the model
            // memory exactly, so the 16-bit count truncation shows at its end.
            BulkMemoryControl::OperandMasked {
                operand: 2,
                mask: 0xffff,
            } if copy => BulkInputClass::ExactEnd,
            // A mask clearing only bits at or above OBSERVED_OPERAND_BITS
            // changes no defined case of the battery.
            BulkMemoryControl::OperandMasked { mask, .. }
                if !mask & ((1u32 << OBSERVED_OPERAND_BITS) - 1) == 0 =>
            {
                return None;
            }
            BulkMemoryControl::OperandMasked { .. } => BulkInputClass::InBounds,
        })
    }

    /// Build the control from a decoded captured body: the mutated body and
    /// the copy model to run it under. `None` when the body does not have the
    /// guarded shape the control mutates (which itself fails the credit).
    pub fn build(self, body: &DecodedBulkBody) -> Option<(DecodedBulkBody, CopyModel)> {
        let guard = body.insts.iter().position(|i| *i == BulkInst::If)?;
        let cond = guard.checked_sub(1)?;
        if !matches!(body.insts[cond], BulkInst::LocalGet(_)) {
            return None;
        }
        let close = skip_block(&body.insts, guard, false).ok()?;
        let mut out = body.clone();
        match self {
            BulkMemoryControl::Unguarded => {
                out.insts.remove(close);
                out.insts.remove(guard);
                out.insts.remove(cond);
            }
            BulkMemoryControl::InvertedGuard => out.insts.insert(guard, BulkInst::I32Eqz),
            BulkMemoryControl::GuardOnDestination => out.insts[cond] = BulkInst::LocalGet(0),
            BulkMemoryControl::SwappedOperands => {
                let (a, b) = (guard + 1, guard + 2);
                if !matches!(out.insts.get(a), Some(BulkInst::LocalGet(_)))
                    || !matches!(out.insts.get(b), Some(BulkInst::LocalGet(_)))
                {
                    return None;
                }
                out.insts.swap(a, b);
            }
            BulkMemoryControl::ForwardByteCopy => return Some((out, CopyModel::ForwardBytes)),
            BulkMemoryControl::OperandMasked { operand, mask } => {
                out = mask_operand(body, operand, mask)?;
            }
        }
        Some((out, CopyModel::Spec))
    }
}

/// `body` with `i32.const mask; i32.and` inserted after the push of operand
/// `operand` of its bulk op. `None` unless the op is immediately preceded by
/// three `local.get`s (its three operand pushes) and `operand < 3`.
pub fn mask_operand(body: &DecodedBulkBody, operand: usize, mask: u32) -> Option<DecodedBulkBody> {
    let op = body
        .insts
        .iter()
        .position(|i| matches!(i, BulkInst::MemoryCopy | BulkInst::MemoryFill))?;
    let first = op.checked_sub(3)?;
    if operand >= 3
        || !body.insts[first..op]
            .iter()
            .all(|i| matches!(i, BulkInst::LocalGet(_)))
    {
        return None;
    }
    let mut out = body.clone();
    let at = first + operand + 1;
    out.insts.insert(at, BulkInst::I32And);
    out.insts.insert(at, BulkInst::I32Const(mask as i32));
    Some(out)
}

// ===========================================================================
// Operand provenance: the op's operands are the function's parameters
// ===========================================================================

/// What a value on the body's operand stack is, in terms of the function's
/// inputs.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum OperandSource {
    /// Parameter `k` as passed.
    Param(u32),
    /// An `i32.const`.
    Const(i32),
    /// `i32.and` of two sources.
    And(Box<OperandSource>, Box<OperandSource>),
    /// `i32.eqz` of a source.
    Eqz(Box<OperandSource>),
    /// A value the walk does not name (a local written on only one arm of an
    /// `if`).
    Unknown,
}

impl fmt::Display for OperandSource {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            OperandSource::Param(k) => write!(f, "param {k}"),
            OperandSource::Const(c) => write!(f, "{c}"),
            OperandSource::And(a, b) => write!(f, "({a} & {b})"),
            OperandSource::Eqz(a) => write!(f, "({a} == 0)"),
            OperandSource::Unknown => write!(f, "<unknown>"),
        }
    }
}

/// What reaches the body's bulk op: its three operands and the condition of
/// every `if` enclosing it, outermost first.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BulkOperandSources {
    /// The op's operands in stack order (destination, source or byte, count).
    pub operands: [OperandSource; 3],
    /// The conditions of the enclosing `if`s.
    pub guards: Vec<OperandSource>,
}

/// Walk `body`'s dataflow from its parameters to its bulk op. `Err` when the
/// body leaves the walked subset (`else`, a `return` or `unreachable` inside
/// an `if`, a stack underflow, an out-of-range local, no op, or more than one).
pub fn bulk_operand_sources(body: &DecodedBulkBody) -> Result<BulkOperandSources, String> {
    use OperandSource as S;
    let mut locals: Vec<S> = (0..3).map(S::Param).collect();
    locals.extend(std::iter::repeat_n(S::Const(0), body.locals.len()));
    let mut stack: Vec<S> = Vec::new();
    // Per open `if`: its condition and the locals at its entry.
    let mut open: Vec<(S, Vec<S>)> = Vec::new();
    let mut found: Option<BulkOperandSources> = None;
    let pop = |stack: &mut Vec<S>, at: usize| {
        stack
            .pop()
            .ok_or_else(|| format!("stack underflow at instruction {at}"))
    };
    for (at, inst) in body.insts.iter().enumerate() {
        let local = |k: u32| -> Result<usize, String> {
            let k = k as usize;
            if k < locals.len() {
                Ok(k)
            } else {
                Err(format!("local {k} out of range at instruction {at}"))
            }
        };
        match *inst {
            BulkInst::Nop => {}
            BulkInst::If => {
                let cond = pop(&mut stack, at)?;
                open.push((cond, locals.clone()));
            }
            BulkInst::Else => {
                return Err(format!(
                    "`else` at instruction {at} is outside the walked subset"
                ));
            }
            BulkInst::End => match open.pop() {
                // A local written inside the arm holds its entry value on the
                // path that skips the arm.
                Some((_, entry)) => {
                    for (now, before) in locals.iter_mut().zip(entry) {
                        if *now != before {
                            *now = S::Unknown;
                        }
                    }
                }
                None => break,
            },
            BulkInst::Return | BulkInst::Unreachable => {
                if !open.is_empty() {
                    return Err(format!(
                        "a return or trap inside an `if` at instruction {at} is outside the                          walked subset"
                    ));
                }
                break;
            }
            BulkInst::Drop => {
                pop(&mut stack, at)?;
            }
            BulkInst::LocalGet(k) => stack.push(locals[local(k)?].clone()),
            BulkInst::LocalSet(k) => {
                let k = local(k)?;
                locals[k] = pop(&mut stack, at)?;
            }
            BulkInst::LocalTee(k) => {
                let k = local(k)?;
                locals[k] = stack
                    .last()
                    .cloned()
                    .ok_or_else(|| format!("stack underflow at instruction {at}"))?;
            }
            BulkInst::I32Const(c) => stack.push(S::Const(c)),
            BulkInst::I32Eqz => {
                let a = pop(&mut stack, at)?;
                stack.push(S::Eqz(Box::new(a)));
            }
            BulkInst::I32And => {
                let b = pop(&mut stack, at)?;
                let a = pop(&mut stack, at)?;
                stack.push(S::And(Box::new(a), Box::new(b)));
            }
            BulkInst::MemoryCopy | BulkInst::MemoryFill => {
                let n = pop(&mut stack, at)?;
                let b = pop(&mut stack, at)?;
                let d = pop(&mut stack, at)?;
                if found.is_some() {
                    return Err("the body contains more than one bulk op".to_string());
                }
                found = Some(BulkOperandSources {
                    operands: [d, b, n],
                    guards: open.iter().map(|(c, _)| c.clone()).collect(),
                });
            }
        }
    }
    found.ok_or_else(|| "the body contains no bulk op".to_string())
}

/// The operand-provenance check: `Ok` exactly when the op's destination is
/// parameter 0, its count is parameter 2, its second operand is parameter 1
/// (for `memory.fill`, also parameter 1 `& 0xff`, the `u8` re-canonicalization
/// that leaves the low byte `memory.fill` writes unchanged), and it sits inside
/// exactly one `if`, whose condition is the count. Every other body is refused
/// with the operand that differs — this is what carries the operand bits no
/// battery over a finite memory can observe.
pub fn bulk_operand_provenance(
    shape: BulkMemoryShape,
    body: &DecodedBulkBody,
) -> Result<(), String> {
    use OperandSource as S;
    let got = bulk_operand_sources(body)?;
    let [d, b, n] = &got.operands;
    let mut wrong = Vec::new();
    if *d != S::Param(0) {
        wrong.push(format!("the destination operand is {d}, not param 0"));
    }
    let byte_mask = S::And(Box::new(S::Param(1)), Box::new(S::Const(0xff)));
    let byte_ok = *b == S::Param(1) || (shape == BulkMemoryShape::MemSet && *b == byte_mask);
    if !byte_ok {
        let what = if shape == BulkMemoryShape::MemSet {
            "fill byte"
        } else {
            "source"
        };
        wrong.push(format!("the {what} operand is {b}, not param 1"));
    }
    if *n != S::Param(2) {
        wrong.push(format!("the count operand is {n}, not param 2"));
    }
    if got.guards != [S::Param(2)] {
        let guards: Vec<String> = got.guards.iter().map(ToString::to_string).collect();
        wrong.push(format!(
            "the op is guarded by [{}], not by exactly `if (param 2)`",
            guards.join(", ")
        ));
    }
    if wrong.is_empty() {
        Ok(())
    } else {
        Err(wrong.join("; "))
    }
}

/// The operand bits the battery does NOT observe on `body` as `shape`: every
/// `(operand, bit)` with `bit < OBSERVED_OPERAND_BITS` (below 8 for the fill
/// byte) whose clearing, by [`mask_operand`], the battery fails to refute.
/// `Err` when a mask cannot be built on the body.
pub fn unobserved_operand_bits(
    shape: BulkMemoryShape,
    body: &DecodedBulkBody,
) -> Result<Vec<(usize, u32)>, String> {
    let mut missed = Vec::new();
    for operand in 0..3 {
        let bits = if operand == 1 && shape == BulkMemoryShape::MemSet {
            8
        } else {
            OBSERVED_OPERAND_BITS
        };
        for bit in 0..bits {
            let masked = mask_operand(body, operand, !(1u32 << bit))
                .ok_or_else(|| format!("operand {operand} cannot be masked on the body"))?;
            let v = check_bulk_memory_body(shape, &masked, CopyModel::Spec);
            if v.refusal.is_some() || v.refuted_classes.is_empty() {
                missed.push((operand, bit));
            }
        }
    }
    Ok(missed)
}

// ===========================================================================
// The coverage-gate credit hook
// ===========================================================================

/// Why the rows of `0xfc` sub-index `sub` do NOT credit over `bodies` — empty
/// when they do.
///
/// A row credits only when EVERY shape it lowers has exactly one captured
/// body that decodes, contains the op exactly once, passes the operand
/// provenance check, agrees with the contract on every input of a battery
/// reaching every class, observes every operand bit below
/// [`OBSERVED_OPERAND_BITS`], and whose every applicable negative control
/// refutes: at its stated class on the battery, and — for an operand mask —
/// also on the provenance check.
pub fn bulk_memory_credit_failures(sub: u32, bodies: &[EmittedBulkMemoryBody]) -> Vec<String> {
    let Some(shapes) = bulk_memory_row(sub) else {
        return vec![format!("0xfc sub-index {sub} is not a bulk-memory row")];
    };
    let mut failures = Vec::new();
    for &shape in shapes {
        let mine: Vec<&[u8]> = bodies
            .iter()
            .filter(|(s, _)| *s == shape)
            .map(|(_, b)| *b)
            .collect();
        let [captured] = mine.as_slice() else {
            failures.push(format!(
                "{shape:?}: {} captured bodies (exactly one is required)",
                mine.len()
            ));
            continue;
        };
        let body = match decode_bulk_body(captured) {
            Ok(b) => b,
            Err(why) => {
                failures.push(format!("{shape:?}: the body does not decode: {why}"));
                continue;
            }
        };
        if body.count_op(sub) != 1 {
            failures.push(format!(
                "{shape:?}: the body contains the 0xfc {sub} op {} times",
                body.count_op(sub)
            ));
            continue;
        }
        // Both checks run, so a body that fails the provenance check still
        // reports where the battery refutes it.
        if let Err(why) = bulk_operand_provenance(shape, &body) {
            failures.push(format!("{shape:?}: operand provenance: {why}"));
        }
        let v = check_bulk_memory_body(shape, &body, CopyModel::Spec);
        if !v.holds() {
            failures.push(format!("{shape:?}: the body does not hold: {v:?}"));
            continue;
        }
        match unobserved_operand_bits(shape, &body) {
            Ok(missed) if missed.is_empty() => {}
            Ok(missed) => failures.push(format!(
                "{shape:?}: the battery does not observe (operand, bit) {missed:?}"
            )),
            Err(why) => failures.push(format!("{shape:?}: {why}")),
        }
        let every_class: BTreeSet<BulkInputClass> = bulk_memory_battery(shape)
            .into_iter()
            .map(|(c, _)| c)
            .collect();
        for control in BulkMemoryControl::ALL {
            if !control.applies_to(shape) {
                continue;
            }
            let Some((mutated, model)) = control.build(&body) else {
                failures.push(format!(
                    "{shape:?}: {control:?} cannot be built on the body"
                ));
                continue;
            };
            if matches!(control, BulkMemoryControl::OperandMasked { .. })
                && bulk_operand_provenance(shape, &mutated).is_ok()
            {
                failures.push(format!(
                    "{shape:?}: the provenance check accepts {control:?}"
                ));
            }
            let Some(class) = control.stated_class(shape) else {
                continue;
            };
            if !every_class.contains(&class) {
                failures.push(format!(
                    "{shape:?}: {control:?} names class {class}, which the battery never reaches"
                ));
                continue;
            }
            let cv = check_bulk_memory_body(shape, &mutated, model);
            if cv.refusal.is_some() || !cv.refuted_classes.contains(&class) {
                failures.push(format!(
                    "{shape:?}: {control:?} does not refute at {class}: {cv:?}"
                ));
            }
        }
    }
    failures
}

/// The coverage-gate credit hook for the `memory.copy` (10) / `memory.fill`
/// (11) rows over the captured corpus.
pub fn bulk_memory_body_discharges_valid(sub: u32) -> bool {
    bulk_memory_credit_failures(sub, EMITTED_BULK_MEMORY_BODIES).is_empty()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_guarded_hand_body_holds_and_its_unguarded_form_refutes() {
        // local.get 2; local.set 3; local.get 3; if; local.get 0; local.get 1;
        // local.get 3; memory.copy; end; return; end
        let entry = [
            0x01, 0x01, 0x7f, 0x20, 0x02, 0x21, 0x03, 0x20, 0x03, 0x04, 0x40, 0x20, 0x00, 0x20,
            0x01, 0x20, 0x03, 0xfc, 0x0a, 0x00, 0x00, 0x0b, 0x0f, 0x0b,
        ];
        let body = decode_bulk_body(&entry).expect("decodes");
        let v = check_bulk_memory_body(BulkMemoryShape::MemMove, &body, CopyModel::Spec);
        assert!(v.holds(), "{v:#?}");
        let (bare, model) = BulkMemoryControl::Unguarded.build(&body).expect("builds");
        let cv = check_bulk_memory_body(BulkMemoryShape::MemMove, &bare, model);
        assert!(
            cv.refuted_classes
                .contains(&BulkInputClass::ZeroLengthOutOfBounds),
            "{cv:#?}"
        );
    }

    /// The captured bodies pass the provenance check; a truncated count, a
    /// truncated source, a cleared destination bit and a recomputed guard are
    /// each refused by name — including a count mask past every modelled
    /// memory, which no battery can see.
    #[test]
    fn provenance_accepts_the_captures_and_refuses_every_operand_rewrite() {
        for &(shape, entry) in EMITTED_BULK_MEMORY_BODIES {
            let body = decode_bulk_body(entry).expect("decodes");
            bulk_operand_provenance(shape, &body)
                .unwrap_or_else(|e| panic!("{shape:?}: the capture is refused: {e}"));
            for (operand, mask, needle) in [
                (2, 0xffff, "count operand"),
                (2, 0x7fff_ffff, "count operand"),
                (0, !2, "destination operand"),
                (1, 0xff, "operand is"),
            ] {
                if shape == BulkMemoryShape::MemSet && operand == 1 {
                    continue;
                }
                let masked = mask_operand(&body, operand, mask).expect("builds");
                let why = bulk_operand_provenance(shape, &masked)
                    .expect_err("a masked operand must be refused");
                assert!(why.contains(needle), "{shape:?} & {mask:#x}: {why}");
            }
            let (inverted, _) = BulkMemoryControl::InvertedGuard
                .build(&body)
                .expect("builds");
            assert!(bulk_operand_provenance(shape, &inverted).is_err());
        }
    }

    /// The battery observes every bit below OBSERVED_OPERAND_BITS of every
    /// operand of every captured body, and the model memory is not periodic
    /// in any of those bits.
    #[test]
    fn every_observed_operand_bit_is_observed() {
        for &(shape, entry) in EMITTED_BULK_MEMORY_BODIES {
            let body = decode_bulk_body(entry).expect("decodes");
            assert_eq!(
                unobserved_operand_bits(shape, &body),
                Ok(Vec::new()),
                "{shape:?}"
            );
        }
        let mem = initial_memory();
        for b in 0..OBSERVED_OPERAND_BITS {
            let at = 1usize << b;
            assert_ne!(mem[..4], mem[at..at + 4], "the memory repeats at 2^{b}");
        }
    }

    #[test]
    fn the_decoder_fails_closed_outside_its_table() {
        assert!(decode_bulk_body(&[0x00, 0xfc, 0x08, 0x00, 0x00, 0x0b]).is_err());
        assert!(decode_bulk_body(&[0x00, 0xfc, 0x0a, 0x01, 0x00, 0x0b]).is_err());
        assert!(decode_bulk_body(&[0x00, 0x6a, 0x0b]).is_err());
        assert!(decode_bulk_body(&[0x00, 0x04, 0x7f, 0x0b]).is_err());
    }
}
