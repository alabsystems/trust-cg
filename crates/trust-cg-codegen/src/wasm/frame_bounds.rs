// trust-cg-codegen/wasm/frame_bounds.rs - frame-relative access bounds
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! The frame-bounds guard: every CONSTANT-offset access a lowered function
//! makes through its own shadow-stack frame lies inside that frame.
//!
//! A function with a frame of `size` bytes owns exactly `[base, base + size)`
//! (the prologue publishes `base` as the new stack pointer; the caller's
//! frame begins at or above `base + size`). A load, store, `memory.copy` or
//! `memory.fill` that reaches `base + size` or beyond writes or reads the
//! caller's frame — or, for the outermost frame of a module whose stack is the
//! top of its memory (a closed module; a `wasm-ld --stack-first` link with no
//! data), bytes past the end of memory, which traps and leaves the stack
//! pointer lowered.
//!
//! The guard reads the EMITTED body (before local coalescing, so a local
//! holding one SSA value or temporary has one static write; a block
//! parameter's local is written once per incoming edge) with its own decoder:
//!
//! 1. it gives every local the join of every value WRITTEN to it
//!    (flow-insensitively, to a fixpoint): the frame-base local is `base + 0`;
//!    `local.get`, `i32.const` and `i32.add`/`i32.sub` of a frame address and
//!    a constant propagate a set of possible frame offsets; anything else is
//!    unknown. A value whose provenance has one static write per local on it
//!    has a single offset; a set of several offsets comes from a join (a
//!    block parameter receiving different frame slots on different edges);
//! 2. it simulates the operand stack of each straight-line run, forgetting it
//!    at every structured-control instruction and call (a pop from a
//!    forgotten stack is unknown);
//! 3. it refuses the function when an access whose address is a frame offset
//!    `k` (plus the memory argument's offset) and whose extent is a constant
//!    `n` does not satisfy `0 <= k` and `k + n <= size` for EVERY `k` the
//!    address may carry — a definite violation. The set over-approximates the
//!    offsets the address takes, so no execution of that access stays inside
//!    the frame. A single-offset address is therefore always checked exactly.
//!
//! Evidence boundary: an access whose offset set is only PARTLY outside the
//! frame is not refused — the join forgets which edge supplied which offset,
//! and a program may reach the access only on the in-frame edges (a pointer
//! block parameter selecting a large or a small slot, dereferenced at a large
//! offset only when it is the large one). Accesses through a runtime-computed
//! address (a dynamic `Alloca`, an indexed element, a pointer parameter) and a
//! `memory.copy` or `memory.fill` of runtime length are outside the claim, as
//! is a read of a local before any write to it (the zero a local starts with
//! is not a frame address). An immediate a relocation rewrites is unknown. A
//! body the decoder does not recognize is refused rather than passed
//! unchecked.

use std::collections::{BTreeSet, HashSet};

/// The most distinct frame offsets one value may carry before it is treated
/// as unknown (bounds the fixpoint).
const MAX_OFFSETS: usize = 16;

/// Passes after which a local whose value still changes is widened straight
/// to unknown (so the fixpoint terminates in a bounded number of passes).
const WIDEN_AFTER: usize = 8;

/// The frame a body is checked against.
#[derive(Debug, Clone, Copy)]
pub struct FrameShape {
    /// Bytes the prologue carves: the frame is `[base, base + size)`.
    pub size: u32,
    /// The local holding `base`, written once, by the prologue.
    pub base_local: u32,
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum Abs {
    Unknown,
    Const(i64),
    /// `base + k` for some `k` in the set.
    Frame(BTreeSet<i64>),
}

fn frame_of(set: BTreeSet<i64>) -> Abs {
    if set.len() > MAX_OFFSETS || set.iter().any(|k| i32::try_from(*k).is_err()) {
        Abs::Unknown
    } else {
        Abs::Frame(set)
    }
}

/// `None` is a local no write has reached yet.
fn join(old: &Option<Abs>, new: &Abs) -> Abs {
    match (old, new) {
        (None, n) => n.clone(),
        (Some(Abs::Unknown), _) | (_, Abs::Unknown) => Abs::Unknown,
        (Some(Abs::Const(a)), Abs::Const(b)) if a == b => Abs::Const(*a),
        (Some(Abs::Frame(a)), Abs::Frame(b)) => frame_of(a.union(b).copied().collect()),
        _ => Abs::Unknown,
    }
}

fn shift(set: &BTreeSet<i64>, by: i64) -> Abs {
    frame_of(set.iter().map(|k| k + by).collect())
}

/// Wrap `v` to an `i32` constant, as the engine's `i32` arithmetic does.
fn wrap32(v: i64) -> i64 {
    i64::from(v as i32)
}

struct Reader<'a> {
    code: &'a [u8],
    pos: usize,
}

impl Reader<'_> {
    fn byte(&mut self) -> Option<u8> {
        let b = *self.code.get(self.pos)?;
        self.pos += 1;
        Some(b)
    }

    fn uleb(&mut self) -> Option<u64> {
        let mut v: u64 = 0;
        let mut shift = 0u32;
        loop {
            let b = self.byte()?;
            if shift < 64 {
                v |= u64::from(b & 0x7f) << shift;
            }
            if b & 0x80 == 0 {
                return Some(v);
            }
            shift += 7;
            if shift > 70 {
                return None;
            }
        }
    }

    fn sleb(&mut self) -> Option<i64> {
        let mut v: i64 = 0;
        let mut shift = 0u32;
        loop {
            let b = self.byte()?;
            if shift < 64 {
                v |= i64::from(b & 0x7f) << shift;
            }
            shift += 7;
            if b & 0x80 == 0 {
                if shift < 64 && b & 0x40 != 0 {
                    v |= -1i64 << shift;
                }
                return Some(v);
            }
            if shift > 70 {
                return None;
            }
        }
    }

    fn skip(&mut self, n: usize) -> Option<()> {
        self.pos = self.pos.checked_add(n)?;
        (self.pos <= self.code.len()).then_some(())
    }

    fn blocktype(&mut self) -> Option<()> {
        match *self.code.get(self.pos)? {
            0x40 | 0x7f | 0x7e | 0x7d | 0x7c | 0x7b | 0x70 | 0x6f => self.skip(1),
            _ => self.sleb().map(|_| ()),
        }
    }

    /// A memory argument's static offset.
    fn memarg(&mut self) -> Option<u64> {
        let align = self.uleb()?;
        if align & 0x40 != 0 {
            self.uleb()?;
        }
        self.uleb()
    }
}

/// Bytes a plain load/store opcode moves.
fn access_width(opcode: u8) -> u32 {
    match opcode {
        0x29 | 0x2b | 0x37 | 0x39 => 8,
        0x28 | 0x2a | 0x34 | 0x35 | 0x36 | 0x38 | 0x3e => 4,
        0x2e | 0x2f | 0x32 | 0x33 | 0x3b | 0x3d => 2,
        _ => 1,
    }
}

struct Pass<'a> {
    frame: FrameShape,
    params: u32,
    locals: &'a mut Vec<Option<Abs>>,
    widen: bool,
    changed: bool,
    base_writes: usize,
    /// Code offsets of immediates a relocation rewrites.
    relocated: &'a HashSet<u32>,
    /// Set on the checking pass: the first out-of-frame access.
    check: bool,
    violation: Option<String>,
}

impl Pass<'_> {
    fn get(&self, l: u32) -> Abs {
        if l == self.frame.base_local {
            return Abs::Frame(BTreeSet::from([0]));
        }
        if l < self.params {
            return Abs::Unknown;
        }
        match self.locals.get(l as usize) {
            Some(Some(a)) => a.clone(),
            _ => Abs::Unknown,
        }
    }

    fn set(&mut self, l: u32, v: &Abs) {
        if l == self.frame.base_local {
            self.base_writes += 1;
            return;
        }
        if l < self.params {
            return;
        }
        let Some(slot) = self.locals.get_mut(l as usize) else {
            return;
        };
        let mut joined = join(slot, v);
        if Some(&joined) != slot.as_ref() {
            if self.widen && slot.is_some() {
                joined = Abs::Unknown;
            }
            if Some(&joined) != slot.as_ref() {
                *slot = Some(joined);
                self.changed = true;
            }
        }
    }

    /// Record a violation when `addr + offset .. + len` leaves the frame for
    /// every frame offset `addr` may carry (a definite violation; see the
    /// module's evidence boundary for a partly outside set).
    fn access(&mut self, at: usize, what: &str, addr: &Abs, offset: u64, len: Option<i64>) {
        if !self.check || self.violation.is_some() {
            return;
        }
        let (Abs::Frame(ks), Some(len)) = (addr, len) else {
            return;
        };
        // Exact arithmetic: a memory argument's offset may exceed `i64`.
        let (offset, len) = (i128::from(offset), i128::from(len));
        let size = i64::from(self.frame.size);
        let outside = |k: i64| {
            let start = i128::from(k) + offset;
            start < 0 || start + len > i128::from(size)
        };
        if !ks.is_empty() && ks.iter().all(|&k| outside(k)) {
            let spans: Vec<String> = ks
                .iter()
                .map(|&k| {
                    let start = i128::from(k) + offset;
                    format!("[{start}, {})", start + len)
                })
                .collect();
            self.violation = Some(format!(
                "{what} at code offset {at} reaches frame bytes {} of a {size}-byte frame",
                spans.join(" or ")
            ));
        }
    }

    /// Run the body once. `None` when the body is not decodable.
    fn run(&mut self, code: &[u8]) -> Option<()> {
        let mut r = Reader { code, pos: 0 };
        let mut stack: Vec<Abs> = Vec::new();
        let pop = |s: &mut Vec<Abs>| s.pop().unwrap_or(Abs::Unknown);
        while r.pos < code.len() {
            let at = r.pos;
            let opcode = r.byte()?;
            match opcode {
                // Structured control, branches, returns, traps and calls: the
                // operand stack is forgotten (sound: pops become unknown).
                0x00 | 0x05 | 0x0b | 0x0f => stack.clear(),
                0x02..=0x04 => {
                    r.blocktype()?;
                    stack.clear();
                }
                0x0c | 0x0d => {
                    r.uleb()?;
                    stack.clear();
                }
                0x0e => {
                    let n = r.uleb()?;
                    for _ in 0..=n {
                        r.uleb()?;
                    }
                    stack.clear();
                }
                0x10 => {
                    r.uleb()?;
                    stack.clear();
                }
                0x11 => {
                    r.uleb()?;
                    r.uleb()?;
                    stack.clear();
                }
                0x01 => {}
                0x1a => {
                    pop(&mut stack);
                }
                0x1b => {
                    pop(&mut stack);
                    pop(&mut stack);
                    pop(&mut stack);
                    stack.push(Abs::Unknown);
                }
                0x1c => {
                    let n = usize::try_from(r.uleb()?).ok()?;
                    r.skip(n)?;
                    pop(&mut stack);
                    pop(&mut stack);
                    pop(&mut stack);
                    stack.push(Abs::Unknown);
                }
                0x20 => {
                    let l = u32::try_from(r.uleb()?).ok()?;
                    stack.push(self.get(l));
                }
                0x21 => {
                    let l = u32::try_from(r.uleb()?).ok()?;
                    let v = pop(&mut stack);
                    self.set(l, &v);
                }
                0x22 => {
                    let l = u32::try_from(r.uleb()?).ok()?;
                    let v = pop(&mut stack);
                    self.set(l, &v);
                    stack.push(v);
                }
                0x23 => {
                    r.uleb()?;
                    stack.push(Abs::Unknown);
                }
                0x24 => {
                    r.uleb()?;
                    pop(&mut stack);
                }
                0x25 => {
                    r.uleb()?;
                    pop(&mut stack);
                    stack.push(Abs::Unknown);
                }
                0x26 => {
                    r.uleb()?;
                    pop(&mut stack);
                    pop(&mut stack);
                }
                0x28..=0x35 => {
                    let offset = r.memarg()?;
                    let addr = pop(&mut stack);
                    let width = i64::from(access_width(opcode));
                    self.access(at, "load", &addr, offset, Some(width));
                    stack.push(Abs::Unknown);
                }
                0x36..=0x3e => {
                    let offset = r.memarg()?;
                    pop(&mut stack);
                    let addr = pop(&mut stack);
                    let width = i64::from(access_width(opcode));
                    self.access(at, "store", &addr, offset, Some(width));
                }
                0x3f => {
                    r.uleb()?;
                    stack.push(Abs::Unknown);
                }
                0x40 => {
                    r.uleb()?;
                    pop(&mut stack);
                    stack.push(Abs::Unknown);
                }
                0x41 => {
                    let imm_at = r.pos as u32;
                    let v = r.sleb()?;
                    stack.push(if self.relocated.contains(&imm_at) {
                        Abs::Unknown
                    } else {
                        Abs::Const(wrap32(v))
                    });
                }
                0x42 => {
                    r.sleb()?;
                    stack.push(Abs::Unknown);
                }
                0x43 => {
                    r.skip(4)?;
                    stack.push(Abs::Unknown);
                }
                0x44 => {
                    r.skip(8)?;
                    stack.push(Abs::Unknown);
                }
                // i32.add / i32.sub keep a frame address a frame address.
                0x6a | 0x6b => {
                    let b = pop(&mut stack);
                    let a = pop(&mut stack);
                    let sub = opcode == 0x6b;
                    stack.push(match (&a, &b) {
                        (Abs::Const(x), Abs::Const(y)) => {
                            Abs::Const(wrap32(if sub { x - y } else { x + y }))
                        }
                        (Abs::Frame(ks), Abs::Const(c)) => shift(ks, if sub { -c } else { *c }),
                        (Abs::Const(c), Abs::Frame(ks)) if !sub => shift(ks, *c),
                        _ => Abs::Unknown,
                    });
                }
                0x45
                | 0x50
                | 0x67..=0x69
                | 0x79..=0x7b
                | 0x8b..=0x91
                | 0x99..=0x9f
                | 0xa7..=0xc4
                | 0xd1 => {
                    pop(&mut stack);
                    stack.push(Abs::Unknown);
                }
                0x46..=0x4f
                | 0x51..=0x5a
                | 0x5b..=0x66
                | 0x6c..=0x78
                | 0x7c..=0x8a
                | 0x92..=0x98
                | 0xa0..=0xa6 => {
                    pop(&mut stack);
                    pop(&mut stack);
                    stack.push(Abs::Unknown);
                }
                0xd0 => {
                    r.skip(1)?;
                    stack.push(Abs::Unknown);
                }
                0xd2 => {
                    r.uleb()?;
                    stack.push(Abs::Unknown);
                }
                0xfc => match r.uleb()? {
                    0..=7 => {
                        pop(&mut stack);
                        stack.push(Abs::Unknown);
                    }
                    8 | 12 | 14 => {
                        r.uleb()?;
                        r.uleb()?;
                        stack.clear();
                    }
                    9 | 13 => {
                        r.uleb()?;
                    }
                    10 => {
                        r.uleb()?;
                        r.uleb()?;
                        let len = pop(&mut stack);
                        let src = pop(&mut stack);
                        let dst = pop(&mut stack);
                        let len = match len {
                            Abs::Const(n) => Some(i64::from(n as u32)),
                            _ => None,
                        };
                        self.access(at, "memory.copy destination", &dst, 0, len);
                        self.access(at, "memory.copy source", &src, 0, len);
                    }
                    11 => {
                        r.uleb()?;
                        let len = pop(&mut stack);
                        pop(&mut stack);
                        let dst = pop(&mut stack);
                        let len = match len {
                            Abs::Const(n) => Some(i64::from(n as u32)),
                            _ => None,
                        };
                        self.access(at, "memory.fill", &dst, 0, len);
                    }
                    15..=17 => {
                        r.uleb()?;
                        stack.clear();
                    }
                    _ => return None,
                },
                _ => return None,
            }
        }
        Some(())
    }
}

/// Refuse `code` (a function body's instructions, without its local
/// declarations) when a constant-offset access through its frame may leave
/// `frame`. `params` is the parameter count and `locals` the declared local
/// count; `reloc_immediates` are the code offsets of relocated immediates.
pub fn check(
    code: &[u8],
    params: u32,
    locals: usize,
    frame: FrameShape,
    reloc_immediates: &HashSet<u32>,
) -> Result<(), String> {
    let total = (params as usize)
        .checked_add(locals)
        .ok_or("local count overflows")?;
    let mut values: Vec<Option<Abs>> = vec![None; total];
    let mut passes = 0usize;
    loop {
        let mut pass = Pass {
            frame,
            params,
            locals: &mut values,
            widen: passes >= WIDEN_AFTER,
            changed: false,
            base_writes: 0,
            relocated: reloc_immediates,
            check: false,
            violation: None,
        };
        pass.run(code)
            .ok_or("the frame-bounds guard cannot decode the body")?;
        if pass.base_writes != 1 {
            return Err(format!(
                "the frame-base local {} is written {} times; the guard's premise is one \
                 prologue write",
                frame.base_local, pass.base_writes
            ));
        }
        passes += 1;
        if !pass.changed {
            break;
        }
    }
    let mut pass = Pass {
        frame,
        params,
        locals: &mut values,
        widen: true,
        changed: false,
        base_writes: 0,
        relocated: reloc_immediates,
        check: true,
        violation: None,
    };
    pass.run(code)
        .ok_or("the frame-bounds guard cannot decode the body")?;
    match pass.violation {
        Some(v) => Err(v),
        None => Ok(()),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn uleb(out: &mut Vec<u8>, mut v: u64) {
        loop {
            let b = (v & 0x7f) as u8;
            v >>= 7;
            if v == 0 {
                out.push(b);
                return;
            }
            out.push(b | 0x80);
        }
    }

    fn sleb(out: &mut Vec<u8>, mut v: i64) {
        loop {
            let b = (v & 0x7f) as u8;
            v >>= 7;
            let done = (v == 0 && b & 0x40 == 0) || (v == -1 && b & 0x40 != 0);
            if done {
                out.push(b);
                return;
            }
            out.push(b | 0x80);
        }
    }

    /// A prologue that makes local 1 the frame base, then `body`.
    fn with_prologue(size: u32, body: &[u8]) -> Vec<u8> {
        let mut c = vec![0x23, 0x00, 0x21, 0x00, 0x20, 0x00, 0x41];
        sleb(&mut c, i64::from(size));
        c.extend_from_slice(&[0x6b, 0x22, 0x01, 0x24, 0x00]);
        c.extend_from_slice(body);
        c.push(0x0b);
        c
    }

    const FRAME: FrameShape = FrameShape {
        size: 32,
        base_local: 1,
    };

    fn store_i64_at(local_off: i64, memarg_off: u64) -> Vec<u8> {
        // local 2 := base + local_off; i64.store [local 2 + memarg_off] = 0
        let mut b = vec![0x20, 0x01, 0x41];
        sleb(&mut b, local_off);
        b.extend_from_slice(&[0x6a, 0x21, 0x02, 0x20, 0x02, 0x42, 0x00, 0x37, 0x03]);
        uleb(&mut b, memarg_off);
        b
    }

    #[test]
    fn in_frame_stores_pass() {
        let code = with_prologue(32, &store_i64_at(16, 8));
        assert_eq!(check(&code, 0, 3, FRAME, &HashSet::new()), Ok(()));
    }

    #[test]
    fn a_store_past_the_frame_is_refused() {
        let code = with_prologue(32, &store_i64_at(16, 16));
        let err = check(&code, 0, 3, FRAME, &HashSet::new()).unwrap_err();
        assert!(err.contains("[32, 40)"), "{err}");
    }

    #[test]
    fn a_copy_past_the_frame_is_refused() {
        // memory.copy(base + 24, base, 16): the destination reaches 40.
        let mut b = vec![0x20, 0x01, 0x41, 24, 0x6a, 0x20, 0x01, 0x41, 16, 0xfc];
        uleb(&mut b, 10);
        b.extend_from_slice(&[0, 0]);
        let code = with_prologue(32, &b);
        let err = check(&code, 0, 3, FRAME, &HashSet::new()).unwrap_err();
        assert!(err.contains("memory.copy destination"), "{err}");
    }

    #[test]
    fn a_frame_address_through_a_second_local_is_tracked() {
        // local 2 := base + 8; local 3 := local 2 + 24; i32.store [local 3].
        let b = [
            0x20, 0x01, 0x41, 8, 0x6a, 0x21, 0x02, 0x20, 0x02, 0x41, 24, 0x6a, 0x21, 0x03, 0x20,
            0x03, 0x41, 0, 0x36, 0x02, 0x00,
        ];
        let code = with_prologue(32, &b);
        let err = check(&code, 0, 4, FRAME, &HashSet::new()).unwrap_err();
        assert!(err.contains("store") && err.contains("[32, 36)"), "{err}");
        let ok = with_prologue(40, &b);
        let frame40 = FrameShape { size: 40, ..FRAME };
        assert_eq!(check(&ok, 0, 4, frame40, &HashSet::new()), Ok(()));
    }

    /// local 2 := base + 0 and, by a second write, base + 24 (the join of a
    /// block parameter's incoming edges); then `i64.store [local 2 + off]`.
    fn joined_store(off: u64) -> Vec<u8> {
        let mut b = vec![
            0x20, 0x01, 0x21, 0x02, 0x20, 0x01, 0x41, 24, 0x6a, 0x21, 0x02, 0x20, 0x02, 0x42, 0x00,
            0x37, 0x03,
        ];
        uleb(&mut b, off);
        with_prologue(32, &b)
    }

    #[test]
    fn a_join_partly_outside_the_frame_is_not_a_definite_violation() {
        // Offsets {0, 24} + 16: [16, 24) is inside, [40, 48) is not.
        assert_eq!(
            check(&joined_store(16), 0, 3, FRAME, &HashSet::new()),
            Ok(())
        );
    }

    #[test]
    fn a_join_wholly_outside_the_frame_is_refused() {
        // Offsets {0, 24} + 32: both [32, 40) and [56, 64) are outside.
        let err = check(&joined_store(32), 0, 3, FRAME, &HashSet::new()).unwrap_err();
        assert!(err.contains("[32, 40) or [56, 64)"), "{err}");
    }

    #[test]
    fn a_runtime_address_is_outside_the_claim() {
        // i64.store [param 0 + 1000]: not a frame address.
        let b = [0x20, 0x00, 0x42, 0x00, 0x37, 0x03, 0xe8, 0x07];
        let mut code = vec![0x23, 0x00, 0x41, 32, 0x6b, 0x22, 0x02, 0x24, 0x00];
        code.extend_from_slice(&b);
        code.push(0x0b);
        let frame = FrameShape {
            size: 32,
            base_local: 2,
        };
        assert_eq!(check(&code, 1, 2, frame, &HashSet::new()), Ok(()));
    }

    #[test]
    fn an_undecodable_body_is_refused() {
        let code = with_prologue(32, &[0xfe, 0x00]);
        assert!(check(&code, 0, 3, FRAME, &HashSet::new()).is_err());
    }
}
