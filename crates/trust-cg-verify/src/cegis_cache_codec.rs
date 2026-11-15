// trust-cg-verify/cegis_cache_codec.rs - CEGIS cache wire format
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Replaces `rmp-serde` (MessagePack) as the CEGIS cache payload format. See the
// module docs for why a hand-rolled format, and for the two behavioural
// deviations from the incumbent.

//! **The CEGIS cache wire format**, hand-rolled so that nothing on this path
//! depends on a serializer Trust does not own.
//!
//! # Why this module exists
//!
//! [`crate::cegis_pass::CegisCacheEntry`] used to reach the disk through
//! `rmp-serde`. `rmp-serde` is the only third-party *normal* dependency edge
//! that keeps `rmp-serde 1.3.1` and `rmp 0.8.15` in the shipping closure of the
//! `crates/` workspace, and `rmp-serde` is one of the third-party crates that
//! keeps `serde` in that closure — so every proof over a unit that transitively
//! reaches this cache is conditional on two compilation units Trust does not
//! own. The payload is five fields of scalars and shallow `Vec`s; a
//! general-purpose self-describing serializer is not buying anything here that
//! ~200 lines of little-endian writes do not.
//!
//! Removing the dependency is the whole point. This module therefore uses
//! `std` only.
//!
//! # What correctness means here
//!
//! This cache is **proof-authority-bearing on the read side**. A cache *hit*
//! makes [`crate::cegis_pass::CegisSuperoptPass`] apply the recorded rewrites
//! to a machine function **without re-running CEGIS** — the entry is the record
//! that those rewrites were once proven equivalent. So:
//!
//! * A **stale miss is free.** The pass re-runs enumeration; the only cost is
//!   solver time. This is what makes a format change cheap: bump the version
//!   and every pre-existing entry becomes a miss.
//! * A **wrong hit is a miscompile.** Decoding a foreign or corrupt blob into a
//!   plausible-looking entry would splice attacker-or-garbage-chosen
//!   instructions into a function at garbage indices, with no solver in the
//!   loop. Every decision in the reader below is therefore fail-closed: unknown
//!   magic, unknown version, unknown tag, short read, non-UTF-8 string, or
//!   **any trailing byte** all return `None`, which callers treat as a miss.
//!
//! The reader checks the format only. Entries carry no MAC, so a well-formed
//! entry with a changed immediate decodes like an honest one. The pass does
//! not trust a decoded body: it applies a recorded rewrite only where its own
//! matcher, run on the current function, rebuilds exactly that body, and
//! otherwise treats the entry as stale (a miss). [`crate::cegis_cache_io`]
//! also refuses a root that another user owns or can write.
//!
//! The on-disk root is shared between worktrees on a host
//! ([`crate::cegis_cache_io`]), so "foreign blob" is not hypothetical: a blob
//! written by a differently-versioned build of this crate is exactly what the
//! reader will be handed.
//!
//! # How that is established
//!
//! 1. **Exhaustive round-trip over every variant.** `tests/cegis_cache_codec.rs`
//!    round-trips a corpus that names every [`MachOperandBlob`],
//!    [`RegClassBlob`], [`SpecialRegBlob`] and [`RewriteLayer`] variant, plus
//!    the numeric extremes (`i64::MIN`, `u64::MAX`, `-0.0`, NaN payloads) and
//!    the empty/absent cases.
//! 2. **Differential against the incumbent, while both exist.** `rmp-serde` is
//!    retained as a **dev-dependency**. Over 512 pseudo-random entries the test
//!    asserts that this codec round-trips exactly the values MessagePack
//!    round-trips, and — since the two byte strings deliberately differ — that
//!    each format *rejects* the other's output. That cross-rejection is the
//!    real gate: it is what makes the version bump safe.
//! 3. **Structural guards against silent format drift.** The encoder
//!    destructures each struct by name, so adding a field is a compile error
//!    rather than a field that silently stops being written; and it matches
//!    each enum exhaustively, so adding a variant is a compile error rather
//!    than a panic or a wrong tag.
//!
//! # Format
//!
//! Little-endian, fixed width, no varints. Every collection is a `u32` count
//! followed by that many elements. Strings are a `u32` byte length followed by
//! UTF-8. Field order is declaration order.
//!
//! ```text
//! entry  := "TCGC" u32:version u8:completion
//!           u64:attempted u64:verified u64:rejected
//!           u32:n (rewrite * n)
//! rewrite:= u32:inst_index u64:proof_hash u32:iterations u32:window_len
//!           u8:layer u32:n (inst * n)
//! inst   := str:opcode u32:n (operand * n)
//! operand:= u8:tag payload
//! str    := u32:len byte*len
//! ```
//!
//! # Deviations from the incumbent, stated at the site
//!
//! * **The bytes are not MessagePack and are not intended to be.** A v5
//!   `rmp-serde` blob cannot decode here (its first byte is `0x95`, a fixarray
//!   header, not `T`), and this format's blobs cannot decode there. That is
//!   deliberate and is why [`crate::cegis_pass::CegisCacheEntry::VERSION`] went
//!   5 → 6. Version 7 subsequently added the completion byte so old partial
//!   search prefixes cannot replay as complete entries. Nothing reads these
//!   bytes except this module.
//! * **The reader is stricter than `rmp-serde` about trailing bytes.**
//!   `rmp_serde::from_slice` decodes the leading value and ignores whatever
//!   follows; this reader requires the buffer to be consumed exactly. Both
//!   behaviours are asserted in `tests/cegis_cache_codec.rs` so the difference
//!   is measured rather than assumed. Stricter is the safe direction for a
//!   format whose only failure mode of interest is a *wrong hit*.
//! * **No capacity is reserved from an untrusted length.** A corrupt count of
//!   `u32::MAX` would make `Vec::with_capacity` request ~240 GB before the
//!   first short read is noticed. Elements are pushed one at a time, so a
//!   truncated buffer fails after allocating only what it actually read.
//!   **This one property is enforced by review, not by a test.** Measured
//!   2026-08-23: reintroducing `Vec::with_capacity(n as usize)` in
//!   [`Reader::seq`] left the whole test file green, because macOS reserves
//!   that address space lazily rather than failing. Do not read
//!   `a_corrupt_length_prefix_is_a_miss` as coverage of it.

use std::fmt;

use crate::cegis_pass::{
    CegisCacheEntry, CegisSearchCompletion, MachInstBlob, MachOperandBlob, ProvenRewrite,
    RegClassBlob, RewriteLayer, SpecialRegBlob,
};

/// Leading bytes of every entry. A blob that does not start with these is
/// rejected before anything else is parsed, which is what keeps a MessagePack
/// entry (or an unrelated file that landed in the cache directory) from being
/// interpreted as a rewrite plan.
const MAGIC: [u8; 4] = *b"TCGC";

/// Operand discriminants. **These are wire values: append, never renumber.**
mod tag {
    pub const VREG: u8 = 0;
    pub const PREG: u8 = 1;
    pub const IMM: u8 = 2;
    pub const FIMM_BITS: u8 = 3;
    pub const BLOCK: u8 = 4;
    pub const STACK_SLOT: u8 = 5;
    pub const FRAME_INDEX: u8 = 6;
    pub const MEM_OP: u8 = 7;
    pub const SPECIAL: u8 = 8;
    pub const SYMBOL: u8 = 9;
    pub const JUMP_TABLE_INDEX: u8 = 10;
    pub const INCOMING_ARG: u8 = 11;
    pub const EXACT_MODULE_SYMBOL: u8 = 12;
}

/// The only way encoding can fail.
///
/// Encoding is otherwise total: every field is a fixed-width scalar or a
/// length-prefixed sequence. Incomplete searches are rejected at the public
/// entry boundary, and collections or strings longer than `u32::MAX` are
/// reported rather than truncated.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CacheCodecError {
    /// A deadline/query/verifier failure left a non-publishable search prefix.
    IncompleteSearch {
        /// Typed reason the search did not complete.
        completion: CegisSearchCompletion,
    },
    /// A sequence or string exceeded the `u32` length prefix.
    TooLong {
        /// Which sequence overflowed.
        what: &'static str,
        /// Its actual length.
        len: usize,
    },
}

impl fmt::Display for CacheCodecError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::IncompleteSearch { completion } => {
                write!(f, "CEGIS cache search is incomplete: {completion:?}")
            }
            Self::TooLong { what, len } => {
                write!(f, "CEGIS cache {what} length {len} exceeds u32 wire limit")
            }
        }
    }
}

impl std::error::Error for CacheCodecError {}

// ---------------------------------------------------------------------------
// Writer
// ---------------------------------------------------------------------------

struct Writer {
    buf: Vec<u8>,
}

impl Writer {
    fn new() -> Self {
        Self {
            buf: Vec::from(MAGIC),
        }
    }

    fn u8(&mut self, v: u8) {
        self.buf.push(v);
    }
    fn u16(&mut self, v: u16) {
        self.buf.extend_from_slice(&v.to_le_bytes());
    }
    fn u32(&mut self, v: u32) {
        self.buf.extend_from_slice(&v.to_le_bytes());
    }
    fn u64(&mut self, v: u64) {
        self.buf.extend_from_slice(&v.to_le_bytes());
    }
    /// Two's-complement little-endian, matching the unsigned writers.
    fn i32(&mut self, v: i32) {
        self.u32(v as u32);
    }
    fn i64(&mut self, v: i64) {
        self.u64(v as u64);
    }

    fn count(&mut self, what: &'static str, n: usize) -> Result<(), CacheCodecError> {
        let n = u32::try_from(n).map_err(|_| CacheCodecError::TooLong { what, len: n })?;
        self.u32(n);
        Ok(())
    }

    fn str(&mut self, s: &str) -> Result<(), CacheCodecError> {
        self.count("string", s.len())?;
        self.buf.extend_from_slice(s.as_bytes());
        Ok(())
    }
}

// ---------------------------------------------------------------------------
// Reader
// ---------------------------------------------------------------------------

/// Bounds-checked cursor. Every accessor returns `None` on a short read, and
/// `None` propagates all the way out to a cache miss.
struct Reader<'a> {
    bytes: &'a [u8],
    pos: usize,
}

impl<'a> Reader<'a> {
    fn new(bytes: &'a [u8]) -> Self {
        Self { bytes, pos: 0 }
    }

    fn take(&mut self, n: usize) -> Option<&'a [u8]> {
        let end = self.pos.checked_add(n)?;
        let out = self.bytes.get(self.pos..end)?;
        self.pos = end;
        Some(out)
    }

    fn u8(&mut self) -> Option<u8> {
        Some(self.take(1)?[0])
    }
    fn u16(&mut self) -> Option<u16> {
        Some(u16::from_le_bytes(self.take(2)?.try_into().ok()?))
    }
    fn u32(&mut self) -> Option<u32> {
        Some(u32::from_le_bytes(self.take(4)?.try_into().ok()?))
    }
    fn u64(&mut self) -> Option<u64> {
        Some(u64::from_le_bytes(self.take(8)?.try_into().ok()?))
    }
    fn i32(&mut self) -> Option<i32> {
        Some(self.u32()? as i32)
    }
    fn i64(&mut self) -> Option<i64> {
        Some(self.u64()? as i64)
    }

    fn str(&mut self) -> Option<String> {
        let len = self.u32()? as usize;
        let bytes = self.take(len)?;
        std::str::from_utf8(bytes).ok().map(str::to_owned)
    }

    /// Read a `u32`-counted sequence.
    ///
    /// Deliberately does **not** `reserve` from `n`: `n` is untrusted, and a
    /// corrupt count must cost a short read, not an allocation.
    fn seq<T>(&mut self, mut item: impl FnMut(&mut Self) -> Option<T>) -> Option<Vec<T>> {
        let n = self.u32()?;
        let mut out = Vec::new();
        for _ in 0..n {
            out.push(item(self)?);
        }
        Some(out)
    }

    fn finish(&self) -> Option<()> {
        (self.pos == self.bytes.len()).then_some(())
    }
}

// ---------------------------------------------------------------------------
// Small enums
// ---------------------------------------------------------------------------

fn put_layer(w: &mut Writer, layer: RewriteLayer) {
    // Exhaustive on purpose: a new layer must not silently take another's tag.
    w.u8(match layer {
        RewriteLayer::A => 0,
        RewriteLayer::B => 1,
        RewriteLayer::C => 2,
    });
}

fn get_layer(r: &mut Reader<'_>) -> Option<RewriteLayer> {
    match r.u8()? {
        0 => Some(RewriteLayer::A),
        1 => Some(RewriteLayer::B),
        2 => Some(RewriteLayer::C),
        _ => None,
    }
}

fn put_reg_class(w: &mut Writer, class: RegClassBlob) {
    w.u8(match class {
        RegClassBlob::Gpr64 => 0,
        RegClassBlob::Gpr32 => 1,
        RegClassBlob::Fpr128 => 2,
        RegClassBlob::Fpr64 => 3,
        RegClassBlob::Fpr32 => 4,
        RegClassBlob::Fpr16 => 5,
        RegClassBlob::Fpr8 => 6,
        RegClassBlob::System => 7,
    });
}

fn get_reg_class(r: &mut Reader<'_>) -> Option<RegClassBlob> {
    match r.u8()? {
        0 => Some(RegClassBlob::Gpr64),
        1 => Some(RegClassBlob::Gpr32),
        2 => Some(RegClassBlob::Fpr128),
        3 => Some(RegClassBlob::Fpr64),
        4 => Some(RegClassBlob::Fpr32),
        5 => Some(RegClassBlob::Fpr16),
        6 => Some(RegClassBlob::Fpr8),
        7 => Some(RegClassBlob::System),
        _ => None,
    }
}

fn put_special_reg(w: &mut Writer, reg: SpecialRegBlob) {
    w.u8(match reg {
        SpecialRegBlob::SP => 0,
        SpecialRegBlob::XZR => 1,
        SpecialRegBlob::WZR => 2,
    });
}

fn get_special_reg(r: &mut Reader<'_>) -> Option<SpecialRegBlob> {
    match r.u8()? {
        0 => Some(SpecialRegBlob::SP),
        1 => Some(SpecialRegBlob::XZR),
        2 => Some(SpecialRegBlob::WZR),
        _ => None,
    }
}

// ---------------------------------------------------------------------------
// Operands
// ---------------------------------------------------------------------------

fn put_operand(w: &mut Writer, operand: &MachOperandBlob) -> Result<(), CacheCodecError> {
    match operand {
        MachOperandBlob::VReg { id, class } => {
            w.u8(tag::VREG);
            w.u32(*id);
            put_reg_class(w, *class);
        }
        MachOperandBlob::PReg { encoding } => {
            w.u8(tag::PREG);
            w.u16(*encoding);
        }
        MachOperandBlob::Imm(v) => {
            w.u8(tag::IMM);
            w.i64(*v);
        }
        // Stored as raw bits by the blob type itself, so NaN payloads and the
        // sign of zero survive; this codec must not round-trip through `f64`.
        MachOperandBlob::FImmBits(bits) => {
            w.u8(tag::FIMM_BITS);
            w.u64(*bits);
        }
        MachOperandBlob::Block(v) => {
            w.u8(tag::BLOCK);
            w.u32(*v);
        }
        MachOperandBlob::StackSlot(v) => {
            w.u8(tag::STACK_SLOT);
            w.u32(*v);
        }
        MachOperandBlob::FrameIndex(v) => {
            w.u8(tag::FRAME_INDEX);
            w.i32(*v);
        }
        MachOperandBlob::MemOp {
            base_encoding,
            offset,
        } => {
            w.u8(tag::MEM_OP);
            w.u16(*base_encoding);
            w.i64(*offset);
        }
        MachOperandBlob::Special(reg) => {
            w.u8(tag::SPECIAL);
            put_special_reg(w, *reg);
        }
        MachOperandBlob::Symbol(name) => {
            w.u8(tag::SYMBOL);
            w.str(name)?;
        }
        MachOperandBlob::ExactModuleSymbol(name) => {
            w.u8(tag::EXACT_MODULE_SYMBOL);
            w.str(name)?;
        }
        MachOperandBlob::JumpTableIndex(v) => {
            w.u8(tag::JUMP_TABLE_INDEX);
            w.u32(*v);
        }
        MachOperandBlob::IncomingArg(v) => {
            w.u8(tag::INCOMING_ARG);
            w.i64(*v);
        }
    }
    Ok(())
}

fn get_operand(r: &mut Reader<'_>) -> Option<MachOperandBlob> {
    Some(match r.u8()? {
        tag::VREG => MachOperandBlob::VReg {
            id: r.u32()?,
            class: get_reg_class(r)?,
        },
        tag::PREG => MachOperandBlob::PReg { encoding: r.u16()? },
        tag::IMM => MachOperandBlob::Imm(r.i64()?),
        tag::FIMM_BITS => MachOperandBlob::FImmBits(r.u64()?),
        tag::BLOCK => MachOperandBlob::Block(r.u32()?),
        tag::STACK_SLOT => MachOperandBlob::StackSlot(r.u32()?),
        tag::FRAME_INDEX => MachOperandBlob::FrameIndex(r.i32()?),
        tag::MEM_OP => MachOperandBlob::MemOp {
            base_encoding: r.u16()?,
            offset: r.i64()?,
        },
        tag::SPECIAL => MachOperandBlob::Special(get_special_reg(r)?),
        tag::SYMBOL => MachOperandBlob::Symbol(r.str()?),
        tag::EXACT_MODULE_SYMBOL => MachOperandBlob::ExactModuleSymbol(r.str()?),
        tag::JUMP_TABLE_INDEX => MachOperandBlob::JumpTableIndex(r.u32()?),
        tag::INCOMING_ARG => MachOperandBlob::IncomingArg(r.i64()?),
        _ => return None,
    })
}

// ---------------------------------------------------------------------------
// Instructions and rewrites
// ---------------------------------------------------------------------------

fn put_inst(w: &mut Writer, inst: &MachInstBlob) -> Result<(), CacheCodecError> {
    // Destructured by name: adding a field to `MachInstBlob` is a compile
    // error here rather than a field that silently stops being written.
    let MachInstBlob { opcode, operands } = inst;
    w.str(opcode)?;
    w.count("operands", operands.len())?;
    for operand in operands {
        put_operand(w, operand)?;
    }
    Ok(())
}

fn get_inst(r: &mut Reader<'_>) -> Option<MachInstBlob> {
    Some(MachInstBlob {
        opcode: r.str()?,
        operands: r.seq(get_operand)?,
    })
}

fn put_rewrite(w: &mut Writer, rewrite: &ProvenRewrite) -> Result<(), CacheCodecError> {
    let ProvenRewrite {
        inst_index,
        proof_hash,
        iterations,
        window_len,
        replacement,
        layer,
    } = rewrite;
    w.u32(*inst_index);
    w.u64(*proof_hash);
    w.u32(*iterations);
    w.u32(*window_len);
    put_layer(w, *layer);
    w.count("replacement", replacement.len())?;
    for inst in replacement {
        put_inst(w, inst)?;
    }
    Ok(())
}

fn get_rewrite(r: &mut Reader<'_>) -> Option<ProvenRewrite> {
    let inst_index = r.u32()?;
    let proof_hash = r.u64()?;
    let iterations = r.u32()?;
    let window_len = r.u32()?;
    let layer = get_layer(r)?;
    let replacement = r.seq(get_inst)?;
    Some(ProvenRewrite {
        inst_index,
        proof_hash,
        iterations,
        window_len,
        replacement,
        layer,
    })
}

// ---------------------------------------------------------------------------
// Entry
// ---------------------------------------------------------------------------

/// Encode an entry. See the module docs for the byte layout.
pub(crate) fn encode_entry(entry: &CegisCacheEntry) -> Result<Vec<u8>, CacheCodecError> {
    let CegisCacheEntry {
        version,
        completion,
        proven_rewrites,
        attempted,
        verified,
        rejected,
    } = entry;
    if !completion.is_complete() {
        return Err(CacheCodecError::IncompleteSearch {
            completion: *completion,
        });
    }
    let mut w = Writer::new();
    w.u32(*version);
    w.u8(match completion {
        CegisSearchCompletion::NotCompleted => 0,
        CegisSearchCompletion::Complete => 1,
        CegisSearchCompletion::DeadlineExceeded => 2,
        CegisSearchCompletion::QueryIncomplete => 3,
        CegisSearchCompletion::VerifierError => 4,
        CegisSearchCompletion::VerifierPanicked => 5,
    });
    w.u64(*attempted);
    w.u64(*verified);
    w.u64(*rejected);
    w.count("proven_rewrites", proven_rewrites.len())?;
    for rewrite in proven_rewrites {
        put_rewrite(&mut w, rewrite)?;
    }
    Ok(w.buf)
}

/// Decode an entry, or `None` for anything a caller must treat as a miss.
///
/// The version gate lives here rather than in the caller: a body written under
/// a different format version may have a different *layout*, so it must not be
/// parsed at all. `version` is still carried in the struct so that
/// `decode(encode(e)) == e` for the current version.
pub(crate) fn decode_entry(bytes: &[u8]) -> Option<CegisCacheEntry> {
    let mut r = Reader::new(bytes);
    if r.take(MAGIC.len())? != MAGIC {
        return None;
    }
    let version = r.u32()?;
    if version != CegisCacheEntry::VERSION {
        return None;
    }
    let completion = match r.u8()? {
        0 => CegisSearchCompletion::NotCompleted,
        1 => CegisSearchCompletion::Complete,
        2 => CegisSearchCompletion::DeadlineExceeded,
        3 => CegisSearchCompletion::QueryIncomplete,
        4 => CegisSearchCompletion::VerifierError,
        5 => CegisSearchCompletion::VerifierPanicked,
        _ => return None,
    };
    if !completion.is_complete() {
        return None;
    }
    let attempted = r.u64()?;
    let verified = r.u64()?;
    let rejected = r.u64()?;
    let proven_rewrites = r.seq(get_rewrite)?;
    // Trailing bytes mean the blob is not what this reader thinks it is.
    r.finish()?;
    Some(CegisCacheEntry {
        version,
        completion,
        proven_rewrites,
        attempted,
        verified,
        rejected,
    })
}
