// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Source-bound x86-64 System V ABI envelope over FINAL function bytes.
//!
//! Two source shapes have nothing a value theorem can observe: an empty void
//! body (`Jump* ; Return`) and a panic entry (`Jump* ; Call f() ; Trap`, the
//! `-Cpanic=abort` lowering). Their pre-register-allocation ISel stream is
//! `[Ret]` or `[Call, Ud2]`, so the x86 body lane
//! ([`crate::x86_source_bound_body`]) refuses them
//! (`X86BodyUnsupported::NoObservable`). What such a body does to its caller
//! happens after instruction selection: the frame, the stack balance, the
//! restored callee-saved registers, the return-address slot, the alignment of
//! the call, and the fixup that names the callee. This owner therefore judges
//! the EXACT pre-relocation function bytes the JIT certifies, together with
//! the symbolic fixup manifest the JIT's linker will patch, the same two
//! inputs its certificate-cache key binds.
//!
//! ```text
//! inputs      rsp0          RSP at entry (the caller's CALL already pushed)
//!             <r>_0         entry value of every register the walk reads
//!             code_base     the function's load address (diverging shape)
//!             obs           an arbitrary byte address
//!             mem_<k>       the caller's memory byte at the k-th distinct
//!                           syntactic address read (see Memory)
//! premises    (= ((_ extract 3 0) (bvadd rsp0 #x..08)) #x0)
//!                           System V: RSP+8 is 16-byte aligned at entry
//!             (bvuge rsp0 depth)
//!                           the stack has `depth` bytes below rsp0
//!             (or (not (= a_i a_j)) (= mem_i mem_j))
//!                           Ackermann consistency of two reads of one memory
//! theorem     (= true (and item_1 (and ... item_n))), n >= 2
//! replayed    one part per goal, each `premises => goal` (below)
//! ```
//!
//! **Void return** (`Jump* ; Return`, no result, bytes ending in `RET`):
//! - the RET's target equals the caller's return address, the 8 bytes of the
//!   entry memory at `rsp0`;
//! - RSP after the RET is `rsp0 + 8`;
//! - every callee-saved GPR (RBX, RBP, R12-R15) the bytes write holds its entry
//!   value after the RET;
//! - memory at or above `rsp0` is unchanged: `(or (bvult obs rsp0) (= final
//!   base))`, emitted when the bytes write memory.
//!
//! **Diverging call** (`Jump* ; Call f() ; Trap`, bytes `... CALL rel32; UD2`):
//! - at callee entry, `RSP + 8` is 16-byte aligned: the SAME System V rule the
//!   entry premise states for `rsp0`. Callee-entry RSP is the RSP AFTER the
//!   CALL pushed its return address, i.e. `rsp0 - 8 - frame` for a frame of
//!   `frame` bytes pushed/allocated before the CALL; equivalently the pre-CALL
//!   RSP is 16-byte aligned. (Stating the item against the pre-CALL RSP with
//!   the entry congruence would accept the frameless, misaligned `call; ud2`
//!   and refute the correct framed body; the unit tests evaluate both
//!   readings against both bodies.)
//! - the return slot at callee entry holds `code_base + offset(UD2)`: a callee
//!   that returns lands on the trap the source ends in. The offset is where
//!   the RECOGNIZER found the source's trap, not the address the CALL pushes
//!   (`code_base + offset(CALL) + 5`, the CALL's semantics). In production
//!   the two are always equal: the Rust walk refuses every body with an
//!   instruction between the CALL and the UD2 (`TrapMissing`, or a named
//!   CALL/RET refusal) before any theorem is built, so for every body the
//!   owner admits this item is a read-back of the CALL's push and holds
//!   without the premises. It is falsified (by the evaluator, and refuted by
//!   AY) only for such a body handed to the test-only walk-free builder;
//!   there it guards the theorem against a walk that stopped refusing;
//! - every callee-saved GPR except RBP (RBX, R12-R15) the bytes write holds its
//!   entry value at callee entry (RBP is the frame pointer the prologue sets);
//! - memory at or above `rsp0` is unchanged at callee entry.
//!
//! **Memory is byte-granular.** Every 8-byte PUSH (and the CALL's return-address
//! push) is eight one-byte writes at `addr`, `addr+1`, ... `addr+7`, little
//! endian; every 8-byte read (POP, RET, the return slot) is the concatenation
//! of eight one-byte reads. A read of address `a` after writes `w_1 .. w_n` is
//! `(ite (= addr_n a) byte_n (ite ... (ite (= addr_1 a) byte_1 base(a))))`,
//! with every address equality left to the solver; no Rust decision
//! simplifies an address or a read. A partial overlap of two 8-byte accesses
//! is therefore modelled exactly, byte by byte.
//!
//! **The entry memory is array-free (Ackermann-reduced).** `base(a)` is a fresh
//! 8-bit input `mem_k` per distinct SYNTACTIC address `a` (one address term,
//! one input: that is the function application itself). For two distinct
//! terms `a_i`, `a_j` the premise `(or (not (= a_i a_j)) (= mem_i mem_j))`
//! restores functionality. The builder emits that premise only for pairs whose
//! address terms are the same base variable plus the same constant offset
//! (for example `rsp0` and `(bvadd (bvsub rsp0 8) 8)`), which is where the
//! correct shapes need it. Omitting a consistency premise only WEAKENS the
//! premises, so a theorem proven with fewer of them implies the fully
//! Ackermannized one, which is equivalent to the statement over one memory
//! function; the pair selection can cost provability, never soundness. The
//! source-bound replay path replays the exact query bytes and never applies
//! `array_row_lowering`, which is why no array sort appears.
//!
//! **Replayed in parts.** The statement above is what the structural checks
//! judge; the solver proves its PARTS, each under the full premise set: one
//! part per item, except that an item equating a 64-bit memory read (a byte
//! concatenation: the return target, the return slot, a restored callee-saved
//! register) is split into its eight byte equations. The statement holds
//! exactly when every part does, and credit requires a Valid replay of every
//! part. The split is mechanical and re-checked ([`check_envelope_parts`]).
//! Measured on the arm64 macOS host with a local overlay AY (build 11378),
//! which strictly certifies every part of the pinned shapes: the whole
//! conjunction is not certified (void return: `incomplete
//! self-check-rejected`; diverging call: `incomplete proof-trusted`; the
//! framed void body with saves: a 30 s timeout), nor is a 64-bit read
//! equation proved as one goal, while each byte equation certifies and
//! Clean fully verifies its proof.
//!
//! **Checked in Rust, not by the solver** (each can only refuse):
//! - byte recognition over a CLOSED set (below); anything else is
//!   [`X86EnvelopeUnsupported::Bytes`];
//! - manifest completeness: the parsed manifest is exactly empty (void
//!   return) or exactly one call row (kind 0) whose disp32 offset is the byte
//!   after the `E8`, naming the LIR call's callee with its exact-module
//!   binding. Any symbol row (GlobalRef, ExternRefGot, TlsTlv,
//!   ExactFunctionAddr), any second row, a row outside the range or over a
//!   non-hole byte, and any malformed or trailing manifest bytes refuse. A
//!   row the linker patches after certification is the only thing that may
//!   change certified bytes, so it must be exactly the hole this owner
//!   judged;
//! - the rel32 placeholder is zero; the walk also refuses a UD2 that is not at
//!   the CALL's return address (the theorem's return-slot item states it too);
//! - the control skeleton: one terminator, nothing after it, RET for a
//!   returning source, CALL immediately followed by UD2 for a diverging one;
//! - the function/LIR pairing (same name);
//! - a Rust shadow walk that refuses stack imbalance, a callee-saved write,
//!   a write at or above `rsp0` and a misaligned call before any theorem is
//!   built, and a concrete-witness evaluation that refuses a theorem one
//!   assignment already falsifies.
//!
//! **Closed byte set.** Measured from the JIT's own compile path (see the
//! codegen test `x86_jit_envelope_shapes_have_pinned_bytes`): `PUSH r` (`50+r`,
//! `41 50+r`), `POP r` (`58+r`, `41 58+r`), `MOV RBP, RSP` (`48 89 E5`),
//! `SUB/ADD RSP, imm8` (`48 83 EC/C4 ib`, 1..127), `CALL rel32` (`E8`), `RET`
//! (`C3`) and `UD2` (`0F 0B`). `PUSH RSP` (`54`) and `POP RSP` (`5C`) are
//! EXCLUDED: the first stores RSP itself and the second loads RSP from memory,
//! neither of which the walk's offset-tracked RSP models. `41 54`/`41 5C` are
//! PUSH/POP R12 and stay admitted. Everything else is outside, including the
//! profile-counter forms `48 B8+r imm64` (MOVABS), `F0 ...` (LOCK), `9C`/`9D`
//! (PUSHFQ/POPFQ), whose imm64 the JIT patches INSIDE the certified range
//! after certification without a manifest row, so refusing them is
//! load-bearing; the surviving dead parameter copy `48 89 F8`; jumps; NOPs.
//!
//! **Non-vacuity.** Each premise must be one of the three forms above; each
//! observed item must equate two structurally DIFFERENT terms of one width
//! (or be the memory item whose two reads differ); the premise set must hold
//! under a concrete witness assignment (so it is satisfiable); and a frameless
//! body whose items would all be identities is
//! [`X86EnvelopeUnsupported::Degenerate`].
//!
//! **Trusted.** The byte recognizer and the x86-64 semantics of the closed
//! set; the Rust fixup pairing (callee name and binding, hole offset, zero
//! placeholder); the manifest parser; the System V entry premises (alignment,
//! stack depth); the Ackermann transcription; the SMT-LIB serializer. Outside
//! this theorem: the JIT's rel32 patching and the absolute-jump veneers it
//! appends after certification, the identity of pre-relocation and published
//! bytes, and what the callee does.

use std::collections::{HashMap, HashSet};

use crate::lowering_proof::{MachineSideProvenance, ProofObligation, TransvalCheckKind};
use crate::smt::SmtExpr as E;
use crate::source_bound_source::linear_chain_to_end;
use crate::x86_source_bound_body::X86SourceBoundAbi;
use trust_cg_ir::function::StackProtectorMode;
use trust_cg_lower::instructions::{DirectCallBinding, Opcode as L};
use trust_cg_lower::{Function, Type};

/// Theorem name of the void-return envelope. Shape-constant: identical
/// theorems dedupe in AY's session and certificate caches.
pub const X86_VOID_RETURN_ENVELOPE_NAME: &str = "Source-bound x86-64 System V envelope (void return, final bytes): return target, stack, callee-saved registers and caller memory";

/// Theorem name of the diverging-call envelope. Shape-constant.
pub const X86_DIVERGING_CALL_ENVELOPE_NAME: &str = "Source-bound x86-64 System V envelope (diverging call, final bytes): aligned callee entry, trap return slot, callee-saved registers and caller memory";

/// Separates the theorem name from a part's label in a part's obligation name.
pub const X86_ENVELOPE_PART_SEPARATOR: &str = " | ";

/// Reason given when an envelope theorem was built but no independently
/// checked proof of it exists. Never credited.
pub const X86_ENVELOPE_NEEDS_REPLAY: &str =
    "source-bound x86 ABI envelope needs independently replayed proof";

/// Magic of the JIT's symbolic fixup manifest (v1).
pub const X86_SYMBOLIC_FIXUP_MANIFEST_MAGIC: &[u8] = b"trust-cg.jit.x86_64-symbolic-fixups.v1\0";

// Verify-owned register identities, ModR/M numbering.
const RSP: u16 = 4;
const RBP: u16 = 5;
const RBX: u16 = 3;
const R12: u16 = 12;
const R13: u16 = 13;
const R14: u16 = 14;
const R15: u16 = 15;

/// System V callee-saved GPRs the caller observes after a return.
const CALLEE_SAVED: [u16; 6] = [RBX, RBP, R12, R13, R14, R15];

const ROOT_NAMES: [&str; 16] = [
    "rax", "rcx", "rdx", "rbx", "rsp", "rbp", "rsi", "rdi", "r8", "r9", "r10", "r11", "r12", "r13",
    "r14", "r15",
];

/// One row of the JIT's symbolic fixup manifest.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum X86FixupRow {
    /// A CALL rel32 hole bound to `callee`.
    Call {
        offset: u64,
        callee: String,
        exact_module: bool,
    },
    /// A symbol reference hole (GlobalRef 0, ExternRefGot 1, TlsTlv 2,
    /// ExactFunctionAddr 3).
    Symbol {
        offset: u64,
        symbol: String,
        kind: u8,
    },
}

impl X86FixupRow {
    /// Certificate-relative offset of the patched 4-byte field.
    pub fn offset(&self) -> u64 {
        match self {
            Self::Call { offset, .. } | Self::Symbol { offset, .. } => *offset,
        }
    }
}

struct ManifestCursor<'b> {
    bytes: &'b [u8],
    pos: usize,
}

impl ManifestCursor<'_> {
    fn take(&mut self, len: usize) -> Result<&[u8], String> {
        let end = self
            .pos
            .checked_add(len)
            .filter(|end| *end <= self.bytes.len())
            .ok_or_else(|| format!("truncated at byte {}", self.pos))?;
        let slice = &self.bytes[self.pos..end];
        self.pos = end;
        Ok(slice)
    }

    fn u8(&mut self) -> Result<u8, String> {
        Ok(self.take(1)?[0])
    }

    fn u64(&mut self) -> Result<u64, String> {
        let bytes: [u8; 8] = self.take(8)?.try_into().expect("eight bytes");
        Ok(u64::from_be_bytes(bytes))
    }

    fn length(&mut self) -> Result<usize, String> {
        let len = self.u64()?;
        usize::try_from(len)
            .ok()
            .filter(|len| *len <= self.bytes.len() - self.pos)
            .ok_or_else(|| format!("length {len} at byte {} exceeds the encoding", self.pos))
    }

    fn part(&mut self, label: &[u8]) -> Result<String, String> {
        let len = self.length()?;
        if self.take(len)? != label {
            return Err(format!(
                "expected the `{}` label",
                String::from_utf8_lossy(label)
            ));
        }
        let len = self.length()?;
        String::from_utf8(self.take(len)?.to_vec()).map_err(|_| "a name is not UTF-8".to_owned())
    }
}

/// Parse the JIT's symbolic fixup manifest (v1) exactly: magic, big-endian
/// row count, then rows of (offset, kind, length-prefixed label and name,
/// flag). Any malformed field, unknown kind or flag, or trailing byte is an
/// error. This is verify-owned; the codegen encoder's round trip through it
/// is tested there.
pub fn parse_x86_symbolic_fixup_manifest(bytes: &[u8]) -> Result<Vec<X86FixupRow>, String> {
    let mut cursor = ManifestCursor { bytes, pos: 0 };
    if cursor.take(X86_SYMBOLIC_FIXUP_MANIFEST_MAGIC.len())? != X86_SYMBOLIC_FIXUP_MANIFEST_MAGIC {
        return Err("wrong magic".into());
    }
    let count = cursor.u64()?;
    // A row is at least 8 + 1 + (8 + 6) + 8 + 1 bytes.
    if count > (bytes.len() as u64) / 32 {
        return Err(format!("row count {count} exceeds the encoding"));
    }
    let mut rows = Vec::with_capacity(count as usize);
    for _ in 0..count {
        let offset = cursor.u64()?;
        match cursor.u8()? {
            0 => {
                let callee = cursor.part(b"callee")?;
                let exact_module = match cursor.u8()? {
                    0 => false,
                    1 => true,
                    flag => return Err(format!("call row exact-module flag {flag}")),
                };
                rows.push(X86FixupRow::Call {
                    offset,
                    callee,
                    exact_module,
                });
            }
            1 => {
                let symbol = cursor.part(b"symbol")?;
                let kind = cursor.u8()?;
                if kind > 3 {
                    return Err(format!("symbol row kind {kind}"));
                }
                rows.push(X86FixupRow::Symbol {
                    offset,
                    symbol,
                    kind,
                });
            }
            kind => return Err(format!("row kind {kind}")),
        }
    }
    if cursor.pos != bytes.len() {
        return Err(format!(
            "{} trailing byte(s) after {count} row(s)",
            bytes.len() - cursor.pos
        ));
    }
    Ok(rows)
}

/// The two admitted source shapes.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum X86EnvelopeShape {
    /// `Jump* ; Return` with no result and no call.
    VoidReturn,
    /// `Jump* ; Call f() ; Trap`: a zero-argument, zero-result direct call.
    DivergingCall { callee: String, exact_module: bool },
}

impl X86EnvelopeShape {
    /// The shape-constant theorem name.
    pub fn theorem_name(&self) -> &'static str {
        match self {
            Self::VoidReturn => X86_VOID_RETURN_ENVELOPE_NAME,
            Self::DivergingCall { .. } => X86_DIVERGING_CALL_ENVELOPE_NAME,
        }
    }
}

/// Why [`source_bound_x86_envelope`] built no theorem.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum X86EnvelopeRefusal {
    /// Outside the checked domain: no claim; ordinary refusals apply.
    #[error("unsupported x86-64 ABI envelope: {0}")]
    Unsupported(X86EnvelopeUnsupported),
    /// An admitted source whose recognized bytes or fixups are wrong.
    #[error("x86-64 ABI envelope mismatch: {0}")]
    Mismatch(X86EnvelopeMismatch),
}

impl X86EnvelopeRefusal {
    /// The typed mismatch, when this refusal identifies an erroneous target.
    pub fn mismatch(&self) -> Option<&X86EnvelopeMismatch> {
        match self {
            Self::Mismatch(mismatch) => Some(mismatch),
            Self::Unsupported(_) => None,
        }
    }
}

/// A (source, bytes, manifest, ABI) tuple outside the lane.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum X86EnvelopeUnsupported {
    #[error("no calling convention was supplied")]
    NoAbi,
    #[error("calling convention {0:?} is outside the lane (System V only)")]
    Abi(X86SourceBoundAbi),
    #[error("LIR source is outside the envelope domain: {0}")]
    Source(String),
    #[error("byte {offset} is outside the closed x86-64 envelope set: {detail}")]
    Bytes { offset: usize, detail: String },
    /// Every item would equate a term with itself (a frameless body).
    #[error("the envelope theorem would be degenerate: {0}")]
    Degenerate(String),
    /// A builder invariant failed. Never credit.
    #[error("the envelope theorem failed its construction check: {0}")]
    Construction(String),
}

/// A recognized envelope that disagrees with its source, its fixups or the
/// System V contract. No correct lowering produces one.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum X86EnvelopeMismatch {
    #[error("machine function `{machine}` is paired with LIR function `{source_name}`")]
    Pairing {
        machine: String,
        source_name: String,
    },
    #[error("symbolic fixup manifest is not exactly the judged holes: {0}")]
    Manifest(String),
    #[error("byte {offset}: {detail}")]
    Control { offset: usize, detail: String },
    #[error("byte {offset}: the source traps after its call, but no UD2 follows the CALL")]
    TrapMissing { offset: usize },
    #[error("the bytes make {found} call(s) where the source makes {expected}")]
    CallCount { expected: usize, found: usize },
    #[error("call at byte {offset} is bound to {found}, where the source calls {expected}")]
    CallTarget {
        offset: usize,
        expected: String,
        found: String,
    },
    #[error("call at byte {offset}: {detail}")]
    CallMetadata { offset: usize, detail: String },
    #[error("call at byte {offset}: the manifest's hole is at {hole}, not the rel32 at {expected}")]
    HolePlacement {
        offset: usize,
        hole: u64,
        expected: u64,
    },
    #[error("call at byte {offset}: the rel32 placeholder is not zero")]
    NonZeroPlaceholder { offset: usize },
    #[error("byte {offset}: RSP is rsp0{rsp_offset:+} where the return needs rsp0+0")]
    StackImbalance { offset: usize, rsp_offset: i64 },
    #[error("byte {offset}: {register} does not hold its entry value")]
    PreservedWrite {
        offset: usize,
        register: &'static str,
    },
    #[error("byte {offset}: the RET does not read the caller's return address")]
    ReturnAddress { offset: usize },
    #[error(
        "byte {offset}: the callee is entered at rsp0{callee_entry_offset:+}, so RSP+8 is not 16-byte aligned"
    )]
    Misaligned {
        offset: usize,
        callee_entry_offset: i64,
    },
    #[error("byte {offset}: writes the caller's memory at rsp0{rsp_offset:+}")]
    CallerMemoryWrite { offset: usize, rsp_offset: i64 },
    #[error("the concrete witness falsifies observed item {item}")]
    WitnessRefutes { item: usize },
}

fn unsupported(reason: X86EnvelopeUnsupported) -> X86EnvelopeRefusal {
    X86EnvelopeRefusal::Unsupported(reason)
}

fn mismatch(reason: X86EnvelopeMismatch) -> X86EnvelopeRefusal {
    X86EnvelopeRefusal::Mismatch(reason)
}

/// Immutable binding of one exact (LIR, final bytes, fixup manifest, ABI)
/// tuple to its envelope theorem. No public constructor: only
/// [`source_bound_x86_envelope`] builds one.
pub struct SourceBoundX86Envelope<'a> {
    source: &'a Function,
    code: &'a [u8],
    manifest: &'a [u8],
    abi: X86SourceBoundAbi,
    shape: X86EnvelopeShape,
    terminator: usize,
    statement: ProofObligation,
    parts: Vec<ProofObligation>,
}

/// One replayable part of a built envelope: the premises imply one goal of
/// the statement. No public constructor: only
/// [`SourceBoundX86Envelope::replay_parts`] hands one out, so a part is
/// always a part of an owner-built theorem.
pub struct X86EnvelopePart<'e> {
    obligation: &'e ProofObligation,
}

impl X86EnvelopePart<'_> {
    pub fn obligation(&self) -> &ProofObligation {
        self.obligation
    }
}

impl<'a> SourceBoundX86Envelope<'a> {
    pub fn source(&self) -> &'a Function {
        self.source
    }
    pub fn code(&self) -> &'a [u8] {
        self.code
    }
    pub fn manifest(&self) -> &'a [u8] {
        self.manifest
    }
    pub fn abi(&self) -> X86SourceBoundAbi {
        self.abi
    }
    pub fn shape(&self) -> &X86EnvelopeShape {
        &self.shape
    }
    /// Byte offset of the terminating RET or UD2. A function-level export is
    /// indexed by it.
    pub fn terminator_offset(&self) -> usize {
        self.terminator
    }
    /// The envelope theorem as one conjunction, the form the structural
    /// non-vacuity checks judge. It is never replayed: AY proves its
    /// [`Self::parts`]. Construction is not discharge.
    pub fn statement(&self) -> &ProofObligation {
        &self.statement
    }
    /// The replayed obligations: one per item, and one per byte of an item
    /// that compares a 64-bit memory read. The statement holds exactly when
    /// every part holds.
    pub fn parts(&self) -> &[ProofObligation] {
        &self.parts
    }
    /// The replay capabilities of [`Self::parts`], in order.
    pub fn replay_parts(&self) -> impl Iterator<Item = X86EnvelopePart<'_>> {
        self.parts
            .iter()
            .map(|obligation| X86EnvelopePart { obligation })
    }
}

fn admitted_abi(abi: Option<X86SourceBoundAbi>) -> Result<X86SourceBoundAbi, X86EnvelopeRefusal> {
    match abi {
        None => Err(unsupported(X86EnvelopeUnsupported::NoAbi)),
        Some(X86SourceBoundAbi::SystemV) => Ok(X86SourceBoundAbi::SystemV),
        Some(other) => Err(unsupported(X86EnvelopeUnsupported::Abi(other))),
    }
}

fn admitted_source(source: &Function) -> Result<X86EnvelopeShape, X86EnvelopeRefusal> {
    let domain = |reason: &str| unsupported(X86EnvelopeUnsupported::Source(reason.to_owned()));
    if !source.eh_info.is_empty()
        || source.stack_protector != StackProtectorMode::None
        || source.abi_sret_param.is_some()
        || !source.sret_arg_callees.is_empty()
        || !source.sret_arg_indirect_callees.is_empty()
    {
        return Err(domain("requires no EH, stack protector or sret metadata"));
    }
    if !source.signature.returns.is_empty() {
        return Err(domain("requires no result"));
    }
    if source.signature.params.len() > 6
        || !source
            .signature
            .params
            .iter()
            .all(|ty| matches!(ty, Type::B1 | Type::I8 | Type::I16 | Type::I32 | Type::I64))
    {
        return Err(domain(
            "requires at most six B1, I8, I16, I32 or I64 register parameters",
        ));
    }
    // Every block must lie on the one chain (checked by the view).
    let chain = linear_chain_to_end(source)
        .ok_or_else(|| domain("is not a bounded unconditional chain over every block"))?;
    let block = chain
        .view
        .blocks
        .get(&chain.view.entry_block)
        .ok_or_else(|| domain("has no entry block"))?;
    let bare = |inst: &trust_cg_lower::instructions::Instruction| {
        inst.args.is_empty() && inst.results.is_empty()
    };
    match block.instructions.as_slice() {
        [ret] if matches!(ret.opcode, L::Return) && bare(ret) => Ok(X86EnvelopeShape::VoidReturn),
        [call, trap] if matches!(trap.opcode, L::Trap) && bare(trap) && bare(call) => {
            let L::Call { name, binding } = &call.opcode else {
                return Err(domain(
                    "is not `Jump* ; Return` or `Jump* ; Call f() ; Trap`",
                ));
            };
            let exact_module = match binding {
                DirectCallBinding::Interposable => false,
                DirectCallBinding::ExactModuleFunction { .. } => true,
                DirectCallBinding::DeclaredExternalFunction { .. }
                | DirectCallBinding::NativeDependency { .. } => {
                    return Err(domain("calls a native dependency"));
                }
            };
            Ok(X86EnvelopeShape::DivergingCall {
                callee: name.clone(),
                exact_module,
            })
        }
        _ => Err(domain(
            "is not `Jump* ; Return` or `Jump* ; Call f() ; Trap` with no values",
        )),
    }
}

/// Whether [`source_bound_x86_envelope`] judges any machine code for
/// `source` under `abi`. `true` claims nothing about the bytes.
pub fn source_admits_x86_envelope_owner(source: &Function, abi: Option<X86SourceBoundAbi>) -> bool {
    admitted_source(source).is_ok() && admitted_abi(abi).is_ok()
}

/// One recognized instruction of the closed set.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Insn {
    Push(u16),
    Pop(u16),
    MovRbpRsp,
    SubRsp(u8),
    AddRsp(u8),
    Call { rel32: [u8; 4] },
    Ret,
    Ud2,
}

#[derive(Debug, Clone, Copy)]
struct Decoded {
    offset: usize,
    len: usize,
    insn: Insn,
}

fn outside(offset: usize, detail: impl Into<String>) -> X86EnvelopeRefusal {
    unsupported(X86EnvelopeUnsupported::Bytes {
        offset,
        detail: detail.into(),
    })
}

/// Recognize `code` over the closed set, or refuse at the first byte outside
/// it. Written from the Intel SDM encodings, independent of codegen's decoder.
fn recognize(code: &[u8]) -> Result<Vec<Decoded>, X86EnvelopeRefusal> {
    let mut out = Vec::new();
    let mut offset = 0;
    while offset < code.len() {
        let rest = &code[offset..];
        let (len, insn) = match rest {
            [0x54, ..] => {
                return Err(outside(
                    offset,
                    "PUSH RSP (54) stores RSP itself, which the walk's offset-tracked RSP does not model",
                ));
            }
            [0x5c, ..] => {
                return Err(outside(
                    offset,
                    "POP RSP (5C) loads RSP from memory, which the walk's offset-tracked RSP does not model",
                ));
            }
            [op @ 0x50..=0x57, ..] => (1, Insn::Push(u16::from(op - 0x50))),
            [op @ 0x58..=0x5f, ..] => (1, Insn::Pop(u16::from(op - 0x58))),
            [0x41, op @ 0x50..=0x57, ..] => (2, Insn::Push(u16::from(op - 0x50) + 8)),
            [0x41, op @ 0x58..=0x5f, ..] => (2, Insn::Pop(u16::from(op - 0x58) + 8)),
            [0x48, 0x89, 0xe5, ..] => (3, Insn::MovRbpRsp),
            [0x48, 0x83, 0xec, imm @ 1..=0x7f, ..] => (4, Insn::SubRsp(*imm)),
            [0x48, 0x83, 0xc4, imm @ 1..=0x7f, ..] => (4, Insn::AddRsp(*imm)),
            [0xe8, a, b, c, d, ..] => (
                5,
                Insn::Call {
                    rel32: [*a, *b, *c, *d],
                },
            ),
            [0xc3, ..] => (1, Insn::Ret),
            [0x0f, 0x0b, ..] => (2, Insn::Ud2),
            [byte, ..] => {
                let named = match byte {
                    0x48 if rest.get(1).is_some_and(|op| (0xb8..=0xbf).contains(op)) => {
                        " (MOVABS r64, imm64: the JIT patches such an imm64 after certification without a manifest row)"
                    }
                    0xf0 => " (LOCK prefix: a profile counter increment)",
                    0x9c | 0x9d => " (PUSHFQ/POPFQ: the profile-counter trampoline)",
                    0x90 => " (NOP)",
                    0xeb | 0xe9 => " (JMP)",
                    _ => "",
                };
                return Err(outside(
                    offset,
                    format!("{byte:02x}{named} is not an admitted encoding"),
                ));
            }
            [] => unreachable!("the loop runs only while bytes remain"),
        };
        out.push(Decoded { offset, len, insn });
        offset += len;
    }
    Ok(out)
}

/// Rust shadow value of a register or stack slot.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Shadow {
    Entry(u16),
    StackAddress(i64),
    Other,
}

/// Symbolic machine state.
#[derive(Clone)]
struct State {
    rsp: E,
    regs: Vec<E>,
    writes: Vec<(E, E)>,
}

/// Entry-memory inputs keyed by syntactic address.
#[derive(Default)]
struct BaseMemory {
    inputs: Vec<(String, E)>,
    by_address: HashMap<E, usize>,
}

impl BaseMemory {
    fn byte(&mut self, address: &E) -> E {
        let index = *self.by_address.entry(address.clone()).or_insert_with(|| {
            self.inputs
                .push((format!("mem_{}", self.inputs.len()), address.clone()));
            self.inputs.len() - 1
        });
        E::var(self.inputs[index].0.clone(), 8)
    }
}

fn entry_name(root: u16) -> String {
    format!("{}_0", ROOT_NAMES[root as usize])
}

fn offset_address(base: &E, k: u64) -> E {
    if k == 0 {
        base.clone()
    } else {
        base.clone().bvadd(E::bv_const(k, 64))
    }
}

fn read_byte(state: &State, memory: &mut BaseMemory, address: &E) -> E {
    let mut value = memory.byte(address);
    for (written, byte) in &state.writes {
        value = E::ite(
            written.clone().eq_expr(address.clone()),
            byte.clone(),
            value,
        );
    }
    value
}

fn read64(state: &State, memory: &mut BaseMemory, address: &E) -> E {
    (0..8)
        .rev()
        .map(|k| read_byte(state, memory, &offset_address(address, k)))
        .reduce(|high, low| high.concat(low))
        .expect("eight bytes")
}

fn write64(state: &mut State, address: &E, value: &E) {
    for k in 0..8u32 {
        state.writes.push((
            offset_address(address, u64::from(k)),
            value.clone().extract(8 * k + 7, 8 * k),
        ));
    }
}

/// What the walk leaves for the theorem.
struct Walked {
    /// Final state (void return: after the RET; diverging: at callee entry).
    state: State,
    /// Void return: the RET's target.
    rip: Option<E>,
    /// Diverging: `code_base + offset(UD2)`.
    return_target: Option<E>,
    /// Lowest RSP offset any write reached (<= 0).
    lowest_offset: i64,
    terminator: usize,
    /// Refusals the theorem also carries (the solver judges them too).
    semantic: Vec<X86EnvelopeMismatch>,
}

fn walk(
    shape: &X86EnvelopeShape,
    code: &[u8],
    decoded: &[Decoded],
    manifest: &[X86FixupRow],
    memory: &mut BaseMemory,
) -> Result<Walked, X86EnvelopeRefusal> {
    let mut state = State {
        rsp: E::var("rsp0", 64),
        regs: (0..16).map(|root| E::var(entry_name(root), 64)).collect(),
        writes: Vec::new(),
    };
    let mut shadow_regs: Vec<Shadow> = (0..16).map(Shadow::Entry).collect();
    let mut shadow_slots: HashMap<i64, Shadow> = HashMap::new();
    let mut rsp_offset: i64 = 0;
    let mut lowest_offset: i64 = 0;
    let mut semantic = Vec::new();
    let mut calls = 0usize;
    let mut rip = None;
    let mut return_target = None;
    let mut terminator = None;
    let expected_calls = usize::from(matches!(shape, X86EnvelopeShape::DivergingCall { .. }));

    let mut index = 0;
    while index < decoded.len() {
        let Decoded { offset, len, insn } = decoded[index];
        if let Some(end) = terminator {
            return Err(mismatch(X86EnvelopeMismatch::Control {
                offset,
                detail: format!("an instruction follows the terminator at byte {end}"),
            }));
        }
        match insn {
            Insn::Push(root) => {
                rsp_offset -= 8;
                lowest_offset = lowest_offset.min(rsp_offset);
                if rsp_offset > -8 {
                    semantic.push(X86EnvelopeMismatch::CallerMemoryWrite { offset, rsp_offset });
                }
                state.rsp = state.rsp.clone().bvsub(E::bv_const(8, 64));
                let value = state.regs[root as usize].clone();
                let address = state.rsp.clone();
                write64(&mut state, &address, &value);
                shadow_slots.insert(rsp_offset, shadow_regs[root as usize]);
            }
            Insn::Pop(root) => {
                let address = state.rsp.clone();
                state.regs[root as usize] = read64(&state, memory, &address);
                shadow_regs[root as usize] = shadow_slots
                    .get(&rsp_offset)
                    .copied()
                    .unwrap_or(Shadow::Other);
                rsp_offset += 8;
                state.rsp = state.rsp.clone().bvadd(E::bv_const(8, 64));
            }
            Insn::MovRbpRsp => {
                state.regs[RBP as usize] = state.rsp.clone();
                shadow_regs[RBP as usize] = Shadow::StackAddress(rsp_offset);
            }
            Insn::SubRsp(imm) => {
                rsp_offset -= i64::from(imm);
                lowest_offset = lowest_offset.min(rsp_offset);
                state.rsp = state.rsp.clone().bvsub(E::bv_const(u64::from(imm), 64));
            }
            Insn::AddRsp(imm) => {
                rsp_offset += i64::from(imm);
                state.rsp = state.rsp.clone().bvadd(E::bv_const(u64::from(imm), 64));
            }
            Insn::Call { rel32 } => {
                calls += 1;
                let X86EnvelopeShape::DivergingCall {
                    callee,
                    exact_module,
                } = shape
                else {
                    return Err(mismatch(X86EnvelopeMismatch::CallCount {
                        expected: 0,
                        found: calls,
                    }));
                };
                if calls > 1 {
                    return Err(mismatch(X86EnvelopeMismatch::CallCount {
                        expected: 1,
                        found: calls,
                    }));
                }
                check_call_row(offset, callee, *exact_module, manifest, code.len())?;
                if rel32 != [0; 4] {
                    return Err(mismatch(X86EnvelopeMismatch::NonZeroPlaceholder { offset }));
                }
                let next = offset + len;
                // The source's trap: the first UD2 the recognizer placed after
                // the CALL. A CALL or RET between them is refused here; any
                // other recognized instruction between them is recorded as the
                // semantic TrapMissing below, which the owner refuses before a
                // theorem is built. Only the test-only walk-free builder lets
                // such bytes reach a theorem, whose return-slot item (stated
                // against this recognized offset, not against the address the
                // CALL pushes) is then falsified.
                let rest = &decoded[index + 1..];
                let Some(trap_at) = rest.iter().position(|d| matches!(d.insn, Insn::Ud2)) else {
                    return Err(mismatch(X86EnvelopeMismatch::TrapMissing { offset: next }));
                };
                for between in &rest[..trap_at] {
                    match between.insn {
                        Insn::Call { .. } => {
                            return Err(mismatch(X86EnvelopeMismatch::CallCount {
                                expected: 1,
                                found: calls + 1,
                            }));
                        }
                        Insn::Ret => {
                            return Err(mismatch(X86EnvelopeMismatch::Control {
                                offset: between.offset,
                                detail: "RET where the source traps".into(),
                            }));
                        }
                        _ => {}
                    }
                }
                let trap_offset = rest[trap_at].offset;
                if trap_offset != next {
                    semantic.push(X86EnvelopeMismatch::TrapMissing { offset: next });
                }
                // The CALL pushes the address of the next instruction.
                rsp_offset -= 8;
                lowest_offset = lowest_offset.min(rsp_offset);
                if rsp_offset > -8 {
                    semantic.push(X86EnvelopeMismatch::CallerMemoryWrite { offset, rsp_offset });
                }
                // rsp0 = 8 (mod 16) at entry, so callee-entry RSP (rsp0 + offset)
                // meets the same rule exactly when offset = 0 (mod 16).
                if rsp_offset.rem_euclid(16) != 0 {
                    semantic.push(X86EnvelopeMismatch::Misaligned {
                        offset,
                        callee_entry_offset: rsp_offset,
                    });
                }
                for root in [RBX, R12, R13, R14, R15] {
                    if shadow_regs[root as usize] != Shadow::Entry(root) {
                        semantic.push(X86EnvelopeMismatch::PreservedWrite {
                            offset,
                            register: ROOT_NAMES[root as usize],
                        });
                    }
                }
                // x86-64 CALL semantics: the pushed return address is the
                // address of the byte after the CALL.
                let pushed = E::var("code_base", 64).bvadd(E::bv_const(next as u64, 64));
                state.rsp = state.rsp.clone().bvsub(E::bv_const(8, 64));
                let address = state.rsp.clone();
                write64(&mut state, &address, &pushed);
                // What the theorem requires of the slot: the recognized UD2.
                return_target =
                    Some(E::var("code_base", 64).bvadd(E::bv_const(trap_offset as u64, 64)));
                terminator = Some(trap_offset);
                // The state stays at callee entry: the instructions between the
                // CALL and the UD2 run only if the callee returns.
                index += 1 + trap_at + 1;
                continue;
            }
            Insn::Ret => {
                if !matches!(shape, X86EnvelopeShape::VoidReturn) {
                    return Err(mismatch(X86EnvelopeMismatch::Control {
                        offset,
                        detail: "RET where the source traps".into(),
                    }));
                }
                if rsp_offset != 0 {
                    semantic.push(X86EnvelopeMismatch::StackImbalance { offset, rsp_offset });
                } else if shadow_slots.contains_key(&0) {
                    semantic.push(X86EnvelopeMismatch::ReturnAddress { offset });
                }
                for root in CALLEE_SAVED {
                    if shadow_regs[root as usize] != Shadow::Entry(root) {
                        semantic.push(X86EnvelopeMismatch::PreservedWrite {
                            offset,
                            register: ROOT_NAMES[root as usize],
                        });
                    }
                }
                let address = state.rsp.clone();
                rip = Some(read64(&state, memory, &address));
                state.rsp = state.rsp.clone().bvadd(E::bv_const(8, 64));
                terminator = Some(offset);
            }
            Insn::Ud2 => {
                return Err(mismatch(X86EnvelopeMismatch::Control {
                    offset,
                    detail: match shape {
                        X86EnvelopeShape::VoidReturn => "UD2 where the source returns".into(),
                        X86EnvelopeShape::DivergingCall { .. } => {
                            "UD2 before the source's call".into()
                        }
                    },
                }));
            }
        }
        index += 1;
    }
    let Some(terminator) = terminator else {
        return Err(mismatch(X86EnvelopeMismatch::Control {
            offset: code.len(),
            detail: "the bytes end without a RET or CALL; UD2".into(),
        }));
    };
    if calls != expected_calls {
        return Err(mismatch(X86EnvelopeMismatch::CallCount {
            expected: expected_calls,
            found: calls,
        }));
    }
    if matches!(shape, X86EnvelopeShape::VoidReturn) && !manifest.is_empty() {
        return Err(mismatch(X86EnvelopeMismatch::Manifest(format!(
            "a body with no call has {} fixup row(s)",
            manifest.len()
        ))));
    }
    Ok(Walked {
        state,
        rip,
        return_target,
        lowest_offset,
        terminator,
        semantic,
    })
}

/// Manifest completeness for the one CALL at `offset`: exactly one row, a
/// call row, at the disp32, naming the source's callee and binding.
fn check_call_row(
    offset: usize,
    callee: &str,
    exact_module: bool,
    manifest: &[X86FixupRow],
    code_len: usize,
) -> Result<(), X86EnvelopeRefusal> {
    let hole = offset as u64 + 1;
    let row = match manifest {
        [row] => row,
        rows => {
            return Err(mismatch(X86EnvelopeMismatch::Manifest(format!(
                "a body with one call has {} fixup row(s)",
                rows.len()
            ))));
        }
    };
    let X86FixupRow::Call {
        offset: row_offset,
        callee: row_callee,
        exact_module: row_exact,
    } = row
    else {
        return Err(mismatch(X86EnvelopeMismatch::Manifest(format!(
            "the only fixup row is a symbol row: {row:?}"
        ))));
    };
    if *row_offset != hole || row_offset.saturating_add(4) > code_len as u64 {
        return Err(mismatch(X86EnvelopeMismatch::HolePlacement {
            offset,
            hole: *row_offset,
            expected: hole,
        }));
    }
    let describe = |name: &str, exact: bool| {
        format!(
            "`{name}` ({})",
            if exact {
                "exact module function"
            } else {
                "by symbol"
            }
        )
    };
    if row_callee != callee {
        return Err(mismatch(X86EnvelopeMismatch::CallTarget {
            offset,
            expected: describe(callee, exact_module),
            found: describe(row_callee, *row_exact),
        }));
    }
    if *row_exact != exact_module {
        return Err(mismatch(X86EnvelopeMismatch::CallMetadata {
            offset,
            detail: format!(
                "the manifest binds {} where the source binds {}",
                describe(row_callee, *row_exact),
                describe(callee, exact_module)
            ),
        }));
    }
    Ok(())
}

/// Base variable and constant offset of an address term built by the walk.
fn affine_address(address: &E) -> Option<(String, u64)> {
    match address {
        E::Var { name, width: 64 } => Some((name.clone(), 0)),
        E::BvAdd { lhs, rhs, .. } => match rhs.as_ref() {
            E::BvConst { value, .. } => {
                affine_address(lhs).map(|(base, offset)| (base, offset.wrapping_add(*value)))
            }
            _ => None,
        },
        E::BvSub { lhs, rhs, .. } => match rhs.as_ref() {
            E::BvConst { value, .. } => {
                affine_address(lhs).map(|(base, offset)| (base, offset.wrapping_sub(*value)))
            }
            _ => None,
        },
        _ => None,
    }
}

/// The ABI entry-alignment rule over `rsp`: `RSP + 8` is 16-byte aligned.
fn aligned_entry(rsp: E) -> E {
    rsp.bvadd(E::bv_const(8, 64))
        .extract(3, 0)
        .eq_expr(E::bv_const(0, 4))
}

/// Metadata of a built theorem the checks and tests need.
#[derive(Debug, Clone)]
pub(crate) struct EnvelopeTheorem {
    pub(crate) obligation: ProofObligation,
    /// Every entry-memory input and its address term.
    pub(crate) memory: Vec<(String, E)>,
    /// The observed items, in order.
    pub(crate) items: Vec<E>,
    /// One shape-constant label per item.
    pub(crate) labels: Vec<String>,
    /// The replayed obligations ([`split_parts`]).
    pub(crate) parts: Vec<ProofObligation>,
    pub(crate) depth: u64,
}

fn build_theorem(
    shape: &X86EnvelopeShape,
    walked: Walked,
    mut memory: BaseMemory,
) -> Result<EnvelopeTheorem, X86EnvelopeRefusal> {
    let rsp0 = E::var("rsp0", 64);
    let mut items: Vec<E> = Vec::new();
    let mut labels: Vec<String> = Vec::new();
    let state = &walked.state;
    let preserved: &[u16] = match shape {
        X86EnvelopeShape::VoidReturn => &CALLEE_SAVED,
        X86EnvelopeShape::DivergingCall { .. } => &[RBX, R12, R13, R14, R15],
    };
    match shape {
        X86EnvelopeShape::VoidReturn => {
            let rip = walked.rip.clone().expect("a void return walks a RET");
            let caller_return = (0..8)
                .rev()
                .map(|k| memory.byte(&offset_address(&rsp0, k)))
                .reduce(|high, low| high.concat(low))
                .expect("eight bytes");
            items.push(rip.eq_expr(caller_return));
            labels.push("return target".into());
            items.push(
                state
                    .rsp
                    .clone()
                    .eq_expr(rsp0.clone().bvadd(E::bv_const(8, 64))),
            );
            labels.push("RSP after the return".into());
        }
        X86EnvelopeShape::DivergingCall { .. } => {
            items.push(aligned_entry(state.rsp.clone()));
            labels.push("callee-entry alignment".into());
            let target = walked
                .return_target
                .clone()
                .expect("a diverging call walks a CALL");
            let slot = read64(state, &mut memory, &state.rsp.clone());
            items.push(slot.eq_expr(target));
            labels.push("trap return slot".into());
        }
    }
    for &root in preserved {
        let entry = E::var(entry_name(root), 64);
        if state.regs[root as usize] != entry {
            items.push(state.regs[root as usize].clone().eq_expr(entry));
            labels.push(format!("{} preserved", ROOT_NAMES[root as usize]));
        }
    }
    if !state.writes.is_empty() {
        let obs = E::var("obs", 64);
        let final_byte = read_byte(state, &mut memory, &obs);
        let base_byte = memory.byte(&obs);
        items.push(
            obs.clone()
                .bvult(rsp0.clone())
                .or_expr(final_byte.eq_expr(base_byte)),
        );
        labels.push("caller memory at or above rsp0".into());
    }
    // Per-item identity refusal: an item that equates a term with itself
    // states nothing about these bytes.
    for (index, item) in items.iter().enumerate() {
        if item_is_identity(item) {
            return Err(unsupported(X86EnvelopeUnsupported::Degenerate(format!(
                "observed item {index} equates a term with itself"
            ))));
        }
    }
    let depth = walked.lowest_offset.unsigned_abs();
    // Premises: alignment, depth, then the Ackermann pairs.
    let mut premises = vec![aligned_entry(rsp0.clone())];
    if depth > 0 {
        premises.push(rsp0.clone().bvuge(E::bv_const(depth, 64)));
    }
    let addresses: Vec<Option<(String, u64)>> = memory
        .inputs
        .iter()
        .map(|(_, address)| affine_address(address))
        .collect();
    for i in 0..memory.inputs.len() {
        for j in i + 1..memory.inputs.len() {
            if addresses[i].is_some() && addresses[i] == addresses[j] {
                let (name_i, address_i) = &memory.inputs[i];
                let (name_j, address_j) = &memory.inputs[j];
                premises.push(ackermann(name_i, address_i, name_j, address_j));
            }
        }
    }
    let machine_side = items
        .iter()
        .cloned()
        .rev()
        .reduce(|tail, item| item.and_expr(tail))
        .expect("at least one item");
    let mut inputs: Vec<(String, u32)> = vec![("rsp0".into(), 64)];
    let mentioned: HashSet<String> = machine_side
        .free_vars()
        .into_iter()
        .chain(premises.iter().flat_map(|premise| premise.free_vars()))
        .collect();
    for root in 0..16u16 {
        let name = entry_name(root);
        if root != RSP && mentioned.contains(&name) {
            inputs.push((name, 64));
        }
    }
    for name in ["code_base", "obs"] {
        if mentioned.contains(name) {
            inputs.push((name.into(), 64));
        }
    }
    for (name, _) in &memory.inputs {
        inputs.push((name.clone(), 8));
    }
    // `negated_equivalence` nests the LAST precondition outermost.
    let preconditions: Vec<E> = premises.into_iter().rev().collect();
    let obligation = ProofObligation {
        name: shape.theorem_name().into(),
        trust_ir_expr: E::bool_const(true),
        aarch64_expr: machine_side,
        inputs,
        preconditions,
        fp_inputs: Vec::new(),
        category: Some(TransvalCheckKind::ControlFlow),
        machine_side_provenance: MachineSideProvenance::StaticDb,
    };
    let parts = split_parts(&obligation, &items, &labels);
    Ok(EnvelopeTheorem {
        obligation,
        memory: memory.inputs,
        items,
        labels,
        parts,
        depth,
    })
}

/// The eight bytes of a 64-bit term, least significant first: the leaves of
/// a byte concatenation (a memory read) as they stand, any other term through
/// `extract`. `None` for a term that is neither 64 bits wide nor such a read.
fn bytes_of(term: &E) -> Option<Vec<E>> {
    fn leaves(term: &E, out: &mut Vec<E>) {
        match term {
            E::Concat { hi, lo, .. } => {
                leaves(hi, out);
                leaves(lo, out);
            }
            leaf => out.push(leaf.clone()),
        }
    }
    if term.try_bv_width().ok()? != 64 {
        return None;
    }
    if matches!(term, E::Concat { .. }) {
        let mut out = Vec::new();
        leaves(term, &mut out);
        if out.len() == 8 && out.iter().all(|b| b.try_bv_width().ok() == Some(8)) {
            out.reverse();
            return Some(out);
        }
        return None;
    }
    Some(
        (0..8)
            .map(|k| term.clone().extract(8 * k + 7, 8 * k))
            .collect(),
    )
}

/// The replayed goals of one observed item: an equation whose left side is a
/// 64-bit memory read (a byte concatenation) is split into its eight byte
/// equations, least significant byte first; every other item is one goal.
/// The conjunction of the goals is equivalent to the item.
fn split_item(item: &E, label: &str) -> Vec<(String, E)> {
    if let E::Eq { lhs, rhs } = item
        && matches!(lhs.as_ref(), E::Concat { .. })
        && let (Some(left), Some(right)) = (bytes_of(lhs), bytes_of(rhs))
    {
        return left
            .into_iter()
            .zip(right)
            .enumerate()
            .map(|(k, (l, r))| (format!("{label} byte {k}"), l.eq_expr(r)))
            .collect();
    }
    vec![(label.to_owned(), item.clone())]
}

/// The theorem as replayed: one obligation per goal ([`split_item`]), each
/// under the full premise set and input declarations of `statement`. The
/// theorem holds exactly when every part does. Part names are shape-constant
/// (`<theorem name> | <item label>[ byte k]`), so identical parts dedupe.
fn split_parts(
    statement: &ProofObligation,
    items: &[E],
    labels: &[String],
) -> Vec<ProofObligation> {
    items
        .iter()
        .zip(labels)
        .flat_map(|(item, label)| split_item(item, label))
        .map(|(label, goal)| ProofObligation {
            name: format!("{}{X86_ENVELOPE_PART_SEPARATOR}{label}", statement.name),
            aarch64_expr: goal,
            ..statement.clone()
        })
        .collect()
}

/// Whether `name` is an envelope part's obligation name.
pub fn is_x86_envelope_part_name(name: &str) -> bool {
    [
        X86_VOID_RETURN_ENVELOPE_NAME,
        X86_DIVERGING_CALL_ENVELOPE_NAME,
    ]
    .iter()
    .any(|theorem| {
        name.strip_prefix(theorem)
            .is_some_and(|rest| rest.starts_with(X86_ENVELOPE_PART_SEPARATOR))
    })
}

/// The parts are exactly the mechanical split of the checked statement: same
/// premises, inputs and category, goals in item order, and no goal is a
/// syntactic identity.
pub(crate) fn check_envelope_parts(theorem: &EnvelopeTheorem) -> Result<(), String> {
    if theorem.labels.len() != theorem.items.len() {
        return Err("every item needs exactly one label".into());
    }
    let expected = split_parts(&theorem.obligation, &theorem.items, &theorem.labels);
    if theorem.parts != expected {
        return Err("the replayed parts are not the split of the statement".into());
    }
    for part in &theorem.parts {
        if let E::Eq { lhs, rhs } = &part.aarch64_expr
            && lhs == rhs
        {
            return Err(format!("part `{}` is an identity", part.name));
        }
    }
    Ok(())
}

fn ackermann(name_i: &str, address_i: &E, name_j: &str, address_j: &E) -> E {
    address_i
        .clone()
        .eq_expr(address_j.clone())
        .not_expr()
        .or_expr(E::var(name_i, 8).eq_expr(E::var(name_j, 8)))
}

fn item_is_identity(item: &E) -> bool {
    match item {
        E::Eq { lhs, rhs } => lhs == rhs,
        E::Or { rhs, .. } => matches!(rhs.as_ref(), E::Eq { lhs, rhs } if lhs == rhs),
        _ => false,
    }
}

/// Structural non-vacuity of a built envelope theorem: the statement is
/// `true` against a right-nested conjunction of at least two items, each an
/// equation of two DIFFERENT terms of one width or the caller-memory item;
/// every premise is exactly one permitted form; every name is declared once.
pub(crate) fn check_envelope_structure(theorem: &EnvelopeTheorem) -> Result<(), String> {
    let obligation = &theorem.obligation;
    if obligation.trust_ir_expr != E::bool_const(true) {
        return Err("the statement is not stated against `true`".into());
    }
    if !obligation.fp_inputs.is_empty() {
        return Err("floating-point inputs are outside the envelope".into());
    }
    let mut items = Vec::new();
    let mut rest = &obligation.aarch64_expr;
    loop {
        match rest {
            E::And { lhs, rhs } => {
                items.push(lhs.as_ref());
                rest = rhs.as_ref();
            }
            last => {
                items.push(last);
                break;
            }
        }
    }
    if items.len() < 2 {
        return Err("the conjunction states fewer than two items".into());
    }
    if items.len() != theorem.items.len() || items.iter().zip(&theorem.items).any(|(a, b)| *a != b)
    {
        return Err("the conjunction is not the builder's item list".into());
    }
    let rsp0 = E::var("rsp0", 64);
    for (index, item) in items.iter().enumerate() {
        match item {
            E::Eq { lhs, rhs } => {
                if lhs == rhs {
                    return Err(format!("observed item {index} is an identity"));
                }
                match (lhs.try_bv_width(), rhs.try_bv_width()) {
                    (Ok(a), Ok(b)) if a == b => {}
                    _ => return Err(format!("observed item {index} mixes widths")),
                }
            }
            E::Or { lhs, rhs } => {
                let bound = rsp0.clone();
                let E::BvUlt {
                    lhs: obs,
                    rhs: floor,
                    ..
                } = lhs.as_ref()
                else {
                    return Err(format!("memory item {index} has no `obs < rsp0` guard"));
                };
                if **obs != E::var("obs", 64) || **floor != bound {
                    return Err(format!("memory item {index} guards another range"));
                }
                let E::Eq {
                    lhs: machine,
                    rhs: base,
                } = rhs.as_ref()
                else {
                    return Err(format!("memory item {index} is not an equation"));
                };
                if machine == base {
                    return Err(format!("memory item {index} is an identity"));
                }
            }
            other => return Err(format!("observed item {index} has form {other}")),
        }
    }
    let memory: HashMap<&str, &E> = theorem
        .memory
        .iter()
        .map(|(name, address)| (name.as_str(), address))
        .collect();
    let mut alignment = 0;
    let mut depth = 0;
    let mut pairs = HashSet::new();
    for premise in &obligation.preconditions {
        if *premise == aligned_entry(rsp0.clone()) {
            alignment += 1;
            continue;
        }
        if *premise == rsp0.clone().bvuge(E::bv_const(theorem.depth, 64)) && theorem.depth > 0 {
            depth += 1;
            continue;
        }
        let permitted = match premise {
            E::Or { lhs, rhs } => match (lhs.as_ref(), rhs.as_ref()) {
                (E::Not { operand }, E::Eq { lhs: m_i, rhs: m_j }) => {
                    match (operand.as_ref(), m_i.as_ref(), m_j.as_ref()) {
                        (
                            E::Eq { lhs: a_i, rhs: a_j },
                            E::Var {
                                name: n_i,
                                width: 8,
                            },
                            E::Var {
                                name: n_j,
                                width: 8,
                            },
                        ) => {
                            n_i != n_j
                                && memory.get(n_i.as_str()) == Some(&a_i.as_ref())
                                && memory.get(n_j.as_str()) == Some(&a_j.as_ref())
                                && pairs.insert((n_i.clone(), n_j.clone()))
                        }
                        _ => false,
                    }
                }
                _ => false,
            },
            _ => false,
        };
        if !permitted {
            return Err(format!("premise {premise} is not a permitted form"));
        }
    }
    if alignment != 1 || depth != usize::from(theorem.depth > 0) {
        return Err("the entry premises are not exactly one alignment and one depth".into());
    }
    let mut declared = HashSet::new();
    for (name, width) in &obligation.inputs {
        if !declared.insert(name.as_str()) {
            return Err(format!("input {name} is declared twice"));
        }
        let expected = if memory.contains_key(name.as_str()) {
            8
        } else {
            64
        };
        if *width != expected {
            return Err(format!("input {name} is declared at width {width}"));
        }
    }
    let used: HashSet<String> = obligation
        .aarch64_expr
        .free_vars()
        .into_iter()
        .chain(obligation.preconditions.iter().flat_map(|p| p.free_vars()))
        .collect();
    for name in &used {
        if !declared.contains(name.as_str()) {
            return Err(format!("{name} is used but not declared"));
        }
    }
    Ok(())
}

/// A concrete assignment satisfying every premise: `rsp0` congruent to 8
/// modulo 16 and far above the stack depth, distinct register values, and
/// entry memory as ONE function of the evaluated address (so every
/// Ackermann premise holds).
pub(crate) fn witness(theorem: &EnvelopeTheorem, rsp0: u64, obs: u64) -> HashMap<String, u64> {
    let mut env: HashMap<String, u64> = HashMap::new();
    env.insert("rsp0".into(), rsp0);
    env.insert("obs".into(), obs);
    env.insert("code_base".into(), 0x0000_5555_0000_0000);
    for root in 0..16u16 {
        env.insert(
            entry_name(root),
            0x0101_0101_0101_0101u64.wrapping_mul(u64::from(root) + 0x11),
        );
    }
    for (name, address) in &theorem.memory {
        let at = address
            .try_eval(&env)
            .map(|value| value.as_u64())
            .unwrap_or(0);
        env.insert(name.clone(), memory_byte(at));
    }
    env
}

fn memory_byte(address: u64) -> u64 {
    (address.wrapping_mul(0x9e37_79b9_7f4a_7c15) >> 56) ^ 0x5a
}

fn holds(expr: &E, env: &HashMap<String, u64>) -> Result<bool, String> {
    expr.try_eval(env)
        .map(|value| value.as_bool())
        .map_err(|error| format!("evaluation failed: {error:?}"))
}

/// Evaluate the premises and each item under `env`.
pub(crate) fn evaluate(
    theorem: &EnvelopeTheorem,
    env: &HashMap<String, u64>,
) -> Result<(bool, Vec<bool>), String> {
    let mut premises = true;
    for premise in &theorem.obligation.preconditions {
        premises &= holds(premise, env)?;
    }
    let items = theorem
        .items
        .iter()
        .map(|item| holds(item, env))
        .collect::<Result<Vec<_>, _>>()?;
    Ok((premises, items))
}

const WITNESS_RSP0: u64 = 0x0000_7ffe_1234_5678;

fn witness_rsp0(depth: u64) -> u64 {
    // Congruent to 8 modulo 16, and above any depth the walk can reach.
    ((WITNESS_RSP0 + depth) & !0xf) | 0x8
}

fn construct<'a>(
    source: &'a Function,
    function_name: &str,
    code: &'a [u8],
    manifest: &'a [u8],
    abi: Option<X86SourceBoundAbi>,
    enforce_walk: bool,
) -> Result<(X86EnvelopeShape, X86SourceBoundAbi, usize, EnvelopeTheorem), X86EnvelopeRefusal> {
    let shape = admitted_source(source)?;
    let abi = admitted_abi(abi)?;
    if source.name != function_name {
        return Err(mismatch(X86EnvelopeMismatch::Pairing {
            machine: function_name.to_owned(),
            source_name: source.name.clone(),
        }));
    }
    let decoded = recognize(code)?;
    let rows = parse_x86_symbolic_fixup_manifest(manifest)
        .map_err(|error| mismatch(X86EnvelopeMismatch::Manifest(error)))?;
    let mut memory = BaseMemory::default();
    let walked = walk(&shape, code, &decoded, &rows, &mut memory)?;
    if enforce_walk && let Some(first) = walked.semantic.first() {
        return Err(mismatch(first.clone()));
    }
    let terminator = walked.terminator;
    let theorem = build_theorem(&shape, walked, memory)?;
    check_envelope_structure(&theorem)
        .and_then(|()| check_envelope_parts(&theorem))
        .map_err(|reason| unsupported(X86EnvelopeUnsupported::Construction(reason)))?;
    let rsp0 = witness_rsp0(theorem.depth);
    let env = witness(&theorem, rsp0, rsp0);
    let (premises, items) = evaluate(&theorem, &env)
        .map_err(|reason| unsupported(X86EnvelopeUnsupported::Construction(reason)))?;
    if !premises {
        return Err(unsupported(X86EnvelopeUnsupported::Construction(
            "the premises do not hold under the concrete witness".into(),
        )));
    }
    if enforce_walk && let Some(item) = items.iter().position(|holds| !holds) {
        return Err(mismatch(X86EnvelopeMismatch::WitnessRefutes { item }));
    }
    Ok((shape, abi, terminator, theorem))
}

/// Build the envelope theorem for an admitted source, the exact final bytes
/// of its function and the JIT's symbolic fixup manifest for them. See the
/// module documentation.
pub fn source_bound_x86_envelope<'a>(
    source: &'a Function,
    function_name: &str,
    code: &'a [u8],
    manifest: &'a [u8],
    abi: Option<X86SourceBoundAbi>,
) -> Result<SourceBoundX86Envelope<'a>, X86EnvelopeRefusal> {
    let (shape, abi, terminator, theorem) =
        construct(source, function_name, code, manifest, abi, true)?;
    Ok(SourceBoundX86Envelope {
        source,
        code,
        manifest,
        abi,
        shape,
        terminator,
        statement: theorem.obligation,
        parts: theorem.parts,
    })
}

/// What [`crate::X86FunctionVerifier::verify_abi_envelope`] found.
#[derive(Debug, Clone)]
pub enum X86EnvelopeOutcome {
    /// Outside the lane: no claim, no certificate.
    Unsupported(X86EnvelopeUnsupported),
    /// A recognized envelope that is wrong: the function must be refused.
    Mismatch(X86EnvelopeMismatch),
    /// A theorem was built and replayed part by part
    /// ([`SourceBoundX86Envelope::parts`]). Only a Valid verdict for EVERY
    /// part (an AY proof Clean independently accepted, each) is credit, and
    /// then `exports` holds one export per part, in order.
    Built {
        theorem_name: &'static str,
        parts: Vec<X86EnvelopePartVerdict>,
        exports: Vec<crate::SourceBoundArithmeticObligation>,
    },
}

/// The replay verdict of one envelope part.
#[derive(Debug, Clone)]
pub struct X86EnvelopePartVerdict {
    /// The part's obligation name (`<theorem> | <label>`).
    pub name: String,
    /// `Some(Valid)`: proven and independently accepted; `Some(Invalid)`:
    /// refuted; `None`: no independently checked proof (replay refused,
    /// unavailable or inconclusive, or not attempted because an earlier part
    /// had no Valid replay).
    pub verdict: Option<crate::verify::VerificationResult>,
    /// Why a part without a Valid replay has none, when known: the replay
    /// was not requested or was refused (and by what), the raw AY outcome
    /// that was not an independently checked proof, or that an earlier part
    /// stopped the replay. Diagnostic text only, never evidence.
    pub detail: Option<String>,
}

/// THE credit rule: a Valid replay (an AY proof Clean independently
/// accepted) of EVERY part, of a non-empty part list. Used by the report
/// assembly and by [`X86EnvelopeOutcome::is_credited`].
fn every_part_valid(parts: &[X86EnvelopePartVerdict]) -> bool {
    !parts.is_empty()
        && parts
            .iter()
            .all(|part| matches!(part.verdict, Some(crate::verify::VerificationResult::Valid)))
}

impl X86EnvelopeOutcome {
    /// Whether this outcome is credit: a built theorem EVERY part of which has
    /// a Valid replay (an AY proof Clean independently accepted, each), with
    /// one export per part.
    pub fn is_credited(&self) -> bool {
        matches!(
            self,
            Self::Built { parts, exports, .. }
                if exports.len() == parts.len() && every_part_valid(parts)
        )
    }

    /// The first part without a Valid replay, and how many parts were Valid.
    pub fn first_unproven_part(&self) -> Option<(&X86EnvelopePartVerdict, usize)> {
        let Self::Built { parts, .. } = self else {
            return None;
        };
        let valid = parts
            .iter()
            .filter(|part| matches!(part.verdict, Some(crate::verify::VerificationResult::Valid)))
            .count();
        parts
            .iter()
            .find(|part| !matches!(part.verdict, Some(crate::verify::VerificationResult::Valid)))
            .map(|part| (part, valid))
    }
}

/// The envelope verdict for one function, bound to its exact input and (only
/// when every part's Valid replay was bound to the request's reusable
/// authority) to that request's identity.
#[derive(Debug, Clone)]
pub struct X86EnvelopeReport {
    function_name: String,
    outcome: X86EnvelopeOutcome,
    input: [u8; 32],
    identity: Option<[u8; 32]>,
}

impl X86EnvelopeReport {
    pub(crate) fn new(
        function_name: &str,
        outcome: X86EnvelopeOutcome,
        input: [u8; 32],
        identity: Option<[u8; 32]>,
    ) -> Self {
        Self {
            function_name: function_name.to_owned(),
            outcome,
            input,
            identity,
        }
    }

    pub fn function_name(&self) -> &str {
        &self.function_name
    }

    pub fn outcome(&self) -> &X86EnvelopeOutcome {
        &self.outcome
    }

    /// Whether every part of the theorem was proven and each proof
    /// independently accepted.
    pub fn is_valid(&self) -> bool {
        self.outcome.is_credited()
    }

    /// Whether this report may be served to `request` from a cache: only a
    /// Valid replay bound to the same reusable authority.
    pub fn reusable_for(&self, request: &crate::FunctionVerificationRequest) -> bool {
        self.is_valid()
            && self.identity.is_some()
            && self.identity == request.reuse_identity()
            && request.may_reuse()
    }

    /// Resident-size estimate of the retained theorem (cache accounting).
    pub fn estimated_theorem_bytes(&self) -> usize {
        match &self.outcome {
            X86EnvelopeOutcome::Built { exports, .. } => exports
                .iter()
                .map(|export| export.obligation().to_smt2().len())
                .sum(),
            _ => 0,
        }
    }

    /// Whether this report was computed for exactly this input.
    pub fn matches_input(
        &self,
        lir: &Function,
        function_name: &str,
        code: &[u8],
        manifest: &[u8],
        abi: Option<X86SourceBoundAbi>,
    ) -> bool {
        self.input
            == crate::function_request::x86_envelope_input(lir, function_name, code, manifest, abi)
    }
}

/// Assemble the report of a built owner from its parts' replay verdicts (one
/// `(verdict, detail)` per part, in order). Credit ([`every_part_valid`]):
/// one export per part, and the request's reusable identity only when every
/// Valid replay was `bound` to the request's authority and the request may
/// reuse. Anything less exports nothing and carries no identity.
pub(crate) fn envelope_report(
    function_name: &str,
    owner: &SourceBoundX86Envelope<'_>,
    input: [u8; 32],
    verdicts: Vec<(Option<crate::verify::VerificationResult>, Option<String>)>,
    bound: bool,
    request: &crate::FunctionVerificationRequest,
) -> X86EnvelopeReport {
    let mut verdicts = verdicts.into_iter();
    let parts: Vec<X86EnvelopePartVerdict> = owner
        .parts()
        .iter()
        .map(|part| {
            let (verdict, detail) = verdicts.next().unwrap_or((
                None,
                Some("no replay verdict was supplied for this part".into()),
            ));
            X86EnvelopePartVerdict {
                name: part.name.clone(),
                verdict,
                detail,
            }
        })
        .collect();
    let valid = every_part_valid(&parts);
    let reusable = valid && bound && request.may_reuse();
    let exports = if valid {
        owner
            .parts()
            .iter()
            .map(|part| {
                crate::SourceBoundArithmeticObligation::x86_envelope(
                    input,
                    function_name,
                    owner.terminator_offset(),
                    part.clone(),
                )
            })
            .collect()
    } else {
        Vec::new()
    };
    X86EnvelopeReport::new(
        function_name,
        X86EnvelopeOutcome::Built {
            theorem_name: owner.shape().theorem_name(),
            parts,
            exports,
        },
        input,
        reusable.then(|| request.reuse_identity()).flatten(),
    )
}

/// The theorem the owner would build WITHOUT its Rust shadow-walk and
/// witness refusals (recognition, control, manifest and pairing checks still
/// apply). Tests use it to hand a WRONG body to the solver or evaluator; it is
/// not an owner and cannot be replayed live.
#[cfg(test)]
pub(crate) fn theorem_without_walk_refusal(
    source: &Function,
    function_name: &str,
    code: &[u8],
    manifest: &[u8],
    abi: Option<X86SourceBoundAbi>,
) -> Result<EnvelopeTheorem, X86EnvelopeRefusal> {
    construct(source, function_name, code, manifest, abi, false).map(|(_, _, _, theorem)| theorem)
}

/// The theorem and its audit metadata for a built owner (tests).
#[cfg(test)]
pub(crate) fn theorem_of(
    source: &Function,
    function_name: &str,
    code: &[u8],
    manifest: &[u8],
    abi: Option<X86SourceBoundAbi>,
) -> Result<EnvelopeTheorem, X86EnvelopeRefusal> {
    construct(source, function_name, code, manifest, abi, true).map(|(_, _, _, theorem)| theorem)
}

#[cfg(test)]
#[path = "x86_source_bound_envelope_tests.rs"]
mod tests;
