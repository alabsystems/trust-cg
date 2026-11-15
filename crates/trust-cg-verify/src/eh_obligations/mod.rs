// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Exception-table obligations for AArch64 Darwin objects and JIT images
//! (ledger L03-P14).
//!
//! Given the emitted bytes and what the compiler's machine IR says each
//! function is (its landing blocks and their catch/filter clauses, which
//! call each invoke protects, its personality, its EH type table and the
//! frame its frame owner laid out), these checks decide, by re-parsing the
//! bytes with decoders written independently of the emitters:
//!
//! * `CallSiteCoverage`: every call that can unwind (every `BL`/`BLR` word
//!   of the function, except one the IR declares unable to unwind) lies in
//!   exactly one LSDA call-site record, read the way the personalities read
//!   the table (sorted, non-overlapping, looked up at the return address
//!   minus one); a filler LSDA of a function without EH structure must cover
//!   its calls too, since its personality is consulted;
//! * `LandingPad`: that record's landing pad is the offset of the landing
//!   block the IR assigns the invoke, or none for a call that is not an
//!   invoke, and no record names any other landing pad;
//! * `ActionTable`: the action chain of every landing pad is the IR's
//!   clause list under the selector contract (catch type index `k` is
//!   filter `k`, its slot GOT-relocated to the IR's typeinfo symbol; the
//!   catch-all is filter `N + 1` over a NULL slot; Rust's empty filter is
//!   filter -1 over an empty list; a cleanup ends the chain with filter 0);
//! * `Personality` and `LsdaBinding`: the compact-unwind entry (or, for a
//!   DWARF-fallback frame, the FDE and its CIE) names the personality the
//!   function names and the LSDA decoded above; a function without EH
//!   structure carries none, or a filler LSDA that names no landing pad;
//! * `FrameDescription`: the compact encoding or FDE rows describe exactly
//!   the frame the frame owner laid out (CFA rule, FP/LR record and every
//!   callee-saved slot);
//! * `UnwindPointFrame`: at every call that can unwind and that control
//!   reaches from the entry or a reached landing pad (the unwind points of
//!   synchronous exceptions; an unreached call is dead code), the frame
//!   state computed from the function's own words (`flow`) satisfies the
//!   description: the CFA rule yields the entry stack pointer, every slot it
//!   names holds that register's entry value, the return address is
//!   recovered from a slot, and every callee-saved register it does not name
//!   still holds its entry value.
//!
//! Evidence strength: these are exact decisions over the bytes, made in
//! process by trusted Rust. They are TESTING-GRADE evidence, not a
//! certificate; no Clean-checked certificate exists for them (OD-139: an
//! in-process decision is never credit). They assume the personality
//! routines and the unwinder interpret the tables as the Itanium ABI and
//! DWARF specify (trusted base TB-21), that the IR side (machine EH metadata
//! and frame layout) is what the source meant (TB-13), and the store-alias
//! boundary stated in [`flow`].

mod a64;
mod cfi;
mod check;
mod flow;
mod lsda;
mod macho;

pub use check::{check_jit_image, check_macho_object};

/// A register a frame description can name.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum EhReg {
    /// General-purpose register Xn (n < 31).
    X(u8),
    /// The low 64 bits of SIMD&FP register Vn.
    D(u8),
}

impl EhReg {
    /// The DWARF register number (AArch64 DWARF ABI).
    pub fn dwarf(self) -> u64 {
        match self {
            Self::X(n) => u64::from(n),
            Self::D(n) => 64 + u64::from(n),
        }
    }

    fn from_dwarf(number: u64) -> Option<Self> {
        match number {
            0..=30 => Some(Self::X(number as u8)),
            64..=95 => Some(Self::D((number - 64) as u8)),
            _ => None,
        }
    }

    /// The AAPCS64 callee-saved registers whose values an unwinder must
    /// recover: X19-X29 and D8-D15.
    fn callee_saved() -> impl Iterator<Item = Self> {
        (19..=29).map(Self::X).chain((8..=15).map(Self::D))
    }
}

impl std::fmt::Display for EhReg {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::X(n) => write!(f, "x{n}"),
            Self::D(n) => write!(f, "d{n}"),
        }
    }
}

/// The frame the frame owner laid out.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EhFrameIntent {
    /// Every saved register (the FP/LR record included) with its slot's
    /// byte offset from the CFA (negative).
    pub saved: Vec<(EhReg, i64)>,
    /// X29 is set up as the frame pointer (CFA = X29 + 16).
    pub uses_frame_pointer: bool,
    /// Total frame size in bytes (the SP-based CFA offset of a frame
    /// without a frame pointer).
    pub total_frame_size: u32,
}

/// One catch/filter clause of a landing pad, in the IR's order.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EhClause {
    /// Catch type index `k` (0 is the catch-all).
    Catch(u32),
    /// Rust's empty exception specification (stop phase-one search here).
    RustEmptyFilter,
}

/// One landing block of the IR.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EhLandingPadIntent {
    /// The machine block id (for diagnostics).
    pub block: u32,
    /// The block's byte offset from the function start.
    pub offset: u32,
    pub clauses: Vec<EhClause>,
    pub cleanup: bool,
}

/// One invoke: the call instruction and the landing block it unwinds to.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct EhInvokeIntent {
    /// Byte offset of the protected `BL`/`BLR` from the function start.
    pub call_offset: u32,
    /// The landing block (`EhLandingPadIntent::block`).
    pub landing_block: u32,
}

/// What the IR says a function's exception tables must express.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EhTablesIntent {
    /// Object-level personality symbol (Mach-O: with its `_` prefix).
    pub personality: String,
    pub landing_pads: Vec<EhLandingPadIntent>,
    pub invokes: Vec<EhInvokeIntent>,
    /// `N`, the length of the function's EH type table (the catch-all is
    /// filter `N + 1`).
    pub type_table_len: u64,
    /// The object-level typeinfo symbol of every catch type index a clause
    /// names (index 0, the catch-all, has none).
    pub typeinfo: Vec<(u32, String)>,
}

/// One function of an object or image.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EhFunctionIntent {
    /// The function's name, for diagnostics.
    pub symbol: String,
    /// Byte offset of the function in the object's `__text` (Mach-O; the
    /// JIT front end places functions through [`EhImageFunction`]).
    pub text_offset: u64,
    /// Bytes of instructions (jump tables follow them).
    pub body_len: u32,
    /// Encoded length: the unwind range.
    pub code_len: u32,
    pub frame: EhFrameIntent,
    /// Offsets of the calls the IR declares cannot unwind (a TLS-descriptor
    /// call, a call flagged as unable to unwind, and, under the
    /// non-unwinding-frame policy, a direct call to a callee declared
    /// `nounwind`). They are not unwind points, and need no call-site record
    /// unless they are invokes.
    pub nounwind_calls: Vec<u32>,
    /// `None` for a function without exception-handling structure.
    pub eh: Option<EhTablesIntent>,
}

/// The functions of one object or JIT image, in emission order.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct EhObjectIntent {
    pub functions: Vec<EhFunctionIntent>,
}

/// The obligations, by name.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum EhObligationKind {
    /// The container (Mach-O object or JIT image) did not decode.
    ObjectDecode,
    /// An LSDA did not decode or is not a well-formed table.
    LsdaStructure,
    /// `__eh_frame` did not decode or a CFA program is outside the
    /// admitted instruction set.
    CfiStructure,
    /// The frame-state analysis could not follow the function's words.
    FrameFlow,
    /// A function lacks its unwind entry, or carries a stray or
    /// inconsistent one.
    UnwindEntry,
    /// A call that can unwind is not in exactly one call-site record.
    CallSiteCoverage,
    /// A record's landing pad is not the IR's landing block.
    LandingPad,
    /// An action chain is not the IR's clause list.
    ActionTable,
    /// The personality is not the one the function names.
    Personality,
    /// The unwind entry does not name the function's LSDA.
    LsdaBinding,
    /// The unwind description is not the frame owner's frame.
    FrameDescription,
    /// At a call, the unwind description does not recover the frame the
    /// function's words built.
    UnwindPointFrame,
    /// The IR-side intent is not consistent with the bytes it describes.
    Intent,
}

impl EhObligationKind {
    /// Stable name used in diagnostics and reports.
    pub fn name(self) -> &'static str {
        match self {
            Self::ObjectDecode => "object-decode",
            Self::LsdaStructure => "lsda-structure",
            Self::CfiStructure => "cfi-structure",
            Self::FrameFlow => "frame-flow",
            Self::UnwindEntry => "unwind-entry",
            Self::CallSiteCoverage => "call-site-coverage",
            Self::LandingPad => "landing-pad",
            Self::ActionTable => "action-table",
            Self::Personality => "personality",
            Self::LsdaBinding => "lsda-binding",
            Self::FrameDescription => "frame-description",
            Self::UnwindPointFrame => "unwind-point-frame",
            Self::Intent => "intent",
        }
    }
}

impl std::fmt::Display for EhObligationKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.name())
    }
}

/// A violated obligation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EhObligationViolation {
    pub kind: EhObligationKind,
    /// The function (object-level symbol), when the obligation is per
    /// function.
    pub function: Option<String>,
    pub detail: String,
}

pub(crate) type Violation = EhObligationViolation;

impl EhObligationViolation {
    pub(crate) fn object(kind: EhObligationKind, detail: impl Into<String>) -> Self {
        Self {
            kind,
            function: None,
            detail: detail.into(),
        }
    }

    pub(crate) fn in_function(mut self, function: &str) -> Self {
        if self.function.is_none() {
            self.function = Some(function.to_string());
        }
        self
    }
}

impl std::fmt::Display for EhObligationViolation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self.function {
            Some(function) => write!(
                f,
                "[TCG-EH-OBLIGATION] {} violated for `{function}`: {}",
                self.kind, self.detail
            ),
            None => write!(
                f,
                "[TCG-EH-OBLIGATION] {} violated: {}",
                self.kind, self.detail
            ),
        }
    }
}

impl std::error::Error for EhObligationViolation {}

/// What held, counted per obligation instance.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct EhObligationReport {
    /// Functions checked.
    pub functions: usize,
    /// Functions with exception-handling structure.
    pub eh_functions: usize,
    /// Calls the analysis reached that can unwind (unwind points).
    pub unwind_points: usize,
    /// Call words no control flow from the entry or a reached landing pad
    /// reaches (dead code; their call-site records are still checked).
    pub unreached_calls: usize,
    /// Calls found inside a call-site record.
    pub covered_calls: usize,
    /// Calls bound to an IR landing pad.
    pub invokes: usize,
    /// Landing pads whose action chain was checked.
    pub landing_pads: usize,
    /// Functions described by a compact-unwind encoding (FRAME/FRAMELESS).
    pub compact_frames: usize,
    /// Functions described by an FDE.
    pub dwarf_frames: usize,
}

impl EhObligationReport {
    /// One line for traces and test output.
    pub fn summary(&self) -> String {
        format!(
            "functions={} eh_functions={} unwind_points={} unreached_calls={} covered_calls={} invokes={} landing_pads={} compact_frames={} dwarf_frames={}",
            self.functions,
            self.eh_functions,
            self.unwind_points,
            self.unreached_calls,
            self.covered_calls,
            self.invokes,
            self.landing_pads,
            self.compact_frames,
            self.dwarf_frames
        )
    }
}

/// One function of a JIT image.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EhImageFunction {
    /// Image offset of the function entry.
    pub code_offset: u64,
    /// Image offset of its FDE (inside `eh_frame`).
    pub fde_offset: u64,
}

/// A JIT image as published: final bytes at their final addresses.
#[derive(Debug, Clone)]
pub struct EhImage<'a> {
    /// The image bytes (code, then unwind tables, LSDAs and slots).
    pub bytes: &'a [u8],
    /// The address the image is mapped at.
    pub base: u64,
    /// Image offset and length of the `.eh_frame` section.
    pub eh_frame: (u64, u64),
    /// One entry per intent function, in the same order.
    pub functions: Vec<EhImageFunction>,
    /// Personality symbol -> the address the image's personality slot must
    /// hold (the JIT's resolved binding).
    pub personalities: Vec<(String, u64)>,
}
