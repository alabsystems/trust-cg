// trust-cg-verify/wasm_cfg_proofs.rs - P4 family 1: the CFG/structural invariant
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Reference: WebAssembly Core Specification, Release 2.0 — §3.3.5 (the typing
//            rules for `block`/`loop`/`if` and `br`/`br_if`/`br_table`), §3.3.9
//            (instruction sequences), §7.3.2 "Validation Algorithm" (the
//            control-stack + polymorphic value-stack algorithm this module
//            re-implements), and §5.4.1 (the binary encoding of the control
//            instructions).
//
// Skeleton: Ramsey, "Beyond Relooper: Recursive Translation of Unstructured
//           Control Flow to Structured Control Flow" (ICFP 2022) — the
//           dominator-tree recursion the wasm backend's `lower.rs` mirrors.
//
// WHAT THIS FAMILY IS, STATED BEFORE ANYTHING ELSE CAN BE OVER-READ.
//
// P4 family 1 in the ladder is named "CFG/SSA semantic simulation (relooper
// bisimulation, ... a structural invariant as the per-compile artifact)". This
// module builds THE PER-COMPILE ARTIFACT AND NOTHING MORE. It is the invariant
// the design names in one sentence.
//
// WHICH COMPILES ACTUALLY CARRY IT, stated exactly, because "per-compile" is a
// claim about a caller and not about this file. [`check_module_structure`] is
// invoked by `trust_cg_codegen::wasm::lower::compile_module_with_evidence`
// and `..._with_evidence_and_policy` — the EVIDENCE-carrying compile routes —
// over the bytes those routes just emitted. A refuted verdict FAILS the compile
// (`WasmLowerError::StructuralInvariantRefuted`); an inconclusive one is filed
// in the evidence's `not_run` list and earns nothing; a holding one is filed in
// `ran` with its counts and moves NOTHING ELSE — that compile's verdict stays
// `MissingEvidence` and its route stays `NotRun`, because what follows is why.
// The plain `compile_module` / `compile_module_with_policy` routes emit the same
// bytes and do NOT run it; the verdict is a property of the evidence route.
//
// The invariant, in one sentence:
//
//   > every `br` depth resolves to a live label reaching the intended
//   > successor, and the value stack is height/type-consistent at every join
//
// checked over the REAL EMITTED BYTES by an independent decoder. It is a
// NECESSARY CONDITION on structuring. It is NOT a bisimulation: nothing here
// says the structured wasm program computes what the trust-ir CFG computes.
// A wasm module can satisfy every invariant in this file and still be a
// miscompile — see [`WASM_CFG_DEFERRALS`], where the bisimulation itself is
// registered as a RED named deferral, and see
// [`MutantExpectation::KnownBlindSpot`], where two concrete wrong lowerings
// that this invariant CANNOT see are shipped as executable evidence of the gap
// rather than as prose. NOTHING in this module promotes the wasm lane out of
// DIFFERENTIAL-EXPERIMENTAL.
//
// WHY IT IS WORTH BUILDING ANYWAY. The invariant already has a real bug under
// it. P3 (`8ff365ef`) found and fixed a merge-child ORDERING defect in exactly
// this area: `node_within` nested merge children EARLIEST-RPO-outermost
// (`split_first`) where Ramsey §4 requires LATEST-outermost (`split_last`), so
// an earlier merge child's subtree was emitted OUTSIDE a later sibling's block
// and its forward branch had no label in scope. That defect's byte-level
// signature is precisely "a `br` whose depth does not name a live label", which
// is invariant B1 below — and the mis-ordered nest is shipped here as a
// synthetic mutant ([`misordered_merge_nest_module`]) that the checker must
// refute.
//
// HOW THE TWO SIDES ARE KEPT APART (anti-tautology). The machine side is
// RECONSTRUCTED: [`decode_module`] and [`decode_body`] parse the emitted `.wasm`
// bytes from scratch — an independent ULEB128/SLEB128 reader, an independent
// section walk, an independent instruction table — and never call
// `trust_cg_codegen::wasm::encode`. No item in this module IMPORTS the codegen
// crate — every entry point takes BYTES, the caller named above is on the other
// side of the dependency edge (trust-cg-codegen depends on trust-cg-verify, never
// the reverse), and the only mentions of it here are in prose like this one. That
// is what keeps the production dependency graph one-way and keeps the machine
// side rebuilt rather than borrowed. The source side is the SPEC's validation
// algorithm, transcribed
// from §7.3.2, not from `lower.rs`. A decoder that cannot read a byte FAILS
// CLOSED as `Inconclusive` — never as "checked" — so an unrecognized opcode is
// visible debt, not silent credit.
//
// THE INVARIANTS, and what each one can actually refute, are enumerated in
// [`WASM_CFG_INVARIANTS`] with a `does_not_cover` field on every row. Two of the
// facts this module reports are DERIVED, not checked, and are labeled as such
// rather than counted: a branch's continuation OFFSET and its FORWARD/BACKWARD
// direction are theorems of this module's own bracket matching, so an obligation
// asserting them would be checking this file against itself. They are reported
// as artifact content (a reader can audit the resolved target of every branch)
// and excluded from the invariant denominator.

//! P4 family 1 — the WebAssembly CFG/structural invariant: an independent
//! decode of the emitted code section, the spec's control-stack/value-stack
//! validation algorithm run over it, per-branch label resolution, and the named
//! deferrals (bisimulation first among them) that this invariant does NOT
//! discharge.

use std::fmt;

// ===========================================================================
// Value types and scope kinds
// ===========================================================================

/// The wasm number types this checker models. `v128` and the reference types
/// are deliberately absent: the backend rejects them, and a module containing
/// one must fail CLOSED (`Inconclusive`) rather than be waved through.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ValKind {
    /// `i32` (spec byte 0x7f).
    I32,
    /// `i64` (spec byte 0x7e).
    I64,
    /// `f32` (spec byte 0x7d).
    F32,
    /// `f64` (spec byte 0x7c).
    F64,
}

impl ValKind {
    /// Decode a spec `valtype` byte. `None` for every byte outside the four
    /// number types (fail closed).
    pub fn from_byte(b: u8) -> Option<Self> {
        match b {
            0x7f => Some(ValKind::I32),
            0x7e => Some(ValKind::I64),
            0x7d => Some(ValKind::F32),
            0x7c => Some(ValKind::F64),
            _ => None,
        }
    }

    /// The spec mnemonic, for report rows and violation messages.
    pub fn name(self) -> &'static str {
        match self {
            ValKind::I32 => "i32",
            ValKind::I64 => "i64",
            ValKind::F32 => "f32",
            ValKind::F64 => "f64",
        }
    }
}

impl fmt::Display for ValKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.name())
    }
}

/// The kind of structured-control scope a label belongs to. The distinction is
/// what makes a label's CONTINUATION well-defined: a `br` to a `loop` label
/// re-enters the loop's own start, a `br` to any other label leaves at the
/// matching `end`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ScopeKind {
    /// The implicit outermost label of a function body: `br` to it RETURNS.
    Func,
    /// `block` (0x02) — a forward label; the continuation is the matching `end`.
    Block,
    /// `loop` (0x03) — a BACKWARD label; the continuation is the loop opener.
    Loop,
    /// `if` (0x04) — a forward label, like `block`.
    If,
    /// The `else` (0x05) half of an `if`; a forward label with the same types.
    Else,
}

impl ScopeKind {
    /// The spec keyword.
    pub fn name(self) -> &'static str {
        match self {
            ScopeKind::Func => "func",
            ScopeKind::Block => "block",
            ScopeKind::Loop => "loop",
            ScopeKind::If => "if",
            ScopeKind::Else => "else",
        }
    }

    /// Does a `br` to this label transfer control BACKWARD (to the scope's own
    /// opener) rather than forward to its `end`? True only for `loop`.
    pub fn is_backward(self) -> bool {
        matches!(self, ScopeKind::Loop)
    }
}

// ===========================================================================
// Verdicts: refuted / inconclusive are DIFFERENT, and neither is green
// ===========================================================================

/// A STRUCTURAL DEFECT found in the emitted bytes: the checker read the module
/// and the invariant does not hold. This is a refutation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CfgViolation {
    /// B1 — a `br`/`br_if`/`br_table` depth names no live label. This is the
    /// byte-level signature of the P3 merge-child ordering defect.
    BranchDepthOutOfRange {
        /// Function index in the module's function index space.
        func: u32,
        /// Byte offset of the branch opcode within the function body.
        offset: usize,
        /// The decoded depth immediate.
        depth: u32,
        /// How many labels were actually live at that point.
        live_labels: usize,
    },
    /// B3 — a `br_table` entry's label arity differs from the default label's.
    /// The spec requires every entry of one table to take the same types.
    BrTableArityMismatch {
        /// Function index.
        func: u32,
        /// Byte offset of the `br_table` opcode.
        offset: usize,
        /// The entry index (`None` = the default label).
        entry: Option<usize>,
        /// The default label's arity.
        default_arity: usize,
        /// This entry's arity.
        entry_arity: usize,
    },
    /// J1 — the value stack height at a join (`end`/`else`) does not match the
    /// scope's entry height plus its results.
    JoinHeightMismatch {
        /// Function index.
        func: u32,
        /// Byte offset of the `end`/`else`.
        offset: usize,
        /// The scope being closed.
        scope: ScopeKind,
        /// The height the scope was entered at.
        expected: usize,
        /// The height actually reached.
        found: usize,
    },
    /// J2 — a value of the wrong TYPE was found where the rule demands another.
    /// Covers both join types and operand types.
    TypeMismatch {
        /// Function index.
        func: u32,
        /// Byte offset of the instruction that demanded the type.
        offset: usize,
        /// The type the rule requires.
        expected: ValKind,
        /// The type actually on the stack.
        found: ValKind,
    },
    /// J3 — an instruction popped past the bottom of its enclosing scope, in
    /// reachable (non-polymorphic) code.
    StackUnderflow {
        /// Function index.
        func: u32,
        /// Byte offset of the instruction.
        offset: usize,
    },
    /// S1 — an `else` whose enclosing scope is not an `if`.
    ElseWithoutIf {
        /// Function index.
        func: u32,
        /// Byte offset of the `else`.
        offset: usize,
    },
    /// S2 — an `end` with no scope to close.
    EndWithoutScope {
        /// Function index.
        func: u32,
        /// Byte offset of the `end`.
        offset: usize,
    },
    /// S3 — the body ran out with scopes still open (a dropped `end`).
    UnclosedScopes {
        /// Function index.
        func: u32,
        /// How many scopes were still open, the function label included.
        open: usize,
    },
    /// S4 — instructions follow the `end` that closes the function label.
    TrailingCodeAfterFunctionEnd {
        /// Function index.
        func: u32,
        /// Byte offset of the first trailing instruction.
        offset: usize,
    },
    /// S5 — an `if` with a result type and no `else` branch.
    IfWithResultsHasNoElse {
        /// Function index.
        func: u32,
        /// Byte offset of the `if`.
        offset: usize,
    },
    /// M1 — an index immediate (local / global / function / type) is out of
    /// range for the module. Not an indexing PROOF (that is family 4) — it is
    /// the minimum this checker needs to give an instruction a type at all.
    IndexOutOfRange {
        /// Function index.
        func: u32,
        /// Byte offset of the instruction.
        offset: usize,
        /// What kind of index it was.
        space: &'static str,
        /// The decoded index.
        index: u32,
        /// The number of entries in that space.
        count: usize,
    },
}

impl fmt::Display for CfgViolation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            CfgViolation::BranchDepthOutOfRange {
                func,
                offset,
                depth,
                live_labels,
            } => write!(
                f,
                "func {func} @0x{offset:x}: br depth {depth} names no live label ({live_labels} \
                 live) — the merge-child ordering signature"
            ),
            CfgViolation::BrTableArityMismatch {
                func,
                offset,
                entry,
                default_arity,
                entry_arity,
            } => write!(
                f,
                "func {func} @0x{offset:x}: br_table entry {entry:?} takes {entry_arity} value(s), \
                 default takes {default_arity}"
            ),
            CfgViolation::JoinHeightMismatch {
                func,
                offset,
                scope,
                expected,
                found,
            } => write!(
                f,
                "func {func} @0x{offset:x}: value stack height {found} at the {} join, expected {expected}",
                scope.name()
            ),
            CfgViolation::TypeMismatch {
                func,
                offset,
                expected,
                found,
            } => write!(
                f,
                "func {func} @0x{offset:x}: expected {expected} on the value stack, found {found}"
            ),
            CfgViolation::StackUnderflow { func, offset } => write!(
                f,
                "func {func} @0x{offset:x}: value stack underflow in reachable code"
            ),
            CfgViolation::ElseWithoutIf { func, offset } => {
                write!(f, "func {func} @0x{offset:x}: `else` outside an `if`")
            }
            CfgViolation::EndWithoutScope { func, offset } => {
                write!(f, "func {func} @0x{offset:x}: `end` with no open scope")
            }
            CfgViolation::UnclosedScopes { func, open } => write!(
                f,
                "func {func}: body ended with {open} scope(s) still open — a dropped `end`"
            ),
            CfgViolation::TrailingCodeAfterFunctionEnd { func, offset } => write!(
                f,
                "func {func} @0x{offset:x}: code after the function label's `end`"
            ),
            CfgViolation::IfWithResultsHasNoElse { func, offset } => write!(
                f,
                "func {func} @0x{offset:x}: `if` with results and no `else`"
            ),
            CfgViolation::IndexOutOfRange {
                func,
                offset,
                space,
                index,
                count,
            } => write!(
                f,
                "func {func} @0x{offset:x}: {space} index {index} out of range ({count} entries)"
            ),
        }
    }
}

/// The checker COULD NOT SPEAK about this module. Distinct from
/// [`CfgViolation`] on purpose: an inconclusive verdict is never credit, never
/// a refutation, and never silently dropped — it is counted in its own column
/// so a module the decoder cannot read reads as DEBT.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CfgUnsupported {
    /// The bytes do not start with the wasm magic + version 1.
    NotAWasmModule,
    /// A section (or an item inside one) ran off the end of its slice.
    Truncated {
        /// Where the truncation was noticed.
        what: &'static str,
    },
    /// A section id outside the spec's 0..=12.
    UnknownSection {
        /// The id byte.
        id: u8,
    },
    /// A malformed section item (bad tag byte, over-long LEB, ...).
    Malformed {
        /// Which structure was malformed.
        what: &'static str,
    },
    /// A `valtype` byte outside the four number types — `v128`/`funcref`/
    /// `externref` land here, which is why they cannot be silently accepted.
    UnsupportedValType {
        /// The byte.
        byte: u8,
    },
    /// An opcode byte this checker has no rule for. FAIL CLOSED: an opcode
    /// without a typing rule is exactly the thing that must not be waved past.
    UnknownOpcode {
        /// Function index.
        func: u32,
        /// Byte offset within the body.
        offset: usize,
        /// The opcode byte.
        byte: u8,
    },
    /// A `0xfc`-prefixed opcode this checker has no rule for.
    UnknownPrefixedOpcode {
        /// Function index.
        func: u32,
        /// Byte offset within the body.
        offset: usize,
        /// The sub-index after the prefix.
        sub: u32,
    },
    /// An instruction's immediate ran off the end of the body.
    TruncatedInstruction {
        /// Function index.
        func: u32,
        /// Byte offset within the body.
        offset: usize,
    },
    /// A `blocktype` this checker does not model — today the multi-value form
    /// (a positive s33 type index). The backend emits only 0x40, so this is a
    /// fail-closed frontier rather than a limitation being papered over.
    UnsupportedBlockType {
        /// Function index.
        func: u32,
        /// Byte offset within the body.
        offset: usize,
        /// The first byte of the blocktype.
        byte: u8,
    },
}

impl fmt::Display for CfgUnsupported {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            CfgUnsupported::NotAWasmModule => f.write_str("not a wasm module (magic/version)"),
            CfgUnsupported::Truncated { what } => write!(f, "truncated {what}"),
            CfgUnsupported::UnknownSection { id } => write!(f, "unknown section id {id}"),
            CfgUnsupported::Malformed { what } => write!(f, "malformed {what}"),
            CfgUnsupported::UnsupportedValType { byte } => {
                write!(
                    f,
                    "valtype 0x{byte:02x} is outside the modeled number types"
                )
            }
            CfgUnsupported::UnknownOpcode { func, offset, byte } => write!(
                f,
                "func {func} @0x{offset:x}: opcode 0x{byte:02x} has no typing rule here"
            ),
            CfgUnsupported::UnknownPrefixedOpcode { func, offset, sub } => write!(
                f,
                "func {func} @0x{offset:x}: 0xfc sub-opcode {sub} has no typing rule here"
            ),
            CfgUnsupported::TruncatedInstruction { func, offset } => {
                write!(f, "func {func} @0x{offset:x}: truncated instruction")
            }
            CfgUnsupported::UnsupportedBlockType { func, offset, byte } => write!(
                f,
                "func {func} @0x{offset:x}: blocktype 0x{byte:02x} is not modeled"
            ),
        }
    }
}

/// The three-way verdict. There is no two-way version on purpose: collapsing
/// [`CfgVerdict::Inconclusive`] into either of the others is how a family
/// launders debt.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CfgVerdict {
    /// Every invariant held on every function of the module.
    Holds(ModuleCfgReport),
    /// A structural defect was found (the FIRST one, fail-closed).
    Refuted(CfgViolation),
    /// The checker could not read the module and says nothing about it.
    Inconclusive(CfgUnsupported),
}

impl CfgVerdict {
    /// Did the invariant hold?
    pub fn holds(&self) -> bool {
        matches!(self, CfgVerdict::Holds(_))
    }
    /// Was a structural defect found?
    pub fn is_refuted(&self) -> bool {
        matches!(self, CfgVerdict::Refuted(_))
    }
    /// Did the checker decline to speak?
    pub fn is_inconclusive(&self) -> bool {
        matches!(self, CfgVerdict::Inconclusive(_))
    }
    /// The report, when the invariant held.
    pub fn report(&self) -> Option<&ModuleCfgReport> {
        match self {
            CfgVerdict::Holds(r) => Some(r),
            _ => None,
        }
    }
}

impl fmt::Display for CfgVerdict {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            CfgVerdict::Holds(r) => write!(
                f,
                "HOLDS: {} function(s), {} branch label reference(s) resolved, {} join(s) checked",
                r.functions.len(),
                r.totals().branch_labels_resolved,
                r.totals().joins_checked
            ),
            CfgVerdict::Refuted(v) => write!(f, "REFUTED: {v}"),
            CfgVerdict::Inconclusive(u) => write!(f, "INCONCLUSIVE: {u}"),
        }
    }
}

// ===========================================================================
// The independent byte reader (no `encode.rs`, no shared LEB code)
// ===========================================================================

/// A bounds-checked cursor over a byte slice with its own LEB128 readers.
///
/// Deliberately NOT `trust_cg_codegen::wasm::encode`'s writer inverted: the
/// point of this family is that the machine side is rebuilt from the bytes by
/// code that shares nothing with the code that wrote them.
struct Reader<'a> {
    bytes: &'a [u8],
    pos: usize,
}

impl<'a> Reader<'a> {
    fn new(bytes: &'a [u8]) -> Self {
        Reader { bytes, pos: 0 }
    }

    fn at_end(&self) -> bool {
        self.pos >= self.bytes.len()
    }

    fn byte(&mut self) -> Option<u8> {
        let b = *self.bytes.get(self.pos)?;
        self.pos += 1;
        Some(b)
    }

    fn take(&mut self, n: usize) -> Option<&'a [u8]> {
        let end = self.pos.checked_add(n)?;
        let slice = self.bytes.get(self.pos..end)?;
        self.pos = end;
        Some(slice)
    }

    /// ULEB128 into a `u64`, capped at 10 payload bytes. Over-long encodings
    /// are REJECTED rather than truncated (an over-long depth is exactly the
    /// kind of thing a sloppy reader would normalize away).
    fn uleb64(&mut self) -> Option<u64> {
        let mut result: u64 = 0;
        let mut shift = 0u32;
        loop {
            let b = self.byte()?;
            let payload = u64::from(b & 0x7f);
            if shift >= 64 {
                return None;
            }
            if shift == 63 && payload > 1 {
                return None;
            }
            result |= payload << shift;
            if b & 0x80 == 0 {
                return Some(result);
            }
            shift += 7;
        }
    }

    /// ULEB128 into a `u32`; rejects anything that does not fit.
    fn uleb32(&mut self) -> Option<u32> {
        u32::try_from(self.uleb64()?).ok()
    }

    /// SLEB128 into an `i64` (the `i32.const`/`i64.const` payload form).
    fn sleb64(&mut self) -> Option<i64> {
        let mut result: i64 = 0;
        let mut shift = 0u32;
        loop {
            let b = self.byte()?;
            if shift >= 64 {
                return None;
            }
            result |= i64::from(b & 0x7f).wrapping_shl(shift);
            shift += 7;
            if b & 0x80 == 0 {
                if shift < 64 && b & 0x40 != 0 {
                    result |= -1i64 << shift;
                }
                return Some(result);
            }
        }
    }

    /// A `name`: ULEB length then that many UTF-8 bytes.
    fn name(&mut self) -> Option<String> {
        let len = usize::try_from(self.uleb64()?).ok()?;
        let raw = self.take(len)?;
        String::from_utf8(raw.to_vec()).ok()
    }

    /// A `limits`: flag byte then min (and max when the flag says so).
    fn limits(&mut self) -> Option<()> {
        let flag = self.byte()?;
        let _min = self.uleb64()?;
        if flag & 0x01 != 0 {
            let _max = self.uleb64()?;
        }
        Some(())
    }
}

// ===========================================================================
// Module view — only what a control-flow type check actually needs
// ===========================================================================

/// A function signature as the checker needs it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FuncSig {
    /// Parameter types, in declaration order.
    pub params: Vec<ValKind>,
    /// Result types, in declaration order.
    pub results: Vec<ValKind>,
}

/// One code-section entry: the flattened local types (params NOT included) and
/// the body bytes, plus where the body sits in the ORIGINAL module buffer so a
/// mutation can patch it in place.
#[derive(Debug, Clone)]
pub struct CodeEntry {
    /// Declared locals, flattened from the `(count, valtype)` runs.
    pub locals: Vec<ValKind>,
    /// The body's instruction bytes, INCLUDING the terminating `end`.
    pub body: Vec<u8>,
    /// Absolute offset of `body[0]` within the module byte buffer.
    pub body_offset: usize,
}

/// The slice of a wasm module this family reads. Everything else (data, element,
/// memory, start) is skipped by length — module-level indexing and encoding is
/// family 4's obligation, not this one's, and pretending otherwise would be a
/// claim this file cannot back.
#[derive(Debug, Clone)]
pub struct WasmModuleView {
    /// The type section.
    pub types: Vec<FuncSig>,
    /// Type index per function, in the FULL index space (imports first).
    pub func_type_idx: Vec<u32>,
    /// How many of `func_type_idx`'s leading entries are imported functions.
    pub imported_funcs: usize,
    /// Global types in the full global index space (imports first).
    pub globals: Vec<ValKind>,
    /// One entry per DEFINED function, in definition order.
    pub code: Vec<CodeEntry>,
    /// Exported function names, keyed by function index.
    pub func_exports: Vec<(String, u32)>,
}

impl WasmModuleView {
    /// The signature of a function index in the full index space.
    pub fn sig_of_func(&self, index: u32) -> Option<&FuncSig> {
        let ty = *self.func_type_idx.get(usize::try_from(index).ok()?)?;
        self.types.get(usize::try_from(ty).ok()?)
    }

    /// The exported name of a function index, if it has one.
    pub fn export_name(&self, index: u32) -> Option<&str> {
        self.func_exports
            .iter()
            .find(|(_, i)| *i == index)
            .map(|(n, _)| n.as_str())
    }
}

fn valkinds(r: &mut Reader<'_>) -> Result<Vec<ValKind>, CfgUnsupported> {
    let n = r
        .uleb32()
        .ok_or(CfgUnsupported::Truncated { what: "vec len" })?;
    let mut out = Vec::new();
    for _ in 0..n {
        let b = r
            .byte()
            .ok_or(CfgUnsupported::Truncated { what: "valtype" })?;
        out.push(ValKind::from_byte(b).ok_or(CfgUnsupported::UnsupportedValType { byte: b })?);
    }
    Ok(out)
}

/// Decode the parts of a wasm module this family needs, from the raw bytes.
///
/// Fail-closed at every step: a bad magic, an unknown section id, an over-long
/// LEB, a non-number valtype and a truncated slice are all
/// [`CfgUnsupported`] — the checker declines rather than guesses.
pub fn decode_module(bytes: &[u8]) -> Result<WasmModuleView, CfgUnsupported> {
    let mut r = Reader::new(bytes);
    let magic = r.take(8).ok_or(CfgUnsupported::NotAWasmModule)?;
    if magic != [0x00, 0x61, 0x73, 0x6d, 0x01, 0x00, 0x00, 0x00] {
        return Err(CfgUnsupported::NotAWasmModule);
    }

    let mut view = WasmModuleView {
        types: Vec::new(),
        func_type_idx: Vec::new(),
        imported_funcs: 0,
        globals: Vec::new(),
        code: Vec::new(),
        func_exports: Vec::new(),
    };
    // Imported functions take the LOW indices, so they must all be recorded
    // before the defined ones; the encoder emits section 2 before section 3, and
    // a module that did not would be rejected by the section-order rule anyway.
    let mut defined_func_types: Vec<u32> = Vec::new();

    while !r.at_end() {
        let id = r
            .byte()
            .ok_or(CfgUnsupported::Truncated { what: "section id" })?;
        let size = usize::try_from(r.uleb64().ok_or(CfgUnsupported::Truncated {
            what: "section size",
        })?)
        .map_err(|_| CfgUnsupported::Malformed {
            what: "section size",
        })?;
        let body_offset = r.pos;
        let body = r.take(size).ok_or(CfgUnsupported::Truncated {
            what: "section body",
        })?;
        let mut s = Reader::new(body);
        match id {
            // Custom — carries no typing information.
            0 => {}
            // Type section.
            1 => {
                let n = s
                    .uleb32()
                    .ok_or(CfgUnsupported::Truncated { what: "type count" })?;
                for _ in 0..n {
                    let tag = s
                        .byte()
                        .ok_or(CfgUnsupported::Truncated { what: "functype" })?;
                    if tag != 0x60 {
                        return Err(CfgUnsupported::Malformed {
                            what: "functype tag",
                        });
                    }
                    let params = valkinds(&mut s)?;
                    let results = valkinds(&mut s)?;
                    view.types.push(FuncSig { params, results });
                }
            }
            // Import section.
            2 => {
                let n = s.uleb32().ok_or(CfgUnsupported::Truncated {
                    what: "import count",
                })?;
                for _ in 0..n {
                    let _module = s.name().ok_or(CfgUnsupported::Truncated {
                        what: "import module",
                    })?;
                    let _name = s.name().ok_or(CfgUnsupported::Truncated {
                        what: "import name",
                    })?;
                    let kind = s
                        .byte()
                        .ok_or(CfgUnsupported::Truncated { what: "importdesc" })?;
                    match kind {
                        0x00 => {
                            let ty = s.uleb32().ok_or(CfgUnsupported::Truncated {
                                what: "import typeidx",
                            })?;
                            view.func_type_idx.push(ty);
                            view.imported_funcs += 1;
                        }
                        0x01 => {
                            let _elem = s
                                .byte()
                                .ok_or(CfgUnsupported::Truncated { what: "elemtype" })?;
                            s.limits().ok_or(CfgUnsupported::Truncated {
                                what: "table limits",
                            })?;
                        }
                        0x02 => {
                            s.limits()
                                .ok_or(CfgUnsupported::Truncated { what: "mem limits" })?;
                        }
                        0x03 => {
                            let vt = s
                                .byte()
                                .ok_or(CfgUnsupported::Truncated { what: "globaltype" })?;
                            let kind = ValKind::from_byte(vt)
                                .ok_or(CfgUnsupported::UnsupportedValType { byte: vt })?;
                            let _mutable = s
                                .byte()
                                .ok_or(CfgUnsupported::Truncated { what: "global mut" })?;
                            view.globals.push(kind);
                        }
                        _ => {
                            return Err(CfgUnsupported::Malformed {
                                what: "importdesc kind",
                            });
                        }
                    }
                }
            }
            // Function section.
            3 => {
                let n = s
                    .uleb32()
                    .ok_or(CfgUnsupported::Truncated { what: "func count" })?;
                for _ in 0..n {
                    defined_func_types.push(s.uleb32().ok_or(CfgUnsupported::Truncated {
                        what: "func typeidx",
                    })?);
                }
            }
            // Table / memory / start / element / data / datacount: skipped by
            // length. They carry nothing this family's typing rules consult.
            4 | 5 | 8 | 9 | 11 | 12 => {}
            // Global section: the DEFINED globals' types, plus their constant
            // initializers (skipped by decoding to the terminating `end`).
            6 => {
                let n = s.uleb32().ok_or(CfgUnsupported::Truncated {
                    what: "global count",
                })?;
                for _ in 0..n {
                    let vt = s
                        .byte()
                        .ok_or(CfgUnsupported::Truncated { what: "globaltype" })?;
                    let kind = ValKind::from_byte(vt)
                        .ok_or(CfgUnsupported::UnsupportedValType { byte: vt })?;
                    let _mutable = s
                        .byte()
                        .ok_or(CfgUnsupported::Truncated { what: "global mut" })?;
                    skip_const_expr(&mut s)?;
                    view.globals.push(kind);
                }
            }
            // Export section: function exports only (names for the report).
            7 => {
                let n = s.uleb32().ok_or(CfgUnsupported::Truncated {
                    what: "export count",
                })?;
                for _ in 0..n {
                    let name = s.name().ok_or(CfgUnsupported::Truncated {
                        what: "export name",
                    })?;
                    let kind = s
                        .byte()
                        .ok_or(CfgUnsupported::Truncated { what: "exportdesc" })?;
                    let idx = s
                        .uleb32()
                        .ok_or(CfgUnsupported::Truncated { what: "export idx" })?;
                    if kind == 0x00 {
                        view.func_exports.push((name, idx));
                    }
                }
            }
            // Code section.
            10 => {
                let n = s
                    .uleb32()
                    .ok_or(CfgUnsupported::Truncated { what: "code count" })?;
                for _ in 0..n {
                    let entry_size =
                        usize::try_from(s.uleb64().ok_or(CfgUnsupported::Truncated {
                            what: "code entry size",
                        })?)
                        .map_err(|_| CfgUnsupported::Malformed {
                            what: "code entry size",
                        })?;
                    let entry_start = s.pos;
                    let entry = s
                        .take(entry_size)
                        .ok_or(CfgUnsupported::Truncated { what: "code entry" })?;
                    let mut e = Reader::new(entry);
                    let runs = e
                        .uleb32()
                        .ok_or(CfgUnsupported::Truncated { what: "local runs" })?;
                    let mut locals = Vec::new();
                    for _ in 0..runs {
                        let count = e.uleb32().ok_or(CfgUnsupported::Truncated {
                            what: "local run count",
                        })?;
                        let vt = e
                            .byte()
                            .ok_or(CfgUnsupported::Truncated { what: "local type" })?;
                        let kind = ValKind::from_byte(vt)
                            .ok_or(CfgUnsupported::UnsupportedValType { byte: vt })?;
                        for _ in 0..count {
                            locals.push(kind);
                        }
                    }
                    let body_start_in_entry = e.pos;
                    let body = entry
                        .get(body_start_in_entry..)
                        .ok_or(CfgUnsupported::Truncated { what: "code body" })?;
                    view.code.push(CodeEntry {
                        locals,
                        body: body.to_vec(),
                        body_offset: body_offset + entry_start + body_start_in_entry,
                    });
                }
            }
            other => return Err(CfgUnsupported::UnknownSection { id: other }),
        }
    }

    view.func_type_idx.extend(defined_func_types);
    Ok(view)
}

/// Skip a constant initializer expression by decoding instructions until the
/// `end` that closes it. Uses the same instruction decoder as the code section,
/// so an unrecognized constant form fails closed too.
fn skip_const_expr(r: &mut Reader<'_>) -> Result<(), CfgUnsupported> {
    let rest = r
        .bytes
        .get(r.pos..)
        .ok_or(CfgUnsupported::Truncated { what: "const expr" })?;
    let mut inner = Reader::new(rest);
    loop {
        let start = inner.pos;
        let op = inner
            .byte()
            .ok_or(CfgUnsupported::Truncated { what: "const expr" })?;
        if op == 0x0b {
            r.pos += inner.pos;
            return Ok(());
        }
        inner.pos = start;
        let inst = decode_one(&mut inner, 0).map_err(|e| match e {
            DecodeStop::Unsupported(u) => u,
        })?;
        let _ = inst;
    }
}

// ===========================================================================
// The independent instruction decoder
// ===========================================================================

/// A `blocktype`, restricted to the forms this checker models.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BlockType {
    /// `0x40` — no parameters, no results.
    Empty,
    /// A single result of this type.
    Value(ValKind),
}

impl BlockType {
    /// The scope's result types.
    pub fn results(self) -> Vec<ValKind> {
        match self {
            BlockType::Empty => Vec::new(),
            BlockType::Value(v) => vec![v],
        }
    }
}

/// The immediate operand(s) of a decoded instruction.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Imm {
    /// No immediate.
    None,
    /// `block`/`loop`/`if`.
    Block(BlockType),
    /// `br`/`br_if` label depth.
    Depth(u32),
    /// `br_table` label vector plus the default label.
    Table {
        /// The indexed labels.
        targets: Vec<u32>,
        /// The default label.
        default: u32,
    },
    /// A single index: local, global, or function.
    Index(u32),
    /// `call_indirect`.
    CallIndirect {
        /// The signature's type index.
        type_idx: u32,
        /// The table index (0 in the MVP).
        table_idx: u32,
    },
    /// A load/store `memarg`.
    MemArg {
        /// Alignment exponent (advisory).
        align: u32,
        /// Static byte offset.
        offset: u32,
    },
    /// The single memory index byte of `memory.size`/`memory.grow`.
    MemIdx(u8),
    /// `i32.const` / `i64.const` payload.
    Int(i64),
    /// `f32.const` / `f64.const` raw little-endian payload.
    Float(Vec<u8>),
}

/// One decoded instruction: where it starts, what it is, and its immediate.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DecodedInst {
    /// Byte offset of the opcode within the function body.
    pub offset: usize,
    /// The opcode byte.
    pub opcode: u8,
    /// The sub-index for a `0xfc`-prefixed opcode.
    pub sub: Option<u32>,
    /// The decoded immediate.
    pub imm: Imm,
    /// Total encoded size in bytes, opcode included.
    pub size: usize,
}

enum DecodeStop {
    Unsupported(CfgUnsupported),
}

fn trunc(func: u32, offset: usize) -> DecodeStop {
    DecodeStop::Unsupported(CfgUnsupported::TruncatedInstruction { func, offset })
}

fn decode_one(r: &mut Reader<'_>, func: u32) -> Result<DecodedInst, DecodeStop> {
    let offset = r.pos;
    let opcode = r.byte().ok_or_else(|| trunc(func, offset))?;
    let mut sub = None;
    let imm = match opcode {
        // ---- control, no immediate ----
        0x00 | 0x01 | 0x05 | 0x0b | 0x0f | 0x1a | 0x1b => Imm::None,
        // ---- block / loop / if : a blocktype ----
        0x02..=0x04 => {
            let b = r.byte().ok_or_else(|| trunc(func, offset))?;
            let bt = if b == 0x40 {
                BlockType::Empty
            } else if let Some(v) = ValKind::from_byte(b) {
                BlockType::Value(v)
            } else {
                return Err(DecodeStop::Unsupported(
                    CfgUnsupported::UnsupportedBlockType {
                        func,
                        offset,
                        byte: b,
                    },
                ));
            };
            Imm::Block(bt)
        }
        // ---- br / br_if ----
        0x0c | 0x0d => Imm::Depth(r.uleb32().ok_or_else(|| trunc(func, offset))?),
        // ---- br_table ----
        0x0e => {
            let n = r.uleb32().ok_or_else(|| trunc(func, offset))?;
            let mut targets = Vec::new();
            for _ in 0..n {
                targets.push(r.uleb32().ok_or_else(|| trunc(func, offset))?);
            }
            let default = r.uleb32().ok_or_else(|| trunc(func, offset))?;
            Imm::Table { targets, default }
        }
        // ---- call ----
        0x10 => Imm::Index(r.uleb32().ok_or_else(|| trunc(func, offset))?),
        // ---- call_indirect ----
        0x11 => {
            let type_idx = r.uleb32().ok_or_else(|| trunc(func, offset))?;
            let table_idx = r.uleb32().ok_or_else(|| trunc(func, offset))?;
            Imm::CallIndirect {
                type_idx,
                table_idx,
            }
        }
        // ---- locals / globals ----
        0x20..=0x24 => Imm::Index(r.uleb32().ok_or_else(|| trunc(func, offset))?),
        // ---- linear memory access: a memarg ----
        0x28..=0x3e => {
            let align = r.uleb32().ok_or_else(|| trunc(func, offset))?;
            let off = r.uleb32().ok_or_else(|| trunc(func, offset))?;
            Imm::MemArg { align, offset: off }
        }
        // ---- memory.size / memory.grow: a memory index byte ----
        0x3f | 0x40 => Imm::MemIdx(r.byte().ok_or_else(|| trunc(func, offset))?),
        // ---- constants ----
        0x41 | 0x42 => Imm::Int(r.sleb64().ok_or_else(|| trunc(func, offset))?),
        0x43 => Imm::Float(r.take(4).ok_or_else(|| trunc(func, offset))?.to_vec()),
        0x44 => Imm::Float(r.take(8).ok_or_else(|| trunc(func, offset))?.to_vec()),
        // ---- numeric, no immediate ----
        0x45..=0xc4 => Imm::None,
        // ---- the 0xfc prefix (saturating truncation, bulk memory) ----
        0xfc => {
            let s = r.uleb32().ok_or_else(|| trunc(func, offset))?;
            match s {
                0..=7 => {}
                // memory.copy: destination and source memory indices.
                10 => {
                    r.take(2).ok_or_else(|| trunc(func, offset))?;
                }
                // memory.fill: the memory index.
                11 => {
                    r.take(1).ok_or_else(|| trunc(func, offset))?;
                }
                _ => {
                    return Err(DecodeStop::Unsupported(
                        CfgUnsupported::UnknownPrefixedOpcode {
                            func,
                            offset,
                            sub: s,
                        },
                    ));
                }
            }
            sub = Some(s);
            Imm::None
        }
        other => {
            return Err(DecodeStop::Unsupported(CfgUnsupported::UnknownOpcode {
                func,
                offset,
                byte: other,
            }));
        }
    };
    Ok(DecodedInst {
        offset,
        opcode,
        sub,
        imm,
        size: r.pos - offset,
    })
}

/// Decode a function body into its instruction stream.
///
/// `func` only names the function in any diagnostic. A byte with no decoding
/// rule stops the decode as [`CfgUnsupported`] — the body is NOT partially
/// credited.
pub fn decode_body(body: &[u8], func: u32) -> Result<Vec<DecodedInst>, CfgUnsupported> {
    let mut r = Reader::new(body);
    let mut out = Vec::new();
    while !r.at_end() {
        match decode_one(&mut r, func) {
            Ok(inst) => out.push(inst),
            Err(DecodeStop::Unsupported(u)) => return Err(u),
        }
    }
    Ok(out)
}

// ===========================================================================
// Pass 1 — bracket matching (the label CONTINUATION table)
// ===========================================================================

/// Where a `br` to a label transfers control, as a byte offset in the body.
///
/// DERIVED, NOT CHECKED. This offset is a theorem of the bracket matching in
/// [`match_scopes`]; an "obligation" asserting it would compare this module to
/// itself. It is reported so a reader can audit the resolved target of every
/// branch, and it is excluded from the invariant denominator.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Continuation {
    /// Byte offset of the instruction control resumes at.
    pub offset: usize,
    /// Does control go BACKWARD (a `loop` label) rather than forward?
    pub backward: bool,
}

/// Match every structured-control opener to its `end`, and check the bracket
/// structure itself.
///
/// Returns, for each instruction index that OPENS a scope, the byte offset just
/// past its matching `end` — plus the index of the `end` that closes the
/// function label.
fn match_scopes(
    insts: &[DecodedInst],
    func: u32,
    body_len: usize,
) -> Result<Vec<Option<usize>>, CfgViolation> {
    // `None` on the stack is the implicit function label.
    let mut stack: Vec<Option<usize>> = vec![None];
    let mut continuation_of: Vec<Option<usize>> = vec![None; insts.len()];
    let mut function_end_seen = false;

    for (i, inst) in insts.iter().enumerate() {
        if function_end_seen {
            return Err(CfgViolation::TrailingCodeAfterFunctionEnd {
                func,
                offset: inst.offset,
            });
        }
        match inst.opcode {
            0x02..=0x04 => stack.push(Some(i)),
            0x05 => {
                let top = stack.last().copied().flatten();
                let is_if = top
                    .and_then(|j| insts.get(j))
                    .map(|o| o.opcode == 0x04)
                    .unwrap_or(false);
                if !is_if {
                    return Err(CfgViolation::ElseWithoutIf {
                        func,
                        offset: inst.offset,
                    });
                }
            }
            0x0b => match stack.pop() {
                Some(Some(j)) => {
                    if let Some(slot) = continuation_of.get_mut(j) {
                        *slot = Some(inst.offset + 1);
                    }
                }
                Some(None) => {
                    function_end_seen = true;
                    if !stack.is_empty() {
                        return Err(CfgViolation::EndWithoutScope {
                            func,
                            offset: inst.offset,
                        });
                    }
                }
                None => {
                    return Err(CfgViolation::EndWithoutScope {
                        func,
                        offset: inst.offset,
                    });
                }
            },
            _ => {}
        }
    }

    if !function_end_seen || !stack.is_empty() {
        return Err(CfgViolation::UnclosedScopes {
            func,
            open: stack.len(),
        });
    }
    let _ = body_len;
    Ok(continuation_of)
}

// ===========================================================================
// Pass 2 — the spec validation algorithm (§7.3.2), over the decoded stream
// ===========================================================================

#[derive(Debug, Clone)]
struct Frame {
    kind: ScopeKind,
    /// The types a `br` to this label must supply.
    label_types: Vec<ValKind>,
    /// The types the scope's `end` must leave.
    end_types: Vec<ValKind>,
    /// Value stack height when the scope was entered.
    height: usize,
    /// Has the rest of this scope been made unreachable?
    unreachable: bool,
    /// The label's continuation (derived; see [`Continuation`]).
    continuation: Continuation,
    /// Byte offset of the opener, for diagnostics.
    opener_offset: usize,
    /// Did this `if` see its `else`?
    saw_else: bool,
}

/// One resolved label reference: which label a branch's depth named, what that
/// label demands, and where it goes.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BranchResolution {
    /// Byte offset of the branch opcode.
    pub offset: usize,
    /// `br` (0x0c), `br_if` (0x0d) or `br_table` (0x0e).
    pub opcode: u8,
    /// For `br_table`, which entry this resolution is for (`None` = default).
    pub table_entry: Option<usize>,
    /// The decoded depth.
    pub depth: u32,
    /// The kind of the label the depth named.
    pub label_kind: ScopeKind,
    /// How many values the label takes.
    pub label_arity: usize,
    /// Where control goes (derived, see [`Continuation`]).
    pub continuation: Continuation,
}

/// What the invariant established for one function.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FunctionCfgReport {
    /// Index in the module's function index space.
    pub func_index: u32,
    /// Exported name, when the module exports this function.
    pub name: Option<String>,
    /// Instructions decoded.
    pub instructions: usize,
    /// `block` scopes opened.
    pub blocks: usize,
    /// `loop` scopes opened.
    pub loops: usize,
    /// `if` scopes opened.
    pub ifs: usize,
    /// `end`/`else` joins whose height and types were checked.
    pub joins_checked: usize,
    /// Deepest label nesting reached, the function label included.
    pub max_label_depth: usize,
    /// Every resolved label reference, in emission order.
    pub branches: Vec<BranchResolution>,
}

/// What the invariant established for a whole module.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ModuleCfgReport {
    /// One entry per DEFINED function, in definition order.
    pub functions: Vec<FunctionCfgReport>,
}

/// The real numbers a report carries. Every field is a COUNT OF CHECKS THAT
/// RAN, never a count of properties assumed.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct CfgTotals {
    /// Functions structurally checked.
    pub functions: usize,
    /// Instructions decoded and given a typing rule.
    pub instructions: usize,
    /// Label references resolved and checked (a `br_table` contributes one per
    /// entry plus one for its default).
    pub branch_labels_resolved: usize,
    /// `end`/`else` joins whose stack height and types were checked.
    pub joins_checked: usize,
    /// Structured-control scopes opened, matched, and closed.
    pub scopes_matched: usize,
}

impl ModuleCfgReport {
    /// Sum the per-function counts.
    pub fn totals(&self) -> CfgTotals {
        let mut t = CfgTotals {
            functions: self.functions.len(),
            ..CfgTotals::default()
        };
        for f in &self.functions {
            t.instructions += f.instructions;
            t.branch_labels_resolved += f.branches.len();
            t.joins_checked += f.joins_checked;
            t.scopes_matched += f.blocks + f.loops + f.ifs;
        }
        t
    }
}

/// Either a refutation or a decline — the two non-green outcomes, kept apart.
#[derive(Debug, Clone, PartialEq, Eq)]
enum Failure {
    Violated(CfgViolation),
    Unsupported(CfgUnsupported),
}

impl From<CfgViolation> for Failure {
    fn from(v: CfgViolation) -> Self {
        Failure::Violated(v)
    }
}

impl From<CfgUnsupported> for Failure {
    fn from(u: CfgUnsupported) -> Self {
        Failure::Unsupported(u)
    }
}

struct Validator<'a> {
    view: &'a WasmModuleView,
    func: u32,
    locals: Vec<ValKind>,
    results: Vec<ValKind>,
    vals: Vec<ValKind>,
    ctrls: Vec<Frame>,
}

impl Validator<'_> {
    fn frame_height(&self) -> usize {
        self.ctrls.last().map(|f| f.height).unwrap_or(0)
    }

    fn frame_unreachable(&self) -> bool {
        self.ctrls.last().map(|f| f.unreachable).unwrap_or(false)
    }

    /// Pop one value. `Ok(None)` is the SPEC's polymorphic "unknown": inside
    /// unreachable code the stack is bottomless and any type is available.
    fn pop(&mut self, offset: usize) -> Result<Option<ValKind>, CfgViolation> {
        if self.vals.len() == self.frame_height() {
            if self.frame_unreachable() {
                return Ok(None);
            }
            return Err(CfgViolation::StackUnderflow {
                func: self.func,
                offset,
            });
        }
        Ok(self.vals.pop())
    }

    fn pop_expect(&mut self, want: ValKind, offset: usize) -> Result<(), CfgViolation> {
        match self.pop(offset)? {
            None => Ok(()),
            Some(got) if got == want => Ok(()),
            Some(got) => Err(CfgViolation::TypeMismatch {
                func: self.func,
                offset,
                expected: want,
                found: got,
            }),
        }
    }

    fn pop_expects(&mut self, want: &[ValKind], offset: usize) -> Result<(), CfgViolation> {
        for t in want.iter().rev() {
            self.pop_expect(*t, offset)?;
        }
        Ok(())
    }

    fn push_all(&mut self, types: &[ValKind]) {
        self.vals.extend_from_slice(types);
    }

    fn mark_unreachable(&mut self) {
        let height = self.frame_height();
        self.vals.truncate(height);
        if let Some(f) = self.ctrls.last_mut() {
            f.unreachable = true;
        }
    }

    fn push_ctrl(
        &mut self,
        kind: ScopeKind,
        label_types: Vec<ValKind>,
        end_types: Vec<ValKind>,
        continuation: Continuation,
        opener_offset: usize,
    ) {
        self.ctrls.push(Frame {
            kind,
            label_types,
            end_types,
            height: self.vals.len(),
            unreachable: false,
            continuation,
            opener_offset,
            saw_else: false,
        });
    }

    /// Validate the close of the innermost scope and pop it, WITHOUT pushing its
    /// results (the caller decides: `end` pushes them, `else` does not).
    fn pop_ctrl(&mut self, offset: usize) -> Result<Frame, CfgViolation> {
        let frame = self
            .ctrls
            .last()
            .cloned()
            .ok_or(CfgViolation::EndWithoutScope {
                func: self.func,
                offset,
            })?;
        self.pop_expects(&frame.end_types, offset)?;
        if self.vals.len() != frame.height {
            return Err(CfgViolation::JoinHeightMismatch {
                func: self.func,
                offset,
                scope: frame.kind,
                expected: frame.height,
                found: self.vals.len(),
            });
        }
        self.ctrls.pop();
        Ok(frame)
    }

    /// Resolve a label depth to its frame, checking B1 (liveness).
    fn label(&self, depth: u32, offset: usize) -> Result<&Frame, CfgViolation> {
        let live = self.ctrls.len();
        let d = usize::try_from(depth).unwrap_or(usize::MAX);
        if d >= live {
            return Err(CfgViolation::BranchDepthOutOfRange {
                func: self.func,
                offset,
                depth,
                live_labels: live,
            });
        }
        self.ctrls
            .get(live - 1 - d)
            .ok_or(CfgViolation::BranchDepthOutOfRange {
                func: self.func,
                offset,
                depth,
                live_labels: live,
            })
    }

    fn local(&self, index: u32, offset: usize) -> Result<ValKind, CfgViolation> {
        usize::try_from(index)
            .ok()
            .and_then(|i| self.locals.get(i).copied())
            .ok_or(CfgViolation::IndexOutOfRange {
                func: self.func,
                offset,
                space: "local",
                index,
                count: self.locals.len(),
            })
    }

    fn global(&self, index: u32, offset: usize) -> Result<ValKind, CfgViolation> {
        usize::try_from(index)
            .ok()
            .and_then(|i| self.view.globals.get(i).copied())
            .ok_or(CfgViolation::IndexOutOfRange {
                func: self.func,
                offset,
                space: "global",
                index,
                count: self.view.globals.len(),
            })
    }
}

/// Number-type rules for the non-memory, non-control opcodes: `(pops, pushes)`,
/// transcribed from the spec's numeric-instruction typing rules.
fn numeric_rule(op: u8) -> Option<(&'static [ValKind], &'static [ValKind])> {
    use ValKind::{F32, F64, I32, I64};
    const I: &[ValKind] = &[I32];
    const II: &[ValKind] = &[I32, I32];
    const L: &[ValKind] = &[I64];
    const LL: &[ValKind] = &[I64, I64];
    const F: &[ValKind] = &[F32];
    const FF: &[ValKind] = &[F32, F32];
    const D: &[ValKind] = &[F64];
    const DD: &[ValKind] = &[F64, F64];
    Some(match op {
        0x45 => (I, I),         // i32.eqz
        0x46..=0x4f => (II, I), // i32 comparisons
        0x50 => (L, I),         // i64.eqz
        0x51..=0x5a => (LL, I), // i64 comparisons
        0x5b..=0x60 => (FF, I), // f32 comparisons
        0x61..=0x66 => (DD, I), // f64 comparisons
        0x67..=0x69 => (I, I),  // i32 clz/ctz/popcnt
        0x6a..=0x78 => (II, I), // i32 binary arith/bitwise/shift/rotate
        0x79..=0x7b => (L, L),  // i64 clz/ctz/popcnt
        0x7c..=0x8a => (LL, L), // i64 binary
        0x8b..=0x91 => (F, F),  // f32 unary
        0x92..=0x98 => (FF, F), // f32 binary
        0x99..=0x9f => (D, D),  // f64 unary
        0xa0..=0xa6 => (DD, D), // f64 binary
        0xa7 => (L, I),         // i32.wrap_i64
        0xa8 | 0xa9 => (F, I),  // i32.trunc_f32_s/u
        0xaa | 0xab => (D, I),  // i32.trunc_f64_s/u
        0xac | 0xad => (I, L),  // i64.extend_i32_s/u
        0xae | 0xaf => (F, L),  // i64.trunc_f32_s/u
        0xb0 | 0xb1 => (D, L),  // i64.trunc_f64_s/u
        0xb2 | 0xb3 => (I, F),  // f32.convert_i32_s/u
        0xb4 | 0xb5 => (L, F),  // f32.convert_i64_s/u
        0xb6 => (D, F),         // f32.demote_f64
        0xb7 | 0xb8 => (I, D),  // f64.convert_i32_s/u
        0xb9 | 0xba => (L, D),  // f64.convert_i64_s/u
        0xbb => (F, D),         // f64.promote_f32
        0xbc => (F, I),         // i32.reinterpret_f32
        0xbd => (D, L),         // i64.reinterpret_f64
        0xbe => (I, F),         // f32.reinterpret_i32
        0xbf => (L, D),         // f64.reinterpret_i64
        0xc0 | 0xc1 => (I, I),  // i32.extend8_s / extend16_s
        0xc2..=0xc4 => (L, L),  // i64.extend8_s / 16_s / 32_s
        _ => return None,
    })
}

/// Linear-memory rules: `(is_load, value type)`, spec §5.4.4's table.
fn memory_rule(op: u8) -> Option<(bool, ValKind)> {
    use ValKind::{F32, F64, I32, I64};
    Some(match op {
        0x28 => (true, I32),
        0x29 => (true, I64),
        0x2a => (true, F32),
        0x2b => (true, F64),
        0x2c..=0x2f => (true, I32),
        0x30..=0x35 => (true, I64),
        0x36 => (false, I32),
        0x37 => (false, I64),
        0x38 => (false, F32),
        0x39 => (false, F64),
        0x3a | 0x3b => (false, I32),
        0x3c..=0x3e => (false, I64),
        _ => return None,
    })
}

/// Saturating float->int truncation rules for the `0xfc` sub-opcodes 0..=7.
fn trunc_sat_rule(sub: u32) -> Option<(ValKind, ValKind)> {
    use ValKind::{F32, F64, I32, I64};
    Some(match sub {
        0 | 1 => (F32, I32),
        2 | 3 => (F64, I32),
        4 | 5 => (F32, I64),
        6 | 7 => (F64, I64),
        _ => return None,
    })
}

fn check_function(
    view: &WasmModuleView,
    func_index: u32,
    entry: &CodeEntry,
) -> Result<FunctionCfgReport, Failure> {
    let sig = view
        .sig_of_func(func_index)
        .ok_or(CfgUnsupported::Malformed {
            what: "function signature",
        })?
        .clone();
    let insts = decode_body(&entry.body, func_index)?;
    let continuation_of = match_scopes(&insts, func_index, entry.body.len())?;

    let mut locals = sig.params.clone();
    locals.extend(entry.locals.iter().copied());

    let mut v = Validator {
        view,
        func: func_index,
        locals,
        results: sig.results.clone(),
        vals: Vec::new(),
        ctrls: Vec::new(),
    };
    // The implicit function label: a `br` to it RETURNS, so it takes the
    // function's results and its continuation is the end of the body.
    v.push_ctrl(
        ScopeKind::Func,
        sig.results.clone(),
        sig.results.clone(),
        Continuation {
            offset: entry.body.len(),
            backward: false,
        },
        0,
    );

    let mut report = FunctionCfgReport {
        func_index,
        name: view.export_name(func_index).map(str::to_string),
        instructions: insts.len(),
        blocks: 0,
        loops: 0,
        ifs: 0,
        joins_checked: 0,
        max_label_depth: 1,
        branches: Vec::new(),
    };

    for (i, inst) in insts.iter().enumerate() {
        let off = inst.offset;
        match inst.opcode {
            // ---------------- control ----------------
            0x00 => v.mark_unreachable(),
            0x01 => {}
            0x02..=0x04 => {
                let bt = match inst.imm {
                    Imm::Block(bt) => bt,
                    _ => {
                        return Err(Failure::Unsupported(CfgUnsupported::Malformed {
                            what: "blocktype immediate",
                        }));
                    }
                };
                if inst.opcode == 0x04 {
                    v.pop_expect(ValKind::I32, off)?;
                }
                let results = bt.results();
                let cont_offset = continuation_of.get(i).copied().flatten().unwrap_or(off);
                let (kind, label_types, continuation) = match inst.opcode {
                    0x02 => (
                        ScopeKind::Block,
                        results.clone(),
                        Continuation {
                            offset: cont_offset,
                            backward: false,
                        },
                    ),
                    0x03 => (
                        ScopeKind::Loop,
                        // A `loop` label takes the block's PARAMETERS, which is
                        // the empty vector for every blocktype modeled here.
                        Vec::new(),
                        Continuation {
                            offset: off,
                            backward: true,
                        },
                    ),
                    _ => (
                        ScopeKind::If,
                        results.clone(),
                        Continuation {
                            offset: cont_offset,
                            backward: false,
                        },
                    ),
                };
                match kind {
                    ScopeKind::Block => report.blocks += 1,
                    ScopeKind::Loop => report.loops += 1,
                    _ => report.ifs += 1,
                }
                v.push_ctrl(kind, label_types, results, continuation, off);
                report.max_label_depth = report.max_label_depth.max(v.ctrls.len());
            }
            0x05 => {
                let frame = v.pop_ctrl(off)?;
                if frame.kind != ScopeKind::If {
                    return Err(Failure::Violated(CfgViolation::ElseWithoutIf {
                        func: func_index,
                        offset: off,
                    }));
                }
                report.joins_checked += 1;
                v.push_ctrl(
                    ScopeKind::Else,
                    frame.label_types.clone(),
                    frame.end_types.clone(),
                    frame.continuation,
                    frame.opener_offset,
                );
                if let Some(f) = v.ctrls.last_mut() {
                    f.saw_else = true;
                }
            }
            0x0b => {
                let frame = v.pop_ctrl(off)?;
                if frame.kind == ScopeKind::If && !frame.end_types.is_empty() && !frame.saw_else {
                    return Err(Failure::Violated(CfgViolation::IfWithResultsHasNoElse {
                        func: func_index,
                        offset: frame.opener_offset,
                    }));
                }
                report.joins_checked += 1;
                let results = frame.end_types.clone();
                if v.ctrls.is_empty() {
                    // That was the function label; the body is over.
                    break;
                }
                v.push_all(&results);
            }
            0x0c | 0x0d => {
                let depth = match inst.imm {
                    Imm::Depth(d) => d,
                    _ => {
                        return Err(Failure::Unsupported(CfgUnsupported::Malformed {
                            what: "branch depth immediate",
                        }));
                    }
                };
                let (label_types, kind, continuation) = {
                    let frame = v.label(depth, off)?;
                    (frame.label_types.clone(), frame.kind, frame.continuation)
                };
                report.branches.push(BranchResolution {
                    offset: off,
                    opcode: inst.opcode,
                    table_entry: None,
                    depth,
                    label_kind: kind,
                    label_arity: label_types.len(),
                    continuation,
                });
                if inst.opcode == 0x0d {
                    v.pop_expect(ValKind::I32, off)?;
                    v.pop_expects(&label_types, off)?;
                    v.push_all(&label_types);
                } else {
                    v.pop_expects(&label_types, off)?;
                    v.mark_unreachable();
                }
            }
            0x0e => {
                let (targets, default) = match &inst.imm {
                    Imm::Table { targets, default } => (targets.clone(), *default),
                    _ => {
                        return Err(Failure::Unsupported(CfgUnsupported::Malformed {
                            what: "br_table immediate",
                        }));
                    }
                };
                v.pop_expect(ValKind::I32, off)?;
                let (default_types, default_kind, default_cont) = {
                    let frame = v.label(default, off)?;
                    (frame.label_types.clone(), frame.kind, frame.continuation)
                };
                for (n, t) in targets.iter().enumerate() {
                    let (types, kind, cont) = {
                        let frame = v.label(*t, off)?;
                        (frame.label_types.clone(), frame.kind, frame.continuation)
                    };
                    if types.len() != default_types.len() {
                        return Err(Failure::Violated(CfgViolation::BrTableArityMismatch {
                            func: func_index,
                            offset: off,
                            entry: Some(n),
                            default_arity: default_types.len(),
                            entry_arity: types.len(),
                        }));
                    }
                    for (a, b) in types.iter().zip(default_types.iter()) {
                        if a != b {
                            return Err(Failure::Violated(CfgViolation::TypeMismatch {
                                func: func_index,
                                offset: off,
                                expected: *b,
                                found: *a,
                            }));
                        }
                    }
                    report.branches.push(BranchResolution {
                        offset: off,
                        opcode: inst.opcode,
                        table_entry: Some(n),
                        depth: *t,
                        label_kind: kind,
                        label_arity: types.len(),
                        continuation: cont,
                    });
                }
                report.branches.push(BranchResolution {
                    offset: off,
                    opcode: inst.opcode,
                    table_entry: None,
                    depth: default,
                    label_kind: default_kind,
                    label_arity: default_types.len(),
                    continuation: default_cont,
                });
                v.pop_expects(&default_types, off)?;
                v.mark_unreachable();
            }
            0x0f => {
                let results = v.results.clone();
                v.pop_expects(&results, off)?;
                v.mark_unreachable();
            }
            0x10 => {
                let idx = match inst.imm {
                    Imm::Index(i) => i,
                    _ => {
                        return Err(Failure::Unsupported(CfgUnsupported::Malformed {
                            what: "call immediate",
                        }));
                    }
                };
                let sig = view
                    .sig_of_func(idx)
                    .ok_or(CfgViolation::IndexOutOfRange {
                        func: func_index,
                        offset: off,
                        space: "function",
                        index: idx,
                        count: view.func_type_idx.len(),
                    })?
                    .clone();
                v.pop_expects(&sig.params, off)?;
                v.push_all(&sig.results);
            }
            0x11 => {
                let type_idx = match inst.imm {
                    Imm::CallIndirect { type_idx, .. } => type_idx,
                    _ => {
                        return Err(Failure::Unsupported(CfgUnsupported::Malformed {
                            what: "call_indirect immediate",
                        }));
                    }
                };
                let sig = usize::try_from(type_idx)
                    .ok()
                    .and_then(|i| view.types.get(i))
                    .cloned()
                    .ok_or(CfgViolation::IndexOutOfRange {
                        func: func_index,
                        offset: off,
                        space: "type",
                        index: type_idx,
                        count: view.types.len(),
                    })?;
                v.pop_expect(ValKind::I32, off)?;
                v.pop_expects(&sig.params, off)?;
                v.push_all(&sig.results);
            }
            0x1a => {
                v.pop(off)?;
            }
            0x20..=0x22 => {
                let idx = match inst.imm {
                    Imm::Index(i) => i,
                    _ => {
                        return Err(Failure::Unsupported(CfgUnsupported::Malformed {
                            what: "local immediate",
                        }));
                    }
                };
                let t = v.local(idx, off)?;
                match inst.opcode {
                    0x20 => v.push_all(&[t]),
                    0x21 => v.pop_expect(t, off)?,
                    _ => {
                        v.pop_expect(t, off)?;
                        v.push_all(&[t]);
                    }
                }
            }
            0x23 | 0x24 => {
                let idx = match inst.imm {
                    Imm::Index(i) => i,
                    _ => {
                        return Err(Failure::Unsupported(CfgUnsupported::Malformed {
                            what: "global immediate",
                        }));
                    }
                };
                let t = v.global(idx, off)?;
                if inst.opcode == 0x23 {
                    v.push_all(&[t]);
                } else {
                    v.pop_expect(t, off)?;
                }
            }
            0x28..=0x3e => {
                let (is_load, t) =
                    memory_rule(inst.opcode).ok_or(CfgUnsupported::UnknownOpcode {
                        func: func_index,
                        offset: off,
                        byte: inst.opcode,
                    })?;
                if is_load {
                    v.pop_expect(ValKind::I32, off)?;
                    v.push_all(&[t]);
                } else {
                    v.pop_expect(t, off)?;
                    v.pop_expect(ValKind::I32, off)?;
                }
            }
            0x3f => v.push_all(&[ValKind::I32]),
            0x40 => {
                v.pop_expect(ValKind::I32, off)?;
                v.push_all(&[ValKind::I32]);
            }
            0x41 => v.push_all(&[ValKind::I32]),
            0x42 => v.push_all(&[ValKind::I64]),
            0x43 => v.push_all(&[ValKind::F32]),
            0x44 => v.push_all(&[ValKind::F64]),
            0xfc => {
                let sub = inst.sub.unwrap_or(u32::MAX);
                if matches!(sub, 10 | 11) {
                    // memory.copy [dst, src, n] / memory.fill [dst, byte, n]:
                    // three i32 operands, no result.
                    v.pop_expects(&[ValKind::I32, ValKind::I32, ValKind::I32], off)?;
                    continue;
                }
                let (from, to) =
                    trunc_sat_rule(sub).ok_or(CfgUnsupported::UnknownPrefixedOpcode {
                        func: func_index,
                        offset: off,
                        sub,
                    })?;
                v.pop_expect(from, off)?;
                v.push_all(&[to]);
            }
            // select: [t t i32] -> [t], both operands one numeric type.
            0x1b => {
                v.pop_expect(ValKind::I32, off)?;
                let b = v.pop(off)?;
                let a = v.pop(off)?;
                match (a, b) {
                    (Some(a), Some(b)) if a != b => {
                        return Err(Failure::Violated(CfgViolation::TypeMismatch {
                            func: func_index,
                            offset: off,
                            expected: a,
                            found: b,
                        }));
                    }
                    (Some(t), _) | (None, Some(t)) => v.push_all(&[t]),
                    // Both operands came from unreachable code: the result is
                    // polymorphic too; model it as nothing on the stack.
                    (None, None) => {}
                }
            }
            other => {
                let (pops, pushes) = numeric_rule(other).ok_or(CfgUnsupported::UnknownOpcode {
                    func: func_index,
                    offset: off,
                    byte: other,
                })?;
                v.pop_expects(pops, off)?;
                v.push_all(pushes);
            }
        }
    }

    if !v.ctrls.is_empty() {
        return Err(Failure::Violated(CfgViolation::UnclosedScopes {
            func: func_index,
            open: v.ctrls.len(),
        }));
    }
    Ok(report)
}

// ===========================================================================
// The per-compile entry points
// ===========================================================================

/// THE PER-COMPILE ARTIFACT. Decode a `.wasm` module and check the structural
/// invariant over every defined function.
///
/// Called by `trust_cg_codegen::wasm::lower::compile_module_with_evidence` and
/// `..._with_evidence_and_policy` on the bytes they emit, so an evidence-carrying
/// wasm compile really does produce this verdict. See the module header for how
/// each of the three values is filed there.
///
/// Three-valued on purpose ([`CfgVerdict`]): `Holds` with the evidence counts,
/// `Refuted` with the first structural defect, or `Inconclusive` when the
/// decoder met something it has no rule for. A caller that collapses the third
/// case into either of the others has broken the honesty property this family
/// exists to keep.
///
/// This is a NECESSARY CONDITION on structuring, not a bisimulation. See
/// [`WASM_CFG_DEFERRALS`]. A compile whose module satisfies it is not a verified
/// compile, and the caller above is careful to say so.
pub fn check_module_structure(module_bytes: &[u8]) -> CfgVerdict {
    let view = match decode_module(module_bytes) {
        Ok(v) => v,
        Err(u) => return CfgVerdict::Inconclusive(u),
    };
    let mut functions = Vec::new();
    for (i, entry) in view.code.iter().enumerate() {
        let func_index = match u32::try_from(view.imported_funcs + i) {
            Ok(n) => n,
            Err(_) => {
                return CfgVerdict::Inconclusive(CfgUnsupported::Malformed {
                    what: "function index space",
                });
            }
        };
        match check_function(&view, func_index, entry) {
            Ok(r) => functions.push(r),
            Err(Failure::Violated(v)) => return CfgVerdict::Refuted(v),
            Err(Failure::Unsupported(u)) => return CfgVerdict::Inconclusive(u),
        }
    }
    CfgVerdict::Holds(ModuleCfgReport { functions })
}

/// Fail-closed boolean form of [`check_module_structure`], for a gate row:
/// `true` ONLY for `Holds`. An inconclusive module earns nothing.
pub fn structural_invariant_holds(module_bytes: &[u8]) -> bool {
    check_module_structure(module_bytes).holds()
}

/// Decode every function body of a module to `(absolute body offset,
/// instructions)`, for callers that want to inspect or MUTATE the emitted
/// bytes.
pub fn decode_function_bodies(
    module_bytes: &[u8],
) -> Result<Vec<(usize, Vec<DecodedInst>)>, CfgUnsupported> {
    let view = decode_module(module_bytes)?;
    let mut out = Vec::new();
    for (i, entry) in view.code.iter().enumerate() {
        let func = u32::try_from(view.imported_funcs + i).unwrap_or(u32::MAX);
        out.push((entry.body_offset, decode_body(&entry.body, func)?));
    }
    Ok(out)
}

// ===========================================================================
// The invariant inventory — with a `does_not_cover` field on every row
// ===========================================================================

/// One structural invariant this family checks, what it REFUTES, and what it
/// leaves open. The last field is not decoration: a row without an honest
/// `does_not_cover` is how a necessary condition gets read as a proof.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CfgInvariantRow {
    /// Short identifier used in reports.
    pub id: &'static str,
    /// What the checker establishes.
    pub statement: &'static str,
    /// A concrete wrong lowering this row refutes.
    pub refutes: &'static str,
    /// What this row does NOT say.
    pub does_not_cover: &'static str,
}

/// The checked invariants. Pinned by the family's tests: adding a row without
/// landing its check, or dropping one, fails the build.
pub const WASM_CFG_INVARIANTS: &[CfgInvariantRow] = &[
    CfgInvariantRow {
        id: "B1 label liveness",
        statement: "every br / br_if / br_table label depth names a LIVE label — a scope that is \
                    open at that program point, resolved against the spec's control stack rebuilt \
                    from the emitted bytes",
        refutes: "the P3 merge-child ORDERING defect: nesting merge children earliest-RPO-outermost \
                  emits an earlier child's subtree OUTSIDE a later sibling's block, so its forward \
                  branch names a label that is no longer open",
        does_not_cover: "WHICH live label the branch should have named. A depth that resolves to a \
                         live label of the same arity is accepted even when it is the wrong one — \
                         see the `branch-target intent binding` deferral and the KnownBlindSpot \
                         mutants",
    },
    CfgInvariantRow {
        id: "B2 branch operand discipline",
        statement: "at every branch the value stack carries the label's argument types, in order; \
                    br_if restores them and br / br_table make the rest of the block unreachable, \
                    per the spec's polymorphic-stack rule",
        refutes: "a branch emitted where the join expects a value the block never produced, and a \
                  br_if lowered as a br (the stack it leaves behind stops matching the fallthrough)",
        does_not_cover: "the VALUES themselves. Types and counts are checked; nothing here says the \
                         value handed to a join is the one the trust-ir edge carried (block-param / \
                         phi resolution is a named deferral)",
    },
    CfgInvariantRow {
        id: "B3 br_table uniformity",
        statement: "every entry of a br_table, its default included, resolves to a live label \
                    taking the SAME types — the spec's uniform-arity requirement on the whole table",
        refutes: "a table nest built one label too shallow or too deep, where one arm's label ends \
                  up at a different arity than the default",
        does_not_cover: "the index-to-arm SELECTION function (which index picks which arm, and that \
                         holes take the default). That is the value-domain family's own br_table \
                         deferral and stays RED there",
    },
    CfgInvariantRow {
        id: "J1 join height",
        statement: "at every join — each `end` and each `else` — the value stack height equals the \
                    scope's entry height plus its result count",
        refutes: "a dropped `end` (the scopes no longer close where the code says they do), and any \
                  path into a join that leaves an extra operand behind",
        does_not_cover: "anything about unreachable code beyond the spec's polymorphism: after \
                         `unreachable` the stack is bottomless by DESIGN, so a defect confined to \
                         provably-unreachable code is invisible here",
    },
    CfgInvariantRow {
        id: "J2 join and operand types",
        statement: "every operand popped by every instruction, at a join or anywhere else, has the \
                    type the spec's rule demands — i32/i64/f32/f64 tracked through the full emitted \
                    opcode surface",
        refutes: "an i32-for-i64 opcode slip (i32.add emitted where the operands are i64), a \
                  local.set lowered as a local.get, and a narrow carrier fed to an f32 op",
        does_not_cover: "the int/FP distinction where it is not a TYPE distinction, and every value \
                         property — the value domain is family 3's obligation set, not this one's",
    },
    CfgInvariantRow {
        id: "S1 bracket structure",
        statement: "the block / loop / if / else / end bracket structure is well formed: every \
                    `else` closes an `if`, every `end` closes an open scope, the body's last \
                    instruction closes the function label, and nothing follows it",
        refutes: "a dropped or duplicated `end`, an `else` outside an `if`, and code emitted past \
                  the function's terminating `end`",
        does_not_cover: "the CHOICE of bracket structure. Any well-formed nest passes; that this \
                         nest is the one Ramsey's dominator-tree recursion prescribes for THIS CFG \
                         is exactly the bisimulation deferral",
    },
    CfgInvariantRow {
        id: "S2 function label arity",
        statement: "the implicit function label takes the function's declared result types, so a \
                    `br` to it and the body's final `end` both leave exactly the declared results",
        refutes: "a body that falls off its end with the wrong number of results, and a `return` \
                  emitted with an empty stack in a value-returning function",
        does_not_cover: "the C-ABI / call-convention side of the signature, which is family 3 \
                         (call/table ABI discipline)",
    },
];

// ===========================================================================
// Named deferrals — RED in the denominator, never a weak obligation
// ===========================================================================

/// One honestly DEFERRED control-flow property: what it is, which family owes
/// an answer, and why THIS invariant cannot supply one.
///
/// Same contract as `wasm_value_domain::WasmValueDomainDeferral`: these stay RED
/// in the denominator, are never allowlisted out, and are never given a weak
/// obligation that would launder them green.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct WasmCfgDeferral {
    /// Display name.
    pub name: &'static str,
    /// The evidence family that must ultimately discharge this.
    pub family: &'static str,
    /// Why the structural invariant cannot express it.
    pub reason: &'static str,
}

/// The five named CFG-family deferrals. The FIRST one is the family's own
/// headline claim, kept RED on purpose: this module does not prove the relooper
/// correct and must never be read as if it did.
pub const WASM_CFG_DEFERRALS: &[WasmCfgDeferral] = &[
    WasmCfgDeferral {
        name: "relooper BISIMULATION (the family's own headline, deliberately RED)",
        family: "CFG/SSA semantic simulation — a ty/Lean simulation relation between the trust-ir \
                 CFG's small-step semantics and the structured wasm program's",
        reason: "the invariant in this file is a NECESSARY CONDITION on the structuring, not a \
                 proof that the structured program computes what the trust-ir CFG computes. It \
                 states that the emitted nest is well formed and that every branch names a live \
                 label of the right arity; it says nothing about the CORRESPONDENCE between wasm \
                 program points and trust-ir blocks, so a structurally perfect nest that visits the \
                 blocks in the wrong ORDER satisfies every row above. Discharging it needs a \
                 simulation relation R between trust-ir configurations and wasm configurations with \
                 R preserved by every step — Ramsey ICFP 2022 gives the skeleton (the dominator-tree \
                 recursion is what `lower.rs` implements), but the relation itself has to be stated \
                 and proved against a wasm operational semantics that does not exist in this \
                 repository. Until it does, the wasm lane stays DIFFERENTIAL-EXPERIMENTAL and this \
                 row stays RED",
    },
    WasmCfgDeferral {
        name: "branch-target INTENT binding (which trust-ir successor a label denotes)",
        family: "CFG/SSA semantic simulation — needs a byte-offset <-> trust-ir-block provenance map \
                 the backend does not emit",
        reason: "the design's phrase is 'every br depth resolves to a live label REACHING THE \
                 INTENDED SUCCESSOR'. The first half is B1 and is checked. The second half is not, \
                 and cannot be from bytes alone: the emitted module carries no record of which \
                 trust-ir block each label was opened for, so a branch retargeted to a DIFFERENT \
                 live label of the same arity is indistinguishable from the correct one. The gap is \
                 not asserted here, it is MEASURED: `all_cfg_mutants` ships two \
                 `MutantExpectation::KnownBlindSpot` mutants — a depth retargeted to another live \
                 same-arity label, and a `block` opener rewritten as a `loop` (which silently turns \
                 a forward exit into a backward jump) — and the family's tests assert that the \
                 checker does NOT catch them. Closing this needs either a provenance side-channel \
                 from `lower.rs` or the full bisimulation above",
    },
    WasmCfgDeferral {
        name: "block-parameter (phi) resolution across edges",
        family: "CFG/SSA semantic simulation — the SSA half of family 1",
        reason: "trust-ir block parameters are lowered to wasm locals: an edge's arguments are \
                 written into the target block's param locals before control transfers, and the \
                 writes are permutation-safe (all reads pushed, then sets in reverse) so a back-edge \
                 that SWAPS two induction variables stays correct. This invariant sees those writes \
                 only as `local.set` instructions with well-typed operands: it checks their TYPES \
                 and their stack discipline and nothing about whether the right value reached the \
                 right parameter, which is a data-flow property over the edge, not a structural one. \
                 A wrong permutation type-checks perfectly",
    },
    WasmCfgDeferral {
        name: "unreachable-code coverage",
        family: "CFG/SSA semantic simulation (jointly with the differential oracle lane)",
        reason: "the spec's validation algorithm makes the value stack POLYMORPHIC after \
                 `unreachable`, `br`, `br_table` and `return`, so operand types in code the \
                 validator can prove unreachable are unconstrained by construction — this module \
                 implements that rule faithfully, which means a defect confined to such code is \
                 invisible to it. This is a property of the spec's typing discipline, not a \
                 shortcut taken here, and it is why the differential corpus (which EXECUTES the \
                 module) is not made redundant by this family",
    },
    WasmCfgDeferral {
        name: "module-level well-formedness beyond the code section",
        family: "module-level indexing/encoding (family 4) and byte reconstruction with an \
                 independent signed-LEB128 decoder (family 5)",
        reason: "this checker decodes the type, import, function, global, export and code sections \
                 because a control-flow type check cannot proceed without them, and it SKIPS table, \
                 memory, start, element, data and datacount by length. Nothing here obligates the \
                 section order, the index-space shift that imported functions impose, the element \
                 segment's funcidx-to-table-index mapping, or the LEB128 encodings themselves \
                 beyond rejecting over-long ones. Those are separate families' rows and must not be \
                 read as covered because a module 'passed the CFG check'",
    },
];

// ===========================================================================
// Anti-tautology — mutate the thing under proof and show it FAILS
// ===========================================================================

/// What a mutant is expected to do to the checker.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MutantExpectation {
    /// The checker MUST refute this mutant. A pass means the matching invariant
    /// is vacuous.
    MustBeRefuted,
    /// The checker is KNOWN not to catch this. Shipped as executable evidence of
    /// a named deferral's gap — asserting it is caught would be the over-claim.
    KnownBlindSpot,
}

/// A deliberately-wrong module, its provenance, and what is expected of it.
#[derive(Debug, Clone)]
pub struct CfgMutant {
    /// Short name for reports.
    pub name: &'static str,
    /// What was changed and why it is the wrong lowering that matters.
    pub description: &'static str,
    /// The mutated module bytes.
    pub bytes: Vec<u8>,
    /// What the checker must do with it.
    pub expectation: MutantExpectation,
}

/// The outcome of running one mutant through [`check_module_structure`].
#[derive(Debug, Clone)]
pub struct MutantOutcome {
    /// The mutant's name.
    pub name: &'static str,
    /// What was expected.
    pub expectation: MutantExpectation,
    /// What happened.
    pub verdict: CfgVerdict,
    /// Did the outcome match the expectation?
    pub as_expected: bool,
}

// --- a hand-encoded reference module, so the mutants need no codegen -------

fn uleb(out: &mut Vec<u8>, mut v: u64) {
    loop {
        let mut byte = (v & 0x7f) as u8;
        v >>= 7;
        if v != 0 {
            byte |= 0x80;
        }
        out.push(byte);
        if v == 0 {
            return;
        }
    }
}

fn section(out: &mut Vec<u8>, id: u8, body: &[u8]) {
    out.push(id);
    uleb(out, body.len() as u64);
    out.extend_from_slice(body);
}

/// Wrap one `(i32, i32) -> i32` body into a complete, self-contained module
/// with one `i32` local. The body must NOT carry its trailing `end`; this adds
/// it, exactly as the code section requires.
fn synth_module(name: &str, body: &[u8]) -> Vec<u8> {
    let mut out = vec![0x00, 0x61, 0x73, 0x6d, 0x01, 0x00, 0x00, 0x00];

    // Type section: one (i32, i32) -> i32.
    let mut types = Vec::new();
    uleb(&mut types, 1);
    types.push(0x60);
    uleb(&mut types, 2);
    types.push(0x7f);
    types.push(0x7f);
    uleb(&mut types, 1);
    types.push(0x7f);
    section(&mut out, 1, &types);

    // Function section: one function of type 0.
    let mut funcs = Vec::new();
    uleb(&mut funcs, 1);
    uleb(&mut funcs, 0);
    section(&mut out, 3, &funcs);

    // Export section.
    let mut exports = Vec::new();
    uleb(&mut exports, 1);
    uleb(&mut exports, name.len() as u64);
    exports.extend_from_slice(name.as_bytes());
    exports.push(0x00);
    uleb(&mut exports, 0);
    section(&mut out, 7, &exports);

    // Code section: one local run of 1 x i32, the body, then `end`.
    let mut entry = Vec::new();
    uleb(&mut entry, 1); // one local run
    uleb(&mut entry, 1); // count 1
    entry.push(0x7f); // i32
    entry.extend_from_slice(body);
    entry.push(0x0b); // the function's `end`

    let mut code = Vec::new();
    uleb(&mut code, 1);
    uleb(&mut code, entry.len() as u64);
    code.extend_from_slice(&entry);
    section(&mut out, 10, &code);

    out
}

/// The CORRECT nest for a node with two merge children, per Ramsey ICFP 2022 §4
/// and `lower.rs`'s `node_within`: **latest-RPO outermost**.
///
/// ```text
/// block            ;; $Y2  — latest RPO, OUTERMOST
///   block          ;; $Y1  — earliest RPO, innermost
///     local.get 0
///     if  ; br 1 -> $Y1 ; else br 2 -> $Y2
///   end            ;; $Y1's join
///   <Y1's subtree>  ;; still inside $Y2, so its forward br 0 -> $Y2 resolves
/// end              ;; $Y2's join
/// <Y2's subtree>   ;; the reachable tail that produces the function's result
/// ```
pub fn correct_merge_nest_module() -> Vec<u8> {
    #[rustfmt::skip]
    let body: Vec<u8> = vec![
        0x02, 0x40,             // block  $Y2
        0x02, 0x40,             //   block $Y1
        0x20, 0x00,             //     local.get 0
        0x04, 0x40,             //     if
        0x0c, 0x01,             //       br 1   -> $Y1
        0x05,                   //     else
        0x0c, 0x02,             //       br 2   -> $Y2
        0x0b,                   //     end (if)
        0x0b,                   //   end $Y1  — the join
        0x20, 0x00,             //   local.get 0     ;; Y1's subtree
        0x1a,                   //   drop
        0x0c, 0x00,             //   br 0     -> $Y2 (still in scope: THIS is the point)
        0x0b,                   // end $Y2 — the join
        0x20, 0x00,             // local.get 0       ;; Y2's subtree: the reachable tail
        0x21, 0x02,             // local.set 2
        0x20, 0x01,             // local.get 1
    ];
    synth_module("merge_nest", &body)
}

/// The MIS-ORDERED nest — the P3 defect shape, earliest-RPO outermost
/// (`split_first`). `$Y1` is opened first, so `Y1`'s subtree is emitted AFTER
/// `$Y1`'s `end`, outside every block, and its forward branch to `$Y2` has no
/// label in scope. Only the function label is live there, so the depth the
/// buggy nest needs names nothing: invariant B1 must REFUTE this.
pub fn misordered_merge_nest_module() -> Vec<u8> {
    #[rustfmt::skip]
    let body: Vec<u8> = vec![
        0x02, 0x40,             // block  $Y1   — earliest RPO outermost: THE BUG
        0x02, 0x40,             //   block $Y2
        0x20, 0x00,             //     local.get 0
        0x04, 0x40,             //     if
        0x0c, 0x02,             //       br 2   -> $Y1
        0x05,                   //     else
        0x0c, 0x01,             //       br 1   -> $Y2
        0x0b,                   //     end (if)
        0x0b,                   //   end $Y2
        0x20, 0x00,             //   local.get 0     ;; Y2's subtree
        0x21, 0x02,             //   local.set 2
        0x0b,                   // end $Y1
        0x20, 0x00,             // local.get 0       ;; Y1's subtree, OUTSIDE both blocks
        0x21, 0x02,             // local.set 2
        0x0c, 0x01,             // br 1 -> $Y2 ... which is CLOSED. Only the func label is live.
        0x20, 0x01,             // local.get 1
    ];
    synth_module("merge_nest_misordered", &body)
}

// --- byte mutators over any real emitted module ---------------------------

/// Patch the first single-byte `br`/`br_if` depth immediate in the module,
/// setting it to `new_depth` (which must encode in one ULEB byte).
///
/// Same-length by construction, so no section or entry length prefix moves —
/// the mutant is a byte-for-byte legal module differing only in one depth.
pub fn mutate_branch_depth(module: &[u8], new_depth: u32) -> Option<Vec<u8>> {
    if new_depth > 0x7f {
        return None;
    }
    let bodies = decode_function_bodies(module).ok()?;
    for (base, insts) in bodies {
        for inst in insts {
            if (inst.opcode == 0x0c || inst.opcode == 0x0d) && inst.size == 2 {
                let mut out = module.to_vec();
                *out.get_mut(base + inst.offset + 1)? = new_depth as u8;
                return Some(out);
            }
        }
    }
    None
}

/// Increment the `nth` single-byte `br`/`br_if` depth immediate by one — the
/// OFF-BY-ONE a depth-arithmetic slip actually produces (`open_labels - depth`
/// computed against a stale frame). Returns `None` once `nth` is past the last
/// such branch, so a caller can enumerate every branch site in the module.
///
/// Whether this is refutable depends on the site: at the outermost label it
/// leaves the label stack entirely (B1 refutes), and deeper in it lands on
/// another live label (the intent-binding blind spot). Both outcomes are real
/// data about what the invariant discriminates, which is why the mutator
/// enumerates rather than picking a convenient site.
pub fn mutate_bump_nth_branch_depth(module: &[u8], nth: usize) -> Option<Vec<u8>> {
    let bodies = decode_function_bodies(module).ok()?;
    let mut seen = 0usize;
    for (base, insts) in bodies {
        for inst in insts {
            if !matches!(inst.opcode, 0x0c..=0x0d) || inst.size != 2 {
                continue;
            }
            let Imm::Depth(d) = inst.imm else { continue };
            if d >= 0x7f {
                continue;
            }
            if seen == nth {
                let mut out = module.to_vec();
                *out.get_mut(base + inst.offset + 1)? = (d + 1) as u8;
                return Some(out);
            }
            seen += 1;
        }
    }
    None
}

/// Retarget the first `br` whose depth is >= 1 to `depth - 1`: still a LIVE
/// label, still the same (void) arity — the wrong-successor mutation the
/// invariant is NOT expected to catch.
pub fn mutate_branch_to_wrong_live_label(module: &[u8]) -> Option<Vec<u8>> {
    let bodies = decode_function_bodies(module).ok()?;
    for (base, insts) in bodies {
        for inst in &insts {
            if inst.opcode != 0x0c || inst.size != 2 {
                continue;
            }
            let Imm::Depth(d) = inst.imm else { continue };
            if !(1..=0x7f).contains(&d) {
                continue;
            }
            let mut out = module.to_vec();
            *out.get_mut(base + inst.offset + 1)? = (d - 1) as u8;
            return Some(out);
        }
    }
    None
}

/// Erase the `nth` non-final `end` by overwriting it with `nop` (0x01) — a
/// dropped block `end`, at the same byte length so nothing else shifts.
pub fn mutate_erase_end(module: &[u8], nth: usize) -> Option<Vec<u8>> {
    let bodies = decode_function_bodies(module).ok()?;
    let mut seen = 0usize;
    for (base, insts) in bodies {
        let last = insts.len().saturating_sub(1);
        for (i, inst) in insts.iter().enumerate() {
            if inst.opcode == 0x0b && i != last {
                if seen == nth {
                    let mut out = module.to_vec();
                    *out.get_mut(base + inst.offset)? = 0x01;
                    return Some(out);
                }
                seen += 1;
            }
        }
    }
    None
}

/// Rewrite the first `local.set` (0x21) as a `local.get` (0x20): one byte, and
/// it turns a pop into a push, so the enclosing join's height stops matching.
pub fn mutate_local_set_to_get(module: &[u8]) -> Option<Vec<u8>> {
    let bodies = decode_function_bodies(module).ok()?;
    for (base, insts) in bodies {
        for inst in insts {
            if inst.opcode == 0x21 {
                let mut out = module.to_vec();
                *out.get_mut(base + inst.offset)? = 0x20;
                return Some(out);
            }
        }
    }
    None
}

/// Rewrite the `nth` `local.set` (0x21) as a `local.get` (0x20), counting
/// across every function body in order. Returns `None` once `nth` is past the
/// last `local.set`, so a caller can enumerate every site: whether the extra
/// value reaches a reachable join depends on the site, as for
/// [`mutate_bump_nth_branch_depth`].
pub fn mutate_nth_local_set_to_get(module: &[u8], nth: usize) -> Option<Vec<u8>> {
    let bodies = decode_function_bodies(module).ok()?;
    let mut seen = 0usize;
    for (base, insts) in bodies {
        for inst in insts {
            if inst.opcode != 0x21 {
                continue;
            }
            if seen == nth {
                let mut out = module.to_vec();
                *out.get_mut(base + inst.offset)? = 0x20;
                return Some(out);
            }
            seen += 1;
        }
    }
    None
}

/// Rewrite the first `i32.add` (0x6a) as `i64.add` (0x7c) — the operand TYPE
/// mutation, which J2 must refute.
pub fn mutate_i32_add_to_i64_add(module: &[u8]) -> Option<Vec<u8>> {
    let bodies = decode_function_bodies(module).ok()?;
    for (base, insts) in bodies {
        for inst in insts {
            if inst.opcode == 0x6a {
                let mut out = module.to_vec();
                *out.get_mut(base + inst.offset)? = 0x7c;
                return Some(out);
            }
        }
    }
    None
}

/// Rewrite the first `block` opener (0x02) as a `loop` (0x03). Every branch to
/// it becomes a BACKWARD jump — a real miscompile — but the label's types are
/// unchanged, so a type-and-height invariant cannot see it. Shipped as a
/// KnownBlindSpot.
pub fn mutate_block_opener_to_loop(module: &[u8]) -> Option<Vec<u8>> {
    let bodies = decode_function_bodies(module).ok()?;
    for (base, insts) in bodies {
        for inst in insts {
            if inst.opcode == 0x02 {
                let mut out = module.to_vec();
                *out.get_mut(base + inst.offset)? = 0x03;
                return Some(out);
            }
        }
    }
    None
}

/// Every mutant built over the module this file encodes by hand, so the
/// anti-tautology battery runs with no codegen dependency. The tests run the
/// SAME mutators over the real backend's output as well.
pub fn all_cfg_mutants() -> Vec<CfgMutant> {
    let base = correct_merge_nest_module();
    let mut out = Vec::new();

    out.push(CfgMutant {
        name: "merge children nested EARLIEST-RPO-outermost (the P3 defect shape)",
        description: "the `split_first` nest: Y1's subtree is emitted outside Y2's block, so its \
                      forward branch names a label that is no longer live",
        bytes: misordered_merge_nest_module(),
        expectation: MutantExpectation::MustBeRefuted,
    });
    if let Some(b) = mutate_branch_depth(&base, 0x7f) {
        out.push(CfgMutant {
            name: "br depth far out of scope",
            description: "a branch depth immediate rewritten to 127 — no such label is open",
            bytes: b,
            expectation: MutantExpectation::MustBeRefuted,
        });
    }
    if let Some(b) = mutate_branch_depth(&base, 0x04) {
        out.push(CfgMutant {
            name: "br depth one past the outermost label",
            description: "the off-by-one a depth arithmetic slip produces: one deeper than the \
                          function label (four labels are live at that branch)",
            bytes: b,
            expectation: MutantExpectation::MustBeRefuted,
        });
    }
    if let Some(b) = mutate_erase_end(&base, 0) {
        out.push(CfgMutant {
            name: "dropped block `end`",
            description: "an inner `end` overwritten with `nop`, so the scope never closes and the \
                          function label is closed in its place",
            bytes: b,
            expectation: MutantExpectation::MustBeRefuted,
        });
    }
    if let Some(b) = mutate_local_set_to_get(&base) {
        out.push(CfgMutant {
            name: "local.set lowered as local.get",
            description: "a pop turned into a push: the enclosing join's stack height no longer \
                          matches its entry height",
            bytes: b,
            expectation: MutantExpectation::MustBeRefuted,
        });
    }
    if let Some(b) = mutate_branch_to_wrong_live_label(&base) {
        out.push(CfgMutant {
            name: "BLIND SPOT: br retargeted to another live, same-arity label",
            description: "the wrong-successor lowering. Structurally impeccable, semantically \
                          wrong; only the bisimulation can see it",
            bytes: b,
            expectation: MutantExpectation::KnownBlindSpot,
        });
    }
    if let Some(b) = mutate_block_opener_to_loop(&base) {
        out.push(CfgMutant {
            name: "BLIND SPOT: `block` opener rewritten as `loop`",
            description: "every branch to that label silently becomes a BACKWARD jump; the label's \
                          types are unchanged, so a type/height invariant cannot see it",
            bytes: b,
            expectation: MutantExpectation::KnownBlindSpot,
        });
    }
    out
}

/// Run the whole anti-tautology battery and report what actually happened —
/// including the blind spots, which are reported as such rather than hidden.
pub fn run_cfg_mutants() -> Vec<MutantOutcome> {
    all_cfg_mutants()
        .into_iter()
        .map(|m| {
            let verdict = check_module_structure(&m.bytes);
            let as_expected = match m.expectation {
                MutantExpectation::MustBeRefuted => verdict.is_refuted(),
                MutantExpectation::KnownBlindSpot => verdict.holds(),
            };
            MutantOutcome {
                name: m.name,
                expectation: m.expectation,
                verdict,
                as_expected,
            }
        })
        .collect()
}

// ===========================================================================
// The audit surface a gate can render
// ===========================================================================

/// A one-line audit summary of this family: what it checked, what it refuted,
/// what it declined, and what stays RED.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CfgFamilySummary {
    /// Invariant rows this family checks.
    pub invariants: usize,
    /// Named deferrals, all RED.
    pub deferrals: usize,
    /// Mutants that must be refuted.
    pub mutants_must_refute: usize,
    /// Mutants shipped as known blind spots.
    pub mutants_blind_spots: usize,
    /// Mutants whose outcome matched the expectation.
    pub mutants_as_expected: usize,
}

/// Summarize the family without any module input — the shape a coverage gate
/// renders next to the value-domain rows.
pub fn cfg_family_summary() -> CfgFamilySummary {
    let outcomes = run_cfg_mutants();
    CfgFamilySummary {
        invariants: WASM_CFG_INVARIANTS.len(),
        deferrals: WASM_CFG_DEFERRALS.len(),
        mutants_must_refute: outcomes
            .iter()
            .filter(|o| o.expectation == MutantExpectation::MustBeRefuted)
            .count(),
        mutants_blind_spots: outcomes
            .iter()
            .filter(|o| o.expectation == MutantExpectation::KnownBlindSpot)
            .count(),
        mutants_as_expected: outcomes.iter().filter(|o| o.as_expected).count(),
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    /// The hand-encoded reference module decodes, and its structure holds.
    #[test]
    fn correct_merge_nest_holds() {
        let m = correct_merge_nest_module();
        let verdict = check_module_structure(&m);
        assert!(verdict.holds(), "{verdict}");
        let report = verdict.report().expect("holds");
        let f = report.functions.first().expect("one function");
        assert_eq!(f.blocks, 2, "two merge blocks");
        assert_eq!(f.ifs, 1);
        assert_eq!(f.loops, 0);
        // Three branches: br 1, br 2, br 0.
        assert_eq!(f.branches.len(), 3);
        assert_eq!(f.name.as_deref(), Some("merge_nest"));
    }

    /// THE TEETH: the P3 merge-child ordering shape is REFUTED, and refuted by
    /// the liveness invariant specifically.
    #[test]
    fn misordered_merge_nest_is_refuted_by_label_liveness() {
        let verdict = check_module_structure(&misordered_merge_nest_module());
        match verdict {
            CfgVerdict::Refuted(CfgViolation::BranchDepthOutOfRange {
                depth, live_labels, ..
            }) => {
                assert_eq!(depth, 1);
                assert_eq!(live_labels, 1, "only the function label is live there");
            }
            other => panic!("expected a liveness refutation, got {other}"),
        }
    }

    /// Every mutant behaves as declared: the must-refute ones are refuted, and
    /// the blind spots are NOT — which is the honest statement of the gap.
    #[test]
    fn mutants_behave_as_declared() {
        let outcomes = run_cfg_mutants();
        assert!(!outcomes.is_empty(), "the battery must not be empty");
        for o in &outcomes {
            assert!(
                o.as_expected,
                "mutant '{}' expected {:?} but got {}",
                o.name, o.expectation, o.verdict
            );
        }
        let must = outcomes
            .iter()
            .filter(|o| o.expectation == MutantExpectation::MustBeRefuted)
            .count();
        let blind = outcomes.len() - must;
        assert!(must >= 5, "at least five must-refute mutants, got {must}");
        assert!(blind >= 2, "the blind spots must be shipped, got {blind}");
    }

    /// An INCONCLUSIVE verdict is never a pass. A module whose code section
    /// carries an opcode with no typing rule here must not be credited.
    #[test]
    fn unknown_opcode_is_inconclusive_not_holds() {
        // 0xd0 (`ref.null`) is outside the modeled surface.
        let body = vec![0x20, 0x00, 0x1a, 0xd0];
        let m = synth_module("unknown", &body);
        let verdict = check_module_structure(&m);
        assert!(verdict.is_inconclusive(), "{verdict}");
        assert!(!structural_invariant_holds(&m));
    }

    /// A truncated / non-wasm buffer declines rather than panicking or passing.
    #[test]
    fn garbage_input_declines() {
        for bytes in [&b""[..], &b"not wasm at all"[..], &[0x00, 0x61][..]] {
            let verdict = check_module_structure(bytes);
            assert!(verdict.is_inconclusive(), "{verdict}");
        }
    }

    /// The independent LEB128 reader agrees with the spec's own examples and
    /// REJECTS an over-long encoding rather than normalizing it away.
    #[test]
    fn leb128_reader_matches_the_spec_examples() {
        let cases: &[(&[u8], u64)] = &[
            (&[0x00], 0),
            (&[0x7f], 127),
            (&[0x80, 0x01], 128),
            (&[0xac, 0x02], 300),
            (&[0xe5, 0x8e, 0x26], 624485),
        ];
        for (bytes, want) in cases {
            let mut r = Reader::new(bytes);
            assert_eq!(r.uleb64(), Some(*want), "uleb {bytes:?}");
        }
        let signed: &[(&[u8], i64)] = &[
            (&[0x00], 0),
            (&[0x7f], -1),
            (&[0x3f], 63),
            (&[0xc0, 0x00], 64),
            (&[0x40], -64),
            (&[0xbf, 0x7f], -65),
        ];
        for (bytes, want) in signed {
            let mut r = Reader::new(bytes);
            assert_eq!(r.sleb64(), Some(*want), "sleb {bytes:?}");
        }
        // 11 continuation bytes cannot be a u64: rejected, not truncated.
        let overlong = [0x80u8; 11];
        let mut r = Reader::new(&overlong);
        assert_eq!(r.uleb64(), None);
    }

    /// The decoder's memory-opcode table agrees with the INDEPENDENT one in
    /// `wasm_semantics` (which the value-domain family keys on). The two were
    /// written from the spec separately; a disagreement means one of them
    /// mis-transcribed §5.4.4.
    #[test]
    fn memory_rules_agree_with_wasm_semantics() {
        for byte in 0x28u8..=0x3e {
            let mine = memory_rule(byte).expect("modeled");
            let theirs = crate::wasm_semantics::decode_mem_op(byte).expect("decoded");
            assert_eq!(mine.0, theirs.is_load(), "0x{byte:02x} load/store");
            let want_value = match theirs.value_bits {
                32 if theirs.is_fp => ValKind::F32,
                64 if theirs.is_fp => ValKind::F64,
                32 => ValKind::I32,
                64 => ValKind::I64,
                other => panic!("0x{byte:02x}: unexpected value width {other}"),
            };
            assert_eq!(mine.1, want_value, "0x{byte:02x} value type");
        }
    }

    /// A `loop` label's continuation is BACKWARD and a `block` label's is
    /// forward. Reported as derived artifact content, asserted here so the
    /// report cannot silently invert.
    #[test]
    fn loop_labels_resolve_backward_and_blocks_forward() {
        #[rustfmt::skip]
        let body: Vec<u8> = vec![
            0x02, 0x40,       // block
            0x03, 0x40,       //   loop
            0x20, 0x00,       //     local.get 0
            0x04, 0x40,       //     if
            0x0c, 0x01,       //       br 1 -> loop  (BACKWARD)
            0x05,             //     else
            0x0c, 0x02,       //       br 2 -> block (forward)
            0x0b,             //     end
            0x0b,             //   end loop
            0x0b,             // end block
            0x20, 0x01,       // local.get 1
        ];
        let m = synth_module("loop_shape", &body);
        let verdict = check_module_structure(&m);
        assert!(verdict.holds(), "{verdict}");
        let f = verdict
            .report()
            .and_then(|r| r.functions.first())
            .expect("one function");
        assert_eq!(f.loops, 1);
        assert_eq!(f.blocks, 1);
        let backward: Vec<bool> = f.branches.iter().map(|b| b.continuation.backward).collect();
        assert_eq!(backward, vec![true, false]);
        let to_loop = f.branches.first().expect("first branch");
        assert!(
            to_loop.continuation.offset < to_loop.offset,
            "a loop label's continuation precedes the branch"
        );
        assert_eq!(to_loop.label_kind, ScopeKind::Loop);
    }

    /// The polymorphic-stack rule is implemented, not approximated: code after
    /// `unreachable` type-checks against anything, exactly as the spec says.
    /// This is the `unreachable-code coverage` deferral, made concrete.
    #[test]
    fn unreachable_code_is_polymorphic_by_the_spec_rule() {
        #[rustfmt::skip]
        let body: Vec<u8> = vec![
            0x00,             // unreachable
            0x6a,             // i32.add  — pops two values that are not there
            0x1a,             // drop
            0x20, 0x01,       // local.get 1
        ];
        let m = synth_module("poly", &body);
        assert!(check_module_structure(&m).holds());
    }

    /// The invariant inventory and the deferral inventory are both pinned:
    /// every row states what it does NOT cover, and every deferral names a
    /// family plus a substantive reason. A token reason is debt behind a label.
    #[test]
    fn inventories_are_named_and_substantive() {
        assert_eq!(WASM_CFG_INVARIANTS.len(), 7);
        for row in WASM_CFG_INVARIANTS {
            assert!(!row.statement.is_empty(), "{} has no statement", row.id);
            assert!(row.refutes.len() > 40, "{} has a token refutation", row.id);
            assert!(
                row.does_not_cover.len() > 40,
                "{} does not say what it leaves open",
                row.id
            );
        }
        assert_eq!(WASM_CFG_DEFERRALS.len(), 5);
        let names: std::collections::HashSet<_> =
            WASM_CFG_DEFERRALS.iter().map(|d| d.name).collect();
        assert_eq!(names.len(), 5, "deferral names must be distinct");
        for d in WASM_CFG_DEFERRALS {
            assert!(!d.family.is_empty(), "{} has no family", d.name);
            assert!(
                d.reason.len() > 200,
                "{} has a token reason, not an auditable one",
                d.name
            );
        }
        // The bisimulation is deferred BY NAME. If this ever stops being true
        // without a simulation relation landing, the family is over-claiming.
        assert!(
            WASM_CFG_DEFERRALS
                .iter()
                .any(|d| d.name.contains("BISIMULATION")),
            "the bisimulation must stay a named RED deferral"
        );
    }

    /// The family summary reports the real battery outcome.
    #[test]
    fn family_summary_counts_are_real() {
        let s = cfg_family_summary();
        assert_eq!(s.invariants, WASM_CFG_INVARIANTS.len());
        assert_eq!(s.deferrals, WASM_CFG_DEFERRALS.len());
        assert_eq!(
            s.mutants_as_expected,
            s.mutants_must_refute + s.mutants_blind_spots,
            "every mutant must behave as declared"
        );
    }
}
