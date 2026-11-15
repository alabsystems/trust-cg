// trust-cg-verify/wasm_abi_proofs.rs - P4 families (2) and (3): the wasm
// shadow-stack / linear-memory refinement OF THE LOWERING, and the call/table
// ABI discipline.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Reference: WebAssembly Core Specification, Release 2.0 — "Binary Format"
//            (module sections, index spaces, LEB128 immediates) and
//            "Instructions" (call / call_indirect, the memory instructions).
//            Normative host contract: crates/trust-cg-codegen/src/wasm/OWNERSHIP.md.
//
// WHAT THIS MODULE IS, AND WHAT IT IS NOT
//
// The design's family (2) asks for a linear-memory refinement OF `lower.rs` —
// specifically the shadow-stack arithmetic that `wasm_memory_proofs.rs`'s own
// header names as NOT covered ("the shadow-stack frame offset arithmetic",
// `wasm_memory_proofs.rs:31-34`, cited by OWNERSHIP.md §1.5's last row as
// guaranteed by "nobody yet"). Family (3) asks for the call/table ABI: the
// argument/return stack discipline, the table index typecheck, and that a
// call's target index resolves to a function of the signature the call site
// declares — which P2 made sharper by giving imported functions the LOW index
// space, so a call target's meaning depends on the import count.
//
// The machine side of every statement here is REBUILT BY DECODING THE REAL
// EMITTED MODULE BYTES with the decoder in this file (an independent
// re-implementation of the binary format: its own ULEB128/SLEB128 readers, its
// own section walker, its own instruction walker that FAILS CLOSED on an opcode
// it does not know). The source side is built from the trust-ir function's own
// layout and signature data. Nothing here reads `lower.rs` or `encode.rs`, and
// the two crates cannot even see each other in the production graph: codegen
// depends on verify, so the backend is reachable from this crate only through
// `[dev-dependencies]` in the test file. The `src` side takes BYTES.
//
// TWO KINDS OF EVIDENCE, LABELED RATHER THAN BLENDED
//
//   * [`ProofObligation`]s — the frame ARITHMETIC. Frame-base computation,
//     alloca placement, containment, pairwise non-overlap and stack-pointer
//     restoration are statements about 32-bit address arithmetic over a
//     SYMBOLIC entry stack pointer, so they are genuine SMT obligations: built
//     by symbolically executing the DECODED prologue / alloca / epilogue
//     instruction windows, discharged by the evaluator, and (where a proof
//     authority exists) by `ay`.
//   * [`AbiStructuralCheck`]s — the INDEX-SPACE and ABI discipline. "This
//     `call`'s target index resolves to a function of the declared signature",
//     "the arg window pushes exactly these types", "element i + 1 is function i"
//     are DECIDABLE equalities over the decoded module. Handing them to a
//     solver would be theatre, so they are not dressed as SMT obligations:
//     they are decoded, compared, and reported with their own counts. Their
//     teeth are the byte-level mutation guards below, not a solver verdict.
//
// ANTI-TAUTOLOGY: THE GUARDS MUTATE REAL BYTES
//
// [`all_wasm_abi_guards`] does not build a hand-written "wrong" expression. It
// takes the REAL emitted module, patches bytes in place (same length, so the
// module stays decodable), re-runs the whole family, and requires the evidence
// to FAIL. A guard that passes means the family has gone vacuous. One guard is
// declared [`GuardExpectation::KnownBlind`] and is reported as NOT refuted,
// with the reason — see `WASM_ABI_DEFERRALS` entry "call-site correspondence".
// Hiding it would be the dishonesty this file exists to avoid.
//
// WHAT IS DEFERRED, BY NAME: see [`WASM_ABI_DEFERRALS`]. Every host obligation
// this family cannot touch — region ownership under an imported memory, the
// stack reserve bound, base alignment, argument-window validity, restoration
// after a trap — stays RED in the denominator with the OWNERSHIP.md clause that
// owns it. None of them is given a weak obligation.
//
// THE INTERNAL ABI: the object lane's multi-value internal ABI (P6) is
// checked by the sibling module `wasm_internal_abi.rs` — the symbol-table
// boundary gate, the forwarding (return) binding of every internal entry's
// C-form entry, its source binding against the trust-ir signature, and the
// link binding across a crate's objects — over relocatable objects, which
// this file's closed-module decoder does not read. Its live gate is the
// separate target `tests/wasm_internal_abi_gate.rs`; it adds nothing to
// this family's denominators.
//
// THIS FAMILY PROMOTES NOTHING TO "VERIFIED". It covers the frame arithmetic
// and the call/table index discipline of the modules it is run over. It says
// nothing about the relooper, the value domain, the encoder's byte layout
// beyond what it decodes, or TargetInfo conformance — those are other families.

//! P4 families (2) and (3) for the WebAssembly backend: shadow-stack frame
//! layout refinement of the lowering, and call / `call_indirect` / funcref-table
//! ABI discipline, both reconstructed by decoding the emitted module bytes.

use std::collections::{BTreeMap, BTreeSet};

use trust_ir::{Constant, FuncId, FuncTy, FuncTyId, Function, Inst, Module, Ty};

use crate::lowering_proof::{
    MachineSideProvenance, ProofObligation, TransvalCheckKind, VerificationConfig,
    verify_by_evaluation_with_config,
};
use crate::smt::SmtExpr;
use crate::verify::VerificationResult;

/// Address width of wasm32 linear memory.
const ADDR_BITS: u32 = 32;

/// Bytes in one WebAssembly linear-memory page (spec, "Memory Instructions").
const PAGE_BYTES: u64 = 65536;

// ===========================================================================
// Named deferrals — debt with a name, a family, and a reason
// ===========================================================================

/// One honestly DEFERRED obligation of the memory / call-ABI families: what it
/// is, who must ultimately answer for it, and why this family cannot.
///
/// These stay RED in the denominator. Giving any of them a weak obligation — a
/// "the module does not contain an out-of-region address constant" check
/// standing in for region ownership, say — would launder the row green while
/// refuting none of the wrong programs that matter.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct WasmAbiDeferral {
    /// Display name of the deferred property.
    pub name: &'static str,
    /// Who must discharge it: a host, an engine, or another evidence family.
    pub owner: &'static str,
    /// The normative clause that states it, where one exists.
    pub citation: &'static str,
    /// Why this family cannot state it.
    pub reason: &'static str,
}

/// The nine named deferrals of the memory / call-ABI families. Pinned by
/// `tests/wasm_abi_proofs_gate.rs`: removing one requires landing its evidence,
/// adding one is a deliberate, reviewable admission of debt.
pub const WASM_ABI_DEFERRALS: &[WasmAbiDeferral] = &[
    WasmAbiDeferral {
        name: "aliasing against host memory under an imported memory (Policy I region map)",
        owner: "HOST",
        citation: "crates/trust-cg-codegen/src/wasm/OWNERSHIP.md §1.3, §1.5, §5",
        reason: "under Policy I the island's rights are exactly the stack reserve S and the \
                 argument windows A, a division of the memory that no wasm mechanism expresses \
                 and no engine checks. The emitted code carries NO region check — a scalar Load \
                 lowers to a bare local.get + load with a zero memarg offset, and a field, lane \
                 or sret access to a load/store whose memarg offset is the field's constant \
                 offset, with no base, limit or comparison either way — so no property of the \
                 bytes can refute an access outside S union A. The frame family below proves \
                 the island's OWN frame arithmetic; whether the region that arithmetic lands in \
                 belongs to the island is a fact about the host's allocator that the module does \
                 not name and this evidence must not appear to cover",
    },
    WasmAbiDeferral {
        name: "stack-reserve sufficiency (sum of frame sizes <= R)",
        owner: "HOST",
        citation: "OWNERSHIP.md §1.4 (\"the bounds that do not hold\"), §2 item 5, §7 item 4",
        reason: "an island's prologue contains no comparison against any limit: there is no \
                 stack-limit global, no guard, and no trap (a closed module's floor check \
                 guards its own static data, not a host reserve). This family proves the shape of ONE frame and \
                 hence the chain bound [B - sum(F), B); it cannot bound sum(F), which is \
                 unbounded for any island with a cycle in its call graph and, because \
                 set_func_table publishes every function, has the whole module as its worst-case \
                 target set once a call_indirect exists. A declared maximum depth D is an open \
                 item on the P2 code, not a fact in the bytes",
    },
    WasmAbiDeferral {
        name: "stack-pointer restoration on a NON-normal exit (trap, or a host throw through an \
               import)",
        owner: "HOST (rule R1)",
        citation: "OWNERSHIP.md §3 (\"abandoned frames poison the instance\")",
        reason: "the epilogue is emitted only on a normal Return. A trap (unreachable, division \
                 by zero, an out-of-bounds access) or a host exception propagated out of an \
                 import call leaves the stack pointer at the inner value permanently, and no \
                 emitted instruction can restore it. The restoration obligation below is \
                 explicitly conditioned on the normal-return path and says nothing about the \
                 others; the mitigation is R1 (discard a trapped instance), which is a host \
                 action, not a module property",
    },
    WasmAbiDeferral {
        name: "stack base alignment B = 0 (mod 8) under Policy I",
        owner: "HOST",
        citation: "OWNERSHIP.md §1.4, §2 item 3",
        reason: "under Policy I the base arrives as an imported immutable i32 global whose value \
                 is bound at instantiation, so the module cannot observe it and no obligation \
                 over the bytes can constrain it. The frame family proves slot offsets are \
                 8-aligned RELATIVE TO the base, which makes every frame slot exactly as aligned \
                 as the host's base is and no more",
    },
    WasmAbiDeferral {
        name: "argument-window validity, liveness and non-concurrent mutation (Region A)",
        owner: "HOST",
        citation: "OWNERSHIP.md §1.3, §2 (the silent-corruption rows), §6b obligations 5 and 6",
        reason: "a pointer argument's window [ptr, ptr + n*sizeof(elem)) is described by the \
                 island manifest and kept valid by the host. The module receives an i32 and \
                 dereferences it; there is no length, no liveness token and no check, so an \
                 invalid window produces confident wrong answers rather than a trap. Nothing in \
                 the emitted bytes distinguishes the two cases",
    },
    WasmAbiDeferral {
        name: "call-site correspondence across a reordered CFG",
        owner: "relooper / CFG structural bisimulation family (P4 family 1)",
        citation: "this file, `GuardExpectation::KnownBlind`",
        reason: "the lowering emits blocks in dominator-tree order, so for a multi-block function \
                 the emitted sequence of calls is a PERMUTATION of the trust-ir order chosen by \
                 the relooper. This family pins the MULTISET of direct-call targets in a \
                 function and the signature each target resolves to, and binds constant \
                 call_indirect sites one by one only when they all sit in one trust-ir block \
                 AND the body emits exactly as many call_indirect sites as the trust-ir has \
                 (otherwise it too pins their multiset); which trust-ir call site produced which \
                 emitted call is otherwise a CFG fact it cannot see. A permutation of two direct \
                 call sites whose targets have the SAME signature, or of two constant \
                 call_indirect sites in different blocks or in a body whose call_indirect count \
                 differs, is therefore NOT refuted here — the \
                 guard that performs the direct-call mutation is registered as KnownBlind and \
                 reported as not refuted rather than omitted",
    },
    WasmAbiDeferral {
        name: "whole-body operand-stack typing across control flow",
        owner: "module validation gate (wasmparser) + the relooper family",
        citation: "crates/trust-cg-codegen/tests/wasm_module_validation.rs",
        reason: "the argument and result discipline stated here is a LOCAL WINDOW around each \
                 call instruction: the operands immediately preceding it and the consumer \
                 immediately following it. Typing the operand stack across block / loop / if / \
                 br / br_table is a whole-function inference this family does not perform, and \
                 re-implementing it would duplicate the independent reference validator that \
                 already gates every emitted module",
    },
    WasmAbiDeferral {
        name: "the engine's call_indirect runtime signature check",
        owner: "ENGINE",
        citation: "WebAssembly Core Specification, \"Control Instructions\" (call_indirect traps \
                  on a type mismatch)",
        reason: "call_indirect traps at runtime when the table element's actual type differs from \
                 the declared type index. That check is the engine's and appears nowhere in the \
                 module's bytes. This family proves the STATIC half — the declared type index \
                 denotes the call site's own signature, the table immediate is 0, and the element \
                 segment fills table 0 so element i + 1 is function i — which is what makes the \
                 engine's check pass rather than a substitute for it",
    },
    WasmAbiDeferral {
        name: "imported function behaviour (the far side of a call into the host)",
        owner: "HOST",
        citation: "OWNERSHIP.md §4.1, §4.2",
        reason: "a call whose target index is below the import count enters the host. This family \
                 proves the index resolves to an IMPORT of the declared signature and that the \
                 arguments pushed match that signature's parameter types. Whether the host's \
                 function honours the signature, or returns a narrow value in its canonical \
                 carrier, is not a module property — the lowering re-canonicalizes a narrow \
                 result on this side of the boundary for exactly that reason, and that \
                 re-canonicalization belongs to the value-domain family",
    },
];

// ===========================================================================
// An INDEPENDENT decoder for the emitted binary module
// ===========================================================================

/// A failure to decode emitted module bytes. Every variant is FAIL-CLOSED: the
/// family builds no obligation and earns no credit from a module it cannot
/// fully decode, rather than skipping the part it did not understand.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AbiDecodeError {
    /// Ran off the end of the byte stream.
    Truncated(&'static str),
    /// The magic number or version word is not `\0asm` / 1.
    BadHeader,
    /// A LEB128 immediate is longer than its type admits.
    LebOverflow(&'static str),
    /// A section id this decoder does not model appeared.
    UnknownSection(u8),
    /// A byte in a section body did not match the format.
    Malformed(String),
    /// An opcode the instruction walker does not know. Fail closed: an unknown
    /// opcode has an unknown immediate length, so every byte after it would be
    /// mis-decoded.
    UnknownOpcode { at: usize, opcode: u8 },
}

impl std::fmt::Display for AbiDecodeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            AbiDecodeError::Truncated(w) => write!(f, "truncated while reading {w}"),
            AbiDecodeError::BadHeader => write!(f, "not a wasm module (bad magic/version)"),
            AbiDecodeError::LebOverflow(w) => write!(f, "LEB128 overflow reading {w}"),
            AbiDecodeError::UnknownSection(id) => write!(f, "unknown section id {id}"),
            AbiDecodeError::Malformed(m) => write!(f, "malformed module: {m}"),
            AbiDecodeError::UnknownOpcode { at, opcode } => {
                write!(f, "unknown opcode 0x{opcode:02x} at code offset {at}")
            }
        }
    }
}

/// A byte cursor over a module or a section body.
struct Cur<'a> {
    b: &'a [u8],
    p: usize,
}

impl<'a> Cur<'a> {
    fn new(b: &'a [u8]) -> Self {
        Cur { b, p: 0 }
    }

    fn done(&self) -> bool {
        self.p >= self.b.len()
    }

    fn byte(&mut self, what: &'static str) -> Result<u8, AbiDecodeError> {
        let v = *self.b.get(self.p).ok_or(AbiDecodeError::Truncated(what))?;
        self.p += 1;
        Ok(v)
    }

    fn take(&mut self, n: usize, what: &'static str) -> Result<&'a [u8], AbiDecodeError> {
        let end = self
            .p
            .checked_add(n)
            .ok_or(AbiDecodeError::Truncated(what))?;
        if end > self.b.len() {
            return Err(AbiDecodeError::Truncated(what));
        }
        let s = &self.b[self.p..end];
        self.p = end;
        Ok(s)
    }

    /// Unsigned LEB128, at most 32 bits of payload.
    ///
    /// Written from the spec's definition rather than mirrored from the
    /// encoder: accumulate 7-bit groups little-endian while the continuation
    /// bit is set, and refuse a group that would push a bit past 32.
    fn uleb32(&mut self, what: &'static str) -> Result<u32, AbiDecodeError> {
        let mut result: u64 = 0;
        let mut shift = 0u32;
        loop {
            let byte = self.byte(what)?;
            result |= u64::from(byte & 0x7f) << shift;
            if byte & 0x80 == 0 {
                break;
            }
            shift += 7;
            if shift >= 35 {
                return Err(AbiDecodeError::LebOverflow(what));
            }
        }
        u32::try_from(result).map_err(|_| AbiDecodeError::LebOverflow(what))
    }

    /// Signed LEB128, at most 64 bits of payload, sign-extended from the last
    /// group's bit 6.
    fn sleb64(&mut self, what: &'static str) -> Result<i64, AbiDecodeError> {
        let mut result: i64 = 0;
        let mut shift = 0u32;
        loop {
            let byte = self.byte(what)?;
            let payload = i64::from(byte & 0x7f);
            if shift < 64 {
                result |= payload << shift;
            } else if payload != 0 && payload != 0x7f {
                return Err(AbiDecodeError::LebOverflow(what));
            }
            shift += 7;
            if byte & 0x80 == 0 {
                // Sign-extend from the group's high payload bit.
                if shift < 64 && byte & 0x40 != 0 {
                    result |= -1i64 << shift;
                }
                break;
            }
            if shift > 70 {
                return Err(AbiDecodeError::LebOverflow(what));
            }
        }
        Ok(result)
    }

    fn name(&mut self) -> Result<String, AbiDecodeError> {
        let n = self.uleb32("name length")? as usize;
        let bytes = self.take(n, "name bytes")?;
        String::from_utf8(bytes.to_vec())
            .map_err(|_| AbiDecodeError::Malformed("import/export name is not UTF-8".to_string()))
    }
}

/// A decoded function type: the raw valtype BYTES, so no enum of this crate's
/// sits between the module and the comparison.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct DecodedFuncType {
    /// Parameter valtype bytes, in order.
    pub params: Vec<u8>,
    /// Result valtype bytes, in order.
    pub results: Vec<u8>,
}

/// What an import entry brings in.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DecodedImportKind {
    /// A function import, carrying its type-section index.
    Func(u32),
    /// A table import.
    Table,
    /// A memory import.
    Memory,
    /// A global import: valtype byte and mutability.
    Global {
        /// Valtype byte.
        ty: u8,
        /// True for a mutable global.
        mutable: bool,
    },
}

/// One decoded import entry.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DecodedImport {
    /// The wasm module name it is imported from.
    pub module: String,
    /// The member name.
    pub name: String,
    /// What kind of entity it is.
    pub kind: DecodedImportKind,
}

/// The constant expression initializing a defined global.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DecodedInit {
    /// `i32.const v`.
    I32(i32),
    /// `i64.const v`.
    I64(i64),
    /// `global.get idx` — legal in a constant expression only for an imported
    /// immutable global.
    GlobalGet(u32),
}

/// One decoded defined global.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct DecodedGlobal {
    /// Valtype byte.
    pub ty: u8,
    /// True for a mutable global.
    pub mutable: bool,
    /// Its constant initializer.
    pub init: DecodedInit,
}

/// One decoded export entry.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DecodedExport {
    /// Export name.
    pub name: String,
    /// Export descriptor kind byte (0 func, 1 table, 2 memory, 3 global).
    pub kind: u8,
    /// Index in the corresponding index space.
    pub index: u32,
}

/// One decoded active element segment.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DecodedElemSegment {
    /// Table index the segment fills.
    pub table: u32,
    /// The segment's constant offset.
    pub offset: i32,
    /// The function indices it writes, in order.
    pub funcs: Vec<u32>,
}

/// One decoded code-section entry.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DecodedBody {
    /// Run-length local declarations: `(count, valtype byte)`.
    pub local_runs: Vec<(u32, u8)>,
    /// The instruction bytes, INCLUDING the body's trailing `end`.
    pub code: Vec<u8>,
}

impl DecodedBody {
    /// The valtype byte of local `idx`, given the function's parameter types
    /// (which occupy locals `0..params.len()`).
    pub fn local_type(&self, params: &[u8], idx: u32) -> Option<u8> {
        let i = idx as usize;
        if i < params.len() {
            return Some(params[i]);
        }
        let mut rest = i - params.len();
        for &(count, ty) in &self.local_runs {
            let c = count as usize;
            if rest < c {
                return Some(ty);
            }
            rest -= c;
        }
        None
    }

    /// Total local count (parameters excluded).
    pub fn declared_local_count(&self) -> u64 {
        self.local_runs.iter().map(|(c, _)| u64::from(*c)).sum()
    }
}

/// One decoded active data segment.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DecodedDataSegment {
    /// The segment's constant byte offset in memory 0.
    pub offset: i32,
    /// Its byte length.
    pub len: usize,
}

/// A decoded wasm module: exactly the structure the memory / call-ABI families
/// state obligations over.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct DecodedModule {
    /// Type section (id 1).
    pub types: Vec<DecodedFuncType>,
    /// Import section (id 2), in appearance order.
    pub imports: Vec<DecodedImport>,
    /// Function section (id 3): type index per DEFINED function.
    pub defined_func_types: Vec<u32>,
    /// Table section (id 4): the minimum size of table 0, when one is defined.
    pub table_min: Option<u32>,
    /// Whether the module DEFINES a table (as opposed to importing one).
    pub defines_table: bool,
    /// Memory section (id 5): the minimum page count of a DEFINED memory.
    pub memory_min_pages: Option<u32>,
    /// Global section (id 6): DEFINED globals only.
    pub globals: Vec<DecodedGlobal>,
    /// Export section (id 7).
    pub exports: Vec<DecodedExport>,
    /// Element section (id 9).
    pub elements: Vec<DecodedElemSegment>,
    /// Code section (id 10), one entry per DEFINED function.
    pub bodies: Vec<DecodedBody>,
    /// Data section (id 11).
    pub data: Vec<DecodedDataSegment>,
    /// Section ids seen, in order.
    pub section_order: Vec<u8>,
}

impl DecodedModule {
    /// Number of imported functions — the base of the DEFINED function index
    /// space, and the number every `call` target must be read against.
    pub fn func_import_count(&self) -> u32 {
        self.imports
            .iter()
            .filter(|i| matches!(i.kind, DecodedImportKind::Func(_)))
            .count() as u32
    }

    /// Number of imported globals — the base of the DEFINED global index space.
    pub fn global_import_count(&self) -> u32 {
        self.imports
            .iter()
            .filter(|i| matches!(i.kind, DecodedImportKind::Global { .. }))
            .count() as u32
    }

    /// Total size of the function index space.
    pub fn func_count(&self) -> u32 {
        self.func_import_count() + self.defined_func_types.len() as u32
    }

    /// Whether the module imports a memory.
    pub fn imports_memory(&self) -> bool {
        self.imports
            .iter()
            .any(|i| matches!(i.kind, DecodedImportKind::Memory))
    }

    /// The imported functions, in index order.
    pub fn func_imports(&self) -> Vec<&DecodedImport> {
        self.imports
            .iter()
            .filter(|i| matches!(i.kind, DecodedImportKind::Func(_)))
            .collect()
    }

    /// The TYPE a function index denotes, resolved through the import section
    /// and then the function section — the resolution a `call` target needs and
    /// the one an import-shift bug gets wrong.
    pub fn type_of_func(&self, func_idx: u32) -> Option<&DecodedFuncType> {
        let n = self.func_import_count();
        let type_idx = if func_idx < n {
            match self.func_imports().get(func_idx as usize)?.kind {
                DecodedImportKind::Func(t) => t,
                _ => return None,
            }
        } else {
            *self.defined_func_types.get((func_idx - n) as usize)?
        };
        self.types.get(type_idx as usize)
    }
}

/// Decode a complete wasm module. Fails closed on anything unrecognized.
pub fn decode_module(bytes: &[u8]) -> Result<DecodedModule, AbiDecodeError> {
    let mut c = Cur::new(bytes);
    let magic = c.take(4, "magic")?;
    let version = c.take(4, "version")?;
    if magic != [0x00, 0x61, 0x73, 0x6d] || version != [0x01, 0x00, 0x00, 0x00] {
        return Err(AbiDecodeError::BadHeader);
    }
    let mut m = DecodedModule::default();
    while !c.done() {
        let id = c.byte("section id")?;
        let size = c.uleb32("section size")? as usize;
        let body = c.take(size, "section body")?;
        m.section_order.push(id);
        let mut s = Cur::new(body);
        match id {
            0 => {} // custom section: not emitted, ignored by the format
            1 => {
                let n = s.uleb32("type count")?;
                for _ in 0..n {
                    if s.byte("functype tag")? != 0x60 {
                        return Err(AbiDecodeError::Malformed(
                            "type entry is not a functype (0x60)".to_string(),
                        ));
                    }
                    let np = s.uleb32("param count")?;
                    let params = s.take(np as usize, "param types")?.to_vec();
                    let nr = s.uleb32("result count")?;
                    let results = s.take(nr as usize, "result types")?.to_vec();
                    m.types.push(DecodedFuncType { params, results });
                }
            }
            2 => {
                let n = s.uleb32("import count")?;
                for _ in 0..n {
                    let module = s.name()?;
                    let name = s.name()?;
                    let kind = match s.byte("importdesc")? {
                        0x00 => DecodedImportKind::Func(s.uleb32("import type index")?),
                        0x01 => {
                            let _et = s.byte("import table elemtype")?;
                            read_limits(&mut s)?;
                            DecodedImportKind::Table
                        }
                        0x02 => {
                            read_limits(&mut s)?;
                            DecodedImportKind::Memory
                        }
                        0x03 => {
                            let ty = s.byte("import global type")?;
                            let mutable = s.byte("import global mut")? != 0;
                            DecodedImportKind::Global { ty, mutable }
                        }
                        other => {
                            return Err(AbiDecodeError::Malformed(format!(
                                "importdesc byte 0x{other:02x}"
                            )));
                        }
                    };
                    m.imports.push(DecodedImport { module, name, kind });
                }
            }
            3 => {
                let n = s.uleb32("function count")?;
                for _ in 0..n {
                    m.defined_func_types.push(s.uleb32("function type index")?);
                }
            }
            4 => {
                let n = s.uleb32("table count")?;
                for _ in 0..n {
                    let _elem = s.byte("table elemtype")?;
                    let (min, _max) = read_limits(&mut s)?;
                    if m.table_min.is_none() {
                        m.table_min = Some(min);
                        m.defines_table = true;
                    }
                }
            }
            5 => {
                let n = s.uleb32("memory count")?;
                for _ in 0..n {
                    let (min, _max) = read_limits(&mut s)?;
                    if m.memory_min_pages.is_none() {
                        m.memory_min_pages = Some(min);
                    }
                }
            }
            6 => {
                let n = s.uleb32("global count")?;
                for _ in 0..n {
                    let ty = s.byte("global type")?;
                    let mutable = s.byte("global mut")? != 0;
                    let init = read_const_expr(&mut s)?;
                    m.globals.push(DecodedGlobal { ty, mutable, init });
                }
            }
            7 => {
                let n = s.uleb32("export count")?;
                for _ in 0..n {
                    let name = s.name()?;
                    let kind = s.byte("export kind")?;
                    let index = s.uleb32("export index")?;
                    m.exports.push(DecodedExport { name, kind, index });
                }
            }
            8 => {
                let _ = s.uleb32("start function")?;
            }
            9 => {
                let n = s.uleb32("element segment count")?;
                for _ in 0..n {
                    let flags = s.uleb32("element flags")?;
                    if flags != 0 {
                        return Err(AbiDecodeError::Malformed(format!(
                            "element segment flags {flags} (only the active, table-0 form is \
                             modeled)"
                        )));
                    }
                    let offset = match read_const_expr(&mut s)? {
                        DecodedInit::I32(v) => v,
                        other => {
                            return Err(AbiDecodeError::Malformed(format!(
                                "element segment offset {other:?} is not an i32 constant"
                            )));
                        }
                    };
                    let count = s.uleb32("element count")?;
                    let mut funcs = Vec::with_capacity(count as usize);
                    for _ in 0..count {
                        funcs.push(s.uleb32("element func index")?);
                    }
                    m.elements.push(DecodedElemSegment {
                        table: 0,
                        offset,
                        funcs,
                    });
                }
            }
            10 => {
                let n = s.uleb32("code entry count")?;
                for _ in 0..n {
                    let size = s.uleb32("code entry size")? as usize;
                    let entry = s.take(size, "code entry")?;
                    let mut e = Cur::new(entry);
                    let runs = e.uleb32("local run count")?;
                    let mut local_runs = Vec::with_capacity(runs as usize);
                    for _ in 0..runs {
                        let count = e.uleb32("local run count")?;
                        let ty = e.byte("local run type")?;
                        local_runs.push((count, ty));
                    }
                    m.bodies.push(DecodedBody {
                        local_runs,
                        code: entry[e.p..].to_vec(),
                    });
                }
            }
            11 => {
                let n = s.uleb32("data segment count")?;
                for _ in 0..n {
                    let kind = s.uleb32("data segment kind")?;
                    if kind != 0 {
                        return Err(AbiDecodeError::Malformed(format!(
                            "data segment kind {kind} (only the active, memory-0 form is modeled)"
                        )));
                    }
                    let offset = match read_const_expr(&mut s)? {
                        DecodedInit::I32(v) => v,
                        other => {
                            return Err(AbiDecodeError::Malformed(format!(
                                "data segment offset {other:?} is not an i32 constant"
                            )));
                        }
                    };
                    let len = s.uleb32("data byte count")? as usize;
                    let _ = s.take(len, "data bytes")?;
                    m.data.push(DecodedDataSegment { offset, len });
                }
            }
            12 => {
                let _ = s.uleb32("datacount")?;
            }
            other => return Err(AbiDecodeError::UnknownSection(other)),
        }
        if !s.done() {
            return Err(AbiDecodeError::Malformed(format!(
                "section {id} has {} trailing byte(s)",
                s.b.len() - s.p
            )));
        }
    }
    Ok(m)
}

fn read_limits(c: &mut Cur<'_>) -> Result<(u32, Option<u32>), AbiDecodeError> {
    let flag = c.byte("limits flag")?;
    let min = c.uleb32("limits min")?;
    let max = match flag {
        0x00 => None,
        0x01 => Some(c.uleb32("limits max")?),
        other => {
            return Err(AbiDecodeError::Malformed(format!(
                "limits flag 0x{other:02x}"
            )));
        }
    };
    Ok((min, max))
}

fn read_const_expr(c: &mut Cur<'_>) -> Result<DecodedInit, AbiDecodeError> {
    let init = match c.byte("const expr opcode")? {
        0x41 => DecodedInit::I32(i32::try_from(c.sleb64("i32.const")?).map_err(|_| {
            AbiDecodeError::Malformed("i32.const payload does not fit in i32".to_string())
        })?),
        0x42 => DecodedInit::I64(c.sleb64("i64.const")?),
        0x23 => DecodedInit::GlobalGet(c.uleb32("global.get index")?),
        other => {
            return Err(AbiDecodeError::Malformed(format!(
                "constant expression opcode 0x{other:02x}"
            )));
        }
    };
    if c.byte("const expr end")? != 0x0b {
        return Err(AbiDecodeError::Malformed(
            "constant expression is not terminated by `end`".to_string(),
        ));
    }
    Ok(init)
}

// ---------------------------------------------------------------------------
// The instruction walker
// ---------------------------------------------------------------------------

/// The immediate operand(s) of a decoded instruction.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Imm {
    /// No immediate.
    None,
    /// A `blocktype` byte.
    BlockType(u8),
    /// A single index immediate (local / global / label / func).
    Idx(u32),
    /// A memory-access `memarg`: alignment exponent and static offset.
    Memarg {
        /// Alignment exponent (advisory).
        align: u32,
        /// Static byte offset.
        offset: u32,
    },
    /// `call_indirect`: the declared type index and the table index.
    CallIndirect {
        /// Type-section index of the declared signature.
        type_idx: u32,
        /// Table index (0 in the MVP).
        table: u32,
    },
    /// A single-byte memory index (`memory.size` / `memory.grow`).
    MemIdx(u8),
    /// `i32.const` payload.
    I32(i32),
    /// `i64.const` payload.
    I64(i64),
    /// A raw IEEE-754 constant payload.
    FpBits(Vec<u8>),
    /// `br_table`: the label vector and the default label.
    BrTable {
        /// Label indices, in order.
        targets: Vec<u32>,
        /// The default label.
        default: u32,
    },
    /// A `0xfc`-prefixed instruction's sub-index.
    Fc(u32),
}

/// One decoded instruction: its byte offset within the body, its opcode byte
/// and its immediate.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DecodedInst {
    /// Byte offset of the opcode within the code body.
    pub at: usize,
    /// The opcode byte.
    pub op: u8,
    /// Its immediate.
    pub imm: Imm,
}

/// Decode a function body's instruction stream.
///
/// FAILS CLOSED on an unrecognized opcode: an unknown opcode has an unknown
/// immediate length, so continuing would mis-decode every byte after it and
/// could silently turn a real instruction into a matched "window".
pub fn decode_insts(code: &[u8]) -> Result<Vec<DecodedInst>, AbiDecodeError> {
    match decode_insts_until_unknown(code) {
        (insts, None) => Ok(insts),
        (_, Some(e)) => Err(e),
    }
}

/// [`decode_insts`], also returning the instructions decoded before the first
/// error, and that error (`None` when the whole body decodes).
pub fn decode_insts_until_unknown(code: &[u8]) -> (Vec<DecodedInst>, Option<AbiDecodeError>) {
    let mut out = Vec::new();
    match decode_insts_into(code, &mut out) {
        Ok(()) => (out, None),
        Err(e) => (out, Some(e)),
    }
}

fn decode_insts_into(code: &[u8], out: &mut Vec<DecodedInst>) -> Result<(), AbiDecodeError> {
    let mut c = Cur::new(code);
    while !c.done() {
        let at = c.p;
        let op = c.byte("opcode")?;
        let imm = match op {
            // Control, no immediate.
            0x00 | 0x01 | 0x05 | 0x0b | 0x0f | 0x1a | 0x1b => Imm::None,
            0x02..=0x04 => Imm::BlockType(c.byte("blocktype")?),
            0x0c | 0x0d => Imm::Idx(c.uleb32("label index")?),
            0x0e => {
                let n = c.uleb32("br_table count")?;
                let mut targets = Vec::with_capacity(n as usize);
                for _ in 0..n {
                    targets.push(c.uleb32("br_table label")?);
                }
                let default = c.uleb32("br_table default")?;
                Imm::BrTable { targets, default }
            }
            0x10 => Imm::Idx(c.uleb32("call target")?),
            0x11 => Imm::CallIndirect {
                type_idx: c.uleb32("call_indirect type")?,
                table: c.uleb32("call_indirect table")?,
            },
            0x20..=0x24 => Imm::Idx(c.uleb32("variable index")?),
            0x28..=0x3e => Imm::Memarg {
                align: c.uleb32("memarg align")?,
                offset: c.uleb32("memarg offset")?,
            },
            0x3f | 0x40 => Imm::MemIdx(c.byte("memory index")?),
            0x41 => Imm::I32(i32::try_from(c.sleb64("i32.const")?).map_err(|_| {
                AbiDecodeError::Malformed("i32.const payload does not fit in i32".to_string())
            })?),
            0x42 => Imm::I64(c.sleb64("i64.const")?),
            0x43 => Imm::FpBits(c.take(4, "f32.const")?.to_vec()),
            0x44 => Imm::FpBits(c.take(8, "f64.const")?.to_vec()),
            // Numeric / comparison / conversion: no immediate.
            0x45..=0xc4 => Imm::None,
            0xfc => {
                let sub = c.uleb32("0xfc sub-opcode")?;
                match sub {
                    // The saturating truncations carry no further immediate.
                    0..=7 => {}
                    // memory.copy: destination and source memory index bytes.
                    10 => {
                        c.byte("memory.copy destination memory")?;
                        c.byte("memory.copy source memory")?;
                    }
                    // memory.fill: the memory index byte.
                    11 => {
                        c.byte("memory.fill memory")?;
                    }
                    // Anything else has an immediate this walker does not model.
                    _ => return Err(AbiDecodeError::UnknownOpcode { at, opcode: 0xfc }),
                }
                Imm::Fc(sub)
            }
            other => return Err(AbiDecodeError::UnknownOpcode { at, opcode: other }),
        };
        out.push(DecodedInst { at, op, imm });
    }
    Ok(())
}

/// The index immediate of an instruction, or `None` when it carries another
/// immediate shape.
fn idx_of(i: &DecodedInst) -> Option<u32> {
    match i.imm {
        Imm::Idx(v) => Some(v),
        _ => None,
    }
}

// wasm opcode bytes this module names. Decoded, never emitted.
const OP_LOCAL_GET: u8 = 0x20;
const OP_LOCAL_SET: u8 = 0x21;
const OP_LOCAL_TEE: u8 = 0x22;
const OP_GLOBAL_GET: u8 = 0x23;
const OP_GLOBAL_SET: u8 = 0x24;
const OP_DROP: u8 = 0x1a;
const OP_RETURN: u8 = 0x0f;
const OP_CALL: u8 = 0x10;
const OP_CALL_INDIRECT: u8 = 0x11;
const OP_I32_CONST: u8 = 0x41;
const VT_I32: u8 = 0x7f;
const VT_I64: u8 = 0x7e;
const VT_F32: u8 = 0x7d;
const VT_F64: u8 = 0x7c;

/// Table-mutating and table-reading instructions. None of them may appear if
/// "element `i + 1` is function `i`" is to hold for the instance's lifetime.
///
/// `table.set` is the single byte 0x26; `table.init` / `elem.drop` /
/// `table.copy` / `table.grow` / `table.size` / `table.fill` are the
/// `0xfc`-prefixed sub-opcodes 12..=17 (`table.size` is not itself mutating —
/// including it is deliberately conservative).
///
/// Both arms are DEFENSIVE rather than load-bearing today: 0x25 / 0x26 and the
/// `0xfc` sub-opcodes 12..=17 are outside [`decode_insts`]'s modeled surface
/// (it decodes only the saturating truncations 0..=7 and `memory.copy` /
/// `memory.fill`, whose memory-index bytes it consumes), so a body containing
/// one fails the instruction walk outright and the whole function is REFUSED. Failing
/// closed is strictly stronger than flagging, and this predicate stays so the
/// property is stated where the check lives if the walker ever learns them.
fn is_table_mutating(i: &DecodedInst) -> bool {
    match (i.op, &i.imm) {
        (0x26, _) => true,
        (0xfc, Imm::Fc(sub)) => matches!(sub, 12..=17),
        _ => false,
    }
}

// ===========================================================================
// The INTENDED model — built from trust-ir, independently of the backend
// ===========================================================================

/// A failure to build the intended (source-side) model from trust-ir.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AbiModelError {
    /// A trust-ir type with no wasm value type.
    UnsupportedType(String),
    /// A trust-ir type with no byte size.
    NoLayout(String),
    /// A signature or callee the module does not resolve.
    Unresolved(String),
    /// A construct outside this family's accepted input.
    Unsupported(String),
}

impl std::fmt::Display for AbiModelError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            AbiModelError::UnsupportedType(m) => write!(f, "unsupported type: {m}"),
            AbiModelError::NoLayout(m) => write!(f, "no layout: {m}"),
            AbiModelError::Unresolved(m) => write!(f, "unresolved: {m}"),
            AbiModelError::Unsupported(m) => write!(f, "unsupported: {m}"),
        }
    }
}

/// The wasm valtype BYTE a trust-ir type is carried in.
///
/// Written from the wasm32 target shape rather than mirrored from the backend:
/// every integer of 32 bits or fewer, every boolean and every pointer rides in
/// an `i32` (wasm32 addresses are 32-bit); 64-bit integers ride in an `i64`;
/// floats keep their width. Fails closed for everything else, which is exactly
/// the set the wasm lane refuses at lowering.
pub fn valtype_byte(ty: &Ty) -> Result<u8, AbiModelError> {
    Ok(match ty {
        Ty::I8 | Ty::U8 | Ty::I16 | Ty::U16 | Ty::I32 | Ty::U32 | Ty::Bool => VT_I32,
        Ty::I64 | Ty::U64 => VT_I64,
        Ty::F32 => VT_F32,
        Ty::F64 => VT_F64,
        Ty::Ptr | Ty::PtrConst(_) | Ty::PtrMut(_) | Ty::Ref(_) | Ty::RefMut(_) | Ty::Rc(_) => {
            VT_I32
        }
        other => return Err(AbiModelError::UnsupportedType(format!("{other:?}"))),
    })
}

fn func_type_bytes(ft: &FuncTy) -> Result<DecodedFuncType, AbiModelError> {
    Ok(DecodedFuncType {
        params: ft
            .params
            .iter()
            .map(valtype_byte)
            .collect::<Result<_, _>>()?,
        results: ft
            .returns
            .iter()
            .map(valtype_byte)
            .collect::<Result<_, _>>()?,
    })
}

/// One intended frame slot: the alloca's byte size and the byte offset the
/// documented layout rule assigns it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct IntendedSlot {
    /// Byte size of the allocated type.
    pub size: u32,
    /// Byte offset within the frame.
    pub offset: u32,
}

/// The intended shadow-stack frame of one function.
///
/// # Where the layout rule comes from
///
/// The rule is the one written down normatively in
/// `crates/trust-cg-codegen/src/wasm/OWNERSHIP.md` §1.4 ("The frame, exactly"):
/// every `Alloca` gets a byte offset `off` with `0 <= off < F` and
/// `off = 0 (mod 8)`, `F = align_up(total, 8)`, frames grow DOWN and occupy
/// `[SP_new, SP_old)`, and an alloca's address is `frame_base + off`. The sizes
/// come from trust-ir's own layout engine.
///
/// Said plainly, because it bounds what the refinement buys: the OFFSET-EQUALITY
/// obligation refines the emitted bytes against that documented rule, so a bug
/// shared between the document and the implementation of the document is
/// outside this evidence. The obligations that do NOT depend on the rule at all
/// — containment in `[frame_base, SP_old)`, pairwise non-overlap, downward
/// growth, and restoration on normal return — are stated over the DECODED
/// offsets, and those hold or fail regardless of what layout algorithm produced
/// them.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct IntendedFrame {
    /// The slots, in trust-ir order of appearance.
    pub slots: Vec<IntendedSlot>,
    /// The frame size in bytes; `0` when the function has no frame.
    pub frame_size: u32,
}

/// One intended direct call: the wasm function index the target must resolve
/// to, plus the signature that index must denote.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IntendedCall {
    /// Name of the callee, for diagnostics.
    pub callee: String,
    /// The import-shifted wasm function index.
    pub target: u32,
    /// The callee's signature, as wasm valtype bytes.
    pub sig: DecodedFuncType,
}

/// One intended indirect call: the signature the call site declares, the
/// trust-ir block it sits in, and the function its callee names when the
/// callee is a function-pointer constant.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IntendedIndirect {
    /// The declared signature, as wasm valtype bytes.
    pub sig: DecodedFuncType,
    /// The ordinal of the trust-ir block holding the call.
    pub block: usize,
    /// The import-shifted wasm function index the callee's pointer constant
    /// names (followed through `Copy` and `reify_fn_pointer`); `None` for a
    /// dynamic callee.
    pub const_callee: Option<u32>,
}

/// The first table element a closed module's element segment fills. Element 0
/// stays the null funcref, so the null pointer (0) is never the address of a
/// function and a `call_indirect` through it traps: a function pointer is
/// `funcidx + CLOSED_TABLE_BASE`. This is the convention `wasm-ld` applies to a
/// linked module (its default `--table-base` is 1), restated here rather than
/// imported from the backend this family checks.
pub const CLOSED_TABLE_BASE: u32 = 1;

/// One intended function-pointer constant: the wasm function index it names
/// (its table index is that plus [`CLOSED_TABLE_BASE`]).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IntendedFuncPtr {
    /// Name of the pointee, for diagnostics.
    pub pointee: String,
    /// The import-shifted wasm function index.
    pub target: u32,
}

/// The intended model of one DEFINED function.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IntendedFunction {
    /// trust-ir name (also the export name).
    pub name: String,
    /// The import-shifted wasm function index.
    pub index: u32,
    /// Its signature, as wasm valtype bytes.
    pub sig: DecodedFuncType,
    /// Its intended frame.
    pub frame: IntendedFrame,
    /// Its direct calls, in trust-ir order.
    pub calls: Vec<IntendedCall>,
    /// Its indirect calls, in trust-ir order.
    pub indirects: Vec<IntendedIndirect>,
    /// Its function-pointer constants, in trust-ir order.
    pub func_ptrs: Vec<IntendedFuncPtr>,
    /// The import-shifted wasm function index of every `call_indirect` whose
    /// callee is a function-pointer constant (followed through `Copy` and
    /// `reify_fn_pointer`), in trust-ir order.
    pub const_callees: Vec<u32>,
    /// Function-pointer constants that reach anything OTHER than the callee
    /// operand of a `call_indirect` (an argument, a store, a block argument, a
    /// return, a select): this family cannot bind such a constant to the table
    /// element it names, so the function is refused rather than credited.
    pub escaping_func_ptrs: Vec<String>,
    /// Whether the function returns normally somewhere (so an epilogue is due).
    pub has_return: bool,
}

/// The intended model of one DECLARED (body-less) function — a wasm import.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IntendedImport {
    /// trust-ir name (also the import member name).
    pub name: String,
    /// Its wasm function index: declaration ordinal, in the LOW index space.
    pub index: u32,
    /// Its signature, as wasm valtype bytes.
    pub sig: DecodedFuncType,
}

/// The intended model of a whole trust-ir module under the wasm32 lane.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct IntendedModule {
    /// Declarations, in trust-ir order: wasm function indices `0..N`.
    pub imports: Vec<IntendedImport>,
    /// Definitions, in trust-ir order: wasm function indices `N..N+M`.
    pub defined: Vec<IntendedFunction>,
    /// Whether any function needs the funcref table.
    pub needs_table: bool,
    /// Whether any function needs a shadow-stack frame.
    pub needs_frame: bool,
}

/// Round `n` up to the next multiple of `align` (a power of two).
fn align_up(n: u32, align: u32) -> u32 {
    n.div_ceil(align).saturating_mul(align)
}

fn size_of(module: &Module, ty: &Ty) -> Result<u32, AbiModelError> {
    let shape = module
        .ty_layout_shape(ty)
        .map_err(|e| AbiModelError::NoLayout(format!("{ty:?}: {e:?}")))?;
    let bytes = shape
        .size_bytes()
        .ok_or_else(|| AbiModelError::NoLayout(format!("{ty:?} has no byte size")))?;
    u32::try_from(bytes).map_err(|_| AbiModelError::NoLayout(format!("{ty:?} is too large")))
}

/// Build the intended frame of `func` from the documented layout rule.
pub fn intended_frame(func: &Function, module: &Module) -> Result<IntendedFrame, AbiModelError> {
    let mut slots = Vec::new();
    let mut offset: u32 = 0;
    for node in func.blocks.iter().flat_map(|b| &b.body) {
        if let Inst::Alloca { ty, count, .. } = &node.inst {
            if count.is_some() {
                return Err(AbiModelError::Unsupported(format!(
                    "`{}` has a dynamic-count Alloca; the wasm lane refuses it at lowering",
                    func.name
                )));
            }
            let size = size_of(module, ty)?;
            offset = align_up(offset, 8);
            slots.push(IntendedSlot { size, offset });
            offset += size;
        }
    }
    let frame_size = if slots.is_empty() {
        0
    } else {
        align_up(offset, 8)
    };
    Ok(IntendedFrame { slots, frame_size })
}

fn is_declaration(f: &Function) -> bool {
    f.blocks.is_empty()
}

fn sig_of_func(module: &Module, id: FuncId) -> Result<(String, DecodedFuncType), AbiModelError> {
    let f = module
        .function_by_id(id)
        .ok_or_else(|| AbiModelError::Unresolved(format!("{id:?}")))?;
    let ft = module
        .func_type(f.ty)
        .ok_or_else(|| AbiModelError::Unresolved(format!("signature of `{}`", f.name)))?;
    Ok((f.name.clone(), func_type_bytes(ft)?))
}

fn sig_of_id(module: &Module, id: FuncTyId) -> Result<DecodedFuncType, AbiModelError> {
    let ft = module
        .func_type(id)
        .ok_or_else(|| AbiModelError::Unresolved(format!("{id:?}")))?;
    func_type_bytes(ft)
}

fn call_unwind_boundary_refusal(construct: &str, function: &str) -> AbiModelError {
    AbiModelError::Unsupported(format!(
        "{construct} in `{function}`: a non-propagating call boundary (trust-ir v53) \
         requires host-unwind semantics; this ABI model does not model it"
    ))
}

/// The public model entry does not run compiler admission. Inspect every
/// stored node before extracting frames, call sites or function-pointer uses:
/// omitting a void or unreachable boundary call would erase its contract.
fn reject_call_unwind_boundaries(module: &Module) -> Result<(), AbiModelError> {
    for function in &module.functions {
        for node in function.blocks.iter().flat_map(|block| &block.body) {
            match &node.inst {
                Inst::CallCannotUnwind { .. } => {
                    return Err(call_unwind_boundary_refusal(
                        "Inst::CallCannotUnwind",
                        &function.name,
                    ));
                }
                Inst::CallIndirectCannotUnwind { .. } => {
                    return Err(call_unwind_boundary_refusal(
                        "Inst::CallIndirectCannotUnwind",
                        &function.name,
                    ));
                }
                // trust-ir v55 / v56 (amendment D): the unwinding twins of a
                // drop (a call of its type's glue) and of an indirect call.
                // Each is a call site with an unwind edge this model does not
                // model; extracting none for it would erase the call.
                Inst::DropInvoke { .. } | Inst::InvokeIndirect { .. } => {
                    let construct = if matches!(node.inst, Inst::DropInvoke { .. }) {
                        "Inst::DropInvoke"
                    } else {
                        "Inst::InvokeIndirect"
                    };
                    return Err(AbiModelError::Unsupported(format!(
                        "{construct} in `{}`: an unwinding call (trust-ir v55/v56) requires \
                         host-unwind semantics; this ABI model does not model it",
                        function.name
                    )));
                }
                _ => {}
            }
        }
    }
    Ok(())
}

/// Build the intended model of a whole trust-ir module.
///
/// The index assignment is the P2 rule stated in OWNERSHIP.md §4.1 / §7 item 2
/// and re-derived here from the spec's index-space rule: imported functions
/// occupy the LOW function index space `0..N` in declaration order, and defined
/// functions follow at `N + ordinal`. Every `call` target, function-pointer
/// constant, table element and export shifts with them.
pub fn intended_module(module: &Module) -> Result<IntendedModule, AbiModelError> {
    reject_call_unwind_boundaries(module)?;
    let mut out = IntendedModule::default();
    let mut index_of: BTreeMap<u32, u32> = BTreeMap::new();

    for (ordinal, f) in module
        .functions
        .iter()
        .filter(|f| is_declaration(f))
        .enumerate()
    {
        let (name, sig) = sig_of_func(module, f.id)?;
        let index = ordinal as u32;
        index_of.insert(f.id.index(), index);
        out.imports.push(IntendedImport { name, index, sig });
    }
    let import_base = out.imports.len() as u32;
    for (ordinal, f) in module
        .functions
        .iter()
        .filter(|f| !is_declaration(f))
        .enumerate()
    {
        index_of.insert(f.id.index(), import_base + ordinal as u32);
    }

    for (ordinal, func) in module
        .functions
        .iter()
        .filter(|f| !is_declaration(f))
        .enumerate()
    {
        let (name, sig) = sig_of_func(module, func.id)?;
        let frame = intended_frame(func, module)?;
        let mut calls = Vec::new();
        let mut indirects = Vec::new();
        let mut func_ptrs = Vec::new();
        let (site_callees, escaping_func_ptrs) = function_pointer_uses(module, func, &index_of)?;
        let const_callees: Vec<u32> = site_callees.iter().flatten().copied().collect();
        let mut has_return = false;
        for (block_ordinal, block) in func.blocks.iter().enumerate() {
            for node in &block.body {
                match &node.inst {
                    Inst::CallCannotUnwind { .. } => {
                        return Err(call_unwind_boundary_refusal(
                            "Inst::CallCannotUnwind",
                            &func.name,
                        ));
                    }
                    Inst::CallIndirectCannotUnwind { .. } => {
                        return Err(call_unwind_boundary_refusal(
                            "Inst::CallIndirectCannotUnwind",
                            &func.name,
                        ));
                    }
                    Inst::Call { callee, .. } => {
                        let (callee_name, csig) = sig_of_func(module, *callee)?;
                        let target = *index_of.get(&callee.index()).ok_or_else(|| {
                            AbiModelError::Unresolved(format!("call target `{callee_name}`"))
                        })?;
                        calls.push(IntendedCall {
                            callee: callee_name,
                            target,
                            sig: csig,
                        });
                    }
                    Inst::CallIndirect { sig, .. } => {
                        // `function_pointer_uses` visits the call sites in
                        // this same order.
                        let const_callee = *site_callees.get(indirects.len()).ok_or_else(|| {
                            AbiModelError::Unsupported(
                                "call_indirect sites and their callees disagree in number"
                                    .to_string(),
                            )
                        })?;
                        indirects.push(IntendedIndirect {
                            sig: sig_of_id(module, *sig)?,
                            block: block_ordinal,
                            const_callee,
                        });
                    }
                    Inst::Const {
                        value: Constant::FnDef(id),
                        ..
                    } => {
                        let (pointee, _) = sig_of_func(module, *id)?;
                        let target = *index_of.get(&id.index()).ok_or_else(|| {
                            AbiModelError::Unresolved(format!("function pointer `{pointee}`"))
                        })?;
                        func_ptrs.push(IntendedFuncPtr { pointee, target });
                    }
                    _ => {}
                }
            }
            if matches!(
                block.terminator().map(|n| &n.inst),
                Some(Inst::Return { .. })
            ) {
                has_return = true;
            }
        }
        out.needs_table |= !indirects.is_empty() || !func_ptrs.is_empty();
        out.needs_frame |= frame.frame_size > 0;
        out.defined.push(IntendedFunction {
            name,
            index: import_base + ordinal as u32,
            sig,
            frame,
            calls,
            indirects,
            func_ptrs,
            const_callees,
            escaping_func_ptrs,
            has_return,
        });
    }
    Ok(out)
}

/// Where each function-pointer constant of `func` goes.
///
/// Returns, for every `call_indirect` in trust-ir order, the import-shifted
/// target its callee names when that callee is such a constant — followed
/// through `Copy` and `reify_fn_pointer`, the two value-preserving forms a
/// frontend puts between them — or `None` for a dynamic callee; and the names
/// of the constants that reach any other use.
fn function_pointer_uses(
    module: &Module,
    func: &Function,
    index_of: &BTreeMap<u32, u32>,
) -> Result<(Vec<Option<u32>>, Vec<String>), AbiModelError> {
    use trust_ir::{CastOp, ValueId};

    let nodes: Vec<&trust_ir::InstrNode> = func.blocks.iter().flat_map(|b| &b.body).collect();
    // The function-pointer constant each value carries, when it is one.
    let mut carries: BTreeMap<ValueId, FuncId> = BTreeMap::new();
    for node in &nodes {
        if let (
            Inst::Const {
                value: Constant::FnDef(id),
                ..
            },
            [r],
        ) = (&node.inst, node.results.as_slice())
        {
            carries.insert(*r, *id);
        }
    }
    // Propagate through the value-preserving forms (SSA: one pass per chain
    // link; the chain is at most as long as the body).
    loop {
        let before = carries.len();
        for node in &nodes {
            let src = match &node.inst {
                Inst::Copy { operand, .. } => Some(*operand),
                Inst::Cast {
                    op: CastOp::ReifyFnPointer,
                    operand,
                    ..
                } => Some(*operand),
                _ => None,
            };
            if let (Some(src), [r]) = (src, node.results.as_slice())
                && let Some(&id) = carries.get(&src)
            {
                carries.insert(*r, id);
            }
        }
        if carries.len() == before {
            break;
        }
    }
    let mut callees = Vec::new();
    let mut escaping = BTreeSet::new();
    for node in &nodes {
        let passes_through = matches!(
            node.inst,
            Inst::Copy { .. }
                | Inst::Cast {
                    op: CastOp::ReifyFnPointer,
                    ..
                }
        );
        match &node.inst {
            Inst::CallCannotUnwind { .. } => {
                return Err(call_unwind_boundary_refusal(
                    "Inst::CallCannotUnwind",
                    &func.name,
                ));
            }
            Inst::CallIndirectCannotUnwind { .. } => {
                return Err(call_unwind_boundary_refusal(
                    "Inst::CallIndirectCannotUnwind",
                    &func.name,
                ));
            }
            Inst::CallIndirect { callee, args, .. } => {
                let mut target = None;
                if let Some(&id) = carries.get(callee) {
                    let (pointee, _) = sig_of_func(module, id)?;
                    target = Some(*index_of.get(&id.index()).ok_or_else(|| {
                        AbiModelError::Unresolved(format!("function pointer `{pointee}`"))
                    })?);
                }
                callees.push(target);
                for a in args {
                    if let Some(&id) = carries.get(a) {
                        escaping.insert(sig_of_func(module, id)?.0);
                    }
                }
            }
            _ if passes_through => {}
            inst => {
                let mut hit = Vec::new();
                inst.visit_value_operands(|v| {
                    if let Some(&id) = carries.get(&v) {
                        hit.push(id);
                    }
                });
                for id in hit {
                    escaping.insert(sig_of_func(module, id)?.0);
                }
            }
        }
    }
    Ok((callees, escaping.into_iter().collect()))
}

// ===========================================================================
// Symbolic execution of the DECODED instruction windows
// ===========================================================================

/// A symbolic machine state over the tiny opcode subset the prologue, alloca
/// and epilogue windows use. Anything else fails closed.
#[derive(Debug, Clone)]
struct SymState {
    stack: Vec<SmtExpr>,
    locals: BTreeMap<u32, SmtExpr>,
    globals: BTreeMap<u32, SmtExpr>,
    /// Number of function parameters — locals below this are the caller's
    /// values (symbolic); locals at or above it are wasm-zero-initialized.
    params: u32,
    /// Extra symbolic leaves the state created for parameter reads.
    extra_inputs: BTreeSet<u32>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum SymError {
    UnsupportedOpcode(u8),
    StackUnderflow(u8),
    BadImmediate(u8),
    UndefinedGlobal(u32),
}

impl SymState {
    fn new(params: u32, sp_global: u32, sp0: SmtExpr) -> Self {
        let mut globals = BTreeMap::new();
        globals.insert(sp_global, sp0);
        SymState {
            stack: Vec::new(),
            locals: BTreeMap::new(),
            globals,
            params,
            extra_inputs: BTreeSet::new(),
        }
    }

    fn read_local(&mut self, idx: u32) -> SmtExpr {
        if let Some(v) = self.locals.get(&idx) {
            return v.clone();
        }
        if idx < self.params {
            // A parameter carries the caller's value: a fresh symbolic leaf.
            self.extra_inputs.insert(idx);
            SmtExpr::var(format!("abi_param{idx}"), ADDR_BITS)
        } else {
            // The spec zero-initializes declared locals.
            SmtExpr::bv_const(0, ADDR_BITS)
        }
    }

    fn pop(&mut self, op: u8) -> Result<SmtExpr, SymError> {
        self.stack.pop().ok_or(SymError::StackUnderflow(op))
    }

    fn step(&mut self, i: &DecodedInst) -> Result<(), SymError> {
        let idx = || idx_of(i).ok_or(SymError::BadImmediate(i.op));
        match i.op {
            OP_LOCAL_GET => {
                let v = self.read_local(idx()?);
                self.stack.push(v);
            }
            OP_LOCAL_SET => {
                let v = self.pop(i.op)?;
                self.locals.insert(idx()?, v);
            }
            OP_LOCAL_TEE => {
                let v = self.pop(i.op)?;
                self.locals.insert(idx()?, v.clone());
                self.stack.push(v);
            }
            OP_GLOBAL_GET => {
                let g = idx()?;
                let v = self
                    .globals
                    .get(&g)
                    .cloned()
                    .ok_or(SymError::UndefinedGlobal(g))?;
                self.stack.push(v);
            }
            OP_GLOBAL_SET => {
                let v = self.pop(i.op)?;
                self.globals.insert(idx()?, v);
            }
            OP_I32_CONST => match i.imm {
                Imm::I32(v) => self
                    .stack
                    .push(SmtExpr::bv_const(u64::from(v as u32), ADDR_BITS)),
                _ => return Err(SymError::BadImmediate(i.op)),
            },
            OP_DROP => {
                self.pop(i.op)?;
            }
            // The i32 binary ALU the address arithmetic can use. A prologue or
            // alloca window that carries a DIFFERENT one of these still
            // executes — which is the point: the obligation then refutes,
            // rather than the matcher silently declining to build it.
            0x6a | 0x6b | 0x6c | 0x71 | 0x72 | 0x73 | 0x74 | 0x75 | 0x76 => {
                let b = self.pop(i.op)?;
                let a = self.pop(i.op)?;
                let r = match i.op {
                    0x6a => a.bvadd(b),
                    0x6b => a.bvsub(b),
                    0x6c => a.bvmul(b),
                    0x71 => a.bvand(b),
                    0x72 => a.bvor(b),
                    0x73 => a.bvxor(b),
                    0x74 => a.bvshl(b),
                    0x75 => a.bvashr(b),
                    _ => a.bvlshr(b),
                };
                self.stack.push(r);
            }
            other => return Err(SymError::UnsupportedOpcode(other)),
        }
        Ok(())
    }

    fn run(&mut self, insts: &[DecodedInst]) -> Result<(), SymError> {
        for i in insts {
            self.step(i)?;
        }
        Ok(())
    }
}

// ---------------------------------------------------------------------------
// Window recognition over the decoded body
// ---------------------------------------------------------------------------

/// The prologue window recovered from a decoded body.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DecodedPrologue {
    /// The global index the prologue READ (the shadow stack pointer).
    pub sp_global_read: u32,
    /// The local the caller's stack pointer was saved into.
    pub saved_local: u32,
    /// The local the new frame base was teed into.
    pub base_local: u32,
    /// The frame-size immediate found in the prologue.
    pub frame_size_imm: i32,
    /// The instruction window itself (7 instructions).
    pub window: Vec<DecodedInst>,
}

/// One alloca window recovered from a decoded body.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DecodedAlloca {
    /// The frame-relative offset immediate.
    pub offset_imm: i32,
    /// The local the resulting pointer was stored into.
    pub dst_local: u32,
    /// The instruction window itself (4 instructions).
    pub window: Vec<DecodedInst>,
}

/// Find the prologue window at the head of a decoded body.
///
/// The shape recognized is positional only — `global.get`, `local.set`, three
/// instructions of address arithmetic, `local.tee`, `global.set`. The ARITHMETIC
/// is not pattern-matched: whatever ALU opcode and whatever immediate are there
/// get symbolically executed, so a wrong opcode or a wrong frame size produces a
/// wrong machine-side expression and the obligation REFUTES, instead of the
/// matcher quietly declining and the row going uncredited.
pub fn find_prologue(insts: &[DecodedInst]) -> Option<DecodedPrologue> {
    if insts.len() < 7 {
        return None;
    }
    let w = &insts[..7];
    if w[0].op != OP_GLOBAL_GET
        || w[1].op != OP_LOCAL_SET
        || w[5].op != OP_LOCAL_TEE
        || w[6].op != OP_GLOBAL_SET
    {
        return None;
    }
    let frame_size_imm = match w[3].imm {
        Imm::I32(v) => v,
        _ => return None,
    };
    Some(DecodedPrologue {
        sp_global_read: idx_of(&w[0])?,
        saved_local: idx_of(&w[1])?,
        base_local: idx_of(&w[5])?,
        frame_size_imm,
        window: w.to_vec(),
    })
}

/// Find every alloca window in a decoded body: `local.get <frame base>;
/// i32.const <off>; <alu>; local.set <dst>`.
///
/// The ALU opcode is again taken as found, not matched, so an `i32.sub` where
/// an `i32.add` belongs is decoded and refuted rather than skipped.
pub fn find_allocas(insts: &[DecodedInst], base_local: u32) -> Vec<DecodedAlloca> {
    let mut out = Vec::new();
    let mut k = 0usize;
    while k + 4 <= insts.len() {
        let w = &insts[k..k + 4];
        let matches = w[0].op == OP_LOCAL_GET
            && idx_of(&w[0]) == Some(base_local)
            && w[1].op == OP_I32_CONST
            && w[3].op == OP_LOCAL_SET;
        if matches && let (Imm::I32(off), Some(dst)) = (w[1].imm.clone(), idx_of(&w[3])) {
            out.push(DecodedAlloca {
                offset_imm: off,
                dst_local: dst,
                window: w.to_vec(),
            });
            k += 4;
            continue;
        }
        k += 1;
    }
    out
}

/// Find every epilogue window: `local.get <saved>; global.set <g>`.
pub fn find_epilogues(insts: &[DecodedInst], saved_local: u32) -> Vec<Vec<DecodedInst>> {
    let mut out = Vec::new();
    for w in insts.windows(2) {
        if w[0].op == OP_LOCAL_GET && idx_of(&w[0]) == Some(saved_local) && w[1].op == OP_GLOBAL_SET
        {
            out.push(w.to_vec());
        }
    }
    out
}

/// Every `local.get`/`global.set` pair that writes SOMETHING into a global —
/// used to detect an epilogue that restores the wrong local.
fn find_global_sets(insts: &[DecodedInst]) -> Vec<(usize, u32)> {
    insts
        .iter()
        .enumerate()
        .filter(|(_, i)| i.op == OP_GLOBAL_SET)
        .filter_map(|(k, i)| idx_of(i).map(|g| (k, g)))
        .collect()
}

// ===========================================================================
// Family (2): the frame obligations
// ===========================================================================

fn recon(
    name: String,
    source: SmtExpr,
    machine: SmtExpr,
    inputs: Vec<(String, u32)>,
    preconditions: Vec<SmtExpr>,
    from: String,
) -> ProofObligation {
    ProofObligation {
        name,
        trust_ir_expr: source,
        aarch64_expr: machine,
        inputs,
        preconditions,
        fp_inputs: vec![],
        category: Some(TransvalCheckKind::InstructionLowering),
        machine_side_provenance: MachineSideProvenance::Reconstructed {
            from_opcode: from,
            arity: 1,
        },
    }
}

fn sp0() -> SmtExpr {
    SmtExpr::var("abi_sp0", ADDR_BITS)
}

/// The no-wrap window for a frame of `f` bytes: the entry stack pointer is at
/// least `f` (so `SP - f` does not wrap below zero) and at most `2^32-1-f` (so
/// no in-frame address wraps above the top). Every frame the backend emits is
/// tens of bytes, so this excludes a vanishing fraction of the 2^32 sample
/// space rather than making the obligation vacuous.
fn no_wrap(f: u32) -> Vec<SmtExpr> {
    let fc = SmtExpr::bv_const(u64::from(f), ADDR_BITS);
    vec![
        sp0().bvuge(fc),
        sp0().bvule(SmtExpr::bv_const(u64::from(u32::MAX - f), ADDR_BITS)),
    ]
}

fn inputs_for(state: &SymState) -> Vec<(String, u32)> {
    let mut v = vec![("abi_sp0".to_string(), ADDR_BITS)];
    for p in &state.extra_inputs {
        v.push((format!("abi_param{p}"), ADDR_BITS));
    }
    v
}

/// The SMT obligations of family (2) for ONE function: the frame arithmetic as
/// EMITTED, refined against the intended layout.
///
/// Returns an empty vector for a frameless function (no prologue, nothing to
/// state) and an error when the body cannot be decoded or the prologue cannot
/// be recognized while the intended model says a frame is due — fail closed, so
/// an unrecognized emission earns NO credit rather than silently passing.
pub fn frame_obligations(
    body: &DecodedBody,
    intended: &IntendedFunction,
) -> Result<Vec<ProofObligation>, String> {
    let insts = decode_insts(&body.code).map_err(|e| format!("`{}`: {e}", intended.name))?;
    if intended.frame.frame_size == 0 {
        return Ok(Vec::new());
    }
    let pro = find_prologue(&insts).ok_or_else(|| {
        format!(
            "`{}` needs a {}-byte frame but no prologue window was decoded at the head of its \
             body — NO CREDIT",
            intended.name, intended.frame.frame_size
        )
    })?;
    let allocas = find_allocas(&insts, pro.base_local);
    if allocas.len() != intended.frame.slots.len() {
        return Err(format!(
            "`{}`: decoded {} alloca window(s), the trust-ir function has {} — NO CREDIT",
            intended.name,
            allocas.len(),
            intended.frame.slots.len()
        ));
    }

    let params = intended.sig.params.len() as u32;
    let f = intended.frame.frame_size;
    let fc = SmtExpr::bv_const(u64::from(f), ADDR_BITS);
    let intended_base = sp0().bvsub(fc.clone());
    let mut out = Vec::new();

    // --- Run the prologue once; every later window resumes from this state. ---
    let mut after_prologue = SymState::new(params, pro.sp_global_read, sp0());
    after_prologue
        .run(&pro.window)
        .map_err(|e| format!("`{}` prologue symexec: {e:?}", intended.name))?;

    let published = after_prologue
        .globals
        .get(&pro.sp_global_read)
        .cloned()
        .ok_or_else(|| format!("`{}`: prologue left the read global unset", intended.name))?;
    let base = after_prologue
        .locals
        .get(&pro.base_local)
        .cloned()
        .ok_or_else(|| {
            format!(
                "`{}`: prologue left the frame-base local unset",
                intended.name
            )
        })?;
    let pro_inputs = inputs_for(&after_prologue);

    // F1a — the prologue PUBLISHES `SP - F` in the very global it read.
    // Refutes: a wrong ALU opcode, a wrong frame-size immediate, and a
    // `global.set` to a different global than the `global.get` read.
    out.push(recon(
        format!(
            "RECONSTRUCTED wasm `{}` prologue -> publishes SP - {f} into global {} (the one it \
             read)",
            intended.name, pro.sp_global_read
        ),
        intended_base.clone(),
        published,
        pro_inputs.clone(),
        no_wrap(f),
        format!("prologue @global {}", pro.sp_global_read),
    ));

    // F1b — the frame-base LOCAL holds the same new stack pointer.
    out.push(recon(
        format!(
            "RECONSTRUCTED wasm `{}` prologue -> frame-base local {} holds SP - {f}",
            intended.name, pro.base_local
        ),
        intended_base.clone(),
        base.clone(),
        pro_inputs.clone(),
        no_wrap(f),
        format!("prologue @local {}", pro.base_local),
    ));

    // F2 — frames grow DOWN: the new base is strictly below the caller's SP.
    // Stated over the DECODED arithmetic, so it holds for whatever the prologue
    // actually computed rather than for the rule it was supposed to follow.
    out.push(recon(
        format!(
            "RECONSTRUCTED wasm `{}` prologue -> the frame grows DOWN (base <u caller SP)",
            intended.name
        ),
        SmtExpr::bool_const(true),
        base.clone().bvult(sp0()),
        pro_inputs.clone(),
        no_wrap(f),
        "prologue growth direction".to_string(),
    ));

    // --- Per-alloca placement, containment, and pairwise non-overlap. ---
    let mut addrs: Vec<(usize, SmtExpr, u32)> = Vec::new();
    for (k, (dec, want)) in allocas.iter().zip(&intended.frame.slots).enumerate() {
        let mut st = after_prologue.clone();
        st.run(&dec.window)
            .map_err(|e| format!("`{}` alloca {k} symexec: {e:?}", intended.name))?;
        let addr =
            st.locals.get(&dec.dst_local).cloned().ok_or_else(|| {
                format!("`{}`: alloca {k} left its dst local unset", intended.name)
            })?;
        let ins = inputs_for(&st);

        // F3 — the emitted address is `frame_base + intended_offset`.
        out.push(recon(
            format!(
                "RECONSTRUCTED wasm `{}` alloca {k} -> frame_base + {} (intended slot offset)",
                intended.name, want.offset
            ),
            intended_base
                .clone()
                .bvadd(SmtExpr::bv_const(u64::from(want.offset), ADDR_BITS)),
            addr.clone(),
            ins.clone(),
            no_wrap(f),
            format!("alloca window -> local {}", dec.dst_local),
        ));

        // F4 — the slot lies WHOLLY inside the frame `[base, caller SP)`.
        // Independent of the layout rule: it is stated over the decoded address.
        let end = addr
            .clone()
            .bvadd(SmtExpr::bv_const(u64::from(want.size), ADDR_BITS));
        out.push(recon(
            format!(
                "RECONSTRUCTED wasm `{}` alloca {k} -> its {} byte(s) lie inside [frame_base, \
                 caller SP)",
                intended.name, want.size
            ),
            SmtExpr::bool_const(true),
            base.clone().bvule(addr.clone()).and_expr(end.bvule(sp0())),
            ins,
            no_wrap(f),
            format!("alloca window -> local {}", dec.dst_local),
        ));
        addrs.push((k, addr, want.size));
    }

    for (a, (j, aj, sj)) in addrs.iter().enumerate() {
        for (k, ak, sk) in addrs.iter().skip(a + 1) {
            let j_end = aj
                .clone()
                .bvadd(SmtExpr::bv_const(u64::from(*sj), ADDR_BITS));
            let k_end = ak
                .clone()
                .bvadd(SmtExpr::bv_const(u64::from(*sk), ADDR_BITS));
            // F5 — distinct allocas occupy DISJOINT byte ranges.
            out.push(recon(
                format!(
                    "RECONSTRUCTED wasm `{}` allocas {j} and {k} -> disjoint byte ranges",
                    intended.name
                ),
                SmtExpr::bool_const(true),
                j_end.bvule(ak.clone()).or_expr(k_end.bvule(aj.clone())),
                pro_inputs.clone(),
                no_wrap(f),
                "alloca windows (non-overlap)".to_string(),
            ));
        }
    }

    // --- F6: the epilogue restores the caller's stack pointer. ---
    //
    // Reconstructed by running the prologue and then the LAST global.set window
    // that precedes a `return`. A correct emission reconstructs to `SP0` on both
    // sides — non-vacuity comes from the machine side being the real decoded
    // window, exactly as for the reconstructed ALU obligations: restoring the
    // wrong local, or writing a different global, reconstructs to a different
    // expression and refutes.
    if intended.has_return {
        let restore = last_restore_window(&insts, pro.sp_global_read).ok_or_else(|| {
            format!(
                "`{}` returns normally but no `<something>; global.set {}` restore window \
                 precedes its `return` — NO CREDIT",
                intended.name, pro.sp_global_read
            )
        })?;
        let mut st = after_prologue.clone();
        st.run(&restore)
            .map_err(|e| format!("`{}` epilogue symexec: {e:?}", intended.name))?;
        let restored = st
            .globals
            .get(&pro.sp_global_read)
            .cloned()
            .ok_or_else(|| format!("`{}`: epilogue left the SP global unset", intended.name))?;
        out.push(recon(
            format!(
                "RECONSTRUCTED wasm `{}` epilogue -> restores the CALLER's stack pointer on \
                 normal return",
                intended.name
            ),
            sp0(),
            restored,
            inputs_for(&st),
            no_wrap(f),
            format!("epilogue @global {}", pro.sp_global_read),
        ));
    }

    Ok(out)
}

/// The last `global.set <sp>` window before the body's first `return`, together
/// with the single instruction that pushes its operand.
///
/// Deliberately NOT keyed on the saved-SP local: keying on it would make an
/// epilogue that restores the WRONG local simply fail to match, and an
/// unmatched window is silence, not a refutation. Taking whatever pushes the
/// value means the wrong local is decoded, executed, and REFUTED.
fn last_restore_window(insts: &[DecodedInst], sp_global: u32) -> Option<Vec<DecodedInst>> {
    let ret = insts.iter().position(|i| i.op == OP_RETURN)?;
    let (k, _) = find_global_sets(&insts[..ret])
        .into_iter()
        .rfind(|(_, g)| *g == sp_global)?;
    if k == 0 {
        return None;
    }
    Some(insts[k - 1..=k].to_vec())
}

// ===========================================================================
// Structural checks — family (3) plus the module-level index space
// ===========================================================================

/// One DECIDABLE structural equality over the decoded module.
///
/// These are not dressed as SMT obligations: "this call's target index resolves
/// to a function of the declared signature" is settled by decoding, and handing
/// it to a solver would add ceremony, not evidence. They are reported with
/// their own counts and their teeth are the byte-mutation guards.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AbiStructuralCheck {
    /// What is being asserted.
    pub name: String,
    /// Whether the decoded module satisfies it.
    pub ok: bool,
    /// The observed-vs-intended detail, always populated (also on success, so a
    /// report reads as evidence rather than as a tick).
    pub detail: String,
}

fn check(name: String, ok: bool, detail: String) -> AbiStructuralCheck {
    AbiStructuralCheck { name, ok, detail }
}

/// Structural checks over the whole module: the index spaces, the exports, the
/// funcref table, the memory, and the data segments.
pub fn module_structural_checks(
    dec: &DecodedModule,
    intended: &IntendedModule,
) -> Vec<AbiStructuralCheck> {
    let mut out = Vec::new();
    let n = dec.func_import_count();

    // S1 — the import count. Every `call` target's meaning depends on it.
    out.push(check(
        "func import count == trust-ir declaration count".to_string(),
        n as usize == intended.imports.len(),
        format!("decoded {n}, intended {}", intended.imports.len()),
    ));

    // S2 — each import, in the LOW index space, with its declared signature.
    let imports = dec.func_imports();
    for want in &intended.imports {
        let got = imports.get(want.index as usize);
        let ok = got.is_some_and(|i| {
            i.name == want.name && dec.type_of_func(want.index) == Some(&want.sig)
        });
        out.push(check(
            format!("import `{}` occupies func index {}", want.name, want.index),
            ok,
            format!(
                "decoded {:?} type {:?}, intended `{}` type {:?}",
                got.map(|i| (&i.module, &i.name)),
                dec.type_of_func(want.index),
                want.name,
                want.sig
            ),
        ));
    }

    // S3 — the defined function count.
    out.push(check(
        "defined function count == trust-ir definition count".to_string(),
        dec.defined_func_types.len() == intended.defined.len()
            && dec.bodies.len() == intended.defined.len(),
        format!(
            "function section {}, code section {}, intended {}",
            dec.defined_func_types.len(),
            dec.bodies.len(),
            intended.defined.len()
        ),
    ));

    // S4 — each definition sits at `import_base + ordinal`, is exported under
    // its trust-ir name at that index, and the index denotes its signature.
    for want in &intended.defined {
        let export = dec
            .exports
            .iter()
            .find(|e| e.name == want.name && e.kind == 0x00);
        let ok = export.is_some_and(|e| e.index == want.index)
            && dec.type_of_func(want.index) == Some(&want.sig);
        out.push(check(
            format!(
                "definition `{}` occupies func index {} (import base {n})",
                want.name, want.index
            ),
            ok,
            format!(
                "export {:?}, index type {:?}, intended type {:?}",
                export.map(|e| e.index),
                dec.type_of_func(want.index),
                want.sig
            ),
        ));
    }

    // S5 — the funcref table covers the null slot plus the WHOLE function index
    // space, and the element segment makes element `i + 1` be function `i`.
    // This is what lets a function-pointer constant be its funcidx plus
    // `CLOSED_TABLE_BASE`, and keeps the null pointer off every function.
    if intended.needs_table {
        let count = dec.func_count();
        let table_ok = dec.table_min == Some(count + CLOSED_TABLE_BASE);
        out.push(check(
            "funcref table covers the null slot and the whole function index space".to_string(),
            table_ok,
            format!(
                "table min {:?}, null slot + function index space {}",
                dec.table_min,
                count + CLOSED_TABLE_BASE
            ),
        ));
        let elems_ok = dec.elements.len() == 1
            && dec.elements[0].offset == CLOSED_TABLE_BASE as i32
            && dec.elements[0].table == 0
            && dec.elements[0].funcs == (0..count).collect::<Vec<_>>();
        out.push(check(
            "element segment fills table 0 from index 1 so element i + 1 is function i".to_string(),
            elems_ok,
            format!(
                "{} segment(s); first {:?}",
                dec.elements.len(),
                dec.elements.first().map(|e| (e.table, e.offset, &e.funcs))
            ),
        ));
    } else {
        out.push(check(
            "no funcref table is declared when no function needs one".to_string(),
            dec.table_min.is_none() && dec.elements.is_empty(),
            format!(
                "table {:?}, {} element segment(s)",
                dec.table_min,
                dec.elements.len()
            ),
        ));
    }

    // S6 — the element binding is FIXED for the instance's lifetime: the table
    // is not exported and no body contains a table-mutating instruction. Without
    // this, "element i + 1 is function i" holds only until someone overwrites it.
    let table_exported = dec.exports.iter().any(|e| e.kind == 0x01);
    let mutates = dec
        .bodies
        .iter()
        .any(|b| decode_insts(&b.code).is_ok_and(|is| is.iter().any(is_table_mutating)));
    out.push(check(
        "the funcref table is neither exported nor mutated by the module".to_string(),
        !table_exported && !mutates,
        format!("table exported: {table_exported}, table-mutating instruction: {mutates}"),
    ));

    // S7 — the shadow stack fits the memory it lives in (Policy O), or the
    // memory is imported and the base is the host's (Policy I).
    if intended.needs_frame {
        let sp_global_idx = dec.global_import_count();
        let sp = dec.globals.first();
        match sp.map(|g| g.init) {
            Some(DecodedInit::I32(top)) => {
                let top_u = u64::from(top as u32);
                let pages = dec.memory_min_pages.map(u64::from).unwrap_or(0);
                out.push(check(
                    "the defined memory reaches the shadow-stack base".to_string(),
                    pages * PAGE_BYTES >= top_u,
                    format!(
                        "memory min {pages} page(s) = {} bytes, base {top_u}",
                        pages * PAGE_BYTES
                    ),
                ));
                // S8 — static data lies strictly BELOW the stack base, so an
                // empty stack does not start inside it. The bound at DEPTH is
                // the deferred stack-reserve obligation, not this one.
                let end = dec
                    .data
                    .iter()
                    .map(|d| u64::from(d.offset as u32) + d.len as u64)
                    .max()
                    .unwrap_or(0);
                out.push(check(
                    "every data segment ends at or below the shadow-stack base".to_string(),
                    end <= top_u,
                    format!("highest data end {end}, stack base {top_u} (depth-0 bound only)"),
                ));
            }
            Some(DecodedInit::GlobalGet(g)) => {
                let ok = dec.imports_memory()
                    && g < dec.global_import_count()
                    && dec
                        .imports
                        .iter()
                        .filter_map(|i| match i.kind {
                            DecodedImportKind::Global { ty, mutable } => Some((ty, mutable)),
                            _ => None,
                        })
                        .nth(g as usize)
                        == Some((VT_I32, false));
                out.push(check(
                    "under an imported memory the stack base is an IMPORTED IMMUTABLE i32 global"
                        .to_string(),
                    ok,
                    format!(
                        "sp global {sp_global_idx} initialized by global.get {g}; memory imported: \
                         {}; {} global import(s)",
                        dec.imports_memory(),
                        dec.global_import_count()
                    ),
                ));
            }
            other => out.push(check(
                "the module declares a shadow stack-pointer global".to_string(),
                false,
                format!("first defined global init {other:?}"),
            )),
        }
    }

    out
}

/// The valtype byte a decoded instruction PUSHES, when this family can say.
/// `None` means "not a single-value push this family models", which is a
/// FAIL-CLOSED answer for the argument-window check.
fn pushed_type(i: &DecodedInst, body: &DecodedBody, params: &[u8]) -> Option<u8> {
    match i.op {
        OP_LOCAL_GET => body.local_type(params, idx_of(i)?),
        OP_I32_CONST => Some(VT_I32),
        _ => None,
    }
}

/// Structural checks over ONE function's decoded body: the call/table ABI.
pub fn call_structural_checks(
    dec: &DecodedModule,
    body: &DecodedBody,
    intended: &IntendedFunction,
) -> Vec<AbiStructuralCheck> {
    let mut out = Vec::new();
    let insts = match decode_insts(&body.code) {
        Ok(i) => i,
        Err(e) => {
            out.push(check(
                format!("`{}` body decodes", intended.name),
                false,
                format!("{e}"),
            ));
            return out;
        }
    };
    let params = &intended.sig.params;

    let direct: Vec<(usize, u32)> = insts
        .iter()
        .enumerate()
        .filter(|(_, i)| i.op == OP_CALL)
        .filter_map(|(k, i)| idx_of(i).map(|t| (k, t)))
        .collect();
    let indirect: Vec<(usize, u32, u32)> = insts
        .iter()
        .enumerate()
        .filter_map(|(k, i)| match i.imm {
            Imm::CallIndirect { type_idx, table } if i.op == OP_CALL_INDIRECT => {
                Some((k, type_idx, table))
            }
            _ => None,
        })
        .collect();

    // C1 — the MULTISET of direct-call targets matches. Order is a relooper
    // fact this family does not own (see the "call-site correspondence"
    // deferral), so the statement is deliberately over the multiset.
    let mut got: Vec<u32> = direct.iter().map(|(_, t)| *t).collect();
    let mut want: Vec<u32> = intended.calls.iter().map(|c| c.target).collect();
    got.sort_unstable();
    want.sort_unstable();
    out.push(check(
        format!(
            "`{}`: emitted direct-call targets == intended",
            intended.name
        ),
        got == want,
        format!("decoded {got:?}, intended {want:?}"),
    ));

    // C2 — every emitted target RESOLVES, through the decoded import and
    // function sections, to a function of a signature the trust-ir module
    // actually calls with. This is the check an import-shift bug fails.
    let want_sigs: BTreeSet<Vec<u8>> = intended.calls.iter().map(|c| encode_sig(&c.sig)).collect();
    for (k, target) in &direct {
        let ty = dec.type_of_func(*target);
        let ok = ty.is_some_and(|t| want_sigs.contains(&encode_sig(t)));
        out.push(check(
            format!(
                "`{}`: call at instruction {k} -> func {target} resolves to a called signature",
                intended.name
            ),
            ok,
            format!(
                "func {target} (import base {}) has type {:?}; call-site signatures {:?}",
                dec.func_import_count(),
                ty,
                intended.calls.iter().map(|c| &c.sig).collect::<Vec<_>>()
            ),
        ));

        // C3 — ARGUMENT discipline: the instructions immediately preceding the
        // call push exactly the parameter types, in order.
        let Some(sig) = ty else { continue };
        let np = sig.params.len();
        if *k < np {
            out.push(check(
                format!(
                    "`{}`: call at instruction {k} is preceded by {np} operand push(es)",
                    intended.name
                ),
                false,
                format!("only {k} instruction(s) precede it"),
            ));
            continue;
        }
        let window = &insts[k - np..*k];
        let pushed: Vec<Option<u8>> = window
            .iter()
            .map(|i| pushed_type(i, body, params))
            .collect();
        let ok = pushed
            .iter()
            .zip(&sig.params)
            .all(|(got, want)| *got == Some(*want));
        out.push(check(
            format!(
                "`{}`: call at instruction {k} pushes exactly its {np} parameter type(s)",
                intended.name
            ),
            ok,
            format!("pushed {pushed:?}, declared params {:?}", sig.params),
        ));

        // C4 — RESULT discipline: a value-returning call is consumed by exactly
        // one consumer; a void call is followed by no consumer.
        let next = insts.get(k + 1);
        let consumed =
            next.is_some_and(|i| i.op == OP_LOCAL_SET || i.op == OP_DROP || i.op == OP_LOCAL_TEE);
        let ok = match sig.results.len() {
            0 => !consumed,
            1 => consumed || is_narrow_canonicalization(next),
            _ => false,
        };
        out.push(check(
            format!(
                "`{}`: call at instruction {k} consumes its {} result(s) exactly once",
                intended.name,
                sig.results.len()
            ),
            ok,
            format!(
                "next instruction {:?}, results {:?}",
                next.map(|i| format!("0x{:02x}", i.op)),
                sig.results
            ),
        ));
    }

    // C5 — call_indirect: the DECLARED type index denotes the call site's own
    // signature; the table immediate names table 0; and the operand pushed
    // immediately before the call is the i32 table index, with the arguments
    // below it.
    let mut want_indirect: Vec<Vec<u8>> = intended
        .indirects
        .iter()
        .map(|i| encode_sig(&i.sig))
        .collect();
    want_indirect.sort();
    let mut got_indirect: Vec<Vec<u8>> = indirect
        .iter()
        .filter_map(|(_, t, _)| dec.types.get(*t as usize).map(encode_sig))
        .collect();
    got_indirect.sort();
    out.push(check(
        format!(
            "`{}`: emitted call_indirect signatures == the declared ones",
            intended.name
        ),
        got_indirect == want_indirect && indirect.len() == intended.indirects.len(),
        format!(
            "decoded {} site(s) {got_indirect:?}, intended {} site(s) {want_indirect:?}",
            indirect.len(),
            intended.indirects.len()
        ),
    ));
    for (k, type_idx, table) in &indirect {
        out.push(check(
            format!(
                "`{}`: call_indirect at instruction {k} uses table 0",
                intended.name
            ),
            *table == 0,
            format!("table immediate {table}"),
        ));
        let Some(sig) = dec.types.get(*type_idx as usize) else {
            out.push(check(
                format!(
                    "`{}`: call_indirect at instruction {k} names a declared type",
                    intended.name
                ),
                false,
                format!(
                    "type index {type_idx} is outside the {} type(s)",
                    dec.types.len()
                ),
            ));
            continue;
        };
        let np = sig.params.len();
        // The callee index sits on top; the arguments are below it.
        if *k < np + 1 {
            out.push(check(
                format!(
                    "`{}`: call_indirect at instruction {k} is preceded by {np} argument(s) + a \
                     table index",
                    intended.name
                ),
                false,
                format!("only {k} instruction(s) precede it"),
            ));
            continue;
        }
        let window = &insts[k - np - 1..*k];
        let pushed: Vec<Option<u8>> = window
            .iter()
            .map(|i| pushed_type(i, body, params))
            .collect();
        let args_ok = pushed[..np]
            .iter()
            .zip(&sig.params)
            .all(|(got, want)| *got == Some(*want));
        let index_ok = pushed[np] == Some(VT_I32);
        out.push(check(
            format!(
                "`{}`: call_indirect at instruction {k} pushes {np} argument(s) then an i32 table \
                 index",
                intended.name
            ),
            args_ok && index_ok,
            format!("pushed {pushed:?}, declared params {:?}", sig.params),
        ));
    }

    // C6 — every call_indirect whose trust-ir callee is a function-pointer
    // constant calls, through the element segment, the function that constant
    // names. The table operand is resolved on the DECODED body: an `i32.const
    // X` pushed directly, or a local whose every write in the body is (a copy
    // of) the same `i32.const X` and which is definitely assigned at the read
    // (a local starts at 0, the null slot, so a read some path reaches before
    // any write is ambiguous and leaves the site unresolved). `X` is then
    // looked up in the decoded element segment — never by assuming the table
    // layout — and the element must have the call site's declared type.
    // Binding the constant to its use site is what keeps an unrelated scalar
    // that happens to equal the table index from standing in for the pointer;
    // a pointer constant with any other use is refused in `wasm_abi_evidence`.
    //
    // WHICH SITE IS WHICH. When every trust-ir `call_indirect` of the function
    // sits in ONE trust-ir block and the body holds exactly as many
    // `call_indirect`s, the lowering emits them in that block's order, so the
    // i-th emitted site is bound to the i-th trust-ir site: its element must be
    // the function ITS OWN pointer constant names, and a dynamic trust-ir
    // callee must not resolve to a constant. Two same-signature pointers
    // swapped between their sites refute. Otherwise (sites in several blocks,
    // whose emitted order is the relooper's, or an emitted count that differs)
    // the statement is over the
    // MULTISET of resolved elements, and which site produced which call is the
    // "call-site correspondence" deferral's. A body whose emitted
    // `call_indirect` count differs from the trust-ir count has no one-to-one
    // correspondence to bind either, so it too is stated over the multiset (and
    // then fails whenever the resolved elements differ from the intended ones).
    if !intended.const_callees.is_empty() || !indirect.is_empty() {
        let blocks: BTreeSet<usize> = intended.indirects.iter().map(|i| i.block).collect();
        let per_site = blocks.len() <= 1 && indirect.len() == intended.indirects.len();
        let mut problems: Vec<String> = Vec::new();
        // The element function a constant site resolves to, after the
        // null-slot and signature checks (which push their own problem).
        let resolve_site = |k: usize, type_idx: u32, problems: &mut Vec<String>| {
            let x = k
                .checked_sub(1)
                .and_then(|j| resolve_i32_constant(&insts, j, params.len()))?;
            match element_function(dec, x) {
                None => {
                    problems.push(format!(
                        "call_indirect at instruction {k}: table index {x} names no element (the \
                         null slot or past the segment)"
                    ));
                    Some(None)
                }
                Some(f) => {
                    let declared = dec.types.get(type_idx as usize);
                    if declared.is_none() || dec.type_of_func(f) != declared {
                        problems.push(format!(
                            "call_indirect at instruction {k}: element {x} is function {f} of \
                             type {:?}, the site declares {declared:?}",
                            dec.type_of_func(f)
                        ));
                    }
                    Some(Some(f))
                }
            }
        };
        if per_site {
            let mut bound: Vec<String> = Vec::new();
            for (ordinal, ((k, type_idx, _), site)) in
                indirect.iter().zip(&intended.indirects).enumerate()
            {
                let got = resolve_site(*k, *type_idx, &mut problems);
                match (site.const_callee, got) {
                    (Some(want), Some(Some(f))) if f == want => {
                        bound.push(format!("site {ordinal} -> function {f}"));
                    }
                    (Some(want), Some(Some(f))) => problems.push(format!(
                        "call_indirect at instruction {k} (trust-ir indirect call {ordinal}) \
                         calls element function {f}, but its pointer constant names function \
                         {want}"
                    )),
                    (Some(_), Some(None)) => {}
                    (Some(want), None) => problems.push(format!(
                        "call_indirect at instruction {k} (trust-ir indirect call {ordinal}) \
                         does not resolve to a constant table index, but its pointer constant \
                         names function {want}"
                    )),
                    (None, Some(_)) => problems.push(format!(
                        "call_indirect at instruction {k} (trust-ir indirect call {ordinal}) \
                         resolves to a constant table index, but its trust-ir callee is not a \
                         function-pointer constant"
                    )),
                    (None, None) => {}
                }
            }
            out.push(check(
                format!(
                    "`{}`: each constant call_indirect site calls, through the element segment, \
                     the function its own pointer constant names",
                    intended.name
                ),
                problems.is_empty(),
                format!(
                    "per-site binding in emission order within one trust-ir block: [{}]{}",
                    bound.join(", "),
                    if problems.is_empty() {
                        String::new()
                    } else {
                        format!("; {}", problems.join("; "))
                    }
                ),
            ));
        } else {
            let mut want: Vec<u32> = intended.const_callees.clone();
            want.sort_unstable();
            let mut got: Vec<u32> = Vec::new();
            for (k, type_idx, _) in &indirect {
                if let Some(Some(f)) = resolve_site(*k, *type_idx, &mut problems) {
                    got.push(f);
                }
            }
            got.sort_unstable();
            out.push(check(
                format!(
                    "`{}`: the constant call_indirect callees resolve, through the element \
                     segment, to the multiset of functions their pointer constants name",
                    intended.name
                ),
                got == want && problems.is_empty(),
                format!(
                    "multiset only ({} call_indirect site(s) across {} trust-ir block(s), {} \
                     emitted; which site produced which call is the call-site correspondence \
                     deferral's): resolved element functions {got:?}, intended constant \
                     callees {want:?}{}",
                    intended.indirects.len(),
                    blocks.len(),
                    indirect.len(),
                    if problems.is_empty() {
                        String::new()
                    } else {
                        format!("; {}", problems.join("; "))
                    }
                ),
            ));
        }
    }

    out
}

/// The single `i32` constant the value pushed by `insts[at]` must hold, when
/// the decoded body alone determines it: an `i32.const`, or a `local.get` of a
/// non-parameter local every write of which stores the same resolvable
/// constant AND that is definitely assigned at the read. A declared local
/// starts at zero, so a read that some path reaches before any write (an
/// earlier position, a write in an `if` arm or a block a branch can leave
/// first, a loop reading before its own write) may observe that implicit 0:
/// without definite assignment the value is ambiguous and the site is
/// unresolved. `None` otherwise, and on a body whose control structure does
/// not decode.
fn resolve_i32_constant(insts: &[DecodedInst], at: usize, param_count: usize) -> Option<i32> {
    fn go(
        insts: &[DecodedInst],
        at: usize,
        param_count: usize,
        seen: &mut BTreeSet<u32>,
    ) -> Option<i32> {
        let i = insts.get(at)?;
        match (i.op, &i.imm) {
            (OP_I32_CONST, Imm::I32(v)) => Some(*v),
            (OP_LOCAL_GET, Imm::Idx(l)) => {
                let l = *l;
                if (l as usize) < param_count || !seen.insert(l) {
                    return None;
                }
                let mut value = None;
                for (j, w) in insts.iter().enumerate() {
                    if (w.op == OP_LOCAL_SET || w.op == OP_LOCAL_TEE) && idx_of(w) == Some(l) {
                        let v = go(insts, j.checked_sub(1)?, param_count, seen)?;
                        if value.is_some_and(|x| x != v) {
                            return None;
                        }
                        value = Some(v);
                    }
                }
                if definitely_assigned(insts, l, at)? {
                    value
                } else {
                    None
                }
            }
            _ => None,
        }
    }
    go(insts, at, param_count, &mut BTreeSet::new())
}

/// Is local `local` written on EVERY path from the function entry to
/// instruction `read`? A forward must-analysis over the structured body:
/// `assigned` only turns true along a path, so a loop header's state is its
/// entry state (a back edge arrives no less assigned than it left), a
/// `block` / `if` end joins its fall-through with every branch to its label
/// (an `if` without `else` also with its entry state), and code after an
/// unconditional branch, `return` or `unreachable` is unreachable (vacuously
/// assigned). `None` when the body's control structure does not decode
/// anywhere in the body (a branch label past the open constructs, an `else`
/// outside an `if`, an unbalanced `end`, an instruction after the body's
/// final `end`) or `read` is not one of its instructions.
fn definitely_assigned(insts: &[DecodedInst], local: u32, read: usize) -> Option<bool> {
    #[derive(Clone, Copy, PartialEq, Eq)]
    enum Kind {
        Block,
        Loop,
        If { else_seen: bool },
    }
    struct Frame {
        kind: Kind,
        entry: bool,
        branched: bool,
    }
    fn record(stack: &mut [Frame], label: u32, a: bool) -> Option<()> {
        let at = stack.len().checked_sub(1 + label as usize)?;
        let f = &mut stack[at];
        if f.kind != Kind::Loop {
            f.branched &= a;
        }
        Some(())
    }
    // The function body is an implicit block; a branch to it returns.
    let mut stack = vec![Frame {
        kind: Kind::Block,
        entry: false,
        branched: true,
    }];
    let mut a = false;
    let mut at_read = None;
    for (k, i) in insts.iter().enumerate() {
        if stack.is_empty() {
            return None;
        }
        if k == read {
            at_read = Some(a);
        }
        match (i.op, &i.imm) {
            (0x02, _) => stack.push(Frame {
                kind: Kind::Block,
                entry: a,
                branched: true,
            }),
            (0x03, _) => stack.push(Frame {
                kind: Kind::Loop,
                entry: a,
                branched: true,
            }),
            (0x04, _) => stack.push(Frame {
                kind: Kind::If { else_seen: false },
                entry: a,
                branched: true,
            }),
            (0x05, _) => {
                let f = stack.last_mut()?;
                let Kind::If { else_seen: false } = f.kind else {
                    return None;
                };
                f.branched &= a;
                f.kind = Kind::If { else_seen: true };
                a = f.entry;
            }
            (0x0b, _) => {
                let f = stack.pop()?;
                a = match f.kind {
                    Kind::Block | Kind::If { else_seen: true } => f.branched && a,
                    Kind::If { else_seen: false } => f.branched && a && f.entry,
                    Kind::Loop => a,
                };
            }
            (0x0c, Imm::Idx(l)) => {
                record(&mut stack, *l, a)?;
                a = true;
            }
            (0x0d, Imm::Idx(l)) => record(&mut stack, *l, a)?,
            (0x0e, Imm::BrTable { targets, default }) => {
                for l in targets.iter().chain(std::iter::once(default)) {
                    record(&mut stack, *l, a)?;
                }
                a = true;
            }
            (0x00 | 0x0f, _) => a = true,
            (OP_LOCAL_SET | OP_LOCAL_TEE, Imm::Idx(l)) if *l == local => a = true,
            _ => {}
        }
    }
    if stack.is_empty() { at_read } else { None }
}

/// The function the decoded element segment of table 0 puts at table index
/// `x`, or `None` for an index no element fills (the null slot among them).
fn element_function(dec: &DecodedModule, x: i32) -> Option<u32> {
    dec.elements.iter().filter(|e| e.table == 0).find_map(|e| {
        let k = i64::from(x) - i64::from(e.offset);
        usize::try_from(k)
            .ok()
            .and_then(|k| e.funcs.get(k).copied())
    })
}

/// Is `i` the start of the narrow-carrier re-canonicalization the lowering
/// emits before binding a narrow call result? Accepting it keeps C4 from
/// mis-flagging a correct narrow return; the canonicalization ITSELF belongs to
/// the value-domain family, not this one.
fn is_narrow_canonicalization(i: Option<&DecodedInst>) -> bool {
    i.is_some_and(|i| matches!(i.op, 0xc0 | 0xc1 | OP_I32_CONST))
}

fn encode_sig(t: &DecodedFuncType) -> Vec<u8> {
    let mut v = vec![t.params.len() as u8];
    v.extend_from_slice(&t.params);
    v.push(t.results.len() as u8);
    v.extend_from_slice(&t.results);
    v
}

/// Structural checks over ONE function's decoded FRAME shape: the frame size,
/// its 8-alignment, the slot offsets, and the presence of an epilogue on every
/// normal return.
pub fn frame_structural_checks(
    body: &DecodedBody,
    intended: &IntendedFunction,
) -> Vec<AbiStructuralCheck> {
    let mut out = Vec::new();
    let insts = match decode_insts(&body.code) {
        Ok(i) => i,
        Err(e) => {
            out.push(check(
                format!("`{}` body decodes", intended.name),
                false,
                format!("{e}"),
            ));
            return out;
        }
    };
    let pro = find_prologue(&insts);
    if intended.frame.frame_size == 0 {
        out.push(check(
            format!(
                "`{}`: a frameless function emits no prologue",
                intended.name
            ),
            pro.is_none(),
            format!("prologue window decoded: {}", pro.is_some()),
        ));
        return out;
    }
    let Some(pro) = pro else {
        out.push(check(
            format!("`{}`: a framed function emits a prologue", intended.name),
            false,
            "no prologue window at the head of the body".to_string(),
        ));
        return out;
    };

    let f = intended.frame.frame_size;
    out.push(check(
        format!(
            "`{}`: emitted frame size == the intended layout",
            intended.name
        ),
        pro.frame_size_imm as u32 == f,
        format!("decoded {}, intended {f}", pro.frame_size_imm),
    ));
    out.push(check(
        format!("`{}`: the emitted frame size is 8-aligned", intended.name),
        (pro.frame_size_imm as u32).is_multiple_of(8),
        format!("decoded frame size {}", pro.frame_size_imm),
    ));

    let allocas = find_allocas(&insts, pro.base_local);
    out.push(check(
        format!("`{}`: one alloca window per trust-ir Alloca", intended.name),
        allocas.len() == intended.frame.slots.len(),
        format!(
            "decoded {}, intended {}",
            allocas.len(),
            intended.frame.slots.len()
        ),
    ));
    for (k, (dec, want)) in allocas.iter().zip(&intended.frame.slots).enumerate() {
        let off = dec.offset_imm as u32;
        out.push(check(
            format!("`{}`: alloca {k} slot offset == intended", intended.name),
            off == want.offset,
            format!("decoded {off}, intended {}", want.offset),
        ));
        out.push(check(
            format!(
                "`{}`: alloca {k}'s {} byte(s) fit inside the {f}-byte frame",
                intended.name, want.size
            ),
            u64::from(off) + u64::from(want.size) <= u64::from(f),
            format!("offset {off} + size {} vs frame {f}", want.size),
        ));
    }

    // Every `return` must be preceded by the restore window. Missing it is the
    // abandoned-frame bug of OWNERSHIP.md §3 on the path that DOES run it.
    let returns: Vec<usize> = insts
        .iter()
        .enumerate()
        .filter(|(_, i)| i.op == OP_RETURN)
        .map(|(k, _)| k)
        .collect();
    let restores = find_epilogues(&insts, pro.saved_local);
    let restores_sp = restores
        .iter()
        .filter(|w| idx_of(&w[1]) == Some(pro.sp_global_read))
        .count();
    out.push(check(
        format!(
            "`{}`: every normal return is preceded by a stack-pointer restore",
            intended.name
        ),
        !returns.is_empty() && restores_sp >= 1,
        format!(
            "{} return(s), {} restore window(s) writing global {}",
            returns.len(),
            restores_sp,
            pro.sp_global_read
        ),
    ));

    out
}

// ===========================================================================
// The family entry point
// ===========================================================================

/// The evidence one module contributes to the memory / call-ABI families.
#[derive(Debug, Clone, Default)]
pub struct WasmAbiEvidence {
    /// SMT obligations over the frame arithmetic.
    pub obligations: Vec<ProofObligation>,
    /// Decidable structural checks over the index spaces and the call ABI.
    pub structural: Vec<AbiStructuralCheck>,
    /// Fail-closed refusals: a function whose emission this family could not
    /// recognize contributes NO obligation, and the reason is recorded here
    /// rather than dropped.
    pub refusals: Vec<String>,
}

impl WasmAbiEvidence {
    /// Structural checks that FAILED.
    pub fn failed_structural(&self) -> Vec<&AbiStructuralCheck> {
        self.structural.iter().filter(|c| !c.ok).collect()
    }

    /// Every SMT obligation is `Reconstructed`-provenanced — the credit
    /// discriminator.
    pub fn all_reconstructed(&self) -> bool {
        self.obligations.iter().all(|o| o.is_reconstructed())
    }
}

/// Build the family's whole evidence for one emitted module.
///
/// `bytes` are the REAL emitted module; `module` is the trust-ir it was
/// compiled from. Fails when the bytes cannot be decoded or the source model
/// refuses a construct, including a trust-ir v53 non-propagating call
/// boundary. A per-function byte recognition failure becomes a recorded
/// REFUSAL (no credit), never a silent skip.
pub fn wasm_abi_evidence(bytes: &[u8], module: &Module) -> Result<WasmAbiEvidence, String> {
    let dec = decode_module(bytes).map_err(|e| format!("decode: {e}"))?;
    let intended = intended_module(module).map_err(|e| format!("intended model: {e}"))?;
    let mut ev = WasmAbiEvidence {
        structural: module_structural_checks(&dec, &intended),
        ..Default::default()
    };
    for (ordinal, want) in intended.defined.iter().enumerate() {
        let Some(body) = dec.bodies.get(ordinal) else {
            ev.refusals.push(format!(
                "`{}`: no code-section entry at ordinal {ordinal} — NO CREDIT",
                want.name
            ));
            continue;
        };
        ev.structural.extend(frame_structural_checks(body, want));
        ev.structural
            .extend(call_structural_checks(&dec, body, want));
        if !want.escaping_func_ptrs.is_empty() {
            ev.refusals.push(format!(
                "`{}`: function-pointer constant(s) {:?} reach a use other than a call_indirect \
                 callee (an argument, a store, a block argument, a return); this family cannot \
                 bind such a constant to the table element it names — NO CREDIT",
                want.name, want.escaping_func_ptrs
            ));
        }
        match frame_obligations(body, want) {
            Ok(obs) => ev.obligations.extend(obs),
            Err(why) => ev.refusals.push(why),
        }
    }
    Ok(ev)
}

/// Discharge the family's SMT obligations by evaluation and report the REAL
/// split: proven, refuted (with names), and inconclusive (with names).
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct AbiDischargeCounts {
    /// Obligations that discharged `Valid`.
    pub proven: usize,
    /// Obligations that were REFUTED, by name.
    pub refuted: Vec<String>,
    /// Obligations the evaluator could not settle, by name.
    pub inconclusive: Vec<String>,
}

/// Evaluate every obligation in `obligations`, returning the honest split.
pub fn discharge_by_evaluation(
    obligations: &[ProofObligation],
    config: &VerificationConfig,
) -> AbiDischargeCounts {
    let mut c = AbiDischargeCounts::default();
    for ob in obligations {
        match verify_by_evaluation_with_config(ob, config) {
            VerificationResult::Valid => c.proven += 1,
            VerificationResult::Invalid { .. } => c.refuted.push(ob.name.clone()),
            _ => c.inconclusive.push(ob.name.clone()),
        }
    }
    c
}

// ===========================================================================
// Anti-tautology guards — mutate the REAL bytes and require a failure
// ===========================================================================

/// What a guard must do to the family's evidence.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum GuardExpectation {
    /// The mutation MUST be caught: at least one obligation refutes, one
    /// structural check fails, or one function is refused.
    MustRefute,
    /// The mutation is KNOWN to be invisible to this family. It is registered
    /// and reported as not-refuted, with the deferral that owns it, rather than
    /// omitted — hiding it would overstate the family's reach.
    KnownBlind {
        /// The [`WASM_ABI_DEFERRALS`] entry that owns this blind spot.
        deferral: &'static str,
    },
}

/// One byte-level mutation of a REAL emitted module.
#[derive(Debug, Clone, Copy)]
pub struct AbiGuard {
    /// What wrong lowering this simulates.
    pub name: &'static str,
    /// Which corpus fixture it mutates.
    pub fixture: &'static str,
    /// The exact byte sequence to find (must occur at least once).
    pub needle: &'static [u8],
    /// Its replacement — the SAME length, so the module stays decodable and
    /// only the modeled property changes.
    pub patch: &'static [u8],
    /// Whether the family must catch it.
    pub expectation: GuardExpectation,
}

/// Apply a guard's mutation to `bytes`, returning the mutated module.
///
/// Fails when the needle does not occur (the fixture drifted) or when it occurs
/// more than once (the mutation would not be the one the guard describes) —
/// both fail-closed, because a guard that silently mutated nothing would report
/// a false "refuted".
pub fn apply_guard(bytes: &[u8], guard: &AbiGuard) -> Result<Vec<u8>, String> {
    if guard.needle.len() != guard.patch.len() {
        return Err(format!(
            "guard `{}`: needle and patch differ in length ({} vs {})",
            guard.name,
            guard.needle.len(),
            guard.patch.len()
        ));
    }
    let hits: Vec<usize> = bytes
        .windows(guard.needle.len())
        .enumerate()
        .filter(|(_, w)| *w == guard.needle)
        .map(|(k, _)| k)
        .collect();
    match hits.len() {
        0 => Err(format!(
            "guard `{}`: its needle {:02x?} does not occur in fixture `{}` — the fixture drifted",
            guard.name, guard.needle, guard.fixture
        )),
        1 => {
            let mut out = bytes.to_vec();
            out[hits[0]..hits[0] + guard.patch.len()].copy_from_slice(guard.patch);
            Ok(out)
        }
        n => Err(format!(
            "guard `{}`: its needle occurs {n} times in fixture `{}` — ambiguous mutation",
            guard.name, guard.fixture
        )),
    }
}

/// The guard corpus.
///
/// Each entry patches the REAL emitted bytes of a named fixture. The needles
/// are read off the emitted modules and pinned by the gate test, so a backend
/// change that moves them fails loudly instead of quietly disarming a guard.
pub const WASM_ABI_GUARDS: &[AbiGuard] = &[
    // ---- family (2): the frame ----
    AbiGuard {
        name: "prologue subtracts the WRONG frame size (0x20 -> 0x28)",
        fixture: "abi_frame",
        // local.get 8; i32.const 32; i32.sub
        needle: &[0x20, 0x08, 0x41, 0x20, 0x6b],
        patch: &[0x20, 0x08, 0x41, 0x28, 0x6b],
        expectation: GuardExpectation::MustRefute,
    },
    AbiGuard {
        name: "prologue grows the frame UPWARD (i32.sub -> i32.add)",
        fixture: "abi_frame",
        needle: &[0x41, 0x20, 0x6b, 0x22, 0x09],
        patch: &[0x41, 0x20, 0x6a, 0x22, 0x09],
        expectation: GuardExpectation::MustRefute,
    },
    AbiGuard {
        name: "a frame slot offset is SHIFTED (alloca 1: +8 -> +16)",
        fixture: "abi_frame",
        // local.get 9; i32.const 8; i32.add; local.set 3
        needle: &[0x20, 0x09, 0x41, 0x08, 0x6a, 0x21, 0x03],
        patch: &[0x20, 0x09, 0x41, 0x10, 0x6a, 0x21, 0x03],
        expectation: GuardExpectation::MustRefute,
    },
    AbiGuard {
        name: "two frame slots COLLIDE (alloca 2's offset 16 -> 8)",
        fixture: "abi_frame",
        // local.get 9; i32.const 16; i32.add; local.set 4
        needle: &[0x20, 0x09, 0x41, 0x10, 0x6a, 0x21, 0x04],
        patch: &[0x20, 0x09, 0x41, 0x08, 0x6a, 0x21, 0x04],
        expectation: GuardExpectation::MustRefute,
    },
    AbiGuard {
        name: "the epilogue restores the FRAME BASE instead of the caller's SP",
        fixture: "abi_frame",
        // local.get 8; global.set 0; local.get 7; return
        needle: &[0x20, 0x08, 0x24, 0x00, 0x20, 0x07, 0x0f],
        patch: &[0x20, 0x09, 0x24, 0x00, 0x20, 0x07, 0x0f],
        expectation: GuardExpectation::MustRefute,
    },
    AbiGuard {
        name: "the prologue publishes the new SP into a DIFFERENT global than it read",
        fixture: "abi_frame",
        // local.tee 9; global.set 0; local.get 9
        needle: &[0x22, 0x09, 0x24, 0x00, 0x20, 0x09],
        patch: &[0x22, 0x09, 0x24, 0x01, 0x20, 0x09],
        expectation: GuardExpectation::MustRefute,
    },
    AbiGuard {
        name: "the island prologue reads the IMPORTED base global instead of its own SP",
        fixture: "abi_island",
        // global.get 1; local.set 7  (sp global is 1: one imported global at 0)
        needle: &[0x23, 0x01, 0x21, 0x07],
        patch: &[0x23, 0x00, 0x21, 0x07],
        expectation: GuardExpectation::MustRefute,
    },
    // ---- family (3): calls, imports and the table ----
    AbiGuard {
        name: "a direct call FORGETS the import shift (call 2 -> call 0)",
        fixture: "abi_calls",
        // local.get 2; local.get 1; call 2; local.set 3
        needle: &[0x20, 0x02, 0x20, 0x01, 0x10, 0x02, 0x21, 0x03],
        patch: &[0x20, 0x02, 0x20, 0x01, 0x10, 0x00, 0x21, 0x03],
        expectation: GuardExpectation::MustRefute,
    },
    AbiGuard {
        name: "a direct call targets an import of the WRONG signature (call 1 -> call 0)",
        fixture: "abi_calls",
        // local.get 4; call 1; local.set 5   (host_b takes an i64)
        needle: &[0x20, 0x04, 0x10, 0x01, 0x21, 0x05],
        patch: &[0x20, 0x04, 0x10, 0x00, 0x21, 0x05],
        expectation: GuardExpectation::MustRefute,
    },
    AbiGuard {
        name: "an argument push is DROPPED (local.get -> nop nop)",
        fixture: "abi_calls",
        // local.get 0; local.get 1; call 0
        needle: &[0x20, 0x00, 0x20, 0x01, 0x10, 0x00],
        patch: &[0x01, 0x01, 0x20, 0x01, 0x10, 0x00],
        expectation: GuardExpectation::MustRefute,
    },
    AbiGuard {
        name: "a call's RESULT is not consumed (local.set -> local.get)",
        fixture: "abi_calls",
        // call 0; local.set 2; local.get 2
        needle: &[0x10, 0x00, 0x21, 0x02, 0x20, 0x02],
        patch: &[0x10, 0x00, 0x20, 0x02, 0x20, 0x02],
        expectation: GuardExpectation::MustRefute,
    },
    AbiGuard {
        name: "a function-pointer constant FORGETS the import shift (3 -> 1)",
        fixture: "abi_table",
        // i32.const 3 (funcidx 2 + the null slot); local.set 2
        needle: &[0x41, 0x03, 0x21, 0x02],
        patch: &[0x41, 0x01, 0x21, 0x02],
        expectation: GuardExpectation::MustRefute,
    },
    AbiGuard {
        name: "a function-pointer constant FORGETS the null slot (3 -> 2)",
        fixture: "abi_table",
        // i32.const 3; local.set 2  ->  the bare funcidx 2
        needle: &[0x41, 0x03, 0x21, 0x02],
        patch: &[0x41, 0x02, 0x21, 0x02],
        expectation: GuardExpectation::MustRefute,
    },
    AbiGuard {
        name: "a function-pointer constant is OFF BY ONE while an unrelated scalar equals its \
               table index (2 -> 1)",
        fixture: "abi_table_collide",
        // `viaptr`: i32.const 2 (add7 = funcidx 1 + the null slot); local.set 1.
        // The scalar `const i32 2` is `i32.const 2; local.set 3`, untouched.
        needle: &[0x41, 0x02, 0x21, 0x01],
        patch: &[0x41, 0x01, 0x21, 0x01],
        expectation: GuardExpectation::MustRefute,
    },
    AbiGuard {
        name: "a function-pointer constant names the NULL slot while an unrelated scalar equals \
               its table index (2 -> 0)",
        fixture: "abi_table_collide",
        needle: &[0x41, 0x02, 0x21, 0x01],
        patch: &[0x41, 0x00, 0x21, 0x01],
        expectation: GuardExpectation::MustRefute,
    },
    AbiGuard {
        name: "the call_indirect reads the unrelated scalar's local BEFORE its only write \
               (local 1 -> local 3: still zero, the null slot, at the call)",
        fixture: "abi_table_collide",
        // `viaptr`: local.get 0; local.get 1; call_indirect. Local 3 is written
        // only by the later `i32.const 2; local.set 3`, which equals the table
        // index but is not assigned on the path to the call.
        needle: &[0x20, 0x00, 0x20, 0x01, 0x11],
        patch: &[0x20, 0x00, 0x20, 0x03, 0x11],
        expectation: GuardExpectation::MustRefute,
    },
    AbiGuard {
        name: "the element segment fills table index 0, the null pointer (offset 1 -> 0)",
        fixture: "abi_table",
        // offset i32.const 1; end; 4 entries; function 0
        needle: &[0x41, 0x01, 0x0b, 0x04, 0x00],
        patch: &[0x41, 0x00, 0x0b, 0x04, 0x00],
        expectation: GuardExpectation::MustRefute,
    },
    AbiGuard {
        name: "the element segment stops covering the import space (element 3 -> 0)",
        fixture: "abi_table",
        // element func indices 0,1,2,3
        needle: &[0x04, 0x00, 0x01, 0x02, 0x03],
        patch: &[0x04, 0x00, 0x01, 0x02, 0x00],
        expectation: GuardExpectation::MustRefute,
    },
    AbiGuard {
        name: "call_indirect declares the wrong table (table 0 -> 1)",
        fixture: "abi_table",
        // call_indirect type 0 table 0; local.set 3
        needle: &[0x11, 0x00, 0x00, 0x21, 0x03],
        patch: &[0x11, 0x00, 0x01, 0x21, 0x03],
        expectation: GuardExpectation::MustRefute,
    },
    AbiGuard {
        name: "the funcref table is EXPORTED, so the host can repoint element i",
        fixture: "abi_table",
        // export "imul" kind=func(0x00) index=2  ->  kind=table(0x01)
        needle: &[0x04, 0x69, 0x6d, 0x75, 0x6c, 0x00, 0x02],
        patch: &[0x04, 0x69, 0x6d, 0x75, 0x6c, 0x01, 0x02],
        expectation: GuardExpectation::MustRefute,
    },
    AbiGuard {
        name: "the imported island stack base is declared MUTABLE",
        fixture: "abi_island",
        // ...global import: i32 (0x7f), immutable (0x00); then section 3
        needle: &[0x03, 0x7f, 0x00, 0x03, 0x02, 0x01, 0x00],
        patch: &[0x03, 0x7f, 0x01, 0x03, 0x02, 0x01, 0x00],
        expectation: GuardExpectation::MustRefute,
    },
    AbiGuard {
        name: "two same-signature function-pointer constants are SWAPPED between their \
               call_indirect sites in one block",
        fixture: "abi_table_two",
        // `two`: i32.const 1 (neg); local.set 1; local.get 0; local.get 1;
        // call_indirect; local.set 2; i32.const 2 (inc). Exchanging the two
        // table indices keeps the multiset of callees and every signature, and
        // computes neg(inc(x)) for inc(neg(x)).
        needle: &[
            0x41, 0x01, 0x21, 0x01, 0x20, 0x00, 0x20, 0x01, 0x11, 0x00, 0x00, 0x21, 0x02, 0x41,
            0x02,
        ],
        patch: &[
            0x41, 0x02, 0x21, 0x01, 0x20, 0x00, 0x20, 0x01, 0x11, 0x00, 0x00, 0x21, 0x02, 0x41,
            0x01,
        ],
        expectation: GuardExpectation::MustRefute,
    },
    // ---- the declared blind spot ----
    AbiGuard {
        name: "two same-signature call targets are PERMUTED within one function",
        fixture: "abi_calls",
        // `root` calls host_a (func 0) and then leaf (func 2). Those two share
        // the signature (i32, i32) -> i32, so swapping the two `call`
        // immediates leaves the MULTISET of targets, every resolved signature,
        // and every argument window intact — it is a different program that
        // this family cannot see. Registered rather than omitted: the
        // "call-site correspondence" deferral is what owes an answer.
        //   call 0; local.set 2; local.get 2; local.get 1; call 2
        needle: &[0x10, 0x00, 0x21, 0x02, 0x20, 0x02, 0x20, 0x01, 0x10, 0x02],
        patch: &[0x10, 0x02, 0x21, 0x02, 0x20, 0x02, 0x20, 0x01, 0x10, 0x00],
        expectation: GuardExpectation::KnownBlind {
            deferral: "call-site correspondence across a reordered CFG",
        },
    },
];

/// The result of running one guard.
#[derive(Debug, Clone)]
pub struct GuardOutcome {
    /// The guard's name.
    pub name: &'static str,
    /// What was expected of it.
    pub expectation: GuardExpectation,
    /// Whether the family CAUGHT the mutation.
    pub refuted: bool,
    /// How it was caught (or why it was not).
    pub detail: String,
}

impl GuardOutcome {
    /// Did the guard behave as declared?
    pub fn as_declared(&self) -> bool {
        match self.expectation {
            GuardExpectation::MustRefute => self.refuted,
            GuardExpectation::KnownBlind { .. } => !self.refuted,
        }
    }
}

/// Run one guard against a fixture's REAL bytes and trust-ir module.
pub fn run_guard(
    guard: &AbiGuard,
    bytes: &[u8],
    module: &Module,
    config: &VerificationConfig,
) -> Result<GuardOutcome, String> {
    let mutated = apply_guard(bytes, guard)?;
    let (refuted, detail) = match wasm_abi_evidence(&mutated, module) {
        Err(e) => (true, format!("the mutated module failed to decode: {e}")),
        Ok(ev) => {
            let counts = discharge_by_evaluation(&ev.obligations, config);
            let failed: Vec<String> = ev
                .failed_structural()
                .iter()
                .map(|c| c.name.clone())
                .collect();
            let caught =
                !counts.refuted.is_empty() || !failed.is_empty() || !ev.refusals.is_empty();
            (
                caught,
                format!(
                    "{} obligation(s) refuted {:?}; {} structural check(s) failed {:?}; {} \
                     refusal(s) {:?}",
                    counts.refuted.len(),
                    counts.refuted,
                    failed.len(),
                    failed,
                    ev.refusals.len(),
                    ev.refusals
                ),
            )
        }
    };
    Ok(GuardOutcome {
        name: guard.name,
        expectation: guard.expectation,
        refuted,
        detail,
    })
}

// ===========================================================================
// The embedded corpus — REAL emitted bytes, kept fresh by the gate test
// ===========================================================================

/// One corpus fixture: a trust-ir module in the TrustIr text format, the wasm
/// policy it is compiled under, and the module bytes the backend's LOWERING
/// really emitted for it (the O0 compile: the input of the lane's local
/// emission pass, which at O1 and above emits a rewrite of a function only
/// when `wasm_local_tv` validates it against these bytes).
///
/// The bytes are frozen so this module needs no dependency on the backend (the
/// dependency direction is codegen -> verify, so it cannot have one). They are
/// kept honest by `tests/wasm_abi_proofs_gate.rs`, which re-compiles every
/// fixture with the REAL backend and requires byte equality: a backend change
/// that alters an emission fails that gate rather than quietly leaving this
/// family proving things about a module nobody emits any more.
#[derive(Debug, Clone, Copy)]
pub struct AbiFixture {
    /// Fixture name, matching [`AbiGuard::fixture`].
    pub name: &'static str,
    /// The compile policy, as a human-readable tag the gate test re-creates.
    pub policy: &'static str,
    /// The trust-ir module, in the TrustIr text format.
    pub tir: &'static str,
    /// The emitted module bytes.
    pub wasm: &'static [u8],
}

/// The six corpus fixtures.
pub const WASM_ABI_FIXTURES: &[AbiFixture] = &[
    AbiFixture {
        name: "abi_frame",
        policy: "closed",
        tir: FRAME_TIR,
        wasm: FRAME_WASM,
    },
    AbiFixture {
        name: "abi_calls",
        policy: "func-imports:trust:island/calls@1",
        tir: CALLS_TIR,
        wasm: CALLS_WASM,
    },
    AbiFixture {
        name: "abi_table",
        policy: "func-imports:trust:island/calls@1",
        tir: TABLE_TIR,
        wasm: TABLE_WASM,
    },
    AbiFixture {
        name: "abi_island",
        policy: "island:abi",
        tir: ISLAND_TIR,
        wasm: ISLAND_WASM,
    },
    AbiFixture {
        name: "abi_table_collide",
        policy: "closed",
        tir: TABLE_COLLIDE_TIR,
        wasm: TABLE_COLLIDE_WASM,
    },
    AbiFixture {
        name: "abi_table_two",
        policy: "closed",
        tir: TABLE_TWO_TIR,
        wasm: TABLE_TWO_WASM,
    },
];

/// Look up a fixture by name.
pub fn fixture(name: &str) -> Option<&'static AbiFixture> {
    WASM_ABI_FIXTURES.iter().find(|f| f.name == name)
}

const FRAME_TIR: &str = r#"; TrustIr text format v1
module "abi_frame"
target "wasm32-unknown-unknown" 4 little

functy.0 = (i32, i32) -> (i32)

type ty.0 = i32

fn @frame3(functy.0) {
bb0(%0: i32, %1: i32):
    %2 = alloca i32
    %3 = alloca i64
    %4 = alloca [ty.0 x 3]
    store i32 %0, ptr %2
    store i32 %0, ptr %3
    store i32 %1, ptr %4
    %5 = load i32, ptr %2
    %6 = load i32, ptr %4
    %7 = add i32 %5, %6
    ret %7
}
"#;

const FRAME_WASM: &[u8] = &[
    0x00, 0x61, 0x73, 0x6d, 0x01, 0x00, 0x00, 0x00, 0x01, 0x07, 0x01, 0x60, 0x02, 0x7f, 0x7f, 0x01,
    0x7f, 0x03, 0x02, 0x01, 0x00, 0x05, 0x03, 0x01, 0x00, 0x01, 0x06, 0x08, 0x01, 0x7f, 0x01, 0x41,
    0x80, 0x80, 0x04, 0x0b, 0x07, 0x0a, 0x01, 0x06, 0x66, 0x72, 0x61, 0x6d, 0x65, 0x33, 0x00, 0x00,
    0x0a, 0x5a, 0x01, 0x58, 0x01, 0x08, 0x7f, 0x23, 0x00, 0x21, 0x08, 0x20, 0x08, 0x41, 0x20, 0x6b,
    0x22, 0x09, 0x24, 0x00, 0x20, 0x09, 0x41, 0x00, 0x6a, 0x21, 0x02, 0x20, 0x09, 0x41, 0x08, 0x6a,
    0x21, 0x03, 0x20, 0x09, 0x41, 0x10, 0x6a, 0x21, 0x04, 0x20, 0x02, 0x20, 0x00, 0x36, 0x02, 0x00,
    0x20, 0x03, 0x20, 0x00, 0x36, 0x02, 0x00, 0x20, 0x04, 0x20, 0x01, 0x36, 0x02, 0x00, 0x20, 0x02,
    0x28, 0x02, 0x00, 0x21, 0x05, 0x20, 0x04, 0x28, 0x02, 0x00, 0x21, 0x06, 0x20, 0x05, 0x20, 0x06,
    0x6a, 0x21, 0x07, 0x20, 0x08, 0x24, 0x00, 0x20, 0x07, 0x0f, 0x00, 0x0b,
];

const CALLS_TIR: &str = r#"; TrustIr text format v1
module "abi_calls"
target "wasm32-unknown-unknown" 4 little

functy.0 = (i32, i32) -> (i32)

functy.1 = (i64) -> (i32)

fn @host_a(functy.0) {
}

fn @host_b(functy.1) {
}

fn @leaf(functy.0) {
bb0(%0: i32, %1: i32):
    %2 = mul i32 %0, %1
    ret %2
}

fn @root(functy.0) {
bb0(%0: i32, %1: i32):
    %2 = call @func.0(%0, %1)
    %3 = call @func.2(%2, %1)
    %4 = sext i32 %3 to i64
    %5 = call @func.1(%4)
    ret %5
}
"#;

const CALLS_WASM: &[u8] = &[
    0x00, 0x61, 0x73, 0x6d, 0x01, 0x00, 0x00, 0x00, 0x01, 0x0c, 0x02, 0x60, 0x02, 0x7f, 0x7f, 0x01,
    0x7f, 0x60, 0x01, 0x7e, 0x01, 0x7f, 0x02, 0x3d, 0x02, 0x14, 0x74, 0x72, 0x75, 0x73, 0x74, 0x3a,
    0x69, 0x73, 0x6c, 0x61, 0x6e, 0x64, 0x2f, 0x63, 0x61, 0x6c, 0x6c, 0x73, 0x40, 0x31, 0x06, 0x68,
    0x6f, 0x73, 0x74, 0x5f, 0x61, 0x00, 0x00, 0x14, 0x74, 0x72, 0x75, 0x73, 0x74, 0x3a, 0x69, 0x73,
    0x6c, 0x61, 0x6e, 0x64, 0x2f, 0x63, 0x61, 0x6c, 0x6c, 0x73, 0x40, 0x31, 0x06, 0x68, 0x6f, 0x73,
    0x74, 0x5f, 0x62, 0x00, 0x01, 0x03, 0x03, 0x02, 0x00, 0x00, 0x07, 0x0f, 0x02, 0x04, 0x6c, 0x65,
    0x61, 0x66, 0x00, 0x02, 0x04, 0x72, 0x6f, 0x6f, 0x74, 0x00, 0x03, 0x0a, 0x39, 0x02, 0x0f, 0x01,
    0x01, 0x7f, 0x20, 0x00, 0x20, 0x01, 0x6c, 0x21, 0x02, 0x20, 0x02, 0x0f, 0x00, 0x0b, 0x27, 0x03,
    0x02, 0x7f, 0x01, 0x7e, 0x01, 0x7f, 0x20, 0x00, 0x20, 0x01, 0x10, 0x00, 0x21, 0x02, 0x20, 0x02,
    0x20, 0x01, 0x10, 0x02, 0x21, 0x03, 0x20, 0x03, 0xac, 0x21, 0x04, 0x20, 0x04, 0x10, 0x01, 0x21,
    0x05, 0x20, 0x05, 0x0f, 0x00, 0x0b,
];

const TABLE_TIR: &str = r#"; TrustIr text format v1
module "abi_table"
target "wasm32-unknown-unknown" 4 little

functy.0 = (i32, i32) -> (i32)

fn @host_a(functy.0) {
}

fn @host_b(functy.0) {
}

fn @imul(functy.0) {
bb0(%0: i32, %1: i32):
    %2 = mul i32 %0, %1
    ret %2
}

fn @dispatch(functy.0) {
bb0(%0: i32, %1: i32):
    %2 = const functy.0 fndef<func.2>
    %3 = call_indirect %2(functy.0)(%0, %1)
    ret %3
}
"#;

const TABLE_WASM: &[u8] = &[
    0x00, 0x61, 0x73, 0x6d, 0x01, 0x00, 0x00, 0x00, 0x01, 0x07, 0x01, 0x60, 0x02, 0x7f, 0x7f, 0x01,
    0x7f, 0x02, 0x3d, 0x02, 0x14, 0x74, 0x72, 0x75, 0x73, 0x74, 0x3a, 0x69, 0x73, 0x6c, 0x61, 0x6e,
    0x64, 0x2f, 0x63, 0x61, 0x6c, 0x6c, 0x73, 0x40, 0x31, 0x06, 0x68, 0x6f, 0x73, 0x74, 0x5f, 0x61,
    0x00, 0x00, 0x14, 0x74, 0x72, 0x75, 0x73, 0x74, 0x3a, 0x69, 0x73, 0x6c, 0x61, 0x6e, 0x64, 0x2f,
    0x63, 0x61, 0x6c, 0x6c, 0x73, 0x40, 0x31, 0x06, 0x68, 0x6f, 0x73, 0x74, 0x5f, 0x62, 0x00, 0x00,
    0x03, 0x03, 0x02, 0x00, 0x00, 0x04, 0x04, 0x01, 0x70, 0x00, 0x05, 0x07, 0x13, 0x02, 0x04, 0x69,
    0x6d, 0x75, 0x6c, 0x00, 0x02, 0x08, 0x64, 0x69, 0x73, 0x70, 0x61, 0x74, 0x63, 0x68, 0x00, 0x03,
    0x09, 0x0a, 0x01, 0x00, 0x41, 0x01, 0x0b, 0x04, 0x00, 0x01, 0x02, 0x03, 0x0a, 0x29, 0x02, 0x0f,
    0x01, 0x01, 0x7f, 0x20, 0x00, 0x20, 0x01, 0x6c, 0x21, 0x02, 0x20, 0x02, 0x0f, 0x00, 0x0b, 0x17,
    0x01, 0x02, 0x7f, 0x41, 0x03, 0x21, 0x02, 0x20, 0x00, 0x20, 0x01, 0x20, 0x02, 0x11, 0x00, 0x00,
    0x21, 0x03, 0x20, 0x03, 0x0f, 0x00, 0x0b,
];

const ISLAND_TIR: &str = r#"; TrustIr text format v1
module "abi_island"
target "wasm32-unknown-unknown" 4 little

functy.0 = (i32, i32) -> (i32)

fn @host_note(functy.0) {
}

fn @island_frame(functy.0) {
bb0(%0: i32, %1: i32):
    %2 = alloca i32
    %3 = alloca i32
    store i32 %0, ptr %2
    store i32 %1, ptr %3
    %4 = load i32, ptr %2
    %5 = load i32, ptr %3
    %6 = call @func.0(%4, %5)
    ret %6
}
"#;

const ISLAND_WASM: &[u8] = &[
    0x00, 0x61, 0x73, 0x6d, 0x01, 0x00, 0x00, 0x00, 0x01, 0x07, 0x01, 0x60, 0x02, 0x7f, 0x7f, 0x01,
    0x7f, 0x02, 0x67, 0x03, 0x12, 0x74, 0x72, 0x75, 0x73, 0x74, 0x3a, 0x69, 0x73, 0x6c, 0x61, 0x6e,
    0x64, 0x2f, 0x61, 0x62, 0x69, 0x40, 0x31, 0x09, 0x68, 0x6f, 0x73, 0x74, 0x5f, 0x6e, 0x6f, 0x74,
    0x65, 0x00, 0x00, 0x12, 0x74, 0x72, 0x75, 0x73, 0x74, 0x3a, 0x69, 0x73, 0x6c, 0x61, 0x6e, 0x64,
    0x2f, 0x61, 0x62, 0x69, 0x40, 0x31, 0x06, 0x6d, 0x65, 0x6d, 0x6f, 0x72, 0x79, 0x02, 0x00, 0x00,
    0x12, 0x74, 0x72, 0x75, 0x73, 0x74, 0x3a, 0x69, 0x73, 0x6c, 0x61, 0x6e, 0x64, 0x2f, 0x61, 0x62,
    0x69, 0x40, 0x31, 0x13, 0x5f, 0x5f, 0x69, 0x73, 0x6c, 0x61, 0x6e, 0x64, 0x5f, 0x73, 0x74, 0x61,
    0x63, 0x6b, 0x5f, 0x62, 0x61, 0x73, 0x65, 0x03, 0x7f, 0x00, 0x03, 0x02, 0x01, 0x00, 0x06, 0x06,
    0x01, 0x7f, 0x01, 0x23, 0x00, 0x0b, 0x07, 0x10, 0x01, 0x0c, 0x69, 0x73, 0x6c, 0x61, 0x6e, 0x64,
    0x5f, 0x66, 0x72, 0x61, 0x6d, 0x65, 0x00, 0x01, 0x0a, 0x4d, 0x01, 0x4b, 0x01, 0x07, 0x7f, 0x23,
    0x01, 0x21, 0x07, 0x20, 0x07, 0x41, 0x10, 0x6b, 0x22, 0x08, 0x24, 0x01, 0x20, 0x08, 0x41, 0x00,
    0x6a, 0x21, 0x02, 0x20, 0x08, 0x41, 0x08, 0x6a, 0x21, 0x03, 0x20, 0x02, 0x20, 0x00, 0x36, 0x02,
    0x00, 0x20, 0x03, 0x20, 0x01, 0x36, 0x02, 0x00, 0x20, 0x02, 0x28, 0x02, 0x00, 0x21, 0x04, 0x20,
    0x03, 0x28, 0x02, 0x00, 0x21, 0x05, 0x20, 0x04, 0x20, 0x05, 0x10, 0x00, 0x21, 0x06, 0x20, 0x07,
    0x24, 0x01, 0x20, 0x06, 0x0f, 0x00, 0x0b,
];

/// A pointer constant whose table index (2, for `add7`) EQUALS an unrelated
/// scalar constant bound to a local in the same body (`const i32 2`), so a
/// check that looks for the index among the body's constants cannot tell a
/// wrong pointer from a right one; binding the pointer to its call_indirect
/// can.
const TABLE_COLLIDE_TIR: &str = r#"; TrustIr text format v1
module "abi_table_collide"
target "wasm32-unknown-unknown" 4 little

functy.0 = (i32) -> (i32)

fn @mul3(functy.0) {
bb0(%1: i32):
    %2 = const i32 3
    %3 = mul i32 %1, %2
    ret %3
}

fn @add7(functy.0) {
bb0(%1: i32):
    %2 = const i32 7
    %3 = add i32 %1, %2
    ret %3
}

fn @viaptr(functy.0) {
bb0(%1: i32):
    %2 = const functy.0 fndef<func.1>
    %3 = call_indirect %2(functy.0)(%1)
    %4 = const i32 2
    %5 = mul i32 %3, %4
    ret %5
}
"#;

const TABLE_COLLIDE_WASM: &[u8] = &[
    0x00, 0x61, 0x73, 0x6d, 0x01, 0x00, 0x00, 0x00, 0x01, 0x06, 0x01, 0x60, 0x01, 0x7f, 0x01, 0x7f,
    0x03, 0x04, 0x03, 0x00, 0x00, 0x00, 0x04, 0x04, 0x01, 0x70, 0x00, 0x04, 0x07, 0x18, 0x03, 0x04,
    0x6d, 0x75, 0x6c, 0x33, 0x00, 0x00, 0x04, 0x61, 0x64, 0x64, 0x37, 0x00, 0x01, 0x06, 0x76, 0x69,
    0x61, 0x70, 0x74, 0x72, 0x00, 0x02, 0x09, 0x09, 0x01, 0x00, 0x41, 0x01, 0x0b, 0x03, 0x00, 0x01,
    0x02, 0x0a, 0x4a, 0x03, 0x13, 0x01, 0x02, 0x7f, 0x41, 0x03, 0x21, 0x01, 0x20, 0x00, 0x20, 0x01,
    0x6c, 0x21, 0x02, 0x20, 0x02, 0x0f, 0x00, 0x0b, 0x13, 0x01, 0x02, 0x7f, 0x41, 0x07, 0x21, 0x01,
    0x20, 0x00, 0x20, 0x01, 0x6a, 0x21, 0x02, 0x20, 0x02, 0x0f, 0x00, 0x0b, 0x20, 0x01, 0x04, 0x7f,
    0x41, 0x02, 0x21, 0x01, 0x20, 0x00, 0x20, 0x01, 0x11, 0x00, 0x00, 0x21, 0x02, 0x41, 0x02, 0x21,
    0x03, 0x20, 0x02, 0x20, 0x03, 0x6c, 0x21, 0x04, 0x20, 0x04, 0x0f, 0x00, 0x0b,
];

/// Two same-signature function pointers called in ONE block: the per-site
/// binding of C6 is what tells `inc(neg(x))` from `neg(inc(x))`.
const TABLE_TWO_TIR: &str = r#"; TrustIr text format v1
module "abi_table_two"
target "wasm32-unknown-unknown" 4 little

functy.0 = (i32) -> (i32)

fn @neg(functy.0) {
bb0(%1: i32):
    %2 = const i32 0
    %3 = sub i32 %2, %1
    ret %3
}

fn @inc(functy.0) {
bb0(%1: i32):
    %2 = const i32 1
    %3 = add i32 %1, %2
    ret %3
}

fn @two(functy.0) {
bb0(%1: i32):
    %2 = const functy.0 fndef<func.0>
    %3 = call_indirect %2(functy.0)(%1)
    %4 = const functy.0 fndef<func.1>
    %5 = call_indirect %4(functy.0)(%3)
    ret %5
}
"#;

const TABLE_TWO_WASM: &[u8] = &[
    0x00, 0x61, 0x73, 0x6d, 0x01, 0x00, 0x00, 0x00, 0x01, 0x06, 0x01, 0x60, 0x01, 0x7f, 0x01, 0x7f,
    0x03, 0x04, 0x03, 0x00, 0x00, 0x00, 0x04, 0x04, 0x01, 0x70, 0x00, 0x04, 0x07, 0x13, 0x03, 0x03,
    0x6e, 0x65, 0x67, 0x00, 0x00, 0x03, 0x69, 0x6e, 0x63, 0x00, 0x01, 0x03, 0x74, 0x77, 0x6f, 0x00,
    0x02, 0x09, 0x09, 0x01, 0x00, 0x41, 0x01, 0x0b, 0x03, 0x00, 0x01, 0x02, 0x0a, 0x4c, 0x03, 0x13,
    0x01, 0x02, 0x7f, 0x41, 0x00, 0x21, 0x01, 0x20, 0x01, 0x20, 0x00, 0x6b, 0x21, 0x02, 0x20, 0x02,
    0x0f, 0x00, 0x0b, 0x13, 0x01, 0x02, 0x7f, 0x41, 0x01, 0x21, 0x01, 0x20, 0x00, 0x20, 0x01, 0x6a,
    0x21, 0x02, 0x20, 0x02, 0x0f, 0x00, 0x0b, 0x22, 0x01, 0x04, 0x7f, 0x41, 0x01, 0x21, 0x01, 0x20,
    0x00, 0x20, 0x01, 0x11, 0x00, 0x00, 0x21, 0x02, 0x41, 0x02, 0x21, 0x03, 0x20, 0x02, 0x20, 0x03,
    0x11, 0x00, 0x00, 0x21, 0x04, 0x20, 0x04, 0x0f, 0x00, 0x0b,
];

// ===========================================================================
// Registration entry points
// ===========================================================================

/// The family's whole evidence over the embedded corpus.
#[derive(Debug, Clone, Default)]
pub struct WasmAbiFamilyReport {
    /// Per-fixture evidence, in corpus order.
    pub per_fixture: Vec<(&'static str, WasmAbiEvidence)>,
    /// Fixtures that could not be modeled at all.
    pub errors: Vec<String>,
}

impl WasmAbiFamilyReport {
    /// Every SMT obligation across the corpus.
    pub fn obligations(&self) -> Vec<ProofObligation> {
        self.per_fixture
            .iter()
            .flat_map(|(_, e)| e.obligations.clone())
            .collect()
    }

    /// Every structural check across the corpus.
    pub fn structural(&self) -> Vec<AbiStructuralCheck> {
        self.per_fixture
            .iter()
            .flat_map(|(_, e)| e.structural.clone())
            .collect()
    }

    /// Every fail-closed refusal across the corpus.
    pub fn refusals(&self) -> Vec<String> {
        self.per_fixture
            .iter()
            .flat_map(|(_, e)| e.refusals.clone())
            .collect()
    }
}

/// Build the family's evidence over the embedded corpus.
///
/// This is the no-argument registration entry: it needs neither the backend nor
/// a caller-supplied module, because the corpus carries REAL emitted bytes and
/// the trust-ir text they were compiled from.
pub fn wasm_abi_family_report() -> WasmAbiFamilyReport {
    let mut report = WasmAbiFamilyReport::default();
    for f in WASM_ABI_FIXTURES {
        match trust_ir::parser::parse_module(f.tir) {
            Err(e) => report.errors.push(format!(
                "fixture `{}`: trust-ir parse failed: {e:?}",
                f.name
            )),
            Ok(module) => match wasm_abi_evidence(f.wasm, &module) {
                Err(e) => report.errors.push(format!("fixture `{}`: {e}", f.name)),
                Ok(ev) => report.per_fixture.push((f.name, ev)),
            },
        }
    }
    report
}

/// Every SMT obligation the family states over its embedded corpus.
///
/// Machine sides are reconstructed by decoding the real emitted bytes, so this
/// is safe to register alongside the other reconstruction families.
pub fn all_wasm_abi_obligations() -> Vec<ProofObligation> {
    wasm_abi_family_report().obligations()
}

/// Every anti-tautology guard, run against the embedded corpus.
///
/// Returns one [`GuardOutcome`] per guard, including the declared blind spot,
/// which is reported as NOT refuted rather than omitted.
pub fn all_wasm_abi_guards(config: &VerificationConfig) -> Vec<Result<GuardOutcome, String>> {
    WASM_ABI_GUARDS
        .iter()
        .map(|g| {
            let Some(f) = fixture(g.fixture) else {
                return Err(format!(
                    "guard `{}`: unknown fixture `{}`",
                    g.name, g.fixture
                ));
            };
            let module = trust_ir::parser::parse_module(f.tir)
                .map_err(|e| format!("guard `{}`: trust-ir parse failed: {e:?}", g.name))?;
            run_guard(g, f.wasm, &module, config)
        })
        .collect()
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    fn cfg() -> VerificationConfig {
        VerificationConfig::default()
    }

    /// The independent LEB128 readers agree with the spec's definition on the
    /// boundary cases the module format actually contains, INCLUDING the
    /// multi-byte forms (`i32.const 65536` is `0x80 0x80 0x04` in the shipped
    /// stack-pointer initializer).
    #[test]
    fn leb128_readers_match_the_spec() {
        let cases: &[(&[u8], u32)] = &[
            (&[0x00], 0),
            (&[0x08], 8),
            (&[0x7f], 127),
            (&[0x80, 0x01], 128),
            (&[0xff, 0xff, 0xff, 0xff, 0x0f], u32::MAX),
        ];
        for (bytes, want) in cases {
            let mut c = Cur::new(bytes);
            assert_eq!(c.uleb32("t").expect("uleb"), *want, "{bytes:02x?}");
            assert!(c.done());
        }
        let signed: &[(&[u8], i64)] = &[
            (&[0x00], 0),
            (&[0x20], 32),
            (&[0x7f], -1),
            (&[0x40], -64),
            (&[0xc0, 0x00], 64),
            (&[0x80, 0x80, 0x04], 65536),
            (&[0x80, 0x80, 0x7c], -65536),
        ];
        for (bytes, want) in signed {
            let mut c = Cur::new(bytes);
            assert_eq!(c.sleb64("t").expect("sleb"), *want, "{bytes:02x?}");
            assert!(c.done());
        }
        // Overlong forms fail closed rather than silently truncating.
        let mut c = Cur::new(&[0x80, 0x80, 0x80, 0x80, 0x80, 0x01]);
        assert!(c.uleb32("t").is_err());
    }

    /// Every fixture decodes, and the decode agrees with what the section
    /// layout says about the index spaces.
    #[test]
    fn every_fixture_decodes() {
        for f in WASM_ABI_FIXTURES {
            let d = decode_module(f.wasm)
                .unwrap_or_else(|e| panic!("fixture `{}` failed to decode: {e}", f.name));
            assert_eq!(
                d.bodies.len(),
                d.defined_func_types.len(),
                "fixture `{}`: code section and function section disagree",
                f.name
            );
            for b in &d.bodies {
                decode_insts(&b.code)
                    .unwrap_or_else(|e| panic!("fixture `{}`: body failed to decode: {e}", f.name));
            }
        }
    }

    /// An unknown opcode FAILS the instruction walk rather than being skipped:
    /// an unknown immediate length would mis-decode every byte after it.
    #[test]
    fn unknown_opcode_fails_closed() {
        // 0xd0 (ref.null) is outside the modeled surface.
        let e = decode_insts(&[0x20, 0x00, 0xd0, 0x0b]).expect_err("must fail closed");
        assert!(matches!(
            e,
            AbiDecodeError::UnknownOpcode { opcode: 0xd0, .. }
        ));
    }

    /// A local operand resolves to a constant only where it is definitely
    /// assigned at the read; a local still holding its implicit 0 on some
    /// path is ambiguous. The read is the last `local.get 1` (params: 1, so
    /// local 1 is a declared local).
    #[test]
    fn a_local_resolves_only_where_it_is_definitely_assigned() {
        let resolve = |code: &[u8]| {
            let insts = decode_insts(code).expect("decodes");
            let read = insts
                .iter()
                .rposition(|i| i.op == OP_LOCAL_GET)
                .expect("a read");
            resolve_i32_constant(&insts, read, 1)
        };
        // A straight-line write before the read.
        assert_eq!(
            resolve(&[0x41, 0x02, 0x21, 0x01, 0x20, 0x01, 0x1a, 0x0b]),
            Some(2)
        );
        // A write before the read, the read nested in a later block.
        assert_eq!(
            resolve(&[
                0x41, 0x02, 0x21, 0x01, 0x02, 0x40, 0x20, 0x01, 0x1a, 0x0b, 0x0b
            ]),
            Some(2)
        );
        // Both arms of an `if` write it.
        assert_eq!(
            resolve(&[
                0x20, 0x00, 0x04, 0x40, 0x41, 0x02, 0x21, 0x01, 0x05, 0x41, 0x02, 0x21, 0x01, 0x0b,
                0x20, 0x01, 0x1a, 0x0b
            ]),
            Some(2)
        );
        // Written in a loop's inner block and read after the loop: the block
        // is left only past the write (`br_if 0`) or back to the loop header
        // (`br_if 1`), so every exit is assigned — the shape the lowering
        // gives a loop with two exits into one block.
        assert_eq!(
            resolve(&[
                0x03, 0x40, 0x02, 0x40, 0x41, 0x02, 0x21, 0x01, 0x20, 0x00, 0x0d, 0x00, 0x20, 0x00,
                0x0d, 0x01, 0x0b, 0x0b, 0x20, 0x01, 0x1a, 0x0b
            ]),
            Some(2)
        );
        // The only write comes AFTER the read: the read sees 0.
        assert_eq!(
            resolve(&[
                0x02, 0x40, 0x20, 0x01, 0x1a, 0x0b, 0x41, 0x02, 0x21, 0x01, 0x0b
            ]),
            None
        );
        // The only write is inside an `if` arm the read is not in.
        assert_eq!(
            resolve(&[
                0x20, 0x00, 0x04, 0x40, 0x41, 0x02, 0x21, 0x01, 0x0b, 0x20, 0x01, 0x1a, 0x0b
            ]),
            None
        );
        // The only write is in the `then` arm, the read in the `else` arm.
        assert_eq!(
            resolve(&[
                0x20, 0x00, 0x04, 0x40, 0x41, 0x02, 0x21, 0x01, 0x05, 0x20, 0x01, 0x1a, 0x0b, 0x0b
            ]),
            None
        );
        // The only write is inside a block a `br_if` can leave before it.
        assert_eq!(
            resolve(&[
                0x02, 0x40, 0x20, 0x00, 0x0d, 0x00, 0x41, 0x02, 0x21, 0x01, 0x0b, 0x20, 0x01, 0x1a,
                0x0b
            ]),
            None
        );
        // A `br_table` leaves the block before its only write.
        assert_eq!(
            resolve(&[
                0x02, 0x40, 0x20, 0x00, 0x0e, 0x01, 0x00, 0x00, 0x41, 0x02, 0x21, 0x01, 0x0b, 0x20,
                0x01, 0x1a, 0x0b
            ]),
            None
        );
        // A loop reading before its own later write: the first iteration
        // sees 0.
        assert_eq!(
            resolve(&[
                0x03, 0x40, 0x20, 0x01, 0x1a, 0x41, 0x02, 0x21, 0x01, 0x0b, 0x0b
            ]),
            None
        );
        // An unbalanced body is not resolved, even past the read.
        assert_eq!(
            resolve(&[0x41, 0x02, 0x21, 0x01, 0x20, 0x01, 0x1a, 0x0b, 0x0b]),
            None
        );
    }

    /// The whole corpus produces evidence, every SMT obligation is
    /// reconstruction-provenanced, and nothing was refused.
    #[test]
    fn corpus_produces_reconstructed_evidence() {
        let report = wasm_abi_family_report();
        assert!(report.errors.is_empty(), "{:?}", report.errors);
        assert_eq!(report.per_fixture.len(), WASM_ABI_FIXTURES.len());
        assert!(
            report.refusals().is_empty(),
            "fail-closed refusals: {:?}",
            report.refusals()
        );
        let obs = report.obligations();
        assert!(!obs.is_empty(), "the family stated no obligation at all");
        for ob in &obs {
            assert!(
                ob.is_reconstructed(),
                "obligation `{}` is not reconstruction-provenanced",
                ob.name
            );
        }
    }

    /// Every SMT obligation discharges `Valid` on the UNMUTATED corpus.
    #[test]
    fn corpus_obligations_discharge_valid() {
        let obs = all_wasm_abi_obligations();
        let counts = discharge_by_evaluation(&obs, &cfg());
        assert_eq!(
            counts.proven,
            obs.len(),
            "refuted {:?}; inconclusive {:?}",
            counts.refuted,
            counts.inconclusive
        );
    }

    /// Every structural check passes on the UNMUTATED corpus.
    #[test]
    fn corpus_structural_checks_pass() {
        let report = wasm_abi_family_report();
        let failed: Vec<String> = report
            .structural()
            .into_iter()
            .filter(|c| !c.ok)
            .map(|c| format!("{}: {}", c.name, c.detail))
            .collect();
        assert!(failed.is_empty(), "failed structural checks: {failed:#?}");
    }

    /// THE TEETH: every guard behaves exactly as declared. A `MustRefute` guard
    /// that passes means the family has gone vacuous; a `KnownBlind` guard that
    /// refutes means the deferral is stale and should be retired.
    #[test]
    fn guards_behave_as_declared() {
        let outcomes = all_wasm_abi_guards(&cfg());
        for o in outcomes {
            let o = o.unwrap_or_else(|e| panic!("guard could not run: {e}"));
            assert!(
                o.as_declared(),
                "guard `{}` expected {:?} but refuted={} — {}",
                o.name,
                o.expectation,
                o.refuted,
                o.detail
            );
        }
    }

    /// The deferrals are named, distinct, and each states an owner, a citation
    /// and a substantive reason. A deferral with a token reason is debt hidden
    /// behind a label.
    #[test]
    fn deferrals_are_named_and_substantive() {
        assert_eq!(WASM_ABI_DEFERRALS.len(), 9);
        let names: BTreeSet<_> = WASM_ABI_DEFERRALS.iter().map(|d| d.name).collect();
        assert_eq!(names.len(), WASM_ABI_DEFERRALS.len());
        for d in WASM_ABI_DEFERRALS {
            assert!(!d.owner.is_empty(), "{} has no owner", d.name);
            assert!(!d.citation.is_empty(), "{} has no citation", d.name);
            assert!(
                d.reason.len() > 120,
                "{} has a token reason, not an auditable one",
                d.name
            );
        }
        // Every KnownBlind guard must point at a deferral that exists.
        for g in WASM_ABI_GUARDS {
            if let GuardExpectation::KnownBlind { deferral } = g.expectation {
                assert!(
                    WASM_ABI_DEFERRALS.iter().any(|d| d.name == deferral),
                    "guard `{}` cites deferral `{deferral}`, which is not registered",
                    g.name
                );
            }
        }
    }

    /// A guard whose needle no longer occurs, or occurs twice, is an ERROR, not
    /// a silent pass. Without this a fixture drift would disarm every guard
    /// while the suite stayed green.
    #[test]
    fn a_missing_needle_is_an_error() {
        let g = AbiGuard {
            name: "synthetic",
            fixture: "abi_frame",
            needle: &[0xde, 0xad, 0xbe, 0xef],
            patch: &[0x00, 0x00, 0x00, 0x00],
            expectation: GuardExpectation::MustRefute,
        };
        let f = fixture("abi_frame").expect("fixture");
        assert!(apply_guard(f.wasm, &g).is_err());
        // A one-byte needle occurs many times: ambiguous, so also an error.
        let ambiguous = AbiGuard {
            needle: &[0x20],
            patch: &[0x21],
            ..g
        };
        assert!(apply_guard(f.wasm, &ambiguous).is_err());
    }

    /// The intended frame layout of the frame fixture, computed from trust-ir
    /// alone, is what the documented rule says: an i32 at 0, an i64 at 8, a
    /// 12-byte array at 16, and a 32-byte frame.
    #[test]
    fn intended_frame_follows_the_documented_rule() {
        let m = trust_ir::parser::parse_module(FRAME_TIR).expect("parse");
        let im = intended_module(&m).expect("model");
        let f = &im.defined[0].frame;
        assert_eq!(
            f.slots,
            vec![
                IntendedSlot { size: 4, offset: 0 },
                IntendedSlot { size: 8, offset: 8 },
                IntendedSlot {
                    size: 12,
                    offset: 16
                },
            ]
        );
        assert_eq!(f.frame_size, 32);
    }

    /// The import-shifted index space, derived from trust-ir alone: two
    /// declarations at 0 and 1, two definitions at 2 and 3.
    #[test]
    fn intended_index_space_is_import_shifted() {
        let m = trust_ir::parser::parse_module(CALLS_TIR).expect("parse");
        let im = intended_module(&m).expect("model");
        assert_eq!(
            im.imports.iter().map(|i| i.index).collect::<Vec<_>>(),
            vec![0, 1]
        );
        assert_eq!(
            im.defined.iter().map(|d| d.index).collect::<Vec<_>>(),
            vec![2, 3]
        );
        let root = im.defined.iter().find(|d| d.name == "root").expect("root");
        assert_eq!(
            root.calls.iter().map(|c| c.target).collect::<Vec<_>>(),
            vec![0, 2, 1]
        );
    }

    // -----------------------------------------------------------------------
    // FORMAL discharge (ay) — the same guarded shape the rest of the wasm
    // suite uses. `z3_available()` is FALSE unless a CAPABLE independent
    // Alethe checker is installed, so these skip loudly rather than pretending.
    // -----------------------------------------------------------------------

    fn proof_authority_available() -> bool {
        crate::ay_bridge::z3_available()
    }

    /// FORMAL: every frame obligation is proven `unsat` by ay — correct for ALL
    /// entry stack pointers in the no-wrap window, not sampled.
    #[test]
    fn frame_obligations_proven_formally() {
        let obs = all_wasm_abi_obligations();
        if !proof_authority_available() {
            eprintln!(
                "frame_obligations_proven_formally: SKIPPED — no capable independent proof \
                 authority; 0 proven, 0 gapped, {} obligations not discharged formally",
                obs.len()
            );
            return;
        }
        let total = obs.len();
        let mut proven = 0usize;
        let mut gapped = 0usize;
        for ob in obs {
            let verdict = crate::wasm_formal::discharge(&ob);
            if verdict == crate::wasm_formal::Formal::Proven {
                proven += 1;
            } else if let Some(reason) = crate::wasm_formal::certification_gap_reason(&verdict) {
                crate::formal_gap::print_gap_skip(
                    &format!("wasm_abi_proofs `{}`", ob.name),
                    &reason,
                );
                gapped += 1;
            } else {
                panic!(
                    "obligation `{}` neither proven nor certification-gapped: {verdict:?}",
                    ob.name
                );
            }
        }
        eprintln!(
            "wasm_abi frame obligations: {proven}/{total} proven (unsat) via ay ({gapped} \
             certification-gap skipped)"
        );
        assert_eq!(proven + gapped, total);
    }
}
