// trust-cg-codegen/wasm/lower.rs - trust-ir -> WebAssembly lowering
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! trust-ir → WebAssembly lowering.
//!
//! Consumes **trust-ir** directly (the contract IR — no new IR, no intermediate
//! SSA) and builds a [`WasmModule`] via [`super::encode`].
//!
//! Supported subset (grows by slice):
//! - **Slice 0** — straight-line `Const` + `BinOp` add/sub/mul over i32/i64 + `Return`.
//! - **Slice 1** — `ICmp` comparisons and structured `if/else`.
//! - **Slice 1b** — **reducible loops** and general structured control flow, via
//!   the dominator-tree relooper of Ramsey, *"Beyond Relooper: Recursive
//!   Translation of Unstructured Control Flow to Structured Control Flow"*
//!   (ICFP 2022). The CFG is structured by recursing the dominator tree in
//!   reverse-postorder: a **loop header** (target of a back-edge) opens a wasm
//!   `loop`; a **merge node** (≥2 forward predecessors) opens a wasm `block`
//!   whose `end` is the join; each edge becomes either an inline continuation,
//!   a `br` to a loop label (back-edge / "continue"), or a `br` to a block
//!   label (forward merge / "break"/join). Branch depths are computed from an
//!   absolute open-label count so the enclosing `if` is counted correctly.
//!
//! Block-parameter SSA is lowered to wasm locals: an edge's args are written
//! into the target block's param locals before control transfers (phi
//! resolution). Writes are permutation-safe (all reads pushed, then sets in
//! reverse) so a back-edge that swaps induction variables is correct.
//!
//! An **irreducible** CFG (a cycle entered at more than one block) has no
//! nest of structured scopes as it stands; it is lowered as a dispatch loop
//! over a label local instead (`Lowering::emit_dispatch`).
//!
//! Fail-closed: any out-of-subset instruction is rejected explicitly, never
//! mis-lowered.
//!
//! # The narrow-carrier invariant (P3)
//!
//! WebAssembly has **no sub-32-bit value type**: `i8`/`i16` exist only as
//! memory access widths and as the `extendN_s` operators. So every trust-ir
//! value of a narrow integer type — `I8`, `U8`, `I16`, `U16` — is carried in a
//! wasm `i32` local, and this backend maintains ONE canonical form for that
//! carrier:
//!
//! > **Invariant N.** A value of a `w`-bit trust-ir integer type occupies the
//! > low `w` bits of its `i32` carrier. Bits `w..32` are the **sign extension**
//! > of bit `w-1` when the type is SIGNED (`I8`, `I16`) and **zero** when it is
//! > UNSIGNED (`U8`, `U16`). Equivalently: the carrier is
//! > `sext_w(v)` / `zext_w(v)` of the trust-ir value `v`.
//!
//! The invariant is what makes narrow code cheap: because every carrier is
//! already canonical, a signed compare is `i32.lt_s`, an unsigned compare is
//! `i32.lt_u`, an `i32.store8` writes the right byte, and `Eq`/`Ne` need no
//! masking at all. It is maintained by making every PRODUCER re-canonicalize:
//!
//! * `Const` — canonicalized at compile time into the emitted `i32.const`.
//! * `Load` — the sub-word load opcode carries the extension
//!   (`i32.load8_s` for `I8`, `i32.load8_u` for `U8`, …), so it lands canonical.
//! * `BinOp`/`UnOp` that can carry out of the narrow width (`Add`, `Sub`,
//!   `Mul`, `Shl`, `Neg`, `Not`, …) — re-canonicalized with `i32.extend8_s` /
//!   `i32.extend16_s` (signed) or `i32.and <mask>` (unsigned).
//! * `Cast` — the destination's canonical form is re-established explicitly.
//! * **Function parameters** — normalized in the prologue. An exported
//!   function's caller is outside the module and cannot be trusted to have
//!   canonicalized anything.
//! * **Call results** — normalized after the `call`, for the same reason: an
//!   imported host function's return value is the host's, not ours.
//!
//! and by making every CONSUMER that needs a particular *view* of the value ask
//! for it: `SDiv`/`SRem`/`AShr` and the signed comparisons read the value
//! SIGN-extended, `UDiv`/`URem`/`LShr` and the unsigned comparisons read it
//! ZERO-extended, and the two coincide with the carrier for exactly one
//! signedness — so the coercion is emitted only when they disagree.
//!
//! A width/op combination this scheme cannot legalize correctly is a named
//! error ([`WasmLowerError::NarrowLegalization`]), never a silent 32-bit
//! computation on a narrow type.
//!
//! `Bool` is a 1-bit member of the same family whose canonical carrier is
//! `0`/`1`. Its width is observable in exactly two places: a cast, which
//! reads it through [`int_repr_of`], and an ORDERED `ICmp`, where trust-ir
//! (like LLVM `i1`) reads `true` SIGNED as `-1` — so a signed predicate on
//! `Bool` executes as the reversed unsigned one ([`carrier_predicate`]).

use std::collections::{HashMap, HashSet};
use std::fmt;

use trust_ir::{
    BinOp, BlockId, CallingConv, CastOp, Constant, FCmpOp, FuncId, FuncTyId, Function, ICmpOp,
    Inst, Module, Ty, UnOp, ValueId,
};

use crate::module_merge::decode_body_global_addr_stub;
use trust_cg_lower::CodegenLicensePolicy;
use trust_cg_verify::wasm_cfg_proofs::ValKind;
use trust_cg_verify::wasm_local_tv::TvBody;
use trust_cg_verify::wasm_nowrap_premise::{NoWrapClaim, check_nowrap_premises};

mod abi;
mod calls;
mod captures;
mod emit;
mod ops;
mod pair;
mod storage;
mod value;
mod wide;

use abi::{ParamLane, WasmSig};
use captures::ParamCaptures;

/// Callee → its wasm function index, for direct calls.
type CallTargets = HashMap<FuncId, u32>;
/// FuncId → wasm function index of its INTERNAL entry: the functions an
/// object routes direct calls to through the internal ABI
/// ([`internal_abi_plan`]). A function in this map is defined with (or
/// imported at) its internal form; its `CallTargets` entry is the C-form
/// entry every function pointer names.
type InternalTargets = HashMap<FuncId, u32>;
/// (trust-ir signature, calling convention) → wasm type-section index, for
/// `call_indirect`. The convention is part of the key because it decides how
/// memory-carried parameters are passed (see [`abi`]).
type SigTypes = HashMap<(FuncTyId, CallingConv), u32>;
/// Module global → where its static-data image lives.
type GlobalAddrs = HashMap<trust_ir::value::GlobalId, DataAddr>;
/// (function, `Const` result) → where a memory-carried constant's image lives.
type ConstPool = HashMap<(FuncId, ValueId), DataAddr>;
/// Symbol name → the undefined data item a relocatable object imports it as.
type ExternData = HashMap<String, DataAddr>;

/// Where a piece of static data lives: its address, and — in a relocatable
/// object — the data item a relocation against it names.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct DataAddr {
    /// The absolute address (closed module) or the object-local address.
    pub addr: u32,
    /// The object data item, when the address must be relocated.
    pub item: Option<u32>,
}

/// Wasm function indices of the runtime helpers and library calls the
/// lowering can emit a `call` to.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct Helpers {
    /// `fmod` for `f64` `FRem`.
    pub fmod: Option<u32>,
    /// `fmodf` for `f32` `FRem`.
    pub fmodf: Option<u32>,
    /// The 128-bit division helper ([`super::helpers::divmod128_module`])
    /// for `UDiv`/`URem`/`SDiv`/`SRem` on `I128`/`U128`.
    pub divmod128: Option<u32>,
}

use super::encode::{
    FuncBody, FuncType, GlobalInit, Reloc, ValType, WASM_PAGE_BYTES, WasmEncodeError,
    WasmMemoryPolicy, WasmModule, emit_i32_const, emit_local_get, emit_memarg, emit_memory_grow,
    emit_memory_size, op, write_sleb128, write_uleb128,
};
use super::layout::{self, Carrier};
pub use super::opt::WasmLocalOptSummary;
use crate::jit_contract::{EvidenceStrength, ProofEvidenceVerdict};
use crate::pipeline::OptLevel;
use trust_cg_irmid::IrmidReport;
// Shared with the capture analysis (`trust_cg_irmid::escape`), so the lane and
// the analysis read a function's shape alike: `is_pointer_carrier` is the
// rustc bridge's POINTER-CARRIED aggregate convention (where an aggregate is
// expected but the operand is a pointer or a raw 64-bit address, the operand
// IS the address of the aggregate's bytes; memory-carried values are
// addresses of bytes already, so this is the same representation);
// `is_declaration` is true of a function this lane emits nothing of, so only an
// import can provide it: a bodyless one, or a trust-ir v41
// `AvailableExternally` one whether or not it carries a body (the body is
// available for inlining and defined elsewhere; this lane has no inliner, so
// emitting it would define a symbol the host already defines; the native
// adapter's `is_bodyless_external_declaration` agrees); `entry_reentered` says
// whether a branch targets the entry block, so that its parameters are written
// by this function (and staged through its frame) rather than bound once by
// the caller.
use trust_cg_irmid::escape::{entry_reentered, is_declaration, is_pointer_carrier};

use super::mid::{WasmInlineHints, WasmOptOptions};

/// Errors from lowering trust-ir to wasm. Fail-closed: anything outside the
/// supported subset is reported explicitly, never silently mis-lowered.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum WasmLowerError {
    /// A type with no wasm value-type mapping (in this slice).
    UnsupportedType(String),
    /// An instruction outside the supported subset.
    UnsupportedInst(String),
    /// Control flow outside the supported subset (a non-branch terminator, a
    /// `Switch` on an unsupported type, …).
    UnsupportedControlFlow(String),
    /// An operand referencing a value that was never defined/bound.
    UndefinedValue(String),
    /// A branch references a block id not present in the function.
    UndefinedBlock(String),
    /// Edge args / block params length mismatch (malformed SSA).
    ArityMismatch(String),
    /// A function whose declared entry block is absent.
    MissingEntry(String),
    /// The module carries no `target_info` at all (target-free IR). The wasm
    /// lane refuses it: target-free layout sizes pointers at 8 bytes while
    /// this lowering addresses memory through i32.
    MissingTargetInfo(String),
    /// The module's `target_info` is not the wasm32 shape (32-bit pointers,
    /// little-endian, a wasm32 triple).
    TargetMismatch(String),
    /// A function or call edge uses a calling convention other than
    /// `CallingConv::C`, the only convention this backend lowers.
    UnsupportedCallingConv(String),
    /// A signature-level ABI this lane cannot lower, refused with the shared
    /// native diagnostic: a variadic function definition
    /// (`[TCG-VARIADIC-DEFINITION]`, no `va_start`/`va_arg` lowering) or a
    /// `byval` parameter on a defined function or direct callee
    /// (`[TCG-BYVAL-ABI]`, no caller-copy lowering).
    UnsupportedAbi(String),
    /// A call whose signature (or SSA node) carries more than one result.
    /// The call lowering binds exactly one result, so a multi-result call
    /// would leave operands on the stack / locals unset — refused instead.
    UnsupportedMultiResultCall(String),
    /// The module touches linear memory (an `Alloca`, `Load`, or `Store`) but
    /// its [`WasmMemoryPolicy`] provides none.
    MemoryUnavailable(String),
    /// The module needs a shadow-stack frame but no stack base is negotiable:
    /// it lives in a host's imported memory, where the private
    /// `pages * 64KiB` top would be the HOST's data, and no
    /// [`WasmStackPolicy::HostBase`] import was configured.
    StackBaseUnavailable(String),
    /// A body-less (declaration-only) trust-ir function with no wasm binding:
    /// the [`WasmFuncImportPolicy`] does not import it, and it has no body to
    /// define.
    UnboundDeclaration(String),
    /// The trust-ir v41 codegen LICENSE refused a body: affirmatively
    /// ungated, licensed by a gate authority the caller's
    /// [`trust_cg_lower::CodegenLicensePolicy`] does not recognize, or
    /// claim-less under a policy that refuses claim-less bodies. The wasm lane
    /// walks `module.functions` itself rather than through the native adapter,
    /// so it applies the same policy decision here.
    CodegenLicense(String),
    /// trust-ir's own codegen admission refused the module, as every native
    /// entry refuses it ([`trust_cg_lower::validate_codegen_prerequisites`]):
    /// an evidence-bound license worn with no kernel-rechecked certificate, a
    /// license a failed translation validation revoked, an invalid
    /// refinement, a tainted value reaching a trusted sink, a `Dealloc`, and
    /// the other findings that admission consumes by name.
    CodegenAdmission(String),
    /// A trust-ir contract-surface construct this lane cannot honor and
    /// refuses rather than silently drop (see [`reject_unconsumed_v41_surface`]):
    /// everything the native adapter refuses target-independently
    /// (`global_asm!`, `#[naked]`, `ExternalWeak`, `Global.section`, import
    /// visibility, unrecognized completed obligations, external evidence
    /// inheritance), plus the two clauses specific to this lane — any
    /// `target_features` (no wasm feature is modeled) and, in a CLOSED module,
    /// an `AvailableExternally` GLOBAL (a closed module has no data-import
    /// channel: a global is an absolute linear-memory address, never an
    /// undefined symbol). A relocatable object has a symbol table and applies
    /// its own floor ([`reject_unconsumed_object_surface`]).
    ContractSurface(String),
    /// A defined function did not land on the function index the call targets
    /// were computed for — the import-shift invariant broke. Never expected;
    /// refused rather than emitted, because the consequence is calls landing
    /// on the wrong function.
    FunctionIndexDrift(String),
    /// A narrow (sub-32-bit) value could not be legalized into its `i32`
    /// carrier while preserving the narrow-carrier invariant (module docs,
    /// "Invariant N") — the width/op/signedness combination has no correct
    /// lowering here. Refused rather than computed at 32 bits, which would
    /// observe the untruncated high bits.
    NarrowLegalization(String),
    /// The module needs to write into, or resize, a linear memory it does not
    /// own, and the host has not granted it. The message names the policy that
    /// grants it.
    HostMemoryNotGranted(String),
    /// A module global has no byte image this backend can emit into a data
    /// segment (an initializer shape outside the supported set).
    UnsupportedConstantData(String),
    /// The module's static data does not fit the memory it was laid out in.
    StaticDataOverflow(String),
    /// A shadow-stack frame or its helper locals exceed the wasm32 domain.
    FrameLayoutOverflow(String),
    /// A lowered function would access bytes at a constant offset from its
    /// frame base that lie outside the frame it allocated for every offset
    /// the frame-bounds guard (`frame_bounds.rs`, over the emitted body)
    /// derives for the address — its caller's frame, or past the end of
    /// memory for the outermost frame. Never expected, and refused rather
    /// than emitted.
    FrameAccessOutOfBounds(String),
    /// A function exceeds an implementation limit every mainstream engine
    /// enforces (the JS-API "Limits": 50,000 locals, 1,000 parameters or
    /// results, a 7,654,321-byte body) even after its locals are coalesced.
    /// Refused rather than emitted as a module no engine will compile.
    ImplementationLimit(String),
    /// The encoder refused a structural request (index-space ordering,
    /// initializer shape, absent memory).
    Encode(WasmEncodeError),
    /// The P4 CFG STRUCTURAL invariant was REFUTED on the bytes this compile
    /// just emitted: a `br` depth that names no live label, an operand-stack
    /// height or type that disagrees at a join, an unmatched scope.
    /// `trust_cg_verify::wasm_cfg_proofs::check_module_structure` rebuilds that
    /// judgement from the emitted bytes with its own decoder and the spec's
    /// §7.3.2 algorithm.
    ///
    /// Never expected, and REFUSED rather than emitted, for the same reason as
    /// [`WasmLowerError::FunctionIndexDrift`]: a module whose structure the spec
    /// algorithm rejects is one the engine may reject, or worse, run with
    /// control landing somewhere the relooper did not intend. Raised only on the
    /// evidence-carrying route
    /// ([`compile_module_with_evidence_and_policy`]) — an INCONCLUSIVE verdict
    /// never raises it and never earns credit either.
    StructuralInvariantRefuted(String),
    /// The function is not well-formed strict SSA as this lane depends on it:
    /// a reachable use its definition does not dominate, a value defined
    /// twice, or a branch argument whose type is not its target parameter's.
    /// The storage rules (alias homes, fixed `Alloca` slots) are sound only
    /// under dominance, so such input is refused, never lowered.
    IllFormedSsa(String),
    /// WS7.3: trust-ir's own codegen validator refused the module at this
    /// ingestion entry ([`trust_cg_lower::admit_module`]) with findings no
    /// named arm of this backend consumes. Carries every finding.
    InvalidTrustIr(trust_cg_lower::InvalidTrustIr),
}

impl From<WasmEncodeError> for WasmLowerError {
    fn from(e: WasmEncodeError) -> Self {
        WasmLowerError::Encode(e)
    }
}

impl fmt::Display for WasmLowerError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use WasmLowerError::*;
        match self {
            UnsupportedType(m) => write!(f, "unsupported type for wasm lowering: {m}"),
            UnsupportedInst(m) => write!(f, "unsupported instruction for wasm lowering: {m}"),
            UnsupportedControlFlow(m) => {
                write!(f, "unsupported control flow for wasm lowering: {m}")
            }
            UndefinedValue(m) => write!(f, "use of undefined value in wasm lowering: {m}"),
            UndefinedBlock(m) => write!(f, "branch to undefined block in wasm lowering: {m}"),
            ArityMismatch(m) => write!(f, "edge arg / block-param arity mismatch: {m}"),
            MissingEntry(m) => write!(f, "function has no entry block: {m}"),
            MissingTargetInfo(m) => write!(f, "module has no target_info: {m}"),
            TargetMismatch(m) => write!(f, "module target_info is not the wasm32 shape: {m}"),
            UnsupportedCallingConv(m) => {
                write!(f, "unsupported calling convention for wasm lowering: {m}")
            }
            UnsupportedAbi(m) => write!(f, "unsupported ABI for wasm lowering: {m}"),
            UnsupportedMultiResultCall(m) => {
                write!(f, "unsupported multi-result call in wasm lowering: {m}")
            }
            MemoryUnavailable(m) => write!(f, "wasm memory policy provides no memory: {m}"),
            StackBaseUnavailable(m) => write!(f, "no negotiable wasm shadow-stack base: {m}"),
            UnboundDeclaration(m) => write!(f, "unbound trust-ir declaration: {m}"),
            CodegenLicense(m) => write!(f, "trust-ir v41 codegen license refused: {m}"),
            CodegenAdmission(m) => write!(f, "codegen admission refused the module: {m}"),
            ContractSurface(m) => write!(f, "trust-ir contract surface refused: {m}"),
            FunctionIndexDrift(m) => write!(f, "wasm function index drift: {m}"),
            NarrowLegalization(m) => write!(f, "narrow value cannot be legalized to i32: {m}"),
            HostMemoryNotGranted(m) => write!(f, "host linear memory not granted: {m}"),
            UnsupportedConstantData(m) => write!(f, "global has no emittable byte image: {m}"),
            StaticDataOverflow(m) => write!(f, "static data does not fit linear memory: {m}"),
            FrameLayoutOverflow(m) => write!(f, "wasm shadow-stack frame layout overflows: {m}"),
            FrameAccessOutOfBounds(m) => {
                write!(f, "wasm frame access outside the allocated frame: {m}")
            }
            ImplementationLimit(m) => write!(f, "wasm function exceeds an engine limit: {m}"),
            Encode(e) => write!(f, "wasm module encoding refused: {e}"),
            StructuralInvariantRefuted(m) => write!(
                f,
                "wasm CFG structural invariant REFUTED on the emitted module: {m}"
            ),
            IllFormedSsa(m) => write!(f, "trust-ir input is not well-formed SSA: {m}"),
            InvalidTrustIr(refusal) => write!(f, "{refusal}"),
        }
    }
}

impl std::error::Error for WasmLowerError {}

/// Map a trust-ir scalar type to a wasm value type. Sub-32-bit integers carry
/// in `i32` (module docs, "Invariant N"); pointer-like types are wasm32
/// addresses (i32).
fn valtype_of(ty: &Ty) -> Result<ValType, WasmLowerError> {
    layout::scalar_valtype(ty).ok_or_else(|| WasmLowerError::UnsupportedType(format!("{ty:?}")))
}

/// How an integer-like trust-ir scalar sits in its wasm carrier: its trust-ir
/// bit width, its signedness (which fixes the CANONICAL carrier form — see
/// "Invariant N"), and the carrier value type.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct IntRepr {
    bits: u32,
    signed: bool,
    carrier: ValType,
}

impl IntRepr {
    const fn new(bits: u32, signed: bool, carrier: ValType) -> Self {
        Self {
            bits,
            signed,
            carrier,
        }
    }

    /// Width of the wasm carrier in bits.
    fn carrier_bits(self) -> u32 {
        match self.carrier {
            ValType::I32 => 32,
            ValType::I64 => 64,
            // Float carriers never appear in an `IntRepr`.
            ValType::F32 | ValType::F64 => 0,
        }
    }

    /// True when the value occupies FEWER bits than its carrier, so the carrier
    /// has a canonical form to maintain.
    fn is_narrow(self) -> bool {
        self.bits < self.carrier_bits()
    }

    /// The low-`bits` mask, as the `i32` immediate an `i32.and` would use.
    fn mask_i32(self) -> i32 {
        debug_assert!(self.bits < 32);
        ((1u64 << self.bits) - 1) as i32
    }

    /// Canonicalize a trust-ir integer VALUE into its carrier bit pattern.
    fn carrier_value(self, v: i128) -> i64 {
        let bits = self.bits;
        let masked = if bits >= 128 {
            v as u128
        } else {
            (v as u128) & ((1u128 << bits) - 1)
        };
        if self.signed && bits < 128 && masked >> (bits - 1) & 1 == 1 {
            // Sign-extend out of `bits` into the full carrier.
            (masked | !((1u128 << bits) - 1)) as i64
        } else {
            masked as i64
        }
    }
}

/// The integer representation of `ty`, or `None` for non-integer scalars.
///
/// Pointers are 32-bit unsigned wasm32 addresses; `Bool` is a 1-bit unsigned
/// value (its canonical carrier is `0`/`1`), which is what makes a
/// `Cast::Trunc` into `Bool` an actual truncation rather than an identity.
fn int_repr_of(ty: &Ty) -> Option<IntRepr> {
    use ValType::{I32, I64};
    Some(match ty {
        Ty::Bool => IntRepr::new(1, false, I32),
        Ty::I8 => IntRepr::new(8, true, I32),
        Ty::U8 => IntRepr::new(8, false, I32),
        Ty::I16 => IntRepr::new(16, true, I32),
        Ty::U16 => IntRepr::new(16, false, I32),
        Ty::I32 => IntRepr::new(32, true, I32),
        Ty::U32 => IntRepr::new(32, false, I32),
        Ty::I64 => IntRepr::new(64, true, I64),
        Ty::U64 => IntRepr::new(64, false, I64),
        // wasm32: pointer-sized integers are 32-bit; `char` is a 32-bit
        // unsigned scalar value.
        Ty::Isize => IntRepr::new(32, true, I32),
        Ty::Usize | Ty::Char => IntRepr::new(32, false, I32),
        Ty::Ptr
        | Ty::PtrConst(_)
        | Ty::PtrMut(_)
        | Ty::Ref(_)
        | Ty::RefMut(_)
        | Ty::Rc(_)
        | Ty::Func(_) => IntRepr::new(32, false, I32),
        _ => return None,
    })
}

/// The narrow representation of `ty` for ARITHMETIC and COMPARISON — the four
/// sub-word integer types whose carrier form is load-bearing.
///
/// `Bool` is deliberately excluded: it is only ever produced as a canonical
/// `0`/`1`, so its arithmetic (`And`/`Or`/`Xor` on booleans) needs no masking,
/// and treating it as a 1-bit integer here would emit dead re-canonicalization
/// on every boolean op. Casts still see `Bool`'s real width through
/// [`int_repr_of`], and ordered comparisons through [`carrier_predicate`].
fn narrow_of(ty: &Ty) -> Option<IntRepr> {
    match ty {
        Ty::I8 | Ty::U8 | Ty::I16 | Ty::U16 => int_repr_of(ty),
        _ => None,
    }
}

/// Whether `ty` is an integer an int<->float conversion reads or writes: the
/// reference interpreter's `int_shape` (every integer width, the
/// pointer-sized integers and `char`) — never `bool` or a pointer.
fn is_convertible_int(ty: &Ty) -> bool {
    matches!(
        ty,
        Ty::I8
            | Ty::U8
            | Ty::I16
            | Ty::U16
            | Ty::I32
            | Ty::U32
            | Ty::I64
            | Ty::U64
            | Ty::I128
            | Ty::U128
            | Ty::Isize
            | Ty::Usize
            | Ty::Char
    )
}

/// Which full-width VIEW of a narrow carrier an operation reads.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum IntView {
    /// The value's `bits` sign-extended into the carrier.
    Signed,
    /// The value's `bits` zero-extended into the carrier.
    Unsigned,
}

/// One linear-memory access: how many bits move, and (for a load) whether the
/// loaded bits are sign- or zero-extended into the carrier.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct MemAccess {
    /// Access width in bits: 8, 16, 32, or 64.
    bits: u32,
    /// Sign-extend the loaded bits (ignored by stores, which write low bits).
    signed: bool,
}

/// The `(load, store, natural-alignment exponent)` triple for one access width
/// at one carrier value type — the complete WebAssembly memory-instruction
/// table (Core Specification, "Memory Instructions", opcodes `0x28..=0x3e`).
///
/// The alignment exponent is `log2` of the access size in bytes, which is the
/// maximum the spec admits for that instruction (a memarg alignment larger than
/// the access size is a validation error; a smaller one is merely a weaker
/// hint, since wasm permits unaligned access).
fn mem_ops_for(carrier: ValType, access: MemAccess) -> Result<(u8, u8, u32), WasmLowerError> {
    use ValType::{F32, F64, I32, I64};
    let ops = match (carrier, access.bits, access.signed) {
        (I32, 8, true) => (op::I32_LOAD8_S, op::I32_STORE8, 0),
        (I32, 8, false) => (op::I32_LOAD8_U, op::I32_STORE8, 0),
        (I32, 16, true) => (op::I32_LOAD16_S, op::I32_STORE16, 1),
        (I32, 16, false) => (op::I32_LOAD16_U, op::I32_STORE16, 1),
        (I32, 32, _) => (op::I32_LOAD, op::I32_STORE, 2),
        (I64, 8, true) => (op::I64_LOAD8_S, op::I64_STORE8, 0),
        (I64, 8, false) => (op::I64_LOAD8_U, op::I64_STORE8, 0),
        (I64, 16, true) => (op::I64_LOAD16_S, op::I64_STORE16, 1),
        (I64, 16, false) => (op::I64_LOAD16_U, op::I64_STORE16, 1),
        (I64, 32, true) => (op::I64_LOAD32_S, op::I64_STORE32, 2),
        (I64, 32, false) => (op::I64_LOAD32_U, op::I64_STORE32, 2),
        (I64, 64, _) => (op::I64_LOAD, op::I64_STORE, 3),
        (F32, 32, _) => (op::F32_LOAD, op::F32_STORE, 2),
        (F64, 64, _) => (op::F64_LOAD, op::F64_STORE, 3),
        _ => {
            return Err(WasmLowerError::UnsupportedInst(format!(
                "no wasm memory instruction moves {} bit(s) to/from a {carrier:?}",
                access.bits,
            )));
        }
    };
    Ok(ops)
}

/// The load/store opcode pair and natural-alignment exponent for a trust-ir
/// type: the sub-word opcodes for a narrow integer (carrying the extension its
/// carrier form demands), the float opcodes for `F32`/`F64`, and the plain
/// `i32`/`i64` pair for everything else.
fn mem_ops(ty: &Ty) -> Result<(u8, u8, u32), WasmLowerError> {
    let carrier = valtype_of(ty)?;
    let access = match int_repr_of(ty) {
        Some(repr) if repr.bits == 1 => {
            // `Bool` is a one-byte object in memory; the byte's low bit is the
            // value, and both `0` and `1` round-trip through a zero-extending
            // byte load. A wider load would read neighbouring bytes.
            MemAccess {
                bits: 8,
                signed: false,
            }
        }
        Some(repr) => MemAccess {
            bits: repr.bits,
            signed: repr.signed,
        },
        None => match carrier {
            ValType::F32 => MemAccess {
                bits: 32,
                signed: false,
            },
            ValType::F64 => MemAccess {
                bits: 64,
                signed: false,
            },
            other => {
                return Err(WasmLowerError::UnsupportedInst(format!(
                    "load/store of {ty:?} (carrier {other:?})"
                )));
            }
        },
    };
    mem_ops_for(carrier, access)
}

/// Round `n` up to a multiple of `align` (a power of two).
fn align_up(n: u32, align: u32) -> Option<u32> {
    n.checked_add(align - 1).map(|n| n & !(align - 1))
}

/// The full-width VIEW each operand of an integer `BinOp` is read at when the
/// operand type is narrow, or `None` when only the low `bits` matter and the
/// carrier can be used as it is.
///
/// This is where the narrow-carrier invariant pays for itself: an operation
/// that reads a value's SIGN (`SDiv`, `SRem`, `AShr`) needs the sign-extended
/// view and an operation that reads its MAGNITUDE (`UDiv`, `URem`, `LShr`)
/// needs the zero-extended view — and each is free for exactly one signedness.
/// `Add`/`Sub`/`Mul`/`And`/`Or`/`Xor`/`Shl` are congruences on the low `bits`,
/// so they read the carrier directly.
///
/// The shift AMOUNT is read zero-extended: the reference interpreter reduces it
/// from `rhs.raw`, the operand's zero-extended `bits`-wide pattern.
fn binop_operand_views(bin: BinOp) -> (Option<IntView>, Option<IntView>) {
    use IntView::{Signed, Unsigned};
    match bin {
        BinOp::SDiv | BinOp::SRem => (Some(Signed), Some(Signed)),
        BinOp::UDiv | BinOp::URem => (Some(Unsigned), Some(Unsigned)),
        BinOp::AShr => (Some(Signed), Some(Unsigned)),
        BinOp::LShr => (Some(Unsigned), Some(Unsigned)),
        BinOp::Shl => (None, Some(Unsigned)),
        _ => (None, None),
    }
}

/// The full-width VIEW each operand of an `ICmp` is read at when the operand
/// type is narrow. `Eq`/`Ne` need none: two canonical carriers are equal
/// exactly when the values they carry are.
fn icmp_operand_view(cmp: ICmpOp) -> Option<IntView> {
    use ICmpOp::*;
    match cmp {
        Eq | Ne => None,
        Slt | Sle | Sgt | Sge => Some(IntView::Signed),
        Ult | Ule | Ugt | Uge => Some(IntView::Unsigned),
    }
}

/// The predicate an integer comparison at `ty` executes on the canonical
/// carrier. `Bool` is a 1-bit integer to an ordered predicate — the reference
/// interpreter (`eval_bool_icmp`), trust-cg's SMT source model and LLVM `i1`
/// all read `true` signed as `-1` — so on the `0`/`1` carrier every signed
/// order is the REVERSED unsigned order (`slt` is `ugt`, `sle` is `uge`, …).
/// Every other type's predicate is its own.
fn carrier_predicate(cmp: ICmpOp, ty: &Ty) -> ICmpOp {
    use ICmpOp::*;
    if *ty != Ty::Bool {
        return cmp;
    }
    match cmp {
        Slt => Ugt,
        Sle => Uge,
        Sgt => Ult,
        Sge => Ule,
        other => other,
    }
}

/// Wasm opcode for an integer `BinOp` at a value type (Slice 0 subset).
fn int_binop_opcode(bin: BinOp, vt: ValType) -> Result<u8, WasmLowerError> {
    let code = match (bin, vt) {
        (BinOp::Add, ValType::I32) => op::I32_ADD,
        (BinOp::Sub, ValType::I32) => op::I32_SUB,
        (BinOp::Mul, ValType::I32) => op::I32_MUL,
        (BinOp::SDiv, ValType::I32) => op::I32_DIV_S,
        (BinOp::UDiv, ValType::I32) => op::I32_DIV_U,
        (BinOp::SRem, ValType::I32) => op::I32_REM_S,
        (BinOp::URem, ValType::I32) => op::I32_REM_U,
        (BinOp::Add, ValType::I64) => op::I64_ADD,
        (BinOp::Sub, ValType::I64) => op::I64_SUB,
        (BinOp::Mul, ValType::I64) => op::I64_MUL,
        (BinOp::SDiv, ValType::I64) => op::I64_DIV_S,
        (BinOp::UDiv, ValType::I64) => op::I64_DIV_U,
        (BinOp::SRem, ValType::I64) => op::I64_REM_S,
        (BinOp::URem, ValType::I64) => op::I64_REM_U,
        (BinOp::And, ValType::I32) => op::I32_AND,
        (BinOp::Or, ValType::I32) => op::I32_OR,
        (BinOp::Xor, ValType::I32) => op::I32_XOR,
        (BinOp::Shl, ValType::I32) => op::I32_SHL,
        (BinOp::AShr, ValType::I32) => op::I32_SHR_S,
        (BinOp::LShr, ValType::I32) => op::I32_SHR_U,
        (BinOp::And, ValType::I64) => op::I64_AND,
        (BinOp::Or, ValType::I64) => op::I64_OR,
        (BinOp::Xor, ValType::I64) => op::I64_XOR,
        (BinOp::Shl, ValType::I64) => op::I64_SHL,
        (BinOp::AShr, ValType::I64) => op::I64_SHR_S,
        (BinOp::LShr, ValType::I64) => op::I64_SHR_U,
        // IEEE-754 float arithmetic (round-to-nearest-ties-to-even).
        (BinOp::FAdd, ValType::F32) => op::F32_ADD,
        (BinOp::FSub, ValType::F32) => op::F32_SUB,
        (BinOp::FMul, ValType::F32) => op::F32_MUL,
        (BinOp::FDiv, ValType::F32) => op::F32_DIV,
        (BinOp::FAdd, ValType::F64) => op::F64_ADD,
        (BinOp::FSub, ValType::F64) => op::F64_SUB,
        (BinOp::FMul, ValType::F64) => op::F64_MUL,
        (BinOp::FDiv, ValType::F64) => op::F64_DIV,
        _ => {
            return Err(WasmLowerError::UnsupportedInst(format!(
                "BinOp::{bin:?} on {vt:?} (supported: int add/sub/mul/div/rem/and/or/xor/shl/shr; \
                 float add/sub/mul/div)"
            )));
        }
    };
    Ok(code)
}

/// Wasm opcode for an integer comparison `ICmp` at an operand value type.
/// Result is always i32 (a wasm boolean).
fn icmp_opcode(cmp: ICmpOp, vt: ValType) -> Result<u8, WasmLowerError> {
    use ICmpOp::*;
    use ValType::{I32, I64};
    let code = match (cmp, vt) {
        (Eq, I32) => op::I32_EQ,
        (Ne, I32) => op::I32_NE,
        (Slt, I32) => op::I32_LT_S,
        (Sle, I32) => op::I32_LE_S,
        (Sgt, I32) => op::I32_GT_S,
        (Sge, I32) => op::I32_GE_S,
        (Ult, I32) => op::I32_LT_U,
        (Ule, I32) => op::I32_LE_U,
        (Ugt, I32) => op::I32_GT_U,
        (Uge, I32) => op::I32_GE_U,
        (Eq, I64) => op::I64_EQ,
        (Ne, I64) => op::I64_NE,
        (Slt, I64) => op::I64_LT_S,
        (Sle, I64) => op::I64_LE_S,
        (Sgt, I64) => op::I64_GT_S,
        (Sge, I64) => op::I64_GE_S,
        (Ult, I64) => op::I64_LT_U,
        (Ule, I64) => op::I64_LE_U,
        (Ugt, I64) => op::I64_GT_U,
        (Uge, I64) => op::I64_GE_U,
        _ => {
            return Err(WasmLowerError::UnsupportedInst(format!(
                "ICmp::{cmp:?} on {vt:?} (supported: integer comparisons on i32/i64)"
            )));
        }
    };
    Ok(code)
}

/// Look up the wasm local slot bound to an SSA value.
fn slot(
    locals: &HashMap<ValueId, (u32, ValType)>,
    v: ValueId,
) -> Result<(u32, ValType), WasmLowerError> {
    locals
        .get(&v)
        .copied()
        .ok_or_else(|| WasmLowerError::UndefinedValue(format!("{v:?}")))
}

/// The trust-ir types of an instruction's results, in result order.
///
/// The lowering needs the trust-ir type, not only its wasm carrier: a narrow
/// value's SIGNEDNESS is what fixes its canonical carrier form (invariant N),
/// and a memory-carried value's type is what fixes its layout.
fn result_tys(inst: &Inst, module: &Module) -> Result<Vec<Ty>, WasmLowerError> {
    result_tys_with(inst, module, &|_| None)
}

/// Whether `ty` is an aggregate a producer may carry by POINTER (see
/// [`is_pointer_carrier`]).
fn is_aggregate_ty(ty: &Ty) -> bool {
    matches!(
        ty,
        Ty::Struct(_) | Ty::Tuple(_) | Ty::Array(_, _) | Ty::Enum(_) | Ty::I128 | Ty::U128
    )
}

/// The result types of every node of `func` that binds results, keyed by
/// `(block index, node index)`, typed to a fixpoint: an `ExtractField` over a
/// pointer carrier is typed by its operand, which the block order may list
/// later. A node still waiting on an untyped operand is absent (its declared
/// [`result_tys`] apply).
fn node_result_types(
    func: &Function,
    module: &Module,
) -> Result<HashMap<(usize, usize), Vec<Ty>>, WasmLowerError> {
    let mut known: HashMap<ValueId, Ty> = HashMap::new();
    for block in &func.blocks {
        for (vid, ty) in &block.params {
            known.insert(*vid, ty.clone());
        }
    }
    let mut node_tys: HashMap<(usize, usize), Vec<Ty>> = HashMap::new();
    loop {
        let mut progress = false;
        for (bi, block) in func.blocks.iter().enumerate() {
            for (ni, node) in block.body.iter().enumerate() {
                if node.results.is_empty() || node_tys.contains_key(&(bi, ni)) {
                    continue;
                }
                let waiting = matches!(&node.inst, Inst::ExtractField { aggregate, .. }
                    if !known.contains_key(aggregate));
                if waiting {
                    continue;
                }
                let tys = result_tys_with(&node.inst, module, &|v| known.get(&v).cloned())?;
                for (&r, t) in node.results.iter().zip(&tys) {
                    known.insert(r, t.clone());
                }
                node_tys.insert((bi, ni), tys);
                progress = true;
            }
        }
        if !progress {
            break;
        }
    }
    Ok(node_tys)
}

/// The type the wasm lane gives every value of `func`: block parameters as
/// declared, results as this lane types them (including the pointer-carried
/// `ExtractField` spelling, whose declared type is the aggregate's). A
/// producer that rewrites a module for this lane types it with this.
pub fn value_types(
    module: &Module,
    func: &Function,
) -> Result<HashMap<ValueId, Ty>, WasmLowerError> {
    let node_tys = node_result_types(func, module)?;
    typed_values(func, module, &node_tys)
}

/// [`value_types`] over already-computed [`node_result_types`].
fn typed_values(
    func: &Function,
    module: &Module,
    node_tys: &HashMap<(usize, usize), Vec<Ty>>,
) -> Result<HashMap<ValueId, Ty>, WasmLowerError> {
    let mut out = HashMap::new();
    for (bi, block) in func.blocks.iter().enumerate() {
        for (vid, ty) in &block.params {
            out.insert(*vid, ty.clone());
        }
        for (ni, node) in block.body.iter().enumerate() {
            if node.results.is_empty() {
                continue;
            }
            let tys = match node_tys.get(&(bi, ni)) {
                Some(tys) => tys.clone(),
                None => result_tys(&node.inst, module)?,
            };
            for (&r, t) in node.results.iter().zip(tys) {
                out.insert(r, t);
            }
        }
    }
    Ok(out)
}

/// Whether `ExtractField { ty: declared, aggregate, field }` over a BY-VALUE
/// operand of type `operand` is the rustc bridge's lane REINTERPRETATION (its
/// `store_incoming_aggregate_param` copies an incoming aggregate argument into
/// its slot as the slot's uniform lanes): the declared type is a record or
/// array of exactly the operand's byte size, lane `field` of the operand is
/// not of the declared type (so the trust-ir spelling, which declares the
/// FIELD type, does not apply), and the result is lane `field` of the DECLARED
/// type read over the operand's bytes. Both types are memory-carried here, so
/// the operand's bytes are its memory image and the lane is an in-bounds
/// view of them.
fn extract_reinterprets(module: &Module, declared: &Ty, operand: &Ty, field: u32) -> bool {
    let record = |t: &Ty| matches!(t, Ty::Struct(_) | Ty::Tuple(_) | Ty::Array(_, _));
    if !record(declared) || !record(operand) || declared == operand {
        return false;
    }
    if let Ok(layout::Lane::At(part)) = layout::lane(module, operand, field, declared)
        && &part.ty == declared
    {
        return false;
    }
    match (
        layout::size_align(module, declared),
        layout::size_align(module, operand),
    ) {
        (Ok((declared_size, _)), Ok((operand_size, _))) => {
            declared_size == operand_size && declared_size > 0
        }
        _ => false,
    }
}

/// Whether a value carried as `value` may be read or written as a lane of
/// type-carrier `lane` without changing how many bytes move: the same scalar
/// value type, or the same memory size (a pair moves 16 bytes), or both
/// zero-sized. A lane access that fails this would move more (or fewer)
/// bytes than the lane holds.
fn lane_carriers_agree(value: layout::Carrier, lane: layout::Carrier) -> bool {
    match (value, lane) {
        (layout::Carrier::Void, layout::Carrier::Void) => true,
        (layout::Carrier::Scalar(a), layout::Carrier::Scalar(b)) => a == b,
        (layout::Carrier::Mem { size: a, .. }, layout::Carrier::Mem { size: b, .. }) => a == b,
        (layout::Carrier::Pair, layout::Carrier::Mem { size, .. }) => size == 16,
        _ => false,
    }
}

/// [`result_tys`] with the types of operands known so far. The one
/// operand-dependent case is the historical `ExtractField` spelling, which
/// declares the AGGREGATE type (not the field type) and whose result is lane
/// `field`: over a pointer carrier, over a by-value aggregate whose own type
/// is the declared one (no field can have its containing aggregate's type, so
/// that spelling is unambiguous), or over a by-value aggregate the declared
/// type reinterprets ([`extract_reinterprets`]).
fn result_tys_with(
    inst: &Inst,
    module: &Module,
    operand_ty: &dyn Fn(ValueId) -> Option<Ty>,
) -> Result<Vec<Ty>, WasmLowerError> {
    let one = |t: Ty| Ok(vec![t]);
    if let Inst::ExtractField {
        ty,
        aggregate,
        field,
    } = inst
        && is_aggregate_ty(ty)
        && let Some(operand) = operand_ty(*aggregate)
        && (is_pointer_carrier(&operand)
            || &operand == ty
            || extract_reinterprets(module, ty, &operand, *field))
    {
        return match layout::lane(module, ty, *field, &Ty::Unit) {
            Ok(layout::Lane::At(part)) => one(part.ty),
            Ok(layout::Lane::EnumTag(image)) => one(image.tag_ty),
            Err(_) => Err(WasmLowerError::UnsupportedInst(format!(
                "ExtractField lane {field} of declared {ty:?} over operand {operand:?} is out \
                 of range"
            ))),
        };
    }
    match inst {
        Inst::BinOp { ty, .. } | Inst::UnOp { ty, .. } => one(ty.clone()),
        // `(value, overflowed)`.
        Inst::Overflow { ty, .. } => Ok(vec![ty.clone(), Ty::Bool]),
        // wasm integer and float compares both yield an i32 0/1.
        Inst::ICmp { .. } | Inst::FCmp { .. } => one(Ty::Bool),
        Inst::Cast { dst_ty, .. } => one(dst_ty.clone()),
        // A function-pointer constant is a table index (a wasm32 address).
        Inst::Const {
            value: Constant::FnDef(_),
            ..
        } => one(Ty::Ptr),
        Inst::Const { ty, .. }
        | Inst::Copy { ty, .. }
        | Inst::Select { ty, .. }
        | Inst::Undef { ty }
        | Inst::Load { ty, .. }
        | Inst::AtomicLoad { ty, .. }
        | Inst::AtomicRMW { ty, .. }
        | Inst::ExtractField { ty, .. }
        | Inst::InsertField { ty, .. }
        | Inst::ExtractElement { ty, .. }
        | Inst::InsertElement { ty, .. }
        | Inst::MakeAggregate { ty, .. }
        | Inst::ArraySplat { ty, .. } => one(ty.clone()),
        Inst::CmpXchg { ty, .. } => Ok(vec![ty.clone(), Ty::Bool]),
        // Pointers: a frame slot, a computed element address, a static-data
        // address, a borrow of a pointer.
        Inst::Alloca { .. }
        | Inst::GEP { .. }
        | Inst::GlobalAddr { .. }
        | Inst::NullPtr
        | Inst::Borrow { .. }
        | Inst::BorrowMut { .. }
        | Inst::PtrData { .. } => one(Ty::Ptr),
        Inst::PtrMetadata { metadata_ty, .. } => one(metadata_ty.clone()),
        Inst::PtrFromParts { ptr_ty, .. } => one(ptr_ty.clone()),
        // trust-ir v74: the operand's pointer, unchanged, at `ptr_ty`.
        Inst::BoxDeref { ptr_ty, .. } => one(ptr_ty.clone()),
        Inst::Call { callee, .. } => module
            .function_by_id(*callee)
            .and_then(|f| module.func_type(f.ty))
            .map(|ft| ft.returns.clone())
            .ok_or_else(|| WasmLowerError::UnsupportedInst(format!("Call to unknown {callee:?}"))),
        Inst::CallIndirect { sig, .. } => module
            .func_type(*sig)
            .map(|ft| ft.returns.clone())
            .ok_or_else(|| WasmLowerError::UnsupportedInst(format!("unknown signature {sig:?}"))),
        other => Err(WasmLowerError::UnsupportedInst(format!(
            "result-producing {other:?}"
        ))),
    }
}

/// Run-length encode local declarations into wasm `(count, type)` runs.
pub(super) fn run_length_encode(types: &[ValType]) -> Vec<(u32, ValType)> {
    let mut runs: Vec<(u32, ValType)> = Vec::new();
    for &vt in types {
        match runs.last_mut() {
            Some((count, last)) if *last == vt => *count += 1,
            _ => runs.push((1, vt)),
        }
    }
    runs
}

/// Whether a memory-carried result of `inst` OWNS storage (a home slot in the
/// frame, written only by this instruction) or ALIASES storage something else
/// owns.
///
/// Aliasing is sound because every memory-carried SSA value's bytes are
/// written only when its own definition executes: an alias `r` of an operand
/// `x` is defined after `x` (x's definition dominates r's), and in SSA any path
/// that re-executes x's definition before reaching a use of `r` also
/// re-executes `r`'s. So a use of `r` always sees the `x` it was derived from.
///
/// The bridge's write-through `InsertField` owns nothing either, and a
/// read-through `ExtractField` / `ExtractElement` (over a pointer carrier)
/// DOES own its result's home, although this predicate cannot see either: both
/// depend on the operand's type ([`owns_storage_typed`]). The argument above
/// covers only an operand that is itself an SSA value; a pointee is not one.
fn owns_storage(inst: &Inst) -> bool {
    !matches!(
        inst,
        Inst::Const { .. }
            | Inst::Copy { .. }
            | Inst::Select { .. }
            | Inst::ExtractField { .. }
            | Inst::ExtractElement { .. }
    )
}

/// Whether `inst` is the rustc bridge's write-THROUGH `InsertField` (the
/// native adapter's `insert_field_writes_through`): its aggregate operand is a
/// POINTER carrier (see [`is_pointer_carrier`]), the lane stores the field
/// through it, and the result is that same pointer. Such a result owns no
/// storage — the bytes it names are the pointee's — so it gets no home slot.
/// `types` is the lane's typing of the function ([`value_types`]); this is the
/// same test `lower_insert_field` applies to choose the write-through form.
fn insert_writes_through(inst: &Inst, types: &HashMap<ValueId, Ty>) -> bool {
    matches!(inst, Inst::InsertField { ty, aggregate, .. }
        if types.get(aggregate).is_some_and(|t| t != ty && is_pointer_carrier(t)))
}

/// Whether `inst` is a READ-THROUGH `ExtractField` / `ExtractElement`: its
/// aggregate operand is a POINTER carrier, so the lane is loaded from the
/// pointee, as a `Load` would. A memory-carried result of such a read OWNS a
/// home and copies the lane's bytes there (`value.rs`, `read_part`), exactly
/// as a `Load` result does: the pointee is not an SSA value, so a later
/// write-through `InsertField`, `Store` or call may overwrite those bytes while
/// the result is live, and an alias would then read the NEW bytes. MEASURED
/// before this predicate existed (wasm32, every opt level): `let old = p.b;
/// p.b = n; f(old)` over a `&mut` struct whose `b` is a `u128` handed `f` the
/// value `n` — which made std's `RangeInclusive<u128>::spec_try_rfold`
/// (`mem::replace(&mut self.end, n)`) fold `end - 1` in place of `end`.
/// `types` is the lane's typing of the function ([`value_types`]); this is the
/// same test `lower_extract_field` applies (`Lowering::pointer_carried`).
fn extract_reads_through(inst: &Inst, types: &HashMap<ValueId, Ty>) -> bool {
    match inst {
        Inst::ExtractField { aggregate, .. }
        | Inst::ExtractElement {
            array: aggregate, ..
        } => types.get(aggregate).is_some_and(is_pointer_carrier),
        _ => false,
    }
}

/// Whether a memory-carried result of `inst` owns a home slot, given the
/// lane's typing of the function: [`owns_storage`], less the write-through
/// `InsertField` ([`insert_writes_through`]), plus the read-through extracts
/// ([`extract_reads_through`]).
fn owns_storage_typed(inst: &Inst, types: &HashMap<ValueId, Ty>) -> bool {
    extract_reads_through(inst, types)
        || (owns_storage(inst) && !insert_writes_through(inst, types))
}

fn first_result(node: &trust_ir::InstrNode, func_name: &str) -> Result<ValueId, WasmLowerError> {
    node.results.first().copied().ok_or_else(|| {
        WasmLowerError::UnsupportedInst(format!("value op without result in `{func_name}`"))
    })
}

/// WebAssembly EH is not wired. Scan the complete function, including
/// unreachable blocks and zero-result nodes, before CFG/local lowering so no
/// incidental reachability or arity behavior can hide an EH instruction.
///
/// The trust-ir v53 non-propagating call boundaries
/// (`Inst::CallCannotUnwind` / `Inst::CallIndirectCannotUnwind`) are refused
/// here by name as well. The module entries already refuse them through the
/// shared floor (`trust_cg_lower::reject_unconsumed_v41_target_neutral_surface`);
/// this scan covers the function `lower_function` is handed, which need not be
/// one of its module's functions. Enforcing the boundary would need a catch at
/// the call site (an imported callee can throw through wasm frames), and
/// WebAssembly EH is not wired; an ordinary call would let the unwind cross.
fn reject_unwired_eh_instructions(func: &Function) -> Result<(), WasmLowerError> {
    for block in &func.blocks {
        for node in &block.body {
            if matches!(node.inst, Inst::MakeClosure { .. }) {
                return Err(WasmLowerError::UnsupportedInst(format!(
                    "Inst::MakeClosure in `{}` block {:?}: runtime closure target/capture ABI is not modeled",
                    func.name, block.id
                )));
            }
            if matches!(
                node.inst,
                Inst::Invoke { .. } | Inst::LandingPad { .. } | Inst::Resume { .. }
            ) {
                return Err(WasmLowerError::UnsupportedInst(format!(
                    "{:?} in `{}` block {:?}: WebAssembly EH/LSDA/personality lowering is not wired",
                    node.inst, func.name, block.id
                )));
            }
            // v54 (amendment P): a sited check with an unwind edge to an
            // in-frame landing pad; refused by name like the EH instructions.
            if matches!(node.inst, Inst::AssertInvoke { .. }) {
                return Err(WasmLowerError::UnsupportedInst(format!(
                    "Inst::AssertInvoke in `{}` block {:?}: a sited check whose failure calls its \
                     panic entry and may enter a landing pad; WebAssembly EH/LSDA/personality \
                     lowering and panic-entry calls are not wired (trust-ir v54)",
                    func.name, block.id
                )));
            }
            // v55 / v56 (amendment D): the unwinding twins of a drop and of an
            // indirect call; refused by name like the EH instructions (the
            // shared floor refuses them first).
            let twin = match node.inst {
                Inst::DropInvoke { .. } => {
                    Some("Inst::DropInvoke (trust-ir v55: a drop runs its type's glue)")
                }
                Inst::InvokeIndirect { .. } => Some("Inst::InvokeIndirect (trust-ir v56)"),
                _ => None,
            };
            if let Some(twin) = twin {
                return Err(WasmLowerError::UnsupportedInst(format!(
                    "{twin} in `{}` block {:?}: an unwind edge to an in-frame landing pad; \
                     WebAssembly EH/LSDA/personality lowering is not wired",
                    func.name, block.id
                )));
            }
            if let Some(refusal) = call_unwind_boundary_refusal(node, func, block.id) {
                return Err(refusal);
            }
        }
    }
    Ok(())
}

/// The by-name refusal of a trust-ir v53 non-propagating call boundary
/// (`Inst::CallCannotUnwind` / `Inst::CallIndirectCannotUnwind`) at `node`,
/// or `None` for any other instruction.
fn call_unwind_boundary_refusal(
    node: &trust_ir::InstrNode,
    func: &Function,
    block: BlockId,
) -> Option<WasmLowerError> {
    let boundary = match node.inst {
        Inst::CallCannotUnwind { .. } => "Inst::CallCannotUnwind",
        Inst::CallIndirectCannotUnwind { .. } => "Inst::CallIndirectCannotUnwind",
        _ => return None,
    };
    Some(WasmLowerError::UnsupportedInst(format!(
        "{boundary} in `{}` block {:?}: a non-propagating call boundary must stop any \
         unwind its callee starts, and the wasm lane has no EH to enforce it with; an \
         ordinary call would let the unwind cross (trust-ir v53)",
        func.name, block
    )))
}

/// The integer scalars the integer unary ops (`Neg`, `Not`, `CtPop`) are
/// admitted at: the native adapter's `is_integer_scalar_ty` set, `Char`'s
/// 32-bit arithmetic carrier included.
fn is_integer_unop_scalar(ty: &Ty) -> bool {
    matches!(
        ty,
        Ty::I8
            | Ty::I16
            | Ty::I32
            | Ty::I64
            | Ty::I128
            | Ty::U8
            | Ty::U16
            | Ty::U32
            | Ty::U64
            | Ty::U128
            | Ty::Isize
            | Ty::Usize
            | Ty::Char
    )
}

/// Refuse, by name, an integer unary op (`Neg`, `Not`, `CtPop`) declared at a
/// type that is not an integer scalar, the same admission the native adapter
/// applies (trust-cg-lower `adapter.rs`, `UnOp::Not => is_integer_scalar_ty`).
///
/// `not bool` is the case that matters: trust-ir's validator refuses it
/// (`UnOpNotOnScalarBool`, WS2.21; the must-refuse row
/// `unop_not_scalar_bool`), and this lane's integer lowering (`x ^ -1`) would
/// turn the 0/1 `Bool` carrier into -1/-2, a value no `Bool` holds. A bool
/// negation is `bxor b, true` or `icmp eq b, false`, which keep 0/1. A
/// `Ptr`/`Func` operand would take the same i32 path and is refused with it.
/// Like [`reject_unwired_eh_instructions`], the scan covers every block,
/// unreachable ones included, and runs before any local or frame analysis.
fn reject_non_integer_scalar_unops(func: &Function) -> Result<(), WasmLowerError> {
    for block in &func.blocks {
        for node in &block.body {
            let Inst::UnOp { op, ty, .. } = &node.inst else {
                continue;
            };
            if !matches!(op, UnOp::Neg | UnOp::Not | UnOp::CtPop) || is_integer_unop_scalar(ty) {
                continue;
            }
            let detail = if matches!((op, ty), (UnOp::Not, Ty::Bool)) {
                "trust-ir refuses `not` on a scalar `Bool` (`UnOpNotOnScalarBool`, WS2.21) and \
                 the integer lowering would leave a value no `Bool` holds; spell a bool \
                 negation `bxor b, true` or `icmp eq b, false`"
            } else {
                "the op is admitted only at an integer scalar type, as in the native adapter"
            };
            return Err(WasmLowerError::UnsupportedInst(format!(
                "UnOp::{op:?} declared type {ty:?} in `{}` block {:?}: {detail}",
                func.name, block.id
            )));
        }
    }
    Ok(())
}

/// Refuse, by name and with the native adapter's reason, the body constructs
/// the native instruction translator refuses and this lane would otherwise
/// lower to something else:
///
/// * any node carrying `ProofAnnotation::RegionHavocStore` (must-refuse row
///   `region_havoc_store`): the marker invalidates every location the pointer
///   may reach, and a wasm store writes one location, so lowering it as an
///   ordinary store could preserve stale values;
/// * an `Undef` carrying proof annotations — `FreshSymbolicHavoc` above all
///   (row `undef_fresh_havoc_feeds_assume`): a nondeterministic-choice marker
///   is not poison, and a claim about a poison value has no value to hold of
///   (trust-cg-lower `borrow_frame_undef`);
/// * an `Undef` that does not declare exactly one result, or whose type is
///   outside the native scalar carrier set
///   ([`trust_cg_lower::borrow_frame_undef::scalar_carrier_ty`]): aggregate and
///   vector poison is unmodelled by the pinned trust-ir reference semantics,
///   and the lane would hand out an uninitialized home slot as its value;
/// * an `ArraySplat` at a type that is not an array (row
///   `array_splat_non_array_type`, trust-ir `InvalidArraySplat`): the lane's
///   splat would treat the scalar result as zero-sized and define nothing;
/// * a `PtrData` / `PtrMetadata` / `PtrFromParts` that does not declare
///   exactly one result, or at a type that is not pointer-like (row
///   `ptr_data_of_non_pointer`, trust-ir `PointerOpInvalid`): the lane would
///   alias the operand;
/// * a `PtrMetadata` / `PtrFromParts` whose declared metadata type is not the
///   pointer type's metadata at the lane's 32-bit pointer width (trust-ir
///   `PointerMetadataTypeMismatch`, which trust-ir's validator derives from the
///   same module pointer width): the lane would read or build a metadata word
///   the pointer does not carry — a fabricated length for a thin pointer.
///
/// Like [`reject_unwired_eh_instructions`], the scan covers every block,
/// unreachable ones included, and runs before any local or frame analysis.
fn reject_unmodeled_body_constructs(func: &Function) -> Result<(), WasmLowerError> {
    use trust_ir::ProofAnnotation;
    for block in &func.blocks {
        for node in &block.body {
            let at = || format!("`{}` block {:?}", func.name, block.id);
            if node
                .proofs
                .iter()
                .any(|proof| matches!(proof, ProofAnnotation::RegionHavocStore))
            {
                return Err(WasmLowerError::UnsupportedInst(format!(
                    "ProofAnnotation::RegionHavocStore in {}: it requires whole-region havoc \
                     semantics; Trust Codegen has no sound lowering",
                    at()
                )));
            }
            match &node.inst {
                Inst::Undef { ty } if !matches!(ty, Ty::Unit | Ty::Never) => {
                    let fresh = node
                        .proofs
                        .iter()
                        .any(|proof| matches!(proof, ProofAnnotation::FreshSymbolicHavoc));
                    if fresh {
                        return Err(WasmLowerError::UnsupportedInst(format!(
                            "Inst::Undef in {}: a FreshSymbolicHavoc-marked undef is a \
                             nondeterministic-choice marker, not poison; it stays outside the \
                             lowering-target subset and a narrowing consumer must refuse it \
                             (must-refuse row refuse/undef_fresh_havoc_feeds_assume)",
                            at()
                        )));
                    }
                    if !node.proofs.is_empty() {
                        return Err(WasmLowerError::UnsupportedInst(format!(
                            "Inst::Undef in {}: an undef carries proof annotations; a claim \
                             about a poison value has no value to hold of",
                            at()
                        )));
                    }
                    if node.results.len() != 1 {
                        return Err(WasmLowerError::UnsupportedInst(format!(
                            "Inst::Undef in {}: declares {} results; exactly one is defined",
                            at(),
                            node.results.len()
                        )));
                    }
                    if !trust_cg_lower::borrow_frame_undef::scalar_carrier_ty(ty) {
                        return Err(WasmLowerError::UnsupportedInst(format!(
                            "Inst::Undef in {}: undef of type {ty}: only scalar integer, Bool, \
                             F32/F64 and thin-pointer poison is materialized; aggregate/vector \
                             poison is unmodelled by the pinned trust-ir reference semantics, \
                             and Char/F16/refined/fat-pointer/handle undef is outside the \
                             lowering-target subset or this carrier set",
                            at()
                        )));
                    }
                }
                Inst::ArraySplat { ty, .. } if !matches!(ty, Ty::Array(..)) => {
                    return Err(WasmLowerError::UnsupportedInst(format!(
                        "Inst::ArraySplat (ty={ty:?}) in {} builds a type that is not an array; \
                         trust-ir refuses it (InvalidArraySplat) and so does this backend",
                        at()
                    )));
                }
                Inst::PtrData { ptr_ty, .. } => {
                    reject_invalid_pointer_operation("PtrData", ptr_ty, None, &node.results, &at)?;
                }
                Inst::PtrMetadata {
                    ptr_ty,
                    metadata_ty,
                    ..
                } => {
                    reject_invalid_pointer_operation(
                        "PtrMetadata",
                        ptr_ty,
                        Some(metadata_ty),
                        &node.results,
                        &at,
                    )?;
                }
                Inst::PtrFromParts {
                    ptr_ty,
                    metadata_ty,
                    ..
                } => {
                    reject_invalid_pointer_operation(
                        "PtrFromParts",
                        ptr_ty,
                        Some(metadata_ty),
                        &node.results,
                        &at,
                    )?;
                }
                _ => {}
            }
        }
    }
    Ok(())
}

/// The wasm32 lane's pointer width in bits; [`require_wasm32_target_info`]
/// admits only modules whose target declares it.
const WASM32_POINTER_BITS: u32 = 32;

/// The native adapter's `validate_pointer_operation` at the wasm32 pointer
/// width: exactly one result, a pointer-like type, and (for `PtrMetadata` /
/// `PtrFromParts`) the declared metadata type equal to the pointer type's
/// metadata at [`WASM32_POINTER_BITS`]. Wording follows the native refusals.
fn reject_invalid_pointer_operation(
    context: &str,
    ptr_ty: &Ty,
    metadata_ty: Option<&Ty>,
    results: &[ValueId],
    at: &dyn Fn() -> String,
) -> Result<(), WasmLowerError> {
    if results.len() != 1 {
        return Err(WasmLowerError::UnsupportedInst(format!(
            "{context} in {} result arity mismatch: got {}, expected 1",
            at(),
            results.len()
        )));
    }
    if !ptr_ty.is_pointer_like() {
        return Err(WasmLowerError::UnsupportedInst(format!(
            "{context} in {} requires a pointer-like type, got {ptr_ty:?}",
            at()
        )));
    }
    if let Some(metadata_ty) = metadata_ty {
        let Some(expected) = ptr_ty.pointer_metadata_ty(WASM32_POINTER_BITS) else {
            return Err(WasmLowerError::UnsupportedInst(format!(
                "{context} in {} has no supported pointer metadata for {ptr_ty:?}",
                at()
            )));
        };
        if metadata_ty != &expected {
            return Err(WasmLowerError::UnsupportedInst(format!(
                "{context} in {} metadata type mismatch for {ptr_ty:?}: declared \
                 {metadata_ty:?}, expected {expected:?} (trust-ir \
                 PointerMetadataTypeMismatch at {WASM32_POINTER_BITS}-bit pointers)",
                at()
            )));
        }
    }
    Ok(())
}

/// Fail-closed accepted-input guard: the module must be pinned to EXACTLY the
/// wasm32 target shape — a wasm32 triple, 32-bit pointers, little-endian.
///
/// A target-free module is refused (not defaulted): the trust-ir layout engine
/// sizes pointers at 8 bytes for target-free IR while this lowering addresses
/// linear memory through i32, so accepting one would silently mis-lay-out
/// every frame and GEP. The diagnostic names the fix
/// ([`super::target::wasm32_target_info`]).
fn require_wasm32_target_info(module: &Module) -> Result<(), WasmLowerError> {
    let Some(ti) = &module.target_info else {
        return Err(WasmLowerError::MissingTargetInfo(format!(
            "module `{}` is target-free; the wasm32 lane compiles only modules pinned to the \
             wasm32 shape (triple {}, 32-bit pointers, little-endian) — stamp \
             `module.target_info = Some(trust_cg_codegen::wasm::wasm32_target_info())`, or in \
             the text format declare `target \"wasm32-unknown-unknown\" 4 little` after the \
             module line",
            module.name,
            super::target::WASM32_TRIPLE,
        )));
    };
    let mut mismatches = Vec::new();
    if !super::target::is_wasm32_target(&ti.triple) {
        mismatches.push(format!("triple `{}` is not a wasm32 triple", ti.triple));
    }
    if ti.pointer_size != 4 {
        mismatches.push(format!(
            "pointer_size {} != 4 (wasm32 addresses are 32-bit)",
            ti.pointer_size
        ));
    }
    if ti.endianness != trust_ir::Endianness::Little {
        mismatches.push(format!(
            "endianness {} != little (wasm linear memory is little-endian)",
            ti.endianness
        ));
    }
    if mismatches.is_empty() {
        Ok(())
    } else {
        Err(WasmLowerError::TargetMismatch(format!(
            "module `{}`: {} — stamp \
             `module.target_info = Some(trust_cg_codegen::wasm::wasm32_target_info())`",
            module.name,
            mismatches.join("; "),
        )))
    }
}

/// Fail-closed call-contract guard, scanned over the COMPLETE function
/// (unreachable blocks included, mirroring the EH scan) so reachability cannot
/// hide a mis-lowerable call:
///
/// * the function's own convention and every call edge's must be one this
///   lane lowers — `CallingConv::C` or `CallingConv::Rust` ([`abi`]); the
///   signature itself is then checked by [`abi::lower_sig`] where it is used;
/// * a call binds at most as many results as its signature returns;
/// * a `byval` parameter on a direct callee is refused with the shared native
///   diagnostic (no caller-copy lowering).
fn reject_unsupported_call_contract(
    func: &Function,
    module: &Module,
) -> Result<(), WasmLowerError> {
    let lowered_cc = |cc: CallingConv| matches!(cc, CallingConv::C | CallingConv::Rust);
    if !lowered_cc(func.calling_conv) {
        return Err(WasmLowerError::UnsupportedCallingConv(format!(
            "function `{}` is declared {:?}; the WASM backend lowers CallingConv::C and \
             CallingConv::Rust",
            func.name, func.calling_conv,
        )));
    }
    for block in &func.blocks {
        for node in &block.body {
            match &node.inst {
                Inst::Call { callee, .. } => {
                    let Some(callee_fn) = module.function_by_id(*callee) else {
                        continue;
                    };
                    trust_cg_lower::reject_byval_params(callee_fn)
                        .map_err(|error| WasmLowerError::UnsupportedAbi(error.to_string()))?;
                    if !lowered_cc(callee_fn.calling_conv) {
                        return Err(WasmLowerError::UnsupportedCallingConv(format!(
                            "call to `{}` in `{}` uses {:?}; the WASM backend lowers \
                             CallingConv::C and CallingConv::Rust",
                            callee_fn.name, func.name, callee_fn.calling_conv,
                        )));
                    }
                    if let Some(ft) = module.func_type(callee_fn.ty)
                        && node.results.len() > ft.returns.len()
                    {
                        return Err(WasmLowerError::UnsupportedMultiResultCall(format!(
                            "call to `{}` in `{}` binds {} results; the signature returns {}",
                            callee_fn.name,
                            func.name,
                            node.results.len(),
                            ft.returns.len(),
                        )));
                    }
                }
                Inst::CallIndirect {
                    sig, calling_conv, ..
                } => {
                    if !lowered_cc(*calling_conv) {
                        return Err(WasmLowerError::UnsupportedCallingConv(format!(
                            "call_indirect in `{}` uses {calling_conv:?}; the WASM backend \
                             lowers CallingConv::C and CallingConv::Rust",
                            func.name,
                        )));
                    }
                    if let Some(ft) = module.func_type(*sig)
                        && node.results.len() > ft.returns.len()
                    {
                        return Err(WasmLowerError::UnsupportedMultiResultCall(format!(
                            "call_indirect via {sig:?} in `{}` binds {} results; the signature \
                             returns {}",
                            func.name,
                            node.results.len(),
                            ft.returns.len(),
                        )));
                    }
                }
                _ => {}
            }
        }
    }
    Ok(())
}

/// The terminator instruction of a block (its last instruction).
fn terminator_of(func: &Function, idx: usize) -> Result<&Inst, WasmLowerError> {
    match func.blocks[idx].body.last() {
        Some(node) if node.inst.is_terminator() => Ok(&node.inst),
        _ => Err(WasmLowerError::UnsupportedControlFlow(format!(
            "block {idx} of `{}` does not end in a terminator",
            func.name
        ))),
    }
}

/// The most fixed-slot `Alloca`s of one function whose slots may share bytes
/// (`Lowering::place_fixed_allocas`); past it each keeps bytes of its own.
const MAX_SHARED_ALLOCAS: usize = 4096;

/// The fewest cases worth a `br_table`. Below this the compare-cascade is both
/// smaller (a 2-case cascade is 2 compares; the table needs 4 blocks) and
/// simpler to read in a disassembly.
pub const BR_TABLE_MIN_CASES: usize = 3;
/// The most table entries one `Switch` may emit. A `br_table` costs one label
/// index per value in the covered range, present as a case or not, and an
/// engine materializes the whole table — so the span is bounded absolutely,
/// not only relatively.
pub const BR_TABLE_MAX_SPAN: i64 = 1024;
/// The density floor: the covered span may exceed the case count by at most
/// this factor, i.e. a table must be at least 1/4 real cases.
pub const BR_TABLE_MAX_SPAN_PER_CASE: i64 = 4;

/// A decided `br_table` dispatch: the index normalization and, for every value
/// in the covered range, which case arm it selects (`None` = a hole, which
/// takes the default edge).
#[derive(Debug, Clone)]
struct BrTablePlan {
    /// The lowest case value, subtracted to normalize the index to `0..span`.
    min: i32,
    /// One entry per value in `min..=max`.
    arm_of_index: Vec<Option<usize>>,
    /// The number of case arms (== `cases.len()`).
    arms: usize,
}

/// Decide whether a `Switch` is dispatched by `br_table`, and with what index
/// normalization. `None` keeps the compare-cascade.
///
/// **The heuristic.** A `br_table` is a jump table: it costs one label index per
/// value in the covered range, whether or not a case lands there, and an engine
/// materializes the whole thing. So all three must hold:
///
/// * at least [`BR_TABLE_MIN_CASES`] cases — below that the cascade is both
///   smaller and simpler to read;
/// * the covered span (`max - min + 1`) is at most [`BR_TABLE_MAX_SPAN`]
///   entries — a hard bound on what one switch may cost the module;
/// * the span is at most [`BR_TABLE_MAX_SPAN_PER_CASE`] times the case count —
///   the DENSITY floor, so a table is never mostly holes.
///
/// **The scope.** Only an `i32`-carrier switch value is dispatched this way.
/// `br_table`'s index is an `i32` compared as UNSIGNED against the table
/// length, and the normalization (`value - min`, WRAPPING) is exactly correct
/// there: an out-of-range value can never wrap back INTO `[0, span)`, because
/// that needs `value <= min - 2^32 + span - 1`, and with
/// `min + span - 1 = max <= i32::MAX` the bound is below `i32::MIN`. The same
/// argument does NOT survive narrowing a 64-bit value to a 32-bit index, so an
/// `i64` switch keeps the cascade rather than getting a subtly wrong range
/// check.
fn br_table_plan(
    value_ty: &Ty,
    cases: &[trust_ir::SwitchCase],
) -> Result<Option<BrTablePlan>, WasmLowerError> {
    if cases.len() < BR_TABLE_MIN_CASES {
        return Ok(None);
    }
    if valtype_of(value_ty)? != ValType::I32 {
        return Ok(None);
    }
    let Some(repr) = int_repr_of(value_ty) else {
        return Ok(None);
    };
    // Canonicalize each case value into the carrier the switch value is
    // compared at, so `min`/`max` are the i32 patterns the dispatch sees.
    let mut values: Vec<i32> = Vec::with_capacity(cases.len());
    for case in cases {
        let Constant::Int(n) = case.value else {
            // A non-integer case value has no table index; the cascade's
            // `emit_const` decides whether it is lowerable at all.
            return Ok(None);
        };
        values.push(repr.carrier_value(n) as i32);
    }
    // `values` has exactly one entry per case and `cases.len() >= BR_TABLE_MIN_CASES`
    // was checked above, so both are `Some` on every reachable path. Decide it
    // rather than asserting it: if that guard is ever weakened, an empty case
    // list keeps the compare-cascade — the conservative lowering — instead of
    // panicking inside codegen.
    let (Some(&min), Some(&max)) = (values.iter().min(), values.iter().max()) else {
        return Ok(None);
    };
    let span = i64::from(max) - i64::from(min) + 1;
    if span > BR_TABLE_MAX_SPAN || span > BR_TABLE_MAX_SPAN_PER_CASE * cases.len() as i64 {
        return Ok(None);
    }
    // `span` fits `BR_TABLE_MAX_SPAN`, so the cast is exact.
    let mut arm_of_index = vec![None; span as usize];
    for (arm, value) in values.iter().enumerate() {
        let i = (i64::from(*value) - i64::from(min)) as usize;
        // FIRST case wins on a duplicated value — the same rule the
        // compare-cascade's leading `value == cases[0]` test applies, so the two
        // lowerings agree on malformed input instead of diverging by heuristic.
        if arm_of_index[i].is_none() {
            arm_of_index[i] = Some(arm);
        }
    }
    Ok(Some(BrTablePlan {
        min,
        arm_of_index,
        arms: cases.len(),
    }))
}

/// An open wasm structured-control label, for branch-depth resolution.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Frame {
    /// A `loop` opened for a header block; `br` to it re-iterates (continue).
    Loop(usize),
    /// A `block` opened for a merge block; `br` to it jumps to the join (break).
    Block(usize),
    /// The `loop` of a dispatch-lowered function; `br` to it re-dispatches on
    /// the label local.
    Dispatch,
}

/// Per-function lowering state.
struct Lowering<'a> {
    func: &'a Function,
    /// The enclosing trust-ir module, for type-layout queries (sizes/offsets).
    module: &'a Module,
    /// FuncId → wasm function index, for direct calls and function pointers.
    call_targets: &'a CallTargets,
    /// FuncId → wasm function index of its internal entry, which a direct
    /// call to it uses instead (an object at O1 and above only).
    internal_abi: &'a InternalTargets,
    /// (signature, convention) → wasm type index, for `call_indirect`.
    sig_types: &'a SigTypes,
    /// Module global → where its static-data image lives.
    global_addrs: &'a GlobalAddrs,
    /// This function's memory-carried constants → their pooled images.
    const_pool: &'a ConstPool,
    /// Runtime helpers / library calls.
    helpers: &'a Helpers,
    /// Callees whose body this compilation does not decide: imports, and in an
    /// object every definition the linker may replace
    /// ([`interposable_linkage`]). Their callers copy by-address aggregate
    /// arguments, since foreign code may write to them.
    foreign: &'a HashSet<FuncId>,
    /// Which callee parameters may capture a pointer argument.
    captures: &'a ParamCaptures,
    /// The lowest address a frame may occupy, when static data lies below the
    /// shadow stack in memory this module owns: a frame or dynamic `Alloca`
    /// reaching below it traps instead of overwriting that data.
    stack_limit: Option<u32>,
    /// Undefined data symbols a body `Const SymbolAddr` names (object only).
    extern_data: &'a ExternData,
    /// Emitting a relocatable object: every index/address immediate is
    /// relocated (see `emit.rs`).
    object: bool,
    /// O1 and above (the env's `unit_scale_elided`): a `GEP` index scaled by
    /// a one-byte element is added unscaled. At O0 the multiply by one stays,
    /// so O0 bytes are those of the lane before the mid-end.
    unit_scale_elided: bool,
    /// O1 and above (the env's `pair_carrier`): the 128-bit integers
    /// `pair::pair_carried` selects are carried in two `i64` locals
    /// ([`Carrier::Pair`]). At O0 every 128-bit integer keeps its home slot,
    /// so O0 bytes are those of the lane before the pair carrier.
    pair_carrier: bool,
    /// The `(low, high)` `i64` locals of every pair-carried value. A pair is
    /// never in `locals`: a lowering that reads a value's one local fails on
    /// a pair instead of reading half of it.
    pair_locals: HashMap<ValueId, (u32, u32)>,
    /// Transient 16-byte frame slots the 128-bit division helper writes a
    /// pair-carried result into, keyed by `(block, node)`.
    divmod_scratch: HashMap<(usize, usize), u32>,
    /// Relocations against `code`.
    relocs: Vec<Reloc>,
    /// This function's lowered signature.
    sig: WasmSig,
    /// The hidden `sret` parameter's local, when the function returns through
    /// memory.
    sret_local: Option<u32>,
    /// How every SSA value is carried.
    carriers: HashMap<ValueId, Carrier>,
    /// Memory-carried values that OWN storage in the frame (the rest alias
    /// storage owned by an operand, a caller, or the constant pool), with the
    /// frame offset `compute_frame` assigned.
    home_offsets: HashMap<ValueId, u32>,
    /// Values that need a home slot, in definition order, with size/align.
    homes: Vec<(ValueId, u32, u32)>,
    /// Staging slots for memory-carried block parameters of blocks with more
    /// than one of them: an edge copies every argument out before copying any
    /// in, so no argument is overwritten by a sibling parameter's copy.
    staging_offsets: HashMap<ValueId, u32>,
    /// Frame slots for copies of by-address arguments passed to foreign
    /// callees, keyed by `(block, node, argument)`.
    arg_copy_offsets: HashMap<(usize, usize, usize), u32>,
    /// Entry parameters passed as scalars that the body carries in memory
    /// (C ABI singletons and split 128-bit integers): `(value, lane, first
    /// incoming wasm local)`, materialized by the prologue.
    materialize: Vec<(ValueId, ParamLane, u32)>,
    /// Scratch `sret` destinations for calls whose memory-carried result is
    /// unused, keyed by `(block, node)`.
    sret_scratch: HashMap<(usize, usize), u32>,
    /// WebAssembly features the emitted code relies on.
    features: std::collections::BTreeSet<&'static str>,
    block_index: HashMap<BlockId, usize>,
    /// Dominator-tree children, each sorted by rpo_index ascending.
    dom_children: Vec<Vec<usize>>,
    /// Block is the target of a back-edge (loop header).
    is_header: Vec<bool>,
    /// Block has ≥2 forward predecessors (merge / join).
    is_merge: Vec<bool>,
    /// Recorded back-edges (source, target).
    back_edges: HashSet<(usize, usize)>,
    /// Immediate dominators (`usize::MAX` for unreachable blocks).
    idom: Vec<usize>,
    /// Block lies on a cycle, so it may run more than once per activation.
    cyclic: Vec<bool>,
    /// For an irreducible CFG, the dispatch loop it is lowered as
    /// ([`Self::emit_dispatch`]); `None` for a reducible CFG, which the
    /// relooper structures.
    dispatch: Option<DispatchPlan>,
    locals: HashMap<ValueId, (u32, ValType)>,
    /// The trust-ir type of every SSA value — the signedness `valtype_of`
    /// erases, which invariant N needs back.
    value_types: HashMap<ValueId, Ty>,
    param_types: Vec<ValType>,
    declared_locals: Vec<ValType>,
    next_local: u32,
    code: Vec<u8>,
    result_types: Option<Vec<ValType>>,
    /// Open structured-control labels, innermost last (for `br` resolution).
    context: Vec<(Frame, u32)>,
    /// Count of currently-open wasm labels (loop/block/if) — the `br` depth base.
    open_labels: u32,
    /// Blocks already emitted (defensive once-only guard).
    emitted: HashSet<usize>,
    /// The module's shadow stack-pointer global, if memory is in use.
    sp_global: Option<u32>,
    /// Byte offset within the frame for each `Alloca` result that keeps one
    /// fixed slot.
    alloca_offsets: HashMap<ValueId, u32>,
    /// `Alloca` results carved from the shadow stack on EVERY execution
    /// (`captures::allocas_needing_fresh_storage`): `(size, align)`, both
    /// multiples of the stack pointer's alignment. Released with the frame
    /// when the function returns.
    dynamic_allocas: HashMap<ValueId, (u32, u32)>,
    /// `Alloca` results whose element count is known only at run time (not an
    /// integer `Const` that fits a `u32`): `(count, element size, align)`,
    /// the alignment a multiple of the stack pointer's. Carved from the
    /// shadow stack at each execution ([`Self::emit_counted_alloca`]) and
    /// released with the frame.
    counted_allocas: HashMap<ValueId, (ValueId, u32, u32)>,
    /// Prepared frame, including zero-byte frames that still need a base pointer.
    frame: Option<ShadowStackFrame>,
    /// Each single-index `GEP` and the byte offset of the `i32.add` that
    /// lowers it: the claims `trust_cg_verify::wasm_nowrap_premise` checks
    /// for the emission pass (which runs at O1 and above only).
    nowrap_claims: Vec<NoWrapClaim>,
}

/// The dispatch loop an irreducible CFG is lowered as
/// ([`Lowering::emit_dispatch`]).
struct DispatchPlan {
    /// Every reachable block, in reverse postorder (the entry first).
    order: Vec<usize>,
    /// Each block's index in `order` (`u32::MAX` when unreachable): the value
    /// of the label local that selects it.
    position: Vec<u32>,
    /// The label local, once declared.
    label: Option<u32>,
}

/// Where [`Lowering::emit_stack_guard`] reads the stack pointer being
/// replaced.
#[derive(Clone, Copy)]
enum StackGuardOld {
    Local(u32),
    Global(u32),
}

#[derive(Clone, Copy)]
struct ShadowStackFrame {
    size: u32,
    /// When `Some(align)`, the prologue aligns the frame base down to `align`
    /// (a slot needs more alignment than the stack pointer guarantees).
    realign: Option<u32>,
    sp_global: u32,
    saved_sp_local: u32,
    base_local: u32,
}

/// Where the shadow stack's base address comes from — the stack half of the
/// host contract an island negotiates rather than assumes.
///
/// The pre-P2 behavior pinned the stack at the top of the module's own single
/// page (address 65536). That is only sound while the module OWNS its memory:
/// in a host's imported memory, 65536 is the host's data, and a frame written
/// there is a silent cross-module corruption. So a module in imported memory
/// must take its base from the host.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub enum WasmStackPolicy {
    /// The module owns its memory and its stack: the stack pointer is a
    /// defined mutable global initialized to the top of the owned memory
    /// (`pages * 64KiB`; one page ⇒ 65536 — the closed-module default).
    ///
    /// Requires [`WasmMemoryPolicy::Owned`]: under any other memory policy a
    /// function needing a frame is refused
    /// ([`WasmLowerError::StackBaseUnavailable`]).
    #[default]
    OwnedTop,
    /// Host-negotiated: the host allocates the island's region and publishes
    /// its TOP through an imported IMMUTABLE `i32` global `(module, name)`.
    /// The island's stack pointer is a defined mutable global whose
    /// initializer is `global.get $that` — the one `global.get` the spec
    /// admits in a constant expression — so the island never names an address
    /// the host did not give it.
    ///
    /// The region is fixed for the module's lifetime: an imported global's
    /// value is bound at instantiation.
    HostBase { module: String, name: String },
}

/// How a body-less (declaration-only) trust-ir function is provided.
///
/// A trust-ir `Function` with no blocks is a declaration: there is nothing to
/// lower. The closed-module default refuses it; an island binds it to a host
/// import.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub enum WasmFuncImportPolicy {
    /// Fail closed: a body-less function is refused
    /// ([`WasmLowerError::UnboundDeclaration`]).
    #[default]
    Forbidden,
    /// Import every body-less function from wasm module `module` under its own
    /// trust-ir name. Imported functions occupy the LOW function index space,
    /// so every defined function's index — and therefore every `call` target,
    /// function-pointer constant, table element and export — shifts by the
    /// number of imports.
    FromModule(String),
}

/// The lowest address the static-data area may use. Addresses `0..8` are left
/// unmapped-by-convention so a null pointer — and a small offset off one —
/// never aliases a real global.
pub const WASM_STATIC_DATA_BASE: u32 = 8;

/// Where a module's STATIC DATA (the byte images of its trust-ir globals) lives
/// in linear memory.
///
/// A wasm data segment is *active*: it is copied into memory at an absolute
/// address when the module is instantiated. In a memory the module owns, the
/// address is the module's own business. In a HOST's memory it is the host's
/// data, so the host must have reserved the region — which is a contract term,
/// not a layout detail.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub enum WasmStaticDataPolicy {
    /// Static data starts at [`WASM_STATIC_DATA_BASE`] and grows up from the
    /// bottom of the module's OWN memory, while the shadow stack grows down
    /// from its top. When the module has static data and owns its stack
    /// ([`WasmStackPolicy::OwnedTop`]), every frame and per-execution `Alloca`
    /// checks the new stack pointer against the end of that data and traps
    /// rather than write below it; with no static data nothing is checked, and
    /// a stack pointer driven below zero traps on its first access. Under any
    /// other memory policy a module that HAS globals is refused
    /// ([`WasmLowerError::HostMemoryNotGranted`]).
    #[default]
    OwnedBottom,
    /// The host reserved `[base, …)` of the memory it shares and grants this
    /// module active data segments there.
    HostReservedAt { base: u32 },
}

/// The exported name of the `memory.size` shim under
/// [`WasmMemoryGrowthPolicy::OwnedShims`] / [`WasmMemoryGrowthPolicy::HostGrantedShims`].
pub const MEMORY_SIZE_EXPORT: &str = "__memory_size";
/// The exported name of the `memory.grow` shim.
pub const MEMORY_GROW_EXPORT: &str = "__memory_grow";

/// Whether the module may RESIZE its linear memory at run time.
///
/// trust-ir has no `memory.grow` instruction of its own, so growth is surfaced
/// as two exported shims — `__memory_size : () -> i32` (pages) and
/// `__memory_grow : (i32) -> i32` (pages to add; returns the PREVIOUS page
/// count, or -1). They are wasm functions like any other and are appended after
/// every trust-ir function, so no defined function's index moves.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub enum WasmMemoryGrowthPolicy {
    /// Fail closed: the module contains no `memory.grow`/`memory.size` at all,
    /// and its memory is exactly the size it declared.
    #[default]
    Fixed,
    /// The module owns its memory and exports the two shims. Refused under
    /// [`WasmMemoryPolicy::Imported`], where growing is the HOST's decision.
    OwnedShims,
    /// The host explicitly granted this module the right to grow the memory it
    /// shares. `memory.grow` moves the host's `ArrayBuffer`, invalidating every
    /// view the host holds — nothing here verifies the host expects that.
    HostGrantedShims,
}

/// The complete host contract a compiled wasm module binds: where its linear
/// memory comes from, where its shadow stack lives, which of its functions the
/// host supplies, where its static data is written, and whether it may resize
/// the memory.
///
/// [`WasmModulePolicy::closed`] (also [`Default`]) reproduces the pre-P2
/// backend byte-for-byte: the module owns one page of memory, stacks at its
/// top, and imports nothing — "the boundary is the module". Any other policy
/// widens the claimed surface to include the bound host contract, which
/// [`WasmCompileEvidence::host_contract`] then reports.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct WasmModulePolicy {
    pub memory: WasmMemoryPolicy,
    pub stack: WasmStackPolicy,
    pub func_imports: WasmFuncImportPolicy,
    pub static_data: WasmStaticDataPolicy,
    pub memory_growth: WasmMemoryGrowthPolicy,
}

/// The fixed island runtime-ABI namespace — the memory and the stack base
/// (`src/wasm/OWNERSHIP.md` §4.3). Deliberately NOT `env`; see
/// [`ISLAND_HOST_MODULE`] for why that namespace is the one an island may not
/// use.
///
/// `@1` is the major version of this fixed surface: it bumps on a name
/// removed, a signature changed, or a region-contract semantic changed, and an
/// island must not import two majors of the same surface.
pub const ISLAND_ABI_NAMESPACE: &str = "trust:island/abi@1";
/// The host memory an [`WasmModulePolicy::island`] shares.
pub const ISLAND_MEMORY_IMPORT: &str = "memory";
/// The imported immutable `i32` global through which the host publishes the
/// TOP of the region it allocated for an [`WasmModulePolicy::island`].
pub const ISLAND_STACK_BASE_IMPORT: &str = "__island_stack_base";
/// The implicit wasm-toolchain namespace, `env` — **not** the island default,
/// and forbidden by the ownership map (`src/wasm/OWNERSHIP.md` §4.2).
///
/// `env` is the namespace Emscripten, wasi-libc and wasm-bindgen glue already
/// occupy, and `env.memory` is its conventional name for a **linker-supplied**
/// memory. A host wiring an island into an import object that already serves an
/// LLVM-built module can satisfy the island's memory import from the existing
/// `env.memory` entry silently, with no error at instantiation and no way for
/// either side to notice — which is exactly what the ownership map exists to
/// prevent. [`WasmModulePolicy::island`] therefore uses
/// [`ISLAND_ABI_NAMESPACE`] instead.
///
/// The constant is retained, unenforced, for one in-flight consumer: a
/// differential whose rustc/LLVM twin is linked with `--import-memory`, where
/// `wasm-ld` fixes the twin's import at `env.memory`, so both modules must be
/// handed the same memory under that name. Removing it is
/// `OWNERSHIP.md` §7 item 7, and it needs the host wiring changed in the same
/// step — it is not a decision this module can make alone.
pub const ISLAND_HOST_MODULE: &str = "env";

/// The import namespace a named island's own host functions live in
/// (`trust:island/<island>@1`), distinct from the fixed
/// [`ISLAND_ABI_NAMESPACE`].
pub fn island_host_namespace(island: &str) -> String {
    format!("trust:island/{island}@1")
}

impl WasmModulePolicy {
    /// The closed module: own one page, stack at its top, import nothing.
    /// Byte-identical to the pre-P2 backend.
    pub fn closed() -> Self {
        Self::default()
    }

    /// An island named `island`, living beside a host module in one linear
    /// memory: it shares the host's memory
    /// ([`ISLAND_ABI_NAMESPACE`].[`ISLAND_MEMORY_IMPORT`]), takes its shadow
    /// stack base from the region the host allocated for it
    /// ([`ISLAND_ABI_NAMESPACE`].[`ISLAND_STACK_BASE_IMPORT`]), and binds
    /// body-less trust-ir functions to host imports in the island's own
    /// namespace ([`island_host_namespace`]).
    pub fn island(island: &str) -> Self {
        Self {
            memory: WasmMemoryPolicy::Imported {
                module: ISLAND_ABI_NAMESPACE.to_string(),
                name: ISLAND_MEMORY_IMPORT.to_string(),
            },
            stack: WasmStackPolicy::HostBase {
                module: ISLAND_ABI_NAMESPACE.to_string(),
                name: ISLAND_STACK_BASE_IMPORT.to_string(),
            },
            func_imports: WasmFuncImportPolicy::FromModule(island_host_namespace(island)),
            // An island's static data would be written into the host's memory
            // at an address the host never reserved, and growing that memory
            // moves it under the host's feet. Both stay fail-closed until the
            // host says otherwise.
            static_data: WasmStaticDataPolicy::OwnedBottom,
            memory_growth: WasmMemoryGrowthPolicy::Fixed,
        }
    }
}

impl<'a> Lowering<'a> {
    fn build(
        func: &'a Function,
        module: &'a Module,
        env: WasmFunctionEnv<'a>,
    ) -> Result<Self, WasmLowerError> {
        let WasmFunctionEnv {
            sp_global,
            call_targets,
            internal_abi,
            sig_types,
            global_addrs,
            const_pool,
            helpers,
            foreign,
            captures,
            stack_limit,
            extern_data,
            object,
            local_opt: _,
            unit_scale_elided,
            pair_carrier,
        } = env;
        let ft = module.func_type(func.ty).ok_or_else(|| {
            WasmLowerError::UnsupportedInst(format!(
                "function `{}` has unknown signature {:?}",
                func.name, func.ty
            ))
        })?;
        // A function with an internal entry IS that entry
        // (`compile_object_parts` emits its C form as a forwarding thunk).
        let sig = if internal_abi.contains_key(&func.id) {
            abi::lower_internal_sig(module, ft, func.calling_conv)?.ok_or_else(|| {
                WasmLowerError::UnsupportedAbi(format!(
                    "[TCG-WASM-INTERNAL-ABI] `{}` is emitted as an internal entry, but its \
                     signature has no internal form",
                    func.name
                ))
            })?
        } else {
            abi::lower_sig(module, ft, func.calling_conv)?
        };
        let n = func.blocks.len();
        let block_index: HashMap<BlockId, usize> = func
            .blocks
            .iter()
            .enumerate()
            .map(|(i, b)| (b.id, i))
            .collect();
        let idx_of = |b: BlockId| -> Result<usize, WasmLowerError> {
            block_index
                .get(&b)
                .copied()
                .ok_or_else(|| WasmLowerError::UndefinedBlock(format!("{b:?}")))
        };

        // Successors from terminators (fail-closed on Switch / non-branch).
        let mut succs: Vec<Vec<usize>> = Vec::with_capacity(n);
        for i in 0..n {
            let s = match terminator_of(func, i)? {
                Inst::Return { .. } | Inst::Unreachable => vec![],
                Inst::Br { target, .. } => vec![idx_of(*target)?],
                Inst::CondBr {
                    then_target,
                    else_target,
                    ..
                } => {
                    vec![idx_of(*then_target)?, idx_of(*else_target)?]
                }
                Inst::Switch { default, cases, .. } => {
                    let mut s = vec![idx_of(*default)?];
                    for c in cases {
                        s.push(idx_of(c.target)?);
                    }
                    s
                }
                other => {
                    return Err(WasmLowerError::UnsupportedControlFlow(format!(
                        "non-branch terminator {other:?}"
                    )));
                }
            };
            succs.push(s);
        }

        let entry = idx_of(func.entry)?;
        let (rpo_index, back_edges) = Self::reverse_postorder(&succs, entry, n);

        // Forward predecessors (exclude back-edges): edge (p, b) where not a back-edge.
        let mut preds: Vec<Vec<usize>> = vec![Vec::new(); n];
        for (p, ss) in succs.iter().enumerate() {
            for &b in ss {
                if !back_edges.contains(&(p, b)) {
                    preds[b].push(p);
                }
            }
        }

        let mut idom = Self::compute_idom(&preds, &rpo_index, entry, n);
        let mut all_preds: Vec<Vec<usize>> = vec![Vec::new(); n];
        for (p, ss) in succs.iter().enumerate() {
            for &b in ss {
                all_preds[b].push(p);
            }
        }

        // Reducibility: every back-edge (u,v) must have v dominate u. Over the
        // forward edges of a reducible CFG those dominators are the CFG's own;
        // an irreducible CFG (a cycle with several entries) gets the
        // dominators of every edge, and is lowered as a dispatch loop
        // ([`Self::emit_dispatch`]) instead of by the relooper.
        let reducible = back_edges
            .iter()
            .all(|&(u, v)| Self::dominates(&idom, v, u, entry));
        let dispatch = if reducible {
            None
        } else {
            idom = Self::compute_idom(&all_preds, &rpo_index, entry, n);
            let mut order: Vec<usize> = (0..n).filter(|&b| rpo_index[b] != usize::MAX).collect();
            order.sort_by_key(|&b| rpo_index[b]);
            let mut position = vec![u32::MAX; n];
            for (i, &b) in order.iter().enumerate() {
                position[b] = u32::try_from(i).map_err(|_| {
                    WasmLowerError::ImplementationLimit(format!(
                        "`{}` has more blocks than a wasm32 dispatch index holds",
                        func.name
                    ))
                })?;
            }
            Some(DispatchPlan {
                order,
                position,
                label: None,
            })
        };

        // Blocks on a cycle: the natural loop of every back edge (u, h) is h
        // plus every block that reaches u without passing through h. Every
        // cycle contains a back edge of the DFS, so this covers every cycle of
        // an irreducible CFG too (over-approximating, which only costs fixed
        // `Alloca` slots).
        let mut cyclic = vec![false; n];
        for &(u, h) in &back_edges {
            cyclic[h] = true;
            let mut seen = vec![false; n];
            seen[h] = true;
            let mut work = vec![u];
            while let Some(b) = work.pop() {
                if seen[b] {
                    continue;
                }
                seen[b] = true;
                cyclic[b] = true;
                work.extend(all_preds[b].iter().copied());
            }
        }

        // Merge nodes: ≥2 forward predecessors. Loop headers: back-edge targets.
        let is_merge: Vec<bool> = (0..n).map(|b| preds[b].len() >= 2).collect();
        let mut is_header = vec![false; n];
        for &(_, v) in &back_edges {
            is_header[v] = true;
        }

        // Dominator-tree children, sorted by rpo_index ascending.
        let mut dom_children: Vec<Vec<usize>> = vec![Vec::new(); n];
        for c in 0..n {
            if c != entry && rpo_index[c] != usize::MAX {
                dom_children[idom[c]].push(c);
            }
        }
        for kids in &mut dom_children {
            kids.sort_by_key(|&c| rpo_index[c]);
        }

        Ok(Self {
            func,
            module,
            call_targets,
            internal_abi,
            sig_types,
            global_addrs,
            const_pool,
            helpers,
            foreign,
            captures,
            stack_limit,
            extern_data,
            object,
            unit_scale_elided,
            pair_carrier,
            pair_locals: HashMap::new(),
            divmod_scratch: HashMap::new(),
            relocs: Vec::new(),
            sig,
            sret_local: None,
            carriers: HashMap::new(),
            home_offsets: HashMap::new(),
            homes: Vec::new(),
            staging_offsets: HashMap::new(),
            arg_copy_offsets: HashMap::new(),
            materialize: Vec::new(),
            sret_scratch: HashMap::new(),
            features: std::collections::BTreeSet::new(),
            block_index,
            dom_children,
            is_header,
            is_merge,
            back_edges,
            idom,
            cyclic,
            dispatch,
            locals: HashMap::new(),
            value_types: HashMap::new(),
            param_types: Vec::new(),
            declared_locals: Vec::new(),
            next_local: 0,
            code: Vec::new(),
            result_types: None,
            context: Vec::new(),
            open_labels: 0,
            emitted: HashSet::new(),
            sp_global,
            alloca_offsets: HashMap::new(),
            dynamic_allocas: HashMap::new(),
            counted_allocas: HashMap::new(),
            frame: None,
            nowrap_claims: Vec::new(),
        })
    }

    /// Pre-pass: lay out one stack frame for the function.
    ///
    /// * Every `Alloca` that runs at most once per activation, or whose
    ///   earlier pointers are provably unobservable, gets one fixed slot,
    ///   first-fit in instruction order from offset 0, aligned to at least 8;
    ///   two such slots share bytes when no pointer derived from one can be
    ///   live where the other is ([`Self::place_fixed_allocas`]). Any other
    ///   `Alloca` is carved from the shadow stack at each execution instead
    ///   ([`Self::dynamic_allocas`]).
    /// * Each memory-carried value that owns storage gets a home slot. Homes
    ///   whose storage is never live at the same time share bytes
    ///   ([`storage::home_conflicts`]); a home whose address may escape a
    ///   bounded read (`storage::Storage::pinned`) shares with nothing.
    /// * Slots live only within one instruction or edge — staging for the
    ///   parameters of a block with several memory-carried ones that a branch
    ///   enters (the entry block's are bound by the caller, so only a branch
    ///   back to it stages them), a call's scratch `sret` destination and its
    ///   copies of by-address arguments to foreign callees — share one
    ///   transient region sized for the largest site.
    ///
    /// If any slot or dynamic `Alloca` exists, two helper locals (saved SP,
    /// frame base) are reserved and the module's stack-pointer global is
    /// required.
    fn compute_frame(&mut self) -> Result<(), WasmLowerError> {
        let overflow = || WasmLowerError::FrameLayoutOverflow(self.func.name.clone());
        let mut offset: u32 = 0;
        let mut max_align: u32 = 8;
        let slot = |offset: &mut u32, size: u32, align: u32, max_align: &mut u32| -> Option<u32> {
            let at = align_up(*offset, align)?;
            *offset = at.checked_add(size)?;
            *max_align = (*max_align).max(align);
            Some(at)
        };
        // The stack pointer is kept 8-aligned in a closed module (every frame
        // is a multiple of 8 below a page-aligned top) and 16-aligned in an
        // object (the wasm C ABI's invariant, which LLVM-compiled callers
        // uphold). A slot needing more is aligned dynamically.
        let sp_align: u32 = if self.object { 16 } else { 8 };
        // An array `Alloca` whose count is an integer `Const` that fits a
        // `u32` has a static extent and is laid out like any other slot; any
        // other count is carved at run time ([`Self::counted_allocas`]).
        let const_counts: HashMap<ValueId, i128> = self
            .func
            .blocks
            .iter()
            .flat_map(|b| &b.body)
            .filter_map(|n| match (&n.inst, n.results.first()) {
                (
                    Inst::Const {
                        ty,
                        value: Constant::Int(v),
                    },
                    Some(r),
                ) if ty.is_integer() => Some((*r, *v)),
                _ => None,
            })
            .collect();
        let fresh = self.allocas_needing_fresh_storage()?;
        // Fixed-slot `Alloca`s, in instruction order: (result, size, align).
        let mut fixed: Vec<(ValueId, u32, u32)> = Vec::new();
        for block in &self.func.blocks {
            for node in &block.body {
                if let Inst::Alloca { ty, count, align } = &node.inst {
                    // `Err(count)`: known only at run time.
                    let static_count = match count {
                        None => Ok(1),
                        Some(c) => const_counts
                            .get(c)
                            .and_then(|&n| u32::try_from(n).ok())
                            .ok_or(*c),
                    };
                    let (elem_size, natural) = layout::size_align(self.module, ty)?;
                    let explicit = match align {
                        None => 1,
                        Some(a) => {
                            let a = *a;
                            if !a.is_power_of_two() {
                                return Err(WasmLowerError::FrameLayoutOverflow(format!(
                                    "{}: alloca alignment {a} is not a power of two",
                                    self.func.name
                                )));
                            }
                            u32::try_from(a).map_err(|_| {
                                WasmLowerError::FrameLayoutOverflow(format!(
                                    "{}: alloca alignment {a} exceeds the wasm32 address space",
                                    self.func.name
                                ))
                            })?
                        }
                    };
                    let slot_align = natural.max(explicit).max(8);
                    if !slot_align.is_power_of_two() {
                        return Err(WasmLowerError::FrameLayoutOverflow(format!(
                            "{}: alloca alignment {slot_align} is not a power of two",
                            self.func.name
                        )));
                    }
                    let result = first_result(node, &self.func.name)?;
                    let count = match static_count {
                        Ok(n) => n,
                        Err(c) => {
                            let align = slot_align.max(sp_align);
                            if i32::try_from(align).is_err() {
                                return Err(WasmLowerError::FrameLayoutOverflow(format!(
                                    "{}: alloca alignment {align} exceeds the largest realignable \
                                 wasm32 frame alignment (2^30)",
                                    self.func.name
                                )));
                            }
                            self.counted_allocas.insert(result, (c, elem_size, align));
                            continue;
                        }
                    };
                    // The interpreter gives every allocation, a zero-sized
                    // one included, at least one byte of address space, so
                    // distinct live allocations never share an address: a
                    // zero-sized slot or carve takes one byte too.
                    let size = elem_size.checked_mul(count).ok_or_else(overflow)?.max(1);
                    if fresh.contains(&result) {
                        let align = slot_align.max(sp_align);
                        let size = align_up(size, align).ok_or_else(overflow)?;
                        if i32::try_from(size).is_err() || i32::try_from(align).is_err() {
                            return Err(overflow());
                        }
                        self.dynamic_allocas.insert(result, (size, align));
                        continue;
                    }
                    fixed.push((result, size, slot_align));
                }
            }
        }
        self.place_fixed_allocas(&fixed, &mut offset, &mut max_align)?;
        self.place_homes(&mut offset, &mut max_align)?;
        // The transient region: every site's slots start at its base.
        let transient = offset;
        let mut transient_end = offset;
        let entry_reentered = entry_reentered(self.func);
        for block in &self.func.blocks {
            if block.id == self.func.entry && !entry_reentered {
                continue;
            }
            let mem_params: Vec<ValueId> = block
                .params
                .iter()
                .map(|(v, _)| *v)
                .filter(|v| self.carriers.get(v).is_some_and(|c| c.is_mem()))
                .collect();
            if mem_params.len() < 2 {
                continue;
            }
            let mut cur = transient;
            for v in mem_params {
                let Some(Carrier::Mem { size, align }) = self.carriers.get(&v).copied() else {
                    continue;
                };
                let at = slot(&mut cur, size, align, &mut max_align).ok_or_else(overflow)?;
                self.staging_offsets.insert(v, at);
            }
            transient_end = transient_end.max(cur);
        }
        for (bi, block) in self.func.blocks.iter().enumerate() {
            for (ni, node) in block.body.iter().enumerate() {
                // The 128-bit division helper stores its result through a
                // pointer: a pair-carried result is written to a transient
                // slot and loaded from it.
                if let Inst::BinOp {
                    op: BinOp::UDiv | BinOp::URem | BinOp::SDiv | BinOp::SRem,
                    ty,
                    ..
                } = &node.inst
                    && wide::is_wide(ty)
                    && node
                        .results
                        .first()
                        .is_some_and(|r| self.carriers.get(r) == Some(&Carrier::Pair))
                {
                    let mut cur = transient;
                    let at = slot(&mut cur, 16, 8, &mut max_align).ok_or_else(overflow)?;
                    self.divmod_scratch.insert((bi, ni), at);
                    transient_end = transient_end.max(cur);
                    continue;
                }
                // (signature, is the callee foreign, arguments)
                let (callee_sig, foreign, args) = match &node.inst {
                    Inst::Call { callee, args } => {
                        let Some(callee_fn) = self.module.function_by_id(*callee) else {
                            continue;
                        };
                        let Some(ft) = self.module.func_type(callee_fn.ty) else {
                            continue;
                        };
                        (
                            self.direct_call_sig(*callee, ft, callee_fn.calling_conv)?,
                            self.foreign.contains(callee),
                            args,
                        )
                    }
                    Inst::CallIndirect {
                        sig,
                        args,
                        calling_conv,
                        ..
                    } => {
                        let Some(ft) = self.module.func_type(*sig) else {
                            continue;
                        };
                        (abi::lower_sig(self.module, ft, *calling_conv)?, true, args)
                    }
                    _ => continue,
                };
                // A pair-carried result has no home for the callee to write:
                // it is returned through a scratch slot and loaded from it.
                let direct_sret = callee_sig.direct_sret_index().is_some_and(|i| {
                    node.results
                        .get(i)
                        .is_some_and(|r| self.carriers.get(r) != Some(&Carrier::Pair))
                });
                let mut cur = transient;
                if let Some((size, align)) = callee_sig.sret_layout
                    && !direct_sret
                {
                    let at = slot(&mut cur, size, align, &mut max_align).ok_or_else(overflow)?;
                    self.sret_scratch.insert((bi, ni), at);
                }
                if foreign {
                    for (ai, (lane, arg)) in callee_sig.params.iter().zip(args).enumerate() {
                        if let ParamLane::ByAddr { size } = lane {
                            let align = match self.carriers.get(arg) {
                                Some(Carrier::Mem { align, .. }) => *align,
                                _ => 8,
                            };
                            let at = slot(&mut cur, *size, align, &mut max_align)
                                .ok_or_else(overflow)?;
                            self.arg_copy_offsets.insert((bi, ni, ai), at);
                        }
                    }
                }
                transient_end = transient_end.max(cur);
            }
        }
        offset = transient_end;
        if self.alloca_offsets.is_empty()
            && self.dynamic_allocas.is_empty()
            && self.counted_allocas.is_empty()
            && self.home_offsets.is_empty()
            && self.staging_offsets.is_empty()
            && self.arg_copy_offsets.is_empty()
            && self.sret_scratch.is_empty()
            && self.divmod_scratch.is_empty()
        {
            return Ok(());
        }
        let sp_global = self.sp_global.ok_or_else(|| {
            WasmLowerError::UnsupportedInst(
                "function allocates but no stack-pointer global was provisioned".to_string(),
            )
        })?;
        let size = align_up(offset, sp_align).ok_or_else(overflow)?;
        // The prologue subtracts the size as an `i32.const`: 2 GiB or more
        // would flip its sign and grow the frame UP into the caller's.
        if i32::try_from(size).is_err() {
            return Err(overflow());
        }
        let realign = (max_align > sp_align).then_some(max_align);
        // The prologue realigns the frame base with an `i32` mask `-align`,
        // and a per-execution `Alloca` refuses an alignment that is not an
        // `i32` already: a frame slot (an explicit `Alloca` alignment, or a
        // zero-sized type declaring one) is held to the same bound.
        if let Some(a) = realign
            && i32::try_from(a).is_err()
        {
            return Err(WasmLowerError::FrameLayoutOverflow(format!(
                "{}: frame alignment {a} exceeds the largest realignable wasm32 frame \
                 alignment (2^30)",
                self.func.name
            )));
        }
        let next_local = self.next_local.checked_add(2).ok_or_else(overflow)?;
        self.frame = Some(ShadowStackFrame {
            size,
            realign,
            sp_global,
            saved_sp_local: self.next_local,
            base_local: self.next_local + 1,
        });
        self.declared_locals.push(ValType::I32);
        self.declared_locals.push(ValType::I32);
        self.next_local = next_local;
        Ok(())
    }

    /// Give every fixed-slot `Alloca` in `fixed` (instruction order) its frame
    /// offset at or above `*offset`, advancing `*offset` past the last.
    ///
    /// trust-ir gives an `Alloca`'s storage the rest of the activation, but
    /// its bytes are observable only through values DERIVED from its result
    /// (`trust_cg_irmid::escape::derive`: every value computed from it, integers included,
    /// except one loaded through a pointer of its provenance or a call result
    /// the callee cannot return it in). So two allocations may share bytes
    /// when, wherever one is allocated, no value derived from the other is
    /// live — the storage liveness [`storage::home_conflicts`] computes over
    /// those derived values, with each `Alloca` as the definition of its own
    /// storage. An
    /// allocation whose pointer may be captured (stored to memory, handed to a
    /// callee that may keep it, called indirectly, or its address bits
    /// escaping the data flow — a branch on them, a write at a location they
    /// index, an access through a pointer rebuilt at a displacement not
    /// provably inside the allocation, which may land in a neighbour — after
    /// which an equal integer can be rebuilt and turned back into a pointer)
    /// is live for the whole activation and shares with nothing. A
    /// zero-sized allocation takes one byte, so no two live allocations share
    /// an address. Placement is first-fit in instruction order, so a function
    /// whose allocations all conflict is laid out exactly as one that places
    /// them one after another (up to filling an alignment gap). Past
    /// [`MAX_SHARED_ALLOCAS`] allocations nothing is shared.
    fn place_fixed_allocas(
        &mut self,
        fixed: &[(ValueId, u32, u32)],
        offset: &mut u32,
        max_align: &mut u32,
    ) -> Result<(), WasmLowerError> {
        let overflow = || WasmLowerError::FrameLayoutOverflow(self.func.name.clone());
        let ids: Vec<ValueId> = fixed.iter().map(|a| a.0).collect();
        let shared = (2..=MAX_SHARED_ALLOCAS).contains(&fixed.len());
        let (storage, interference) = if shared {
            let storage = self.alloca_storage(&ids)?;
            let entry = self.idx(self.func.entry)?;
            let interference =
                storage::home_conflicts(self.func, &self.block_index, entry, &storage, &ids);
            (Some(storage), Some(interference))
        } else {
            (None, None)
        };
        let base = *offset;
        let mut end = base;
        let mut by_start: std::collections::BTreeSet<(u32, u32, usize)> =
            std::collections::BTreeSet::new();
        for (i, &(v, size, align)) in fixed.iter().enumerate() {
            let alone = storage.as_ref().is_none_or(|s| s.pinned.contains(&v));
            let mut at = align_up(base, align).ok_or_else(overflow)?;
            for &(s, e, j) in &by_start {
                if at.checked_add(size).ok_or_else(overflow)? <= s {
                    break;
                }
                let apart = alone
                    || storage
                        .as_ref()
                        .is_some_and(|st| st.pinned.contains(&fixed[j].0))
                    || interference.as_ref().is_some_and(|c| c.conflict(i, j));
                if e > at && apart {
                    at = align_up(e, align).ok_or_else(overflow)?;
                }
            }
            let stop = at.checked_add(size).ok_or_else(overflow)?;
            by_start.insert((at, stop, i));
            end = end.max(stop);
            *max_align = (*max_align).max(align);
            self.alloca_offsets.insert(v, at);
        }
        *offset = end;
        Ok(())
    }

    /// Assign every home slot an offset at or above `*offset` (see
    /// [`Self::compute_frame`]), advancing `*offset` past the last one.
    fn place_homes(&mut self, offset: &mut u32, max_align: &mut u32) -> Result<(), WasmLowerError> {
        let overflow = || WasmLowerError::FrameLayoutOverflow(self.func.name.clone());
        if self.homes.is_empty() {
            return Ok(());
        }
        let homes = self.homes.clone();
        let ids: Vec<ValueId> = homes.iter().map(|h| h.0).collect();
        let sources: HashSet<ValueId> = ids.iter().copied().collect();
        let carriers = &self.carriers;
        let facts = storage::analyze(
            self.func,
            &|v| carriers.get(&v).is_some_and(|c| c.is_mem()),
            &sources,
        );
        let entry = self.idx(self.func.entry)?;
        let interference =
            storage::home_conflicts(self.func, &self.block_index, entry, &facts, &ids);
        // Pinned homes first, each in bytes of its own.
        for &(v, size, align) in homes.iter().filter(|h| facts.pinned.contains(&h.0)) {
            let at = align_up(*offset, align).ok_or_else(overflow)?;
            *offset = at.checked_add(size).ok_or_else(overflow)?;
            *max_align = (*max_align).max(align);
            self.home_offsets.insert(v, at);
        }
        let base = *offset;
        let end = match &interference {
            storage::Interference::Exact(_) => {
                // First-fit, in definition order, beside every placed home it
                // conflicts with: the lowest aligned offset past `base` whose
                // bytes overlap none of them. The placed conflicts are
                // visited in (start, end) order either by collecting and
                // sorting them (few conflicts) or by scanning every placed
                // home in that order and testing each (many) — the same
                // offsets either way: a scan stops at the first placed home
                // starting at or past the candidate's end, and every later
                // one starts later still.
                let mut end = base;
                let mut placed: Vec<Option<(u32, u32)>> = vec![None; homes.len()];
                let mut by_start: std::collections::BTreeSet<(u32, u32, usize)> =
                    std::collections::BTreeSet::new();
                for (i, &(v, size, align)) in homes.iter().enumerate() {
                    if facts.pinned.contains(&v) {
                        continue;
                    }
                    let mut at = align_up(base, align).ok_or_else(overflow)?;
                    let few = interference
                        .degree(i)
                        .is_some_and(|d| d.saturating_mul(8) < by_start.len());
                    if few {
                        let mut taken: Vec<(u32, u32)> = Vec::new();
                        interference.for_each_conflict(i, |j| {
                            if let Some(p) = placed[j] {
                                taken.push(p);
                            }
                        });
                        taken.sort_unstable();
                        for (s, e) in taken {
                            if at.checked_add(size).ok_or_else(overflow)? <= s {
                                break;
                            }
                            if e > at {
                                at = align_up(e, align).ok_or_else(overflow)?;
                            }
                        }
                    } else {
                        for &(s, e, j) in &by_start {
                            if at.checked_add(size).ok_or_else(overflow)? <= s {
                                break;
                            }
                            if e > at && interference.conflict(i, j) {
                                at = align_up(e, align).ok_or_else(overflow)?;
                            }
                        }
                    }
                    let stop = at.checked_add(size).ok_or_else(overflow)?;
                    placed[i] = Some((at, stop));
                    by_start.insert((at, stop, i));
                    end = end.max(stop);
                    *max_align = (*max_align).max(align);
                    self.home_offsets.insert(v, at);
                }
                end
            }
            storage::Interference::Hulls(hulls) => {
                // Too many homes for the exact relation: a linear scan per
                // (size, alignment) class over the live hulls, each class in
                // a region of its own, where a slot is reused once every
                // home in it has ended.
                let mut class_of: HashMap<(u32, u32), usize> = HashMap::new();
                let mut classes: Vec<((u32, u32), Vec<usize>)> = Vec::new();
                for (i, &(v, size, align)) in homes.iter().enumerate() {
                    if facts.pinned.contains(&v) {
                        continue;
                    }
                    let k = *class_of.entry((size, align)).or_insert_with(|| {
                        classes.push(((size, align), Vec::new()));
                        classes.len() - 1
                    });
                    classes[k].1.push(i);
                }
                let mut cursor = base;
                for ((size, align), mut members) in classes {
                    let stride = align_up(size, align).ok_or_else(overflow)?;
                    let region = align_up(cursor, align).ok_or_else(overflow)?;
                    members.sort_by_key(|&i| (hulls[i].0, i));
                    let mut active: std::collections::BinaryHeap<std::cmp::Reverse<(usize, u32)>> =
                        std::collections::BinaryHeap::new();
                    let mut free: std::collections::BinaryHeap<std::cmp::Reverse<u32>> =
                        std::collections::BinaryHeap::new();
                    let mut slots: u32 = 0;
                    for i in members {
                        let (lo, hi) = hulls[i];
                        while let Some(&std::cmp::Reverse((e, slot))) = active.peek() {
                            if e >= lo {
                                break;
                            }
                            active.pop();
                            free.push(std::cmp::Reverse(slot));
                        }
                        let slot = match free.pop() {
                            Some(std::cmp::Reverse(slot)) => slot,
                            None => {
                                slots = slots.checked_add(1).ok_or_else(overflow)?;
                                slots - 1
                            }
                        };
                        let at = slot
                            .checked_mul(stride)
                            .and_then(|o| region.checked_add(o))
                            .ok_or_else(overflow)?;
                        self.home_offsets.insert(homes[i].0, at);
                        active.push(std::cmp::Reverse((hi, slot)));
                    }
                    cursor = slots
                        .checked_mul(stride)
                        .and_then(|o| region.checked_add(o))
                        .ok_or_else(overflow)?;
                    *max_align = (*max_align).max(align);
                }
                cursor
            }
        };
        *offset = end;
        Ok(())
    }

    /// Re-canonicalize every narrow PARAMETER in place, at function entry.
    ///
    /// The narrow-carrier invariant is a property of values inside this module,
    /// and a function's arguments come from outside it: an exported function is
    /// called by the host with an arbitrary `i32`, and an indirect call reaches
    /// a signature, not a caller. So the callee establishes the invariant for
    /// its own parameters rather than assuming it. Emits nothing when no
    /// parameter is narrow — which is every function the pre-P3 backend
    /// compiled.
    fn emit_param_canonicalization(&mut self) -> Result<(), WasmLowerError> {
        let entry = self.idx(self.func.entry)?;
        let params: Vec<(ValueId, Ty)> = self.func.blocks[entry].params.to_vec();
        for (vid, ty) in params {
            let Some(repr) = narrow_of(&ty) else { continue };
            let local = slot(&self.locals, vid)?.0;
            emit_local_get(&mut self.code, local);
            self.emit_canonicalize(repr)?;
            self.emit_local_set(local);
        }
        Ok(())
    }

    /// Emit the frame prologue: save the caller SP, carve out this frame, and
    /// publish the new SP. No-op when the function has no frame.
    fn emit_prologue(&mut self) -> Result<(), WasmLowerError> {
        let Some(frame) = self.frame else {
            return Ok(());
        };
        self.emit_global_op(op::GLOBAL_GET, frame.sp_global);
        self.emit_local_set(frame.saved_sp_local);
        emit_local_get(&mut self.code, frame.saved_sp_local);
        emit_i32_const(&mut self.code, frame.size as i32);
        self.code.push(op::I32_SUB);
        if let Some(align) = frame.realign {
            // `-align` as a bit pattern: a power-of-two `align` below 2^31
            // (`compute_frame`) masks the low bits.
            emit_i32_const(&mut self.code, align.wrapping_neg() as i32);
            self.code.push(op::I32_AND);
        }
        self.code.push(op::LOCAL_TEE);
        write_uleb128(&mut self.code, u64::from(frame.base_local));
        self.emit_global_op(op::GLOBAL_SET, frame.sp_global);
        self.emit_stack_guard(frame.base_local, StackGuardOld::Local(frame.saved_sp_local));
        // An ENTRY parameter that owns a home is materialized here, so its
        // address local is set here. Every other home's address local is set
        // where the value is written — at its defining instruction, or on
        // each edge into its block (`set_home_addr`) — so it is live only
        // while the value is, and local coalescing can reuse it. The order is
        // total and input-determined — frame offset, then definition order
        // (`homes` is in definition order and the sort is stable): homes that
        // never conflict share an offset, and a hash-map order here would
        // make the module bytes vary from run to run.
        let entry = self.idx(self.func.entry)?;
        let entry_params: HashSet<ValueId> = self.func.blocks[entry]
            .params
            .iter()
            .map(|(v, _)| *v)
            .collect();
        let mut homes: Vec<(ValueId, u32)> = Vec::new();
        for &(v, ..) in &self.homes {
            if entry_params.contains(&v)
                && let Some(&off) = self.home_offsets.get(&v)
            {
                homes.push((v, off));
            }
        }
        homes.sort_by_key(|&(_, o)| o);
        for (v, off) in homes {
            let addr = slot(&self.locals, v)?.0;
            emit_local_get(&mut self.code, frame.base_local);
            emit_i32_const(&mut self.code, off as i32);
            self.code.push(op::I32_ADD);
            self.emit_local_set(addr);
        }
        // Parameters that arrived as scalars but are carried in memory.
        for (v, lane, first) in std::mem::take(&mut self.materialize) {
            let addr = slot(&self.locals, v)?.0;
            match lane {
                ParamLane::Singleton { offset, ty, .. } => {
                    emit_local_get(&mut self.code, addr);
                    emit_local_get(&mut self.code, first);
                    self.emit_store(&ty, offset)?;
                }
                ParamLane::Split128 { offset } => {
                    emit_local_get(&mut self.code, addr);
                    emit_local_get(&mut self.code, first);
                    self.emit_store(&Ty::U64, offset)?;
                    emit_local_get(&mut self.code, addr);
                    emit_local_get(&mut self.code, first + 1);
                    self.emit_store(&Ty::U64, offset + 8)?;
                }
                ParamLane::ByAddr { size } => self.emit_copy(addr, 0, first, 0, size),
                _ => {}
            }
        }
        Ok(())
    }

    /// Point `v`'s address local at its home slot, when `v` owns one: `base
    /// + offset`, emitted where the value is about to be written (its
    /// defining instruction, or an edge into its block). Every read of the
    /// value is dominated by such a write (strict SSA,
    /// [`Self::check_strict_ssa`]), so every read sees the address.
    fn set_home_addr(&mut self, v: ValueId) -> Result<(), WasmLowerError> {
        let Some(&off) = self.home_offsets.get(&v) else {
            return Ok(());
        };
        let frame = self.frame.ok_or_else(|| {
            WasmLowerError::UnsupportedInst(format!(
                "home of {v:?} in `{}` has no prepared shadow-stack frame",
                self.func.name
            ))
        })?;
        let addr = slot(&self.locals, v)?.0;
        emit_local_get(&mut self.code, frame.base_local);
        emit_i32_const(&mut self.code, off as i32);
        self.code.push(op::I32_ADD);
        self.emit_local_set(addr);
        Ok(())
    }

    /// Trap unless the new stack pointer in local `new` lies in
    /// `[stack_limit, old]`: at or above the end of static data (so the carve
    /// never overwrote it) and not above the previous stack pointer (so the
    /// subtraction did not wrap). No-op when the module has no such limit.
    ///
    /// Every stack pointer this module publishes is either within that range
    /// or followed immediately by `unreachable`, so no frame byte is ever
    /// written below the limit. A trap therefore leaves behind either a
    /// lowered stack pointer that is still at or above the limit (later frames
    /// run with less stack and are still checked) or one below it (after which
    /// every framed call traps).
    fn emit_stack_guard(&mut self, new: u32, old: StackGuardOld) {
        let Some(limit) = self.stack_limit else {
            return;
        };
        emit_local_get(&mut self.code, new);
        emit_i32_const(&mut self.code, limit as i32);
        self.code.push(op::I32_LT_U);
        emit_local_get(&mut self.code, new);
        match old {
            StackGuardOld::Local(l) => emit_local_get(&mut self.code, l),
            StackGuardOld::Global(g) => self.emit_global_op(op::GLOBAL_GET, g),
        }
        self.code.push(op::I32_GT_U);
        self.code.push(op::I32_OR);
        self.code.push(op::IF);
        self.code.push(op::BLOCKTYPE_VOID);
        self.code.push(op::UNREACHABLE);
        self.code.push(op::END);
    }

    /// `Alloca` carved from the shadow stack at this execution: `SP := (SP -
    /// size) & -align`, checked against the stack limit before it is
    /// published. The frame's epilogue restores the caller's SP, which
    /// releases every such allocation when the function returns.
    fn emit_dynamic_alloca(
        &mut self,
        dst: u32,
        size: u32,
        align: u32,
    ) -> Result<(), WasmLowerError> {
        let frame = self.frame.ok_or_else(|| {
            WasmLowerError::UnsupportedInst(
                "a per-execution Alloca has no prepared shadow-stack frame".to_string(),
            )
        })?;
        self.emit_global_op(op::GLOBAL_GET, frame.sp_global);
        emit_i32_const(&mut self.code, size as i32);
        self.code.push(op::I32_SUB);
        emit_i32_const(&mut self.code, align.wrapping_neg() as i32);
        self.code.push(op::I32_AND);
        self.emit_local_set(dst);
        self.emit_stack_guard(dst, StackGuardOld::Global(frame.sp_global));
        emit_local_get(&mut self.code, dst);
        self.emit_global_op(op::GLOBAL_SET, frame.sp_global);
        Ok(())
    }

    /// `Alloca` of `count` elements of `elem_size` bytes, carved from the
    /// shadow stack at this execution: `SP := (SP - count * elem_size) &
    /// -align`, the new stack pointer checked like a per-execution
    /// `Alloca`'s before it is published and released with the frame.
    ///
    /// The count is read at its trust-ir type: a signed count at or below
    /// zero, an unsigned count of zero, a byte size past the wasm32 address
    /// space, and a size above the current stack pointer (the subtraction
    /// would wrap) all trap. The interpreter rejects the first two as
    /// undefined behaviour and the rest cannot be allocated.
    fn emit_counted_alloca(
        &mut self,
        dst: u32,
        count: ValueId,
        elem_size: u32,
        align: u32,
    ) -> Result<(), WasmLowerError> {
        let frame = self.frame.ok_or_else(|| {
            WasmLowerError::UnsupportedInst(
                "a counted Alloca has no prepared shadow-stack frame".to_string(),
            )
        })?;
        let cty = self.value_ty(count)?;
        if !cty.is_integer() {
            return Err(WasmLowerError::UnsupportedInst(format!(
                "Alloca count of type {cty:?} in `{}` (an integer count is required)",
                self.func.name
            )));
        }
        let trap_if = |code: &mut Vec<u8>| {
            code.push(op::IF);
            code.push(op::BLOCKTYPE_VOID);
            code.push(op::UNREACHABLE);
            code.push(op::END);
        };
        // `n`: the count as an i64 (zero- or sign-extended per its type).
        let n = self.temp(ValType::I64);
        if wide::is_wide(&cty) {
            // A 128-bit count past 2^64 is past any allocation: its high half
            // must be zero, and then its value is the low half, unsigned.
            let src = self.wide_source(count)?;
            self.push_wide_half(src, true)?;
            self.code.push(op::I64_EQZ);
            self.code.push(op::I32_EQZ);
            trap_if(&mut self.code);
            self.push_wide_half(src, false)?;
            self.emit_local_set(n);
            emit_local_get(&mut self.code, n);
            self.code.push(op::I64_EQZ);
        } else {
            let (local, vt) = slot(&self.locals, count)?;
            emit_local_get(&mut self.code, local);
            if vt == ValType::I32 {
                self.code.push(if cty.is_signed() {
                    op::I64_EXTEND_I32_S
                } else {
                    op::I64_EXTEND_I32_U
                });
            }
            self.emit_local_set(n);
            emit_local_get(&mut self.code, n);
            if cty.is_signed() {
                self.code.push(op::I64_CONST);
                write_sleb128(&mut self.code, 0);
                self.code.push(op::I64_LE_S);
            } else {
                self.code.push(op::I64_EQZ);
            }
        }
        trap_if(&mut self.code);
        // `sz`: the byte size, at most `u32::MAX`.
        let sz = self.temp(ValType::I32);
        if let Some(max_count) = u32::MAX.checked_div(elem_size) {
            emit_local_get(&mut self.code, n);
            self.code.push(op::I64_CONST);
            write_sleb128(&mut self.code, i64::from(max_count));
            self.code.push(op::I64_GT_U);
            trap_if(&mut self.code);
            emit_local_get(&mut self.code, n);
            self.code.push(op::I64_CONST);
            write_sleb128(&mut self.code, i64::from(elem_size));
            self.code.push(op::I64_MUL);
            self.code.push(op::I32_WRAP_I64);
        } else {
            // A zero-sized allocation still takes a byte of its own
            // (`compute_frame`).
            emit_i32_const(&mut self.code, 1);
        }
        self.emit_local_set(sz);
        self.emit_global_op(op::GLOBAL_GET, frame.sp_global);
        emit_local_get(&mut self.code, sz);
        self.code.push(op::I32_LT_U);
        trap_if(&mut self.code);
        self.emit_global_op(op::GLOBAL_GET, frame.sp_global);
        emit_local_get(&mut self.code, sz);
        self.code.push(op::I32_SUB);
        emit_i32_const(&mut self.code, align.wrapping_neg() as i32);
        self.code.push(op::I32_AND);
        self.emit_local_set(dst);
        self.emit_stack_guard(dst, StackGuardOld::Global(frame.sp_global));
        emit_local_get(&mut self.code, dst);
        self.emit_global_op(op::GLOBAL_SET, frame.sp_global);
        Ok(())
    }

    /// Iterative DFS from `entry`: records back-edges (retreating edges whose
    /// target is on the current path) and returns a reverse-postorder index
    /// (`usize::MAX` for unreachable blocks). Shared with the capture
    /// analysis (`trust_cg_irmid::escape::reverse_postorder`).
    fn reverse_postorder(
        succs: &[Vec<usize>],
        entry: usize,
        n: usize,
    ) -> (Vec<usize>, HashSet<(usize, usize)>) {
        trust_cg_irmid::escape::reverse_postorder(succs, entry, n)
    }

    /// Cooper-Harvey-Kennedy iterative dominance over reverse-postorder
    /// (`trust_cg_irmid::escape::compute_idom`).
    fn compute_idom(
        preds: &[Vec<usize>],
        rpo_index: &[usize],
        entry: usize,
        n: usize,
    ) -> Vec<usize> {
        trust_cg_irmid::escape::compute_idom(preds, rpo_index, entry, n)
    }

    /// Does `a` dominate `b`? Walk `b`'s idom chain to the entry
    /// (`trust_cg_irmid::escape::dominates_in`).
    fn dominates(idom: &[usize], a: usize, b: usize, entry: usize) -> bool {
        trust_cg_irmid::escape::dominates_in(idom, a, b, entry)
    }

    /// Size in bytes of a type — the reference interpreter's `byte_size`,
    /// through the lane's one layout authority ([`layout::size_align`]), so
    /// an `Alloca` slot and a `GEP` stride agree with the offsets every field
    /// access of the same type uses.
    fn size_of(&self, ty: &Ty) -> Result<u32, WasmLowerError> {
        layout::size_align(self.module, ty).map(|(size, _)| size)
    }

    fn idx(&self, b: BlockId) -> Result<usize, WasmLowerError> {
        self.block_index
            .get(&b)
            .copied()
            .ok_or_else(|| WasmLowerError::UndefinedBlock(format!("{b:?}")))
    }

    /// Assign a wasm local to every SSA value: the function's wasm parameters
    /// first (in the lowered signature's order — `sret`, then each parameter's
    /// lane), then every other block param and instruction result.
    fn assign_locals(&mut self) -> Result<(), WasmLowerError> {
        let entry = self.idx(self.func.entry)?;
        let sig = self.sig.clone();
        self.param_types = sig.wasm.params.clone();
        let mut next_param: u32 = 0;
        if sig.sret {
            self.sret_local = Some(0);
            next_param = 1;
        }
        self.next_local = sig.wasm.params.len() as u32;
        let params = self.func.blocks[entry].params.clone();
        if params.len() != sig.params.len() {
            return Err(WasmLowerError::ArityMismatch(format!(
                "`{}`: entry block has {} params, signature has {}",
                self.func.name,
                params.len(),
                sig.params.len()
            )));
        }
        // Type every value first, then bind locals in the historical order.
        let mut node_tys = node_result_types(self.func, self.module)?;
        let all_tys = typed_values(self.func, self.module, &node_tys)?;
        let byaddr: Vec<ValueId> = params
            .iter()
            .zip(&sig.params)
            .filter(|(_, lane)| matches!(lane, ParamLane::ByAddr { .. }))
            .map(|((v, _), _)| *v)
            .collect();
        let escaping = if byaddr.is_empty() {
            HashSet::new()
        } else {
            storage::escaping_sources(self.func, self.module, entry, &all_tys, &byaddr)?
        };
        let byaddr_escapes = |v: &ValueId| escaping.contains(v);
        let pairs = if self.pair_carrier {
            pair::pair_carried(self.func, self.module, &all_tys)?
        } else {
            HashSet::new()
        };
        for ((vid, ty), lane) in params.iter().zip(&sig.params) {
            self.value_types.insert(*vid, ty.clone());
            match lane {
                ParamLane::Scalar(vt) => {
                    self.locals.insert(*vid, (next_param, *vt));
                    self.carriers.insert(*vid, Carrier::Scalar(*vt));
                    next_param += 1;
                }
                ParamLane::Void => {
                    self.carriers.insert(*vid, Carrier::Void);
                }
                ParamLane::ByAddr { .. } if self.is_header[entry] || byaddr_escapes(vid) => {
                    // A branch back to the entry block rebinds this parameter,
                    // and an edge writes the parameter's storage — which must
                    // then be this frame's own, never the caller's. Likewise a
                    // parameter whose address flows somewhere the lane cannot
                    // bound must not publish the caller's storage. Either way
                    // the incoming bytes are copied into a home slot once, in
                    // the prologue, before the entry block's `loop` opens.
                    let carrier = layout::carrier_of(self.module, ty)?;
                    let Carrier::Mem { size, align } = carrier else {
                        return Err(WasmLowerError::UnsupportedType(format!(
                            "{ty:?} is passed by address but is not memory-carried"
                        )));
                    };
                    self.carriers.insert(*vid, carrier);
                    self.bind_declared(*vid, ValType::I32);
                    self.homes.push((*vid, size, align));
                    self.materialize.push((*vid, lane.clone(), next_param));
                    next_param += 1;
                }
                ParamLane::ByAddr { .. } => {
                    // The incoming address IS the value's address: the value
                    // lives in the caller's memory. The entry block has no
                    // predecessor, so no edge ever writes this parameter, and
                    // its address never leaves the frame (`byaddr_escapes`):
                    // the callee only reads the caller's bytes.
                    let carrier = layout::carrier_of(self.module, ty)?;
                    self.locals.insert(*vid, (next_param, ValType::I32));
                    self.carriers.insert(*vid, carrier);
                    next_param += 1;
                }
                ParamLane::Split128 { offset: 0 } if pairs.contains(vid) => {
                    // The two incoming halves ARE the pair: nothing is
                    // materialized, and a branch back to the entry block
                    // rebinds them as it rebinds a scalar parameter.
                    self.carriers.insert(*vid, Carrier::Pair);
                    self.pair_locals.insert(*vid, (next_param, next_param + 1));
                    next_param += 2;
                }
                ParamLane::Singleton { .. } | ParamLane::Split128 { .. } => {
                    let carrier = layout::carrier_of(self.module, ty)?;
                    let Carrier::Mem { size, align } = carrier else {
                        return Err(WasmLowerError::UnsupportedType(format!(
                            "{ty:?} is passed as a scalar lane but is not memory-carried"
                        )));
                    };
                    self.carriers.insert(*vid, carrier);
                    self.bind_declared(*vid, ValType::I32);
                    self.homes.push((*vid, size, align));
                    self.materialize.push((*vid, lane.clone(), next_param));
                    next_param += if matches!(lane, ParamLane::Split128 { .. }) {
                        2
                    } else {
                        1
                    };
                }
            }
        }
        for (bi, block) in self.func.blocks.iter().enumerate() {
            if bi != entry {
                for (vid, ty) in &block.params {
                    self.bind_value(*vid, ty.clone(), true, pairs.contains(vid))?;
                }
            }
            for (ni, node) in block.body.iter().enumerate() {
                if node.results.is_empty() {
                    continue;
                }
                let tys = match node_tys.remove(&(bi, ni)) {
                    Some(tys) => tys,
                    None => result_tys(&node.inst, self.module)?,
                };
                if node.results.len() > tys.len() {
                    return Err(WasmLowerError::ArityMismatch(format!(
                        "`{}`: {:?} binds {} results but produces {}",
                        self.func.name,
                        node.inst,
                        node.results.len(),
                        tys.len()
                    )));
                }
                let owns = owns_storage_typed(&node.inst, &all_tys);
                for (&res, ty) in node.results.iter().zip(tys) {
                    self.bind_value(res, ty, owns, pairs.contains(&res))?;
                }
            }
        }
        Ok(())
    }

    /// Refuse input that is not strict SSA in the sense the lowering relies
    /// on ([`WasmLowerError::IllFormedSsa`]):
    ///
    /// * every value is defined exactly once;
    /// * every operand of a REACHABLE block is dominated by its definition —
    ///   an entry parameter, a parameter of a dominating block, or an earlier
    ///   result (in the same block, or in a strictly dominating one). The
    ///   storage decisions assume it: an alias home is read after its source's
    ///   definition re-executes ([`owns_storage`]), and an `Alloca` in a loop
    ///   keeps one slot when no earlier pointer can reach a later iteration
    ///   (`captures.rs`);
    /// * every branch argument agrees with its target parameter's type
    ///   ([`Self::edge_arg_agrees`]): an edge copies the parameter's carrier
    ///   out of the argument.
    ///
    /// Unreachable blocks are never emitted, so only their DEFINITIONS matter
    /// (a reachable use of one is refused).
    fn check_strict_ssa(&self) -> Result<(), WasmLowerError> {
        let n = self.func.blocks.len();
        let entry = self.idx(self.func.entry)?;
        let name = &self.func.name;
        // Dominator-tree interval numbering, iteratively: `a` dominates `b`
        // iff `pre[a] <= pre[b] && post[b] <= post[a]`.
        let mut pre = vec![usize::MAX; n];
        let mut post = vec![0usize; n];
        let mut clock = 0usize;
        let mut stack: Vec<(usize, usize)> = vec![(entry, 0)];
        pre[entry] = clock;
        clock += 1;
        while let Some(top) = stack.last_mut() {
            let (b, i) = *top;
            if let Some(&c) = self.dom_children[b].get(i) {
                top.1 += 1;
                pre[c] = clock;
                clock += 1;
                stack.push((c, 0));
            } else {
                post[b] = clock;
                clock += 1;
                stack.pop();
            }
        }
        let reachable = |b: usize| pre[b] != usize::MAX;
        let dominates = |a: usize, b: usize| pre[a] <= pre[b] && post[b] <= post[a];
        // Definition site of every value: (block, position), where a block's
        // parameters sit at position 0 and node `k` defines at `k + 1`.
        let mut def: HashMap<ValueId, (usize, usize)> = HashMap::new();
        for (bi, block) in self.func.blocks.iter().enumerate() {
            let sites = block.params.iter().map(|(v, _)| (*v, 0)).chain(
                block
                    .body
                    .iter()
                    .enumerate()
                    .flat_map(|(ni, node)| node.results.iter().map(move |r| (*r, ni + 1))),
            );
            for (v, at) in sites {
                if def.insert(v, (bi, at)).is_some() {
                    return Err(WasmLowerError::IllFormedSsa(format!(
                        "`{name}`: value {v:?} is defined more than once"
                    )));
                }
            }
        }
        for (bi, block) in self.func.blocks.iter().enumerate() {
            if !reachable(bi) {
                continue;
            }
            for (ni, node) in block.body.iter().enumerate() {
                let mut bad: Option<ValueId> = None;
                node.inst.visit_value_operands(|v| {
                    if bad.is_some() {
                        return;
                    }
                    let ok = match def.get(&v) {
                        None => false,
                        Some(&(db, at)) if db == bi => at <= ni,
                        Some(&(db, _)) => reachable(db) && dominates(db, bi),
                    };
                    if !ok {
                        bad = Some(v);
                    }
                });
                if let Some(v) = bad {
                    return Err(WasmLowerError::IllFormedSsa(format!(
                        "`{name}`: {v:?} is used in block {:?} (instruction {ni}) where its \
                         definition does not dominate the use",
                        block.id
                    )));
                }
                for (target, args) in storage::edges(&node.inst) {
                    let ti = self.idx(target)?;
                    let params = &self.func.blocks[ti].params;
                    if params.len() != args.len() {
                        return Err(WasmLowerError::ArityMismatch(format!(
                            "`{name}`: an edge from block {:?} to {target:?} passes {} \
                             argument(s) for {} parameter(s)",
                            block.id,
                            args.len(),
                            params.len()
                        )));
                    }
                    for (&a, (p, pty)) in args.iter().zip(params) {
                        if !self.edge_arg_agrees(a, pty)? {
                            let aty = self.value_ty(a)?;
                            return Err(WasmLowerError::IllFormedSsa(format!(
                                "`{name}`: the edge from block {:?} to {target:?} binds \
                                 {a:?} of type {aty:?} to parameter {p:?} of type {pty:?}",
                                block.id
                            )));
                        }
                    }
                }
            }
        }
        Ok(())
    }

    /// Whether branch argument `a` may bind a parameter of type `pty`: the
    /// same type; two zero-sized types (nothing is copied); or two integer or
    /// address scalars the lane carries identically — the same wasm value
    /// type, and, below 32 bits, the same width and signedness (the canonical
    /// carrier form, invariant N). A memory-carried parameter's edge copy
    /// moves the parameter's bytes out of the argument, so any other pairing
    /// is refused.
    fn edge_arg_agrees(&self, a: ValueId, pty: &Ty) -> Result<bool, WasmLowerError> {
        let aty = self.value_ty(a)?;
        if &aty == pty {
            return Ok(true);
        }
        if matches!(
            (
                layout::carrier_of(self.module, &aty)?,
                layout::carrier_of(self.module, pty)?
            ),
            (Carrier::Void, Carrier::Void)
        ) {
            return Ok(true);
        }
        Ok(match (int_repr_of(&aty), int_repr_of(pty)) {
            (Some(x), Some(y)) => x.carrier == y.carrier && (x == y || x.bits.min(y.bits) >= 32),
            _ => false,
        })
    }

    /// Bind a local (and, for a memory-carried value that owns its bytes, a
    /// home slot) to SSA value `v` of type `ty`; `pair`: `v` is a 128-bit
    /// integer `pair::pair_carried` selected, bound to two `i64` locals.
    fn bind_value(
        &mut self,
        v: ValueId,
        ty: Ty,
        owns: bool,
        pair: bool,
    ) -> Result<(), WasmLowerError> {
        let mut carrier = layout::carrier_of(self.module, &ty)?;
        if pair {
            if !wide::is_wide(&ty) {
                return Err(WasmLowerError::UnsupportedType(format!(
                    "{v:?} of type {ty:?} in `{}` was selected for a 128-bit pair carrier",
                    self.func.name
                )));
            }
            carrier = Carrier::Pair;
        }
        self.value_types.insert(v, ty);
        self.carriers.insert(v, carrier);
        match carrier {
            Carrier::Scalar(vt) => self.bind_declared(v, vt),
            Carrier::Void => {}
            Carrier::Mem { size, align } => {
                self.bind_declared(v, ValType::I32);
                if owns {
                    self.homes.push((v, size, align));
                }
            }
            Carrier::Pair => {
                let lo = self.next_local;
                self.declared_locals.push(ValType::I64);
                self.declared_locals.push(ValType::I64);
                self.next_local += 2;
                self.pair_locals.insert(v, (lo, lo + 1));
            }
        }
        Ok(())
    }

    /// The trust-ir type bound to an SSA value.
    fn value_ty(&self, v: ValueId) -> Result<Ty, WasmLowerError> {
        self.value_types
            .get(&v)
            .cloned()
            .ok_or_else(|| WasmLowerError::UndefinedValue(format!("{v:?}")))
    }

    fn bind_declared(&mut self, v: ValueId, vt: ValType) {
        self.locals.insert(v, (self.next_local, vt));
        self.declared_locals.push(vt);
        self.next_local += 1;
    }

    fn emit_local_set(&mut self, idx: u32) {
        self.code.push(op::LOCAL_SET);
        write_uleb128(&mut self.code, u64::from(idx));
    }

    // --- The narrow-carrier invariant (module docs, "Invariant N") ----------

    /// Sign-extend the low `bits` of the `i32` on top of the stack into the
    /// whole carrier. `i32.extend8_s` / `i32.extend16_s` are the spec's
    /// single-opcode form (Core Specification 2.0, "Numeric Instructions");
    /// any other sub-32 width expands to the MVP `shl`/`shr_s` pair, which is
    /// the same function.
    fn emit_sign_extend_i32(&mut self, bits: u32) -> Result<(), WasmLowerError> {
        match bits {
            8 => self.code.push(op::I32_EXTEND8_S),
            16 => self.code.push(op::I32_EXTEND16_S),
            b if (1..32).contains(&b) => {
                let shift = (32 - b) as i32;
                emit_i32_const(&mut self.code, shift);
                self.code.push(op::I32_SHL);
                emit_i32_const(&mut self.code, shift);
                self.code.push(op::I32_SHR_S);
            }
            other => {
                return Err(WasmLowerError::NarrowLegalization(format!(
                    "no wasm operator sign-extends {other} bit(s) into an i32 carrier in `{}`",
                    self.func.name,
                )));
            }
        }
        Ok(())
    }

    /// Re-canonicalize the value on top of the operand stack into `repr`'s
    /// carrier form: sign-extended for a signed narrow type, zero-extended for
    /// an unsigned one. A value that already fills its carrier needs nothing.
    fn emit_canonicalize(&mut self, repr: IntRepr) -> Result<(), WasmLowerError> {
        if !repr.is_narrow() {
            return Ok(());
        }
        if repr.carrier != ValType::I32 {
            return Err(WasmLowerError::NarrowLegalization(format!(
                "{}-bit value in a {:?} carrier in `{}`",
                repr.bits, repr.carrier, self.func.name,
            )));
        }
        if repr.signed {
            self.emit_sign_extend_i32(repr.bits)?;
        } else {
            emit_i32_const(&mut self.code, repr.mask_i32());
            self.code.push(op::I32_AND);
        }
        Ok(())
    }

    /// Coerce the CANONICAL carrier on top of the stack into the full-width
    /// `view` an operation reads. When the view matches the carrier's own form
    /// (a signed type read signed, an unsigned type read unsigned) this emits
    /// nothing — which is the whole point of pinning a canonical form.
    fn emit_view(&mut self, repr: IntRepr, view: IntView) -> Result<(), WasmLowerError> {
        if !repr.is_narrow() {
            return Ok(());
        }
        let want_signed = view == IntView::Signed;
        if want_signed == repr.signed {
            return Ok(());
        }
        self.emit_canonicalize(IntRepr {
            signed: want_signed,
            ..repr
        })
    }

    /// Push a value operand, coerced to `view` when the operand type is narrow
    /// AND the operation asks for a particular view of it.
    fn emit_operand(
        &mut self,
        local: u32,
        narrow: Option<IntRepr>,
        view: Option<IntView>,
    ) -> Result<(), WasmLowerError> {
        emit_local_get(&mut self.code, local);
        if let (Some(repr), Some(view)) = (narrow, view) {
            self.emit_view(repr, view)?;
        }
        Ok(())
    }

    /// Re-canonicalize the value on top of the stack when `ty` is narrow — the
    /// producer half of invariant N, applied uniformly after every narrow
    /// result so no arm has to argue that its particular operation happened to
    /// leave the carrier canonical.
    fn canonicalize_result(&mut self, ty: &Ty) -> Result<(), WasmLowerError> {
        match narrow_of(ty) {
            Some(repr) => self.emit_canonicalize(repr),
            None => Ok(()),
        }
    }

    /// Emit a unary op, leaving the result on the operand stack. `src` is the
    /// operand's local. Integer `Neg`/`Not` have no wasm opcode, so they expand
    /// (`0 - x` / `x ^ -1`); the float unaries and `popcnt` are single opcodes.
    ///
    /// A narrow operand is read ZERO-extended where the op inspects the whole
    /// carrier (`popcnt` must not count a negative `I8`'s sign extension), and
    /// the result is re-canonicalized into the narrow carrier form.
    fn emit_unop(&mut self, un: UnOp, ty: &Ty, src: u32) -> Result<(), WasmLowerError> {
        use ValType::{F32, F64, I32, I64};
        let vt = valtype_of(ty)?;
        let narrow = narrow_of(ty);
        match (un, vt) {
            // Integer negate: 0 - x.
            (UnOp::Neg, I32) => {
                emit_i32_const(&mut self.code, 0);
                emit_local_get(&mut self.code, src);
                self.code.push(op::I32_SUB);
            }
            (UnOp::Neg, I64) => {
                self.code.push(op::I64_CONST);
                write_sleb128(&mut self.code, 0);
                emit_local_get(&mut self.code, src);
                self.code.push(op::I64_SUB);
            }
            // Bitwise NOT: x ^ -1 (all ones).
            (UnOp::Not, I32) => {
                emit_local_get(&mut self.code, src);
                emit_i32_const(&mut self.code, -1);
                self.code.push(op::I32_XOR);
            }
            (UnOp::Not, I64) => {
                emit_local_get(&mut self.code, src);
                self.code.push(op::I64_CONST);
                write_sleb128(&mut self.code, -1);
                self.code.push(op::I64_XOR);
            }
            // Single-opcode unaries: operand then opcode.
            _ => {
                let opcode = match (un, vt) {
                    (UnOp::CtPop, I32) => op::I32_POPCNT,
                    (UnOp::CtPop, I64) => op::I64_POPCNT,
                    (UnOp::FNeg, F32) => op::F32_NEG,
                    (UnOp::FNeg, F64) => op::F64_NEG,
                    (UnOp::FAbs, F32) => op::F32_ABS,
                    (UnOp::FAbs, F64) => op::F64_ABS,
                    (UnOp::FSqrt, F32) => op::F32_SQRT,
                    (UnOp::FSqrt, F64) => op::F64_SQRT,
                    (UnOp::FCeil, F32) => op::F32_CEIL,
                    (UnOp::FCeil, F64) => op::F64_CEIL,
                    (UnOp::FFloor, F32) => op::F32_FLOOR,
                    (UnOp::FFloor, F64) => op::F64_FLOOR,
                    (UnOp::FTrunc, F32) => op::F32_TRUNC,
                    (UnOp::FTrunc, F64) => op::F64_TRUNC,
                    _ => {
                        return Err(WasmLowerError::UnsupportedInst(format!(
                            "UnOp::{un:?} on {vt:?}"
                        )));
                    }
                };
                // `popcnt` counts every set bit of the CARRIER, so a narrow
                // operand must be zero-extended first: the sign extension of a
                // negative `I8` is not part of its value.
                self.emit_operand(src, narrow, Some(IntView::Unsigned))?;
                self.code.push(opcode);
            }
        }
        self.canonicalize_result(ty)
    }

    /// Emit an integer↔integer resize between two carriers, preserving
    /// invariant N on both sides.
    ///
    /// Three steps, in order:
    /// 1. bring the SOURCE to the full-width `view` the cast reads it at
    ///    (`Trunc`/`ZExt` read the zero-extended pattern, `SExt` the
    ///    sign-extended one — matching the reference interpreter, whose
    ///    `InterpretInt::as_signed` sign-extends from the value's own width and
    ///    whose `raw` is that width zero-extended);
    /// 2. change carrier width (`i64.extend_i32_s/u`, `i32.wrap_i64`);
    /// 3. re-canonicalize into the DESTINATION's carrier form.
    ///
    /// Every trust-ir integer resize is one of these three composed, which is
    /// why `Trunc`, `ZExt` and `SExt` differ here only in their `view`.
    fn emit_int_resize(
        &mut self,
        src: IntRepr,
        dst: IntRepr,
        view: IntView,
    ) -> Result<(), WasmLowerError> {
        self.emit_view(src, view)?;
        match (src.carrier, dst.carrier) {
            (a, b) if a == b => {}
            (ValType::I32, ValType::I64) => self.code.push(match view {
                IntView::Signed => op::I64_EXTEND_I32_S,
                IntView::Unsigned => op::I64_EXTEND_I32_U,
            }),
            (ValType::I64, ValType::I32) => self.code.push(op::I32_WRAP_I64),
            (a, b) => {
                return Err(WasmLowerError::NarrowLegalization(format!(
                    "integer resize between {a:?} and {b:?} carriers in `{}`",
                    self.func.name,
                )));
            }
        }
        self.emit_canonicalize(dst)
    }

    /// Emit a cast conversion. The operand is already on the stack; this
    /// appends the conversion opcode(s) for the `src_ty → dst_ty` pair.
    ///
    /// Integer resizes go through [`Lowering::emit_int_resize`], so a narrow
    /// source is read at the right width and a narrow destination lands in its
    /// canonical carrier form (invariant N) rather than keeping the source's
    /// high bits. Float→int uses the SATURATING `trunc_sat` (matching Rust `as`
    /// / the trust-ir interpreter, which saturate rather than trap).
    fn emit_cast(&mut self, op: CastOp, src_ty: &Ty, dst_ty: &Ty) -> Result<(), WasmLowerError> {
        use ValType::{F32, F64, I32, I64};
        let src_vt = valtype_of(src_ty)?;
        let dst_vt = valtype_of(dst_ty)?;
        let sat = |s: &mut Self, idx: u32| {
            s.code.push(op::FC_PREFIX);
            write_uleb128(&mut s.code, u64::from(idx));
        };
        // A bool lane is one bit of value in a byte of storage: trust-ir never
        // reinterprets it (the validator's `BoolLaneReinterpret`; the reference
        // interpreter's `eval_bitcast` has no bool source), so a non-identity
        // `Bitcast`/`Transmute` with a bool side is invalid IR — refused by name
        // before the i32 carriers could make it look like an identity.
        if matches!(op, CastOp::Bitcast | CastOp::Transmute)
            && src_ty != dst_ty
            && (*src_ty == Ty::Bool || *dst_ty == Ty::Bool)
        {
            return Err(WasmLowerError::UnsupportedInst(format!(
                "Cast::{op:?} {src_ty:?} -> {dst_ty:?} in `{}`: trust-ir never reinterprets a \
                 bool lane (BoolLaneReinterpret); resize it with ZExt/Trunc",
                self.func.name
            )));
        }
        // The integer resize family: identical machinery, different source
        // view. `Bitcast` between two same-width integers is a resize too —
        // the bit pattern survives, but the destination's canonical carrier
        // form may differ (`U8` 0xFF and `I8` -1 are the same byte, not the
        // same i32).
        let resize_view = match op {
            CastOp::Trunc | CastOp::ZExt => Some(IntView::Unsigned),
            CastOp::SExt => Some(IntView::Signed),
            CastOp::PtrToInt | CastOp::IntToPtr | CastOp::PtrToPtr => Some(IntView::Unsigned),
            CastOp::Bitcast if src_vt == dst_vt => Some(IntView::Unsigned),
            _ => None,
        };
        if let Some(view) = resize_view
            && let (Some(src), Some(dst)) = (int_repr_of(src_ty), int_repr_of(dst_ty))
        {
            if op == CastOp::Bitcast && src.bits != dst.bits {
                // trust-ir defines `Bitcast` only between equal bit widths.
                return Err(WasmLowerError::UnsupportedInst(format!(
                    "Cast::Bitcast {src_ty:?} -> {dst_ty:?} in `{}`: a {}-bit to {}-bit \
                     reinterpretation is not a trust-ir Bitcast (widths must match)",
                    self.func.name, src.bits, dst.bits
                )));
            }
            return self.emit_int_resize(src, dst, view);
        }
        let float_to_int = matches!(
            op,
            CastOp::FPToSI | CastOp::FPToSISat | CastOp::FPToUI | CastOp::FPToUISat
        );
        // An int<->float conversion reads or writes an INTEGER: `bool` and the
        // pointer types have no integer shape the reference interpreter
        // converts (its `int_shape`), so such a cast is refused by name rather
        // than lowered as if the i32 carrier were an integer.
        let int_side = if float_to_int {
            Some(dst_ty)
        } else if matches!(op, CastOp::SIToFP | CastOp::UIToFP) {
            Some(src_ty)
        } else {
            None
        };
        if let Some(t) = int_side
            && !is_convertible_int(t)
        {
            return Err(WasmLowerError::UnsupportedInst(format!(
                "Cast::{op:?} {src_ty:?} -> {dst_ty:?} in `{}`: {t:?} is not an integer type",
                self.func.name
            )));
        }
        if float_to_int && let Some(dst) = narrow_of(dst_ty) {
            return self.emit_float_to_narrow(op, src_vt, dst);
        }
        match op {
            CastOp::Trunc | CastOp::ZExt | CastOp::SExt => {
                // Reached only when one side is not integer-like at all.
                return Err(self.bad_cast(op, src_vt, dst_vt));
            }
            CastOp::FPTrunc => match (src_vt, dst_vt) {
                (F64, F32) => self.code.push(op::F32_DEMOTE_F64),
                (a, b) if a == b => {}
                _ => return Err(self.bad_cast(op, src_vt, dst_vt)),
            },
            CastOp::FPExt => match (src_vt, dst_vt) {
                (F32, F64) => self.code.push(op::F64_PROMOTE_F32),
                (a, b) if a == b => {}
                _ => return Err(self.bad_cast(op, src_vt, dst_vt)),
            },
            // trunc_sat is EXACTLY the Sat variants' semantics (NaN -> 0,
            // clamp — Rust `as`), and a sound refinement for the raw
            // FPToSI/FPToUI (out-of-range/NaN is UB per trust-ir; a defined
            // saturated result refines UB).
            CastOp::FPToSI | CastOp::FPToSISat => match (src_vt, dst_vt) {
                (F32, I32) => sat(self, op::I32_TRUNC_SAT_F32_S),
                (F64, I32) => sat(self, op::I32_TRUNC_SAT_F64_S),
                (F32, I64) => sat(self, op::I64_TRUNC_SAT_F32_S),
                (F64, I64) => sat(self, op::I64_TRUNC_SAT_F64_S),
                _ => return Err(self.bad_cast(op, src_vt, dst_vt)),
            },
            CastOp::FPToUI | CastOp::FPToUISat => match (src_vt, dst_vt) {
                (F32, I32) => sat(self, op::I32_TRUNC_SAT_F32_U),
                (F64, I32) => sat(self, op::I32_TRUNC_SAT_F64_U),
                (F32, I64) => sat(self, op::I64_TRUNC_SAT_F32_U),
                (F64, I64) => sat(self, op::I64_TRUNC_SAT_F64_U),
                _ => return Err(self.bad_cast(op, src_vt, dst_vt)),
            },
            // int → float reads the source at its own signedness: a narrow
            // operand is coerced to the matching full-carrier view first, so
            // `SIToFP` of `U8` 0xFF converts -1 (which is what the reference
            // interpreter's `as_signed` produces) and `UIToFP` converts 255.
            CastOp::SIToFP | CastOp::UIToFP => {
                let view = if op == CastOp::SIToFP {
                    IntView::Signed
                } else {
                    IntView::Unsigned
                };
                if let Some(src) = int_repr_of(src_ty) {
                    self.emit_view(src, view)?;
                }
                let opcode = match (op, src_vt, dst_vt) {
                    (CastOp::SIToFP, I32, F32) => op::F32_CONVERT_I32_S,
                    (CastOp::SIToFP, I32, F64) => op::F64_CONVERT_I32_S,
                    (CastOp::SIToFP, I64, F32) => op::F32_CONVERT_I64_S,
                    (CastOp::SIToFP, I64, F64) => op::F64_CONVERT_I64_S,
                    (CastOp::UIToFP, I32, F32) => op::F32_CONVERT_I32_U,
                    (CastOp::UIToFP, I32, F64) => op::F64_CONVERT_I32_U,
                    (CastOp::UIToFP, I64, F32) => op::F32_CONVERT_I64_U,
                    (CastOp::UIToFP, I64, F64) => op::F64_CONVERT_I64_U,
                    _ => return Err(self.bad_cast(op, src_vt, dst_vt)),
                };
                self.code.push(opcode);
            }
            CastOp::Bitcast => match (src_vt, dst_vt) {
                (I32, F32) => self.code.push(op::F32_REINTERPRET_I32),
                (F32, I32) => self.code.push(op::I32_REINTERPRET_F32),
                (I64, F64) => self.code.push(op::F64_REINTERPRET_I64),
                (F64, I64) => self.code.push(op::I64_REINTERPRET_F64),
                (a, b) if a == b => {} // same float repr: identity
                _ => return Err(self.bad_cast(op, src_vt, dst_vt)),
            },
            // Pointers are wasm32 i32. A ptr↔int pair that is integer-like on
            // both sides took the resize path above; anything left here is not.
            CastOp::PtrToInt | CastOp::IntToPtr | CastOp::PtrToPtr => {
                return Err(self.bad_cast(op, src_vt, dst_vt));
            }
            // A function item becomes a function pointer: both are the
            // callee's table index.
            CastOp::ReifyFnPointer if src_vt == ValType::I32 && dst_vt == ValType::I32 => {}
            // A same-size reinterpretation between scalars is a bitcast.
            CastOp::Transmute => {
                if let (Some(s), Some(d)) = (int_repr_of(src_ty), int_repr_of(dst_ty))
                    && src_vt == dst_vt
                    && s.bits == d.bits
                {
                    return self.emit_int_resize(s, d, IntView::Unsigned);
                }
                match (src_vt, dst_vt) {
                    (I32, F32) => self.code.push(op::F32_REINTERPRET_I32),
                    (F32, I32) => self.code.push(op::I32_REINTERPRET_F32),
                    (I64, F64) => self.code.push(op::F64_REINTERPRET_I64),
                    (F64, I64) => self.code.push(op::I64_REINTERPRET_F64),
                    (a, b)
                        if a == b
                            && int_repr_of(src_ty).is_none()
                            && int_repr_of(dst_ty).is_none() => {}
                    _ => return Err(self.bad_cast(op, src_vt, dst_vt)),
                }
            }
            CastOp::ReifyFnPointer => return Err(self.bad_cast(op, src_vt, dst_vt)),
        }
        Ok(())
    }

    /// Float → 8/16-bit integer, the float on the stack. wasm's `trunc_sat`
    /// saturates at the i32 CARRIER's bounds, not the narrow type's, so:
    ///
    /// 1. the SIGNED `i32.trunc_sat` for either op signedness — exact
    ///    truncation toward zero for `|v| < 2^31`, NaN to 0, saturating beyond,
    ///    and every 8/16-bit bound fits well inside;
    /// 2. a clamp to the OP's range — the reference interpreter takes the
    ///    saturation bounds from the op's signedness (`fptosi.sat` clamps to
    ///    `[-2^(N-1), 2^(N-1)-1]`, `fptoui.sat` to `[0, 2^N-1]`), whatever the
    ///    destination's;
    /// 3. the destination's canonical carrier (invariant N), which also
    ///    reinterprets a mixed-sign result (`fptosi.sat -200.0 -> u8` is
    ///    `0x80`, `fptoui.sat 300.0 -> i8` is `-1`).
    ///
    /// The raw `FPToSI`/`FPToUI` are undefined for NaN and out-of-range inputs;
    /// the saturated result refines that, exactly as the 32/64-bit lowering does.
    fn emit_float_to_narrow(
        &mut self,
        op: CastOp,
        src_vt: ValType,
        dst: IntRepr,
    ) -> Result<(), WasmLowerError> {
        let trunc = match src_vt {
            ValType::F32 => op::I32_TRUNC_SAT_F32_S,
            ValType::F64 => op::I32_TRUNC_SAT_F64_S,
            other => return Err(self.bad_cast(op, other, ValType::I32)),
        };
        if dst.carrier != ValType::I32 || !(1..32).contains(&dst.bits) {
            return Err(WasmLowerError::NarrowLegalization(format!(
                "Cast::{op:?} to a {}-bit {:?} carrier in `{}`",
                dst.bits, dst.carrier, self.func.name
            )));
        }
        self.code.push(op::FC_PREFIX);
        write_uleb128(&mut self.code, u64::from(trunc));
        let half = 1i64 << (dst.bits - 1);
        let (lo, hi) = if matches!(op, CastOp::FPToSI | CastOp::FPToSISat) {
            (-half, half - 1)
        } else {
            (0, 2 * half - 1)
        };
        let (lo, hi) = (lo as i32, hi as i32);
        let t = self.temp(ValType::I32);
        self.emit_local_set(t);
        // t = t > hi ? hi : t
        emit_i32_const(&mut self.code, hi);
        emit_local_get(&mut self.code, t);
        emit_local_get(&mut self.code, t);
        emit_i32_const(&mut self.code, hi);
        self.code.push(op::I32_GT_S);
        self.code.push(op::SELECT);
        self.emit_local_set(t);
        // t < lo ? lo : t
        emit_i32_const(&mut self.code, lo);
        emit_local_get(&mut self.code, t);
        emit_local_get(&mut self.code, t);
        emit_i32_const(&mut self.code, lo);
        self.code.push(op::I32_LT_S);
        self.code.push(op::SELECT);
        self.emit_canonicalize(dst)
    }

    fn bad_cast(&self, op: CastOp, s: ValType, d: ValType) -> WasmLowerError {
        WasmLowerError::UnsupportedInst(format!("Cast::{op:?} {s:?} -> {d:?}"))
    }

    /// Emit a float comparison, leaving an i32 (0/1) on the stack. wasm's
    /// `eq/lt/gt/le/ge` are ORDERED (false on NaN) and `ne` is UNORDERED (true
    /// on NaN), so the ordered/unordered trust-ir predicates are built from
    /// these plus `isnan(x) = f.ne(x,x)` and `i32.or`. ONe (ordered ne) =
    /// `lt | gt`. The formal proof discharges these against `encode_trust_ir_
    /// fcmp` over all bit patterns (NaN included).
    fn emit_fcmp(
        &mut self,
        cmp: FCmpOp,
        vt: ValType,
        a: u32,
        b: u32,
    ) -> Result<(), WasmLowerError> {
        let (eq, ne, lt, gt, le, ge) = match vt {
            ValType::F32 => (
                op::F32_EQ,
                op::F32_NE,
                op::F32_LT,
                op::F32_GT,
                op::F32_LE,
                op::F32_GE,
            ),
            ValType::F64 => (
                op::F64_EQ,
                op::F64_NE,
                op::F64_LT,
                op::F64_GT,
                op::F64_LE,
                op::F64_GE,
            ),
            other => {
                return Err(WasmLowerError::UnsupportedInst(format!(
                    "FCmp on {other:?}"
                )));
            }
        };
        // a <op> b → i32 bool.
        let bin = |s: &mut Self, opcode: u8| {
            emit_local_get(&mut s.code, a);
            emit_local_get(&mut s.code, b);
            s.code.push(opcode);
        };
        match cmp {
            FCmpOp::OEq => bin(self, eq),
            FCmpOp::OLt => bin(self, lt),
            FCmpOp::OLe => bin(self, le),
            FCmpOp::OGt => bin(self, gt),
            FCmpOp::OGe => bin(self, ge),
            // ordered-not-equal = (a<b) | (a>b).
            FCmpOp::ONe => {
                bin(self, lt);
                bin(self, gt);
                self.code.push(op::I32_OR);
            }
            // unordered-not-equal is exactly wasm f.ne.
            FCmpOp::UNe => bin(self, ne),
            // unordered X = (ordered X) | isnan(a) | isnan(b).
            FCmpOp::UEq | FCmpOp::ULt | FCmpOp::ULe | FCmpOp::UGt | FCmpOp::UGe => {
                let ordered = match cmp {
                    FCmpOp::UEq => eq,
                    FCmpOp::ULt => lt,
                    FCmpOp::ULe => le,
                    FCmpOp::UGt => gt,
                    FCmpOp::UGe => ge,
                    _ => unreachable!(),
                };
                bin(self, ordered);
                // | isnan(a): a != a  (unordered ne is true iff NaN)
                emit_local_get(&mut self.code, a);
                emit_local_get(&mut self.code, a);
                self.code.push(ne);
                self.code.push(op::I32_OR);
                // | isnan(b)
                emit_local_get(&mut self.code, b);
                emit_local_get(&mut self.code, b);
                self.code.push(ne);
                self.code.push(op::I32_OR);
            }
        }
        Ok(())
    }

    /// Emit a block's non-terminator instructions (everything but the last).
    fn emit_block_body(&mut self, cur: usize) -> Result<(), WasmLowerError> {
        let body_len = self.func.blocks[cur].body.len();
        for ni in 0..body_len.saturating_sub(1) {
            let node = &self.func.blocks[cur].body[ni];
            let results = node.results.clone();
            let inst = node.inst.clone();
            self.emit_inst(cur, ni, &results, &inst)?;
        }
        Ok(())
    }

    /// Fail closed unless scalar operand `v` is carried at the wasm value type
    /// of `ty` — the type the instruction declares for it. A producer that
    /// feeds (say) an `i64` into a 32-bit operation would otherwise yield a
    /// module whose operand stack does not type-check; the width mismatch is
    /// refused by name instead.
    fn check_operand(&self, v: ValueId, ty: &Ty) -> Result<(), WasmLowerError> {
        let Some(want) = layout::scalar_valtype(ty) else {
            return Ok(());
        };
        let got = match self.carriers.get(&v).copied() {
            Some(Carrier::Scalar(got)) => got,
            // A memory-carried value's local holds its ADDRESS, and a pair is
            // two locals; using either where a scalar is expected would read
            // the address, or half the value, as the value.
            Some(Carrier::Mem { .. } | Carrier::Pair) => {
                let actual = self.value_types.get(&v);
                return Err(WasmLowerError::UnsupportedInst(format!(
                    "operand {v:?} of memory-carried type {actual:?} is used as the scalar \
                     {ty:?} in `{}`",
                    self.func.name
                )));
            }
            _ => return Ok(()),
        };
        if got != want {
            let actual = self.value_types.get(&v);
            return Err(WasmLowerError::UnsupportedInst(format!(
                "operand {v:?} of type {actual:?} ({got:?}) is used as {ty:?} ({want:?}) in `{}`; \
                 the wasm lane does not reinterpret across value-type widths",
                self.func.name
            )));
        }
        Ok(())
    }

    /// The single result of a value-producing instruction.
    fn result1(&self, results: &[ValueId]) -> Result<ValueId, WasmLowerError> {
        results.first().copied().ok_or_else(|| {
            WasmLowerError::UnsupportedInst(format!(
                "value op without result in `{}`",
                self.func.name
            ))
        })
    }

    /// Whether `v` has a scalar local (a result bound to a zero-sized or
    /// unused value has none).
    fn scalar_result(&self, v: ValueId) -> Result<Option<u32>, WasmLowerError> {
        Ok(match self.carrier(v)? {
            Carrier::Scalar(_) => Some(slot(&self.locals, v)?.0),
            _ => None,
        })
    }

    /// Check every scalar operand whose wasm value type the instruction pins.
    fn check_inst_operands(&self, inst: &Inst) -> Result<(), WasmLowerError> {
        match inst {
            Inst::BinOp { ty, lhs, rhs, .. }
            | Inst::ICmp { ty, lhs, rhs, .. }
            | Inst::FCmp { ty, lhs, rhs, .. }
            | Inst::Overflow { ty, lhs, rhs, .. } => {
                self.check_operand(*lhs, ty)?;
                self.check_operand(*rhs, ty)
            }
            Inst::UnOp { ty, operand, .. } | Inst::Copy { ty, operand } => {
                self.check_operand(*operand, ty)
            }
            Inst::Cast {
                src_ty, operand, ..
            } => self.check_operand(*operand, src_ty),
            Inst::Select {
                ty,
                cond,
                then_val,
                else_val,
            } => {
                self.check_operand(*cond, &Ty::Bool)?;
                self.check_operand(*then_val, ty)?;
                self.check_operand(*else_val, ty)
            }
            Inst::Store { ty, ptr, value, .. } | Inst::AtomicStore { ty, ptr, value, .. } => {
                self.check_operand(*ptr, &Ty::Ptr)?;
                self.check_operand(*value, ty)
            }
            Inst::Load { ptr, .. } | Inst::AtomicLoad { ptr, .. } => {
                self.check_operand(*ptr, &Ty::Ptr)
            }
            Inst::AtomicRMW { ty, ptr, value, .. } => {
                self.check_operand(*ptr, &Ty::Ptr)?;
                self.check_operand(*value, ty)
            }
            Inst::CmpXchg {
                ty,
                ptr,
                expected,
                desired,
                ..
            } => {
                self.check_operand(*ptr, &Ty::Ptr)?;
                self.check_operand(*expected, ty)?;
                self.check_operand(*desired, ty)
            }
            Inst::GEP { base, .. } => self.check_operand(*base, &Ty::Ptr),
            Inst::Call { callee, args } => {
                let Some(ft) = self
                    .module
                    .function_by_id(*callee)
                    .and_then(|f| self.module.func_type(f.ty))
                else {
                    return Ok(());
                };
                for (a, t) in args.iter().zip(&ft.params) {
                    self.check_operand(*a, t)?;
                }
                Ok(())
            }
            Inst::CallIndirect { sig, args, .. } => {
                let Some(ft) = self.module.func_type(*sig) else {
                    return Ok(());
                };
                for (a, t) in args.iter().zip(&ft.params) {
                    self.check_operand(*a, t)?;
                }
                Ok(())
            }
            _ => Ok(()),
        }
    }

    fn emit_inst(
        &mut self,
        cur: usize,
        ni: usize,
        results: &[ValueId],
        inst: &Inst,
    ) -> Result<(), WasmLowerError> {
        self.check_inst_operands(inst)?;
        for &r in results {
            self.set_home_addr(r)?;
        }
        match inst {
            Inst::Const {
                value: Constant::FnDef(fid),
                ..
            } => {
                // A function pointer is its table index (`emit_func_ptr`).
                let widx = *self.call_targets.get(fid).ok_or_else(|| {
                    WasmLowerError::UnsupportedInst(format!("function pointer to unknown {fid:?}"))
                })?;
                let dst = slot(&self.locals, self.result1(results)?)?.0;
                self.emit_func_ptr(widx);
                self.emit_local_set(dst);
            }
            Inst::Const { ty, value } => {
                let r = self.result1(results)?;
                match self.carrier(r)? {
                    Carrier::Void => {}
                    Carrier::Mem { .. } => self.lower_mem_const(r)?,
                    Carrier::Pair => {
                        let k: u128 = match value {
                            Constant::Int(n) => *n as u128,
                            Constant::U128(n) => *n,
                            other => {
                                return Err(WasmLowerError::UnsupportedInst(format!(
                                    "a pair-carried {ty:?} constant {other:?} in `{}`",
                                    self.func.name
                                )));
                            }
                        };
                        self.const_pair(r, k)?;
                    }
                    Carrier::Scalar(_) => {
                        let dst = slot(&self.locals, r)?.0;
                        match (decode_body_global_addr_stub(ty, value), value) {
                            // The 0xFADE global-address stub: the address of
                            // `module.globals[index] + offset`, exactly as the
                            // native lower adapter decodes it.
                            (Some((index, offset)), _) => {
                                self.emit_global_stub(ty, index, offset)?
                            }
                            (None, Constant::SymbolAddr { symbol, addend }) => {
                                self.emit_symbol_addr(ty, symbol, *addend)?
                            }
                            (None, _) => self.emit_scalar_const(ty, value)?,
                        }
                        self.emit_local_set(dst);
                    }
                }
            }
            Inst::BinOp {
                op: bin,
                ty,
                lhs,
                rhs,
            } if wide::is_wide(ty) => {
                let r = self.result1(results)?;
                self.lower_wide_binop((cur, ni), r, *bin, *lhs, *rhs)?;
            }
            Inst::UnOp {
                op: un,
                ty,
                operand,
            } if wide::is_wide(ty) => {
                let r = self.result1(results)?;
                self.lower_wide_unop(r, *un, *operand)?;
            }
            Inst::ICmp {
                op: cmp,
                ty,
                lhs,
                rhs,
            } if wide::is_wide(ty) => {
                let r = self.result1(results)?;
                self.lower_wide_icmp(r, *cmp, *lhs, *rhs)?;
            }
            Inst::Overflow {
                op: oop,
                ty,
                lhs,
                rhs,
            } if wide::is_wide(ty) => {
                self.lower_wide_overflow(results, *oop, *ty == Ty::I128, *lhs, *rhs)?
            }
            Inst::BinOp {
                op: bin,
                ty,
                lhs,
                rhs,
            } => {
                let l = slot(&self.locals, *lhs)?.0;
                let r = slot(&self.locals, *rhs)?.0;
                let dst = slot(&self.locals, self.result1(results)?)?.0;
                let vt = valtype_of(ty)?;
                match bin {
                    BinOp::RotL | BinOp::RotR => self.emit_rotate(*bin, ty, l, r)?,
                    BinOp::FMin | BinOp::FMax | BinOp::FCopySign | BinOp::FRem => {
                        self.emit_float_binop(*bin, vt, l, r)?
                    }
                    _ => {
                        let bin = match bin {
                            // On the canonical 0/1 carrier the boolean
                            // connectives are the bitwise ones.
                            BinOp::BAnd => BinOp::And,
                            BinOp::BOr => BinOp::Or,
                            BinOp::BXor => BinOp::Xor,
                            other => *other,
                        };
                        let opcode = int_binop_opcode(bin, vt)?;
                        let narrow = narrow_of(ty);
                        let (lv, rv) = binop_operand_views(bin);
                        self.emit_operand(l, narrow, lv)?;
                        self.emit_operand(r, narrow, rv)?;
                        self.code.push(opcode);
                        self.canonicalize_result(ty)?;
                    }
                }
                self.emit_local_set(dst);
            }
            Inst::UnOp {
                op: un,
                ty,
                operand,
            } => {
                let src = slot(&self.locals, *operand)?.0;
                let dst = slot(&self.locals, self.result1(results)?)?.0;
                match un {
                    UnOp::CtLz | UnOp::CtTz | UnOp::BSwap | UnOp::BitReverse => {
                        self.emit_bit_unop(*un, ty, src)?
                    }
                    _ => self.emit_unop(*un, ty, src)?,
                }
                self.emit_local_set(dst);
            }
            Inst::Overflow {
                op: oop,
                ty,
                lhs,
                rhs,
            } => self.lower_overflow(results, *oop, ty, *lhs, *rhs)?,
            Inst::ICmp {
                op: cmp,
                ty,
                lhs,
                rhs,
            } => {
                let vt = valtype_of(ty)?;
                let cmp = carrier_predicate(*cmp, ty);
                let opcode = icmp_opcode(cmp, vt)?;
                let narrow = narrow_of(ty);
                let view = icmp_operand_view(cmp);
                let l = slot(&self.locals, *lhs)?.0;
                let r = slot(&self.locals, *rhs)?.0;
                let dst = slot(&self.locals, self.result1(results)?)?.0;
                self.emit_operand(l, narrow, view)?;
                self.emit_operand(r, narrow, view)?;
                self.code.push(opcode);
                // The result is a wasm boolean (0/1), already canonical.
                self.emit_local_set(dst);
            }
            Inst::FCmp {
                op: cmp,
                ty,
                lhs,
                rhs,
            } => {
                let vt = valtype_of(ty)?;
                let l = slot(&self.locals, *lhs)?.0;
                let r = slot(&self.locals, *rhs)?.0;
                let dst = slot(&self.locals, self.result1(results)?)?.0;
                self.emit_fcmp(*cmp, vt, l, r)?;
                self.emit_local_set(dst);
            }
            Inst::Cast {
                op: cop,
                src_ty,
                dst_ty,
                operand,
            } => {
                let r = self.result1(results)?;
                let wide_or_mem = |c: Carrier| c.is_mem() || c == Carrier::Pair;
                if wide_or_mem(self.carrier(r)?) || wide_or_mem(self.carrier(*operand)?) {
                    self.lower_mem_cast(r, *cop, src_ty, dst_ty, *operand)?;
                } else {
                    let src = slot(&self.locals, *operand)?.0;
                    let dst = slot(&self.locals, r)?.0;
                    emit_local_get(&mut self.code, src);
                    self.emit_cast(*cop, src_ty, dst_ty)?;
                    self.emit_local_set(dst);
                }
            }
            Inst::Copy { operand, .. } => {
                let r = self.result1(results)?;
                self.alias(r, *operand)?;
            }
            Inst::Select {
                cond,
                then_val,
                else_val,
                ..
            } => {
                let r = self.result1(results)?;
                self.lower_select(r, *cond, *then_val, *else_val)?;
            }
            Inst::NullPtr => {
                let dst = slot(&self.locals, self.result1(results)?)?.0;
                emit_i32_const(&mut self.code, 0);
                self.emit_local_set(dst);
            }
            Inst::Undef { ty } => {
                let r = self.result1(results)?;
                self.lower_undef(r, ty)?;
            }
            // A v52 source `Assert` is a Rust panic of a stated kind, not a
            // trap: the module floors of both the closed-module and object
            // lanes refuse it before any body is walked (an unsited check
            // and a sited one of `Unspecified` kind at the shared floor,
            // `reject_unconsumed_v41_target_neutral_surface`; every other
            // sited check at this lane's `reject_panic_sites`). This backstop
            // names the kind should a caller bypass those floors (the
            // per-function entry); it never lowers the panic to a generic
            // `unreachable`. v54 (amendment P): a sited check is refused by
            // name, as by `reject_panic_sites`.
            Inst::Assert {
                cond,
                kind,
                site: Some(site),
            } => {
                return Err(WasmLowerError::UnsupportedInst(format!(
                    "[TCG-ASSERT-PANIC] Inst::Assert {{ site: Some(_) }} on {cond:?} of kind `{}` \
                     calls panic entry {:?} on failure (trust-ir v54 panic site); the wasm lane \
                     lowers no panic-entry call, so it is refused rather than lowered to a trap",
                    kind.keyword(),
                    site.entry,
                )));
            }
            Inst::Assert {
                cond,
                kind,
                site: None,
            } => {
                return Err(WasmLowerError::UnsupportedInst(format!(
                    "[TCG-ASSERT-PANIC] source Assert on {cond:?} of kind `{}` needs {}; the \
                     wasm lane has no faithful panic route (payload, caller location, panic \
                     handler), so it is refused rather than lowered to a trap",
                    kind.keyword(),
                    kind.rust_panic_lang_item()
                        .unwrap_or("a stated panic kind (unspecified identity)"),
                )));
            }
            // An assumption is a proof hint: its failure is undefined
            // behaviour, which any behaviour (including none) refines.
            Inst::Assume { .. } => {}
            // Single-threaded wasm: every fence is trivially satisfied.
            Inst::Fence { .. } => {}
            Inst::Borrow { ptr } | Inst::BorrowMut { ptr } => {
                let r = self.result1(results)?;
                self.alias(r, *ptr)?;
            }
            // trust-ir v74 `Inst::BoxDeref`, admitted by the ONE acceptance
            // check both wasm module entries and the single-function entry
            // run before any body is walked (`trust_cg_lower::box_deref`,
            // through `validate_codegen_prerequisites`, the shared floor and
            // the codegen license). The result IS the operand, as a borrow's
            // is. The pointee and the fact are deliberately unread: no check
            // is removed and no memory access is emitted or moved on the
            // strength of a named assumption (section 28, "No licence").
            Inst::BoxDeref {
                ptr_ty: _,
                pointee: _,
                operand,
                fact: _,
            } => {
                let r = self.result1(results)?;
                self.alias(r, *operand)?;
            }
            Inst::EndBorrow { .. } => {}
            Inst::Alloca { .. } => {
                let result = self.result1(results)?;
                if let Some(&(size, align)) = self.dynamic_allocas.get(&result) {
                    let dst = slot(&self.locals, result)?.0;
                    return self.emit_dynamic_alloca(dst, size, align);
                }
                if let Some(&(count, elem_size, align)) = self.counted_allocas.get(&result) {
                    let dst = slot(&self.locals, result)?.0;
                    return self.emit_counted_alloca(dst, count, elem_size, align);
                }
                let off = *self.alloca_offsets.get(&result).ok_or_else(|| {
                    WasmLowerError::UnsupportedInst(format!(
                        "Alloca result {result:?} missing a frame slot"
                    ))
                })?;
                let dst = slot(&self.locals, result)?.0;
                // pointer = frame_base + offset
                let frame = self.frame.ok_or_else(|| {
                    WasmLowerError::UnsupportedInst(
                        "Alloca has no prepared shadow-stack frame".to_string(),
                    )
                })?;
                emit_local_get(&mut self.code, frame.base_local);
                emit_i32_const(&mut self.code, off as i32);
                self.code.push(op::I32_ADD);
                self.emit_local_set(dst);
            }
            Inst::GEP {
                pointee_ty,
                base,
                indices,
                ..
            } => {
                let dst = slot(&self.locals, self.result1(results)?)?.0;
                let base_l = slot(&self.locals, *base)?.0;
                let elem_size = self.size_of(pointee_ty)?;

                // TrustIR GEP is flat: every index is scaled by the
                // complete pointee extent. Empty indices preserve base. An
                // index of any width is read modulo 2^32 (`emit_index_i32`):
                // wrapping i32 arithmetic is exact on every GEP whose result
                // is a wasm32 address, and any other is undefined behaviour.
                // A one-byte element needs no scaling: `index * 1 = index`
                // in i32 arithmetic, so at O1 and above the multiply is not
                // emitted (the mid-end's byte-offset GEPs are this form).
                emit_local_get(&mut self.code, base_l);
                for index in indices {
                    self.emit_index_i32(*index, "GEP index")?;
                    if !(self.unit_scale_elided && elem_size == 1) {
                        emit_i32_const(&mut self.code, elem_size as i32);
                        self.code.push(op::I32_MUL);
                    }
                    self.code.push(op::I32_ADD);
                }
                // A single-index GEP's address addition does not wrap when the
                // GEP is defined: claimed here, admitted only by the checker.
                if let ([_], [value]) = (indices.as_slice(), results)
                    && let Ok(add_offset) = u32::try_from(self.code.len() - 1)
                {
                    self.nowrap_claims.push(NoWrapClaim {
                        value: *value,
                        add_offset,
                    });
                }
                self.emit_local_set(dst);
            }
            // A narrow load picks the EXTENDING opcode its type demands
            // (`i32.load8_s` for `I8`, `i32.load8_u` for `U8`, …), so the
            // value lands in its canonical carrier form with no extra
            // instruction; a narrow store writes the low bits of that same
            // canonical carrier with `i32.store8` / `i32.store16`.
            Inst::Load { ty, ptr, .. } | Inst::AtomicLoad { ty, ptr, .. } => {
                let r = self.result1(results)?;
                match self.carrier(r)? {
                    Carrier::Void => {}
                    Carrier::Mem { .. } => self.lower_mem_load(r, *ptr)?,
                    Carrier::Pair => {
                        let p = slot(&self.locals, *ptr)?.0;
                        self.load_pair_from(r, 0, &|s: &mut Self| emit_local_get(&mut s.code, p))?;
                    }
                    Carrier::Scalar(_) => {
                        let (load_op, _, align) = mem_ops(ty)?;
                        let p = slot(&self.locals, *ptr)?.0;
                        let dst = slot(&self.locals, r)?.0;
                        emit_local_get(&mut self.code, p);
                        self.code.push(load_op);
                        emit_memarg(&mut self.code, align, 0);
                        self.emit_local_set(dst);
                    }
                }
            }
            Inst::Store { ty, ptr, value, .. } | Inst::AtomicStore { ty, ptr, value, .. } => {
                // Keyed on the DECLARED type: a memory-carried value, or a
                // pointer-carried aggregate, is a byte copy.
                match layout::carrier_of(self.module, ty)? {
                    Carrier::Void => {}
                    Carrier::Mem { size, .. } if self.is_pair(*value) => {
                        // A pair's image is exactly its two halves.
                        if size != 16 {
                            return Err(WasmLowerError::UnsupportedInst(format!(
                                "a 128-bit pair stored as the {size}-byte {ty:?} in `{}`",
                                self.func.name
                            )));
                        }
                        let p = slot(&self.locals, *ptr)?.0;
                        self.store_pair_at(p, 0, *value)?;
                    }
                    Carrier::Mem { size, .. } => {
                        let src = self.addr_local(*value)?;
                        let p = slot(&self.locals, *ptr)?.0;
                        self.emit_copy(p, 0, src, 0, size);
                    }
                    Carrier::Pair => {
                        return Err(WasmLowerError::UnsupportedType(format!(
                            "{ty:?} has no type-level pair carrier"
                        )));
                    }
                    Carrier::Scalar(_) => {
                        let (_, store_op, align) = mem_ops(ty)?;
                        let p = slot(&self.locals, *ptr)?.0;
                        let v = slot(&self.locals, *value)?.0;
                        emit_local_get(&mut self.code, p); // address
                        emit_local_get(&mut self.code, v); // value
                        self.code.push(store_op);
                        emit_memarg(&mut self.code, align, 0);
                    }
                }
            }
            Inst::AtomicRMW {
                op: rop,
                ty,
                ptr,
                value,
                ..
            } => self.lower_atomic_rmw(results.first().copied(), *rop, ty, *ptr, *value)?,
            Inst::CmpXchg {
                ty,
                ptr,
                expected,
                desired,
                ..
            } => self.lower_cmpxchg(results, ty, *ptr, *expected, *desired)?,
            Inst::MemCopy {
                dst, src, bytes, ..
            } => self.lower_memcopy(*dst, *src, *bytes)?,
            Inst::MemSet { dst, byte, bytes } => self.lower_memset(*dst, *byte, *bytes)?,
            // A module global's address: an absolute address in a closed
            // module, a relocated data-symbol address in an object.
            Inst::GlobalAddr { global } => {
                let addr = *self.global_addrs.get(global).ok_or_else(|| {
                    WasmLowerError::UnsupportedInst(format!(
                        "GlobalAddr of unknown {global:?} in `{}`",
                        self.func.name
                    ))
                })?;
                let dst = slot(&self.locals, self.result1(results)?)?.0;
                self.emit_data_addr(addr, 0);
                self.emit_local_set(dst);
            }
            Inst::ExtractField {
                ty,
                aggregate,
                field,
            } => {
                let r = self.result1(results)?;
                self.lower_extract_field(r, ty, *aggregate, *field)?;
            }
            Inst::InsertField {
                ty,
                aggregate,
                field,
                value,
            } => {
                let r = self.result1(results)?;
                self.lower_insert_field(r, ty, *aggregate, *field, *value)?;
            }
            Inst::ExtractElement { ty, array, index } => {
                let r = self.result1(results)?;
                self.lower_extract_element(r, ty, *array, *index)?;
            }
            Inst::InsertElement {
                ty,
                array,
                index,
                value,
            } => {
                let r = self.result1(results)?;
                self.lower_insert_element(r, ty, *array, *index, *value)?;
            }
            Inst::MakeAggregate {
                ty,
                variant,
                fields,
            } => {
                let r = self.result1(results)?;
                self.lower_make_aggregate(r, ty, *variant, fields)?;
            }
            Inst::ArraySplat { ty, value } => {
                let r = self.result1(results)?;
                self.lower_array_splat(r, ty, *value)?;
            }
            Inst::PtrData { ptr_ty, ptr } => {
                let r = self.result1(results)?;
                self.lower_ptr_data(r, ptr_ty, *ptr)?;
            }
            Inst::PtrMetadata { ptr_ty, ptr, .. } => {
                if let Some(r) = results.first() {
                    self.lower_ptr_metadata(*r, ptr_ty, *ptr)?;
                }
            }
            Inst::PtrFromParts {
                ptr_ty,
                data,
                metadata,
                ..
            } => {
                let r = self.result1(results)?;
                self.lower_ptr_from_parts(r, ptr_ty, *data, *metadata)?;
            }
            Inst::CallIndirect {
                callee,
                sig,
                args,
                calling_conv,
            } => {
                self.lower_call_indirect((cur, ni), results, *callee, *sig, args, *calling_conv)?
            }
            Inst::Call { callee, args } => self.lower_call((cur, ni), results, *callee, args)?,
            other => {
                return Err(WasmLowerError::UnsupportedInst(format!(
                    "{other:?} (not lowered by the wasm backend)"
                )));
            }
        }
        let _ = Self::scalar_result;
        Ok(())
    }

    /// Emit a constant onto the wasm operand stack.
    ///
    /// An integer constant is canonicalized into its carrier AT COMPILE TIME
    /// (invariant N): `Const { ty: U8, value: 300 }` emits `i32.const 44` and
    /// `Const { ty: I8, value: 200 }` emits `i32.const -56`, so no
    /// re-canonicalization instruction is ever needed after a constant.
    fn emit_scalar_const(&mut self, ty: &Ty, value: &Constant) -> Result<(), WasmLowerError> {
        self.emit_const(ty, value)
    }

    /// Push the address a global-address stub names (see
    /// [`crate::global_stub`]); the legacy `i64` carrier gets it zero-extended.
    fn emit_global_stub(&mut self, ty: &Ty, index: u64, offset: u32) -> Result<(), WasmLowerError> {
        let global = u32::try_from(index)
            .ok()
            .map(trust_ir::value::GlobalId::new)
            .and_then(|g| self.global_addrs.get(&g).copied())
            .ok_or_else(|| {
                WasmLowerError::UnsupportedInst(format!(
                    "global-address stub names global {index}, which `{}`'s module does not have",
                    self.func.name
                ))
            })?;
        let addend = i32::try_from(offset).map_err(|_| {
            WasmLowerError::UnsupportedInst(format!(
                "global-address stub offset {offset} exceeds the wasm32 address space"
            ))
        })?;
        self.emit_data_addr(global, addend);
        if *ty == Ty::I64 {
            self.code.push(op::I64_EXTEND_I32_U);
        }
        Ok(())
    }

    /// Push the address a function-body `Const SymbolAddr` names, through the
    /// same resolver static-data images use ([`layout::resolve_symbol`]): a
    /// module global's data address plus `addend` (relocated in an object, as
    /// `GlobalAddr` is), a function's table index (as `FnDef` is), or — in a
    /// relocatable object only — an undefined data symbol the linker binds. A
    /// closed module has no linker, so a symbol it does not define is refused,
    /// as its static data refuses one.
    fn emit_symbol_addr(
        &mut self,
        ty: &Ty,
        symbol: &str,
        addend: i64,
    ) -> Result<(), WasmLowerError> {
        if layout::scalar_valtype(ty) != Some(ValType::I32) {
            return Err(WasmLowerError::UnsupportedInst(format!(
                "Const symaddr<{symbol}> at {ty:?} in `{}`: a wasm32 address is an i32",
                self.func.name
            )));
        }
        let addend32 = i32::try_from(addend).map_err(|_| {
            WasmLowerError::UnsupportedInst(format!(
                "Const symaddr<{symbol} + {addend}> in `{}`: the addend exceeds the wasm32 \
                 address space",
                self.func.name
            ))
        })?;
        let target = layout::resolve_symbol(self.module, symbol, addend).map_err(|why| {
            WasmLowerError::UnsupportedInst(format!(
                "Const symaddr<{symbol} + {addend}> in `{}`: {why}",
                self.func.name
            ))
        })?;
        match target {
            layout::ImageRef::Global(gid, _) => {
                let addr = *self.global_addrs.get(&gid).ok_or_else(|| {
                    WasmLowerError::UnsupportedInst(format!(
                        "Const symaddr<{symbol}> of unknown {gid:?} in `{}`",
                        self.func.name
                    ))
                })?;
                self.emit_data_addr(addr, addend32);
            }
            layout::ImageRef::Func(fid) => {
                let widx = *self.call_targets.get(&fid).ok_or_else(|| {
                    WasmLowerError::UnsupportedInst(format!(
                        "Const symaddr<{symbol}> of unknown {fid:?} in `{}`",
                        self.func.name
                    ))
                })?;
                self.emit_func_ptr(widx);
            }
            layout::ImageRef::Symbol(name, _) => {
                let addr = *self.extern_data.get(&name).ok_or_else(|| {
                    WasmLowerError::UnsupportedInst(format!(
                        "Const symaddr<{name}> in `{}` names a symbol this closed module does \
                         not define; only a relocatable object can refer to an external symbol",
                        self.func.name
                    ))
                })?;
                self.emit_data_addr(addr, addend32);
            }
        }
        Ok(())
    }

    fn emit_const(&mut self, ty: &Ty, value: &Constant) -> Result<(), WasmLowerError> {
        let vt = valtype_of(ty)?;
        let repr = int_repr_of(ty);
        match (vt, value) {
            // A `Bool` holds only 0 and 1. The 1-bit carrier would mask any other
            // integer (`const bool 2` would become `false`), so refuse it as the
            // native adapter does; the interpreter rejects it as ill-typed.
            (ValType::I32, Constant::Int(n)) if matches!(ty, Ty::Bool) && !matches!(*n, 0 | 1) => {
                return Err(WasmLowerError::UnsupportedInst(format!(
                    "Const {n} does not fit in Bool (range [0, 1])"
                )));
            }
            (ValType::I32, Constant::Int(n)) => {
                let carried = repr
                    .ok_or_else(|| {
                        WasmLowerError::UnsupportedInst(format!("integer Const at {ty:?}"))
                    })?
                    .carrier_value(*n);
                emit_i32_const(&mut self.code, carried as i32);
            }
            (ValType::I32, Constant::Bool(b)) => emit_i32_const(&mut self.code, i32::from(*b)),
            (ValType::I64, Constant::Int(n)) => {
                let carried = repr
                    .ok_or_else(|| {
                        WasmLowerError::UnsupportedInst(format!("integer Const at {ty:?}"))
                    })?
                    .carrier_value(*n);
                self.code.push(op::I64_CONST);
                write_sleb128(&mut self.code, carried);
            }
            // Float constants carry their exact bit pattern (WebAssembly Core
            // Specification: `f32.const` / `f64.const` take a raw little-endian
            // IEEE-754 payload, not a LEB128).
            (ValType::F32, Constant::Float(f)) => {
                self.code.push(op::F32_CONST);
                self.code.extend_from_slice(&(*f as f32).to_le_bytes());
            }
            (ValType::F64, Constant::Float(f)) => {
                self.code.push(op::F64_CONST);
                self.code.extend_from_slice(&f.to_le_bytes());
            }
            _ => {
                return Err(WasmLowerError::UnsupportedInst(format!(
                    "Const {value:?} as {vt:?} (supported: integer/bool/float constants)"
                )));
            }
        }
        Ok(())
    }

    /// Set a target block's param locals from an edge's args (phi resolution).
    /// Permutation-safe: scalar sources are all pushed onto the operand stack
    /// before any destination is `local.set` (in reverse), so a swap like
    /// `br head [b, a]` is correct; memory-carried parameters are copied, in
    /// two phases through staging slots when a block has several of them.
    fn set_params(&mut self, target: BlockId, args: &[ValueId]) -> Result<(), WasmLowerError> {
        let ti = self.idx(target)?;
        let params = &self.func.blocks[ti].params;
        if params.len() != args.len() {
            return Err(WasmLowerError::ArityMismatch(format!(
                "block {ti}: {} params vs {} args",
                params.len(),
                args.len()
            )));
        }
        let pairs: Vec<(ValueId, ValueId)> = params
            .iter()
            .map(|(p, _)| *p)
            .zip(args.iter().copied())
            .collect();
        let mem_pairs: Vec<(ValueId, ValueId)> = pairs
            .iter()
            .copied()
            .filter(|(p, _)| self.carriers.get(p).is_some_and(|c| c.is_mem()))
            .collect();
        for &(p, _) in &mem_pairs {
            self.set_home_addr(p)?;
        }
        match mem_pairs.len() {
            0 => {}
            1 => self.copy_edge_arg(mem_pairs[0].0, mem_pairs[0].1)?,
            _ => self.copy_edge_args_staged(&mem_pairs)?,
        }
        // Every scalar and pair argument is read before any parameter is
        // written (a parallel copy on the operand stack), so an argument that
        // is itself a parameter of the target is read before it changes.
        let mut dest_locals: Vec<u32> = Vec::with_capacity(args.len());
        for (p, a) in pairs {
            match self.carriers.get(&p) {
                Some(Carrier::Scalar(_)) => {
                    let pty = self.value_ty(p)?;
                    self.check_operand(a, &pty)?;
                    let a = slot(&self.locals, a)?.0;
                    let p = slot(&self.locals, p)?.0;
                    emit_local_get(&mut self.code, a);
                    dest_locals.push(p);
                }
                Some(Carrier::Pair) => {
                    // `pair::pair_carried` ties an argument's class to its
                    // parameter's, so the argument is a pair too.
                    let (alo, ahi) = self.pair_of(a)?;
                    let (plo, phi) = self.pair_of(p)?;
                    emit_local_get(&mut self.code, alo);
                    emit_local_get(&mut self.code, ahi);
                    dest_locals.push(plo);
                    dest_locals.push(phi);
                }
                _ => {}
            }
        }
        for &p in dest_locals.iter().rev() {
            self.emit_local_set(p);
        }
        Ok(())
    }

    /// Resolve a `br` to `target` of the given frame kind, returning the depth
    /// immediate. `N = open_labels - frame_depth` (counts the enclosing `if`).
    fn resolve_branch(&self, want_loop: bool, target: usize) -> Result<u32, WasmLowerError> {
        for (frame, depth) in self.context.iter().rev() {
            let matches = match frame {
                Frame::Loop(t) => want_loop && *t == target,
                Frame::Block(t) => !want_loop && *t == target,
                Frame::Dispatch => false,
            };
            if matches {
                return Ok(self.open_labels - depth);
            }
        }
        Err(WasmLowerError::UnsupportedControlFlow(format!(
            "branch target block {target} not in scope — unstructured CFG in `{}`",
            self.func.name
        )))
    }

    /// The dominator-tree children of `x` that are merge nodes (RPO-sorted).
    fn merge_children(&self, x: usize) -> Vec<usize> {
        self.dom_children[x]
            .iter()
            .copied()
            .filter(|&c| self.is_merge[c])
            .collect()
    }

    /// Open a structured-control scope: emit the opcode, push the frame.
    fn open_scope(&mut self, frame: Frame) {
        let opcode = match frame {
            Frame::Loop(_) | Frame::Dispatch => op::LOOP,
            Frame::Block(_) => op::BLOCK,
        };
        self.code.push(opcode);
        self.code.push(op::BLOCKTYPE_VOID);
        self.open_labels += 1;
        self.context.push((frame, self.open_labels));
    }

    fn close_scope(&mut self) {
        self.code.push(op::END);
        self.context.pop();
        self.open_labels -= 1;
    }

    /// Emit the structured control flow of the whole function: the
    /// dominator-tree relooper (Ramsey, "Beyond Relooper", ICFP 2022) rooted
    /// at `entry`.
    ///
    /// The walk is driven by an explicit work stack of [`Step`]s, never by
    /// Rust recursion, so the compiler's own stack depth is constant however
    /// deep the dominator tree or however many cases a `Switch` has. Each
    /// step does exactly what one level of the recursive formulation did, in
    /// the same order, so the emitted bytes are the recursive relooper's:
    ///
    /// * `Tree(x)` — a loop header opens a `loop`; then a `block` for each
    ///   merge child of `x`, LATEST-RPO outermost; then `x`'s own code; then,
    ///   after each block's `end`, that merge child's subtree (its join).
    ///   The nesting order is load-bearing: control inside a dominator
    ///   subtree flows FORWARD in reverse-postorder, so an earlier merge
    ///   child's subtree may branch to a later one but never the reverse,
    ///   and putting the latest-RPO block outermost keeps its label in scope
    ///   while every earlier child's subtree is emitted:
    ///
    ///   ```text
    ///   block $Y_n            ;; latest RPO — outermost
    ///     block $Y_1          ;; earliest RPO — innermost
    ///       <x's code>        ;; may br to every $Y_i
    ///     end
    ///     <Y_1's subtree>     ;; still inside $Y_n, so it may br to it
    ///   end
    ///   <Y_n's subtree>
    ///   ```
    ///
    ///   (The shape that needs this appears as soon as a node has two merge
    ///   children, e.g. a `Switch` whose default edge reuses one of its own
    ///   case blocks.)
    /// * `Node(x)` — `x`'s body and terminator; an edge is `Branch`.
    /// * `Branch(x, t)` — a back-edge is a `br` to the loop label, a forward
    ///   edge to a merge node a `br` to its block label; any other edge
    ///   inlines `t`'s subtree (`Tree(t)`).
    fn emit_structured(&mut self, entry: usize) -> Result<(), WasmLowerError> {
        if self.dispatch.is_some() {
            return self.emit_dispatch();
        }
        self.run_steps(vec![Step::Tree(entry)])
    }

    /// Emit an IRREDUCIBLE CFG — one with a cycle entered at more than one
    /// block, which no nest of wasm `block`/`loop` scopes can express as it
    /// stands — as a dispatch loop over a label local:
    ///
    /// ```text
    /// label := 0                        ;; the entry's position
    /// loop $dispatch
    ///   block $b_{k-1} … block $b_0
    ///     block $bad
    ///       br_table $b_0 … $b_{k-1} $bad (label)
    ///     end
    ///     unreachable                   ;; no block has that position
    ///   end                             ;; $b_0
    ///   <block order[0]>                ;; each edge: its arguments,
    ///   unreachable                     ;;   label := target; br $dispatch
    ///   …
    /// end
    /// ```
    ///
    /// Every reachable block is emitted once, in reverse postorder, after
    /// the `end` of its own label, and every edge (forward, backward or
    /// switch arm) binds its target's parameters exactly as the relooper's
    /// edges do ([`Self::set_params`]), then sets the label to the target's
    /// position and re-enters the loop. A block's code ends in a branch, a
    /// `return` or a trap, so the `unreachable` after it never runs. The
    /// relooper still structures every reducible CFG.
    fn emit_dispatch(&mut self) -> Result<(), WasmLowerError> {
        let order = match &self.dispatch {
            Some(plan) => plan.order.clone(),
            None => return Ok(()),
        };
        let label = self.temp(ValType::I32);
        if let Some(plan) = &mut self.dispatch {
            plan.label = Some(label);
        }
        emit_i32_const(&mut self.code, 0);
        self.emit_local_set(label);
        self.open_scope(Frame::Dispatch);
        for _ in 0..order.len() {
            self.open_anon_block(); // $b_{k-1} … $b_0
        }
        self.open_anon_block(); // $bad
        emit_local_get(&mut self.code, label);
        // From inside $bad, $b_i is i + 1 labels out and $bad is 0.
        self.code.push(op::BR_TABLE);
        write_uleb128(&mut self.code, order.len() as u64);
        for i in 0..order.len() {
            write_uleb128(&mut self.code, i as u64 + 1);
        }
        write_uleb128(&mut self.code, 0);
        self.close_anon_block(); // end $bad
        self.code.push(op::UNREACHABLE);
        for &x in &order {
            self.close_anon_block(); // end $b_i: block x's code follows
            self.run_steps(vec![Step::Node(x)])?;
            self.code.push(op::UNREACHABLE);
        }
        self.close_scope(); // end $dispatch
        Ok(())
    }

    /// `label := position(t); br $dispatch` — an edge of a dispatch-lowered
    /// function, after its arguments are bound.
    fn emit_dispatch_edge(&mut self, t: usize) -> Result<(), WasmLowerError> {
        let (pos, label) = match &self.dispatch {
            Some(DispatchPlan {
                position,
                label: Some(label),
                ..
            }) => (position[t], *label),
            _ => {
                return Err(WasmLowerError::UnsupportedControlFlow(format!(
                    "dispatch edge in `{}` outside its dispatch loop",
                    self.func.name
                )));
            }
        };
        let pos = i32::try_from(pos).map_err(|_| {
            WasmLowerError::UnsupportedControlFlow(format!(
                "dispatch edge in `{}` to unreachable block {t}",
                self.func.name
            ))
        })?;
        emit_i32_const(&mut self.code, pos);
        self.emit_local_set(label);
        let depth = self
            .context
            .iter()
            .rev()
            .find(|(frame, _)| *frame == Frame::Dispatch)
            .map(|(_, depth)| self.open_labels - depth)
            .ok_or_else(|| {
                WasmLowerError::UnsupportedControlFlow(format!(
                    "dispatch edge in `{}` outside its dispatch loop",
                    self.func.name
                ))
            })?;
        self.code.push(op::BR);
        write_uleb128(&mut self.code, u64::from(depth));
        Ok(())
    }

    /// Run [`Step`]s until the work stack is empty.
    fn run_steps(&mut self, mut work: Vec<Step>) -> Result<(), WasmLowerError> {
        while let Some(step) = work.pop() {
            match step {
                Step::Tree(x) => {
                    let merge_kids = self.merge_children(x);
                    if self.is_header[x] {
                        self.open_scope(Frame::Loop(x));
                        work.push(Step::CloseScope);
                    }
                    for &y in merge_kids.iter().rev() {
                        self.open_scope(Frame::Block(y));
                        work.push(Step::Tree(y));
                        work.push(Step::CloseScope);
                    }
                    work.push(Step::Node(x));
                }
                Step::Node(x) => {
                    if !self.emitted.insert(x) {
                        return Err(WasmLowerError::UnsupportedControlFlow(format!(
                            "re-emission of block {x} in `{}` — unstructured/irreducible CFG",
                            self.func.name
                        )));
                    }
                    self.emit_block_body(x)?;
                    self.emit_terminator(x, &mut work)?;
                }
                Step::Branch(x, t) => {
                    if self.dispatch.is_some() {
                        self.emit_dispatch_edge(t)?;
                    } else if self.back_edges.contains(&(x, t)) {
                        let n = self.resolve_branch(true, t)?;
                        self.code.push(op::BR);
                        write_uleb128(&mut self.code, u64::from(n));
                    } else if self.is_merge[t] {
                        let n = self.resolve_branch(false, t)?;
                        self.code.push(op::BR);
                        write_uleb128(&mut self.code, u64::from(n));
                    } else {
                        work.push(Step::Tree(t));
                    }
                }
                Step::SetParams(target, args) => self.set_params(target, &args)?,
                Step::CaseTest {
                    vlocal,
                    eq,
                    value_ty,
                    value,
                    target,
                    args,
                } => {
                    // The switch value is a canonical carrier and the case
                    // constant is canonicalized to the same form by
                    // `emit_const`, so an equality test needs no coercion on
                    // either side (invariant N).
                    emit_local_get(&mut self.code, vlocal);
                    self.emit_const(&value_ty, &value)?;
                    self.code.push(eq);
                    self.open_if();
                    self.set_params(target, &args)?;
                }
                Step::WideCaseTest {
                    src,
                    value,
                    target,
                    args,
                } => {
                    let k: u128 = match value {
                        Constant::Int(n) => n as u128,
                        Constant::U128(n) => n,
                        ref other => {
                            return Err(WasmLowerError::UnsupportedInst(format!(
                                "128-bit Switch case {other:?}"
                            )));
                        }
                    };
                    self.emit_wide_case_eq(src, k)?;
                    self.open_if();
                    self.set_params(target, &args)?;
                }
                Step::Else => self.code.push(op::ELSE),
                Step::CloseScope => self.close_scope(),
                Step::CloseIf => self.close_if(),
                Step::CloseAnon => self.close_anon_block(),
                Step::BrOut(depth) => {
                    self.code.push(op::BR);
                    write_uleb128(&mut self.code, depth);
                }
            }
        }
        Ok(())
    }

    /// Emit `x`'s terminator, pushing onto `work` (in reverse) the steps that
    /// follow it: each edge's `Branch`, and the code between and after them.
    fn emit_terminator(&mut self, x: usize, work: &mut Vec<Step>) -> Result<(), WasmLowerError> {
        let term = terminator_of(self.func, x)?.clone();
        match term {
            Inst::Return { values } => self.emit_return(&values)?,
            Inst::Unreachable => self.code.push(op::UNREACHABLE),
            Inst::Br { target, args } => {
                self.set_params(target, &args)?;
                let t = self.idx(target)?;
                work.push(Step::Branch(x, t));
            }
            Inst::CondBr {
                cond,
                then_target,
                then_args,
                else_target,
                else_args,
            } => {
                let then_i = self.idx(then_target)?;
                let else_i = self.idx(else_target)?;
                let cond_local = slot(&self.locals, cond)?.0;
                emit_local_get(&mut self.code, cond_local);
                self.open_if();
                self.set_params(then_target, &then_args)?;
                work.push(Step::CloseIf);
                work.push(Step::Branch(x, else_i));
                work.push(Step::SetParams(else_target, else_args));
                work.push(Step::Else);
                work.push(Step::Branch(x, then_i));
            }
            // `exhaustive_enum_unreachable` only authorizes DROPPING the default
            // edge; both lowerings below always emit it (a correct superset),
            // so the hint is not consulted here.
            Inst::Switch {
                value,
                default,
                default_args,
                cases,
                exhaustive_enum_unreachable: _,
            } => {
                let value_ty = self.value_ty(value)?;
                if wide::is_wide(&value_ty) {
                    let src = self.wide_source(value)?;
                    self.push_cascade(x, cases, default, default_args, work, |case| {
                        Ok(Step::WideCaseTest {
                            src,
                            value: case.value,
                            target: case.target,
                            args: case.args,
                        })
                    })?;
                    return Ok(());
                }
                let (vlocal, vt) = slot(&self.locals, value)?;
                match br_table_plan(&value_ty, &cases)? {
                    // A dense-enough case range: one `br_table` dispatch.
                    Some(plan) => self.emit_switch_br_table(
                        vlocal,
                        &plan,
                        x,
                        cases,
                        default,
                        default_args,
                        work,
                    )?,
                    // Otherwise an if/else compare-cascade: each case is
                    // `if value == k { <case edge> } else { <rest> }`, ending in
                    // the default edge. Case targets that are merge nodes,
                    // back-edges or inlinable blocks are all `Branch` steps. The
                    // nested `if`s are counted in open_labels, so branch depths
                    // stay correct.
                    None => {
                        let eq = if cases.is_empty() {
                            op::I32_EQ
                        } else {
                            match vt {
                                ValType::I32 => op::I32_EQ,
                                ValType::I64 => op::I64_EQ,
                                other => {
                                    return Err(WasmLowerError::UnsupportedInst(format!(
                                        "Switch on {other:?} (supported: i32/i64)"
                                    )));
                                }
                            }
                        };
                        self.push_cascade(x, cases, default, default_args, work, |case| {
                            Ok(Step::CaseTest {
                                vlocal,
                                eq,
                                value_ty: value_ty.clone(),
                                value: case.value,
                                target: case.target,
                                args: case.args,
                            })
                        })?;
                    }
                }
            }
            other => {
                return Err(WasmLowerError::UnsupportedControlFlow(format!(
                    "terminator {other:?}"
                )));
            }
        }
        Ok(())
    }

    /// Push a `Switch` compare-cascade: for each case in order, its test
    /// (opening an `if`), its edge, and an `else`; then the default edge,
    /// then one `end` per case.
    fn push_cascade(
        &self,
        x: usize,
        cases: Vec<trust_ir::SwitchCase>,
        default: BlockId,
        default_args: Vec<ValueId>,
        work: &mut Vec<Step>,
        mut test: impl FnMut(trust_ir::SwitchCase) -> Result<Step, WasmLowerError>,
    ) -> Result<(), WasmLowerError> {
        let d = self.idx(default)?;
        let mut targets = Vec::with_capacity(cases.len());
        for case in &cases {
            targets.push(self.idx(case.target)?);
        }
        work.reserve(cases.len() * 4 + 2);
        work.extend(std::iter::repeat_with(|| Step::CloseIf).take(cases.len()));
        work.push(Step::Branch(x, d));
        work.push(Step::SetParams(default, default_args));
        for (case, t) in cases.into_iter().zip(targets).rev() {
            work.push(Step::Else);
            work.push(Step::Branch(x, t));
            work.push(test(case)?);
        }
        Ok(())
    }

    /// Emit an `if`/`else` opener with a void blocktype, counting the label.
    fn open_if(&mut self) {
        self.code.push(op::IF);
        self.code.push(op::BLOCKTYPE_VOID);
        self.open_labels += 1;
    }

    fn close_if(&mut self) {
        self.code.push(op::END);
        self.open_labels -= 1;
    }

    /// Lower a `Switch` to `br_table` (opcode `0x0e`; WebAssembly Core
    /// Specification, "Control Instructions": `br_table l* lN`, which pops an
    /// `i32` index `i` and branches to `l[i]` when `i < |l*|` — the index is
    /// UNSIGNED — and to `lN` otherwise).
    ///
    /// The block nest is the standard one:
    ///
    /// ```text
    /// block $out
    ///   block $default
    ///     block $arm_{m-1} … block $arm_0
    ///       block $dispatch
    ///         <index>            ;; value - min, wrapping
    ///         br_table $arm_0 … $arm_{m-1} $default
    ///       end                  ;; $dispatch — unreachable, br_table always branches
    ///     end                    ;; $arm_0 …  each `end` falls into the next arm's code
    ///     <arm 0>; br $out
    ///     …
    ///   end                      ;; $default
    ///   <default>
    /// end                        ;; $out — the switch's continuation
    /// ```
    ///
    /// The trailing `br $out` after each arm is what makes the nest safe: an
    /// arm's code may FALL THROUGH (a `Branch` inlines a subtree whose own
    /// paths end elsewhere), and without the branch that fallthrough would run
    /// the NEXT arm. `$out`'s `end` is exactly where the compare-cascade's
    /// outermost `end` sits, so both lowerings hand control to the same
    /// continuation.
    ///
    /// The dispatch is emitted here; every arm is pushed onto `work`.
    #[allow(clippy::too_many_arguments)]
    fn emit_switch_br_table(
        &mut self,
        vlocal: u32,
        plan: &BrTablePlan,
        x: usize,
        cases: Vec<trust_ir::SwitchCase>,
        default: BlockId,
        default_args: Vec<ValueId>,
        work: &mut Vec<Step>,
    ) -> Result<(), WasmLowerError> {
        let m = plan.arms;
        // $out, $default, $arm_{m-1} … $arm_0, $dispatch.
        self.open_anon_block(); // $out
        self.open_anon_block(); // $default
        for _ in 0..m {
            self.open_anon_block(); // $arm_{m-1} … $arm_0
        }
        self.open_anon_block(); // $dispatch

        // The index: `value - min`, in wrapping i32. `min == 0` is the common
        // case (a switch over 0.., an enum discriminant) and needs no subtract.
        emit_local_get(&mut self.code, vlocal);
        if plan.min != 0 {
            emit_i32_const(&mut self.code, plan.min);
            self.code.push(op::I32_SUB);
        }
        // Depths, measured from inside $dispatch: $arm_j is j+1 out, $default
        // is m+1 out. (Every label between here and there is one of the blocks
        // opened above, so the arithmetic is closed-form rather than a lookup.)
        self.code.push(op::BR_TABLE);
        write_uleb128(&mut self.code, plan.arm_of_index.len() as u64);
        for entry in &plan.arm_of_index {
            let depth = match entry {
                Some(arm) => *arm as u64 + 1,
                // A HOLE in the covered range is not a case: it takes the
                // default edge, exactly like a value outside the range.
                None => m as u64 + 1,
            };
            write_uleb128(&mut self.code, depth);
        }
        write_uleb128(&mut self.code, m as u64 + 1); // default label

        self.close_anon_block(); // end $dispatch

        // Pushed in reverse: after the last arm, `end $default`, the default
        // edge, and `end $out` — no `br $out` there, since $out's `end` is
        // the next byte and a fallthrough already lands on the continuation.
        let d = self.idx(default)?;
        work.push(Step::CloseAnon); // end $out
        work.push(Step::Branch(x, d));
        work.push(Step::SetParams(default, default_args));
        work.push(Step::CloseAnon); // end $default
        let mut arms = Vec::with_capacity(cases.len());
        for case in cases {
            let t = self.idx(case.target)?;
            arms.push((case, t));
        }
        for (j, (case, t)) in arms.into_iter().enumerate().rev() {
            // Leave the nest: $out is (m - j) labels out after arm j.
            work.push(Step::BrOut((m - j) as u64));
            work.push(Step::Branch(x, t));
            work.push(Step::SetParams(case.target, case.args));
            work.push(Step::CloseAnon); // end $arm_j — arm j's code follows
        }
        Ok(())
    }

    /// Open a `block` that no trust-ir block owns — a label the switch dispatch
    /// addresses by computed depth. It is counted in `open_labels` (so every
    /// `br` resolved through `context` still gets the right depth) but pushes
    /// no frame (nothing can branch to it by block id).
    fn open_anon_block(&mut self) {
        self.code.push(op::BLOCK);
        self.code.push(op::BLOCKTYPE_VOID);
        self.open_labels += 1;
    }

    fn close_anon_block(&mut self) {
        self.code.push(op::END);
        self.open_labels -= 1;
    }
}

/// One pending action of [`Lowering::emit_structured`].
enum Step {
    /// Open `x`'s scopes, then emit its subtree.
    Tree(usize),
    /// `x`'s body and terminator (its merge children's blocks are open).
    Node(usize),
    /// The edge `x -> t`.
    Branch(usize, usize),
    /// Copy an edge's arguments into the target's parameters.
    SetParams(BlockId, Vec<ValueId>),
    /// A narrow-cascade case: `value == k`, open its `if`, copy its edge's
    /// arguments.
    CaseTest {
        vlocal: u32,
        eq: u8,
        value_ty: Ty,
        value: Constant,
        target: BlockId,
        args: Vec<ValueId>,
    },
    /// A 128-bit-cascade case, likewise.
    WideCaseTest {
        src: wide::WideSource,
        value: Constant,
        target: BlockId,
        args: Vec<ValueId>,
    },
    Else,
    CloseScope,
    CloseIf,
    CloseAnon,
    /// `br depth`.
    BrOut(u64),
}

/// The module-level context one function's lowering reads: where the shadow
/// stack pointer lives, which wasm function index each callee has, which type
/// index each indirect-call signature has, where every piece of static data
/// lives, and whether the output is a relocatable object.
#[derive(Debug, Clone, Copy)]
pub struct WasmFunctionEnv<'a> {
    /// The shadow stack-pointer global, when the module provisioned one.
    sp_global: Option<u32>,
    call_targets: &'a CallTargets,
    /// The functions whose direct calls use their internal entry (an object
    /// at O1 and above only; empty everywhere else).
    internal_abi: &'a InternalTargets,
    sig_types: &'a SigTypes,
    global_addrs: &'a GlobalAddrs,
    const_pool: &'a ConstPool,
    helpers: &'a Helpers,
    foreign: &'a HashSet<FuncId>,
    captures: &'a ParamCaptures,
    stack_limit: Option<u32>,
    /// Undefined data symbols a function body takes the address of (a
    /// relocatable object only; a closed module has none).
    extern_data: &'a ExternData,
    object: bool,
    /// Whether the local emission pass (`opt.rs`) runs on this body. Only a
    /// module or object compile sets it, at O1 and above: its candidates are
    /// validated by `opt::validate_pending`, which a direct caller of
    /// [`lower_function`] never reaches.
    local_opt: bool,
    /// Whether a `GEP` index scaled by a one-byte element is added unscaled:
    /// set at O1 and above by a module or object compile, also when it lowers
    /// only to check that the lane accepts the module.
    unit_scale_elided: bool,
    /// Whether the 128-bit integers `pair::pair_carried` selects are carried
    /// in two `i64` locals instead of a home slot: set with
    /// `unit_scale_elided`.
    pair_carrier: bool,
}

impl WasmFunctionEnv<'_> {
    /// The env of a module with no calls, no indirect calls, no globals and no
    /// shadow stack — everything a single straight-line function needs.
    pub fn empty() -> WasmFunctionEnv<'static> {
        use std::sync::OnceLock;
        static CALL_TARGETS: OnceLock<CallTargets> = OnceLock::new();
        static INTERNAL_ABI: OnceLock<InternalTargets> = OnceLock::new();
        static SIG_TYPES: OnceLock<SigTypes> = OnceLock::new();
        static GLOBAL_ADDRS: OnceLock<GlobalAddrs> = OnceLock::new();
        static CONST_POOL: OnceLock<ConstPool> = OnceLock::new();
        static HELPERS: OnceLock<Helpers> = OnceLock::new();
        static FOREIGN: OnceLock<HashSet<FuncId>> = OnceLock::new();
        static CAPTURES: OnceLock<ParamCaptures> = OnceLock::new();
        static EXTERN_DATA: OnceLock<ExternData> = OnceLock::new();
        WasmFunctionEnv {
            sp_global: None,
            call_targets: CALL_TARGETS.get_or_init(HashMap::new),
            internal_abi: INTERNAL_ABI.get_or_init(HashMap::new),
            sig_types: SIG_TYPES.get_or_init(HashMap::new),
            global_addrs: GLOBAL_ADDRS.get_or_init(HashMap::new),
            const_pool: CONST_POOL.get_or_init(HashMap::new),
            helpers: HELPERS.get_or_init(Helpers::default),
            foreign: FOREIGN.get_or_init(HashSet::new),
            captures: CAPTURES.get_or_init(ParamCaptures::default),
            stack_limit: None,
            extern_data: EXTERN_DATA.get_or_init(HashMap::new),
            object: false,
            local_opt: false,
            unit_scale_elided: false,
            pair_carrier: false,
        }
    }
}

/// Lower a single trust-ir function and append it to `module`. Returns the new
/// wasm function index. Supports straight-line code, `if/else`, reducible
/// loops, `Switch` (compare-cascade or `br_table`), and irreducible CFGs (as
/// a dispatch loop); fail-closed on out-of-subset ops.
///
/// A public single-function entry admits its input as the module entries do:
/// trust-ir's codegen admission over `ir_module` with `func` in place
/// ([`trust_cg_lower::validate_function_codegen_prerequisites`]); `func`'s
/// codegen license is then decided under [`CodegenLicensePolicy::default`]
/// (claim-less bodies refused, DG-73).
pub fn lower_function(
    module: &mut WasmModule,
    func: &Function,
    ir_module: &Module,
    env: WasmFunctionEnv<'_>,
) -> Result<u32, WasmLowerError> {
    lower_function_with_license(
        module,
        func,
        ir_module,
        env,
        &CodegenLicensePolicy::default(),
    )
}

/// [`lower_function`] under the caller's codegen-license policy, decided for
/// `func` against `ir_module` with `func` in place (the evidence an
/// evidence-bound authority names lives on the module, roadmap WS7.5(b)).
pub fn lower_function_with_license(
    module: &mut WasmModule,
    func: &Function,
    ir_module: &Module,
    env: WasmFunctionEnv<'_>,
    license: &CodegenLicensePolicy,
) -> Result<u32, WasmLowerError> {
    refuse_declared_closure_layouts(ir_module)?;
    trust_cg_lower::validate_function_codegen_prerequisites(func, ir_module)
        .map_err(|error| WasmLowerError::CodegenAdmission(error.to_string()))?;
    lower_admitted_function(
        module,
        func,
        ir_module,
        env,
        FunctionLicense::Decide(license),
    )
}

/// How the codegen license of a function [`lower_admitted_function`] lowers
/// is decided.
#[derive(Clone, Copy)]
enum FunctionLicense<'l> {
    /// Decide it here, for this function against its module, under this
    /// policy (a single-function entry, or a helper body this lane builds).
    Decide(&'l CodegenLicensePolicy),
    /// The caller decided it for the WHOLE module it lowers, under the
    /// caller's policy, immediately before lowering any body
    /// ([`admit_for_codegen`]: once per module, and once more on the
    /// mid-end's output, by [`compile_module_parts`] and
    /// [`compile_object_parts`]). Re-deciding it per function would re-run
    /// trust-ir's license layer — a kernel re-check of every certificate —
    /// once per function; only the per-function metadata floor applies.
    DecidedForModule,
}

/// The license under which this lane lowers the runtime helper bodies it
/// builds itself (`fmod`, `divmod128`): lane templates, never producer
/// input, so they carry no `body_gate`. They compile under the NAMED, COUNTED
/// exception [`trust_cg_lower::UnlicensedPermitException::LaneRuntimeHelper`],
/// never under a silent default.
fn lane_helper_license() -> CodegenLicensePolicy {
    CodegenLicensePolicy::default().with_unlicensed_permit_exception(
        trust_cg_lower::UnlicensedPermitException::LaneRuntimeHelper,
    )
}

/// [`lower_function`] for a function whose license is decided as `license`
/// says. The per-function metadata floor applies either way.
fn lower_admitted_function(
    module: &mut WasmModule,
    func: &Function,
    ir_module: &Module,
    env: WasmFunctionEnv<'_>,
    license: FunctionLicense<'_>,
) -> Result<u32, WasmLowerError> {
    match license {
        FunctionLicense::Decide(license) => {
            trust_cg_lower::validate_function_codegen_metadata_with_license(
                func, ir_module, license,
            )
        }
        FunctionLicense::DecidedForModule => {
            trust_cg_lower::validate_function_codegen_metadata_floor(func)
        }
    }
    .map_err(|error| WasmLowerError::UnsupportedInst(error.to_string()))?;
    // The contract-surface floor of the lane this function is emitted into: an
    // object has a symbol table and honors what a closed module cannot
    // (function visibility, data imports). Only `compile_object_parts` builds
    // an object env (the env's fields are private to this module).
    if env.object {
        reject_unconsumed_object_surface(ir_module)?;
    } else {
        reject_unconsumed_v41_surface(ir_module)?;
    }
    reject_detached_function_formula_texts(func, ir_module)?;
    if is_declaration(func) {
        return Err(WasmLowerError::UnboundDeclaration(format!(
            "function `{}` has no body this wasm entry may emit",
            func.name
        )));
    }
    // The wasm32 pin is checked HERE too, not only in `compile_module`: this
    // function is part of the crate's public surface, and frame/GEP layout is
    // computed from `ir_module`'s target while addresses are emitted as i32 —
    // a target-free or 64-bit-pinned module would silently mis-lay-out every
    // frame (the hazard `require_wasm32_target_info` exists to refuse).
    require_wasm32_target_info(ir_module)?;
    // Same signature-level refusals, with the same named diagnostics, as the
    // native adapter: the wasm type of a variadic definition would silently
    // drop its anonymous arguments, and a byval parameter would be read as a
    // plain address.
    trust_cg_lower::reject_variadic_definition(func, ir_module)
        .and_then(|()| trust_cg_lower::reject_byval_params(func))
        .map_err(|error| WasmLowerError::UnsupportedAbi(error.to_string()))?;
    reject_unsigned_variadic_callees(func, ir_module)?;
    reject_unwired_eh_instructions(func)?;
    reject_non_integer_scalar_unops(func)?;
    reject_unmodeled_body_constructs(func)?;
    reject_unsupported_call_contract(func, ir_module)?;
    let mut low = Lowering::build(func, ir_module, env)?;
    low.assign_locals()?;
    low.check_strict_ssa()?;
    low.compute_frame()?;
    // Invariant N is established for the function's own parameters BEFORE any
    // of its code runs — including before the frame prologue, so a narrow
    // pointer-ish argument is canonical for every use.
    low.emit_param_canonicalization()?;
    low.emit_prologue()?;
    let entry = low.idx(func.entry)?;
    low.emit_structured(entry)?;
    // All paths return; mark the statically-dead tail so the module validates.
    low.code.push(op::UNREACHABLE);
    // Every constant-offset access through the frame stays inside it. Checked
    // on the lowering's own locals, before coalescing merges their roles.
    if let Some(frame) = low.frame {
        let relocated: HashSet<u32> = low.relocs.iter().map(|r| r.offset).collect();
        super::frame_bounds::check(
            &low.code,
            u32::try_from(low.sig.wasm.params.len())
                .map_err(|_| WasmLowerError::FrameLayoutOverflow(func.name.clone()))?,
            low.declared_locals.len(),
            super::frame_bounds::FrameShape {
                size: frame.size,
                base_local: frame.base_local,
            },
            &relocated,
        )
        .map_err(|m| WasmLowerError::FrameAccessOutOfBounds(format!("`{}`: {m}", func.name)))?;
    }

    // One local per SSA value and scratch temporary is what the lowering
    // binds. When the env enables it, this body is queued for the emission
    // pass (`opt.rs`), which rewrites and validates it once the module's
    // signatures are final; its rewrite replaces the BASELINE emitted below
    // only if the validator accepts it. Otherwise (O0, or a direct caller)
    // the baseline is all that is emitted.
    let params = low.sig.wasm.params.len();
    let pending = if env.local_opt {
        let pre = super::opt::Body {
            declared: low.declared_locals.clone(),
            code: low.code.clone(),
            relocs: low.relocs.clone(),
        };
        let exclusive: Vec<u32> = low.frame.iter().map(|f| f.base_local).collect();
        // The GEP additions' no-wrap premises, re-derived from the trust-ir
        // function by the checker (never taken from the claims).
        let check = {
            let slots: Vec<(ValueId, u32)> =
                low.locals.iter().map(|(v, (l, _))| (*v, *l)).collect();
            let params: Vec<ValKind> = low
                .sig
                .wasm
                .params
                .iter()
                .copied()
                .map(super::opt::kind_of)
                .collect();
            let locals: Vec<ValKind> = pre
                .declared
                .iter()
                .copied()
                .map(super::opt::kind_of)
                .collect();
            check_nowrap_premises(
                ir_module,
                func,
                &slots,
                &params,
                &TvBody {
                    locals: &locals,
                    code: &pre.code,
                    relocs: &[],
                },
                &low.nowrap_claims,
            )
        };
        // A prologue followed by the stack guard traps unless the new stack
        // pointer did not wrap below the old one, so on every path past it
        // `base <= 2^32 - 1 - size` (with a realigned base, when `2 size +
        // align <= 2^32`). The validator re-derives this from the guard.
        let frame_base = match (low.frame, low.stack_limit) {
            (Some(f), Some(_))
                if f.realign
                    .is_none_or(|a| 2 * u64::from(f.size) + u64::from(a) <= 1u64 << 32) =>
            {
                Some((f.base_local, u64::from(u32::MAX) - u64::from(f.size)))
            }
            _ => None,
        };
        Some((pre, exclusive, frame_base, check))
    } else {
        None
    };
    // The baseline reuses locals by liveness before the engine limit is
    // checked, exactly as the lane did before the emission pass.
    if low.declared_locals.len() >= super::locals::BASELINE_COALESCE_MIN_LOCALS
        && let Some(c) =
            super::locals::coalesce(params, &low.declared_locals, &low.code, &low.relocs)
    {
        low.declared_locals = c.declared;
        low.code = c.code;
        low.relocs = c.relocs;
    }
    let locals = run_length_encode(&low.declared_locals);
    super::locals::check_limits(
        &func.name,
        params,
        low.sig.wasm.results.len(),
        &locals,
        low.code.len(),
    )
    .map_err(WasmLowerError::ImplementationLimit)?;

    let sig = low.sig.clone();
    low.note_sig_features(&sig);
    let wasm_params = sig.wasm.params.clone();
    let results = sig.wasm.results.len();
    let ty_idx = module.add_type(sig.wasm);
    for feature in &low.features {
        module.require_feature(feature);
    }
    let body = FuncBody {
        locals,
        code: low.code,
        relocs: low.relocs,
    };
    let idx = module.add_function(ty_idx, body);
    if let Some((pre, exclusive, frame_base, check)) = pending {
        module.push_local_opt(super::opt::PendingLocalOpt {
            func: idx,
            name: func.name.clone(),
            params: wasm_params,
            results,
            pre,
            exclusive,
            frame_base,
            premises: check.premises,
            refused: check.refused.into_iter().map(|(_, why)| why).collect(),
        });
    }
    Ok(idx)
}

/// The module floor already checked a borrowed module-owned function. A
/// standalone caller may instead supply a newer clone: inventory THAT
/// function's formulas through IR's borrowed inventory, without cloning a
/// function or constructing a temporary module. This closes only the detached formula seam;
/// it does not extend other metadata admission policies or grant authority.
fn reject_detached_function_formula_texts(
    func: &Function,
    ir_module: &Module,
) -> Result<(), WasmLowerError> {
    // Dense-id modules take a constant-time identity check; sparse/reordered
    // modules fall back to identity membership without assuming id indexing.
    if ir_module
        .functions
        .get(func.id.index() as usize)
        .is_some_and(|owned| std::ptr::eq(owned, func))
        || ir_module
            .functions
            .iter()
            .any(|owned| std::ptr::eq(owned, func))
    {
        return Ok(());
    }
    if let Some(site) = func.first_formula_stating_two_texts() {
        let error = trust_ir_build::ValidationError::FormulaTextsDisagree {
            site: site.into_owned(),
        };
        let refusal = trust_cg_lower::AdapterError::TrustIrAdmissionRefused {
            error: error.to_string(),
        };
        return Err(WasmLowerError::ContractSurface(refusal.to_string()));
    }
    Ok(())
}

/// What a function needs from its module's memory: a shadow-stack FRAME (an
/// `Alloca`, a memory-carried value that owns storage, a parameter
/// materialized from scalar lanes, a scratch `sret` destination, a copy of a
/// by-address argument for a foreign callee) and/or linear MEMORY at all (any
/// load/store/bulk operation, any memory-carried value, a global's address).
///
/// Over-approximating is harmless — an unused stack-pointer global or memory
/// costs a few bytes — while under-approximating would emit an invalid module,
/// so every doubtful case counts.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
struct MemoryUse {
    frame: bool,
    memory: bool,
    table: bool,
}

fn function_memory_use(
    func: &Function,
    module: &Module,
    internal: &HashSet<FuncId>,
) -> Result<MemoryUse, WasmLowerError> {
    let is_mem =
        |ty: &Ty| -> Result<bool, WasmLowerError> { Ok(layout::carrier_of(module, ty)?.is_mem()) };
    // The signature a function is defined, or directly called, with: its
    // internal form when it has an internal entry (`Lowering::build`,
    // `Lowering::direct_call_sig`).
    let sig_of = |id: FuncId, ft: &trust_ir::FuncTy, cc: CallingConv| {
        if internal.contains(&id)
            && let Some(sig) = abi::lower_internal_sig(module, ft, cc)?
        {
            return Ok(sig);
        }
        abi::lower_sig(module, ft, cc)
    };
    // The function's OWN signature first: its convention (`CUnwind`, ...)
    // and carriers are refused by the signature lowering's named diagnostic
    // before any body construct is judged, as the native adapter refuses a
    // definition's convention before it translates an instruction. Lowering
    // the signature reads no instruction.
    let own_sig = module
        .func_type(func.ty)
        .map(|ft| sig_of(func.id, ft, func.calling_conv))
        .transpose()?;
    // The module entries run this pre-pass over every defined function before
    // any of them is lowered, and its result typing has no arm for an EH
    // instruction; scan the body first so an EH instruction is refused by
    // name here as well (the rule `reject_unwired_eh_instructions` states),
    // not as an anonymous "result-producing" instruction.
    reject_unwired_eh_instructions(func)?;
    let mut u = MemoryUse::default();
    if let Some(sig) = own_sig {
        let mut byaddr = Vec::new();
        for (lane, (v, _)) in sig.params.iter().zip(
            func.blocks
                .iter()
                .find(|b| b.id == func.entry)
                .map_or(&[][..], |b| b.params.as_slice()),
        ) {
            match lane {
                ParamLane::Singleton { .. } | ParamLane::Split128 { .. } => {
                    u.frame = true;
                    u.memory = true;
                }
                ParamLane::ByAddr { .. } => {
                    u.memory = true;
                    byaddr.push(*v);
                }
                _ => {}
            }
        }
        if sig.sret {
            u.memory = true;
        }
        // A by-address parameter whose address may escape gets a home
        // (`Lowering::assign_locals`).
        if !byaddr.is_empty()
            && let Some(entry) = func.blocks.iter().position(|b| b.id == func.entry)
        {
            let types = value_types(module, func)?;
            if !storage::escaping_sources(func, module, entry, &types, &byaddr)?.is_empty() {
                u.frame = true;
            }
        }
    }
    // A branch back to the entry block writes the entry's memory-carried
    // parameters, which then live in (and stage through) this frame.
    let entry_reentered = entry_reentered(func);
    let mut types: Option<HashMap<ValueId, Ty>> = None;
    for (bi, block) in func.blocks.iter().enumerate() {
        if entry_reentered || bi != 0 || func.blocks[0].id != func.entry {
            for (_, ty) in &block.params {
                if is_mem(ty)? {
                    u.frame = true;
                    u.memory = true;
                }
            }
        }
        for node in &block.body {
            match &node.inst {
                Inst::Alloca { .. } => {
                    u.frame = true;
                    u.memory = true;
                }
                Inst::Load { .. }
                | Inst::Store { .. }
                | Inst::AtomicLoad { .. }
                | Inst::AtomicStore { .. }
                | Inst::AtomicRMW { .. }
                | Inst::CmpXchg { .. }
                | Inst::MemCopy { .. }
                | Inst::MemSet { .. }
                | Inst::GlobalAddr { .. } => u.memory = true,
                Inst::Const { ty, value } if decode_body_global_addr_stub(ty, value).is_some() => {
                    u.memory = true;
                }
                Inst::Const {
                    value: Constant::SymbolAddr { symbol, addend },
                    ..
                } => {
                    u.memory = true;
                    if matches!(
                        layout::resolve_symbol(module, symbol, *addend),
                        Ok(layout::ImageRef::Func(_))
                    ) {
                        u.table = true;
                    }
                }
                Inst::Const {
                    value: Constant::FnDef(_),
                    ..
                } => u.table = true,
                Inst::CallIndirect { .. } => u.table = true,
                _ => {}
            }
            let (callee_ft, callee_cc, direct) = match &node.inst {
                Inst::Call { callee, .. } => {
                    let f = module.function_by_id(*callee);
                    (
                        f.and_then(|f| module.func_type(f.ty)),
                        f.map(|f| f.calling_conv),
                        Some(*callee),
                    )
                }
                Inst::CallIndirect {
                    sig, calling_conv, ..
                } => (module.func_type(*sig), Some(*calling_conv), None),
                _ => (None, None, None),
            };
            if let (Some(ft), Some(cc)) = (callee_ft, callee_cc) {
                let sig = match direct {
                    Some(callee) => sig_of(callee, ft, cc)?,
                    None => abi::lower_sig(module, ft, cc)?,
                };
                if sig.sret
                    || sig
                        .params
                        .iter()
                        .any(|l| !matches!(l, ParamLane::Scalar(_) | ParamLane::Void))
                {
                    u.frame = true;
                    u.memory = true;
                }
            }
            if node.results.is_empty() {
                continue;
            }
            for ty in result_tys(&node.inst, module)? {
                if is_mem(&ty)? {
                    u.memory = true;
                    if owns_storage(&node.inst) {
                        u.frame = true;
                    }
                }
            }
            // A read-through extract owns its memory-carried result's home
            // ([`extract_reads_through`]); its declared result type need not
            // name that lane, so ask the lane's typing of the function.
            if !u.frame
                && matches!(
                    node.inst,
                    Inst::ExtractField { .. } | Inst::ExtractElement { .. }
                )
            {
                if types.is_none() {
                    types = Some(value_types(module, func)?);
                }
                if let Some(types) = &types
                    && extract_reads_through(&node.inst, types)
                {
                    for r in &node.results {
                        if let Some(ty) = types.get(r)
                            && is_mem(ty)?
                        {
                            u.frame = true;
                            u.memory = true;
                        }
                    }
                }
            }
        }
    }
    Ok(u)
}

/// Does any function lower `FRem` at this float width?
fn uses_frem(module: &Module, ty: &Ty) -> bool {
    module.functions.iter().any(|f| {
        f.blocks
            .iter()
            .flat_map(|b| &b.body)
            .any(|n| matches!(&n.inst, Inst::BinOp { op: BinOp::FRem, ty: t, .. } if t == ty))
    })
}

/// Does any function divide or take the remainder of a 128-bit integer (the
/// operations [`super::helpers::divmod128_module`] computes)?
fn uses_wide_divmod(module: &Module) -> bool {
    module
        .functions
        .iter()
        .filter(|f| !is_declaration(f))
        .any(|f| {
            f.blocks.iter().flat_map(|b| &b.body).any(|n| {
                matches!(
                    &n.inst,
                    Inst::BinOp {
                        op: BinOp::UDiv | BinOp::URem | BinOp::SDiv | BinOp::SRem,
                        ty,
                        ..
                    } if wide::is_wide(ty)
                )
            })
        })
}

/// Refuse every trust-ir v41 contract-surface construct this lane cannot
/// honor, BEFORE any body is walked. The target-neutral clauses are the native
/// adapter's own (`trust_cg_lower::reject_unconsumed_v41_target_neutral_surface`
/// — decided in one place so this lane can never accept what the native lane
/// refuses); the two clauses below are specific to wasm.
///
/// What this lane CONSUMES, and how: `Linkage::{WeakOdr, LinkOnceOdr}` are
/// definitions like every other defined function here (a single wasm module
/// has no linker to pick between definitions, exactly as `Weak`/`LinkOnce`
/// already were); an `AvailableExternally` FUNCTION is a declaration
/// ([`is_declaration`]) and binds through the func-import policy or is
/// refused as unbound; `Global.visibility` on a definition is honored
/// vacuously — this lane never emits a data symbol at all (a global is an
/// absolute address, exported by nothing), so `Hidden`/`Protected` promise
/// nothing this lane could break; `Global.retained` is honored vacuously —
/// every global gets its address and data segment, nothing is ever stripped.
fn refuse_declared_closure_layouts(module: &Module) -> Result<(), WasmLowerError> {
    if !module.closure_layouts.is_empty() {
        return Err(WasmLowerError::ContractSurface(
            "declared closure layout(s) (trust-ir v58): wasm does not consume physical capture offsets".into(),
        ));
    }
    Ok(())
}

fn reject_unconsumed_v41_surface(module: &Module) -> Result<(), WasmLowerError> {
    refuse_declared_closure_layouts(module)?;
    trust_cg_lower::reject_unconsumed_v41_target_neutral_surface(module)
        .map_err(|error| WasmLowerError::ContractSurface(error.to_string()))?;
    reject_panic_sites(module)?;
    // A v43 opaque runtime handle (trust-ir v43) is refused OUTRIGHT here,
    // where the native lane admits transport to a pinned runtime entry point.
    // The shared floor admits that transport, so this lane has to say no
    // itself: a handle's only origin is a pinned NATIVE C declaration, and
    // this lane has no channel to one — a wasm import bound to that symbol is
    // whatever the embedder supplies, which is exactly the forgery the handle
    // type exists to exclude. `valtype_of` would refuse the type anyway; this
    // clause refuses BEFORE any body is walked and names the runtime.
    trust_cg_lower::refuse_handle_surface(module, "wasm")
        .map_err(|error| WasmLowerError::ContractSurface(error.to_string()))?;
    reject_unconsumed_target_abi_surface(module)?;
    // v42 declared tuple layouts: the shared floor admits a row that equals
    // the NATIVE byte path's declaration-order layout (WS7.7). This lane lays
    // tuples out by its own rules, so that agreement says nothing about it;
    // it keeps refusing every table outside the pointer-transport profile.
    trust_cg_lower::refuse_declared_tuple_layouts_outside_pointer_transport(module)
        .map_err(|error| WasmLowerError::ContractSurface(error.to_string()))?;
    // No wasm feature (simd128, bulk-memory, threads, ...) is modeled by this
    // lane, so a body may not assume ANY target feature: the vocabulary is
    // empty, the same fail-closed rule as `known_target_features(Riscv64)`.
    if let Some((func, feature)) = module
        .functions
        .iter()
        .find_map(|f| f.attrs.target_features.first().map(|feature| (f, feature)))
    {
        return Err(WasmLowerError::ContractSurface(format!(
            "function `{}` assumes target feature {feature:?} (trust-ir v41); the wasm lane \
             models no target feature and refuses rather than compile a body that may rely on \
             one",
            func.name
        )));
    }
    // A wasm module has no object sections: every global is laid out at an
    // absolute linear-memory address by `layout_static_data`, so an explicit
    // section (well-formed names pass the shared floor for the native
    // AArch64 emitters) can only be refused here, never ignored.
    if let Some(global) = module.globals.iter().find(|g| g.section.is_some()) {
        return Err(WasmLowerError::ContractSurface(format!(
            "[TCG-SECTION-TARGET] global `{}` requests explicit section `{}` (trust-ir v41): \
             the wasm lane lays every global out in linear memory and has no object \
             sections, so it refuses rather than ignore the request",
            global.name,
            global.section.as_deref().unwrap_or_default()
        )));
    }
    // A data import has no spelling here: every global is laid out at an
    // absolute linear-memory address by `layout_static_data`, so an
    // `available_externally` global could only be emitted as a DEFINITION —
    // the one thing that linkage says it must never be.
    if let Some(global) = module
        .globals
        .iter()
        .find(|g| g.linkage == trust_ir::Linkage::AvailableExternally)
    {
        return Err(WasmLowerError::ContractSurface(format!(
            "global `{}` has linkage `available_externally` (trust-ir v41): it is a cross-object \
             import, and a closed wasm module has no data-import channel (a global is an absolute \
             linear-memory address), so it refuses rather than emit the initializer as a \
             definition",
            global.name
        )));
    }
    Ok(())
}

/// trust-ir v54 (amendment P) panic sites, refused BY NAME by both surface
/// floors right after the shared floor, before any import, signature or body
/// is lowered: a sited `Inst::Assert` and every `Inst::AssertInvoke`. A
/// site's failure calls its panic entry with the kind's operands and the
/// location record and never returns, and an `AssertInvoke`'s failure may
/// also enter an in-frame landing pad. This lane lowers neither that call nor
/// that edge, and a trap or a dropped check would compile a different
/// program.
///
/// The shared floor refused every site by name until the native lanes gained
/// sited delivery (8318a495e). It now refuses only a site whose kind is
/// `Unspecified` (no Rust panic identity), so this lane refuses the rest
/// itself, as it does the handle surface the shared floor admits (decision
/// LD-W7-9). Without this clause a site of a stated kind reached later,
/// unrelated refusals first, such as its panic entry as an unbound
/// declaration. The body-walk arms (`reject_unwired_eh_instructions`, the
/// `Inst::Assert` arm of the instruction lowering) stay as the backstops of
/// the per-function entry, which runs no module floor over the function it
/// lowers. Every field is named, so a later pin's field fails to compile here
/// until it is classified.
fn reject_panic_sites(module: &Module) -> Result<(), WasmLowerError> {
    for func in &module.functions {
        for block in &func.blocks {
            for node in &block.body {
                let (construct, kind, entry) = match &node.inst {
                    Inst::Assert {
                        cond: _,
                        kind,
                        site: Some(site),
                    } => ("Inst::Assert { site: Some(_) }", kind, site.entry),
                    Inst::AssertInvoke {
                        cond: _,
                        kind,
                        site,
                        normal_dest: _,
                        normal_args: _,
                        unwind_dest: _,
                    } => ("Inst::AssertInvoke", kind, site.entry),
                    _ => continue,
                };
                return Err(WasmLowerError::UnsupportedInst(format!(
                    "[TCG-ASSERT-PANIC] {construct} in `{}` block {:?}: a check of kind `{}` \
                     whose failure calls panic entry {entry:?} (trust-ir v54 panic site); the \
                     wasm lane lowers no panic-entry call or unwind edge, so it is refused \
                     rather than lowered to a trap",
                    func.name,
                    block.id,
                    kind.keyword(),
                )));
            }
        }
    }
    Ok(())
}

/// The target-ABI clauses both surface floors share, decided over the module
/// before any signature is lowered:
///
/// * `TargetInfo.struct_passing`, by the native lanes' own clause
///   ([`trust_cg_lower::reject_unconsumed_struct_passing`]): this lane passes
///   aggregates by the WebAssembly Basic C ABI, so `AlwaysMemory` is refused
///   and an `Unclassified` module is refused once an aggregate crosses a call
///   edge by value — the lane never picks a classification the producer did
///   not perform;
/// * an unrecorded narrow argument extension on a C-convention declaration:
///   the Basic C ABI, like DarwinPCS, makes the CALLER extend an `i8`/`i16`
///   argument to `i32` (clang marks the parameter `signext`/`zeroext`, and an
///   LLVM-compiled callee relies on it). A recorded `ParamAttrs` slot whose
///   `ext` is `None` says the extension is UNRECORDED (trust-ir v45, "never
///   'no extension needed'"), so it is refused rather than picked, the native
///   DarwinPCS rule (must-refuse row `narrow_arg_ext_unrecorded_darwin`). A
///   declaration with no slot keeps the extension its IR type's signedness
///   states, as on the native lanes; a recorded extension is refused by the
///   shared floor until an emitter honours it.
fn reject_unconsumed_target_abi_surface(module: &Module) -> Result<(), WasmLowerError> {
    if let Some(target_info) = &module.target_info {
        trust_cg_lower::reject_unconsumed_struct_passing(module, target_info.struct_passing)
            .map_err(|error| WasmLowerError::UnsupportedAbi(error.to_string()))?;
    }
    for func in &module.functions {
        if !func.blocks.is_empty() || func.calling_conv != CallingConv::C {
            continue;
        }
        let Some(signature) = module.func_type(func.ty) else {
            continue;
        };
        for (index, ty) in signature.params.iter().enumerate() {
            if !matches!(ty, Ty::I8 | Ty::U8 | Ty::I16 | Ty::U16) {
                continue;
            }
            if func
                .attrs
                .params
                .get(index)
                .is_some_and(|attrs| attrs.ext == trust_ir::ArgExt::None)
            {
                return Err(WasmLowerError::UnsupportedAbi(format!(
                    "function `{}` (a C-convention declaration on wasm32) has narrow parameter \
                     {index} of type {ty:?} with a recorded `ParamAttrs` slot and no recorded \
                     argument extension (`ext = None`, trust-ir v45): the WebAssembly Basic C \
                     ABI makes the caller extend it and trust-ir records that fact as \
                     UNRECORDED, so this backend refuses rather than pick an extension",
                    func.name
                )));
            }
        }
    }
    Ok(())
}

/// The object-lane counterpart of [`reject_unconsumed_v41_surface`]. An object
/// HAS a symbol table, so it honors what a closed module cannot: hidden and
/// protected visibility on functions (rustc's default for a non-exported
/// cross-CGU function) and on data imports, and data imports themselves
/// (undefined data symbols). What it still refuses: weak undefined references,
/// explicit code or data sections (a wasm object has no named sections to put
/// them in), target features, and the handle surface.
fn reject_unconsumed_object_surface(module: &Module) -> Result<(), WasmLowerError> {
    refuse_declared_closure_layouts(module)?;
    let policy = trust_cg_lower::ObjectSymbolPolicy {
        weak_references: trust_cg_lower::WeakUndefinedReferencePolicy::Refuse,
        function_symbol_facts: trust_cg_lower::FunctionSymbolFactPolicy::AdmitElfSymbolFacts,
        data_import_visibility:
            trust_cg_lower::DataImportVisibilityPolicy::AdmitElfUndefinedVisibility,
    };
    trust_cg_lower::reject_unconsumed_v41_target_neutral_surface_with_weak_references(
        module, policy,
    )
    .map_err(|error| WasmLowerError::ContractSurface(error.to_string()))?;
    reject_panic_sites(module)?;
    trust_cg_lower::refuse_handle_surface(module, "wasm")
        .map_err(|error| WasmLowerError::ContractSurface(error.to_string()))?;
    reject_unconsumed_target_abi_surface(module)?;
    // v42 declared tuple layouts (WS7.7): the shared floor's agreement is with
    // the NATIVE byte path's layout, which says nothing about this lane, so
    // the object lane refuses every table outside the pointer-transport
    // profile exactly as the closed-module floor does.
    trust_cg_lower::refuse_declared_tuple_layouts_outside_pointer_transport(module)
        .map_err(|error| WasmLowerError::ContractSurface(error.to_string()))?;
    if let Some((func, feature)) = module
        .functions
        .iter()
        .find_map(|f| f.attrs.target_features.first().map(|feature| (f, feature)))
    {
        return Err(WasmLowerError::ContractSurface(format!(
            "function `{}` assumes target feature {feature:?} (trust-ir v41); the wasm lane \
             models no target feature and refuses rather than compile a body that may rely on \
             one",
            func.name
        )));
    }
    if let Some(func) = module.functions.iter().find(|f| f.section.is_some()) {
        return Err(WasmLowerError::ContractSurface(format!(
            "[TCG-SECTION-TARGET] function `{}` requests explicit section `{}`: a wasm object \
             has no named code sections, so the lane refuses rather than ignore the request",
            func.name,
            func.section.as_deref().unwrap_or_default()
        )));
    }
    if let Some(global) = module.globals.iter().find(|g| g.section.is_some()) {
        return Err(WasmLowerError::ContractSurface(format!(
            "[TCG-SECTION-TARGET] global `{}` requests explicit section `{}`: a wasm object \
             lays data out in its own segments, so the lane refuses rather than ignore the \
             request",
            global.name,
            global.section.as_deref().unwrap_or_default()
        )));
    }
    Ok(())
}

/// A memory-carried constant a function needs pooled into static data.
struct PoolRequest {
    func: FuncId,
    value: ValueId,
    ty: Ty,
    constant: Constant,
}

/// Every memory-carried `Const` in the module's DEFINED functions. With
/// `pairs` (the lowering's `pair_carrier`, O1 and above), a 128-bit constant
/// the lowering carries as a pair (`pair::pair_carried`, decided from the
/// same typing the lowering uses) is two `i64.const`s and needs no image.
fn pool_requests(module: &Module, pairs: bool) -> Result<Vec<PoolRequest>, WasmLowerError> {
    let mut out = Vec::new();
    for func in module.functions.iter().filter(|f| !is_declaration(f)) {
        let mut paired: Option<HashSet<ValueId>> = None;
        for node in func.blocks.iter().flat_map(|b| &b.body) {
            let Inst::Const { ty, value } = &node.inst else {
                continue;
            };
            if matches!(value, Constant::FnDef(_)) {
                continue;
            }
            let Some(&result) = node.results.first() else {
                continue;
            };
            if pairs && wide::is_wide(ty) {
                // A function the lane cannot type is refused when it is
                // lowered; its constants are pooled meanwhile.
                let paired = paired.get_or_insert_with(|| {
                    value_types(module, func)
                        .and_then(|types| pair::pair_carried(func, module, &types))
                        .unwrap_or_default()
                });
                if paired.contains(&result) {
                    continue;
                }
            }
            if layout::carrier_of(module, ty)?.is_mem() {
                out.push(PoolRequest {
                    func: func.id,
                    value: result,
                    ty: ty.clone(),
                    constant: value.clone(),
                });
            }
        }
    }
    Ok(out)
}

/// Resolve a closed module's image references in place: a function becomes
/// its table index ([`super::encode::closed_table_index`], never the null 0),
/// a global its absolute address. A module has no linker, so a symbol it does
/// not define cannot be resolved and is refused.
fn patch_closed_image(
    image: &mut layout::ConstImage,
    call_targets: &CallTargets,
    global_addrs: &GlobalAddrs,
    needs_table: &mut bool,
) -> Result<(), WasmLowerError> {
    for (at, r) in std::mem::take(&mut image.refs) {
        let value: u32 = match r {
            layout::ImageRef::Func(fid) => {
                *needs_table = true;
                super::encode::closed_table_index(*call_targets.get(&fid).ok_or_else(|| {
                    WasmLowerError::UnsupportedConstantData(format!(
                        "function pointer to unknown {fid:?} in static data"
                    ))
                })?)
            }
            layout::ImageRef::Global(gid, addend) => {
                let base = global_addrs.get(&gid).ok_or_else(|| {
                    WasmLowerError::UnsupportedConstantData(format!(
                        "address of unknown {gid:?} in static data"
                    ))
                })?;
                (base.addr as i64).wrapping_add(addend) as u32
            }
            layout::ImageRef::Symbol(name, _) => {
                return Err(WasmLowerError::UnsupportedConstantData(format!(
                    "static data takes the address of `{name}`, which this closed module does \
                     not define; only a relocatable object can refer to an external symbol"
                )));
            }
        };
        let at = at as usize;
        image.bytes[at..at + 4].copy_from_slice(&value.to_le_bytes());
    }
    Ok(())
}

/// Where [`place_static_data`] put a closed module's static data.
struct StaticPlacement {
    /// The address of every module global, in module order.
    globals: Vec<u32>,
    /// The byte size of every module global, in module order.
    global_sizes: Vec<u64>,
    /// The address and unpatched image of every pooled constant, in request
    /// order.
    pool: Vec<(u32, layout::ConstImage)>,
    /// One past the last byte of the area (an absolute address).
    end: u64,
}

/// Pass 1 of [`layout_static_data`]: bottom-up from `base`, every global and
/// then every pooled constant at its own natural alignment. The one placement
/// rule the layout and [`sized_closed_policy`] both use.
fn place_static_data(
    module: &Module,
    pool: &[PoolRequest],
    base: u32,
) -> Result<StaticPlacement, WasmLowerError> {
    let mut cursor = u64::from(base);
    // The whole item must lie in the wasm32 address space, image or not (a
    // BSS global past it would wrap every address into it). This is decided
    // here, from the layout alone, before any global's image is derived, so
    // an oversized initializer is refused without building its bytes.
    let place = |cursor: &mut u64, size: u64, align: u64, what: &str| {
        *cursor = cursor.div_ceil(align) * align;
        let addr = u32::try_from(*cursor).map_err(|_| {
            WasmLowerError::StaticDataOverflow(format!(
                "{what} lands at {cursor}, past the wasm32 address space"
            ))
        })?;
        *cursor = cursor
            .checked_add(size)
            .filter(|end| *end <= u64::from(u32::MAX) + 1)
            .ok_or_else(|| {
                WasmLowerError::StaticDataOverflow(format!(
                    "{what} of {size} byte(s) at {cursor} runs past the wasm32 address space"
                ))
            })?;
        Ok::<u32, WasmLowerError>(addr)
    };
    let mut globals = Vec::with_capacity(module.globals.len());
    let mut global_sizes = Vec::with_capacity(module.globals.len());
    for global in &module.globals {
        // The same layout authority the object lane and every value access use.
        let (size, natural) = layout::size_align(module, &global.ty).map_err(|e| {
            WasmLowerError::UnsupportedType(format!("layout of global `{}`: {e}", global.name))
        })?;
        let size = u64::from(size);
        let align_bytes = u64::from(natural)
            .max(global.align.map_or(1, u64::from))
            .max(1);
        let addr = place(
            &mut cursor,
            size,
            align_bytes,
            &format!("global `{}`", global.name),
        )?;
        globals.push(addr);
        global_sizes.push(size);
    }
    let mut pooled = Vec::with_capacity(pool.len());
    for req in pool {
        // Placed from its layout first, so a constant past the address space
        // is refused before its image is built.
        let (size, align) = layout::size_align(module, &req.ty)?;
        let addr = place(
            &mut cursor,
            u64::from(size),
            u64::from(align),
            "a pooled constant",
        )?;
        let image = layout::const_image(module, &req.ty, &req.constant)?;
        debug_assert_eq!(image.bytes.len() as u64, u64::from(size));
        pooled.push((addr, image));
    }
    if u32::try_from(cursor).is_err() {
        return Err(WasmLowerError::StaticDataOverflow(format!(
            "module `{}`: static data ends at {cursor}, past the wasm32 address space",
            module.name
        )));
    }
    Ok(StaticPlacement {
        globals,
        global_sizes,
        pool: pooled,
        end: cursor,
    })
}

/// The shadow stack a closed module sized by [`sized_closed_policy`] keeps
/// above its static data: what the default one-page module leaves when it
/// has no static data at all (the page less its null guard).
pub const WASM_CLOSED_MIN_STACK_BYTES: u32 = WASM_PAGE_BYTES - WASM_STATIC_DATA_BASE;

/// The closed policy ([`WasmModulePolicy::closed`]) with enough owned pages
/// for `module`'s static data AND a stack.
///
/// The module owns the fewest pages (at least the default one) that hold the
/// whole static-data area (zero-initialized globals included) plus
/// [`WASM_CLOSED_MIN_STACK_BYTES`] of shadow stack above it, so every module
/// sized this way has at least that much stack whatever its data size. A
/// module with no static data keeps the one default page, and its bytes are
/// exactly [`compile_module`]'s; any static data grows the memory by the
/// data's size rounded up to pages. The memory is still fixed-size and private
/// to the module; only its declared minimum changes.
pub fn sized_closed_policy(module: &Module) -> Result<WasmModulePolicy, WasmLowerError> {
    // A policy sized for a module carrying a non-propagating call boundary
    // would be a pre-layout fact about a module no wasm entry compiles; refuse
    // every stored boundary by name first, as `lower_function`'s scan does.
    for func in &module.functions {
        for block in &func.blocks {
            if let Some(refusal) = block
                .body
                .iter()
                .find_map(|node| call_unwind_boundary_refusal(node, func, block.id))
            {
                return Err(refusal);
            }
        }
    }
    let mut policy = WasmModulePolicy::closed();
    let WasmMemoryPolicy::Owned { pages, .. } = &mut policy.memory else {
        return Ok(policy);
    };
    // Every memory-carried constant's image is counted, as O0 pools them:
    // at O1 and above the pair-carried ones are not laid out, which only
    // leaves more of the sized memory to the stack.
    let end = place_static_data(
        module,
        &pool_requests(module, false)?,
        WASM_STATIC_DATA_BASE,
    )?
    .end;
    let page = u64::from(WASM_PAGE_BYTES);
    let needed = (end + u64::from(WASM_CLOSED_MIN_STACK_BYTES))
        .div_ceil(page)
        .max(u64::from(*pages));
    // wasm32 addresses 65536 pages; the stack pointer's initial value is the
    // top of the memory as an `i32` bit pattern, so the full 4 GiB is refused.
    if needed >= 65536 {
        return Err(WasmLowerError::StaticDataOverflow(format!(
            "module `{}`: static data ends at {end}; with a {WASM_CLOSED_MIN_STACK_BYTES}-byte \
             stack it needs {needed} pages, past the wasm32 address space",
            module.name
        )));
    }
    *pages = needed as u32;
    Ok(policy)
}

/// Lay a closed module's static data out in linear memory — every global,
/// then every pooled memory-carried constant — and declare its data segments.
/// Returns where each lives and the total EXTENT of the static-data area in
/// bytes (the region a host must have reserved).
///
/// Placement is bottom-up from the policy's base, each item at its own
/// natural alignment. The shadow stack grows DOWN from the top of the same
/// memory, so a module whose static data would run past the memory it declared
/// is refused rather than emitted with a data segment the engine would trap on,
/// and in an owned memory the extent returned here is the stack's floor
/// (`Lowering::emit_stack_guard`).
fn layout_static_data(
    module: &Module,
    policy: &WasmModulePolicy,
    wasm: &mut WasmModule,
    pool: &[PoolRequest],
    call_targets: &CallTargets,
) -> Result<(GlobalAddrs, ConstPool, u64), WasmLowerError> {
    let mut addrs = GlobalAddrs::new();
    let mut pool_addrs = ConstPool::new();
    if module.globals.is_empty() && pool.is_empty() {
        return Ok((addrs, pool_addrs, 0));
    }
    let base = match (&policy.static_data, &policy.memory) {
        (WasmStaticDataPolicy::OwnedBottom, WasmMemoryPolicy::Owned { .. }) => {
            WASM_STATIC_DATA_BASE
        }
        (WasmStaticDataPolicy::HostReservedAt { base }, _) => {
            wasm.grant_imported_memory_data();
            *base
        }
        (WasmStaticDataPolicy::OwnedBottom, other) => {
            return Err(WasmLowerError::HostMemoryNotGranted(format!(
                "module `{}` has {} global(s) and {} pooled constant(s) whose bytes must be \
                 written into linear memory, but the memory policy is {other:?} — an ACTIVE data \
                 segment there writes at an absolute address in a memory this module does not \
                 own. Configure WasmStaticDataPolicy::HostReservedAt {{ base }} with the region \
                 the host reserved.",
                module.name,
                module.globals.len(),
                pool.len(),
            )));
        }
    };
    wasm.require_memory()?;

    // Pass 1: addresses.
    let placed = place_static_data(module, pool, base)?;
    let cursor = placed.end;
    // The WHOLE area must lie inside a memory this module owns — zero-filled
    // (initializer-less) globals included. Their bytes get no data segment, so
    // the per-segment range check in the encoder never sees them; checked
    // here, on the layout, a trailing BSS global past the owned pages is
    // refused instead of emitted at an address every access traps on (and
    // above the stack's floor, where every framed call would trap).
    if let WasmMemoryPolicy::Owned { pages, .. } = &policy.memory {
        let limit = u64::from(*pages) * u64::from(WASM_PAGE_BYTES);
        if cursor > limit {
            return Err(WasmLowerError::StaticDataOverflow(format!(
                "module `{}`: static data (zero-initialized globals included) ends at \
                 {cursor}, past the {pages}-page ({limit}-byte) memory this module owns",
                module.name
            )));
        }
    }
    for (index, &addr) in placed.globals.iter().enumerate() {
        addrs.insert(
            trust_ir::value::GlobalId::new(index as u32),
            DataAddr { addr, item: None },
        );
    }
    let global_sizes = placed.global_sizes;
    let mut pool_images = Vec::with_capacity(pool.len());
    for (req, (addr, image)) in pool.iter().zip(placed.pool) {
        pool_addrs.insert((req.func, req.value), DataAddr { addr, item: None });
        pool_images.push((addr, image));
    }

    // Pass 2: images, with every address now known.
    let mut needs_table = false;
    for (index, global) in module.globals.iter().enumerate() {
        // No initializer: BSS. Linear memory already reads as zero.
        let Some(init) = &global.initializer else {
            continue;
        };
        // A zero splat (trust-ir v50) is BSS too, whatever its length: its
        // image is never built.
        if layout::is_zero_splat(module, &global.ty, init)? {
            continue;
        }
        let mut image = layout::const_image(module, &global.ty, init).map_err(|e| match e {
            WasmLowerError::UnsupportedConstantData(m) => WasmLowerError::UnsupportedConstantData(
                format!("global `{}` of type {:?}: {m}", global.name, global.ty),
            ),
            other => other,
        })?;
        patch_closed_image(&mut image, call_targets, &addrs, &mut needs_table)?;
        debug_assert_eq!(image.bytes.len() as u64, global_sizes[index]);
        let addr = addrs[&trust_ir::value::GlobalId::new(index as u32)].addr;
        wasm.add_data_segment(addr, image.bytes)?;
    }
    for (addr, mut image) in pool_images {
        patch_closed_image(&mut image, call_targets, &addrs, &mut needs_table)?;
        wasm.add_data_segment(addr, image.bytes)?;
    }
    if needs_table {
        wasm.enable_func_table();
    }
    Ok((addrs, pool_addrs, cursor - u64::from(base)))
}

/// Append the `memory.size` / `memory.grow` shims and export them.
///
/// They are ordinary defined functions appended AFTER every trust-ir function,
/// so no trust-ir function's index moves and every call target computed above
/// stays valid.
fn append_memory_growth_shims(
    module: &Module,
    policy: &WasmModulePolicy,
    wasm: &mut WasmModule,
) -> Result<(), WasmLowerError> {
    match (&policy.memory_growth, &policy.memory) {
        (WasmMemoryGrowthPolicy::Fixed, _) => return Ok(()),
        (WasmMemoryGrowthPolicy::HostGrantedShims, _)
        | (WasmMemoryGrowthPolicy::OwnedShims, WasmMemoryPolicy::Owned { .. }) => {}
        (WasmMemoryGrowthPolicy::OwnedShims, other) => {
            return Err(WasmLowerError::HostMemoryNotGranted(format!(
                "module `{}` asks to export memory.grow shims under memory policy {other:?} — \
                 growing a memory this module does not own moves the HOST's buffer and \
                 invalidates every view it holds. Configure \
                 WasmMemoryGrowthPolicy::HostGrantedShims once the host has agreed.",
                module.name,
            )));
        }
    }
    wasm.require_memory()?;

    let size_ty = wasm.add_type(FuncType {
        params: vec![],
        results: vec![ValType::I32],
    });
    let mut size_code = Vec::new();
    emit_memory_size(&mut size_code);
    let size_idx = wasm.add_function(
        size_ty,
        FuncBody {
            locals: vec![],
            code: size_code,
            relocs: vec![],
        },
    );
    wasm.export_func(MEMORY_SIZE_EXPORT, size_idx);

    let grow_ty = wasm.add_type(FuncType {
        params: vec![ValType::I32],
        results: vec![ValType::I32],
    });
    let mut grow_code = Vec::new();
    emit_local_get(&mut grow_code, 0);
    emit_memory_grow(&mut grow_code);
    let grow_idx = wasm.add_function(
        grow_ty,
        FuncBody {
            locals: vec![],
            code: grow_code,
            relocs: vec![],
        },
    );
    wasm.export_func(MEMORY_GROW_EXPORT, grow_idx);
    Ok(())
}

/// The level the entries without one compile at: the CLI's default `-O`.
const DEFAULT_OPT_LEVEL: OptLevel = OptLevel::O2;

/// Whether `level` runs the local emission pass (`opt.rs`). O0 emits the
/// baseline body of every function, byte-identical to the lane before the
/// pass existed.
fn runs_local_emission(level: OptLevel) -> bool {
    level != OptLevel::O0
}

/// Lower every function in a trust-ir module to wasm and export each under its
/// own name. If any function needs linear memory or a shadow-stack frame, the
/// module gains one linear memory and a shared shadow stack-pointer global.
///
/// Accepted-input guards (fail-closed, named diagnostics):
/// * the module must be pinned to the wasm32 target shape
///   ([`super::target::wasm32_target_info`]) — target-free and
///   non-wasm32-pinned modules are refused;
/// * functions and call edges use `CallingConv::C` or `CallingConv::Rust`;
/// * every value's type has a wasm32 carrier ([`super::layout`]).
///
/// Every closed-module entry without a level compiles at O2 and runs the
/// validated trust-ir mid-end and local emission pass;
/// [`compile_module_with_evidence_and_policy_optimized`] takes the level (O0
/// runs neither and emits each function's baseline body).
pub fn compile_module(module: &Module) -> Result<Vec<u8>, WasmLowerError> {
    compile_module_with_policy(module, &WasmModulePolicy::closed())
}

/// [`compile_module`] under an explicit host contract — the entry an *island*
/// uses to live beside a host module.
///
/// With [`WasmModulePolicy::closed`] the emitted bytes are identical to
/// [`compile_module`]'s. Any other policy changes what the module *binds*:
///
/// * [`WasmMemoryPolicy::Imported`] — the module defines no memory and shares
///   the host's, so its shadow stack must be host-negotiated
///   ([`WasmStackPolicy::HostBase`]); asking for a frame at the private
///   `pages * 64KiB` top of someone else's memory is refused
///   ([`WasmLowerError::StackBaseUnavailable`]).
/// * [`WasmMemoryPolicy::Absent`] — any memory access is refused
///   ([`WasmLowerError::MemoryUnavailable`]).
/// * [`WasmFuncImportPolicy::FromModule`] — body-less trust-ir functions
///   become wasm function imports, which occupy the LOW function index space
///   and shift every defined function's index.
pub fn compile_module_with_policy(
    module: &Module,
    policy: &WasmModulePolicy,
) -> Result<Vec<u8>, WasmLowerError> {
    compile_module_with_policy_and_license(module, policy, &CodegenLicensePolicy::default())
}

/// [`compile_module`] under the caller's codegen-license policy: the closed
/// module, admitted exactly as [`compile_module_with_policy_and_license`]
/// admits it.
pub fn compile_module_with_license(
    module: &Module,
    license: &CodegenLicensePolicy,
) -> Result<Vec<u8>, WasmLowerError> {
    compile_module_with_policy_and_license(module, &WasmModulePolicy::closed(), license)
}

/// [`compile_module_with_policy`] under the caller's codegen-license policy
/// (`license`), the policy a native entry takes through
/// `Compiler::with_codegen_license`: which gate authorities are recognized,
/// and whether a claim-less body may be compiled. Every other entry of this
/// lane applies [`CodegenLicensePolicy::default`]. The license is one half of
/// the admission; the other, trust-ir's codegen admission
/// ([`trust_cg_lower::validate_codegen_prerequisites`]), is not a policy and
/// runs under every license.
pub fn compile_module_with_policy_and_license(
    module: &Module,
    policy: &WasmModulePolicy,
    license: &CodegenLicensePolicy,
) -> Result<Vec<u8>, WasmLowerError> {
    Ok(compile_module_parts(
        module,
        policy,
        ClosedPolicyFit::AsGiven,
        license,
        WasmOptOptions::at(DEFAULT_OPT_LEVEL),
    )?
    .bytes)
}

/// The codegen admission every module entry of this lane runs before any
/// contract surface or body is looked at, in the native adapter's order:
/// trust-ir's own codegen admission
/// ([`trust_cg_lower::validate_codegen_prerequisites`]), which no policy
/// widens, then the caller's codegen LICENSE (`Ungated` refused under every
/// policy; `Gated` needs an authority `license` recognizes; `None` is
/// `license.unlicensed`'s decision).
fn admit_for_codegen(
    module: &Module,
    license: &CodegenLicensePolicy,
) -> Result<(), WasmLowerError> {
    refuse_declared_closure_layouts(module)?;
    trust_cg_lower::validate_codegen_prerequisites(module)
        .map_err(|error| WasmLowerError::CodegenAdmission(error.to_string()))?;
    license
        .enforce_module(module)
        .map_err(|error| WasmLowerError::CodegenLicense(error.to_string()))
}

/// A U10 prologue stack-limit tag asks for a check this lane cannot emit
/// (the wasm follow-up is an imported limit global). Both the closed-module
/// and the object lane refuse it rather than compile the function without
/// its check.
fn reject_stack_limit_requests(module: &Module) -> Result<(), WasmLowerError> {
    if trust_cg_lower::stack_limit::module_requests_stack_limits(module) {
        return Err(WasmLowerError::UnsupportedInst(
            "[TCG-STACK-LIMIT-REQUEST] the wasm32 lane has no prologue stack-limit lowering \
             (v1 is AArch64 only)"
                .to_string(),
        ));
    }
    Ok(())
}

/// The signature-level refusals every lane shares, run over every DEFINED
/// function before anything else looks at a signature, so a variadic
/// definition or a `byval` parameter is refused with the native lanes' own
/// diagnostic (`[TCG-VARIADIC-DEFINITION]`, `[TCG-BYVAL-ABI]`), and a direct
/// call through an unsigned variadic declaration with
/// `[TCG-UNSIGNED-VARIADIC]` ([`reject_unsigned_variadic_callees`]).
fn reject_shared_signature_surface(module: &Module) -> Result<(), WasmLowerError> {
    for func in module.functions.iter().filter(|f| !is_declaration(f)) {
        trust_cg_lower::reject_variadic_definition(func, module)
            .and_then(|()| trust_cg_lower::reject_byval_params(func))
            .map_err(|error| WasmLowerError::UnsupportedAbi(error.to_string()))?;
        reject_unsigned_variadic_callees(func, module)?;
    }
    Ok(())
}

/// Refuse a direct call or invoke in `func` whose callee declaration is
/// variadic with no trustworthy fixed-argument count, with the native
/// adapter's diagnostic (`trust_cg_lower::reject_unsigned_variadic_callee`).
/// [`abi::lower_sig`] refuses every variadic signature on this lane anyway;
/// this runs first so the producer's unsigned `(...)` is named the same way
/// here as on the native lanes.
fn reject_unsigned_variadic_callees(
    func: &Function,
    module: &Module,
) -> Result<(), WasmLowerError> {
    for node in func.blocks.iter().flat_map(|block| &block.body) {
        let (Inst::Call { callee, .. } | Inst::Invoke { callee, .. }) = &node.inst else {
            continue;
        };
        let Some(callee_fn) = module.function_by_id(*callee) else {
            continue;
        };
        let Some(ft) = module.func_type(callee_fn.ty) else {
            continue;
        };
        trust_cg_lower::reject_unsigned_variadic_callee(callee_fn, ft)
            .map_err(|error| WasmLowerError::UnsupportedAbi(error.to_string()))?;
    }
    Ok(())
}

/// Signature types for every `call_indirect` in the module.
fn indirect_sig_types(module: &Module, wasm: &mut WasmModule) -> Result<SigTypes, WasmLowerError> {
    let mut sig_types: SigTypes = HashMap::new();
    for func in module.functions.iter().filter(|f| !is_declaration(f)) {
        for node in func.blocks.iter().flat_map(|b| &b.body) {
            if let Inst::CallIndirect {
                sig, calling_conv, ..
            } = &node.inst
                && !sig_types.contains_key(&(*sig, *calling_conv))
            {
                let ft = module.func_type(*sig).ok_or_else(|| {
                    WasmLowerError::UnsupportedInst(format!("unknown signature {sig:?}"))
                })?;
                let lowered = abi::lower_sig(module, ft, *calling_conv)?;
                let idx = wasm.add_type(lowered.wasm);
                sig_types.insert((*sig, *calling_conv), idx);
            }
        }
    }
    Ok(sig_types)
}

/// The wasm type of a function's lowered signature.
fn function_wasm_type(module: &Module, func: &Function) -> Result<FuncType, WasmLowerError> {
    let ft = module.func_type(func.ty).ok_or_else(|| {
        WasmLowerError::UnsupportedInst(format!(
            "declaration `{}` has unknown signature {:?}",
            func.name, func.ty
        ))
    })?;
    abi::lower_sig(module, ft, func.calling_conv)
        .map(|sig| sig.wasm)
        .map_err(|error| match error {
            WasmLowerError::UnsupportedCallingConv(m) => {
                WasmLowerError::UnsupportedCallingConv(format!("declaration `{}`: {m}", func.name))
            }
            other => other,
        })
}

/// The defined functions a closed module exports, each under its trust-ir
/// name, beside the memory's export when the policy surfaces one and the
/// growth shims when it grants them.
///
/// Every externally visible definition is exported, and two such exports of
/// one name are refused (`[TCG-WASM-EXPORT]`): an export section with a name
/// twice is invalid, so no engine would accept the module. A module-local
/// (internal/private) definition is exported too, unless another definition
/// or export uses its name: nothing outside the module may name a module-local
/// function, so such an ambiguous one is left unexported rather than refused
/// (calls inside the module name functions by id, never by name). The
/// trust-ir validator refuses two functions of one name whatever their
/// linkage, so only unvalidated input, or a module-local function named like
/// the memory export or a shim, meets that rule.
fn closed_function_exports(
    module: &Module,
    policy: &WasmModulePolicy,
) -> Result<HashSet<FuncId>, WasmLowerError> {
    let defined = || module.functions.iter().filter(|f| !is_declaration(f));
    let mut names: Vec<(&str, &str)> = defined()
        .filter(|f| !trust_cg_lower::is_module_local_function_definition(f))
        .map(|f| (f.name.as_str(), "function"))
        .collect();
    if let WasmMemoryPolicy::Owned {
        export: Some(name), ..
    } = &policy.memory
    {
        names.push((name.as_str(), "the memory export"));
    }
    if policy.memory_growth != WasmMemoryGrowthPolicy::Fixed {
        names.push((MEMORY_SIZE_EXPORT, "the memory.size shim"));
        names.push((MEMORY_GROW_EXPORT, "the memory.grow shim"));
    }
    let mut seen: HashMap<&str, &str> = HashMap::new();
    for (name, what) in names {
        if let Some(prev) = seen.insert(name, what) {
            return Err(WasmLowerError::ContractSurface(format!(
                "[TCG-WASM-EXPORT] module `{}` would export `{name}` twice ({prev} and {what}); \
                 a wasm module's export names are unique",
                module.name
            )));
        }
    }
    let mut local_names: HashMap<&str, usize> = HashMap::new();
    for f in defined().filter(|f| trust_cg_lower::is_module_local_function_definition(f)) {
        *local_names.entry(f.name.as_str()).or_default() += 1;
    }
    Ok(defined()
        .filter(|f| {
            !trust_cg_lower::is_module_local_function_definition(f)
                || (!seen.contains_key(f.name.as_str()) && local_names[f.name.as_str()] == 1)
        })
        .map(|f| f.id)
        .collect())
}

/// What one compile of the module or object lane produced.
struct CompiledParts {
    bytes: Vec<u8>,
    /// The host contract the bytes bind (see [`WasmModule::host_contract`]).
    host_contract: Vec<String>,
    local_emission: WasmLocalOptSummary,
    mid_end: IrmidReport,
    /// The CFG structural invariant's verdict on `bytes` when it was already
    /// computed: always for the mid-end's output, which is emitted only when
    /// that verdict is not `Refuted` ([`screen_mid_end_output`]); `None` for
    /// the lowered input, which a caller that reports the invariant checks
    /// itself.
    cfg_verdict: Option<trust_cg_verify::wasm_cfg_proofs::CfgVerdict>,
    /// When the mid-end's output is emitted: the input's own lowering (its
    /// baseline bodies, from the check-only lowering), so a caller that
    /// reports the invariant also checks the input, whose refutation fails
    /// the compile as it would without the mid-end.
    input_check: Option<Vec<u8>>,
}

impl CompiledParts {
    /// The structural verdict to file for this compile, computing what the
    /// compile did not: the input's lowering first when the mid-end's output
    /// replaced it (its `Refuted` is the compile's), then the emitted bytes.
    fn take_cfg_verdict(&mut self) -> trust_cg_verify::wasm_cfg_proofs::CfgVerdict {
        use trust_cg_verify::wasm_cfg_proofs::{CfgVerdict, check_module_structure};
        if let Some(input) = self.input_check.take() {
            let verdict = check_module_structure(&input);
            if matches!(verdict, CfgVerdict::Refuted(_)) {
                return verdict;
            }
        }
        self.cfg_verdict
            .take()
            .unwrap_or_else(|| check_module_structure(&self.bytes))
    }
}

/// How a closed-module compile may fit its memory policy to the module it
/// emits.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ClosedPolicyFit {
    /// The caller's policy is used as given: the mid-end adds no static data
    /// (constant-table promotion is withheld), and an optimized module whose
    /// static data still outgrows the input's falls back to the input.
    AsGiven,
    /// The policy is [`sized_closed_policy`] of the input, and the optimized
    /// module's owned pages are grown so that it keeps at least the input's
    /// shadow stack above its own static data.
    SizedForEmitted,
}

/// Where the shadow stack of a closed module that owns its memory stops: the
/// end of its static data (from [`WASM_STATIC_DATA_BASE`]) rounded to the
/// stack guard's 8 bytes, as the lowering's stack limit bounds it. A module
/// without static data is measured from the base, as
/// [`WASM_CLOSED_MIN_STACK_BYTES`] is.
fn closed_stack_floor(static_data_len: u64) -> u64 {
    (u64::from(WASM_STATIC_DATA_BASE) + static_data_len).div_ceil(8) * 8
}

/// The bytes of static data `module` lays out under `policy` (zero when it
/// has none), as [`layout_static_data`] measures them; `pairs` as for
/// [`pool_requests`].
fn static_data_len(
    module: &Module,
    policy: &WasmModulePolicy,
    pairs: bool,
) -> Result<u64, WasmLowerError> {
    let pool = pool_requests(module, pairs)?;
    if module.globals.is_empty() && pool.is_empty() {
        return Ok(0);
    }
    let base = match &policy.static_data {
        WasmStaticDataPolicy::OwnedBottom => WASM_STATIC_DATA_BASE,
        WasmStaticDataPolicy::HostReservedAt { base } => *base,
    };
    Ok(place_static_data(module, &pool, base)?.end - u64::from(base))
}

/// The policy the mid-end's output is lowered under, or why it does not fit
/// the memory the input was given (the input is then emitted).
///
/// Under [`ClosedPolicyFit::AsGiven`] the output's static data may not
/// outgrow the input's: in memory the module owns it would come out of the
/// shadow stack above it, and in a host-reserved region it would write past
/// the reservation. Under [`ClosedPolicyFit::SizedForEmitted`] the owned
/// pages grow by what the output's stack floor rose, so its stack is at least
/// the input's.
fn emitted_policy(
    policy: &WasmModulePolicy,
    fit: ClosedPolicyFit,
    input_static: u64,
    candidate: &Module,
    pairs: bool,
) -> Result<WasmModulePolicy, String> {
    let output_static = static_data_len(candidate, policy, pairs).map_err(|error| {
        format!("the lane cannot lay out the optimized module's static data: {error}")
    })?;
    if output_static <= input_static {
        return Ok(policy.clone());
    }
    let sized_pages = match (&policy.memory, &policy.stack, &policy.static_data) {
        (
            WasmMemoryPolicy::Owned { pages, .. },
            WasmStackPolicy::OwnedTop,
            WasmStaticDataPolicy::OwnedBottom,
        ) if fit == ClosedPolicyFit::SizedForEmitted => *pages,
        _ => {
            return Err(format!(
                "the optimized module has {output_static} bytes of static data, more than the \
                 input's {input_static}, and the caller fixed the memory layout: the extra data \
                 would shorten the input's stack or overrun the host's reserved region"
            ));
        }
    };
    let rise = closed_stack_floor(output_static) - closed_stack_floor(input_static);
    let pages = u64::from(sized_pages) + rise.div_ceil(u64::from(WASM_PAGE_BYTES));
    // As in `sized_closed_policy`: the stack pointer starts at the top of the
    // memory as an `i32` bit pattern, so the full 4 GiB is out of reach.
    if pages >= 65536 {
        return Err(format!(
            "the optimized module's {output_static} bytes of static data and the input's stack \
             need {pages} pages, past the wasm32 address space"
        ));
    }
    let mut grown = policy.clone();
    if let WasmMemoryPolicy::Owned { pages: owned, .. } = &mut grown.memory {
        *owned = pages as u32;
    }
    Ok(grown)
}

/// Whether the lowered mid-end output `bytes` is emitted: the CFG structural
/// invariant must not be refuted on them. A refutation falls back to the
/// input (recorded in `mid`) rather than failing the compile, which then
/// fails only if the input's own bytes are refuted, as without the mid-end.
/// Returns the verdict when the output is kept.
fn screen_mid_end_output(
    bytes: &[u8],
    mid: &mut IrmidReport,
) -> Option<trust_cg_verify::wasm_cfg_proofs::CfgVerdict> {
    use trust_cg_verify::wasm_cfg_proofs::{CfgVerdict, check_module_structure};
    match check_module_structure(bytes) {
        CfgVerdict::Refuted(violation) => {
            mid.fall_back(format!(
                "the CFG structural invariant was refuted on the optimized module: {violation}"
            ));
            None
        }
        verdict => {
            mid.applied = true;
            Some(verdict)
        }
    }
}

/// The shared compile body. The input is admitted first; at O1 and above,
/// when the mid-end changed something, the input is lowered too (its refusal
/// is the compile's), and the mid-end's output is emitted when it passes the
/// same admission (`super::mid`), the lane lowers it, and the CFG structural
/// invariant is not refuted on its bytes ([`screen_mid_end_output`]);
/// otherwise the input is emitted.
///
/// `fit` says whether the memory layout may follow the module emitted
/// ([`ClosedPolicyFit`]): the mid-end's output never gets less shadow stack
/// than the input, and never writes static data past a host's reserved
/// region ([`emitted_policy`]).
fn compile_module_parts(
    module: &Module,
    policy: &WasmModulePolicy,
    fit: ClosedPolicyFit,
    license: &CodegenLicensePolicy,
    options: WasmOptOptions,
) -> Result<CompiledParts, WasmLowerError> {
    use super::mid::StaticDataRoom;
    require_wasm32_target_info(module)?;
    admit_closed_module(module, license)?;
    let room = match fit {
        ClosedPolicyFit::SizedForEmitted => StaticDataRoom::Grows,
        ClosedPolicyFit::AsGiven => StaticDataRoom::Fixed(
            "the caller fixed the module's memory policy: a promoted table's static data would \
             shorten its stack or overrun the host's reserved region",
        ),
    };
    let (candidate, mut mid) =
        super::mid::optimize(module, options, room, &WasmInlineHints::default(), |m| {
            admit_closed_module(m, license)
        });
    if let Some(candidate) = candidate {
        // The input must lower first: a construct the lane refuses stays
        // refused even when a rewrite removed it (dead code, an unreachable
        // block). The check lowers at the same level without the local
        // emission pass, which never refuses; its bytes are kept only for the
        // structural check of `CompiledParts::take_cfg_verdict`.
        let input = lower_module_parts(module, policy, options.level, true)?;
        let pairs = runs_local_emission(options.level);
        match emitted_policy(policy, fit, input.static_data_len, &candidate, pairs) {
            Err(why) => mid.fall_back(why),
            Ok(emitted) => match lower_module_parts(&candidate, &emitted, options.level, false) {
                Ok(lowered) => {
                    if let Some(verdict) = screen_mid_end_output(&lowered.bytes, &mut mid) {
                        return Ok(CompiledParts {
                            bytes: lowered.bytes,
                            host_contract: lowered.host_contract,
                            local_emission: lowered.local_emission,
                            mid_end: mid,
                            cfg_verdict: Some(verdict),
                            input_check: Some(input.bytes),
                        });
                    }
                }
                Err(error) => {
                    mid.fall_back(format!("the lane refused the optimized module: {error}"));
                }
            },
        }
    }
    let lowered = lower_module_parts(module, policy, options.level, false)?;
    Ok(CompiledParts {
        bytes: lowered.bytes,
        host_contract: lowered.host_contract,
        local_emission: lowered.local_emission,
        mid_end: mid,
        cfg_verdict: None,
        input_check: None,
    })
}

/// What [`lower_module_parts`] produced.
struct LoweredModule {
    bytes: Vec<u8>,
    host_contract: Vec<String>,
    local_emission: WasmLocalOptSummary,
    /// Bytes of static data laid out (zero when the module has none).
    static_data_len: u64,
}

/// Decided before any body is walked: the codegen admission under the
/// caller's license ([`admit_for_codegen`]), then every contract-surface
/// construct this lane can neither emit nor silently drop.
fn admit_closed_module(
    module: &Module,
    license: &CodegenLicensePolicy,
) -> Result<(), WasmLowerError> {
    admit_for_codegen(module, license)?;
    reject_unconsumed_v41_surface(module)?;
    reject_shared_signature_surface(module)?;
    reject_stack_limit_requests(module)?;
    admit_ingestion(module, license)
}

/// WS7.3 INGESTION ADMISSION, run by both lanes' admissions
/// ([`admit_closed_module`], [`admit_object`]) after the lane's own named
/// floors (so their diagnostics stand), and so also on every mid-end candidate
/// those admissions re-check before it is lowered: trust-ir's composed codegen
/// admission under the caller's license policy, every finding a refusal. This
/// lane registers no dialect, so only trust-ir's in-tree namespaces pass the
/// lowerability layer (and the lowering still refuses any op it has no arm
/// for).
fn admit_ingestion(module: &Module, license: &CodegenLicensePolicy) -> Result<(), WasmLowerError> {
    trust_cg_lower::admit_module(module, license, &[])
        .map(|_| ())
        .map_err(|error| match error {
            trust_cg_lower::AdapterError::InvalidTrustIrModule(refusal) => {
                WasmLowerError::InvalidTrustIr(refusal)
            }
            other => WasmLowerError::CodegenAdmission(other.to_string()),
        })
}

/// Lower an admitted module to a closed module or island.
///
/// `module` passed [`admit_closed_module`] under the caller's license
/// immediately before this call, which decided its codegen license for every
/// function at once ([`FunctionLicense::DecidedForModule`]).
///
/// `check_only` lowers without queuing the local emission pass (the caller
/// discards the bytes and keeps only whether the lane accepts the module);
/// everything else, including what the lane refuses, is as at `level`.
fn lower_module_parts(
    module: &Module,
    policy: &WasmModulePolicy,
    level: OptLevel,
    check_only: bool,
) -> Result<LoweredModule, WasmLowerError> {
    let unit_scale_elided = runs_local_emission(level);
    let local_opt = unit_scale_elided && !check_only;
    let exported = closed_function_exports(module, policy)?;
    let mut wasm = WasmModule::with_memory_policy(policy.memory.clone());

    // ---- Imports FIRST. Imported functions occupy function indices 0..N, so
    // every index below (call targets, function-pointer constants, table
    // elements, exports) is derived from `func_import_count`, never from a
    // definition ordinal. Declaring an import after a definition is refused by
    // the encoder, so this ordering is enforced, not merely intended.
    let mut call_targets: CallTargets = HashMap::new();
    let mut foreign: HashSet<FuncId> = HashSet::new();
    for func in module.functions.iter().filter(|f| is_declaration(f)) {
        let WasmFuncImportPolicy::FromModule(host) = &policy.func_imports else {
            return Err(WasmLowerError::UnboundDeclaration(format!(
                "module `{}` declares `{}` with no body this lane emits (bodyless, or \
                 `available_externally`), and the func-import policy is Forbidden — bind it \
                 with WasmFuncImportPolicy::FromModule(<host module>)",
                module.name, func.name,
            )));
        };
        let type_idx = wasm.add_type(function_wasm_type(module, func)?);
        let widx = wasm.add_func_import(host, &func.name, type_idx)?;
        call_targets.insert(func.id, widx);
        foreign.insert(func.id);
    }

    // ---- What the defined functions need from memory.
    let mut uses = Vec::new();
    for func in module.functions.iter().filter(|f| !is_declaration(f)) {
        uses.push((func, function_memory_use(func, module, &HashSet::new())?));
    }
    let pool = pool_requests(module, unit_scale_elided)?;

    // ---- Linear memory, per the policy. Anything that touches memory —
    // alloca, load, store, a global's address, a memory-carried value — needs
    // one; a policy that provides none refuses, naming the function.
    let memory_user = uses
        .iter()
        .find(|(_, u)| u.memory || u.frame)
        .map(|(f, _)| *f);
    if let Some(f) = memory_user
        && policy.memory == WasmMemoryPolicy::Absent
    {
        return Err(WasmLowerError::MemoryUnavailable(format!(
            "module `{}`: function `{}` accesses linear memory, but the memory policy is Absent",
            module.name, f.name,
        )));
    }
    if !module.globals.is_empty() && policy.memory == WasmMemoryPolicy::Absent {
        return Err(WasmLowerError::MemoryUnavailable(format!(
            "module `{}` has {} global(s) whose static data lives in linear memory, but the \
             memory policy is Absent",
            module.name,
            module.globals.len(),
        )));
    }
    // An OWNED memory is an implementation detail: emit it only when the code
    // needs it, or when the policy explicitly surfaces it to a host. An
    // IMPORTED memory is part of the host contract, so it is always declared.
    let surface_owned_memory = matches!(
        &policy.memory,
        WasmMemoryPolicy::Owned {
            export: Some(_),
            ..
        }
    );
    if memory_user.is_some()
        || surface_owned_memory
        || matches!(policy.memory, WasmMemoryPolicy::Imported { .. })
    {
        wasm.require_memory()?;
    }

    // ---- The shadow stack pointer: a DEFINED mutable i32 global, seeded
    // either from the top of the module's own memory or from the host's
    // imported immutable base global. Its index is import-shifted, so the
    // prologue/epilogue `global.get`/`global.set` immediates are too.
    let frame_user = uses.iter().find(|(_, u)| u.frame).map(|(f, _)| *f);
    let sp_global = match frame_user {
        None => None,
        Some(f) => match &policy.stack {
            WasmStackPolicy::OwnedTop => {
                let WasmMemoryPolicy::Owned { pages, .. } = &policy.memory else {
                    return Err(WasmLowerError::StackBaseUnavailable(format!(
                        "module `{}`: function `{}` needs a shadow-stack frame under memory \
                         policy {:?}, but WasmStackPolicy::OwnedTop pins the stack at the top of \
                         a memory this module does not own — that address is the HOST's data. \
                         Configure WasmStackPolicy::HostBase {{ module, name }} so the host \
                         publishes the island's region top.",
                        module.name, f.name, policy.memory,
                    )));
                };
                let top = pages.checked_mul(WASM_PAGE_BYTES).ok_or_else(|| {
                    WasmLowerError::StackBaseUnavailable(format!(
                        "module `{}`: {pages} owned pages overflow the wasm32 address space",
                        module.name,
                    ))
                })?;
                // `top as i32` is bit-preserving: wasm32 addresses are
                // unsigned i32 bit patterns.
                Some(wasm.add_global(ValType::I32, true, GlobalInit::I32(top as i32))?)
            }
            WasmStackPolicy::HostBase { module: m, name: n } => {
                let base = wasm.add_global_import(m, n, ValType::I32, false)?;
                Some(wasm.add_global(ValType::I32, true, GlobalInit::ImportedGlobal(base))?)
            }
        },
    };

    // ---- Direct-call targets for DEFINED functions: `N + ordinal`, where `N`
    // is the number of imported functions. This is the index `add_function`
    // will return; the lowering loop re-checks that below.
    let import_base = wasm.func_import_count();
    let defined: Vec<&Function> = module
        .functions
        .iter()
        .filter(|f| !is_declaration(f))
        .collect();
    for (ordinal, func) in defined.iter().enumerate() {
        call_targets.insert(func.id, import_base + ordinal as u32);
    }

    // ---- Runtime helpers a closed module carries itself, appended right after
    // the trust-ir functions so no trust-ir index moves.
    let mut helpers = Helpers::default();
    let mut helper_modules = Vec::new();
    let mut next_index = import_base + defined.len() as u32;
    for (ty, single) in [(Ty::F64, false), (Ty::F32, true)] {
        if uses_frem(module, &ty) {
            helper_modules.push(super::helpers::fmod_module(single)?);
            if single {
                helpers.fmodf = Some(next_index);
            } else {
                helpers.fmod = Some(next_index);
            }
            next_index += 1;
        }
    }
    if uses_wide_divmod(module) {
        // The helper stores its result through a pointer; the module already
        // has memory for the 128-bit operands' home slots.
        wasm.require_memory()?;
        let name = super::helpers::divmod128_helper_name_at(level);
        helper_modules.push(super::helpers::divmod128_module(&name, level)?);
        helpers.divmod128 = Some(next_index);
    }

    // Function table + indirect-call signature types, if the module needs them.
    // The table covers the whole function index space (imports included) after
    // the null slot, so a function pointer is `closed_table_index(funcidx)`;
    // the encoder derives its size.
    if uses.iter().any(|(_, u)| u.table) {
        wasm.enable_func_table();
    }
    let sig_types = indirect_sig_types(module, &mut wasm)?;

    // ---- Static data: every module global and pooled constant gets an
    // absolute address and a data segment. Laid out BEFORE any function is
    // lowered, because `GlobalAddr` materializes that address as an
    // `i32.const` inside the code.
    let (global_addrs, const_pool, static_data_len) =
        layout_static_data(module, policy, &mut wasm, &pool, &call_targets)?;
    let no_extern_data = ExternData::new();

    // In memory this module owns, static data sits at the bottom and the
    // shadow stack grows down from the top toward it. When the module has
    // static data, every frame and dynamic `Alloca` checks that it stays at or
    // above the end of that data, so an overflowing stack traps instead of
    // overwriting it. With no static data there is no check: a stack pointer
    // driven below zero wraps to a huge address, and the engine's bounds
    // check traps on the first access through it.
    let stack_limit = match (&policy.memory, &policy.stack) {
        (WasmMemoryPolicy::Owned { pages, .. }, WasmStackPolicy::OwnedTop)
            if sp_global.is_some() && static_data_len > 0 =>
        {
            let base = match &policy.static_data {
                WasmStaticDataPolicy::OwnedBottom => u64::from(WASM_STATIC_DATA_BASE),
                WasmStaticDataPolicy::HostReservedAt { base } => u64::from(*base),
            };
            let end = (base + static_data_len).div_ceil(8) * 8;
            // The stack's floor may not lie above its initial pointer (the
            // top of the owned memory): every frame would then trap in its
            // guard. `layout_static_data` already bounds the area by the
            // owned pages; this keeps the floor honest on its own terms.
            let top = u64::from(*pages) * u64::from(WASM_PAGE_BYTES);
            if end > top {
                return Err(WasmLowerError::StaticDataOverflow(format!(
                    "module `{}`: static data ends at {end}, above the {top}-byte top of the \
                     memory its shadow stack grows down from",
                    module.name
                )));
            }
            Some(u32::try_from(end).map_err(|_| {
                WasmLowerError::StaticDataOverflow(format!(
                    "module `{}`: static data ends at {end}, past the wasm32 address space",
                    module.name
                ))
            })?)
        }
        _ => None,
    };
    let captures = captures::param_captures(module, &foreign);
    // A closed module is never linked: every function keeps the C form.
    let no_internal_abi = InternalTargets::new();
    let env = WasmFunctionEnv {
        sp_global,
        call_targets: &call_targets,
        internal_abi: &no_internal_abi,
        sig_types: &sig_types,
        global_addrs: &global_addrs,
        const_pool: &const_pool,
        helpers: &helpers,
        foreign: &foreign,
        captures: &captures,
        stack_limit,
        extern_data: &no_extern_data,
        object: false,
        local_opt,
        unit_scale_elided,
        pair_carrier: unit_scale_elided,
    };
    for func in &defined {
        let idx = lower_admitted_function(
            &mut wasm,
            func,
            module,
            env,
            FunctionLicense::DecidedForModule,
        )?;
        // The call targets above were computed as `import_base + ordinal`. If
        // the emitted index ever disagreed, every `call` to this function
        // would land somewhere else — refuse rather than emit.
        let expected = call_targets.get(&func.id).copied();
        if expected != Some(idx) {
            return Err(WasmLowerError::FunctionIndexDrift(format!(
                "`{}` was emitted as wasm function {idx}, but its call targets were computed as \
                 {expected:?} (import base {import_base})",
                func.name,
            )));
        }
        if exported.contains(&func.id) {
            wasm.export_func(&func.name, idx);
        }
    }
    for (expected_helper, helper) in (import_base + defined.len() as u32..).zip(&helper_modules) {
        let func = &helper.functions[0];
        let helper_env = WasmFunctionEnv {
            local_opt,
            unit_scale_elided,
            ..WasmFunctionEnv::empty()
        };
        let idx = lower_admitted_function(
            &mut wasm,
            func,
            helper,
            helper_env,
            FunctionLicense::Decide(&lane_helper_license()),
        )?;
        // Every `call` to a helper was emitted with the index provisioned
        // above, in the order of `helper_modules`.
        if idx != expected_helper {
            return Err(WasmLowerError::FunctionIndexDrift(format!(
                "helper `{}` was emitted as wasm function {idx}, but its calls target \
                 {expected_helper}",
                func.name,
            )));
        }
    }

    // The growth shims come LAST so they occupy function indices above every
    // trust-ir function — no call target, function pointer, or export moves.
    append_memory_growth_shims(module, policy, &mut wasm)?;
    // Every signature is final: validate the emission pass's candidates.
    let mut local_opt_summary = super::opt::validate_pending(&mut wasm);
    local_opt_summary.enabled = local_opt;

    // The host contract is every import PLUS the grants the policy took over a
    // memory this module does not own. A grant is not an import — nothing in
    // the binary names it — but it is exactly as load-bearing: the host must
    // have reserved that region, and must expect its buffer to move. Reporting
    // the imports alone would understate the claimed surface (WP-0), so the
    // granted terms join the same list.
    let mut contract = wasm.host_contract();
    if let WasmMemoryPolicy::Imported { module: m, name: n } = &policy.memory {
        // A reserved region the module never writes into is not a grant it
        // took, so an empty static-data area adds no term.
        if let WasmStaticDataPolicy::HostReservedAt { base } = &policy.static_data
            && static_data_len > 0
        {
            let end = u64::from(*base) + static_data_len;
            contract.push(format!("data {m}.{n}[{base}..{end})"));
        }
        if policy.memory_growth != WasmMemoryGrowthPolicy::Fixed {
            contract.push(format!("grow {m}.{n}"));
        }
    }
    Ok(LoweredModule {
        bytes: wasm.finish(),
        host_contract: contract,
        local_emission: local_opt_summary,
        static_data_len,
    })
}

/// Whether an object's DEFINITION with this linkage may be replaced at link
/// time. It is emitted as a WEAK symbol ([`symbol_flags`]), and `wasm-ld`
/// binds every relocated reference to it — this object's own direct calls
/// included — to another object's strong definition, or to any one of
/// several weak copies. That body may be foreign code (C, LLVM-compiled
/// Rust), which owns and may write its by-address parameters (the C ABI's
/// caller-made copy) and may keep a pointer argument. ODR linkage promises
/// equivalent observable results, not the same use of the ABI's private
/// argument copies, so the `_odr` forms are replaceable too.
///
/// An object therefore treats a call to such a definition as a call to an
/// import (`compile_object_parts` puts it in the `foreign` set), and
/// `trust_cg_irmid::escape::analyzable` derives no capture facts from its body. A closed
/// module has no linker, so its bodies are final.
///
/// The verdict is the capture analysis's own
/// (`trust_cg_irmid::escape::interposable_linkage`).
pub(super) fn interposable_linkage(linkage: trust_ir::Linkage) -> bool {
    trust_cg_irmid::escape::interposable_linkage(linkage)
}

/// Symbol attributes of a DEFINITION with this linkage / visibility /
/// retention.
///
/// `Protected` is visible and non-preemptible. A wasm symbol has no
/// preemption (a linked module binds every reference at link time), so
/// protected is honored by the DEFAULT visibility; `WASM_SYM_VISIBILITY_HIDDEN`
/// would additionally withhold the symbol from `--export-dynamic`, which
/// protected does not ask for (clang maps protected to default on wasm too).
fn symbol_flags(
    linkage: trust_ir::Linkage,
    visibility: trust_ir::Visibility,
    retained: bool,
) -> super::encode::SymbolFlags {
    use trust_ir::Linkage as L;
    super::encode::SymbolFlags {
        local: matches!(linkage, L::Internal | L::Private),
        weak: interposable_linkage(linkage),
        hidden: !matches!(linkage, L::Internal | L::Private)
            && visibility == trust_ir::Visibility::Hidden,
        no_strip: retained,
    }
}

/// Symbol attributes of an UNDEFINED symbol (a declaration or a data import):
/// only its visibility. A reference is always STRONG — an initializer-less
/// `weak`/`linkonce` global is classified as an import exactly as the native
/// lanes classify it, and the native lanes keep every such import a strong
/// undefined reference; a weak undefined wasm symbol would instead resolve to
/// address 0 when nothing defines it, aliasing every such global. The encoder
/// writes only the visibility of an undefined symbol either way.
fn import_symbol_flags(visibility: trust_ir::Visibility) -> super::encode::SymbolFlags {
    super::encode::SymbolFlags {
        hidden: visibility == trust_ir::Visibility::Hidden,
        ..Default::default()
    }
}

/// Whether a global is a reference to data defined ELSEWHERE (an undefined
/// data symbol in an object): an initializer-less external/weak one, or an
/// `available_externally` one.
fn global_is_import(global: &trust_ir::Global) -> bool {
    use trust_ir::Linkage as L;
    matches!(global.linkage, L::AvailableExternally | L::ExternalWeak)
        || (global.initializer.is_none()
            && matches!(
                global.linkage,
                L::External | L::Weak | L::LinkOnce | L::WeakOdr | L::LinkOnceOdr
            ))
}

/// Compile a trust-ir module to a RELOCATABLE wasm32 OBJECT for `wasm-ld`
/// (WebAssembly tool-conventions `Linking.md`) — the wasm counterpart of the
/// native ELF/Mach-O/COFF object writers, and what a Rust crate is compiled to
/// before rustc links it.
///
/// Unlike [`compile_module`], nothing here is closed:
///
/// * the linear memory is imported (`env.__linear_memory`), the stack pointer
///   is the linker's `env.__stack_pointer`, and an indirect call goes through
///   the linker's `env.__indirect_function_table`;
/// * every body-less function is an UNDEFINED function symbol and every
///   initializer-less external global an UNDEFINED data symbol, both resolved
///   by the linker — typically against LLVM-compiled `core` and
///   `compiler_builtins` objects;
/// * every definition is a symbol with the binding and visibility its trust-ir
///   linkage and visibility state; every global and pooled constant is its own
///   data segment;
/// * every function index, data address, table index, type index and global
///   index in the code (and every pointer in static data) is relocated;
/// * `FRem` calls the library's `fmod` / `fmodf`, as LLVM's lowering does;
/// * 128-bit division calls the lane's own trust-ir helper, which the object
///   DEFINES as a weak hidden symbol named by
///   [`super::helpers::divmod128_helper_name`] (one copy survives the link);
/// * nothing is exported: which symbols a linked module exports is the
///   linker's decision (`--export`, `--export-dynamic`).
///
/// It compiles at the lane's default level, O2: see [`compile_object_optimized`].
pub fn compile_object(module: &Module) -> Result<Vec<u8>, WasmLowerError> {
    compile_object_with_license(module, &CodegenLicensePolicy::default())
}

/// [`compile_object`] at an explicit optimization level. The level selects
/// both of the lane's optimizations, the trust-ir mid-end (`super::mid`) and
/// the local emission pass: at O0 neither runs and every function is emitted
/// with its baseline body (the bytes the lane emitted before either pass
/// existed); at O1 and above the mid-end's validated output is lowered where
/// it passes the lane's re-checks, and each function's rewritten body is used
/// where `trust_cg_verify::wasm_local_tv` validates it (see
/// [`WasmLocalOptSummary`] and [`IrmidReport`]). The rustc bridge's
/// `no-wasm-local-opt` knob compiles at O0, so it switches off both.
pub fn compile_object_optimized(
    module: &Module,
    level: OptLevel,
) -> Result<Vec<u8>, WasmLowerError> {
    compile_object_with_license_optimized(module, &CodegenLicensePolicy::default(), level)
}

/// [`compile_object`] under the caller's codegen-license policy, admitted as
/// [`compile_module_with_policy_and_license`] admits a closed module.
pub fn compile_object_with_license(
    module: &Module,
    license: &CodegenLicensePolicy,
) -> Result<Vec<u8>, WasmLowerError> {
    compile_object_with_license_optimized(module, license, DEFAULT_OPT_LEVEL)
}

/// [`compile_object`] under the caller's codegen-license policy and at an
/// explicit optimization level: [`compile_object_with_license`]'s admission
/// and [`compile_object_optimized`]'s emission.
pub fn compile_object_with_license_optimized(
    module: &Module,
    license: &CodegenLicensePolicy,
    level: OptLevel,
) -> Result<Vec<u8>, WasmLowerError> {
    compile_object_with_license_options(module, license, WasmOptOptions::at(level))
}

/// [`compile_object_with_license_optimized`] with the optimizations chosen
/// by `options`: the level, and whether the trust-ir mid-end runs.
pub fn compile_object_with_license_options(
    module: &Module,
    license: &CodegenLicensePolicy,
    options: WasmOptOptions,
) -> Result<Vec<u8>, WasmLowerError> {
    compile_object_with_license_options_hints(module, license, options, &WasmInlineHints::default())
}

/// [`compile_object_with_license_options`] with the producer's inline
/// hints ([`WasmInlineHints`]: the functions the mid-end's inliner never
/// splices).
pub fn compile_object_with_license_options_hints(
    module: &Module,
    license: &CodegenLicensePolicy,
    options: WasmOptOptions,
    hints: &WasmInlineHints,
) -> Result<Vec<u8>, WasmLowerError> {
    let mut parts = compile_object_parts(module, license, options, hints)?;
    // The CFG structural invariant runs on every object: a REFUTED verdict (a
    // branch to no live label, an operand stack that does not type-check)
    // fails the compile rather than hand a broken object to the linker. An
    // inconclusive verdict is uncredited but does not block.
    let (mut ran, mut not_run) = (Vec::new(), Vec::new());
    classify_cfg_verdict(parts.take_cfg_verdict(), &mut ran, &mut not_run)?;
    Ok(parts.bytes)
}

/// [`compile_object`], plus the same honest [`WasmCompileEvidence`] summary a
/// closed compile reports. The CFG structural invariant runs over the object's
/// bytes (an object is a valid wasm module), and the evidence's
/// `host_contract` is the object's LINK contract: every undefined symbol and
/// linker-owned entity it imports.
pub fn compile_object_with_evidence(
    module: &Module,
) -> Result<(Vec<u8>, WasmCompileEvidence), WasmLowerError> {
    compile_object_with_evidence_and_license(module, &CodegenLicensePolicy::default())
}

/// [`compile_object_with_evidence`] at an explicit optimization level (see
/// [`compile_object_optimized`]).
pub fn compile_object_with_evidence_optimized(
    module: &Module,
    level: OptLevel,
) -> Result<(Vec<u8>, WasmCompileEvidence), WasmLowerError> {
    compile_object_with_evidence_license_optimized(module, &CodegenLicensePolicy::default(), level)
}

/// [`compile_object_with_evidence`] under the caller's codegen-license
/// policy, admitted as [`compile_object_with_license`] admits it.
pub fn compile_object_with_evidence_and_license(
    module: &Module,
    license: &CodegenLicensePolicy,
) -> Result<(Vec<u8>, WasmCompileEvidence), WasmLowerError> {
    compile_object_with_evidence_license_optimized(module, license, DEFAULT_OPT_LEVEL)
}

/// [`compile_object_with_evidence`] under the caller's codegen-license policy
/// and at an explicit optimization level (see
/// [`compile_object_with_license_optimized`]).
pub fn compile_object_with_evidence_license_optimized(
    module: &Module,
    license: &CodegenLicensePolicy,
    level: OptLevel,
) -> Result<(Vec<u8>, WasmCompileEvidence), WasmLowerError> {
    compile_object_with_evidence_license_options(module, license, WasmOptOptions::at(level))
}

/// [`compile_object_with_evidence_license_optimized`] with the optimizations
/// chosen by `options` (see [`compile_object_with_license_options`]).
pub fn compile_object_with_evidence_license_options(
    module: &Module,
    license: &CodegenLicensePolicy,
    options: WasmOptOptions,
) -> Result<(Vec<u8>, WasmCompileEvidence), WasmLowerError> {
    compile_object_with_evidence_license_options_hints(
        module,
        license,
        options,
        &WasmInlineHints::default(),
    )
}

/// [`compile_object_with_evidence_license_options`] with the producer's
/// inline hints (see [`compile_object_with_license_options_hints`]).
pub fn compile_object_with_evidence_license_options_hints(
    module: &Module,
    license: &CodegenLicensePolicy,
    options: WasmOptOptions,
    hints: &WasmInlineHints,
) -> Result<(Vec<u8>, WasmCompileEvidence), WasmLowerError> {
    let mut parts = compile_object_parts(module, license, options, hints)?;
    let cfg_verdict = parts.take_cfg_verdict();
    let CompiledParts {
        bytes,
        host_contract,
        local_emission,
        mid_end,
        ..
    } = parts;
    let mut ran = vec![
        "wasm32_target_info_guard",
        "trust_ir_codegen_admission",
        "codegen_license",
        "calling_convention_guard",
        "eh_instruction_reject_scan",
        "cfg_structuring",
        "import_index_space_guard",
        "relocatable_object_encoding",
    ];
    let mut not_run = vec![
        "per_function_lowering_proofs",
        "translation_validation",
        "solver_verification",
        "per_module_differential_execution",
        "optimization_pipeline",
        // The linker resolves the undefined symbols and lays memory out;
        // nothing here checks what it binds them to.
        "link_verification",
    ];
    // trust-ir v74: a module holding an `Inst::BoxDeref` compiled only
    // because the license opted below the refusing default: the
    // named-premise floor, whose Box validity is ASSUMED (the assumptions
    // are in the license's `BoxDerefDisclosure`), or this backend's
    // locally re-derived floor, a consumer-side analysis that is not proof
    // evidence. Either way validity is not ESTABLISHED by any check here.
    if trust_cg_lower::box_deref::module_has_box_deref(module) {
        not_run.push(BOX_VALIDITY_NOT_ESTABLISHED);
    }
    if local_emission.optimized > 0 {
        ran.push("wasm_local_emission_tv");
    }
    credit_mid_end(&mid_end, &mut ran, &mut not_run);
    let cfg_structural = classify_cfg_verdict(cfg_verdict, &mut ran, &mut not_run)?;
    let evidence = WasmCompileEvidence {
        schema: WASM_COMPILE_EVIDENCE_SCHEMA,
        target: super::target::WASM32_TRIPLE,
        verdict: ProofEvidenceVerdict::MissingEvidence,
        verification_route: EvidenceStrength::NotRun,
        assurance_tier: "differential-tested (offline corpus difftest + link-and-run \
                         differential; not run on this compile). The CFG structural invariant \
                         runs on these bytes and verifies no lowering",
        ran,
        not_run,
        function_count: module
            .functions
            .iter()
            .filter(|f| !is_declaration(f))
            .count(),
        module_size_bytes: bytes.len(),
        module_sha256: crate::jit_diagnostics::sha256_hex(&bytes),
        host_contract,
        cfg_structural,
        local_emission,
        mid_end,
    };
    Ok((bytes, evidence))
}

/// Every function `constant` names at ANY depth: a `FnDef`, a closure's
/// function, or a `SymbolAddr` that resolves to a function — whether it is
/// the constant itself or an element of an aggregate, array, record or
/// closure capture (a vtable is an array of `FnDef`s).
fn constant_function_refs(module: &Module, constant: &Constant, out: &mut Vec<FuncId>) {
    constant.visit_constants(|c| match c {
        Constant::FnDef(fid) => out.push(*fid),
        Constant::Closure { func, .. } => out.push(*func),
        Constant::SymbolAddr { symbol, addend } => {
            if let Ok(layout::ImageRef::Func(fid)) = layout::resolve_symbol(module, symbol, *addend)
            {
                out.push(fid);
            }
        }
        _ => {}
    });
}

/// Every function whose ADDRESS `module` takes, in definition order: named by
/// a `Const` in code at any depth ([`constant_function_refs`]), or by a
/// global's initializer.
fn address_taken_functions(module: &Module) -> Vec<FuncId> {
    let mut out = Vec::new();
    for node in module
        .functions
        .iter()
        .flat_map(|f| f.blocks.iter().flat_map(|b| &b.body))
    {
        if let Inst::Const { value, .. } = &node.inst {
            constant_function_refs(module, value, &mut out);
        }
    }
    for global in &module.globals {
        if let Some(init) = &global.initializer {
            constant_function_refs(module, init, &mut out);
        }
    }
    out
}

/// Every function a body or a static-data image of `module` names: a direct
/// callee, or a function whose address is taken
/// ([`address_taken_functions`]).
fn referenced_functions(module: &Module) -> HashSet<FuncId> {
    let mut out: HashSet<FuncId> = address_taken_functions(module).into_iter().collect();
    for node in module
        .functions
        .iter()
        .flat_map(|f| f.blocks.iter().flat_map(|b| &b.body))
    {
        if let Inst::Call { callee, .. } = &node.inst {
            out.insert(*callee);
        }
    }
    out
}

/// Whether a declaration nothing references is left out of the object: one
/// whose signature has no wasm32 import (a C variadic, a Rust-convention
/// placeholder `(...)`) or may not cross a link boundary
/// ([`abi::rust_link_boundary_refusal`]). A declaration is only a promise
/// that the symbol exists; with no reference there is nothing to bind, which
/// is also why LLVM emits no import for one.
fn skip_unreferenced_declaration(
    module: &Module,
    func: &Function,
    referenced: &HashSet<FuncId>,
) -> Result<bool, WasmLowerError> {
    if referenced.contains(&func.id) {
        return Ok(false);
    }
    let Some(ft) = module.func_type(func.ty) else {
        return Ok(false);
    };
    Ok(ft.is_vararg
        || (func.calling_conv == CallingConv::Rust
            && abi::rust_link_boundary_refusal(module, ft)?.is_some()))
}

/// Symbols `wasm-ld` synthesizes (or that this object imports from it). A
/// module-wide DEFINITION of one would be a second definition the linker
/// resolves against its own — a signature-mismatch stub or a duplicate — and
/// any symbol named like the stack pointer or the table the object imports
/// is a second symbol of that name in the object itself.
const WASM_LINKER_SYNTHETIC_SYMBOLS: &[&str] = &[
    super::encode::OBJECT_STACK_POINTER_IMPORT,
    super::encode::OBJECT_TABLE_IMPORT,
    "__wasm_call_ctors",
    "__wasm_init_memory",
    "__wasm_init_tls",
    "__wasm_apply_data_relocs",
    "__wasm_apply_global_relocs",
    "__wasm_first_page_end",
    "__heap_base",
    "__heap_end",
    "__data_end",
    "__global_base",
    "__dso_handle",
    "__memory_base",
    "__table_base",
    "__stack_low",
    "__stack_high",
    "__tls_base",
    "__tls_size",
    "__tls_align",
];

/// Refuse what would give the object two NON-LOCAL symbols of one name, or a
/// definition of a name the linker owns (`[TCG-WASM-SYMBOL]`), before
/// anything is emitted:
///
/// * a non-local definition (function body, or a global with bytes) whose
///   name is in [`WASM_LINKER_SYNTHETIC_SYMBOLS`], or any non-local symbol
///   named like the stack pointer or table the object imports;
/// * two non-local symbols of one name — two definitions, a definition and a
///   declaration, a function and a global — except body-less declarations
///   of one kind, which share one undefined symbol when they agree (see the
///   declaration and data-import loops of [`compile_object_parts`]).
///
/// Module-local (internal/private) definitions are local symbols and never
/// collide. `WasmModule::object_duplicate_symbol` re-checks the finished
/// symbol table as a backstop.
fn reject_object_symbol_collisions(
    module: &Module,
    referenced: &HashSet<FuncId>,
) -> Result<(), WasmLowerError> {
    // Every non-local symbol the module names: (name, kind, body-less).
    let mut claims: Vec<(&str, &'static str, bool)> = Vec::new();
    for func in &module.functions {
        let import = is_declaration(func);
        if import && skip_unreferenced_declaration(module, func, referenced)? {
            continue;
        }
        if !import && trust_cg_lower::is_module_local_function_definition(func) {
            continue;
        }
        claims.push((func.name.as_str(), "function", import));
    }
    for global in &module.globals {
        let import = global_is_import(global);
        if !import && trust_cg_lower::is_module_local_data_definition(global) {
            continue;
        }
        claims.push((global.name.as_str(), "global", import));
    }
    let mut seen: HashMap<&str, (&'static str, bool)> = HashMap::new();
    for (sym, kind, import) in claims {
        let own_import = sym == super::encode::OBJECT_STACK_POINTER_IMPORT
            || sym == super::encode::OBJECT_TABLE_IMPORT;
        if own_import || (!import && WASM_LINKER_SYNTHETIC_SYMBOLS.contains(&sym)) {
            return Err(WasmLowerError::ContractSurface(format!(
                "[TCG-WASM-SYMBOL] module `{}` {} a non-local {kind} `{sym}`, a symbol \
                 `wasm-ld` synthesizes (or this object imports from it); the linker would \
                 bind it to its own entity — refusing (give it internal linkage, or another \
                 name)",
                module.name,
                if import { "references" } else { "defines" },
            )));
        }
        match seen.get(sym) {
            None => {
                seen.insert(sym, (kind, import));
            }
            Some(&(prev, prev_import)) if prev == kind && prev_import && import => {}
            Some(&(prev, _)) => {
                return Err(WasmLowerError::ContractSurface(format!(
                    "[TCG-WASM-SYMBOL] module `{}` has two non-local symbols named `{sym}` (a \
                     {prev} and a {kind}); a wasm object names a symbol once, so only \
                     body-less declarations of one kind may share it",
                    module.name
                )));
            }
        }
    }
    Ok(())
}

/// Refuse a module that names, with any linkage, a function or global under
/// [`super::helpers::DIVMOD128_SYMBOL_PREFIX`] (`[TCG-WASM-SYMBOL]`). Those
/// names are reserved for the weak hidden 128-bit division helper every
/// dividing object defines; a strong definition in any object of the link
/// would replace it, and a declaration would bind to it. The check holds per
/// object and does not depend on whether this module divides: a frontend
/// that compiles one crate as several objects (the bridge's per-function
/// fallback) puts a definition and the division it would hijack into
/// different objects.
fn reject_reserved_helper_symbols(module: &Module) -> Result<(), WasmLowerError> {
    let prefix = super::helpers::DIVMOD128_SYMBOL_PREFIX;
    let named = module
        .functions
        .iter()
        .map(|f| (f.name.as_str(), "function"))
        .chain(module.globals.iter().map(|g| (g.name.as_str(), "global")))
        .find(|(name, _)| name.starts_with(prefix));
    if let Some((sym, kind)) = named {
        return Err(WasmLowerError::ContractSurface(format!(
            "[TCG-WASM-SYMBOL] module `{}` names the {kind} `{sym}`; the `{prefix}` prefix is \
             reserved for the wasm32 object lane's 128-bit division helper, which any object \
             of the link may define — refusing a symbol that could replace or bind to it",
            module.name
        )));
    }
    Ok(())
}

/// The mark a crate-private symbol carries before its 16 lowercase hex
/// digits: the rustc bridge names every CGU-private function rustc placed
/// `<symbol>.tcg.crate.<StableCrateId>` (`wasm32_linkage::crate_private_symbol`),
/// a name every object of that crate defines and references it by and no
/// other crate's object can.
const CRATE_PRIVATE_MARK: &str = ".tcg.crate.";

/// The suffix of an internal entry's symbol: `<crate-private name>.tcg.mv`
/// ([`internal_abi_symbol`]). Reserved: a module naming a function or global
/// with it is refused ([`reject_reserved_internal_abi_symbols`]).
const INTERNAL_ABI_SUFFIX: &str = ".tcg.mv";

/// The symbol of `name`'s internal entry.
fn internal_abi_symbol(name: &str) -> String {
    format!("{name}{INTERNAL_ABI_SUFFIX}")
}

/// Whether `name` is a crate-private name: a non-empty symbol, the
/// [`CRATE_PRIVATE_MARK`], then exactly 16 lowercase hex digits.
fn is_crate_private_name(name: &str) -> bool {
    let Some(at) = name.rfind(CRATE_PRIVATE_MARK) else {
        return false;
    };
    let tag = &name[at + CRATE_PRIVATE_MARK.len()..];
    at > 0
        && tag.len() == 16
        && tag
            .bytes()
            .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
}

/// The name the linked module's `name` section shows for the function whose
/// object symbol is `symbol`, when it differs from the symbol: the symbol
/// without each crate-private mark and its 16 lowercase hex digits
/// ([`CRATE_PRIVATE_MARK`]) that ends the name or a `.`-separated part of it,
/// and then, when a mark was removed, without a trailing internal-entry
/// suffix ([`INTERNAL_ABI_SUFFIX`]). `<path>.tcg.crate.<tag>` and its
/// internal entry `<path>.tcg.crate.<tag>.tcg.mv` are both shown as
/// `<path>`, the name rustc's LLVM backend gives the function, and an
/// argument-promoted clone `<path>.tcg.ap<h>.tcg.crate.<tag>` as
/// `<path>.tcg.ap<h>`, since its signature is not the source function's. The
/// mark and the suffix only route the link (one crate's copy apart from
/// another's, a direct call to the multi-value entry), which a debugger does
/// not need.
///
/// Debug information only: the symbol keeps both, so what the linker
/// resolves, what the internal-ABI gate and the bridge's link check read, and
/// every export and import name are unchanged. Two functions of a linked
/// module may share a debug name (a C-form entry and its internal entry, or
/// two crates' private copies of one upstream function), which a `name`
/// section allows.
fn debug_function_name(symbol: &str) -> Option<String> {
    const TAG_LEN: usize = 16;
    let mut out = String::with_capacity(symbol.len());
    let mut rest = symbol;
    let mut changed = false;
    while let Some(at) = rest.find(CRATE_PRIVATE_MARK) {
        let tail = &rest[at + CRATE_PRIVATE_MARK.len()..];
        let is_tag = tail.len() >= TAG_LEN
            && tail.as_bytes()[..TAG_LEN]
                .iter()
                .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(b))
            && matches!(tail.as_bytes().get(TAG_LEN), None | Some(b'.'));
        let prefix_nonempty = !out.is_empty() || at > 0;
        if is_tag && prefix_nonempty {
            out.push_str(&rest[..at]);
            rest = &tail[TAG_LEN..];
            changed = true;
        } else {
            let keep = at + CRATE_PRIVATE_MARK.len();
            out.push_str(&rest[..keep]);
            rest = &rest[keep..];
        }
    }
    out.push_str(rest);
    if !changed {
        return None;
    }
    if let Some(plain) = out.strip_suffix(INTERNAL_ABI_SUFFIX) {
        out.truncate(plain.len());
    }
    Some(out)
}

/// The fewest code bytes a body needs before [`finish_with_body_folds`]
/// folds it: a forwarder adds one call to every call of the folded function,
/// which only a body this long makes small beside the work it does.
const BODY_FOLD_MIN_CODE: usize = 128;

/// Encode an object whose identical bodies are folded: the bodies of
/// `eligible` functions (trust-ir definitions that use the C ABI, never an
/// internal entry, its C-form entry or a lane helper) that
/// [`WasmModule::plan_body_folds`] finds equal become forwarders to one kept
/// copy ([`WasmModule::apply_body_folds`]). The folded object is returned
/// only when `trust_cg_verify::wasm_body_fold::check_body_folds`, over the
/// object encoded before and after, re-derives from the bytes that every
/// folded body equalled its kept body and is now exactly a forwarder to it,
/// that no forwarder lies on a cycle of calls among the object's functions
/// (an indirect call reaching every function whose address the object takes
/// and every function another object can name), and that nothing
/// else changed; otherwise the unfolded object is returned.
/// A fold never refuses a compile.
fn finish_with_body_folds(wasm: &mut WasmModule, eligible: &HashSet<u32>) -> Vec<u8> {
    let plan = wasm.plan_body_folds(&|f| eligible.contains(&f), BODY_FOLD_MIN_CODE);
    let before = wasm.finish();
    if plan.is_empty() {
        return before;
    }
    let applied = wasm.apply_body_folds(&plan);
    if applied.is_empty() {
        return before;
    }
    let after = wasm.finish();
    match trust_cg_verify::wasm_body_fold::check_body_folds(&before, &after, &applied) {
        Ok(_) => after,
        Err(_) => before,
    }
}

/// Record [`debug_function_name`] of `symbol` for the defined function
/// `idx`, when it differs from the symbol.
fn set_debug_name(wasm: &mut WasmModule, idx: u32, symbol: &str) {
    if let Some(name) = debug_function_name(symbol) {
        wasm.set_function_debug_name(idx, &name);
    }
}

/// The functions of an object that use the internal ABI: every function,
/// defined or declared, that is
///
/// * a STRONG (`External`) symbol with HIDDEN visibility under a
///   crate-private name ([`is_crate_private_name`]): only this crate's
///   objects can name it, all of them compiled by this lane with one level,
///   and the linker binds every reference to its one definition (a weak or
///   link-once copy, which the linker may replace, is excluded); and
/// * of a signature with an internal form ([`abi::lower_internal_sig`]).
///
/// The verdict depends only on the name, linkage, visibility and signature,
/// which every object of the crate gives a function's definition and its
/// declarations alike (the bridge stamps a declaration with its definition's
/// visibility), so every object decides it the same way. Such a function is
/// DEFINED as its internal entry under [`internal_abi_symbol`] plus a C-form
/// entry under its own name that forwards to it
/// ([`emit_internal_abi_thunk`]), and every direct call to it in any object
/// calls the internal entry. Whether its address is taken does not matter: a
/// function pointer, in this object or another (a static's data, a vtable),
/// names the C-form entry, so foreign code and `call_indirect` never meet
/// the internal ABI. A caller that does not know the plan calls the C-form
/// entry, which is always correct; a caller that calls an internal entry no
/// object defines fails to link.
///
/// The plan is consulted only at O1 and above and only when the producer
/// admits the `multivalue` feature (`WasmInlineHints::without_multivalue`
/// unset); otherwise every function keeps the C form. The rustc bridge
/// derives that switch from the session, so all objects of one crate agree
/// on it.
fn internal_abi_plan(module: &Module) -> HashSet<FuncId> {
    module
        .functions
        .iter()
        .filter(|f| {
            f.linkage == trust_ir::Linkage::External
                && f.visibility == trust_ir::Visibility::Hidden
                && is_crate_private_name(&f.name)
                && module.func_type(f.ty).is_some_and(|ft| {
                    !ft.is_vararg
                        && matches!(
                            abi::lower_internal_sig(module, ft, f.calling_conv),
                            Ok(Some(_))
                        )
                })
        })
        .map(|f| f.id)
        .collect()
}

/// The functions a direct `Call` names.
fn directly_called_functions(module: &Module) -> HashSet<FuncId> {
    module
        .functions
        .iter()
        .flat_map(|f| f.blocks.iter().flat_map(|b| &b.body))
        .filter_map(|n| match &n.inst {
            Inst::Call { callee, .. } => Some(*callee),
            _ => None,
        })
        .collect()
}

/// The internal form of a planned function's signature.
fn internal_entry_sig(module: &Module, func: &Function) -> Result<WasmSig, WasmLowerError> {
    let ft = module.func_type(func.ty).ok_or_else(|| {
        WasmLowerError::UnsupportedInst(format!(
            "function `{}` has unknown signature {:?}",
            func.name, func.ty
        ))
    })?;
    abi::lower_internal_sig(module, ft, func.calling_conv)?.ok_or_else(|| {
        WasmLowerError::UnsupportedAbi(format!(
            "[TCG-WASM-INTERNAL-ABI] `{}` is planned for the internal ABI, but its signature \
             has no internal form",
            func.name
        ))
    })
}

/// Emit the C-form entry of planned definition `func`, whose body is its
/// internal entry, wasm function `internal`, and return its index. It passes
/// its parameters after the `sret` pointer on unchanged (the two forms share
/// their parameter lanes), calls the internal entry, and writes each result
/// where the C form's own return writes it (`calls.rs`, `emit_return`): a
/// scalar with its type's store at its C-layout offset in the `sret` buffer
/// (a lone 128-bit result at offset 0), a 128-bit integer as its low and
/// high halves at that offset and 8 bytes on. It touches no stack-pointer
/// global and no frame.
fn emit_internal_abi_thunk(
    wasm: &mut WasmModule,
    module: &Module,
    func: &Function,
    internal: u32,
) -> Result<u32, WasmLowerError> {
    use super::encode::{RelocKind, RelocTarget, write_padded_uleb128};
    let ft = module.func_type(func.ty).ok_or_else(|| {
        WasmLowerError::UnsupportedInst(format!(
            "function `{}` has unknown signature {:?}",
            func.name, func.ty
        ))
    })?;
    let c = abi::lower_sig(module, ft, func.calling_conv)?;
    let inner = internal_entry_sig(module, func)?;
    let drift = |what: &str| {
        WasmLowerError::UnsupportedAbi(format!(
            "[TCG-WASM-INTERNAL-ABI] the C and internal forms of `{}` disagree: {what}",
            func.name
        ))
    };
    if !c.sret
        || c.wasm.params.first() != Some(&ValType::I32)
        || c.wasm.params[1..] != inner.wasm.params[..]
        || !c.wasm.results.is_empty()
        || c.rets.len() != inner.rets.len()
    {
        return Err(drift("parameters or result shape"));
    }
    let params = u32::try_from(c.wasm.params.len()).map_err(|_| drift("parameter count"))?;
    let mut code = Vec::new();
    let mut relocs = Vec::new();
    for p in 1..params {
        emit_local_get(&mut code, p);
    }
    code.push(op::CALL);
    relocs.push(Reloc {
        kind: RelocKind::FunctionIndexLeb,
        offset: code.len() as u32,
        target: RelocTarget::Func(internal),
        addend: 0,
    });
    write_padded_uleb128(&mut code, internal);
    // One declared local per result value, set from the top of the stack.
    let declared = inner.wasm.results.clone();
    let results = declared.len() as u32;
    for k in (0..results).rev() {
        code.push(op::LOCAL_SET);
        write_uleb128(&mut code, u64::from(params + k));
    }
    let mut next = params;
    let mut store = |code: &mut Vec<u8>, ty: &Ty, offset: u32| -> Result<(), WasmLowerError> {
        let (_, store_op, align) = mem_ops(ty)?;
        emit_local_get(code, 0);
        emit_local_get(code, next);
        next += 1;
        code.push(store_op);
        emit_memarg(code, align, offset);
        Ok(())
    };
    for ((c_lane, lane), ty) in c.rets.iter().zip(&inner.rets).zip(&ft.returns) {
        let offset = match c_lane {
            abi::RetLane::Void => continue,
            abi::RetLane::Field { offset, .. } => *offset,
            abi::RetLane::Sret { .. } => 0,
            _ => return Err(drift("a C result lane that is not in the sret buffer")),
        };
        match lane {
            abi::RetLane::Scalar(_) => store(&mut code, ty, offset)?,
            abi::RetLane::Wide => {
                let high = offset
                    .checked_add(8)
                    .ok_or_else(|| drift("result offset"))?;
                store(&mut code, &Ty::U64, offset)?;
                store(&mut code, &Ty::U64, high)?;
            }
            _ => return Err(drift("an internal result lane")),
        }
    }
    if next != params + results {
        return Err(drift("result count"));
    }
    let ty_idx = wasm.add_type(c.wasm);
    Ok(wasm.add_function(
        ty_idx,
        FuncBody {
            locals: run_length_encode(&declared),
            code,
            relocs,
        },
    ))
}

/// Refuse a module that names, with any linkage, a function or global
/// ending in [`INTERNAL_ABI_SUFFIX`] (`[TCG-WASM-SYMBOL]`): those names are
/// the internal entries of crate-private functions, which any object of the
/// crate may define or call by name with the internal ABI.
fn reject_reserved_internal_abi_symbols(module: &Module) -> Result<(), WasmLowerError> {
    let named = module
        .functions
        .iter()
        .map(|f| (f.name.as_str(), "function"))
        .chain(module.globals.iter().map(|g| (g.name.as_str(), "global")))
        .find(|(name, _)| name.ends_with(INTERNAL_ABI_SUFFIX));
    if let Some((sym, kind)) = named {
        return Err(WasmLowerError::ContractSurface(format!(
            "[TCG-WASM-SYMBOL] module `{}` names the {kind} `{sym}`; the `{INTERNAL_ABI_SUFFIX}` \
             suffix is reserved for the wasm32 object lane's internal-ABI entries, which other \
             objects call by name — refusing a symbol that could replace or bind to one",
            module.name
        )));
    }
    Ok(())
}

/// Refuse a `CallingConv::Rust` signature whose aggregate lanes would cross
/// a LINK boundary ([`abi::rust_link_boundary_refusal`]): this lane's Rust
/// convention is an ABI only between the functions it compiles, and rustc's
/// Rust ABI for the same aggregate differs, so a linked caller or callee
/// would read the other side's bytes wrongly with no link error. The
/// boundary is every body-less declaration, every definition another object
/// may call (any linkage but internal/private), every function whose address
/// is taken (the pointer may reach foreign code), and every indirect call
/// (its target may be foreign).
fn reject_rust_abi_link_boundary(
    module: &Module,
    referenced: &HashSet<FuncId>,
) -> Result<(), WasmLowerError> {
    let refuse = |what: String, ft: &trust_ir::FuncTy| -> Result<(), WasmLowerError> {
        match abi::rust_link_boundary_refusal(module, ft)? {
            None => Ok(()),
            Some(why) => Err(WasmLowerError::UnsupportedAbi(format!(
                "[TCG-WASM-RUST-ABI-LINK] {what} uses CallingConv::Rust with {why} at a link \
                 boundary; the wasm32 object lane's Rust convention (aggregates by address, \
                 `sret` returns) is not rustc's Rust ABI, so a linked caller or callee would \
                 disagree about its bytes — refusing (use CallingConv::C, or internal linkage \
                 for a function only this object calls)"
            ))),
        }
    };
    let sig_of = |f: &Function| {
        module.func_type(f.ty).ok_or_else(|| {
            WasmLowerError::UnsupportedInst(format!(
                "function `{}` has unknown signature {:?}",
                f.name, f.ty
            ))
        })
    };
    for func in &module.functions {
        for node in func.blocks.iter().flat_map(|b| &b.body) {
            if let Inst::CallIndirect {
                sig,
                calling_conv: CallingConv::Rust,
                ..
            } = &node.inst
                && let Some(ft) = module.func_type(*sig)
            {
                refuse(format!("an indirect call in `{}`", func.name), ft)?;
            }
        }
    }
    let address_taken: HashSet<FuncId> = address_taken_functions(module).into_iter().collect();
    for func in &module.functions {
        if func.calling_conv != CallingConv::Rust {
            continue;
        }
        let what = if is_declaration(func) {
            if !referenced.contains(&func.id) {
                // Not imported ([`skip_unreferenced_declaration`]).
                continue;
            }
            format!("declaration `{}`", func.name)
        } else if !trust_cg_lower::is_module_local_function_definition(func) {
            format!("externally visible function `{}`", func.name)
        } else if address_taken.contains(&func.id) {
            format!("function `{}`, whose address is taken,", func.name)
        } else {
            continue;
        };
        refuse(what, sig_of(func)?)?;
    }
    Ok(())
}

fn compile_object_parts(
    module: &Module,
    license: &CodegenLicensePolicy,
    options: WasmOptOptions,
    hints: &WasmInlineHints,
) -> Result<CompiledParts, WasmLowerError> {
    require_wasm32_target_info(module)?;
    admit_object(module, license)?;
    // The internal ABI declares `+multivalue`: a session that withholds the
    // feature keeps every function on the C form.
    let internal_abi = !hints.without_multivalue;
    // The linker places an object's data apart from its stack, so a promoted
    // table's static data takes nothing from the stack.
    let (candidate, mut mid) = super::mid::optimize(
        module,
        options,
        super::mid::StaticDataRoom::Grows,
        hints,
        |m| admit_object(m, license),
    );
    if let Some(candidate) = candidate {
        // As in `compile_module_parts`: the input must lower first, so no
        // rewrite turns a lane refusal into an accepted object, the output
        // is screened by the CFG structural invariant, and the input's
        // lowering is kept for the caller's structural check.
        let (input, _, _) = lower_object_parts(module, options.level, internal_abi, true)?;
        match lower_object_parts(&candidate, options.level, internal_abi, false) {
            Ok((bytes, host_contract, local_emission)) => {
                if let Some(verdict) = screen_mid_end_output(&bytes, &mut mid) {
                    return Ok(CompiledParts {
                        bytes,
                        host_contract,
                        local_emission,
                        mid_end: mid,
                        cfg_verdict: Some(verdict),
                        input_check: Some(input),
                    });
                }
            }
            Err(error) => mid.fall_back(format!("the lane refused the optimized module: {error}")),
        }
    }
    let (bytes, host_contract, local_emission) =
        lower_object_parts(module, options.level, internal_abi, false)?;
    Ok(CompiledParts {
        bytes,
        host_contract,
        local_emission,
        mid_end: mid,
        cfg_verdict: None,
        input_check: None,
    })
}

/// The object lane's admission and link-surface refusals, decided before any
/// body is walked.
fn admit_object(module: &Module, license: &CodegenLicensePolicy) -> Result<(), WasmLowerError> {
    admit_for_codegen(module, license)?;
    reject_unconsumed_object_surface(module)?;
    reject_shared_signature_surface(module)?;
    reject_stack_limit_requests(module)?;
    reject_reserved_helper_symbols(module)?;
    reject_reserved_internal_abi_symbols(module)?;
    let referenced = referenced_functions(module);
    reject_object_symbol_collisions(module, &referenced)?;
    reject_rust_abi_link_boundary(module, &referenced)?;
    admit_ingestion(module, license)
}

/// Lower an admitted module to a relocatable object.
///
/// `module` passed [`admit_object`] under the caller's license immediately
/// before this call ([`FunctionLicense::DecidedForModule`]).
///
/// `internal_abi` admits the internal multi-value ABI at O1 and above
/// ([`internal_abi_plan`]); `check_only` is as in [`lower_module_parts`].
fn lower_object_parts(
    module: &Module,
    level: OptLevel,
    internal_abi: bool,
    check_only: bool,
) -> Result<(Vec<u8>, Vec<String>, WasmLocalOptSummary), WasmLowerError> {
    let unit_scale_elided = runs_local_emission(level);
    let local_opt = unit_scale_elided && !check_only;
    // At O1 and above the object names its crate-private functions for the
    // debugger without their link namespace mark ([`debug_function_name`]);
    // at O0 the object carries no `name` section.
    let debug_names = level != OptLevel::O0;
    // At O1 and above identical bodies are folded ([`finish_with_body_folds`]).
    let fold_bodies = level != OptLevel::O0;
    let mut fold_eligible: HashSet<u32> = HashSet::new();
    let referenced = referenced_functions(module);
    let mut wasm = WasmModule::new_object();
    // At O1 and above the crate-internal functions use the internal ABI
    // ([`internal_abi_plan`]) unless the producer withholds `multivalue`; at
    // O0 every function keeps the C form.
    let internal_plan = if unit_scale_elided && internal_abi {
        internal_abi_plan(module)
    } else {
        HashSet::new()
    };
    let address_taken: HashSet<FuncId> = address_taken_functions(module).into_iter().collect();
    let called = directly_called_functions(module);
    let mut internal_targets: InternalTargets = HashMap::new();

    // ---- Undefined functions: every declaration, then the library calls the
    // lowering itself needs. Declarations of one name share ONE import (one
    // undefined symbol) when they agree on its wasm type and visibility;
    // disagreeing ones are refused, since the object can name the symbol once.
    // A planned declaration that is called imports its internal entry; it
    // imports its C form too only when its address is taken here, or, as any
    // other declaration, when nothing references it.
    let mut call_targets: CallTargets = HashMap::new();
    let mut foreign: HashSet<FuncId> = HashSet::new();
    let mut imported: HashMap<String, (u32, FuncType, bool)> = HashMap::new();
    let mut import_once = |wasm: &mut WasmModule,
                           name: &str,
                           ty: FuncType,
                           hidden: bool|
     -> Result<u32, WasmLowerError> {
        match imported.get(name) {
            Some((widx, prev_ty, prev_hidden)) if *prev_ty == ty && *prev_hidden == hidden => {
                Ok(*widx)
            }
            Some((_, prev_ty, prev_hidden)) => Err(WasmLowerError::ContractSurface(format!(
                "[TCG-WASM-SYMBOL] declarations of `{name}` disagree (wasm type {prev_ty:?}, \
                 hidden {prev_hidden} vs {ty:?}, hidden {hidden}); the object can import the \
                 symbol once"
            ))),
            None => {
                let type_idx = wasm.add_type(ty.clone());
                let widx =
                    wasm.add_func_import(super::encode::OBJECT_IMPORT_MODULE, name, type_idx)?;
                wasm.set_func_import_hidden(widx, hidden);
                imported.insert(name.to_owned(), (widx, ty, hidden));
                Ok(widx)
            }
        }
    };
    for func in module.functions.iter().filter(|f| is_declaration(f)) {
        if skip_unreferenced_declaration(module, func, &referenced)? {
            continue;
        }
        let hidden = import_symbol_flags(func.visibility).hidden;
        if internal_plan.contains(&func.id) && called.contains(&func.id) {
            let ty = internal_entry_sig(module, func)?.wasm;
            let widx = import_once(&mut wasm, &internal_abi_symbol(&func.name), ty, hidden)?;
            internal_targets.insert(func.id, widx);
            foreign.insert(func.id);
            if !address_taken.contains(&func.id) {
                continue;
            }
        }
        let ty = function_wasm_type(module, func)?;
        let widx = import_once(&mut wasm, &func.name, ty, hidden)?;
        call_targets.insert(func.id, widx);
        foreign.insert(func.id);
    }
    // `FRem` calls the C library's `fmod` / `fmodf` BY NAME; these two are
    // the only routines this object references by a name the module could
    // also define (`__stack_pointer` and `__indirect_function_table` are
    // linker-synthetic). A module that DECLARES the routine with its exact
    // signature is called through that declaration (the library routine).
    // A module that DEFINES a function of that name is refused whatever its
    // linkage: `frem` means trust-ir's IEEE remainder, and `wasm-ld` would
    // bind the object's reference to the module's own body, which nothing
    // here knows to compute it. A global of that name, or any other
    // signature, is refused too; otherwise the routine is imported.
    let mut helpers = Helpers::default();
    let mut named_helpers: Vec<(bool, FuncId)> = Vec::new();
    for (ty, vt, name) in [
        (Ty::F64, ValType::F64, "fmod"),
        (Ty::F32, ValType::F32, "fmodf"),
    ] {
        if !uses_frem(module, &ty) {
            continue;
        }
        let single = vt == ValType::F32;
        let routine = FuncType {
            params: vec![vt, vt],
            results: vec![vt],
        };
        if module.globals.iter().any(|g| g.name == name) {
            return Err(WasmLowerError::ContractSurface(format!(
                "global `{name}` is named like the C library routine the wasm32 object lane \
                 calls by name for `frem {ty:?}`; the object would carry a data symbol and a \
                 function symbol of one name (fail-closed)"
            )));
        }
        match module.function_by_name(name) {
            Some(f) if !is_declaration(f) => {
                let scope = if trust_cg_lower::is_module_local_function_definition(f) {
                    "module-local"
                } else {
                    "defined"
                };
                return Err(WasmLowerError::ContractSurface(format!(
                    "{scope} function `{name}` on target {} is named like the C library \
                     routine the wasm32 object lane calls by name for `frem {ty:?}`; that \
                     reference would bind to the module's body, which is not known to compute \
                     trust-ir's `frem` (fail-closed)",
                    super::target::WASM32_TRIPLE
                )));
            }
            Some(f) => {
                let is_vararg = module.func_type(f.ty).is_some_and(|ft| ft.is_vararg);
                let wasm_ty = function_wasm_type(module, f)?;
                if is_vararg || wasm_ty != routine {
                    return Err(WasmLowerError::ContractSurface(format!(
                        "function `{name}` has wasm signature {wasm_ty:?}{}, but the wasm32 \
                         object lane calls `{name}` by name for `frem {ty:?}` as the C library \
                         routine {routine:?}; refusing rather than bind `frem` to it",
                        if is_vararg { " (variadic)" } else { "" },
                    )));
                }
                named_helpers.push((single, f.id));
            }
            None => {
                let type_idx = wasm.add_type(FuncType {
                    params: vec![vt, vt],
                    results: vec![vt],
                });
                let widx =
                    wasm.add_func_import(super::encode::OBJECT_IMPORT_MODULE, name, type_idx)?;
                if single {
                    helpers.fmodf = Some(widx);
                } else {
                    helpers.fmod = Some(widx);
                }
            }
        }
    }

    // ---- Memory, stack pointer, table.
    let mut uses = Vec::new();
    for func in module.functions.iter().filter(|f| !is_declaration(f)) {
        uses.push((func, function_memory_use(func, module, &internal_plan)?));
    }
    let pool = pool_requests(module, unit_scale_elided)?;
    // A C-form entry forwarding to an internal entry writes the `sret` buffer.
    let thunks = module
        .functions
        .iter()
        .any(|f| !is_declaration(f) && internal_plan.contains(&f.id));
    if uses.iter().any(|(_, u)| u.memory || u.frame)
        || !module.globals.is_empty()
        || !pool.is_empty()
        || thunks
    {
        wasm.require_memory()?;
    }
    let sp_global = if uses.iter().any(|(_, u)| u.frame) {
        Some(wasm.add_global_import(
            super::encode::OBJECT_IMPORT_MODULE,
            super::encode::OBJECT_STACK_POINTER_IMPORT,
            ValType::I32,
            true,
        )?)
    } else {
        None
    };
    if sp_global.is_some() {
        wasm.require_feature("mutable-globals");
    }
    let import_base = wasm.func_import_count();
    let defined: Vec<&Function> = module
        .functions
        .iter()
        .filter(|f| !is_declaration(f))
        .collect();
    // A planned definition's body is its INTERNAL entry, at
    // `import_base + ordinal` like every other body; its C form is a
    // forwarding entry ([`emit_internal_abi_thunk`]) appended after the bodies
    // and the division helper, which every function pointer to it names.
    let mut next_thunk = import_base + defined.len() as u32 + u32::from(uses_wide_divmod(module));
    let mut thunk_targets: Vec<(&Function, u32)> = Vec::new();
    for (ordinal, func) in defined.iter().enumerate() {
        let body = import_base + ordinal as u32;
        if internal_plan.contains(&func.id) {
            internal_targets.insert(func.id, body);
            call_targets.insert(func.id, next_thunk);
            thunk_targets.push((func, next_thunk));
            next_thunk += 1;
        } else {
            call_targets.insert(func.id, body);
        }
        // The body emitted here need not be the one a call reaches
        // ([`interposable_linkage`]): its callers copy by-address arguments
        // as for an import, and its parameters are assumed captured.
        if interposable_linkage(func.linkage) {
            foreign.insert(func.id);
        }
    }
    for (single, fid) in named_helpers {
        let widx = call_targets.get(&fid).copied();
        if single {
            helpers.fmodf = widx;
        } else {
            helpers.fmod = widx;
        }
    }
    // The 128-bit division helper is DEFINED here, right after the trust-ir
    // functions, as a weak hidden symbol whose name is reserved and pinned to
    // the helper's text at this level
    // ([`super::helpers::divmod128_helper_name_at`]): every
    // object carries a copy and `wasm-ld` binds every call to one of them. A
    // module that itself names a reserved helper symbol was refused by
    // [`reject_reserved_helper_symbols`].
    let divmod128 = if uses_wide_divmod(module) {
        let name = super::helpers::divmod128_helper_name_at(level);
        let helper = super::helpers::divmod128_module(&name, level)?;
        helpers.divmod128 = Some(import_base + defined.len() as u32);
        Some((name, helper))
    } else {
        None
    };
    // A `call_indirect` names the table (and, relocated, needs
    // reference-types' LEB table immediate). The table import itself is also
    // derived by the encoder from every table-index relocation — a function
    // pointer in code or in static data needs the table without any indirect
    // call ([`WasmModule::object_needs_table`]).
    let any_indirect = module
        .functions
        .iter()
        .flat_map(|f| f.blocks.iter().flat_map(|b| &b.body))
        .any(|n| matches!(n.inst, Inst::CallIndirect { .. }));
    if any_indirect {
        wasm.require_table_import();
        wasm.require_feature("reference-types");
    }
    let sig_types = indirect_sig_types(module, &mut wasm)?;

    // ---- Data items: globals first (so `GlobalAddr` can name them), then
    // pooled constants. Undefined data symbols for external references are
    // appended as they are met.
    let mut global_addrs = GlobalAddrs::new();
    let mut extern_data: HashMap<String, u32> = HashMap::new();
    let mut global_items = Vec::with_capacity(module.globals.len());
    let mut data_imports: HashMap<&str, (u32, u32)> = HashMap::new();
    for (index, global) in module.globals.iter().enumerate() {
        if global.tls.is_some() {
            return Err(WasmLowerError::ContractSurface(format!(
                "global `{}` is thread-local; the wasm object lane has no TLS model",
                global.name
            )));
        }
        let is_import = global_is_import(global);
        if is_import && global.retained {
            return Err(WasmLowerError::ContractSurface(format!(
                "global `{}` is a cross-object import marked retained (trust-ir v41); it has \
                 no bytes here to retain (fail-closed)",
                global.name
            )));
        }
        let flags = if is_import {
            import_symbol_flags(global.visibility)
        } else {
            symbol_flags(global.linkage, global.visibility, global.retained)
        };
        let def = if is_import {
            None
        } else {
            let (size, align) = layout::size_align(module, &global.ty)?;
            let align = align.max(global.align.unwrap_or(1));
            Some(super::encode::DataDef {
                bytes: vec![0; size as usize],
                align,
                relocs: Vec::new(),
                readonly: !global.mutable,
            })
        };
        // Data imports of one name share one undefined symbol
        // (`reject_object_symbol_collisions` admits only that sharing).
        let shared = if is_import {
            data_imports.get(global.name.as_str()).copied()
        } else {
            None
        };
        let (item, addr) = match shared {
            Some(existing) => existing,
            None => {
                let placed = wasm.add_data_item(&global.name, flags, def)?;
                if is_import {
                    data_imports.insert(global.name.as_str(), placed);
                }
                placed
            }
        };
        global_addrs.insert(
            trust_ir::value::GlobalId::new(index as u32),
            DataAddr {
                addr,
                item: Some(item),
            },
        );
        global_items.push(item);
    }
    let mut const_pool = ConstPool::new();
    let mut pool_images = Vec::with_capacity(pool.len());
    for (k, req) in pool.iter().enumerate() {
        let image = layout::const_image(module, &req.ty, &req.constant)?;
        let (_, align) = layout::size_align(module, &req.ty)?;
        let (item, addr) = wasm.add_data_item(
            &format!("__tcg_const.{}.{k}", module.name),
            super::encode::SymbolFlags {
                local: true,
                ..Default::default()
            },
            Some(super::encode::DataDef {
                bytes: vec![0; image.bytes.len()],
                align,
                relocs: Vec::new(),
                readonly: true,
            }),
        )?;
        const_pool.insert(
            (req.func, req.value),
            DataAddr {
                addr,
                item: Some(item),
            },
        );
        pool_images.push((item, image));
    }
    // Initializer images, with pointers as relocations.
    let mut images: Vec<(u32, layout::ConstImage)> = Vec::new();
    for (index, global) in module.globals.iter().enumerate() {
        if global_is_import(global) {
            continue;
        }
        if let Some(init) = &global.initializer {
            let image = layout::const_image(module, &global.ty, init)?;
            images.push((global_items[index], image));
        }
    }
    images.extend(pool_images);
    for (item, image) in images {
        let mut relocs = Vec::new();
        for (at, r) in &image.refs {
            let (kind, target, addend) = match r {
                layout::ImageRef::Func(fid) => {
                    let widx = *call_targets.get(fid).ok_or_else(|| {
                        WasmLowerError::UnsupportedConstantData(format!(
                            "function pointer to unknown {fid:?} in static data"
                        ))
                    })?;
                    (
                        super::encode::RelocKind::TableIndexI32,
                        super::encode::RelocTarget::Func(widx),
                        0,
                    )
                }
                layout::ImageRef::Global(gid, addend) => {
                    let d = global_addrs[gid];
                    (
                        super::encode::RelocKind::MemoryAddrI32,
                        super::encode::RelocTarget::Data(d.item.unwrap_or(0)),
                        *addend as i32,
                    )
                }
                layout::ImageRef::Symbol(name, addend) => {
                    let item = match extern_data.get(name) {
                        Some(i) => *i,
                        None => {
                            let (i, _) = wasm.add_data_item(
                                name,
                                super::encode::SymbolFlags::default(),
                                None,
                            )?;
                            extern_data.insert(name.clone(), i);
                            i
                        }
                    };
                    (
                        super::encode::RelocKind::MemoryAddrI32,
                        super::encode::RelocTarget::Data(item),
                        *addend as i32,
                    )
                }
            };
            relocs.push(super::encode::Reloc {
                kind,
                offset: *at,
                target,
                addend,
            });
        }
        wasm.set_data_item_image(item, image.bytes, relocs)?;
    }

    let captures = captures::param_captures(module, &foreign);
    // Undefined data symbols a function body takes the address of join the
    // ones static data referred to above.
    for func in &defined {
        for node in func.blocks.iter().flat_map(|b| &b.body) {
            let Inst::Const {
                ty,
                value: Constant::SymbolAddr { symbol, addend },
            } = &node.inst
            else {
                continue;
            };
            if layout::scalar_valtype(ty).is_none() || extern_data.contains_key(symbol) {
                continue;
            }
            if let Ok(layout::ImageRef::Symbol(name, _)) =
                layout::resolve_symbol(module, symbol, *addend)
            {
                let (i, _) =
                    wasm.add_data_item(&name, super::encode::SymbolFlags::default(), None)?;
                extern_data.insert(name, i);
            }
        }
    }
    let extern_addrs: ExternData = extern_data
        .iter()
        .map(|(name, &item)| {
            (
                name.clone(),
                DataAddr {
                    addr: 0,
                    item: Some(item),
                },
            )
        })
        .collect();
    let env = WasmFunctionEnv {
        sp_global,
        call_targets: &call_targets,
        internal_abi: &internal_targets,
        sig_types: &sig_types,
        global_addrs: &global_addrs,
        const_pool: &const_pool,
        helpers: &helpers,
        foreign: &foreign,
        captures: &captures,
        // The linker owns the stack's placement in an object.
        stack_limit: None,
        extern_data: &extern_addrs,
        object: true,
        local_opt,
        unit_scale_elided,
        pair_carrier: unit_scale_elided,
    };
    for func in &defined {
        let idx = lower_admitted_function(
            &mut wasm,
            func,
            module,
            env,
            FunctionLicense::DecidedForModule,
        )?;
        let internal = internal_targets.get(&func.id).copied();
        let expected = internal.or_else(|| call_targets.get(&func.id).copied());
        if expected != Some(idx) {
            return Err(WasmLowerError::FunctionIndexDrift(format!(
                "`{}` was emitted as wasm function {idx}, but its call targets were computed as \
                 {expected:?} (import base {import_base})",
                func.name,
            )));
        }
        if internal.is_some() {
            // Hidden and strong like the definition, under the reserved name
            // only direct calls of this crate's objects use.
            let symbol = internal_abi_symbol(&func.name);
            wasm.set_function_symbol(
                idx,
                &symbol,
                super::encode::SymbolFlags {
                    hidden: true,
                    ..Default::default()
                },
            );
            if debug_names {
                set_debug_name(&mut wasm, idx, &symbol);
            }
        } else {
            wasm.set_function_symbol(
                idx,
                &func.name,
                symbol_flags(func.linkage, func.visibility, func.retained),
            );
            if debug_names {
                set_debug_name(&mut wasm, idx, &func.name);
            }
            fold_eligible.insert(idx);
        }
    }
    if let Some((name, helper)) = &divmod128 {
        let func = &helper.functions[0];
        // The helper calls nothing and names no data, so its body carries no
        // relocation; `object` keeps it encoded exactly as an object body.
        let helper_env = WasmFunctionEnv {
            object: true,
            local_opt,
            unit_scale_elided,
            ..WasmFunctionEnv::empty()
        };
        let idx = lower_admitted_function(
            &mut wasm,
            func,
            helper,
            helper_env,
            FunctionLicense::Decide(&lane_helper_license()),
        )?;
        if Some(idx) != helpers.divmod128 {
            return Err(WasmLowerError::FunctionIndexDrift(format!(
                "helper `{name}` was emitted as wasm function {idx}, but its calls target \
                 {:?}",
                helpers.divmod128
            )));
        }
        wasm.set_function_symbol(
            idx,
            name,
            symbol_flags(
                trust_ir::Linkage::LinkOnceOdr,
                trust_ir::Visibility::Hidden,
                false,
            ),
        );
    }
    for (func, expected) in thunk_targets {
        let internal = internal_targets[&func.id];
        let idx = emit_internal_abi_thunk(&mut wasm, module, func, internal)?;
        if idx != expected {
            return Err(WasmLowerError::FunctionIndexDrift(format!(
                "the C-form entry of `{}` was emitted as wasm function {idx}, but its function \
                 pointers name {expected}",
                func.name,
            )));
        }
        wasm.set_function_symbol(
            idx,
            &func.name,
            symbol_flags(func.linkage, func.visibility, func.retained),
        );
        if debug_names {
            set_debug_name(&mut wasm, idx, &func.name);
        }
        wasm.require_feature("multivalue");
    }
    wasm.require_feature("sign-ext");
    wasm.require_feature("nontrapping-fptoint");
    // Backstop over the symbol table as written: an object that names one
    // non-local symbol twice is malformed to every LLVM object reader.
    if let Some(name) = wasm.object_duplicate_symbol() {
        return Err(WasmLowerError::ContractSurface(format!(
            "[TCG-WASM-SYMBOL] module `{}` would give the object two non-local symbols named \
             `{name}` (a function or data symbol beside one of the same name, or beside a \
             symbol this object imports from the linker); refusing a malformed object",
            module.name
        )));
    }
    // Every signature is final: validate the emission pass's candidates.
    let mut local_opt_summary = super::opt::validate_pending(&mut wasm);
    local_opt_summary.enabled = local_opt;
    let mut contract = wasm.host_contract();
    if wasm.object_needs_table() {
        contract.push(format!(
            "table {}.{}",
            super::encode::OBJECT_IMPORT_MODULE,
            super::encode::OBJECT_TABLE_IMPORT
        ));
    }
    let bytes = if fold_bodies {
        finish_with_body_folds(&mut wasm, &fold_eligible)
    } else {
        wasm.finish()
    };
    // The ABI boundary, decided over the object's own symbol table: every
    // function with a multi-value signature is a hidden, strong, crate-private
    // internal entry only direct calls reach, its C-form entry forwards every
    // result into the `sret` buffer, and both match the trust-ir signature.
    trust_cg_verify::wasm_internal_abi::check_object_against_module(&bytes, module).map_err(
        |refusal| {
            WasmLowerError::ContractSurface(format!(
                "[TCG-WASM-INTERNAL-ABI] module `{}`: the object's ABI boundary gate refused \
                 it: {refusal}",
                module.name
            ))
        },
    )?;
    Ok((bytes, contract, local_opt_summary))
}

/// Evidence-summary schema name for [`WasmCompileEvidence`].
pub const WASM_COMPILE_EVIDENCE_SCHEMA: &str = "trust-cg.wasm_compile_evidence.v1";

/// What the P4 family-(1) CFG STRUCTURAL invariant said about the module THIS
/// compile emitted.
///
/// The checker is `trust_cg_verify::wasm_cfg_proofs::check_module_structure`: it
/// re-decodes the emitted `.wasm` bytes with its own reader and runs the spec's
/// §7.3.2 control-stack / value-stack algorithm over them. Its verdict is
/// three-valued, and the three values are kept apart here on purpose:
///
/// * `Holds` — the invariant held. It goes in [`WasmCompileEvidence::ran`].
///   **This is a NECESSARY CONDITION on the structuring, not a proof of
///   correctness**: nothing in it says the structured wasm computes what the
///   trust-ir CFG computes. Relooper bisimulation is a named RED deferral of
///   that family, and two wrong lowerings it provably cannot see ship as
///   measured blind spots. The compile's [`WasmCompileEvidence::verdict`] stays
///   [`ProofEvidenceVerdict::MissingEvidence`] and its
///   [`WasmCompileEvidence::verification_route`] stays
///   [`EvidenceStrength::NotRun`] whatever this says.
/// * `Inconclusive` — the checker met something it has no rule for and says
///   NOTHING about this module. UNCREDITED: it goes in
///   [`WasmCompileEvidence::not_run`], never in `ran`.
/// * `Refuted` — has no variant here, because it never reaches a caller: it
///   fails the compile with [`WasmLowerError::StructuralInvariantRefuted`]. A
///   refutation is not a field to be read past.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum WasmCfgStructural {
    /// The structural invariant HELD, with the counts behind it.
    Holds {
        /// Defined functions checked.
        functions: usize,
        /// Instructions decoded and given a spec typing rule.
        instructions: usize,
        /// `br` / `br_if` / `br_table` label references resolved against the
        /// rebuilt control stack.
        branch_labels_resolved: usize,
        /// `end` / `else` joins whose stack height and types were checked.
        joins_checked: usize,
        /// Structured-control scopes opened, matched and closed.
        scopes_matched: usize,
    },
    /// The checker DECLINED to speak about this module, with its reason.
    Inconclusive(String),
}

impl WasmCfgStructural {
    /// Did the invariant hold? False for `Inconclusive` — an inconclusive
    /// verdict is debt, never credit.
    pub fn holds(&self) -> bool {
        matches!(self, WasmCfgStructural::Holds { .. })
    }

    /// Canonical JSON rendering.
    pub fn to_json(&self) -> serde_json::Value {
        match self {
            WasmCfgStructural::Holds {
                functions,
                instructions,
                branch_labels_resolved,
                joins_checked,
                scopes_matched,
            } => serde_json::json!({
                "verdict": "holds",
                "means": "a NECESSARY CONDITION on the structuring — not a bisimulation, and not \
                          a proof that the emitted module computes what the trust-ir CFG computes",
                "functions": functions,
                "instructions": instructions,
                "branch_labels_resolved": branch_labels_resolved,
                "joins_checked": joins_checked,
                "scopes_matched": scopes_matched,
            }),
            WasmCfgStructural::Inconclusive(why) => serde_json::json!({
                "verdict": "inconclusive",
                "means": "the checker has no rule for something in these bytes and says NOTHING \
                          about this module; uncredited",
                "detail": why,
            }),
        }
    }
}

/// Machine-readable evidence summary for one wasm32 module compile — the
/// smallest honest analogue of the native pipeline's `ProofEvidenceSummary`
/// (WP-0, `crate::proof_evidence`): every wasm compile *names* what ran and
/// what did NOT, so absence of verification is never inferable-as-presence.
///
/// The wasm lane's assurance story today is the **differential-tested tier**:
/// the backend is exercised offline by the corpus difftest
/// (`examples/wasm_difftest.rs` + `.mjs`, interpreter vs compiled wasm) and
/// the CFG fuzzer (`examples/wasm_cfg_fuzz.rs`) — but none of that runs on
/// *this* compile, and no per-function lowering proof, translation validation,
/// or solver runs on this route at all. Per WP-0 that is reported as
/// [`EvidenceStrength::NotRun`] / verdict
/// [`ProofEvidenceVerdict::MissingEvidence`], never as an absent field.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct WasmCompileEvidence {
    /// Schema name ([`WASM_COMPILE_EVIDENCE_SCHEMA`]).
    pub schema: &'static str,
    /// Target the module was compiled for.
    pub target: &'static str,
    /// Verification verdict for this compile: always
    /// [`ProofEvidenceVerdict::MissingEvidence`] on this route.
    pub verdict: ProofEvidenceVerdict,
    /// How the lowering obligations were discharged on this compile:
    /// [`EvidenceStrength::NotRun`] — nothing verified this module's bytes.
    pub verification_route: EvidenceStrength,
    /// The assurance tier this lane belongs to: the backend is
    /// differential-tested at corpus level, offline.
    pub assurance_tier: &'static str,
    /// Named checks that DID run on this compile (fail-closed guards).
    pub ran: Vec<&'static str>,
    /// Named machinery that did NOT run on this compile.
    pub not_run: Vec<&'static str>,
    /// Number of trust-ir functions lowered into the module.
    pub function_count: usize,
    /// Size of the emitted `.wasm` module in bytes.
    pub module_size_bytes: usize,
    /// SHA-256 of the emitted module bytes, binding this (negative) evidence
    /// to the artifact it describes.
    pub module_sha256: String,
    /// Every term of the host contract, as `"<kind> <module>.<name>"`: each
    /// IMPORT the module binds (`func` / `memory` / `global`), plus each GRANT
    /// the policy took over a memory it does not own — `data <mem>[base..end)`
    /// for an active data segment written into the host's address space, and
    /// `grow <mem>` for the right to resize the host's memory.
    ///
    /// **Empty is the strong claim**: a closed module's boundary really is the
    /// module. A non-empty contract is the honest widening P2/P3 create — once
    /// a module imports host memory, a host stack base, or host functions, or
    /// writes into and resizes a memory it shares, that whole
    /// host/import/shared-memory/initialization contract joins the claimed
    /// surface, and nothing here verifies the host's half of it.
    pub host_contract: Vec<String>,
    /// The P4 family-(1) CFG STRUCTURAL invariant, run on THESE bytes by
    /// `trust_cg_verify::wasm_cfg_proofs`. See [`WasmCfgStructural`] for what a
    /// `Holds` does and does not say — it is a necessary condition on the
    /// structuring, so it does NOT move [`Self::verdict`] off
    /// [`ProofEvidenceVerdict::MissingEvidence`] or [`Self::verification_route`]
    /// off [`EvidenceStrength::NotRun`].
    pub cfg_structural: WasmCfgStructural,
    /// What the local emission pass did: functions emitted with a rewritten
    /// body that the per-segment translation validator accepted, and those
    /// that kept their baseline body, by reason. The validator compares two
    /// wasm bodies of one function (the lane's own and the rewritten one), so
    /// an accepted rewrite moves neither [`Self::verdict`] nor
    /// [`Self::verification_route`]: nothing here relates the module to the
    /// trust-ir it was lowered from. `wasm_local_emission_tv` is in
    /// [`Self::ran`] when at least one function was validated;
    /// `translation_validation` (source to wasm) stays in [`Self::not_run`],
    /// and so does `optimization_pipeline` (trust-ir optimization) unless the
    /// mid-end's output was lowered ([`Self::mid_end`]).
    pub local_emission: WasmLocalOptSummary,
    /// What the trust-ir mid-end (`trust_cg_irmid`, O1 and above) did: passes
    /// run, functions changed, rollbacks by reason, skipped functions,
    /// proof-table transport and interpreter-differential coverage, and
    /// whether its output was the module lowered. A kept rewrite passed its
    /// witness checker and the differential on the counted inputs; neither
    /// moves [`Self::verdict`] or [`Self::verification_route`]. When the
    /// output was lowered, `optimization_pipeline` moves from
    /// [`Self::not_run`] to [`Self::ran`] with `trust_ir_mid_witness_tv`
    /// (and `trust_ir_mid_interp_differential` when an input was compared).
    pub mid_end: IrmidReport,
}

/// File the mid-end's checks under `ran` when its output was lowered.
fn credit_mid_end(
    mid_end: &IrmidReport,
    ran: &mut Vec<&'static str>,
    not_run: &mut Vec<&'static str>,
) {
    if !mid_end.applied {
        return;
    }
    not_run.retain(|name| *name != "optimization_pipeline");
    ran.push("optimization_pipeline");
    ran.push("trust_ir_mid_witness_tv");
    if mid_end.tv.samples_compared > 0 {
        ran.push("trust_ir_mid_interp_differential");
    }
}

impl WasmCompileEvidence {
    /// Canonical JSON rendering (stable strings via the contract `as_str`s).
    pub fn to_json(&self) -> serde_json::Value {
        serde_json::json!({
            "schema": self.schema,
            "target": self.target,
            "verdict": self.verdict.as_str(),
            "verification_route": self.verification_route.as_str(),
            "assurance_tier": self.assurance_tier,
            "ran": self.ran,
            "not_run": self.not_run,
            "function_count": self.function_count,
            "module_size_bytes": self.module_size_bytes,
            "module_sha256": self.module_sha256,
            "host_contract": self.host_contract,
            "cfg_structural": self.cfg_structural.to_json(),
            "local_emission": self.local_emission.to_json(),
            "irmid": self.mid_end.to_json(),
        })
    }
}

/// Run the P4 CFG structural invariant over `bytes` and file the verdict.
///
/// Split out of [`compile_module_with_evidence_and_policy`] so that all THREE
/// arms are reachable from a test. The `Refuted` arm in particular cannot be
/// reached by compiling anything — the backend does not emit a structurally
/// broken module on purpose — so the only way to show that a refutation is
/// really loud, rather than a promise in a doc comment, is to hand this function
/// bytes that the family's own mutants have made wrong.
#[cfg(test)]
fn classify_cfg_structural(
    bytes: &[u8],
    ran: &mut Vec<&'static str>,
    not_run: &mut Vec<&'static str>,
) -> Result<WasmCfgStructural, WasmLowerError> {
    classify_cfg_verdict(
        trust_cg_verify::wasm_cfg_proofs::check_module_structure(bytes),
        ran,
        not_run,
    )
}

/// File the P4 CFG structural invariant's verdict on a compile's bytes:
/// `Holds` is credited, `Inconclusive` is filed under `not_run`, and
/// `Refuted` fails the compile. The verdict is computed by the caller
/// ([`CompiledParts::take_cfg_verdict`]), so bytes the mid-end screen already
/// checked are not decoded twice.
fn classify_cfg_verdict(
    verdict: trust_cg_verify::wasm_cfg_proofs::CfgVerdict,
    ran: &mut Vec<&'static str>,
    not_run: &mut Vec<&'static str>,
) -> Result<WasmCfgStructural, WasmLowerError> {
    use trust_cg_verify::wasm_cfg_proofs::CfgVerdict;
    match verdict {
        CfgVerdict::Holds(report) => {
            let t = report.totals();
            ran.push("wasm_cfg_structural_invariant");
            Ok(WasmCfgStructural::Holds {
                functions: t.functions,
                instructions: t.instructions,
                branch_labels_resolved: t.branch_labels_resolved,
                joins_checked: t.joins_checked,
                scopes_matched: t.scopes_matched,
            })
        }
        // Uncredited. It goes in `not_run`, so a module the checker could not
        // read reports as unverified rather than as verified-and-fine.
        CfgVerdict::Inconclusive(why) => {
            not_run.push("wasm_cfg_structural_invariant");
            Ok(WasmCfgStructural::Inconclusive(why.to_string()))
        }
        CfgVerdict::Refuted(violation) => Err(WasmLowerError::StructuralInvariantRefuted(
            violation.to_string(),
        )),
    }
}

/// [`compile_module`], plus the honest [`WasmCompileEvidence`] summary of what
/// ran and what did not on this compile. The bytes are identical to
/// [`compile_module`]'s.
///
/// This route additionally RUNS the P4 CFG structural invariant over the bytes
/// it just emitted (see [`WasmCompileEvidence::cfg_structural`]) and refuses the
/// compile if that invariant is refuted, so an evidence-carrying compile really
/// does carry a verdict rather than describe one. It still verifies no lowering:
/// [`WasmCompileEvidence::verdict`] stays
/// [`ProofEvidenceVerdict::MissingEvidence`].
pub fn compile_module_with_evidence(
    module: &Module,
) -> Result<(Vec<u8>, WasmCompileEvidence), WasmLowerError> {
    compile_module_with_evidence_and_policy(module, &WasmModulePolicy::closed())
}

/// [`compile_module_with_policy`], plus the honest [`WasmCompileEvidence`]
/// summary — including the [`WasmCompileEvidence::host_contract`] the policy
/// bound, which is the part of the claimed surface an island adds.
pub fn compile_module_with_evidence_and_policy(
    module: &Module,
    policy: &WasmModulePolicy,
) -> Result<(Vec<u8>, WasmCompileEvidence), WasmLowerError> {
    compile_module_with_evidence_policy_and_license(
        module,
        policy,
        &CodegenLicensePolicy::default(),
    )
}

/// [`compile_module_with_evidence_and_policy`] at an explicit optimization
/// level; the level selects both the trust-ir mid-end and the local emission
/// pass (O0 runs neither), as in [`compile_object_optimized`].
pub fn compile_module_with_evidence_and_policy_optimized(
    module: &Module,
    policy: &WasmModulePolicy,
    level: OptLevel,
) -> Result<(Vec<u8>, WasmCompileEvidence), WasmLowerError> {
    compile_module_with_evidence_policy_license_optimized(
        module,
        policy,
        &CodegenLicensePolicy::default(),
        level,
    )
}

/// [`compile_module_with_evidence_and_policy`] under the caller's
/// codegen-license policy, admitted as
/// [`compile_module_with_policy_and_license`] admits it.
pub fn compile_module_with_evidence_policy_and_license(
    module: &Module,
    policy: &WasmModulePolicy,
    license: &CodegenLicensePolicy,
) -> Result<(Vec<u8>, WasmCompileEvidence), WasmLowerError> {
    compile_module_with_evidence_policy_license_optimized(
        module,
        policy,
        license,
        DEFAULT_OPT_LEVEL,
    )
}

/// [`compile_module_with_evidence_and_policy`] under the caller's
/// codegen-license policy and at an explicit optimization level.
pub fn compile_module_with_evidence_policy_license_optimized(
    module: &Module,
    policy: &WasmModulePolicy,
    license: &CodegenLicensePolicy,
    level: OptLevel,
) -> Result<(Vec<u8>, WasmCompileEvidence), WasmLowerError> {
    compile_module_with_evidence_policy_license_options(
        module,
        policy,
        license,
        WasmOptOptions::at(level),
    )
}

/// [`compile_module_with_evidence_policy_license_optimized`] with the
/// optimizations chosen by `options`: the level, and whether the trust-ir
/// mid-end runs.
pub fn compile_module_with_evidence_policy_license_options(
    module: &Module,
    policy: &WasmModulePolicy,
    license: &CodegenLicensePolicy,
    options: WasmOptOptions,
) -> Result<(Vec<u8>, WasmCompileEvidence), WasmLowerError> {
    compile_module_evidence(module, policy, ClosedPolicyFit::AsGiven, license, options)
}

/// The closed module sized for its own static data plus a shadow stack of at
/// least [`WASM_CLOSED_MIN_STACK_BYTES`] ([`sized_closed_policy`]), with the
/// evidence, under the caller's codegen-license policy and at an explicit
/// optimization level: the CLI's `--target wasm32` route.
///
/// The policy is sized for the input. When the trust-ir mid-end's output is
/// emitted and its static data is larger (constant-table promotion moves a
/// table out of a frame into read-only data), its owned pages grow so that it
/// keeps at least the input's stack. A compile whose mid-end adds no static
/// data emits exactly [`compile_module_with_evidence_policy_license_optimized`]'s
/// bytes under `sized_closed_policy(module)`.
pub fn compile_sized_closed_module_with_evidence_license_optimized(
    module: &Module,
    license: &CodegenLicensePolicy,
    level: OptLevel,
) -> Result<(Vec<u8>, WasmCompileEvidence), WasmLowerError> {
    compile_sized_closed_module_with_evidence_license_options(
        module,
        license,
        WasmOptOptions::at(level),
    )
}

/// [`compile_sized_closed_module_with_evidence_license_optimized`] with the
/// optimizations chosen by `options`.
pub fn compile_sized_closed_module_with_evidence_license_options(
    module: &Module,
    license: &CodegenLicensePolicy,
    options: WasmOptOptions,
) -> Result<(Vec<u8>, WasmCompileEvidence), WasmLowerError> {
    let policy = sized_closed_policy(module)?;
    compile_module_evidence(
        module,
        &policy,
        ClosedPolicyFit::SizedForEmitted,
        license,
        options,
    )
}

/// The [`WasmCompileEvidence::not_run`] entry of a module compiled under a
/// named Box validity assumption (trust-ir v74 `Inst::BoxDeref` admitted at
/// the license's opt-in floor): nothing established that validity.
pub const BOX_VALIDITY_NOT_ESTABLISHED: &str = "box_validity_establishment";

/// The closed-module evidence entries' shared body.
fn compile_module_evidence(
    module: &Module,
    policy: &WasmModulePolicy,
    fit: ClosedPolicyFit,
    license: &CodegenLicensePolicy,
    options: WasmOptOptions,
) -> Result<(Vec<u8>, WasmCompileEvidence), WasmLowerError> {
    let mut parts = compile_module_parts(module, policy, fit, license, options)?;
    let cfg_verdict = parts.take_cfg_verdict();
    let CompiledParts {
        bytes,
        host_contract,
        local_emission,
        mid_end,
        ..
    } = parts;

    // THE PER-COMPILE ARTIFACT of P4 family (1). The checker is given only the
    // BYTES this compile just emitted, and rebuilds its judgement from them with
    // its own decoder and the spec's §7.3.2 algorithm — it shares no code with
    // `encode.rs`, which is what keeps it evidence rather than a restatement.
    //
    // Three-valued, and all three land somewhere a reader can see:
    //   Refuted      -> the compile FAILS, loudly, right here.
    //   Inconclusive -> `not_run`, uncredited, with the reason kept.
    //   Holds        -> `ran`, with its counts — and NOTHING ELSE MOVES. The
    //                   verdict stays MissingEvidence and the route stays
    //                   NotRun, because a structural invariant holding is a
    //                   necessary condition on the structuring, not a proof
    //                   that this module computes what the trust-ir CFG does.
    let mut ran = vec![
        "wasm32_target_info_guard",
        "trust_ir_codegen_admission",
        "codegen_license",
        "calling_convention_guard",
        "multi_result_call_guard",
        "eh_instruction_reject_scan",
        "cfg_structuring",
        "import_index_space_guard",
        "memory_policy_guard",
        "stack_base_policy_guard",
        "module_encoding",
    ];
    let mut not_run = vec![
        "per_function_lowering_proofs",
        "translation_validation",
        "solver_verification",
        "per_module_differential_execution",
        "optimization_pipeline",
        // Nothing here checks the HOST's half of `host_contract`: that the
        // memory it supplies is the one the island was told about, or that
        // the stack base names a region only this island may touch.
        "host_contract_verification",
    ];
    // trust-ir v74: a module holding an `Inst::BoxDeref` compiled only
    // because the license opted below the refusing default: the
    // named-premise floor, whose Box validity is ASSUMED (the assumptions
    // are in the license's `BoxDerefDisclosure`), or this backend's
    // locally re-derived floor, a consumer-side analysis that is not proof
    // evidence. Either way validity is not ESTABLISHED by any check here.
    if trust_cg_lower::box_deref::module_has_box_deref(module) {
        not_run.push(BOX_VALIDITY_NOT_ESTABLISHED);
    }
    if local_emission.optimized > 0 {
        ran.push("wasm_local_emission_tv");
    }
    credit_mid_end(&mid_end, &mut ran, &mut not_run);
    let cfg_structural = classify_cfg_verdict(cfg_verdict, &mut ran, &mut not_run)?;

    let evidence = WasmCompileEvidence {
        schema: WASM_COMPILE_EVIDENCE_SCHEMA,
        target: super::target::WASM32_TRIPLE,
        verdict: ProofEvidenceVerdict::MissingEvidence,
        verification_route: EvidenceStrength::NotRun,
        assurance_tier: "differential-tested (offline corpus difftest + CFG fuzzer; not run on \
                         this compile). The one check that DOES run on this compile is the P4 \
                         CFG structural invariant, a necessary condition on the structuring — \
                         see `cfg_structural`; it verifies no lowering",
        ran,
        not_run,
        function_count: module.functions.len(),
        module_size_bytes: bytes.len(),
        module_sha256: crate::jit_diagnostics::sha256_hex(&bytes),
        host_contract,
        cfg_structural,
        local_emission,
        mid_end,
    };
    Ok((bytes, evidence))
}

#[cfg(test)]
mod tests {
    use super::*;
    use trust_ir::{ICmpOp, Ty};
    use trust_ir_build::ModuleBuilder;

    /// This file's fixtures are hand-built and carry no codegen license
    /// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
    /// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
    /// them passes because it was silently refused.
    fn permit_unlicensed() -> crate::CodegenLicensePolicy {
        crate::CodegenLicensePolicy::default().with_unlicensed(crate::UnlicensedBodyPolicy::Permit)
    }

    /// The debug name drops each crate-private mark that ends the name or a
    /// `.`-separated part of it, then an internal-entry suffix; a mark that
    /// is not followed by exactly 16 lowercase hex digits, or begins the
    /// name, stays, and a name without a mark has no debug name.
    #[test]
    fn debug_function_names_drop_only_well_formed_crate_marks() {
        const TAG: &str = "0123456789abcdef";
        for (symbol, want) in [
            (format!("f.tcg.crate.{TAG}"), Some("f".to_string())),
            (format!("f.tcg.crate.{TAG}.tcg.mv"), Some("f".to_string())),
            (
                format!("f.tcg.ap00c0ffee.tcg.crate.{TAG}"),
                Some("f.tcg.ap00c0ffee".to_string()),
            ),
            (
                format!("f.tcg.ap00c0ffee.tcg.crate.{TAG}.tcg.mv"),
                Some("f.tcg.ap00c0ffee".to_string()),
            ),
            ("f".to_string(), None),
            ("f.tcg.mv".to_string(), None),
            ("__tcg_divmod128_7b90c2514708d153".to_string(), None),
            (format!(".tcg.crate.{TAG}"), None),
            ("f.tcg.crate.0123456789ABCDEF".to_string(), None),
            ("f.tcg.crate.0123456789abcde".to_string(), None),
            (format!("f.tcg.crate.{TAG}0"), None),
            (format!("f.tcg.crate.{TAG}x"), None),
        ] {
            assert_eq!(debug_function_name(&symbol), want, "{symbol}");
        }
    }

    fn assert_wasm_header(bytes: &[u8]) {
        assert!(bytes.len() > 8, "module too short: {}", bytes.len());
        assert_eq!(
            &bytes[..8],
            &[0x00, 0x61, 0x73, 0x6d, 0x01, 0x00, 0x00, 0x00]
        );
    }

    /// Stamp the canonical wasm32 target info — the `compile_module`
    /// accepted-input guard refuses target-free modules.
    fn wasm32(mut module: Module) -> Module {
        module.target_info = Some(crate::wasm::target::wasm32_target_info());
        module
    }

    fn binop_module(name: &str, ty: Ty, op: BinOp) -> Module {
        let mut mb = ModuleBuilder::new("m");
        let ft = mb.add_func_type(vec![ty.clone(), ty.clone()], vec![ty.clone()]);
        let mut fb = mb.function(name, ft);
        let entry = fb.create_block();
        let a = fb.add_block_param(entry, ty.clone());
        let b = fb.add_block_param(entry, ty.clone());
        fb.switch_to_block(entry);
        let r = fb.binop(op, ty, a, b);
        fb.ret(vec![r]);
        fb.build();
        wasm32(mb.build().expect("ModuleBuilder::build: test fixture"))
    }

    #[test]
    fn lowers_straight_line_arithmetic() {
        for (ty, op) in [(Ty::I32, BinOp::Add), (Ty::I64, BinOp::Mul)] {
            assert_wasm_header(
                &compile_module_with_license(&binop_module("f", ty, op), &permit_unlicensed())
                    .unwrap(),
            );
        }
    }

    #[test]
    fn lowers_division() {
        for (ty, op) in [
            (Ty::I32, BinOp::SDiv),
            (Ty::I32, BinOp::UDiv),
            (Ty::I32, BinOp::SRem),
            (Ty::I32, BinOp::URem),
            (Ty::I64, BinOp::SDiv),
            (Ty::I64, BinOp::URem),
        ] {
            assert_wasm_header(
                &compile_module_with_license(&binop_module("f", ty, op), &permit_unlicensed())
                    .unwrap(),
            );
        }
    }

    #[test]
    fn lowers_const() {
        let mut mb = ModuleBuilder::new("m");
        let ft = mb.add_func_type(vec![], vec![Ty::I32]);
        let mut fb = mb.function("seven", ft);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        let c = fb.iconst(Ty::I32, 7);
        fb.ret(vec![c]);
        fb.build();
        assert_wasm_header(
            &compile_module_with_license(
                &wasm32(mb.build().expect("ModuleBuilder::build: test fixture")),
                &permit_unlicensed(),
            )
            .unwrap(),
        );
    }

    /// A `Bool` constant is `Constant::Bool`. An integer at `Bool` is
    /// ill-typed — the 1-bit carrier would silently mask an out-of-range one
    /// (`const bool 2` read back as `false`) — and TrustIR's typed admission
    /// refuses every integer spelling, 0 and 1 included, before this lane.
    #[test]
    fn refuses_an_out_of_range_bool_constant() {
        let module = |value: Constant| {
            let mut mb = ModuleBuilder::new("m");
            let ft = mb.add_func_type(vec![], vec![Ty::Bool]);
            let mut fb = mb.function("b", ft);
            let entry = fb.create_block();
            fb.switch_to_block(entry);
            let c = fb.const_value(Ty::Bool, value);
            fb.ret(vec![c]);
            fb.build();
            wasm32(mb.build().expect("ModuleBuilder::build: test fixture"))
        };
        for value in [false, true] {
            let bytes =
                compile_module_with_license(&module(Constant::Bool(value)), &permit_unlicensed())
                    .unwrap_or_else(|e| panic!("const bool {value} must lower: {e}"));
            assert_wasm_header(&bytes);
        }
        for value in [0, 1, 2, -1] {
            let e =
                compile_module_with_license(&module(Constant::Int(value)), &permit_unlicensed())
                    .expect_err("an integer at Bool must be refused");
            assert!(
                e.to_string().ends_with(
                    "trust-ir codegen admission refused the module: function 'b' bb0: \
                     const type mismatch: expected bool, got int"
                ),
                "const bool {value}: {e}"
            );
        }
    }

    /// max(a, b) = if a >= b { a } else { b } — an if/else diamond (merge join).
    #[test]
    fn lowers_if_else_diamond() {
        let mut mb = ModuleBuilder::new("m");
        let ft = mb.add_func_type(vec![Ty::I32, Ty::I32], vec![Ty::I32]);
        let mut fb = mb.function("max", ft);
        let entry = fb.create_block();
        let then_b = fb.create_block();
        let else_b = fb.create_block();
        let join = fb.create_block();
        let r = fb.add_block_param(join, Ty::I32);
        let a = fb.add_block_param(entry, Ty::I32);
        let b = fb.add_block_param(entry, Ty::I32);
        fb.switch_to_block(entry);
        let cond = fb.icmp(ICmpOp::Sge, Ty::I32, a, b);
        fb.condbr(cond, then_b, vec![], else_b, vec![]);
        fb.switch_to_block(then_b);
        fb.br(join, vec![a]);
        fb.switch_to_block(else_b);
        fb.br(join, vec![b]);
        fb.switch_to_block(join);
        fb.ret(vec![r]);
        fb.build();
        assert_wasm_header(
            &compile_module_with_license(
                &wasm32(mb.build().expect("ModuleBuilder::build: test fixture")),
                &permit_unlicensed(),
            )
            .unwrap(),
        );
    }

    /// sum_to(n,acc,i,step): while i<=n { acc+=i; i+=step } ; return acc.
    #[test]
    fn lowers_counting_loop() {
        let bytes = compile_module_with_license(&sum_to_module(), &permit_unlicensed()).unwrap();
        assert_wasm_header(&bytes);
    }

    fn sum_to_module() -> Module {
        let mut mb = ModuleBuilder::new("m");
        let ft = mb.add_func_type(vec![Ty::I32, Ty::I32, Ty::I32, Ty::I32], vec![Ty::I32]);
        let mut fb = mb.function("sum_to", ft);
        let entry = fb.create_block();
        let header = fb.create_block();
        let body = fb.create_block();
        let exit = fb.create_block();
        let acc = fb.add_block_param(header, Ty::I32);
        let i = fb.add_block_param(header, Ty::I32);
        let bacc = fb.add_block_param(body, Ty::I32);
        let bi = fb.add_block_param(body, Ty::I32);
        let racc = fb.add_block_param(exit, Ty::I32);
        let n = fb.add_block_param(entry, Ty::I32);
        let acc0 = fb.add_block_param(entry, Ty::I32);
        let i0 = fb.add_block_param(entry, Ty::I32);
        let step = fb.add_block_param(entry, Ty::I32);
        fb.switch_to_block(entry);
        fb.br(header, vec![acc0, i0]);
        fb.switch_to_block(header);
        let c = fb.icmp(ICmpOp::Sle, Ty::I32, i, n);
        fb.condbr(c, body, vec![acc, i], exit, vec![acc]);
        fb.switch_to_block(body);
        let nacc = fb.add(Ty::I32, bacc, bi);
        let ni = fb.add(Ty::I32, bi, step);
        fb.br(header, vec![nacc, ni]); // back-edge
        fb.switch_to_block(exit);
        fb.ret(vec![racc]);
        fb.build();
        wasm32(mb.build().expect("ModuleBuilder::build: test fixture"))
    }

    /// Irreducible: entry → {A,B}; A↔B mutually branch (two loop entries).
    /// Lowered as a dispatch loop, which the structural invariant accepts.
    #[test]
    fn lowers_irreducible_loop_as_a_dispatch_loop() {
        let mut mb = ModuleBuilder::new("m");
        // Bool branch conditions: trust-ir refuses an `i32` CondBr condition
        // (`CondBrRequiresBool`) before this lane's own control-flow refusal
        // would be reached (WS7.3 ingestion admission).
        let ft = mb.add_func_type(vec![Ty::Bool, Ty::Bool, Ty::I32], vec![Ty::I32]);
        let mut fb = mb.function("irr", ft);
        let entry = fb.create_block();
        let a = fb.create_block();
        let b = fb.create_block();
        let exit = fb.create_block();
        let p = fb.add_block_param(entry, Ty::Bool);
        let q = fb.add_block_param(entry, Ty::Bool);
        let r = fb.add_block_param(entry, Ty::I32);
        fb.switch_to_block(entry);
        fb.condbr(p, a, vec![], b, vec![]);
        fb.switch_to_block(a);
        fb.br(b, vec![]); // A -> B
        fb.switch_to_block(b);
        fb.condbr(q, a, vec![], exit, vec![]); // B -> A (back) and B -> exit
        fb.switch_to_block(exit);
        fb.ret(vec![r]);
        fb.build();
        let module = wasm32(mb.build().expect("ModuleBuilder::build: test fixture"));
        let bytes = compile_module_with_license(&module, &permit_unlicensed())
            .expect("an irreducible CFG lowers");
        assert_wasm_header(&bytes);
        let (evidence_bytes, evidence) = compile_module_with_evidence_policy_and_license(
            &module,
            &WasmModulePolicy::closed(),
            &permit_unlicensed(),
        )
        .expect("evidence");
        assert_eq!(evidence_bytes, bytes);
        assert!(
            evidence.cfg_structural.holds(),
            "{:?}",
            evidence.cfg_structural
        );
        assert!(evidence.ran.contains(&"cfg_structuring"));
    }

    /// switch v { 0 => a, 1 => b, _ => c } — a Switch compare-cascade.
    #[test]
    fn lowers_switch() {
        use trust_ir::SwitchCase;
        let mut mb = ModuleBuilder::new("m");
        let ft = mb.add_func_type(vec![Ty::I32; 4], vec![Ty::I32]);
        let mut fb = mb.function("pick", ft);
        let entry = fb.create_block();
        let c0 = fb.create_block();
        let c1 = fb.create_block();
        let def = fb.create_block();
        let join = fb.create_block();
        let r = fb.add_block_param(join, Ty::I32);
        let v = fb.add_block_param(entry, Ty::I32);
        let a = fb.add_block_param(entry, Ty::I32);
        let b = fb.add_block_param(entry, Ty::I32);
        let c = fb.add_block_param(entry, Ty::I32);
        fb.switch_to_block(entry);
        fb.switch(
            v,
            vec![
                SwitchCase {
                    value: Constant::Int(0),
                    target: c0,
                    args: vec![],
                },
                SwitchCase {
                    value: Constant::Int(1),
                    target: c1,
                    args: vec![],
                },
            ],
            def,
            vec![],
        );
        fb.switch_to_block(c0);
        fb.br(join, vec![a]);
        fb.switch_to_block(c1);
        fb.br(join, vec![b]);
        fb.switch_to_block(def);
        fb.br(join, vec![c]);
        fb.switch_to_block(join);
        fb.ret(vec![r]);
        fb.build();
        assert_wasm_header(
            &compile_module_with_license(
                &wasm32(mb.build().expect("ModuleBuilder::build: test fixture")),
                &permit_unlicensed(),
            )
            .unwrap(),
        );
    }

    /// roundtrip(x) = { let c = alloca i32; *c = x; *c } — alloca/store/load.
    #[test]
    fn lowers_alloca_store_load() {
        let mut mb = ModuleBuilder::new("m");
        let ft = mb.add_func_type(vec![Ty::I32], vec![Ty::I32]);
        let mut fb = mb.function("roundtrip", ft);
        let entry = fb.create_block();
        let x = fb.add_block_param(entry, Ty::I32);
        fb.switch_to_block(entry);
        let cell = fb.alloca(Ty::I32);
        fb.store(Ty::I32, cell, x);
        let r = fb.load(Ty::I32, cell);
        fb.ret(vec![r]);
        fb.build();
        // The mid-end would forward the store to the load and remove the
        // slot; this test is about the lane's frame, so it lowers the module
        // as given.
        let (bytes, _) = compile_module_with_evidence_policy_license_options(
            &wasm32(mb.build().expect("ModuleBuilder::build: test fixture")),
            &WasmModulePolicy::closed(),
            &permit_unlicensed(),
            WasmOptOptions {
                level: DEFAULT_OPT_LEVEL,
                mid_end: false,
            },
        )
        .unwrap();
        assert_wasm_header(&bytes);
        // Memory section (id 5) must be present.
        assert!(bytes.contains(&0x05), "expected a memory section");
    }

    /// add3(a,b,c) = addtwo(addtwo(a,b), c) — direct calls, chained.
    #[test]
    fn lowers_direct_call() {
        let mut mb = ModuleBuilder::new("m");
        let ft2 = mb.add_func_type(vec![Ty::I32, Ty::I32], vec![Ty::I32]);
        let addtwo_id = {
            let mut fb = mb.function("addtwo", ft2);
            let e = fb.create_block();
            let a = fb.add_block_param(e, Ty::I32);
            let b = fb.add_block_param(e, Ty::I32);
            fb.switch_to_block(e);
            let r = fb.add(Ty::I32, a, b);
            fb.ret(vec![r]);
            fb.build()
        };
        let ft3 = mb.add_func_type(vec![Ty::I32, Ty::I32, Ty::I32], vec![Ty::I32]);
        let mut fb = mb.function("add3", ft3);
        let e = fb.create_block();
        let a = fb.add_block_param(e, Ty::I32);
        let b = fb.add_block_param(e, Ty::I32);
        let c = fb.add_block_param(e, Ty::I32);
        fb.switch_to_block(e);
        let ab = fb.call(addtwo_id, vec![a, b]);
        let abc = fb.call(addtwo_id, vec![ab, c]);
        fb.ret(vec![abc]);
        fb.build();
        assert_wasm_header(
            &compile_module_with_license(
                &wasm32(mb.build().expect("ModuleBuilder::build: test fixture")),
                &permit_unlicensed(),
            )
            .unwrap(),
        );
    }

    /// set_get(i, x) = { let buf: [i32;4]; buf[i] = x; buf[i] } — array GEP.
    #[test]
    fn lowers_array_gep() {
        let mut mb = ModuleBuilder::new("m");
        let elem = mb.add_type(Ty::I32);
        let ft = mb.add_func_type(vec![Ty::I32, Ty::I32], vec![Ty::I32]);
        let mut fb = mb.function("set_get", ft);
        let e = fb.create_block();
        let i = fb.add_block_param(e, Ty::I32);
        let x = fb.add_block_param(e, Ty::I32);
        fb.switch_to_block(e);
        let buf = fb.alloca(Ty::Array(elem, 4));
        let p = fb.gep(Ty::I32, buf, vec![i]);
        fb.store(Ty::I32, p, x);
        let p2 = fb.gep(Ty::I32, buf, vec![i]);
        let r = fb.load(Ty::I32, p2);
        fb.ret(vec![r]);
        fb.build();
        let bytes = compile_module_with_license(
            &wasm32(mb.build().expect("ModuleBuilder::build: test fixture")),
            &permit_unlicensed(),
        )
        .unwrap();
        assert_wasm_header(&bytes);
    }

    /// pair_sum(x,y): Pair{a@0,b@4}; p.a=x; p.b=y; p.a+p.b — explicit field byte offsets.
    #[test]
    fn lowers_explicit_struct_field_offsets() {
        use trust_ir::StructId;
        use trust_ir::ty::{FieldDef, StructDef};
        let mut mb = ModuleBuilder::new("m");
        let sid = mb.add_struct(StructDef {
            origin: None,
            id: StructId::new(0),
            name: "Pair".to_string(),
            fields: vec![
                FieldDef {
                    name: "a".to_string(),
                    ty: Ty::I32,
                    offset: Some(0),
                },
                FieldDef {
                    name: "b".to_string(),
                    ty: Ty::I32,
                    offset: Some(4),
                },
            ],
            size: Some(8),
            align: Some(4),
            repr: Default::default(),
        });
        let ft = mb.add_func_type(vec![Ty::I32, Ty::I32], vec![Ty::I32]);
        let mut fb = mb.function("pair_sum", ft);
        let e = fb.create_block();
        let x = fb.add_block_param(e, Ty::I32);
        let y = fb.add_block_param(e, Ty::I32);
        fb.switch_to_block(e);
        let buf = fb.alloca(Ty::Struct(sid));
        let f0 = fb.iconst(Ty::I32, 0);
        let f1 = fb.iconst(Ty::I32, 4);
        let pa = fb.gep(Ty::U8, buf, vec![f0]);
        fb.store(Ty::I32, pa, x);
        let pb = fb.gep(Ty::U8, buf, vec![f1]);
        fb.store(Ty::I32, pb, y);
        let qa = fb.gep(Ty::U8, buf, vec![f0]);
        let va = fb.load(Ty::I32, qa);
        let qb = fb.gep(Ty::U8, buf, vec![f1]);
        let vb = fb.load(Ty::I32, qb);
        let s = fb.add(Ty::I32, va, vb);
        fb.ret(vec![s]);
        fb.build();
        assert_wasm_header(
            &compile_module_with_license(
                &wasm32(mb.build().expect("ModuleBuilder::build: test fixture")),
                &permit_unlicensed(),
            )
            .unwrap(),
        );
    }

    /// dispatch(x,y) = (*fn_ptr(imul))(x,y) — indirect call through the table.
    #[test]
    fn lowers_indirect_call() {
        let mut mb = ModuleBuilder::new("m");
        let ft2 = mb.add_func_type(vec![Ty::I32, Ty::I32], vec![Ty::I32]);
        let imul_id = {
            let mut fb = mb.function("imul", ft2);
            let e = fb.create_block();
            let a = fb.add_block_param(e, Ty::I32);
            let b = fb.add_block_param(e, Ty::I32);
            fb.switch_to_block(e);
            let r = fb.mul(Ty::I32, a, b);
            fb.ret(vec![r]);
            fb.build()
        };
        let mut fb = mb.function("dispatch", ft2);
        let e = fb.create_block();
        let x = fb.add_block_param(e, Ty::I32);
        let y = fb.add_block_param(e, Ty::I32);
        fb.switch_to_block(e);
        let fp = fb.fn_addr(ft2, imul_id);
        let r = fb.call_indirect(fp, ft2, vec![x, y]);
        fb.ret(vec![r]);
        fb.build();
        assert_wasm_header(
            &compile_module_with_license(
                &wasm32(mb.build().expect("ModuleBuilder::build: test fixture")),
                &permit_unlicensed(),
            )
            .unwrap(),
        );
    }

    /// Float remainder has no wasm opcode: a closed module carries the
    /// trust-ir `fmod` helper, appended after the trust-ir functions.
    #[test]
    fn lowers_frem_through_the_fmod_helper() {
        for ty in [Ty::F32, Ty::F64] {
            let bytes = compile_module_with_license(
                &binop_module("d", ty, BinOp::FRem),
                &permit_unlicensed(),
            )
            .unwrap();
            assert_wasm_header(&bytes);
        }
    }

    /// 128-bit division calls the module's one division helper: a closed
    /// module with all four operations carries exactly one function beyond
    /// its own, and a function lowered without a provisioned helper fails
    /// closed instead of calling nothing.
    #[test]
    fn wide_division_calls_the_one_provisioned_helper() {
        for ty in [Ty::U128, Ty::I128] {
            for op in [BinOp::UDiv, BinOp::URem, BinOp::SDiv, BinOp::SRem] {
                let module = binop_module("d", ty.clone(), op);
                let bytes = compile_module_with_license(&module, &permit_unlicensed()).unwrap();
                assert_wasm_header(&bytes);
                let bodies =
                    wasmparser::Parser::new(0)
                        .parse_all(&bytes)
                        .find_map(|p| match p.unwrap() {
                            wasmparser::Payload::CodeSectionStart { count, .. } => Some(count),
                            _ => None,
                        });
                assert_eq!(
                    bodies,
                    Some(2),
                    "{ty:?} {op:?}: the function and ONE helper"
                );

                let mut wasm = WasmModule::new();
                wasm.require_memory().unwrap();
                let sp = wasm
                    .add_global(ValType::I32, true, GlobalInit::I32(65536))
                    .unwrap();
                let env = WasmFunctionEnv {
                    sp_global: Some(sp),
                    ..WasmFunctionEnv::empty()
                };
                let err = lower_function_with_license(
                    &mut wasm,
                    &module.functions[0],
                    &module,
                    env,
                    &permit_unlicensed(),
                )
                .expect_err("no helper provisioned");
                assert!(
                    matches!(&err, WasmLowerError::UnsupportedInst(m)
                        if m.contains("no 128-bit division helper")),
                    "{ty:?} {op:?}: {err}"
                );
            }
        }
    }

    /// A type with no wasm32 carrier still fails closed.
    #[test]
    fn rejects_unsupported_binop() {
        let err = compile_module_with_license(
            &binop_module("d", Ty::F16, BinOp::FAdd),
            &permit_unlicensed(),
        )
        .unwrap_err();
        assert!(matches!(err, WasmLowerError::UnsupportedType(_)), "{err}");
    }

    #[test]
    fn rejects_exception_handling_instructions_fail_closed() {
        use trust_ir::{
            Block as TrustIrBlock, FuncId, FuncTy, Function as TrustIrFunction, InstrNode, ValueId,
        };

        let make_module = |name: &str, blocks: Vec<TrustIrBlock>| {
            let mut module = Module::new(name);
            let ty = module
                .add_func_type(FuncTy {
                    params: vec![],
                    returns: vec![],
                    abi: None,
                    is_vararg: false,
                })
                .expect("Module::add_func_type: test fixture");
            let mut func = TrustIrFunction::new(FuncId::new(0), name, ty, BlockId::new(0));
            func.blocks = blocks;
            module
                .try_add_function(func)
                .expect("Module::try_add_function: test fixture");
            wasm32(module)
        };

        let invoke = make_module(
            "wasm_reject_invoke",
            vec![
                TrustIrBlock {
                    id: BlockId::new(0),
                    params: vec![],
                    body: vec![InstrNode::new(Inst::Invoke {
                        callee: FuncId::new(0),
                        args: vec![],
                        normal_dest: BlockId::new(1),
                        normal_args: vec![],
                        unwind_dest: BlockId::new(2),
                    })],
                },
                TrustIrBlock {
                    id: BlockId::new(1),
                    params: vec![],
                    body: vec![InstrNode::new(Inst::Return { values: vec![] })],
                },
                // The unwind edge enters a landing pad that re-raises: a
                // well-formed EH region (trust-ir refuses an unwind edge into
                // a non-pad block, `UnwindDestWithoutLandingPad`), so the
                // refusal below is this lane's own.
                TrustIrBlock {
                    id: BlockId::new(2),
                    params: vec![],
                    body: vec![
                        InstrNode::new(Inst::LandingPad {
                            is_cleanup: true,
                            catch_type_indices: vec![],
                        })
                        .with_results(vec![ValueId::new(0), ValueId::new(1)]),
                        InstrNode::new(Inst::Resume {
                            exn: ValueId::new(0),
                        }),
                    ],
                },
            ],
        );
        let err = compile_module_with_license(&invoke, &permit_unlicensed())
            .expect_err("Wasm has no EH instruction lowering");
        assert!(matches!(err, WasmLowerError::UnsupportedInst(_)), "{err}");
        assert!(err.to_string().contains("Invoke"), "{err}");

        // A `Resume` or `LandingPad` outside a well-formed invoke region is
        // malformed trust-ir (`MisplacedLandingPad`): since WS7.3 ingestion
        // admission refuses it before this lane's EH scan is reached.
        let malformed_eh = |module: &Module, what: &str| {
            let err = compile_module_with_license(module, &permit_unlicensed()).expect_err(what);
            match &err {
                WasmLowerError::InvalidTrustIr(refusal) => assert!(
                    refusal.any(|finding| matches!(
                        finding,
                        trust_ir_build::ValidationError::MisplacedLandingPad { .. }
                    )),
                    "{what}: {err}"
                ),
                other => panic!("{what}: expected the admission refusal, got {other}"),
            }
        };

        let resume = make_module(
            "wasm_reject_resume",
            vec![TrustIrBlock {
                id: BlockId::new(0),
                params: vec![],
                body: vec![InstrNode::new(Inst::Resume {
                    exn: ValueId::new(0),
                })],
            }],
        );
        malformed_eh(&resume, "a resume no landing pad produced");

        let landing_pad = make_module(
            "wasm_reject_landing_pad",
            vec![TrustIrBlock {
                id: BlockId::new(0),
                params: vec![],
                body: vec![
                    InstrNode::new(Inst::LandingPad {
                        is_cleanup: true,
                        catch_type_indices: vec![],
                    })
                    .with_results(vec![ValueId::new(0), ValueId::new(1)]),
                    InstrNode::new(Inst::Return { values: vec![] }),
                ],
            }],
        );
        malformed_eh(&landing_pad, "a landing pad heading the entry block");

        let unreachable_zero_result_pad = make_module(
            "wasm_reject_unreachable_landing_pad",
            vec![
                TrustIrBlock {
                    id: BlockId::new(0),
                    params: vec![],
                    body: vec![InstrNode::new(Inst::Return { values: vec![] })],
                },
                TrustIrBlock {
                    id: BlockId::new(1),
                    params: vec![],
                    body: vec![
                        InstrNode::new(Inst::LandingPad {
                            is_cleanup: true,
                            catch_type_indices: vec![],
                        }),
                        InstrNode::new(Inst::Return { values: vec![] }),
                    ],
                },
            ],
        );
        let err = compile_module_with_license(&unreachable_zero_result_pad, &permit_unlicensed())
            .expect_err("an unreachable zero-result landing pad is refused");
        assert!(matches!(err, WasmLowerError::InvalidTrustIr(_)), "{err}");
    }

    /// Cross-check the backend's actual opcode emission against the
    /// proof-validated source-of-truth decode in trust-cg-verify. Closes the gap
    /// the refinement proofs (which hand-mirror the table) cannot: if
    /// `int_binop_opcode` ever emits the wrong opcode for a `BinOp`, the byte
    /// decodes to the wrong `WasmAluOp` and THIS unit test fails — so a backend
    /// opcode bug is caught by a test, not only by execution.
    #[test]
    fn backend_opcodes_match_proven_semantics() {
        use trust_cg_verify::wasm_semantics::{WasmAluOp, decode_int_binop};
        let cases = [
            (BinOp::Add, WasmAluOp::Add),
            (BinOp::Sub, WasmAluOp::Sub),
            (BinOp::Mul, WasmAluOp::Mul),
            (BinOp::SDiv, WasmAluOp::DivS),
            (BinOp::UDiv, WasmAluOp::DivU),
            (BinOp::SRem, WasmAluOp::RemS),
            (BinOp::URem, WasmAluOp::RemU),
            (BinOp::And, WasmAluOp::And),
            (BinOp::Or, WasmAluOp::Or),
            (BinOp::Xor, WasmAluOp::Xor),
            (BinOp::Shl, WasmAluOp::Shl),
            (BinOp::AShr, WasmAluOp::ShrS),
            (BinOp::LShr, WasmAluOp::ShrU),
        ];
        for (binop, expected) in cases {
            for vt in [ValType::I32, ValType::I64] {
                let byte = int_binop_opcode(binop, vt)
                    .unwrap_or_else(|e| panic!("{binop:?}/{vt:?} should lower: {e}"));
                assert_eq!(
                    decode_int_binop(byte),
                    Some(expected),
                    "backend emits {byte:#x} for {binop:?}/{vt:?} — decodes to {:?}, not {expected:?}",
                    decode_int_binop(byte),
                );
            }
        }
    }

    // -----------------------------------------------------------------------
    // P3 — the value domain: narrow legalization, sub-word memory, br_table.
    // -----------------------------------------------------------------------

    /// Invariant N, as arithmetic: a narrow value's i32 carrier is its low
    /// `bits` sign-extended (signed types) or zero-extended (unsigned ones).
    #[test]
    fn a_narrow_constant_is_canonicalized_into_its_carrier() {
        let cases: &[(Ty, i128, i64)] = &[
            (Ty::U8, 200, 200),
            (Ty::U8, 300, 44),  // wraps to 8 bits
            (Ty::U8, -1, 255),  // two's complement, zero-extended
            (Ty::I8, 200, -56), // 0xC8 read as i8
            (Ty::I8, -1, -1),   // sign-extended
            (Ty::I8, 127, 127),
            (Ty::U16, -1, 65535),
            (Ty::I16, 40000, -25536),
            (Ty::I32, -1, -1),
            (Ty::U32, -1, 4294967295),
            (Ty::I64, -1, -1),
            (Ty::Bool, 3, 1),
        ];
        for (ty, value, expected) in cases {
            let repr = int_repr_of(ty).unwrap_or_else(|| panic!("{ty:?} has an int repr"));
            assert_eq!(
                repr.carrier_value(*value),
                *expected,
                "{ty:?} carrier of {value}",
            );
        }
        // Only the four sub-word integer types take the arithmetic narrow path.
        for ty in [Ty::I8, Ty::U8, Ty::I16, Ty::U16] {
            assert!(narrow_of(&ty).is_some(), "{ty:?} is narrow");
        }
        for ty in [Ty::I32, Ty::U32, Ty::I64, Ty::U64, Ty::Bool, Ty::Ptr] {
            assert!(narrow_of(&ty).is_none(), "{ty:?} is not narrow arithmetic");
        }
    }

    /// A `Load`/`Store` picks the access width AND the extension the trust-ir
    /// type demands, with the natural-alignment exponent the spec caps it at.
    #[test]
    fn memory_ops_follow_the_trust_ir_type() {
        use super::super::encode::op as o;
        let cases: &[(Ty, u8, u8, u32)] = &[
            (Ty::I8, o::I32_LOAD8_S, o::I32_STORE8, 0),
            (Ty::U8, o::I32_LOAD8_U, o::I32_STORE8, 0),
            (Ty::I16, o::I32_LOAD16_S, o::I32_STORE16, 1),
            (Ty::U16, o::I32_LOAD16_U, o::I32_STORE16, 1),
            (Ty::I32, o::I32_LOAD, o::I32_STORE, 2),
            (Ty::U32, o::I32_LOAD, o::I32_STORE, 2),
            (Ty::I64, o::I64_LOAD, o::I64_STORE, 3),
            (Ty::U64, o::I64_LOAD, o::I64_STORE, 3),
            (Ty::F32, o::F32_LOAD, o::F32_STORE, 2),
            (Ty::F64, o::F64_LOAD, o::F64_STORE, 3),
            (Ty::Ptr, o::I32_LOAD, o::I32_STORE, 2),
            // A `Bool` is a one-BYTE object; a wider load would read its
            // neighbours.
            (Ty::Bool, o::I32_LOAD8_U, o::I32_STORE8, 0),
        ];
        for (ty, load, store, align) in cases {
            assert_eq!(
                mem_ops(ty).unwrap_or_else(|e| panic!("{ty:?}: {e}")),
                (*load, *store, *align),
                "memory ops for {ty:?}",
            );
        }
        // The i64 sub-word rows of the same table (the carrier the current type
        // mapping never produces, since every sub-32-bit trust-ir integer
        // carries in i32) are wired and pinned here.
        let i64_rows: &[(u32, bool, u8, u8, u32)] = &[
            (8, true, o::I64_LOAD8_S, o::I64_STORE8, 0),
            (8, false, o::I64_LOAD8_U, o::I64_STORE8, 0),
            (16, true, o::I64_LOAD16_S, o::I64_STORE16, 1),
            (16, false, o::I64_LOAD16_U, o::I64_STORE16, 1),
            (32, true, o::I64_LOAD32_S, o::I64_STORE32, 2),
            (32, false, o::I64_LOAD32_U, o::I64_STORE32, 2),
        ];
        for (bits, signed, load, store, align) in i64_rows {
            assert_eq!(
                mem_ops_for(
                    ValType::I64,
                    MemAccess {
                        bits: *bits,
                        signed: *signed
                    }
                )
                .unwrap(),
                (*load, *store, *align),
                "i64.load{bits}_{}",
                if *signed { "s" } else { "u" },
            );
        }
    }

    /// No trust-ir scalar type reaches an `i64` carrier narrower than 64 bits,
    /// so `mem_ops` never selects `i64.load8/16/32_*` (0x30..=0x35) or
    /// `i64.store8/16/32` (0x3c..=0x3e): the verify value-domain gate excludes
    /// exactly those bytes as never selected, and this is the fact its reason
    /// cites.
    #[test]
    fn no_scalar_type_selects_an_i64_sub_word_access() {
        let tys = [
            Ty::Bool,
            Ty::I8,
            Ty::U8,
            Ty::I16,
            Ty::U16,
            Ty::I32,
            Ty::U32,
            Ty::I64,
            Ty::U64,
            Ty::Isize,
            Ty::Usize,
            Ty::Char,
            Ty::Ptr,
            Ty::F32,
            Ty::F64,
        ];
        for ty in &tys {
            if let Some(repr) = int_repr_of(ty) {
                assert!(
                    !(repr.carrier == ValType::I64 && repr.bits < 64),
                    "{ty:?} gets a narrow i64 carrier"
                );
            }
            let (load, store, _) = mem_ops(ty).unwrap_or_else(|e| panic!("{ty:?}: {e}"));
            assert!(
                !(0x30..=0x35).contains(&load),
                "{ty:?} selects load 0x{load:02x}"
            );
            assert!(
                !(0x3c..=0x3e).contains(&store),
                "{ty:?} selects store 0x{store:02x}"
            );
        }
    }

    /// A trust-ir `MemCopy` (both `overlap` settings) or `MemSet` lowers to
    /// its op inside `if (n)` on the count, with the pointers and the count
    /// reaching the op unchanged: a zero count skips the op, whose range-end
    /// check would trap on an out-of-memory pointer where trust-ir defines a
    /// no-op, and a nonzero count reaches it whole. The lowering binds the
    /// count to a fresh local; the emission pass coalesces that copy into the
    /// count parameter itself, so the module reads parameter 2 at both the
    /// guard and the op. The verify bulk-memory credit runs these bodies;
    /// this pins the shape it relies on in the emitted module.
    #[test]
    fn a_bulk_memory_op_is_guarded_on_its_whole_count() {
        use trust_cg_verify::wasm_abi_proofs::{Imm, decode_insts, decode_module};
        for (what, sub) in [("memcpy", 10u32), ("memmove", 10), ("memset", 11)] {
            let mut mb = ModuleBuilder::new("bulk");
            let second = if what == "memset" { Ty::U8 } else { Ty::Ptr };
            let ft = mb.add_func_type(vec![Ty::Ptr, second.clone(), Ty::Usize], vec![]);
            let mut f = mb.function("bulk", ft);
            let e = f.create_block();
            let dst = f.add_block_param(e, Ty::Ptr);
            let b = f.add_block_param(e, second);
            let n = f.add_block_param(e, Ty::Usize);
            f.switch_to_block(e);
            match what {
                "memcpy" => f.memcopy(dst, b, n, false),
                "memmove" => f.memcopy(dst, b, n, true),
                _ => f.memset(dst, b, n),
            }
            f.ret(vec![]);
            f.build();
            let bytes = compile_module_with_license(
                &wasm32(mb.build().expect("ModuleBuilder::build: test fixture")),
                &permit_unlicensed(),
            )
            .expect("compiles");
            let module = decode_module(&bytes).expect("decodes");
            let insts = decode_insts(&module.bodies[0].code).expect("the body decodes");
            let ops: Vec<(u8, Imm)> = insts.iter().map(|i| (i.op, i.imm.clone())).collect();
            let at: Vec<usize> = ops
                .iter()
                .enumerate()
                .filter(|(_, (op, imm))| *op == 0xfc && *imm == Imm::Fc(sub))
                .map(|(k, _)| k)
                .collect();
            let [k] = at[..] else {
                panic!("{what}: {} bulk ops in {ops:?}", at.len());
            };
            let Some((0x20, Imm::Idx(count))) = ops.get(k - 1).cloned() else {
                panic!("{what}: the count operand is not a local read: {ops:?}");
            };
            assert_eq!(count, 2, "{what}: the count is read from its parameter");
            assert_eq!(
                ops[k - 5..=k + 1],
                [
                    (0x20, Imm::Idx(2)),
                    (0x04, Imm::BlockType(0x40)),
                    (0x20, Imm::Idx(0)),
                    (0x20, Imm::Idx(1)),
                    (0x20, Imm::Idx(count)),
                    (0xfc, Imm::Fc(sub)),
                    (0x0b, Imm::None),
                ],
                "{what}: the op must sit inside `if (n)` on the unmodified count"
            );
        }
    }

    /// The `br_table` heuristic and its scope, stated as a table.
    #[test]
    fn br_table_is_chosen_only_when_dense_enough() {
        use trust_ir::SwitchCase;
        let switch_cases = |values: &[i128]| -> Vec<SwitchCase> {
            values
                .iter()
                .map(|v| SwitchCase {
                    value: Constant::Int(*v),
                    target: BlockId::new(0),
                    args: vec![],
                })
                .collect()
        };
        let plan = |ty: Ty, values: &[i128]| br_table_plan(&ty, &switch_cases(values)).unwrap();

        // Below the minimum case count: cascade.
        assert!(plan(Ty::I32, &[0, 1]).is_none());
        // Dense and contiguous: a table with no holes.
        let dense = plan(Ty::I32, &[0, 1, 2, 3]).expect("dense range uses br_table");
        assert_eq!(dense.min, 0);
        assert_eq!(dense.arms, 4);
        assert_eq!(dense.arm_of_index, vec![Some(0), Some(1), Some(2), Some(3)]);
        // Cases that do not start at 0 are normalized by `min`, and a hole in
        // the covered range takes the DEFAULT edge.
        let shifted = plan(Ty::I32, &[10, 11, 13]).expect("a 4-wide span over 3 cases");
        assert_eq!(shifted.min, 10);
        assert_eq!(shifted.arm_of_index, vec![Some(0), Some(1), None, Some(2)]);
        // Negative case values normalize the same way.
        let negative = plan(Ty::I32, &[-2, -1, 0, 1]).expect("negative range uses br_table");
        assert_eq!(negative.min, -2);
        assert_eq!(negative.arm_of_index.len(), 4);
        // Too sparse (span 5 over 3 cases is fine; span 40 over 3 is not).
        assert!(plan(Ty::I32, &[0, 1, 4]).is_some());
        assert!(plan(Ty::I32, &[0, 1, 39]).is_none());
        // Past the absolute span bound, however dense the rest would be.
        let wide: Vec<i128> = (0..600).map(|k| k * 2).collect();
        assert!(plan(Ty::I32, &wide).is_none());
        // An i64 switch keeps the cascade: the 32-bit index normalization is
        // not sound for a 64-bit value.
        assert!(plan(Ty::I64, &[0, 1, 2, 3]).is_none());
        // A narrow switch value normalizes at its CARRIER: `I8` 200 is -56.
        let narrow = plan(Ty::I8, &[200, 201, 202]).expect("narrow switch uses br_table");
        assert_eq!(narrow.min, -56);
        // A duplicated case value binds the FIRST arm, matching the cascade.
        let duplicated = plan(Ty::I32, &[5, 6, 5, 7]).expect("dense");
        assert_eq!(
            duplicated.arm_of_index,
            vec![Some(0), Some(1), Some(3)],
            "the second `5` does not displace the first"
        );
    }

    /// Narrow arithmetic compiles, and the emitted body carries the
    /// re-canonicalization the invariant demands (a `U8` add masks; an `I8` add
    /// sign-extends).
    #[test]
    fn narrow_arithmetic_recanonicalizes_its_result() {
        let u8_add = compile_module_with_license(
            &binop_module("f", Ty::U8, BinOp::Add),
            &permit_unlicensed(),
        )
        .unwrap();
        assert_wasm_header(&u8_add);
        assert!(
            u8_add.windows(3).any(|w| w == [op::I32_CONST, 0xff, 0x01]),
            "a U8 add must mask its result to 8 bits"
        );
        let i8_add = compile_module_with_license(
            &binop_module("f", Ty::I8, BinOp::Add),
            &permit_unlicensed(),
        )
        .unwrap();
        assert!(
            i8_add.contains(&op::I32_EXTEND8_S),
            "an I8 add must sign-extend its result back to 8 bits"
        );
        // Every narrow type compiles across the arithmetic surface.
        for ty in [Ty::I8, Ty::U8, Ty::I16, Ty::U16] {
            for op in [
                BinOp::Add,
                BinOp::Sub,
                BinOp::Mul,
                BinOp::And,
                BinOp::Or,
                BinOp::Xor,
                BinOp::Shl,
                BinOp::LShr,
                BinOp::AShr,
                BinOp::SDiv,
                BinOp::UDiv,
                BinOp::SRem,
                BinOp::URem,
            ] {
                let bytes = compile_module_with_license(
                    &binop_module("f", ty.clone(), op),
                    &permit_unlicensed(),
                )
                .unwrap_or_else(|e| panic!("{ty:?} {op:?}: {e}"));
                assert_wasm_header(&bytes);
            }
        }
    }

    /// `trunc_sat` saturates at the CARRIER's range, so a float→narrow cast
    /// converts through the SIGNED i32 `trunc_sat` and clamps to the op's
    /// narrow range; a float→`bool` cast is not an integer conversion and is
    /// refused by name.
    #[test]
    fn a_float_to_narrow_integer_cast_clamps_the_i32_conversion() {
        let module = |dst: Ty| {
            let mut mb = ModuleBuilder::new("m");
            let ft = mb.add_func_type(vec![Ty::F32], vec![dst.clone()]);
            let mut fb = mb.function("narrow_fptoui", ft);
            let e = fb.create_block();
            let x = fb.add_block_param(e, Ty::F32);
            fb.switch_to_block(e);
            let r = fb.cast(CastOp::FPToUISat, Ty::F32, dst, x);
            fb.ret(vec![r]);
            fb.build();
            wasm32(mb.build().expect("ModuleBuilder::build: test fixture"))
        };
        let bytes = compile_module_with_license(&module(Ty::U8), &permit_unlicensed())
            .expect("float -> u8 lowers");
        assert_wasm_header(&bytes);
        // i32.trunc_sat_f32_s (0xfc 0x00), never the unsigned form (0xfc 0x01).
        assert!(bytes.windows(2).any(|w| w == [op::FC_PREFIX, 0x00]));
        assert!(!bytes.windows(2).any(|w| w == [op::FC_PREFIX, 0x01]));
        // WS7.3: the module entries run trust-ir's codegen admission first,
        // which refuses the cast by its own finding (`CastIncompatible`)...
        let to_bool = module(Ty::Bool);
        match compile_module_with_license(&to_bool, &permit_unlicensed()).unwrap_err() {
            WasmLowerError::InvalidTrustIr(refusal) => assert!(
                refusal.any(|finding| matches!(
                    finding,
                    trust_ir_build::ValidationError::CastIncompatible { .. }
                )),
                "{refusal}"
            ),
            other => panic!("float -> bool: expected the admission refusal, got {other}"),
        }
        // ...and this lane's own arm still refuses it by name where no module
        // admission runs (the public per-function entry, whose prerequisite
        // check does not judge casts). The fixture is claim-less, so it states
        // `Permit` as every compile above does: under the default policy the
        // per-function entry refuses it first, by its missing license (DG-73).
        let err = lower_function_with_license(
            &mut WasmModule::new(),
            &to_bool.functions[0],
            &to_bool,
            WasmFunctionEnv::empty(),
            &permit_unlicensed(),
        )
        .map(drop)
        .unwrap_err();
        assert!(err.to_string().contains("not an integer type"), "{err}");
    }

    /// Fail-closed: a module with globals under an IMPORTED memory would write
    /// its static data into the host's address space at an address the host
    /// never reserved.
    #[test]
    fn refuses_static_data_in_an_ungranted_host_memory() {
        use trust_ir::Global;
        let table_module = || {
            let mut mb = ModuleBuilder::new("table");
            mb.add_global(Global {
                section: None,
                visibility: trust_ir::Visibility::Default,
                retained: false,
                name: "TABLE".to_string(),
                ty: Ty::U32,
                mutable: false,
                initializer: Some(Constant::Int(0x1A2B_3C4D)),
                linkage: Default::default(),
                tls: None,
                align: None,
            });
            let ft = mb.add_func_type(vec![], vec![Ty::U32]);
            let mut fb = mb.function("read", ft);
            let e = fb.create_block();
            fb.switch_to_block(e);
            let p = fb.global_addr(trust_ir::value::GlobalId::new(0));
            let v = fb.load(Ty::U32, p);
            fb.ret(vec![v]);
            fb.build();
            wasm32(mb.build().expect("ModuleBuilder::build: test fixture"))
        };

        // Owned memory: the initializer's LITTLE-ENDIAN byte image ships in a
        // data segment, and the module reads it back through linear memory.
        let bytes = compile_module_with_license(&table_module(), &permit_unlicensed()).unwrap();
        assert_wasm_header(&bytes);
        assert!(
            bytes.windows(4).any(|w| w == [0x4d, 0x3c, 0x2b, 0x1a]),
            "the global's byte image must ship in a data segment"
        );

        let island = WasmModulePolicy::island("tables");
        let err =
            compile_module_with_policy_and_license(&table_module(), &island, &permit_unlicensed())
                .unwrap_err();
        assert!(
            matches!(err, WasmLowerError::HostMemoryNotGranted(_)),
            "{err}"
        );
        assert!(err.to_string().contains("HostReservedAt"), "{err}");
    }

    /// Fail-closed: growing a memory the module does not own is the host's
    /// decision, and the refusal names the policy that records the grant.
    #[test]
    fn refuses_memory_growth_in_an_ungranted_host_memory() {
        let policy = WasmModulePolicy {
            memory_growth: WasmMemoryGrowthPolicy::OwnedShims,
            ..WasmModulePolicy::island("grower")
        };
        let err =
            compile_module_with_policy_and_license(&frame_module(), &policy, &permit_unlicensed())
                .unwrap_err();
        assert!(
            matches!(err, WasmLowerError::HostMemoryNotGranted(_)),
            "{err}"
        );
        assert!(err.to_string().contains("HostGrantedShims"), "{err}");

        // Under an OWNED memory the same request is granted by construction.
        let owned = WasmModulePolicy {
            memory_growth: WasmMemoryGrowthPolicy::OwnedShims,
            ..WasmModulePolicy::closed()
        };
        let bytes =
            compile_module_with_policy_and_license(&frame_module(), &owned, &permit_unlicensed())
                .unwrap();
        assert_wasm_header(&bytes);
    }

    #[test]
    fn run_length_encode_groups_consecutive() {
        use ValType::*;
        assert_eq!(run_length_encode(&[]), vec![]);
        assert_eq!(run_length_encode(&[I32, I32, I32]), vec![(3, I32)]);
        assert_eq!(
            run_length_encode(&[I32, I64, I64, I32]),
            vec![(1, I32), (2, I64), (1, I32)]
        );
    }

    /// A target-free module is refused with a diagnostic naming the fix.
    #[test]
    fn public_lower_function_refuses_a_target_free_module() {
        // The guard must hold at the crate's PUBLIC entry too, not only in
        // `compile_module`: frame/GEP layout comes from the module's target
        // while addresses are emitted as i32, so a target-free module would
        // silently mis-lay-out every frame.
        let mut mb = ModuleBuilder::new("target_free_probe");
        let ty = mb.add_func_type(vec![], vec![Ty::I32]);
        let mut fb = mb.function("seven", ty);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        let seven = fb.iconst(Ty::I32, 7);
        fb.ret(vec![seven]);
        fb.build();
        let module = mb.build().expect("ModuleBuilder::build: test fixture");
        assert!(module.target_info.is_none(), "probe must be target-free");

        let mut wasm_module = WasmModule::new();
        let err = lower_function_with_license(
            &mut wasm_module,
            &module.functions[0],
            &module,
            WasmFunctionEnv::empty(),
            &permit_unlicensed(),
        )
        .expect_err("a target-free module must be refused at the public entry");
        assert!(
            matches!(err, WasmLowerError::MissingTargetInfo(_)),
            "expected MissingTargetInfo, got {err:?}"
        );
    }

    #[test]
    fn refuses_target_free_module() {
        let mut module = sum_to_module();
        module.target_info = None;
        let err = compile_module_with_license(&module, &permit_unlicensed()).unwrap_err();
        assert!(matches!(err, WasmLowerError::MissingTargetInfo(_)), "{err}");
        let msg = err.to_string();
        assert!(msg.contains("wasm32_target_info"), "{msg}");
        assert!(msg.contains("wasm32-unknown-unknown"), "{msg}");
    }

    /// A module pinned to a 64-bit-pointer native target is refused, naming
    /// every mismatched component.
    #[test]
    fn refuses_non_wasm32_target_info() {
        use trust_ir::{Endianness, StructPassingPolicy, TargetInfo};
        let mut module = sum_to_module();
        module.target_info = Some(TargetInfo {
            triple: "aarch64-apple-darwin".to_string(),
            pointer_size: 8,
            endianness: Endianness::Little,
            abi: None,
            struct_passing: StructPassingPolicy::Unclassified,
        });
        let err = compile_module_with_license(&module, &permit_unlicensed()).unwrap_err();
        assert!(matches!(err, WasmLowerError::TargetMismatch(_)), "{err}");
        let msg = err.to_string();
        assert!(msg.contains("aarch64-apple-darwin"), "{msg}");
        assert!(msg.contains("pointer_size 8"), "{msg}");
        assert!(msg.contains("wasm32_target_info"), "{msg}");
    }

    /// The canonical constructor passes the guard by construction.
    #[test]
    fn accepts_canonical_wasm32_target_info() {
        assert_wasm_header(
            &compile_module_with_license(&sum_to_module(), &permit_unlicensed()).unwrap(),
        );
    }

    /// A call to a multi-return callee uses wasm multi-value results.
    #[test]
    fn lowers_multi_result_direct_call() {
        use trust_ir::{
            Block as TrustIrBlock, FuncId, FuncTy, Function as TrustIrFunction, InstrNode, ValueId,
        };

        let mut module = Module::new("multi_result_call");
        let pair_ty = module
            .add_func_type(FuncTy {
                params: vec![],
                returns: vec![Ty::I32, Ty::I32],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let one_ty = module
            .add_func_type(FuncTy {
                params: vec![],
                returns: vec![Ty::I32],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");

        let mut callee = TrustIrFunction::new(FuncId::new(0), "pair", pair_ty, BlockId::new(0));
        callee.blocks = vec![TrustIrBlock {
            id: BlockId::new(0),
            params: vec![],
            body: vec![
                InstrNode::new(Inst::Const {
                    ty: Ty::I32,
                    value: Constant::Int(1),
                })
                .with_results(vec![ValueId::new(0)]),
                InstrNode::new(Inst::Const {
                    ty: Ty::I32,
                    value: Constant::Int(2),
                })
                .with_results(vec![ValueId::new(1)]),
                InstrNode::new(Inst::Return {
                    values: vec![ValueId::new(0), ValueId::new(1)],
                }),
            ],
        }];
        let mut caller = TrustIrFunction::new(FuncId::new(1), "caller", one_ty, BlockId::new(0));
        caller.blocks = vec![TrustIrBlock {
            id: BlockId::new(0),
            params: vec![],
            body: vec![
                // Both results bound (trust-ir refuses a call that binds
                // fewer results than its callee returns,
                // `InstrResultArityMismatch`), so the refusal is this lane's.
                InstrNode::new(Inst::Call {
                    callee: FuncId::new(0),
                    args: vec![],
                })
                .with_results(vec![ValueId::new(10), ValueId::new(11)]),
                InstrNode::new(Inst::Return {
                    values: vec![ValueId::new(10)],
                }),
            ],
        }];
        module
            .try_add_function(callee)
            .expect("Module::try_add_function: test fixture");
        module
            .try_add_function(caller)
            .expect("Module::try_add_function: test fixture");
        let module = wasm32(module);

        // Multi-value: the callee returns both lanes, the caller binds one and
        // drops the other.
        let bytes = compile_module_with_license(&module, &permit_unlicensed()).unwrap();
        assert_wasm_header(&bytes);
    }

    /// A Rust-convention function with an all-scalar signature lowers to
    /// exactly the bytes of its C-convention twin: the two conventions differ
    /// only for memory-carried values (`abi.rs`).
    #[test]
    fn lowers_rust_convention_function() {
        let mut module = sum_to_module();
        let c_bytes = compile_module_with_license(&module, &permit_unlicensed()).unwrap();
        module.functions[0].calling_conv = CallingConv::Rust;
        assert_eq!(
            compile_module_with_license(&module, &permit_unlicensed()).unwrap(),
            c_bytes
        );
    }

    /// A function declared with a convention this lane does not lower is
    /// refused.
    #[test]
    fn refuses_non_c_calling_convention_function() {
        let mut module = sum_to_module();
        module.functions[0].calling_conv = CallingConv::Swift;
        let err = compile_module_with_license(&module, &permit_unlicensed()).unwrap_err();
        assert!(
            matches!(err, WasmLowerError::UnsupportedCallingConv(_)),
            "{err}"
        );
        assert!(err.to_string().contains("Swift"), "{err}");
        assert!(err.to_string().contains("CallingConv::C"), "{err}");
    }

    /// The call-contract scan covers the COMPLETE function: a non-C
    /// `call_indirect` in a block that never runs is still refused. (The block
    /// is DEAD, behind a constant-false branch, not unreachable: trust-ir
    /// refuses a block no edge reaches, `UnreachableBlock`, and since WS7.3
    /// ingestion admission refuses what the validator refuses.)
    #[test]
    fn refuses_non_c_indirect_call_in_unreachable_block() {
        use trust_ir::{
            Block as TrustIrBlock, FuncId, FuncTy, Function as TrustIrFunction, InstrNode, ValueId,
        };

        let mut module = Module::new("unreachable_fast_call");
        let void_ty = module
            .add_func_type(FuncTy {
                params: vec![],
                returns: vec![],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut func = TrustIrFunction::new(FuncId::new(0), "f", void_ty, BlockId::new(0));
        func.blocks = vec![
            TrustIrBlock {
                id: BlockId::new(0),
                params: vec![],
                body: vec![
                    InstrNode::new(Inst::Const {
                        ty: Ty::Bool,
                        value: Constant::Bool(false),
                    })
                    .with_result(ValueId::new(1)),
                    InstrNode::new(Inst::CondBr {
                        cond: ValueId::new(1),
                        then_target: BlockId::new(1),
                        then_args: vec![],
                        else_target: BlockId::new(2),
                        else_args: vec![],
                    }),
                ],
            },
            TrustIrBlock {
                id: BlockId::new(2),
                params: vec![],
                body: vec![InstrNode::new(Inst::Return { values: vec![] })],
            },
            // Never runs (the branch above is constant false).
            TrustIrBlock {
                id: BlockId::new(1),
                params: vec![],
                body: vec![
                    InstrNode::new(Inst::NullPtr).with_result(ValueId::new(0)),
                    InstrNode::new(Inst::CallIndirect {
                        callee: ValueId::new(0),
                        sig: void_ty,
                        args: vec![],
                        calling_conv: CallingConv::Fast,
                    }),
                    InstrNode::new(Inst::Return { values: vec![] }),
                ],
            },
        ];
        module
            .try_add_function(func)
            .expect("Module::try_add_function: test fixture");

        let err = compile_module_with_license(&wasm32(module), &permit_unlicensed()).unwrap_err();
        assert!(
            matches!(err, WasmLowerError::UnsupportedCallingConv(_)),
            "{err}"
        );
        assert!(err.to_string().contains("Fast"), "{err}");
    }

    /// The evidence sibling returns the same bytes plus an honest summary:
    /// verification route NotRun / verdict MissingEvidence (WP-0), the named
    /// ran / not-run lists, and a sha256 binding to the emitted module.
    #[test]
    fn evidence_reports_not_run_and_binds_module_bytes() {
        let module = sum_to_module();
        let (bytes, ev) = compile_module_with_evidence_policy_and_license(
            &module,
            &WasmModulePolicy::closed(),
            &permit_unlicensed(),
        )
        .unwrap();
        assert_eq!(
            bytes,
            compile_module_with_license(&module, &permit_unlicensed()).unwrap()
        );
        assert_wasm_header(&bytes);

        assert_eq!(ev.schema, WASM_COMPILE_EVIDENCE_SCHEMA);
        assert_eq!(ev.target, crate::wasm::target::WASM32_TRIPLE);
        assert_eq!(ev.verification_route, EvidenceStrength::NotRun);
        assert_eq!(ev.verdict, ProofEvidenceVerdict::MissingEvidence);
        assert!(ev.ran.contains(&"wasm32_target_info_guard"));
        assert!(ev.ran.contains(&"multi_result_call_guard"));
        assert!(ev.ran.contains(&"trust_ir_codegen_admission"));
        assert!(ev.ran.contains(&"codegen_license"));
        assert!(ev.not_run.contains(&"per_function_lowering_proofs"));
        assert!(ev.not_run.contains(&"per_module_differential_execution"));
        assert_eq!(ev.function_count, 1);
        assert_eq!(ev.module_size_bytes, bytes.len());
        assert_eq!(ev.module_sha256, crate::jit_diagnostics::sha256_hex(&bytes));
        assert!(
            ev.host_contract.is_empty(),
            "a closed module binds no host: {:?}",
            ev.host_contract
        );

        let json = ev.to_json();
        assert_eq!(json["schema"], WASM_COMPILE_EVIDENCE_SCHEMA);
        assert_eq!(json["verification_route"], "not_run");
        assert_eq!(json["verdict"], "missing_evidence");
        assert_eq!(json["host_contract"], serde_json::json!([]));
    }

    /// P4 family (1) is a PER-COMPILE ARTIFACT, not a description of one: the
    /// evidence route really runs `wasm_cfg_proofs::check_module_structure` over
    /// the bytes it just emitted, and the counts prove the checker walked a
    /// module with control flow in it rather than trivially accepting nothing.
    ///
    /// And the honesty half, which is the point of the row: a structural
    /// invariant HOLDING is a necessary condition on the structuring, so it must
    /// not move the verdict or the route. Both are asserted UNCHANGED here.
    #[test]
    fn the_cfg_structural_invariant_runs_on_the_evidence_compile() {
        let (bytes, ev) = compile_module_with_evidence_policy_and_license(
            &sum_to_module(),
            &WasmModulePolicy::closed(),
            &permit_unlicensed(),
        )
        .unwrap();

        assert!(
            ev.ran.contains(&"wasm_cfg_structural_invariant"),
            "the structural invariant must be reported as HAVING RUN: {:?}",
            ev.ran
        );
        assert!(!ev.not_run.contains(&"wasm_cfg_structural_invariant"));

        let WasmCfgStructural::Holds {
            functions,
            instructions,
            branch_labels_resolved,
            joins_checked,
            scopes_matched,
        } = ev.cfg_structural
        else {
            panic!("expected Holds, got {:?}", ev.cfg_structural);
        };
        assert_eq!(functions, 1);
        assert!(instructions > 0);
        assert!(
            branch_labels_resolved > 0,
            "`sum_to` is a counted loop; a run that resolved NO branch label \
             checked nothing about its control flow"
        );
        assert!(joins_checked > 0);
        assert!(scopes_matched > 0);

        // Nothing else moved. A necessary condition is not a proof.
        assert_eq!(ev.verdict, ProofEvidenceVerdict::MissingEvidence);
        assert_eq!(ev.verification_route, EvidenceStrength::NotRun);
        assert_eq!(ev.to_json()["cfg_structural"]["verdict"], "holds");

        // Same bytes as the plain route: the check refuses, it never rewrites.
        assert_eq!(
            bytes,
            compile_module_with_license(&sum_to_module(), &permit_unlicensed()).unwrap()
        );
    }

    /// A REFUTATION IS LOUD. The backend will not emit a structurally broken
    /// module on request, so the refuted arm is exercised with the CFG family's
    /// own mis-ordered merge nest — the byte-level shape of the P3 defect
    /// (`8ff365ef`) where a forward `br` had no label in scope.
    #[test]
    fn a_refuted_structural_invariant_fails_the_compile_loudly() {
        let mut ran = Vec::new();
        let mut not_run = Vec::new();
        let broken = trust_cg_verify::wasm_cfg_proofs::misordered_merge_nest_module();
        let err = classify_cfg_structural(&broken, &mut ran, &mut not_run)
            .expect_err("a mis-ordered merge nest must REFUSE, not report");
        assert!(
            matches!(err, WasmLowerError::StructuralInvariantRefuted(_)),
            "{err}"
        );
        assert!(
            err.to_string().contains("REFUTED"),
            "the message must say so: {err}"
        );
        assert!(
            ran.is_empty() && not_run.is_empty(),
            "a refusal credits nothing"
        );

        // The same checker ACCEPTS the correct nest, so the refusal above is a
        // judgement about those bytes and not a checker that refuses everything.
        let mut ran_ok = Vec::new();
        let mut not_run_ok = Vec::new();
        let good = trust_cg_verify::wasm_cfg_proofs::correct_merge_nest_module();
        assert!(
            classify_cfg_structural(&good, &mut ran_ok, &mut not_run_ok)
                .expect("the correct nest is accepted")
                .holds()
        );
        assert_eq!(ran_ok, vec!["wasm_cfg_structural_invariant"]);
    }

    /// A mid-end output whose bytes refute the CFG structural invariant is
    /// not emitted: the screen records a fallback (the caller then lowers the
    /// input) instead of failing the compile, and keeps an output it accepts
    /// together with its verdict.
    #[test]
    fn a_refuted_mid_end_output_falls_back_to_the_input() {
        use trust_cg_irmid::MidProfile;
        let mut mid = IrmidReport::not_run(MidProfile::Wasm32, "test");
        let broken = trust_cg_verify::wasm_cfg_proofs::misordered_merge_nest_module();
        assert!(screen_mid_end_output(&broken, &mut mid).is_none());
        assert!(!mid.applied);
        let why = mid.fallback.as_deref().expect("the fallback is recorded");
        assert!(why.contains("CFG structural invariant"), "{why}");

        let mut mid = IrmidReport::not_run(MidProfile::Wasm32, "test");
        let good = trust_cg_verify::wasm_cfg_proofs::correct_merge_nest_module();
        let verdict = screen_mid_end_output(&good, &mut mid).expect("the output is kept");
        assert!(verdict.holds());
        assert!(mid.applied && mid.fallback.is_none());
    }

    /// THE INPUT'S REFUTATION IS THE COMPILE'S. When the mid-end's output is
    /// emitted, the input's own lowering is checked too, and its `Refuted`
    /// verdict wins over the output's `Holds`; a holding input leaves the
    /// output's verdict in place.
    #[test]
    fn a_refuted_input_lowering_is_filed_when_the_output_is_emitted() {
        use trust_cg_irmid::MidProfile;
        use trust_cg_verify::wasm_cfg_proofs::{
            CfgVerdict, check_module_structure, correct_merge_nest_module,
            misordered_merge_nest_module,
        };
        let good = correct_merge_nest_module();
        let parts = |input: Vec<u8>| CompiledParts {
            bytes: good.clone(),
            host_contract: Vec::new(),
            local_emission: WasmLocalOptSummary::default(),
            mid_end: IrmidReport::not_run(MidProfile::Wasm32, "test"),
            cfg_verdict: Some(check_module_structure(&good)),
            input_check: Some(input),
        };
        let verdict = parts(misordered_merge_nest_module()).take_cfg_verdict();
        assert!(matches!(verdict, CfgVerdict::Refuted(_)), "{verdict:?}");
        let (mut ran, mut not_run) = (Vec::new(), Vec::new());
        let error = classify_cfg_verdict(verdict, &mut ran, &mut not_run)
            .expect_err("the input's refutation fails the compile");
        assert!(
            matches!(error, WasmLowerError::StructuralInvariantRefuted(_)),
            "{error}"
        );
        assert!(parts(good.clone()).take_cfg_verdict().holds());
    }

    /// A table program for the static-data fit: `t[a & 7]` of an eight-word
    /// local constant table, which constant-table promotion turns into 32
    /// bytes of read-only data.
    fn promoted_table_pair() -> (Module, Module) {
        let mut text = String::from(
            "module \"fit\"\ntarget \"wasm32-unknown-unknown\" 4 little\n\n\
             type ty.0 = i32\n\nfuncty.0 = (i32) -> (i32)\n\n\
             fn @t(functy.0) {\nbb0(%0: i32):\n\
             \x20   %1 = alloca [ty.0 x 8], align 4\n\
             \x20   %2 = ptrtoint ptr %1 to i32\n",
        );
        for i in 0..8 {
            let v = 10 + 4 * i;
            text.push_str(&format!(
                "    %{v} = const i32 {}\n    %{} = const i32 {}\n    %{} = add i32 %2, %{}\n    \
                 %{} = inttoptr i32 %{} to ptr\n    store i32 %{v}, ptr %{}\n",
                3 * i + 1,
                v + 1,
                4 * i,
                v + 2,
                v + 1,
                v + 3,
                v + 2,
                v + 3
            ));
        }
        text.push_str(
            "    %50 = const i32 7\n    %51 = and i32 %0, %50\n    %52 = bitcast i32 %51 to u32\n\
             \x20   %53 = const u32 8\n    %54 = icmp ult u32 %52, %53\n    condbr %54, bb1, bb2\n\
             bb2:\n    unreachable\nbb1:\n    %55 = const i32 4\n    %56 = mul i32 %51, %55\n\
             \x20   %57 = add i32 %2, %56\n    %58 = inttoptr i32 %57 to ptr\n\
             \x20   %59 = load i32, ptr %58\n    ret %59\n}\n",
        );
        let module = trust_ir::parser::parse_module(&text).expect("parse the table program");
        let (candidate, report) =
            trust_cg_irmid::optimize_module(&module, &trust_cg_irmid::MidConfig::wasm32());
        assert_eq!(report.globals_added, 1, "the table is promoted: {report:?}");
        (module, candidate)
    }

    /// STATIC DATA FITS THE INPUT'S LAYOUT. A fixed policy refuses an
    /// optimized module with more static data than its input (a closed page
    /// or a host-reserved region alike), and the sized policy grows its pages
    /// by exactly what the stack floor rose, so the stack is never shorter.
    #[test]
    fn the_optimized_modules_static_data_fits_the_inputs_layout() {
        let (input, candidate) = promoted_table_pair();
        let closed = WasmModulePolicy::closed();
        let why = emitted_policy(&closed, ClosedPolicyFit::AsGiven, 0, &candidate, true)
            .expect_err("a fixed page cannot take new static data");
        assert!(why.contains("32 bytes of static data"), "{why}");
        let host = WasmModulePolicy {
            static_data: WasmStaticDataPolicy::HostReservedAt { base: 4096 },
            ..WasmModulePolicy::island("fit")
        };
        assert!(emitted_policy(&host, ClosedPolicyFit::AsGiven, 0, &candidate, true).is_err());
        // The input itself fits as given, and so does the candidate when the
        // input already had as much static data.
        assert_eq!(
            emitted_policy(&closed, ClosedPolicyFit::AsGiven, 0, &input, true).as_ref(),
            Ok(&closed)
        );
        assert!(emitted_policy(&closed, ClosedPolicyFit::AsGiven, 32, &candidate, true).is_ok());

        let sized = sized_closed_policy(&input).expect("size");
        let grown = emitted_policy(
            &sized,
            ClosedPolicyFit::SizedForEmitted,
            0,
            &candidate,
            true,
        )
        .expect("the sized policy grows");
        let pages = |p: &WasmModulePolicy| match &p.memory {
            WasmMemoryPolicy::Owned { pages, .. } => u64::from(*pages),
            other => panic!("{other:?}"),
        };
        assert_eq!(pages(&grown), pages(&sized) + 1);
        let stack = |p: &WasmModulePolicy, data: u64| {
            pages(p) * u64::from(WASM_PAGE_BYTES) - closed_stack_floor(data)
        };
        assert!(stack(&grown, 32) >= stack(&sized, 0));
    }

    /// AN INCONCLUSIVE VERDICT IS UNCREDITED. Bytes the checker cannot read
    /// report as `not_run` with the reason kept — never as `ran`, and never as a
    /// silent pass.
    #[test]
    fn an_inconclusive_structural_verdict_is_uncredited() {
        let mut ran = Vec::new();
        let mut not_run = Vec::new();
        // A well-formed preamble followed by nothing the section walk can read.
        let unreadable = b"\0asm\x01\x00\x00\x00\x7f\x7f\x7f\x7f".to_vec();
        let outcome = classify_cfg_structural(&unreadable, &mut ran, &mut not_run)
            .expect("an unreadable module is a decline, not a refusal");
        assert!(
            matches!(outcome, WasmCfgStructural::Inconclusive(_)),
            "{outcome:?}"
        );
        assert!(!outcome.holds(), "an inconclusive verdict is not credit");
        assert!(ran.is_empty(), "nothing may be credited: {ran:?}");
        assert_eq!(not_run, vec!["wasm_cfg_structural_invariant"]);
        assert_eq!(outcome.to_json()["verdict"], "inconclusive");
    }

    // -----------------------------------------------------------------------
    // P2 — the island policy.
    // -----------------------------------------------------------------------

    /// roundtrip(x) = { let c = alloca i32; *c = x; *c } — needs a frame, and
    /// therefore an address to put it at.
    fn frame_module() -> Module {
        let mut mb = ModuleBuilder::new("frame");
        let ft = mb.add_func_type(vec![Ty::I32], vec![Ty::I32]);
        let mut fb = mb.function("roundtrip", ft);
        let entry = fb.create_block();
        let x = fb.add_block_param(entry, Ty::I32);
        fb.switch_to_block(entry);
        let cell = fb.alloca(Ty::I32);
        fb.store(Ty::I32, cell, x);
        let r = fb.load(Ty::I32, cell);
        fb.ret(vec![r]);
        fb.build();
        wasm32(mb.build().expect("ModuleBuilder::build: test fixture"))
    }

    fn array_frame_module(sizes: &[u64]) -> Module {
        let mut mb = ModuleBuilder::new("array_frame");
        let element = mb.add_type(Ty::I8);
        let ft = mb.add_func_type(vec![], vec![]);
        let mut fb = mb.function("array_frame", ft);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        for &size in sizes {
            fb.alloca(Ty::Array(element, size));
        }
        fb.ret(vec![]);
        fb.build();
        wasm32(mb.build().expect("ModuleBuilder::build: test fixture"))
    }

    #[test]
    fn oversized_shadow_stack_frames_return_errors_instead_of_wrapping() {
        for sizes in [
            vec![0x8000_0000, 0x8000_0000],
            vec![0x8000_0000],
            vec![u64::from(u32::MAX)],
            vec![u64::from(u32::MAX - 3), 1],
        ] {
            assert!(matches!(
                compile_module_with_license(&array_frame_module(&sizes), &permit_unlicensed()),
                Err(WasmLowerError::FrameLayoutOverflow(_))
            ));
        }
    }

    #[test]
    fn zero_byte_alloca_still_has_an_initialized_shadow_stack_base() {
        let module = array_frame_module(&[0]);
        let mut env = WasmFunctionEnv::empty();
        env.sp_global = Some(7);
        let mut lower = Lowering::build(&module.functions[0], &module, env).unwrap();
        lower.assign_locals().unwrap();
        lower.compute_frame().unwrap();
        let frame = lower
            .frame
            .expect("even a zero-byte alloca needs a frame base");
        // A zero-sized allocation takes one byte of address space (an
        // address no other live allocation has), rounded to the stack
        // pointer's alignment.
        assert_eq!(frame.size, 8);
        assert_eq!(frame.sp_global, 7);
        assert_ne!(
            frame.base_local,
            lower.locals[&module.functions[0].blocks[0].body[0].results[0]].0
        );
        lower.emit_prologue().unwrap();
        assert_eq!(&lower.code[..2], &[op::GLOBAL_GET, 7]);
        assert_wasm_header(&compile_module_with_license(&module, &permit_unlicensed()).unwrap());
        assert!(matches!(
            lower_function_with_license(
                &mut WasmModule::new(),
                &module.functions[0],
                &module,
                WasmFunctionEnv::empty(),
                &permit_unlicensed(),
            ),
            Err(WasmLowerError::UnsupportedInst(_))
        ));
    }

    /// The closed policy is the pre-P2 backend, byte for byte.
    #[test]
    fn the_closed_policy_is_the_default_compile() {
        for module in [sum_to_module(), frame_module()] {
            assert_eq!(
                compile_module_with_license(&module, &permit_unlicensed()).unwrap(),
                compile_module_with_policy_and_license(
                    &module,
                    &WasmModulePolicy::closed(),
                    &permit_unlicensed()
                )
                .unwrap(),
            );
        }
    }

    /// Under the island policy the module binds a host contract, and the
    /// evidence REPORTS it — the honest widening of the claimed surface.
    #[test]
    fn island_evidence_reports_the_bound_host_contract() {
        let module = frame_module();
        let policy = WasmModulePolicy::island("memhash");
        // Lowered as given: the mid-end would forward the frame's one slot
        // away, and with it the frame the stack-base import serves.
        let (bytes, ev) = compile_module_with_evidence_policy_license_options(
            &module,
            &policy,
            &permit_unlicensed(),
            WasmOptOptions {
                level: DEFAULT_OPT_LEVEL,
                mid_end: false,
            },
        )
        .unwrap();
        assert_wasm_header(&bytes);
        assert_eq!(
            ev.host_contract,
            vec![
                format!("memory {ISLAND_ABI_NAMESPACE}.{ISLAND_MEMORY_IMPORT}"),
                format!("global {ISLAND_ABI_NAMESPACE}.{ISLAND_STACK_BASE_IMPORT}"),
            ],
        );
        // The island's OWN host functions live in its own namespace, never in
        // the fixed ABI one (OWNERSHIP.md §4.3).
        assert_eq!(
            policy.func_imports,
            WasmFuncImportPolicy::FromModule("trust:island/memhash@1".to_string()),
        );
        assert_ne!(ISLAND_ABI_NAMESPACE, ISLAND_HOST_MODULE);
        assert!(ev.not_run.contains(&"host_contract_verification"));
        assert_eq!(
            ev.to_json()["host_contract"],
            serde_json::json!(ev.host_contract),
        );
        // The island's bytes are NOT the closed module's.
        assert_ne!(
            bytes,
            compile_module_with_license(&module, &permit_unlicensed()).unwrap()
        );
    }

    /// A frame under an imported memory with the private page-top stack is the
    /// collision this slice exists to prevent — refused, not emitted.
    #[test]
    fn refuses_a_private_stack_top_inside_an_imported_memory() {
        let policy = WasmModulePolicy {
            memory: WasmMemoryPolicy::Imported {
                module: ISLAND_ABI_NAMESPACE.to_string(),
                name: ISLAND_MEMORY_IMPORT.to_string(),
            },
            stack: WasmStackPolicy::OwnedTop,
            func_imports: WasmFuncImportPolicy::Forbidden,
            ..WasmModulePolicy::closed()
        };
        let err =
            compile_module_with_policy_and_license(&frame_module(), &policy, &permit_unlicensed())
                .unwrap_err();
        assert!(
            matches!(err, WasmLowerError::StackBaseUnavailable(_)),
            "{err}"
        );
        assert!(err.to_string().contains("HostBase"), "{err}");
    }

    /// A memory access under the no-memory policy is refused by name.
    #[test]
    fn refuses_a_memory_access_with_no_memory() {
        let policy = WasmModulePolicy {
            memory: WasmMemoryPolicy::Absent,
            ..WasmModulePolicy::closed()
        };
        let err =
            compile_module_with_policy_and_license(&frame_module(), &policy, &permit_unlicensed())
                .unwrap_err();
        assert!(matches!(err, WasmLowerError::MemoryUnavailable(_)), "{err}");
        assert!(err.to_string().contains("roundtrip"), "{err}");
    }

    /// A memory-free module compiles fine under `Absent`: the policy refuses
    /// only what actually needs memory.
    #[test]
    fn a_memory_free_module_compiles_with_no_memory_at_all() {
        let policy = WasmModulePolicy {
            memory: WasmMemoryPolicy::Absent,
            ..WasmModulePolicy::closed()
        };
        let bytes =
            compile_module_with_policy_and_license(&sum_to_module(), &policy, &permit_unlicensed())
                .unwrap();
        assert_wasm_header(&bytes);
        // Byte-identical to the closed compile: neither emits a memory.
        assert_eq!(
            bytes,
            compile_module_with_license(&sum_to_module(), &permit_unlicensed()).unwrap()
        );
    }

    /// A body-less function is a declaration: refused by the closed lane,
    /// bound to a host import by the island lane.
    #[test]
    fn a_declaration_is_refused_closed_and_imported_by_an_island() {
        let declaration_module = || {
            let mut mb = ModuleBuilder::new("decl");
            let ft = mb.add_func_type(vec![Ty::I32], vec![Ty::I32]);
            mb.function("host_fn", ft).build();
            wasm32(mb.build().expect("ModuleBuilder::build: test fixture"))
        };
        let err =
            compile_module_with_license(&declaration_module(), &permit_unlicensed()).unwrap_err();
        assert!(
            matches!(err, WasmLowerError::UnboundDeclaration(_)),
            "{err}"
        );
        assert!(err.to_string().contains("host_fn"), "{err}");

        let policy = WasmModulePolicy {
            func_imports: WasmFuncImportPolicy::FromModule(island_host_namespace("decl")),
            ..WasmModulePolicy::closed()
        };
        let (bytes, ev) = compile_module_with_evidence_policy_and_license(
            &declaration_module(),
            &policy,
            &permit_unlicensed(),
        )
        .unwrap();
        assert_wasm_header(&bytes);
        assert_eq!(ev.host_contract, vec!["func trust:island/decl@1.host_fn"]);
    }

    /// A non-C declaration is refused at the import boundary too — the
    /// convention guard covers imports, not only defined functions.
    #[test]
    fn refuses_a_non_c_declaration_import() {
        let mut mb = ModuleBuilder::new("decl_conv");
        let ft = mb.add_func_type(vec![Ty::I32], vec![Ty::I32]);
        mb.function("host_fn", ft).build();
        let mut module = wasm32(mb.build().expect("ModuleBuilder::build: test fixture"));
        module.functions[0].calling_conv = CallingConv::Swift;

        let policy = WasmModulePolicy {
            func_imports: WasmFuncImportPolicy::FromModule(island_host_namespace("decl_conv")),
            ..WasmModulePolicy::closed()
        };
        let err = compile_module_with_policy_and_license(&module, &policy, &permit_unlicensed())
            .unwrap_err();
        assert!(
            matches!(err, WasmLowerError::UnsupportedCallingConv(_)),
            "{err}"
        );
        assert!(err.to_string().contains("host_fn"), "{err}");
    }

    // -----------------------------------------------------------------------
    // trust-ir v41 contract surface on the wasm lane: the target-neutral
    // refusals are the native adapter's own (shared gate), the two wasm
    // clauses are this lane's, and what is CONSUMED is pinned by bytes.
    // -----------------------------------------------------------------------

    /// `v41_call_module` with `entry`'s call to `helper` replaced by a trust-ir
    /// v53 non-propagating call boundary (`indirect`: through a `FnDef`
    /// constant of `helper`'s signature).
    fn v53_call_boundary_module(indirect: bool) -> Module {
        let mut module = v41_call_module(trust_ir::Linkage::External, true);
        let helper = module
            .functions
            .iter()
            .position(|f| f.name == "helper")
            .expect("helper");
        let callee = FuncId::new(u32::try_from(helper).expect("function index"));
        let sig = module.functions[helper].ty;
        let entry = module
            .functions
            .iter_mut()
            .find(|f| f.name == "entry")
            .expect("entry");
        let body = &mut entry.blocks[0].body;
        let at = body
            .iter()
            .position(|n| matches!(n.inst, Inst::Call { .. }))
            .expect("entry calls helper");
        if indirect {
            let pointer = ValueId::new(1_000);
            body[at].inst = Inst::CallIndirectCannotUnwind {
                callee: pointer,
                sig,
                args: vec![],
                calling_conv: trust_ir::CallingConv::default(),
            };
            body.insert(
                at,
                trust_ir::InstrNode::new(Inst::Const {
                    ty: Ty::Func(sig),
                    value: Constant::FnDef(callee),
                })
                .with_result(pointer),
            );
        } else {
            body[at].inst = Inst::CallCannotUnwind {
                callee,
                args: vec![],
            };
        }
        module
    }

    /// trust-ir v53: both wasm lanes (closed module and object) and
    /// `lower_function` refuse a non-propagating call boundary BY NAME, as
    /// the shared floor does; the same module with an ordinary call compiles.
    #[test]
    fn v53_call_unwind_boundaries_are_refused_by_name_on_every_wasm_entry() {
        let control = v41_call_module(trust_ir::Linkage::External, true);
        compile_module_with_license(&control, &permit_unlicensed())
            .expect("the ordinary-call neighbour compiles");
        compile_object_with_license(&control, &permit_unlicensed())
            .expect("the ordinary-call neighbour compiles as an object");
        for (indirect, construct) in [
            (false, "Inst::CallCannotUnwind"),
            (true, "Inst::CallIndirectCannotUnwind"),
        ] {
            let module = v53_call_boundary_module(indirect);
            let native = trust_cg_lower::reject_unconsumed_v41_target_neutral_surface(&module)
                .expect_err(construct)
                .to_string();
            assert!(native.contains(construct), "{construct}: {native}");
            let policy = WasmModulePolicy::closed();
            let entry_fn = module
                .functions
                .iter()
                .find(|f| f.name == "entry")
                .expect("entry");
            for (entry, result) in [
                (
                    "compile_module",
                    compile_module_with_license(&module, &permit_unlicensed()).map(drop),
                ),
                (
                    "compile_module_with_policy",
                    compile_module_with_policy_and_license(&module, &policy, &permit_unlicensed())
                        .map(drop),
                ),
                (
                    "compile_module_with_evidence",
                    compile_module_with_evidence_policy_and_license(
                        &module,
                        &WasmModulePolicy::closed(),
                        &permit_unlicensed(),
                    )
                    .map(drop),
                ),
                (
                    "compile_object",
                    compile_object_with_license(&module, &permit_unlicensed()).map(drop),
                ),
                (
                    "lower_function",
                    lower_function_with_license(
                        &mut WasmModule::new(),
                        entry_fn,
                        &module,
                        WasmFunctionEnv::empty(),
                        &permit_unlicensed(),
                    )
                    .map(drop),
                ),
            ] {
                match result.expect_err(entry) {
                    WasmLowerError::ContractSurface(detail) => {
                        assert_eq!(detail, native, "{entry}: {construct}");
                    }
                    other => panic!("{entry}: wrong refusal for {construct}: {other}"),
                }
            }
            // A detached function the module does not hold reaches the lane's
            // own per-function scan, which names the construct too.
            let detached = entry_fn.clone();
            let error = lower_function_with_license(
                &mut WasmModule::new(),
                &detached,
                &control,
                WasmFunctionEnv::empty(),
                &permit_unlicensed(),
            )
            .expect_err("a detached boundary must be refused");
            assert!(
                matches!(&error, WasmLowerError::UnsupportedInst(text) if text.contains(construct)),
                "{construct}: {error}"
            );
        }
    }

    /// `f: (ty) -> ty` returning `op ty %0`, pinned to wasm32.
    fn unop_module(op: UnOp, ty: Ty) -> Module {
        let mut mb = ModuleBuilder::new("m");
        let ft = mb.add_func_type(vec![ty.clone()], vec![ty.clone()]);
        let mut fb = mb.function("f", ft);
        let entry = fb.create_block();
        let x = fb.add_block_param(entry, ty.clone());
        fb.switch_to_block(entry);
        let r = fb.unop(op, ty, x);
        fb.ret(vec![r]);
        fb.build();
        wasm32(mb.build().expect("ModuleBuilder::build: test fixture"))
    }

    /// trust-ir WS2.21 (`UnOpNotOnScalarBool`, the must-refuse row
    /// `unop_not_scalar_bool`): `not bool` is refused BY NAME on every wasm
    /// entry, before lowering, since the integer `x ^ -1` would leave -1/-2 in a
    /// `Bool`. `Neg`/`CtPop` at `Bool` are refused with it (the native
    /// adapter's admission). The integer neighbours still compile.
    #[test]
    fn integer_unops_at_a_non_integer_type_are_refused_by_name_on_every_wasm_entry() {
        for ty in [Ty::I8, Ty::I32, Ty::U64, Ty::I128] {
            for op in [UnOp::Not, UnOp::Neg, UnOp::CtPop] {
                let module = unop_module(op, ty.clone());
                compile_module_with_license(&module, &permit_unlicensed())
                    .unwrap_or_else(|e| panic!("{op:?} {ty:?}: {e}"));
                compile_object_with_license(&module, &permit_unlicensed())
                    .unwrap_or_else(|e| panic!("{op:?} {ty:?} object: {e}"));
            }
        }
        // WS7.3: the module entries run trust-ir's codegen admission first,
        // which refuses each of these by its own finding before this lane's
        // scan: `not bool` by name, `neg`/`ctpop` at `bool` as integer-only.
        let admission_not = |finding: &trust_ir_build::ValidationError| {
            matches!(
                finding,
                trust_ir_build::ValidationError::UnOpNotOnScalarBool { .. }
            )
        };
        let admission_integer_only = |spelling: &'static str| {
            move |finding: &trust_ir_build::ValidationError| {
                matches!(
                    finding,
                    trust_ir_build::ValidationError::BinOpRequiresInteger { op, ty, .. }
                        if op == spelling && ty == "bool"
                )
            }
        };
        let admission_neg = admission_integer_only("neg");
        let admission_ctpop = admission_integer_only("ctpop");
        let cases: [(
            UnOp,
            &str,
            &dyn Fn(&trust_ir_build::ValidationError) -> bool,
        ); 3] = [
            (UnOp::Not, "UnOpNotOnScalarBool", &admission_not),
            (UnOp::Neg, "UnOp::Neg declared type Bool", &admission_neg),
            (
                UnOp::CtPop,
                "UnOp::CtPop declared type Bool",
                &admission_ctpop,
            ),
        ];
        for (op, needle, admission_finding) in cases {
            let module = unop_module(op, Ty::Bool);
            let policy = WasmModulePolicy::closed();
            let func = &module.functions[0];
            for (entry, result) in [
                (
                    "compile_module",
                    compile_module_with_license(&module, &permit_unlicensed()).map(drop),
                ),
                (
                    "compile_module_with_policy",
                    compile_module_with_policy_and_license(&module, &policy, &permit_unlicensed())
                        .map(drop),
                ),
                (
                    "compile_module_with_evidence",
                    compile_module_with_evidence_policy_and_license(
                        &module,
                        &WasmModulePolicy::closed(),
                        &permit_unlicensed(),
                    )
                    .map(drop),
                ),
                (
                    "compile_object",
                    compile_object_with_license(&module, &permit_unlicensed()).map(drop),
                ),
                (
                    "lower_function",
                    lower_function_with_license(
                        &mut WasmModule::new(),
                        func,
                        &module,
                        WasmFunctionEnv::empty(),
                        &permit_unlicensed(),
                    )
                    .map(drop),
                ),
            ] {
                match result.expect_err(entry) {
                    WasmLowerError::UnsupportedInst(text)
                        if entry == "lower_function" && text.contains(needle) => {}
                    WasmLowerError::InvalidTrustIr(refusal)
                        if entry != "lower_function" && refusal.any(admission_finding) => {}
                    other => panic!("{entry}: wrong refusal for {op:?} bool: {other}"),
                }
            }
        }
    }

    /// `entry: () -> i64` calling `helper: () -> i64`; `helper` carries a body
    /// returning 9 when `helper_has_body`, and gets `helper_linkage`.
    fn v41_call_module(helper_linkage: trust_ir::Linkage, helper_has_body: bool) -> Module {
        let mut mb = ModuleBuilder::new("v41");
        let ft = mb.add_func_type(vec![], vec![Ty::I64]);
        let helper = {
            let mut fb = mb.function("helper", ft);
            if helper_has_body {
                let e = fb.create_block();
                fb.switch_to_block(e);
                let c = fb.iconst(Ty::I64, 9);
                fb.ret(vec![c]);
            }
            fb.build()
        };
        let mut fb = mb.function("entry", ft);
        let e = fb.create_block();
        fb.switch_to_block(e);
        let r = fb.call(helper, vec![]);
        fb.ret(vec![r]);
        fb.build();
        let mut module = wasm32(mb.build().expect("ModuleBuilder::build: test fixture"));
        module
            .functions
            .iter_mut()
            .find(|f| f.name == "helper")
            .expect("helper")
            .linkage = helper_linkage;
        module
    }

    /// `read: () -> u32` loading the module global `TABLE`, which gets `global`'s
    /// linkage/visibility/retained/section from the caller.
    fn v41_global_module(mutate: impl FnOnce(&mut trust_ir::Global)) -> Module {
        let mut mb = ModuleBuilder::new("v41");
        let mut global = trust_ir::Global {
            name: "TABLE".to_string(),
            ty: Ty::U32,
            mutable: false,
            initializer: Some(Constant::Int(0x1A2B_3C4D)),
            linkage: trust_ir::Linkage::Internal,
            tls: None,
            align: None,
            section: None,
            visibility: trust_ir::Visibility::Default,
            retained: false,
        };
        mutate(&mut global);
        mb.add_global(global);
        let ft = mb.add_func_type(vec![], vec![Ty::U32]);
        let mut fb = mb.function("read", ft);
        let e = fb.create_block();
        fb.switch_to_block(e);
        let p = fb.global_addr(trust_ir::value::GlobalId::new(0));
        let v = fb.load(Ty::U32, p);
        fb.ret(vec![v]);
        fb.build();
        wasm32(mb.build().expect("ModuleBuilder::build: test fixture"))
    }

    /// `v41_global_module` whose `TABLE` is `[u32; len]` spelled
    /// `splat[ value; len ]` (trust-ir v50).
    fn splat_global_module(len: u64, value: i128) -> Module {
        let mut module = v41_global_module(|_| {});
        let elem = module
            .add_type(Ty::U32)
            .expect("Module::add_type: test fixture");
        let global = &mut module.globals[0];
        global.ty = Ty::Array(elem, len);
        global.initializer = Some(Constant::Splat {
            elem: Box::new(Constant::Int(value)),
            len,
        });
        module
    }

    /// trust-ir v50: a splat global's data image is written once per
    /// element, by a doubling copy, into a fallibly reserved buffer
    /// ([`layout::const_image`]); every address in the element is recorded
    /// once per lane. A zero splat is BSS whatever its length (its image is
    /// never built), and a global the wasm32 address space cannot hold is
    /// refused from its layout before any image is built (zero or not): one
    /// whose size the 32-bit layout cannot describe by the layout itself, one
    /// that fits the layout but not the space above the static-data base by
    /// [`place_static_data`].
    #[test]
    fn splat_global_image_scales_with_its_output_and_refuses_what_it_cannot_hold() {
        let image = |module: &Module| {
            let global = &module.globals[0];
            layout::const_image(module, &global.ty, global.initializer.as_ref().unwrap())
        };
        let zero_splat = |module: &Module| {
            let global = &module.globals[0];
            layout::is_zero_splat(module, &global.ty, global.initializer.as_ref().unwrap())
        };
        let small = splat_global_module(5, 0x0102_0304);
        let small_image = image(&small).unwrap();
        assert_eq!(
            small_image.bytes,
            [4u8, 3, 2, 1].repeat(5),
            "the lane, repeated"
        );
        assert!(small_image.refs.is_empty());
        assert!(!zero_splat(&small).unwrap());
        assert!(zero_splat(&splat_global_module(5, 0)).unwrap());
        assert!(zero_splat(&splat_global_module(1 << 20, 0)).unwrap());

        // An address in the element is one relocation per lane.
        let mut fn_table = v41_global_module(|_| {});
        let ptr = fn_table
            .add_type(Ty::Ptr)
            .expect("Module::add_type: test fixture");
        let read = fn_table.functions[0].id;
        fn_table.globals[0].ty = Ty::Array(ptr, 3);
        fn_table.globals[0].initializer = Some(Constant::Splat {
            elem: Box::new(Constant::FnDef(read)),
            len: 3,
        });
        let refs = image(&fn_table).unwrap().refs;
        assert_eq!(
            refs,
            [0u32, 4, 8]
                .map(|at| (at, layout::ImageRef::Func(read)))
                .to_vec()
        );

        // 2^63 bytes of u32 lanes: the 32-bit layout refuses it, so no image
        // is ever reserved.
        let huge = 1u64 << 61;
        for value in [0, 7] {
            let error = image(&splat_global_module(huge, value)).unwrap_err();
            assert!(
                matches!(&error, WasmLowerError::UnsupportedType(message)
                    if message.contains("larger than the wasm32 space")),
                "value {value}: {error}"
            );
        }

        // Through the lowering: the small table is one 20-byte segment; an
        // 8 GiB table (zero or not) has no wasm32 layout, and a 4 GiB - 4
        // table fits the layout but runs past the address space above the
        // static-data base, both refused before its image exists.
        let bytes = compile_module_with_license(&small, &permit_unlicensed()).unwrap();
        assert!(
            bytes.windows(20).any(|w| w == [4u8, 3, 2, 1].repeat(5)),
            "the data segment carries the table"
        );
        for value in [0, 7] {
            let error = compile_module_with_license(
                &splat_global_module(1 << 31, value),
                &permit_unlicensed(),
            )
            .unwrap_err();
            assert!(
                matches!(&error, WasmLowerError::UnsupportedType(message)
                    if message.contains("larger than the wasm32 space")),
                "value {value}: {error}"
            );
            let error = compile_module_with_license(
                &splat_global_module((1 << 30) - 1, value),
                &permit_unlicensed(),
            )
            .unwrap_err();
            assert!(
                matches!(&error, WasmLowerError::StaticDataOverflow(message)
                    if message.contains("runs past the wasm32 address space")),
                "value {value}: {error}"
            );
        }
    }

    fn v41_obligation(
        kind: trust_ir::proof::ObligationKind,
        status: trust_ir::proof::ProofStatus,
    ) -> trust_ir::proof::ProofObligation {
        trust_ir::proof::ProofObligation {
            id: trust_ir::ProofId::new(0),
            kind,
            status,
            description: "hand-built".to_string(),
            formula: None,
            function: Some(FuncId::new(0)),
            source: None,
            site: None,
            spec: None,
        }
    }

    /// An `available_externally` FUNCTION is a declaration for this lane
    /// exactly as for the native adapter: its body is NEVER emitted. Under the
    /// closed import policy that is an unbound declaration (refused); under a
    /// host import policy it becomes an import, byte-identical to the module
    /// where the helper is a bodyless `External` declaration.
    #[test]
    fn v41_available_externally_function_is_never_emitted_on_wasm() {
        use trust_ir::Linkage;
        let bodied = v41_call_module(Linkage::AvailableExternally, true);
        let err = compile_module_with_license(&bodied, &permit_unlicensed()).unwrap_err();
        assert!(
            matches!(err, WasmLowerError::UnboundDeclaration(_)),
            "{err}"
        );
        assert!(err.to_string().contains("helper"), "{err}");
        assert!(err.to_string().contains("available_externally"), "{err}");

        let host = island_host_namespace("v41");
        let policy = WasmModulePolicy {
            func_imports: WasmFuncImportPolicy::FromModule(host.clone()),
            ..WasmModulePolicy::closed()
        };
        let imported =
            compile_module_with_policy_and_license(&bodied, &policy, &permit_unlicensed()).unwrap();
        let declared = compile_module_with_policy_and_license(
            &v41_call_module(Linkage::External, false),
            &policy,
            &permit_unlicensed(),
        )
        .unwrap();
        assert_eq!(
            imported, declared,
            "an available_externally body must leave no trace: the module must equal the \
             one whose helper is a bodyless declaration"
        );
        // The helper is bound as an IMPORT from the host namespace — the
        // namespace string is in the import section — and only there.
        let names_host = |bytes: &[u8]| bytes.windows(host.len()).any(|w| w == host.as_bytes());
        assert!(
            names_host(&imported),
            "the helper must be imported from {host}"
        );
        // The control: a real `External` definition of the same helper is a
        // different module that imports nothing.
        let defined = compile_module_with_policy_and_license(
            &v41_call_module(Linkage::External, true),
            &policy,
            &permit_unlicensed(),
        )
        .unwrap();
        assert_ne!(defined, declared);
        assert!(!names_host(&defined), "a defined helper imports nothing");
    }

    /// An `available_externally` GLOBAL is a cross-object import, and this
    /// lane has no data-import channel — every global is an absolute
    /// linear-memory address. Refused rather than emitted as a definition.
    #[test]
    fn v41_available_externally_global_is_refused_on_wasm() {
        let err = compile_module_with_license(
            &v41_global_module(|g| {
                g.linkage = trust_ir::Linkage::AvailableExternally;
            }),
            &permit_unlicensed(),
        )
        .unwrap_err();
        assert!(matches!(err, WasmLowerError::ContractSurface(_)), "{err}");
        assert!(err.to_string().contains("TABLE"), "{err}");
        assert!(err.to_string().contains("available_externally"), "{err}");

        // Control: the same global as an `Internal` definition compiles and
        // its byte image ships in a data segment.
        let bytes =
            compile_module_with_license(&v41_global_module(|_| {}), &permit_unlicensed()).unwrap();
        assert!(bytes.windows(4).any(|w| w == [0x4d, 0x3c, 0x2b, 0x1a]));
    }

    /// Every target-neutral refusal of the native adapter reaches this lane
    /// through the shared gate. One construct per module; the shared gate's
    /// own message is carried verbatim.
    #[test]
    fn v41_target_neutral_refusals_reach_the_wasm_lane() {
        use trust_ir::proof::{ObligationKind, ProofCertificate, ProofEvidence, ProofStatus};
        use trust_ir::{ExternRef, Linkage, ModuleImport, ProofId, Visibility};

        let mut asm = v41_call_module(Linkage::External, true);
        asm.global_asm.push(".globl nothing".to_string());

        let mut naked = v41_call_module(Linkage::External, true);
        naked.functions[0].attrs.naked = true;

        let weak_undef_fn = v41_call_module(Linkage::ExternalWeak, false);

        let weak_undef_global = v41_global_module(|g| {
            g.linkage = Linkage::ExternalWeak;
            g.initializer = None;
        });

        // A MALFORMED section name is refused by the shared floor on every
        // lane; a well-formed one is a wasm-lane refusal (tested below).
        let sectioned = v41_global_module(|g| g.section = Some("has space".to_string()));

        let hidden_import = v41_global_module(|g| {
            g.linkage = Linkage::External;
            g.initializer = None;
            g.visibility = Visibility::Hidden;
        });

        // `Discharged`, not `Certified`: a `Certified` row with no CleanCic
        // certificate is refused first by trust-ir's codegen admission
        // (`CertifiedWithoutCleanCic`), which every entry runs before this
        // floor.
        let mut terminated = v41_call_module(Linkage::External, true);
        terminated.proof_obligations.push(v41_obligation(
            ObligationKind::Termination,
            ProofStatus::Discharged,
        ));

        let mut inherited = v41_call_module(Linkage::External, true);
        inherited.proof_obligations.push(v41_obligation(
            ObligationKind::MemorySafety,
            ProofStatus::Pending,
        ));
        let import = inherited
            .intern_import(ModuleImport::new(
                "sibling",
                trust_ir::proof::ProofDigest::zero(),
            ))
            .expect("Module::intern_import: test fixture");
        inherited.proof_certificates.push(ProofCertificate {
            obligation: ProofId::new(0),
            prover: "hand".to_string(),
            evidence: ProofEvidence::InheritedFromCallee {
                callee: FuncId::new(0),
                obligation: ProofId::new(0),
                external: Some(ExternRef::new(import, "sibling_fn")),
            },
            assurance: None,
        });

        for (what, module, needle) in [
            ("global_asm", asm, "global_asm!"),
            ("naked", naked, "#[naked]"),
            ("external_weak function", weak_undef_fn, "helper"),
            ("external_weak global", weak_undef_global, "TABLE"),
            ("malformed section", sectioned, "has space"),
            ("import visibility", hidden_import, "TABLE"),
            (
                "completed Termination obligation",
                terminated,
                "termination",
            ),
            ("external evidence inheritance", inherited, "sibling_fn"),
        ] {
            let err = compile_module_with_license(&module, &permit_unlicensed())
                .err()
                .unwrap_or_else(|| panic!("{what} must be refused on wasm"));
            assert!(
                matches!(err, WasmLowerError::ContractSurface(_)),
                "{what}: {err}"
            );
            let text = err.to_string();
            assert!(text.contains("trust-ir v41"), "{what}: {text}");
            assert!(
                text.to_lowercase().contains(&needle.to_lowercase()),
                "{what}: expected {needle:?} in {text}"
            );
            // The refusal is the shared gate's own verdict, not a wasm
            // paraphrase of it.
            let native = trust_cg_lower::reject_unconsumed_v41_target_neutral_surface(&module)
                .expect_err(what)
                .to_string();
            assert!(text.ends_with(&native), "{what}: {text} vs {native}");
        }
    }

    /// Unproved summaries and DesignOnly specs: no proof authority is assumed.
    fn summary_and_spec_formula_cases(
        formula: &trust_ir::proof::ProofFormula,
    ) -> Vec<(trust_ir::proof::FormulaSite, Module)> {
        use trust_ir::proof::{FormulaSite, ProofFormula};
        use trust_ir::{FunctionSummary, SpecInvariant, SpecModule, SpecTemporal, TemporalForm};

        let mut cases = Vec::new();
        for (clause, summary) in [
            (
                "requires",
                FunctionSummary::new().requiring(formula.clone()),
            ),
            ("ensures", FunctionSummary::new().ensuring(formula.clone())),
            (
                "decreases",
                FunctionSummary::new().decreasing(formula.clone()),
            ),
        ] {
            let mut module = v41_call_module(trust_ir::Linkage::External, true);
            // The helper takes no arguments, so its empty formal list is exact.
            module.functions[0].summary = Some(summary);
            cases.push((
                FormulaSite::SummaryClause {
                    function: FuncId::new(0),
                    clause,
                    index: 0,
                },
                module,
            ));
        }
        let mut spec = SpecModule::design_only("formula_floor");
        spec.invariants
            .push(SpecInvariant::new("Invariant", "design predicate").with_typed(formula.clone()));
        let mut module = v41_call_module(trust_ir::Linkage::External, true);
        module.spec_modules.push(spec);
        cases.push((
            FormulaSite::SpecInvariant {
                machine: "formula_floor".into(),
                invariant: "Invariant".into(),
            },
            module,
        ));
        let other = ProofFormula::smtlib2("true", "Bool");
        for (property, form) in [
            ("Always", TemporalForm::Always(formula.clone())),
            ("Eventually", TemporalForm::Eventually(formula.clone())),
            (
                "LeadsToLeft",
                TemporalForm::LeadsTo(formula.clone(), other.clone()),
            ),
            (
                "LeadsToRight",
                TemporalForm::LeadsTo(other, formula.clone()),
            ),
            (
                "WeakFair",
                TemporalForm::WeakFair {
                    action: "Step".into(),
                    relation: Some(formula.clone()),
                },
            ),
            (
                "StrongFair",
                TemporalForm::StrongFair {
                    action: "Step".into(),
                    relation: Some(formula.clone()),
                },
            ),
        ] {
            let mut spec = SpecModule::design_only("formula_floor");
            spec.actions.push("Step".into());
            spec.temporal.push(SpecTemporal::new(property, form));
            let mut module = v41_call_module(trust_ir::Linkage::External, true);
            module.spec_modules.push(spec);
            cases.push((
                FormulaSite::SpecTemporal {
                    machine: "formula_floor".into(),
                    property: property.into(),
                },
                module,
            ));
        }
        cases
    }

    fn assert_formula_refused_on_every_wasm_entry(
        module: &Module,
        site: trust_ir::proof::FormulaSite,
    ) {
        let original = module.clone();
        let expected = trust_ir_build::ValidationError::FormulaTextsDisagree { site: site.clone() }
            .to_string();
        let native = trust_cg_lower::reject_unconsumed_v41_target_neutral_surface(module)
            .expect_err("contradictory formula must fail the shared floor");
        assert!(matches!(
            &native,
            trust_cg_lower::AdapterError::TrustIrAdmissionRefused { error } if error == &expected
        ));
        let policy = WasmModulePolicy::closed();
        // The fixtures carry no codegen license, which every DEFAULT wasm
        // entry refuses (WS7.5, DG-73); the formula floor is asserted through
        // each entry's explicit-license twin under a stated Permit, so the
        // verdict below can only be the formula's.
        for (entry, result) in [
            (
                "compile_module_with_policy_and_license(closed)",
                compile_module_with_policy_and_license(
                    module,
                    &WasmModulePolicy::closed(),
                    &permit_unlicensed(),
                )
                .map(drop),
            ),
            (
                "compile_module_with_policy_and_license",
                compile_module_with_policy_and_license(module, &policy, &permit_unlicensed())
                    .map(drop),
            ),
            (
                "compile_module_with_evidence_policy_and_license(closed)",
                compile_module_with_evidence_policy_and_license(
                    module,
                    &WasmModulePolicy::closed(),
                    &permit_unlicensed(),
                )
                .map(drop),
            ),
            (
                "compile_module_with_evidence_policy_and_license",
                compile_module_with_evidence_policy_and_license(
                    module,
                    &policy,
                    &permit_unlicensed(),
                )
                .map(drop),
            ),
            (
                "lower_function_with_license",
                lower_function_with_license(
                    &mut WasmModule::new(),
                    &module.functions[0],
                    module,
                    WasmFunctionEnv::empty(),
                    &permit_unlicensed(),
                )
                .map(drop),
            ),
        ] {
            // trust-ir's codegen admission, which every entry runs before
            // the shared floor (as the native entries do), states the same
            // finding in the same words.
            match result.expect_err(entry) {
                WasmLowerError::CodegenAdmission(detail) => {
                    assert_eq!(detail, native.to_string(), "{entry}: {site}");
                }
                other => panic!("{entry}: wrong formula refusal for {site}: {other}"),
            }
        }
        assert_eq!(module, &original, "{site}: do not repair the formula");
    }

    #[test]
    fn disagreeing_formula_texts_are_refused_on_every_wasm_entry() {
        use trust_ir::proof::{FormulaSite, ObligationKind, ProofFormula, ProofStatus};

        let mut formula = ProofFormula::smtlib2("(>= 0 5)", "Bool");
        formula.smtlib = Some("(>= 5 0)".into());
        for status in [ProofStatus::Pending, ProofStatus::Discharged] {
            let mut module = v41_call_module(trust_ir::Linkage::External, true);
            let mut claim = v41_obligation(ObligationKind::Postcondition, status);
            claim.formula = Some(formula.clone());
            module.proof_obligations.push(claim);
            assert_formula_refused_on_every_wasm_entry(
                &module,
                FormulaSite::Obligation(trust_ir::ProofId::new(0)),
            );
        }
        for (site, module) in summary_and_spec_formula_cases(&formula) {
            assert_formula_refused_on_every_wasm_entry(&module, site);
        }
    }

    #[test]
    fn detached_function_formula_texts_are_refused_before_wasm_emission() {
        use trust_ir::FunctionSummary;
        use trust_ir::proof::{FormulaSite, ProofFormula};

        let ir_module = v41_call_module(trust_ir::Linkage::External, true);
        assert!(ir_module.functions[0].summary.is_none());
        let mut seeded = WasmModule::new();
        lower_function_with_license(
            &mut seeded,
            &ir_module.functions[0],
            &ir_module,
            WasmFunctionEnv::empty(),
            &permit_unlicensed(),
        )
        .expect("module-owned helper is admissible");
        let before_bytes = seeded.finish();
        let before_count = seeded.func_count();
        let mut formula = ProofFormula::smtlib2("(>= 0 5)", "Bool");
        formula.smtlib = Some("(>= 5 0)".into());
        for (clause, summary) in [
            (
                "requires",
                FunctionSummary::new().requiring(formula.clone()),
            ),
            ("ensures", FunctionSummary::new().ensuring(formula.clone())),
            (
                "decreases",
                FunctionSummary::new().decreasing(formula.clone()),
            ),
        ] {
            // The module's original is still clean; only the actual supplied
            // function states two texts. Checking the module alone misses it.
            let mut actual = ir_module.functions[0].clone();
            actual.summary = Some(summary);
            let mut output = seeded.clone();
            let error = lower_function_with_license(
                &mut output,
                &actual,
                &ir_module,
                WasmFunctionEnv::empty(),
                &permit_unlicensed(),
            )
            .expect_err("detached summary must be checked before appending output");
            let expected = trust_cg_lower::AdapterError::TrustIrAdmissionRefused {
                error: trust_ir_build::ValidationError::FormulaTextsDisagree {
                    site: FormulaSite::SummaryClause {
                        function: actual.id,
                        clause,
                        index: 0,
                    },
                }
                .to_string(),
            }
            .to_string();
            // The single-function entry runs trust-ir's codegen admission
            // over the module with `actual` in place, before the shared floor.
            match error {
                WasmLowerError::CodegenAdmission(detail) => {
                    assert_eq!(detail, expected, "{clause}")
                }
                other => panic!("{clause}: wrong detached formula refusal: {other}"),
            }
            assert_eq!(
                output.func_count(),
                before_count,
                "{clause}: partial function emitted"
            );
            assert_eq!(
                output.finish(),
                before_bytes,
                "{clause}: output changed on refusal"
            );
            assert!(
                ir_module.functions[0].summary.is_none(),
                "do not repair the supplied module"
            );
        }
    }

    #[test]
    fn detached_consistent_formula_metadata_preserves_wasm_bytes() {
        use trust_ir::FunctionSummary;
        use trust_ir::proof::ProofFormula;

        let ir_module = v41_call_module(trust_ir::Linkage::External, true);
        let mut borrowed = WasmModule::new();
        let expected_index = lower_function_with_license(
            &mut borrowed,
            &ir_module.functions[0],
            &ir_module,
            WasmFunctionEnv::empty(),
            &permit_unlicensed(),
        )
        .expect("module-owned helper");
        let expected_bytes = borrowed.finish();
        let check = |label: &str, actual: &Function| {
            let mut output = WasmModule::new();
            assert_eq!(
                lower_function_with_license(
                    &mut output,
                    actual,
                    &ir_module,
                    WasmFunctionEnv::empty(),
                    &permit_unlicensed()
                )
                .expect(label),
                expected_index,
                "{label}: function index changed",
            );
            assert_eq!(
                output.finish(),
                expected_bytes,
                "{label}: metadata changed bytes"
            );
        };
        let equivalent = ir_module.functions[0].clone();
        check("equivalent detached clone", &equivalent);
        let consistent = ProofFormula::smtlib2("(>= 5 0)", "Bool");
        let mut absent = consistent.clone();
        absent.smtlib = None;
        let mut opaque = ProofFormula::new("test.opaque@1", "{\"predicate\":\"opaque\"}");
        opaque.smtlib = Some("(>= 5 0)".into());
        for formula in [&consistent, &absent, &opaque] {
            for (clause, summary) in [
                (
                    "requires",
                    FunctionSummary::new().requiring(formula.clone()),
                ),
                ("ensures", FunctionSummary::new().ensuring(formula.clone())),
                (
                    "decreases",
                    FunctionSummary::new().decreasing(formula.clone()),
                ),
            ] {
                let mut actual = equivalent.clone();
                actual.summary = Some(summary);
                let original = actual.clone();
                // An unproved carried summary is not an authority to assume
                // its opaque rendering or elide any of the actual body.
                check(clause, &actual);
                assert_eq!(actual, original, "{clause}: metadata was rewritten");
            }
        }
        assert!(ir_module.functions[0].summary.is_none());
    }

    #[test]
    fn consistent_and_opaque_formula_metadata_do_not_change_wasm_bytes() {
        use trust_ir::proof::{ObligationKind, ProofFormula, ProofStatus};

        // The lane's own bytes: the mid-end leaves a function a proof
        // obligation, summary or spec names alone (its inliner then keeps
        // `helper` called), so with it the carried metadata would change the
        // bytes for a reason unrelated to proof authority.
        let compile_module = |module: &Module| {
            compile_module_parts(
                module,
                &WasmModulePolicy::closed(),
                ClosedPolicyFit::AsGiven,
                &permit_unlicensed(),
                WasmOptOptions {
                    level: DEFAULT_OPT_LEVEL,
                    mid_end: false,
                },
            )
            .map(|parts| parts.bytes)
        };
        let control = v41_call_module(trust_ir::Linkage::External, true);
        let control_bytes = compile_module(&control).expect("unchanged control");
        let consistent = ProofFormula::smtlib2("(>= 5 0)", "Bool");
        let mut absent = consistent.clone();
        absent.smtlib = None;
        let mut opaque = ProofFormula::new("test.opaque@1", "{\"predicate\":\"opaque\"}");
        opaque.smtlib = Some("(>= 5 0)".into());
        for (label, formula) in [
            ("equal SMT-LIB rendering", &consistent),
            ("absent SMT-LIB rendering", &absent),
            ("opaque payload with rendering", &opaque),
        ] {
            // A `Discharged` row with no certificate is refused at ingestion
            // (WS7.3: trust-ir's `DischargedWithoutCertificate`), whatever its
            // formula carries; metadata never earns a discharge.
            let mut discharged = control.clone();
            let mut claim = v41_obligation(ObligationKind::Postcondition, ProofStatus::Discharged);
            claim.formula = Some(formula.clone());
            discharged.proof_obligations.push(claim);
            match compile_module(&discharged) {
                Err(WasmLowerError::InvalidTrustIr(refusal)) => assert!(
                    refusal.any(|finding| matches!(
                        finding,
                        trust_ir_build::ValidationError::DischargedWithoutCertificate { .. }
                    )),
                    "{label}: {refusal}"
                ),
                other => panic!("{label}: an uncertified discharge must be refused, got {other:?}"),
            }
        }
        {
            let status = ProofStatus::Pending;
            for (label, formula) in [
                ("equal SMT-LIB rendering", &consistent),
                ("absent SMT-LIB rendering", &absent),
                ("opaque payload with rendering", &opaque),
            ] {
                let mut module = control.clone();
                let mut claim = v41_obligation(ObligationKind::Postcondition, status);
                claim.formula = Some(formula.clone());
                module.proof_obligations.push(claim.clone());
                // These are carried, not grounded or promoted to proof authority.
                assert_eq!(
                    compile_module(&module).expect(label),
                    control_bytes,
                    "{label}"
                );
                lower_function_with_license(
                    &mut WasmModule::new(),
                    &module.functions[0],
                    &module,
                    WasmFunctionEnv::empty(),
                    &permit_unlicensed(),
                )
                .expect(label);
                assert_eq!(
                    module.proof_obligations[0], claim,
                    "{label}: preserve metadata"
                );
            }
        }
        for formula in [&consistent, &absent, &opaque] {
            for (site, module) in summary_and_spec_formula_cases(formula) {
                let original = module.clone();
                // DesignOnly metadata remains inert; this is not a Linked
                // spec admission claim or a use of an opaque rendering as proof.
                assert_eq!(
                    compile_module_with_policy_and_license(
                        &module,
                        &WasmModulePolicy::closed(),
                        &permit_unlicensed()
                    )
                    .expect("consistent carrier"),
                    control_bytes,
                    "{site}"
                );
                lower_function_with_license(
                    &mut WasmModule::new(),
                    &module.functions[0],
                    &module,
                    WasmFunctionEnv::empty(),
                    &permit_unlicensed(),
                )
                .expect("consistent carrier");
                assert_eq!(module, original, "{site}: preserve metadata");
            }
        }
    }

    #[test]
    fn v42_unused_declared_tuple_layout_is_refused_on_wasm() {
        let mut module = v41_call_module(trust_ir::Linkage::External, true);
        let tuple_type = module
            .add_type(Ty::Tuple(vec![Ty::U8, Ty::U8]))
            .expect("Module::add_type: test fixture");
        module.tuple_layouts.push(trust_ir::TupleLayoutDescriptor {
            tuple_type,
            size: 2,
            align: 1,
            field_offsets: vec![1, 0],
        });
        module
            .validate_tuple_layouts()
            .expect("valid reordered layout");
        // A reordered row disagrees with the native byte path's
        // declaration-order layout, so the SHARED floor refuses it (WS7.7).
        let err = compile_module_with_license(&module, &permit_unlicensed())
            .expect_err("declared layout is not consumed");
        assert!(matches!(err, WasmLowerError::ContractSurface(_)));
        let native = trust_cg_lower::reject_unconsumed_v41_target_neutral_surface(&module)
            .expect_err("shared layout refusal");
        assert!(matches!(
            native,
            trust_cg_lower::AdapterError::DeclaredTupleLayoutDisagrees { .. }
        ));
        assert!(err.to_string().ends_with(&native.to_string()));
        // A row that AGREES passes the shared floor, but this lane does not
        // lay tuples out as the native byte path does, so it still refuses.
        module.tuple_layouts[0].field_offsets = vec![0, 1];
        trust_cg_lower::reject_unconsumed_v41_target_neutral_surface(&module)
            .expect("the shared floor admits an agreeing row");
        let err = compile_module_with_license(&module, &permit_unlicensed())
            .expect_err("wasm does not consume declared layouts");
        let lane = trust_cg_lower::refuse_declared_tuple_layouts_outside_pointer_transport(&module)
            .expect_err("wasm lane refusal");
        assert!(matches!(
            lane,
            trust_cg_lower::AdapterError::DeclaredTupleLayoutUnsupported { layouts: 1, .. }
        ));
        assert!(err.to_string().ends_with(&lane.to_string()));
        module.tuple_layouts.clear();
        compile_module_with_license(&module, &permit_unlicensed())
            .expect("unchanged empty-layout control");
    }

    #[test]
    fn completeness_claims_are_refused_on_every_wasm_entry() {
        use trust_ir::{ModuleCompleteness, UnloweredRow};

        let control = v41_call_module(trust_ir::Linkage::External, true);
        assert_eq!(control.completeness, None);
        compile_module_with_license(&control, &permit_unlicensed()).expect("None remains no claim");
        lower_function_with_license(
            &mut WasmModule::new(),
            &control.functions[0],
            &control,
            WasmFunctionEnv::empty(),
            &permit_unlicensed(),
        )
        .expect("claim-less single-function control");
        for claim in [
            ModuleCompleteness::Complete,
            ModuleCompleteness::Partial(vec![UnloweredRow {
                symbol: "missing".into(),
                display_path: None,
                reason: "body was not lowered".into(),
            }]),
            ModuleCompleteness::Partial(vec![]),
        ] {
            let mut module = control.clone();
            module.completeness = Some(claim.clone());
            let native = trust_cg_lower::reject_unconsumed_v41_target_neutral_surface(&module)
                .expect_err("completeness has no native binary carrier");
            assert!(matches!(
                &native,
                trust_cg_lower::AdapterError::ModuleCompletenessUnsupported { .. }
            ));
            let policy = WasmModulePolicy::closed();
            for (entry, result) in [
                (
                    "compile_module",
                    compile_module_with_license(&module, &permit_unlicensed()).map(drop),
                ),
                (
                    "compile_module_with_policy",
                    compile_module_with_policy_and_license(&module, &policy, &permit_unlicensed())
                        .map(drop),
                ),
                (
                    "compile_module_with_evidence",
                    compile_module_with_evidence_policy_and_license(
                        &module,
                        &WasmModulePolicy::closed(),
                        &permit_unlicensed(),
                    )
                    .map(drop),
                ),
                (
                    "compile_module_with_evidence_and_policy",
                    compile_module_with_evidence_policy_and_license(
                        &module,
                        &policy,
                        &permit_unlicensed(),
                    )
                    .map(drop),
                ),
                (
                    "lower_function",
                    lower_function_with_license(
                        &mut WasmModule::new(),
                        &module.functions[0],
                        &module,
                        WasmFunctionEnv::empty(),
                        &permit_unlicensed(),
                    )
                    .map(drop),
                ),
            ] {
                let error = result.expect_err(entry);
                match error {
                    WasmLowerError::ContractSurface(detail) => {
                        assert_eq!(detail, native.to_string(), "{entry}: {claim:?}");
                    }
                    other => panic!("{entry}: wrong refusal for {claim:?}: {other}"),
                }
            }
            assert_eq!(module.completeness, Some(claim), "claim must not be erased");
        }
        assert_eq!(control.completeness, None, "no implicit completeness claim");
    }

    /// A well-formed explicit section passes the shared floor (the native
    /// AArch64 emitters place it) but has no wasm spelling: refused here.
    #[test]
    fn v41_well_formed_section_is_refused_on_wasm() {
        let module = v41_global_module(|g| g.section = Some(".init_array".to_string()));
        trust_cg_lower::reject_unconsumed_v41_target_neutral_surface(&module)
            .expect("a well-formed name passes the shared floor");
        let err = compile_module_with_license(&module, &permit_unlicensed())
            .expect_err("wasm has no object sections");
        assert!(matches!(err, WasmLowerError::ContractSurface(_)), "{err}");
        let text = err.to_string();
        assert!(
            text.contains("TCG-SECTION-TARGET") && text.contains(".init_array"),
            "{text}"
        );
    }

    /// This lane models NO wasm feature, so every `target_features` entry is
    /// refused — including one the native AArch64 lane would accept.
    #[test]
    fn v41_any_target_feature_is_refused_on_wasm() {
        for feature in ["simd128", "neon"] {
            let mut module = v41_call_module(trust_ir::Linkage::External, true);
            module.functions[1].attrs.target_features = vec![feature.to_string()];
            let err = compile_module_with_license(&module, &permit_unlicensed()).unwrap_err();
            assert!(matches!(err, WasmLowerError::ContractSurface(_)), "{err}");
            assert!(err.to_string().contains(feature), "{err}");
            assert!(err.to_string().contains("entry"), "{err}");
        }
    }

    /// What this lane CONSUMES, pinned by bytes. Visibility and `retained` on
    /// a global DEFINITION are vacuous here (no data symbol is ever emitted,
    /// nothing is ever stripped), so the module is byte-identical to the
    /// default one; the ODR linkage kinds are definitions exactly like their
    /// non-ODR forms.
    #[test]
    fn v41_consumed_surface_on_wasm_is_byte_pinned() {
        use trust_ir::{Linkage, Visibility};
        let baseline =
            compile_module_with_license(&v41_global_module(|_| {}), &permit_unlicensed()).unwrap();
        for (what, mutate) in [
            (
                "hidden",
                Box::new(|g: &mut trust_ir::Global| g.visibility = Visibility::Hidden)
                    as Box<dyn FnOnce(&mut trust_ir::Global)>,
            ),
            (
                "protected",
                Box::new(|g: &mut trust_ir::Global| g.visibility = Visibility::Protected),
            ),
            (
                "retained",
                Box::new(|g: &mut trust_ir::Global| g.retained = true),
            ),
            (
                "weak_odr",
                Box::new(|g: &mut trust_ir::Global| g.linkage = Linkage::WeakOdr),
            ),
            (
                "linkonce_odr",
                Box::new(|g: &mut trust_ir::Global| g.linkage = Linkage::LinkOnceOdr),
            ),
        ] {
            let bytes =
                compile_module_with_license(&v41_global_module(mutate), &permit_unlicensed())
                    .unwrap();
            assert_eq!(bytes, baseline, "{what} global definition");
        }

        for (odr, plain) in [
            (Linkage::WeakOdr, Linkage::Weak),
            (Linkage::LinkOnceOdr, Linkage::LinkOnce),
        ] {
            let odr_bytes =
                compile_module_with_license(&v41_call_module(odr, true), &permit_unlicensed())
                    .unwrap();
            let plain_bytes =
                compile_module_with_license(&v41_call_module(plain, true), &permit_unlicensed())
                    .unwrap();
            assert_eq!(odr_bytes, plain_bytes, "{odr:?} function vs {plain:?}");
            assert_wasm_header(&odr_bytes);
        }
    }
}
