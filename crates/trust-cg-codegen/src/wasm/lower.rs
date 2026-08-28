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
//! Fail-closed: irreducible / multi-entry loops and any out-of-subset
//! instruction are rejected explicitly, never mis-lowered.
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
//! `Bool` is a 1-bit unsigned member of the same family, but it is only ever
//! produced as a canonical `0`/`1` by `ICmp`/`FCmp`/`Const`, so it takes the
//! narrow path only where a cast makes its width observable.

use std::collections::{HashMap, HashSet};
use std::fmt;

use trust_ir::{
    BinOp, BlockId, CallingConv, CastOp, Constant, FCmpOp, FuncId, FuncTyId, Function, ICmpOp,
    Inst, Module, Ty, UnOp, ValueId,
};

/// Per-callee call target: its wasm function index and (optional) return type.
type CallTargets = HashMap<FuncId, (u32, Option<ValType>)>;
/// trust-ir signature → wasm type-section index (for `call_indirect`).
type SigTypes = HashMap<FuncTyId, u32>;
/// Module global → the absolute wasm32 address of its static-data slot.
type GlobalAddrs = HashMap<trust_ir::value::GlobalId, u32>;

use super::encode::{
    FuncBody, FuncType, GlobalInit, ValType, WASM_PAGE_BYTES, WasmEncodeError, WasmMemoryPolicy,
    WasmModule, emit_i32_const, emit_local_get, emit_memarg, emit_memory_grow, emit_memory_size,
    op, write_sleb128, write_uleb128,
};
use crate::jit_contract::{EvidenceStrength, ProofEvidenceVerdict};

/// Errors from lowering trust-ir to wasm. Fail-closed: anything outside the
/// supported subset is reported explicitly, never silently mis-lowered.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum WasmLowerError {
    /// A type with no wasm value-type mapping (in this slice).
    UnsupportedType(String),
    /// An instruction outside the supported subset.
    UnsupportedInst(String),
    /// Control flow outside the supported subset (irreducible, switch, …).
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
            UnsupportedMultiResultCall(m) => {
                write!(f, "unsupported multi-result call in wasm lowering: {m}")
            }
            MemoryUnavailable(m) => write!(f, "wasm memory policy provides no memory: {m}"),
            StackBaseUnavailable(m) => write!(f, "no negotiable wasm shadow-stack base: {m}"),
            UnboundDeclaration(m) => write!(f, "unbound trust-ir declaration: {m}"),
            FunctionIndexDrift(m) => write!(f, "wasm function index drift: {m}"),
            NarrowLegalization(m) => write!(f, "narrow value cannot be legalized to i32: {m}"),
            HostMemoryNotGranted(m) => write!(f, "host linear memory not granted: {m}"),
            UnsupportedConstantData(m) => write!(f, "global has no emittable byte image: {m}"),
            StaticDataOverflow(m) => write!(f, "static data does not fit linear memory: {m}"),
            Encode(e) => write!(f, "wasm module encoding refused: {e}"),
            StructuralInvariantRefuted(m) => write!(
                f,
                "wasm CFG structural invariant REFUTED on the emitted module: {m}"
            ),
        }
    }
}

impl std::error::Error for WasmLowerError {}

/// Map a trust-ir scalar type to a wasm value type. Sub-32-bit integers carry
/// in `i32` (module docs, "Invariant N"); pointer-like types are wasm32
/// addresses (i32).
fn valtype_of(ty: &Ty) -> Result<ValType, WasmLowerError> {
    match ty {
        Ty::I8 | Ty::U8 | Ty::I16 | Ty::U16 | Ty::I32 | Ty::U32 | Ty::Bool => Ok(ValType::I32),
        Ty::I64 | Ty::U64 => Ok(ValType::I64),
        Ty::F32 => Ok(ValType::F32),
        Ty::F64 => Ok(ValType::F64),
        Ty::Ptr | Ty::PtrConst(_) | Ty::PtrMut(_) | Ty::Ref(_) | Ty::RefMut(_) | Ty::Rc(_) => {
            Ok(ValType::I32)
        }
        other => Err(WasmLowerError::UnsupportedType(format!("{other:?}"))),
    }
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
        Ty::Ptr | Ty::PtrConst(_) | Ty::PtrMut(_) | Ty::Ref(_) | Ty::RefMut(_) | Ty::Rc(_) => {
            IntRepr::new(32, false, I32)
        }
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
/// [`int_repr_of`].
fn narrow_of(ty: &Ty) -> Option<IntRepr> {
    match ty {
        Ty::I8 | Ty::U8 | Ty::I16 | Ty::U16 => int_repr_of(ty),
        _ => None,
    }
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
fn align_up(n: u32, align: u32) -> u32 {
    (n + align - 1) & !(align - 1)
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

/// The trust-ir type produced by a result-bearing instruction.
///
/// The lowering needs the trust-ir type, not only its wasm carrier: a narrow
/// value's SIGNEDNESS is what fixes its canonical carrier form (invariant N),
/// and `valtype_of` has already erased it.
fn result_ty(inst: &Inst, module: &Module) -> Result<Ty, WasmLowerError> {
    let ty = match inst {
        Inst::BinOp { ty, .. } => ty.clone(),
        // Every supported UnOp (Neg/Not/CtPop, FNeg/FAbs/FSqrt/FCeil/FFloor/
        // FTrunc) returns a value of the operand type.
        Inst::UnOp { ty, .. } => ty.clone(),
        // wasm integer and float compares both yield an i32 0/1.
        Inst::ICmp { .. } | Inst::FCmp { .. } => Ty::Bool,
        Inst::Cast { dst_ty, .. } => dst_ty.clone(),
        // A function-pointer constant is a table index (a wasm32 address).
        Inst::Const {
            value: Constant::FnDef(_),
            ..
        } => Ty::Ptr,
        Inst::Const { ty, .. } => ty.clone(),
        // Pointers: a frame slot, a computed element address, a static-data
        // address.
        Inst::Alloca { .. } | Inst::GEP { .. } | Inst::GlobalAddr { .. } => Ty::Ptr,
        Inst::Load { ty, .. } => ty.clone(),
        Inst::Call { callee, .. } => {
            let ft = module
                .function_by_id(*callee)
                .and_then(|f| module.func_type(f.ty))
                .ok_or_else(|| {
                    WasmLowerError::UnsupportedInst(format!("Call to unknown {callee:?}"))
                })?;
            ft.returns.first().cloned().ok_or_else(|| {
                WasmLowerError::UnsupportedInst(format!(
                    "Call to {callee:?} returns no value but its result is used"
                ))
            })?
        }
        Inst::CallIndirect { sig, .. } => {
            let ft = module.func_type(*sig).ok_or_else(|| {
                WasmLowerError::UnsupportedInst(format!("unknown signature {sig:?}"))
            })?;
            ft.returns.first().cloned().ok_or_else(|| {
                WasmLowerError::UnsupportedInst(
                    "indirect call result used but signature returns void".to_string(),
                )
            })?
        }
        other => {
            return Err(WasmLowerError::UnsupportedInst(format!(
                "result-producing {other:?}"
            )));
        }
    };
    Ok(ty)
}

/// Run-length encode local declarations into wasm `(count, type)` runs.
fn run_length_encode(types: &[ValType]) -> Vec<(u32, ValType)> {
    let mut runs: Vec<(u32, ValType)> = Vec::new();
    for &vt in types {
        match runs.last_mut() {
            Some((count, last)) if *last == vt => *count += 1,
            _ => runs.push((1, vt)),
        }
    }
    runs
}

fn first_result(node: &trust_ir::InstrNode, func_name: &str) -> Result<ValueId, WasmLowerError> {
    node.results.first().copied().ok_or_else(|| {
        WasmLowerError::UnsupportedInst(format!("value op without result in `{func_name}`"))
    })
}

/// WebAssembly EH is not wired. Scan the complete function, including
/// unreachable blocks and zero-result nodes, before CFG/local lowering so no
/// incidental reachability or arity behavior can hide an EH instruction.
fn reject_unwired_eh_instructions(func: &Function) -> Result<(), WasmLowerError> {
    for block in &func.blocks {
        for node in &block.body {
            if matches!(
                node.inst,
                Inst::Invoke { .. } | Inst::LandingPad { .. } | Inst::Resume { .. }
            ) {
                return Err(WasmLowerError::UnsupportedInst(format!(
                    "{:?} in `{}` block {:?}: WebAssembly EH/LSDA/personality lowering is not wired",
                    node.inst, func.name, block.id
                )));
            }
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
/// * only `CallingConv::C` is lowered — the function's own convention and
///   every `call_indirect` edge are checked;
/// * multi-result calls are refused — the call lowering binds exactly one
///   result, so a call whose signature returns more than one value (or whose
///   SSA node binds more than one result) would leave operand-stack values
///   undropped and locals unset. TrustIr validates such calls; this backend
///   does not lower them yet.
fn reject_unsupported_call_contract(
    func: &Function,
    module: &Module,
) -> Result<(), WasmLowerError> {
    if func.calling_conv != CallingConv::C {
        return Err(WasmLowerError::UnsupportedCallingConv(format!(
            "function `{}` is declared {:?}; the WASM backend lowers only CallingConv::C",
            func.name, func.calling_conv,
        )));
    }
    for block in &func.blocks {
        for node in &block.body {
            match &node.inst {
                Inst::Call { callee, .. } => {
                    if node.results.len() > 1 {
                        return Err(WasmLowerError::UnsupportedMultiResultCall(format!(
                            "call to {callee:?} in `{}` binds {} results; wasm call lowering \
                             supports at most one",
                            func.name,
                            node.results.len(),
                        )));
                    }
                    if let Some(callee_fn) = module.function_by_id(*callee)
                        && let Some(ft) = module.func_type(callee_fn.ty)
                        && ft.returns.len() > 1
                    {
                        return Err(WasmLowerError::UnsupportedMultiResultCall(format!(
                            "call to `{}` in `{}` has {} return values; wasm call lowering \
                             supports at most one",
                            callee_fn.name,
                            func.name,
                            ft.returns.len(),
                        )));
                    }
                }
                Inst::CallIndirect {
                    sig, calling_conv, ..
                } => {
                    if *calling_conv != CallingConv::C {
                        return Err(WasmLowerError::UnsupportedCallingConv(format!(
                            "call_indirect in `{}` uses {calling_conv:?}; the WASM backend \
                             lowers only CallingConv::C",
                            func.name,
                        )));
                    }
                    if node.results.len() > 1 {
                        return Err(WasmLowerError::UnsupportedMultiResultCall(format!(
                            "call_indirect in `{}` binds {} results; wasm call lowering \
                             supports at most one",
                            func.name,
                            node.results.len(),
                        )));
                    }
                    if let Some(ft) = module.func_type(*sig)
                        && ft.returns.len() > 1
                    {
                        return Err(WasmLowerError::UnsupportedMultiResultCall(format!(
                            "call_indirect via {sig:?} in `{}` has {} return values; wasm call \
                             lowering supports at most one",
                            func.name,
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
}

/// Per-function lowering state.
struct Lowering<'a> {
    func: &'a Function,
    /// The enclosing trust-ir module, for type-layout queries (sizes/offsets).
    module: &'a Module,
    /// FuncId → (wasm function index, return type) for direct calls.
    call_targets: &'a CallTargets,
    /// trust-ir signature → wasm type index, for `call_indirect`.
    sig_types: &'a SigTypes,
    /// Module global → the absolute address of its static-data slot.
    global_addrs: &'a GlobalAddrs,
    block_index: HashMap<BlockId, usize>,
    /// Dominator-tree children, each sorted by rpo_index ascending.
    dom_children: Vec<Vec<usize>>,
    /// Block is the target of a back-edge (loop header).
    is_header: Vec<bool>,
    /// Block has ≥2 forward predecessors (merge / join).
    is_merge: Vec<bool>,
    /// Recorded back-edges (source, target).
    back_edges: HashSet<(usize, usize)>,
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
    /// Byte offset within the frame for each `Alloca` result.
    alloca_offsets: HashMap<ValueId, u32>,
    /// Integer-constant value for each `Const` result (for constant GEP indices).
    const_ints: HashMap<ValueId, i64>,
    /// Total frame size in bytes (0 ⇒ no frame / no prologue).
    frame_size: u32,
    /// Local holding the caller's stack pointer (restored on return).
    saved_sp_local: u32,
    /// Local holding this frame's base address (`alloca` = base + offset).
    frame_base_local: u32,
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
    /// from its top. Under any other memory policy a module that HAS globals is
    /// refused ([`WasmLowerError::HostMemoryNotGranted`]).
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
            sig_types,
            global_addrs,
        } = env;
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

        let idom = Self::compute_idom(&preds, &rpo_index, entry, n);

        // Reducibility: every back-edge (u,v) must have v dominate u.
        for &(u, v) in &back_edges {
            if !Self::dominates(&idom, v, u, entry) {
                return Err(WasmLowerError::UnsupportedControlFlow(format!(
                    "irreducible control flow (multi-entry loop) in `{}`",
                    func.name
                )));
            }
        }

        // Merge nodes: ≥2 forward predecessors. Loop headers: back-edge targets.
        let is_merge: Vec<bool> = (0..n).map(|b| preds[b].len() >= 2).collect();
        let mut is_header = vec![false; n];
        for &(_, v) in &back_edges {
            is_header[v] = true;
        }

        // Integer constants, for resolving constant GEP (field) indices.
        let mut const_ints: HashMap<ValueId, i64> = HashMap::new();
        for block in &func.blocks {
            for node in &block.body {
                if let Inst::Const {
                    value: Constant::Int(v),
                    ..
                } = &node.inst
                    && let Some(r) = node.results.first()
                {
                    const_ints.insert(*r, *v as i64);
                }
            }
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
            sig_types,
            global_addrs,
            block_index,
            dom_children,
            is_header,
            is_merge,
            back_edges,
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
            const_ints,
            frame_size: 0,
            saved_sp_local: 0,
            frame_base_local: 0,
        })
    }

    /// Pre-pass: lay out one stack frame for all `Alloca`s in the function
    /// (LLVM-style, hoisted to entry so allocas in loops reuse the slot). Each
    /// alloca gets a naturally-aligned offset; the frame is rounded to 8 bytes.
    /// If any alloca exists, two helper locals (saved SP, frame base) are
    /// reserved and the module's stack-pointer global is required.
    fn compute_frame(&mut self) -> Result<(), WasmLowerError> {
        let mut offset: u32 = 0;
        for block in &self.func.blocks {
            for node in &block.body {
                if let Inst::Alloca { ty, count, .. } = &node.inst {
                    if count.is_some() {
                        return Err(WasmLowerError::UnsupportedInst(
                            "array Alloca with a dynamic count (Slice 2b)".to_string(),
                        ));
                    }
                    // wasm allows unaligned access, so 8-byte slot alignment is
                    // a cleanliness choice, not a correctness requirement.
                    let size = self.size_of(ty)?;
                    offset = align_up(offset, 8);
                    let result = first_result(node, &self.func.name)?;
                    self.alloca_offsets.insert(result, offset);
                    offset += size;
                }
            }
        }
        if offset == 0 {
            return Ok(());
        }
        if self.sp_global.is_none() {
            return Err(WasmLowerError::UnsupportedInst(
                "function allocates but no stack-pointer global was provisioned".to_string(),
            ));
        }
        self.frame_size = align_up(offset, 8);
        self.saved_sp_local = self.next_local;
        self.declared_locals.push(ValType::I32);
        self.frame_base_local = self.next_local + 1;
        self.declared_locals.push(ValType::I32);
        self.next_local += 2;
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
    fn emit_prologue(&mut self) {
        if self.frame_size == 0 {
            return;
        }
        let sp = self.sp_global.expect("frame implies sp_global");
        self.code.push(op::GLOBAL_GET);
        write_uleb128(&mut self.code, u64::from(sp));
        self.emit_local_set(self.saved_sp_local);
        emit_local_get(&mut self.code, self.saved_sp_local);
        emit_i32_const(&mut self.code, self.frame_size as i32);
        self.code.push(op::I32_SUB);
        self.code.push(op::LOCAL_TEE);
        write_uleb128(&mut self.code, u64::from(self.frame_base_local));
        self.code.push(op::GLOBAL_SET);
        write_uleb128(&mut self.code, u64::from(sp));
    }

    /// Iterative DFS from `entry`: records back-edges (retreating edges whose
    /// target is on the current path) and returns a reverse-postorder index
    /// (`usize::MAX` for unreachable blocks).
    fn reverse_postorder(
        succs: &[Vec<usize>],
        entry: usize,
        n: usize,
    ) -> (Vec<usize>, HashSet<(usize, usize)>) {
        let mut visited = vec![false; n];
        let mut on_path = vec![false; n];
        let mut postorder: Vec<usize> = Vec::new();
        let mut back_edges: HashSet<(usize, usize)> = HashSet::new();

        enum Step {
            Enter(usize),
            Exit(usize),
        }
        let mut stack = vec![Step::Enter(entry)];
        while let Some(step) = stack.pop() {
            match step {
                Step::Enter(u) => {
                    if visited[u] {
                        continue;
                    }
                    visited[u] = true;
                    on_path[u] = true;
                    stack.push(Step::Exit(u));
                    for &v in succs[u].iter().rev() {
                        if on_path[v] {
                            back_edges.insert((u, v));
                        } else if !visited[v] {
                            stack.push(Step::Enter(v));
                        }
                    }
                }
                Step::Exit(u) => {
                    on_path[u] = false;
                    postorder.push(u);
                }
            }
        }

        let mut rpo_index = vec![usize::MAX; n];
        for (pos, &block) in postorder.iter().rev().enumerate() {
            rpo_index[block] = pos;
        }
        (rpo_index, back_edges)
    }

    /// Cooper-Harvey-Kennedy iterative dominance over reverse-postorder.
    fn compute_idom(
        preds: &[Vec<usize>],
        rpo_index: &[usize],
        entry: usize,
        n: usize,
    ) -> Vec<usize> {
        // Reachable blocks in RPO order (excluding entry).
        let mut order: Vec<usize> = (0..n)
            .filter(|&b| b != entry && rpo_index[b] != usize::MAX)
            .collect();
        order.sort_by_key(|&b| rpo_index[b]);

        let undefined = usize::MAX;
        let mut idom = vec![undefined; n];
        idom[entry] = entry;

        let intersect = |mut a: usize, mut b: usize, idom: &[usize]| -> usize {
            while a != b {
                while rpo_index[a] > rpo_index[b] {
                    a = idom[a];
                }
                while rpo_index[b] > rpo_index[a] {
                    b = idom[b];
                }
            }
            a
        };

        let mut changed = true;
        while changed {
            changed = false;
            for &b in &order {
                let mut new_idom = undefined;
                for &p in &preds[b] {
                    if idom[p] == undefined {
                        continue; // not yet processed
                    }
                    new_idom = if new_idom == undefined {
                        p
                    } else {
                        intersect(p, new_idom, &idom)
                    };
                }
                if new_idom != undefined && idom[b] != new_idom {
                    idom[b] = new_idom;
                    changed = true;
                }
            }
        }
        idom
    }

    /// Does `a` dominate `b`? Walk `b`'s idom chain to the entry.
    fn dominates(idom: &[usize], a: usize, b: usize, entry: usize) -> bool {
        let mut cur = b;
        loop {
            if cur == a {
                return true;
            }
            if cur == entry {
                return false;
            }
            let next = idom[cur];
            if next == cur || next == usize::MAX {
                return false;
            }
            cur = next;
        }
    }

    /// Size in bytes of a type, via the trust-ir layout engine (scalars,
    /// arrays, structs, tuples).
    fn size_of(&self, ty: &Ty) -> Result<u32, WasmLowerError> {
        let shape = self
            .module
            .ty_layout_shape(ty)
            .map_err(|e| WasmLowerError::UnsupportedType(format!("layout of {ty:?}: {e:?}")))?;
        let bytes = shape
            .size_bytes()
            .ok_or_else(|| WasmLowerError::UnsupportedType(format!("{ty:?} has no byte size")))?;
        u32::try_from(bytes)
            .map_err(|_| WasmLowerError::UnsupportedType(format!("{ty:?} too large")))
    }

    fn idx(&self, b: BlockId) -> Result<usize, WasmLowerError> {
        self.block_index
            .get(&b)
            .copied()
            .ok_or_else(|| WasmLowerError::UndefinedBlock(format!("{b:?}")))
    }

    /// Assign a wasm local to every SSA value: entry-block params first (the
    /// function params), then every other block param and instruction result.
    fn assign_locals(&mut self) -> Result<(), WasmLowerError> {
        let entry = self.idx(self.func.entry)?;
        for (vid, ty) in &self.func.blocks[entry].params {
            let vt = valtype_of(ty)?;
            self.locals.insert(*vid, (self.next_local, vt));
            self.value_types.insert(*vid, ty.clone());
            self.param_types.push(vt);
            self.next_local += 1;
        }
        for (bi, block) in self.func.blocks.iter().enumerate() {
            if bi != entry {
                for (vid, ty) in &block.params {
                    let vt = valtype_of(ty)?;
                    self.value_types.insert(*vid, ty.clone());
                    self.bind_declared(*vid, vt);
                }
            }
            for node in &block.body {
                if node.results.is_empty() {
                    continue;
                }
                let ty = result_ty(&node.inst, self.module)?;
                let vt = valtype_of(&ty)?;
                for &res in &node.results {
                    self.value_types.insert(res, ty.clone());
                    self.bind_declared(res, vt);
                }
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
                return Err(self.bad_cast(op, src_vt, dst_vt));
            }
            return self.emit_int_resize(src, dst, view);
        }
        // A narrow destination has no float→int lowering here: `trunc_sat`
        // saturates to the CARRIER's range (i32/i64), not to the narrow type's,
        // so the `*Sat` casts would clamp at the wrong bound and the plain ones
        // would keep bits the narrow type does not have.
        if matches!(
            op,
            CastOp::FPToSI | CastOp::FPToSISat | CastOp::FPToUI | CastOp::FPToUISat
        ) && narrow_of(dst_ty).is_some()
        {
            return Err(WasmLowerError::NarrowLegalization(format!(
                "Cast::{op:?} to {dst_ty:?} in `{}`: wasm's trunc_sat saturates to the i32/i64 \
                 carrier, not to a {}-bit range — cast to the carrier width first, then Trunc",
                self.func.name,
                narrow_of(dst_ty).map_or(0, |r| r.bits),
            )));
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
            // FPToSISat/FPToUISat: excluded from the proven surface (ay's
            // encode_cast fails closed; Lean-excluded), so they fail closed
            // here too even though wasm's trunc_sat family matches their
            // saturating semantics — no lowering without the proof story.
            CastOp::Transmute | CastOp::ReifyFnPointer => {
                return Err(WasmLowerError::UnsupportedInst(format!(
                    "Cast::{op:?} (not supported)"
                )));
            }
        }
        Ok(())
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
            match &node.inst {
                Inst::Const {
                    value: Constant::FnDef(fid),
                    ..
                } => {
                    // A function pointer is its table index (== its wasm funcidx).
                    let (widx, _) = *self.call_targets.get(fid).ok_or_else(|| {
                        WasmLowerError::UnsupportedInst(format!(
                            "function pointer to unknown {fid:?}"
                        ))
                    })?;
                    let dst = slot(&self.locals, first_result(node, &self.func.name)?)?.0;
                    emit_i32_const(&mut self.code, widx as i32);
                    self.emit_local_set(dst);
                }
                Inst::Const { ty, value } => {
                    let dst = slot(&self.locals, first_result(node, &self.func.name)?)?.0;
                    self.emit_const(ty, value)?;
                    self.emit_local_set(dst);
                }
                Inst::BinOp {
                    op: bin,
                    ty,
                    lhs,
                    rhs,
                } => {
                    let vt = valtype_of(ty)?;
                    let opcode = int_binop_opcode(*bin, vt)?;
                    let narrow = narrow_of(ty);
                    let (lv, rv) = binop_operand_views(*bin);
                    let l = slot(&self.locals, *lhs)?.0;
                    let r = slot(&self.locals, *rhs)?.0;
                    let dst = slot(&self.locals, first_result(node, &self.func.name)?)?.0;
                    self.emit_operand(l, narrow, lv)?;
                    self.emit_operand(r, narrow, rv)?;
                    self.code.push(opcode);
                    self.canonicalize_result(ty)?;
                    self.emit_local_set(dst);
                }
                Inst::UnOp {
                    op: un,
                    ty,
                    operand,
                } => {
                    let src = slot(&self.locals, *operand)?.0;
                    let dst = slot(&self.locals, first_result(node, &self.func.name)?)?.0;
                    self.emit_unop(*un, ty, src)?;
                    self.emit_local_set(dst);
                }
                Inst::ICmp {
                    op: cmp,
                    ty,
                    lhs,
                    rhs,
                } => {
                    let vt = valtype_of(ty)?;
                    let opcode = icmp_opcode(*cmp, vt)?;
                    let narrow = narrow_of(ty);
                    let view = icmp_operand_view(*cmp);
                    let l = slot(&self.locals, *lhs)?.0;
                    let r = slot(&self.locals, *rhs)?.0;
                    let dst = slot(&self.locals, first_result(node, &self.func.name)?)?.0;
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
                    let dst = slot(&self.locals, first_result(node, &self.func.name)?)?.0;
                    self.emit_fcmp(*cmp, vt, l, r)?;
                    self.emit_local_set(dst);
                }
                Inst::Cast {
                    op: cop,
                    src_ty,
                    dst_ty,
                    operand,
                } => {
                    let src = slot(&self.locals, *operand)?.0;
                    let dst = slot(&self.locals, first_result(node, &self.func.name)?)?.0;
                    emit_local_get(&mut self.code, src);
                    self.emit_cast(*cop, src_ty, dst_ty)?;
                    self.emit_local_set(dst);
                }
                Inst::Alloca { ty, .. } => {
                    let _ = ty; // size already accounted in the frame pre-pass
                    let result = first_result(node, &self.func.name)?;
                    let off = *self.alloca_offsets.get(&result).ok_or_else(|| {
                        WasmLowerError::UnsupportedInst(format!(
                            "Alloca result {result:?} missing a frame slot"
                        ))
                    })?;
                    let dst = slot(&self.locals, result)?.0;
                    // pointer = frame_base + offset
                    emit_local_get(&mut self.code, self.frame_base_local);
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
                    let dst = slot(&self.locals, first_result(node, &self.func.name)?)?.0;
                    let base_l = slot(&self.locals, *base)?.0;
                    let elem_size = self.size_of(pointee_ty)?;

                    // Element index (first): addr = base + idx0 * sizeof(pointee).
                    let (idx_l, idx_vt) = slot(&self.locals, indices[0])?;
                    if idx_vt != ValType::I32 {
                        return Err(WasmLowerError::UnsupportedInst(format!(
                            "GEP index of {idx_vt:?} (wasm32 addresses use i32 indices)"
                        )));
                    }
                    emit_local_get(&mut self.code, base_l);
                    emit_local_get(&mut self.code, idx_l);
                    emit_i32_const(&mut self.code, elem_size as i32);
                    self.code.push(op::I32_MUL);
                    self.code.push(op::I32_ADD);

                    match indices.len() {
                        1 => {}
                        2 => {
                            // Struct field: + field_offset(struct, const field).
                            let Ty::Struct(sid) = pointee_ty else {
                                return Err(WasmLowerError::UnsupportedInst(format!(
                                    "2-index GEP into non-struct {pointee_ty:?} (Slice 2c: structs)"
                                )));
                            };
                            let field = *self.const_ints.get(&indices[1]).ok_or_else(|| {
                                WasmLowerError::UnsupportedInst(
                                    "struct GEP field index must be a constant".to_string(),
                                )
                            })?;
                            let field = u32::try_from(field).map_err(|_| {
                                WasmLowerError::UnsupportedInst(format!("bad field index {field}"))
                            })?;
                            let off_bits = self
                                .module
                                .struct_field_offset_bits(*sid, field)
                                .map_err(|e| {
                                    WasmLowerError::UnsupportedInst(format!(
                                        "struct field offset: {e:?}"
                                    ))
                                })?;
                            emit_i32_const(&mut self.code, (off_bits / 8) as i32);
                            self.code.push(op::I32_ADD);
                        }
                        n => {
                            return Err(WasmLowerError::UnsupportedInst(format!(
                                "GEP with {n} indices (supported: 1 element, 2 struct-field)"
                            )));
                        }
                    }
                    self.emit_local_set(dst);
                }
                // A narrow load picks the EXTENDING opcode its type demands
                // (`i32.load8_s` for `I8`, `i32.load8_u` for `U8`, …), so the
                // value lands in its canonical carrier form with no extra
                // instruction; a narrow store writes the low bits of that same
                // canonical carrier with `i32.store8` / `i32.store16`.
                Inst::Load { ty, ptr, .. } => {
                    let (load_op, _, align) = mem_ops(ty)?;
                    let p = slot(&self.locals, *ptr)?.0;
                    let dst = slot(&self.locals, first_result(node, &self.func.name)?)?.0;
                    emit_local_get(&mut self.code, p);
                    self.code.push(load_op);
                    emit_memarg(&mut self.code, align, 0);
                    self.emit_local_set(dst);
                }
                Inst::Store { ty, ptr, value, .. } => {
                    let (_, store_op, align) = mem_ops(ty)?;
                    let p = slot(&self.locals, *ptr)?.0;
                    let v = slot(&self.locals, *value)?.0;
                    emit_local_get(&mut self.code, p); // address
                    emit_local_get(&mut self.code, v); // value
                    self.code.push(store_op);
                    emit_memarg(&mut self.code, align, 0);
                }
                // A module global's address is a link-time constant here: the
                // static-data layout assigned it an absolute wasm32 address,
                // and its bytes were emitted as a data segment.
                Inst::GlobalAddr { global } => {
                    let addr = *self.global_addrs.get(global).ok_or_else(|| {
                        WasmLowerError::UnsupportedInst(format!(
                            "GlobalAddr of unknown {global:?} in `{}`",
                            self.func.name
                        ))
                    })?;
                    let dst = slot(&self.locals, first_result(node, &self.func.name)?)?.0;
                    emit_i32_const(&mut self.code, addr as i32);
                    self.emit_local_set(dst);
                }
                // The WASM backend lowers only `CallingConv::C`. A non-C edge
                // is rejected here (fail-closed) rather than silently lowered
                // through the `sig`-derived `call_indirect` type index with the
                // wrong ABI, mirroring the adapter's indirect-call guard.
                Inst::CallIndirect {
                    callee,
                    sig,
                    args,
                    calling_conv,
                } => {
                    if *calling_conv != CallingConv::C {
                        return Err(WasmLowerError::UnsupportedInst(format!(
                            "call_indirect uses unsupported calling convention {calling_conv:?}; the WASM backend lowers only CallingConv::C"
                        )));
                    }
                    let type_idx = *self.sig_types.get(sig).ok_or_else(|| {
                        WasmLowerError::UnsupportedInst(format!(
                            "call_indirect with unknown {sig:?}"
                        ))
                    })?;
                    let ret_is_value = self
                        .module
                        .func_type(*sig)
                        .is_some_and(|ft| !ft.returns.is_empty());
                    // Push args, then the callee table index, then call_indirect.
                    let arg_locals: Vec<u32> = args
                        .iter()
                        .map(|a| slot(&self.locals, *a).map(|s| s.0))
                        .collect::<Result<_, _>>()?;
                    for a in arg_locals {
                        emit_local_get(&mut self.code, a);
                    }
                    let callee_l = slot(&self.locals, *callee)?.0;
                    emit_local_get(&mut self.code, callee_l);
                    self.code.push(op::CALL_INDIRECT);
                    write_uleb128(&mut self.code, u64::from(type_idx));
                    write_uleb128(&mut self.code, 0); // table 0
                    match (node.results.first(), ret_is_value) {
                        (Some(r), true) => {
                            // The callee is reached through a table, so nothing
                            // here proves it canonicalized a narrow result —
                            // re-establish invariant N on this side.
                            if let Some(ret_ty) = self
                                .module
                                .func_type(*sig)
                                .and_then(|ft| ft.returns.first())
                            {
                                self.canonicalize_result(ret_ty)?;
                            }
                            let dst = slot(&self.locals, *r)?.0;
                            self.emit_local_set(dst);
                        }
                        (None, true) => self.code.push(op::DROP),
                        (None, false) => {}
                        (Some(_), false) => {
                            return Err(WasmLowerError::UnsupportedInst(
                                "indirect call result used but signature returns void".to_string(),
                            ));
                        }
                    }
                }
                Inst::Call { callee, args } => {
                    let (widx, ret) = *self.call_targets.get(callee).ok_or_else(|| {
                        WasmLowerError::UnsupportedInst(format!("Call to unknown {callee:?}"))
                    })?;
                    // Push args in order, then `call`.
                    let arg_locals: Vec<u32> = args
                        .iter()
                        .map(|a| slot(&self.locals, *a).map(|s| s.0))
                        .collect::<Result<_, _>>()?;
                    for a in arg_locals {
                        emit_local_get(&mut self.code, a);
                    }
                    self.code.push(op::CALL);
                    write_uleb128(&mut self.code, u64::from(widx));
                    // Consume the result: bind it, drop it, or (void) nothing.
                    match (node.results.first(), ret) {
                        (Some(r), Some(_)) => {
                            // A callee may be an IMPORT, whose return value is
                            // the host's: re-canonicalize a narrow result here
                            // rather than trusting the other side of the
                            // boundary to have done it (invariant N).
                            if let Some(ret_ty) = self
                                .module
                                .function_by_id(*callee)
                                .and_then(|f| self.module.func_type(f.ty))
                                .and_then(|ft| ft.returns.first())
                            {
                                self.canonicalize_result(ret_ty)?;
                            }
                            let dst = slot(&self.locals, *r)?.0;
                            self.emit_local_set(dst);
                        }
                        (None, Some(_)) => self.code.push(op::DROP),
                        (None, None) => {}
                        (Some(_), None) => {
                            return Err(WasmLowerError::UnsupportedInst(format!(
                                "Call to {callee:?} returns no value but its result is used"
                            )));
                        }
                    }
                }
                other => {
                    return Err(WasmLowerError::UnsupportedInst(format!(
                        "{other:?} (supported: Const, BinOp add/sub/mul, ICmp, Alloca, GEP, \
                         Load, Store, Call)"
                    )));
                }
            }
        }
        Ok(())
    }

    /// Emit a constant onto the wasm operand stack.
    ///
    /// An integer constant is canonicalized into its carrier AT COMPILE TIME
    /// (invariant N): `Const { ty: U8, value: 300 }` emits `i32.const 44` and
    /// `Const { ty: I8, value: 200 }` emits `i32.const -56`, so no
    /// re-canonicalization instruction is ever needed after a constant.
    fn emit_const(&mut self, ty: &Ty, value: &Constant) -> Result<(), WasmLowerError> {
        let vt = valtype_of(ty)?;
        let repr = int_repr_of(ty);
        match (vt, value) {
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
    /// Permutation-safe: push every source value onto the operand stack first,
    /// then `local.set` the destinations in reverse — so a swap like
    /// `br head [b, a]` is correct.
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
        let mut dest_locals: Vec<u32> = Vec::with_capacity(args.len());
        for ((pv, _), av) in params.iter().zip(args) {
            let a = slot(&self.locals, *av)?.0;
            let p = slot(&self.locals, *pv)?.0;
            emit_local_get(&mut self.code, a);
            dest_locals.push(p);
        }
        for &p in dest_locals.iter().rev() {
            self.emit_local_set(p);
        }
        Ok(())
    }

    fn emit_return(&mut self, values: &[ValueId]) -> Result<(), WasmLowerError> {
        // Epilogue: restore the caller's stack pointer before leaving.
        if self.frame_size != 0 {
            let sp = self.sp_global.expect("frame implies sp_global");
            emit_local_get(&mut self.code, self.saved_sp_local);
            self.code.push(op::GLOBAL_SET);
            write_uleb128(&mut self.code, u64::from(sp));
        }
        let mut tys = Vec::with_capacity(values.len());
        for v in values {
            let (idx, vt) = slot(&self.locals, *v)?;
            emit_local_get(&mut self.code, idx);
            tys.push(vt);
        }
        self.code.push(op::RETURN);
        if self.result_types.is_none() {
            self.result_types = Some(tys);
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
            Frame::Loop(_) => op::LOOP,
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

    /// Recurse the dominator tree at `x`: a loop header opens a `loop`.
    fn do_tree(&mut self, x: usize) -> Result<(), WasmLowerError> {
        let merge_kids = self.merge_children(x);
        if self.is_header[x] {
            self.open_scope(Frame::Loop(x));
            self.node_within(x, &merge_kids)?;
            self.close_scope();
        } else {
            self.node_within(x, &merge_kids)?;
        }
        Ok(())
    }

    /// Open a `block` for each pending merge child — **LATEST-RPO outermost** —
    /// then emit `x`'s body in the innermost context. After each block's `end`,
    /// recurse that merge child's subtree (its join point).
    ///
    /// The nesting order is load-bearing. Control inside this dominator subtree
    /// flows FORWARD in reverse-postorder, so an earlier merge child's subtree
    /// may branch to a later one but never the reverse. Peeling the LAST child
    /// (`split_last`, `merge_kids` being RPO-ascending) puts the latest-RPO
    /// block outermost, which is what keeps its label in scope while every
    /// earlier child's subtree is emitted:
    ///
    /// ```text
    /// block $Y_n            ;; latest RPO — outermost
    ///   block $Y_1          ;; earliest RPO — innermost
    ///     <x's code>        ;; may br to every $Y_i
    ///   end
    ///   <Y_1's subtree>     ;; still inside $Y_n, so it may br to it
    /// end
    /// <Y_n's subtree>
    /// ```
    ///
    /// Peeling the FIRST child instead inverts this and puts `$Y_n` innermost,
    /// so `Y_1`'s subtree is emitted outside `$Y_n` and its forward branch has
    /// no label in scope — the shape that appears as soon as a node has two
    /// merge children, e.g. a `Switch` whose default edge reuses one of its own
    /// case blocks (that block gains a second predecessor and becomes a merge
    /// child beside the join). This is the ordering of Ramsey, ICFP 2022, §4.
    fn node_within(&mut self, x: usize, merge_kids: &[usize]) -> Result<(), WasmLowerError> {
        if let Some((&y, rest)) = merge_kids.split_last() {
            self.open_scope(Frame::Block(y));
            self.node_within(x, rest)?;
            self.close_scope();
            self.do_tree(y)?;
        } else {
            if !self.emitted.insert(x) {
                return Err(WasmLowerError::UnsupportedControlFlow(format!(
                    "re-emission of block {x} in `{}` — unstructured/irreducible CFG",
                    self.func.name
                )));
            }
            self.emit_block_body(x)?;
            self.do_terminator(x)?;
        }
        Ok(())
    }

    fn do_terminator(&mut self, x: usize) -> Result<(), WasmLowerError> {
        let term = terminator_of(self.func, x)?.clone();
        match term {
            Inst::Return { values } => self.emit_return(&values)?,
            Inst::Unreachable => self.code.push(op::UNREACHABLE),
            Inst::Br { target, args } => {
                self.set_params(target, &args)?;
                let t = self.idx(target)?;
                self.do_branch(x, t)?;
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
                self.do_branch(x, then_i)?;
                self.code.push(op::ELSE);
                self.set_params(else_target, &else_args)?;
                self.do_branch(x, else_i)?;
                self.close_if();
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
                let (vlocal, vt) = slot(&self.locals, value)?;
                match br_table_plan(&value_ty, &cases)? {
                    // A dense-enough case range: one `br_table` dispatch.
                    Some(plan) => {
                        self.emit_switch_br_table(x, vlocal, &plan, &cases, default, &default_args)?
                    }
                    // Otherwise an if/else compare-cascade: each case is
                    // `if value == k { <case edge> } else { <rest> }`, ending in
                    // the default edge. Reuses do_branch, so case targets that
                    // are merge nodes / back-edges / inlinable blocks are all
                    // handled. The nested `if`s are counted in open_labels, so
                    // branch depths stay correct.
                    None => self.emit_switch_cascade(
                        x,
                        vlocal,
                        vt,
                        &value_ty,
                        &cases,
                        default,
                        &default_args,
                    )?,
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

    /// Emit the recursive `Switch` compare-cascade.
    fn emit_switch_cascade(
        &mut self,
        x: usize,
        vlocal: u32,
        vt: ValType,
        value_ty: &Ty,
        cases: &[trust_ir::SwitchCase],
        default: BlockId,
        default_args: &[ValueId],
    ) -> Result<(), WasmLowerError> {
        match cases.split_first() {
            None => {
                self.set_params(default, default_args)?;
                let d = self.idx(default)?;
                self.do_branch(x, d)
            }
            Some((case, rest)) => {
                let eq = match vt {
                    ValType::I32 => op::I32_EQ,
                    ValType::I64 => op::I64_EQ,
                    other => {
                        return Err(WasmLowerError::UnsupportedInst(format!(
                            "Switch on {other:?} (supported: i32/i64)"
                        )));
                    }
                };
                // The switch value is a canonical carrier and the case constant
                // is canonicalized to the same form by `emit_const`, so an
                // equality test needs no coercion on either side (invariant N).
                emit_local_get(&mut self.code, vlocal);
                self.emit_const(value_ty, &case.value)?;
                self.code.push(eq);
                self.open_if();
                self.set_params(case.target, &case.args)?;
                let t = self.idx(case.target)?;
                self.do_branch(x, t)?;
                self.code.push(op::ELSE);
                self.emit_switch_cascade(x, vlocal, vt, value_ty, rest, default, default_args)?;
                self.close_if();
                Ok(())
            }
        }
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
    /// arm's code may FALL THROUGH (`do_branch` inlines a subtree whose own
    /// paths end elsewhere), and without the branch that fallthrough would run
    /// the NEXT arm. `$out`'s `end` is exactly where the compare-cascade's
    /// outermost `end` sits, so both lowerings hand control to the same
    /// continuation.
    fn emit_switch_br_table(
        &mut self,
        x: usize,
        vlocal: u32,
        plan: &BrTablePlan,
        cases: &[trust_ir::SwitchCase],
        default: BlockId,
        default_args: &[ValueId],
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

        for (j, case) in cases.iter().enumerate() {
            self.close_anon_block(); // end $arm_j — arm j's code follows
            self.set_params(case.target, &case.args)?;
            let t = self.idx(case.target)?;
            self.do_branch(x, t)?;
            // Leave the nest: $out is (m - j) labels out from here.
            self.code.push(op::BR);
            write_uleb128(&mut self.code, (m - j) as u64);
        }

        self.close_anon_block(); // end $default — the default edge follows
        self.set_params(default, default_args)?;
        let d = self.idx(default)?;
        self.do_branch(x, d)?;
        // No `br $out` needed: $out's `end` is the next byte, so a fallthrough
        // already lands on the continuation.
        self.close_anon_block(); // end $out
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

    /// Translate the edge `x -> t`: back-edge → `br` to the loop label; forward
    /// merge → `br` to the block label; otherwise inline `t`'s subtree.
    fn do_branch(&mut self, x: usize, t: usize) -> Result<(), WasmLowerError> {
        if self.back_edges.contains(&(x, t)) {
            let n = self.resolve_branch(true, t)?;
            self.code.push(op::BR);
            write_uleb128(&mut self.code, u64::from(n));
        } else if self.is_merge[t] {
            let n = self.resolve_branch(false, t)?;
            self.code.push(op::BR);
            write_uleb128(&mut self.code, u64::from(n));
        } else {
            self.do_tree(t)?;
        }
        Ok(())
    }
}

/// The module-level context one function's lowering reads: where the shadow
/// stack pointer lives, which wasm function index each callee has, which type
/// index each indirect-call signature has, and the absolute address of every
/// module global's static-data slot.
#[derive(Debug, Clone, Copy)]
pub struct WasmFunctionEnv<'a> {
    /// The shadow stack-pointer global, when the module provisioned one.
    pub sp_global: Option<u32>,
    /// FuncId → (wasm function index, return value type) for direct calls.
    pub call_targets: &'a HashMap<FuncId, (u32, Option<ValType>)>,
    /// trust-ir signature → wasm type index, for `call_indirect`.
    pub sig_types: &'a HashMap<FuncTyId, u32>,
    /// Module global → the absolute wasm32 address of its static-data slot.
    pub global_addrs: &'a HashMap<trust_ir::value::GlobalId, u32>,
}

impl WasmFunctionEnv<'_> {
    /// The env of a module with no calls, no indirect calls, no globals and no
    /// shadow stack — everything a single straight-line function needs.
    pub fn empty() -> WasmFunctionEnv<'static> {
        use std::sync::OnceLock;
        static CALL_TARGETS: OnceLock<CallTargets> = OnceLock::new();
        static SIG_TYPES: OnceLock<SigTypes> = OnceLock::new();
        static GLOBAL_ADDRS: OnceLock<GlobalAddrs> = OnceLock::new();
        WasmFunctionEnv {
            sp_global: None,
            call_targets: CALL_TARGETS.get_or_init(HashMap::new),
            sig_types: SIG_TYPES.get_or_init(HashMap::new),
            global_addrs: GLOBAL_ADDRS.get_or_init(HashMap::new),
        }
    }
}

/// Lower a single trust-ir function and append it to `module`. Returns the new
/// wasm function index. Supports straight-line code, `if/else`, reducible
/// loops, and `Switch` (compare-cascade or `br_table`); fail-closed on
/// irreducible CFGs and out-of-subset ops.
pub fn lower_function(
    module: &mut WasmModule,
    func: &Function,
    ir_module: &Module,
    env: WasmFunctionEnv<'_>,
) -> Result<u32, WasmLowerError> {
    // The wasm32 pin is checked HERE too, not only in `compile_module`: this
    // function is part of the crate's public surface, and frame/GEP layout is
    // computed from `ir_module`'s target while addresses are emitted as i32 —
    // a target-free or 64-bit-pinned module would silently mis-lay-out every
    // frame (the hazard `require_wasm32_target_info` exists to refuse).
    require_wasm32_target_info(ir_module)?;
    reject_unwired_eh_instructions(func)?;
    reject_unsupported_call_contract(func, ir_module)?;
    let mut low = Lowering::build(func, ir_module, env)?;
    low.assign_locals()?;
    low.compute_frame()?;
    // Invariant N is established for the function's own parameters BEFORE any
    // of its code runs — including before the frame prologue, so a narrow
    // pointer-ish argument is canonical for every use.
    low.emit_param_canonicalization()?;
    low.emit_prologue();
    let entry = low.idx(func.entry)?;
    low.do_tree(entry)?;
    // All paths return; mark the statically-dead tail so the module validates.
    low.code.push(op::UNREACHABLE);

    let results = low.result_types.unwrap_or_default();
    let ty_idx = module.add_type(FuncType {
        params: low.param_types,
        results,
    });
    let body = FuncBody {
        locals: run_length_encode(&low.declared_locals),
        code: low.code,
    };
    Ok(module.add_function(ty_idx, body))
}

/// True if `func` contains any `Alloca` (and therefore needs a stack frame).
fn uses_stack_frame(func: &Function) -> bool {
    func.blocks
        .iter()
        .flat_map(|b| &b.body)
        .any(|n| matches!(n.inst, Inst::Alloca { .. }))
}

/// True if `func` ACCESSES linear memory. Broader than [`uses_stack_frame`]: a
/// function that only loads through a pointer parameter needs no frame but
/// still needs a memory to load from, and emitting `i32.load` into a module
/// with no memory is an invalid module.
fn uses_linear_memory(func: &Function) -> bool {
    func.blocks.iter().flat_map(|b| &b.body).any(|n| {
        matches!(
            n.inst,
            Inst::Alloca { .. } | Inst::Load { .. } | Inst::Store { .. } | Inst::GlobalAddr { .. }
        )
    })
}

/// True if `func` is a declaration: it has no body to lower, so it can only be
/// provided by an import.
fn is_declaration(func: &Function) -> bool {
    func.blocks.is_empty()
}

/// True if `func` takes a function address or makes an indirect call (needs a
/// function table).
fn uses_func_table(func: &Function) -> bool {
    func.blocks.iter().flat_map(|b| &b.body).any(|n| {
        matches!(n.inst, Inst::CallIndirect { .. })
            || matches!(
                &n.inst,
                Inst::Const {
                    value: Constant::FnDef(_),
                    ..
                }
            )
    })
}

/// The little-endian byte image of a scalar constant at `ty`, or `None` when
/// the constant/type pair has no scalar image.
fn scalar_byte_image(ty: &Ty, value: &Constant, size: usize) -> Option<Vec<u8>> {
    let bytes = match (value, ty) {
        (Constant::Bool(b), Ty::Bool) => vec![u8::from(*b)],
        (Constant::Int(n), _) => {
            // `n as u128` is the value's two's-complement pattern, sign-extended
            // to 128 bits; its low `size` bytes ARE the little-endian image of
            // the value at its own width. Guarded by `int_repr_of` so a
            // non-integer type never takes this arm.
            int_repr_of(ty)?;
            (*n as u128).to_le_bytes().get(..size)?.to_vec()
        }
        (Constant::Float(f), Ty::F32) => (*f as f32).to_le_bytes().to_vec(),
        (Constant::Float(f), Ty::F64) => f.to_le_bytes().to_vec(),
        _ => return None,
    };
    (bytes.len() == size).then_some(bytes)
}

/// The byte image a module global contributes to the static-data area.
///
/// An EMPTY image means "all zeros", which needs no data segment at all: wasm
/// linear memory is zero-initialized, so a BSS-style global is free. Anything
/// whose bytes this backend cannot derive is refused by name
/// ([`WasmLowerError::UnsupportedConstantData`]) rather than emitted as
/// whatever the layout engine happened to leave behind.
fn global_byte_image(
    module: &Module,
    global: &trust_ir::Global,
    size: usize,
) -> Result<Vec<u8>, WasmLowerError> {
    let Some(init) = &global.initializer else {
        // No initializer: BSS. Linear memory already reads as zero.
        return Ok(Vec::new());
    };
    let refuse = |why: &str| {
        WasmLowerError::UnsupportedConstantData(format!(
            "global `{}` of type {:?}: {why}",
            global.name, global.ty
        ))
    };
    match init {
        // Raw byte payload — the `[u8; N]` / `&str` backing image.
        Constant::Bytes { data, .. } => {
            if data.len() > size {
                return Err(refuse(&format!(
                    "{} initializer byte(s) do not fit its {size}-byte layout",
                    data.len()
                )));
            }
            let mut bytes = data.clone();
            bytes.resize(size, 0);
            Ok(bytes)
        }
        // An element-wise array of scalars — a constant lookup table.
        Constant::Array(elements) => {
            let Ty::Array(elem_id, len) = &global.ty else {
                return Err(refuse("an Array initializer needs an Array type"));
            };
            if elements.len() as u64 != *len {
                return Err(refuse(&format!(
                    "{} initializer element(s) for a {len}-element array",
                    elements.len()
                )));
            }
            let elem_ty = module
                .ty(*elem_id)
                .cloned()
                .ok_or_else(|| refuse("unknown array element type"))?;
            let stride = size / elements.len().max(1);
            if stride * elements.len() != size {
                return Err(refuse(&format!(
                    "{size} bytes do not divide evenly into {} element(s)",
                    elements.len()
                )));
            }
            let mut bytes = Vec::with_capacity(size);
            for element in elements {
                let mut image = scalar_byte_image(&elem_ty, element, stride)
                    .ok_or_else(|| refuse(&format!("element {element:?} has no byte image")))?;
                bytes.append(&mut image);
            }
            bytes.resize(size, 0);
            Ok(bytes)
        }
        scalar => scalar_byte_image(&global.ty, scalar, size)
            .ok_or_else(|| refuse(&format!("initializer {scalar:?} has no byte image"))),
    }
}

/// Lay the module's globals out in linear memory and declare their data
/// segments, returning the absolute address of each and the total EXTENT of the
/// static-data area in bytes (the region a host must have reserved).
///
/// Placement is bottom-up from the policy's base, each global at its own
/// natural alignment. The shadow stack grows DOWN from the top of the same
/// memory, so a module whose static data would run past the memory it declared
/// is refused rather than emitted with a data segment the engine would trap on.
fn layout_static_data(
    module: &Module,
    policy: &WasmModulePolicy,
    wasm: &mut WasmModule,
) -> Result<(GlobalAddrs, u64), WasmLowerError> {
    let mut addrs = GlobalAddrs::new();
    if module.globals.is_empty() {
        return Ok((addrs, 0));
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
                "module `{}` has {} global(s) whose bytes must be written into linear memory, \
                 but the memory policy is {other:?} — an ACTIVE data segment there writes at an \
                 absolute address in a memory this module does not own. Configure \
                 WasmStaticDataPolicy::HostReservedAt {{ base }} with the region the host \
                 reserved.",
                module.name,
                module.globals.len(),
            )));
        }
    };
    wasm.require_memory()?;

    let mut cursor = u64::from(base);
    for (index, global) in module.globals.iter().enumerate() {
        let shape = module.ty_layout_shape(&global.ty).map_err(|e| {
            WasmLowerError::UnsupportedType(format!("layout of global `{}`: {e:?}", global.name))
        })?;
        let size = shape.size_bytes().ok_or_else(|| {
            WasmLowerError::UnsupportedType(format!("global `{}` has no byte size", global.name))
        })?;
        let align_bytes = shape
            .align_bits
            .map(|bits| (bits / 8).max(1))
            .unwrap_or(1)
            .max(global.align.map_or(1, u64::from))
            .max(1);
        cursor = cursor.div_ceil(align_bytes) * align_bytes;
        let addr = u32::try_from(cursor).map_err(|_| {
            WasmLowerError::StaticDataOverflow(format!(
                "global `{}` lands at {cursor}, past the wasm32 address space",
                global.name
            ))
        })?;
        let image = global_byte_image(module, global, size as usize)?;
        wasm.add_data_segment(addr, image)?;
        addrs.insert(trust_ir::value::GlobalId::new(index as u32), addr);
        cursor += size;
    }
    Ok((addrs, cursor - u64::from(base)))
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
        },
    );
    wasm.export_func(MEMORY_GROW_EXPORT, grow_idx);
    Ok(())
}

/// Map a trust-ir signature to a wasm function type.
fn wasm_func_type(ft: &trust_ir::FuncTy) -> Result<FuncType, WasmLowerError> {
    let params = ft.params.iter().map(valtype_of).collect::<Result<_, _>>()?;
    let results = ft
        .returns
        .iter()
        .map(valtype_of)
        .collect::<Result<_, _>>()?;
    Ok(FuncType { params, results })
}

/// Lower every function in a trust-ir module to wasm and export each under its
/// own name. If any function uses the stack (allocas), the module gains one
/// linear memory and a shared shadow stack-pointer global.
///
/// Accepted-input guards (fail-closed, named diagnostics):
/// * the module must be pinned to the wasm32 target shape
///   ([`super::target::wasm32_target_info`]) — target-free and
///   non-wasm32-pinned modules are refused;
/// * only `CallingConv::C` functions and call edges are lowered;
/// * multi-result calls are refused (the lowering binds one result).
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
    Ok(compile_module_parts(module, policy)?.0)
}

/// The shared compile body: the module bytes plus the host contract it bound
/// (see [`WasmModule::host_contract`]).
fn compile_module_parts(
    module: &Module,
    policy: &WasmModulePolicy,
) -> Result<(Vec<u8>, Vec<String>), WasmLowerError> {
    require_wasm32_target_info(module)?;
    let mut wasm = WasmModule::with_memory_policy(policy.memory.clone());

    // ---- Imports FIRST. Imported functions occupy function indices 0..N, so
    // every index below (call targets, function-pointer constants, table
    // elements, exports) is derived from `func_import_count`, never from a
    // definition ordinal. Declaring an import after a definition is refused by
    // the encoder, so this ordering is enforced, not merely intended.
    let mut call_targets: CallTargets = HashMap::new();
    for func in module.functions.iter().filter(|f| is_declaration(f)) {
        let WasmFuncImportPolicy::FromModule(host) = &policy.func_imports else {
            return Err(WasmLowerError::UnboundDeclaration(format!(
                "module `{}` declares `{}` with no body, and the func-import policy is \
                 Forbidden — bind it with WasmFuncImportPolicy::FromModule(<host module>)",
                module.name, func.name,
            )));
        };
        if func.calling_conv != CallingConv::C {
            return Err(WasmLowerError::UnsupportedCallingConv(format!(
                "imported declaration `{}` is {:?}; the WASM backend lowers only CallingConv::C",
                func.name, func.calling_conv,
            )));
        }
        let ft = module.func_type(func.ty).ok_or_else(|| {
            WasmLowerError::UnsupportedInst(format!(
                "declaration `{}` has unknown signature {:?}",
                func.name, func.ty
            ))
        })?;
        if ft.returns.len() > 1 {
            return Err(WasmLowerError::UnsupportedMultiResultCall(format!(
                "imported declaration `{}` has {} return values; wasm call lowering supports at \
                 most one",
                func.name,
                ft.returns.len(),
            )));
        }
        let type_idx = wasm.add_type(wasm_func_type(ft)?);
        let widx = wasm.add_func_import(host, &func.name, type_idx)?;
        let ret = ft.returns.first().map(valtype_of).transpose()?;
        call_targets.insert(func.id, (widx, ret));
    }

    // ---- Linear memory, per the policy. Anything that touches memory —
    // alloca, load, store, a global's address — needs one; a policy that
    // provides none refuses, naming the function that needs it.
    let memory_user = module.functions.iter().find(|f| uses_linear_memory(f));
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
    let frame_user = module.functions.iter().find(|f| uses_stack_frame(f));
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
    for (ordinal, func) in module
        .functions
        .iter()
        .filter(|f| !is_declaration(f))
        .enumerate()
    {
        let ret = match module.func_type(func.ty) {
            Some(ft) => ft.returns.first().map(valtype_of).transpose()?,
            None => None,
        };
        call_targets.insert(func.id, (import_base + ordinal as u32, ret));
    }

    // Function table + indirect-call signature types, if the module needs them.
    // The table covers the whole function index space (imports included), so
    // element index == funcidx still holds; the encoder derives its size.
    if module.functions.iter().any(uses_func_table) {
        wasm.enable_func_table();
    }
    let mut sig_types: SigTypes = HashMap::new();
    for func in &module.functions {
        for node in func.blocks.iter().flat_map(|b| &b.body) {
            if let Inst::CallIndirect { sig, .. } = &node.inst
                && !sig_types.contains_key(sig)
            {
                let ft = module.func_type(*sig).ok_or_else(|| {
                    WasmLowerError::UnsupportedInst(format!("unknown signature {sig:?}"))
                })?;
                let idx = wasm.add_type(wasm_func_type(ft)?);
                sig_types.insert(*sig, idx);
            }
        }
    }

    // ---- Static data: every module global gets an absolute address and a data
    // segment. Laid out BEFORE any function is lowered, because `GlobalAddr`
    // materializes that address as an `i32.const` inside the code.
    let (global_addrs, static_data_len) = layout_static_data(module, policy, &mut wasm)?;

    let env = WasmFunctionEnv {
        sp_global,
        call_targets: &call_targets,
        sig_types: &sig_types,
        global_addrs: &global_addrs,
    };
    for func in module.functions.iter().filter(|f| !is_declaration(f)) {
        let idx = lower_function(&mut wasm, func, module, env)?;
        // The call targets above were computed as `import_base + ordinal`. If
        // the emitted index ever disagreed, every `call` to this function
        // would land somewhere else — refuse rather than emit.
        let expected = call_targets.get(&func.id).map(|(i, _)| *i);
        if expected != Some(idx) {
            return Err(WasmLowerError::FunctionIndexDrift(format!(
                "`{}` was emitted as wasm function {idx}, but its call targets were computed as \
                 {expected:?} (import base {import_base})",
                func.name,
            )));
        }
        wasm.export_func(&func.name, idx);
    }

    // The growth shims come LAST so they occupy function indices above every
    // trust-ir function — no call target, function pointer, or export moves.
    append_memory_growth_shims(module, policy, &mut wasm)?;

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
    Ok((wasm.finish(), contract))
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
fn classify_cfg_structural(
    bytes: &[u8],
    ran: &mut Vec<&'static str>,
    not_run: &mut Vec<&'static str>,
) -> Result<WasmCfgStructural, WasmLowerError> {
    use trust_cg_verify::wasm_cfg_proofs::{CfgVerdict, check_module_structure};
    match check_module_structure(bytes) {
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
    let (bytes, host_contract) = compile_module_parts(module, policy)?;

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
        "calling_convention_guard",
        "multi_result_call_guard",
        "eh_instruction_reject_scan",
        "reducible_cfg_structuring",
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
    let cfg_structural = classify_cfg_structural(&bytes, &mut ran, &mut not_run)?;

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
    };
    Ok((bytes, evidence))
}

#[cfg(test)]
mod tests {
    use super::*;
    use trust_ir::{ICmpOp, Ty};
    use trust_ir_build::ModuleBuilder;

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
        wasm32(mb.build())
    }

    #[test]
    fn lowers_straight_line_arithmetic() {
        for (ty, op) in [(Ty::I32, BinOp::Add), (Ty::I64, BinOp::Mul)] {
            assert_wasm_header(&compile_module(&binop_module("f", ty, op)).unwrap());
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
            assert_wasm_header(&compile_module(&binop_module("f", ty, op)).unwrap());
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
        assert_wasm_header(&compile_module(&wasm32(mb.build())).unwrap());
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
        assert_wasm_header(&compile_module(&wasm32(mb.build())).unwrap());
    }

    /// sum_to(n,acc,i,step): while i<=n { acc+=i; i+=step } ; return acc.
    #[test]
    fn lowers_counting_loop() {
        let bytes = compile_module(&sum_to_module()).unwrap();
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
        wasm32(mb.build())
    }

    /// Irreducible: entry → {A,B}; A↔B mutually branch (two loop entries).
    #[test]
    fn rejects_irreducible_loop() {
        let mut mb = ModuleBuilder::new("m");
        let ft = mb.add_func_type(vec![Ty::I32, Ty::I32], vec![Ty::I32]);
        let mut fb = mb.function("irr", ft);
        let entry = fb.create_block();
        let a = fb.create_block();
        let b = fb.create_block();
        let exit = fb.create_block();
        let p = fb.add_block_param(entry, Ty::I32);
        let q = fb.add_block_param(entry, Ty::I32);
        fb.switch_to_block(entry);
        fb.condbr(p, a, vec![], b, vec![]);
        fb.switch_to_block(a);
        fb.br(b, vec![]); // A -> B
        fb.switch_to_block(b);
        fb.condbr(q, a, vec![], exit, vec![]); // B -> A (back) and B -> exit
        fb.switch_to_block(exit);
        fb.ret(vec![p]);
        fb.build();
        let err = compile_module(&wasm32(mb.build())).unwrap_err();
        assert!(
            matches!(err, WasmLowerError::UnsupportedControlFlow(_)),
            "{err}"
        );
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
        assert_wasm_header(&compile_module(&wasm32(mb.build())).unwrap());
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
        let bytes = compile_module(&wasm32(mb.build())).unwrap();
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
        assert_wasm_header(&compile_module(&wasm32(mb.build())).unwrap());
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
        let bytes = compile_module(&wasm32(mb.build())).unwrap();
        assert_wasm_header(&bytes);
    }

    /// pair_sum(x,y): Pair{a@0,b@4}; p.a=x; p.b=y; p.a+p.b — struct-field GEP.
    #[test]
    fn lowers_struct_field_gep() {
        use trust_ir::StructId;
        use trust_ir::ty::{FieldDef, StructDef};
        let mut mb = ModuleBuilder::new("m");
        let sid = mb.add_struct(StructDef {
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
        let zero = fb.iconst(Ty::I32, 0);
        let f0 = fb.iconst(Ty::I32, 0);
        let f1 = fb.iconst(Ty::I32, 1);
        let pa = fb.gep(Ty::Struct(sid), buf, vec![zero, f0]);
        fb.store(Ty::I32, pa, x);
        let pb = fb.gep(Ty::Struct(sid), buf, vec![zero, f1]);
        fb.store(Ty::I32, pb, y);
        let qa = fb.gep(Ty::Struct(sid), buf, vec![zero, f0]);
        let va = fb.load(Ty::I32, qa);
        let qb = fb.gep(Ty::Struct(sid), buf, vec![zero, f1]);
        let vb = fb.load(Ty::I32, qb);
        let s = fb.add(Ty::I32, va, vb);
        fb.ret(vec![s]);
        fb.build();
        assert_wasm_header(&compile_module(&wasm32(mb.build())).unwrap());
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
        assert_wasm_header(&compile_module(&wasm32(mb.build())).unwrap());
    }

    #[test]
    fn rejects_unsupported_binop() {
        // Float remainder has no wasm opcode (it's a libcall), so it stays
        // unlowered — a still-unsupported op for the fail-closed check.
        let err = compile_module(&binop_module("d", Ty::F32, BinOp::FRem)).unwrap_err();
        assert!(matches!(err, WasmLowerError::UnsupportedInst(_)), "{err}");
    }

    #[test]
    fn rejects_exception_handling_instructions_fail_closed() {
        use trust_ir::{
            Block as TrustIrBlock, FuncId, FuncTy, Function as TrustIrFunction, InstrNode, ValueId,
        };

        let make_module = |name: &str, blocks: Vec<TrustIrBlock>| {
            let mut module = Module::new(name);
            let ty = module.add_func_type(FuncTy {
                params: vec![],
                returns: vec![],
                is_vararg: false,
            });
            let mut func = TrustIrFunction::new(FuncId::new(0), name, ty, BlockId::new(0));
            func.blocks = blocks;
            module.add_function(func);
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
                TrustIrBlock {
                    id: BlockId::new(2),
                    params: vec![],
                    body: vec![InstrNode::new(Inst::Return { values: vec![] })],
                },
            ],
        );
        let err = compile_module(&invoke).expect_err("Wasm has no EH instruction lowering");
        assert!(matches!(err, WasmLowerError::UnsupportedInst(_)), "{err}");
        assert!(err.to_string().contains("Invoke"), "{err}");

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
        let err = compile_module(&resume).expect_err("Wasm has no resume lowering");
        assert!(matches!(err, WasmLowerError::UnsupportedInst(_)), "{err}");
        assert!(err.to_string().contains("Resume"), "{err}");

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
        let err = compile_module(&landing_pad).expect_err("Wasm has no landing-pad lowering");
        assert!(matches!(err, WasmLowerError::UnsupportedInst(_)), "{err}");
        assert!(err.to_string().contains("LandingPad"), "{err}");

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
        let err = compile_module(&unreachable_zero_result_pad)
            .expect_err("the whole-function EH scan must include unreachable zero-result nodes");
        assert!(matches!(err, WasmLowerError::UnsupportedInst(_)), "{err}");
        assert!(err.to_string().contains("LandingPad"), "{err}");
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
        let u8_add = compile_module(&binop_module("f", Ty::U8, BinOp::Add)).unwrap();
        assert_wasm_header(&u8_add);
        assert!(
            u8_add.windows(3).any(|w| w == [op::I32_CONST, 0xff, 0x01]),
            "a U8 add must mask its result to 8 bits"
        );
        let i8_add = compile_module(&binop_module("f", Ty::I8, BinOp::Add)).unwrap();
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
                let bytes = compile_module(&binop_module("f", ty.clone(), op))
                    .unwrap_or_else(|e| panic!("{ty:?} {op:?}: {e}"));
                assert_wasm_header(&bytes);
            }
        }
    }

    /// Fail-closed: `trunc_sat` saturates to the CARRIER's range, so a
    /// float→narrow cast is refused by name rather than clamped at the wrong
    /// bound.
    #[test]
    fn refuses_a_float_to_narrow_integer_cast() {
        let mut mb = ModuleBuilder::new("m");
        let ft = mb.add_func_type(vec![Ty::F32], vec![Ty::U8]);
        let mut fb = mb.function("narrow_fptoui", ft);
        let e = fb.create_block();
        let x = fb.add_block_param(e, Ty::F32);
        fb.switch_to_block(e);
        let r = fb.cast(CastOp::FPToUISat, Ty::F32, Ty::U8, x);
        fb.ret(vec![r]);
        fb.build();
        let err = compile_module(&wasm32(mb.build())).unwrap_err();
        assert!(
            matches!(err, WasmLowerError::NarrowLegalization(_)),
            "{err}"
        );
        assert!(err.to_string().contains("trunc_sat"), "{err}");
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
            wasm32(mb.build())
        };

        // Owned memory: the initializer's LITTLE-ENDIAN byte image ships in a
        // data segment, and the module reads it back through linear memory.
        let bytes = compile_module(&table_module()).unwrap();
        assert_wasm_header(&bytes);
        assert!(
            bytes.windows(4).any(|w| w == [0x4d, 0x3c, 0x2b, 0x1a]),
            "the global's byte image must ship in a data segment"
        );

        let island = WasmModulePolicy::island("tables");
        let err = compile_module_with_policy(&table_module(), &island).unwrap_err();
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
        let err = compile_module_with_policy(&frame_module(), &policy).unwrap_err();
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
        let bytes = compile_module_with_policy(&frame_module(), &owned).unwrap();
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
        let module = mb.build();
        assert!(module.target_info.is_none(), "probe must be target-free");

        let mut wasm_module = WasmModule::new();
        let err = lower_function(
            &mut wasm_module,
            &module.functions[0],
            &module,
            WasmFunctionEnv::empty(),
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
        let err = compile_module(&module).unwrap_err();
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
        let err = compile_module(&module).unwrap_err();
        assert!(matches!(err, WasmLowerError::TargetMismatch(_)), "{err}");
        let msg = err.to_string();
        assert!(msg.contains("aarch64-apple-darwin"), "{msg}");
        assert!(msg.contains("pointer_size 8"), "{msg}");
        assert!(msg.contains("wasm32_target_info"), "{msg}");
    }

    /// The canonical constructor passes the guard by construction.
    #[test]
    fn accepts_canonical_wasm32_target_info() {
        assert_wasm_header(&compile_module(&sum_to_module()).unwrap());
    }

    /// A call to a multi-return callee is refused: the call lowering binds
    /// exactly one result, so lowering it would leave a stack value undropped.
    #[test]
    fn refuses_multi_result_direct_call() {
        use trust_ir::{
            Block as TrustIrBlock, FuncId, FuncTy, Function as TrustIrFunction, InstrNode, ValueId,
        };

        let mut module = Module::new("multi_result_call");
        let pair_ty = module.add_func_type(FuncTy {
            params: vec![],
            returns: vec![Ty::I32, Ty::I32],
            is_vararg: false,
        });
        let one_ty = module.add_func_type(FuncTy {
            params: vec![],
            returns: vec![Ty::I32],
            is_vararg: false,
        });

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
                InstrNode::new(Inst::Call {
                    callee: FuncId::new(0),
                    args: vec![],
                })
                .with_results(vec![ValueId::new(10)]),
                InstrNode::new(Inst::Return {
                    values: vec![ValueId::new(10)],
                }),
            ],
        }];
        module.add_function(callee);
        module.add_function(caller);

        let err = compile_module(&wasm32(module)).unwrap_err();
        assert!(
            matches!(err, WasmLowerError::UnsupportedMultiResultCall(_)),
            "{err}"
        );
        assert!(err.to_string().contains("2 return values"), "{err}");
    }

    /// A function declared with a non-C calling convention is refused.
    #[test]
    fn refuses_non_c_calling_convention_function() {
        let mut module = sum_to_module();
        module.functions[0].calling_conv = CallingConv::Rust;
        let err = compile_module(&module).unwrap_err();
        assert!(
            matches!(err, WasmLowerError::UnsupportedCallingConv(_)),
            "{err}"
        );
        assert!(err.to_string().contains("Rust"), "{err}");
        assert!(err.to_string().contains("CallingConv::C"), "{err}");
    }

    /// The call-contract scan covers the COMPLETE function: a non-C
    /// `call_indirect` in an unreachable block is still refused.
    #[test]
    fn refuses_non_c_indirect_call_in_unreachable_block() {
        use trust_ir::{
            Block as TrustIrBlock, FuncId, FuncTy, Function as TrustIrFunction, InstrNode, ValueId,
        };

        let mut module = Module::new("unreachable_fast_call");
        let void_ty = module.add_func_type(FuncTy {
            params: vec![],
            returns: vec![],
            is_vararg: false,
        });
        let mut func = TrustIrFunction::new(FuncId::new(0), "f", void_ty, BlockId::new(0));
        func.blocks = vec![
            TrustIrBlock {
                id: BlockId::new(0),
                params: vec![],
                body: vec![InstrNode::new(Inst::Return { values: vec![] })],
            },
            // Unreachable from the entry.
            TrustIrBlock {
                id: BlockId::new(1),
                params: vec![],
                body: vec![
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
        module.add_function(func);

        let err = compile_module(&wasm32(module)).unwrap_err();
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
        let (bytes, ev) = compile_module_with_evidence(&module).unwrap();
        assert_eq!(bytes, compile_module(&module).unwrap());
        assert_wasm_header(&bytes);

        assert_eq!(ev.schema, WASM_COMPILE_EVIDENCE_SCHEMA);
        assert_eq!(ev.target, crate::wasm::target::WASM32_TRIPLE);
        assert_eq!(ev.verification_route, EvidenceStrength::NotRun);
        assert_eq!(ev.verdict, ProofEvidenceVerdict::MissingEvidence);
        assert!(ev.ran.contains(&"wasm32_target_info_guard"));
        assert!(ev.ran.contains(&"multi_result_call_guard"));
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
        let (bytes, ev) = compile_module_with_evidence(&sum_to_module()).unwrap();

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
        assert_eq!(bytes, compile_module(&sum_to_module()).unwrap());
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
        wasm32(mb.build())
    }

    /// The closed policy is the pre-P2 backend, byte for byte.
    #[test]
    fn the_closed_policy_is_the_default_compile() {
        for module in [sum_to_module(), frame_module()] {
            assert_eq!(
                compile_module(&module).unwrap(),
                compile_module_with_policy(&module, &WasmModulePolicy::closed()).unwrap(),
            );
        }
    }

    /// Under the island policy the module binds a host contract, and the
    /// evidence REPORTS it — the honest widening of the claimed surface.
    #[test]
    fn island_evidence_reports_the_bound_host_contract() {
        let module = frame_module();
        let policy = WasmModulePolicy::island("memhash");
        let (bytes, ev) = compile_module_with_evidence_and_policy(&module, &policy).unwrap();
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
        assert_ne!(bytes, compile_module(&module).unwrap());
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
        let err = compile_module_with_policy(&frame_module(), &policy).unwrap_err();
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
        let err = compile_module_with_policy(&frame_module(), &policy).unwrap_err();
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
        let bytes = compile_module_with_policy(&sum_to_module(), &policy).unwrap();
        assert_wasm_header(&bytes);
        // Byte-identical to the closed compile: neither emits a memory.
        assert_eq!(bytes, compile_module(&sum_to_module()).unwrap());
    }

    /// A body-less function is a declaration: refused by the closed lane,
    /// bound to a host import by the island lane.
    #[test]
    fn a_declaration_is_refused_closed_and_imported_by_an_island() {
        let declaration_module = || {
            let mut mb = ModuleBuilder::new("decl");
            let ft = mb.add_func_type(vec![Ty::I32], vec![Ty::I32]);
            mb.function("host_fn", ft).build();
            wasm32(mb.build())
        };
        let err = compile_module(&declaration_module()).unwrap_err();
        assert!(
            matches!(err, WasmLowerError::UnboundDeclaration(_)),
            "{err}"
        );
        assert!(err.to_string().contains("host_fn"), "{err}");

        let policy = WasmModulePolicy {
            func_imports: WasmFuncImportPolicy::FromModule(island_host_namespace("decl")),
            ..WasmModulePolicy::closed()
        };
        let (bytes, ev) =
            compile_module_with_evidence_and_policy(&declaration_module(), &policy).unwrap();
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
        let mut module = wasm32(mb.build());
        module.functions[0].calling_conv = CallingConv::Rust;

        let policy = WasmModulePolicy {
            func_imports: WasmFuncImportPolicy::FromModule(island_host_namespace("decl_conv")),
            ..WasmModulePolicy::closed()
        };
        let err = compile_module_with_policy(&module, &policy).unwrap_err();
        assert!(
            matches!(err, WasmLowerError::UnsupportedCallingConv(_)),
            "{err}"
        );
        assert!(err.to_string().contains("host_fn"), "{err}");
    }
}
