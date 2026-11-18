// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Slice 25 of the x86-64 source-bound body theorem: scaled-index (SIB)
//! memory rows and memory-destination `add`/`xor` (ruling OD-227).
//! `X86Peephole`'s address folds turn the selector's `lea t, [b + i*s + d];
//! mov v, [t]` into one row `mov v, [b + i*s + d]` (a SIB load or store,
//! its base a virtual register or, after `sib_base_lea_fold`, a stack
//! slot), and its RMW fusion turns `mov t, [m]; add d, t, s; mov [m], d`
//! into `add [m], s`. The owner states a SIB row as the address `LeaSib`
//! computes, by `LeaSib`'s own code, followed by the access without the
//! index through the unchanged slice 4/13/15/17 code, and an `add`/`xor`
//! into incoming memory as that access's load, the operation and its store.
//!
//! Fixtures take their LIR from the trust-ir adapter (translated with an
//! explicit `Permit`) and their machine stream from the real x86-64
//! instruction selector (`super::select`), then from the real x86 pass
//! pipeline at O2 (`X86Pipeline::run_x86_optimization_passes`), which makes
//! the SIB and RMW rows; [`slice25_pair`] asserts nothing, and
//! `every_fixture_has_its_row` asserts each fixture's row is there (an
//! inherited opt-out knob cannot hollow a fixture). Synthetic edits are
//! disclosed by [`Shape25::synthetic`]: [`Shape25::ByteMerge`] (no selector
//! path emits `MovRM8`, so its `MovRM8Sib` is the real `MovzxRM8Sib` with
//! its opcode edited), [`Shape25::AddCarry`] (the fusion declines while
//! the carry is live, so its three rows are fused by hand), and the constant
//! field/slot forms whose current O2 stream uses plain memory displacements.
//! Those forms are independently checked on the unchanged production stream
//! and reconstructed with the exact same address for the SIB-specific controls.
//! Every test here runs without a solver (the
//! `x86_source_bound_body::tests::slice25::` library gate); the replay on
//! AY and Clean is in `slice25_qualification`.
//!
//! Everything above the "Controls" section uses only the slice 1-24a API,
//! so the same fixtures are judged by the code before slice 25 (the
//! fails-before record of the 2026-11-04 report).

use super::slice5::describe;
use super::slice6::describe_lir;
use super::slice24::owner_holds;
use super::*;
use trust_ir::{BinOp, ICmpOp, OverflowOp};

// ---------------------------------------------------------------------------
// Fixtures
// ---------------------------------------------------------------------------

/// Slice-25 fixture shapes (design §5.2), each a correct lowering.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Shape25 {
    // ---- R: incoming memory through `[v + v*s + d]`
    /// R1: `fn(p: *const u8, i: u64) -> u32 { p[i] as u32 }`: `MovzxRM8Sib
    /// [v + v*1]`.
    ByteZext,
    /// R2: `fn(p: *const u64, i: u64) -> u64 { p[i] }`: `MovRMSib [p +
    /// t*1]` with `t = imul i, 8` (the `ret` keeps the multiply's flags
    /// live, so the fold leaves it out of the scale).
    U64Index,
    /// R3: `fn(p: *const u8, off: u64) -> u64 { *(p.add(off) as *const u64)
    /// }`: `MovRMSib [v + v*1]`.
    ByteOffsetU64,
    /// R4: `fn(p: *const u32, i: u64) -> u32 { p[i] }`: `MovRM32Sib [p +
    /// t*1]` with `t = imul i, 4`.
    U32Index,
    /// R2 scaled: `fn(p: *const u64, i: u64, x: u64) -> u64 { p[i] + x }`:
    /// the `add` overwrites the flags the index's `imul` wrote, so the fold
    /// takes the multiply into the scale, `MovRMSib [v + v*8]` (the slice-14
    /// dispatch shape over a data pointer).
    U64Scaled,
    /// R4 scaled by a shift: `fn(p: *const u8, i: u64, x: u32) -> u32 {
    /// *(p.add(i << 2) as *const u32) + x }`: `MovRM32Sib [v + v*4]`.
    U32Scaled,
    /// R5: `fn(p: *const u8, i: u64) -> u32 { *(p.add(i).add(16) as *const
    /// u32) }`: `LeaSib b, [p + i*1]`, the 16 in a register `c`, and
    /// `MovRM32 [b + 16]` at O2; the SIB control explicitly reconstructs
    /// `MovRM32Sib [b + c*1]` with `c = 16`.
    FieldU32,
    /// R5': `fn(p: *const u8, i: u64) -> u32 { *(p.add(i).sub(16) as *const
    /// u32) }`: R5's rows with displacement and reconstructed `c = -16`.
    FieldBelowU32,
    /// R5 with a later `add`: `fn(p: *const u8, i: u64, x: u32) -> u32 {
    /// *(p.add(16).add(i) as *const u32) + x }`.
    FieldDispU32,
    /// R6: `fn(p: *mut u8, i: u64, x: u8) { p[i] = x }`: `MovMR8Sib`.
    StoreByte,
    /// R6: `fn(p: *mut u32, i: u64, x: u32) { p[i] = x }`: `MovMR32Sib`.
    StoreU32,
    /// R6: `fn(p: *mut u64, i: u64, x: u64) { p[i] = x }`: `MovMRSib`.
    StoreU64,
    /// R6 scaled: `fn(p: *mut u64, i: u64, x: u64, y: u64) -> u64 { p[i] = x;
    /// x + y }`: `MovMRSib [v + v*8]`.
    StoreScaled,
    /// R7: `fn(p: *const f64, i: u64) -> f64 { p[i] }`: `MovsdRMSib`.
    F64Index,
    /// R7: `fn(p: *const f32, i: u64) -> f32 { p[i] }`: `MovssRMSib`.
    F32Index,
    /// R8 (synthetic): `fn(p: *const u8, i: u64) -> u8 { p[i] }`, its
    /// `MovzxRM8Sib` edited to `MovRM8Sib` (no selector path emits a
    /// merging byte load into a virtual register): the returned AL is the
    /// loaded byte, bits 8..63 a free input.
    ByteMerge,
    /// R2 in a merged block (slice 24a, OD-226): `fn(p: *const u64, i: u64,
    /// x: u64) -> u64 { if x != 0 { let s = p[i] + x; s } else { 0 } }`, the
    /// `then` arm a chain of two LIR blocks (an argument-free `Jump` into a
    /// block no other edge enters) that `X86BlockMerge` joins: the
    /// `MovRMSib [v + v*8]` is stated over the merged-chain quotient.
    MergedScaled,
    // ---- S: private stack slots
    /// S1: `fn(x: u64, y: u64) -> u64 { a: [u64; 4]; a[1] = x; a[2] = y;
    /// a[1] }`, every element `a.gep[k]` at a constant index: `[StackSlot +
    /// t*1]` with `t = imul k, 8` of a constant `k`, walked as a frame
    /// address. Current O2 folds these into plain displacements; the SIB
    /// control explicitly reconstructs each exact constant-index address.
    SlotConstU64,
    /// S2: S1 with the constant index defined in the entry block and the
    /// accesses in its successors (a diamond).
    SlotConstAcrossBlocks,
    /// S3: `fn(i: u64) -> u8 { T: [u8; 16]; if i < 16 { T[i] } else { panic
    /// } }`: `[StackSlot + v*1]`, an indexed address whose site the stamp
    /// names.
    SlotGuardedByte,
    /// S4: `fn(x: u32, y: u32) -> u32 { a: [u32; 4]; a[0] = x; a[3] = y;
    /// a[0] + a[3] }`: plain constant-displacement stores and reloads at O2,
    /// reconstructed as exact SIB accesses for this slice's controls.
    SlotStoreReloadU32,
    /// S5: `fn(i: u64) -> u32 { T: [u8; 16]; if i < 16 { *(i + &T) as u32 +
    /// 1 } else { panic } }`, the address `i + &T` (the index first): `[v +
    /// a*1]` with `a` the slot's address, at scale 1, read the other way
    /// round.
    SlotCommuted,
    /// S6: `fn(i: u64) -> u32 { a: [u32; 300]; fill(&mut a); if i < 300 {
    /// a[i] } else { panic } }`: an indexed address whose stamp names a site
    /// of modulus 4 (300 candidates; every offset of the 1200-byte slot would
    /// be 1197, past the lane's 1024).
    SlotBigU32Table,
    /// S7: `fn(i: u64, x: u64) { a: [u64; 16]; fill64(&mut a); if i < 16 {
    /// a[i] = x; fill64(&mut a) } else { panic } }`: an indexed scaled-index
    /// STORE into a slot (slice 17's update), observed by the second call.
    SlotIndexedStore,
    /// S6 in a merged block (slice 24a, OD-226): S6's indexed load in the
    /// bounds check's in-bounds block, which jumps (argument-free) into the
    /// block that returns the value, the two joined by `X86BlockMerge`: the
    /// stamp that sizes the indexed access's candidates is the quotient's
    /// renumbered one.
    MergedBigU32Table,
    // ---- M: memory-destination `add`/`xor` (RMW) of incoming memory
    /// M1: `fn(p: *mut u64, x: u64) { *p += x }`: `AddMR [v + 0], v`.
    AddInto,
    /// M1: `fn(p: *mut u64, x: u64) { *(p.add(16) as *mut u64) += x }` (a
    /// byte offset): `AddMRSib [v + c*1], v`, the offset in a register.
    AddIntoField,
    /// M2: `fn(p: *mut u64, x: u64) { *p ^= x }`: `XorMR`.
    XorInto,
    /// M3: `fn(p: *mut u64, i: u64, x: u64) { p[i] += x }`: `AddMRSib`.
    AddIntoIndexed,
    /// M3: `fn(p: *mut u64, i: u64, x: u64) { p[i] ^= x }`: `XorMRSib`.
    XorIntoIndexed,
    /// M4 (synthetic): `fn(p: *mut u64, x: u64) -> bool { let (s, c) =
    /// (*p).overflowing_add(x); *p = s; c }`: the fusion declines while the
    /// carry is live, so its `mov t, [p]; add s, t, x; setc; mov [p], s` is
    /// fused by hand into `add [p], x; setc`, the carry read after the fused
    /// add.
    AddCarry,
    /// M1 in a merged block (OD-226), shaped as `MergedScaled`:
    /// `fn(p: *mut u64, x: u64) -> u64 { if x != 0 { *p += x; y = x + 1;
    /// goto tail; tail: return y } return 0 }`, `then` and `tail` joined by
    /// `X86BlockMerge`: the fused `AddMR` stated over the quotient.
    MergedAddInto,
}

/// Every slice-25 fixture shape.
pub(crate) const SLICE_TWENTY_FIVE: [Shape25; 32] = [
    Shape25::ByteZext,
    Shape25::U64Index,
    Shape25::ByteOffsetU64,
    Shape25::U32Index,
    Shape25::U64Scaled,
    Shape25::U32Scaled,
    Shape25::FieldU32,
    Shape25::FieldBelowU32,
    Shape25::FieldDispU32,
    Shape25::StoreByte,
    Shape25::StoreU32,
    Shape25::StoreU64,
    Shape25::StoreScaled,
    Shape25::F64Index,
    Shape25::F32Index,
    Shape25::ByteMerge,
    Shape25::MergedScaled,
    Shape25::SlotConstU64,
    Shape25::SlotConstAcrossBlocks,
    Shape25::SlotGuardedByte,
    Shape25::SlotStoreReloadU32,
    Shape25::SlotCommuted,
    Shape25::SlotBigU32Table,
    Shape25::SlotIndexedStore,
    Shape25::MergedBigU32Table,
    Shape25::AddInto,
    Shape25::AddIntoField,
    Shape25::XorInto,
    Shape25::AddIntoIndexed,
    Shape25::XorIntoIndexed,
    Shape25::AddCarry,
    Shape25::MergedAddInto,
];

impl Shape25 {
    fn name(self) -> String {
        let name = format!("{self:?}");
        let mut snake = String::from("s25_");
        for (i, c) in name.chars().enumerate() {
            if c.is_ascii_uppercase() && i > 0 {
                snake.push('_');
            }
            snake.push(c.to_ascii_lowercase());
        }
        snake
    }

    /// The rows the fixture is for: each must be in its machine stream.
    pub(crate) fn expected(self) -> &'static [X86Opcode] {
        use Shape25::*;
        match self {
            ByteZext | SlotGuardedByte | SlotCommuted => &[X86Opcode::MovzxRM8Sib],
            U64Index | ByteOffsetU64 | U64Scaled | MergedScaled | SlotConstAcrossBlocks => {
                &[X86Opcode::MovRMSib]
            }
            U32Index | U32Scaled | FieldU32 | FieldBelowU32 | FieldDispU32 | SlotBigU32Table
            | MergedBigU32Table => &[X86Opcode::MovRM32Sib],
            StoreByte => &[X86Opcode::MovMR8Sib],
            StoreU32 => &[X86Opcode::MovMR32Sib],
            StoreU64 | StoreScaled | SlotIndexedStore => &[X86Opcode::MovMRSib],
            F64Index => &[X86Opcode::MovsdRMSib],
            F32Index => &[X86Opcode::MovssRMSib],
            ByteMerge => &[X86Opcode::MovRM8Sib],
            SlotConstU64 => &[X86Opcode::MovMRSib, X86Opcode::MovRMSib],
            SlotStoreReloadU32 => &[X86Opcode::MovMR32Sib, X86Opcode::MovRM32Sib],
            AddInto | AddCarry | MergedAddInto => &[X86Opcode::AddMR],
            XorInto => &[X86Opcode::XorMR],
            AddIntoIndexed | AddIntoField => &[X86Opcode::AddMRSib],
            XorIntoIndexed => &[X86Opcode::XorMRSib],
        }
    }

    /// The synthetic edit of a fixture that no producer makes, if any.
    pub(crate) fn synthetic(self) -> Option<&'static str> {
        match self {
            Shape25::ByteMerge => Some("MovzxRM8Sib edited to MovRM8Sib"),
            Shape25::AddCarry => Some("MovRM, AddRR and MovMR fused into AddMR by hand"),
            Shape25::FieldU32
            | Shape25::FieldBelowU32
            | Shape25::SlotConstU64
            | Shape25::SlotStoreReloadU32
            | Shape25::AddIntoField => Some(
                "plain constant-displacement accesses reconstructed as exact same-address SIB rows",
            ),
            _ => None,
        }
    }

    fn constant_displacement(self) -> bool {
        matches!(
            self,
            Self::FieldU32
                | Self::FieldBelowU32
                | Self::SlotConstU64
                | Self::SlotStoreReloadU32
                | Self::AddIntoField
        )
    }
}

/// Translate one function of `builder`'s module under the explicit Permit
/// the workspace's fixtures use.
fn translate25(builder: ModuleBuilder, name: &str) -> Function {
    let module = builder.build().expect("ModuleBuilder::build: test fixture");
    trust_cg_lower::translate_module_for_arch_with_tls_with_license(
        &module,
        trust_cg_lower::GuardCarrierArch::X86_64,
        trust_cg_lower::TlsDialect::default(),
        &crate::license_test_support::permit_unlicensed(),
    )
    .unwrap_or_else(|error| panic!("{name}: fixture translates: {error:?}"))
    .into_iter()
    .map(|(function, _)| function)
    .find(|function| function.name == name)
    .unwrap_or_else(|| panic!("{name}: no translated function"))
}

type Builder25<'a> = trust_ir_build::FunctionBuilder<'a>;
type V25 = trust_ir::value::ValueId;

/// `if index < bound { .. } else { panic_bounds(index, bound); trap }`: the
/// in-bounds block current.
fn bounds_check25(f: &mut Builder25<'_>, panic: trust_ir::FuncId, index: V25, bound: u64) {
    let (ok, fail) = (f.create_block(), f.create_block());
    let limit = f.iconst(Ty::U64, i128::from(bound));
    let test = f.icmp(ICmpOp::Ult, Ty::U64, index, limit);
    f.condbr(test, ok, vec![], fail, vec![]);
    f.switch_to_block(fail);
    f.call_void(panic, vec![index, limit]);
    f.unreachable();
    f.switch_to_block(ok);
}

/// The 16-byte local digit table, stored as two 8-byte constants.
fn table25(f: &mut Builder25<'_>, ty: Ty) -> V25 {
    let t = f.alloca(ty);
    let bytes = b"0123456789abcdef";
    for half in 0..2 {
        let word = u64::from_le_bytes(bytes[8 * half..8 * half + 8].try_into().unwrap());
        let value = f.iconst(Ty::U64, i128::from(word));
        let at = if half == 0 {
            t
        } else {
            f.gep_byte_offset(t, 8)
        };
        f.store(Ty::U64, at, value);
    }
    t
}

/// The LIR the trust-ir adapter produces for a slice-25 shape.
pub(crate) fn slice25_lir(shape: Shape25) -> Function {
    use Shape25::*;
    let mut builder = ModuleBuilder::new("x86_source_bound_body_slice25");
    let array = |builder: &mut ModuleBuilder, element: Ty, count: u64| {
        let element = builder.add_type(element);
        Ty::Array(element, count)
    };
    let u8x16 = array(&mut builder, Ty::U8, 16);
    let u64x4 = array(&mut builder, Ty::U64, 4);
    let u32x4 = array(&mut builder, Ty::U32, 4);
    let ptr = |ty: Ty| Ty::PtrMut(Box::new(ty));
    let panic_ty = builder.add_func_type(vec![Ty::U64, Ty::U64], vec![]);
    let panic = builder.declare_function("panic_bounds", panic_ty);
    let fill_ty = builder.add_func_type(vec![ptr(Ty::U32)], vec![]);
    let fill = builder.declare_function("fill", fill_ty);
    let u32x300 = array(&mut builder, Ty::U32, 300);
    let u64x16 = array(&mut builder, Ty::U64, 16);
    let fill64_ty = builder.add_func_type(vec![ptr(Ty::U64)], vec![]);
    let fill64 = builder.declare_function("fill64", fill64_ty);
    let (params, results): (Vec<Ty>, Vec<Ty>) = match shape {
        ByteZext => (vec![ptr(Ty::U8), Ty::U64], vec![Ty::U32]),
        U64Index => (vec![ptr(Ty::U64), Ty::U64], vec![Ty::U64]),
        ByteOffsetU64 => (vec![ptr(Ty::U8), Ty::U64], vec![Ty::U64]),
        U64Scaled | MergedScaled => (vec![ptr(Ty::U64), Ty::U64, Ty::U64], vec![Ty::U64]),
        U32Scaled => (vec![ptr(Ty::U8), Ty::U64, Ty::U32], vec![Ty::U32]),
        FieldDispU32 => (vec![ptr(Ty::U8), Ty::U64, Ty::U32], vec![Ty::U32]),
        StoreScaled => (vec![ptr(Ty::U64), Ty::U64, Ty::U64, Ty::U64], vec![Ty::U64]),
        U32Index => (vec![ptr(Ty::U32), Ty::U64], vec![Ty::U32]),
        FieldU32 | FieldBelowU32 => (vec![ptr(Ty::U8), Ty::U64], vec![Ty::U32]),
        StoreByte => (vec![ptr(Ty::U8), Ty::U64, Ty::U8], vec![]),
        StoreU32 => (vec![ptr(Ty::U32), Ty::U64, Ty::U32], vec![]),
        StoreU64 => (vec![ptr(Ty::U64), Ty::U64, Ty::U64], vec![]),
        F64Index => (vec![ptr(Ty::F64), Ty::U64], vec![Ty::F64]),
        F32Index => (vec![ptr(Ty::F32), Ty::U64], vec![Ty::F32]),
        ByteMerge => (vec![ptr(Ty::U8), Ty::U64], vec![Ty::U8]),
        SlotConstU64 | SlotConstAcrossBlocks => (vec![Ty::U64, Ty::U64], vec![Ty::U64]),
        SlotGuardedByte => (vec![Ty::U64], vec![Ty::U8]),
        SlotCommuted => (vec![Ty::U64], vec![Ty::U32]),
        SlotStoreReloadU32 => (vec![Ty::U32, Ty::U32], vec![Ty::U32]),
        SlotBigU32Table | MergedBigU32Table => (vec![Ty::U64], vec![Ty::U32]),
        SlotIndexedStore => (vec![Ty::U64, Ty::U64], vec![]),
        AddInto | AddIntoField | XorInto => (vec![ptr(Ty::U64), Ty::U64], vec![]),
        MergedAddInto => (vec![ptr(Ty::U64), Ty::U64], vec![Ty::U64]),
        AddIntoIndexed | XorIntoIndexed => (vec![ptr(Ty::U64), Ty::U64, Ty::U64], vec![]),
        AddCarry => (vec![ptr(Ty::U64), Ty::U64], vec![Ty::Bool]),
    };
    let signature = builder.add_func_type(params.clone(), results);
    let name = shape.name();
    let mut f = builder.function(name.clone(), signature);
    let entry = f.create_block();
    let args: Vec<V25> = params
        .iter()
        .map(|ty| f.add_block_param(entry, ty.clone()))
        .collect();
    f.switch_to_block(entry);
    match shape {
        ByteZext => {
            let at = f.gep(Ty::U8, args[0], vec![args[1]]);
            let byte = f.load(Ty::U8, at);
            let wide = f.zext(Ty::U8, Ty::U32, byte);
            f.ret(vec![wide]);
        }
        ByteMerge => {
            let at = f.gep(Ty::U8, args[0], vec![args[1]]);
            let byte = f.load(Ty::U8, at);
            f.ret(vec![byte]);
        }
        U64Index | U32Index | F64Index | F32Index => {
            let element = match shape {
                U64Index => Ty::U64,
                U32Index => Ty::U32,
                F64Index => Ty::F64,
                _ => Ty::F32,
            };
            let at = f.gep(element.clone(), args[0], vec![args[1]]);
            let value = f.load(element, at);
            f.ret(vec![value]);
        }
        ByteOffsetU64 => {
            let at = f.gep(Ty::U8, args[0], vec![args[1]]);
            let value = f.load(Ty::U64, at);
            f.ret(vec![value]);
        }
        U64Scaled => {
            let at = f.gep(Ty::U64, args[0], vec![args[1]]);
            let value = f.load(Ty::U64, at);
            let sum = f.add(Ty::U64, value, args[2]);
            f.ret(vec![sum]);
        }
        MergedScaled => {
            let (then, tail, otherwise) = (f.create_block(), f.create_block(), f.create_block());
            let zero = f.iconst(Ty::U64, 0);
            let test = f.icmp(ICmpOp::Ne, Ty::U64, args[2], zero);
            f.condbr(test, then, vec![], otherwise, vec![]);
            f.switch_to_block(then);
            let at = f.gep(Ty::U64, args[0], vec![args[1]]);
            let value = f.load(Ty::U64, at);
            let sum = f.add(Ty::U64, value, args[2]);
            f.br(tail, vec![]);
            f.switch_to_block(tail);
            f.ret(vec![sum]);
            f.switch_to_block(otherwise);
            f.ret(vec![zero]);
        }
        U32Scaled => {
            let amount = f.iconst(Ty::U64, 2);
            let offset = f.binop(BinOp::Shl, Ty::U64, args[1], amount);
            let at = f.gep(Ty::U8, args[0], vec![offset]);
            let value = f.load(Ty::U32, at);
            let sum = f.add(Ty::U32, value, args[2]);
            f.ret(vec![sum]);
        }
        FieldDispU32 => {
            let field = f.gep_byte_offset(args[0], 16);
            let at = f.gep(Ty::U8, field, vec![args[1]]);
            let value = f.load(Ty::U32, at);
            let sum = f.add(Ty::U32, value, args[2]);
            f.ret(vec![sum]);
        }
        StoreScaled => {
            let at = f.gep(Ty::U64, args[0], vec![args[1]]);
            f.store(Ty::U64, at, args[2]);
            let sum = f.add(Ty::U64, args[2], args[3]);
            f.ret(vec![sum]);
        }
        FieldU32 | FieldBelowU32 => {
            let at = f.gep(Ty::U8, args[0], vec![args[1]]);
            let offset = f.iconst(Ty::I64, if shape == FieldU32 { 16 } else { -16 });
            let field = f.gep(Ty::U8, at, vec![offset]);
            let value = f.load(Ty::U32, field);
            f.ret(vec![value]);
        }
        StoreByte | StoreU32 | StoreU64 => {
            let element = match shape {
                StoreByte => Ty::U8,
                StoreU32 => Ty::U32,
                _ => Ty::U64,
            };
            let at = f.gep(element.clone(), args[0], vec![args[1]]);
            f.store(element, at, args[2]);
            f.ret(vec![]);
        }
        SlotConstU64 => {
            let a = f.alloca(u64x4.clone());
            let one = f.iconst(Ty::U64, 1);
            let two = f.iconst(Ty::U64, 2);
            let first = f.gep(Ty::U64, a, vec![one]);
            f.store(Ty::U64, first, args[0]);
            let second = f.gep(Ty::U64, a, vec![two]);
            f.store(Ty::U64, second, args[1]);
            let again = f.gep(Ty::U64, a, vec![one]);
            let value = f.load(Ty::U64, again);
            f.ret(vec![value]);
        }
        SlotConstAcrossBlocks => {
            let a = f.alloca(u64x4.clone());
            let one = f.iconst(Ty::U64, 1);
            let zero = f.iconst(Ty::U64, 0);
            let (left, right, join) = (f.create_block(), f.create_block(), f.create_block());
            let test = f.icmp(ICmpOp::Ne, Ty::U64, args[0], zero);
            f.condbr(test, left, vec![], right, vec![]);
            f.switch_to_block(left);
            let at = f.gep(Ty::U64, a, vec![one]);
            f.store(Ty::U64, at, args[1]);
            f.br(join, vec![]);
            f.switch_to_block(right);
            let at = f.gep(Ty::U64, a, vec![one]);
            let bumped = f.add(Ty::U64, args[1], one);
            f.store(Ty::U64, at, bumped);
            f.br(join, vec![]);
            f.switch_to_block(join);
            let at = f.gep(Ty::U64, a, vec![one]);
            let value = f.load(Ty::U64, at);
            f.ret(vec![value]);
        }
        SlotGuardedByte => {
            let t = table25(&mut f, u8x16.clone());
            bounds_check25(&mut f, panic, args[0], 16);
            let at = f.gep(Ty::U8, t, vec![args[0]]);
            let value = f.load(Ty::U8, at);
            f.ret(vec![value]);
        }
        SlotCommuted => {
            let t = table25(&mut f, u8x16.clone());
            bounds_check25(&mut f, panic, args[0], 16);
            let address = f.cast(trust_ir::CastOp::PtrToInt, Ty::Ptr, Ty::U64, t);
            let sum = f.add(Ty::U64, args[0], address);
            let at = f.cast(trust_ir::CastOp::IntToPtr, Ty::U64, Ty::Ptr, sum);
            let value = f.load(Ty::U8, at);
            let wide = f.zext(Ty::U8, Ty::U32, value);
            let one = f.iconst(Ty::U32, 1);
            let bumped = f.add(Ty::U32, wide, one);
            f.ret(vec![bumped]);
        }
        SlotBigU32Table | MergedBigU32Table => {
            let a = f.alloca(u32x300.clone());
            f.call_void(fill, vec![a]);
            bounds_check25(&mut f, panic, args[0], 300);
            let at = f.gep(Ty::U32, a, vec![args[0]]);
            let value = f.load(Ty::U32, at);
            if shape == MergedBigU32Table {
                let tail = f.create_block();
                f.br(tail, vec![]);
                f.switch_to_block(tail);
            }
            f.ret(vec![value]);
        }
        SlotIndexedStore => {
            let a = f.alloca(u64x16.clone());
            f.call_void(fill64, vec![a]);
            bounds_check25(&mut f, panic, args[0], 16);
            let at = f.gep(Ty::U64, a, vec![args[0]]);
            f.store(Ty::U64, at, args[1]);
            f.call_void(fill64, vec![a]);
            f.ret(vec![]);
        }
        MergedAddInto => {
            let (then, tail, otherwise) = (f.create_block(), f.create_block(), f.create_block());
            let zero = f.iconst(Ty::U64, 0);
            let test = f.icmp(ICmpOp::Ne, Ty::U64, args[1], zero);
            f.condbr(test, then, vec![], otherwise, vec![]);
            f.switch_to_block(then);
            let old = f.load(Ty::U64, args[0]);
            let new = f.add(Ty::U64, old, args[1]);
            f.store(Ty::U64, args[0], new);
            let one = f.iconst(Ty::U64, 1);
            let bumped = f.add(Ty::U64, args[1], one);
            f.br(tail, vec![]);
            f.switch_to_block(tail);
            f.ret(vec![bumped]);
            f.switch_to_block(otherwise);
            f.ret(vec![zero]);
        }
        SlotStoreReloadU32 => {
            let a = f.alloca(u32x4.clone());
            let zero = f.iconst(Ty::U64, 0);
            let three = f.iconst(Ty::U64, 3);
            let first = f.gep(Ty::U32, a, vec![zero]);
            f.store(Ty::U32, first, args[0]);
            let last = f.gep(Ty::U32, a, vec![three]);
            f.store(Ty::U32, last, args[1]);
            let first = f.gep(Ty::U32, a, vec![zero]);
            let x = f.load(Ty::U32, first);
            let last = f.gep(Ty::U32, a, vec![three]);
            let y = f.load(Ty::U32, last);
            let sum = f.add(Ty::U32, x, y);
            f.ret(vec![sum]);
        }
        AddInto | XorInto | AddIntoField => {
            let at = if shape == AddIntoField {
                f.gep_byte_offset(args[0], 16)
            } else {
                args[0]
            };
            let old = f.load(Ty::U64, at);
            let op = if shape == XorInto {
                BinOp::Xor
            } else {
                BinOp::Add
            };
            let new = f.binop(op, Ty::U64, old, args[1]);
            f.store(Ty::U64, at, new);
            f.ret(vec![]);
        }
        AddIntoIndexed | XorIntoIndexed => {
            let at = f.gep(Ty::U64, args[0], vec![args[1]]);
            let old = f.load(Ty::U64, at);
            let op = if shape == XorIntoIndexed {
                BinOp::Xor
            } else {
                BinOp::Add
            };
            let new = f.binop(op, Ty::U64, old, args[2]);
            f.store(Ty::U64, at, new);
            f.ret(vec![]);
        }
        AddCarry => {
            let old = f.load(Ty::U64, args[0]);
            let (sum, carry) = f.overflow(OverflowOp::AddOverflow, Ty::U64, old, args[1]);
            f.store(Ty::U64, args[0], sum);
            f.ret(vec![carry]);
        }
    }
    f.build();
    translate25(builder, &name)
}

/// The machine stream of `source`: the real selector, then the real x86
/// pass pipeline at `opt_level` (O0: the selector's stream).
pub(crate) fn optimized(source: &Function, opt_level: trust_cg_opt::OptLevel) -> X86ISelFunction {
    use trust_cg_codegen::x86_64::pipeline::{X86Pipeline, X86PipelineConfig};
    let mut machine = select(source, X86CallAbi::SystemV);
    X86Pipeline::new(X86PipelineConfig {
        opt_level,
        call_abi: X86CallAbi::SystemV,
        ..X86PipelineConfig::default()
    })
    .run_x86_optimization_passes(&mut machine);
    machine
}

/// The walk ordinals of every row with one of `opcodes`.
pub(crate) fn rows_with(machine: &X86ISelFunction, opcodes: &[X86Opcode]) -> Vec<usize> {
    rows(machine)
        .into_iter()
        .filter(|(_, block, index)| opcodes.contains(&machine.blocks[block].insts[*index].opcode))
        .map(|(ordinal, _, _)| ordinal)
        .collect()
}

/// The slice-25 SIB access and read-modify-write opcodes.
pub(crate) const SLICE25_ROWS: [X86Opcode; 13] = [
    X86Opcode::MovRMSib,
    X86Opcode::MovRM32Sib,
    X86Opcode::MovRM8Sib,
    X86Opcode::MovzxRM8Sib,
    X86Opcode::MovsdRMSib,
    X86Opcode::MovssRMSib,
    X86Opcode::MovMRSib,
    X86Opcode::MovMR32Sib,
    X86Opcode::MovMR8Sib,
    X86Opcode::AddMR,
    X86Opcode::XorMR,
    X86Opcode::AddMRSib,
    X86Opcode::XorMRSib,
];

/// A slice-25 fixture pair: the adapter's LIR and the real O2 stream, with
/// the fixture's synthetic edit applied ([`Shape25::synthetic`]).
pub(crate) fn slice25_pair(shape: Shape25) -> (Function, X86ISelFunction) {
    let source = slice25_lir(shape);
    let mut machine = optimized(&source, trust_cg_opt::OptLevel::O2);
    if shape.constant_displacement() {
        reconstruct_constant_sib(shape, &mut machine);
    }
    if shape == Shape25::ByteMerge {
        for row in rows_with(&machine, &[X86Opcode::MovzxRM8Sib]) {
            inst_mut(&mut machine, row).opcode = X86Opcode::MovRM8Sib;
        }
    }
    if shape == Shape25::AddCarry {
        fuse_rmw_by_hand(&mut machine);
    }
    (source, machine)
}

/// A disclosed synthetic inverse of the constant-index address fold. Preserve
/// the actual access width, value, metadata and base, and materialize its exact
/// signed displacement as an index. A directly defined frame base is expressed
/// as its identical stack slot, as the original slice's private-SIB controls
/// require. No optimizer or model policy changes here.
fn reconstruct_constant_sib(shape: Shape25, machine: &mut X86ISelFunction) {
    use X86Opcode as Op;
    let accesses = rows_with(
        machine,
        &[Op::MovRM, Op::MovMR, Op::MovRM32, Op::MovMR32, Op::AddMR],
    );
    assert!(
        !accesses.is_empty(),
        "{shape:?}: no production memory access"
    );
    // Walk backwards so insertions preserve each as-yet-unprocessed ordinal.
    for row in accesses.into_iter().rev() {
        let (opcode, operand) = match inst(machine, row).opcode {
            Op::MovRM => (Op::MovRMSib, 1),
            Op::MovMR => (Op::MovMRSib, 0),
            Op::MovRM32 => (Op::MovRM32Sib, 1),
            Op::MovMR32 => (Op::MovMR32Sib, 0),
            Op::AddMR => (Op::AddMRSib, 0),
            _ => unreachable!(),
        };
        let O::MemAddr { mut base, disp } = inst(machine, row).operands[operand].clone() else {
            panic!("{shape:?}: plain memory operand\n{}", describe(machine));
        };
        if matches!(shape, Shape25::SlotConstU64 | Shape25::SlotStoreReloadU32) {
            let definition = defining_row(machine, row, &base).expect("the actual frame base");
            let [
                _,
                O::MemAddr {
                    base: slot,
                    disp: 0,
                },
            ] = inst(machine, definition).operands.as_slice()
            else {
                panic!("{shape:?}: frame base must be an exact zero-offset slot LEA");
            };
            assert_eq!(inst(machine, definition).opcode, Op::Lea);
            assert!(matches!(slot.as_ref(), O::StackSlot(_)));
            base = slot.clone();
        }
        let scale = if shape == Shape25::SlotConstU64 { 8 } else { 1 };
        assert_eq!(i64::from(disp) % i64::from(scale), 0);
        let constant = i64::from(disp) / i64::from(scale);
        assert_eq!(constant * i64::from(scale), i64::from(disp));
        let index = vreg(machine.next_vreg);
        machine.next_vreg = machine
            .next_vreg
            .checked_add(1)
            .expect("fresh fixture vreg");
        let original = inst(machine, row).clone();
        let rewritten = inst_mut(machine, row);
        rewritten.opcode = opcode;
        rewritten.operands[operand] = O::SibMemAddr {
            base,
            index: Box::new(index.clone()),
            scale,
            disp: 0,
        };
        assert_eq!(
            rewritten.operands[1 - operand],
            original.operands[1 - operand]
        );
        assert_eq!(rewritten.flags, opcode.default_flags());
        insert_at(
            machine,
            row,
            X86ISelInst::new(Op::MovRI, vec![index, O::Imm(constant)]),
        );
    }
}

/// Independently re-fold only actual constant-index memory operands for the
/// fixture image comparison. Remove only complete default MovRI instructions
/// defining the fresh register range; keep every other instruction and field.
/// Canonicalize a frame base only through its actual zero-offset slot LEA.
/// This is a machine-data check, not an SMT simplifier or proof authority.
fn refold_fixture_image(machine: &X86ISelFunction, first_fresh: u32) -> String {
    use X86Opcode as Op;
    assert!(first_fresh <= machine.next_vreg);
    let mut image = machine.clone();
    let mut constants = Vec::new();
    let mut fresh_ids = std::collections::BTreeSet::new();
    for (row, _, _) in rows(machine) {
        let node = inst(machine, row);
        if let Some(O::VReg(register)) = node.operands.first()
            && register.id >= first_fresh
        {
            assert_eq!(register.class, RegClass::Gpr64);
            assert!(register.id < machine.next_vreg);
            assert!(matches!(node.operands.as_slice(), [O::VReg(_), O::Imm(_)]));
            let expected = X86ISelInst::new(Op::MovRI, node.operands.clone());
            assert_eq!(format!("{node:?}"), format!("{expected:?}"));
            assert!(fresh_ids.insert(register.id), "one fresh definition");
            constants.push(row);
            continue;
        }
        let (opcode, operand) = match node.opcode {
            Op::MovRM | Op::MovRMSib => (Op::MovRM, 1),
            Op::MovMR | Op::MovMRSib => (Op::MovMR, 0),
            Op::MovRM32 | Op::MovRM32Sib => (Op::MovRM32, 1),
            Op::MovMR32 | Op::MovMR32Sib => (Op::MovMR32, 0),
            Op::AddMR | Op::AddMRSib => (Op::AddMR, 0),
            _ => continue,
        };
        let (mut base, disp) = match &node.operands[operand] {
            O::MemAddr { base, disp } => (base.clone(), *disp),
            O::SibMemAddr {
                base, scale, disp, ..
            } => {
                let constant = constant_of(machine, row, operand);
                let offset = constant
                    .checked_mul(i64::from(*scale))
                    .and_then(|value| value.checked_add(i64::from(*disp)))
                    .and_then(|value| i32::try_from(value).ok())
                    .expect("the actual constant SIB address fits its displacement");
                (base.clone(), offset)
            }
            _ => panic!("the fixture memory operand"),
        };
        if let Some(definition) = defining_row(machine, row, &base)
            && inst(machine, definition).opcode == Op::Lea
            && let [
                _,
                O::MemAddr {
                    base: slot,
                    disp: 0,
                },
            ] = inst(machine, definition).operands.as_slice()
            && matches!(slot.as_ref(), O::StackSlot(_))
        {
            base = slot.clone();
        }
        let folded = inst_mut(&mut image, row);
        folded.opcode = opcode;
        folded.operands[operand] = O::MemAddr { base, disp };
    }
    assert_eq!(
        fresh_ids,
        (first_fresh..machine.next_vreg).collect::<std::collections::BTreeSet<_>>()
    );
    for row in constants.into_iter().rev() {
        remove_at(&mut image, row);
    }
    image.next_vreg = first_fresh;
    format!("{image:#?}")
}

/// [`Shape25::AddCarry`]'s synthetic edit: its `mov t, [m]; add s, t, x;
/// ..; mov [m], s` fused into `add [m], x` as `X86Peephole`'s fusion fuses
/// it where the flags are dead (the fused row unattributed, as the fusion
/// leaves it).
fn fuse_rmw_by_hand(machine: &mut X86ISelFunction) {
    let first = |machine: &X86ISelFunction, opcode: X86Opcode| {
        *rows_with(machine, &[opcode])
            .first()
            .unwrap_or_else(|| panic!("no {opcode:?} row\n{}", describe(machine)))
    };
    let (load, add, store) = (
        first(machine, X86Opcode::MovRM),
        first(machine, X86Opcode::AddRR),
        first(machine, X86Opcode::MovMR),
    );
    assert!(load < add && add < store, "{}", describe(machine));
    let [loaded, address] = inst(machine, load).operands.as_slice() else {
        panic!("MovRM [dst, address]");
    };
    let (loaded, address) = (loaded.clone(), address.clone());
    let addend = inst(machine, add).operands[1..]
        .iter()
        .find(|operand| **operand != loaded)
        .expect("the added register")
        .clone();
    assert_eq!(inst(machine, store).operands[0], address, "one address");
    remove_at(machine, store);
    *inst_mut(machine, add) = X86ISelInst::new(X86Opcode::AddMR, vec![address, addend]);
    remove_at(machine, load);
}

/// The owner of a slice-25 pair (the production entry, System V).
pub(crate) fn owner25<'a>(
    source: &'a Function,
    machine: &'a X86ISelFunction,
) -> Result<SourceBoundX86Body<'a>, X86BodyRefusal> {
    source_bound_x86_body(source, machine, SYSV)
}

/// A refusal's text, or `stated`.
pub(crate) fn refusal_text25(result: &Result<SourceBoundX86Body<'_>, X86BodyRefusal>) -> String {
    match result {
        Ok(_) => "stated".into(),
        Err(refusal) => format!("{refusal}"),
    }
}

/// The slice-25 rows of `machine`, each as `ordinal opcode operands`.
pub(crate) fn slice25_rows(machine: &X86ISelFunction) -> Vec<String> {
    rows_with(machine, &SLICE25_ROWS)
        .into_iter()
        .map(|row| {
            let inst = inst(machine, row);
            format!("{row} {:?} {:?}", inst.opcode, inst.operands)
        })
        .collect()
}

/// The `LeaSib` controls whose refusal texts slice 25 must keep
/// (`refactor_is_byte_identical`): each an O0 selector stream (whose
/// `LeaSib` is the selector's own `ArrayGep` row) with that row edited. An
/// undefined base; a private base with an undefined index; a private base at
/// a constant index whose offset overflows; and the base and index swapped,
/// so the base holds bits and the scale-1 index a private address (which
/// `LeaSib` reads as a value: it never commutes).
pub(crate) fn lea_sib_controls() -> Vec<(&'static str, Function, X86ISelFunction)> {
    let level = trust_cg_opt::OptLevel::O0;
    let edit = |shape: Shape25, what: &'static str, f: &dyn Fn(&mut X86ISelFunction, usize)| {
        let source = slice25_lir(shape);
        let mut machine = optimized(&source, level);
        let row = *rows_with(&machine, &[X86Opcode::LeaSib])
            .first()
            .unwrap_or_else(|| panic!("{what}: no LeaSib row\n{}", describe(&machine)));
        f(&mut machine, row);
        (what, source, machine)
    };
    let sib = |machine: &mut X86ISelFunction, row: usize| -> (O, O, u8, i32) {
        let O::SibMemAddr {
            base,
            index,
            scale,
            disp,
        } = &inst(machine, row).operands[1]
        else {
            panic!("LeaSib operand");
        };
        ((**base).clone(), (**index).clone(), *scale, *disp)
    };
    let set = |machine: &mut X86ISelFunction, row: usize, base: O, index: O, scale: u8, disp| {
        inst_mut(machine, row).operands[1] = O::SibMemAddr {
            base: Box::new(base),
            index: Box::new(index),
            scale,
            disp,
        };
    };
    vec![
        edit(
            Shape25::U64Index,
            "lea_sib_undefined_base",
            &|machine, row| {
                let (_, index, scale, disp) = sib(machine, row);
                set(machine, row, vreg(9_999), index, scale, disp);
            },
        ),
        edit(
            Shape25::SlotGuardedByte,
            "lea_sib_private_base_undefined_index",
            &|machine, row| {
                let (base, _, scale, disp) = sib(machine, row);
                set(machine, row, base, vreg(9_999), scale, disp);
            },
        ),
        edit(
            Shape25::SlotConstU64,
            "lea_sib_overflow",
            &|machine, row| {
                let (base, _, _, disp) = sib(machine, row);
                insert_at(
                    machine,
                    row,
                    X86ISelInst::new(X86Opcode::MovRI, vec![vreg(9_999), O::Imm(i64::MAX / 2)]),
                );
                set(machine, row + 1, base, vreg(9_999), 8, disp);
            },
        ),
        edit(
            Shape25::SlotGuardedByte,
            "lea_sib_bits_base_frame_index",
            &|machine, row| {
                let (base, index, _, disp) = sib(machine, row);
                set(machine, row, index, base, 1, disp);
            },
        ),
    ]
}

/// The refusal texts of the `LeaSib` controls ([`lea_sib_controls`]) as the
/// code before slice 25 gives them (the fails-before record's `S25_LEA_SIB`
/// lines, the body-domain opcode list written `<BODY_OPCODES>`): `LeaSib`
/// keeps its own arms, reads its base before its index, and never commutes.
pub(crate) const LEA_SIB_TEXTS: &[(&str, &str)] = &[
    (
        "lea_sib_undefined_base",
        "source-bound x86-64 body mismatch: row 4 reads v9999, which holds no defined value",
    ),
    (
        "lea_sib_private_base_undefined_index",
        "unsupported source-bound x86-64 body: machine row 6 is outside the body domain \
         (<BODY_OPCODES>): LeaSib reads the private stack address in v1 as a value (the slot's \
         address escapes)",
    ),
    (
        "lea_sib_overflow",
        "unsupported source-bound x86-64 body: machine row 8 is outside the body domain \
         (<BODY_OPCODES>): overflows a private stack offset",
    ),
    (
        "lea_sib_bits_base_frame_index",
        "unsupported source-bound x86-64 body: machine row 6 is outside the body domain \
         (<BODY_OPCODES>): LeaSib reads the private stack address in v1 as a value (the slot's \
         address escapes)",
    ),
];

/// Each `LeaSib` control's refusal text, the body-domain opcode list written
/// `<BODY_OPCODES>` (slice 25 extends that list, nothing else).
pub(crate) fn lea_sib_texts() -> Vec<(&'static str, String)> {
    lea_sib_controls()
        .into_iter()
        .map(|(what, source, machine)| {
            let text = refusal_text25(&owner25(&source, &machine));
            (what, text.replace(BODY_OPCODES, "<BODY_OPCODES>"))
        })
        .collect()
}

/// The `LeaSib` refactor of slice 25 (`sib_private`, `sib_bits`) is
/// byte-identical: every `LeaSib` control refuses with the text the code
/// before slice 25 gives (every snapshot digest of slices 1-24a is its own
/// test).
#[test]
fn refactor_is_byte_identical() {
    let texts = lea_sib_texts();
    assert_eq!(texts.len(), LEA_SIB_TEXTS.len());
    for ((what, text), (label, expected)) in texts.iter().zip(LEA_SIB_TEXTS) {
        assert_eq!(what, label);
        assert_eq!(text, expected, "{what}");
    }
}

/// Every fixture's slice-25 row is in its machine stream (an inherited
/// opt-out knob cannot hollow a fixture), and the opt-outs of the FP and
/// scale-1 SIB folds and of the RMW fusion are unset.
#[test]
fn every_fixture_has_its_row() {
    assert!(
        [
            "TCG_NO_X86_SIB_FP_FOLD",
            "TCG_NO_X86_SIB_SCALE1_FOLD",
            "TCG_NO_X86_RMW_FUSE"
        ]
        .into_iter()
        .all(|knob| std::env::var_os(knob).is_none()),
        "a slice-25 fold is opted out of in this environment"
    );
    for shape in SLICE_TWENTY_FIVE {
        let (_, machine) = slice25_pair(shape);
        for opcode in shape.expected() {
            assert!(
                !rows_with(&machine, &[*opcode]).is_empty(),
                "{shape:?}: no {opcode:?} row\n{}",
                describe(&machine)
            );
        }
        if let Err(why) = named_operand(shape, &machine) {
            panic!("{shape:?}: {why}\n{}", describe(&machine));
        }
    }
}

/// Constant-index folding is exercised as real production output separately
/// from this slice's explicitly reconstructed SIB forms. Keep the complete
/// access widths and live displacements, and require both bodies to hold.
#[test]
fn constant_displacement_production_streams_and_synthetic_sib_are_both_checked() {
    use Shape25::*;
    use X86Opcode as Op;
    for (shape, opcodes, expected_displacements) in [
        (FieldU32, &[Op::MovRM32][..], &[16][..]),
        (FieldBelowU32, &[Op::MovRM32][..], &[-16][..]),
        (SlotConstU64, &[Op::MovMR, Op::MovRM][..], &[8, 16][..]),
        (
            SlotStoreReloadU32,
            &[Op::MovMR32, Op::MovRM32][..],
            &[0, 12][..],
        ),
        (AddIntoField, &[Op::AddMR][..], &[16][..]),
    ] {
        let source = slice25_lir(shape);
        let production = optimized(&source, trust_cg_opt::OptLevel::O2);
        let mut displacements = Vec::new();
        for opcode in opcodes {
            let accesses = rows_with(&production, &[*opcode]);
            assert!(!accesses.is_empty(), "{shape:?}: no production {opcode:?}");
            for row in accesses {
                let address = inst(&production, row)
                    .operands
                    .iter()
                    .find_map(|operand| {
                        if let O::MemAddr { disp, .. } = operand {
                            Some(*disp)
                        } else {
                            None
                        }
                    })
                    .expect("the live production memory operand");
                displacements.push(address);
            }
        }
        displacements.sort_unstable();
        displacements.dedup();
        assert_eq!(displacements, expected_displacements, "{shape:?}");
        holds25(&source, &production).unwrap_or_else(|why| panic!("{shape:?} production: {why}"));
        let mut synthetic = production.clone();
        reconstruct_constant_sib(shape, &mut synthetic);
        holds25(&source, &synthetic).unwrap_or_else(|why| panic!("{shape:?} synthetic: {why}"));
        assert!(shape.synthetic().is_some());
        // Added initialized constants extend the SSA formula, so equal raw
        // SMT text is not an invariant. Check the complete refolded machine
        // image, including every non-memory row and all stored metadata.
        assert_eq!(
            refold_fixture_image(&production, production.next_vreg),
            refold_fixture_image(&synthetic, production.next_vreg),
            "{shape:?}: exact refolded machine image"
        );
    }
}

/// The operand a fixture is named for, on every one of its rows
/// ([`Shape25::expected`]): a stack-slot base for the S fixtures; for
/// `SlotCommuted` a register base and an index a `lea` of the slot defines;
/// scale 8 or 4 for the scaled fixtures. The golden cannot tell a stack-slot
/// base from a register holding the same frame address, so this does.
/// The last row before `row` that writes register `register`
/// (`destination_reg`: a compare, a store or a branch naming it first reads
/// it), and through any plain `mov` copies, the row that defines the value.
fn defining_row(machine: &X86ISelFunction, row: usize, register: &O) -> Option<usize> {
    let mut register = register.clone();
    let mut before = row;
    loop {
        let wanted = gpr(&register)?;
        let at = (0..before)
            .rev()
            .find(|at| destination_reg(inst(machine, *at)) == Some(wanted))?;
        match (
            inst(machine, at).opcode,
            inst(machine, at).operands.as_slice(),
        ) {
            (X86Opcode::MovRR, [_, source @ O::VReg(_)]) => {
                register = source.clone();
                before = at;
            }
            _ => return Some(at),
        }
    }
}

fn named_operand(shape: Shape25, machine: &X86ISelFunction) -> Result<(), String> {
    use Shape25::*;
    let fixture_rows = rows_with(machine, shape.expected());
    // One scaled-index row: its index, base, index register and scale.
    type SibRow = (usize, O, O, u8);
    let operands: Vec<SibRow> = fixture_rows
        .iter()
        .filter_map(|row| {
            inst(machine, *row)
                .operands
                .iter()
                .find_map(|operand| match operand {
                    O::SibMemAddr {
                        base, index, scale, ..
                    } => Some((*row, (**base).clone(), (**index).clone(), *scale)),
                    _ => None,
                })
        })
        .collect();
    let every = |what: &str, holds: &dyn Fn(&SibRow) -> bool| {
        if !operands.is_empty() && operands.iter().all(holds) {
            Ok(())
        } else {
            Err(format!("not every row has {what}: {operands:?}"))
        }
    };
    match shape {
        SlotConstU64
        | SlotConstAcrossBlocks
        | SlotGuardedByte
        | SlotStoreReloadU32
        | SlotBigU32Table
        | SlotIndexedStore
        | MergedBigU32Table => every("a stack-slot base", &|(_, base, _, _)| {
            matches!(base, O::StackSlot(_))
        }),
        SlotCommuted => every(
            "a register base over an index a `lea` of the slot defines",
            &|(row, base, index, scale)| {
                let defined_by_slot_lea = defining_row(machine, *row, index).is_some_and(|at| {
                    let def = inst(machine, at);
                    def.opcode == X86Opcode::Lea
                        && matches!(
                            def.operands.get(1),
                            Some(O::MemAddr { base, .. }) if matches!(base.as_ref(), O::StackSlot(_))
                        )
                });
                matches!(base, O::VReg(_)) && *scale == 1 && defined_by_slot_lea
            },
        ),
        U64Scaled | StoreScaled | MergedScaled | AddIntoIndexed | XorIntoIndexed => {
            every("scale 8", &|(_, _, _, scale)| *scale == 8)
        }
        U32Scaled => every("scale 4", &|(_, _, _, scale)| *scale == 4),
        _ => Ok(()),
    }
}

/// A diagnostic, not a check: the refusal text of every `LeaSib` control
/// ([`lea_sib_controls`]).
#[test]
#[ignore]
fn print_lea_sib_control_refusals() {
    for (what, source, machine) in lea_sib_controls() {
        println!(
            "S25_LEA_SIB control={what} result={}",
            refusal_text25(&owner25(&source, &machine))
        );
    }
}

/// A diagnostic, not a check: every fixture's LIR, its machine stream at
/// O1, O2 and O3, its slice-25 rows and the owner's outcome.
#[test]
#[ignore]
fn print_slice_twenty_five_fixtures() {
    for shape in SLICE_TWENTY_FIVE {
        if let Err(payload) = std::panic::catch_unwind(|| print_fixture25(shape)) {
            let message = payload
                .downcast_ref::<String>()
                .cloned()
                .or_else(|| {
                    payload
                        .downcast_ref::<&str>()
                        .map(|text| (*text).to_owned())
                })
                .unwrap_or_default();
            println!("S25_FIXTURE shape={shape:?} panicked: {message}");
        }
    }
}

/// [`print_slice_twenty_five_fixtures`] for one shape.
fn print_fixture25(shape: Shape25) {
    let source = slice25_lir(shape);
    println!(
        "==== {shape:?}{}\n{}",
        shape
            .synthetic()
            .map(|edit| format!(" (synthetic: {edit})"))
            .unwrap_or_default(),
        describe_lir(&source)
    );
    for level in [
        trust_cg_opt::OptLevel::O1,
        trust_cg_opt::OptLevel::O2,
        trust_cg_opt::OptLevel::O3,
    ] {
        let machine = if level == trust_cg_opt::OptLevel::O2 {
            slice25_pair(shape).1
        } else {
            optimized(&source, level)
        };
        let result = owner25(&source, &machine);
        let holds = result
            .as_ref()
            .map(|owner| owner_holds(owner).is_ok())
            .unwrap_or(false);
        let merged = result.as_ref().ok().and_then(|owner| owner.merged_chains());
        println!(
            "---- {level:?}\n{}S25_FIXTURE shape={shape:?} level={level:?} rows={:?} \
             holds={holds} merged={merged:?} result={}",
            describe(&machine),
            slice25_rows(&machine),
            refusal_text25(&result)
        );
    }
}
// ---------------------------------------------------------------------------
// Edited pairs (the slice 1-24a API only: the fails-before record runs them)
// ---------------------------------------------------------------------------

use super::slice9::dag_refuted_on_samples;
use super::slice14::{DefinedShape, slice14_pair};
use super::slice24::{owner_refuted, text};

/// The first row with `opcode`.
#[track_caller]
fn row_of(machine: &X86ISelFunction, opcode: X86Opcode) -> usize {
    *rows_with(machine, &[opcode])
        .first()
        .unwrap_or_else(|| panic!("no {opcode:?} row\n{}", describe(machine)))
}

/// Edit the scaled-index operand of row `row`.
fn edit_sib(
    machine: &mut X86ISelFunction,
    row: usize,
    edit: impl FnOnce(&mut O, &mut O, &mut u8, &mut i32),
) {
    let inst = inst_mut(machine, row);
    let operand = inst
        .operands
        .iter_mut()
        .find(|operand| matches!(operand, O::SibMemAddr { .. }))
        .expect("a scaled-index operand");
    let O::SibMemAddr {
        base,
        index,
        scale,
        disp,
    } = operand
    else {
        unreachable!("matched");
    };
    edit(base, index, scale, disp);
}

/// The first `opcode` row of `shape`'s pair, its scaled-index operand edited.
fn sib_edit(
    shape: Shape25,
    opcode: X86Opcode,
    edit: impl FnOnce(&mut O, &mut O, &mut u8, &mut i32),
) -> (Function, X86ISelFunction) {
    let (source, mut machine) = slice25_pair(shape);
    let row = row_of(&machine, opcode);
    edit_sib(&mut machine, row, edit);
    (source, machine)
}

/// The first `from` row of `shape`'s pair, its opcode replaced by `to`.
fn opcode_edit(shape: Shape25, from: X86Opcode, to: X86Opcode) -> (Function, X86ISelFunction) {
    let (source, mut machine) = slice25_pair(shape);
    let row = row_of(&machine, from);
    inst_mut(&mut machine, row).opcode = to;
    (source, machine)
}

/// A virtual register of class `class`.
fn vreg_of(id: u32, class: RegClass) -> O {
    O::VReg(VReg::new(id, class))
}

/// The register operand a load's scaled-index row writes, or a store's or
/// read-modify-write's reads.
fn value_operand(inst: &X86ISelInst) -> usize {
    match inst.operands.as_slice() {
        [O::SibMemAddr { .. } | O::MemAddr { .. }, _] => 1,
        _ => 0,
    }
}

/// The owner of `(source, machine)` states it and its theorem holds on
/// samples.
fn holds25(source: &Function, machine: &X86ISelFunction) -> Result<(), String> {
    let owner = owner25(source, machine).map_err(|refusal| format!("refused: {refusal}"))?;
    owner_holds(&owner)
}

/// A wrong lowering is refuted: the theorem without the affine refusal is
/// refuted on samples (or a mismatch names it before a theorem exists), and
/// the owner names a mismatch or states a refuted theorem.
fn refuted25(source: &Function, machine: &X86ISelFunction) -> Result<(), String> {
    match theorem_without_affine_refusal(source, machine, SYSV) {
        Ok(theorem) if dag_refuted_on_samples(&theorem) => {}
        Ok(_) => return Err("its theorem without the affine refusal holds on samples".into()),
        Err(X86BodyRefusal::Mismatch(_)) => {}
        Err(refusal) => {
            return Err(format!(
                "its theorem without the affine refusal is refused: {refusal}"
            ));
        }
    }
    match owner25(source, machine) {
        Err(X86BodyRefusal::Mismatch(_)) => Ok(()),
        Ok(owner) if owner_refuted(&owner) => Ok(()),
        Ok(_) => Err("the owner's theorem holds".into()),
        Err(refusal) => Err(format!("the owner refuses: {refusal}")),
    }
}

/// A wrong lowering is never credited: refused (no claim), a mismatch, or a
/// refuted theorem.
fn never_credited25(source: &Function, machine: &X86ISelFunction) -> Result<(), String> {
    match owner25(source, machine) {
        Err(_) => Ok(()),
        Ok(owner) if owner_refuted(&owner) => Ok(()),
        Ok(_) => Err("a wrong lowering's theorem holds".into()),
    }
}

/// The owner refuses `(source, machine)` with a text containing `needle`.
fn refused25(source: &Function, machine: &X86ISelFunction, needle: &str) -> Result<(), String> {
    match owner25(source, machine) {
        Err(refusal) if format!("{refusal}").contains(needle) => Ok(()),
        Err(refusal) => Err(format!("refused, but not with {needle:?}: {refusal}")),
        Ok(_) => Err(format!("stated, not refused with {needle:?}")),
    }
}

/// The constant the walk's operand `operand` of row `row` names: the
/// `MovRI` that defines it, or a `LeaSib [k + k*s]` of one (the selector's
/// constant index arithmetic).
#[track_caller]
fn constant_of(machine: &X86ISelFunction, row: usize, operand: usize) -> i64 {
    let O::SibMemAddr { index, .. } = &inst(machine, row).operands[operand] else {
        panic!("row {row} operand {operand} is not a scaled-index operand");
    };
    let value = |register: &O| -> Option<i64> {
        (0..row).rev().find_map(|at| {
            let def = inst(machine, at);
            (def.operands.first() == Some(register)).then(|| {
                match (def.opcode, def.operands.as_slice()) {
                    (X86Opcode::MovRI, [_, O::Imm(k)]) => Some(*k),
                    (X86Opcode::XorRR, [_, a, b]) if a == b => Some(0),
                    _ => None,
                }
            })?
        })
    };
    if let Some(k) = value(index) {
        return k;
    }
    let lea = (0..row)
        .rev()
        .find(|at| inst(machine, *at).operands.first() == Some(index.as_ref()))
        .expect("the index's definition");
    match inst(machine, lea).operands.as_slice() {
        [
            _,
            O::SibMemAddr {
                base,
                index,
                scale,
                disp,
            },
        ] if base == index => {
            let k = value(base).expect("a constant LeaSib operand");
            k * (1 + i64::from(*scale)) + i64::from(*disp)
        }
        other => panic!(
            "row {row}'s index is not a constant: {other:?}\n{}",
            describe(machine)
        ),
    }
}

/// Change every actual S1 access to element 1, through its live SIB index
/// definition. A dead selector constant left after O2 folding is no mutant.
fn change_live_slot_one_index(machine: &mut X86ISelFunction, replacement: i64) {
    let mut changed = 0;
    for row in rows_with(machine, &[X86Opcode::MovMRSib, X86Opcode::MovRMSib]) {
        let operand = usize::from(inst(machine, row).opcode == X86Opcode::MovRMSib);
        let O::SibMemAddr {
            base,
            index,
            scale: 8,
            disp: 0,
        } = &inst(machine, row).operands[operand]
        else {
            panic!("S1 must use its live element-index SIB operand");
        };
        assert!(matches!(base.as_ref(), O::StackSlot(_)));
        if constant_of(machine, row, operand) == 1 {
            let definition =
                defining_row(machine, row, index).expect("the live SIB index definition");
            assert_eq!(inst(machine, definition).opcode, X86Opcode::MovRI);
            inst_mut(machine, definition).operands[1] = O::Imm(replacement);
            changed += 1;
        }
    }
    assert_eq!(
        changed, 2,
        "the original element-1 store and reload must both change"
    );
}

/// `shape`'s `MovRM32Sib [b + c*1]`, `b = LeaSib [x + y*1]` and `c` the
/// constant `k`, folded by hand into `[x + y*1 + k]`: a correct synthetic
/// edit (the same effective address), the only source of a nonzero
/// scaled-index displacement here (the pipeline leaves every one zero on
/// these fixtures).
fn folded_into_disp(shape: Shape25) -> (Function, X86ISelFunction) {
    let (source, mut machine) = slice25_pair(shape);
    let row = row_of(&machine, X86Opcode::MovRM32Sib);
    let k = constant_of(&machine, row, 1);
    let O::SibMemAddr { base, .. } = &inst(&machine, row).operands[1] else {
        unreachable!("a scaled-index load");
    };
    let lea = (0..row)
        .rev()
        .find(|at| inst(&machine, *at).operands.first() == Some(base.as_ref()))
        .expect("the base's definition");
    let [
        _,
        O::SibMemAddr {
            base,
            index,
            scale: 1,
            disp: 0,
        },
    ] = inst(&machine, lea).operands.as_slice()
    else {
        panic!("the base is not a LeaSib [x + y*1]\n{}", describe(&machine));
    };
    let folded = O::SibMemAddr {
        base: base.clone(),
        index: index.clone(),
        scale: 1,
        disp: i32::try_from(k).expect("an i32 displacement"),
    };
    inst_mut(&mut machine, row).operands[1] = folded;
    (source, machine)
}

/// The stack slot that row `row`'s scaled-index operand has as its base.
#[track_caller]
fn sib_slot(machine: &X86ISelFunction, row: usize) -> u32 {
    inst(machine, row)
        .operands
        .iter()
        .find_map(|operand| match operand {
            O::SibMemAddr { base, .. } => match base.as_ref() {
                O::StackSlot(slot) => Some(*slot),
                _ => None,
            },
            _ => None,
        })
        .unwrap_or_else(|| panic!("row {row} has no stack-slot base\n{}", describe(machine)))
}

/// Row `row`'s `[slot + x*s + d]` through a FRAME register: `lea f, [slot +
/// lea_disp]` inserted before it, and the row's base `f` (a synthetic edit:
/// the same address at `lea_disp` 0; the pipeline folds such a `lea` into
/// the base).
fn frame_register_base(machine: &mut X86ISelFunction, row: usize, lea_disp: i32) {
    let slot = sib_slot(machine, row);
    let frame = vreg(9_984);
    insert_at(
        machine,
        row,
        X86ISelInst::new(
            X86Opcode::Lea,
            vec![
                frame.clone(),
                O::MemAddr {
                    base: Box::new(O::StackSlot(slot)),
                    disp: lea_disp,
                },
            ],
        ),
    );
    edit_sib(machine, row + 1, |base, _, _, _| *base = frame);
}

/// Row `row`'s `[slot + x*1 + 0]` through an INDEXED register: `lea a,
/// [slot]; LeaSib b, [a + first*1]` inserted before it, and the row's
/// operand `[b + second*1 + disp]` (a synthetic edit: the same address when
/// `first + second + disp` is the row's index).
fn indexed_register_base(
    machine: &mut X86ISelFunction,
    row: usize,
    first: O,
    second: O,
    disp: i32,
) {
    let slot = sib_slot(machine, row);
    let (address, indexed) = (vreg(9_982), vreg(9_983));
    insert_at(
        machine,
        row,
        X86ISelInst::new(
            X86Opcode::Lea,
            vec![
                address.clone(),
                O::MemAddr {
                    base: Box::new(O::StackSlot(slot)),
                    disp: 0,
                },
            ],
        ),
    );
    insert_at(
        machine,
        row + 1,
        X86ISelInst::new(
            X86Opcode::LeaSib,
            vec![
                indexed.clone(),
                O::SibMemAddr {
                    base: Box::new(address),
                    index: Box::new(first),
                    scale: 1,
                    disp: 0,
                },
            ],
        ),
    );
    edit_sib(machine, row + 2, |base, index, scale, d| {
        *base = indexed;
        *index = second;
        *scale = 1;
        *d = disp;
    });
}

/// The two registers whose sum row `row`'s scaled-index index holds: its
/// definition `add k, a, b`, the tied `mov k, a; add k, b`, or `LeaSib k, [a
/// + b*1]`.
#[track_caller]
fn summands(machine: &X86ISelFunction, row: usize) -> (O, O) {
    let index = inst(machine, row)
        .operands
        .iter()
        .find_map(|operand| match operand {
            O::SibMemAddr { index, .. } => Some((**index).clone()),
            _ => None,
        })
        .expect("a scaled-index operand");
    let writes = |at: usize| {
        destination_reg(inst(machine, at)).is_some()
            && destination_reg(inst(machine, at)) == gpr(&index)
    };
    let def = (0..row)
        .rev()
        .find(|at| writes(*at))
        .unwrap_or_else(|| panic!("no definition of {index:?}\n{}", describe(machine)));
    match (
        inst(machine, def).opcode,
        inst(machine, def).operands.as_slice(),
    ) {
        (X86Opcode::AddRR, [_, a, b]) => (a.clone(), b.clone()),
        (X86Opcode::AddRR, [_, b]) => {
            let copy = (0..def)
                .rev()
                .find(|at| writes(*at))
                .expect("the tied copy");
            match inst(machine, copy).operands.as_slice() {
                [_, a] if inst(machine, copy).opcode == X86Opcode::MovRR => (a.clone(), b.clone()),
                other => panic!("not a tied add: {other:?}\n{}", describe(machine)),
            }
        }
        (
            X86Opcode::LeaSib,
            [
                _,
                O::SibMemAddr {
                    base,
                    index,
                    scale: 1,
                    disp: 0,
                },
            ],
        ) => ((**base).clone(), (**index).clone()),
        other => panic!("{index:?} is not a sum: {other:?}\n{}", describe(machine)),
    }
}

/// Every later row's operand `from` (a register) replaced by `to`.
fn rename_after(machine: &mut X86ISelFunction, row: usize, from: &O, to: &O) {
    let total = rows(machine).len();
    for at in row + 1..total {
        for operand in &mut inst_mut(machine, at).operands {
            if operand == from {
                *operand = to.clone();
            }
        }
    }
}

/// The scaled-index load `load` inserted before the first `reader` row of
/// slice 9's `Diamonds5` that reads the join register its first diamond's
/// `else` arm sets to a frame address (`a_root_of_different_kinds_at_a_join_makes_no_claim`):
/// a mixed root, as the load's index (`MovzxRM8Sib [v + root*1]`) or base
/// (`MovRMSib [root + v*8]`).
fn mixed25(load: X86Opcode) -> (Function, X86ISelFunction) {
    use super::slice9::{DagShape, slice9_pair};
    use X86Opcode as Op;
    let (mut source, mut machine) = slice9_pair(DagShape::Diamonds5);
    let copies: Vec<usize> = rows_with(&machine, &[Op::MovRR])
        .into_iter()
        .filter(|row| inst(&machine, row + 1).opcode == Op::Jmp)
        .collect();
    let copy = copies[1];
    let join = inst(&machine, copy).operands[0].clone();
    let provenance = inst(&machine, copy).lowering_provenance;
    let row = inst_mut(&mut machine, copy);
    *row = X86ISelInst::new(
        Op::Lea,
        vec![
            join.clone(),
            O::MemAddr {
                base: Box::new(O::StackSlot(0)),
                disp: 0,
            },
        ],
    );
    row.lowering_provenance = provenance;
    machine.stack_slots = vec![trust_cg_lower::StackSlotInfo::new(8, 8)];
    source.stack_slots = machine.stack_slots.clone();
    if load == Op::MovzxRM8Sib {
        sib_load_reading(&mut machine, &join, Op::CmpRR);
    } else {
        let reader = rows_with(&machine, &[Op::CmpRR])
            .into_iter()
            .find(|row| inst(&machine, *row).operands.contains(&join))
            .unwrap_or_else(|| panic!("no CmpRR reads {join:?}\n{}", describe(&machine)));
        let other = inst(&machine, reader)
            .operands
            .iter()
            .find(|operand| **operand != join)
            .expect("a second operand")
            .clone();
        insert_at(
            &mut machine,
            reader,
            X86ISelInst::new(
                load,
                vec![
                    vreg(9_990),
                    O::SibMemAddr {
                        base: Box::new(join),
                        index: Box::new(other),
                        scale: 8,
                        disp: 0,
                    },
                ],
            ),
        );
    }
    (source, machine)
}

// ---- edited pairs, by label

/// Design §5.5's must-refute edits: each a correct fixture with one row
/// made wrong.
pub(crate) const REFUTED: &[&str] = &[
    "R5 folded, disp 16 to -16",
    "R5 folded, disp plus the scale",
    "R5' folded, disp -16 to 16",
    "R4 scale 4 to 2",
    "R1 scale 1 to 8",
    "R2 scale 8 to 4",
    "R4 base and index swapped at scale 4",
    "R2 base and index swapped at scale 8",
    "R1 movzx to a merging byte load",
    "S1 constant index 1 to 2",
    "S3 disp plus one",
    "S6 scale 1 to 4",
    "M1 add to xor",
    "M2 xor to add",
    "M1 source swapped for the base",
    "M1 disp 0 to 8",
    "M1 base swapped for the source",
    "M3 index disp 0 to 8",
    "M4 setc to seto",
    "S3 frame register at disp 1",
    "S1 frame register at scale 8, constant 2",
    "S3 indexed register, constant index 1",
    "S3 sum through an indexed register, disp 1",
    "S7 store disp plus 8",
    "S7 scale changed",
];

/// Wrong edits whose verdict is a refusal or a refutation, never credit:
/// an incoming access of the wrong width is unpaired (`AccessTrace`).
const NEVER_CREDITED: &[&str] = &[
    "R4 mov32 to mov64",
    "R2 mov64 to mov32",
    "R7 movsd to movss",
    "R6 store8 to store32",
    "S2 scale 8 to 4",
    "S4 store32 to store8",
    "S4 store into another declared slot",
];

/// Design §5.5's must-hold edits.
const NEUTRAL: &[&str] = &[
    "R2 loop load at a zero index",
    "R1 base and index swapped at scale 1",
    "R3 base and index swapped at scale 1",
    "R5 base and index swapped at scale 1",
    "R5 folded into the displacement",
    "R5' folded into the displacement",
    "S4 constant index folded into the displacement",
    "S4 scale at constant index 0",
    "S3 stamp names no site",
    "S3 stamp names another instruction",
    "M4 compare before the add",
    "S3 base through a frame register",
    "S1 base through a frame register at scale 8",
    "S3 base through an indexed register",
    "S3 sum through an indexed register",
];

/// The must-hold edits whose theorems the golden pins and the replay lane
/// certifies: a scaled-index base through a frame register (at a term and,
/// at scale 8, a constant index) and through an indexed register (at a
/// constant and a term index), and the only nonzero scaled-index
/// displacements (the correct hand folds).
pub(crate) const QUALIFIED_EDITS: &[&str] = &[
    "S3 base through a frame register",
    "S1 base through a frame register at scale 8",
    "S3 base through an indexed register",
    "S3 sum through an indexed register",
    "R5 folded into the displacement",
    "R5' folded into the displacement",
    "S4 constant index folded into the displacement",
];

/// The rows slice 14's shape admitted whose verdict slice 25 changes other
/// than by a claim (design §2.4's table): a virtual `MovRMSib [b + i*8 +
/// 0]` was refused at the walk's dispatch arm whatever `b` held; now an
/// undefined base is a named mismatch, a frame register's address a private
/// access, a mixed root the mixed text.
pub(crate) const TRANSITIONS: &[&str] = &[
    "R2s undefined base",
    "S1 base through a frame register at scale 8",
    "R2s mixed base",
];

/// Design §3's must-refuse inputs and the text each refusal contains.
const REFUSALS: &[(&str, &str)] = &[
    ("R1 physical index", "MovzxRM8Sib with operands"),
    ("R1 physical base", "MovzxRM8Sib with operands"),
    ("R2 RBP base", "MovRMSib with operands"),
    ("R1 RSP base", "MovzxRM8Sib with operands"),
    ("R1 scale 3", "MovzxRM8Sib with operands"),
    ("R1 32-bit index", "MovzxRM8Sib with operands"),
    ("R6 physical value register", "MovMR8Sib with operands"),
    (
        "R2 proof origin",
        "MovRMSib carries call, internal-return or proof-origin metadata",
    ),
    (
        "R1 undefined index",
        "reads v9999, which holds no defined value",
    ),
    (
        "R1 undefined base",
        "reads v9999, which holds no defined value",
    ),
    (
        "S5 private index at scale 4",
        "as a value (the slot's address escapes)",
    ),
    (
        "S5 two private components",
        "as a value (the slot's address escapes)",
    ),
    (
        "S3 undeclared slot base",
        "names stack slot 7, which is not declared",
    ),
    (
        "S3 slot as index",
        "references a stack slot outside a modelled",
    ),
    (
        "S3 slot as index under a register base",
        "references a stack slot outside a modelled",
    ),
    (
        "S3 slot base on LeaSib",
        "references a stack slot outside a modelled",
    ),
    ("M1 slot base", "references a stack slot outside a modelled"),
    ("M3 slot base", "references a stack slot outside a modelled"),
    (
        "M1 through a private address",
        "read-modify-writes a private stack slot",
    ),
    (
        "M1 source a private address",
        "as a value (the slot's address escapes)",
    ),
    (
        "M1 against load, call, store",
        "an incoming-memory store where the source's next event is call 0",
    ),
    (
        "M1 against store, load",
        "a load paired with a source store",
    ),
    (
        "M1 against a 4-byte source",
        "a 8-byte access paired with a 4-byte source access",
    ),
    (
        "M2 compare, xor, setcc",
        "reads flags that no compare or test row of its block wrote",
    ),
    (
        "dispatch at scale 4 disp 16",
        "MovRMSib outside the selector's jump-table dispatch",
    ),
    (
        "R2 physical destination",
        "MovRMSib outside the selector's jump-table dispatch",
    ),
    (
        "dispatch through an entry",
        "MovRMSib outside the selector's jump-table dispatch",
    ),
    ("R2 MovsxdRMSib", "carries flags"),
    ("R2 MovdquRMSib", "carries flags"),
    ("R2 ImulRMSib", "carries flags"),
    (
        "S3 big byte table",
        "candidate offsets (the lane admits 1024)",
    ),
    ("S3 unbounded index", "IndexedUnbounded"),
    (
        "R2s undefined base",
        "reads v9999, which holds no defined value",
    ),
    (
        "R1 mixed index",
        "which the paths into its block leave holding different kinds of value",
    ),
    (
        "R2s mixed base",
        "which the paths into its block leave holding different kinds of value",
    ),
    (
        "dispatch at scale 8 disp 0 in a target block",
        "MovRMSib reads jump table 0 outside its dispatch block",
    ),
    (
        "dispatch table base as a MovRM32Sib base",
        "MovRM32Sib reads the jump-table address or entry in",
    ),
    (
        "M3 through a private address",
        "AddMRSib read-modify-writes a private stack slot",
    ),
    (
        "M1 proof origin",
        "AddMR carries call, internal-return or proof-origin metadata",
    ),
    (
        "S3 constant index overflows at scale 8",
        "overflows a private stack offset",
    ),
    (
        "S6 stamp names no site",
        "with 1197 candidate offsets (the lane admits 1 to 1024)",
    ),
    ("R6 store wider than its register", "MovMRSib with operands"),
    ("R2s 32-bit destination", "MovRMSib with operands"),
    (
        "S7 stored value a private address",
        "MovMRSib stores a private stack address through an indexed address",
    ),
    (
        "S7 update over a stored private address",
        "updates private stack slot 0 byte 0, which is unreadable or holds a private stack address",
    ),
    (
        "S3 read over a stored private address",
        "reads private stack slot 0 at candidate offset 0, which is unreadable or holds a private \
         stack address",
    ),
    (
        "R2 physical destination and its reader",
        "MovRMSib outside the selector's jump-table dispatch",
    ),
];

/// A source variant that a control pairs with a fixture's machine stream.
fn variant25(name: &str) -> Function {
    let mut builder = ModuleBuilder::new("x86_source_bound_body_slice25_variants");
    let ptr = |ty: Ty| Ty::PtrMut(Box::new(ty));
    let element = builder.add_type(Ty::U8);
    let u8x16 = Ty::Array(element, 16);
    let u8x1100 = Ty::Array(element, 1100);
    let panic_ty = builder.add_func_type(vec![Ty::U64, Ty::U64], vec![]);
    let panic = builder.declare_function("panic_bounds", panic_ty);
    let fill_ty = builder.add_func_type(vec![ptr(Ty::U8)], vec![]);
    let fill = builder.declare_function("fill_bytes", fill_ty);
    let effect_ty = builder.add_func_type(vec![], vec![]);
    let effect = builder.declare_function("effect", effect_ty);
    let (params, results) = match name {
        "s25_slot_unguarded_byte" => (vec![Ty::U64], vec![Ty::U8]),
        "s25_slot_sum_index" => (vec![Ty::U64, Ty::U64], vec![Ty::U8]),
        "s25_slot_big_byte_table" => (vec![Ty::U64], vec![Ty::U8]),
        "s25_add_into_around_call" | "s25_store_then_load" => (vec![ptr(Ty::U64), Ty::U64], vec![]),
        "s25_add_into_u32" => (vec![ptr(Ty::U64), Ty::U64], vec![]),
        other => unreachable!("{other}"),
    };
    let signature = builder.add_func_type(params.clone(), results);
    let mut f = builder.function(name.to_owned(), signature);
    let entry = f.create_block();
    let args: Vec<V25> = params
        .iter()
        .map(|ty| f.add_block_param(entry, ty.clone()))
        .collect();
    f.switch_to_block(entry);
    match name {
        "s25_slot_unguarded_byte" => {
            let t = table25(&mut f, u8x16);
            let at = f.gep(Ty::U8, t, vec![args[0]]);
            let value = f.load(Ty::U8, at);
            f.ret(vec![value]);
        }
        "s25_slot_sum_index" => {
            let t = table25(&mut f, u8x16);
            let k = f.add(Ty::U64, args[0], args[1]);
            bounds_check25(&mut f, panic, k, 16);
            let at = f.gep(Ty::U8, t, vec![k]);
            let value = f.load(Ty::U8, at);
            f.ret(vec![value]);
        }
        "s25_slot_big_byte_table" => {
            let t = f.alloca(u8x1100);
            f.call_void(fill, vec![t]);
            bounds_check25(&mut f, panic, args[0], 1100);
            let at = f.gep(Ty::U8, t, vec![args[0]]);
            let value = f.load(Ty::U8, at);
            f.ret(vec![value]);
        }
        "s25_add_into_around_call" => {
            let old = f.load(Ty::U64, args[0]);
            f.call_void(effect, vec![]);
            let new = f.add(Ty::U64, old, args[1]);
            f.store(Ty::U64, args[0], new);
            f.ret(vec![]);
        }
        "s25_store_then_load" => {
            f.store(Ty::U64, args[0], args[1]);
            let again = f.load(Ty::U64, args[0]);
            let doubled = f.add(Ty::U64, again, again);
            f.store(Ty::U64, args[0], doubled);
            f.ret(vec![]);
        }
        "s25_add_into_u32" => {
            // AddInto's signature; the source reads 4 bytes, then stores 8.
            let old = f.load(Ty::U32, args[0]);
            let wide = f.zext(Ty::U32, Ty::U64, old);
            let new = f.add(Ty::U64, wide, args[1]);
            f.store(Ty::U64, args[0], new);
            f.ret(vec![]);
        }
        _ => unreachable!(),
    }
    f.build();
    translate25(builder, name)
}

/// The pair a control label names (design §5.5 and §3).
pub(crate) fn case25(label: &str) -> (Function, X86ISelFunction) {
    use Shape25::*;
    use X86Opcode as Op;
    let swap = |base: &mut O, index: &mut O, _: &mut u8, _: &mut i32| std::mem::swap(base, index);
    match label {
        "R5 folded, disp 16 to -16"
        | "R5 folded, disp plus the scale"
        | "R5' folded, disp -16 to 16" => {
            let shape = if label.starts_with("R5'") {
                FieldBelowU32
            } else {
                FieldU32
            };
            let (source, mut machine) = folded_into_disp(shape);
            let row = row_of(&machine, Op::MovRM32Sib);
            edit_sib(&mut machine, row, |_, _, scale, disp| {
                if label == "R5 folded, disp plus the scale" {
                    *disp += i32::from(*scale)
                } else {
                    *disp = -*disp
                }
            });
            (source, machine)
        }
        "R5 folded into the displacement" => folded_into_disp(FieldU32),
        "R5' folded into the displacement" => folded_into_disp(FieldBelowU32),
        "R4 scale 4 to 2" => sib_edit(U32Scaled, Op::MovRM32Sib, |_, _, scale, _| *scale = 2),
        "R1 scale 1 to 8" => sib_edit(ByteZext, Op::MovzxRM8Sib, |_, _, scale, _| *scale = 8),
        "R2 scale 8 to 4" => sib_edit(U64Scaled, Op::MovRMSib, |_, _, scale, _| *scale = 4),
        "R4 base and index swapped at scale 4" => sib_edit(U32Scaled, Op::MovRM32Sib, swap),
        "R2 base and index swapped at scale 8" => sib_edit(U64Scaled, Op::MovRMSib, swap),
        "S1 constant index 1 to 2" => {
            let (source, mut machine) = slice25_pair(SlotConstU64);
            change_live_slot_one_index(&mut machine, 2);
            (source, machine)
        }
        "S2 scale 8 to 4" => {
            let (source, mut machine) = slice25_pair(SlotConstAcrossBlocks);
            let row = *rows_with(&machine, &[Op::MovMRSib])
                .iter()
                .find(|row| {
                    matches!(
                        inst(&machine, **row).operands[0],
                        O::SibMemAddr { scale: 8, .. }
                    )
                })
                .unwrap_or_else(|| panic!("no store at scale 8\n{}", describe(&machine)));
            edit_sib(&mut machine, row, |_, _, scale, _| *scale = 4);
            (source, machine)
        }
        "S4 store32 to store8" => opcode_edit(SlotStoreReloadU32, Op::MovMR32Sib, Op::MovMR8Sib),
        "S4 store into another declared slot" => {
            let (mut source, mut machine) = slice25_pair(SlotStoreReloadU32);
            let slot = machine.stack_slots[0];
            machine.stack_slots.push(slot);
            source.stack_slots = machine.stack_slots.clone();
            let row = row_of(&machine, Op::MovMR32Sib);
            edit_sib(&mut machine, row, |base, _, _, _| *base = O::StackSlot(1));
            (source, machine)
        }
        "S4 constant index folded into the displacement" => {
            // `[slot + c*1]`, `c = lea [k + k*2]` with `k = 4` (12), as
            // `[slot + z*1 + 12]` with `z = 0`: the same address.
            let (source, mut machine) = slice25_pair(SlotStoreReloadU32);
            let zero = rows_with(&machine, &[Op::MovRI])
                .into_iter()
                .find(|row| inst(&machine, *row).operands.get(1) == Some(&O::Imm(0)))
                .map(|row| inst(&machine, row).operands[0].clone())
                .unwrap_or_else(|| panic!("no MovRI 0\n{}", describe(&machine)));
            let row = rows_with(&machine, &[Op::MovMR32Sib])[1];
            let twelve = constant_of(&machine, row, 0);
            assert_eq!(twelve, 12, "{}", describe(&machine));
            edit_sib(&mut machine, row, |_, index, _, disp| {
                *index = zero;
                *disp = 12;
            });
            (source, machine)
        }
        "S4 scale at constant index 0" => {
            let (source, mut machine) = slice25_pair(SlotStoreReloadU32);
            let row = row_of(&machine, Op::MovMR32Sib);
            assert_eq!(constant_of(&machine, row, 0), 0, "{}", describe(&machine));
            edit_sib(&mut machine, row, |_, _, scale, _| *scale = 8);
            (source, machine)
        }
        "R1 movzx to a merging byte load" => opcode_edit(ByteZext, Op::MovzxRM8Sib, Op::MovRM8Sib),
        "S3 disp plus one" => {
            sib_edit(SlotGuardedByte, Op::MovzxRM8Sib, |_, _, _, disp| *disp += 1)
        }
        "S6 scale 1 to 4" => sib_edit(SlotBigU32Table, Op::MovRM32Sib, |_, _, scale, _| *scale = 4),
        "M1 add to xor" => opcode_edit(AddInto, Op::AddMR, Op::XorMR),
        "M2 xor to add" => opcode_edit(XorInto, Op::XorMR, Op::AddMR),
        "M1 source swapped for the base" | "M1 base swapped for the source" => {
            let (source, mut machine) = slice25_pair(AddInto);
            let row = row_of(&machine, Op::AddMR);
            let inst = inst_mut(&mut machine, row);
            let value = inst.operands[1].clone();
            let O::MemAddr { base, .. } = &mut inst.operands[0] else {
                panic!("AddMR [base + disp]");
            };
            if label == "M1 source swapped for the base" {
                let address_base = (**base).clone();
                inst.operands[1] = address_base;
            } else {
                **base = value;
            }
            (source, machine)
        }
        "M1 disp 0 to 8" => {
            let (source, mut machine) = slice25_pair(AddInto);
            let row = row_of(&machine, Op::AddMR);
            let O::MemAddr { disp, .. } = &mut inst_mut(&mut machine, row).operands[0] else {
                panic!("AddMR [base + disp]");
            };
            *disp += 8;
            (source, machine)
        }
        "M3 index disp 0 to 8" => {
            sib_edit(AddIntoIndexed, Op::AddMRSib, |_, _, _, disp| *disp += 8)
        }
        "M4 setc to seto" => {
            let (source, mut machine) = slice25_pair(AddCarry);
            let row = row_of(&machine, Op::Setcc);
            for operand in &mut inst_mut(&mut machine, row).operands {
                if let O::CondCode(code) = operand {
                    *code = trust_cg_ir::X86CondCode::O;
                }
            }
            (source, machine)
        }
        "R4 mov32 to mov64" => opcode_edit(U32Index, Op::MovRM32Sib, Op::MovRMSib),
        "R2 mov64 to mov32" => opcode_edit(U64Index, Op::MovRMSib, Op::MovRM32Sib),
        "R7 movsd to movss" => opcode_edit(F64Index, Op::MovsdRMSib, Op::MovssRMSib),
        "R6 store8 to store32" => opcode_edit(StoreByte, Op::MovMR8Sib, Op::MovMR32Sib),
        "R1 base and index swapped at scale 1" => sib_edit(ByteZext, Op::MovzxRM8Sib, swap),
        "R3 base and index swapped at scale 1" => sib_edit(ByteOffsetU64, Op::MovRMSib, swap),
        "R5 base and index swapped at scale 1" => sib_edit(FieldU32, Op::MovRM32Sib, swap),
        "S3 stamp names no site" | "S3 stamp names another instruction" => {
            let (source, mut machine) = slice25_pair(SlotGuardedByte);
            let row = row_of(&machine, Op::MovzxRM8Sib);
            let inst = inst_mut(&mut machine, row);
            if label == "S3 stamp names no site" {
                inst.lowering_provenance = LoweringProvenance::UNATTRIBUTED;
            } else if let LoweringProvenance::SourceInst { id, .. } = &mut inst.lowering_provenance
            {
                id.index = id.index.wrapping_sub(1);
            } else {
                panic!("S3's access carries its LIR load's stamp");
            }
            (source, machine)
        }
        "M4 compare before the add" => {
            let (source, mut machine) = slice25_pair(AddCarry);
            let row = row_of(&machine, Op::AddMR);
            let addend = inst(&machine, row).operands[1].clone();
            insert_at(
                &mut machine,
                row,
                X86ISelInst::new(Op::CmpRR, vec![addend.clone(), addend]),
            );
            (source, machine)
        }
        "R1 physical index" => {
            sib_edit(ByteZext, Op::MovzxRM8Sib, |_, index, _, _| *index = preg(6))
        }
        "R1 physical base" => sib_edit(ByteZext, Op::MovzxRM8Sib, |base, _, _, _| *base = preg(7)),
        "R2 RBP base" => sib_edit(U64Index, Op::MovRMSib, |base, _, _, _| *base = preg(5)),
        "R1 RSP base" => sib_edit(ByteZext, Op::MovzxRM8Sib, |base, _, _, _| *base = preg(4)),
        "R1 scale 3" => sib_edit(ByteZext, Op::MovzxRM8Sib, |_, _, scale, _| *scale = 3),
        "R1 32-bit index" => sib_edit(ByteZext, Op::MovzxRM8Sib, |_, index, _, _| {
            let O::VReg(vreg) = index else {
                panic!("a virtual index");
            };
            *index = vreg_of(vreg.id, RegClass::Gpr32);
        }),
        "R6 physical value register" => {
            let (source, mut machine) = slice25_pair(StoreByte);
            let row = row_of(&machine, Op::MovMR8Sib);
            let inst = inst_mut(&mut machine, row);
            let at = value_operand(inst);
            inst.operands[at] = preg(2);
            (source, machine)
        }
        "R2 proof origin" => {
            let (source, mut machine) = slice25_pair(U64Index);
            let row = row_of(&machine, Op::MovRMSib);
            inst_mut(&mut machine, row).proof_origin = Some(X86ProofOrigin::AtomicLoad);
            (source, machine)
        }
        "R1 undefined index" => sib_edit(ByteZext, Op::MovzxRM8Sib, |_, index, _, _| {
            *index = vreg(9_999)
        }),
        "R1 undefined base" => sib_edit(ByteZext, Op::MovzxRM8Sib, |base, _, _, _| {
            *base = vreg(9_999)
        }),
        "S5 private index at scale 4" => {
            sib_edit(SlotCommuted, Op::MovzxRM8Sib, |_, _, scale, _| *scale = 4)
        }
        "S5 two private components" => {
            sib_edit(SlotCommuted, Op::MovzxRM8Sib, |base, index, _, _| {
                *base = index.clone()
            })
        }
        "S3 undeclared slot base" => sib_edit(SlotGuardedByte, Op::MovzxRM8Sib, |base, _, _, _| {
            *base = O::StackSlot(7)
        }),
        "S3 slot as index" => sib_edit(SlotGuardedByte, Op::MovzxRM8Sib, |base, index, _, _| {
            *index = base.clone()
        }),
        "S3 slot as index under a register base" => {
            sib_edit(SlotGuardedByte, Op::MovzxRM8Sib, |base, index, _, _| {
                *index = std::mem::replace(base, vreg(9_998))
            })
        }
        "S3 slot base on LeaSib" => {
            let (source, mut machine) = slice25_pair(SlotGuardedByte);
            let row = row_of(&machine, Op::MovzxRM8Sib);
            let address = inst(&machine, row).operands[1].clone();
            insert_at(
                &mut machine,
                row,
                X86ISelInst::new(Op::LeaSib, vec![vreg(9_998), address]),
            );
            (source, machine)
        }
        "M1 slot base" | "M3 slot base" => {
            let shape = if label == "M1 slot base" {
                AddInto
            } else {
                AddIntoIndexed
            };
            let (mut source, mut machine) = slice25_pair(shape);
            let slots = vec![trust_cg_lower::StackSlotInfo::new(8, 8)];
            source.stack_slots = slots.clone();
            machine.stack_slots = slots;
            let row = row_of(
                &machine,
                if shape == AddInto {
                    Op::AddMR
                } else {
                    Op::AddMRSib
                },
            );
            match &mut inst_mut(&mut machine, row).operands[0] {
                O::MemAddr { base, .. } | O::SibMemAddr { base, .. } => **base = O::StackSlot(0),
                other => panic!("an RMW address, not {other:?}"),
            }
            (source, machine)
        }
        "M1 through a private address" | "M1 source a private address" => {
            let (mut source, mut machine) = slice25_pair(AddInto);
            let slots = vec![trust_cg_lower::StackSlotInfo::new(8, 8)];
            source.stack_slots = slots.clone();
            machine.stack_slots = slots;
            let row = row_of(&machine, Op::AddMR);
            insert_at(
                &mut machine,
                row,
                X86ISelInst::new(
                    Op::Lea,
                    vec![
                        vreg(9_997),
                        O::MemAddr {
                            base: Box::new(O::StackSlot(0)),
                            disp: 0,
                        },
                    ],
                ),
            );
            let inst = inst_mut(&mut machine, row + 1);
            if label == "M1 through a private address" {
                let O::MemAddr { base, .. } = &mut inst.operands[0] else {
                    panic!("AddMR [base + disp]");
                };
                **base = vreg(9_997);
            } else {
                inst.operands[1] = vreg(9_997);
            }
            (source, machine)
        }
        "M1 against load, call, store"
        | "M1 against store, load"
        | "M1 against a 4-byte source" => {
            // AddInto's machine against another source of the same name:
            // the pairing is the access trace's, not the function's.
            let machine = slice25_pair(AddInto).1;
            let mut source = variant25(match label {
                "M1 against load, call, store" => "s25_add_into_around_call",
                "M1 against store, load" => "s25_store_then_load",
                _ => "s25_add_into_u32",
            });
            source.name = machine.name.clone();
            (source, machine)
        }
        "M2 compare, xor, setcc" => {
            let (source, mut machine) = slice25_pair(XorInto);
            let row = row_of(&machine, Op::XorMR);
            let value = inst(&machine, row).operands[1].clone();
            insert_at(
                &mut machine,
                row + 1,
                X86ISelInst::new(
                    Op::Setcc,
                    vec![
                        vreg_of(9_996, RegClass::Gpr32),
                        O::CondCode(trust_cg_ir::X86CondCode::E),
                    ],
                ),
            );
            insert_at(
                &mut machine,
                row,
                X86ISelInst::new(Op::CmpRR, vec![value.clone(), value]),
            );
            (source, machine)
        }
        "dispatch at scale 4 disp 16"
        | "dispatch at scale 8 disp 0 in a target block"
        | "dispatch through an entry"
        | "dispatch table base as a MovRM32Sib base" => {
            // The dispatch block stays the selector's idiom (any edit there
            // is the admission's `dispatch idiom` refusal); a further row
            // opens the table's first target block, where the table's
            // address is still live: a `MovRMSib` through it at another
            // scale and displacement, or at the dispatch's own scale 8 and
            // displacement 0, or through the dispatch's loaded entry, or a
            // `MovRM32Sib` through it.
            let (source, mut machine) = slice14_pair(DefinedShape::JumpTable);
            let row = row_of(&machine, Op::MovRMSib);
            let load = inst(&machine, row).clone();
            let O::SibMemAddr { base, index, .. } = &load.operands[1] else {
                panic!("the dispatch load's scaled-index operand");
            };
            let (base, scale, disp) = match label {
                "dispatch at scale 4 disp 16" => ((**base).clone(), 4, 16),
                "dispatch through an entry" => (load.operands[0].clone(), 8, 0),
                "dispatch table base as a MovRM32Sib base" => ((**base).clone(), 4, 0),
                _ => ((**base).clone(), 8, 0),
            };
            let (opcode, value) = if label == "dispatch table base as a MovRM32Sib base" {
                (Op::MovRM32Sib, vreg_of(9_995, RegClass::Gpr32))
            } else {
                (Op::MovRMSib, vreg(9_995))
            };
            let read = X86ISelInst::new(
                opcode,
                vec![
                    value,
                    O::SibMemAddr {
                        base: Box::new(base),
                        index: index.clone(),
                        scale,
                        disp,
                    },
                ],
            );
            let target = machine.jump_tables[0].targets[0];
            machine
                .blocks
                .get_mut(&target)
                .expect("the table's first target block")
                .insts
                .insert(0, read);
            (source, machine)
        }
        "R2 physical destination" => {
            let (source, mut machine) = slice25_pair(U64Scaled);
            let row = row_of(&machine, Op::MovRMSib);
            inst_mut(&mut machine, row).operands[0] = preg(0);
            (source, machine)
        }
        "R2 MovsxdRMSib" => opcode_edit(U64Index, Op::MovRMSib, Op::MovsxdRMSib),
        "R2 MovdquRMSib" => opcode_edit(U64Index, Op::MovRMSib, Op::MovdquRMSib),
        "R2 ImulRMSib" => opcode_edit(U64Index, Op::MovRMSib, Op::ImulRMSib),
        "S3 big byte table" | "S3 unbounded index" => {
            let source = variant25(if label == "S3 big byte table" {
                "s25_slot_big_byte_table"
            } else {
                "s25_slot_unguarded_byte"
            });
            let machine = optimized(&source, trust_cg_opt::OptLevel::O2);
            (source, machine)
        }
        "S3 base through a frame register" | "S3 frame register at disp 1" => {
            let (source, mut machine) = slice25_pair(SlotGuardedByte);
            let row = row_of(&machine, Op::MovzxRM8Sib);
            let lea_disp = i32::from(label == "S3 frame register at disp 1");
            frame_register_base(&mut machine, row, lea_disp);
            (source, machine)
        }
        "S1 base through a frame register at scale 8"
        | "S1 frame register at scale 8, constant 2" => {
            // S1's reload of `a[1]`, `[slot + t*1]` with `t = 8`, as `lea f,
            // [slot]; mov v, [f + k*8 + 0]` over the constant `k` (1): the
            // slice-14 dispatch operand shape over a frame register.
            let (source, mut machine) = slice25_pair(SlotConstU64);
            let one = rows_with(&machine, &[Op::MovRI])
                .into_iter()
                .find(|row| inst(&machine, *row).operands.get(1) == Some(&O::Imm(1)))
                .map(|row| inst(&machine, row).operands[0].clone())
                .unwrap_or_else(|| panic!("no MovRI 1\n{}", describe(&machine)));
            let mut row = row_of(&machine, Op::MovRMSib);
            let index = if label.ends_with("constant 2") {
                insert_at(
                    &mut machine,
                    row,
                    X86ISelInst::new(Op::MovRI, vec![vreg(9_981), O::Imm(2)]),
                );
                row += 1;
                vreg(9_981)
            } else {
                one
            };
            frame_register_base(&mut machine, row, 0);
            edit_sib(&mut machine, row + 1, |_, slot_index, scale, disp| {
                *slot_index = index;
                *scale = 8;
                *disp = 0;
            });
            (source, machine)
        }
        "S3 base through an indexed register" | "S3 indexed register, constant index 1" => {
            // S3's `[slot + i*1]` as `lea a, [slot]; LeaSib b, [a + i*1]; mov
            // z, k; movzx v, [b + z*1]`, `k` 0 (or 1, a wrong address).
            let (source, mut machine) = slice25_pair(SlotGuardedByte);
            let row = row_of(&machine, Op::MovzxRM8Sib);
            let index = inst(&machine, row)
                .operands
                .iter()
                .find_map(|operand| match operand {
                    O::SibMemAddr { index, .. } => Some((**index).clone()),
                    _ => None,
                })
                .expect("S3's scaled-index operand");
            let k = i64::from(label.ends_with("index 1"));
            insert_at(
                &mut machine,
                row,
                X86ISelInst::new(Op::MovRI, vec![vreg(9_981), O::Imm(k)]),
            );
            indexed_register_base(&mut machine, row + 1, index, vreg(9_981), 0);
            (source, machine)
        }
        "S3 sum through an indexed register" | "S3 sum through an indexed register, disp 1" => {
            // `T[i + j]`, whose row is `[slot + k*1]` with `k = i + j`, as
            // `lea a, [slot]; LeaSib b, [a + i*1]; movzx v, [b + j*1]`: an
            // indexed base at a term index.
            let source = variant25("s25_slot_sum_index");
            let mut machine = optimized(&source, trust_cg_opt::OptLevel::O2);
            let row = row_of(&machine, Op::MovzxRM8Sib);
            let (i, j) = summands(&machine, row);
            let disp = i32::from(label.ends_with("disp 1"));
            indexed_register_base(&mut machine, row, i, j, disp);
            (source, machine)
        }
        "R2s undefined base" => {
            sib_edit(U64Scaled, Op::MovRMSib, |base, _, _, _| *base = vreg(9_999))
        }
        "R2s 32-bit destination" => {
            let (source, mut machine) = slice25_pair(U64Scaled);
            let row = row_of(&machine, Op::MovRMSib);
            let O::VReg(destination) = inst(&machine, row).operands[0].clone() else {
                panic!("a virtual destination");
            };
            inst_mut(&mut machine, row).operands[0] = vreg_of(destination.id, RegClass::Gpr32);
            (source, machine)
        }
        "R1 mixed index" => mixed25(Op::MovzxRM8Sib),
        "R2s mixed base" => mixed25(Op::MovRMSib),
        "R2 physical destination and its reader" => {
            // R2's destination and every later read of it the physical RAX:
            // a correct machine, outside the virtual-only row shape.
            let (source, mut machine) = slice25_pair(U64Scaled);
            let row = row_of(&machine, Op::MovRMSib);
            let destination = inst(&machine, row).operands[0].clone();
            inst_mut(&mut machine, row).operands[0] = preg(0);
            rename_after(&mut machine, row, &destination, &preg(0));
            (source, machine)
        }
        "M3 through a private address" => {
            let (mut source, mut machine) = slice25_pair(AddIntoIndexed);
            let slots = vec![trust_cg_lower::StackSlotInfo::new(8, 8)];
            source.stack_slots = slots.clone();
            machine.stack_slots = slots;
            let row = row_of(&machine, Op::AddMRSib);
            insert_at(
                &mut machine,
                row,
                X86ISelInst::new(
                    Op::Lea,
                    vec![
                        vreg(9_997),
                        O::MemAddr {
                            base: Box::new(O::StackSlot(0)),
                            disp: 0,
                        },
                    ],
                ),
            );
            edit_sib(&mut machine, row + 1, |base, _, _, _| *base = vreg(9_997));
            (source, machine)
        }
        "M1 proof origin" => {
            let (source, mut machine) = slice25_pair(AddInto);
            let row = row_of(&machine, Op::AddMR);
            inst_mut(&mut machine, row).proof_origin = Some(X86ProofOrigin::AtomicLoad);
            (source, machine)
        }
        "S3 constant index overflows at scale 8" => {
            let (source, mut machine) = slice25_pair(SlotGuardedByte);
            let row = row_of(&machine, Op::MovzxRM8Sib);
            insert_at(
                &mut machine,
                row,
                X86ISelInst::new(Op::MovRI, vec![vreg(9_999), O::Imm(i64::MAX / 2)]),
            );
            edit_sib(&mut machine, row + 1, |_, index, scale, _| {
                *index = vreg(9_999);
                *scale = 8;
            });
            (source, machine)
        }
        "S6 stamp names no site" => {
            let (source, mut machine) = slice25_pair(SlotBigU32Table);
            let row = row_of(&machine, Op::MovRM32Sib);
            inst_mut(&mut machine, row).lowering_provenance = LoweringProvenance::UNATTRIBUTED;
            (source, machine)
        }
        "R6 store wider than its register" => {
            let (source, mut machine) = slice25_pair(StoreU64);
            let row = row_of(&machine, Op::MovMRSib);
            let at = value_operand(inst(&machine, row));
            let O::VReg(value) = inst(&machine, row).operands[at].clone() else {
                panic!("a virtual value register");
            };
            inst_mut(&mut machine, row).operands[at] = vreg_of(value.id, RegClass::Gpr32);
            (source, machine)
        }
        "S7 store disp plus 8" => {
            sib_edit(SlotIndexedStore, Op::MovMRSib, |_, _, _, disp| *disp += 8)
        }
        "S7 scale changed" => sib_edit(SlotIndexedStore, Op::MovMRSib, |_, _, scale, _| {
            *scale = if *scale == 8 { 4 } else { *scale * 2 }
        }),
        "S7 stored value a private address" | "S7 update over a stored private address" => {
            let (source, mut machine) = slice25_pair(SlotIndexedStore);
            let row = row_of(&machine, Op::MovMRSib);
            let slot = sib_slot(&machine, row);
            let frame = vreg(9_986);
            insert_at(
                &mut machine,
                row,
                X86ISelInst::new(
                    Op::Lea,
                    vec![
                        frame.clone(),
                        O::MemAddr {
                            base: Box::new(O::StackSlot(slot)),
                            disp: 0,
                        },
                    ],
                ),
            );
            if label == "S7 stored value a private address" {
                let at = value_operand(inst(&machine, row + 1));
                inst_mut(&mut machine, row + 1).operands[at] = frame;
            } else {
                insert_at(
                    &mut machine,
                    row + 1,
                    X86ISelInst::new(
                        Op::MovMR,
                        vec![
                            O::MemAddr {
                                base: Box::new(O::StackSlot(slot)),
                                disp: 0,
                            },
                            frame,
                        ],
                    ),
                );
            }
            (source, machine)
        }
        "S3 read over a stored private address" => {
            // The slot's own address stored into its first 8 bytes before
            // the indexed byte load: a candidate reads a private address.
            let (source, mut machine) = slice25_pair(SlotGuardedByte);
            let row = row_of(&machine, Op::MovzxRM8Sib);
            let slot = sib_slot(&machine, row);
            let frame = vreg(9_986);
            insert_at(
                &mut machine,
                row,
                X86ISelInst::new(
                    Op::Lea,
                    vec![
                        frame.clone(),
                        O::MemAddr {
                            base: Box::new(O::StackSlot(slot)),
                            disp: 0,
                        },
                    ],
                ),
            );
            insert_at(
                &mut machine,
                row + 1,
                X86ISelInst::new(
                    Op::MovMR,
                    vec![
                        O::MemAddr {
                            base: Box::new(O::StackSlot(slot)),
                            disp: 0,
                        },
                        frame,
                    ],
                ),
            );
            (source, machine)
        }
        "R2 carried index" | "R2 loop load at a zero index" => {
            // Slice 12's `LoadSum` with its per-iteration load `[t + 0]`
            // rewritten to `[t + z*1]`, `z` 0 from the entry; the carried
            // case also rewrites `z` (with 0 again) in the loop body.
            use super::slice12::{LoopShape, slice12_pair};
            let (source, mut machine) = slice12_pair(LoopShape::LoadSum);
            let load = row_of(&machine, Op::MovRM);
            let zero = vreg(9_989);
            let define = X86ISelInst::new(Op::MovRI, vec![zero.clone(), O::Imm(0)]);
            {
                let row = inst_mut(&mut machine, load);
                let O::MemAddr { base, disp: 0 } = row.operands[1].clone() else {
                    panic!("LoadSum's load is `[t + 0]`\n{}", describe(&machine));
                };
                row.opcode = Op::MovRMSib;
                row.operands[1] = O::SibMemAddr {
                    base,
                    index: Box::new(zero),
                    scale: 1,
                    disp: 0,
                };
            }
            if label == "R2 carried index" {
                insert_at(&mut machine, load + 1, define.clone());
            }
            insert_at(&mut machine, 0, define);
            (source, machine)
        }
        "S1 constant index 1 to 4" => {
            let (source, mut machine) = slice25_pair(SlotConstU64);
            change_live_slot_one_index(&mut machine, 4);
            (source, machine)
        }
        other => unreachable!("no control {other:?}"),
    }
}

/// A scaled-index load inserted before the first `opcode` row of `machine`
/// that reads `root`, its index `root` and its base that row's other
/// operand (a value).
fn sib_load_reading(machine: &mut X86ISelFunction, root: &O, opcode: X86Opcode) {
    let reader = rows_with(machine, &[opcode])
        .into_iter()
        .find(|row| inst(machine, *row).operands.contains(root))
        .unwrap_or_else(|| panic!("no {opcode:?} reads {root:?}\n{}", describe(machine)));
    let base = inst(machine, reader)
        .operands
        .iter()
        .find(|operand| *operand != root)
        .expect("a second operand")
        .clone();
    insert_at(
        machine,
        reader,
        X86ISelInst::new(
            X86Opcode::MovzxRM8Sib,
            vec![
                vreg(9_990),
                O::SibMemAddr {
                    base: Box::new(base),
                    index: Box::new(root.clone()),
                    scale: 1,
                    disp: 0,
                },
            ],
        ),
    );
}

// ---------------------------------------------------------------------------
// Controls (slice 25)
// ---------------------------------------------------------------------------

use super::super::quotient::mutant;

// ---- the solver-free gate

/// Every fixture is stated and its theorem holds on samples.
#[test]
fn owner_states_every_slice25_shape() {
    let failures: Vec<String> = SLICE_TWENTY_FIVE
        .into_iter()
        .filter_map(|shape| {
            let (source, machine) = slice25_pair(shape);
            holds25(&source, &machine)
                .err()
                .map(|why| format!("{shape:?}: {why}\n{}", describe(&machine)))
        })
        .collect();
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

/// `sib_bits` is the SDM effective address `base + index*scale +
/// sext(disp)` mod 2^64, its affine value exact where it is kept.
#[test]
fn sib_bits_is_the_sdm_effective_address() {
    let mut seed = 0x5125_u64;
    let mut next = || {
        seed ^= seed << 13;
        seed ^= seed >> 7;
        seed ^= seed << 17;
        seed
    };
    use crate::smt::{EvalEnv, EvalResult};
    for _ in 0..4_000 {
        let (b, i) = (next(), next());
        let disp = next() as i32;
        let mut env = EvalEnv::default();
        env.insert("b".into(), b);
        env.insert("i".into(), i);
        for scale in [1u8, 2, 4, 8] {
            let expected = b
                .wrapping_add(i.wrapping_mul(u64::from(scale)))
                .wrapping_add(i64::from(disp) as u64);
            let (expr, affine) = sib_bits(
                (E::var("b", 64), None),
                (E::var("i", 64), None),
                scale,
                disp,
            );
            assert_eq!(
                expr.eval(&env),
                EvalResult::Bv(expected),
                "{b:#x} + {i:#x}*{scale} + {disp}"
            );
            assert!(affine.is_none(), "no affine value of unknown operands");
            let (_, affine) = sib_bits(
                (E::var("b", 64), Some(Affine::constant(b, u64::MAX))),
                (E::var("i", 64), Some(Affine::constant(i, u64::MAX))),
                scale,
                disp,
            );
            assert_eq!(
                affine.and_then(Affine::as_constant),
                Some(expected),
                "the affine value of two constants"
            );
        }
    }
}

/// The private address of `[slot + I*s + d]` is O0's `lea [slot + d0];
/// LeaSib [. + I*s + d1]` for every split `d = d0 + d1`, at a term index
/// and a constant one.
#[test]
fn private_sib_matches_o0() {
    let index = E::var("i", 64);
    for scale in [1u8, 2, 4, 8] {
        for disp in [-24i32, -1, 0, 3, 16, 1 << 20] {
            let fused = sib_private(
                MachinePrivate::Frame(FrameAddr { slot: 2, offset: 0 }),
                SibIndex::Term(index.clone()),
                scale,
                disp,
            )
            .expect("in range");
            let constant = sib_private(
                MachinePrivate::Frame(FrameAddr { slot: 2, offset: 0 }),
                SibIndex::Constant(5),
                scale,
                disp,
            )
            .expect("in range");
            for d0 in [-8i32, 0, 5, disp] {
                let d1 = disp - d0;
                let lea = MachinePrivate::Frame(FrameAddr {
                    slot: 2,
                    offset: i64::from(d0),
                });
                let o0 = sib_private(lea.clone(), SibIndex::Term(index.clone()), scale, d1)
                    .expect("in range");
                let (MachinePrivate::Indexed(fused), MachinePrivate::Indexed(o0)) = (&fused, &o0)
                else {
                    panic!("a term index gives an indexed address");
                };
                assert_eq!((fused.slot, fused.base), (o0.slot, o0.base));
                assert_eq!(fused.term(), o0.term(), "scale {scale}, {d0} + {d1}");
                let o0 = sib_private(lea, SibIndex::Constant(5), scale, d1).expect("in range");
                let (MachinePrivate::Frame(constant), MachinePrivate::Frame(o0)) = (&constant, &o0)
                else {
                    panic!("a constant index gives a frame address");
                };
                assert_eq!(constant, o0, "scale {scale}, {d0} + {d1}");
            }
        }
    }
    // The offset overflows `i64`: no address.
    assert!(
        sib_private(
            MachinePrivate::Frame(FrameAddr { slot: 0, offset: 0 }),
            SibIndex::Constant((i64::MAX / 2) as u64),
            8,
            0,
        )
        .is_none()
    );
}

/// Each SIB fixture's row split into the rows slices 4 and 17 state (`lea
/// t, [slot]` for a slot base, then `LeaSib t, [base + index*scale + disp]`,
/// or the commuted `add t, index, base` at scale 1, then the access through
/// `[t + 0]`) states the same theorem text, and both hold; each RMW
/// fixture's row split into `mov t, [m]; op d, t, s; mov [m], d` holds too.
#[test]
fn decomposition_equivalence() {
    let pairs = SLICE_TWENTY_FIVE
        .into_iter()
        .map(|shape| {
            let (source, machine) = slice25_pair(shape);
            (
                format!("{shape:?}"),
                shape == Shape25::SlotCommuted,
                source,
                machine,
            )
        })
        .chain(QUALIFIED_EDITS.iter().map(|label| {
            let (source, machine) = case25(label);
            ((*label).to_owned(), false, source, machine)
        }));
    for (label, commuted, source, fused) in pairs {
        let decomposed = decompose(&fused, commuted);
        holds25(&source, &fused).unwrap_or_else(|why| panic!("{label} fused: {why}"));
        holds25(&source, &decomposed)
            .unwrap_or_else(|why| panic!("{label} decomposed: {why}\n{}", describe(&decomposed)));
        let is_rmw = rows_with(&fused, &SLICE25_ROWS)
            .into_iter()
            .any(|row| read_modify_write(inst(&fused, row).opcode).is_some());
        if !is_rmw {
            let fused_text = text(owner25(&source, &fused).expect("stated").obligation());
            let decomposed_text = text(owner25(&source, &decomposed).expect("stated").obligation());
            assert_eq!(fused_text, decomposed_text, "{label}: the fused row's text");
        }
    }
}

/// `machine` with every scaled-index access and read-modify-write row split
/// into the rows the earlier slices state ([`decomposition_equivalence`]),
/// each split row keeping the fused row's TV-1 stamp; `commuted`: a scale-1
/// row whose index holds the private address, split as `add t, index, base`
/// (which `LeaSib` never reads that way round).
pub(crate) fn decompose(machine: &X86ISelFunction, commuted: bool) -> X86ISelFunction {
    let mut machine = machine.clone();
    let mut fresh = 20_000u32;
    for block in machine.block_order.clone() {
        let Some(body) = machine.blocks.get_mut(&block) else {
            continue;
        };
        let mut split = Vec::with_capacity(body.insts.len());
        for inst in body.insts.drain(..) {
            if SLICE25_ROWS.contains(&inst.opcode) {
                split_row(&inst, commuted, &mut fresh, &mut split);
            } else {
                split.push(inst);
            }
        }
        body.insts = split;
    }
    machine
}

/// The rows the earlier slices state for one slice-25 row: `lea b, [slot]`
/// for a slot base, then `LeaSib t, [base + index*scale + disp]` and the
/// access through `[t + 0]`; a read-modify-write's `mov t, [m]; op d, t, s;
/// mov [m], d`.
fn split_row(inst: &X86ISelInst, commuted: bool, fresh: &mut u32, split: &mut Vec<X86ISelInst>) {
    use X86Opcode as Op;
    let mut fresh_vreg = || {
        *fresh += 1;
        vreg(*fresh)
    };
    let stamped = |opcode, operands| {
        let mut row = X86ISelInst::new(opcode, operands);
        row.lowering_provenance = inst.lowering_provenance;
        row
    };
    let mut address = |split: &mut Vec<X86ISelInst>, operand: &O| {
        let O::SibMemAddr {
            base,
            index,
            scale,
            disp,
        } = operand
        else {
            return operand.clone();
        };
        let base = match base.as_ref() {
            O::StackSlot(slot) => {
                let b = fresh_vreg();
                split.push(X86ISelInst::new(
                    Op::Lea,
                    vec![
                        b.clone(),
                        O::MemAddr {
                            base: Box::new(O::StackSlot(*slot)),
                            disp: 0,
                        },
                    ],
                ));
                b
            }
            other => other.clone(),
        };
        let t = fresh_vreg();
        if commuted && *scale == 1 {
            split.push(X86ISelInst::new(
                Op::AddRR,
                vec![t.clone(), (**index).clone(), base],
            ));
            return O::MemAddr {
                base: Box::new(t),
                disp: *disp,
            };
        }
        split.push(X86ISelInst::new(
            Op::LeaSib,
            vec![
                t.clone(),
                O::SibMemAddr {
                    base: Box::new(base),
                    index: index.clone(),
                    scale: *scale,
                    disp: *disp,
                },
            ],
        ));
        O::MemAddr {
            base: Box::new(t),
            disp: 0,
        }
    };
    match read_modify_write(inst.opcode) {
        Some((op, _)) => {
            let at = address(split, &inst.operands[0]);
            let (t, d) = (fresh_vreg(), fresh_vreg());
            split.push(stamped(Op::MovRM, vec![t.clone(), at.clone()]));
            let alu = if op == RmwOp::Add {
                Op::AddRR
            } else {
                Op::XorRR
            };
            split.push(X86ISelInst::new(
                alu,
                vec![d.clone(), t, inst.operands[1].clone()],
            ));
            split.push(stamped(Op::MovMR, vec![at, d]));
        }
        None => {
            let sibling = sib_sibling(inst.opcode).expect("a scaled-index access row");
            let at = usize::from(sib_access(inst.opcode).expect("an access").load);
            let mut operands = inst.operands.clone();
            operands[at] = address(split, &inst.operands[at]);
            split.push(stamped(sibling, operands));
        }
    }
}

/// Design §5.5: each must-refute edit is refuted.
#[test]
fn every_wrong_sib_or_rmw_row_is_refuted() {
    let failures: Vec<String> = REFUTED
        .iter()
        .filter_map(|label| {
            let (source, machine) = case25(label);
            refuted25(&source, &machine)
                .err()
                .map(|why| format!("{label}: {why}\n{}", describe(&machine)))
        })
        .collect();
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

/// An incoming access of the wrong width is unpaired: never credited.
#[test]
fn a_wrong_width_is_never_credited() {
    for label in NEVER_CREDITED {
        let (source, machine) = case25(label);
        never_credited25(&source, &machine).unwrap_or_else(|why| panic!("{label}: {why}"));
    }
}

/// Design §5.5's must-hold edits hold: each is stated and its theorem holds
/// on samples (S3 with its stamp removed or pointed at another instruction
/// included: the stamp only sizes S3's 16 candidates).
#[test]
fn neutral_edits_hold() {
    let failures: Vec<String> = NEUTRAL
        .iter()
        .chain(QUALIFIED_EDITS)
        .filter_map(|label| {
            let (source, machine) = case25(label);
            holds25(&source, &machine)
                .err()
                .map(|why| format!("{label}: {why}\n{}", describe(&machine)))
        })
        .collect();
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

/// Design §3: each must-refuse input is refused, with its text.
#[test]
fn out_of_domain_sib_and_rmw_rows_are_refused_by_name() {
    let failures: Vec<String> = REFUSALS
        .iter()
        .filter_map(|(label, needle)| {
            let (source, machine) = case25(label);
            refused25(&source, &machine, needle)
                .err()
                .map(|why| format!("{label}: {why}"))
        })
        .collect();
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

/// An undefined component is a mismatch (`UndefinedRead`), as through a
/// base-only address.
#[test]
fn an_undefined_component_is_a_mismatch() {
    for label in [
        "R1 undefined index",
        "R1 undefined base",
        "R2s undefined base",
    ] {
        let (source, machine) = case25(label);
        assert!(
            matches!(
                owner25(&source, &machine),
                Err(X86BodyRefusal::Mismatch(
                    X86BodyMismatch::UndefinedRead { .. }
                ))
            ),
            "{label}"
        );
    }
}

/// Design §2.4's verdict transitions, each with its fixture: a virtual
/// `MovRMSib v, [b + i*8 + 0]`, which slice 14's shape admitted and the
/// walk's dispatch arm refused whatever `b` held, is now judged by what `b`
/// holds: a value is a data load (`U64Scaled` holds), an undefined base a
/// named `UndefinedRead`, a frame register's address a private access that
/// holds, and a mixed root keeps a refusal with the mixed text.
#[test]
fn the_scale_eight_movrmsib_transitions_are_the_designs() {
    let (source, machine) = slice25_pair(Shape25::U64Scaled);
    holds25(&source, &machine).unwrap_or_else(|why| panic!("U64Scaled: {why}"));
    let mut seen = 0;
    for label in TRANSITIONS {
        let (source, machine) = case25(label);
        let result = owner25(&source, &machine);
        let ok = match *label {
            "R2s undefined base" => matches!(
                result,
                Err(X86BodyRefusal::Mismatch(
                    X86BodyMismatch::UndefinedRead { .. }
                ))
            ),
            "S1 base through a frame register at scale 8" => holds25(&source, &machine).is_ok(),
            "R2s mixed base" => matches!(
                &result,
                Err(refusal) if !matches!(refusal, X86BodyRefusal::Mismatch(_))
                    && refusal.to_string().contains(
                        "which the paths into its block leave holding different kinds of value"
                    )
            ),
            other => panic!("no expected verdict for transition {other}"),
        };
        assert!(ok, "{label}: {}", refusal_text25(&result));
        seen += 1;
    }
    assert_eq!(seen, 3);
}

/// A constant-index access outside its slot is a named mismatch
/// (`StackSlotBounds`), as at O0: S1 with its constant index 4, `a[4]` of a
/// `[u64; 4]`.
#[test]
fn a_constant_index_outside_its_slot_is_a_named_mismatch() {
    let (source, machine) = case25("S1 constant index 1 to 4");
    let result = owner25(&source, &machine);
    assert!(
        matches!(
            result,
            Err(X86BodyRefusal::Mismatch(
                X86BodyMismatch::StackSlotBounds { .. }
            ))
        ),
        "{}\n{}",
        refusal_text25(&result),
        describe(&machine)
    );
}

/// Design §2.4's transitions: a virtual `MovRMSib [b + i*8 + 0]`, the shape
/// slice 14's dispatch admitted, is now routed by what `b` holds: an
/// undefined base is `UndefinedRead`, a frame register's address a private
/// access that holds, a mixed root the mixed text (before slice 25 each was
/// refused at the dispatch arm, the fails-before record).
#[test]
fn a_scale_eight_movrmsib_is_routed_by_its_base() {
    let (source, machine) = case25("R2s undefined base");
    assert!(
        matches!(
            owner25(&source, &machine),
            Err(X86BodyRefusal::Mismatch(
                X86BodyMismatch::UndefinedRead { .. }
            ))
        ),
        "R2s undefined base"
    );
    let (source, machine) = case25("S1 base through a frame register at scale 8");
    let row = row_of(&machine, X86Opcode::MovRMSib);
    assert!(
        matches!(
            inst(&machine, row).operands[1],
            O::SibMemAddr {
                scale: 8,
                disp: 0,
                ..
            }
        ),
        "{}",
        describe(&machine)
    );
    holds25(&source, &machine).unwrap_or_else(|why| panic!("{why}\n{}", describe(&machine)));
    let (source, machine) = case25("R2s mixed base");
    refused25(
        &source,
        &machine,
        "which the paths into its block leave holding different kinds of value",
    )
    .unwrap();
}

/// An unbounded slot index is refused, and its theorem built without the
/// bound finder is refuted by an in-bounds claim.
#[test]
fn an_unbounded_slot_index_is_refused_and_its_claim_refutes_it() {
    let (source, machine) = case25("S3 unbounded index");
    let theorem = theorem_without_indexed_bounds(&source, &machine, SYSV)
        .unwrap_or_else(|refusal| panic!("{refusal}\n{}", describe(&machine)));
    assert!(dag_refuted_on_samples(&theorem));
}

/// Design §3: a scaled-index component the paths into its block leave
/// holding different kinds of value (slice 9's mixed root: a private
/// address on one arm, bits on the other), or one its loop carries paired
/// with no header parameter (slice 12), makes no claim, by the walk's own
/// texts, at the scaled-index row.
#[test]
fn a_mixed_or_carried_component_makes_no_claim() {
    // Mixed: the first diamond's `else` arm copies a frame address into the
    // join's value register (`a_root_of_different_kinds_at_a_join_makes_no_claim`),
    // read as a scaled-index index, and (a design §2.4 transition) as the
    // base of a scale-8 `MovRMSib`, which slice 14's shape admitted.
    for (label, opcode) in [
        ("R1 mixed index", "MovzxRM8Sib reads"),
        ("R2s mixed base", "MovRMSib reads"),
    ] {
        let (source, machine) = case25(label);
        let refusal = owner25(&source, &machine).err().expect("refused");
        let text = refusal.to_string();
        assert!(
            text.contains(opcode)
                && text.contains(
                    "which the paths into its block leave holding different kinds of value"
                ),
            "{label}: {text}\n{}",
            describe(&machine)
        );
    }
    // Carried: the per-iteration load of slice 12's `LoadSum` reads `[t +
    // z*1]`, where `z` is 0 from the entry and the loop body rewrites it
    // (with 0 again): the first round of the header fixpoint pairs the load
    // with the source's, and the next, which takes every register the loop
    // writes and no header parameter pairs as carried, reads `z` as one
    // (`a_register_the_loop_writes_is_never_assumed_unchanged`).
    let (source, machine) = case25("R2 carried index");
    let refusal = owner25(&source, &machine).err().expect("refused");
    let text = refusal.to_string();
    assert!(
        text.contains("MovRMSib reads v9989, which its loop carries paired with no loop-header"),
        "{text}\n{}",
        describe(&machine)
    );
    // The same machine without the loop's rewrite of `z` is stated: the
    // refusal is the carried component's.
    let (source, machine) = case25("R2 loop load at a zero index");
    holds25(&source, &machine).unwrap_or_else(|why| panic!("{why}\n{}", describe(&machine)));
}

/// Slice 25 composes with slice 24a's merged-chain quotient (OD-226): a
/// scaled-index row in a block `X86BlockMerge` made of a chain of LIR blocks
/// is checked over the quotient, and a refusal of the walk there names the
/// chains (`OverQuotient`, its own text first).
#[test]
fn scaled_index_rows_compose_with_the_merged_chain_quotient() {
    for shape in [
        Shape25::MergedScaled,
        Shape25::MergedBigU32Table,
        Shape25::MergedAddInto,
    ] {
        let (source, machine) = slice25_pair(shape);
        let owner = owner25(&source, &machine)
            .unwrap_or_else(|refusal| panic!("{shape:?}: {refusal}\n{}", describe(&machine)));
        assert!(
            owner.merged_chains().is_some(),
            "{shape:?} is not stated over a quotient\n{}",
            describe(&machine)
        );
        owner_holds(&owner).unwrap_or_else(|why| panic!("{shape:?}: {why}"));
    }
    // The indexed load's candidates are sized by its stamp, renumbered in
    // the quotient: without it the 1200-byte slot's 1197 offsets refuse.
    let (source, mut machine) = slice25_pair(Shape25::MergedBigU32Table);
    let row = row_of(&machine, X86Opcode::MovRM32Sib);
    inst_mut(&mut machine, row).lowering_provenance = LoweringProvenance::UNATTRIBUTED;
    let text = refusal_text25(&owner25(&source, &machine));
    assert!(
        text.contains("with 1197 candidate offsets (the lane admits 1 to 1024)")
            && text.contains("(over the merged-chain quotient: chains"),
        "{text}"
    );
    let (source, mut machine) = slice25_pair(Shape25::MergedScaled);
    let row = row_of(&machine, X86Opcode::MovRMSib);
    edit_sib(&mut machine, row, |base, _, _, _| *base = O::StackSlot(7));
    let text = owner25(&source, &machine)
        .err()
        .expect("an undeclared slot base is refused")
        .to_string();
    assert!(
        text.contains("names stack slot 7, which is not declared")
            && text.contains("(over the merged-chain quotient: chains"),
        "{text}"
    );
}

/// Slice 25 composes with the split route (OD-182): every fixture stated in
/// parts, cut at every program point at which its machine rows split
/// cleanly ([`super::slice16::every_point`]), holds, or is refused, or
/// fails exactly where its decomposition into the earlier slices' rows
/// fails too; never a named mismatch. A cut between the two source events a
/// read-modify-write row pairs (`AddInto` cut before its LIR `add`, and
/// before its `store`) is refused, never stated.
#[test]
fn scaled_index_and_rmw_rows_are_stated_in_parts() {
    use super::slice16::{every_point, in_parts};
    let mut stated = Vec::new();
    let mut not_holding = Vec::new();
    for shape in SLICE_TWENTY_FIVE {
        let (source, machine) = slice25_pair(shape);
        let points = every_point(&source, &machine);
        let result = in_parts(&source, &machine, points.clone());
        eprintln!(
            "S25_SPLIT shape={shape:?} points={points:?} parts={} result={}",
            result
                .as_ref()
                .map(|owner| owner.parts().len())
                .unwrap_or(0),
            refusal_text25(&result)
        );
        match &result {
            Ok(owner) => {
                assert!(owner.is_stated_in_parts(), "{shape:?}");
                match owner_holds(owner) {
                    Ok(()) => stated.push(shape),
                    // A part that does not hold is the split route's own
                    // verdict on the rows the earlier slices state, never
                    // slice 25's: the fixture's `lea; mov [t]` (or `mov;
                    // op; mov`) decomposition, cut at the same points, must
                    // fail the same way (and neither is credited).
                    Err(why) => {
                        let decomposed = decompose(&machine, shape == Shape25::SlotCommuted);
                        let split = in_parts(&source, &decomposed, points.clone());
                        let decomposed_why = match &split {
                            Ok(owner) => owner_holds(owner).err(),
                            Err(refusal) => Some(refusal.to_string()),
                        };
                        eprintln!(
                            "S25_SPLIT_DECOMPOSED shape={shape:?} fused={why} decomposed={decomposed_why:?}"
                        );
                        assert!(
                            decomposed_why.is_some()
                                && !matches!(split, Err(X86BodyRefusal::Mismatch(_))),
                            "{shape:?} in parts fails ({why}) but its decomposition holds"
                        );
                        not_holding.push(shape);
                    }
                }
            }
            Err(X86BodyRefusal::Mismatch(mismatch)) => {
                panic!("{shape:?} in parts: a correct body named {mismatch:?}")
            }
            Err(_) => {}
        }
    }
    eprintln!(
        "S25_SPLIT_SUMMARY stated={} not_holding={not_holding:?}",
        stated.len()
    );
    // OD-233: the slot fixtures' `imul` items of two constants are defined
    // cut inputs, so they hold. ByteMerge's refuted claim equates the
    // zero-extended byte with the merging load's undefined high bits, a
    // machine input that stays free (OD-233b, demanded bits).
    assert_eq!(
        not_holding,
        vec![Shape25::ByteMerge],
        "the fixtures stated in parts that do not hold"
    );
    for k in [1, 2] {
        let (source, machine) = slice25_pair(Shape25::AddInto);
        let result = in_parts(&source, &machine, vec![(source.entry_block, k)]);
        eprintln!("S25_SPLIT_RMW cut={k} result={}", refusal_text25(&result));
        // The fused row is one machine row for two source events: no cut
        // falls between them.
        assert!(
            matches!(&result, Err(refusal) if !matches!(refusal, X86BodyRefusal::Mismatch(_)))
                && refusal_text25(&result).contains(&format!(
                    "the machine rows of block Block(0) do not split cleanly before its \
                     instruction {k}"
                )),
            "AddInto cut before LIR instruction {k}: {}",
            refusal_text25(&result)
        );
    }
    assert!(!stated.is_empty(), "no slice-25 fixture is stated in parts");
}

/// The fused read-modify-write row carries no TV-1 stamp (the fusion copies
/// only the proof origin), and nothing reads one: a read-modify-write of
/// incoming memory pairs with the source's accesses by position, and one of
/// a private slot is refused by name, never stated through a guessed site.
#[test]
fn an_unstamped_read_modify_write_is_never_given_a_site() {
    use Shape25::*;
    for shape in [
        AddInto,
        AddIntoField,
        XorInto,
        AddIntoIndexed,
        XorIntoIndexed,
        MergedAddInto,
    ] {
        let (source, machine) = slice25_pair(shape);
        let fused = rows_with(
            &machine,
            &[
                X86Opcode::AddMR,
                X86Opcode::XorMR,
                X86Opcode::AddMRSib,
                X86Opcode::XorMRSib,
            ],
        );
        assert!(!fused.is_empty(), "{shape:?}");
        for row in fused {
            assert!(
                inst(&machine, row)
                    .lowering_provenance
                    .source_id()
                    .is_none(),
                "{shape:?} row {row} carries a stamp: {:?}",
                inst(&machine, row).lowering_provenance
            );
        }
        holds25(&source, &machine).unwrap_or_else(|why| panic!("{shape:?}: {why}"));
    }
    let (source, machine) = case25("M1 through a private address");
    refused25(&source, &machine, "read-modify-writes a private stack slot").unwrap();
}

/// Every slice-14 jump-table fixture's dispatch load still reads its table.
fn dispatch_control() -> Result<(), String> {
    for shape in [
        DefinedShape::JumpTable,
        DefinedShape::JumpTableShared,
        DefinedShape::JumpTableHoles,
        DefinedShape::JumpTableOffset,
    ] {
        let (source, machine) = slice14_pair(shape);
        holds25(&source, &machine).map_err(|why| format!("{shape:?}: {why}"))?;
    }
    Ok(())
}

#[test]
fn jump_table_loads_still_read_their_tables() {
    dispatch_control().unwrap();
}

/// No correct fixture at O1, O2 or O3 is named a mismatch: each is stated
/// and holds, or makes no claim.
#[test]
fn a_slice25_body_never_names_a_correct_machine_a_mismatch() {
    let mut stated = 0usize;
    for shape in SLICE_TWENTY_FIVE {
        let source = slice25_lir(shape);
        for level in [
            trust_cg_opt::OptLevel::O1,
            trust_cg_opt::OptLevel::O2,
            trust_cg_opt::OptLevel::O3,
        ] {
            // Only these two shapes require an opcode/fusion that no real
            // selector stream supplies. Constant-displacement forms still
            // retain every original, unmodified O1/O3 production control.
            if matches!(shape, Shape25::ByteMerge | Shape25::AddCarry)
                && level != trust_cg_opt::OptLevel::O2
            {
                continue;
            }
            let machine = if level == trust_cg_opt::OptLevel::O2 {
                slice25_pair(shape).1
            } else {
                optimized(&source, level)
            };
            match owner25(&source, &machine) {
                Ok(owner) => {
                    owner_holds(&owner).unwrap_or_else(|why| panic!("{shape:?} {level:?}: {why}"));
                    stated += 1;
                }
                Err(X86BodyRefusal::Mismatch(mismatch)) => {
                    panic!("{shape:?} {level:?}: a correct body named {mismatch:?}")
                }
                Err(_) => {}
            }
        }
    }
    assert!(stated >= SLICE_TWENTY_FIVE.len(), "{stated} stated");
}

// ---- mutants (design §5.6)

/// A control of the mutant campaign.
#[derive(Debug, Clone, Copy)]
enum Control25 {
    Holds(Shape25),
    Neutral(&'static str),
    Refused(&'static str),
    Refuted(&'static str),
    LeaSib,
    Dispatch,
    /// The control run with this mutant added to the active ones: a check
    /// behind another one is load-bearing only once the other is removed.
    Background(&'static str, &'static Control25),
}

fn run_control25(control: Control25) -> Result<(), String> {
    match control {
        Control25::Background(background, inner) => {
            let active = mutant::active();
            let names = if active.is_empty() {
                background.to_owned()
            } else {
                format!("{active},{background}")
            };
            let _background = mutant::set(&names);
            run_control25(*inner)
        }
        Control25::Holds(shape) => {
            let (source, machine) = slice25_pair(shape);
            holds25(&source, &machine)
        }
        Control25::Neutral(label) => {
            let (source, machine) = case25(label);
            holds25(&source, &machine)
        }
        Control25::Refused(label) => {
            let needle = REFUSALS
                .iter()
                .find(|(known, _)| *known == label)
                .map(|(_, needle)| *needle)
                .unwrap_or_else(|| panic!("no refusal {label}"));
            let (source, machine) = case25(label);
            refused25(&source, &machine, needle)
        }
        Control25::Refuted(label) => {
            let (source, machine) = case25(label);
            refuted25(&source, &machine)
        }
        Control25::LeaSib => {
            for ((what, got), (_, expected)) in lea_sib_texts().iter().zip(LEA_SIB_TEXTS) {
                if got != expected {
                    return Err(format!("{what}: {got}"));
                }
            }
            Ok(())
        }
        Control25::Dispatch => dispatch_control(),
    }
}

/// `control` under the mutants `names` on this thread; a panic is a failed
/// control.
fn under25(names: &str, control: Control25) -> Result<(), String> {
    let _mutant = mutant::set(names);
    std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| run_control25(control)))
        .unwrap_or_else(|payload| {
            let message = payload
                .downcast_ref::<String>()
                .cloned()
                .or_else(|| {
                    payload
                        .downcast_ref::<&str>()
                        .map(|text| (*text).to_owned())
                })
                .unwrap_or_else(|| "a panic with no message".into());
            Err(format!("panicked: {message}"))
        })
}

/// Design §5.6: each slice-25 rule mutant and the controls it must break.
const MUTANTS25: &[(&str, &[Control25])] = &[
    (
        "s25-commute-every-scale",
        &[Control25::Refused("S5 private index at scale 4")],
    ),
    ("s25-no-commute", &[Control25::Holds(Shape25::SlotCommuted)]),
    (
        "s25-disp-zero-extended",
        &[Control25::Neutral("R5' folded into the displacement")],
    ),
    ("s25-scale-ignored", &[Control25::Holds(Shape25::U32Scaled)]),
    (
        "s25-slot-base-at-disp",
        &[Control25::Neutral(
            "S4 constant index folded into the displacement",
        )],
    ),
    ("s25-every-movrmsib-to-memory", &[Control25::Dispatch]),
    // The scale check sits behind the block check (a table read outside its
    // dispatch block refuses at any scale), so it is load-bearing once the
    // block check is removed.
    (
        "s25-dispatch-no-scale-check",
        &[Control25::Background(
            "s25-dispatch-any-block",
            &Control25::Refused("dispatch at scale 4 disp 16"),
        )],
    ),
    (
        "s25-dispatch-any-block",
        &[Control25::Refused(
            "dispatch at scale 8 disp 0 in a target block",
        )],
    ),
    (
        "s25-routing-operand-only",
        &[
            Control25::Refused("R2 physical destination and its reader"),
            Control25::Refused("R2 physical destination"),
        ],
    ),
    (
        "s25-rmw-flags-not-clobbered",
        &[Control25::Refused("M2 compare, xor, setcc")],
    ),
    (
        "s25-xor-stated-as-add",
        &[
            Control25::Holds(Shape25::XorInto),
            Control25::Refuted("M1 add to xor"),
        ],
    ),
    ("s25-rmw-store-only", &[Control25::Holds(Shape25::AddInto)]),
    (
        "s25-rmw-store-via-frame-of",
        &[Control25::Refused("M1 source a private address")],
    ),
    (
        "s25-scan-exempts-index",
        &[Control25::Refused("S3 slot as index")],
    ),
    (
        "s25-no-declared-slot-check",
        &[Control25::Refused("S3 undeclared slot base")],
    ),
    (
        "s25-indexed-stamp-wrong-row",
        &[Control25::Holds(Shape25::SlotBigU32Table)],
    ),
    ("s25-lea-sib-commutes", &[Control25::LeaSib]),
];

/// Every control passes without a mutant, and each mutant makes one of its
/// controls fail.
#[test]
fn every_slice25_mutant_fails_a_control() {
    let mut survived = Vec::new();
    for (names, controls) in MUTANTS25 {
        for control in *controls {
            under25("", *control)
                .unwrap_or_else(|why| panic!("control {control:?} fails unmutated: {why}"));
        }
        let killed = controls
            .iter()
            .any(|control| match under25(names, *control) {
                Ok(()) => false,
                Err(why) => {
                    eprintln!("S25_MUTANT mutant={names} control={control:?} failed: {why}");
                    true
                }
            });
        if !killed {
            survived.push(format!("{names} survived {controls:?}"));
        }
    }
    assert!(survived.is_empty(), "{}", survived.join("\n"));
}

/// The neutral mutant: the scaled-index effective address left unnamed
/// changes no verdict, and the switch is wired: the theorem text of an
/// incoming scaled-index load and of a scaled-index read-modify-write
/// changes under it (the address is spelled inline, not named).
#[test]
fn the_unnamed_ea_mutant_is_neutral() {
    let named = |shape: Shape25| {
        let (source, machine) = slice25_pair(shape);
        let owner = owner25(&source, &machine).unwrap_or_else(|refusal| panic!("{refusal}"));
        text(owner.obligation())
    };
    let wired = [Shape25::U64Scaled, Shape25::AddIntoIndexed];
    let before: Vec<String> = wired.into_iter().map(named).collect();
    let _mutant = mutant::set("s25-unnamed-ea");
    for (shape, before) in wired.into_iter().zip(before) {
        assert_ne!(
            named(shape),
            before,
            "{shape:?}: s25-unnamed-ea changes nothing"
        );
    }
    for shape in SLICE_TWENTY_FIVE {
        let (source, machine) = slice25_pair(shape);
        holds25(&source, &machine).unwrap_or_else(|why| panic!("{shape:?}: {why}"));
    }
}

// ---- the golden text

/// The golden text of every slice-25 fixture's theorem.
pub(crate) fn slice_twenty_five_snapshots() -> String {
    let mut rendered = String::new();
    for shape in SLICE_TWENTY_FIVE {
        let (source, machine) = slice25_pair(shape);
        let owner =
            owner25(&source, &machine).unwrap_or_else(|refusal| panic!("{shape:?}: {refusal}"));
        rendered.push_str(&format!(";;;; {shape:?}\n{}\n", text(owner.obligation())));
    }
    for label in QUALIFIED_EDITS {
        let (source, machine) = case25(label);
        let owner =
            owner25(&source, &machine).unwrap_or_else(|refusal| panic!("{label}: {refusal}"));
        rendered.push_str(&format!(
            ";;;; edit {label}\n{}\n",
            text(owner.obligation())
        ));
    }
    rendered
}

/// The reviewed digest of the slice-25 golden text.
const SLICE_TWENTY_FIVE_SNAPSHOT_SHA256: &str =
    "c23b51fe0fcda9bd136225065ae671c27cbd720e8afcf4366f8201629a6403ef";

/// The rendered theorems of every slice-25 fixture are the reviewed golden
/// text, pinned by digest.
#[test]
fn slice_twenty_five_smt2_is_canonical_per_shape() {
    use sha2::{Digest, Sha256};
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/x86_source_bound_body/slice25_snapshots.smt2");
    let rendered = slice_twenty_five_snapshots();
    let digest = format!("{:x}", Sha256::digest(rendered.as_bytes()));
    if std::env::var_os("TCG_X86_BODY_SNAPSHOT_WRITE").is_some() {
        std::fs::write(&path, &rendered).unwrap();
        panic!(
            "rewrote {}; review its diff, set SLICE_TWENTY_FIVE_SNAPSHOT_SHA256 to {digest} and \
             re-run without TCG_X86_BODY_SNAPSHOT_WRITE",
            path.display()
        );
    }
    let golden = std::fs::read_to_string(&path).unwrap_or_default();
    assert_eq!(rendered, golden, "slice25_snapshots.smt2 drifted");
    assert_eq!(digest, SLICE_TWENTY_FIVE_SNAPSHOT_SHA256);
}
