// Copyright 2026 Andrew Yates | Apache-2.0
//! AArch64 Mach-O native control for the borrow / binding-frame / `Undef`
//! legalization stage (ledger L05-P9, `trust_cg_lower::borrow_frame_undef`).
//!
//! The corpus below spells every construct the stage lowers through the
//! `trust_ir_build` builder: shared and unique borrows of a stack cell and of
//! mutable and read-only global cells with reads and writes through the
//! borrow, unique-of-unique, shared-of-unique and shared-of-shared reborrows,
//! unique and shared borrows (and a shared reborrow) of FAT slice pointers to
//! a stack array and to a read-only global array, written and read through
//! their data lane with their length read from the metadata lane, binding
//! frames that store and load mixed-width slots (`U8`, `U16`, `U32`, `U64`,
//! `I64`, `I128`, `Bool`, `F32`, `F64`, `Ptr`) across blocks, two frames live
//! at once, a loop-carried frame, and `Undef`. `U64` poison is transported
//! through a plain store, a copy, a select arm, a frame slot that is rebound
//! before it is read and a block argument (`bf_undef_transport`); poison of
//! nine carriers (`Bool`, `I8`, `U16`, `I32`, `U64`, `I128`, `F32`, `F64`,
//! `Ptr`) is copied and stored plainly, never reloaded (`bf_undef_carriers`).
//! No admitted program can observe the materialized zero natively (poison is
//! only ever transported), so the zero constant of every carrier is pinned at
//! LIR level by the conformance-manifest row `Inst::Undef zero pattern of
//! every scalar carrier`, not here. Every function is compiled at O0-O3,
//! linked against a C driver and run on several inputs; the trust-ir
//! reference interpreter replays every `(function, input)` pair and the
//! native value must equal it. The interpreter is itself pinned to closed
//! forms.
//!
//! `Undef` consumed by arithmetic is NOT a positive case: the pinned trust-ir
//! makes inspecting poison undefined behaviour (ub-numerics-policy §4; the
//! interpreter faults at the arithmetic), so a masked arithmetic use has no
//! defined result to agree with. It is a named refusal below, together with
//! an undef branch condition, guard, divisor, return and volatile store, a
//! FreshSymbolicHavoc marker, an aggregate undef, a shared-to-unique
//! reborrow, a borrow of a non-pointer and of null, a superseded frame handle
//! read after a rebind in the same block and in a successor block, an
//! escaping frame handle, a frame handle reaching an entry-block parameter,
//! an aggregate slot, an inspected unbound slot and a slot bound on one path
//! only; for each poison refusal the interpreter's own verdict (undefined
//! behaviour) is checked too.
//!
//! Execution evidence on aarch64-apple-darwin only (Mach-O objects linked by
//! the host `cc`); the refusal, receipt and strict-entry rows run on any host.
//! No ELF/Linux twin exists. Test evidence, not proof.

#[path = "common/rosetta.rs"]
mod process;

#[path = "common/admission_expect.rs"]
mod admission_expect;

use std::fs;
use std::process::Command;
use std::time::{SystemTime, UNIX_EPOCH};

use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::target::TargetSpec;
use trust_cg_codegen::{Compiler, CompilerConfig};
use trust_cg_lower::borrow_frame_undef::BorrowKind;
use trust_ir::inst::{BindingFrameDef, BindingSlot};
use trust_ir::interpret::{InterpretErrorCode, InterpretValue, Interpreter};
use trust_ir::value::{BindingFrameId, GlobalId};
use trust_ir::{
    BinOp, CastOp, Constant, Endianness, FatPtrKind, Global, ICmpOp, Linkage, Module,
    ProofAnnotation, StructPassingPolicy, TargetInfo, Ty, ValueId,
};
use trust_ir_build::{FunctionBuilder, ModuleBuilder, validate_module};

const TRIPLE: &str = "aarch64-apple-darwin";
const LEVELS: [OptLevel; 4] = [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3];

/// Inputs every function runs on, natively and in the interpreter.
const INPUTS: [u64; 10] = [
    0,
    1,
    7,
    9,
    41,
    1000,
    1001,
    0xFFFF_FFFF,
    0x1234_5678_9ABC_DEF0,
    u64::MAX,
];

/// The corpus functions (`fn(u64) -> u64` each), in driver order.
const FUNCTIONS: [&str; 10] = [
    "bf_stack_borrow",
    "bf_reborrow",
    "bf_global_rw",
    "bf_global_table",
    "bf_fat_borrow",
    "bf_frame_mixed",
    "bf_frame_loop",
    "bf_frame_nested",
    "bf_undef_transport",
    "bf_undef_carriers",
];

const G_CELL: u32 = 0;
const G_TABLE: u32 = 1;
const TABLE: [u64; 4] = [10, 20, 30, 40];

fn target() -> TargetInfo {
    TargetInfo {
        triple: TRIPLE.into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: Some("aapcs64".into()),
        struct_passing: StructPassingPolicy::NativeC,
    }
}

fn global(name: &str, ty: Ty, mutable: bool, initializer: Constant) -> Global {
    Global {
        section: None,
        visibility: trust_ir::Visibility::Default,
        retained: false,
        name: name.into(),
        ty,
        mutable,
        initializer: Some(initializer),
        linkage: Linkage::External,
        tls: None,
        align: None,
    }
}

fn frame_def(id: u32, slots: &[(&str, Ty)]) -> BindingFrameDef {
    BindingFrameDef::new(
        BindingFrameId::new(id),
        format!("frame{id}"),
        slots
            .iter()
            .map(|(name, ty)| BindingSlot::new(*name, ty.clone()))
            .collect(),
    )
}

fn u64c(f: &mut FunctionBuilder<'_>, value: u64) -> ValueId {
    f.uconst(Ty::U64, u128::from(value))
}

/// The closed form each corpus function must compute.
fn oracle(name: &str, x: u64) -> u64 {
    match name {
        "bf_stack_borrow" => x.wrapping_mul(3).wrapping_add(1),
        "bf_reborrow" => x.wrapping_add(5).wrapping_mul(2),
        "bf_global_rw" => x ^ 0x55,
        "bf_global_table" => TABLE[(x & 3) as usize].wrapping_add(x),
        "bf_fat_borrow" => x.wrapping_add(4).wrapping_add(TABLE[(x & 3) as usize]),
        "bf_frame_mixed" => {
            let wide = u128::from(x) * 2;
            let mut sum = x & 0xff;
            sum = sum.wrapping_add(x);
            sum = sum.wrapping_add((x >> 7) & 0xffff_ffff);
            sum = sum.wrapping_add(if x > 1000 { 1000 } else { 0 });
            sum = sum.wrapping_add((x >> 3) & 0xffff);
            sum = sum
                .wrapping_add(wide as u64)
                .wrapping_add((wide >> 64) as u64);
            sum = sum.wrapping_add(x & 0xffff);
            sum.wrapping_add(x ^ 0xABCD)
        }
        "bf_frame_loop" => (0..(x & 31)).map(|i| i * i).sum(),
        "bf_frame_nested" => {
            let signed = i64::from(x as u32 as i32);
            let unsigned = i64::from(x as u32);
            (signed + unsigned + (x & 0xff) as i64) as u64
        }
        "bf_undef_transport" => x.wrapping_mul(3).wrapping_add(1),
        "bf_undef_carriers" => x,
        other => panic!("no oracle for {other}"),
    }
}

/// The positive corpus.
fn corpus() -> Module {
    let mut m = ModuleBuilder::new_with_target_info("borrows_frames", target());
    let u64_ty = m.add_type(Ty::U64);
    m.add_global(global("bf_cell", Ty::U64, true, Constant::Int(7)));
    m.add_global(global(
        "bf_table",
        Ty::Array(u64_ty, 4),
        false,
        Constant::Array(
            TABLE
                .iter()
                .map(|v| Constant::Int(i128::from(*v)))
                .collect(),
        ),
    ));
    let unary = m.add_func_type(vec![Ty::U64], vec![Ty::U64]);

    // bf_stack_borrow(x) = 3x + 1: written and read back through borrows of
    // one stack cell.
    {
        let mut f = m.function("bf_stack_borrow", unary);
        let entry = f.create_block();
        let x = f.add_block_param(entry, Ty::U64);
        f.switch_to_block(entry);
        let cell = f.alloca(Ty::U64);
        f.store(Ty::U64, cell, x);
        let unique = f.borrow_mut(cell);
        let v = f.load(Ty::U64, unique);
        let three = u64c(&mut f, 3);
        let one = u64c(&mut f, 1);
        let tripled = f.binop(BinOp::Mul, Ty::U64, v, three);
        let next = f.binop(BinOp::Add, Ty::U64, tripled, one);
        f.store(Ty::U64, unique, next);
        f.end_borrow(unique);
        let shared = f.borrow(cell);
        let read = f.load(Ty::U64, shared);
        f.end_borrow(shared);
        f.ret(vec![read]);
        f.build();
    }

    // bf_reborrow(x) = 2(x + 5): a unique reborrow writes, a shared reborrow
    // of the unique borrow and a shared reborrow of that read back.
    {
        let mut f = m.function("bf_reborrow", unary);
        let entry = f.create_block();
        let x = f.add_block_param(entry, Ty::U64);
        f.switch_to_block(entry);
        let cell = f.alloca(Ty::U64);
        f.store(Ty::U64, cell, x);
        let unique = f.borrow_mut(cell);
        let reunique = f.borrow_mut(unique);
        let v = f.load(Ty::U64, reunique);
        let five = u64c(&mut f, 5);
        let bumped = f.binop(BinOp::Add, Ty::U64, v, five);
        f.store(Ty::U64, reunique, bumped);
        f.end_borrow(reunique);
        let shared = f.borrow(unique);
        let reshared = f.borrow(shared);
        let read = f.load(Ty::U64, reshared);
        f.end_borrow(reshared);
        f.end_borrow(shared);
        f.end_borrow(unique);
        let direct = f.load(Ty::U64, cell);
        let sum = f.binop(BinOp::Add, Ty::U64, read, direct);
        f.ret(vec![sum]);
        f.build();
    }

    // bf_global_rw(x) = x ^ 0x55: stored into a mutable global through a
    // unique borrow of its address, read back through a shared one.
    {
        let mut f = m.function("bf_global_rw", unary);
        let entry = f.create_block();
        let x = f.add_block_param(entry, Ty::U64);
        f.switch_to_block(entry);
        let address = f.global_addr(GlobalId::new(G_CELL));
        let unique = f.borrow_mut(address);
        let mask = u64c(&mut f, 0x55);
        let value = f.binop(BinOp::Xor, Ty::U64, x, mask);
        f.store(Ty::U64, unique, value);
        f.end_borrow(unique);
        let shared = f.borrow(address);
        let read = f.load(Ty::U64, shared);
        f.end_borrow(shared);
        f.ret(vec![read]);
        f.build();
    }

    // bf_global_table(x) = TABLE[x & 3] + x: indexed through a shared borrow
    // of a read-only global array.
    {
        let mut f = m.function("bf_global_table", unary);
        let entry = f.create_block();
        let x = f.add_block_param(entry, Ty::U64);
        f.switch_to_block(entry);
        let address = f.global_addr(GlobalId::new(G_TABLE));
        let shared = f.borrow(address);
        let three = u64c(&mut f, 3);
        let index = f.binop(BinOp::And, Ty::U64, x, three);
        let element = f.gep(Ty::U64, shared, vec![index]);
        let value = f.load(Ty::U64, element);
        f.end_borrow(shared);
        let sum = f.binop(BinOp::Add, Ty::U64, value, x);
        f.ret(vec![sum]);
        f.build();
    }

    // bf_fat_borrow(x) = x + 4 + TABLE[x & 3]: a fat slice pointer to a
    // four-element stack array is written through a unique borrow's data
    // lane and read back through a shared reborrow chain, whose metadata
    // lane supplies the length; a shared borrow of a fat slice pointer to
    // the read-only global table is indexed the same way.
    {
        let mut f = m.function("bf_fat_borrow", unary);
        let entry = f.create_block();
        let x = f.add_block_param(entry, Ty::U64);
        f.switch_to_block(entry);
        let slice = Ty::FatPtr(FatPtrKind::Slice(u64_ty));
        let cells = f.alloca(Ty::Array(u64_ty, 4));
        let four = u64c(&mut f, 4);
        let fat = f.ptr_from_parts(slice.clone(), Ty::U64, cells, four);
        let three = u64c(&mut f, 3);
        let index = f.binop(BinOp::And, Ty::U64, x, three);
        let unique = f.borrow_mut(fat);
        let data = f.ptr_data(slice.clone(), unique);
        let element = f.gep(Ty::U64, data, vec![index]);
        f.store(Ty::U64, element, x);
        f.end_borrow(unique);
        let shared = f.borrow(fat);
        let reshared = f.borrow(shared);
        let data = f.ptr_data(slice.clone(), reshared);
        let length = f.ptr_metadata(slice.clone(), Ty::U64, reshared);
        let element = f.gep(Ty::U64, data, vec![index]);
        let value = f.load(Ty::U64, element);
        f.end_borrow(reshared);
        f.end_borrow(shared);
        let table = f.global_addr(GlobalId::new(G_TABLE));
        let table_fat = f.ptr_from_parts(slice.clone(), Ty::U64, table, four);
        let table_shared = f.borrow(table_fat);
        let table_data = f.ptr_data(slice, table_shared);
        let table_element = f.gep(Ty::U64, table_data, vec![index]);
        let table_value = f.load(Ty::U64, table_element);
        f.end_borrow(table_shared);
        let sum = f.binop(BinOp::Add, Ty::U64, value, length);
        let sum = f.binop(BinOp::Add, Ty::U64, sum, table_value);
        f.ret(vec![sum]);
        f.build();
    }

    // bf_frame_mixed: eight slots of mixed width bound in the entry block
    // and read in the next one through a block-parameter handle.
    {
        let mut f = m.function("bf_frame_mixed", unary);
        let entry = f.create_block();
        let next = f.create_block();
        let x = f.add_block_param(entry, Ty::U64);
        let handle = f.add_block_param(next, Ty::Ptr);
        f.switch_to_block(entry);
        let cell = f.alloca(Ty::U64);
        let mask = u64c(&mut f, 0xABCD);
        let masked = f.binop(BinOp::Xor, Ty::U64, x, mask);
        f.store(Ty::U64, cell, masked);
        let f0 = f.open_frame(frame_def(
            0,
            &[
                ("a", Ty::U8),
                ("b", Ty::U64),
                ("c", Ty::U32),
                ("d", Ty::Bool),
                ("e", Ty::U16),
                ("w", Ty::I128),
                ("g", Ty::F64),
                ("h", Ty::Ptr),
            ],
        ));
        let a = f.trunc(Ty::U64, Ty::U8, x);
        let f1 = f.bind_slot(f0, 0, a);
        let f2 = f.bind_slot(f1, 1, x);
        let seven = u64c(&mut f, 7);
        let shifted = f.binop(BinOp::LShr, Ty::U64, x, seven);
        let c = f.trunc(Ty::U64, Ty::U32, shifted);
        let f3 = f.bind_slot(f2, 2, c);
        let thousand = u64c(&mut f, 1000);
        let d = f.icmp(ICmpOp::Ugt, Ty::U64, x, thousand);
        let f4 = f.bind_slot(f3, 3, d);
        let three = u64c(&mut f, 3);
        let shifted = f.binop(BinOp::LShr, Ty::U64, x, three);
        let e = f.trunc(Ty::U64, Ty::U16, shifted);
        let f5 = f.bind_slot(f4, 4, e);
        let wide = f.zext(Ty::U64, Ty::I128, x);
        let doubled = f.binop(BinOp::Add, Ty::I128, wide, wide);
        let f6 = f.bind_slot(f5, 5, doubled);
        let low_mask = u64c(&mut f, 0xffff);
        let low = f.binop(BinOp::And, Ty::U64, x, low_mask);
        let g = f.cast(CastOp::UIToFP, Ty::U64, Ty::F64, low);
        let f7 = f.bind_slot(f6, 6, g);
        let f8 = f.bind_slot(f7, 7, cell);
        f.br(next, vec![f8]);

        f.switch_to_block(next);
        let a = f.load_slot(handle, 0, Ty::U8);
        let a = f.zext(Ty::U8, Ty::U64, a);
        let b = f.load_slot(handle, 1, Ty::U64);
        let c = f.load_slot(handle, 2, Ty::U32);
        let c = f.zext(Ty::U32, Ty::U64, c);
        let d = f.load_slot(handle, 3, Ty::Bool);
        let thousand = u64c(&mut f, 1000);
        let zero = u64c(&mut f, 0);
        let d = f.select(Ty::U64, d, thousand, zero);
        let e = f.load_slot(handle, 4, Ty::U16);
        let e = f.zext(Ty::U16, Ty::U64, e);
        let w = f.load_slot(handle, 5, Ty::I128);
        let sixty_four = f.iconst(Ty::I128, 64);
        let high = f.binop(BinOp::LShr, Ty::I128, w, sixty_four);
        let high = f.trunc(Ty::I128, Ty::U64, high);
        let low = f.trunc(Ty::I128, Ty::U64, w);
        let g = f.load_slot(handle, 6, Ty::F64);
        let g = f.cast(CastOp::FPToUI, Ty::F64, Ty::U64, g);
        let h = f.load_slot(handle, 7, Ty::Ptr);
        let pointee = f.load(Ty::U64, h);
        f.close_frame(handle);
        let mut sum = f.binop(BinOp::Add, Ty::U64, a, b);
        for term in [c, d, e, low, high, g, pointee] {
            sum = f.binop(BinOp::Add, Ty::U64, sum, term);
        }
        f.ret(vec![sum]);
        f.build();
    }

    // bf_frame_loop(x) = sum of i*i for i < (x & 31): the quantifier shape,
    // a loop-carried frame rebound twice per iteration.
    {
        let mut f = m.function("bf_frame_loop", unary);
        let entry = f.create_block();
        let header = f.create_block();
        let body = f.create_block();
        let exit = f.create_block();
        let x = f.add_block_param(entry, Ty::U64);
        let handle = f.add_block_param(header, Ty::Ptr);
        f.switch_to_block(entry);
        let bound_mask = u64c(&mut f, 31);
        let n = f.binop(BinOp::And, Ty::U64, x, bound_mask);
        let f0 = f.open_frame(frame_def(0, &[("i", Ty::U64), ("acc", Ty::U64)]));
        let zero = u64c(&mut f, 0);
        let f1 = f.bind_slot(f0, 0, zero);
        let f2 = f.bind_slot(f1, 1, zero);
        f.br(header, vec![f2]);

        f.switch_to_block(header);
        let i = f.load_slot(handle, 0, Ty::U64);
        let more = f.icmp(ICmpOp::Ult, Ty::U64, i, n);
        f.condbr(more, body, vec![], exit, vec![]);

        f.switch_to_block(body);
        let acc = f.load_slot(handle, 1, Ty::U64);
        let square = f.binop(BinOp::Mul, Ty::U64, i, i);
        let acc = f.binop(BinOp::Add, Ty::U64, acc, square);
        let one = u64c(&mut f, 1);
        let i_next = f.binop(BinOp::Add, Ty::U64, i, one);
        let fa = f.bind_slot(handle, 1, acc);
        let fb = f.bind_slot(fa, 0, i_next);
        f.br(header, vec![fb]);

        f.switch_to_block(exit);
        let result = f.load_slot(handle, 1, Ty::U64);
        f.close_frame(handle);
        f.ret(vec![result]);
        f.build();
    }

    // bf_frame_nested: two frames live at once (an I64 and an F32 slot in the
    // inner one, a U32 slot in the outer one), closed innermost first.
    {
        let mut f = m.function("bf_frame_nested", unary);
        let entry = f.create_block();
        let x = f.add_block_param(entry, Ty::U64);
        f.switch_to_block(entry);
        let outer = f.open_frame(frame_def(0, &[("u", Ty::U32)]));
        let narrow = f.trunc(Ty::U64, Ty::U32, x);
        let outer = f.bind_slot(outer, 0, narrow);
        let inner = f.open_frame(frame_def(1, &[("v", Ty::I64), ("w", Ty::F32)]));
        let signed = f.trunc(Ty::U64, Ty::I32, x);
        let signed = f.sext(Ty::I32, Ty::I64, signed);
        let inner = f.bind_slot(inner, 0, signed);
        let byte_mask = u64c(&mut f, 0xff);
        let byte = f.binop(BinOp::And, Ty::U64, x, byte_mask);
        let float = f.cast(CastOp::UIToFP, Ty::U64, Ty::F32, byte);
        let inner = f.bind_slot(inner, 1, float);
        let v = f.load_slot(inner, 0, Ty::I64);
        let w = f.load_slot(inner, 1, Ty::F32);
        let w = f.cast(CastOp::FPToSI, Ty::F32, Ty::I64, w);
        f.close_frame(inner);
        let u = f.load_slot(outer, 0, Ty::U32);
        let u = f.zext(Ty::U32, Ty::I64, u);
        f.close_frame(outer);
        let sum = f.binop(BinOp::Add, Ty::I64, v, u);
        let sum = f.binop(BinOp::Add, Ty::I64, sum, w);
        let sum = f.cast(CastOp::Bitcast, Ty::I64, Ty::U64, sum);
        f.ret(vec![sum]);
        f.build();
    }

    // bf_undef_transport(x) = 3x + 1: an undef is stored plainly (then
    // overwritten), copied, selected as an arm and stored, bound into a frame
    // slot that is rebound before the read, and passed as a block argument
    // that is only stored. No path inspects it.
    {
        let mut f = m.function("bf_undef_transport", unary);
        let entry = f.create_block();
        let next = f.create_block();
        let x = f.add_block_param(entry, Ty::U64);
        let carried = f.add_block_param(next, Ty::U64);
        let handle = f.add_block_param(next, Ty::Ptr);
        f.switch_to_block(entry);
        let poison = f.undef(Ty::U64);
        let cell = f.alloca(Ty::U64);
        f.store(Ty::U64, cell, poison);
        let one = u64c(&mut f, 1);
        let x1 = f.binop(BinOp::Add, Ty::U64, x, one);
        f.store(Ty::U64, cell, x1);
        let copied = f.copy(Ty::U64, poison);
        let ten = u64c(&mut f, 10);
        let small = f.icmp(ICmpOp::Ult, Ty::U64, x, ten);
        let selected = f.select(Ty::U64, small, copied, x);
        let scratch = f.alloca(Ty::U64);
        f.store(Ty::U64, scratch, selected);
        let f0 = f.open_frame(frame_def(0, &[("s", Ty::U64)]));
        let f1 = f.bind_slot(f0, 0, poison);
        let two = u64c(&mut f, 2);
        let x2 = f.binop(BinOp::Mul, Ty::U64, x, two);
        let f2 = f.bind_slot(f1, 0, x2);
        f.br(next, vec![poison, f2]);

        f.switch_to_block(next);
        f.store(Ty::U64, scratch, carried);
        let v = f.load_slot(handle, 0, Ty::U64);
        f.close_frame(handle);
        let w = f.load(Ty::U64, cell);
        let sum = f.binop(BinOp::Add, Ty::U64, v, w);
        f.ret(vec![sum]);
        f.build();
    }

    // bf_undef_carriers(x) = x: an undef of nine scalar carriers the NoUndef
    // model materializes, each copied and stored plainly, never reloaded.
    {
        let mut f = m.function("bf_undef_carriers", unary);
        let entry = f.create_block();
        let x = f.add_block_param(entry, Ty::U64);
        f.switch_to_block(entry);
        for ty in [
            Ty::Bool,
            Ty::I8,
            Ty::U16,
            Ty::I32,
            Ty::U64,
            Ty::I128,
            Ty::F32,
            Ty::F64,
            Ty::Ptr,
        ] {
            let poison = f.undef(ty.clone());
            let copied = f.copy(ty.clone(), poison);
            let cell = f.alloca(ty.clone());
            f.store(ty, cell, copied);
        }
        f.ret(vec![x]);
        f.build();
    }

    m.build().expect("ModuleBuilder::build: test fixture")
}

/// A one-function module `refused(x: u64) -> u64` whose body `body` builds.
fn fixture(body: impl FnOnce(&mut FunctionBuilder<'_>, ValueId)) -> Module {
    let mut m = ModuleBuilder::new_with_target_info("borrows_frames_refused", target());
    let unary = m.add_func_type(vec![Ty::U64], vec![Ty::U64]);
    let mut f = m.function("refused", unary);
    let entry = f.create_block();
    let x = f.add_block_param(entry, Ty::U64);
    f.switch_to_block(entry);
    body(&mut f, x);
    f.build();
    m.build().expect("ModuleBuilder::build: test fixture")
}

/// `refused(x: u64, h: ptr) -> u64` whose entry block is also the target of
/// a back edge carrying a frame handle into `h`: on entry `h` is the
/// caller's pointer, which no `OpenFrame` produced.
fn entry_parameter_frame_fixture() -> Module {
    let mut m = ModuleBuilder::new_with_target_info("borrows_frames_refused", target());
    let binary = m.add_func_type(vec![Ty::U64, Ty::Ptr], vec![Ty::U64]);
    let mut f = m.function("refused", binary);
    let entry = f.create_block();
    let exit = f.create_block();
    let x = f.add_block_param(entry, Ty::U64);
    let handle = f.add_block_param(entry, Ty::Ptr);
    f.switch_to_block(entry);
    let read = f.load_slot(handle, 0, Ty::U64);
    let f0 = f.open_frame(frame_def(0, &[("s", Ty::U64)]));
    let f1 = f.bind_slot(f0, 0, x);
    let zero = u64c(&mut f, 0);
    let done = f.icmp(ICmpOp::Eq, Ty::U64, x, zero);
    f.condbr(done, exit, vec![], entry, vec![zero, f1]);
    f.switch_to_block(exit);
    f.close_frame(f1);
    f.ret(vec![read]);
    f.build();
    m.build().expect("ModuleBuilder::build: test fixture")
}

/// `(fixture, needle the refusal must name, the interpreter must fault with
/// undefined behaviour on input 3)`.
fn refusal_fixtures() -> Vec<(&'static str, &'static str, bool, Module)> {
    vec![
        (
            "undef_masked_by_arithmetic",
            "reaches an inspecting use in Inst::BinOp",
            true,
            fixture(|f, x| {
                let poison = f.undef(Ty::U64);
                let zero = u64c(f, 0);
                let masked = f.binop(BinOp::And, Ty::U64, poison, zero);
                let sum = f.binop(BinOp::Add, Ty::U64, masked, x);
                f.ret(vec![sum]);
            }),
        ),
        (
            "undef_branch_condition",
            "reaches an inspecting use in Inst::CondBr",
            true,
            fixture(|f, x| {
                let taken = f.create_block();
                let other = f.create_block();
                let poison = f.undef(Ty::Bool);
                f.condbr(poison, taken, vec![], other, vec![]);
                f.switch_to_block(taken);
                f.ret(vec![x]);
                f.switch_to_block(other);
                let zero = u64c(f, 0);
                f.ret(vec![zero]);
            }),
        ),
        (
            "undef_guard",
            "reaches an inspecting use in Inst::Assume",
            true,
            fixture(|f, x| {
                let poison = f.undef(Ty::Bool);
                f.assume(poison);
                f.ret(vec![x]);
            }),
        ),
        (
            "undef_trapping_divisor",
            "reaches an inspecting use in Inst::BinOp",
            true,
            fixture(|f, x| {
                let poison = f.undef(Ty::U64);
                let quotient = f.binop(BinOp::UDiv, Ty::U64, x, poison);
                f.ret(vec![quotient]);
            }),
        ),
        (
            "undef_returned_through_a_select",
            "reaches an inspecting use in Inst::Return",
            true,
            fixture(|f, x| {
                let poison = f.undef(Ty::U64);
                let ten = u64c(f, 10);
                let small = f.icmp(ICmpOp::Ult, Ty::U64, x, ten);
                let selected = f.select(Ty::U64, small, poison, x);
                f.ret(vec![selected]);
            }),
        ),
        (
            "undef_fresh_symbolic_havoc",
            "FreshSymbolicHavoc",
            false,
            fixture(|f, x| {
                let havoc = f.undef_proven(Ty::U64, vec![ProofAnnotation::FreshSymbolicHavoc]);
                let cell = f.alloca(Ty::U64);
                f.store(Ty::U64, cell, havoc);
                f.ret(vec![x]);
            }),
        ),
        (
            "undef_aggregate",
            "aggregate/vector poison is unmodelled",
            false,
            fixture(|f, x| {
                let pair = Ty::Tuple(vec![Ty::U64, Ty::U64]);
                let poison = f.undef(pair.clone());
                let cell = f.alloca(pair.clone());
                f.store(pair, cell, poison);
                f.ret(vec![x]);
            }),
        ),
        (
            "unique_reborrow_of_a_shared_borrow",
            "BorrowMutThroughSharedRef",
            false,
            fixture(|f, x| {
                let cell = f.alloca(Ty::U64);
                f.store(Ty::U64, cell, x);
                let shared = f.borrow(cell);
                let unique = f.borrow_mut(shared);
                f.store(Ty::U64, unique, x);
                f.end_borrow(unique);
                f.end_borrow(shared);
                let read = f.load(Ty::U64, cell);
                f.ret(vec![read]);
            }),
        ),
        (
            "borrow_of_a_non_pointer",
            "non-addressable",
            false,
            fixture(|f, x| {
                let borrowed = f.borrow(x);
                f.end_borrow(borrowed);
                f.ret(vec![x]);
            }),
        ),
        (
            "borrow_of_null",
            "the null pointer",
            true,
            fixture(|f, x| {
                let null = f.null_ptr();
                let borrowed = f.borrow(null);
                f.end_borrow(borrowed);
                f.ret(vec![x]);
            }),
        ),
        (
            "superseded_frame_handle_read_after_rebind",
            "still live after",
            false,
            fixture(|f, x| {
                let f0 = f.open_frame(frame_def(0, &[("s", Ty::U64)]));
                let f1 = f.bind_slot(f0, 0, x);
                let one = u64c(f, 1);
                let f2 = f.bind_slot(f1, 0, one);
                let stale = f.load_slot(f1, 0, Ty::U64);
                let fresh = f.load_slot(f2, 0, Ty::U64);
                f.close_frame(f2);
                let sum = f.binop(BinOp::Add, Ty::U64, stale, fresh);
                f.ret(vec![sum]);
            }),
        ),
        (
            "superseded_frame_handle_read_in_a_successor_block",
            "still live after",
            false,
            fixture(|f, x| {
                let next = f.create_block();
                let f0 = f.open_frame(frame_def(0, &[("s", Ty::U64)]));
                let f1 = f.bind_slot(f0, 0, x);
                let one = u64c(f, 1);
                let bumped = f.binop(BinOp::Add, Ty::U64, x, one);
                let f2 = f.bind_slot(f1, 0, bumped);
                f.br(next, vec![]);
                f.switch_to_block(next);
                let stale = f.load_slot(f1, 0, Ty::U64);
                f.close_frame(f2);
                f.ret(vec![stale]);
            }),
        ),
        (
            "frame_handle_in_an_entry_block_parameter",
            "entry-block parameter",
            false,
            entry_parameter_frame_fixture(),
        ),
        (
            "frame_handle_escapes_to_a_store",
            "escapes into Inst::Store",
            false,
            fixture(|f, x| {
                let cell = f.alloca(Ty::Ptr);
                let f0 = f.open_frame(frame_def(0, &[("s", Ty::U64)]));
                f.store(Ty::Ptr, cell, f0);
                f.close_frame(f0);
                f.ret(vec![x]);
            }),
        ),
        (
            "aggregate_frame_slot",
            "only scalar",
            false,
            fixture(|f, x| {
                let f0 = f.open_frame(frame_def(0, &[("pair", Ty::Tuple(vec![Ty::U64, Ty::U64]))]));
                f.close_frame(f0);
                f.ret(vec![x]);
            }),
        ),
        (
            "slot_bound_on_one_path_only",
            "may be unbound",
            true,
            fixture(|f, x| {
                let bound_arm = f.create_block();
                let unbound_arm = f.create_block();
                let merge = f.create_block();
                let handle = f.add_block_param(merge, Ty::Ptr);
                let f0 = f.open_frame(frame_def(0, &[("s", Ty::U64)]));
                // Input 3 takes the unbound arm.
                let two = u64c(f, 2);
                let small = f.icmp(ICmpOp::Ult, Ty::U64, x, two);
                f.condbr(small, bound_arm, vec![], unbound_arm, vec![]);
                f.switch_to_block(bound_arm);
                let f1 = f.bind_slot(f0, 0, x);
                f.br(merge, vec![f1]);
                f.switch_to_block(unbound_arm);
                f.br(merge, vec![f0]);
                f.switch_to_block(merge);
                let read = f.load_slot(handle, 0, Ty::U64);
                f.close_frame(handle);
                f.ret(vec![read]);
            }),
        ),
        (
            "undef_volatile_store",
            "reaches an inspecting use in Inst::Store",
            true,
            fixture(|f, x| {
                let poison = f.undef(Ty::U64);
                let cell = f.alloca(Ty::U64);
                f.store_volatile(Ty::U64, cell, poison);
                f.ret(vec![x]);
            }),
        ),
        (
            "unbound_slot_inspected",
            "may be unbound",
            true,
            fixture(|f, x| {
                let f0 = f.open_frame(frame_def(0, &[("s", Ty::U64)]));
                let read = f.load_slot(f0, 0, Ty::U64);
                f.close_frame(f0);
                let sum = f.binop(BinOp::Add, Ty::U64, read, x);
                f.ret(vec![sum]);
            }),
        ),
    ]
}

fn compile(module: &Module, opt_level: OptLevel) -> Result<Vec<u8>, String> {
    Compiler::new_for_target_spec(
        CompilerConfig {
            opt_level,
            ..CompilerConfig::default()
        },
        TargetSpec::parse(TRIPLE).unwrap(),
    )
    .with_codegen_license(permit_unlicensed())
    .compile(module)
    .map(|output| output.object_code)
    .map_err(|error| format!("{error}"))
}

fn interpret(
    module: &Module,
    name: &str,
    x: u64,
) -> Result<u64, trust_ir::interpret::InterpretError> {
    let function = module
        .functions
        .iter()
        .find(|f| f.name == name)
        .unwrap_or_else(|| panic!("no function {name}"));
    let argument = InterpretValue::int(Ty::U64, i128::from(x)).expect("u64 argument");
    let outcome = Interpreter::with_module(module).execute_function(function, [argument])?;
    let [value] = outcome.returns.as_slice() else {
        panic!("{name}: expected one result, got {:?}", outcome.returns)
    };
    let int = value.as_int().expect("integer result");
    Ok(u64::try_from(int.as_unsigned() & u128::from(u64::MAX)).expect("u64 pattern"))
}

fn driver() -> String {
    let mut text = String::from("#include <stdint.h>\n#include <stdio.h>\n\n");
    for name in FUNCTIONS {
        text.push_str(&format!("extern uint64_t {name}(uint64_t);\n"));
    }
    text.push_str("\nint main(void) {\n    static const uint64_t inputs[] = {");
    for x in INPUTS {
        text.push_str(&format!("{x}ull, "));
    }
    text.push_str("};\n    int lines = 0;\n");
    text.push_str("    for (unsigned i = 0; i < sizeof inputs / sizeof inputs[0]; i++) {\n");
    text.push_str("        uint64_t x = inputs[i];\n");
    for name in FUNCTIONS {
        text.push_str(&format!(
            "        printf(\"{name}(%llu)=%llu\\n\", (unsigned long long)x, (unsigned long long){name}(x)); lines++;\n"
        ));
    }
    text.push_str("    }\n    printf(\"DONE %d\\n\", lines);\n    return 0;\n}\n");
    text
}

/// The interpreter itself is pinned to the closed forms, so it cannot agree
/// with a wrong native value by being wrong the same way.
#[test]
fn interpreter_oracle_matches_the_closed_forms() {
    let module = corpus();
    assert_eq!(
        validate_module(&module),
        [],
        "the corpus must be valid trust-ir"
    );
    for name in FUNCTIONS {
        for x in INPUTS {
            assert_eq!(
                interpret(&module, name, x).unwrap_or_else(|e| panic!("{name}({x}): {e:?}")),
                oracle(name, x),
                "{name}({x})"
            );
        }
    }
}

/// Every construct lowers through the named stage and is recorded in the
/// function's receipt: each borrow with its kind and root, each retirement,
/// each frame's storage, each materialized undef.
#[test]
fn every_positive_function_lowers_with_its_receipt() {
    let module = corpus();
    let lowered = permit_translate_module(&module).expect("the corpus lowers");
    let receipt = |name: &str| {
        let index = module
            .functions
            .iter()
            .position(|f| f.name == name)
            .unwrap_or_else(|| panic!("no function {name}"));
        lowered[index].1.borrow_frame_undef.clone()
    };

    let stack = receipt("bf_stack_borrow");
    assert_eq!(stack.borrows.len(), 2);
    assert_eq!(stack.retired_borrows.len(), 2);
    assert_eq!(
        stack.borrows.iter().map(|b| b.kind).collect::<Vec<_>>(),
        [BorrowKind::Unique, BorrowKind::Shared]
    );
    assert_eq!(
        stack.borrows[0].root, stack.borrows[1].root,
        "both borrow the one cell"
    );

    let reborrow = receipt("bf_reborrow");
    assert_eq!(reborrow.borrows.len(), 4);
    assert_eq!(reborrow.retired_borrows.len(), 4);
    let root = reborrow.borrows[0].root;
    assert!(
        reborrow.borrows.iter().all(|b| b.root == root),
        "every reborrow records the original cell as its root: {reborrow:?}"
    );

    let mixed = receipt("bf_frame_mixed");
    assert_eq!(mixed.frames.len(), 1);
    let frame = &mixed.frames[0];
    assert_eq!(frame.slots.len(), 8);
    assert!(frame.bytes % 8 == 0 && frame.align >= 8);
    let mut previous_end = 0;
    for slot in &frame.slots {
        assert!(
            slot.offset >= previous_end,
            "slots do not overlap: {frame:?}"
        );
        assert_eq!(slot.offset % slot.carrier.align(), 0, "{frame:?}");
        previous_end = slot.offset + slot.carrier.bytes();
    }
    assert!(previous_end <= frame.bytes);

    let fat = receipt("bf_fat_borrow");
    assert_eq!(fat.borrows.len(), 4);
    assert_eq!(fat.retired_borrows.len(), 4);
    assert_eq!(
        fat.borrows.iter().map(|b| b.kind).collect::<Vec<_>>(),
        [
            BorrowKind::Unique,
            BorrowKind::Shared,
            BorrowKind::Shared,
            BorrowKind::Shared
        ]
    );
    assert!(
        fat.borrows[..3]
            .iter()
            .all(|b| b.root == fat.borrows[0].root),
        "the stack fat pointer's borrows and reborrow share one root: {fat:?}"
    );
    assert_ne!(
        fat.borrows[3].root, fat.borrows[0].root,
        "the global table's fat pointer is a different root"
    );

    assert_eq!(receipt("bf_frame_nested").frames.len(), 2);
    assert_eq!(receipt("bf_frame_loop").frames.len(), 1);
    assert_eq!(receipt("bf_undef_transport").undefs.len(), 1);
    assert_eq!(receipt("bf_undef_carriers").undefs.len(), 9);
    assert!(receipt("bf_global_rw").frames.is_empty());
}

/// The strict (no pre-LIR rewrite) entry lowers the same corpus: the stage is
/// ordinary lowering with a receipt, not an adapter-owned module clone.
#[test]
fn the_strict_entry_lowers_the_corpus_with_the_same_receipts() {
    let module = corpus();
    let strict =
        trust_cg_codegen::strict_adapter::translate_core_module_for_target_with_validation_and_license(
            &module,
            TargetSpec::parse(TRIPLE).unwrap(),
            &permit_unlicensed(),
        )
        .expect("the strict entry admits the legalized corpus");
    let compatibility = permit_translate_module(&module).expect("the corpus lowers");
    assert_eq!(strict.functions().len(), compatibility.len());
    for ((_, strict), (_, compatible)) in strict.functions().iter().zip(&compatibility) {
        assert_eq!(strict.borrow_frame_undef, compatible.borrow_frame_undef);
    }
}

/// What stays refused is refused by name at O0 and O3; for every poison
/// fixture the reference interpreter's own verdict is undefined behaviour.
#[test]
fn what_stays_refused_is_refused_by_name_and_poison_is_undefined_in_trust_ir() {
    for (fixture, needle, interpreter_faults, module) in refusal_fixtures() {
        for opt_level in [OptLevel::O0, OptLevel::O3] {
            let error = compile(&module, opt_level).err().unwrap_or_else(|| {
                panic!("{fixture} {opt_level:?}: compiled, expected `{needle}`")
            });
            // A fixture trust-ir itself refuses is refused by that finding at
            // ingestion since WS7.3, before the backend's named arm; trust-ir
            // judges it under the policy `compile` states.
            match admission_expect::names_first_finding(&module, &error, &permit_unlicensed()) {
                Some(named) => assert!(named, "{fixture} {opt_level:?}: {error}"),
                None => assert!(
                    error.contains(needle),
                    "{fixture} {opt_level:?}: `{needle}` not in {error}"
                ),
            }
        }
        if interpreter_faults {
            let error = interpret(&module, "refused", 3)
                .expect_err("inspecting poison is undefined behaviour in trust-ir");
            assert_eq!(
                error.code,
                InterpretErrorCode::UndefinedBehavior,
                "{fixture}: {error:?}"
            );
        }
    }
}

#[test]
fn native_borrows_frames_and_undef_agree_with_the_interpreter_o0_through_o3() {
    if !cfg!(all(target_os = "macos", target_arch = "aarch64")) {
        eprintln!("SKIP: needs aarch64-apple-darwin");
        return;
    }
    let module = corpus();
    assert_eq!(
        validate_module(&module),
        [],
        "the corpus must be valid trust-ir"
    );
    let mut expected = Vec::new();
    for x in INPUTS {
        for name in FUNCTIONS {
            let value =
                interpret(&module, name, x).unwrap_or_else(|e| panic!("{name}({x}): {e:?}"));
            expected.push(format!("{name}({x})={value}"));
        }
    }
    for opt_level in LEVELS {
        let object = compile(&module, opt_level).unwrap();
        assert_eq!(
            &object[..4],
            &[0xcf, 0xfa, 0xed, 0xfe],
            "Mach-O 64 object expected"
        );
        let dir = std::env::temp_dir().join(format!(
            "trust-cg-borrows-frames-{}-{}",
            std::process::id(),
            SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        fs::create_dir(&dir).unwrap();
        fs::write(dir.join("module.o"), &object).unwrap();
        fs::write(dir.join("driver.c"), driver()).unwrap();
        let binary = dir.join("driver");
        let link = process::command_output_with_timeout(
            Command::new("cc")
                .arg("-O2")
                .arg(dir.join("driver.c"))
                .arg(dir.join("module.o"))
                .arg("-o")
                .arg(&binary),
            process::codegen_link_timeout(),
        )
        .unwrap();
        assert!(
            !link.timed_out && link.output.status.success(),
            "{opt_level:?} files={dir:?}: {}",
            String::from_utf8_lossy(&link.output.stderr)
        );
        let run =
            process::run_executable_with_timeout(&binary, process::codegen_run_timeout()).unwrap();
        let stdout = String::from_utf8_lossy(&run.output.stdout);
        assert!(
            !run.timed_out && run.output.status.success(),
            "{opt_level:?} files={dir:?}: {stdout} {}",
            String::from_utf8_lossy(&run.output.stderr)
        );
        let mut lines: Vec<&str> = stdout.lines().collect();
        assert_eq!(
            lines.pop(),
            Some(format!("DONE {}", expected.len()).as_str()),
            "{opt_level:?} files={dir:?}: incomplete native execution: {stdout}"
        );
        assert_eq!(lines.len(), expected.len(), "{opt_level:?}: {stdout}");
        for (native, want) in lines.iter().zip(&expected) {
            assert_eq!(
                native, want,
                "{opt_level:?}: native value disagrees with the interpreter"
            );
        }
        eprintln!(
            "{opt_level:?}: {} native (function, input) values agree with the interpreter",
            expected.len()
        );
        fs::remove_dir_all(&dir).unwrap();
    }
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles and lowerings state `Permit`
/// explicitly, so none of them passes (or is refused) because the license
/// silently refused it.
fn permit_unlicensed() -> trust_cg_codegen::CodegenLicensePolicy {
    trust_cg_codegen::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_codegen::UnlicensedBodyPolicy::Permit)
}

/// `trust_cg_lower::translate_module` under [`permit_unlicensed`].
fn permit_translate_module(
    module: &Module,
) -> Result<
    Vec<(trust_cg_lower::Function, trust_cg_lower::ProofContext)>,
    trust_cg_lower::AdapterError,
> {
    trust_cg_lower::translate_module_for_arch_with_tls_with_license(
        module,
        trust_cg_lower::GuardCarrierArch::default(),
        trust_cg_lower::TlsDialect::default(),
        &permit_unlicensed(),
    )
}
