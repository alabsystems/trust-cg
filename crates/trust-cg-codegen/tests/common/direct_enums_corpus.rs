// Copyright 2026 Andrew Yates | Apache-2.0
//! Shared TrustIR corpus, C driver and reference-interpreter oracle for the
//! AArch64 direct-tag enum native controls (`e2e_aarch64_direct_enums.rs` on
//! Darwin, `e2e_aarch64_direct_enums_linux.rs` on Linux), ledger L05-P5:
//!
//! ```text
//! Ordering { Less = -1, Equal = 0, Greater = 1 }   repr i8      int8_t
//! Mixed    { A(u8, u32) = 10, B(u64) = 20, C = 30 } repr u8     tag@0 A.0@1 A.1@4 B.0@8, 16/8
//! ReprC    { X(u8), Y(u8) }                         repr u32    tag@0 payload@4, 8/4
//! Small    { A(u16, u8), B(u8) }                                tag@0 A.0@2 A.1@1 B.0@1, 4/2
//! Slot     { Empty = 0, Fn(ptr) = 7 }                           tag@0 ptr@8, 16/8
//! Bytes3   { First([u8; 3], u8), Second(..) }       repr u8     tag@0 [u8;3]@1 u8@4, 5/1
//! Rec      { a: u16, b: u64 }                       record      a@0 b@8, 16/8
//! ```
//!
//! Every enum carries the producer layout rustc gives it, spelled in the C
//! driver as the plain scalar or struct it is. The corpus reads discriminants
//! (`ExtractField` element 0), switches and signed-compares on them,
//! constructs variants from constants, reads payload lanes at the producer's
//! offsets, and reads enum-, record- and relocation-bearing globals. The
//! driver's oracle is the C meaning of each spelling; every zero-argument
//! function is ALSO run by the trust-ir reference interpreter, and the native
//! value printed by the driver must equal the interpreter's, at O0-O3. The
//! refusal fixtures are what stays refused by name on either object format.
//!
//! The driver's function boundaries are pointers and `uint64_t`/`int64_t`
//! values plus one `uint8_t` selector, so the layouts it spells are the same
//! under the Apple arm64 ABI and AAPCS64; the selector is where the two
//! differ (Apple's caller extends it to 32 bits, AAPCS64 leaves the upper
//! bits unspecified for the callee to ignore), which the Linux twin tests
//! separately. Execution evidence, not proof of enum semantics.
#![allow(dead_code)]

use trust_cg_codegen::pipeline::OptLevel;
use trust_ir::interpret::Interpreter;
use trust_ir::ty::{EnumLayoutDescriptor, EnumTagEncoding, EnumTagRepr};
use trust_ir::value::GlobalId;
use trust_ir::{
    Constant, Endianness, EnumDef, EnumId, EnumVariant, FieldDef, FuncId, Global, ICmpOp, Linkage,
    Module, RecordDef, RecordId, StructPassingPolicy, SwitchCase, TargetInfo, Ty,
};
use trust_ir_build::{FunctionBuilder, ModuleBuilder};

pub const LEVELS: [OptLevel; 4] = [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3];

pub const ORDERING: u32 = 0;
pub const MIXED: u32 = 1;
pub const REPRC: u32 = 2;
pub const SLOT: u32 = 3;
pub const BYTES3: u32 = 4;
pub const SMALL: u32 = 5;
pub const REC: u32 = 0;

const G_ORD: u32 = 0;
const G_MIXED: u32 = 1;
// GlobalId 2 is `g_slot`, read by the C driver alone (its payload is a relocation).
const G_REC: u32 = 3;
const G_BYTES: u32 = 4;

/// The zero-argument functions the driver prints and the interpreter replays,
/// with the closed form each must equal (the interpreter is pinned to it too,
/// so a wrong oracle cannot hide a wrong native value).
pub const ORACLE: &[(&str, u64)] = &[
    ("o_ord_less", 100),
    ("o_ord_equal", 200),
    ("o_ord_greater", 300),
    ("o_ord_sext", u64::MAX),
    ("o_ord_is_less", 1),
    ("o_ord_is_not_less", 0),
    ("o_mixed_a", 0x11 + 0x2233_4455),
    ("o_mixed_b", 0x1122_3344_5566_7788),
    ("o_mixed_c", 3000),
    ("o_reprc_x", 0x2A),
    ("o_reprc_y", 0x2B + 1000),
    ("o_small_a", 0x1234 + 0x56),
    ("o_small_b", 0x78 + 500),
    ("o_g_ord", 1),
    ("o_g_mixed", 0x5A + 0x1122_3344),
    ("o_g_bytes", 1 + 0xe7),
];

/// Zero-argument functions the reference interpreter cannot replay — it has
/// no byte layout for a `Ty::Record` ("record.0 has no byte layout"), so a
/// record global's image is checked against its closed form by the driver
/// alone, at the natural-C layout the byte path emits for records.
pub const NATIVE_ONLY: &[(&str, u64)] = &[("o_g_rec", 0x0A0B + 0x0102_0304_0506_0708)];

pub fn target(triple: &str) -> TargetInfo {
    TargetInfo {
        triple: triple.into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: Some("aapcs64".into()),
        struct_passing: StructPassingPolicy::NativeC,
    }
}

fn variant(name: &str, fields: Vec<Ty>) -> EnumVariant {
    EnumVariant {
        name: name.into(),
        fields,
        field_names: Vec::new(),
    }
}

fn direct(tag_offset: u64, size: u64, align: u64, offsets: Vec<Vec<u64>>) -> EnumLayoutDescriptor {
    EnumLayoutDescriptor {
        encoding: EnumTagEncoding::Direct { tag_offset },
        size,
        align,
        variant_field_offsets: offsets,
    }
}

pub fn enum_ty(id: u32) -> Ty {
    Ty::Enum(EnumId::new(id))
}

fn case(value: i128, target: trust_ir::BlockId) -> SwitchCase {
    SwitchCase {
        value: Constant::Int(value),
        target,
        args: vec![],
    }
}

/// `Ordering { Less = -1, Equal = 0, Greater = 1 }`, `#[repr(i8)]`: (c) MEASURED
/// size 1, align 1 under rustc.
fn ordering() -> EnumDef {
    EnumDef {
        origin: None,
        id: EnumId::new(ORDERING),
        name: "Ordering".into(),
        variants: vec![
            variant("Less", vec![]),
            variant("Equal", vec![]),
            variant("Greater", vec![]),
        ],
        discriminants: vec![Some(-1), Some(0), Some(1)],
        repr: Some(EnumTagRepr::I8),
        layout: Some(direct(0, 1, 1, vec![vec![], vec![], vec![]])),
    }
}

/// `Mixed { A(u8, u32) = 10, B(u64) = 20, C = 30 }`, `#[repr(u8)]`: rustc lays
/// each variant out as its own struct behind the tag, so `A.0` is at byte 1
/// and `A.1` at byte 4, where the canonical shape puts every payload at 8.
fn mixed() -> EnumDef {
    EnumDef {
        origin: None,
        id: EnumId::new(MIXED),
        name: "Mixed".into(),
        variants: vec![
            variant("A", vec![Ty::U8, Ty::U32]),
            variant("B", vec![Ty::U64]),
            variant("C", vec![]),
        ],
        discriminants: vec![Some(10), Some(20), Some(30)],
        repr: Some(EnumTagRepr::U8),
        layout: Some(direct(0, 16, 8, vec![vec![1, 4], vec![8], vec![]])),
    }
}

/// `#[repr(C)] enum ReprC { X(u8), Y(u8) }`: a C `int` tag, the payload at 4,
/// 8 bytes, 4-aligned — a declared four-byte tag lane on a two-variant enum,
/// which the canonical shape reproduces.
fn reprc() -> EnumDef {
    EnumDef {
        origin: None,
        id: EnumId::new(REPRC),
        name: "ReprC".into(),
        variants: vec![variant("X", vec![Ty::U8]), variant("Y", vec![Ty::U8])],
        discriminants: Vec::new(),
        repr: Some(EnumTagRepr::U32),
        layout: Some(direct(0, 8, 4, vec![vec![4], vec![4]])),
    }
}

/// `enum Small { A(u16, u8), B(u8) }`, `repr(Rust)`: rustc REORDERS `A`'s
/// fields (the u8 at byte 1, the u16 at byte 2) and packs the whole enum into
/// 4 bytes, where the canonical shape needs 6 (payload at 2, `A.0` at 2, `A.1`
/// at 4): a size disagreement as well as an offset one.
fn small() -> EnumDef {
    EnumDef {
        origin: None,
        id: EnumId::new(SMALL),
        name: "Small".into(),
        variants: vec![
            variant("A", vec![Ty::U16, Ty::U8]),
            variant("B", vec![Ty::U8]),
        ],
        discriminants: Vec::new(),
        repr: None,
        layout: Some(direct(0, 4, 2, vec![vec![2, 1], vec![1]])),
    }
}

/// `Slot { Empty = 0, Fn(*const ()) = 7 }`: a pointer payload behind a
/// padded tag; its global initializer carries a relocation.
fn slot() -> EnumDef {
    EnumDef {
        origin: None,
        id: EnumId::new(SLOT),
        name: "Slot".into(),
        variants: vec![variant("Empty", vec![]), variant("Fn", vec![Ty::Ptr])],
        discriminants: vec![Some(0), Some(7)],
        repr: None,
        layout: Some(direct(0, 16, 8, vec![vec![], vec![8]])),
    }
}

/// `Bytes3 { First([u8; 3], u8), Second([u8; 3], u8) }`, `#[repr(u8)]`, 5 bytes.
fn bytes3(payload: Ty) -> EnumDef {
    EnumDef {
        origin: None,
        id: EnumId::new(BYTES3),
        name: "Bytes3".into(),
        variants: vec![
            variant("First", vec![payload.clone(), Ty::U8]),
            variant("Second", vec![payload, Ty::U8]),
        ],
        discriminants: Vec::new(),
        repr: Some(EnumTagRepr::U8),
        layout: Some(direct(0, 5, 1, vec![vec![1, 4], vec![1, 4]])),
    }
}

fn record() -> RecordDef {
    RecordDef {
        id: RecordId::new(REC),
        name: "Rec".into(),
        fields: vec![
            FieldDef {
                name: "a".into(),
                ty: Ty::U16,
                offset: None,
            },
            FieldDef {
                name: "b".into(),
                ty: Ty::U64,
                offset: None,
            },
        ],
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

/// `switch tag { value => ret constant.. } default => ret 0xBAD`.
fn ret_by_switch(f: &mut FunctionBuilder<'_>, tag: trust_ir::ValueId, arms: &[(i128, u64)]) {
    let blocks: Vec<_> = arms.iter().map(|_| f.create_block()).collect();
    let bad = f.create_block();
    f.switch(
        tag,
        arms.iter()
            .zip(&blocks)
            .map(|((value, _), block)| case(*value, *block))
            .collect(),
        bad,
        vec![],
    );
    for ((_, result), block) in arms.iter().zip(&blocks) {
        f.switch_to_block(*block);
        let r = f.iconst(Ty::U64, i128::from(*result));
        f.ret(vec![r]);
    }
    f.switch_to_block(bad);
    let r = f.iconst(Ty::U64, 0xBAD);
    f.ret(vec![r]);
}

/// A zero-argument function that stores `constant` (of `ty`) in a stack slot
/// and returns `callee(slot)`.
fn define_oracle_call(
    m: &mut ModuleBuilder,
    name: &str,
    ty: Ty,
    constant: Constant,
    callee: FuncId,
    ret_ty: Ty,
) {
    let sig = m.add_func_type(vec![], vec![ret_ty]);
    let mut f = m.function(name, sig);
    let entry = f.create_block();
    f.switch_to_block(entry);
    let slot = f.alloca(ty.clone());
    let value = f.const_value(ty.clone(), constant);
    f.store(ty, slot, value);
    let r = f.call(callee, vec![slot]);
    f.ret(vec![r]);
    f.build();
}

/// A zero-argument function returning `callee(&global)`.
fn define_oracle_global(
    m: &mut ModuleBuilder,
    name: &str,
    global: u32,
    callee: FuncId,
    ret_ty: Ty,
) {
    let sig = m.add_func_type(vec![], vec![ret_ty]);
    let mut f = m.function(name, sig);
    let entry = f.create_block();
    f.switch_to_block(entry);
    let p = f.global_addr(GlobalId::new(global));
    let r = f.call(callee, vec![p]);
    f.ret(vec![r]);
    f.build();
}

/// `{name}(out, which)`: store the `which`-th constant of `ty` (the last one
/// for every other selector).
fn define_make(m: &mut ModuleBuilder, name: &str, ty: Ty, constants: &[Constant]) {
    let sig = m.add_func_type(vec![Ty::Ptr, Ty::U8], vec![]);
    let mut f = m.function(name, sig);
    let entry = f.create_block();
    let out = f.add_block_param(entry, Ty::Ptr);
    let which = f.add_block_param(entry, Ty::U8);
    f.switch_to_block(entry);
    let blocks: Vec<_> = constants.iter().map(|_| f.create_block()).collect();
    let (last, cased) = blocks.split_last().expect("at least one constant");
    f.switch(
        which,
        cased
            .iter()
            .enumerate()
            .map(|(i, block)| case(i as i128, *block))
            .collect(),
        *last,
        vec![],
    );
    for (constant, block) in constants.iter().zip(&blocks) {
        f.switch_to_block(*block);
        let value = f.const_value(ty.clone(), constant.clone());
        f.store(ty.clone(), out, value);
        f.ret(vec![]);
    }
    f.build();
}

fn ordering_const(disc: i128) -> Constant {
    Constant::Aggregate(vec![Constant::Int(disc)])
}

fn mixed_a(x: i128, y: i128) -> Constant {
    Constant::Aggregate(vec![Constant::Int(10), Constant::Int(x), Constant::Int(y)])
}

fn mixed_b(v: i128) -> Constant {
    Constant::Aggregate(vec![Constant::Int(20), Constant::Int(v)])
}

fn mixed_c() -> Constant {
    Constant::Aggregate(vec![Constant::Int(30)])
}

fn reprc_const(disc: i128, v: i128) -> Constant {
    Constant::Aggregate(vec![Constant::Int(disc), Constant::Int(v)])
}

fn small_a(x: i128, y: i128) -> Constant {
    Constant::Aggregate(vec![Constant::Int(0), Constant::Int(x), Constant::Int(y)])
}

fn small_b(v: i128) -> Constant {
    Constant::Aggregate(vec![Constant::Int(1), Constant::Int(v)])
}

/// The corpus, for `triple`.
pub fn corpus(triple: &str) -> Module {
    let mut m = ModuleBuilder::new_with_target_info("direct_enums", target(triple));
    let u8_ty = m.add_type(Ty::U8);
    let three = Ty::Array(u8_ty, 3);
    m.add_enum(ordering());
    m.add_enum(mixed());
    m.add_enum(reprc());
    m.add_enum(slot());
    m.add_enum(bytes3(three));
    m.add_enum(small());
    m.add_record(record());
    let rec_ty = Ty::Record(RecordId::new(REC));

    // Globals, in GlobalId order.
    m.add_global(global("g_ord", enum_ty(ORDERING), false, ordering_const(1)));
    m.add_global(global(
        "g_mixed",
        enum_ty(MIXED),
        true,
        mixed_a(0x5A, 0x1122_3344),
    ));
    m.add_global(global(
        "g_slot",
        enum_ty(SLOT),
        false,
        Constant::Aggregate(vec![
            Constant::Int(7),
            Constant::SymbolAddr {
                symbol: "ord_disc".into(),
                addend: 0,
            },
        ]),
    ));
    m.add_global(global(
        "g_rec",
        rec_ty.clone(),
        false,
        // trust-ir's validator requires a record constant's fields in
        // declaration order; the renderer would accept either.
        Constant::Record(vec![
            ("a".into(), Constant::Int(0x0A0B)),
            ("b".into(), Constant::Int(0x0102_0304_0506_0708)),
        ]),
    ));
    m.add_global(global(
        "g_bytes",
        enum_ty(BYTES3),
        false,
        Constant::Aggregate(vec![
            Constant::Int(1),
            Constant::Bytes {
                data: vec![0x00, 0xc3, 0xa9],
                utf8: true,
            },
            Constant::Int(0xe7),
        ]),
    ));

    // ord_disc(p) = (i64) discriminant(*p), sign-extended from the i8 lane.
    let ord_disc = {
        let sig = m.add_func_type(vec![Ty::Ptr], vec![Ty::I64]);
        let mut f = m.function("ord_disc", sig);
        let entry = f.create_block();
        let p = f.add_block_param(entry, Ty::Ptr);
        f.switch_to_block(entry);
        let v = f.load(enum_ty(ORDERING), p);
        let t = f.extract_field(Ty::I8, v, 0);
        let wide = f.sext(Ty::I8, Ty::I64, t);
        f.ret(vec![wide]);
        f.build()
    };
    // ord_classify(p): Less -> 100, Equal -> 200, Greater -> 300.
    let ord_classify = {
        let sig = m.add_func_type(vec![Ty::Ptr], vec![Ty::U64]);
        let mut f = m.function("ord_classify", sig);
        let entry = f.create_block();
        let p = f.add_block_param(entry, Ty::Ptr);
        f.switch_to_block(entry);
        let v = f.load(enum_ty(ORDERING), p);
        let t = f.extract_field(Ty::I8, v, 0);
        ret_by_switch(&mut f, t, &[(-1, 100), (0, 200), (1, 300)]);
        f.build()
    };
    // ord_is_less(p) = discriminant(*p) <s 0: a SIGNED compare on the i8 lane.
    let ord_is_less = {
        let sig = m.add_func_type(vec![Ty::Ptr], vec![Ty::U64]);
        let mut f = m.function("ord_is_less", sig);
        let entry = f.create_block();
        let p = f.add_block_param(entry, Ty::Ptr);
        f.switch_to_block(entry);
        let v = f.load(enum_ty(ORDERING), p);
        let t = f.extract_field(Ty::I8, v, 0);
        let zero = f.iconst(Ty::I8, 0);
        let less = f.icmp(ICmpOp::Slt, Ty::I8, t, zero);
        let wide = f.zext(Ty::Bool, Ty::U64, less);
        f.ret(vec![wide]);
        f.build()
    };
    define_make(
        &mut m,
        "ord_make",
        enum_ty(ORDERING),
        &[ordering_const(-1), ordering_const(0), ordering_const(1)],
    );

    // mixed_disc(p) = (u64) discriminant(*p).
    let mixed_disc = {
        let sig = m.add_func_type(vec![Ty::Ptr], vec![Ty::U64]);
        let mut f = m.function("mixed_disc", sig);
        let entry = f.create_block();
        let p = f.add_block_param(entry, Ty::Ptr);
        f.switch_to_block(entry);
        let v = f.load(enum_ty(MIXED), p);
        let t = f.extract_field(Ty::U8, v, 0);
        let wide = f.zext(Ty::U8, Ty::U64, t);
        f.ret(vec![wide]);
        f.build()
    };
    let _ = mixed_disc;
    // mixed_sum(p): A(x, y) -> x + y, B(v) -> v, C -> 3000.
    let mixed_sum = {
        let sig = m.add_func_type(vec![Ty::Ptr], vec![Ty::U64]);
        let mut f = m.function("mixed_sum", sig);
        let entry = f.create_block();
        let a = f.create_block();
        let b = f.create_block();
        let c = f.create_block();
        let bad = f.create_block();
        let p = f.add_block_param(entry, Ty::Ptr);
        f.switch_to_block(entry);
        let v = f.load(enum_ty(MIXED), p);
        let t = f.extract_field(Ty::U8, v, 0);
        f.switch(t, vec![case(10, a), case(20, b), case(30, c)], bad, vec![]);
        f.switch_to_block(a);
        let x = f.extract_field(Ty::U8, v, 1);
        let y = f.extract_field(Ty::U32, v, 2);
        let wx = f.zext(Ty::U8, Ty::U64, x);
        let wy = f.zext(Ty::U32, Ty::U64, y);
        let sum = f.add(Ty::U64, wx, wy);
        f.ret(vec![sum]);
        f.switch_to_block(b);
        let payload = f.extract_field(Ty::U64, v, 1);
        f.ret(vec![payload]);
        f.switch_to_block(c);
        let r = f.iconst(Ty::U64, 3000);
        f.ret(vec![r]);
        f.switch_to_block(bad);
        let r = f.iconst(Ty::U64, 0xBAD);
        f.ret(vec![r]);
        f.build()
    };
    define_make(
        &mut m,
        "mixed_make",
        enum_ty(MIXED),
        &[
            mixed_a(0x11, 0x2233_4455),
            mixed_b(0x1122_3344_5566_7788),
            mixed_c(),
        ],
    );

    // reprc_get(p): X(v) -> v, Y(v) -> v + 1000.
    let reprc_get = {
        let sig = m.add_func_type(vec![Ty::Ptr], vec![Ty::U64]);
        let mut f = m.function("reprc_get", sig);
        let entry = f.create_block();
        let x = f.create_block();
        let y = f.create_block();
        let bad = f.create_block();
        let p = f.add_block_param(entry, Ty::Ptr);
        f.switch_to_block(entry);
        let v = f.load(enum_ty(REPRC), p);
        let t = f.extract_field(Ty::U32, v, 0);
        f.switch(t, vec![case(0, x), case(1, y)], bad, vec![]);
        f.switch_to_block(x);
        let payload = f.extract_field(Ty::U8, v, 1);
        let wide = f.zext(Ty::U8, Ty::U64, payload);
        f.ret(vec![wide]);
        f.switch_to_block(y);
        let payload = f.extract_field(Ty::U8, v, 1);
        let wide = f.zext(Ty::U8, Ty::U64, payload);
        let thousand = f.iconst(Ty::U64, 1000);
        let sum = f.add(Ty::U64, wide, thousand);
        f.ret(vec![sum]);
        f.switch_to_block(bad);
        let r = f.iconst(Ty::U64, 0xBAD);
        f.ret(vec![r]);
        f.build()
    };
    define_make(
        &mut m,
        "reprc_make",
        enum_ty(REPRC),
        &[reprc_const(0, 0x2A), reprc_const(1, 0x2B)],
    );

    // small_get(p): A(x, y) -> x + y (x at byte 2, y at byte 1), B(v) -> v + 500.
    let small_get = {
        let sig = m.add_func_type(vec![Ty::Ptr], vec![Ty::U64]);
        let mut f = m.function("small_get", sig);
        let entry = f.create_block();
        let a = f.create_block();
        let b = f.create_block();
        let bad = f.create_block();
        let p = f.add_block_param(entry, Ty::Ptr);
        f.switch_to_block(entry);
        let v = f.load(enum_ty(SMALL), p);
        let t = f.extract_field(Ty::U8, v, 0);
        f.switch(t, vec![case(0, a), case(1, b)], bad, vec![]);
        f.switch_to_block(a);
        let x = f.extract_field(Ty::U16, v, 1);
        let y = f.extract_field(Ty::U8, v, 2);
        let wx = f.zext(Ty::U16, Ty::U64, x);
        let wy = f.zext(Ty::U8, Ty::U64, y);
        let sum = f.add(Ty::U64, wx, wy);
        f.ret(vec![sum]);
        f.switch_to_block(b);
        let payload = f.extract_field(Ty::U8, v, 1);
        let wide = f.zext(Ty::U8, Ty::U64, payload);
        let five_hundred = f.iconst(Ty::U64, 500);
        let sum = f.add(Ty::U64, wide, five_hundred);
        f.ret(vec![sum]);
        f.switch_to_block(bad);
        let r = f.iconst(Ty::U64, 0xBAD);
        f.ret(vec![r]);
        f.build()
    };
    define_make(
        &mut m,
        "small_make",
        enum_ty(SMALL),
        &[small_a(0x1234, 0x56), small_b(0x78)],
    );

    // slot_ptr(p) = the Fn payload of *p.
    {
        let sig = m.add_func_type(vec![Ty::Ptr], vec![Ty::Ptr]);
        let mut f = m.function("slot_ptr", sig);
        let entry = f.create_block();
        let p = f.add_block_param(entry, Ty::Ptr);
        f.switch_to_block(entry);
        let v = f.load(enum_ty(SLOT), p);
        let fp = f.extract_field(Ty::Ptr, v, 1);
        f.ret(vec![fp]);
        f.build();
    }

    // rec_sum(p) = a + b of the record at p.
    let rec_sum = {
        let sig = m.add_func_type(vec![Ty::Ptr], vec![Ty::U64]);
        let mut f = m.function("rec_sum", sig);
        let entry = f.create_block();
        let p = f.add_block_param(entry, Ty::Ptr);
        f.switch_to_block(entry);
        let v = f.load(rec_ty.clone(), p);
        let a = f.extract_field(Ty::U16, v, 0);
        let b = f.extract_field(Ty::U64, v, 1);
        let wa = f.zext(Ty::U16, Ty::U64, a);
        let sum = f.add(Ty::U64, wa, b);
        f.ret(vec![sum]);
        f.build()
    };
    // bytes_sum(p) = tag + trailing byte of the Bytes3 at p.
    let bytes_sum = {
        let sig = m.add_func_type(vec![Ty::Ptr], vec![Ty::U64]);
        let mut f = m.function("bytes_sum", sig);
        let entry = f.create_block();
        let p = f.add_block_param(entry, Ty::Ptr);
        f.switch_to_block(entry);
        let v = f.load(enum_ty(BYTES3), p);
        let t = f.extract_field(Ty::U8, v, 0);
        let tail = f.extract_field(Ty::U8, v, 2);
        let wt = f.zext(Ty::U8, Ty::U64, t);
        let wtail = f.zext(Ty::U8, Ty::U64, tail);
        let sum = f.add(Ty::U64, wt, wtail);
        f.ret(vec![sum]);
        f.build()
    };

    // The zero-argument oracle functions.
    let ord = enum_ty(ORDERING);
    define_oracle_call(
        &mut m,
        "o_ord_less",
        ord.clone(),
        ordering_const(-1),
        ord_classify,
        Ty::U64,
    );
    define_oracle_call(
        &mut m,
        "o_ord_equal",
        ord.clone(),
        ordering_const(0),
        ord_classify,
        Ty::U64,
    );
    define_oracle_call(
        &mut m,
        "o_ord_greater",
        ord.clone(),
        ordering_const(1),
        ord_classify,
        Ty::U64,
    );
    define_oracle_call(
        &mut m,
        "o_ord_sext",
        ord.clone(),
        ordering_const(-1),
        ord_disc,
        Ty::I64,
    );
    define_oracle_call(
        &mut m,
        "o_ord_is_less",
        ord.clone(),
        ordering_const(-1),
        ord_is_less,
        Ty::U64,
    );
    define_oracle_call(
        &mut m,
        "o_ord_is_not_less",
        ord,
        ordering_const(1),
        ord_is_less,
        Ty::U64,
    );
    let mixed_ty = enum_ty(MIXED);
    define_oracle_call(
        &mut m,
        "o_mixed_a",
        mixed_ty.clone(),
        mixed_a(0x11, 0x2233_4455),
        mixed_sum,
        Ty::U64,
    );
    define_oracle_call(
        &mut m,
        "o_mixed_b",
        mixed_ty.clone(),
        mixed_b(0x1122_3344_5566_7788),
        mixed_sum,
        Ty::U64,
    );
    define_oracle_call(&mut m, "o_mixed_c", mixed_ty, mixed_c(), mixed_sum, Ty::U64);
    define_oracle_call(
        &mut m,
        "o_reprc_x",
        enum_ty(REPRC),
        reprc_const(0, 0x2A),
        reprc_get,
        Ty::U64,
    );
    define_oracle_call(
        &mut m,
        "o_reprc_y",
        enum_ty(REPRC),
        reprc_const(1, 0x2B),
        reprc_get,
        Ty::U64,
    );
    define_oracle_call(
        &mut m,
        "o_small_a",
        enum_ty(SMALL),
        small_a(0x1234, 0x56),
        small_get,
        Ty::U64,
    );
    define_oracle_call(
        &mut m,
        "o_small_b",
        enum_ty(SMALL),
        small_b(0x78),
        small_get,
        Ty::U64,
    );
    define_oracle_global(&mut m, "o_g_ord", G_ORD, ord_disc, Ty::I64);
    define_oracle_global(&mut m, "o_g_mixed", G_MIXED, mixed_sum, Ty::U64);
    define_oracle_global(&mut m, "o_g_rec", G_REC, rec_sum, Ty::U64);
    define_oracle_global(&mut m, "o_g_bytes", G_BYTES, bytes_sum, Ty::U64);
    m.build().expect("ModuleBuilder::build: test fixture")
}

const DRIVER_DECLS: &str = r#"
#include <stdint.h>
#include <stddef.h>
#include <stdio.h>
#include <string.h>

extern int64_t ord_disc(const void *);
extern uint64_t ord_classify(const void *);
extern uint64_t ord_is_less(const void *);
extern void ord_make(void *, uint8_t);
extern uint64_t mixed_disc(const void *);
extern uint64_t mixed_sum(const void *);
extern void mixed_make(void *, uint8_t);
extern uint64_t reprc_get(const void *);
extern void reprc_make(void *, uint8_t);
extern uint64_t small_get(const void *);
extern void small_make(void *, uint8_t);
extern const void *slot_ptr(const void *);
extern uint64_t rec_sum(const void *);
extern uint64_t bytes_sum(const void *);
extern const int8_t g_ord;
extern uint8_t g_mixed[16];
extern const uint8_t g_slot[16];
extern const uint8_t g_rec[16];
extern const uint8_t g_bytes[5];

static int checks = 0;
static int failures = 0;
#define CHECK(cond) do { checks++; if (!(cond)) { failures++; printf("FAIL line %d: %s\n", __LINE__, #cond); } } while (0)

/* rustc's layout of Mixed::A: tag@0, u8@1, u32@4. */
struct mixed_a { uint8_t tag; uint8_t x; uint8_t pad[2]; uint32_t y; uint64_t tail; };
/* rustc's layout of Mixed::B: tag@0, u64@8. */
struct mixed_b { uint8_t tag; uint8_t pad[7]; uint64_t v; };
/* #[repr(C)] enum ReprC { X(u8), Y(u8) }: an int tag, the payload at 4. */
struct reprc { uint32_t tag; uint8_t v; uint8_t pad[3]; };
/* rustc's layout of Small::A: tag@0, the u8 at 1, the u16 at 2 (reordered). */
struct small_a { uint8_t tag; uint8_t y; uint16_t x; };
/* rustc's layout of Small::B: tag@0, u8@1. */
struct small_b { uint8_t tag; uint8_t v; uint8_t pad[2]; };
/* The record { a: u16, b: u64 } at natural C. */
struct rec { uint16_t a; uint8_t pad[6]; uint64_t b; };
"#;

const DRIVER_MAIN: &str = r#"
int main(void) {
    int8_t less = -1, equal = 0, greater = 1;
    CHECK(ord_disc(&less) == -1);
    CHECK(ord_disc(&equal) == 0);
    CHECK(ord_disc(&greater) == 1);
    CHECK(ord_classify(&less) == 100);
    CHECK(ord_classify(&equal) == 200);
    CHECK(ord_classify(&greater) == 300);
    CHECK(ord_is_less(&less) == 1);
    CHECK(ord_is_less(&equal) == 0);
    CHECK(ord_is_less(&greater) == 0);
    int8_t made = 0x55;
    ord_make(&made, 0); CHECK(made == -1);
    ord_make(&made, 1); CHECK(made == 0);
    ord_make(&made, 2); CHECK(made == 1);

    CHECK(sizeof(struct mixed_a) == 16 && offsetof(struct mixed_a, x) == 1 && offsetof(struct mixed_a, y) == 4);
    CHECK(sizeof(struct mixed_b) == 16 && offsetof(struct mixed_b, v) == 8);
    struct mixed_a a; memset(&a, 0xEE, sizeof a); a.tag = 10; a.x = 0x11; a.y = 0x22334455u;
    CHECK(mixed_disc(&a) == 10);
    CHECK(mixed_sum(&a) == 0x11 + 0x22334455ull);
    struct mixed_b b; memset(&b, 0xEE, sizeof b); b.tag = 20; b.v = 0x1122334455667788ull;
    CHECK(mixed_disc(&b) == 20);
    CHECK(mixed_sum(&b) == 0x1122334455667788ull);
    uint8_t c[16]; memset(c, 0xEE, 16); c[0] = 30;
    CHECK(mixed_disc(c) == 30);
    CHECK(mixed_sum(c) == 3000);
    uint8_t img[16]; uint32_t y32; uint64_t v64; uint32_t tag32;
    memset(img, 0xEE, 16); mixed_make(img, 0);
    CHECK(img[0] == 10 && img[1] == 0x11);
    memcpy(&y32, img + 4, 4); CHECK(y32 == 0x22334455u);
    memset(img, 0xEE, 16); mixed_make(img, 1);
    CHECK(img[0] == 20);
    memcpy(&v64, img + 8, 8); CHECK(v64 == 0x1122334455667788ull);
    memset(img, 0xEE, 16); mixed_make(img, 2);
    CHECK(img[0] == 30);

    CHECK(sizeof(struct reprc) == 8 && offsetof(struct reprc, v) == 4);
    struct reprc x = { 0, 0x2A, {0, 0, 0} };
    struct reprc yv = { 1, 0x2B, {0, 0, 0} };
    CHECK(reprc_get(&x) == 0x2A);
    CHECK(reprc_get(&yv) == 0x2B + 1000);
    memset(img, 0xEE, 16); reprc_make(img, 0);
    memcpy(&tag32, img, 4); CHECK(tag32 == 0 && img[4] == 0x2A);
    memset(img, 0xEE, 16); reprc_make(img, 1);
    memcpy(&tag32, img, 4); CHECK(tag32 == 1 && img[4] == 0x2B);

    CHECK(sizeof(struct small_a) == 4 && offsetof(struct small_a, y) == 1 && offsetof(struct small_a, x) == 2);
    struct small_a sa = { 0, 0x56, 0x1234 };
    struct small_b sb = { 1, 0x78, {0, 0} };
    CHECK(small_get(&sa) == 0x1234 + 0x56);
    CHECK(small_get(&sb) == 0x78 + 500);
    memset(img, 0xEE, 16); small_make(img, 0);
    CHECK(img[0] == 0 && img[1] == 0x56 && img[2] == 0x34 && img[3] == 0x12 && img[4] == 0xEE);
    memset(img, 0xEE, 16); small_make(img, 1);
    CHECK(img[0] == 1 && img[1] == 0x78 && img[4] == 0xEE);

    /* Globals, read by C at the producer layout. */
    CHECK(g_ord == 1);
    CHECK(g_mixed[0] == 10 && g_mixed[1] == 0x5A);
    memcpy(&y32, g_mixed + 4, 4); CHECK(y32 == 0x11223344u);
    CHECK(g_slot[0] == 7);
    uintptr_t fp; memcpy(&fp, g_slot + 8, 8);
    CHECK(fp == (uintptr_t)&ord_disc);
    CHECK(slot_ptr(g_slot) == (const void *)&ord_disc);
    uint16_t ra; memcpy(&ra, g_rec, 2);
    uint64_t rb; memcpy(&rb, g_rec + 8, 8);
    CHECK(ra == 0x0A0B && rb == 0x0102030405060708ull);
    struct rec r; memset(&r, 0, sizeof r); r.a = 0x0A0B; r.b = 0x0102030405060708ull;
    CHECK(rec_sum(&r) == 0x0A0B + 0x0102030405060708ull);
    static const uint8_t want_bytes[5] = { 1, 0x00, 0xc3, 0xa9, 0xe7 };
    CHECK(memcmp(g_bytes, want_bytes, 5) == 0);
    CHECK(bytes_sum(g_bytes) == 1 + 0xe7);
    /* The C view and the compiled view of every global agree. */
    CHECK(mixed_sum(g_mixed) == 0x5A + 0x11223344ull);
    g_mixed[1] = 0x5B;
    CHECK(mixed_sum(g_mixed) == 0x5B + 0x11223344ull);
    g_mixed[1] = 0x5A; /* restore before the oracle functions read the global */
    CHECK(ord_disc(&g_ord) == 1);
"#;

const DRIVER_TAIL: &str = r#"
    if (failures) { printf("FAIL %d of %d direct-enum checks\n", failures, checks); return 1; }
    printf("PASS %d direct-enum checks\n", checks);
    return 0;
}
"#;

/// The complete driver: the declarations, the C checks, then one
/// `name=value` line per oracle function for the interpreter comparison.
pub fn driver() -> String {
    let mut text = String::from(DRIVER_DECLS);
    for (name, _) in ORACLE.iter().chain(NATIVE_ONLY) {
        text.push_str(&format!("extern uint64_t {name}(void);\n"));
    }
    text.push_str(DRIVER_MAIN);
    for (name, want) in NATIVE_ONLY {
        text.push_str(&format!("    CHECK({name}() == {want}ull);\n"));
    }
    for (name, _) in ORACLE {
        text.push_str(&format!(
            "    printf(\"{name}=%llu\\n\", (unsigned long long){name}());\n"
        ));
    }
    text.push_str(DRIVER_TAIL);
    text
}

/// The number of `CHECK`s in `DRIVER_MAIN` plus one per `NATIVE_ONLY` entry;
/// the driver's verdict pins it so a check that vanishes fails the run.
pub const EXPECTED_CHECKS: usize = 48 + NATIVE_ONLY.len();

/// The image a global's initializer must render to, independent of the
/// object format: the bytes at each lane the code reads (padding bytes are
/// unconstrained) and the one pointer-sized slot that must carry a
/// relocation against `ord_disc` (`g_slot`'s `Fn` payload).
pub struct GlobalImage {
    pub name: &'static str,
    pub size: u64,
    pub mutable: bool,
    pub lanes: &'static [(u64, &'static [u8])],
    pub symbol_slot: Option<u64>,
}

/// The corpus globals, in `GlobalId` order, at the producer layouts the C
/// driver spells (little-endian lanes).
pub const GLOBAL_IMAGES: &[GlobalImage] = &[
    GlobalImage {
        name: "g_ord",
        size: 1,
        mutable: false,
        lanes: &[(0, &[1])],
        symbol_slot: None,
    },
    GlobalImage {
        name: "g_mixed",
        size: 16,
        mutable: true,
        lanes: &[(0, &[10]), (1, &[0x5A]), (4, &[0x44, 0x33, 0x22, 0x11])],
        symbol_slot: None,
    },
    GlobalImage {
        name: "g_slot",
        size: 16,
        mutable: false,
        lanes: &[(0, &[7])],
        symbol_slot: Some(8),
    },
    GlobalImage {
        name: "g_rec",
        size: 16,
        mutable: false,
        lanes: &[(0, &[0x0B, 0x0A]), (8, &[8, 7, 6, 5, 4, 3, 2, 1])],
        symbol_slot: None,
    },
    GlobalImage {
        name: "g_bytes",
        size: 5,
        mutable: false,
        lanes: &[(0, &[1, 0x00, 0xc3, 0xa9, 0xe7])],
        symbol_slot: None,
    },
];

/// The pointer-taking helper functions, in definition order.
pub const HELPERS: &[&str] = &[
    "ord_disc",
    "ord_classify",
    "ord_is_less",
    "ord_make",
    "mixed_disc",
    "mixed_sum",
    "mixed_make",
    "reprc_get",
    "reprc_make",
    "small_get",
    "small_make",
    "slot_ptr",
    "rec_sum",
    "bytes_sum",
];

/// Every function the corpus defines, in definition order: the pointer-taking
/// helpers the driver calls directly, then the zero-argument oracle functions.
pub fn symbols() -> Vec<&'static str> {
    HELPERS
        .iter()
        .chain(ORACLE.iter().chain(NATIVE_ONLY).map(|(name, _)| name))
        .copied()
        .collect()
}

/// The reference interpreter's value of the zero-argument function `name`,
/// as the unsigned 64-bit pattern the driver prints.
pub fn interpret(module: &Module, name: &str) -> u64 {
    let function = module
        .functions
        .iter()
        .find(|f| f.name == name)
        .unwrap_or_else(|| panic!("no function {name}"));
    let outcome = Interpreter::with_module(module)
        .execute_function(function, std::iter::empty())
        .unwrap_or_else(|e| panic!("interpret {name}: {e:?}"));
    let [ret] = outcome.returns.as_slice() else {
        panic!("{name}: expected one result, got {:?}", outcome.returns)
    };
    let int = ret.as_int().expect("integer result");
    u64::try_from(int.as_unsigned() & u128::from(u64::MAX)).expect("u64 pattern")
}

/// A module whose one function loads and stores a value of `edef`'s type.
fn with_enum(triple: &str, name: &str, edef: EnumDef) -> Module {
    let mut m = ModuleBuilder::new_with_target_info(name, target(triple));
    let id = edef.id;
    m.add_enum(edef);
    let sig = m.add_func_type(vec![Ty::Ptr], vec![]);
    let mut f = m.function(name, sig);
    let entry = f.create_block();
    let p = f.add_block_param(entry, Ty::Ptr);
    f.switch_to_block(entry);
    let v = f.load(Ty::Enum(id), p);
    f.store(Ty::Enum(id), p, v);
    f.ret(vec![]);
    f.build();
    m.build().expect("ModuleBuilder::build: test fixture")
}

/// A module whose one function returns the address of `GlobalId(0)`.
fn with_global_addr(mut m: ModuleBuilder, name: &str) -> Module {
    let sig = m.add_func_type(vec![], vec![Ty::Ptr]);
    let mut f = m.function(name, sig);
    let entry = f.create_block();
    f.switch_to_block(entry);
    let p = f.global_addr(GlobalId::new(0));
    f.ret(vec![p]);
    f.build();
    m.build().expect("ModuleBuilder::build: test fixture")
}

/// What stays refused, as `(fixture, needle, module)`: the real compiler must
/// refuse each module with an error naming `needle`, on either object format.
/// A re-tag through `InsertField`, duplicate discriminants, a 128-bit tag
/// lane, a descriptor whose field overlaps its tag word, a niche-enum-typed
/// global, and a global initializer whose discriminant names no variant.
pub fn refusal_fixtures(triple: &str) -> Vec<(&'static str, &'static str, Module)> {
    // InsertField at element 0 re-tags the value.
    let mut m = ModuleBuilder::new_with_target_info("retag", target(triple));
    m.add_enum(ordering());
    {
        let sig = m.add_func_type(vec![Ty::Ptr], vec![]);
        let mut f = m.function("retag", sig);
        let entry = f.create_block();
        let p = f.add_block_param(entry, Ty::Ptr);
        f.switch_to_block(entry);
        let v = f.load(enum_ty(ORDERING), p);
        let one = f.iconst(Ty::I8, 1);
        let w = f.insert_field(enum_ty(ORDERING), v, 0, one);
        f.store(enum_ty(ORDERING), p, w);
        f.ret(vec![]);
        f.build();
    }
    let retag = m.build().expect("ModuleBuilder::build: test fixture");

    let mut duplicate = mixed();
    duplicate.discriminants = vec![Some(10), Some(10), Some(30)];
    let mut wide = mixed();
    wide.repr = Some(EnumTagRepr::I128);
    wide.layout = None;
    let mut overlapping = mixed();
    overlapping.layout = Some(direct(8, 16, 8, vec![vec![1, 4], vec![8], vec![]]));

    // A niche-enum-typed global has no renderer yet.
    let mut m = ModuleBuilder::new_with_target_info("niche_global", target(triple));
    m.add_enum(EnumDef {
        origin: None,
        id: EnumId::new(0),
        name: "OptionNonZero".into(),
        variants: vec![variant("None", vec![]), variant("Some", vec![Ty::U32])],
        discriminants: Vec::new(),
        repr: None,
        layout: Some(EnumLayoutDescriptor {
            encoding: EnumTagEncoding::Niche {
                untagged_variant: 1,
                niche_variants_start: 0,
                niche_variants_end: 0,
                niche_start: 0,
                niche_offset: 0,
                niche_ty: EnumTagRepr::U32,
            },
            size: 4,
            align: 4,
            variant_field_offsets: vec![vec![], vec![0]],
        }),
    });
    m.add_global(global(
        "g_niche",
        enum_ty(0),
        false,
        Constant::Aggregate(vec![Constant::Int(1), Constant::Int(5)]),
    ));
    let niche_global = with_global_addr(m, "niche_addr");

    // A global whose discriminant names no variant.
    let mut m = ModuleBuilder::new_with_target_info("wrong_disc", target(triple));
    m.add_enum(mixed());
    m.add_global(global(
        "g_wrong",
        enum_ty(MIXED),
        false,
        Constant::Aggregate(vec![Constant::Int(11), Constant::Int(1), Constant::Int(2)]),
    ));
    let wrong_disc = with_global_addr(m, "wrong_addr");

    vec![
        ("retag", "EnumTagWriteUnsupported", retag),
        // TrustIR's typed admission, which every compiler entry consumes
        // first, refuses these three before the adapter's own guards
        // (`EnumDef.discriminants`, `over the tag word`, the writer's `names
        // no variant`) are reached; each is pinned to TrustIR's exact text.
        (
            "duplicate",
            "TrustIrAdmissionRefused { error: \"enum.1 (Mixed): const type mismatch: expected \
             resolvable, duplicate-free discriminant assignment, got ill-formed discriminants\" }",
            with_enum(triple, "duplicate", duplicate),
        ),
        ("wide", "128-bit", with_enum(triple, "wide", wide)),
        (
            "overlapping",
            "TrustIrAdmissionRefused { error: \"enum.1 (Mixed) layout: const type mismatch: \
             expected a direct tag disjoint from every non-ZST field, got tag overlaps variant 1 \
             field 0\" }",
            with_enum(triple, "overlapping", overlapping),
        ),
        (
            "niche_global",
            "niche or untagged producer layout",
            niche_global,
        ),
        (
            "wrong_disc",
            "TrustIrAdmissionRefused { error: \"global 'g_wrong': const type mismatch: expected a \
             discriminant of enum Mixed, got 11\" }",
            wrong_disc,
        ),
    ]
}
