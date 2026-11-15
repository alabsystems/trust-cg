// niche_enum_codec.rs — the niche DISCRIMINANT codec, checked independently
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! The adapter's niche codec (`src/niche_codec.rs`) reads and
//! constructs the discriminant of a trust-ir niche-encoded `Ty::Enum`. These
//! tests check the LIR it emits, not the codec's own helpers:
//!
//! * a small evaluator in this file executes the emitted LIR over a byte
//!   memory, and
//! * an independent reference model, transcribed from trust-ir's interpreter
//!   (`interpret.rs`, `EnumByteView::Niche` in `encode_value`/`decode_value`),
//!   states what the answer must be.
//!
//! Every 8-bit and 16-bit lane value is decoded exhaustively; 32- and 64-bit
//! lanes use their boundary values plus a fixed pseudo-random sample. The
//! shapes are the layouts rustc gives `Option<&u64>`, `Option<NonZeroU32>`,
//! `Option<bool>`, `Option<char>`, a three-variant `enum { Data(bool), Low,
//! High }`, trust-ir's own wrapping `Wrapped` fixture (the untagged variant
//! inside the niche interval, reserved values wrapping past 255), a lane
//! inside a struct, a lane inside a nested niche enum, a lane on a nested
//! Direct enum's tag, a 16-bit lane, a signed lane repr, a high 64-bit
//! `niche_start`, non-index discriminants (one set with a negative untagged
//! discriminant) and a lane on an interior array element. The refusal rows
//! are malformed descriptors the codec must decline with a `[TCG-NICHE-ENUM]`
//! diagnostic, plus one row showing a declined codec leaves payload-only
//! access admitted, and untagged constants whose lane element holds a reserved
//! value.
//!
//! This is model evidence for the adapter's LIR. Native execution against a C
//! oracle covers six of these shapes (`Option<&u64>`, `Option<NonZeroU32>`,
//! `Option<bool>`, `Option<char>`, `Tri` and `Wrapped`) in
//! `trust-cg-codegen/tests/e2e_aarch64_niche_enum.rs`; the others are
//! model-only.

use std::collections::{BTreeMap, HashMap};

use trust_cg_lower::adapter::AdapterError;
use trust_cg_lower::declared_tuple_layout::TupleLayoutComponent;
use trust_cg_lower::instructions::{Instruction, IntCC, Opcode, Value};
use trust_cg_lower::types::Type;
use trust_ir::ty::{EnumLayoutDescriptor, EnumTagEncoding, EnumTagRepr};
use trust_ir::{
    Block as TrustIrBlock, BlockId, Constant, EnumDef, EnumId, EnumVariant, FatPtrKind, FieldDef,
    FuncId, FuncTy, FuncTyId, Function as TrustIrFunction, Global, Inst, InstrNode, Linkage,
    Module as TrustIrModule, StructDef, StructId, StructRepr, Ty, TyId, ValueId, Visibility,
};

#[path = "common/typed_refusal.rs"]
mod typed_refusal;
use typed_refusal::{assert_typed_const_refusal, typed_const_refusal};

#[path = "common/below_admission.rs"]
mod below_admission;
use below_admission::body_refusal_below_admission;

// ---------------------------------------------------------------------------
// Independent reference model (trust-ir interpret.rs, EnumByteView::Niche)
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, Copy)]
struct Niche {
    untagged: u32,
    start: u32,
    end: u32,
    niche_start: u128,
    offset: u64,
    repr: EnumTagRepr,
}

impl Niche {
    fn bytes(&self) -> u64 {
        match self.repr {
            EnumTagRepr::U8 | EnumTagRepr::I8 => 1,
            EnumTagRepr::U16 | EnumTagRepr::I16 => 2,
            EnumTagRepr::U32 | EnumTagRepr::I32 => 4,
            EnumTagRepr::U64 | EnumTagRepr::I64 => 8,
            EnumTagRepr::U128 | EnumTagRepr::I128 => 16,
        }
    }

    fn mask(&self) -> u128 {
        u128::MAX >> (128 - self.bytes() * 8)
    }

    /// `decode_value`: `Err` is the untagged variant's dead reserved value.
    fn decode(&self, lane: u128) -> Result<u32, ()> {
        let relative = lane.wrapping_sub(self.niche_start) & self.mask();
        let range_len = u128::from(self.end - self.start);
        if relative <= range_len {
            let candidate = self.start + relative as u32;
            if candidate == self.untagged {
                return Err(());
            }
            Ok(candidate)
        } else {
            Ok(self.untagged)
        }
    }

    /// `encode_value`: the lane bits of a niche-tagged variant.
    fn encode(&self, variant: u32) -> Option<u128> {
        (variant != self.untagged).then(|| {
            let relative = u128::from(variant).wrapping_sub(u128::from(self.start));
            self.niche_start.wrapping_add(relative) & self.mask()
        })
    }

    fn encoding(&self) -> EnumTagEncoding {
        EnumTagEncoding::Niche {
            untagged_variant: self.untagged,
            niche_variants_start: self.start,
            niche_variants_end: self.end,
            niche_start: self.niche_start,
            niche_offset: self.offset,
            niche_ty: self.repr,
        }
    }
}

// ---------------------------------------------------------------------------
// Minimal evaluator for the straight-line LIR the codec emits
// ---------------------------------------------------------------------------

const BASE: u64 = 0x1_0000;
const SLOT_BASE: u64 = 0x10_0000;

fn width(ty: &Type) -> u64 {
    match ty {
        Type::I8 | Type::B1 => 1,
        Type::I16 => 2,
        Type::I32 => 4,
        Type::I64 => 8,
        other => panic!("the evaluator models integer scalars only, got {other:?}"),
    }
}

fn wmask(bytes: u64) -> u64 {
    if bytes == 8 {
        u64::MAX
    } else {
        (1u64 << (bytes * 8)) - 1
    }
}

#[derive(Default)]
struct Machine {
    mem: BTreeMap<u64, u8>,
    vals: HashMap<Value, u64>,
}

impl Machine {
    fn read(&self, addr: u64, bytes: u64) -> u64 {
        (0..bytes).fold(0u64, |acc, i| {
            let byte = *self
                .mem
                .get(&(addr + i))
                .unwrap_or_else(|| panic!("read of uninitialised byte {:#x}", addr + i));
            acc | (u64::from(byte) << (8 * i))
        })
    }

    fn write(&mut self, addr: u64, bytes: u64, value: u64) {
        for i in 0..bytes {
            self.mem.insert(addr + i, (value >> (8 * i)) as u8);
        }
    }

    fn get(&self, v: Value) -> u64 {
        *self
            .vals
            .get(&v)
            .unwrap_or_else(|| panic!("value {v:?} used before definition"))
    }

    /// Run `instrs`; return the `Return`'s first argument, if any.
    fn run(&mut self, instrs: &[Instruction]) -> Option<u64> {
        for inst in instrs {
            let arg = |m: &Machine, i: usize| m.get(inst.args[i]);
            let out = match &inst.opcode {
                Opcode::Iconst { ty, imm } => Some(*imm as u64 & wmask(width(ty))),
                Opcode::Copy => Some(arg(self, 0)),
                Opcode::Iadd => Some(arg(self, 0).wrapping_add(arg(self, 1))),
                Opcode::Isub => Some(arg(self, 0).wrapping_sub(arg(self, 1))),
                Opcode::Band => Some(arg(self, 0) & arg(self, 1)),
                Opcode::Uextend { from_ty, .. } => Some(arg(self, 0) & wmask(width(from_ty))),
                Opcode::Sextend { from_ty, .. } => {
                    let bits = width(from_ty) * 8;
                    let shift = 64 - bits;
                    Some((((arg(self, 0) << shift) as i64) >> shift) as u64)
                }
                Opcode::Trunc { to_ty } => Some(arg(self, 0) & wmask(width(to_ty))),
                Opcode::Icmp { cond } => {
                    let (a, b) = (arg(self, 0), arg(self, 1));
                    let (sa, sb) = (a as i64, b as i64);
                    Some(u64::from(match cond {
                        IntCC::Equal => a == b,
                        IntCC::NotEqual => a != b,
                        IntCC::UnsignedLessThan => a < b,
                        IntCC::UnsignedLessThanOrEqual => a <= b,
                        IntCC::UnsignedGreaterThan => a > b,
                        IntCC::UnsignedGreaterThanOrEqual => a >= b,
                        IntCC::SignedLessThan => sa < sb,
                        IntCC::SignedLessThanOrEqual => sa <= sb,
                        IntCC::SignedGreaterThan => sa > sb,
                        IntCC::SignedGreaterThanOrEqual => sa >= sb,
                    }))
                }
                Opcode::Select {
                    cond: IntCC::NotEqual,
                } => Some(if arg(self, 0) != 0 {
                    arg(self, 1)
                } else {
                    arg(self, 2)
                }),
                Opcode::Load { ty, .. } => Some(self.read(arg(self, 0), width(ty))),
                Opcode::Store { ty, .. } => {
                    let (value, addr) = (arg(self, 0), arg(self, 1));
                    self.write(addr, width(ty), value);
                    None
                }
                Opcode::StackAddr { slot } => Some(SLOT_BASE + u64::from(*slot) * 0x1000),
                Opcode::StructGep {
                    struct_ty,
                    field_index,
                } => Some(
                    arg(self, 0)
                        + u64::from(
                            struct_ty
                                .offset_of(*field_index as usize)
                                .expect("StructGep names a field"),
                        ),
                ),
                Opcode::ArrayGep { elem_ty } => {
                    Some(arg(self, 0) + arg(self, 1) * u64::from(elem_ty.bytes()))
                }
                Opcode::Return => return inst.args.first().map(|v| self.get(*v)),
                other => panic!("the evaluator does not model {other:?}"),
            };
            if let (Some(value), Some(result)) = (out, inst.results.first()) {
                self.vals.insert(*result, value);
            }
        }
        None
    }
}

// ---------------------------------------------------------------------------
// Fixtures
// ---------------------------------------------------------------------------

fn v(n: u32) -> ValueId {
    ValueId::new(n)
}

fn variant(name: &str, fields: Vec<Ty>) -> EnumVariant {
    EnumVariant {
        name: name.to_string(),
        fields,
        field_names: Vec::new(),
    }
}

const E: u32 = 0;

fn enum_ty() -> Ty {
    Ty::Enum(EnumId::new(E))
}

fn niche_enum(
    name: &str,
    variants: Vec<EnumVariant>,
    niche: Niche,
    size: u64,
    align: u64,
    offsets: Vec<Vec<u64>>,
) -> EnumDef {
    EnumDef {
        origin: None,
        id: EnumId::new(E),
        name: name.to_string(),
        variants,
        discriminants: Vec::new(),
        repr: None,
        layout: Some(EnumLayoutDescriptor {
            encoding: niche.encoding(),
            size,
            align,
            variant_field_offsets: offsets,
        }),
    }
}

/// A shape under test: its module tables, its niche, and a VALID untagged
/// payload constant (one that does not occupy a reserved value).
#[derive(Clone)]
struct Shape {
    name: &'static str,
    structs: Vec<StructDef>,
    /// The module type table (`Ty::Array` element types).
    types: Vec<Ty>,
    enums: Vec<EnumDef>,
    niche: Niche,
    /// trust-ir type of element 0 (the canonical tag type).
    tag_ty: Ty,
    /// Every variant's discriminant, by index.
    discs: Vec<i128>,
    /// The field constants each variant is constructed with; the untagged
    /// variant's is a VALID payload (one that occupies no reserved value).
    variant_fields: Vec<Vec<Constant>>,
    /// The bytes the untagged payload writes, at the enum's own offsets.
    payload_image: Vec<(u64, u8)>,
}

fn option_of(name: &'static str, payload: Ty, niche: Niche, size: u64, align: u64) -> EnumDef {
    niche_enum(
        name,
        vec![variant("None", vec![]), variant("Some", vec![payload])],
        niche,
        size,
        align,
        vec![vec![], vec![0]],
    )
}

fn le(value: u64, bytes: u64, at: u64) -> Vec<(u64, u8)> {
    (0..bytes)
        .map(|i| (at + i, (value >> (8 * i)) as u8))
        .collect()
}

fn option_ref() -> Shape {
    let niche = Niche {
        untagged: 1,
        start: 0,
        end: 0,
        niche_start: 0,
        offset: 0,
        repr: EnumTagRepr::U64,
    };
    Shape {
        name: "Option<&u64>",
        structs: vec![],
        types: vec![],
        enums: vec![option_of(
            "OptionRefU64",
            Ty::Ref(Box::new(Ty::U64)),
            niche,
            8,
            8,
        )],
        niche,
        tag_ty: Ty::U8,
        discs: vec![0, 1],
        // `Some(&TARGET)`: a `&u64` constant's one spelling is the address of
        // an immutable `u64` global; no image is checked (see
        // `holds_symbol_address`).
        variant_fields: vec![vec![], vec![symbol_address()]],
        payload_image: vec![],
    }
}

fn non_zero_u32_struct() -> StructDef {
    StructDef {
        origin: None,
        id: StructId::new(0),
        name: "NonZeroU32".to_string(),
        fields: vec![FieldDef {
            name: "0".to_string(),
            ty: Ty::U32,
            offset: Some(0),
        }],
        size: Some(4),
        align: Some(4),
        repr: StructRepr::Transparent,
    }
}

fn option_non_zero_u32() -> Shape {
    let niche = Niche {
        untagged: 1,
        start: 0,
        end: 0,
        niche_start: 0,
        offset: 0,
        repr: EnumTagRepr::U32,
    };
    Shape {
        name: "Option<NonZeroU32>",
        structs: vec![non_zero_u32_struct()],
        types: vec![],
        enums: vec![option_of(
            "OptionNonZeroU32",
            Ty::Struct(StructId::new(0)),
            niche,
            4,
            4,
        )],
        niche,
        tag_ty: Ty::U8,
        discs: vec![0, 1],
        variant_fields: vec![
            vec![],
            vec![Constant::Aggregate(vec![Constant::Int(0xDEAD_BEEF)])],
        ],
        payload_image: le(0xDEAD_BEEF, 4, 0),
    }
}

fn option_bool() -> Shape {
    let niche = Niche {
        untagged: 1,
        start: 0,
        end: 0,
        niche_start: 2,
        offset: 0,
        repr: EnumTagRepr::U8,
    };
    Shape {
        name: "Option<bool>",
        structs: vec![],
        types: vec![],
        enums: vec![option_of("OptionBool", Ty::Bool, niche, 1, 1)],
        niche,
        tag_ty: Ty::U8,
        discs: vec![0, 1],
        variant_fields: vec![vec![], vec![Constant::Bool(true)]],
        payload_image: vec![(0, 1)],
    }
}

fn option_char() -> Shape {
    let niche = Niche {
        untagged: 1,
        start: 0,
        end: 0,
        niche_start: 0x11_0000,
        offset: 0,
        repr: EnumTagRepr::U32,
    };
    Shape {
        name: "Option<char>",
        structs: vec![],
        types: vec![],
        enums: vec![option_of("OptionChar", Ty::Char, niche, 4, 4)],
        niche,
        tag_ty: Ty::U8,
        discs: vec![0, 1],
        variant_fields: vec![vec![], vec![Constant::Int(0x1F600)]],
        payload_image: le(0x1F600, 4, 0),
    }
}

/// `enum Tri { Data(bool), Low, High }` — rustc's layout: size 1, the bool
/// at byte 0, `Low` = 2 and `High` = 3.
fn tri() -> Shape {
    let niche = Niche {
        untagged: 0,
        start: 1,
        end: 2,
        niche_start: 2,
        offset: 0,
        repr: EnumTagRepr::U8,
    };
    Shape {
        name: "Tri",
        structs: vec![],
        types: vec![],
        enums: vec![niche_enum(
            "Tri",
            vec![
                variant("Data", vec![Ty::Bool]),
                variant("Low", vec![]),
                variant("High", vec![]),
            ],
            niche,
            1,
            1,
            vec![vec![0], vec![], vec![]],
        )],
        niche,
        tag_ty: Ty::U8,
        discs: vec![0, 1, 2],
        variant_fields: vec![vec![Constant::Bool(false)], vec![], vec![]],
        payload_image: vec![(0, 0)],
    }
}

/// trust-ir's own interpreter fixture: `Low` = 254, `Data`'s reserved 255 is
/// dead, `High` WRAPS to 0.
fn wrapped() -> Shape {
    let niche = Niche {
        untagged: 1,
        start: 0,
        end: 2,
        niche_start: 254,
        offset: 0,
        repr: EnumTagRepr::U8,
    };
    Shape {
        name: "Wrapped",
        structs: vec![],
        types: vec![],
        enums: vec![niche_enum(
            "Wrapped",
            vec![
                variant("Low", vec![]),
                variant("Data", vec![Ty::U8]),
                variant("High", vec![]),
            ],
            niche,
            1,
            1,
            vec![vec![], vec![0], vec![]],
        )],
        niche,
        tag_ty: Ty::U8,
        discs: vec![0, 1, 2],
        variant_fields: vec![vec![], vec![Constant::Int(42)], vec![]],
        payload_image: vec![(0, 42)],
    }
}

/// `struct Pair { a: u32, b: &u64 }` at declared offsets 0 and 8, 16/8.
fn pair_struct() -> StructDef {
    StructDef {
        origin: None,
        id: StructId::new(0),
        name: "Pair".to_string(),
        fields: vec![
            FieldDef {
                name: "a".to_string(),
                ty: Ty::U32,
                offset: Some(0),
            },
            FieldDef {
                name: "b".to_string(),
                ty: Ty::Ref(Box::new(Ty::U64)),
                offset: Some(8),
            },
        ],
        size: Some(16),
        align: Some(8),
        repr: StructRepr::Rust,
    }
}

/// `Option<Pair>`: the reference lives at byte 8, so the lane is an interior
/// leaf of the payload. (A TUPLE payload cannot reach the codec: TrustIR has
/// layout evidence for a tuple only from a declared tuple layout, which this
/// backend refuses wholesale; the struct carries the same interior lane.)
fn option_struct_lane() -> Shape {
    let niche = Niche {
        untagged: 1,
        start: 0,
        end: 0,
        niche_start: 0,
        offset: 8,
        repr: EnumTagRepr::U64,
    };
    Shape {
        name: "Option<Pair { u32, &u64 }>",
        structs: vec![pair_struct()],
        types: vec![],
        enums: vec![option_of(
            "OptionPair",
            Ty::Struct(StructId::new(0)),
            niche,
            16,
            8,
        )],
        niche,
        tag_ty: Ty::U8,
        discs: vec![0, 1],
        variant_fields: vec![
            vec![],
            vec![Constant::Aggregate(vec![
                Constant::Int(7),
                symbol_address(),
            ])],
        ],
        payload_image: vec![],
    }
}

/// `Option<Option<bool>>`: the outer lane IS the inner enum's lane, whose
/// valid values are the bool's 0..=1 plus the inner `None` = 2, so the outer
/// `None` is 3.
fn option_option_bool() -> Shape {
    let inner_niche = Niche {
        untagged: 1,
        start: 0,
        end: 0,
        niche_start: 2,
        offset: 0,
        repr: EnumTagRepr::U8,
    };
    let mut inner = option_of("OptionBool", Ty::Bool, inner_niche, 1, 1);
    inner.id = EnumId::new(1);
    let niche = Niche {
        niche_start: 3,
        ..inner_niche
    };
    Shape {
        name: "Option<Option<bool>>",
        structs: vec![],
        types: vec![],
        enums: vec![
            option_of("OptionOptionBool", Ty::Enum(EnumId::new(1)), niche, 1, 1),
            inner,
        ],
        niche,
        tag_ty: Ty::U8,
        discs: vec![0, 1],
        // Some(None): the inner enum's reserved value 2 is a VALID outer payload.
        variant_fields: vec![vec![], vec![Constant::Aggregate(vec![Constant::Int(0)])]],
        payload_image: vec![(0, 2)],
    }
}

/// `Option<Color>` over a Direct `enum Color { R, G, B }`: the lane is the
/// Direct tag word, whose valid values are 0..=2.
fn option_direct() -> Shape {
    let niche = Niche {
        untagged: 1,
        start: 0,
        end: 0,
        niche_start: 3,
        offset: 0,
        repr: EnumTagRepr::U8,
    };
    let color = EnumDef {
        origin: None,
        id: EnumId::new(1),
        name: "Color".to_string(),
        variants: vec![
            variant("R", vec![]),
            variant("G", vec![]),
            variant("B", vec![]),
        ],
        discriminants: Vec::new(),
        repr: None,
        layout: Some(EnumLayoutDescriptor {
            encoding: EnumTagEncoding::Direct { tag_offset: 0 },
            size: 1,
            align: 1,
            variant_field_offsets: vec![vec![], vec![], vec![]],
        }),
    };
    Shape {
        name: "Option<Color>",
        structs: vec![],
        types: vec![],
        enums: vec![
            option_of("OptionColor", Ty::Enum(EnumId::new(1)), niche, 1, 1),
            color,
        ],
        niche,
        tag_ty: Ty::U8,
        discs: vec![0, 1],
        variant_fields: vec![vec![], vec![Constant::Aggregate(vec![Constant::Int(2)])]],
        payload_image: vec![(0, 2)],
    }
}

fn option_u16_lane() -> Shape {
    let niche = Niche {
        untagged: 1,
        start: 0,
        end: 0,
        niche_start: 0,
        offset: 0,
        repr: EnumTagRepr::U16,
    };
    Shape {
        name: "Option<NonZeroU16>",
        structs: vec![],
        types: vec![],
        enums: vec![option_of("OptionNonZeroU16", Ty::U16, niche, 2, 2)],
        niche,
        tag_ty: Ty::U8,
        discs: vec![0, 1],
        variant_fields: vec![vec![], vec![Constant::Int(0xABCD)]],
        payload_image: le(0xABCD, 2, 0),
    }
}

/// A signed lane repr: the niche arithmetic is modular, so an `i32` lane with
/// a negative-looking `niche_start` bit pattern decodes the same way.
fn option_signed_lane() -> Shape {
    let niche = Niche {
        untagged: 1,
        start: 0,
        end: 0,
        niche_start: 0x8000_0000,
        offset: 0,
        repr: EnumTagRepr::I32,
    };
    Shape {
        name: "Option<i32 with MIN niche>",
        structs: vec![],
        types: vec![],
        enums: vec![option_of("OptionI32", Ty::I32, niche, 4, 4)],
        niche,
        tag_ty: Ty::U8,
        discs: vec![0, 1],
        variant_fields: vec![vec![], vec![Constant::Int(-5)]],
        payload_image: le((-5i64) as u64, 4, 0),
    }
}

/// `Option<Vec<_>>`-style capacity niche: a 64-bit lane with `niche_start`
/// above `i64::MAX`.
fn option_high_u64() -> Shape {
    let niche = Niche {
        untagged: 1,
        start: 0,
        end: 0,
        niche_start: 0x8000_0000_0000_0000,
        offset: 0,
        repr: EnumTagRepr::U64,
    };
    Shape {
        name: "Option<capacity>",
        structs: vec![],
        types: vec![],
        enums: vec![option_of("OptionCap", Ty::Usize, niche, 8, 8)],
        niche,
        tag_ty: Ty::U8,
        discs: vec![0, 1],
        variant_fields: vec![vec![], vec![Constant::Int(64)]],
        payload_image: le(64, 8, 0),
    }
}

/// Non-index discriminants with an `i8` repr hint: `None` = -3, `Some` = 11.
/// The niche arithmetic is over indices; element 0 carries discriminants.
fn option_explicit_discriminants() -> Shape {
    let mut shape = option_bool();
    shape.name = "Option<bool> with discriminants -3/11";
    shape.enums[0].discriminants = vec![Some(-3), Some(11)];
    shape.enums[0].repr = Some(EnumTagRepr::I8);
    shape.tag_ty = Ty::I8;
    shape.discs = vec![-3, 11];
    shape
}

/// `enum Tagged { Data(u8, NonZeroU32), Byte(u8), Empty }`, rustc's layout:
/// size 8, the u8 at byte 0 in both `Data` and `Byte`, the niche on `Data`'s
/// u32 at byte 4 (`Byte` = 0, `Empty` = 1). A niche-TAGGED variant with a
/// field of its own, written beside the lane.
fn tagged_with_fields() -> Shape {
    let niche = Niche {
        untagged: 0,
        start: 1,
        end: 2,
        niche_start: 0,
        offset: 4,
        repr: EnumTagRepr::U32,
    };
    let mut image = vec![(0, 0x33)];
    image.extend(le(0x7777, 4, 4));
    Shape {
        name: "Tagged",
        structs: vec![],
        types: vec![],
        enums: vec![niche_enum(
            "Tagged",
            vec![
                variant("Data", vec![Ty::U8, Ty::U32]),
                variant("Byte", vec![Ty::U8]),
                variant("Empty", vec![]),
            ],
            niche,
            8,
            4,
            vec![vec![0, 4], vec![0], vec![]],
        )],
        niche,
        tag_ty: Ty::U8,
        discs: vec![0, 1, 2],
        variant_fields: vec![
            vec![Constant::Int(0x33), Constant::Int(0x7777)],
            vec![Constant::Int(0x44)],
            vec![],
        ],
        payload_image: image,
    }
}

/// Non-index discriminants whose UNTAGGED one is negative: `None` = 5,
/// `Some` = -2, `i8` repr. A runtime write of -2 is the untagged variant only
/// when the narrow tag is SIGN-extended before it is compared with the
/// untagged discriminant; zero-extending it would store a reserved value over
/// the payload.
fn option_negative_untagged_discriminant() -> Shape {
    let mut shape = option_bool();
    shape.name = "Option<bool> with discriminants 5/-2";
    shape.enums[0].discriminants = vec![Some(5), Some(-2)];
    shape.enums[0].repr = Some(EnumTagRepr::I8);
    shape.tag_ty = Ty::I8;
    shape.discs = vec![5, -2];
    shape
}

/// `Option<[u8; 4]>` whose lane is array ELEMENT 2 (byte 2), `None` = 0; the
/// producer declares that byte never 0 in `Some`. The valid payload's element
/// 0 IS 0, so an untagged-constant check that inspected any element but the
/// lane's own would refuse it.
fn option_array_lane() -> Shape {
    let niche = Niche {
        untagged: 1,
        start: 0,
        end: 0,
        niche_start: 0,
        offset: 2,
        repr: EnumTagRepr::U8,
    };
    Shape {
        name: "Option<[u8; 4]> lane on element 2",
        structs: vec![],
        types: vec![Ty::U8],
        enums: vec![option_of(
            "OptionArrayLane",
            Ty::Array(TyId::new(0), 4),
            niche,
            4,
            1,
        )],
        niche,
        tag_ty: Ty::U8,
        discs: vec![0, 1],
        variant_fields: vec![vec![], vec![byte_array([0x00, 0x11, 0x22, 0x33])]],
        payload_image: vec![(0, 0x00), (1, 0x11), (2, 0x22), (3, 0x33)],
    }
}

fn byte_array(bytes: [u8; 4]) -> Constant {
    Constant::Array(
        bytes
            .iter()
            .map(|byte| Constant::Int(i128::from(*byte)))
            .collect(),
    )
}

fn byte_string(bytes: [u8; 4]) -> Constant {
    Constant::Bytes {
        data: bytes.to_vec(),
        utf8: false,
    }
}

fn all_shapes() -> Vec<Shape> {
    vec![
        option_ref(),
        option_non_zero_u32(),
        option_bool(),
        option_char(),
        tri(),
        wrapped(),
        option_struct_lane(),
        option_option_bool(),
        option_direct(),
        option_u16_lane(),
        option_signed_lane(),
        option_high_u64(),
        option_explicit_discriminants(),
        tagged_with_fields(),
        option_negative_untagged_discriminant(),
        option_array_lane(),
    ]
}

/// The immutable `u64` a reference payload points at.
const TARGET: &str = "NICHE_TARGET";

/// `&TARGET`: the one constant spelling of a `&u64` (TrustIR refuses an
/// integer at a reference type).
fn symbol_address() -> Constant {
    Constant::SymbolAddr {
        symbol: TARGET.to_string(),
        addend: 0,
    }
}

/// Whether a payload constant holds a symbol address. The codec cannot show a
/// relocated address is not a reserved lane value, so it refuses an untagged
/// constant whose lane is one ("does not determine the value") rather than
/// emit an image it cannot classify.
fn holds_symbol_address(constant: &Constant) -> bool {
    match constant {
        Constant::SymbolAddr { .. } => true,
        Constant::Aggregate(elems) | Constant::Array(elems) => {
            elems.iter().any(holds_symbol_address)
        }
        _ => false,
    }
}

fn target_global() -> Global {
    Global {
        name: TARGET.to_string(),
        ty: Ty::U64,
        mutable: false,
        initializer: Some(Constant::Int(0x55)),
        linkage: Linkage::Internal,
        tls: None,
        align: None,
        section: None,
        visibility: Visibility::Default,
        retained: false,
    }
}

fn module(
    shape: &Shape,
    params: Vec<(ValueId, Ty)>,
    returns: Vec<Ty>,
    body: Vec<InstrNode>,
) -> TrustIrModule {
    let mut module = TrustIrModule::new("niche_codec");
    module.structs = shape.structs.clone();
    module.types = shape.types.clone();
    module.enums = shape.enums.clone();
    module.globals = vec![target_global()];
    let fty = module
        .add_func_type(FuncTy {
            params: params.iter().map(|(_, t)| t.clone()).collect(),
            returns,
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut func = TrustIrFunction::new(FuncId::new(0), "k", fty, BlockId::new(0));
    func.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params,
        body,
    }];
    module
        .try_add_function(func)
        .expect("Module::try_add_function: test fixture");
    module
}

fn lower(module: &TrustIrModule) -> Result<Vec<Instruction>, String> {
    let func = module.functions.first().expect("one function");
    let (lir, _) =
        trust_cg_lower::translate_function_with_license(func, module, &permit_unlicensed())
            .map_err(|e| e.to_string())?;
    Ok(lir.blocks[&lir.entry_block].instructions.clone())
}

fn params_of(module: &TrustIrModule) -> Vec<Value> {
    let func = module.functions.first().expect("one function");
    let (lir, _) =
        trust_cg_lower::translate_function_with_license(func, module, &permit_unlicensed())
            .expect("lowers");
    lir.blocks[&lir.entry_block]
        .params
        .iter()
        .map(|(v, _)| *v)
        .collect()
}

fn tag_mask(tag_ty: &Ty) -> u64 {
    match tag_ty {
        Ty::U8 | Ty::I8 => 0xFF,
        Ty::U16 | Ty::I16 => 0xFFFF,
        Ty::U32 | Ty::I32 => 0xFFFF_FFFF,
        _ => u64::MAX,
    }
}

/// The lane values a width is checked at.
fn lane_samples(niche: &Niche) -> Vec<u128> {
    let mask = niche.mask();
    if niche.bytes() <= 2 {
        return (0..=mask).collect();
    }
    let mut samples = vec![0, 1, 2, mask, mask - 1, mask / 2, mask / 2 + 1];
    for delta in 0..4u128 {
        let span = u128::from(niche.end - niche.start);
        samples.push(niche.niche_start.wrapping_add(delta) & mask);
        samples.push(niche.niche_start.wrapping_sub(delta + 1) & mask);
        samples.push(niche.niche_start.wrapping_add(span + delta + 1) & mask);
    }
    let mut state = 0x9E37_79B9_7F4A_7C15u64;
    for _ in 0..512 {
        state = state
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        samples.push(u128::from(state) & mask);
    }
    samples
}

// ---------------------------------------------------------------------------
// DECODE: ExtractField element 0
// ---------------------------------------------------------------------------

fn decode_program(shape: &Shape) -> (Vec<Instruction>, Value) {
    let m = module(
        shape,
        vec![(v(0), enum_ty())],
        vec![shape.tag_ty.clone()],
        vec![
            InstrNode::new(Inst::ExtractField {
                ty: shape.tag_ty.clone(),
                aggregate: v(0),
                field: 0,
            })
            .with_result(v(1)),
            InstrNode::new(Inst::Return { values: vec![v(1)] }),
        ],
    );
    let instrs = lower(&m).unwrap_or_else(|e| panic!("{}: decode must lower: {e}", shape.name));
    (instrs, params_of(&m)[0])
}

#[test]
fn decode_agrees_with_the_reference_model_for_every_shape() {
    for shape in all_shapes() {
        let (instrs, param) = decode_program(&shape);
        let n = shape.niche;
        let mut checked = 0usize;
        for lane in lane_samples(&n) {
            let mut machine = Machine::default();
            machine.vals.insert(param, BASE);
            machine.write(BASE + n.offset, n.bytes(), lane as u64);
            // A narrow SIGNED tag is extended for the return ABI; compare the
            // tag's own width.
            let got =
                machine.run(&instrs).expect("returns the discriminant") & tag_mask(&shape.tag_ty);
            let variant = match n.decode(lane) {
                Ok(variant) => variant,
                // The dead reserved value of an untagged variant inside the
                // interval is not a trust-ir value; the emitted decode names
                // the untagged variant for it, as rustc's does.
                Err(()) => n.untagged,
            };
            let want = (shape.discs[variant as usize] as u64) & tag_mask(&shape.tag_ty);
            assert_eq!(
                got, want,
                "{}: lane {lane:#x} decodes to {got:#x}, reference says variant {variant} = \
                 {want:#x}",
                shape.name
            );
            checked += 1;
        }
        assert!(checked >= 256, "{}: only {checked} lane values", shape.name);
    }
}

/// The decode reads the lane at the DECLARED offset and nowhere else: every
/// shape's program touches exactly the lane bytes (the evaluator panics on any
/// other, uninitialised, byte).
#[test]
fn decode_reads_only_the_lane() {
    for shape in all_shapes() {
        let (instrs, param) = decode_program(&shape);
        let loads: Vec<_> = instrs
            .iter()
            .filter(|i| matches!(i.opcode, Opcode::Load { .. }))
            .collect();
        assert_eq!(loads.len(), 1, "{}: one lane load: {instrs:?}", shape.name);
        let mut machine = Machine::default();
        machine.vals.insert(param, BASE);
        machine.write(BASE + shape.niche.offset, shape.niche.bytes(), 0);
        machine.run(&instrs);
    }
}

#[test]
fn a_single_niche_variant_is_one_equality_and_a_range_is_one_unsigned_compare() {
    let (single, _) = decode_program(&option_bool());
    assert!(
        single
            .iter()
            .any(|i| matches!(i.opcode, Opcode::Icmp { cond: IntCC::Equal }))
    );
    let (range, _) = decode_program(&tri());
    assert!(range.iter().any(|i| matches!(
        i.opcode,
        Opcode::Icmp {
            cond: IntCC::UnsignedLessThanOrEqual
        }
    )));
    assert!(
        range.iter().any(|i| matches!(i.opcode, Opcode::Band)),
        "an 8-bit lane wraps at 8 bits: {range:?}"
    );
}

// ---------------------------------------------------------------------------
// ENCODE: Constant::Aggregate construction
// ---------------------------------------------------------------------------

/// `k` materializes `value` at the shape's enum type and returns nothing.
fn constant_module(shape: &Shape, value: Constant) -> TrustIrModule {
    module(
        shape,
        vec![],
        vec![],
        vec![
            InstrNode::new(Inst::Const {
                ty: enum_ty(),
                value,
            })
            .with_result(v(0)),
            InstrNode::new(Inst::Return { values: vec![] }),
        ],
    )
}

fn construct(shape: &Shape, value: Constant) -> Result<BTreeMap<u64, u8>, String> {
    image(&constant_module(shape, value))
}

/// The bytes `module`'s `k` writes, by offset into its stack slot.
fn image(module: &TrustIrModule) -> Result<BTreeMap<u64, u8>, String> {
    let instrs = lower(module)?;
    let mut machine = Machine::default();
    machine.run(&instrs);
    Ok(machine
        .mem
        .iter()
        .map(|(addr, byte)| (addr - SLOT_BASE, *byte))
        .collect())
}

/// An untagged constant whose lane is a symbol address is refused by the
/// codec, by name: the address is fixed only at link time, so the constant
/// does not show the lane avoids the reserved values.
fn assert_reference_lane_refused(shape: &Shape, result: Result<BTreeMap<u64, u8>, String>) {
    let err = result.expect_err("a symbol-address lane cannot be classified");
    assert!(
        err.contains("[TCG-NICHE-ENUM]")
            && err.contains("does not determine the value its payload puts in the niche lane"),
        "{}: {err}",
        shape.name
    );
}

#[test]
fn constants_write_the_reserved_value_or_the_payload() {
    for shape in all_shapes() {
        let n = shape.niche;
        for (index, disc) in shape.discs.iter().enumerate() {
            let mut elems = vec![Constant::Int(*disc)];
            elems.extend(shape.variant_fields[index].clone());
            let index = index as u32;
            if shape.variant_fields[index as usize]
                .iter()
                .any(holds_symbol_address)
            {
                assert_reference_lane_refused(
                    &shape,
                    construct(&shape, Constant::Aggregate(elems)),
                );
                continue;
            }
            let image = construct(&shape, Constant::Aggregate(elems))
                .unwrap_or_else(|e| panic!("{} variant {index}: {e}", shape.name));
            match n.encode(index) {
                Some(reserved) => {
                    let lane: Vec<u8> = (0..n.bytes()).map(|i| image[&(n.offset + i)]).collect();
                    assert_eq!(
                        lane,
                        (reserved as u64).to_le_bytes()[..n.bytes() as usize].to_vec(),
                        "{} variant {index}: the lane must hold reserved value {reserved:#x}",
                        shape.name
                    );
                }
                None => {
                    for (addr, byte) in &shape.payload_image {
                        assert_eq!(
                            image.get(addr),
                            Some(byte),
                            "{} untagged: payload byte {addr}",
                            shape.name
                        );
                    }
                }
            }
        }
    }
}

/// Construct every variant, then decode the image: the round trip returns the
/// discriminant the constant named.
#[test]
fn constants_round_trip_through_the_decode() {
    for shape in all_shapes() {
        let (decode, param) = decode_program(&shape);
        for (index, disc) in shape.discs.iter().enumerate() {
            let mut elems = vec![Constant::Int(*disc)];
            elems.extend(shape.variant_fields[index].clone());
            if shape.variant_fields[index].iter().any(holds_symbol_address) {
                assert_reference_lane_refused(
                    &shape,
                    construct(&shape, Constant::Aggregate(elems)),
                );
                continue;
            }
            let image = construct(&shape, Constant::Aggregate(elems)).expect("constructs");
            let mut machine = Machine::default();
            for (addr, byte) in image {
                machine.mem.insert(BASE + addr, byte);
            }
            machine.vals.insert(param, BASE);
            assert_eq!(
                machine
                    .run(&decode)
                    .map(|got| got & tag_mask(&shape.tag_ty)),
                Some((*disc as u64) & tag_mask(&shape.tag_ty)),
                "{} variant {index}",
                shape.name
            );
        }
    }
}

/// The codec classifies a lane constant only when it is an integer, `bool` or
/// `u128` literal, so it refuses every untagged constant whose lane holds a
/// relocated address, not only a reference: a `SymbolAddr` at a `Ref`,
/// `PtrConst` (the raw-pointer lane of an `Option<NonNull<T>>`) or bare `Ptr`
/// lane, an `FnDef` at a function-pointer lane (`Some(f)` as an
/// `Option<fn()>`), and the data word of a `&str` constant (`Some("abc")`).
/// TrustIR admits each one, and the niche-tagged `None` beside it still writes
/// its reserved value. Ruled in docs/decision-record.md,
/// OD-TYPED-ADMISSION-GAPS-20261010.
#[test]
fn every_relocated_address_lane_is_refused_not_only_a_reference() {
    let base = option_ref();
    let text = Global {
        name: "TEXT".to_string(),
        ty: Ty::Array(TyId::new(0), 3),
        mutable: false,
        initializer: Some(Constant::Bytes {
            data: b"abc".to_vec(),
            utf8: true,
        }),
        linkage: Linkage::Internal,
        tls: None,
        align: None,
        section: None,
        visibility: Visibility::Default,
        retained: false,
    };
    // `k`, the module's only function, has type `fn()`: function type 0.
    let lanes = [
        (
            "a `&u64` lane",
            Ty::Ref(Box::new(Ty::U64)),
            8,
            symbol_address(),
        ),
        (
            "a `*const u64` lane",
            Ty::PtrConst(Box::new(Ty::U64)),
            8,
            symbol_address(),
        ),
        ("a `ptr` lane", Ty::Ptr, 8, symbol_address()),
        (
            "a `fn()` lane",
            Ty::Func(FuncTyId::new(0)),
            8,
            Constant::FnDef(FuncId::new(0)),
        ),
        (
            "a `&str` data word",
            Ty::FatPtr(FatPtrKind::Str),
            16,
            Constant::Aggregate(vec![
                Constant::SymbolAddr {
                    symbol: "TEXT".to_string(),
                    addend: 0,
                },
                Constant::Int(3),
            ]),
        ),
    ];
    for (name, payload, size, value) in lanes {
        let mut shape = base.clone();
        shape.name = name;
        shape.types = vec![Ty::U8];
        shape.enums = vec![option_of("OptionRelocated", payload, base.niche, size, 8)];
        let build = |constant: Constant| {
            let mut module = constant_module(&shape, constant);
            module.globals.push(text.clone());
            let errors = trust_ir_build::validate_module(&module);
            assert!(errors.is_empty(), "{name}: TrustIR admits it: {errors:?}");
            module
        };
        let none = image(&build(Constant::Aggregate(vec![Constant::Int(0)])))
            .unwrap_or_else(|e| panic!("{name}: None lowers: {e}"));
        assert_eq!(
            none,
            le(0, 8, 0).into_iter().collect::<BTreeMap<_, _>>(),
            "{name}: None writes the reserved value 0 in the lane"
        );
        assert_reference_lane_refused(
            &shape,
            lower(&build(Constant::Aggregate(vec![Constant::Int(1), value])))
                .map(|_| BTreeMap::new()),
        );
    }
}

/// A niche or untagged enum whose payload is a TUPLE lowers only under a
/// declared tuple layout that EQUALS the declaration-order layout this
/// backend's byte path emits. TrustIR bounds a descriptor's fields by their
/// layout, and a tuple has layout evidence only from a declared tuple layout,
/// so the undeclared spelling is refused by TrustIR's floor. Since WS7.7 an
/// agreeing declared row is consumed, honoured by construction; a row that
/// differs is refused as `DeclaredTupleLayoutDisagrees`, never substituted.
/// This is the reversal OD-TYPED-ADMISSION-GAPS-20261010 (item 2) named: before
/// WS7.7 the declared spelling met `DeclaredTupleLayoutUnsupported`.
#[test]
fn a_tuple_payload_lowers_only_under_an_agreeing_declared_layout() {
    // `Option<(u32, bool)>`: the lane is the bool at byte 4, whose 2 is `None`.
    let niche = Niche {
        untagged: 1,
        start: 0,
        end: 0,
        niche_start: 2,
        offset: 4,
        repr: EnumTagRepr::U8,
    };
    let payload = Ty::Tuple(vec![Ty::U32, Ty::Bool]);
    let mut shape = option_bool();
    shape.enums = vec![option_of("OptionTuple", payload.clone(), niche, 8, 4)];
    let some = Constant::Aggregate(vec![
        Constant::Int(1),
        Constant::Aggregate(vec![Constant::Int(7), Constant::Bool(true)]),
    ]);

    let mut module = constant_module(&shape, some);
    let err = trust_cg_lower::translate_function_with_license(
        &module.functions[0],
        &module,
        &permit_unlicensed(),
    )
    .expect_err("an undeclared tuple payload has no layout to bound it");
    assert_eq!(
        err.to_string(),
        typed_const_refusal(
            "enum.0 (OptionTuple) layout",
            "variant 1 field 0 to have a resolvable layout (needed to bound it within size 8)",
            "offset 0, layout UNRESOLVABLE for type (u32, bool): tuple has no concrete memory \
             layout evidence",
        )
        .to_string()
    );

    module.target_info = Some(trust_ir::TargetInfo {
        triple: "aarch64-apple-darwin".into(),
        pointer_size: 8,
        endianness: trust_ir::Endianness::Little,
        abi: None,
        struct_passing: Default::default(),
    });
    let tuple_type = module
        .add_type(payload)
        .expect("Module::add_type: test fixture");
    module.tuple_layouts.push(trust_ir::TupleLayoutDescriptor {
        tuple_type,
        size: 8,
        align: 4,
        field_offsets: vec![0, 4],
    });
    let errors = trust_ir_build::validate_module(&module);
    assert!(
        errors.is_empty(),
        "TrustIR admits the declared layout: {errors:?}"
    );
    // WS7.7 is the reversal OD-TYPED-ADMISSION-GAPS-20261010 names: this row
    // EQUALS the declaration-order layout the byte path emits for (u32, bool)
    // (offsets 0 and 4, size 8, align 4), so it is consumed, not substituted,
    // and the constant lowers.
    let bytes = image(&module).expect("an agreeing declared tuple layout is consumed");
    assert_eq!(
        (0..5).map(|at| bytes.get(&at).copied()).collect::<Vec<_>>(),
        vec![Some(7), Some(0), Some(0), Some(0), Some(1)],
        "Some((7, true)): the u32 at byte 0, the bool lane at byte 4"
    );

    // The same payload under a valid but REORDERED declared layout (the bool
    // first) disagrees with the declaration-order layout and is refused by
    // name, at the first component that differs: this backend never
    // substitutes its own tuple layout for a declared one.
    //
    // Only the offsets move; the enum's niche lane stays at byte 4, which under
    // the reordered row is the u32's low byte, not the bool. That is deliberate:
    // with the lane at byte 0 the niche codec's own lane refusal would catch
    // the module first, while here ONLY the agreement check stands between the
    // module and a silent substitution (measured in review 2026-10-15: with the
    // `mutation-knobs` feature and `set_admit_disagreeing_tuple_layouts(true)`
    // this module lowers to the image {0: 7, 4: 1}). The `validate_module`
    // assertion below relies on TrustIR not checking niche lanes against the
    // tuple layout (true at pin cb6397762); if TrustIR starts refusing this
    // row, move the lane with the offsets and keep the agreement refusal.
    module.tuple_layouts[0].field_offsets = vec![4, 0];
    let errors = trust_ir_build::validate_module(&module);
    assert!(
        errors.is_empty(),
        "TrustIR admits the reordered layout, so the refusal is this backend's: {errors:?}"
    );
    let err = trust_cg_lower::translate_function_with_license(
        &module.functions[0],
        &module,
        &permit_unlicensed(),
    )
    .expect_err("a disagreeing declared layout is not substituted");
    assert!(
        matches!(
            err,
            AdapterError::DeclaredTupleLayoutDisagrees {
                field: TupleLayoutComponent::FieldOffset(0),
                declared: 4,
                emitted: 0,
                ..
            }
        ),
        "{err:?}"
    );
}

// ---------------------------------------------------------------------------
// REFUSAL: canonical InsertField cannot rewrite an enum discriminant
// ---------------------------------------------------------------------------

#[test]
fn runtime_discriminant_writes_are_refused_for_every_niche_shape() {
    for shape in all_shapes() {
        let m = module(
            &shape,
            vec![(v(0), enum_ty()), (v(1), shape.tag_ty.clone())],
            vec![],
            vec![
                InstrNode::new(Inst::InsertField {
                    ty: enum_ty(),
                    aggregate: v(0),
                    field: 0,
                    value: v(1),
                })
                .with_result(v(2)),
                InstrNode::new(Inst::Return { values: vec![] }),
            ],
        );
        let errors = trust_ir_build::validate_module(&m);
        assert!(errors.iter().any(|error| matches!(
            error,
            trust_ir_build::ValidationError::FieldAccessInvalid { op, reason, .. }
                if op.as_str() == "insert_field" && reason.contains("cannot rewrite an enum discriminant")
        )), "{}: {errors:?}", shape.name);
        let error = trust_cg_lower::translate_function_with_license(
            &m.functions[0],
            &m,
            &permit_unlicensed(),
        )
        .expect_err("canonical enum retagging is invalid for every encoding");
        assert!(
            matches!(error, AdapterError::EnumTagWriteUnsupported { .. }),
            "{}: {error}",
            shape.name
        );
    }
}

// ---------------------------------------------------------------------------
// REFUSALS
// ---------------------------------------------------------------------------

/// `k` reads element 0 (the discriminant) of its enum parameter and returns it.
fn decode_module(shape: &Shape) -> TrustIrModule {
    module(
        shape,
        vec![(v(0), enum_ty())],
        vec![shape.tag_ty.clone()],
        vec![
            InstrNode::new(Inst::ExtractField {
                ty: shape.tag_ty.clone(),
                aggregate: v(0),
                field: 0,
            })
            .with_result(v(1)),
            InstrNode::new(Inst::Return { values: vec![v(1)] }),
        ],
    )
}

/// The public entry's refusal of the decode program over `shape`.
fn decode_refusal(shape: &Shape) -> AdapterError {
    let m = decode_module(shape);
    let func = m.functions.first().expect("one function");
    trust_cg_lower::translate_function_with_license(func, &m, &permit_unlicensed())
        .expect_err("the descriptor must be refused")
}

/// The codec's own refusal of `shape`'s descriptor for `reason`, as the
/// adapter alone reports it lowering the decode program below typed admission
/// (`body_refusal_below_admission`).
fn codec_refusal_below_admission(shape: &Shape, reason: &str) -> String {
    format!(
        "not lowerable: unsupported trust_ir type: [TCG-NICHE-ENUM] enum EnumId(0) (`{}`): the \
         niche discriminant codec refuses the producer's niche descriptor ({reason}); refusing \
         rather than reading or writing the discriminant through a lane trust-cg's own layout \
         does not confirm",
        shape.enums[0].name
    )
}

fn decode_err(shape: &Shape) -> String {
    let err = lower(&decode_module(shape)).expect_err("the codec must refuse this descriptor");
    assert!(
        err.contains("[TCG-NICHE-ENUM]"),
        "{}: named diagnostic expected: {err}",
        shape.name
    );
    err
}

fn with_niche(mut shape: Shape, edit: impl FnOnce(&mut Niche)) -> Shape {
    edit(&mut shape.niche);
    shape.enums[0].layout.as_mut().unwrap().encoding = shape.niche.encoding();
    shape
}

/// TrustIR's typed admission checks every niche parameter against its enum,
/// so an incoherent descriptor is refused there on every codegen entry, before
/// the codec is asked. Below that admission the codec's own coherence checks
/// refuse each one by name.
#[test]
fn incoherent_niche_parameters_are_refused() {
    for (shape, location, expected, actual, codec) in [
        (
            with_niche(tri(), |n| n.untagged = 3),
            "enum.0 (Tri) layout",
            "an in-range untagged variant",
            "untagged_variant 3",
            "untagged_variant 3 does not name one of the 3 variants",
        ),
        (
            with_niche(tri(), |n| {
                n.start = 2;
                n.end = 1;
            }),
            "enum.0 (Tri) layout",
            "an ordered, in-range niche variant interval",
            "2..=1",
            "the niche variant interval 2..=1 is not an ordered interval of the 3 variants",
        ),
        (
            with_niche(tri(), |n| n.end = 1),
            "enum.0 (Tri) layout",
            "the niche interval plus the untagged variant to cover every inhabited variant",
            "inhabited variant 2 (High) is neither untagged 0 nor in niche interval 1..=1",
            "the niche variant interval 1..=1 plus untagged variant 0 does not cover the 3 \
             variants exactly",
        ),
        (
            with_niche(option_bool(), |n| n.niche_start = 0x100),
            "enum.0 (OptionBool) layout",
            "niche_start representable in 8 bits",
            "niche_start 256",
            "niche_start 0x100 does not fit the 8-bit lane",
        ),
    ] {
        assert_typed_const_refusal(&decode_refusal(&shape), location, expected, actual);
        assert_eq!(
            body_refusal_below_admission(&decode_module(&shape)),
            codec_refusal_below_admission(&shape, codec)
        );
    }
}

#[test]
fn valid_128_bit_niche_lanes_are_refused_without_narrowing() {
    for (repr, ty) in [(EnumTagRepr::U128, Ty::U128), (EnumTagRepr::I128, Ty::I128)] {
        let mut shape = with_niche(option_ref(), |n| n.repr = repr);
        shape.enums[0] = option_of("WideNiche", ty, shape.niche, 16, 16);
        assert_eq!(shape.niche.bytes(), 16);
        assert_eq!(shape.niche.mask(), u128::MAX);
        assert_eq!(shape.niche.decode(1u128 << 127), Ok(1));
        let m = module(
            &shape,
            vec![(v(0), enum_ty())],
            vec![shape.tag_ty.clone()],
            vec![
                InstrNode::new(Inst::ExtractField {
                    ty: shape.tag_ty.clone(),
                    aggregate: v(0),
                    field: 0,
                })
                .with_result(v(1)),
                InstrNode::new(Inst::Return { values: vec![v(1)] }),
            ],
        );
        let errors = trust_ir_build::validate_module(&m);
        assert!(errors.is_empty(), "{repr:?}: {errors:?}");
        let err = lower(&m).expect_err("128-bit niche lowering is not implemented");
        assert!(
            err.contains("[TCG-NICHE-ENUM]") && err.contains("128-bit"),
            "{err}"
        );
    }
}

/// A lane the descriptor cannot hold is refused by TrustIR's typed admission
/// on every codegen entry; below that admission the codec's own lane-placement
/// checks refuse it by name.
#[test]
fn a_misplaced_lane_is_refused() {
    for (shape, location, expected, actual, codec) in [
        // More aligned than the enum: a u64 lane in a 4-byte, align-4 enum.
        (
            with_niche(option_char(), |n| n.repr = EnumTagRepr::U64),
            "enum.0 (OptionChar) layout",
            "descriptor align at least niche alignment 8",
            "align 4",
            "the 8-byte lane at byte 0 is misaligned or more aligned than the enum's align 4",
        ),
        // Misaligned: a u32 lane at byte 2 of `Option<Pair>`.
        (
            with_niche(option_struct_lane(), |n| {
                n.offset = 2;
                n.repr = EnumTagRepr::U32;
            }),
            "enum.0 (OptionPair) layout",
            "a niche lane aligned to 4 bytes",
            "niche_offset 2",
            "the 4-byte lane at byte 2 is misaligned or more aligned than the enum's align 8",
        ),
        // Past the declared size.
        (
            with_niche(option_struct_lane(), |n| n.offset = 16),
            "enum.0 (OptionPair) layout",
            "a niche lane (8 bytes) within size 16",
            "niche_offset 16",
            "the 8-byte lane at byte 16 runs past the declared size 16",
        ),
    ] {
        assert_typed_const_refusal(&decode_refusal(&shape), location, expected, actual);
        assert_eq!(
            body_refusal_below_admission(&decode_module(&shape)),
            codec_refusal_below_admission(&shape, codec)
        );
    }
}

#[test]
fn a_lane_that_is_not_exactly_one_payload_scalar_is_refused() {
    // Padding: bytes 4..8 of `Pair { u32, &u64 }` belong to no field.
    let err = decode_err(&with_niche(option_struct_lane(), |n| {
        n.offset = 4;
        n.repr = EnumTagRepr::U32;
    }));
    assert!(err.contains("padding"), "{err}");
    // Part of a scalar: an 8-bit lane over the first byte of a char.
    let err = decode_err(&with_niche(option_char(), |n| {
        n.repr = EnumTagRepr::U8;
        n.niche_start = 0;
    }));
    assert!(err.contains("does not cover the scalar exactly"), "{err}");
    // A float is not a niche carrier.
    let mut float = option_char();
    float.enums[0].variants[1] = variant("Some", vec![Ty::F32]);
    let err = decode_err(&float);
    assert!(err.contains("F32"), "{err}");
    // Inside a nested niche enum but NOT on its lane. The inner
    // `Option<U8Bool>` (`struct U8Bool(u8, bool)`) keeps its niche in the bool
    // at byte 1; its byte 0 is only meaningful in `Some`, so an outer lane
    // there is refused.
    let inner_niche = Niche {
        untagged: 1,
        start: 0,
        end: 0,
        niche_start: 2,
        offset: 1,
        repr: EnumTagRepr::U8,
    };
    let u8_bool = StructDef {
        origin: None,
        id: StructId::new(0),
        name: "U8Bool".to_string(),
        fields: vec![
            FieldDef {
                name: "0".to_string(),
                ty: Ty::U8,
                offset: Some(0),
            },
            FieldDef {
                name: "1".to_string(),
                ty: Ty::Bool,
                offset: Some(1),
            },
        ],
        size: Some(2),
        align: Some(1),
        repr: StructRepr::Rust,
    };
    let mut inner = option_of(
        "OptionU8Bool",
        Ty::Struct(StructId::new(0)),
        inner_niche,
        2,
        1,
    );
    inner.id = EnumId::new(1);
    let outer_niche = Niche {
        niche_start: 0,
        offset: 0,
        ..inner_niche
    };
    let nested = Shape {
        name: "Option<Option<U8Bool>> on the wrong byte",
        structs: vec![u8_bool],
        types: vec![],
        enums: vec![
            option_of("Outer", Ty::Enum(EnumId::new(1)), outer_niche, 2, 1),
            inner,
        ],
        niche: outer_niche,
        tag_ty: Ty::U8,
        discs: vec![0, 1],
        variant_fields: vec![vec![], vec![]],
        payload_image: vec![],
    };
    let err = decode_err(&nested);
    assert!(err.contains("not that enum's own niche lane"), "{err}");
    // The same outer enum with its lane ON the inner lane (byte 1, the inner
    // `None` = 2 taken, so the outer `None` is 3) is admitted.
    let mut on_lane = nested.clone();
    on_lane.enums[0] = option_of(
        "Outer",
        Ty::Enum(EnumId::new(1)),
        Niche {
            niche_start: 3,
            offset: 1,
            ..inner_niche
        },
        2,
        1,
    );
    let m = module(
        &on_lane,
        vec![(v(0), enum_ty())],
        vec![Ty::U8],
        vec![
            InstrNode::new(Inst::ExtractField {
                ty: Ty::U8,
                aggregate: v(0),
                field: 0,
            })
            .with_result(v(1)),
            InstrNode::new(Inst::Return { values: vec![v(1)] }),
        ],
    );
    lower(&m).expect("an outer lane on the inner lane is admitted");
}

#[test]
fn reserved_values_that_are_valid_payload_values_are_refused() {
    // bool: 1 is `true`.
    let err = decode_err(&with_niche(option_bool(), |n| n.niche_start = 1));
    assert!(err.contains("overlap the valid payload values"), "{err}");
    // char: 'A' is a Unicode scalar value.
    let err = decode_err(&with_niche(option_char(), |n| n.niche_start = 0x41));
    assert!(err.contains("overlap"), "{err}");
    // A reference is non-null, so only 0 may be reserved.
    let err = decode_err(&with_niche(option_ref(), |n| n.niche_start = 8));
    assert!(err.contains("overlap"), "{err}");
    // Tri reserves 2 and 3; starting at 1 reserves `true`.
    let err = decode_err(&with_niche(tri(), |n| n.niche_start = 1));
    assert!(err.contains("overlap"), "{err}");
    // A reserved range that WRAPS into the bool's 0..=1.
    let err = decode_err(&with_niche(tri(), |n| n.niche_start = 255));
    assert!(err.contains("overlap"), "{err}");
    // Nested: the inner `None` (2) is a valid outer payload.
    let err = decode_err(&with_niche(option_option_bool(), |n| n.niche_start = 2));
    assert!(err.contains("overlap"), "{err}");
    // Direct tag: `B` (2) is a valid `Color`.
    let err = decode_err(&with_niche(option_direct(), |n| n.niche_start = 2));
    assert!(err.contains("overlap"), "{err}");
}

#[test]
fn a_niche_tagged_variant_whose_field_covers_the_lane_is_refused() {
    let mut shape = option_non_zero_u32();
    // `None` gains a u32 at byte 0 — exactly where its reserved value goes.
    shape.enums[0].variants[0] = variant("None", vec![Ty::U32]);
    shape.enums[0]
        .layout
        .as_mut()
        .unwrap()
        .variant_field_offsets[0] = vec![0];
    shape.enums[0].variants[1] = variant("Some", vec![Ty::U32]);
    assert_typed_const_refusal(
        &decode_refusal(&shape),
        "enum.0 (OptionNonZeroU32) layout",
        "the niche lane disjoint from non-ZST fields of niche-tagged variants",
        "lane overlaps variant 0 field 0",
    );
    // Below typed admission the codec's own rule refuses it by name.
    assert_eq!(
        body_refusal_below_admission(&decode_module(&shape)),
        codec_refusal_below_admission(
            &shape,
            "field 0 of niche-tagged variant 0 (`None`) overlaps the lane at byte 0"
        )
    );
}

#[test]
fn a_non_affine_discriminant_map_is_refused() {
    let mut shape = tri();
    shape.enums[0].discriminants = vec![Some(0), Some(5), Some(7)];
    let err = decode_err(&shape);
    assert!(err.contains("do not step by one"), "{err}");
}

/// A codec the descriptor does not support is refused only where the
/// DISCRIMINANT is touched: payload-only access keeps the admission it had.
#[test]
fn a_refused_codec_leaves_payload_access_admitted() {
    let shape = with_niche(option_bool(), |n| n.niche_start = 1);
    let m = module(
        &shape,
        vec![(v(0), enum_ty())],
        vec![Ty::Bool],
        vec![
            InstrNode::new(Inst::ExtractField {
                ty: Ty::Bool,
                aggregate: v(0),
                field: 1,
            })
            .with_result(v(1)),
            InstrNode::new(Inst::Return { values: vec![v(1)] }),
        ],
    );
    lower(&m).expect("payload field 0 stays addressable");
}

#[test]
fn malformed_constants_are_refused() {
    // Head names no variant, and the wrong arity: both are TrustIR's typed
    // findings, refused before the codec is asked on every codegen entry. The
    // codec's own head and arity checks are pinned below that admission.
    let no_variant = Constant::Aggregate(vec![Constant::Int(9)]);
    let err = construct(&tri(), no_variant.clone()).expect_err("no such discriminant");
    assert_eq!(
        err,
        typed_const_refusal("function 'k' bb0", "a discriminant of enum Tri", "9").to_string()
    );
    assert_eq!(
        body_refusal_below_admission(&constant_module(&tri(), no_variant)),
        "not lowerable: unsupported trust_ir instruction: [TCG-NICHE-ENUM] Constant::Aggregate \
         for niche-encoded enum EnumId(0) (`Tri`) has head 9, which names no variant \
         discriminant (variants carry [0, 1, 2])"
    );
    let wrong_arity = Constant::Aggregate(vec![Constant::Int(1), Constant::Bool(true)]);
    let err = construct(&tri(), wrong_arity.clone()).expect_err("Low has no fields");
    assert_eq!(
        err,
        typed_const_refusal(
            "function 'k' bb0",
            "0 payload field(s) for variant Low",
            "1 field(s)"
        )
        .to_string()
    );
    assert_eq!(
        body_refusal_below_admission(&constant_module(&tri(), wrong_arity)),
        "not lowerable: unsupported trust_ir instruction: [TCG-NICHE-ENUM] Constant::Aggregate \
         arity mismatch for niche-encoded enum EnumId(0) (`Tri`): variant 1 expects 0 payload \
         fields, got 1"
    );
    // Untagged payload holding a reserved value: `Some(0)` of a NonZeroU32.
    let err = construct(
        &option_non_zero_u32(),
        Constant::Aggregate(vec![
            Constant::Int(1),
            Constant::Aggregate(vec![Constant::Int(0)]),
        ]),
    )
    .expect_err("Some(0) is None's image");
    assert!(err.contains("reserved niche value 0x0"), "{err}");
    // Wrapped: Data(254) is Low's image, Data(255) the dead value.
    for reserved in [254, 255, 0] {
        let err = construct(
            &wrapped(),
            Constant::Aggregate(vec![Constant::Int(1), Constant::Int(reserved)]),
        )
        .expect_err("reserved payload");
        assert!(err.contains("reserved niche value"), "{reserved}: {err}");
    }
    // Nested: `Some(Some(x))` is fine, but the outer reserved value 3 can
    // never be produced by a valid inner constant — the inner head decides.
    construct(
        &option_option_bool(),
        Constant::Aggregate(vec![
            Constant::Int(1),
            Constant::Aggregate(vec![Constant::Int(1), Constant::Bool(true)]),
        ]),
    )
    .expect("Some(Some(true))");
}

/// The untagged-constant check reads the LANE's element, not its neighbour.
/// With the lane on element 2 of `[u8; 4]`, a 0 on element 0 is payload and a
/// 0 on element 2 is `None`'s image, whether the array is spelled element by
/// element or as a byte string. A check that followed the wrong element would
/// refuse the first constant and emit the second as `None`.
#[test]
fn an_untagged_constant_is_checked_at_the_lanes_own_element() {
    let shape = option_array_lane();
    let spellings = [
        ("array", byte_array as fn([u8; 4]) -> Constant),
        ("bytes", byte_string),
    ];
    for (spelling, spell) in spellings {
        let image = construct(
            &shape,
            Constant::Aggregate(vec![Constant::Int(1), spell([0x00, 0x11, 0x22, 0x33])]),
        )
        .unwrap_or_else(|e| panic!("{spelling}: a 0 off the lane is payload: {e}"));
        let bytes: Vec<u8> = (0..4).map(|at| image[&at]).collect();
        assert_eq!(bytes, [0x00, 0x11, 0x22, 0x33], "{spelling}");
        let err = construct(
            &shape,
            Constant::Aggregate(vec![Constant::Int(1), spell([0x44, 0x55, 0x00, 0x66])]),
        )
        .expect_err("a 0 on the lane is None's image");
        assert!(
            err.contains("[TCG-NICHE-ENUM]") && err.contains("reserved niche value 0x0"),
            "{spelling}: {err}"
        );
    }
}

#[test]
fn a_discriminant_write_of_the_wrong_type_is_refused() {
    let shape = tri();
    let m = module(
        &shape,
        vec![(v(0), enum_ty()), (v(1), Ty::U32)],
        vec![],
        vec![
            InstrNode::new(Inst::InsertField {
                ty: enum_ty(),
                aggregate: v(0),
                field: 0,
                value: v(1),
            })
            .with_result(v(2)),
            InstrNode::new(Inst::Return { values: vec![] }),
        ],
    );
    let err = lower(&m).expect_err("retagging is refused even with a wrong-width tag");
    assert!(err.contains("rewrite the discriminant"), "{err}");
}

/// The emitted lane accesses are the lane's own width: a byte for bool, a
/// word for char, a doubleword for a pointer. A wider access would read or
/// clobber the neighbouring payload.
#[test]
fn lane_accesses_have_the_lane_width() {
    for (shape, ty) in [
        (option_bool(), Type::I8),
        (option_u16_lane(), Type::I16),
        (option_char(), Type::I32),
        (option_ref(), Type::I64),
    ] {
        let (instrs, _) = decode_program(&shape);
        assert!(
            instrs
                .iter()
                .any(|i| matches!(&i.opcode, Opcode::Load { ty: t, .. } if *t == ty)),
            "{}: {instrs:?}",
            shape.name
        );
    }
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes because it was silently refused.
fn permit_unlicensed() -> trust_cg_lower::CodegenLicensePolicy {
    trust_cg_lower::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit)
}
