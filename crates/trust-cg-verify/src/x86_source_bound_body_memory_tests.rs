// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Slice 4 of the x86-64 source-bound body theorem: private stack slots and
//! incoming memory.
//!
//! Fixtures are real: LIR from the trust-ir adapter, the machine stream from
//! the real x86-64 instruction selector (`super::select`). Negative controls
//! mutate that stream and must end as a typed mismatch, a refuted theorem or
//! an unsupported (uncredited) body, never as Formal credit.

use super::*;

/// Slice-4 fixture shapes. Every pointer parameter may alias every other.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum MemShape {
    // ---- incoming loads
    /// `*p` (u64).
    LoadU64,
    /// `*p` (u8): `mov r8, m` then the selector's `movzx`.
    LoadU8,
    /// `*p` (i16).
    LoadI16,
    /// `*p` (u32): `mov r32, m` zero-extends.
    LoadU32,
    /// `*p` (bool): the loaded byte `m` read as `m != 0`.
    LoadBool,
    /// `*p as u32` (bool loaded, zero-extended to the u32 result).
    LoadBoolWidened,
    /// `g2(*p)`: a loaded bool passed as a call argument.
    LoadBoolArgument,
    /// `*(p + 7)` (bool): a bool field at a constant offset.
    BoolFieldLoad,
    /// `*p as u32` (u8 loaded, zero-extended to the u32 result).
    LoadU8Widened,
    /// `*(p + 8)`: a field load at a constant offset.
    FieldLoad,
    // ---- incoming stores
    /// `*p = v` (u64).
    StoreU64,
    /// `*p = v` (u8).
    StoreU8,
    /// `*p = v` (u16).
    StoreU16,
    /// `*p = v` (u32).
    StoreU32,
    /// `*p = v` (bool).
    StoreBool,
    /// `*p = x as i64` (x: i8): a sign extension stored as eight bytes.
    StoreWidened,
    /// `*a = *b` (u32).
    CopyU32,
    /// `*a = x; *b` (u64): the load may read the store.
    StoreThenLoad,
    /// `*a = x; *b = y` (u64).
    TwoStores,
    /// `*a = x; *b = y; *a` (u64): `a` and `b` may alias.
    StoresReload,
    // ---- private stack slots
    /// `let s = x; s` through one u64 slot.
    LocalRoundTrip,
    /// The same through a u8 slot.
    LocalU8,
    /// The same through a bool slot.
    LocalBool,
    /// A 16-byte slot holding two u64 fields, both read back and added.
    SlotPair,
    /// Two u32 halves stored, the u64 read back whole.
    SlotHalves,
    /// Two u64 slots; the first is returned.
    TwoSlots,
    /// A slot store that is never read: `let s = x; x`.
    DeadSlotStore,
    /// `let s = x; *p = s`: a slot, then an incoming store.
    SlotToStore,
    /// Four field stores of mixed widths (u32, u16, u8, bool) through one
    /// pointer, the `#[repr(C)] struct Mixed` writer.
    MixedStores,
    /// `(*p).second` through a LIR `StructGep` (the bridge's field access).
    StructField,
    /// The second field of a private pair slot through a `StructGep`.
    SlotStructField,
    /// An sret writer: `fn(buf: &mut Pair (hidden), x, y) { *buf = Pair(x, y) }`,
    /// which must also return `buf` in RAX.
    SretPair,
    /// `SlotPair` with the second field's offset computed as `2 * 4` (the
    /// bridge folds field offsets from constant products at O0).
    SlotFoldedOffset,
    // ---- memory threaded through calls
    /// `let v = *p; g1(v) + *p`: the second load reads after the call.
    LoadCallLoad,
    /// `*p = x; g1(x)`.
    StoreCall,
}

/// Every shape whose real selection the owner admits and whose theorem
/// holds ([`every_admitted_fixture_shape_is_qualified`] checks that none is
/// left out). The four bool loads from incoming memory joined when the
/// selector began computing `byte != 0` (the rest keep their order, so the
/// golden file's earlier entries are unchanged except `LocalBool`'s machine
/// side).
pub(crate) const MEMORY_SHAPES: [MemShape; 35] = [
    MemShape::LoadU64,
    MemShape::LoadU8,
    MemShape::LoadI16,
    MemShape::LoadU32,
    MemShape::LoadU8Widened,
    MemShape::FieldLoad,
    MemShape::StoreU64,
    MemShape::StoreU8,
    MemShape::StoreU16,
    MemShape::StoreU32,
    MemShape::StoreBool,
    MemShape::StoreWidened,
    MemShape::CopyU32,
    MemShape::StoreThenLoad,
    MemShape::TwoStores,
    MemShape::StoresReload,
    MemShape::LocalRoundTrip,
    MemShape::LocalU8,
    MemShape::LocalBool,
    MemShape::SlotPair,
    MemShape::SlotHalves,
    MemShape::TwoSlots,
    MemShape::DeadSlotStore,
    MemShape::SlotToStore,
    MemShape::MixedStores,
    MemShape::LoadCallLoad,
    MemShape::StoreCall,
    MemShape::StructField,
    MemShape::SlotStructField,
    MemShape::SretPair,
    MemShape::SlotFoldedOffset,
    MemShape::LoadBool,
    MemShape::LoadBoolWidened,
    MemShape::LoadBoolArgument,
    MemShape::BoolFieldLoad,
];

impl MemShape {
    fn name(self) -> String {
        let name = format!("{self:?}");
        let mut snake = String::from("mem_");
        for (i, c) in name.chars().enumerate() {
            if c.is_ascii_uppercase() && i > 0 {
                snake.push('_');
            }
            snake.push(c.to_ascii_lowercase());
        }
        snake
    }
}

/// The LIR the trust-ir adapter produces for a slice-4 shape.
pub(crate) fn memory_lir(shape: MemShape) -> Function {
    use MemShape::*;
    // Hand-derived LIR: the adapter's spelling of a shape with its constant
    // address offset rewritten as the `StructGep` the bridge emits for a
    // field, or with the sret declaration the bridge's `PassMode::Indirect`
    // return makes. The machine stream is still the real selector's.
    let rename = |mut function: Function, shape: MemShape| {
        function.name = shape.name();
        function
    };
    match shape {
        StructField => return rename(struct_gep(memory_lir(FieldLoad)), shape),
        SlotStructField => return rename(struct_gep(memory_lir(SlotPair)), shape),
        SlotFoldedOffset => {
            let mut function = rename(memory_lir(SlotPair), shape);
            let entry = function.entry_block;
            let body = function.blocks.get_mut(&entry).unwrap();
            let eight = body
                .instructions
                .iter()
                .position(|inst| matches!(inst.opcode, L::Iconst { imm: 8, .. }))
                .expect("the field offset");
            let result = body.instructions[eight].results[0];
            let (two, four) = (Value(10_000), Value(10_001));
            body.instructions[eight] = Instruction {
                opcode: L::Imul,
                args: vec![two, four],
                results: vec![result],
            };
            for (at, value, imm) in [(eight, four, 4), (eight, two, 2)] {
                body.instructions.insert(
                    at,
                    Instruction {
                        opcode: L::Iconst { ty: Type::I64, imm },
                        args: vec![],
                        results: vec![value],
                    },
                );
            }
            return function;
        }
        SretPair => {
            let mut function = rename(memory_lir(TwoStores), shape);
            // `*p = x; *(p + 8) = y` over params (p, x, y): drop the second
            // pointer parameter of TwoStores by rewriting it to `p + 8`.
            let entry = function.entry_block;
            let body = function.blocks.get_mut(&entry).unwrap();
            let offset = Value(10_000);
            let field = Value(10_001);
            body.instructions.insert(
                0,
                Instruction {
                    opcode: L::Iconst {
                        ty: Type::I64,
                        imm: 8,
                    },
                    args: vec![],
                    results: vec![offset],
                },
            );
            body.instructions.insert(
                1,
                Instruction {
                    opcode: L::Iadd,
                    args: vec![Value(0), offset],
                    results: vec![field],
                },
            );
            for inst in &mut body.instructions {
                for arg in &mut inst.args {
                    if *arg == Value(1) {
                        *arg = field;
                    }
                }
            }
            let mut function = struct_gep(function);
            function.abi_sret_param =
                Some(trust_cg_lower::function::AbiSretParam { param_index: 0 });
            return function;
        }
        _ => {}
    }
    let mut builder = ModuleBuilder::new("x86_source_bound_body_memory");
    let unary = builder.add_func_type(vec![Ty::U64], vec![Ty::U64]);
    let g1 = builder.declare_function("g1", unary);
    let of_bool = builder.add_func_type(vec![Ty::Bool], vec![Ty::U64]);
    let g2 = builder.declare_function("g2", of_bool);
    let pair = Ty::Struct(
        builder.add_struct(StructDef {
            origin: None,
            id: StructId::new(0),
            name: "Pair".into(),
            fields: ["first", "second"]
                .map(|name| FieldDef {
                    name: name.into(),
                    ty: Ty::U64,
                    offset: None,
                })
                .to_vec(),
            size: None,
            align: None,
            repr: StructRepr::C,
        }),
    );
    let ptr = |ty: Ty| Ty::PtrMut(Box::new(ty));
    let (params, result): (Vec<Ty>, Option<Ty>) = match shape {
        LoadU64 | FieldLoad => (vec![ptr(Ty::U64)], Some(Ty::U64)),
        LoadU8 => (vec![ptr(Ty::U8)], Some(Ty::U8)),
        LoadI16 => (vec![ptr(Ty::I16)], Some(Ty::I16)),
        LoadU32 => (vec![ptr(Ty::U32)], Some(Ty::U32)),
        LoadBool => (vec![ptr(Ty::Bool)], Some(Ty::Bool)),
        LoadBoolWidened => (vec![ptr(Ty::Bool)], Some(Ty::U32)),
        LoadBoolArgument => (vec![ptr(Ty::Bool)], Some(Ty::U64)),
        BoolFieldLoad => (vec![ptr(Ty::U64)], Some(Ty::Bool)),
        LoadU8Widened => (vec![ptr(Ty::U8)], Some(Ty::U32)),
        StoreU64 => (vec![ptr(Ty::U64), Ty::U64], None),
        StoreU8 => (vec![ptr(Ty::U8), Ty::U8], None),
        StoreU16 => (vec![ptr(Ty::U16), Ty::U16], None),
        StoreU32 => (vec![ptr(Ty::U32), Ty::U32], None),
        StoreBool => (vec![ptr(Ty::Bool), Ty::Bool], None),
        StoreWidened => (vec![ptr(Ty::I64), Ty::I8], None),
        CopyU32 => (vec![ptr(Ty::U32), ptr(Ty::U32)], None),
        StoreThenLoad => (vec![ptr(Ty::U64), ptr(Ty::U64), Ty::U64], Some(Ty::U64)),
        TwoStores => (vec![ptr(Ty::U64), ptr(Ty::U64), Ty::U64, Ty::U64], None),
        StoresReload => (
            vec![ptr(Ty::U64), ptr(Ty::U64), Ty::U64, Ty::U64],
            Some(Ty::U64),
        ),
        LocalRoundTrip | DeadSlotStore => (vec![Ty::U64], Some(Ty::U64)),
        LocalU8 => (vec![Ty::U8], Some(Ty::U8)),
        LocalBool => (vec![Ty::Bool], Some(Ty::Bool)),
        SlotPair | TwoSlots => (vec![Ty::U64, Ty::U64], Some(Ty::U64)),
        SlotHalves => (vec![Ty::U32, Ty::U32], Some(Ty::U64)),
        SlotToStore => (vec![ptr(Ty::U64), Ty::U64], None),
        MixedStores => (vec![ptr(Ty::U32), Ty::U32, Ty::U16, Ty::U8, Ty::Bool], None),
        StructField | SlotStructField | SretPair | SlotFoldedOffset => {
            unreachable!("derived above")
        }
        LoadCallLoad => (vec![ptr(Ty::U64)], Some(Ty::U64)),
        StoreCall => (vec![ptr(Ty::U64), Ty::U64], Some(Ty::U64)),
    };
    let signature = builder.add_func_type(params.clone(), result.iter().cloned().collect());
    let mut f = builder.function(shape.name(), signature);
    let entry = f.create_block();
    let a: Vec<_> = params
        .iter()
        .map(|ty| f.add_block_param(entry, ty.clone()))
        .collect();
    f.switch_to_block(entry);
    let value = match shape {
        LoadU64 => Some(f.load(Ty::U64, a[0])),
        LoadU8 => Some(f.load(Ty::U8, a[0])),
        LoadI16 => Some(f.load(Ty::I16, a[0])),
        LoadU32 => Some(f.load(Ty::U32, a[0])),
        LoadBool => Some(f.load(Ty::Bool, a[0])),
        LoadBoolWidened => {
            let flag = f.load(Ty::Bool, a[0]);
            Some(f.zext(Ty::Bool, Ty::U32, flag))
        }
        LoadBoolArgument => {
            let flag = f.load(Ty::Bool, a[0]);
            Some(f.call(g2, vec![flag]))
        }
        BoolFieldLoad => {
            let field = f.gep_byte_offset(a[0], 7);
            Some(f.load(Ty::Bool, field))
        }
        LoadU8Widened => {
            let byte = f.load(Ty::U8, a[0]);
            Some(f.zext(Ty::U8, Ty::U32, byte))
        }
        FieldLoad => {
            let field = f.gep_byte_offset(a[0], 8);
            Some(f.load(Ty::U64, field))
        }
        StoreU64 | StoreU8 | StoreU16 | StoreU32 | StoreBool => {
            let ty = params[1].clone();
            f.store(ty, a[0], a[1]);
            None
        }
        StoreWidened => {
            let wide = f.sext(Ty::I8, Ty::I64, a[1]);
            f.store(Ty::I64, a[0], wide);
            None
        }
        CopyU32 => {
            let v = f.load(Ty::U32, a[1]);
            f.store(Ty::U32, a[0], v);
            None
        }
        StoreThenLoad => {
            f.store(Ty::U64, a[0], a[2]);
            Some(f.load(Ty::U64, a[1]))
        }
        TwoStores | StoresReload => {
            f.store(Ty::U64, a[0], a[2]);
            f.store(Ty::U64, a[1], a[3]);
            (shape == StoresReload).then(|| f.load(Ty::U64, a[0]))
        }
        LocalRoundTrip | LocalU8 | LocalBool => {
            let ty = params[0].clone();
            let slot = f.alloca(ty.clone());
            f.store(ty.clone(), slot, a[0]);
            Some(f.load(ty, slot))
        }
        SlotPair => {
            let slot = f.alloca(pair.clone());
            f.store(Ty::U64, slot, a[0]);
            let second = f.gep_byte_offset(slot, 8);
            f.store(Ty::U64, second, a[1]);
            let x = f.load(Ty::U64, slot);
            let y = f.load(Ty::U64, second);
            Some(f.add(Ty::U64, x, y))
        }
        SlotHalves => {
            let slot = f.alloca(Ty::U64);
            f.store(Ty::U32, slot, a[0]);
            let high = f.gep_byte_offset(slot, 4);
            f.store(Ty::U32, high, a[1]);
            Some(f.load(Ty::U64, slot))
        }
        TwoSlots => {
            let first = f.alloca(Ty::U64);
            let second = f.alloca(Ty::U64);
            f.store(Ty::U64, first, a[0]);
            f.store(Ty::U64, second, a[1]);
            Some(f.load(Ty::U64, first))
        }
        DeadSlotStore => {
            let slot = f.alloca(Ty::U64);
            f.store(Ty::U64, slot, a[0]);
            Some(a[0])
        }
        SlotToStore => {
            let slot = f.alloca(Ty::U64);
            f.store(Ty::U64, slot, a[1]);
            let v = f.load(Ty::U64, slot);
            f.store(Ty::U64, a[0], v);
            None
        }
        MixedStores => {
            f.store(Ty::U32, a[0], a[1]);
            let h = f.gep_byte_offset(a[0], 4);
            f.store(Ty::U16, h, a[2]);
            let b = f.gep_byte_offset(a[0], 6);
            f.store(Ty::U8, b, a[3]);
            let flag = f.gep_byte_offset(a[0], 7);
            f.store(Ty::Bool, flag, a[4]);
            None
        }
        LoadCallLoad => {
            let v = f.load(Ty::U64, a[0]);
            let r = f.call(g1, vec![v]);
            let w = f.load(Ty::U64, a[0]);
            Some(f.add(Ty::U64, r, w))
        }
        StoreCall => {
            f.store(Ty::U64, a[0], a[1]);
            Some(f.call(g1, vec![a[1]]))
        }
        StructField | SlotStructField | SretPair | SlotFoldedOffset => {
            unreachable!("derived above")
        }
    };
    f.ret(value.into_iter().collect());
    f.build();
    let module = builder.build().expect("ModuleBuilder::build: test fixture");
    trust_cg_lower::translate_module_for_arch_with_tls_with_license(
        &module,
        trust_cg_lower::GuardCarrierArch::X86_64,
        trust_cg_lower::TlsDialect::default(),
        &super::permit_unlicensed(),
    )
    .unwrap_or_else(|error| panic!("{shape:?}: fixture translates: {error:?}"))
    .into_iter()
    .map(|(function, _)| function)
    .find(|function| function.name == shape.name())
    .unwrap_or_else(|| panic!("{shape:?}: no translated function"))
}

/// Rewrite the first byte-address GEP (or legacy Iadd) with an `Iconst 8` into the
/// `StructGep { Struct([I64, I64]), 1 }` the bridge emits for the second
/// field of a pair.
fn struct_gep(mut function: Function) -> Function {
    let entry = function.entry_block;
    let body = function.blocks.get_mut(&entry).unwrap();
    let eights: HashSet<Value> = body
        .instructions
        .iter()
        .filter(|inst| matches!(inst.opcode, L::Iconst { imm: 8, .. }))
        .map(|inst| inst.results[0])
        .collect();
    let gep = body
        .instructions
        .iter()
        .position(|inst| {
            matches!(inst.opcode, L::Iadd | L::ArrayGep { elem_ty: Type::I8 })
                && eights.contains(&inst.args[1])
        })
        .expect("a pointer plus eight");
    let base = body.instructions[gep].args[0];
    body.instructions[gep].opcode = L::StructGep {
        struct_ty: Type::Struct(vec![Type::I64, Type::I64]),
        field_index: 1,
    };
    body.instructions[gep].args = vec![base];
    function
}

pub(crate) fn memory_pair(shape: MemShape) -> (Function, X86ISelFunction) {
    let source = memory_lir(shape);
    let machine = select(&source, X86CallAbi::SystemV);
    (source, machine)
}

/// Every row whose opcode is one of `opcodes`, in walk order.
fn rows_of(machine: &X86ISelFunction, opcodes: &[X86Opcode]) -> Vec<usize> {
    rows(machine)
        .into_iter()
        .filter(|(_, block, index)| opcodes.contains(&machine.blocks[block].insts[*index].opcode))
        .map(|(ordinal, _, _)| ordinal)
        .collect()
}

const LOADS: [X86Opcode; 6] = [
    X86Opcode::MovRM8,
    X86Opcode::MovRM16,
    X86Opcode::MovzxRM8,
    X86Opcode::MovzxRM16,
    X86Opcode::MovRM32,
    X86Opcode::MovRM,
];
const STORES: [X86Opcode; 4] = [
    X86Opcode::MovMR8,
    X86Opcode::MovMR16,
    X86Opcode::MovMR32,
    X86Opcode::MovMR,
];

/// The memory operand of a load (`[1]`) or store (`[0]`) row.
fn memory_operand(machine: &mut X86ISelFunction, row: usize) -> &mut O {
    let load = LOADS.contains(&inst(machine, row).opcode);
    &mut inst_mut(machine, row).operands[usize::from(load)]
}

/// The base and byte offset of a 64-bit address, without changing its ISA form.
pub(crate) fn byte_address_inputs(inst: &X86ISelInst) -> Option<(&O, &O)> {
    match (inst.opcode, inst.operands.as_slice()) {
        (X86Opcode::AddRR, [_, base, index]) => Some((base, index)),
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
        ) => Some((base.as_ref(), index.as_ref())),
        _ => None,
    }
}

pub(crate) fn set_byte_address_base(machine: &mut X86ISelFunction, row: usize, to: O) {
    let inst = inst_mut(machine, row);
    match (inst.opcode, inst.operands.as_mut_slice()) {
        (X86Opcode::AddRR, [_, base, _]) => *base = to,
        (
            X86Opcode::LeaSib,
            [
                _,
                O::SibMemAddr {
                    base,
                    scale: 1,
                    disp: 0,
                    ..
                },
            ],
        ) => **base = to,
        _ => panic!("not a byte address: {inst:?}"),
    }
}

fn describe(machine: &X86ISelFunction) -> String {
    let mut text = String::new();
    for (ordinal, block, index) in rows(machine) {
        let inst = &machine.blocks[&block].insts[index];
        text.push_str(&format!(
            "  [{ordinal}] {:?} {:?}\n",
            inst.opcode, inst.operands
        ));
    }
    text
}

// ---------------------------------------------------------------------------
// Construction (no solver)
// ---------------------------------------------------------------------------

#[test]
fn memory_fixtures_have_the_expected_pre_ra_shapes() {
    use X86Opcode::*;
    assert_eq!(
        opcodes(&memory_pair(MemShape::LoadU64).1),
        vec![MovRR, MovRM, MovRR, Ret]
    );
    // A u8 load is the zero-extending `movzx r32, m8`, which writes the whole
    // register; the return's re-extension of it is a 32-bit copy.
    assert_eq!(
        opcodes(&memory_pair(MemShape::LoadU8).1),
        vec![MovRR, MovzxRM8, MovRR32, MovRR32, Ret]
    );
    // A bool load is `movzx r32, m8`, then `m != 0` into the clean 32-bit
    // bool the backend returns in EAX: `add 255; shr 8`.
    assert_eq!(
        opcodes(&memory_pair(MemShape::LoadBool).1),
        vec![MovRR, MovzxRM8, AddRI, ShrRI, MovRR32, Ret]
    );
    assert_eq!(
        opcodes(&memory_pair(MemShape::StoreU64).1),
        vec![MovRR, MovRR, MovMR, Ret]
    );
    assert_eq!(
        opcodes(&memory_pair(MemShape::LocalRoundTrip).1),
        vec![MovRR, Lea, MovMR, MovRM, MovRR, Ret]
    );
    let (source, machine) = memory_pair(MemShape::LocalRoundTrip);
    assert_eq!(source.stack_slots, machine.stack_slots);
    assert_eq!(
        inst(&machine, 1).operands[1],
        O::MemAddr {
            base: Box::new(O::StackSlot(0)),
            disp: 0
        }
    );
}

#[test]
fn owner_builds_for_every_memory_shape_and_covers_every_value_row() {
    for shape in MEMORY_SHAPES {
        let (source, machine) = memory_pair(shape);
        let owner = source_bound_x86_body(&source, &machine, SYSV)
            .unwrap_or_else(|refusal| panic!("{shape:?}: {refusal}\n{}", describe(&machine)));
        let expected: Vec<usize> = rows(&machine)
            .into_iter()
            .filter(|(_, block, index)| {
                let opcode = machine.blocks[block].insts[*index].opcode;
                !opcode.is_pseudo()
                    && !matches!(
                        opcode,
                        X86Opcode::Jmp | X86Opcode::Ret | X86Opcode::Call | X86Opcode::Ud2
                    )
            })
            .map(|(ordinal, _, _)| ordinal)
            .collect();
        assert_eq!(owner.bound_rows(), expected, "{shape:?}");
        // Every incoming access is paired, in order, with a machine load or
        // store row; private stack accesses are not in the trace.
        let incoming: Vec<usize> = owner
            .access_sites()
            .iter()
            .map(|(_, _, row)| *row)
            .collect();
        for row in &incoming {
            assert!(
                LOADS.contains(&inst(&machine, *row).opcode)
                    || STORES.contains(&inst(&machine, *row).opcode),
                "{shape:?}"
            );
        }
        assert_eq!(
            owner.access_sites().len(),
            source
                .blocks
                .values()
                .flat_map(|block| &block.instructions)
                .filter(|inst| matches!(inst.opcode, L::Load { .. } | L::Store { .. }))
                .count()
                - private_accesses(&source),
            "{shape:?}"
        );
        let entries = free_inputs_of(owner.obligation());
        assert_eq!(
            owner_check(&source, &machine, owner.obligation(), &entries),
            Ok(())
        );
        assert!(owner.obligation().is_genuinely_proven(), "{shape:?}");
        assert!(source_admits_x86_body_owner(&source, SYSV), "{shape:?}");
    }
}

/// LIR loads and stores whose address is a private stack slot's.
fn private_accesses(source: &Function) -> usize {
    let mut frame: HashSet<Value> = HashSet::new();
    let mut count = 0;
    for block in source.layout_order() {
        for inst in &source.blocks[&block].instructions {
            match &inst.opcode {
                L::StackAddr { .. } => {
                    frame.insert(inst.results[0]);
                }
                L::Iadd | L::Copy | L::StructGep { .. }
                    if inst.args.iter().any(|arg| frame.contains(arg)) =>
                {
                    frame.insert(inst.results[0]);
                }
                L::ArrayGep { elem_ty: Type::I8 } if frame.contains(&inst.args[0]) => {
                    frame.insert(inst.results[0]);
                }
                L::Load { .. } if frame.contains(&inst.args[0]) => count += 1,
                L::Store { .. } if frame.contains(&inst.args[1]) => count += 1,
                _ => {}
            }
        }
    }
    count
}

#[test]
fn memory_theorems_hold_on_samples() {
    for shape in MEMORY_SHAPES {
        let (source, machine) = memory_pair(shape);
        let owner = source_bound_x86_body(&source, &machine, SYSV).unwrap();
        assert!(holds_on_samples(owner.obligation()), "{shape:?}");
    }
}

/// Every fixture shape, in declaration order.
fn all_memory_shapes() -> Vec<MemShape> {
    use MemShape::*;
    let all = vec![
        LoadU64,
        LoadU8,
        LoadI16,
        LoadU32,
        LoadBool,
        LoadBoolWidened,
        LoadBoolArgument,
        BoolFieldLoad,
        LoadU8Widened,
        FieldLoad,
        StoreU64,
        StoreU8,
        StoreU16,
        StoreU32,
        StoreBool,
        StoreWidened,
        CopyU32,
        StoreThenLoad,
        TwoStores,
        StoresReload,
        LocalRoundTrip,
        LocalU8,
        LocalBool,
        SlotPair,
        SlotHalves,
        TwoSlots,
        DeadSlotStore,
        SlotToStore,
        MixedStores,
        StructField,
        SlotStructField,
        SretPair,
        SlotFoldedOffset,
        LoadCallLoad,
        StoreCall,
    ];
    // Exhaustive: a new shape does not compile until it is listed here.
    for shape in &all {
        match shape {
            LoadU64 | LoadU8 | LoadI16 | LoadU32 | LoadBool | LoadBoolWidened
            | LoadBoolArgument | BoolFieldLoad | LoadU8Widened | FieldLoad | StoreU64 | StoreU8
            | StoreU16 | StoreU32 | StoreBool | StoreWidened | CopyU32 | StoreThenLoad
            | TwoStores | StoresReload | LocalRoundTrip | LocalU8 | LocalBool | SlotPair
            | SlotHalves | TwoSlots | DeadSlotStore | SlotToStore | MixedStores | StructField
            | SlotStructField | SretPair | SlotFoldedOffset | LoadCallLoad | StoreCall => {}
        }
    }
    all
}

/// The golden, owner, credit and host-qualification tests run over
/// [`MEMORY_SHAPES`]: every fixture whose real selection the owner admits
/// with a theorem that holds must be in it, so none is silently left out of
/// qualification.
#[test]
fn every_admitted_fixture_shape_is_qualified() {
    for shape in all_memory_shapes() {
        let (source, machine) = memory_pair(shape);
        let holds = source_bound_x86_body(&source, &machine, SYSV)
            .is_ok_and(|owner| holds_on_samples(owner.obligation()));
        assert_eq!(
            MEMORY_SHAPES.contains(&shape),
            holds,
            "{shape:?}: MEMORY_SHAPES must hold exactly the admitted fixtures whose theorem holds"
        );
    }
}

#[test]
fn a_paired_load_is_one_shared_input_and_private_slots_are_not_observed() {
    // `*p`: the source result and the machine load read the same `l0`; the
    // observable is the returned value and the load's address.
    let (source, machine) = memory_pair(MemShape::LoadU64);
    source_bound_x86_body(&source, &machine, SYSV).unwrap();
    let items = observable_items(&plain_theorem(&source, &machine));
    assert_eq!(items.len(), 2, "{items:?}");
    assert!(
        plain_theorem(&source, &machine)
            .inputs
            .iter()
            .any(|(name, width)| name == "l0" && *width == 64)
    );
    // A local round trip observes the returned value only: no address, no
    // slot byte, no load input.
    let (source, machine) = memory_pair(MemShape::LocalRoundTrip);
    source_bound_x86_body(&source, &machine, SYSV).unwrap();
    assert_eq!(observable_items(&plain_theorem(&source, &machine)).len(), 1);
    assert!(
        plain_theorem(&source, &machine)
            .inputs
            .iter()
            .all(|(name, _)| !is_memory_input(name))
    );
    // A store observes its address and value at the stored width.
    let (source, machine) = memory_pair(MemShape::StoreU16);
    source_bound_x86_body(&source, &machine, SYSV).unwrap();
    let items = observable_items(&plain_theorem(&source, &machine));
    assert_eq!(
        items
            .iter()
            .map(|(source, machine)| (source.bv_width(), machine.bv_width()))
            .collect::<Vec<_>>(),
        vec![(64, 64), (16, 16)]
    );
    // A bool store writes the byte 0 or 1.
    let (source, machine) = memory_pair(MemShape::StoreBool);
    source_bound_x86_body(&source, &machine, SYSV).unwrap();
    assert_eq!(
        observable_items(&plain_theorem(&source, &machine))[1]
            .0
            .bv_width(),
        8
    );
}

// ---------------------------------------------------------------------------
// Negative controls (no solver): each wrong lowering is refused (a typed
// mismatch or an uncredited Unsupported body) or its theorem is refuted.
// ---------------------------------------------------------------------------

/// A wrong lowering the owner still binds: the replayed query itself must be
/// refuted (sampled here; the tool-gated qualification replays it on AY).
#[track_caller]
fn refuted(source: &Function, machine: &X86ISelFunction, what: &str) {
    let theorem = theorem_without_affine_refusal(source, machine, SYSV)
        .unwrap_or_else(|refusal| panic!("{what}: {refusal}\n{}", describe(machine)));
    assert!(
        refuted_on_samples(&theorem),
        "{what}: the theorem must refute the wrong lowering\n{}",
        describe(machine)
    );
}

#[track_caller]
fn trace_refused(source: &Function, machine: &X86ISelFunction, what: &str) {
    match source_bound_x86_body(source, machine, SYSV) {
        Err(X86BodyRefusal::Unsupported(X86BodyUnsupported::AccessTrace { .. })) => {}
        Err(other) => panic!("{what}: expected an access-trace refusal, got {other}"),
        Ok(_) => panic!("{what}: a wrong lowering built a body theorem"),
    }
}

#[test]
fn wrong_slot_offset_or_width_is_refused() {
    // Wrong slot: the return load reads the second slot.
    let (source, mut machine) = memory_pair(MemShape::TwoSlots);
    let leas = find(&machine, X86Opcode::Lea);
    let load = rows_of(&machine, &LOADS)[0];
    let second = inst(&machine, leas[1]).operands[0].clone();
    *memory_operand(&mut machine, load) = O::MemAddr {
        base: Box::new(second),
        disp: 0,
    };
    refuted(&source, &machine, "load from the wrong slot");
    // Wrong slot offset: the first field read at offset 8.
    let (source, mut machine) = memory_pair(MemShape::SlotHalves);
    let load = rows_of(&machine, &LOADS)[0];
    if let O::MemAddr { disp, .. } = memory_operand(&mut machine, load) {
        *disp = 4;
    }
    // Bytes 4..12 of an 8-byte slot: outside the slot.
    expect_mismatch(&source, &machine, "out-of-slot read", |mismatch| {
        matches!(mismatch, X86BodyMismatch::StackSlotBounds { .. })
    });
    let (source, mut machine) = memory_pair(MemShape::SlotPair);
    let load = rows_of(&machine, &LOADS)[1];
    let base = match memory_operand(&mut machine, load) {
        O::MemAddr { base, .. } => base.as_ref().clone(),
        other => panic!("{other:?}"),
    };
    let first_lea = find(&machine, X86Opcode::Lea)[0];
    let slot_base = inst(&machine, first_lea).operands[0].clone();
    assert_ne!(
        base, slot_base,
        "the second field is addressed through the offset"
    );
    *memory_operand(&mut machine, load) = O::MemAddr {
        base: Box::new(slot_base),
        disp: 0,
    };
    refuted(&source, &machine, "second field read at offset 0");
    // Wrong incoming offset: the field load at +0 instead of +8. The exact
    // affine check names it; the theorem refutes it too.
    let (source, mut machine) = memory_pair(MemShape::FieldLoad);
    let address = rows(&machine)
        .into_iter()
        .map(|(row, _, _)| row)
        .find(|row| byte_address_inputs(inst(&machine, *row)).is_some())
        .expect("the field's byte address");
    let pointer = byte_address_inputs(inst(&machine, address))
        .unwrap()
        .0
        .clone();
    let load = rows_of(&machine, &LOADS)[0];
    *memory_operand(&mut machine, load) = O::MemAddr {
        base: Box::new(pointer),
        disp: 0,
    };
    expect_mismatch(&source, &machine, "field at +0", |mismatch| {
        *mismatch == X86BodyMismatch::MemoryAddress { access: 0 }
    });
    refuted(&source, &machine, "field at +0");
    // Wrong width, private: an 8-byte slot written with 4 bytes, read with 8.
    let (source, mut machine) = memory_pair(MemShape::LocalRoundTrip);
    let store = rows_of(&machine, &STORES)[0];
    inst_mut(&mut machine, store).opcode = X86Opcode::MovMR32;
    refuted(&source, &machine, "4-byte store of an 8-byte local");
    // Wrong width, incoming: an 8-byte store lowered as 4 bytes (and 8 for
    // 4) does not follow the source's trace.
    let (source, mut machine) = memory_pair(MemShape::StoreU64);
    let store = rows_of(&machine, &STORES)[0];
    inst_mut(&mut machine, store).opcode = X86Opcode::MovMR32;
    trace_refused(&source, &machine, "4-byte store of a u64");
    let (source, mut machine) = memory_pair(MemShape::StoreU32);
    let store = rows_of(&machine, &STORES)[0];
    inst_mut(&mut machine, store).opcode = X86Opcode::MovMR;
    // An 8-byte store of the u32's 32-bit register is outside the domain
    // (it would read bits the register does not name); of the 64-bit
    // argument register, it does not follow the source's 4-byte trace.
    expect_unsupported(&source, &machine, "8-byte store of a 32-bit register");
    inst_mut(&mut machine, store).operands[1] = preg(RSI);
    trace_refused(&source, &machine, "8-byte store of a u32");
}

#[test]
fn missing_or_misdirected_stores_are_refused() {
    // Missing incoming store: nothing is credited.
    let (source, mut machine) = memory_pair(MemShape::StoreU64);
    let store = rows_of(&machine, &STORES)[0];
    remove_at(&mut machine, store);
    trace_refused(&source, &machine, "missing store");
    // Missing private store: the load reads bytes the body never wrote.
    let (source, mut machine) = memory_pair(MemShape::LocalRoundTrip);
    let store = rows_of(&machine, &STORES)[0];
    remove_at(&mut machine, store);
    refuted(&source, &machine, "missing slot store");
    // A store through the wrong pointer.
    let (source, mut machine) = memory_pair(MemShape::TwoStores);
    let stores = rows_of(&machine, &STORES);
    let other = match memory_operand(&mut machine, stores[1]) {
        O::MemAddr { base, .. } => base.as_ref().clone(),
        operand => panic!("{operand:?}"),
    };
    *memory_operand(&mut machine, stores[0]) = O::MemAddr {
        base: Box::new(other),
        disp: 0,
    };
    expect_mismatch(
        &source,
        &machine,
        "store to the wrong pointer",
        |mismatch| *mismatch == X86BodyMismatch::MemoryAddress { access: 0 },
    );
    refuted(&source, &machine, "store to the wrong pointer");
    // A store of the wrong value.
    let (source, mut machine) = memory_pair(MemShape::TwoStores);
    let stores = rows_of(&machine, &STORES);
    let other_value = inst(&machine, stores[1]).operands[1].clone();
    inst_mut(&mut machine, stores[0]).operands[1] = other_value;
    expect_mismatch(&source, &machine, "wrong stored value", |mismatch| {
        *mismatch == X86BodyMismatch::MemoryValue { access: 0 }
    });
    refuted(&source, &machine, "wrong stored value");
}

#[test]
fn reordering_and_aliasing_assumptions_are_refused() {
    // A load moved before the store it may depend on (a and b may alias).
    let (source, mut machine) = memory_pair(MemShape::StoreThenLoad);
    let store = rows_of(&machine, &STORES)[0];
    let load = rows_of(&machine, &LOADS)[0];
    assert!(store < load);
    let moved = remove_at(&mut machine, load);
    insert_at(&mut machine, store, moved);
    trace_refused(&source, &machine, "load before the store");
    // A lowering that assumes `a` and `b` never alias: it returns `x` for
    // `*a` after `*b = y` instead of reloading. It keeps the reload (so the
    // trace matches) but returns the stored register.
    let (source, mut machine) = memory_pair(MemShape::StoresReload);
    let stores = rows_of(&machine, &STORES);
    let stored = inst(&machine, stores[0]).operands[1].clone();
    let ret_copy = *find(&machine, X86Opcode::MovRR).last().unwrap();
    inst_mut(&mut machine, ret_copy).operands[1] = stored;
    refuted(
        &source,
        &machine,
        "store-to-load forwarding across a may-alias store",
    );
    // The model assumes no disjointness either way: two stores in the
    // other order are a different trace, never credited.
    let (source, mut machine) = memory_pair(MemShape::TwoStores);
    let stores = rows_of(&machine, &STORES);
    let first = remove_at(&mut machine, stores[0]);
    insert_at(&mut machine, stores[1], first);
    trace_refused(&source, &machine, "stores reordered");
    // The addresses permuted but the values left in place (`*b = x; *a =
    // y` for `*a = x; *b = y`) is not a reordering: it writes the wrong value
    // to both locations whenever `a != b`, and is named.
    let (source, mut machine) = memory_pair(MemShape::TwoStores);
    let stores = rows_of(&machine, &STORES);
    let (a, b) = (
        memory_operand(&mut machine, stores[0]).clone(),
        memory_operand(&mut machine, stores[1]).clone(),
    );
    *memory_operand(&mut machine, stores[0]) = b;
    *memory_operand(&mut machine, stores[1]) = a;
    expect_mismatch(
        &source,
        &machine,
        "addresses permuted, values not",
        |mismatch| *mismatch == X86BodyMismatch::MemoryAddress { access: 0 },
    );
    refuted(&source, &machine, "addresses permuted, values not");
    // Two stores to ONE location never trade places: `*a = y; *a = x` for
    // `*a = x; *a = y` leaves the other value there.
    let (mut source, mut machine) = memory_pair(MemShape::TwoStores);
    let entry = source.entry_block;
    for inst in &mut source.blocks.get_mut(&entry).unwrap().instructions {
        if matches!(inst.opcode, L::Store { .. }) {
            inst.args[1] = Value(0);
        }
    }
    let stores = rows_of(&machine, &STORES);
    let a = memory_operand(&mut machine, stores[0]).clone();
    *memory_operand(&mut machine, stores[1]) = a;
    assert!(source_bound_x86_body(&source, &machine, SYSV).is_ok());
    let (x, y) = (
        inst(&machine, stores[0]).operands[1].clone(),
        inst(&machine, stores[1]).operands[1].clone(),
    );
    inst_mut(&mut machine, stores[0]).operands[1] = y;
    inst_mut(&mut machine, stores[1]).operands[1] = x;
    expect_mismatch(
        &source,
        &machine,
        "same-location stores swapped",
        |mismatch| *mismatch == X86BodyMismatch::MemoryValue { access: 0 },
    );
    refuted(&source, &machine, "same-location stores swapped");
}

/// Turn the first zero-extending load of `machine` into its MERGING sibling
/// (`movzx r32, m8` -> `mov r8, m8`, `movzx r32, m16` -> `mov r16, m16`): the
/// same access at the same address, writing only the low byte/word.
fn merging_load(machine: &mut X86ISelFunction) -> usize {
    let load = rows_of(machine, &[X86Opcode::MovzxRM8, X86Opcode::MovzxRM16])[0];
    let merged = match inst(machine, load).opcode {
        X86Opcode::MovzxRM8 => X86Opcode::MovRM8,
        _ => X86Opcode::MovRM16,
    };
    inst_mut(machine, load).opcode = merged;
    load
}

#[test]
fn a_narrow_load_defines_only_its_low_bits() {
    // `(*p) as u32`: the selector's `movzx r32, m8` writes the whole register,
    // so its value returned through 32-bit copies is the zero extension, and
    // the theorem holds with no free input for the bits above the byte.
    let (source, machine) = memory_pair(MemShape::LoadU8Widened);
    assert!(
        find(&machine, X86Opcode::Movzx).is_empty(),
        "{}",
        describe(&machine)
    );
    let theorem = theorem_without_affine_refusal(&source, &machine, SYSV).unwrap();
    assert!(holds_on_samples(&theorem), "{}", describe(&machine));
    assert!(
        !theorem.inputs.iter().any(|(name, _)| name == "u0"),
        "a zero-extending load leaves no undefined bits: {:?}",
        theorem.inputs
    );
    // The same body with the MERGING `mov r8, m` in its place: it writes only
    // the destination's low byte, so EAX bits 8..31 are a free input and the
    // theorem is refuted.
    let (source, mut machine) = memory_pair(MemShape::LoadU8Widened);
    merging_load(&mut machine);
    refuted(&source, &machine, "u8 merging load returned without movzx");
    // The same for a 16-bit load, whose i16 result observes AX only: the
    // undefined upper bits are not read.
    let (source, mut machine) = memory_pair(MemShape::LoadI16);
    merging_load(&mut machine);
    assert!(
        theorem_without_affine_refusal(&source, &machine, SYSV)
            .map(|theorem| holds_on_samples(&theorem))
            .unwrap_or(false),
        "an i16 result reads AX only"
    );
    // A merging u8 load into a register that already holds zero is still NOT
    // its zero extension: register allocation treats the destination of `mov
    // r8, m` as a pure definition (`first_operand_is_def_and_use` in the
    // x86-64 pipeline), so it may give the load a register holding anything
    // and reuse the zeroed one in between. The bits above the byte stay a
    // free input and the theorem is refuted, never credited.
    let (source, machine) = narrow_load_into_a_zeroed_register();
    let theorem = theorem_without_affine_refusal(&source, &machine, SYSV).unwrap();
    assert!(
        refuted_on_samples(&theorem),
        "a byte loaded into a zeroed register was treated as its zero extension\n{}",
        describe(&machine)
    );
    assert!(
        theorem
            .inputs
            .iter()
            .any(|(name, width)| name == "u0" && *width == 56),
        "the load's upper bits are a free input: {:?}",
        theorem.inputs
    );
    // The same for a merging 16-bit load into a register that holds a value.
    let (source, mut machine) = memory_pair(MemShape::LoadI16);
    let load = merging_load(&mut machine);
    let destination = inst(&machine, load).operands[0].clone();
    insert_at(
        &mut machine,
        load,
        X86ISelInst::new(X86Opcode::MovRI, vec![destination, O::Imm(0)]),
    );
    let theorem = theorem_without_affine_refusal(&source, &machine, SYSV).unwrap();
    assert!(
        theorem
            .inputs
            .iter()
            .any(|(name, width)| name == "u0" && *width == 48),
        "{:?}",
        theorem.inputs
    );
}

/// `(*p) as u32` with `mov r, 0` before a MERGING byte load into the same
/// register: the pre-RA stream reads as a zero extension, but the allocated
/// code need not be one.
fn narrow_load_into_a_zeroed_register() -> (Function, X86ISelFunction) {
    let (source, mut machine) = memory_pair(MemShape::LoadU8Widened);
    let load = merging_load(&mut machine);
    let destination = inst(&machine, load).operands[0].clone();
    insert_at(
        &mut machine,
        load,
        X86ISelInst::new(X86Opcode::MovRI, vec![destination, O::Imm(0)]),
    );
    (source, machine)
}

/// An 8-byte store reads 64 bits of its register operand, so the operand
/// must name 64: register allocation keeps only the low 32 bits of a 32-bit
/// register (a four-byte spill and reload, a coalesced 32-bit copy), so
/// whatever the pre-RA stream holds above them is not what the allocated
/// code stores.
#[test]
fn an_eight_byte_store_reads_a_sixty_four_bit_register() {
    // `*p = x as i64` (x: i8): `movsx r64, r8` then an 8-byte store.
    let (source, machine) = memory_pair(MemShape::StoreWidened);
    let store = rows_of(&machine, &STORES)[0];
    assert_eq!(inst(&machine, store).opcode, X86Opcode::MovMR);
    let extension = find(&machine, X86Opcode::MovsxB)[0];
    let O::VReg(widened) = inst(&machine, extension).operands[0].clone() else {
        panic!("{}", describe(&machine));
    };
    assert_eq!(inst(&machine, store).operands[1], O::VReg(widened));
    assert!(source_bound_x86_body(&source, &machine, SYSV).is_ok());
    // The same stream with the extension's result retyped to a 32-bit
    // register everywhere: the pre-RA walk still reads its sign bits, but
    // the store is outside the domain.
    let mut retyped = machine.clone();
    let narrow = VReg::new(widened.id, RegClass::Gpr32);
    for (ordinal, _, _) in rows(&machine) {
        for operand in &mut inst_mut(&mut retyped, ordinal).operands {
            if *operand == O::VReg(widened) {
                *operand = O::VReg(narrow);
            }
        }
    }
    expect_unsupported(&source, &retyped, "8-byte store of a 32-bit register");
    // The rule is on the width the operand names, for a private slot store
    // and a physical register too: a u64 local stored as 8 bytes of EDI.
    let (source, mut machine) = memory_pair(MemShape::LocalRoundTrip);
    let store = rows_of(&machine, &STORES)[0];
    inst_mut(&mut machine, store).operands[1] = preg(GPR32_ALIAS_BASE + RDI);
    expect_unsupported(&source, &machine, "8-byte slot store of EDI");
    // Narrower stores of a 32-bit register read only bits it names.
    let (source, machine) = memory_pair(MemShape::StoreU32);
    let store = rows_of(&machine, &STORES)[0];
    assert!(matches!(
        inst(&machine, store).operands[1],
        O::VReg(VReg {
            class: RegClass::Gpr32,
            ..
        })
    ));
    assert!(source_bound_x86_body(&source, &machine, SYSV).is_ok());
}

/// The rows of a `B1` load's normalization in `machine`: `(load, add, shr)`,
/// the first byte load (the zero-extending `movzx z, m8`) and the two rows the
/// selector emits after it (`add t, z, 255; shr b, t, 8`).
fn bool_normalization(machine: &X86ISelFunction) -> (usize, usize, usize) {
    let load = rows_of(machine, &[X86Opcode::MovzxRM8])[0];
    let rows = (load, load + 1, load + 2);
    assert_eq!(
        [rows.1, rows.2].map(|row| inst(machine, row).opcode),
        [X86Opcode::AddRI, X86Opcode::ShrRI],
        "{}",
        describe(machine)
    );
    assert_eq!(
        inst(machine, rows.1).operands[1],
        inst(machine, load).operands[0],
        "the add reads exactly the loaded register"
    );
    assert_eq!(inst(machine, rows.1).operands[2], O::Imm(0xFF));
    assert_eq!(inst(machine, rows.2).operands[2], O::Imm(8));
    rows
}

/// Every operand after `from` that is exactly `old` becomes `new`.
fn replace_uses_after(machine: &mut X86ISelFunction, from: usize, old: &O, new: &O) {
    for ordinal in from + 1..rows(machine).len() {
        for operand in &mut inst_mut(machine, ordinal).operands {
            if operand == old {
                *operand = new.clone();
            }
        }
    }
}

/// `shape` with the `!= 0` of its bool load deleted: every use of the
/// normalized bool reads the zero-extended loaded byte instead, so the byte
/// itself is the bool (the selection before this backend computed `!= 0`).
fn bool_load_as_its_byte(shape: MemShape) -> (Function, X86ISelFunction) {
    let (source, mut machine) = memory_pair(shape);
    let (load, add, shr) = bool_normalization(&machine);
    let byte = inst(&machine, load).operands[0].clone();
    let truth = inst(&machine, shr).operands[0].clone();
    replace_uses_after(&mut machine, shr, &truth, &byte);
    remove_at(&mut machine, shr);
    remove_at(&mut machine, add);
    (source, machine)
}

/// `shape` with its bool load's `add 255; shr 8` rewritten to compute
/// another predicate of the byte `m`: `and 1; shr 0` is bit 0 (`m & 1`, the
/// psABI's reading of a valid bool), and `add 254; shr 8` is `m >= 2`.
fn bool_load_with_predicate(
    shape: MemShape,
    predicate: (X86Opcode, i64, i64),
) -> (Function, X86ISelFunction) {
    let (source, mut machine) = memory_pair(shape);
    let (_, add, shr) = bool_normalization(&machine);
    let (opcode, imm, shift) = predicate;
    inst_mut(&mut machine, add).opcode = opcode;
    inst_mut(&mut machine, add).operands[2] = O::Imm(imm);
    inst_mut(&mut machine, shr).operands[2] = O::Imm(shift);
    (source, machine)
}

/// The bytes `m` for which the theorem's two sides disagree when the loaded
/// byte `l0` is `m`, every other free input taking sample `seed`'s value:
/// exhaustive over the byte. Test-only semantics, never credit.
fn disagreeing_bytes(obligation: &ProofObligation, seed: u64) -> Vec<u8> {
    (0..=u8::MAX)
        .filter(|byte| !sides_agree_with(obligation, seed, &[("l0", u64::from(*byte))]))
        .collect()
}

/// The four bool loads from incoming memory.
const BOOL_LOADS: [MemShape; 4] = [
    MemShape::LoadBool,
    MemShape::LoadBoolWidened,
    MemShape::LoadBoolArgument,
    MemShape::BoolFieldLoad,
];

/// A `bool` loaded from incoming memory is the byte `m` read as `m != 0`,
/// trust-ir's `Load Bool` (its reference interpreter's `decode_leaf`), with
/// no premise that `m` is 0 or 1: the paired load input `l0` is the whole
/// byte on both sides. The real selection (`movzx r32, m8; add 255; shr 8`) agrees
/// with the source for every byte; the byte returned or passed as is, its
/// bit 0, and `m >= 2` disagree exactly where those predicates differ from
/// `m != 0`, and the owner still builds each theorem (the Rust walk cannot
/// judge the value), so only the theorem judges them.
#[test]
fn bool_loads_from_incoming_memory_read_the_byte_as_nonzero() {
    for shape in BOOL_LOADS {
        let (source, machine) = memory_pair(shape);
        assert!(source_admits_x86_body_owner(&source, SYSV), "{shape:?}");
        let owner = source_bound_x86_body(&source, &machine, SYSV)
            .unwrap_or_else(|refusal| panic!("{shape:?}: {refusal}\n{}", describe(&machine)));
        assert!(
            owner
                .obligation()
                .inputs
                .iter()
                .any(|(name, width)| name == "l0" && *width == 8),
            "{shape:?}: the loaded byte is an 8-bit input: {:?}",
            owner.obligation().inputs
        );
        for seed in 0..8 {
            assert_eq!(
                disagreeing_bytes(owner.obligation(), seed),
                Vec::<u8>::new(),
                "{shape:?} seed {seed}"
            );
        }
        let every = |predicate: fn(u8) -> bool| -> Vec<u8> {
            (0..=u8::MAX).filter(|m| predicate(*m)).collect()
        };
        let controls: [(&str, (Function, X86ISelFunction), Vec<u8>); 3] = [
            (
                "the byte itself",
                bool_load_as_its_byte(shape),
                every(|m| m >= 2),
            ),
            (
                "bit 0",
                bool_load_with_predicate(shape, (X86Opcode::AndRI, 1, 0)),
                every(|m| m != 0 && m % 2 == 0),
            ),
            (
                "m >= 2",
                bool_load_with_predicate(shape, (X86Opcode::AddRI, 0xFE, 8)),
                vec![1],
            ),
        ];
        for (label, (source, machine), expected) in controls {
            let owner = source_bound_x86_body(&source, &machine, SYSV).unwrap_or_else(|refusal| {
                panic!("{shape:?} {label}: {refusal}\n{}", describe(&machine))
            });
            for seed in 0..8 {
                assert_eq!(
                    disagreeing_bytes(owner.obligation(), seed),
                    expected,
                    "{shape:?} {label} seed {seed}"
                );
            }
        }
    }
    // A bool store stays in the domain: its byte is 0 or 1 by construction.
    let (source, machine) = memory_pair(MemShape::StoreBool);
    assert!(source_bound_x86_body(&source, &machine, SYSV).is_ok());
}

/// `LocalBool` with the selector's normalization deleted and the return copy
/// reading the loaded register: with the zero-extending load, `movzx r32, m8;
/// mov eax, r32`; with `merge`, the merging `mov r8, m; mov eax, r32`, the
/// lowering the selector emitted before it zero-extended `B1` loads.
fn slot_bool_without_normalization(merge: bool) -> (Function, X86ISelFunction) {
    let (source, mut machine) = memory_pair(MemShape::LocalBool);
    let (load, add, shr) = bool_normalization(&machine);
    let loaded = inst(&machine, load).operands[0].clone();
    let truth = inst(&machine, shr).operands[0].clone();
    replace_uses_after(&mut machine, shr, &truth, &loaded);
    for row in [shr, add] {
        remove_at(&mut machine, row);
    }
    if merge {
        merging_load(&mut machine);
    }
    assert_eq!(
        opcodes(&machine),
        vec![
            X86Opcode::Movzx,
            X86Opcode::Lea,
            X86Opcode::MovMR8,
            if merge {
                X86Opcode::MovRM8
            } else {
                X86Opcode::MovzxRM8
            },
            X86Opcode::MovRR32,
            X86Opcode::Ret
        ],
        "{}",
        describe(&machine)
    );
    (source, machine)
}

/// A private slot's `bool` is loaded with the zero-extending `movzx r32, m8`
/// and normalized (`add 255; shr 8`) before the return: the backend's clean
/// 32-bit bool result (module documentation). The slot byte a bool store
/// wrote is 0 or 1, and the real selection proves. So does the zero-extended
/// byte returned without the normalization (the slot's byte is 0 or 1, and
/// the load writes the whole register). The MERGING `mov r8, m; mov eax, r32`
/// leaves EAX bits 8..31 whatever the load's destination register held, and
/// the exact load model refutes it: the owner still builds the theorem (the
/// Rust check cannot judge the undefined carrier bits) and the covered rows
/// fail, never credit.
#[test]
fn a_slot_bool_returned_without_extension_is_refuted() {
    use X86Opcode::*;
    let (source, machine) = memory_pair(MemShape::LocalBool);
    assert_eq!(
        opcodes(&machine),
        // (slice 15: the `bool` parameter is the `movzx` of EDI's low byte)
        vec![Movzx, Lea, MovMR8, MovzxRM8, AddRI, ShrRI, MovRR32, Ret],
        "{}",
        describe(&machine)
    );
    let _ = bool_normalization(&machine);
    let owner = source_bound_x86_body(&source, &machine, SYSV).unwrap();
    assert!(holds_on_samples(owner.obligation()));
    let (source, machine) = slot_bool_without_normalization(false);
    let owner = source_bound_x86_body(&source, &machine, SYSV).unwrap();
    assert!(
        holds_on_samples(owner.obligation()),
        "a zero-extended slot bool byte is the clean bool"
    );
    let (source, machine) = slot_bool_without_normalization(true);
    let owner = source_bound_x86_body(&source, &machine, SYSV)
        .expect("admitted: the Rust walk cannot judge the undefined carrier bits");
    assert!(refuted_on_samples(owner.obligation()));
    // The theorem's machine side reads a free input for the bits above the
    // loaded byte (construction, read in slice 18's spelling: slice 19's
    // spelling drops the psABI claim's read of them, which its low byte
    // never depends on).
    let owner = with_normal_groups(normal::Groups::NONE, || {
        source_bound_x86_body(&source, &machine, SYSV).expect("admitted")
    });
    assert!(
        owner
            .obligation()
            .inputs
            .iter()
            .any(|(name, width)| name == "u0" && *width == 56),
        "{:?}",
        owner.obligation().inputs
    );
}

#[test]
fn private_slots_are_unobservable_and_incoming_stores_are_observable() {
    // A dead private store may be dropped, or an extra one added: the slot
    // is private, so neither changes the theorem's truth.
    let (source, mut machine) = memory_pair(MemShape::DeadSlotStore);
    let store = rows_of(&machine, &STORES)[0];
    remove_at(&mut machine, store);
    let owner = source_bound_x86_body(&source, &machine, SYSV).unwrap();
    assert!(holds_on_samples(owner.obligation()));
    let (source, mut machine) = memory_pair(MemShape::LocalRoundTrip);
    let store = rows_of(&machine, &STORES)[0];
    let slot = inst(&machine, find(&machine, X86Opcode::Lea)[0]).operands[0].clone();
    let load = rows_of(&machine, &LOADS)[0];
    let stored = inst(&machine, store).operands[1].clone();
    // After the load, store into the slot again: nobody reads it.
    insert_at(
        &mut machine,
        load + 1,
        X86ISelInst::new(
            X86Opcode::MovMR,
            vec![
                O::MemAddr {
                    base: Box::new(slot),
                    disp: 0,
                },
                stored,
            ],
        ),
    );
    let owner = source_bound_x86_body(&source, &machine, SYSV).unwrap();
    assert!(holds_on_samples(owner.obligation()));
    // An incoming store redirected into the private slot is not made: the
    // caller never sees it, and the trace refuses the body.
    let (source, mut machine) = memory_pair(MemShape::SlotToStore);
    let stores = rows_of(&machine, &STORES);
    let slot = inst(&machine, find(&machine, X86Opcode::Lea)[0]).operands[0].clone();
    *memory_operand(&mut machine, stores[1]) = O::MemAddr {
        base: Box::new(slot),
        disp: 0,
    };
    trace_refused(
        &source,
        &machine,
        "incoming store made into the private slot",
    );
    // A slot address that escapes into a call is outside the domain.
    let (source, mut machine) = memory_pair(MemShape::StoreCall);
    let call = find(&machine, X86Opcode::Call)[0];
    let setup = setup_row(&machine, 0, RDI);
    inst_mut(&mut machine, setup).opcode = X86Opcode::Lea;
    inst_mut(&mut machine, setup).operands[1] = O::MemAddr {
        base: Box::new(O::StackSlot(0)),
        disp: 0,
    };
    assert!(call > setup);
    expect_unsupported(&source, &machine, "slot address passed to a call");
}

#[test]
fn a_call_threads_memory_and_accesses_never_cross_it() {
    // The second load moved before the call: the callee may write `*p`.
    let (source, mut machine) = memory_pair(MemShape::LoadCallLoad);
    let call = find(&machine, X86Opcode::Call)[0];
    let loads = rows_of(&machine, &LOADS);
    assert!(loads[0] < call && call < loads[1], "{}", describe(&machine));
    let moved = remove_at(&mut machine, loads[1]);
    insert_at(&mut machine, loads[0] + 1, moved);
    trace_refused(&source, &machine, "load moved across the call");
    // The first load's value reused after the call (no reload).
    let (source, mut machine) = memory_pair(MemShape::LoadCallLoad);
    let loads = rows_of(&machine, &LOADS);
    let first = inst(&machine, loads[0]).operands[0].clone();
    let reload = remove_at(&mut machine, loads[1]);
    insert_at(
        &mut machine,
        loads[1],
        X86ISelInst::new(X86Opcode::MovRR, vec![reload.operands[0].clone(), first]),
    );
    trace_refused(&source, &machine, "pre-call load reused after the call");
    // A store moved after the call: the callee may read `*p`.
    let (source, mut machine) = memory_pair(MemShape::StoreCall);
    let store = rows_of(&machine, &STORES)[0];
    let call = find(&machine, X86Opcode::Call)[0];
    let moved = remove_at(&mut machine, store);
    insert_at(&mut machine, call, moved);
    trace_refused(&source, &machine, "store moved across the call");
}

#[test]
fn struct_field_offsets_and_sret_returns_are_judged() {
    // A field read at the wrong offset (16 for 8): the exact affine check
    // names it, and the theorem refutes it.
    let (source, mut machine) = memory_pair(MemShape::StructField);
    let lea = find(&machine, X86Opcode::Lea)[0];
    if let O::MemAddr { disp, .. } = &mut inst_mut(&mut machine, lea).operands[1] {
        *disp = 16;
    }
    expect_mismatch(&source, &machine, "field at +16", |mismatch| {
        *mismatch == X86BodyMismatch::MemoryAddress { access: 0 }
    });
    refuted(&source, &machine, "field at +16");
    // A private field read at the wrong offset reads the other field.
    let (source, mut machine) = memory_pair(MemShape::SlotStructField);
    let lea = find(&machine, X86Opcode::Lea)[1];
    if let O::MemAddr { disp, .. } = &mut inst_mut(&mut machine, lea).operands[1] {
        *disp = 0;
    }
    refuted(&source, &machine, "private field at +0");
    // An sret function must return its buffer in RAX (System V).
    let (source, mut machine) = memory_pair(MemShape::SretPair);
    let ret_copy = *find(&machine, X86Opcode::MovRR).last().unwrap();
    assert_eq!(inst(&machine, ret_copy).operands[0], preg(RAX));
    let mut dropped = machine.clone();
    remove_at(&mut dropped, ret_copy);
    expect_mismatch(&source, &dropped, "sret without RAX", |mismatch| {
        *mismatch == X86BodyMismatch::UndefinedReturn { register: "rax" }
    });
    inst_mut(&mut machine, ret_copy).operands[1] = vreg(2);
    expect_mismatch(&source, &machine, "sret returning a value", |mismatch| {
        *mismatch == X86BodyMismatch::ReturnValue { lane: 0 }
    });
    // Only a leading buffer of a function with no return value is admitted.
    let mut late = memory_lir(MemShape::SretPair);
    late.abi_sret_param = Some(trust_cg_lower::function::AbiSretParam { param_index: 1 });
    assert!(!source_admits_x86_body_owner(&late, SYSV));
}

/// The verify-owned C layout agrees with the LIR's own `Type::offset_of` on
/// every field of a set of struct and array types (it is computed
/// independently, so a shared layout bug would show as a refuted theorem).
#[test]
fn verify_owned_field_offsets_agree_with_the_lir_layout() {
    let types = [
        Type::Struct(vec![Type::I64, Type::I64]),
        Type::Struct(vec![Type::I8, Type::I64, Type::I16]),
        Type::Struct(vec![Type::I32, Type::I16, Type::I16]),
        Type::Struct(vec![Type::I64, Type::I8, Type::B1, Type::B1, Type::B1]),
        Type::Struct(vec![
            Type::B1,
            Type::Struct(vec![Type::I8, Type::I32]),
            Type::I8,
        ]),
        Type::Struct(vec![
            Type::I8,
            Type::Array(Box::new(Type::I16), 3),
            Type::I64,
        ]),
        Type::Struct(vec![Type::I8, Type::I128]),
        Type::Array(Box::new(Type::I64), 4),
        Type::Array(Box::new(Type::I32), 4),
        Type::Array(Box::new(Type::Struct(vec![Type::I32, Type::I8])), 3),
    ];
    for ty in types {
        let count = match &ty {
            Type::Struct(fields) => fields.len() as u32,
            Type::Array(_, count) => *count,
            _ => unreachable!(),
        };
        for index in 0..count {
            assert_eq!(
                field_offset(&ty, index),
                ty.offset_of(index as usize).map(u64::from),
                "{ty:?} field {index}"
            );
        }
        assert_eq!(field_offset(&ty, count), None, "{ty:?} past the end");
    }
}

#[test]
fn memory_rows_outside_the_slice_four_domain_are_unsupported() {
    // A SIB load or store with a PHYSICAL index (slice 25 states only SIB
    // rows whose base and index are virtual or a stack-slot base), a
    // volatile load, a store of an address into memory, and a slot table
    // disagreement make no claim.
    let (source, mut machine) = memory_pair(MemShape::LoadU64);
    let load = rows_of(&machine, &LOADS)[0];
    inst_mut(&mut machine, load).opcode = X86Opcode::VolatileMovRM;
    expect_unsupported(&source, &machine, "volatile load row");
    let sib = |base: O| O::SibMemAddr {
        base: Box::new(base),
        index: Box::new(preg(RSI)),
        scale: 1,
        disp: 0,
    };
    let (source, mut machine) = memory_pair(MemShape::LoadU64);
    let load = rows_of(&machine, &LOADS)[0];
    let base = match memory_operand(&mut machine, load) {
        O::MemAddr { base, .. } => base.as_ref().clone(),
        other => panic!("{other:?}"),
    };
    *memory_operand(&mut machine, load) = sib(base);
    inst_mut(&mut machine, load).opcode = X86Opcode::MovRMSib;
    expect_unsupported(&source, &machine, "SIB load row");
    let (source, mut machine) = memory_pair(MemShape::StoreU64);
    let store = rows_of(&machine, &STORES)[0];
    let base = match memory_operand(&mut machine, store) {
        O::MemAddr { base, .. } => base.as_ref().clone(),
        other => panic!("{other:?}"),
    };
    *memory_operand(&mut machine, store) = sib(base);
    inst_mut(&mut machine, store).opcode = X86Opcode::MovMRSib;
    expect_unsupported(&source, &machine, "SIB store row");
    let (source, mut machine) = memory_pair(MemShape::LocalRoundTrip);
    machine
        .stack_slots
        .push(trust_cg_lower::StackSlotInfo::new(8, 8));
    expect_unsupported(&source, &machine, "machine slot table differs");
    // The slot's address stored where the source stores a value: slice 13
    // states a stored private address as data (the slot's address term), so
    // the theorem refutes it against the value.
    let (source, mut machine) = memory_pair(MemShape::SlotToStore);
    let stores = rows_of(&machine, &STORES);
    let slot = inst(&machine, find(&machine, X86Opcode::Lea)[0]).operands[0].clone();
    inst_mut(&mut machine, stores[1]).operands[1] = slot;
    assert_theorem_refutes(&source, &machine, "slot address stored for a value");
}

// ---------------------------------------------------------------------------
// Canonical SMT2 (golden file with a reviewed digest pin)
// ---------------------------------------------------------------------------

/// Re-pinned 2026-09-30 for the zero-extending narrow loads (`movzx r32,
/// m8/m16`): the nine shapes with a byte or word load (`LoadU8`, `LoadI16`,
/// `LoadU8Widened`, `LocalU8`, `LocalBool` and the four bool loads) lose the
/// free input `u0` above the loaded bytes (the load writes the whole register)
/// and the register `movzx` row; the other 26 entries are byte-identical.
const MEMORY_SNAPSHOT_SHA256: &str =
    "45a5b165ca2b0db8fa12fab872072dbb239fa0cea4f5a761c0f3e40ddcf4c55a";

#[test]
fn memory_smt2_is_canonical_per_shape() {
    use sha2::{Digest, Sha256};
    const GOLDEN: &str =
        include_str!("../tests/fixtures/x86_source_bound_body/memory_snapshots.smt2");
    let mut rendered = String::new();
    for shape in MEMORY_SHAPES {
        let (source, machine) = memory_pair(shape);
        let owner = source_bound_x86_body(&source, &machine, SYSV).unwrap();
        let smt2 = generate_smt2_query_raw(owner.obligation(), &replay_config());
        rendered.push_str(&format!(";;;; {shape:?}\n{smt2}\n"));
        let (mut source, mut machine) = (source.clone(), machine.clone());
        source.name = "renamed_function".into();
        machine.name = "renamed_function".into();
        let renamed = source_bound_x86_body(&source, &machine, SYSV).unwrap();
        assert_eq!(
            generate_smt2_query_raw(renamed.obligation(), &replay_config()),
            smt2
        );
    }
    if std::env::var_os("TCG_X86_BODY_SNAPSHOT_WRITE").is_some() {
        let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("tests/fixtures/x86_source_bound_body/memory_snapshots.smt2");
        std::fs::write(&path, &rendered).unwrap();
        panic!(
            "rewrote {}; review its diff, set MEMORY_SNAPSHOT_SHA256 to {:x} and re-run without \
             TCG_X86_BODY_SNAPSHOT_WRITE",
            path.display(),
            Sha256::digest(rendered.as_bytes())
        );
    }
    assert_eq!(
        format!("{:x}", Sha256::digest(GOLDEN.as_bytes())),
        MEMORY_SNAPSHOT_SHA256,
        "the golden file changed without the reviewed digest pin"
    );
    assert_eq!(rendered, GOLDEN, "memory snapshots drifted");
}

#[test]
#[ignore]
fn print_memory_fixtures() {
    for shape in all_memory_shapes() {
        let (source, machine) = memory_pair(shape);
        println!("==== {shape:?}\n{}", describe(&machine));
        match source_bound_x86_body(&source, &machine, SYSV) {
            Ok(owner) => println!(
                "{}",
                generate_smt2_query_raw(owner.obligation(), &replay_config())
            ),
            Err(refusal) => println!("REFUSED {refusal}"),
        }
    }
}

// ---------------------------------------------------------------------------
// Host qualification and verifier credit (tool-gated: real AY + Clean)
// ---------------------------------------------------------------------------

/// Slice-4 fixture shapes whose canonical theorem the qualified AY/Clean pair
/// does NOT certify: a recorded replayer gap, never a credit route. Empty on
/// the qualification host ([`QUALIFIED_AY`], Clean 5f09e36c): every FIXTURE
/// shape certifies. Admitted bodies beyond the fixtures do not all certify
/// (LIMITATIONS.md records the measured corpus and `core` gaps with their
/// exact tool output); their rows stay Unverified.
pub(crate) const KNOWN_UNCERTIFIED_MEMORY: &[Uncertified] = &[];

/// The encodings slice 4 did NOT choose, restated for three representative
/// shapes and replayed on the qualification host: evidence for the one
/// canonical encoding (the Ackermann-reduced access trace), never a credit
/// route. `Array` is one `(Array (_ BitVec 64) (_ BitVec 8))` incoming
/// memory with `store` chains and the final memory observed at a free
/// address; `ByteUf` is the initial memory as a 1-ary uninterpreted function
/// under `ite` store chains. The canonical trace theorem of every shape
/// certifies on both qualification pairs. With AY build 10530, which chose
/// the encoding, none of the six certified: five were rejected by AY's own
/// strict certification (`computed UNSAT rejected by mandatory strict
/// certification: strict UNSAT proof validation failed: step t0/t1 uses
/// unverified trust rule` / `unknown`), and the array form of `load` was
/// refused at publication (`required UNSAT publication failed: refusing to
/// write unverifiable proof ... (#8821): invalid surface congruence step
/// t27: printed congruence operands are not position-preserving congruence
/// over exact multiplication commutations; left="(select mem0 (bvadd p0 (_
/// bv7 64)))"`, AY exit status 1). With AY build 12713, and with
/// [`QUALIFIED_AY`] (build 13556), five certify and only the byte-UF form of
/// `store_then_load` is still rejected by AY's strict self-check. The
/// canonical encoding is kept: it is the one every fixture shape certifies
/// on every pair, and an encoding is never chosen per AY or per function.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum MemoryEncoding {
    Array,
    ByteUf,
}

/// `(shape label, encoding, measured outcome class)` for
/// [`encoding_evidence`] (see [`outcome_class`]).
pub(super) const MEMORY_ENCODING_OUTCOMES: &[(&str, MemoryEncoding, &str)] = &[
    ("store", MemoryEncoding::Array, "Verified"),
    ("store", MemoryEncoding::ByteUf, "Verified"),
    ("load", MemoryEncoding::Array, "Verified"),
    ("load", MemoryEncoding::ByteUf, "Verified"),
    ("store_then_load", MemoryEncoding::Array, "Verified"),
    (
        "store_then_load",
        MemoryEncoding::ByteUf,
        "self-check-rejected",
    ),
];

/// A stable class of a non-certifying outcome: the exact outcome text of an
/// AY publication refusal carries its wall time.
fn outcome_class(result: &AYResult) -> String {
    let outcome = stable_outcome(result);
    if outcome == SELF_CHECK_REJECTED {
        "self-check-rejected".into()
    } else if matches!(result, AYResult::Error(text)
        if text.contains("required UNSAT publication failed") && text.contains("(#8821)"))
    {
        "publication-refused-8821".into()
    } else {
        outcome
    }
}

/// A side's incoming memory under one of the rejected encodings.
struct EvidenceMemory {
    encoding: MemoryEncoding,
    side: char,
    /// Array: the current array term.
    array: E,
    /// ByteUf: the byte stores so far.
    stores: Vec<(E, E)>,
    definitions: Vec<E>,
}

impl EvidenceMemory {
    fn new(encoding: MemoryEncoding, side: char) -> Self {
        Self {
            encoding,
            side,
            array: E::uf("mem0", vec![], crate::memory_proofs::memory_sort()),
            stores: Vec::new(),
            definitions: Vec::new(),
        }
    }

    fn at(address: &E, offset: u64) -> E {
        if offset == 0 {
            address.clone()
        } else {
            address.clone().bvadd(E::bv_const(offset, 64))
        }
    }

    fn store(&mut self, address: &E, value: &E, bytes: u64) {
        for byte in 0..bytes {
            let data = value.clone().extract(8 * byte as u32 + 7, 8 * byte as u32);
            match self.encoding {
                MemoryEncoding::Array => {
                    self.array = E::store(self.array.clone(), Self::at(address, byte), data)
                }
                MemoryEncoding::ByteUf => self.stores.push((Self::at(address, byte), data)),
            }
        }
        if self.encoding == MemoryEncoding::Array {
            let name = E::uf(
                format!("{}mem{}", self.side, self.definitions.len()),
                vec![],
                crate::memory_proofs::memory_sort(),
            );
            self.definitions
                .push(name.clone().eq_expr(self.array.clone()));
            self.array = name;
        }
    }

    fn byte(&self, address: E) -> E {
        match self.encoding {
            MemoryEncoding::Array => E::select(self.array.clone(), address),
            MemoryEncoding::ByteUf => {
                let mut value = E::uf(
                    "mem0",
                    vec![address.clone()],
                    crate::smt::SmtSort::BitVec(8),
                );
                for (at, data) in &self.stores {
                    value = E::ite(address.clone().eq_expr(at.clone()), data.clone(), value);
                }
                value
            }
        }
    }

    fn load(&self, address: &E, bytes: u64) -> E {
        concat_bytes(
            (0..bytes)
                .map(|byte| self.byte(Self::at(address, byte)))
                .collect(),
        )
    }
}

/// The rejected encodings of three u64 shapes: `store` (`*p = v`), `load`
/// (`*p`) and `store_then_load` (`*a = x; *b`, which may alias).
pub(super) fn encoding_evidence(label: &str, encoding: MemoryEncoding) -> ProofObligation {
    let entries = ["e_rdi", "e_rsi", "e_rdx"];
    let arguments = match label {
        "store" => 2,
        "load" => 1,
        _ => 3,
    };
    let mut definitions: Vec<E> = Vec::new();
    let mut inputs: Vec<(String, u32)> = entries[..arguments]
        .iter()
        .map(|name| ((*name).to_owned(), 64))
        .collect();
    let mut side_values = |side: char| {
        (0..arguments)
            .map(|i| {
                let name = format!("{side}{i}");
                definitions.push(E::var(&name, 64).eq_expr(E::var(entries[i], 64)));
                inputs.push((name.clone(), 64));
                E::var(name, 64)
            })
            .collect::<Vec<_>>()
    };
    let source = side_values('p');
    let machine = side_values('m');
    let (mut source_memory, mut machine_memory) = (
        EvidenceMemory::new(encoding, 's'),
        EvidenceMemory::new(encoding, 'm'),
    );
    let goal = match label {
        "store" => {
            source_memory.store(&source[0], &source[1], 8);
            machine_memory.store(&machine[0], &machine[1], 8);
            inputs.push(("obs".into(), 64));
            let observe = E::var("obs", 64);
            source_memory
                .byte(observe.clone())
                .eq_expr(machine_memory.byte(observe))
        }
        "load" => source_memory
            .load(&source[0], 8)
            .eq_expr(machine_memory.load(&machine[0], 8)),
        _ => {
            source_memory.store(&source[0], &source[2], 8);
            machine_memory.store(&machine[0], &machine[2], 8);
            source_memory
                .load(&source[1], 8)
                .eq_expr(machine_memory.load(&machine[1], 8))
        }
    };
    definitions.extend(source_memory.definitions);
    definitions.extend(machine_memory.definitions);
    // `negated_equivalence` nests the last precondition outermost.
    definitions.reverse();
    ProofObligation {
        name: format!("slice-4 encoding evidence: {label} ({encoding:?})"),
        trust_ir_expr: E::bool_const(true),
        aarch64_expr: goal,
        inputs,
        preconditions: definitions,
        fp_inputs: Vec::new(),
        category: Some(TransvalCheckKind::InstructionLowering),
        machine_side_provenance: MachineSideProvenance::StaticDb,
    }
}

/// Wrong lowerings of slice-4 shapes, with the Rust refusal bypassed: the
/// replayed theorem must be refuted by AY with a counterexample.
pub(super) fn memory_refutations() -> Vec<(&'static str, Function, X86ISelFunction)> {
    let mut cases = Vec::new();
    let (source, mut machine) = memory_pair(MemShape::TwoSlots);
    let leas = find(&machine, X86Opcode::Lea);
    let load = rows_of(&machine, &LOADS)[0];
    let second = inst(&machine, leas[1]).operands[0].clone();
    *memory_operand(&mut machine, load) = O::MemAddr {
        base: Box::new(second),
        disp: 0,
    };
    cases.push(("load from the wrong slot", source, machine));
    let (source, mut machine) = memory_pair(MemShape::LocalRoundTrip);
    let store = rows_of(&machine, &STORES)[0];
    remove_at(&mut machine, store);
    cases.push(("missing slot store", source, machine));
    let (source, mut machine) = memory_pair(MemShape::LocalRoundTrip);
    let store = rows_of(&machine, &STORES)[0];
    inst_mut(&mut machine, store).opcode = X86Opcode::MovMR32;
    cases.push(("4-byte store of an 8-byte local", source, machine));
    let (source, mut machine) = memory_pair(MemShape::FieldLoad);
    let address = rows(&machine)
        .into_iter()
        .map(|(row, _, _)| row)
        .find(|row| byte_address_inputs(inst(&machine, *row)).is_some())
        .expect("the field's byte address");
    let pointer = byte_address_inputs(inst(&machine, address))
        .unwrap()
        .0
        .clone();
    let load = rows_of(&machine, &LOADS)[0];
    *memory_operand(&mut machine, load) = O::MemAddr {
        base: Box::new(pointer),
        disp: 0,
    };
    cases.push(("field read at +0 instead of +8", source, machine));
    let (source, mut machine) = memory_pair(MemShape::TwoStores);
    let stores = rows_of(&machine, &STORES);
    let other = match memory_operand(&mut machine, stores[1]) {
        O::MemAddr { base, .. } => base.as_ref().clone(),
        operand => panic!("{operand:?}"),
    };
    *memory_operand(&mut machine, stores[0]) = O::MemAddr {
        base: Box::new(other),
        disp: 0,
    };
    cases.push(("store through the wrong pointer", source, machine));
    let (source, mut machine) = memory_pair(MemShape::TwoStores);
    let stores = rows_of(&machine, &STORES);
    let other_value = inst(&machine, stores[1]).operands[1].clone();
    inst_mut(&mut machine, stores[0]).operands[1] = other_value;
    cases.push(("store of the wrong value", source, machine));
    let (source, mut machine) = memory_pair(MemShape::StoresReload);
    let stores = rows_of(&machine, &STORES);
    let stored = inst(&machine, stores[0]).operands[1].clone();
    let ret_copy = *find(&machine, X86Opcode::MovRR).last().unwrap();
    inst_mut(&mut machine, ret_copy).operands[1] = stored;
    cases.push(("forwarding across a may-alias store", source, machine));
    let (source, mut machine) = memory_pair(MemShape::LoadU8Widened);
    merging_load(&mut machine);
    cases.push(("merging u8 load treated as zero-extending", source, machine));
    let (source, machine) = narrow_load_into_a_zeroed_register();
    cases.push((
        "u8 load into a zeroed register treated as zero-extending",
        source,
        machine,
    ));
    let (source, mut machine) = memory_pair(MemShape::TwoStores);
    let stores = rows_of(&machine, &STORES);
    let (a, b) = (
        memory_operand(&mut machine, stores[0]).clone(),
        memory_operand(&mut machine, stores[1]).clone(),
    );
    *memory_operand(&mut machine, stores[0]) = b;
    *memory_operand(&mut machine, stores[1]) = a;
    cases.push(("store addresses permuted, values not", source, machine));
    let (source, machine) = slot_bool_without_normalization(true);
    cases.push((
        "slot bool merged by mov r8, m and returned without movzx",
        source,
        machine,
    ));
    // An incoming bool byte read as anything but `!= 0`.
    let (source, machine) = bool_load_as_its_byte(MemShape::LoadBool);
    cases.push(("incoming bool returned as its byte", source, machine));
    let (source, machine) = bool_load_as_its_byte(MemShape::LoadBoolArgument);
    cases.push(("incoming bool passed as its byte", source, machine));
    let (source, machine) = bool_load_with_predicate(MemShape::LoadBool, (X86Opcode::AndRI, 1, 0));
    cases.push(("incoming bool read as its bit 0", source, machine));
    let (source, machine) =
        bool_load_with_predicate(MemShape::BoolFieldLoad, (X86Opcode::AddRI, 0xFE, 8));
    cases.push(("incoming bool field read as byte >= 2", source, machine));
    cases
}

/// Step 1 of slice 4: the canonical memory theorems, generated THROUGH THE
/// REAL BUILDER, replay on this host's admitted AY with a Clean-accepted
/// proof; the rejected encodings replay to their recorded outcomes; and
/// every wrong lowering is refuted with a counterexample. The recorded
/// outcomes are compared only under the replayer pair they were measured
/// with ([`assert_qualification_replayer`]): under another pair the test
/// still checks that no correct lowering is refuted and every wrong one is,
/// then fails with a re-qualification message.
#[test]
fn host_qualification_replays_the_memory_body_theorems() {
    let test = "host_qualification_replays_the_memory_body_theorems";
    let edits = replay_environment(test);
    let _serial = crate::ay_bridge::formal_solver_test_lock();
    let dump = std::env::var_os("TCG_X86_BODY_QUALIFY_DUMP").map(std::path::PathBuf::from);
    let (uncertified, outcomes) = with_edits(&edits, || {
        let request = FunctionVerificationRequest::capture(
            VerificationConfig::for_proof_promotion(),
            ProvenanceXCheckMode::Enforce,
        );
        let mut uncertified = Vec::new();
        for shape in MEMORY_SHAPES {
            let label = format!("{shape:?}");
            let (source, machine) = memory_pair(shape);
            let owner = source_bound_x86_body(&source, &machine, SYSV).unwrap();
            if let Some(dir) = &dump {
                std::fs::create_dir_all(dir).unwrap();
                std::fs::write(
                    dir.join(format!("{label}.smt2")),
                    generate_smt2_query_raw(owner.obligation(), &replay_config()),
                )
                .unwrap();
            }
            let started = std::time::Instant::now();
            let result = request
                .ay()
                .verify_fresh_source_bound(&owner, &replay_config());
            eprintln!(
                "X86_BODY_MEMORY_QUALIFICATION shape={label} result={result:?} ms={}",
                started.elapsed().as_millis()
            );
            assert!(
                !matches!(result, AYResult::CounterExample(_)),
                "{label}: a correct lowering was refuted: {result:?}"
            );
            if result != AYResult::Verified {
                eprintln!(
                    "X86_BODY_MEMORY_QUALIFICATION gap={label} outcome={} proof_gate_class={}",
                    stable_outcome(&result),
                    proof_gate_class(&result)
                );
                uncertified.push(label);
            }
        }
        // Evidence for the one canonical encoding.
        let mut outcomes = Vec::new();
        for (label, encoding, _) in MEMORY_ENCODING_OUTCOMES {
            let theorem = encoding_evidence(label, *encoding);
            let result =
                crate::ay_bridge::verify_with_cli_raw_attributed(&theorem, &replay_config()).result;
            eprintln!(
                "X86_BODY_MEMORY_QUALIFICATION encoding={label}/{encoding:?} result={result:?}"
            );
            assert!(
                !matches!(result, AYResult::CounterExample(_)),
                "{label}/{encoding:?}: a correct encoding was refuted: {result:?}"
            );
            outcomes.push((*label, *encoding, outcome_class(&result)));
        }
        // Refutation through the real builder.
        for (label, source, machine) in memory_refutations() {
            let theorem = theorem_without_affine_refusal(&source, &machine, SYSV)
                .unwrap_or_else(|refusal| panic!("{label}: {refusal}"));
            let refuted =
                crate::ay_bridge::verify_with_cli_raw_attributed(&theorem, &replay_config());
            eprintln!(
                "X86_BODY_MEMORY_QUALIFICATION refutation={label} result={:?}",
                refuted.result
            );
            assert!(
                matches!(refuted.result, AYResult::CounterExample(_)),
                "{label} must be refuted: {:?}",
                refuted.result
            );
        }
        (uncertified, outcomes)
    });
    // The pinned outcomes are evidence about one replayer pair: compare them
    // only under that pair.
    let qualified = assert_qualification_replayer(&edits);
    let recorded = super::recorded_gap_labels(
        KNOWN_UNCERTIFIED_MEMORY,
        "KNOWN_UNCERTIFIED_MEMORY",
        &qualified,
    );
    assert_eq!(
        uncertified, recorded,
        "the certified memory set changed on this host: update the recorded replayer gaps \
         (and LIMITATIONS.md) after reviewing each outcome above"
    );
    let recorded: Vec<(&str, MemoryEncoding, String)> = MEMORY_ENCODING_OUTCOMES
        .iter()
        .map(|(label, encoding, outcome)| (*label, *encoding, (*outcome).to_owned()))
        .collect();
    assert_eq!(
        outcomes, recorded,
        "a rejected memory encoding changed outcome on this host; review the encoding note"
    );
}

/// With the real tools, every covered row of every slice-4 shape is Formal
/// under the body theorem (memory rows included), the function is
/// promotable and its exports bind the ABI (the four bool loads from
/// incoming memory included); a slot bool returned without its
/// normalization, an incoming bool returned as its byte and a narrow load
/// into a register that held a value fail their rows; and a wrong lowering
/// the Rust check cannot judge is refuted.
#[test]
fn host_qualification_verifier_credits_every_bound_memory_row_with_the_replayed_body_theorem() {
    let test =
        "host_qualification_verifier_credits_every_bound_memory_row_with_the_replayed_body_theorem";
    let edits = replay_environment(test);
    // The per-host gap view this lane branches on was recorded with one
    // replayer pair: check the pair before the first replay.
    let qualified = assert_qualification_replayer(&edits);
    let _serial = crate::ay_bridge::formal_solver_test_lock();
    with_edits(&edits, || {
        let verifier = promotion_verifier();
        let request = verifier.capture_request_with_mode(ProvenanceXCheckMode::Enforce);
        for shape in MEMORY_SHAPES {
            let (source, machine) = memory_pair(shape);
            let owner = source_bound_x86_body(&source, &machine, SYSV).unwrap();
            let (report, exports) =
                verifier.verify_with_request_for_export(&machine, Some(&source), SYSV, &request);
            // The same per-host view as the gap lane's: a shape with a
            // recorded gap has every bound row awaiting replay.
            if super::gap_applies_here(
                KNOWN_UNCERTIFIED_MEMORY,
                "KNOWN_UNCERTIFIED_MEMORY",
                &format!("{shape:?}"),
                &qualified,
            ) {
                assert_eq!(
                    covered_rows_matching(&owner, report.report(), is_needs_replay),
                    owner.bound_rows().len(),
                    "{shape:?}"
                );
                assert!(!report.report().has_failures(), "{shape:?}");
                assert!(exports.is_empty(), "{shape:?}");
                continue;
            }
            for row in &report.report().instructions {
                if owner.covers(row.inst_index) {
                    assert!(
                        is_body_credit(&row.result),
                        "{shape:?} row {} {:?}: {:?}",
                        row.inst_index,
                        row.opcode,
                        row.result
                    );
                }
            }
            let credited_memory = report
                .report()
                .instructions
                .iter()
                .filter(|row| {
                    matches!(row.opcode,
                        crate::function_verifier::InstructionOpcode::X86_64(opcode)
                            if LOADS.contains(&opcode) || STORES.contains(&opcode))
                        && is_body_credit(&row.result)
                })
                .count();
            assert!(credited_memory > 0, "{shape:?}");
            let inventory = report.report().emitted_opcode_inventory();
            assert!(inventory.is_promotable(), "{shape:?}: {inventory:?}");
            assert_eq!(exports.len(), owner.bound_rows().len(), "{shape:?}");
            assert!(report.matches_x86_input(&machine, Some(&source), SYSV));
        }
        // A slot bool returned without its normalization, an incoming bool
        // returned as its byte and a narrow load into a register that held
        // a value: the replayed theorem is refuted, so every covered row
        // fails and nothing is exported.
        let (local_bool, local_bool_machine) = slot_bool_without_normalization(true);
        for (label, source, machine) in [
            (
                "slot bool merged and without movzx",
                local_bool,
                local_bool_machine,
            ),
            {
                let (source, machine) = bool_load_as_its_byte(MemShape::LoadBool);
                ("incoming bool returned as its byte", source, machine)
            },
            {
                let (source, machine) = narrow_load_into_a_zeroed_register();
                ("narrow load into a zeroed register", source, machine)
            },
        ] {
            let owner = source_bound_x86_body(&source, &machine, SYSV).unwrap();
            let (report, exports) =
                verifier.verify_with_request_for_export(&machine, Some(&source), SYSV, &request);
            assert_eq!(
                covered_rows_matching(&owner, report.report(), |result| matches!(
                    result,
                    InstructionVerificationResult::Failed { proof_name, .. }
                        if proof_name == X86_BODY_OBLIGATION_NAME
                )),
                owner.bound_rows().len(),
                "{label}: {:?}",
                report.report()
            );
            assert!(!report.report().emitted_opcode_inventory().is_promotable());
            assert!(exports.is_empty());
        }
        // A wrong lowering the Rust check cannot judge (forwarding across a
        // may-alias store): refuted, every covered row fails.
        let (source, mut machine) = memory_pair(MemShape::StoresReload);
        let stores = rows_of(&machine, &STORES);
        let stored = inst(&machine, stores[0]).operands[1].clone();
        let ret_copy = *find(&machine, X86Opcode::MovRR).last().unwrap();
        inst_mut(&mut machine, ret_copy).operands[1] = stored;
        let owner = source_bound_x86_body(&source, &machine, SYSV)
            .expect("the loaded value has no affine form, so only the theorem judges it");
        let (report, exports) =
            verifier.verify_with_request_for_export(&machine, Some(&source), SYSV, &request);
        assert_eq!(
            covered_rows_matching(&owner, report.report(), |result| matches!(
                result,
                InstructionVerificationResult::Failed { proof_name, .. }
                    if proof_name == X86_BODY_OBLIGATION_NAME
            )),
            owner.bound_rows().len()
        );
        assert!(exports.is_empty());
    });
}
