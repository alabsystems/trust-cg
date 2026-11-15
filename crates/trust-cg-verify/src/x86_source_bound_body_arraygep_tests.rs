// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! LIR `ArrayGep` in the x86-64 source-bound body theorem (ruling OD-185):
//! an array element's address `base + index * size(elem_ty)` at 64 bits,
//! wrapping, over an incoming pointer, a derived address (OD-114) or, at a
//! constant index, a private stack slot; and the selector's rows for it
//! (`select_array_gep`: a scaled `lea` for a size of 1, 2, 4 or 8, a scaled
//! `lea` and an `add` of the index for 3, 5 or 9, an `imul` and an `add`
//! otherwise).
//!
//! Fixtures are real: LIR from the trust-ir adapter (a trust-ir GEP with two
//! indices is two `ArrayGep`s, each scaled by the pointee's size) and the
//! machine stream from the real x86-64 instruction selector
//! (`super::select`). Wrong lowerings mutate that stream and must end as a
//! typed mismatch, a refuted theorem or an unsupported (uncredited) body,
//! never as Formal credit.
//!
//! Every test here runs without a solver (the
//! `x86_source_bound_body::tests::arraygep::` library gate); the replay on
//! AY and Clean and the verifier credit are in `arraygep_qualification`.

use super::slice5::describe;
use super::slice6::describe_lir;
use super::slice11::{theorem_holds, theorem_refuted};
use super::slice22::fixture_owner;
use super::*;

/// `ArrayGep` fixture shapes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ElementShape {
    // ---- (a) an incoming pointer at variable indices: `p.gep[i, j]`
    /// `fn(p: *const u64, i: u64, j: u64) -> u64 { *p.gep[i, j] }`: two
    /// `lea [b + i*8]`.
    LoadU64,
    /// `-> u32`: `lea [b + i*4]`.
    LoadU32,
    /// `-> u16`: `lea [b + i*2]`.
    LoadU16,
    /// `-> u8`: `lea [b + i]`.
    LoadU8,
    /// A 3-byte element (`[u8; 3]`), its first byte loaded: `lea [b +
    /// i*2]; add i`.
    LoadStride3,
    /// A 12-byte element (`[u32; 3]`), its first word loaded: `imul i, 12;
    /// add b`.
    LoadStride12,
    /// `fn(p: *mut u64, i: u64, j: u64, v: u64) { *p.gep[i, j] = v }`.
    StoreU64,
    /// `u32` indices, zero-extended before the opcode.
    IndexU32,
    /// `i32` indices, sign-extended before the opcode.
    IndexI32,
    /// `fn(p, i, j) -> *const u64 { p.gep[i, j] }`: the address returned.
    Address,
    /// `fn(p) -> u64 { *p.gep[1, 2] }`: constant indices.
    ConstIndex,
    // ---- (b) a private slot at constant indices
    /// `fn(x: u64, y: u64) -> u64 { a[1] = x; a[2] = y; a[1] }` for `a:
    /// [u64; 4]`, each element addressed `a.gep[k, 0]`, the load
    /// `a.gep[0, 1]`.
    FrameU64,
    /// Likewise over `[[u8; 3]; 4]`, bytes stored and loaded.
    FrameStride3,
    /// Likewise over `[[u32; 3]; 4]`, words stored and loaded.
    FrameStride12,
    // ---- (c) a derived base (OD-114)
    /// `fn(i: u64, j: u64) -> u64 { let mut p = null; fill(&mut p);
    /// *p.gep[i, j] }`.
    Derived,
    // ---- (d) OD-186: a slot address the LIR types as a by-value aggregate
    // (the adapter's copy of an aggregate `Load` into a fresh slot)
    /// `fn(p: *const [u64; 2]) -> [u64; 2] { *p }`: the copy returned (in
    /// RAX and RDX).
    LoadedReturned,
    /// `fn(p: *const [u32; 2]) -> u64 { take(*p) }`: the copy passed by
    /// value.
    LoadedPassed,
    /// `fn(p: *const [u64; 2]) -> u64 { (*p)[1] }`: an element of the copy,
    /// `ArrayGep` of the slot at the constant index 1.
    LoadedElement,
}

/// Every `ArrayGep` shape whose real selection the owner admits and whose
/// theorem holds ([`every_admitted_arraygep_fixture_is_qualified`] checks
/// that none is left out).
pub(crate) const ARRAY_GEP: [ElementShape; 18] = [
    ElementShape::LoadU64,
    ElementShape::LoadU32,
    ElementShape::LoadU16,
    ElementShape::LoadU8,
    ElementShape::LoadStride3,
    ElementShape::LoadStride12,
    ElementShape::StoreU64,
    ElementShape::IndexU32,
    ElementShape::IndexI32,
    ElementShape::Address,
    ElementShape::ConstIndex,
    ElementShape::FrameU64,
    ElementShape::FrameStride3,
    ElementShape::FrameStride12,
    ElementShape::Derived,
    ElementShape::LoadedReturned,
    ElementShape::LoadedPassed,
    ElementShape::LoadedElement,
];

impl ElementShape {
    fn name(self) -> String {
        let name = format!("{self:?}");
        let mut snake = String::from("agep_");
        for (i, c) in name.chars().enumerate() {
            if c.is_ascii_uppercase() && i > 0 {
                snake.push('_');
            }
            snake.push(c.to_ascii_lowercase());
        }
        snake
    }
}

/// Translate one function of `builder`'s module under the explicit Permit
/// the workspace's fixtures use.
fn translate(builder: ModuleBuilder, name: &str) -> Function {
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

/// The LIR the trust-ir adapter produces for an `ArrayGep` shape.
pub(crate) fn arraygep_lir(shape: ElementShape) -> Function {
    use ElementShape::*;
    let mut builder = ModuleBuilder::new("x86_source_bound_body_arraygep");
    let array = |builder: &mut ModuleBuilder, element: Ty, count: u64| {
        let element = builder.add_type(element);
        Ty::Array(element, count)
    };
    let bytes3 = array(&mut builder, Ty::U8, 3);
    let words3 = array(&mut builder, Ty::U32, 3);
    let u32x2 = array(&mut builder, Ty::U32, 2);
    let u64x2 = array(&mut builder, Ty::U64, 2);
    let take_ty = builder.add_func_type(vec![u32x2.clone()], vec![Ty::U64]);
    let take = builder.declare_function("take", take_ty);
    let (element, loaded) = match shape {
        LoadU32 => (Ty::U32, Ty::U32),
        LoadU16 => (Ty::U16, Ty::U16),
        LoadU8 => (Ty::U8, Ty::U8),
        LoadStride3 | FrameStride3 => (bytes3.clone(), Ty::U8),
        LoadStride12 | FrameStride12 => (words3.clone(), Ty::U32),
        _ => (Ty::U64, Ty::U64),
    };
    let slot = match shape {
        FrameU64 => array(&mut builder, Ty::U64, 4),
        FrameStride3 => array(&mut builder, bytes3.clone(), 4),
        FrameStride12 => array(&mut builder, words3.clone(), 4),
        _ => Ty::U64,
    };
    let ptr_u64 = Ty::PtrMut(Box::new(Ty::U64));
    let fill_ty = builder.add_func_type(vec![Ty::PtrMut(Box::new(ptr_u64.clone()))], vec![]);
    let fill = builder.declare_function("fill", fill_ty);
    let pointer = Ty::PtrMut(Box::new(element.clone()));
    let (params, results): (Vec<Ty>, Vec<Ty>) = match shape {
        LoadU64 | LoadU32 | LoadU16 | LoadU8 | LoadStride3 | LoadStride12 => (
            vec![pointer.clone(), Ty::U64, Ty::U64],
            vec![loaded.clone()],
        ),
        StoreU64 => (vec![pointer.clone(), Ty::U64, Ty::U64, Ty::U64], vec![]),
        IndexU32 => (vec![pointer.clone(), Ty::U32, Ty::U32], vec![Ty::U64]),
        IndexI32 => (vec![pointer.clone(), Ty::I32, Ty::I32], vec![Ty::U64]),
        Address => (
            vec![pointer.clone(), Ty::U64, Ty::U64],
            vec![pointer.clone()],
        ),
        ConstIndex => (vec![pointer.clone()], vec![Ty::U64]),
        FrameU64 | FrameStride3 | FrameStride12 => {
            (vec![loaded.clone(), loaded.clone()], vec![loaded.clone()])
        }
        Derived => (vec![Ty::U64, Ty::U64], vec![Ty::U64]),
        LoadedReturned => (
            vec![Ty::PtrMut(Box::new(u64x2.clone()))],
            vec![u64x2.clone()],
        ),
        LoadedPassed => (vec![Ty::PtrMut(Box::new(u32x2.clone()))], vec![Ty::U64]),
        LoadedElement => (vec![Ty::PtrMut(Box::new(u64x2.clone()))], vec![Ty::U64]),
    };
    let signature = builder.add_func_type(params.clone(), results);
    let name = shape.name();
    let mut f = builder.function(name.clone(), signature);
    let entry = f.create_block();
    let args: Vec<_> = params
        .iter()
        .map(|ty| f.add_block_param(entry, ty.clone()))
        .collect();
    f.switch_to_block(entry);
    match shape {
        LoadU64 | LoadU32 | LoadU16 | LoadU8 | LoadStride3 | LoadStride12 | IndexU32 | IndexI32 => {
            let address = f.gep(element.clone(), args[0], vec![args[1], args[2]]);
            let value = f.load(loaded.clone(), address);
            f.ret(vec![value]);
        }
        StoreU64 => {
            let address = f.gep(element.clone(), args[0], vec![args[1], args[2]]);
            f.store(Ty::U64, address, args[3]);
            f.ret(vec![]);
        }
        Address => {
            let address = f.gep(element.clone(), args[0], vec![args[1], args[2]]);
            f.ret(vec![address]);
        }
        ConstIndex => {
            let one = f.iconst(Ty::U64, 1);
            let two = f.iconst(Ty::U64, 2);
            let address = f.gep(element.clone(), args[0], vec![one, two]);
            let value = f.load(loaded.clone(), address);
            f.ret(vec![value]);
        }
        FrameU64 | FrameStride3 | FrameStride12 => {
            let a = f.alloca(slot.clone());
            let zero = f.iconst(Ty::U64, 0);
            let one = f.iconst(Ty::U64, 1);
            let two = f.iconst(Ty::U64, 2);
            let first = f.gep(element.clone(), a, vec![one, zero]);
            f.store(loaded.clone(), first, args[0]);
            let second = f.gep(element.clone(), a, vec![two, zero]);
            f.store(loaded.clone(), second, args[1]);
            let again = f.gep(element.clone(), a, vec![zero, one]);
            let value = f.load(loaded.clone(), again);
            f.ret(vec![value]);
        }
        Derived => {
            let p = f.alloca(ptr_u64.clone());
            let null = f.null_ptr();
            f.store(ptr_u64.clone(), p, null);
            f.call_void(fill, vec![p]);
            let base = f.load(ptr_u64.clone(), p);
            let address = f.gep(Ty::U64, base, vec![args[0], args[1]]);
            let value = f.load(Ty::U64, address);
            f.ret(vec![value]);
        }
        LoadedReturned => {
            let copy = f.load(u64x2.clone(), args[0]);
            f.ret(vec![copy]);
        }
        LoadedPassed => {
            let copy = f.load(u32x2.clone(), args[0]);
            let result = f.call(take, vec![copy]);
            f.ret(vec![result]);
        }
        LoadedElement => {
            let copy = f.load(u64x2.clone(), args[0]);
            let one = f.iconst(Ty::U64, 1);
            let element = f.extract_element(Ty::U64, copy, one);
            f.ret(vec![element]);
        }
    }
    f.build();
    translate(builder, &name)
}

pub(crate) fn arraygep_pair(shape: ElementShape) -> (Function, X86ISelFunction) {
    let source = arraygep_lir(shape);
    let machine = select(&source, X86CallAbi::SystemV);
    (source, machine)
}

/// Every fixture shape, in declaration order.
pub(crate) fn all_arraygep_shapes() -> Vec<ElementShape> {
    use ElementShape::*;
    let all = ARRAY_GEP.to_vec();
    // Exhaustive: a new shape does not compile until it is listed here.
    for shape in &all {
        match shape {
            LoadU64 | LoadU32 | LoadU16 | LoadU8 | LoadStride3 | LoadStride12 | StoreU64
            | IndexU32 | IndexI32 | Address | ConstIndex | FrameU64 | FrameStride3
            | FrameStride12 | Derived | LoadedReturned | LoadedPassed | LoadedElement => {}
        }
    }
    all
}

#[track_caller]
fn owner(source: &Function, machine: &X86ISelFunction, what: &str) -> ProofObligation {
    fixture_owner(source, machine)
        .unwrap_or_else(|refusal| {
            panic!(
                "{what}: {refusal}\n{}{}",
                describe_lir(source),
                describe(machine)
            )
        })
        .obligation()
        .clone()
}

/// The source admission's refusal of `source`, as text.
#[track_caller]
fn admission_refusal(source: &Function) -> String {
    match admitted_body(source) {
        Ok(_) => panic!("admitted\n{}", describe_lir(source)),
        Err(refusal) => refusal.to_string(),
    }
}

/// The walk ordinals of every row with `opcode`.
fn rows_of(machine: &X86ISelFunction, opcode: X86Opcode) -> Vec<usize> {
    find(machine, opcode)
}

/// The `ArrayGep` instructions of `source`, in layout order, as
/// `(block, index)`.
fn array_geps(source: &Function) -> Vec<(Block, usize)> {
    source
        .layout_order()
        .into_iter()
        .flat_map(|block| {
            source.blocks[&block]
                .instructions
                .iter()
                .enumerate()
                .filter(|(_, inst)| matches!(inst.opcode, L::ArrayGep { .. }))
                .map(move |(index, _)| (block, index))
                .collect::<Vec<_>>()
        })
        .collect()
}

/// `source` with the instruction at `at` replaced by `edit`'s result.
fn edited(source: &Function, at: (Block, usize), edit: impl FnOnce(&mut Instruction)) -> Function {
    let mut source = source.clone();
    edit(
        &mut source
            .blocks
            .get_mut(&at.0)
            .expect("the block")
            .instructions[at.1],
    );
    source
}

/// The `SibMemAddr` operand of the row at `ordinal`.
fn sib_mut(machine: &mut X86ISelFunction, ordinal: usize) -> (&mut O, &mut O, &mut u8, &mut i32) {
    match &mut inst_mut(machine, ordinal).operands[1] {
        O::SibMemAddr {
            base,
            index,
            scale,
            disp,
        } => (base.as_mut(), index.as_mut(), scale, disp),
        other => panic!("not a SIB address: {other:?}"),
    }
}

// ---------------------------------------------------------------------------
// Construction (no solver)
// ---------------------------------------------------------------------------

/// The fixtures exercise the forms they are named for: the LIR carries
/// `ArrayGep` of the element type, and the selector's rows are the scaled
/// `lea`, the `lea` and `add`, or the `imul` and `add`.
#[test]
fn arraygep_fixtures_have_the_expected_lir_and_pre_ra_shapes() {
    use ElementShape::*;
    for shape in all_arraygep_shapes() {
        let (source, machine) = arraygep_pair(shape);
        let geps = array_geps(&source);
        let expected_geps = match shape {
            FrameU64 | FrameStride3 | FrameStride12 => 6,
            LoadedReturned | LoadedPassed => 0,
            LoadedElement => 1,
            _ => 2,
        };
        assert_eq!(
            geps.len(),
            expected_geps,
            "{shape:?}\n{}",
            describe_lir(&source)
        );
        let scales: Vec<u8> = rows_of(&machine, X86Opcode::LeaSib)
            .into_iter()
            .map(|row| match &inst(&machine, row).operands[1] {
                O::SibMemAddr { scale, .. } => *scale,
                _ => unreachable!(),
            })
            .collect();
        let expected: Vec<u8> = match shape {
            LoadU32 => vec![4, 4],
            LoadU16 => vec![2, 2],
            LoadU8 => vec![1, 1],
            LoadStride3 => vec![2, 2],
            LoadStride12 => vec![],
            FrameU64 => vec![8; 6],
            FrameStride3 => vec![2; 6],
            FrameStride12 => vec![],
            LoadedReturned | LoadedPassed => vec![],
            LoadedElement => vec![8],
            _ => vec![8, 8],
        };
        assert_eq!(scales, expected, "{shape:?}\n{}", describe(&machine));
        if matches!(shape, LoadStride12 | FrameStride12) {
            assert!(
                !rows_of(&machine, X86Opcode::ImulRRI).is_empty(),
                "{shape:?}\n{}",
                describe(&machine)
            );
        }
    }
}

#[test]
fn owner_builds_for_every_arraygep_shape_and_covers_every_value_row() {
    for shape in ARRAY_GEP {
        let (source, machine) = arraygep_pair(shape);
        let body = fixture_owner(&source, &machine).unwrap_or_else(|refusal| {
            panic!(
                "{shape:?}: {refusal}\n{}{}",
                describe_lir(&source),
                describe(&machine)
            )
        });
        let expected: Vec<usize> = rows(&machine)
            .into_iter()
            .filter(|(_, block, index)| {
                let opcode = machine.blocks[block].insts[*index].opcode;
                !opcode.is_pseudo()
                    && !matches!(
                        opcode,
                        X86Opcode::Jmp
                            | X86Opcode::Ret
                            | X86Opcode::Call
                            | X86Opcode::CallR
                            | X86Opcode::Ud2
                    )
            })
            .map(|(ordinal, _, _)| ordinal)
            .collect();
        assert_eq!(
            body.bound_rows(),
            expected,
            "{shape:?}\n{}",
            describe(&machine)
        );
        let entries = free_inputs_of(body.obligation());
        assert_eq!(
            owner_check(&source, &machine, body.obligation(), &entries),
            Ok(()),
            "{shape:?}"
        );
        assert!(body.obligation().is_genuinely_proven(), "{shape:?}");
        assert!(source_admits_x86_body_owner(&source, SYSV), "{shape:?}");
    }
}

#[test]
fn arraygep_theorems_hold_on_samples() {
    for shape in ARRAY_GEP {
        let (source, machine) = arraygep_pair(shape);
        let obligation = owner(&source, &machine, &format!("{shape:?}"));
        assert!(
            theorem_holds(&obligation),
            "{shape:?}\n{}",
            describe(&machine)
        );
    }
}

/// The golden, owner, credit and host-qualification tests run over
/// [`ARRAY_GEP`]: every fixture whose real selection the owner admits with a
/// theorem that holds must be in it.
#[test]
fn every_admitted_arraygep_fixture_is_qualified() {
    for shape in all_arraygep_shapes() {
        let (source, machine) = arraygep_pair(shape);
        let holds =
            fixture_owner(&source, &machine).is_ok_and(|owner| theorem_holds(owner.obligation()));
        assert_eq!(ARRAY_GEP.contains(&shape), holds, "{shape:?}");
    }
}

// ---------------------------------------------------------------------------
// The meaning (no solver)
// ---------------------------------------------------------------------------

/// The verify-owned stride is the selector's: `Type::bytes` of the element,
/// natural C, over scalars, structs with padding, nested arrays and their
/// combinations; zero-sized elements and enums have none.
#[test]
fn the_verify_owned_stride_is_the_selectors_element_size() {
    let scalars = [
        Type::B1,
        Type::I8,
        Type::I16,
        Type::I32,
        Type::I64,
        Type::I128,
        Type::F32,
        Type::F64,
    ];
    let mut types: Vec<Type> = scalars.to_vec();
    for a in &scalars {
        for b in &scalars {
            types.push(Type::Struct(vec![a.clone(), b.clone()]));
            types.push(Type::Struct(vec![a.clone(), b.clone(), Type::I8]));
            types.push(Type::Array(Box::new(a.clone()), 3));
            types.push(Type::Array(
                Box::new(Type::Struct(vec![a.clone(), b.clone()])),
                5,
            ));
            types.push(Type::Struct(vec![
                Type::I8,
                Type::Array(Box::new(a.clone()), 3),
                b.clone(),
            ]));
        }
    }
    for ty in &types {
        assert_eq!(
            array_element_stride(ty),
            Some(u64::from(ty.bytes())),
            "{ty:?}"
        );
    }
    assert_eq!(array_element_stride(&Type::Struct(vec![])), None);
    assert_eq!(
        array_element_stride(&Type::Array(Box::new(Type::I64), 0)),
        None
    );
}

/// The one spelling of an element address: `base + index` at stride 1, else
/// `base + index * stride`, wrapping at 64 bits.
#[test]
fn the_element_address_is_the_wrapping_scaled_sum() {
    use crate::smt::{EvalEnv, EvalResult};
    for stride in [1u64, 2, 3, 4, 5, 8, 9, 12, 24, 1 << 31] {
        for (base, index) in [
            (0u64, 0u64),
            (0x1000, 7),
            (u64::MAX, 1),
            (0x8000_0000_0000_0000, u64::MAX),
            (12345, 1 << 62),
        ] {
            let mut env = EvalEnv::default();
            env.insert("b".into(), base);
            env.insert("i".into(), index);
            let EvalResult::Bv(address) =
                array_element_address(E::var("b", 64), E::var("i", 64), stride).eval(&env)
            else {
                panic!("a bit-vector");
            };
            assert_eq!(
                address,
                base.wrapping_add(index.wrapping_mul(stride)),
                "{base:#x} + {index:#x} * {stride}"
            );
        }
    }
}

/// An element address the walks compute at a constant index of a private
/// slot is the exact offset `index * stride` into it: element 1 (`a.gep[0,
/// 1]`) reads back exactly the store to element 1 (`a.gep[1, 0]`), never the
/// store to element 2, and with the load moved to element 2 it reads that.
#[test]
fn a_constant_index_of_a_private_slot_is_its_exact_offset() {
    use ElementShape::*;
    for shape in [FrameU64, FrameStride3, FrameStride12] {
        let source = arraygep_lir(shape);
        let params: Vec<Value> = source.blocks[&source.entry_block]
            .params
            .iter()
            .map(|(value, _)| *value)
            .collect();
        let loaded = |source: &Function| {
            let load = source.blocks[&source.entry_block]
                .instructions
                .iter()
                .find(|inst| matches!(inst.opcode, L::Load { .. }))
                .expect("the load")
                .results[0];
            let body = admitted_body(source).expect("admitted");
            body.paths[0]
                .definitions
                .iter()
                .find(|definition| definition.result == load)
                .map(|definition| definition.op.clone())
                .expect("the load's definition")
        };
        assert!(
            matches!(loaded(&source), SourceOp::Copy(value) if value == params[0]),
            "{shape:?}"
        );
        // The load's second index moved from 1 to 2: element 2 is `y`.
        let geps = array_geps(&source);
        let two = source.blocks[&geps[2].0].instructions[geps[2].1].args[1];
        let moved = edited(&source, geps[5], |inst| inst.args[1] = two);
        assert!(
            matches!(loaded(&moved), SourceOp::Copy(value) if value == params[1]),
            "{shape:?}"
        );
    }
}

// ---------------------------------------------------------------------------
// Refusals (no solver)
// ---------------------------------------------------------------------------

/// A private slot at a non-constant `I64` index is slice 17's indexed
/// address with the element size as its stride (offset `c + index * 8`
/// here); with no bound its region holds (the index a parameter, no guard),
/// it is refused by name (`IndexedUnbounded`), never admitted unbounded.
#[test]
fn a_private_slot_at_a_variable_index_is_indexed_with_the_element_stride() {
    let mut builder = ModuleBuilder::new("x86_source_bound_body_arraygep_indexed");
    let slot = {
        let element = builder.add_type(Ty::U64);
        Ty::Array(element, 4)
    };
    let signature = builder.add_func_type(vec![Ty::U64, Ty::U64], vec![Ty::U64]);
    let mut f = builder.function("agep_frame_indexed", signature);
    let entry = f.create_block();
    let i = f.add_block_param(entry, Ty::U64);
    let x = f.add_block_param(entry, Ty::U64);
    f.switch_to_block(entry);
    let a = f.alloca(slot);
    let zero = f.iconst(Ty::U64, 0);
    let element = f.gep(Ty::U64, a, vec![i, zero]);
    f.store(Ty::U64, element, x);
    let first = f.gep(Ty::U64, a, vec![zero, zero]);
    let value = f.load(Ty::U64, first);
    f.ret(vec![value]);
    f.build();
    let source = translate(builder, "agep_frame_indexed");
    let refusal = admission_refusal(&source);
    assert!(
        refusal.contains("IndexedUnbounded") && refusal.contains("* 8 (indexed)"),
        "{refusal}\n{}",
        describe_lir(&source)
    );
}

/// The index is the 64-bit value itself: an index of another type (the
/// adapter extends a narrower one first), an element type outside the
/// layout model, a zero-sized element, an index that is a private address
/// and an offset past `i64` are refused by name.
#[test]
fn indices_and_elements_outside_the_meaning_are_refused_by_name() {
    use ElementShape::*;
    // An `I32` index (the extension dropped from the LIR).
    let source = arraygep_lir(IndexU32);
    let first = array_geps(&source)[0];
    let narrow = source.blocks[&source.entry_block].params[1].0;
    let source = edited(&source, first, |inst| inst.args[1] = narrow);
    let refusal = admission_refusal(&source);
    assert!(
        refusal.contains("indexes an array by a value other than an I64"),
        "{refusal}"
    );
    // An enum element.
    let source = arraygep_lir(LoadU64);
    let first = array_geps(&source)[0];
    let source = edited(&source, first, |inst| {
        inst.opcode = L::ArrayGep {
            elem_ty: Type::Enum {
                tag_width: trust_cg_ir::function::EnumTagWidth::U8,
                variants: vec![vec![Type::I64]],
            },
        }
    });
    let refusal = admission_refusal(&source);
    assert!(
        refusal.contains("indexes elements of a type outside the layout model"),
        "{refusal}"
    );
    // A zero-sized element.
    let source = arraygep_lir(LoadU64);
    let first = array_geps(&source)[0];
    let source = edited(&source, first, |inst| {
        inst.opcode = L::ArrayGep {
            elem_ty: Type::Struct(vec![]),
        }
    });
    let refusal = admission_refusal(&source);
    assert!(
        refusal.contains("indexes elements of a type outside the layout model"),
        "{refusal}"
    );
    // A private slot at a constant index past `i64`.
    let source = arraygep_lir(FrameU64);
    let first = array_geps(&source)[0];
    let index = source.blocks[&first.0].instructions[first.1].args[1];
    let mut source = source.clone();
    for block in source.blocks.values_mut() {
        for inst in &mut block.instructions {
            if inst.results.first() == Some(&index)
                && let L::Iconst { imm, .. } = &mut inst.opcode
            {
                *imm = i64::MAX;
            }
        }
    }
    let refusal = admission_refusal(&source);
    assert!(
        refusal.contains("overflows a private stack offset"),
        "{refusal}"
    );
    // A private slot address as the index.
    let source = arraygep_lir(FrameU64);
    let first = array_geps(&source)[0];
    let base = source.blocks[&first.0].instructions[first.1].args[0];
    let source = edited(&source, first, |inst| inst.args[1] = base);
    let refusal = admission_refusal(&source);
    assert!(
        refusal.contains("indexes a private stack address by a private stack address"),
        "{refusal}"
    );
}

/// OD-186: a slot's own address the LIR types as a by-value aggregate (the
/// adapter's copy of an aggregate `Load`) is that aggregate, as the selector
/// types it; an element address hinted as an aggregate stays refused, since
/// the selector defines it as a pointer whatever its hint.
#[test]
fn a_slot_address_typed_as_an_aggregate_is_that_aggregate() {
    use ElementShape::*;
    for shape in [LoadedReturned, LoadedPassed, LoadedElement] {
        let source = arraygep_lir(shape);
        let hinted = source.blocks[&source.entry_block]
            .instructions
            .iter()
            .find(|inst| matches!(inst.opcode, L::StackAddr { .. }))
            .map(|inst| inst.results[0])
            .expect("the copy's slot");
        assert!(
            matches!(source.value_types.get(&hinted), Some(Type::Array(..))),
            "{shape:?}: {:?}\n{}",
            source.value_types.get(&hinted),
            describe_lir(&source)
        );
        assert!(admitted_body(&source).is_ok(), "{shape:?}");
    }
    let source = arraygep_lir(LoadedElement);
    let element = array_geps(&source)[0];
    let result = source.blocks[&element.0].instructions[element.1].results[0];
    let mut hinted = source.clone();
    hinted
        .value_types
        .insert(result, Type::Array(Box::new(Type::I64), 1));
    let refusal = admission_refusal(&hinted);
    assert!(refusal.contains("inconsistent type hint"), "{refusal}");
}

/// A scaled `lea` of a frame address by a register the walk does not know
/// as a constant is slice 17's indexed address (its offset the scaled
/// register's term): where the source stores a constant element, the
/// machine's offset is free and the theorem is refuted, never credited.
#[test]
fn a_frame_lea_at_an_unknown_index_is_refuted() {
    let (source, mut machine) = arraygep_pair(ElementShape::FrameU64);
    let lea = rows_of(&machine, X86Opcode::LeaSib)[0];
    let entry = rows(&machine)
        .into_iter()
        .map(|(ordinal, _, _)| ordinal)
        .find(|ordinal| {
            let row = inst(&machine, *ordinal);
            row.opcode == X86Opcode::MovRR && row.operands[1] == preg(RDI)
        })
        .expect("x's copy");
    let x = inst(&machine, entry).operands[0].clone();
    *sib_mut(&mut machine, lea).1 = x;
    let owner = fixture_owner(&source, &machine)
        .unwrap_or_else(|refusal| panic!("an indexed machine address: {refusal}"));
    // The theorem states the machine's in-bounds claim (no equation), so
    // the DAG sampler, which evaluates any Boolean claim, judges it.
    assert!(super::slice9::dag_refuted_on_samples(owner.obligation()));
}

// ---------------------------------------------------------------------------
// Typed mismatches (the exact affine evaluation, no solver)
// ---------------------------------------------------------------------------

/// A wrong element address the exact affine evaluation knows on both sides
/// is a typed mismatch: a constant index scaled by another element size,
/// and (stride 1) another base.
#[test]
fn a_known_wrong_element_address_is_a_typed_mismatch() {
    use ElementShape::*;
    let (source, mut machine) = arraygep_pair(ConstIndex);
    let lea = rows_of(&machine, X86Opcode::LeaSib)[1];
    *sib_mut(&mut machine, lea).2 = 4;
    expect_mismatch(&source, &machine, "ConstIndex scaled by 4", |mismatch| {
        matches!(mismatch, X86BodyMismatch::MemoryAddress { .. })
    });
    let (source, mut machine) = arraygep_pair(LoadU8);
    let lea = rows_of(&machine, X86Opcode::LeaSib)[0];
    let index = sib_mut(&mut machine, lea).1.clone();
    *sib_mut(&mut machine, lea).0 = index;
    expect_mismatch(&source, &machine, "LoadU8 based at i", |mismatch| {
        matches!(mismatch, X86BodyMismatch::MemoryAddress { .. })
    });
    // A private slot's element written at another offset is read back as
    // other bytes: the walk decides which (a refuted theorem, or no claim
    // when the bytes leave the slot), never credit.
    let (source, mut machine) = arraygep_pair(FrameU64);
    let lea = rows_of(&machine, X86Opcode::LeaSib)[0];
    *sib_mut(&mut machine, lea).2 = 4;
    match fixture_owner(&source, &machine) {
        Ok(owner) => assert!(theorem_refuted(owner.obligation())),
        Err(refusal) => panic!("FrameU64 scaled by 4: {refusal}"),
    }
}

// ---------------------------------------------------------------------------
// Refutations
// ---------------------------------------------------------------------------

/// The walk ordinal of the first load row.
fn first_load(machine: &X86ISelFunction) -> usize {
    rows(machine)
        .into_iter()
        .map(|(ordinal, _, _)| ordinal)
        .find(|ordinal| memory_access(inst(machine, *ordinal).opcode).is_some_and(|f| f.load))
        .expect("a load")
}

/// The walk ordinal of the last load row.
fn last_load(machine: &X86ISelFunction) -> usize {
    rows(machine)
        .into_iter()
        .map(|(ordinal, _, _)| ordinal)
        .rfind(|ordinal| memory_access(inst(machine, *ordinal).opcode).is_some_and(|f| f.load))
        .expect("a load")
}

/// Wrong lowerings of an element address, each one refuted by the theorem on
/// samples (and replayed to a counterexample on the qualification host): an
/// index scaled by the wrong element size, the wrong base, a missing or
/// wrong index extension, an off-by-one element, a load or store of the
/// wrong element.
pub(crate) fn arraygep_refutations() -> Vec<(&'static str, Function, X86ISelFunction)> {
    use ElementShape::*;
    let mut cases = Vec::new();
    // The first index scaled by 4 where the element is 8 bytes.
    let (source, mut machine) = arraygep_pair(LoadU64);
    let lea = rows_of(&machine, X86Opcode::LeaSib)[0];
    *sib_mut(&mut machine, lea).2 = 4;
    cases.push(("LoadU64/wrong-element-size", source, machine));
    // The 3-byte stride's `add` of the index dropped (a stride of 2).
    let (source, mut machine) = arraygep_pair(LoadStride3);
    let add = rows_of(&machine, X86Opcode::AddRR)[0];
    remove_at(&mut machine, add);
    cases.push(("LoadStride3/wrong-element-size", source, machine));
    // The 12-byte stride multiplied by 8.
    let (source, mut machine) = arraygep_pair(LoadStride12);
    let imul = rows_of(&machine, X86Opcode::ImulRRI)[0];
    inst_mut(&mut machine, imul).operands[2] = O::Imm(8);
    cases.push(("LoadStride12/wrong-element-size", source, machine));
    // The first element address based at the index register.
    let (source, mut machine) = arraygep_pair(LoadU64);
    let lea = rows_of(&machine, X86Opcode::LeaSib)[0];
    let index = sib_mut(&mut machine, lea).1.clone();
    *sib_mut(&mut machine, lea).0 = index;
    cases.push(("LoadU64/wrong-base", source, machine));
    // A `u32` index used without its zero extension: the parameter's whole
    // register, whose bits above 31 a caller leaves undefined.
    let (source, mut machine) = arraygep_pair(IndexU32);
    let extension = rows_of(&machine, X86Opcode::MovRR32)
        .into_iter()
        .find(|row| matches!(inst(&machine, *row).operands[1], O::VReg(_)))
        .expect("the zero extension of i");
    let row = inst_mut(&mut machine, extension);
    row.opcode = X86Opcode::MovRR;
    row.operands[1] = preg(RSI);
    cases.push(("IndexU32/missing-extension", source, machine));
    // An `i32` index zero-extended instead of sign-extended.
    let (source, mut machine) = arraygep_pair(IndexI32);
    let extension = rows_of(&machine, X86Opcode::Movsx)[0];
    inst_mut(&mut machine, extension).opcode = X86Opcode::MovRR32;
    cases.push(("IndexI32/wrong-extension", source, machine));
    // One element further: the second `lea` displaced by one element.
    let (source, mut machine) = arraygep_pair(LoadU64);
    let lea = rows_of(&machine, X86Opcode::LeaSib)[1];
    *sib_mut(&mut machine, lea).3 = 8;
    cases.push(("LoadU64/off-by-one-element", source, machine));
    // The returned address one element further.
    let (source, mut machine) = arraygep_pair(Address);
    let lea = rows_of(&machine, X86Opcode::LeaSib)[1];
    *sib_mut(&mut machine, lea).3 = 8;
    cases.push(("Address/off-by-one-element", source, machine));
    // The load through the first element address (`p.gep[i]`), not the
    // second (`p.gep[i, j]`).
    let (source, mut machine) = arraygep_pair(LoadU64);
    let leas = rows_of(&machine, X86Opcode::LeaSib);
    let first = inst(&machine, leas[0]).operands[0].clone();
    let load = first_load(&machine);
    if let O::MemAddr { base, .. } = &mut inst_mut(&mut machine, load).operands[1] {
        **base = first;
    }
    cases.push(("LoadU64/wrong-element-loaded", source, machine));
    // The store through the first element address.
    let (source, mut machine) = arraygep_pair(StoreU64);
    let leas = rows_of(&machine, X86Opcode::LeaSib);
    let first = inst(&machine, leas[0]).operands[0].clone();
    let store = rows(&machine)
        .into_iter()
        .map(|(ordinal, _, _)| ordinal)
        .find(|ordinal| {
            memory_access(inst(&machine, *ordinal).opcode).is_some_and(|form| !form.load)
        })
        .expect("the store");
    if let O::MemAddr { base, .. } = &mut inst_mut(&mut machine, store).operands[0] {
        **base = first;
    }
    cases.push(("StoreU64/wrong-element-stored", source, machine));
    // A private slot: `x` stored at the half-scaled offset 4.
    let (source, mut machine) = arraygep_pair(FrameU64);
    let lea = rows_of(&machine, X86Opcode::LeaSib)[0];
    *sib_mut(&mut machine, lea).2 = 4;
    cases.push(("FrameU64/wrong-element-size", source, machine));
    // A private slot: element 2 (`y`) loaded where the source loads 1.
    let (source, mut machine) = arraygep_pair(FrameU64);
    let lea = *rows_of(&machine, X86Opcode::LeaSib).last().expect("a lea");
    *sib_mut(&mut machine, lea).3 = 8;
    cases.push(("FrameU64/wrong-element-loaded", source, machine));
    // A private slot of 12-byte elements: `x` stored at a stride of 8.
    let (source, mut machine) = arraygep_pair(FrameStride12);
    let imul = rows_of(&machine, X86Opcode::ImulRRI)[0];
    inst_mut(&mut machine, imul).operands[2] = O::Imm(8);
    cases.push(("FrameStride12/wrong-element-size", source, machine));
    // A derived base: the load through `q.gep[i]`, not `q.gep[i, j]`.
    let (source, mut machine) = arraygep_pair(Derived);
    let leas = rows_of(&machine, X86Opcode::LeaSib);
    let first = inst(&machine, leas[0]).operands[0].clone();
    let load = last_load(&machine);
    if let O::MemAddr { base, .. } = &mut inst_mut(&mut machine, load).operands[1] {
        **base = first;
    }
    cases.push(("Derived/wrong-element-loaded", source, machine));
    // OD-186: the copy's two eightbytes returned the other way round.
    let (source, mut machine) = arraygep_pair(LoadedReturned);
    let loads: Vec<usize> = rows(&machine)
        .into_iter()
        .map(|(ordinal, _, _)| ordinal)
        .filter(|ordinal| inst(&machine, *ordinal).opcode == X86Opcode::MovRM)
        .collect();
    for (row, disp) in loads.iter().zip([8, 0]) {
        if let O::MemAddr { disp: d, .. } = &mut inst_mut(&mut machine, *row).operands[1] {
            *d = disp;
        }
    }
    cases.push(("LoadedReturned/swapped-eightbytes", source, machine));
    // OD-186: element 0 of the copy loaded where the source loads element 1.
    let (source, mut machine) = arraygep_pair(LoadedElement);
    let lea = rows_of(&machine, X86Opcode::LeaSib)[0];
    *sib_mut(&mut machine, lea).3 = -8;
    cases.push(("LoadedElement/wrong-element-loaded", source, machine));
    // OD-186: the copy passed by value made 4 bytes short.
    let (source, mut machine) = arraygep_pair(LoadedPassed);
    let length = rows(&machine)
        .into_iter()
        .map(|(ordinal, _, _)| ordinal)
        .find(|ordinal| {
            let row = inst(&machine, *ordinal);
            row.opcode == X86Opcode::MovRI && row.operands[1] == O::Imm(8)
        })
        .expect("the copy's length");
    inst_mut(&mut machine, length).operands[1] = O::Imm(4);
    cases.push(("LoadedPassed/short-copy", source, machine));
    cases
}

#[test]
fn every_arraygep_refutation_is_refuted_on_samples() {
    for (label, source, machine) in arraygep_refutations() {
        let theorem = theorem_without_affine_refusal(&source, &machine, SYSV)
            .unwrap_or_else(|refusal| panic!("{label}: {refusal}\n{}", describe(&machine)));
        assert!(theorem_refuted(&theorem), "{label}\n{}", describe(&machine));
    }
}

/// The real x86 optimizer's output at O1, O2 and O3 for every fixture: the
/// owner never names a mismatch for a correct lowering, and every theorem it
/// builds holds.
#[test]
fn optimized_arraygep_fixtures_are_judged_without_false_mismatches() {
    use trust_cg_codegen::x86_64::pipeline::{X86Pipeline, X86PipelineConfig};
    let mut built = 0;
    for opt_level in [
        trust_cg_opt::OptLevel::O1,
        trust_cg_opt::OptLevel::O2,
        trust_cg_opt::OptLevel::O3,
    ] {
        let pipeline = X86Pipeline::new(X86PipelineConfig {
            opt_level,
            call_abi: X86CallAbi::SystemV,
            ..X86PipelineConfig::default()
        });
        for shape in all_arraygep_shapes() {
            let (source, mut machine) = arraygep_pair(shape);
            pipeline.run_x86_optimization_passes(&mut machine);
            match fixture_owner(&source, &machine) {
                Ok(owner) => {
                    built += 1;
                    assert!(
                        theorem_holds(owner.obligation()),
                        "{shape:?} at {opt_level:?}\n{}",
                        describe(&machine)
                    );
                }
                Err(X86BodyRefusal::Unsupported(refusal)) => {
                    eprintln!("{opt_level:?} {shape:?}: no claim ({refusal})");
                }
                Err(other) => panic!(
                    "{shape:?} at {opt_level:?}: {other}\n{}",
                    describe(&machine)
                ),
            }
        }
    }
    assert!(built > 0, "no optimized fixture built a theorem");
}

const ARRAY_GEP_SNAPSHOT_SHA256: &str =
    "144a12d55cde752af8884e1e21d2d4b1e41aa58753e71c112138ea92b67679b4";

#[test]
fn arraygep_smt2_is_canonical_per_shape() {
    use sha2::{Digest, Sha256};
    const GOLDEN: &str =
        include_str!("../tests/fixtures/x86_source_bound_body/arraygep_snapshots.smt2");
    let mut rendered = String::new();
    for shape in ARRAY_GEP {
        let (source, machine) = arraygep_pair(shape);
        let owner = fixture_owner(&source, &machine).unwrap();
        let smt2 = generate_smt2_query_raw(owner.obligation(), &replay_config());
        rendered.push_str(&format!(";;;; {shape:?}\n{smt2}\n"));
        let (mut source, mut machine) = (source.clone(), machine.clone());
        source.name = "renamed_function".into();
        machine.name = "renamed_function".into();
        let renamed = fixture_owner(&source, &machine).unwrap();
        assert_eq!(
            generate_smt2_query_raw(renamed.obligation(), &replay_config()),
            smt2
        );
    }
    if std::env::var_os("TCG_X86_BODY_SNAPSHOT_WRITE").is_some() {
        let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("tests/fixtures/x86_source_bound_body/arraygep_snapshots.smt2");
        std::fs::write(&path, &rendered).unwrap();
        panic!(
            "rewrote {}; review its diff, set ARRAY_GEP_SNAPSHOT_SHA256 to {:x} and re-run \
             without TCG_X86_BODY_SNAPSHOT_WRITE",
            path.display(),
            Sha256::digest(rendered.as_bytes())
        );
    }
    assert_eq!(
        format!("{:x}", Sha256::digest(GOLDEN.as_bytes())),
        ARRAY_GEP_SNAPSHOT_SHA256,
        "the golden file changed without the reviewed digest pin"
    );
    assert_eq!(rendered, GOLDEN, "ArrayGep snapshots drifted");
}

/// A diagnostic, not a check: every fixture's LIR, machine rows and theorem
/// (or refusal).
#[test]
#[ignore]
fn print_arraygep_fixtures() {
    for shape in all_arraygep_shapes() {
        let (source, machine) = arraygep_pair(shape);
        println!(
            "==== {shape:?}\n{}{}",
            describe_lir(&source),
            describe(&machine)
        );
        match fixture_owner(&source, &machine) {
            Ok(owner) => println!(
                "{}",
                generate_smt2_query_raw(owner.obligation(), &replay_config())
            ),
            Err(refusal) => println!("REFUSED {refusal}"),
        }
    }
}
