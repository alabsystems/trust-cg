// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Slice 8 of the x86-64 source-bound body theorem: aggregates in
//! general-purpose registers. A parameter, a result, a call argument or a
//! call result may be a `Struct` or `Array` of 1 to 16 bytes whose every
//! System V eightbyte is INTEGER: the caller passes (and the callee returns)
//! each eightbyte in the low bytes of one register, RDI.. for arguments and
//! RAX, RDX for results. LIR carries such a value by its address; the
//! selector copies a parameter into a private slot, loads an argument's or a
//! result's eightbytes from the value's slot into the ABI registers, and
//! stores a call result's into a fresh slot.
//!
//! Fixtures are real: LIR from the trust-ir adapter (by-value aggregates are
//! trust-ir aggregate values, built with `make_aggregate` and read with
//! `extract_field`, the shapes the rustc bridge's `PassMode::Cast` and
//! small-aggregate arguments produce) and the machine stream from the real
//! x86-64 instruction selector (`super::select`). Negative controls mutate
//! that stream and must end as a typed mismatch, a refuted theorem or an
//! unsupported (uncredited) body, never as Formal credit.
//!
//! Every test here runs without a solver, and the soundness check runs them
//! all (the `x86_source_bound_body::tests::slice8::` library gate). The
//! replay on AY and Clean and the verifier-credit tests are in
//! `slice8_qualification`.

use super::slice5::describe;
use super::slice6::{describe_lir, path_claims, paths_refuted_on_samples};
use super::*;
use trust_ir::ICmpOp;

/// Slice-8 fixture shapes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum AggShape {
    // ---- (a) aggregate parameters
    /// `fn(a: [u8; 4]) -> u8 { a[2] }`: one 4-byte eightbyte in EDI.
    ParamField,
    /// `fn(a: [u64; 1], x: u64) -> u64 { a[0] + x }`: the selector's
    /// single-register lane, then a scalar in RSI.
    ParamWord,
    /// `fn(p: [u64; 2]) -> u64 { p[0] - p[1] }`: two eightbytes, RDI:RSI.
    ParamTwoLanes,
    /// `fn(x: u64, a: [u16; 3]) -> u16 { a[2] }`: a 6-byte partial eightbyte
    /// in RSI, stored as 4 + 2 bytes.
    ParamPartial,
    /// `fn(x: u64, b: [u8; 1]) -> u8 { b[0] }`: a one-byte lane.
    ParamByte,
    /// `fn(s: { u32, u16, u8 }) -> u32 { s.0 + s.2 as u32 }`: a struct with
    /// a padding byte.
    ParamStruct,
    /// `fn(a: [u8; 9]) -> u8 { a[0] ^ a[8] }`: a full eightbyte and a
    /// one-byte one.
    ParamNineBytes,
    /// `fn(f: [bool; 2]) -> bool { f[1] }`: a `bool` field read from the
    /// caller's byte, `byte != 0`.
    ParamBool,
    // ---- (b) aggregate results
    /// `fn(x: u32) -> [u32; 1] { [x] }`: one 4-byte lane in EAX.
    ResultWord,
    /// `fn(x: u32, y: u32) -> [u32; 2] { [x, y] }`: one full eightbyte.
    ResultPair,
    /// `fn(x: u64, y: u64) -> [u64; 2] { [x, y] }`: RAX:RDX.
    ResultTwoLanes,
    /// `fn(x: u8) -> [u8; 5] { [x, 1, 2, 3, x] }`: a 5-byte partial eightbyte,
    /// assembled from a 4-byte and a 1-byte load.
    ResultPartial,
    /// `fn(x: u8) -> [u8; 1] { [x] }`: a one-byte lane in AL.
    ResultByte,
    /// `fn(a: [u16; 2]) -> [u16; 2] { a }`: a parameter returned.
    ResultForward,
    // ---- (c) calls
    /// `fn(x: u8) -> u64 { take4([x, 1, 2, x]) }`: an aggregate argument.
    CallArg,
    /// `fn(x: u64) -> u32 { let r = give2(x); r[0] ^ r[1] }`: an aggregate
    /// call result.
    CallResult,
    /// `fn(x: u64) -> [u32; 2] { give2(x) }`: a call result returned.
    CallResultForward,
    /// `fn(p: [u64; 2]) -> u64 { take2(p) }`: a parameter passed on.
    CallArgForward,
    /// `fn(x: u64) -> u64 { take2w(give2w(x)) }`: a two-lane result passed
    /// on by value.
    CallResultThenCall,
    /// `fn(x: u64) -> u32 { match opt(x) { [0, _] => 7, [_, v] => v } }`: a
    /// tag in a call result branched on.
    CallResultBranch,
    /// `fn(x: u64) -> u64 { give1(x)[0] as u64 }`: a 4-byte call result
    /// lane widened (the bits of RAX above it are not the callee's).
    CallResultWiden,
    /// `fn(x: u64, b: [u8; 1]) -> u32 { b[0] as u32 }`: a one-byte lane
    /// widened.
    ParamByteWiden,
}

/// Every slice-8 shape whose real selection the owner admits and whose
/// theorem holds ([`every_admitted_slice_eight_fixture_is_qualified`] checks
/// that none is left out).
pub(crate) const SLICE_EIGHT: [AggShape; 22] = [
    AggShape::ParamField,
    AggShape::ParamWord,
    AggShape::ParamTwoLanes,
    AggShape::ParamPartial,
    AggShape::ParamByte,
    AggShape::ParamStruct,
    AggShape::ParamNineBytes,
    AggShape::ParamBool,
    AggShape::ResultWord,
    AggShape::ResultPair,
    AggShape::ResultTwoLanes,
    AggShape::ResultPartial,
    AggShape::ResultByte,
    AggShape::ResultForward,
    AggShape::CallArg,
    AggShape::CallResult,
    AggShape::CallResultForward,
    AggShape::CallArgForward,
    AggShape::CallResultThenCall,
    AggShape::CallResultBranch,
    AggShape::CallResultWiden,
    AggShape::ParamByteWiden,
];

impl AggShape {
    fn name(self) -> String {
        let name = format!("{self:?}");
        let mut snake = String::from("s8_");
        for (i, c) in name.chars().enumerate() {
            if c.is_ascii_uppercase() && i > 0 {
                snake.push('_');
            }
            snake.push(c.to_ascii_lowercase());
        }
        snake
    }
}

/// The LIR the trust-ir adapter produces for a slice-8 shape.
pub(crate) fn slice8_lir(shape: AggShape) -> Function {
    use AggShape::*;
    let mut builder = ModuleBuilder::new("x86_source_bound_body_slice8");
    let array = |builder: &mut ModuleBuilder, element: Ty, count: u64| {
        let element = builder.add_type(element);
        Ty::Array(element, count)
    };
    let u8x4 = array(&mut builder, Ty::U8, 4);
    let u64x1 = array(&mut builder, Ty::U64, 1);
    let u64x2 = array(&mut builder, Ty::U64, 2);
    let u16x3 = array(&mut builder, Ty::U16, 3);
    let u8x1 = array(&mut builder, Ty::U8, 1);
    let u8x9 = array(&mut builder, Ty::U8, 9);
    let boolx2 = array(&mut builder, Ty::Bool, 2);
    let u32x1 = array(&mut builder, Ty::U32, 1);
    let u32x2 = array(&mut builder, Ty::U32, 2);
    let u8x5 = array(&mut builder, Ty::U8, 5);
    let u16x2 = array(&mut builder, Ty::U16, 2);
    let mixed = Ty::Struct(
        builder.add_struct(StructDef {
            origin: None,
            id: StructId::new(0),
            name: "Mixed".into(),
            fields: [Ty::U32, Ty::U16, Ty::U8]
                .into_iter()
                .enumerate()
                .map(|(i, ty)| FieldDef {
                    name: format!("f{i}"),
                    ty,
                    offset: None,
                })
                .collect(),
            size: None,
            align: None,
            repr: StructRepr::C,
        }),
    );
    let mut declare = |name: &str, params: Vec<Ty>, results: Vec<Ty>| {
        let ty = builder.add_func_type(params, results);
        builder.declare_function(name, ty)
    };
    let take4 = declare("take4", vec![u8x4.clone()], vec![Ty::U64]);
    let give2 = declare("give2", vec![Ty::U64], vec![u32x2.clone()]);
    let take2 = declare("take2", vec![u64x2.clone()], vec![Ty::U64]);
    let give2w = declare("give2w", vec![Ty::U64], vec![u64x2.clone()]);
    let give1 = declare("give1", vec![Ty::U64], vec![u32x1.clone()]);
    let (params, results): (Vec<Ty>, Vec<Ty>) = match shape {
        ParamField => (vec![u8x4.clone()], vec![Ty::U8]),
        ParamWord => (vec![u64x1.clone(), Ty::U64], vec![Ty::U64]),
        ParamTwoLanes => (vec![u64x2.clone()], vec![Ty::U64]),
        ParamPartial => (vec![Ty::U64, u16x3.clone()], vec![Ty::U16]),
        ParamByte => (vec![Ty::U64, u8x1.clone()], vec![Ty::U8]),
        ParamStruct => (vec![mixed.clone()], vec![Ty::U32]),
        ParamNineBytes => (vec![u8x9.clone()], vec![Ty::U8]),
        ParamBool => (vec![boolx2.clone()], vec![Ty::Bool]),
        ResultWord => (vec![Ty::U32], vec![u32x1.clone()]),
        ResultPair => (vec![Ty::U32, Ty::U32], vec![u32x2.clone()]),
        ResultTwoLanes => (vec![Ty::U64, Ty::U64], vec![u64x2.clone()]),
        ResultPartial => (vec![Ty::U8], vec![u8x5.clone()]),
        ResultByte => (vec![Ty::U8], vec![u8x1.clone()]),
        ResultForward => (vec![u16x2.clone()], vec![u16x2.clone()]),
        CallArg => (vec![Ty::U8], vec![Ty::U64]),
        CallResult => (vec![Ty::U64], vec![Ty::U32]),
        CallResultForward => (vec![Ty::U64], vec![u32x2.clone()]),
        CallArgForward => (vec![u64x2.clone()], vec![Ty::U64]),
        CallResultThenCall => (vec![Ty::U64], vec![Ty::U64]),
        CallResultBranch => (vec![Ty::U64], vec![Ty::U32]),
        CallResultWiden => (vec![Ty::U64], vec![Ty::U64]),
        ParamByteWiden => (vec![Ty::U64, u8x1.clone()], vec![Ty::U32]),
    };
    let signature = builder.add_func_type(params.clone(), results);
    let mut f = builder.function(shape.name(), signature);
    // An aggregate built field by field into its storage and used as that
    // storage, as the rustc bridge builds and returns one (`alloca`, then per
    // field its byte address and a typed `Store` there, the bridge's
    // `emit_aggregate_field_store` since WS7.1: `Const`, `PtrToInt`, `Add`,
    // `IntToPtr`, `Store`, which lower to `Iconst`, `Copy`, `Iadd`, `Copy`,
    // `Store`; `ret` and a by-value argument take the alloca itself). Every
    // aggregate built here is an array of `element`, so field `i` is at
    // `i * size_of(element)`. (The store form of `insert_field` the bridge
    // used before is invalid trust-ir and refused by name.)
    let build =
        |f: &mut trust_ir_build::FunctionBuilder<'_>, ty: &Ty, element: Ty, fields: Vec<_>| {
            let size: u64 = match element {
                Ty::U8 => 1,
                Ty::U16 => 2,
                Ty::U32 => 4,
                Ty::U64 => 8,
                ref other => panic!("no fixture builds an array of {other:?}"),
            };
            let storage = f.alloca(ty.clone());
            for (index, field) in (0u64..).zip(fields) {
                let offset = f.iconst(Ty::I64, i128::from(index * size));
                let base = f.cast(trust_ir::CastOp::PtrToInt, Ty::Ptr, Ty::I64, storage);
                let address = f.binop(BinOp::Add, Ty::I64, base, offset);
                let address = f.cast(trust_ir::CastOp::IntToPtr, Ty::I64, Ty::Ptr, address);
                f.store(element.clone(), address, field);
            }
            storage
        };
    let entry = f.create_block();
    let args: Vec<_> = params
        .iter()
        .map(|ty| f.add_block_param(entry, ty.clone()))
        .collect();
    f.switch_to_block(entry);
    match shape {
        ParamField => {
            let field = f.extract_field(Ty::U8, args[0], 2);
            f.ret(vec![field]);
        }
        ParamWord => {
            let word = f.extract_field(Ty::U64, args[0], 0);
            let sum = f.add(Ty::U64, word, args[1]);
            f.ret(vec![sum]);
        }
        ParamTwoLanes => {
            let low = f.extract_field(Ty::U64, args[0], 0);
            let high = f.extract_field(Ty::U64, args[0], 1);
            let difference = f.binop(BinOp::Sub, Ty::U64, low, high);
            f.ret(vec![difference]);
        }
        ParamPartial => {
            let last = f.extract_field(Ty::U16, args[1], 2);
            f.ret(vec![last]);
        }
        ParamByte => {
            let byte = f.extract_field(Ty::U8, args[1], 0);
            f.ret(vec![byte]);
        }
        ParamStruct => {
            let a = f.extract_field(Ty::U32, args[0], 0);
            let c = f.extract_field(Ty::U8, args[0], 2);
            let wide = f.zext(Ty::U8, Ty::U32, c);
            let sum = f.add(Ty::U32, a, wide);
            f.ret(vec![sum]);
        }
        ParamNineBytes => {
            let first = f.extract_field(Ty::U8, args[0], 0);
            let last = f.extract_field(Ty::U8, args[0], 8);
            let mixed = f.binop(BinOp::Xor, Ty::U8, first, last);
            f.ret(vec![mixed]);
        }
        ParamBool => {
            let flag = f.extract_field(Ty::Bool, args[0], 1);
            f.ret(vec![flag]);
        }
        ResultWord => {
            let value = build(&mut f, &u32x1, Ty::U32, vec![args[0]]);
            f.ret(vec![value]);
        }
        ResultPair => {
            let value = build(&mut f, &u32x2, Ty::U32, vec![args[0], args[1]]);
            f.ret(vec![value]);
        }
        ResultTwoLanes => {
            let value = build(&mut f, &u64x2, Ty::U64, vec![args[0], args[1]]);
            f.ret(vec![value]);
        }
        ResultPartial => {
            let (one, two, three) = (
                f.iconst(Ty::U8, 1),
                f.iconst(Ty::U8, 2),
                f.iconst(Ty::U8, 3),
            );
            let value = build(
                &mut f,
                &u8x5,
                Ty::U8,
                vec![args[0], one, two, three, args[0]],
            );
            f.ret(vec![value]);
        }
        ResultByte => {
            let value = build(&mut f, &u8x1, Ty::U8, vec![args[0]]);
            f.ret(vec![value]);
        }
        ResultForward => {
            f.ret(vec![args[0]]);
        }
        CallArg => {
            let one = f.iconst(Ty::U8, 1);
            let two = f.iconst(Ty::U8, 2);
            let bytes = build(&mut f, &u8x4, Ty::U8, vec![args[0], one, two, args[0]]);
            let result = f.call(take4, vec![bytes]);
            f.ret(vec![result]);
        }
        CallResult => {
            let pair = f.call(give2, vec![args[0]]);
            let a = f.extract_field(Ty::U32, pair, 0);
            let b = f.extract_field(Ty::U32, pair, 1);
            let mixed = f.binop(BinOp::Xor, Ty::U32, a, b);
            f.ret(vec![mixed]);
        }
        CallResultForward => {
            let pair = f.call(give2, vec![args[0]]);
            f.ret(vec![pair]);
        }
        CallArgForward => {
            let result = f.call(take2, vec![args[0]]);
            f.ret(vec![result]);
        }
        CallResultThenCall => {
            let pair = f.call(give2w, vec![args[0]]);
            let result = f.call(take2, vec![pair]);
            f.ret(vec![result]);
        }
        CallResultBranch => {
            let pair = f.call(give2, vec![args[0]]);
            let tag = f.extract_field(Ty::U32, pair, 0);
            let zero = f.iconst(Ty::U32, 0);
            let none = f.icmp(ICmpOp::Eq, Ty::U32, tag, zero);
            let (some_block, none_block, join) =
                (f.create_block(), f.create_block(), f.create_block());
            let result = f.add_block_param(join, Ty::U32);
            f.condbr(none, none_block, vec![], some_block, vec![]);
            f.switch_to_block(some_block);
            let payload = f.extract_field(Ty::U32, pair, 1);
            f.br(join, vec![payload]);
            f.switch_to_block(none_block);
            let seven = f.iconst(Ty::U32, 7);
            f.br(join, vec![seven]);
            f.switch_to_block(join);
            f.ret(vec![result]);
        }
        CallResultWiden => {
            let one = f.call(give1, vec![args[0]]);
            let lane = f.extract_field(Ty::U32, one, 0);
            let wide = f.zext(Ty::U32, Ty::U64, lane);
            f.ret(vec![wide]);
        }
        ParamByteWiden => {
            let byte = f.extract_field(Ty::U8, args[1], 0);
            let wide = f.zext(Ty::U8, Ty::U32, byte);
            f.ret(vec![wide]);
        }
    }
    f.build();
    let module = builder.build().expect("ModuleBuilder::build: test fixture");
    trust_cg_lower::translate_module_for_arch_with_tls_with_license(
        &module,
        trust_cg_lower::GuardCarrierArch::X86_64,
        trust_cg_lower::TlsDialect::default(),
        &crate::license_test_support::permit_unlicensed(),
    )
    .unwrap_or_else(|error| panic!("{shape:?}: fixture translates: {error:?}"))
    .into_iter()
    .map(|(function, _)| function)
    .find(|function| function.name == shape.name())
    .unwrap_or_else(|| panic!("{shape:?}: no translated function"))
}

pub(crate) fn slice8_pair(shape: AggShape) -> (Function, X86ISelFunction) {
    let source = slice8_lir(shape);
    let machine = select(&source, X86CallAbi::SystemV);
    (source, machine)
}

/// Every fixture shape, in declaration order.
pub(crate) fn all_slice_eight_shapes() -> Vec<AggShape> {
    use AggShape::*;
    let all = SLICE_EIGHT.to_vec();
    // Exhaustive: a new shape does not compile until it is listed here.
    for shape in &all {
        match shape {
            ParamField | ParamWord | ParamTwoLanes | ParamPartial | ParamByte | ParamStruct
            | ParamNineBytes | ParamBool | ResultWord | ResultPair | ResultTwoLanes
            | ResultPartial | ResultByte | ResultForward | CallArg | CallResult
            | CallResultForward | CallArgForward | CallResultThenCall | CallResultBranch
            | CallResultWiden | ParamByteWiden => {}
        }
    }
    all
}

// ---------------------------------------------------------------------------
// The sampler (test-only semantics check; never credit)
// ---------------------------------------------------------------------------

/// Whether `obligation` is a several-path theorem.
fn path_form(obligation: &ProofObligation) -> bool {
    obligation.trust_ir_expr == E::bool_const(true)
        && matches!(
            &obligation.aarch64_expr,
            E::And { lhs, .. } if matches!(lhs.as_ref(), E::Or { .. })
        )
}

/// Whether sample `seed` zeroes byte `byte` of every free input: at seeds
/// `6k + 3` the boundary `k mod 9` steps through every byte of a 64-bit
/// word, zeroing the bytes below it for even `k / 9` and the bytes at or
/// above it for odd. An aggregate's fields share one register, so a field
/// read at another offset or width differs from the right one only when its
/// neighbour's bytes differ from its own: each byte is zero here while its
/// neighbours are not, and the reverse.
fn zeroed_byte(seed: u64, byte: u32) -> bool {
    if seed % 6 != 3 {
        return false;
    }
    let k = seed / 6;
    let boundary = (k % 9) as u32;
    if (k / 9).is_multiple_of(2) {
        byte < boundary
    } else {
        byte >= boundary
    }
}

/// Evaluate the theorem at one sampled assignment of its free inputs (the
/// premises are definitional): whether its observable holds and, for a
/// several-path theorem, which source paths' conditions hold. Every sixth
/// sample sets every input to 0; the samples at `6k + 3` zero the bytes of
/// every input on one side of a byte boundary ([`zeroed_byte`]).
fn evaluate_sample(obligation: &ProofObligation, seed: u64) -> (bool, Option<Vec<bool>>) {
    use crate::smt::{EvalEnv, EvalResult};
    let mut env = EvalEnv::default();
    let mut state = seed.wrapping_add(0x51ce_8a9b_0d3f_2e17);
    for (name, width) in free_inputs_of(obligation) {
        state = state
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        let high = state >> 29;
        let mut value = if seed.is_multiple_of(6) {
            0
        } else {
            match seed % 4 {
                0 => high & 0xff,
                1 => high % 12,
                2 => state ^ (state << 13),
                _ => state ^ (state >> 31),
            }
        };
        for byte in 0..width.div_ceil(8) {
            if zeroed_byte(seed, byte) {
                value &= !(0xffu64 << (8 * byte));
            }
        }
        env.insert(name, crate::smt::mask(value, width));
    }
    for premise in obligation.preconditions.iter().rev() {
        let E::Eq { lhs, rhs } = premise else {
            panic!("premise {premise} is not an equation")
        };
        let E::Var { name, .. } = lhs.as_ref() else {
            panic!("premise {premise} defines no name")
        };
        let EvalResult::Bv(value) = rhs.eval(&env) else {
            panic!("definition of {name} is not a bitvector")
        };
        env.insert(name.clone(), value);
    }
    if path_form(obligation) {
        let holds = |expr: &E| matches!(expr.eval(&env), EvalResult::Bool(true));
        let conditions = path_claims(obligation)
            .iter()
            .map(|(condition, _)| holds(condition))
            .collect();
        (holds(&obligation.aarch64_expr), Some(conditions))
    } else {
        let agree = observable_items(obligation)
            .iter()
            .all(|(source, machine)| source.eval(&env) == machine.eval(&env));
        (agree, None)
    }
}

const SAMPLES: u64 = 1080;

/// Whether the theorem holds at every sample, (several paths) every path is
/// exercised, and the slice-7 sampler (and through it the earlier slices')
/// finds no refutation either.
pub(crate) fn theorem_holds(obligation: &ProofObligation) -> bool {
    let mut exercised: Option<Vec<bool>> = None;
    for seed in 0..SAMPLES {
        let (holds, conditions) = evaluate_sample(obligation, seed);
        if !holds {
            return false;
        }
        if let Some(conditions) = conditions {
            assert_eq!(
                conditions.iter().filter(|c| **c).count(),
                1,
                "exactly one source path is taken at seed {seed}"
            );
            let seen = exercised.get_or_insert_with(|| vec![false; conditions.len()]);
            for (seen, now) in seen.iter_mut().zip(conditions) {
                *seen |= now;
            }
        }
    }
    exercised.is_none_or(|seen| seen.into_iter().all(|seen| seen))
        && super::slice7::theorem_holds(obligation)
}

/// Whether some sample refutes the theorem (this sampler or slice 7's).
pub(crate) fn theorem_refuted(obligation: &ProofObligation) -> bool {
    (0..SAMPLES).any(|seed| !evaluate_sample(obligation, seed).0)
        || super::slice7::theorem_refuted(obligation)
        || (path_form(obligation) && paths_refuted_on_samples(obligation))
}

#[track_caller]
fn owner(source: &Function, machine: &X86ISelFunction, what: &str) -> ProofObligation {
    source_bound_x86_body(source, machine, SYSV)
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

/// A wrong lowering whose theorem the owner builds without its exact affine
/// refusal must be refuted on samples (the replay refutes it on the
/// qualification host).
#[track_caller]
fn refuted(source: &Function, machine: &X86ISelFunction, what: &str) {
    let theorem = theorem_without_affine_refusal(source, machine, SYSV)
        .unwrap_or_else(|refusal| panic!("{what}: {refusal}\n{}", describe(machine)));
    assert!(
        theorem_refuted(&theorem),
        "{what}: the theorem must refute the wrong lowering\n{}",
        describe(machine)
    );
}

/// A wrong lowering that the owner names as a mismatch or refutes: never a
/// theorem that holds.
#[track_caller]
fn never_credited(source: &Function, machine: &X86ISelFunction, what: &str) {
    match source_bound_x86_body(source, machine, SYSV) {
        Ok(owner) => assert!(
            theorem_refuted(owner.obligation()),
            "{what}: the theorem must refute the wrong lowering\n{}",
            describe(machine)
        ),
        Err(X86BodyRefusal::Mismatch(_)) => {}
        Err(X86BodyRefusal::Unsupported(refusal)) => {
            panic!("{what}: expected a refutation or a named mismatch, got {refusal}")
        }
    }
}

// ---------------------------------------------------------------------------
// Construction (no solver)
// ---------------------------------------------------------------------------

/// The selector's slot table is the source's, then the copy of each
/// aggregate parameter and the slot of each aggregate call result, at the
/// aggregate's size and alignment ([`SourceBody::machine_slots`]).
#[test]
fn slice_eight_fixtures_have_the_expected_pre_ra_shapes() {
    for shape in SLICE_EIGHT {
        let (source, machine) = slice8_pair(shape);
        let text = format!("{shape:?}\n{}{}", describe_lir(&source), describe(&machine));
        let body = admitted_body(&source).unwrap_or_else(|refusal| panic!("{text}{refusal}"));
        assert_eq!(machine.stack_slots, body.machine_slots, "{text}");
        let aggregate = |ty: &Type| matches!(ty, Type::Struct(_) | Type::Array(..));
        let results = source
            .blocks
            .values()
            .flat_map(|block| &block.instructions)
            .filter(|inst| {
                matches!(inst.opcode, L::Call { .. })
                    && inst.results.len() == 1
                    && source
                        .value_types
                        .get(&inst.results[0])
                        .is_some_and(aggregate)
            })
            .count();
        let copies = source
            .signature
            .params
            .iter()
            .filter(|ty| aggregate(ty))
            .count();
        assert_eq!(
            machine.stack_slots.len(),
            source.stack_slots.len() + copies + results,
            "{text}"
        );
    }
}

#[test]
fn owner_builds_for_every_slice_eight_shape_and_covers_every_value_row() {
    for shape in SLICE_EIGHT {
        let (source, machine) = slice8_pair(shape);
        let body = source_bound_x86_body(&source, &machine, SYSV).unwrap_or_else(|refusal| {
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
                        X86Opcode::Jmp | X86Opcode::Ret | X86Opcode::Call | X86Opcode::Ud2
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
fn slice_eight_theorems_hold_on_samples() {
    for shape in SLICE_EIGHT {
        let (source, machine) = slice8_pair(shape);
        let obligation = owner(&source, &machine, &format!("{shape:?}"));
        assert!(
            theorem_holds(&obligation),
            "{shape:?}\n{}",
            describe(&machine)
        );
    }
}

/// The golden, owner, credit and host-qualification tests run over
/// [`SLICE_EIGHT`]: every fixture whose real selection the owner admits with a
/// theorem that holds must be in it.
#[test]
fn every_admitted_slice_eight_fixture_is_qualified() {
    for shape in all_slice_eight_shapes() {
        let (source, machine) = slice8_pair(shape);
        let holds = source_bound_x86_body(&source, &machine, SYSV)
            .is_ok_and(|owner| theorem_holds(owner.obligation()));
        assert_eq!(SLICE_EIGHT.contains(&shape), holds, "{shape:?}");
    }
}

/// The model on real fixtures: an aggregate result's eightbytes are observed
/// at their own bytes in RAX and RDX, an aggregate argument's at its own
/// bytes in its argument register, and an aggregate parameter's field is an
/// extract of the argument register (no SMT term for its slot).
#[test]
fn eightbytes_are_observed_at_their_own_bytes() {
    let widths = |shape: AggShape| {
        let (source, machine) = slice8_pair(shape);
        observable_items(&owned_plain_theorem(
            &source,
            &machine,
            &format!("{shape:?}"),
        ))
        .iter()
        .map(|(source, _)| source.bv_width())
        .collect::<Vec<_>>()
    };
    // `[u8; 5]` in RAX: one 40-bit item.
    assert_eq!(widths(AggShape::ResultPartial), [40]);
    // `[u64; 2]` returned: RAX, then RDX.
    assert_eq!(widths(AggShape::ResultTwoLanes), [64, 64]);
    // `[u8; 1]` in AL.
    assert_eq!(widths(AggShape::ResultByte), [8]);
    // `take4([x, 1, 2, x])`: the 64-bit result and the 32-bit argument.
    assert_eq!(widths(AggShape::CallArg), [64, 32]);
    // `take2(p)` forwards a parameter: its eightbytes are RDI and RSI at entry.
    let (source, machine) = slice8_pair(AggShape::CallArgForward);
    let items = observable_items(&owned_plain_theorem(&source, &machine, "CallArgForward"));
    assert!(
        items.iter().any(|(s, _)| *s == E::var("e_rdi", 64))
            && items.iter().any(|(s, _)| *s == E::var("e_rsi", 64)),
        "{items:?}"
    );
    // `a[2]` of `[u8; 4]` reads bits 16..23 of RDI.
    let (source, machine) = slice8_pair(AggShape::ParamField);
    let obligation = owned_plain_theorem(&source, &machine, "ParamField");
    let premises = format!("{:?}", obligation.preconditions);
    assert!(premises.contains("e_rdi"), "{premises}");
}

/// What slice 8 adds to every fixture: an aggregate parameter, result,
/// by-value argument or call result.
#[test]
fn every_slice_eight_fixture_passes_an_aggregate_by_value() {
    for shape in SLICE_EIGHT {
        let source = slice8_lir(shape);
        let body = admitted_body(&source).unwrap();
        let by_value_argument = body.paths.iter().flat_map(|path| &path.calls).any(|call| {
            call.args
                .iter()
                .any(|arg| matches!(arg, CallArg::Aggregate(_)))
        });
        let aggregate_result = body.paths.iter().any(|path| {
            path.return_tys
                .iter()
                .any(|lane| matches!(lane, ReturnLane::Eightbyte(_)))
        });
        let aggregate_param = body.paths[0]
            .params
            .iter()
            .any(|param| matches!(param.abi, ParamAbi::Aggregate { .. }));
        let aggregate_call_result = source
            .value_types
            .values()
            .any(|ty| matches!(ty, Type::Struct(_) | Type::Array(..)));
        assert!(
            by_value_argument || aggregate_result || aggregate_param || aggregate_call_result,
            "{shape:?}"
        );
    }
}

// ---------------------------------------------------------------------------
// The System V classification is checked against the selector's own
// ---------------------------------------------------------------------------

type NamedTypes = Vec<(String, Ty)>;

/// The aggregate types of the classification sweep: integer arrays of every
/// size from 1 to 16 bytes, structs with interior and tail padding, nested
/// aggregates and `bool` fields; then types the lane refuses by name.
fn sweep_types(builder: &mut ModuleBuilder) -> (NamedTypes, NamedTypes) {
    let mut struct_id = 100;
    let mut record = |builder: &mut ModuleBuilder, fields: Vec<Ty>| {
        struct_id += 1;
        Ty::Struct(
            builder.add_struct(StructDef {
                origin: None,
                id: StructId::new(struct_id),
                name: format!("Sweep{struct_id}"),
                fields: fields
                    .into_iter()
                    .enumerate()
                    .map(|(i, ty)| FieldDef {
                        name: format!("f{i}"),
                        ty,
                        offset: None,
                    })
                    .collect(),
                size: None,
                align: None,
                repr: StructRepr::C,
            }),
        )
    };
    let mut admitted = Vec::new();
    for (element, size, counts) in [
        (Ty::U8, 1, 1..=16),
        (Ty::U16, 2, 1..=8),
        (Ty::U32, 4, 1..=4),
        (Ty::U64, 8, 1..=2),
        (Ty::Bool, 1, 1..=3),
    ] {
        for count in counts {
            let id = builder.add_type(element.clone());
            admitted.push((
                format!("[{element:?}; {count}] ({} bytes)", size * count),
                Ty::Array(id, count),
            ));
        }
    }
    let u8x3 = {
        let id = builder.add_type(Ty::U8);
        Ty::Array(id, 3)
    };
    for fields in [
        vec![Ty::U8, Ty::U32],
        vec![Ty::U32, Ty::U8],
        vec![Ty::U16, Ty::U8, Ty::U32],
        vec![Ty::U64, Ty::U8],
        vec![Ty::U8, Ty::U64],
        vec![Ty::U32, Ty::U32, Ty::U32],
        vec![Ty::U8, Ty::U16],
        vec![Ty::U64, Ty::U16, Ty::U8],
        vec![Ty::Bool, Ty::U32],
        vec![Ty::U8, u8x3.clone()],
        vec![Ty::U32, u8x3.clone(), Ty::Bool],
    ] {
        let name = format!("{fields:?}");
        let ty = record(builder, fields);
        admitted.push((name, ty));
    }
    let inner = record(builder, vec![Ty::U16, Ty::U8]);
    admitted.push((
        "{ {u16, u8}, u32 }".into(),
        record(builder, vec![inner, Ty::U32]),
    ));
    let mut refused = Vec::new();
    for fields in [
        vec![Ty::F64],
        vec![Ty::U64, Ty::F64],
        vec![Ty::F32, Ty::U32],
        vec![Ty::U64, Ty::U64, Ty::U8],
    ] {
        let name = format!("{fields:?}");
        let ty = record(builder, fields);
        refused.push((name, ty));
    }
    let u8x17 = {
        let id = builder.add_type(Ty::U8);
        Ty::Array(id, 17)
    };
    refused.push(("[u8; 17]".into(), u8x17));
    let f32x2 = {
        let id = builder.add_type(Ty::F32);
        Ty::Array(id, 2)
    };
    refused.push(("[f32; 2]".into(), f32x2));
    (admitted, refused)
}

/// `fn f(x: T) -> T { g(x) }` for every sweep type `T`, through the adapter
/// and the real selector: the parameter's copy, the by-value argument, the
/// call result's slot and the returned eightbytes all follow the selector's
/// own classifier, and the theorem states the verify-owned one
/// ([`classify_aggregate`]). Where the lane admits `T`, the owner builds
/// without a mismatch (the call row declares exactly the argument and result
/// registers and widths the verify-owned classification gives) and the
/// theorem holds on samples, unless a 3-byte eightbyte makes the selector
/// move it through a register of another width (a row no slice admits: no
/// claim). Where it refuses `T`, it says why by name.
#[test]
fn the_verify_owned_classification_agrees_with_the_selector() {
    let mut builder = ModuleBuilder::new("x86_source_bound_body_slice8_sweep");
    let (admitted, refused) = sweep_types(&mut builder);
    let mut names = Vec::new();
    for (k, (_, ty)) in admitted.iter().chain(&refused).enumerate() {
        let callee = format!("sweep_callee_{k}");
        let signature = builder.add_func_type(vec![ty.clone()], vec![ty.clone()]);
        let callee_id = builder.declare_function(&callee, signature);
        let name = format!("sweep_{k}");
        let mut f = builder.function(&name, signature);
        let entry = f.create_block();
        let x = f.add_block_param(entry, ty.clone());
        f.switch_to_block(entry);
        let y = f.call(callee_id, vec![x]);
        f.ret(vec![y]);
        f.build();
        names.push(name);
    }
    let module = builder.build().expect("ModuleBuilder::build: test fixture");
    let lir: HashMap<String, Function> =
        trust_cg_lower::translate_module_for_arch_with_tls_with_license(
            &module,
            trust_cg_lower::GuardCarrierArch::X86_64,
            trust_cg_lower::TlsDialect::default(),
            &crate::license_test_support::permit_unlicensed(),
        )
        .expect("sweep translates")
        .into_iter()
        .map(|(function, _)| (function.name.clone(), function))
        .collect();
    let (mut built, mut three_byte) = (0, 0);
    for (k, (label, _)) in admitted.iter().enumerate() {
        let source = &lir[&names[k]];
        let aggregate = classify_aggregate(&source.signature.params[0])
            .unwrap_or_else(|reason| panic!("{label}: {reason}"));
        assert_eq!(
            (aggregate.size, aggregate.align),
            (
                source.signature.params[0].bytes(),
                source.signature.params[0].align()
            ),
            "{label}: the verify-owned layout and the LIR type's"
        );
        let machine = select(source, X86CallAbi::SystemV);
        let call = &machine
            .blocks
            .values()
            .flat_map(|b| &b.insts)
            .find(|i| i.opcode == X86Opcode::Call)
            .expect("a call")
            .clone();
        let expected_args: Vec<(u16, u16)> = aggregate
            .lanes
            .iter()
            .zip(SYSV_ARGUMENT_ROOTS)
            .map(|(lane, root)| (root, lane.register_bits() as u16))
            .collect();
        let expected_results: Vec<(u16, u16)> = aggregate
            .lanes
            .iter()
            .zip(SYSV_RETURN_ROOTS)
            .map(|(lane, root)| (root, lane.register_bits() as u16))
            .collect();
        let declared_args: Vec<(u16, u16)> = call
            .call_arg_regs
            .iter()
            .map(|arg| (arg.reg.encoding(), arg.read_bits))
            .collect();
        let declared_results: Vec<(u16, u16)> = call
            .call_result_regs
            .iter()
            .flatten()
            .map(|result| (result.reg.encoding(), result.defined_bits))
            .collect();
        assert_eq!(
            declared_args,
            expected_args,
            "{label}\n{}",
            describe(&machine)
        );
        assert_eq!(
            declared_results,
            expected_results,
            "{label}\n{}",
            describe(&machine)
        );
        match source_bound_x86_body(source, &machine, SYSV) {
            Ok(owner) => {
                assert!(
                    theorem_holds(owner.obligation()),
                    "{label}\n{}",
                    describe(&machine)
                );
                built += 1;
            }
            Err(X86BodyRefusal::Unsupported(X86BodyUnsupported::MachineRow { .. }))
                if aggregate.lanes.iter().any(|lane| lane.bytes == 3) =>
            {
                three_byte += 1;
            }
            Err(other) => panic!("{label}: {other}\n{}", describe(&machine)),
        }
    }
    // Slice 15: the 3-byte eightbytes, moved through registers of mixed
    // width, build theorems that hold too.
    assert_eq!(
        (admitted.len(), built, three_byte, refused.len()),
        (45, 45, 0, 6),
        "admitted types, theorems that hold, 3-byte eightbyte refusals, refused types"
    );
    for (k, (label, _)) in refused.iter().enumerate() {
        let source = &lir[&names[admitted.len() + k]];
        let refusal = source_bound_x86_body_refusal(source);
        assert!(
            refusal.contains("outside the System V INTEGER register class"),
            "{label}: {refusal}"
        );
    }
}

/// The owner's refusal of `source` before any machine is inspected.
fn source_bound_x86_body_refusal(source: &Function) -> String {
    match admitted_body(source) {
        Ok(_) => panic!("{} is admitted", source.name),
        Err(refusal) => refusal.to_string(),
    }
}

/// The verify-owned classification on LIR types the sweep cannot build:
/// an enum, a vector field, an eightbyte with no field cannot occur in C
/// layout; every refusal is named. (Slice 11 admits an `i128` field that
/// fills both eightbytes.)
#[test]
fn the_classification_refuses_by_name() {
    use trust_cg_ir::function::EnumTagWidth;
    let cases: Vec<(Type, &str)> = vec![
        (
            Type::Enum {
                tag_width: EnumTagWidth::U8,
                variants: vec![vec![Type::I32]],
            },
            "an enum",
        ),
        (Type::Struct(vec![Type::V128]), "a vector field"),
        (Type::Struct(vec![Type::F32, Type::F32]), "an SSE eightbyte"),
        (Type::Array(Box::new(Type::I64), 3), "over 16 bytes"),
        (Type::Struct(vec![]), "an empty aggregate"),
        (Type::I32, "not an aggregate"),
    ];
    for (ty, reason) in cases {
        let refusal = classify_aggregate(&ty).expect_err("refused");
        assert!(refusal.contains(reason), "{ty:?}: {refusal}");
    }
    let lanes = |ty: Type| {
        classify_aggregate(&ty)
            .unwrap()
            .lanes
            .iter()
            .map(|lane| (lane.offset, lane.bytes, lane.register_bits()))
            .collect::<Vec<_>>()
    };
    assert_eq!(lanes(Type::Array(Box::new(Type::I8), 3)), [(0, 3, 32)]);
    assert_eq!(
        lanes(Type::Array(Box::new(Type::I8), 13)),
        [(0, 8, 64), (8, 5, 64)]
    );
    assert_eq!(
        lanes(Type::Struct(vec![Type::I64, Type::I16])),
        [(0, 8, 64), (8, 8, 64)]
    );
    assert_eq!(lanes(Type::Struct(vec![Type::I8])), [(0, 1, 8)]);
    // Slice 11: an `i128` field is two whole INTEGER eightbytes.
    assert_eq!(
        lanes(Type::Struct(vec![Type::I128])),
        [(0, 8, 64), (8, 8, 64)]
    );
}

/// Every aggregate shape outside the lane is refused before the machine is
/// inspected, by name: a 16-bit float or vector parameter or result (slice
/// 11 admits `i128` and `f32`/`f64` ones), an aggregate or `i128` result
/// beside another result, and parameters needing more than six argument
/// registers (or eight SSE ones).
#[test]
fn values_outside_the_register_lane_are_refused_by_name() {
    let (add, _) = pair(Shape::Add);
    let pair_of_u64 = Type::Array(Box::new(Type::I64), 2);
    let cases: Vec<(Vec<Type>, Vec<Type>, &str)> = vec![
        (
            vec![Type::V128],
            vec![Type::I64],
            "has an f16 or vector parameter",
        ),
        (
            vec![Type::F16],
            vec![Type::I64],
            "has an f16 or vector parameter",
        ),
        (
            vec![Type::I64],
            vec![Type::V128],
            "has an f16 or vector result",
        ),
        (
            vec![Type::I64],
            vec![Type::I128, Type::I64],
            "has an i128 result beside another result",
        ),
        (
            vec![Type::F64; 9],
            vec![Type::I64],
            "passes its parameters in more than six argument registers (or eight SSE",
        ),
        // (Slice 15 admits an `I128` on the stack, `[I64; 5]` then `I128`;
        // a `bool` there stays outside.)
        (
            vec![
                Type::I64,
                Type::I64,
                Type::I64,
                Type::I64,
                Type::I64,
                Type::I64,
                Type::B1,
            ],
            vec![Type::I64],
            "passes its parameters in more than six argument registers",
        ),
        (
            vec![Type::I64],
            vec![pair_of_u64.clone(), Type::I64],
            "has an aggregate result beside another result",
        ),
        // An aggregate past the six integer registers (slice 13 admits an
        // `I64` there, on the stack, but no aggregate).
        (
            vec![
                pair_of_u64.clone(),
                pair_of_u64.clone(),
                pair_of_u64.clone(),
                pair_of_u64.clone(),
            ],
            vec![Type::I64],
            "passes its parameters in more than six argument registers",
        ),
        (
            vec![Type::Array(Box::new(Type::I8), 17)],
            vec![Type::I64],
            "over 16 bytes (MEMORY class)",
        ),
    ];
    for (params, returns, reason) in cases {
        let mut source = add.clone();
        source.signature.params = params.clone();
        source.signature.returns = returns.clone();
        let refusal = match admitted_frame(&source) {
            Ok(_) => panic!("{params:?} -> {returns:?} is admitted"),
            Err(refusal) => refusal.to_string(),
        };
        assert!(
            refusal.contains(reason),
            "{params:?} -> {returns:?}: {refusal}"
        );
    }
}

// ---------------------------------------------------------------------------
// Wrong lowerings (controls): never credited
// ---------------------------------------------------------------------------

/// The walk ordinal of the first row satisfying `predicate`.
#[track_caller]
fn row_where(machine: &X86ISelFunction, predicate: impl Fn(&X86ISelInst) -> bool) -> usize {
    rows(machine)
        .into_iter()
        .map(|(ordinal, _, _)| ordinal)
        .find(|ordinal| predicate(inst(machine, *ordinal)))
        .unwrap_or_else(|| panic!("no such row\n{}", describe(machine)))
}

/// The displacement of a row's `[base + disp]` memory operand.
fn disp_mut(inst: &mut X86ISelInst) -> &mut i32 {
    inst.operands
        .iter_mut()
        .find_map(|operand| match operand {
            O::MemAddr { disp, .. } => Some(disp),
            _ => None,
        })
        .expect("a memory operand")
}

fn is_store_from(inst: &X86ISelInst, opcode: X86Opcode, disp: i32) -> bool {
    inst.opcode == opcode && matches!(&inst.operands[0], O::MemAddr { disp: d, .. } if *d == disp)
}

fn writes(inst: &X86ISelInst, opcode: X86Opcode, encoding: u16) -> bool {
    inst.opcode == opcode && inst.operands.first() == Some(&preg(encoding))
}

/// Each wrong lowering of an aggregate's eightbytes the owner binds, with
/// the fixture it mutates. Every one changes what a caller or callee can
/// observe for some input (the robustness probe's independent interpreter
/// agrees), so its theorem must be refuted; `slice8_qualification` replays
/// each to an AY counterexample.
pub(crate) fn slice_eight_refutations() -> Vec<(&'static str, Function, X86ISelFunction)> {
    let mut cases = Vec::new();
    // The two eightbytes of a parameter swapped: RSI's bytes stored at +0.
    let (source, mut machine) = slice8_pair(AggShape::ParamTwoLanes);
    let low = row_where(&machine, |i| is_store_from(i, X86Opcode::MovMR, 0));
    let high = row_where(&machine, |i| is_store_from(i, X86Opcode::MovMR, 8));
    let (a, b) = (
        inst(&machine, low).operands[1].clone(),
        inst(&machine, high).operands[1].clone(),
    );
    inst_mut(&mut machine, low).operands[1] = b;
    inst_mut(&mut machine, high).operands[1] = a;
    cases.push(("ParamTwoLanes/swapped-halves", source, machine));
    // A parameter's eightbyte taken from the next register.
    let (source, mut machine) = slice8_pair(AggShape::ParamWord);
    let copy = row_where(&machine, |i| {
        i.opcode == X86Opcode::MovRR && i.operands.get(1) == Some(&preg(RDI))
    });
    inst_mut(&mut machine, copy).operands[1] = preg(RSI);
    cases.push(("ParamWord/wrong-register", source, machine));
    // A field read at another offset.
    let (source, mut machine) = slice8_pair(AggShape::ParamField);
    let field = row_where(&machine, |i| {
        i.opcode == X86Opcode::Lea && matches!(&i.operands[1], O::MemAddr { disp: 2, .. })
    });
    *disp_mut(inst_mut(&mut machine, field)) = 1;
    cases.push(("ParamField/wrong-offset", source, machine));
    // A partial eightbyte's last piece stored one byte short.
    let (source, mut machine) = slice8_pair(AggShape::ParamPartial);
    let piece = row_where(&machine, |i| is_store_from(i, X86Opcode::MovMR16, 4));
    inst_mut(&mut machine, piece).opcode = X86Opcode::MovMR8;
    cases.push(("ParamPartial/short-store", source, machine));
    // A `u8` field sign-extended where the source zero-extends it: the
    // copy of its zero-extending load (`movzx r32, m8`) re-extends the byte
    // with its sign.
    let (source, mut machine) = slice8_pair(AggShape::ParamStruct);
    let load = row_where(&machine, |i| i.opcode == X86Opcode::MovzxRM8);
    let loaded = inst(&machine, load).operands[0].clone();
    let extend = row_where(&machine, |i| {
        i.opcode == X86Opcode::MovRR32 && i.operands.get(1) == Some(&loaded)
    });
    inst_mut(&mut machine, extend).opcode = X86Opcode::MovsxB;
    cases.push(("ParamStruct/sign-extended", source, machine));
    // The two result eightbytes returned in each other's register.
    let (source, mut machine) = slice8_pair(AggShape::ResultTwoLanes);
    let rax = row_where(&machine, |i| writes(i, X86Opcode::MovRM, RAX));
    let rdx = row_where(&machine, |i| writes(i, X86Opcode::MovRM, RDX));
    *disp_mut(inst_mut(&mut machine, rax)) = 8;
    *disp_mut(inst_mut(&mut machine, rdx)) = 0;
    cases.push(("ResultTwoLanes/swapped-registers", source, machine));
    // A 4-byte result eightbyte returned through AX: its high half is not
    // the result's.
    let (source, mut machine) = slice8_pair(AggShape::ResultWord);
    let load = row_where(&machine, |i| {
        writes(i, X86Opcode::MovRM32, GPR32_ALIAS_BASE + RAX)
    });
    let row = inst_mut(&mut machine, load);
    row.opcode = X86Opcode::MovRM16;
    row.operands[0] = preg(GPR16_ALIAS_BASE + RAX);
    cases.push(("ResultWord/narrowed", source, machine));
    // A partial result eightbyte assembled without its low piece (the tied
    // `or` replaced by a move).
    let (source, mut machine) = slice8_pair(AggShape::ResultPartial);
    let or = row_where(&machine, |i| {
        i.opcode == X86Opcode::OrRR && i.operands.len() == 2
    });
    inst_mut(&mut machine, or).opcode = X86Opcode::MovRR;
    cases.push(("ResultPartial/or-dropped", source, machine));
    // A partial result eightbyte whose top byte is read one byte low (only
    // the eightbyte's last byte is wrong).
    let (source, mut machine) = slice8_pair(AggShape::ResultPartial);
    let top = row_where(&machine, |i| {
        matches!(i.opcode, X86Opcode::MovRM8 | X86Opcode::MovzxRM8)
            && matches!(&i.operands[1], O::MemAddr { disp: 4, .. })
    });
    *disp_mut(inst_mut(&mut machine, top)) = 3;
    cases.push(("ResultPartial/top-byte-offset", source, machine));
    // An argument's two eightbytes passed in each other's register.
    let (source, mut machine) = slice8_pair(AggShape::CallArgForward);
    let rdi = row_where(&machine, |i| writes(i, X86Opcode::MovRM, RDI));
    let rsi = row_where(&machine, |i| writes(i, X86Opcode::MovRM, RSI));
    *disp_mut(inst_mut(&mut machine, rdi)) = 8;
    *disp_mut(inst_mut(&mut machine, rsi)) = 0;
    cases.push(("CallArgForward/swapped-registers", source, machine));
    // A call result's two eightbytes stored at each other's offset.
    let (source, mut machine) = slice8_pair(AggShape::CallResultThenCall);
    let low = row_where(&machine, |i| is_store_from(i, X86Opcode::MovMR, 0));
    let high = row_where(&machine, |i| is_store_from(i, X86Opcode::MovMR, 8));
    *disp_mut(inst_mut(&mut machine, low)) = 8;
    *disp_mut(inst_mut(&mut machine, high)) = 0;
    cases.push(("CallResultThenCall/swapped-stores", source, machine));
    // A 4-byte call result eightbyte used as all of RAX (no round trip
    // through its slot): the bits above it are not the callee's.
    let (source, mut machine) = slice8_pair(AggShape::CallResultWiden);
    let ret = find(&machine, X86Opcode::Ret)[0];
    remove_at(&mut machine, ret - 1);
    cases.push(("CallResultWiden/result-register-widened", source, machine));
    // A one-byte eightbyte loaded into AL and returned as a 32-bit value.
    let (source, mut machine) = slice8_pair(AggShape::ParamByteWiden);
    let lea = row_where(&machine, |i| {
        i.opcode == X86Opcode::Lea
            && matches!(&i.operands[1], O::MemAddr { base, .. } if matches!(base.as_ref(), O::StackSlot(0)))
    });
    let address = inst(&machine, lea).operands[0].clone();
    let ret = find(&machine, X86Opcode::Ret)[0];
    *inst_mut(&mut machine, ret - 1) = X86ISelInst::new(
        X86Opcode::MovRM8,
        vec![
            preg(GPR8_ALIAS_BASE + RAX),
            O::MemAddr {
                base: Box::new(address),
                disp: 0,
            },
        ],
    );
    cases.push(("ParamByteWiden/al-widened", source, machine));
    // A `bool` field read as its bit 0 rather than `byte != 0`.
    let (source, mut machine) = slice8_pair(AggShape::ParamBool);
    let add = row_where(&machine, |i| i.opcode == X86Opcode::AddRI);
    let shift = row_where(&machine, |i| i.opcode == X86Opcode::ShrRI);
    let row = inst_mut(&mut machine, add);
    row.opcode = X86Opcode::AndRI;
    row.operands[2] = O::Imm(1);
    let row = inst_mut(&mut machine, shift);
    let (destination, operand) = (row.operands[0].clone(), row.operands[1].clone());
    *row = X86ISelInst::new(X86Opcode::MovRR32, vec![destination, operand]);
    cases.push(("ParamBool/bit-zero", source, machine));
    cases
}

#[test]
fn every_slice_eight_refutation_is_refuted_on_samples() {
    for (label, source, machine) in slice_eight_refutations() {
        refuted(&source, &machine, label);
    }
}

/// A call row whose declared argument or result registers or widths differ
/// from the verify-owned classification is a named mismatch.
#[test]
fn a_wrong_eightbyte_declaration_is_a_named_mismatch() {
    let (source, mut machine) = slice8_pair(AggShape::CallArg);
    let call = find(&machine, X86Opcode::Call)[0];
    inst_mut(&mut machine, call).call_arg_regs[0] = X86CallArgReg::new(X86PReg::new(RDI), 16);
    expect_mismatch(&source, &machine, "CallArg/argument-width", |m| {
        matches!(m, X86BodyMismatch::CallMetadata { .. })
    });
    let (source, mut machine) = slice8_pair(AggShape::CallResultThenCall);
    let call = find(&machine, X86Opcode::Call)[0];
    inst_mut(&mut machine, call)
        .call_result_regs
        .as_mut()
        .unwrap()
        .truncate(1);
    expect_mismatch(
        &source,
        &machine,
        "CallResultThenCall/one-result-register",
        |m| matches!(m, X86BodyMismatch::CallMetadata { .. }),
    );
}

/// An aggregate the source passes by value must reach the callee as bytes:
/// its slot's address in the argument register is a named mismatch.
#[test]
fn an_aggregate_passed_as_its_address_is_a_named_mismatch() {
    let (source, mut machine) = slice8_pair(AggShape::CallArg);
    let load = row_where(&machine, |i| {
        writes(i, X86Opcode::MovRM32, GPR32_ALIAS_BASE + RDI)
    });
    let O::MemAddr { base, .. } = inst(&machine, load).operands[1].clone() else {
        panic!("a memory operand")
    };
    *inst_mut(&mut machine, load) = X86ISelInst::new(X86Opcode::MovRR, vec![preg(RDI), *base]);
    expect_mismatch(&source, &machine, "CallArg/address", |m| {
        matches!(m, X86BodyMismatch::CallStackAddress { .. })
    });
}

/// The machine's slot table must hold each aggregate copy at the
/// aggregate's size and alignment (the frame is laid out from it): a missing
/// or smaller copy makes no claim.
#[test]
fn a_slot_table_without_the_aggregate_copies_makes_no_claim() {
    for shape in [AggShape::ParamField, AggShape::CallResult] {
        let (source, machine) = slice8_pair(shape);
        let mut missing = machine.clone();
        missing.stack_slots.pop();
        let mut smaller = machine.clone();
        smaller.stack_slots.last_mut().unwrap().size -= 1;
        for (what, machine) in [("missing", missing), ("smaller", smaller)] {
            assert!(
                matches!(
                    source_bound_x86_body(&source, &machine, SYSV),
                    Err(X86BodyRefusal::Unsupported(
                        X86BodyUnsupported::MachineFunction(_)
                    ))
                ),
                "{shape:?}/{what}"
            );
        }
    }
}

/// The tied two-operand form is `d = d op x`: dropping the destination's old
/// value is refuted (above), and reading an undefined destination is named.
/// Only the forms the eightbyte moves emit are untied here. The optimizer's
/// `xor r, r` zeroing idiom reads no value of `r`, so THIS rule must not
/// claim it -- it would name an undefined read of `r`. It is admitted
/// instead as the constant row it computes (`zeroing_idiom`, 2026-10-14),
/// and only when both operands are the same register at the same width.
#[test]
fn tied_two_operand_rows_are_their_three_operand_form() {
    let (source, mut machine) = slice8_pair(AggShape::ResultPartial);
    let or = row_where(&machine, |i| {
        i.opcode == X86Opcode::OrRR && i.operands.len() == 2
    });
    let fresh = O::VReg(VReg::new(9_100, RegClass::Gpr64));
    inst_mut(&mut machine, or).operands[0] = fresh;
    never_credited(&source, &machine, "ResultPartial/or-into-undefined");
    let (source, mut machine) = slice8_pair(AggShape::ParamWord);
    let add = row_where(&machine, |i| i.opcode == X86Opcode::AddRR);
    let destination = inst(&machine, add).operands[0].clone();
    insert_at(
        &mut machine,
        add,
        X86ISelInst::new(X86Opcode::XorRR, vec![destination.clone(), destination]),
    );
    // The idiom is now MODELLED as the constant row it computes, so this
    // semantics-preserving insertion is credited. That is not a weakness this
    // admission introduced: `a_dead_in_domain_row_is_credited_too` shows the
    // lane credits a dead row of an opcode that was ALWAYS in the domain. This
    // lane states REFINEMENT, not accounting for every row, so the former
    // refusal here was an accident of the idiom being out of domain.
    assert!(
        source_bound_x86_body(&source, &machine, SYSV).is_ok(),
        "the zeroing idiom is its constant row: {}",
        describe(&machine)
    );
    // The untie rule itself still does not claim it: that rule states a
    // two-operand row as `d = d op s`, which would name an undefined read of
    // `d`. Only [`zeroing_idiom`] admits it, and only at ONE register.
    let (source, mut machine) = slice8_pair(AggShape::ParamWord);
    let add = row_where(&machine, |i| i.opcode == X86Opcode::AddRR);
    let other = O::VReg(VReg::new(9_300, RegClass::Gpr64));
    let destination = inst(&machine, add).operands[0].clone();
    insert_at(
        &mut machine,
        add,
        X86ISelInst::new(X86Opcode::XorRR, vec![destination, other]),
    );
    assert!(
        matches!(
            source_bound_x86_body(&source, &machine, SYSV),
            Err(X86BodyRefusal::Unsupported(
                X86BodyUnsupported::MachineRow { .. }
            ))
        ),
        "a two-operand xor of DIFFERENT registers is not the idiom: {}",
        describe(&machine)
    );
}

/// The lane credits a machine carrying a dead row whose opcode was always in
/// the domain, so refusing an extra row is not a guarantee it offers.
///
/// This is the control that settles what admitting the `xor d, d` zeroing
/// idiom costs: nothing. Measured 2026-10-14, with `MovRI` — in the domain
/// since slice 1 — inserted dead into a correct machine.
#[test]
fn a_dead_in_domain_row_is_credited_too() {
    let (source, mut machine) = slice8_pair(AggShape::ParamWord);
    let add = row_where(&machine, |i| i.opcode == X86Opcode::AddRR);
    let fresh = O::VReg(VReg::new(9_200, RegClass::Gpr64));
    insert_at(
        &mut machine,
        add,
        X86ISelInst::new(X86Opcode::MovRI, vec![fresh, O::Imm(0)]),
    );
    assert!(
        source_bound_x86_body(&source, &machine, SYSV).is_ok(),
        "a dead in-domain row is credited: {}",
        describe(&machine)
    );
}

/// Once a slot's address escaped, an aggregate call result's bytes may be
/// an address derived from it (slice 7's retention rule, applied to the
/// bytes slice 8 adds): an incoming access through one observes the escaped
/// slots' contents (slice 15; slice 8 held it outside the domain).
#[test]
fn an_access_through_a_call_result_after_an_escape_observes_the_slot() {
    let build = |escape: bool| {
        let mut builder = ModuleBuilder::new("x86_source_bound_body_slice8_taint");
        let u64x1 = {
            let id = builder.add_type(Ty::U64);
            Ty::Array(id, 1)
        };
        let bump = {
            let ty = builder.add_func_type(vec![Ty::PtrMut(Box::new(Ty::U64))], vec![]);
            builder.declare_function("bump", ty)
        };
        let give = {
            let ty = builder.add_func_type(vec![Ty::U64], vec![u64x1.clone()]);
            builder.declare_function("give1w", ty)
        };
        let signature = builder.add_func_type(vec![Ty::U64, Ty::U64], vec![Ty::U64]);
        let mut f = builder.function("s8_taint", signature);
        let entry = f.create_block();
        let x = f.add_block_param(entry, Ty::U64);
        let y = f.add_block_param(entry, Ty::U64);
        f.switch_to_block(entry);
        if escape {
            let v = f.alloca(Ty::U64);
            f.store(Ty::U64, v, x);
            f.call_void(bump, vec![v]);
        }
        let r = f.call(give, vec![y]);
        let word = f.extract_field(Ty::U64, r, 0);
        let pointer = f.cast(trust_ir::CastOp::IntToPtr, Ty::U64, Ty::Ptr, word);
        let loaded = f.load(Ty::U64, pointer);
        f.ret(vec![loaded]);
        f.build();
        trust_cg_lower::translate_module_for_arch_with_tls_with_license(
            &builder.build().expect("ModuleBuilder::build: test fixture"),
            trust_cg_lower::GuardCarrierArch::X86_64,
            trust_cg_lower::TlsDialect::default(),
            &crate::license_test_support::permit_unlicensed(),
        )
        .expect("translates")
        .into_iter()
        .map(|(function, _)| function)
        .find(|function| function.name == "s8_taint")
        .unwrap()
    };
    // Without an escape the result's bytes are an ordinary incoming address.
    let source = build(false);
    let machine = select(&source, X86CallAbi::SystemV);
    let obligation = owner(&source, &machine, "no escape");
    assert!(theorem_holds(&obligation));
    // After one they may point into the escaped slot, whose contents the
    // load observes.
    let source = build(true);
    let body = admitted_body(&source).expect("admitted");
    assert!(
        body.paths[0]
            .accesses
            .iter()
            .any(|access| access.slot_reads.is_some())
    );
    let machine = select(&source, X86CallAbi::SystemV);
    let obligation = owner(&source, &machine, "after an escape");
    assert!(theorem_holds(&obligation));
}

/// The real x86 optimizer's output at O1, O2 and O3 for every slice-8
/// fixture: the owner never names a mismatch for a correct lowering, and
/// every theorem it builds holds.
#[test]
fn optimized_slice_eight_fixtures_are_judged_without_false_mismatches() {
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
        for shape in all_slice_eight_shapes() {
            let (source, mut machine) = slice8_pair(shape);
            pipeline.run_x86_optimization_passes(&mut machine);
            match source_bound_x86_body(&source, &machine, SYSV) {
                Ok(owner) => {
                    built += 1;
                    assert!(
                        theorem_holds(owner.obligation()),
                        "{shape:?} at {opt_level:?}\n{}",
                        describe(&machine)
                    );
                    eprintln!("{opt_level:?} {shape:?}: theorem holds on samples");
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

const SLICE_EIGHT_SNAPSHOT_SHA256: &str =
    "a656a3eb88e6e5c28b10efadd5f735e8f5b9cf8d7e984c502223321b25d1b5a8";

#[test]
fn slice_eight_smt2_is_canonical_per_shape() {
    use sha2::{Digest, Sha256};
    const GOLDEN: &str =
        include_str!("../tests/fixtures/x86_source_bound_body/slice8_snapshots.smt2");
    let mut rendered = String::new();
    for shape in SLICE_EIGHT {
        let (source, machine) = slice8_pair(shape);
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
            .join("tests/fixtures/x86_source_bound_body/slice8_snapshots.smt2");
        std::fs::write(&path, &rendered).unwrap();
        panic!(
            "rewrote {}; review its diff, set SLICE_EIGHT_SNAPSHOT_SHA256 to {:x} and re-run \
             without TCG_X86_BODY_SNAPSHOT_WRITE",
            path.display(),
            Sha256::digest(rendered.as_bytes())
        );
    }
    assert_eq!(
        format!("{:x}", Sha256::digest(GOLDEN.as_bytes())),
        SLICE_EIGHT_SNAPSHOT_SHA256,
        "the golden file changed without the reviewed digest pin"
    );
    assert_eq!(rendered, GOLDEN, "slice-8 snapshots drifted");
}

/// Slices 1 to 7 are unchanged by slice 8: no earlier fixture's body has an
/// aggregate slot copy, an aggregate lane or a by-value argument.
#[test]
fn bodies_without_an_aggregate_bind_no_aggregate_lane() {
    let check = |source: &Function, what: &str| {
        let Ok(body) = admitted_body(source) else {
            return;
        };
        assert_eq!(body.machine_slots, source.stack_slots, "{what}");
        for path in &body.paths {
            assert!(
                path.return_tys
                    .iter()
                    .all(|lane| matches!(lane, ReturnLane::Scalar(_))),
                "{what}"
            );
            assert!(
                path.calls.iter().all(|call| call
                    .args
                    .iter()
                    .all(|arg| !matches!(arg, CallArg::Aggregate(_)))),
                "{what}"
            );
        }
    };
    for shape in all_shapes() {
        check(&pair(shape).0, &format!("{shape:?}"));
    }
    for shape in super::memory::MEMORY_SHAPES {
        check(&super::memory::memory_pair(shape).0, &format!("{shape:?}"));
    }
    for shape in super::slice7::all_slice_seven_shapes() {
        check(&super::slice7::slice7_pair(shape).0, &format!("{shape:?}"));
    }
}
