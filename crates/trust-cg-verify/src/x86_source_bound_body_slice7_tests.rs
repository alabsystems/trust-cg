// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Slice 7 of the x86-64 source-bound body theorem: calls through memory. A
//! direct call receives a private stack slot's address, as the hidden return
//! buffer of a callee whose argument 0 is one (`sret`), or as an ordinary
//! out-parameter (`&mut local`, `&local`); the slot escapes, the call reads
//! its bytes and leaves call-defined ones, and the caller reads them back.
//!
//! Fixtures are real: LIR from the trust-ir adapter (the callee declared
//! with the `sret` parameter attribute the bridge's `PassMode::Indirect`
//! return carries, which the adapter turns into `Function::sret_arg_callees`)
//! and the machine stream from the real x86-64 instruction selector
//! (`super::select`). Negative controls mutate that stream and must end as a
//! typed mismatch, a refuted theorem or an unsupported (uncredited) body,
//! never as Formal credit.
//!
//! Every test here runs without a solver, and the soundness check runs them
//! all (the `x86_source_bound_body::tests::slice7::` library gate). The
//! replay on AY and Clean and the verifier-credit tests are in
//! `slice7_qualification`.

use super::slice5::describe;
use super::slice6::{describe_lir, path_claims, paths_refuted_on_samples};
use super::*;
use trust_ir::{ICmpOp, ParamAttrs};

/// Slice-7 fixture shapes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum CallMemShape {
    // ---- (a) return buffers (sret callees)
    /// `let t = make3(x); t.a + t.b + t.c`: a callee returning a 3-word
    /// struct through the buffer, every field read back.
    SretSum3,
    /// `make3(x).b`: one field of the buffer.
    SretField,
    /// `let r = mixed(x); r.b as u64 + r.flag as u64`: a `u32` field and a
    /// `bool` field (`{ a: u64, b: u32, flag: bool }`) read back at their
    /// widths from call-defined bytes.
    SretNarrow,
    /// `make3(x).a + make3(y).c`: two buffers, the first read after the
    /// second call (which may write it through a retained address).
    SretTwoBuffers,
    /// `fn(x) -> Three { make3(x) }`: an sret function forwarding its own
    /// incoming buffer (no private slot) to an sret callee.
    SretForward,
    /// `if c { make3(x).c } else { x }`: control flow plus an sret call.
    SretBranch,
    /// `match pair(x) { Some((a, b)) => a ^ b, None => 9 }`: an
    /// `Option<(u64, u64)>` returned through the buffer, its tag branched
    /// on.
    SretOption,
    // ---- (b) out-parameters
    /// `let mut v = x; bump(&mut v); v`.
    OutParam,
    /// `let mut v = x; bump(&mut v); bump(&mut v); v`: two calls sharing
    /// one slot.
    OutParamTwice,
    /// `let v = x; peek(&v)`: a call that reads the slot it is given.
    ReadRef,
    /// `let mut s = (x, y); bump(&mut s.1); s.0 + s.1`: an address into the
    /// middle of the slot; the whole slot escapes.
    OutParamField,
    /// `let mut v = x; bump(&mut v); g1(y) + v`: the slot stays escaped
    /// across a later call that is not given it.
    OutParamThenCall,
    /// `fn(x) { let mut v = x; bump(&mut v) }`: the only observable is the
    /// slot's contents at the call.
    OutParamVoid,
    /// `fn(p, x) { let mut v = x; bump(&mut v); *p = v }`: an incoming store
    /// after the escape, through a parameter's address.
    OutParamThenStore,
    /// `let mut o: Option<u64> = None; fill(&mut o); match o { Some(v) =>
    /// v, None => 0 }`: an `Option<u64>` out-parameter, its tag branched on.
    OptionOutParam,
}

/// Every slice-7 shape whose real selection the owner admits and whose
/// theorem holds ([`every_admitted_slice_seven_fixture_is_qualified`] checks
/// that none is left out).
pub(crate) const SLICE_SEVEN: [CallMemShape; 15] = [
    CallMemShape::SretSum3,
    CallMemShape::SretField,
    CallMemShape::SretNarrow,
    CallMemShape::SretTwoBuffers,
    CallMemShape::SretForward,
    CallMemShape::SretBranch,
    CallMemShape::SretOption,
    CallMemShape::OutParam,
    CallMemShape::OutParamTwice,
    CallMemShape::ReadRef,
    CallMemShape::OutParamField,
    CallMemShape::OutParamThenCall,
    CallMemShape::OutParamVoid,
    CallMemShape::OutParamThenStore,
    CallMemShape::OptionOutParam,
];

impl CallMemShape {
    fn name(self) -> String {
        let name = format!("{self:?}");
        let mut snake = String::from("s7_");
        for (i, c) in name.chars().enumerate() {
            if c.is_ascii_uppercase() && i > 0 {
                snake.push('_');
            }
            snake.push(c.to_ascii_lowercase());
        }
        snake
    }
}

/// Declare `name` with the `sret` attribute on its leading pointer
/// parameter, as the bridge declares a `PassMode::Indirect` return.
fn mark_sret(module: &mut trust_ir::Module, name: &str) {
    let function = module
        .functions
        .iter_mut()
        .find(|function| function.name == name)
        .unwrap_or_else(|| panic!("no declaration of {name}"));
    function.attrs.params = vec![
        ParamAttrs {
            sret: true,
            ..ParamAttrs::default()
        },
        ParamAttrs::default(),
    ];
}

/// The LIR the trust-ir adapter produces for a slice-7 shape.
pub(crate) fn slice7_lir(shape: CallMemShape) -> Function {
    use CallMemShape::*;
    let mut builder = ModuleBuilder::new("x86_source_bound_body_slice7");
    // Each struct its own id: the module resolves a struct type by id.
    let struct_of = |builder: &mut ModuleBuilder, id: u32, name: &str, fields: Vec<Ty>| {
        Ty::Struct(
            builder.add_struct(StructDef {
                origin: None,
                id: StructId::new(id),
                name: name.into(),
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
    let three = struct_of(&mut builder, 0, "Three", vec![Ty::U64; 3]);
    let mixed = struct_of(&mut builder, 1, "Mixed", vec![Ty::U64, Ty::U32, Ty::Bool]);
    let pair = struct_of(&mut builder, 2, "Pair", vec![Ty::U64; 2]);
    let ptr = Ty::Ptr;
    let mut declare = |name: &str, params: Vec<Ty>, results: Vec<Ty>| {
        let ty = builder.add_func_type(params, results);
        builder.declare_function(name, ty)
    };
    // `make3`, `mixed_of` and `pair_of` return through a buffer (argument 0).
    let make3 = declare("make3", vec![ptr.clone(), Ty::U64], vec![]);
    let mixed_of = declare("mixed_of", vec![ptr.clone(), Ty::U64], vec![]);
    let pair_of = declare("pair_of", vec![ptr.clone(), Ty::U64], vec![]);
    let bump = declare("bump", vec![Ty::PtrMut(Box::new(Ty::U64))], vec![]);
    let peek = declare("peek", vec![Ty::PtrConst(Box::new(Ty::U64))], vec![Ty::U64]);
    let fill = declare("fill", vec![Ty::PtrMut(Box::new(Ty::U64))], vec![]);
    let g1 = declare("g1", vec![Ty::U64], vec![Ty::U64]);
    let (params, results): (Vec<Ty>, Vec<Ty>) = match shape {
        SretSum3 | SretField | SretNarrow | SretOption | OutParam | OutParamTwice | ReadRef
        | OptionOutParam => (vec![Ty::U64], vec![Ty::U64]),
        SretTwoBuffers | OutParamField | OutParamThenCall => {
            (vec![Ty::U64, Ty::U64], vec![Ty::U64])
        }
        SretForward => (vec![ptr.clone(), Ty::U64], vec![]),
        SretBranch => (vec![Ty::Bool, Ty::U64], vec![Ty::U64]),
        OutParamVoid => (vec![Ty::U64], vec![]),
        OutParamThenStore => (vec![Ty::PtrMut(Box::new(Ty::U64)), Ty::U64], vec![]),
    };
    let signature = builder.add_func_type(params.clone(), results);
    let mut f = builder.function(shape.name(), signature);
    let entry = f.create_block();
    let args: Vec<_> = params
        .iter()
        .map(|ty| f.add_block_param(entry, ty.clone()))
        .collect();
    f.switch_to_block(entry);
    match shape {
        SretSum3 => {
            let t = f.alloca(three.clone());
            f.call_void(make3, vec![t, args[0]]);
            let a = f.load(Ty::U64, t);
            let pb = f.gep_byte_offset(t, 8);
            let b = f.load(Ty::U64, pb);
            let pc = f.gep_byte_offset(t, 16);
            let c = f.load(Ty::U64, pc);
            let ab = f.add(Ty::U64, a, b);
            let sum = f.add(Ty::U64, ab, c);
            f.ret(vec![sum]);
        }
        SretField => {
            let t = f.alloca(three.clone());
            f.call_void(make3, vec![t, args[0]]);
            let pb = f.gep_byte_offset(t, 8);
            let b = f.load(Ty::U64, pb);
            f.ret(vec![b]);
        }
        SretNarrow => {
            let r = f.alloca(mixed.clone());
            f.call_void(mixed_of, vec![r, args[0]]);
            let pb = f.gep_byte_offset(r, 8);
            let b = f.load(Ty::U32, pb);
            let pflag = f.gep_byte_offset(r, 12);
            let flag = f.load(Ty::Bool, pflag);
            let wide_b = f.zext(Ty::U32, Ty::U64, b);
            let wide_flag = f.zext(Ty::Bool, Ty::U64, flag);
            let sum = f.add(Ty::U64, wide_b, wide_flag);
            f.ret(vec![sum]);
        }
        SretTwoBuffers => {
            let first = f.alloca(three.clone());
            f.call_void(make3, vec![first, args[0]]);
            let second = f.alloca(three.clone());
            f.call_void(make3, vec![second, args[1]]);
            let a = f.load(Ty::U64, first);
            let pc = f.gep_byte_offset(second, 16);
            let c = f.load(Ty::U64, pc);
            let sum = f.add(Ty::U64, a, c);
            f.ret(vec![sum]);
        }
        SretForward => {
            f.call_void(make3, vec![args[0], args[1]]);
            f.ret(vec![]);
        }
        SretBranch => {
            let (then, other, join) = (f.create_block(), f.create_block(), f.create_block());
            let result = f.add_block_param(join, Ty::U64);
            f.condbr(args[0], then, vec![], other, vec![]);
            f.switch_to_block(then);
            let t = f.alloca(three.clone());
            f.call_void(make3, vec![t, args[1]]);
            let pc = f.gep_byte_offset(t, 16);
            let c = f.load(Ty::U64, pc);
            f.br(join, vec![c]);
            f.switch_to_block(other);
            f.br(join, vec![args[1]]);
            f.switch_to_block(join);
            f.ret(vec![result]);
        }
        SretOption => {
            // `Option<(u64, u64)>`: the tag word, then the payload.
            let o = f.alloca(three.clone());
            f.call_void(pair_of, vec![o, args[0]]);
            let tag = f.load(Ty::U64, o);
            let zero = f.iconst(Ty::U64, 0);
            let is_some = f.icmp(ICmpOp::Ne, Ty::U64, tag, zero);
            let (some, none, join) = (f.create_block(), f.create_block(), f.create_block());
            let result = f.add_block_param(join, Ty::U64);
            f.condbr(is_some, some, vec![], none, vec![]);
            f.switch_to_block(some);
            let pa = f.gep_byte_offset(o, 8);
            let a = f.load(Ty::U64, pa);
            let pb = f.gep_byte_offset(o, 16);
            let b = f.load(Ty::U64, pb);
            let x = f.binop(BinOp::Xor, Ty::U64, a, b);
            f.br(join, vec![x]);
            f.switch_to_block(none);
            let nine = f.iconst(Ty::U64, 9);
            f.br(join, vec![nine]);
            f.switch_to_block(join);
            f.ret(vec![result]);
        }
        OutParam | OutParamTwice => {
            let v = f.alloca(Ty::U64);
            f.store(Ty::U64, v, args[0]);
            f.call_void(bump, vec![v]);
            if shape == OutParamTwice {
                f.call_void(bump, vec![v]);
            }
            let back = f.load(Ty::U64, v);
            f.ret(vec![back]);
        }
        ReadRef => {
            let v = f.alloca(Ty::U64);
            f.store(Ty::U64, v, args[0]);
            let seen = f.call(peek, vec![v]);
            f.ret(vec![seen]);
        }
        OutParamField => {
            let s = f.alloca(pair.clone());
            f.store(Ty::U64, s, args[0]);
            let second = f.gep_byte_offset(s, 8);
            f.store(Ty::U64, second, args[1]);
            f.call_void(bump, vec![second]);
            let a = f.load(Ty::U64, s);
            let b = f.load(Ty::U64, second);
            let sum = f.add(Ty::U64, a, b);
            f.ret(vec![sum]);
        }
        OutParamThenCall => {
            let v = f.alloca(Ty::U64);
            f.store(Ty::U64, v, args[0]);
            f.call_void(bump, vec![v]);
            let y = f.call(g1, vec![args[1]]);
            let back = f.load(Ty::U64, v);
            let sum = f.add(Ty::U64, y, back);
            f.ret(vec![sum]);
        }
        OutParamVoid => {
            let v = f.alloca(Ty::U64);
            f.store(Ty::U64, v, args[0]);
            f.call_void(bump, vec![v]);
            f.ret(vec![]);
        }
        OutParamThenStore => {
            let v = f.alloca(Ty::U64);
            f.store(Ty::U64, v, args[1]);
            f.call_void(bump, vec![v]);
            let back = f.load(Ty::U64, v);
            f.store(Ty::U64, args[0], back);
            f.ret(vec![]);
        }
        OptionOutParam => {
            // `Option<u64>`: the tag word (0 is `None`), then the payload.
            let o = f.alloca(pair.clone());
            let none = f.iconst(Ty::U64, 0);
            f.store(Ty::U64, o, none);
            f.call_void(fill, vec![o]);
            let tag = f.load(Ty::U64, o);
            let zero = f.iconst(Ty::U64, 0);
            let is_some = f.icmp(ICmpOp::Ne, Ty::U64, tag, zero);
            let (some, other, join) = (f.create_block(), f.create_block(), f.create_block());
            let result = f.add_block_param(join, Ty::U64);
            f.condbr(is_some, some, vec![], other, vec![]);
            f.switch_to_block(some);
            let payload = f.gep_byte_offset(o, 8);
            let value = f.load(Ty::U64, payload);
            f.br(join, vec![value]);
            f.switch_to_block(other);
            let fallback = f.iconst(Ty::U64, 0);
            f.br(join, vec![fallback]);
            f.switch_to_block(join);
            f.ret(vec![result]);
        }
    }
    f.build();
    let mut module = builder.build().expect("ModuleBuilder::build: test fixture");
    for name in ["make3", "mixed_of", "pair_of"] {
        mark_sret(&mut module, name);
    }
    translated_function(&module, &shape.name())
}

/// The LIR of the function `name` in the translated `module`.
fn translated_function(module: &trust_ir::Module, name: &str) -> Function {
    trust_cg_lower::translate_module_for_arch_with_tls_with_license(
        module,
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

pub(crate) fn slice7_pair(shape: CallMemShape) -> (Function, X86ISelFunction) {
    let source = slice7_lir(shape);
    let machine = select(&source, X86CallAbi::SystemV);
    (source, machine)
}

/// Every fixture shape, in declaration order.
pub(crate) fn all_slice_seven_shapes() -> Vec<CallMemShape> {
    use CallMemShape::*;
    let all = SLICE_SEVEN.to_vec();
    // Exhaustive: a new shape does not compile until it is listed here.
    for shape in &all {
        match shape {
            SretSum3 | SretField | SretNarrow | SretTwoBuffers | SretForward | SretBranch
            | SretOption | OutParam | OutParamTwice | ReadRef | OutParamField
            | OutParamThenCall | OutParamVoid | OutParamThenStore | OptionOutParam => {}
        }
    }
    all
}

/// Whether `obligation` is a several-path theorem.
fn path_form(obligation: &ProofObligation) -> bool {
    obligation.trust_ir_expr == E::bool_const(true)
        && matches!(
            &obligation.aarch64_expr,
            E::And { lhs, .. } if matches!(lhs.as_ref(), E::Or { .. })
        )
}

/// Evaluate the theorem at one sampled assignment of its free inputs (the
/// premises are definitional): whether its observable holds and, for a
/// several-path theorem, which source paths' conditions hold. Every sixth
/// sample sets every call-defined byte to 0, so a tag the callee writes
/// (an `Option`'s) takes its `None` value too, which independent random
/// bytes almost never spell; the samples between zero the call-defined
/// bytes on one side of a boundary (see [`zeroed_call_byte`]), so a zero tag
/// beside a nonzero payload, or a zero low half under a nonzero high half,
/// occurs as well. Test-only semantics check; never credit.
fn evaluate_sample(obligation: &ProofObligation, seed: u64) -> (bool, Option<Vec<bool>>) {
    use crate::smt::{EvalEnv, EvalResult};
    let mut env = EvalEnv::default();
    let mut state = seed.wrapping_add(0x9e37_79b9_7f4a_7c15);
    for (name, width) in free_inputs_of(obligation) {
        state = state
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        let high = state >> 29;
        // Slice 15: a byte a store through a derived address left is sampled
        // like a call-defined one.
        let call_byte = parse_call_byte_name(&name)
            .or_else(|| parse_access_byte_name(&name))
            .map(|(_, _, offset)| offset);
        let value = if (call_byte.is_some() && seed.is_multiple_of(6))
            || call_byte.is_some_and(|offset| zeroed_call_byte(seed, offset))
        {
            0
        } else {
            match seed % 4 {
                0 => high & 0xff,
                1 => high % 12,
                2 => high & 0x1_ffff_ffff,
                _ => state ^ (state >> 31),
            }
        };
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

/// Whether sample `seed` zeroes the call-defined byte at `offset` of its
/// slot. At seeds `6k + 3` the boundary `k mod 33` steps through every offset
/// of a 32-byte slot, zeroing the bytes below it for even `k / 33` and the
/// bytes at or above it for odd: each word of a buffer is zero while its
/// neighbour is not, and each half of a word is zero while the other is not.
fn zeroed_call_byte(seed: u64, offset: i64) -> bool {
    if seed % 6 != 3 {
        return false;
    }
    let k = seed / 6;
    let boundary = (k % 33) as i64;
    if (k / 33).is_multiple_of(2) {
        offset < boundary
    } else {
        offset >= boundary
    }
}

const SAMPLES: u64 = 768;

/// Whether the theorem holds at every sample, and (several paths) exactly
/// one source path's condition holds at each and every path is exercised.
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
    // The earlier slices' samplers must find no refutation either (the
    // several-path one may not exercise a path whose branch reads only
    // call-defined bytes, which this sampler does).
    exercised.is_none_or(|seen| seen.into_iter().all(|seen| seen))
        && if path_form(obligation) {
            !paths_refuted_on_samples(obligation)
        } else {
            holds_on_samples(obligation)
        }
}

/// Whether some sample refutes the theorem.
pub(crate) fn theorem_refuted(obligation: &ProofObligation) -> bool {
    (0..SAMPLES).any(|seed| !evaluate_sample(obligation, seed).0)
        || if path_form(obligation) {
            paths_refuted_on_samples(obligation)
        } else {
            refuted_on_samples(obligation)
        }
}

/// Every call-defined byte (`d{site}s{slot}o{offset}`) the theorem declares.
fn call_bytes_of(obligation: &ProofObligation) -> Vec<String> {
    obligation
        .inputs
        .iter()
        .filter(|(name, _)| parse_call_byte_name(name).is_some())
        .map(|(name, _)| name.clone())
        .collect()
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

/// A wrong lowering the owner still binds: its theorem must be refuted on
/// samples (the replay refutes it on the qualification host).
#[track_caller]
fn refuted(source: &Function, machine: &X86ISelFunction, what: &str) {
    let obligation = owner(source, machine, what);
    assert!(
        theorem_refuted(&obligation),
        "{what}: the theorem must refute the wrong lowering\n{}",
        describe(machine)
    );
}

// ---------------------------------------------------------------------------
// Construction (no solver)
// ---------------------------------------------------------------------------

/// The selector passes the slot's address exactly as an argument: `lea` of
/// the slot, copied into the argument register, and the call row declares
/// that register at 64 bits (RDI for argument 0, a return buffer included).
#[test]
fn slice_seven_fixtures_have_the_expected_pre_ra_shapes() {
    for shape in SLICE_SEVEN {
        let (source, machine) = slice7_pair(shape);
        let text = format!("{shape:?}\n{}{}", describe_lir(&source), describe(&machine));
        assert_eq!(source.stack_slots, machine.stack_slots, "{text}");
        let sret = matches!(
            shape,
            CallMemShape::SretSum3
                | CallMemShape::SretField
                | CallMemShape::SretNarrow
                | CallMemShape::SretTwoBuffers
                | CallMemShape::SretForward
                | CallMemShape::SretBranch
                | CallMemShape::SretOption
        );
        assert_eq!(!source.sret_arg_callees.is_empty(), sret, "{text}");
        let calls = find(&machine, X86Opcode::Call);
        assert!(!calls.is_empty(), "{text}");
        for call in calls {
            let call_row = inst(&machine, call);
            let first = call_row.call_arg_regs.first().expect("an argument");
            assert_eq!(first.reg.encoding(), RDI, "{text}");
            assert_eq!(first.read_bits, 64, "{text}");
        }
        if shape != CallMemShape::SretForward {
            assert!(
                rows(&machine).iter().any(|(ordinal, _, _)| {
                    let row = inst(&machine, *ordinal);
                    row.opcode == X86Opcode::Lea
                        && matches!(&row.operands[1], O::MemAddr { base, .. }
                            if matches!(base.as_ref(), O::StackSlot(_)))
                }),
                "{text}"
            );
        }
    }
}

#[test]
fn owner_builds_for_every_slice_seven_shape_and_covers_every_value_row() {
    for shape in SLICE_SEVEN {
        let (source, machine) = slice7_pair(shape);
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
        assert_eq!(
            body.call_sites().len(),
            find(&machine, X86Opcode::Call).len(),
            "{shape:?}"
        );
    }
}

#[test]
fn slice_seven_theorems_hold_on_samples() {
    for shape in SLICE_SEVEN {
        let (source, machine) = slice7_pair(shape);
        let obligation = owner(&source, &machine, &format!("{shape:?}"));
        assert!(
            theorem_holds(&obligation),
            "{shape:?}\n{}",
            describe(&machine)
        );
    }
}

/// The golden, owner, credit and host-qualification tests run over
/// [`SLICE_SEVEN`]: every fixture whose real selection the owner admits with a
/// theorem that holds must be in it.
#[test]
fn every_admitted_slice_seven_fixture_is_qualified() {
    for shape in all_slice_seven_shapes() {
        let (source, machine) = slice7_pair(shape);
        let holds = source_bound_x86_body(&source, &machine, SYSV)
            .is_ok_and(|owner| theorem_holds(owner.obligation()));
        assert_eq!(SLICE_SEVEN.contains(&shape), holds, "{shape:?}");
    }
}

/// What slice 7 adds to every fixture: a call to a return-buffer callee, or
/// a call given a private slot's address (each was outside slices 1 to 6:
/// the frame condition "an sret-arg callee", or a slot address escaping as
/// a call argument). The forwarding sret function passes its own incoming
/// buffer, which is no private slot.
#[test]
fn every_slice_seven_fixture_calls_through_memory() {
    for shape in SLICE_SEVEN {
        let source = slice7_lir(shape);
        let body = admitted_body(&source).unwrap();
        let passes_slot = body.paths.iter().flat_map(|path| &path.calls).any(|call| {
            call.args
                .iter()
                .any(|arg| matches!(arg, CallArg::Frame(..)))
        });
        let sret = !source.sret_arg_callees.is_empty();
        assert!(passes_slot || sret, "{shape:?}");
        assert_eq!(passes_slot, shape != CallMemShape::SretForward, "{shape:?}");
    }
}

/// The model's parts on real fixtures: the slot's contents at the call are
/// observed when they differ in spelling (the stored argument against the
/// machine's stored register), the bytes read back after the call are the
/// call-defined inputs on both sides, and a private address argument is no
/// SMT term (only the scalar arguments are observed).
#[test]
fn the_escaped_slot_is_observed_at_the_call_and_redefined_after_it() {
    // `bump(&mut v)`: v's contents (x) at the call, then the call's bytes.
    let (source, machine) = slice7_pair(CallMemShape::OutParam);
    let obligation = owner(&source, &machine, "OutParam");
    assert_eq!(
        call_bytes_of(&obligation),
        (0..8).map(|y| format!("d0s0o{y}")).collect::<Vec<_>>()
    );
    // Two items: the returned value and the slot's 8 bytes at the call.
    assert_eq!(observable_items(&obligation).len(), 2, "{obligation:?}");
    // The return buffer is uninitialized at the call: its chunks are the
    // same initial bytes on both sides and state nothing, so the call's
    // observable is its scalar argument alone.
    let (source, machine) = slice7_pair(CallMemShape::SretSum3);
    let obligation = owner(&source, &machine, "SretSum3");
    assert_eq!(call_bytes_of(&obligation).len(), 24);
    assert!(
        !obligation
            .inputs
            .iter()
            .any(|(name, _)| name.starts_with('f')),
        "no initial byte is read: {:?}",
        obligation.inputs
    );
    assert_eq!(observable_items(&obligation).len(), 2);
    // The second call reads the bytes the first left (one site's inputs on
    // both sides: not stated) and redefines the slot again.
    let (source, machine) = slice7_pair(CallMemShape::OutParamTwice);
    let obligation = owner(&source, &machine, "OutParamTwice");
    let bytes = call_bytes_of(&obligation);
    assert!(
        bytes.iter().all(|name| name.starts_with("d1s0")),
        "{bytes:?}"
    );
    // A later call without the slot as an argument redefines it too.
    let (source, machine) = slice7_pair(CallMemShape::OutParamThenCall);
    let obligation = owner(&source, &machine, "OutParamThenCall");
    let bytes = call_bytes_of(&obligation);
    assert!(
        !bytes.is_empty() && bytes.iter().all(|name| name.starts_with("d1s0")),
        "{bytes:?}"
    );
    // A bool read of a call-defined byte is `byte != 0`; a u32 read is four
    // bytes.
    let (source, machine) = slice7_pair(CallMemShape::SretNarrow);
    let obligation = owner(&source, &machine, "SretNarrow");
    assert_eq!(
        call_bytes_of(&obligation),
        (8..13).map(|y| format!("d0s0o{y}")).collect::<Vec<_>>()
    );
}

// ---------------------------------------------------------------------------
// Negative controls (no solver)
// ---------------------------------------------------------------------------

/// The `lea` of a slot that feeds the `n`-th call's argument register, and
/// that call's row.
fn argument_lea(machine: &X86ISelFunction, n: usize) -> (usize, usize) {
    let call = find(machine, X86Opcode::Call)[n];
    let feed = (0..call)
        .rev()
        .find(|ordinal| {
            let row = inst(machine, *ordinal);
            row.opcode == X86Opcode::MovRR && row.operands[0] == preg(RDI)
        })
        .expect("the argument copy");
    let O::VReg(source) = inst(machine, feed).operands[1] else {
        panic!("argument copied from a virtual register")
    };
    let lea = (0..feed)
        .rev()
        .find(|ordinal| {
            let row = inst(machine, *ordinal);
            row.opcode == X86Opcode::Lea && row.operands[0] == O::VReg(source)
        })
        .expect("the slot's lea");
    (lea, call)
}

fn set_lea(machine: &mut X86ISelFunction, lea: usize, slot: u32, disp: i32) {
    inst_mut(machine, lea).operands[1] = O::MemAddr {
        base: Box::new(O::StackSlot(slot)),
        disp,
    };
}

/// A machine that passes another slot, or the paired slot at another
/// offset, is a named mismatch: the walk checks the private address exactly.
#[test]
fn a_wrong_slot_or_offset_argument_is_a_named_mismatch() {
    let wrong = |what: &str, source: &Function, machine: &X86ISelFunction| {
        expect_mismatch(source, machine, what, |mismatch| {
            matches!(
                mismatch,
                X86BodyMismatch::CallStackAddress { argument: 0, .. }
            )
        });
    };
    // The second buffer's address passed to the first call.
    let (source, mut machine) = slice7_pair(CallMemShape::SretTwoBuffers);
    let (lea, _) = argument_lea(&machine, 0);
    set_lea(&mut machine, lea, 1, 0);
    wrong("SretTwoBuffers: wrong slot", &source, &machine);
    // The paired slot, eight bytes in.
    let (source, mut machine) = slice7_pair(CallMemShape::SretSum3);
    let (lea, _) = argument_lea(&machine, 0);
    set_lea(&mut machine, lea, 0, 8);
    wrong("SretSum3: wrong offset", &source, &machine);
    // The field's address at the slot's start.
    let (source, mut machine) = slice7_pair(CallMemShape::OutParamField);
    let call = find(&machine, X86Opcode::Call)[0];
    let feed = (0..call)
        .rev()
        .find(|ordinal| inst(&machine, *ordinal).operands.first() == Some(&preg(RDI)))
        .unwrap();
    let base_lea = find(&machine, X86Opcode::Lea)[0];
    let base = inst(&machine, base_lea).operands[0].clone();
    inst_mut(&mut machine, feed).operands[1] = base;
    wrong("OutParamField: the slot's start", &source, &machine);
}

/// A private address where the source passes a value is a named mismatch;
/// a value the walk does not track as a private address, where the source
/// passes one, makes no claim.
#[test]
fn a_private_address_argument_must_be_paired_with_one() {
    // `g1(y)` given v's address.
    let (source, mut machine) = slice7_pair(CallMemShape::OutParamThenCall);
    let second = find(&machine, X86Opcode::Call)[1];
    let feed = (0..second)
        .rev()
        .find(|ordinal| inst(&machine, *ordinal).operands.first() == Some(&preg(RDI)))
        .unwrap();
    let (lea, _) = argument_lea(&machine, 0);
    let slot_register = inst(&machine, lea).operands[0].clone();
    inst_mut(&mut machine, feed).operands[1] = slot_register;
    expect_mismatch(&source, &machine, "a slot for a value", |mismatch| {
        matches!(
            mismatch,
            X86BodyMismatch::CallStackAddress { argument: 0, .. }
        )
    });
    // `bump` given the stored value instead of the slot's address.
    let (source, mut machine) = slice7_pair(CallMemShape::OutParam);
    let (_, call) = argument_lea(&machine, 0);
    let feed = (0..call)
        .rev()
        .find(|ordinal| inst(&machine, *ordinal).operands.first() == Some(&preg(RDI)))
        .unwrap();
    let parameter = inst(&machine, 0).operands[0].clone();
    inst_mut(&mut machine, feed).operands[1] = parameter;
    expect_unsupported(&source, &machine, "a value for a slot");
}

/// The first load row after the `n`-th call that reads a private slot.
fn load_after_call(machine: &X86ISelFunction, n: usize) -> usize {
    let call = find(machine, X86Opcode::Call)[n];
    (call + 1..rows(machine).len())
        .find(|ordinal| memory_access(inst(machine, *ordinal).opcode).is_some_and(|f| f.load))
        .expect("a load after the call")
}

/// Move the row at `from` to just before the row at `to` (`to < from`).
fn move_before(machine: &mut X86ISelFunction, from: usize, to: usize) {
    let row = remove_at(machine, from);
    insert_at(machine, to, row);
}

/// A caller read of the slot taken before the call, where the source reads
/// after it, is refuted: before the call the slot holds the stored value,
/// after it the call's bytes.
#[test]
fn reading_the_slot_before_the_call_is_refuted() {
    for shape in [
        CallMemShape::OutParam,
        CallMemShape::SretSum3,
        CallMemShape::OutParamThenStore,
    ] {
        let (source, mut machine) = slice7_pair(shape);
        let load = load_after_call(&machine, 0);
        let call = find(&machine, X86Opcode::Call)[0];
        // The load's base register is defined before the argument copy.
        let feed = (0..call)
            .rev()
            .find(|ordinal| inst(&machine, *ordinal).operands.first() == Some(&preg(RDI)))
            .unwrap();
        move_before(&mut machine, load, feed);
        match source_bound_x86_body(&source, &machine, SYSV) {
            Ok(body) => assert!(
                theorem_refuted(body.obligation()),
                "{shape:?}: early read\n{}",
                describe(&machine)
            ),
            Err(X86BodyRefusal::Unsupported(_)) => {
                panic!("{shape:?}: an early read must be judged, not refused")
            }
            Err(other) => panic!("{shape:?}: {other}"),
        }
    }
}

/// The value stored before the call, used where the source reads the slot
/// after it (the callee's write treated as the old contents), is refuted.
#[test]
fn the_old_contents_after_the_call_are_refuted() {
    let (source, mut machine) = slice7_pair(CallMemShape::OutParam);
    let load = load_after_call(&machine, 0);
    let destination = inst(&machine, load).operands[0].clone();
    // `mov v, x` (the stored parameter) instead of the reload.
    *inst_mut(&mut machine, load) = X86ISelInst::new(X86Opcode::MovRR, vec![destination, vreg(0)]);
    refuted(&source, &machine, "the stored value kept across the call");
    let (source, mut machine) = slice7_pair(CallMemShape::OutParamTwice);
    let load = load_after_call(&machine, 1);
    let destination = inst(&machine, load).operands[0].clone();
    *inst_mut(&mut machine, load) = X86ISelInst::new(X86Opcode::MovRR, vec![destination, vreg(0)]);
    refuted(&source, &machine, "the stored value kept across two calls");
}

/// A read of a byte the call did not define (another slot's, which no call
/// received) where the source reads the call's bytes, is refuted.
#[test]
fn a_byte_the_call_did_not_define_is_refuted() {
    // Read the second buffer where the source reads the first, before the
    // second call: the bytes the call never wrote (its initial bytes).
    let (source, mut machine) = slice7_pair(CallMemShape::SretField);
    let load = load_after_call(&machine, 0);
    let destination = inst(&machine, load).operands[0].clone();
    let mut machine_slots = machine.stack_slots.clone();
    machine_slots.push(machine_slots[0]);
    machine.stack_slots = machine_slots.clone();
    let mut source = source;
    source.stack_slots = machine_slots;
    *inst_mut(&mut machine, load) = X86ISelInst::new(
        X86Opcode::MovRM,
        vec![
            destination,
            O::MemAddr {
                base: Box::new(O::StackSlot(1)),
                disp: 8,
            },
        ],
    );
    refuted(&source, &machine, "a slot no call received");
    // The paired slot at another offset after the call: another byte.
    let (source, mut machine) = slice7_pair(CallMemShape::SretSum3);
    let lea = find(&machine, X86Opcode::Lea)[0];
    let base = inst(&machine, lea).operands[0].clone();
    let load = load_after_call(&machine, 0);
    let destination = inst(&machine, load).operands[0].clone();
    *inst_mut(&mut machine, load) = X86ISelInst::new(
        X86Opcode::MovRM,
        vec![
            destination,
            O::MemAddr {
                base: Box::new(base),
                disp: 16,
            },
        ],
    );
    refuted(&source, &machine, "another field of the buffer");
}

/// A value read from the escaped slot between the call that received it and
/// a later call that did not, used where the source reads after the later
/// call, is refuted: the later call may write the slot through a retained
/// address.
#[test]
fn a_slot_value_kept_across_a_later_call_is_refuted() {
    let (source, mut machine) = slice7_pair(CallMemShape::OutParamThenCall);
    let load = load_after_call(&machine, 1);
    let first = find(&machine, X86Opcode::Call)[0];
    move_before(&mut machine, load, first + 1);
    refuted(&source, &machine, "a read before the later call");
    // The first buffer's field, read right after its own call where the
    // source reads it after the second buffer's call.
    let (source, mut machine) = slice7_pair(CallMemShape::SretTwoBuffers);
    let (lea_first, first_call) = argument_lea(&machine, 0);
    let base = inst(&machine, lea_first).operands[0].clone();
    let read = (first_call + 1..rows(&machine).len())
        .find(|ordinal| {
            let row = inst(&machine, *ordinal);
            memory_access(row.opcode).is_some_and(|form| form.load)
                && row.operands[1]
                    == O::MemAddr {
                        base: Box::new(base.clone()),
                        disp: 0,
                    }
        })
        .expect("the first buffer's read");
    assert!(read > find(&machine, X86Opcode::Call)[1]);
    move_before(&mut machine, read, first_call + 1);
    refuted(
        &source,
        &machine,
        "a buffer read before the second buffer's call",
    );
}

/// Different sizes: a narrower read of a call-defined field is refuted, and
/// a machine slot table that differs from the source's (a smaller buffer)
/// makes no claim.
#[test]
fn mismatched_sizes_are_refuted_or_refused() {
    let (source, mut machine) = slice7_pair(CallMemShape::SretField);
    let load = load_after_call(&machine, 0);
    let operands = inst(&machine, load).operands.clone();
    let O::VReg(destination) = operands[0] else {
        panic!("a virtual destination")
    };
    *inst_mut(&mut machine, load) = X86ISelInst::new(
        X86Opcode::MovRM32,
        vec![
            O::VReg(VReg::new(destination.id, RegClass::Gpr64)),
            operands[1].clone(),
        ],
    );
    refuted(&source, &machine, "a four-byte read of an eight-byte field");
    let (source, mut machine) = slice7_pair(CallMemShape::SretSum3);
    machine.stack_slots[0].size = 16;
    expect_unsupported(&source, &machine, "a sixteen-byte buffer");
}

/// An `Option` tag the call wrote, read at another offset of the buffer or
/// as its low half, is refuted on samples. Each differs from the source only
/// where the tag is zero and the other bytes read are not (or the low half
/// is zero and the high half is not), so the sampler must zero call-defined
/// bytes independently, not only all together.
#[test]
fn a_misplaced_or_narrowed_option_tag_read_is_refuted_on_samples() {
    for (shape, displacements) in [
        (CallMemShape::SretOption, &[1, 4, 8, 16][..]),
        (CallMemShape::OptionOutParam, &[1, 4, 8][..]),
    ] {
        let (source, selected) = slice7_pair(shape);
        let tag = load_after_call(&selected, 0);
        assert!(
            matches!(
                &inst(&selected, tag).operands[1],
                O::MemAddr { disp: 0, .. }
            ),
            "{shape:?}: the tag is read at offset 0\n{}",
            describe(&selected)
        );
        for &displacement in displacements {
            let mut machine = selected.clone();
            let O::MemAddr { disp, .. } = &mut inst_mut(&mut machine, tag).operands[1] else {
                unreachable!()
            };
            *disp = displacement;
            refuted(
                &source,
                &machine,
                &format!("{shape:?}: the tag read at offset {displacement}"),
            );
        }
        let mut machine = selected.clone();
        let operands = inst(&machine, tag).operands.clone();
        let O::VReg(destination) = operands[0] else {
            panic!("{shape:?}: a virtual destination")
        };
        *inst_mut(&mut machine, tag) = X86ISelInst::new(
            X86Opcode::MovRM32,
            vec![
                O::VReg(VReg::new(destination.id, RegClass::Gpr64)),
                operands[1].clone(),
            ],
        );
        refuted(
            &source,
            &machine,
            &format!("{shape:?}: the tag's low four bytes"),
        );
    }
}

/// The bytes the callee can read must be the source's: a machine that
/// stores another value into the slot before the call, or none, is refuted.
#[test]
fn different_slot_contents_at_the_call_are_refuted() {
    for (label, shape) in [
        ("ReadRef", CallMemShape::ReadRef),
        ("OutParamVoid", CallMemShape::OutParamVoid),
        ("OptionOutParam", CallMemShape::OptionOutParam),
    ] {
        // The store before the call omitted: the callee reads the slot's
        // initial bytes.
        let (source, mut machine) = slice7_pair(shape);
        let call = find(&machine, X86Opcode::Call)[0];
        let store = (0..call)
            .rev()
            .find(|ordinal| {
                memory_access(inst(&machine, *ordinal).opcode).is_some_and(|form| !form.load)
            })
            .unwrap();
        remove_at(&mut machine, store);
        refuted(
            &source,
            &machine,
            &format!("{label}: no store before the call"),
        );
        // Another value stored (an immediate the selector did not choose).
        let (source, mut machine) = slice7_pair(shape);
        let call = find(&machine, X86Opcode::Call)[0];
        let store = (0..call)
            .rev()
            .find(|ordinal| {
                memory_access(inst(&machine, *ordinal).opcode).is_some_and(|form| !form.load)
            })
            .unwrap();
        let temp = O::VReg(VReg::new(9_000, RegClass::Gpr64));
        inst_mut(&mut machine, store).operands[1] = temp.clone();
        insert_at(
            &mut machine,
            store,
            X86ISelInst::new(X86Opcode::MovRI, vec![temp, O::Imm(77)]),
        );
        refuted(&source, &machine, &format!("{label}: another stored value"));
    }
}

/// Source-side retention: once a slot escaped, an incoming load or store
/// through an address that may derive from it (a call result, an incoming
/// load's bytes, a call-defined slot byte, or a value computed from one) may
/// reach the slot. Slice 7 held it outside the domain; since slice 15 it is
/// admitted and observes the escaped slots' contents at the access (a store
/// redefines them), and the theorem holds. Through a parameter's address,
/// or a call result from before the escape, it is an ordinary incoming
/// access that observes no slot.
#[test]
fn accesses_through_addresses_that_may_derive_from_an_escaped_slot_observe_it() {
    let mut builder = ModuleBuilder::new("x86_source_bound_body_slice7_retention");
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
    let pu64 = Ty::PtrMut(Box::new(Ty::U64));
    let unary_ptr = builder.add_func_type(vec![pu64.clone()], vec![pu64.clone()]);
    let into = builder.declare_function("into", unary_ptr);
    let void_ptr = builder.add_func_type(vec![pu64.clone()], vec![]);
    let bump = builder.declare_function("bump", void_ptr);
    let nullary = builder.add_func_type(vec![], vec![pu64.clone()]);
    let fresh = builder.declare_function("fresh", nullary);
    let cases: [(&str, Vec<Ty>); 6] = [
        // `let p = into(&mut v); *p = 5; v`: a store through a call result.
        ("store_through_result", vec![Ty::U64]),
        // `let p = into(&mut v); *p`: a load through a call result.
        ("load_through_result", vec![Ty::U64]),
        // `bump(&mut v); **pp`: a load through an incoming load's bytes.
        (
            "load_through_loaded",
            vec![Ty::PtrMut(Box::new(pu64.clone())), Ty::U64],
        ),
        // `bump(&mut s.0); *(s.1 as *mut u64)`: through a call-defined byte.
        ("load_through_slot_byte", vec![Ty::U64]),
        // `let p = fresh(); bump(&mut v); *p`: a result from before the
        // escape stays an incoming address (admitted).
        ("load_through_earlier_result", vec![Ty::U64]),
        // `bump(&mut v); *q = v`: a parameter's address (admitted).
        ("store_through_parameter", vec![pu64.clone(), Ty::U64]),
    ];
    for (name, params) in &cases {
        let results = if name.starts_with("store") {
            vec![]
        } else {
            vec![Ty::U64]
        };
        let ty = builder.add_func_type(params.clone(), results);
        let mut f = builder.function(*name, ty);
        let entry = f.create_block();
        let args: Vec<_> = params
            .iter()
            .map(|ty| f.add_block_param(entry, ty.clone()))
            .collect();
        f.switch_to_block(entry);
        let x = *args.last().unwrap();
        match *name {
            "store_through_result" | "load_through_result" => {
                let v = f.alloca(Ty::U64);
                f.store(Ty::U64, v, x);
                let p = f.call(into, vec![v]);
                if *name == "store_through_result" {
                    let five = f.iconst(Ty::U64, 5);
                    f.store(Ty::U64, p, five);
                    f.ret(vec![]);
                } else {
                    let read = f.load(Ty::U64, p);
                    f.ret(vec![read]);
                }
            }
            "load_through_loaded" => {
                let v = f.alloca(Ty::U64);
                f.store(Ty::U64, v, x);
                f.call_void(bump, vec![v]);
                let p = f.load(pu64.clone(), args[0]);
                let read = f.load(Ty::U64, p);
                f.ret(vec![read]);
            }
            "load_through_slot_byte" => {
                let s = f.alloca(pair.clone());
                f.store(Ty::U64, s, x);
                f.call_void(bump, vec![s]);
                let second = f.gep_byte_offset(s, 8);
                let p = f.load(pu64.clone(), second);
                let read = f.load(Ty::U64, p);
                f.ret(vec![read]);
            }
            "load_through_earlier_result" => {
                let p = f.call(fresh, vec![]);
                let v = f.alloca(Ty::U64);
                f.store(Ty::U64, v, x);
                f.call_void(bump, vec![v]);
                let read = f.load(Ty::U64, p);
                f.ret(vec![read]);
            }
            "store_through_parameter" => {
                let v = f.alloca(Ty::U64);
                f.store(Ty::U64, v, x);
                f.call_void(bump, vec![v]);
                let back = f.load(Ty::U64, v);
                f.store(Ty::U64, args[0], back);
                f.ret(vec![]);
            }
            _ => unreachable!(),
        }
        f.build();
    }
    let module = builder.build().expect("ModuleBuilder::build: test fixture");
    for (name, _) in &cases {
        let source = translated_function(&module, name);
        let derived = !(name.ends_with("earlier_result") || name.ends_with("parameter"));
        let body = admitted_body(&source).unwrap_or_else(|refusal| panic!("{name}: {refusal}"));
        let observes = body.paths[0]
            .accesses
            .iter()
            .any(|access| access.slot_reads.is_some());
        assert_eq!(
            observes, derived,
            "{name}: a derived access observes the slots"
        );
        let machine = select(&source, X86CallAbi::SystemV);
        let obligation = owner(&source, &machine, name);
        assert!(theorem_holds(&obligation), "{name}");
    }
}

/// `g1(&v as *const u64 as u64)`: the slot's address cast to an integer (a
/// LIR `Copy`, which keeps it a private address) and passed to a callee is
/// inside the domain since slice 7 (before, the slice-3 domain test held it
/// outside): the slot escapes to the call, which observes its contents, and
/// the theorem holds. Returning the same address stays outside
/// (`calls_outside_the_slice_three_domain_are_unsupported`).
#[test]
fn a_cast_slot_address_passed_to_a_call_is_admitted() {
    let mut builder = ModuleBuilder::new("x86_source_bound_body_slice7_cast");
    let unary = builder.add_func_type(vec![Ty::U64], vec![Ty::U64]);
    let g1 = builder.declare_function("g1", unary);
    let mut f = builder.function("slot_escapes", unary);
    let entry = f.create_block();
    let x = f.add_block_param(entry, Ty::U64);
    f.switch_to_block(entry);
    let slot = f.alloca(Ty::U64);
    f.store(Ty::U64, slot, x);
    let address = f.cast(trust_ir::CastOp::PtrToInt, Ty::Ptr, Ty::U64, slot);
    let result = f.call(g1, vec![address]);
    f.ret(vec![result]);
    f.build();
    let source = translated_function(
        &builder.build().expect("ModuleBuilder::build: test fixture"),
        "slot_escapes",
    );
    let machine = select(&source, X86CallAbi::SystemV);
    let obligation = owner(&source, &machine, "slot_escapes");
    assert!(theorem_holds(&obligation));
    // The call's observable is the slot's contents (no scalar argument),
    // then the result is returned.
    assert_eq!(observable_items(&obligation).len(), 2);
}

/// A slot's address is still only a load/store address or a call argument:
/// stored, returned or computed with, it stays outside the domain; and a
/// return-buffer callee must take a leading pointer and return nothing.
#[test]
fn other_uses_of_an_escaped_address_stay_outside_the_domain() {
    // `*p = &v`, before or after a call that receives v.
    let mut source = slice7_lir(CallMemShape::OutParamThenStore);
    let entry = source.entry_block;
    let body = source.blocks.get_mut(&entry).unwrap();
    let slot = body
        .instructions
        .iter()
        .find(|inst| matches!(inst.opcode, L::StackAddr { .. }))
        .unwrap()
        .results[0];
    let store = body
        .instructions
        .iter()
        .rposition(|inst| matches!(inst.opcode, L::Store { .. }))
        .unwrap();
    body.instructions[store].args[0] = slot;
    let machine = select(&source, X86CallAbi::SystemV);
    // Slice 13 admits a private address stored as data: the theorem holds.
    let owner = source_bound_x86_body(&source, &machine, SYSV)
        .unwrap_or_else(|refusal| panic!("an escaped address stored: {refusal}"));
    assert!(
        theorem_holds(owner.obligation()),
        "an escaped address stored"
    );
    // Returning the escaped address stays outside.
    let mut source = slice7_lir(CallMemShape::OutParam);
    let entry = source.entry_block;
    let body = source.blocks.get_mut(&entry).unwrap();
    let slot = body
        .instructions
        .iter()
        .find(|inst| matches!(inst.opcode, L::StackAddr { .. }))
        .unwrap()
        .results[0];
    for inst in &mut body.instructions {
        if matches!(inst.opcode, L::Return) {
            inst.args = vec![slot];
        }
    }
    let machine = select(&source, X86CallAbi::SystemV);
    expect_unsupported(&source, &machine, "an escaped address returned");
    // An aggregate passed BY VALUE: LIR represents it by its slot's address
    // and types it by the sidecar hint, and the selector passes its bytes
    // (in registers or on the stack), not the address. It is never taken
    // for a private-address argument: since OD-186 the slot's address so
    // typed is that aggregate, passed by its bytes as the selector passes it
    // (the slot does not escape), and a type larger than the slot is
    // refused by name. (The selector refuses this source's store through
    // the address so typed; `arraygep::LoadedPassed` is the machine side.)
    let source = slice7_lir(CallMemShape::ReadRef);
    let slot = source
        .blocks
        .values()
        .flat_map(|block| &block.instructions)
        .find(|inst| matches!(inst.opcode, L::StackAddr { .. }))
        .unwrap()
        .results[0];
    let mut hinted = source.clone();
    hinted
        .value_types
        .insert(slot, Type::Array(Box::new(Type::I64), 1));
    let body = admitted_body(&hinted).expect("a slot address typed as an aggregate");
    assert!(
        matches!(
            body.paths[0].calls[0].args.as_slice(),
            [CallArg::Aggregate(_)]
        ),
        "passed by value, not as the address"
    );
    let mut hinted = source.clone();
    hinted
        .value_types
        .insert(slot, Type::Array(Box::new(Type::I64), 2));
    assert!(matches!(
        admitted_body(&hinted),
        Err(X86BodyRefusal::Unsupported(X86BodyUnsupported::SourceDomain(reason)))
            if reason.contains("passes an aggregate that extends past its slot")
    ));
    // A return-buffer callee with a result is refused by the owner (the
    // selector refuses it too: it would claim the buffer register twice).
    let mut source = slice7_lir(CallMemShape::SretField);
    for block in source.blocks.values_mut() {
        for inst in &mut block.instructions {
            if let L::Call { .. } = inst.opcode {
                inst.results = vec![Value(9_999)];
            }
        }
    }
    source.value_types.insert(Value(9_999), Type::I64);
    assert!(matches!(
        admitted_body(&source),
        Err(X86BodyRefusal::Unsupported(X86BodyUnsupported::SourceDomain(reason)))
            if reason.contains("return-buffer callee")
    ));
}

/// Wrong lowerings the Rust walk cannot judge, each one refuted by the
/// theorem on samples (and replayed to a counterexample on the qualification
/// host): the slot read before the call, the stored value kept across it, a
/// slot value kept across a later call, another field read back, and another
/// value in the slot at the call.
pub(crate) fn slice_seven_refutations() -> Vec<(&'static str, Function, X86ISelFunction)> {
    let mut cases = Vec::new();
    // OutParam: the reload moved before the call.
    let (source, mut machine) = slice7_pair(CallMemShape::OutParam);
    let load = load_after_call(&machine, 0);
    let call = find(&machine, X86Opcode::Call)[0];
    let feed = (0..call)
        .rev()
        .find(|ordinal| inst(&machine, *ordinal).operands.first() == Some(&preg(RDI)))
        .unwrap();
    move_before(&mut machine, load, feed);
    cases.push(("OutParam/read-before-call", source, machine));
    // OutParam: the parameter instead of the reload.
    let (source, mut machine) = slice7_pair(CallMemShape::OutParam);
    let load = load_after_call(&machine, 0);
    let destination = inst(&machine, load).operands[0].clone();
    *inst_mut(&mut machine, load) = X86ISelInst::new(X86Opcode::MovRR, vec![destination, vreg(0)]);
    cases.push(("OutParam/old-contents", source, machine));
    // OutParamThenCall: the slot read before the later call.
    let (source, mut machine) = slice7_pair(CallMemShape::OutParamThenCall);
    let load = load_after_call(&machine, 1);
    let first = find(&machine, X86Opcode::Call)[0];
    move_before(&mut machine, load, first + 1);
    cases.push(("OutParamThenCall/read-before-later-call", source, machine));
    // SretSum3: the third field read where the first is.
    let (source, mut machine) = slice7_pair(CallMemShape::SretSum3);
    let lea = find(&machine, X86Opcode::Lea)[0];
    let base = inst(&machine, lea).operands[0].clone();
    let load = load_after_call(&machine, 0);
    let destination = inst(&machine, load).operands[0].clone();
    *inst_mut(&mut machine, load) = X86ISelInst::new(
        X86Opcode::MovRM,
        vec![
            destination,
            O::MemAddr {
                base: Box::new(base),
                disp: 16,
            },
        ],
    );
    cases.push(("SretSum3/another-field", source, machine));
    // ReadRef: another value in the slot at the call.
    let (source, mut machine) = slice7_pair(CallMemShape::ReadRef);
    let call = find(&machine, X86Opcode::Call)[0];
    let store = (0..call)
        .rev()
        .find(|ordinal| {
            memory_access(inst(&machine, *ordinal).opcode).is_some_and(|form| !form.load)
        })
        .unwrap();
    let temp = O::VReg(VReg::new(9_000, RegClass::Gpr64));
    inst_mut(&mut machine, store).operands[1] = temp.clone();
    insert_at(
        &mut machine,
        store,
        X86ISelInst::new(X86Opcode::MovRI, vec![temp, O::Imm(77)]),
    );
    cases.push(("ReadRef/other-contents", source, machine));
    // OptionOutParam: the tag read before the call (the stored `None`).
    let (source, mut machine) = slice7_pair(CallMemShape::OptionOutParam);
    let load = load_after_call(&machine, 0);
    let call = find(&machine, X86Opcode::Call)[0];
    let feed = (0..call)
        .rev()
        .find(|ordinal| inst(&machine, *ordinal).operands.first() == Some(&preg(RDI)))
        .unwrap();
    move_before(&mut machine, load, feed);
    cases.push(("OptionOutParam/tag-before-call", source, machine));
    cases
}

#[test]
fn every_slice_seven_refutation_is_refuted_on_samples() {
    for (label, source, machine) in slice_seven_refutations() {
        // As built, in slice 18's spelling: slice 19's states some of these
        // wrong lowerings as one guarded item, a form this file's sampler
        // (written for the slice-7 construction) does not read; its value is
        // slice 18's on every input
        // (`slice19::the_full_spelling_preserves_every_fixture_theorem`).
        let theorem = with_normal_groups(normal::Groups::NONE, || {
            theorem_without_affine_refusal(&source, &machine, SYSV)
        })
        .unwrap_or_else(|refusal| panic!("{label}: {refusal}\n{}", describe(&machine)));
        assert!(theorem_refuted(&theorem), "{label}\n{}", describe(&machine));
    }
}

/// The real x86 optimizer's output at O1, O2 and O3 for every slice-7
/// fixture: the owner never names a mismatch for a correct lowering, and
/// every theorem it builds holds. (An optimized body it cannot pair makes no
/// claim.)
#[test]
fn optimized_slice_seven_fixtures_are_judged_without_false_mismatches() {
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
        for shape in all_slice_seven_shapes() {
            let (source, mut machine) = slice7_pair(shape);
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

/// Re-pinned for the zero-extending narrow loads (`movzx r32, m8/m16`): the
/// one shape with a byte load, `SretNarrow` (its `bool` read back from the
/// escaped `sret` buffer), loses the free input `u0` above the loaded byte
/// and the register `movzx` row, and widens the 0/1 result with `MovRR32`;
/// every other entry is byte-identical.
const SLICE_SEVEN_SNAPSHOT_SHA256: &str =
    "e8786dda14882fa0d492712200e22a3e2494070bc6b54ff08b36823ec564ea99";

#[test]
fn slice_seven_smt2_is_canonical_per_shape() {
    use sha2::{Digest, Sha256};
    const GOLDEN: &str =
        include_str!("../tests/fixtures/x86_source_bound_body/slice7_snapshots.smt2");
    let mut rendered = String::new();
    for shape in SLICE_SEVEN {
        let (source, machine) = slice7_pair(shape);
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
            .join("tests/fixtures/x86_source_bound_body/slice7_snapshots.smt2");
        std::fs::write(&path, &rendered).unwrap();
        panic!(
            "rewrote {}; review its diff, set SLICE_SEVEN_SNAPSHOT_SHA256 to {:x} and re-run \
             without TCG_X86_BODY_SNAPSHOT_WRITE",
            path.display(),
            Sha256::digest(rendered.as_bytes())
        );
    }
    assert_eq!(
        format!("{:x}", Sha256::digest(GOLDEN.as_bytes())),
        SLICE_SEVEN_SNAPSHOT_SHA256,
        "the golden file changed without the reviewed digest pin"
    );
    assert_eq!(rendered, GOLDEN, "slice-7 snapshots drifted");
}

/// Slices 1 to 6 are unchanged by slice 7: a body with no escaped slot
/// observes no slot contents and declares no call-defined byte.
#[test]
fn bodies_without_an_escaped_slot_declare_no_call_defined_byte() {
    for shape in all_shapes() {
        let (source, machine) = pair(shape);
        if let Ok(body) = source_bound_x86_body(&source, &machine, SYSV) {
            assert!(call_bytes_of(body.obligation()).is_empty(), "{shape:?}");
        }
    }
    for shape in super::memory::MEMORY_SHAPES {
        let (source, machine) = super::memory::memory_pair(shape);
        let body = source_bound_x86_body(&source, &machine, SYSV).unwrap();
        assert!(call_bytes_of(body.obligation()).is_empty(), "{shape:?}");
    }
}

/// The several-path fixtures state one claim per path, and a path that does
/// not run the call reads no call-defined byte.
#[test]
fn a_path_without_the_call_reads_no_call_defined_byte() {
    let (source, machine) = slice7_pair(CallMemShape::SretBranch);
    let obligation = owned_plain_theorem(&source, &machine, "SretBranch");
    let claims = path_claims(&obligation);
    assert_eq!(claims.len(), 2);
    let names = |expr: &E| expr.free_vars().into_iter().collect::<HashSet<_>>();
    let defined: HashMap<String, E> = obligation
        .preconditions
        .iter()
        .filter_map(|premise| match premise {
            E::Eq { lhs, rhs } => match lhs.as_ref() {
                E::Var { name, .. } => Some((name.clone(), rhs.as_ref().clone())),
                _ => None,
            },
            _ => None,
        })
        .collect();
    let reaches_call_byte = |expr: &E| {
        let mut pending: Vec<String> = names(expr).into_iter().collect();
        let mut seen = HashSet::new();
        while let Some(name) = pending.pop() {
            if parse_call_byte_name(&name).is_some() {
                return true;
            }
            if seen.insert(name.clone())
                && let Some(expr) = defined.get(&name)
            {
                pending.extend(expr.free_vars());
            }
        }
        false
    };
    assert!(
        reaches_call_byte(&claims[0].1),
        "the `then` path reads the buffer"
    );
    assert!(!reaches_call_byte(&claims[1].1), "the `else` path does not");
}
