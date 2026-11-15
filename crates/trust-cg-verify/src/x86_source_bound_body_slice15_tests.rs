// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Slice 15 of the x86-64 source-bound body theorem: the value, call and
//! observable residue. Float constants and the sign-bit operations `Fneg` and
//! `Fabs` as exact bit-pattern operations (the selector's constant-pool
//! `movss`/`movsd` loads and `pxor`/`andps`/`andpd` masks); register copies
//! and ALU rows of mixed 32- and 64-bit registers (a 3-byte aggregate
//! eightbyte), of which only the low 32 bits are defined; a `bool` parameter
//! forwarded as a `bool` argument (the selector zero-extends a `bool`
//! parameter's low byte at entry); accesses through an address that may
//! derive from an escaped slot, observed with the escaped slots' contents;
//! and an `I128` parameter or argument in the stack argument areas.
//!
//! Fixtures are real: LIR from the trust-ir adapter and the machine stream
//! from the real x86-64 instruction selector (`super::select`). Negative
//! controls mutate that stream and must end as a typed mismatch, a refuted
//! theorem or an unsupported (uncredited) body, never as Formal credit.
//!
//! Every test here runs without a solver, and the soundness check runs them
//! all (the `x86_source_bound_body::tests::slice15::` library gate). The
//! replay on AY and Clean and the verifier-credit tests are in
//! `slice15_qualification`.

use super::slice5::describe;
use super::slice6::describe_lir;
use super::slice11::{theorem_holds, theorem_refuted};
use super::*;
use trust_ir::UnOp;

/// Slice-15 fixture shapes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ResidueShape {
    // ---- (a) float bit patterns (OD-73's model, ruling OD-112)
    /// `fn() -> f32 { 1.5 }`: a constant-pool `movss`.
    ConstF32,
    /// `fn() -> f64 { f64::MIN_POSITIVE }`.
    ConstF64,
    /// `fn() -> f64 { f64::NAN }`: the NaN's exact bits.
    ConstF64Nan,
    /// `fn() -> f32 { f32::INFINITY }`.
    ConstF32Inf,
    /// `fn(p: *mut f64) { *p = -0.0 }`: a stored constant.
    ConstStored,
    /// `fn(x: f32) -> f32 { -x }`: `pxor` with the sign mask.
    NegF32,
    /// `fn(x: f64) -> f64 { -x }`.
    NegF64,
    /// `fn(x: f32) -> f32 { x.abs() }`: `andps` with the magnitude mask.
    AbsF32,
    /// `fn(x: f64) -> f64 { x.abs() }`: `andpd`.
    AbsF64,
    /// `fn(x: f64) -> u64 { (-x).abs().to_bits() }`.
    NegAbsBits,
    // ---- (b) mixed-width registers (a 3-byte aggregate eightbyte)
    /// `fn(x: [u8; 3]) -> [u8; 3] { g3(x) }`: the parameter's eightbyte
    /// copied from a 32-bit into a 64-bit register, the argument's assembled
    /// in EDI from a 64-bit one (`mov edi, r64; or edi, r64`).
    ThreeBytes,
    // ---- (c) a `bool` parameter forwarded (ruling OD-113)
    /// `fn(b: bool) { sink(b) }`.
    ForwardBool,
    /// `fn(x: u64, b: bool) -> u64 { mix(x, b) }`.
    ForwardBoolMixed,
    /// `fn(b: bool) -> bool { flip(b) }`: walked under both caller views.
    ForwardBoolReturn,
    // ---- (d) accesses through a derived address (ruling OD-114)
    /// `fn() -> u64 { let mut p = null; fill(&mut p); *p }`: the pointer a
    /// callee left in an escaped slot, loaded through.
    DerivedLoad,
    /// `fn(x: u64) -> u64 { let v = x; let p = id(&v); *p }`: a pointer
    /// the call returned after `v` escaped (it may be `&v`).
    DerivedLoadReturned,
    /// `fn(x: u64, y: u64) -> u64 { let v = x; let p = id(&v); *p = y; v }`:
    /// a store through it, then `v` read back.
    DerivedStore,
    /// `fn() -> u64 { let mut r = [0; 2]; data(&mut r); *((r[1] + 8) as
    /// *const u64) }`: a vtable-like load at an offset.
    DerivedLoadOffset,
    // ---- (e) `I128` in the stack argument areas
    /// `fn(a: u64, b: u128, c: u128, d: u128) -> u128 { d }`: `d` at
    /// `[rbp + 16]` (R9 alone is left).
    StackParamI128,
    /// `fn(a: u64, b: u128, c: u128, d: u128, e: u64) -> u64 { e }`: `e`
    /// takes R9 after `d` went to the stack.
    StackParamI128ThenScalar,
    /// `fn(a: u64, b: u128, c: u128, d: u128) -> u64 { take4(a, b, c, d) }`:
    /// `d` at `[rsp]` at the call.
    StackArgI128,
    /// `fn(a: u64, b: u128, c: u128, d: u128) -> u64 { take5(a, b, c, a, d) }`:
    /// `d` 16-byte aligned past a scalar stack argument, at `[rsp + 16]`.
    StackArgI128Aligned,
}

/// Every slice-15 shape whose real selection the owner admits and whose
/// theorem holds ([`every_admitted_slice_fifteen_fixture_is_qualified`]
/// checks that none is left out).
pub(crate) const SLICE_FIFTEEN: [ResidueShape; 22] = [
    ResidueShape::ConstF32,
    ResidueShape::ConstF64,
    ResidueShape::ConstF64Nan,
    ResidueShape::ConstF32Inf,
    ResidueShape::ConstStored,
    ResidueShape::NegF32,
    ResidueShape::NegF64,
    ResidueShape::AbsF32,
    ResidueShape::AbsF64,
    ResidueShape::NegAbsBits,
    ResidueShape::ThreeBytes,
    ResidueShape::ForwardBool,
    ResidueShape::ForwardBoolMixed,
    ResidueShape::ForwardBoolReturn,
    ResidueShape::DerivedLoad,
    ResidueShape::DerivedLoadReturned,
    ResidueShape::DerivedStore,
    ResidueShape::DerivedLoadOffset,
    ResidueShape::StackParamI128,
    ResidueShape::StackParamI128ThenScalar,
    ResidueShape::StackArgI128,
    ResidueShape::StackArgI128Aligned,
];

impl ResidueShape {
    fn name(self) -> String {
        let name = format!("{self:?}");
        let mut snake = String::from("s15_");
        for (i, c) in name.chars().enumerate() {
            if c.is_ascii_uppercase() && i > 0 {
                snake.push('_');
            }
            snake.push(c.to_ascii_lowercase());
        }
        snake
    }
}

/// The LIR the trust-ir adapter produces for a slice-15 shape.
pub(crate) fn slice15_lir(shape: ResidueShape) -> Function {
    use ResidueShape::*;
    let mut builder = ModuleBuilder::new("x86_source_bound_body_slice15");
    let bytes3 = {
        let element = builder.add_type(Ty::U8);
        Ty::Array(element, 3)
    };
    let u64x2 = {
        let element = builder.add_type(Ty::U64);
        Ty::Array(element, 2)
    };
    let ptr_u64 = Ty::PtrMut(Box::new(Ty::U64));
    let ptr_ptr = Ty::PtrMut(Box::new(ptr_u64.clone()));
    let mut declare = |name: &str, params: Vec<Ty>, results: Vec<Ty>| {
        let ty = builder.add_func_type(params, results);
        builder.declare_function(name, ty)
    };
    let g3 = declare("g3", vec![bytes3.clone()], vec![bytes3.clone()]);
    let sink = declare("sink", vec![Ty::Bool], vec![]);
    let mix = declare("mix", vec![Ty::U64, Ty::Bool], vec![Ty::U64]);
    let flip = declare("flip", vec![Ty::Bool], vec![Ty::Bool]);
    let fill = declare("fill", vec![ptr_ptr.clone()], vec![]);
    let id = declare("id", vec![ptr_u64.clone()], vec![ptr_u64.clone()]);
    let data = declare("data", vec![Ty::PtrMut(Box::new(u64x2.clone()))], vec![]);
    let take4 = declare(
        "take4",
        vec![Ty::U64, Ty::U128, Ty::U128, Ty::U128],
        vec![Ty::U64],
    );
    let take5 = declare(
        "take5",
        vec![Ty::U64, Ty::U128, Ty::U128, Ty::U64, Ty::U128],
        vec![Ty::U64],
    );
    let wide = vec![Ty::U64, Ty::U128, Ty::U128, Ty::U128];
    let (params, results): (Vec<Ty>, Vec<Ty>) = match shape {
        ConstF32 | ConstF32Inf => (vec![], vec![Ty::F32]),
        ConstF64 | ConstF64Nan => (vec![], vec![Ty::F64]),
        ConstStored => (vec![Ty::Ptr], vec![]),
        NegF32 | AbsF32 => (vec![Ty::F32], vec![Ty::F32]),
        NegF64 | AbsF64 => (vec![Ty::F64], vec![Ty::F64]),
        NegAbsBits => (vec![Ty::F64], vec![Ty::U64]),
        ThreeBytes => (vec![bytes3.clone()], vec![bytes3.clone()]),
        ForwardBool => (vec![Ty::Bool], vec![]),
        ForwardBoolMixed => (vec![Ty::U64, Ty::Bool], vec![Ty::U64]),
        ForwardBoolReturn => (vec![Ty::Bool], vec![Ty::Bool]),
        DerivedLoad | DerivedLoadOffset => (vec![], vec![Ty::U64]),
        DerivedLoadReturned => (vec![Ty::U64], vec![Ty::U64]),
        DerivedStore => (vec![Ty::U64, Ty::U64], vec![Ty::U64]),
        StackParamI128 => (wide.clone(), vec![Ty::U128]),
        StackParamI128ThenScalar => {
            let mut params = wide.clone();
            params.push(Ty::U64);
            (params, vec![Ty::U64])
        }
        StackArgI128 | StackArgI128Aligned => (wide.clone(), vec![Ty::U64]),
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
        ConstF32 | ConstF32Inf | ConstF64 | ConstF64Nan => {
            let (ty, value) = match shape {
                ConstF32 => (Ty::F32, 1.5),
                ConstF32Inf => (Ty::F32, f64::INFINITY),
                ConstF64 => (Ty::F64, f64::MIN_POSITIVE),
                _ => (Ty::F64, f64::NAN),
            };
            let constant = f.fconst(ty, value);
            f.ret(vec![constant]);
        }
        ConstStored => {
            let constant = f.fconst(Ty::F64, -0.0);
            f.store(Ty::F64, args[0], constant);
            f.ret(vec![]);
        }
        NegF32 | NegF64 | AbsF32 | AbsF64 => {
            let ty = if matches!(shape, NegF32 | AbsF32) {
                Ty::F32
            } else {
                Ty::F64
            };
            let op = if matches!(shape, NegF32 | NegF64) {
                UnOp::FNeg
            } else {
                UnOp::FAbs
            };
            let value = f.unop(op, ty, args[0]);
            f.ret(vec![value]);
        }
        NegAbsBits => {
            let negated = f.unop(UnOp::FNeg, Ty::F64, args[0]);
            let magnitude = f.unop(UnOp::FAbs, Ty::F64, negated);
            let bits = f.cast(CastOp::Bitcast, Ty::F64, Ty::U64, magnitude);
            f.ret(vec![bits]);
        }
        ThreeBytes => {
            let result = f.call(g3, vec![args[0]]);
            f.ret(vec![result]);
        }
        ForwardBool => {
            f.call_void(sink, vec![args[0]]);
            f.ret(vec![]);
        }
        ForwardBoolMixed => {
            let result = f.call(mix, vec![args[0], args[1]]);
            f.ret(vec![result]);
        }
        ForwardBoolReturn => {
            let result = f.call(flip, vec![args[0]]);
            f.ret(vec![result]);
        }
        DerivedLoad => {
            let p = f.alloca(ptr_u64.clone());
            let null = f.null_ptr();
            f.store(ptr_u64.clone(), p, null);
            f.call_void(fill, vec![p]);
            let pointer = f.load(ptr_u64.clone(), p);
            let value = f.load(Ty::U64, pointer);
            f.ret(vec![value]);
        }
        DerivedLoadReturned | DerivedStore => {
            let v = f.alloca(Ty::U64);
            f.store(Ty::U64, v, args[0]);
            let pointer = f.call(id, vec![v]);
            if shape == DerivedLoadReturned {
                let value = f.load(Ty::U64, pointer);
                f.ret(vec![value]);
            } else {
                f.store(Ty::U64, pointer, args[1]);
                let back = f.load(Ty::U64, v);
                f.ret(vec![back]);
            }
        }
        DerivedLoadOffset => {
            let r = f.alloca(u64x2.clone());
            let zero = f.iconst(Ty::U64, 0);
            f.store(Ty::U64, r, zero);
            let second = f.gep_byte_offset(r, 8);
            f.store(Ty::U64, second, zero);
            f.call_void(data, vec![r]);
            let table = f.load(Ty::U64, second);
            let base = f.cast(CastOp::IntToPtr, Ty::U64, Ty::Ptr, table);
            let entry_address = f.gep_byte_offset(base, 8);
            let value = f.load(Ty::U64, entry_address);
            f.ret(vec![value]);
        }
        StackParamI128 => f.ret(vec![args[3]]),
        StackParamI128ThenScalar => f.ret(vec![args[4]]),
        StackArgI128 => {
            let result = f.call(take4, vec![args[0], args[1], args[2], args[3]]);
            f.ret(vec![result]);
        }
        StackArgI128Aligned => {
            let result = f.call(take5, vec![args[0], args[1], args[2], args[0], args[3]]);
            f.ret(vec![result]);
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

pub(crate) fn slice15_pair(shape: ResidueShape) -> (Function, X86ISelFunction) {
    let source = slice15_lir(shape);
    let machine = select(&source, X86CallAbi::SystemV);
    (source, machine)
}

/// Every fixture shape, in declaration order.
pub(crate) fn all_slice_fifteen_shapes() -> Vec<ResidueShape> {
    use ResidueShape::*;
    let all = SLICE_FIFTEEN.to_vec();
    // Exhaustive: a new shape does not compile until it is listed here.
    for shape in &all {
        match shape {
            ConstF32
            | ConstF64
            | ConstF64Nan
            | ConstF32Inf
            | ConstStored
            | NegF32
            | NegF64
            | AbsF32
            | AbsF64
            | NegAbsBits
            | ThreeBytes
            | ForwardBool
            | ForwardBoolMixed
            | ForwardBoolReturn
            | DerivedLoad
            | DerivedLoadReturned
            | DerivedStore
            | DerivedLoadOffset
            | StackParamI128
            | StackParamI128ThenScalar
            | StackArgI128
            | StackArgI128Aligned => {}
        }
    }
    all
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

/// The pair makes no claim, for the reason `needle` names (another refusal
/// later in the walk would hide a missing rule).
#[track_caller]
fn expect_unsupported_naming(source: &Function, machine: &X86ISelFunction, needle: &str) {
    match source_bound_x86_body(source, machine, SYSV) {
        Err(X86BodyRefusal::Unsupported(reason)) => {
            let reason = reason.to_string();
            assert!(
                reason.contains(needle),
                "expected `{needle}`, got: {reason}"
            );
        }
        Err(other) => panic!("{needle}: expected Unsupported, got {other}"),
        Ok(_) => panic!("{needle}: an out-of-domain pair built a body theorem"),
    }
}

/// The source admission's refusal of `source`, as text.
#[track_caller]
fn admission_refusal(source: &Function) -> String {
    match admitted_body(source) {
        Ok(_) => panic!("admitted\n{}", describe_lir(source)),
        Err(refusal) => refusal.to_string(),
    }
}

/// The walk ordinal of the first row satisfying `predicate`.
#[track_caller]
fn row_where(machine: &X86ISelFunction, predicate: impl Fn(&X86ISelInst) -> bool) -> usize {
    rows(machine)
        .into_iter()
        .map(|(ordinal, _, _)| ordinal)
        .find(|ordinal| predicate(inst(machine, *ordinal)))
        .unwrap_or_else(|| panic!("no such row\n{}", describe(machine)))
}

/// Whether a row reads or writes memory through `[base + disp]` with a
/// physical base register `root`.
fn through(inst: &X86ISelInst, root: u16) -> bool {
    inst.operands
        .iter()
        .any(|operand| matches!(operand, O::MemAddr { base, .. } if **base == preg(root)))
}

/// The walk ordinal of the first load row after the `n`-th call.
fn load_after_call(machine: &X86ISelFunction, n: usize) -> usize {
    let call = find(machine, X86Opcode::Call)[n];
    (call + 1..rows(machine).len())
        .find(|ordinal| memory_access(inst(machine, *ordinal).opcode).is_some_and(|f| f.load))
        .expect("a load after the call")
}

/// A fresh 64-bit virtual register.
fn fresh(id: u32) -> O {
    O::VReg(VReg::new(id, RegClass::Gpr64))
}

// ---------------------------------------------------------------------------
// Construction (no solver)
// ---------------------------------------------------------------------------

#[test]
fn owner_builds_for_every_slice_fifteen_shape_and_covers_every_value_row() {
    for shape in SLICE_FIFTEEN {
        let (source, machine) = slice15_pair(shape);
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
fn slice_fifteen_theorems_hold_on_samples() {
    for shape in SLICE_FIFTEEN {
        let (source, machine) = slice15_pair(shape);
        let obligation = owner(&source, &machine, &format!("{shape:?}"));
        assert!(
            theorem_holds(&obligation),
            "{shape:?}\n{}",
            describe(&machine)
        );
    }
}

/// The golden, owner, credit and host-qualification tests run over
/// [`SLICE_FIFTEEN`]: every fixture whose real selection the owner admits
/// with a theorem that holds must be in it.
#[test]
fn every_admitted_slice_fifteen_fixture_is_qualified() {
    for shape in all_slice_fifteen_shapes() {
        let (source, machine) = slice15_pair(shape);
        let holds = source_bound_x86_body(&source, &machine, SYSV)
            .is_ok_and(|owner| theorem_holds(owner.obligation()));
        assert_eq!(SLICE_FIFTEEN.contains(&shape), holds, "{shape:?}");
    }
}

/// The fixtures exercise the forms they are named for: the selector's
/// constant-pool loads and sign masks, mixed-width moves, the `bool`
/// parameter's zero extension at entry and the stack areas' `I128`
/// eightbytes.
#[test]
fn slice_fifteen_fixtures_have_the_expected_pre_ra_shapes() {
    use ResidueShape::*;
    let has = |shape: ResidueShape, opcode: X86Opcode| {
        let (_, machine) = slice15_pair(shape);
        !find(&machine, opcode).is_empty()
    };
    assert!(has(ConstF32, X86Opcode::MovssRipRel));
    assert!(has(ConstF64Nan, X86Opcode::MovsdRipRel));
    assert!(has(NegF32, X86Opcode::Pxor) && has(NegF64, X86Opcode::Pxor));
    assert!(has(AbsF32, X86Opcode::Andps) && has(AbsF64, X86Opcode::Andpd));
    {
        let shape = ThreeBytes;
        let (_, machine) = slice15_pair(shape);
        let mixed = rows(&machine).into_iter().any(|(ordinal, _, _)| {
            let row = inst(&machine, ordinal);
            let widths: Vec<Option<u32>> = row
                .operands
                .iter()
                .map(|operand| gpr(operand).map(|reg| reg.bits))
                .collect();
            matches!(row.opcode, X86Opcode::MovRR | X86Opcode::OrRR)
                && widths.iter().all(Option::is_some)
                && widths.windows(2).any(|pair| pair[0] != pair[1])
        });
        assert!(
            mixed,
            "{shape:?}: a mixed-width row\n{}",
            describe(&machine)
        );
    }
    for shape in [ForwardBool, ForwardBoolMixed, ForwardBoolReturn] {
        let (_, machine) = slice15_pair(shape);
        let entry = row_where(&machine, |row| {
            row.opcode == X86Opcode::Movzx
                && row
                    .operands
                    .get(1)
                    .and_then(gpr)
                    .is_some_and(|reg| matches!(reg.root, Root::Physical(_)))
        });
        assert!(
            entry < 3,
            "{shape:?}: the bool parameter zero-extended at entry\n{}",
            describe(&machine)
        );
    }
    let (_, machine) = slice15_pair(StackParamI128);
    let reads: Vec<i32> = rows(&machine)
        .into_iter()
        .filter_map(
            |(ordinal, _, _)| match &inst(&machine, ordinal).operands.get(1) {
                Some(O::MemAddr { base, disp }) if **base == preg(RBP) => Some(*disp),
                _ => None,
            },
        )
        .collect();
    assert_eq!(reads, vec![16, 24], "{}", describe(&machine));
}

// ---------------------------------------------------------------------------
// The model's rules (no solver)
// ---------------------------------------------------------------------------

/// Run a one-function trust-ir module on the pinned reference interpreter
/// (`trust_ir::interpret`) with float arguments given as bit patterns, and
/// return the bit pattern of its one float result.
fn interpret_float(module: &trust_ir::Module, name: &str, args: &[(Ty, u64)]) -> u64 {
    use trust_ir::interpret::{InterpretValue, InterpretValueKind, Interpreter};
    let function = module.function_by_name(name).expect("the function");
    let interpreter = Interpreter::with_module(module);
    let values: Vec<InterpretValue> = args
        .iter()
        .map(|(ty, bits)| InterpretValue {
            ty: ty.clone(),
            kind: InterpretValueKind::FloatBits(*bits),
        })
        .collect();
    let outcome = interpreter
        .execute_function(function, values)
        .unwrap_or_else(|error| panic!("{name}: {error:?}"));
    match &outcome.returns[..] {
        [
            InterpretValue {
                kind: InterpretValueKind::FloatBits(bits),
                ..
            },
        ] => *bits,
        other => panic!("{name}: {other:?}"),
    }
}

/// The verify-owned meanings of `Fneg`, `Fabs` ([`FloatSignOp`]) and a float
/// constant ([`float_constant_bits`]) are trust-ir's, measured against the
/// pinned reference interpreter on every class of bit pattern: zeros,
/// subnormals, normals, infinities, quiet and signalling NaNs with payloads,
/// of either sign; and constants that round, overflow and underflow at `f32`.
#[test]
fn the_float_sign_and_constant_meanings_are_trust_irs() {
    use crate::smt::{EvalEnv, EvalResult};
    let mut builder = ModuleBuilder::new("x86_source_bound_body_slice15_float_meanings");
    for (ty, tag) in [(Ty::F32, "f32"), (Ty::F64, "f64")] {
        for (op, op_tag) in [(UnOp::FNeg, "neg"), (UnOp::FAbs, "abs")] {
            let signature = builder.add_func_type(vec![ty.clone()], vec![ty.clone()]);
            let mut f = builder.function(format!("{op_tag}_{tag}"), signature);
            let entry = f.create_block();
            let x = f.add_block_param(entry, ty.clone());
            f.switch_to_block(entry);
            let y = f.unop(op, ty.clone(), x);
            f.ret(vec![y]);
            f.build();
        }
    }
    let constants: Vec<(Ty, f64)> = [
        0.0,
        -0.0,
        1.5,
        0.1,
        f64::MIN_POSITIVE,
        1e-40,
        1e-50,
        3.5e38,
        1e300,
        f64::INFINITY,
        f64::NEG_INFINITY,
        f64::NAN,
        f64::from_bits(0x7ff0_0000_0000_0001),
        f64::from_bits(0xfff8_dead_beef_0000),
    ]
    .into_iter()
    .flat_map(|value| [(Ty::F32, value), (Ty::F64, value)])
    .filter(|(ty, value)| !(*ty == Ty::F32 && value.is_nan()))
    .collect();
    for (k, (ty, value)) in constants.iter().enumerate() {
        let signature = builder.add_func_type(vec![], vec![ty.clone()]);
        let mut f = builder.function(format!("const_{k}"), signature);
        let entry = f.create_block();
        f.switch_to_block(entry);
        let c = f.fconst(ty.clone(), *value);
        f.ret(vec![c]);
        f.build();
    }
    let module = builder.build().expect("ModuleBuilder::build: test fixture");
    let patterns32: Vec<u64> = vec![
        0,
        0x8000_0000,
        1,
        0x0000_ffff,
        0x3f80_0000,
        0xbf80_0000,
        0x7f80_0000,
        0xff80_0000,
        0x7fc0_0000,
        0xffc0_0001,
        0x7f80_0001,
        0xff80_1234,
        0x7fbf_ffff,
        0x1234_5678,
        0xdead_beef,
    ];
    let patterns64: Vec<u64> = vec![
        0,
        1 << 63,
        1,
        0x000f_ffff_ffff_ffff,
        0x3ff0_0000_0000_0000,
        0xbff0_0000_0000_0000,
        0x7ff0_0000_0000_0000,
        0xfff0_0000_0000_0000,
        0x7ff8_0000_0000_0000,
        0xfff8_0000_0000_0001,
        0x7ff0_0000_0000_0001,
        0xfff4_0000_dead_beef,
        0x0123_4567_89ab_cdef,
        0xdead_beef_cafe_f00d,
    ];
    for (ty, tag, bits, patterns) in [
        (Ty::F32, "f32", 32, &patterns32),
        (Ty::F64, "f64", 64, &patterns64),
    ] {
        for (op, op_tag) in [(FloatSignOp::Neg, "neg"), (FloatSignOp::Abs, "abs")] {
            for pattern in patterns {
                let expected = interpret_float(
                    &module,
                    &format!("{op_tag}_{tag}"),
                    &[(ty.clone(), *pattern)],
                );
                let mut env = EvalEnv::default();
                env.insert("x".into(), *pattern);
                let EvalResult::Bv(stated) = op.apply(E::var("x", bits), bits).eval(&env) else {
                    panic!("a bit-vector");
                };
                assert_eq!(stated, expected, "{op_tag}_{tag} of {pattern:#x}");
            }
        }
    }
    for (k, (ty, value)) in constants.iter().enumerate() {
        let carrier = if *ty == Ty::F32 {
            Carrier::F32
        } else {
            Carrier::F64
        };
        let expected = interpret_float(&module, &format!("const_{k}"), &[]);
        assert_eq!(
            float_constant_bits(carrier, *value),
            Some(expected),
            "{ty:?} constant {value:e}"
        );
    }
    // An `f32` NaN constant's narrowed payload is not pinned: outside.
    assert_eq!(float_constant_bits(Carrier::F32, f64::NAN), None);
}

/// A float constant or sign mask is read from the constant pool only by a
/// `movss`/`movsd` load of exactly the entry's bytes; anything else makes no
/// claim, an `f32` NaN constant is refused by name, and every other
/// floating-point operation stays outside (OD-73).
#[test]
fn constant_pool_reads_and_float_operations_are_admitted_exactly() {
    // A 4-byte entry read by `movsd`.
    let (source, mut machine) = slice15_pair(ResidueShape::ConstF32);
    let load = row_where(&machine, |row| row.opcode == X86Opcode::MovssRipRel);
    inst_mut(&mut machine, load).opcode = X86Opcode::MovsdRipRel;
    expect_unsupported_naming(&source, &machine, "which does not hold 8 bytes");
    // An entry of another size.
    let (source, mut machine) = slice15_pair(ResidueShape::ConstF64);
    machine.const_pool_entries[0].data.truncate(4);
    expect_unsupported_naming(&source, &machine, "which does not hold 8 bytes");
    // An entry named by a row other than the scalar load.
    let (source, mut machine) = slice15_pair(ResidueShape::AbsF32);
    let mask = row_where(&machine, |row| row.opcode == X86Opcode::Andps);
    inst_mut(&mut machine, mask).operands[2] = O::ConstPoolEntry(0);
    expect_unsupported_naming(&source, &machine, "constant pool");
    // An `f32` NaN constant.
    let mut source = slice15_lir(ResidueShape::ConstF32);
    for block in source.blocks.values_mut() {
        for inst in &mut block.instructions {
            if let L::Fconst { imm, .. } = &mut inst.opcode {
                *imm = f64::NAN;
            }
        }
    }
    let refusal = admission_refusal(&source);
    assert!(refusal.contains("is an f32 NaN constant"), "{refusal}");
    // Floating-point arithmetic stays outside, by name.
    for opcode in [L::Fsqrt, L::Ffloor] {
        let mut source = slice15_lir(ResidueShape::NegF32);
        for block in source.blocks.values_mut() {
            for inst in &mut block.instructions {
                if matches!(inst.opcode, L::Fneg) {
                    inst.opcode = opcode.clone();
                }
            }
        }
        let refusal = admission_refusal(&source);
        assert!(
            refusal.contains("is a floating-point operation"),
            "{opcode:?}: {refusal}"
        );
    }
}

/// A copy between a 32- and a 64-bit register defines only its low 32 bits:
/// returning all 64 bits of `mov r64, r32` where the source zero-extends is
/// refuted (a 32-bit copy, `MovRR32`, zero-extends and is not), and a mixed
/// copy of a private address makes no claim.
#[test]
fn a_mixed_width_copy_defines_only_its_low_32_bits() {
    let mut builder = ModuleBuilder::new("x86_source_bound_body_slice15_mixed");
    let signature = builder.add_func_type(vec![Ty::U32], vec![Ty::U64]);
    let mut f = builder.function("s15_widen", signature);
    let entry = f.create_block();
    let x = f.add_block_param(entry, Ty::U32);
    f.switch_to_block(entry);
    let wide = f.zext(Ty::U32, Ty::U64, x);
    f.ret(vec![wide]);
    f.build();
    let source = trust_cg_lower::translate_module_for_arch_with_tls_with_license(
        &builder.build().expect("ModuleBuilder::build: test fixture"),
        trust_cg_lower::GuardCarrierArch::X86_64,
        trust_cg_lower::TlsDialect::default(),
        &crate::license_test_support::permit_unlicensed(),
    )
    .expect("translates")
    .into_iter()
    .map(|(function, _)| function)
    .find(|function| function.name == "s15_widen")
    .expect("translated");
    let machine = select(&source, X86CallAbi::SystemV);
    assert!(theorem_holds(&owner(&source, &machine, "s15_widen")));
    // A 64-bit copy of the 32-bit parameter into RAX just before the return.
    let mut mixed = machine.clone();
    let parameter = rows(&mixed)
        .into_iter()
        .map(|(ordinal, _, _)| ordinal)
        .find(|ordinal| {
            let row = inst(&mixed, *ordinal);
            row.opcode == X86Opcode::MovRR32 && row.operands[1] == preg(GPR32_ALIAS_BASE + RDI)
        })
        .expect("the parameter copy");
    let narrow = inst(&mixed, parameter).operands[0].clone();
    let ret = find(&mixed, X86Opcode::Ret)[0];
    insert_at(
        &mut mixed,
        ret,
        X86ISelInst::new(X86Opcode::MovRR, vec![preg(RAX), narrow]),
    );
    let theorem = theorem_without_affine_refusal(&source, &mixed, SYSV)
        .unwrap_or_else(|refusal| panic!("{refusal}\n{}", describe(&mixed)));
    assert!(theorem_refuted(&theorem), "{}", describe(&mixed));
    // Likewise an ALU row of mixed widths: a 64-bit sum computed into a
    // 32-bit register and returned whole.
    let (source, mut machine) = pair(Shape::Add);
    let add = find(&machine, X86Opcode::AddRR)[0];
    let narrow = O::VReg(VReg::new(9_400, RegClass::Gpr32));
    let sum = std::mem::replace(&mut inst_mut(&mut machine, add).operands[0], narrow.clone());
    for (ordinal, _, _) in rows(&machine) {
        let row = inst_mut(&mut machine, ordinal);
        if row.opcode == X86Opcode::MovRR && row.operands[1] == sum {
            row.operands[1] = narrow.clone();
        }
    }
    let theorem = theorem_without_affine_refusal(&source, &machine, SYSV)
        .unwrap_or_else(|refusal| panic!("{refusal}\n{}", describe(&machine)));
    assert!(theorem_refuted(&theorem), "{}", describe(&machine));
    // A 64-bit register holding a private address copied into a 32-bit one.
    let (source, mut machine) = slice15_pair(ResidueShape::DerivedLoadReturned);
    let lea = row_where(&machine, |row| row.opcode == X86Opcode::Lea);
    let address = inst(&machine, lea).operands[0].clone();
    insert_at(
        &mut machine,
        lea + 1,
        X86ISelInst::new(
            X86Opcode::MovRR,
            vec![O::VReg(VReg::new(9_500, RegClass::Gpr32)), address],
        ),
    );
    expect_unsupported_naming(&source, &machine, "reads the private stack address");
}

/// An ALU row of mixed widths defines only the low 32 bits of its operation,
/// whatever the 32-bit operand held: `fn(a: u64, b: u32) -> u64 { a + b as
/// u64 }` with the zero extension's copy dropped (`add r64, r64, r32` of the
/// parameter's 32-bit register) is refuted, although the zero-extending
/// 32-bit copy that defined that register left its bits above 31 clear: the
/// REX.W row reads whatever the allocated register holds there, which a
/// 32-bit virtual register does not keep. The selector's own lowering, with
/// the copy, holds.
#[test]
fn a_mixed_width_alu_row_defines_only_its_low_32_bits() {
    let mut builder = ModuleBuilder::new("x86_source_bound_body_slice15_mixed_alu");
    let signature = builder.add_func_type(vec![Ty::U64, Ty::U32], vec![Ty::U64]);
    let mut f = builder.function("s15_add_widened", signature);
    let entry = f.create_block();
    let a = f.add_block_param(entry, Ty::U64);
    let b = f.add_block_param(entry, Ty::U32);
    f.switch_to_block(entry);
    let wide = f.zext(Ty::U32, Ty::U64, b);
    let sum = f.add(Ty::U64, a, wide);
    f.ret(vec![sum]);
    f.build();
    let source = trust_cg_lower::translate_module_for_arch_with_tls_with_license(
        &builder.build().expect("ModuleBuilder::build: test fixture"),
        trust_cg_lower::GuardCarrierArch::X86_64,
        trust_cg_lower::TlsDialect::default(),
        &crate::license_test_support::permit_unlicensed(),
    )
    .expect("translates")
    .into_iter()
    .map(|(function, _)| function)
    .find(|function| function.name == "s15_add_widened")
    .expect("translated");
    let machine = select(&source, X86CallAbi::SystemV);
    assert!(
        theorem_holds(&owner(&source, &machine, "s15_add_widened")),
        "{}",
        describe(&machine)
    );
    // The add reads the 32-bit parameter register directly.
    let mut mixed = machine.clone();
    let parameter = rows(&mixed)
        .into_iter()
        .map(|(ordinal, _, _)| ordinal)
        .find(|ordinal| {
            let row = inst(&mixed, *ordinal);
            row.opcode == X86Opcode::MovRR32 && row.operands[1] == preg(GPR32_ALIAS_BASE + RSI)
        })
        .expect("the 32-bit parameter's copy");
    let narrow = inst(&mixed, parameter).operands[0].clone();
    assert!(matches!(&narrow, O::VReg(v) if v.class == RegClass::Gpr32));
    let add = find(&mixed, X86Opcode::AddRR)[0];
    let operands = &mut inst_mut(&mut mixed, add).operands;
    let last = operands.len() - 1;
    operands[last] = narrow;
    let theorem = theorem_without_affine_refusal(&source, &mixed, SYSV)
        .unwrap_or_else(|refusal| panic!("{refusal}\n{}", describe(&mixed)));
    assert!(theorem_refuted(&theorem), "{}", describe(&mixed));
}

/// A `bool` parameter forwarded as a `bool` argument is observed as the clean
/// 32-bit bool the callee reads, under every caller view walked: forwarding
/// the 32-bit register a psABI caller may leave dirty above bit 7 is refuted
/// (`slice_fifteen_refutations`); the selector's `movzx` of its low byte at
/// entry is not. A function that also returns a `bool` is walked under both
/// views.
#[test]
fn a_forwarded_bool_is_the_clean_32_bit_bool_under_every_caller_view() {
    let (source, machine) = slice15_pair(ResidueShape::ForwardBoolReturn);
    let obligation = owned_plain_theorem(&source, &machine, "ForwardBoolReturn");
    let inputs: Vec<String> = obligation.inputs.iter().map(|(n, _)| n.clone()).collect();
    assert!(
        inputs.iter().any(|n| n == "a0") && inputs.iter().any(|n| n == "z0"),
        "both caller views: {inputs:?}"
    );
    for shape in [ResidueShape::ForwardBool, ResidueShape::ForwardBoolMixed] {
        let (source, machine) = slice15_pair(shape);
        let body = admitted_body(&source).expect("admitted");
        assert!(
            body.paths[0].calls[0]
                .args
                .iter()
                .any(|arg| matches!(arg, CallArg::Scalar(_, Carrier::B1))),
            "{shape:?}"
        );
        assert!(theorem_holds(&owner(
            &source,
            &machine,
            &format!("{shape:?}")
        )));
    }
}

/// A load or store through an address that may derive from an escaped slot
/// observes the escaped slots' contents (a store then leaves each of their
/// bytes as its site's free input), and when the machine lets other slots
/// escape than the source at such an access, no single trace states both:
/// no claim.
#[test]
fn derived_accesses_observe_the_escaped_slots() {
    let body = admitted_body(&slice15_lir(ResidueShape::DerivedLoadReturned)).expect("admitted");
    let reads: Vec<Option<Vec<u32>>> = body.paths[0]
        .accesses
        .iter()
        .map(|access| {
            access
                .slot_reads
                .as_ref()
                .map(|reads| reads.iter().map(|(slot, _)| *slot).collect())
        })
        .collect();
    assert_eq!(reads, vec![Some(vec![0])]);
    let body = admitted_body(&slice15_lir(ResidueShape::DerivedStore)).expect("admitted");
    let store = &body.paths[0].accesses[0];
    assert!(store.store_site.is_some() && store.slot_reads.is_some());
    let reread = body.paths[0]
        .definitions
        .iter()
        .rev()
        .find_map(|definition| match &definition.op {
            SourceOp::StackBytes(bytes) => Some(bytes.clone()),
            _ => None,
        })
        .expect("v read back");
    assert!(
        reread
            .iter()
            .all(|(_, byte)| matches!(byte, Some(SlotByte::AccessStore(0)))),
        "{reread:?}"
    );
    // An access through a parameter, after an escape, observes no slot.
    let mut builder = ModuleBuilder::new("x86_source_bound_body_slice15_sets");
    let ptr_u64 = Ty::PtrMut(Box::new(Ty::U64));
    let ptr_ptr = Ty::PtrMut(Box::new(ptr_u64.clone()));
    let id_ty = builder.add_func_type(vec![ptr_u64.clone()], vec![ptr_u64.clone()]);
    let id = builder.declare_function("id", id_ty);
    let signature = builder.add_func_type(vec![ptr_ptr.clone(), Ty::U64], vec![Ty::U64]);
    let mut f = builder.function("s15_sets", signature);
    let entry = f.create_block();
    let q = f.add_block_param(entry, ptr_ptr.clone());
    let x = f.add_block_param(entry, Ty::U64);
    f.switch_to_block(entry);
    let v = f.alloca(Ty::U64);
    f.store(Ty::U64, v, x);
    let w = f.alloca(Ty::U64);
    f.store(Ty::U64, w, x);
    let p = f.call(id, vec![v]);
    f.store(ptr_u64.clone(), q, w);
    let value = f.load(Ty::U64, p);
    f.ret(vec![value]);
    f.build();
    let source = trust_cg_lower::translate_module_for_arch_with_tls_with_license(
        &builder.build().expect("ModuleBuilder::build: test fixture"),
        trust_cg_lower::GuardCarrierArch::X86_64,
        trust_cg_lower::TlsDialect::default(),
        &crate::license_test_support::permit_unlicensed(),
    )
    .expect("translates")
    .into_iter()
    .map(|(function, _)| function)
    .find(|function| function.name == "s15_sets")
    .expect("translated");
    let body = admitted_body(&source).expect("admitted");
    let accesses = &body.paths[0].accesses;
    assert!(accesses[0].slot_reads.is_none(), "the store through q");
    assert_eq!(
        accesses[1]
            .slot_reads
            .as_ref()
            .map(|reads| reads.iter().map(|(slot, _)| *slot).collect::<Vec<_>>()),
        Some(vec![0, 1]),
        "v escaped to the call, w at the store"
    );
    let mut machine = select(&source, X86CallAbi::SystemV);
    assert!(theorem_holds(&owner(&source, &machine, "s15_sets")));
    // The machine stores the parameter where the source stores `&w`: w never
    // escapes there, so the escaped slots at the derived load differ.
    let store = rows(&machine)
        .into_iter()
        .map(|(ordinal, _, _)| ordinal)
        .rfind(|ordinal| {
            let row = inst(&machine, *ordinal);
            row.opcode == X86Opcode::MovMR
                && !matches!(&row.operands[0], O::MemAddr { base, .. } if matches!(**base, O::StackSlot(_)))
        })
        .expect("the store of &w");
    let parameter = rows(&machine)
        .into_iter()
        .map(|(ordinal, _, _)| ordinal)
        .find_map(|ordinal| {
            let row = inst(&machine, ordinal);
            (row.opcode == X86Opcode::MovRR && row.operands[1] == preg(RSI))
                .then(|| row.operands[0].clone())
        })
        .expect("x's copy");
    inst_mut(&mut machine, store).operands[1] = parameter;
    expect_unsupported_naming(
        &source,
        &machine,
        "the private stack slots escaped at access",
    );
}

/// The verify-owned placement of `I128` parameters and arguments past the
/// integer registers ([`parameter_locations`], [`stack_arguments`]: two
/// eightbytes, the first 16-byte aligned, a later scalar still taking a
/// register left over) agrees with the selector's: its formal-argument
/// bindings and stack reads, and the outgoing stores before each call.
#[test]
fn the_verify_owned_i128_stack_placement_agrees_with_the_selector() {
    let signatures: Vec<Vec<Ty>> = vec![
        vec![Ty::U64, Ty::U128, Ty::U128, Ty::U128],
        vec![Ty::U64, Ty::U128, Ty::U128, Ty::U128, Ty::U64],
        vec![Ty::U64, Ty::U128, Ty::U128, Ty::U128, Ty::U128],
        vec![Ty::U128, Ty::U128, Ty::U128, Ty::U64, Ty::U128],
        vec![Ty::U128, Ty::U128, Ty::U128, Ty::U64, Ty::U64, Ty::U128],
        vec![Ty::U64; 7].into_iter().chain([Ty::U128]).collect(),
    ];
    for (n, params) in signatures.into_iter().enumerate() {
        let mut builder = ModuleBuilder::new("x86_source_bound_body_slice15_placement");
        let callee_ty = builder.add_func_type(params.clone(), vec![]);
        let callee = builder.declare_function("callee", callee_ty);
        let signature = builder.add_func_type(params.clone(), vec![]);
        let name = format!("s15_placement_{n}");
        let mut f = builder.function(name.clone(), signature);
        let entry = f.create_block();
        let args: Vec<_> = params
            .iter()
            .map(|ty| f.add_block_param(entry, ty.clone()))
            .collect();
        f.switch_to_block(entry);
        f.call_void(callee, args);
        f.ret(vec![]);
        f.build();
        let module = builder.build().expect("ModuleBuilder::build: test fixture");
        let source = trust_cg_lower::translate_module_for_arch_with_tls_with_license(
            &module,
            trust_cg_lower::GuardCarrierArch::X86_64,
            trust_cg_lower::TlsDialect::default(),
            &crate::license_test_support::permit_unlicensed(),
        )
        .expect("translates")
        .into_iter()
        .map(|(function, _)| function)
        .find(|function| function.name == name)
        .expect("translated");
        let machine = select(&source, X86CallAbi::SystemV);
        // Incoming: the selector's recorded stack eightbyte of each scalar
        // parameter, and the 8-byte reads of every stack eightbyte.
        let mut selector: Vec<(u32, i32)> = machine
            .formal_argument_bindings()
            .sorted_entries()
            .into_iter()
            .filter_map(|(_, binding)| match binding.location {
                trust_cg_lower::x86_64_isel::X86FormalArgumentLocation::IncomingStack {
                    rbp_disp,
                } => Some((binding.param_index, rbp_disp)),
                _ => None,
            })
            .collect();
        let mut wide_reads: Vec<i32> = rows(&machine)
            .into_iter()
            .filter_map(|(ordinal, _, _)| {
                let row = inst(&machine, ordinal);
                match row.operands.get(1) {
                    Some(O::MemAddr { base, disp })
                        if **base == preg(RBP) && row.opcode == X86Opcode::MovRM =>
                    {
                        Some(*disp)
                    }
                    _ => None,
                }
            })
            .collect();
        let frame = admitted_frame(&source).expect("admitted frame");
        let mut verify_owned: Vec<(u32, i32)> = Vec::new();
        let mut verify_wide: Vec<i32> = Vec::new();
        for (i, param) in frame.params.iter().enumerate() {
            let eightbytes = param.stack_eightbytes();
            match (param.abi.scalar(), eightbytes.as_slice()) {
                (Some(Carrier::I128), halves @ [_, _]) => verify_wide.extend(halves),
                (_, [disp]) => {
                    verify_owned.push((i as u32, *disp));
                    if param.abi == ParamAbi::Scalar(Carrier::I64) {
                        verify_wide.push(*disp);
                    }
                }
                _ => {}
            }
        }
        selector.sort_unstable();
        verify_owned.sort_unstable();
        wide_reads.sort_unstable();
        verify_wide.sort_unstable();
        assert!(!verify_wide.is_empty(), "{name}: a stack parameter");
        assert_eq!(verify_owned, selector, "{name}: scalar stack parameters");
        assert_eq!(verify_wide, wide_reads, "{name}: 8-byte stack reads");
        // Outgoing: the call's stack arguments, as offsets the selector
        // stores to.
        let body = admitted_body(&source).expect("admitted");
        let call = &body.paths[0].calls[0];
        let mut verify_out: Vec<i32> = call
            .stack_args
            .iter()
            .flat_map(|(arg, offset)| match arg {
                CallArg::Scalar(_, Carrier::I128) => vec![*offset, offset + 8],
                _ => vec![*offset],
            })
            .collect();
        let mut stored: Vec<i32> = rows(&machine)
            .into_iter()
            .filter_map(
                |(ordinal, _, _)| match inst(&machine, ordinal).operands.first() {
                    Some(O::MemAddr { base, disp }) if **base == preg(RSP) => Some(*disp),
                    _ => None,
                },
            )
            .collect();
        verify_out.sort_unstable();
        stored.sort_unstable();
        assert_eq!(verify_out, stored, "{name}: outgoing stack arguments");
        assert!(
            theorem_holds(&owner(&source, &machine, &name)),
            "{name}\n{}",
            describe(&machine)
        );
    }
}

// ---------------------------------------------------------------------------
// Refutations
// ---------------------------------------------------------------------------

/// The walk ordinal of the row that defines the first parameter at entry
/// (a `bool`'s `movzx`).
fn entry_bool_extension(machine: &X86ISelFunction) -> usize {
    row_where(machine, |row| {
        row.opcode == X86Opcode::Movzx
            && row
                .operands
                .get(1)
                .and_then(gpr)
                .is_some_and(|reg| matches!(reg.root, Root::Physical(_)))
    })
}

/// Wrong lowerings the Rust walk cannot judge, each one refuted by the
/// theorem on samples (and replayed to a counterexample on the qualification
/// host).
pub(crate) fn slice_fifteen_refutations() -> Vec<(&'static str, Function, X86ISelFunction)> {
    use ResidueShape::*;
    let mut cases = Vec::new();
    // ConstF32: another constant's bits in the pool.
    let (source, mut machine) = slice15_pair(ConstF32);
    machine.const_pool_entries[0].data = 1.25f32.to_le_bytes().to_vec();
    cases.push(("ConstF32/other-constant", source, machine));
    // ConstF64Nan: a NaN of another payload.
    let (source, mut machine) = slice15_pair(ConstF64Nan);
    machine.const_pool_entries[0].data = 0x7ff8_0000_0000_0001u64.to_le_bytes().to_vec();
    cases.push(("ConstF64Nan/other-payload", source, machine));
    // NegF32: the mask flips another bit.
    let (source, mut machine) = slice15_pair(NegF32);
    machine.const_pool_entries[0].data = 0x4000_0000u32.to_le_bytes().to_vec();
    cases.push(("NegF32/other-bit", source, machine));
    // AbsF64: the magnitude mask XORed instead of ANDed.
    let (source, mut machine) = slice15_pair(AbsF64);
    let and = row_where(&machine, |row| row.opcode == X86Opcode::Andpd);
    inst_mut(&mut machine, and).opcode = X86Opcode::Pxor;
    cases.push(("AbsF64/xor-for-and", source, machine));
    // NegF64: the sign mask ANDed instead of XORed.
    let (source, mut machine) = slice15_pair(NegF64);
    let xor = row_where(&machine, |row| row.opcode == X86Opcode::Pxor);
    inst_mut(&mut machine, xor).opcode = X86Opcode::Andpd;
    cases.push(("NegF64/and-for-xor", source, machine));
    // NegAbsBits: the magnitude dropped (the negation's bits returned).
    let (source, mut machine) = slice15_pair(NegAbsBits);
    let and = row_where(&machine, |row| row.opcode == X86Opcode::Andpd);
    let operands = inst(&machine, and).operands.clone();
    *inst_mut(&mut machine, and) = X86ISelInst::new(
        X86Opcode::MovsdRR,
        vec![operands[0].clone(), operands[1].clone()],
    );
    cases.push(("NegAbsBits/abs-dropped", source, machine));
    // ThreeBytes: the argument's third byte never assembled into EDI.
    let (source, mut machine) = slice15_pair(ThreeBytes);
    let or = row_where(&machine, |row| {
        row.opcode == X86Opcode::OrRR && row.operands.first() == Some(&preg(GPR32_ALIAS_BASE + RDI))
    });
    remove_at(&mut machine, or);
    cases.push(("ThreeBytes/third-byte-dropped", source, machine));
    // ForwardBool / ForwardBoolMixed: the parameter's 32-bit register
    // forwarded without the zero extension of its low byte.
    for (label, shape) in [
        ("ForwardBool/raw-forward", ForwardBool),
        ("ForwardBoolMixed/raw-forward", ForwardBoolMixed),
    ] {
        let (source, mut machine) = slice15_pair(shape);
        let extension = entry_bool_extension(&machine);
        inst_mut(&mut machine, extension).opcode = X86Opcode::MovRR32;
        cases.push((label, source, machine));
    }
    // DerivedLoadReturned: `v` overwritten before the load through the
    // returned pointer, which may read it.
    let (source, mut machine) = slice15_pair(DerivedLoadReturned);
    let load = load_after_call(&machine, 0);
    let seven = fresh(9_300);
    insert_at(
        &mut machine,
        load,
        X86ISelInst::new(X86Opcode::MovRI, vec![seven.clone(), O::Imm(7)]),
    );
    insert_at(
        &mut machine,
        load + 1,
        X86ISelInst::new(
            X86Opcode::MovMR,
            vec![
                O::MemAddr {
                    base: Box::new(O::StackSlot(0)),
                    disp: 0,
                },
                seven,
            ],
        ),
    );
    cases.push((
        "DerivedLoadReturned/slot-written-before-load",
        source,
        machine,
    ));
    // DerivedStore: `v` kept in a register across the store through the
    // pointer, which may have written it.
    let (source, mut machine) = slice15_pair(DerivedStore);
    let reload = rows(&machine)
        .into_iter()
        .map(|(ordinal, _, _)| ordinal)
        .rfind(|ordinal| {
            let row = inst(&machine, *ordinal);
            row.opcode == X86Opcode::MovRM
                && matches!(&row.operands[1], O::MemAddr { base, .. } if matches!(**base, O::StackSlot(0)) || matches!(**base, O::VReg(_)))
        })
        .expect("v's reload");
    let destination = inst(&machine, reload).operands[0].clone();
    let x = rows(&machine)
        .into_iter()
        .map(|(ordinal, _, _)| ordinal)
        .find_map(|ordinal| {
            let row = inst(&machine, ordinal);
            (row.opcode == X86Opcode::MovRR && row.operands[1] == preg(RDI))
                .then(|| row.operands[0].clone())
        })
        .expect("x's copy");
    *inst_mut(&mut machine, reload) = X86ISelInst::new(X86Opcode::MovRR, vec![destination, x]);
    cases.push(("DerivedStore/kept-across-store", source, machine));
    // DerivedLoadOffset: the entry read 8 bytes further.
    let (source, mut machine) = slice15_pair(DerivedLoadOffset);
    let load = rows(&machine)
        .into_iter()
        .map(|(ordinal, _, _)| ordinal)
        .rfind(|ordinal| inst(&machine, *ordinal).opcode == X86Opcode::MovRM)
        .expect("the derived load");
    if let O::MemAddr { disp, .. } = &mut inst_mut(&mut machine, load).operands[1] {
        *disp += 8;
    }
    cases.push(("DerivedLoadOffset/other-offset", source, machine));
    // StackParamI128: the two stack eightbytes read the other way round.
    let (source, mut machine) = slice15_pair(StackParamI128);
    let reads: Vec<usize> = rows(&machine)
        .into_iter()
        .map(|(ordinal, _, _)| ordinal)
        .filter(|ordinal| through(inst(&machine, *ordinal), RBP))
        .collect();
    for (row, disp) in reads.iter().zip([24, 16]) {
        if let O::MemAddr { disp: d, .. } = &mut inst_mut(&mut machine, *row).operands[1] {
            *d = disp;
        }
    }
    cases.push(("StackParamI128/swapped-eightbytes", source, machine));
    // StackArgI128: the two halves stored the other way round.
    let (source, mut machine) = slice15_pair(StackArgI128);
    let stores: Vec<usize> = rows(&machine)
        .into_iter()
        .map(|(ordinal, _, _)| ordinal)
        .filter(|ordinal| {
            let row = inst(&machine, *ordinal);
            row.opcode == X86Opcode::MovMR && through(row, RSP)
        })
        .collect();
    for (row, disp) in stores.iter().zip([8, 0]) {
        if let O::MemAddr { disp: d, .. } = &mut inst_mut(&mut machine, *row).operands[0] {
            *d = disp;
        }
    }
    cases.push(("StackArgI128/swapped-halves", source, machine));
    cases
}

#[test]
fn every_slice_fifteen_refutation_is_refuted_on_samples() {
    for (label, source, machine) in slice_fifteen_refutations() {
        let theorem = theorem_without_affine_refusal(&source, &machine, SYSV)
            .unwrap_or_else(|refusal| panic!("{label}: {refusal}\n{}", describe(&machine)));
        assert!(theorem_refuted(&theorem), "{label}\n{}", describe(&machine));
    }
}

/// The real x86 optimizer's output at O1, O2 and O3 for every slice-15
/// fixture: the owner never names a mismatch for a correct lowering, and
/// every theorem it builds holds.
#[test]
fn optimized_slice_fifteen_fixtures_are_judged_without_false_mismatches() {
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
        for shape in all_slice_fifteen_shapes() {
            let (source, mut machine) = slice15_pair(shape);
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

const SLICE_FIFTEEN_SNAPSHOT_SHA256: &str =
    "7d037264e29d7784520ef3637b1a249ba054297eff203fbe88f76366d2780db9";

#[test]
fn slice_fifteen_smt2_is_canonical_per_shape() {
    use sha2::{Digest, Sha256};
    const GOLDEN: &str =
        include_str!("../tests/fixtures/x86_source_bound_body/slice15_snapshots.smt2");
    let mut rendered = String::new();
    for shape in SLICE_FIFTEEN {
        let (source, machine) = slice15_pair(shape);
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
            .join("tests/fixtures/x86_source_bound_body/slice15_snapshots.smt2");
        std::fs::write(&path, &rendered).unwrap();
        panic!(
            "rewrote {}; review its diff, set SLICE_FIFTEEN_SNAPSHOT_SHA256 to {:x} and re-run \
             without TCG_X86_BODY_SNAPSHOT_WRITE",
            path.display(),
            Sha256::digest(rendered.as_bytes())
        );
    }
    assert_eq!(
        format!("{:x}", Sha256::digest(GOLDEN.as_bytes())),
        SLICE_FIFTEEN_SNAPSHOT_SHA256,
        "the golden file changed without the reviewed digest pin"
    );
    assert_eq!(rendered, GOLDEN, "slice-15 snapshots drifted");
}
