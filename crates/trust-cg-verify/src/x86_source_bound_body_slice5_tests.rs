// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Slice 5 of the x86-64 source-bound body theorem: scalar pairs (a two-lane
//! RAX:RDX return, pair parameters and pair call results), symbol addresses
//! (`GlobalRef`/`ExternRef`) and branch-free compares (`Icmp` to a `bool`).
//!
//! Fixtures are real: LIR from the trust-ir adapter, the machine stream from
//! the real x86-64 instruction selector (`super::select`). Negative controls
//! mutate that stream and must end as a typed mismatch, a refuted theorem or
//! an unsupported (uncredited) body, never as Formal credit.
//!
//! Every test here runs without a solver, and the soundness check runs them
//! all (the `x86_source_bound_body::tests::slice5::` library gate). The
//! replay on AY and Clean and the verifier-credit tests are in
//! `slice5_qualification`.

use super::*;
use trust_ir::value::GlobalId;
use trust_ir::{Constant, ICmpOp, Linkage};

/// Slice-5 fixture shapes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum PairShape {
    // ---- (a) scalar pairs
    /// `(b, a)`: two u64 lanes, swapped.
    PairSwap,
    /// `(a, b)` of `(u64, u32)`: an EDX lane.
    PairU32Lane,
    /// `(a, b)` of `(u64, u8)`: a DL lane carried in a 32-bit value.
    PairU8Lane,
    /// `(a, b)` of `(u64, bool)`: a bool lane (the backend's clean EDX bool).
    PairBoolLane,
    /// `(1, 2)`: two constant lanes.
    PairConst,
    /// `(p + 1, len - 1)`: a slice fat pointer in, one out (`&s[1..]`).
    PairSliceTail,
    /// `len` of a slice passed after four u64 parameters: the pair's lanes
    /// are R8 and R9, the last two argument registers.
    PairParamLast,
    /// `let (a, b) = g2(x); a + b`: a call returning a pair.
    PairCallSum,
    /// `g2(x)` returned as is: both lanes forwarded.
    PairCallForward,
    /// `let (_, b) = gn(x); b as u64`: a DL lane of a call result.
    PairCallNarrow,
    /// `hp(p, len)`: a pair passed as two register arguments.
    PairCallArgs,
    /// `let (_, b) = gb(x); b as u64`: a bool lane in DL, bit 0 alone.
    PairCallBool,
    /// `let (b, _) = gf(x); b as u64`: a bool lane in AL, bit 0 alone.
    PairCallBoolFirst,
    /// `gb(x)` returned as is: a forwarded bool lane.
    PairCallBoolForward,
    /// `bg(gb(x).1)`: a bool lane passed as a bool argument.
    PairCallBoolArg,
    /// `*p = gb(x).1`: a stored bool lane.
    PairCallBoolStore,
    // ---- (b) symbol addresses
    /// `&G` (a defined global: `GlobalRef`, `lea r, [rip + G]`).
    GlobalAddr,
    /// `G` (a load through the global's address).
    GlobalLoad,
    /// `G = v` (a store through it).
    GlobalStore,
    /// `(&G).second`: the global's address plus a field offset.
    GlobalField,
    /// `(&A, &B)`: two symbols in the two return lanes.
    TwoGlobals,
    /// `&E` (an external data import: `ExternRef`, a GOT load).
    ExternAddr,
    /// `E` (a load through the imported address).
    ExternLoad,
    /// `sink(&MSG, 35)` then a trap: the `core` panic helpers' shape.
    PanicMessage,
    // ---- (c) branch-free compares
    CmpEqU64,
    CmpNeU64,
    CmpUltU64,
    CmpSltI64,
    CmpUgeU32,
    CmpSgtI32,
    CmpUleU16,
    CmpSleI16,
    CmpUgtU8,
    CmpSgeI8,
    /// `x == 5`: a constant operand.
    CmpEqConst,
    /// `a == b` of two bools.
    CmpBoolEq,
    /// `(a < b) as u64`.
    CmpZext,
    /// `*p = a < b`: a stored bool.
    CmpStore,
    /// `bg(a < b)`: a bool call argument.
    CmpCallArg,
    /// `(a < b, a)`: a compare in a pair lane.
    CmpPairLane,
}

/// Every slice-5 shape whose real selection the owner admits and whose
/// theorem holds ([`every_admitted_slice_five_fixture_is_qualified`] checks
/// that none is left out).
pub(crate) const SLICE_FIVE: [PairShape; 40] = [
    PairShape::PairSwap,
    PairShape::PairU32Lane,
    PairShape::PairU8Lane,
    PairShape::PairBoolLane,
    PairShape::PairConst,
    PairShape::PairSliceTail,
    PairShape::PairParamLast,
    PairShape::PairCallSum,
    PairShape::PairCallForward,
    PairShape::PairCallNarrow,
    PairShape::PairCallArgs,
    PairShape::PairCallBool,
    PairShape::PairCallBoolFirst,
    PairShape::PairCallBoolForward,
    PairShape::PairCallBoolArg,
    PairShape::PairCallBoolStore,
    PairShape::GlobalAddr,
    PairShape::GlobalLoad,
    PairShape::GlobalStore,
    PairShape::GlobalField,
    PairShape::TwoGlobals,
    PairShape::ExternAddr,
    PairShape::ExternLoad,
    PairShape::PanicMessage,
    PairShape::CmpEqU64,
    PairShape::CmpNeU64,
    PairShape::CmpUltU64,
    PairShape::CmpSltI64,
    PairShape::CmpUgeU32,
    PairShape::CmpSgtI32,
    PairShape::CmpUleU16,
    PairShape::CmpSleI16,
    PairShape::CmpUgtU8,
    PairShape::CmpSgeI8,
    PairShape::CmpEqConst,
    PairShape::CmpBoolEq,
    PairShape::CmpZext,
    PairShape::CmpStore,
    PairShape::CmpCallArg,
    PairShape::CmpPairLane,
];

impl PairShape {
    fn name(self) -> String {
        let name = format!("{self:?}");
        let mut snake = String::from("s5_");
        for (i, c) in name.chars().enumerate() {
            if c.is_ascii_uppercase() && i > 0 {
                snake.push('_');
            }
            snake.push(c.to_ascii_lowercase());
        }
        snake
    }
}

/// Global ids of the fixture module (in `add_global` order).
const G: u32 = 0;
const A: u32 = 1;
const B: u32 = 2;
const MSG: u32 = 3;
const EXT: u32 = 4;

/// The LIR the trust-ir adapter produces for a slice-5 shape.
pub(crate) fn slice5_lir(shape: PairShape) -> Function {
    use PairShape::*;
    let mut builder = ModuleBuilder::new("x86_source_bound_body_slice5");
    let global = |name: &str, ty: Ty, defined: bool| trust_ir::Global {
        name: name.into(),
        ty,
        mutable: true,
        initializer: defined.then_some(Constant::Int(0)),
        linkage: Linkage::External,
        tls: None,
        align: None,
        section: None,
        visibility: Default::default(),
        retained: false,
    };
    let pair_ty = Ty::Struct(
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
    // A struct global's initializer is a constant of its type: one integer
    // per field (trust-ir admission refuses a scalar for a struct).
    let mut pair_global = global("s5_g", pair_ty, true);
    pair_global.initializer = Some(Constant::Aggregate(vec![Constant::Int(0); 2]));
    builder.add_global(pair_global);
    builder.add_global(global("s5_a", Ty::U64, true));
    builder.add_global(global("s5_b", Ty::U64, true));
    builder.add_global(global("s5_msg", Ty::U64, true));
    builder.add_global(global("s5_ext", Ty::U64, false));
    let u64s = |n: usize| vec![Ty::U64; n];
    let bytes = Ty::PtrConst(Box::new(Ty::U8));
    let g2_ty = builder.add_func_type(u64s(1), u64s(2));
    let g2 = builder.declare_function("g2", g2_ty);
    let gn_ty = builder.add_func_type(u64s(1), vec![Ty::U64, Ty::U8]);
    let gn = builder.declare_function("gn", gn_ty);
    let hp_ty = builder.add_func_type(vec![bytes.clone(), Ty::Usize], u64s(1));
    let hp = builder.declare_function("hp", hp_ty);
    let sink_ty = builder.add_func_type(vec![bytes.clone(), Ty::Usize], vec![]);
    let sink = builder.declare_function("sink", sink_ty);
    let bg_ty = builder.add_func_type(vec![Ty::Bool], u64s(1));
    let bg = builder.declare_function("bg", bg_ty);
    let gb_ty = builder.add_func_type(u64s(1), vec![Ty::U64, Ty::Bool]);
    let gb = builder.declare_function("gb", gb_ty);
    let gf_ty = builder.add_func_type(u64s(1), vec![Ty::Bool, Ty::U64]);
    let gf = builder.declare_function("gf", gf_ty);
    let compare = |shape: PairShape| -> Option<(ICmpOp, Ty)> {
        Some(match shape {
            CmpEqU64 | CmpZext | CmpStore | CmpCallArg | CmpPairLane => (ICmpOp::Eq, Ty::U64),
            CmpNeU64 => (ICmpOp::Ne, Ty::U64),
            CmpUltU64 => (ICmpOp::Ult, Ty::U64),
            CmpSltI64 => (ICmpOp::Slt, Ty::I64),
            CmpUgeU32 => (ICmpOp::Uge, Ty::U32),
            CmpSgtI32 => (ICmpOp::Sgt, Ty::I32),
            CmpUleU16 => (ICmpOp::Ule, Ty::U16),
            CmpSleI16 => (ICmpOp::Sle, Ty::I16),
            CmpUgtU8 => (ICmpOp::Ugt, Ty::U8),
            CmpSgeI8 => (ICmpOp::Sge, Ty::I8),
            CmpBoolEq => (ICmpOp::Eq, Ty::Bool),
            _ => return None,
        })
    };
    let (params, results): (Vec<Ty>, Vec<Ty>) = match shape {
        PairSwap => (u64s(2), u64s(2)),
        PairU32Lane => (vec![Ty::U64, Ty::U32], vec![Ty::U64, Ty::U32]),
        PairU8Lane => (vec![Ty::U64, Ty::U8], vec![Ty::U64, Ty::U8]),
        PairBoolLane => (vec![Ty::U64, Ty::Bool], vec![Ty::U64, Ty::Bool]),
        PairConst => (vec![], u64s(2)),
        PairSliceTail => (
            vec![bytes.clone(), Ty::Usize],
            vec![bytes.clone(), Ty::Usize],
        ),
        PairParamLast => {
            let mut params = u64s(4);
            params.extend([bytes.clone(), Ty::Usize]);
            (params, vec![Ty::Usize])
        }
        PairCallSum | PairCallNarrow => (u64s(1), u64s(1)),
        PairCallForward => (u64s(1), u64s(2)),
        PairCallArgs => (vec![bytes.clone(), Ty::Usize], u64s(1)),
        PairCallBool | PairCallBoolFirst | PairCallBoolArg => (u64s(1), u64s(1)),
        PairCallBoolForward => (u64s(1), vec![Ty::U64, Ty::Bool]),
        PairCallBoolStore => (vec![Ty::PtrMut(Box::new(Ty::Bool)), Ty::U64], vec![]),
        GlobalAddr | ExternAddr => (vec![], vec![Ty::PtrConst(Box::new(Ty::U64))]),
        GlobalLoad | GlobalField | ExternLoad => (vec![], u64s(1)),
        GlobalStore => (u64s(1), vec![]),
        TwoGlobals => (vec![], vec![Ty::PtrConst(Box::new(Ty::U64)); 2]),
        PanicMessage => (vec![], vec![]),
        CmpEqConst => (u64s(1), vec![Ty::Bool]),
        CmpZext => (u64s(2), u64s(1)),
        CmpStore => (
            vec![Ty::PtrMut(Box::new(Ty::Bool)), Ty::U64, Ty::U64],
            vec![],
        ),
        CmpCallArg => (u64s(2), u64s(1)),
        CmpPairLane => (u64s(2), vec![Ty::Bool, Ty::U64]),
        other => {
            let (_, ty) = compare(other).expect("a compare shape");
            (vec![ty.clone(), ty], vec![Ty::Bool])
        }
    };
    let signature = builder.add_func_type(params.clone(), results.clone());
    let mut f = builder.function(shape.name(), signature);
    let entry = f.create_block();
    let a: Vec<_> = params
        .iter()
        .map(|ty| f.add_block_param(entry, ty.clone()))
        .collect();
    f.switch_to_block(entry);
    let values: Option<Vec<trust_ir::ValueId>> = match shape {
        PairSwap => Some(vec![a[1], a[0]]),
        PairU32Lane | PairU8Lane | PairBoolLane => Some(vec![a[0], a[1]]),
        PairConst => {
            let one = f.iconst(Ty::U64, 1);
            let two = f.iconst(Ty::U64, 2);
            Some(vec![one, two])
        }
        PairSliceTail => {
            let tail = f.gep_byte_offset(a[0], 1);
            let one = f.iconst(Ty::Usize, 1);
            let len = f.sub(Ty::Usize, a[1], one);
            Some(vec![tail, len])
        }
        PairParamLast => Some(vec![a[5]]),
        PairCallSum => {
            let [x, y] = f.call_results::<2>(g2, vec![a[0]]);
            Some(vec![f.add(Ty::U64, x, y)])
        }
        PairCallForward => {
            let [x, y] = f.call_results::<2>(g2, vec![a[0]]);
            Some(vec![x, y])
        }
        PairCallNarrow => {
            let [_, byte] = f.call_results::<2>(gn, vec![a[0]]);
            Some(vec![f.zext(Ty::U8, Ty::U64, byte)])
        }
        PairCallArgs => Some(vec![f.call(hp, vec![a[0], a[1]])]),
        PairCallBool => {
            let [_, lane] = f.call_results::<2>(gb, vec![a[0]]);
            Some(vec![f.zext(Ty::Bool, Ty::U64, lane)])
        }
        PairCallBoolFirst => {
            let [lane, _] = f.call_results::<2>(gf, vec![a[0]]);
            Some(vec![f.zext(Ty::Bool, Ty::U64, lane)])
        }
        PairCallBoolForward => {
            let [x, lane] = f.call_results::<2>(gb, vec![a[0]]);
            Some(vec![x, lane])
        }
        PairCallBoolArg => {
            let [_, lane] = f.call_results::<2>(gb, vec![a[0]]);
            Some(vec![f.call(bg, vec![lane])])
        }
        PairCallBoolStore => {
            let [_, lane] = f.call_results::<2>(gb, vec![a[1]]);
            f.store(Ty::Bool, a[0], lane);
            Some(vec![])
        }
        GlobalAddr => Some(vec![f.global_addr(GlobalId::new(A))]),
        GlobalLoad => {
            let address = f.global_addr(GlobalId::new(A));
            Some(vec![f.load(Ty::U64, address)])
        }
        GlobalStore => {
            let address = f.global_addr(GlobalId::new(A));
            f.store(Ty::U64, address, a[0]);
            Some(vec![])
        }
        GlobalField => {
            let address = f.global_addr(GlobalId::new(G));
            let field = f.gep_byte_offset(address, 8);
            Some(vec![f.load(Ty::U64, field)])
        }
        TwoGlobals => Some(vec![
            f.global_addr(GlobalId::new(A)),
            f.global_addr(GlobalId::new(B)),
        ]),
        ExternAddr => Some(vec![f.global_addr(GlobalId::new(EXT))]),
        ExternLoad => {
            let address = f.global_addr(GlobalId::new(EXT));
            Some(vec![f.load(Ty::U64, address)])
        }
        PanicMessage => {
            let message = f.global_addr(GlobalId::new(MSG));
            let length = f.iconst(Ty::Usize, 35);
            f.call_void(sink, vec![message, length]);
            None
        }
        CmpEqConst => {
            let five = f.iconst(Ty::U64, 5);
            Some(vec![f.icmp(ICmpOp::Eq, Ty::U64, a[0], five)])
        }
        CmpZext => {
            let less = f.icmp(ICmpOp::Ult, Ty::U64, a[0], a[1]);
            Some(vec![f.zext(Ty::Bool, Ty::U64, less)])
        }
        CmpStore => {
            let less = f.icmp(ICmpOp::Ult, Ty::U64, a[1], a[2]);
            f.store(Ty::Bool, a[0], less);
            Some(vec![])
        }
        CmpCallArg => {
            let less = f.icmp(ICmpOp::Ult, Ty::U64, a[0], a[1]);
            Some(vec![f.call(bg, vec![less])])
        }
        CmpPairLane => {
            let less = f.icmp(ICmpOp::Ult, Ty::U64, a[0], a[1]);
            Some(vec![less, a[0]])
        }
        other => {
            let (op, ty) = compare(other).expect("a compare shape");
            Some(vec![f.icmp(op, ty, a[0], a[1])])
        }
    };
    match values {
        Some(values) => f.ret(values),
        None => f.unreachable(),
    }
    f.build();
    let module = builder.build().expect("ModuleBuilder::build: test fixture");
    // The fixture is hand-built and claim-less (`body_gate: None`), which
    // trust-cg refuses by default (roadmap WS7.5, DG-73): state Permit through
    // the parent module's helper.
    trust_cg_lower::translate_module_for_arch_with_tls_with_license(
        &module,
        trust_cg_lower::GuardCarrierArch::X86_64,
        trust_cg_lower::TlsDialect::default(),
        &permit_unlicensed(),
    )
    .unwrap_or_else(|error| panic!("{shape:?}: fixture translates: {error:?}"))
    .into_iter()
    .map(|(function, _)| function)
    .find(|function| function.name == shape.name())
    .unwrap_or_else(|| panic!("{shape:?}: no translated function"))
}

pub(crate) fn slice5_pair(shape: PairShape) -> (Function, X86ISelFunction) {
    let source = slice5_lir(shape);
    let machine = select(&source, X86CallAbi::SystemV);
    (source, machine)
}

pub(super) fn describe(machine: &X86ISelFunction) -> String {
    let mut text = String::new();
    for (ordinal, block, index) in rows(machine) {
        let inst = &machine.blocks[&block].insts[index];
        text.push_str(&format!(
            "  [{ordinal}] {:?} {:?}{}{}\n",
            inst.opcode,
            inst.operands,
            if inst.call_arg_regs.is_empty() {
                String::new()
            } else {
                format!(" args={:?}", inst.call_arg_regs)
            },
            match &inst.call_result_regs {
                Some(results) if inst.opcode == X86Opcode::Call => format!(" results={results:?}"),
                _ => String::new(),
            }
        ));
    }
    text
}

/// Walk ordinals of every row whose opcode is `opcode`.
fn rows_with(machine: &X86ISelFunction, opcode: X86Opcode) -> Vec<usize> {
    find(machine, opcode)
}

/// The last row before the first `Ret` that writes the 64-bit root `root`
/// (through any width alias): the return move of that result lane.
fn return_move(machine: &X86ISelFunction, root: u16) -> usize {
    let ret = rows_with(machine, X86Opcode::Ret)[0];
    (0..ret)
        .rev()
        .find(|ordinal| {
            let row = inst(machine, *ordinal);
            !matches!(
                row.opcode,
                X86Opcode::Call | X86Opcode::CmpRR | X86Opcode::CmpRI
            ) && row
                .operands
                .first()
                .and_then(gpr)
                .is_some_and(|reg| reg.root == Root::Physical(root))
        })
        .unwrap_or_else(|| panic!("no return move into root {root}\n{}", describe(machine)))
}

/// Whether the row at `ordinal` defines a register (every bound row except a
/// compare or a store).
fn defines_a_register(machine: &X86ISelFunction, ordinal: usize) -> bool {
    let opcode = inst(machine, ordinal).opcode;
    !matches!(
        opcode,
        X86Opcode::CmpRR
            | X86Opcode::CmpRI
            | X86Opcode::MovMR8
            | X86Opcode::MovMR16
            | X86Opcode::MovMR32
            | X86Opcode::MovMR
    )
}

/// A wrong lowering the owner still binds: the replayed query itself must be
/// refuted (sampled here; the tool-gated qualification replays it on AY).
#[track_caller]
fn theorem_refuted(source: &Function, machine: &X86ISelFunction, what: &str) {
    let theorem = theorem_without_affine_refusal(source, machine, SYSV)
        .unwrap_or_else(|refusal| panic!("{what}: {refusal}\n{}", describe(machine)));
    assert!(
        refuted_on_samples(&theorem) || !holds_at_boundaries(&theorem),
        "{what}: the theorem must refute the wrong lowering\n{}",
        describe(machine)
    );
}

/// The observed items' widths `(source, machine)`.
fn item_widths(obligation: &ProofObligation) -> Vec<(u32, u32)> {
    observable_items(obligation)
        .iter()
        .map(|(source, machine)| (source.bv_width(), machine.bv_width()))
        .collect()
}

/// Every fixture shape, in declaration order.
fn all_slice_five_shapes() -> Vec<PairShape> {
    use PairShape::*;
    let all = SLICE_FIVE.to_vec();
    // Exhaustive: a new shape does not compile until it is listed here.
    for shape in &all {
        match shape {
            PairSwap | PairU32Lane | PairU8Lane | PairBoolLane | PairConst | PairSliceTail
            | PairParamLast | PairCallSum | PairCallForward | PairCallNarrow | PairCallArgs
            | PairCallBool | PairCallBoolFirst | PairCallBoolForward | PairCallBoolArg
            | PairCallBoolStore | GlobalAddr | GlobalLoad | GlobalStore | GlobalField
            | TwoGlobals | ExternAddr | ExternLoad | PanicMessage | CmpEqU64 | CmpNeU64
            | CmpUltU64 | CmpSltI64 | CmpUgeU32 | CmpSgtI32 | CmpUleU16 | CmpSleI16 | CmpUgtU8
            | CmpSgeI8 | CmpEqConst | CmpBoolEq | CmpZext | CmpStore | CmpCallArg | CmpPairLane => {
            }
        }
    }
    all
}

// ---------------------------------------------------------------------------
// Construction (no solver)
// ---------------------------------------------------------------------------

#[test]
fn slice_five_fixtures_have_the_expected_pre_ra_shapes() {
    use X86Opcode::*;
    // A pair returns lane 0 in RAX and lane 1 in RDX.
    let (source, machine) = slice5_pair(PairShape::PairSwap);
    assert_eq!(source.signature.returns, vec![Type::I64, Type::I64]);
    assert_eq!(opcodes(&machine), vec![MovRR, MovRR, MovRR, MovRR, Ret]);
    assert_eq!(inst(&machine, 2).operands[0], preg(RAX));
    assert_eq!(inst(&machine, 3).operands[0], preg(RDX));
    // A u8 lane rides a 32-bit carrier and returns through EDX.
    let (_, machine) = slice5_pair(PairShape::PairU8Lane);
    assert_eq!(
        opcodes(&machine),
        vec![MovRR, MovRR32, Movzx, MovRR, MovRR32, Ret]
    );
    assert_eq!(
        inst(&machine, 4).operands[0],
        O::PReg(trust_cg_ir::x86_64_regs::EDX)
    );
    // A call with a pair result defines RAX (64 bits) and DL (8 bits), and
    // the caller re-extends DL.
    let (_, machine) = slice5_pair(PairShape::PairCallNarrow);
    let call = rows_with(&machine, Call)[0];
    assert_eq!(
        inst(&machine, call).call_result_regs,
        Some(vec![
            X86CallResultReg::new(X86PReg::new(RAX), 64),
            X86CallResultReg::new(X86PReg::new(RDX), 8),
        ])
    );
    assert_eq!(
        inst(&machine, call + 2).operands[1],
        O::PReg(trust_cg_ir::x86_64_regs::DL)
    );
    // A bool lane of a pair call: the same DL metadata, re-extended and then
    // masked to bit 0.
    let (_, machine) = slice5_pair(PairShape::PairCallBool);
    let call = rows_with(&machine, Call)[0];
    assert_eq!(
        inst(&machine, call).call_result_regs,
        Some(vec![
            X86CallResultReg::new(X86PReg::new(RAX), 64),
            X86CallResultReg::new(X86PReg::new(RDX), 8),
        ])
    );
    assert_eq!(
        opcodes(&machine)[call..call + 4],
        [Call, MovRR, Movzx, AndRI]
    );
    assert_eq!(
        inst(&machine, call + 2).operands[1],
        O::PReg(trust_cg_ir::x86_64_regs::DL)
    );
    assert_eq!(inst(&machine, call + 3).operands[2], O::Imm(1));
    // The verify-owned alias table reads DL and DX as RDX's low bits.
    assert_eq!(
        narrow_alias(&O::PReg(trust_cg_ir::x86_64_regs::DL), 8),
        Some(Root::Physical(RDX))
    );
    assert_eq!(
        narrow_alias(&O::PReg(trust_cg_ir::x86_64_regs::DX), 16),
        Some(Root::Physical(RDX))
    );
    // Symbol addresses: `lea r, [rip + G]` for a defined global, `mov r,
    // [rip + E@GOT]` for an imported one.
    let (source, machine) = slice5_pair(PairShape::GlobalAddr);
    assert!(
        source.blocks[&source.entry_block]
            .instructions
            .iter()
            .any(|inst| matches!(&inst.opcode, L::GlobalRef { name } if name == "s5_a"))
    );
    assert_eq!(opcodes(&machine), vec![LeaRip, MovRR, Ret]);
    let (source, machine) = slice5_pair(PairShape::ExternAddr);
    assert!(
        source.blocks[&source.entry_block]
            .instructions
            .iter()
            .any(|inst| matches!(&inst.opcode, L::ExternRef { name } if name == "s5_ext"))
    );
    assert_eq!(opcodes(&machine), vec![MovRipRel, MovRR, Ret]);
    assert_eq!(
        opcodes(&slice5_pair(PairShape::PanicMessage).1),
        vec![LeaRip, MovRI, MovRR, MovRR, Call, Ud2]
    );
    // A compare: CMP, SETcc into a 32-bit register, MOVZX of that byte. A
    // narrow signed compare sign-extends both operands first; a bool
    // compare zero-extends and masks them.
    assert_eq!(
        opcodes(&slice5_pair(PairShape::CmpUltU64).1),
        vec![MovRR, MovRR, CmpRR, Setcc, Movzx, MovRR32, Ret]
    );
    assert_eq!(
        opcodes(&slice5_pair(PairShape::CmpSgeI8).1),
        vec![
            MovRR32, MovRR32, MovsxB, MovsxB, CmpRR, Setcc, Movzx, MovRR32, Ret
        ]
    );
    // (slice 15: each `bool` parameter is the `movzx` of its register's low
    // byte)
    assert_eq!(
        opcodes(&slice5_pair(PairShape::CmpBoolEq).1),
        vec![
            Movzx, Movzx, Movzx, AndRI, Movzx, AndRI, CmpRR, Setcc, Movzx, MovRR32, Ret
        ]
    );
    assert_eq!(
        opcodes(&slice5_pair(PairShape::CmpEqConst).1),
        vec![MovRR, MovRI, CmpRR, Setcc, Movzx, MovRR32, Ret]
    );
    let (_, machine) = slice5_pair(PairShape::CmpSltI64);
    let setcc = rows_with(&machine, Setcc)[0];
    assert_eq!(
        inst(&machine, setcc).operands[1],
        O::CondCode(trust_cg_ir::X86CondCode::L)
    );
}

#[test]
fn owner_builds_for_every_slice_five_shape_and_covers_every_value_row() {
    for shape in SLICE_FIVE {
        let (source, machine) = slice5_pair(shape);
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
        assert_eq!(
            owner
                .call_sites()
                .iter()
                .map(|(_, _, row)| *row)
                .collect::<Vec<_>>(),
            rows_with(&machine, X86Opcode::Call),
            "{shape:?}"
        );
        // Every bound row that defines a register is named once per walk; a
        // compare defines only RFLAGS and a store only memory.
        let walks = if source.signature.returns.contains(&Type::B1)
            && source.signature.params.contains(&Type::B1)
        {
            2
        } else {
            1
        };
        let defining = expected
            .iter()
            .filter(|row| defines_a_register(&machine, **row))
            .count();
        assert_eq!(
            owner.machine_definitions().len(),
            walks * defining,
            "{shape:?}"
        );
        let entries = free_inputs_of(owner.obligation());
        assert_eq!(
            owner_check(&source, &machine, owner.obligation(), &entries),
            Ok(()),
            "{shape:?}"
        );
        assert!(owner.obligation().is_genuinely_proven(), "{shape:?}");
        assert!(source_admits_x86_body_owner(&source, SYSV), "{shape:?}");
    }
}

#[test]
fn slice_five_theorems_hold_on_samples() {
    for shape in SLICE_FIVE {
        let (source, machine) = slice5_pair(shape);
        let owner = source_bound_x86_body(&source, &machine, SYSV).unwrap();
        assert!(holds_on_samples(owner.obligation()), "{shape:?}");
        assert!(holds_at_boundaries(owner.obligation()), "{shape:?}");
    }
    for (label, source, machine) in slice_five_variants() {
        let owner = source_bound_x86_body(&source, &machine, SYSV)
            .unwrap_or_else(|refusal| panic!("{label}: {refusal}"));
        assert!(holds_on_samples(owner.obligation()), "{label}");
        assert!(holds_at_boundaries(owner.obligation()), "{label}");
    }
}

/// The golden, owner, credit and host-qualification tests run over
/// [`SLICE_FIVE`]: every fixture whose real selection the owner admits with
/// a theorem that holds must be in it, so none is silently left out of
/// qualification.
#[test]
fn every_admitted_slice_five_fixture_is_qualified() {
    for shape in all_slice_five_shapes() {
        let (source, machine) = slice5_pair(shape);
        let holds = source_bound_x86_body(&source, &machine, SYSV).is_ok_and(|owner| {
            holds_on_samples(owner.obligation()) && holds_at_boundaries(owner.obligation())
        });
        assert_eq!(
            SLICE_FIVE.contains(&shape),
            holds,
            "{shape:?}: SLICE_FIVE must hold exactly the admitted fixtures whose theorem holds"
        );
    }
}

/// Alternative correct machine bodies for admitted slice-5 sources, qualified
/// exactly like the selector's own output.
pub(crate) fn slice_five_variants() -> Vec<(String, Function, X86ISelFunction)> {
    let mut variants = Vec::new();
    // `x == 5` against an immediate (`cmp r, imm32`); the constant's MovRI
    // stays as a dead row.
    let (source, mut machine) = slice5_pair(PairShape::CmpEqConst);
    let cmp = rows_with(&machine, X86Opcode::CmpRR)[0];
    let lhs = inst(&machine, cmp).operands[0].clone();
    *inst_mut(&mut machine, cmp) = X86ISelInst::new(X86Opcode::CmpRI, vec![lhs, O::Imm(5)]);
    variants.push(("CmpEqConst/CmpRI".into(), source, machine));
    // `a < b` as `b > a`: the operands commuted and the condition mirrored.
    let (source, mut machine) = slice5_pair(PairShape::CmpUltU64);
    let cmp = rows_with(&machine, X86Opcode::CmpRR)[0];
    inst_mut(&mut machine, cmp).operands.swap(0, 1);
    let setcc = rows_with(&machine, X86Opcode::Setcc)[0];
    inst_mut(&mut machine, setcc).operands[1] = O::CondCode(trust_cg_ir::X86CondCode::A);
    variants.push(("CmpUltU64/mirrored".into(), source, machine));
    // `&G + 8` as `lea r, [base + 8]`; the offset constant stays dead.
    let (source, mut machine) = slice5_pair(PairShape::GlobalField);
    let address = rows(&machine)
        .into_iter()
        .map(|(row, _, _)| row)
        .find(|row| super::memory::byte_address_inputs(inst(&machine, *row)).is_some())
        .expect("the global field's byte address");
    let dst = inst(&machine, address).operands[0].clone();
    let base = super::memory::byte_address_inputs(inst(&machine, address))
        .unwrap()
        .0
        .clone();
    *inst_mut(&mut machine, address) = X86ISelInst::new(
        X86Opcode::Lea,
        vec![
            dst,
            O::MemAddr {
                base: Box::new(base),
                disp: 8,
            },
        ],
    );
    variants.push(("GlobalField/Lea".into(), source, machine));
    variants
}

#[test]
fn a_pair_return_observes_both_lanes_at_their_abi_bits() {
    // Two u64 lanes: RAX then RDX, 64 bits each.
    let (source, machine) = slice5_pair(PairShape::PairSwap);
    source_bound_x86_body(&source, &machine, SYSV).unwrap();
    assert_eq!(
        item_widths(&plain_theorem(&source, &machine)),
        vec![(64, 64), (64, 64)]
    );
    // A u32 lane is EDX; a u8 lane is DL.
    let (source, machine) = slice5_pair(PairShape::PairU32Lane);
    source_bound_x86_body(&source, &machine, SYSV).unwrap();
    assert_eq!(
        item_widths(&plain_theorem(&source, &machine)),
        vec![(64, 64), (32, 32)]
    );
    let (source, machine) = slice5_pair(PairShape::PairU8Lane);
    source_bound_x86_body(&source, &machine, SYSV).unwrap();
    assert_eq!(
        item_widths(&plain_theorem(&source, &machine)),
        vec![(64, 64), (8, 8)]
    );
    // A bool lane of a function that takes a bool: the clean-bool walk
    // observes EDX, the psABI walk DL.
    let (source, machine) = slice5_pair(PairShape::PairBoolLane);
    source_bound_x86_body(&source, &machine, SYSV).unwrap();
    assert_eq!(
        item_widths(&plain_theorem(&source, &machine)),
        vec![(64, 64), (32, 32), (64, 64), (8, 8)]
    );
    // A compare in lane 0 of a function that takes no bool: EAX = 0/1.
    let (source, machine) = slice5_pair(PairShape::CmpPairLane);
    source_bound_x86_body(&source, &machine, SYSV).unwrap();
    assert_eq!(
        item_widths(&plain_theorem(&source, &machine)),
        vec![(32, 32), (64, 64)]
    );
    // A pair call's lanes are two free inputs, `r0` (RAX) and `q0` (RDX); the
    // bits of RDX above a u8 lane are `h0`.
    let (source, machine) = slice5_pair(PairShape::PairCallNarrow);
    source_bound_x86_body(&source, &machine, SYSV).unwrap();
    let plain = plain_theorem(&source, &machine);
    let inputs = &plain.inputs;
    for (name, width) in [("r0", 64), ("q0", 8), ("h0", 56)] {
        assert!(
            inputs.contains(&(name.to_owned(), width)),
            "{name}: {inputs:?}"
        );
    }
}

/// A `bool` lane of a pair call defines bit 0 alone: rustc returns a
/// `ScalarPair` as `{ T, i1 }` with no `zeroext`, and an LLVM callee may
/// leave bits 1..7 of the lane's byte set (`(x, transmute::<u8, bool>(x as u8
/// & 1))` returns with `movl %eax, %edx`). The lane is the free input `q0`
/// (or `r0`) of one bit under 63 free bits, so a caller that uses the byte
/// without the selector's mask is refuted, where it relies on it as a
/// return, a zero extension, a bool argument or a stored byte.
#[test]
fn a_bool_lane_of_a_pair_call_defines_bit_zero_alone() {
    for (shape, expected) in [
        (PairShape::PairCallBool, [("r0", 64), ("q0", 1), ("h0", 63)]),
        (
            PairShape::PairCallBoolFirst,
            [("r0", 1), ("g0", 63), ("q0", 64)],
        ),
    ] {
        let (source, machine) = slice5_pair(shape);
        let owner = source_bound_x86_body(&source, &machine, SYSV).unwrap();
        let inputs = &owner.obligation().inputs;
        for (name, width) in expected {
            assert!(
                inputs.contains(&(name.to_owned(), width)),
                "{shape:?} {name}: {inputs:?}"
            );
        }
    }
    for shape in [
        PairShape::PairCallBool,
        PairShape::PairCallBoolFirst,
        PairShape::PairCallBoolForward,
        PairShape::PairCallBoolArg,
        PairShape::PairCallBoolStore,
    ] {
        let (source, mut machine) = slice5_pair(shape);
        let call = rows_with(&machine, X86Opcode::Call)[0];
        let mask = rows_with(&machine, X86Opcode::AndRI)
            .into_iter()
            .find(|row| *row > call)
            .unwrap_or_else(|| panic!("{shape:?}: no lane mask\n{}", describe(&machine)));
        remove_at(&mut machine, mask);
        theorem_refuted(
            &source,
            &machine,
            &format!("{shape:?} without the lane mask"),
        );
    }
}

#[test]
fn wrong_pair_lowerings_are_refused() {
    // Swapped pair halves: RAX gets lane 1 and RDX lane 0. The exact affine
    // evaluation names lane 0, and the theorem refutes it without that check.
    let (source, mut machine) = slice5_pair(PairShape::PairSwap);
    let (rax, rdx) = (return_move(&machine, RAX), return_move(&machine, RDX));
    let (first, second) = (
        inst(&machine, rax).operands[1].clone(),
        inst(&machine, rdx).operands[1].clone(),
    );
    inst_mut(&mut machine, rax).operands[1] = second;
    inst_mut(&mut machine, rdx).operands[1] = first;
    expect_mismatch(&source, &machine, "swapped pair halves", |m| {
        matches!(m, X86BodyMismatch::ReturnValue { lane: 0 })
    });
    theorem_refuted(&source, &machine, "swapped pair halves");
    // Lane 1 wrong alone: RDX holds lane 0 too.
    let (source, mut machine) = slice5_pair(PairShape::PairSwap);
    let (rax, rdx) = (return_move(&machine, RAX), return_move(&machine, RDX));
    let first = inst(&machine, rax).operands[1].clone();
    inst_mut(&mut machine, rdx).operands[1] = first;
    expect_mismatch(&source, &machine, "RDX holds lane 0", |m| {
        matches!(m, X86BodyMismatch::ReturnValue { lane: 1 })
    });
    theorem_refuted(&source, &machine, "RDX holds lane 0");
    // Missing RDX write: nothing defines RDX of a two-parameter function.
    let (source, mut machine) = slice5_pair(PairShape::PairSwap);
    let rdx = return_move(&machine, RDX);
    remove_at(&mut machine, rdx);
    expect_mismatch(&source, &machine, "missing RDX write", |m| {
        *m == X86BodyMismatch::UndefinedReturn { register: "rdx" }
    });
    // Wrong lane width: a u64 lane returned through a 32-bit move, and a u32
    // lane through a 16-bit extension. No affine value exists for either, so
    // only the theorem judges them.
    let (source, mut machine) = slice5_pair(PairShape::PairSwap);
    let rdx = return_move(&machine, RDX);
    inst_mut(&mut machine, rdx).opcode = X86Opcode::MovRR32;
    let owner = source_bound_x86_body(&source, &machine, SYSV)
        .expect("a 32-bit move of a u64 lane has no affine value");
    assert!(
        refuted_on_samples(owner.obligation()),
        "u64 lane through MovRR32"
    );
    let (source, mut machine) = slice5_pair(PairShape::PairU32Lane);
    let edx = return_move(&machine, RDX);
    let lane = inst(&machine, edx).operands[1].clone();
    *inst_mut(&mut machine, edx) = X86ISelInst::new(
        X86Opcode::MovzxW,
        vec![O::PReg(trust_cg_ir::x86_64_regs::EDX), lane],
    );
    theorem_refuted(&source, &machine, "u32 lane through MovzxW");
    // A pair call's lanes returned swapped.
    let (source, mut machine) = slice5_pair(PairShape::PairCallForward);
    let (rax, rdx) = (return_move(&machine, RAX), return_move(&machine, RDX));
    let (first, second) = (
        inst(&machine, rax).operands[1].clone(),
        inst(&machine, rdx).operands[1].clone(),
    );
    inst_mut(&mut machine, rax).operands[1] = second;
    inst_mut(&mut machine, rdx).operands[1] = first;
    theorem_refuted(&source, &machine, "pair call lanes swapped");
    // A pair call whose metadata drops or narrows the RDX lane.
    let (source, mut machine) = slice5_pair(PairShape::PairCallSum);
    let call = rows_with(&machine, X86Opcode::Call)[0];
    inst_mut(&mut machine, call).call_result_regs =
        Some(vec![X86CallResultReg::new(X86PReg::new(RAX), 64)]);
    expect_mismatch(&source, &machine, "RDX lane dropped", |m| {
        matches!(m, X86BodyMismatch::CallMetadata { .. })
    });
    let (source, mut machine) = slice5_pair(PairShape::PairCallSum);
    inst_mut(&mut machine, call).call_result_regs = Some(vec![
        X86CallResultReg::new(X86PReg::new(RAX), 64),
        X86CallResultReg::new(X86PReg::new(RDX), 32),
    ]);
    expect_mismatch(&source, &machine, "RDX lane narrowed", |m| {
        matches!(m, X86BodyMismatch::CallMetadata { .. })
    });
    // Result registers out of the System V order are no scalar pair.
    let (source, mut machine) = slice5_pair(PairShape::PairCallSum);
    inst_mut(&mut machine, call).call_result_regs = Some(vec![
        X86CallResultReg::new(X86PReg::new(RDX), 64),
        X86CallResultReg::new(X86PReg::new(RAX), 64),
    ]);
    expect_unsupported(&source, &machine, "result registers RDX, RAX");
    // Reading RDX after a single-result call: the callee clobbered it.
    let (source, mut machine) = slice5_pair(PairShape::PairCallArgs);
    let call = rows_with(&machine, X86Opcode::Call)[0];
    let copy = call + 1;
    assert_eq!(inst(&machine, copy).operands[1], preg(RAX));
    inst_mut(&mut machine, copy).operands[1] = preg(RDX);
    expect_mismatch(
        &source,
        &machine,
        "RDX read after a one-result call",
        |m| matches!(m, X86BodyMismatch::UndefinedRead { operand, .. } if operand == "rdx"),
    );
    // ... and RCX after a pair call.
    let (source, mut machine) = slice5_pair(PairShape::PairCallSum);
    let call = rows_with(&machine, X86Opcode::Call)[0];
    inst_mut(&mut machine, call + 2).operands[1] = preg(RCX);
    expect_mismatch(
        &source,
        &machine,
        "RCX read after a pair call",
        |m| matches!(m, X86BodyMismatch::UndefinedRead { operand, .. } if operand == "rcx"),
    );
}

#[test]
fn pair_parameters_follow_the_system_v_numbering() {
    // Four u64 parameters, then a slice's two lanes: R8 and R9, the last two
    // argument registers. Reading the length from R8 (the pointer's
    // register) is a wrong numbering of the pair.
    let (source, machine) = slice5_pair(PairShape::PairParamLast);
    assert!(source_bound_x86_body(&source, &machine, SYSV).is_ok());
    let mut wrong = machine.clone();
    let copy = rows(&wrong)
        .into_iter()
        .map(|(ordinal, _, _)| ordinal)
        .find(|ordinal| inst(&wrong, *ordinal).operands.get(1) == Some(&preg(R9)))
        .expect("the length is copied out of R9");
    inst_mut(&mut wrong, copy).operands[1] = preg(R8);
    expect_mismatch(&source, &wrong, "pair lane 1 read from R8", |m| {
        matches!(m, X86BodyMismatch::ReturnValue { lane: 0 })
    });
    theorem_refuted(&source, &wrong, "pair lane 1 read from R8");
    // At register exhaustion (five u64 parameters, then the pair) rustc
    // passes lane 0 in R9 and lane 1 on the stack: the source has a seventh
    // parameter, which no register carries, and stays outside the domain.
    let mut exhausted = source.clone();
    exhausted.signature.params = vec![Type::I64; 7];
    assert!(!source_admits_x86_body_owner(&exhausted, SYSV));
    expect_unsupported(&exhausted, &machine, "a pair lane on the stack");
}

#[test]
fn symbol_addresses_are_one_shared_input_per_symbol_and_form() {
    // `&G` and `&E` read the free inputs `sym0`, shared by the source's
    // reference and the machine's; the theorem constrains nothing else.
    for shape in [PairShape::GlobalAddr, PairShape::ExternAddr] {
        let (source, machine) = slice5_pair(shape);
        let owner = source_bound_x86_body(&source, &machine, SYSV).unwrap();
        // A free input, never a definition: no premise constrains it
        // (`check_definitional` refuses one that would).
        assert!(
            free_inputs_of(owner.obligation()).contains(&("sym0".to_owned(), 64)),
            "{shape:?}"
        );
    }
    let (source, machine) = slice5_pair(PairShape::TwoGlobals);
    let owner = source_bound_x86_body(&source, &machine, SYSV).unwrap();
    let inputs = &owner.obligation().inputs;
    assert!(inputs.contains(&("sym0".to_owned(), 64)) && inputs.contains(&("sym1".to_owned(), 64)));
    // A load through a symbol's address is an incoming-memory access: its
    // address is observed and it reads the paired input `l0`.
    let (source, machine) = slice5_pair(PairShape::GlobalLoad);
    let owner = source_bound_x86_body(&source, &machine, SYSV).unwrap();
    assert_eq!(owner.access_sites().len(), 1);
    assert_eq!(item_widths(owner.obligation()), vec![(64, 64), (64, 64)]);
}

#[test]
fn wrong_symbol_references_are_refused() {
    // Symbols swapped between the two lanes: both are the source's, so only
    // the theorem judges it.
    let (source, mut machine) = slice5_pair(PairShape::TwoGlobals);
    let leas = rows_with(&machine, X86Opcode::LeaRip);
    let (first, second) = (
        inst(&machine, leas[0]).operands[1].clone(),
        inst(&machine, leas[1]).operands[1].clone(),
    );
    inst_mut(&mut machine, leas[0]).operands[1] = second;
    inst_mut(&mut machine, leas[1]).operands[1] = first;
    let owner = source_bound_x86_body(&source, &machine, SYSV)
        .expect("a swap of two referenced symbols is judged by the theorem");
    assert!(refuted_on_samples(owner.obligation()), "symbols swapped");
    // A symbol the source never references.
    let (source, mut machine) = slice5_pair(PairShape::GlobalAddr);
    let lea = rows_with(&machine, X86Opcode::LeaRip)[0];
    inst_mut(&mut machine, lea).operands[1] = O::Symbol("s5_b".into());
    expect_mismatch(
        &source,
        &machine,
        "an unreferenced symbol",
        |m| matches!(m, X86BodyMismatch::Symbol { symbol, .. } if symbol.contains("s5_b")),
    );
    // The right symbol in the other form: a GOT load of a direct reference,
    // and a direct address of a GOT-indirect one (under interposition the
    // two differ).
    let (source, mut machine) = slice5_pair(PairShape::GlobalAddr);
    inst_mut(&mut machine, lea).opcode = X86Opcode::MovRipRel;
    inst_mut(&mut machine, lea).flags = X86Opcode::MovRipRel.default_flags();
    expect_mismatch(&source, &machine, "GOT load of a direct reference", |m| {
        matches!(m, X86BodyMismatch::Symbol { .. })
    });
    let (source, mut machine) = slice5_pair(PairShape::ExternAddr);
    let got = rows_with(&machine, X86Opcode::MovRipRel)[0];
    inst_mut(&mut machine, got).opcode = X86Opcode::LeaRip;
    inst_mut(&mut machine, got).flags = X86Opcode::LeaRip.default_flags();
    expect_mismatch(
        &source,
        &machine,
        "direct address of a GOT reference",
        |m| matches!(m, X86BodyMismatch::Symbol { .. }),
    );
    // A field of the global at the wrong offset (+12 for +8).
    let (source, mut machine) = slice5_pair(PairShape::GlobalField);
    let load = rows_with(&machine, X86Opcode::MovRM)[0];
    if let O::MemAddr { disp, .. } = &mut inst_mut(&mut machine, load).operands[1] {
        *disp = 4;
    }
    theorem_refuted(&source, &machine, "field at +12 for +8");
    // The panic helper passes the wrong length.
    let (source, mut machine) = slice5_pair(PairShape::PanicMessage);
    let length = rows_with(&machine, X86Opcode::MovRI)[0];
    inst_mut(&mut machine, length).operands[1] = O::Imm(34);
    expect_mismatch(&source, &machine, "wrong message length", |m| {
        matches!(
            m,
            X86BodyMismatch::CallArgument {
                call: 0,
                argument: 1
            }
        )
    });
}

/// Operand values at every ordering boundary a compare can split on: zero,
/// one, the sign bits of each width and their neighbours, all ones.
const BOUNDARY_VALUES: [u64; 16] = [
    0,
    1,
    2,
    0x7f,
    0x80,
    0xff,
    0x7fff,
    0x8000,
    0xffff,
    0x7fff_ffff,
    0x8000_0000,
    0xffff_ffff,
    0x7fff_ffff_ffff_ffff,
    0x8000_0000_0000_0000,
    0xffff_ffff_ffff_fffe,
    u64::MAX,
];

/// Every 64-bit constant the obligation mentions (both sides and every
/// premise), in first-seen order.
fn wide_constants(obligation: &ProofObligation) -> Vec<u64> {
    fn walk(expr: &E, constants: &mut Vec<u64>) {
        if let E::BvConst { value, width: 64 } = expr
            && !constants.contains(value)
        {
            constants.push(*value);
        }
        expr.for_each_child(&mut |child| walk(child, constants));
    }
    let mut constants = Vec::new();
    for expr in [&obligation.trust_ir_expr, &obligation.aarch64_expr]
        .into_iter()
        .chain(&obligation.preconditions)
    {
        walk(expr, &mut constants);
    }
    constants
}

/// The operand pairs [`holds_at_boundaries`] tries in the first two entry
/// registers: every pair of [`BOUNDARY_VALUES`], and each extra value
/// against every boundary value in either register. The extra values are
/// each boundary value below 2^32 with bit 32 set, which agrees with it in
/// the low 32 bits alone, and each 64-bit constant of the obligation, alone
/// and with bit 32 or bit 63 flipped. So a u64 operand the machine compares
/// or copies at 32 bits (`cmp edi, 5` for `x == 5`) meets a value that tells
/// the two apart, which random samples almost never do.
fn boundary_pairs(obligation: &ProofObligation) -> Vec<(u64, u64)> {
    let mut extra: Vec<u64> = BOUNDARY_VALUES
        .iter()
        .filter(|value| **value <= u64::from(u32::MAX))
        .map(|value| value | (1 << 32))
        .collect();
    for constant in wide_constants(obligation) {
        extra.extend([constant, constant ^ (1 << 32), constant ^ (1 << 63)]);
    }
    let mut seen: HashSet<u64> = BOUNDARY_VALUES.into_iter().collect();
    extra.retain(|value| seen.insert(*value));
    let mut pairs = Vec::new();
    for a in BOUNDARY_VALUES {
        pairs.extend(BOUNDARY_VALUES.map(|b| (a, b)));
    }
    for x in extra {
        for b in BOUNDARY_VALUES {
            pairs.extend([(x, b), (b, x)]);
        }
    }
    pairs
}

/// Whether both sides agree when the first two entry registers take each of
/// the [`boundary_pairs`] (equal operands included, which random samples
/// almost never meet) and every other free input a value derived from them.
/// Test-only semantics check; it is never credit.
fn holds_at_boundaries(obligation: &ProofObligation) -> bool {
    use crate::smt::{EvalEnv, EvalResult};
    boundary_pairs(obligation).into_iter().all(|(a, b)| {
        let mut env = EvalEnv::default();
        for (name, width) in free_inputs_of(obligation) {
            let value = match name.as_str() {
                "e_rdi" => a,
                "e_rsi" => b,
                _ => a.rotate_left(7) ^ b.wrapping_mul(0x9e37_79b9_7f4a_7c15),
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
        observable_items(obligation)
            .iter()
            .all(|(source, machine)| source.eval(&env) == machine.eval(&env))
    })
}

/// Every x86 condition code.
const CONDITION_CODES: [trust_cg_ir::X86CondCode; 16] = {
    use trust_cg_ir::X86CondCode::*;
    [O, NO, B, AE, E, NE, BE, A, S, NS, P, NP, L, GE, LE, G]
};

/// What the machine compares: full-width operands, or narrow ones sign- or
/// zero-extended to 64 bits (the selector's `MovsxB`/`MovsxW` for a signed
/// narrow order, `Movzx`/`MovzxW` or a masked bool otherwise).
#[derive(Clone, Copy)]
enum Compared {
    Full,
    SignExtended,
    ZeroExtended,
}

/// The conditions equal to `cc` on every pair of `compared` operands. A
/// 64-bit subtraction of two extended narrow values never overflows (OF is
/// 0), so L is S and GE is NS; for zero-extended values the result is
/// negative exactly when the subtraction borrows (SF is CF), so the signed
/// and unsigned orders coincide: B = L = S, AE = GE = NS, BE = LE, A = G.
fn equal_conditions(
    cc: trust_cg_ir::X86CondCode,
    compared: Compared,
) -> Vec<trust_cg_ir::X86CondCode> {
    use trust_cg_ir::X86CondCode::*;
    let classes: &[&[trust_cg_ir::X86CondCode]] = match compared {
        Compared::Full => &[],
        Compared::SignExtended => &[&[L, S], &[GE, NS]],
        Compared::ZeroExtended => &[&[B, L, S], &[AE, GE, NS], &[BE, LE], &[A, G]],
    };
    classes
        .iter()
        .find(|class| class.contains(&cc))
        .map_or_else(|| vec![cc], |class| class.to_vec())
}

#[test]
fn branch_free_compares_have_exact_predicate_semantics() {
    use PairShape::*;
    // For every compare shape, the selector's condition holds, and every
    // other condition is refuted unless it equals that condition on every
    // pair of operands the machine compares ([`equal_conditions`]): the
    // theorem is exact, neither weaker nor stronger than the x86 flags.
    for shape in [
        CmpEqU64, CmpNeU64, CmpUltU64, CmpSltI64, CmpUgeU32, CmpSgtI32, CmpUleU16, CmpSleI16,
        CmpUgtU8, CmpSgeI8, CmpEqConst, CmpBoolEq,
    ] {
        let (source, machine) = slice5_pair(shape);
        let setcc = rows_with(&machine, X86Opcode::Setcc)[0];
        let O::CondCode(selected) = inst(&machine, setcc).operands[1] else {
            panic!("{shape:?}: setcc has no condition");
        };
        let compared = match shape {
            CmpUleU16 | CmpUgtU8 | CmpBoolEq => Compared::ZeroExtended,
            CmpSleI16 | CmpSgeI8 => Compared::SignExtended,
            _ => Compared::Full,
        };
        let equal = equal_conditions(selected, compared);
        for cc in CONDITION_CODES {
            let mut mutant = machine.clone();
            inst_mut(&mut mutant, setcc).operands[1] = O::CondCode(cc);
            let theorem = theorem_without_affine_refusal(&source, &mutant, SYSV).unwrap();
            let holds = holds_on_samples(&theorem) && holds_at_boundaries(&theorem);
            let expected = equal.contains(&cc);
            assert_eq!(
                holds, expected,
                "{shape:?}: setcc {cc:?} (selected {selected:?})"
            );
        }
    }
    // A zero extension where a signed narrow compare needs a sign extension.
    let (source, mut machine) = slice5_pair(CmpSgeI8);
    for row in rows_with(&machine, X86Opcode::MovsxB) {
        inst_mut(&mut machine, row).opcode = X86Opcode::Movzx;
    }
    theorem_refuted(&source, &machine, "movzx for a signed i8 compare");
    // Compare operands swapped.
    let (source, mut machine) = slice5_pair(CmpSltI64);
    let cmp = rows_with(&machine, X86Opcode::CmpRR)[0];
    inst_mut(&mut machine, cmp).operands.swap(0, 1);
    theorem_refuted(&source, &machine, "compare operands swapped");
    // A 32-bit compare of 64-bit operands.
    let (source, mut machine) = slice5_pair(CmpUltU64);
    let cmp = rows_with(&machine, X86Opcode::CmpRR)[0];
    let narrowed: Vec<O> = inst(&machine, cmp)
        .operands
        .iter()
        .map(|operand| match operand {
            O::VReg(vreg) => O::VReg(VReg::new(vreg.id + 100, RegClass::Gpr32)),
            other => other.clone(),
        })
        .collect();
    for (operand, source_operand) in narrowed.iter().zip(inst(&machine, cmp).operands.clone()) {
        insert_at(
            &mut machine,
            cmp,
            X86ISelInst::new(X86Opcode::MovRR32, vec![operand.clone(), source_operand]),
        );
    }
    let cmp = rows_with(&machine, X86Opcode::CmpRR)[0];
    inst_mut(&mut machine, cmp).operands = narrowed;
    theorem_refuted(&source, &machine, "32-bit compare of u64 operands");
    // A wrong immediate in `cmp r, imm32`.
    let (_, source, mut machine) = slice_five_variants()
        .into_iter()
        .find(|(label, ..)| label == "CmpEqConst/CmpRI")
        .unwrap();
    let cmp = rows_with(&machine, X86Opcode::CmpRI)[0];
    inst_mut(&mut machine, cmp).operands[1] = O::Imm(6);
    theorem_refuted(&source, &machine, "cmp against 6 for 5");
}

#[test]
fn setcc_defines_only_its_low_byte_and_reads_only_compare_flags() {
    // SETcc without the zero extension: EAX bits 8..31 are the undefined
    // bits above the byte (register allocation treats the destination as a
    // pure definition), so a bool result that relies on them is refuted.
    let (source, mut machine) = slice5_pair(PairShape::CmpEqU64);
    let movzx = rows_with(&machine, X86Opcode::Movzx)[0];
    assert_eq!(movzx, rows_with(&machine, X86Opcode::Setcc)[0] + 1);
    remove_at(&mut machine, movzx);
    theorem_refuted(&source, &machine, "setcc without movzx");
    // ... also where the destination held a zero before: the pre-RA merge is
    // not a promise the allocated code keeps.
    let (source, mut machine) = slice5_pair(PairShape::CmpEqU64);
    let setcc = rows_with(&machine, X86Opcode::Setcc)[0];
    let destination = inst(&machine, setcc).operands[0].clone();
    remove_at(&mut machine, setcc + 1);
    insert_at(
        &mut machine,
        setcc - 1,
        X86ISelInst::new(X86Opcode::MovRI, vec![destination, O::Imm(0)]),
    );
    theorem_refuted(&source, &machine, "setcc into a zeroed register, no movzx");
    // SETcc with no compare before it reads the entry flags: undefined.
    let (source, mut machine) = slice5_pair(PairShape::CmpEqU64);
    let cmp = rows_with(&machine, X86Opcode::CmpRR)[0];
    remove_at(&mut machine, cmp);
    expect_mismatch(
        &source,
        &machine,
        "setcc of the entry flags",
        |m| matches!(m, X86BodyMismatch::UndefinedRead { operand, .. } if operand == "rflags"),
    );
    // An ALU row between the compare and the SETcc rewrites the flags: no
    // claim.
    let (source, mut machine) = slice5_pair(PairShape::CmpEqU64);
    let cmp = rows_with(&machine, X86Opcode::CmpRR)[0];
    let operand = inst(&machine, cmp).operands[0].clone();
    insert_at(
        &mut machine,
        cmp + 1,
        X86ISelInst::new(X86Opcode::AddRI, vec![vreg(90), operand, O::Imm(1)]),
    );
    expect_unsupported(&source, &machine, "flags rewritten before setcc");
    // A SETcc into an 8-bit physical alias is outside the row forms.
    let (source, mut machine) = slice5_pair(PairShape::CmpEqU64);
    let setcc = rows_with(&machine, X86Opcode::Setcc)[0];
    inst_mut(&mut machine, setcc).operands[0] = O::PReg(trust_cg_ir::x86_64_regs::AL);
    expect_unsupported(&source, &machine, "setcc al");
}

#[test]
fn compare_results_reach_every_observable() {
    // Stored: the bool byte (8 bits) at the stored address.
    let (source, machine) = slice5_pair(PairShape::CmpStore);
    source_bound_x86_body(&source, &machine, SYSV).unwrap();
    assert_eq!(
        item_widths(&plain_theorem(&source, &machine)),
        vec![(64, 64), (8, 8)]
    );
    // Passed: the backend's clean 32-bit bool argument.
    let (source, machine) = slice5_pair(PairShape::CmpCallArg);
    source_bound_x86_body(&source, &machine, SYSV).unwrap();
    assert_eq!(
        item_widths(&plain_theorem(&source, &machine)),
        vec![(64, 64), (32, 32)]
    );
    // Widened: `(a < b) as u64` in RAX.
    let (source, machine) = slice5_pair(PairShape::CmpZext);
    source_bound_x86_body(&source, &machine, SYSV).unwrap();
    assert_eq!(
        item_widths(&plain_theorem(&source, &machine)),
        vec![(64, 64)]
    );
}

#[test]
fn compares_outside_the_slice_five_domain_are_unsupported() {
    // A signed order of two bools: LIR orders a 1-bit value as signed (true
    // is -1), the selector compares the 0/1 bytes.
    let mut signed_bools = slice5_lir(PairShape::CmpBoolEq);
    let entry = signed_bools.entry_block;
    for inst in &mut signed_bools.blocks.get_mut(&entry).unwrap().instructions {
        if let L::Icmp { cond } = &mut inst.opcode {
            *cond = IntCC::SignedLessThan;
        }
    }
    assert!(!source_admits_x86_body_owner(&signed_bools, SYSV));
    // Three results leave the System V return pair.
    let mut three = slice5_lir(PairShape::PairSwap);
    three.signature.returns.push(Type::I64);
    assert!(!source_admits_x86_body_owner(&three, SYSV));
    // A non-scalar lane.
    let mut wide = slice5_lir(PairShape::PairSwap);
    wide.signature.returns[1] = Type::I128;
    assert!(!source_admits_x86_body_owner(&wide, SYSV));
}

// ---------------------------------------------------------------------------
// Canonical SMT2 (golden file with a reviewed digest pin)
// ---------------------------------------------------------------------------

/// `x == 5` of a u64 made at 32 bits: the copy of `x` truncated (`MovRR32`),
/// against the constant register or the immediate, or `cmp edi, 5` itself.
/// Each differs from the source only when bits 32..63 of `x` are set and its
/// low half is 5, so it is wrong for `x = 0x1_0000_0005`.
fn truncated_u64_compares() -> Vec<(&'static str, Function, X86ISelFunction)> {
    let mut cases = Vec::new();
    let (source, mut machine) = slice5_pair(PairShape::CmpEqConst);
    assert_eq!(inst(&machine, 0).opcode, X86Opcode::MovRR);
    inst_mut(&mut machine, 0).opcode = X86Opcode::MovRR32;
    cases.push(("u64 == 5 with x copied at 32 bits", source, machine));
    let (_, source, machine) = slice_five_variants()
        .into_iter()
        .find(|(label, _, _)| label == "CmpEqConst/CmpRI")
        .expect("the immediate form");
    let mut copied = machine.clone();
    assert_eq!(inst(&copied, 0).opcode, X86Opcode::MovRR);
    inst_mut(&mut copied, 0).opcode = X86Opcode::MovRR32;
    cases.push((
        "u64 == 5 with x copied at 32 bits, against an immediate",
        source.clone(),
        copied,
    ));
    let mut direct = machine;
    let cmp = rows_with(&direct, X86Opcode::CmpRI)[0];
    inst_mut(&mut direct, cmp).operands[0] = O::PReg(trust_cg_ir::x86_64_regs::EDI);
    cases.push(("u64 == 5 as cmp edi, 5", source, direct));
    cases
}

/// The test-only sampled oracle ([`theorem_refuted`]) refutes a u64 compare
/// made at 32 bits, which random 64-bit samples miss: its boundary values
/// carry each 64-bit constant of the theorem with bit 32 set.
#[test]
fn a_u64_compare_made_at_32_bits_is_refuted() {
    for (label, source, machine) in truncated_u64_compares() {
        theorem_refuted(&source, &machine, label);
    }
}

const SLICE_FIVE_SNAPSHOT_SHA256: &str =
    "7da7fc96879b7cae55f5b8ca1bcd8d898f1cb3f9de0c5a1684b21b7c5a468601";

#[test]
fn slice_five_smt2_is_canonical_per_shape() {
    use sha2::{Digest, Sha256};
    const GOLDEN: &str =
        include_str!("../tests/fixtures/x86_source_bound_body/slice5_snapshots.smt2");
    let mut rendered = String::new();
    for shape in SLICE_FIVE {
        let (source, machine) = slice5_pair(shape);
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
            .join("tests/fixtures/x86_source_bound_body/slice5_snapshots.smt2");
        std::fs::write(&path, &rendered).unwrap();
        panic!(
            "rewrote {}; review its diff, set SLICE_FIVE_SNAPSHOT_SHA256 to {:x} and re-run \
             without TCG_X86_BODY_SNAPSHOT_WRITE",
            path.display(),
            Sha256::digest(rendered.as_bytes())
        );
    }
    assert_eq!(
        format!("{:x}", Sha256::digest(GOLDEN.as_bytes())),
        SLICE_FIVE_SNAPSHOT_SHA256,
        "the golden file changed without the reviewed digest pin"
    );
    assert_eq!(rendered, GOLDEN, "slice-5 snapshots drifted");
}

// ---------------------------------------------------------------------------
// Wrong lowerings the Rust check cannot judge (no solver)
// ---------------------------------------------------------------------------

/// Wrong lowerings of slice-5 shapes, with the Rust refusal bypassed: the
/// sampled oracle refutes each one here, and the replayed theorem must be
/// refuted by AY with a counterexample (`slice5_qualification`).
pub(super) fn slice_five_refutations() -> Vec<(&'static str, Function, X86ISelFunction)> {
    let mut cases = Vec::new();
    let (source, mut machine) = slice5_pair(PairShape::PairSwap);
    let (rax, rdx) = (return_move(&machine, RAX), return_move(&machine, RDX));
    let (first, second) = (
        inst(&machine, rax).operands[1].clone(),
        inst(&machine, rdx).operands[1].clone(),
    );
    inst_mut(&mut machine, rax).operands[1] = second;
    inst_mut(&mut machine, rdx).operands[1] = first.clone();
    cases.push(("pair halves swapped", source, machine));
    let (source, mut machine) = slice5_pair(PairShape::PairSwap);
    inst_mut(&mut machine, rdx).operands[1] = first;
    cases.push(("RDX holds lane 0", source, machine));
    let (source, mut machine) = slice5_pair(PairShape::PairSwap);
    inst_mut(&mut machine, rdx).opcode = X86Opcode::MovRR32;
    cases.push(("u64 lane through MovRR32", source, machine));
    let (source, mut machine) = slice5_pair(PairShape::PairCallForward);
    let (rax, rdx) = (return_move(&machine, RAX), return_move(&machine, RDX));
    let (first, second) = (
        inst(&machine, rax).operands[1].clone(),
        inst(&machine, rdx).operands[1].clone(),
    );
    inst_mut(&mut machine, rax).operands[1] = second;
    inst_mut(&mut machine, rdx).operands[1] = first;
    cases.push(("pair call lanes swapped", source, machine));
    for (label, shape) in [
        ("pair call bool lane unmasked", PairShape::PairCallBool),
        (
            "forwarded pair call bool lane unmasked",
            PairShape::PairCallBoolForward,
        ),
    ] {
        let (source, mut machine) = slice5_pair(shape);
        let call = rows_with(&machine, X86Opcode::Call)[0];
        let mask = rows_with(&machine, X86Opcode::AndRI)
            .into_iter()
            .find(|row| *row > call)
            .expect("the lane mask");
        remove_at(&mut machine, mask);
        cases.push((label, source, machine));
    }
    let (source, mut machine) = slice5_pair(PairShape::TwoGlobals);
    let leas = rows_with(&machine, X86Opcode::LeaRip);
    let (first, second) = (
        inst(&machine, leas[0]).operands[1].clone(),
        inst(&machine, leas[1]).operands[1].clone(),
    );
    inst_mut(&mut machine, leas[0]).operands[1] = second;
    inst_mut(&mut machine, leas[1]).operands[1] = first;
    cases.push(("symbols swapped", source, machine));
    let (source, mut machine) = slice5_pair(PairShape::GlobalField);
    let load = rows_with(&machine, X86Opcode::MovRM)[0];
    if let O::MemAddr { disp, .. } = &mut inst_mut(&mut machine, load).operands[1] {
        *disp = 4;
    }
    cases.push(("global field at +12 for +8", source, machine));
    for (label, shape, cc) in [
        (
            "signed order for an unsigned compare",
            PairShape::CmpUltU64,
            trust_cg_ir::X86CondCode::L,
        ),
        (
            "unsigned order for a signed compare",
            PairShape::CmpSltI64,
            trust_cg_ir::X86CondCode::B,
        ),
        (
            "negated equality",
            PairShape::CmpEqU64,
            trust_cg_ir::X86CondCode::NE,
        ),
        (
            "signed order for an unsigned u32 compare",
            PairShape::CmpUgeU32,
            trust_cg_ir::X86CondCode::GE,
        ),
    ] {
        let (source, mut machine) = slice5_pair(shape);
        let setcc = rows_with(&machine, X86Opcode::Setcc)[0];
        inst_mut(&mut machine, setcc).operands[1] = O::CondCode(cc);
        cases.push((label, source, machine));
    }
    let (source, mut machine) = slice5_pair(PairShape::CmpSgeI8);
    for row in rows_with(&machine, X86Opcode::MovsxB) {
        inst_mut(&mut machine, row).opcode = X86Opcode::Movzx;
    }
    cases.push(("movzx for a signed i8 compare", source, machine));
    let (source, mut machine) = slice5_pair(PairShape::CmpEqU64);
    let movzx = rows_with(&machine, X86Opcode::Movzx)[0];
    remove_at(&mut machine, movzx);
    cases.push(("setcc without movzx", source, machine));
    let (source, mut machine) = slice5_pair(PairShape::CmpSltI64);
    let cmp = rows_with(&machine, X86Opcode::CmpRR)[0];
    inst_mut(&mut machine, cmp).operands.swap(0, 1);
    cases.push(("compare operands swapped", source, machine));
    cases.extend(truncated_u64_compares());
    cases
}

#[test]
fn every_slice_five_refutation_is_refuted_on_samples() {
    for (label, source, machine) in slice_five_refutations() {
        theorem_refuted(&source, &machine, label);
    }
}
