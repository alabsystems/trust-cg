// trust-cg-codegen/tests/tmbc_roundtrip_prop.rs
// Property-based round-trip test for the `.tmbc` binary format (#415).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Transport-format property 1:
//
//     Round-trip property: forall m: Module, decode(encode(m)) = m
//
// This suite is the empirical (property-test) half of that property; it is
// test-rung evidence over the generated sample, never a proof. Two
// generators:
//
// * The SCALAR generator (#415): a bounded shape (≤3 functions, ≤5 blocks
//   per function, ≤10 instructions per block) over the integer BinOps
//   Add..AShr, FAdd..FDiv, Neg/Not/CtPop, every ICmpOp, the ordered FCmpOps,
//   zext/trunc, Select, branches, returns and block parameters, at
//   I8/I16/I32/I64 and F32/F64. Each module is encoded via `encode_tmbc`,
//   decoded via `decode_tmbc`, and asserted structurally equal and
//   byte-stable.
// * The CONSTRUCT generator (L05-P7, `mod constructs` below): aggregates,
//   enums with every layout encoding, records, closures, sequences/sets,
//   globals with initializers/TLS/symbol attributes, handles, refinements
//   and predicate tables, dialect types and ops, proof tables with lineage
//   sidecars, v41-v50 metadata, TrustIR's v51 INST wire batch, and the
//   constructs the pinned writer has no wire image for — each module driven through trust-cg's binary, JSON and
//   text writers and readers with trust-ir's reader and the MessagePack codec
//   as oracles, and required to round-trip EXACTLY or be refused by the name
//   the generator predicts.
//
// Neither generator invokes the compiler or the verifier, and neither
// requires semantic validity beyond what the codecs require. The pinned
// corpus itself is the subject of `tests/trust_ir_corpus_roundtrip.rs`;
// `tests/tmbc_canonical.rs` (#416) pins encode determinism on fixed fixtures.

use proptest::prelude::*;
use trust_cg_codegen::pipeline::{decode_tmbc, encode_tmbc};
use trust_ir::{BinOp, FCmpOp, ICmpOp, Module as TrustIrModule, Ty, UnOp};
use trust_ir_build::ModuleBuilder;

// ---------------------------------------------------------------------------
// Shape specification
// ---------------------------------------------------------------------------

/// A tiny IR-level instruction description that the generator knows how to
/// lower into one or more builder calls. Kept deliberately opaque so the
/// generator is free to pick operands.
#[derive(Debug, Clone)]
enum InstKind {
    IConst(IntKind, i64),
    FConst(FloatKind, f64),
    IBinop(BinOp, IntKind),
    FBinop(BinOp, FloatKind),
    IUnop(UnOp, IntKind),
    ICmp(ICmpOp, IntKind),
    FCmp(FCmpOp, FloatKind),
    IZext(IntKind, IntKind),  // src -> dst (widening)
    ITrunc(IntKind, IntKind), // src -> dst (narrowing)
    Select,                   // select cond:Bool, then:I64, else:I64 -> I64
}

#[derive(Debug, Clone, Copy)]
enum IntKind {
    I8,
    I16,
    I32,
    I64,
}

impl IntKind {
    fn ty(self) -> Ty {
        match self {
            IntKind::I8 => Ty::I8,
            IntKind::I16 => Ty::I16,
            IntKind::I32 => Ty::I32,
            IntKind::I64 => Ty::I64,
        }
    }
    fn bits(self) -> u32 {
        match self {
            IntKind::I8 => 8,
            IntKind::I16 => 16,
            IntKind::I32 => 32,
            IntKind::I64 => 64,
        }
    }
}

#[derive(Debug, Clone, Copy)]
enum FloatKind {
    F32,
    F64,
}
impl FloatKind {
    fn ty(self) -> Ty {
        match self {
            FloatKind::F32 => Ty::F32,
            FloatKind::F64 => Ty::F64,
        }
    }
}

/// A single block's spec: how many instructions to attempt, and whether it
/// terminates by branching to the next block (`false`) or by returning
/// (`true`). The last block in a function always returns.
#[derive(Debug, Clone)]
struct BlockSpec {
    insts: Vec<InstKind>,
    terminates_with_ret: bool,
    // For conditional branch: if true and there is a successor +2 (i.e. two
    // distinct forward blocks available), emit condbr. Otherwise emit br.
    use_condbr: bool,
}

#[derive(Debug, Clone)]
struct FuncSpec {
    name: String,
    num_params: u8, // 0..=2 I64 params
    blocks: Vec<BlockSpec>,
}

#[derive(Debug, Clone)]
struct ModuleSpec {
    name: String,
    functions: Vec<FuncSpec>,
}

// ---------------------------------------------------------------------------
// Proptest strategies
// ---------------------------------------------------------------------------

fn int_kind_strategy() -> impl Strategy<Value = IntKind> {
    prop_oneof![
        Just(IntKind::I8),
        Just(IntKind::I16),
        Just(IntKind::I32),
        Just(IntKind::I64),
    ]
}

fn float_kind_strategy() -> impl Strategy<Value = FloatKind> {
    prop_oneof![Just(FloatKind::F32), Just(FloatKind::F64)]
}

fn binop_int_strategy() -> impl Strategy<Value = BinOp> {
    prop_oneof![
        Just(BinOp::Add),
        Just(BinOp::Sub),
        Just(BinOp::Mul),
        Just(BinOp::And),
        Just(BinOp::Or),
        Just(BinOp::Xor),
        Just(BinOp::Shl),
        Just(BinOp::LShr),
        Just(BinOp::AShr),
    ]
}

fn binop_float_strategy() -> impl Strategy<Value = BinOp> {
    prop_oneof![
        Just(BinOp::FAdd),
        Just(BinOp::FSub),
        Just(BinOp::FMul),
        Just(BinOp::FDiv),
    ]
}

fn icmp_strategy() -> impl Strategy<Value = ICmpOp> {
    prop_oneof![
        Just(ICmpOp::Eq),
        Just(ICmpOp::Ne),
        Just(ICmpOp::Slt),
        Just(ICmpOp::Sle),
        Just(ICmpOp::Sgt),
        Just(ICmpOp::Sge),
        Just(ICmpOp::Ult),
        Just(ICmpOp::Ule),
        Just(ICmpOp::Ugt),
        Just(ICmpOp::Uge),
    ]
}

fn fcmp_strategy() -> impl Strategy<Value = FCmpOp> {
    prop_oneof![
        Just(FCmpOp::OEq),
        Just(FCmpOp::ONe),
        Just(FCmpOp::OLt),
        Just(FCmpOp::OLe),
        Just(FCmpOp::OGt),
        Just(FCmpOp::OGe),
    ]
}

fn unop_int_strategy() -> impl Strategy<Value = UnOp> {
    prop_oneof![Just(UnOp::Neg), Just(UnOp::Not), Just(UnOp::CtPop)]
}

fn inst_kind_strategy() -> impl Strategy<Value = InstKind> {
    prop_oneof![
        // IConst covers all int widths; use a narrow i64 value range so we
        // stay safely representable in every int kind.
        (int_kind_strategy(), (-1000i64..=1000i64)).prop_map(|(k, v)| InstKind::IConst(k, v)),
        (float_kind_strategy(), (-1e3f64..=1e3f64)).prop_map(|(k, v)| InstKind::FConst(k, v)),
        (binop_int_strategy(), int_kind_strategy()).prop_map(|(op, k)| InstKind::IBinop(op, k)),
        (binop_float_strategy(), float_kind_strategy()).prop_map(|(op, k)| InstKind::FBinop(op, k)),
        (unop_int_strategy(), int_kind_strategy()).prop_map(|(op, k)| InstKind::IUnop(op, k)),
        (icmp_strategy(), int_kind_strategy()).prop_map(|(op, k)| InstKind::ICmp(op, k)),
        (fcmp_strategy(), float_kind_strategy()).prop_map(|(op, k)| InstKind::FCmp(op, k)),
        // Widening zext: pick two kinds, require src.bits < dst.bits.
        (int_kind_strategy(), int_kind_strategy())
            .prop_filter("src < dst for zext", |(s, d)| s.bits() < d.bits())
            .prop_map(|(s, d)| InstKind::IZext(s, d)),
        // Narrowing trunc: pick two kinds, require src.bits > dst.bits.
        (int_kind_strategy(), int_kind_strategy())
            .prop_filter("src > dst for trunc", |(s, d)| s.bits() > d.bits())
            .prop_map(|(s, d)| InstKind::ITrunc(s, d)),
        Just(InstKind::Select),
    ]
}

fn block_spec_strategy() -> impl Strategy<Value = BlockSpec> {
    (
        prop::collection::vec(inst_kind_strategy(), 0..=10),
        any::<bool>(),
        any::<bool>(),
    )
        .prop_map(|(insts, terminates_with_ret, use_condbr)| BlockSpec {
            insts,
            terminates_with_ret,
            use_condbr,
        })
}

fn func_spec_strategy(idx: usize) -> impl Strategy<Value = FuncSpec> {
    (0u8..=2, prop::collection::vec(block_spec_strategy(), 1..=5)).prop_map(
        move |(num_params, blocks)| FuncSpec {
            name: format!("_prop_f{}", idx),
            num_params,
            blocks,
        },
    )
}

fn module_spec_strategy() -> impl Strategy<Value = ModuleSpec> {
    (1usize..=3usize).prop_flat_map(|n| {
        let funcs = (0..n).map(func_spec_strategy).collect::<Vec<_>>();
        (Just(n), funcs).prop_map(|(n, functions)| ModuleSpec {
            name: format!("tmbc_prop_mod_{}", n),
            functions,
        })
    })
}

// ---------------------------------------------------------------------------
// Spec -> trust_ir::Module materialisation
// ---------------------------------------------------------------------------

fn materialise(spec: &ModuleSpec) -> TrustIrModule {
    let mut mb = ModuleBuilder::new(&spec.name);
    for fspec in &spec.functions {
        let params = vec![Ty::I64; fspec.num_params as usize];
        let ty = mb.add_func_type(params, vec![Ty::I64]);
        let mut fb = mb.function(&fspec.name, ty);

        // Create all blocks up front so `br` / `condbr` have forward targets.
        let block_count = fspec.blocks.len();
        let mut blocks = Vec::with_capacity(block_count);
        for _ in 0..block_count {
            blocks.push(fb.create_block());
        }

        // Entry block: take function params (all I64).
        let entry = blocks[0];
        let mut entry_params: Vec<_> = Vec::new();
        for _ in 0..fspec.num_params {
            entry_params.push(fb.add_block_param(entry, Ty::I64));
        }
        // Non-entry blocks: no block params (keeps branch lowering trivial).

        for (bi, bspec) in fspec.blocks.iter().enumerate() {
            fb.switch_to_block(blocks[bi]);

            // Per-block scratch: a small stack of (value, ty) we can pull
            // operands from. Seeded with entry params in block 0 for
            // realistic data flow; other blocks start empty so we emit
            // iconst-first to populate.
            let mut scratch: Vec<(trust_ir::ValueId, Ty)> = if bi == 0 {
                entry_params.iter().map(|v| (*v, Ty::I64)).collect()
            } else {
                Vec::new()
            };

            for inst in &bspec.insts {
                emit_inst(&mut fb, &mut scratch, inst);
            }

            // Terminator.
            let is_last = bi + 1 == block_count;
            if is_last || bspec.terminates_with_ret {
                // Return an I64. If we have an I64 in scratch, use it;
                // otherwise materialise a zero.
                let ret_v = pick_or_make_i64(&mut fb, &mut scratch);
                fb.ret(vec![ret_v]);
            } else {
                let next = blocks[bi + 1];
                let successor_exists = bi + 2 < block_count;
                if bspec.use_condbr && successor_exists {
                    // Need a Bool cond; fabricate via `icmp eq 0, 0` (always true).
                    let z = fb.iconst(Ty::I64, 0);
                    let cond = fb.icmp(ICmpOp::Eq, Ty::I64, z, z);
                    let tgt2 = blocks[bi + 2];
                    fb.condbr(cond, next, vec![], tgt2, vec![]);
                } else {
                    fb.br(next, vec![]);
                }
            }
        }
        fb.build();
    }
    mb.build().expect("ModuleBuilder::build: test fixture")
}

fn emit_inst(
    fb: &mut trust_ir_build::FunctionBuilder<'_>,
    scratch: &mut Vec<(trust_ir::ValueId, Ty)>,
    inst: &InstKind,
) {
    match inst {
        InstKind::IConst(k, v) => {
            let vid = fb.iconst(k.ty(), *v as i128);
            scratch.push((vid, k.ty()));
        }
        InstKind::FConst(k, v) => {
            // Skip NaN/±inf to avoid any serializer-level float quirks that
            // are out of scope for this ticket (see #415 out-of-scope).
            if !v.is_finite() {
                return;
            }
            let vid = fb.fconst(k.ty(), *v);
            scratch.push((vid, k.ty()));
        }
        InstKind::IBinop(op, k) => {
            let ty = k.ty();
            let lhs = find_or_make(fb, scratch, &ty);
            let rhs = find_or_make(fb, scratch, &ty);
            let vid = fb.binop(*op, ty.clone(), lhs, rhs);
            scratch.push((vid, ty));
        }
        InstKind::FBinop(op, k) => {
            let ty = k.ty();
            let lhs = find_or_make_f(fb, scratch, &ty);
            let rhs = find_or_make_f(fb, scratch, &ty);
            let vid = fb.binop(*op, ty.clone(), lhs, rhs);
            scratch.push((vid, ty));
        }
        InstKind::IUnop(op, k) => {
            let ty = k.ty();
            let operand = find_or_make(fb, scratch, &ty);
            let vid = fb.unop(*op, ty.clone(), operand);
            scratch.push((vid, ty));
        }
        InstKind::ICmp(op, k) => {
            let ty = k.ty();
            let lhs = find_or_make(fb, scratch, &ty);
            let rhs = find_or_make(fb, scratch, &ty);
            let vid = fb.icmp(*op, ty, lhs, rhs);
            scratch.push((vid, Ty::Bool));
        }
        InstKind::FCmp(op, k) => {
            let ty = k.ty();
            let lhs = find_or_make_f(fb, scratch, &ty);
            let rhs = find_or_make_f(fb, scratch, &ty);
            let vid = fb.fcmp(*op, ty, lhs, rhs);
            scratch.push((vid, Ty::Bool));
        }
        InstKind::IZext(s, d) => {
            let src_ty = s.ty();
            let operand = find_or_make(fb, scratch, &src_ty);
            let vid = fb.zext(src_ty, d.ty(), operand);
            scratch.push((vid, d.ty()));
        }
        InstKind::ITrunc(s, d) => {
            let src_ty = s.ty();
            let operand = find_or_make(fb, scratch, &src_ty);
            let vid = fb.trunc(src_ty, d.ty(), operand);
            scratch.push((vid, d.ty()));
        }
        InstKind::Select => {
            let cond = find_or_make_bool(fb, scratch);
            let then_v = find_or_make(fb, scratch, &Ty::I64);
            let else_v = find_or_make(fb, scratch, &Ty::I64);
            let vid = fb.select(Ty::I64, cond, then_v, else_v);
            scratch.push((vid, Ty::I64));
        }
    }
}

fn find_or_make(
    fb: &mut trust_ir_build::FunctionBuilder<'_>,
    scratch: &mut Vec<(trust_ir::ValueId, Ty)>,
    want: &Ty,
) -> trust_ir::ValueId {
    for (v, t) in scratch.iter().rev() {
        if t == want {
            return *v;
        }
    }
    let v = fb.iconst(want.clone(), 0);
    scratch.push((v, want.clone()));
    v
}

fn find_or_make_f(
    fb: &mut trust_ir_build::FunctionBuilder<'_>,
    scratch: &mut Vec<(trust_ir::ValueId, Ty)>,
    want: &Ty,
) -> trust_ir::ValueId {
    for (v, t) in scratch.iter().rev() {
        if t == want {
            return *v;
        }
    }
    let v = fb.fconst(want.clone(), 0.0);
    scratch.push((v, want.clone()));
    v
}

fn find_or_make_bool(
    fb: &mut trust_ir_build::FunctionBuilder<'_>,
    scratch: &mut Vec<(trust_ir::ValueId, Ty)>,
) -> trust_ir::ValueId {
    for (v, t) in scratch.iter().rev() {
        if *t == Ty::Bool {
            return *v;
        }
    }
    let v = fb.bool_const(false);
    scratch.push((v, Ty::Bool));
    v
}

fn pick_or_make_i64(
    fb: &mut trust_ir_build::FunctionBuilder<'_>,
    scratch: &mut Vec<(trust_ir::ValueId, Ty)>,
) -> trust_ir::ValueId {
    for (v, t) in scratch.iter().rev() {
        if *t == Ty::I64 {
            return *v;
        }
    }
    let v = fb.iconst(Ty::I64, 0);
    scratch.push((v, Ty::I64));
    v
}

// ---------------------------------------------------------------------------
// Property tests
// ---------------------------------------------------------------------------

proptest! {
    // 256 cases satisfies the ticket's ≥256 lower bound. Runtime is well
    // under a minute even with every instruction variant in play.
    #![proptest_config(ProptestConfig {
        cases: 256,
        .. ProptestConfig::default()
    })]

    #[test]
    fn tmbc_roundtrip_preserves_structural_equality(spec in module_spec_strategy()) {
        let module = materialise(&spec);
        let bytes = encode_tmbc(&module).expect("encode_tmbc must succeed");
        let decoded = decode_tmbc(&bytes).expect("decode_tmbc must succeed");
        prop_assert_eq!(
            &module, &decoded,
            "round-trip must preserve structural Module equality"
        );
    }

    #[test]
    fn tmbc_reencode_is_a_fixed_point(spec in module_spec_strategy()) {
        // Even stricter than structural equality: encode -> decode -> encode
        // must produce byte-equal output. This catches any field that
        // round-trips to a semantically-equal but byte-different state (a
        // canonicality violation exposed only via random inputs).
        let module = materialise(&spec);
        let b1 = encode_tmbc(&module).expect("encode #1");
        let round = decode_tmbc(&b1).expect("decode");
        let b2 = encode_tmbc(&round).expect("encode #2");
        prop_assert_eq!(
            b1, b2,
            "encode ∘ decode ∘ encode must equal encode (canonical fixed point)"
        );
    }
}

// Smoke: confirm the generator itself produces a usable module with the
// required shape bounds. Runs once per `cargo test` invocation.
#[test]
fn generator_smoke_bounds_respected() {
    use proptest::strategy::{Strategy, ValueTree};
    use proptest::test_runner::TestRunner;

    let mut runner = TestRunner::default();
    for _ in 0..64 {
        let tree = module_spec_strategy().new_tree(&mut runner).unwrap();
        let spec = tree.current();
        assert!(!spec.functions.is_empty() && spec.functions.len() <= 3);
        for f in &spec.functions {
            assert!(!f.blocks.is_empty() && f.blocks.len() <= 5);
            for b in &f.blocks {
                assert!(b.insts.len() <= 10);
            }
        }
        // Must materialise without panic and round-trip cleanly.
        let m = materialise(&spec);
        let bytes = encode_tmbc(&m).expect("encode");
        let back = decode_tmbc(&bytes).expect("decode");
        assert_eq!(m, back);
    }
}

// ===========================================================================
// Construct generator (L05-P7): every module family beyond the scalar shape
// ===========================================================================

/// The scalar generator above covers `BinOp`/`ICmp`/`UnOp`/`FCmp`, casts and
/// `Select` over I8-I64/F32-F64 only. This generator composes MODULE ITEMS —
/// aggregates (structs, tuples with v42 declared layouts, arrays with v50
/// splats), enums (no descriptor, `Direct`, `Niche`, `Untagged`, and a
/// deliberately self-contradicting descriptor), records, closures, sequences
/// and sets, globals with initializers, TLS models and v45 symbol attributes,
/// v43 opaque handles, refinements over an interned predicate table, dialect
/// types and ops, proof tables (obligations, certificates, diagnostics,
/// instruction and function annotations) with an optional lineage sidecar,
/// and v41-v45 function metadata (codegen license, display path, producer,
/// SSA names, lexical scopes, spans, calling conventions, symbol and
/// parameter attributes, imports) — and drives each module through trust-cg's
/// own writers and readers.
///
/// Every knob is a proptest value (small `u8` picks, `Vec`s, `bool`s), so a
/// failing module SHRINKS to the fewest, simplest items that still fail —
/// `construct_generator_shrinks_to_a_minimal_counterexample` pins that.
mod constructs {
    use std::collections::BTreeSet;

    use proptest::collection::vec;
    use proptest::prelude::*;
    use trust_cg_codegen::pipeline;
    use trust_ir::text_loss::{TextLoss, TextLossKind, text_losses};
    use trust_ir::value::GlobalId;
    use trust_ir::{
        ArgExt, AttrValue, Block, BlockId, BodyGate, CallingConv, ClosureTy, Constant,
        DiagnosticSeverity, DialectInst, DialectTy, Divergence, Endianness, EnumDef,
        EnumLayoutDescriptor, EnumTagEncoding, EnumTagRepr, EnumVariant, FieldDef, FuncId, FuncTy,
        Function, Global, IdentityScheme, Inst, InstrNode, Linkage, Module, ModuleImport,
        ObligationDiagnostic, ObligationKind, Ordering, ParamAttrs, PassMode, Pred, Producer,
        ProofAnnotation, ProofCertificate, ProofDigest, ProofEvidence, ProofFormula, ProofId,
        ProofLineageId, ProofLineageManifest, ProofLineageNode, ProofObligation,
        ProofObligationSourceIdentity, ProofStatus, ProofTag, ProofTransform, ProofTransformStage,
        RecordDef, RecordId, ScopeData, SetRepr, SourceSpan, Space, StructDef, StructId,
        StructRepr, TargetInfo, TlsModel, TupleLayoutDescriptor, Ty, Universe, ValueId, Visibility,
    };

    // ---------------------------------------------------------------------
    // Specification
    // ---------------------------------------------------------------------

    /// A scalar a generated construct is built from. The first eleven have a
    /// natural size and alignment on both canonical 64-bit targets and are
    /// the only ones a layout-bearing item (declared struct/tuple layout,
    /// enum descriptor) uses; the rest ride signatures, globals and
    /// constants.
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    pub enum Sc {
        I32,
        I64,
        I8,
        I16,
        U8,
        U16,
        U32,
        U64,
        Bool,
        F32,
        F64,
        I128,
        U128,
        Char,
        Usize,
        Isize,
    }

    impl Sc {
        pub fn ty(self) -> Ty {
            match self {
                Sc::I32 => Ty::I32,
                Sc::I64 => Ty::I64,
                Sc::I8 => Ty::I8,
                Sc::I16 => Ty::I16,
                Sc::U8 => Ty::U8,
                Sc::U16 => Ty::U16,
                Sc::U32 => Ty::U32,
                Sc::U64 => Ty::U64,
                Sc::Bool => Ty::Bool,
                Sc::F32 => Ty::F32,
                Sc::F64 => Ty::F64,
                Sc::I128 => Ty::I128,
                Sc::U128 => Ty::U128,
                Sc::Char => Ty::Char,
                Sc::Usize => Ty::Usize,
                Sc::Isize => Ty::Isize,
            }
        }

        /// Size = alignment in bytes on the canonical 64-bit targets.
        fn natural(self) -> u64 {
            match self {
                Sc::I8 | Sc::U8 | Sc::Bool => 1,
                Sc::I16 | Sc::U16 => 2,
                Sc::I32 | Sc::U32 | Sc::F32 | Sc::Char => 4,
                Sc::I64 | Sc::U64 | Sc::F64 | Sc::Usize | Sc::Isize => 8,
                Sc::I128 | Sc::U128 => 16,
            }
        }

        /// A constant of this scalar. Floats include the IEEE specials
        /// (`NaN`, `-0.0`, the infinities) — `Constant` compares floats
        /// bit-exactly, so they round-trip or fail loudly; `U128` reaches the
        /// `Constant::U128` carrier above `i128::MAX` (the one-spelling rule).
        pub fn constant(self, seed: i8) -> Constant {
            match self {
                Sc::Bool => Constant::Bool(seed & 1 == 1),
                Sc::F32 | Sc::F64 => Constant::Float(float_of(seed)),
                Sc::Char => Constant::Int(i128::from(b'a') + i128::from(seed.unsigned_abs() % 26)),
                Sc::U8 | Sc::U16 | Sc::U32 | Sc::U64 | Sc::Usize => {
                    Constant::Int(i128::from(seed.unsigned_abs()))
                }
                Sc::U128 if seed < 0 => Constant::U128(u128::MAX - u128::from(seed.unsigned_abs())),
                _ => Constant::Int(i128::from(seed)),
            }
        }
    }

    fn float_of(seed: i8) -> f64 {
        match seed {
            i8::MIN => f64::NAN,
            -127 => f64::NEG_INFINITY,
            i8::MAX => f64::INFINITY,
            -1 => -0.0,
            s => f64::from(s) / 4.0,
        }
    }

    /// How an enum's memory layout is described.
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    pub enum Layout {
        None,
        Direct,
        Niche,
        Untagged,
        /// A `Direct` descriptor whose size is not a multiple of its align:
        /// the binary and serde carriers keep it verbatim, and the text
        /// printer must REFUSE it (`TextLoss::EnumLayout`), never drop it.
        SelfContradicting,
    }

    /// Whether (and how much of) the module's bodies carry a v41 codegen
    /// license. The binary reader holds a v41+ producer to stamping EVERY
    /// body, so a partially or un-stamped module whose writer header is v41+
    /// must be refused by name at decode (`ProducerOmittedBodyGate`).
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    pub enum License {
        All,
        None,
        Partial,
    }

    #[derive(Debug, Clone)]
    pub enum Item {
        Struct {
            fields: Vec<Sc>,
            repr: u8,
            declared: bool,
            seed: i8,
        },
        Tuple {
            fields: Vec<Sc>,
            declared: bool,
            seed: i8,
        },
        Array {
            elem: Sc,
            len: u8,
            splat: bool,
            seed: i8,
        },
        Enum {
            variants: Vec<Vec<Sc>>,
            explicit: bool,
            repr: Option<u8>,
            layout: Layout,
            field_names: bool,
            seed: i8,
        },
        Record {
            fields: Vec<Sc>,
            offsets: bool,
            seed: i8,
        },
        Closure {
            captures: Vec<Sc>,
            seed: i8,
        },
        Collection {
            elem: Sc,
            set: Option<bool>,
            len: u8,
        },
        Global {
            ty: Sc,
            init: bool,
            tls: Option<u8>,
            linkage: u8,
            visibility: u8,
            section: bool,
            retained: bool,
            align_log2: Option<u8>,
            mutable: bool,
            seed: i8,
        },
        Handle {
            roles: u8,
        },
        Refine {
            base: Sc,
            pred: u8,
            lo: i8,
            width: u8,
        },
        DialectType {
            name: u8,
            version: u8,
        },
        DialectOp {
            attrs: Vec<u8>,
            version: u8,
            seed: i8,
        },
        Proof {
            kind: u8,
            status: u8,
            formula: bool,
            scoped: bool,
            source: bool,
            evidence: Option<u8>,
            diagnostics: Vec<u8>,
            annotations: Vec<u8>,
        },
        Metadata {
            display_path: bool,
            producer: Option<u8>,
            names: bool,
            scopes: bool,
            spans: bool,
            conv: u8,
            visibility: u8,
            section: bool,
            retained: bool,
            param: Option<u8>,
            ret_ext: u8,
        },
        Import {
            v3: bool,
            producer: Option<u8>,
            seed: u8,
        },
        /// A member of TrustIR's v51 INST wire batch (`MakeAggregate` over a
        /// struct or an enum, `MemCopy`, `MemSet`, a bit intrinsic, a
        /// rotate). Until trust-ir `e2154f00` these were `binary_wire_gap`s
        /// the writer refused; at v51 each has a binary tag, so the module
        /// must round-trip EXACTLY like any other construct.
        InstWireBatch {
            which: u8,
        },
        /// A construct the pinned trust-ir's binary writer has NO wire image
        /// for (an inlining-chain scope link, a completeness claim):
        /// `encode_tmbc` must refuse the module by name (`NoTmbcWireImage`)
        /// while JSON and text still carry it.
        WireGap {
            which: u8,
        },
    }

    #[derive(Debug, Clone)]
    pub struct Spec {
        pub items: Vec<Item>,
        pub license: License,
        pub target: u8,
        pub lineage: bool,
    }

    // ---------------------------------------------------------------------
    // Strategies (every pick shrinks toward its first, simplest choice)
    // ---------------------------------------------------------------------

    fn layout_sc() -> impl Strategy<Value = Sc> {
        prop_oneof![
            Just(Sc::I32),
            Just(Sc::I64),
            Just(Sc::I8),
            Just(Sc::I16),
            Just(Sc::U8),
            Just(Sc::U16),
            Just(Sc::U32),
            Just(Sc::U64),
            Just(Sc::Bool),
            Just(Sc::F32),
            Just(Sc::F64),
        ]
    }

    fn any_sc() -> impl Strategy<Value = Sc> {
        prop_oneof![
            4 => layout_sc(),
            1 => prop_oneof![
                Just(Sc::I128),
                Just(Sc::U128),
                Just(Sc::Char),
                Just(Sc::Usize),
                Just(Sc::Isize),
            ],
        ]
    }

    fn int_sc() -> impl Strategy<Value = Sc> {
        prop_oneof![
            Just(Sc::I32),
            Just(Sc::I64),
            Just(Sc::I8),
            Just(Sc::I16),
            Just(Sc::U8),
            Just(Sc::U16),
            Just(Sc::U32),
            Just(Sc::U64),
        ]
    }

    fn layout_pick() -> impl Strategy<Value = Layout> {
        prop_oneof![
            Just(Layout::None),
            Just(Layout::Direct),
            Just(Layout::Niche),
            Just(Layout::Untagged),
            Just(Layout::SelfContradicting),
        ]
    }

    fn struct_item() -> impl Strategy<Value = Item> {
        (vec(layout_sc(), 1..=4), 0u8..4, any::<bool>(), any::<i8>()).prop_map(
            |(fields, repr, declared, seed)| Item::Struct {
                fields,
                repr,
                declared,
                seed,
            },
        )
    }

    fn tuple_item() -> impl Strategy<Value = Item> {
        (vec(layout_sc(), 1..=3), any::<bool>(), any::<i8>()).prop_map(
            |(fields, declared, seed)| Item::Tuple {
                fields,
                declared,
                seed,
            },
        )
    }

    fn array_item() -> impl Strategy<Value = Item> {
        (layout_sc(), 0u8..=4, any::<bool>(), any::<i8>()).prop_map(|(elem, len, splat, seed)| {
            Item::Array {
                elem,
                len,
                splat,
                seed,
            }
        })
    }

    fn enum_item() -> impl Strategy<Value = Item> {
        (
            vec(vec(layout_sc(), 0..=2), 1..=3),
            any::<bool>(),
            proptest::option::of(0u8..5),
            layout_pick(),
            proptest::bool::weighted(0.2),
            any::<i8>(),
        )
            .prop_map(
                |(variants, explicit, repr, layout, field_names, seed)| Item::Enum {
                    variants,
                    explicit,
                    repr,
                    layout,
                    field_names,
                    seed,
                },
            )
    }

    fn record_item() -> impl Strategy<Value = Item> {
        (
            vec(any_sc(), 1..=3),
            proptest::bool::weighted(0.2),
            any::<i8>(),
        )
            .prop_map(|(fields, offsets, seed)| Item::Record {
                fields,
                offsets,
                seed,
            })
    }

    fn closure_item() -> impl Strategy<Value = Item> {
        (vec(any_sc(), 0..=2), any::<i8>())
            .prop_map(|(captures, seed)| Item::Closure { captures, seed })
    }

    fn collection_item() -> impl Strategy<Value = Item> {
        (int_sc(), proptest::option::of(any::<bool>()), 0u8..=4)
            .prop_map(|(elem, set, len)| Item::Collection { elem, set, len })
    }

    fn global_item() -> impl Strategy<Value = Item> {
        (
            (
                any_sc(),
                any::<bool>(),
                proptest::option::of(0u8..4),
                0u8..9,
                0u8..3,
            ),
            (
                any::<bool>(),
                any::<bool>(),
                proptest::option::of(0u8..5),
                any::<bool>(),
                any::<i8>(),
            ),
        )
            .prop_map(
                |(
                    (ty, init, tls, linkage, visibility),
                    (section, retained, align_log2, mutable, seed),
                )| Item::Global {
                    ty,
                    init,
                    tls,
                    linkage,
                    visibility,
                    section,
                    retained,
                    align_log2,
                    mutable,
                    seed,
                },
            )
    }

    fn refine_item() -> impl Strategy<Value = Item> {
        (int_sc(), 0u8..8, any::<i8>(), 0u8..16).prop_map(|(base, pred, lo, width)| Item::Refine {
            base,
            pred,
            lo,
            width,
        })
    }

    fn dialect_op_item() -> impl Strategy<Value = Item> {
        (vec(0u8..7, 0..=4), 0u8..3, any::<i8>()).prop_map(|(attrs, version, seed)| {
            Item::DialectOp {
                attrs,
                version,
                seed,
            }
        })
    }

    fn proof_item() -> impl Strategy<Value = Item> {
        (
            (0u8..16, 0u8..5, any::<bool>(), any::<bool>(), any::<bool>()),
            (
                proptest::option::of(0u8..7),
                vec(0u8..3, 0..=2),
                vec(0u8..20, 0..=4),
            ),
        )
            .prop_map(
                |(
                    (kind, status, formula, scoped, source),
                    (evidence, diagnostics, annotations),
                )| Item::Proof {
                    kind,
                    status,
                    formula,
                    scoped,
                    source,
                    evidence,
                    diagnostics,
                    annotations,
                },
            )
    }

    fn metadata_item() -> impl Strategy<Value = Item> {
        (
            (
                any::<bool>(),
                proptest::option::of(0u8..4),
                any::<bool>(),
                any::<bool>(),
                any::<bool>(),
                0u8..12,
            ),
            (
                0u8..3,
                any::<bool>(),
                any::<bool>(),
                proptest::option::of(0u8..5),
                0u8..3,
            ),
        )
            .prop_map(
                |(
                    (display_path, producer, names, scopes, spans, conv),
                    (visibility, section, retained, param, ret_ext),
                )| Item::Metadata {
                    display_path,
                    producer,
                    names,
                    scopes,
                    spans,
                    conv,
                    visibility,
                    section,
                    retained,
                    param,
                    ret_ext,
                },
            )
    }

    fn import_item() -> impl Strategy<Value = Item> {
        (any::<bool>(), proptest::option::of(0u8..4), any::<u8>())
            .prop_map(|(v3, producer, seed)| Item::Import { v3, producer, seed })
    }

    pub fn item() -> BoxedStrategy<Item> {
        prop_oneof![
            struct_item(),
            tuple_item(),
            array_item(),
            enum_item(),
            record_item(),
            closure_item(),
            collection_item(),
            global_item(),
            (1u8..16).prop_map(|roles| Item::Handle { roles }),
            refine_item(),
            (0u8..3, 0u8..3).prop_map(|(name, version)| Item::DialectType { name, version }),
            dialect_op_item(),
            proof_item(),
            metadata_item(),
            import_item(),
            (0u8..6).prop_map(|which| Item::InstWireBatch { which }),
            (0u8..2).prop_map(|which| Item::WireGap { which }),
        ]
        .boxed()
    }

    pub fn spec() -> impl Strategy<Value = Spec> {
        (
            vec(item(), 1..=6),
            prop_oneof![
                Just(License::All),
                Just(License::None),
                Just(License::Partial)
            ],
            0u8..3,
            any::<bool>(),
        )
            .prop_map(|(items, license, target, lineage)| Spec {
                items,
                license,
                target,
                lineage,
            })
    }

    // ---------------------------------------------------------------------
    // Materialization
    // ---------------------------------------------------------------------

    /// A materialized module, the lineage sidecar bound to its proof tables
    /// (when the spec asks for one), the construct tags it exercises, and —
    /// when a `WireGap` item placed one — the text the writer's refusal must
    /// name.
    pub struct Built {
        pub module: Module,
        pub lineage: Option<ProofLineageManifest>,
        pub tags: BTreeSet<&'static str>,
        pub wire_gap: Option<&'static str>,
        /// A construct the pinned WRITER encodes but the pinned READER
        /// refuses (today: a zero- or one-copy `Constant::Splat`, which the
        /// one-spelling rule spells `Constant::Array`), with the text every
        /// reader's refusal must name.
        pub decode_refusal: Option<&'static str>,
    }

    struct Body {
        params: Vec<(ValueId, Ty)>,
        nodes: Vec<InstrNode>,
        next: u32,
    }

    impl Body {
        fn new(params: &[Ty]) -> Self {
            let params: Vec<(ValueId, Ty)> = params
                .iter()
                .enumerate()
                .map(|(i, ty)| (ValueId::new(i as u32), ty.clone()))
                .collect();
            let next = params.len() as u32;
            Self {
                params,
                nodes: Vec::new(),
                next,
            }
        }

        fn arg(&self, i: usize) -> ValueId {
            self.params[i].0
        }

        fn fresh(&mut self) -> ValueId {
            let v = ValueId::new(self.next);
            self.next += 1;
            v
        }

        fn val(&mut self, inst: Inst) -> ValueId {
            let v = self.fresh();
            self.nodes.push(InstrNode::new(inst).with_result(v));
            v
        }

        fn konst(&mut self, sc: Sc, seed: i8) -> ValueId {
            self.val(Inst::Const {
                ty: sc.ty(),
                value: sc.constant(seed),
            })
        }
    }

    struct Cx {
        m: Module,
        tags: BTreeSet<&'static str>,
        file: Option<u32>,
        /// The FIRST wire gap placed: `wire_identity_blocker` walks the
        /// functions' instructions first, then scopes, then the completeness
        /// claim, so the needle is the first gap in that order.
        wire_gaps: Vec<(u8, &'static str)>,
        decode_refusal: Option<&'static str>,
    }

    impl Cx {
        fn tag(&mut self, tag: &'static str) {
            self.tags.insert(tag);
        }

        fn file(&mut self) -> u32 {
            if let Some(file) = self.file {
                return file;
            }
            let file = self
                .m
                .intern_file("src/prop.rs")
                .expect("Module::intern_file: test fixture");
            self.file = Some(file);
            file
        }

        /// One-block function: the parameters are the entry block's
        /// parameters; `body` appends instructions and names the returned
        /// values; `configure` sets function-level metadata before the
        /// function is added, so claim annotations synthesize their
        /// obligations exactly as a producer's would.
        fn define(
            &mut self,
            name: String,
            params: Vec<Ty>,
            returns: Vec<Ty>,
            body: impl FnOnce(&mut Body) -> Vec<ValueId>,
            configure: impl FnOnce(&mut Function),
        ) -> FuncId {
            let ty = self
                .m
                .add_func_type(FuncTy {
                    params: params.clone(),
                    returns,
                    abi: None,
                    is_vararg: false,
                })
                .expect("Module::add_func_type: test fixture");
            let id = FuncId::new(self.m.functions.len() as u32);
            let mut func = Function::new(id, name, ty, BlockId::new(0));
            let mut b = Body::new(&params);
            let values = body(&mut b);
            let mut block = Block::new(BlockId::new(0));
            block.params = b.params;
            block.body = b.nodes;
            block.body.push(InstrNode::new(Inst::Return { values }));
            func.blocks.push(block);
            configure(&mut func);
            self.m
                .try_add_function(func)
                .expect("Module::try_add_function: test fixture");
            id
        }

        fn declare(&mut self, name: &str, ty: FuncTy, configure: impl FnOnce(&mut Function)) {
            if self.m.functions.iter().any(|f| f.name == name) {
                return;
            }
            let ty = self
                .m
                .add_func_type(ty)
                .expect("Module::add_func_type: test fixture");
            let id = FuncId::new(self.m.functions.len() as u32);
            let mut func = Function::new(id, name, ty, BlockId::new(0));
            configure(&mut func);
            self.m
                .try_add_function(func)
                .expect("Module::try_add_function: test fixture");
        }

        fn global(&mut self, name: String, ty: Ty, initializer: Option<Constant>) -> GlobalId {
            self.m.globals.push(Global {
                name,
                ty,
                mutable: false,
                initializer,
                linkage: Linkage::Internal,
                tls: None,
                align: None,
                section: None,
                visibility: Visibility::Default,
                retained: false,
            });
            GlobalId::new(self.m.globals.len() as u32 - 1)
        }

        fn ensure_target(&mut self) {
            if self.m.target_info.is_none() {
                self.m.target_info = Some(darwin());
            }
        }
    }

    fn darwin() -> TargetInfo {
        TargetInfo {
            triple: "aarch64-apple-darwin".into(),
            pointer_size: 8,
            endianness: Endianness::Little,
            abi: Some("aapcs64".into()),
            struct_passing: Default::default(),
        }
    }

    fn linux() -> TargetInfo {
        TargetInfo {
            triple: "x86_64-unknown-linux-gnu".into(),
            pointer_size: 8,
            endianness: Endianness::Little,
            abi: Some("sysv64".into()),
            struct_passing: Default::default(),
        }
    }

    fn align_up(value: u64, align: u64) -> u64 {
        value.div_ceil(align) * align
    }

    /// C layout of `fields` starting at `start`: (offsets, end, align).
    fn natural_layout(fields: &[Sc], start: u64) -> (Vec<u64>, u64, u64) {
        let mut offset = start;
        let mut align = 1;
        let mut offsets = Vec::with_capacity(fields.len());
        for field in fields {
            let a = field.natural();
            offset = align_up(offset, a);
            offsets.push(offset);
            offset += a;
            align = align.max(a);
        }
        (offsets, offset, align)
    }

    fn producer_of(pick: u8) -> Producer {
        match pick {
            0 => Producer::TRust,
            1 => Producer::Clean,
            2 => Producer::TrustIr,
            _ => Producer::TSwift,
        }
    }

    fn visibility_of(pick: u8) -> Visibility {
        match pick {
            0 => Visibility::Default,
            1 => Visibility::Hidden,
            _ => Visibility::Protected,
        }
    }

    pub fn materialize(spec: &Spec) -> Built {
        let mut cx = Cx {
            m: Module::new("tmbc_prop_constructs"),
            tags: BTreeSet::new(),
            file: None,
            wire_gaps: Vec::new(),
            decode_refusal: None,
        };
        cx.m.target_info = match spec.target {
            0 => None,
            1 => Some(darwin()),
            _ => Some(linux()),
        };
        for (i, item) in spec.items.iter().enumerate() {
            materialize_item(&mut cx, i, item);
        }

        // v41 codegen license over the bodied functions.
        for (bodied, func) in
            cx.m.functions
                .iter_mut()
                .filter(|f| !f.is_declaration())
                .enumerate()
        {
            let stamp = match spec.license {
                License::All => true,
                License::None => false,
                License::Partial => bodied.is_multiple_of(2),
            };
            if stamp {
                func.body_gate = Some(if bodied % 3 == 2 {
                    BodyGate::Ungated
                } else {
                    BodyGate::gated("trust-cg-roundtrip-prop")
                });
            }
        }
        let gates: Vec<&'static str> =
            cx.m.functions
                .iter()
                .filter_map(|func| match &func.body_gate {
                    Some(BodyGate::Gated { .. }) => Some("meta.body_gate_gated_v41"),
                    Some(BodyGate::Ungated) => Some("meta.body_gate_ungated_v41"),
                    None => None,
                })
                .collect();
        cx.tags.extend(gates);

        let lineage = (spec.lineage && !cx.m.proof_obligations.is_empty()).then(|| {
            cx.tags.insert("proof.lineage_sidecar");
            lineage_for(&cx.m)
        });
        if !cx.m.tuple_layouts.is_empty() {
            cx.m.validate_tuple_layouts()
                .expect("the generator declares only coherent tuple layouts");
        }
        // `wire_identity_blocker` reports a scope-chain link before a
        // completeness claim (since v51 no instruction is a gap).
        let wire_gap = cx
            .wire_gaps
            .iter()
            .min_by_key(|(which, _)| *which)
            .map(|(_, needle)| *needle);
        Built {
            module: cx.m,
            lineage,
            tags: cx.tags,
            wire_gap,
            decode_refusal: cx.decode_refusal,
        }
    }

    /// A one-node lineage sidecar over the module's own proof tables.
    fn lineage_for(module: &Module) -> ProofLineageManifest {
        let mut node = ProofLineageNode::new(
            ProofLineageId::new(0),
            ProofTransform::new(
                ProofTransformStage::TrustIrLowering,
                "trust-cg-roundtrip-prop",
                "TrustCg",
                "0",
            ),
            ProofDigest::sha256([0x51; 32]),
            // Not `module.stable_digest()`: a module carrying a wire gap has
            // no canonical image to digest (the writer panics on one).
            ProofDigest::sha256([0x52; 32]),
        );
        node.obligations = module.proof_obligations.iter().map(|o| o.id).collect();
        node.certificates = module
            .proof_certificates
            .iter()
            .map(ProofCertificate::lineage_ref)
            .collect();
        let mut manifest = ProofLineageManifest::new();
        manifest.nodes.push(node);
        manifest.roots.push(ProofLineageId::new(0));
        manifest
    }

    fn materialize_item(cx: &mut Cx, i: usize, item: &Item) {
        match item {
            Item::Struct {
                fields,
                repr,
                declared,
                seed,
            } => materialize_struct(cx, i, fields, *repr, *declared, *seed),
            Item::Tuple {
                fields,
                declared,
                seed,
            } => {
                cx.tag("tuple");
                let tty = Ty::Tuple(fields.iter().map(|sc| sc.ty()).collect());
                if *declared {
                    cx.tag("tuple.declared_layout_v42");
                    cx.ensure_target();
                    let (offsets, end, align) = natural_layout(fields, 0);
                    let tuple_type =
                        cx.m.add_type(tty.clone())
                            .expect("Module::add_type: test fixture");
                    cx.m.tuple_layouts.push(TupleLayoutDescriptor {
                        tuple_type,
                        size: align_up(end, align),
                        align,
                        field_offsets: offsets,
                    });
                }
                let tty2 = tty.clone();
                cx.define(
                    format!("tuple_first{i}"),
                    vec![tty.clone()],
                    vec![fields[0].ty()],
                    move |b| {
                        let t = b.arg(0);
                        vec![b.val(Inst::ExtractField {
                            ty: tty2,
                            aggregate: t,
                            field: 0,
                        })]
                    },
                    |_| {},
                );
                cx.global(
                    format!("G_T{i}"),
                    tty,
                    Some(Constant::Aggregate(
                        fields.iter().map(|sc| sc.constant(*seed)).collect(),
                    )),
                );
            }
            Item::Array {
                elem,
                len,
                splat,
                seed,
            } => {
                cx.tag("array");
                let elem_id =
                    cx.m.add_type(elem.ty())
                        .expect("Module::add_type: test fixture");
                let aty = Ty::Array(elem_id, u64::from(*len));
                let init = if *splat {
                    cx.tag("constant.splat_v50");
                    if *len <= 1 {
                        // The pinned writer encodes it; the pinned reader
                        // refuses it (SPEC_RATIFICATIONS §3.1).
                        cx.tag("constant.splat_non_canonical");
                        cx.decode_refusal
                            .get_or_insert("non-canonical Constant::Splat");
                    }
                    Constant::Splat {
                        elem: Box::new(elem.constant(*seed)),
                        len: u64::from(*len),
                    }
                } else {
                    cx.tag("constant.array");
                    Constant::Array(
                        (0..*len)
                            .map(|k| elem.constant(seed.wrapping_add(k as i8)))
                            .collect(),
                    )
                };
                cx.global(format!("G_A{i}"), aty.clone(), Some(init));
                let elem = *elem;
                cx.define(
                    format!("array_splat{i}"),
                    vec![elem.ty()],
                    vec![elem.ty()],
                    move |b| {
                        let x = b.arg(0);
                        let a = b.val(Inst::ArraySplat { ty: aty, value: x });
                        let index = b.konst(Sc::I64, 0);
                        vec![b.val(Inst::ExtractElement {
                            ty: elem.ty(),
                            array: a,
                            index,
                        })]
                    },
                    |_| {},
                );
                cx.tag("inst.array_splat_v50");
            }
            Item::Enum {
                variants,
                explicit,
                repr,
                layout,
                field_names,
                seed,
            } => materialize_enum(
                cx,
                i,
                variants,
                *explicit,
                *repr,
                *layout,
                *field_names,
                *seed,
            ),
            Item::Record {
                fields,
                offsets,
                seed,
            } => {
                cx.tag("record");
                if *offsets {
                    cx.tag("record.offsets");
                }
                let (offs, _, _) = natural_layout(fields, 0);
                let id = cx.m.add_record(RecordDef {
                    id: RecordId::new(cx.m.records.len() as u32),
                    name: format!("R{i}"),
                    fields: fields
                        .iter()
                        .enumerate()
                        .map(|(k, sc)| FieldDef {
                            name: format!("r{k}"),
                            ty: sc.ty(),
                            offset: offsets.then(|| offs[k]),
                        })
                        .collect(),
                });
                cx.global(
                    format!("G_R{i}"),
                    Ty::Record(id),
                    Some(Constant::Record(
                        fields
                            .iter()
                            .enumerate()
                            .map(|(k, sc)| (format!("r{k}"), sc.constant(*seed)))
                            .collect(),
                    )),
                );
                cx.tag("constant.record");
            }
            Item::Closure { captures, seed } => {
                cx.tag("closure");
                let body = cx.define(
                    format!("closure_body{i}"),
                    vec![Ty::I32],
                    vec![Ty::I32],
                    |b| vec![b.arg(0)],
                    |_| {},
                );
                let ft = cx.m.functions[body.index() as usize].ty;
                let id =
                    cx.m.add_closure_type(ClosureTy {
                        func: ft,
                        captures: captures.iter().map(|sc| sc.ty()).collect(),
                    })
                    .expect("Module::add_closure_type: test fixture");
                cx.global(
                    format!("G_C{i}"),
                    Ty::Closure(id),
                    Some(Constant::Closure {
                        func: body,
                        captures: captures.iter().map(|sc| sc.constant(*seed)).collect(),
                    }),
                );
                cx.global(
                    format!("G_FN{i}"),
                    Ty::Func(ft),
                    Some(Constant::FnDef(body)),
                );
                cx.tag("constant.closure");
            }
            Item::Collection { elem, set, len } => {
                let elem_id =
                    cx.m.add_type(elem.ty())
                        .expect("Module::add_type: test fixture");
                let items: Vec<Constant> =
                    (0..*len).map(|k| Constant::Int(i128::from(k))).collect();
                let (ty, init) = match set {
                    None => {
                        cx.tag("sequence");
                        (Ty::Sequence(elem_id), Constant::Sequence(items))
                    }
                    Some(bitset) => {
                        let repr = if *bitset {
                            cx.tag("set.bitset");
                            SetRepr::Bitset
                        } else {
                            cx.tag("set.boxed");
                            SetRepr::Boxed
                        };
                        (Ty::Set(elem_id, repr), Constant::Set(items))
                    }
                };
                cx.global(format!("G_Q{i}"), ty, Some(init));
            }
            Item::Global {
                ty,
                init,
                tls,
                linkage,
                visibility,
                section,
                retained,
                align_log2,
                mutable,
                seed,
            } => {
                cx.tag("global");
                let initializer = init.then(|| ty.constant(*seed));
                if initializer.is_some() {
                    cx.tag("global.initializer");
                }
                let id = cx.global(format!("G{i}"), ty.ty(), initializer);
                let g = &mut cx.m.globals[id.index() as usize];
                g.mutable = *mutable;
                g.tls = tls.map(|t| match t {
                    0 => TlsModel::LocalExec,
                    1 => TlsModel::InitialExec,
                    2 => TlsModel::GeneralDynamic,
                    _ => TlsModel::LocalDynamic,
                });
                g.linkage = match linkage {
                    0 => Linkage::Internal,
                    1 => Linkage::External,
                    2 => Linkage::Private,
                    3 => Linkage::Weak,
                    4 => Linkage::LinkOnce,
                    5 => Linkage::WeakOdr,
                    6 => Linkage::LinkOnceOdr,
                    7 => Linkage::AvailableExternally,
                    _ => Linkage::ExternalWeak,
                };
                g.visibility = visibility_of(*visibility);
                g.section = section.then(|| format!("__DATA,__prop{i}"));
                g.retained = *retained;
                g.align = align_log2.map(|k| 1u32 << k);
                let tls_set = g.tls.is_some();
                let attrs_set =
                    g.visibility != Visibility::Default || g.section.is_some() || g.retained;
                let align_set = g.align.is_some();
                if tls_set {
                    cx.tag("global.tls");
                }
                if attrs_set {
                    cx.tag("global.symbol_attrs");
                }
                if align_set {
                    cx.tag("global.align");
                }
                cx.define(
                    format!("global_addr{i}"),
                    vec![],
                    vec![Ty::Ptr],
                    move |b| vec![b.val(Inst::GlobalAddr { global: id })],
                    |_| {},
                );
            }
            Item::Handle { roles } => {
                cx.tag("handle_v43");
                let pin = &trust_ir_build::TRUSTED_HANDLE_RUNTIMES[0];
                let handle = pin.handle_ty();
                for (k, entry) in pin.entry_points.iter().enumerate() {
                    if roles & (1 << (k % 8)) == 0 {
                        continue;
                    }
                    cx.declare(entry.symbol, pin.func_ty(entry), |func| {
                        func.calling_conv = pin.calling_conv;
                        func.display_path = Some(entry.def_path.to_string());
                    });
                }
                let h2 = handle.clone();
                cx.define(
                    format!("handle_transport{i}"),
                    vec![handle.clone()],
                    vec![handle],
                    move |b| {
                        let h = b.arg(0);
                        vec![b.val(Inst::Copy { ty: h2, operand: h })]
                    },
                    |_| {},
                );
            }
            Item::Refine {
                base,
                pred,
                lo,
                width,
            } => materialize_refinement(cx, i, *base, *pred, *lo, *width),
            Item::DialectType { name, version } => {
                cx.tag("dialect.type_v39");
                let nominal = Ty::Dialect(Box::new(DialectTy::new(
                    "example",
                    ["value", "state", "token"][*name as usize],
                    u32::from(*version) + 1,
                )));
                let n2 = nominal.clone();
                cx.define(
                    format!("nominal{i}"),
                    vec![nominal.clone()],
                    vec![nominal],
                    move |b| {
                        let x = b.arg(0);
                        vec![b.val(Inst::Copy { ty: n2, operand: x })]
                    },
                    |_| {},
                );
            }
            Item::DialectOp {
                attrs,
                version,
                seed,
            } => {
                cx.tag("dialect.op");
                let mut op = DialectInst::new("verif", format!("op{i}"))
                    .with_result_ty(Ty::I32)
                    .with_version(u32::from(*version) + 1);
                for (k, attr) in attrs.iter().enumerate() {
                    let value = match attr {
                        0 => AttrValue::I64(i64::from(*seed)),
                        1 => AttrValue::U64(u64::from(seed.unsigned_abs())),
                        2 => AttrValue::F64(f64::from(*seed) / 8.0),
                        3 => AttrValue::Bool(*seed < 0),
                        4 => AttrValue::Str(format!("s{seed}")),
                        5 => AttrValue::Bytes(vec![seed.unsigned_abs(), 0, 0xFF]),
                        _ => AttrValue::Ty(Ty::I32),
                    };
                    op = op.with_attr(format!("a{k}"), value);
                }
                cx.define(
                    format!("dialect_op{i}"),
                    vec![Ty::I32],
                    vec![Ty::I32],
                    move |b| {
                        let x = b.arg(0);
                        vec![b.val(Inst::DialectOp(Box::new(op.with_operand(x))))]
                    },
                    |_| {},
                );
            }
            Item::Proof {
                kind,
                status,
                formula,
                scoped,
                source,
                evidence,
                diagnostics,
                annotations,
            } => materialize_proof(
                cx,
                i,
                ProofPicks {
                    kind: *kind,
                    status: *status,
                    formula: *formula,
                    scoped: *scoped,
                    source: *source,
                    evidence: *evidence,
                },
                diagnostics,
                annotations,
            ),
            Item::Metadata {
                display_path,
                producer,
                names,
                scopes,
                spans,
                conv,
                visibility,
                section,
                retained,
                param,
                ret_ext,
            } => {
                let picks = MetaPicks {
                    display_path: *display_path,
                    producer: *producer,
                    names: *names,
                    scopes: *scopes,
                    spans: *spans,
                    conv: *conv,
                    visibility: *visibility,
                    section: *section,
                    retained: *retained,
                    param: *param,
                    ret_ext: *ret_ext,
                };
                materialize_metadata(cx, i, &picks);
            }
            Item::Import { v3, producer, seed } => {
                cx.tag(if *v3 {
                    "meta.import_v3_v44"
                } else {
                    "meta.import_v2"
                });
                let mut import =
                    ModuleImport::new(format!("dep{i}"), ProofDigest::sha256([*seed; 32]))
                        .with_scheme(if *v3 {
                            IdentityScheme::V3
                        } else {
                            IdentityScheme::V2
                        });
                if let Some(p) = producer {
                    import = import.with_producer(producer_of(*p));
                }
                cx.m.intern_import(import)
                    .expect("Module::intern_import: test fixture");
            }
            Item::InstWireBatch { which } => materialize_inst_wire_batch(cx, i, *which),
            Item::WireGap { which } => materialize_wire_gap(cx, i, *which),
        }
    }

    /// One member of TrustIR's v51 INST wire batch: the writer encodes it
    /// (raising the header to 51 only for a module that carries one), so it
    /// records no wire gap and the module goes through the binary lane.
    fn materialize_inst_wire_batch(cx: &mut Cx, i: usize, which: u8) {
        use trust_ir::{BinOp, UnOp};
        match which {
            0 => {
                cx.tag("inst_wire_batch.make_aggregate_struct");
                let id = cx.m.add_struct(StructDef {
                    origin: None,
                    id: StructId::new(cx.m.structs.len() as u32),
                    name: format!("Lit{i}"),
                    fields: vec![FieldDef {
                        name: "v".into(),
                        ty: Ty::I32,
                        offset: None,
                    }],
                    size: None,
                    align: None,
                    repr: StructRepr::Rust,
                });
                cx.define(
                    format!("struct_literal{i}"),
                    vec![Ty::I32],
                    vec![Ty::Struct(id)],
                    move |b| {
                        let x = b.arg(0);
                        vec![b.val(Inst::MakeAggregate {
                            ty: Ty::Struct(id),
                            variant: None,
                            fields: vec![x],
                        })]
                    },
                    |_| {},
                );
            }
            1 => {
                cx.tag("inst_wire_batch.make_aggregate_enum");
                let id = cx.m.add_enum(EnumDef::new(
                    trust_ir::EnumId::new(cx.m.enums.len() as u32),
                    format!("Opt{i}"),
                    vec![
                        EnumVariant {
                            name: "Some".into(),
                            fields: vec![Ty::I32],
                            field_names: Vec::new(),
                        },
                        EnumVariant {
                            name: "None".into(),
                            fields: Vec::new(),
                            field_names: Vec::new(),
                        },
                    ],
                ));
                cx.define(
                    format!("enum_literal{i}"),
                    vec![Ty::I32],
                    vec![Ty::Enum(id)],
                    move |b| {
                        let x = b.arg(0);
                        vec![b.val(Inst::MakeAggregate {
                            ty: Ty::Enum(id),
                            variant: Some(0),
                            fields: vec![x],
                        })]
                    },
                    |_| {},
                );
            }
            2 | 3 => {
                let copy = which == 2;
                cx.tag(if copy {
                    "inst_wire_batch.mem_copy"
                } else {
                    "inst_wire_batch.mem_set"
                });
                cx.define(
                    format!("bulk_memory{i}"),
                    vec![Ty::Ptr, Ty::Ptr],
                    vec![],
                    move |b| {
                        let (dst, src) = (b.arg(0), b.arg(1));
                        let bytes = b.konst(Sc::I64, 8);
                        let inst = if copy {
                            Inst::MemCopy {
                                dst,
                                src,
                                bytes,
                                overlap: false,
                            }
                        } else {
                            let byte = b.konst(Sc::U8, 0);
                            Inst::MemSet { dst, byte, bytes }
                        };
                        b.nodes.push(InstrNode::new(inst));
                        vec![]
                    },
                    |_| {},
                );
            }
            4 => {
                cx.tag("inst_wire_batch.bit_intrinsic");
                cx.define(
                    format!("count_zeros{i}"),
                    vec![Ty::I32],
                    vec![Ty::I32],
                    |b| {
                        let x = b.arg(0);
                        vec![b.val(Inst::UnOp {
                            op: UnOp::CtLz,
                            ty: Ty::I32,
                            operand: x,
                        })]
                    },
                    |_| {},
                );
            }
            _ => {
                cx.tag("inst_wire_batch.rotate");
                cx.define(
                    format!("rotate{i}"),
                    vec![Ty::I32, Ty::I32],
                    vec![Ty::I32],
                    |b| {
                        let (x, y) = (b.arg(0), b.arg(1));
                        vec![b.val(Inst::BinOp {
                            op: BinOp::RotL,
                            ty: Ty::I32,
                            lhs: x,
                            rhs: y,
                        })]
                    },
                    |_| {},
                );
            }
        }
    }

    /// One construct the pinned writer has no wire image for, and the text
    /// `encode_tmbc`'s refusal must name.
    fn materialize_wire_gap(cx: &mut Cx, i: usize, which: u8) {
        use trust_ir::{InlinedAt, ModuleCompleteness, UnloweredRow};
        let needle = match which {
            0 => {
                cx.tag("wire_gap.inlined_scope_chain");
                let file = cx.file();
                let span = SourceSpan {
                    file,
                    line: 9,
                    col: 1,
                };
                let inlined = cx.define(
                    format!("inlined{i}"),
                    vec![Ty::I32],
                    vec![Ty::I32],
                    |b| vec![b.arg(0)],
                    |_| {},
                );
                cx.m.functions[inlined.index() as usize].scopes = Some(vec![
                    ScopeData {
                        parent: None,
                        span: Some(span),
                        inlined_at: None,
                    },
                    ScopeData {
                        parent: Some(0),
                        span: Some(span),
                        inlined_at: Some(InlinedAt {
                            span,
                            callee: "prop::callee".into(),
                        }),
                    },
                ]);
                "inlining chain"
            }
            _ => {
                cx.tag("wire_gap.completeness_claim");
                cx.m.completeness = Some(if i.is_multiple_of(2) {
                    ModuleCompleteness::Complete
                } else {
                    ModuleCompleteness::Partial(vec![UnloweredRow {
                        symbol: format!("unlowered{i}"),
                        display_path: Some("prop::unlowered".into()),
                        reason: "generator".into(),
                    }])
                });
                "completeness"
            }
        };
        cx.wire_gaps.push((which, needle));
    }

    fn materialize_struct(
        cx: &mut Cx,
        i: usize,
        fields: &[Sc],
        repr: u8,
        declared: bool,
        seed: i8,
    ) {
        cx.tag("struct");
        let (offsets, end, align) = natural_layout(fields, 0);
        let repr = match repr {
            0 => StructRepr::Rust,
            1 => StructRepr::C,
            2 => StructRepr::Transparent,
            _ => StructRepr::Packed(1),
        };
        if repr != StructRepr::Rust {
            cx.tag("struct.repr");
        }
        if declared {
            cx.tag("struct.declared_layout");
        }
        let id = cx.m.add_struct(StructDef {
            id: StructId::new(cx.m.structs.len() as u32),
            name: format!("S{i}"),
            origin: None,
            fields: fields
                .iter()
                .enumerate()
                .map(|(k, sc)| FieldDef {
                    name: format!("f{k}"),
                    ty: sc.ty(),
                    offset: declared.then(|| offsets[k]),
                })
                .collect(),
            size: declared.then(|| align_up(end, align)),
            align: declared.then_some(align),
            repr,
        });
        let sty = Ty::Struct(id);
        let sty2 = sty.clone();
        cx.define(
            format!("struct_ops{i}"),
            vec![sty.clone()],
            vec![fields[0].ty()],
            move |b| {
                let s = b.arg(0);
                let e = b.val(Inst::ExtractField {
                    ty: sty2.clone(),
                    aggregate: s,
                    field: 0,
                });
                b.val(Inst::InsertField {
                    ty: sty2,
                    aggregate: s,
                    field: 0,
                    value: e,
                });
                vec![e]
            },
            |_| {},
        );
        cx.global(
            format!("G_S{i}"),
            sty,
            Some(Constant::Aggregate(
                fields.iter().map(|sc| sc.constant(seed)).collect(),
            )),
        );
        cx.tag("constant.aggregate");
    }

    #[allow(clippy::too_many_arguments)]
    fn materialize_enum(
        cx: &mut Cx,
        i: usize,
        variants: &[Vec<Sc>],
        explicit: bool,
        repr: Option<u8>,
        layout: Layout,
        field_names: bool,
        seed: i8,
    ) {
        cx.tag("enum");
        // `Untagged` describes exactly one variant; `Niche` needs a niche
        // lane in the untagged variant and at least one niched variant.
        let mut variants: Vec<Vec<Sc>> = variants.to_vec();
        match layout {
            Layout::Untagged => variants.truncate(1),
            Layout::Niche => {
                if variants.len() < 2 {
                    variants.push(Vec::new());
                }
                if variants[0].is_empty() {
                    variants[0].push(Sc::U8);
                }
            }
            _ => {}
        }
        let mut ed = EnumDef::new(
            trust_ir::EnumId::new(cx.m.enums.len() as u32),
            format!("E{i}"),
            variants
                .iter()
                .enumerate()
                .map(|(k, fields)| EnumVariant {
                    name: format!("V{k}"),
                    fields: fields.iter().map(|sc| sc.ty()).collect(),
                    field_names: if field_names {
                        (0..fields.len()).map(|n| format!("n{n}")).collect()
                    } else {
                        Vec::new()
                    },
                })
                .collect(),
        );
        if field_names && variants.iter().any(|v| !v.is_empty()) {
            cx.tag("enum.field_names");
        }
        if explicit {
            cx.tag("enum.explicit_discriminants");
            ed = ed.with_discriminants(
                (0..variants.len())
                    .map(|k| Some(i128::from(seed) + 7 * k as i128))
                    .collect(),
            );
        }
        if let Some(repr) = repr {
            cx.tag("enum.tag_repr");
            ed = ed.with_repr(match repr {
                0 => EnumTagRepr::I32,
                1 => EnumTagRepr::U8,
                2 => EnumTagRepr::I64,
                3 => EnumTagRepr::U128,
                _ => EnumTagRepr::I128,
            });
        }
        ed.layout = match layout {
            Layout::None => None,
            Layout::Direct | Layout::SelfContradicting => {
                let tag = ed
                    .canonical_tag_repr()
                    .map_or(1, EnumTagRepr::size_bytes)
                    .max(1);
                let mut align = tag;
                let mut end = tag;
                let offsets: Vec<Vec<u64>> = variants
                    .iter()
                    .map(|fields| {
                        let (offs, e, a) = natural_layout(fields, tag);
                        end = end.max(e);
                        align = align.max(a);
                        offs
                    })
                    .collect();
                let size = if layout == Layout::SelfContradicting {
                    cx.tag("enum.layout_self_contradicting");
                    // Not a multiple of the (at least 2-byte) align below.
                    align_up(end, align.max(2)) + 1
                } else {
                    cx.tag("enum.layout_direct");
                    align_up(end, align)
                };
                Some(EnumLayoutDescriptor {
                    encoding: EnumTagEncoding::Direct { tag_offset: 0 },
                    size,
                    align: if layout == Layout::SelfContradicting {
                        align.max(2)
                    } else {
                        align
                    },
                    variant_field_offsets: offsets,
                })
            }
            Layout::Niche => {
                cx.tag("enum.layout_niche");
                let (first, end, align) = natural_layout(&variants[0], 0);
                Some(EnumLayoutDescriptor {
                    encoding: EnumTagEncoding::Niche {
                        untagged_variant: 0,
                        niche_variants_start: 1,
                        niche_variants_end: variants.len() as u32 - 1,
                        niche_start: 2,
                        niche_offset: 0,
                        niche_ty: EnumTagRepr::U8,
                    },
                    size: align_up(end, align),
                    align,
                    variant_field_offsets: variants
                        .iter()
                        .enumerate()
                        .map(|(k, fields)| {
                            if k == 0 {
                                first.clone()
                            } else {
                                vec![0; fields.len()]
                            }
                        })
                        .collect(),
                })
            }
            Layout::Untagged => {
                cx.tag("enum.layout_untagged");
                let (offs, end, align) = natural_layout(&variants[0], 0);
                Some(EnumLayoutDescriptor {
                    encoding: EnumTagEncoding::Untagged,
                    size: align_up(end, align),
                    align,
                    variant_field_offsets: vec![offs],
                })
            }
        };
        let id = cx.m.add_enum(ed);
        let ety = Ty::Enum(id);
        let e2 = ety.clone();
        cx.define(
            format!("enum_transport{i}"),
            vec![ety.clone()],
            vec![ety.clone()],
            move |b| {
                let x = b.arg(0);
                vec![b.val(Inst::Copy { ty: e2, operand: x })]
            },
            |_| {},
        );
        // The interpreter's enum value spelling: `[tag, fields..]`.
        let mut value = vec![Constant::Int(0)];
        value.extend(variants[0].iter().map(|sc| sc.constant(seed)));
        cx.global(format!("G_E{i}"), ety, Some(Constant::Aggregate(value)));
    }

    fn materialize_refinement(cx: &mut Cx, i: usize, base: Sc, pred: u8, lo: i8, width: u8) {
        cx.tag("refinement");
        let lo = i128::from(lo);
        let hi = lo + i128::from(width);
        let interval =
            cx.m.intern_pred(Pred::Interval { lo, hi })
                .expect("Module::intern_pred: test fixture")
                .expect("interval");
        let pred_id = match pred {
            0 => {
                cx.tag("pred.interval");
                interval
            }
            1 => {
                cx.tag("pred.non_zero");
                cx.m.intern_pred(Pred::NonZero)
                    .expect("Module::intern_pred: test fixture")
                    .expect("non-zero")
            }
            2 => {
                cx.tag("pred.top");
                cx.m.intern_pred(Pred::Top)
                    .expect("Module::intern_pred: test fixture")
                    .expect("top")
            }
            3 => {
                cx.tag("pred.finite_set");
                cx.m.intern_pred(Pred::FiniteSet(vec![
                    Constant::Int(lo),
                    Constant::Int(hi + 1),
                ]))
                .expect("Module::intern_pred: test fixture")
                .expect("finite set")
            }
            4 | 5 => {
                let nonzero =
                    cx.m.intern_pred(Pred::NonZero)
                        .expect("Module::intern_pred: test fixture")
                        .expect("non-zero");
                let connective = if pred == 4 {
                    cx.tag("pred.conj");
                    Pred::Conj(vec![interval, nonzero])
                } else {
                    cx.tag("pred.disj");
                    Pred::Disj(vec![interval, nonzero])
                };
                cx.m.intern_pred(connective)
                    .expect("Module::intern_pred: test fixture")
                    .expect("connective")
            }
            6 => {
                cx.tag("pred.in_universe");
                let universe =
                    cx.m.intern_universe(Universe::IntRange { lo, hi })
                        .expect("Module::intern_universe: test fixture")
                        .expect("universe");
                cx.m.intern_pred(Pred::InUniverse(universe, Space::Index))
                    .expect("Module::intern_pred: test fixture")
                    .expect("in-universe")
            }
            _ => {
                cx.tag("pred.bottom");
                cx.m.intern_pred(Pred::Bottom)
                    .expect("Module::intern_pred: test fixture")
                    .expect("bottom")
            }
        };
        let base_id =
            cx.m.add_type(base.ty())
                .expect("Module::add_type: test fixture");
        let rty = Ty::Refine(base_id, pred_id);
        let r2 = rty.clone();
        cx.define(
            format!("refined{i}"),
            vec![rty.clone()],
            vec![rty],
            move |b| {
                let x = b.arg(0);
                vec![b.val(Inst::Copy { ty: r2, operand: x })]
            },
            |_| {},
        );
    }

    struct ProofPicks {
        kind: u8,
        status: u8,
        formula: bool,
        scoped: bool,
        source: bool,
        evidence: Option<u8>,
    }

    fn annotation_of(pick: u8, obligation: ProofId) -> ProofAnnotation {
        match pick {
            0 => ProofAnnotation::NoOverflow,
            1 => ProofAnnotation::InBounds,
            2 => ProofAnnotation::NotNull,
            3 => ProofAnnotation::DivNonZero,
            4 => ProofAnnotation::Pure,
            5 => ProofAnnotation::Terminates,
            6 => ProofAnnotation::BranchWeights(vec![3, 1]),
            7 => ProofAnnotation::BoundedOutput { lo: -1.0, hi: 1.0 },
            8 => ProofAnnotation::Aligned(16),
            9 => ProofAnnotation::BoundedLoop(8),
            10 => ProofAnnotation::ValueRange {
                lo: i128::MIN,
                hi: i128::MAX,
            },
            11 => ProofAnnotation::KnownBits {
                zeros: 0xF0,
                ones: 0x01,
            },
            12 => ProofAnnotation::AtomicOrdering(Ordering::SeqCst),
            13 => ProofAnnotation::DivergenceClass(Divergence::Uniform),
            14 => ProofAnnotation::Custom(ProofTag::new(7)),
            15 => ProofAnnotation::ProofRef(obligation),
            16 => ProofAnnotation::Tainted,
            17 => ProofAnnotation::NoPanic,
            18 => ProofAnnotation::FreshSymbolicHavoc,
            _ => ProofAnnotation::RegionHavocStore,
        }
    }

    fn materialize_proof(
        cx: &mut Cx,
        i: usize,
        picks: ProofPicks,
        diagnostics: &[u8],
        annotations: &[u8],
    ) {
        cx.tag("proof.obligation");
        // A `ProofRef` names the row this item appends, whose id is known
        // only after `add_function` synthesized the carrier's claim rows; a
        // placeholder is rebound below.
        let placeholder = ProofId::new(u32::MAX);
        let inst_annotation = annotations
            .first()
            .map(|pick| annotation_of(*pick, placeholder));
        let fn_annotations: Vec<ProofAnnotation> = annotations
            .iter()
            .skip(1)
            .map(|pick| annotation_of(*pick, placeholder))
            .collect();
        if !annotations.is_empty() {
            cx.tag("proof.annotation");
        }
        let carrier = cx.define(
            format!("proof_carrier{i}"),
            vec![Ty::I64],
            vec![Ty::I64],
            move |b| {
                let x = b.arg(0);
                let sum = b.fresh();
                let mut node = InstrNode::new(Inst::BinOp {
                    op: trust_ir::BinOp::Add,
                    ty: Ty::I64,
                    lhs: x,
                    rhs: x,
                })
                .with_result(sum);
                if let Some(proof) = inst_annotation {
                    node = node.with_proof(proof);
                }
                b.nodes.push(node);
                vec![sum]
            },
            move |func| func.proofs = fn_annotations,
        );
        let next =
            cx.m.proof_obligations
                .iter()
                .map(|o| o.id.index() + 1)
                .max()
                .unwrap_or(0);
        let id = ProofId::new(next);
        let carrier_func = &mut cx.m.functions[carrier.index() as usize];
        let (proofs, blocks) = (&mut carrier_func.proofs, &mut carrier_func.blocks);
        for proof in proofs
            .iter_mut()
            .chain(blocks[0].body.iter_mut().flat_map(|n| n.proofs.iter_mut()))
        {
            if *proof == ProofAnnotation::ProofRef(placeholder) {
                *proof = ProofAnnotation::ProofRef(id);
            }
        }
        let kind = match picks.kind {
            0 => ObligationKind::Precondition,
            1 => ObligationKind::Postcondition,
            2 => ObligationKind::LoopInvariant,
            3 => ObligationKind::TypeInvariant,
            4 => ObligationKind::RefinementType,
            5 => ObligationKind::TranslationValidation,
            6 => ObligationKind::MemorySafety,
            7 => ObligationKind::PanicFreedom,
            8 => ObligationKind::TemporalSafety,
            9 => ObligationKind::Liveness,
            10 => ObligationKind::ArithmeticSafety,
            11 => ObligationKind::BoundsCheck,
            12 => ObligationKind::GiveBackRefinement,
            13 => ObligationKind::Termination,
            14 => ObligationKind::Ownership,
            _ => {
                cx.tag("proof.obligation_custom_kind");
                ObligationKind::Custom {
                    namespace: "trust_cg.prop".into(),
                    name: format!("claim{i}"),
                }
            }
        };
        let status = match picks.status {
            0 => ProofStatus::Pending,
            1 => ProofStatus::Discharged,
            2 => ProofStatus::Failed,
            3 => ProofStatus::Trusted,
            _ => ProofStatus::Certified,
        };
        let mut obligation = ProofObligation::new(id, kind, status, format!("prop obligation {i}"));
        if picks.formula {
            cx.tag("proof.formula");
            obligation = obligation.with_formula(ProofFormula::smtlib2("(> x 0)", "Bool"));
        }
        if picks.scoped {
            obligation = obligation.with_function(carrier);
        }
        if picks.source {
            cx.tag("proof.source_identity");
            obligation = obligation.with_source(ProofObligationSourceIdentity::new(
                format!("rust:src/prop.rs::carrier{i}"),
                format!("assert:{i}"),
            ));
        }
        cx.m.proof_obligations.push(obligation);
        if let Some(evidence) = picks.evidence {
            cx.tag("proof.certificate");
            let evidence = match evidence {
                0 => ProofEvidence::SmtProof(vec![1, 2, 3]),
                1 => ProofEvidence::LeanProof("exact rfl".into()),
                2 => ProofEvidence::KaniHarness("#[kani::proof] fn check() {}".into()),
                3 => ProofEvidence::TranslationValidation {
                    rule_name: "const-fold".into(),
                    smt_hash: [0xAB; 32],
                },
                4 => ProofEvidence::Trusted("audited".into()),
                5 => ProofEvidence::InheritedFromCallee {
                    callee: carrier,
                    obligation: id,
                    external: None,
                },
                _ => ProofEvidence::GammaCrownBound {
                    epsilon: 0.001,
                    verified_layers: 3,
                },
            };
            cx.m.proof_certificates.push(ProofCertificate {
                obligation: id,
                prover: format!("prover{i}"),
                evidence,
                assurance: None,
            });
        }
        for (k, severity) in diagnostics.iter().enumerate() {
            cx.tag("proof.diagnostic");
            let mut diagnostic = ObligationDiagnostic::error(id, format!("diagnostic {i}.{k}"));
            diagnostic.severity = match severity {
                0 => DiagnosticSeverity::Error,
                1 => DiagnosticSeverity::Warning,
                _ => DiagnosticSeverity::Note,
            };
            if k.is_multiple_of(2) {
                let file = cx.file();
                diagnostic = diagnostic.with_location(SourceSpan {
                    file,
                    line: 7,
                    col: 3,
                });
            }
            if *severity != 0 {
                diagnostic = diagnostic.with_detail("counterexample: x = 0");
            }
            cx.m.obligation_diagnostics.push(diagnostic);
        }
    }

    struct MetaPicks {
        display_path: bool,
        producer: Option<u8>,
        names: bool,
        scopes: bool,
        spans: bool,
        conv: u8,
        visibility: u8,
        section: bool,
        retained: bool,
        param: Option<u8>,
        ret_ext: u8,
    }

    fn materialize_metadata(cx: &mut Cx, i: usize, picks: &MetaPicks) {
        cx.tag("meta.function");
        let file = (picks.spans || picks.scopes).then(|| cx.file());
        let span = move |line| file.map(|file| SourceSpan { file, line, col: 4 });
        let (spans, scopes) = (picks.spans, picks.scopes);
        let meta = cx.define(
            format!("meta{i}"),
            vec![Ty::I32],
            vec![Ty::I32],
            move |b| {
                let x = b.arg(0);
                let one = b.fresh();
                let sum = b.fresh();
                let mut c = InstrNode::new(Inst::Const {
                    ty: Ty::I32,
                    value: Constant::Int(1),
                })
                .with_result(one);
                let mut add = InstrNode::new(Inst::BinOp {
                    op: trust_ir::BinOp::Add,
                    ty: Ty::I32,
                    lhs: x,
                    rhs: one,
                })
                .with_result(sum);
                if let (true, Some(s2), Some(s3)) = (spans, span(2), span(3)) {
                    c = c.with_span(s2);
                    add = add.with_span(s3);
                }
                if scopes {
                    c = c.with_scope(1);
                    add = add.with_scope(0);
                }
                b.nodes.push(c);
                b.nodes.push(add);
                vec![sum]
            },
            |_| {},
        );
        let conventions = CallingConv::ALL;
        let func = &mut cx.m.functions[meta.index() as usize];
        if picks.display_path {
            func.display_path = Some(format!("prop::meta<{i}>"));
        }
        func.producer = picks.producer.map(producer_of);
        if picks.names {
            func.value_names = Some(vec![
                (ValueId::new(0), "x".to_string()),
                (ValueId::new(2), format!("sum, {i}")),
            ]);
        }
        if scopes {
            func.scopes = Some(vec![
                ScopeData {
                    parent: None,
                    span: span(1),
                    inlined_at: None,
                },
                ScopeData {
                    parent: Some(0),
                    span: span(2),
                    inlined_at: None,
                },
            ]);
        }
        func.calling_conv = conventions[picks.conv as usize % conventions.len()];
        func.visibility = visibility_of(picks.visibility);
        func.section = picks.section.then(|| "__TEXT,__prop".to_string());
        func.retained = picks.retained;
        if let Some(param) = picks.param {
            func.attrs.params = vec![ParamAttrs {
                ext: if param.is_multiple_of(2) {
                    ArgExt::SignExt
                } else {
                    ArgExt::ZeroExt
                },
                pass: match param {
                    0 | 1 => Some(PassMode::Direct),
                    2 => Some(PassMode::Cast {
                        pieces: vec![Ty::I32],
                    }),
                    _ => None,
                },
                noalias: param == 4,
                ..ParamAttrs::default()
            }];
        }
        func.attrs.ret = ParamAttrs {
            ext: match picks.ret_ext {
                0 => ArgExt::None,
                1 => ArgExt::ZeroExt,
                _ => ArgExt::SignExt,
            },
            ..ParamAttrs::default()
        };
        let tags = [
            (func.display_path.is_some(), "meta.display_path_v41"),
            (func.producer.is_some(), "meta.producer_v23"),
            (func.value_names.is_some(), "meta.value_names_v32"),
            (func.scopes.is_some(), "meta.scopes_v33"),
            (spans, "meta.spans"),
            (func.calling_conv != CallingConv::C, "meta.calling_conv"),
            (
                func.visibility != Visibility::Default || func.section.is_some() || func.retained,
                "meta.symbol_attrs_v45",
            ),
            (func.attrs.ret.ext != ArgExt::None, "meta.ret_attrs_v45"),
            (!func.attrs.params.is_empty(), "meta.param_attrs_v45"),
        ];
        for (on, tag) in tags {
            if on {
                cx.tag(tag);
            }
        }
    }

    // ---------------------------------------------------------------------
    // The property: an exact round trip through trust-cg's paths, or a
    // refusal the generator predicted, by name
    // ---------------------------------------------------------------------

    /// What one module did on each lane.
    #[derive(Debug, Default)]
    pub struct Lanes {
        pub binary_exact: bool,
        pub binary_refused_producer_omission: bool,
        pub binary_refused_wire_gap: bool,
        pub binary_refused_noncanonical: bool,
        pub text_exact: bool,
        pub text_refused: BTreeSet<TextLossKind>,
    }

    fn kinds(losses: &[TextLoss]) -> BTreeSet<TextLossKind> {
        losses.iter().map(TextLoss::kind).collect()
    }

    /// Drive `built` through trust-cg's binary, JSON and text writers and
    /// readers, with trust-ir's own binary reader and the MessagePack codec
    /// (which trust-cg never uses) as oracles. `Err` names the violated
    /// clause.
    pub fn check(built: &Built) -> Result<Lanes, String> {
        let m = &built.module;
        let mut lanes = Lanes::default();
        match (built.wire_gap, pipeline::encode_tmbc(m)) {
            (None, Ok(envelope)) => match built.decode_refusal {
                None => binary_lane(m, &envelope, &mut lanes)?,
                Some(needle) => {
                    // Written, then refused by EVERY reader, by name.
                    let payload = &envelope[8..];
                    let oracle = trust_ir::binary::deserialize_module(payload)
                        .map(|_| ())
                        .map_err(|e| e.to_string());
                    let reads = [
                        ("trust_ir::binary::deserialize_module", oracle),
                        (
                            "decode_tmbc",
                            pipeline::decode_tmbc(&envelope)
                                .map(|_| ())
                                .map_err(|e| e.to_string()),
                        ),
                        (
                            "load_module_from_bytes(TRUST_IR)",
                            pipeline::load_module_from_bytes(payload)
                                .map(|_| ())
                                .map_err(|e| e.to_string()),
                        ),
                    ];
                    for (entry, read) in reads {
                        match read {
                            Err(e) if e.contains(needle) => {}
                            other => {
                                return Err(format!(
                                    "{entry}: expected a `{needle}` refusal, got {other:?}"
                                ));
                            }
                        }
                    }
                    lanes.binary_refused_noncanonical = true;
                }
            },
            (Some(needle), Err(e)) => {
                let e = e.to_string();
                if !e.contains("no tMBC wire image") || !e.contains(needle) {
                    return Err(format!(
                        "encode_tmbc refused a `{needle}` module, but not by that name: {e}"
                    ));
                }
                lanes.binary_refused_wire_gap = true;
            }
            (Some(needle), Ok(_)) => {
                return Err(format!(
                    "encode_tmbc wrote an image for a module carrying `{needle}`, which the \
                     pinned writer has no wire tag for"
                ));
            }
            (None, Err(e)) => return Err(format!("encode_tmbc refused: {e}")),
        }
        serde_and_text_lanes(built, &mut lanes)?;
        Ok(lanes)
    }

    /// The binary lane over `envelope = encode_tmbc(m)`: trust-ir's reader
    /// is the oracle for the writer, then every trust-cg binary entry must
    /// either reproduce `m` and the bytes exactly or refuse the module as a
    /// producer omission exactly when the generator predicts one.
    fn binary_lane(m: &Module, envelope: &[u8], lanes: &mut Lanes) -> Result<(), String> {
        let payload = &envelope[8..];
        let header = u32::from_le_bytes(payload[8..12].try_into().expect("header word"));
        let oracle = trust_ir::binary::deserialize_module(payload)
            .map_err(|e| format!("trust-ir's reader refused trust-cg's bytes: {e}"))?;
        if &oracle != m {
            return Err("trust-ir's reader decodes trust-cg's bytes to another module".into());
        }
        let unstamped_body = m
            .functions
            .iter()
            .any(|f| !f.is_declaration() && f.body_gate.is_none());
        let predicted_refusal = header >= 41 && unstamped_body;
        let reads = [
            ("decode_tmbc", pipeline::decode_tmbc(envelope)),
            (
                "load_module_from_bytes(tMBC)",
                pipeline::load_module_from_bytes(envelope),
            ),
            (
                "load_module_from_bytes(TRUST_IR)",
                pipeline::load_module_from_bytes(payload),
            ),
            ("decode_binary(TRUST_IR)", pipeline::decode_binary(payload)),
        ];
        for (entry, read) in reads {
            match (read, predicted_refusal) {
                (Ok(back), false) => {
                    if &back != m {
                        return Err(format!("{entry}: binary round trip lost information"));
                    }
                    let again = pipeline::encode_tmbc(&back).map_err(|e| e.to_string())?;
                    if again != envelope {
                        return Err(format!("{entry}: tMBC bytes are not a fixed point"));
                    }
                }
                (Err(e), true) => {
                    let e = e.to_string();
                    if !e.contains("producer omission") {
                        return Err(format!(
                            "{entry}: v{header} blob with an unstamped body refused, but not as \
                             a producer omission: {e}"
                        ));
                    }
                }
                (Ok(_), true) => {
                    return Err(format!(
                        "{entry}: accepted a v{header} blob with an unstamped body (the \
                         decoded-provenance rule was not applied)"
                    ));
                }
                (Err(e), false) => return Err(format!("{entry}: refused a clean module: {e}")),
            }
        }
        if predicted_refusal {
            lanes.binary_refused_producer_omission = true;
        } else {
            lanes.binary_exact = true;
        }
        Ok(())
    }

    /// The JSON lane (the CLI's `--emit-json` spelling through trust-cg's
    /// reader, with MessagePack as the independent oracle), the text lane
    /// (`--emit-trust_ir` / `--format=text`), and the lineage sidecar.
    fn serde_and_text_lanes(built: &Built, lanes: &mut Lanes) -> Result<(), String> {
        let m = &built.module;
        if let Some(needle) = built.decode_refusal {
            // Every WRITER spells the non-canonical construct; every READER
            // refuses it — serde by the same name as the binary reader, the
            // text parser by its own.
            let json = serde_json::to_string_pretty(m).map_err(|e| e.to_string())?;
            let packed = rmp_serde::to_vec(m).map_err(|e| e.to_string())?;
            let reads = [
                (
                    "load_module_from_bytes(JSON)",
                    pipeline::load_module_from_bytes(json.as_bytes())
                        .map(|_| ())
                        .map_err(|e| e.to_string()),
                ),
                (
                    "rmp_serde (oracle)",
                    rmp_serde::from_slice::<Module>(&packed)
                        .map(|_| ())
                        .map_err(|e| e.to_string()),
                ),
            ];
            for (entry, read) in reads {
                match read {
                    Err(e) if e.contains(needle) => {}
                    other => {
                        return Err(format!(
                            "{entry}: expected a `{needle}` refusal, got {other:?}"
                        ));
                    }
                }
            }
            // The `#lossy` tripwire, when the module has a loss, fires first.
            let expected = if text_losses(m).is_empty() {
                "splat"
            } else {
                "LOSSILY"
            };
            match pipeline::parse_trust_ir_text(&pipeline::encode_trust_ir_text(m)) {
                Err(e) if e.to_string().contains(expected) => {}
                other => {
                    return Err(format!(
                        "the text reader must refuse a non-canonical splat by `{expected}`, \
                         got {:?}",
                        other.map(|_| ())
                    ));
                }
            }
            return Ok(());
        }
        // --- JSON: trust-cg's reader over the CLI's `--emit-json` spelling ---
        let json = serde_json::to_string_pretty(m).map_err(|e| e.to_string())?;
        let back = pipeline::load_module_from_bytes(json.as_bytes())
            .map_err(|e| format!("JSON reader refused: {e}"))?;
        if &back != m {
            return Err("JSON round trip lost information".into());
        }
        if serde_json::to_string_pretty(&back).map_err(|e| e.to_string())? != json {
            return Err("JSON is not a fixed point".into());
        }
        let packed = rmp_serde::to_vec(m).map_err(|e| e.to_string())?;
        let unpacked: Module = rmp_serde::from_slice(&packed).map_err(|e| e.to_string())?;
        if &unpacked != m {
            return Err("the MessagePack oracle disagrees".into());
        }
        if pipeline::load_module_from_bytes(&packed).is_ok() {
            return Err("trust-cg's reader accepted MessagePack bytes as a module".into());
        }

        // --- text: `--emit-trust_ir` writer, `--format=text` reader ---
        let text = pipeline::encode_trust_ir_text(m);
        let losses = text_losses(m);
        match pipeline::parse_trust_ir_text(&text) {
            Ok(back) if losses.is_empty() => {
                if &back != m {
                    return Err("text round trip lost information with no reported loss".into());
                }
                if pipeline::encode_trust_ir_text(&back) != text {
                    return Err("text is not a fixed point".into());
                }
                let canonical = trust_ir::format::canonical(m);
                let parsed = pipeline::parse_trust_ir_text(&canonical)
                    .map_err(|e| format!("canonical text refused: {e}"))?;
                if parsed != trust_ir::format::canonicalize(m) {
                    return Err("canonical text does not re-parse to canonicalize(m)".into());
                }
                lanes.text_exact = true;
            }
            Ok(_) => {
                return Err(format!(
                    "the text reader ACCEPTED a lossy dump (losses {:?}): the #lossy tripwire \
                     was laundered",
                    kinds(&losses)
                ));
            }
            Err(e) if !losses.is_empty() => {
                let e = e.to_string();
                if !e.contains("LOSSILY") {
                    return Err(format!(
                        "lossy text refused, but not by the #lossy marker: {e}"
                    ));
                }
                lanes.text_refused = kinds(&losses);
            }
            Err(e) => return Err(format!("the text reader refused a loss-free dump: {e}")),
        }

        // --- lineage sidecar: trust-ir's codec (trust-cg has no sidecar reader) ---
        if let Some(manifest) = &built.lineage {
            let bytes = trust_ir::binary::serialize_proof_lineage_manifest(manifest);
            let back = trust_ir::binary::deserialize_proof_lineage_manifest(&bytes)
                .map_err(|e| format!("lineage sidecar refused: {e:?}"))?;
            if &back != manifest
                || trust_ir::binary::serialize_proof_lineage_manifest(&back) != bytes
            {
                return Err("lineage sidecar binary round trip is not exact".into());
            }
            let json = serde_json::to_string_pretty(manifest).map_err(|e| e.to_string())?;
            let from_json: ProofLineageManifest =
                serde_json::from_str(&json).map_err(|e| e.to_string())?;
            let named = rmp_serde::to_vec_named(manifest).map_err(|e| e.to_string())?;
            let from_msgpack: ProofLineageManifest =
                rmp_serde::from_slice(&named).map_err(|e| e.to_string())?;
            if &from_json != manifest || &from_msgpack != manifest {
                return Err("lineage sidecar serde round trip is not exact".into());
            }
            if pipeline::load_module_from_bytes(&bytes).is_ok()
                || pipeline::load_module_from_bytes(json.as_bytes()).is_ok()
            {
                return Err("trust-cg's module reader accepted a lineage sidecar".into());
            }
        }
        Ok(())
    }
}

proptest! {
    #![proptest_config(ProptestConfig {
        cases: 256,
        .. ProptestConfig::default()
    })]

    /// L05-P7: every generated construct module round-trips EXACTLY through
    /// trust-cg's binary, JSON and text paths, or is refused by name where
    /// the generator predicts it (a v41+ blob with an unstamped body; a text
    /// dump carrying a construct the grammar cannot spell).
    #[test]
    fn construct_modules_round_trip_or_are_refused_by_name(spec in constructs::spec()) {
        let built = constructs::materialize(&spec);
        if let Err(violation) = constructs::check(&built) {
            prop_assert!(false, "{}", violation);
        }
    }
}

/// Every construct family the generator exists for is actually generated —
/// and both outcomes of every lane (exact, refused by name) actually occur —
/// over a fixed-seed sample, so the property above cannot pass vacuously on
/// a generator that stopped producing a family.
#[test]
fn construct_generator_covers_every_family_and_both_outcomes() {
    use proptest::strategy::{Strategy, ValueTree};
    use proptest::test_runner::TestRunner;
    use std::collections::{BTreeMap, BTreeSet};

    const FAMILIES: &[&str] = &[
        "struct",
        "struct.declared_layout",
        "struct.repr",
        "tuple",
        "tuple.declared_layout_v42",
        "array",
        "constant.array",
        "constant.splat_v50",
        "inst.array_splat_v50",
        "constant.aggregate",
        "enum",
        "enum.explicit_discriminants",
        "enum.tag_repr",
        "enum.field_names",
        "enum.layout_direct",
        "enum.layout_niche",
        "enum.layout_untagged",
        "enum.layout_self_contradicting",
        "record",
        "record.offsets",
        "constant.record",
        "closure",
        "constant.closure",
        "sequence",
        "set.bitset",
        "set.boxed",
        "global",
        "global.initializer",
        "global.tls",
        "global.symbol_attrs",
        "global.align",
        "handle_v43",
        "refinement",
        "pred.interval",
        "pred.non_zero",
        "pred.top",
        "pred.finite_set",
        "pred.conj",
        "pred.disj",
        "pred.in_universe",
        "pred.bottom",
        "dialect.type_v39",
        "dialect.op",
        "proof.obligation",
        "proof.obligation_custom_kind",
        "proof.formula",
        "proof.source_identity",
        "proof.certificate",
        "proof.diagnostic",
        "proof.annotation",
        "proof.lineage_sidecar",
        "meta.function",
        "meta.body_gate_gated_v41",
        "meta.body_gate_ungated_v41",
        "meta.display_path_v41",
        "meta.producer_v23",
        "meta.value_names_v32",
        "meta.scopes_v33",
        "meta.spans",
        "meta.calling_conv",
        "meta.symbol_attrs_v45",
        "meta.ret_attrs_v45",
        "meta.param_attrs_v45",
        "meta.import_v2",
        "meta.import_v3_v44",
        "inst_wire_batch.make_aggregate_struct",
        "inst_wire_batch.make_aggregate_enum",
        "inst_wire_batch.mem_copy",
        "inst_wire_batch.mem_set",
        "inst_wire_batch.bit_intrinsic",
        "inst_wire_batch.rotate",
        "wire_gap.inlined_scope_chain",
        "wire_gap.completeness_claim",
        "constant.splat_non_canonical",
    ];

    let mut runner = TestRunner::deterministic();
    let strategy = constructs::spec();
    let mut seen: BTreeSet<&'static str> = BTreeSet::new();
    let (mut binary_exact, mut binary_refused, mut text_exact) = (0usize, 0usize, 0usize);
    let (mut wire_gap_refused, mut noncanonical_refused) = (0usize, 0usize);
    let mut text_refused: BTreeMap<String, usize> = BTreeMap::new();
    let mut headers: BTreeSet<u32> = BTreeSet::new();
    const SAMPLES: usize = 512;
    for _ in 0..SAMPLES {
        let spec = strategy.new_tree(&mut runner).unwrap().current();
        let built = constructs::materialize(&spec);
        let lanes = constructs::check(&built)
            .unwrap_or_else(|violation| panic!("{violation}\nspec: {spec:#?}"));
        seen.extend(built.tags.iter().copied());
        binary_exact += usize::from(lanes.binary_exact);
        binary_refused += usize::from(lanes.binary_refused_producer_omission);
        wire_gap_refused += usize::from(lanes.binary_refused_wire_gap);
        noncanonical_refused += usize::from(lanes.binary_refused_noncanonical);
        text_exact += usize::from(lanes.text_exact);
        for kind in &lanes.text_refused {
            *text_refused.entry(format!("{kind:?}")).or_default() += 1;
        }
        if built.wire_gap.is_none() {
            let bytes = trust_ir::binary::serialize_module(&built.module)
                .expect("serialize_module: test fixture");
            headers.insert(u32::from_le_bytes(bytes[8..12].try_into().unwrap()));
        }
    }
    let missing: Vec<&&str> = FAMILIES.iter().filter(|f| !seen.contains(**f)).collect();
    let unlisted: Vec<&&str> = seen.iter().filter(|t| !FAMILIES.contains(t)).collect();
    eprintln!(
        "construct generator over {SAMPLES} fixed-seed modules: binary exact {binary_exact}, \
         binary refused as a producer omission {binary_refused}, no tMBC wire image \
         {wire_gap_refused}, written but refused as non-canonical {noncanonical_refused}, text \
         exact {text_exact}, text refused by kind {text_refused:?}, writer headers {headers:?}"
    );
    assert!(missing.is_empty(), "families never generated: {missing:?}");
    assert!(
        unlisted.is_empty(),
        "tags missing from FAMILIES: {unlisted:?}"
    );
    assert!(
        binary_exact > 0 && binary_refused > 0 && wire_gap_refused > 0 && noncanonical_refused > 0,
        "every binary outcome occurs"
    );
    assert!(
        text_exact > 0 && !text_refused.is_empty(),
        "both text outcomes occur"
    );
    for kind in ["EnumLayout", "RecordFieldOffsets"] {
        assert!(
            text_refused.contains_key(kind),
            "the generator never produced a text-refused `{kind}`: {text_refused:?}"
        );
    }
    // Since trust-ir 24e1ef5c (WS4.5) the text carries a variant's field names
    // whenever the list is parallel to its fields, the only shape
    // `validate_module` admits; the generator emits only that shape, so its
    // field names always round-trip and are never a text loss.
    assert!(
        seen.contains("enum.field_names") && !text_refused.contains_key("EnumFieldNames"),
        "enum field names are generated and carried by the text: {text_refused:?}"
    );
    // The writer's header spans the pre-contract surface and the v41+ one,
    // and reaches v51 exactly when an INST wire batch member is written.
    assert!(headers.iter().any(|h| *h < 41) && headers.iter().any(|h| *h >= 45));
    assert!(
        headers.contains(&51),
        "no module carrying an INST wire batch member was written: {headers:?}"
    );
}

/// Shrinking is live on the construct generator: a property that fails on
/// any TLS global is reported with a counterexample reduced to ONE item —
/// that global — with every other knob at its simplest choice.
#[test]
fn construct_generator_shrinks_to_a_minimal_counterexample() {
    use proptest::test_runner::{Config, TestError, TestRunner};

    let mut runner = TestRunner::new_with_rng(
        Config {
            cases: 256,
            ..Config::default()
        },
        proptest::test_runner::TestRng::deterministic_rng(
            proptest::test_runner::RngAlgorithm::ChaCha,
        ),
    );
    let result = runner.run(&constructs::spec(), |spec| {
        let built = constructs::materialize(&spec);
        prop_assert!(!built.module.globals.iter().any(|g| g.tls.is_some()));
        Ok(())
    });
    let Err(TestError::Fail(_, minimal)) = result else {
        panic!("a TLS global is generated within 256 cases: {result:?}");
    };
    assert_eq!(minimal.items.len(), 1, "shrunk to one item: {minimal:#?}");
    let constructs::Item::Global {
        ty,
        init,
        tls,
        linkage,
        section,
        retained,
        align_log2,
        seed,
        ..
    } = &minimal.items[0]
    else {
        panic!("the one item is the TLS global: {minimal:#?}");
    };
    assert_eq!(*tls, Some(0), "TLS model shrinks to its first choice");
    assert_eq!(*ty, constructs::Sc::I32);
    assert!(!init && !section && !retained && align_log2.is_none() && *linkage == 0);
    assert_eq!(*seed, 0);
    assert!(!minimal.lineage && minimal.target == 0);
}
