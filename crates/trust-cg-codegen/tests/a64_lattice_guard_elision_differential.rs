// a64_lattice_guard_elision_differential.rs — WP-2's payoff, measured end to end.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Declared refinements preserve runtime guards and the representation of their base type.
//!
//! Bare, exact-interval and off-by-one index declarations compile through the AArch64
//! pipeline, then their Mach-O text is counted and interpreted. Every declaration keeps
//! its guard, including with `lattice-guard-elision` enabled: predicate implication does
//! not prove that an external caller or a load supplied an in-range value (OD-27).
//! Tests execute all eight valid indices and an out-of-range index for external and
//! loaded inputs, distinguish BRK traps from unsupported instructions, and check retained
//! predicate metadata without minted source capabilities. A future fewer-guards positive
//! fixture must carry an actually replayed RefinementType premise; none exists today.

#[path = "common/admission_expect.rs"]
mod admission_expect;

use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::target::{Target, TargetSpec};
use trust_ir::pred::Pred;
use trust_ir::{
    Block, BlockId, FuncId, FuncTy, Function, Inst, InstrNode, Module, ProofAnnotation, Ty, ValueId,
};

#[path = "common/mod.rs"]
mod common;
use common::a64_interp::{A64Error, A64Interp, extract_text, symbol_addrs, text_branch_relocs};

/// Element count of the indexed array — and therefore the exact bound the guard tests.
const ARRAY_LEN: u64 = 8;
/// Where the test places the array in the interpreter's flat memory.
const ARRAY_BASE: u64 = 0x4000;
const INDEX_ADDRESS: u64 = 0x5000;
/// Contents of that array; deliberately not equal to the index, so a wrong index is visible.
const ARRAY_DATA: [u64; ARRAY_LEN as usize] = [11, 22, 33, 44, 55, 66, 77, 88];

/// Which refinement (if any) the index parameter declares.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum IndexTy {
    /// `i64` — no predicate. A dropped fact lands on `Top`, and `Top` entails nothing.
    Bare,
    /// `Refine(i64, Interval(0, hi))`.
    Refined { hi: i128 },
}

/// `i64 lattice_probe(Array(I64, 8) arr, IDX idx) { return arr[idx] }`, with the array access
/// carrying `ProofAnnotation::InBounds` so the proof-only carrier is emitted in EVERY fixture.
///
/// The carrier's presence is what makes this a differential about *elision* rather than about
/// emission: all three fixtures must retain the same guard because their predicates are declared.
fn build_module(index_ty: IndexTy) -> Module {
    let mut module = Module::new("lattice_guard_elision_differential");
    let elem_ty = module
        .add_type(Ty::I64)
        .expect("Module::add_type: test fixture");
    let array_ty = Ty::Array(elem_ty, ARRAY_LEN);

    let index_ty = match index_ty {
        IndexTy::Bare => Ty::I64,
        IndexTy::Refined { hi } => {
            // Interned by CONTENT: `intern_pred` is the only sanctioned way to mint a `PredId`,
            // and it guarantees the table invariant the trust-ir validator enforces.
            let base = module
                .add_type(Ty::I64)
                .expect("Module::add_type: test fixture");
            let pred = module
                .intern_pred(Pred::interval(0, hi).expect("well-formed interval"))
                .expect("Module::intern_pred: test fixture")
                .expect("interned predicate");
            Ty::Refine(base, pred)
        }
    };

    let ft = module
        .add_func_type(FuncTy {
            params: vec![array_ty.clone(), index_ty.clone()],
            returns: vec![Ty::I64],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut func = Function::new(FuncId::new(0), "lattice_probe", ft, BlockId::new(0));
    func.blocks = vec![Block {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), array_ty), (ValueId::new(1), index_ty)],
        body: vec![
            InstrNode::new(Inst::ExtractElement {
                ty: Ty::I64,
                array: ValueId::new(0),
                index: ValueId::new(1),
            })
            .with_result(ValueId::new(2))
            .with_proof(ProofAnnotation::InBounds),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(2)],
            }),
        ],
    }];
    module
        .try_add_function(func)
        .expect("Module::try_add_function: test fixture");
    module
}

/// Whether trust-ir refuses `module` for its refinement-typed index: its
/// validator reads an `ExtractElement` index of type `Refine(i64, ..)` as not
/// an integer (`InvalidVectorElementOp`), and since WS7.3 every ingestion
/// entry refuses what the validator refuses. When it does, the compile is
/// asserted to name that finding (the refinement payoff cannot be measured
/// end to end until trust-ir reads a refined integer as its base type).
/// BOTH LAYERS JUDGE UNDER ONE POLICY, [`permit_unlicensed`]. These fixtures
/// are synthetic, claim-less bodies (`body_gate: None`), which the DEFAULT
/// policy refuses by design (DG-73, `UnlicensedBodyPolicy::Refuse`) — and the
/// two layers reach that refusal in a different ORDER: trust-ir's admission
/// finds the refinement-typed index first, while the backend compile finds
/// the missing license first, so the row's assertion read the license verdict
/// where it expects the refinement one. Permitting the claim-less body on
/// both sides is what makes the row measure the refinement refusal it names.
/// It does not weaken the license rule, which has its own tests
/// (`codegen_license_flags`, `codegen_license_evidence`) and is what
/// `compile_a64` below already states for the same fixtures.
fn refined_index_refused_at_ingestion(module: &Module) -> bool {
    let Some((variant, text)) = admission_expect::first_finding(module, &permit_unlicensed())
    else {
        return false;
    };
    assert!(
        variant == "InvalidVectorElementOp" && text.contains("refine"),
        "trust-ir refuses the fixture for another reason: {variant}: {text}"
    );
    let spec = TargetSpec::parse("aarch64-apple-darwin").expect("parse aarch64-apple-darwin");
    let error = Compiler::new_for_target_spec(
        CompilerConfig {
            opt_level: OptLevel::O2,
            target: Target::Aarch64,
            ..CompilerConfig::default()
        },
        spec,
    )
    .with_codegen_license(permit_unlicensed())
    .compile(module)
    .expect_err("trust-ir refuses the refined fixture, so trust-cg must")
    .to_string();
    assert!(error.contains("InvalidVectorElementOp"), "{error}");
    eprintln!(
        "REFUSED {}: refinement-typed index outside trust-ir's validator",
        module.name
    );
    true
}

fn compile_a64(module: &Module) -> Vec<u8> {
    // Mach-O, because the shared AArch64 decode+interpret harness (`common::a64_interp`) reads
    // `__text` and the symbol table out of a 64-bit little-endian Mach-O object.
    let spec = TargetSpec::parse("aarch64-apple-darwin").expect("parse aarch64-apple-darwin");
    Compiler::new_for_target_spec(
        CompilerConfig {
            opt_level: OptLevel::O2,
            target: Target::Aarch64,
            ..CompilerConfig::default()
        },
        spec,
    )
    .with_codegen_license(permit_unlicensed())
    .compile(module)
    .expect("aarch64 compile")
    .object_code
}

/// Count expanded bounds-guard traps in `__text`.
///
/// `expand_trap_bounds_check_exact` lowers a surviving `TrapBoundsCheckExact` to
/// `CMP idx,#bound ; B.LO +2 ; BRK #imm`. `BRK` is the `0xD42x_xxxx` family and this fixture has
/// no other trap source, so one `BRK` == one surviving bounds guard.
fn surviving_guard_count(obj: &[u8]) -> usize {
    let text = extract_text(obj);
    text.bytes
        .as_chunks::<4>()
        .0
        .iter()
        .filter(|w| {
            let word = u32::from_le_bytes([w[0], w[1], w[2], w[3]]);
            word & 0xFFE0_001F == 0xD420_0000
        })
        .count()
}

/// Decode + interpret the emitted code with `arr` seeded in memory and `idx` in x1.
fn run(obj: &[u8], index: u64) -> u64 {
    run_with_index(obj, index, false).expect("a64 interp run")
}

fn run_with_index(obj: &[u8], index: u64, loaded: bool) -> Result<u64, A64Error> {
    let text = extract_text(obj);
    let addrs = symbol_addrs(obj);
    let n_value = *addrs
        .get("_lattice_probe")
        .or_else(|| addrs.get("lattice_probe"))
        .unwrap_or_else(|| panic!("symbol lattice_probe missing; have {:?}", addrs.keys()));
    let entry = (n_value - text.addr) as usize;
    let mut interp = A64Interp::new(text.bytes).with_branch_relocs(text_branch_relocs(obj));
    for (i, value) in ARRAY_DATA.iter().enumerate() {
        for byte in 0..8u64 {
            interp.mem.insert(
                ARRAY_BASE + i as u64 * 8 + byte,
                (value >> (8 * byte)) as u8,
            );
        }
    }
    interp.set_x(0, ARRAY_BASE);
    if loaded {
        for byte in 0..8u64 {
            interp
                .mem
                .insert(INDEX_ADDRESS + byte, (index >> (8 * byte)) as u8);
        }
        interp.set_x(1, INDEX_ADDRESS);
    } else {
        interp.set_x(1, index);
    }
    interp.run(entry)
}

/// The same source predicate on a load result instead of an external parameter.
fn build_loaded_index_module(index_ty: IndexTy) -> Module {
    let mut module = build_module(index_ty);
    let declared_ty = module.func_types[0].params[1].clone();
    module.func_types[0].params[1] = Ty::Ptr;
    let block = &mut module.functions[0].blocks[0];
    block.params[1].1 = Ty::Ptr;
    if let Inst::ExtractElement { index, .. } = &mut block.body[0].inst {
        *index = ValueId::new(3);
    } else {
        panic!("fixture must start with ExtractElement");
    }
    block.body.insert(
        0,
        InstrNode::new(Inst::Load {
            ty: declared_ty,
            ptr: ValueId::new(1),
            volatile: false,
            align: Some(8),
        })
        .with_result(ValueId::new(3)),
    );
    module
}

#[test]
fn declared_external_parameter_keeps_the_runtime_guard() {
    assert_declared_index_guard(false);
}

#[test]
fn declared_loaded_index_keeps_the_runtime_guard() {
    assert_declared_index_guard(true);
}

fn assert_declared_index_guard(loaded: bool) {
    let build = if loaded {
        build_loaded_index_module
    } else {
        build_module
    };
    if refined_index_refused_at_ingestion(&build(IndexTy::Refined { hi: 7 })) {
        return;
    }
    let bare = compile_a64(&build(IndexTy::Bare));
    let declared = compile_a64(&build(IndexTy::Refined { hi: 7 }));
    assert_eq!(
        surviving_guard_count(&bare),
        1,
        "non-vacuous baseline, loaded={loaded}"
    );
    // Execute the first index excluded by the annotation. A predicate declaration
    // cannot establish that an external caller or memory supplied an in-range value.
    assert_eq!(
        run_with_index(&bare, ARRAY_LEN, loaded),
        Err(A64Error::Trap { immediate: 1 })
    );
    assert_eq!(
        run_with_index(&declared, ARRAY_LEN, loaded),
        Err(A64Error::Trap { immediate: 1 }),
        "declared predicate removed a required runtime check, loaded={loaded}"
    );
    assert_eq!(surviving_guard_count(&declared), 1);
    for index in 0..ARRAY_LEN {
        assert_eq!(
            run_with_index(&declared, index, loaded),
            Ok(ARRAY_DATA[index as usize])
        );
    }
    let module = build(IndexTy::Refined { hi: 7 });
    assert_eq!(module.functions[0].linkage, trust_ir::Linkage::External);
    let (_, ctx) = trust_cg_lower::translate_function_with_license(
        &module.functions[0],
        &module,
        &permit_unlicensed(),
    )
    .unwrap();
    assert!(
        ctx.value_proofs
            .values()
            .flatten()
            .any(|p| matches!(p, trust_cg_lower::Proof::Refinement { .. }))
    );
    assert!(!ctx.refinement_env.is_empty());
    assert!(
        ctx.lattice_bounds_capabilities.is_empty(),
        "a declared predicate mints no capability, loaded={loaded}"
    );
}

#[test]
fn declared_refinement_preserves_the_guard_and_every_in_bounds_result() {
    if refined_index_refused_at_ingestion(&build_module(IndexTy::Refined { hi: 7 })) {
        return;
    }
    let bare = compile_a64(&build_module(IndexTy::Bare));
    let refined = compile_a64(&build_module(IndexTy::Refined { hi: 7 }));
    let off_by_one = compile_a64(&build_module(IndexTy::Refined { hi: 8 }));

    let bare_guards = surviving_guard_count(&bare);
    let refined_guards = surviving_guard_count(&refined);
    let off_by_one_guards = surviving_guard_count(&off_by_one);

    println!(
        "[lattice-guard] authority={} guards: bare={bare_guards} refined={refined_guards} \
         off_by_one={off_by_one_guards}",
        trust_cg_lower::lattice_guard::lattice_guard_replay_authority_available(),
    );

    // The fixture must actually emit a guard, or the whole comparison is vacuous.
    assert!(
        bare_guards >= 1,
        "fixture emits no bounds guard at all — the differential would be vacuous"
    );

    assert_eq!(
        refined_guards, bare_guards,
        "a declared predicate must retain the runtime guard on every build"
    );

    // (3) FAIL-CLOSED. Off by exactly one on the upper end: `[0,8]` admits index 8, which the
    // bound-8 guard traps on. `implies` answers false, no capability is minted, guard stays.
    assert_eq!(
        off_by_one_guards, bare_guards,
        "an ALMOST-sufficient predicate must not elide anything (off_by_one={off_by_one_guards}, \
         bare={bare_guards})"
    );

    // (2) BYTE-IDENTICAL RESULTS over the entire domain the predicate covers.
    for index in 0..ARRAY_LEN {
        let want = run(&bare, index);
        assert_eq!(
            want, ARRAY_DATA[index as usize],
            "oracle: arr[{index}] must be {}",
            ARRAY_DATA[index as usize]
        );
        assert_eq!(
            run(&refined, index),
            want,
            "guard elision changed the result at index {index}"
        );
        assert_eq!(
            run(&off_by_one, index),
            want,
            "the fail-closed fixture changed the result at index {index}"
        );
    }
}

/// The representation-preservation claim, checked on the object bytes rather than argued.
///
/// A module that uses NO refinements must compile to the byte-identical object it compiled to
/// before the typed value model existed. There is no way to diff against the old compiler from
/// inside this test, so it checks the equivalent invariant that makes that true: compiling the
/// same unrefined module twice and compiling the declared REFINED module all produce the
/// same bytes as the bare fixture, including with the lattice feature enabled.
#[test]
fn refinements_move_no_bytes_without_authority() {
    if refined_index_refused_at_ingestion(&build_module(IndexTy::Refined { hi: 7 })) {
        return;
    }
    let bare_a = compile_a64(&build_module(IndexTy::Bare));
    let bare_b = compile_a64(&build_module(IndexTy::Bare));
    assert_eq!(bare_a, bare_b, "compilation must be deterministic");

    let refined = compile_a64(&build_module(IndexTy::Refined { hi: 7 }));
    assert_eq!(
        refined, bare_a,
        "a declared refinement is representation-preserving and grants no elision authority"
    );

    // And the off-by-one fixture is byte-identical to bare on EVERY build — it never had
    // authority to begin with.
    let off_by_one = compile_a64(&build_module(IndexTy::Refined { hi: 8 }));
    assert_eq!(
        off_by_one, bare_a,
        "an almost-sufficient predicate must move no bytes at all"
    );
}

/// The adapter half, checked directly: a refined value's predicate reaches
/// `ProofContext::value_proofs`, but no source capability is minted without replayed authority.
#[test]
fn adapter_records_the_declared_predicate_without_minting_a_capability() {
    let module = build_module(IndexTy::Refined { hi: 7 });
    let func = &module.functions[0];
    let (_lir, ctx) =
        trust_cg_lower::translate_function_with_license(func, &module, &permit_unlicensed())
            .expect("adapter translate");

    let refinements: Vec<_> = ctx
        .value_proofs
        .values()
        .flatten()
        .filter_map(|p| match p {
            trust_cg_lower::Proof::Refinement { pred } => Some(*pred),
            _ => None,
        })
        .collect();
    assert_eq!(
        refinements.len(),
        1,
        "exactly the refined index parameter carries a predicate"
    );
    assert!(
        !ctx.refinement_env.is_empty(),
        "the module's interned lattice tables must travel with the proof context"
    );

    assert!(ctx.lattice_bounds_capabilities.is_empty());
    // The implication is still decidable and replayable as an unbound diagnostic.
    // What is missing is proof that the runtime index satisfies this predicate.
    let capability = trust_cg_lower::lattice_guard::certify_bounds_guard(
        &ctx.refinement_env,
        refinements[0],
        ARRAY_LEN,
    )
    .expect("the exact predicate entails the bound");
    assert_eq!(capability.bound(), ARRAY_LEN);
    assert_eq!(capability.discharging_pred(), refinements[0]);
    assert!(capability.replay(&ctx.refinement_env));
    let text = capability.obligation_text();
    assert!(
        text.contains("index in [0, 7]") && text.contains("pred."),
        "{text}"
    );

    // Fail-closed mirror: the off-by-one module mints nothing, though it records the predicate.
    let module = build_module(IndexTy::Refined { hi: 8 });
    let func = &module.functions[0];
    let (_lir, ctx) =
        trust_cg_lower::translate_function_with_license(func, &module, &permit_unlicensed())
            .expect("adapter translate");
    assert!(
        ctx.value_proofs
            .values()
            .flatten()
            .any(|p| matches!(p, trust_cg_lower::Proof::Refinement { .. })),
        "the predicate is still recorded — it is simply not sufficient"
    );
    assert!(
        ctx.lattice_bounds_capabilities.is_empty(),
        "an off-by-one predicate must mint no capability"
    );

    // And a bare module records nothing and mints nothing.
    let module = build_module(IndexTy::Bare);
    let func = &module.functions[0];
    let (_lir, ctx) =
        trust_cg_lower::translate_function_with_license(func, &module, &permit_unlicensed())
            .expect("adapter translate");
    assert!(
        !ctx.value_proofs
            .values()
            .flatten()
            .any(|p| matches!(p, trust_cg_lower::Proof::Refinement { .. }))
    );
    assert!(ctx.lattice_bounds_capabilities.is_empty());
    assert!(ctx.refinement_env.is_empty());
}

/// `translate_type` sees straight through a refinement: the machine type of `Refine(b, p)` IS the
/// machine type of `b`, for every base the backend supports.
#[test]
fn refine_translates_to_exactly_its_base_type() {
    // The table-only helper deliberately fails closed on `Ty::Refine` (upstream's
    // `refinements_validated` gate): only a validated Module may erase a refinement.
    {
        let mut module = Module::new("refine_repr_reject");
        let base = module
            .add_type(Ty::I64)
            .expect("Module::add_type: test fixture");
        let pred = module
            .intern_pred(Pred::interval(0, 7).unwrap())
            .expect("Module::intern_pred: test fixture")
            .unwrap();
        let types: Vec<Ty> = module.types.clone();
        assert!(
            trust_cg_lower::adapter::translate_type_with_tables(
                &Ty::Refine(base, pred),
                &[],
                &types
            )
            .is_err(),
            "a table-only type helper must refuse to erase a refinement without module validation"
        );
    }

    // Representation preservation, through the sanctioned (validated-module) path: an identity
    // function over `Refine(b, Top)` must lower to EXACTLY the machine signature of the same
    // identity function over bare `b`.
    let bases = [
        Ty::I8,
        Ty::I16,
        Ty::I32,
        Ty::I64,
        Ty::U8,
        Ty::U16,
        Ty::U32,
        Ty::U64,
        Ty::Bool,
        Ty::Ptr,
        Ty::F32,
        Ty::F64,
    ];
    for base in &bases {
        let bare = lowered_identity_signature(base.clone(), false);
        let refined = lowered_identity_signature(base.clone(), true);
        assert_eq!(
            bare, refined,
            "Refine({base:?}, p) must have EXACTLY {base:?}'s machine signature"
        );
    }
}

/// Lower `fn identity(x: T) -> T` through the full validated-module adapter path and return the
/// LIR signature, where `T` is `base` itself or `Refine(base, Top)`.
fn lowered_identity_signature(
    base: Ty,
    refine: bool,
) -> (Vec<trust_cg_lower::Type>, Vec<trust_cg_lower::Type>) {
    let mut module = Module::new("refine_repr");
    let param_ty = if refine {
        let base_id = module
            .add_type(base)
            .expect("Module::add_type: test fixture");
        let pred = module
            .intern_pred(Pred::Top)
            .expect("Module::intern_pred: test fixture")
            .expect("Top is a canonical predicate");
        Ty::Refine(base_id, pred)
    } else {
        base
    };
    let ft = module
        .add_func_type(FuncTy {
            params: vec![param_ty.clone()],
            returns: vec![param_ty.clone()],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut func = Function::new(FuncId::new(0), "identity", ft, BlockId::new(0));
    func.blocks = vec![Block {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), param_ty)],
        body: vec![InstrNode::new(Inst::Return {
            values: vec![ValueId::new(0)],
        })],
    }];
    module
        .try_add_function(func)
        .expect("Module::try_add_function: test fixture");
    let lowered = permit_translate_module(&module)
        .unwrap_or_else(|e| panic!("identity over {refine:?}-refined base must lower: {e}"));
    (
        lowered[0].0.signature.params.clone(),
        lowered[0].0.signature.returns.clone(),
    )
}

/// Guard against a silently-empty differential: `surviving_guard_count` must be measuring
/// something real.
#[test]
fn guard_counter_is_not_vacuous() {
    let bare = compile_a64(&build_module(IndexTy::Bare));
    assert!(
        surviving_guard_count(&bare) > 0,
        "the bare fixture must emit at least one runtime guard to count"
    );
}

/// `i64 two_probes(Array(I64,8) arr, IDX a, i64 b) { return arr[a] + arr[b] }` — TWO array
/// accesses, both carrying `InBounds`, indexed by two DIFFERENT parameters. Only the first
/// parameter's type varies.
fn build_two_probe_module(first_index_ty: IndexTy) -> Module {
    let mut module = Module::new("lattice_guard_scope");
    let elem_ty = module
        .add_type(Ty::I64)
        .expect("Module::add_type: test fixture");
    let array_ty = Ty::Array(elem_ty, ARRAY_LEN);
    let first_ty = match first_index_ty {
        IndexTy::Bare => Ty::I64,
        IndexTy::Refined { hi } => {
            let base = module
                .add_type(Ty::I64)
                .expect("Module::add_type: test fixture");
            let pred = module
                .intern_pred(Pred::interval(0, hi).expect("well-formed interval"))
                .expect("Module::intern_pred: test fixture")
                .expect("interned predicate");
            Ty::Refine(base, pred)
        }
    };
    let ft = module
        .add_func_type(FuncTy {
            params: vec![array_ty.clone(), first_ty.clone(), Ty::I64],
            returns: vec![Ty::I64],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut func = Function::new(FuncId::new(0), "two_probes", ft, BlockId::new(0));
    func.blocks = vec![Block {
        id: BlockId::new(0),
        params: vec![
            (ValueId::new(0), array_ty),
            (ValueId::new(1), first_ty),
            (ValueId::new(2), Ty::I64),
        ],
        body: vec![
            InstrNode::new(Inst::ExtractElement {
                ty: Ty::I64,
                array: ValueId::new(0),
                index: ValueId::new(1),
            })
            .with_result(ValueId::new(3))
            .with_proof(ProofAnnotation::InBounds),
            InstrNode::new(Inst::ExtractElement {
                ty: Ty::I64,
                array: ValueId::new(0),
                index: ValueId::new(2),
            })
            .with_result(ValueId::new(4))
            .with_proof(ProofAnnotation::InBounds),
            InstrNode::new(Inst::BinOp {
                op: trust_ir::BinOp::Add,
                ty: Ty::I64,
                lhs: ValueId::new(3),
                rhs: ValueId::new(4),
            })
            .with_result(ValueId::new(5)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(5)],
            }),
        ],
    }];
    module
        .try_add_function(func)
        .expect("Module::try_add_function: test fixture");
    module
}

/// Refining one of two externally supplied indices cannot remove either guard.
#[test]
fn declaring_one_of_two_indices_retains_both_guards() {
    if refined_index_refused_at_ingestion(&build_two_probe_module(IndexTy::Refined { hi: 7 })) {
        return;
    }
    let bare = compile_a64(&build_two_probe_module(IndexTy::Bare));
    let one_refined = compile_a64(&build_two_probe_module(IndexTy::Refined { hi: 7 }));

    let bare_guards = surviving_guard_count(&bare);
    let refined_guards = surviving_guard_count(&one_refined);
    println!(
        "[lattice-guard scope] authority={} two-probe guards: bare={bare_guards} \
         one_refined={refined_guards}",
        trust_cg_lower::lattice_guard::lattice_guard_replay_authority_available(),
    );

    assert_eq!(
        bare_guards, 2,
        "the two-probe fixture must emit exactly two bounds guards"
    );
    assert_eq!(refined_guards, bare_guards);
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes because it was silently refused.
fn permit_unlicensed() -> trust_cg_lower::CodegenLicensePolicy {
    trust_cg_lower::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit)
}

/// `translate_module` under [`permit_unlicensed`].
fn permit_translate_module(
    module: &trust_ir::Module,
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
