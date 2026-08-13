// a64_lattice_guard_elision_differential.rs — WP-2's payoff, measured end to end.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! **The differential: does putting the encoding convention in the type buy real code?**
//!
//! Three trust-ir modules that differ along EXACTLY ONE AXIS — the declared type of the index
//! parameter — are compiled through the full AArch64 pipeline, and the emitted machine code is
//! decoded and executed:
//!
//! | fixture | index parameter type | what the lattice decides |
//! |---|---|---|
//! | `BARE`     | `i64`                              | no predicate at all (`Top`): nothing to decide |
//! | `REFINED`  | `Refine(i64, Interval(0, 7))`      | entails `[0,7]` — the guard's exact condition |
//! | `OFF_BY_ONE` | `Refine(i64, Interval(0, 8))`    | admits index 8 — **not** sufficient |
//!
//! Everything else is byte-for-byte identical: same array type, same `ExtractElement`, same
//! `InBounds` annotation, same opt level, same target. `Ty::Refine` is representation-preserving,
//! so the type change moves no layout, no ABI slot and no machine type — the ONLY thing it can
//! change is what the decidable lattice is able to prove.
//!
//! Three things are asserted:
//!
//! 1. **STRICTLY FEWER GUARDS.** `REFINED` emits strictly fewer expanded bounds-check traps than
//!    `BARE` (`TrapBoundsCheckExact` lowers to `CMP idx,#bound ; B.LO +2 ; BRK`, so counting `BRK`
//!    in `__text` counts surviving guards).
//! 2. **BYTE-IDENTICAL RESULTS.** Over the ENTIRE domain the predicate covers (every in-bounds
//!    index), the decoded-and-interpreted machine code of all three fixtures returns the same
//!    64-bit value. Eliding a guard whose trap is unreachable cannot change a result — and this
//!    executes that claim rather than asserting it.
//! 3. **FAIL-CLOSED.** `OFF_BY_ONE` keeps every guard `BARE` keeps. Its predicate is almost
//!    sufficient — wrong by exactly one on the upper end — and `implies` answers `false`, so no
//!    capability is minted and the runtime check stays. That the *other* fixture does fire is what
//!    makes this refusal non-vacuous.
//!
//! Without the `lattice-guard-elision` feature the whole payoff is inert by construction, so
//! assertion 1 is stated as "identical guard counts" instead. Assertions 2 and 3 hold either way,
//! and 3 is the load-bearing one: it must hold on BOTH builds.

use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::target::{Target, TargetSpec};
use trust_ir::pred::Pred;
use trust_ir::{
    Block, BlockId, FuncId, FuncTy, Function, Inst, InstrNode, Module, ProofAnnotation, Ty, ValueId,
};

#[path = "common/mod.rs"]
mod common;
use common::a64_interp::{A64Interp, extract_text, symbol_addrs, text_branch_relocs};

/// Element count of the indexed array — and therefore the exact bound the guard tests.
const ARRAY_LEN: u64 = 8;
/// Where the test places the array in the interpreter's flat memory.
const ARRAY_BASE: u64 = 0x4000;
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
/// emission: all three fixtures emit the same guard, and only the lattice decides whether it may
/// be deleted.
fn build_module(index_ty: IndexTy) -> Module {
    let mut module = Module::new("lattice_guard_elision_differential");
    let elem_ty = module.add_type(Ty::I64);
    let array_ty = Ty::Array(elem_ty, ARRAY_LEN);

    let index_ty = match index_ty {
        IndexTy::Bare => Ty::I64,
        IndexTy::Refined { hi } => {
            // Interned by CONTENT: `intern_pred` is the only sanctioned way to mint a `PredId`,
            // and it guarantees the table invariant the trust-ir validator enforces.
            let base = module.add_type(Ty::I64);
            let pred = module
                .intern_pred(Pred::interval(0, hi).expect("well-formed interval"))
                .expect("interned predicate");
            Ty::Refine(base, pred)
        }
    };

    let ft = module.add_func_type(FuncTy {
        params: vec![array_ty.clone(), index_ty.clone()],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
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
    module.add_function(func);
    module
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
        .chunks_exact(4)
        .filter(|w| {
            let word = u32::from_le_bytes([w[0], w[1], w[2], w[3]]);
            word & 0xFFE0_001F == 0xD420_0000
        })
        .count()
}

/// Decode + interpret the emitted code with `arr` seeded in memory and `idx` in x1.
fn run(obj: &[u8], index: u64) -> u64 {
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
    interp.set_x(1, index);
    interp.run(entry).expect("a64 interp run")
}

#[test]
fn refinement_elides_the_guard_without_changing_a_single_result() {
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

    // (1) STRICTLY FEWER GUARDS, when the authority is held.
    if trust_cg_lower::lattice_guard::lattice_guard_replay_authority_available() {
        assert!(
            refined_guards < bare_guards,
            "an exactly-sufficient refinement must elide at least one guard \
             (bare={bare_guards}, refined={refined_guards})"
        );
        assert_eq!(
            refined_guards, 0,
            "every guard in this fixture is discharged by the predicate"
        );
    } else {
        assert_eq!(
            refined_guards, bare_guards,
            "without lattice authority the compiler must be byte-for-byte the pre-lattice one"
        );
    }

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
/// same unrefined module twice, and compiling the REFINED module on a build with no lattice
/// authority, all produce the same bytes as the bare fixture.
#[test]
fn refinements_move_no_bytes_without_authority() {
    let bare_a = compile_a64(&build_module(IndexTy::Bare));
    let bare_b = compile_a64(&build_module(IndexTy::Bare));
    assert_eq!(bare_a, bare_b, "compilation must be deterministic");

    let refined = compile_a64(&build_module(IndexTy::Refined { hi: 7 }));
    if trust_cg_lower::lattice_guard::lattice_guard_replay_authority_available() {
        assert_ne!(
            refined, bare_a,
            "with authority held, the certified elision must be observable in the object"
        );
    } else {
        assert_eq!(
            refined, bare_a,
            "`Ty::Refine` is representation-preserving: without lattice authority a refined \
             module must emit BYTE-IDENTICAL code to the unrefined one"
        );
    }

    // And the off-by-one fixture is byte-identical to bare on EVERY build — it never had
    // authority to begin with.
    let off_by_one = compile_a64(&build_module(IndexTy::Refined { hi: 8 }));
    assert_eq!(
        off_by_one, bare_a,
        "an almost-sufficient predicate must move no bytes at all"
    );
}

/// The adapter half, checked directly: a refined value's predicate reaches
/// `ProofContext::value_proofs`, and a capability is minted for the guard it discharges.
#[test]
fn adapter_records_the_predicate_and_mints_a_capability() {
    let module = build_module(IndexTy::Refined { hi: 7 });
    let func = &module.functions[0];
    let (_lir, ctx) = trust_cg_lower::translate_function(func, &module).expect("adapter translate");

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

    assert_eq!(
        ctx.lattice_bounds_capabilities.len(),
        1,
        "the sufficient predicate must mint exactly one capability"
    );
    let capability = &ctx.lattice_bounds_capabilities[0];
    assert_eq!(capability.bound(), ARRAY_LEN);
    assert_eq!(capability.discharging_pred(), refinements[0]);
    assert!(
        capability.replay(&ctx.refinement_env),
        "a recorded capability must replay against the env it travelled with"
    );
    let text = capability.obligation_text();
    assert!(
        text.contains("index in [0, 7]") && text.contains("pred."),
        "the certificate must name the obligation AND the discharging predicate: {text}"
    );

    // Fail-closed mirror: the off-by-one module mints nothing, though it records the predicate.
    let module = build_module(IndexTy::Refined { hi: 8 });
    let func = &module.functions[0];
    let (_lir, ctx) = trust_cg_lower::translate_function(func, &module).expect("adapter translate");
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
    let (_lir, ctx) = trust_cg_lower::translate_function(func, &module).expect("adapter translate");
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
        let base = module.add_type(Ty::I64);
        let pred = module.intern_pred(Pred::interval(0, 7).unwrap()).unwrap();
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
        let base_id = module.add_type(base);
        let pred = module
            .intern_pred(Pred::Top)
            .expect("Top is a canonical predicate");
        Ty::Refine(base_id, pred)
    } else {
        base
    };
    let ft = module.add_func_type(FuncTy {
        params: vec![param_ty.clone()],
        returns: vec![param_ty.clone()],
        is_vararg: false,
    });
    let mut func = Function::new(FuncId::new(0), "identity", ft, BlockId::new(0));
    func.blocks = vec![Block {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), param_ty)],
        body: vec![InstrNode::new(Inst::Return {
            values: vec![ValueId::new(0)],
        })],
    }];
    module.add_function(func);
    let lowered = trust_cg_lower::adapter::translate_module(&module)
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
    let elem_ty = module.add_type(Ty::I64);
    let array_ty = Ty::Array(elem_ty, ARRAY_LEN);
    let first_ty = match first_index_ty {
        IndexTy::Bare => Ty::I64,
        IndexTy::Refined { hi } => {
            let base = module.add_type(Ty::I64);
            let pred = module
                .intern_pred(Pred::interval(0, hi).expect("well-formed interval"))
                .expect("interned predicate");
            Ty::Refine(base, pred)
        }
    };
    let ft = module.add_func_type(FuncTy {
        params: vec![array_ty.clone(), first_ty.clone(), Ty::I64],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
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
    module.add_function(func);
    module
}

/// **Per-carrier selectivity.** Elision is bound to the exact carrier whose operands the
/// capability was certified for — it is not "bounds checking is now off".
///
/// Two identical array accesses in one function, indexed by two different parameters, both
/// carrying `InBounds`. Refining ONLY the first parameter must remove EXACTLY ONE of the two
/// guards. If the authorization leaked to the whole guard class (or to the whole function), both
/// would go and this fails.
#[test]
fn elision_is_bound_to_the_certified_carrier_only() {
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
    if trust_cg_lower::lattice_guard::lattice_guard_replay_authority_available() {
        assert_eq!(
            refined_guards, 1,
            "EXACTLY the certified carrier may go; the un-refined index keeps its guard"
        );
    } else {
        assert_eq!(refined_guards, bare_guards);
    }
}
