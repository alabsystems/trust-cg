// trust-cg-codegen/tests/aarch64_memory_order_obligations.rs - the C11/Rust ->
// AArch64 memory-order mapping, checked on the words the real selector emits
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Ledger L03-P3: every atomic form the AArch64 selector emits implements the
//! C11/Rust ordering it was selected for.
//!
//! One trust-ir function per request (load, store, every RMW op, compare-
//! exchange at all 15 valid (success, failure) pairs, fence) at every width
//! the selector admits (bool, 8, 16, 32, 64, 128 bits) and every ordering,
//! compiled through the real pipeline on three AArch64 profiles at O0-O3:
//!
//! * `darwin-aot`: the Darwin AOT `Compiler` (Apple arm64: LSE, LSE2),
//! * `lse`: the explicit LSE profile without LSE2 (128-bit atomics through
//!   the LL/SC pair pseudos),
//! * `baseline`: armv8.0 (every RMW and compare-exchange through LL/SC
//!   loops).
//!
//! Each function's words are read back from the object's symbol table and
//! handed to `trust_cg_verify::aarch64_memory_order::check_lowering`, which
//! decodes them with its own decoder and refuses by name any unmapped form or
//! any form weaker than the mapping requires. Each function's form is also
//! pinned exactly (`expected_form`), so a selector change that stays
//! conformant is still visible. Mutation controls rewrite the emitted words
//! the way each plausible selector defect would (the pre-L03-P3 release fence
//! `DMB ISHST` first among them) and require a named refusal.
//!
//! Evidence strength: MAPPING CONFORMANCE, exhaustive over the selector's
//! request space on these profiles; the ordering contribution of each
//! instruction is the ARM architecture specification and the mapping's
//! whole-program soundness is the published C11 -> ARMv8 compilation result,
//! neither re-checked here. Not a memory-model proof.

use std::collections::BTreeMap;

use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::target::{AArch64IsaProfile, TargetSpec};
use trust_cg_lower::instructions::AtomicOrdering;
use trust_cg_verify::aarch64_memory_order::{
    AtomicKind, AtomicRequest, MemoryOrderRefusal, OrderingTarget, check_lowering,
    cmpxchg_failure_lift_table, llvm_reference, render_table,
};
use trust_ir::{
    AtomicRMWOp, Block, BlockId, FuncId, FuncTy, Function, Inst, InstrNode, Linkage, Module,
    Ordering, Ty, ValueId,
};

#[path = "common/function_words.rs"]
mod function_words;
#[path = "common/native_host.rs"]
mod native_host;

const TRIPLE: &str = "aarch64-apple-darwin";
const OPT_LEVELS: [OptLevel; 4] = [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3];
const ORDERINGS: [Ordering; 5] = [
    Ordering::Relaxed,
    Ordering::Acquire,
    Ordering::Release,
    Ordering::AcqRel,
    Ordering::SeqCst,
];
const RMW_OPS: [(AtomicRMWOp, &str); 10] = [
    (AtomicRMWOp::Add, "add"),
    (AtomicRMWOp::Sub, "sub"),
    (AtomicRMWOp::And, "and"),
    (AtomicRMWOp::Or, "or"),
    (AtomicRMWOp::Xor, "xor"),
    (AtomicRMWOp::Xchg, "xchg"),
    (AtomicRMWOp::Max, "smax"),
    (AtomicRMWOp::Min, "smin"),
    (AtomicRMWOp::UMax, "umax"),
    (AtomicRMWOp::UMin, "umin"),
];

fn lir(ordering: Ordering) -> AtomicOrdering {
    match ordering {
        Ordering::Relaxed => AtomicOrdering::Relaxed,
        Ordering::Acquire => AtomicOrdering::Acquire,
        Ordering::Release => AtomicOrdering::Release,
        Ordering::AcqRel => AtomicOrdering::AcqRel,
        Ordering::SeqCst => AtomicOrdering::SeqCst,
    }
}

/// `(type, memory bytes, name)` for every width the selector admits.
fn widths() -> [(Ty, u32, &'static str); 6] {
    [
        (Ty::Bool, 1, "b1"),
        (Ty::I8, 1, "i8"),
        (Ty::I16, 2, "i16"),
        (Ty::I32, 4, "i32"),
        (Ty::I64, 8, "i64"),
        (Ty::I128, 16, "i128"),
    ]
}

/// The profile a lane compiles for.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Lane {
    DarwinAot,
    Lse,
    Baseline,
}

impl Lane {
    const ALL: [Self; 3] = [Self::DarwinAot, Self::Lse, Self::Baseline];

    fn name(self) -> &'static str {
        match self {
            Self::DarwinAot => "darwin-aot",
            Self::Lse => "lse",
            Self::Baseline => "baseline",
        }
    }

    fn lse(self) -> bool {
        self != Self::Baseline
    }

    fn target(self) -> OrderingTarget {
        OrderingTarget {
            lse2: self == Self::DarwinAot,
        }
    }

    fn compile(self, module: &Module, opt_level: OptLevel) -> Vec<u8> {
        match self {
            Self::DarwinAot => {
                Compiler::new_for_target_spec(
                    CompilerConfig {
                        opt_level,
                        ..CompilerConfig::default()
                    },
                    TargetSpec::parse(TRIPLE).expect("triple parses"),
                )
                .with_codegen_license(permit_unlicensed())
                .compile(module)
                .unwrap_or_else(|error| panic!("darwin-aot {opt_level:?}: {error}"))
                .object_code
            }
            Self::Lse | Self::Baseline => native_host::compile_with_isa_profile_for(
                TRIPLE,
                module,
                opt_level,
                if self == Self::Lse {
                    AArch64IsaProfile::LSE
                } else {
                    AArch64IsaProfile::BASELINE
                },
            )
            .unwrap_or_else(|error| panic!("{} {opt_level:?}: {error}", self.name())),
        }
    }
}

/// One function: its request, and the RMW op stem when it is an RMW.
#[derive(Debug, Clone)]
struct Case {
    request: AtomicRequest,
    rmw_stem: Option<&'static str>,
}

fn ptr(ty: &Ty) -> Ty {
    Ty::PtrMut(Box::new(ty.clone()))
}

fn add_function(
    module: &mut Module,
    name: &str,
    params: Vec<Ty>,
    returns: Vec<Ty>,
    body: Vec<InstrNode>,
) {
    let sig = module
        .add_func_type(FuncTy {
            params: params.clone(),
            returns,
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let id = FuncId::new(module.functions.len() as u32);
    let mut function = Function::new(id, name, sig, BlockId::new(0));
    function.linkage = Linkage::External;
    function.blocks = vec![Block {
        id: BlockId::new(0),
        params: params
            .into_iter()
            .enumerate()
            .map(|(index, ty)| (ValueId::new(index as u32), ty))
            .collect(),
        body,
    }];
    module.functions.push(function);
}

fn ret(values: &[u32]) -> InstrNode {
    InstrNode::new(Inst::Return {
        values: values.iter().map(|&value| ValueId::new(value)).collect(),
    })
}

/// LSE opcode stem the selector uses for each RMW op (`sub` is LDADD of the
/// negated operand, `and` is LDCLR of the inverted one).
fn lse_stem(op: AtomicRMWOp) -> &'static str {
    match op {
        AtomicRMWOp::Add | AtomicRMWOp::Sub => "LDADD",
        AtomicRMWOp::And => "LDCLR",
        AtomicRMWOp::Or => "LDSET",
        AtomicRMWOp::Xor => "LDEOR",
        AtomicRMWOp::Max => "LDSMAX",
        AtomicRMWOp::Min => "LDSMIN",
        AtomicRMWOp::UMax => "LDUMAX",
        AtomicRMWOp::UMin => "LDUMIN",
        AtomicRMWOp::Xchg => "SWP",
    }
}

/// Every request the selector admits, one function each.
fn obligations_module() -> (Module, BTreeMap<String, Case>) {
    let mut module = Module::new("memory_order_obligations");
    let mut cases = BTreeMap::new();
    let mut add = |module: &mut Module,
                   name: String,
                   case: Case,
                   params: Vec<Ty>,
                   returns: Vec<Ty>,
                   body: Vec<InstrNode>| {
        add_function(module, &name, params, returns, body);
        assert!(cases.insert(name, case).is_none());
    };
    for (ty, bytes, width) in widths() {
        for ordering in ORDERINGS {
            if lir(ordering).is_legal_for_load() {
                add(
                    &mut module,
                    format!("load_{width}_{ordering:?}"),
                    Case {
                        request: AtomicRequest::load(bytes, lir(ordering)),
                        rmw_stem: None,
                    },
                    vec![ptr(&ty)],
                    vec![ty.clone()],
                    vec![
                        InstrNode::new(Inst::AtomicLoad {
                            ty: ty.clone(),
                            ptr: ValueId::new(0),
                            ordering,
                        })
                        .with_result(ValueId::new(1)),
                        ret(&[1]),
                    ],
                );
            }
            if lir(ordering).is_legal_for_store() {
                add(
                    &mut module,
                    format!("store_{width}_{ordering:?}"),
                    Case {
                        request: AtomicRequest::store(bytes, lir(ordering)),
                        rmw_stem: None,
                    },
                    vec![ptr(&ty), ty.clone()],
                    vec![],
                    vec![
                        InstrNode::new(Inst::AtomicStore {
                            ty: ty.clone(),
                            ptr: ValueId::new(0),
                            value: ValueId::new(1),
                            ordering,
                        }),
                        ret(&[]),
                    ],
                );
            }
            for (op, op_name) in RMW_OPS {
                let bool_ok = matches!(
                    op,
                    AtomicRMWOp::Xchg | AtomicRMWOp::And | AtomicRMWOp::Or | AtomicRMWOp::Xor
                );
                if ty == Ty::Bool && !bool_ok {
                    continue;
                }
                add(
                    &mut module,
                    format!("rmw_{op_name}_{width}_{ordering:?}"),
                    Case {
                        request: AtomicRequest::rmw(bytes, lir(ordering)),
                        rmw_stem: Some(lse_stem(op)),
                    },
                    vec![ptr(&ty), ty.clone()],
                    vec![ty.clone()],
                    vec![
                        InstrNode::new(Inst::AtomicRMW {
                            op,
                            ty: ty.clone(),
                            ptr: ValueId::new(0),
                            value: ValueId::new(1),
                            ordering,
                        })
                        .with_result(ValueId::new(2)),
                        ret(&[2]),
                    ],
                );
            }
            for failure in [Ordering::Relaxed, Ordering::Acquire, Ordering::SeqCst] {
                add(
                    &mut module,
                    format!("cas_{width}_{ordering:?}_{failure:?}"),
                    Case {
                        request: AtomicRequest::cmpxchg(bytes, lir(ordering), lir(failure)),
                        rmw_stem: None,
                    },
                    vec![ptr(&ty), ty.clone(), ty.clone()],
                    vec![ty.clone()],
                    vec![
                        InstrNode::new(Inst::CmpXchg {
                            ty: ty.clone(),
                            ptr: ValueId::new(0),
                            expected: ValueId::new(1),
                            desired: ValueId::new(2),
                            success: ordering,
                            failure,
                            weak: false,
                        })
                        .with_results(vec![ValueId::new(3), ValueId::new(4)]),
                        ret(&[3]),
                    ],
                );
            }
        }
    }
    // A Relaxed fence is not in the request space: the pipeline refuses it
    // by name (see `orderings_without_a_mapping_row_never_reach_the_object`).
    for ordering in ORDERINGS.into_iter().skip(1) {
        add(
            &mut module,
            format!("fence_{ordering:?}"),
            Case {
                request: AtomicRequest::fence(lir(ordering)),
                rmw_stem: None,
            },
            vec![],
            vec![],
            vec![InstrNode::new(Inst::Fence { ordering }), ret(&[])],
        );
    }
    (module, cases)
}

/// `A`/`L` suffix of an LSE or exclusive form for an RMW-style ordering.
fn suffixes(ordering: AtomicOrdering) -> (&'static str, &'static str) {
    match ordering {
        AtomicOrdering::Relaxed => ("", ""),
        AtomicOrdering::Acquire => ("A", ""),
        AtomicOrdering::Release => ("", "L"),
        AtomicOrdering::AcqRel | AtomicOrdering::SeqCst => ("A", "L"),
    }
}

fn size_suffix(bytes: u32) -> &'static str {
    match bytes {
        1 => "B",
        2 => "H",
        _ => "",
    }
}

/// The exact form the selector emits for `case` on `lane`, in the checker's
/// mnemonic spelling: the trust-cg mapping restated, so any selection change
/// is visible even when it stays conformant.
fn expected_form(case: &Case, lane: Lane) -> String {
    let request = case.request;
    let bytes = request.bytes;
    let s = size_suffix(bytes);
    // The selector lifts a compare-exchange's success ordering to cover the
    // failure ordering; every other kind uses its one ordering.
    let ordering = request.failure.map_or(request.ordering, |failure| {
        request.ordering.lift_for_cmpxchg_failure(failure)
    });
    let (a, l) = suffixes(ordering);
    let exclusive_loop = |extra_store: bool, clrex: bool| {
        let (load, store) = if bytes == 16 {
            (format!("LD{a}XP"), format!("ST{l}XP ({bytes} B)"))
        } else {
            (format!("LD{a}XR{s}"), format!("ST{l}XR{s} ({bytes} B)"))
        };
        let mut parts = vec![load, store.clone()];
        if extra_store {
            parts.push(store);
        }
        if clrex {
            parts.push("CLREX".to_string());
        }
        parts.join("; ")
    };
    match request.kind {
        AtomicKind::Fence => match request.ordering {
            AtomicOrdering::Relaxed => String::new(),
            AtomicOrdering::Acquire => "DMB ISHLD".to_string(),
            _ => "DMB ISH".to_string(),
        },
        AtomicKind::Load if bytes == 16 => match (lane, request.ordering) {
            (Lane::DarwinAot, AtomicOrdering::Relaxed) => "LDP (16 B)".to_string(),
            (Lane::DarwinAot, AtomicOrdering::Acquire) => "LDP (16 B); DMB ISHLD".to_string(),
            (Lane::DarwinAot, _) => "DMB ISH; LDP (16 B); DMB ISH".to_string(),
            // The LL/SC load: Relaxed LDXP/STXP, Acquire LDAXP/STXP, SeqCst
            // LDAXP/STLXP.
            (_, AtomicOrdering::Relaxed) => "LDXP; STXP (16 B)".to_string(),
            (_, AtomicOrdering::Acquire) => "LDAXP; STXP (16 B)".to_string(),
            _ => "LDAXP; STLXP (16 B)".to_string(),
        },
        AtomicKind::Load => format!("LDAR{s} ({bytes} B)"),
        AtomicKind::Store if bytes == 16 => match request.ordering {
            AtomicOrdering::Relaxed => "LDXP; STXP (16 B)".to_string(),
            AtomicOrdering::Release => "LDXP; STLXP (16 B)".to_string(),
            _ => "LDAXP; STLXP (16 B)".to_string(),
        },
        AtomicKind::Store => format!("STLR{s} ({bytes} B)"),
        AtomicKind::Rmw if bytes == 16 || !lane.lse() => exclusive_loop(false, false),
        AtomicKind::Rmw => format!(
            "{}{a}{l}{s} ({bytes} B)",
            case.rmw_stem.expect("an RMW case carries its stem")
        ),
        AtomicKind::CmpXchg if bytes == 16 => exclusive_loop(true, false),
        AtomicKind::CmpXchg if !lane.lse() => exclusive_loop(false, true),
        AtomicKind::CmpXchg => format!("CAS{a}{l}{s} ({bytes} B)"),
    }
}

/// Compile every lane at every level once (the objects are large).
fn objects() -> Vec<(Lane, OptLevel, BTreeMap<String, Vec<u32>>)> {
    let (module, _) = obligations_module();
    let mut out = Vec::new();
    for lane in Lane::ALL {
        for opt_level in OPT_LEVELS {
            let object = lane.compile(&module, opt_level);
            out.push((lane, opt_level, function_words::function_words(&object)));
        }
    }
    out
}

#[test]
fn every_selected_atomic_form_implements_its_c11_ordering() {
    let (_, cases) = obligations_module();
    let mut checked = 0usize;
    let mut table = Vec::new();
    for (lane, opt_level, functions) in objects() {
        let label = format!("{} {opt_level:?}", lane.name());
        assert_eq!(
            functions.keys().collect::<Vec<_>>(),
            cases.keys().collect::<Vec<_>>(),
            "{label}: defined functions"
        );
        let mut problems = Vec::new();
        for (name, case) in &cases {
            let words = &functions[name];
            match check_lowering(&case.request, lane.target(), words) {
                Ok(row) => {
                    let want = expected_form(case, lane);
                    if row.form.mnemonic != want {
                        problems.push(format!(
                            "{name}: form `{}`, expected `{want}`",
                            row.form.mnemonic
                        ));
                    }
                    if lane == Lane::DarwinAot && opt_level == OptLevel::O2 {
                        table.push((row, llvm_reference(&case.request, true)));
                    }
                }
                Err(refusal) => problems.push(format!("{name}: {refusal}")),
            }
            checked += 1;
        }
        assert!(problems.is_empty(), "{label}: {problems:#?}");
    }
    assert_eq!(checked, cases.len() * Lane::ALL.len() * OPT_LEVELS.len());
    // The rendered table (darwin-aot, O2) is the ordering-obligation table
    // LIMITATIONS.md describes: request, trust-cg form, LLVM form, and where
    // the trust-cg form is stronger than required.
    table.sort_by_key(|(row, _)| row.request.to_string());
    table.dedup_by_key(|(row, _)| row.request);
    eprintln!("{}", render_table(&table));
    eprintln!("memory-order obligations: {checked} (function, lane, level) rows conform");
}

#[test]
fn the_request_space_covers_every_kind_width_and_legal_ordering() {
    let (_, cases) = obligations_module();
    let count = |kind| {
        cases
            .values()
            .filter(|case| case.request.kind == kind)
            .count()
    };
    // 6 widths x 3 legal load orderings; the same for stores.
    assert_eq!(count(AtomicKind::Load), 18);
    assert_eq!(count(AtomicKind::Store), 18);
    // (5 integer widths x 10 ops + bool x 4 ops) x 5 orderings.
    assert_eq!(count(AtomicKind::Rmw), (5 * 10 + 4) * 5);
    // 6 widths x the 15 valid (success, failure) pairs.
    assert_eq!(count(AtomicKind::CmpXchg), 6 * 15);
    assert_eq!(count(AtomicKind::Fence), 4);
    // The lifting obligation behind every compare-exchange row.
    let lifts = cmpxchg_failure_lift_table().unwrap_or_else(|refusal| panic!("{refusal}"));
    assert_eq!(lifts.iter().filter(|row| row.lifted.is_some()).count(), 15);
    assert!(lifts.iter().all(|row| row.minimal));
}

/// The orderings with no mapping row are refused by name before any word is
/// emitted: a releasing load, an acquiring store and a releasing failure
/// ordering by the adapter (trust-ir legality), and a Relaxed fence (a C11
/// no-op that Rust's `fence` panics on) by dataflow-integrity enforcement,
/// which refuses an effectful instruction that emits nothing.
#[test]
fn orderings_without_a_mapping_row_never_reach_the_object() {
    let mut module = Module::new("memory_order_refused_fence");
    add_function(
        &mut module,
        "refused",
        vec![],
        vec![],
        vec![
            InstrNode::new(Inst::Fence {
                ordering: Ordering::Relaxed,
            }),
            ret(&[]),
        ],
    );
    let error = Lane::DarwinAot
        .compile_result(&module)
        .expect_err("a Relaxed fence must be refused");
    assert!(error.contains("dataflow-integrity"), "{error}");
    let compile = |inst: Inst, params: Vec<Ty>, returns: Vec<Ty>, result: bool| {
        let mut module = Module::new("memory_order_refused");
        let node = if result {
            InstrNode::new(inst).with_result(ValueId::new(params.len() as u32))
        } else {
            InstrNode::new(inst)
        };
        let values: Vec<u32> = if result {
            vec![params.len() as u32]
        } else {
            vec![]
        };
        add_function(
            &mut module,
            "refused",
            params,
            returns,
            vec![node, ret(&values)],
        );
        Lane::DarwinAot.compile_result(&module)
    };
    for ordering in [Ordering::Release, Ordering::AcqRel] {
        let error = compile(
            Inst::AtomicLoad {
                ty: Ty::I64,
                ptr: ValueId::new(0),
                ordering,
            },
            vec![ptr(&Ty::I64)],
            vec![Ty::I64],
            true,
        )
        .expect_err("a releasing load must be refused");
        assert!(error.contains("ordering"), "{ordering:?}: {error}");
    }
    for ordering in [Ordering::Acquire, Ordering::AcqRel] {
        let error = compile(
            Inst::AtomicStore {
                ty: Ty::I64,
                ptr: ValueId::new(0),
                value: ValueId::new(1),
                ordering,
            },
            vec![ptr(&Ty::I64), Ty::I64],
            vec![],
            false,
        )
        .expect_err("an acquiring store must be refused");
        assert!(error.contains("ordering"), "{ordering:?}: {error}");
    }
    for failure in [Ordering::Release, Ordering::AcqRel] {
        let mut module = Module::new("memory_order_refused_cas");
        add_function(
            &mut module,
            "refused",
            vec![ptr(&Ty::I64), Ty::I64, Ty::I64],
            vec![Ty::I64],
            vec![
                InstrNode::new(Inst::CmpXchg {
                    ty: Ty::I64,
                    ptr: ValueId::new(0),
                    expected: ValueId::new(1),
                    desired: ValueId::new(2),
                    success: Ordering::SeqCst,
                    failure,
                    weak: false,
                })
                .with_results(vec![ValueId::new(3), ValueId::new(4)]),
                ret(&[3]),
            ],
        );
        let error = Lane::DarwinAot
            .compile_result(&module)
            .expect_err("a releasing failure ordering must be refused");
        assert!(error.contains("rdering"), "{failure:?}: {error}");
    }
}

impl Lane {
    fn compile_result(self, module: &Module) -> Result<Vec<u8>, String> {
        Compiler::new_for_target_spec(
            CompilerConfig::default(),
            TargetSpec::parse(TRIPLE).expect("triple parses"),
        )
        .with_codegen_license(permit_unlicensed())
        .compile(module)
        .map(|result| result.object_code)
        .map_err(|error| error.to_string())
    }
}

/// Each plausible selector defect, applied to the words the selector really
/// emitted, is refused by name. The first is the pre-L03-P3 release fence.
#[test]
fn ordering_mutations_of_the_emitted_words_are_refused_by_name() {
    let (_, cases) = obligations_module();
    let darwin = Lane::DarwinAot.compile(&obligations_module().0, OptLevel::O2);
    let darwin = function_words::function_words(&darwin);
    let baseline = Lane::Baseline.compile(&obligations_module().0, OptLevel::O2);
    let baseline = function_words::function_words(&baseline);
    const DMB_ISH: u32 = 0xD503_3BBF;
    const DMB_ISHST: u32 = 0xD503_3ABF;
    const DMB_NSH: u32 = 0xD503_37BF;
    let is_dmb = |word: u32| word & 0xFFFF_F0FF == 0xD503_30BF;
    let ldar = |word: u32| word & 0x3FFF_FC00 == 0x08DF_FC00;
    let lse_rmw = |word: u32| word & 0x3F20_0C00 == 0x3820_0000;
    let lse_cas = |word: u32| word & 0x3FA0_7C00 == 0x08A0_7C00;
    let load_exclusive = |word: u32| word & 0x3FDF_0000 == 0x085F_0000;
    let store_exclusive = |word: u32| word & 0x3FC0_0000 == 0x0800_0000;
    type Mutate = Box<dyn Fn(&[u32]) -> Vec<u32>>;
    let map = |f: Box<dyn Fn(u32) -> u32>| -> Mutate {
        Box::new(move |words: &[u32]| words.iter().map(|&w| f(w)).collect())
    };
    let check = |name: &str, objects: &BTreeMap<String, Vec<u32>>, target, mutate: &Mutate| {
        let words = &objects[name];
        let mutated = mutate(words);
        assert_ne!(&mutated, words, "{name}: the mutation changed nothing");
        let request = cases[name].request;
        check_lowering(&request, target, &mutated)
            .map(|row| row.form.mnemonic)
            .expect_err(&format!("{name}: a weakened form was admitted"))
    };
    let lse2 = OrderingTarget { lse2: true };
    let no_lse2 = OrderingTarget { lse2: false };
    /// (function, its lane's words, target, mutation, expected refusal).
    type Mutation<'a> = (
        &'static str,
        &'a BTreeMap<String, Vec<u32>>,
        OrderingTarget,
        Mutate,
        &'static str,
    );
    let mutations: Vec<Mutation<'_>> = vec![
        (
            "fence_Release",
            &darwin,
            lse2,
            map(Box::new(move |w| if w == DMB_ISH { DMB_ISHST } else { w })),
            "WeakerFence",
        ),
        (
            "fence_AcqRel",
            &darwin,
            lse2,
            map(Box::new(move |w| if w == DMB_ISH { DMB_ISHST } else { w })),
            "WeakerFence",
        ),
        (
            "fence_SeqCst",
            &darwin,
            lse2,
            map(Box::new(move |w| if w == DMB_ISH { DMB_NSH } else { w })),
            "WeakerFence",
        ),
        (
            "load_i64_SeqCst",
            &darwin,
            lse2,
            // LDAR -> LDAPR (RCpc).
            map(Box::new(move |w| {
                if ldar(w) {
                    0x38BF_C000 | (w & 0xC000_03FF)
                } else {
                    w
                }
            })),
            "MissingSeqCstEntry",
        ),
        (
            "load_i32_Acquire",
            &darwin,
            lse2,
            // LDAR -> LDR (unsigned offset 0).
            map(Box::new(move |w| {
                if ldar(w) {
                    0x3940_0000 | (w & 0xC000_03FF)
                } else {
                    w
                }
            })),
            "MissingAcquire",
        ),
        (
            "load_i128_SeqCst",
            &darwin,
            lse2,
            // LLVM's FEAT_LSE2 form: drop the leading DMB ISH.
            Box::new(move |words: &[u32]| {
                let first = words.iter().position(|&w| is_dmb(w)).expect("a barrier");
                let mut out = words.to_vec();
                out.remove(first);
                out
            }),
            "MissingSeqCstEntry",
        ),
        (
            "rmw_add_i64_SeqCst",
            &darwin,
            lse2,
            // LDADDAL -> LDADDL.
            map(Box::new(
                move |w| if lse_rmw(w) { w & !0x0080_0000 } else { w },
            )),
            "MissingAcquire",
        ),
        (
            "rmw_xchg_i8_Release",
            &darwin,
            lse2,
            // SWPLB -> SWPB.
            map(Box::new(
                move |w| if lse_rmw(w) { w & !0x0040_0000 } else { w },
            )),
            "MissingRelease",
        ),
        (
            "rmw_umax_i16_AcqRel",
            &darwin,
            lse2,
            // Rt -> XZR: acquire semantics dropped.
            map(Box::new(move |w| if lse_rmw(w) { w | 0x1F } else { w })),
            "MissingAcquire",
        ),
        (
            "cas_i32_Release_Acquire",
            &darwin,
            lse2,
            // CASAL -> CASL: the lifted failure acquire is lost.
            map(Box::new(
                move |w| if lse_cas(w) { w & !0x0040_0000 } else { w },
            )),
            "MissingAcquire",
        ),
        (
            "store_i16_Release",
            &darwin,
            lse2,
            // STLRH -> STRH.
            map(Box::new(move |w| {
                if w & 0x3FFF_FC00 == 0x089F_FC00 {
                    0x3900_0000 | (w & 0xC000_03FF)
                } else {
                    w
                }
            })),
            "MissingRelease",
        ),
        (
            "rmw_add_i64_Acquire",
            &baseline,
            no_lse2,
            // LDAXR -> LDXR.
            map(Box::new(
                move |w| if load_exclusive(w) { w & !0x8000 } else { w },
            )),
            "MissingAcquire",
        ),
        (
            "cas_i64_SeqCst_SeqCst",
            &baseline,
            no_lse2,
            // STLXR -> STXR.
            map(Box::new(
                move |w| if store_exclusive(w) { w & !0x8000 } else { w },
            )),
            "MissingRelease",
        ),
        (
            "store_i128_SeqCst",
            &baseline,
            no_lse2,
            // STLXP -> STXP.
            map(Box::new(
                move |w| if store_exclusive(w) { w & !0x8000 } else { w },
            )),
            "MissingRelease",
        ),
    ];
    for (name, objects, target, mutate, expected) in &mutations {
        let refusal: MemoryOrderRefusal = check(name, objects, *target, mutate);
        assert!(
            refusal.to_string().contains(expected),
            "{name}: expected {expected}, got {refusal}"
        );
    }
}

/// The words of the fences and the 128-bit SeqCst load, against Apple clang's
/// own selection for the same C11 operations (a native differential of the
/// emitted forms): every fence word is identical; the SeqCst 128-bit load
/// differs exactly by the leading `DMB ISH` this backend adds (L03-P3).
#[cfg(all(target_arch = "aarch64", target_os = "macos"))]
#[test]
fn fence_and_wide_load_words_match_clang_except_the_seq_cst_entry_barrier() {
    use std::process::Command;
    let directory = tempfile::Builder::new()
        .prefix("trust-cg-memory-order-")
        .tempdir()
        .unwrap();
    let source = directory.path().join("orders.c");
    let object = directory.path().join("orders.o");
    std::fs::write(
        &source,
        "#include <stdatomic.h>\n\
         void fence_Acquire(void) { atomic_thread_fence(memory_order_acquire); }\n\
         void fence_Release(void) { atomic_thread_fence(memory_order_release); }\n\
         void fence_AcqRel(void) { atomic_thread_fence(memory_order_acq_rel); }\n\
         void fence_SeqCst(void) { atomic_thread_fence(memory_order_seq_cst); }\n\
         __int128 load_i128_SeqCst(_Atomic __int128 *p) { return atomic_load_explicit(p, memory_order_seq_cst); }\n\
         __int128 load_i128_Acquire(_Atomic __int128 *p) { return atomic_load_explicit(p, memory_order_acquire); }\n",
    )
    .unwrap();
    let output = Command::new(native_host::C_COMPILER)
        .args(["-O2", "-arch", "arm64", "-c"])
        .arg(&source)
        .arg("-o")
        .arg(&object)
        .output()
        .expect("host C compiler");
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let clang = function_words::function_words(&std::fs::read(&object).unwrap());
    let ours = function_words::function_words(
        &Lane::DarwinAot.compile(&obligations_module().0, OptLevel::O2),
    );
    let barriers = |words: &[u32]| -> Vec<u32> {
        words
            .iter()
            .copied()
            .filter(|&w| w & 0xFFFF_F0FF == 0xD503_30BF)
            .collect()
    };
    for name in [
        "fence_Acquire",
        "fence_Release",
        "fence_AcqRel",
        "fence_SeqCst",
    ] {
        assert_eq!(barriers(&ours[name]), barriers(&clang[name]), "{name}");
    }
    assert_eq!(barriers(&ours["fence_Release"]), vec![0xD503_3BBF]);
    assert_eq!(
        barriers(&ours["load_i128_Acquire"]),
        barriers(&clang["load_i128_Acquire"])
    );
    let mut with_entry = vec![0xD503_3BBF];
    with_entry.extend(barriers(&clang["load_i128_SeqCst"]));
    assert_eq!(barriers(&ours["load_i128_SeqCst"]), with_entry);
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes, and no refusal is the license's, by accident.
fn permit_unlicensed() -> trust_cg_codegen::CodegenLicensePolicy {
    trust_cg_codegen::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_codegen::UnlicensedBodyPolicy::Permit)
}
