// trust-cg-codegen/tests/aarch64_volatile_access_preservation.rs - volatile accesses survive to the final AArch64 stream
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! X-OPCODES-P6 at the pipeline boundary. Every AArch64 function preparation
//! decides that its final machine stream performs the lowered source's
//! volatile loads and stores on every path, in order, by direction and size
//! (`trust_cg_verify::volatile_access_preservation`), and fails closed
//! otherwise. This target:
//!
//! * compiles a volatile corpus — straight-line mixed widths, a loop with a
//!   runtime trip count, a diamond, a volatile access feeding control flow and
//!   a volatile store of a floating-point value — at O0 through O3 for the
//!   Linux GNU and Darwin triples, through the production `Compiler`, and
//!   requires every preparation to carry a preservation certificate that
//!   counts each side's accesses;
//! * takes a real prepared machine function and corrupts its stream the ways
//!   a wrong transformation would — deleting, duplicating, merging,
//!   reordering and resizing a volatile access, and replacing one by its plain
//!   twin — and requires the check to refute each;
//! * pins the stated limit: constant control flow around volatile accesses is
//!   either kept (certified) or, if a transformation removed a source path,
//!   REFUSED by name (the source graph assumes every edge is takeable); a
//!   stream with one diamond arm removed is refuted deterministically.
//!
//! Object-level only; nothing here executes. The dereferenced values and the
//! hardware memory model are outside the claim.

use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::pipeline::{OptLevel, Pipeline, PipelineConfig, PreparationMetrics};
use trust_cg_codegen::target::TargetSpec;
use trust_cg_ir::inst::{AArch64Opcode, MachInst};
use trust_cg_verify::volatile_access_preservation::{
    VolatileTraceOutcome, aarch64_volatile_trace, check_volatile_trace_preservation,
    lir_volatile_trace,
};
use trust_ir::{
    BinOp, Block, BlockId, Constant, FuncId, FuncTy, Function, ICmpOp, Inst, InstrNode, Module, Ty,
    ValueId,
};

const TRIPLES: [&str; 2] = ["aarch64-unknown-linux-gnu", "aarch64-apple-darwin"];
const OPT_LEVELS: [OptLevel; 4] = [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3];

fn v(id: u32) -> ValueId {
    ValueId::new(id)
}

fn node(inst: Inst, result: Option<u32>) -> InstrNode {
    let node = InstrNode::new(inst);
    match result {
        Some(id) => node.with_result(v(id)),
        None => node,
    }
}

fn vload(ty: Ty, ptr: u32, result: u32) -> InstrNode {
    node(
        Inst::Load {
            ty,
            ptr: v(ptr),
            volatile: true,
            align: None,
        },
        Some(result),
    )
}

fn vstore(ty: Ty, ptr: u32, value: u32) -> InstrNode {
    node(
        Inst::Store {
            ty,
            ptr: v(ptr),
            value: v(value),
            volatile: true,
            align: None,
        },
        None,
    )
}

fn iconst(ty: Ty, value: i128, result: u32) -> InstrNode {
    node(
        Inst::Const {
            ty,
            value: Constant::Int(value),
        },
        Some(result),
    )
}

fn ret() -> InstrNode {
    node(Inst::Return { values: vec![] }, None)
}

fn br(target: u32, args: Vec<u32>) -> InstrNode {
    node(
        Inst::Br {
            target: BlockId::new(target),
            args: args.into_iter().map(v).collect(),
        },
        None,
    )
}

fn condbr(cond: u32, then_target: u32, else_target: u32) -> InstrNode {
    node(
        Inst::CondBr {
            cond: v(cond),
            then_target: BlockId::new(then_target),
            then_args: vec![],
            else_target: BlockId::new(else_target),
            else_args: vec![],
        },
        None,
    )
}

fn block(id: u32, params: Vec<(u32, Ty)>, body: Vec<InstrNode>) -> Block {
    Block {
        id: BlockId::new(id),
        params: params.into_iter().map(|(id, ty)| (v(id), ty)).collect(),
        body,
    }
}

fn add(module: &mut Module, name: &str, params: Vec<Ty>, blocks: Vec<Block>) {
    let ty = module
        .add_func_type(FuncTy {
            params,
            returns: vec![],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let id = FuncId::new(module.functions.len() as u32);
    let mut function = Function::new(id, name, ty, BlockId::new(0));
    function.blocks = blocks;
    module
        .try_add_function(function)
        .expect("Module::try_add_function: test fixture");
}

/// The corpus that must compile, with every preparation certified.
fn corpus() -> Module {
    let mut module = Module::new("volatile_access_preservation");
    // Mixed widths and directions in one block.
    add(
        &mut module,
        "vol_straight",
        vec![Ty::Ptr],
        vec![block(
            0,
            vec![(0, Ty::Ptr)],
            vec![
                vload(Ty::I32, 0, 1),
                vstore(Ty::I32, 0, 1),
                vload(Ty::I8, 0, 2),
                iconst(Ty::I16, 7, 3),
                vstore(Ty::I16, 0, 3),
                vload(Ty::I64, 0, 4),
                vstore(Ty::I64, 0, 4),
                ret(),
            ],
        )],
    );
    // A loop with a runtime trip count.
    add(
        &mut module,
        "vol_loop",
        vec![Ty::Ptr, Ty::I32],
        vec![
            block(
                0,
                vec![(0, Ty::Ptr), (1, Ty::I32)],
                vec![iconst(Ty::I32, 0, 2), br(1, vec![2])],
            ),
            block(
                1,
                vec![(3, Ty::I32)],
                vec![
                    node(
                        Inst::ICmp {
                            op: ICmpOp::Slt,
                            ty: Ty::I32,
                            lhs: v(3),
                            rhs: v(1),
                        },
                        Some(4),
                    ),
                    condbr(4, 2, 3),
                ],
            ),
            block(
                2,
                vec![],
                vec![
                    vstore(Ty::I32, 0, 3),
                    iconst(Ty::I32, 1, 5),
                    node(
                        Inst::BinOp {
                            op: BinOp::Add,
                            ty: Ty::I32,
                            lhs: v(3),
                            rhs: v(5),
                        },
                        Some(6),
                    ),
                    br(1, vec![6]),
                ],
            ),
            block(3, vec![], vec![vload(Ty::I32, 0, 7), ret()]),
        ],
    );
    // A diamond whose arms differ, joined by one more access.
    add(
        &mut module,
        "vol_diamond",
        vec![Ty::Ptr, Ty::I32],
        vec![
            block(
                0,
                vec![(0, Ty::Ptr), (1, Ty::I32)],
                vec![
                    iconst(Ty::I32, 0, 2),
                    node(
                        Inst::ICmp {
                            op: ICmpOp::Ne,
                            ty: Ty::I32,
                            lhs: v(1),
                            rhs: v(2),
                        },
                        Some(3),
                    ),
                    condbr(3, 1, 2),
                ],
            ),
            block(1, vec![], vec![vload(Ty::I64, 0, 4), br(3, vec![])]),
            block(
                2,
                vec![],
                vec![iconst(Ty::I64, 5, 5), vstore(Ty::I64, 0, 5), br(3, vec![])],
            ),
            block(3, vec![], vec![vload(Ty::I16, 0, 6), ret()]),
        ],
    );
    // A volatile load deciding control flow (a status poll).
    add(
        &mut module,
        "vol_poll",
        vec![Ty::Ptr],
        vec![
            block(0, vec![(0, Ty::Ptr)], vec![br(1, vec![])]),
            block(
                1,
                vec![],
                vec![
                    vload(Ty::I32, 0, 1),
                    iconst(Ty::I32, 0, 2),
                    node(
                        Inst::ICmp {
                            op: ICmpOp::Eq,
                            ty: Ty::I32,
                            lhs: v(1),
                            rhs: v(2),
                        },
                        Some(3),
                    ),
                    condbr(3, 1, 2),
                ],
            ),
            block(2, vec![], vec![vstore(Ty::I32, 0, 1), ret()]),
        ],
    );
    // A floating-point value through FPR-width volatile accesses.
    add(
        &mut module,
        "vol_fp",
        vec![Ty::Ptr],
        vec![block(
            0,
            vec![(0, Ty::Ptr)],
            vec![
                vload(Ty::F64, 0, 1),
                vstore(Ty::F64, 0, 1),
                vload(Ty::F32, 0, 2),
                vstore(Ty::F32, 0, 2),
                ret(),
            ],
        )],
    );
    module
}

/// A lowered source function and its preparation result.
type Prepared = (
    trust_cg_lower::Function,
    Result<(trust_cg_ir::function::MachFunction, PreparationMetrics), String>,
);

fn prepare(module: &Module, triple: &str, opt_level: OptLevel) -> Vec<Prepared> {
    let lowered = permit_translate_module(module).expect("adapter");
    let pipeline = Pipeline::new(PipelineConfig {
        opt_level,
        target_triple: triple.into(),
        ..PipelineConfig::default()
    });
    lowered
        .into_iter()
        .map(|(function, proof_ctx)| {
            let prepared = pipeline
                .prepare_function_with_metrics(&function, Some(&proof_ctx))
                .map_err(|error| error.to_string());
            (function, prepared)
        })
        .collect()
}

#[test]
fn every_preparation_of_the_volatile_corpus_is_certified() {
    let module = corpus();
    let mut certified = 0;
    for triple in TRIPLES {
        for opt in OPT_LEVELS {
            for (source, prepared) in prepare(&module, triple, opt) {
                let (machine, metrics) = prepared
                    .unwrap_or_else(|error| panic!("{triple} {opt:?} {}: {error}", source.name));
                let certificate = metrics.volatile_access_preservation.unwrap_or_else(|| {
                    panic!("{} carries no preservation certificate", source.name)
                });
                let expected = lir_volatile_trace(&source)
                    .unwrap()
                    .reachable_access_count();
                assert!(expected > 0, "{}", source.name);
                assert_eq!(certificate.source_accesses, expected, "{}", source.name);
                assert!(certificate.machine_accesses >= 1, "{}", source.name);
                assert!(certificate.product_states > 0, "{}", source.name);
                // The certificate is reproducible from the returned stream.
                let recheck = check_volatile_trace_preservation(
                    &lir_volatile_trace(&source).unwrap(),
                    &aarch64_volatile_trace(&machine).unwrap(),
                )
                .unwrap();
                assert!(matches!(recheck, VolatileTraceOutcome::Preserved(_)));
                certified += 1;
            }
            // The one-shot `compile_to_object` route (Darwin triple) makes the
            // same decision and accepts the corpus too.
            if triple == "aarch64-apple-darwin" {
                for (source, _) in prepare(&module, triple, opt) {
                    trust_cg_codegen::pipeline::compile_to_object(&source, opt).unwrap_or_else(
                        |error| panic!("compile_to_object {opt:?} {}: {error}", source.name),
                    );
                }
            }
            // The production Compiler runs the same preparation.
            Compiler::new_for_target_spec(
                CompilerConfig {
                    opt_level: opt,
                    ..CompilerConfig::default()
                },
                TargetSpec::parse(triple).unwrap(),
            )
            .with_codegen_license(permit_unlicensed())
            .compile(&module)
            .unwrap_or_else(|error| panic!("{triple} {opt:?}: {error}"));
        }
    }
    assert_eq!(certified, TRIPLES.len() * OPT_LEVELS.len() * 5);
}

const VOLATILE: [AArch64Opcode; 6] = [
    AArch64Opcode::VolatileLdrRI,
    AArch64Opcode::VolatileLdrbRI,
    AArch64Opcode::VolatileLdrhRI,
    AArch64Opcode::VolatileStrRI,
    AArch64Opcode::VolatileStrbRI,
    AArch64Opcode::VolatileStrhRI,
];

/// Positions (block, index within block) of the volatile instructions.
fn volatile_sites(machine: &trust_cg_ir::function::MachFunction) -> Vec<(usize, usize)> {
    let mut sites = Vec::new();
    for &block in &machine.block_order {
        for (index, inst) in machine.blocks[block.0 as usize].insts.iter().enumerate() {
            if VOLATILE.contains(&machine.insts[inst.0 as usize].opcode) {
                sites.push((block.0 as usize, index));
            }
        }
    }
    sites
}

fn outcome(
    source: &trust_cg_lower::Function,
    machine: &trust_cg_ir::function::MachFunction,
) -> VolatileTraceOutcome {
    check_volatile_trace_preservation(
        &lir_volatile_trace(source).unwrap(),
        &aarch64_volatile_trace(machine).unwrap(),
    )
    .unwrap()
}

/// Corrupt a real prepared stream the ways a wrong pass would; each
/// corruption must be refuted.
#[test]
fn corrupted_final_streams_are_refuted() {
    let module = corpus();
    let prepared = prepare(&module, "aarch64-unknown-linux-gnu", OptLevel::O2);
    let (source, result) = prepared
        .into_iter()
        .find(|(function, _)| function.name == "vol_straight")
        .unwrap();
    let (machine, _) = result.unwrap();
    assert!(matches!(
        outcome(&source, &machine),
        VolatileTraceOutcome::Preserved(_)
    ));
    let sites = volatile_sites(&machine);
    assert_eq!(
        sites.len(),
        6,
        "vol_straight performs six volatile accesses"
    );
    let refuted = |mutated: &trust_cg_ir::function::MachFunction, what: &str| {
        assert!(
            matches!(outcome(&source, mutated), VolatileTraceOutcome::Violated(_)),
            "{what} was not refuted"
        );
    };

    // Delete each volatile access in turn.
    for &(block, index) in &sites {
        let mut deleted = machine.clone();
        deleted.blocks[block].insts.remove(index);
        refuted(&deleted, "a deleted volatile access");
    }
    // Duplicate each one in place.
    for &(block, index) in &sites {
        let mut duplicated = machine.clone();
        let copy = duplicated.insts[duplicated.blocks[block].insts[index].0 as usize].clone();
        let id = duplicated.push_inst(copy);
        duplicated.blocks[block].insts.insert(index + 1, id);
        refuted(&duplicated, "a duplicated volatile access");
    }
    // Replace each by its plain (non-volatile) twin: the access disappears
    // from the observable trace, as if a pass had demoted it.
    for &(block, index) in &sites {
        let mut demoted = machine.clone();
        let id = demoted.blocks[block].insts[index].0 as usize;
        demoted.insts[id].opcode = match demoted.insts[id].opcode {
            AArch64Opcode::VolatileLdrRI => AArch64Opcode::LdrRI,
            AArch64Opcode::VolatileLdrbRI => AArch64Opcode::LdrbRI,
            AArch64Opcode::VolatileLdrhRI => AArch64Opcode::LdrhRI,
            AArch64Opcode::VolatileStrRI => AArch64Opcode::StrRI,
            AArch64Opcode::VolatileStrbRI => AArch64Opcode::StrbRI,
            _ => AArch64Opcode::StrhRI,
        };
        refuted(&demoted, "a volatile access demoted to a plain one");
    }
    // Reorder: move the first volatile access (a 32-bit load) after the
    // second (a 32-bit store).
    let (block, first) = sites[0];
    let (block2, second) = sites[1];
    assert_eq!(block, block2);
    let mut reordered = machine.clone();
    let moved = reordered.blocks[block].insts.remove(first);
    reordered.blocks[block].insts.insert(second, moved);
    refuted(
        &reordered,
        "a volatile load reordered past a volatile store",
    );
    // Merge: the 64-bit load stands in for the 32-bit load and the 8-bit
    // load (one wider access instead of two).
    let mut merged = machine.clone();
    let load64 = {
        let (b, i) = sites[4];
        merged.blocks[b].insts[i]
    };
    let (b0, i0) = sites[0];
    merged.blocks[b0].insts[i0] = load64;
    let (b2, i2) = sites[2];
    merged.blocks[b2].insts.remove(i2);
    refuted(&merged, "two volatile loads merged into one wider load");

    // Resize: the same accesses in the same order and number, one of them at
    // another width (the 32-bit load performed as an 8-bit LDRB, the 64-bit
    // store as a 16-bit STRH). Only the size label tells these streams from
    // the source, so a check that matched labels by direction alone would
    // accept them.
    for (site, narrower) in [
        (0, AArch64Opcode::VolatileLdrbRI),
        (5, AArch64Opcode::VolatileStrhRI),
    ] {
        let mut resized = machine.clone();
        let (b, i) = sites[site];
        let id = resized.blocks[b].insts[i].0 as usize;
        assert_ne!(resized.insts[id].opcode, narrower);
        resized.insts[id].opcode = narrower;
        refuted(&resized, "a volatile access performed at another width");
    }

    // The trace sees the plain twin only as absent; a fabricated volatile
    // access where the source has none is refuted too.
    let mut fabricated = machine.clone();
    let extra = MachInst::new(
        AArch64Opcode::VolatileStrbRI,
        machine.insts[machine.blocks[sites[2].0].insts[sites[2].1].0 as usize]
            .operands
            .clone(),
    );
    let id = fabricated.push_inst(extra);
    fabricated.blocks[sites[5].0]
        .insts
        .insert(sites[5].1 + 1, id);
    refuted(&fabricated, "a fabricated volatile store");
}

/// Constant control flow around volatile accesses. The source graph assumes
/// every edge is takeable, so a transformation that resolved a constant
/// branch or a constant trip count would remove source paths: the function
/// must then be REFUSED by name, never accepted with a trace the check
/// cannot relate. Every preparation here is either certified with equal
/// traces or refused; `outcomes` records which, and the edge-removal control
/// below makes the refusal arm run deterministically.
#[test]
fn constant_control_is_certified_or_refused_never_accepted_silently() {
    let mut module = Module::new("volatile_constant_control");
    add(
        &mut module,
        "vol_const_branch",
        vec![Ty::Ptr],
        vec![
            block(
                0,
                vec![(0, Ty::Ptr)],
                vec![
                    node(
                        Inst::Const {
                            ty: Ty::Bool,
                            value: Constant::Bool(true),
                        },
                        Some(1),
                    ),
                    condbr(1, 1, 2),
                ],
            ),
            block(
                1,
                vec![],
                vec![iconst(Ty::I32, 1, 2), vstore(Ty::I32, 0, 2), br(2, vec![])],
            ),
            block(2, vec![], vec![ret()]),
        ],
    );
    // for i in 0..4 { write_volatile(p, i) }
    add(
        &mut module,
        "vol_const_trip",
        vec![Ty::Ptr],
        vec![
            block(
                0,
                vec![(0, Ty::Ptr)],
                vec![iconst(Ty::I32, 0, 1), br(1, vec![1])],
            ),
            block(
                1,
                vec![(2, Ty::I32)],
                vec![
                    iconst(Ty::I32, 4, 3),
                    node(
                        Inst::ICmp {
                            op: ICmpOp::Slt,
                            ty: Ty::I32,
                            lhs: v(2),
                            rhs: v(3),
                        },
                        Some(4),
                    ),
                    condbr(4, 2, 3),
                ],
            ),
            block(
                2,
                vec![],
                vec![
                    vstore(Ty::I32, 0, 2),
                    iconst(Ty::I32, 1, 5),
                    node(
                        Inst::BinOp {
                            op: BinOp::Add,
                            ty: Ty::I32,
                            lhs: v(2),
                            rhs: v(5),
                        },
                        Some(6),
                    ),
                    br(1, vec![6]),
                ],
            ),
            block(3, vec![], vec![ret()]),
        ],
    );
    let mut outcomes = Vec::new();
    for opt in OPT_LEVELS {
        for (source, prepared) in prepare(&module, "aarch64-unknown-linux-gnu", opt) {
            match prepared {
                Ok((machine, metrics)) => {
                    assert!(metrics.volatile_access_preservation.is_some());
                    assert!(matches!(
                        outcome(&source, &machine),
                        VolatileTraceOutcome::Preserved(_)
                    ));
                    outcomes.push(format!("{opt:?} {}: certified", source.name));
                }
                Err(error) => {
                    assert!(
                        error.contains("volatile access preservation check rejected"),
                        "{opt:?} {}: {error}",
                        source.name
                    );
                    outcomes.push(format!("{opt:?} {}: refused", source.name));
                }
            }
        }
    }
    eprintln!("constant control around volatile accesses: {outcomes:#?}");
    assert_eq!(outcomes.len(), 2 * OPT_LEVELS.len());
}

/// A final stream that lost one arm of a diamond (an edge removed as a
/// resolved branch would remove it) is refuted.
#[test]
fn a_removed_path_is_refuted() {
    let prepared = prepare(&corpus(), "aarch64-unknown-linux-gnu", OptLevel::O2);
    let (source, result) = prepared
        .into_iter()
        .find(|(function, _)| function.name == "vol_diamond")
        .unwrap();
    let (machine, _) = result.unwrap();
    assert!(matches!(
        outcome(&source, &machine),
        VolatileTraceOutcome::Preserved(_)
    ));
    let mut refuted = 0;
    for &block in &machine.block_order {
        let succs = machine.blocks[block.0 as usize].succs.clone();
        if succs.len() < 2 {
            continue;
        }
        for dropped in &succs {
            let mut pruned = machine.clone();
            pruned.blocks[block.0 as usize]
                .succs
                .retain(|succ| succ != dropped);
            if matches!(outcome(&source, &pruned), VolatileTraceOutcome::Violated(_)) {
                refuted += 1;
            }
        }
    }
    assert!(
        refuted >= 2,
        "both diamond arms must be observable: {refuted}"
    );
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
