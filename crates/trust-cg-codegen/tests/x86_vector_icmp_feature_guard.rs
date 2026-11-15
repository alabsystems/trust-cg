// trust-cg-codegen/tests/x86_vector_icmp_feature_guard.rs — an available x86-64
// vector-compare cell compiles on exactly the targets that have its published
// `feature_guard`.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! trust-ir `docs/dialects.md` (the x86-64 per-cell rule, item 4, trust-ir
//! `7b0947ee`): the reader's verdict is the TRIPLE — status, reason AND
//! `feature_guard` — and an available cell may be lowered only on a target that
//! has its guard: the `v2_i64` `eq`/`ne` cells need `x86.sse4.1` (`pcmpeqq`)
//! and its signed `slt`/`sle`/`sgt`/`sge` cells `x86.sse4.2` (`pcmpgtq`); every
//! other available cell is baseline `x86.sse2`.
//!
//! This backend holds the guard where the instruction is CHOSEN, not at module
//! entry: x86 ISel emits `pcmpeqq` / `pcmpgtq` for exactly those cells, and the
//! x86 pipeline refuses either on a target without the feature
//! (`X86PipelineError::UnsupportedTargetFeature`). This test pins the agreement
//! per cell, derived from the reader: every available cell's module is lowered
//! for x86-64 and compiled at three cumulative feature levels (SSE2; +SSE4.1;
//! +SSE4.1+SSE4.2 — a CPU with SSE4.2 has SSE4.1), and it must compile exactly
//! from its guard's level up, refused below it by the feature rule.
//!
//! The four unsigned `<16 x i8>` cells (`icmp.ult`/`ule`/`ugt`/`uge` of
//! `chc_x86.v16_i8`), available since trust-ir `72dee4b6`, are also pinned BY
//! NAME: each must be available with the baseline `x86.sse2` guard and compile
//! at every level (the sign-bit bias `pxor` and `pcmpgtb`, plus `pcmpeqb` and
//! `por` for the inclusive predicates, are all SSE2). While they were
//! fail-closed the reader-derived loop skipped them; the named pin keeps the
//! loop from silently skipping them again. Test rung, not proof.

use trust_cg_codegen::x86_64::pipeline::X86RegAllocMode;
use trust_cg_codegen::x86_64::{
    X86OutputFormat, X86Pipeline, X86PipelineConfig, X86PipelineError, X86TargetFeature,
    X86TargetFeatures,
};
use trust_cg_lower::{
    GuardCarrierArch, TlsDialect, translate_module_for_arch_with_tls_with_license,
};
use trust_ir::{
    Block, BlockId, Endianness, FuncId, FuncTy, Function, ICmpOp, Inst, InstrNode, Module,
    StructPassingPolicy, TargetInfo, Ty, ValueId,
};

const OPS: [ICmpOp; 10] = [
    ICmpOp::Eq,
    ICmpOp::Ne,
    ICmpOp::Ult,
    ICmpOp::Ule,
    ICmpOp::Ugt,
    ICmpOp::Uge,
    ICmpOp::Slt,
    ICmpOp::Sle,
    ICmpOp::Sgt,
    ICmpOp::Sge,
];

/// The cumulative x86-64 feature levels, lowest first, with the manifest
/// guard each one first satisfies.
fn levels() -> [(&'static str, X86TargetFeatures); 3] {
    let sse2 = X86TargetFeatures::generic_x86_64();
    let sse41 = sse2.with_feature(X86TargetFeature::Sse41);
    let sse42 = sse41.with_feature(X86TargetFeature::Sse42);
    [
        ("x86.sse2", sse2),
        ("x86.sse4.1", sse41),
        ("x86.sse4.2", sse42),
    ]
}

fn compare_module(op: ICmpOp, elem: &Ty, lanes: u32) -> Module {
    let ty = Ty::Vector(Box::new(elem.clone()), lanes);
    let mask = Ty::Vector(Box::new(Ty::Bool), lanes);
    let mut module = Module::new("x86_vector_icmp_feature_guard");
    module.target_info = Some(TargetInfo {
        triple: "x86_64-unknown-linux-gnu".into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: None,
        struct_passing: StructPassingPolicy::NativeC,
    });
    let sig = module
        .add_func_type(FuncTy {
            params: vec![ty.clone(), ty.clone()],
            returns: vec![mask],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut func = Function::new(FuncId::new(0), "cmp", sig, BlockId::new(0));
    let mut block = Block::new(BlockId::new(0));
    block.params = vec![(ValueId::new(0), ty.clone()), (ValueId::new(1), ty.clone())];
    block.body.push(
        InstrNode::new(Inst::ICmp {
            op,
            ty,
            lhs: ValueId::new(0),
            rhs: ValueId::new(1),
        })
        .with_result(ValueId::new(2)),
    );
    block.body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(2)],
    }));
    func.blocks.push(block);
    module.functions.push(func);
    module
}

/// MUTATION CONTROL (recorded in the commit): mapping `Pcmpgtq` to no
/// required feature in the pipeline's opcode-feature table makes every
/// `v2_i64` signed cell compile at the SSE4.1 level, below its guard, and
/// this test fail naming each.
#[test]
fn available_cells_compile_exactly_from_their_feature_guard_up() {
    let mut failures = Vec::new();
    let mut checked = 0usize;
    let mut compiled_at_every_level: Vec<(u32, u32, ICmpOp, &'static str)> = Vec::new();
    for (elem, lanes) in [(Ty::I32, 4), (Ty::I64, 2), (Ty::I8, 16), (Ty::I16, 8)] {
        let bits = elem.bit_width().expect("integer lanes");
        for op in OPS {
            let cell = trust_ir::chc_x86_vector_icmp_cell_status(bits, lanes, op)
                .expect("the descriptor publishes a row for every ICmpOp");
            if cell.fail_closed() {
                continue;
            }
            let guard = cell
                .feature_guard
                .expect("an available cell publishes its feature guard");
            let what = format!("<{lanes} x i{bits}> {op:?} (guard {guard})");
            let Some(guard_level) = levels().iter().position(|(name, _)| *name == guard) else {
                failures.push(format!("{what}: a guard this test has no level for"));
                continue;
            };
            let lir = match translate_module_for_arch_with_tls_with_license(
                &compare_module(op, &elem, lanes),
                GuardCarrierArch::X86_64,
                TlsDialect::default(),
                &permit_unlicensed(),
            ) {
                Ok(functions) => functions,
                Err(error) => {
                    failures.push(format!("{what}: x86-64 module entry refused it: {error:?}"));
                    continue;
                }
            };
            checked += 1;
            let mut every_level = true;
            for (level, (name, features)) in levels().into_iter().enumerate() {
                let pipeline = X86Pipeline::new(X86PipelineConfig {
                    opt_level: trust_cg_opt::OptLevel::O0,
                    output_format: X86OutputFormat::RawBytes,
                    emit_frame: false,
                    regalloc_mode: X86RegAllocMode::Simplified,
                    target_features: features,
                    ..X86PipelineConfig::generic_x86_64()
                });
                let result = lir
                    .iter()
                    .try_for_each(|(func, _)| pipeline.compile_trust_ir_function(func).map(drop));
                every_level &= result.is_ok();
                match (level >= guard_level, result) {
                    (true, Ok(())) => {}
                    (false, Err(X86PipelineError::UnsupportedTargetFeature { .. })) => {}
                    (true, Err(error)) => failures.push(format!(
                        "{what}: refused at {name}, which has its guard: {error}"
                    )),
                    (false, Ok(())) => failures.push(format!(
                        "{what}: compiled at {name}, BELOW its published guard"
                    )),
                    (false, Err(error)) => failures.push(format!(
                        "{what}: refused at {name}, but not by the feature rule: {error}"
                    )),
                }
            }
            if every_level {
                compiled_at_every_level.push((bits, lanes, op, guard));
            }
        }
    }
    // The unsigned `<16 x i8>` cells, by name: available, baseline SSE2, and
    // compiled at every level.
    for op in [ICmpOp::Ult, ICmpOp::Ule, ICmpOp::Ugt, ICmpOp::Uge] {
        if !compiled_at_every_level.contains(&(8, 16, op, "x86.sse2")) {
            failures.push(format!(
                "<16 x i8> {op:?}: not an available x86.sse2 cell compiled at every level \
                 (the reader answers {:?})",
                trust_ir::chc_x86_vector_icmp_cell_status(8, 16, op)
            ));
        }
    }
    assert!(
        failures.is_empty(),
        "{} finding(s):\n  {}",
        failures.len(),
        failures.join("\n  ")
    );
    assert!(checked > 0, "some chc_x86 cell is available");
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes (or is refused) because the license silently refused it.
fn permit_unlicensed() -> trust_cg_codegen::CodegenLicensePolicy {
    trust_cg_codegen::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_codegen::UnlicensedBodyPolicy::Permit)
}
