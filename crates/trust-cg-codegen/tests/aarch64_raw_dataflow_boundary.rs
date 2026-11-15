// Copyright 2026 Andrew Yates | Apache-2.0
//! TV-3 observes raw ISel, not the legitimately merged optimized CFG. Native
//! execution and structural mutation controls are regressions, not final-code
//! semantic or proof-composition authority.

#![cfg(all(
    target_arch = "aarch64",
    any(target_os = "macos", all(target_os = "linux", target_env = "gnu"))
))]
// Test fixture: the big `Err` is the compiler's own public error type, not this file's to shrink.
#![allow(clippy::result_large_err)]

#[path = "common/aarch64_native.rs"]
#[allow(dead_code)] // This fixture selects proof policy itself; only link_run is shared.
mod native;

// `native` (common/aarch64_native.rs) already loads `common/rosetta.rs`;
// reuse that single copy rather than compiling the file into this target a
// second time.
use crate::native::process;

#[path = "common/native_host.rs"]
mod native_host;

use trust_cg_codegen::compiler::{Compiler, CompilerConfig, CompilerTraceLevel};
use trust_cg_codegen::pipeline::{OptLevel, Pipeline, PipelineConfig};
use trust_cg_codegen::target::TargetSpec;
use trust_cg_ir::{AArch64Opcode, InstId, MachFunction, MachInst};
use trust_cg_lower::abi::AArch64AbiVariant;
use trust_cg_lower::isel::InstructionSelector;
use trust_cg_verify::dataflow_integrity::{DataflowViolationKind, check_function};
use trust_ir::{Endianness, Module, StructPassingPolicy, TargetInfo, Ty};
use trust_ir_build::ModuleBuilder;

fn source() -> (Module, trust_cg_lower::Function) {
    let mut builder = ModuleBuilder::new("raw_dataflow_boundary");
    let signature = builder.add_func_type(vec![Ty::U64], vec![Ty::U64]);
    let provider = builder.declare_function("raw_provider", signature);
    let mut function = builder.function("raw_wrapper", signature);
    let entry = function.create_block();
    let value = function.add_block_param(entry, Ty::U64);
    let continuation = function.create_block();
    function.switch_to_block(entry);
    let returned = function.call(provider, vec![value]);
    function.br(continuation, vec![]);
    function.switch_to_block(continuation);
    let nine = function.iconst(Ty::U64, 9);
    let answer = function.add(Ty::U64, returned, nine);
    function.ret(vec![answer]);
    function.build();
    let mut module = builder.build().expect("ModuleBuilder::build: test fixture");
    module.target_info = Some(TargetInfo {
        triple: native_host::TRIPLE.into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: Some("aapcs64".into()),
        struct_passing: StructPassingPolicy::NativeC,
    });
    let function = module
        .functions
        .iter()
        .find(|function| function.name == "raw_wrapper")
        .unwrap();
    let (lir, _) =
        trust_cg_lower::translate_function_with_license(function, &module, &permit_unlicensed())
            .unwrap();
    (module, lir)
}

fn raw_selection(source: &trust_cg_lower::Function) -> MachFunction {
    let mut selector = InstructionSelector::new(source.name.clone(), source.signature.clone());
    selector.set_abi_variant(AArch64AbiVariant::Aapcs64);
    selector.seed_value_types(&source.value_types);
    selector.seed_iconst_origins(
        source
            .blocks
            .values()
            .map(|block| block.instructions.as_slice()),
    );
    selector.seed_function_value_use_counts(source);
    selector
        .lower_formal_arguments(&source.signature, source.entry_block)
        .unwrap();
    for block in source.layout_order() {
        let body = &source.blocks[&block];
        if block != source.entry_block {
            selector.define_block_params(&body.params);
        }
        selector.select_block(block, &body.instructions).unwrap();
    }
    selector.finalize().to_ir_func()
}

fn pipeline(level: OptLevel) -> Pipeline {
    Pipeline::new(PipelineConfig {
        opt_level: level,
        target_triple: native_host::TRIPLE.into(),
        ..Default::default()
    })
}

#[test]
fn valid_cfg_merging_keeps_raw_observation_and_final_structural_refusal() {
    let (_, source) = source();
    let raw = raw_selection(&source);
    assert!(check_function(&raw, &source, "aarch64").is_empty());
    for level in [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3] {
        trust_cg_process_env::with_env_overrides(&[("TCG_DATAFLOW_INTEGRITY", "enforce")], || {
            let pipeline = pipeline(level);
            let (prepared, metrics) = pipeline
                .prepare_function_with_metrics(&source, None)
                .unwrap();
            let observed = metrics
                .pre_optimization_dataflow_integrity
                .as_ref()
                .expect("real raw observation");
            assert!(observed.was_evaluated() && observed.was_enforced());
            assert_eq!(observed.function(), source.name);
            assert_eq!(observed.source_blocks(), 2);
            assert!(observed.machine_instructions() > 0);
            if matches!(level, OptLevel::O2 | OptLevel::O3) {
                assert!(
                    check_function(&prepared, &source, "aarch64")
                        .iter()
                        .any(|violation| violation.kind
                            == DataflowViolationKind::MultipleSourceBlocks),
                    "fixture must exercise the old wrong-phase failure at {level:?}"
                );
            }
            let mut malformed = prepared.clone();
            let return_block = malformed
                .blocks
                .iter()
                .position(|block| {
                    block
                        .insts
                        .iter()
                        .any(|id| malformed.inst(*id).opcode == AArch64Opcode::Ret)
                })
                .unwrap();
            let id = InstId(malformed.insts.len() as u32);
            malformed
                .insts
                .push(MachInst::new(AArch64Opcode::AddRR, vec![]));
            malformed.blocks[return_block].insts.push(id);
            assert!(
                pipeline.compile_module(&[malformed]).is_err(),
                "a raw observation cannot excuse malformed final code"
            );
        });
    }
}

#[test]
fn diagnostic_compiler_and_direct_pipeline_execute_calls_with_raw_enforcement() {
    let (module, source) = source();
    let driver = r#"
#include <stdint.h>
static uint64_t calls;
uint64_t raw_provider(uint64_t x) { calls++; return x * 17 - 5; }
extern uint64_t raw_wrapper(uint64_t);
int main(void) {
    for (uint64_t x = 0; x < 256; x++) {
        if (raw_wrapper(x) != x * 17 + 4) return 1;
        if (calls != x + 1) return 2;
    }
    return 0;
}

"#;
    for level in [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3] {
        // Native behavior is diagnostic, not proof-emitting compilation: the
        // frame pairs have no source-bound proof. Keep the raw gate enforced
        // on both execution routes and test proof-required refusal separately.
        let result = trust_cg_process_env::with_env_overrides(
            &[("TCG_DATAFLOW_INTEGRITY", "enforce")],
            || {
                Compiler::new_for_target_spec(
                    CompilerConfig {
                        opt_level: level,
                        emit_proofs: false,
                        trace_level: CompilerTraceLevel::Full,
                        ..Default::default()
                    },
                    TargetSpec::parse(native_host::TRIPLE).unwrap(),
                )
                .with_codegen_license(permit_unlicensed())
                .compile(&module)
            },
        )
        .unwrap_or_else(|error| panic!("{level:?}: {error}"));
        let trace = result.trace.as_ref().unwrap();
        assert!(trace.entries.iter().any(|entry| {
            entry.phase == "dataflow_integrity"
                && entry
                    .detail
                    .as_deref()
                    .unwrap_or("")
                    .contains("raw pre-optimization")
        }));
        assert_eq!(
            native::link_run("raw_tv3_compiler", &result.object_code, driver),
            Some(0)
        );
        let object = trust_cg_process_env::with_env_overrides(
            &[("TCG_DATAFLOW_INTEGRITY", "enforce")],
            || pipeline(level).compile_function(&source),
        )
        .unwrap();
        assert_eq!(
            native::link_run("raw_tv3_direct_pipeline", &object, driver),
            Some(0)
        );
    }
    eprintln!(
        "raw TV-3 boundary: 2 entry points x O0-O3 x 256 native calls = 2048 calls, 4096 value/effect checks"
    );
}

/// The raw-integrity opt-out never makes a proof-emitting compile publish.
///
/// Owner ruling 2026-09-29 (`bound_memory_authority`): the wrapper's frame
/// `STP`/`LDP` rows are no longer the unproved rows — each is credited by the
/// replayed committed certificate of its pair FORM theorem — so the refusal
/// must come from the rows that remain uncredited, and must not list a pair
/// opcode. (Before the ruling the pair rows were refused as sampled
/// obligations; earlier still, as unmapped opcodes.) On a host whose
/// `drat-trim` bytes the bound-memory manifest does not qualify, the pair rows
/// are uncredited (a fail-closed checker-identity miss) and ARE listed; that
/// host's one red test is `bound_memory_set_binds_the_exact_runtime_checker_bytes`.
#[test]
fn proof_emitting_calls_refuse_unproved_frame_pairs_even_with_raw_opt_out() {
    use trust_cg_codegen::compiler::CompileError;
    use trust_cg_codegen::target::Target;

    let (module, _) = source();
    let pairs_credited =
        trust_cg_verify::bound_memory_authority::bound_memory_checker_qualification().is_ok();
    for level in [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3] {
        let error =
            trust_cg_process_env::with_env_overrides(&[("TCG_DATAFLOW_INTEGRITY", "off")], || {
                Compiler::new_for_target_spec(
                    CompilerConfig {
                        opt_level: level,
                        emit_proofs: true,
                        trace_level: CompilerTraceLevel::Full,
                        ..Default::default()
                    },
                    TargetSpec::parse(native_host::TRIPLE).unwrap(),
                )
                .with_codegen_license(permit_unlicensed())
                .compile(&module)
            })
            .expect_err("raw integrity cannot certify the wrapper's uncredited rows");
        assert!(
            matches!(error, CompileError::ProofPromotionRejected {
            target: Target::Aarch64, ref reason,
        } if reason.contains("raw_wrapper")
            && reason.contains("uncovered non-pseudo opcode(s)")
            && reason.contains("AArch64::StpPreIndex") != pairs_credited
            && reason.contains("AArch64::LdpPostIndex") != pairs_credited),
            "{level:?} (pairs credited: {pairs_credited}): {error}"
        );
    }
    // This early-refusal test does not observe raw-check metrics on a failed
    // compile. The compiler-private policy regression exercises that earlier
    // phase directly under ambient off, before object proof promotion.
}

#[test]
fn dynamic_bounds_guard_falls_through_or_traps_with_raw_enforcement_at_all_tiers() {
    use sha2::{Digest, Sha256};
    use std::{fs, process::Command};
    use trust_ir::{
        Block, BlockId, FuncId, FuncTy, ICmpOp, Inst, InstrNode, ProofAnnotation, ValueId,
    };

    let mut module = Module::new("guard_fallthrough");
    let signature = module
        .add_func_type(FuncTy {
            params: vec![Ty::U64, Ty::U64],
            returns: vec![Ty::Bool],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut function = trust_ir::Function::new(
        FuncId::new(47),
        "guarded_predicate",
        signature,
        BlockId::new(9),
    );
    let (a, b, result) = (ValueId::new(101), ValueId::new(303), ValueId::new(707));
    let mut compare = InstrNode::new(Inst::ICmp {
        op: ICmpOp::Ult,
        ty: Ty::U64,
        lhs: a,
        rhs: b,
    })
    .with_result(result);
    compare.proofs.push(ProofAnnotation::InBounds);
    function.blocks.push(Block {
        id: function.entry,
        params: vec![(a, Ty::U64), (b, Ty::U64)],
        body: vec![
            compare,
            InstrNode::new(Inst::Return {
                values: vec![result],
            }),
        ],
    });
    module
        .try_add_function(function)
        .expect("Module::try_add_function: test fixture");
    let (lir, proofs) = trust_cg_lower::translate_function_with_license(
        &module.functions[0],
        &module,
        &permit_unlicensed(),
    )
    .unwrap();
    assert!(
        lir.blocks
            .values()
            .flat_map(|b| &b.instructions)
            .any(|inst| matches!(
                inst.opcode,
                trust_cg_lower::instructions::Opcode::GuardBoundsCheckDyn { .. }
            ))
    );
    let raw = raw_selection(&lir);
    assert!(check_function(&raw, &lir, "aarch64").is_empty());
    assert!(matches!(
        trust_cg_verify::aarch64_affine_lowering::check_aarch64_trust_ir_affine_lowering(&module, 0, &lir, &raw),
        Err(trust_cg_verify::aarch64_affine_lowering::TrustIrAffineLoweringError::UnsupportedTrustIr(_))
    ), "native guard behavior is not a pure-predicate receipt");

    let directory_scratch = crate::fresh_dir::create("trust-cg-guard-fallthrough-");
    let directory = directory_scratch.to_path_buf();
    eprintln!("Guard fallthrough native evidence={directory:?}");
    fs::write(directory.join("source.trustir"), format!("{module:#?}")).unwrap();
    fs::write(directory.join("source.lir"), format!("{lir:#?}")).unwrap();
    fs::write(directory.join("source.raw.machir"), format!("{raw:#?}")).unwrap();
    fs::write(directory.join("driver.c"), r#"
#include <stdint.h>
#include <stdbool.h>
#include <stdio.h>
#include <signal.h>
#include <sys/resource.h>
#include <sys/wait.h>
#include <unistd.h>
extern bool guarded_predicate(uint64_t, uint64_t);
int main(void) {
    const struct rlimit no_core = {0, 0};
    if (setrlimit(RLIMIT_CORE, &no_core)) return 90;
    const uint64_t valid[][2] = {
        {0,1}, {1,2}, {4095,4096}, {UINT64_C(0x7fffffffffffffff), UINT64_C(0x8000000000000000)},
        {UINT64_C(0x8000000000000000), UINT64_MAX}, {UINT64_MAX-1,UINT64_MAX}, {0,UINT64_MAX}, {17,4095}
    };
    const uint64_t invalid[][2] = {
        {0,0}, {1,1}, {2,1}, {UINT64_MAX,UINT64_MAX}, {UINT64_MAX,0},
        {UINT64_C(0x8000000000000000), UINT64_C(0x7fffffffffffffff)}
    };
    for (unsigned i=0; i<8; ++i) if (!guarded_predicate(valid[i][0],valid[i][1])) return 1;
    for (unsigned i=0; i<6; ++i) {
        pid_t child=fork(); if (child<0) return 91;
        if (child==0) { (void)guarded_predicate(invalid[i][0],invalid[i][1]); _exit(92); }
        int status=0;
        if (waitpid(child,&status,0)!=child || !WIFSIGNALED(status) || WTERMSIG(status)!=SIGTRAP) {
            fprintf(stderr,"case=%u status=%d expected SIGTRAP\n",i,status); return 2;
        }
    }
    puts("PASS 8 fallthrough returns and 6 observed SIGTRAP exits");
    return 0;
}
"#).unwrap();

    for level in [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3] {
        let tier = directory.join(format!("{level:?}"));
        fs::create_dir(&tier).unwrap();
        let pipeline = pipeline(level);
        let (prepared, metrics) = trust_cg_process_env::with_env_overrides(
            &[("TCG_DATAFLOW_INTEGRITY", "enforce")],
            || pipeline.prepare_function_with_metrics(&lir, Some(&proofs)),
        )
        .unwrap();
        let observed = metrics
            .pre_optimization_dataflow_integrity
            .as_ref()
            .unwrap();
        assert!(observed.was_evaluated() && observed.was_enforced());
        fs::write(tier.join("prepared.machir"), format!("{prepared:#?}")).unwrap();
        fs::write(tier.join("metrics.txt"), format!("{metrics:#?}")).unwrap();
        let object = pipeline.compile_module(&[prepared]).unwrap();
        native_host::assert_native_object(&object);
        fs::write(tier.join("module.o"), object).unwrap();
        let mut link = Command::new("cc");
        link.args(["-O2", "-std=c11", "-Wall", "-Wextra", "-Werror"])
            .args(native_host::link_hardening_args())
            .arg(directory.join("driver.c"))
            .arg(tier.join("module.o"))
            .arg("-o")
            .arg(tier.join("driver"));
        fs::write(
            tier.join("link.command"),
            format!("{link:?}\ntimeout={:?}\n", process::codegen_link_timeout()),
        )
        .unwrap();
        let link = process::command_output_with_timeout(&mut link, process::codegen_link_timeout())
            .unwrap();
        fs::write(tier.join("link.stderr"), &link.output.stderr).unwrap();
        fs::write(
            tier.join("link.status"),
            format!("{:?} timed_out={}\n", link.output.status, link.timed_out),
        )
        .unwrap();
        assert!(
            !link.timed_out && link.output.status.success(),
            "{directory:?}: {}",
            String::from_utf8_lossy(&link.output.stderr)
        );
        let run = process::run_executable_with_timeout(
            &tier.join("driver"),
            process::codegen_run_timeout(),
        )
        .unwrap();
        fs::write(tier.join("stdout.log"), &run.output.stdout).unwrap();
        fs::write(tier.join("stderr.log"), &run.output.stderr).unwrap();
        fs::write(
            tier.join("run.status"),
            format!("{:?} timed_out={}\n", run.output.status, run.timed_out),
        )
        .unwrap();
        assert!(
            !run.timed_out && run.output.status.success(),
            "{directory:?}: {}",
            String::from_utf8_lossy(&run.output.stderr)
        );
        assert_eq!(
            String::from_utf8(run.output.stdout).unwrap().trim(),
            "PASS 8 fallthrough returns and 6 observed SIGTRAP exits"
        );
        let mut paths: Vec<_> = fs::read_dir(&tier)
            .unwrap()
            .map(|entry| entry.unwrap().path())
            .collect();
        paths.sort();
        let sums = paths
            .iter()
            .map(|path| {
                format!(
                    "{:x}  {}\n",
                    Sha256::digest(fs::read(path).unwrap()),
                    path.file_name().unwrap().to_string_lossy()
                )
            })
            .collect::<String>();
        fs::write(tier.join("SHA256SUMS"), sums).unwrap();
        println!("GUARD_NATIVE_CENSUS tier={level:?} fallthrough=8 trapped=6 retained={tier:?}");
    }
}

#[test]
fn narrow_register_offset_gathers_survive_real_spills_and_frame_lowering() {
    use sha2::{Digest, Sha256};
    use std::{fs, process::Command};
    use trust_cg_ir::aarch64_regs::preg_class;
    use trust_cg_ir::{MachOperand, RegClass};

    const LANES: usize = 64;
    let mut builder = ModuleBuilder::new("narrow_ro_pipeline");
    let signature = builder.add_func_type(vec![Ty::Ptr, Ty::Ptr, Ty::Ptr], vec![]);
    for (name, ty) in [("narrow_gather_u8", Ty::U8), ("narrow_gather_u16", Ty::U16)] {
        let mut function = builder.function(name, signature);
        let entry = function.create_block();
        let data = function.add_block_param(entry, Ty::Ptr);
        let indices = function.add_block_param(entry, Ty::Ptr);
        let output = function.add_block_param(entry, Ty::Ptr);
        function.switch_to_block(entry);
        // All 64 runtime indices are live before the first gather. Volatile
        // source loads are not rematerializable constants. Keep all gathered
        // values live until the final stores, so pressure is real on both sides.
        let mut live_indices = Vec::with_capacity(LANES);
        for lane in 0..LANES {
            let lane = function.iconst(Ty::U64, lane as i128);
            let address = function.gep(Ty::U32, indices, vec![lane]);
            live_indices.push(function.load_volatile(Ty::U32, address));
        }
        let mut values = Vec::with_capacity(LANES);
        for index in live_indices {
            let address = function.gep(ty.clone(), data, vec![index]);
            let value = function.load(ty.clone(), address);
            values.push(function.zext(ty.clone(), Ty::U64, value));
        }
        for (lane, value) in values.into_iter().enumerate() {
            let lane = function.iconst(Ty::U64, lane as i128);
            let address = function.gep(Ty::U64, output, vec![lane]);
            function.store(Ty::U64, address, value);
        }
        function.ret(vec![]);
        function.build();
    }
    let mut module = builder.build().expect("ModuleBuilder::build: test fixture");
    module.target_info = Some(TargetInfo {
        triple: native_host::TRIPLE.into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: Some("aapcs64".into()),
        struct_passing: StructPassingPolicy::NativeC,
    });
    let directory_scratch = crate::fresh_dir::create("trust-cg-narrow-ro-pipeline-");
    let directory = directory_scratch.to_path_buf();
    eprintln!("Narrow RO pipeline native evidence={directory:?}");
    fs::write(directory.join("source.trustir"), format!("{module:#?}")).unwrap();
    let source_errors = trust_ir_build::validate_module(&module);
    assert!(source_errors.is_empty(), "{source_errors:#?}");
    let pipeline = Pipeline::new(PipelineConfig {
        opt_level: OptLevel::O2,
        target_triple: native_host::TRIPLE.into(),
        disabled_passes_override: Some(String::new()),
        ..Default::default()
    });
    let mut functions = Vec::new();
    for (function, ri, ro) in [
        (
            &module.functions[0],
            AArch64Opcode::LdrbRI,
            AArch64Opcode::LdrbRO,
        ),
        (
            &module.functions[1],
            AArch64Opcode::LdrhRI,
            AArch64Opcode::LdrhRO,
        ),
    ] {
        let (lir, proofs) = trust_cg_lower::translate_function_with_license(
            function,
            &module,
            &permit_unlicensed(),
        )
        .unwrap();
        let raw = raw_selection(&lir);
        fs::write(
            directory.join(format!("{}.lir", lir.name)),
            format!("{lir:#?}"),
        )
        .unwrap();
        fs::write(
            directory.join(format!("{}.raw.machir", lir.name)),
            format!("{raw:#?}"),
        )
        .unwrap();
        assert_eq!(
            raw.blocks
                .iter()
                .flat_map(|b| &b.insts)
                .filter(|id| raw.inst(**id).opcode == ri)
                .count(),
            LANES
        );
        assert!(
            !raw.blocks
                .iter()
                .flat_map(|b| &b.insts)
                .any(|id| raw.inst(*id).opcode == ro),
            "RO must come from the optimizer"
        );
        let (prepared, metrics) = trust_cg_process_env::with_env_overrides(
            &[("TCG_DATAFLOW_INTEGRITY", "enforce")],
            || pipeline.prepare_function_with_metrics(&lir, Some(&proofs)),
        )
        .unwrap();
        fs::write(
            directory.join(format!("{}.prepared.machir", lir.name)),
            format!("{prepared:#?}"),
        )
        .unwrap();
        fs::write(
            directory.join(format!("{}.metrics.txt", lir.name)),
            format!("{metrics:#?}"),
        )
        .unwrap();
        let observed = metrics
            .pre_optimization_dataflow_integrity
            .as_ref()
            .unwrap();
        assert!(observed.was_evaluated() && observed.was_enforced());
        assert_eq!(observed.function(), lir.name);
        assert!(metrics.spill_slot_count > 0, "{}: {metrics:#?}", lir.name);
        assert!(
            metrics.timings.optimization.is_some()
                && metrics.timings.regalloc.is_some()
                && metrics.timings.frame_lowering.is_some()
        );
        let active: Vec<_> = prepared
            .blocks
            .iter()
            .flat_map(|b| &b.insts)
            .map(|id| prepared.inst(*id))
            .collect();
        assert!(
            active.iter().any(|inst| inst.opcode == ro),
            "{}: no final RO",
            lir.name
        );
        assert_eq!(
            active
                .iter()
                .filter(|inst| inst.opcode == ri || inst.opcode == ro)
                .count(),
            LANES
        );
        assert!(
            active
                .iter()
                .all(|inst| inst.operands.iter().all(|operand| !matches!(
                    operand,
                    MachOperand::VReg(_)
                        | MachOperand::FrameIndex(_)
                        | MachOperand::StackSlot(_)
                        | MachOperand::IncomingArg(_)
                )))
        );
        // This is an actual resolved reload feeding an RO index, not merely an
        // unrelated spill-slot count. Do not prescribe every allocator choice.
        let index_reloads = prepared
            .blocks
            .iter()
            .flat_map(|block| block.insts.windows(2))
            .filter(|pair| {
                let load = prepared.inst(pair[0]);
                let gather = prepared.inst(pair[1]);
                if load.opcode != AArch64Opcode::LdrRI || gather.opcode != ro {
                    return false;
                }
                let (Some(loaded), Some(index)) = (
                    load.operands.first().and_then(MachOperand::as_preg),
                    gather.operands.get(2).and_then(MachOperand::as_preg),
                ) else {
                    return false;
                };
                preg_class(loaded) == RegClass::Gpr32
                    && matches!(loaded.hw_enc(), 16 | 17)
                    && index.hw_enc() == loaded.hw_enc()
                    && matches!(preg_class(index), RegClass::Gpr32 | RegClass::Gpr64)
            })
            .count();
        assert!(
            index_reloads > 0,
            "{}: no actual W spill reload feeding RO",
            lir.name
        );
        fs::write(directory.join(format!("{}.census.txt", lir.name)),
            format!("source_gathers={LANES} final_ro={} spill_slots={} adjacent_index_reloads={index_reloads}\n",
                active.iter().filter(|inst| inst.opcode == ro).count(), metrics.spill_slot_count)).unwrap();
        functions.push(prepared);
    }
    // Compile the exact inspected prepared functions once. This diagnostic
    // object/native path does not request or claim final proof promotion.
    let object = pipeline.compile_module(&functions).unwrap();
    native_host::assert_native_object(&object);
    fs::write(directory.join("module.o"), object).unwrap();
    fs::write(
        directory.join("driver.c"),
        r#"
#include <stdint.h>
#include <stdio.h>
#include <inttypes.h>
enum { N=131072, LANES=64, PATTERNS=16 };
extern void narrow_gather_u8(const uint8_t *, const uint32_t *, uint64_t *);
extern void narrow_gather_u16(const uint16_t *, const uint32_t *, uint64_t *);
static unsigned failures, calls, lanes_checked;
static uint32_t index_at(unsigned p, unsigned lane) {
    switch (lane % 8) { case 0:return 0; case 1:return N-1; case 2:return 1; case 3:return N-2; }
    return (lane*37u+p*251u) % N;
}
static uint8_t byte_at(unsigned p, unsigned i) {
    switch ((i+p)%8) { case 0:return 0; case 1:return 255; case 2:return 128; case 3:return 127; }
    return (uint8_t)((i*29u+p*17u) ^ (i>>8) ^ ((i>>16)*0x5bu));
}
static uint16_t half_at(unsigned p, unsigned i) {
    static const uint16_t boundary[]={0,65535,32768,32767,255,65280,256};
    unsigned k=(i+p)%8;
    return k<7 ? boundary[k] : (uint16_t)((i*499u+p*8191u) ^ ((i>>16)*0x9e37u));
}
static void check(uint64_t got, uint64_t want, unsigned p, unsigned width, unsigned lane) {
    if (got != want && ++failures <= 8)
        fprintf(stderr,"p=%u width=%u lane=%u got=%016" PRIx64 " want=%016" PRIx64 "\n",
                p,width,lane,got,want);
}
int main(void) {
    // Oracle discrimination only: neither masked address is passed to CG.
    // Keep both widths sensitive to lost index bits, even if patterns change.
    const uint32_t masks[]={0xffu,0xffffu};
    const uint32_t endpoint=N-1;
    unsigned oracle_failures=0;
    for (unsigned m=0;m<2;m++) {
        unsigned byte_witnesses=0, half_witnesses=0;
        for (unsigned p=0;p<PATTERNS;p++) {
            byte_witnesses += byte_at(p,endpoint) != byte_at(p,endpoint&masks[m]);
            half_witnesses += half_at(p,endpoint) != half_at(p,endpoint&masks[m]);
        }
        if (!byte_witnesses) {
            fprintf(stderr,"ORACLE byte index mask=%" PRIx32 " not distinguished\n",masks[m]);
            oracle_failures++;
        }
        if (!half_witnesses) {
            fprintf(stderr,"ORACLE half index mask=%" PRIx32 " not distinguished\n",masks[m]);
            oracle_failures++;
        }
    }
    if (oracle_failures) return 2;
    uint8_t bytes[N+2]; uint16_t halves[N+2]; uint32_t indices[LANES+2]; uint64_t out[LANES+2];
    for (unsigned p=0;p<PATTERNS;p++) {
        bytes[0]=0x5a; bytes[N+1]=0xa5; halves[0]=0x1234; halves[N+1]=0xabcd;
        indices[0]=0x12345678; indices[LANES+1]=0xabcdef01;
        for (unsigned i=0;i<N;i++) { bytes[i+1]=byte_at(p,i); halves[i+1]=half_at(p,i); }
        for (unsigned i=0;i<LANES;i++) indices[i+1]=index_at(p,i);
        for (unsigned width=1;width<=2;width++) {
            out[0]=UINT64_C(0x0123456789abcdef); out[LANES+1]=UINT64_C(0xfedcba9876543210);
            for (unsigned i=0;i<LANES;i++) out[i+1]=UINT64_C(0xfedcba9876543210);
            if (width==1) narrow_gather_u8(bytes+1,indices+1,out+1);
            else narrow_gather_u16(halves+1,indices+1,out+1);
            calls++;
            // Volatile reads observe initialized primitive elements, not padded
            // structs or reconstructed pointers. No object aliases another.
            for (unsigned i=0;i<LANES;i++) {
                uint32_t index=index_at(p,i);
                uint64_t want=width==1 ? byte_at(p,index) : half_at(p,index);
                check(((volatile uint64_t *)out)[i+1],want,p,width,i); lanes_checked++;
                check(((volatile uint32_t *)indices)[i+1],index,p,width,i);
            }
            for (unsigned i=0;i<N;i++) {
                check(((volatile uint8_t *)bytes)[i+1],byte_at(p,i),p,width,i);
                check(((volatile uint16_t *)halves)[i+1],half_at(p,i),p,width,i);
            }
            check(((volatile uint64_t *)out)[0],UINT64_C(0x0123456789abcdef),p,width,LANES);
            check(((volatile uint64_t *)out)[LANES+1],UINT64_C(0xfedcba9876543210),p,width,LANES+1);
            check(((volatile uint32_t *)indices)[0],0x12345678,p,width,LANES);
            check(((volatile uint32_t *)indices)[LANES+1],0xabcdef01,p,width,LANES+1);
            check(((volatile uint8_t *)bytes)[0],0x5a,p,width,N);
            check(((volatile uint8_t *)bytes)[N+1],0xa5,p,width,N+1);
            check(((volatile uint16_t *)halves)[0],0x1234,p,width,N);
            check(((volatile uint16_t *)halves)[N+1],0xabcd,p,width,N+1);
        }
    }
    if (calls!=32 || lanes_checked!=2048 || failures) return 1;
    puts("PASS narrow RO pipeline calls=32 lane_outputs=2048");
    return 0;
}
"#,
    )
    .unwrap();
    let mut link = Command::new("cc");
    link.args(["-O2", "-std=c11", "-Wall", "-Wextra", "-Werror"])
        .args(native_host::link_hardening_args())
        .arg(directory.join("driver.c"))
        .arg(directory.join("module.o"))
        .arg("-o")
        .arg(directory.join("driver"));
    fs::write(
        directory.join("link.command"),
        format!("{link:?}\ntimeout={:?}\n", process::codegen_link_timeout()),
    )
    .unwrap();
    let link =
        process::command_output_with_timeout(&mut link, process::codegen_link_timeout()).unwrap();
    fs::write(directory.join("link.stdout"), &link.output.stdout).unwrap();
    fs::write(directory.join("link.stderr"), &link.output.stderr).unwrap();
    fs::write(
        directory.join("link.status"),
        format!("{:?} timed_out={}\n", link.output.status, link.timed_out),
    )
    .unwrap();
    assert!(
        !link.timed_out && link.output.status.success(),
        "{directory:?}: {}",
        String::from_utf8_lossy(&link.output.stderr)
    );
    fs::write(
        directory.join("run.command"),
        format!(
            "{:?}\ntimeout={:?}\n",
            directory.join("driver"),
            process::codegen_run_timeout()
        ),
    )
    .unwrap();
    let run = process::run_executable_with_timeout(
        &directory.join("driver"),
        process::codegen_run_timeout(),
    )
    .unwrap();
    fs::write(directory.join("stdout.log"), &run.output.stdout).unwrap();
    fs::write(directory.join("stderr.log"), &run.output.stderr).unwrap();
    fs::write(
        directory.join("run.status"),
        format!("{:?} timed_out={}\n", run.output.status, run.timed_out),
    )
    .unwrap();
    assert!(
        !run.timed_out && run.output.status.success(),
        "{directory:?}: {}",
        String::from_utf8_lossy(&run.output.stderr)
    );
    assert!(run.output.stderr.is_empty());
    assert_eq!(
        run.output.stdout,
        b"PASS narrow RO pipeline calls=32 lane_outputs=2048\n"
    );
    let mut paths: Vec<_> = fs::read_dir(&directory)
        .unwrap()
        .map(|entry| entry.unwrap().path())
        .collect();
    paths.sort();
    let sums = paths
        .iter()
        .map(|path| {
            format!(
                "{:x}  {}\n",
                Sha256::digest(fs::read(path).unwrap()),
                path.file_name().unwrap().to_string_lossy()
            )
        })
        .collect::<String>();
    fs::write(directory.join("SHA256SUMS"), sums).unwrap();
}

/// Straight-line LIR for one block, numbering results from `Value(1)`
/// (`Value(0)` is the first formal argument). Every slot access forms its own
/// `StackAddr`, as the trust-ir adapter does.
struct SlotLadder {
    instructions: Vec<trust_cg_lower::instructions::Instruction>,
    next: u32,
}

impl SlotLadder {
    fn op(
        &mut self,
        opcode: trust_cg_lower::instructions::Opcode,
        args: Vec<trust_cg_lower::instructions::Value>,
    ) -> trust_cg_lower::instructions::Value {
        let result = trust_cg_lower::instructions::Value(self.next);
        self.next += 1;
        self.instructions
            .push(trust_cg_lower::instructions::Instruction {
                opcode,
                args,
                results: vec![result],
            });
        result
    }

    fn effect(
        &mut self,
        opcode: trust_cg_lower::instructions::Opcode,
        args: Vec<trust_cg_lower::instructions::Value>,
    ) {
        self.instructions
            .push(trust_cg_lower::instructions::Instruction {
                opcode,
                args,
                results: vec![],
            });
    }

    fn i32_const(&mut self, imm: i64) -> trust_cg_lower::instructions::Value {
        self.op(
            trust_cg_lower::instructions::Opcode::Iconst {
                ty: trust_cg_lower::Type::I32,
                imm,
            },
            vec![],
        )
    }

    fn slot_addr(&mut self) -> trust_cg_lower::instructions::Value {
        self.op(
            trust_cg_lower::instructions::Opcode::StackAddr { slot: 0 },
            vec![],
        )
    }

    fn load_slot(&mut self) -> trust_cg_lower::instructions::Value {
        let addr = self.slot_addr();
        self.op(
            trust_cg_lower::instructions::Opcode::Load {
                ty: trust_cg_lower::Type::I32,
                align: Some(4),
            },
            vec![addr],
        )
    }

    fn store_slot(&mut self, value: trust_cg_lower::instructions::Value) {
        let addr = self.slot_addr();
        self.effect(
            trust_cg_lower::instructions::Opcode::Store {
                ty: trust_cg_lower::Type::I32,
                align: Some(4),
            },
            vec![value, addr],
        );
    }
}

/// `name(n)`: clang's unoptimized `ReverseBits32` ladder over a 4-byte slot
/// (three swap steps stored back, then a byte swap read four times), with
/// `tail` receiving the reversed value and ending the block. The slot is left
/// holding each byte of `n` bit-reversed in place.
fn reversebits32_slot_ladder(
    name: &str,
    tail: impl FnOnce(&mut SlotLadder, trust_cg_lower::instructions::Value),
) -> trust_cg_lower::Function {
    use trust_cg_lower::instructions::{Opcode, Value};
    let mut b = SlotLadder {
        instructions: Vec::new(),
        next: 1,
    };
    b.store_slot(Value(0));
    for (shift, mask) in [(1, 0x5555_5555), (2, 0x3333_3333), (4, 0x0f0f_0f0f)] {
        let shift = b.i32_const(shift);
        let mask = b.i32_const(mask);
        let right = b.load_slot();
        let right = b.op(Opcode::Ushr, vec![right, shift]);
        let right = b.op(Opcode::Band, vec![right, mask]);
        let left = b.load_slot();
        let left = b.op(Opcode::Band, vec![left, mask]);
        let left = b.op(Opcode::Ishl, vec![left, shift]);
        let combined = b.op(Opcode::Bor, vec![right, left]);
        b.store_slot(combined);
    }
    let mut root = None;
    for (mask, shift_left, shift) in [
        (0xff00_0000u32, false, 24),
        (0x00ff_0000, false, 8),
        (0x0000_ff00, true, 8),
        (0x0000_00ff, true, 24),
    ] {
        let loaded = b.load_slot();
        let mask = b.i32_const(i64::from(mask as i32));
        let masked = b.op(Opcode::Band, vec![loaded, mask]);
        let shift = b.i32_const(shift);
        let opcode = if shift_left {
            Opcode::Ishl
        } else {
            Opcode::Ushr
        };
        let term = b.op(opcode, vec![masked, shift]);
        root = Some(match root {
            None => term,
            Some(previous) => b.op(Opcode::Bor, vec![previous, term]),
        });
    }
    tail(&mut b, root.unwrap());

    let mut source = trust_cg_lower::Function::new(
        name,
        trust_cg_lower::function::Signature {
            params: vec![trust_cg_lower::Type::I32],
            returns: vec![trust_cg_lower::Type::I32],
        },
    );
    source.stack_slots = vec![trust_cg_lower::function::StackSlotInfo::new(4, 4)];
    source.block_order = vec![trust_cg_lower::instructions::Block(0)];
    source.blocks.insert(
        trust_cg_lower::instructions::Block(0),
        trust_cg_lower::function::BasicBlock {
            params: vec![],
            instructions: b.instructions,
            source_locs: vec![],
        },
    );
    source
}

/// A private slot's stores fold into RBIT, recorded as fusion edges that the
/// enforced raw gate accepts. With the slot's address escaping to a C callee
/// or the slot read again through another address, the selector keeps every
/// store and the callee and read-back see the stored state. Each variant runs
/// against a C reference at O0-O3.
#[test]
fn private_slot_bitreverse_folds_and_non_private_slots_keep_stores_at_all_tiers() {
    use trust_cg_lower::instructions::{DirectCallBinding, Opcode};
    let fused = reversebits32_slot_ladder("ReverseBits32", |b, root| {
        b.effect(Opcode::Return, vec![root]);
    });
    let escaped = reversebits32_slot_ladder("ReverseBits32Escaped", |b, root| {
        let addr = b.slot_addr();
        b.effect(
            Opcode::Call {
                name: "observe32".into(),
                binding: DirectCallBinding::Interposable,
            },
            vec![addr],
        );
        b.effect(Opcode::Return, vec![root]);
    });
    let read_back = reversebits32_slot_ladder("ReverseBits32ReadBack", |b, root| {
        let again = b.load_slot();
        let mixed = b.op(Opcode::Bxor, vec![root, again]);
        b.effect(Opcode::Return, vec![mixed]);
    });
    let reference = r#"
#include <stdint.h>
#include <stdio.h>
static uint32_t ref32(uint32_t x) {
    uint32_t r = 0;
    for (int i = 0; i < 32; i++) r |= ((x >> i) & 1u) << (31 - i);
    return r;
}
static uint32_t swapped_bytes32(uint32_t x) {
    uint32_t r = 0;
    for (int i = 0; i < 32; i++) r |= ((x >> i) & 1u) << ((i & ~7) + 7 - (i & 7));
    return r;
}
static volatile uint32_t observed;
void observe32(uint32_t *slot) { observed = *slot; }
int check(uint32_t x);
int main(void) {
    static const uint32_t edges[] = {0, 1, 0x80u, 0x80000000u, 0xffffffffu, 0x12345678u};
    for (unsigned i = 0; i < sizeof edges / sizeof edges[0]; i++)
        if (check(edges[i])) { printf("edge %u\n", i); return 1; }
    uint64_t state = 0x9e3779b97f4a7c15ull;
    for (int i = 0; i < 4096; i++) {
        state = state * 6364136223846793005ull + 1442695040888963407ull;
        if (check((uint32_t)(state >> 17))) { printf("input %d\n", i); return 2; }
    }
    return 0;
}
"#;
    let checks = [
        (
            &fused,
            "extern uint32_t ReverseBits32(uint32_t);\n\
             int check(uint32_t x) { return ReverseBits32(x) != ref32(x); }\n",
        ),
        (
            &escaped,
            "extern uint32_t ReverseBits32Escaped(uint32_t);\n\
             int check(uint32_t x) {\n\
                 observed = 0xdeadbeefu;\n\
                 return ReverseBits32Escaped(x) != ref32(x) || observed != swapped_bytes32(x);\n\
             }\n",
        ),
        (
            &read_back,
            "extern uint32_t ReverseBits32ReadBack(uint32_t);\n\
             int check(uint32_t x) {\n\
                 return ReverseBits32ReadBack(x) != (ref32(x) ^ swapped_bytes32(x));\n\
             }\n",
        ),
    ];
    let policy = [("TCG_DATAFLOW_INTEGRITY", "enforce")];
    for level in [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3] {
        for (source, check) in checks {
            let (prepared, _) = trust_cg_process_env::with_env_overrides(&policy, || {
                pipeline(level).prepare_function_with_metrics(source, None)
            })
            .unwrap_or_else(|error| panic!("{level:?} {}: {error}", source.name));
            let has_rbit = prepared.blocks.iter().any(|block| {
                block
                    .insts
                    .iter()
                    .any(|id| prepared.inst(*id).opcode == AArch64Opcode::Rbit)
            });
            let private = source.name == "ReverseBits32";
            assert_eq!(has_rbit, private, "{level:?} {}", source.name);
            let object = trust_cg_process_env::with_env_overrides(&policy, || {
                pipeline(level).compile_function(source)
            })
            .unwrap_or_else(|error| panic!("{level:?} {}: {error}", source.name));
            let driver = format!("{reference}{check}");
            let tag = format!("bitreverse_slot_{}_{level:?}", source.name);
            if native::link_run(&tag, &object, &driver).is_none() {
                return;
            }
        }
    }
}

#[path = "common/fresh_dir.rs"]
mod fresh_dir;

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes because it was silently refused.
fn permit_unlicensed() -> trust_cg_lower::CodegenLicensePolicy {
    trust_cg_lower::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit)
}
