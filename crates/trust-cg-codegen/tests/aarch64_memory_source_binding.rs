// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0
//! Source-bound memory rows on the code the proof-grade AArch64 pipeline
//! actually emits (ledger L07-P2, X-OPCODES-P1).
//!
//! Small trust-ir load/store leaves are lowered and prepared on the host's own
//! triple at O0 to O3, exactly as the verifying JIT prepares them (frameless:
//! the zero-storage audit omits the envelope around a load/store body). The
//! memory-leaf checker must bind every access of every such body to its LIR
//! access, and must bind nothing once an access is corrupted (wrong slot,
//! wrong source operand, swapped width, wrong stored value). Through the
//! verifier's walk a bound access is credited only by the source-bound route
//! (every memory-effect part with a Clean-checked certificate); this file
//! checks that it is never failed on correct code and never credited without
//! that route's proof name, whichever proof tools this host resolves. The
//! Formal-only rule's form certificates are disabled in that walk so the rows
//! reach the source-bound route on every host. The verifying JIT then
//! publishes (and this file runs natively) a load/store leaf only when every
//! bound access is credited, and otherwise refuses it naming those rows.
#![cfg(all(target_arch = "aarch64", feature = "verify"))]

use trust_cg_codegen::pipeline::{OptLevel, Pipeline, PipelineConfig};
use trust_cg_ir::{AArch64Opcode as M, MachFunction, MachOperand};
use trust_cg_verify::aarch64_memory_source_binding::{
    SOURCE_BOUND_MEMORY_NOT_CREDITED, SOURCE_BOUND_MEMORY_PROOF_PREFIX,
};
use trust_cg_verify::function_verifier::InstructionVerificationResult;
use trust_cg_verify::provenance_xcheck::ProvenanceXCheckMode;
use trust_cg_verify::source_bound_frame::{MemoryLeafRefusal, source_bound_memory_leaf};
use trust_cg_verify::{FunctionVerifier, VerificationConfig};
use trust_ir::Ty;
use trust_ir_build::ModuleBuilder;

const LEVELS: [OptLevel; 4] = [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3];

/// `(name, accesses)`: each leaf and how many memory accesses its source makes.
const SHAPES: [(&str, usize); 10] = [
    ("load64", 1),
    ("load32", 1),
    ("load16", 1),
    ("load8", 1),
    ("load64_offset", 1),
    ("chase", 2),
    ("store64", 1),
    ("store8", 1),
    ("copy64", 2),
    ("swap64", 4),
];

fn module(shape: &str) -> trust_ir::Module {
    let mut builder = ModuleBuilder::new("memory_leaf");
    let (params, returns) = match shape {
        "load64" | "load64_offset" | "chase" => (vec![Ty::Ptr], vec![Ty::U64]),
        "load32" => (vec![Ty::Ptr], vec![Ty::U32]),
        "load16" => (vec![Ty::Ptr], vec![Ty::U16]),
        "load8" => (vec![Ty::Ptr], vec![Ty::U8]),
        "store64" => (vec![Ty::Ptr, Ty::U64], vec![]),
        "store8" => (vec![Ty::Ptr, Ty::U8], vec![]),
        "copy64" | "swap64" => (vec![Ty::Ptr, Ty::Ptr], vec![]),
        _ => unreachable!("closed shape set"),
    };
    let signature = builder.add_func_type(params.clone(), returns);
    let mut f = builder.function("leaf", signature);
    let entry = f.create_block();
    let args: Vec<_> = params
        .iter()
        .map(|ty| f.add_block_param(entry, ty.clone()))
        .collect();
    f.switch_to_block(entry);
    match shape {
        "load64" | "load32" | "load16" | "load8" => {
            let ty = match shape {
                "load64" => Ty::U64,
                "load32" => Ty::U32,
                "load16" => Ty::U16,
                _ => Ty::U8,
            };
            let v = f.load(ty, args[0]);
            f.ret(vec![v]);
        }
        "load64_offset" => {
            let p = f.gep_byte_offset(args[0], 16);
            let v = f.load(Ty::U64, p);
            f.ret(vec![v]);
        }
        "chase" => {
            let p = f.load(Ty::Ptr, args[0]);
            let q = f.gep_byte_offset(p, 8);
            let v = f.load(Ty::U64, q);
            f.ret(vec![v]);
        }
        "store64" => {
            f.store(Ty::U64, args[0], args[1]);
            f.ret(vec![]);
        }
        "store8" => {
            f.store(Ty::U8, args[0], args[1]);
            f.ret(vec![]);
        }
        "copy64" => {
            let v = f.load(Ty::U64, args[1]);
            f.store(Ty::U64, args[0], v);
            f.ret(vec![]);
        }
        "swap64" => {
            let a = f.load(Ty::U64, args[0]);
            let b = f.load(Ty::U64, args[1]);
            f.store(Ty::U64, args[0], b);
            f.store(Ty::U64, args[1], a);
            f.ret(vec![]);
        }
        _ => unreachable!("closed shape set"),
    }
    f.build();
    builder.build().expect("ModuleBuilder::build: test fixture")
}

/// The LIR and the prepared machine function of `shape` at `level`.
fn prepared(shape: &str, level: OptLevel) -> (trust_cg_lower::Function, MachFunction) {
    let source = module(shape);
    let (lir, _) = trust_cg_lower::translate_function_with_license(
        &source.functions[0],
        &source,
        &permit_unlicensed(),
    )
    .unwrap();
    let pipeline = Pipeline::new(PipelineConfig {
        opt_level: level,
        verify: false,
        ..PipelineConfig::for_host_aarch64()
    })
    .with_proof_grade_aarch64_publication();
    let machine = pipeline.prepare_function(&lir).unwrap();
    (lir, machine)
}

fn is_memory(opcode: M) -> bool {
    matches!(
        opcode,
        M::LdrRI | M::LdrbRI | M::LdrhRI | M::StrRI | M::StrbRI | M::StrhRI
    )
}

fn memory_instructions(machine: &MachFunction) -> Vec<usize> {
    machine
        .blocks
        .iter()
        .flat_map(|block| &block.insts)
        .map(|id| id.0 as usize)
        .filter(|index| is_memory(machine.insts[*index].opcode))
        .collect()
}

#[test]
fn every_access_of_every_pipeline_leaf_is_bound_to_its_source_access() {
    let mut bound = 0;
    for (shape, accesses) in SHAPES {
        for level in LEVELS {
            let (lir, machine) = prepared(shape, level);
            let leaf = source_bound_memory_leaf(&lir, &machine)
                .unwrap_or_else(|refusal| panic!("{shape} {level:?}: {refusal}: {machine:?}"));
            assert_eq!(leaf.accesses().len(), accesses, "{shape} {level:?}");
            let instructions: Vec<usize> = leaf
                .accesses()
                .iter()
                .map(|access| access.instruction.0 as usize)
                .collect();
            assert_eq!(
                instructions,
                memory_instructions(&machine),
                "{shape} {level:?}: every emitted access, in order"
            );
            bound += accesses;
        }
    }
    assert_eq!(bound, 4 * 15, "15 accesses at each of four levels");
}

/// Corrupting one access of a real pipeline body (its slot, its base, its
/// width or its stored register) withholds the whole binding, by name.
#[test]
fn a_corrupted_pipeline_access_binds_nothing() {
    for level in LEVELS {
        // Wrong slot: chase's second load.
        let (lir, mut machine) = prepared("chase", level);
        let second = memory_instructions(&machine)[1];
        let offset = machine.insts[second]
            .operands
            .iter_mut()
            .rev()
            .find_map(|operand| match operand {
                MachOperand::Imm(value) => Some(value),
                _ => None,
            });
        match offset {
            // `ldr x0, [x1, #8]`: read `#16` instead.
            Some(value) => *value += 8,
            // O0/O1 materialize the address: read `[base, #8]` past it.
            None => machine.insts[second].operands.push(MachOperand::Imm(8)),
        }
        assert!(
            matches!(
                source_bound_memory_leaf(&lir, &machine),
                Err(MemoryLeafRefusal::Trace { position: 1, .. })
            ),
            "chase {level:?}"
        );
        // Wrong source operand: swap's first load through the second pointer.
        let (lir, mut machine) = prepared("swap64", level);
        let first = memory_instructions(&machine)[0];
        let other = machine.insts[memory_instructions(&machine)[1]].operands[1].clone();
        machine.insts[first].operands[1] = other;
        assert!(
            matches!(
                source_bound_memory_leaf(&lir, &machine),
                Err(MemoryLeafRefusal::Trace { position: 0, .. })
            ),
            "swap64 {level:?}"
        );
        // Swapped width: the 8-byte store as a byte store.
        let (lir, mut machine) = prepared("store64", level);
        let store = memory_instructions(&machine)[0];
        machine.insts[store].opcode = M::StrbRI;
        machine.insts[store].operands[0] = MachOperand::PReg(trust_cg_ir::regs::PReg::new(33));
        assert!(
            matches!(
                source_bound_memory_leaf(&lir, &machine),
                Err(MemoryLeafRefusal::Trace { position: 0, .. })
            ),
            "store64 {level:?}"
        );
        // Wrong stored register: copy stores the pointer, not the value.
        let (lir, mut machine) = prepared("copy64", level);
        let store = memory_instructions(&machine)[1];
        machine.insts[store].operands[0] = machine.insts[store].operands[1].clone();
        assert!(
            matches!(
                source_bound_memory_leaf(&lir, &machine),
                Err(MemoryLeafRefusal::Trace { position: 1, .. })
            ),
            "copy64 {level:?}"
        );
    }
}

/// Through the walk, a bound access of a real body is never failed on
/// correct code, and is `Verified` only under the source-bound route's proof
/// name; otherwise it names the source binding and how far its parts got.
/// Which of the two depends on the proof tools this host resolves, so the
/// counts are pinned for the measured pairs ([`measured_part_certification`]:
/// the installed Trust package 9192 certifies no part, so all 30 are refused;
/// the overlay of AY `2657db47c` and Clean `ed21fee39` certifies every part,
/// so all 30 are credited) and only an unmeasured pair may give either. A
/// function is promotable only if every bound access is credited.
#[test]
fn bound_pipeline_accesses_are_credited_only_with_every_part_checked() {
    trust_cg_verify::env_lock::with_env_overrides(&[("TCG_CANARY_NO_CACHE", "1")], || {
        let verifier = FunctionVerifier::with_config(VerificationConfig::for_proof_promotion());
        let request = verifier.capture_request_with_mode(ProvenanceXCheckMode::Enforce);
        let (mut credited, mut refused) = (0, 0);
        for (shape, _) in SHAPES {
            for level in [OptLevel::O0, OptLevel::O3] {
                let (lir, machine) = prepared(shape, level);
                let captured = verifier.verify_with_request(&machine, Some(&lir), &request);
                let report = captured.report();
                assert!(report.precondition_failure.is_none(), "{shape} {level:?}");
                let mut all_credited = true;
                for row in &report.instructions {
                    if !is_memory(machine.insts[row.inst_index].opcode) {
                        continue;
                    }
                    match &row.result {
                        InstructionVerificationResult::Verified { proof_name, .. } => {
                            assert!(
                                proof_name.starts_with(SOURCE_BOUND_MEMORY_PROOF_PREFIX),
                                "{shape} {level:?}: credited by another route: {proof_name}"
                            );
                            credited += 1;
                        }
                        InstructionVerificationResult::Unverified { reason } => {
                            assert!(
                                reason.contains(SOURCE_BOUND_MEMORY_NOT_CREDITED)
                                    && reason.contains("parts have a Clean-checked certificate"),
                                "{shape} {level:?}: {reason}"
                            );
                            all_credited = false;
                            refused += 1;
                        }
                        other => panic!("{shape} {level:?}: {other:?}"),
                    }
                }
                if !all_credited {
                    assert!(
                        !report.emitted_opcode_inventory().is_promotable(),
                        "{shape} {level:?}"
                    );
                }
            }
        }
        eprintln!(
            "SOURCE_BOUND_MEMORY_PIPELINE credited={credited} refused={refused} tools={}",
            proof_tools()
        );
        assert_eq!(credited + refused, 2 * 15);
        match measured_part_certification() {
            Some(true) => assert_eq!(credited, 2 * 15, "{}", proof_tools()),
            Some(false) => assert_eq!(
                credited,
                0,
                "credit without a certificate: {}",
                proof_tools()
            ),
            None => {}
        }
    });
}

/// The verifying JIT publishes a load/store leaf whose only other row is its
/// return exactly when every bound access is credited by the source-bound
/// route, and then runs it natively against host memory; otherwise it
/// refuses it, naming only the memory rows and their source-bound clause.
/// Which happens depends on the resolved proof tools, as above (all 8
/// refused with package 9192, all 8 published with the overlay); the
/// Formal-only rule's form certificates are disabled so the source-bound
/// route is the only one that can credit the rows.
#[test]
fn the_verifying_jit_publishes_a_bound_leaf_only_with_every_access_credited() {
    use std::collections::HashMap;
    use trust_cg_codegen::compiler::{CompileError, Compiler, CompilerConfig};
    use trust_cg_codegen::target::Target;
    trust_cg_verify::env_lock::with_env_overrides(&[("TCG_CANARY_NO_CACHE", "1")], || {
        let (mut published, mut refused) = (0, 0);
        for shape in ["chase", "store64", "copy64", "swap64"] {
            // O2 and O3 leave no register copy or address ADD in these
            // leaves (O0 and O1 keep some), so their only other row is RET.
            for level in [OptLevel::O2, OptLevel::O3] {
                let compiler = Compiler::new(CompilerConfig {
                    opt_level: level,
                    emit_proofs: true,
                    parallel: false,
                    ..CompilerConfig::jit_fast(Target::Aarch64)
                })
                .with_codegen_license(permit_unlicensed());
                let result = match compiler.compile_module_to_jit(&module(shape), &HashMap::new()) {
                    Ok(result) => result,
                    Err(CompileError::ProofPromotionRejected {
                        target: Target::Aarch64,
                        reason,
                    }) => {
                        let uncovered = reason
                            .split_once(" distinct opcode(s) [")
                            .and_then(|(_, rest)| rest.split_once(']'))
                            .map(|(opcodes, _)| opcodes.to_owned())
                            .unwrap_or_default();
                        assert!(
                            !uncovered.is_empty()
                                && uncovered.split(", ").all(|opcode| {
                                    matches!(opcode, "AArch64::LdrRI" | "AArch64::StrRI")
                                })
                                && reason.contains(SOURCE_BOUND_MEMORY_NOT_CREDITED),
                            "{shape} {level:?}: refused for another reason: {reason}"
                        );
                        refused += 1;
                        continue;
                    }
                    Err(other) => panic!("{shape} {level:?}: {other}"),
                };
                let certificate = result.buffer.certificate("leaf").expect("a certificate");
                assert!(certificate.is_verified(), "{shape} {level:?}");
                let memory_rows = certificate
                    .chain()
                    .certificates
                    .iter()
                    .filter(|row| {
                        row.obligation_name
                            .starts_with(SOURCE_BOUND_MEMORY_PROOF_PREFIX)
                    })
                    .count();
                assert_eq!(
                    memory_rows,
                    SHAPES.iter().find(|(name, _)| *name == shape).unwrap().1,
                    "{shape} {level:?}: every access is a source-bound row"
                );
                let buffer = &result.buffer;
                // SAFETY: each arm uses the leaf's exact C ABI, the verifying
                // JIT published it, `buffer` is live, and every pointer
                // names live, aligned host memory of the accessed width.
                unsafe {
                    match shape {
                        "chase" => {
                            let inner = [11u64, 42u64];
                            let outer: *const u64 = inner.as_ptr();
                            let f = buffer
                                .get_fn_bound::<extern "C" fn(*const *const u64) -> u64>("leaf")
                                .unwrap();
                            assert_eq!(f.as_ref()(&outer), 42);
                        }
                        "store64" => {
                            let mut cell = 0u64;
                            let f = buffer
                                .get_fn_bound::<extern "C" fn(*mut u64, u64)>("leaf")
                                .unwrap();
                            f.as_ref()(&mut cell, 0xfeed_beef_0bad_f00d);
                            assert_eq!(cell, 0xfeed_beef_0bad_f00d);
                        }
                        "copy64" => {
                            let (mut dst, src) = (0u64, u64::MAX - 7);
                            let f = buffer
                                .get_fn_bound::<extern "C" fn(*mut u64, *const u64)>("leaf")
                                .unwrap();
                            f.as_ref()(&mut dst, &src);
                            assert_eq!(dst, u64::MAX - 7);
                        }
                        _ => {
                            let (mut a, mut b) = (1u64 << 63, 5u64);
                            let f = buffer
                                .get_fn_bound::<extern "C" fn(*mut u64, *mut u64)>("leaf")
                                .unwrap();
                            f.as_ref()(&mut a, &mut b);
                            assert_eq!((a, b), (5, 1 << 63));
                        }
                    }
                }
                published += 1;
            }
        }
        eprintln!(
            "SOURCE_BOUND_MEMORY_JIT published={published} refused={refused} tools={}",
            proof_tools()
        );
        assert_eq!(published + refused, 8);
        match measured_part_certification() {
            Some(true) => assert_eq!(published, 8, "{}", proof_tools()),
            Some(false) => assert_eq!(
                published,
                0,
                "published without a certificate: {}",
                proof_tools()
            ),
            None => {}
        }
    });
}

/// What the resolved tools do with these leaves' memory-effect parts, for the
/// pairs this host measured (`reports/2026-10-01-darwin-memory-source-binding`):
/// `Some(false)` for the installed Trust package 9192's AY (SHA-256
/// `40e852cc…`), which answers holey `unsat` or `unknown` for every part
/// whatever Clean it is paired with; `Some(true)` for the overlay of AY
/// `2657db47c` (`b37fa549…`) and Clean `ed21fee39` (`ad10bed6…`), which
/// certifies every part; `None` for any other or unresolved pair.
fn measured_part_certification() -> Option<bool> {
    const PACKAGE_9192_AY: &str =
        "40e852cc7fa3a3289f17a47b5a8d6d1a5218177b4a95087538ff2c3d702ac7a8";
    const OVERLAY_AY: &str = "b37fa549fa0712cc6283f0675d029f2a802641d1c61c0a6a329ed69faae3a9a8";
    const OVERLAY_CLEAN: &str = "ad10bed671a8bf8110b3abefd4f72d6b13380ddba308aa1c58181867a03fac96";
    let ay = trust_cg_verify::ay_identity::resolve_for_process().ok()?;
    if ay.sha256() == PACKAGE_9192_AY {
        return Some(false);
    }
    let (_, clean) = trust_cg_verify::obligation_cert_store::resolve_proof_checker().ok()?;
    (ay.sha256() == OVERLAY_AY && clean == OVERLAY_CLEAN).then_some(true)
}

fn proof_tools() -> String {
    let ay = match trust_cg_verify::ay_identity::resolve_for_process() {
        Ok(ay) => format!("AY {}", ay.describe()),
        Err(refusal) => format!("no AY admitted ({refusal})"),
    };
    let clean = match trust_cg_verify::obligation_cert_store::resolve_proof_checker() {
        Ok((path, sha256)) => format!("Clean {} sha256 {sha256}", path.display()),
        Err(reason) => format!("no Clean checker resolves ({reason})"),
    };
    format!("{ay}; {clean}")
}

/// This file's fixtures are built with `ModuleBuilder` and carry no codegen
/// license (`body_gate: None`), which trust-cg REFUSES by default (roadmap
/// WS7.5, decision gate DG-73). Its compiles state `Permit` explicitly, so
/// none of them passes (or is refused) because the license silently refused
/// it.
fn permit_unlicensed() -> trust_cg_codegen::CodegenLicensePolicy {
    trust_cg_codegen::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_codegen::UnlicensedBodyPolicy::Permit)
}
