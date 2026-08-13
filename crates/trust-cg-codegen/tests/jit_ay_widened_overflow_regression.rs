// trust-cg-codegen/tests/jit_ay_widened_overflow_regression.rs
//
// End-to-end AArch64 runtime regression for the i128-widened signed-overflow
// compare/branch idiom consumed by ay's checked-batch JIT lowering path.

#![cfg(target_arch = "aarch64")]

#[path = "common/fixture_contract.rs"]
mod fixture_contract;
use fixture_contract::FixtureContractLookup;

use std::collections::HashMap;

use trust_cg_codegen::Target;
use trust_cg_codegen::jit::{JitCompiler, JitConfig};
use trust_cg_codegen::jit_contract::{
    AbiDescriptor, AbiValue, AbiValueKind, ArtifactContractError, ArtifactSection,
    ArtifactSectionKind, ArtifactSymbol, DeterministicArtifactManifest, Endianness,
    InvalidationKey, JitArtifactKind, LayoutManifest, ProofPolicy, SymbolLayout,
    SymbolLookupContract, SymbolSignature, SymbolVisibility, TargetDescriptor,
    TargetOperatingSystem,
};
use trust_cg_codegen::pipeline::{OptLevel, Pipeline, PipelineConfig};
use trust_cg_ir::inst::AArch64Opcode;
use trust_cg_ir::operand::MachOperand;
use trust_cg_lower::function::{BasicBlock, Function, Signature};
use trust_cg_lower::instructions::{Block, Instruction, IntCC, Opcode, Value};
use trust_cg_lower::types::Type;

const CHECKED_BATCH_ADD_SYMBOL: &str = "ay_checked_batch_widened_add";

type CheckedBatchAddFn = unsafe extern "C" fn(i64, i64) -> i64;

fn inst(opcode: Opcode, args: Vec<Value>, results: Vec<Value>) -> Instruction {
    Instruction {
        opcode,
        args,
        results,
    }
}

fn build_ay_checked_batch_widened_add() -> Function {
    let entry = Block(0);
    let overflow = Block(1);
    let ok = Block(2);

    let mut func = Function::new(
        "ay_checked_batch_widened_add",
        Signature {
            params: vec![Type::I64, Type::I64],
            returns: vec![Type::I64],
        },
    );
    func.entry_block = entry;
    func.block_order = vec![entry, overflow, ok];

    // This is the ay checked-batch consumer shape:
    //   sum       = add i64 a, b
    //   true_sum  = add i128 (sext a), (sext b)
    //   overflow  = (sext sum) != true_sum
    //   br overflow, overflow_exit, success
    //
    // Issue #430 teaches AArch64 ISel to collapse this into ADDS + B.VS.
    let entry_block = BasicBlock {
        params: vec![],
        instructions: vec![
            inst(Opcode::Iadd, vec![Value(0), Value(1)], vec![Value(2)]),
            inst(
                Opcode::Sextend {
                    from_ty: Type::I64,
                    to_ty: Type::I128,
                },
                vec![Value(0)],
                vec![Value(3)],
            ),
            inst(
                Opcode::Sextend {
                    from_ty: Type::I64,
                    to_ty: Type::I128,
                },
                vec![Value(1)],
                vec![Value(4)],
            ),
            inst(Opcode::Iadd, vec![Value(3), Value(4)], vec![Value(5)]),
            inst(
                Opcode::Sextend {
                    from_ty: Type::I64,
                    to_ty: Type::I128,
                },
                vec![Value(2)],
                vec![Value(6)],
            ),
            inst(
                Opcode::Icmp {
                    cond: IntCC::NotEqual,
                },
                vec![Value(6), Value(5)],
                vec![Value(7)],
            ),
            inst(
                Opcode::Brif {
                    cond: Value(7),
                    then_dest: overflow,
                    else_dest: ok,
                },
                vec![Value(7)],
                vec![],
            ),
        ],
        source_locs: vec![],
    };

    let overflow_block = BasicBlock {
        params: vec![],
        instructions: vec![
            inst(
                Opcode::Iconst {
                    ty: Type::I64,
                    imm: -12345,
                },
                vec![],
                vec![Value(8)],
            ),
            inst(Opcode::Return, vec![Value(8)], vec![]),
        ],
        source_locs: vec![],
    };

    let ok_block = BasicBlock {
        params: vec![],
        instructions: vec![inst(Opcode::Return, vec![Value(2)], vec![])],
        source_locs: vec![],
    };

    func.blocks.insert(entry, entry_block);
    func.blocks.insert(overflow, overflow_block);
    func.blocks.insert(ok, ok_block);
    func
}

fn prepare_o2_ay_checked_batch_add() -> trust_cg_ir::function::MachFunction {
    let config = PipelineConfig {
        opt_level: OptLevel::O2,
        ..PipelineConfig::default()
    };
    let pipeline = Pipeline::new(config);
    pipeline
        .prepare_function(&build_ay_checked_batch_widened_add())
        .expect("O2 pipeline should prepare widened overflow regression")
}

fn i64_abi_value() -> AbiValue {
    AbiValue::new(AbiValueKind::I64)
}

fn ay_checked_batch_signature() -> SymbolSignature {
    SymbolSignature::extern_c(
        vec![i64_abi_value(), i64_abi_value()],
        vec![i64_abi_value()],
    )
}

fn target_os_descriptor() -> TargetOperatingSystem {
    if cfg!(target_os = "macos") {
        TargetOperatingSystem::Macos
    } else if cfg!(target_os = "linux") {
        TargetOperatingSystem::Linux
    } else {
        TargetOperatingSystem::Unknown
    }
}

fn ay_checked_batch_target() -> TargetDescriptor {
    TargetDescriptor::for_trust_cg_target(Target::Aarch64, target_os_descriptor())
        .with_cpu("aarch64-ay-test")
        .with_features(["fp", "simd"])
}

fn ay_checked_batch_abi() -> AbiDescriptor {
    let mut abi = AbiDescriptor::for_trust_cg_target(Target::Aarch64);
    abi.name = "ay-checked-batch-aapcs64-lp64".to_owned();
    abi
}

fn ay_checked_batch_layout() -> LayoutManifest {
    let mut layout = LayoutManifest::lp64(Endianness::Little, 16);
    layout.wrapper_identity = Some("ay::checked_batch::widened_overflow:v1".to_owned());
    layout.symbols.push(SymbolLayout {
        name: CHECKED_BATCH_ADD_SYMBOL.to_owned(),
        section: ".text".to_owned(),
        offset_bytes: Some(0),
        size_bytes: 128,
        alignment_bytes: 16,
    });
    layout.metadata.insert(
        "kernel".to_owned(),
        "ay_checked_batch_widened_overflow".to_owned(),
    );
    layout
}

fn ay_checked_batch_invalidation(
    target: &TargetDescriptor,
    abi: &AbiDescriptor,
    layout: &LayoutManifest,
    proof_policy: &ProofPolicy,
) -> InvalidationKey {
    InvalidationKey::new(
        "ay:checked-batch:widened-overflow:v1",
        "trust-cg:phase7:widened-overflow:o2",
        target.checksum(),
        abi.checksum(),
        layout.checksum(),
        proof_policy.checksum(),
        686,
    )
}

fn ay_checked_batch_manifest() -> DeterministicArtifactManifest {
    let target = ay_checked_batch_target();
    let abi = ay_checked_batch_abi();
    let layout = ay_checked_batch_layout();
    let proof_policy = ProofPolicy::disabled();
    let invalidation = ay_checked_batch_invalidation(&target, &abi, &layout, &proof_policy);
    let mut manifest = DeterministicArtifactManifest::new(
        "ay-checked-batch-widened-overflow-probe",
        JitArtifactKind::ExecutableMemory,
        target,
        abi,
        layout,
        invalidation,
        proof_policy,
    );
    manifest.symbols.push(ArtifactSymbol {
        name: CHECKED_BATCH_ADD_SYMBOL.to_owned(),
        visibility: SymbolVisibility::Exported,
        signature: ay_checked_batch_signature(),
        offset_bytes: Some(0),
        checksum: None,
    });
    manifest.sections.push(ArtifactSection {
        name: ".text".to_owned(),
        kind: ArtifactSectionKind::Text,
        size_bytes: 128,
        alignment_bytes: 16,
        checksum: None,
    });
    manifest
        .metadata
        .insert("consumer".to_owned(), "ay".to_owned());
    manifest.metadata.insert(
        "promotion_disposition".to_owned(),
        "manifest_backed_test_probe".to_owned(),
    );
    manifest
}

fn ay_checked_batch_lookup_contract(
    manifest: &DeterministicArtifactManifest,
) -> SymbolLookupContract {
    SymbolLookupContract::new(
        CHECKED_BATCH_ADD_SYMBOL,
        ay_checked_batch_signature(),
        manifest.target.checksum(),
        manifest.abi.checksum(),
        manifest.layout.checksum(),
    )
    .with_invalidation_checksum(manifest.invalidation.checksum())
    .with_manifest_checksum(manifest.checksum())
}

fn all_opcodes(func: &trust_cg_ir::function::MachFunction) -> Vec<AArch64Opcode> {
    func.blocks
        .iter()
        .flat_map(|block| block.insts.iter())
        .map(|id| func.insts[id.0 as usize].opcode)
        .collect()
}

#[test]
fn ay_checked_batch_widened_overflow_contract_rejects_layout_drift() {
    let manifest = ay_checked_batch_manifest();
    let contract = ay_checked_batch_lookup_contract(&manifest);
    let mut drifted = manifest.clone();
    drifted.layout.stack_alignment_bytes = 32;

    let result = drifted.validate_symbol_lookup(&contract);
    assert!(
        matches!(
            result,
            Err(ArtifactContractError::ChecksumMismatch {
                ref component,
                ..
            }) if component == "artifact_manifest"
        ),
        "layout drift must reject the widened-overflow typed lookup contract; result={result:?}"
    );
}

#[test]
fn ay_checked_batch_widened_overflow_o2_uses_adds_bvs() {
    let func = prepare_o2_ay_checked_batch_add();
    let opcodes = all_opcodes(&func);

    assert!(
        opcodes.contains(&AArch64Opcode::AddsRR),
        "O2 ay checked-batch widened overflow idiom must emit flag-setting ADDS; opcodes={opcodes:?}"
    );
    assert!(
        !opcodes.contains(&AArch64Opcode::Adc),
        "widened overflow fast path must not fall back to full i128 ADD+ADC lowering; opcodes={opcodes:?}"
    );
    assert!(
        !opcodes.contains(&AArch64Opcode::CSet),
        "branch-only overflow consumer should use B.VS directly, not materialize CSET; opcodes={opcodes:?}"
    );

    let has_bvs = func.insts.iter().any(|inst| {
        inst.opcode == AArch64Opcode::BCond
            && matches!(inst.operands.first(), Some(MachOperand::Imm(6)))
    });
    assert!(
        has_bvs,
        "O2 ay checked-batch widened overflow idiom must branch on VS; insts={:#?}",
        func.insts
    );
}

#[test]
fn ay_checked_batch_widened_overflow_o2_runtime_cases() {
    let func = prepare_o2_ay_checked_batch_add();
    let jit = JitCompiler::new(JitConfig {
        opt_level: OptLevel::O2,
        ..JitConfig::default()
    });
    let buffer = jit
        .compile_raw(&[func], &HashMap::new())
        .expect("O2 JIT compile should succeed for ay checked-batch widened overflow");
    let manifest = ay_checked_batch_manifest();
    let contract = ay_checked_batch_lookup_contract(&manifest);
    let checked_add = unsafe {
        buffer
            .get_fixture_contract_symbol_bound::<CheckedBatchAddFn>(&manifest, &contract)
            .expect("ay checked-batch widened overflow symbol satisfies artifact contract")
            .into_fn()
    };

    let no_overflow = unsafe { checked_add(40, 2) };
    assert_eq!(no_overflow, 42, "non-overflow path should return the sum");

    let positive_overflow = unsafe { checked_add(i64::MAX, 1) };
    assert_eq!(
        positive_overflow, -12345,
        "positive signed overflow should branch to the checked-batch overflow sentinel"
    );

    let negative_overflow = unsafe { checked_add(i64::MIN, -1) };
    assert_eq!(
        negative_overflow, -12345,
        "negative signed overflow should branch to the checked-batch overflow sentinel"
    );
}
