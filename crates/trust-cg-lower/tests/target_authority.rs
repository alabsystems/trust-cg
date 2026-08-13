// Production authority regressions for heterogeneous target selection.

use trust_cg_lower::adapter::{Proof, ProofContext};
use trust_cg_lower::instructions::Value;
use trust_cg_lower::target_analysis::{
    ComputeTarget, ProofAnalyzer, SubgraphDescriptor, SubgraphId, SubgraphProof, TargetProofContext,
};
use trust_cg_lower::types::Type;
use trust_ir::ValueId;

#[test]
fn forged_proof_labels_cannot_authorize_gpu_ane_or_parallel_reduction() {
    let id = SubgraphId(7);
    let base = Value(0);
    let index = Value(1);
    let mut subgraph = SubgraphDescriptor::new(id);
    subgraph.values = vec![base, index];
    subgraph
        .value_types
        .insert(base, Type::Array(Box::new(Type::F64), 4096));
    subgraph.value_types.insert(index, Type::I64);
    subgraph.data_size_bytes = 32 * 1024;
    subgraph.subgraph_proofs.extend([
        SubgraphProof::Pure,
        SubgraphProof::Associative,
        SubgraphProof::Commutative,
        SubgraphProof::Deterministic,
    ]);

    let mut proof_ctx = ProofContext::default();
    proof_ctx.value_proofs.insert(
        index,
        vec![
            Proof::InBounds {
                base: ValueId::new(0),
                index: ValueId::new(1),
            },
            Proof::ValidBorrow {
                borrow: ValueId::new(0),
            },
        ],
    );
    let mut target_ctx = TargetProofContext::new(proof_ctx);
    target_ctx.add_subgraph_proof(id, SubgraphProof::Pure);
    target_ctx.add_subgraph_proof(id, SubgraphProof::Associative);
    target_ctx.add_subgraph_proof(id, SubgraphProof::Commutative);

    let legality = ProofAnalyzer::with_defaults().analyze(&subgraph, &target_ctx);
    assert!(legality.is_legal(ComputeTarget::CpuScalar));
    assert!(!legality.is_legal(ComputeTarget::Gpu));
    assert!(!legality.is_legal(ComputeTarget::NeuralEngine));
    assert!(!legality.parallel_reduction_legal);
    assert!(
        legality
            .reason(ComputeTarget::Gpu)
            .is_some_and(|reason| reason.contains("exact validator-issued target replay"))
    );

    // Labels remain available for reports and future exact replay; only their authority is removed.
    assert!(subgraph.has_proof(SubgraphProof::Pure));
    assert!(target_ctx.proof_ctx.has_in_bounds(&index));
    assert!(target_ctx.proof_ctx.has_valid_borrow(&index));
}
