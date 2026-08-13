// Regression for a TY native BFS parent loop with no enabled action body.
//
// The loop still has live parent-loop state carried as block arguments and
// records the status fields that downstream O1/O3 gates compare.

#![cfg(target_arch = "aarch64")]

use std::collections::HashMap;

use trust_cg_codegen::pipeline::{OptLevel, ProofOptimizationCertificateCitation};
use trust_cg_codegen::{Compiler, CompilerConfig, ExecutableBuffer, Target};
use trust_ir::{BinOp, FieldDef, ICmpOp, ProofAnnotation, StructDef, Ty, ValueId};
use trust_ir_build::{FunctionBuilder, ModuleBuilder};

#[path = "common/ty_contract.rs"]
mod ty_contract;

use ty_contract::{abi_i64, abi_ptr, bind_ty_reducer_entry, extern_c_signature};

const ENTRY_NAME: &str = "ty_native_bfs_no_action_parent_loop";
const FINGERPRINT_SEED: u64 = 7;
const FINGERPRINT_PRIME: u64 = 131;

type EntryFn = extern "C" fn(*const u64, u64, *mut u64) -> u64;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct BfsSummary {
    state_count: u64,
    generated: u64,
    last_parent: u64,
    fingerprint: u64,
    status: u64,
}

impl BfsSummary {
    fn from_slots(slots: [u64; 5]) -> Self {
        Self {
            state_count: slots[0],
            generated: slots[1],
            last_parent: slots[2],
            fingerprint: slots[3],
            status: slots[4],
        }
    }
}

fn store_summary_slot(fb: &mut FunctionBuilder<'_>, out: ValueId, slot: u64, value: ValueId) {
    let slot = fb.iconst(Ty::U64, i128::from(slot));
    let ptr = fb.gep(Ty::U64, out, vec![slot]);
    fb.store(Ty::U64, ptr, value);
}

fn build_no_action_parent_loop_module() -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("ty_native_bfs_no_action_parent_loop");
    let summary_pair = mb.add_struct(StructDef {
        id: trust_ir::StructId::new(0),
        name: "TyBfsSummaryPair".to_owned(),
        fields: vec![
            FieldDef {
                name: "state_count".to_owned(),
                ty: Ty::U64,
                offset: None,
            },
            FieldDef {
                name: "generated".to_owned(),
                ty: Ty::U64,
                offset: None,
            },
        ],
        size: None,
        align: Some(16),
        repr: Default::default(),
    });
    let entry_ty = mb.add_func_type(vec![Ty::Ptr, Ty::U64, Ty::Ptr], vec![Ty::U64]);

    {
        let mut fb = mb.function(ENTRY_NAME, entry_ty);

        let entry = fb.create_block();
        let parents = fb.add_block_param(entry, Ty::Ptr);
        let parent_count = fb.add_block_param(entry, Ty::U64);
        let out = fb.add_block_param(entry, Ty::Ptr);

        let header = fb.create_block();
        let idx = fb.add_block_param(header, Ty::U64);
        let state_count = fb.add_block_param(header, Ty::U64);
        let generated = fb.add_block_param(header, Ty::U64);
        let last_parent = fb.add_block_param(header, Ty::U64);
        let fingerprint = fb.add_block_param(header, Ty::U64);
        let status = fb.add_block_param(header, Ty::U64);

        let body = fb.create_block();
        let done = fb.create_block();
        let done_state_count = fb.add_block_param(done, Ty::U64);
        let done_generated = fb.add_block_param(done, Ty::U64);
        let done_last_parent = fb.add_block_param(done, Ty::U64);
        let done_fingerprint = fb.add_block_param(done, Ty::U64);
        let done_status = fb.add_block_param(done, Ty::U64);

        fb.switch_to_block(entry);
        let zero = fb.iconst(Ty::U64, 0);
        let seed = fb.iconst(Ty::U64, i128::from(FINGERPRINT_SEED));
        fb.br(header, vec![zero, zero, zero, zero, seed, zero]);

        fb.switch_to_block(header);
        let has_parent = fb.icmp(ICmpOp::Ult, Ty::U64, idx, parent_count);
        fb.condbr(
            has_parent,
            body,
            vec![],
            done,
            vec![state_count, generated, last_parent, fingerprint, status],
        );

        fb.switch_to_block(body);
        let parent_ptr = fb.gep(Ty::U64, parents, vec![idx]);
        let parent = fb.load(Ty::U64, parent_ptr);
        let one = fb.iconst(Ty::U64, 1);
        let next_idx = fb.binop(BinOp::Add, Ty::U64, idx, one);
        let next_state_count = fb.binop(BinOp::Add, Ty::U64, state_count, one);
        let mixed = fb.binop(BinOp::Xor, Ty::U64, fingerprint, parent);
        let prime = fb.iconst(Ty::U64, i128::from(FINGERPRINT_PRIME));
        let mixed = fb.binop(BinOp::Mul, Ty::U64, mixed, prime);
        let next_fingerprint = fb.binop(BinOp::Add, Ty::U64, mixed, next_state_count);
        fb.br(
            header,
            vec![
                next_idx,
                next_state_count,
                generated,
                parent,
                next_fingerprint,
                status,
            ],
        );

        fb.switch_to_block(done);
        fb.store_proven(
            Ty::U64,
            out,
            done_state_count,
            vec![ProofAnnotation::Aligned(16)],
        );
        let _ = fb.insert_field(Ty::Struct(summary_pair), out, 1, done_generated);
        store_summary_slot(&mut fb, out, 2, done_last_parent);
        store_summary_slot(&mut fb, out, 3, done_fingerprint);
        store_summary_slot(&mut fb, out, 4, done_status);
        fb.ret(vec![done_status]);

        fb.build();
    }

    mb.build()
}

fn compile_to_jit(module: &trust_ir::Module, opt_level: OptLevel) -> ExecutableBuffer {
    let mut config = CompilerConfig::jit_fast(Target::Aarch64);
    config.opt_level = opt_level;
    Compiler::new(config)
        .compile_module_to_jit(module, &HashMap::new())
        .unwrap_or_else(|err| panic!("{opt_level:?} compile failed: {err}"))
        .buffer
}

fn entry_signature() -> trust_cg_codegen::jit_contract::SymbolSignature {
    extern_c_signature(vec![abi_ptr(), abi_i64(), abi_ptr()], vec![abi_i64()])
}

fn run_at(opt_level: OptLevel, parents: &[u64]) -> BfsSummary {
    let module = build_no_action_parent_loop_module();
    let buffer = compile_to_jit(&module, opt_level);
    let entry: EntryFn = bind_ty_reducer_entry(&buffer, opt_level, ENTRY_NAME, entry_signature());

    let mut slots = [u64::MAX; 5];
    let status = entry(parents.as_ptr(), parents.len() as u64, slots.as_mut_ptr());
    assert_eq!(status, slots[4], "{opt_level:?} return/status mismatch");
    BfsSummary::from_slots(slots)
}

fn run_at_with_certs(
    opt_level: OptLevel,
    parents: &[u64],
) -> (BfsSummary, Vec<ProofOptimizationCertificateCitation>) {
    let module = build_no_action_parent_loop_module();
    let buffer = compile_to_jit(&module, opt_level);
    let certs = buffer.proof_optimization_certificates().to_vec();
    let entry: EntryFn = bind_ty_reducer_entry(&buffer, opt_level, ENTRY_NAME, entry_signature());

    let mut slots = [u64::MAX; 5];
    let status = entry(parents.as_ptr(), parents.len() as u64, slots.as_mut_ptr());
    assert_eq!(status, slots[4], "{opt_level:?} return/status mismatch");
    (BfsSummary::from_slots(slots), certs)
}

fn assert_no_alignment_claim_authority(certs: &[ProofOptimizationCertificateCitation]) {
    let aligned_pair_certs: Vec<_> = certs
        .iter()
        .filter(|cert| {
            cert.function_name == ENTRY_NAME
                && cert.transform_name == "proof-opts.aligned.pair-combined"
                && cert.kind == "PairCombined"
                && cert.status == "applied"
                && cert.admission == "proof-facts"
                && cert
                    .consumed_facts
                    .iter()
                    .any(|fact| fact.name == "Aligned" && fact.payload.as_deref() == Some("16"))
        })
        .collect();

    assert!(
        aligned_pair_certs.is_empty(),
        "producer-owned Aligned(16) claims must not mint PairCombined certificates without replay authority; got {certs:#?}"
    );
}

fn interpret_no_action_parent_loop(parents: &[u64]) -> BfsSummary {
    let mut summary = BfsSummary {
        state_count: 0,
        generated: 0,
        last_parent: 0,
        fingerprint: FINGERPRINT_SEED,
        status: 0,
    };

    for &parent in parents {
        summary.state_count += 1;
        summary.last_parent = parent;
        summary.fingerprint =
            (summary.fingerprint ^ parent) * FINGERPRINT_PRIME + summary.state_count;
    }

    summary
}

#[test]
fn native_bfs_no_action_parent_loop_o1_o3_status_summaries_match() {
    for parents in [&[][..], &[4, 7, 4, 8][..]] {
        let expected = interpret_no_action_parent_loop(parents);
        let o1 = run_at(OptLevel::O1, parents);
        let (o3, o3_certs) = run_at_with_certs(OptLevel::O3, parents);

        assert_eq!(o1, expected, "O1 summary diverged for parents={parents:?}");
        assert_eq!(o3, expected, "O3 summary diverged for parents={parents:?}");
        assert_eq!(
            o3, o1,
            "O3 should match O1 for state count, generated count, parent index, fingerprint, and status"
        );
        assert_no_alignment_claim_authority(&o3_certs);
    }
}
