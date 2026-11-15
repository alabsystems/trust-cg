// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Epoch names affect identity only; this supplies no call/world proof.

use super::*;

#[derive(Default)]
struct Bytes(Vec<u8>);

impl Sink for Bytes {
    fn write(&mut self, bytes: &[u8]) {
        self.0.extend_from_slice(bytes);
    }

    fn fail(&mut self, error: RetainedIdentityError) {
        panic!("small independent encoding must fit: {error}");
    }
}

#[test]
fn clause_places_keep_legacy_bytes_and_distinct_appended_world_epoch_tags() {
    use trust_ir::value::ValueId;
    let rows = [
        (ClausePlace::Param { index: 17 }, 0_u16, Some(17_u32)),
        (ClausePlace::ResultSlot { index: 17 }, 1, Some(17)),
        (ClausePlace::MutParamExit { index: 17 }, 2, Some(17)),
        (ClausePlace::World, 3, None),
        (ClausePlace::Unwind, 4, None),
        (ClausePlace::Value(ValueId::new(17)), 5, Some(17)),
        (ClausePlace::SpecVar { index: 17 }, 6, Some(17)),
        (ClausePlace::SpecVarNext { index: 17 }, 7, Some(17)),
        (ClausePlace::WorldPre, 8, None),
        (ClausePlace::WorldPost, 9, None),
        (ClausePlace::ParamPointeeEntry { index: 17 }, 10, Some(17)),
    ];
    for (place, tag, index) in rows {
        let mut expected = tag.to_be_bytes().to_vec();
        if let Some(index) = index {
            expected.extend_from_slice(&index.to_be_bytes());
        }
        let mut bytes = Bytes::default();
        encode_clause_place(&mut Encoder(&mut bytes), &place);
        assert_eq!(bytes.0, expected, "{place:?}");
        let mut count = CountSink::default();
        encode_clause_place(&mut Encoder(&mut count), &place);
        assert_eq!(count.0, Ok(expected.len() as u64), "{place:?}");
    }
}

#[test]
fn retained_formula_identity_separates_legacy_entry_and_exit_world_bindings() {
    let function = Function::new(
        "world_identity",
        Signature {
            params: vec![],
            returns: vec![],
        },
    );
    let digest = |place| {
        let mut formula = ProofFormula::new("world.schema", "identical proposition");
        formula.bindings.push((
            "heap".to_owned(),
            ClauseBinding {
                sort: ClauseSort::Array(
                    Box::new(ClauseSort::BitVec(64)),
                    Box::new(ClauseSort::BitVec(8)),
                ),
                place,
            },
        ));
        let mut proofs = ProofContext::default();
        proofs.synthesized_obligation_formulas.push((1, formula));
        retained_lir_proof_context_digest(&[(function.clone(), proofs)])
            .expect("small complete retained payload")
    };
    let legacy = digest(ClausePlace::World);
    let entry = digest(ClausePlace::WorldPre);
    let exit = digest(ClausePlace::WorldPost);
    assert_ne!(legacy, entry);
    assert_ne!(legacy, exit);
    assert_ne!(entry, exit);
    assert_eq!(entry, digest(ClausePlace::WorldPre));
    assert_eq!(exit, digest(ClausePlace::WorldPost));
}
