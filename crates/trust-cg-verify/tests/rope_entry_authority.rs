// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0
//! Entry-authority scans visit stored sequence/set elements, not the logical
//! length of compact ropes. This is a bounded control, not a benchmark.

use trust_cg_verify::fsym_trust_ir::FSYM_RUN_MODEL;
use trust_ir::{ArrayValue, InterpretOptions, InterpretValue, InterpretValueKind, Ty, TyId};

#[test]
fn compact_sequence_and_set_entries_do_not_hide_unwritten_lanes_or_forged_handles() {
    let options = InterpretOptions::default();
    let scalar = InterpretValue::int(Ty::U64, 7).unwrap();
    let length = 1u64 << 40;
    for is_set in [false, true] {
        let wrap = |values: ArrayValue| InterpretValue {
            ty: if is_set {
                Ty::Set(TyId::new(0), trust_ir::SetRepr::Boxed)
            } else {
                Ty::Sequence(TyId::new(0))
            },
            kind: if is_set {
                InterpretValueKind::Set(values)
            } else {
                InterpretValueKind::Sequence(values)
            },
        };
        let clean = ArrayValue::splat(scalar.clone(), length);
        assert_eq!(clean.len(), length);
        assert_eq!(
            FSYM_RUN_MODEL.breach(&options, &[wrap(clean.clone())]),
            None
        );
        for (poison, expected) in [
            (
                InterpretValue {
                    ty: Ty::U64,
                    kind: InterpretValueKind::Uninit,
                },
                "unwritten aggregate lane (uninit)",
            ),
            (
                InterpretValue {
                    ty: Ty::U64,
                    kind: InterpretValueKind::Handle { id: 1 },
                },
                "runtime handle",
            ),
        ] {
            // A persistent edit at the final logical element must still be
            // visited, without materializing the trillion-element splat.
            let changed = clean.set(length - 1, poison).unwrap();
            let refusal = FSYM_RUN_MODEL.breach(&options, &[wrap(changed)]).unwrap();
            assert!(refusal.contains(expected), "{refusal}");
            assert_eq!(
                FSYM_RUN_MODEL.breach(&options, &[wrap(clean.clone())]),
                None
            );
        }
    }
}
