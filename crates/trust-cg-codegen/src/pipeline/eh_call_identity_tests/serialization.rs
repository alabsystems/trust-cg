//! The standalone serializer must not ignore modern machine-call custody.

use super::*;

#[test]
fn standalone_lsda_serialization_accepts_resolved_custody_and_refuses_identity_mutants() {
    let mut valid = fixture();
    resolve(&mut valid, &EhPropagation::Filler).unwrap();
    assert!(generate_lsda_for_function(&valid.func).unwrap().is_some());
    let selected_binding = bindings(&mut valid)[0];
    for change in 0..5 {
        let mut bad = valid.clone();
        match change {
            0 => bindings(&mut bad).clear(),
            1 => bindings(&mut bad).push(selected_binding),
            2 => bindings(&mut bad)[0].call_inst = InstId(u32::MAX),
            3 => bindings(&mut bad)[0].call_block = valid.normal,
            4 => bad.func.insts[valid.selected.0 as usize] = IrMachInst::new(IrOpcode::Nop, vec![]),
            _ => unreachable!(),
        }
        let error = generate_lsda_for_function(&bad.func).unwrap_err();
        assert!(
            matches!(error, PipelineError::MalformedAarch64Eh { .. }),
            "change {change}: {error}"
        );
    }
}

#[test]
fn orphan_exact_custody_cannot_serialize_as_an_empty_non_eh_function() {
    let mut bad = fixture();
    bad.func.eh_metadata.personality = None;
    bad.func.eh_metadata.landing_pads.clear();
    bad.func.eh_metadata.call_sites.clear();
    assert!(matches!(
        generate_lsda_for_function(&bad.func),
        Err(PipelineError::MalformedAarch64Eh { .. })
    ));
}
