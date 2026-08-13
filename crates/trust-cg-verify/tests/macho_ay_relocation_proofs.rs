// trust-cg-verify/tests/macho_ay_relocation_proofs.rs - external AY lane
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use trust_cg_verify::ay_bridge::{AYConfig, AYResult, verify_with_ay};
use trust_cg_verify::macho_data_reloc_proofs::{
    x86_64_macho_data_relocation_negative_controls, x86_64_macho_data_relocation_proofs,
};
use trust_cg_verify::macho_proofs::macho_relocation_proofs;

#[test]
fn ay_proves_macho_relocation_arithmetic_subset() {
    let config = AYConfig::default().with_timeout(10_000);
    let mut verified = 0usize;

    for obligation in macho_relocation_proofs() {
        let result = verify_with_ay(&obligation, &config);
        assert!(
            matches!(result, AYResult::Verified),
            "Mach-O relocation ay proof '{}' returned {}; expected Verified",
            obligation.name,
            result
        );
        verified += 1;
    }

    assert_eq!(verified, 10);
}

/// Discharge the x86-64 Mach-O DATA relocation selection/encoding proofs
/// through the real solver lane: every positive obligation must be Verified
/// (the emitted linker formula == the intended address expression).
#[test]
fn ay_proves_x86_64_macho_data_relocation_selection() {
    let config = AYConfig::default().with_timeout(10_000);
    let mut verified = 0usize;

    for obligation in x86_64_macho_data_relocation_proofs() {
        let result = verify_with_ay(&obligation, &config);
        assert!(
            matches!(result, AYResult::Verified),
            "x86-64 Mach-O data relocation ay proof '{}' returned {}; expected Verified",
            obligation.name,
            result
        );
        verified += 1;
    }

    assert_eq!(verified, 9);
}

/// Soundness witness: every NEGATIVE control (a malformed relocation row with
/// the wrong r_pcrel / r_length / addend / operand order) must be REFUTED by
/// the solver. This proves the positive obligations are real equivalences and
/// not tautologies.
#[test]
fn ay_refutes_x86_64_macho_data_relocation_wrong_encodings() {
    let config = AYConfig::default().with_timeout(10_000);
    let mut refuted = 0usize;

    for obligation in x86_64_macho_data_relocation_negative_controls() {
        let result = verify_with_ay(&obligation, &config);
        assert!(
            matches!(result, AYResult::CounterExample(_)),
            "x86-64 Mach-O data relocation NEGATIVE control '{}' returned {}; \
             a wrong encoding must produce a CounterExample",
            obligation.name,
            result
        );
        refuted += 1;
    }

    assert_eq!(refuted, 7);
}
