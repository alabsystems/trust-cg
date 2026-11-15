use super::*;
use crate::{FunctionVerifier, provenance_xcheck::ProvenanceXCheckMode};
use trust_cg_ir::{MachFunction, Signature};

#[derive(serde::Deserialize)]
struct Capture {
    module: trust_ir::Module,
    lir: trust_cg_lower::Function,
}

fn capture() -> Capture {
    let mut captures: Vec<Capture> =
        serde_json::from_str(include_str!("source_bound_cell_sources.json")).unwrap();
    captures.remove(0)
}

#[test]
fn module_custody_binds_original_and_lowered_declarations_without_lir_changes() {
    let fixture = capture();
    let source = FunctionSourceModules::capture(&fixture.module, &fixture.module).unwrap();
    assert!(std::ptr::eq(source.original(), &fixture.module));
    assert!(std::ptr::eq(source.lowered(), &fixture.module));
    let clone = fixture.module.clone();
    assert_eq!(
        source.digest(),
        FunctionSourceModules::capture(&clone, &clone)
            .unwrap()
            .digest()
    );

    let machine = MachFunction::new(fixture.lir.name.clone(), Signature::new(vec![], vec![]));
    let verifier = FunctionVerifier::new();
    let request = verifier.capture_request_with_mode(ProvenanceXCheckMode::Off);
    let report =
        verifier.verify_with_request_and_modules(&machine, Some(&fixture.lir), &source, &request);
    assert_eq!(report.report().genuinely_verified_count(), 0);
    assert!(!report.reusable_for(&request));
    assert!(report.matches_aarch64_input_with_modules(&machine, Some(&fixture.lir), &source));
    assert!(!report.matches_aarch64_input(&machine, Some(&fixture.lir)));
    let legacy = verifier.verify_with_request(&machine, Some(&fixture.lir), &request);
    assert!(!legacy.matches_aarch64_input_with_modules(&machine, Some(&fixture.lir), &source));

    for mutation in 0..6 {
        let mut changed = fixture.module.clone();
        match mutation {
            0 => changed.functions[0].calling_conv = trust_ir::CallingConv::Fast,
            1 => changed.functions[1].calling_conv = trust_ir::CallingConv::Fast,
            2 => changed.functions[1].attrs.readonly = true,
            3 => changed.func_types[1].params[0] = trust_ir::Ty::Ptr,
            4 => changed.func_types[1].is_vararg = true,
            _ => changed.functions[1].name.push_str("_different_target"),
        }
        for modules in [
            FunctionSourceModules::capture(&changed, &fixture.module).unwrap(),
            FunctionSourceModules::capture(&fixture.module, &changed).unwrap(),
        ] {
            assert_ne!(source.digest(), modules.digest(), "mutation {mutation}");
            assert!(!report.matches_aarch64_input_with_modules(
                &machine,
                Some(&fixture.lir),
                &modules,
            ));
        }
    }
}

#[test]
fn module_identity_preserves_float_payload_bits() {
    let fixture = capture();
    let mut first = fixture.module.clone();
    first.functions[0].blocks[0].body[0].inst = trust_ir::Inst::Const {
        ty: trust_ir::Ty::F64,
        value: trust_ir::Constant::Float(f64::from_bits(0x7ff8_0000_0000_0001)),
    };
    let mut second = first.clone();
    second.functions[0].blocks[0].body[0].inst = trust_ir::Inst::Const {
        ty: trust_ir::Ty::F64,
        value: trust_ir::Constant::Float(f64::from_bits(0x7ff8_0000_0000_0002)),
    };
    assert_eq!(format!("{first:?}"), format!("{second:?}"));
    assert_ne!(
        FunctionSourceModules::capture(&first, &fixture.module)
            .unwrap()
            .digest(),
        FunctionSourceModules::capture(&second, &fixture.module)
            .unwrap()
            .digest(),
    );
}

/// Since wire v51 (trust-ir 9674bea5) every instruction has a binary tag: a
/// module carrying a WS3.20 `UnOp::CtLz` has a lossless image, so the pair has
/// a custody digest, and it differs from the unmodified pair's.
#[test]
fn module_custody_binds_a_v51_ws3_20_instruction() {
    let fixture = capture();
    let mut v51 = fixture.module.clone();
    v51.functions[0].blocks[0].body[0].inst = trust_ir::Inst::UnOp {
        op: trust_ir::UnOp::CtLz,
        ty: trust_ir::Ty::U32,
        operand: trust_ir::ValueId::new(0),
    };
    assert_eq!(
        v51.functions[0].blocks[0].body[0].inst.binary_wire_gap(),
        None
    );
    let control = FunctionSourceModules::capture(&fixture.module, &fixture.module).unwrap();
    for (original, lowered) in [
        (&v51, &fixture.module),
        (&fixture.module, &v51),
        (&v51, &v51),
    ] {
        let modules = FunctionSourceModules::capture(original, lowered)
            .expect("a v51 instruction has a binary image");
        assert_ne!(modules.digest(), control.digest());
    }
}

/// A module carrying a construct still ahead of its trust-ir wire tag has no
/// binary image, so the pair has no custody digest: `capture` refuses it by
/// name, on whichever side carries it, instead of letting trust-ir's writer
/// panic. The two such constructs a module can carry since wire v61 are
/// probed in `trust_ir_build::wire_identity_blocker`'s order: an inlining
/// chain link and a completeness claim. A bound CleanCic recheck, the third
/// until v61 (`certificate-binding`) gave it a carrier, now has an image and
/// so a custody digest (checked below).
#[test]
fn module_custody_refuses_a_module_without_a_wire_image() {
    let fixture = capture();
    let mut inlined = fixture.module.clone();
    inlined.functions[0].scopes = Some(vec![trust_ir::ScopeData {
        parent: None,
        span: None,
        inlined_at: Some(trust_ir::InlinedAt {
            span: trust_ir::SourceSpan {
                file: 0,
                line: 1,
                col: 1,
            },
            callee: "inlined_callee".to_owned(),
        }),
    }]);
    let mut claimed = fixture.module.clone();
    claimed.completeness = Some(trust_ir::ModuleCompleteness::Complete);
    let mut bound = fixture.module.clone();
    bound.proof_certificates.push(trust_ir::ProofCertificate {
        obligation: trust_ir::ProofId::new(73),
        prover: "synthetic custody fixture; not certified".into(),
        evidence: trust_ir::ProofEvidence::CleanCic {
            term: vec![1, 2],
            context: vec![3],
            lineage: trust_ir::ProofDigest::trust_ir_stable("synthetic.custody", b"lineage"),
            kernel_recheck: Some(trust_ir::CleanCicKernelRecheck {
                module: "CustodyFixture".into(),
                theorems: vec![],
                anchor: "custody-fixture".into(),
                allowed_axioms: vec![],
                binding: Some(Box::new(trust_ir::CertificateBinding::new(
                    trust_ir::ProofDigest::trust_ir_stable("synthetic.custody", b"environment"),
                    trust_ir::ProofDigest::trust_ir_stable("synthetic.custody", b"statement"),
                ))),
            }),
        },
        assurance: None,
    });
    for (unencodable, construct, location) in [
        (&inlined, "inlining chain link", "lexical scope #0"),
        (&claimed, "Module.completeness", "module"),
    ] {
        for (original, lowered, side) in [
            (unencodable, &fixture.module, "original"),
            (&fixture.module, unencodable, "lowered"),
            (unencodable, unencodable, "original"),
        ] {
            let refusal = FunctionSourceModules::capture(original, lowered)
                .expect_err("no binary image, no custody digest");
            assert_eq!(refusal.side, side);
            assert!(refusal.construct.contains(construct), "{refusal}");
            assert!(refusal.location.contains(location), "{refusal}");
        }
    }
    // Control: the unmodified pair still has an identity.
    FunctionSourceModules::capture(&fixture.module, &fixture.module).unwrap();
    // Since v61 the bound recheck has a binary image on either side, and the
    // binding is part of what the custody digest identifies: its unbound twin
    // (the same certificate, `binding: None`) digests differently.
    let mut unbound = bound.clone();
    let trust_ir::ProofEvidence::CleanCic {
        kernel_recheck: Some(recheck),
        ..
    } = &mut unbound.proof_certificates.last_mut().unwrap().evidence
    else {
        unreachable!("the fixture certificate carries a recheck directive")
    };
    recheck.binding = None;
    for (bound_pair, unbound_pair) in [
        ((&bound, &fixture.module), (&unbound, &fixture.module)),
        ((&fixture.module, &bound), (&fixture.module, &unbound)),
    ] {
        let with = FunctionSourceModules::capture(bound_pair.0, bound_pair.1)
            .unwrap_or_else(|refusal| panic!("a bound recheck has a wire image: {refusal}"));
        let without = FunctionSourceModules::capture(unbound_pair.0, unbound_pair.1).unwrap();
        assert_ne!(with.digest(), without.digest());
    }
}
