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
    let source = FunctionSourceModules::capture(&fixture.module, &fixture.module);
    assert!(std::ptr::eq(source.original(), &fixture.module));
    assert!(std::ptr::eq(source.lowered(), &fixture.module));
    let clone = fixture.module.clone();
    assert_eq!(
        source.digest(),
        FunctionSourceModules::capture(&clone, &clone).digest()
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
            FunctionSourceModules::capture(&changed, &fixture.module),
            FunctionSourceModules::capture(&fixture.module, &changed),
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
        FunctionSourceModules::capture(&first, &fixture.module).digest(),
        FunctionSourceModules::capture(&second, &fixture.module).digest(),
    );
}
