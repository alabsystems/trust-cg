// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0
//! Original modules captured from the genuine Trust frontend. Validation and
//! v52 refuses the original kindless assertions instead of erasing panic
//! identity in generic traps. These historical captures are not rewritten.

use trust_cg_codegen::compiler::module_object_globals;
use trust_cg_lower::global_image::type_flat_image;
use trust_cg_lower::instructions::Opcode;
use trust_ir::{Inst, Module};

fn module(name: &str, level: u8) -> Module {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/canonical_bounds")
        .join(format!("{name}-O{level}.trust-ir.json"));
    serde_json::from_slice(&std::fs::read(path).unwrap()).unwrap()
}

#[test]
fn actual_frontend_bounds_keep_original_conditions_and_refuse_kindless_panics() {
    for name in [
        "bounds_const",
        "bounds_dominated",
        "bounds_mask",
        "bounds_dynamic",
        "output_memory_writer",
    ] {
        for level in [0, 1] {
            let module = module(name, level);
            let errors = trust_ir_build::validate_module(&module);
            assert!(errors.is_empty(), "{name} O{level}: {errors:?}");
            assert!(module.proof_obligations.is_empty());
            assert!(module.proof_certificates.is_empty());
            let function = &module.functions[0];
            let expected = match (name, level) {
                ("bounds_const" | "output_memory_writer", 1) => 0,
                ("output_memory_writer", 0) => 5,
                _ => 1,
            };
            let mut assertions = 0;
            let mut comparisons = 0;
            for block in &function.blocks {
                for (position, node) in block.body.iter().enumerate() {
                    assert!(node.proofs.is_empty());
                    if matches!(node.inst, Inst::ICmp { .. }) {
                        comparisons += 1;
                        assert_eq!(node.results.len(), 1);
                    }
                    if let Inst::Assert {
                        cond,
                        kind: trust_ir::AssertKind::Unspecified,
                        site: _,
                    } = node.inst
                    {
                        assertions += 1;
                        let producer = &block.body[position.checked_sub(1).unwrap()];
                        assert!(matches!(producer.inst, Inst::ICmp { .. }));
                        assert_eq!(producer.results, vec![cond]);
                    }
                }
            }
            assert_eq!(assertions, expected, "{name} O{level}");
            assert_eq!(
                comparisons,
                expected + usize::from(name == "bounds_dominated")
            );
            let translated = trust_cg_lower::translate_function_with_license(
                function,
                &module,
                &permit_unlicensed(),
            );
            if expected != 0 {
                let err = translated.unwrap_err();
                assert!(err.to_string().contains("unspecified panic kind"), "{err}");
                assert!(
                    err.to_string().contains("require_assert_panic_kinds"),
                    "{err}"
                );
                continue;
            }
            let (lir, proofs) = translated.unwrap();
            assert!(proofs.synthesized_discharged.is_empty());
            assert!(proofs.synthesized_obligation_formulas.is_empty());
            let guards = lir
                .blocks
                .values()
                .flat_map(|block| &block.instructions)
                .filter(|node| {
                    matches!(
                        node.opcode,
                        Opcode::GuardBoundsCheck {
                            obligation: None,
                            ..
                        }
                    )
                })
                .count();
            assert_eq!(guards, expected, "{name} O{level}");
        }
    }
}

#[test]
fn actual_unwinding_bounds_keep_failure_edge_and_panic_call() {
    for level in [0, 1] {
        let module = module("bounds_unwind", level);
        let errors = trust_ir_build::validate_module(&module);
        // The unchanged panic path still has three malformed byte globals:
        // aggregates declared as Ptr. Preserve their exact validation refusal;
        // retaining the unwind edge does not establish whole-module validity.
        assert_eq!(errors.len(), 3, "O{level}: {errors:?}");
        for (global, bytes) in [("alloc1", 19), ("alloc3", 17), ("alloc2", 92)] {
            assert!(
                errors.contains(&trust_ir_build::ValidationError::ConstTypeMismatch {
                    location: format!("global 'bounds_unwind.const.{global}'"),
                    expected: "ptr".into(),
                    actual: format!("aggregate[{bytes}]"),
                }),
                "O{level}: {errors:?}"
            );
        }
        assert!(module.proof_obligations.is_empty());
        let function = &module.functions[0];
        let mut failures = 0;
        for block in &function.blocks {
            for node in &block.body {
                assert!(!matches!(node.inst, Inst::Assert { .. }));
                if let Inst::CondBr { else_target, .. } = node.inst {
                    let failure = function
                        .blocks
                        .iter()
                        .find(|b| b.id == else_target)
                        .unwrap();
                    assert!(
                        failure
                            .body
                            .iter()
                            .any(|n| matches!(n.inst, Inst::Call { .. } | Inst::Invoke { .. }))
                    );
                    failures += 1;
                }
            }
        }
        assert_eq!(failures, 1);
        // Every adapter entry consumes TrustIR's typed admission, so the three
        // byte images are given their canonical storage types in memory (the
        // capture file is not rewritten) before the function lowers. The
        // object writer's image of each is exactly the original's.
        let mut repaired = module.clone();
        let images: Vec<usize> = (0..repaired.globals.len())
            .filter(|&index| {
                matches!(
                    &repaired.globals[index],
                    trust_ir::Global {
                        ty: trust_ir::Ty::Ptr,
                        initializer: Some(trust_ir::Constant::Aggregate(_)),
                        ..
                    }
                )
            })
            .collect();
        assert_eq!(images.len(), 3, "O{level}");
        for index in images {
            let Some(trust_ir::Constant::Aggregate(image)) =
                repaired.globals[index].initializer.take()
            else {
                unreachable!("selected above");
            };
            let name = repaired.globals[index].name.clone();
            let typed = type_flat_image(&mut repaired, &name, image, 8).unwrap();
            repaired.globals[index].ty = typed.ty;
            repaired.globals[index].initializer = Some(typed.initializer);
        }
        assert_eq!(trust_ir_build::validate_module(&repaired), [], "O{level}");
        assert_eq!(
            module_object_globals(&repaired).unwrap(),
            module_object_globals(&module).unwrap(),
            "O{level}"
        );
        let function = &repaired.functions[0];
        let (lir, proofs) = trust_cg_lower::translate_function_with_license(
            function,
            &repaired,
            &permit_unlicensed(),
        )
        .unwrap();
        assert!(proofs.synthesized_discharged.is_empty());
        assert!(
            !lir.blocks
                .values()
                .flat_map(|b| &b.instructions)
                .any(|n| matches!(n.opcode, Opcode::GuardBoundsCheck { .. }))
        );
    }
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes because it was silently refused.
fn permit_unlicensed() -> trust_cg_lower::CodegenLicensePolicy {
    trust_cg_lower::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit)
}
