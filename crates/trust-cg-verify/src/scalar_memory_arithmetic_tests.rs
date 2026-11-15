// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Exact scalar-memory transcription controls, not independent replay proof.
//! The original source, memory/access inventory and legacy read-only codec stay
//! complete. A new pending query is not a certificate for historical raw bytes.

use super::*;
use crate::smt::{EvalEnv, SmtSort};
#[cfg(all(target_arch = "aarch64", target_os = "macos"))]
use sha2::{Digest, Sha256};
#[cfg(all(target_arch = "aarch64", target_os = "macos"))]
use trust_cg_codegen::CoreHostJitTarget;

fn graph(operations: Vec<(Option<(u32, Kind)>, Operation)>, kind: Kind) -> Graph {
    let parameters = vec![(0, kind)];
    Graph {
        entry: 0,
        parameters: parameters.clone(),
        blocks: vec![Block {
            id: 0,
            parameters,
            nodes: operations
                .into_iter()
                .enumerate()
                .map(|(instruction, (result, operation))| Node {
                    site: ReadOnlySite {
                        block: 0,
                        instruction,
                    },
                    result,
                    operation,
                })
                .collect(),
        }],
    }
}

fn arithmetic(bits: u32, opcode: Opcode, a: u64, b: u64) -> Graph {
    let kind = if bits == 32 { Kind::Word32 } else { Kind::Word };
    let mut nodes = vec![
        (Some((1, kind)), Operation::Constant(a)),
        (Some((2, kind)), Operation::Constant(b)),
        (
            Some((3, kind)),
            Operation::Binary {
                opcode,
                left: 1,
                right: 2,
            },
        ),
    ];
    let returned = if bits == 32 {
        nodes.push((Some((4, Kind::Word)), Operation::ZeroExtend(3)));
        4
    } else {
        3
    };
    nodes.push((None, Operation::Return(returned)));
    graph(nodes, Kind::Word)
}

fn observed(graph: &Graph, profile: Profile) -> Result<Observations, ReadOnlySourceError> {
    observe_profile(
        graph,
        &[("abi_x0".into(), 64)],
        &E::uf("entry_memory", vec![], memory_sort()),
        Boundary::Source,
        profile,
    )
}

fn first_rhs(observations: &Observations) -> &E {
    let E::Eq { lhs, rhs } = &observations.memory.as_ref().unwrap().definitions.equations[0] else {
        panic!("complete semantic definition equation required");
    };
    assert!(matches!(lhs.as_ref(), E::UF { args, .. } if args.is_empty()));
    rhs
}

#[test]
fn scalar_add_sub_use_exact_width_shared_codec_and_one_operation_node() {
    for bits in [32, 64] {
        let ty = if bits == 32 {
            LirType::I32
        } else {
            LirType::I64
        };
        for opcode in [Opcode::Iadd, Opcode::Isub] {
            for endpoint in [scalar_memory::Endpoint::Core, scalar_memory::Endpoint::Lir] {
                let observations = observed(
                    &arithmetic(bits, opcode.clone(), 7, 9),
                    Profile::ScalarMemory(endpoint),
                )
                .unwrap();
                let rhs = first_rhs(&observations);
                assert_eq!(rhs.try_bv_width().unwrap(), bits);
                assert_eq!(rhs.sort(), SmtSort::BitVec(bits));
                assert_eq!(
                    rhs,
                    &crate::trust_ir_semantics::encode_trust_ir_binop(
                        &opcode,
                        ty.clone(),
                        E::bv_const(7, bits),
                        E::bv_const(9, bits),
                    )
                );
                assert!(
                    matches!(rhs, E::BvAdd { width, .. } | E::BvSub { width, .. } if *width == bits)
                );
                let definitions = &observations.memory.as_ref().unwrap().definitions;
                assert_eq!(definitions.equations.len(), if bits == 32 { 2 } else { 1 });
                // Two leaves + one arithmetic operation + equality/UF; a
                // narrow return additionally defines its exact zero extension.
                assert_eq!(definitions.nodes, if bits == 32 { 9 } else { 5 });
                assert!(observations.geometry.is_empty());
                assert!(observations.reads.is_empty());
                assert!(observations.memory.as_ref().unwrap().writes.is_empty());
            }
        }
    }
}

#[test]
fn scalar_modular_boundaries_match_legacy_widened_results_without_assumptions() {
    for bits in [32, 64] {
        let mask = if bits == 32 {
            u32::MAX as u64
        } else {
            u64::MAX
        };
        let sign = 1u64 << (bits - 1);
        let samples = [
            (0, 0),
            (0, 1),
            (mask, 1),
            (mask, mask),
            (sign - 1, 1),
            (sign, 1),
            (sign, mask),
            (sign, sign),
            (1, mask),
            (0xaaaa_aaaa_aaaa_aaaa & mask, 0x5555_5555_5555_5555 & mask),
        ];
        for opcode in [Opcode::Iadd, Opcode::Isub] {
            for (a, b) in samples {
                let observations = observed(
                    &arithmetic(bits, opcode.clone(), a, b),
                    Profile::ScalarMemory(scalar_memory::Endpoint::Core),
                )
                .unwrap();
                let rhs = first_rhs(&observations);
                let old = raw_arithmetic(
                    &opcode,
                    bits,
                    &Term::leaf(E::bv_const(a, bits)),
                    &Term::leaf(E::bv_const(b, bits)),
                )
                .unwrap();
                let environment = EvalEnv::default();
                assert_eq!(
                    rhs.try_eval(&environment).unwrap(),
                    old.expr.try_eval(&environment).unwrap()
                );
                let expected = if opcode == Opcode::Iadd {
                    a.wrapping_add(b)
                } else {
                    a.wrapping_sub(b)
                } & mask;
                assert_eq!(rhs.try_eval(&environment).unwrap().as_u64(), expected);
            }
        }
    }
}

#[test]
fn readonly_retains_exact_widened_add_sub_transcription() {
    for opcode in [Opcode::Iadd, Opcode::Isub] {
        let observations =
            observed(&arithmetic(64, opcode.clone(), 7, 9), Profile::ReadOnly).unwrap();
        let old = raw_arithmetic(
            &opcode,
            64,
            &Term::leaf(E::bv_const(7, 64)),
            &Term::leaf(E::bv_const(9, 64)),
        )
        .unwrap();
        let expected = E::ite(E::BoolConst(true), old.expr, E::bv_const(0, 64));
        assert_eq!(observations.result.as_ref().unwrap().expr, expected);
        assert_eq!(observations.result.as_ref().unwrap().nodes, 9);
        let mnemonic = if opcode == Opcode::Iadd {
            "bvadd"
        } else {
            "bvsub"
        };
        assert_eq!(
            observations.result.as_ref().unwrap().expr.to_string(),
            format!(
                "(ite true ((_ extract 63 0) ({mnemonic} ((_ zero_extend 1) (_ bv7 64)) ((_ zero_extend 1) (_ bv9 64)))) (_ bv0 64))"
            )
        );
        assert!(observations.memory.is_none());
        assert!(observations.geometry.is_empty());
    }
}

#[test]
fn scalar_arithmetic_still_refuses_mixed_width_pointer_and_wrong_result_codecs() {
    for opcode in [Opcode::Iadd, Opcode::Isub] {
        for (a, b, result, parameter, reason) in [
            (
                Kind::Word32,
                Kind::Word,
                Kind::Word,
                Kind::Word,
                "binary operand type",
            ),
            (
                Kind::Word,
                Kind::Word32,
                Kind::Word,
                Kind::Word,
                "binary operand type",
            ),
            (
                Kind::Word32,
                Kind::Word32,
                Kind::Word,
                Kind::Word,
                "result type or repeated SSA definition",
            ),
            (
                Kind::Boolean,
                Kind::Boolean,
                Kind::Boolean,
                Kind::Word,
                "binary/shift outside raw profile",
            ),
            (
                Kind::Pointer,
                Kind::Pointer,
                Kind::Word,
                Kind::Pointer,
                "binary operand type",
            ),
        ] {
            let value = |id, kind| {
                (
                    Some((id, kind)),
                    if kind == Kind::Pointer {
                        Operation::Copy(0)
                    } else {
                        Operation::Constant(0)
                    },
                )
            };
            let input = graph(
                vec![
                    value(1, a),
                    value(2, b),
                    (
                        Some((3, result)),
                        Operation::Binary {
                            opcode: opcode.clone(),
                            left: 1,
                            right: 2,
                        },
                    ),
                    (None, Operation::Return(3)),
                ],
                parameter,
            );
            assert!(
                matches!(observed(&input, Profile::ScalarMemory(scalar_memory::Endpoint::Core)), Err(ReadOnlySourceError::Source(actual)) if actual == reason)
            );
        }
    }
}

#[cfg(all(target_arch = "aarch64", target_os = "macos"))]
#[test]
fn complete_original_scalar_capture_retains_every_definition_geometry_and_access() {
    let bytes = include_str!("../tests/fixtures/ty_original_scalar_action.json");
    assert_eq!(
        format!("{:x}", Sha256::digest(bytes.as_bytes())),
        "99ae4db9ad00d6ae1cefbf4ee787fdefce14e2d8531b27337227a0840d2f51cd"
    );
    let capture: serde_json::Value = serde_json::from_str(bytes).unwrap();
    assert_eq!(capture["format"], "ty-original-scalar-action-source-v1");
    assert_eq!(capture["selection"]["unit_key"], "next:Next@91-101");
    let original: Module = serde_json::from_value(capture["module"].clone()).unwrap();
    assert_eq!(original.functions.len(), 10);
    assert_eq!(original.functions[3].id.index(), 60_002);
    assert_eq!(original.functions[3].blocks.len(), 16);
    assert_eq!(
        original.functions[3]
            .blocks
            .iter()
            .map(|b| b.body.len())
            .sum::<usize>(),
        117
    );
    assert!(original.target_info.is_none());
    let mut module = original.clone();
    module.target_info = Some(
        CoreHostJitTarget::detect()
            .unwrap()
            .trust_ir_target_info()
            .clone(),
    );
    let mut restored = module.clone();
    restored.target_info = None;
    assert_eq!(
        serde_json::to_value(restored).unwrap(),
        serde_json::to_value(original).unwrap()
    );
    let (lowering, _proof_context) = trust_cg_lower::translate_function_with_license(
        &module.functions[3],
        &module,
        &crate::license_test_support::permit_unlicensed(),
    )
    .unwrap();
    let queries = scalar_memory::bind_scalar_memory_source(&module, 3, &lowering).unwrap();
    assert!(std::ptr::eq(queries.source(), &module.functions[3]));
    assert!(std::ptr::eq(queries.lir(), &lowering));
    assert_eq!(queries.original_encoding_definitions().len(), 58);
    assert_eq!(queries.encoding_definitions().len(), 118);
    assert_eq!(queries.source_geometry().len(), 31);
    assert_eq!(queries.source_reads().len(), 10);
    assert_eq!(queries.lowering_reads().len(), 10);
    assert_eq!(queries.source_writes().len(), 5);
    assert_eq!(queries.lowering_writes().len(), 5);
    assert_eq!(queries.read_obligations().len(), 10);
    assert_eq!(queries.write_obligations().len(), 5);
    assert_eq!(
        queries.status_obligation().trust_ir_expr.sort(),
        SmtSort::BitVec(64)
    );
    let obligations = std::iter::once(queries.status_obligation())
        .chain(std::iter::once(queries.memory_obligation()))
        .chain(queries.read_obligations())
        .chain(queries.write_obligations());
    for obligation in obligations {
        assert_eq!(obligation.preconditions.len(), 149);
        assert_eq!(&obligation.preconditions[..31], queries.source_geometry());
        assert_eq!(
            &obligation.preconditions[31..],
            queries.encoding_definitions()
        );
        assert_eq!(
            obligation.inputs,
            (0..4)
                .map(|i| (format!("abi_x{i}"), 64))
                .chain(std::iter::once(("observe".into(), 64)))
                .collect::<Vec<_>>()
        );
    }
    // GEP stays in its complete original transcription: only arithmetic
    // operations changed, not source geometry or pointer provenance premises.
    assert_eq!(
        queries.encoding_definitions()[0].to_string(),
        "(= scalar_memory_core_d0 (bvadd abi_x1 (bvmul (_ bv0 64) (_ bv1 64))))"
    );
    assert_eq!(
        queries.encoding_definitions()[58].to_string(),
        "(= scalar_memory_lir_d0 (bvadd abi_x1 (bvmul (_ bv0 64) (_ bv1 64))))"
    );
}
