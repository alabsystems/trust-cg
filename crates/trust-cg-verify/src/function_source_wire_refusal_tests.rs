// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Actual writer-preflight and retained custody controls.
//! These establish encoding/identity behavior, not validation or native credit.

use super::wire_refusal::{map_wire_refusal, wire_image_blocker};
use super::*;
use trust_ir::{BinaryProjectionError, Module, Ty, WireNodeSite};

#[path = "function_source_wire_refusal_support.rs"]
mod support;
use support::{assert_refuses_each_side, binary_pair_digest, fixture, with_unused_abi};

#[test]
fn unused_recorded_abi_encoding_limits_refuse_before_custody_hashing() {
    let plain = fixture();
    for case in 0..3 {
        let (mut module, row) = with_unused_abi();
        let abi = module.func_types[row].abi.as_mut().unwrap();
        let expected = match case {
            0 => {
                abi.target.cpu = "a".repeat(trust_ir::signature_abi::MAX_ABI_TEXT_BYTES + 1);
                "ABI identity exceeds wire byte limit"
            }
            1 => {
                // Raw identity bytes fit; escaping expands the canonical
                // spelling past the shared bounded reader's byte limit.
                abi.target.cpu = "\0".repeat(trust_ir::signature_abi::MAX_ABI_TEXT_BYTES / 4);
                assert!(
                    abi.to_canonical_text().len() > trust_ir::signature_abi::MAX_ABI_TEXT_BYTES
                );
                "ABI text exceeds byte limit"
            }
            _ => {
                // Empty arguments and an Ignore result have 26 tree nodes.
                // 65,511 feature nodes put the actual descriptor one over.
                abi.target.features = (0..65_511).map(|i| format!("f{i:05}")).collect();
                "ABI record count exceeds wire node limit"
            }
        };
        assert_eq!(abi.validate_encoding_limits().unwrap_err(), expected);
        let refusal = BinaryProjectionError::SignatureAbiUnencodable {
            signature: row,
            detail: expected.to_owned(),
        };
        assert_eq!(module.wire_image_refusal(), Some(refusal.clone()));
        assert_refuses_each_side(
            &plain,
            &module,
            &format!("signature #{row}"),
            &refusal.to_string(),
        );
    }
}

#[test]
fn exact_abi_node_limit_and_semantic_only_malformed_records_keep_wire_custody() {
    let plain = fixture();
    let (mut at_limit, row) = with_unused_abi();
    let abi = at_limit.func_types[row].abi.as_mut().unwrap();
    abi.target.features = (0..65_510).map(|i| format!("f{i:05}")).collect();
    let text = abi.to_canonical_text();
    assert!(text.len() < trust_ir::signature_abi::MAX_ABI_TEXT_BYTES);
    assert_eq!(
        trust_ir::signature_abi::SignatureAbi::from_canonical_text(&text).unwrap(),
        *abi
    );
    abi.validate_encoding_limits().unwrap();
    assert_eq!(at_limit.wire_image_refusal(), None);
    for (original, lowered) in [
        (&at_limit, &plain),
        (&plain, &at_limit),
        (&at_limit, &at_limit),
    ] {
        assert!(FunctionSourceModules::capture(original, lowered).is_ok());
    }

    let (mut semantic_only, row) = with_unused_abi();
    semantic_only.func_types[row]
        .abi
        .as_mut()
        .unwrap()
        .fixed_count = 1;
    let signature = &semantic_only.func_types[row];
    let abi = signature.abi.as_ref().unwrap();
    abi.validate_encoding_limits().unwrap();
    assert_eq!(
        abi.validate(signature).unwrap_err(),
        "signature ABI variadic/fixed argument census disagrees"
    );
    assert_eq!(semantic_only.wire_image_refusal(), None);
    // Custody preserves untrusted claims; it never grants ABI or validation
    // authority. Adding semantic validation to the wire preflight is wrong.
    for (original, lowered) in [
        (&semantic_only, &plain),
        (&plain, &semantic_only),
        (&semantic_only, &semantic_only),
    ] {
        let captured = FunctionSourceModules::capture(original, lowered).unwrap();
        assert_eq!(*captured.digest(), binary_pair_digest(original, lowered));
    }
}

#[test]
fn producer_internal_type_refuses_both_sides_and_alias_without_writer_panic() {
    let plain = fixture();
    let refusal = BinaryProjectionError::ProducerInternalType;
    for unused_signature in [false, true] {
        let mut module = plain.clone();
        if unused_signature {
            let row = module.func_types.len();
            assert!(
                module
                    .functions
                    .iter()
                    .all(|function| function.ty.index() as usize != row)
            );
            module
                .func_types
                .push(trust_ir::FuncTy::unrecorded(vec![Ty::Error], vec![], false));
        } else {
            module.types.push(Ty::Error);
        }
        assert_eq!(module.wire_image_refusal(), Some(refusal.clone()));
        assert_refuses_each_side(&plain, &module, "module", &refusal.to_string());
    }
}

#[test]
fn writer_class_precedence_and_original_endpoint_precedence_stay_distinct() {
    let plain = fixture();
    let (mut abi_and_type, row) = with_unused_abi();
    abi_and_type.func_types[row]
        .abi
        .as_mut()
        .unwrap()
        .target
        .cpu = "a".repeat(trust_ir::signature_abi::MAX_ABI_TEXT_BYTES + 1);
    abi_and_type.types.push(Ty::Error);
    let abi_refusal = BinaryProjectionError::SignatureAbiUnencodable {
        signature: row,
        detail: "ABI identity exceeds wire byte limit".into(),
    };
    assert_eq!(abi_and_type.wire_image_refusal(), Some(abi_refusal.clone()));
    assert_refuses_each_side(
        &plain,
        &abi_and_type,
        &format!("signature #{row}"),
        &abi_refusal.to_string(),
    );
    abi_and_type.completeness = Some(trust_ir::ModuleCompleteness::Complete);
    assert_eq!(
        abi_and_type.wire_image_refusal(),
        Some(BinaryProjectionError::CompletenessClaimUnencodable)
    );
    assert_refuses_each_side(
        &plain,
        &abi_and_type,
        "module",
        "a Module.completeness claim ahead of its binary carrier",
    );

    let mut original = plain.clone();
    original.types.push(Ty::Error);
    let mut lowered = plain.clone();
    lowered.completeness = Some(trust_ir::ModuleCompleteness::Complete);
    let refusal = match FunctionSourceModules::capture(&original, &lowered) {
        Err(refusal) => refusal,
        Ok(_) => panic!("unencodable pair acquired custody"),
    };
    assert_eq!(refusal.side, "original");
    assert_eq!(
        refusal.construct,
        BinaryProjectionError::ProducerInternalType.to_string()
    );
}

#[test]
fn legacy_three_actual_refusal_diagnostics_remain_byte_exact() {
    let plain = fixture();
    let mut inlined = plain.clone();
    inlined.functions[0].scopes = Some(vec![trust_ir::ScopeData {
        parent: None,
        span: None,
        inlined_at: Some(trust_ir::InlinedAt {
            span: trust_ir::SourceSpan {
                file: 0,
                line: 1,
                col: 1,
            },
            callee: "inlined_callee".into(),
        }),
    }]);
    assert_refuses_each_side(
        &plain,
        &inlined,
        &format!(
            "function #{} lexical scope #0",
            inlined.functions[0].id.index()
        ),
        "a ScopeData.inlined_at inlining chain link ahead of its binary carrier",
    );
    let mut claimed = plain.clone();
    claimed.completeness = Some(trust_ir::ModuleCompleteness::Complete);
    assert_refuses_each_side(
        &plain,
        &claimed,
        "module",
        "a Module.completeness claim ahead of its binary carrier",
    );
    let mut bound = plain.clone();
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
    // trust-ir binary v61 (`certificate-binding`) writes the binding, so the
    // writer's preflight no longer refuses it and neither does this one: the
    // retired fourth diagnostic must not outlive the carrier gap it named.
    assert_eq!(bound.wire_image_refusal(), None);
    assert!(wire_image_blocker("original", &bound).is_none());
    assert!(wire_image_blocker("lowered", &bound).is_none());
}

#[test]
fn site_diagnostics_use_actual_ids_and_refuse_ambiguous_or_unknown_coordinates() {
    let mut module = fixture();
    module.functions[0].id = trust_ir::FuncId::new(60_002);
    module.functions[0].blocks[0].id = trust_ir::BlockId::new(7);
    let site = WireNodeSite {
        function: 60_002,
        block: 7,
        index: 0,
    };
    let gap = |site| BinaryProjectionError::ConstructAheadOfWireTag {
        construct: "diagnostic-only future instruction gap",
        site,
    };
    // All current instructions have wire tags. This is a mapper-only control
    // using real retained node coordinates, not a fabricated admission case.
    let mapped = map_wire_refusal("original", &module, gap(Some(site)));
    assert_eq!(
        mapped.location,
        format!("function '{}' bb7 #0", module.functions[0].name)
    );
    assert_eq!(mapped.construct, "diagnostic-only future instruction gap");
    let mut ambiguous_block = module.clone();
    let duplicate_block = ambiguous_block.functions[0].blocks[0].clone();
    ambiguous_block.functions[0].blocks.push(duplicate_block);
    assert_eq!(
        map_wire_refusal("original", &ambiguous_block, gap(Some(site))).location,
        "function #60002 bb7 #0"
    );
    let mut duplicate = module.functions[0].clone();
    duplicate.name.push_str("_ambiguous");
    // Duplicate FuncIds stay ambiguous even when only one has this block.
    duplicate.blocks[0].id = trust_ir::BlockId::new(999);
    module.functions.push(duplicate);
    assert_eq!(
        map_wire_refusal("lowered", &module, gap(Some(site))).location,
        "function #60002 bb7 #0"
    );
    assert_eq!(
        map_wire_refusal(
            "original",
            &module,
            gap(Some(WireNodeSite {
                index: usize::MAX,
                ..site
            }))
        )
        .location,
        format!("function #60002 bb7 #{}", usize::MAX)
    );
    let unsited = gap(None);
    let mapped = map_wire_refusal("original", &module, unsited.clone());
    assert_eq!(mapped.location, "module");
    assert_eq!(mapped.construct, unsited.to_string());
    let additive = BinaryProjectionError::DialectTypeRequiresV39;
    let mapped = map_wire_refusal("lowered", &module, additive.clone());
    assert_eq!(mapped.side, "lowered");
    assert_eq!(mapped.location, "module");
    assert_eq!(mapped.construct, additive.to_string());
}

#[test]
fn valid_streamed_pair_identity_matches_independent_binary_oracle_and_exact_borrows() {
    let plain = fixture();
    let cloned = plain.clone();
    let (recorded, _) = with_unused_abi();
    for (original, lowered) in [
        (&plain, &plain),
        (&plain, &cloned),
        (&plain, &recorded),
        (&recorded, &plain),
        (&recorded, &recorded),
    ] {
        assert!(wire_image_blocker("original", original).is_none());
        assert!(wire_image_blocker("lowered", lowered).is_none());
        let captured = FunctionSourceModules::capture(original, lowered).unwrap();
        assert!(std::ptr::eq(captured.original(), original));
        assert!(std::ptr::eq(captured.lowered(), lowered));
        assert_eq!(*captured.digest(), binary_pair_digest(original, lowered));
    }
    assert_eq!(
        FunctionSourceModules::capture(&plain, &plain)
            .unwrap()
            .digest(),
        FunctionSourceModules::capture(&plain, &cloned)
            .unwrap()
            .digest()
    );
    assert_ne!(
        binary_pair_digest(&plain, &recorded),
        binary_pair_digest(&recorded, &plain)
    );
}

/// Genuine normal allocation, never an unsafe manufactured Vec/slice. The
/// 64-bit host must reserve 4 GiB virtual space; lazy zero-fill depends on its
/// allocator. Collection/checking does not touch payload pages. An allocator
/// that eagerly zeros may use that much RSS, so this control is not a portable
/// memory-cost claim. No binary serialization/digest is attempted on `big`.
#[cfg(target_pointer_width = "64")]
#[test]
fn actual_overcount_refuses_each_endpoint_before_reading_or_hashing_bytes() {
    let plain = fixture();
    let mut big = plain.clone();
    let count = u64::from(u32::MAX) + 1;
    big.globals.push(trust_ir::Global {
        name: "custody-count-limit".into(),
        ty: Ty::U8,
        mutable: false,
        initializer: Some(trust_ir::Constant::Bytes {
            data: vec![0; usize::try_from(count).unwrap()],
            utf8: false,
        }),
        linkage: trust_ir::Linkage::Internal,
        tls: None,
        align: None,
        section: None,
        visibility: trust_ir::Visibility::Default,
        retained: false,
    });
    let refusal = BinaryProjectionError::CountExceedsFormat {
        what: "Constant::Bytes data",
        count,
    };
    assert_eq!(big.wire_image_refusal(), Some(refusal.clone()));
    assert_refuses_each_side(
        &plain,
        &big,
        "module field 'Constant::Bytes data'",
        &refusal.to_string(),
    );
}
