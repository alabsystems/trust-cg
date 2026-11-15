// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0
//! Ordinary independent two-function source, actual framed BL caller, and an
//! opaque entry retaining its real private writable stack through invocation.
#![cfg(all(feature = "verify", target_arch = "aarch64", target_os = "macos"))]

use cg::jit::entry_stack::{EntryStackError, OwnedEntryStack};
use trust_cg_codegen as cg;
#[path = "common/defined_call_fixture.rs"]
mod fixture;

fn manifest() -> cg::jit_contract::ArtifactManifestV1 {
    use cg::jit_contract::*;
    let target = TargetDescriptor::for_trust_cg_host_jit();
    let abi = AbiDescriptor::for_trust_cg_target_os(
        cg::target::Target::Aarch64,
        target.operating_system.clone(),
    );
    let layout = LayoutManifest::lp64(Endianness::Little, 16);
    let policy = ProofPolicy::require_certificates(std::iter::empty::<String>());
    let invalidation = InvalidationKey::new(
        "source:DefinedCalls.entry",
        "sealed-core",
        target.checksum(),
        abi.checksum(),
        layout.checksum(),
        policy.checksum(),
        1,
    );
    let mut manifest = ArtifactManifestV1::new(
        "source-bound-core-peer-entry",
        JitArtifactKind::ExecutableMemory,
        target,
        abi,
        layout,
        invalidation,
        policy,
    );
    manifest.symbols.push(ArtifactSymbol {
        name: "entry".into(),
        visibility: SymbolVisibility::Exported,
        signature: SymbolSignature::extern_c(vec![], vec![AbiValue::new(AbiValueKind::I64)]),
        offset_bytes: None,
        checksum: None,
    });
    manifest
}

#[test]
fn unchanged_source_framed_peer_executes_only_with_owned_storage() {
    let (module, target, _) = fixture::certified(42).unwrap();
    let source_digest = module
        .function_body_digest(trust_ir::FuncId::new(1))
        .unwrap();
    let conditional = fixture::qualified_plan(module, target)
        .compile_for_owned_peer_entry("entry")
        .expect("same original request, genuine callee, exact frame and final BL replay");
    assert_eq!(conditional.source_function(), trust_ir::FuncId::new(1));
    assert_eq!(conditional.required_private_stack_bytes(), 16);
    let diagnostic = conditional.diagnostic_report();
    assert_eq!(diagnostic.genuinely_verified_count(), 0);
    assert!(!diagnostic.emitted_opcode_inventory().is_promotable());
    assert!(
        diagnostic
            .instructions
            .iter()
            .all(|row| row.result.is_unverified())
    );
    let mut insufficient = OwnedEntryStack::allocate(15).unwrap();
    assert!(matches!(
        conditional.check_entry_storage(&mut insufficient),
        Err(EntryStackError::Insufficient {
            required: 16,
            available: 0
        })
    ));
    assert_eq!(
        conditional.diagnostic_report().genuinely_verified_count(),
        0
    );
    let stack = OwnedEntryStack::allocate(65_536).unwrap();
    let (mut entry, installed_manifest) = conditional
        .install_owned_stack(
            stack,
            manifest(),
            cg::compile_service::CompileGeneration::new(1),
        )
        .expect("actual storage discharge, existing final-image publisher and installed replay");
    assert_eq!(entry.source_function(), trust_ir::FuncId::new(1));
    assert_eq!(entry.required_private_stack_bytes(), 16);
    assert!(
        installed_manifest
            .symbols
            .iter()
            .any(|symbol| symbol.name == "entry" && symbol.offset_bytes.is_none())
    );
    assert_eq!(entry.invoke0_u64().unwrap(), 42);
    assert_eq!(entry.invoke0_u64().unwrap(), 42);
    println!(
        "CORE_ORDINARY_SOURCE_FRAMED_PEER_NATIVE_RESULT=42 frame_bytes=16 source_body={source_digest}"
    );
}
