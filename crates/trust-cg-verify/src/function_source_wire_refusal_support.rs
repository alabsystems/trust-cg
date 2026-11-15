// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Actual retained capture fixtures and independent custody digest oracle.
//! These controls establish encoding/identity behavior, never proof authority.

use super::*;
use sha2::{Digest, Sha256};
use trust_ir::signature_abi::{AbiArgument, AbiFrontend, AbiPassMode, AbiTarget, SignatureAbi};

#[derive(serde::Deserialize)]
struct Capture {
    module: Module,
}

pub(super) fn fixture() -> Module {
    let mut captures: Vec<Capture> =
        serde_json::from_str(include_str!("source_bound_cell_sources.json")).unwrap();
    captures.remove(0).module
}

/// The descriptor is initially structurally consistent with the actual
/// retained target and an appended, unreferenced empty signature. None of
/// these producer records authenticates a physical ABI or a native caller.
pub(super) fn with_unused_abi() -> (Module, usize) {
    let mut module = fixture();
    let target = module.target_info.as_ref().unwrap();
    let mut signature = trust_ir::FuncTy::unrecorded(vec![], vec![], false);
    signature.abi = Some(SignatureAbi {
        target: AbiTarget {
            triple: target.triple.clone(),
            data_layout: "e-m:e-i64:64-i128:128-n32:64-S128".into(),
            abi: target.abi.clone().unwrap_or_else(|| "aapcs".into()),
            cpu: "generic".into(),
            features: vec![],
            target_spec: "function-source-wire-control-v1".into(),
            pointer_bytes: target.pointer_size.try_into().unwrap(),
            little_endian: target.endianness == trust_ir::Endianness::Little,
        },
        frontend: AbiFrontend {
            name: "function-source-wire-control".into(),
            revision: "v1".into(),
        },
        convention: "aapcs".into(),
        lowered_convention: trust_ir::CallingConv::C,
        source_abi: "C".into(),
        can_unwind: true,
        variadic: false,
        fixed_count: 0,
        arguments: vec![],
        result: AbiArgument {
            size: 0,
            align: 1,
            mode: AbiPassMode::Ignore,
            bindings: vec![],
        },
    });
    let abi = signature.abi.as_ref().unwrap();
    abi.validate(&signature).unwrap();
    abi.validate_target(module.target_info.as_ref()).unwrap();
    let row = module.func_types.len();
    assert!(
        module
            .functions
            .iter()
            .all(|function| function.ty.index() as usize != row)
    );
    module.func_types.push(signature);
    assert_eq!(module.wire_image_refusal(), None);
    (module, row)
}

pub(super) fn assert_refuses_each_side(
    plain: &Module,
    unencodable: &Module,
    location: &str,
    construct: &str,
) {
    for (original, lowered, side) in [
        (unencodable, plain, "original"),
        (plain, unencodable, "lowered"),
        (unencodable, unencodable, "original"),
    ] {
        // Never format a whole unexpectedly accepted module: the overcount
        // control has a genuine 4 GiB allocation, not a fabricated slice.
        let refusal = match FunctionSourceModules::capture(original, lowered) {
            Err(refusal) => refusal,
            Ok(_) => panic!("a module without a wire image received custody identity"),
        };
        assert_eq!(refusal.side, side);
        assert_eq!(refusal.location, location);
        assert_eq!(refusal.construct, construct);
    }
}

/// Separate materialized-binary path, used only on the small valid fixtures.
/// The production path must remain its existing streaming plan, borrow-bound
/// endpoints and the exact historical prefix strings/order.
pub(super) fn binary_pair_digest(original: &Module, lowered: &Module) -> [u8; 32] {
    let endpoint = |module: &Module| -> [u8; 32] {
        let bytes =
            trust_ir::binary::serialize_module(module).expect("serialize_module: test fixture");
        let mut hash = Sha256::new();
        hash.update(b"trust-cg.function-source-module.v1\0");
        hash.update(bytes);
        hash.finalize().into()
    };
    let mut hash = Sha256::new();
    hash.update(b"trust-cg.function-source-modules.v1\0");
    hash.update(endpoint(original));
    hash.update(endpoint(lowered));
    hash.finalize().into()
}
