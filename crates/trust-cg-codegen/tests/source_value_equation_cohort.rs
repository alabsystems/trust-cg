// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The pinned original-source equation API in the default native CG consumer.
//! Actual producer DATA is checked independently; acceptance grants no body
//! license, backend certificate, ABI, SDK or emitted-code assurance.

use trust_ir::proof::decode_clean_expr_v1;
use trust_ir::{FuncId, Module};
use trust_ir_build::clean_kernel::{Declaration, Environment, Expr, ExprKind, Name};

struct DefinitionData {
    name: &'static [u8],
    type_: &'static [u8],
    value: &'static [u8],
    is_reducible: bool,
}
struct Fixture {
    expected_source: &'static str,
    module: &'static [u8],
    definitions: Vec<DefinitionData>,
    theorem_name: &'static [u8],
    theorem_type: &'static [u8],
    theorem_value: &'static [u8],
    original_source_digest: &'static [u8],
}

fn expression(bytes: &[u8]) -> Expr {
    decode_clean_expr_v1(bytes).expect("bounded canonical Expr carrier")
}
fn name(bytes: &[u8]) -> Name {
    let e = expression(bytes);
    let ExprKind::Const(name, levels) = e.kind() else {
        panic!("fixture name is not a typed kernel Const")
    };
    assert!(levels.is_empty());
    name.clone()
}
fn load(f: &Fixture) -> (Module, Environment, Name, Declaration, FuncId) {
    let module = trust_ir::binary::deserialize_module(f.module)
        .expect("the complete actual producer module decodes");
    let mut original_environment = Environment::with_prelude();
    for d in &f.definitions {
        original_environment
            .add_decl(Declaration::Definition {
                name: name(d.name),
                level_params: vec![],
                type_: expression(d.type_),
                value: expression(d.value),
                is_reducible: d.is_reducible,
            })
            .expect("independently kernel-check actual original definition data");
    }
    // These expected names are hardcoded caller-side mappings, not read from
    // the proposed theorem. The source declarations are separate env inputs.
    let source = Name::from_string(f.expected_source);
    let function = module
        .functions
        .iter()
        .find(|function| function.name == f.expected_source)
        .expect("the externally selected actual function")
        .id;
    assert_eq!(
        original_environment
            .closure_digest(&source)
            .unwrap()
            .as_slice(),
        f.original_source_digest,
        "the reconstructed actual custom source closure must match the retained original data"
    );
    let proposed = Declaration::Theorem {
        name: name(f.theorem_name),
        level_params: vec![],
        type_: expression(f.theorem_type),
        value: expression(f.theorem_value),
    };
    (module, original_environment, source, proposed, function)
}

#[path = "source_value_equation_cohort/conditional.rs"]
mod conditional;
