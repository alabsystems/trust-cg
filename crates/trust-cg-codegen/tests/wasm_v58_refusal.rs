// trust-cg-codegen/tests/wasm_v58_refusal.rs — trust-ir v58 nominal type
// origins and declared closure layouts on both wasm32 lanes.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Wire v58 adds `StructDef.origin` / `EnumDef.origin` (a producer's nominal
//! key) and `Module.closure_layouts` (a declared closure frame, which gives
//! `Ty::Closure` a byte size in trust-ir's layout engine). On the
//! closed-module and the object lane, at O0 and at O2 (where the mid-end
//! runs), through the lane's real admission order:
//!
//! * a module declaring a closure layout is refused by name
//!   (`DeclaredClosureLayoutUnsupported`, the shared floor of OD-145), so the
//!   mid-end's passes, which read a sized type as plain bytes, never see one;
//!   the same module without the row compiles;
//! * two definitions claiming one nominal origin are refused by name
//!   (`TypeOriginConflict`), unused and identically shaped ones included;
//! * distinct origins are inert: the bytes equal the unkeyed module's.
//!
//! Test-rung evidence about admission; no closure lowering is claimed.

use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::wasm::{
    self, WasmFuncImportPolicy, WasmLowerError, WasmMemoryPolicy, WasmModulePolicy,
};
use trust_ir::ty::{FieldDef, StructDef, StructRepr, TypeOrigin};
use trust_ir::{ClosureLayoutDescriptor, ClosureTy, ClosureTyId, Module, StructId, Ty};

const PROGRAM: &str = "module \"v58\"\ntarget \"wasm32-unknown-unknown\" 4 little\n\n\
type ty.0 = i32\n\n\
functy.0 = (i32, i32) -> (i32)\n\n\
fn @f(functy.0) {\n\
bb0(%0: i32, %1: i32):\n\
\x20   %2 = alloca [ty.0 x 2], align 4\n\
\x20   store i32 %0, ptr %2\n\
\x20   %3 = const usize 4\n\
\x20   %4 = gep u8, ptr %2, %3\n\
\x20   store i32 %1, ptr %4\n\
\x20   %5 = load i32, ptr %2\n\
\x20   %6 = load i32, ptr %4\n\
\x20   %7 = add i32 %5, %6\n\
\x20   ret %7\n\
}\n";

fn program() -> Module {
    trust_ir::parser::parse_module(PROGRAM).unwrap_or_else(|e| panic!("parse: {e}"))
}

fn policy() -> WasmModulePolicy {
    WasmModulePolicy {
        memory: WasmMemoryPolicy::Owned {
            pages: 2,
            export: Some("memory".to_string()),
        },
        func_imports: WasmFuncImportPolicy::FromModule("host".to_string()),
        ..WasmModulePolicy::closed()
    }
}

type Lane = fn(&Module, OptLevel) -> Result<Vec<u8>, WasmLowerError>;

fn closed_lane(m: &Module, level: OptLevel) -> Result<Vec<u8>, WasmLowerError> {
    wasm::compile_module_with_evidence_policy_license_optimized(
        m,
        &policy(),
        &permit_unlicensed(),
        level,
    )
    .map(|(bytes, _)| bytes)
}

fn object_lane(m: &Module, level: OptLevel) -> Result<Vec<u8>, WasmLowerError> {
    wasm::compile_object_with_license_optimized(m, &permit_unlicensed(), level)
}

const LANES: &[(&str, Lane)] = &[("wasm-module", closed_lane), ("wasm-object", object_lane)];
const LEVELS: &[OptLevel] = &[OptLevel::O0, OptLevel::O2];

/// `program()` with a closure type over `(u64, u8)` in its table.
fn with_closure_type() -> Module {
    let mut m = program();
    let sig = m.functions[0].ty;
    m.closure_types.push(ClosureTy {
        func: sig,
        captures: vec![Ty::U64, Ty::U8],
    });
    m
}

#[test]
fn a_declared_closure_layout_is_refused_by_name_on_both_wasm_lanes_at_every_level() {
    let control = with_closure_type();
    let mut declared = control.clone();
    declared.closure_layouts.push(ClosureLayoutDescriptor {
        origin: None,
        closure: ClosureTyId::new(0),
        size: 16,
        align: 8,
        capture_offsets: vec![8, 0],
    });
    declared
        .validate_closure_layouts()
        .expect("the declared frame is coherent");
    assert!(
        declared
            .ty_layout_shape(&Ty::Closure(ClosureTyId::new(0)))
            .is_ok_and(|shape| shape.size_bytes() == Some(16)),
        "the premise: a declared frame gives the closure a size"
    );
    let mut cells = 0;
    for (lane, compile) in LANES {
        for &level in LEVELS {
            compile(&control, level)
                .unwrap_or_else(|e| panic!("{lane} {level:?}: the control is refused: {e}"));
            let text = compile(&declared, level)
                .expect_err(&format!(
                    "{lane} {level:?} compiled a declared closure layout"
                ))
                .to_string();
            assert!(
                text.contains("declared closure layout(s) (trust-ir v58)"),
                "{lane} {level:?}: refused for another reason: {text}"
            );
            cells += 1;
        }
    }
    assert_eq!(cells, LANES.len() * LEVELS.len());
}

fn keyed(id: u32, origin: Option<TypeOrigin>) -> StructDef {
    StructDef {
        id: StructId::new(id),
        name: format!("Keyed{id}"),
        fields: vec![FieldDef {
            name: "value".into(),
            ty: Ty::I32,
            offset: Some(0),
        }],
        size: Some(4),
        align: Some(4),
        repr: StructRepr::C,
        origin,
    }
}

fn origin(byte: u8) -> TypeOrigin {
    TypeOrigin::Rust {
        stable_crate_id: 7,
        def_path_hash: [8; 16],
        args_digest: trust_ir::proof::ProofDigest::sha256([byte; 32]),
    }
}

#[test]
fn nominal_origins_split_or_refuse_and_change_no_byte_on_both_wasm_lanes() {
    let with = |a: Option<TypeOrigin>, b: Option<TypeOrigin>| {
        let mut m = program();
        m.structs = vec![keyed(0, a), keyed(1, b)];
        m
    };
    let unkeyed = with(None, None);
    let distinct = with(Some(origin(9)), Some(origin(10)));
    let duplicate = with(Some(origin(9)), Some(origin(9)));
    for (lane, compile) in LANES {
        for &level in LEVELS {
            let base = compile(&unkeyed, level)
                .unwrap_or_else(|e| panic!("{lane} {level:?}: the unkeyed module: {e}"));
            let keyed = compile(&distinct, level)
                .unwrap_or_else(|e| panic!("{lane} {level:?}: distinct origins: {e}"));
            assert_eq!(base, keyed, "{lane} {level:?}: an origin changed a byte");
            let text = compile(&duplicate, level)
                .expect_err(&format!("{lane} {level:?} compiled a duplicate origin"))
                .to_string();
            assert!(
                text.contains("nominal type origin"),
                "{lane} {level:?}: refused for another reason: {text}"
            );
        }
    }
}

/// These hand-built backend fixtures carry no source proof. The explicit
/// legacy policy exercises lowering without changing production admission.
fn permit_unlicensed() -> trust_cg_codegen::CodegenLicensePolicy {
    trust_cg_codegen::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_codegen::UnlicensedBodyPolicy::Permit)
}
