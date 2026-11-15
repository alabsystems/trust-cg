// trust-cg-codegen/tests/wasm_refine_representation.rs - refined values on
// both wasm32 lanes and through the trust-ir mid-end.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! The native adapter resolves a `Ty::Refine` to its representation type at
//! ABI and refusal boundaries (narrow argument and return extension, the
//! volatile `i128` refusal) and the shared codegen admission refuses a
//! refined `gep` index (`GepIndexNotInteger`). The wasm32 lanes lay out no
//! refined value: a refined parameter, result, call argument or volatile
//! access has no wasm32 carrier there and is refused BY NAME (the error names
//! the `Refine` type), on the closed-module and the object lane at O0-O3,
//! while the same module without the refinement compiles. The refined `gep`
//! index is refused by the shared admission before anything else.
//!
//! The trust-ir mid-end (`trust_cg_irmid`, wasm32 profile, O2 configuration)
//! models no refinement: it may move a refined value only where its type is
//! unchanged (a forwarded copy, a spliced call), so every volatile access is
//! kept, and a load whose type differs from its slot's store across a
//! refinement (`store i8` then `load refine<i8>`, and the reverse) is never
//! forwarded or scalar-replaced away. Its output gains no trust-ir
//! validation finding.
//!
//! Test-rung evidence about refusals and mid-end barriers; no lowering of a
//! refined value on wasm32 is claimed.

use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::wasm::{self, WasmLowerError};
use trust_cg_irmid::{MidConfig, optimize_module};
use trust_ir::{Function, Inst, Module, Pred, PredId, Ty, TyId};

type Lane = fn(&Module, OptLevel) -> Result<(), WasmLowerError>;

fn closed_lane(module: &Module, level: OptLevel) -> Result<(), WasmLowerError> {
    wasm::compile_module_with_evidence_policy_license_optimized(
        module,
        &wasm::WasmModulePolicy::closed(),
        &permit_unlicensed(),
        level,
    )
    .map(drop)
}

fn object_lane(module: &Module, level: OptLevel) -> Result<(), WasmLowerError> {
    wasm::compile_object_with_license_optimized(module, &permit_unlicensed(), level).map(drop)
}

const LANES: &[(&str, Lane)] = &[("wasm-module", closed_lane), ("wasm-object", object_lane)];
const LEVELS: &[OptLevel] = &[OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3];

/// The bases a refinement wraps here: the four the native lanes extend at an
/// ABI boundary, and one they pass unextended.
const BASES: &[Ty] = &[Ty::I8, Ty::U8, Ty::I16, Ty::U16, Ty::I32];

/// A wasm32 module whose `ty.0` is `base` and `pred.0` is `top`, with the
/// function types `sigs` (in order), and the functions `body` (trust-ir text,
/// `R` standing for `refine<ty.0, pred.0>` when `refined`, for `base`
/// otherwise; `B` always for `base`).
fn module(name: &str, base: &Ty, refined: bool, sigs: &[(&[&str], &[&str])], body: &str) -> Module {
    let mut header = Module::new(name);
    header.target_info = Some(wasm::wasm32_target_info());
    assert_eq!(
        header
            .add_type(base.clone())
            .expect("Module::add_type: test fixture"),
        TyId::new(0)
    );
    assert_eq!(
        header
            .intern_pred(Pred::Top)
            .expect("Module::intern_pred: test fixture"),
        Some(PredId::new(0))
    );
    let r = if refined {
        "refine<ty.0, pred.0>".to_string()
    } else {
        base.to_string()
    };
    let b = base.to_string();
    let spell = |t: &str| match t {
        "R" => r.clone(),
        "B" => b.clone(),
        other => other.to_string(),
    };
    let mut text = header.to_string();
    for (index, (params, returns)) in sigs.iter().enumerate() {
        let params: Vec<String> = params.iter().map(|t| spell(t)).collect();
        let returns: Vec<String> = returns.iter().map(|t| spell(t)).collect();
        text.push_str(&format!(
            "\nfuncty.{index} = ({}) -> ({})\n",
            params.join(", "),
            returns.join(", ")
        ));
    }
    text.push('\n');
    text.push_str(&body.replace("{R}", &r).replace("{B}", &b));
    let parsed = trust_ir::parser::parse_module(&text)
        .unwrap_or_else(|e| panic!("{name}: the test module does not parse: {e}\n{text}"));
    if refined {
        assert!(
            mentions_refine(&parsed),
            "{name}: the refined module carries no refinement"
        );
    }
    parsed
}

fn mentions_refine(module: &Module) -> bool {
    module
        .func_types
        .iter()
        .flat_map(|ft| ft.params.iter().chain(&ft.returns))
        .chain(
            module
                .functions
                .iter()
                .flat_map(|f| &f.blocks)
                .flat_map(|b| b.params.iter().map(|(_, ty)| ty)),
        )
        .any(|ty| matches!(ty, Ty::Refine(..)))
        || module
            .functions
            .iter()
            .flat_map(|f| &f.blocks)
            .flat_map(|b| &b.body)
            .any(|n| matches!(&n.inst, Inst::Load { ty, .. } | Inst::Store { ty, .. } if matches!(ty, Ty::Refine(..))))
}

/// A refined identity: the refined parameter is the refined result.
fn identity(base: &Ty, refined: bool) -> Module {
    module(
        "refine_identity",
        base,
        refined,
        &[(&["R"], &["R"])],
        "fn @probe(functy.0) {\nbb0(%0: {R}):\n    ret %0\n}\n",
    )
}

/// A refined value passed to, and returned by, a module-local callee.
fn call(base: &Ty, refined: bool) -> Module {
    module(
        "refine_call",
        base,
        refined,
        &[(&["R"], &["R"])],
        "internal fn @observe(functy.0) {\nbb0(%0: {R}):\n    ret %0\n}\n\n\
         fn @caller(functy.0) {\nbb0(%0: {R}):\n    %1 = call @func.0(%0)\n    \
         %2 = call @func.0(%1)\n    ret %2\n}\n",
    )
}

/// A volatile store and reload of a refined value through a pointer.
fn volatile(base: &Ty, refined: bool) -> Module {
    module(
        "refine_volatile",
        base,
        refined,
        &[(&["ptr", "R"], &["R"])],
        "fn @vol(functy.0) {\nbb0(%0: ptr, %1: {R}):\n    volatile store {R} %1, ptr %0\n    \
         %2 = volatile load {R}, ptr %0\n    ret %2\n}\n",
    )
}

/// A frame slot written at the base type and read at the refined one, and
/// the reverse: the mid-end must not forward or scalar-replace across the
/// type change.
fn launder(base: &Ty, refined: bool) -> Module {
    module(
        "refine_launder",
        base,
        refined,
        &[(&["B"], &["R"]), (&["R"], &["B"])],
        "fn @into(functy.0) {\nbb0(%0: {B}):\n    %1 = alloca {B}\n    store {B} %0, ptr %1\n    \
         %2 = load {R}, ptr %1\n    ret %2\n}\n\n\
         fn @out(functy.1) {\nbb0(%0: {R}):\n    %1 = alloca {B}\n    store {R} %0, ptr %1\n    \
         %2 = load {B}, ptr %1\n    ret %2\n}\n",
    )
}

/// A refined `gep` index.
fn gep_index(refined: bool) -> Module {
    module(
        "refine_gep_index",
        &Ty::I32,
        refined,
        &[(&["ptr", "R"], &["ptr"])],
        "fn @index(functy.0) {\nbb0(%0: ptr, %1: {R}):\n    %2 = gep u8, ptr %0, %1\n    \
         ret %2\n}\n",
    )
}

type Build = fn(&Ty, bool) -> Module;

const BUILDS: &[(&str, Build)] = &[
    ("identity", identity),
    ("call", call),
    ("volatile", volatile),
    ("launder", launder),
];

fn expect_refused(label: &str, module: &Module, names: &[&str]) {
    for (lane, compile) in LANES {
        for &level in LEVELS {
            let error = compile(module, level).expect_err(&format!(
                "{lane} {level:?} {label}: a refined value compiled"
            ));
            let text = error.to_string();
            assert!(
                names.iter().any(|n| text.contains(n)),
                "{lane} {level:?} {label}: refused without naming {names:?}: {text}"
            );
            assert!(
                !matches!(error, WasmLowerError::CodegenLicense(_)),
                "{lane} {level:?} {label}: the license layer refused: {text}"
            );
        }
    }
}

fn expect_compiled(label: &str, module: &Module) {
    for (lane, compile) in LANES {
        for &level in LEVELS {
            compile(module, level)
                .unwrap_or_else(|e| panic!("{lane} {level:?} {label}: the control refused: {e}"));
        }
    }
}

#[test]
fn refined_values_are_refused_by_name_on_both_wasm_lanes_at_every_level() {
    for base in BASES {
        for (name, build) in BUILDS {
            let label = format!("{name} {base}");
            let bare = build(base, false);
            let refined = build(base, true);
            assert!(
                trust_ir_build::validate_module(&refined).is_empty(),
                "{label}: {:?}",
                trust_ir_build::validate_module(&refined)
            );
            expect_compiled(&label, &bare);
            expect_refused(&label, &refined, &["Refine"]);
        }
    }
    // A refined 128-bit volatile access: the native adapter refuses it as a
    // split volatile event; here it is refused as a refined value too.
    expect_refused("volatile i128", &volatile(&Ty::I128, true), &["Refine"]);
}

#[test]
fn a_refined_gep_index_is_refused_by_the_shared_admission_on_both_lanes() {
    expect_compiled("gep index i32", &gep_index(false));
    let refined = gep_index(true);
    assert!(
        trust_ir_build::validate_module(&refined)
            .iter()
            .any(|e| matches!(
                e,
                trust_ir_build::ValidationError::GepIndexNotInteger { .. }
            )),
        "the pinned validator no longer reports the refined index"
    );
    expect_refused("gep index", &refined, &["gep index must be integer"]);
    for (lane, compile) in LANES {
        for &level in LEVELS {
            let error = compile(&refined, level).unwrap_err();
            assert!(
                matches!(error, WasmLowerError::CodegenAdmission(_)),
                "{lane} {level:?}: the admission did not refuse first: {error:?}"
            );
        }
    }
}

/// Every volatile access of `func`, in order.
fn volatile_accesses(func: &Function) -> Vec<Inst> {
    func.blocks
        .iter()
        .flat_map(|b| &b.body)
        .filter(|n| {
            matches!(
                n.inst,
                Inst::Load { volatile: true, .. } | Inst::Store { volatile: true, .. }
            )
        })
        .map(|n| n.inst.clone())
        .collect()
}

/// Every load of `func` at a type its slot's stores do not use, in order.
fn type_changing_loads(func: &Function) -> Vec<Inst> {
    let stored: Vec<&Ty> = func
        .blocks
        .iter()
        .flat_map(|b| &b.body)
        .filter_map(|n| match &n.inst {
            Inst::Store { ty, .. } => Some(ty),
            _ => None,
        })
        .collect();
    func.blocks
        .iter()
        .flat_map(|b| &b.body)
        .filter(|n| matches!(&n.inst, Inst::Load { ty, .. } if !stored.contains(&ty)))
        .map(|n| n.inst.clone())
        .collect()
}

#[test]
fn the_mid_end_keeps_every_refined_access_it_does_not_model() {
    let config = MidConfig::wasm32();
    let mut launders = 0;
    for base in BASES.iter().chain([&Ty::I128]) {
        let modules: Vec<(String, Module)> = BUILDS
            .iter()
            .filter(|(name, _)| *base != Ty::I128 || *name == "volatile")
            .map(|(name, build)| (format!("{name} {base}"), build(base, true)))
            .chain((*base == Ty::I32).then(|| ("gep index".to_string(), gep_index(true))))
            .collect();
        for (label, module) in modules {
            let (optimized, report) = optimize_module(&module, &config);
            assert!(
                trust_ir_build::validate_module(&optimized).len()
                    <= trust_ir_build::validate_module(&module).len(),
                "{label}: the mid-end added a validation finding: {:?}",
                trust_ir_build::validate_module(&optimized)
            );
            assert_eq!(
                optimized.func_types, module.func_types,
                "{label}: signatures"
            );
            for (before, after) in module.functions.iter().zip(&optimized.functions) {
                assert_eq!(before.name, after.name, "{label}");
                assert_eq!(
                    volatile_accesses(before),
                    volatile_accesses(after),
                    "{label} {}: a volatile access moved or went: {report:?}",
                    before.name
                );
                let changing = type_changing_loads(before);
                if !changing.is_empty() {
                    launders += 1;
                    assert_eq!(
                        changing,
                        type_changing_loads(after),
                        "{label} {}: a load across the refinement was rewritten: {report:?}",
                        before.name
                    );
                }
                assert_eq!(
                    before.blocks[0].params, after.blocks[0].params,
                    "{label} {}: entry parameters",
                    before.name
                );
            }
            // Through both lanes after the mid-end at O2: still refused by
            // name (the lanes lower the input whenever the mid-end changed it).
            for (lane, compile) in LANES {
                let error = compile(&module, OptLevel::O2)
                    .expect_err(&format!("{lane} {label}: compiled at O2"));
                let text = error.to_string();
                assert!(
                    text.contains("Refine") || text.contains("gep index must be integer"),
                    "{lane} {label}: {text}"
                );
            }
        }
    }
    assert_eq!(launders, 2 * BASES.len(), "every launder row was checked");
    // Control: without the refinement the same slots are forwarded away, so
    // the rows above exercise a pass that would otherwise rewrite them.
    for base in BASES {
        let (optimized, report) = optimize_module(&launder(base, false), &config);
        for func in &optimized.functions {
            assert!(
                !func
                    .blocks
                    .iter()
                    .flat_map(|b| &b.body)
                    .any(|n| matches!(n.inst, Inst::Load { .. })),
                "{base} {}: the unrefined slot was not forwarded: {report:?}",
                func.name
            );
        }
    }
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes (or is refused) because the license silently refused it.
fn permit_unlicensed() -> trust_cg_codegen::CodegenLicensePolicy {
    trust_cg_codegen::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_codegen::UnlicensedBodyPolicy::Permit)
}
