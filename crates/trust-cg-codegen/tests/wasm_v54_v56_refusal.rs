// trust-cg-codegen/tests/wasm_v54_v56_refusal.rs — the trust-ir v54 panic
// sites and the v55/v56 unwinding twins on both wasm32 lanes.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! The vendored trust-ir conformance goldens `assert_panic_site`,
//! `assert_invoke` (wire v54), `drop_glue` (v55) and `unwind_twins` (v56),
//! read by trust-cg's own reader and retargeted to wasm32, are refused BY
//! NAME on the closed-module and the object lane, at O0 and at O2 (where the
//! P3 local emission runs), through the lane's real admission order: the
//! codegen admission and the caller's license first, then the shared floor.
//!
//! Each golden wears `body_gate: ungated`, which the license layer refuses
//! before any body is read. This target re-licenses every bodied function to
//! a test authority it recognizes FOR THIS RUN (a test-time decision that
//! licenses nothing in production) so the refusal reached is the
//! construct's, and asserts no refusal names that authority. The ungated
//! originals are pinned too, so the license layer still decides first.
//!
//! The per-function entry ([`wasm::lower_function`]) is driven with a
//! function that is not its module's own copy, so the module floor never sees
//! the construct: the lane's backstops (`reject_unwired_eh_instructions` and
//! the `Inst::Assert { site: Some(_) }` arm) must name it themselves.
//!
//! Test-rung evidence about refusals; no lowering of a panic site, a drop or
//! an unwind edge is claimed.

use std::path::{Path, PathBuf};

use trust_cg_codegen::pipeline::{self, OptLevel};
use trust_cg_codegen::wasm::{self, WasmFunctionEnv, WasmLowerError, WasmModule};
use trust_cg_lower::CodegenLicensePolicy;
use trust_ir::{BodyGate, Inst, Module};

/// A gate authority no consumer recognizes by default.
const TEST_AUTHORITY: &str = "trust-cg-test-wasm-v54-v56";

/// The shared floor's refusal of a sited check whose kind is `Unspecified`:
/// the check has no Rust panic identity, so no lane can deliver it
/// (`AdapterError::AssertPanicUnsupported`, the refusal every native lane
/// gives it too). `assert_panic_site`'s `resumed` carries one.
const UNSPECIFIED_SITED_CHECK: &str = "[TCG-ASSERT-PANIC] function `resumed` bb0 instruction 0: \
     Inst::Assert panic Unspecified requires unknown panic identity";

/// `(golden, the construct its subject-isolated form is refused by, every
/// construct the golden as vendored may be refused by)`. A golden mixing
/// several refused constructs is refused at whichever the floor meets first:
/// `drop_glue` drops before its `DropInvoke`, `unwind_twins`' `boom`
/// carries an unsited `DivByZero` check ([`isolated`] removes both), and
/// `assert_panic_site`'s `resumed` carries a sited check of `Unspecified`
/// kind, which the shared floor refuses for its kind on the module lanes
/// ([`floor_isolated`] removes it there; decision LD-W7-9).
const GOLDENS: &[(&str, &str, &[&str])] = &[
    (
        "assert_panic_site",
        "Inst::Assert { site: Some(_) }",
        &["Inst::Assert { site: Some(_) }", UNSPECIFIED_SITED_CHECK],
    ),
    (
        "assert_invoke",
        "Inst::AssertInvoke",
        &["Inst::AssertInvoke"],
    ),
    (
        "drop_glue",
        "Inst::DropInvoke",
        &["Inst::DropInvoke", "Inst::Drop"],
    ),
    (
        "unwind_twins",
        "Inst::InvokeIndirect",
        &["Inst::InvokeIndirect", "[TCG-ASSERT-PANIC]"],
    ),
];

fn fixture_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/fixtures/trust_ir_binary_container/conformance")
}

/// The golden's `.tmbc`, read by trust-cg's reader and retargeted to wasm32
/// (the golden is pinned to the canonical `aarch64-apple-darwin`; its
/// `struct_passing` producer fact is kept).
fn golden(name: &str) -> Module {
    let path = fixture_root().join(format!("{name}.tmbc"));
    let bytes = std::fs::read(&path).unwrap_or_else(|e| panic!("{}: {e}", path.display()));
    let mut module = pipeline::load_module_from_bytes(&bytes)
        .unwrap_or_else(|e| panic!("{name}: trust-cg's reader refused the golden: {e}"));
    let info = module
        .target_info
        .take()
        .expect("the golden declares a target");
    assert_eq!(info.triple, "aarch64-apple-darwin", "{name}");
    module.target_info = Some(trust_ir::TargetInfo {
        struct_passing: info.struct_passing,
        ..wasm::wasm32_target_info()
    });
    module
}

/// `module` with every bodied function licensed by [`TEST_AUTHORITY`].
fn relicensed(mut module: Module) -> Module {
    let mut ungated = 0;
    for func in module.functions.iter_mut().filter(|f| !f.blocks.is_empty()) {
        if func.body_gate == Some(BodyGate::Ungated) {
            ungated += 1;
        }
        func.body_gate = Some(BodyGate::gated(TEST_AUTHORITY.to_string()));
    }
    assert!(
        ungated > 0,
        "the golden wears `ungated` (the premise moved)"
    );
    module
}

/// `module` with every plain `Inst::Drop` and every unsited `Inst::Assert`
/// removed (neither defines a value), so the only refused constructs left
/// are the v54-v56 subjects and the floor must name one of them.
fn isolated(mut module: Module) -> Module {
    for block in module
        .functions
        .iter_mut()
        .flat_map(|f| f.blocks.iter_mut())
    {
        block.body.retain(|node| {
            !matches!(
                node.inst,
                Inst::Drop { .. } | Inst::Assert { site: None, .. }
            )
        });
    }
    let errors = trust_ir_build::validate_module(&module);
    assert!(
        errors.is_empty(),
        "{}: isolation broke the module: {errors:?}",
        module.name
    );
    module
}

/// [`isolated`] `module` as the MODULE lanes see it: also without the sited
/// checks of `Unspecified` kind. Since the native lanes deliver sited checks
/// of a stated kind, the shared floor refuses a sited check only when its
/// kind is `Unspecified` (it has no Rust panic identity), before any lane
/// walks a body, so such a check would hide every other subject from the
/// lane's own by-name refusal. Removing it (it defines no value) leaves the
/// lane's refusal of a sited check of a stated kind as the only one; the
/// vendored golden still pins the floor's refusal
/// ([`UNSPECIFIED_SITED_CHECK`]). The per-function entry has no module floor,
/// so its test keeps these checks.
fn floor_isolated(mut module: Module) -> Module {
    for block in module
        .functions
        .iter_mut()
        .flat_map(|f| f.blocks.iter_mut())
    {
        block.body.retain(|node| {
            !matches!(
                &node.inst,
                Inst::Assert {
                    site: Some(_),
                    kind,
                    ..
                } if kind.is_unspecified()
            )
        });
    }
    let errors = trust_ir_build::validate_module(&module);
    assert!(
        errors.is_empty(),
        "{}: isolation broke the module: {errors:?}",
        module.name
    );
    assert!(
        module
            .functions
            .iter()
            .flat_map(|f| &f.blocks)
            .flat_map(|b| &b.body)
            .any(|node| is_subject(&node.inst)),
        "{}: the module-lane twin keeps a v54-v56 subject",
        module.name
    );
    module
}

fn license() -> CodegenLicensePolicy {
    CodegenLicensePolicy::default().with_recognized_authority(TEST_AUTHORITY)
}

type Lane = fn(&Module, &CodegenLicensePolicy, OptLevel) -> Result<(), WasmLowerError>;

fn closed_lane(
    m: &Module,
    l: &CodegenLicensePolicy,
    level: OptLevel,
) -> Result<(), WasmLowerError> {
    wasm::compile_module_with_evidence_policy_license_optimized(
        m,
        &wasm::WasmModulePolicy::closed(),
        l,
        level,
    )
    .map(drop)
}

fn object_lane(
    m: &Module,
    l: &CodegenLicensePolicy,
    level: OptLevel,
) -> Result<(), WasmLowerError> {
    wasm::compile_object_with_license_optimized(m, l, level).map(drop)
}

const LANES: &[(&str, Lane)] = &[("wasm-module", closed_lane), ("wasm-object", object_lane)];
const LEVELS: &[OptLevel] = &[OptLevel::O0, OptLevel::O2];

#[test]
fn v54_v56_goldens_are_refused_by_name_on_both_wasm_lanes_at_every_level() {
    let mut cells = 0;
    for (name, subject, constructs) in GOLDENS {
        let vendored = relicensed(golden(name));
        let isolated = floor_isolated(isolated(vendored.clone()));
        for (module, constructs) in [(&vendored, *constructs), (&isolated, &[*subject][..])] {
            for (lane, compile) in LANES {
                for &level in LEVELS {
                    let error = compile(module, &license(), level).expect_err(&format!(
                        "{lane} {level:?} compiled the {name} golden: a v54-v56 construct was \
                     accepted"
                    ));
                    let text = error.to_string();
                    assert!(
                        constructs.iter().any(|c| text.contains(c)),
                        "{lane} {level:?} {name}: refused for another reason (expected one of \
                     {constructs:?}): {text}"
                    );
                    assert!(
                        !text.contains(TEST_AUTHORITY),
                        "{lane} {level:?} {name}: the license layer refused: {text}"
                    );
                    cells += 1;
                }
            }
        }
    }
    assert_eq!(cells, 2 * GOLDENS.len() * LANES.len() * LEVELS.len());
}

/// The ungated originals are refused by the license layer, which runs before
/// the floor on both lanes (round 8's admission order).
#[test]
fn ungated_goldens_are_refused_by_the_license_layer_first() {
    for (name, _, _) in GOLDENS {
        let module = golden(name);
        for (lane, compile) in LANES {
            let error = compile(&module, &license(), OptLevel::O2)
                .expect_err(&format!("{lane}: the ungated {name} golden compiled"));
            assert!(
                matches!(error, WasmLowerError::CodegenLicense(_)),
                "{lane} {name}: expected the license refusal first, got {error:?}"
            );
            assert!(
                error.to_string().contains("affirmatively ungated"),
                "{lane} {name}: {error}"
            );
        }
    }
}

/// Whether `inst` is one of the v54-v56 constructs this target is about.
fn is_subject(inst: &Inst) -> bool {
    matches!(
        inst,
        Inst::Assert { site: Some(_), .. }
            | Inst::AssertInvoke { .. }
            | Inst::DropInvoke { .. }
            | Inst::InvokeIndirect { .. }
    )
}

/// The per-function entry reached with a function the module floor never
/// sees: the module's copy of every function carrying a subject is emptied to
/// a declaration, and the original (claim-less, so the default license the
/// entry applies permits it) is handed to [`wasm::lower_function`]. The
/// lane's own backstop must refuse it by name; an earlier admission refusal
/// is tolerated, a compile never is.
#[test]
fn the_per_function_entry_refuses_every_subject_without_the_module_floor() {
    let mut subjects = 0;
    let mut by_name = 0;
    for (name, subject, _) in GOLDENS {
        let mut module = isolated(golden(name));
        for f in &mut module.functions {
            f.body_gate = None;
        }
        let carries = |f: &trust_ir::Function| {
            f.blocks
                .iter()
                .flat_map(|b| &b.body)
                .any(|n| is_subject(&n.inst))
        };
        let mut floorless = module.clone();
        for f in floorless.functions.iter_mut().filter(|f| carries(f)) {
            f.blocks.clear();
        }
        for func in module.functions.iter().filter(|f| carries(f)) {
            let outcome = wasm::lower_function_with_license(
                &mut WasmModule::new(),
                func,
                &floorless,
                WasmFunctionEnv::empty(),
                &permit_unlicensed(),
            );
            let error = outcome.expect_err(&format!(
                "{name}: lower_function compiled `{}`, which carries a v54-v56 construct",
                func.name
            ));
            let text = error.to_string();
            eprintln!("{name} `{}`: {text}", func.name);
            if text.contains(subject) {
                by_name += 1;
            } else {
                assert!(
                    matches!(error, WasmLowerError::CodegenAdmission(_)),
                    "{name} `{}`: refused for another reason: {text}",
                    func.name
                );
            }
            subjects += 1;
        }
    }
    assert!(
        subjects >= GOLDENS.len(),
        "every golden has a subject function"
    );
    assert_eq!(
        by_name, subjects,
        "every subject reached its by-name backstop"
    );
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes (or is refused) because the license silently refused it.
fn permit_unlicensed() -> trust_cg_codegen::CodegenLicensePolicy {
    trust_cg_codegen::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_codegen::UnlicensedBodyPolicy::Permit)
}
