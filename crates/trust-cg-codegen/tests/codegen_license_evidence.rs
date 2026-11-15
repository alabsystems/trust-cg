// trust-cg-codegen/tests/codegen_license_evidence.rs — roadmap WS7.5: the
// codegen license on every COMPILER lane (AOT object, host JIT, closed-JIT
// Core, compile service, wasm32).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Two decisions, pinned on the lanes that produce machine code:
//!
//! 1. **`Gated{"clean-kernel-tv"}` is bound to evidence (WS7.5(b), F-006).**
//!    The real Clean Fragment-2 `addmul` (trust-ir's `lean_library_envelope`
//!    conformance fixture, vendored byte-identical at the pin), its license
//!    carrying the trust-ir v61 `GateEvidence` that holds for it
//!    ([`certified_envelope`]), compiles on every lane under the DEFAULT
//!    policy and, JIT-compiled, computes what the reference interpreter
//!    computes; the same module without its certificate is refused on every
//!    lane as `GatedWithoutEvidence`.
//! 2. **`body_gate: None` is refused by default (DG-73, WS7.5 DECIDE 1).** A
//!    claim-less body compiles only under an explicit `Permit`; closed-JIT
//!    Core admission defers the claim-less decision to the planner (named
//!    exception `CoreAdmissionFloor`), which refuses it under the default.
//!
//! Ported rows (each a test named after it): `rerun.moved04`,
//! `rerun.moved07`, `rerun.moved08`, `rerun.finding05` (the rerun-lean-head
//! adjudication of findings F-116 and F-103, consumer half). The CLI-level
//! twins (`LEAN.consumer.ungated_codegen`, `--permit-unlicensed` and its
//! disclosure line) are in trust-cg-cli `tests/codegen_license_flags.rs`.
//!
//! The mutation control (`--features mutation-knobs`, which no gate runs) is
//! OPEN: red by construction since `d3785f3a1` (see the control at the end).
//! It was written to switch the evidence binding off and require the negative
//! twin to compile on the AOT lane again.

// Used by the native host-JIT controls alone, so imported under their gate.
#[cfg(all(
    target_arch = "aarch64",
    any(target_os = "macos", all(target_os = "linux", target_env = "gnu"))
))]
use std::collections::HashMap;

use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::pipeline::{self, OptLevel};
use trust_cg_codegen::target::TargetSpec;
use trust_cg_codegen::{
    ArtifactKind, CLEAN_KERNEL_TV_AUTHORITY, CodegenLicensePolicy, CompileGeneration, CompilePlan,
    CompileRequest, CompileService, CompileServiceConfig, CompileStatus, InstallIntent,
    UnlicensedBodyPolicy,
};
use trust_ir::proof::ObligationKind;
use trust_ir::{BodyGate, GateEvidence, Module};

/// The `mutation-knobs` control flips a PROCESS-GLOBAL knob; every test in
/// this binary holds this lock, so no refusal below can race it.
static SERIAL: std::sync::Mutex<()> = std::sync::Mutex::new(());

fn serial() -> std::sync::MutexGuard<'static, ()> {
    SERIAL
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner)
}

const ENVELOPE: &str = concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/../../tests/fixtures/trust_ir_binary_container/conformance/lean_library_envelope.tmbc"
);

/// The canonical object target the envelope (which declares none) is
/// compiled for.
const OBJECT_TARGET: &str = "aarch64-apple-darwin";

/// The envelope, decoded through trust-cg's own reader (the CLI's), and
/// required kernel-certified for codegen by the pinned trust-ir.
fn envelope() -> Module {
    let bytes = std::fs::read(ENVELOPE).unwrap_or_else(|e| panic!("read {ENVELOPE}: {e}"));
    let module = pipeline::load_module_from_bytes(&bytes).expect("trust-cg reads the envelope");
    assert_eq!(trust_ir_build::validate_module_for_codegen(&module), []);
    module
}

/// The envelope with `addmul`'s `clean-kernel-tv` license carrying the
/// trust-ir v61 `GateEvidence` that holds for it: its `Certified`
/// TranslationValidation row and the digest of its body as decoded. The
/// vendored envelope predates v61 and records none, which the admission
/// refuses by default (`UnevidencedGate`, OD-V61-GATE-EVIDENCE-20261014), so
/// the positive arms bind it here, as trust-cg-lower's
/// `tests/codegen_license_evidence.rs` does; the negative arms keep the
/// envelope as decoded.
fn certified_envelope() -> Module {
    let mut module = envelope();
    let addmul = module.function_by_name("addmul").expect("addmul").id;
    let obligation = module
        .proof_obligations
        .iter()
        .find(|o| o.kind == ObligationKind::TranslationValidation && o.function == Some(addmul))
        .expect("the TV row scoped to addmul")
        .id;
    let body_digest = module
        .function_body_digest(addmul)
        .expect("the licensed body has a digest");
    let function = module
        .functions
        .iter_mut()
        .find(|f| f.id == addmul)
        .expect("addmul");
    function.body_gate = Some(BodyGate::Gated {
        authority: CLEAN_KERNEL_TV_AUTHORITY.to_string(),
        evidence: Some(GateEvidence {
            obligation,
            body_digest,
        }),
    });
    assert_eq!(trust_ir_build::validate_module_for_codegen(&module), []);
    module
}

/// The negative twin: no obligations, no certificates.
fn without_evidence(mut module: Module) -> Module {
    module.proof_obligations.clear();
    module.proof_certificates.clear();
    module
}

/// Every bodied function re-stamped `gate`.
fn restamped(mut module: Module, gate: Option<BodyGate>) -> Module {
    for function in module.functions.iter_mut().filter(|f| !f.is_declaration()) {
        function.body_gate = gate.clone();
    }
    module
}

fn permit() -> CodegenLicensePolicy {
    CodegenLicensePolicy::default().with_unlicensed(UnlicensedBodyPolicy::Permit)
}

/// AOT object compile for [`OBJECT_TARGET`] under `license`.
fn aot(module: &Module, license: &CodegenLicensePolicy) -> Result<Vec<u8>, String> {
    let spec = TargetSpec::parse(OBJECT_TARGET).expect("target");
    Compiler::new_for_target_spec(
        CompilerConfig {
            opt_level: OptLevel::O0,
            ..CompilerConfig::default()
        },
        spec,
    )
    .with_codegen_license(license.clone())
    .compile(module)
    .map(|result| result.object_code)
    .map_err(|e| e.to_string())
}

/// AOT under the compiler's OWN default policy (no `with_codegen_license`).
fn aot_default(module: &Module) -> Result<Vec<u8>, String> {
    let spec = TargetSpec::parse(OBJECT_TARGET).expect("target");
    Compiler::new_for_target_spec(
        CompilerConfig {
            opt_level: OptLevel::O0,
            ..CompilerConfig::default()
        },
        spec,
    )
    .compile(module)
    .map(|result| result.object_code)
    .map_err(|e| e.to_string())
}

/// The compile service with `license`, object artifact.
fn service(module: &Module, license: &CodegenLicensePolicy) -> Result<(), String> {
    let spec = TargetSpec::parse(OBJECT_TARGET).expect("target");
    let service = CompileService::new(CompileServiceConfig {
        codegen_license: license.clone(),
        ..CompileServiceConfig::default()
    });
    let mut request = CompileRequest::new("ws7.5", CompileGeneration::new(1));
    request.artifact_kind = ArtifactKind::Object;
    request.install_intent = InstallIntent::CompileOnly;
    let response = service.compile_plan(CompilePlan::new(request, spec), module);
    if response.status == CompileStatus::Compiled {
        return Ok(());
    }
    Err(response
        .diagnostics
        .iter()
        .map(|d| format!("[{}] {}", d.code, d.message))
        .collect::<Vec<_>>()
        .join("; "))
}

/// The wasm32 lane under the DEFAULT license (the module re-targeted to
/// wasm32; the TV certificate is target-independent).
fn wasm_default(module: &Module) -> Result<Vec<u8>, String> {
    let mut module = module.clone();
    module.target_info = Some(trust_cg_codegen::wasm::wasm32_target_info());
    trust_cg_codegen::wasm::compile_module(&module).map_err(|e| e.to_string())
}

fn assert_refused(outcome: Result<impl Sized, String>, needle: &str, what: &str) {
    match outcome {
        Ok(_) => panic!("{what}: must be refused (`{needle}`)"),
        Err(message) => assert!(
            message.contains(needle),
            "{what}: refused, but not by the arm that spells `{needle}`: {message}"
        ),
    }
}

/// `GatedWithoutEvidence`'s rendered text, for `addmul`.
const NO_EVIDENCE: &str = "function `addmul` claims codegen license `Gated{\"clean-kernel-tv\"}` without the evidence it names";

/// `UngatedBody`'s rendered text, for `addmul` — the verbatim diagnostic the
/// rerun recorded.
const UNGATED: &str = "function `addmul` is affirmatively ungated";

/// `UnlicensedBody`'s rendered text, for `addmul`.
const UNLICENSED: &str = "function `addmul` carries no codegen license";

// ---------------------------------------------------------------------------
// Row consumer.cg.kernel_tv_license_bound, compiler lanes
// ---------------------------------------------------------------------------

/// Positive: the certified envelope, its evidence bound
/// ([`certified_envelope`]), compiles on the AOT, service and wasm lanes
/// under the DEFAULT policy — no `Permit` anywhere.
#[test]
fn certified_kernel_tv_body_compiles_on_every_lane_under_the_default_policy() {
    let _serial = serial();
    let module = certified_envelope();
    let object = aot(&module, &CodegenLicensePolicy::default()).expect("AOT compiles addmul");
    assert!(!object.is_empty());
    aot_default(&module).expect("the compiler's own default compiles addmul");
    service(&module, &CodegenLicensePolicy::default()).expect("the service compiles addmul");
    wasm_default(&module).expect("the wasm32 lane compiles addmul");
}

/// Negative twin: the same module without its certificate is refused on every
/// lane, by name, under every policy.
#[test]
fn kernel_tv_body_without_its_certificate_is_refused_on_every_lane() {
    let _serial = serial();
    let module = without_evidence(envelope());
    for license in [
        CodegenLicensePolicy::default(),
        permit(),
        CodegenLicensePolicy::recognizing_nothing(),
    ] {
        assert_refused(aot(&module, &license), NO_EVIDENCE, "AOT");
        assert_refused(service(&module, &license), NO_EVIDENCE, "service");
    }
    assert_refused(aot_default(&module), NO_EVIDENCE, "AOT default");
    assert_refused(wasm_default(&module), NO_EVIDENCE, "wasm32");
}

// ---------------------------------------------------------------------------
// Host JIT (native execution) and closed-JIT Core
// ---------------------------------------------------------------------------

#[cfg(all(
    target_arch = "aarch64",
    any(target_os = "macos", all(target_os = "linux", target_env = "gnu"))
))]
mod host_jit {
    use super::*;
    use trust_cg_codegen::{
        CoreDeclaredImportManifest, CoreHostJitTarget, CoreJitPlanningError, Target,
        admit_identity_core_module_for_host_jit,
    };
    use trust_cg_lower::AdapterError;
    use trust_ir::Ty;
    use trust_ir::interpret::{InterpretValue, Interpreter};

    fn jit_compiler(license: &CodegenLicensePolicy) -> Compiler {
        let host = CoreHostJitTarget::detect().expect("supported native AArch64 test host");
        Compiler::new_for_target_spec(
            CompilerConfig::jit_fast(Target::Aarch64),
            host.target_spec(),
        )
        .with_codegen_license(license.clone())
    }

    /// A JIT compile's outcome, as the other lanes' `Result<_, String>`.
    fn jit(module: &Module, license: &CodegenLicensePolicy) -> Result<(), String> {
        jit_compiler(license)
            .compile_module_to_jit(module, &HashMap::new())
            .map(|_| ())
            .map_err(|e| e.to_string())
    }

    fn interpret_addmul(module: &Module, a: u64, b: u64) -> u64 {
        let function = module.function_by_name("addmul").expect("addmul");
        let args = [
            InterpretValue::int(Ty::U64, i128::from(a)).expect("u64"),
            InterpretValue::int(Ty::U64, i128::from(b)).expect("u64"),
        ];
        let outcome = Interpreter::with_module(module)
            .execute_function(function, args)
            .expect("interpret addmul");
        u64::try_from(outcome.returns[0].as_int().expect("int").as_unsigned()).expect("u64")
    }

    /// Row `rerun.finding05` (F-103, consumer half): "the only minter of
    /// Gated{clean-kernel-tv} is the kernel TV certificate". A Clean body
    /// that carries it is exactly what this backend compiles natively — and
    /// the object computes what the interpreter computes (`addmul(a, b) =
    /// a*b + a`, wrapping) — while the same body stamped `Ungated` (what the
    /// pinned clean emits for every body its TV skipped) or wearing the
    /// license without its certificate is refused.
    #[test]
    fn rerun_finding05_the_native_path_for_clean_bodies_is_the_kernel_tv_certificate() {
        let _serial = serial();
        let module = certified_envelope();
        let buffer = jit_compiler(&CodegenLicensePolicy::default())
            .compile_module_to_jit(&module, &HashMap::new())
            .expect("the certified body JIT-compiles under the default policy")
            .buffer;
        for (a, b) in [
            (6, 7),
            (0, 0),
            (u64::MAX, 2),
            (1 << 33, 1 << 33),
            (3, u64::MAX),
        ] {
            // SAFETY: `addmul` is `(u64, u64) -> u64` under the C convention,
            // and `buffer` outlives the call.
            let native = unsafe {
                buffer
                    .get_fn_bound::<extern "C" fn(u64, u64) -> u64>("addmul")
                    .expect("addmul")
                    .as_ref()(a, b)
            };
            assert_eq!(native, interpret_addmul(&module, a, b), "addmul({a}, {b})");
            assert_eq!(
                native,
                a.wrapping_mul(b).wrapping_add(a),
                "addmul({a}, {b})"
            );
        }
        let ungated = restamped(module, Some(BodyGate::Ungated));
        assert_refused(jit(&ungated, &permit()), UNGATED, "JIT ungated");
        assert_refused(
            jit(&without_evidence(envelope()), &permit()),
            NO_EVIDENCE,
            "JIT without evidence",
        );
    }

    /// Closed-JIT Core: admission lowers under the license FLOOR, which
    /// defers a claim-less body (named exception `CoreAdmissionFloor`), and
    /// the planner re-decides under the compiler's policy — the DEFAULT now
    /// refuses it (DG-73), a `Permit` compiler plans it. A `Gated` body
    /// without its evidence never gets past admission.
    /// Set in the child that [`core_admission_defers_claim_less_bodies_and_the_default_planner_refuses_them`]
    /// re-runs itself in.
    const CORE_CHILD: &str = "WS7_5_CORE_LICENSE_CHILD";

    #[test]
    fn core_admission_defers_claim_less_bodies_and_the_default_planner_refuses_them() {
        let _serial = serial();
        // Identity-Core admission refuses every unkeyed compiler control in
        // the RAW process environment (a logical removal cannot hide one),
        // and a test-harness knob such as the landing lane's
        // `TRUST_CG_TEST_TIMEOUT_SCALE` is one. That refusal is its own rule
        // (`core_jit_planning`'s `plan_rejects_unknown_ambient_compiler_controls`);
        // this test is about the LICENSE, so it runs its body in a child of
        // this binary with exactly those controls removed, rather than pass
        // or fail on the harness.
        let ambient = trust_cg_codegen::env_lock::artifact_reuse_environment_safety();
        if std::env::var_os(CORE_CHILD).is_none() && !ambient.is_reuse_safe() {
            let name = "host_jit::core_admission_defers_claim_less_bodies_and_the_default_planner_refuses_them";
            let mut child =
                std::process::Command::new(std::env::current_exe().expect("this test binary"));
            child
                .args(["--exact", name, "--nocapture", "--test-threads=1"])
                .env(CORE_CHILD, "1");
            for control in ambient.unkeyed_controls() {
                child.env_remove(control);
            }
            let output = child.output().expect("run the child");
            let stdout = String::from_utf8_lossy(&output.stdout);
            assert!(
                output.status.success() && stdout.contains("1 passed"),
                "child without {:?}: {}\n{stdout}\n{}",
                ambient.unkeyed_controls(),
                output.status,
                String::from_utf8_lossy(&output.stderr)
            );
            return;
        }
        let target = CoreHostJitTarget::detect().expect("host");
        let mut module = restamped(without_evidence(envelope()), None);
        module.target_info = Some(target.trust_ir_target_info().clone());
        let core = admit_identity_core_module_for_host_jit(
            module.clone(),
            &target,
            CoreDeclaredImportManifest::empty(),
        )
        .expect("admission defers the claim-less body to the planner");
        let failure = Compiler::new_for_target_spec(
            CompilerConfig::for_host_jit_unchecked(),
            target.target_spec(),
        )
        .plan_core_module_for_jit_compilation(core)
        .expect_err("the default planner refuses the claim-less body");
        assert!(
            matches!(
                failure.reason(),
                CoreJitPlanningError::CodegenLicense(AdapterError::UnlicensedBody { function })
                    if function == "addmul"
            ),
            "{:?}",
            failure.reason()
        );
        let (_, core) = failure.into_parts();
        Compiler::new_for_target_spec(
            CompilerConfig::for_host_jit_unchecked(),
            target.target_spec(),
        )
        .with_codegen_license(permit())
        .plan_core_module_for_jit_compilation(core)
        .expect("an explicit Permit compiler plans it");

        let mut gated = without_evidence(envelope());
        gated.target_info = Some(target.trust_ir_target_info().clone());
        let refusal = admit_identity_core_module_for_host_jit(
            gated,
            &target,
            CoreDeclaredImportManifest::empty(),
        )
        .expect_err("a gated body without its evidence is refused at admission");
        let text = format!("{refusal:?}");
        assert!(
            text.contains("GatedWithoutEvidence") && text.contains("\"addmul\""),
            "{text}"
        );
    }
}

// ---------------------------------------------------------------------------
// Ported rows (rerun-lean-head, F-116 and F-103 consumer half)
// ---------------------------------------------------------------------------

/// Row `rerun.moved04` (F-116): the Part A-Lean envelope re-stamped
/// `Ungated` ("native_codegen=unavailable") is refused — verbatim "function
/// `addmul` is affirmatively ungated" — on every lane and under every
/// policy, the permissive one included.
#[test]
fn rerun_moved04_the_ungated_envelope_is_refused_on_every_lane() {
    let _serial = serial();
    let module = restamped(envelope(), Some(BodyGate::Ungated));
    for license in [
        CodegenLicensePolicy::default(),
        permit(),
        CodegenLicensePolicy::default().with_recognized_authority("ungated"),
    ] {
        assert_refused(aot(&module, &license), UNGATED, "AOT");
        assert_refused(service(&module, &license), UNGATED, "service");
    }
    assert_refused(aot_default(&module), UNGATED, "AOT default");
    assert_refused(wasm_default(&module), UNGATED, "wasm32");
}

/// Row `rerun.moved07` (F-103): `clean compile --emit obj` hands trust-cg a
/// v41 blob whose every body is stamped `Ungated`; it is refused "by design"
/// through trust-cg's own reader and every compiler lane. Emulated exactly:
/// the Ungated envelope serialized by trust-ir's writer (a v41 header,
/// because `body_gate` is present) and read back by `load_module_from_bytes`.
#[test]
fn rerun_moved07_clean_emit_obj_ungated_blob_is_refused_by_design() {
    let _serial = serial();
    let module = restamped(envelope(), Some(BodyGate::Ungated));
    let bytes =
        trust_ir::binary::serialize_module(&module).expect("serialize_module: test fixture");
    assert_eq!(
        u32::from_le_bytes(bytes[8..12].try_into().expect("header")),
        41,
        "the contract surface selects v41"
    );
    let decoded = pipeline::load_module_from_bytes(&bytes).expect("an Ungated v41 blob decodes");
    assert_refused(
        aot(&decoded, &CodegenLicensePolicy::default()),
        UNGATED,
        "AOT",
    );
    assert_refused(aot(&decoded, &permit()), UNGATED, "AOT under Permit");
}

/// Row `rerun.moved08` (F-103): once the Ungated refusal is honored the link
/// rows are unreachable, and the rerun's run-4 EXPERIMENT showed the one way
/// around it: delete the `#body-gate: ungated` stamp, so the body carries NO
/// claim, and trust-cg's then-default `Permit` compiled it (and the pinned
/// clean's `w8` came back silently WRONG). Stripping the stamp is no longer a
/// bypass: a claim-less body is refused by default on every lane (DG-73),
/// and compiles only under the explicit `Permit` a caller must spell.
#[test]
fn rerun_moved08_stripping_the_ungated_stamp_is_not_a_bypass() {
    let _serial = serial();
    let module = restamped(without_evidence(envelope()), None);
    assert_refused(
        aot(&module, &CodegenLicensePolicy::default()),
        UNLICENSED,
        "AOT",
    );
    assert_refused(aot_default(&module), UNLICENSED, "AOT default");
    assert_refused(
        service(&module, &CodegenLicensePolicy::default()),
        UNLICENSED,
        "service",
    );
    assert_refused(wasm_default(&module), UNLICENSED, "wasm32");
    // Only the explicit, spelled Permit compiles it.
    aot(&module, &permit()).expect("an explicit Permit compiles the claim-less body");
    service(&module, &permit()).expect("an explicit Permit compiles it in the service too");
    // A text/JSON route cannot launder it either (the run-4 experiment used
    // `--format=text`): the parsed module carries no wire version, so only
    // the license can refuse it — and does.
    let text = module.to_string();
    let parsed = trust_ir::parser::parse_module(&text).expect("text round trip");
    assert_refused(
        aot(&parsed, &CodegenLicensePolicy::default()),
        UNLICENSED,
        "AOT from text",
    );
    // And a v41 BINARY blob with a claim-less body is the producer's
    // omission, refused by trust-cg's reader before any policy (the envelope
    // keeps its v41 `display_path`, so the writer selects v41).
    let bytes =
        trust_ir::binary::serialize_module(&module).expect("serialize_module: test fixture");
    assert_eq!(
        u32::from_le_bytes(bytes[8..12].try_into().expect("header")),
        41
    );
    let refusal = pipeline::load_module_from_bytes(&bytes)
        .expect_err("a v41 blob with a claim-less body is a producer omission");
    assert!(
        refusal.to_string().contains("no codegen license"),
        "{refusal}"
    );
}

// ---------------------------------------------------------------------------
// Mutation control
// ---------------------------------------------------------------------------

/// A default build carries no mutation knob.
#[test]
fn default_build_has_no_mutation_knobs() {
    let _serial = serial();
    assert_eq!(
        trust_cg_lower::MUTATION_KNOBS,
        cfg!(feature = "mutation-knobs")
    );
}

/// Other mutation features do not disable the compiler's evidence floor.
#[cfg(feature = "mutation-knobs")]
#[test]
fn mutation_build_keeps_the_mandatory_evidence_floor() {
    let _serial = serial();
    let module = without_evidence(envelope());
    let license = CodegenLicensePolicy::default();
    assert_refused(aot(&module, &license), NO_EVIDENCE, "mutation-enabled AOT");
    assert_refused(
        service(&module, &license),
        NO_EVIDENCE,
        "mutation-enabled service",
    );
    assert_refused(
        wasm_default(&module),
        NO_EVIDENCE,
        "mutation-enabled wasm32",
    );
}

/// The authority constant this crate re-exports is the evidence-bound one.
#[test]
fn the_default_recognized_authority_is_trust_irs_evidence_bound_one() {
    let _serial = serial();
    assert_eq!(CLEAN_KERNEL_TV_AUTHORITY, "clean-kernel-tv");
    assert!(trust_ir_build::gate_evidence_rule(CLEAN_KERNEL_TV_AUTHORITY).is_some());
    assert!(CodegenLicensePolicy::default().recognizes(CLEAN_KERNEL_TV_AUTHORITY));
}

// ---------------------------------------------------------------------------
// The wasm32 lane's own runtime helpers (named exception `LaneRuntimeHelper`)
// ---------------------------------------------------------------------------

/// A wasm32 module whose one producer body `f` takes an `f64` remainder, which
/// the lane emits as a call to the `fmod` helper body it builds itself. Every
/// producer body is stamped `gate`; the helper, a lane template, carries none.
fn frem_module(gate: Option<BodyGate>) -> Module {
    const TEXT: &str = "; TrustIr text format v1\nmodule \"frem_helper\"\n\
        target \"wasm32-unknown-unknown\" 4 little\n\n\
        functy.0 = (f64, f64) -> (f64)\n\n\
        fn @f(functy.0) {\nbb0(%0: f64, %1: f64):\n    %2 = frem f64 %0, %1\n    ret %2\n}\n";
    let module = trust_ir::parser::parse_module(TEXT).expect("the probe parses");
    assert_eq!(trust_ir_build::validate_module(&module), []);
    restamped(module, gate)
}

/// Both wasm32 entries (closed module and object) under `license`.
fn wasm_lanes(
    module: &Module,
    license: &CodegenLicensePolicy,
) -> [(&'static str, Result<(), String>); 2] {
    use trust_cg_codegen::wasm::{compile_module_with_license, compile_object_with_license};
    [
        (
            "wasm32 module",
            compile_module_with_license(module, license)
                .map(drop)
                .map_err(|e| e.to_string()),
        ),
        (
            "wasm32 object",
            compile_object_with_license(module, license)
                .map(drop)
                .map_err(|e| e.to_string()),
        ),
    ]
}

/// The helper is LICENSED by its named exception, independently of the
/// caller: a producer body licensed by an authority the caller recognizes
/// compiles WITH its claim-less `fmod` helper under the caller's DEFAULT
/// (claim-less-refusing) policy. Were the helper decided under the caller's
/// policy, this compile would be refused at the helper.
#[test]
fn lane_helper_compiles_beside_a_licensed_body_under_the_refusing_default() {
    let _guard = serial();
    let vendor = CodegenLicensePolicy::default().with_recognized_authority("vendor-gate");
    let module = frem_module(Some(BodyGate::gated("vendor-gate")));
    for (lane, outcome) in wasm_lanes(&module, &vendor) {
        outcome.unwrap_or_else(|e| panic!("{lane}: the licensed body and its helper compile: {e}"));
    }
}

/// Adversarial: the helper's exception never reaches a PRODUCER body. The
/// same module with `f` claim-less is refused under the default policy; with
/// `f` ungated, or worn under an authority nobody recognizes, or wearing
/// `clean-kernel-tv` without its certificate, it is refused even under
/// `Permit` — by the arm that names the producer's own license.
#[test]
fn lane_helper_exception_never_licenses_a_producer_body() {
    let _guard = serial();
    let cases: [(&str, Option<BodyGate>, CodegenLicensePolicy, &str); 4] = [
        (
            "claim-less under the default",
            None,
            CodegenLicensePolicy::default(),
            "function `f` carries no codegen license",
        ),
        (
            "ungated under Permit",
            Some(BodyGate::Ungated),
            permit(),
            "function `f` is affirmatively ungated",
        ),
        (
            "unrecognized authority under Permit",
            Some(BodyGate::gated("vendor-gate")),
            permit(),
            "does not recognize",
        ),
        (
            "clean-kernel-tv without its certificate under Permit",
            Some(BodyGate::gated(CLEAN_KERNEL_TV_AUTHORITY)),
            permit(),
            "without the evidence it names",
        ),
    ];
    for (case, gate, license, needle) in cases {
        let module = frem_module(gate);
        for (lane, outcome) in wasm_lanes(&module, &license) {
            assert_refused(outcome, needle, &format!("{lane}: {case}"));
        }
    }
}

/// Control: the same claim-less module compiles, helper included, under an
/// explicit `Permit` — so the refusals above are the license's, not the
/// fixture's.
#[test]
fn lane_helper_fixture_compiles_under_permit() {
    let _guard = serial();
    for (lane, outcome) in wasm_lanes(&frem_module(None), &permit()) {
        outcome.unwrap_or_else(|e| panic!("{lane}: the claim-less control compiles: {e}"));
    }
}
