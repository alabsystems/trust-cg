// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! X-OPCODES-P13 through each production certificate lane.
//!
//! A `covered_elsewhere` row that cites a per-compile decode check (x86-64
//! `MovRI` cites ENC-3, AArch64 `AlignNop` cites ENC-5) is positive only when
//! the backing its lane hands the certificate builder says that check gated
//! the compile. The builder's half is pinned in `compiler.rs`'s unit tests;
//! these tests pin the lanes' half by compiling a probe function through each
//! real route and comparing, from `decode_check::lane_probe`, the mode every
//! encode of that function ran its decode check in with the backing the lane
//! handed the builder, and the cited rows that came out.
//!
//! Lanes and what each test can observe:
//!
//! * x86-64 AOT (`compile_x86_64`): the backing follows `TCG_DECODE_CHECK` /
//!   `TCG_NO_DECODE_CHECK`, so a lane that passed a fixed backing fails here.
//! * x86-64 JIT (`x86_jit_certify_functions`): the same, in both the cached
//!   (`CachedVerified`) and uncached (`AlwaysVerify`) modes; both branches
//!   build through one conversion, and the cached branch is reachable only
//!   under an enforced backing (the outer-cache gate).
//! * AArch64 JIT (`compile_replayed_lir_module_to_jit`): a verifying mode
//!   encodes at proof grade (ENC-5 forced to enforce whatever the
//!   environment says); a compile that emits proofs under the `Unchecked`
//!   override encodes under the compatibility policy, so there the backing
//!   follows `TCG_DECODE_CHECK_A64` / `TCG_NO_DECODE_CHECK`. This lane gates
//!   its certificates before it encodes, so a compile the gate refuses has no
//!   encode to compare with and is checked against the policy alone.
//! * AArch64 AOT (`compile`): it builds certificates only when proofs are
//!   requested, which also selects proof-grade publication, so its backing is
//!   enforced in every environment. The test pins that the backing equals
//!   the mode the encode ran; a fixed `Enforced` there is equal by
//!   construction, which this test states rather than hides.
//!
//! The address-free AArch64 route passes `Enforced` as a constant: it encodes
//! only through `affine_bytes::encode_core_function`, under the proof-grade
//! policy, before its certificates are built.

use super::*;
use crate::decode_check::lane_probe::{self, Event, PROBE};
use crate::decode_check::{DecodeCheckBacking, DecodeCheckMode};
use crate::proof_evidence::{COVERED_ELSEWHERE_CATEGORY, COVERED_ELSEWHERE_WITHHELD_CATEGORY};

/// `fn <name>() -> u64 { 0x0123_4567_89ab_cdef }`. On x86-64 its body
/// materializes the constant with `MovRI`.
fn probe_module(name: &str) -> trust_ir::Module {
    use trust_ir_build::ModuleBuilder;

    let mut mb = ModuleBuilder::new("decode_backing_lane_probe");
    let ty = mb.add_func_type(vec![], vec![trust_ir::Ty::U64]);
    let mut fb = mb.function(name, ty);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let constant = fb.iconst(trust_ir::Ty::U64, 0x0123_4567_89ab_cdef);
    fb.ret(vec![constant]);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

/// A labelled set of environment overrides and the backing a check that
/// follows the environment resolves to under it.
type Environment = (
    &'static str,
    Vec<(&'static str, &'static str)>,
    DecodeCheckBacking,
);

/// The environments every lane is compiled under, for the given check's
/// environment key (`TCG_DECODE_CHECK` or `TCG_DECODE_CHECK_A64`).
fn environments(key: &'static str) -> [Environment; 4] {
    [
        ("default", vec![], DecodeCheckBacking::Enforced),
        ("warn", vec![(key, "warn")], DecodeCheckBacking::Warned),
        ("off", vec![(key, "off")], DecodeCheckBacking::NotRun),
        (
            "no_check",
            vec![("TCG_NO_DECODE_CHECK", "1")],
            DecodeCheckBacking::NotRun,
        ),
    ]
}

/// Run `compile` under `overrides` plus `TCG_REFINE_SOLVER=0` (no solver
/// replay, so the cited row reaches the covered-elsewhere path on any host).
fn under<T>(overrides: &[(&'static str, &'static str)], compile: impl FnOnce() -> T) -> T {
    let mut overrides = overrides.to_vec();
    overrides.push(("TCG_REFINE_SOLVER", "0"));
    crate::env_lock::with_env_overrides(&overrides, compile)
}

/// Where a lane's encode stands relative to its certificate build.
#[derive(Clone, Copy, Debug)]
enum EncodeOrder {
    /// The lane encodes the function before its certificates are built (x86-64
    /// AOT and JIT, AArch64 AOT), so every compile records an encode.
    First,
    /// The lane builds and gates the certificates before it encodes (the
    /// AArch64 JIT): a compile the promotion gate refused (`refused`) never
    /// reached the encode, and then only the expected backing is checked.
    /// Only the AArch64 JIT lane's test constructs it.
    #[cfg_attr(not(target_arch = "aarch64"), allow(dead_code))]
    AfterTheGate { refused: bool },
}

/// Check what `lane` did for the probe function `name`: every encode of it
/// ran `check` in the mode `expected` names, every certificate build of it
/// took exactly that backing, and every row whose strength starts with
/// `cited` follows it (positive `covered_elsewhere` only when enforced,
/// otherwise a blocking withheld row naming `check`). With `require_cited`,
/// at least one such row must exist.
fn assert_lane_follows_its_encode(
    lane: &str,
    name: &str,
    check: &'static str,
    cited: &str,
    expected: DecodeCheckBacking,
    require_cited: bool,
    order: EncodeOrder,
) {
    let events = lane_probe::take(name);
    let encodes: Vec<DecodeCheckMode> = events
        .iter()
        .filter_map(|event| match event {
            Event::Encode { check: ran, mode } if *ran == check => Some(*mode),
            _ => None,
        })
        .collect();
    let builds: Vec<(DecodeCheckBacking, &[ProofCertificate])> = events
        .iter()
        .filter_map(|event| match event {
            Event::Certificates { backing, certs } => Some((*backing, certs.as_slice())),
            Event::Encode { .. } => None,
        })
        .collect();
    match order {
        EncodeOrder::First | EncodeOrder::AfterTheGate { refused: false } => assert!(
            !encodes.is_empty(),
            "{lane}: no {check} encode of {name} was recorded: {events:?}"
        ),
        EncodeOrder::AfterTheGate { refused: true } => assert!(
            encodes.is_empty(),
            "{lane}: a compile refused before its encode recorded one: {events:?}"
        ),
    }
    assert!(
        !builds.is_empty(),
        "{lane}: no certificate build of {name} was recorded: {events:?}"
    );
    for mode in &encodes {
        assert_eq!(
            DecodeCheckBacking::from_mode(*mode),
            expected,
            "{lane}: the {check} mode an encode of {name} ran"
        );
    }
    for (backing, certs) in builds {
        assert_eq!(
            backing, expected,
            "{lane}: the backing the lane handed the certificate builder for {name} differs \
             from the {check} its encode ran ({encodes:?})"
        );
        let rows: Vec<&ProofCertificate> = certs
            .iter()
            .filter(|cert| cert.strength.starts_with(cited))
            .collect();
        assert!(
            !require_cited || !rows.is_empty(),
            "{lane}: no {cited} row for {name}: {certs:?}"
        );
        for row in rows {
            if expected.gates_the_compile() {
                assert!(row.verified, "{lane} {expected:?}: {row:?}");
                assert_eq!(row.category, COVERED_ELSEWHERE_CATEGORY, "{lane}");
            } else {
                assert!(!row.verified, "{lane} {expected:?}: {row:?}");
                assert_eq!(row.category, COVERED_ELSEWHERE_WITHHELD_CATEGORY, "{lane}");
                assert!(row.strength.contains(check), "{lane}: {row:?}");
            }
        }
    }
}

/// The x86-64 AOT lane hands its certificate builder the ENC-3 backing of the
/// compile's own encode, and the `MovRI` row follows it.
#[test]
fn x86_aot_lane_hands_its_certificates_the_enc3_backing_of_its_encode() {
    for (case, overrides, expected) in environments("TCG_DECODE_CHECK") {
        let name = format!("{PROBE}x86_aot_{case}_fn");
        let module = probe_module(&name);
        let result = under(&overrides, || {
            Compiler::new_for_target_spec(
                CompilerConfig {
                    opt_level: OptLevel::O0,
                    target: Target::X86_64,
                    emit_proofs: true,
                    parallel: false,
                    ..CompilerConfig::default()
                },
                TargetSpec::parse("x86_64-unknown-linux-gnu").unwrap(),
            )
            .with_codegen_license(permit_unlicensed())
            .compile(&module)
        });
        // A withheld row blocks promotion, so no relaxed compile publishes.
        assert!(
            expected.gates_the_compile() || result.is_err(),
            "{case}: a compile whose ENC-3 did not gate it was promoted"
        );
        assert_lane_follows_its_encode(
            &format!("x86-64 AOT, {case}"),
            &name,
            "ENC-3",
            "x86_64::MovRI:",
            expected,
            true,
            EncodeOrder::First,
        );
    }
}

/// The x86-64 JIT lane, in the cached (`CachedVerified`, the x86-64 default)
/// and uncached (`AlwaysVerify`) modes: its certificate builds take the ENC-3
/// backing of the JIT's own encode, and the `MovRI` row follows it. A relaxed
/// check also keeps the compile off the outer certificate cache.
#[test]
fn x86_jit_lane_hands_its_certificates_the_enc3_backing_of_its_encode() {
    for mode in [
        JitValidationMode::CachedVerified,
        JitValidationMode::AlwaysVerify,
    ] {
        for (case, overrides, expected) in environments("TCG_DECODE_CHECK") {
            let name = format!("{PROBE}x86_jit_{mode:?}_{case}_fn");
            let lir = trust_cg_lower::translate_module_for_arch_with_tls_with_license(
                &probe_module(&name),
                guard_carrier_arch_for_target(Target::X86_64),
                trust_cg_lower::TlsDialect::default(),
                &permit_unlicensed(),
            )
            .expect("the probe translates");
            let cache = std::sync::Arc::new(crate::jit_cert::JitCertCache::new());
            let compiler = Compiler::new(CompilerConfig::jit_fast(Target::X86_64))
                .with_jit_cert_cache(cache.clone());
            let definitions = x86_test_module_definitions(lir.iter().map(|(function, _)| function));
            let result = under(&overrides, || {
                compiler.compile_x86_64_to_jit(
                    lir,
                    &HashMap::new(),
                    JitExternalSymbolResolutionPolicy::ExplicitOnly,
                    crate::jit::ProfileHookMode::None,
                    mode,
                    Instant::now(),
                    false,
                    Vec::new(),
                    &definitions,
                )
            });
            assert!(
                expected.gates_the_compile() || result.is_err(),
                "{mode:?} {case}: a JIT compile whose ENC-3 did not gate it was published"
            );
            let (hits, misses, _, _) = cache.stats();
            assert_eq!(hits, 0, "{mode:?} {case}: a fresh cache cannot hit");
            // Under an enforced ENC-3 a `CachedVerified` compile takes the
            // cached branch (one miss) wherever the verifier request has a
            // reuse identity (an admitted AY; measured on the Apple M4 Max,
            // 2026-10-12); every other compile builds outside the cache.
            if !expected.gates_the_compile() || mode == JitValidationMode::AlwaysVerify {
                assert_eq!(
                    misses, 0,
                    "{mode:?} {case}: this compile must not consult the outer cache"
                );
            } else {
                assert!(misses <= 1, "{mode:?} {case}: {misses} misses");
            }
            assert_lane_follows_its_encode(
                &format!("x86-64 JIT, {mode:?}, {case}"),
                &name,
                "ENC-3",
                "x86_64::MovRI:",
                expected,
                true,
                EncodeOrder::First,
            );
        }
    }
}

/// The AArch64 AOT lane builds certificates only for a compile that requests
/// proofs, which also selects proof-grade publication: its encode runs ENC-5
/// in enforce whatever the environment says, and the backing it hands the
/// certificate builder is that one.
#[test]
fn aarch64_aot_lane_hands_its_certificates_the_enc5_backing_of_its_encode() {
    for (case, overrides, _) in environments("TCG_DECODE_CHECK_A64") {
        let name = format!("{PROBE}a64_aot_{case}_fn");
        let module = probe_module(&name);
        let _ = under(&overrides, || {
            Compiler::new(CompilerConfig {
                opt_level: OptLevel::O0,
                target: Target::Aarch64,
                emit_proofs: true,
                parallel: false,
                ..CompilerConfig::default()
            })
            .with_codegen_license(permit_unlicensed())
            .compile(&module)
        });
        assert_lane_follows_its_encode(
            &format!("AArch64 AOT, {case}"),
            &name,
            "ENC-5",
            "AArch64::AlignNop:",
            DecodeCheckBacking::Enforced,
            false,
            EncodeOrder::First,
        );
    }
}

/// The AArch64 JIT lane: a verifying compile encodes at proof grade, so its
/// backing is enforced in every environment; a compile that emits proofs
/// under the `Unchecked` override encodes under the compatibility policy, so
/// its backing follows `TCG_DECODE_CHECK_A64` / `TCG_NO_DECODE_CHECK`. This
/// lane gates its certificates before the `JitCompiler` encodes, so a compile
/// the gate refuses (the probe's unproved rows refuse every one without a
/// solver) records no encode; then the backing is checked against the policy
/// alone, and wherever the encode ran, against the mode it ran.
#[cfg(target_arch = "aarch64")]
#[test]
fn aarch64_jit_lane_hands_its_certificates_the_enc5_backing_of_its_encode() {
    for (label, config, follows_environment) in [
        (
            "verifying",
            CompilerConfig {
                emit_proofs: true,
                ..CompilerConfig::for_host_jit()
            },
            false,
        ),
        (
            "unchecked_with_proofs",
            CompilerConfig {
                emit_proofs: true,
                ..CompilerConfig::for_host_jit_unchecked()
            },
            true,
        ),
    ] {
        for (case, overrides, compatibility) in environments("TCG_DECODE_CHECK_A64") {
            let name = format!("{PROBE}a64_jit_{label}_{case}_fn");
            let module = probe_module(&name);
            let result = under(&overrides, || {
                Compiler::new(config.clone())
                    .with_codegen_license(permit_unlicensed())
                    .compile_module_to_jit(&module, &HashMap::new())
            });
            let expected = if follows_environment {
                compatibility
            } else {
                DecodeCheckBacking::Enforced
            };
            assert_lane_follows_its_encode(
                &format!("AArch64 JIT, {label}, {case}"),
                &name,
                "ENC-5",
                "AArch64::AlignNop:",
                expected,
                false,
                EncodeOrder::AfterTheGate {
                    refused: result.is_err(),
                },
            );
        }
    }
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes because it was silently refused. The policy comes from the
/// crate's plain-`#[cfg(test)]` helper: this file is declared under
/// `#[cfg(all(test, feature = "verify"))]`, which the production `Permit`
/// census reads as production code, so it must not spell `Permit` itself.
fn permit_unlicensed() -> crate::CodegenLicensePolicy {
    crate::license_test_support::permit_unlicensed()
}
