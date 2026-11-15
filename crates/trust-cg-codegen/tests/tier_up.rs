// trust-cg-codegen/tests/tier_up.rs - JIT tier-up through the compile service
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// A module compiled through `TierUpSession` + `ServiceTierBackend` at O0 on
// the caller's thread and O2 in the background:
//
// * every tier answers exactly what the Rust reference answers, on the same
//   inputs, before and after the upgrade;
// * each tier's code is BYTE-IDENTICAL to an ordinary compile-service compile
//   of the same request at that level (tier-up adds no code, only schedule);
// * a `TierEntryTable` swaps entry addresses to the new tier while keeping the
//   old tier's code callable;
// * a generation made stale, an object request, and a proof policy the host
//   cannot satisfy are refused by name, and the installed tier survives.

#![cfg(all(
    unix,
    any(target_arch = "x86_64", target_arch = "aarch64"),
    any(target_os = "macos", target_os = "linux")
))]

use std::collections::HashMap;
use std::sync::Arc;

use trust_cg_codegen::compile_service::{
    ArtifactKind, CompileGeneration, CompileGenerationFence, CompileRequest, CompileService,
    CompileStatus, InstalledArtifact, SourceKind,
};
use trust_cg_codegen::jit_contract::{
    AbiDescriptor, ArtifactManifestV1, Endianness, InvalidationKey, JitArtifactKind,
    LayoutManifest, ProofPolicy, TargetDescriptor,
};
use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::target::Target;
use trust_cg_codegen::tier_up::{
    ServiceTierBackend, TierEntryError, TierEntryTable, TierPlan, TierRefusal, TierStartFailure,
    TierUpPoll, TierUpSession, tier_request,
};
use trust_ir::{BinOp, ICmpOp, Module, Ty};
use trust_ir_build::ModuleBuilder;

const MIX: &str = "tier_up_mix";
const ANSWER: &str = "tier_up_answer";

type MixFn = extern "C" fn(i64, i64) -> i64;
type AnswerFn = extern "C" fn() -> i64;

/// `mix(x, n)`: n rounds of a 64-bit LCG step folded with a xorshift, a loop
/// the optimizer has something to do with. `answer()` returns 42.
fn module(name: &str) -> Module {
    let mut mb = ModuleBuilder::new(name);
    let mix_ty = mb.add_func_type(vec![Ty::I64, Ty::I64], vec![Ty::I64]);
    let mut fb = mb.function(MIX, mix_ty);
    let entry = fb.create_block();
    let x = fb.add_block_param(entry, Ty::I64);
    let n = fb.add_block_param(entry, Ty::I64);
    let header = fb.create_block();
    let acc = fb.add_block_param(header, Ty::I64);
    let i = fb.add_block_param(header, Ty::I64);
    let body = fb.create_block();
    let exit = fb.create_block();

    fb.switch_to_block(entry);
    let zero = fb.iconst(Ty::I64, 0);
    fb.br(header, vec![x, zero]);

    fb.switch_to_block(header);
    let more = fb.icmp(ICmpOp::Slt, Ty::I64, i, n);
    fb.condbr(more, body, vec![], exit, vec![]);

    fb.switch_to_block(body);
    let multiplier = fb.iconst(Ty::I64, 6_364_136_223_846_793_005);
    let increment = fb.iconst(Ty::I64, 1_442_695_040_888_963_407);
    let product = fb.mul(Ty::I64, acc, multiplier);
    let stepped = fb.add(Ty::I64, product, increment);
    let shift = fb.iconst(Ty::I64, 29);
    let high = fb.binop(BinOp::LShr, Ty::I64, stepped, shift);
    let folded = fb.binop(BinOp::Xor, Ty::I64, stepped, high);
    let with_index = fb.add(Ty::I64, folded, i);
    let one = fb.iconst(Ty::I64, 1);
    let next = fb.add(Ty::I64, i, one);
    fb.br(header, vec![with_index, next]);

    fb.switch_to_block(exit);
    fb.ret(vec![acc]);
    fb.build();

    let answer_ty = mb.add_func_type(vec![], vec![Ty::I64]);
    let mut fb = mb.function(ANSWER, answer_ty);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let answer = fb.iconst(Ty::I64, 42);
    fb.ret(vec![answer]);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

fn reference_mix(mut acc: i64, n: i64) -> i64 {
    let mut i = 0i64;
    while i < n {
        let stepped = acc
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        let folded = stepped ^ ((stepped as u64) >> 29) as i64;
        acc = folded.wrapping_add(i);
        i += 1;
    }
    acc
}

const INPUTS: [(i64, i64); 7] = [
    (0, 0),
    (1, 1),
    (-1, 3),
    (42, 1000),
    (i64::MIN, 17),
    (i64::MAX, 255),
    (0x5eed, 100_000),
];

fn call_mix(artifact: &InstalledArtifact) -> Vec<i64> {
    // SAFETY: `tier_up_mix` is `(i64, i64) -> i64` with the C ABI in every
    // tier (the session refuses a tier whose compiler-derived signature
    // differs), and `artifact` owns the code for the duration of each call.
    let mix = unsafe { artifact.buffer.get_fn_bound::<MixFn>(MIX) }.expect("mix resolves");
    INPUTS.iter().map(|&(x, n)| (*mix.as_ref())(x, n)).collect()
}

fn reference_outputs() -> Vec<i64> {
    INPUTS.iter().map(|&(x, n)| reference_mix(x, n)).collect()
}

/// The deterministic contract the compile service requires before it
/// exposes any executable artifact (`MissingManifest` otherwise): host
/// target, ABI and core layout as the host-JIT compiler derives them.
fn manifest(artifact_id: &str, generation: u64, proof_policy: ProofPolicy) -> ArtifactManifestV1 {
    let target = TargetDescriptor::for_trust_cg_host_jit();
    let abi =
        AbiDescriptor::for_trust_cg_target_os(Target::host(), target.operating_system.clone());
    let layout = LayoutManifest::lp64(Endianness::Little, Target::host().stack_alignment() as u16);
    let invalidation = InvalidationKey::new(
        format!("sha256:{artifact_id}-source"),
        "trust-cg-codegen:tier-up-test",
        target.checksum(),
        abi.checksum(),
        layout.checksum(),
        proof_policy.checksum(),
        generation,
    );
    ArtifactManifestV1::new(
        artifact_id,
        JitArtifactKind::ExecutableMemory,
        target,
        abi,
        layout,
        invalidation,
        proof_policy,
    )
}

fn request_with_policy(id: &str, proof_policy: ProofPolicy) -> CompileRequest {
    let mut request = CompileRequest::new(id, CompileGeneration::new(11))
        .with_artifact_manifest(manifest(id, 11, proof_policy.clone()));
    request.artifact_kind = ArtifactKind::ExecutableMemory;
    request.proof_policy = proof_policy;
    request.provenance.source_kind = SourceKind::TrustIrModule;
    request.provenance.source_fingerprint = Some(format!("sha256:{id}-source"));
    request
}

fn base_request(id: &str) -> CompileRequest {
    request_with_policy(id, ProofPolicy::disabled())
}

fn start(
    id: &str,
    request: CompileRequest,
    plan: TierPlan,
) -> Result<
    (
        TierUpSession<InstalledArtifact>,
        trust_cg_codegen::tier_up::TierInstall<InstalledArtifact>,
    ),
    TierStartFailure,
> {
    let module = Arc::new(module(id));
    let backend = ServiceTierBackend::for_request(
        permit_compile_service(),
        &request,
        module,
        &HashMap::new(),
    );
    TierUpSession::start(backend, request, plan)
}

fn payload_sha256(artifact: &InstalledArtifact) -> String {
    artifact
        .metadata
        .installed_payload_binding
        .as_ref()
        .expect("an installed artifact carries its payload binding")
        .native_payload_sha256
        .clone()
}

/// The ordinary compile-service compile of `tier`'s request, for byte
/// comparison with what the session delivered.
fn ordinary_compile(id: &str, base: &CompileRequest, tier: usize, level: OptLevel) -> String {
    let request = tier_request(base, tier, level, base.cancellation.clone());
    let response = permit_compile_service().compile(request, &module(id));
    assert_eq!(
        response.status,
        CompileStatus::Compiled,
        "{:?}",
        response.diagnostics
    );
    let installed = response
        .into_installed_artifact()
        .expect("the ordinary compile installs");
    payload_sha256(&installed)
}

#[test]
fn tiers_answer_the_reference_and_match_ordinary_compiles_byte_for_byte() {
    let id = "tier_up_answers";
    let request = base_request(id);
    let plan = TierPlan::new([OptLevel::O0, OptLevel::O2]).unwrap();
    let (mut session, tier0) = start(id, request.clone(), plan).expect("tier 0 compiles");
    assert_eq!((tier0.tier, tier0.opt_level), (0, OptLevel::O0));
    let expected = reference_outputs();
    assert_eq!(call_mix(&tier0.artifact), expected, "tier 0 (O0)");

    let tier1 = match session.wait() {
        TierUpPoll::Upgraded(install) => install,
        other => panic!("expected the O2 tier, got {other:?}"),
    };
    assert_eq!((tier1.tier, tier1.opt_level), (1, OptLevel::O2));
    assert_eq!(tier1.generation, CompileGeneration::new(11));
    assert_eq!(call_mix(&tier1.artifact), expected, "tier 1 (O2)");
    assert!(matches!(session.poll(), TierUpPoll::Complete));

    // The session exported what the compiler derived for this module.
    let symbols: Vec<&str> = session
        .exports()
        .iter()
        .map(|export| export.symbol.as_str())
        .collect();
    assert!(
        symbols.contains(&MIX) && symbols.contains(&ANSWER),
        "{symbols:?}"
    );

    // Each tier is exactly the ordinary compile at its level: tier-up
    // changes when code is compiled, never what is compiled.
    assert_eq!(
        payload_sha256(&tier0.artifact),
        ordinary_compile(id, &request, 0, OptLevel::O0)
    );
    assert_eq!(
        payload_sha256(&tier1.artifact),
        ordinary_compile(id, &request, 1, OptLevel::O2)
    );
    // And the two levels really are different code, or there is nothing to
    // tier up to.
    assert_ne!(
        payload_sha256(&tier0.artifact),
        payload_sha256(&tier1.artifact)
    );

    let report = session.shutdown();
    let json = report.to_json_value();
    assert_eq!(json["delivered_tier"], 1);
    assert_eq!(json["tiers"][0]["outcome"], "delivered");
    assert_eq!(json["tiers"][1]["outcome"], "delivered");
    assert_eq!(json["tiers"][1]["opt_level"], "O2");
}

#[test]
fn a_concurrent_start_delivers_the_same_bytes_as_a_sequential_one() {
    let id = "tier_up_concurrent";
    let request = base_request(id);
    let plan = TierPlan::new([OptLevel::O0, OptLevel::O2]).unwrap();
    let backend = ServiceTierBackend::for_request(
        permit_compile_service(),
        &request,
        Arc::new(module(id)),
        &HashMap::new(),
    );
    let (mut session, tier0) =
        TierUpSession::start_concurrent(backend, request.clone(), plan).expect("tier 0 compiles");
    let tier1 = match session.wait() {
        TierUpPoll::Upgraded(install) => install,
        other => panic!("expected the O2 tier, got {other:?}"),
    };
    let expected = reference_outputs();
    assert_eq!(call_mix(&tier0.artifact), expected);
    assert_eq!(call_mix(&tier1.artifact), expected);
    assert_eq!(
        payload_sha256(&tier0.artifact),
        ordinary_compile(id, &request, 0, OptLevel::O0)
    );
    assert_eq!(
        payload_sha256(&tier1.artifact),
        ordinary_compile(id, &request, 1, OptLevel::O2)
    );
    assert!(matches!(session.wait(), TierUpPoll::Complete));
}

#[test]
fn an_entry_table_swaps_to_the_new_tier_and_keeps_the_old_one_callable() {
    let id = "tier_up_entry_table";
    let plan = TierPlan::new([OptLevel::O0, OptLevel::O1, OptLevel::O2]).unwrap();
    let (mut session, tier0) = start(id, base_request(id), plan).expect("tier 0 compiles");
    let table = TierEntryTable::new([MIX, ANSWER], tier0.tier, &tier0.artifact).unwrap();
    table.prepare_current_thread();
    let mix_index = table.index_of(MIX).unwrap();
    let answer_index = table.index_of(ANSWER).unwrap();
    let expected = reference_outputs();
    let call_table = |table: &TierEntryTable| -> Vec<i64> {
        let address = table.entry(mix_index).unwrap();
        // SAFETY: every tier's `tier_up_mix` is `(i64, i64) -> i64`, C ABI,
        // and the table keeps every installed tier mapped while it lives.
        let mix: MixFn = unsafe { std::mem::transmute::<*const u8, MixFn>(address) };
        INPUTS.iter().map(|&(x, n)| mix(x, n)).collect()
    };
    assert_eq!(call_table(&table), expected);
    let tier0_mix = table.entry(mix_index).unwrap();

    let mut installed = vec![tier0];
    loop {
        match session.wait() {
            TierUpPoll::Upgraded(install) => {
                table.install(install.tier, &install.artifact).unwrap();
                assert_eq!(table.installed_tier(), install.tier);
                assert_eq!(call_table(&table), expected, "tier {}", install.tier);
                installed.push(install);
            }
            TierUpPoll::Complete => break,
            other => panic!("unexpected {other:?}"),
        }
    }
    assert_eq!(table.installed_tier(), 2);
    assert_ne!(table.entry(mix_index).unwrap(), tier0_mix);

    // Re-installing an older tier is refused and changes nothing.
    let before = table.entry(mix_index).unwrap();
    assert!(matches!(
        table.install(0, &installed[0].artifact),
        Err(TierEntryError::NotNewer {
            tier: 0,
            installed: 2
        })
    ));
    assert_eq!(table.entry(mix_index).unwrap(), before);

    // Dropping every delivered artifact leaves the table's code mapped: the
    // tier-0 address a caller loaded before the swap still runs.
    drop(installed);
    // SAFETY: as above; the table still holds tier 0's execution lease.
    let old_mix: MixFn = unsafe { std::mem::transmute::<*const u8, MixFn>(tier0_mix) };
    assert_eq!(old_mix(42, 1000), reference_mix(42, 1000));
    // SAFETY: `tier_up_answer` is `() -> i64`, C ABI, retained by the table.
    let answer: AnswerFn =
        unsafe { std::mem::transmute::<*const u8, AnswerFn>(table.entry(answer_index).unwrap()) };
    assert_eq!(answer(), 42);

    assert!(matches!(
        TierEntryTable::new(["tier_up_missing"], 0, &{
            let id = "tier_up_entry_table_missing";
            start(id, base_request(id), TierPlan::single(OptLevel::O0))
                .unwrap()
                .1
                .artifact
        }),
        Err(TierEntryError::Unresolved { .. })
    ));
}

#[test]
fn a_background_installer_swaps_entries_under_a_calling_thread() {
    let id = "tier_up_installer";
    let plan = TierPlan::new([OptLevel::O0, OptLevel::O1, OptLevel::O2]).unwrap();
    let (session, tier0) = start(id, base_request(id), plan).expect("tier 0 compiles");
    let table = Arc::new(TierEntryTable::new([MIX], tier0.tier, &tier0.artifact).unwrap());
    // The table's execution lease keeps tier 0 mapped; the artifact may go.
    drop(tier0);
    let installer_table = Arc::clone(&table);
    let installer = session.install_with(move |install| {
        installer_table
            .install(install.tier, &install.artifact)
            .map_err(|error| error.to_string())
    });
    let caller_table = Arc::clone(&table);
    let caller = std::thread::spawn(move || {
        caller_table.prepare_current_thread();
        let deadline = std::time::Instant::now() + std::time::Duration::from_secs(300);
        let mut tiers_called = std::collections::BTreeSet::new();
        loop {
            let tier = caller_table.installed_tier();
            let address = caller_table.entry(0).expect("entry 0");
            // SAFETY: every tier's `tier_up_mix` is `(i64, i64) -> i64`, C
            // ABI, kept mapped by the table for its lifetime.
            let mix: MixFn = unsafe { std::mem::transmute::<*const u8, MixFn>(address) };
            for &(x, n) in &INPUTS {
                assert_eq!(mix(x, n), reference_mix(x, n), "tier {tier}");
            }
            tiers_called.insert(tier);
            if tier == 2 || std::time::Instant::now() > deadline {
                return tiers_called;
            }
        }
    });
    let report = installer.join().expect("installer thread");
    let tiers_called = caller.join().expect("caller thread");
    assert_eq!(report.delivered_tier, 2);
    assert_eq!(table.installed_tier(), 2);
    assert!(tiers_called.contains(&2), "{tiers_called:?}");
}

#[test]
fn a_generation_superseded_before_the_upgrade_arrives_is_never_delivered() {
    let id = "tier_up_stale";
    let fence = CompileGenerationFence::new();
    let mut request = base_request(id);
    request.generation_fence = Some(fence.clone());
    let plan = TierPlan::new([OptLevel::O0, OptLevel::O2]).unwrap();
    let (mut session, tier0) = start(id, request, plan).expect("tier 0 compiles");
    fence.mark_stale_before(CompileGeneration::new(12));
    // Refused at whichever gate sees it first: before the O2 compile, after
    // it, or at this poll. Never delivered.
    match session.wait() {
        TierUpPoll::Refused {
            tier: 1,
            refusal: TierRefusal::Stale,
            ..
        } => {}
        other => panic!("expected a stale refusal, got {other:?}"),
    }
    assert_eq!(session.delivered_tier(), 0);
    // The installed tier is untouched.
    assert_eq!(call_mix(&tier0.artifact), reference_outputs());
    let report = session.shutdown();
    assert_eq!(
        report.to_json_value()["tiers"][1]["code"],
        "tier_up.stale_generation"
    );
}

#[test]
fn requests_the_service_would_not_install_are_refused_at_tier_zero() {
    let id = "tier_up_object";
    let mut request = base_request(id);
    request.artifact_kind = ArtifactKind::Object;
    match start(id, request, TierPlan::single(OptLevel::O0)) {
        Err(TierStartFailure::Failed(failure)) => {
            assert_eq!(failure.code(), "tier_up.not_executable_memory");
        }
        other => panic!("expected an object request to be refused, got {other:?}"),
    }

    // A proof policy naming a solver nothing on this route certifies with:
    // the compile service refuses to install the artifact, so tier-up
    // delivers nothing either — the service's refusal, by its own code.
    let id = "tier_up_proof";
    let request = request_with_policy(
        id,
        ProofPolicy::require_certificates(["tier-up-no-such-solver"]),
    );
    match start(
        id,
        request,
        TierPlan::new([OptLevel::O0, OptLevel::O2]).unwrap(),
    ) {
        Err(TierStartFailure::Failed(failure)) => {
            assert!(!failure.state.is_installable(), "{failure:?}");
            assert!(!failure.diagnostics.is_empty(), "{failure:?}");
        }
        Ok((_, install)) => panic!(
            "a policy no certificate satisfies must not install: {:?}",
            install.artifact.metadata.proofs
        ),
        Err(other) => panic!("unexpected {other:?}"),
    }
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which the compile service REFUSES by default (roadmap
/// WS7.5, decision gate DG-73). Its services state `Permit` explicitly, so no
/// tier is installed, or refused, because the license silently refused it.
fn permit_compile_service() -> CompileService {
    CompileService::new(trust_cg_codegen::compile_service::CompileServiceConfig {
        codegen_license: trust_cg_codegen::CodegenLicensePolicy::default()
            .with_unlicensed(trust_cg_codegen::UnlicensedBodyPolicy::Permit),
        ..trust_cg_codegen::compile_service::CompileServiceConfig::default()
    })
}
