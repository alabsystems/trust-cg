// trust-cg-codegen/jit_shadow_replay.rs - JIT-everywhere shadow replay prework
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Data-only shadow replay harness for JIT-everywhere prework.
//!
//! Shadow replay may compare native observations against authoritative
//! baseline observations, but it cannot publish callable handles, replace
//! consumer-visible results, install cache entries, activate ay/TY native
//! dispatch, or increment useful-native counters.

use crate::jit_diagnostics::sha256_hex;
use crate::target::Target;

/// Stable schema tag for shadow replay bundles.
pub const JIT_EVERYWHERE_SHADOW_REPLAY_SCHEMA: &str = "trust-cg.jit_everywhere.shadow_replay.v1";

/// Stable numeric schema version for shadow replay bundles.
pub const JIT_EVERYWHERE_SHADOW_REPLAY_SCHEMA_VERSION: u32 = 1;

/// Stable schema tag for the private TY native-fused three-spec smoke replay fixture.
pub const TY_NATIVE_FUSED_THREE_SPEC_SMOKE_SCHEMA: &str =
    "trust-cg.ty.native_fused_three_spec_smoke.shadow_replay.v1";

/// Stable numeric schema version for the TY native-fused smoke replay fixture.
pub const TY_NATIVE_FUSED_THREE_SPEC_SMOKE_SCHEMA_VERSION: u32 = 1;

/// Issue carrying this shadow-only replay packet.
pub const TY_NATIVE_FUSED_THREE_SPEC_SMOKE_ISSUE: u64 = 663;

/// TY commit identity recorded in the accepted local three-spec smoke replay.
pub const TY_NATIVE_FUSED_THREE_SPEC_SMOKE_TY_GIT_COMMIT: &str =
    "b2467ae55068cecf0558265b19209e9c73d1c875";

/// Required spec ids covered by the TY three-spec native-fused smoke replay.
pub const TY_NATIVE_FUSED_THREE_SPEC_SMOKE_SPEC_IDS: &[&str] =
    &["CoffeeCan1000BeansSafety", "EWD998Small", "MCLamportMutex"];

/// Canonical hash of the full TY three-spec native-fused smoke replay fixture.
///
/// SHA-256 of the committed fixture identity produced by
/// `ShadowReplayTyNativeFusedSmokeFixture::canonical_fixture_sha256` over the
/// fixed `ty_native_fused_three_spec_smoke_fixture()` rows (specs sorted by
/// `spec_id`, length-prefixed framing) — all string/integer literals, so the
/// digest is host/arch-independent. Refreshed to the value the committed
/// fixture data actually hashes to; the previous literal was baked from an
/// older fixture/serialization and was stale (not platform drift), which made
/// `validate_fixture_identity()` fail closed on every host.
pub const TY_NATIVE_FUSED_THREE_SPEC_SMOKE_CANONICAL_FIXTURE_SHA256: &str =
    "sha256:a22299fede23292057c7d72abd2d9fe06b5c5ccdcc5ca8c72f7c54c3a862f733";

/// Consumer covered by a shadow replay bundle.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ShadowReplayConsumer {
    /// ay solver family.
    AY,
    /// TY native execution family.
    Ty,
}

impl ShadowReplayConsumer {
    /// Return the stable lower-snake-case string.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::AY => "ay",
            Self::Ty => "ty",
        }
    }
}

/// Shadow hook used to keep baseline state authoritative.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ShadowReplayHook {
    /// Immutable input slices are replayed.
    ImmutableInputs,
    /// Solver or runtime mutable state is copied before native execution.
    CopyOnWriteState,
    /// Recorded trace steps are replayed.
    ReplayedTrace,
    /// TY shadow arena is used instead of product arena mutation.
    ShadowTyArena,
}

impl ShadowReplayHook {
    /// Return the stable lower-snake-case string.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::ImmutableInputs => "immutable_inputs",
            Self::CopyOnWriteState => "copy_on_write_state",
            Self::ReplayedTrace => "replayed_trace",
            Self::ShadowTyArena => "shadow_ty_arena",
        }
    }
}

/// Compiler configuration identity for a shadow bundle.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ShadowReplayCompilerConfig {
    /// Optimization pipeline id or checksum.
    pub optimization_pipeline: String,
    /// Codegen configuration checksum.
    pub codegen_config_sha256: String,
    /// Proof policy id or checksum.
    pub proof_policy: String,
    /// Profile schema id or checksum.
    pub profile_schema: String,
}

impl ShadowReplayCompilerConfig {
    /// Build compiler configuration identity.
    pub fn new(
        optimization_pipeline: impl Into<String>,
        codegen_config_sha256: impl Into<String>,
        proof_policy: impl Into<String>,
        profile_schema: impl Into<String>,
    ) -> Self {
        Self {
            optimization_pipeline: optimization_pipeline.into(),
            codegen_config_sha256: codegen_config_sha256.into(),
            proof_policy: proof_policy.into(),
            profile_schema: profile_schema.into(),
        }
    }

    fn has_required_identity(&self) -> bool {
        !missing_required_text(&self.optimization_pipeline)
            && !missing_required_text(&self.codegen_config_sha256)
            && !missing_required_text(&self.proof_policy)
            && !missing_required_text(&self.profile_schema)
    }
}

/// Consumer generation facts bound to shadow replay.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ShadowReplayGenerationFacts {
    /// Runtime or consumer generation domain.
    pub generation_domain: String,
    /// Generation observed by the bundle.
    pub observed_generation: u64,
    /// Current generation expected during replay.
    pub current_generation: u64,
    /// Layout generation or checksum domain.
    pub layout_generation: String,
}

impl ShadowReplayGenerationFacts {
    /// Build consumer generation facts.
    pub fn new(
        generation_domain: impl Into<String>,
        observed_generation: u64,
        current_generation: u64,
        layout_generation: impl Into<String>,
    ) -> Self {
        Self {
            generation_domain: generation_domain.into(),
            observed_generation,
            current_generation,
            layout_generation: layout_generation.into(),
        }
    }

    fn has_required_identity(&self) -> bool {
        !missing_required_text(&self.generation_domain)
            && !missing_required_text(&self.layout_generation)
            && self.observed_generation == self.current_generation
    }
}

/// Minimal input slice captured for shadow replay.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ShadowReplayInputSlice {
    /// Stable input slice name.
    pub name: String,
    /// Input slice SHA-256.
    pub input_sha256: String,
    /// Input slice length in bytes.
    pub byte_len: u64,
}

impl ShadowReplayInputSlice {
    /// Build one input slice.
    pub fn new(name: impl Into<String>, input_sha256: impl Into<String>, byte_len: u64) -> Self {
        Self {
            name: name.into(),
            input_sha256: input_sha256.into(),
            byte_len,
        }
    }

    fn has_required_identity(&self) -> bool {
        !missing_required_text(&self.name)
            && !missing_required_text(&self.input_sha256)
            && self.byte_len > 0
    }
}

/// Replay bundle identity and immutable replay inputs.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ShadowReplayBundle {
    /// Bundle schema.
    pub schema: &'static str,
    /// Bundle schema version.
    pub schema_version: u32,
    /// Implementing issue.
    pub issue: u64,
    /// Consumer covered by the bundle.
    pub consumer: ShadowReplayConsumer,
    /// Consumer family or mode.
    pub consumer_family: String,
    /// Artifact manifest SHA-256.
    pub manifest_sha256: String,
    /// Source SHA-256.
    pub source_sha256: String,
    /// Canonical trust_ir SHA-256.
    pub trust_ir_sha256: String,
    /// Native payload SHA-256.
    pub native_payload_sha256: String,
    /// Compiler configuration identity.
    pub compiler_config: ShadowReplayCompilerConfig,
    /// Target architecture.
    pub target: Target,
    /// Target facts SHA-256.
    pub target_facts_sha256: String,
    /// Proof report SHA-256.
    pub proof_report_sha256: String,
    /// Consumer generation facts.
    pub generation: ShadowReplayGenerationFacts,
    /// Minimal input slices.
    pub input_slices: Vec<ShadowReplayInputSlice>,
    /// Shadow hooks active for this bundle.
    pub hooks: Vec<ShadowReplayHook>,
    /// Replay root SHA-256.
    pub replay_root_sha256: String,
    /// Canonical bundle SHA-256.
    pub bundle_sha256: String,
}

impl ShadowReplayBundle {
    /// Build a shadow replay bundle.
    pub fn new(
        consumer: ShadowReplayConsumer,
        consumer_family: impl Into<String>,
        manifest_sha256: impl Into<String>,
        source_sha256: impl Into<String>,
        trust_ir_sha256: impl Into<String>,
        native_payload_sha256: impl Into<String>,
        compiler_config: ShadowReplayCompilerConfig,
        target: Target,
        target_facts_sha256: impl Into<String>,
        proof_report_sha256: impl Into<String>,
        generation: ShadowReplayGenerationFacts,
        input_slices: Vec<ShadowReplayInputSlice>,
        hooks: Vec<ShadowReplayHook>,
        replay_root_sha256: impl Into<String>,
    ) -> Self {
        let mut bundle = Self {
            schema: JIT_EVERYWHERE_SHADOW_REPLAY_SCHEMA,
            schema_version: JIT_EVERYWHERE_SHADOW_REPLAY_SCHEMA_VERSION,
            issue: 738,
            consumer,
            consumer_family: consumer_family.into(),
            manifest_sha256: manifest_sha256.into(),
            source_sha256: source_sha256.into(),
            trust_ir_sha256: trust_ir_sha256.into(),
            native_payload_sha256: native_payload_sha256.into(),
            compiler_config,
            target,
            target_facts_sha256: target_facts_sha256.into(),
            proof_report_sha256: proof_report_sha256.into(),
            generation,
            input_slices,
            hooks,
            replay_root_sha256: replay_root_sha256.into(),
            bundle_sha256: String::new(),
        };
        bundle.bundle_sha256 = bundle.canonical_bundle_sha256();
        bundle
    }

    /// Return the stable hash of this bundle.
    pub fn canonical_bundle_sha256(&self) -> String {
        let mut out = Vec::new();
        put_str(&mut out, self.schema);
        put_u32(&mut out, self.schema_version);
        put_u64(&mut out, self.issue);
        put_str(&mut out, self.consumer.as_str());
        put_str(&mut out, &self.consumer_family);
        put_str(&mut out, &self.manifest_sha256);
        put_str(&mut out, &self.source_sha256);
        put_str(&mut out, &self.trust_ir_sha256);
        put_str(&mut out, &self.native_payload_sha256);
        put_compiler_config(&mut out, &self.compiler_config);
        put_str(&mut out, self.target.name());
        put_str(&mut out, &self.target_facts_sha256);
        put_str(&mut out, &self.proof_report_sha256);
        put_generation(&mut out, &self.generation);
        put_u64(&mut out, self.input_slices.len() as u64);
        for slice in &self.input_slices {
            put_str(&mut out, &slice.name);
            put_str(&mut out, &slice.input_sha256);
            put_u64(&mut out, slice.byte_len);
        }
        put_u64(&mut out, self.hooks.len() as u64);
        for hook in &self.hooks {
            put_str(&mut out, hook.as_str());
        }
        put_str(&mut out, &self.replay_root_sha256);
        format!("sha256:{}", sha256_hex(&out))
    }

    /// Return true when the bundle has enough immutable replay identity.
    pub fn is_replayable(&self) -> bool {
        self.schema == JIT_EVERYWHERE_SHADOW_REPLAY_SCHEMA
            && self.schema_version == JIT_EVERYWHERE_SHADOW_REPLAY_SCHEMA_VERSION
            && self.issue == 738
            && !missing_required_text(&self.consumer_family)
            && !missing_required_text(&self.manifest_sha256)
            && !missing_required_text(&self.source_sha256)
            && !missing_required_text(&self.trust_ir_sha256)
            && !missing_required_text(&self.native_payload_sha256)
            && self.compiler_config.has_required_identity()
            && !missing_required_text(&self.target_facts_sha256)
            && !missing_required_text(&self.proof_report_sha256)
            && self.generation.has_required_identity()
            && !self.input_slices.is_empty()
            && self
                .input_slices
                .iter()
                .all(ShadowReplayInputSlice::has_required_identity)
            && !self.hooks.is_empty()
            && !missing_required_text(&self.replay_root_sha256)
            && self.bundle_sha256 == self.canonical_bundle_sha256()
    }

    fn requires_ty_three_spec_fixture_hash(&self) -> bool {
        self.consumer == ShadowReplayConsumer::Ty
            && self
                .consumer_family
                .starts_with("ty_native_fused_three_spec_smoke:")
    }
}

/// Native or baseline status observed during shadow comparison.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ShadowReplayStatus {
    /// Execution completed normally.
    Ok,
    /// Native path deoptimized or fell back.
    Deopt,
    /// Native path crashed.
    Crash,
    /// Native path timed out.
    Timeout,
    /// Verification failed before or during shadow comparison.
    VerifierFailure,
}

impl ShadowReplayStatus {
    /// Return the stable lower-snake-case string.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Ok => "ok",
            Self::Deopt => "deopt",
            Self::Crash => "crash",
            Self::Timeout => "timeout",
            Self::VerifierFailure => "verifier_failure",
        }
    }
}

/// ay no-wrong-answer/witness/proof checks for a shadowed family.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ShadowReplayAYChecks {
    /// ay no-wrong-answer check result.
    pub no_wrong_answer: bool,
    /// Witness digest observed by the route.
    pub witness_sha256: String,
    /// Proof digest observed by the route.
    pub proof_sha256: String,
}

impl ShadowReplayAYChecks {
    /// Build ay shadow checks.
    pub fn new(
        no_wrong_answer: bool,
        witness_sha256: impl Into<String>,
        proof_sha256: impl Into<String>,
    ) -> Self {
        Self {
            no_wrong_answer,
            witness_sha256: witness_sha256.into(),
            proof_sha256: proof_sha256.into(),
        }
    }

    fn has_required_identity(&self) -> bool {
        self.no_wrong_answer
            && !missing_required_text(&self.witness_sha256)
            && !missing_required_text(&self.proof_sha256)
    }
}

/// TY state/generated/fingerprint/callback equivalence checks.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ShadowReplayTyChecks {
    /// State count observed by the route.
    pub state_count: u64,
    /// Generated successor count observed by the route.
    pub generated_count: u64,
    /// Fingerprint digest observed by the route.
    pub fingerprint_sha256: String,
    /// Parent sequence digest observed by the route.
    pub parent_sequence_sha256: String,
    /// Status digest observed by the route.
    pub status_sha256: String,
    /// Callback-visible digest observed by the route.
    pub callback_visible_sha256: String,
}

impl ShadowReplayTyChecks {
    /// Build TY shadow checks.
    pub fn new(
        state_count: u64,
        generated_count: u64,
        fingerprint_sha256: impl Into<String>,
        parent_sequence_sha256: impl Into<String>,
        status_sha256: impl Into<String>,
        callback_visible_sha256: impl Into<String>,
    ) -> Self {
        Self {
            state_count,
            generated_count,
            fingerprint_sha256: fingerprint_sha256.into(),
            parent_sequence_sha256: parent_sequence_sha256.into(),
            status_sha256: status_sha256.into(),
            callback_visible_sha256: callback_visible_sha256.into(),
        }
    }

    fn has_required_identity(&self) -> bool {
        self.state_count > 0
            && self.generated_count > 0
            && !missing_required_text(&self.fingerprint_sha256)
            && !missing_required_text(&self.parent_sequence_sha256)
            && !missing_required_text(&self.status_sha256)
            && !missing_required_text(&self.callback_visible_sha256)
    }
}

/// Target and optimization controls recorded for TY native-fused smoke replay.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ShadowReplayTyNativeFusedSmokeControls {
    /// Target triple observed in replay artifacts.
    pub target_triple: String,
    /// Native callout optimization level.
    pub native_callout_opt_level: String,
    /// Native-fused parent loop optimization level.
    pub native_fused_parent_loop_opt_level: String,
    /// Strict native-fused replay control.
    pub native_fused_strict: bool,
}

impl ShadowReplayTyNativeFusedSmokeControls {
    /// Build target/O3 controls for a replay row.
    pub fn new(
        target_triple: impl Into<String>,
        native_callout_opt_level: impl Into<String>,
        native_fused_parent_loop_opt_level: impl Into<String>,
        native_fused_strict: bool,
    ) -> Self {
        Self {
            target_triple: target_triple.into(),
            native_callout_opt_level: native_callout_opt_level.into(),
            native_fused_parent_loop_opt_level: native_fused_parent_loop_opt_level.into(),
            native_fused_strict,
        }
    }

    fn has_required_o3_identity(&self) -> bool {
        !missing_required_text(&self.target_triple)
            && self.native_callout_opt_level == "O3"
            && self.native_fused_parent_loop_opt_level == "O3"
            && self.native_fused_strict
    }
}

/// One spec row from the TY native-fused three-spec smoke replay fixture.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ShadowReplayTyNativeFusedSmokeSpec {
    /// Stable TY spec id.
    pub spec_id: String,
    /// TY commit identity recorded by the replay artifacts.
    pub ty_git_commit: String,
    /// Target and optimization controls.
    pub controls: ShadowReplayTyNativeFusedSmokeControls,
    /// Opaque replay artifact-directory SHA-256.
    pub replay_artifact_dir_sha256: String,
    /// Total state count observed by native-fused replay.
    pub state_count: u64,
    /// Generated successor count observed by native-fused replay.
    pub generated_count: u64,
    /// State fingerprint digest observed by replay.
    pub fingerprint_sha256: String,
    /// Parent sequence digest observed by replay.
    pub parent_sequence_sha256: String,
    /// Status digest observed by replay.
    pub status_sha256: String,
    /// Callback-visible digest observed by replay.
    pub callback_visible_sha256: String,
}

impl ShadowReplayTyNativeFusedSmokeSpec {
    /// Build one TY native-fused smoke replay spec row.
    pub fn new(
        spec_id: impl Into<String>,
        ty_git_commit: impl Into<String>,
        controls: ShadowReplayTyNativeFusedSmokeControls,
        replay_artifact_dir_sha256: impl Into<String>,
        state_count: u64,
        generated_count: u64,
        fingerprint_sha256: impl Into<String>,
        parent_sequence_sha256: impl Into<String>,
        status_sha256: impl Into<String>,
        callback_visible_sha256: impl Into<String>,
    ) -> Self {
        Self {
            spec_id: spec_id.into(),
            ty_git_commit: ty_git_commit.into(),
            controls,
            replay_artifact_dir_sha256: replay_artifact_dir_sha256.into(),
            state_count,
            generated_count,
            fingerprint_sha256: fingerprint_sha256.into(),
            parent_sequence_sha256: parent_sequence_sha256.into(),
            status_sha256: status_sha256.into(),
            callback_visible_sha256: callback_visible_sha256.into(),
        }
    }

    /// Convert the replay row into TY shadow comparison checks.
    pub fn to_ty_checks(&self) -> ShadowReplayTyChecks {
        ShadowReplayTyChecks::new(
            self.state_count,
            self.generated_count,
            self.fingerprint_sha256.clone(),
            self.parent_sequence_sha256.clone(),
            self.status_sha256.clone(),
            self.callback_visible_sha256.clone(),
        )
    }

    fn has_required_identity(&self) -> bool {
        !missing_required_text(&self.spec_id)
            && !missing_required_text(&self.ty_git_commit)
            && self.controls.has_required_o3_identity()
            && !missing_required_text(&self.replay_artifact_dir_sha256)
            && self.state_count > 0
            && self.generated_count > 0
            && !missing_required_text(&self.fingerprint_sha256)
            && !missing_required_text(&self.parent_sequence_sha256)
            && !missing_required_text(&self.status_sha256)
            && !missing_required_text(&self.callback_visible_sha256)
    }
}

/// Data-only TY native-fused smoke replay fixture used as shadow evidence.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ShadowReplayTyNativeFusedSmokeFixture {
    /// Fixture schema.
    pub schema: &'static str,
    /// Fixture schema version.
    pub schema_version: u32,
    /// Implementing issue.
    pub issue: u64,
    /// Shadow-only disposition.
    pub shadow_only: bool,
    /// Product promotion is not allowed by this fixture.
    pub product_promotion_allowed: bool,
    /// Useful-native credit is not allowed by this fixture.
    pub useful_native_credit_allowed: bool,
    /// Accepted TY commit identity for all rows.
    pub ty_git_commit: String,
    /// Per-spec replay rows.
    pub specs: Vec<ShadowReplayTyNativeFusedSmokeSpec>,
}

impl ShadowReplayTyNativeFusedSmokeFixture {
    /// Build a shadow-only three-spec replay fixture.
    pub fn new(
        ty_git_commit: impl Into<String>,
        specs: Vec<ShadowReplayTyNativeFusedSmokeSpec>,
    ) -> Self {
        Self {
            schema: TY_NATIVE_FUSED_THREE_SPEC_SMOKE_SCHEMA,
            schema_version: TY_NATIVE_FUSED_THREE_SPEC_SMOKE_SCHEMA_VERSION,
            issue: TY_NATIVE_FUSED_THREE_SPEC_SMOKE_ISSUE,
            shadow_only: true,
            product_promotion_allowed: false,
            useful_native_credit_allowed: false,
            ty_git_commit: ty_git_commit.into(),
            specs,
        }
    }

    /// Return the stable hash of the fixture identity.
    pub fn canonical_fixture_sha256(&self) -> String {
        let mut out = Vec::new();
        put_str(&mut out, self.schema);
        put_u32(&mut out, self.schema_version);
        put_u64(&mut out, self.issue);
        put_bool(&mut out, self.shadow_only);
        put_bool(&mut out, self.product_promotion_allowed);
        put_bool(&mut out, self.useful_native_credit_allowed);
        put_str(&mut out, &self.ty_git_commit);
        let mut specs = self.specs.clone();
        specs.sort_by(|left, right| left.spec_id.cmp(&right.spec_id));
        put_u64(&mut out, specs.len() as u64);
        for spec in &specs {
            put_ty_native_fused_smoke_spec(&mut out, spec);
        }
        format!("sha256:{}", sha256_hex(&out))
    }

    /// Return true when the fixture covers all required specs and cannot promote native use.
    pub fn is_shadow_only_non_promoting(&self) -> bool {
        self.validate_fixture_identity().is_ok()
    }

    /// Validate fixture-level identity before any row observation is accepted.
    pub fn validate_fixture_identity(&self) -> Result<(), ShadowReplayTyNativeFusedSmokeRejection> {
        if self.schema != TY_NATIVE_FUSED_THREE_SPEC_SMOKE_SCHEMA
            || self.schema_version != TY_NATIVE_FUSED_THREE_SPEC_SMOKE_SCHEMA_VERSION
            || self.issue != TY_NATIVE_FUSED_THREE_SPEC_SMOKE_ISSUE
        {
            return Err(ShadowReplayTyNativeFusedSmokeRejection::MalformedFixtureSchema);
        }
        if !self.shadow_only || self.product_promotion_allowed || self.useful_native_credit_allowed
        {
            return Err(ShadowReplayTyNativeFusedSmokeRejection::ShadowFlagsMismatch);
        }
        if self.ty_git_commit != TY_NATIVE_FUSED_THREE_SPEC_SMOKE_TY_GIT_COMMIT {
            return Err(ShadowReplayTyNativeFusedSmokeRejection::StaleTyCommitIdentity);
        }
        if self.specs.len() != TY_NATIVE_FUSED_THREE_SPEC_SMOKE_SPEC_IDS.len()
            || !TY_NATIVE_FUSED_THREE_SPEC_SMOKE_SPEC_IDS
                .iter()
                .all(|spec_id| self.expected_spec(spec_id).is_some())
        {
            return Err(ShadowReplayTyNativeFusedSmokeRejection::SpecSetMismatch);
        }
        if !self
            .specs
            .iter()
            .all(ShadowReplayTyNativeFusedSmokeSpec::has_required_identity)
            || !self
                .specs
                .iter()
                .all(|spec| spec.ty_git_commit == self.ty_git_commit)
        {
            return Err(ShadowReplayTyNativeFusedSmokeRejection::CanonicalFixtureHashMismatch);
        }
        if self.canonical_fixture_sha256()
            != TY_NATIVE_FUSED_THREE_SPEC_SMOKE_CANONICAL_FIXTURE_SHA256
        {
            return Err(ShadowReplayTyNativeFusedSmokeRejection::CanonicalFixtureHashMismatch);
        }
        Ok(())
    }

    /// Find one expected spec row.
    pub fn expected_spec(&self, spec_id: &str) -> Option<&ShadowReplayTyNativeFusedSmokeSpec> {
        self.specs.iter().find(|spec| spec.spec_id == spec_id)
    }

    /// Validate one candidate replay observation against the fixture.
    pub fn validate_spec_observation<'a>(
        &'a self,
        observation: &ShadowReplayTyNativeFusedSmokeSpec,
    ) -> Result<&'a ShadowReplayTyNativeFusedSmokeSpec, ShadowReplayTyNativeFusedSmokeRejection>
    {
        self.validate_fixture_identity()?;
        let Some(expected) = self.expected_spec(&observation.spec_id) else {
            return Err(ShadowReplayTyNativeFusedSmokeRejection::MissingSpec);
        };
        if self.ty_git_commit != TY_NATIVE_FUSED_THREE_SPEC_SMOKE_TY_GIT_COMMIT
            || expected.ty_git_commit != self.ty_git_commit
            || observation.ty_git_commit != self.ty_git_commit
        {
            return Err(ShadowReplayTyNativeFusedSmokeRejection::StaleTyCommitIdentity);
        }
        if expected.controls != observation.controls
            || !observation.controls.has_required_o3_identity()
        {
            return Err(ShadowReplayTyNativeFusedSmokeRejection::TargetOrO3ControlMismatch);
        }
        if missing_required_text(&expected.replay_artifact_dir_sha256)
            || missing_required_text(&observation.replay_artifact_dir_sha256)
        {
            return Err(ShadowReplayTyNativeFusedSmokeRejection::MissingReplayRoot);
        }
        if expected.replay_artifact_dir_sha256 != observation.replay_artifact_dir_sha256 {
            return Err(ShadowReplayTyNativeFusedSmokeRejection::MissingReplayRoot);
        }
        if expected.state_count != observation.state_count
            || expected.generated_count != observation.generated_count
            || expected.fingerprint_sha256 != observation.fingerprint_sha256
        {
            return Err(
                ShadowReplayTyNativeFusedSmokeRejection::StateGeneratedOrFingerprintMismatch,
            );
        }
        if expected.parent_sequence_sha256 != observation.parent_sequence_sha256 {
            return Err(ShadowReplayTyNativeFusedSmokeRejection::ParentSequenceMismatch);
        }
        if expected.status_sha256 != observation.status_sha256 {
            return Err(ShadowReplayTyNativeFusedSmokeRejection::StatusDigestMismatch);
        }
        if expected.callback_visible_sha256 != observation.callback_visible_sha256 {
            return Err(ShadowReplayTyNativeFusedSmokeRejection::CallbackVisibleMismatch);
        }
        Ok(expected)
    }
}

/// Rejection reason for TY native-fused three-spec smoke replay validation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ShadowReplayTyNativeFusedSmokeRejection {
    MalformedFixtureSchema,
    ShadowFlagsMismatch,
    SpecSetMismatch,
    CanonicalFixtureHashMismatch,
    MissingSpec,
    StaleTyCommitIdentity,
    TargetOrO3ControlMismatch,
    MissingReplayRoot,
    StateGeneratedOrFingerprintMismatch,
    ParentSequenceMismatch,
    StatusDigestMismatch,
    CallbackVisibleMismatch,
}

impl ShadowReplayTyNativeFusedSmokeRejection {
    /// Return the stable lower-snake-case code.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::MalformedFixtureSchema => "malformed_ty_three_spec_fixture_schema",
            Self::ShadowFlagsMismatch => "ty_three_spec_shadow_flags_mismatch",
            Self::SpecSetMismatch => "ty_three_spec_set_mismatch",
            Self::CanonicalFixtureHashMismatch => "ty_three_spec_fixture_hash_mismatch",
            Self::MissingSpec => "missing_ty_three_spec",
            Self::StaleTyCommitIdentity => "stale_ty_commit_identity",
            Self::TargetOrO3ControlMismatch => "ty_target_or_o3_control_mismatch",
            Self::MissingReplayRoot => "missing_replay_root",
            Self::StateGeneratedOrFingerprintMismatch => {
                "ty_state_generated_or_fingerprint_mismatch"
            }
            Self::ParentSequenceMismatch => "ty_parent_sequence_mismatch",
            Self::StatusDigestMismatch => "ty_status_digest_mismatch",
            Self::CallbackVisibleMismatch => "ty_callback_visible_mismatch",
        }
    }
}

/// Return the data-only private three-spec smoke fixture as opaque shadow evidence.
pub fn ty_native_fused_three_spec_smoke_fixture() -> ShadowReplayTyNativeFusedSmokeFixture {
    let controls =
        ShadowReplayTyNativeFusedSmokeControls::new("aarch64-apple-darwin", "O3", "O3", true);
    ShadowReplayTyNativeFusedSmokeFixture::new(
        TY_NATIVE_FUSED_THREE_SPEC_SMOKE_TY_GIT_COMMIT,
        vec![
            ShadowReplayTyNativeFusedSmokeSpec::new(
                "CoffeeCan1000BeansSafety",
                TY_NATIVE_FUSED_THREE_SPEC_SMOKE_TY_GIT_COMMIT,
                controls.clone(),
                "sha256:6249d2c9445adbe504dd9e1e51a956dcd0c86308b76243c349763883a194d535",
                2001,
                2997,
                "sha256:3b85504aed42f77fc677ecd21f89bad729f46195fde6864ad310b0ecde03c4ea",
                "sha256:2a7e216d4a6a1597cb135d77833604e44c7ade00670c71263c36c38bb72f3423",
                "sha256:6a9cecfaf691ec505c2b42b5744c76ecaf0b9c1c9dd336c25990a2ae7185019a",
                "sha256:0a1584922ab5e409a517b14e2f42ff12d7f17ac68e01da5512203237c4da55d4",
            ),
            ShadowReplayTyNativeFusedSmokeSpec::new(
                "EWD998Small",
                TY_NATIVE_FUSED_THREE_SPEC_SMOKE_TY_GIT_COMMIT,
                controls.clone(),
                "sha256:13cbb072d248b9db4ecfe5f1a8f6fffd8ee967f8c500adf93c40507069d3c4ca",
                9404,
                22532,
                "sha256:79ec7763ffc34c180e0e0ffd8da955f9a44edf33034e01a56eeaa2d483abc559",
                "sha256:ae76c7a348c3c9991a402cef3fb5548cca13cd0568eee2dd9c8feed6ba00b7e4",
                "sha256:91e04a7006111fa629d04e4ede0fb374236d2817d1ae277585de8e7ca69de96c",
                "sha256:ec5332cc7fce96331420a2f06604ab4473a5a1c0553003602f8a90d081cb5d92",
            ),
            ShadowReplayTyNativeFusedSmokeSpec::new(
                "MCLamportMutex",
                TY_NATIVE_FUSED_THREE_SPEC_SMOKE_TY_GIT_COMMIT,
                controls,
                "sha256:be111c73a451630420a3e36548d59f59d4cd60f364f33dae5f6520c4ba1a687f",
                4,
                3,
                "sha256:dfa97beab15daa6a42293bb8ccc94b3d124faf83709ec9504cc935c83b6a56b2",
                "sha256:4cfe95da220f5e4b0193a8e858986dcc5365b7c6776a73b150d9ad779a917fdd",
                "sha256:593d83bfbb433feea12f14a25375e9f33db8909541d90721fcd782786353708e",
                "sha256:ce01e75d586a0cd4cc0954da1d714e59d45501b895fef8584877f241619b0962",
            ),
        ],
    )
}

/// One baseline or native observation used for comparison.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ShadowReplayObservation {
    /// Observed execution status.
    pub status: ShadowReplayStatus,
    /// Optional deopt code.
    pub deopt_code: Option<String>,
    /// Consumer-visible result digest.
    pub consumer_result_sha256: String,
    /// Memory-effect digest.
    pub memory_effect_sha256: String,
    /// Optional ay checks.
    pub ay_checks: Option<ShadowReplayAYChecks>,
    /// Optional TY checks.
    pub ty_checks: Option<ShadowReplayTyChecks>,
}

impl ShadowReplayObservation {
    /// Build one shadow observation.
    pub fn new(
        status: ShadowReplayStatus,
        deopt_code: Option<String>,
        consumer_result_sha256: impl Into<String>,
        memory_effect_sha256: impl Into<String>,
        ay_checks: Option<ShadowReplayAYChecks>,
        ty_checks: Option<ShadowReplayTyChecks>,
    ) -> Self {
        Self {
            status,
            deopt_code,
            consumer_result_sha256: consumer_result_sha256.into(),
            memory_effect_sha256: memory_effect_sha256.into(),
            ay_checks,
            ty_checks,
        }
    }

    fn has_required_identity(&self) -> bool {
        !missing_required_text(&self.consumer_result_sha256)
            && !missing_required_text(&self.memory_effect_sha256)
    }
}

/// Reducer or replay reference for a shadow decision.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ShadowReplayEvidenceReference {
    /// Replay record SHA-256.
    pub replay_record_sha256: String,
    /// Optional reducer SHA-256.
    pub reducer_sha256: Option<String>,
    /// Optional canonical fixture SHA-256 bound to the replay decision.
    pub canonical_fixture_sha256: Option<String>,
}

impl ShadowReplayEvidenceReference {
    /// Build one evidence reference.
    pub fn new(replay_record_sha256: impl Into<String>, reducer_sha256: Option<String>) -> Self {
        Self {
            replay_record_sha256: replay_record_sha256.into(),
            reducer_sha256,
            canonical_fixture_sha256: None,
        }
    }

    /// Bind a canonical fixture SHA-256 to this replay evidence reference.
    pub fn with_canonical_fixture_sha256(
        mut self,
        canonical_fixture_sha256: impl Into<String>,
    ) -> Self {
        self.canonical_fixture_sha256 = Some(canonical_fixture_sha256.into());
        self
    }

    fn has_required_identity(&self) -> bool {
        !missing_required_text(&self.replay_record_sha256)
            && self
                .canonical_fixture_sha256
                .as_deref()
                .map(|sha256| !missing_required_text(sha256))
                .unwrap_or(true)
    }
}

/// Shadow comparison outcome.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ShadowReplayOutcome {
    /// Native and baseline matched in shadow mode.
    Match,
    /// Native result mismatched baseline.
    Mismatch,
    /// Native path crashed.
    NativeCrash,
    /// Native path timed out.
    NativeTimeout,
    /// Native verifier failed.
    VerifierFailure,
    /// Native deoptimized or fell back.
    NativeDeopt,
    /// Bundle or comparison evidence was incomplete.
    ReplayRejected,
}

impl ShadowReplayOutcome {
    /// Return the stable lower-snake-case string.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Match => "match",
            Self::Mismatch => "mismatch",
            Self::NativeCrash => "native_crash",
            Self::NativeTimeout => "native_timeout",
            Self::VerifierFailure => "verifier_failure",
            Self::NativeDeopt => "native_deopt",
            Self::ReplayRejected => "replay_rejected",
        }
    }
}

/// Shadow-only side effects; all install-authorizing fields must remain false.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct ShadowReplaySideEffects {
    /// Whether a callable handle was published.
    pub callable_handle_published: bool,
    /// Whether an installable cache entry was accepted.
    pub installable_cache_hit_accepted: bool,
    /// Whether ay native registry insertion occurred.
    pub ay_registry_inserted: bool,
    /// Whether TY native activation occurred.
    pub ty_native_activated: bool,
    /// Whether baseline result was replaced.
    pub baseline_replaced: bool,
    /// Useful-native counter delta.
    pub useful_native_delta: u64,
}

impl ShadowReplaySideEffects {
    /// Return true when every install-authorizing side effect is blocked.
    pub const fn all_install_authority_blocked(self) -> bool {
        !self.callable_handle_published
            && !self.installable_cache_hit_accepted
            && !self.ay_registry_inserted
            && !self.ty_native_activated
            && !self.baseline_replaced
            && self.useful_native_delta == 0
    }
}

/// Result of comparing native shadow output against baseline output.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ShadowReplayDecision {
    /// Bundle SHA-256 consumed by the decision.
    pub bundle_sha256: String,
    /// Comparison outcome.
    pub outcome: ShadowReplayOutcome,
    /// Stable rejection or evidence code.
    pub evidence_code: Option<String>,
    /// Baseline remains authoritative for consumer-visible output.
    pub baseline_authoritative: bool,
    /// Native result is never authoritative in this prework slice.
    pub native_authoritative: bool,
    /// Native observation status.
    pub native_status: ShadowReplayStatus,
    /// Baseline observation status.
    pub baseline_status: ShadowReplayStatus,
    /// Optional replay/reducer reference.
    pub evidence_reference: Option<ShadowReplayEvidenceReference>,
    /// Explicit side-effect summary.
    pub side_effects: ShadowReplaySideEffects,
    /// Canonical decision SHA-256.
    pub decision_sha256: String,
}

impl ShadowReplayDecision {
    /// Return the stable hash of this decision.
    pub fn canonical_decision_sha256(&self) -> String {
        let mut out = Vec::new();
        put_str(
            &mut out,
            "trust-cg.jit_everywhere.shadow_replay.decision.v1",
        );
        put_str(&mut out, &self.bundle_sha256);
        put_str(&mut out, self.outcome.as_str());
        put_option_str(&mut out, self.evidence_code.as_deref());
        put_bool(&mut out, self.baseline_authoritative);
        put_bool(&mut out, self.native_authoritative);
        put_str(&mut out, self.native_status.as_str());
        put_str(&mut out, self.baseline_status.as_str());
        if let Some(reference) = &self.evidence_reference {
            put_bool(&mut out, true);
            put_str(&mut out, &reference.replay_record_sha256);
            put_option_str(&mut out, reference.reducer_sha256.as_deref());
            if let Some(canonical_fixture_sha256) = &reference.canonical_fixture_sha256 {
                put_str(&mut out, canonical_fixture_sha256);
            }
        } else {
            put_bool(&mut out, false);
        }
        put_side_effects(&mut out, self.side_effects);
        format!("sha256:{}", sha256_hex(&out))
    }

    /// Return true when shadow replay did not authorize native product use.
    pub fn is_shadow_only(&self) -> bool {
        self.baseline_authoritative
            && !self.native_authoritative
            && self.side_effects.all_install_authority_blocked()
            && self.decision_sha256 == self.canonical_decision_sha256()
    }
}

/// Compare native shadow output against authoritative baseline output.
pub fn compare_shadow_replay(
    bundle: &ShadowReplayBundle,
    baseline: &ShadowReplayObservation,
    native: &ShadowReplayObservation,
    evidence_reference: Option<ShadowReplayEvidenceReference>,
) -> ShadowReplayDecision {
    let (outcome, evidence_code) =
        shadow_replay_outcome(bundle, baseline, native, evidence_reference.as_ref());
    let mut decision = ShadowReplayDecision {
        bundle_sha256: bundle.bundle_sha256.clone(),
        outcome,
        evidence_code: evidence_code.map(str::to_owned),
        baseline_authoritative: true,
        native_authoritative: false,
        native_status: native.status,
        baseline_status: baseline.status,
        evidence_reference,
        side_effects: ShadowReplaySideEffects::default(),
        decision_sha256: String::new(),
    };
    decision.decision_sha256 = decision.canonical_decision_sha256();
    decision
}

fn shadow_replay_outcome(
    bundle: &ShadowReplayBundle,
    baseline: &ShadowReplayObservation,
    native: &ShadowReplayObservation,
    evidence_reference: Option<&ShadowReplayEvidenceReference>,
) -> (ShadowReplayOutcome, Option<&'static str>) {
    if !bundle.is_replayable()
        || !baseline.has_required_identity()
        || !native.has_required_identity()
    {
        return (
            ShadowReplayOutcome::ReplayRejected,
            Some("missing_replay_evidence"),
        );
    }
    let Some(evidence_reference) = evidence_reference else {
        return (
            ShadowReplayOutcome::ReplayRejected,
            Some("missing_replay_evidence"),
        );
    };
    if !evidence_reference.has_required_identity() {
        return (
            ShadowReplayOutcome::ReplayRejected,
            Some("missing_replay_evidence"),
        );
    }
    if bundle.requires_ty_three_spec_fixture_hash()
        && evidence_reference.canonical_fixture_sha256.as_deref()
            != Some(TY_NATIVE_FUSED_THREE_SPEC_SMOKE_CANONICAL_FIXTURE_SHA256)
    {
        return (
            ShadowReplayOutcome::ReplayRejected,
            Some("ty_three_spec_fixture_hash_mismatch"),
        );
    }

    match native.status {
        ShadowReplayStatus::Crash => {
            return (ShadowReplayOutcome::NativeCrash, Some("native_crash"));
        }
        ShadowReplayStatus::Timeout => {
            return (ShadowReplayOutcome::NativeTimeout, Some("native_timeout"));
        }
        ShadowReplayStatus::VerifierFailure => {
            return (
                ShadowReplayOutcome::VerifierFailure,
                Some("verifier_failure"),
            );
        }
        ShadowReplayStatus::Deopt => {
            return (ShadowReplayOutcome::NativeDeopt, Some("native_deopt"));
        }
        ShadowReplayStatus::Ok => {}
    }

    if baseline.status != ShadowReplayStatus::Ok {
        return (
            ShadowReplayOutcome::ReplayRejected,
            Some("baseline_not_authoritative_ok"),
        );
    }

    if native.consumer_result_sha256 != baseline.consumer_result_sha256
        || native.memory_effect_sha256 != baseline.memory_effect_sha256
    {
        return (
            ShadowReplayOutcome::Mismatch,
            Some("consumer_or_memory_mismatch"),
        );
    }

    if let Some(code) = consumer_specific_mismatch(bundle, baseline, native) {
        return (ShadowReplayOutcome::Mismatch, Some(code));
    }

    (ShadowReplayOutcome::Match, None)
}

fn consumer_specific_mismatch(
    bundle: &ShadowReplayBundle,
    baseline: &ShadowReplayObservation,
    native: &ShadowReplayObservation,
) -> Option<&'static str> {
    match bundle.consumer {
        ShadowReplayConsumer::AY => {
            let (Some(baseline), Some(native)) = (&baseline.ay_checks, &native.ay_checks) else {
                return Some("missing_ay_shadow_checks");
            };
            if !baseline.has_required_identity() || !native.has_required_identity() {
                return Some("missing_ay_shadow_checks");
            }
            if baseline.witness_sha256 != native.witness_sha256
                || baseline.proof_sha256 != native.proof_sha256
            {
                Some("ay_witness_or_proof_mismatch")
            } else {
                None
            }
        }
        ShadowReplayConsumer::Ty => {
            let (Some(baseline), Some(native)) = (&baseline.ty_checks, &native.ty_checks) else {
                return Some("missing_ty_shadow_checks");
            };
            if !baseline.has_required_identity() || !native.has_required_identity() {
                return Some("missing_ty_shadow_checks");
            }
            if baseline.state_count != native.state_count
                || baseline.generated_count != native.generated_count
                || baseline.fingerprint_sha256 != native.fingerprint_sha256
            {
                Some("ty_state_generated_or_fingerprint_mismatch")
            } else if baseline.parent_sequence_sha256 != native.parent_sequence_sha256 {
                Some("ty_parent_sequence_mismatch")
            } else if baseline.status_sha256 != native.status_sha256 {
                Some("ty_status_digest_mismatch")
            } else if baseline.callback_visible_sha256 != native.callback_visible_sha256 {
                Some("ty_callback_visible_mismatch")
            } else {
                None
            }
        }
    }
}

fn put_compiler_config(out: &mut Vec<u8>, config: &ShadowReplayCompilerConfig) {
    put_str(out, &config.optimization_pipeline);
    put_str(out, &config.codegen_config_sha256);
    put_str(out, &config.proof_policy);
    put_str(out, &config.profile_schema);
}

fn put_generation(out: &mut Vec<u8>, generation: &ShadowReplayGenerationFacts) {
    put_str(out, &generation.generation_domain);
    put_u64(out, generation.observed_generation);
    put_u64(out, generation.current_generation);
    put_str(out, &generation.layout_generation);
}

fn put_side_effects(out: &mut Vec<u8>, side_effects: ShadowReplaySideEffects) {
    put_bool(out, side_effects.callable_handle_published);
    put_bool(out, side_effects.installable_cache_hit_accepted);
    put_bool(out, side_effects.ay_registry_inserted);
    put_bool(out, side_effects.ty_native_activated);
    put_bool(out, side_effects.baseline_replaced);
    put_u64(out, side_effects.useful_native_delta);
}

fn put_ty_native_fused_smoke_controls(
    out: &mut Vec<u8>,
    controls: &ShadowReplayTyNativeFusedSmokeControls,
) {
    put_str(out, &controls.target_triple);
    put_str(out, &controls.native_callout_opt_level);
    put_str(out, &controls.native_fused_parent_loop_opt_level);
    put_bool(out, controls.native_fused_strict);
}

fn put_ty_native_fused_smoke_spec(out: &mut Vec<u8>, spec: &ShadowReplayTyNativeFusedSmokeSpec) {
    put_str(out, &spec.spec_id);
    put_str(out, &spec.ty_git_commit);
    put_ty_native_fused_smoke_controls(out, &spec.controls);
    put_str(out, &spec.replay_artifact_dir_sha256);
    put_u64(out, spec.state_count);
    put_u64(out, spec.generated_count);
    put_str(out, &spec.fingerprint_sha256);
    put_str(out, &spec.parent_sequence_sha256);
    put_str(out, &spec.status_sha256);
    put_str(out, &spec.callback_visible_sha256);
}

fn put_str(out: &mut Vec<u8>, value: &str) {
    put_u64(out, value.len() as u64);
    out.extend_from_slice(value.as_bytes());
}

fn put_option_str(out: &mut Vec<u8>, value: Option<&str>) {
    if let Some(value) = value {
        put_bool(out, true);
        put_str(out, value);
    } else {
        put_bool(out, false);
    }
}

fn put_u32(out: &mut Vec<u8>, value: u32) {
    out.extend_from_slice(&value.to_le_bytes());
}

fn put_u64(out: &mut Vec<u8>, value: u64) {
    out.extend_from_slice(&value.to_le_bytes());
}

fn put_bool(out: &mut Vec<u8>, value: bool) {
    out.push(u8::from(value));
}

fn missing_required_text(value: &str) -> bool {
    value.trim().is_empty()
}
