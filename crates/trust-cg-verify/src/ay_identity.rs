// trust-cg-verify/ay_identity.rs - the ONE rule for which AY may run
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Which `ay` binary may run — one rule, and the only way to start AY.
//!
//! # The defect this replaces
//!
//! AY used to be DISCOVERED: an explicit `AY_SOLVER_PATH`, then aterm's managed
//! `store/ay/current`, then `TRUST_SYSROOT`, the running sysroot, `~/trust`
//! scans, `PATH`, `CARGO_TARGET_DIR`, `~/ay` and `/tmp` builds. Nothing compared
//! what that search found against anything. Measured 2026-09-17 (trust-cg
//! 27db8805, Trust bundle 9178): the plugin's unit tests and `trustc` with the
//! plugin both ran aterm's managed `store/ay/8256` (ay 0.13.0) instead of the
//! toolchain's own `bin/ay` (ay 0.26.0, commit 075a482ae).
//!
//! A first version of this rule compared the candidate's self-reported
//! `--version` banner. That authenticates nothing: a shell script printing the
//! pinned banner was admitted and received solve requests (measured, round 4).
//!
//! # The rule
//!
//! 1. **The record.** `build.rs` records, from the compiler that builds this
//!    crate (`$RUSTC --print sysroot`), the SHA-256 of `<sysroot>/bin/ay`'s
//!    BYTES, plus that binary's build banner (version, build number, commit)
//!    for diagnostics. The digest is what admission compares; the banner is a
//!    label bound to those bytes at build time. When this crate is compiled
//!    INTO a compiler (Trust's bootstrap), the build names the sysroot that
//!    compiler is assembled in (`TOOLCHAIN_AY_RECORD_HOST_SYSROOT`) and THAT
//!    sysroot's `bin/ay` is recorded: it is the one rule 2 names when the
//!    compiler hosts this crate. The build compiler's would be the previous
//!    stage's battery, which the assembled compiler never ships.
//! 2. **The candidate.** Exactly one path is named, never searched for:
//!    * the toolchain's `<sysroot>/bin/ay`, where the toolchain is the compiler
//!      HOSTING this process when there is one (the running executable IS a
//!      `trustc`/`rustc` driver in a sysroot `bin/` next to `lib/rustlib` — a
//!      backend loaded into the compiler), otherwise the compiler that built
//!      this crate;
//!    * or an absolute `AY_SOLVER_PATH` (never looked up on `PATH`);
//!    * or an absolute path chosen in code ([`resolve_explicit_path`]).
//! 3. **The identity.** The candidate is admitted only when the SHA-256 of its
//!    bytes EQUALS the recorded digest. Nothing is executed to decide this. A
//!    missing record, a missing or unreadable candidate and different bytes
//!    are each refused with a named [`AyIdentityRefusal`]; none falls back.
//! 4. **The bytes that run.** The admitted bytes are copied into a private,
//!    content-addressed file this user owns (`<user cache>/trust-cg/ay-exec/
//!    <sha256>/ay`, directory `0700`, file `0500`; see `ay_private_copy`),
//!    digested again, and AY is started from THAT file, never from the
//!    admitted path. AY re-executes itself by its own path at startup (its
//!    kernel memory governor), so starting it from a path anyone else can
//!    write would let them choose what runs after admission; the private copy
//!    makes the re-exec land on the admitted bytes too. A copy that cannot be
//!    made is refused (`TCG-AY-IDENTITY-UNMATERIALIZED`).
//! 5. **The only launcher.** An admitted binary is a [`PinnedAy`]. Its fields
//!    are private and the rule is its only constructor, and
//!    [`PinnedAy::command`] is the only `Command` for an AY in this crate. It
//!    re-checks the admitted file's state (device, inode, size, mtime, ctime)
//!    and refuses (`TCG-AY-IDENTITY-CHANGED`) if it was replaced or modified
//!    since; it re-checks the private copy (owner, mode, link count, file
//!    state, digest) and refuses (`TCG-AY-IDENTITY-COPY-CHANGED`) if it is no
//!    longer the admitted bytes; and it starts the private copy. On a host
//!    that assesses new executables (macOS), a copy's first start is made
//!    before any solver deadline starts (`first_start`).
//!
//! # What remains trusted
//!
//! * The build machine at build time: whatever `<build sysroot>/bin/ay`
//!   contained when `build.rs` ran is what is pinned (`build.rs` digests it
//!   before and after reading its banner and refuses a file that changed).
//! * The `trust-cg-verify` code itself, which carries the record: anyone who
//!   can modify the compiled library can modify the record.
//! * This user and root, who alone can write the private copy's directory or
//!   change the file (and can already change the running verifier). A change
//!   by the owner moves the file's ctime, which only root can set back.
//! * SHA-256 collision resistance.
//! * Nothing about AY's ANSWERS: an admitted AY is still an untrusted solver;
//!   its UNSAT is credited only after independent proof replay.
//!
//! # Unit-test fixtures
//!
//! Only in this crate's own `cfg(test)` build, a test may declare the SHA-256
//! of fixture executables through `test_fixtures`; those digests join the
//! admissible set for that test's scope. The candidate is still named by the
//! same rule and admitted only for those exact bytes. No such input exists in
//! any other build.

use std::ffi::{OsStr, OsString};
use std::fmt;
use std::path::{Path, PathBuf};
use std::sync::{Mutex, OnceLock};

#[path = "ay_private_copy.rs"]
mod ay_private_copy;
use ay_private_copy::PrivateCopy;

pub use crate::ay_identity_banner::{AyBuildIdentity, parse_ay_version_banner};

/// The explicit environment override. Identity-checked like every route.
pub const AY_OVERRIDE_ENV: &str = "AY_SOLVER_PATH";

/// The identity an admitted AY has: the SHA-256 of its bytes, and — for the
/// toolchain record — the build banner `build.rs` read from those bytes.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct AyIdentity {
    sha256: String,
    build: Option<AyBuildIdentity>,
    overlay: Option<ToolchainOverlay>,
}

/// A local OVERLAY toolchain (`scripts/assemble_trust_overlay.py`): an
/// installed Trust pack whose `bin/ay` and `bin/clean` were replaced by local
/// builds, named by a manifest (`<sysroot>/overlay.json`). `build.rs` records
/// one only when the manifest names exactly the bytes of both files, so the
/// AY identity it accompanies and the Clean digest below come from one
/// manifest.
///
/// It is provenance, not authority: admission still compares only the AY
/// digest. Its Clean digest does bind the proof checker, though: a build from
/// an overlay accepts no other checker (see `obligation_cert_store`).
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct ToolchainOverlay {
    manifest_sha256: String,
    clean_sha256: String,
    clean_commit: String,
}

impl ToolchainOverlay {
    /// Build an overlay record from its fields; each must be lowercase hex
    /// (64 digits for the digests, 40 for the commit).
    pub fn new(
        manifest_sha256: &str,
        clean_sha256: &str,
        clean_commit: &str,
    ) -> Result<Self, String> {
        if !is_sha256_hex(manifest_sha256) || !is_sha256_hex(clean_sha256) {
            return Err(format!(
                "overlay digests {manifest_sha256:?} / {clean_sha256:?} are not 64 lowercase hex digits"
            ));
        }
        if clean_commit.len() != 40
            || !clean_commit
                .bytes()
                .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
        {
            return Err(format!(
                "overlay Clean commit {clean_commit:?} is not 40 lowercase hex digits"
            ));
        }
        Ok(Self {
            manifest_sha256: manifest_sha256.to_owned(),
            clean_sha256: clean_sha256.to_owned(),
            clean_commit: clean_commit.to_owned(),
        })
    }

    /// SHA-256 of the overlay manifest's bytes.
    pub fn manifest_sha256(&self) -> &str {
        &self.manifest_sha256
    }

    /// SHA-256 of the overlay's `bin/clean`: the only checker a build from
    /// this overlay accepts.
    pub fn clean_sha256(&self) -> &str {
        &self.clean_sha256
    }

    /// The Clean source commit the manifest names. A label: `clean
    /// --version` reports no commit, so the assembler asserted it.
    pub fn clean_commit(&self) -> &str {
        &self.clean_commit
    }

    /// One-line form appended to the AY identity in provenance.
    pub fn describe(&self) -> String {
        format!(
            "overlay-toolchain manifest-sha256 {} clean-sha256 {} clean-commit {}",
            self.manifest_sha256, self.clean_sha256, self.clean_commit
        )
    }
}

impl AyIdentity {
    /// Lowercase-hex SHA-256 of the executable's bytes (what admission compares).
    pub fn sha256(&self) -> &str {
        &self.sha256
    }

    /// The build banner recorded for these bytes. `None` only for a unit-test
    /// fixture, which has no AY build.
    pub fn build(&self) -> Option<&AyBuildIdentity> {
        self.build.as_ref()
    }

    /// The overlay toolchain these bytes came from, when `build.rs` recorded
    /// them from one.
    pub fn overlay(&self) -> Option<&ToolchainOverlay> {
        self.overlay.as_ref()
    }

    /// One-line form used in diagnostics, reports and verdict provenance.
    pub fn describe(&self) -> String {
        let base = match &self.build {
            Some(build) => format!("{} sha256 {}", build.describe(), self.sha256),
            None => format!("unit-test fixture sha256 {}", self.sha256),
        };
        match &self.overlay {
            Some(overlay) => format!("{base} {}", overlay.describe()),
            None => base,
        }
    }

    /// The same identity, recorded from an overlay toolchain.
    #[must_use]
    pub(crate) fn with_overlay(mut self, overlay: Option<ToolchainOverlay>) -> Self {
        self.overlay = overlay;
        self
    }

    fn recorded(
        sha256: &str,
        commit: &str,
        version: &str,
        increment: &str,
    ) -> Result<Self, String> {
        if !is_sha256_hex(sha256) {
            return Err(format!(
                "recorded sha256 {sha256:?} is not 64 lowercase hex digits"
            ));
        }
        Ok(Self {
            sha256: sha256.to_owned(),
            build: Some(AyBuildIdentity::from_recorded_fields(
                commit, version, increment,
            )?),
            overlay: None,
        })
    }
}

fn is_sha256_hex(text: &str) -> bool {
    text.len() == 64
        && text
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
}

/// What this crate's build recorded about its toolchain's AY.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ToolchainAyRecord {
    build_sysroot: PathBuf,
    expected: Result<AyIdentity, String>,
    overlay: OverlayRecord,
}

/// Whether the build sysroot was an overlay toolchain.
#[derive(Clone, Debug, PartialEq, Eq)]
enum OverlayRecord {
    /// An installed toolchain (or none): no manifest.
    None,
    /// A manifest that names exactly the sysroot's `bin/ay` and `bin/clean`.
    Valid(ToolchainOverlay),
    /// A manifest that does not: nothing was recorded, and no checker is
    /// accepted either.
    Invalid,
}

/// Parse the overlay fields `build.rs` recorded.
fn overlay_record(status: &str, manifest: &str, clean: &str, commit: &str) -> OverlayRecord {
    match status {
        "" => OverlayRecord::None,
        "valid" => ToolchainOverlay::new(manifest, clean, commit)
            .map_or(OverlayRecord::Invalid, OverlayRecord::Valid),
        _ => OverlayRecord::Invalid,
    }
}

impl ToolchainAyRecord {
    /// The record compiled into this crate by `build.rs`.
    ///
    /// A unit test cannot rebuild the crate from another toolchain, so in
    /// this crate's `cfg(test)` build a test may stand a fixture record in for
    /// it on its own thread ([`test_fixtures::with_recorded`]); everything that
    /// reads the record, the checker policy included, then runs unchanged.
    pub fn recorded() -> &'static Self {
        #[cfg(test)]
        if let Some(record) = test_fixtures::recorded_override() {
            return record;
        }
        static RECORD: OnceLock<ToolchainAyRecord> = OnceLock::new();
        RECORD.get_or_init(|| {
            let unrecorded = env!("TOOLCHAIN_AY_RECORD_UNRECORDED");
            let overlay = overlay_record(
                env!("TOOLCHAIN_AY_RECORD_OVERLAY"),
                env!("TOOLCHAIN_AY_RECORD_OVERLAY_SHA256"),
                env!("TOOLCHAIN_AY_RECORD_OVERLAY_CLEAN_SHA256"),
                env!("TOOLCHAIN_AY_RECORD_OVERLAY_CLEAN_COMMIT"),
            );
            let expected = if unrecorded.is_empty() {
                AyIdentity::recorded(
                    env!("TOOLCHAIN_AY_RECORD_SHA256"),
                    env!("TOOLCHAIN_AY_RECORD_COMMIT"),
                    env!("TOOLCHAIN_AY_RECORD_VERSION"),
                    env!("TOOLCHAIN_AY_RECORD_INCREMENT"),
                )
                .map_err(|reason| format!("the recorded identity is malformed: {reason}"))
            } else {
                Err(unrecorded.to_owned())
            };
            Self::with_overlay_record(
                PathBuf::from(env!("TOOLCHAIN_AY_RECORD_SYSROOT")),
                expected,
                overlay,
            )
        })
    }

    fn with_overlay_record(
        build_sysroot: PathBuf,
        expected: Result<AyIdentity, String>,
        overlay: OverlayRecord,
    ) -> Self {
        let expected = match (&overlay, expected) {
            (OverlayRecord::Valid(record), Ok(identity)) => {
                Ok(identity.with_overlay(Some(record.clone())))
            }
            (OverlayRecord::Invalid, Ok(_)) => Err(
                "the overlay toolchain record is malformed, so no AY identity is recorded".into(),
            ),
            (_, expected) => expected,
        };
        Self {
            build_sysroot,
            expected,
            overlay,
        }
    }

    /// A record for resolving against an explicit fixture toolchain.
    #[cfg(test)]
    pub(crate) fn new(build_sysroot: PathBuf, expected: Result<AyIdentity, String>) -> Self {
        Self::with_overlay_record(build_sysroot, expected, OverlayRecord::None)
    }

    /// A fixture record built from an overlay toolchain (`None`: an invalid
    /// manifest).
    #[cfg(test)]
    pub(crate) fn new_overlay(
        build_sysroot: PathBuf,
        expected: Result<AyIdentity, String>,
        overlay: Option<ToolchainOverlay>,
    ) -> Self {
        let overlay = overlay.map_or(OverlayRecord::Invalid, OverlayRecord::Valid);
        Self::with_overlay_record(build_sysroot, expected, overlay)
    }

    /// The overlay toolchain the crate was built from, if it was.
    pub fn overlay(&self) -> Option<&ToolchainOverlay> {
        match &self.overlay {
            OverlayRecord::Valid(overlay) => Some(overlay),
            OverlayRecord::None | OverlayRecord::Invalid => None,
        }
    }

    /// The only Clean checker digest this build accepts: `None` for a build
    /// from an installed toolchain (ordinary discovery), `Some(digest)` for an
    /// overlay build, and `Some("")`, which no file matches, for a build whose
    /// overlay manifest was refused. An overlay build never falls back from
    /// its own `bin/clean` to another checker.
    pub fn pinned_clean_sha256(&self) -> Option<&str> {
        match &self.overlay {
            OverlayRecord::None => None,
            OverlayRecord::Valid(overlay) => Some(overlay.clean_sha256()),
            OverlayRecord::Invalid => Some(""),
        }
    }

    /// Sysroot of the compiler that built this crate.
    pub fn build_sysroot(&self) -> &Path {
        &self.build_sysroot
    }

    /// The AY identity the build recorded, or why none was recorded.
    pub fn expected(&self) -> Result<&AyIdentity, &str> {
        self.expected.as_ref().map_err(String::as_str)
    }
}

/// How an admitted AY was named.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum AyRoute {
    /// `<toolchain sysroot>/bin/ay`.
    ToolchainSysroot,
    /// An absolute `AY_SOLVER_PATH`.
    EnvironmentOverride,
    /// An absolute path chosen in code ([`resolve_explicit_path`]).
    ExplicitPath,
}

impl AyRoute {
    /// Stable route label recorded in solver selections and diagnostics.
    pub fn as_str(self) -> &'static str {
        match self {
            Self::ToolchainSysroot => "toolchain-pinned-ay",
            Self::EnvironmentOverride => "override-pinned-ay",
            Self::ExplicitPath => "explicit-pinned-ay",
        }
    }

    fn naming(self) -> &'static str {
        match self {
            Self::ToolchainSysroot => "the toolchain AY",
            Self::EnvironmentOverride => AY_OVERRIDE_ENV,
            Self::ExplicitPath => "the explicit AY path",
        }
    }
}

/// Which compiler's sysroot the toolchain route used.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum SysrootSource {
    /// The running executable is that sysroot's compiler driver.
    HostingCompiler,
    /// No hosting compiler: the sysroot of the compiler that built this crate.
    BuildCompiler,
}

impl SysrootSource {
    fn as_str(self) -> &'static str {
        match self {
            Self::HostingCompiler => "hosting-compiler",
            Self::BuildCompiler => "build-compiler",
        }
    }
}

/// File state bound to a digest. A replaced, rebuilt, touched or rewritten
/// executable no longer matches.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct FileStamp {
    len: u64,
    modified: Option<std::time::SystemTime>,
    #[cfg(unix)]
    device: u64,
    #[cfg(unix)]
    inode: u64,
    #[cfg(unix)]
    ctime: (i64, i64),
}

fn file_stamp(path: &Path) -> Option<FileStamp> {
    let metadata = std::fs::metadata(path).ok()?;
    #[cfg(unix)]
    use std::os::unix::fs::MetadataExt;
    Some(FileStamp {
        len: metadata.len(),
        modified: metadata.modified().ok(),
        #[cfg(unix)]
        device: metadata.dev(),
        #[cfg(unix)]
        inode: metadata.ino(),
        #[cfg(unix)]
        ctime: (metadata.ctime(), metadata.ctime_nsec()),
    })
}

/// An AY admitted by the rule. The only value from which this crate starts AY.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct PinnedAy {
    path: PathBuf,
    identity: AyIdentity,
    route: AyRoute,
    toolchain: Option<(PathBuf, SysrootSource)>,
    stamp: FileStamp,
    copy: PrivateCopy,
}

impl PinnedAy {
    /// The admitted executable (as named; verdicts and reports cite it).
    pub fn path(&self) -> &Path {
        &self.path
    }

    /// The private copy of the admitted bytes that [`Self::command`] starts.
    pub fn exec_path(&self) -> &Path {
        self.copy.path()
    }

    /// Its identity (equal to an admissible recorded identity).
    pub fn identity(&self) -> &AyIdentity {
        &self.identity
    }

    /// Lowercase-hex SHA-256 of the admitted bytes.
    pub fn sha256(&self) -> &str {
        self.identity.sha256()
    }

    /// How it was named.
    pub fn route(&self) -> AyRoute {
        self.route
    }

    /// The toolchain sysroot the rule selected (toolchain route only).
    pub fn sysroot(&self) -> Option<&Path> {
        self.toolchain
            .as_ref()
            .map(|(sysroot, _)| sysroot.as_path())
    }

    /// Whether that sysroot is the hosting or the building compiler's.
    pub fn sysroot_source(&self) -> Option<SysrootSource> {
        self.toolchain.as_ref().map(|(_, source)| *source)
    }

    /// One line recording route, toolchain, path and identity.
    pub fn describe(&self) -> String {
        let toolchain = match &self.toolchain {
            Some((sysroot, source)) => {
                format!(" toolchain={} ({})", sysroot.display(), source.as_str())
            }
            None => String::new(),
        };
        format!(
            "route={}{toolchain} ay={} identity=[{}]",
            self.route.as_str(),
            self.path.display(),
            self.identity.describe()
        )
    }

    /// Refuse if the admitted file is no longer the one whose bytes were
    /// admitted, or the private copy is no longer those bytes.
    pub fn revalidate(&self) -> Result<(), AyIdentityRefusal> {
        if file_stamp(&self.path).as_ref() != Some(&self.stamp) {
            return Err(AyIdentityRefusal::Changed {
                route: self.route,
                path: self.path.clone(),
            });
        }
        self.copy
            .verify(self.sha256())
            .map_err(|reason| AyIdentityRefusal::CopyChanged {
                route: self.route,
                path: self.copy.path().to_path_buf(),
                reason,
            })
    }

    /// A `Command` for this AY's private copy, after [`Self::revalidate`].
    /// This is the only place trust-cg-verify constructs a process for an AY
    /// binary, and it never starts the admitted path itself. On a host that
    /// assesses new executables, the copy's first start has been made (or
    /// waited for) before it returns ([`Self::make_first_start`]), so the
    /// deadline of the run it is for never pays that assessment.
    pub fn command(&self) -> Result<std::process::Command, AyIdentityRefusal> {
        self.make_first_start();
        self.launcher()
    }

    /// Make this AY's private copy's first start now if it is still pending,
    /// or wait while another thread makes it (see `first_start`). A caller
    /// that starts a solver deadline BEFORE it asks for a command (the
    /// resident server, whose deadline starts at admission and whose spawn
    /// happens inside it) calls this first.
    pub(crate) fn make_first_start(&self) {
        first_start::ensure(self, first_start::Scope::Pending, first_start::ALLOWANCE);
    }

    /// The identity-warm thread's early first start: only of a copy this
    /// process published, and never waiting for another thread's, so the
    /// host's assessment overlaps the compiler's front end instead of the
    /// first solve. A warm cache (a copy that predates the process) starts
    /// nothing here.
    pub(crate) fn prime_published_copy(&self) {
        first_start::ensure(
            self,
            first_start::Scope::PublishedHere,
            first_start::ALLOWANCE,
        );
    }

    /// Every AY start goes through here, the first start included.
    fn launcher(&self) -> Result<std::process::Command, AyIdentityRefusal> {
        self.revalidate()?;
        crate::proof_tool_record::note(
            crate::proof_tool_record::ProofTool::Ay,
            &self.path,
            self.sha256(),
            Some(&self.identity.describe()),
        );
        crate::process_cost::note_solver_start();
        Ok(std::process::Command::new(self.copy.path()))
    }
}

/// The first start of an admitted AY's private copy is made before a solver
/// deadline starts, never inside one.
///
/// # The defect this removes
///
/// The private copy is a new executable file, and macOS holds its FIRST start
/// until it has assessed the file (`ay_private_copy::HOST_ASSESSES_FIRST_START`
/// has the measurements: up to 32.2 s for the 158 MB toolchain AY on a busy
/// host, 0.01-0.04 s for every later start). That first start used to be the
/// first query's: the resident server is spawned inside the query's deadline,
/// and a one-shot run is bounded as a whole. So the first query after a new
/// copy timed out whatever it asked. Measured on trust-cg 7e85a7fa7,
/// `cegis::tests` single-threaded: the first three resident spawns each ended
/// in `server_timeout` at 5.0 s, and every later query took 0.001-0.07 s. With
/// a fresh copy (a fresh `XDG_CACHE_HOME`), the first query of each of
/// `cegis_layer_a`, `cegis_stats_trace` and `cegis_layer_b` timed out at
/// 1.006-1.007 s against its 1 s budget. The identity-warm thread's prime
/// (`ay_bridge::prime_published_solver_copy`) takes the start off a compile's
/// critical path when its front end is long enough, but only a compile runs
/// it, and a query that arrived while it ran paid the rest of the assessment
/// inside its own deadline.
///
/// # The rule
///
/// On a host that assesses new executables, a copy's first start is PENDING
/// while no completed first start of its exact file state is known: this
/// process published it, or found it without a marker beside it recording one
/// (`ay_private_copy::note_found`; a copy another process published and never
/// started, or is starting right now). A pending first start is made exactly
/// once per process, as `ay --version` with an empty environment, its output
/// and status ignored, stopped after `first_start::ALLOWANCE`:
///
/// * by the identity-warm thread, early, for a copy this process published
///   ([`PinnedAy::prime_published_copy`]);
/// * otherwise by the first thread that needs a command
///   ([`PinnedAy::command`]) or is about to start a resident query's deadline
///   ([`PinnedAy::make_first_start`]), before that deadline starts.
///
/// A thread that needs a command while another thread makes the start waits
/// for it, so no deadline covers any part of it. A start that ran to its exit
/// is recorded beside the copy, so later processes start nothing extra; one
/// stopped at the allowance counts as made in this process only (a later
/// process makes it again) and is reported once. The start decides nothing:
/// it runs the admitted bytes through the same revalidation as every start.
/// A unit-test fixture (an identity without an AY build) is never started this
/// way: its side files count exactly the starts its test makes. A test that
/// gives a new fixture a deadline starts it first itself
/// (`test_fixtures::warm`). No other host makes a first start on its own.
mod first_start {
    use super::{PinnedAy, ay_private_copy};
    use std::time::Duration;

    /// How long a first start may run before it is stopped: about four times
    /// the slowest first start measured (32.2 s, a fresh copy of the 158 MB
    /// toolchain AY at load average 43 during a compile). A hang guard, not a
    /// budget: a start that finishes decides nothing, and one stopped here
    /// leaves the rest of the assessment to the next start, inside a solver
    /// deadline, as before this rule.
    pub(super) const ALLOWANCE: Duration = Duration::from_secs(120);

    /// Which pending first starts a caller may make.
    pub(super) enum Scope {
        /// Any pending one, waiting for another thread's (a deadline follows).
        Pending,
        /// Only one of a copy published during this process; never wait.
        PublishedHere,
    }

    pub(super) fn ensure(pinned: &PinnedAy, scope: Scope, allowance: Duration) {
        if !ay_private_copy::HOST_ASSESSES_FIRST_START || pinned.identity.build.is_none() {
            return;
        }
        let published_only = matches!(scope, Scope::PublishedHere);
        match ay_private_copy::claim_first_start(&pinned.copy, published_only) {
            ay_private_copy::FirstStartClaim::Nothing => {}
            ay_private_copy::FirstStartClaim::Wait => {
                crate::process_cost::mark("ay_first_start_wait_begin");
                ay_private_copy::await_first_start(&pinned.copy, allowance);
                crate::process_cost::mark("ay_first_start_wait_end");
            }
            ay_private_copy::FirstStartClaim::Make(claim) => {
                claim.finish(start(pinned, allowance));
            }
        }
    }

    /// Start the copy once as `ay --version`; whether it ran to its exit.
    fn start(pinned: &PinnedAy, allowance: Duration) -> bool {
        let Ok(mut command) = pinned.launcher() else {
            return false;
        };
        command.arg("--version").env_clear();
        let began = std::time::Instant::now();
        crate::process_cost::mark("ay_first_start_begin");
        let outcome = crate::subprocess::run(&mut command, Some(allowance));
        crate::process_cost::mark("ay_first_start_end");
        if crate::diag::solve_trace_enabled() {
            eprintln!(
                "TCG_SOLVE_TRACE ay_first_start {:.3}s completed={} copy={}",
                began.elapsed().as_secs_f64(),
                outcome.is_ok(),
                pinned.exec_path().display()
            );
        }
        match outcome {
            Ok(_) => true,
            Err(crate::subprocess::RunError::Timeout(_)) => {
                eprintln!(
                    "trust-cg-verify: the first start of the private AY copy {} did not finish \
                     within {allowance:?} and was stopped; a later start may pay the rest of the \
                     operating system's first-start assessment inside a solver deadline",
                    pinned.exec_path().display()
                );
                false
            }
            Err(_) => false,
        }
    }

    /// [`ensure`] for any pending first start, stopped after `allowance`.
    #[cfg(test)]
    pub(crate) fn ensure_within(pinned: &PinnedAy, allowance: Duration) {
        ensure(pinned, Scope::Pending, allowance);
    }

    /// Whether this process knows `pinned`'s copy's first start to be made.
    #[cfg(test)]
    pub(crate) fn made(pinned: &PinnedAy) -> bool {
        ay_private_copy::first_start_made(&pinned.copy)
    }

    /// Whether a thread of this process is making it now.
    #[cfg(test)]
    pub(crate) fn in_progress(pinned: &PinnedAy) -> bool {
        ay_private_copy::first_start_in_progress(&pinned.copy)
    }

    /// How many threads have waited for it.
    #[cfg(test)]
    pub(crate) fn waits(pinned: &PinnedAy) -> usize {
        ay_private_copy::first_start_waits(&pinned.copy)
    }

    /// Forget what this process knows about it, as a new process would.
    #[cfg(test)]
    pub(crate) fn forget(pinned: &PinnedAy) {
        ay_private_copy::forget_first_start(pinned.exec_path());
    }
}

impl fmt::Display for PinnedAy {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.describe())
    }
}

/// Why no AY is admitted. Every variant is terminal: nothing falls back.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum AyIdentityRefusal {
    /// The build recorded no expected identity, so no AY is admissible.
    Unrecorded {
        /// Sysroot of the compiler that built this crate.
        build_sysroot: PathBuf,
        /// What `build.rs` reported.
        reason: String,
    },
    /// The selected toolchain ships no AY.
    ToolchainAyMissing {
        /// The toolchain sysroot the rule selected.
        sysroot: PathBuf,
        /// Hosting or building compiler.
        sysroot_source: SysrootSource,
        /// The expected `bin/ay` path.
        path: PathBuf,
    },
    /// An override or explicit path is empty or relative (never searched).
    OverrideNotAbsolute {
        /// How it was named.
        route: AyRoute,
        /// The raw value.
        value: OsString,
    },
    /// An override or explicit path names no executable file.
    OverrideMissing {
        /// How it was named.
        route: AyRoute,
        /// The path.
        path: PathBuf,
    },
    /// The candidate's bytes could not be digested (unreadable, or changed
    /// while being read).
    Unidentified {
        /// How the candidate was named.
        route: AyRoute,
        /// The candidate.
        path: PathBuf,
        /// Read failure.
        reason: String,
    },
    /// The candidate's bytes are not the recorded AY.
    Mismatch {
        /// How the candidate was named.
        route: AyRoute,
        /// The candidate.
        path: PathBuf,
        /// The recorded identity.
        expected: Box<AyIdentity>,
        /// SHA-256 of the candidate's bytes.
        found_sha256: String,
    },
    /// An admitted executable was replaced or modified before it was started.
    Changed {
        /// How it was named when admitted.
        route: AyRoute,
        /// The executable.
        path: PathBuf,
    },
    /// The admitted bytes could not be placed in a private copy to start from.
    Unmaterialized {
        /// How the candidate was named.
        route: AyRoute,
        /// The admitted executable.
        path: PathBuf,
        /// Why.
        reason: String,
    },
    /// The private copy is no longer the admitted bytes, or no longer private.
    CopyChanged {
        /// How the candidate was named.
        route: AyRoute,
        /// The private copy.
        path: PathBuf,
        /// What check failed.
        reason: String,
    },
}

impl AyIdentityRefusal {
    /// Stable diagnostic code (also the selection's route label).
    pub fn code(&self) -> &'static str {
        match self {
            Self::Unrecorded { .. } => "TCG-AY-IDENTITY-UNRECORDED",
            Self::ToolchainAyMissing { .. } => "TCG-AY-IDENTITY-MISSING",
            Self::OverrideNotAbsolute { .. } => "TCG-AY-IDENTITY-OVERRIDE-NOT-ABSOLUTE",
            Self::OverrideMissing { .. } => "TCG-AY-IDENTITY-OVERRIDE-MISSING",
            Self::Unidentified { .. } => "TCG-AY-IDENTITY-UNIDENTIFIED",
            Self::Mismatch { .. } => "TCG-AY-IDENTITY-MISMATCH",
            Self::Changed { .. } => "TCG-AY-IDENTITY-CHANGED",
            Self::Unmaterialized { .. } => "TCG-AY-IDENTITY-UNMATERIALIZED",
            Self::CopyChanged { .. } => "TCG-AY-IDENTITY-COPY-CHANGED",
        }
    }
}

impl fmt::Display for AyIdentityRefusal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "[{}] ", self.code())?;
        match self {
            Self::Unrecorded {
                build_sysroot,
                reason,
            } => write!(
                f,
                "no AY is admissible: the build of trust-cg-verify recorded no toolchain AY \
                 identity (build compiler sysroot {:?}): {reason}",
                build_sysroot.display().to_string()
            ),
            Self::ToolchainAyMissing {
                sysroot,
                sysroot_source,
                path,
            } => write!(
                f,
                "the {} toolchain at {} ships no AY at {}; no other location is searched",
                sysroot_source.as_str(),
                sysroot.display(),
                path.display()
            ),
            Self::OverrideNotAbsolute { route, value } => write!(
                f,
                "{}={value:?} is not an absolute path; it is never looked up on PATH and does \
                 not fall back to the toolchain AY",
                route.naming()
            ),
            Self::OverrideMissing { route, path } => write!(
                f,
                "{}={} names no executable file; it does not fall back to the toolchain AY",
                route.naming(),
                path.display()
            ),
            Self::Unidentified {
                route,
                path,
                reason,
            } => write!(
                f,
                "{} ({}) could not be digested: {reason}",
                path.display(),
                route.as_str()
            ),
            Self::Mismatch {
                route,
                path,
                expected,
                found_sha256,
            } => write!(
                f,
                "{} ({}) has sha256 {found_sha256}, not the recorded toolchain AY [{}]",
                path.display(),
                route.as_str(),
                expected.describe()
            ),
            Self::Changed { route, path } => write!(
                f,
                "{} ({}) was replaced or modified after its bytes were admitted; it is not started",
                path.display(),
                route.as_str()
            ),
            Self::Unmaterialized {
                route,
                path,
                reason,
            } => write!(
                f,
                "{} ({}) was admitted, but no private copy of its bytes could be made to start \
                 from: {reason}; it is not started",
                path.display(),
                route.as_str()
            ),
            Self::CopyChanged {
                route,
                path,
                reason,
            } => write!(
                f,
                "the private copy {} ({}) of the admitted bytes failed its check: {reason}; it \
                 is not started",
                path.display(),
                route.as_str()
            ),
        }
    }
}

impl std::error::Error for AyIdentityRefusal {}

/// The identity the build recorded, for callers that report it.
pub fn recorded_toolchain_ay_identity() -> Result<&'static AyIdentity, AyIdentityRefusal> {
    let record = ToolchainAyRecord::recorded();
    record
        .expected()
        .map_err(|reason| AyIdentityRefusal::Unrecorded {
            build_sysroot: record.build_sysroot().to_path_buf(),
            reason: reason.to_owned(),
        })
}

fn executable_name() -> String {
    format!("ay{}", std::env::consts::EXE_SUFFIX)
}

/// The sysroot of the compiler hosting `exe`, if any: `exe` IS a `trustc` or
/// `rustc` driver, it sits in a directory named `bin`, and that directory's
/// parent is a Rust sysroot (`lib/rustlib` exists). A tool that merely sits in
/// some `bin/` next to a file named `rustc` is not hosted by a compiler.
fn hosting_compiler_sysroot(exe: &Path) -> Option<PathBuf> {
    let exe_suffix = std::env::consts::EXE_SUFFIX;
    let name = exe.file_name()?;
    let is_driver = ["trustc", "rustc"]
        .iter()
        .any(|driver| name == OsStr::new(&format!("{driver}{exe_suffix}")));
    if !is_driver {
        return None;
    }
    let bin = exe.parent()?;
    if bin.file_name()? != OsStr::new("bin") {
        return None;
    }
    let sysroot = bin.parent()?;
    sysroot
        .join("lib")
        .join("rustlib")
        .is_dir()
        .then(|| sysroot.to_path_buf())
}

fn is_executable_file(path: &Path) -> bool {
    let Ok(metadata) = std::fs::metadata(path) else {
        return false;
    };
    if !metadata.is_file() {
        return false;
    }
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        metadata.permissions().mode() & 0o111 != 0
    }
    #[cfg(not(unix))]
    {
        true
    }
}

/// How the caller names the candidate.
#[derive(Clone, Copy, Debug)]
enum Naming<'a> {
    /// The toolchain's `bin/ay`, unless `AY_SOLVER_PATH` (the value) is set.
    Process(Option<&'a OsStr>),
    /// A path chosen in code.
    Explicit(&'a OsStr),
}

/// Everything the rule reads, passed in so it is testable without touching
/// process state.
#[derive(Clone, Copy, Debug)]
struct ResolutionInputs<'a> {
    running_exe: Option<&'a Path>,
    record: &'a ToolchainAyRecord,
    naming: Naming<'a>,
}

/// A candidate named by the rule, before its bytes are digested.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct Candidate {
    path: PathBuf,
    route: AyRoute,
    toolchain: Option<(PathBuf, SysrootSource)>,
    admissible: Vec<AyIdentity>,
}

/// Identities admission accepts in this build: the compiled record, plus — in
/// this crate's unit-test build only — fixture digests the test declared.
fn admissible_identities(record: &ToolchainAyRecord) -> Result<Vec<AyIdentity>, AyIdentityRefusal> {
    let recorded = record.expected().ok().cloned().into_iter();
    #[cfg(not(test))]
    let admissible: Vec<AyIdentity> = recorded.collect();
    #[cfg(test)]
    let admissible: Vec<AyIdentity> = recorded.chain(test_fixtures::declared()).collect();
    if admissible.is_empty() {
        let reason = record
            .expected()
            .err()
            .unwrap_or("no identity is admissible")
            .to_owned();
        return Err(AyIdentityRefusal::Unrecorded {
            build_sysroot: record.build_sysroot().to_path_buf(),
            reason,
        });
    }
    Ok(admissible)
}

fn named_path(route: AyRoute, value: &OsStr) -> Result<PathBuf, AyIdentityRefusal> {
    let path = PathBuf::from(value);
    if value.is_empty() || !path.is_absolute() {
        return Err(AyIdentityRefusal::OverrideNotAbsolute {
            route,
            value: value.to_owned(),
        });
    }
    if !is_executable_file(&path) {
        return Err(AyIdentityRefusal::OverrideMissing { route, path });
    }
    Ok(path)
}

fn candidate(inputs: ResolutionInputs<'_>) -> Result<Candidate, AyIdentityRefusal> {
    // No record, nothing admissible — including an explicit path, whose bytes
    // have nothing to be compared against.
    let admissible = admissible_identities(inputs.record)?;
    let (route, override_value) = match inputs.naming {
        Naming::Process(Some(value)) => (AyRoute::EnvironmentOverride, Some(value)),
        Naming::Process(None) => (AyRoute::ToolchainSysroot, None),
        Naming::Explicit(value) => (AyRoute::ExplicitPath, Some(value)),
    };
    if let Some(value) = override_value {
        return Ok(Candidate {
            path: named_path(route, value)?,
            route,
            toolchain: None,
            admissible,
        });
    }
    let (sysroot, source) = match inputs.running_exe.and_then(hosting_compiler_sysroot) {
        Some(sysroot) => (sysroot, SysrootSource::HostingCompiler),
        None => (
            inputs.record.build_sysroot().to_path_buf(),
            SysrootSource::BuildCompiler,
        ),
    };
    let path = sysroot.join("bin").join(executable_name());
    if !is_executable_file(&path) {
        return Err(AyIdentityRefusal::ToolchainAyMissing {
            sysroot,
            sysroot_source: source,
            path,
        });
    }
    Ok(Candidate {
        path,
        route,
        toolchain: Some((sysroot, source)),
        admissible,
    })
}

/// Stream `path` through SHA-256 and return the digest with the file state it
/// is bound to. A file whose state changes while it is read has no identity.
///
/// COMPUTE-ONCE per file state. The memo slot for `(path, state)` is locked
/// across the read, so a caller that arrives while another thread is reading
/// the same file state waits for that digest instead of reading the whole
/// executable a second time. A compile resolves its AY on the background
/// identity-warm thread and again on the first proof query, and both verify
/// the private copy. Before this, a cold compile under contention could read
/// one 91 MB file twice: cold compiles of `fixed_cost_budget_aarch64`'s
/// library counted 6 digests in 12 of 48 runs made six at a time, against the
/// fixture's bound of 5. A failed or torn read leaves the slot empty, so the
/// next caller reads again.
fn digest_file(path: &Path) -> Result<(String, FileStamp), String> {
    use sha2::{Digest, Sha256};
    use std::io::Read;

    let before = file_stamp(path).ok_or_else(|| "cannot stat the executable".to_owned())?;
    let slot = digest_memo_slot(path, &before);
    // Held across the read below. The memo's own lock is already released, so
    // the memo -> slot order is never inverted and a digest of another file
    // state never waits on this one.
    let mut slot = slot.lock().unwrap_or_else(|poisoned| poisoned.into_inner());
    if let Some(sha256) = slot.as_ref() {
        return Ok((sha256.clone(), before));
    }
    #[cfg(test)]
    note_digest_computed(path);
    let mut file = std::fs::File::open(path)
        .map_err(|error| format!("cannot open the executable: {error}"))?;
    let mut hasher = Sha256::new();
    let mut buffer = vec![0u8; 1 << 20];
    let mut total = 0u64;
    loop {
        let read = file
            .read(&mut buffer)
            .map_err(|error| format!("cannot read the executable: {error}"))?;
        if read == 0 {
            break;
        }
        hasher.update(&buffer[..read]);
        total = total.saturating_add(read as u64);
    }
    crate::process_cost::note_executable_digest(total, "digest_ay_file");
    #[cfg(test)]
    after_whole_read(path);
    let sha256 = format!("{:x}", hasher.finalize());
    if file_stamp(path).as_ref() != Some(&before) {
        return Err("the executable changed while it was being digested".to_owned());
    }
    *slot = Some(sha256.clone());
    Ok((sha256, before))
}

/// One file state's digest: empty until a read of that state completes.
type DigestSlot = std::sync::Arc<Mutex<Option<String>>>;

type DigestMemo = Vec<((PathBuf, FileStamp), DigestSlot)>;

const DIGEST_MEMO_CAPACITY: usize = 32;

fn digest_memo() -> &'static Mutex<DigestMemo> {
    static MEMO: OnceLock<Mutex<DigestMemo>> = OnceLock::new();
    MEMO.get_or_init(|| Mutex::new(Vec::new()))
}

// In-process only. A digest persisted outside this process would be a trust
// input an unprivileged writer could forge.
fn digest_memo_slot(path: &Path, stamp: &FileStamp) -> DigestSlot {
    let mut memo = digest_memo()
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner());
    if let Some((_, slot)) = memo
        .iter()
        .find(|((cached_path, cached_stamp), _)| cached_path == path && cached_stamp == stamp)
    {
        return std::sync::Arc::clone(slot);
    }
    if memo.len() == DIGEST_MEMO_CAPACITY {
        drop(memo.remove(0));
    }
    let slot = DigestSlot::default();
    memo.push((
        (path.to_path_buf(), stamp.clone()),
        std::sync::Arc::clone(&slot),
    ));
    slot
}

/// How many times [`digest_file`] actually read each path, so the
/// compute-once property can be asserted. Test-only; production never reads it.
#[cfg(test)]
fn digest_computations() -> &'static Mutex<std::collections::HashMap<PathBuf, usize>> {
    static COUNTS: OnceLock<Mutex<std::collections::HashMap<PathBuf, usize>>> = OnceLock::new();
    COUNTS.get_or_init(|| Mutex::new(std::collections::HashMap::new()))
}

#[cfg(test)]
fn note_digest_computed(path: &Path) {
    *digest_computations()
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner())
        .entry(path.to_path_buf())
        .or_insert(0) += 1;
}

/// Test-only: an action on a file that was just read whole.
#[cfg(test)]
type AfterWholeRead = Box<dyn FnOnce(&Path)>;

#[cfg(test)]
thread_local! {
    /// Test-only: what this thread's next whole read of an executable
    /// ([`digest_file`], or the one-read admission's copy) does with the file
    /// after reading it and before checking that its stamp still holds.
    static AFTER_WHOLE_READ: std::cell::RefCell<Option<AfterWholeRead>> =
        const { std::cell::RefCell::new(None) };
}

/// Test-only: run `action` on the file this thread next reads whole, after
/// the read and before its stamp is checked again.
#[cfg(test)]
fn on_next_whole_read(action: impl FnOnce(&Path) + 'static) {
    AFTER_WHOLE_READ.with(|next| *next.borrow_mut() = Some(Box::new(action)));
}

#[cfg(test)]
fn after_whole_read(path: &Path) {
    if let Some(action) = AFTER_WHOLE_READ.with(|next| next.borrow_mut().take()) {
        action(path);
    }
}

#[cfg(test)]
fn digest_computation_count(path: &Path) -> usize {
    digest_computations()
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner())
        .get(path)
        .copied()
        .unwrap_or(0)
}

fn admit(
    candidate: Candidate,
    digested: Result<(String, FileStamp), String>,
) -> Result<PinnedAy, AyIdentityRefusal> {
    let (found_sha256, stamp) = digested.map_err(|reason| AyIdentityRefusal::Unidentified {
        route: candidate.route,
        path: candidate.path.clone(),
        reason,
    })?;
    let Some(identity) = candidate
        .admissible
        .iter()
        .find(|identity| identity.sha256 == found_sha256)
        .cloned()
    else {
        return Err(AyIdentityRefusal::Mismatch {
            route: candidate.route,
            path: candidate.path,
            expected: Box::new(candidate.admissible[0].clone()),
            found_sha256,
        });
    };
    let copy =
        ay_private_copy::materialize(&candidate.path, identity.sha256()).map_err(|reason| {
            AyIdentityRefusal::Unmaterialized {
                route: candidate.route,
                path: candidate.path.clone(),
                reason,
            }
        })?;
    Ok(PinnedAy {
        path: candidate.path,
        identity,
        route: candidate.route,
        toolchain: candidate.toolchain,
        stamp,
        copy,
    })
}

fn resolve(inputs: ResolutionInputs<'_>) -> Result<PinnedAy, AyIdentityRefusal> {
    let candidate = candidate(inputs)?;
    let digested = match admit_while_copying(&candidate) {
        OneReadAdmission::Admitted(pinned) => return Ok(*pinned),
        OneReadAdmission::Digested(found, stamp) => Ok((found, stamp)),
        OneReadAdmission::Undecided => digest_file(&candidate.path),
    };
    admit(candidate, digested)
}

/// What [`admit_while_copying`] decided.
enum OneReadAdmission {
    Admitted(Box<PinnedAy>),
    /// The candidate's bytes in this file state digest to this, which is not
    /// the admitted identity; [`admit`] refuses it from this digest.
    Digested(String, FileStamp),
    /// The caller takes the separate admission digest.
    Undecided,
}

/// Admission and the private copy from ONE read of the candidate, when this
/// process has not digested the candidate's current file state yet and no
/// copy is published (a fresh cache root): see
/// [`ay_private_copy::materialize_admitting`].
///
/// Only when exactly one identity is admissible (every production build),
/// because the copy's directory is named by the digest the bytes must have.
/// The candidate's memo slot is held throughout, so a concurrent
/// [`digest_file`] of the same file state waits and then reads the digest
/// recorded here. A read that completed in the stamped state records its
/// digest in the slot whatever it is: the admitted identity, or other bytes,
/// which [`admit`] then refuses as a mismatch without reading them again.
/// [`OneReadAdmission::Undecided`] leaves the slot empty, unless the source
/// was admitted and then the published copy failed its checks; the slot then
/// holds the source's digest, which is correct for that state. The caller
/// runs the separate admission digest and [`admit`], whose refusals are
/// unchanged.
fn admit_while_copying(candidate: &Candidate) -> OneReadAdmission {
    let [identity] = candidate.admissible.as_slice() else {
        return OneReadAdmission::Undecided;
    };
    let Some(stamp) = file_stamp(&candidate.path) else {
        return OneReadAdmission::Undecided;
    };
    let slot = digest_memo_slot(&candidate.path, &stamp);
    let mut slot = slot.lock().unwrap_or_else(|poisoned| poisoned.into_inner());
    if slot.is_some() {
        return OneReadAdmission::Undecided;
    }
    let outcome =
        ay_private_copy::materialize_admitting(&candidate.path, &stamp, identity.sha256(), || {
            #[cfg(test)]
            note_digest_computed(&candidate.path);
            *slot = Some(identity.sha256().to_owned());
        });
    match outcome {
        ay_private_copy::OneRead::Admitted(copy) => {
            OneReadAdmission::Admitted(Box::new(PinnedAy {
                path: candidate.path.clone(),
                identity: identity.clone(),
                route: candidate.route,
                toolchain: candidate.toolchain.clone(),
                stamp,
                copy,
            }))
        }
        ay_private_copy::OneRead::OtherBytes(found) => {
            #[cfg(test)]
            note_digest_computed(&candidate.path);
            *slot = Some(found.clone());
            OneReadAdmission::Digested(found, stamp)
        }
        ay_private_copy::OneRead::Undecided => OneReadAdmission::Undecided,
    }
}

/// Apply the rule to THIS process: its executable, the compiled-in record, and
/// the request-scoped `AY_SOLVER_PATH` (read through `trust-cg-process-env`).
///
/// Solver availability is polled per function during codegen, so a digest is
/// memoized in-process against the executable's exact file state.
pub fn resolve_for_process() -> Result<PinnedAy, AyIdentityRefusal> {
    let override_value = trust_cg_process_env::var_os(AY_OVERRIDE_ENV);
    let running_exe = std::env::current_exe().ok();
    resolve(ResolutionInputs {
        running_exe: running_exe.as_deref(),
        record: ToolchainAyRecord::recorded(),
        naming: Naming::Process(override_value.as_deref()),
    })
}

/// Apply the rule to a path chosen in code (a caller's configuration, a
/// certificate producer, a test that names its solver). The path must be
/// absolute and its bytes must be the recorded AY; it is never searched for.
pub fn resolve_explicit_path(path: impl AsRef<OsStr>) -> Result<PinnedAy, AyIdentityRefusal> {
    let running_exe = std::env::current_exe().ok();
    resolve(ResolutionInputs {
        running_exe: running_exe.as_deref(),
        record: ToolchainAyRecord::recorded(),
        naming: Naming::Explicit(path.as_ref()),
    })
}

/// Unit-test fixture admission. Compiled only into this crate's `cfg(test)`
/// build; see the module documentation.
#[cfg(test)]
pub(crate) mod test_fixtures {
    use super::*;
    use std::cell::Cell;

    thread_local! {
        static RECORDED: Cell<Option<&'static ToolchainAyRecord>> = const { Cell::new(None) };
    }

    /// The fixture record standing in for the build record on this thread.
    pub(crate) fn recorded_override() -> Option<&'static ToolchainAyRecord> {
        RECORDED.with(Cell::get)
    }

    /// Run `f` with `record` standing in for this crate's build record
    /// ([`ToolchainAyRecord::recorded`]) on the current thread, so a test in an
    /// ordinary build drives the production readers of the record (the checker
    /// policy and its discovery) as an overlay build would. The record is
    /// leaked: `recorded` hands out `'static` references.
    pub(crate) fn with_recorded<T>(record: ToolchainAyRecord, f: impl FnOnce() -> T) -> T {
        struct Restore(Option<&'static ToolchainAyRecord>);
        impl Drop for Restore {
            fn drop(&mut self) {
                RECORDED.with(|recorded| recorded.set(self.0));
            }
        }
        let record: &'static ToolchainAyRecord = Box::leak(Box::new(record));
        let _restore = Restore(RECORDED.with(|recorded| recorded.replace(Some(record))));
        f()
    }

    /// Run `f` under an ordinary build's record: no overlay, so no checker is
    /// pinned and an explicitly selected fixture checker resolves as it does
    /// in a package build. An overlay build's own record pins its real Clean
    /// and refuses every fixture checker, so a test written against an
    /// ordinary build's resolution failed only in overlay builds (the
    /// qualification host's among them) without this.
    pub(crate) fn with_ordinary_record<T>(f: impl FnOnce() -> T) -> T {
        with_recorded(
            ToolchainAyRecord::new(
                PathBuf::from("/nonexistent-fixture-sysroot"),
                Err("transport fixture: an ordinary build's record".into()),
            ),
            f,
        )
    }

    /// Scoped variable (read through `trust-cg-process-env`, so it follows the
    /// same request scopes and worker snapshots as `AY_SOLVER_PATH`) holding
    /// comma-separated SHA-256 digests of fixture executables.
    pub(crate) const FIXTURE_DIGESTS_ENV: &str = "AY_UNIT_TEST_FIXTURE_SHA256";

    /// A fixture script that names ITSELF by `path` instead of `$0`.
    ///
    /// An admitted AY is started from its private copy (`ay_private_copy`),
    /// so inside a started fixture `$0` is that copy, shared by every fixture
    /// with the same bytes. A fixture whose side files (`.calls`, `.release`,
    /// `.executed`, …) belong to the test that wrote it, or that rewrites the
    /// admitted file, names that file literally. Embedding the path also makes
    /// each fixture's bytes, and so its private copy, its own.
    pub(crate) fn bind_self(path: &Path, script: &str) -> String {
        let literal = path.to_str().expect("fixture path is UTF-8");
        assert!(
            !literal.contains(['"', '$', '`', '\\']),
            "fixture path {literal:?} cannot be embedded in a double-quoted shell word"
        );
        script.replace("$0", literal)
    }

    /// First argument a fixture answers by exiting 0 before its body runs, so
    /// that [`warm`] starts it without doing anything its test observes.
    pub(crate) const WARM_ARGUMENT: &str = "--trust-cg-fixture-warm";

    /// The line, right after `#!/bin/sh`, that makes a fixture answer
    /// [`WARM_ARGUMENT`] that way.
    pub(crate) fn warm_guard() -> String {
        format!("test \"$1\" = {WARM_ARGUMENT} && exit 0")
    }

    /// `script` with [`warm_guard`] inserted right after its `#!` line.
    pub(crate) fn with_warm_guard(script: &str) -> String {
        let (interpreter, body) = script
            .split_once('\n')
            .filter(|(interpreter, _)| interpreter.starts_with("#!"))
            .expect("a fixture script starts with its #! line");
        format!("{interpreter}\n{}\n{body}", warm_guard())
    }

    /// Start a new fixture executable once, outside every deadline, before
    /// its test gives it one. The fixture must answer [`WARM_ARGUMENT`]
    /// ([`warm_guard`]) by exiting 0.
    ///
    /// macOS assesses a newly created executable on its FIRST `exec`, inside
    /// the child, after `posix_spawn` has already returned. Measured
    /// 2026-09-27 on the loaded audit host (load average 25-43): a fresh
    /// three-line script took a median 215 ms and up to 1.7 s to run its first
    /// time and 8 ms its second; a byte-identical copy at a new path pays
    /// again. Measured 2026-09-30 at load average 32-38: 0.17-6.0 s first,
    /// 4 ms second. Every fixture is a new file, and an admitted AY fixture is
    /// started from a new private copy of it, so that cost used to land inside
    /// whatever deadline the test's first call held. The product makes that
    /// first start before any deadline only for an AY build
    /// (`first_start`); a fixture is exempt there because its side files
    /// count exactly the starts its test makes. So a test that bounded a
    /// fresh fixture by a deadline of a few seconds failed whenever the
    /// assessment outlasted it, whatever the fixture did: 0.016 s, or the
    /// whole 5 s with the script never started. Paying it here leaves the
    /// deadlines measuring what the tests are about; a fixture that really
    /// misses its deadline still does.
    ///
    /// Both files a test can start are warmed: the fixture itself (a checker
    /// or driver is run from its path) and the private copy an admitted AY is
    /// started from (the same file for every later admission of these bytes
    /// in this process, by [`pin`] or by a declared `AY_SOLVER_PATH`). Both
    /// starts are made at once: the host assesses new files one at a time for
    /// every process, so queueing them together waits for that queue once.
    ///
    /// Like the product's first start, a warm-up is stopped after
    /// `first_start::ALLOWANCE` (120 s), a hang guard rather than a budget: on
    /// 2026-09-30, with other worktrees' compiler builds publishing new
    /// executables, a fresh script's first start waited over 5 minutes in
    /// that queue. A warm-up stopped there is reported, and the test's own
    /// deadline then pays the rest of the assessment, as it would without
    /// this.
    pub(crate) fn warm(path: &Path) {
        #[cfg(unix)]
        const ETXTBSY: Option<i32> = Some(libc::ETXTBSY);
        #[cfg(not(unix))]
        const ETXTBSY: Option<i32> = None;
        let copy = pin(path).command().expect("admitted fixture copy");
        let deadline = std::time::Instant::now() + first_start::ALLOWANCE;
        let starts: Vec<_> = [std::process::Command::new(path), copy]
            .into_iter()
            .map(|mut command| {
                command
                    .arg(WARM_ARGUMENT)
                    .stdin(std::process::Stdio::null())
                    .stdout(std::process::Stdio::null())
                    .stderr(std::process::Stdio::null());
                // ETXTBSY: a sibling test thread that forked while this file
                // was open for writing holds that descriptor until its own
                // exec; the condition is transient.
                let mut attempt = 0;
                loop {
                    match command.spawn() {
                        Err(error) if error.raw_os_error() == ETXTBSY && attempt < 100 => {
                            attempt += 1;
                            std::thread::sleep(std::time::Duration::from_millis(2));
                        }
                        started => break (command, started.expect("start the fixture's warm-up")),
                    }
                }
            })
            .collect();
        for (command, mut child) in starts {
            let program = Path::new(command.get_program()).display();
            loop {
                match child.try_wait().expect("poll the fixture's warm-up") {
                    Some(status) => {
                        assert!(status.success(), "warming {program} failed: {status}");
                        break;
                    }
                    None if std::time::Instant::now() >= deadline => {
                        let _ = child.kill();
                        let _ = child.wait();
                        eprintln!(
                            "test_fixtures::warm: the warm-up start of {program} did not finish \
                             within {:?} and was stopped; its test's deadline may pay the rest \
                             of the host's first-start assessment",
                            first_start::ALLOWANCE
                        );
                        break;
                    }
                    None => std::thread::sleep(std::time::Duration::from_millis(5)),
                }
            }
        }
    }

    /// SHA-256 of a fixture file's bytes.
    pub(crate) fn sha256_of(path: &Path) -> String {
        digest_file(path)
            .unwrap_or_else(|reason| panic!("fixture {} has no digest: {reason}", path.display()))
            .0
    }

    /// Value for [`FIXTURE_DIGESTS_ENV`] declaring these exact fixture bytes.
    pub(crate) fn declare(paths: &[&Path]) -> String {
        paths
            .iter()
            .map(|path| sha256_of(path))
            .collect::<Vec<_>>()
            .join(",")
    }

    /// Fixture identities declared in the current scope.
    pub(super) fn declared() -> Vec<AyIdentity> {
        let Some(value) = trust_cg_process_env::var_os(FIXTURE_DIGESTS_ENV) else {
            return Vec::new();
        };
        value
            .to_string_lossy()
            .split(',')
            .filter(|digest| is_sha256_hex(digest))
            .map(|digest| AyIdentity {
                sha256: digest.to_owned(),
                build: None,
                overlay: None,
            })
            .collect()
    }

    /// A process-wide fixture for tests that need an admitted AY value but must
    /// never run a solver (memo/key plumbing): any invocation exits 97.
    pub(crate) fn inert() -> PinnedAy {
        static INERT: OnceLock<PathBuf> = OnceLock::new();
        let path = INERT.get_or_init(|| {
            let directory = tempfile::Builder::new()
                .prefix("trust-cg-verify-inert-ay-")
                .tempdir()
                .expect("create inert AY fixture directory")
                .keep();
            ay_private_copy::remove_at_process_exit(&directory);
            let path = directory.join(executable_name());
            std::fs::write(&path, "#!/bin/sh\n# inert unit-test AY fixture\nexit 97\n")
                .expect("write inert AY fixture");
            #[cfg(unix)]
            {
                use std::os::unix::fs::PermissionsExt;
                std::fs::set_permissions(&path, std::fs::Permissions::from_mode(0o755))
                    .expect("make inert AY fixture executable");
            }
            path
        });
        pin(path)
    }

    /// Admit `path` as an explicit path against a record containing only its
    /// own current bytes — the same candidate/digest/compare path as
    /// production, with the fixture as the recorded AY.
    pub(crate) fn pin(path: &Path) -> PinnedAy {
        pin_with_build(path, None)
    }

    /// Measured `--version` output of the Trust 9178 bundle's `bin/ay`, used
    /// as the build label of a fixture standing in for a real AY build.
    const STAND_IN_BUILD_BANNER: &str =
        "ay 0.26.0+build.9624.075a482aec84e441918d935743957876bd24afdb@2026-09-16T06:27:30Z
build.version=0.26.0
build.increment=9624
build.commit=075a482aec84e441918d935743957876bd24afdb
build.datetime_utc=2026-09-16T06:27:30Z
build.stamp=0.26.0+build.9624.075a482aec84e441918d935743957876bd24afdb@2026-09-16T06:27:30Z
";

    /// [`pin`] for a fixture standing in for a real AY build: its identity
    /// carries a build banner, so it is started the way the toolchain AY is,
    /// including the first start of its copy (see `first_start`). Its copy
    /// still lives in this process's fixture root.
    pub(crate) fn pin_as_build(path: &Path) -> PinnedAy {
        let build = parse_ay_version_banner(STAND_IN_BUILD_BANNER)
            .expect("the stand-in build banner parses");
        pin_with_build(path, Some(build))
    }

    fn pin_with_build(path: &Path, build: Option<AyBuildIdentity>) -> PinnedAy {
        let record = ToolchainAyRecord::new(
            PathBuf::from("/nonexistent-fixture-sysroot"),
            Ok(AyIdentity {
                sha256: sha256_of(path),
                build,
                overlay: None,
            }),
        );
        resolve(ResolutionInputs {
            running_exe: None,
            record: &record,
            naming: Naming::Explicit(path.as_os_str()),
        })
        .unwrap_or_else(|refusal| panic!("fixture {} not admitted: {refusal}", path.display()))
    }
}

#[cfg(test)]
#[path = "ay_identity_tests.rs"]
mod tests;
