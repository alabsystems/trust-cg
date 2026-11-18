#![cfg_attr(
    all(unix, feature = "trust-child-resources"),
    feature(trust_process_inherit_fds)
)]
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Thread-local environment overrides for the trust-cg workspace.
//!
//! Rust 2024 correctly makes process-environment mutation unsafe. On Unix, a
//! writer-only mutex cannot establish the required absence of concurrent
//! environment readers, including hidden readers in libc or the standard
//! library. This crate therefore never calls `std::env::set_var` or
//! `std::env::remove_var`.
//!
//! Trust-cg code that needs an in-process override reads through [`var`] or
//! [`var_os`]. Overrides are nested, restore-on-unwind, exact [`OsString`]
//! values scoped to the current thread, so parallel tests cannot observe one
//! another's temporary configuration. Code launching a child applies the
//! current override set with [`apply_to_command`], which uses the safe
//! per-command environment API.
//!
//! Overrides are deliberately not inherited by newly spawned threads. Parallel
//! in-process work must receive explicit configuration, or callers must keep
//! override-sensitive work on the thread that owns the scope.

use sha2::{Digest, Sha256};
use std::cell::{Cell, RefCell};
use std::env::VarError;
use std::ffi::{OsStr, OsString};
use std::marker::PhantomData;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::rc::Rc;
use std::sync::OnceLock;

pub mod private_fs;
pub mod resource_budget;
#[cfg(feature = "trust-child-resources")]
pub mod trust_child;

/// Environment namespaces reserved for Trust Codegen compiler controls.
///
/// Artifact-cache clients should not try to maintain a list of today's
/// behavior-changing switches. A new variable in either namespace is an
/// unkeyed compiler input until it is migrated into an explicit compile policy
/// or deliberately classified as cache transport/identity metadata below.
pub const COMPILER_CONTROL_ENV_PREFIXES: &[&str] = &["TCG_", "TRUST_CG_"];

/// Trust Codegen environment variables that do not change compiler behavior.
///
/// `TCG_ARTIFACT_CACHE_DIR` and `TRUST_CG_JIT_DISK_CACHE` select cache
/// transport only. The `TRUST_CG_COMPILE_ARTIFACT_*` variables populate the
/// dependency/toolchain identity already carried by Trust Codegen's canonical
/// object-cache key. Every other present variable in a reserved namespace is
/// conservatively treated as an unkeyed compiler input.
///
/// In particular, `TRUST_CG_MAX_PARALLELISM` is intentionally not exempt yet.
/// Order-stable executor lanes consume its typed artifact-neutral view through
/// [`resource_budget::ArtifactNeutralExecutorBudget`], but legacy search lanes
/// can still let the effective width influence a chosen result. The shared
/// environment boundary must remain fail-closed until every such lane carries
/// an [`resource_budget::IdentityBoundSearchPolicy`] in artifact identity.
pub const ARTIFACT_REUSE_ENV_EXEMPT_KEYS: &[&str] = &[
    "TCG_ARTIFACT_CACHE_DIR",
    "TRUST_CG_JIT_DISK_CACHE",
    "TRUST_CG_COMPILE_ARTIFACT_AY_IDENTITY",
    "TRUST_CG_COMPILE_ARTIFACT_CARGO_IDENTITY",
    "TRUST_CG_COMPILE_ARTIFACT_DEPENDENCY_MODE",
    "TRUST_CG_COMPILE_ARTIFACT_RUSTC_IDENTITY",
    "TRUST_CG_COMPILE_ARTIFACT_TRUST_CG_IDENTITY",
    "TRUST_CG_COMPILE_ARTIFACT_TRUST_IR_IDENTITY",
];

/// Immutable, digest-bound environment for verifier subprocesses.
///
/// Capturing an unrestricted parent environment would let unrelated compiler
/// controls, shell state, and dynamic-loader search paths affect a solver or
/// proof checker. [`Self::capture_verifier`] instead builds a fixed environment
/// with these rules:
///
/// - `PATH` is `/usr/bin:/bin` on Unix; verifier authorities should otherwise
///   be launched by their already-resolved exact path.
/// - `LC_ALL` and `LANG` are always `C`, independent of the parent locale.
/// - `TMPDIR`, `TMP`, and `TEMP` are copied when present so platform temporary
///   storage remains usable.
/// - `GOVERN_AY_MB`, `AY_CONCURRENCY`, `MIMALLOC_ARENA_RESERVE`,
///   `RAYON_NUM_THREADS`, and `RUST_MIN_STACK` are the only inherited resource
///   controls.
/// - Windows additionally retains `SystemRoot`, `WINDIR`, `ComSpec`, and
///   `PATHEXT`, which are operating-system process-launch resources.
/// - The current working directory is captured, digest-bound, and explicitly
///   applied so it cannot drift between authority capture and child spawn.
///
/// Every copied value is read through this crate's [`var_os`] boundary, so a
/// request's scoped overrides are respected. In particular, arbitrary
/// `TCG_*`, `TRUST_*`, or `AY_*` algorithm controls, home/cache directories,
/// and `LD_*`/`DYLD_*` loader overrides are not inherited. Callers must bind an
/// exact solver/checker executable identity separately; this digest authenticates
/// only the child environment, not filesystem content named by an entry.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct SanitizedChildEnv {
    entries: Vec<(OsString, OsString)>,
    working_dir: Option<PathBuf>,
    digest: [u8; 32],
}

const VERIFIER_CHILD_ENV_DOMAIN: &[u8] = b"trust-cg/verifier-child-env/v1\0";

const VERIFIER_CHILD_INHERITED_KEYS: &[&str] = &[
    "AY_CONCURRENCY",
    "GOVERN_AY_MB",
    "MIMALLOC_ARENA_RESERVE",
    "RAYON_NUM_THREADS",
    "RUST_MIN_STACK",
    "TEMP",
    "TMP",
    "TMPDIR",
];

#[cfg(windows)]
const VERIFIER_CHILD_WINDOWS_INHERITED_KEYS: &[&str] =
    &["ComSpec", "PATHEXT", "SystemRoot", "WINDIR"];

impl SanitizedChildEnv {
    /// Capture the exact environment permitted for a verifier subprocess.
    pub fn capture_verifier() -> Self {
        let mut entries = Vec::with_capacity(
            VERIFIER_CHILD_INHERITED_KEYS.len()
                + if cfg!(windows) { 4 } else { 0 }
                + if cfg!(unix) { 1 } else { 0 }
                + 2,
        );
        for key in VERIFIER_CHILD_INHERITED_KEYS {
            if let Some(value) = var_os(key) {
                entries.push((OsString::from(*key), value));
            }
        }
        #[cfg(windows)]
        for key in VERIFIER_CHILD_WINDOWS_INHERITED_KEYS {
            if let Some(value) = var_os(key) {
                entries.push((OsString::from(*key), value));
            }
        }

        #[cfg(unix)]
        entries.push((OsString::from("PATH"), OsString::from("/usr/bin:/bin")));
        entries.push((OsString::from("LANG"), OsString::from("C")));
        entries.push((OsString::from("LC_ALL"), OsString::from("C")));

        entries.sort_by(|left, right| left.0.as_encoded_bytes().cmp(right.0.as_encoded_bytes()));
        let working_dir = std::env::current_dir().ok();
        let digest = sanitized_child_env_digest(&entries, working_dir.as_deref());
        Self {
            entries,
            working_dir,
            digest,
        }
    }

    /// Return the stable SHA-256 digest of the exact sorted child environment.
    ///
    /// Unix names and values are hashed as their raw bytes. Windows names and
    /// values are hashed as little-endian wide code units. Length prefixes and
    /// a platform-specific encoding tag make the representation unambiguous;
    /// no lossy Unicode conversion is performed.
    pub fn digest(&self) -> [u8; 32] {
        self.digest
    }

    /// The working directory captured with this exact child environment.
    /// `None` is an incomplete execution identity: applying the snapshot then
    /// retains the command's ordinary working-directory behavior. Consumers
    /// must not authorize reusable results from an incomplete snapshot.
    pub fn working_dir(&self) -> Option<&Path> {
        self.working_dir.as_deref()
    }

    /// Resolve a selected path against this snapshot, without observing a later
    /// process working directory or canonicalizing symlink spelling.
    pub fn anchor_path(&self, path: &Path) -> Option<PathBuf> {
        if path.is_absolute() {
            Some(path.to_path_buf())
        } else {
            self.working_dir().map(|base| base.join(path))
        }
    }

    /// Clear a command's inherited environment and install this exact snapshot.
    pub fn apply_to_command(&self, command: &mut Command) {
        command.env_clear();
        for (key, value) in &self.entries {
            command.env(key, value);
        }
        if let Some(working_dir) = &self.working_dir {
            command.current_dir(working_dir);
        }
    }
}

/// Resolve one executable using the current request's effective `PATH` while
/// preserving the exact selected spelling for process execution.
///
/// This is intended for callers that will subsequently `env_clear` a child:
/// a bare command must be resolved before the inherited search path is
/// removed. Symlinks are deliberately not canonicalized because their path
/// can affect `argv[0]`, wrapper behavior, and sibling-resource discovery.
/// On Unix, non-executable regular files are skipped. On Windows, `PATHEXT` is
/// honored for both bare commands and explicit extension-less paths.
pub fn resolve_executable_path(command: &OsStr) -> Option<PathBuf> {
    let command_path = Path::new(command);
    if command_path.components().count() > 1 {
        return resolve_executable_candidate(command_path);
    }

    let path = var_os("PATH")?;
    for directory in std::env::split_paths(&path) {
        if let Some(resolved) = resolve_executable_candidate(&directory.join(command_path)) {
            return Some(resolved);
        }
    }
    None
}

/// Resolve using the effective discovery PATH, but anchor every relative
/// candidate to one already-captured child working directory. This does not
/// reuse the sanitized child's fixed PATH as the discovery PATH.
pub fn resolve_executable_path_with_environment(
    command: &OsStr,
    child_env: &SanitizedChildEnv,
) -> Option<PathBuf> {
    let command_path = Path::new(command);
    if command_path.components().count() > 1 {
        return resolve_executable_candidate(&child_env.anchor_path(command_path)?);
    }
    for directory in std::env::split_paths(&var_os("PATH")?) {
        let Some(candidate) = child_env.anchor_path(&directory.join(command_path)) else {
            continue;
        };
        if let Some(resolved) = resolve_executable_candidate(&candidate) {
            return Some(resolved);
        }
    }
    None
}

fn resolve_executable_candidate(candidate: &Path) -> Option<PathBuf> {
    if executable_file(candidate) {
        return Some(candidate.to_path_buf());
    }

    #[cfg(windows)]
    if candidate.extension().is_none() {
        let pathext = var("PATHEXT").unwrap_or_else(|_| ".COM;.EXE;.BAT;.CMD".to_string());
        for extension in pathext
            .split(';')
            .map(str::trim)
            .filter(|value| !value.is_empty())
        {
            let extension = extension.strip_prefix('.').unwrap_or(extension);
            let with_extension = candidate.with_extension(extension);
            if executable_file(&with_extension) {
                return Some(with_extension);
            }
        }
    }

    None
}

fn executable_file(path: &Path) -> bool {
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

fn sanitized_child_env_digest(
    entries: &[(OsString, OsString)],
    working_dir: Option<&Path>,
) -> [u8; 32] {
    let mut hasher = Sha256::new();
    hasher.update(VERIFIER_CHILD_ENV_DOMAIN);
    #[cfg(unix)]
    hasher.update(b"unix/raw-bytes\0");
    #[cfg(windows)]
    hasher.update(b"windows/wide-le\0");
    #[cfg(not(any(unix, windows)))]
    hasher.update(b"other/rust-encoded-bytes\0");
    hasher.update((entries.len() as u128).to_le_bytes());
    for (key, value) in entries {
        update_digest_with_os_str(&mut hasher, key);
        update_digest_with_os_str(&mut hasher, value);
    }
    match working_dir {
        Some(path) => {
            hasher.update(b"working-dir-present\0");
            update_digest_with_os_str(&mut hasher, path.as_os_str());
        }
        None => hasher.update(b"working-dir-unavailable\0"),
    }
    hasher.finalize().into()
}

fn update_digest_with_os_str(hasher: &mut Sha256, value: &OsStr) {
    #[cfg(unix)]
    {
        use std::os::unix::ffi::OsStrExt;

        let bytes = value.as_bytes();
        hasher.update((bytes.len() as u128).to_le_bytes());
        hasher.update(bytes);
    }
    #[cfg(windows)]
    {
        use std::os::windows::ffi::OsStrExt;

        hasher.update((value.encode_wide().count() as u128).to_le_bytes());
        for unit in value.encode_wide() {
            hasher.update(unit.to_le_bytes());
        }
    }
    #[cfg(not(any(unix, windows)))]
    {
        let bytes = value.as_encoded_bytes();
        hasher.update((bytes.len() as u128).to_le_bytes());
        hasher.update(bytes);
    }
}

/// Fail-closed snapshot of ambient compiler controls at an artifact boundary.
///
/// This is a necessary cache-reuse condition, not cache authentication: a
/// frontend must still bind source, explicit compile policy, target facts,
/// backend/dependency identity, proof policy, and artifact integrity. Unknown
/// future `TCG_*` or `TRUST_CG_*` controls become blockers automatically.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ArtifactReuseEnvironmentSafety {
    unkeyed_controls: Vec<OsString>,
}

impl ArtifactReuseEnvironmentSafety {
    /// Return true when no unkeyed ambient compiler controls are present.
    pub fn is_reuse_safe(&self) -> bool {
        self.unkeyed_controls.is_empty()
    }

    /// Return the sorted, deduplicated controls that prevent safe cache reuse.
    pub fn unkeyed_controls(&self) -> &[OsString] {
        &self.unkeyed_controls
    }
}

/// Temporal authorization for one artifact-cache reuse transaction.
///
/// A permit is issued only while the effective environment has no unkeyed
/// compiler controls. It is bound to the current thread and becomes
/// permanently invalid after any unkeyed compiler-control override is pushed
/// or removed on that thread, even when the override begins and ends between
/// cache lookup and publication. This closes the otherwise-invisible case
/// where a build runs inside a short-lived override and returns to a seemingly
/// safe environment before publishing its result.
#[derive(Debug)]
pub struct ArtifactReusePermit {
    mutation_epoch: u64,
    _thread_bound: PhantomData<Rc<()>>,
}

impl ArtifactReusePermit {
    /// Return true when this permit still authorizes artifact reuse.
    ///
    /// Validation requires both an unchanged per-thread mutation epoch and a
    /// currently safe effective environment. A permit cannot be moved to a
    /// different thread.
    pub fn is_valid(&self) -> bool {
        unkeyed_control_mutation_epoch() == Some(self.mutation_epoch)
            && artifact_reuse_environment_is_safe_fast()
    }
}

/// `Some(value)` overrides a key; `None` makes it logically absent.
type OverrideValue = Option<OsString>;

thread_local! {
    static OVERRIDES: RefCell<Vec<OverrideEntry>> = const { RefCell::new(Vec::new()) };
    static UNKEYED_CONTROL_MUTATION_STATE: Cell<UnkeyedControlMutationState> =
        const { Cell::new(UnkeyedControlMutationState { epoch: 0, exhausted: false }) };
}

#[derive(Clone, Copy)]
struct UnkeyedControlMutationState {
    epoch: u64,
    exhausted: bool,
}

fn unkeyed_control_mutation_epoch() -> Option<u64> {
    UNKEYED_CONTROL_MUTATION_STATE.with(|state| {
        let state = state.get();
        (!state.exhausted).then_some(state.epoch)
    })
}

fn bump_unkeyed_control_mutation_epoch() {
    UNKEYED_CONTROL_MUTATION_STATE.with(|state| {
        let current = state.get();
        let next = match current.epoch.checked_add(1) {
            Some(epoch) if !current.exhausted => UnkeyedControlMutationState {
                epoch,
                exhausted: false,
            },
            _ => UnkeyedControlMutationState {
                epoch: current.epoch,
                exhausted: true,
            },
        };
        state.set(next);
    });
}

#[derive(Clone)]
struct OverrideId(Rc<()>);

struct OverrideEntry {
    id: OverrideId,
    key: OsString,
    value: OverrideValue,
}

fn keys_equal(left: &OsStr, right: &OsStr) -> bool {
    #[cfg(windows)]
    {
        left.eq_ignore_ascii_case(right)
    }
    #[cfg(not(windows))]
    {
        left == right
    }
}

fn latest_override<'a>(overrides: &'a [OverrideEntry], key: &OsStr) -> Option<&'a OverrideValue> {
    overrides
        .iter()
        .rev()
        .find(|entry| keys_equal(&entry.key, key))
        .map(|entry| &entry.value)
}

fn push_override(key: &OsStr, value: OverrideValue) -> OverrideId {
    let id = OVERRIDES.with(|overrides| {
        let mut overrides = overrides.borrow_mut();
        let id = OverrideId(Rc::new(()));
        overrides.push(OverrideEntry {
            id: id.clone(),
            key: key.to_owned(),
            value,
        });
        id
    });
    if artifact_reuse_key_is_unkeyed_control(key) {
        bump_unkeyed_control_mutation_epoch();
    }
    id
}

fn remove_override(id: &OverrideId) {
    let removed_unkeyed_control = OVERRIDES.with(|overrides| {
        let mut overrides = overrides.borrow_mut();
        if let Some(index) = overrides
            .iter()
            .position(|entry| Rc::ptr_eq(&entry.id.0, &id.0))
        {
            let entry = overrides.remove(index);
            artifact_reuse_key_is_unkeyed_control(&entry.key)
        } else {
            false
        }
    });
    if removed_unkeyed_control {
        bump_unkeyed_control_mutation_epoch();
    }
}

/// Read one environment value, honoring the current thread's innermost
/// trust-cg override before falling back to the real process environment.
pub fn var_os(key: impl AsRef<OsStr>) -> Option<OsString> {
    let key = key.as_ref();
    let overridden = OVERRIDES.with(|overrides| {
        let overrides = overrides.borrow();
        latest_override(&overrides, key).cloned()
    });
    overridden.unwrap_or_else(|| std::env::var_os(key))
}

/// Read one Unicode environment value through [`var_os`].
pub fn var(key: impl AsRef<OsStr>) -> Result<String, VarError> {
    match var_os(key) {
        Some(value) => value.into_string().map_err(VarError::NotUnicode),
        None => Err(VarError::NotPresent),
    }
}

/// Snapshot the process environment with the current thread's trust-cg
/// overrides applied.
///
/// The returned iterator owns its snapshot. An explicitly removed override is
/// absent, and an explicitly set override replaces a matching process key.
pub fn vars_os() -> std::vec::IntoIter<(OsString, OsString)> {
    let mut values = std::env::vars_os().collect::<Vec<_>>();
    OVERRIDES.with(|overrides| {
        for entry in overrides.borrow().iter() {
            let position = values
                .iter()
                .position(|(candidate, _)| keys_equal(candidate, &entry.key));
            match (position, &entry.value) {
                (Some(index), Some(value)) => values[index].1 = value.clone(),
                (Some(index), None) => {
                    values.remove(index);
                }
                (None, Some(value)) => values.push((entry.key.clone(), value.clone())),
                (None, None) => {}
            }
        }
    });
    values.into_iter()
}

fn key_has_compiler_control_prefix(key: &OsStr) -> bool {
    let key = key.to_string_lossy();
    COMPILER_CONTROL_ENV_PREFIXES.iter().any(|prefix| {
        #[cfg(windows)]
        {
            key.get(..prefix.len())
                .is_some_and(|head| head.eq_ignore_ascii_case(prefix))
        }
        #[cfg(not(windows))]
        {
            key.starts_with(prefix)
        }
    })
}

fn artifact_reuse_key_is_exempt(key: &OsStr) -> bool {
    ARTIFACT_REUSE_ENV_EXEMPT_KEYS
        .iter()
        .any(|exempt| keys_equal(key, OsStr::new(exempt)))
}

fn artifact_reuse_key_is_unkeyed_control(key: &OsStr) -> bool {
    key_has_compiler_control_prefix(key) && !artifact_reuse_key_is_exempt(key)
}

fn push_unkeyed_control(controls: &mut Vec<OsString>, key: OsString) {
    if artifact_reuse_key_is_unkeyed_control(&key)
        && !controls.iter().any(|existing| keys_equal(existing, &key))
    {
        controls.push(key);
    }
}

fn sort_unkeyed_controls(controls: &mut [OsString]) {
    controls.sort_by(|left, right| left.as_encoded_bytes().cmp(right.as_encoded_bytes()));
}

/// Classify an explicit environment snapshot for artifact-cache reuse.
///
/// Presence is significant even when a value is empty: many legacy compiler
/// switches use `var_os(...).is_some()`. The result is sorted and deduplicated
/// so callers can emit stable diagnostics without exposing environment values.
pub fn artifact_reuse_environment_safety_from<I>(variables: I) -> ArtifactReuseEnvironmentSafety
where
    I: IntoIterator<Item = (OsString, OsString)>,
{
    let mut unkeyed_controls = Vec::<OsString>::new();
    for (key, _) in variables {
        push_unkeyed_control(&mut unkeyed_controls, key);
    }
    sort_unkeyed_controls(&mut unkeyed_controls);
    ArtifactReuseEnvironmentSafety { unkeyed_controls }
}

fn raw_process_unkeyed_controls() -> &'static [OsString] {
    static RAW_CONTROLS: OnceLock<Vec<OsString>> = OnceLock::new();
    RAW_CONTROLS.get_or_init(|| {
        artifact_reuse_environment_safety_from(std::env::vars_os()).unkeyed_controls
    })
}

fn active_thread_override_unkeyed_controls() -> Vec<OsString> {
    OVERRIDES.with(|overrides| {
        let overrides = overrides.borrow();
        let mut seen = Vec::<OsString>::new();
        let mut controls = Vec::<OsString>::new();
        for entry in overrides.iter().rev() {
            if !key_has_compiler_control_prefix(&entry.key)
                || artifact_reuse_key_is_exempt(&entry.key)
                || seen.iter().any(|existing| keys_equal(existing, &entry.key))
            {
                continue;
            }
            seen.push(entry.key.clone());
            if entry.value.is_some() {
                controls.push(entry.key.clone());
            }
        }
        sort_unkeyed_controls(&mut controls);
        controls
    })
}

fn active_thread_override_has_unkeyed_control() -> bool {
    OVERRIDES.with(|overrides| {
        let overrides = overrides.borrow();
        for (index, entry) in overrides.iter().enumerate().rev() {
            if !artifact_reuse_key_is_unkeyed_control(&entry.key)
                || overrides[index + 1..]
                    .iter()
                    .any(|later| keys_equal(&later.key, &entry.key))
            {
                continue;
            }
            if entry.value.is_some() {
                return true;
            }
        }
        false
    })
}

fn artifact_reuse_environment_is_safe_fast() -> bool {
    raw_process_unkeyed_controls().is_empty() && !active_thread_override_has_unkeyed_control()
}

/// Determine whether artifact reuse is free of unkeyed Trust Codegen compiler
/// controls.
///
/// Frontends should check this at both cache lookup and cache publication
/// boundaries. Trust Codegen's production object cache also performs this
/// check internally.
///
/// The real process environment is immutable by contract and its blocker names
/// are captured once. Each call then inspects only the active thread-local
/// override stack. This makes the ordinary safe JIT-cache hit allocation-free
/// and independent of total process-environment size. A logical removal cannot
/// hide a raw process blocker because legacy compiler code has not all migrated
/// to [`var_os`] and may still read that raw value directly.
pub fn artifact_reuse_environment_safety() -> ArtifactReuseEnvironmentSafety {
    let raw_controls = raw_process_unkeyed_controls();
    let mut unkeyed_controls = active_thread_override_unkeyed_controls();
    if !raw_controls.is_empty() {
        for key in raw_controls {
            push_unkeyed_control(&mut unkeyed_controls, key.clone());
        }
        sort_unkeyed_controls(&mut unkeyed_controls);
    }
    ArtifactReuseEnvironmentSafety { unkeyed_controls }
}

/// Acquire a temporal permit for artifact-cache lookup and publication.
///
/// Callers should acquire one permit before lookup, carry it across any build
/// work, and require [`ArtifactReusePermit::is_valid`] before publishing. The
/// permit detects transient unkeyed thread-local overrides that a pair of
/// point-in-time environment snapshots would miss. `None` means lookup and
/// publication must both be bypassed.
pub fn artifact_reuse_permit() -> Option<ArtifactReusePermit> {
    let mutation_epoch = unkeyed_control_mutation_epoch()?;
    if !artifact_reuse_environment_is_safe_fast()
        || unkeyed_control_mutation_epoch() != Some(mutation_epoch)
    {
        return None;
    }
    Some(ArtifactReusePermit {
        mutation_epoch,
        _thread_bound: PhantomData,
    })
}

/// Apply the current thread's trust-cg overrides to one child command.
///
/// `Command::env` and `Command::env_remove` alter only the child environment,
/// so this is safe even when the parent process is multithreaded.
pub fn apply_to_command(command: &mut Command) {
    OVERRIDES.with(|overrides| {
        for entry in overrides.borrow().iter() {
            match &entry.value {
                Some(value) => {
                    command.env(&entry.key, value);
                }
                None => {
                    command.env_remove(&entry.key);
                }
            }
        }
    });
}

/// Owned snapshot of the current thread's explicit environment overrides.
///
/// Overrides remain thread-local by default. Compiler executors that
/// deliberately move one logical operation to a worker thread can capture this
/// value and install it there with [`Self::run`]. This transfers explicit
/// configuration without mutating the process environment or leaking it to
/// unrelated work scheduled on the same worker.
#[derive(Debug, Clone, Default)]
pub struct EnvOverrideSnapshot {
    entries: Vec<(OsString, OverrideValue)>,
}

impl EnvOverrideSnapshot {
    /// Capture the complete nested override stack on the current thread.
    pub fn capture_current_thread() -> Self {
        let entries = OVERRIDES.with(|overrides| {
            overrides
                .borrow()
                .iter()
                .map(|entry| (entry.key.clone(), entry.value.clone()))
                .collect()
        });
        Self { entries }
    }

    /// Run one operation with this snapshot installed on the current thread.
    ///
    /// Installation replaces (rather than appends to) the worker's complete
    /// override stack. This is essential on work-stealing pools: an absent key
    /// in this snapshot must mask an unrelated task's temporarily installed
    /// value. The previous worker stack is restored exactly when the operation
    /// returns or unwinds.
    pub fn run<T>(&self, operation: impl FnOnce() -> T) -> T {
        let replacement = self
            .entries
            .iter()
            .map(|(key, value)| OverrideEntry {
                id: OverrideId(Rc::new(())),
                key: key.clone(),
                value: value.clone(),
            })
            .collect::<Vec<_>>();
        let previous = OVERRIDES.with(|overrides| {
            let mut overrides = overrides.borrow_mut();
            std::mem::replace(&mut *overrides, replacement)
        });
        let touches_unkeyed_control = previous
            .iter()
            .any(|entry| artifact_reuse_key_is_unkeyed_control(&entry.key))
            || self
                .entries
                .iter()
                .any(|(key, _)| artifact_reuse_key_is_unkeyed_control(key));
        if touches_unkeyed_control {
            bump_unkeyed_control_mutation_epoch();
        }
        let restore = OverrideStackRestore {
            previous,
            touches_unkeyed_control,
        };
        let result = operation();
        drop(restore);
        result
    }
}

struct OverrideStackRestore {
    previous: Vec<OverrideEntry>,
    touches_unkeyed_control: bool,
}

impl Drop for OverrideStackRestore {
    fn drop(&mut self) {
        let previous = std::mem::take(&mut self.previous);
        OVERRIDES.with(|overrides| {
            let mut overrides = overrides.borrow_mut();
            *overrides = previous;
        });
        if self.touches_unkeyed_control {
            bump_unkeyed_control_mutation_epoch();
        }
    }
}

/// A thread-bound token that scopes guard-style overrides.
///
/// [`ScopedEnvVar`] borrows this token, which makes it impossible to drop the
/// scope before its guards. The token and guards are deliberately neither
/// `Send` nor `Sync`: thread-local overrides must be restored on their creator
/// thread.
pub struct EnvOverrideScope {
    _thread_bound: PhantomData<Rc<()>>,
}

/// Begin a guard-style override scope on the current thread.
pub fn override_scope() -> EnvOverrideScope {
    EnvOverrideScope {
        _thread_bound: PhantomData,
    }
}

/// One thread-local environment override, restored exactly on drop.
pub struct ScopedEnvVar<'scope> {
    id: OverrideId,
    _scope: PhantomData<&'scope EnvOverrideScope>,
    _thread_bound: PhantomData<Rc<()>>,
}

impl<'scope> ScopedEnvVar<'scope> {
    /// Override `key=value` for the guard's lifetime.
    pub fn set(
        _scope: &'scope EnvOverrideScope,
        key: impl AsRef<OsStr>,
        value: impl AsRef<OsStr>,
    ) -> Self {
        let id = push_override(key.as_ref(), Some(value.as_ref().to_owned()));
        Self {
            id,
            _scope: PhantomData,
            _thread_bound: PhantomData,
        }
    }

    /// Make `key` logically absent for the guard's lifetime.
    pub fn unset(_scope: &'scope EnvOverrideScope, key: impl AsRef<OsStr>) -> Self {
        let id = push_override(key.as_ref(), None);
        Self {
            id,
            _scope: PhantomData,
            _thread_bound: PhantomData,
        }
    }
}

impl Drop for ScopedEnvVar<'_> {
    fn drop(&mut self) {
        remove_override(&self.id);
    }
}

/// Run `f` with fixed thread-local values and restore prior overrides.
pub fn with_env_overrides<T>(vars: &[(&str, &str)], f: impl FnOnce() -> T) -> T {
    with_env_edits(|editor| {
        for &(key, value) in vars {
            editor.set(key, value);
        }
        f()
    })
}

/// Run `f` with keys logically absent and restore prior overrides.
pub fn with_env_overrides_removed<T>(vars: &[&str], f: impl FnOnce() -> T) -> T {
    with_env_edits(|editor| {
        for &key in vars {
            editor.remove(key);
        }
        f()
    })
}

/// A thread-local editor for sequences of environment overrides.
pub struct EnvEditor<'scope> {
    ids: Vec<OverrideId>,
    _scope: PhantomData<&'scope EnvOverrideScope>,
    _thread_bound: PhantomData<Rc<()>>,
}

impl<'scope> EnvEditor<'scope> {
    fn new(_scope: &'scope EnvOverrideScope) -> Self {
        Self {
            ids: Vec::new(),
            _scope: PhantomData,
            _thread_bound: PhantomData,
        }
    }

    /// Set a value until the next edit or the end of the editor scope.
    pub fn set(&mut self, key: impl AsRef<OsStr>, value: impl AsRef<OsStr>) {
        self.ids
            .push(push_override(key.as_ref(), Some(value.as_ref().to_owned())));
    }

    /// Make a key absent until the next edit or the end of the editor scope.
    pub fn remove(&mut self, key: impl AsRef<OsStr>) {
        self.ids.push(push_override(key.as_ref(), None));
    }
}

impl Drop for EnvEditor<'_> {
    fn drop(&mut self) {
        for id in self.ids.drain(..).rev() {
            remove_override(&id);
        }
    }
}

/// Run `f` with nested, restore-on-unwind environment overrides on the current
/// thread.
pub fn with_env_edits<T>(f: impl FnOnce(&mut EnvEditor<'_>) -> T) -> T {
    let scope = override_scope();
    let mut editor = EnvEditor::new(&scope);
    let result = f(&mut editor);
    drop(editor);
    result
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn restores_after_unwind_without_mutating_process_environment() {
        let key = "TRUST_CG_PROCESS_ENV_UNWIND";
        let process_value = std::env::var_os(key);
        let result = std::panic::catch_unwind(|| {
            with_env_overrides(&[(key, "temporary")], || {
                assert_eq!(var_os(key).as_deref(), Some(OsStr::new("temporary")));
                assert_eq!(std::env::var_os(key), process_value);
                panic!("test unwind");
            });
        });
        assert!(result.is_err());
        assert_eq!(var_os(key), process_value);
        assert_eq!(std::env::var_os(key), process_value);
    }

    #[test]
    fn duplicate_edits_restore_the_original_override() {
        let key = "TRUST_CG_PROCESS_ENV_DUPLICATE";
        let process_value = std::env::var_os(key);
        let observed = with_env_overrides(&[(key, "first"), (key, "second")], || var_os(key));
        assert_eq!(observed.as_deref(), Some(OsStr::new("second")));
        assert_eq!(var_os(key), process_value);
        assert_eq!(std::env::var_os(key), process_value);
    }

    #[test]
    fn guards_can_be_dropped_out_of_order() {
        let key = "TRUST_CG_PROCESS_ENV_OUT_OF_ORDER";
        let process_value = std::env::var_os(key);
        {
            let scope = override_scope();
            let outer = ScopedEnvVar::set(&scope, key, "outer");
            let inner = ScopedEnvVar::set(&scope, key, "inner");
            drop(outer);
            assert_eq!(var_os(key).as_deref(), Some(OsStr::new("inner")));
            drop(inner);
        }
        assert_eq!(var_os(key), process_value);
        assert_eq!(std::env::var_os(key), process_value);
    }

    #[test]
    fn logical_removal_restores_an_outer_override() {
        let key = "TRUST_CG_PROCESS_ENV_LOGICAL_REMOVAL";
        let process_value = std::env::var_os(key);
        {
            let scope = override_scope();
            let _outer = ScopedEnvVar::set(&scope, key, "outer");
            {
                let _removed = ScopedEnvVar::unset(&scope, key);
                assert_eq!(var_os(key), None);
                assert_eq!(std::env::var_os(key), process_value);
            }
            assert_eq!(var_os(key).as_deref(), Some(OsStr::new("outer")));
        }
        assert_eq!(var_os(key), process_value);
    }

    #[cfg(unix)]
    #[test]
    fn restores_non_unicode_override_exactly() {
        use std::os::unix::ffi::OsStringExt;

        let key = "TRUST_CG_PROCESS_ENV_NON_UNICODE";
        let process_value = std::env::var_os(key);
        let non_unicode = OsString::from_vec(vec![b'a', 0x80, b'z']);
        {
            let scope = override_scope();
            let _baseline = ScopedEnvVar::set(&scope, key, &non_unicode);
            {
                let _temporary = ScopedEnvVar::set(&scope, key, "temporary");
                assert_eq!(var_os(key).as_deref(), Some(OsStr::new("temporary")));
            }
            assert_eq!(var_os(key).as_deref(), Some(non_unicode.as_os_str()));
        }
        assert_eq!(var_os(key), process_value);
        assert_eq!(std::env::var_os(key), process_value);
    }

    #[test]
    fn overrides_are_isolated_between_threads() {
        let key = "TRUST_CG_PROCESS_ENV_THREAD_ISOLATION";
        let process_value = std::env::var_os(key);
        let barrier = std::sync::Barrier::new(2);
        std::thread::scope(|threads| {
            threads.spawn(|| {
                with_env_overrides(&[(key, "left")], || {
                    barrier.wait();
                    assert_eq!(var_os(key).as_deref(), Some(OsStr::new("left")));
                    barrier.wait();
                });
            });
            threads.spawn(|| {
                barrier.wait();
                assert_eq!(var_os(key), process_value);
                with_env_overrides(&[(key, "right")], || {
                    assert_eq!(var_os(key).as_deref(), Some(OsStr::new("right")));
                });
                barrier.wait();
            });
        });
        assert_eq!(var_os(key), process_value);
        assert_eq!(std::env::var_os(key), process_value);
    }

    #[test]
    fn explicit_snapshot_transfers_overrides_to_one_worker_scope() {
        let set_key = "TRUST_CG_PROCESS_ENV_SNAPSHOT_SET";
        let removed_key = "TRUST_CG_PROCESS_ENV_SNAPSHOT_REMOVED";
        let process_set = std::env::var_os(set_key);
        let process_removed = std::env::var_os(removed_key);

        let observed = with_env_edits(|editor| {
            editor.set(set_key, "captured");
            editor.remove(removed_key);
            let snapshot = EnvOverrideSnapshot::capture_current_thread();
            let worker_process_set = process_set.clone();
            let worker_process_removed = process_removed.clone();
            std::thread::spawn(move || {
                assert_eq!(var_os(set_key), worker_process_set);
                assert_eq!(var_os(removed_key), worker_process_removed);
                let inside = snapshot.run(|| (var_os(set_key), var_os(removed_key)));
                let restored = (var_os(set_key), var_os(removed_key));
                (inside, restored)
            })
            .join()
            .unwrap()
        });

        assert_eq!(observed.0.0.as_deref(), Some(OsStr::new("captured")));
        assert_eq!(observed.0.1, None);
        assert_eq!(observed.1, (process_set, process_removed));
    }

    #[test]
    fn snapshot_masks_worker_only_overrides_and_restores_them() {
        let captured_key = "TCG_PROCESS_ENV_SNAPSHOT_CAPTURED";
        let worker_only_key = "TCG_PROCESS_ENV_SNAPSHOT_WORKER_ONLY";
        let snapshot = with_env_overrides(&[(captured_key, "captured")], || {
            EnvOverrideSnapshot::capture_current_thread()
        });

        with_env_overrides(&[(worker_only_key, "worker")], || {
            snapshot.run(|| {
                assert_eq!(var(captured_key).as_deref(), Ok("captured"));
                assert_eq!(var_os(worker_only_key), None);
            });
            assert_eq!(var(worker_only_key).as_deref(), Ok("worker"));
            assert_eq!(var_os(captured_key), None);
        });
    }

    #[test]
    fn command_receives_set_and_removed_overrides() {
        with_env_edits(|editor| {
            editor.set("TRUST_CG_PROCESS_ENV_CHILD_SET", "value");
            editor.remove("TRUST_CG_PROCESS_ENV_CHILD_REMOVED");
            let mut command = Command::new("unused");
            command.env("TRUST_CG_PROCESS_ENV_CHILD_SET", "stale");
            command.env("TRUST_CG_PROCESS_ENV_CHILD_REMOVED", "stale");
            apply_to_command(&mut command);
            let edits = command
                .get_envs()
                .map(|(key, value)| (key.to_owned(), value.map(OsStr::to_owned)))
                .collect::<Vec<_>>();
            assert!(edits.contains(&(
                OsString::from("TRUST_CG_PROCESS_ENV_CHILD_SET"),
                Some(OsString::from("value")),
            )));
            assert!(edits.contains(&(OsString::from("TRUST_CG_PROCESS_ENV_CHILD_REMOVED"), None,)));

            let snapshot = vars_os().collect::<Vec<_>>();
            assert!(snapshot.contains(&(
                OsString::from("TRUST_CG_PROCESS_ENV_CHILD_SET"),
                OsString::from("value"),
            )));
            assert!(!snapshot.iter().any(|(key, _)| {
                key.as_os_str() == OsStr::new("TRUST_CG_PROCESS_ENV_CHILD_REMOVED")
            }));
        });
    }

    fn sanitized_entry<'a>(environment: &'a SanitizedChildEnv, key: &str) -> Option<&'a OsStr> {
        environment
            .entries
            .iter()
            .find(|(candidate, _)| keys_equal(candidate, OsStr::new(key)))
            .map(|(_, value)| value.as_os_str())
    }

    #[test]
    fn sanitized_verifier_environment_is_sorted_and_deterministic() {
        let first = SanitizedChildEnv::capture_verifier();
        let second = SanitizedChildEnv::capture_verifier();

        assert_eq!(first, second);
        assert_eq!(first.digest(), second.digest());
        assert!(
            first.entries.windows(2).all(|entries| {
                entries[0].0.as_encoded_bytes() < entries[1].0.as_encoded_bytes()
            })
        );
        assert_eq!(sanitized_entry(&first, "LANG"), Some(OsStr::new("C")));
        assert_eq!(sanitized_entry(&first, "LC_ALL"), Some(OsStr::new("C")));
        #[cfg(unix)]
        assert_eq!(
            sanitized_entry(&first, "PATH"),
            Some(OsStr::new("/usr/bin:/bin"))
        );
    }

    #[test]
    fn sanitized_verifier_environment_honors_scoped_allowlisted_overrides() {
        with_env_edits(|editor| {
            editor.set("TMPDIR", "scoped-verifier-temp");
            editor.set("RUST_MIN_STACK", "8388608");
            editor.set("LANG", "ambient-locale-must-not-win");
            let environment = SanitizedChildEnv::capture_verifier();

            assert_eq!(
                sanitized_entry(&environment, "TMPDIR"),
                Some(OsStr::new("scoped-verifier-temp"))
            );
            assert_eq!(
                sanitized_entry(&environment, "RUST_MIN_STACK"),
                Some(OsStr::new("8388608"))
            );
            assert_eq!(sanitized_entry(&environment, "LANG"), Some(OsStr::new("C")));
        });
    }

    #[test]
    fn sanitized_verifier_environment_excludes_unrelated_and_authority_knobs() {
        with_env_edits(|editor| {
            for key in [
                "AY_SOLVER_PATH",
                "HOME",
                "LD_LIBRARY_PATH",
                "TCG_FUTURE_ALGORITHM_KNOB",
                "TRUST_ROOT",
                "XDG_CACHE_HOME",
            ] {
                editor.set(key, "must-not-be-inherited");
            }
            let environment = SanitizedChildEnv::capture_verifier();

            for key in [
                "AY_SOLVER_PATH",
                "HOME",
                "LD_LIBRARY_PATH",
                "TCG_FUTURE_ALGORITHM_KNOB",
                "TRUST_ROOT",
                "XDG_CACHE_HOME",
            ] {
                assert_eq!(sanitized_entry(&environment, key), None, "key={key}");
            }
        });
    }

    #[test]
    fn sanitized_verifier_environment_apply_clears_prior_command_environment() {
        let environment = SanitizedChildEnv::capture_verifier();
        let mut command = Command::new("unused");
        command.env("SANITIZED_CHILD_ENV_MUST_BE_CLEARED", "inherited");
        environment.apply_to_command(&mut command);

        let mut applied = command
            .get_envs()
            .map(|(key, value)| {
                (
                    key.to_owned(),
                    value
                        .expect("the sanitized snapshot contains no removals")
                        .to_owned(),
                )
            })
            .collect::<Vec<_>>();
        applied.sort_by(|left, right| left.0.as_encoded_bytes().cmp(right.0.as_encoded_bytes()));

        assert_eq!(applied, environment.entries);
        assert_eq!(
            command.get_current_dir(),
            environment.working_dir.as_deref()
        );
        assert_eq!(
            sanitized_entry(&environment, "SANITIZED_CHILD_ENV_MUST_BE_CLEARED"),
            None
        );
    }

    #[cfg(unix)]
    #[test]
    fn executable_resolution_skips_non_executable_path_entries() {
        use std::os::unix::fs::PermissionsExt;

        let root = std::env::temp_dir().join(format!(
            "trust-cg-process-env-resolve-{}-{:?}",
            std::process::id(),
            std::thread::current().id()
        ));
        let shadow_dir = root.join("shadow");
        let executable_dir = root.join("executable");
        std::fs::create_dir_all(&shadow_dir).expect("create shadow directory");
        std::fs::create_dir_all(&executable_dir).expect("create executable directory");
        let shadow = shadow_dir.join("ay");
        let executable = executable_dir.join("ay");
        std::fs::write(&shadow, b"shadow").expect("write shadow fixture");
        std::fs::write(&executable, b"executable").expect("write executable fixture");
        std::fs::set_permissions(&shadow, std::fs::Permissions::from_mode(0o644))
            .expect("make shadow non-executable");
        std::fs::set_permissions(&executable, std::fs::Permissions::from_mode(0o755))
            .expect("make fixture executable");
        let path = std::env::join_paths([shadow_dir, executable_dir]).expect("join fixture PATH");

        let resolved = with_env_edits(|environment| {
            environment.set("PATH", &path);
            resolve_executable_path(OsStr::new("ay"))
        });
        assert_eq!(resolved.as_deref(), Some(executable.as_path()));

        let _ = std::fs::remove_dir_all(root);
    }

    #[test]
    fn sanitized_verifier_environment_digest_binds_allowlisted_values() {
        let first = with_env_overrides(&[("TMPDIR", "verifier-temp-a")], || {
            SanitizedChildEnv::capture_verifier()
        });
        let second = with_env_overrides(&[("TMPDIR", "verifier-temp-b")], || {
            SanitizedChildEnv::capture_verifier()
        });

        assert_ne!(first, second);
        assert_ne!(first.digest(), second.digest());
    }

    // Captured-path controls construct snapshots directly; they never mutate
    // the process-global CWD shared with other test threads.
    fn captured_path_environment(working_dir: Option<PathBuf>) -> SanitizedChildEnv {
        let mut snapshot = SanitizedChildEnv::capture_verifier();
        snapshot.working_dir = working_dir;
        snapshot.digest =
            sanitized_child_env_digest(&snapshot.entries, snapshot.working_dir.as_deref());
        snapshot
    }

    #[test]
    fn captured_path_anchor_preserves_spelling_and_incomplete_snapshot() {
        let current = std::env::current_dir().unwrap();
        let captured = current.join("captured-path-diagnostic-only");
        let snapshot = captured_path_environment(Some(captured.clone()));
        let relative = Path::new("tools/../bin/checker");
        let absolute = current.join("absolute-checker");
        assert_eq!(snapshot.working_dir(), Some(captured.as_path()));
        assert_eq!(
            snapshot.anchor_path(relative),
            Some(captured.join(relative))
        );
        assert_eq!(snapshot.anchor_path(&absolute), Some(absolute.clone()));
        let mut command = Command::new("not-executed");
        snapshot.apply_to_command(&mut command);
        assert_eq!(command.get_current_dir(), Some(captured.as_path()));

        let incomplete = captured_path_environment(None);
        assert_ne!(snapshot.digest(), incomplete.digest());
        assert!(incomplete.working_dir().is_none());
        assert!(incomplete.anchor_path(relative).is_none());
        assert_eq!(incomplete.anchor_path(&absolute), Some(absolute));
        let mut command = Command::new("not-executed");
        incomplete.apply_to_command(&mut command);
        assert!(command.get_current_dir().is_none());
        assert!(incomplete.working_dir().is_none());
        assert_eq!(std::env::current_dir().unwrap(), current);
    }

    #[cfg(unix)]
    struct CapturedPathTestDirectory(PathBuf);

    #[cfg(unix)]
    impl CapturedPathTestDirectory {
        fn new() -> Self {
            use std::sync::atomic::{AtomicU64, Ordering};
            static NONCE: AtomicU64 = AtomicU64::new(0);
            let root = std::env::temp_dir().join(format!(
                "trust-cg-captured-path-{}-{}-{}",
                std::process::id(),
                std::time::SystemTime::now()
                    .duration_since(std::time::UNIX_EPOCH)
                    .unwrap()
                    .as_nanos(),
                NONCE.fetch_add(1, Ordering::Relaxed),
            ));
            std::fs::create_dir(&root).unwrap();
            Self(root)
        }

        fn executable(&self, relative: &str) -> PathBuf {
            use std::os::unix::fs::PermissionsExt;
            let path = self.0.join(relative);
            std::fs::create_dir_all(path.parent().unwrap()).unwrap();
            std::fs::write(&path, b"#!/bin/sh\nexit 0\n").unwrap();
            std::fs::set_permissions(&path, std::fs::Permissions::from_mode(0o755)).unwrap();
            path
        }
    }

    #[cfg(unix)]
    impl Drop for CapturedPathTestDirectory {
        fn drop(&mut self) {
            let _ = std::fs::remove_dir_all(&self.0);
        }
    }

    #[cfg(unix)]
    #[test]
    fn captured_path_resolver_uses_supplied_cwd_for_command_and_path_entries() {
        let current = std::env::current_dir().unwrap();
        let root = CapturedPathTestDirectory::new();
        let a = root.executable("a/bin/checker");
        let b = root.executable("b/bin/checker");
        let a_root = root.0.join("a");
        let b_root = root.0.join("b");
        let snapshot_a = captured_path_environment(Some(a_root.clone()));
        let snapshot_b = captured_path_environment(Some(b_root.clone()));
        assert_ne!(snapshot_a.digest(), snapshot_b.digest());
        assert_eq!(
            resolve_executable_path_with_environment(OsStr::new("bin/checker"), &snapshot_a),
            Some(a.clone())
        );
        let discovery_path =
            std::env::join_paths([PathBuf::from("bin"), b_root.join("bin")]).unwrap();
        with_env_edits(|editor| {
            editor.set("PATH", &discovery_path);
            assert_eq!(
                resolve_executable_path_with_environment(OsStr::new("checker"), &snapshot_a),
                Some(a.clone())
            );
            assert_eq!(
                resolve_executable_path_with_environment(OsStr::new("checker"), &snapshot_b),
                Some(b)
            );
        });
        // The selected symlink spelling, not its canonical target, is retained.
        let link = a_root.join("checker-link");
        std::os::unix::fs::symlink(&a, &link).unwrap();
        assert_eq!(
            resolve_executable_path_with_environment(OsStr::new("./checker-link"), &snapshot_a),
            Some(a_root.join("./checker-link"))
        );
        let current_entry = root.executable("a/checker");
        with_env_overrides(&[("PATH", "")], || {
            assert_eq!(
                resolve_executable_path_with_environment(OsStr::new("checker"), &snapshot_a),
                Some(current_entry)
            );
        });
        assert_eq!(std::env::current_dir().unwrap(), current);
    }

    #[cfg(unix)]
    #[test]
    fn captured_path_resolver_incomplete_cwd_skips_relative_but_keeps_absolute_candidates() {
        let current = std::env::current_dir().unwrap();
        let root = CapturedPathTestDirectory::new();
        let absolute = root.executable("absolute/checker");
        let incomplete = captured_path_environment(None);
        let digest = incomplete.digest();
        assert!(
            resolve_executable_path_with_environment(OsStr::new("relative/checker"), &incomplete)
                .is_none()
        );
        with_env_overrides(&[("PATH", "relative-bin")], || {
            assert!(
                resolve_executable_path_with_environment(OsStr::new("checker"), &incomplete)
                    .is_none()
            );
        });
        let mixed = std::env::join_paths([
            PathBuf::from("relative-bin"),
            PathBuf::new(),
            root.0.join("absolute"),
        ])
        .unwrap();
        with_env_edits(|editor| {
            editor.set("PATH", mixed);
            assert_eq!(
                resolve_executable_path_with_environment(OsStr::new("checker"), &incomplete),
                Some(absolute.clone())
            );
        });
        assert_eq!(
            resolve_executable_path_with_environment(absolute.as_os_str(), &incomplete),
            Some(absolute)
        );
        // Finding an absolute executable never upgrades an incomplete snapshot.
        assert!(incomplete.working_dir().is_none());
        assert_eq!(incomplete.digest(), digest);
        assert_eq!(std::env::current_dir().unwrap(), current);
    }

    #[cfg(unix)]
    #[test]
    fn sanitized_verifier_environment_hashes_non_unicode_without_loss() {
        use std::os::unix::ffi::OsStringExt;

        let first_value = OsString::from_vec(vec![b't', b'm', b'p', 0x80]);
        let second_value = OsString::from_vec(vec![b't', b'm', b'p', 0x81]);
        let unrelated_key = OsString::from_vec(b"TCG_UNRELATED_\xff".to_vec());
        let first = with_env_edits(|editor| {
            editor.set("TMPDIR", &first_value);
            editor.set(&unrelated_key, "excluded");
            SanitizedChildEnv::capture_verifier()
        });
        let second = with_env_edits(|editor| {
            editor.set("TMPDIR", &second_value);
            SanitizedChildEnv::capture_verifier()
        });

        assert_eq!(
            sanitized_entry(&first, "TMPDIR"),
            Some(first_value.as_os_str())
        );
        assert!(
            !first
                .entries
                .iter()
                .any(|(key, _)| key.as_os_str() == unrelated_key.as_os_str())
        );
        assert_ne!(first.digest(), second.digest());
    }

    #[cfg(windows)]
    #[test]
    fn sanitized_verifier_environment_hashes_unpaired_wide_units_without_loss() {
        use std::os::windows::ffi::OsStringExt;

        let first_value = OsString::from_wide(&[b't' as u16, 0xd800]);
        let second_value = OsString::from_wide(&[b't' as u16, 0xd801]);
        let unrelated_key =
            OsString::from_wide(&[b'T' as u16, b'C' as u16, b'G' as u16, b'_' as u16, 0xd800]);
        let first = with_env_edits(|editor| {
            editor.set("TMPDIR", &first_value);
            editor.set(&unrelated_key, "excluded");
            SanitizedChildEnv::capture_verifier()
        });
        let second = with_env_edits(|editor| {
            editor.set("TMPDIR", &second_value);
            SanitizedChildEnv::capture_verifier()
        });

        assert_eq!(
            sanitized_entry(&first, "TMPDIR"),
            Some(first_value.as_os_str())
        );
        assert!(
            !first
                .entries
                .iter()
                .any(|(key, _)| key.as_os_str() == unrelated_key.as_os_str())
        );
        assert_ne!(first.digest(), second.digest());
    }

    #[test]
    fn artifact_reuse_environment_fails_closed_for_unknown_controls() {
        let safety = artifact_reuse_environment_safety_from([
            (OsString::from("PATH"), OsString::from("/bin")),
            (OsString::from("TCG_Z_FUTURE_OPTION"), OsString::new()),
            (
                OsString::from("TRUST_CG_DISABLE_PASSES"),
                OsString::from("licm"),
            ),
            (OsString::from("TCG_A_OPTION"), OsString::from("0")),
            (OsString::from("TCG_A_OPTION"), OsString::from("1")),
            (
                OsString::from("TCG_ARTIFACT_CACHE_DIR_FUTURE"),
                OsString::from("/cache"),
            ),
            (
                OsString::from("TRUST_CG_COMPILE_ARTIFACT_FUTURE_IDENTITY"),
                OsString::from("future"),
            ),
        ]);

        assert!(!safety.is_reuse_safe());
        assert_eq!(
            safety.unkeyed_controls(),
            [
                OsString::from("TCG_ARTIFACT_CACHE_DIR_FUTURE"),
                OsString::from("TCG_A_OPTION"),
                OsString::from("TCG_Z_FUTURE_OPTION"),
                OsString::from("TRUST_CG_COMPILE_ARTIFACT_FUTURE_IDENTITY"),
                OsString::from("TRUST_CG_DISABLE_PASSES"),
            ]
        );
    }

    #[cfg(unix)]
    #[test]
    fn artifact_reuse_environment_fails_closed_for_non_unicode_control_name() {
        use std::os::unix::ffi::OsStringExt;

        let key = OsString::from_vec(b"TCG_\xff_FUTURE_OPTION".to_vec());
        let safety =
            artifact_reuse_environment_safety_from([(key.clone(), OsString::from("configured"))]);

        assert!(!safety.is_reuse_safe());
        assert_eq!(safety.unkeyed_controls(), [key]);
    }

    #[test]
    fn artifact_reuse_environment_exempts_only_transport_and_keyed_identity() {
        let variables = ARTIFACT_REUSE_ENV_EXEMPT_KEYS
            .iter()
            .map(|key| (OsString::from(key), OsString::from("configured")))
            .chain([(OsString::from("UNRELATED_APP_OPTION"), OsString::from("1"))]);
        let safety = artifact_reuse_environment_safety_from(variables);

        assert!(safety.is_reuse_safe(), "{safety:?}");
        assert!(safety.unkeyed_controls().is_empty());
    }

    #[test]
    fn max_parallelism_remains_unkeyed_until_search_consumers_are_bound() {
        let safety = artifact_reuse_environment_safety_from([(
            OsString::from(resource_budget::TRUST_CG_MAX_PARALLELISM_ENV),
            OsString::from("2"),
        )]);

        assert!(!safety.is_reuse_safe());
        assert_eq!(
            safety.unkeyed_controls(),
            [OsString::from(
                resource_budget::TRUST_CG_MAX_PARALLELISM_ENV
            )]
        );
    }

    #[test]
    fn artifact_reuse_environment_honors_thread_local_overrides() {
        let key = "TCG_PROCESS_ENV_CACHE_SAFETY_FUTURE_OPTION";
        with_env_overrides(&[(key, "")], || {
            let safety = artifact_reuse_environment_safety();
            assert!(
                safety
                    .unkeyed_controls()
                    .iter()
                    .any(|control| control == OsStr::new(key)),
                "{safety:?}"
            );
        });
    }

    #[test]
    fn artifact_reuse_environment_uses_latest_thread_override_edit() {
        let key = "TCG_PROCESS_ENV_CACHE_SAFETY_NESTED_OPTION";
        let scope = override_scope();
        let present = ScopedEnvVar::set(&scope, key, "1");
        assert!(
            artifact_reuse_environment_safety()
                .unkeyed_controls()
                .iter()
                .any(|control| control == OsStr::new(key))
        );

        let removed = ScopedEnvVar::unset(&scope, key);
        assert!(
            !artifact_reuse_environment_safety()
                .unkeyed_controls()
                .iter()
                .any(|control| control == OsStr::new(key)),
            "the latest logical removal must hide an outer thread override"
        );

        drop(removed);
        assert!(
            artifact_reuse_environment_safety()
                .unkeyed_controls()
                .iter()
                .any(|control| control == OsStr::new(key)),
            "dropping the removal must restore the outer override"
        );
        drop(present);
    }

    #[test]
    fn artifact_reuse_permit_detects_a_transient_unkeyed_override() {
        let permit = artifact_reuse_permit().expect("default environment should issue a permit");
        assert!(permit.is_valid());

        with_env_overrides(&[("TCG_PROCESS_ENV_TRANSIENT_BUILD_OPTION", "1")], || {
            assert!(
                !permit.is_valid(),
                "an active override must invalidate reuse"
            );
        });

        assert!(
            artifact_reuse_environment_safety().is_reuse_safe(),
            "the effective environment should be safe again after the scope"
        );
        assert!(
            !permit.is_valid(),
            "ending a transient override must not revalidate an old permit"
        );
        assert!(
            artifact_reuse_permit()
                .expect("a new permit should be available")
                .is_valid(),
            "a caller may begin a new cache transaction after the mutation"
        );
    }

    #[test]
    fn artifact_reuse_permit_ignores_exact_transport_exemptions() {
        let permit = artifact_reuse_permit().expect("default environment should issue a permit");
        with_env_overrides(&[("TRUST_CG_JIT_DISK_CACHE", "0")], || {
            assert!(permit.is_valid());
        });
        assert!(permit.is_valid());
    }
}
