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

use std::cell::{Cell, RefCell};
use std::env::VarError;
use std::ffi::{OsStr, OsString};
use std::marker::PhantomData;
use std::process::Command;
use std::rc::Rc;
use std::sync::OnceLock;

pub mod resource_budget;

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
