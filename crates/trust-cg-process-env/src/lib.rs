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

use std::cell::RefCell;
use std::env::VarError;
use std::ffi::{OsStr, OsString};
use std::marker::PhantomData;
use std::process::Command;
use std::rc::Rc;

/// `Some(value)` overrides a key; `None` makes it logically absent.
type OverrideValue = Option<OsString>;

thread_local! {
    static OVERRIDES: RefCell<Vec<OverrideEntry>> = const { RefCell::new(Vec::new()) };
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
    OVERRIDES.with(|overrides| {
        let mut overrides = overrides.borrow_mut();
        let id = OverrideId(Rc::new(()));
        overrides.push(OverrideEntry {
            id: id.clone(),
            key: key.to_owned(),
            value,
        });
        id
    })
}

fn remove_override(id: &OverrideId) {
    OVERRIDES.with(|overrides| {
        let mut overrides = overrides.borrow_mut();
        if let Some(index) = overrides
            .iter()
            .position(|entry| Rc::ptr_eq(&entry.id.0, &id.0))
        {
            overrides.remove(index);
        }
    });
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
}
