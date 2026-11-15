// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Owner-private directories and files for Trust Codegen's caches.
//!
//! Every directory Trust Codegen creates under the user cache (`$XDG_CACHE_HOME`
//! or `$HOME/.cache`), the cache base and the shared `trust-cg` root included,
//! is created by [`create_private_dir_all`], so the creation rule is written
//! once.
//!
//! # Why
//!
//! `std::fs::create_dir_all` creates with mode `0777 & !umask`. Under umask
//! `0002`, Ubuntu's default for a user with a user-private group, that is
//! `0775`: group-writable. The private copy AY is started from
//! (`trust-cg-verify` `ay_private_copy`) refuses an ancestor directory that
//! anyone else may rename entries in, so one cache directory created that way
//! (measured 2026-09-26: `<cache>/trust-cg` at `0775`) refused AY in every
//! later process on that host.
//!
//! # The rule
//!
//! * Every directory this module CREATES has mode exactly `0700` on Unix,
//!   whatever the umask. `mkdir(2)` can only clear bits of the requested
//!   `0700`, and Linux adds the set-group-ID bit under a set-group-ID parent;
//!   when either happens, the new directory's mode is set to `0700` by name
//!   without following a symlink. If that fails (glibc before 2.32 refuses
//!   `fchmodat` with `AT_SYMLINK_NOFOLLOW`), the call fails and removes the
//!   directory it made, rather than leave one a later call would accept.
//! * A directory that already exists is never changed, whatever its mode.
//!   Judging it is the caller's business (for AY, `check_ancestors`), and
//!   opening one that is too permissive is its owner's decision
//!   (`chmod go-w <dir>`).
//! * Files are created exclusively (`O_EXCL`) with mode exactly `0600`.
//!
//! # Where the user cache is
//!
//! Every trust-cg cache root under the user cache (AY's private copy, the
//! solver-identity memo, the Alethe certificate store, the CEGIS cache, the
//! JIT caches) resolves its base by [`user_cache_base`], one rule:
//! `$XDG_CACHE_HOME` when it is an absolute path, else `$HOME/.cache` when
//! `HOME` is absolute, else no cache. An empty or relative `XDG_CACHE_HOME`
//! is ignored, as the XDG Base Directory specification requires. No base
//! depends on the working directory, so every reader in every directory
//! resolves the same one: a reader that anchored a relative value to its
//! working directory copied AY below a group-writable checkout and was
//! refused there, while `--print-ay-identity`, the Linux floor's preflight
//! and the refusal note, which read `$HOME/.cache`, reported AY admitted
//! (X-HOST-P13 second audit, 2026-10-03). `scripts/private_cache.py`
//! `user_cache_base` is the same rule, with the same refusal text, for the
//! repository's scripts.

use std::ffi::OsStr;
use std::fs::File;
use std::io;
use std::path::{Path, PathBuf};

/// The user cache base (see the module documentation): `$XDG_CACHE_HOME`
/// when `xdg_cache_home` is an absolute path, else `<home>/.cache` when
/// `home` is absolute. An empty or relative `xdg_cache_home` is ignored; with
/// no absolute base the `Err` names the variables. Pure: callers pass the
/// values of whichever environment they read.
pub fn user_cache_base(
    xdg_cache_home: Option<&OsStr>,
    home: Option<&OsStr>,
) -> Result<PathBuf, String> {
    if let Some(xdg) = xdg_cache_home
        .map(Path::new)
        .filter(|path| path.is_absolute())
    {
        return Ok(xdg.to_path_buf());
    }
    match home.map(Path::new) {
        Some(home) if home.is_absolute() => Ok(home.join(".cache")),
        Some(home) => Err(format!(
            "HOME={} is not absolute and XDG_CACHE_HOME names no absolute directory",
            home.display()
        )),
        None => Err("neither XDG_CACHE_HOME nor HOME names an absolute directory".to_owned()),
    }
}

/// [`user_cache_base`] of this process's environment as the current request
/// scope sees it ([`crate::var_os`]).
pub fn current_user_cache_base() -> Result<PathBuf, String> {
    user_cache_base(
        crate::var_os("XDG_CACHE_HOME").as_deref(),
        crate::var_os("HOME").as_deref(),
    )
}

/// Mode of every directory [`create_private_dir_all`] creates (Unix).
pub const PRIVATE_DIRECTORY_MODE: u32 = 0o700;

/// Mode of every file [`create_private_file`] creates (Unix).
pub const PRIVATE_FILE_MODE: u32 = 0o600;

/// Create `path` and every missing ancestor. Each directory this call creates
/// has mode exactly [`PRIVATE_DIRECTORY_MODE`] on Unix, whatever the umask,
/// or the call fails (and removes it); every directory that already exists
/// (a symlink to one included, as with `std::fs::create_dir_all`) is left
/// exactly as it is.
pub fn create_private_dir_all(path: &Path) -> io::Result<()> {
    create_private_dir_all_reporting(path).map(|_| ())
}

/// [`create_private_dir_all`], answering whether THIS call created `path`
/// itself (`true`) or found a directory there (`false`). A caller that just
/// created a store directory knows it holds nothing yet, so it can skip work
/// an existing directory needs (e.g. a cache's first cap sweep). The answer
/// is exact for this call's own `mkdir`; a directory a concurrent creator
/// made first reads `false`.
pub fn create_private_dir_all_reporting(path: &Path) -> io::Result<bool> {
    if path.as_os_str().is_empty() {
        return Ok(false);
    }
    // The same walk as `std::fs::DirBuilder::create` with `recursive(true)`,
    // so a directory another creator made first is not an error, but each
    // directory is made by `create_private_dir`. Only a failed `mkdir` may
    // find a directory there already; a directory THIS call created and could
    // not make private is always an error.
    match create_private_dir(path) {
        Ok(()) => return Ok(true),
        Err(Creation::Mkdir(error)) if error.kind() == io::ErrorKind::NotFound => {}
        Err(Creation::Mkdir(_)) if path.is_dir() => return Ok(false),
        Err(Creation::Mkdir(error) | Creation::Settle(error)) => return Err(error),
    }
    match path.parent() {
        Some(parent) => create_private_dir_all(parent)?,
        None => return Err(io::Error::other("failed to create whole tree")),
    }
    match create_private_dir(path) {
        Ok(()) => Ok(true),
        Err(Creation::Mkdir(_)) if path.is_dir() => Ok(false),
        Err(Creation::Mkdir(error) | Creation::Settle(error)) => Err(error),
    }
}

/// Why [`create_private_dir`] failed: `mkdir` itself (the directory may exist
/// already), or the directory it just created could not be made private.
enum Creation {
    Mkdir(io::Error),
    Settle(io::Error),
}

/// Create the one directory `path` (its parent must exist), mode exactly
/// [`PRIVATE_DIRECTORY_MODE`] on Unix. An existing `path` is a `mkdir`
/// error. A directory it creates but cannot make private is removed again
/// (best effort, so no retry mistakes it for one that already existed).
fn create_private_dir(path: &Path) -> Result<(), Creation> {
    let mut builder = std::fs::DirBuilder::new();
    #[cfg(unix)]
    {
        use std::os::unix::fs::DirBuilderExt;
        builder.mode(PRIVATE_DIRECTORY_MODE);
    }
    builder.create(path).map_err(Creation::Mkdir)?;
    #[cfg(unix)]
    if let Err(error) = settle_new_directory_mode(path) {
        let _ = std::fs::remove_dir(path);
        return Err(Creation::Settle(error));
    }
    Ok(())
}

/// Make the directory this process just created exactly
/// [`PRIVATE_DIRECTORY_MODE`]. Under a umask that leaves the owner bits alone
/// (`0002`, `0022`, `0077`, ...) and a parent without the set-group-ID bit,
/// `mkdir` already produced it and nothing is changed.
#[cfg(unix)]
fn settle_new_directory_mode(path: &Path) -> io::Result<()> {
    use std::os::unix::ffi::OsStrExt;
    use std::os::unix::fs::MetadataExt;

    let private = |metadata: &std::fs::Metadata| {
        metadata.file_type().is_dir() && metadata.mode() & 0o7777 == PRIVATE_DIRECTORY_MODE
    };
    let metadata = std::fs::symlink_metadata(path)?;
    if private(&metadata) {
        return Ok(());
    }
    let name = std::ffi::CString::new(path.as_os_str().as_bytes())
        .map_err(|_| io::Error::new(io::ErrorKind::InvalidInput, "path contains a NUL byte"))?;
    // By name, never through a symlink: had the new entry been replaced by a
    // symlink, this changes nothing and fails. (`0o700` fits Darwin's `u16`
    // `mode_t`.)
    let mode = PRIVATE_DIRECTORY_MODE as libc::mode_t;
    // SAFETY: `name` is a NUL-terminated path that outlives the call, and
    // `fchmodat` reads nothing else from this process's memory.
    let status = unsafe {
        libc::fchmodat(
            libc::AT_FDCWD,
            name.as_ptr(),
            mode,
            libc::AT_SYMLINK_NOFOLLOW,
        )
    };
    let failure = (status != 0).then(io::Error::last_os_error);
    // Stands in for glibc < 2.32, whose `fchmodat` refuses
    // `AT_SYMLINK_NOFOLLOW` with ENOTSUP.
    #[cfg(test)]
    let failure = if tests::SETTLE_FAILS.with(std::cell::Cell::get) {
        Some(io::Error::from_raw_os_error(libc::ENOTSUP))
    } else {
        failure
    };
    let failure = match failure {
        None if !private(&std::fs::symlink_metadata(path)?) => Some(io::Error::other(
            "its mode is still not private after the change",
        )),
        failure => failure,
    };
    if let Some(error) = failure {
        return Err(io::Error::new(
            error.kind(),
            format!(
                "created {} with mode {:04o} and cannot make it {PRIVATE_DIRECTORY_MODE:04o}: {error}",
                path.display(),
                metadata.mode() & 0o7777
            ),
        ));
    }
    Ok(())
}

/// Create the file `path`, which must not exist yet (`O_EXCL`, so an existing
/// file or symlink there fails the call), with mode exactly
/// [`PRIVATE_FILE_MODE`] on Unix whatever the umask, and open it for writing.
pub fn create_private_file(path: &Path) -> io::Result<File> {
    let mut options = std::fs::OpenOptions::new();
    options.write(true).create_new(true);
    #[cfg(unix)]
    {
        use std::os::unix::fs::OpenOptionsExt;
        options.mode(PRIVATE_FILE_MODE);
    }
    let file = options.open(path)?;
    #[cfg(unix)]
    {
        use std::os::unix::fs::{MetadataExt, PermissionsExt};
        // Through the descriptor this call created, so nothing else is changed.
        if file.metadata()?.mode() & 0o7777 != PRIVATE_FILE_MODE {
            file.set_permissions(std::fs::Permissions::from_mode(PRIVATE_FILE_MODE))?;
        }
    }
    Ok(file)
}

/// Publish the complete file `from` under the name `to`, only if `to` does
/// not exist yet: atomically, the whole file appears at `to` or nothing does,
/// and an existing `to` is never replaced. On every `Ok` return `from` no
/// longer exists (it was renamed, or removed after losing to an existing
/// `to`); on `Err` it may remain and the caller removes it.
///
/// `Ok(true)`: published. `Ok(false)`: `to` already existed.
///
/// macOS `renamex_np(RENAME_EXCL)` and Linux `renameat2(RENAME_NOREPLACE)`
/// publish with one rename; where neither exists, or the file system refuses
/// the flag, a hard link (the portable no-clobber publish) followed by the
/// removal of `from`. The rename is much cheaper: measured on APFS
/// (2026-09-28, M5 Max, instructions retired incl. kernel) `link` 3.7 M vs
/// `renamex_np(RENAME_EXCL)` 0.65 M.
pub fn publish_no_clobber(from: &Path, to: &Path) -> io::Result<bool> {
    match rename_no_clobber(from, to) {
        Ok(()) => return Ok(true),
        Err(error) if error.kind() == io::ErrorKind::AlreadyExists => {
            let _ = std::fs::remove_file(from);
            return Ok(false);
        }
        Err(error) if !rename_flag_unsupported(&error) => return Err(error),
        Err(_) => {}
    }
    let published = match std::fs::hard_link(from, to) {
        Ok(()) => true,
        Err(error) if error.kind() == io::ErrorKind::AlreadyExists => false,
        Err(error) => return Err(error),
    };
    let _ = std::fs::remove_file(from);
    Ok(published)
}

/// Whether a no-clobber rename failed only because this platform or file
/// system does not offer it (the caller then falls back to a hard link).
fn rename_flag_unsupported(error: &io::Error) -> bool {
    #[cfg(unix)]
    {
        matches!(
            error.raw_os_error(),
            Some(libc::ENOTSUP | libc::EINVAL | libc::ENOSYS)
        ) || error.kind() == io::ErrorKind::Unsupported
    }
    #[cfg(not(unix))]
    {
        let _ = error;
        true
    }
}

#[cfg(target_vendor = "apple")]
fn rename_no_clobber(from: &Path, to: &Path) -> io::Result<()> {
    use std::os::unix::ffi::OsStrExt;
    let from = std::ffi::CString::new(from.as_os_str().as_bytes())
        .map_err(|_| io::Error::new(io::ErrorKind::InvalidInput, "path contains a NUL byte"))?;
    let to = std::ffi::CString::new(to.as_os_str().as_bytes())
        .map_err(|_| io::Error::new(io::ErrorKind::InvalidInput, "path contains a NUL byte"))?;
    // SAFETY: both arguments are NUL-terminated paths that outlive the call,
    // and `renamex_np` reads nothing else from this process's memory.
    if unsafe { libc::renamex_np(from.as_ptr(), to.as_ptr(), libc::RENAME_EXCL) } == 0 {
        Ok(())
    } else {
        Err(io::Error::last_os_error())
    }
}

#[cfg(all(target_os = "linux", any(target_env = "gnu", target_env = "musl")))]
fn rename_no_clobber(from: &Path, to: &Path) -> io::Result<()> {
    use std::os::unix::ffi::OsStrExt;
    let from = std::ffi::CString::new(from.as_os_str().as_bytes())
        .map_err(|_| io::Error::new(io::ErrorKind::InvalidInput, "path contains a NUL byte"))?;
    let to = std::ffi::CString::new(to.as_os_str().as_bytes())
        .map_err(|_| io::Error::new(io::ErrorKind::InvalidInput, "path contains a NUL byte"))?;
    // SAFETY: both arguments are NUL-terminated paths that outlive the call,
    // and `renameat2` reads nothing else from this process's memory.
    let status = unsafe {
        libc::renameat2(
            libc::AT_FDCWD,
            from.as_ptr(),
            libc::AT_FDCWD,
            to.as_ptr(),
            libc::RENAME_NOREPLACE,
        )
    };
    if status == 0 {
        Ok(())
    } else {
        Err(io::Error::last_os_error())
    }
}

#[cfg(not(any(
    target_vendor = "apple",
    all(target_os = "linux", any(target_env = "gnu", target_env = "musl"))
)))]
fn rename_no_clobber(_from: &Path, _to: &Path) -> io::Result<()> {
    Err(io::Error::from(io::ErrorKind::Unsupported))
}

/// Refuse `path` unless it is owned by this process's effective user and no
/// other user may write it: a directory (when `directory`) or a regular file,
/// never a symlink, with no group/other write bit (and, for a file, no
/// group/other bit at all). Stores that hold executable or secret bytes call
/// this before trusting anything under `path`.
#[cfg(unix)]
pub fn check_owner_private(path: &Path, directory: bool) -> io::Result<()> {
    check_owner_private_metadata(path, &std::fs::symlink_metadata(path)?, directory)
}

#[cfg(unix)]
fn check_owner_private_metadata(
    path: &Path,
    metadata: &std::fs::Metadata,
    directory: bool,
) -> io::Result<()> {
    use std::os::unix::fs::MetadataExt;

    let kind_ok = if directory {
        metadata.file_type().is_dir()
    } else {
        metadata.file_type().is_file()
    };
    if !kind_ok {
        return Err(io::Error::new(
            io::ErrorKind::PermissionDenied,
            format!(
                "{} is not a {} (symlinks are refused)",
                path.display(),
                if directory {
                    "directory"
                } else {
                    "regular file"
                }
            ),
        ));
    }
    // SAFETY: `geteuid` reads a process attribute and cannot fail.
    let euid = unsafe { libc::geteuid() };
    if metadata.uid() != euid {
        return Err(io::Error::new(
            io::ErrorKind::PermissionDenied,
            format!(
                "{} is owned by uid {}, not the effective uid {euid}",
                path.display(),
                metadata.uid()
            ),
        ));
    }
    let forbidden = if directory { 0o022 } else { 0o077 };
    if metadata.mode() & forbidden != 0 {
        let consequence = if metadata.mode() & 0o022 != 0 {
            "another user could replace its contents"
        } else {
            "another user could read it"
        };
        return Err(io::Error::new(
            io::ErrorKind::PermissionDenied,
            format!(
                "{} has mode {:04o}; {consequence}",
                path.display(),
                metadata.mode() & 0o7777
            ),
        ));
    }
    Ok(())
}

/// Non-Unix hosts have no owner/mode model this check can read: refuse.
#[cfg(not(unix))]
pub fn check_owner_private(path: &Path, _directory: bool) -> io::Result<()> {
    Err(io::Error::new(
        io::ErrorKind::Unsupported,
        format!("{}: owner-private check is Unix-only", path.display()),
    ))
}

/// Resolve directory aliases once and validate the path retained by a secret
/// or executable store. The leaf must be owner-private; every canonical
/// ancestor must be owned by this user or root and must not permit another
/// user to rename entries. Sticky shared ancestors (for example `/tmp`) are
/// allowed because all their descendants on this path have trusted owners.
///
/// Returns the canonical path, which callers must retain instead of the
/// original alias. This supports macOS `/tmp` aliases without trusting a
/// later change to a symlink. No permissions are changed. The access model is
/// Unix ownership and mode bits; callers must ensure extended ACLs or other
/// authorization mechanisms do not grant additional write access. Hostile
/// processes running as the same user or root are outside this boundary.
#[cfg(unix)]
pub fn canonical_owner_private_directory(path: &Path) -> io::Result<PathBuf> {
    use std::os::unix::fs::MetadataExt;

    let canonical = std::fs::canonicalize(path)?;
    // SAFETY: `geteuid` reads a process attribute and cannot fail.
    let euid = unsafe { libc::geteuid() };
    let ancestors: Vec<_> = canonical.ancestors().skip(1).collect();
    // Establish custody of each parent before inspecting its child.
    for ancestor in ancestors.into_iter().rev() {
        let metadata = std::fs::symlink_metadata(ancestor)?;
        if !metadata.file_type().is_dir()
            || (metadata.uid() != euid && metadata.uid() != 0)
            || (metadata.mode() & 0o022 != 0 && metadata.mode() & 0o1000 == 0)
        {
            return Err(io::Error::new(
                io::ErrorKind::PermissionDenied,
                format!(
                    "{} is not a trusted directory ancestor (uid {}, mode {:04o})",
                    ancestor.display(),
                    metadata.uid(),
                    metadata.mode() & 0o7777
                ),
            ));
        }
    }
    check_owner_private(&canonical, true)?;
    Ok(canonical)
}

/// Non-Unix hosts lack the ownership and rename policy this boundary needs.
#[cfg(not(unix))]
pub fn canonical_owner_private_directory(path: &Path) -> io::Result<PathBuf> {
    Err(io::Error::new(
        io::ErrorKind::Unsupported,
        format!(
            "{}: owner-private directory check is Unix-only",
            path.display()
        ),
    ))
}

/// Open an owner-private regular file without following a final symlink, and
/// check the opened descriptor rather than a pathname examined before open.
/// Callers must also protect its ancestors (for example by retaining a path
/// from [`canonical_owner_private_directory`]). No permissions are changed.
#[cfg(unix)]
pub fn open_owner_private_file(path: &Path) -> io::Result<File> {
    use std::os::unix::fs::OpenOptionsExt;

    // O_NONBLOCK avoids waiting on a replaced FIFO before fstat can reject
    // its kind. It has no effect on an admitted regular file.
    let file = std::fs::OpenOptions::new()
        .read(true)
        .custom_flags(libc::O_NOFOLLOW | libc::O_NONBLOCK)
        .open(path)?;
    check_owner_private_metadata(path, &file.metadata()?, false)?;
    Ok(file)
}

/// Non-Unix hosts have no owner/mode model this boundary can authenticate.
#[cfg(not(unix))]
pub fn open_owner_private_file(path: &Path) -> io::Result<File> {
    Err(io::Error::new(
        io::ErrorKind::Unsupported,
        format!("{}: owner-private file open is Unix-only", path.display()),
    ))
}

#[cfg(all(test, unix))]
mod tests {
    use super::*;
    use std::os::unix::fs::{MetadataExt, PermissionsExt};
    use std::path::PathBuf;

    const CHILD: &str = "PRIVATE_FS_UMASK_CHILD";

    thread_local! {
        /// Makes this thread's `fchmodat` in `settle_new_directory_mode` fail
        /// with ENOTSUP, as glibc < 2.32 does for `AT_SYMLINK_NOFOLLOW`.
        pub(super) static SETTLE_FAILS: std::cell::Cell<bool> =
            const { std::cell::Cell::new(false) };
    }

    fn mode(path: &Path) -> u32 {
        std::fs::symlink_metadata(path).unwrap().mode() & 0o7777
    }

    /// The one user-cache rule, row for row the table
    /// `scripts/tests/test_private_cache.py` holds `private_cache.py`'s
    /// `user_cache_base` to (same results, same refusal texts): an absolute
    /// XDG_CACHE_HOME wins, exactly as given; an empty or relative one (a
    /// leading space makes it relative) is ignored; then an absolute HOME's
    /// `.cache`; else no cache. The scoped
    /// reader sees request-scoped values.
    #[test]
    fn user_cache_base_is_the_xdg_rule_and_never_the_working_directory() {
        let refused_home = |home: &str| {
            Err(format!(
                "HOME={home} is not absolute and XDG_CACHE_HOME names no absolute directory"
            ))
        };
        let neither = Err("neither XDG_CACHE_HOME nor HOME names an absolute directory".to_owned());
        /// `XDG_CACHE_HOME`, `HOME` and the base they resolve to.
        type Row<'a> = (Option<&'a str>, Option<&'a str>, Result<PathBuf, String>);
        let rows: [Row<'_>; 10] = [
            (Some("/xdg"), Some("/home/u"), Ok("/xdg".into())),
            (Some("/xdg"), None, Ok("/xdg".into())),
            (Some(""), Some("/home/u"), Ok("/home/u/.cache".into())),
            (
                Some("relative"),
                Some("/home/u"),
                Ok("/home/u/.cache".into()),
            ),
            (
                Some(" /padded"),
                Some("/home/u"),
                Ok("/home/u/.cache".into()),
            ),
            (None, Some("/home/u"), Ok("/home/u/.cache".into())),
            (
                Some("relative"),
                Some("relative-home"),
                refused_home("relative-home"),
            ),
            (Some(""), Some(""), refused_home("")),
            (Some("relative"), None, neither.clone()),
            (None, None, neither),
        ];
        for (xdg, home, expected) in rows {
            assert_eq!(
                user_cache_base(xdg.map(OsStr::new), home.map(OsStr::new)),
                expected,
                "XDG_CACHE_HOME={xdg:?} HOME={home:?}"
            );
            crate::with_env_edits(|env| {
                match xdg {
                    Some(value) => env.set("XDG_CACHE_HOME", value),
                    None => env.remove("XDG_CACHE_HOME"),
                }
                match home {
                    Some(value) => env.set("HOME", value),
                    None => env.remove("HOME"),
                }
                assert_eq!(current_user_cache_base(), expected);
            });
        }
    }

    /// A no-clobber publish moves the complete file into place, never
    /// replaces an existing one, and consumes the source either way.
    #[test]
    fn publish_no_clobber_publishes_once_and_never_replaces() {
        let dir = scratch("publish");
        let target = dir.join("target");
        let first = dir.join("first.tmp");
        std::fs::write(&first, b"first").unwrap();
        assert!(publish_no_clobber(&first, &target).unwrap());
        assert!(!first.exists(), "the source is consumed");
        assert_eq!(std::fs::read(&target).unwrap(), b"first");
        let second = dir.join("second.tmp");
        std::fs::write(&second, b"second").unwrap();
        assert!(!publish_no_clobber(&second, &target).unwrap());
        assert!(!second.exists(), "the losing source is removed");
        assert_eq!(std::fs::read(&target).unwrap(), b"first", "never replaced");
        std::fs::remove_dir_all(&dir).unwrap();
    }

    /// The reporting variant answers whether THIS call made the leaf: a
    /// fresh leaf (with or without missing ancestors) reads `true`, an
    /// existing one `false`, and the leaf is private either way.
    #[test]
    fn reporting_creation_answers_whether_this_call_made_the_leaf() {
        let dir = scratch("reporting");
        let leaf = dir.join("store");
        assert!(create_private_dir_all_reporting(&leaf).unwrap());
        assert_eq!(mode(&leaf), PRIVATE_DIRECTORY_MODE);
        assert!(!create_private_dir_all_reporting(&leaf).unwrap());
        let deep = dir.join("a").join("b").join("store");
        assert!(create_private_dir_all_reporting(&deep).unwrap());
        assert_eq!(mode(&deep), PRIVATE_DIRECTORY_MODE);
        assert!(!create_private_dir_all_reporting(&deep).unwrap());
        std::fs::remove_dir_all(&dir).unwrap();
    }

    /// A fresh scratch directory under the system temporary directory, mode
    /// exactly `0700` whatever this process's umask, so a test that checks
    /// its ancestors sees the same fixture under umask `0002` as under
    /// `0022` (a umask-mode scratch directory was `0775` under `0002`, and
    /// the ancestor check rightly refused it).
    fn scratch(label: &str) -> PathBuf {
        use std::sync::atomic::{AtomicU64, Ordering};
        static NEXT: AtomicU64 = AtomicU64::new(0);
        let dir = std::env::temp_dir().join(format!(
            "trust-cg-private-fs-{label}-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        std::fs::create_dir(&dir).unwrap();
        std::fs::set_permissions(&dir, std::fs::Permissions::from_mode(0o700)).unwrap();
        dir
    }

    /// Run test `name` again in a child test process started by `sh` under
    /// `umask`, with a fresh scratch directory. The umask is a process
    /// attribute, so it is set only in that child, never in this harness.
    fn in_child_under_umask(name: &str, umask: &str) {
        let dir = scratch("child");
        let output = std::process::Command::new("/bin/sh")
            .arg("-c")
            .arg(format!("umask {umask} && exec \"$0\" \"$@\""))
            .arg(std::env::current_exe().unwrap())
            .args(["--exact", name, "--nocapture", "--test-threads=1"])
            .env(CHILD, &dir)
            .output()
            .unwrap();
        let _ = std::fs::remove_dir_all(&dir);
        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(
            output.status.success() && stdout.contains("1 passed"),
            "umask {umask} child of {name}: {}\n{stdout}\n{stderr}",
            output.status
        );
    }

    fn child_dir() -> Option<PathBuf> {
        std::env::var_os(CHILD).map(PathBuf::from)
    }

    /// Under umask 0002 `std::fs::create_dir_all` makes `0775` directories
    /// (the control), while every directory the helper creates is `0700` and
    /// an existing group-writable ancestor is left exactly as it was.
    #[test]
    fn creates_only_0700_directories_under_umask_0002() {
        let Some(dir) = child_dir() else {
            in_child_under_umask(
                "private_fs::tests::creates_only_0700_directories_under_umask_0002",
                "0002",
            );
            return;
        };
        let control = dir.join("control/nested");
        std::fs::create_dir_all(&control).unwrap();
        assert_eq!(mode(&control), 0o775, "the child must run under umask 0002");

        let open = dir.join("open");
        std::fs::create_dir(&open).unwrap();
        assert_eq!(mode(&open), 0o775);
        let tree = open.join("cache/trust-cg/ay-exec");
        create_private_dir_all(&tree).unwrap();
        for created in [
            open.join("cache"),
            open.join("cache/trust-cg"),
            tree.clone(),
        ] {
            assert_eq!(mode(&created), 0o700, "{}", created.display());
        }
        assert_eq!(mode(&open), 0o775, "an existing directory is never changed");
        // Existing directories, a symlink to one included, are success.
        create_private_dir_all(&tree).unwrap();
        let link = dir.join("link");
        std::os::unix::fs::symlink(&tree, &link).unwrap();
        create_private_dir_all(&link).unwrap();
        create_private_dir_all(&link.join("below")).unwrap();
        assert_eq!(mode(&tree.join("below")), 0o700);

        let file = tree.join("entry");
        drop(create_private_file(&file).unwrap());
        assert_eq!(mode(&file), 0o600);
        assert_eq!(
            create_private_file(&file).unwrap_err().kind(),
            io::ErrorKind::AlreadyExists
        );
        println!("PRIVATE_FS_UMASK_0002 created=0700 control=0775");
    }

    /// A umask that clears the owner's own bits, and a set-group-ID parent,
    /// still produce exactly `0700` directories and `0600` files.
    #[test]
    fn corrects_owner_bits_and_inherited_setgid() {
        let Some(dir) = child_dir() else {
            for umask in ["0277", "0477", "0077"] {
                in_child_under_umask(
                    "private_fs::tests::corrects_owner_bits_and_inherited_setgid",
                    umask,
                );
            }
            return;
        };
        let tree = dir.join("a/b/c");
        create_private_dir_all(&tree).unwrap();
        for created in [dir.join("a"), dir.join("a/b"), tree.clone()] {
            assert_eq!(mode(&created), 0o700, "{}", created.display());
        }
        let file = tree.join("entry");
        drop(create_private_file(&file).unwrap());
        assert_eq!(mode(&file), 0o600);

        // The owner may set the set-group-ID bit on a directory of its own
        // group; Linux then gives it to every directory created inside.
        let shared = dir.join("setgid");
        std::fs::create_dir(&shared).unwrap();
        std::fs::set_permissions(&shared, std::fs::Permissions::from_mode(0o2770)).unwrap();
        if mode(&shared) == 0o2770 {
            let below = shared.join("x/y");
            create_private_dir_all(&below).unwrap();
            assert_eq!(mode(&shared.join("x")), 0o700);
            assert_eq!(mode(&below), 0o700);
            assert_eq!(
                mode(&shared),
                0o2770,
                "an existing directory is never changed"
            );
        }
    }

    /// A directory this call created but cannot make `0700` (the mode fix
    /// fails, as `fchmodat(AT_SYMLINK_NOFOLLOW)` does on glibc < 2.32) is an
    /// error and is removed, under a umask that clears an owner bit and under
    /// a set-group-ID parent. Only a directory that existed before the call is
    /// accepted as it is.
    #[test]
    fn a_new_directory_that_cannot_be_made_private_is_an_error() {
        let Some(dir) = child_dir() else {
            in_child_under_umask(
                "private_fs::tests::a_new_directory_that_cannot_be_made_private_is_an_error",
                "0277",
            );
            return;
        };
        struct Injected;
        impl Drop for Injected {
            fn drop(&mut self) {
                SETTLE_FAILS.with(|fails| fails.set(false));
            }
        }
        let _injected = Injected;
        SETTLE_FAILS.with(|fails| fails.set(true));

        // Umask 0277: mkdir gives 0500, which only the mode fix corrects.
        let tree = dir.join("a/b");
        let error = create_private_dir_all(&tree).unwrap_err();
        assert_eq!(error.raw_os_error(), None, "{error}");
        let message = error.to_string();
        assert!(
            message.contains("with mode 0500 and cannot make it 0700"),
            "{message}"
        );
        assert!(
            !dir.join("a").exists(),
            "the unsettled directory is removed"
        );
        assert!(
            create_private_dir_all(&tree).is_err(),
            "a retry fails the same way"
        );

        // A set-group-ID parent: mkdir gives 2700 (or 2500 under this umask).
        let shared = dir.join("setgid");
        std::fs::create_dir(&shared).unwrap();
        std::fs::set_permissions(&shared, std::fs::Permissions::from_mode(0o2770)).unwrap();
        if mode(&shared) == 0o2770 {
            let below = shared.join("x");
            let message = create_private_dir_all(&below).unwrap_err().to_string();
            assert!(message.contains("cannot make it 0700"), "{message}");
            assert!(!below.exists());
        }

        // Directories that existed before the call are accepted unchanged;
        // no mode fix runs for them.
        let existing = dir.join("existing");
        std::fs::create_dir(&existing).unwrap();
        assert_eq!(mode(&existing), 0o500);
        create_private_dir_all(&existing).unwrap();
        assert_eq!(mode(&existing), 0o500);

        // Without the injected failure the same creation succeeds.
        SETTLE_FAILS.with(|fails| fails.set(false));
        create_private_dir_all(&tree).unwrap();
        assert_eq!(mode(&dir.join("a")), 0o700);
        assert_eq!(mode(&tree), 0o700);
    }

    /// A path through a regular file is refused, and nothing is created.
    #[test]
    fn refuses_a_file_in_the_way() {
        let dir = scratch("file");
        let file = dir.join("file");
        std::fs::write(&file, b"x").unwrap();
        assert!(create_private_dir_all(&file).is_err());
        assert!(create_private_dir_all(&file.join("below")).is_err());
        assert!(std::fs::symlink_metadata(file.join("below")).is_err());
        std::fs::remove_dir_all(&dir).unwrap();
    }

    /// The owner-private check accepts exactly an owned, non-symlink entry
    /// of the requested kind that no other user can write.
    #[test]
    fn owner_private_check_refuses_shared_symlinked_and_wrong_kind_entries() {
        let dir = scratch("owner");
        let store = dir.join("store");
        create_private_dir_all(&store).unwrap();
        check_owner_private(&store, true).unwrap();
        assert!(
            check_owner_private(&store, false).is_err(),
            "a directory is not a file"
        );
        std::fs::set_permissions(&store, std::fs::Permissions::from_mode(0o777)).unwrap();
        assert!(
            check_owner_private(&store, true).is_err(),
            "world-writable directory"
        );
        std::fs::set_permissions(&store, std::fs::Permissions::from_mode(0o720)).unwrap();
        assert!(
            check_owner_private(&store, true).is_err(),
            "group-writable directory"
        );
        std::fs::set_permissions(&store, std::fs::Permissions::from_mode(0o755)).unwrap();
        check_owner_private(&store, true).unwrap();

        let key = store.join("key");
        drop(create_private_file(&key).unwrap());
        check_owner_private(&key, false).unwrap();
        std::fs::set_permissions(&key, std::fs::Permissions::from_mode(0o640)).unwrap();
        let readable = check_owner_private(&key, false).unwrap_err().to_string();
        assert!(
            readable.ends_with("has mode 0640; another user could read it"),
            "group-readable secret: {readable}"
        );
        std::fs::set_permissions(&key, std::fs::Permissions::from_mode(0o620)).unwrap();
        let writable = check_owner_private(&key, false).unwrap_err().to_string();
        assert!(
            writable.ends_with("has mode 0620; another user could replace its contents"),
            "group-writable secret: {writable}"
        );
        std::fs::set_permissions(&key, std::fs::Permissions::from_mode(0o600)).unwrap();
        let link = store.join("link");
        std::os::unix::fs::symlink(&key, &link).unwrap();
        assert!(
            check_owner_private(&link, false).is_err(),
            "symlink to a private file"
        );
        assert!(check_owner_private(&store.join("absent"), false).is_err());
        std::fs::remove_dir_all(&dir).unwrap();
    }

    /// Runs here and again in a child under umask `0002`. Each run makes its
    /// own fixture (`scratch`, then `create_private_dir_all`), so the child's
    /// run shows that the fixture does not depend on the umask: with a
    /// umask-mode `scratch`, the child's ancestor check refuses its own
    /// `0775` scratch directory.
    #[test]
    fn canonical_private_directory_refuses_mutable_ancestors_and_retains_alias_target() {
        if child_dir().is_none() {
            in_child_under_umask(
                "private_fs::tests::\
                 canonical_private_directory_refuses_mutable_ancestors_and_retains_alias_target",
                "0002",
            );
        }
        let dir = scratch("ancestors");
        let parent = dir.join("parent");
        let store = parent.join("store");
        create_private_dir_all(&store).unwrap();
        let expected = std::fs::canonicalize(&store).unwrap();
        assert_eq!(canonical_owner_private_directory(&store).unwrap(), expected);

        for ancestor_mode in [0o777, 0o770] {
            std::fs::set_permissions(&parent, std::fs::Permissions::from_mode(ancestor_mode))
                .unwrap();
            let error = canonical_owner_private_directory(&store).unwrap_err();
            assert_eq!(error.kind(), io::ErrorKind::PermissionDenied);
            assert_eq!(
                mode(&parent),
                ancestor_mode,
                "never repair an existing ancestor"
            );
        }
        std::fs::set_permissions(&parent, std::fs::Permissions::from_mode(0o1777)).unwrap();
        assert_eq!(canonical_owner_private_directory(&store).unwrap(), expected);

        let alias = dir.join("alias");
        std::os::unix::fs::symlink(&store, &alias).unwrap();
        let retained = canonical_owner_private_directory(&alias).unwrap();
        assert_eq!(retained, expected);
        let other = dir.join("other");
        create_private_dir_all(&other).unwrap();
        std::fs::remove_file(&alias).unwrap();
        std::os::unix::fs::symlink(&other, &alias).unwrap();
        assert_eq!(
            retained, expected,
            "the retained path does not follow the changed alias"
        );
        assert_ne!(std::fs::canonicalize(&alias).unwrap(), retained);
        std::fs::remove_dir_all(&dir).unwrap();
    }

    #[test]
    fn private_file_descriptor_is_bound_to_the_opened_inode() {
        use std::io::{Read, Write};

        let dir = scratch("descriptor");
        let key = dir.join("key");
        let moved = dir.join("moved");
        create_private_file(&key)
            .unwrap()
            .write_all(b"original")
            .unwrap();
        let mut opened = open_owner_private_file(&key).unwrap();
        let opened_inode = opened.metadata().unwrap().ino();
        std::fs::rename(&key, &moved).unwrap();
        create_private_file(&key)
            .unwrap()
            .write_all(b"replacement")
            .unwrap();
        let mut bytes = Vec::new();
        opened.read_to_end(&mut bytes).unwrap();
        assert_eq!(bytes, b"original");
        assert_eq!(opened_inode, std::fs::metadata(&moved).unwrap().ino());
        assert_ne!(opened_inode, std::fs::metadata(&key).unwrap().ino());
        std::fs::remove_file(&key).unwrap();
        std::os::unix::fs::symlink(&moved, &key).unwrap();
        assert!(
            open_owner_private_file(&key).is_err(),
            "never follow a final symlink"
        );
        assert!(
            open_owner_private_file(&dir).is_err(),
            "a directory is not a regular file"
        );
        std::fs::set_permissions(&moved, std::fs::Permissions::from_mode(0o640)).unwrap();
        assert_eq!(
            open_owner_private_file(&moved).unwrap_err().kind(),
            io::ErrorKind::PermissionDenied
        );
        std::fs::remove_dir_all(&dir).unwrap();
    }
}
