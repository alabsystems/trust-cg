// trust-cg-verify/ay_private_copy.rs - the bytes an admitted AY is started from
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! A private, content-addressed copy of an admitted AY, owned by this user.
//!
//! # Why admission alone is not enough
//!
//! Admission digests the file at the admitted path. Starting a process from
//! that path afterwards still lets whoever can write the path choose what runs,
//! and not only in the microseconds between the last check and `exec(2)`: AY
//! RE-EXECUTES ITSELF BY PATH. On macOS its first statement
//! (`ay_sys::govern::arm`, AY commit 075a482ae) re-execs
//! `std::env::current_exe()` under `/usr/sbin/taskpolicy -m <MB>` so a kernel
//! memory bound binds the real image, unless `AY_GOVERN_ARMED` is already set.
//! Measured 2026-09-24 against the Trust 9192 `bin/ay` (ay 0.26.0 build 9624,
//! sha256 40e852cc…): a byte copy started by path and replaced by a shell script
//! 30 ms later printed the script's `unsat`; setting `RUST_MIN_STACK` (which
//! gates only the `pb` subcommand's own re-exec) did not change that. The
//! re-exec happens for as long as AY takes to start, so a verdict could be
//! credited to the admitted digest while another program produced it.
//!
//! Setting `AY_GOVERN_ARMED` would stop the re-exec, but only by switching off
//! the kernel memory bound AY refuses to run without (its `EXIT_UNGOVERNED`);
//! that trades a safety property for this one, so it is not done.
//!
//! # The rule
//!
//! After the admitted bytes are digested, they are copied into
//! `<user cache>/trust-cg/ay-exec/<sha256>/ay`, where `<user cache>` is
//! `$XDG_CACHE_HOME` or `$HOME/.cache` (both absolute: an empty or relative
//! `XDG_CACHE_HOME` is ignored and a relative `HOME` names no cache; read
//! through `trust-cg-process-env` by the one rule every trust-cg cache root
//! shares, `private_fs::user_cache_base`):
//!
//! * `ay-exec` and `<sha256>` are directories owned by this user with mode
//!   exactly `0700`; every ancestor (including the shared `trust-cg` cache
//!   directory) is owned by this user or root, is not a symlink after the
//!   base is resolved, and is not writable by group or others unless it is
//!   sticky (as `/tmp` is). Every directory of that path trust-cg creates is
//!   made `0700` whatever the umask (`trust_cg_process_env::private_fs`, the
//!   rule every trust-cg cache shares), so under umask `0002` the tree it
//!   creates passes this rule. A directory that already exists is never
//!   changed: one too permissive is refused with the directory, its mode and
//!   the remedy (`chmod go-w <dir>`, or an `XDG_CACHE_HOME` only this user
//!   can write), which `TCG-AY-IDENTITY-UNMATERIALIZED` carries to the
//!   proof-promotion refusal it causes;
//! * the copy is a regular file (never a symlink) owned by this user, with mode
//!   exactly `0500` and a single link, whose bytes digest to the admitted
//!   SHA-256. It is streamed to a temporary name in bounded chunks, each
//!   digested as it is written; only a temporary whose streamed digest is the
//!   admitted one is published, with a no-clobber link, so two processes never
//!   replace each other's copy, and the published file is digested again
//!   before it is used. The writer holds an exclusive lock on its
//!   temporary until it publishes or exits; a later materialization removes
//!   a temporary whose lock is free and which is older than the
//!   create-to-lock window, so a writer killed mid-copy leaks nothing.
//!
//! AY is started from this copy, so its self re-exec lands on the same
//! admitted bytes. Before every start the copy is checked again: the same
//! ownership, mode and link count, and the same file state (device, inode,
//! size, mtime, ctime) its digest is bound to. Nobody but this user (or root)
//! can write the directory or change the file, and any change the owner makes
//! moves the file's ctime, which cannot be set back without root.
//!
//! # What remains trusted
//!
//! This user and root: both can already change the running verifier itself.

use std::io::Write;
use std::path::{Path, PathBuf};

use super::{FileStamp, digest_file, file_stamp};

/// Directory, under the user cache, holding the private copies.
const EXEC_DIRECTORY: [&str; 2] = ["trust-cg", "ay-exec"];

/// Name prefix of the temporary a copy is written to before it is published.
const TEMPORARY_PREFIX: &str = ".ay-copy-";

/// A temporary younger than this is never removed: its writer may be between
/// creating it and locking it (microseconds in practice).
const STALE_TEMPORARY_AGE: std::time::Duration = std::time::Duration::from_secs(300);

/// At most this many temporaries are examined per materialization.
const STALE_TEMPORARY_SCAN_LIMIT: usize = 64;

/// Bytes a copy is read, digested and written in at a time.
pub(super) const COPY_CHUNK_BYTES: usize = 1 << 20;

/// A verified private copy of admitted AY bytes.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(super) struct PrivateCopy {
    path: PathBuf,
    stamp: FileStamp,
}

impl PrivateCopy {
    pub(super) fn path(&self) -> &Path {
        &self.path
    }

    /// Re-check the copy before a start: still private, still the file whose
    /// bytes digest to `sha256`.
    pub(super) fn verify(&self, sha256: &str) -> Result<(), String> {
        check_private_file(&self.path)?;
        if file_stamp(&self.path).as_ref() != Some(&self.stamp) {
            return Err("the private copy was replaced or modified".to_owned());
        }
        check_private_dir(parent(&self.path)?)?;
        // Memoized against the exact file state checked above; a changed file
        // was refused already, so this reads the bytes once per process.
        let (found, stamp) = digest_file(&self.path)?;
        if found != sha256 || stamp != self.stamp {
            return Err(format!(
                "the private copy digests to {found}, not the admitted {sha256}"
            ));
        }
        Ok(())
    }
}

fn parent(path: &Path) -> Result<&Path, String> {
    path.parent()
        .ok_or_else(|| format!("{} has no parent directory", path.display()))
}

/// `<user cache>/trust-cg/ay-exec`, the user cache base by the one rule every
/// trust-cg cache root is resolved by
/// (`trust_cg_process_env::private_fs::user_cache_base`: only an absolute
/// value is used; a relative one would depend on the working directory).
/// Process-level admission
/// (`--print-ay-identity`, the floor's preflight, the refusal note) and every
/// function-verification request read the same `XDG_CACHE_HOME` and `HOME`
/// here: a request freezes them as given, never anchored to its working
/// directory (`function_request::capture_policy`), so all of them resolve
/// this same root wherever they run.
#[cfg(not(test))]
fn exec_root(_sha256: &str) -> Result<PathBuf, String> {
    let mut root = trust_cg_process_env::private_fs::current_user_cache_base()?;
    root.extend(EXEC_DIRECTORY);
    Ok(root)
}

/// Unit tests keep their copies out of the user's cache, under the same
/// checks, in one of two roots:
///
/// * the AY this build records (the toolchain `bin/ay`, hundreds of MB) is
///   copied ONCE per user into a shared root that every test process reuses,
///   as production reuses `<cache>/trust-cg/ay-exec/<sha256>`. A per-process
///   root kept a 626 MB copy for every test process (measured 2026-09-26: 104
///   processes, 65 GB). Concurrent processes publish it with the same
///   no-clobber link as production and nothing ever deletes it, so no
///   process races another's removal;
/// * fixture executables (a few hundred bytes each, and some tests tamper
///   with their copies or open their root) get a private root per test
///   process, removed when the process exits.
#[cfg(test)]
fn exec_root(sha256: &str) -> Result<PathBuf, String> {
    let recorded = super::ToolchainAyRecord::recorded()
        .expected()
        .is_ok_and(|identity| identity.sha256() == sha256);
    if recorded {
        Ok(shared_test_root())
    } else {
        process_test_root()
    }
}

/// `<temp dir>/trust-cg-verify-ay-exec-uid<uid>/trust-cg/ay-exec`: one per
/// user. The ownership and ancestor checks refuse one another user made.
#[cfg(test)]
pub(super) fn shared_test_root() -> PathBuf {
    #[cfg(unix)]
    let user = current_uid().to_string();
    #[cfg(not(unix))]
    let user = "user".to_owned();
    let mut root = std::env::temp_dir().join(format!("trust-cg-verify-ay-exec-uid{user}"));
    root.extend(EXEC_DIRECTORY);
    root
}

#[cfg(test)]
fn process_test_root() -> Result<PathBuf, String> {
    use std::sync::OnceLock;
    static ROOT: OnceLock<Result<PathBuf, String>> = OnceLock::new();
    ROOT.get_or_init(|| {
        let mut builder = tempfile::Builder::new();
        builder.prefix("trust-cg-verify-ay-exec-");
        // An ancestor of the private copy: `0700` like every cache directory
        // trust-cg creates (tempfile's default is `0777 & !umask`, `0775`
        // under umask 0002, which the ancestor rule refuses).
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            builder.permissions(std::fs::Permissions::from_mode(0o700));
        }
        let base = builder
            .tempdir()
            .map_err(|error| format!("cannot create the unit-test cache: {error}"))?
            .keep();
        remove_at_process_exit(&base);
        let mut root = base;
        root.extend(EXEC_DIRECTORY);
        Ok(root)
    })
    .clone()
}

/// Remove `path` (a directory) when this test process exits. libtest catches
/// a failing test's panic and then exits the process normally, so this runs
/// after failures too; only a killed process leaves its (small) directories.
#[cfg(test)]
pub(super) fn remove_at_process_exit(path: &Path) {
    use std::sync::{Mutex, OnceLock};
    static PATHS: OnceLock<Mutex<Vec<PathBuf>>> = OnceLock::new();
    extern "C" fn remove_registered() {
        if let Some(paths) = PATHS.get() {
            let paths = paths
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner);
            for path in paths.iter() {
                let _ = std::fs::remove_dir_all(path);
            }
        }
    }
    let mut registered = false;
    let paths = PATHS.get_or_init(|| {
        registered = true;
        Mutex::new(Vec::new())
    });
    paths
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner)
        .push(path.to_path_buf());
    #[cfg(unix)]
    if registered {
        // SAFETY: `remove_registered` takes no arguments and only reads a
        // static; registering it has no other effect on this process.
        unsafe {
            libc::atexit(remove_registered);
        }
    }
    #[cfg(not(unix))]
    let _ = (registered, remove_registered as extern "C" fn());
}

#[cfg(unix)]
fn current_uid() -> u32 {
    // SAFETY: geteuid takes no arguments, cannot fail and touches no memory
    // the caller owns.
    unsafe { libc::geteuid() }
}

/// Create `path` (mode `0700`, whatever the umask) if it is missing, then
/// require it private.
fn ensure_private_dir(path: &Path) -> Result<(), String> {
    match std::fs::symlink_metadata(path) {
        Ok(_) => {}
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => {
            create_private_dir_all(path)?;
        }
        Err(error) => return Err(format!("cannot stat {}: {error}", path.display())),
    }
    check_private_dir(path)
}

/// The one creation rule of every trust-cg cache directory: each directory
/// created is `0700` whatever the umask; an existing one is left as it is.
fn create_private_dir_all(path: &Path) -> Result<(), String> {
    trust_cg_process_env::private_fs::create_private_dir_all(path)
        .map_err(|error| format!("cannot create {}: {error}", path.display()))
}

/// A directory owned by this user, not a symlink, mode exactly `0700`.
fn check_private_dir(path: &Path) -> Result<(), String> {
    let metadata = std::fs::symlink_metadata(path)
        .map_err(|error| format!("cannot stat {}: {error}", path.display()))?;
    if !metadata.file_type().is_dir() {
        return Err(format!("{} is not a directory", path.display()));
    }
    #[cfg(unix)]
    {
        use std::os::unix::fs::MetadataExt;
        if metadata.uid() != current_uid() {
            return Err(format!(
                "{} is owned by uid {}, not this user (uid {})",
                path.display(),
                metadata.uid(),
                current_uid()
            ));
        }
        let mode = metadata.mode() & 0o7777;
        if mode != 0o700 {
            return Err(format!(
                "{} has mode {mode:04o}, not 0700 (trust-cg never changes an existing \
                 directory; `chmod 0700 {}` makes it private)",
                path.display(),
                path.display()
            ));
        }
    }
    Ok(())
}

/// A regular file owned by this user, not a symlink, mode exactly `0500`, one
/// link (no other name through which it could be reached).
fn check_private_file(path: &Path) -> Result<(), String> {
    let metadata = std::fs::symlink_metadata(path)
        .map_err(|error| format!("cannot stat {}: {error}", path.display()))?;
    if !metadata.file_type().is_file() {
        return Err(format!("{} is not a regular file", path.display()));
    }
    #[cfg(unix)]
    {
        use std::os::unix::fs::MetadataExt;
        if metadata.uid() != current_uid() {
            return Err(format!(
                "{} is owned by uid {}, not this user (uid {})",
                path.display(),
                metadata.uid(),
                current_uid()
            ));
        }
        let mode = metadata.mode() & 0o7777;
        if mode != 0o500 {
            return Err(format!("{} has mode {mode:04o}, not 0500", path.display()));
        }
        if metadata.nlink() != 1 {
            return Err(format!(
                "{} has {} links, not 1",
                path.display(),
                metadata.nlink()
            ));
        }
    }
    Ok(())
}

/// Every ancestor of `root` is owned by this user or root, and nobody else can
/// rename entries in it: not group/other writable, unless sticky.
fn check_ancestors(root: &Path) -> Result<(), String> {
    #[cfg(unix)]
    {
        use std::os::unix::fs::MetadataExt;
        for ancestor in root.ancestors().skip(1) {
            let metadata = std::fs::symlink_metadata(ancestor)
                .map_err(|error| format!("cannot stat {}: {error}", ancestor.display()))?;
            if !metadata.file_type().is_dir() {
                return Err(format!(
                    "{} is not a directory (a symlink is not followed)",
                    ancestor.display()
                ));
            }
            if metadata.uid() != 0 && metadata.uid() != current_uid() {
                return Err(format!(
                    "{} is owned by uid {}, neither this user nor root (set XDG_CACHE_HOME \
                     to a directory this user owns)",
                    ancestor.display(),
                    metadata.uid()
                ));
            }
            let mode = metadata.mode() & 0o7777;
            if mode & 0o022 != 0 && mode & 0o1000 == 0 {
                return Err(ancestor_refusal(ancestor, mode));
            }
        }
    }
    #[cfg(not(unix))]
    let _ = root;
    Ok(())
}

/// Why an ancestor that group or others may write refuses AY, with the
/// remedy. The directory is never changed automatically: it may be shared on
/// purpose, and its owner decides.
#[cfg(unix)]
fn ancestor_refusal(ancestor: &Path, mode: u32) -> String {
    format!(
        "{dir} has mode {mode:04o}: others may rename entries in it, so no AY is started \
         beneath it; run `chmod go-w {dir}` or set XDG_CACHE_HOME to a directory only this \
         user can write (trust-cg creates each cache directory 0700 whatever the umask, but \
         never changes one that already exists)",
        dir = ancestor.display()
    )
}

/// The private directory tree, created as needed and checked. Returns the
/// resolved `ay-exec` directory.
fn private_root(sha256: &str) -> Result<PathBuf, String> {
    private_root_at(&exec_root(sha256)?)
}

/// [`private_root`] for the `.../trust-cg/ay-exec` directory `root`.
///
/// The base is resolved ONCE (`canonicalize`) and everything below it is
/// named from the resolved base, never through `root` again, so the returned
/// directory is the one the checks examined: an alias of the base (a symlink
/// in a directory others can write) is used only where it led at the check.
/// Each directory is judged before anything is created in it: nothing is
/// created inside a `trust-cg` that already exists open to others or as a
/// symlink, nor inside a base that is, or lies below, a directory others may
/// rename entries in, before the refusal (X-HOST-P13 third closure audit:
/// `ay-exec` was created inside an open and inside a symlinked `trust-cg`,
/// then refused). The base itself is still created when missing: it must
/// exist to be resolved.
pub(super) fn private_root_at(root: &Path) -> Result<PathBuf, String> {
    let base = root
        .parent()
        .and_then(Path::parent)
        .ok_or_else(|| format!("{} has no cache base", root.display()))?;
    create_private_dir_all(base)?;
    let base = std::fs::canonicalize(base)
        .map_err(|error| format!("cannot resolve {}: {error}", base.display()))?;
    // `trust-cg` is shared with the other trust-cg caches, which create it by
    // the same `0700` rule; one that already exists keeps its mode and is
    // held to the ancestor rule. Only `ay-exec` and what it contains must be
    // exactly private.
    let trust_cg = base.join(EXEC_DIRECTORY[0]);
    check_ancestors(&trust_cg)?;
    create_private_dir_all(&trust_cg)?;
    let root = trust_cg.join(EXEC_DIRECTORY[1]);
    check_ancestors(&root)?;
    ensure_private_dir(&root)?;
    Ok(root)
}

/// The private copy of the admitted bytes with digest `sha256`, whose original
/// is `source`. An existing copy is reused only after the same checks as a new
/// one; one that fails them is removed and written again.
pub(super) fn materialize(source: &Path, sha256: &str) -> Result<PrivateCopy, String> {
    let root = private_root(sha256)?;
    let directory = root.join(sha256);
    ensure_private_dir(&directory)?;
    // One writer per copy in this process. The identity-warm thread and the
    // first proof query both resolve the AY; without this, both found no copy
    // in a fresh cache root and each streamed the whole AY into its own
    // temporary (a second 91 MB read, digest and write). A thread that waits
    // here finds the published copy and checks it like any existing one.
    // Other processes are still arbitrated by the no-clobber publication.
    let writer = copy_writer(&directory);
    let _writing = writer
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner());
    // A writer killed mid-copy leaves its temporary (up to the whole AY)
    // behind in this shared directory; nothing else would ever remove it.
    remove_stale_temporaries(&directory);
    let path = directory.join(format!("ay{}", std::env::consts::EXE_SUFFIX));
    // Concurrent processes publish the same digest; a copy another process is
    // publishing (or removed as invalid) is simply checked again.
    let mut attempt = 0;
    loop {
        attempt += 1;
        if std::fs::symlink_metadata(&path).is_ok() {
            match existing(&path, sha256) {
                Ok(copy) => {
                    note_found(&copy);
                    return Ok(copy);
                }
                Err(_) => match std::fs::remove_file(&path) {
                    Ok(()) => {}
                    Err(error) if error.kind() == std::io::ErrorKind::NotFound => {}
                    Err(error) => {
                        return Err(format!(
                            "cannot remove the invalid copy {}: {error}",
                            path.display()
                        ));
                    }
                },
            }
        }
        if write_copy(source, sha256, &directory, &path)? {
            begin_host_assessment_of_published(&path);
        }
        match existing(&path, sha256) {
            Ok(copy) => {
                note_published(&copy);
                return Ok(copy);
            }
            Err(reason) if attempt >= 3 => return Err(reason),
            Err(_) => {}
        }
    }
}

/// What one read of a source whose admission digest has not been taken
/// decided ([`materialize_admitting`]).
pub(super) enum OneRead {
    /// The source, in the stamped file state, digests to the one admitted
    /// identity. It is admitted, and this is its private copy, verified like
    /// any other before it is used.
    Admitted(PrivateCopy),
    /// The source, in the stamped file state, digests to this OTHER digest.
    /// Nothing was published; the caller refuses the source from it without
    /// reading it again.
    OtherBytes(String),
    /// Nothing decided: the caller takes the separate admission digest.
    Undecided,
}

/// [`materialize`] for a source whose admission digest has not been taken
/// yet, when no copy is published: ONE read of `source` both admits it and
/// writes the copy (L14-P5).
///
/// Admission digests the source's bytes in one file state
/// (`ay_identity::digest_file`: stamp, read everything, stamp again), and
/// writing a copy reads those same bytes again to stream and digest them. On
/// a fresh cache root that was two whole reads of the 91 MB AY, one after the
/// other, ahead of the copy's first start. Here the copy is streamed from
/// `source` while `source` must stay in `source_stamp` (checked before the
/// read and after it, as `digest_file` checks, and before the digest is
/// compared), so the streamed digest is the digest of the source in that
/// state. When it equals `sha256` (the one identity the caller admits),
/// `source_admitted` runs, under the copy's writer lock, before anything else
/// can use the copy, and the copy is published and then digested again before
/// it is used, exactly as [`materialize`] does.
///
/// A source that digests to other bytes is [`OneRead::OtherBytes`]: the
/// temporary it was streamed into is removed and nothing is published, but
/// the directory named by `sha256` (empty, as a correct AY's first compile
/// would create it) stays, and the refused source's bytes were written once
/// into the cache root before the comparison could be made.
///
/// [`OneRead::Undecided`] whenever this cannot decide by itself: a copy is
/// already published, the directory is unusable, the source changed, or the
/// published copy does not verify. The caller then takes the separate
/// admission digest and calls [`materialize`], so every refusal keeps its
/// wording; nothing is published from bytes that do not digest to `sha256`.
pub(super) fn materialize_admitting(
    source: &Path,
    source_stamp: &FileStamp,
    sha256: &str,
    source_admitted: impl FnOnce(),
) -> OneRead {
    let Ok(root) = private_root(sha256) else {
        return OneRead::Undecided;
    };
    let directory = root.join(sha256);
    if ensure_private_dir(&directory).is_err() {
        return OneRead::Undecided;
    }
    let writer = copy_writer(&directory);
    let _writing = writer
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner());
    remove_stale_temporaries(&directory);
    let path = directory.join(format!("ay{}", std::env::consts::EXE_SUFFIX));
    if std::fs::symlink_metadata(&path).is_ok() {
        return OneRead::Undecided;
    }
    let published_here =
        match write_copy_from(source, Some(source_stamp), sha256, &directory, &path) {
            Ok(Written::Published) => true,
            Ok(Written::PublishedElsewhere) => false,
            Ok(Written::OtherBytes(found)) => return OneRead::OtherBytes(found),
            Err(_) => return OneRead::Undecided,
        };
    source_admitted();
    if published_here {
        begin_host_assessment_of_published(&path);
    }
    match existing(&path, sha256) {
        Ok(copy) => {
            note_published(&copy);
            OneRead::Admitted(copy)
        }
        Err(_) => OneRead::Undecided,
    }
}

/// A copy THIS process just streamed from bytes that digest to the admitted
/// identity, and published itself, is about to be digested again
/// ([`existing`]) and then started. On a host that assesses a new executable
/// at its first start ([`HOST_ASSESSES_FIRST_START`]), begin that assessment
/// now, so it overlaps the verification digest and whatever else comes before
/// the first start ([`begin_host_assessment`]). A copy another process
/// published first is not spawned before [`existing`] has checked it.
fn begin_host_assessment_of_published(path: &Path) {
    crate::process_cost::mark("ay_copy_published");
    if HOST_ASSESSES_FIRST_START {
        let _ = begin_host_assessment(path);
    }
}

/// The directory the copy of the bytes with digest `sha256` is published in.
#[cfg(test)]
pub(super) fn copy_directory(sha256: &str) -> Result<PathBuf, String> {
    Ok(private_root(sha256)?.join(sha256))
}

/// The in-process writer lock of one copy directory (one per admitted
/// digest). The map holds one entry per digest this process materializes.
fn copy_writer(directory: &Path) -> std::sync::Arc<std::sync::Mutex<()>> {
    type Writers = std::collections::HashMap<PathBuf, std::sync::Arc<std::sync::Mutex<()>>>;
    static WRITERS: std::sync::OnceLock<std::sync::Mutex<Writers>> = std::sync::OnceLock::new();
    let mut writers = WRITERS
        .get_or_init(Default::default)
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner());
    std::sync::Arc::clone(writers.entry(directory.to_path_buf()).or_default())
}

/// Whether this host holds the FIRST start of a new executable file while it
/// assesses the file, so that a first start is worth making before any solver
/// deadline starts ([`claim_first_start`]).
///
/// macOS does: for an ad hoc signed binary that carries provenance, as a copy
/// written here does, `syspolicyd` has XProtect scan the whole file before
/// `exec` returns, and it runs those scans one at a time for every process on
/// the host. Measured on the first start of a new copy: 0.67-1.0 s for the
/// 91 MB Trust 9192 AY (M4 Max, macOS 26.6.2, 2026-09-28, lightly loaded),
/// 8 ms after; 1.6-11.8 s for the 158 MB toolchain AY 0.27.0 build 10934 at
/// load average 34-54 and once 32.2 s at load 43 during a compile (maintainer's
/// macOS arm64 host, 2026-09-27), 0.01-0.04 s for later starts. Concurrent
/// starts of one new file share one scan. No other host is known to do this,
/// so nowhere else is a first start made on its own.
pub(super) const HOST_ASSESSES_FIRST_START: bool = cfg!(target_os = "macos");

/// Begin the host's first-start assessment of the executable at `path`
/// without running any of it (macOS; a no-op elsewhere). Whether a suspended
/// child was started, seen not to have run, and then killed and reaped.
///
/// The file is started SUSPENDED (`POSIX_SPAWN_START_SUSPENDED`, with every
/// descriptor closed in the child, an empty environment and the argument
/// `--version`) and the child is killed with `SIGKILL` and reaped at once:
/// not one instruction of the file runs, so this relies on nothing about its
/// bytes and establishes nothing. What it does is make `syspolicyd` start
/// assessing the file, and that assessment runs to its end after the child
/// is gone. Measured on the Trust 9192 AY (91 MB; M4 Max, macOS 26.6.2,
/// 2026-09-29): a real first start made 0.5 s after such a spawn took
/// 0.32-0.33 s, against 0.80-0.82 s for a fresh copy started cold, and a real
/// start made immediately after it took the whole assessment, as a cold one
/// does. The first start (`ay_identity::first_start`) is still made before
/// any solver deadline; it just waits for less of the assessment.
///
/// That the child has not run is checked, not assumed, before the kill
/// ([`spawned_child_has_not_run`]: stopped, with no user time). A child that
/// fails the check still has kill and reap attempted. Success requires a
/// successful kill and a reap reporting `SIGKILL`; any check or cleanup
/// failure prevents further assessment spawns in this process.
///
/// The spawn and bounded cleanup attempt run under [`ASSESSMENT_SPAWNS`],
/// which a registered `atexit` hook also takes. Normal exit waits for that
/// attempt, and no spawn starts once exit has begun. A cleanup failure is
/// reported and disables later assessment spawns; successful cleanup is not
/// guaranteed for every OS outcome.
#[cfg(target_os = "macos")]
pub(super) fn begin_host_assessment(path: &Path) -> bool {
    use std::os::unix::ffi::OsStrExt;

    extern "C" fn close_assessment_spawns() {
        *ASSESSMENT_SPAWNS
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner) = true;
    }
    static REGISTER_EXIT_HOOK: std::sync::Once = std::sync::Once::new();
    REGISTER_EXIT_HOOK.call_once(|| {
        // SAFETY: `close_assessment_spawns` is an `extern "C" fn()` that only
        // takes a process-lifetime mutex, as `atexit` handlers may.
        unsafe {
            libc::atexit(close_assessment_spawns);
        }
    });

    let Ok(program) = std::ffi::CString::new(path.as_os_str().as_bytes()) else {
        return false;
    };
    let version = c"--version";
    let argv: [*mut libc::c_char; 3] = [
        program.as_ptr().cast_mut(),
        version.as_ptr().cast_mut(),
        std::ptr::null_mut(),
    ];
    let envp: [*mut libc::c_char; 1] = [std::ptr::null_mut()];

    let mut closing = ASSESSMENT_SPAWNS
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    if *closing {
        return false;
    }
    let mut attributes = std::mem::MaybeUninit::<libc::posix_spawnattr_t>::uninit();
    // SAFETY: `attributes` is writable storage for one `posix_spawnattr_t`,
    // which `posix_spawnattr_init` initializes on success.
    if unsafe { libc::posix_spawnattr_init(attributes.as_mut_ptr()) } != 0 {
        return false;
    }
    // SAFETY: initialized just above.
    let mut attributes = unsafe { attributes.assume_init() };
    let flags = libc::POSIX_SPAWN_START_SUSPENDED | libc::POSIX_SPAWN_CLOEXEC_DEFAULT;
    let mut pid: libc::pid_t = 0;
    // SAFETY: `attributes` is initialized; `program`, `argv` and `envp` are
    // NUL-terminated and outlive the call; no file actions are passed.
    let spawned = unsafe {
        libc::posix_spawnattr_setflags(&mut attributes, flags as libc::c_short) == 0
            && libc::posix_spawn(
                &mut pid,
                program.as_ptr(),
                std::ptr::null(),
                &attributes,
                argv.as_ptr(),
                envp.as_ptr(),
            ) == 0
    };
    // SAFETY: `attributes` was initialized by `posix_spawnattr_init`.
    unsafe {
        libc::posix_spawnattr_destroy(&mut attributes);
    }
    if !spawned || pid <= 0 {
        return false;
    }
    crate::process_cost::note_assessment_spawn();
    #[cfg(test)]
    if let Some(hold) = HOLD_SPAWNED_CHILD.with(std::cell::Cell::take) {
        std::thread::sleep(hold);
    }
    let unrun = spawned_child_has_not_run(pid);
    // SAFETY: `pid` is this process's own child, created above.
    let killed = unsafe { libc::kill(pid, libc::SIGKILL) == 0 };
    // A killed suspended child is reaped at once; the deadline only keeps a
    // host that never delivers the kill from holding exit (which waits on
    // this lock) for longer than it.
    let deadline = std::time::Instant::now() + std::time::Duration::from_secs(2);
    let reaped = loop {
        let mut status = 0;
        // SAFETY: `status` is writable; `pid` is this process's child.
        let waited = unsafe { libc::waitpid(pid, &mut status, libc::WNOHANG) };
        let interrupted =
            waited < 0 && std::io::Error::last_os_error().raw_os_error() == Some(libc::EINTR);
        if waited != 0 && !interrupted {
            break waited == pid
                && libc::WIFSIGNALED(status)
                && libc::WTERMSIG(status) == libc::SIGKILL;
        }
        if std::time::Instant::now() >= deadline {
            break false;
        }
        std::thread::sleep(std::time::Duration::from_micros(200));
    };
    if !unrun || !killed || !reaped {
        *closing = true;
        drop(closing);
        crate::process_cost::mark(if !unrun {
            "ay_assessment_spawn_not_suspended"
        } else {
            "ay_assessment_cleanup_incomplete"
        });
        return false;
    }
    drop(closing);
    crate::process_cost::mark("ay_assessment_begun");
    true
}

#[cfg(not(target_os = "macos"))]
pub(super) fn begin_host_assessment(_path: &Path) -> bool {
    false
}

/// Whether this process's child `pid`, just spawned with
/// `POSIX_SPAWN_START_SUSPENDED`, has not run: the kernel reports it stopped
/// (`SSTOP`, which it sets before `posix_spawn` returns for a suspended
/// spawn; an ordinary child is `SRUN`) and it has spent no time in user mode.
/// `false` whenever either cannot be read.
#[cfg(target_os = "macos")]
fn spawned_child_has_not_run(pid: libc::pid_t) -> bool {
    let mut info = std::mem::MaybeUninit::<libc::proc_bsdinfo>::zeroed();
    let size = std::mem::size_of::<libc::proc_bsdinfo>();
    let Ok(size_arg) = libc::c_int::try_from(size) else {
        return false;
    };
    // SAFETY: `info` is writable storage of `size` bytes, the size passed.
    let filled = unsafe {
        libc::proc_pidinfo(
            pid,
            libc::PROC_PIDTBSDINFO,
            0,
            info.as_mut_ptr().cast(),
            size_arg,
        )
    };
    if filled != size_arg {
        return false;
    }
    // SAFETY: zero-initialized, and every field is an integer or an array
    // of integers, which the kernel filled.
    let info = unsafe { info.assume_init() };
    if info.pbi_status != libc::SSTOP {
        return false;
    }
    let mut usage = std::mem::MaybeUninit::<libc::rusage_info_v0>::zeroed();
    // SAFETY: `usage` is writable storage for one `rusage_info_v0`, the
    // flavor requested (the binding types the buffer as `*mut rusage_info_t`).
    let read =
        unsafe { libc::proc_pid_rusage(pid, libc::RUSAGE_INFO_V0, usage.as_mut_ptr().cast()) };
    if read != 0 {
        return false;
    }
    // SAFETY: zero-initialized integers, filled by the kernel.
    let usage = unsafe { usage.assume_init() };
    usage.ri_user_time == 0
}

/// Set once the process has begun to exit, or once a spawned child was not
/// seen suspended and unrun, or its successful kill and reap could not be
/// confirmed: no assessment spawn starts after that. Held across each spawn
/// and its kill ([`begin_host_assessment`]).
#[cfg(target_os = "macos")]
static ASSESSMENT_SPAWNS: std::sync::Mutex<bool> = std::sync::Mutex::new(false);

#[cfg(all(test, target_os = "macos"))]
thread_local! {
    /// Test-only: how long this thread's next assessment spawn waits between
    /// the spawn and the check that its child has not run.
    static HOLD_SPAWNED_CHILD: std::cell::Cell<Option<std::time::Duration>> =
        const { std::cell::Cell::new(None) };
}

/// Test-only: make this thread's next [`begin_host_assessment`] wait `hold`
/// before it checks and kills its child, long enough for a child that was
/// NOT started suspended to run its file (start `sh`, write a marker, exit).
#[cfg(all(test, target_os = "macos"))]
pub(super) fn hold_next_spawned_child(hold: std::time::Duration) {
    HOLD_SPAWNED_CHILD.with(|next| next.set(Some(hold)));
}

/// Name, beside a copy, of the marker recording that a first start of that
/// copy's exact file state has completed in some process.
const FIRST_START_MARKER: &str = "ay.first-start";

/// Where a copy stands with respect to its first start, in this process.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum FirstStart {
    /// No completed first start is known: this process published the copy,
    /// or found it without a marker for its file state.
    Pending,
    /// A thread of this process is making it now.
    Starting,
    /// Made (or stopped at its allowance), here or, per the marker, elsewhere.
    Made,
}

struct FirstStartEntry {
    stamp: FileStamp,
    /// Published during this process (by it, or by a concurrent process it
    /// raced), rather than found already published.
    published_here: bool,
    state: FirstStart,
    /// Threads that have waited for a first start another thread was making.
    #[cfg(test)]
    waits: usize,
}

/// The one registry of copies whose first start is still to be made. It is
/// fed by [`materialize`] (a copy it publishes, or one it finds without a
/// completed-first-start marker) and consumed by `ay_identity::first_start`,
/// which makes that start once, before a solver deadline starts, or earlier
/// on the identity-warm thread for a copy this process published. A thread
/// that needs the start while another is making it waits for it
/// ([`await_first_start`]) instead of paying the rest of it inside its own
/// solver deadline.
struct FirstStarts {
    entries: std::sync::Mutex<std::collections::HashMap<PathBuf, FirstStartEntry>>,
    changed: std::sync::Condvar,
}

fn first_starts() -> &'static FirstStarts {
    static REGISTRY: std::sync::OnceLock<FirstStarts> = std::sync::OnceLock::new();
    REGISTRY.get_or_init(|| FirstStarts {
        entries: std::sync::Mutex::new(std::collections::HashMap::new()),
        changed: std::sync::Condvar::new(),
    })
}

fn first_start_entries()
-> std::sync::MutexGuard<'static, std::collections::HashMap<PathBuf, FirstStartEntry>> {
    first_starts()
        .entries
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner)
}

/// A copy this process just published has had no start anywhere.
fn note_published(copy: &PrivateCopy) {
    first_start_entries().insert(
        copy.path.clone(),
        FirstStartEntry {
            stamp: copy.stamp.clone(),
            published_here: true,
            state: FirstStart::Pending,
            #[cfg(test)]
            waits: 0,
        },
    );
}

/// A copy found already published: its first start is pending unless a
/// marker records a completed first start of this exact file state. Read once
/// per copy state and process; a copy this process already knows is kept.
fn note_found(copy: &PrivateCopy) {
    fn known(
        entries: &std::collections::HashMap<PathBuf, FirstStartEntry>,
        copy: &PrivateCopy,
    ) -> bool {
        entries
            .get(&copy.path)
            .is_some_and(|entry| entry.stamp == copy.stamp)
    }
    if known(&first_start_entries(), copy) {
        return;
    }
    let made = HOST_ASSESSES_FIRST_START && first_start_recorded(copy);
    let mut entries = first_start_entries();
    if known(&entries, copy) {
        return;
    }
    entries.insert(
        copy.path.clone(),
        FirstStartEntry {
            stamp: copy.stamp.clone(),
            published_here: false,
            state: if made {
                FirstStart::Made
            } else {
                FirstStart::Pending
            },
            #[cfg(test)]
            waits: 0,
        },
    );
}

/// What a caller of [`claim_first_start`] is to do.
pub(super) enum FirstStartClaim {
    /// Nothing: no first start is pending for this copy (or none this caller
    /// may take).
    Nothing,
    /// Make the first start now, then [`FirstStartGuard::finish`] it.
    Make(FirstStartGuard),
    /// Another thread is making it: [`await_first_start`].
    Wait,
}

/// Claim the pending first start of `copy`. `published_only` restricts the
/// claim to a copy published during this process (the identity-warm thread's
/// early start, which never waits for another thread's).
pub(super) fn claim_first_start(copy: &PrivateCopy, published_only: bool) -> FirstStartClaim {
    let mut entries = first_start_entries();
    let Some(entry) = entries
        .get_mut(&copy.path)
        .filter(|entry| entry.stamp == copy.stamp)
    else {
        return FirstStartClaim::Nothing;
    };
    match entry.state {
        FirstStart::Pending if entry.published_here || !published_only => {
            entry.state = FirstStart::Starting;
            FirstStartClaim::Make(FirstStartGuard {
                copy: copy.clone(),
                completed: false,
            })
        }
        FirstStart::Starting if !published_only => FirstStartClaim::Wait,
        _ => FirstStartClaim::Nothing,
    }
}

/// Wait, at most `limit`, while another thread makes `copy`'s first start.
/// That start is itself stopped at its allowance, so the limit only guards a
/// thread that never finishes it.
pub(super) fn await_first_start(copy: &PrivateCopy, limit: std::time::Duration) {
    let registry = first_starts();
    let entries = first_start_entries();
    #[cfg(test)]
    let entries = {
        let mut entries = entries;
        if let Some(entry) = entries.get_mut(&copy.path) {
            entry.waits += 1;
        }
        entries
    };
    let _ = registry
        .changed
        .wait_timeout_while(entries, limit, |entries| {
            entries.get(&copy.path).is_some_and(|entry| {
                entry.stamp == copy.stamp && entry.state == FirstStart::Starting
            })
        });
}

/// The claim on one copy's first start. Dropping it (also by unwinding)
/// marks the start made and wakes waiters; only [`Self::finish`] with a start
/// that completed records it for other processes.
pub(super) struct FirstStartGuard {
    copy: PrivateCopy,
    completed: bool,
}

impl FirstStartGuard {
    /// The first start is over. `completed` is whether it ran to its exit
    /// (whatever its status): only then has the host finished assessing the
    /// file, and only then is that recorded beside the copy for other
    /// processes. A start stopped at its allowance still counts as made in
    /// this process, so no later command repeats the allowance.
    pub(super) fn finish(mut self, completed: bool) {
        self.completed = completed;
    }
}

impl Drop for FirstStartGuard {
    fn drop(&mut self) {
        if self.completed {
            record_first_start(&self.copy);
        }
        let registry = first_starts();
        if let Some(entry) = first_start_entries()
            .get_mut(&self.copy.path)
            .filter(|entry| entry.stamp == self.copy.stamp)
        {
            entry.state = FirstStart::Made;
        }
        registry.changed.notify_all();
    }
}

/// The marker's contents for a copy's file state: the fields a replaced or
/// rewritten file cannot keep (device, inode, size, change time).
fn first_start_marker_text(stamp: &FileStamp) -> String {
    #[cfg(unix)]
    let text = format!(
        "{} {} {} {} {}\n",
        stamp.device, stamp.inode, stamp.len, stamp.ctime.0, stamp.ctime.1
    );
    #[cfg(not(unix))]
    let text = format!("{} {:?}\n", stamp.len, stamp.modified);
    text
}

/// Whether the marker beside `copy` records a completed first start of its
/// current file state. A missing, unreadable, oversized or stale marker
/// records nothing. The marker decides only whether one more `--version`
/// start is made before a deadline: it is never evidence about AY's bytes,
/// which every start re-checks.
fn first_start_recorded(copy: &PrivateCopy) -> bool {
    use std::io::Read;
    let Some(marker) = copy.path.parent().map(|dir| dir.join(FIRST_START_MARKER)) else {
        return false;
    };
    let mut options = std::fs::OpenOptions::new();
    options.read(true);
    #[cfg(unix)]
    {
        use std::os::unix::fs::OpenOptionsExt;
        options.custom_flags(libc::O_NOFOLLOW);
    }
    let Ok(file) = options.open(&marker) else {
        return false;
    };
    let mut text = String::new();
    if file.take(256).read_to_string(&mut text).is_err() {
        return false;
    }
    text == first_start_marker_text(&copy.stamp)
}

/// Record, beside `copy`, that a first start of its current file state has
/// completed. Written to a temporary and renamed into place, so a reader sees
/// a whole marker or none; a failure only means a later process makes one
/// more first start.
fn record_first_start(copy: &PrivateCopy) {
    let Some(directory) = copy.path.parent() else {
        return;
    };
    // The temporary prefix is the copy's own, so one a killed writer leaves
    // is removed by the same stale-temporary sweep.
    let Ok(mut temporary) = tempfile::Builder::new()
        .prefix(TEMPORARY_PREFIX)
        .tempfile_in(directory)
    else {
        return;
    };
    if temporary
        .write_all(first_start_marker_text(&copy.stamp).as_bytes())
        .is_err()
    {
        return;
    }
    let _ = temporary.persist(directory.join(FIRST_START_MARKER));
}

/// Forget what this process knows about `path`'s first start, as a new
/// process would.
#[cfg(test)]
pub(super) fn forget_first_start(path: &Path) {
    first_start_entries().remove(path);
}

/// Whether this process knows `copy`'s first start to be made.
#[cfg(test)]
pub(super) fn first_start_made(copy: &PrivateCopy) -> bool {
    first_start_entries()
        .get(&copy.path)
        .is_some_and(|entry| entry.stamp == copy.stamp && entry.state == FirstStart::Made)
}

/// How many threads have waited for `copy`'s first start.
#[cfg(test)]
pub(super) fn first_start_waits(copy: &PrivateCopy) -> usize {
    first_start_entries()
        .get(&copy.path)
        .map_or(0, |entry| entry.waits)
}

/// Whether a thread of this process is making `copy`'s first start now.
#[cfg(test)]
pub(super) fn first_start_in_progress(copy: &PrivateCopy) -> bool {
    first_start_entries()
        .get(&copy.path)
        .is_some_and(|entry| entry.stamp == copy.stamp && entry.state == FirstStart::Starting)
}

/// Remove the temporaries in `directory` (one `<sha256>` directory) whose
/// writer is provably gone, so a copy interrupted by a killed process does not
/// stay there forever. A temporary is removed only when every condition holds:
///
/// * its name has [`TEMPORARY_PREFIX`] (never the published `ay`);
/// * it is a regular file owned by this user, not a symlink (never followed:
///   it is opened with `O_NOFOLLOW` and must be the same inode that was
///   examined);
/// * it is older than [`STALE_TEMPORARY_AGE`], so a writer that has created
///   it but not yet locked it keeps it;
/// * its lock is free: every writer holds an exclusive lock on its temporary
///   until it publishes or exits, and the kernel releases it only then.
///
/// At most [`STALE_TEMPORARY_SCAN_LIMIT`] names are examined per call, and
/// every failure leaves the file in place.
#[cfg(unix)]
pub(super) fn remove_stale_temporaries(directory: &Path) {
    use std::os::unix::fs::{MetadataExt, OpenOptionsExt};

    let Ok(entries) = std::fs::read_dir(directory) else {
        return;
    };
    let temporaries = entries.filter_map(Result::ok).filter(|entry| {
        entry
            .file_name()
            .as_encoded_bytes()
            .starts_with(TEMPORARY_PREFIX.as_bytes())
    });
    for entry in temporaries.take(STALE_TEMPORARY_SCAN_LIMIT) {
        let path = entry.path();
        let Ok(examined) = std::fs::symlink_metadata(&path) else {
            continue;
        };
        let stale = examined
            .modified()
            .ok()
            .and_then(|modified| modified.elapsed().ok())
            .is_some_and(|age| age >= STALE_TEMPORARY_AGE);
        if !examined.file_type().is_file() || examined.uid() != current_uid() || !stale {
            continue;
        }
        let Ok(file) = std::fs::OpenOptions::new()
            .read(true)
            .custom_flags(libc::O_NOFOLLOW)
            .open(&path)
        else {
            continue;
        };
        let same = file
            .metadata()
            .is_ok_and(|opened| (opened.dev(), opened.ino()) == (examined.dev(), examined.ino()));
        // A held lock is a live writer; an error is not proof of anything.
        if same && file.try_lock().is_ok() {
            let _ = std::fs::remove_file(&path);
        }
    }
}

#[cfg(not(unix))]
pub(super) fn remove_stale_temporaries(_directory: &Path) {}

fn existing(path: &Path, sha256: &str) -> Result<PrivateCopy, String> {
    check_private_file(path)?;
    let (found, stamp) = digest_file(path)?;
    if found != sha256 {
        return Err(format!(
            "{} digests to {found}, not {sha256}",
            path.display()
        ));
    }
    let copy = PrivateCopy {
        path: path.to_path_buf(),
        stamp,
    };
    copy.verify(sha256)?;
    Ok(copy)
}

/// Copy `source`'s bytes (which must digest to `sha256`) to a temporary file
/// in `directory`, make it `0500`, and publish it at `path` without replacing
/// anything already there. `Ok(true)` when this process published it,
/// `Ok(false)` when another process published a copy there first (the caller
/// checks that one).
pub(super) fn write_copy(
    source: &Path,
    sha256: &str,
    directory: &Path,
    path: &Path,
) -> Result<bool, String> {
    match write_copy_from(source, None, sha256, directory, path)? {
        Written::Published => Ok(true),
        Written::PublishedElsewhere => Ok(false),
        Written::OtherBytes(found) => Err(format!(
            "{} changed after admission: it now digests to {found}, not {sha256}",
            source.display()
        )),
    }
}

/// What [`write_copy_from`] did with the bytes it streamed.
enum Written {
    /// They digest to `sha256`, and this process published them at `path`.
    Published,
    /// They digest to `sha256`, but another process published a copy at
    /// `path` first; these were discarded.
    PublishedElsewhere,
    /// They digest to this, not `sha256`; nothing was published.
    OtherBytes(String),
}

/// [`write_copy`], and with `Some(source_stamp)` also require `source` to be
/// in that file state before it is opened and after it has been read, as
/// `ay_identity::digest_file` requires of the file it digests. Both checks
/// come before the digest is compared, so any digest this reports, equal to
/// `sha256` or not, is the digest of `source` in that state.
fn write_copy_from(
    source: &Path,
    source_stamp: Option<&FileStamp>,
    sha256: &str,
    directory: &Path,
    path: &Path,
) -> Result<Written, String> {
    use sha2::{Digest, Sha256};
    use std::io::Read;

    let source_unchanged =
        || source_stamp.is_none_or(|stamp| file_stamp(source).as_ref() == Some(stamp));
    if !source_unchanged() {
        return Err(format!("{} changed before it was read", source.display()));
    }
    let mut input = std::fs::File::open(source)
        .map_err(|error| format!("cannot read {}: {error}", source.display()))?;
    let mut temporary = tempfile::Builder::new()
        .prefix(TEMPORARY_PREFIX)
        .tempfile_in(directory)
        .map_err(|error| format!("cannot create a copy in {}: {error}", directory.display()))?;
    // Held until this process publishes the copy or exits (the kernel drops
    // it even on SIGKILL): a temporary whose lock is free has no live writer
    // ([`remove_stale_temporaries`]).
    temporary
        .as_file()
        .lock()
        .map_err(|error| format!("cannot lock the copy being written: {error}"))?;
    // The bytes are read once, in bounded chunks, and each chunk is digested
    // and then written, so the digest is over exactly the bytes written and a
    // source replaced after admission cannot leak in. Streaming keeps the
    // copy's memory at one chunk: reading the whole AY first held ~91 MB
    // (Trust 9192) at the peak of every compile that populated the cache.
    let mut hasher = Sha256::new();
    let mut buffer = vec![0u8; COPY_CHUNK_BYTES];
    let mut total = 0u64;
    loop {
        let read = input
            .read(&mut buffer)
            .map_err(|error| format!("cannot read {}: {error}", source.display()))?;
        let Some(chunk) = buffer.get(..read) else {
            return Err(format!("{} read past its buffer", source.display()));
        };
        if chunk.is_empty() {
            break;
        }
        hasher.update(chunk);
        total = total.saturating_add(chunk.len() as u64);
        temporary
            .write_all(chunk)
            .map_err(|error| format!("cannot write the copy: {error}"))?;
    }
    crate::process_cost::note_executable_digest(total, "digest_ay_copy_streamed");
    #[cfg(test)]
    note_copy_written(directory);
    #[cfg(test)]
    super::after_whole_read(source);
    // The temporary is removed when it is dropped; nothing is published.
    if !source_unchanged() {
        return Err(format!("{} changed while it was read", source.display()));
    }
    let found = format!("{:x}", hasher.finalize());
    if found != sha256 {
        return Ok(Written::OtherBytes(found));
    }
    temporary
        .as_file()
        .sync_all()
        .map_err(|error| format!("cannot write the copy: {error}"))?;
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        temporary
            .as_file()
            .set_permissions(std::fs::Permissions::from_mode(0o500))
            .map_err(|error| format!("cannot make the copy 0500: {error}"))?;
    }
    match temporary.persist_noclobber(path) {
        Ok(_) => Ok(Written::Published),
        // Another process published the same digest first; the caller checks it.
        Err(error) if error.error.kind() == std::io::ErrorKind::AlreadyExists => {
            Ok(Written::PublishedElsewhere)
        }
        Err(error) => Err(format!(
            "cannot publish the copy at {}: {}",
            path.display(),
            error.error
        )),
    }
}

/// How many copies [`write_copy`] streamed into each directory, so the
/// one-writer property can be asserted. Test-only; production never reads it.
#[cfg(test)]
fn copies_written() -> &'static std::sync::Mutex<std::collections::HashMap<PathBuf, usize>> {
    static COUNTS: std::sync::OnceLock<
        std::sync::Mutex<std::collections::HashMap<PathBuf, usize>>,
    > = std::sync::OnceLock::new();
    COUNTS.get_or_init(Default::default)
}

#[cfg(test)]
fn note_copy_written(directory: &Path) {
    *copies_written()
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner())
        .entry(directory.to_path_buf())
        .or_insert(0) += 1;
}

#[cfg(test)]
pub(super) fn copies_written_into(directory: &Path) -> usize {
    copies_written()
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner())
        .get(directory)
        .copied()
        .unwrap_or(0)
}
