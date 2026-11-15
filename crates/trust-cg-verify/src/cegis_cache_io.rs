// trust-cg-verify/cegis_cache_io.rs - Host-shared CEGIS cache backend
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Host-shared CEGIS cache backend.
//!
//! [`SharedCegisCache`] stores CEGIS pass payloads in an on-disk
//! [`trust_cg_opt::FileCache`] so separate worktrees on the same host can reuse
//! solver results. The cache is advisory: construction falls back to an
//! in-memory cache when the root is unusable, and write failures never fail
//! compilation.
//!
//! Entries carry no MAC, so the root must be private. On Unix a root is used
//! only if the directory it resolves to is owned by the current user and
//! writable by no one else; any other root, in particular a
//! `/tmp/.trust-cg-cegis-cache` another user created, is refused with a
//! warning and the process uses an in-memory cache. Directories the cache
//! creates are `0700` and its files `0600`. The pass does not trust entries
//! in a private root either: replay applies a recorded rewrite only if the
//! search's matcher rebuilds it exactly (see `cegis_pass`).

use std::io;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Arc, Once, OnceLock};
use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};

use trust_cg_opt::cache::{
    CacheBackend, CacheKey, FileCache, InMemoryCache, create_private_dir_all, create_private_file,
};

/// Default directory name used under the chosen cache root.
pub const CEGIS_CACHE_DIR_NAME: &str = "trust-cg-cegis";

/// Environment variable that overrides the default cache root.
pub const CEGIS_CACHE_ENV: &str = "TRUST_CG_CEGIS_CACHE";

/// Max time a writer waits for the per-key lockfile before skipping a write.
pub const WRITE_LOCK_WAIT: Duration = Duration::from_secs(5);

/// Polling interval for the writer-side lock retry loop.
pub const WRITE_LOCK_POLL: Duration = Duration::from_millis(25);

/// Lockfiles older than this are treated as stale and may be removed.
pub const STALE_LOCK_AGE: Duration = Duration::from_secs(30);

static ROOT_PROBE_COUNTER: AtomicU64 = AtomicU64::new(0);

/// Resolve the default shared cache root.
///
/// First match wins:
///
/// 1. `$TRUST_CG_CEGIS_CACHE`
/// 2. `<user cache>/trust-cg-cegis`, the user cache by the one rule every
///    trust-cg cache root is resolved by
///    (`trust_cg_process_env::private_fs::user_cache_base`: an absolute
///    `$XDG_CACHE_HOME`, else an absolute `$HOME/.cache`; an empty or
///    relative value is ignored, never read against the working directory)
/// 3. `std::env::temp_dir()/.trust-cg-cegis-cache`
///
/// The last is a path every user of the host shares. [`SharedCegisCache`]
/// uses it only if the current user owns it and no one else can write it.
pub fn default_cache_root() -> PathBuf {
    if let Ok(raw) = crate::env_lock::var(CEGIS_CACHE_ENV) {
        let trimmed = raw.trim();
        if !trimmed.is_empty() {
            return PathBuf::from(trimmed);
        }
    }

    if let Ok(base) = trust_cg_process_env::private_fs::current_user_cache_base() {
        return base.join(CEGIS_CACHE_DIR_NAME);
    }

    std::env::temp_dir().join(".trust-cg-cegis-cache")
}

/// Verify that `root` is a directory we can create and remove files in.
///
/// `FileCache::new` only proves that `create_dir_all(root)` succeeded. An
/// existing read-only directory also passes that check, then fails later on
/// every write. This probe lets [`SharedCegisCache::is_on_disk`] report the
/// actual backend choice at construction time.
fn validate_writable_root(root: &Path) -> io::Result<()> {
    if !root.is_dir() {
        return Err(io::Error::other(format!(
            "cache root is not a directory: {}",
            root.display()
        )));
    }

    let nonce = ROOT_PROBE_COUNTER.fetch_add(1, Ordering::Relaxed);
    let nanos = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|d| d.as_nanos())
        .unwrap_or(0);
    let probe = root.join(format!(
        ".trust-cg-cegis-write-probe.{}.{}.{}",
        std::process::id(),
        nonce,
        nanos
    ));

    let file = create_private_file(&probe)?;
    drop(file);
    std::fs::remove_file(&probe)?;
    Ok(())
}

/// Why a cache root was not used.
enum RootRefusal {
    /// The directory could not be created, resolved or written.
    Unusable(io::Error),
    /// The directory is not private to the current user.
    #[cfg_attr(not(unix), allow(dead_code))]
    Untrusted(String),
}

/// The effective user id new files are created under.
#[cfg(unix)]
fn current_uid() -> u32 {
    // SAFETY: geteuid takes no arguments, cannot fail and touches no memory
    // the caller owns.
    unsafe { libc::geteuid() }
}

/// Require the directory `root` to be private to the user `uid`: owned by
/// `uid` and neither group- nor world-writable. A group or other user who
/// can write the root can plant or replace entries (or, for a sticky
/// world-writable directory such as `/tmp`, own it in the first place).
#[cfg(unix)]
fn check_private_root(root: &Path, uid: u32) -> Result<(), RootRefusal> {
    use std::os::unix::fs::MetadataExt;
    let metadata = std::fs::metadata(root).map_err(RootRefusal::Unusable)?;
    if !metadata.is_dir() {
        return Err(RootRefusal::Unusable(io::Error::other(format!(
            "cache root is not a directory: {}",
            root.display()
        ))));
    }
    if metadata.uid() != uid {
        return Err(RootRefusal::Untrusted(format!(
            "owned by uid {}, not the current user (uid {uid})",
            metadata.uid()
        )));
    }
    let mode = metadata.mode() & 0o7777;
    if mode & 0o022 != 0 {
        return Err(RootRefusal::Untrusted(format!(
            "mode {mode:04o} lets the group or other users write it"
        )));
    }
    Ok(())
}

/// Create `root` if missing (`0700`), resolve it, require the resolved
/// directory to be private and writable, and open the cache there. Later
/// reads and writes use the resolved path, so re-pointing a symlink in the
/// configured path after this check does not redirect them.
fn open_private_root(root: &Path) -> Result<FileCache, RootRefusal> {
    create_private_dir_all(root).map_err(RootRefusal::Unusable)?;
    let resolved = std::fs::canonicalize(root).map_err(RootRefusal::Unusable)?;
    #[cfg(unix)]
    check_private_root(&resolved, current_uid())?;
    validate_writable_root(&resolved).map_err(RootRefusal::Unusable)?;
    FileCache::new(resolved).map_err(RootRefusal::Unusable)
}

/// RAII guard for a per-key writer lockfile.
struct WriteLock {
    path: PathBuf,
}

impl WriteLock {
    fn try_acquire(path: PathBuf) -> io::Result<Option<Self>> {
        let deadline = Instant::now() + WRITE_LOCK_WAIT;
        loop {
            match create_private_file(&path) {
                Ok(_file) => return Ok(Some(Self { path })),
                Err(e) if e.kind() == io::ErrorKind::AlreadyExists => {
                    if stale_lock(&path) {
                        let _ = std::fs::remove_file(&path);
                        continue;
                    }
                    if Instant::now() >= deadline {
                        return Ok(None);
                    }
                    std::thread::sleep(WRITE_LOCK_POLL);
                }
                Err(e) => return Err(e),
            }
        }
    }
}

impl Drop for WriteLock {
    fn drop(&mut self) {
        let _ = std::fs::remove_file(&self.path);
    }
}

fn stale_lock(path: &Path) -> bool {
    match std::fs::metadata(path).and_then(|md| md.modified()) {
        Ok(mtime) => mtime
            .elapsed()
            .map(|age| age >= STALE_LOCK_AGE)
            .unwrap_or(false),
        Err(_) => false,
    }
}

/// [`CacheBackend`] that persists CEGIS entries under a host-shared root.
pub struct SharedCegisCache {
    inner: Backend,
    on_disk: bool,
    root: PathBuf,
}

enum Backend {
    Disk { file: FileCache },
    InMemory { mem: InMemoryCache },
}

impl SharedCegisCache {
    /// Construct a cache rooted at [`default_cache_root`].
    pub fn new_default() -> Self {
        Self::new_at(default_cache_root())
    }

    /// Construct a cache rooted at `root`.
    ///
    /// A missing root is created `0700`. If the directory cannot be created
    /// or cannot accept a write probe, or (on Unix) the directory it resolves
    /// to is not owned by the current user or is group- or world-writable,
    /// the cache degrades to an in-memory backend and logs the reason once.
    pub fn new_at(root: impl Into<PathBuf>) -> Self {
        let root = root.into();
        match open_private_root(&root) {
            Ok(file) => Self {
                inner: Backend::Disk { file },
                on_disk: true,
                root,
            },
            Err(refusal) => {
                match refusal {
                    RootRefusal::Unusable(e) => log_fallback_once(&root, &e),
                    RootRefusal::Untrusted(reason) => log_untrusted_once(&root, &reason),
                }
                Self {
                    inner: Backend::InMemory {
                        mem: InMemoryCache::new(),
                    },
                    on_disk: false,
                    root,
                }
            }
        }
    }

    /// Whether this cache is backed by the shared on-disk root.
    pub fn is_on_disk(&self) -> bool {
        self.on_disk
    }

    /// Intended cache root. On fallback, this is the path that was attempted.
    pub fn root(&self) -> &Path {
        &self.root
    }

    /// Build an `Arc<dyn CacheBackend>` wired for the default root.
    ///
    /// The root path is resolved now, on the calling thread, so a
    /// thread-local `TRUST_CG_CEGIS_CACHE` override in scope applies; the
    /// directory is created and judged on the first read or write (see
    /// [`Self::arc_at`]).
    pub fn default_arc() -> Arc<dyn CacheBackend> {
        Self::arc_at(default_cache_root())
    }

    /// Build an `Arc<dyn CacheBackend>` at an explicit root, opened by
    /// [`Self::new_at`] on its first read or write. Every compiler pipeline
    /// builds one whether or not CEGIS runs, so a compile without CEGIS never
    /// creates the directory or logs a refused root.
    pub fn arc_at(root: impl Into<PathBuf>) -> Arc<dyn CacheBackend> {
        Arc::new(DeferredSharedCegisCache {
            root: root.into(),
            cache: OnceLock::new(),
        })
    }
}

/// A [`SharedCegisCache`] opened at `root` on first use.
struct DeferredSharedCegisCache {
    root: PathBuf,
    cache: OnceLock<SharedCegisCache>,
}

impl DeferredSharedCegisCache {
    fn cache(&self) -> &SharedCegisCache {
        self.cache
            .get_or_init(|| SharedCegisCache::new_at(self.root.clone()))
    }
}

impl CacheBackend for DeferredSharedCegisCache {
    fn get(&self, key: &CacheKey) -> Option<Vec<u8>> {
        self.cache().get(key)
    }

    fn put(&self, key: &CacheKey, value: &[u8]) {
        self.cache().put(key, value)
    }
}

impl CacheBackend for SharedCegisCache {
    fn get(&self, key: &CacheKey) -> Option<Vec<u8>> {
        match &self.inner {
            Backend::Disk { file } => file.get(key),
            Backend::InMemory { mem } => mem.get(key),
        }
    }

    fn put(&self, key: &CacheKey, value: &[u8]) {
        match &self.inner {
            Backend::Disk { file } => {
                let target = disk_path_for(file, key);
                let lock_path = target.with_extension("lock");
                if let Some(parent) = lock_path.parent() {
                    let _ = create_private_dir_all(parent);
                }

                match WriteLock::try_acquire(lock_path.clone()) {
                    Ok(Some(_guard)) => file.put(key, value),
                    Ok(None) => log_contention_once(&lock_path),
                    Err(e) => log_io_once(&lock_path, &e),
                }
            }
            Backend::InMemory { mem } => mem.put(key, value),
        }
    }
}

impl std::fmt::Debug for SharedCegisCache {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("SharedCegisCache")
            .field("on_disk", &self.on_disk)
            .field("root", &self.root)
            .finish()
    }
}

fn disk_path_for(file: &FileCache, key: &CacheKey) -> PathBuf {
    let hex = key.hex();
    file.root().join(&hex[0..2]).join(hex)
}

static FALLBACK_ONCE: Once = Once::new();
static UNTRUSTED_ONCE: Once = Once::new();
static CONTENTION_ONCE: Once = Once::new();
static IO_ONCE: Once = Once::new();

fn log_untrusted_once(root: &Path, reason: &str) {
    UNTRUSTED_ONCE.call_once(|| {
        eprintln!(
            "trust-cg-verify::cegis_cache_io: warning: refusing untrusted shared cache root {} \
             ({reason}); a CEGIS cache root must be a directory the current user owns and no \
             other user can write (`chmod 700` repairs one you own); falling back to \
             in-memory cache for this process",
            root.display(),
        );
    });
}

fn log_fallback_once(root: &Path, err: &io::Error) {
    FALLBACK_ONCE.call_once(|| {
        eprintln!(
            "trust-cg-verify::cegis_cache_io: warning: shared cache root {} unusable ({}); \
             falling back to in-memory cache for this process",
            root.display(),
            err,
        );
    });
}

fn log_contention_once(lock_path: &Path) {
    CONTENTION_ONCE.call_once(|| {
        eprintln!(
            "trust-cg-verify::cegis_cache_io: warning: shared cache writer lock {} held > {:?}; \
             skipping put",
            lock_path.display(),
            WRITE_LOCK_WAIT,
        );
    });
}

fn log_io_once(lock_path: &Path, err: &io::Error) {
    IO_ONCE.call_once(|| {
        eprintln!(
            "trust-cg-verify::cegis_cache_io: warning: shared cache lock {} I/O error: {}; \
             continuing without put",
            lock_path.display(),
            err,
        );
    });
}

#[cfg(test)]
mod tests {
    use super::*;

    fn isolated_root(tag: &str) -> PathBuf {
        let nonce = ROOT_PROBE_COUNTER.fetch_add(1, Ordering::Relaxed);
        let root = std::env::temp_dir().join(format!(
            "trust_cg_cegis_cache_io_{}_{}_{}",
            tag,
            std::process::id(),
            nonce
        ));
        let _ = std::fs::remove_dir_all(&root);
        root
    }

    fn key(module_hash: u128) -> CacheKey {
        CacheKey::new(
            module_hash,
            2,
            "aarch64-apple-darwin".to_string(),
            "apple-m1".to_string(),
            vec!["+neon".to_string()],
        )
    }

    #[test]
    fn default_root_respects_explicit_env() {
        let want = isolated_root("explicit_env");
        let want_str = want.to_str().expect("temp cache path is valid UTF-8");
        // The thread-local override is restored on scope exit, even on panic.
        crate::env_lock::with_env_overrides(&[(CEGIS_CACHE_ENV, want_str)], || {
            assert_eq!(default_cache_root(), want);
        });
    }

    /// The default root's user cache is the one rule every trust-cg cache
    /// root shares (`private_fs::user_cache_base`): an empty, blank or
    /// relative `XDG_CACHE_HOME` is ignored, never read against the working
    /// directory.
    #[test]
    fn default_root_ignores_an_empty_or_relative_xdg_cache_home() {
        let resolve = |xdg: &str| {
            crate::env_lock::with_env_overrides_removed(&[CEGIS_CACHE_ENV], || {
                crate::env_lock::with_env_overrides(
                    &[("XDG_CACHE_HOME", xdg), ("HOME", "/home/u")],
                    default_cache_root,
                )
            })
        };
        for ignored in ["", "  ", "relative-cache"] {
            assert_eq!(
                resolve(ignored),
                Path::new("/home/u/.cache").join(CEGIS_CACHE_DIR_NAME),
                "XDG_CACHE_HOME={ignored:?}"
            );
        }
        assert_eq!(
            resolve("/xdg"),
            Path::new("/xdg").join(CEGIS_CACHE_DIR_NAME)
        );
    }

    #[test]
    fn on_disk_round_trip_cleans_lockfile() {
        let root = isolated_root("round_trip");
        let cache = SharedCegisCache::new_at(&root);
        assert!(cache.is_on_disk());

        let key = key(0x633);
        cache.put(&key, b"payload");
        assert_eq!(cache.get(&key).as_deref(), Some(&b"payload"[..]));

        let Backend::Disk { file } = &cache.inner else {
            panic!("expected disk backend");
        };
        let lock = disk_path_for(file, &key).with_extension("lock");
        assert!(!lock.exists(), "lockfile must be removed after put");

        let _ = std::fs::remove_dir_all(&root);
    }

    #[cfg(unix)]
    fn mode(path: &Path) -> u32 {
        use std::os::unix::fs::PermissionsExt;
        std::fs::metadata(path)
            .expect("metadata")
            .permissions()
            .mode()
            & 0o7777
    }

    #[cfg(unix)]
    fn chmod(path: &Path, mode: u32) {
        use std::os::unix::fs::PermissionsExt;
        std::fs::set_permissions(path, std::fs::Permissions::from_mode(mode)).expect("chmod");
    }

    #[cfg(unix)]
    fn untrusted_reason(result: Result<(), RootRefusal>) -> String {
        match result {
            Err(RootRefusal::Untrusted(reason)) => reason,
            Err(RootRefusal::Unusable(e)) => panic!("expected an untrusted root, got {e}"),
            Ok(()) => panic!("expected an untrusted root, got a private one"),
        }
    }

    /// Under this host's umask (002) the old writer left the root and shard
    /// directories 0775 and entries 0664, so any member of the group could
    /// replace a recorded rewrite.
    #[cfg(unix)]
    #[test]
    fn created_root_shards_entries_and_locks_are_private() {
        let root = isolated_root("private_modes");
        let cache = SharedCegisCache::new_at(&root);
        assert!(cache.is_on_disk());
        assert_eq!(mode(&root), 0o700);

        let key = key(0x0700);
        cache.put(&key, b"payload");
        let Backend::Disk { file } = &cache.inner else {
            panic!("expected disk backend");
        };
        let entry = disk_path_for(file, &key);
        assert_eq!(mode(entry.parent().expect("shard")), 0o700);
        assert_eq!(mode(&entry), 0o600);

        let lock = entry.with_extension("lock");
        let guard = WriteLock::try_acquire(lock.clone())
            .expect("lock I/O")
            .expect("uncontended lock");
        assert_eq!(mode(&lock), 0o600);
        drop(guard);
        assert!(!lock.exists());

        let _ = std::fs::remove_dir_all(&root);
    }

    #[cfg(unix)]
    #[test]
    fn group_or_world_writable_root_is_refused() {
        let root = isolated_root("writable_by_others");
        create_private_dir_all(&root).expect("create root");
        for others_write in [0o770, 0o775, 0o777, 0o1777, 0o720, 0o702] {
            chmod(&root, others_write);
            let reason = untrusted_reason(check_private_root(&root, current_uid()));
            assert!(reason.contains("group or other users write"), "{reason}");
            let cache = SharedCegisCache::new_at(&root);
            assert!(!cache.is_on_disk(), "mode {others_write:o} must be refused");
            let key = key(0x0775);
            cache.put(&key, b"memory");
            assert_eq!(cache.get(&key).as_deref(), Some(&b"memory"[..]));
            let entries = std::fs::read_dir(&root).expect("read root").count();
            assert_eq!(entries, 0, "a refused root is never written");
        }

        // `chmod 700` repairs a root the current user owns.
        chmod(&root, 0o700);
        assert!(check_private_root(&root, current_uid()).is_ok());
        assert!(SharedCegisCache::new_at(&root).is_on_disk());
        let _ = std::fs::remove_dir_all(&root);
    }

    #[cfg(unix)]
    #[test]
    fn root_owned_by_another_user_is_refused() {
        let root = isolated_root("other_owner");
        create_private_dir_all(&root).expect("create root");
        let other = current_uid().wrapping_add(1);
        let reason = untrusted_reason(check_private_root(&root, other));
        assert!(reason.contains("not the current user"), "{reason}");
        let _ = std::fs::remove_dir_all(&root);

        // A real directory another user owns: `/` is root's.
        if current_uid() != 0 {
            let reason = untrusted_reason(check_private_root(Path::new("/"), current_uid()));
            assert!(reason.contains("owned by uid 0"), "{reason}");
            assert!(!SharedCegisCache::new_at("/").is_on_disk());
        }
    }

    /// With no `TRUST_CG_CEGIS_CACHE`, `XDG_CACHE_HOME` or `HOME`, the root is
    /// a fixed name in the host-wide temp directory. Whoever creates it first
    /// owns it: another user's copy, or the sticky world-writable temp
    /// directory itself, is refused.
    #[cfg(unix)]
    #[test]
    fn shared_temp_dir_fallback_is_used_only_when_private() {
        let fallback = crate::env_lock::with_env_overrides_removed(
            &[CEGIS_CACHE_ENV, "XDG_CACHE_HOME", "HOME"],
            default_cache_root,
        );
        assert_eq!(fallback, std::env::temp_dir().join(".trust-cg-cegis-cache"));

        let tmp = Path::new("/tmp");
        if mode(tmp) & 0o002 != 0 {
            untrusted_reason(check_private_root(tmp, current_uid()));
            assert!(!SharedCegisCache::new_at(tmp).is_on_disk());
        }

        // The same fixed name, created by another user or left world-writable.
        let planted = isolated_root("shared_fallback").join(".trust-cg-cegis-cache");
        create_private_dir_all(&planted).expect("create fallback");
        untrusted_reason(check_private_root(&planted, current_uid().wrapping_add(1)));
        chmod(&planted, 0o1777);
        assert!(!SharedCegisCache::new_at(&planted).is_on_disk());
        let _ = std::fs::remove_dir_all(planted.parent().expect("parent"));
    }

    /// The directory a symlinked root resolves to is judged, and used: the
    /// cache keeps the resolved path, so re-pointing the link afterwards does
    /// not redirect it.
    #[cfg(unix)]
    #[test]
    fn symlinked_root_is_judged_and_used_by_its_target() {
        let base = isolated_root("symlink");
        let open = base.join("open");
        let private = base.join("private");
        let link = base.join("link");
        create_private_dir_all(&open).expect("create open");
        create_private_dir_all(&private).expect("create private");
        chmod(&open, 0o777);

        std::os::unix::fs::symlink(&open, &link).expect("symlink");
        assert!(!SharedCegisCache::new_at(&link).is_on_disk());

        std::fs::remove_file(&link).expect("unlink");
        std::os::unix::fs::symlink(&private, &link).expect("symlink");
        let cache = SharedCegisCache::new_at(&link);
        assert!(cache.is_on_disk());
        std::fs::remove_file(&link).expect("unlink");
        std::os::unix::fs::symlink(&open, &link).expect("re-point");

        let key = key(0x5717);
        cache.put(&key, b"resolved");
        let Backend::Disk { file } = &cache.inner else {
            panic!("expected disk backend");
        };
        assert!(disk_path_for(file, &key).starts_with(std::fs::canonicalize(&private).unwrap()));
        assert_eq!(std::fs::read_dir(&open).expect("read open").count(), 0);
        let _ = std::fs::remove_dir_all(&base);
    }

    /// Every pipeline builds the default cache, CEGIS or not; the root is
    /// created and judged only when the pass first reads or writes.
    #[test]
    fn deferred_cache_opens_its_root_on_first_use() {
        let root = isolated_root("deferred");
        let cache = SharedCegisCache::arc_at(&root);
        assert!(
            !root.exists(),
            "building the backend must not touch the root"
        );
        let key = key(0xDEF);
        assert!(cache.get(&key).is_none());
        assert!(root.is_dir());
        cache.put(&key, b"deferred");
        assert_eq!(cache.get(&key).as_deref(), Some(&b"deferred"[..]));
        let _ = std::fs::remove_dir_all(&root);
    }

    #[test]
    fn file_root_falls_back_to_memory() {
        let root = isolated_root("file_root");
        std::fs::write(&root, b"not a directory").expect("create file root");

        let cache = SharedCegisCache::new_at(&root);
        assert!(!cache.is_on_disk());

        let key = key(0x634);
        cache.put(&key, b"memory payload");
        assert_eq!(cache.get(&key).as_deref(), Some(&b"memory payload"[..]));

        let _ = std::fs::remove_file(&root);
    }
}
