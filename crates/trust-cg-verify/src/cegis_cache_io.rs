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

use std::fs::OpenOptions;
use std::io;
use std::path::{Path, PathBuf};
use std::sync::Arc;
use std::sync::Once;
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};

use trust_cg_opt::cache::{CacheBackend, CacheKey, FileCache, InMemoryCache};

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
/// 2. `$XDG_CACHE_HOME/trust-cg-cegis`
/// 3. `$HOME/.cache/trust-cg-cegis`
/// 4. `std::env::temp_dir()/.trust-cg-cegis-cache`
pub fn default_cache_root() -> PathBuf {
    if let Ok(raw) = crate::env_lock::var(CEGIS_CACHE_ENV) {
        let trimmed = raw.trim();
        if !trimmed.is_empty() {
            return PathBuf::from(trimmed);
        }
    }

    if let Ok(raw) = std::env::var("XDG_CACHE_HOME") {
        let trimmed = raw.trim();
        if !trimmed.is_empty() {
            return PathBuf::from(trimmed).join(CEGIS_CACHE_DIR_NAME);
        }
    }

    if let Some(home) = std::env::var_os("HOME") {
        let home = PathBuf::from(home);
        if !home.as_os_str().is_empty() {
            return home.join(".cache").join(CEGIS_CACHE_DIR_NAME);
        }
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

    let file = OpenOptions::new()
        .create_new(true)
        .write(true)
        .open(&probe)?;
    drop(file);
    std::fs::remove_file(&probe)?;
    Ok(())
}

/// RAII guard for a per-key writer lockfile.
struct WriteLock {
    path: PathBuf,
}

impl WriteLock {
    fn try_acquire(path: PathBuf) -> io::Result<Option<Self>> {
        let deadline = Instant::now() + WRITE_LOCK_WAIT;
        loop {
            match OpenOptions::new().create_new(true).write(true).open(&path) {
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
    /// If the directory cannot be created or cannot accept a write probe, the
    /// cache degrades to an in-memory backend and logs the reason once.
    pub fn new_at(root: impl Into<PathBuf>) -> Self {
        let root = root.into();
        match FileCache::new(root.clone()).and_then(|file| {
            validate_writable_root(&root)?;
            Ok(file)
        }) {
            Ok(file) => Self {
                inner: Backend::Disk { file },
                on_disk: true,
                root,
            },
            Err(e) => {
                log_fallback_once(&root, &e);
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
    pub fn default_arc() -> Arc<dyn CacheBackend> {
        Arc::new(Self::new_default())
    }

    /// Build an `Arc<dyn CacheBackend>` at an explicit root.
    pub fn arc_at(root: impl Into<PathBuf>) -> Arc<dyn CacheBackend> {
        Arc::new(Self::new_at(root))
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
                    let _ = std::fs::create_dir_all(parent);
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
static CONTENTION_ONCE: Once = Once::new();
static IO_ONCE: Once = Once::new();

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
