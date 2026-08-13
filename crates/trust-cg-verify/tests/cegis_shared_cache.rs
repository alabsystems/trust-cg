// cegis_shared_cache - focused SharedCegisCache backend coverage (#633)
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use std::path::PathBuf;
use std::sync::atomic::{AtomicU64, Ordering};
use std::thread;

use trust_cg_opt::{CacheBackend, CacheKey};
use trust_cg_verify::{CegisCacheEntry, SharedCegisCache};

static TEST_COUNTER: AtomicU64 = AtomicU64::new(0);

fn isolated_root(tag: &str) -> PathBuf {
    let id = TEST_COUNTER.fetch_add(1, Ordering::Relaxed);
    let root = std::env::temp_dir().join(format!(
        "trust_cg_cegis_shared_cache_{}_{}_{}",
        tag,
        std::process::id(),
        id
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
        vec!["+neon".to_string(), "+fp-armv8".to_string()],
    )
}

#[test]
fn two_handles_share_current_cegis_entry_payloads() {
    let root = isolated_root("two_handles");

    let cache_a = SharedCegisCache::new_at(&root);
    assert!(
        cache_a.is_on_disk(),
        "fresh temp root should use disk cache"
    );
    let key = key(0x633);
    let entry = CegisCacheEntry::empty();
    assert_eq!(entry.version, CegisCacheEntry::VERSION);

    cache_a.put(&key, &entry.encode().expect("encode CEGIS entry"));

    let cache_b = SharedCegisCache::new_at(&root);
    assert!(cache_b.is_on_disk());
    let hit = cache_b.get(&key).expect("shared cache hit");
    assert_eq!(CegisCacheEntry::decode(&hit), Some(entry));

    let _ = std::fs::remove_dir_all(&root);
}

#[test]
fn different_keys_do_not_collide() {
    let root = isolated_root("no_collision");
    let cache = SharedCegisCache::new_at(&root);
    assert!(cache.is_on_disk());

    let alpha = key(0xA11CE);
    let beta = key(0xB0B);
    cache.put(&alpha, b"alpha");

    assert_eq!(cache.get(&alpha).as_deref(), Some(&b"alpha"[..]));
    assert!(cache.get(&beta).is_none(), "distinct key must miss");

    cache.put(&beta, b"beta");
    assert_eq!(cache.get(&alpha).as_deref(), Some(&b"alpha"[..]));
    assert_eq!(cache.get(&beta).as_deref(), Some(&b"beta"[..]));

    let _ = std::fs::remove_dir_all(&root);
}

#[test]
fn concurrent_prewarmed_reads_all_hit() {
    const N: usize = 4;
    let root = isolated_root("prewarmed_reads");
    let key = key(0xCAFE);
    let entry = CegisCacheEntry::empty();
    let bytes = entry.encode().expect("encode CEGIS entry");

    let warm = SharedCegisCache::new_at(&root);
    assert!(warm.is_on_disk());
    warm.put(&key, &bytes);

    let handles: Vec<_> = (0..N)
        .map(|_| {
            let root = root.clone();
            let key = key.clone();
            let expected = entry.clone();
            thread::spawn(move || {
                let cache = SharedCegisCache::new_at(root);
                let hit = cache.get(&key).expect("prewarmed hit");
                CegisCacheEntry::decode(&hit) == Some(expected)
            })
        })
        .collect();

    for handle in handles {
        assert!(handle.join().expect("reader thread panicked"));
    }

    let _ = std::fs::remove_dir_all(&root);
}

#[test]
fn concurrent_cold_writes_leave_decodable_entry() {
    const N: usize = 4;
    let root = isolated_root("cold_writes");
    let key = key(0xF00D);
    let bytes = CegisCacheEntry::empty()
        .encode()
        .expect("encode CEGIS entry");

    let handles: Vec<_> = (0..N)
        .map(|_| {
            let root = root.clone();
            let key = key.clone();
            let bytes = bytes.clone();
            thread::spawn(move || {
                let cache = SharedCegisCache::new_at(root);
                cache.put(&key, &bytes);
            })
        })
        .collect();

    for handle in handles {
        handle.join().expect("writer thread panicked");
    }

    let observer = SharedCegisCache::new_at(&root);
    let hit = observer.get(&key).expect("observer hit after writes");
    assert!(
        CegisCacheEntry::decode(&hit).is_some(),
        "cold concurrent writes must not leave a torn payload"
    );

    let _ = std::fs::remove_dir_all(&root);
}

#[test]
fn file_root_falls_back_to_memory_without_disk_flag() {
    let root = isolated_root("file_root");
    std::fs::write(&root, b"not a directory").expect("create file root");

    let cache = SharedCegisCache::new_at(&root);
    assert!(!cache.is_on_disk(), "file root must use in-memory fallback");

    let key = key(0xBAD);
    cache.put(&key, b"fallback");
    assert_eq!(cache.get(&key).as_deref(), Some(&b"fallback"[..]));

    let _ = std::fs::remove_file(&root);
}

#[cfg(unix)]
#[test]
fn unwritable_existing_directory_falls_back_without_disk_flag() {
    use std::fs::OpenOptions;
    use std::os::unix::fs::PermissionsExt;

    struct Cleanup {
        root: PathBuf,
        mode: u32,
    }

    impl Drop for Cleanup {
        fn drop(&mut self) {
            let _ =
                std::fs::set_permissions(&self.root, std::fs::Permissions::from_mode(self.mode));
            let _ = std::fs::remove_dir_all(&self.root);
        }
    }

    let root = isolated_root("unwritable");
    std::fs::create_dir_all(&root).expect("create root");
    let mode = std::fs::metadata(&root)
        .expect("metadata")
        .permissions()
        .mode();
    let _cleanup = Cleanup {
        root: root.clone(),
        mode,
    };
    std::fs::set_permissions(&root, std::fs::Permissions::from_mode(0o555))
        .expect("chmod read-only");

    let probe = root.join("write_probe");
    if OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(&probe)
        .is_ok()
    {
        let _ = std::fs::remove_file(probe);
        eprintln!("skipping unwritable-directory assertion: test process can write anyway");
        return;
    }

    let cache = SharedCegisCache::new_at(&root);
    assert!(
        !cache.is_on_disk(),
        "unwritable existing directory must not report on_disk=true"
    );

    let key = key(0xDEAD);
    cache.put(&key, b"memory");
    assert_eq!(cache.get(&key).as_deref(), Some(&b"memory"[..]));
}
