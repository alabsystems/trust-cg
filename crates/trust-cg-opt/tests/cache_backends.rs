// Integration test: cache backend semantics (InMemory + File).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Verifies the miss → put → hit lifecycle on both backends, and that the
// on-disk backend survives across two FileCache constructions on the same
// root (as a crash-safety/atomic-rename smoke test).

use std::fs;
use std::path::PathBuf;
use std::sync::{Arc, Barrier};
use std::thread;

use trust_cg_opt::{CacheBackend, CacheKey, FileCache, InMemoryCache};

fn tmp_root(name: &str) -> PathBuf {
    let mut p = std::env::temp_dir();
    let pid = std::process::id();
    let nanos = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|d| d.as_nanos())
        .unwrap_or(0);
    p.push(format!(
        "trust-cg-cache-backends-{}-{}-{}-test",
        name, pid, nanos
    ));
    let _ = fs::remove_dir_all(&p);
    fs::create_dir_all(&p).expect("create tmp root");
    p
}

fn make_key(tag: u64) -> CacheKey {
    CacheKey::new(
        (tag as u128) ^ 0xA5A5_A5A5_A5A5_A5A5_u128,
        2,
        "aarch64-apple-darwin".to_string(),
        "apple-m1".to_string(),
        vec!["neon".to_string()],
    )
}

#[test]
fn inmemory_miss_put_hit() {
    let cache = InMemoryCache::new();
    let key = make_key(1);

    assert!(cache.get(&key).is_none(), "fresh cache is empty");
    cache.put(&key, b"hello");
    let got = cache.get(&key);
    assert_eq!(got.as_deref(), Some(b"hello".as_slice()));
}

#[test]
fn inmemory_distinct_keys_are_separate() {
    let cache = InMemoryCache::new();
    let k1 = make_key(1);
    let k2 = make_key(2);
    cache.put(&k1, b"one");
    cache.put(&k2, b"two");
    assert_eq!(cache.get(&k1).as_deref(), Some(b"one".as_slice()));
    assert_eq!(cache.get(&k2).as_deref(), Some(b"two".as_slice()));
}

#[test]
fn file_cache_miss_put_hit() {
    let root = tmp_root("miss_put_hit");
    let cache = FileCache::new(root.clone()).expect("create file cache");
    let key = make_key(7);

    assert!(cache.get(&key).is_none(), "fresh disk cache is empty");
    cache.put(&key, b"disk-value-0");
    let got = cache.get(&key);
    assert_eq!(got.as_deref(), Some(b"disk-value-0".as_slice()));

    let _ = fs::remove_dir_all(&root);
}

#[test]
fn file_cache_persists_across_new_handles() {
    let root = tmp_root("persist");
    let key = make_key(42);

    {
        let a = FileCache::new(root.clone()).expect("create file cache");
        a.put(&key, b"persisted");
    }
    // Second handle on the same root must see the write from the first.
    let b = FileCache::new(root.clone()).expect("reopen file cache");
    assert_eq!(b.get(&key).as_deref(), Some(b"persisted".as_slice()));

    let _ = fs::remove_dir_all(&root);
}

#[test]
fn file_cache_overwrite_wins() {
    let root = tmp_root("overwrite");
    let cache = FileCache::new(root.clone()).expect("create file cache");
    let key = make_key(3);
    cache.put(&key, b"first");
    cache.put(&key, b"second");
    assert_eq!(cache.get(&key).as_deref(), Some(b"second".as_slice()));
    let _ = fs::remove_dir_all(&root);
}

#[test]
fn file_cache_concurrent_same_key_puts_do_not_share_temp_files() {
    let root = tmp_root("concurrent_same_key");
    let cache = Arc::new(FileCache::new(root.clone()).expect("create file cache"));
    let key = make_key(55);
    let barrier = Arc::new(Barrier::new(16));

    let mut handles = Vec::new();
    for i in 0..16 {
        let cache = Arc::clone(&cache);
        let barrier = Arc::clone(&barrier);
        let key = key.clone();
        handles.push(thread::spawn(move || {
            let payload = format!("payload-{i}");
            barrier.wait();
            cache.put(&key, payload.as_bytes());
        }));
    }

    for handle in handles {
        handle.join().expect("cache writer thread panicked");
    }

    let got = cache.get(&key).expect("one concurrent writer should win");
    let got = std::str::from_utf8(&got).expect("payload should be utf8");
    assert!(
        (0..16).any(|i| got == format!("payload-{i}")),
        "final payload should come from one writer, got {got:?}",
    );

    let hex = key.hex();
    let shard_dir = root.join(&hex[0..2]);
    let tmp_leftovers = fs::read_dir(&shard_dir)
        .expect("cache shard should exist")
        .filter_map(Result::ok)
        .filter(|entry| entry.file_name().to_string_lossy().ends_with(".tmp"))
        .count();
    assert_eq!(
        tmp_leftovers, 0,
        "temp files should be renamed or cleaned up"
    );

    let _ = fs::remove_dir_all(&root);
}
