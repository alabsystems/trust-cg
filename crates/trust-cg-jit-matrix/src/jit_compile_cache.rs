// trust-cg-jit-matrix/src/jit_compile_cache.rs - Content-addressed
// thread-local cache of compiled JIT BCP providers.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// # Why this exists
//
// JIT compilation adds a fixed per-formula cost that a single-shot solve may
// not amortize. An in-process benchmark harness can solve the same CNF many
// times, so repeated compilation would distort the measurement; this cache
// lets later solves reuse the compiled provider.
//
// # Design
//
// * Content-addressed by `formula_hash`: a stable 64-bit hash of
//   `(num_vars, clauses)`. Each clause's literals and the outer clause list are
//   normalized before hashing, so semantically identical reorderings share a
//   cache entry. The module builders use the same normalized formula contract.
//
// * Bounded LRU eviction: `JIT_COMPILE_CACHE_CAPACITY` entries per
//   provider type. Insertion order tracked via `VecDeque<u64>`; on
//   overflow the front entry is dropped. Cheap, predictable, good
//   enough for the corpus sizes we benchmark.
//
// * Three thread-locals, one per provider type. MicroSAT runs
//   single-threaded inside this crate's binaries and tests, so a
//   thread-local cache is the right granularity.
//
// # Disk-backed persistence
//
// The in-memory cache is now paired with an optional on-disk
// content-addressed cache of serialized trust-ir module text (see
// `jit_disk_cache`). The disk path is keyed by `(formula_hash,
// kernel_name)` and stores the same IR a fresh module-builder call
// would produce. On disk hit, the per-kernel `compile_or_get_cached`
// path skips the `build_bcp_propagate_*_module()` step and feeds the
// cached IR text directly into `Compiler::compile_module_to_jit`. On
// disk miss, the freshly-built module's IR text is written back to
// disk for future process invocations - SAT-Comp's one-solve-per-
// process model still amortizes the front-end IR-construction cost
// across successive launches.
//
// Disk I/O failures NEVER break compilation. The disk module degrades
// to "act as if the disk cache is not configured" on any error path
// (missing dir, permission denied, corrupt content, concurrent-writer
// races); see `jit_disk_cache` for the full error contract.
//
// # Scope vs ExecutableBuffer-on-disk
//
// We persist only the IR text, not the final ExecutableBuffer. This
// saves the front-end module-construction work but still pays ISel,
// optimization, regalloc, frame lowering, and encoding on every disk
// hit. A future revision could persist the ExecutableBuffer itself
// (with relocations) to eliminate all compile cost, but that requires
// owning the trust-cg-codegen output format serializer.

use std::collections::{HashMap, VecDeque};
use std::hash::{BuildHasher, BuildHasherDefault, Hash, Hasher};
use std::sync::Arc;

use sha2::{Digest, Sha256};
use trust_cg_codegen::jit::ExecutableBuffer;
// `ExecutableBuffer` is referenced in the type-bound of
// `get_or_compile_with_buffer_disk::BuildBuf` below.

use crate::jit_bcp_kernel::{
    JitBcpKernelProvider, JitBcpWatchedLiteralChunkedKernelProvider,
    JitBcpWatchedLiteralKernelProvider, JitBcpWithDecisionsProvider,
};

/// Per-provider-type cache capacity. Sixteen entries bound memory while still
/// covering the focused smoke/benchmark subsets; a full 27-fixture release
/// corpus traversal may evict older entries.
pub const JIT_COMPILE_CACHE_CAPACITY: usize = 16;

/// Compute a stable 64-bit hash of `(num_vars, clauses)`.
///
/// Normalization rules:
/// * Each clause's literals are sorted before hashing so `[1, -2]`
///   hashes identically to `[-2, 1]`.
/// * The outer clause list is also sorted (lex on the
///   already-intra-sorted literals) so `[c1, c2]` and `[c2, c1]`
///   share a hash. BCP is commutative across clauses for the
///   correctness contract this cache cares about (same input
///   formula, same compiled propagation behaviour).
///
/// We use `BuildHasherDefault<std::hash::DefaultHasher>` so the
/// numeric hash value is process-stable (`DefaultHasher` is seeded
/// deterministically from the program's start). The same input
/// always produces the same `u64` inside a single process, which is
/// all the cache contract requires.
pub fn compute_formula_hash(num_vars: usize, clauses: &[Vec<i32>]) -> u64 {
    let normalized = normalized_clauses(clauses);

    let builder: BuildHasherDefault<std::collections::hash_map::DefaultHasher> =
        BuildHasherDefault::default();
    let mut hasher = builder.build_hasher();
    // Domain-separate against other potential hashes that might
    // share `DefaultHasher` state in the same crate (defensive).
    "trust-cg-jit-matrix::jit_compile_cache::formula::v1".hash(&mut hasher);
    num_vars.hash(&mut hasher);
    normalized.len().hash(&mut hasher);
    for clause in &normalized {
        clause.len().hash(&mut hasher);
        for &lit in clause {
            lit.hash(&mut hasher);
        }
    }
    hasher.finish()
}

/// A collision-resistant identity for a normalized `(num_vars, clauses)`
/// formula: the 32-byte SHA-256 of its canonical byte encoding.
///
/// Unlike [`compute_formula_hash`] (a 64-bit `DefaultHasher` digest used only
/// as a cheap bucket index), this is used as the *authoritative* content key:
/// the in-memory cache compares it on every hit, and the disk tiers embed it in
/// the cache filename. A 64-bit bucket collision between two genuinely different
/// formulas therefore can never serve one formula's compiled artifact for the
/// other — the `FormulaKey` will differ (SHA-256 collision probability ~2^-128,
/// the same strength the disk caches already rely on for payload integrity and
/// codegen-version identity).
pub type FormulaKey = [u8; 32];

/// Normalize `clauses` for hashing/identity: sort literals within each clause
/// (so `[1, -2]` == `[-2, 1]`) then sort the outer clause list (so clause order
/// does not matter). Returns owned copies; the caller's input is untouched.
fn normalized_clauses(clauses: &[Vec<i32>]) -> Vec<Vec<i32>> {
    let mut normalized: Vec<Vec<i32>> = clauses
        .iter()
        .map(|c| {
            let mut copy = c.clone();
            copy.sort_unstable();
            copy
        })
        .collect();
    normalized.sort();
    normalized
}

/// Canonical, unambiguous byte encoding of a normalized formula. Length-prefixes
/// every variable-width field so two distinct formulas can never encode to the
/// same bytes (no delimiter-collision across clause boundaries).
fn canonical_formula_bytes(num_vars: usize, clauses: &[Vec<i32>]) -> Vec<u8> {
    let normalized = normalized_clauses(clauses);
    let mut bytes =
        Vec::with_capacity(16 + normalized.iter().map(|c| 4 + 4 * c.len()).sum::<usize>());
    bytes.extend_from_slice(b"trust-cg-jit-matrix::formula::v1\0");
    bytes.extend_from_slice(&(num_vars as u64).to_le_bytes());
    bytes.extend_from_slice(&(normalized.len() as u64).to_le_bytes());
    for clause in &normalized {
        bytes.extend_from_slice(&(clause.len() as u64).to_le_bytes());
        for &lit in clause {
            bytes.extend_from_slice(&lit.to_le_bytes());
        }
    }
    bytes
}

/// Compute the [`FormulaKey`] (SHA-256 of the canonical encoding) for a formula.
pub fn formula_sha256(num_vars: usize, clauses: &[Vec<i32>]) -> FormulaKey {
    let mut hasher = Sha256::new();
    hasher.update(canonical_formula_bytes(num_vars, clauses));
    let digest = hasher.finalize();
    let mut out = [0u8; 32];
    out.copy_from_slice(&digest);
    out
}

/// Lowercase hex rendering of a [`FormulaKey`], for embedding in disk-cache
/// filenames so distinct formulas never share an on-disk slot.
pub fn formula_key_hex(key: &FormulaKey) -> String {
    let mut s = String::with_capacity(64);
    for byte in key {
        s.push_str(&format!("{byte:02x}"));
    }
    s
}

/// Build the disk-cache slot discriminator for a `(kernel, formula)` pair.
///
/// The on-disk caches name files `{hash:016x}-{slot}.{ext}`. By folding the
/// full 256-bit formula SHA-256 into `slot` here, two distinct formulas that
/// share a 64-bit bucket hash resolve to DIFFERENT files, so a collision can
/// never surface another formula's persisted artifact across processes. The
/// kernel name is kept as a human-readable prefix so the three BCP kernels stay
/// distinguishable on disk.
fn disk_slot_name(kernel_name: &str, formula_key: &FormulaKey) -> String {
    format!("{kernel_name}-{}", formula_key_hex(formula_key))
}

/// In-memory bounded LRU cache keyed by `formula_hash`. Values are
/// `Arc<P>` so callers can hold cheap clones while the cache retains
/// a strong reference for future hits.
///
/// When `disk_backed` is true (the default), the cache also consults
/// the on-disk IR text cache in `jit_disk_cache` for entries that miss
/// in memory. Tests that want to exercise pure in-memory semantics
/// (e.g. timing the cold compile path with no chance of disk hits)
/// can flip `disk_backed` to false via [`Self::set_disk_backed`].
pub struct JitCompileCache<P> {
    /// Keyed by the cheap 64-bit bucket hash, but each entry ALSO stores the
    /// collision-resistant [`FormulaKey`]. Every hit compares the stored
    /// `FormulaKey` against the caller's before returning the cached `Arc<P>`,
    /// so a 64-bit bucket collision between two distinct formulas can never
    /// serve the wrong compiled artifact — it is treated as a miss and the
    /// correct formula is compiled fresh.
    entries: HashMap<u64, (FormulaKey, Arc<P>)>,
    order: VecDeque<u64>,
    max_entries: usize,
    disk_backed: bool,
}

impl<P> JitCompileCache<P> {
    pub fn new(max_entries: usize) -> Self {
        Self {
            entries: HashMap::new(),
            order: VecDeque::with_capacity(max_entries.max(1)),
            max_entries: max_entries.max(1),
            disk_backed: true,
        }
    }

    /// Toggle the disk-backed behaviour for this cache instance.
    pub fn set_disk_backed(&mut self, enabled: bool) {
        self.disk_backed = enabled;
    }

    /// Returns whether disk-backed persistence is active.
    pub fn disk_backed(&self) -> bool {
        self.disk_backed
    }

    /// Number of entries currently held. Test-facing.
    pub fn len(&self) -> usize {
        self.entries.len()
    }

    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    /// Return the cached `Arc<P>` for `hash` if present, otherwise
    /// invoke `build_fn` to compile a fresh provider, insert it, and
    /// return an `Arc<P>` referencing it. Insertion may evict the
    /// oldest entry if the cache is at capacity.
    pub fn get_or_compile<E, F>(
        &mut self,
        hash: u64,
        formula_key: FormulaKey,
        build_fn: F,
    ) -> Result<Arc<P>, E>
    where
        F: FnOnce() -> Result<P, E>,
    {
        // Verify-on-hit: only trust the cached artifact when the stored
        // collision-resistant key matches. A 64-bit bucket collision (same
        // `hash`, different `formula_key`) falls through and compiles fresh.
        if let Some((stored_key, arc)) = self.entries.get(&hash)
            && *stored_key == formula_key
        {
            return Ok(Arc::clone(arc));
        }
        let provider = build_fn()?;
        let arc = Arc::new(provider);
        self.insert_in_memory(hash, formula_key, &arc);
        Ok(arc)
    }

    /// Disk-aware variant of [`Self::get_or_compile`].
    ///
    /// Behaviour:
    /// 1. Return the in-memory entry if present.
    /// 2. Otherwise consult the on-disk cache (when `disk_backed`).
    ///    The cached IR text (or `None` on miss) is passed to
    ///    `build_fn`, which returns the constructed provider AND the
    ///    IR text that should be persisted on disk for future runs.
    /// 3. On a disk MISS the returned IR text is written back via
    ///    `jit_disk_cache::disk_store` so the next process invocation
    ///    skips module construction. A disk hit is left untouched only
    ///    when the builder returns the exact text it was given. If the
    ///    builder rejects cached text and rebuilds, the fresh text replaces
    ///    the poisoned entry atomically.
    /// 4. The fresh `Arc<P>` is inserted into the in-memory cache
    ///    (evicting the oldest entry if at capacity).
    ///
    /// The caller controls both halves of the disk handshake because
    /// the build closure is the only code that knows how to turn IR
    /// text into a kernel-specific provider (each kernel uses a
    /// different entry symbol and arena layout).
    pub fn get_or_compile_with_disk<E, F>(
        &mut self,
        hash: u64,
        formula_key: FormulaKey,
        kernel_name: &str,
        build_fn: F,
    ) -> Result<Arc<P>, E>
    where
        F: FnOnce(Option<String>) -> Result<(P, String), E>,
    {
        // Verify-on-hit (see `get_or_compile`).
        if let Some((stored_key, arc)) = self.entries.get(&hash)
            && *stored_key == formula_key
        {
            return Ok(Arc::clone(arc));
        }
        // The disk slot is keyed by the full formula SHA-256 (embedded in the
        // filename), so a 64-bit bucket collision cannot read another formula's
        // persisted artifact.
        let disk_kernel = disk_slot_name(kernel_name, &formula_key);
        let disk_text = if self.disk_backed {
            crate::jit_disk_cache::disk_lookup(hash, &disk_kernel)
        } else {
            None
        };
        // Keep the exact decoded payload so the builder can signal rejection
        // without widening this public API: the cache text is authoritative
        // only when the builder returns it unchanged. `load_or_build_module`
        // returns freshly encoded text after a parse failure, which therefore
        // replaces the integrity-valid but syntactically invalid entry.
        let cached_module_text = disk_text.clone();
        let (provider, module_text) = build_fn(disk_text)?;
        let arc = Arc::new(provider);
        let cache_entry_needs_store = cached_module_text.as_deref() != Some(module_text.as_str());
        if cache_entry_needs_store && self.disk_backed {
            crate::jit_disk_cache::disk_store(hash, &disk_kernel, &module_text);
        }
        self.insert_in_memory(hash, formula_key, &arc);
        Ok(arc)
    }

    /// Disk-aware variant of [`Self::get_or_compile_with_disk`] with a
    /// quarantined executable-buffer tier.
    ///
    /// Lookup order:
    /// 1. **L1 (in-memory)** — return the cached `Arc<P>` if present.
    /// 2. **Reserved L2 (serialized ExecutableBuffer)** — when `disk_backed`, try
    ///    [`crate::executable_buffer_cache::read_buffer_from_disk`]. On a
    ///    same-process test/benchmark hit, pass the decoded buffer into
    ///    `build_from_buffer` to wrap
    ///    it in a provider (typically: re-derive the arena from
    ///    `(num_vars, clauses)`, then plug the deserialized buffer into
    ///    the provider's existing struct). This skips ISel + regalloc +
    ///    optimization + encoding — the full ~95% of compile time
    ///    according to TT's profile. Production reads are hard-disabled until
    ///    external relocations can be rebound after ASLR.
    /// 3. **L3 (on-disk IR text)** — when `disk_backed`, fall through to
    ///    KKK's IR-text cache. The cached IR text (or `None`) is passed
    ///    into `build_from_module`, which must return the constructed
    ///    provider, the freshly compiled `ExecutableBuffer` (so this
    ///    method can populate L2), and the IR text that should be
    ///    persisted to disk for future L3 hits.
    /// 4. **Cold compile** — when both disk tiers miss, the same
    ///    `build_from_module` closure handles `disk_text = None`,
    ///    building the module from scratch.
    ///
    /// On a cold compile, or when the module builder rejects an L3 payload and
    /// returns freshly encoded IR, that text is persisted atomically. An
    /// accepted L3 payload is not rewritten. The freshly compiled buffer is
    /// offered to the guarded L2 writer, which is a no-op in production and is
    /// usable only through the explicitly unsafe, process-private
    /// test/benchmark hook.
    ///
    /// The two-closure split exists because the caller is the only
    /// code that knows the kernel-specific arena layout
    /// (`BcpArena`, `BcpWatchedArena`, parent-loop) and entry symbol.
    /// Only the caller can reconstruct a provider from a deserialized
    /// buffer.
    pub fn get_or_compile_with_buffer_disk<E, BuildBuf, BuildMod>(
        &mut self,
        hash: u64,
        formula_key: FormulaKey,
        kernel_name: &str,
        build_from_buffer: BuildBuf,
        build_from_module: BuildMod,
    ) -> Result<Arc<P>, E>
    where
        BuildBuf: FnOnce(ExecutableBuffer) -> Result<P, E>,
        BuildMod: FnOnce(Option<String>) -> Result<(P, Vec<u8>, String), E>,
    {
        // Verify-on-hit (see `get_or_compile`).
        if let Some((stored_key, arc)) = self.entries.get(&hash)
            && *stored_key == formula_key
        {
            return Ok(Arc::clone(arc));
        }

        // Both disk tiers are keyed by the full formula SHA-256 (embedded in
        // the filename), so a 64-bit bucket collision cannot read another
        // formula's persisted IR text or compiled buffer.
        let disk_kernel = disk_slot_name(kernel_name, &formula_key);

        // Reserved L2: serialized ExecutableBuffer. The called module keeps
        // production I/O hard-disabled; only a process-private test/benchmark
        // override can make this return a buffer.
        if self.disk_backed
            && let Some(buffer) =
                crate::executable_buffer_cache::read_buffer_from_disk(hash, &disk_kernel)
        {
            let provider = build_from_buffer(buffer)?;
            let arc = Arc::new(provider);
            self.insert_in_memory(hash, formula_key, &arc);
            return Ok(arc);
        }

        // L3: IR text — gives us a head start over a cold build_module()
        // call. Fall through to a fresh compile on miss; the closure
        // returns serialized buffer bytes alongside the provider so the
        // quarantined same-process L2 tests can exercise replay without
        // disturbing the provider's owned executable mapping.
        let disk_text = if self.disk_backed {
            crate::jit_disk_cache::disk_lookup(hash, &disk_kernel)
        } else {
            None
        };
        // Preserve the payload to distinguish an accepted L3 hit from a
        // semantic miss hidden behind the builder's fail-open fallback. The
        // latter returns fresh text, so it must repair the persistent slot.
        let cached_module_text = disk_text.clone();
        let (provider, buffer_bytes, module_text) = build_from_module(disk_text)?;

        if self.disk_backed {
            if cached_module_text.as_deref() != Some(module_text.as_str()) {
                crate::jit_disk_cache::disk_store(hash, &disk_kernel, &module_text);
            }
            // Offered to the quarantined L2 writer. Production calls are
            // intentionally discarded until relocation-aware replay exists.
            crate::executable_buffer_cache::write_buffer_bytes_to_disk(
                hash,
                &disk_kernel,
                &buffer_bytes,
            );
        }

        let arc = Arc::new(provider);
        self.insert_in_memory(hash, formula_key, &arc);
        Ok(arc)
    }

    /// Internal: evict-and-insert helper shared by all cache variants. Stores
    /// the `FormulaKey` alongside the provider so future hits can verify the
    /// formula identity. On a bucket-collision overwrite (same `hash`, new
    /// `formula_key`) the existing `order` entry is reused so the LRU deque does
    /// not accumulate duplicate keys.
    fn insert_in_memory(&mut self, hash: u64, formula_key: FormulaKey, arc: &Arc<P>) {
        let overwrites_existing = self.entries.contains_key(&hash);
        if !overwrites_existing {
            while self.entries.len() >= self.max_entries {
                if let Some(oldest) = self.order.pop_front() {
                    self.entries.remove(&oldest);
                } else {
                    break;
                }
            }
        }
        self.entries.insert(hash, (formula_key, Arc::clone(arc)));
        if !overwrites_existing {
            self.order.push_back(hash);
        }
    }

    /// Clear all entries. Test-facing.
    pub fn clear(&mut self) {
        self.entries.clear();
        self.order.clear();
    }
}

impl<P> Default for JitCompileCache<P> {
    fn default() -> Self {
        Self::new(JIT_COMPILE_CACHE_CAPACITY)
    }
}

thread_local! {
    /// Cache of compiled `JitBcpKernelProvider` instances. The scan
    /// kernel is the simplest provider (parameter-less, single-shot
    /// per arena) and is mainly used by the SHADOW_MODE shadow path
    /// today; cached for parity with the other two.
    pub static JIT_BCP_CACHE: std::cell::RefCell<JitCompileCache<JitBcpKernelProvider>> =
        std::cell::RefCell::new(JitCompileCache::new(JIT_COMPILE_CACHE_CAPACITY));

    /// Cache of compiled `JitBcpWithDecisionsProvider` instances.
    /// This is the provider used by the explicit with-decisions mode.
    pub static JIT_BCP_WITH_DECISIONS_CACHE: std::cell::RefCell<
        JitCompileCache<JitBcpWithDecisionsProvider>,
    > = std::cell::RefCell::new(JitCompileCache::new(JIT_COMPILE_CACHE_CAPACITY));

    /// Cache of compiled `JitBcpWatchedLiteralKernelProvider`
    /// instances. This is the default `JIT_KERNEL_CHOICE` since the
    /// watched-literal switchover and is the primary beneficiary of repeated
    /// formula cache hits.
    pub static JIT_BCP_WATCHED_LITERAL_CACHE: std::cell::RefCell<
        JitCompileCache<JitBcpWatchedLiteralKernelProvider>,
    > = std::cell::RefCell::new(JitCompileCache::new(JIT_COMPILE_CACHE_CAPACITY));

    /// Cache of compiled `JitBcpWatchedLiteralChunkedKernelProvider`
    /// instances. This is the chunked-layout sibling of the watched-
    /// literal kernel above; it shares the same algorithm but uses an
    /// `O(num_vars + num_clauses)` linked-list watch table instead of
    /// the fixed-capacity row-major layout the NN-era kernel uses.
    /// Backed by the `watched-literal-chunked` slot on the on-disk IR
    /// cache.
    pub static JIT_BCP_WATCHED_LITERAL_CHUNKED_CACHE: std::cell::RefCell<
        JitCompileCache<JitBcpWatchedLiteralChunkedKernelProvider>,
    > = std::cell::RefCell::new(JitCompileCache::new(JIT_COMPILE_CACHE_CAPACITY));
}

/// Clear all three thread-local caches. Tests use this between
/// scenarios to ensure a clean start; production code does not need
/// to call it.
pub fn reset_jit_compile_caches_for_tests() {
    JIT_BCP_CACHE.with(|c| c.borrow_mut().clear());
    JIT_BCP_WITH_DECISIONS_CACHE.with(|c| c.borrow_mut().clear());
    JIT_BCP_WATCHED_LITERAL_CACHE.with(|c| c.borrow_mut().clear());
    JIT_BCP_WATCHED_LITERAL_CHUNKED_CACHE.with(|c| c.borrow_mut().clear());
}

/// Delete every cached IR file from the on-disk JIT cache directory.
/// Re-exported from [`crate::jit_disk_cache::clear_disk_cache`] so
/// callers (tests, benches, and operators clearing stale state)
/// have one entry point. A missing cache directory is treated as
/// already-clear and never raises an error.
pub fn clear_disk_cache() {
    crate::jit_disk_cache::clear_disk_cache();
}

#[cfg(any(target_arch = "aarch64", target_arch = "x86_64"))]
#[cfg(test)]
mod tests {
    use super::*;
    use std::time::Instant;

    fn small_formula() -> (usize, Vec<Vec<i32>>) {
        (3, vec![vec![1, 2], vec![-2, 3]])
    }

    fn other_formula() -> (usize, Vec<Vec<i32>>) {
        (3, vec![vec![1, -2], vec![2, 3], vec![-1, -3]])
    }

    #[test]
    fn hash_is_order_insensitive_within_clause() {
        let h1 = compute_formula_hash(3, &[vec![1, -2], vec![3]]);
        let h2 = compute_formula_hash(3, &[vec![-2, 1], vec![3]]);
        assert_eq!(h1, h2, "intra-clause literal order must not change hash");
    }

    #[test]
    fn hash_is_order_insensitive_across_clauses() {
        let h1 = compute_formula_hash(3, &[vec![1, -2], vec![2, 3]]);
        let h2 = compute_formula_hash(3, &[vec![2, 3], vec![1, -2]]);
        assert_eq!(h1, h2, "outer clause order must not change hash");
    }

    #[test]
    fn hash_differs_for_distinct_formulas() {
        let (n1, c1) = small_formula();
        let (n2, c2) = other_formula();
        let h1 = compute_formula_hash(n1, &c1);
        let h2 = compute_formula_hash(n2, &c2);
        assert_ne!(h1, h2, "distinct formulas should hash differently");
    }

    #[test]
    fn hash_differs_when_num_vars_differs() {
        let clauses = vec![vec![1, 2], vec![-2, 3]];
        let h1 = compute_formula_hash(3, &clauses);
        let h2 = compute_formula_hash(4, &clauses);
        assert_ne!(h1, h2, "num_vars must participate in the hash");
    }

    #[test]
    fn cache_hit_returns_same_buffer() {
        let mut cache: JitCompileCache<JitBcpKernelProvider> = JitCompileCache::new(8);
        let (num_vars, clauses) = small_formula();
        let hash = compute_formula_hash(num_vars, &clauses);
        let key = formula_sha256(num_vars, &clauses);

        let arc1 = cache
            .get_or_compile::<crate::jit_bcp_kernel::JitCompileError, _>(hash, key, || {
                JitBcpKernelProvider::compile(num_vars, clauses.clone())
            })
            .expect("first compile");
        let arc2 = cache
            .get_or_compile::<crate::jit_bcp_kernel::JitCompileError, _>(hash, key, || {
                panic!("build_fn must not be called on cache hit");
            })
            .expect("cache hit");
        assert!(
            Arc::ptr_eq(&arc1, &arc2),
            "cache hit must return the same Arc"
        );
    }

    #[test]
    fn cache_miss_compiles_fresh() {
        let mut cache: JitCompileCache<JitBcpKernelProvider> = JitCompileCache::new(8);
        let (n1, c1) = small_formula();
        let (n2, c2) = other_formula();
        let h1 = compute_formula_hash(n1, &c1);
        let h2 = compute_formula_hash(n2, &c2);
        let k1 = formula_sha256(n1, &c1);
        let k2 = formula_sha256(n2, &c2);

        let a = cache
            .get_or_compile::<crate::jit_bcp_kernel::JitCompileError, _>(h1, k1, || {
                JitBcpKernelProvider::compile(n1, c1.clone())
            })
            .expect("compile a");
        let b = cache
            .get_or_compile::<crate::jit_bcp_kernel::JitCompileError, _>(h2, k2, || {
                JitBcpKernelProvider::compile(n2, c2.clone())
            })
            .expect("compile b");
        assert!(
            !Arc::ptr_eq(&a, &b),
            "distinct hashes must yield distinct Arcs"
        );
    }

    #[test]
    fn cache_distinguishes_distinct_formulas() {
        let mut cache: JitCompileCache<JitBcpKernelProvider> = JitCompileCache::new(8);
        // Two formulas that differ only in clause/literal order:
        // hash and Arc identity must match after normalization.
        let same_a = vec![vec![1, 2], vec![-2, 3]];
        let same_b = vec![vec![3, -2], vec![2, 1]];
        let h_a = compute_formula_hash(3, &same_a);
        let h_b = compute_formula_hash(3, &same_b);
        assert_eq!(h_a, h_b, "reordered same-content formulas must collide");
        let k_a = formula_sha256(3, &same_a);
        let k_b = formula_sha256(3, &same_b);
        assert_eq!(k_a, k_b, "reordered same-content formulas must share a key");

        let arc_a = cache
            .get_or_compile::<crate::jit_bcp_kernel::JitCompileError, _>(h_a, k_a, || {
                JitBcpKernelProvider::compile(3, same_a.clone())
            })
            .expect("compile a");
        let arc_b = cache
            .get_or_compile::<crate::jit_bcp_kernel::JitCompileError, _>(h_b, k_b, || {
                panic!("reordered duplicate should hit the cache");
            })
            .expect("cache hit on reordered");
        assert!(Arc::ptr_eq(&arc_a, &arc_b));

        // A genuinely different formula must produce a different Arc.
        let diff = vec![vec![1, -2], vec![2, 3], vec![-1, -3]];
        let h_diff = compute_formula_hash(3, &diff);
        let k_diff = formula_sha256(3, &diff);
        assert_ne!(h_a, h_diff);
        let arc_diff = cache
            .get_or_compile::<crate::jit_bcp_kernel::JitCompileError, _>(h_diff, k_diff, || {
                JitBcpKernelProvider::compile(3, diff.clone())
            })
            .expect("compile diff");
        assert!(!Arc::ptr_eq(&arc_a, &arc_diff));
    }

    #[test]
    fn cache_eviction_bounded_at_capacity() {
        const CAP: usize = 3;
        let mut cache: JitCompileCache<JitBcpKernelProvider> = JitCompileCache::new(CAP);

        // Insert CAP + 1 distinct formulas. Use trivially distinct
        // unit clauses so each hash is unique.
        let mut hashes = Vec::new();
        for k in 0..(CAP + 1) {
            let clauses = vec![vec![(k + 1) as i32]];
            let h = compute_formula_hash(k + 1, &clauses);
            let key = formula_sha256(k + 1, &clauses);
            hashes.push(h);
            let _ = cache
                .get_or_compile::<crate::jit_bcp_kernel::JitCompileError, _>(h, key, || {
                    JitBcpKernelProvider::compile(k + 1, clauses.clone())
                })
                .expect("compile");
        }
        assert_eq!(cache.len(), CAP, "len must stay at capacity after overflow");
        // The first-inserted hash should have been evicted; the
        // others should still be cache hits.
        assert!(!cache.entries.contains_key(&hashes[0]));
        for h in &hashes[1..] {
            assert!(cache.entries.contains_key(h));
        }
    }

    /// A cache hit on the watched-literal kernel runs in well under
    /// 100 microseconds, vs a cold compile around 1.5 ms on the
    /// scan kernel and ~30 ms on the watched-literal kernel. We
    /// measure the gap directly here as a regression guard.
    #[test]
    fn cache_hit_in_primary_jit_mode_skips_compile() {
        let mut cache: JitCompileCache<JitBcpWatchedLiteralKernelProvider> =
            JitCompileCache::new(4);
        let num_vars = 8;
        let clauses: Vec<Vec<i32>> = vec![
            vec![1, 2, 3],
            vec![-1, 4],
            vec![-2, -3, 5],
            vec![-4, -5, 6],
            vec![-6, 7, 8],
        ];
        let hash = compute_formula_hash(num_vars, &clauses);
        let key = formula_sha256(num_vars, &clauses);

        let t0 = Instant::now();
        let _cold = cache
            .get_or_compile::<crate::jit_bcp_kernel::JitCompileError, _>(hash, key, || {
                JitBcpWatchedLiteralKernelProvider::compile(num_vars, clauses.clone(), num_vars)
            })
            .expect("cold compile");
        let cold = t0.elapsed();

        let t1 = Instant::now();
        let _warm = cache
            .get_or_compile::<crate::jit_bcp_kernel::JitCompileError, _>(hash, key, || {
                panic!("warm path must not invoke build_fn");
            })
            .expect("warm hit");
        let warm = t1.elapsed();

        // Cold should be at least 10x the warm hit on any sane host,
        // and warm itself should be under 100 microseconds. We use
        // 500 microseconds as the upper bound to be robust to noisy
        // CI hardware. The eprintln makes the cold/warm numbers
        // visible in `cargo test -- --nocapture` so the report's
        // headline ("cache hit ~Xus, miss ~Yms") can be quoted
        // directly without a separate microbench binary.
        eprintln!(
            "jit_compile_cache: cold={}us warm={}us speedup={:.1}x",
            cold.as_micros(),
            warm.as_micros(),
            cold.as_secs_f64() / warm.as_secs_f64().max(1e-9)
        );
        assert!(
            warm.as_micros() < 500,
            "cache hit must be under 500us, was {warm:?}"
        );
        assert!(
            cold > warm,
            "cold compile {cold:?} should exceed warm hit {warm:?}"
        );
    }

    #[test]
    fn formula_sha256_matches_hash_normalization() {
        // Same normalization contract as the 64-bit bucket hash: intra-clause
        // and inter-clause order are irrelevant, num_vars participates.
        let a = formula_sha256(3, &[vec![1, -2], vec![3]]);
        let b = formula_sha256(3, &[vec![-2, 1], vec![3]]);
        assert_eq!(a, b, "intra-clause order must not change the key");

        let c = formula_sha256(3, &[vec![1, -2], vec![2, 3]]);
        let d = formula_sha256(3, &[vec![2, 3], vec![1, -2]]);
        assert_eq!(c, d, "outer clause order must not change the key");

        let e = formula_sha256(3, &[vec![1, 2]]);
        let f = formula_sha256(4, &[vec![1, 2]]);
        assert_ne!(e, f, "num_vars must participate in the key");
    }

    #[test]
    fn bucket_hash_collision_does_not_serve_wrong_artifact() {
        // Soundness regression guard for the 64-bit-collision defect: two
        // genuinely different formulas are forced into the SAME bucket hash
        // (`hash`), but carry DIFFERENT `FormulaKey`s. The second lookup must
        // NOT return the first formula's compiled artifact — it must compile
        // fresh, because verify-on-hit rejects the mismatched key.
        let mut cache: JitCompileCache<JitBcpKernelProvider> = JitCompileCache::new(8);

        let (n1, c1) = small_formula();
        let (n2, c2) = other_formula();
        // A single forged bucket hash shared by both formulas (simulating a
        // 64-bit DefaultHasher collision that the real hash makes astronomically
        // unlikely but never impossible).
        let forced_hash: u64 = 0xC0FFEE_u64;
        let k1 = formula_sha256(n1, &c1);
        let k2 = formula_sha256(n2, &c2);
        assert_ne!(k1, k2, "the two formulas must have distinct keys");

        let arc1 = cache
            .get_or_compile::<crate::jit_bcp_kernel::JitCompileError, _>(forced_hash, k1, || {
                JitBcpKernelProvider::compile(n1, c1.clone())
            })
            .expect("compile formula 1");

        // Same bucket hash, different formula. build_fn MUST run (a wrong-artifact
        // hit would skip it and return arc1).
        let mut second_built = false;
        let arc2 = cache
            .get_or_compile::<crate::jit_bcp_kernel::JitCompileError, _>(forced_hash, k2, || {
                second_built = true;
                JitBcpKernelProvider::compile(n2, c2.clone())
            })
            .expect("compile formula 2");

        assert!(
            second_built,
            "a bucket collision with a different formula must recompile, not serve the cached artifact"
        );
        assert!(
            !Arc::ptr_eq(&arc1, &arc2),
            "collision must not alias the two formulas' providers"
        );

        // Re-looking-up formula 1 by its real key now misses (formula 2 overwrote
        // the shared bucket); it recompiles rather than serving formula 2.
        let mut first_rebuilt = false;
        let _arc1b = cache
            .get_or_compile::<crate::jit_bcp_kernel::JitCompileError, _>(forced_hash, k1, || {
                first_rebuilt = true;
                JitBcpKernelProvider::compile(n1, c1.clone())
            })
            .expect("recompile formula 1");
        assert!(
            first_rebuilt,
            "after overwrite, formula 1 must recompile rather than serve formula 2's artifact"
        );
    }
}
