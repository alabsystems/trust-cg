// trust-cg-jit-matrix/src/jit_bcp_kernel.rs - JIT'd BCP kernel SolverKernelProvider.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// # Interior mutability of the per-provider arena
//
// The compiled kernel writes the assignment values, trail entries, and
// (for the watched-literal variant) per-literal watch lists through
// raw pointers baked into the arena's header at construction time.
// Those writes do not flow through Rust's borrow checker, so all
// mutation is already "interior" from the language's point of view.
// To let `Arc<Self>` (handed out by the thread-local compile cache)
// reset and reuse the arena across calls, we wrap the arena field in
// a `RefCell`. The kernel-side raw-pointer writes are unaffected
// (they target the same heap storage either way); the `RefCell` only
// gates the few Rust-level call sites that need `&mut` for `reset`
// or for slice views.

use std::cell::{Ref, RefCell};
use std::collections::HashMap;
use std::sync::Arc;

use thiserror::Error;

use trust_cg_codegen::compiler::CompileError;
use trust_cg_codegen::jit::ExecutableBuffer;
use trust_cg_codegen::pipeline::{encode_trust_ir_text, parse_trust_ir_text};
use trust_cg_codegen::{Compiler, CompilerConfig};

use crate::bcp_module_builder::{
    BcpArena, BcpWatchedArena, BcpWatchedChunkedArena, ENTRY_NAME, ENTRY_NAME_WATCHED_LITERAL,
    ENTRY_NAME_WATCHED_LITERAL_CHUNKED, ENTRY_NAME_WITH_DECISIONS, build_bcp_propagate_module,
    build_bcp_propagate_watched_literal_chunked_module, build_bcp_propagate_watched_literal_module,
    build_bcp_propagate_with_decisions_module,
};
use crate::jit_compile_cache::{
    JIT_BCP_CACHE, JIT_BCP_WATCHED_LITERAL_CACHE, JIT_BCP_WATCHED_LITERAL_CHUNKED_CACHE,
    JIT_BCP_WITH_DECISIONS_CACHE, compute_formula_hash, formula_sha256,
};
use crate::solver_kernel_abi::{
    KernelCtx, KernelEntry, NO_CONFLICTING_CLAUSE, SolverKernelProvider,
};

#[derive(Debug, Error)]
pub enum JitCompileError {
    #[error("trust-cg codegen failed: {0}")]
    Codegen(#[source] Box<CompileError>),
    #[error("JIT buffer is missing required entry symbol `{0}`")]
    MissingEntry(&'static str),
}

impl From<CompileError> for JitCompileError {
    fn from(error: CompileError) -> Self {
        Self::Codegen(Box::new(error))
    }
}

/// Disk-cache module-loading helper shared by every kernel provider.
///
/// If `disk_text` is `Some(text)`, attempt to parse it via
/// `parse_trust_ir_text`. On parse success, return the parsed module
/// and the same text (avoiding a re-encode). On parse failure, fall
/// back to a fresh build via `build_fresh` and emit a warning so an
/// operator can investigate a corrupt cache entry.
///
/// If `disk_text` is `None`, call `build_fresh` and encode the result
/// to text for persistence.
fn load_or_build_module<F>(disk_text: Option<String>, build_fresh: F) -> (trust_ir::Module, String)
where
    F: FnOnce() -> trust_ir::Module,
{
    if let Some(text) = disk_text {
        match parse_trust_ir_text(&text) {
            Ok(module) => return (module, text),
            Err(err) => {
                eprintln!(
                    "trust-cg jit disk cache: cached IR failed to parse ({err}); rebuilding from scratch"
                );
            }
        }
    }
    let module = build_fresh();
    let text = encode_trust_ir_text(&module);
    (module, text)
}

pub struct JitBcpKernelProvider {
    buffer: ExecutableBuffer,
    entry: KernelEntry,
    arena: RefCell<BcpArena>,
}

impl JitBcpKernelProvider {
    pub fn compile(num_vars: usize, clauses: Vec<Vec<i32>>) -> Result<Self, JitCompileError> {
        let module = build_bcp_propagate_module();
        Self::compile_from_module(&module, num_vars, clauses)
    }

    /// Internal: compile `module` into a JIT'd provider with the
    /// supplied formula. Factored out of [`Self::compile`] so the
    /// disk-cache hit path can hand in a pre-parsed module from the
    /// cached IR text without recomputing it from the module builder.
    fn compile_from_module(
        module: &trust_ir::Module,
        num_vars: usize,
        clauses: Vec<Vec<i32>>,
    ) -> Result<Self, JitCompileError> {
        let config = CompilerConfig::for_host_jit();
        let extern_symbols: HashMap<String, *const u8> = HashMap::new();
        let result = Compiler::new(config).compile_module_to_jit(module, &extern_symbols)?;
        let buffer = result.buffer;

        let entry: KernelEntry = {
            // SAFETY: `KernelEntry` is the documented ABI of the
            // `bcp_propagate_scan` function compiled from
            // `build_bcp_propagate_module`. The JitFn wrapper borrows from
            // `buffer`; we extract the raw function pointer via
            // `into_inner()` and keep `buffer` owned by `Self` so the
            // executable memory remains live for every subsequent call
            // through this provider.
            let jit_fn = unsafe { buffer.get_fn_bound::<KernelEntry>(ENTRY_NAME) }
                .ok_or(JitCompileError::MissingEntry(ENTRY_NAME))?;
            jit_fn.into_inner()
        };

        let trail_capacity = (num_vars + 1).max(8);
        let arena = BcpArena::build(num_vars, &clauses, trail_capacity);

        Ok(Self {
            buffer,
            entry,
            arena: RefCell::new(arena),
        })
    }

    /// Borrow the assignment values vector. The returned `Ref` derefs
    /// to `&[i8]` so existing callers reading e.g. `arena_values()[v]`
    /// continue to work via auto-deref.
    pub fn arena_values(&self) -> Ref<'_, [i8]> {
        Ref::map(self.arena.borrow(), |a| a.values.as_slice())
    }

    pub fn arena_trail_len(&self) -> u64 {
        self.arena.borrow().trail_len()
    }

    pub fn buffer(&self) -> &ExecutableBuffer {
        &self.buffer
    }

    /// Look up `(num_vars, clauses)` in the thread-local
    /// `JIT_BCP_CACHE`. On a hit, return the cached `Arc<Self>`
    /// without invoking the JIT compiler. On a miss, consult the
    /// on-disk cache (when enabled); a disk hit skips module
    /// construction, a disk miss builds the module fresh and persists
    /// the IR text for the next process invocation. Either way the
    /// resulting `Arc<Self>` is inserted into the in-memory cache so
    /// subsequent same-process solves are a cheap Arc clone.
    pub fn compile_or_get_cached(
        num_vars: usize,
        clauses: Vec<Vec<i32>>,
    ) -> Result<Arc<Self>, JitCompileError> {
        let hash = compute_formula_hash(num_vars, &clauses);
        // Collision-resistant identity: verify-on-hit (in-memory) and disk-slot
        // keying both use this so a 64-bit `hash` collision can never serve a
        // different formula's cached artifact.
        let formula_key = formula_sha256(num_vars, &clauses);
        // L2 (ExecutableBuffer cache) needs its own copy of `clauses`
        // because the L3 closure may also consume it.
        let l2_clauses = clauses.clone();
        let l2_num_vars = num_vars;
        JIT_BCP_CACHE.with(|cell| {
            cell.borrow_mut().get_or_compile_with_buffer_disk(
                hash,
                formula_key,
                "scan",
                move |buffer: ExecutableBuffer| -> Result<Self, JitCompileError> {
                    Self::from_replayed_buffer(buffer, l2_num_vars, l2_clauses)
                },
                |disk_text: Option<String>| -> Result<(Self, Vec<u8>, String), JitCompileError> {
                    let (module, ir_text) =
                        load_or_build_module(disk_text, build_bcp_propagate_module);
                    let provider = Self::compile_from_module(&module, num_vars, clauses)?;
                    let buffer_bytes =
                        crate::executable_buffer_cache::serialize_buffer(provider.buffer());
                    Ok((provider, buffer_bytes, ir_text))
                },
            )
        })
    }

    /// Rebuild a provider around a deserialized `ExecutableBuffer`.
    /// The buffer was emitted from `build_bcp_propagate_module()`, so
    /// its entry symbol is the same `ENTRY_NAME` as a fresh compile.
    fn from_replayed_buffer(
        buffer: ExecutableBuffer,
        num_vars: usize,
        clauses: Vec<Vec<i32>>,
    ) -> Result<Self, JitCompileError> {
        let entry: KernelEntry = {
            // SAFETY: executable-buffer disk I/O is admitted only by the
            // process-private unsafe test/benchmark override; production
            // cross-process replay is quarantined. The current-process buffer
            // was emitted by this module builder and its `ENTRY_NAME` symbol
            // carries the documented BCP-kernel ABI. We keep `buffer` owned by
            // `Self` so the executable mapping survives every subsequent call.
            let jit_fn = unsafe { buffer.get_fn_bound::<KernelEntry>(ENTRY_NAME) }
                .ok_or(JitCompileError::MissingEntry(ENTRY_NAME))?;
            jit_fn.into_inner()
        };
        let trail_capacity = (num_vars + 1).max(8);
        let arena = BcpArena::build(num_vars, &clauses, trail_capacity);
        Ok(Self {
            buffer,
            entry,
            arena: RefCell::new(arena),
        })
    }
}

impl SolverKernelProvider for JitBcpKernelProvider {
    fn entry(&self) -> KernelEntry {
        self.entry
    }

    fn ctx_seed(&self) -> KernelCtx {
        // The `header` Vec is heap-allocated; its data pointer is
        // stable for the lifetime of the arena (i.e. for the lifetime
        // of `self`). Borrow through the RefCell briefly to read the
        // pointer + length, then drop the borrow so the kernel call
        // (which writes through the baked-in raw `arena_ptr`) does
        // not race with any subsequent `reset_arena()` borrow_mut.
        let arena = self.arena.borrow();
        let arena_ptr = arena.header.as_ptr() as *mut u8;
        let arena_len = arena.header_byte_len();
        drop(arena);
        KernelCtx {
            arena_ptr,
            arena_len,
            formula_constants_ptr: core::ptr::null(),
            formula_constants_len: 0,
            user_data: core::ptr::null_mut(),
            status: 0,
            implied_literals_out: core::ptr::NonNull::<i32>::dangling().as_ptr(),
            implied_literals_cap: 0,
            implied_literals_len: 0,
            conflicting_clause_index: NO_CONFLICTING_CLAUSE,
            _reserved_pad: 0,
            implied_reasons_out: core::ptr::null_mut(),
            implied_reasons_cap: 0,
            clause_id_translation: core::ptr::null(),
            initial_values: core::ptr::null(),
            initial_values_len: 0,
        }
    }
}

pub struct JitBcpWithDecisionsProvider {
    buffer: ExecutableBuffer,
    entry: KernelEntry,
    arena: RefCell<BcpArena>,
}

impl JitBcpWithDecisionsProvider {
    pub fn compile(
        num_vars: usize,
        clauses: Vec<Vec<i32>>,
        trail_capacity_hint: usize,
    ) -> Result<Self, JitCompileError> {
        let module = build_bcp_propagate_with_decisions_module();
        Self::compile_from_module(&module, num_vars, clauses, trail_capacity_hint)
    }

    fn compile_from_module(
        module: &trust_ir::Module,
        num_vars: usize,
        clauses: Vec<Vec<i32>>,
        trail_capacity_hint: usize,
    ) -> Result<Self, JitCompileError> {
        let config = CompilerConfig::for_host_jit();
        let extern_symbols: HashMap<String, *const u8> = HashMap::new();
        let result = Compiler::new(config).compile_module_to_jit(module, &extern_symbols)?;
        let buffer = result.buffer;

        let entry: KernelEntry = {
            // SAFETY: `KernelEntry` matches the ABI of
            // `bcp_propagate_with_decisions` produced by
            // `build_bcp_propagate_with_decisions_module`. `buffer` is kept
            // owned by `Self` so the executable memory remains live for the
            // lifetime of every call through this provider.
            let jit_fn = unsafe { buffer.get_fn_bound::<KernelEntry>(ENTRY_NAME_WITH_DECISIONS) }
                .ok_or(JitCompileError::MissingEntry(ENTRY_NAME_WITH_DECISIONS))?;
            jit_fn.into_inner()
        };

        let trail_capacity = (num_vars + 1 + trail_capacity_hint).max(8);
        let arena = BcpArena::build(num_vars, &clauses, trail_capacity);

        Ok(Self {
            buffer,
            entry,
            arena: RefCell::new(arena),
        })
    }

    /// Borrow the assignment values vector. Returns a `Ref` that
    /// derefs to `&[i8]`; existing index-style callers continue to
    /// work via auto-deref.
    pub fn arena_values(&self) -> Ref<'_, [i8]> {
        Ref::map(self.arena.borrow(), |a| a.values.as_slice())
    }

    pub fn arena_trail_len(&self) -> u64 {
        self.arena.borrow().trail_len()
    }

    pub fn buffer(&self) -> &ExecutableBuffer {
        &self.buffer
    }

    pub fn entry_fn(&self) -> KernelEntry {
        self.entry
    }

    /// Reset the arena's values/trail in place. Takes `&self` so it
    /// can be invoked through a shared reference (e.g. `Arc<Self>`
    /// handed out by the thread-local compile cache).
    pub fn reset_arena(&self) {
        self.arena.borrow_mut().reset_values_and_trail();
    }

    /// Cached counterpart to [`compile`]. See
    /// [`JitBcpKernelProvider::compile_or_get_cached`] for the
    /// caching contract. Uses `JIT_BCP_WITH_DECISIONS_CACHE` and
    /// the `with-decisions` slot of the on-disk IR cache.
    pub fn compile_or_get_cached(
        num_vars: usize,
        clauses: Vec<Vec<i32>>,
        trail_capacity_hint: usize,
    ) -> Result<Arc<Self>, JitCompileError> {
        let hash = compute_formula_hash(num_vars, &clauses);
        // Collision-resistant identity: verify-on-hit (in-memory) and disk-slot
        // keying both use this so a 64-bit `hash` collision can never serve a
        // different formula's cached artifact.
        let formula_key = formula_sha256(num_vars, &clauses);
        let l2_clauses = clauses.clone();
        let l2_num_vars = num_vars;
        let l2_trail = trail_capacity_hint;
        JIT_BCP_WITH_DECISIONS_CACHE.with(|cell| {
            cell.borrow_mut().get_or_compile_with_buffer_disk(
                hash,
                formula_key,
                "with-decisions",
                move |buffer: ExecutableBuffer| -> Result<Self, JitCompileError> {
                    Self::from_replayed_buffer(buffer, l2_num_vars, l2_clauses, l2_trail)
                },
                |disk_text: Option<String>| -> Result<(Self, Vec<u8>, String), JitCompileError> {
                    let (module, ir_text) = load_or_build_module(disk_text, || {
                        build_bcp_propagate_with_decisions_module()
                    });
                    let provider =
                        Self::compile_from_module(&module, num_vars, clauses, trail_capacity_hint)?;
                    let buffer_bytes =
                        crate::executable_buffer_cache::serialize_buffer(provider.buffer());
                    Ok((provider, buffer_bytes, ir_text))
                },
            )
        })
    }

    fn from_replayed_buffer(
        buffer: ExecutableBuffer,
        num_vars: usize,
        clauses: Vec<Vec<i32>>,
        trail_capacity_hint: usize,
    ) -> Result<Self, JitCompileError> {
        let entry: KernelEntry = {
            // SAFETY: the buffer was produced from
            // `build_bcp_propagate_with_decisions_module()` so
            // `ENTRY_NAME_WITH_DECISIONS` carries the documented
            // KernelEntry ABI. The buffer is owned by `Self` so the
            // executable mapping survives every subsequent call.
            let jit_fn = unsafe { buffer.get_fn_bound::<KernelEntry>(ENTRY_NAME_WITH_DECISIONS) }
                .ok_or(JitCompileError::MissingEntry(ENTRY_NAME_WITH_DECISIONS))?;
            jit_fn.into_inner()
        };
        let trail_capacity = (num_vars + 1 + trail_capacity_hint).max(8);
        let arena = BcpArena::build(num_vars, &clauses, trail_capacity);
        Ok(Self {
            buffer,
            entry,
            arena: RefCell::new(arena),
        })
    }
}

/// JIT'd watched-literal BCP kernel provider.
///
/// Built from `build_bcp_propagate_watched_literal_module`. The provider
/// owns a `BcpWatchedArena` whose layout matches the kernel's documented
/// header offsets. `reset_arena` should be called before every measured
/// invocation when running back-to-back calls so the watch lists and the
/// clause-literal swap state start from a known baseline.
pub struct JitBcpWatchedLiteralKernelProvider {
    buffer: ExecutableBuffer,
    entry: KernelEntry,
    arena: RefCell<BcpWatchedArena>,
}

impl JitBcpWatchedLiteralKernelProvider {
    pub fn compile(
        num_vars: usize,
        clauses: Vec<Vec<i32>>,
        trail_capacity_hint: usize,
    ) -> Result<Self, JitCompileError> {
        let module = build_bcp_propagate_watched_literal_module();
        Self::compile_from_module(&module, num_vars, clauses, trail_capacity_hint)
    }

    fn compile_from_module(
        module: &trust_ir::Module,
        num_vars: usize,
        clauses: Vec<Vec<i32>>,
        trail_capacity_hint: usize,
    ) -> Result<Self, JitCompileError> {
        let config = CompilerConfig::for_host_jit();
        let extern_symbols: HashMap<String, *const u8> = HashMap::new();
        let result = Compiler::new(config).compile_module_to_jit(module, &extern_symbols)?;
        let buffer = result.buffer;

        let entry: KernelEntry = {
            // SAFETY: `KernelEntry` is the documented ABI of the
            // `bcp_propagate_watched_literal` function compiled from
            // `build_bcp_propagate_watched_literal_module`. `buffer` is kept
            // owned by `Self` so the executable memory remains live for
            // every subsequent call through this provider.
            let jit_fn = unsafe { buffer.get_fn_bound::<KernelEntry>(ENTRY_NAME_WATCHED_LITERAL) }
                .ok_or(JitCompileError::MissingEntry(ENTRY_NAME_WATCHED_LITERAL))?;
            jit_fn.into_inner()
        };

        let trail_capacity = (num_vars + 1 + trail_capacity_hint).max(8);
        let arena = BcpWatchedArena::build(num_vars, &clauses, trail_capacity);

        Ok(Self {
            buffer,
            entry,
            arena: RefCell::new(arena),
        })
    }

    /// Borrow the assignment values vector. Returns a `Ref` that
    /// derefs to `&[i8]`; existing index-style callers continue to
    /// work via auto-deref.
    pub fn arena_values(&self) -> Ref<'_, [i8]> {
        Ref::map(self.arena.borrow(), |a| a.values.as_slice())
    }

    pub fn arena_trail_len(&self) -> u64 {
        self.arena.borrow().trail_len()
    }

    pub fn buffer(&self) -> &ExecutableBuffer {
        &self.buffer
    }

    pub fn entry_fn(&self) -> KernelEntry {
        self.entry
    }

    /// Reset the arena's values, trail, and watch-list scratch in
    /// place. Takes `&self` so the cached `Arc<Self>` can drive
    /// repeated resets without exclusive access.
    pub fn reset_arena(&self) {
        self.arena.borrow_mut().reset_arena();
    }

    /// Cached counterpart to [`compile`]. See
    /// [`JitBcpKernelProvider::compile_or_get_cached`] for the
    /// caching contract. Uses `JIT_BCP_WATCHED_LITERAL_CACHE` and
    /// the `watched-literal` slot of the on-disk IR cache. This is
    /// the headline kernel for DDD-v2's primary_jit path.
    pub fn compile_or_get_cached(
        num_vars: usize,
        clauses: Vec<Vec<i32>>,
        trail_capacity_hint: usize,
    ) -> Result<Arc<Self>, JitCompileError> {
        let hash = compute_formula_hash(num_vars, &clauses);
        // Collision-resistant identity: verify-on-hit (in-memory) and disk-slot
        // keying both use this so a 64-bit `hash` collision can never serve a
        // different formula's cached artifact.
        let formula_key = formula_sha256(num_vars, &clauses);
        let l2_clauses = clauses.clone();
        let l2_num_vars = num_vars;
        let l2_trail = trail_capacity_hint;
        JIT_BCP_WATCHED_LITERAL_CACHE.with(|cell| {
            cell.borrow_mut().get_or_compile_with_buffer_disk(
                hash,
                formula_key,
                "watched-literal",
                move |buffer: ExecutableBuffer| -> Result<Self, JitCompileError> {
                    Self::from_replayed_buffer(buffer, l2_num_vars, l2_clauses, l2_trail)
                },
                |disk_text: Option<String>| -> Result<(Self, Vec<u8>, String), JitCompileError> {
                    let (module, ir_text) = load_or_build_module(disk_text, || {
                        build_bcp_propagate_watched_literal_module()
                    });
                    let provider =
                        Self::compile_from_module(&module, num_vars, clauses, trail_capacity_hint)?;
                    let buffer_bytes =
                        crate::executable_buffer_cache::serialize_buffer(provider.buffer());
                    Ok((provider, buffer_bytes, ir_text))
                },
            )
        })
    }

    fn from_replayed_buffer(
        buffer: ExecutableBuffer,
        num_vars: usize,
        clauses: Vec<Vec<i32>>,
        trail_capacity_hint: usize,
    ) -> Result<Self, JitCompileError> {
        let entry: KernelEntry = {
            // SAFETY: replayed buffer originates from
            // `build_bcp_propagate_watched_literal_module()` so its
            // `ENTRY_NAME_WATCHED_LITERAL` symbol carries the
            // documented KernelEntry ABI. The buffer is owned by
            // `Self` so the executable mapping survives subsequent
            // calls.
            let jit_fn = unsafe { buffer.get_fn_bound::<KernelEntry>(ENTRY_NAME_WATCHED_LITERAL) }
                .ok_or(JitCompileError::MissingEntry(ENTRY_NAME_WATCHED_LITERAL))?;
            jit_fn.into_inner()
        };
        let trail_capacity = (num_vars + 1 + trail_capacity_hint).max(8);
        let arena = BcpWatchedArena::build(num_vars, &clauses, trail_capacity);
        Ok(Self {
            buffer,
            entry,
            arena: RefCell::new(arena),
        })
    }
}

impl SolverKernelProvider for JitBcpWatchedLiteralKernelProvider {
    fn entry(&self) -> KernelEntry {
        self.entry
    }

    fn ctx_seed(&self) -> KernelCtx {
        // The `header` Vec is heap-allocated; its data pointer is
        // stable for the lifetime of `self`. We drop the borrow
        // before returning so the kernel call (which only writes
        // through the raw `arena_ptr` we baked in) does not race
        // with any subsequent `reset_arena()` taking `borrow_mut`.
        let arena = self.arena.borrow();
        let arena_ptr = arena.header.as_ptr() as *mut u8;
        let arena_len = arena.header_byte_len();
        drop(arena);
        KernelCtx {
            arena_ptr,
            arena_len,
            formula_constants_ptr: core::ptr::null(),
            formula_constants_len: 0,
            user_data: core::ptr::null_mut(),
            status: 0,
            implied_literals_out: core::ptr::NonNull::<i32>::dangling().as_ptr(),
            implied_literals_cap: 0,
            implied_literals_len: 0,
            conflicting_clause_index: NO_CONFLICTING_CLAUSE,
            _reserved_pad: 0,
            implied_reasons_out: core::ptr::null_mut(),
            implied_reasons_cap: 0,
            clause_id_translation: core::ptr::null(),
            initial_values: core::ptr::null(),
            initial_values_len: 0,
        }
    }
}

impl SolverKernelProvider for JitBcpWithDecisionsProvider {
    fn entry(&self) -> KernelEntry {
        self.entry
    }

    fn ctx_seed(&self) -> KernelCtx {
        // See JitBcpWatchedLiteralKernelProvider::ctx_seed for the
        // RefCell-borrow rationale.
        let arena = self.arena.borrow();
        let arena_ptr = arena.header.as_ptr() as *mut u8;
        let arena_len = arena.header_byte_len();
        drop(arena);
        KernelCtx {
            arena_ptr,
            arena_len,
            formula_constants_ptr: core::ptr::null(),
            formula_constants_len: 0,
            user_data: core::ptr::null_mut(),
            status: 0,
            implied_literals_out: core::ptr::NonNull::<i32>::dangling().as_ptr(),
            implied_literals_cap: 0,
            implied_literals_len: 0,
            conflicting_clause_index: NO_CONFLICTING_CLAUSE,
            _reserved_pad: 0,
            implied_reasons_out: core::ptr::null_mut(),
            implied_reasons_cap: 0,
            clause_id_translation: core::ptr::null(),
            initial_values: core::ptr::null(),
            initial_values_len: 0,
        }
    }
}

/// JIT'd chunked-layout watched-literal BCP kernel provider.
///
/// Built from `build_bcp_propagate_watched_literal_chunked_module`. The
/// provider owns a `BcpWatchedChunkedArena` whose layout matches the
/// kernel's documented header offsets. The arena's `watch_heads` +
/// `watch_nodes` use `O(num_vars + num_clauses)` memory, in contrast to
/// `JitBcpWatchedLiteralKernelProvider`'s `O(num_vars * num_clauses)`
/// fixed-capacity row-major table. The algorithm and the per-call
/// throughput are identical to the fixed-capacity variant (same
/// watched-literal swap policy, same trail/qhead loop, same conflict
/// reporting); only the watch-list data shape differs.
///
/// Use this provider when the comparison target is MicroSAT (which uses
/// the same linked-list layout) so the remaining variable is "native C
/// compiled with -O3" vs "trust-cg JIT'd from trust-ir" — i.e. the
/// chunked layout closes the data-layout-vs-codegen attribution gap.
pub struct JitBcpWatchedLiteralChunkedKernelProvider {
    buffer: ExecutableBuffer,
    entry: KernelEntry,
    arena: RefCell<BcpWatchedChunkedArena>,
}

impl JitBcpWatchedLiteralChunkedKernelProvider {
    pub fn compile(
        num_vars: usize,
        clauses: Vec<Vec<i32>>,
        trail_capacity_hint: usize,
    ) -> Result<Self, JitCompileError> {
        let module = build_bcp_propagate_watched_literal_chunked_module();
        Self::compile_from_module(&module, num_vars, clauses, trail_capacity_hint)
    }

    fn compile_from_module(
        module: &trust_ir::Module,
        num_vars: usize,
        clauses: Vec<Vec<i32>>,
        trail_capacity_hint: usize,
    ) -> Result<Self, JitCompileError> {
        let config = CompilerConfig::for_host_jit();
        let extern_symbols: HashMap<String, *const u8> = HashMap::new();
        let result = Compiler::new(config).compile_module_to_jit(module, &extern_symbols)?;
        let buffer = result.buffer;

        let entry: KernelEntry = {
            // SAFETY: `KernelEntry` is the documented ABI of the
            // `bcp_propagate_watched_literal_chunked` function compiled
            // from `build_bcp_propagate_watched_literal_chunked_module`.
            // The ABI is identical to the fixed-cap watched-literal
            // kernel (the entry signature is shared across all BCP
            // kernels). `buffer` is kept owned by `Self` so the
            // executable memory remains live for every subsequent call
            // through this provider.
            let jit_fn =
                unsafe { buffer.get_fn_bound::<KernelEntry>(ENTRY_NAME_WATCHED_LITERAL_CHUNKED) }
                    .ok_or(JitCompileError::MissingEntry(
                    ENTRY_NAME_WATCHED_LITERAL_CHUNKED,
                ))?;
            jit_fn.into_inner()
        };

        let trail_capacity = (num_vars + 1 + trail_capacity_hint).max(8);
        let arena = BcpWatchedChunkedArena::build(num_vars, &clauses, trail_capacity);

        Ok(Self {
            buffer,
            entry,
            arena: RefCell::new(arena),
        })
    }

    /// Borrow the assignment values vector. Returns a `Ref` that
    /// derefs to `&[i8]`.
    pub fn arena_values(&self) -> Ref<'_, [i8]> {
        Ref::map(self.arena.borrow(), |a| a.values.as_slice())
    }

    pub fn arena_trail_len(&self) -> u64 {
        self.arena.borrow().trail_len()
    }

    pub fn buffer(&self) -> &ExecutableBuffer {
        &self.buffer
    }

    pub fn entry_fn(&self) -> KernelEntry {
        self.entry
    }

    /// Total bytes owned by the chunked watch infrastructure
    /// (`watch_heads` + `watch_nodes`). Used by the bench to report
    /// the chunked-vs-fixed memory delta on the same formula.
    pub fn watch_memory_bytes(&self) -> usize {
        self.arena.borrow().watch_memory_bytes()
    }

    /// Reset the arena's values, trail, and watch-list scratch in
    /// place. Takes `&self` so the cached `Arc<Self>` can drive
    /// repeated resets without exclusive access.
    pub fn reset_arena(&self) {
        self.arena.borrow_mut().reset_arena();
    }

    /// Cached counterpart to [`compile`]. See
    /// [`JitBcpKernelProvider::compile_or_get_cached`] for the
    /// caching contract. Uses `JIT_BCP_WATCHED_LITERAL_CHUNKED_CACHE`
    /// and the `watched-literal-chunked` slot of the on-disk IR cache.
    pub fn compile_or_get_cached(
        num_vars: usize,
        clauses: Vec<Vec<i32>>,
        trail_capacity_hint: usize,
    ) -> Result<Arc<Self>, JitCompileError> {
        let hash = compute_formula_hash(num_vars, &clauses);
        // Collision-resistant identity: verify-on-hit (in-memory) and disk-slot
        // keying both use this so a 64-bit `hash` collision can never serve a
        // different formula's cached artifact.
        let formula_key = formula_sha256(num_vars, &clauses);
        let l2_clauses = clauses.clone();
        let l2_num_vars = num_vars;
        let l2_trail = trail_capacity_hint;
        JIT_BCP_WATCHED_LITERAL_CHUNKED_CACHE.with(|cell| {
            cell.borrow_mut().get_or_compile_with_buffer_disk(
                hash,
                formula_key,
                "watched-literal-chunked",
                move |buffer: ExecutableBuffer| -> Result<Self, JitCompileError> {
                    Self::from_replayed_buffer(buffer, l2_num_vars, l2_clauses, l2_trail)
                },
                |disk_text: Option<String>| -> Result<(Self, Vec<u8>, String), JitCompileError> {
                    let (module, ir_text) = load_or_build_module(disk_text, || {
                        build_bcp_propagate_watched_literal_chunked_module()
                    });
                    let provider =
                        Self::compile_from_module(&module, num_vars, clauses, trail_capacity_hint)?;
                    let buffer_bytes =
                        crate::executable_buffer_cache::serialize_buffer(provider.buffer());
                    Ok((provider, buffer_bytes, ir_text))
                },
            )
        })
    }

    fn from_replayed_buffer(
        buffer: ExecutableBuffer,
        num_vars: usize,
        clauses: Vec<Vec<i32>>,
        trail_capacity_hint: usize,
    ) -> Result<Self, JitCompileError> {
        let entry: KernelEntry = {
            // SAFETY: replayed buffer originates from
            // `build_bcp_propagate_watched_literal_chunked_module()` so
            // its `ENTRY_NAME_WATCHED_LITERAL_CHUNKED` symbol carries
            // the documented KernelEntry ABI. The buffer is owned by
            // `Self` so the executable mapping survives subsequent
            // calls.
            let jit_fn =
                unsafe { buffer.get_fn_bound::<KernelEntry>(ENTRY_NAME_WATCHED_LITERAL_CHUNKED) }
                    .ok_or(JitCompileError::MissingEntry(
                    ENTRY_NAME_WATCHED_LITERAL_CHUNKED,
                ))?;
            jit_fn.into_inner()
        };
        let trail_capacity = (num_vars + 1 + trail_capacity_hint).max(8);
        let arena = BcpWatchedChunkedArena::build(num_vars, &clauses, trail_capacity);
        Ok(Self {
            buffer,
            entry,
            arena: RefCell::new(arena),
        })
    }
}

impl SolverKernelProvider for JitBcpWatchedLiteralChunkedKernelProvider {
    fn entry(&self) -> KernelEntry {
        self.entry
    }

    fn ctx_seed(&self) -> KernelCtx {
        // See JitBcpWatchedLiteralKernelProvider::ctx_seed for the
        // RefCell-borrow rationale.
        let arena = self.arena.borrow();
        let arena_ptr = arena.header.as_ptr() as *mut u8;
        let arena_len = arena.header_byte_len();
        drop(arena);
        KernelCtx {
            arena_ptr,
            arena_len,
            formula_constants_ptr: core::ptr::null(),
            formula_constants_len: 0,
            user_data: core::ptr::null_mut(),
            status: 0,
            implied_literals_out: core::ptr::NonNull::<i32>::dangling().as_ptr(),
            implied_literals_cap: 0,
            implied_literals_len: 0,
            conflicting_clause_index: NO_CONFLICTING_CLAUSE,
            _reserved_pad: 0,
            implied_reasons_out: core::ptr::null_mut(),
            implied_reasons_cap: 0,
            clause_id_translation: core::ptr::null(),
            initial_values: core::ptr::null(),
            initial_values_len: 0,
        }
    }
}

#[cfg(any(target_arch = "aarch64", target_arch = "x86_64"))]
#[cfg(test)]
mod tests {
    use super::*;
    use crate::bcp_baseline::BcpState;
    use crate::bcp_kernel::BcpKernelProvider;
    use crate::solver_kernel_abi::SolverKernelHandle;

    #[test]
    fn compile_round_trip() {
        let clauses: Vec<Vec<i32>> = vec![vec![1, 2], vec![-2, 3]];
        let provider =
            JitBcpKernelProvider::compile(3, clauses).expect("JIT compile of BCP propagate kernel");
        let mut handle = SolverKernelHandle::from_provider(&provider);
        let status = handle.call(&[]);
        assert_eq!(
            status.result, 0,
            "non-unit clauses should not signal conflict"
        );
    }

    #[test]
    fn jit_matches_native_on_unit_clause() {
        let num_vars = 3;
        let clauses = vec![vec![3]];

        let jit_provider =
            JitBcpKernelProvider::compile(num_vars, clauses.clone()).expect("compile");
        let mut jit_handle = SolverKernelHandle::from_provider(&jit_provider);
        let jit_status = jit_handle.call(&[]);

        let mut native_state = BcpState::new(num_vars, clauses);
        let native_provider = BcpKernelProvider::new(&mut native_state);
        let mut native_handle = SolverKernelHandle::from_provider(&native_provider);
        let native_status = native_handle.call(&[]);

        assert_eq!(jit_status.result, native_status.result);
        assert_eq!(jit_status.counters, native_status.counters);
    }

    #[test]
    fn jit_matches_native_on_conflict() {
        let num_vars = 3;
        let clauses = vec![vec![1, 2, 3], vec![-1], vec![-2], vec![-3]];

        let jit_provider =
            JitBcpKernelProvider::compile(num_vars, clauses.clone()).expect("compile");
        let mut jit_handle = SolverKernelHandle::from_provider(&jit_provider);
        let jit_status = jit_handle.call(&[]);

        let mut native_state = BcpState::new(num_vars, clauses);
        let native_provider = BcpKernelProvider::new(&mut native_state);
        let mut native_handle = SolverKernelHandle::from_provider(&native_provider);
        let native_status = native_handle.call(&[]);

        assert_eq!(jit_status.result, 1, "JIT path should detect conflict");
        assert_eq!(jit_status.result, native_status.result);
        assert_eq!(jit_status.counters, native_status.counters);
    }
}
