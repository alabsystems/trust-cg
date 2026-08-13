// trust-cg-jit-matrix/src/jit_parent_loop_kernel.rs - JIT'd parent-loop kernel
// SolverKernelProvider, mirroring the BCP provider shape.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// The compiled kernel writes the per-call mutable arena fields (frontier,
// visited bitmap, counters) through raw pointers baked into the arena's
// header at construction time. Those writes do not flow through Rust's
// borrow checker, so the arena field uses `RefCell` only to let `&self`
// drive resets (matching the BCP-side pattern).

use std::cell::{Ref, RefCell};
use std::collections::HashMap;

use trust_cg_codegen::jit::ExecutableBuffer;
use trust_cg_codegen::{Compiler, CompilerConfig};

use crate::jit_bcp_kernel::JitCompileError;
use crate::parent_loop_baseline::{State, TransitionSystem};
use crate::parent_loop_module_builder::{
    PARENT_LOOP_ENTRY_NAME, ParentLoopArena, build_parent_loop_module,
};
use crate::solver_kernel_abi::{
    KernelCtx, KernelEntry, NO_CONFLICTING_CLAUSE, SolverKernelProvider,
};

/// JIT'd parent-loop kernel provider.
///
/// Compiles `build_parent_loop_module` once at construction and bundles the
/// resulting executable buffer with a `ParentLoopArena` sized for the given
/// transition system. The arena owns every backing allocation referenced
/// from the kernel's address space; the kernel-side raw-pointer writes
/// target the same heap storage either way.
///
/// One `call(input)` invocation runs up to `input.len()` `explore_one_step`
/// iterations; the `input` slice itself is unused. Use `reset_arena` to
/// rewind the per-call mutable state between bench iterations.
pub struct JitParentLoopKernelProvider {
    buffer: ExecutableBuffer,
    entry: KernelEntry,
    arena: RefCell<ParentLoopArena>,
    initial_state: State,
}

impl JitParentLoopKernelProvider {
    pub fn compile(
        num_vars: u32,
        system: TransitionSystem,
        frontier_capacity: usize,
    ) -> Result<Self, JitCompileError> {
        let module = build_parent_loop_module();
        let config = CompilerConfig::for_host_jit();
        let extern_symbols: HashMap<String, *const u8> = HashMap::new();
        let result = Compiler::new(config).compile_module_to_jit(&module, &extern_symbols)?;
        let buffer = result.buffer;

        let entry: KernelEntry = {
            // SAFETY: `KernelEntry` matches the ABI of
            // `parent_loop_explore_steps` produced by
            // `build_parent_loop_module`. `buffer` is kept owned by
            // `Self` so the executable memory remains live for the
            // lifetime of every call through this provider.
            let jit_fn = unsafe { buffer.get_fn_bound::<KernelEntry>(PARENT_LOOP_ENTRY_NAME) }
                .ok_or(JitCompileError::MissingEntry(PARENT_LOOP_ENTRY_NAME))?;
            jit_fn.into_inner()
        };

        let initial_state = system.init;
        let arena = ParentLoopArena::build(num_vars, &system, frontier_capacity);

        Ok(Self {
            buffer,
            entry,
            arena: RefCell::new(arena),
            initial_state,
        })
    }

    pub fn buffer(&self) -> &ExecutableBuffer {
        &self.buffer
    }

    pub fn entry_fn(&self) -> KernelEntry {
        self.entry
    }

    /// Borrow the arena (read-only). Useful for asserting counter values
    /// after `SolverKernelHandle::call`.
    pub fn arena(&self) -> Ref<'_, ParentLoopArena> {
        self.arena.borrow()
    }

    /// Reset the per-call mutable state (frontier, visited, counters) so
    /// the next call starts from the same `init` state the provider was
    /// built with. Takes `&self` to mirror the BCP providers; the
    /// underlying `RefCell` keeps borrows scoped.
    pub fn reset_arena(&self) {
        self.arena.borrow_mut().reset(self.initial_state);
    }

    pub fn parent_count(&self) -> u64 {
        self.arena.borrow().parent_count()
    }
    pub fn generated_count(&self) -> u64 {
        self.arena.borrow().generated_count()
    }
    pub fn parent_digest(&self) -> u64 {
        self.arena.borrow().parent_digest()
    }
    pub fn fingerprint(&self) -> u64 {
        self.arena.borrow().fingerprint()
    }
    pub fn invariant_violations(&self) -> u64 {
        self.arena.borrow().invariant_violations()
    }
    pub fn last_violating_state(&self) -> u64 {
        self.arena.borrow().last_violating_state()
    }
    pub fn frontier_len(&self) -> u64 {
        self.arena.borrow().frontier_len()
    }
}

impl SolverKernelProvider for JitParentLoopKernelProvider {
    fn entry(&self) -> KernelEntry {
        self.entry
    }

    fn ctx_seed(&self) -> KernelCtx {
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
