// trust-cg-jit-matrix/solver_kernel_abi.rs - Solver-kernel JIT ABI scaffold.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

/// Solver-kernel call context.
///
/// # Layout
///
/// `#[repr(C)]` with the following field order. The byte offsets below are
/// load-bearing: the JIT'd kernels emit raw `gep`/`load`/`store`
/// instructions against these offsets, so reordering or resizing fields
/// without also updating `bcp_module_builder.rs` will silently break
/// every JIT kernel.
///
/// ```text
///   +  0: arena_ptr                  (u64 / *mut u8)
///   +  8: arena_len                  (u64)
///   + 16: formula_constants_ptr      (u64 / *const u32)
///   + 24: formula_constants_len      (u64)
///   + 32: user_data                  (u64 / *mut u8)
///   + 40: status                     (u64)
///   + 48: implied_literals_out       (u64 / *mut i32)
///   + 56: implied_literals_cap       (u64)
///   + 64: implied_literals_len       (u64) -- in/out, see contract
///   + 72: conflicting_clause_index   (i32) -- output, see contract
///   + 76: _reserved_pad              (u32) -- alignment padding to 8 bytes
///   + 80: implied_reasons_out        (u64 / *mut i32)
///   + 88: implied_reasons_cap        (u64)
///   + 96: clause_id_translation      (u64 / *const i32)
///   +104: initial_values             (u64 / *const i8)
///   +112: initial_values_len         (u64)
/// ```
///
/// # Initial-values seeding contract
///
/// `initial_values` and `initial_values_len` describe a host-provided
/// slice of `i8` per-variable assignments that the kernel must copy into
/// its arena's `values[]` array on entry, BEFORE processing any input
/// decisions. The slice is indexed by DIMACS variable number, i.e.
/// `initial_values[var]` holds `+1` if `var` is assigned true, `-1` if
/// false, and `0` if unassigned. Slot `0` is unused (DIMACS variables
/// start at 1) and must be `0`.
///
/// The host uses this slot to communicate the **already-settled** trail
/// state to the kernel without re-pushing each settled literal as a
/// decision. The decision-literal input slice should then describe only
/// the **unprocessed** suffix of the trail (i.e. literals MicroSAT has
/// not yet propagated). This split mirrors MicroSAT's native
/// `propagate`, which iterates only `S->trail[S->processed..S->assigned]`
/// and leaves the pre-existing trail prefix untouched.
///
/// When `initial_values` is `null` or `initial_values_len` is `0`, the
/// kernel uses the arena's zero-initialised `values[]` array (the
/// historical behaviour, equivalent to "no prior assignments").
///
/// # Implied-literals output contract
///
/// Before each `KernelEntry` call, the caller is expected to:
///   1. Set `implied_literals_out` to a non-null `*mut i32` buffer (a
///      dangling-but-non-null pointer is acceptable when `implied_literals_cap == 0`).
///   2. Set `implied_literals_cap` to the buffer capacity in `i32` elements.
///      A safe upper bound for any well-formed call is `num_vars * 2`.
///   3. Reset `implied_literals_len` to `0`.
///
/// On return, `implied_literals_len` holds either:
///   - The number of DIMACS-signed literals newly assigned during the call,
///     written in propagation order to `implied_literals_out[0..len]`.
///   - `usize::MAX` if the kernel would have written more entries than
///     `implied_literals_cap` could hold. When overflow is signalled, the
///     contents of the output buffer are unspecified.
///
/// Decode-phase assignments (from kernels that consume an `input: &[u32]`
/// slice of decision literals) are NOT included in the implied-literals
/// stream: only literals produced by BCP propagation are appended.
///
/// # Implied-reasons output contract
///
/// `implied_reasons_out[i]` corresponds 1:1 with `implied_literals_out[i]`
/// and holds the "external clause id" of the clause that forced the
/// literal at index `i`. The literal and reason buffers always increment
/// in lockstep, so the count is `implied_literals_len` (there is no
/// separate `implied_reasons_len` field).
///
/// The semantic of the reason id is **host-defined**: the kernel emits
/// whatever value the host has registered in the clause-id translation
/// table (`clause_id_translation`). In passthrough mode (translation
/// table `null`) the kernel writes the JIT-internal clause index directly.
/// Typical hosts (e.g. MicroSAT) register `S->DB` offset+1 for each
/// clause so that the buffer feeds directly into `S->reason[var]`.
///
/// Graceful degradation: if `implied_reasons_out` is `null`, the kernel
/// skips reason writes (literal writes still occur). If the literal
/// buffer overflows, the reason buffer follows the same sticky-overflow
/// signal via the shared `implied_literals_len` counter. The reason
/// buffer is assumed to be at least as large as `implied_literals_cap`;
/// the kernel does NOT independently bounds-check `implied_reasons_cap`,
/// it is stored only as a sanity field for the host's own bookkeeping.
///
/// # Clause-id translation contract
///
/// The kernel knows only its own clause indices (0..num_clauses in arena
/// order). When a literal is implied by JIT clause index `c`, the kernel
/// reads `id = clause_id_translation[c]` (a `*const i32`) and writes that
/// `id` to `implied_reasons_out[i]`. If `clause_id_translation` is `null`,
/// the kernel writes `c` directly (passthrough). The table is set once
/// after JIT compile (not per-call) via
/// `SolverKernelHandle::set_clause_id_translation`.
///
/// # Conflicting-clause contract
///
/// On a successful call:
///   - When `result == 1` (conflict), `conflicting_clause_index` holds the
///     0-based clause index that became all-false during the call.
///   - When `result == 0` (ok) or `result == 2` (decode error), the field
///     is unspecified.
///
/// The caller is expected to ignore `conflicting_clause_index` unless
/// `result == 1`. The field is initialized to `-1` by `SolverKernelHandle`
/// at construction time and re-initialized to `-1` between calls by
/// `SolverKernelHandle::call`.
#[repr(C)]
pub struct KernelCtx {
    /// Scratch arena base pointer the solver kernel may freely read and write.
    pub arena_ptr: *mut u8,
    /// Length in bytes of the scratch arena referenced by `arena_ptr`.
    pub arena_len: usize,
    /// Read-only formula constants (literal table, clause indices, etc.).
    pub formula_constants_ptr: *const u32,
    /// Length in `u32` elements of the formula constants buffer.
    pub formula_constants_len: usize,
    /// Opaque user data pointer reserved for harness-side bookkeeping.
    pub user_data: *mut u8,
    /// Mutable status word the kernel may stamp during execution.
    pub status: u64,
    /// Output buffer for the implied-literals stream. See type-level
    /// "Implied-literals output contract" for the full protocol.
    pub implied_literals_out: *mut i32,
    /// Capacity of `implied_literals_out` in `i32` elements.
    pub implied_literals_cap: usize,
    /// Count of literals written to `implied_literals_out` (or
    /// `usize::MAX` to signal overflow). See type-level contract.
    pub implied_literals_len: usize,
    /// 0-based clause index that became false on conflict (`result == 1`).
    /// Unspecified for other result codes. `-1` sentinel means "no conflict".
    pub conflicting_clause_index: i32,
    /// Padding so the struct ends on an 8-byte boundary for predictable
    /// downstream arena layout.
    pub _reserved_pad: u32,
    /// Output buffer for the per-implied-literal "reason clause id"
    /// stream. Parallel to `implied_literals_out`. May be `null` to
    /// request graceful degradation (literals still written; reasons
    /// skipped). See type-level "Implied-reasons output contract".
    pub implied_reasons_out: *mut i32,
    /// Capacity of `implied_reasons_out` in `i32` elements. Stored for
    /// host bookkeeping; the kernel itself does NOT bounds-check this
    /// field — it relies on the shared `implied_literals_len` overflow
    /// signal.
    pub implied_reasons_cap: usize,
    /// Optional `*const i32` table of length `num_clauses` mapping each
    /// JIT clause index to a host-defined external id (typically a
    /// `S->DB` offset+1 for MicroSAT). When `null`, the kernel emits
    /// JIT clause indices directly (passthrough mode). See type-level
    /// "Clause-id translation contract".
    pub clause_id_translation: *const i32,
    /// Optional `*const i8` slice of length `initial_values_len` holding
    /// the per-variable initial assignment state to seed the kernel's
    /// `values[]` array on entry. See type-level "Initial-values seeding
    /// contract". `null` (with len `0`) skips the seed and uses the
    /// arena's zero-initialised values, matching historical behaviour.
    pub initial_values: *const i8,
    /// Length of `initial_values` in `i8` elements. The kernel reads at
    /// most `min(initial_values_len, num_vars + 1)` bytes when seeding.
    pub initial_values_len: usize,
}

pub type KernelEntry =
    unsafe extern "C" fn(ctx: *mut KernelCtx, input: *const u32, len: usize) -> u64;

/// Packed status word layout returned by a solver kernel.
///
/// ```text
///  63                           32 31                            0
/// +-------------------------------+-------------------------------+
/// | side-channel counters (hi32)  | result code           (lo32)  |
/// +-------------------------------+-------------------------------+
/// ```
///
/// - Bits `[0, 32)` hold the kernel result code (UNSAT/SAT/UNKNOWN/error tag).
/// - Bits `[32, 64)` hold an opaque side-channel counter (propagations,
///   conflicts, or any monotone telemetry the kernel chooses to expose).
pub const KERNEL_RESULT_MASK: u64 = 0x0000_0000_FFFF_FFFF;
/// Shift applied to extract the side-channel counter half of the status word.
pub const KERNEL_COUNTER_SHIFT: u32 = 32;
/// Mask applied after `KERNEL_COUNTER_SHIFT` to recover the side-channel counter.
pub const KERNEL_COUNTER_MASK: u64 = 0x0000_0000_FFFF_FFFF;

/// Sentinel value written to `KernelCtx::conflicting_clause_index` between
/// calls to indicate "no conflict reported yet."
pub const NO_CONFLICTING_CLAUSE: i32 = -1;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct KernelStatus {
    /// Low 32 bits of the packed status word.
    pub result: u32,
    /// High 32 bits of the packed status word.
    pub counters: u32,
    /// Clause index that became false on conflict (`result == 1`); `-1`
    /// otherwise. Populated from `KernelCtx::conflicting_clause_index`
    /// after the kernel call returns.
    pub conflicting_clause_index: i32,
    /// Number of implied literals the kernel newly assigned during the
    /// call, written to the caller-supplied `implied_literals_out` buffer.
    /// `usize::MAX` indicates the caller-supplied buffer was too small;
    /// the buffer contents are unspecified in that case. Populated from
    /// `KernelCtx::implied_literals_len` after the kernel call returns.
    pub implied_literals_len: usize,
    /// `true` when the host installed an `implied_reasons_out` buffer
    /// AND the kernel populated it during this call. The count of
    /// valid reasons equals `implied_literals_len` (when not overflow).
    pub implied_reasons_present: bool,
}

impl KernelStatus {
    /// Build a status snapshot from the packed return word alone. The
    /// `conflicting_clause_index`, `implied_literals_len`, and
    /// `implied_reasons_present` fields are left at "no information
    /// available" sentinels (`-1`, `0`, and `false`).
    pub const fn from_packed(packed: u64) -> Self {
        Self {
            result: (packed & KERNEL_RESULT_MASK) as u32,
            counters: ((packed >> KERNEL_COUNTER_SHIFT) & KERNEL_COUNTER_MASK) as u32,
            conflicting_clause_index: NO_CONFLICTING_CLAUSE,
            implied_literals_len: 0,
            implied_reasons_present: false,
        }
    }

    /// Build a status snapshot from the packed return word combined with
    /// the post-call `KernelCtx` side channels.
    pub fn from_packed_and_ctx(packed: u64, ctx: &KernelCtx) -> Self {
        let mut status = Self::from_packed(packed);
        status.conflicting_clause_index = ctx.conflicting_clause_index;
        status.implied_literals_len = ctx.implied_literals_len;
        // `implied_reasons_present` is true iff the host installed a
        // non-null reasons buffer AND the kernel actually wrote at
        // least one entry (or signalled overflow on a non-empty stream).
        status.implied_reasons_present = !ctx.implied_reasons_out.is_null()
            && (ctx.implied_literals_len != 0)
            && (ctx.implied_reasons_cap != 0);
        status
    }

    pub const fn to_packed(self) -> u64 {
        (self.result as u64) | ((self.counters as u64) << KERNEL_COUNTER_SHIFT)
    }
}

pub trait SolverKernelProvider {
    fn entry(&self) -> KernelEntry;
    fn ctx_seed(&self) -> KernelCtx;
}

pub struct SolverKernelHandle {
    entry: KernelEntry,
    ctx: Box<KernelCtx>,
}

impl SolverKernelHandle {
    pub fn from_provider<P: SolverKernelProvider>(provider: &P) -> Self {
        let mut ctx = Box::new(provider.ctx_seed());
        // Establish ctx-side defaults that callers don't have to think
        // about: the conflict-index field starts at -1, and the
        // implied-literals counter starts at 0 with an empty (but
        // non-null) buffer so kernels can store unconditionally only
        // when the caller has actually installed a buffer.
        ctx.conflicting_clause_index = NO_CONFLICTING_CLAUSE;
        ctx.implied_literals_out = core::ptr::NonNull::<i32>::dangling().as_ptr();
        ctx.implied_literals_cap = 0;
        ctx.implied_literals_len = 0;
        // Reasons buffer defaults to `null` so the kernel's null-check
        // branch fires (graceful degradation). The clause-id translation
        // table also defaults to `null` so the kernel emits JIT clause
        // indices directly (passthrough mode).
        ctx.implied_reasons_out = core::ptr::null_mut();
        ctx.implied_reasons_cap = 0;
        ctx.clause_id_translation = core::ptr::null();
        // Initial-values default: null/0 means "use the arena's
        // zero-initialised values" (historical behaviour). Hosts that
        // need to seed the kernel with already-settled trail state call
        // `set_initial_values` before `call`.
        ctx.initial_values = core::ptr::null();
        ctx.initial_values_len = 0;
        Self {
            entry: provider.entry(),
            ctx,
        }
    }

    /// Install (or clear) a caller-supplied output buffer for the
    /// implied-literals stream produced by `call(...)`. The buffer must
    /// remain valid until the next `call(...)` returns; the typical
    /// pattern is for the host to reuse one buffer of size `num_vars * 2`
    /// across many calls.
    ///
    /// Calling this with an empty slice clears any previously installed
    /// buffer and leaves the per-call overflow signal active (the kernel
    /// will set `implied_literals_len = usize::MAX` on the very first
    /// propagation, which the caller can ignore).
    pub fn set_implied_literals_buffer(&mut self, buf: &mut [i32]) {
        let ptr = if buf.is_empty() {
            core::ptr::NonNull::<i32>::dangling().as_ptr()
        } else {
            buf.as_mut_ptr()
        };
        self.ctx.implied_literals_out = ptr;
        self.ctx.implied_literals_cap = buf.len();
        self.ctx.implied_literals_len = 0;
    }

    /// Install (or clear) a caller-supplied output buffer for the
    /// per-implied-literal "reason clause id" stream produced by
    /// `call(...)`. Parallel to `set_implied_literals_buffer`: index `i`
    /// in this buffer holds the reason id for the literal at index `i`
    /// in the literals buffer. The buffer must remain valid until the
    /// next `call(...)` returns.
    ///
    /// Calling this with an empty slice clears any previously installed
    /// buffer; the kernel will skip reason writes for the next call
    /// (graceful degradation — literal writes still occur).
    pub fn set_implied_reasons_buffer(&mut self, buf: &mut [i32]) {
        let (ptr, cap) = if buf.is_empty() {
            (core::ptr::null_mut::<i32>(), 0usize)
        } else {
            (buf.as_mut_ptr(), buf.len())
        };
        self.ctx.implied_reasons_out = ptr;
        self.ctx.implied_reasons_cap = cap;
    }

    /// Install (or clear) the host-defined clause-id translation table.
    /// `table[i]` is the external id (typically MicroSAT's `S->DB`
    /// offset+1) that the kernel emits whenever JIT clause index `i`
    /// implies a literal. Passing an empty slice clears the table and
    /// reverts the kernel to passthrough mode (emit JIT clause indices
    /// directly).
    ///
    /// The table is read by the kernel on every implied-literal write
    /// site, so it must remain valid for as long as subsequent
    /// `call(...)` invocations may fire. The host typically registers
    /// the table once after JIT compile (not per-call).
    pub fn set_clause_id_translation(&mut self, table: &[i32]) {
        self.ctx.clause_id_translation = if table.is_empty() {
            core::ptr::null()
        } else {
            table.as_ptr()
        };
    }

    /// Install (or clear) the host-supplied initial-values slice. See
    /// `KernelCtx`'s "Initial-values seeding contract" for the protocol.
    /// `initial_values[var]` is the i8 assignment value for DIMACS
    /// variable `var` (`+1` true, `-1` false, `0` unassigned); slot `0`
    /// is unused and must be `0`. The slice must remain valid until the
    /// next `call(...)` returns. Passing an empty slice clears the
    /// previously-installed pointer and reverts the kernel to its
    /// historical "arena-zeroed values" behaviour.
    pub fn set_initial_values(&mut self, buf: &[i8]) {
        let (ptr, len) = if buf.is_empty() {
            (core::ptr::null::<i8>(), 0usize)
        } else {
            (buf.as_ptr(), buf.len())
        };
        self.ctx.initial_values = ptr;
        self.ctx.initial_values_len = len;
    }

    pub fn call(&mut self, input: &[u32]) -> KernelStatus {
        // Reset per-call output state so the caller observes a clean
        // snapshot regardless of what the previous call wrote.
        self.ctx.conflicting_clause_index = NO_CONFLICTING_CLAUSE;
        self.ctx.implied_literals_len = 0;

        let ctx_ptr: *mut KernelCtx = &mut *self.ctx;
        let input_ptr = input.as_ptr();
        let input_len = input.len();
        // SAFETY: `ctx_ptr` is derived from a live `Box<KernelCtx>` owned by
        // `self` for the duration of this call, `input_ptr` is valid for
        // `input_len` `u32` reads because it comes from a Rust slice, and the
        // kernel ABI requires the callee to honor those provenance bounds.
        let packed = unsafe { (self.entry)(ctx_ptr, input_ptr, input_len) };
        KernelStatus::from_packed_and_ctx(packed, &self.ctx)
    }

    pub fn ctx(&self) -> &KernelCtx {
        &self.ctx
    }

    pub fn ctx_mut(&mut self) -> &mut KernelCtx {
        &mut self.ctx
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    unsafe extern "C" fn test_kernel(_ctx: *mut KernelCtx, _input: *const u32, _len: usize) -> u64 {
        ((0xCAFEBABE_u64) << KERNEL_COUNTER_SHIFT) | 0x0000_0007_u64
    }

    struct TestProvider;

    impl SolverKernelProvider for TestProvider {
        fn entry(&self) -> KernelEntry {
            test_kernel
        }

        fn ctx_seed(&self) -> KernelCtx {
            KernelCtx {
                arena_ptr: core::ptr::null_mut(),
                arena_len: 0,
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

    #[test]
    fn status_round_trip_through_wrapper() {
        let mut handle = SolverKernelHandle::from_provider(&TestProvider);
        let input: [u32; 3] = [1, 2, 3];
        let status = handle.call(&input);
        assert_eq!(status.result, 0x0000_0007);
        assert_eq!(status.counters, 0xCAFEBABE);
        assert_eq!(status.conflicting_clause_index, NO_CONFLICTING_CLAUSE);
        assert_eq!(status.implied_literals_len, 0);

        let packed = status.to_packed();
        assert_eq!(packed & KERNEL_RESULT_MASK, 0x0000_0007);
        assert_eq!(
            (packed >> KERNEL_COUNTER_SHIFT) & KERNEL_COUNTER_MASK,
            0xCAFEBABE
        );
    }

    #[test]
    fn ctx_layout_offsets_are_stable() {
        // The JIT'd kernels hard-code these offsets via load/store
        // sequences in `bcp_module_builder.rs`. If any of these
        // `assert_eq!` calls fires, the builder code MUST be updated
        // in lockstep.
        let ctx = KernelCtx {
            arena_ptr: core::ptr::null_mut(),
            arena_len: 0,
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
        };
        let base = (&ctx) as *const KernelCtx as usize;
        assert_eq!(((&ctx.arena_ptr) as *const _ as usize) - base, 0);
        assert_eq!(((&ctx.arena_len) as *const _ as usize) - base, 8);
        assert_eq!(
            ((&ctx.formula_constants_ptr) as *const _ as usize) - base,
            16
        );
        assert_eq!(
            ((&ctx.formula_constants_len) as *const _ as usize) - base,
            24
        );
        assert_eq!(((&ctx.user_data) as *const _ as usize) - base, 32);
        assert_eq!(((&ctx.status) as *const _ as usize) - base, 40);
        assert_eq!(
            ((&ctx.implied_literals_out) as *const _ as usize) - base,
            48
        );
        assert_eq!(
            ((&ctx.implied_literals_cap) as *const _ as usize) - base,
            56
        );
        assert_eq!(
            ((&ctx.implied_literals_len) as *const _ as usize) - base,
            64
        );
        assert_eq!(
            ((&ctx.conflicting_clause_index) as *const _ as usize) - base,
            72
        );
        // New reason-emission ABI slots (extensions to the kernel ABI).
        assert_eq!(((&ctx.implied_reasons_out) as *const _ as usize) - base, 80);
        assert_eq!(((&ctx.implied_reasons_cap) as *const _ as usize) - base, 88);
        assert_eq!(
            ((&ctx.clause_id_translation) as *const _ as usize) - base,
            96
        );
        // Initial-values seeding slots (extensions to the kernel ABI).
        assert_eq!(((&ctx.initial_values) as *const _ as usize) - base, 104);
        assert_eq!(((&ctx.initial_values_len) as *const _ as usize) - base, 112);
    }
}
