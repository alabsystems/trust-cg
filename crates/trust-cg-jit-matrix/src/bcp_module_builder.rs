// trust-cg-jit-matrix/src/bcp_module_builder.rs - Shared BCP trust_ir module builder + arena layout.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use trust_ir::{BinOp, BlockId, ICmpOp, Ty, ValueId};
use trust_ir_build::{FunctionBuilder, ModuleBuilder};

pub const ENTRY_NAME: &str = "bcp_propagate_scan";
pub const ENTRY_NAME_WITH_DECISIONS: &str = "bcp_propagate_with_decisions";
pub const ENTRY_NAME_WATCHED_LITERAL: &str = "bcp_propagate_watched_literal";
/// Chunked-layout watched-literal kernel entry symbol. Authored by
/// `build_bcp_propagate_watched_literal_chunked_module`. Same ABI as
/// `ENTRY_NAME_WATCHED_LITERAL` (KernelEntry) — only the arena layout
/// differs (linked-list watch lists in a shared node pool instead of
/// the per-literal fixed-capacity row-major table).
pub const ENTRY_NAME_WATCHED_LITERAL_CHUNKED: &str = "bcp_propagate_watched_literal_chunked";

pub const BCP_RESULT_OK: u32 = 0;
pub const BCP_RESULT_CONFLICT: u32 = 1;
pub const BCP_RESULT_DECODE_ERROR: u32 = 2;

/// Byte offsets into `solver_kernel_abi::KernelCtx` that the JIT'd
/// kernels load/store directly. Kept here as `i64`-indexed slots
/// because every field is 8 bytes wide (with `conflicting_clause_index`
/// occupying the low 32 bits of slot 9).
///
/// MUST stay in lockstep with the field order in `KernelCtx` (the
/// `ctx_layout_offsets_are_stable` test in `solver_kernel_abi.rs`
/// pins the byte offsets and will fire if the layout drifts).
pub const CTX_SLOT_ARENA_PTR: i128 = 0;
pub const CTX_SLOT_IMPLIED_OUT: i128 = 6;
pub const CTX_SLOT_IMPLIED_CAP: i128 = 7;
pub const CTX_SLOT_IMPLIED_LEN: i128 = 8;
pub const CTX_SLOT_CONFLICTING_CLAUSE_INDEX: i128 = 9;
/// `implied_reasons_out: *mut i32` — byte offset 80 (slot 10).
pub const CTX_SLOT_IMPLIED_REASONS_OUT: i128 = 10;
/// `implied_reasons_cap: usize` — byte offset 88 (slot 11). Stored for
/// host bookkeeping; the kernel does NOT bounds-check against this
/// field, the literals counter overflow signal carries the reasons
/// stream along with it (the two streams share an index).
pub const CTX_SLOT_IMPLIED_REASONS_CAP: i128 = 11;
/// `clause_id_translation: *const i32` — byte offset 96 (slot 12).
/// When `null`, the kernel emits JIT clause indices directly.
pub const CTX_SLOT_CLAUSE_ID_TRANSLATION: i128 = 12;
/// `initial_values: *const i8` — byte offset 104 (slot 13). When `null`,
/// the kernel uses the arena's zero-initialised values (historical
/// behaviour). When non-null, the kernel copies the first
/// `min(initial_values_len, num_vars + 1)` bytes into `values[]` on
/// entry, before processing input decisions.
pub const CTX_SLOT_INITIAL_VALUES_PTR: i128 = 13;
/// `initial_values_len: usize` — byte offset 112 (slot 14). Length in
/// `i8` elements of the `initial_values` buffer.
pub const CTX_SLOT_INITIAL_VALUES_LEN: i128 = 14;

/// Emit the per-propagation "record implied literal" IR sequence and
/// continue control flow at `cont_block`.
///
/// Logic (matches `bcp_kernel::record_implied_literal`):
///
/// ```text
///   let out = load ptr from ctx[CTX_SLOT_IMPLIED_OUT]
///   let cap = load i64 from ctx[CTX_SLOT_IMPLIED_CAP]
///   let len = load i64 from ctx[CTX_SLOT_IMPLIED_LEN]
///   if len < cap (unsigned):
///       out[len] = lit_i32
///       if reason_ci is Some(ci) and ctx.implied_reasons_out is non-null:
///           let table = ctx.clause_id_translation
///           let id = (table == null) ? ci_i32 : table[ci]
///           ctx.implied_reasons_out[len] = id
///       store len + 1 to ctx[CTX_SLOT_IMPLIED_LEN]
///   else:
///       store usize::MAX to ctx[CTX_SLOT_IMPLIED_LEN]
///   br cont_block(cont_args)
/// ```
///
/// The implementation reads the three ctx slots fresh on every call so
/// that prior overflow signals (`len == usize::MAX`) remain sticky:
/// `usize::MAX < cap` is always false, so we re-enter the overflow arm
/// and harmlessly re-store `usize::MAX`.
///
/// `cont_args` are evaluated in the caller's block before this helper
/// is invoked, so they are visible in both inner branches via SSA
/// dominance (the inner blocks merge into `cont_block` which already
/// has matching block params).
///
/// When `reason_ci_i64` is `None` the helper writes only the literal
/// (matching the pre-reasons CCC contract). When `Some(ci)`, the helper
/// also emits the per-propagation reason write described above; `ci`
/// must be an `I64` value holding the JIT clause index of the clause
/// that forced the literal. Each kernel passes the clause-index value
/// that is in scope at the propagation site.
fn emit_record_implied_literal(
    fb: &mut FunctionBuilder<'_>,
    ctx_ptr: ValueId,
    lit_i32: ValueId,
    reason_ci_i64: Option<ValueId>,
    cont_block: BlockId,
    cont_args: Vec<ValueId>,
) {
    // Slot pointers into the ctx.
    let imp_out_idx = fb.iconst(Ty::I64, CTX_SLOT_IMPLIED_OUT);
    let imp_cap_idx = fb.iconst(Ty::I64, CTX_SLOT_IMPLIED_CAP);
    let imp_len_idx = fb.iconst(Ty::I64, CTX_SLOT_IMPLIED_LEN);

    let imp_out_slot_ptr = fb.gep(Ty::I64, ctx_ptr, vec![imp_out_idx]);
    let imp_cap_slot_ptr = fb.gep(Ty::I64, ctx_ptr, vec![imp_cap_idx]);
    let imp_len_slot_ptr = fb.gep(Ty::I64, ctx_ptr, vec![imp_len_idx]);

    let out_addr = fb.load(Ty::I64, imp_out_slot_ptr);
    let out_ptr = fb.cast(trust_ir::CastOp::IntToPtr, Ty::I64, Ty::Ptr, out_addr);
    let cap = fb.load(Ty::I64, imp_cap_slot_ptr);
    let len = fb.load(Ty::I64, imp_len_slot_ptr);

    let in_bounds = fb.icmp(ICmpOp::Ult, Ty::I64, len, cap);

    let do_write = fb.create_block();
    let do_overflow = fb.create_block();
    fb.condbr(in_bounds, do_write, vec![], do_overflow, vec![]);

    // Write branch: out[len] = lit; ctx.len = len + 1.
    fb.switch_to_block(do_write);
    let slot_ptr = fb.gep(Ty::I32, out_ptr, vec![len]);
    fb.store(Ty::I32, slot_ptr, lit_i32);

    // Optional reason write: load reasons_out, branch on null, look up
    // translation, store the resulting id at index `len`.
    if let Some(reason_ci) = reason_ci_i64 {
        emit_record_implied_reason(fb, ctx_ptr, reason_ci, len);
    }

    let one_i64 = fb.iconst(Ty::I64, 1);
    let new_len = fb.binop(BinOp::Add, Ty::I64, len, one_i64);
    // Re-derive the ctx slot pointer in this block (cross-block SSA via
    // rematerialization works, but a fresh GEP keeps the IR easy to
    // audit and matches the per-block style used elsewhere in this file).
    let imp_len_idx_w = fb.iconst(Ty::I64, CTX_SLOT_IMPLIED_LEN);
    let imp_len_slot_w = fb.gep(Ty::I64, ctx_ptr, vec![imp_len_idx_w]);
    fb.store(Ty::I64, imp_len_slot_w, new_len);
    fb.br(cont_block, cont_args.clone());

    // Overflow branch: store usize::MAX (-1 as i64).
    fb.switch_to_block(do_overflow);
    let max_len = fb.iconst(Ty::I64, -1);
    let imp_len_idx_o = fb.iconst(Ty::I64, CTX_SLOT_IMPLIED_LEN);
    let imp_len_slot_o = fb.gep(Ty::I64, ctx_ptr, vec![imp_len_idx_o]);
    fb.store(Ty::I64, imp_len_slot_o, max_len);
    fb.br(cont_block, cont_args);
}

/// Emit the per-propagation reason write into ctx's reasons buffer.
/// Assumes the caller has already established `len < cap` for the
/// literals buffer (so the index is in bounds for the reasons buffer
/// too — the ABI documents reasons_cap as "host bookkeeping; sized to
/// match cap"). When reasons_out is null, no write occurs; when the
/// translation table is null, the JIT clause index is written directly
/// (passthrough mode); otherwise the translated id is written.
///
/// `idx` is the literal-buffer index where the corresponding literal
/// was just written; the reason write targets the same index.
fn emit_record_implied_reason(
    fb: &mut FunctionBuilder<'_>,
    ctx_ptr: ValueId,
    reason_ci_i64: ValueId,
    idx: ValueId,
) {
    // Load `implied_reasons_out` and short-circuit on null.
    let reasons_out_idx_c = fb.iconst(Ty::I64, CTX_SLOT_IMPLIED_REASONS_OUT);
    let reasons_out_slot = fb.gep(Ty::I64, ctx_ptr, vec![reasons_out_idx_c]);
    let reasons_out_addr = fb.load(Ty::I64, reasons_out_slot);
    let zero_i64 = fb.iconst(Ty::I64, 0);
    let reasons_present = fb.icmp(ICmpOp::Ne, Ty::I64, reasons_out_addr, zero_i64);

    let do_emit = fb.create_block();
    let do_skip = fb.create_block();
    fb.condbr(reasons_present, do_emit, vec![], do_skip, vec![]);

    fb.switch_to_block(do_emit);
    let reasons_ptr = fb.cast(
        trust_ir::CastOp::IntToPtr,
        Ty::I64,
        Ty::Ptr,
        reasons_out_addr,
    );

    // Load `clause_id_translation` and branch on null.
    let xlate_idx_c = fb.iconst(Ty::I64, CTX_SLOT_CLAUSE_ID_TRANSLATION);
    let xlate_slot = fb.gep(Ty::I64, ctx_ptr, vec![xlate_idx_c]);
    let xlate_addr = fb.load(Ty::I64, xlate_slot);
    let zero_i64_b = fb.iconst(Ty::I64, 0);
    let xlate_present = fb.icmp(ICmpOp::Ne, Ty::I64, xlate_addr, zero_i64_b);

    let do_translate = fb.create_block();
    let do_passthrough = fb.create_block();
    fb.condbr(xlate_present, do_translate, vec![], do_passthrough, vec![]);

    // Passthrough: write the JIT clause index directly (truncated to i32).
    fb.switch_to_block(do_passthrough);
    let ci_i32_pass = fb.cast(trust_ir::CastOp::Trunc, Ty::I64, Ty::I32, reason_ci_i64);
    let slot_pass = fb.gep(Ty::I32, reasons_ptr, vec![idx]);
    fb.store(Ty::I32, slot_pass, ci_i32_pass);
    fb.br(do_skip, vec![]);

    // Translate: load `clause_id_translation[reason_ci]` as i32 and
    // write that value to reasons_out[idx].
    fb.switch_to_block(do_translate);
    let xlate_ptr = fb.cast(trust_ir::CastOp::IntToPtr, Ty::I64, Ty::Ptr, xlate_addr);
    let xlate_entry_ptr = fb.gep(Ty::I32, xlate_ptr, vec![reason_ci_i64]);
    let xlated_id = fb.load(Ty::I32, xlate_entry_ptr);
    let slot_tr = fb.gep(Ty::I32, reasons_ptr, vec![idx]);
    fb.store(Ty::I32, slot_tr, xlated_id);
    fb.br(do_skip, vec![]);

    // Merge point — caller continues in do_skip (the next IR after this
    // helper). We rejoin a single block to keep dominance simple for
    // any subsequent stores by the caller.
    fb.switch_to_block(do_skip);
}

/// Emit the IR to write the conflict-clause index into the ctx side
/// channel `KernelCtx::conflicting_clause_index`. Called just before
/// returning a conflict packed status word; the field at byte offset 72
/// is `i32` so we store an i32 directly through a Ptr derived from the
/// ctx's slot-9 pointer.
fn emit_set_conflicting_clause_index(
    fb: &mut FunctionBuilder<'_>,
    ctx_ptr: ValueId,
    ci_i64: ValueId,
) {
    let ci_i32 = fb.cast(trust_ir::CastOp::Trunc, Ty::I64, Ty::I32, ci_i64);
    let slot_idx = fb.iconst(Ty::I64, CTX_SLOT_CONFLICTING_CLAUSE_INDEX);
    let slot_ptr = fb.gep(Ty::I64, ctx_ptr, vec![slot_idx]);
    fb.store(Ty::I32, slot_ptr, ci_i32);
}

/// Emit the IR that seeds the arena's `values[]` array from the host's
/// `initial_values` slice in the ctx, before any decision decoding runs.
///
/// Logic (matches the host-side contract documented on
/// `KernelCtx::initial_values`):
///
/// ```text
///   let iv_ptr = load ptr from ctx[CTX_SLOT_INITIAL_VALUES_PTR]
///   if iv_ptr == null: br after_seed
///   let iv_len = load i64 from ctx[CTX_SLOT_INITIAL_VALUES_LEN]
///   // copy min(iv_len, num_vars + 1) bytes from iv_ptr into values_ptr
///   for i in 0 .. min(iv_len, num_vars + 1):
///       values_ptr[i] = iv_ptr[i]
///   br after_seed
/// ```
///
/// `values_ptr` is the arena's `values` base pointer (already cast to
/// `Ty::Ptr` by the caller). `num_vars` is the arena-resident `i64`
/// variable count. `ctx_ptr` is the kernel context pointer. The
/// `after_seed` block is where control resumes once seeding is done.
///
/// The function creates and switches through three helper blocks
/// (check, header, body) and leaves the builder positioned at
/// `after_seed` so the caller can continue emitting straight-line IR.
fn emit_seed_values_from_initial(
    fb: &mut FunctionBuilder<'_>,
    ctx_ptr: ValueId,
    values_ptr: ValueId,
    num_vars: ValueId,
    after_seed: BlockId,
) {
    let k0_i64 = fb.iconst(Ty::I64, 0);
    let k1_i64 = fb.iconst(Ty::I64, 1);

    // Load `initial_values` pointer and length.
    let iv_ptr_slot_idx = fb.iconst(Ty::I64, CTX_SLOT_INITIAL_VALUES_PTR);
    let iv_ptr_slot = fb.gep(Ty::I64, ctx_ptr, vec![iv_ptr_slot_idx]);
    let iv_addr_u64 = fb.load(Ty::I64, iv_ptr_slot);

    let iv_len_slot_idx = fb.iconst(Ty::I64, CTX_SLOT_INITIAL_VALUES_LEN);
    let iv_len_slot = fb.gep(Ty::I64, ctx_ptr, vec![iv_len_slot_idx]);
    let iv_len = fb.load(Ty::I64, iv_len_slot);

    // Branch on `iv_addr == 0` to skip seeding entirely when the host
    // did not install a buffer.
    let iv_present = fb.icmp(ICmpOp::Ne, Ty::I64, iv_addr_u64, k0_i64);

    let do_seed = fb.create_block();
    fb.condbr(iv_present, do_seed, vec![], after_seed, vec![]);

    fb.switch_to_block(do_seed);
    // limit = min(iv_len, num_vars + 1). The values array is sized
    // `num_vars + 1` so we never overrun it; the host slice may legally
    // be longer (a defensive cap on the kernel side).
    let nv_plus_1 = fb.binop(BinOp::Add, Ty::I64, num_vars, k1_i64);
    let iv_smaller = fb.icmp(ICmpOp::Ult, Ty::I64, iv_len, nv_plus_1);
    let limit = fb.select(Ty::I64, iv_smaller, iv_len, nv_plus_1);

    let iv_ptr = fb.cast(trust_ir::CastOp::IntToPtr, Ty::I64, Ty::Ptr, iv_addr_u64);

    // Copy loop.
    let seed_header = fb.create_block();
    let sh_i = fb.add_block_param(seed_header, Ty::I64);
    let seed_body = fb.create_block();
    let sb_i = fb.add_block_param(seed_body, Ty::I64);

    fb.br(seed_header, vec![k0_i64]);

    fb.switch_to_block(seed_header);
    let sh_done = fb.icmp(ICmpOp::Sge, Ty::I64, sh_i, limit);
    fb.condbr(sh_done, after_seed, vec![], seed_body, vec![sh_i]);

    fb.switch_to_block(seed_body);
    let src_ptr = fb.gep(Ty::I8, iv_ptr, vec![sb_i]);
    let src_val = fb.load(Ty::I8, src_ptr);
    let dst_ptr = fb.gep(Ty::I8, values_ptr, vec![sb_i]);
    fb.store(Ty::I8, dst_ptr, src_val);
    let sb_next = fb.binop(BinOp::Add, Ty::I64, sb_i, k1_i64);
    fb.br(seed_header, vec![sb_next]);
}

pub fn build_bcp_propagate_module() -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("bcp_propagate");

    let entry_ty = mb.add_func_type(vec![Ty::Ptr, Ty::Ptr, Ty::I64], vec![Ty::I64]);

    {
        let mut fb = mb.function(ENTRY_NAME, entry_ty);

        let entry = fb.create_block();
        let ctx_ptr = fb.add_block_param(entry, Ty::Ptr);
        let _input_ptr = fb.add_block_param(entry, Ty::Ptr);
        let _input_len = fb.add_block_param(entry, Ty::I64);

        let outer_header = fb.create_block();
        let propagations = fb.add_block_param(outer_header, Ty::I64);
        let progressed_in = fb.add_block_param(outer_header, Ty::I64);

        let outer_body = fb.create_block();
        let outer_props = fb.add_block_param(outer_body, Ty::I64);

        let clause_header = fb.create_block();
        let ch_ci = fb.add_block_param(clause_header, Ty::I64);
        let ch_props = fb.add_block_param(clause_header, Ty::I64);
        let ch_progressed = fb.add_block_param(clause_header, Ty::I64);

        let clause_body = fb.create_block();
        let cb_ci = fb.add_block_param(clause_body, Ty::I64);
        let cb_props = fb.add_block_param(clause_body, Ty::I64);
        let cb_progressed = fb.add_block_param(clause_body, Ty::I64);

        let lit_header = fb.create_block();
        let lh_k = fb.add_block_param(lit_header, Ty::I64);
        let lh_end = fb.add_block_param(lit_header, Ty::I64);
        let lh_ci = fb.add_block_param(lit_header, Ty::I64);
        let lh_props = fb.add_block_param(lit_header, Ty::I64);
        let lh_progressed = fb.add_block_param(lit_header, Ty::I64);
        let lh_ucnt = fb.add_block_param(lit_header, Ty::I64);
        let lh_first_unassigned = fb.add_block_param(lit_header, Ty::I32);
        let lh_satisfied = fb.add_block_param(lit_header, Ty::I64);

        let lit_body = fb.create_block();
        let lb_k = fb.add_block_param(lit_body, Ty::I64);
        let lb_end = fb.add_block_param(lit_body, Ty::I64);
        let lb_ci = fb.add_block_param(lit_body, Ty::I64);
        let lb_props = fb.add_block_param(lit_body, Ty::I64);
        let lb_progressed = fb.add_block_param(lit_body, Ty::I64);
        let lb_ucnt = fb.add_block_param(lit_body, Ty::I64);
        let lb_first_unassigned = fb.add_block_param(lit_body, Ty::I32);
        let lb_satisfied = fb.add_block_param(lit_body, Ty::I64);

        let clause_done = fb.create_block();
        let cd_ci = fb.add_block_param(clause_done, Ty::I64);
        let cd_props = fb.add_block_param(clause_done, Ty::I64);
        let cd_progressed = fb.add_block_param(clause_done, Ty::I64);
        let cd_ucnt = fb.add_block_param(clause_done, Ty::I64);
        let cd_first_unassigned = fb.add_block_param(clause_done, Ty::I32);
        let cd_satisfied = fb.add_block_param(clause_done, Ty::I64);

        let propagate_step = fb.create_block();
        let ps_ci = fb.add_block_param(propagate_step, Ty::I64);
        let ps_props = fb.add_block_param(propagate_step, Ty::I64);
        let ps_lit = fb.add_block_param(propagate_step, Ty::I32);

        let exit_conflict = fb.create_block();
        let xc_props = fb.add_block_param(exit_conflict, Ty::I64);
        let xc_ci = fb.add_block_param(exit_conflict, Ty::I64);

        let exit_ok = fb.create_block();
        let xo_props = fb.add_block_param(exit_ok, Ty::I64);

        fb.switch_to_block(entry);
        // Hoisted constants reused across non-dominated blocks. ISel rematerializes
        // each at the use site when the def does not dominate; see
        // docs/isel_cross_block_iconst_dominance.md.
        let k_zero_i64 = fb.iconst(Ty::I64, 0);
        let k_one_i64 = fb.iconst(Ty::I64, 1);
        let k_zero_i32 = fb.iconst(Ty::I32, 0);
        let k_shift32_i64 = fb.iconst(Ty::I64, 32);
        let arena_addr_u64 = fb.load(Ty::I64, ctx_ptr);
        let arena_ptr = fb.cast(trust_ir::CastOp::IntToPtr, Ty::I64, Ty::Ptr, arena_addr_u64);

        let num_vars = {
            let p = fb.gep(Ty::I64, arena_ptr, vec![k_zero_i64]);
            fb.load(Ty::I64, p)
        };
        let num_clauses = {
            let p = fb.gep(Ty::I64, arena_ptr, vec![k_one_i64]);
            fb.load(Ty::I64, p)
        };
        let clauses_lits_addr = {
            let off = fb.iconst(Ty::I64, 2);
            let p = fb.gep(Ty::I64, arena_ptr, vec![off]);
            fb.load(Ty::I64, p)
        };
        let clauses_lits_ptr = fb.cast(
            trust_ir::CastOp::IntToPtr,
            Ty::I64,
            Ty::Ptr,
            clauses_lits_addr,
        );

        let clause_offsets_addr = {
            let off = fb.iconst(Ty::I64, 3);
            let p = fb.gep(Ty::I64, arena_ptr, vec![off]);
            fb.load(Ty::I64, p)
        };
        let clause_offsets_ptr = fb.cast(
            trust_ir::CastOp::IntToPtr,
            Ty::I64,
            Ty::Ptr,
            clause_offsets_addr,
        );

        let values_addr = {
            let off = fb.iconst(Ty::I64, 4);
            let p = fb.gep(Ty::I64, arena_ptr, vec![off]);
            fb.load(Ty::I64, p)
        };
        let values_ptr = fb.cast(trust_ir::CastOp::IntToPtr, Ty::I64, Ty::Ptr, values_addr);

        let trail_addr = {
            let off = fb.iconst(Ty::I64, 5);
            let p = fb.gep(Ty::I64, arena_ptr, vec![off]);
            fb.load(Ty::I64, p)
        };
        let trail_ptr = fb.cast(trust_ir::CastOp::IntToPtr, Ty::I64, Ty::Ptr, trail_addr);

        let trail_len_addr = {
            let off = fb.iconst(Ty::I64, 6);
            let p = fb.gep(Ty::I64, arena_ptr, vec![off]);
            fb.load(Ty::I64, p)
        };
        let trail_len_ptr = fb.cast(trust_ir::CastOp::IntToPtr, Ty::I64, Ty::Ptr, trail_len_addr);

        // ---- Phase 0: optional seed of `values[]` from the host's
        // `initial_values` slice. When the host installs a buffer (i.e.
        // the ctx pointer is non-null), this overwrites the arena's
        // zero-initialised values so the BCP loop runs against the
        // exact assignment state MicroSAT had at entry to propagate.
        let after_seed = fb.create_block();
        emit_seed_values_from_initial(&mut fb, ctx_ptr, values_ptr, num_vars, after_seed);

        fb.switch_to_block(after_seed);
        fb.br(outer_header, vec![k_zero_i64, k_one_i64]);

        fb.switch_to_block(outer_header);
        let exit_ok_cond = fb.icmp(ICmpOp::Eq, Ty::I64, progressed_in, k_zero_i64);
        fb.condbr(
            exit_ok_cond,
            exit_ok,
            vec![propagations],
            outer_body,
            vec![propagations],
        );

        fb.switch_to_block(outer_body);
        fb.br(clause_header, vec![k_zero_i64, outer_props, k_zero_i64]);

        fb.switch_to_block(clause_header);
        let done_cond = fb.icmp(ICmpOp::Sge, Ty::I64, ch_ci, num_clauses);
        fb.condbr(
            done_cond,
            outer_header,
            vec![ch_props, ch_progressed],
            clause_body,
            vec![ch_ci, ch_props, ch_progressed],
        );

        fb.switch_to_block(clause_body);
        let off_start_ptr = fb.gep(Ty::U32, clause_offsets_ptr, vec![cb_ci]);
        let start_u32 = fb.load(Ty::U32, off_start_ptr);
        let start_i64 = fb.cast(trust_ir::CastOp::ZExt, Ty::U32, Ty::I64, start_u32);
        let ci_plus_1 = fb.binop(BinOp::Add, Ty::I64, cb_ci, k_one_i64);
        let off_end_ptr = fb.gep(Ty::U32, clause_offsets_ptr, vec![ci_plus_1]);
        let end_u32 = fb.load(Ty::U32, off_end_ptr);
        let end_i64 = fb.cast(trust_ir::CastOp::ZExt, Ty::U32, Ty::I64, end_u32);

        fb.br(
            lit_header,
            vec![
                start_i64,
                end_i64,
                cb_ci,
                cb_props,
                cb_progressed,
                k_zero_i64,
                k_zero_i32,
                k_zero_i64,
            ],
        );

        fb.switch_to_block(lit_header);
        let done_lit_cond = fb.icmp(ICmpOp::Sge, Ty::I64, lh_k, lh_end);
        fb.condbr(
            done_lit_cond,
            clause_done,
            vec![
                lh_ci,
                lh_props,
                lh_progressed,
                lh_ucnt,
                lh_first_unassigned,
                lh_satisfied,
            ],
            lit_body,
            vec![
                lh_k,
                lh_end,
                lh_ci,
                lh_props,
                lh_progressed,
                lh_ucnt,
                lh_first_unassigned,
                lh_satisfied,
            ],
        );

        fb.switch_to_block(lit_body);
        let lit_ptr = fb.gep(Ty::I32, clauses_lits_ptr, vec![lb_k]);
        let lit = fb.load(Ty::I32, lit_ptr);

        let neg_lit = fb.binop(BinOp::Sub, Ty::I32, k_zero_i32, lit);
        let lit_is_neg = fb.icmp(ICmpOp::Slt, Ty::I32, lit, k_zero_i32);
        let var_i32 = fb.select(Ty::I32, lit_is_neg, neg_lit, lit);
        let var_i64 = fb.cast(trust_ir::CastOp::SExt, Ty::I32, Ty::I64, var_i32);

        let val_ptr = fb.gep(Ty::I8, values_ptr, vec![var_i64]);
        let val_i8 = fb.load(Ty::I8, val_ptr);
        let val_i32 = fb.cast(trust_ir::CastOp::SExt, Ty::I8, Ty::I32, val_i8);

        let val_zero = fb.icmp(ICmpOp::Eq, Ty::I32, val_i32, k_zero_i32);

        let neg_val = fb.binop(BinOp::Sub, Ty::I32, k_zero_i32, val_i32);
        let val_for_lit = fb.select(Ty::I32, lit_is_neg, neg_val, val_i32);
        let sat_this = fb.icmp(ICmpOp::Sgt, Ty::I32, val_for_lit, k_zero_i32);

        let sat_this_i64 = fb.cast(trust_ir::CastOp::ZExt, Ty::Bool, Ty::I64, sat_this);
        let new_satisfied = fb.binop(BinOp::Or, Ty::I64, lb_satisfied, sat_this_i64);

        let val_zero_i64 = fb.cast(trust_ir::CastOp::ZExt, Ty::Bool, Ty::I64, val_zero);
        let new_ucnt = fb.binop(BinOp::Add, Ty::I64, lb_ucnt, val_zero_i64);

        let lb_ucnt_is_zero = fb.icmp(ICmpOp::Eq, Ty::I64, lb_ucnt, k_zero_i64);
        let lb_ucnt_is_zero_i64 =
            fb.cast(trust_ir::CastOp::ZExt, Ty::Bool, Ty::I64, lb_ucnt_is_zero);
        let take_first_i64 = fb.binop(BinOp::And, Ty::I64, lb_ucnt_is_zero_i64, val_zero_i64);
        let take_first_bool = fb.icmp(ICmpOp::Ne, Ty::I64, take_first_i64, k_zero_i64);
        let new_first_unassigned = fb.select(Ty::I32, take_first_bool, lit, lb_first_unassigned);

        let next_k = fb.binop(BinOp::Add, Ty::I64, lb_k, k_one_i64);
        fb.br(
            lit_header,
            vec![
                next_k,
                lb_end,
                lb_ci,
                lb_props,
                lb_progressed,
                new_ucnt,
                new_first_unassigned,
                new_satisfied,
            ],
        );

        fb.switch_to_block(clause_done);
        let next_ci_for_done = fb.binop(BinOp::Add, Ty::I64, cd_ci, k_one_i64);

        let sat_nonzero = fb.icmp(ICmpOp::Ne, Ty::I64, cd_satisfied, k_zero_i64);

        let check_conflict = fb.create_block();
        let cc_ci = fb.add_block_param(check_conflict, Ty::I64);
        let cc_props = fb.add_block_param(check_conflict, Ty::I64);
        let cc_progressed = fb.add_block_param(check_conflict, Ty::I64);
        let cc_ucnt = fb.add_block_param(check_conflict, Ty::I64);
        let cc_first = fb.add_block_param(check_conflict, Ty::I32);

        let check_unit = fb.create_block();
        let cu_ci = fb.add_block_param(check_unit, Ty::I64);
        let cu_props = fb.add_block_param(check_unit, Ty::I64);
        let cu_progressed = fb.add_block_param(check_unit, Ty::I64);
        let cu_ucnt = fb.add_block_param(check_unit, Ty::I64);
        let cu_first = fb.add_block_param(check_unit, Ty::I32);

        fb.condbr(
            sat_nonzero,
            clause_header,
            vec![next_ci_for_done, cd_props, cd_progressed],
            check_conflict,
            vec![cd_ci, cd_props, cd_progressed, cd_ucnt, cd_first_unassigned],
        );

        fb.switch_to_block(check_conflict);
        let is_conflict = fb.icmp(ICmpOp::Eq, Ty::I64, cc_ucnt, k_zero_i64);
        fb.condbr(
            is_conflict,
            exit_conflict,
            vec![cc_props, cc_ci],
            check_unit,
            vec![cc_ci, cc_props, cc_progressed, cc_ucnt, cc_first],
        );

        fb.switch_to_block(check_unit);
        let is_unit = fb.icmp(ICmpOp::Eq, Ty::I64, cu_ucnt, k_one_i64);
        let next_ci_from_cu = fb.binop(BinOp::Add, Ty::I64, cu_ci, k_one_i64);
        fb.condbr(
            is_unit,
            propagate_step,
            vec![cu_ci, cu_props, cu_first],
            clause_header,
            vec![next_ci_from_cu, cu_props, cu_progressed],
        );

        fb.switch_to_block(propagate_step);
        let neg_ps_lit = fb.binop(BinOp::Sub, Ty::I32, k_zero_i32, ps_lit);
        let ps_lit_is_neg = fb.icmp(ICmpOp::Slt, Ty::I32, ps_lit, k_zero_i32);
        let ps_var_i32 = fb.select(Ty::I32, ps_lit_is_neg, neg_ps_lit, ps_lit);
        let ps_var_i64 = fb.cast(trust_ir::CastOp::SExt, Ty::I32, Ty::I64, ps_var_i32);

        let pos_one_i8 = fb.iconst(Ty::I8, 1);
        let neg_one_i8 = fb.iconst(Ty::I8, -1);
        let new_val_i8 = fb.select(Ty::I8, ps_lit_is_neg, neg_one_i8, pos_one_i8);
        let ps_val_ptr = fb.gep(Ty::I8, values_ptr, vec![ps_var_i64]);
        fb.store(Ty::I8, ps_val_ptr, new_val_i8);

        let cur_trail_len = fb.load(Ty::I64, trail_len_ptr);
        let trail_slot_ptr = fb.gep(Ty::I32, trail_ptr, vec![cur_trail_len]);
        fb.store(Ty::I32, trail_slot_ptr, ps_lit);
        let new_trail_len = fb.binop(BinOp::Add, Ty::I64, cur_trail_len, k_one_i64);
        fb.store(Ty::I64, trail_len_ptr, new_trail_len);

        let new_props = fb.binop(BinOp::Add, Ty::I64, ps_props, k_one_i64);
        let next_ci_after_prop = fb.binop(BinOp::Add, Ty::I64, ps_ci, k_one_i64);

        // Append the implied literal (and its forcing clause id) to the
        // caller-supplied output buffers, or sticky-overflow the count,
        // before falling through to the clause-header loop continuation.
        emit_record_implied_literal(
            &mut fb,
            ctx_ptr,
            ps_lit,
            Some(ps_ci),
            clause_header,
            vec![next_ci_after_prop, new_props, k_one_i64],
        );

        fb.switch_to_block(exit_conflict);
        emit_set_conflicting_clause_index(&mut fb, ctx_ptr, xc_ci);
        let xc_props_shifted = fb.binop(BinOp::Shl, Ty::I64, xc_props, k_shift32_i64);
        let xc_packed = fb.binop(BinOp::Or, Ty::I64, xc_props_shifted, k_one_i64);
        fb.ret(vec![xc_packed]);

        fb.switch_to_block(exit_ok);
        let xo_packed = fb.binop(BinOp::Shl, Ty::I64, xo_props, k_shift32_i64);
        fb.ret(vec![xo_packed]);

        fb.build();
    }

    mb.build()
}

/// Sibling kernel that consumes the `input: &[u32]` slice before
/// propagating.
///
/// Invariants:
/// - Each `u32` in the input slice encodes one decision literal as
///   `(var << 1) | polarity` per `BCP_INPUT_FORMAT_VERSION`. `polarity` of
///   `0` selects `+var` (truth value `1`), `polarity` of `1` selects `-var`
///   (truth value `-1`).
/// - All input literals are assigned in order before propagation starts.
///   Propagation does NOT run between input assignments.
/// - If any input literal has `var == 0` or `var > num_vars`, the kernel
///   returns `(0 << 32) | BCP_RESULT_DECODE_ERROR` and does NOT run
///   propagation; partial value-array writes from earlier valid input
///   literals are observable in the arena.
/// - On a clean propagation phase the lo32 of the returned `u64` is
///   `BCP_RESULT_OK`; on conflict it is `BCP_RESULT_CONFLICT`. The hi32 is
///   the number of propagation steps performed during the propagate phase
///   (decode-phase assignments do NOT count toward this counter).
pub fn build_bcp_propagate_with_decisions_module() -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("bcp_propagate_with_decisions");

    let entry_ty = mb.add_func_type(vec![Ty::Ptr, Ty::Ptr, Ty::I64], vec![Ty::I64]);

    {
        let mut fb = mb.function(ENTRY_NAME_WITH_DECISIONS, entry_ty);

        let entry = fb.create_block();
        let ctx_ptr = fb.add_block_param(entry, Ty::Ptr);
        let input_ptr = fb.add_block_param(entry, Ty::Ptr);
        let input_len = fb.add_block_param(entry, Ty::I64);

        let decode_header = fb.create_block();
        let dh_i = fb.add_block_param(decode_header, Ty::I64);

        let decode_body = fb.create_block();
        let db_i = fb.add_block_param(decode_body, Ty::I64);

        let decode_error = fb.create_block();

        let propagate_init = fb.create_block();

        let outer_header = fb.create_block();
        let propagations = fb.add_block_param(outer_header, Ty::I64);
        let progressed_in = fb.add_block_param(outer_header, Ty::I64);

        let outer_body = fb.create_block();
        let outer_props = fb.add_block_param(outer_body, Ty::I64);

        let clause_header = fb.create_block();
        let ch_ci = fb.add_block_param(clause_header, Ty::I64);
        let ch_props = fb.add_block_param(clause_header, Ty::I64);
        let ch_progressed = fb.add_block_param(clause_header, Ty::I64);

        let clause_body = fb.create_block();
        let cb_ci = fb.add_block_param(clause_body, Ty::I64);
        let cb_props = fb.add_block_param(clause_body, Ty::I64);
        let cb_progressed = fb.add_block_param(clause_body, Ty::I64);

        let lit_header = fb.create_block();
        let lh_k = fb.add_block_param(lit_header, Ty::I64);
        let lh_end = fb.add_block_param(lit_header, Ty::I64);
        let lh_ci = fb.add_block_param(lit_header, Ty::I64);
        let lh_props = fb.add_block_param(lit_header, Ty::I64);
        let lh_progressed = fb.add_block_param(lit_header, Ty::I64);
        let lh_ucnt = fb.add_block_param(lit_header, Ty::I64);
        let lh_first_unassigned = fb.add_block_param(lit_header, Ty::I32);
        let lh_satisfied = fb.add_block_param(lit_header, Ty::I64);

        let lit_body = fb.create_block();
        let lb_k = fb.add_block_param(lit_body, Ty::I64);
        let lb_end = fb.add_block_param(lit_body, Ty::I64);
        let lb_ci = fb.add_block_param(lit_body, Ty::I64);
        let lb_props = fb.add_block_param(lit_body, Ty::I64);
        let lb_progressed = fb.add_block_param(lit_body, Ty::I64);
        let lb_ucnt = fb.add_block_param(lit_body, Ty::I64);
        let lb_first_unassigned = fb.add_block_param(lit_body, Ty::I32);
        let lb_satisfied = fb.add_block_param(lit_body, Ty::I64);

        let clause_done = fb.create_block();
        let cd_ci = fb.add_block_param(clause_done, Ty::I64);
        let cd_props = fb.add_block_param(clause_done, Ty::I64);
        let cd_progressed = fb.add_block_param(clause_done, Ty::I64);
        let cd_ucnt = fb.add_block_param(clause_done, Ty::I64);
        let cd_first_unassigned = fb.add_block_param(clause_done, Ty::I32);
        let cd_satisfied = fb.add_block_param(clause_done, Ty::I64);

        let propagate_step = fb.create_block();
        let ps_ci = fb.add_block_param(propagate_step, Ty::I64);
        let ps_props = fb.add_block_param(propagate_step, Ty::I64);
        let ps_lit = fb.add_block_param(propagate_step, Ty::I32);

        let exit_conflict = fb.create_block();
        let xc_props = fb.add_block_param(exit_conflict, Ty::I64);
        let xc_ci = fb.add_block_param(exit_conflict, Ty::I64);

        let exit_ok = fb.create_block();
        let xo_props = fb.add_block_param(exit_ok, Ty::I64);

        fb.switch_to_block(entry);
        let arena_addr_u64 = fb.load(Ty::I64, ctx_ptr);
        let arena_ptr = fb.cast(trust_ir::CastOp::IntToPtr, Ty::I64, Ty::Ptr, arena_addr_u64);

        let num_vars = {
            let off = fb.iconst(Ty::I64, 0);
            let p = fb.gep(Ty::I64, arena_ptr, vec![off]);
            fb.load(Ty::I64, p)
        };
        let num_clauses = {
            let off = fb.iconst(Ty::I64, 1);
            let p = fb.gep(Ty::I64, arena_ptr, vec![off]);
            fb.load(Ty::I64, p)
        };
        let clauses_lits_addr = {
            let off = fb.iconst(Ty::I64, 2);
            let p = fb.gep(Ty::I64, arena_ptr, vec![off]);
            fb.load(Ty::I64, p)
        };
        let clauses_lits_ptr = fb.cast(
            trust_ir::CastOp::IntToPtr,
            Ty::I64,
            Ty::Ptr,
            clauses_lits_addr,
        );

        let clause_offsets_addr = {
            let off = fb.iconst(Ty::I64, 3);
            let p = fb.gep(Ty::I64, arena_ptr, vec![off]);
            fb.load(Ty::I64, p)
        };
        let clause_offsets_ptr = fb.cast(
            trust_ir::CastOp::IntToPtr,
            Ty::I64,
            Ty::Ptr,
            clause_offsets_addr,
        );

        let values_addr = {
            let off = fb.iconst(Ty::I64, 4);
            let p = fb.gep(Ty::I64, arena_ptr, vec![off]);
            fb.load(Ty::I64, p)
        };
        let values_ptr = fb.cast(trust_ir::CastOp::IntToPtr, Ty::I64, Ty::Ptr, values_addr);

        let trail_addr = {
            let off = fb.iconst(Ty::I64, 5);
            let p = fb.gep(Ty::I64, arena_ptr, vec![off]);
            fb.load(Ty::I64, p)
        };
        let trail_ptr = fb.cast(trust_ir::CastOp::IntToPtr, Ty::I64, Ty::Ptr, trail_addr);

        let trail_len_addr = {
            let off = fb.iconst(Ty::I64, 6);
            let p = fb.gep(Ty::I64, arena_ptr, vec![off]);
            fb.load(Ty::I64, p)
        };
        let trail_len_ptr = fb.cast(trust_ir::CastOp::IntToPtr, Ty::I64, Ty::Ptr, trail_len_addr);

        // ---- Phase 0: optional seed of `values[]` from the host's
        // `initial_values` slice. See `emit_seed_values_from_initial`.
        let after_seed = fb.create_block();
        emit_seed_values_from_initial(&mut fb, ctx_ptr, values_ptr, num_vars, after_seed);

        fb.switch_to_block(after_seed);
        let i_init = fb.iconst(Ty::I64, 0);
        fb.br(decode_header, vec![i_init]);

        fb.switch_to_block(decode_header);
        let decode_done = fb.icmp(ICmpOp::Sge, Ty::I64, dh_i, input_len);
        fb.condbr(decode_done, propagate_init, vec![], decode_body, vec![dh_i]);

        fb.switch_to_block(decode_body);
        let lit_slot_ptr = fb.gep(Ty::U32, input_ptr, vec![db_i]);
        let lit_packed_u32 = fb.load(Ty::U32, lit_slot_ptr);
        let lit_packed_i64 = fb.cast(trust_ir::CastOp::ZExt, Ty::U32, Ty::I64, lit_packed_u32);
        let shift_one_i64 = fb.iconst(Ty::I64, 1);
        let var_i64 = fb.binop(BinOp::LShr, Ty::I64, lit_packed_i64, shift_one_i64);
        let mask_one_i64 = fb.iconst(Ty::I64, 1);
        let polarity_i64 = fb.binop(BinOp::And, Ty::I64, lit_packed_i64, mask_one_i64);

        let zero_i64_db = fb.iconst(Ty::I64, 0);
        let var_is_zero = fb.icmp(ICmpOp::Eq, Ty::I64, var_i64, zero_i64_db);
        let var_oob = fb.icmp(ICmpOp::Sgt, Ty::I64, var_i64, num_vars);
        let var_is_zero_i64 = fb.cast(trust_ir::CastOp::ZExt, Ty::Bool, Ty::I64, var_is_zero);
        let var_oob_i64 = fb.cast(trust_ir::CastOp::ZExt, Ty::Bool, Ty::I64, var_oob);
        let bad_i64 = fb.binop(BinOp::Or, Ty::I64, var_is_zero_i64, var_oob_i64);
        let zero_for_bad = fb.iconst(Ty::I64, 0);
        let bad_bool = fb.icmp(ICmpOp::Ne, Ty::I64, bad_i64, zero_for_bad);

        let do_assign = fb.create_block();
        let da_i = fb.add_block_param(do_assign, Ty::I64);
        let da_var = fb.add_block_param(do_assign, Ty::I64);
        let da_polarity = fb.add_block_param(do_assign, Ty::I64);

        fb.condbr(
            bad_bool,
            decode_error,
            vec![],
            do_assign,
            vec![db_i, var_i64, polarity_i64],
        );

        fb.switch_to_block(do_assign);
        let zero_for_pol = fb.iconst(Ty::I64, 0);
        let is_negative = fb.icmp(ICmpOp::Ne, Ty::I64, da_polarity, zero_for_pol);
        let pos_one_i8 = fb.iconst(Ty::I8, 1);
        let neg_one_i8 = fb.iconst(Ty::I8, -1);
        let new_val_i8 = fb.select(Ty::I8, is_negative, neg_one_i8, pos_one_i8);
        let val_dst_ptr = fb.gep(Ty::I8, values_ptr, vec![da_var]);
        fb.store(Ty::I8, val_dst_ptr, new_val_i8);

        let var_i32 = fb.cast(trust_ir::CastOp::Trunc, Ty::I64, Ty::I32, da_var);
        let zero_i32_da = fb.iconst(Ty::I32, 0);
        let neg_var_i32 = fb.binop(BinOp::Sub, Ty::I32, zero_i32_da, var_i32);
        let signed_lit_i32 = fb.select(Ty::I32, is_negative, neg_var_i32, var_i32);

        let cur_trail_len_da = fb.load(Ty::I64, trail_len_ptr);
        let trail_slot_ptr_da = fb.gep(Ty::I32, trail_ptr, vec![cur_trail_len_da]);
        fb.store(Ty::I32, trail_slot_ptr_da, signed_lit_i32);
        let one_i64_da = fb.iconst(Ty::I64, 1);
        let new_trail_len_da = fb.binop(BinOp::Add, Ty::I64, cur_trail_len_da, one_i64_da);
        fb.store(Ty::I64, trail_len_ptr, new_trail_len_da);

        let next_i = fb.binop(BinOp::Add, Ty::I64, da_i, one_i64_da);
        fb.br(decode_header, vec![next_i]);

        fb.switch_to_block(decode_error);
        let de_shift = fb.iconst(Ty::I64, 32);
        let de_zero_props = fb.iconst(Ty::I64, 0);
        let de_props_shifted = fb.binop(BinOp::Shl, Ty::I64, de_zero_props, de_shift);
        let de_status = fb.iconst(Ty::I64, 2);
        let de_packed = fb.binop(BinOp::Or, Ty::I64, de_props_shifted, de_status);
        fb.ret(vec![de_packed]);

        fb.switch_to_block(propagate_init);
        let init_props = fb.iconst(Ty::I64, 0);
        let init_progressed = fb.iconst(Ty::I64, 1);
        fb.br(outer_header, vec![init_props, init_progressed]);

        fb.switch_to_block(outer_header);
        let zero_oh = fb.iconst(Ty::I64, 0);
        let exit_ok_cond = fb.icmp(ICmpOp::Eq, Ty::I64, progressed_in, zero_oh);
        fb.condbr(
            exit_ok_cond,
            exit_ok,
            vec![propagations],
            outer_body,
            vec![propagations],
        );

        fb.switch_to_block(outer_body);
        let ci0 = fb.iconst(Ty::I64, 0);
        let prog0 = fb.iconst(Ty::I64, 0);
        fb.br(clause_header, vec![ci0, outer_props, prog0]);

        fb.switch_to_block(clause_header);
        let done_cond = fb.icmp(ICmpOp::Sge, Ty::I64, ch_ci, num_clauses);
        fb.condbr(
            done_cond,
            outer_header,
            vec![ch_props, ch_progressed],
            clause_body,
            vec![ch_ci, ch_props, ch_progressed],
        );

        fb.switch_to_block(clause_body);
        let off_start_ptr = fb.gep(Ty::U32, clause_offsets_ptr, vec![cb_ci]);
        let start_u32 = fb.load(Ty::U32, off_start_ptr);
        let start_i64 = fb.cast(trust_ir::CastOp::ZExt, Ty::U32, Ty::I64, start_u32);
        let one_cb = fb.iconst(Ty::I64, 1);
        let ci_plus_1 = fb.binop(BinOp::Add, Ty::I64, cb_ci, one_cb);
        let off_end_ptr = fb.gep(Ty::U32, clause_offsets_ptr, vec![ci_plus_1]);
        let end_u32 = fb.load(Ty::U32, off_end_ptr);
        let end_i64 = fb.cast(trust_ir::CastOp::ZExt, Ty::U32, Ty::I64, end_u32);

        let zero_i32_cb = fb.iconst(Ty::I32, 0);
        let zero_ucnt = fb.iconst(Ty::I64, 0);
        let zero_sat = fb.iconst(Ty::I64, 0);
        fb.br(
            lit_header,
            vec![
                start_i64,
                end_i64,
                cb_ci,
                cb_props,
                cb_progressed,
                zero_ucnt,
                zero_i32_cb,
                zero_sat,
            ],
        );

        fb.switch_to_block(lit_header);
        let done_lit_cond = fb.icmp(ICmpOp::Sge, Ty::I64, lh_k, lh_end);
        fb.condbr(
            done_lit_cond,
            clause_done,
            vec![
                lh_ci,
                lh_props,
                lh_progressed,
                lh_ucnt,
                lh_first_unassigned,
                lh_satisfied,
            ],
            lit_body,
            vec![
                lh_k,
                lh_end,
                lh_ci,
                lh_props,
                lh_progressed,
                lh_ucnt,
                lh_first_unassigned,
                lh_satisfied,
            ],
        );

        fb.switch_to_block(lit_body);
        let lit_ptr = fb.gep(Ty::I32, clauses_lits_ptr, vec![lb_k]);
        let lit = fb.load(Ty::I32, lit_ptr);

        let zero_for_lit = fb.iconst(Ty::I32, 0);
        let neg_lit = fb.binop(BinOp::Sub, Ty::I32, zero_for_lit, lit);
        let lit_is_neg = fb.icmp(ICmpOp::Slt, Ty::I32, lit, zero_for_lit);
        let var_i32_lb = fb.select(Ty::I32, lit_is_neg, neg_lit, lit);
        let var_i64_lb = fb.cast(trust_ir::CastOp::SExt, Ty::I32, Ty::I64, var_i32_lb);

        let val_ptr = fb.gep(Ty::I8, values_ptr, vec![var_i64_lb]);
        let val_i8 = fb.load(Ty::I8, val_ptr);
        let val_i32 = fb.cast(trust_ir::CastOp::SExt, Ty::I8, Ty::I32, val_i8);

        let val_zero = fb.icmp(ICmpOp::Eq, Ty::I32, val_i32, zero_for_lit);

        let neg_val = fb.binop(BinOp::Sub, Ty::I32, zero_for_lit, val_i32);
        let val_for_lit = fb.select(Ty::I32, lit_is_neg, neg_val, val_i32);
        let sat_this = fb.icmp(ICmpOp::Sgt, Ty::I32, val_for_lit, zero_for_lit);

        let sat_this_i64 = fb.cast(trust_ir::CastOp::ZExt, Ty::Bool, Ty::I64, sat_this);
        let new_satisfied = fb.binop(BinOp::Or, Ty::I64, lb_satisfied, sat_this_i64);

        let one_for_ucnt = fb.iconst(Ty::I64, 1);
        let val_zero_i64 = fb.cast(trust_ir::CastOp::ZExt, Ty::Bool, Ty::I64, val_zero);
        let new_ucnt = fb.binop(BinOp::Add, Ty::I64, lb_ucnt, val_zero_i64);

        let zero_for_ucnt = fb.iconst(Ty::I64, 0);
        let lb_ucnt_is_zero = fb.icmp(ICmpOp::Eq, Ty::I64, lb_ucnt, zero_for_ucnt);
        let lb_ucnt_is_zero_i64 =
            fb.cast(trust_ir::CastOp::ZExt, Ty::Bool, Ty::I64, lb_ucnt_is_zero);
        let take_first_i64 = fb.binop(BinOp::And, Ty::I64, lb_ucnt_is_zero_i64, val_zero_i64);
        let take_first_bool = fb.icmp(ICmpOp::Ne, Ty::I64, take_first_i64, zero_for_ucnt);
        let new_first_unassigned = fb.select(Ty::I32, take_first_bool, lit, lb_first_unassigned);

        let next_k = fb.binop(BinOp::Add, Ty::I64, lb_k, one_for_ucnt);
        fb.br(
            lit_header,
            vec![
                next_k,
                lb_end,
                lb_ci,
                lb_props,
                lb_progressed,
                new_ucnt,
                new_first_unassigned,
                new_satisfied,
            ],
        );

        fb.switch_to_block(clause_done);
        let one_for_done = fb.iconst(Ty::I64, 1);
        let next_ci_for_done = fb.binop(BinOp::Add, Ty::I64, cd_ci, one_for_done);

        let zero_for_done = fb.iconst(Ty::I64, 0);
        let sat_nonzero = fb.icmp(ICmpOp::Ne, Ty::I64, cd_satisfied, zero_for_done);

        let check_conflict = fb.create_block();
        let cc_ci = fb.add_block_param(check_conflict, Ty::I64);
        let cc_props = fb.add_block_param(check_conflict, Ty::I64);
        let cc_progressed = fb.add_block_param(check_conflict, Ty::I64);
        let cc_ucnt = fb.add_block_param(check_conflict, Ty::I64);
        let cc_first = fb.add_block_param(check_conflict, Ty::I32);

        let check_unit = fb.create_block();
        let cu_ci = fb.add_block_param(check_unit, Ty::I64);
        let cu_props = fb.add_block_param(check_unit, Ty::I64);
        let cu_progressed = fb.add_block_param(check_unit, Ty::I64);
        let cu_ucnt = fb.add_block_param(check_unit, Ty::I64);
        let cu_first = fb.add_block_param(check_unit, Ty::I32);

        fb.condbr(
            sat_nonzero,
            clause_header,
            vec![next_ci_for_done, cd_props, cd_progressed],
            check_conflict,
            vec![cd_ci, cd_props, cd_progressed, cd_ucnt, cd_first_unassigned],
        );

        fb.switch_to_block(check_conflict);
        let zero_for_cc = fb.iconst(Ty::I64, 0);
        let is_conflict = fb.icmp(ICmpOp::Eq, Ty::I64, cc_ucnt, zero_for_cc);
        fb.condbr(
            is_conflict,
            exit_conflict,
            vec![cc_props, cc_ci],
            check_unit,
            vec![cc_ci, cc_props, cc_progressed, cc_ucnt, cc_first],
        );

        fb.switch_to_block(check_unit);
        let one_for_unit = fb.iconst(Ty::I64, 1);
        let is_unit = fb.icmp(ICmpOp::Eq, Ty::I64, cu_ucnt, one_for_unit);
        let next_ci_from_cu = fb.binop(BinOp::Add, Ty::I64, cu_ci, one_for_unit);
        fb.condbr(
            is_unit,
            propagate_step,
            vec![cu_ci, cu_props, cu_first],
            clause_header,
            vec![next_ci_from_cu, cu_props, cu_progressed],
        );

        fb.switch_to_block(propagate_step);
        let zero32_in_ps = fb.iconst(Ty::I32, 0);
        let neg_ps_lit = fb.binop(BinOp::Sub, Ty::I32, zero32_in_ps, ps_lit);
        let ps_lit_is_neg = fb.icmp(ICmpOp::Slt, Ty::I32, ps_lit, zero32_in_ps);
        let ps_var_i32 = fb.select(Ty::I32, ps_lit_is_neg, neg_ps_lit, ps_lit);
        let ps_var_i64 = fb.cast(trust_ir::CastOp::SExt, Ty::I32, Ty::I64, ps_var_i32);

        let pos_one_i8_ps = fb.iconst(Ty::I8, 1);
        let neg_one_i8_ps = fb.iconst(Ty::I8, -1);
        let new_val_i8_ps = fb.select(Ty::I8, ps_lit_is_neg, neg_one_i8_ps, pos_one_i8_ps);
        let ps_val_ptr = fb.gep(Ty::I8, values_ptr, vec![ps_var_i64]);
        fb.store(Ty::I8, ps_val_ptr, new_val_i8_ps);

        let cur_trail_len = fb.load(Ty::I64, trail_len_ptr);
        let trail_slot_ptr = fb.gep(Ty::I32, trail_ptr, vec![cur_trail_len]);
        fb.store(Ty::I32, trail_slot_ptr, ps_lit);
        let one_i64_ps = fb.iconst(Ty::I64, 1);
        let new_trail_len = fb.binop(BinOp::Add, Ty::I64, cur_trail_len, one_i64_ps);
        fb.store(Ty::I64, trail_len_ptr, new_trail_len);

        let new_props = fb.binop(BinOp::Add, Ty::I64, ps_props, one_i64_ps);
        let progressed_true = fb.iconst(Ty::I64, 1);
        let next_ci_after_prop = fb.binop(BinOp::Add, Ty::I64, ps_ci, one_i64_ps);
        emit_record_implied_literal(
            &mut fb,
            ctx_ptr,
            ps_lit,
            Some(ps_ci),
            clause_header,
            vec![next_ci_after_prop, new_props, progressed_true],
        );

        fb.switch_to_block(exit_conflict);
        emit_set_conflicting_clause_index(&mut fb, ctx_ptr, xc_ci);
        let shift32 = fb.iconst(Ty::I64, 32);
        let xc_props_shifted = fb.binop(BinOp::Shl, Ty::I64, xc_props, shift32);
        let one_status = fb.iconst(Ty::I64, 1);
        let xc_packed = fb.binop(BinOp::Or, Ty::I64, xc_props_shifted, one_status);
        fb.ret(vec![xc_packed]);

        fb.switch_to_block(exit_ok);
        let shift32b = fb.iconst(Ty::I64, 32);
        let xo_packed = fb.binop(BinOp::Shl, Ty::I64, xo_props, shift32b);
        fb.ret(vec![xo_packed]);

        fb.build();
    }

    mb.build()
}

/// Watched-literal BCP kernel authored in trust-ir.
///
/// Unlike `build_bcp_propagate_with_decisions_module` (which uses a
/// scan-based BCP loop), this kernel implements the classical two-watched-
/// literal algorithm using fixed-capacity arrays. Per-formula watch-list
/// capacity is encoded in the arena header so the JIT'd code can use any
/// formula at run time without recompilation — the arena layout is sized
/// at arena-build time, not at JIT-compile time.
///
/// # Arena layout (12 `u64` header slots)
///
/// ```text
///   +  0: u64 num_vars
///   +  1: u64 num_clauses
///   +  2: u64 clauses_lits_ptr     -> i32[total_lits]  (mutable; swaps allowed)
///   +  3: u64 clause_offsets_ptr   -> u32[num_clauses + 1]
///   +  4: u64 values_ptr           -> i8[num_vars + 1]
///   +  5: u64 trail_ptr            -> i32[trail_capacity]
///   +  6: u64 trail_len_ptr        -> u64
///   +  7: u64 watch_lens_ptr       -> u32[2 * num_vars + 2]
///   +  8: u64 watches_ptr          -> u32[(2 * num_vars + 2) * watch_cap]
///   +  9: u64 watch_cap            (capacity per literal-indexed watch row)
///   + 10: u64 qhead_ptr            -> u64
///   + 11: u64 reserved             (currently 0; held for future use)
/// ```
///
/// # Semantics
///
/// On every call the kernel:
/// 1. Re-initializes watch lists from current `clauses_lits[start..start+2]` for
///    every clause whose length is >= 2. The caller is expected to reset
///    `clauses_lits` to its original positions before each call when
///    repeatability across calls matters; the `BcpWatchedArena` helper does
///    so in `reset_arena`.
/// 2. Decodes each input `u32` as `(var << 1) | polarity` and assigns it,
///    pushing the signed literal to the trail. Decode errors return
///    `BCP_RESULT_DECODE_ERROR` (lo32) with a zero propagation counter.
/// 3. Walks unit clauses (length 1) once, propagating or detecting conflict.
/// 4. Runs the watched-literal BCP loop to fixpoint.
///
/// The lo32 of the returned `u64` is the result code; the hi32 is the
/// number of propagation steps performed by the BCP loop (decode-phase
/// assignments and initial unit-clause assignments are NOT counted).
pub fn build_bcp_propagate_watched_literal_module() -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("bcp_propagate_watched_literal");

    let entry_ty = mb.add_func_type(vec![Ty::Ptr, Ty::Ptr, Ty::I64], vec![Ty::I64]);

    {
        let mut fb = mb.function(ENTRY_NAME_WATCHED_LITERAL, entry_ty);

        // ---- Block forward declarations ----
        let entry = fb.create_block();
        let ctx_ptr = fb.add_block_param(entry, Ty::Ptr);
        let input_ptr = fb.add_block_param(entry, Ty::Ptr);
        let input_len = fb.add_block_param(entry, Ty::I64);

        // Phase 1: clear watch lengths watch_lens[0..(2*num_vars+2)].
        let init_lens_header = fb.create_block();
        let ilh_i = fb.add_block_param(init_lens_header, Ty::I64);
        let init_lens_body = fb.create_block();
        let ilb_i = fb.add_block_param(init_lens_body, Ty::I64);

        // Phase 2: register two watches per clause (positions 0 and 1).
        let init_w_header = fb.create_block();
        let iwh_ci = fb.add_block_param(init_w_header, Ty::I64);
        let init_w_body = fb.create_block();
        let iwb_ci = fb.add_block_param(init_w_body, Ty::I64);

        // Phase 3: decode input decision literals.
        let decode_header = fb.create_block();
        let dh_i = fb.add_block_param(decode_header, Ty::I64);
        let decode_body = fb.create_block();
        let db_i = fb.add_block_param(decode_body, Ty::I64);
        let decode_error = fb.create_block();

        // Phase 4: scan unit clauses.
        let unit_header = fb.create_block();
        let uh_ci = fb.add_block_param(unit_header, Ty::I64);
        let unit_body = fb.create_block();
        let ub_ci = fb.add_block_param(unit_body, Ty::I64);

        // Phase 5: BCP loop.
        let bcp_loop = fb.create_block();
        let bl_props = fb.add_block_param(bcp_loop, Ty::I64);

        let bcp_step = fb.create_block();
        let bs_props = fb.add_block_param(bcp_step, Ty::I64);

        let watch_walk_header = fb.create_block();
        let wwh_i = fb.add_block_param(watch_walk_header, Ty::I64);
        let wwh_j = fb.add_block_param(watch_walk_header, Ty::I64);
        let wwh_watch_idx = fb.add_block_param(watch_walk_header, Ty::I64);
        let wwh_falsified = fb.add_block_param(watch_walk_header, Ty::I32);
        let wwh_props = fb.add_block_param(watch_walk_header, Ty::I64);

        let watch_walk_body = fb.create_block();
        let wwb_i = fb.add_block_param(watch_walk_body, Ty::I64);
        let wwb_j = fb.add_block_param(watch_walk_body, Ty::I64);
        let wwb_watch_idx = fb.add_block_param(watch_walk_body, Ty::I64);
        let wwb_falsified = fb.add_block_param(watch_walk_body, Ty::I32);
        let wwb_props = fb.add_block_param(watch_walk_body, Ty::I64);

        // After examining `other`, the per-clause loop searches for a
        // non-false replacement watch starting at clause[2].
        let search_header = fb.create_block();
        let sh_k = fb.add_block_param(search_header, Ty::I64);
        let sh_end = fb.add_block_param(search_header, Ty::I64);
        let sh_clause_start = fb.add_block_param(search_header, Ty::I64);
        let sh_ci = fb.add_block_param(search_header, Ty::I64);
        let sh_i = fb.add_block_param(search_header, Ty::I64);
        let sh_j = fb.add_block_param(search_header, Ty::I64);
        let sh_watch_idx = fb.add_block_param(search_header, Ty::I64);
        let sh_falsified = fb.add_block_param(search_header, Ty::I32);
        let sh_props = fb.add_block_param(search_header, Ty::I64);

        let search_body = fb.create_block();
        let sb_k = fb.add_block_param(search_body, Ty::I64);
        let sb_end = fb.add_block_param(search_body, Ty::I64);
        let sb_clause_start = fb.add_block_param(search_body, Ty::I64);
        let sb_ci = fb.add_block_param(search_body, Ty::I64);
        let sb_i = fb.add_block_param(search_body, Ty::I64);
        let sb_j = fb.add_block_param(search_body, Ty::I64);
        let sb_watch_idx = fb.add_block_param(search_body, Ty::I64);
        let sb_falsified = fb.add_block_param(search_body, Ty::I32);
        let sb_props = fb.add_block_param(search_body, Ty::I64);

        // No replacement found: keep watch in current list and either
        // propagate `other`, detect conflict, or skip if `other` is true.
        let no_replacement = fb.create_block();
        let nr_clause_start = fb.add_block_param(no_replacement, Ty::I64);
        let nr_ci = fb.add_block_param(no_replacement, Ty::I64);
        let nr_i = fb.add_block_param(no_replacement, Ty::I64);
        let nr_j = fb.add_block_param(no_replacement, Ty::I64);
        let nr_watch_idx = fb.add_block_param(no_replacement, Ty::I64);
        let nr_falsified = fb.add_block_param(no_replacement, Ty::I32);
        let nr_props = fb.add_block_param(no_replacement, Ty::I64);

        let exit_conflict = fb.create_block();
        let xc_props = fb.add_block_param(exit_conflict, Ty::I64);
        let xc_ci = fb.add_block_param(exit_conflict, Ty::I64);
        let exit_ok = fb.create_block();
        let xo_props = fb.add_block_param(exit_ok, Ty::I64);

        // ---- Entry block: load all arena fields ----
        fb.switch_to_block(entry);
        let k0_i64 = fb.iconst(Ty::I64, 0);
        let k1_i64 = fb.iconst(Ty::I64, 1);
        let k2_i64 = fb.iconst(Ty::I64, 2);
        let k32_i64 = fb.iconst(Ty::I64, 32);
        let k0_i32 = fb.iconst(Ty::I32, 0);
        let k0_u32 = fb.iconst(Ty::U32, 0);

        let arena_addr_u64 = fb.load(Ty::I64, ctx_ptr);
        let arena_ptr = fb.cast(trust_ir::CastOp::IntToPtr, Ty::I64, Ty::Ptr, arena_addr_u64);

        let num_vars = {
            let p = fb.gep(Ty::I64, arena_ptr, vec![k0_i64]);
            fb.load(Ty::I64, p)
        };
        let num_clauses = {
            let p = fb.gep(Ty::I64, arena_ptr, vec![k1_i64]);
            fb.load(Ty::I64, p)
        };
        let clauses_lits_addr = {
            let off = fb.iconst(Ty::I64, 2);
            let p = fb.gep(Ty::I64, arena_ptr, vec![off]);
            fb.load(Ty::I64, p)
        };
        let clauses_lits_ptr = fb.cast(
            trust_ir::CastOp::IntToPtr,
            Ty::I64,
            Ty::Ptr,
            clauses_lits_addr,
        );
        let clause_offsets_addr = {
            let off = fb.iconst(Ty::I64, 3);
            let p = fb.gep(Ty::I64, arena_ptr, vec![off]);
            fb.load(Ty::I64, p)
        };
        let clause_offsets_ptr = fb.cast(
            trust_ir::CastOp::IntToPtr,
            Ty::I64,
            Ty::Ptr,
            clause_offsets_addr,
        );
        let values_addr = {
            let off = fb.iconst(Ty::I64, 4);
            let p = fb.gep(Ty::I64, arena_ptr, vec![off]);
            fb.load(Ty::I64, p)
        };
        let values_ptr = fb.cast(trust_ir::CastOp::IntToPtr, Ty::I64, Ty::Ptr, values_addr);
        let trail_addr = {
            let off = fb.iconst(Ty::I64, 5);
            let p = fb.gep(Ty::I64, arena_ptr, vec![off]);
            fb.load(Ty::I64, p)
        };
        let trail_ptr = fb.cast(trust_ir::CastOp::IntToPtr, Ty::I64, Ty::Ptr, trail_addr);
        let trail_len_addr = {
            let off = fb.iconst(Ty::I64, 6);
            let p = fb.gep(Ty::I64, arena_ptr, vec![off]);
            fb.load(Ty::I64, p)
        };
        let trail_len_ptr = fb.cast(trust_ir::CastOp::IntToPtr, Ty::I64, Ty::Ptr, trail_len_addr);
        let watch_lens_addr = {
            let off = fb.iconst(Ty::I64, 7);
            let p = fb.gep(Ty::I64, arena_ptr, vec![off]);
            fb.load(Ty::I64, p)
        };
        let watch_lens_ptr = fb.cast(
            trust_ir::CastOp::IntToPtr,
            Ty::I64,
            Ty::Ptr,
            watch_lens_addr,
        );
        let watches_addr = {
            let off = fb.iconst(Ty::I64, 8);
            let p = fb.gep(Ty::I64, arena_ptr, vec![off]);
            fb.load(Ty::I64, p)
        };
        let watches_ptr = fb.cast(trust_ir::CastOp::IntToPtr, Ty::I64, Ty::Ptr, watches_addr);
        let watch_cap = {
            let off = fb.iconst(Ty::I64, 9);
            let p = fb.gep(Ty::I64, arena_ptr, vec![off]);
            fb.load(Ty::I64, p)
        };
        let qhead_addr = {
            let off = fb.iconst(Ty::I64, 10);
            let p = fb.gep(Ty::I64, arena_ptr, vec![off]);
            fb.load(Ty::I64, p)
        };
        let qhead_ptr = fb.cast(trust_ir::CastOp::IntToPtr, Ty::I64, Ty::Ptr, qhead_addr);

        // Precompute 2 * num_vars + 2 (the watch-list count).
        let two_nv = fb.binop(BinOp::Shl, Ty::I64, num_vars, k1_i64);
        let watch_count = fb.binop(BinOp::Add, Ty::I64, two_nv, k2_i64);

        // ---- Phase 0: optional seed of `values[]` from the host's
        // `initial_values` slice. Runs BEFORE the watch-list build so
        // unit-clause init (Phase 4) and BCP (Phase 5) observe the
        // exact assignment state MicroSAT had at entry to propagate.
        let after_seed = fb.create_block();
        emit_seed_values_from_initial(&mut fb, ctx_ptr, values_ptr, num_vars, after_seed);

        fb.switch_to_block(after_seed);
        // Begin Phase 1: zero out watch_lens[0..watch_count].
        fb.br(init_lens_header, vec![k0_i64]);

        // ---- Phase 1: clear watch_lens ----
        fb.switch_to_block(init_lens_header);
        let il_done = fb.icmp(ICmpOp::Sge, Ty::I64, ilh_i, watch_count);
        fb.condbr(
            il_done,
            init_w_header,
            vec![k0_i64],
            init_lens_body,
            vec![ilh_i],
        );

        fb.switch_to_block(init_lens_body);
        let ilb_slot = fb.gep(Ty::U32, watch_lens_ptr, vec![ilb_i]);
        fb.store(Ty::U32, ilb_slot, k0_u32);
        let ilb_next = fb.binop(BinOp::Add, Ty::I64, ilb_i, k1_i64);
        fb.br(init_lens_header, vec![ilb_next]);

        // ---- Phase 2: for each clause with len >= 2, register watches on
        //              positions 0 and 1.
        fb.switch_to_block(init_w_header);
        let iw_done = fb.icmp(ICmpOp::Sge, Ty::I64, iwh_ci, num_clauses);
        fb.condbr(
            iw_done,
            decode_header,
            vec![k0_i64],
            init_w_body,
            vec![iwh_ci],
        );

        fb.switch_to_block(init_w_body);
        let iw_off_start_ptr = fb.gep(Ty::U32, clause_offsets_ptr, vec![iwb_ci]);
        let iw_start_u32 = fb.load(Ty::U32, iw_off_start_ptr);
        let iw_start = fb.cast(trust_ir::CastOp::ZExt, Ty::U32, Ty::I64, iw_start_u32);
        let iw_ci_plus1 = fb.binop(BinOp::Add, Ty::I64, iwb_ci, k1_i64);
        let iw_off_end_ptr = fb.gep(Ty::U32, clause_offsets_ptr, vec![iw_ci_plus1]);
        let iw_end_u32 = fb.load(Ty::U32, iw_off_end_ptr);
        let iw_end = fb.cast(trust_ir::CastOp::ZExt, Ty::U32, Ty::I64, iw_end_u32);
        let iw_len = fb.binop(BinOp::Sub, Ty::I64, iw_end, iw_start);

        let iw_register = fb.create_block();
        let iwr_ci = fb.add_block_param(iw_register, Ty::I64);
        let iwr_start = fb.add_block_param(iw_register, Ty::I64);

        let iw_skip = fb.create_block();
        let iwsk_ci = fb.add_block_param(iw_skip, Ty::I64);

        let iw_has_two = fb.icmp(ICmpOp::Sge, Ty::I64, iw_len, k2_i64);
        fb.condbr(
            iw_has_two,
            iw_register,
            vec![iwb_ci, iw_start],
            iw_skip,
            vec![iwb_ci],
        );

        fb.switch_to_block(iw_skip);
        let iw_next_skip = fb.binop(BinOp::Add, Ty::I64, iwsk_ci, k1_i64);
        fb.br(init_w_header, vec![iw_next_skip]);

        fb.switch_to_block(iw_register);
        // Compute lit_index for position 0 and position 1; push iwr_ci onto
        // each list (watches[idx][len] = ci; len += 1).
        let lit0_ptr = fb.gep(Ty::I32, clauses_lits_ptr, vec![iwr_start]);
        let lit0 = fb.load(Ty::I32, lit0_ptr);
        let iwr_start_p1 = fb.binop(BinOp::Add, Ty::I64, iwr_start, k1_i64);
        let lit1_ptr = fb.gep(Ty::I32, clauses_lits_ptr, vec![iwr_start_p1]);
        let lit1 = fb.load(Ty::I32, lit1_ptr);

        // lit_index(lit) = 2*|lit| + (lit < 0 ? 1 : 0).
        let lit0_neg = fb.binop(BinOp::Sub, Ty::I32, k0_i32, lit0);
        let lit0_is_neg = fb.icmp(ICmpOp::Slt, Ty::I32, lit0, k0_i32);
        let lit0_var_i32 = fb.select(Ty::I32, lit0_is_neg, lit0_neg, lit0);
        let lit0_var_i64 = fb.cast(trust_ir::CastOp::SExt, Ty::I32, Ty::I64, lit0_var_i32);
        let lit0_two_var = fb.binop(BinOp::Shl, Ty::I64, lit0_var_i64, k1_i64);
        let lit0_neg_bit = fb.cast(trust_ir::CastOp::ZExt, Ty::Bool, Ty::I64, lit0_is_neg);
        let lit0_idx = fb.binop(BinOp::Or, Ty::I64, lit0_two_var, lit0_neg_bit);

        let lit1_neg = fb.binop(BinOp::Sub, Ty::I32, k0_i32, lit1);
        let lit1_is_neg = fb.icmp(ICmpOp::Slt, Ty::I32, lit1, k0_i32);
        let lit1_var_i32 = fb.select(Ty::I32, lit1_is_neg, lit1_neg, lit1);
        let lit1_var_i64 = fb.cast(trust_ir::CastOp::SExt, Ty::I32, Ty::I64, lit1_var_i32);
        let lit1_two_var = fb.binop(BinOp::Shl, Ty::I64, lit1_var_i64, k1_i64);
        let lit1_neg_bit = fb.cast(trust_ir::CastOp::ZExt, Ty::Bool, Ty::I64, lit1_is_neg);
        let lit1_idx = fb.binop(BinOp::Or, Ty::I64, lit1_two_var, lit1_neg_bit);

        // Push iwr_ci onto watches[lit0_idx].
        let lit0_len_ptr = fb.gep(Ty::U32, watch_lens_ptr, vec![lit0_idx]);
        let lit0_len_u32 = fb.load(Ty::U32, lit0_len_ptr);
        let lit0_len_i64 = fb.cast(trust_ir::CastOp::ZExt, Ty::U32, Ty::I64, lit0_len_u32);
        let lit0_row_base = fb.binop(BinOp::Mul, Ty::I64, lit0_idx, watch_cap);
        let lit0_slot_off = fb.binop(BinOp::Add, Ty::I64, lit0_row_base, lit0_len_i64);
        let lit0_slot_ptr = fb.gep(Ty::U32, watches_ptr, vec![lit0_slot_off]);
        let iwr_ci_u32 = fb.cast(trust_ir::CastOp::Trunc, Ty::I64, Ty::U32, iwr_ci);
        fb.store(Ty::U32, lit0_slot_ptr, iwr_ci_u32);
        let one_u32_for_l0 = fb.iconst(Ty::U32, 1);
        let lit0_len_p1 = fb.binop(BinOp::Add, Ty::U32, lit0_len_u32, one_u32_for_l0);
        fb.store(Ty::U32, lit0_len_ptr, lit0_len_p1);

        // Push iwr_ci onto watches[lit1_idx].
        let lit1_len_ptr = fb.gep(Ty::U32, watch_lens_ptr, vec![lit1_idx]);
        let lit1_len_u32 = fb.load(Ty::U32, lit1_len_ptr);
        let lit1_len_i64 = fb.cast(trust_ir::CastOp::ZExt, Ty::U32, Ty::I64, lit1_len_u32);
        let lit1_row_base = fb.binop(BinOp::Mul, Ty::I64, lit1_idx, watch_cap);
        let lit1_slot_off = fb.binop(BinOp::Add, Ty::I64, lit1_row_base, lit1_len_i64);
        let lit1_slot_ptr = fb.gep(Ty::U32, watches_ptr, vec![lit1_slot_off]);
        fb.store(Ty::U32, lit1_slot_ptr, iwr_ci_u32);
        let one_u32_for_l1 = fb.iconst(Ty::U32, 1);
        let lit1_len_p1 = fb.binop(BinOp::Add, Ty::U32, lit1_len_u32, one_u32_for_l1);
        fb.store(Ty::U32, lit1_len_ptr, lit1_len_p1);

        let iw_next = fb.binop(BinOp::Add, Ty::I64, iwr_ci, k1_i64);
        fb.br(init_w_header, vec![iw_next]);

        // ---- Phase 3: decode input literals ----
        fb.switch_to_block(decode_header);
        let dec_done = fb.icmp(ICmpOp::Sge, Ty::I64, dh_i, input_len);
        fb.condbr(dec_done, unit_header, vec![k0_i64], decode_body, vec![dh_i]);

        fb.switch_to_block(decode_body);
        let dec_slot = fb.gep(Ty::U32, input_ptr, vec![db_i]);
        let dec_u32 = fb.load(Ty::U32, dec_slot);
        let dec_i64 = fb.cast(trust_ir::CastOp::ZExt, Ty::U32, Ty::I64, dec_u32);
        let dec_var = fb.binop(BinOp::LShr, Ty::I64, dec_i64, k1_i64);
        let dec_polarity = fb.binop(BinOp::And, Ty::I64, dec_i64, k1_i64);

        let var_is_zero = fb.icmp(ICmpOp::Eq, Ty::I64, dec_var, k0_i64);
        let var_oob = fb.icmp(ICmpOp::Sgt, Ty::I64, dec_var, num_vars);
        let var_is_zero_i64 = fb.cast(trust_ir::CastOp::ZExt, Ty::Bool, Ty::I64, var_is_zero);
        let var_oob_i64 = fb.cast(trust_ir::CastOp::ZExt, Ty::Bool, Ty::I64, var_oob);
        let bad_i64 = fb.binop(BinOp::Or, Ty::I64, var_is_zero_i64, var_oob_i64);
        let bad_bool = fb.icmp(ICmpOp::Ne, Ty::I64, bad_i64, k0_i64);

        let do_assign = fb.create_block();
        let da_i = fb.add_block_param(do_assign, Ty::I64);
        let da_var = fb.add_block_param(do_assign, Ty::I64);
        let da_polarity = fb.add_block_param(do_assign, Ty::I64);

        fb.condbr(
            bad_bool,
            decode_error,
            vec![],
            do_assign,
            vec![db_i, dec_var, dec_polarity],
        );

        fb.switch_to_block(do_assign);
        let is_neg = fb.icmp(ICmpOp::Ne, Ty::I64, da_polarity, k0_i64);
        let pos1_i8 = fb.iconst(Ty::I8, 1);
        let neg1_i8 = fb.iconst(Ty::I8, -1);
        let new_val_i8 = fb.select(Ty::I8, is_neg, neg1_i8, pos1_i8);
        let val_dst = fb.gep(Ty::I8, values_ptr, vec![da_var]);
        fb.store(Ty::I8, val_dst, new_val_i8);

        let var_i32 = fb.cast(trust_ir::CastOp::Trunc, Ty::I64, Ty::I32, da_var);
        let neg_var_i32 = fb.binop(BinOp::Sub, Ty::I32, k0_i32, var_i32);
        let signed_lit_i32 = fb.select(Ty::I32, is_neg, neg_var_i32, var_i32);

        let cur_tl = fb.load(Ty::I64, trail_len_ptr);
        let trail_slot = fb.gep(Ty::I32, trail_ptr, vec![cur_tl]);
        fb.store(Ty::I32, trail_slot, signed_lit_i32);
        let new_tl = fb.binop(BinOp::Add, Ty::I64, cur_tl, k1_i64);
        fb.store(Ty::I64, trail_len_ptr, new_tl);

        let dec_next = fb.binop(BinOp::Add, Ty::I64, da_i, k1_i64);
        fb.br(decode_header, vec![dec_next]);

        fb.switch_to_block(decode_error);
        let de_zero_props = fb.iconst(Ty::I64, 0);
        let de_status = fb.iconst(Ty::I64, 2);
        let de_props_shifted = fb.binop(BinOp::Shl, Ty::I64, de_zero_props, k32_i64);
        let de_packed = fb.binop(BinOp::Or, Ty::I64, de_props_shifted, de_status);
        fb.ret(vec![de_packed]);

        // ---- Phase 4: unit-clause initial propagation ----
        fb.switch_to_block(unit_header);
        let uh_done = fb.icmp(ICmpOp::Sge, Ty::I64, uh_ci, num_clauses);
        fb.condbr(uh_done, bcp_loop, vec![k0_i64], unit_body, vec![uh_ci]);

        fb.switch_to_block(unit_body);
        let u_off_start_ptr = fb.gep(Ty::U32, clause_offsets_ptr, vec![ub_ci]);
        let u_start_u32 = fb.load(Ty::U32, u_off_start_ptr);
        let u_start = fb.cast(trust_ir::CastOp::ZExt, Ty::U32, Ty::I64, u_start_u32);
        let u_ci_p1 = fb.binop(BinOp::Add, Ty::I64, ub_ci, k1_i64);
        let u_off_end_ptr = fb.gep(Ty::U32, clause_offsets_ptr, vec![u_ci_p1]);
        let u_end_u32 = fb.load(Ty::U32, u_off_end_ptr);
        let u_end = fb.cast(trust_ir::CastOp::ZExt, Ty::U32, Ty::I64, u_end_u32);
        let u_len = fb.binop(BinOp::Sub, Ty::I64, u_end, u_start);

        let u_is_unit = fb.icmp(ICmpOp::Eq, Ty::I64, u_len, k1_i64);

        let u_handle = fb.create_block();
        let uh2_ci = fb.add_block_param(u_handle, Ty::I64);
        let uh2_start = fb.add_block_param(u_handle, Ty::I64);
        let u_skip = fb.create_block();
        let usk_ci = fb.add_block_param(u_skip, Ty::I64);

        fb.condbr(
            u_is_unit,
            u_handle,
            vec![ub_ci, u_start],
            u_skip,
            vec![ub_ci],
        );

        fb.switch_to_block(u_skip);
        let u_next_skip = fb.binop(BinOp::Add, Ty::I64, usk_ci, k1_i64);
        fb.br(unit_header, vec![u_next_skip]);

        fb.switch_to_block(u_handle);
        let uh_lit_ptr = fb.gep(Ty::I32, clauses_lits_ptr, vec![uh2_start]);
        let uh_lit = fb.load(Ty::I32, uh_lit_ptr);
        // var = |lit|; value_for_lit = if lit<0 then -values[var] else values[var]
        let uh_lit_neg = fb.binop(BinOp::Sub, Ty::I32, k0_i32, uh_lit);
        let uh_lit_is_neg = fb.icmp(ICmpOp::Slt, Ty::I32, uh_lit, k0_i32);
        let uh_var_i32 = fb.select(Ty::I32, uh_lit_is_neg, uh_lit_neg, uh_lit);
        let uh_var_i64 = fb.cast(trust_ir::CastOp::SExt, Ty::I32, Ty::I64, uh_var_i32);
        let uh_val_ptr = fb.gep(Ty::I8, values_ptr, vec![uh_var_i64]);
        let uh_val_i8 = fb.load(Ty::I8, uh_val_ptr);
        let uh_val_i32 = fb.cast(trust_ir::CastOp::SExt, Ty::I8, Ty::I32, uh_val_i8);
        let uh_neg_val = fb.binop(BinOp::Sub, Ty::I32, k0_i32, uh_val_i32);
        let uh_val_for_lit = fb.select(Ty::I32, uh_lit_is_neg, uh_neg_val, uh_val_i32);

        let uh_is_false = fb.icmp(ICmpOp::Slt, Ty::I32, uh_val_for_lit, k0_i32);
        let uh_is_unassigned = fb.icmp(ICmpOp::Eq, Ty::I32, uh_val_for_lit, k0_i32);

        let u_conflict = fb.create_block();
        let uconf_ci = fb.add_block_param(u_conflict, Ty::I64);
        let u_check_unassigned = fb.create_block();
        let ucu_ci = fb.add_block_param(u_check_unassigned, Ty::I64);
        let ucu_lit = fb.add_block_param(u_check_unassigned, Ty::I32);
        let u_assign = fb.create_block();
        let ua_ci = fb.add_block_param(u_assign, Ty::I64);
        let ua_lit = fb.add_block_param(u_assign, Ty::I32);

        fb.condbr(
            uh_is_false,
            u_conflict,
            vec![uh2_ci],
            u_check_unassigned,
            vec![uh2_ci, uh_lit],
        );

        fb.switch_to_block(u_conflict);
        emit_set_conflicting_clause_index(&mut fb, ctx_ptr, uconf_ci);
        let uc_zero = fb.iconst(Ty::I64, 0);
        let uc_shifted = fb.binop(BinOp::Shl, Ty::I64, uc_zero, k32_i64);
        let uc_status = fb.iconst(Ty::I64, 1);
        let uc_packed = fb.binop(BinOp::Or, Ty::I64, uc_shifted, uc_status);
        fb.ret(vec![uc_packed]);

        fb.switch_to_block(u_check_unassigned);
        let u_skip2 = fb.create_block();
        let usk2_ci = fb.add_block_param(u_skip2, Ty::I64);
        fb.condbr(
            uh_is_unassigned,
            u_assign,
            vec![ucu_ci, ucu_lit],
            u_skip2,
            vec![ucu_ci],
        );

        fb.switch_to_block(u_skip2);
        let u_next_skip2 = fb.binop(BinOp::Add, Ty::I64, usk2_ci, k1_i64);
        fb.br(unit_header, vec![u_next_skip2]);

        fb.switch_to_block(u_assign);
        // Assign ua_lit: write to values, push onto trail.
        let ua_lit_neg = fb.binop(BinOp::Sub, Ty::I32, k0_i32, ua_lit);
        let ua_lit_is_neg = fb.icmp(ICmpOp::Slt, Ty::I32, ua_lit, k0_i32);
        let ua_var_i32 = fb.select(Ty::I32, ua_lit_is_neg, ua_lit_neg, ua_lit);
        let ua_var_i64 = fb.cast(trust_ir::CastOp::SExt, Ty::I32, Ty::I64, ua_var_i32);
        let ua_pos1 = fb.iconst(Ty::I8, 1);
        let ua_neg1 = fb.iconst(Ty::I8, -1);
        let ua_new_val = fb.select(Ty::I8, ua_lit_is_neg, ua_neg1, ua_pos1);
        let ua_val_dst = fb.gep(Ty::I8, values_ptr, vec![ua_var_i64]);
        fb.store(Ty::I8, ua_val_dst, ua_new_val);

        let ua_cur_tl = fb.load(Ty::I64, trail_len_ptr);
        let ua_trail_slot = fb.gep(Ty::I32, trail_ptr, vec![ua_cur_tl]);
        fb.store(Ty::I32, ua_trail_slot, ua_lit);
        let ua_new_tl = fb.binop(BinOp::Add, Ty::I64, ua_cur_tl, k1_i64);
        fb.store(Ty::I64, trail_len_ptr, ua_new_tl);

        let ua_next = fb.binop(BinOp::Add, Ty::I64, ua_ci, k1_i64);
        // Unit-clause propagations are BCP work, not decode-phase writes;
        // surface them through the implied-literals output buffer. The
        // unit clause itself (`ua_ci`) is the forcing clause.
        emit_record_implied_literal(
            &mut fb,
            ctx_ptr,
            ua_lit,
            Some(ua_ci),
            unit_header,
            vec![ua_next],
        );

        // ---- Phase 5: BCP loop ----
        fb.switch_to_block(bcp_loop);
        let bl_qhead = fb.load(Ty::I64, qhead_ptr);
        let bl_tl = fb.load(Ty::I64, trail_len_ptr);
        let bl_done = fb.icmp(ICmpOp::Sge, Ty::I64, bl_qhead, bl_tl);
        fb.condbr(bl_done, exit_ok, vec![bl_props], bcp_step, vec![bl_props]);

        fb.switch_to_block(bcp_step);
        let bs_qhead = fb.load(Ty::I64, qhead_ptr);
        let bs_assigned_ptr = fb.gep(Ty::I32, trail_ptr, vec![bs_qhead]);
        let bs_assigned = fb.load(Ty::I32, bs_assigned_ptr);
        let bs_qhead_p1 = fb.binop(BinOp::Add, Ty::I64, bs_qhead, k1_i64);
        fb.store(Ty::I64, qhead_ptr, bs_qhead_p1);

        // falsified = -assigned
        let bs_falsified = fb.binop(BinOp::Sub, Ty::I32, k0_i32, bs_assigned);
        // watch_idx = lit_index(falsified) = 2*|falsified| + (falsified<0 ? 1 : 0)
        let bs_fl_neg = fb.binop(BinOp::Sub, Ty::I32, k0_i32, bs_falsified);
        let bs_fl_is_neg = fb.icmp(ICmpOp::Slt, Ty::I32, bs_falsified, k0_i32);
        let bs_fl_var_i32 = fb.select(Ty::I32, bs_fl_is_neg, bs_fl_neg, bs_falsified);
        let bs_fl_var_i64 = fb.cast(trust_ir::CastOp::SExt, Ty::I32, Ty::I64, bs_fl_var_i32);
        let bs_two_var = fb.binop(BinOp::Shl, Ty::I64, bs_fl_var_i64, k1_i64);
        let bs_neg_bit = fb.cast(trust_ir::CastOp::ZExt, Ty::Bool, Ty::I64, bs_fl_is_neg);
        let bs_watch_idx = fb.binop(BinOp::Or, Ty::I64, bs_two_var, bs_neg_bit);

        fb.br(
            watch_walk_header,
            vec![k0_i64, k0_i64, bs_watch_idx, bs_falsified, bs_props],
        );

        // ---- Phase 5a: walk the watch list of falsified, compacting in place ----
        fb.switch_to_block(watch_walk_header);
        let ww_len_ptr = fb.gep(Ty::U32, watch_lens_ptr, vec![wwh_watch_idx]);
        let ww_len_u32 = fb.load(Ty::U32, ww_len_ptr);
        let ww_len_i64 = fb.cast(trust_ir::CastOp::ZExt, Ty::U32, Ty::I64, ww_len_u32);
        let ww_done = fb.icmp(ICmpOp::Sge, Ty::I64, wwh_i, ww_len_i64);

        let ww_finish = fb.create_block();
        let wwf_j = fb.add_block_param(ww_finish, Ty::I64);
        let wwf_watch_idx = fb.add_block_param(ww_finish, Ty::I64);
        let wwf_props = fb.add_block_param(ww_finish, Ty::I64);

        fb.condbr(
            ww_done,
            ww_finish,
            vec![wwh_j, wwh_watch_idx, wwh_props],
            watch_walk_body,
            vec![wwh_i, wwh_j, wwh_watch_idx, wwh_falsified, wwh_props],
        );

        fb.switch_to_block(ww_finish);
        // Store final length j into watch_lens[watch_idx], then loop back to BCP.
        let wwf_j_u32 = fb.cast(trust_ir::CastOp::Trunc, Ty::I64, Ty::U32, wwf_j);
        let wwf_len_ptr = fb.gep(Ty::U32, watch_lens_ptr, vec![wwf_watch_idx]);
        fb.store(Ty::U32, wwf_len_ptr, wwf_j_u32);
        fb.br(bcp_loop, vec![wwf_props]);

        // ---- watch_walk_body: process one watched clause ----
        fb.switch_to_block(watch_walk_body);
        // ci = watches[watch_idx][i] (decoded from row-major flat array).
        let wwb_row_base = fb.binop(BinOp::Mul, Ty::I64, wwb_watch_idx, watch_cap);
        let wwb_off = fb.binop(BinOp::Add, Ty::I64, wwb_row_base, wwb_i);
        let wwb_slot = fb.gep(Ty::U32, watches_ptr, vec![wwb_off]);
        let wwb_ci_u32 = fb.load(Ty::U32, wwb_slot);
        let wwb_ci = fb.cast(trust_ir::CastOp::ZExt, Ty::U32, Ty::I64, wwb_ci_u32);

        // Load clause start/end.
        let wwb_off_start_ptr = fb.gep(Ty::U32, clause_offsets_ptr, vec![wwb_ci]);
        let wwb_off_start_u32 = fb.load(Ty::U32, wwb_off_start_ptr);
        let wwb_off_start = fb.cast(trust_ir::CastOp::ZExt, Ty::U32, Ty::I64, wwb_off_start_u32);
        let wwb_ci_p1 = fb.binop(BinOp::Add, Ty::I64, wwb_ci, k1_i64);
        let wwb_off_end_ptr = fb.gep(Ty::U32, clause_offsets_ptr, vec![wwb_ci_p1]);
        let wwb_off_end_u32 = fb.load(Ty::U32, wwb_off_end_ptr);
        let wwb_off_end = fb.cast(trust_ir::CastOp::ZExt, Ty::U32, Ty::I64, wwb_off_end_u32);

        // Load clause[0] and clause[1].
        let wwb_pos0_ptr = fb.gep(Ty::I32, clauses_lits_ptr, vec![wwb_off_start]);
        let wwb_lit0 = fb.load(Ty::I32, wwb_pos0_ptr);
        let wwb_off_start_p1 = fb.binop(BinOp::Add, Ty::I64, wwb_off_start, k1_i64);
        let wwb_pos1_ptr = fb.gep(Ty::I32, clauses_lits_ptr, vec![wwb_off_start_p1]);
        let wwb_lit1 = fb.load(Ty::I32, wwb_pos1_ptr);

        // If clause[0] == falsified, swap (clause[0] <-> clause[1]) so clause[1] is always the falsified one.
        let lit0_is_falsified = fb.icmp(ICmpOp::Eq, Ty::I32, wwb_lit0, wwb_falsified);
        // Final clause[0] = was-lit1 if lit0 was falsified, else lit0.
        let wwb_other = fb.select(Ty::I32, lit0_is_falsified, wwb_lit1, wwb_lit0);
        // Final clause[1] = the falsified one.
        // Always write back so the watch invariant holds.
        fb.store(Ty::I32, wwb_pos0_ptr, wwb_other);
        fb.store(Ty::I32, wwb_pos1_ptr, wwb_falsified);

        // Check value_of_lit(other).
        let other_neg = fb.binop(BinOp::Sub, Ty::I32, k0_i32, wwb_other);
        let other_is_neg = fb.icmp(ICmpOp::Slt, Ty::I32, wwb_other, k0_i32);
        let other_var_i32 = fb.select(Ty::I32, other_is_neg, other_neg, wwb_other);
        let other_var_i64 = fb.cast(trust_ir::CastOp::SExt, Ty::I32, Ty::I64, other_var_i32);
        let other_val_ptr = fb.gep(Ty::I8, values_ptr, vec![other_var_i64]);
        let other_val_i8 = fb.load(Ty::I8, other_val_ptr);
        let other_val_i32 = fb.cast(trust_ir::CastOp::SExt, Ty::I8, Ty::I32, other_val_i8);
        let other_neg_val = fb.binop(BinOp::Sub, Ty::I32, k0_i32, other_val_i32);
        let other_val_for_lit = fb.select(Ty::I32, other_is_neg, other_neg_val, other_val_i32);
        let other_is_true = fb.icmp(ICmpOp::Sgt, Ty::I32, other_val_for_lit, k0_i32);

        // If other is true, keep watch in current list (copy ci to j, j++).
        let other_true_branch = fb.create_block();
        let otb_i = fb.add_block_param(other_true_branch, Ty::I64);
        let otb_j = fb.add_block_param(other_true_branch, Ty::I64);
        let otb_watch_idx = fb.add_block_param(other_true_branch, Ty::I64);
        let otb_falsified = fb.add_block_param(other_true_branch, Ty::I32);
        let otb_props = fb.add_block_param(other_true_branch, Ty::I64);
        let otb_ci = fb.add_block_param(other_true_branch, Ty::I64);

        let other_not_true_branch = fb.create_block();
        let ontb_i = fb.add_block_param(other_not_true_branch, Ty::I64);
        let ontb_j = fb.add_block_param(other_not_true_branch, Ty::I64);
        let ontb_watch_idx = fb.add_block_param(other_not_true_branch, Ty::I64);
        let ontb_falsified = fb.add_block_param(other_not_true_branch, Ty::I32);
        let ontb_props = fb.add_block_param(other_not_true_branch, Ty::I64);
        let ontb_ci = fb.add_block_param(other_not_true_branch, Ty::I64);
        let ontb_off_start = fb.add_block_param(other_not_true_branch, Ty::I64);
        let ontb_off_end = fb.add_block_param(other_not_true_branch, Ty::I64);

        fb.condbr(
            other_is_true,
            other_true_branch,
            vec![
                wwb_i,
                wwb_j,
                wwb_watch_idx,
                wwb_falsified,
                wwb_props,
                wwb_ci,
            ],
            other_not_true_branch,
            vec![
                wwb_i,
                wwb_j,
                wwb_watch_idx,
                wwb_falsified,
                wwb_props,
                wwb_ci,
                wwb_off_start,
                wwb_off_end,
            ],
        );

        // other is true: copy ci to position j, then advance i and j by 1.
        fb.switch_to_block(other_true_branch);
        let otb_row_base = fb.binop(BinOp::Mul, Ty::I64, otb_watch_idx, watch_cap);
        let otb_j_off = fb.binop(BinOp::Add, Ty::I64, otb_row_base, otb_j);
        let otb_j_slot = fb.gep(Ty::U32, watches_ptr, vec![otb_j_off]);
        let otb_ci_u32 = fb.cast(trust_ir::CastOp::Trunc, Ty::I64, Ty::U32, otb_ci);
        fb.store(Ty::U32, otb_j_slot, otb_ci_u32);
        let otb_next_i = fb.binop(BinOp::Add, Ty::I64, otb_i, k1_i64);
        let otb_next_j = fb.binop(BinOp::Add, Ty::I64, otb_j, k1_i64);
        fb.br(
            watch_walk_header,
            vec![
                otb_next_i,
                otb_next_j,
                otb_watch_idx,
                otb_falsified,
                otb_props,
            ],
        );

        // other is not true: search clause[2..end] for a non-false replacement.
        fb.switch_to_block(other_not_true_branch);
        let ontb_search_start = fb.binop(BinOp::Add, Ty::I64, ontb_off_start, k2_i64);
        fb.br(
            search_header,
            vec![
                ontb_search_start,
                ontb_off_end,
                ontb_off_start,
                ontb_ci,
                ontb_i,
                ontb_j,
                ontb_watch_idx,
                ontb_falsified,
                ontb_props,
            ],
        );

        // search_header: iterate k from clause[2] to clause[end-1], looking
        // for a non-false literal.
        fb.switch_to_block(search_header);
        let sh_done = fb.icmp(ICmpOp::Sge, Ty::I64, sh_k, sh_end);
        fb.condbr(
            sh_done,
            no_replacement,
            vec![
                sh_clause_start,
                sh_ci,
                sh_i,
                sh_j,
                sh_watch_idx,
                sh_falsified,
                sh_props,
            ],
            search_body,
            vec![
                sh_k,
                sh_end,
                sh_clause_start,
                sh_ci,
                sh_i,
                sh_j,
                sh_watch_idx,
                sh_falsified,
                sh_props,
            ],
        );

        fb.switch_to_block(search_body);
        let sb_cand_ptr = fb.gep(Ty::I32, clauses_lits_ptr, vec![sb_k]);
        let sb_cand = fb.load(Ty::I32, sb_cand_ptr);
        let sb_cand_neg = fb.binop(BinOp::Sub, Ty::I32, k0_i32, sb_cand);
        let sb_cand_is_neg = fb.icmp(ICmpOp::Slt, Ty::I32, sb_cand, k0_i32);
        let sb_cand_var_i32 = fb.select(Ty::I32, sb_cand_is_neg, sb_cand_neg, sb_cand);
        let sb_cand_var_i64 = fb.cast(trust_ir::CastOp::SExt, Ty::I32, Ty::I64, sb_cand_var_i32);
        let sb_cand_val_ptr = fb.gep(Ty::I8, values_ptr, vec![sb_cand_var_i64]);
        let sb_cand_val_i8 = fb.load(Ty::I8, sb_cand_val_ptr);
        let sb_cand_val_i32 = fb.cast(trust_ir::CastOp::SExt, Ty::I8, Ty::I32, sb_cand_val_i8);
        let sb_cand_neg_val = fb.binop(BinOp::Sub, Ty::I32, k0_i32, sb_cand_val_i32);
        let sb_cand_val_for_lit =
            fb.select(Ty::I32, sb_cand_is_neg, sb_cand_neg_val, sb_cand_val_i32);
        // "Not false" means val_for_lit >= 0.
        let sb_cand_is_false = fb.icmp(ICmpOp::Slt, Ty::I32, sb_cand_val_for_lit, k0_i32);

        let sb_advance = fb.create_block();
        let sba_k = fb.add_block_param(sb_advance, Ty::I64);
        let sba_end = fb.add_block_param(sb_advance, Ty::I64);
        let sba_clause_start = fb.add_block_param(sb_advance, Ty::I64);
        let sba_ci = fb.add_block_param(sb_advance, Ty::I64);
        let sba_i = fb.add_block_param(sb_advance, Ty::I64);
        let sba_j = fb.add_block_param(sb_advance, Ty::I64);
        let sba_watch_idx = fb.add_block_param(sb_advance, Ty::I64);
        let sba_falsified = fb.add_block_param(sb_advance, Ty::I32);
        let sba_props = fb.add_block_param(sb_advance, Ty::I64);

        let sb_found = fb.create_block();
        let sbf_k = fb.add_block_param(sb_found, Ty::I64);
        let sbf_clause_start = fb.add_block_param(sb_found, Ty::I64);
        let sbf_ci = fb.add_block_param(sb_found, Ty::I64);
        let sbf_i = fb.add_block_param(sb_found, Ty::I64);
        let sbf_j = fb.add_block_param(sb_found, Ty::I64);
        let sbf_watch_idx = fb.add_block_param(sb_found, Ty::I64);
        let sbf_falsified = fb.add_block_param(sb_found, Ty::I32);
        let sbf_props = fb.add_block_param(sb_found, Ty::I64);
        let sbf_cand = fb.add_block_param(sb_found, Ty::I32);

        fb.condbr(
            sb_cand_is_false,
            sb_advance,
            vec![
                sb_k,
                sb_end,
                sb_clause_start,
                sb_ci,
                sb_i,
                sb_j,
                sb_watch_idx,
                sb_falsified,
                sb_props,
            ],
            sb_found,
            vec![
                sb_k,
                sb_clause_start,
                sb_ci,
                sb_i,
                sb_j,
                sb_watch_idx,
                sb_falsified,
                sb_props,
                sb_cand,
            ],
        );

        fb.switch_to_block(sb_advance);
        let sba_next_k = fb.binop(BinOp::Add, Ty::I64, sba_k, k1_i64);
        fb.br(
            search_header,
            vec![
                sba_next_k,
                sba_end,
                sba_clause_start,
                sba_ci,
                sba_i,
                sba_j,
                sba_watch_idx,
                sba_falsified,
                sba_props,
            ],
        );

        // Found replacement at k: swap clause[1] with clause[k], add ci to
        // watches[lit_index(cand)], and DO NOT keep ci in the current list
        // (j stays, i advances).
        fb.switch_to_block(sb_found);
        // clause[1] <- cand; clause[k] <- falsified
        let sbf_pos1_off = fb.binop(BinOp::Add, Ty::I64, sbf_clause_start, k1_i64);
        let sbf_pos1_ptr = fb.gep(Ty::I32, clauses_lits_ptr, vec![sbf_pos1_off]);
        let sbf_posk_ptr = fb.gep(Ty::I32, clauses_lits_ptr, vec![sbf_k]);
        fb.store(Ty::I32, sbf_pos1_ptr, sbf_cand);
        fb.store(Ty::I32, sbf_posk_ptr, sbf_falsified);

        // watch_idx_cand = lit_index(cand).
        let sbf_cand_neg = fb.binop(BinOp::Sub, Ty::I32, k0_i32, sbf_cand);
        let sbf_cand_is_neg = fb.icmp(ICmpOp::Slt, Ty::I32, sbf_cand, k0_i32);
        let sbf_cand_var_i32 = fb.select(Ty::I32, sbf_cand_is_neg, sbf_cand_neg, sbf_cand);
        let sbf_cand_var_i64 = fb.cast(trust_ir::CastOp::SExt, Ty::I32, Ty::I64, sbf_cand_var_i32);
        let sbf_two_var = fb.binop(BinOp::Shl, Ty::I64, sbf_cand_var_i64, k1_i64);
        let sbf_neg_bit = fb.cast(trust_ir::CastOp::ZExt, Ty::Bool, Ty::I64, sbf_cand_is_neg);
        let sbf_cand_watch_idx = fb.binop(BinOp::Or, Ty::I64, sbf_two_var, sbf_neg_bit);

        // watches[cand_watch_idx][len] = ci; len += 1.
        let sbf_cand_len_ptr = fb.gep(Ty::U32, watch_lens_ptr, vec![sbf_cand_watch_idx]);
        let sbf_cand_len_u32 = fb.load(Ty::U32, sbf_cand_len_ptr);
        let sbf_cand_len_i64 = fb.cast(trust_ir::CastOp::ZExt, Ty::U32, Ty::I64, sbf_cand_len_u32);
        let sbf_cand_row_base = fb.binop(BinOp::Mul, Ty::I64, sbf_cand_watch_idx, watch_cap);
        let sbf_cand_slot_off = fb.binop(BinOp::Add, Ty::I64, sbf_cand_row_base, sbf_cand_len_i64);
        let sbf_cand_slot_ptr = fb.gep(Ty::U32, watches_ptr, vec![sbf_cand_slot_off]);
        let sbf_ci_u32 = fb.cast(trust_ir::CastOp::Trunc, Ty::I64, Ty::U32, sbf_ci);
        fb.store(Ty::U32, sbf_cand_slot_ptr, sbf_ci_u32);
        let one_u32_for_sbf = fb.iconst(Ty::U32, 1);
        let sbf_cand_len_p1 = fb.binop(BinOp::Add, Ty::U32, sbf_cand_len_u32, one_u32_for_sbf);
        fb.store(Ty::U32, sbf_cand_len_ptr, sbf_cand_len_p1);

        // Advance i; j unchanged (we removed ci from the current list).
        let sbf_next_i = fb.binop(BinOp::Add, Ty::I64, sbf_i, k1_i64);
        fb.br(
            watch_walk_header,
            vec![sbf_next_i, sbf_j, sbf_watch_idx, sbf_falsified, sbf_props],
        );

        // ---- no_replacement: keep watch in current list (copy ci to j, j++),
        //                     then check whether `other` is false (conflict)
        //                     or unassigned (propagate).
        fb.switch_to_block(no_replacement);
        let nr_row_base = fb.binop(BinOp::Mul, Ty::I64, nr_watch_idx, watch_cap);
        let nr_j_off = fb.binop(BinOp::Add, Ty::I64, nr_row_base, nr_j);
        let nr_j_slot = fb.gep(Ty::U32, watches_ptr, vec![nr_j_off]);
        let nr_ci_u32 = fb.cast(trust_ir::CastOp::Trunc, Ty::I64, Ty::U32, nr_ci);
        fb.store(Ty::U32, nr_j_slot, nr_ci_u32);

        // Reload `other` from clause[0] (it was rewritten to `other` above).
        let nr_pos0_ptr = fb.gep(Ty::I32, clauses_lits_ptr, vec![nr_clause_start]);
        let nr_other = fb.load(Ty::I32, nr_pos0_ptr);
        // Compute other's value.
        let nr_other_neg = fb.binop(BinOp::Sub, Ty::I32, k0_i32, nr_other);
        let nr_other_is_neg = fb.icmp(ICmpOp::Slt, Ty::I32, nr_other, k0_i32);
        let nr_other_var_i32 = fb.select(Ty::I32, nr_other_is_neg, nr_other_neg, nr_other);
        let nr_other_var_i64 = fb.cast(trust_ir::CastOp::SExt, Ty::I32, Ty::I64, nr_other_var_i32);
        let nr_other_val_ptr = fb.gep(Ty::I8, values_ptr, vec![nr_other_var_i64]);
        let nr_other_val_i8 = fb.load(Ty::I8, nr_other_val_ptr);
        let nr_other_val_i32 = fb.cast(trust_ir::CastOp::SExt, Ty::I8, Ty::I32, nr_other_val_i8);
        let nr_other_neg_val = fb.binop(BinOp::Sub, Ty::I32, k0_i32, nr_other_val_i32);
        let nr_other_val_for_lit =
            fb.select(Ty::I32, nr_other_is_neg, nr_other_neg_val, nr_other_val_i32);
        let nr_other_is_false = fb.icmp(ICmpOp::Slt, Ty::I32, nr_other_val_for_lit, k0_i32);

        let nr_conflict_branch = fb.create_block();
        let nrcb_i = fb.add_block_param(nr_conflict_branch, Ty::I64);
        let nrcb_j = fb.add_block_param(nr_conflict_branch, Ty::I64);
        let nrcb_watch_idx = fb.add_block_param(nr_conflict_branch, Ty::I64);
        let nrcb_props = fb.add_block_param(nr_conflict_branch, Ty::I64);
        let nrcb_ci = fb.add_block_param(nr_conflict_branch, Ty::I64);

        let nr_propagate_branch = fb.create_block();
        let nrpb_i = fb.add_block_param(nr_propagate_branch, Ty::I64);
        let nrpb_j = fb.add_block_param(nr_propagate_branch, Ty::I64);
        let nrpb_watch_idx = fb.add_block_param(nr_propagate_branch, Ty::I64);
        let nrpb_falsified = fb.add_block_param(nr_propagate_branch, Ty::I32);
        let nrpb_props = fb.add_block_param(nr_propagate_branch, Ty::I64);
        let nrpb_other = fb.add_block_param(nr_propagate_branch, Ty::I32);
        // The JIT clause index that forced `other`; threaded through so
        // the per-propagation reason write (kernel ABI extension) can
        // look it up against the host's clause-id translation table.
        let nrpb_ci = fb.add_block_param(nr_propagate_branch, Ty::I64);

        fb.condbr(
            nr_other_is_false,
            nr_conflict_branch,
            vec![nr_i, nr_j, nr_watch_idx, nr_props, nr_ci],
            nr_propagate_branch,
            vec![
                nr_i,
                nr_j,
                nr_watch_idx,
                nr_falsified,
                nr_props,
                nr_other,
                nr_ci,
            ],
        );

        fb.switch_to_block(nr_conflict_branch);
        // Conflict: copy remaining unprocessed entries (i+1 .. len) to j+1 .. .
        // Then write final length and exit with conflict status.
        let nrcb_copy_header = fb.create_block();
        let nrcbh_i = fb.add_block_param(nrcb_copy_header, Ty::I64);
        let nrcbh_j = fb.add_block_param(nrcb_copy_header, Ty::I64);
        let nrcbh_watch_idx = fb.add_block_param(nrcb_copy_header, Ty::I64);
        let nrcbh_props = fb.add_block_param(nrcb_copy_header, Ty::I64);
        let nrcbh_ci = fb.add_block_param(nrcb_copy_header, Ty::I64);

        let nrcb_copy_body = fb.create_block();
        let nrcbb_i = fb.add_block_param(nrcb_copy_body, Ty::I64);
        let nrcbb_j = fb.add_block_param(nrcb_copy_body, Ty::I64);
        let nrcbb_watch_idx = fb.add_block_param(nrcb_copy_body, Ty::I64);
        let nrcbb_props = fb.add_block_param(nrcb_copy_body, Ty::I64);
        let nrcbb_ci = fb.add_block_param(nrcb_copy_body, Ty::I64);

        let nrcb_finish = fb.create_block();
        let nrcbf_j = fb.add_block_param(nrcb_finish, Ty::I64);
        let nrcbf_watch_idx = fb.add_block_param(nrcb_finish, Ty::I64);
        let nrcbf_props = fb.add_block_param(nrcb_finish, Ty::I64);
        let nrcbf_ci = fb.add_block_param(nrcb_finish, Ty::I64);

        // Increment i and j (we already wrote ci at position j).
        let nrcb_next_i = fb.binop(BinOp::Add, Ty::I64, nrcb_i, k1_i64);
        let nrcb_next_j = fb.binop(BinOp::Add, Ty::I64, nrcb_j, k1_i64);
        fb.br(
            nrcb_copy_header,
            vec![
                nrcb_next_i,
                nrcb_next_j,
                nrcb_watch_idx,
                nrcb_props,
                nrcb_ci,
            ],
        );

        fb.switch_to_block(nrcb_copy_header);
        // Reload current length.
        let nrcbh_len_ptr = fb.gep(Ty::U32, watch_lens_ptr, vec![nrcbh_watch_idx]);
        let nrcbh_len_u32 = fb.load(Ty::U32, nrcbh_len_ptr);
        let nrcbh_len_i64 = fb.cast(trust_ir::CastOp::ZExt, Ty::U32, Ty::I64, nrcbh_len_u32);
        let nrcbh_done = fb.icmp(ICmpOp::Sge, Ty::I64, nrcbh_i, nrcbh_len_i64);
        fb.condbr(
            nrcbh_done,
            nrcb_finish,
            vec![nrcbh_j, nrcbh_watch_idx, nrcbh_props, nrcbh_ci],
            nrcb_copy_body,
            vec![nrcbh_i, nrcbh_j, nrcbh_watch_idx, nrcbh_props, nrcbh_ci],
        );

        fb.switch_to_block(nrcb_copy_body);
        let nrcbb_row_base = fb.binop(BinOp::Mul, Ty::I64, nrcbb_watch_idx, watch_cap);
        let nrcbb_src_off = fb.binop(BinOp::Add, Ty::I64, nrcbb_row_base, nrcbb_i);
        let nrcbb_dst_off = fb.binop(BinOp::Add, Ty::I64, nrcbb_row_base, nrcbb_j);
        let nrcbb_src_ptr = fb.gep(Ty::U32, watches_ptr, vec![nrcbb_src_off]);
        let nrcbb_dst_ptr = fb.gep(Ty::U32, watches_ptr, vec![nrcbb_dst_off]);
        let nrcbb_val = fb.load(Ty::U32, nrcbb_src_ptr);
        fb.store(Ty::U32, nrcbb_dst_ptr, nrcbb_val);
        let nrcbb_next_i = fb.binop(BinOp::Add, Ty::I64, nrcbb_i, k1_i64);
        let nrcbb_next_j = fb.binop(BinOp::Add, Ty::I64, nrcbb_j, k1_i64);
        fb.br(
            nrcb_copy_header,
            vec![
                nrcbb_next_i,
                nrcbb_next_j,
                nrcbb_watch_idx,
                nrcbb_props,
                nrcbb_ci,
            ],
        );

        fb.switch_to_block(nrcb_finish);
        // Write final length and return conflict.
        let nrcbf_j_u32 = fb.cast(trust_ir::CastOp::Trunc, Ty::I64, Ty::U32, nrcbf_j);
        let nrcbf_len_ptr = fb.gep(Ty::U32, watch_lens_ptr, vec![nrcbf_watch_idx]);
        fb.store(Ty::U32, nrcbf_len_ptr, nrcbf_j_u32);
        fb.br(exit_conflict, vec![nrcbf_props, nrcbf_ci]);

        // Propagate `other`: assign + push, advance i and j.
        fb.switch_to_block(nr_propagate_branch);
        // assign other.
        let nrpb_other_neg = fb.binop(BinOp::Sub, Ty::I32, k0_i32, nrpb_other);
        let nrpb_other_is_neg = fb.icmp(ICmpOp::Slt, Ty::I32, nrpb_other, k0_i32);
        let nrpb_other_var_i32 = fb.select(Ty::I32, nrpb_other_is_neg, nrpb_other_neg, nrpb_other);
        let nrpb_other_var_i64 =
            fb.cast(trust_ir::CastOp::SExt, Ty::I32, Ty::I64, nrpb_other_var_i32);
        let pos1_in_p = fb.iconst(Ty::I8, 1);
        let neg1_in_p = fb.iconst(Ty::I8, -1);
        let nrpb_new_val = fb.select(Ty::I8, nrpb_other_is_neg, neg1_in_p, pos1_in_p);
        let nrpb_val_dst = fb.gep(Ty::I8, values_ptr, vec![nrpb_other_var_i64]);
        fb.store(Ty::I8, nrpb_val_dst, nrpb_new_val);

        // Push other onto trail.
        let nrpb_cur_tl = fb.load(Ty::I64, trail_len_ptr);
        let nrpb_trail_slot = fb.gep(Ty::I32, trail_ptr, vec![nrpb_cur_tl]);
        fb.store(Ty::I32, nrpb_trail_slot, nrpb_other);
        let nrpb_new_tl = fb.binop(BinOp::Add, Ty::I64, nrpb_cur_tl, k1_i64);
        fb.store(Ty::I64, trail_len_ptr, nrpb_new_tl);

        let nrpb_new_props = fb.binop(BinOp::Add, Ty::I64, nrpb_props, k1_i64);
        let nrpb_next_i = fb.binop(BinOp::Add, Ty::I64, nrpb_i, k1_i64);
        let nrpb_next_j = fb.binop(BinOp::Add, Ty::I64, nrpb_j, k1_i64);
        // Newly propagated implication: record `other` in the
        // implied-literals output buffer (sticky-overflow on too-small
        // cap). `nrpb_ci` is the JIT clause index that forced `other`;
        // it gets translated by the kernel ABI's clause-id translation
        // table before being written to the reasons buffer.
        emit_record_implied_literal(
            &mut fb,
            ctx_ptr,
            nrpb_other,
            Some(nrpb_ci),
            watch_walk_header,
            vec![
                nrpb_next_i,
                nrpb_next_j,
                nrpb_watch_idx,
                nrpb_falsified,
                nrpb_new_props,
            ],
        );

        // ---- Exit blocks ----
        fb.switch_to_block(exit_conflict);
        emit_set_conflicting_clause_index(&mut fb, ctx_ptr, xc_ci);
        let xc_shifted = fb.binop(BinOp::Shl, Ty::I64, xc_props, k32_i64);
        let xc_one = fb.iconst(Ty::I64, 1);
        let xc_packed = fb.binop(BinOp::Or, Ty::I64, xc_shifted, xc_one);
        fb.ret(vec![xc_packed]);

        fb.switch_to_block(exit_ok);
        let xo_packed = fb.binop(BinOp::Shl, Ty::I64, xo_props, k32_i64);
        fb.ret(vec![xo_packed]);

        // Silence unused-variable warnings for params held purely for dataflow
        // routing (kept by name for clarity above).
        let _ = (
            input_ptr,
            wwh_falsified,
            wwh_props,
            ontb_i,
            ontb_j,
            ontb_watch_idx,
            ontb_falsified,
            ontb_props,
            ontb_ci,
        );

        fb.build();
    }

    mb.build()
}

pub struct BcpArena {
    pub header: Vec<u64>,
    pub clauses_lits: Vec<i32>,
    pub clause_offsets: Vec<u32>,
    pub values: Vec<i8>,
    pub trail: Vec<i32>,
    pub trail_len: Box<u64>,
}

impl BcpArena {
    pub fn build(num_vars: usize, clauses: &[Vec<i32>], trail_capacity: usize) -> Self {
        let mut clauses_lits: Vec<i32> = Vec::new();
        let mut clause_offsets: Vec<u32> = Vec::with_capacity(clauses.len() + 1);
        clause_offsets.push(0);
        for c in clauses {
            for &lit in c {
                clauses_lits.push(lit);
            }
            clause_offsets.push(clauses_lits.len() as u32);
        }
        let values = vec![0i8; num_vars + 1];
        let trail = vec![0i32; trail_capacity];
        let trail_len = Box::new(0u64);

        let mut arena = BcpArena {
            header: vec![0u64; 7],
            clauses_lits,
            clause_offsets,
            values,
            trail,
            trail_len,
        };
        arena.header[0] = num_vars as u64;
        arena.header[1] = clauses.len() as u64;
        arena.header[2] = arena.clauses_lits.as_ptr() as u64;
        arena.header[3] = arena.clause_offsets.as_ptr() as u64;
        arena.header[4] = arena.values.as_mut_ptr() as u64;
        arena.header[5] = arena.trail.as_mut_ptr() as u64;
        arena.header[6] = (&mut *arena.trail_len) as *mut u64 as u64;
        arena
    }

    pub fn header_ptr(&mut self) -> *mut u8 {
        self.header.as_mut_ptr() as *mut u8
    }

    pub fn header_byte_len(&self) -> usize {
        self.header.len() * 8
    }

    pub fn trail_len(&self) -> u64 {
        *self.trail_len
    }

    pub fn values_at(&self, var: usize) -> i8 {
        self.values[var]
    }

    pub fn reset_values_and_trail(&mut self) {
        for v in self.values.iter_mut() {
            *v = 0;
        }
        *self.trail_len = 0;
    }
}

/// Heap-pinned arena for the watched-literal BCP kernel.
///
/// Owns the formula data + the per-literal watch tables. The arena has a
/// fixed `watch_cap` chosen at construction time so that the kernel never
/// overflows: `watch_cap >= num_clauses` always suffices because each
/// clause contributes at most two watch entries (one per watched literal)
/// across all literals — and within any single literal's row, a clause can
/// appear at most once. The simpler upper bound used here is
/// `watch_cap = max(num_clauses, 1)`, which is correct and trivially
/// computable at JIT-compile time.
///
/// A tighter chunked-free-list layout (per-literal head pointer into a
/// shared flat array of size `2 * num_clauses`) is left as future work;
/// the current layout matches the simplicity-first plan and keeps the
/// JIT'd code's per-literal indexing trivially row-major.
pub struct BcpWatchedArena {
    pub header: Vec<u64>,
    /// Mutable clause-literal arena. `JitBcpWatchedLiteralKernelProvider`
    /// reads from `original_clauses_lits` and copies into `clauses_lits`
    /// each reset to keep call-to-call repeatability.
    pub clauses_lits: Vec<i32>,
    pub original_clauses_lits: Vec<i32>,
    pub clause_offsets: Vec<u32>,
    pub values: Vec<i8>,
    pub trail: Vec<i32>,
    pub trail_len: Box<u64>,
    pub watch_lens: Vec<u32>,
    pub watches: Vec<u32>,
    pub watch_cap: u64,
    pub qhead: Box<u64>,
}

impl BcpWatchedArena {
    pub fn build(num_vars: usize, clauses: &[Vec<i32>], trail_capacity: usize) -> Self {
        let mut clauses_lits: Vec<i32> = Vec::new();
        let mut clause_offsets: Vec<u32> = Vec::with_capacity(clauses.len() + 1);
        clause_offsets.push(0);
        for c in clauses {
            for &lit in c {
                clauses_lits.push(lit);
            }
            clause_offsets.push(clauses_lits.len() as u32);
        }
        let original_clauses_lits = clauses_lits.clone();
        let values = vec![0i8; num_vars + 1];
        let trail = vec![0i32; trail_capacity];
        let trail_len = Box::new(0u64);
        let qhead = Box::new(0u64);

        // Per-literal watch list capacity: each clause contributes at most
        // one entry to a given literal's row, so `num_clauses` is a safe
        // (loose) upper bound.
        let watch_cap = clauses.len().max(1) as u64;
        let watch_rows = 2 * num_vars + 2;
        let watch_lens = vec![0u32; watch_rows];
        let watches = vec![0u32; watch_rows * (watch_cap as usize)];

        let mut arena = BcpWatchedArena {
            header: vec![0u64; 12],
            clauses_lits,
            original_clauses_lits,
            clause_offsets,
            values,
            trail,
            trail_len,
            watch_lens,
            watches,
            watch_cap,
            qhead,
        };
        arena.header[0] = num_vars as u64;
        arena.header[1] = clauses.len() as u64;
        arena.header[2] = arena.clauses_lits.as_mut_ptr() as u64;
        arena.header[3] = arena.clause_offsets.as_ptr() as u64;
        arena.header[4] = arena.values.as_mut_ptr() as u64;
        arena.header[5] = arena.trail.as_mut_ptr() as u64;
        arena.header[6] = (&mut *arena.trail_len) as *mut u64 as u64;
        arena.header[7] = arena.watch_lens.as_mut_ptr() as u64;
        arena.header[8] = arena.watches.as_mut_ptr() as u64;
        arena.header[9] = arena.watch_cap;
        arena.header[10] = (&mut *arena.qhead) as *mut u64 as u64;
        arena.header[11] = 0;
        arena
    }

    pub fn header_ptr(&mut self) -> *mut u8 {
        self.header.as_mut_ptr() as *mut u8
    }

    pub fn header_byte_len(&self) -> usize {
        self.header.len() * 8
    }

    pub fn trail_len(&self) -> u64 {
        *self.trail_len
    }

    pub fn values_at(&self, var: usize) -> i8 {
        self.values[var]
    }

    /// Reset everything that the kernel mutates so that the next call
    /// observes the same start state as the very first call. Re-copies
    /// `original_clauses_lits` into `clauses_lits` so watched-position
    /// swaps from prior calls don't drift the watch initialization.
    pub fn reset_arena(&mut self) {
        for v in self.values.iter_mut() {
            *v = 0;
        }
        *self.trail_len = 0;
        *self.qhead = 0;
        self.clauses_lits
            .copy_from_slice(&self.original_clauses_lits);
        for slot in self.watch_lens.iter_mut() {
            *slot = 0;
        }
        // `watches` rows are length-tracked by `watch_lens`, so we don't
        // need to zero the data; the kernel rebuilds the lists from scratch
        // on every call (the kernel itself begins with a watch_lens clear).
    }
}

/// Build the chunked-layout watched-literal BCP kernel module.
///
/// This kernel implements the same two-watched-literal algorithm as
/// `build_bcp_propagate_watched_literal_module`, but stores the
/// per-literal watch lists as singly linked lists of `WatchNode`s drawn
/// from a shared flat pool, instead of the fixed-capacity row-major
/// table the NN-era kernel uses. The MicroSAT C baseline uses the same
/// linked-list layout, so this kernel's only remaining variable from
/// MicroSAT is "native C compiled with -O3" vs "trust-cg JIT'd from
/// trust-ir" — i.e. the chunked layout closes the data-layout-vs-codegen
/// attribution gap.
///
/// # Arena header layout
///
/// ```text
/// header[0]  num_vars:                u64
/// header[1]  num_clauses:             u64
/// header[2]  clauses_lits_ptr:        *mut i32   // flat clause literals
/// header[3]  clause_offsets_ptr:      *const u32 // [num_clauses + 1]
/// header[4]  values_ptr:              *mut i8    // [num_vars + 1]
/// header[5]  trail_ptr:               *mut i32   // [trail_capacity]
/// header[6]  trail_len_ptr:           *mut u64
/// header[7]  watch_heads_ptr:         *mut u32   // [2*num_vars + 2]
/// header[8]  watch_nodes_ptr:         *mut u32   // flat (ci, next) pairs
/// header[9]  watch_node_capacity:     u64        // node count incl. sentinel
/// header[10] qhead_ptr:               *mut u64
/// header[11] watch_free_head_ptr:     *mut u32   // reserved: never used in
///                                                // the BCP kernel itself,
///                                                // kept so future allocator
///                                                // changes don't break ABI
/// ```
///
/// # Watch list encoding
///
/// `watch_nodes` is a flat `u32` array. Node index `k` occupies slots
/// `[2*k, 2*k + 1]`:
///
/// * `watch_nodes[2*k] = clause_idx`
/// * `watch_nodes[2*k + 1] = next_node` (0 = end of list)
///
/// Node 0 is reserved as a sentinel; `watch_heads[i] == 0` means an
/// empty list. Each clause with `len >= 2` is registered into exactly
/// two lists (one per watched literal) using two pre-determined node
/// slots `(2*ci + 1, 2*ci + 2)`. No allocator state is needed inside the
/// kernel because every node is owned by exactly one clause for the
/// entire lifetime of the arena; the BCP loop only **re-links** existing
/// nodes between heads (it never allocates or frees).
///
/// Total node capacity = `2 * num_clauses + 1`; total memory for
/// `watch_heads + watch_nodes` is `(2*num_vars + 2) * 4 + (2*num_clauses
/// + 1) * 8` bytes — `O(num_vars + num_clauses)` instead of the
/// fixed-cap layout's `O(num_vars * num_clauses)`.
pub fn build_bcp_propagate_watched_literal_chunked_module() -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("bcp_propagate_watched_literal_chunked");

    let entry_ty = mb.add_func_type(vec![Ty::Ptr, Ty::Ptr, Ty::I64], vec![Ty::I64]);

    {
        let mut fb = mb.function(ENTRY_NAME_WATCHED_LITERAL_CHUNKED, entry_ty);

        // ---- Block forward declarations ----
        let entry = fb.create_block();
        let ctx_ptr = fb.add_block_param(entry, Ty::Ptr);
        let input_ptr = fb.add_block_param(entry, Ty::Ptr);
        let input_len = fb.add_block_param(entry, Ty::I64);

        // Phase 1: clear watch_heads[0..2*num_vars+2].
        let init_heads_header = fb.create_block();
        let ihh_i = fb.add_block_param(init_heads_header, Ty::I64);
        let init_heads_body = fb.create_block();
        let ihb_i = fb.add_block_param(init_heads_body, Ty::I64);

        // Phase 2: for each clause register two watches (linked-list push).
        let init_w_header = fb.create_block();
        let iwh_ci = fb.add_block_param(init_w_header, Ty::I64);
        let init_w_body = fb.create_block();
        let iwb_ci = fb.add_block_param(init_w_body, Ty::I64);

        // Phase 3: decode input decision literals.
        let decode_header = fb.create_block();
        let dh_i = fb.add_block_param(decode_header, Ty::I64);
        let decode_body = fb.create_block();
        let db_i = fb.add_block_param(decode_body, Ty::I64);
        let decode_error = fb.create_block();

        // Phase 4: scan unit clauses.
        let unit_header = fb.create_block();
        let uh_ci = fb.add_block_param(unit_header, Ty::I64);
        let unit_body = fb.create_block();
        let ub_ci = fb.add_block_param(unit_body, Ty::I64);

        // Phase 5: BCP loop.
        let bcp_loop = fb.create_block();
        let bl_props = fb.add_block_param(bcp_loop, Ty::I64);

        let bcp_step = fb.create_block();
        let bs_props = fb.add_block_param(bcp_step, Ty::I64);

        // Walk header: walking a linked list. Carries:
        //   - prev_next_ptr: Ptr to the u32 cell that contains `cur_node`
        //                    (either `&watch_heads[falsified_idx]` for the
        //                    head step or `&watch_nodes[2*prev_node + 1]`
        //                    for subsequent steps).
        //   - cur_node:      u32 node index (0 = done with list).
        //   - falsified:     i32 falsified literal (constant per BCP step).
        //   - falsified_idx: i64 lit_index(falsified) (constant per step).
        //   - props:         i64 propagation counter.
        let walk_header = fb.create_block();
        let wh_prev_ptr = fb.add_block_param(walk_header, Ty::Ptr);
        let wh_cur_node = fb.add_block_param(walk_header, Ty::U32);
        let wh_falsified = fb.add_block_param(walk_header, Ty::I32);
        let wh_falsified_idx = fb.add_block_param(walk_header, Ty::I64);
        let wh_props = fb.add_block_param(walk_header, Ty::I64);

        // Walk body: load clause_idx and next; process the clause.
        let walk_body = fb.create_block();
        let wb_prev_ptr = fb.add_block_param(walk_body, Ty::Ptr);
        let wb_cur_node = fb.add_block_param(walk_body, Ty::U32);
        let wb_falsified = fb.add_block_param(walk_body, Ty::I32);
        let wb_falsified_idx = fb.add_block_param(walk_body, Ty::I64);
        let wb_props = fb.add_block_param(walk_body, Ty::I64);

        // After examining `other`, the per-clause logic searches for a
        // non-false replacement watch starting at clause[2].
        let search_header = fb.create_block();
        let sh_k = fb.add_block_param(search_header, Ty::I64);
        let sh_end = fb.add_block_param(search_header, Ty::I64);
        let sh_clause_start = fb.add_block_param(search_header, Ty::I64);
        let sh_ci = fb.add_block_param(search_header, Ty::I64);
        let sh_prev_ptr = fb.add_block_param(search_header, Ty::Ptr);
        let sh_cur_node = fb.add_block_param(search_header, Ty::U32);
        let sh_cur_next_ptr = fb.add_block_param(search_header, Ty::Ptr);
        let sh_next_node = fb.add_block_param(search_header, Ty::U32);
        let sh_falsified = fb.add_block_param(search_header, Ty::I32);
        let sh_falsified_idx = fb.add_block_param(search_header, Ty::I64);
        let sh_props = fb.add_block_param(search_header, Ty::I64);

        let search_body = fb.create_block();
        let sb_k = fb.add_block_param(search_body, Ty::I64);
        let sb_end = fb.add_block_param(search_body, Ty::I64);
        let sb_clause_start = fb.add_block_param(search_body, Ty::I64);
        let sb_ci = fb.add_block_param(search_body, Ty::I64);
        let sb_prev_ptr = fb.add_block_param(search_body, Ty::Ptr);
        let sb_cur_node = fb.add_block_param(search_body, Ty::U32);
        let sb_cur_next_ptr = fb.add_block_param(search_body, Ty::Ptr);
        let sb_next_node = fb.add_block_param(search_body, Ty::U32);
        let sb_falsified = fb.add_block_param(search_body, Ty::I32);
        let sb_falsified_idx = fb.add_block_param(search_body, Ty::I64);
        let sb_props = fb.add_block_param(search_body, Ty::I64);

        // No replacement found: keep watch in current list (advance prev),
        // then check whether `other` is false (conflict) or unassigned
        // (propagate).
        let no_replacement = fb.create_block();
        let nr_clause_start = fb.add_block_param(no_replacement, Ty::I64);
        let nr_ci = fb.add_block_param(no_replacement, Ty::I64);
        let nr_prev_ptr = fb.add_block_param(no_replacement, Ty::Ptr);
        let nr_cur_node = fb.add_block_param(no_replacement, Ty::U32);
        let nr_cur_next_ptr = fb.add_block_param(no_replacement, Ty::Ptr);
        let nr_next_node = fb.add_block_param(no_replacement, Ty::U32);
        let nr_falsified = fb.add_block_param(no_replacement, Ty::I32);
        let nr_falsified_idx = fb.add_block_param(no_replacement, Ty::I64);
        let nr_props = fb.add_block_param(no_replacement, Ty::I64);

        let exit_conflict = fb.create_block();
        let xc_props = fb.add_block_param(exit_conflict, Ty::I64);
        let xc_ci = fb.add_block_param(exit_conflict, Ty::I64);
        let exit_ok = fb.create_block();
        let xo_props = fb.add_block_param(exit_ok, Ty::I64);

        // ---- Entry block: load all arena fields ----
        fb.switch_to_block(entry);
        let k0_i64 = fb.iconst(Ty::I64, 0);
        let k1_i64 = fb.iconst(Ty::I64, 1);
        let k2_i64 = fb.iconst(Ty::I64, 2);
        let k32_i64 = fb.iconst(Ty::I64, 32);
        let k0_i32 = fb.iconst(Ty::I32, 0);
        let k0_u32 = fb.iconst(Ty::U32, 0);

        let arena_addr_u64 = fb.load(Ty::I64, ctx_ptr);
        let arena_ptr = fb.cast(trust_ir::CastOp::IntToPtr, Ty::I64, Ty::Ptr, arena_addr_u64);

        let num_vars = {
            let p = fb.gep(Ty::I64, arena_ptr, vec![k0_i64]);
            fb.load(Ty::I64, p)
        };
        let num_clauses = {
            let p = fb.gep(Ty::I64, arena_ptr, vec![k1_i64]);
            fb.load(Ty::I64, p)
        };
        let clauses_lits_addr = {
            let off = fb.iconst(Ty::I64, 2);
            let p = fb.gep(Ty::I64, arena_ptr, vec![off]);
            fb.load(Ty::I64, p)
        };
        let clauses_lits_ptr = fb.cast(
            trust_ir::CastOp::IntToPtr,
            Ty::I64,
            Ty::Ptr,
            clauses_lits_addr,
        );
        let clause_offsets_addr = {
            let off = fb.iconst(Ty::I64, 3);
            let p = fb.gep(Ty::I64, arena_ptr, vec![off]);
            fb.load(Ty::I64, p)
        };
        let clause_offsets_ptr = fb.cast(
            trust_ir::CastOp::IntToPtr,
            Ty::I64,
            Ty::Ptr,
            clause_offsets_addr,
        );
        let values_addr = {
            let off = fb.iconst(Ty::I64, 4);
            let p = fb.gep(Ty::I64, arena_ptr, vec![off]);
            fb.load(Ty::I64, p)
        };
        let values_ptr = fb.cast(trust_ir::CastOp::IntToPtr, Ty::I64, Ty::Ptr, values_addr);
        let trail_addr = {
            let off = fb.iconst(Ty::I64, 5);
            let p = fb.gep(Ty::I64, arena_ptr, vec![off]);
            fb.load(Ty::I64, p)
        };
        let trail_ptr = fb.cast(trust_ir::CastOp::IntToPtr, Ty::I64, Ty::Ptr, trail_addr);
        let trail_len_addr = {
            let off = fb.iconst(Ty::I64, 6);
            let p = fb.gep(Ty::I64, arena_ptr, vec![off]);
            fb.load(Ty::I64, p)
        };
        let trail_len_ptr = fb.cast(trust_ir::CastOp::IntToPtr, Ty::I64, Ty::Ptr, trail_len_addr);
        let watch_heads_addr = {
            let off = fb.iconst(Ty::I64, 7);
            let p = fb.gep(Ty::I64, arena_ptr, vec![off]);
            fb.load(Ty::I64, p)
        };
        let watch_heads_ptr = fb.cast(
            trust_ir::CastOp::IntToPtr,
            Ty::I64,
            Ty::Ptr,
            watch_heads_addr,
        );
        let watch_nodes_addr = {
            let off = fb.iconst(Ty::I64, 8);
            let p = fb.gep(Ty::I64, arena_ptr, vec![off]);
            fb.load(Ty::I64, p)
        };
        let watch_nodes_ptr = fb.cast(
            trust_ir::CastOp::IntToPtr,
            Ty::I64,
            Ty::Ptr,
            watch_nodes_addr,
        );
        // Slot 9 (watch_node_capacity) is loaded for completeness — the
        // chunked kernel does not depend on the value at runtime because
        // node allocation is deterministic (slots 2*ci+1, 2*ci+2). The
        // host still publishes it so a future variant could bounds-check.
        let _watch_node_capacity = {
            let off = fb.iconst(Ty::I64, 9);
            let p = fb.gep(Ty::I64, arena_ptr, vec![off]);
            fb.load(Ty::I64, p)
        };
        let qhead_addr = {
            let off = fb.iconst(Ty::I64, 10);
            let p = fb.gep(Ty::I64, arena_ptr, vec![off]);
            fb.load(Ty::I64, p)
        };
        let qhead_ptr = fb.cast(trust_ir::CastOp::IntToPtr, Ty::I64, Ty::Ptr, qhead_addr);
        // Slot 11 (watch_free_head_ptr) is reserved for future allocator
        // changes; never accessed by the BCP kernel itself.

        // Precompute 2 * num_vars + 2 (the watch-head count).
        let two_nv = fb.binop(BinOp::Shl, Ty::I64, num_vars, k1_i64);
        let head_count = fb.binop(BinOp::Add, Ty::I64, two_nv, k2_i64);

        // ---- Phase 0: optional seed of `values[]` ----
        let after_seed = fb.create_block();
        emit_seed_values_from_initial(&mut fb, ctx_ptr, values_ptr, num_vars, after_seed);

        fb.switch_to_block(after_seed);
        // Begin Phase 1: zero out watch_heads[0..head_count].
        fb.br(init_heads_header, vec![k0_i64]);

        // ---- Phase 1: clear watch_heads ----
        fb.switch_to_block(init_heads_header);
        let ih_done = fb.icmp(ICmpOp::Sge, Ty::I64, ihh_i, head_count);
        fb.condbr(
            ih_done,
            init_w_header,
            vec![k0_i64],
            init_heads_body,
            vec![ihh_i],
        );

        fb.switch_to_block(init_heads_body);
        let ihb_slot = fb.gep(Ty::U32, watch_heads_ptr, vec![ihb_i]);
        fb.store(Ty::U32, ihb_slot, k0_u32);
        let ihb_next = fb.binop(BinOp::Add, Ty::I64, ihb_i, k1_i64);
        fb.br(init_heads_header, vec![ihb_next]);

        // ---- Phase 2: register two linked-list nodes per clause-with-len>=2.
        //               Node a = 2*ci + 1 watches clause[0].
        //               Node b = 2*ci + 2 watches clause[1].
        fb.switch_to_block(init_w_header);
        let iw_done = fb.icmp(ICmpOp::Sge, Ty::I64, iwh_ci, num_clauses);
        fb.condbr(
            iw_done,
            decode_header,
            vec![k0_i64],
            init_w_body,
            vec![iwh_ci],
        );

        fb.switch_to_block(init_w_body);
        let iw_off_start_ptr = fb.gep(Ty::U32, clause_offsets_ptr, vec![iwb_ci]);
        let iw_start_u32 = fb.load(Ty::U32, iw_off_start_ptr);
        let iw_start = fb.cast(trust_ir::CastOp::ZExt, Ty::U32, Ty::I64, iw_start_u32);
        let iw_ci_plus1 = fb.binop(BinOp::Add, Ty::I64, iwb_ci, k1_i64);
        let iw_off_end_ptr = fb.gep(Ty::U32, clause_offsets_ptr, vec![iw_ci_plus1]);
        let iw_end_u32 = fb.load(Ty::U32, iw_off_end_ptr);
        let iw_end = fb.cast(trust_ir::CastOp::ZExt, Ty::U32, Ty::I64, iw_end_u32);
        let iw_len = fb.binop(BinOp::Sub, Ty::I64, iw_end, iw_start);

        let iw_register = fb.create_block();
        let iwr_ci = fb.add_block_param(iw_register, Ty::I64);
        let iwr_start = fb.add_block_param(iw_register, Ty::I64);

        let iw_skip = fb.create_block();
        let iwsk_ci = fb.add_block_param(iw_skip, Ty::I64);

        let iw_has_two = fb.icmp(ICmpOp::Sge, Ty::I64, iw_len, k2_i64);
        fb.condbr(
            iw_has_two,
            iw_register,
            vec![iwb_ci, iw_start],
            iw_skip,
            vec![iwb_ci],
        );

        fb.switch_to_block(iw_skip);
        let iw_next_skip = fb.binop(BinOp::Add, Ty::I64, iwsk_ci, k1_i64);
        fb.br(init_w_header, vec![iw_next_skip]);

        fb.switch_to_block(iw_register);
        // Compute lit_index for position 0 and position 1.
        let lit0_ptr = fb.gep(Ty::I32, clauses_lits_ptr, vec![iwr_start]);
        let lit0 = fb.load(Ty::I32, lit0_ptr);
        let iwr_start_p1 = fb.binop(BinOp::Add, Ty::I64, iwr_start, k1_i64);
        let lit1_ptr = fb.gep(Ty::I32, clauses_lits_ptr, vec![iwr_start_p1]);
        let lit1 = fb.load(Ty::I32, lit1_ptr);

        // lit_index(lit) = 2*|lit| + (lit < 0 ? 1 : 0).
        let lit0_neg = fb.binop(BinOp::Sub, Ty::I32, k0_i32, lit0);
        let lit0_is_neg = fb.icmp(ICmpOp::Slt, Ty::I32, lit0, k0_i32);
        let lit0_var_i32 = fb.select(Ty::I32, lit0_is_neg, lit0_neg, lit0);
        let lit0_var_i64 = fb.cast(trust_ir::CastOp::SExt, Ty::I32, Ty::I64, lit0_var_i32);
        let lit0_two_var = fb.binop(BinOp::Shl, Ty::I64, lit0_var_i64, k1_i64);
        let lit0_neg_bit = fb.cast(trust_ir::CastOp::ZExt, Ty::Bool, Ty::I64, lit0_is_neg);
        let lit0_idx = fb.binop(BinOp::Or, Ty::I64, lit0_two_var, lit0_neg_bit);

        let lit1_neg = fb.binop(BinOp::Sub, Ty::I32, k0_i32, lit1);
        let lit1_is_neg = fb.icmp(ICmpOp::Slt, Ty::I32, lit1, k0_i32);
        let lit1_var_i32 = fb.select(Ty::I32, lit1_is_neg, lit1_neg, lit1);
        let lit1_var_i64 = fb.cast(trust_ir::CastOp::SExt, Ty::I32, Ty::I64, lit1_var_i32);
        let lit1_two_var = fb.binop(BinOp::Shl, Ty::I64, lit1_var_i64, k1_i64);
        let lit1_neg_bit = fb.cast(trust_ir::CastOp::ZExt, Ty::Bool, Ty::I64, lit1_is_neg);
        let lit1_idx = fb.binop(BinOp::Or, Ty::I64, lit1_two_var, lit1_neg_bit);

        // node_a = 2*iwr_ci + 1; node_b = 2*iwr_ci + 2.
        let iwr_two_ci = fb.binop(BinOp::Shl, Ty::I64, iwr_ci, k1_i64);
        let iwr_node_a = fb.binop(BinOp::Add, Ty::I64, iwr_two_ci, k1_i64);
        let iwr_node_b = fb.binop(BinOp::Add, Ty::I64, iwr_two_ci, k2_i64);
        let iwr_ci_u32 = fb.cast(trust_ir::CastOp::Trunc, Ty::I64, Ty::U32, iwr_ci);
        let iwr_node_a_u32 = fb.cast(trust_ir::CastOp::Trunc, Ty::I64, Ty::U32, iwr_node_a);
        let iwr_node_b_u32 = fb.cast(trust_ir::CastOp::Trunc, Ty::I64, Ty::U32, iwr_node_b);

        // node_a fields: nodes[2*a] = ci; nodes[2*a + 1] = watch_heads[lit0_idx];
        // watch_heads[lit0_idx] = node_a.
        let two_a = fb.binop(BinOp::Shl, Ty::I64, iwr_node_a, k1_i64);
        let two_a_p1 = fb.binop(BinOp::Add, Ty::I64, two_a, k1_i64);
        let a_ci_slot = fb.gep(Ty::U32, watch_nodes_ptr, vec![two_a]);
        let a_next_slot = fb.gep(Ty::U32, watch_nodes_ptr, vec![two_a_p1]);
        fb.store(Ty::U32, a_ci_slot, iwr_ci_u32);
        let lit0_head_slot = fb.gep(Ty::U32, watch_heads_ptr, vec![lit0_idx]);
        let lit0_old_head = fb.load(Ty::U32, lit0_head_slot);
        fb.store(Ty::U32, a_next_slot, lit0_old_head);
        fb.store(Ty::U32, lit0_head_slot, iwr_node_a_u32);

        // node_b fields: same idea on lit1.
        let two_b = fb.binop(BinOp::Shl, Ty::I64, iwr_node_b, k1_i64);
        let two_b_p1 = fb.binop(BinOp::Add, Ty::I64, two_b, k1_i64);
        let b_ci_slot = fb.gep(Ty::U32, watch_nodes_ptr, vec![two_b]);
        let b_next_slot = fb.gep(Ty::U32, watch_nodes_ptr, vec![two_b_p1]);
        fb.store(Ty::U32, b_ci_slot, iwr_ci_u32);
        let lit1_head_slot = fb.gep(Ty::U32, watch_heads_ptr, vec![lit1_idx]);
        let lit1_old_head = fb.load(Ty::U32, lit1_head_slot);
        fb.store(Ty::U32, b_next_slot, lit1_old_head);
        fb.store(Ty::U32, lit1_head_slot, iwr_node_b_u32);

        let iw_next = fb.binop(BinOp::Add, Ty::I64, iwr_ci, k1_i64);
        fb.br(init_w_header, vec![iw_next]);

        // ---- Phase 3: decode input literals (identical to fixed-cap) ----
        fb.switch_to_block(decode_header);
        let dec_done = fb.icmp(ICmpOp::Sge, Ty::I64, dh_i, input_len);
        fb.condbr(dec_done, unit_header, vec![k0_i64], decode_body, vec![dh_i]);

        fb.switch_to_block(decode_body);
        let dec_slot = fb.gep(Ty::U32, input_ptr, vec![db_i]);
        let dec_u32 = fb.load(Ty::U32, dec_slot);
        let dec_i64 = fb.cast(trust_ir::CastOp::ZExt, Ty::U32, Ty::I64, dec_u32);
        let dec_var = fb.binop(BinOp::LShr, Ty::I64, dec_i64, k1_i64);
        let dec_polarity = fb.binop(BinOp::And, Ty::I64, dec_i64, k1_i64);

        let var_is_zero = fb.icmp(ICmpOp::Eq, Ty::I64, dec_var, k0_i64);
        let var_oob = fb.icmp(ICmpOp::Sgt, Ty::I64, dec_var, num_vars);
        let var_is_zero_i64 = fb.cast(trust_ir::CastOp::ZExt, Ty::Bool, Ty::I64, var_is_zero);
        let var_oob_i64 = fb.cast(trust_ir::CastOp::ZExt, Ty::Bool, Ty::I64, var_oob);
        let bad_i64 = fb.binop(BinOp::Or, Ty::I64, var_is_zero_i64, var_oob_i64);
        let bad_bool = fb.icmp(ICmpOp::Ne, Ty::I64, bad_i64, k0_i64);

        let do_assign = fb.create_block();
        let da_i = fb.add_block_param(do_assign, Ty::I64);
        let da_var = fb.add_block_param(do_assign, Ty::I64);
        let da_polarity = fb.add_block_param(do_assign, Ty::I64);

        fb.condbr(
            bad_bool,
            decode_error,
            vec![],
            do_assign,
            vec![db_i, dec_var, dec_polarity],
        );

        fb.switch_to_block(do_assign);
        let is_neg = fb.icmp(ICmpOp::Ne, Ty::I64, da_polarity, k0_i64);
        let pos1_i8 = fb.iconst(Ty::I8, 1);
        let neg1_i8 = fb.iconst(Ty::I8, -1);
        let new_val_i8 = fb.select(Ty::I8, is_neg, neg1_i8, pos1_i8);
        let val_dst = fb.gep(Ty::I8, values_ptr, vec![da_var]);
        fb.store(Ty::I8, val_dst, new_val_i8);

        let var_i32 = fb.cast(trust_ir::CastOp::Trunc, Ty::I64, Ty::I32, da_var);
        let neg_var_i32 = fb.binop(BinOp::Sub, Ty::I32, k0_i32, var_i32);
        let signed_lit_i32 = fb.select(Ty::I32, is_neg, neg_var_i32, var_i32);

        let cur_tl = fb.load(Ty::I64, trail_len_ptr);
        let trail_slot = fb.gep(Ty::I32, trail_ptr, vec![cur_tl]);
        fb.store(Ty::I32, trail_slot, signed_lit_i32);
        let new_tl = fb.binop(BinOp::Add, Ty::I64, cur_tl, k1_i64);
        fb.store(Ty::I64, trail_len_ptr, new_tl);

        let dec_next = fb.binop(BinOp::Add, Ty::I64, da_i, k1_i64);
        fb.br(decode_header, vec![dec_next]);

        fb.switch_to_block(decode_error);
        let de_zero_props = fb.iconst(Ty::I64, 0);
        let de_status = fb.iconst(Ty::I64, 2);
        let de_props_shifted = fb.binop(BinOp::Shl, Ty::I64, de_zero_props, k32_i64);
        let de_packed = fb.binop(BinOp::Or, Ty::I64, de_props_shifted, de_status);
        fb.ret(vec![de_packed]);

        // ---- Phase 4: unit-clause initial propagation (identical to fixed-cap) ----
        fb.switch_to_block(unit_header);
        let uh_done = fb.icmp(ICmpOp::Sge, Ty::I64, uh_ci, num_clauses);
        fb.condbr(uh_done, bcp_loop, vec![k0_i64], unit_body, vec![uh_ci]);

        fb.switch_to_block(unit_body);
        let u_off_start_ptr = fb.gep(Ty::U32, clause_offsets_ptr, vec![ub_ci]);
        let u_start_u32 = fb.load(Ty::U32, u_off_start_ptr);
        let u_start = fb.cast(trust_ir::CastOp::ZExt, Ty::U32, Ty::I64, u_start_u32);
        let u_ci_p1 = fb.binop(BinOp::Add, Ty::I64, ub_ci, k1_i64);
        let u_off_end_ptr = fb.gep(Ty::U32, clause_offsets_ptr, vec![u_ci_p1]);
        let u_end_u32 = fb.load(Ty::U32, u_off_end_ptr);
        let u_end = fb.cast(trust_ir::CastOp::ZExt, Ty::U32, Ty::I64, u_end_u32);
        let u_len = fb.binop(BinOp::Sub, Ty::I64, u_end, u_start);

        let u_is_unit = fb.icmp(ICmpOp::Eq, Ty::I64, u_len, k1_i64);

        let u_handle = fb.create_block();
        let uh2_ci = fb.add_block_param(u_handle, Ty::I64);
        let uh2_start = fb.add_block_param(u_handle, Ty::I64);
        let u_skip = fb.create_block();
        let usk_ci = fb.add_block_param(u_skip, Ty::I64);

        fb.condbr(
            u_is_unit,
            u_handle,
            vec![ub_ci, u_start],
            u_skip,
            vec![ub_ci],
        );

        fb.switch_to_block(u_skip);
        let u_next_skip = fb.binop(BinOp::Add, Ty::I64, usk_ci, k1_i64);
        fb.br(unit_header, vec![u_next_skip]);

        fb.switch_to_block(u_handle);
        let uh_lit_ptr = fb.gep(Ty::I32, clauses_lits_ptr, vec![uh2_start]);
        let uh_lit = fb.load(Ty::I32, uh_lit_ptr);
        let uh_lit_neg = fb.binop(BinOp::Sub, Ty::I32, k0_i32, uh_lit);
        let uh_lit_is_neg = fb.icmp(ICmpOp::Slt, Ty::I32, uh_lit, k0_i32);
        let uh_var_i32 = fb.select(Ty::I32, uh_lit_is_neg, uh_lit_neg, uh_lit);
        let uh_var_i64 = fb.cast(trust_ir::CastOp::SExt, Ty::I32, Ty::I64, uh_var_i32);
        let uh_val_ptr = fb.gep(Ty::I8, values_ptr, vec![uh_var_i64]);
        let uh_val_i8 = fb.load(Ty::I8, uh_val_ptr);
        let uh_val_i32 = fb.cast(trust_ir::CastOp::SExt, Ty::I8, Ty::I32, uh_val_i8);
        let uh_neg_val = fb.binop(BinOp::Sub, Ty::I32, k0_i32, uh_val_i32);
        let uh_val_for_lit = fb.select(Ty::I32, uh_lit_is_neg, uh_neg_val, uh_val_i32);

        let uh_is_false = fb.icmp(ICmpOp::Slt, Ty::I32, uh_val_for_lit, k0_i32);
        let uh_is_unassigned = fb.icmp(ICmpOp::Eq, Ty::I32, uh_val_for_lit, k0_i32);

        let u_conflict = fb.create_block();
        let uconf_ci = fb.add_block_param(u_conflict, Ty::I64);
        let u_check_unassigned = fb.create_block();
        let ucu_ci = fb.add_block_param(u_check_unassigned, Ty::I64);
        let ucu_lit = fb.add_block_param(u_check_unassigned, Ty::I32);
        let u_assign = fb.create_block();
        let ua_ci = fb.add_block_param(u_assign, Ty::I64);
        let ua_lit = fb.add_block_param(u_assign, Ty::I32);

        fb.condbr(
            uh_is_false,
            u_conflict,
            vec![uh2_ci],
            u_check_unassigned,
            vec![uh2_ci, uh_lit],
        );

        fb.switch_to_block(u_conflict);
        emit_set_conflicting_clause_index(&mut fb, ctx_ptr, uconf_ci);
        let uc_zero = fb.iconst(Ty::I64, 0);
        let uc_shifted = fb.binop(BinOp::Shl, Ty::I64, uc_zero, k32_i64);
        let uc_status = fb.iconst(Ty::I64, 1);
        let uc_packed = fb.binop(BinOp::Or, Ty::I64, uc_shifted, uc_status);
        fb.ret(vec![uc_packed]);

        fb.switch_to_block(u_check_unassigned);
        let u_skip2 = fb.create_block();
        let usk2_ci = fb.add_block_param(u_skip2, Ty::I64);
        fb.condbr(
            uh_is_unassigned,
            u_assign,
            vec![ucu_ci, ucu_lit],
            u_skip2,
            vec![ucu_ci],
        );

        fb.switch_to_block(u_skip2);
        let u_next_skip2 = fb.binop(BinOp::Add, Ty::I64, usk2_ci, k1_i64);
        fb.br(unit_header, vec![u_next_skip2]);

        fb.switch_to_block(u_assign);
        let ua_lit_neg = fb.binop(BinOp::Sub, Ty::I32, k0_i32, ua_lit);
        let ua_lit_is_neg = fb.icmp(ICmpOp::Slt, Ty::I32, ua_lit, k0_i32);
        let ua_var_i32 = fb.select(Ty::I32, ua_lit_is_neg, ua_lit_neg, ua_lit);
        let ua_var_i64 = fb.cast(trust_ir::CastOp::SExt, Ty::I32, Ty::I64, ua_var_i32);
        let ua_pos1 = fb.iconst(Ty::I8, 1);
        let ua_neg1 = fb.iconst(Ty::I8, -1);
        let ua_new_val = fb.select(Ty::I8, ua_lit_is_neg, ua_neg1, ua_pos1);
        let ua_val_dst = fb.gep(Ty::I8, values_ptr, vec![ua_var_i64]);
        fb.store(Ty::I8, ua_val_dst, ua_new_val);

        let ua_cur_tl = fb.load(Ty::I64, trail_len_ptr);
        let ua_trail_slot = fb.gep(Ty::I32, trail_ptr, vec![ua_cur_tl]);
        fb.store(Ty::I32, ua_trail_slot, ua_lit);
        let ua_new_tl = fb.binop(BinOp::Add, Ty::I64, ua_cur_tl, k1_i64);
        fb.store(Ty::I64, trail_len_ptr, ua_new_tl);

        let ua_next = fb.binop(BinOp::Add, Ty::I64, ua_ci, k1_i64);
        emit_record_implied_literal(
            &mut fb,
            ctx_ptr,
            ua_lit,
            Some(ua_ci),
            unit_header,
            vec![ua_next],
        );

        // ---- Phase 5: BCP loop ----
        fb.switch_to_block(bcp_loop);
        let bl_qhead = fb.load(Ty::I64, qhead_ptr);
        let bl_tl = fb.load(Ty::I64, trail_len_ptr);
        let bl_done = fb.icmp(ICmpOp::Sge, Ty::I64, bl_qhead, bl_tl);
        fb.condbr(bl_done, exit_ok, vec![bl_props], bcp_step, vec![bl_props]);

        fb.switch_to_block(bcp_step);
        let bs_qhead = fb.load(Ty::I64, qhead_ptr);
        let bs_assigned_ptr = fb.gep(Ty::I32, trail_ptr, vec![bs_qhead]);
        let bs_assigned = fb.load(Ty::I32, bs_assigned_ptr);
        let bs_qhead_p1 = fb.binop(BinOp::Add, Ty::I64, bs_qhead, k1_i64);
        fb.store(Ty::I64, qhead_ptr, bs_qhead_p1);

        // falsified = -assigned; falsified_idx = lit_index(falsified).
        let bs_falsified = fb.binop(BinOp::Sub, Ty::I32, k0_i32, bs_assigned);
        let bs_fl_neg = fb.binop(BinOp::Sub, Ty::I32, k0_i32, bs_falsified);
        let bs_fl_is_neg = fb.icmp(ICmpOp::Slt, Ty::I32, bs_falsified, k0_i32);
        let bs_fl_var_i32 = fb.select(Ty::I32, bs_fl_is_neg, bs_fl_neg, bs_falsified);
        let bs_fl_var_i64 = fb.cast(trust_ir::CastOp::SExt, Ty::I32, Ty::I64, bs_fl_var_i32);
        let bs_two_var = fb.binop(BinOp::Shl, Ty::I64, bs_fl_var_i64, k1_i64);
        let bs_neg_bit = fb.cast(trust_ir::CastOp::ZExt, Ty::Bool, Ty::I64, bs_fl_is_neg);
        let bs_falsified_idx = fb.binop(BinOp::Or, Ty::I64, bs_two_var, bs_neg_bit);

        // prev_next_ptr = &watch_heads[falsified_idx]; cur_node = *prev_next_ptr.
        let bs_head_slot = fb.gep(Ty::U32, watch_heads_ptr, vec![bs_falsified_idx]);
        let bs_cur_node = fb.load(Ty::U32, bs_head_slot);
        fb.br(
            walk_header,
            vec![
                bs_head_slot,
                bs_cur_node,
                bs_falsified,
                bs_falsified_idx,
                bs_props,
            ],
        );

        // ---- Phase 5a: walk the linked list ----
        fb.switch_to_block(walk_header);
        let wh_done = fb.icmp(ICmpOp::Eq, Ty::U32, wh_cur_node, k0_u32);
        fb.condbr(
            wh_done,
            bcp_loop,
            vec![wh_props],
            walk_body,
            vec![
                wh_prev_ptr,
                wh_cur_node,
                wh_falsified,
                wh_falsified_idx,
                wh_props,
            ],
        );

        fb.switch_to_block(walk_body);
        // Load clause_idx and next from this node.
        let wb_cur_node_i64 = fb.cast(trust_ir::CastOp::ZExt, Ty::U32, Ty::I64, wb_cur_node);
        let wb_two_n = fb.binop(BinOp::Shl, Ty::I64, wb_cur_node_i64, k1_i64);
        let wb_two_n_p1 = fb.binop(BinOp::Add, Ty::I64, wb_two_n, k1_i64);
        let wb_ci_slot = fb.gep(Ty::U32, watch_nodes_ptr, vec![wb_two_n]);
        let wb_next_slot = fb.gep(Ty::U32, watch_nodes_ptr, vec![wb_two_n_p1]);
        let wb_ci_u32 = fb.load(Ty::U32, wb_ci_slot);
        let wb_ci = fb.cast(trust_ir::CastOp::ZExt, Ty::U32, Ty::I64, wb_ci_u32);
        let wb_next_node = fb.load(Ty::U32, wb_next_slot);

        // Load clause start/end.
        let wb_off_start_ptr = fb.gep(Ty::U32, clause_offsets_ptr, vec![wb_ci]);
        let wb_off_start_u32 = fb.load(Ty::U32, wb_off_start_ptr);
        let wb_off_start = fb.cast(trust_ir::CastOp::ZExt, Ty::U32, Ty::I64, wb_off_start_u32);
        let wb_ci_p1 = fb.binop(BinOp::Add, Ty::I64, wb_ci, k1_i64);
        let wb_off_end_ptr = fb.gep(Ty::U32, clause_offsets_ptr, vec![wb_ci_p1]);
        let wb_off_end_u32 = fb.load(Ty::U32, wb_off_end_ptr);
        let wb_off_end = fb.cast(trust_ir::CastOp::ZExt, Ty::U32, Ty::I64, wb_off_end_u32);

        // Load clause[0] and clause[1]; swap so clause[1] is the falsified one.
        let wb_pos0_ptr = fb.gep(Ty::I32, clauses_lits_ptr, vec![wb_off_start]);
        let wb_lit0 = fb.load(Ty::I32, wb_pos0_ptr);
        let wb_off_start_p1 = fb.binop(BinOp::Add, Ty::I64, wb_off_start, k1_i64);
        let wb_pos1_ptr = fb.gep(Ty::I32, clauses_lits_ptr, vec![wb_off_start_p1]);
        let wb_lit1 = fb.load(Ty::I32, wb_pos1_ptr);

        let wb_lit0_is_falsified = fb.icmp(ICmpOp::Eq, Ty::I32, wb_lit0, wb_falsified);
        let wb_other = fb.select(Ty::I32, wb_lit0_is_falsified, wb_lit1, wb_lit0);
        fb.store(Ty::I32, wb_pos0_ptr, wb_other);
        fb.store(Ty::I32, wb_pos1_ptr, wb_falsified);

        // Check value_of_lit(other).
        let wb_other_neg = fb.binop(BinOp::Sub, Ty::I32, k0_i32, wb_other);
        let wb_other_is_neg = fb.icmp(ICmpOp::Slt, Ty::I32, wb_other, k0_i32);
        let wb_other_var_i32 = fb.select(Ty::I32, wb_other_is_neg, wb_other_neg, wb_other);
        let wb_other_var_i64 = fb.cast(trust_ir::CastOp::SExt, Ty::I32, Ty::I64, wb_other_var_i32);
        let wb_other_val_ptr = fb.gep(Ty::I8, values_ptr, vec![wb_other_var_i64]);
        let wb_other_val_i8 = fb.load(Ty::I8, wb_other_val_ptr);
        let wb_other_val_i32 = fb.cast(trust_ir::CastOp::SExt, Ty::I8, Ty::I32, wb_other_val_i8);
        let wb_other_neg_val = fb.binop(BinOp::Sub, Ty::I32, k0_i32, wb_other_val_i32);
        let wb_other_val_for_lit =
            fb.select(Ty::I32, wb_other_is_neg, wb_other_neg_val, wb_other_val_i32);
        let wb_other_is_true = fb.icmp(ICmpOp::Sgt, Ty::I32, wb_other_val_for_lit, k0_i32);

        // If other is true, keep watch in current list: advance prev_next_ptr
        // to this node's `next` field, advance cur_node to next_node.
        let other_true_branch = fb.create_block();
        let other_not_true_branch = fb.create_block();
        let ontb_falsified = fb.add_block_param(other_not_true_branch, Ty::I32);
        let ontb_falsified_idx = fb.add_block_param(other_not_true_branch, Ty::I64);
        let ontb_props = fb.add_block_param(other_not_true_branch, Ty::I64);
        let ontb_prev_ptr = fb.add_block_param(other_not_true_branch, Ty::Ptr);
        let ontb_cur_node = fb.add_block_param(other_not_true_branch, Ty::U32);
        let ontb_cur_next_ptr = fb.add_block_param(other_not_true_branch, Ty::Ptr);
        let ontb_next_node = fb.add_block_param(other_not_true_branch, Ty::U32);
        let ontb_ci = fb.add_block_param(other_not_true_branch, Ty::I64);
        let ontb_off_start = fb.add_block_param(other_not_true_branch, Ty::I64);
        let ontb_off_end = fb.add_block_param(other_not_true_branch, Ty::I64);

        fb.condbr(
            wb_other_is_true,
            other_true_branch,
            vec![],
            other_not_true_branch,
            vec![
                wb_falsified,
                wb_falsified_idx,
                wb_props,
                wb_prev_ptr,
                wb_cur_node,
                wb_next_slot,
                wb_next_node,
                wb_ci,
                wb_off_start,
                wb_off_end,
            ],
        );

        // other is true: advance through this node.
        fb.switch_to_block(other_true_branch);
        fb.br(
            walk_header,
            vec![
                wb_next_slot,
                wb_next_node,
                wb_falsified,
                wb_falsified_idx,
                wb_props,
            ],
        );

        // other is not true: search clause[2..end] for non-false replacement.
        fb.switch_to_block(other_not_true_branch);
        let ontb_search_start = fb.binop(BinOp::Add, Ty::I64, ontb_off_start, k2_i64);
        fb.br(
            search_header,
            vec![
                ontb_search_start,
                ontb_off_end,
                ontb_off_start,
                ontb_ci,
                ontb_prev_ptr,
                ontb_cur_node,
                ontb_cur_next_ptr,
                ontb_next_node,
                ontb_falsified,
                ontb_falsified_idx,
                ontb_props,
            ],
        );

        // search_header: iterate k from clause[2] to clause[end-1].
        fb.switch_to_block(search_header);
        let sh_done = fb.icmp(ICmpOp::Sge, Ty::I64, sh_k, sh_end);
        fb.condbr(
            sh_done,
            no_replacement,
            vec![
                sh_clause_start,
                sh_ci,
                sh_prev_ptr,
                sh_cur_node,
                sh_cur_next_ptr,
                sh_next_node,
                sh_falsified,
                sh_falsified_idx,
                sh_props,
            ],
            search_body,
            vec![
                sh_k,
                sh_end,
                sh_clause_start,
                sh_ci,
                sh_prev_ptr,
                sh_cur_node,
                sh_cur_next_ptr,
                sh_next_node,
                sh_falsified,
                sh_falsified_idx,
                sh_props,
            ],
        );

        fb.switch_to_block(search_body);
        let sb_cand_ptr = fb.gep(Ty::I32, clauses_lits_ptr, vec![sb_k]);
        let sb_cand = fb.load(Ty::I32, sb_cand_ptr);
        let sb_cand_neg = fb.binop(BinOp::Sub, Ty::I32, k0_i32, sb_cand);
        let sb_cand_is_neg = fb.icmp(ICmpOp::Slt, Ty::I32, sb_cand, k0_i32);
        let sb_cand_var_i32 = fb.select(Ty::I32, sb_cand_is_neg, sb_cand_neg, sb_cand);
        let sb_cand_var_i64 = fb.cast(trust_ir::CastOp::SExt, Ty::I32, Ty::I64, sb_cand_var_i32);
        let sb_cand_val_ptr = fb.gep(Ty::I8, values_ptr, vec![sb_cand_var_i64]);
        let sb_cand_val_i8 = fb.load(Ty::I8, sb_cand_val_ptr);
        let sb_cand_val_i32 = fb.cast(trust_ir::CastOp::SExt, Ty::I8, Ty::I32, sb_cand_val_i8);
        let sb_cand_neg_val = fb.binop(BinOp::Sub, Ty::I32, k0_i32, sb_cand_val_i32);
        let sb_cand_val_for_lit =
            fb.select(Ty::I32, sb_cand_is_neg, sb_cand_neg_val, sb_cand_val_i32);
        let sb_cand_is_false = fb.icmp(ICmpOp::Slt, Ty::I32, sb_cand_val_for_lit, k0_i32);

        let sb_advance = fb.create_block();
        let sba_k = fb.add_block_param(sb_advance, Ty::I64);
        let sba_end = fb.add_block_param(sb_advance, Ty::I64);
        let sba_clause_start = fb.add_block_param(sb_advance, Ty::I64);
        let sba_ci = fb.add_block_param(sb_advance, Ty::I64);
        let sba_prev_ptr = fb.add_block_param(sb_advance, Ty::Ptr);
        let sba_cur_node = fb.add_block_param(sb_advance, Ty::U32);
        let sba_cur_next_ptr = fb.add_block_param(sb_advance, Ty::Ptr);
        let sba_next_node = fb.add_block_param(sb_advance, Ty::U32);
        let sba_falsified = fb.add_block_param(sb_advance, Ty::I32);
        let sba_falsified_idx = fb.add_block_param(sb_advance, Ty::I64);
        let sba_props = fb.add_block_param(sb_advance, Ty::I64);

        let sb_found = fb.create_block();
        let sbf_k = fb.add_block_param(sb_found, Ty::I64);
        let sbf_clause_start = fb.add_block_param(sb_found, Ty::I64);
        let sbf_ci = fb.add_block_param(sb_found, Ty::I64);
        let sbf_prev_ptr = fb.add_block_param(sb_found, Ty::Ptr);
        let sbf_cur_node = fb.add_block_param(sb_found, Ty::U32);
        let sbf_cur_next_ptr = fb.add_block_param(sb_found, Ty::Ptr);
        let sbf_next_node = fb.add_block_param(sb_found, Ty::U32);
        let sbf_falsified = fb.add_block_param(sb_found, Ty::I32);
        let sbf_falsified_idx = fb.add_block_param(sb_found, Ty::I64);
        let sbf_props = fb.add_block_param(sb_found, Ty::I64);
        let sbf_cand = fb.add_block_param(sb_found, Ty::I32);

        fb.condbr(
            sb_cand_is_false,
            sb_advance,
            vec![
                sb_k,
                sb_end,
                sb_clause_start,
                sb_ci,
                sb_prev_ptr,
                sb_cur_node,
                sb_cur_next_ptr,
                sb_next_node,
                sb_falsified,
                sb_falsified_idx,
                sb_props,
            ],
            sb_found,
            vec![
                sb_k,
                sb_clause_start,
                sb_ci,
                sb_prev_ptr,
                sb_cur_node,
                sb_cur_next_ptr,
                sb_next_node,
                sb_falsified,
                sb_falsified_idx,
                sb_props,
                sb_cand,
            ],
        );

        fb.switch_to_block(sb_advance);
        let sba_next_k = fb.binop(BinOp::Add, Ty::I64, sba_k, k1_i64);
        fb.br(
            search_header,
            vec![
                sba_next_k,
                sba_end,
                sba_clause_start,
                sba_ci,
                sba_prev_ptr,
                sba_cur_node,
                sba_cur_next_ptr,
                sba_next_node,
                sba_falsified,
                sba_falsified_idx,
                sba_props,
            ],
        );

        // Found replacement at k: swap clause[1] with clause[k], detach
        // cur_node from current list, and prepend cur_node onto
        // watch_heads[lit_index(cand)].
        fb.switch_to_block(sb_found);
        // clause[1] <- cand; clause[k] <- falsified.
        let sbf_pos1_off = fb.binop(BinOp::Add, Ty::I64, sbf_clause_start, k1_i64);
        let sbf_pos1_ptr = fb.gep(Ty::I32, clauses_lits_ptr, vec![sbf_pos1_off]);
        let sbf_posk_ptr = fb.gep(Ty::I32, clauses_lits_ptr, vec![sbf_k]);
        fb.store(Ty::I32, sbf_pos1_ptr, sbf_cand);
        fb.store(Ty::I32, sbf_posk_ptr, sbf_falsified);

        // Detach cur_node: *prev_ptr = next_node.
        fb.store(Ty::U32, sbf_prev_ptr, sbf_next_node);

        // Prepend cur_node to watch_heads[lit_index(cand)]:
        //   cur_node.next = watch_heads[cand_idx]
        //   watch_heads[cand_idx] = cur_node
        let sbf_cand_neg = fb.binop(BinOp::Sub, Ty::I32, k0_i32, sbf_cand);
        let sbf_cand_is_neg = fb.icmp(ICmpOp::Slt, Ty::I32, sbf_cand, k0_i32);
        let sbf_cand_var_i32 = fb.select(Ty::I32, sbf_cand_is_neg, sbf_cand_neg, sbf_cand);
        let sbf_cand_var_i64 = fb.cast(trust_ir::CastOp::SExt, Ty::I32, Ty::I64, sbf_cand_var_i32);
        let sbf_two_var = fb.binop(BinOp::Shl, Ty::I64, sbf_cand_var_i64, k1_i64);
        let sbf_neg_bit = fb.cast(trust_ir::CastOp::ZExt, Ty::Bool, Ty::I64, sbf_cand_is_neg);
        let sbf_cand_idx = fb.binop(BinOp::Or, Ty::I64, sbf_two_var, sbf_neg_bit);

        let sbf_cand_head_slot = fb.gep(Ty::U32, watch_heads_ptr, vec![sbf_cand_idx]);
        let sbf_cand_old_head = fb.load(Ty::U32, sbf_cand_head_slot);
        fb.store(Ty::U32, sbf_cur_next_ptr, sbf_cand_old_head);
        fb.store(Ty::U32, sbf_cand_head_slot, sbf_cur_node);

        // Continue walking the current literal's list from next_node.
        // prev_next_ptr is UNCHANGED: it still points to where cur_node
        // used to be linked, which is now `next_node`.
        let _ = sbf_falsified_idx; // routed through but redundant here
        fb.br(
            walk_header,
            vec![
                sbf_prev_ptr,
                sbf_next_node,
                sbf_falsified,
                sbf_falsified_idx,
                sbf_props,
            ],
        );

        // ---- no_replacement: keep watch in current list, then check `other`. ----
        fb.switch_to_block(no_replacement);
        // Reload `other` from clause[0].
        let nr_pos0_ptr = fb.gep(Ty::I32, clauses_lits_ptr, vec![nr_clause_start]);
        let nr_other = fb.load(Ty::I32, nr_pos0_ptr);
        let nr_other_neg = fb.binop(BinOp::Sub, Ty::I32, k0_i32, nr_other);
        let nr_other_is_neg = fb.icmp(ICmpOp::Slt, Ty::I32, nr_other, k0_i32);
        let nr_other_var_i32 = fb.select(Ty::I32, nr_other_is_neg, nr_other_neg, nr_other);
        let nr_other_var_i64 = fb.cast(trust_ir::CastOp::SExt, Ty::I32, Ty::I64, nr_other_var_i32);
        let nr_other_val_ptr = fb.gep(Ty::I8, values_ptr, vec![nr_other_var_i64]);
        let nr_other_val_i8 = fb.load(Ty::I8, nr_other_val_ptr);
        let nr_other_val_i32 = fb.cast(trust_ir::CastOp::SExt, Ty::I8, Ty::I32, nr_other_val_i8);
        let nr_other_neg_val = fb.binop(BinOp::Sub, Ty::I32, k0_i32, nr_other_val_i32);
        let nr_other_val_for_lit =
            fb.select(Ty::I32, nr_other_is_neg, nr_other_neg_val, nr_other_val_i32);
        let nr_other_is_false = fb.icmp(ICmpOp::Slt, Ty::I32, nr_other_val_for_lit, k0_i32);

        let nr_conflict_branch = fb.create_block();
        let nrcb_ci = fb.add_block_param(nr_conflict_branch, Ty::I64);
        let nrcb_props = fb.add_block_param(nr_conflict_branch, Ty::I64);

        let nr_propagate_branch = fb.create_block();
        let nrpb_falsified = fb.add_block_param(nr_propagate_branch, Ty::I32);
        let nrpb_falsified_idx = fb.add_block_param(nr_propagate_branch, Ty::I64);
        let nrpb_props = fb.add_block_param(nr_propagate_branch, Ty::I64);
        let nrpb_cur_next_ptr = fb.add_block_param(nr_propagate_branch, Ty::Ptr);
        let nrpb_next_node = fb.add_block_param(nr_propagate_branch, Ty::U32);
        let nrpb_other = fb.add_block_param(nr_propagate_branch, Ty::I32);
        let nrpb_ci = fb.add_block_param(nr_propagate_branch, Ty::I64);

        let _ = nr_prev_ptr;
        let _ = nr_cur_node;
        fb.condbr(
            nr_other_is_false,
            nr_conflict_branch,
            vec![nr_ci, nr_props],
            nr_propagate_branch,
            vec![
                nr_falsified,
                nr_falsified_idx,
                nr_props,
                nr_cur_next_ptr,
                nr_next_node,
                nr_other,
                nr_ci,
            ],
        );

        fb.switch_to_block(nr_conflict_branch);
        // The chunked layout's "keep watch in current list" is a no-op:
        // cur_node is already linked at prev_next_ptr (we never removed
        // it). On conflict, the list is already well-formed (every
        // remaining unprocessed node is still reachable). We can exit
        // directly.
        fb.br(exit_conflict, vec![nrcb_props, nrcb_ci]);

        // Propagate `other`: assign + push, advance prev to this node's
        // next field, continue walking from next_node.
        fb.switch_to_block(nr_propagate_branch);
        let nrpb_other_neg = fb.binop(BinOp::Sub, Ty::I32, k0_i32, nrpb_other);
        let nrpb_other_is_neg = fb.icmp(ICmpOp::Slt, Ty::I32, nrpb_other, k0_i32);
        let nrpb_other_var_i32 = fb.select(Ty::I32, nrpb_other_is_neg, nrpb_other_neg, nrpb_other);
        let nrpb_other_var_i64 =
            fb.cast(trust_ir::CastOp::SExt, Ty::I32, Ty::I64, nrpb_other_var_i32);
        let pos1_in_p = fb.iconst(Ty::I8, 1);
        let neg1_in_p = fb.iconst(Ty::I8, -1);
        let nrpb_new_val = fb.select(Ty::I8, nrpb_other_is_neg, neg1_in_p, pos1_in_p);
        let nrpb_val_dst = fb.gep(Ty::I8, values_ptr, vec![nrpb_other_var_i64]);
        fb.store(Ty::I8, nrpb_val_dst, nrpb_new_val);

        let nrpb_cur_tl = fb.load(Ty::I64, trail_len_ptr);
        let nrpb_trail_slot = fb.gep(Ty::I32, trail_ptr, vec![nrpb_cur_tl]);
        fb.store(Ty::I32, nrpb_trail_slot, nrpb_other);
        let nrpb_new_tl = fb.binop(BinOp::Add, Ty::I64, nrpb_cur_tl, k1_i64);
        fb.store(Ty::I64, trail_len_ptr, nrpb_new_tl);

        let nrpb_new_props = fb.binop(BinOp::Add, Ty::I64, nrpb_props, k1_i64);
        // Advance: prev_next_ptr = cur_node's next-field; cur_node = next_node.
        emit_record_implied_literal(
            &mut fb,
            ctx_ptr,
            nrpb_other,
            Some(nrpb_ci),
            walk_header,
            vec![
                nrpb_cur_next_ptr,
                nrpb_next_node,
                nrpb_falsified,
                nrpb_falsified_idx,
                nrpb_new_props,
            ],
        );

        // ---- Exit blocks ----
        fb.switch_to_block(exit_conflict);
        emit_set_conflicting_clause_index(&mut fb, ctx_ptr, xc_ci);
        let xc_shifted = fb.binop(BinOp::Shl, Ty::I64, xc_props, k32_i64);
        let xc_one = fb.iconst(Ty::I64, 1);
        let xc_packed = fb.binop(BinOp::Or, Ty::I64, xc_shifted, xc_one);
        fb.ret(vec![xc_packed]);

        fb.switch_to_block(exit_ok);
        let xo_packed = fb.binop(BinOp::Shl, Ty::I64, xo_props, k32_i64);
        fb.ret(vec![xo_packed]);

        // Silence unused-variable warnings for params held purely for
        // dataflow routing (e.g. `sbf_ci` is the clause index the search
        // started with; we have it via the node so we never need to
        // re-load it in sb_found, but the search_header signature carries
        // it for symmetry with the fixed-cap kernel).
        let _ = (input_ptr, sbf_ci);

        fb.build();
    }

    mb.build()
}

/// Heap-pinned arena for the chunked-layout watched-literal BCP kernel.
///
/// Compared to `BcpWatchedArena`, this arena swaps the per-literal
/// fixed-capacity row-major watch table (`(2*num_vars + 2) *
/// max(num_clauses, 1) * 4` bytes) for a chunked free-list layout
/// (`(2*num_vars + 2) * 4` bytes for `watch_heads` plus `(2 *
/// num_clauses + 1) * 8` bytes for `watch_nodes`). The asymptotic
/// improvement is from `O(num_vars * num_clauses)` to `O(num_vars +
/// num_clauses)`, matching what MicroSAT's C implementation does.
pub struct BcpWatchedChunkedArena {
    pub header: Vec<u64>,
    /// Mutable clause-literal arena. The chunked kernel performs the
    /// same watched-position swaps the fixed-cap kernel does, so
    /// `clauses_lits` must be reset to `original_clauses_lits` between
    /// calls for repeatability.
    pub clauses_lits: Vec<i32>,
    pub original_clauses_lits: Vec<i32>,
    pub clause_offsets: Vec<u32>,
    pub values: Vec<i8>,
    pub trail: Vec<i32>,
    pub trail_len: Box<u64>,
    /// `watch_heads[i]` = head node index of literal i's watch list,
    /// or 0 if empty. Sized `2*num_vars + 2` (with the `+2` matching the
    /// fixed-cap kernel's "lit_index(var=num_vars, neg) + 1" upper
    /// bound).
    pub watch_heads: Vec<u32>,
    /// Flat node pool. Each node occupies two `u32` slots:
    ///   `watch_nodes[2*k]   = clause_idx`
    ///   `watch_nodes[2*k+1] = next` (0 = end of list)
    /// Node 0 is the sentinel; first usable node is index 1. Total
    /// capacity is `2 * num_clauses + 1` nodes (`= 4 * num_clauses + 2`
    /// `u32` slots), regardless of any individual literal's degree.
    pub watch_nodes: Vec<u32>,
    /// Node count (including sentinel). Published in slot 9 of the
    /// arena header so a future variant can bounds-check; the current
    /// kernel does not read it at runtime.
    pub watch_node_capacity: u64,
    pub qhead: Box<u64>,
    /// Free-list head sentinel. Reserved in the ABI (slot 11) but never
    /// used by the chunked BCP kernel itself (no node is ever freed
    /// during BCP — nodes are only re-linked). Kept as a `Box<u32>` so
    /// the arena header carries a stable pointer.
    pub watch_free_head: Box<u32>,
}

impl BcpWatchedChunkedArena {
    pub fn build(num_vars: usize, clauses: &[Vec<i32>], trail_capacity: usize) -> Self {
        let mut clauses_lits: Vec<i32> = Vec::new();
        let mut clause_offsets: Vec<u32> = Vec::with_capacity(clauses.len() + 1);
        clause_offsets.push(0);
        for c in clauses {
            for &lit in c {
                clauses_lits.push(lit);
            }
            clause_offsets.push(clauses_lits.len() as u32);
        }
        let original_clauses_lits = clauses_lits.clone();
        let values = vec![0i8; num_vars + 1];
        let trail = vec![0i32; trail_capacity];
        let trail_len = Box::new(0u64);
        let qhead = Box::new(0u64);
        let watch_free_head = Box::new(0u32);

        // 2*num_vars + 2 head slots (matches the fixed-cap kernel's row
        // count; preserves the kernel-side lit_index encoding).
        let head_count = 2 * num_vars + 2;
        let watch_heads = vec![0u32; head_count];

        // Node pool: 1 sentinel + 2 per clause. Each node = 2 u32 slots.
        // This is correct regardless of any individual literal's degree:
        // every (clause_idx, watched_position) pair owns exactly one
        // node for the lifetime of the arena; BCP only re-links nodes
        // between heads.
        let node_count: u64 = 2 * (clauses.len() as u64) + 1;
        let watch_nodes = vec![0u32; (node_count as usize) * 2];

        let mut arena = BcpWatchedChunkedArena {
            header: vec![0u64; 12],
            clauses_lits,
            original_clauses_lits,
            clause_offsets,
            values,
            trail,
            trail_len,
            watch_heads,
            watch_nodes,
            watch_node_capacity: node_count,
            qhead,
            watch_free_head,
        };
        arena.header[0] = num_vars as u64;
        arena.header[1] = clauses.len() as u64;
        arena.header[2] = arena.clauses_lits.as_mut_ptr() as u64;
        arena.header[3] = arena.clause_offsets.as_ptr() as u64;
        arena.header[4] = arena.values.as_mut_ptr() as u64;
        arena.header[5] = arena.trail.as_mut_ptr() as u64;
        arena.header[6] = (&mut *arena.trail_len) as *mut u64 as u64;
        arena.header[7] = arena.watch_heads.as_mut_ptr() as u64;
        arena.header[8] = arena.watch_nodes.as_mut_ptr() as u64;
        arena.header[9] = arena.watch_node_capacity;
        arena.header[10] = (&mut *arena.qhead) as *mut u64 as u64;
        arena.header[11] = (&mut *arena.watch_free_head) as *mut u32 as u64;
        arena
    }

    pub fn header_ptr(&mut self) -> *mut u8 {
        self.header.as_mut_ptr() as *mut u8
    }

    pub fn header_byte_len(&self) -> usize {
        self.header.len() * 8
    }

    pub fn trail_len(&self) -> u64 {
        *self.trail_len
    }

    pub fn values_at(&self, var: usize) -> i8 {
        self.values[var]
    }

    /// Total bytes owned by the watch infrastructure (`watch_heads` +
    /// `watch_nodes`). Excludes the header / trail / values / clause
    /// storage so the bench comparison can isolate the chunked-vs-fixed
    /// memory delta.
    pub fn watch_memory_bytes(&self) -> usize {
        self.watch_heads.len() * std::mem::size_of::<u32>()
            + self.watch_nodes.len() * std::mem::size_of::<u32>()
    }

    /// Reset everything the kernel mutates so the next call observes
    /// the same start state as the very first call.
    pub fn reset_arena(&mut self) {
        for v in self.values.iter_mut() {
            *v = 0;
        }
        *self.trail_len = 0;
        *self.qhead = 0;
        self.clauses_lits
            .copy_from_slice(&self.original_clauses_lits);
        for slot in self.watch_heads.iter_mut() {
            *slot = 0;
        }
        // `watch_nodes` is fully rewritten by the kernel's Phase 2 every
        // call, so we don't bother zeroing it host-side.
    }
}
