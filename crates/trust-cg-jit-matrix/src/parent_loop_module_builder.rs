// trust-cg-jit-matrix/src/parent_loop_module_builder.rs - TLA+/TY parent-loop kernel
// authored in trust_ir. First application of the verified-JIT pattern beyond BCP.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// # What this kernel does
//
// Mirrors `parent_loop_baseline::explore_one_step` over a fixed-capacity arena.
// One kernel call runs up to `input_len` parent steps (the `input` slice itself
// is unused — it is repurposed as a step budget). The kernel returns early on
// frontier-empty or invariant violation.
//
// The state visited-set in the native baseline is `HashSet<State>`. The JIT
// version uses a direct-indexed bitmap sized to `2^num_vars / 64` u64 words.
// Since `random_transition_system` masks every state to `num_vars` bits and
// `apply_action` preserves that mask, direct indexing is sound and matches the
// baseline set semantics exactly. Maximum supported state width is therefore
// bounded by the bitmap arena allocation (the native baseline has the same
// 64-bit upper bound).
//
// # Arena layout (16 u64 header slots)
//
// ```text
//   +  0: num_vars
//   +  1: num_actions
//   +  2: actions_ptr            -> u64[4 * num_actions]
//                                   (guard_mask, guard_value, set_mask, set_value)
//   +  3: invariant_mask
//   +  4: invariant_value
//   +  5: visited_word_count     (power of two; equals 2^num_vars / 64)
//   +  6: visited_ptr            -> u64[visited_word_count]
//   +  7: frontier_ptr           -> u64[frontier_cap]
//   +  8: frontier_cap           (host bookkeeping; kernel does NOT bounds check)
//   +  9: frontier_len_ptr       -> u64
//   + 10: parent_count_ptr       -> u64
//   + 11: generated_count_ptr    -> u64
//   + 12: parent_digest_ptr      -> u64
//   + 13: fingerprint_ptr        -> u64
//   + 14: invariant_violations_ptr -> u64
//   + 15: last_violating_state_ptr -> u64
// ```
//
// # Kernel return contract
//
// Packed status word, low 32 bits = result code, high 32 bits = step counter
// (number of `explore_one_step` iterations executed by this call):
//
// - `PARENT_LOOP_RESULT_CONTINUED` (0): step budget exhausted without
//   frontier empty / invariant violation.
// - `PARENT_LOOP_RESULT_FRONTIER_EMPTY` (1): frontier reached empty during
//   the call. The step counter is the number of completed steps before
//   the empty pop.
// - `PARENT_LOOP_RESULT_INVARIANT_VIOLATION` (2): a successor failed the
//   invariant. `last_violating_state` holds the offending state. The
//   per-step counters are updated normally up to and including that step.

use trust_ir::{BinOp, ICmpOp, Ty, ValueId};
use trust_ir_build::{FunctionBuilder, ModuleBuilder};

use crate::bcp_module_builder::CTX_SLOT_ARENA_PTR;

pub const PARENT_LOOP_ENTRY_NAME: &str = "parent_loop_explore_steps";

pub const PARENT_LOOP_RESULT_CONTINUED: u32 = 0;
pub const PARENT_LOOP_RESULT_FRONTIER_EMPTY: u32 = 1;
pub const PARENT_LOOP_RESULT_INVARIANT_VIOLATION: u32 = 2;

/// Build the trust-ir module for the JIT'd parent-loop kernel. The
/// resulting `Module` exports one function named `PARENT_LOOP_ENTRY_NAME`
/// with the standard `KernelEntry` signature `(ctx, _input, max_steps) -> u64`.
pub fn build_parent_loop_module() -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("parent_loop_explore_steps");

    let entry_ty = mb.add_func_type(vec![Ty::Ptr, Ty::Ptr, Ty::I64], vec![Ty::I64]);

    {
        let mut fb = mb.function(PARENT_LOOP_ENTRY_NAME, entry_ty);

        // ---- Block declarations -------------------------------------
        let entry = fb.create_block();
        let ctx_ptr = fb.add_block_param(entry, Ty::Ptr);
        let _input_ptr = fb.add_block_param(entry, Ty::Ptr);
        let max_steps = fb.add_block_param(entry, Ty::I64);

        // Outer step header: takes (steps_done).
        let step_header = fb.create_block();
        let sh_steps = fb.add_block_param(step_header, Ty::I64);

        // Action loop header: takes (steps_done, action_idx, parent_state).
        let action_header = fb.create_block();
        let ah_steps = fb.add_block_param(action_header, Ty::I64);
        let ah_idx = fb.add_block_param(action_header, Ty::I64);
        let ah_parent = fb.add_block_param(action_header, Ty::I64);

        // Action body: examine actions[ah_idx], possibly produce successor.
        let action_body = fb.create_block();
        let ab_steps = fb.add_block_param(action_body, Ty::I64);
        let ab_idx = fb.add_block_param(action_body, Ty::I64);
        let ab_parent = fb.add_block_param(action_body, Ty::I64);

        // Action done: advance idx and loop to action_header.
        let action_skip = fb.create_block();
        let asx_steps = fb.add_block_param(action_skip, Ty::I64);
        let asx_idx = fb.add_block_param(action_skip, Ty::I64);
        let asx_parent = fb.add_block_param(action_skip, Ty::I64);

        // Exit blocks: parameterised by completed steps + (optional) violating
        // state for the violation branch.
        let exit_continued = fb.create_block();
        let xc_steps = fb.add_block_param(exit_continued, Ty::I64);

        let exit_frontier_empty = fb.create_block();
        let xfe_steps = fb.add_block_param(exit_frontier_empty, Ty::I64);

        let exit_invariant = fb.create_block();
        let xv_steps = fb.add_block_param(exit_invariant, Ty::I64);
        let xv_state = fb.add_block_param(exit_invariant, Ty::I64);

        // ---- Entry: load all arena slots ----------------------------
        fb.switch_to_block(entry);

        let k0_i64 = fb.iconst(Ty::I64, 0);
        let k1_i64 = fb.iconst(Ty::I64, 1);
        let k2_i64 = fb.iconst(Ty::I64, 2);
        let k3_i64 = fb.iconst(Ty::I64, 3);
        let k6_i64 = fb.iconst(Ty::I64, 6);
        let k13_i64 = fb.iconst(Ty::I64, 13);
        let k32_i64 = fb.iconst(Ty::I64, 32);
        let k51_i64 = fb.iconst(Ty::I64, 51);
        let k63_i64 = fb.iconst(Ty::I64, 63);
        // Action record stride is 4 u64s -> offset = idx << 2 (log2 = 2).
        let k_action_stride_log2 = k2_i64;
        let k_golden_ratio_i64 = fb.iconst(Ty::I64, 0x9e3779b97f4a7c15_u64 as i128);

        // ctx[0] -> arena_ptr; then walk arena slots.
        let arena_slot_off = fb.iconst(Ty::I64, CTX_SLOT_ARENA_PTR);
        let arena_slot_ptr = fb.gep(Ty::I64, ctx_ptr, vec![arena_slot_off]);
        let arena_addr = fb.load(Ty::I64, arena_slot_ptr);
        let arena_ptr = fb.cast(trust_ir::CastOp::IntToPtr, Ty::I64, Ty::Ptr, arena_addr);

        let load_slot_u64 = |fb: &mut FunctionBuilder<'_>, idx: i128| -> ValueId {
            let off = fb.iconst(Ty::I64, idx);
            let p = fb.gep(Ty::I64, arena_ptr, vec![off]);
            fb.load(Ty::I64, p)
        };
        let load_slot_ptr = |fb: &mut FunctionBuilder<'_>, idx: i128| -> ValueId {
            let raw = load_slot_u64(fb, idx);
            fb.cast(trust_ir::CastOp::IntToPtr, Ty::I64, Ty::Ptr, raw)
        };

        let _num_vars = load_slot_u64(&mut fb, 0);
        let num_actions = load_slot_u64(&mut fb, 1);
        let actions_ptr = load_slot_ptr(&mut fb, 2);
        let invariant_mask = load_slot_u64(&mut fb, 3);
        let invariant_value = load_slot_u64(&mut fb, 4);
        let _visited_word_count = load_slot_u64(&mut fb, 5);
        let visited_ptr = load_slot_ptr(&mut fb, 6);
        let frontier_ptr = load_slot_ptr(&mut fb, 7);
        let _frontier_cap = load_slot_u64(&mut fb, 8);
        let frontier_len_ptr = load_slot_ptr(&mut fb, 9);
        let parent_count_ptr = load_slot_ptr(&mut fb, 10);
        let generated_count_ptr = load_slot_ptr(&mut fb, 11);
        let parent_digest_ptr = load_slot_ptr(&mut fb, 12);
        let fingerprint_ptr = load_slot_ptr(&mut fb, 13);
        let invariant_violations_ptr = load_slot_ptr(&mut fb, 14);
        let last_violating_state_ptr = load_slot_ptr(&mut fb, 15);

        // Begin the outer step loop with steps_done = 0.
        fb.br(step_header, vec![k0_i64]);

        // ---- step_header: budget check, then pop a parent ---------
        fb.switch_to_block(step_header);
        let budget_done = fb.icmp(ICmpOp::Sge, Ty::I64, sh_steps, max_steps);

        // We need a "do step" block to actually execute one step.
        let do_step = fb.create_block();
        let ds_steps = fb.add_block_param(do_step, Ty::I64);

        fb.condbr(
            budget_done,
            exit_continued,
            vec![sh_steps],
            do_step,
            vec![sh_steps],
        );

        // ---- do_step: pop one parent from the frontier ------------
        fb.switch_to_block(do_step);
        let f_len = fb.load(Ty::I64, frontier_len_ptr);
        let frontier_empty = fb.icmp(ICmpOp::Eq, Ty::I64, f_len, k0_i64);

        let pop_parent = fb.create_block();
        let pp_steps = fb.add_block_param(pop_parent, Ty::I64);

        fb.condbr(
            frontier_empty,
            exit_frontier_empty,
            vec![ds_steps],
            pop_parent,
            vec![ds_steps],
        );

        // ---- pop_parent: read frontier[f_len-1], decrement len ----
        fb.switch_to_block(pop_parent);
        let new_f_len = fb.binop(BinOp::Sub, Ty::I64, f_len, k1_i64);
        // Store the new length first (the slot contents stay live but unused).
        fb.store(Ty::I64, frontier_len_ptr, new_f_len);
        let parent_slot = fb.gep(Ty::I64, frontier_ptr, vec![new_f_len]);
        let parent_state = fb.load(Ty::I64, parent_slot);

        // parent_count += 1
        let pc = fb.load(Ty::I64, parent_count_ptr);
        let pc_next = fb.binop(BinOp::Add, Ty::I64, pc, k1_i64);
        fb.store(Ty::I64, parent_count_ptr, pc_next);

        // parent_digest += mix(parent)
        // mix(x) = x.wrapping_mul(GOLDEN).rotate_left(13)
        // rotate_left(x, 13) = (x << 13) | (x >> (64 - 13)) = (x << 13) | (x >> 51)
        let pmul = fb.binop(BinOp::Mul, Ty::I64, parent_state, k_golden_ratio_i64);
        let plo = fb.binop(BinOp::Shl, Ty::I64, pmul, k13_i64);
        let phi = fb.binop(BinOp::LShr, Ty::I64, pmul, k51_i64);
        let pmix = fb.binop(BinOp::Or, Ty::I64, plo, phi);
        let pd = fb.load(Ty::I64, parent_digest_ptr);
        let pd_next = fb.binop(BinOp::Add, Ty::I64, pd, pmix);
        fb.store(Ty::I64, parent_digest_ptr, pd_next);

        // Enter the per-action loop.
        fb.br(action_header, vec![pp_steps, k0_i64, parent_state]);

        // ---- action_header: bound check, branch to body / advance step
        fb.switch_to_block(action_header);
        let actions_done = fb.icmp(ICmpOp::Sge, Ty::I64, ah_idx, num_actions);

        // When the per-parent action sweep is done, this step is complete:
        // increment steps and loop back to the step header.
        let step_done = fb.create_block();
        let stp_steps = fb.add_block_param(step_done, Ty::I64);

        fb.condbr(
            actions_done,
            step_done,
            vec![ah_steps],
            action_body,
            vec![ah_steps, ah_idx, ah_parent],
        );

        // ---- step_done: steps_done + 1, loop to step_header -------
        fb.switch_to_block(step_done);
        let stp_next = fb.binop(BinOp::Add, Ty::I64, stp_steps, k1_i64);
        fb.br(step_header, vec![stp_next]);

        // ---- action_body: examine one action ----------------------
        fb.switch_to_block(action_body);

        // action_offset = ab_idx * 4
        let action_off = fb.binop(BinOp::Shl, Ty::I64, ab_idx, k_action_stride_log2);
        let guard_mask_slot = fb.gep(Ty::I64, actions_ptr, vec![action_off]);
        let guard_mask = fb.load(Ty::I64, guard_mask_slot);
        let off_plus1 = fb.binop(BinOp::Add, Ty::I64, action_off, k1_i64);
        let guard_value_slot = fb.gep(Ty::I64, actions_ptr, vec![off_plus1]);
        let guard_value = fb.load(Ty::I64, guard_value_slot);
        let off_plus2 = fb.binop(BinOp::Add, Ty::I64, action_off, k2_i64);
        let set_mask_slot = fb.gep(Ty::I64, actions_ptr, vec![off_plus2]);
        let set_mask = fb.load(Ty::I64, set_mask_slot);
        let off_plus3 = fb.binop(BinOp::Add, Ty::I64, action_off, k3_i64);
        let set_value_slot = fb.gep(Ty::I64, actions_ptr, vec![off_plus3]);
        let set_value = fb.load(Ty::I64, set_value_slot);

        // enabled = (parent & guard_mask) == guard_value
        let parent_masked = fb.binop(BinOp::And, Ty::I64, ab_parent, guard_mask);
        let enabled = fb.icmp(ICmpOp::Eq, Ty::I64, parent_masked, guard_value);

        let apply_action = fb.create_block();
        let aa_steps = fb.add_block_param(apply_action, Ty::I64);
        let aa_idx = fb.add_block_param(apply_action, Ty::I64);
        let aa_parent = fb.add_block_param(apply_action, Ty::I64);
        let aa_set_mask = fb.add_block_param(apply_action, Ty::I64);
        let aa_set_value = fb.add_block_param(apply_action, Ty::I64);

        fb.condbr(
            enabled,
            apply_action,
            vec![ab_steps, ab_idx, ab_parent, set_mask, set_value],
            action_skip,
            vec![ab_steps, ab_idx, ab_parent],
        );

        // ---- action_skip: advance idx, loop back ------------------
        fb.switch_to_block(action_skip);
        let ask_next = fb.binop(BinOp::Add, Ty::I64, asx_idx, k1_i64);
        fb.br(action_header, vec![asx_steps, ask_next, asx_parent]);

        // ---- apply_action: compute successor + invariant + dedup --
        fb.switch_to_block(apply_action);

        // succ = (parent & !set_mask) | set_value
        let minus_one = fb.iconst(Ty::I64, -1);
        let inv_mask = fb.binop(BinOp::Xor, Ty::I64, aa_set_mask, minus_one);
        let masked_parent = fb.binop(BinOp::And, Ty::I64, aa_parent, inv_mask);
        let succ = fb.binop(BinOp::Or, Ty::I64, masked_parent, aa_set_value);

        // generated_count += 1
        let gc = fb.load(Ty::I64, generated_count_ptr);
        let gc_next = fb.binop(BinOp::Add, Ty::I64, gc, k1_i64);
        fb.store(Ty::I64, generated_count_ptr, gc_next);

        // fingerprint += mix(succ)
        let smul = fb.binop(BinOp::Mul, Ty::I64, succ, k_golden_ratio_i64);
        let slo = fb.binop(BinOp::Shl, Ty::I64, smul, k13_i64);
        let shi = fb.binop(BinOp::LShr, Ty::I64, smul, k51_i64);
        let smix = fb.binop(BinOp::Or, Ty::I64, slo, shi);
        let fp = fb.load(Ty::I64, fingerprint_ptr);
        let fp_next = fb.binop(BinOp::Add, Ty::I64, fp, smix);
        fb.store(Ty::I64, fingerprint_ptr, fp_next);

        // invariant check: (succ & invariant_mask) != invariant_value -> violation
        let succ_masked = fb.binop(BinOp::And, Ty::I64, succ, invariant_mask);
        let inv_holds = fb.icmp(ICmpOp::Eq, Ty::I64, succ_masked, invariant_value);

        let check_visited = fb.create_block();
        let cv_steps = fb.add_block_param(check_visited, Ty::I64);
        let cv_idx = fb.add_block_param(check_visited, Ty::I64);
        let cv_parent = fb.add_block_param(check_visited, Ty::I64);
        let cv_succ = fb.add_block_param(check_visited, Ty::I64);

        // On violation: increment invariant_violations, store last_violating_state,
        // jump to exit_invariant.
        let do_violation = fb.create_block();
        let dv_steps = fb.add_block_param(do_violation, Ty::I64);
        let dv_succ = fb.add_block_param(do_violation, Ty::I64);

        fb.condbr(
            inv_holds,
            check_visited,
            vec![aa_steps, aa_idx, aa_parent, succ],
            do_violation,
            vec![aa_steps, succ],
        );

        fb.switch_to_block(do_violation);
        let iv = fb.load(Ty::I64, invariant_violations_ptr);
        let iv_next = fb.binop(BinOp::Add, Ty::I64, iv, k1_i64);
        fb.store(Ty::I64, invariant_violations_ptr, iv_next);
        fb.store(Ty::I64, last_violating_state_ptr, dv_succ);
        fb.br(exit_invariant, vec![dv_steps, dv_succ]);

        // ---- check_visited: word/bit index, test-and-set, push frontier
        fb.switch_to_block(check_visited);
        // word_idx = succ >> 6   (i.e. succ / 64)
        let word_idx = fb.binop(BinOp::LShr, Ty::I64, cv_succ, k6_i64);
        let word_slot = fb.gep(Ty::I64, visited_ptr, vec![word_idx]);
        let bit_pos = fb.binop(BinOp::And, Ty::I64, cv_succ, k63_i64);
        let bit_mask = fb.binop(BinOp::Shl, Ty::I64, k1_i64, bit_pos);
        let word_val = fb.load(Ty::I64, word_slot);
        let test = fb.binop(BinOp::And, Ty::I64, word_val, bit_mask);
        let already_visited = fb.icmp(ICmpOp::Ne, Ty::I64, test, k0_i64);

        let do_push = fb.create_block();
        let dp_steps = fb.add_block_param(do_push, Ty::I64);
        let dp_idx = fb.add_block_param(do_push, Ty::I64);
        let dp_parent = fb.add_block_param(do_push, Ty::I64);
        let dp_succ = fb.add_block_param(do_push, Ty::I64);

        fb.condbr(
            already_visited,
            action_skip,
            vec![cv_steps, cv_idx, cv_parent],
            do_push,
            vec![cv_steps, cv_idx, cv_parent, cv_succ],
        );

        // ---- do_push: set visited bit, push to frontier -----------
        fb.switch_to_block(do_push);
        // Reload (the load+OR+store sequence below) just to be explicit; the
        // arena is single-threaded so we don't need atomic semantics.
        let word_idx2 = fb.binop(BinOp::LShr, Ty::I64, dp_succ, k6_i64);
        let word_slot2 = fb.gep(Ty::I64, visited_ptr, vec![word_idx2]);
        let word_val2 = fb.load(Ty::I64, word_slot2);
        let bit_pos2 = fb.binop(BinOp::And, Ty::I64, dp_succ, k63_i64);
        let bit_mask2 = fb.binop(BinOp::Shl, Ty::I64, k1_i64, bit_pos2);
        let word_set = fb.binop(BinOp::Or, Ty::I64, word_val2, bit_mask2);
        fb.store(Ty::I64, word_slot2, word_set);

        // Push the successor to the frontier and bump frontier_len.
        let cur_flen = fb.load(Ty::I64, frontier_len_ptr);
        let push_slot = fb.gep(Ty::I64, frontier_ptr, vec![cur_flen]);
        fb.store(Ty::I64, push_slot, dp_succ);
        let new_flen = fb.binop(BinOp::Add, Ty::I64, cur_flen, k1_i64);
        fb.store(Ty::I64, frontier_len_ptr, new_flen);

        // Advance to next action and loop back to action_header.
        let next_idx = fb.binop(BinOp::Add, Ty::I64, dp_idx, k1_i64);
        fb.br(action_header, vec![dp_steps, next_idx, dp_parent]);

        // ---- Exit blocks ------------------------------------------
        fb.switch_to_block(exit_continued);
        let xc_packed = pack_result(&mut fb, xc_steps, PARENT_LOOP_RESULT_CONTINUED, k32_i64);
        fb.ret(vec![xc_packed]);

        fb.switch_to_block(exit_frontier_empty);
        let xfe_packed = pack_result(
            &mut fb,
            xfe_steps,
            PARENT_LOOP_RESULT_FRONTIER_EMPTY,
            k32_i64,
        );
        fb.ret(vec![xfe_packed]);

        fb.switch_to_block(exit_invariant);
        let xv_packed = pack_result(
            &mut fb,
            xv_steps,
            PARENT_LOOP_RESULT_INVARIANT_VIOLATION,
            k32_i64,
        );
        // `xv_state` is captured into last_violating_state via the
        // do_violation block above; the exit block itself only emits the
        // packed status word. Silence the unused-warning by reading it via
        // a no-op pattern: the value is already stored, the param is just
        // a routing artifact for SSA dominance.
        let _ = xv_state;
        fb.ret(vec![xv_packed]);

        fb.build();
    }

    mb.build()
}

/// Pack `(steps << 32) | result` into the standard KernelEntry status word.
fn pack_result(
    fb: &mut FunctionBuilder<'_>,
    steps: ValueId,
    result_code: u32,
    k32_i64: ValueId,
) -> ValueId {
    let shifted = fb.binop(BinOp::Shl, Ty::I64, steps, k32_i64);
    let result_const = fb.iconst(Ty::I64, result_code as i128);
    fb.binop(BinOp::Or, Ty::I64, shifted, result_const)
}

// ---------------------------------------------------------------------
// Arena helper
// ---------------------------------------------------------------------

use crate::parent_loop_baseline::{Action, State, TransitionSystem};

/// Heap-pinned arena for the JIT'd parent-loop kernel.
///
/// Mirrors the layout documented at the top of this module. The arena owns
/// every backing allocation; `header` holds raw pointers/integers into those
/// allocations, and the JIT'd code does `gep` + `load` against those slots.
///
/// Visited-bitmap sizing: we allocate `2^num_vars / 64` u64 words, so the
/// bitmap directly indexes the full state space. This matches the native
/// baseline's `HashSet<State>` semantics exactly (no aliasing collisions).
/// Memory cost at num_vars=24 is 2 MiB; that is the maximum size used by the
/// existing native bench.
pub struct ParentLoopArena {
    pub header: Vec<u64>,
    pub actions: Vec<u64>,
    pub visited: Vec<u64>,
    pub frontier: Vec<u64>,
    pub frontier_len: Box<u64>,
    pub parent_count: Box<u64>,
    pub generated_count: Box<u64>,
    pub parent_digest: Box<u64>,
    pub fingerprint: Box<u64>,
    pub invariant_violations: Box<u64>,
    pub last_violating_state: Box<u64>,
    pub num_vars: u32,
    pub visited_word_count: u64,
}

impl ParentLoopArena {
    /// Build a fresh arena for `system`. `num_vars` must equal the width
    /// the transition system was constructed with — it determines the
    /// visited bitmap size. `frontier_capacity` is a host-side hint; the
    /// kernel does NOT bounds-check pushes, so callers must size this
    /// conservatively (`2^num_vars` is the loose upper bound; a much
    /// tighter bound is typically fine, e.g. `2^num_vars + 1`).
    pub fn build(num_vars: u32, system: &TransitionSystem, frontier_capacity: usize) -> Self {
        assert!(num_vars <= 26, "visited bitmap unsupported above 26 vars");
        let total_states = 1u64 << num_vars;
        let visited_word_count = total_states / 64;
        let visited_word_count = visited_word_count.max(1);

        // Flatten actions to a u64 array: [g_mask, g_value, s_mask, s_value]
        // per action.
        let mut actions = Vec::with_capacity(system.actions.len() * 4);
        for act in &system.actions {
            actions.push(act.guard_mask);
            actions.push(act.guard_value);
            actions.push(act.set_mask);
            actions.push(act.set_value);
        }
        let visited = vec![0u64; visited_word_count as usize];
        let frontier = vec![0u64; frontier_capacity.max(1)];
        let frontier_len = Box::new(0u64);
        let parent_count = Box::new(0u64);
        let generated_count = Box::new(0u64);
        let parent_digest = Box::new(0u64);
        let fingerprint = Box::new(0u64);
        let invariant_violations = Box::new(0u64);
        let last_violating_state = Box::new(0u64);

        let mut arena = ParentLoopArena {
            header: vec![0u64; 16],
            actions,
            visited,
            frontier,
            frontier_len,
            parent_count,
            generated_count,
            parent_digest,
            fingerprint,
            invariant_violations,
            last_violating_state,
            num_vars,
            visited_word_count,
        };

        arena.header[0] = num_vars as u64;
        arena.header[1] = system.actions.len() as u64;
        arena.header[2] = arena.actions.as_ptr() as u64;
        arena.header[3] = system.invariant_mask;
        arena.header[4] = system.invariant_value;
        arena.header[5] = visited_word_count;
        arena.header[6] = arena.visited.as_mut_ptr() as u64;
        arena.header[7] = arena.frontier.as_mut_ptr() as u64;
        arena.header[8] = arena.frontier.len() as u64;
        arena.header[9] = (&mut *arena.frontier_len) as *mut u64 as u64;
        arena.header[10] = (&mut *arena.parent_count) as *mut u64 as u64;
        arena.header[11] = (&mut *arena.generated_count) as *mut u64 as u64;
        arena.header[12] = (&mut *arena.parent_digest) as *mut u64 as u64;
        arena.header[13] = (&mut *arena.fingerprint) as *mut u64 as u64;
        arena.header[14] = (&mut *arena.invariant_violations) as *mut u64 as u64;
        arena.header[15] = (&mut *arena.last_violating_state) as *mut u64 as u64;

        arena.seed_initial_state(system.init);
        arena
    }

    fn seed_initial_state(&mut self, init: State) {
        // Visited starts with just `init`.
        for w in self.visited.iter_mut() {
            *w = 0;
        }
        let word_idx = (init.0 / 64) as usize;
        let bit = init.0 & 63;
        self.visited[word_idx] |= 1u64 << bit;

        // Frontier starts with [init].
        self.frontier[0] = init.0;
        *self.frontier_len = 1;
    }

    /// Reset every counter and the visited+frontier state to "freshly
    /// initialized for `system.init`". Intended for back-to-back bench
    /// iterations; preserves the action table and invariant config.
    pub fn reset(&mut self, init: State) {
        *self.frontier_len = 0;
        *self.parent_count = 0;
        *self.generated_count = 0;
        *self.parent_digest = 0;
        *self.fingerprint = 0;
        *self.invariant_violations = 0;
        *self.last_violating_state = 0;
        self.seed_initial_state(init);
    }

    pub fn header_ptr(&mut self) -> *mut u8 {
        self.header.as_mut_ptr() as *mut u8
    }

    pub fn header_byte_len(&self) -> usize {
        self.header.len() * 8
    }

    pub fn parent_count(&self) -> u64 {
        *self.parent_count
    }
    pub fn generated_count(&self) -> u64 {
        *self.generated_count
    }
    pub fn parent_digest(&self) -> u64 {
        *self.parent_digest
    }
    pub fn fingerprint(&self) -> u64 {
        *self.fingerprint
    }
    pub fn invariant_violations(&self) -> u64 {
        *self.invariant_violations
    }
    pub fn last_violating_state(&self) -> u64 {
        *self.last_violating_state
    }
    pub fn frontier_len(&self) -> u64 {
        *self.frontier_len
    }
    pub fn visited_contains(&self, state: u64) -> bool {
        let word_idx = (state / 64) as usize;
        let bit = state & 63;
        if word_idx >= self.visited.len() {
            return false;
        }
        (self.visited[word_idx] >> bit) & 1 != 0
    }

    /// Read-only view of the action table; one element corresponds to
    /// `(guard_mask, guard_value, set_mask, set_value)` flattened.
    pub fn actions_raw(&self) -> &[u64] {
        &self.actions
    }
}

// Force compile-time use of `Action` to silence dead-code warnings on
// non-test builds (the arena builder consumes `Action` through the
// `&TransitionSystem` reference, but rustc cannot see that through a
// helper.) — kept for documentation parity with the baseline.
#[allow(dead_code)]
fn _action_typecheck(a: Action) -> Action {
    a
}
