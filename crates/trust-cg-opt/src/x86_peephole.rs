// trust-cg-opt - x86-64 Peephole
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Conservative algebraic peepholes for x86-64 ISel-output functions.
//!
//! Includes algebraic identities, address folding, and instruction-sequence
//! rewrites. Flag-changing replacements require a proof that the affected
//! flags are dead or that the replacement preserves the consumed flags.

use trust_cg_ir::X86Opcode;
use trust_cg_ir::regs::{RegClass, VReg};
use trust_cg_lower::{X86ISelFunction, X86ISelInst, X86ISelOperand};

use crate::effects::{
    FlagOverwrite, condition_flag_overwrite, x86_inst_effect, x86_reads_flags, x86_writes_flags,
};
use crate::fast_hash::{FxHashMap, FxHashSet};
use crate::x86_flag_liveness::X86FlagLiveness;
use crate::x86_pass_manager::X86MachinePass;

/// Admission callback for the peepholes that CONSTRUCT a reconstruction-lane
/// opcode: the memory-destination RMW fusion (`rmw_fuse` — `XorMR`/`AddMR`/
/// `XorMRSib`/`AddMRSib`) and the variable-count rotate collapse
/// (`rotate_var_idiom` — `RolRCl`). `true` iff the candidate opcode's
/// representative reconstruction obligation is proof-covered on this build.
/// Injected by the constructor (trust-cg-opt must not depend on
/// trust-cg-verify — same callback-injection pattern as
/// `X86IfConvert`/`X86StrengthReduce`); the fail-closed default
/// ([`X86Peephole::default`]) admits NOTHING, so neither fusion ever fires
/// unless a caller explicitly wires the proof-backed admission.
pub type ReconstructionAdmit = fn(X86Opcode) -> bool;

/// Admission callback for the `IMUL r,r,imm` -> `SHL ; ADD/SUB` const-multiply
/// strength reduction. `true` iff the ALGEBRAIC identity
///
/// ```text
///   x * (2^a + 1) == (x << a) + x        (plus_one = true)
///   x * (2^a - 1) == (x << a) - x        (plus_one = false)
/// ```
///
/// at bit-width `width` is discharged on this build. Unlike
/// [`ReconstructionAdmit`] the opcodes involved (`ShlRI`/`AddRR`/`SubRR`) are
/// pre-existing emittable surface already verified per-instruction — what this
/// gate discharges is the RING IDENTITY the rewrite relies on, which the
/// AArch64 side proves as `proof_add_lsl_shift` / `proof_sub_lsl_shift`.
///
/// Injected by the constructor for the same reason as `ReconstructionAdmit`
/// (trust-cg-opt must not depend on trust-cg-verify), and the fail-closed
/// default ([`X86Peephole::default`], [`X86Peephole::new`]) admits NOTHING, so
/// the arm never fires unless a caller wires the proof-backed admission. A
/// `false` verdict leaves the original (correct, itself proof-covered) `IMUL`
/// in place: an admission gate, never a rejection gate.
pub type ConstMulShiftAdmit = fn(width: u32, a: u32, plus_one: bool) -> bool;

/// Bounded algebraic-identity peepholes for x86-64 ISel-output functions.
pub struct X86Peephole {
    /// Proof admission for opcode-constructing fusions. See
    /// [`ReconstructionAdmit`].
    admit_reconstructed: ReconstructionAdmit,
    /// Proof admission for the const-multiply shift reduction. See
    /// [`ConstMulShiftAdmit`].
    admit_constmul_shift: ConstMulShiftAdmit,
    /// Whether this compile keeps no proof certificates and its driver
    /// enabled the certificate-free IMUL reductions
    /// ([`Self::with_certificate_free_imul_reductions`]). `false` (every
    /// constructor's default) keeps the IMUL reductions exactly as they were
    /// before 2026-11-15: no doubling-LEA arm, and the flags scan stops at
    /// every store.
    certificate_free_imul: bool,
}

impl X86Peephole {
    /// Create the pass with the given reconstruction-proof admission callback.
    /// The const-multiply shift reduction stays FAIL-CLOSED; use
    /// [`Self::with_admissions`] to wire it.
    pub fn new(admit_reconstructed: ReconstructionAdmit) -> Self {
        Self {
            admit_reconstructed,
            admit_constmul_shift: |_, _, _| false,
            certificate_free_imul: false,
        }
    }

    /// Create the pass with BOTH proof admissions wired.
    pub fn with_admissions(
        admit_reconstructed: ReconstructionAdmit,
        admit_constmul_shift: ConstMulShiftAdmit,
    ) -> Self {
        Self {
            admit_reconstructed,
            admit_constmul_shift,
            certificate_free_imul: false,
        }
    }

    /// Enable (`true`) the two IMUL reductions a compile that keeps proof
    /// certificates withholds: the `ImulRRI d, s, 2` -> doubling `LEA` arm,
    /// and a flags scan for every `ImulRRI` reduction that lets a plain store
    /// pass ([`imul_flags_are_dead`]). Both change the emitted bytes and no
    /// compile with proof certificates has exercised them (the certificate
    /// lane does not run on the host that measured them), so the codegen
    /// pipeline passes `true` only in a certificate-free compile
    /// (`X86AllocationQuality::CertificateFree`, or an installed policy that
    /// enables them) and the default is `false`.
    #[must_use]
    pub fn with_certificate_free_imul_reductions(mut self, enabled: bool) -> Self {
        self.certificate_free_imul = enabled;
        self
    }

    /// Run x86 peepholes directly on an ISel function.
    pub fn run_on_function(&mut self, func: &mut X86ISelFunction) -> bool {
        run_impl(
            func,
            self.admit_reconstructed,
            self.admit_constmul_shift,
            self.certificate_free_imul,
        )
    }
}

impl Default for X86Peephole {
    /// The CLOSED admission: every peephole except the RMW fusion, the
    /// variable-rotate collapse and the const-multiply shift reduction runs
    /// unchanged; the admission-gated rewrites never fire (fail-closed on the
    /// proof).
    fn default() -> Self {
        Self {
            admit_reconstructed: |_| false,
            admit_constmul_shift: |_, _, _| false,
            certificate_free_imul: false,
        }
    }
}

impl X86MachinePass for X86Peephole {
    fn name(&self) -> &str {
        "x86-peephole"
    }

    fn run(&mut self, func: &mut X86ISelFunction) -> bool {
        run_impl(
            func,
            self.admit_reconstructed,
            self.admit_constmul_shift,
            self.certificate_free_imul,
        )
    }
}

enum PeepholeEdit {
    Remove,
    Replace(X86ISelInst),
    /// Replace one instruction with two (spliced in order at its position).
    ReplaceTwo(X86ISelInst, X86ISelInst),
}

static PEEPHOLE_ENTRY_TRACE: std::sync::OnceLock<bool> = std::sync::OnceLock::new();

/// Install the peephole-entry body dump from a TRACKED compiler option, once
/// (`-Ztrust-ir-cg-args=trace-peephole-entry`). DEFAULT OFF, diagnostics only, no
/// codegen effect.
///
/// # Why this exists
///
/// The x86 lane had dumps at exactly two pass positions, both owned by the
/// vectorizer: `vectorize-post-sroa` (after SROA, before LICM) and
/// `vectorize-late` (after the WHOLE cleanup cluster). There was nothing at the
/// peephole/BCE/DCE position.
///
/// That gap has a measured cost. Five separate transformations were designed in
/// this round against a `vectorize-late` dump and every one fired on NOTHING,
/// because that dump shows the body AFTER the peephole has already run, so the
/// shapes they matched do not exist where they execute. `p2_collatz`'s late dump
/// shows `ShrRI v26, v12, 1 ; MovRR v27, v26` with `v27` multi-def — a textbook
/// match for a producer/write-back coalesce — and such a fold declines, because at
/// THIS position that shape is not there.
///
/// So: before writing a transformation for a pass in the cleanup cluster, dump the
/// body as that pass sees it.
pub fn set_peephole_entry_trace_enabled(enabled: bool) -> bool {
    match PEEPHOLE_ENTRY_TRACE.set(enabled) {
        Ok(()) => true,
        Err(requested) => PEEPHOLE_ENTRY_TRACE.get() == Some(&requested),
    }
}

fn peephole_entry_trace_enabled() -> bool {
    if let Some(enabled) = PEEPHOLE_ENTRY_TRACE.get() {
        return *enabled;
    }
    crate::tcg_env_flag("TCG_X86_TRACE_PEEPHOLE_ENTRY")
}

fn run_impl(
    func: &mut X86ISelFunction,
    admit_reconstructed: ReconstructionAdmit,
    admit_constmul_shift: ConstMulShiftAdmit,
    certificate_free_imul: bool,
) -> bool {
    let mut changed = false;

    // Ground-truth dump of the body AS THIS PASS SEES IT. See
    // `set_peephole_entry_trace_enabled` for why this exists.
    if peephole_entry_trace_enabled() {
        eprintln!(
            "x86-peephole[entry]: fn `{}` blocks={}",
            func.name,
            func.block_order.len()
        );
        for block_id in &func.block_order {
            let Some(block) = func.blocks.get(block_id) else {
                continue;
            };
            eprintln!(
                "  block {:?} succs={:?}",
                block_id.0,
                block.successors.iter().map(|b| b.0).collect::<Vec<_>>()
            );
            for inst in &block.insts {
                eprintln!("    {:?} {:?}", inst.opcode, inst.operands);
            }
        }
    }

    // Function-scope pass: fold uniquely-defined `MovRI` constants into the
    // immediate slot of their ALU consumers. Runs before the fusion passes so
    // a `CmpRR a, const_vreg` collapsed to `CmpRI` is visible to them.
    if fold_unique_const_into_imm_forms(func) {
        changed = true;
    }

    // Multi-instruction pass: cmp+setcc+(zero-test)+Jcc fusion. Must run FIRST,
    // before any pass rewrites the `Setcc`/`Movzx`/`CmpRI %D,0`/`Jcc` shape
    // (and-pow2-bt and the single-inst loop rewrite the zero-test). Collapses a materialized-boolean branch back to a
    // direct conditional jump on the comparison's flags. See
    // `try_cmp_setcc_branch_fusion` for the hand-proof and side conditions.
    for block_id in func.block_order.clone() {
        if cmp_setcc_branch_fusion_run_on_block(func, block_id) {
            changed = true;
        }
    }

    // Multi-instruction pass: cmp+setcc+(normalize)+zero-test+Cmovcc fusion,
    // the select-side sibling of the branch fusion above, under the same
    // ordering constraint. Withheld unless an installed policy enables it
    // (`x86_select_flag_fusion`'s evidence boundary).
    if crate::x86_select_flag_fusion::x86_select_flag_fusion_enabled()
        && crate::x86_select_flag_fusion::select_flag_fusion_run(func)
    {
        changed = true;
    }

    // No pass here may separate a `Setcc %D, cc` from ISel's following
    // `Movzx %D, %D`. `Setcc` writes only %D[7:0], and every register model
    // (the allocator's `x86_operand_access`, `effects::x86_operand0_may_be_read`,
    // the post-RA dataflow check) treats it as a pure def of operand 0 that
    // does not read %D. A form that relies on %D[31:8] surviving the `Setcc`
    // (the retired setcc-flag-hoist: `XorRR %D,%D; [flag_writer]; Setcc %D`
    // with the Movzx deleted) is invisible to those models: the xor's value is
    // dead in liveness, and a spilled %D gets a fresh scratch with no reload,
    // so the stored bool carries stale bits 31:8. See the regression
    // `setcc_bool_survives_peephole_and_spill_materialization` (codegen).

    // Multi-instruction pass: shl/shr/or -> ROL. Flags liveness is computed ONCE
    // for the function; the rewrite is only legal where the OR's flags are dead.
    {
        let live_in = flags_live_in_by_block(func);
        for block_id in func.block_order.clone() {
            if rotate_idiom_run_on_block(func, block_id, &live_in) {
                changed = true;
            }
        }
    }

    // Multi-instruction pass: VARIABLE-count shl/shr/or expansion -> ROL
    // r64,CL (Stage 2 of the p6 variable-rotate arc, DEFAULT-ON;
    // `TCG_NO_X86_ROTATE_VAR_IDIOM` opts out). ADMISSION-GATED on the
    // injected reconstruction-proof callback exactly like the RMW fusion
    // below: `RolRCl` is never constructed unless its RotlVar reconstruction
    // obligation discharges Valid (fail-closed `|_| false` default). Flags
    // liveness is recomputed because the constant-rotate pass above may have
    // deleted flag-writing shifts. See `rotate_var_idiom_run_on_block` for
    // the hand-proof and side conditions.
    // The whole-function maps (single-def instruction index + function-wide
    // use/def counts) are a pure function of `func`, and this routine mutates
    // `func` ONLY when it returns `true`, so ONE build serves every block up
    // to the next collapse — instead of one build per block, which made this
    // loop O(blocks x instructions). Rebuilding immediately after any
    // collapse hands each block exactly the maps a per-block build would have
    // produced, so the emitted bytes are unchanged. (Same restructuring as
    // `SibFoldVRegMaps` above; `function_use_def_counts` was 8.4% of the whole
    // x86 optimization phase at 2400 functions, measured 2026-08-31.)
    //
    // The maps are also built LAZILY: the routine can only rewrite at an
    // `OrRR` anchor, and on a block without one it returns `false` having
    // read nothing, so such a block needs no maps. A build is made at the
    // first block that has an anchor and again at the first anchor block
    // after each collapse, so every block that reads the maps reads exactly
    // the maps of the current `func`. Which blocks the filter admits is
    // pinned by `peephole_lazy_fn_maps_still_reach_every_anchor_block`; that
    // a rewrite drops the maps is checked in test and debug builds against a
    // fresh build before every reuse, and pinned by
    // `peephole_lazy_fn_facts_are_rebuilt_after_each_rewrite`.
    if rotate_var_idiom_enabled() {
        let live_in = flags_live_in_by_block(func);
        let mut maps: Option<RotateVarFnMaps> = None;
        for block_id in func.block_order.clone() {
            if !block_has_opcode(func, block_id, X86Opcode::OrRR) {
                continue;
            }
            let current = maps.get_or_insert_with(|| RotateVarFnMaps::build(func));
            // A reused build must be the build of the current `func`: test and
            // debug builds compare it with a fresh one, so a rewrite that
            // stops dropping the maps fails there.
            #[cfg(any(test, debug_assertions))]
            assert_eq!(
                current.canonical_view(),
                RotateVarFnMaps::build(func).canonical_view(),
                "rotate-var maps are stale at block {block_id:?}"
            );
            if rotate_var_idiom_run_on_block_with_maps(
                func,
                block_id,
                &live_in,
                admit_reconstructed,
                current,
            ) {
                changed = true;
                maps = None;
            }
        }
    }

    // Multi-instruction pass: AND-power-of-2 + CMP-zero + Jcc -> BT + Jcc.
    // Must run before the single-instruction simplification loop because that
    // loop rewrites `CmpRI %dst, 0` to `TestRR %dst, %dst`, breaking the
    // pattern shape we look for. See `try_and_pow2_bt_branch` for the
    // hand-proof and side conditions.
    for block_id in func.block_order.clone() {
        if and_pow2_bt_branch_run_on_block(func, block_id) {
            changed = true;
        }
    }

    // Multi-instruction pass: fold a scaled-index address computation
    // (`imul index,{1,2,4,8}` or `shl index,{0..3}` then `add base,scaled`)
    // into the SIB memory operand of the subsequent 64-bit load/store. This
    // is the x86 base+index*scale addressing-mode fold (OPT-7 / LEVER 1). It
    // must run before the single-instruction loop, which could otherwise
    // rewrite the imul/shl/add shape (e.g. imm folding) and break the window.
    // See `try_sib_addr_fold` for the full hand-proof and side conditions.
    // The whole-function VReg maps are a pure function of `func`, and a block
    // that folds nothing leaves `func` untouched, so ONE build serves every
    // block up to the next fold — instead of one build per block, which made
    // this loop O(blocks x instructions) (10.8% of the whole x86 optimization
    // phase at 2400 functions, measured 2026-08-31). Rebuilding immediately
    // after any fold hands each block exactly the maps a per-block build would
    // have produced, so the emitted bytes are unchanged.
    //
    // The rebuild after a fold is INCREMENTAL: a fold edits only its own
    // block, and every map is a sum (counts) or a union (mentioning blocks)
    // of per-block parts, so taking the block's part out before the fold and
    // putting its new part in after yields the maps a whole-function build of
    // the edited function produces (`sib_fold_maps_refresh_matches_rebuild`
    // pins it). A block is measured before every fold attempt; the whole
    // function is no longer re-scanned once per fold.
    {
        let mut maps = SibFoldVRegMaps::build(func);
        for block_id in func.block_order.clone() {
            // Every anchor is a `LeaSib` or an `AddRR`; a block with neither
            // folds nothing, so it needs no part measured.
            if !block_has_opcode(func, block_id, X86Opcode::LeaSib)
                && !block_has_opcode(func, block_id, X86Opcode::AddRR)
            {
                continue;
            }
            let before = SibFoldBlockPart::of(func, block_id);
            if sib_addr_fold_run_on_block_with_maps(func, block_id, &maps) {
                changed = true;
                maps.replace_block_part(block_id, &before, &SibFoldBlockPart::of(func, block_id));
                // The refresh is exact only while a fold edits nothing outside
                // its own block. Test and debug builds check that against a
                // whole-function rebuild after every fold, so a fold that
                // starts touching another block fails there instead of
                // leaving stale counts or escape sets for the next block.
                #[cfg(any(test, debug_assertions))]
                assert_eq!(
                    maps.canonical_view(),
                    SibFoldVRegMaps::build(func).canonical_view(),
                    "SIB fold edited outside block {block_id:?}: incremental map refresh is stale"
                );
            }
        }
    }

    // Same fold, the anchor the loop above does not have: a memory op that
    // ALREADY carries a SIB operand with `scale == 1` whose index is a
    // power-of-two `imul`/`shl`. A frontend that lowers an element address as an
    // explicit stride multiply and lets the SIB do the base addition emits
    // neither a `LeaSib` nor an `AddRR`, so the multiply survived into the hot
    // loop. The rewrite is an exact equality (both the `imul` and SIB scaling are
    // modulo 2^64), so it carries no overflow side condition. DEFAULT-ON;
    // `TCG_NO_X86_SIB_SCALE1_FOLD` is the forensic opt-out. See
    // `sib_scale1_index_fold_run_on_block` for the side conditions.
    //
    // The counts and the flag liveness are built only for a block that holds
    // a candidate multiply ([`block_has_sib_scale_candidate`]): on any other
    // block the fold returns `false` having read neither. They are rebuilt
    // at the next candidate block after a fold, exactly as the eager rebuild
    // after every fold would give that block.
    if sib_scale1_index_fold_enabled() {
        let mut facts: Option<(FnUseDefCounts, X86FlagLiveness)> = None;
        for block_id in func.block_order.clone() {
            if !block_has_sib_scale_candidate(func, block_id) {
                continue;
            }
            let (counts, flags) = facts.get_or_insert_with(|| {
                (FnUseDefCounts::build(func), X86FlagLiveness::analyze(func))
            });
            // As for the rotate-var maps: a reused build must equal a fresh one.
            #[cfg(any(test, debug_assertions))]
            {
                assert_eq!(
                    counts.canonical_view(),
                    FnUseDefCounts::build(func).canonical_view(),
                    "SIB scale-1 use/def counts are stale at block {block_id:?}"
                );
                assert_eq!(
                    flags.canonical_view(),
                    X86FlagLiveness::analyze(func).canonical_view(),
                    "SIB scale-1 flag liveness is stale at block {block_id:?}"
                );
            }
            if sib_scale1_index_fold_run_on_block(func, block_id, counts, flags) {
                changed = true;
                facts = None;
            }
        }
    }

    // Multi-instruction pass: a SIB memory operand whose INDEX register holds
    // a block-local compile-time constant becomes `[base + disp]`. This is the
    // machine-level form of an element address at a literal index
    // (`Iconst k; Iconst size; Imul; ArrayGep`), which the selector emits as a
    // scaled-index address over a materialized constant and the SIB fold above
    // carries into the load or store. It runs here, on the optimizer's stream,
    // so the selector's own rows for `ArrayGep` are untouched. Rewrite-only:
    // DCE sweeps the constant's computation. Before the address-chain fold so
    // that fold sees the plain `[base + disp]` operand. See
    // `sib_const_index_fold_run_on_block` for the side conditions.
    for block_id in func.block_order.clone() {
        if sib_const_index_fold_run_on_block(func, block_id) {
            changed = true;
        }
    }

    // Multi-instruction pass: LOCAL address-chain fold (X9 slice 2).
    // Generalizes the SIB fold above to the post-unroll dialect (multi-def vreg
    // ids from verbatim clones, AddRI displacement chains, scale-1 AddRR
    // indices) via local nearest-reaching-def resolution. Rewrite-only: the dead
    // chains are swept by DCE. See `addr_chain_fold_run_on_block` for the
    // hand-proof.
    for block_id in func.block_order.clone() {
        if addr_chain_fold_run_on_block(func, block_id) {
            changed = true;
        }
    }

    // Multi-instruction pass: RM fusion (X9 slice 3). Folds a locally-dead 64-bit load into the
    // multiply that is its only consumer (`ImulRM`/`ImulRMSib`). Runs after
    // the addr-chain fold so SIB-formed loads are already in their final
    // shape. See `imul_fuse_run_on_block` for the hand-proof.
    for block_id in func.block_order.clone() {
        if imul_fuse_run_on_block(func, block_id) {
            changed = true;
        }
    }

    // Multi-instruction pass: memory-destination RMW fusion (Stage 2 of the
    // b1 RMW arc, DEFAULT-ON; `TCG_NO_X86_RMW_FUSE` opts out). Folds a
    // load / commutative-ALU / same-address store triple into the single
    // memory-destination ALU (`XorMR*`/`AddMR*`). ADMISSION-GATED on the
    // injected proof callback (fail-closed `|_| false` default): a fused
    // opcode is only ever created when the caller certifies its
    // reconstruction obligation discharges Valid. Runs after imul_fuse so
    // the two RM/MR families never race for one load, and after the
    // addr-chain fold so SIB shapes are final. See `rmw_fuse_run_on_block`
    // for the hand-proof.
    // Same hoist as the rotate-var loop above: the whole-function maps are a
    // pure function of `func` and `rmw_fuse_run_on_block_with_maps` mutates
    // `func` only when it returns `true`, so one build serves every block up
    // to the next fusion and is rebuilt the instant one fires — handing each
    // block exactly the maps a per-block build would have produced.
    // Built lazily as above: an anchor is an `XorRR` or `AddRR`, and a block
    // with neither returns `false` without reading the maps or tracing.
    if rmw_fuse_enabled() {
        let mut maps: Option<RmwFuseFnMaps> = None;
        for block_id in func.block_order.clone() {
            if !block_has_opcode(func, block_id, X86Opcode::XorRR)
                && !block_has_opcode(func, block_id, X86Opcode::AddRR)
            {
                continue;
            }
            let current = maps.get_or_insert_with(|| RmwFuseFnMaps::build(func));
            // As for the rotate-var maps: a reused build must equal a fresh one.
            #[cfg(any(test, debug_assertions))]
            assert_eq!(
                current.canonical_view(),
                RmwFuseFnMaps::build(func).canonical_view(),
                "RMW-fuse maps are stale at block {block_id:?}"
            );
            if rmw_fuse_run_on_block_with_maps(
                func,
                block_id,
                admit_reconstructed,
                current,
                rmw_fuse_sdef_enabled(),
            ) {
                changed = true;
                maps = None;
            }
        }
    }

    // Whole-function VReg use/def counts, SHARED by the four passes below
    // (latch-advance collapse, LEA-displacement fold, commute normalization,
    // SIB-base LEA fold). Each used to build its own private copy at its own
    // entry, and `function_use_def_counts` is an O(instructions x operands)
    // hashing scan: measured 2026-08-31 at 2400 functions, whole-function map
    // building was the largest single item inside this pass, which is itself
    // ~32% of x86_optimization.
    //
    // The sharing is EXACT, not approximate. `function_use_def_counts` is a
    // pure function of `func`; each routine below reports mutation precisely by
    // returning `true`; and the cache is cleared the moment one does. So every
    // consumer still sees counts frozen at ITS OWN entry — which is what their
    // side conditions are proved against (see
    // `latch_advance_collapse_run_on_block`: "windows are matched against
    // counts frozen at pass entry"). The rebuild is skipped only when `func` is
    // provably the identical function the cached counts describe, so the edit
    // sets, and therefore the emitted bytes, are unchanged.
    //
    // DISCIPLINE: a cached copy must never outlive an IR mutation. Anything
    // added between here and the `drop` below that can rewrite `func` MUST
    // clear `fn_counts` (the `drop` makes a later reader a compile error, not a
    // silent stale read).
    let mut fn_counts: Option<FnUseDefCounts> = None;

    // Multi-instruction pass: latch-advance collapse. The frontend's counted-loop latch
    // `AddRI n,c,k ; MovRR c,n ; Cmp{RI,RR} n,… ; Jcc` advances through a
    // fresh vreg `n`, which regalloc must place in a SECOND register and the
    // AddRI->LEA bridge then spells as `lea k(c),n ; mov n,c ; cmp n,…` — two
    // instructions and one register more than LLVM's `add k,c ; cmp c,…`.
    // When `n` has no other def or use, advancing IN PLACE is
    // value-identical: the compare reads the same advanced value through `c`,
    // and the flag schedule is unchanged (AddRI wrote flags at the same
    // position before; the compare overwrites them before the Jcc either
    // way). Measured (hand-asm ablation, 2026-08-28): p1 latch -10.3%,
    // exact-parity with LLVM together with the commute pass below.
    let counts: &FnUseDefCounts = fn_counts.get_or_insert_with(|| FnUseDefCounts::build(func));
    let mut fired = false;
    for block_id in func.block_order.clone() {
        if latch_advance_collapse_run_on_block(
            func,
            block_id,
            &counts.uses,
            &counts.defs,
            latch_advance_window_enabled(),
        ) {
            fired = true;
        }
    }
    if fired {
        changed = true;
        fn_counts = None; // `func` mutated: the cached counts are stale.
    }

    // Two-address increment collapse: `Lea tmp,[base+disp] ; MovRR base,tmp` ->
    // `AddRI base,base,disp`, wherever the flags are dead from the `lea` onward
    // (`Lea` writes none, `AddRI` writes all — that condition IS the argument).
    // The expansion exists because its emitter could not know the flags were
    // dead; this pass can. DEFAULT-ON; `TCG_NO_X86_LEA_WRITEBACK` opts out.
    if lea_writeback_collapse_enabled() {
        let counts: &FnUseDefCounts = fn_counts.get_or_insert_with(|| FnUseDefCounts::build(func));
        let mut fired = false;
        for block_id in func.block_order.clone() {
            if lea_writeback_collapse_run_on_block(func, block_id, counts) {
                fired = true;
            }
        }
        if fired {
            changed = true;
            fn_counts = None; // `func` mutated: the cached counts are stale.
        }
    }

    // Multi-instruction pass: LEA displacement fold. `LeaSib t,[b+i*s+d] ; AddRI x,t,k`
    // with `t` living only in this window folds to `LeaSib x,[b+i*s+(d+k)]` —
    // the p2_collatz `lea (%rcx,%rcx,2) ; add $1` chain becomes LLVM's single
    // `lea 1(%rcx,%rcx,2)`. Legal when the AddRI's flags are provably dead
    // (LEA writes none) and the folded displacement stays in i32.
    let counts: &FnUseDefCounts = fn_counts.get_or_insert_with(|| FnUseDefCounts::build(func));
    let mut fired = false;
    for block_id in func.block_order.clone() {
        if lea_disp_fold_run_on_block(func, block_id, &counts.uses, &counts.defs) {
            fired = true;
        }
    }
    if fired {
        changed = true;
        fn_counts = None; // `func` mutated: the cached counts are stale.
    }

    // Single-instruction pass: commutative dying-source-first normalization
    // (OPT-IN `TCG_X86_COMMUTE_DST` — REFUTED as a default, see
    // `commute_dying_source_enabled`). For a commutative
    // 3-operand ALU op `Op d, s1, s2`, two-address fixup ties d to s1 —
    // copying s1. When s1 outlives the op but s2 DIES here, that copy is a
    // real extra instruction (the xorshift `x ^= t` bodies pay 3 of them per
    // round); swapping to `Op d, s2, s1` lets the tie copy the dying value,
    // which regalloc coalesces away. Wrapping add/mul and the bitwise ops are
    // fully commutative including their flag results, so the swap is
    // semantics- and proof-neutral (reconstruction re-checks the operand
    // wiring). Precedent: the saxpyq ImulRR operand swap (3ea43e17).
    if commute_dying_source_enabled() {
        let counts: &FnUseDefCounts = fn_counts.get_or_insert_with(|| FnUseDefCounts::build(func));
        let mut fired = false;
        for block_id in func.block_order.clone() {
            if commute_dying_source_run_on_block(func, block_id, &counts.uses, &counts.defs) {
                fired = true;
            }
        }
        if fired {
            changed = true;
            fn_counts = None; // `func` mutated: the cached counts are stale.
        }
    }

    // SIB-base LEA fold (measured evidence in the comment above
    // `sib_base_lea_fold`): fold each
    // stack-slot base-`Lea` into its already-formed indexed SIB memory operand,
    // killing the redundant per-access `leaq -N(%rbp)`. See
    // `sib_base_lea_fold`. NOTE: this
    // runs in the mid-pipeline peephole (before cmov-swap), so on a swap-diamond
    // bench (b06) it changes the store addressing enough that cmov-swap's
    // recognizer no longer matches -> b06 keeps the fold's addressing but loses
    // cmov-swap (a b06-specific TRADE — the fold helps b07/b18/b05 which have no
    // cmov-swap diamond). Scheduling it LATE (after cmov-swap) was tried and
    // REVERTED: the pass-manager fixpoint then converges to a state where the
    // fold never fires whenever cmov-swap is scheduled, making it a no-op.
    //
    // Takes the shared whole-function counts: `def_count`/`use_count` are the
    // only maps it consults, so it no longer builds a private
    // `SibFoldVRegMaps` whose `mention_blocks` half it never queried.
    let counts: &FnUseDefCounts = fn_counts.get_or_insert_with(|| FnUseDefCounts::build(func));
    if sib_base_lea_fold(func, counts) {
        changed = true;
    }
    // Last consumer of the shared counts. Moving the cache out here retires it
    // by construction: this fold may have rewritten `func`, and any future
    // reader added below would now fail to compile (use after move) instead of
    // silently reading counts that no longer describe the IR.
    drop(fn_counts);

    // Multi-instruction pass: redundant self-zero-test elision (task #72
    // pass 2). `test v,v` / `cmp v,0` whose ZF is already established by the
    // nearest preceding ALU def of `v` is deleted when every downstream flag
    // reader in the block needs only ZF (E/NE). OPT-IN via
    // `TCG_X86_TEST_ELIDE` for the staged rollout. See
    // `redundant_self_test_elision_run_on_block` for the side conditions.
    if test_elide_enabled() {
        for block_id in func.block_order.clone() {
            if redundant_self_test_elision_run_on_block(func, block_id) {
                changed = true;
            }
        }
    }

    // Zero-idiom gate: compute the function-wide use set once so the MovRI-0 -> XorRR rewrite
    // can DECLINE on never-read destinations. Rationale: `XorRR d, d` puts d
    // in a formal USE position, which makes the (per-vreg, function-wide)
    // DCE use-set consider every def of that id live — in a post-unroll body
    // the 24 cloned MovRI-0 defs then survive to regalloc and get spilled as
    // store pairs. Leaving an unread zero as MovRI keeps it in DCE's
    // removable set. Declining a rewrite is a semantic no-op, so both error
    // directions of this predicate reduce to the status quo.
    let zeroidiom_used = peephole_function_use_set(func);

    for block_id in func.block_order.clone() {
        let Some(block) = func.blocks.get_mut(&block_id) else {
            continue;
        };

        let mut index = 0;
        while index < block.insts.len() {
            match simplify_inst_gated(
                &block.insts,
                index,
                Some(&zeroidiom_used),
                admit_constmul_shift,
                certificate_free_imul,
            ) {
                Some(PeepholeEdit::Remove) => {
                    block.insts.remove(index);
                    changed = true;
                }
                Some(PeepholeEdit::Replace(mut inst)) => {
                    if inst.proof_origin.is_none() {
                        inst.proof_origin = block.insts[index].proof_origin;
                    }
                    block.insts[index] = inst;
                    changed = true;
                    index += 1;
                }
                Some(PeepholeEdit::ReplaceTwo(mut a, mut b)) => {
                    let origin = block.insts[index].proof_origin;
                    if a.proof_origin.is_none() {
                        a.proof_origin = origin;
                    }
                    if b.proof_origin.is_none() {
                        b.proof_origin = origin;
                    }
                    block.insts[index] = a;
                    block.insts.insert(index + 1, b);
                    changed = true;
                    index += 2;
                }
                None => index += 1,
            }
        }
    }

    changed
}

// ---------------------------------------------------------------------------
// Cmp + Setcc + (zero-test) + Jcc  ->  Cmp + Jcc  (branch fusion)
// ---------------------------------------------------------------------------
//
// trust_ir lowers `if a <cc> b { .. }` as two separate instructions: an Icmp
// that materializes a boolean (`Cmp a,b; Setcc %D,cc; Movzx %D,%D`), then a
// CondBr that re-tests the boolean (`Cmp %D,0; Jcc NE`). When the Icmp result
// is consumed only by the branch, the boolean round-trip is pure overhead.
// This window collapses it back to a direct `Cmp a,b; Jcc cc`, the form a
// hand-written assembler (and LLVM) would emit. In a tight loop header this
// removes a `Setcc`, a `Movzx`, and the redundant zero-test from every
// iteration.
//
// Pattern (before), all within one basic block:
//   [c]   <flag_writer>            ; CmpRR/CmpRI/CmpRI8/TestRR/... full RFLAGS
//   [c+1] Setcc %D, cc             ; %D[7:0] = cc-holds ? 1 : 0
//   [c+2] Movzx %D, %D             ; zero-extend (canonical ISel pair)
//   [z]   CmpRI %D, 0 | TestRR %D, %D   ; zero-test re-deriving (%D != 0)
//   [z+1] Jcc {NE | E}, target
//
// Pattern (after):
//   [c]   <flag_writer>
//   [z+1] Jcc { cc        if orig was NE (branch-when-true)
//             | cc.invert  if orig was E  (branch-when-false) }, target
//   (Setcc, Movzx, and the zero-test are erased.)
//
// HAND-PROOF (semantic equivalence):
//   - flag_writer sets RFLAGS to the comparison result of `a <cc'> b` (cc is the
//     condition code Setcc reads from those flags).
//   - Setcc %D = (cc satisfied by flag_writer's RFLAGS) ? 1 : 0; Movzx makes %D
//     exactly 0 or 1.
//   - The zero-test recomputes flags so that (%D != 0) <=> ZF==0 <=> cc was
//     satisfied. So the original `Jcc NE` branches exactly when cc holds, and
//     `Jcc E` branches exactly when cc does NOT hold.
//   - In the rewritten form, the SAME flag_writer RFLAGS are consumed directly
//     by the new Jcc: `Jcc cc` branches when cc holds; `Jcc cc.invert()`
//     branches when cc does not hold. These are pointwise identical to the
//     original branch outcomes.
//   - Erasing Setcc/Movzx/zero-test is observationally invisible because (see
//     side conditions) %D is dead after the branch and nothing else reads it,
//     and none of the erased instructions has a side effect beyond producing
//     %D / RFLAGS (which we either keep, via flag_writer, or no longer need).
//
// SIDE CONDITIONS (each must hold or the rewrite is unsound):
//   1. flag_writer fully overwrites RFLAGS (`condition_flag_overwrite == Full`)
//      and is a pure flag producer (not call/branch/terminator/return, no
//      memory side effects, not pseudo). This is what guarantees the new Jcc
//      reads exactly flag_writer's result.
//   2. Setcc immediately follows flag_writer; Movzx immediately follows Setcc;
//      they form the canonical pair `Setcc %D,cc` / `Movzx %D,%D` with %D a
//      Gpr32 vreg and both at their opcode default flags.
//   3. The condition code Setcc reads is one of the standard comparison codes
//      (B/AE/BE/A/E/NE/L/GE/LE/G). Both `cc` and `cc.invert()` are then valid
//      Jcc conditions over the flags flag_writer wrote.
//   4. Between the Movzx and the zero-test, NO instruction writes RFLAGS and NO
//      instruction reads RFLAGS. (No flag write keeps flag_writer's RFLAGS live
//      for the new Jcc; no flag read means we are not stealing flags some other
//      consumer depended on.)  No instruction in that range may write %D either
//      (it must still equal the Setcc/Movzx result at the zero-test — though in
//      practice, with the single-use guard below, nothing touches %D there).
//   5. The zero-test is `CmpRI %D, 0` or `TestRR %D, %D` (reading %D), at
//      opcode-default flags with no memory side effects, immediately followed
//      by `Jcc {E | NE}, target`.
//   6. %D is single-use across the whole function: its only uses are the Movzx
//      source and the zero-test. Concretely: total in-block uses == 2 (one
//      Movzx src + one zero-test operand; TestRR mentions %D twice so == 3 in
//      that case), %D is defined only by the Setcc here, and %D is not
//      mentioned in any other block (no live-out). This makes erasing the
//      boolean invisible.
//
// PROOF PROVENANCE: hand-proved peephole (CEGIS is not yet wired to x86). The
// new Jcc inherits `proof_origin` from the original Jcc so source-location
// reporting still points at the trust_ir CondBr.

fn cmp_setcc_branch_fusion_run_on_block(
    func: &mut X86ISelFunction,
    block_id: trust_cg_lower::instructions::Block,
) -> bool {
    let Some(block) = func.blocks.get(&block_id) else {
        return false;
    };
    let insts = &block.insts;

    let mut edits: Vec<CmpSetccBranchEdit> = Vec::new();
    let mut i = 0;
    while i + 2 < insts.len() {
        if let Some(edit) = try_cmp_setcc_branch_fusion(insts, i) {
            // Cross-block liveness guard: %D must not be read in any other
            // block (no live-out). We are erasing its only definition.
            let setcc_dst = edit.setcc_dst;
            let mut escapes = false;
            for (other_id, other_block) in &func.blocks {
                if *other_id == block_id {
                    continue;
                }
                if other_block
                    .insts
                    .iter()
                    .any(|inst| instruction_mentions_vreg(inst, setcc_dst))
                {
                    escapes = true;
                    break;
                }
            }
            if escapes {
                i += 1;
                continue;
            }
            // Advance past the Jcc so we do not re-scan inside the window.
            i = edit.jcc_idx + 1;
            edits.push(edit);
        } else {
            i += 1;
        }
    }

    if edits.is_empty() {
        return false;
    }

    let block = func.blocks.get_mut(&block_id).expect("block existed above");
    // Apply edits in reverse order so earlier indices remain valid.
    for edit in edits.into_iter().rev() {
        let jcc_inst = block.insts[edit.jcc_idx].clone();
        let mut new_jcc = X86ISelInst::new(
            X86Opcode::Jcc,
            vec![
                X86ISelOperand::CondCode(edit.new_cc),
                X86ISelOperand::Block(edit.target),
            ],
        );
        new_jcc.proof_origin = jcc_inst.proof_origin;

        // Erase every instruction strictly after flag_writer up to and including
        // the Jcc. The window `(flag_writer, jcc]` is exactly the dead boolean
        // plumbing (Setcc, Movzx, the optional normalize Movzx/AndRI, the
        // zero-test, and the old Jcc) verified by `try_cmp_setcc_branch_fusion`.
        // Then insert the direct conditional jump right after flag_writer.
        debug_assert!(edit.flag_writer_idx < edit.jcc_idx);
        for idx in (edit.flag_writer_idx + 1..=edit.jcc_idx).rev() {
            block.insts.remove(idx);
        }
        block.insts.insert(edit.flag_writer_idx + 1, new_jcc);
    }

    true
}

#[derive(Debug)]
struct CmpSetccBranchEdit {
    flag_writer_idx: usize,
    jcc_idx: usize,
    setcc_dst: VReg,
    new_cc: trust_cg_ir::X86CondCode,
    target: trust_cg_lower::instructions::Block,
}

fn try_cmp_setcc_branch_fusion(
    insts: &[X86ISelInst],
    flag_writer_idx: usize,
) -> Option<CmpSetccBranchEdit> {
    use trust_cg_ir::X86CondCode;

    // Side condition 1: flag_writer fully overwrites RFLAGS and is a pure flag
    // producer.
    let flag_writer = insts.get(flag_writer_idx)?;
    if !x86_writes_flags(flag_writer.opcode) {
        return None;
    }
    if condition_flag_overwrite(flag_writer) != FlagOverwrite::Full {
        return None;
    }
    let fw_flags = flag_writer.flags;
    if fw_flags.is_call()
        || fw_flags.is_branch()
        || fw_flags.is_terminator()
        || fw_flags.is_return()
        || fw_flags.reads_memory()
        || fw_flags.writes_memory()
        || fw_flags.is_pseudo()
    {
        return None;
    }

    // Side condition 2: canonical `Setcc %D, cc` / `Movzx %D, %D` pair directly
    // after flag_writer.
    let setcc_idx = flag_writer_idx + 1;
    let setcc = insts.get(setcc_idx)?;
    if setcc.opcode != X86Opcode::Setcc {
        return None;
    }
    if setcc.flags != X86Opcode::Setcc.default_flags() {
        return None;
    }
    let (setcc_dst, setcc_cc) = match setcc.operands.as_slice() {
        [X86ISelOperand::VReg(dst), X86ISelOperand::CondCode(cc)] => (*dst, *cc),
        _ => return None,
    };
    if setcc_dst.class != RegClass::Gpr32 {
        return None;
    }
    // flag_writer must not mention %D (it writes flags, not the boolean).
    if instruction_mentions_vreg(flag_writer, setcc_dst) {
        return None;
    }

    let movzx_idx = setcc_idx + 1;
    let movzx = insts.get(movzx_idx)?;
    if movzx.opcode != X86Opcode::Movzx {
        return None;
    }
    if movzx.flags != X86Opcode::Movzx.default_flags() {
        return None;
    }
    match movzx.operands.as_slice() {
        [X86ISelOperand::VReg(mdst), X86ISelOperand::VReg(msrc)]
            if *mdst == setcc_dst && *msrc == setcc_dst => {}
        _ => return None,
    }

    // Side condition 3: standard comparison condition code, so cc and its
    // inverse are both valid Jcc predicates over flag_writer's RFLAGS.
    if !is_standard_compare_cc(setcc_cc) {
        return None;
    }

    // After Setcc+Movzx, %D holds exactly 0 or 1. The CondBr lowering then runs
    // `emit_condition_zero_test`, which (for a B1 condition) normalizes %D via
    //   Movzx %D2, %D ; AndRI %D2, %D2, 1
    // before testing it. We OPTIONALLY consume that normalize pair, tracking the
    // value that the zero-test will read (`tail`). Because %D is 0/1, the
    // re-extend and bit-0 mask are value-preserving, so collapsing them is
    // sound. We collect every intermediate vreg so the single-use / liveness
    // checks below cover the whole chain.
    let mut chain_vregs: Vec<VReg> = vec![setcc_dst];
    let mut tail = setcc_dst;
    let mut idx = movzx_idx + 1;

    // Optional normalize Movzx: `Movzx %D2, %tail` where %D2 is a fresh dst.
    if let Some(nz) = insts.get(idx)
        && nz.opcode == X86Opcode::Movzx
        && nz.flags == X86Opcode::Movzx.default_flags()
        && let [X86ISelOperand::VReg(ndst), X86ISelOperand::VReg(nsrc)] = nz.operands.as_slice()
        && *nsrc == tail
        && *ndst != tail
    {
        let ndst = *ndst;
        // Optional normalize mask: `AndRI %D2, %D2, 1`.
        if let Some(am) = insts.get(idx + 1)
            && am.opcode == X86Opcode::AndRI
            && am.flags == X86Opcode::AndRI.default_flags()
            && let [
                X86ISelOperand::VReg(adst),
                X86ISelOperand::VReg(asrc),
                X86ISelOperand::Imm(1),
            ] = am.operands.as_slice()
            && *adst == ndst
            && *asrc == ndst
        {
            chain_vregs.push(ndst);
            tail = ndst;
            idx += 2;
        }
    }

    // Side condition 5: the zero-test reads `tail` and is at default flags with
    // no memory effects.
    let zero_test_idx = idx;
    let zero_test = insts.get(zero_test_idx)?;
    if !is_zero_test_of(zero_test, tail) {
        return None;
    }
    if zero_test.flags != zero_test.opcode.default_flags() {
        return None;
    }
    if zero_test.flags.reads_memory()
        || zero_test.flags.writes_memory()
        || zero_test.flags.is_pseudo()
    {
        return None;
    }

    // Jcc {E|NE} must immediately follow the zero-test.
    let jcc_idx = zero_test_idx + 1;
    let jcc = insts.get(jcc_idx)?;
    if jcc.opcode != X86Opcode::Jcc {
        return None;
    }
    if jcc.flags != X86Opcode::Jcc.default_flags() {
        return None;
    }
    let (orig_cc, target) = match jcc.operands.as_slice() {
        [X86ISelOperand::CondCode(cc), X86ISelOperand::Block(blk)] => (*cc, *blk),
        _ => return None,
    };
    let new_cc = match orig_cc {
        // Branch-when-(tail != 0) == branch-when-cc-holds  -> Jcc cc.
        X86CondCode::NE => setcc_cc,
        // Branch-when-(tail == 0) == branch-when-cc-fails  -> Jcc cc.invert().
        X86CondCode::E => setcc_cc.invert(),
        _ => return None,
    };

    // Side condition 6: every value in the boolean chain is single-use and dead
    // after the Jcc. We require the total number of uses of each chain vreg in
    // the block to exactly equal the number of times it appears as a source in
    // the window (Movzx %D,%D contributes 1; normalize Movzx + AndRI consume the
    // prior value once and %D2 twice (AndRI src + zero-test) or per-shape). The
    // simplest exact check: no chain vreg may be mentioned BEFORE flag_writer or
    // AFTER the Jcc, and within the window each appears only in the consuming
    // instructions we are erasing. Since we erase the entire window
    // `(flag_writer, jcc]`, it suffices that no chain vreg escapes the window.
    for prior in &insts[..flag_writer_idx] {
        for v in &chain_vregs {
            if instruction_mentions_vreg(prior, *v) {
                return None;
            }
        }
    }
    for later in &insts[jcc_idx + 1..] {
        for v in &chain_vregs {
            if instruction_mentions_vreg(later, *v) {
                return None;
            }
        }
    }
    // NOTE (2026-08-31): this matcher used to take a block-wide
    // `HashMap<VReg, u32>` use-count map "as a redundant guard", but never
    // read it — the window is proved internal by the in-block scan above plus
    // the caller's cross-block escape scan. The parameter and the per-block
    // `vreg_uses_in_block` build that existed only to feed it are gone; the
    // side conditions and therefore the emitted bytes are unchanged.

    Some(CmpSetccBranchEdit {
        flag_writer_idx,
        jcc_idx,
        setcc_dst,
        new_cc,
        target,
    })
}

/// The standard arithmetic-comparison condition codes produced by `Icmp`/`Fcmp`
/// lowering. For these, both `cc` and `cc.invert()` are well-defined Jcc
/// predicates over the RFLAGS a comparison wrote.
fn is_standard_compare_cc(cc: trust_cg_ir::X86CondCode) -> bool {
    use trust_cg_ir::X86CondCode::*;
    matches!(cc, B | AE | BE | A | E | NE | L | GE | LE | G)
}

/// True if `inst` is a zero/non-zero test of `vreg`: `CmpRI %vreg, 0`,
/// `CmpRI8 %vreg, 0`, or `TestRR %vreg, %vreg`.
fn is_zero_test_of(inst: &X86ISelInst, vreg: VReg) -> bool {
    match inst.opcode {
        X86Opcode::CmpRI | X86Opcode::CmpRI8 => matches!(
            inst.operands.as_slice(),
            [X86ISelOperand::VReg(r), X86ISelOperand::Imm(0)] if *r == vreg
        ),
        X86Opcode::TestRR => matches!(
            inst.operands.as_slice(),
            [X86ISelOperand::VReg(a), X86ISelOperand::VReg(b)] if *a == vreg && *b == vreg
        ),
        _ => false,
    }
}

/// Returns true if `vreg` appears anywhere in `inst`'s operand list, either
/// as a top-level VReg or inside a memory-addressing operand. Conservative:
/// any mention counts.
fn instruction_mentions_vreg(inst: &X86ISelInst, vreg: VReg) -> bool {
    inst.operands
        .iter()
        .any(|op| operand_mentions_vreg(op, vreg))
}

fn operand_mentions_vreg(op: &X86ISelOperand, vreg: VReg) -> bool {
    match op {
        X86ISelOperand::VReg(v) => *v == vreg,
        X86ISelOperand::MemAddr { base, .. } => operand_mentions_vreg(base, vreg),
        X86ISelOperand::SibMemAddr { base, index, .. } => {
            operand_mentions_vreg(base, vreg) || operand_mentions_vreg(index, vreg)
        }
        _ => false,
    }
}

/// True when `inst` mentions ANY width view of `v`'s register, in any operand
/// position. Used by the latch-advance window scan, where a MISSED mention is
/// fail-open (a reader of `c` before the write-back would observe the advanced
/// value after the rewrite).
fn inst_mentions_vreg_id(inst: &X86ISelInst, v: VReg) -> bool {
    inst.operands
        .iter()
        .any(|op| operand_mentions_vreg_id(op, v))
}

fn operand_mentions_vreg_id(op: &X86ISelOperand, v: VReg) -> bool {
    match op {
        X86ISelOperand::VReg(x) => x.id == v.id,
        X86ISelOperand::MemAddr { base, .. } => operand_mentions_vreg_id(base, v),
        X86ISelOperand::SibMemAddr { base, index, .. } => {
            operand_mentions_vreg_id(base, v) || operand_mentions_vreg_id(index, v)
        }
        _ => false,
    }
}

/// True when `inst` may DEFINE any width view of `v`'s register, over the audited
/// def-position table. Class-blind on the id, as everywhere else in this file.
fn inst_defines_vreg_id_local(inst: &X86ISelInst, v: VReg) -> bool {
    crate::effects::x86_may_defined_vregs(inst).any(|d| d.id == v.id)
        || (crate::effects::x86_produces_value(inst.opcode)
            && matches!(inst.operands.first(), Some(X86ISelOperand::VReg(d)) if d.id == v.id))
}

/// Whether the latch-advance collapse may reach ACROSS the loop's other carried
/// copies (and accept the flag-neutral `Lea` spelling of the advance), rather
/// than requiring the advance, write-back, compare and branch to be adjacent.
///
/// DEFAULT OFF, and the reason is measured rather than cautionary. Widened, it
/// fires on 9 of the 18 `beat-llvm` programs and is a NET LOSS:
///
/// | program | new/old | in-batch control |
/// | --- | ---: | ---: |
/// | b1_mispredict | 0.9961 (0.39% faster) | 0.9993 |
/// | h3_box_leak | **1.0173 (1.7% SLOWER)** | 0.9986 |
/// | v3_popcount | 1.0028 | 0.9992 |
/// | h1, h4, m2, p1, p5, p6 | neutral | |
///
/// So it buys 0.39% on the largest gap and costs 1.7% on h3_box_leak, which is
/// itself one of the programs still above LLVM — removing an instruction from
/// h3's loop made it slower, the same non-monotonicity this corpus has shown
/// four other times. Correct and tested, but the global default stays as it was.
/// `-Ztrust-ir-cg-args=x86-latch-window` opts in.
fn latch_advance_window_enabled() -> bool {
    if let Some(enabled) = LATCH_ADVANCE_WINDOW.get() {
        return *enabled;
    }
    crate::tcg_env_flag("TCG_X86_LATCH_WINDOW")
}

static LATCH_ADVANCE_WINDOW: std::sync::OnceLock<bool> = std::sync::OnceLock::new();

/// Install the widened latch-advance window from a TRACKED compiler option.
pub fn set_latch_advance_window_enabled(enabled: bool) -> bool {
    match LATCH_ADVANCE_WINDOW.set(enabled) {
        Ok(()) => true,
        Err(requested) => LATCH_ADVANCE_WINDOW.get() == Some(&requested),
    }
}

/// The commutative dying-source-first swap is 🛑 REFUTED AS A DEFAULT and
/// OPT-IN only (`TCG_X86_COMMUTE_DST=1`). Per-switch isolation A/B
/// (2026-08-28, 4-program lanes): with the swap ON p1_xorshift sits at
/// ~1.48x and p6/b1 regress ~6-9%; with it OFF p1 returns to ~1.20x.
/// Root cause: for a LOOP-CARRIED chain `x' = x ^ t`, tying the
/// destination to `x` (the original order) lets regalloc coalesce the
/// backedge — x' simply becomes x's register, zero copies — while tying
/// to the dying temp forces a real x'-to-x copy every iteration. The
/// single-def/single-use "dying" model cannot see that the destination is
/// the carried successor of s1; a future version would need to exempt
/// operands whose def-use web forms a carried chain with the destination.
fn commute_dying_source_enabled() -> bool {
    std::env::var_os("TCG_X86_COMMUTE_DST").is_some()
}

/// Whether block `block_id` of `func` holds an instruction with `opcode`
/// (false for an absent block).
fn block_has_opcode(
    func: &X86ISelFunction,
    block_id: trust_cg_lower::instructions::Block,
    opcode: X86Opcode,
) -> bool {
    func.blocks
        .get(&block_id)
        .is_some_and(|block| block.insts.iter().any(|inst| inst.opcode == opcode))
}

/// FUNCTION-WIDE use and def counts under [`vreg_uses_in_block`]'s exact
/// def/use convention (operand 0 of a value-producing opcode is the def; its
/// only reads are addressing base/index regs; every other operand is a use).
fn function_use_def_counts(func: &X86ISelFunction) -> (FxHashMap<VReg, u32>, FxHashMap<VReg, u32>) {
    let mut uses = FxHashMap::default();
    let mut defs = FxHashMap::default();
    for block in func.blocks.values() {
        for inst in &block.insts {
            count_inst_uses_defs(inst, &mut uses, &mut defs);
        }
    }
    (uses, defs)
}

/// One instruction's contribution to [`function_use_def_counts`], which is
/// the sum of these over every instruction of the function.
fn count_inst_uses_defs(
    inst: &X86ISelInst,
    uses: &mut FxHashMap<VReg, u32>,
    defs: &mut FxHashMap<VReg, u32>,
) {
    let produces = crate::effects::x86_produces_value(inst.opcode);
    for (idx, op) in inst.operands.iter().enumerate() {
        if produces && idx == 0 {
            if let X86ISelOperand::VReg(d) = op {
                *defs.entry(*d).or_insert(0) += 1;
            }
            count_addressing_uses(op, uses);
            continue;
        }
        count_operand_uses(op, uses);
    }
}

static TEST_ELIDE_ENABLED: std::sync::OnceLock<bool> = std::sync::OnceLock::new();

/// Install the redundant self-test elision from a TRACKED compiler option, once
/// (`-Ztrust-ir-cg-args=x86-test-elide`). DEFAULT OFF.
///
/// The pass deletes a `test v,v` / `cmp v,0` whose ZF is already established by
/// the nearest preceding ALU definition of `v`, when every downstream flag reader
/// in the block needs only ZF. Its comment calls it opt-in "for the staged
/// rollout" — i.e. pending measurement rather than refused — and the only lever
/// was `TCG_X86_TEST_ELIDE`, which `trustc` refuses before the backend loads, so
/// the staged rollout could not actually be measured through the bridge.
pub fn set_test_elide_enabled(enabled: bool) -> bool {
    match TEST_ELIDE_ENABLED.set(enabled) {
        Ok(()) => true,
        Err(requested) => TEST_ELIDE_ENABLED.get() == Some(&requested),
    }
}

fn test_elide_enabled() -> bool {
    if let Some(enabled) = TEST_ELIDE_ENABLED.get() {
        return *enabled;
    }
    crate::tcg_env_flag("TCG_X86_TEST_ELIDE")
}

static LEA_WRITEBACK_DISABLED: std::sync::OnceLock<bool> = std::sync::OnceLock::new();

/// Install the two-address increment collapse's opt-out from a TRACKED compiler
/// option, once (`-Ztrust-ir-cg-args=no-x86-lea-writeback`). `true` disables it.
///
/// The environment fallback below is refused by `trustc`, so this setter is the
/// only channel that can A/B the fold through the bridge.
pub fn set_lea_writeback_disabled(disabled: bool) -> bool {
    match LEA_WRITEBACK_DISABLED.set(disabled) {
        Ok(()) => true,
        Err(requested) => LEA_WRITEBACK_DISABLED.get() == Some(&requested),
    }
}

fn lea_writeback_collapse_enabled() -> bool {
    if let Some(disabled) = LEA_WRITEBACK_DISABLED.get() {
        return !*disabled;
    }
    // Match tracked Boolean policy: an explicit zero does not opt out.
    std::env::var_os("TCG_NO_X86_LEA_WRITEBACK")
        .is_none_or(|value| value == std::ffi::OsStr::new("0"))
}

/// Collapse a two-address increment expansion: `Lea tmp, [base + disp]` followed
/// immediately by `MovRR base, tmp` becomes `AddRI base, base, disp`.
///
/// # The shape
///
/// A source-level `x += k` on a value the register allocator keeps in `base`
/// reaches the machine level as a non-destructive `lea` into a fresh vreg plus a
/// copy back, because `lea` does not write flags and the expansion is
/// flag-neutral by construction:
///
/// ```text
///   lea  tmp, [base + 1]
///   mov  base, tmp        ; write-back
/// ```
///
/// Two instructions and a wasted register for what `add $1, base` does in one.
/// Measured in `p2_collatz`'s inner loop, and present once or twice per hot loop
/// in 11 of the 14 ported beat-llvm programs.
///
/// # Why the flag condition is the whole argument
///
/// `Lea` writes NO flags; `AddRI` writes all of them. So the rewrite is only
/// sound where the flags are dead from the `lea`'s position onward, and
/// [`sib_fold_flags_dead`] is what establishes that — it refuses on the first
/// flag reader and on any control-flow or ABI boundary that could expose RFLAGS.
/// This is exactly why the expansion exists in the first place: whoever emitted
/// it could not know the flags were dead, and this pass can.
///
/// # Side conditions (any failure leaves both instructions alone)
///
/// * The two instructions are ADJACENT, so nothing between them can read `base`
///   (which would see the pre-increment value the fold destroys) or redefine
///   either register.
/// * The `lea`'s address is `MemAddr { base: VReg, disp }` with `disp != 0`; a
///   SIB form has a runtime index and is not an immediate add, and `disp == 0` is
///   a plain copy for other passes to handle.
/// * `tmp` is globally single-def and used EXACTLY once (by the write-back), so
///   retiring it cannot change any other reader.
/// * `base` and `tmp` are distinct 64-bit registers, and neither instruction
///   carries a `proof_origin` or non-default flags.
fn lea_writeback_collapse_run_on_block(
    func: &mut X86ISelFunction,
    block_id: trust_cg_lower::instructions::Block,
    counts: &FnUseDefCounts,
) -> bool {
    let Some(block) = func.blocks.get(&block_id) else {
        return false;
    };
    let insts = block.insts.clone();
    // (lea index, base vreg, displacement)
    let mut edits: Vec<(usize, VReg, i64)> = Vec::new();

    for idx in 0..insts.len().saturating_sub(1) {
        let lea = &insts[idx];
        let mov = &insts[idx + 1];
        if mov.opcode != X86Opcode::MovRR {
            continue;
        }
        if !matches!(lea.opcode, X86Opcode::Lea | X86Opcode::AddRI) {
            continue;
        }
        if lea.proof_origin.is_some() || mov.proof_origin.is_some() {
            continue;
        }
        if lea.flags != lea.opcode.default_flags() || mov.flags != mov.opcode.default_flags() {
            continue;
        }
        // Two spellings of the same non-destructive increment reach here:
        //
        //   Lea   tmp, [base + disp]   -- flag-NEUTRAL, so folding to `AddRI`
        //                                 introduces a flag write and needs the
        //                                 flag-deadness proof below.
        //   AddRI tmp, base, disp      -- already writes the flags, at the very
        //                                 position the rewrite keeps them at and
        //                                 with the identical result, so that
        //                                 spelling needs NO flag condition.
        let (tmp, base, disp) = match lea.opcode {
            X86Opcode::Lea => {
                let [
                    X86ISelOperand::VReg(tmp),
                    X86ISelOperand::MemAddr { base, disp },
                ] = lea.operands.as_slice()
                else {
                    continue;
                };
                let X86ISelOperand::VReg(base) = base.as_ref() else {
                    continue;
                };
                (*tmp, *base, i64::from(*disp))
            }
            _ => {
                let [
                    X86ISelOperand::VReg(tmp),
                    X86ISelOperand::VReg(base),
                    X86ISelOperand::Imm(imm),
                ] = lea.operands.as_slice()
                else {
                    continue;
                };
                (*tmp, *base, *imm)
            }
        };
        let (tmp, base) = (&tmp, &base);
        if disp == 0 {
            continue;
        }
        // The write-back must copy exactly this `tmp` into exactly this `base`.
        let [X86ISelOperand::VReg(mov_dst), X86ISelOperand::VReg(mov_src)] =
            mov.operands.as_slice()
        else {
            continue;
        };
        if mov_dst != base || mov_src != tmp || base == tmp {
            continue;
        }
        if base.class != RegClass::Gpr64 || tmp.class != RegClass::Gpr64 {
            continue;
        }
        if counts.def_count(*tmp) != 1 || counts.use_count(*tmp) != 1 {
            continue;
        }
        // Only the `Lea` spelling introduces a flag write that was not there
        // before; the `AddRI` spelling keeps the same write at the same place.
        if lea.opcode == X86Opcode::Lea && !sib_fold_flags_dead(&insts, idx) {
            continue;
        }
        edits.push((idx, *base, disp));
    }

    if edits.is_empty() {
        return false;
    }
    let block = func.blocks.get_mut(&block_id).expect("block existed above");
    // Descending so earlier indices stay valid as the write-backs are removed.
    for (idx, base, disp) in edits.into_iter().rev() {
        block.insts[idx] = X86ISelInst::new(
            X86Opcode::AddRI,
            vec![
                X86ISelOperand::VReg(base),
                X86ISelOperand::VReg(base),
                X86ISelOperand::Imm(disp),
            ],
        );
        block.insts.remove(idx + 1);
    }
    true
}

/// Latch-advance collapse: `AddRI n,c,k ; MovRR c,n ; Cmp{RI,RR} n,… ; Jcc`
/// -> `AddRI c,c,k ; Cmp{RI,RR} c,… ; Jcc` when `n` is single-def and its
/// ONLY uses are the write-back and the compare. Value-exact: the compare
/// reads the identical advanced value; `c` holds it from the AddRI onward
/// (nothing sits between the four matched instructions); the AddRI's flag
/// write happens at the same position as before and is overwritten by the
/// compare either way. Windows are matched against counts frozen at pass
/// entry — a vreg consumed by one rewrite cannot satisfy another window's
/// side conditions (its counts would have excluded the first match), so
/// applying all matches in one sweep is sound.
fn latch_advance_collapse_run_on_block(
    func: &mut X86ISelFunction,
    block_id: trust_cg_lower::instructions::Block,
    uses: &FxHashMap<VReg, u32>,
    defs: &FxHashMap<VReg, u32>,
    widened: bool,
) -> bool {
    let Some(block) = func.blocks.get_mut(&block_id) else {
        return false;
    };
    let insts = &mut block.insts;
    let mut changed = false;
    let mut i = 0;
    while i + 3 < insts.len() {
        let matched = (|| -> Option<(VReg, VReg, i64, usize, usize)> {
            // The advance arrives in EITHER spelling. `AddRI n,c,k` already
            // writes the flags at the position the rewrite keeps them at, so it
            // needs no flag condition. `Lea n,[c+k]` is flag-NEUTRAL, so folding
            // it to `AddRI` INTRODUCES a flag write — discharged by the window
            // itself: the matched `Cmp` overwrites the flags before the matched
            // `Jcc` reads them, and the scan below admits no flag reader in
            // between.
            let (n, c, k) = match (insts[i].opcode, insts[i].operands.as_slice()) {
                (
                    X86Opcode::AddRI,
                    [
                        X86ISelOperand::VReg(n),
                        X86ISelOperand::VReg(c),
                        X86ISelOperand::Imm(k),
                    ],
                ) => (*n, *c, *k),
                (
                    X86Opcode::Lea,
                    [
                        X86ISelOperand::VReg(n),
                        X86ISelOperand::MemAddr { base, disp },
                    ],
                ) if widened => match base.as_ref() {
                    X86ISelOperand::VReg(c) => (*n, *c, i64::from(*disp)),
                    _ => return None,
                },
                _ => return None,
            };
            if n == c || n.class != c.class || n.class != RegClass::Gpr64 {
                return None;
            }
            // Only the `Lea` spelling INTRODUCES a flag write at the advance's
            // position (`AddRI` already wrote the flags there, unchanged by the
            // rewrite). That distinction is what scan (1) below needs.
            let advance_introduces_flag_write = insts[i].opcode == X86Opcode::Lea;
            if insts[i].proof_origin.is_some() || insts[i].flags != insts[i].opcode.default_flags()
            {
                return None;
            }
            // `n` exists ONLY inside this window: one def (the advance), two
            // uses (the write-back and the compare).
            if defs.get(&n).copied().unwrap_or(0) != 1 || uses.get(&n).copied().unwrap_or(0) != 2 {
                return None;
            }

            // The write-back and the compare NEED NOT BE ADJACENT to the advance.
            // The ISel interleaves the loop's OTHER carried copies between them —
            // b1_mispredict's latch is
            //   AddRI n,c,1 ; MovRR v11,v29 ; MovRR c,n ; MovRR v10,v107 ; CmpRI n,K ; Jcc
            // so an adjacency-only matcher declined it. Search forward instead,
            // with exactly the two scans the rewrite needs.
            // Off: the original strict-adjacency window (the write-back at i+1,
            // the compare at i+2, the Jcc at i+3). On: search forward up to 12.
            let limit = if widened {
                (i + 12).min(insts.len())
            } else {
                (i + 4).min(insts.len())
            };

            // (1) Find the write-back `MovRR c,n`. Between the advance and it,
            //     NOTHING may mention `c`: after the rewrite `c` is clobbered at
            //     the advance, so a reader in that range would see the ADVANCED
            //     value instead of the old one.
            let mut w = None;
            for (j, inst) in insts.iter().enumerate().take(limit).skip(i + 1) {
                if inst.opcode == X86Opcode::MovRR
                    && inst.operands.as_slice()
                        == [X86ISelOperand::VReg(c), X86ISelOperand::VReg(n)].as_slice()
                    && inst.proof_origin.is_none()
                {
                    w = Some(j);
                    break;
                }
                if inst_mentions_vreg_id(inst, c) || inst_mentions_vreg_id(inst, n) {
                    return None;
                }
                // ⚑ SOUNDNESS, and it only bites once `widened` admits the `Lea`
                // spelling: rewriting a flag-NEUTRAL `Lea` to `AddRI` makes
                // position `i` a flag WRITER. A flag reader between the advance
                // and the write-back would then read the advance's flags instead
                // of the ones live-in to `i`. Scan (2) already refuses a flag
                // reader on its own stretch; this stretch is empty in the strict
                // window (`w == i + 1`) and up to 11 instructions long in the
                // widened one, which is why the check was not needed before.
                if advance_introduces_flag_write && x86_reads_flags(inst.opcode) {
                    return None;
                }
            }
            let w = w?;
            if !widened && w != i + 1 {
                return None;
            }

            // (2) Find `Cmp n,_` with its `Jcc` immediately after. Between the
            //     write-back and it, nothing may DEFINE `c` or `n` (the compare
            //     is rewritten to read `c`, so it must still hold the advanced
            //     value) and nothing may read the flags (the advance's flag write
            //     stays where it is, but the compare must remain the reader the
            //     `Jcc` sees).
            let mut m = None;
            for j in (w + 1)..limit.saturating_sub(1) {
                let inst = &insts[j];
                let reads_n = match (inst.opcode, inst.operands.as_slice()) {
                    (X86Opcode::CmpRI, [X86ISelOperand::VReg(a), X86ISelOperand::Imm(_)]) => {
                        *a == n
                    }
                    (X86Opcode::CmpRR, [X86ISelOperand::VReg(a), X86ISelOperand::VReg(b)]) => {
                        *a == n && *b != n && *b != c
                    }
                    _ => false,
                };
                if reads_n && insts[j + 1].opcode == X86Opcode::Jcc && inst.proof_origin.is_none() {
                    m = Some(j);
                    break;
                }
                if inst_defines_vreg_id_local(inst, c)
                    || inst_defines_vreg_id_local(inst, n)
                    || x86_reads_flags(inst.opcode)
                {
                    return None;
                }
            }
            let m = m?;
            if !widened && m != i + 2 {
                return None;
            }
            Some((n, c, k, w, m))
        })();
        if let Some((_n, c, k, w, m)) = matched {
            // Rebuild as the in-place `AddRI c,c,k` regardless of the matched
            // spelling, rewrite the compare to read `c`, and drop the write-back.
            insts[i] = X86ISelInst::new(
                X86Opcode::AddRI,
                vec![
                    X86ISelOperand::VReg(c),
                    X86ISelOperand::VReg(c),
                    X86ISelOperand::Imm(k),
                ],
            );
            if let X86ISelOperand::VReg(a) = &mut insts[m].operands[0] {
                *a = c;
            }
            insts.remove(w);
            changed = true;
            i = m; // past the rewritten compare (indices shifted down by one)
        } else {
            i += 1;
        }
    }
    changed
}

/// `LeaSib t,[b+i*s+d] ; AddRI x,t,k` -> `LeaSib x,[b+i*s+(d+k)]` when `t`
/// is single-def and this AddRI is its only use, the AddRI's flag write is
/// provably dead (LEA writes no flags, so the fold must not lose a consumed
/// flag result), and `d+k` fits i32. The two instructions need not be
/// adjacent as long as nothing between them redefines `b`/`i` (we require
/// adjacency anyway — the ISel emits the pair back-to-back and adjacency
/// keeps the redefinition argument trivial).
fn lea_disp_fold_run_on_block(
    func: &mut X86ISelFunction,
    block_id: trust_cg_lower::instructions::Block,
    uses: &FxHashMap<VReg, u32>,
    defs: &FxHashMap<VReg, u32>,
) -> bool {
    let Some(block) = func.blocks.get_mut(&block_id) else {
        return false;
    };
    let insts = &mut block.insts;
    let mut changed = false;
    let mut i = 0;
    while i + 1 < insts.len() {
        let matched = (|| -> Option<(VReg, i32)> {
            if insts[i].opcode != X86Opcode::LeaSib {
                return None;
            }
            let [
                X86ISelOperand::VReg(t),
                X86ISelOperand::SibMemAddr { disp, .. },
            ] = insts[i].operands.as_slice()
            else {
                return None;
            };
            let (t, d) = (*t, *disp);
            if insts[i + 1].opcode != X86Opcode::AddRI {
                return None;
            }
            let [
                X86ISelOperand::VReg(x),
                X86ISelOperand::VReg(src),
                X86ISelOperand::Imm(k),
            ] = insts[i + 1].operands.as_slice()
            else {
                return None;
            };
            if *src != t || *x == t || x.class != t.class {
                return None;
            }
            // `t` lives only here: one def (the LeaSib), one use (this AddRI).
            if defs.get(&t).copied().unwrap_or(0) != 1 || uses.get(&t).copied().unwrap_or(0) != 1 {
                return None;
            }
            // The AddRI's flag write must be dead — the fold removes it.
            if !flags_written_here_are_dead(insts, i + 1) {
                return None;
            }
            let folded = (d as i64).checked_add(*k)?;
            let folded = i32::try_from(folded).ok()?;
            Some((*x, folded))
        })();
        if let Some((x, folded)) = matched {
            insts[i].operands[0] = X86ISelOperand::VReg(x);
            if let X86ISelOperand::SibMemAddr { disp, .. } = &mut insts[i].operands[1] {
                *disp = folded;
            }
            insts.remove(i + 1);
            changed = true;
        }
        i += 1;
    }
    changed
}

/// Commutative dying-source-first normalization: for `Op d, s1, s2` with a
/// commutative wrapping/bitwise `Op`, when `s1` outlives the op (more than
/// one use or def) but `s2` is single-def and this is its only use, swap to
/// `Op d, s2, s1` so the two-address tie copies the DYING value. Result and
/// flags are identical for either operand order on AddRR/ImulRR/AndRR/OrRR/
/// XorRR (all flag outputs are functions of the unordered operand pair).
fn commute_dying_source_run_on_block(
    func: &mut X86ISelFunction,
    block_id: trust_cg_lower::instructions::Block,
    uses: &FxHashMap<VReg, u32>,
    defs: &FxHashMap<VReg, u32>,
) -> bool {
    let Some(block) = func.blocks.get_mut(&block_id) else {
        return false;
    };
    let mut changed = false;
    for inst in &mut block.insts {
        if !matches!(
            inst.opcode,
            X86Opcode::AddRR
                | X86Opcode::ImulRR
                | X86Opcode::AndRR
                | X86Opcode::OrRR
                | X86Opcode::XorRR
        ) {
            continue;
        }
        let [
            X86ISelOperand::VReg(d),
            X86ISelOperand::VReg(s1),
            X86ISelOperand::VReg(s2),
        ] = inst.operands.as_slice()
        else {
            continue;
        };
        let (d, s1, s2) = (*d, *s1, *s2);
        if d == s1 || d == s2 || s1 == s2 || s1.class != s2.class {
            continue;
        }
        let dying = |v: VReg| {
            defs.get(&v).copied().unwrap_or(0) == 1 && uses.get(&v).copied().unwrap_or(0) == 1
        };
        if !dying(s1) && dying(s2) {
            inst.operands.swap(1, 2);
            changed = true;
        }
    }
    changed
}

fn vreg_uses_in_block(insts: &[X86ISelInst]) -> FxHashMap<VReg, u32> {
    use crate::effects::x86_produces_value;
    let mut counts = FxHashMap::default();
    for inst in insts {
        let produces = x86_produces_value(inst.opcode);
        for (idx, op) in inst.operands.iter().enumerate() {
            // Operand 0 of a value-producing inst is the def; skip it as a
            // top-level use. Memory-addr operands inside the def slot (e.g.,
            // store-to-memory destinations) are not common in ISel output for
            // producing opcodes, and Setcc/Movzx's operand-0 is a plain VReg
            // we don't want to count.
            if produces && idx == 0 {
                // But memory-addressing inside op 0 (rare) would still mean
                // base/index regs are *read*. Walk only the addressing regs.
                count_addressing_uses(op, &mut counts);
                continue;
            }
            count_operand_uses(op, &mut counts);
        }
    }
    counts
}

fn count_operand_uses(op: &X86ISelOperand, counts: &mut FxHashMap<VReg, u32>) {
    match op {
        X86ISelOperand::VReg(v) => {
            *counts.entry(*v).or_insert(0) += 1;
        }
        X86ISelOperand::MemAddr { base, .. } => count_operand_uses(base, counts),
        X86ISelOperand::SibMemAddr { base, index, .. } => {
            count_operand_uses(base, counts);
            count_operand_uses(index, counts);
        }
        _ => {}
    }
}

fn count_addressing_uses(op: &X86ISelOperand, counts: &mut FxHashMap<VReg, u32>) {
    match op {
        X86ISelOperand::MemAddr { base, .. } => count_operand_uses(base, counts),
        X86ISelOperand::SibMemAddr { base, index, .. } => {
            count_operand_uses(base, counts);
            count_operand_uses(index, counts);
        }
        _ => {}
    }
}

/// How many times a SINGLE VReg `target` is USED in ONE instruction — the
/// per-instruction, single-key specialization of [`vreg_uses_in_block`]. Uses
/// the SAME def/use convention (operand 0 of a value-producing opcode is the
/// def, whose only reads are its addressing base/index regs; every other
/// operand is a use, counting a mem operand's base/index) so that
/// `vreg_uses_in_inst(inst, v)` is byte-identical to
/// `vreg_uses_in_block(std::slice::from_ref(inst)).get(&v).copied().unwrap_or(0)`
/// — but with NO HashMap allocation. The SIB-fold consumer scans
/// ([`collect_addr_consumers`] / [`collect_pointer_mem_ops`]) call this once per
/// instruction per anchor; the previous per-instruction HashMap build made those
/// scans allocate O(anchors * insts) maps on a large block.
fn vreg_uses_in_inst(inst: &X86ISelInst, target: VReg) -> u32 {
    use crate::effects::x86_produces_value;
    let produces = x86_produces_value(inst.opcode);
    let mut count = 0u32;
    for (idx, op) in inst.operands.iter().enumerate() {
        if produces && idx == 0 {
            count += count_addressing_uses_of(op, target);
        } else {
            count += count_operand_uses_of(op, target);
        }
    }
    count
}

/// Single-key mirror of [`count_operand_uses`].
fn count_operand_uses_of(op: &X86ISelOperand, target: VReg) -> u32 {
    match op {
        X86ISelOperand::VReg(v) => u32::from(*v == target),
        X86ISelOperand::MemAddr { base, .. } => count_operand_uses_of(base, target),
        X86ISelOperand::SibMemAddr { base, index, .. } => {
            count_operand_uses_of(base, target) + count_operand_uses_of(index, target)
        }
        _ => 0,
    }
}

/// Single-key mirror of [`count_addressing_uses`].
fn count_addressing_uses_of(op: &X86ISelOperand, target: VReg) -> u32 {
    match op {
        X86ISelOperand::MemAddr { base, .. } => count_operand_uses_of(base, target),
        X86ISelOperand::SibMemAddr { base, index, .. } => {
            count_operand_uses_of(base, target) + count_operand_uses_of(index, target)
        }
        _ => 0,
    }
}

// ---------------------------------------------------------------------------
// AND-power-of-2 + CMP-zero + Jcc -> BT + Jcc (3-instruction window rewrite)
// ---------------------------------------------------------------------------
//
// Pattern (before):
//   [1] AndRI %dst, [%src,] #(1 << k)   ; two-op `[%dst, imm]` or three-op
//                                        ; `[%dst, %src, imm]` form
//   [2] CmpRI %dst, #0                   ; flags <- (dst == 0)
//   [3] Jcc {E|NE}, target               ; branch on ZF
//
// Pattern (after):
//   [1] BtRI %bt_src, #k                 ; CF <- bit k of %bt_src
//   [2] Jcc {AE|B}, target               ; AE = CF==0 = "bit was 0" = original E
//                                        ; B  = CF==1 = "bit was 1" = original NE
//
// HAND-PROOF (algebraic identity):
//   - (x AND (1 << k)) == 0  iff  bit k of x is 0.
//   - BtRI sets CF := bit_k(src), and leaves OF/SF/ZF/AF/PF undefined per
//     Intel SDM.
//   - The original CMP-zero+Jcc tests ZF. We re-encode the predicate on CF
//     by inverting the condition: Jcc E (ZF=1, AND result zero) becomes
//     Jcc AE (CF=0, bit was clear); Jcc NE (ZF=0, AND result nonzero) becomes
//     Jcc B (CF=1, bit was set).
//
// SIDE CONDITIONS (each must hold or the rewrite is unsound):
//   (a) AndRI's immediate is a positive power of two and k = imm.trailing_zeros()
//       fits in the AND's register class (k <= 63 for Gpr64, k <= 31 for Gpr32).
//       `imm.count_ones() == 1` together with `imm > 0` enforces this.
//   (b) The CmpRI immediately follows the AndRI; the Jcc immediately follows
//       the CmpRI. Adjacency guarantees no foreign flag write between AND and
//       CMP, and between CMP and Jcc - so the flags consumed by Jcc come from
//       CmpRI (and we are free to replace both AND and CMP).
//   (c) CmpRI compares the AND's destination vreg against the immediate 0.
//   (d) The Jcc tests {E, NE}. Other condition codes (S, L, etc.) would map
//       to flags that BT leaves undefined; we refuse to fire on those.
//   (e) Reserved. The original single-use guard is subsumed by (b) (adjacency,
//       so no intervening instruction reads %dst between AndRI and CmpRI) and
//       (f) (dst dead after Jcc, so no later instruction reads %dst). Earlier
//       instructions reading %dst are unaffected because they precede the
//       AndRI we are erasing.
//   (f) AndRI's destination is dead after the Jcc - no later block-local
//       instruction mentions %dst. This is what makes erasing the AND's
//       write-back observationally invisible.
//   (g) AndRI's flags are the opcode default (no foreign side-effect bits)
//       and the AndRI does not touch memory (we are erasing it; if it had
//       side effects beyond writing RFLAGS, the rewrite would change
//       observable behavior). Same constraint on CmpRI.
//   (h) The BT source register is the AndRI's source operand:
//         - two-op form `AndRI [%dst, imm]`: %dst was both src and dst;
//           since (f) requires %dst to be dead after Jcc, the BT can read
//           %dst directly (its pre-AND value is what BT needs, but BT
//           sources from a vreg by name and the AND has already been
//           erased - so the value at the BT site is the original %dst).
//         - three-op form `AndRI [%dst, %src, imm]`: BT reads %src directly.
//
// PROOF PROVENANCE: hand-proved peephole. Each rewritten BtRI and Jcc inherit
// `proof_origin` from the consumed AndRI/Jcc respectively, so source-location
// reporting still points at the originating trust_ir instruction.
//
// WHY THE TWO-OP FORM IS SOUND: trust-cg-ir's two-operand `AndRI [%v, imm]`
// is a read-modify-write of %v - it reads the pre-AND value of %v and writes
// %v back. After our rewrite, the AND is erased, so %v at the BtRI point
// still holds its pre-AND value. The pre-AND value is exactly what we need
// to test (we are checking bit k of the original input). Since (f) makes %v
// dead after the Jcc, erasing the AND's write-back is observationally
// invisible.

/// Flag-barrier predicate for a CFG-aware scan.
///
/// [`instruction_may_export_flags`] treats ANY terminator as an export, which is
/// correct for a block-local pass that cannot see past the branch — but here the
/// successor is analysed explicitly, so a plain unconditional `Jmp` must be
/// TRANSPARENT or the scan can never reach the CFG step at all. (Measured: with
/// the terminator treated as a barrier, the rotate peephole fired ZERO times —
/// every candidate rejected at its block's closing `Jmp`.)
///
/// Still barriers: calls and anything with side effects. A CONDITIONAL branch
/// needs no special case — `x86_reads_flags` already covers `Jcc`, and a `Ret`
/// block has no successors, where the caller's `any()` over an empty successor
/// set correctly reports the flags dead (they are not part of the ABI result).
fn flags_barrier_for_cfg_scan(inst: &X86ISelInst) -> bool {
    inst.flags.is_call() || inst.flags.has_side_effects()
}

/// Block-granularity FLAGS LIVENESS: `true` for block `B` when a flag value
/// defined BEFORE `B` may still be read on some path from `B`'s entry.
///
/// A backward fixpoint over the CFG. Per block the local answer is the FIRST
/// flag-relevant instruction: a reader (or a possible flag export, e.g. a call)
/// means live, a full overwrite means dead, and a block with neither passes the
/// question through to its successors. A block with no successors is dead —
/// flags are not observable across a return.
///
/// Needed because the block-local `flags_written_here_are_dead` treats
/// "reached the end of the block" as LIVE, which is the right default but makes
/// the rotate idiom unrecognisable: the `OrRR` completing
/// `(s << k) | (s >>u (w-k))` sits at the end of its block and the instruction
/// that kills the flags is in the successor. Measured with the block-local
/// check alone, the rotate peephole fired ZERO times across all 18 beat-llvm
/// programs.
fn flags_live_in_by_block(
    func: &X86ISelFunction,
) -> FxHashMap<trust_cg_lower::instructions::Block, bool> {
    let local_answer = |b: &trust_cg_lower::X86ISelBlock| -> Option<bool> {
        b.insts.iter().find_map(|inst| {
            if x86_reads_flags(inst.opcode) || flags_barrier_for_cfg_scan(inst) {
                Some(true)
            } else if condition_flag_overwrite(inst) == FlagOverwrite::Full {
                Some(false)
            } else {
                None
            }
        })
    };
    let mut live: FxHashMap<_, bool> = func.blocks.keys().map(|b| (*b, false)).collect();
    // Monotone in `live`, so this terminates; bounded anyway for safety.
    for _ in 0..=func.blocks.len() {
        let mut changed = false;
        for (id, block) in &func.blocks {
            let v = match local_answer(block) {
                Some(x) => x,
                None => block
                    .successors
                    .iter()
                    .any(|s| live.get(s).copied().unwrap_or(true)),
            };
            if live.get(id).copied() != Some(v) {
                live.insert(*id, v);
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
    live
}

/// Are the flags written at `index` of `block_id` dead, allowing the kill to
/// happen in a successor? Scans forward locally, then defers to
/// [`flags_live_in_by_block`] for the fall-off-the-end case.
fn flags_dead_at(
    func: &X86ISelFunction,
    live_in: &FxHashMap<trust_cg_lower::instructions::Block, bool>,
    block_id: trust_cg_lower::instructions::Block,
    index: usize,
) -> bool {
    let Some(block) = func.blocks.get(&block_id) else {
        return false;
    };
    for inst in &block.insts[index + 1..] {
        if x86_reads_flags(inst.opcode) || flags_barrier_for_cfg_scan(inst) {
            return false;
        }
        if condition_flag_overwrite(inst) == FlagOverwrite::Full {
            return true;
        }
    }
    !block
        .successors
        .iter()
        .any(|s| live_in.get(s).copied().unwrap_or(true))
}

/// ROTATE IDIOM -> ROL. Collapses the six-instruction `rotate_left` lowering
///
/// ```text
///   a = ShlRI(s, k)
///   b = ShrRI(s, w - k)
///   d = OrRR(a, b)          ==>   d = RolRI(s, k)
/// ```
///
/// x86 had NO rotate opcode until `RolRI`, so `x.rotate_left(k)` cost six
/// instructions where AArch64 has emitted a single `ROR` all along — and on a
/// dependency chain the latency cost exceeds even that. The x86 mirror of
/// `rotate_idiom.rs`.
///
/// SOUNDNESS. `ROL(s, k)` IS `(s << k) | (s >>u (w - k))` for `k` in `[1, w)`;
/// that obligation is proven with refuting controls
/// (`x86_64_lowering_proofs::proof_x86_rol_ri`). The side conditions establish
/// only that these three instructions really are that shape:
///
/// * both shifts read the SAME source and both amounts are immediates summing
///   EXACTLY to the register width;
/// * `a` and `b` are each defined ONCE function-wide and used ONLY by this
///   `OrRR`, so the rewrite leaves both shifts dead for DCE rather than a
///   half-live mixed state;
/// * `s` is not redefined between its shifts and the `OrRR`;
/// * THE FLAGS ARE DEAD. This is load-bearing, not hygiene: `OR` sets ZF/SF/PF
///   from the result while `ROL` leaves them UNTOUCHED, so the rewrite is only
///   valid where nothing observes them. `post_ra_dataflow` models the rotate's
///   real flag effect separately and fails closed if this is ever wrong.
fn rotate_idiom_run_on_block(
    func: &mut X86ISelFunction,
    block_id: trust_cg_lower::instructions::Block,
    live_in: &FxHashMap<trust_cg_lower::instructions::Block, bool>,
) -> bool {
    let Some(block) = func.blocks.get(&block_id) else {
        return false;
    };
    let insts = &block.insts;
    let use_counts = vreg_uses_in_block(insts);
    // (or_index, dst, src, amount, shl_index, shr_index)
    let mut edits: Vec<(usize, VReg, VReg, i64, usize, usize)> = Vec::new();

    for (i, inst) in insts.iter().enumerate() {
        if inst.opcode != X86Opcode::OrRR || inst.operands.len() < 3 {
            continue;
        }
        let (
            Some(X86ISelOperand::VReg(d)),
            Some(X86ISelOperand::VReg(a)),
            Some(X86ISelOperand::VReg(b)),
        ) = (
            inst.operands.first(),
            inst.operands.get(1),
            inst.operands.get(2),
        )
        else {
            continue;
        };
        let width: i64 = match d.class {
            RegClass::Gpr64 => 64,
            RegClass::Gpr32 => 32,
            _ => continue,
        };

        let mut shl: Option<(usize, VReg, i64)> = None;
        let mut shr: Option<(usize, VReg, i64)> = None;
        for (j, cand) in insts[..i].iter().enumerate() {
            let (
                Some(X86ISelOperand::VReg(cd)),
                Some(X86ISelOperand::VReg(cs)),
                Some(X86ISelOperand::Imm(amt)),
            ) = (
                cand.operands.first(),
                cand.operands.get(1),
                cand.operands.get(2),
            )
            else {
                continue;
            };
            if cd == a || cd == b {
                match cand.opcode {
                    X86Opcode::ShlRI => shl = Some((j, *cs, *amt)),
                    X86Opcode::ShrRI => shr = Some((j, *cs, *amt)),
                    _ => {}
                }
            }
        }
        let (Some((shl_at, shl_src, k)), Some((shr_at, shr_src, r))) = (shl, shr) else {
            continue;
        };
        if shl_src != shr_src || k + r != width || !(1..width).contains(&k) {
            continue;
        }
        if function_vreg_def_count(func, *a) != 1
            || function_vreg_def_count(func, *b) != 1
            || use_counts.get(a).copied().unwrap_or(0) != 1
            || use_counts.get(b).copied().unwrap_or(0) != 1
        {
            continue;
        }
        let first_shift = shl_at.min(shr_at);
        if insts[first_shift..i].iter().any(|between| {
            crate::effects::x86_produces_value(between.opcode)
                && matches!(between.operands.first(), Some(X86ISelOperand::VReg(v)) if *v == shl_src)
        }) {
            continue;
        }
        if !flags_dead_at(func, live_in, block_id, i) {
            continue;
        }
        edits.push((i, *d, shl_src, k, shl_at, shr_at));
    }

    if edits.is_empty() {
        return false;
    }
    let Some(block) = func.blocks.get_mut(&block_id) else {
        return false;
    };
    // Rewrite the OR in place, then DELETE the two feeding shifts.
    //
    // Deleting them here rather than leaving them for DCE is not an
    // optimisation shortcut — `X86DeadCodeElimination` runs BEFORE this pass in
    // the pipeline, so nothing else would remove them and the loop would keep
    // all six instructions plus the new rotate. The side conditions above
    // already establish exactly what deletion needs: each shift result is
    // defined ONCE function-wide and used ONLY by this `OrRR`.
    let mut doomed: Vec<usize> = Vec::new();
    for (at, d, src, k, shl_at, shr_at) in edits {
        block.insts[at] = X86ISelInst::new(
            X86Opcode::RolRI,
            vec![
                X86ISelOperand::VReg(d),
                X86ISelOperand::VReg(src),
                X86ISelOperand::Imm(k),
            ],
        );
        doomed.push(shl_at);
        doomed.push(shr_at);
    }
    doomed.sort_unstable();
    for idx in doomed.into_iter().rev() {
        block.insts.remove(idx);
    }
    true
}

// ---------------------------------------------------------------------------
// VARIABLE-count rotate idiom -> RolRCl (Stage 2 of the p6 variable-rotate arc)
// ---------------------------------------------------------------------------

/// Kill switch for the variable-count rotate collapse (any value disables).
fn rotate_var_idiom_enabled() -> bool {
    crate::env_lock::var_os("TCG_NO_X86_ROTATE_VAR_IDIOM").is_none()
}

/// Def sites of FUNCTION-WIDE single-def vregs, storing the FULL defining
/// instruction: id -> inst. The `rmw_fuse_single_def_sites` shape, but with
/// the whole instruction so the low-6 chain walk can enforce default flags
/// and no `proof_origin` on every link it crosses (fail-closed hardening the
/// opcode/operands pair cannot express).
fn rotate_var_single_def_insts(func: &X86ISelFunction) -> FxHashMap<u32, X86ISelInst> {
    use crate::effects::x86_produces_value;
    let mut sites: FxHashMap<u32, Option<X86ISelInst>> = FxHashMap::default();
    for block in func.blocks.values() {
        for inst in &block.insts {
            if !x86_produces_value(inst.opcode) {
                continue;
            }
            if let Some(X86ISelOperand::VReg(d)) = inst.operands.first() {
                match sites.entry(d.id) {
                    std::collections::hash_map::Entry::Vacant(e) => {
                        e.insert(Some(inst.clone()));
                    }
                    std::collections::hash_map::Entry::Occupied(mut e) => {
                        e.insert(None); // multi-def: disqualified
                    }
                }
            }
        }
    }
    sites
        .into_iter()
        .filter_map(|(id, v)| v.map(|v| (id, v)))
        .collect()
}

/// The whole-function facts the variable-rotate matcher consults: the
/// single-def instruction index and the function-wide use/def counts. A PURE
/// function of `func`, so one build is valid for as long as `func` is
/// unchanged — see [`rotate_var_idiom_run_on_block_with_maps`].
struct RotateVarFnMaps {
    sites: FxHashMap<u32, X86ISelInst>,
    fn_uses: FxHashMap<VReg, u32>,
    fn_defs: FxHashMap<VReg, u32>,
}

impl RotateVarFnMaps {
    fn build(func: &X86ISelFunction) -> Self {
        let sites = rotate_var_single_def_insts(func);
        let (fn_uses, fn_defs) = function_use_def_counts(func);
        RotateVarFnMaps {
            sites,
            fn_uses,
            fn_defs,
        }
    }

    /// Every entry, rendered and sorted, so two builds compare as values.
    #[cfg(any(test, debug_assertions))]
    fn canonical_view(&self) -> [Vec<String>; 3] {
        [
            sorted_debug_entries(&self.sites),
            sorted_debug_entries(&self.fn_uses),
            sorted_debug_entries(&self.fn_defs),
        ]
    }
}

/// A map's entries rendered with `Debug` and sorted, so two builds of the
/// same facts compare equal whatever their hash order.
#[cfg(any(test, debug_assertions))]
fn sorted_debug_entries<'a, K, V>(entries: impl IntoIterator<Item = (&'a K, &'a V)>) -> Vec<String>
where
    K: std::fmt::Debug + 'a,
    V: std::fmt::Debug + 'a,
{
    let mut rendered: Vec<String> = entries
        .into_iter()
        .map(|(key, value)| format!("{key:?}={value:?}"))
        .collect();
    rendered.sort();
    rendered
}

/// Chase `v` through single-def plain `MovRR` copies to a single-def `MovRI`
/// root, returning the immediate — the same soundness argument as
/// `fold_unique_const_into_imm_forms`' copy chase: a single-def vreg has one
/// static value assignment, so any read that observes a defined value
/// observes exactly the root immediate. Fail-closed on any non-default-flags
/// or proof-tagged link.
fn rotate_var_const_of(sites: &FxHashMap<u32, X86ISelInst>, v: VReg) -> Option<i64> {
    let mut v = v;
    for _ in 0..16 {
        let inst = sites.get(&v.id)?;
        if inst.proof_origin.is_some() || inst.flags != inst.opcode.default_flags() {
            return None;
        }
        match (inst.opcode, inst.operands.as_slice()) {
            (X86Opcode::MovRI, [X86ISelOperand::VReg(_), X86ISelOperand::Imm(k)]) => {
                return Some(*k);
            }
            (X86Opcode::MovRR, [X86ISelOperand::VReg(_), X86ISelOperand::VReg(s)]) => v = *s,
            _ => return None,
        }
    }
    None
}

/// If `inst` (a single-def site) is a LOW-6-BITS-PRESERVING link from its
/// destination to one source vreg, return that source. Links:
///
/// * `MovRR`/`MovRR32` register copies (a 32-bit mov zero-extends: bits 0-5
///   of the destination equal bits 0-5 of the source in every class pairing);
/// * `AndRI` whose mask has ALL-ONES low 6 bits;
/// * `AndRR` where the OTHER operand is a (copy-chased) unique constant with
///   all-ones low 6 bits.
///
/// Anything else — including a non-default-flags or proof-tagged def — is not
/// a link and stops the walk (fail-closed).
fn rotate_var_low6_link(sites: &FxHashMap<u32, X86ISelInst>, inst: &X86ISelInst) -> Option<VReg> {
    if inst.proof_origin.is_some() || inst.flags != inst.opcode.default_flags() {
        return None;
    }
    match (inst.opcode, inst.operands.as_slice()) {
        (
            X86Opcode::MovRR | X86Opcode::MovRR32,
            [X86ISelOperand::VReg(_), X86ISelOperand::VReg(s)],
        ) => Some(*s),
        (
            X86Opcode::AndRI,
            [
                X86ISelOperand::VReg(_),
                X86ISelOperand::VReg(s),
                X86ISelOperand::Imm(m),
            ],
        ) if m & 63 == 63 => Some(*s),
        (
            X86Opcode::AndRR,
            [
                X86ISelOperand::VReg(_),
                X86ISelOperand::VReg(a),
                X86ISelOperand::VReg(b),
            ],
        ) => {
            if rotate_var_const_of(sites, *b).is_some_and(|m| m & 63 == 63) {
                Some(*a)
            } else if rotate_var_const_of(sites, *a).is_some_and(|m| m & 63 == 63) {
                Some(*b)
            } else {
                None
            }
        }
        _ => None,
    }
}

/// Walk `start` back through low-6-bits-preserving single-def links. Returns
/// `(root, feed)`:
///
/// * `root` — the walk's fixpoint, used to prove the CL feed and the
///   complement chain read counts with EQUAL low 6 bits (two deterministic
///   walks that reach the same single-def root carry the same value there);
/// * `feed` — the DEEPEST `Gpr64` vreg on the walk, the value the rewrite
///   moves into RCX. Hardware masks the CL count mod 64 (the Stage-1 masked
///   machine model `encode_rol_rcl_masked` proves exactly this), so any
///   low-6-equal feed is exact; choosing the deepest one lets DCE kill the
///   whole masking chain (the p6 [1]-[6] chain).
fn rotate_var_low6_walk(sites: &FxHashMap<u32, X86ISelInst>, start: VReg) -> (VReg, VReg) {
    let mut v = start;
    let mut feed = start;
    for _ in 0..16 {
        let Some(inst) = sites.get(&v.id) else {
            break;
        };
        let Some(next) = rotate_var_low6_link(sites, inst) else {
            break;
        };
        v = next;
        if v.class == RegClass::Gpr64 {
            feed = v;
        }
    }
    (v, feed)
}

/// Does this operand mention any register aliasing RCX (RCX/ECX/CX/CL)?
fn rotate_var_operand_mentions_rcx(op: &X86ISelOperand) -> bool {
    use trust_cg_ir::x86_64_regs::{RCX, x86_regs_overlap};
    match op {
        X86ISelOperand::PReg(p) => x86_regs_overlap(*p, RCX),
        X86ISelOperand::MemAddr { base, .. } => rotate_var_operand_mentions_rcx(base),
        X86ISelOperand::SibMemAddr { base, index, .. } => {
            rotate_var_operand_mentions_rcx(base) || rotate_var_operand_mentions_rcx(index)
        }
        _ => false,
    }
}

/// Does this instruction read or write any part of RCX — explicitly (a PReg
/// operand, including inside a memory address) or implicitly (the CL-count
/// shift/rotate family)? Calls and other side-effecting instructions are
/// refused separately by the window purity predicate.
fn rotate_var_touches_rcx(inst: &X86ISelInst) -> bool {
    inst.operands.iter().any(rotate_var_operand_mentions_rcx)
        || matches!(
            inst.opcode,
            X86Opcode::ShlRR | X86Opcode::ShrRR | X86Opcode::SarRR | X86Opcode::RolRCl
        )
}

/// Window purity for a NON-member instruction inside the matched span:
/// pure register ALU (no branch/call/terminator/return/pseudo/memory/
/// side-effect), no flag READ (the rewrite deletes flag-writing members, so
/// an interleaved reader would observe a different flag state), and no RCX
/// contact (CL must carry the kept mov's value unmodified into the rotate).
fn rotate_var_window_ok(inst: &X86ISelInst) -> bool {
    imul_fuse_window_ok(inst) && !x86_reads_flags(inst.opcode) && !rotate_var_touches_rcx(inst)
}

/// VARIABLE-COUNT ROTATE IDIOM -> `RolRCl`. Collapses the bridge's
/// `bitmanip_rotate` expansion of `x.rotate_left(c)` with a RUNTIME count
///
/// ```text
///   eff   = AndRI(c, 63)          ; or any low-6-preserving chain (v2)
///   neg   = SubRR(z, eff')        ; z a uniquely-defined MovRI 0
///   compl = AndRI(neg, 63)
///   MovRR PReg(RCX) <- eff        ; kept (source may be rewritten, see below)
///   lo    = ShlRR [lo, x]
///   MovRR PReg(RCX) <- compl
///   hi    = ShrRR [hi, x]
///   d     = OrRR(lo, hi)          ==>  d = RolRCl [d, x]
/// ```
///
/// into the single `ROL r64, CL` (plus the kept CL mov), 64-bit `Gpr64` only.
///
/// SOUNDNESS. The value identity is the Stage-2 admission's own obligation
/// (`X86SourceOp::RotlVar`, TOTAL — no preconditions): for ANY CL value `c`,
/// `ROL64(x, c & 63)` IS `(x << (c & 63)) | (x >>u ((0 - (c & 63)) & 63))`.
/// The side conditions establish only that the eight instructions really are
/// that shape for ONE count value:
///
/// * the SHL's count is `CL1 & 63` (hardware CL masking) where `CL1` is the
///   value the kept mov loads;
/// * the SHR's count is `compl = (0 - (e & 63)) & 63` where `e` low-6-equals
///   `CL1`: both are chased through deterministic low-6-preserving single-def
///   chains ([`rotate_var_low6_walk`]) that must reach the SAME root, whose
///   def count is <= 1 (one static value; modular arithmetic gives
///   `(0 - e) & 63 == (0 - (e & 63)) & 63`);
/// * `lo`/`hi`/`neg`/`compl` are each single-def function-wide and used ONLY
///   inside the pattern (the rmw_fuse whole-function deadness precedent), so
///   the deletions leave no half-live state;
/// * `x` is not (re)defined inside the window — the rotate reads it at the
///   OR's position instead of the shifts';
/// * no non-member in the window touches RCX or reads flags, and THE FLAGS
///   ARE DEAD AT THE OR (`flags_dead_at`, as `rotate_idiom`): `OR` defines
///   SF/ZF/PF where `RolRCl` writes only CF/OF (and only when the count is
///   nonzero) — `post_ra_dataflow` models the rotate's real flag effect and
///   fails closed if this is ever wrong.
///
/// The kept CL mov's source is rewritten to the DEEPEST `Gpr64` link of the
/// count chain (v2): sound because every link preserves the low 6 bits, each
/// link is single-def, and the root's def dominates every chain read
/// (definite initialization at the ORIGINAL reads is the frontend's existing
/// obligation — the `fold_unique_const_into_imm_forms` argument). In p6 this
/// retires the entire 6-instruction masking chain via DCE and reproduces the
/// binary-patch ceiling (`mov %rdi,%rcx; rolq %cl,%r8`).
///
/// ADMISSION (owner doctrine, exceptionless): `RolRCl` is only constructed
/// when `admit(RolRCl)` — the injected, memoized
/// `reconstruction_discharges_valid` callback. No admission, no rewrite; the
/// (itself proof-covered) generic expansion stays.
fn rotate_var_idiom_run_on_block_with_maps(
    func: &mut X86ISelFunction,
    block_id: trust_cg_lower::instructions::Block,
    live_in: &FxHashMap<trust_cg_lower::instructions::Block, bool>,
    admit: ReconstructionAdmit,
    // Whole-function facts for the CURRENT state of `func`, owned by the
    // caller. This routine mutates `func` ONLY when it returns `true` (see
    // the `edits.is_empty()` early return below), so the caller may reuse one
    // build across consecutive blocks that collapsed nothing and rebuild the
    // instant one does — which is exactly what a per-block build would have
    // produced, and is what keeps the emitted bytes identical.
    maps: &RotateVarFnMaps,
) -> bool {
    use trust_cg_ir::x86_64_regs::RCX;

    let sites = &maps.sites;
    let fn_uses = &maps.fn_uses;
    let fn_defs = &maps.fn_defs;
    // Shared reborrow for the whole MATCH phase (the closure below needs the
    // function for `flags_dead_at` while `insts` is borrowed); the mutable
    // APPLY phase begins only after both borrows end.
    let func_ref: &X86ISelFunction = func;
    let Some(block) = func_ref.blocks.get(&block_id) else {
        return false;
    };
    let insts = &block.insts;

    struct Edit {
        or_idx: usize,
        d: VReg,
        x: VReg,
        mov1_idx: usize,
        feed: Option<VReg>, // Some => rewrite the kept CL mov's source
        doomed: Vec<usize>, // shl, shr, second CL mov, in-block neg/compl defs
    }
    let mut edits: Vec<Edit> = Vec::new();
    let mut consumed: FxHashSet<usize> = FxHashSet::default();

    let clean = |w: &X86ISelInst| w.proof_origin.is_none() && w.flags == w.opcode.default_flags();
    let single_def_single_use = |v: VReg| {
        fn_defs.get(&v).copied().unwrap_or(0) == 1 && fn_uses.get(&v).copied().unwrap_or(0) == 1
    };
    // Nearest RCX-touching instruction strictly before `pos`.
    let nearest_rcx_touch_before =
        |pos: usize| (0..pos).rev().find(|&j| rotate_var_touches_rcx(&insts[j]));
    // `MovRR PReg(RCX) <- vreg64` — the kept/deleted CL setup form.
    let cl_mov_src = |w: &X86ISelInst| -> Option<VReg> {
        if w.opcode != X86Opcode::MovRR || !clean(w) {
            return None;
        }
        match w.operands.as_slice() {
            [X86ISelOperand::PReg(p), X86ISelOperand::VReg(s)]
                if *p == RCX && s.class == RegClass::Gpr64 =>
            {
                Some(*s)
            }
            _ => None,
        }
    };

    for i in 0..insts.len() {
        let or = &insts[i];
        if or.opcode != X86Opcode::OrRR || or.operands.len() != 3 || !clean(or) {
            continue;
        }
        let [
            X86ISelOperand::VReg(d),
            X86ISelOperand::VReg(a),
            X86ISelOperand::VReg(b),
        ] = or.operands.as_slice()
        else {
            continue;
        };
        if d.class != RegClass::Gpr64 {
            continue;
        }
        let (d, a, b) = (*d, *a, *b);

        // OR commutes: try both operand orders for (lo, hi).
        let matched = [(a, b), (b, a)].into_iter().find_map(|(lo, hi)| {
            if lo.class != RegClass::Gpr64 || hi.class != RegClass::Gpr64 {
                return None;
            }
            // The shift defs, found at lo/hi's unique in-block def position.
            let shl_idx = (0..i).find(|&j| local_fold_defines_vreg(&insts[j], lo))?;
            let shr_idx = (0..i).find(|&j| local_fold_defines_vreg(&insts[j], hi))?;
            let shl = &insts[shl_idx];
            let shr = &insts[shr_idx];
            if shl.opcode != X86Opcode::ShlRR || shr.opcode != X86Opcode::ShrRR {
                return None;
            }
            if !clean(shl) || !clean(shr) {
                return None;
            }
            let (
                [X86ISelOperand::VReg(_), X86ISelOperand::VReg(x1)],
                [X86ISelOperand::VReg(_), X86ISelOperand::VReg(x2)],
            ) = (shl.operands.as_slice(), shr.operands.as_slice())
            else {
                return None;
            };
            if x1 != x2 || x1.class != RegClass::Gpr64 {
                return None;
            }
            let x = *x1;
            // lo/hi live ONLY inside the pattern (def = the shift, use = OR).
            if !single_def_single_use(lo) || !single_def_single_use(hi) {
                return None;
            }
            // CL setups: the NEAREST RCX contact above each shift must be the
            // MovRR-to-RCX form. The implicit CL read of ShlRR itself makes
            // an out-of-order match (mov2 before the SHL, SHR before the SHL,
            // a clobber between mov and shift) surface as a wrong-form
            // nearest hit — refused.
            let mov1_idx = nearest_rcx_touch_before(shl_idx)?;
            let f1 = cl_mov_src(&insts[mov1_idx])?;
            let mov2_idx = nearest_rcx_touch_before(shr_idx)?;
            if mov2_idx <= shl_idx || mov2_idx == mov1_idx {
                return None;
            }
            let compl = cl_mov_src(&insts[mov2_idx])?;
            // The complement chain: compl = AndRI(neg, 63) — the EXACT mask
            // 63 is load-bearing (`(0-e) & 31` is a DIFFERENT rotate count);
            // neg = SubRR(z, e) with z a uniquely-defined constant 0. Both
            // are function-wide single-def and consumed only here.
            if !single_def_single_use(compl) || fn_defs.get(&f1).copied().unwrap_or(0) > 1 {
                return None;
            }
            let compl_def = sites.get(&compl.id)?;
            if compl_def.opcode != X86Opcode::AndRI || !clean(compl_def) {
                return None;
            }
            let [
                X86ISelOperand::VReg(_),
                X86ISelOperand::VReg(neg),
                X86ISelOperand::Imm(63),
            ] = compl_def.operands.as_slice()
            else {
                return None;
            };
            let neg = *neg;
            if !single_def_single_use(neg) {
                return None;
            }
            let neg_def = sites.get(&neg.id)?;
            if neg_def.opcode != X86Opcode::SubRR || !clean(neg_def) {
                return None;
            }
            let [
                X86ISelOperand::VReg(_),
                X86ISelOperand::VReg(z),
                X86ISelOperand::VReg(e),
            ] = neg_def.operands.as_slice()
            else {
                return None;
            };
            if rotate_var_const_of(sites, *z) != Some(0) {
                return None;
            }
            // Count equality: the CL feed and the complement input must chase
            // to the SAME <=1-def root through low-6-preserving links.
            let (root_cl, feed) = rotate_var_low6_walk(sites, f1);
            let (root_e, _) = rotate_var_low6_walk(sites, *e);
            if root_cl != root_e || fn_defs.get(&root_cl).copied().unwrap_or(0) > 1 {
                return None;
            }
            // The proof admission gate (condition P): no admission, no
            // rewrite — the opcode is never constructed.
            if !admit(X86Opcode::RolRCl) {
                return None;
            }
            // In-block defs of neg/compl are pattern members and deleted
            // outright (DCE runs after this pass, but the rotate_idiom
            // deletion discipline keeps the block canonical immediately).
            let mut doomed = vec![shl_idx, shr_idx, mov2_idx];
            let mut members = vec![mov1_idx, shl_idx, mov2_idx, shr_idx, i];
            for v in [neg, compl] {
                if let Some(j) = (0..i).find(|&j| local_fold_defines_vreg(&insts[j], v)) {
                    doomed.push(j);
                    members.push(j);
                }
            }
            // Window discipline over every NON-member from the earliest
            // member to the OR: pure ALU, no flag read, no RCX contact, and
            // no (potential) def of any register the pattern reasons about.
            // The earliest member is the minimum over `members`, folded from
            // `mov1_idx` — itself a member — so the result is exactly
            // `min(members)` with no empty case to assert against.
            let scan_start = members.iter().copied().fold(mov1_idx, usize::min);
            let watched = [x, f1, feed, compl, neg, *e];
            for (k, w) in insts.iter().enumerate().take(i).skip(scan_start) {
                if members.contains(&k) {
                    continue;
                }
                if !rotate_var_window_ok(w) {
                    return None;
                }
                if watched.iter().any(|&v| local_fold_defines_vreg(w, v)) {
                    return None;
                }
            }
            // RCX after the pattern now holds the CL feed instead of compl.
            // Pre-RA nothing reads CL without a same-block setup mov (the
            // isel emits the mov/shift pair adjacently, and call arg regs are
            // populated by their own arg-setup movs), but enforce it anyway:
            // walking forward from the OR, any RCX contact before a definite
            // full-RCX overwrite refuses the match. Block end / terminator is
            // safe — pre-RA physical CL uses are strictly block-local.
            for w in &insts[i + 1..] {
                let full_rcx_overwrite = matches!(
                    w.opcode,
                    X86Opcode::MovRR | X86Opcode::MovRR32 | X86Opcode::MovRI
                ) && matches!(
                    w.operands.first(),
                    Some(X86ISelOperand::PReg(p))
                        if trust_cg_ir::x86_64_regs::x86_regs_overlap(*p, RCX)
                );
                if full_rcx_overwrite {
                    break;
                }
                if rotate_var_touches_rcx(w) {
                    return None;
                }
            }
            // Flags must be dead at the OR (identical infra to rotate_idiom).
            if !flags_dead_at(func_ref, live_in, block_id, i) {
                return None;
            }
            if members.iter().any(|j| consumed.contains(j)) {
                return None;
            }
            consumed.extend(members.iter().copied());
            Some(Edit {
                or_idx: i,
                d,
                x,
                mov1_idx,
                feed: (feed != f1).then_some(feed),
                doomed,
            })
        });
        if let Some(edit) = matched {
            edits.push(edit);
        }
    }

    if edits.is_empty() {
        return false;
    }

    if crate::env_lock::var_os("TCG_X86_ROTATE_VAR_LOG").is_some() {
        eprintln!(
            "x86-rotate-var-idiom: collapsed {} variable rotate(s) in `{}` block #{:?}",
            edits.len(),
            func.name,
            block_id.0,
        );
    }

    // Rewrite the ORs (and CL feeds) in place, then DELETE the dead members —
    // indices stay valid because deletion happens strictly after every
    // in-place write, in descending order.
    //
    // INVARIANT (panic audit, class A): `func.blocks.get(&block_id)` returned
    // `Some` at the top of this function (the `else { return false }` guard),
    // and between that guard and here `func` is only ever read — the shared
    // `func_ref` reborrow for the match phase and `func.name` in the log line
    // — so no block was inserted or removed and the same key is still
    // present. The lookup cannot be hoisted into the guard itself: the match
    // closure needs the WHOLE function immutably (`flags_dead_at(func_ref,
    // ..)`) while `insts` is borrowed, which a live `&mut` block would forbid.
    let block = func.blocks.get_mut(&block_id).expect("block existed above");
    let mut doomed: Vec<usize> = Vec::new();
    for edit in edits {
        block.insts[edit.or_idx] = X86ISelInst::new(
            X86Opcode::RolRCl,
            vec![X86ISelOperand::VReg(edit.d), X86ISelOperand::VReg(edit.x)],
        );
        if let Some(feed) = edit.feed {
            block.insts[edit.mov1_idx].operands[1] = X86ISelOperand::VReg(feed);
        }
        doomed.extend(edit.doomed);
    }
    doomed.sort_unstable();
    for idx in doomed.into_iter().rev() {
        block.insts.remove(idx);
    }
    true
}

/// Build the whole-function maps and collapse one block. Equivalent to
/// [`rotate_var_idiom_run_on_block_with_maps`] with a freshly built map set;
/// kept for the unit tests, which exercise one block of a fixed function.
#[cfg(test)]
fn rotate_var_idiom_run_on_block(
    func: &mut X86ISelFunction,
    block_id: trust_cg_lower::instructions::Block,
    live_in: &FxHashMap<trust_cg_lower::instructions::Block, bool>,
    admit: ReconstructionAdmit,
) -> bool {
    let maps = RotateVarFnMaps::build(func);
    rotate_var_idiom_run_on_block_with_maps(func, block_id, live_in, admit, &maps)
}

fn and_pow2_bt_branch_run_on_block(
    func: &mut X86ISelFunction,
    block_id: trust_cg_lower::instructions::Block,
) -> bool {
    let Some(block) = func.blocks.get(&block_id) else {
        return false;
    };
    let insts = &block.insts;

    let mut edits: Vec<AndPow2BtEdit> = Vec::new();
    let mut consumed: FxHashSet<usize> = FxHashSet::default();

    let mut i = 0;
    while i + 2 < insts.len() {
        if consumed.contains(&i) {
            i += 1;
            continue;
        }
        if let Some(edit) = try_and_pow2_bt_branch(insts, i) {
            // Cross-block liveness guard: refuse if %and_dst is mentioned in
            // any other block of the function. This is conservative but
            // correct - the rewrite erases the AND's write-back, so any
            // out-of-block reader would observe the pre-AND value instead of
            // the and-result.
            let and_dst = match func.blocks[&block_id].insts[edit.and_idx].operands.first() {
                Some(X86ISelOperand::VReg(v)) => *v,
                _ => {
                    i += 1;
                    continue;
                }
            };
            let mut escapes = false;
            for (other_id, other_block) in &func.blocks {
                if *other_id == block_id {
                    continue;
                }
                if other_block
                    .insts
                    .iter()
                    .any(|inst| instruction_mentions_vreg(inst, and_dst))
                {
                    escapes = true;
                    break;
                }
            }
            if escapes {
                i += 1;
                continue;
            }
            consumed.insert(edit.and_idx);
            consumed.insert(edit.cmp_idx);
            consumed.insert(edit.jcc_idx);
            // Advance past the Jcc so we do not match into the rewritten window.
            i = edit.jcc_idx + 1;
            edits.push(edit);
        } else {
            i += 1;
        }
    }

    if edits.is_empty() {
        return false;
    }

    // Apply edits in reverse order so earlier indices remain valid.
    let block = func.blocks.get_mut(&block_id).expect("block existed above");
    for edit in edits.into_iter().rev() {
        let and_inst = block.insts[edit.and_idx].clone();
        let jcc_inst = block.insts[edit.jcc_idx].clone();

        // Build BtRI %bt_src, #k with proof_origin inherited from the AND.
        let mut bt = X86ISelInst::new(
            X86Opcode::BtRI,
            vec![
                X86ISelOperand::VReg(edit.bt_src),
                X86ISelOperand::Imm(edit.bit_k as i64),
            ],
        );
        bt.proof_origin = and_inst.proof_origin;

        // Build Jcc <new_cc>, target with proof_origin inherited from the
        // original Jcc.
        let mut new_jcc = X86ISelInst::new(
            X86Opcode::Jcc,
            vec![
                X86ISelOperand::CondCode(edit.new_cc),
                X86ISelOperand::Block(edit.target),
            ],
        );
        new_jcc.proof_origin = jcc_inst.proof_origin;

        // Replace [AND, CMP, JCC] with [BT, JCC]. Remove cmp and jcc first
        // (largest indices), then overwrite AND with BT, then insert the new
        // Jcc just after.
        block.insts.remove(edit.jcc_idx);
        block.insts.remove(edit.cmp_idx);
        block.insts[edit.and_idx] = bt;
        block.insts.insert(edit.and_idx + 1, new_jcc);
    }

    true
}

#[derive(Debug)]
struct AndPow2BtEdit {
    and_idx: usize,
    cmp_idx: usize,
    jcc_idx: usize,
    bt_src: VReg,
    bit_k: u32,
    new_cc: trust_cg_ir::X86CondCode,
    target: trust_cg_lower::instructions::Block,
}

fn try_and_pow2_bt_branch(insts: &[X86ISelInst], and_idx: usize) -> Option<AndPow2BtEdit> {
    use trust_cg_ir::X86CondCode;

    let and_inst = insts.get(and_idx)?;
    if and_inst.opcode != X86Opcode::AndRI {
        return None;
    }
    // (g) AndRI must have default flags (no foreign side-effects) and not
    // touch memory.
    if and_inst.flags != X86Opcode::AndRI.default_flags() {
        return None;
    }
    let and_flags = and_inst.flags;
    if and_flags.reads_memory()
        || and_flags.writes_memory()
        || and_flags.is_pseudo()
        || and_flags.is_call()
        || and_flags.is_branch()
        || and_flags.is_terminator()
        || and_flags.is_return()
    {
        return None;
    }

    // Parse AndRI operand shape. Accept either two-operand `[%dst, Imm]` or
    // three-operand `[%dst, %src, Imm]`. In the two-op form, bt_src == dst.
    let (and_dst, bt_src, imm) = match and_inst.operands.as_slice() {
        [X86ISelOperand::VReg(dst), X86ISelOperand::Imm(imm)] if is_supported_gpr(*dst) => {
            (*dst, *dst, *imm)
        }
        [
            X86ISelOperand::VReg(dst),
            X86ISelOperand::VReg(src),
            X86ISelOperand::Imm(imm),
        ] if same_supported_class(*dst, *src) => (*dst, *src, *imm),
        _ => return None,
    };

    // (a) Immediate must be a positive power of two.
    if imm <= 0 {
        return None;
    }
    if (imm as u64).count_ones() != 1 {
        return None;
    }
    let bit_k = (imm as u64).trailing_zeros();
    // Bit index must fit in the source register class. BT r64, imm8 is
    // encoded with imm8 mod 64; we refuse if the bit index would not match
    // the AND's interpretation. For 32-bit AND, k must be 0..=31.
    match and_dst.class {
        RegClass::Gpr64 => {
            if bit_k > 63 {
                return None;
            }
        }
        RegClass::Gpr32 => {
            if bit_k > 31 {
                return None;
            }
        }
        _ => return None,
    }

    // (b) CmpRI must immediately follow.
    let cmp_idx = and_idx + 1;
    let cmp_inst = insts.get(cmp_idx)?;
    if !matches!(cmp_inst.opcode, X86Opcode::CmpRI | X86Opcode::CmpRI8) {
        return None;
    }
    if cmp_inst.flags != cmp_inst.opcode.default_flags() {
        return None;
    }
    let cmp_flags = cmp_inst.flags;
    if cmp_flags.reads_memory() || cmp_flags.writes_memory() || cmp_flags.is_pseudo() {
        return None;
    }
    // (c) CmpRI must compare %and_dst against 0.
    match cmp_inst.operands.as_slice() {
        [X86ISelOperand::VReg(cmp_reg), X86ISelOperand::Imm(0)]
            if *cmp_reg == and_dst && is_supported_gpr(*cmp_reg) => {}
        _ => return None,
    }

    // (b cont.) Jcc must immediately follow.
    let jcc_idx = cmp_idx + 1;
    let jcc_inst = insts.get(jcc_idx)?;
    if jcc_inst.opcode != X86Opcode::Jcc {
        return None;
    }
    if jcc_inst.flags != X86Opcode::Jcc.default_flags() {
        return None;
    }
    // (d) Cond code must be E or NE. Decode operand shape `[CondCode, Block]`.
    let (orig_cc, target) = match jcc_inst.operands.as_slice() {
        [X86ISelOperand::CondCode(cc), X86ISelOperand::Block(blk)] => (*cc, *blk),
        _ => return None,
    };
    let new_cc = match orig_cc {
        // Jcc E (ZF=1) <=> dst == 0 <=> bit k clear <=> CF=0 <=> Jcc AE.
        X86CondCode::E => X86CondCode::AE,
        // Jcc NE (ZF=0) <=> dst != 0 <=> bit k set <=> CF=1 <=> Jcc B.
        X86CondCode::NE => X86CondCode::B,
        _ => return None,
    };

    // (e) intentionally elided - subsumed by (b) and (f). (This matcher used
    // to take a block-wide use-count map for that condition and never read it;
    // the parameter and the `vreg_uses_in_block` build that fed it were
    // removed 2026-08-31 without touching any side condition.)

    // (f) AndRI's destination must be dead after the Jcc - no later block-local
    // instruction mentions %and_dst.
    for later in &insts[jcc_idx + 1..] {
        if instruction_mentions_vreg(later, and_dst) {
            return None;
        }
    }
    // For the two-op AndRI form, %and_dst was also the source register. Any
    // prior reader of %and_dst saw the original value, which is fine because
    // it precedes the AndRI we are erasing. But any prior write to %and_dst
    // outside the canonical RMW chain doesn't matter either: the only way to
    // observe the AND's destruction is to read %and_dst AFTER the AND, and
    // (f) forbids that within the block. Cross-block liveness is handled by
    // the caller (see `and_pow2_bt_branch_run_on_block`), which checks that
    // no other block in the function reads %and_dst.

    // In the two-op form `bt_src == and_dst`. The two-op AndRI reads %dst,
    // erasing the AND leaves %dst at its pre-AND value, which is what BT
    // needs. In the three-op form, %src is unchanged by the AND, so reading
    // it from BT is unambiguous; we still require %src to be alive at the BT
    // point (it is, since the AND read it and we are replacing the AND
    // in-place).

    Some(AndPow2BtEdit {
        and_idx,
        cmp_idx,
        jcc_idx,
        bt_src,
        bit_k,
        new_cc,
        target,
    })
}

/// Function-wide vreg USE set for the zero-idiom gate (same convention as
/// DCE's `collect_used_vregs`: operand 0 of a value producer is a def, not a
/// use, except for tied first operands; addressing regs count).
fn peephole_function_use_set(func: &X86ISelFunction) -> FxHashSet<VReg> {
    let mut used = FxHashSet::default();
    for block_id in &func.block_order {
        let Some(block) = func.blocks.get(block_id) else {
            continue;
        };
        for inst in &block.insts {
            let has_def = crate::effects::x86_produces_value(inst.opcode);
            for (index, operand) in inst.operands.iter().enumerate() {
                if index == 0 && has_def && !dce_style_first_operand_is_use(inst) {
                    continue;
                }
                collect_peephole_operand_vregs(operand, &mut used);
            }
        }
    }
    used
}

/// Tied-first-operand test for the use-set above: the immediate/RM ALU
/// family in tied FORM, plus 2-operand tied RR ALU. Over-approximating
/// (counting a def as a use) is safe here — it only makes the gate DECLINE
/// fewer rewrites, and declining is itself a no-op.
fn dce_style_first_operand_is_use(inst: &X86ISelInst) -> bool {
    use X86Opcode::*;
    matches!(
        inst.opcode,
        Neg | Not
            | Inc
            | Dec
            | AddRI
            | SubRI
            | AndRI
            | OrRI
            | XorRI
            | AddRM
            | SubRM
            | ImulRM
            | ImulRMSib
            | ShlRI
            | ShrRI
            | SarRI
            | ShlRR
            | ShrRR
            | SarRR
            // Rotate-by-CL: same tied [dst, src] shape as the CL shifts.
            | RolRCl
    ) || (matches!(inst.opcode, AddRR | SubRR | ImulRR | AndRR | OrRR | XorRR)
        && inst.operands.len() == 2)
}

fn collect_peephole_operand_vregs(operand: &X86ISelOperand, used: &mut FxHashSet<VReg>) {
    match operand {
        X86ISelOperand::VReg(vreg) => {
            used.insert(*vreg);
        }
        X86ISelOperand::MemAddr { base, .. } => collect_peephole_operand_vregs(base, used),
        X86ISelOperand::SibMemAddr { base, index, .. } => {
            collect_peephole_operand_vregs(base, used);
            collect_peephole_operand_vregs(index, used);
        }
        _ => {}
    }
}

#[cfg(test)]
fn simplify_inst(insts: &[X86ISelInst], index: usize) -> Option<PeepholeEdit> {
    // Fail-closed const-multiply admission, exactly like `X86Peephole::default`:
    // the existing single-instruction tests must observe no behaviour change.
    simplify_inst_gated(insts, index, None, |_, _, _| false, false)
}

/// [`simplify_inst`] with the const-multiply shift reduction ADMITTED — the
/// in-test stand-in for the proof-backed callback wired in the codegen
/// pipeline. Keeps the admission an explicit, visible argument at every call
/// site instead of a global.
#[cfg(test)]
fn simplify_inst_constmul_admitted(insts: &[X86ISelInst], index: usize) -> Option<PeepholeEdit> {
    simplify_inst_gated(insts, index, None, |_, _, _| true, false)
}

/// [`simplify_inst_constmul_admitted`] in a certificate-free compile: the
/// doubling-LEA arm and the store-passing IMUL flags scan are enabled too.
#[cfg(test)]
fn simplify_inst_constmul_admitted_certificate_free(
    insts: &[X86ISelInst],
    index: usize,
) -> Option<PeepholeEdit> {
    simplify_inst_gated(insts, index, None, |_, _, _| true, true)
}

// ---------------------------------------------------------------------------
// RM-fusion (X9 slice 3)
//
//   MovRMSib t, [sib]        MovRR     d, a          (3-operand form; the
//   ImulRR   d, a, t    ->   ImulRMSib d, [sib]       2-op tied `ImulRR d, t`
//                                                      fuses to the bare
//                                                      `ImulRMSib d, [sib]`)
// ---------------------------------------------------------------------------
//
// Folds a 64-bit load whose destination's ONLY consumption is the next
// multiply into the multiply's memory operand (`IMUL r64, r/m64`). The
// base+disp `MovRM` load fuses to `ImulRM` identically.
//
// HAND-PROOF (semantic equivalence): the fused `ImulRMSib d, [ea]` computes
// `d := factor * load64(ea)` where `factor` is `a`'s value at the multiply.
// The unfused pair computed `t := load64(ea)` at the LOAD's position, then
// `d := a * t`. Equality needs exactly: (1) `load64(ea)` yields the same
// value at both positions — guaranteed because the window between load and
// multiply admits NO memory-writing instruction, no call, and no other
// memory op at all (condition W below), and the EA registers (base/index)
// have no defs in the window (condition E); (2) the load's movement past the
// window cannot change observable behavior — the window contains no branch /
// terminator / pseudo (trap carriers included), so no path leaves between
// them and no trap can fire between them; both orders fault identically or
// not at all (same EA, same memory state); (3) `t`'s value is consumed ONLY
// by the fused multiply — `t` is locally dead after it (condition D, the
// per-def window rule: a later same-block full redef of `t` with no use and
// no control flow between). RFLAGS: `ImulRR` and `ImulRMSib` write the
// identical mul-family flag set at the same program point; nothing else in
// the rewrite touches flags.
//
// SIDE CONDITIONS (all fail-closed):
//   A. Anchor: `ImulRR` with default flags, no proof_origin, all-Gpr64
//      operands; forms `[d, a, t]` / `[d, t, a]` (commutative) or tied
//      `[d, t]` with `t != d`. The non-load factor must NOT be `t` itself
//      (both factors from one load would need the value twice).
//   B. Load: the NEAREST prior def of `t` in the block is a `MovRMSib`
//      (-> ImulRMSib) or full-width `MovRM` (-> ImulRM) with default flags
//      and no proof_origin, defining exactly `t`.
//   W. Window (load, imul): every inst is pure register ALU — no
//      reads_memory / writes_memory / call / branch / terminator / return /
//      pseudo / xchg-family.
//   E. No def of the load's base/index vreg ids (class-blind) in the window,
//      and none of the EA regs may BE `t` (the load overwrites t; the fused
//      form must read the pre-load EA regs — refuse `base.id == t.id` etc.).
//   D. `t` locally dead after the multiply (same rule as the per-def DCE
//      tier: later full redef in-block, no use / branch / call / pseudo
//      between). The redef scan is class-blind on the id (narrow-alias).
// ---------------------------------------------------------------------------

/// The `AddRR` arm of RM fusion's opt-out, set from a tracked compiler option.
static ADD_FUSE: std::sync::OnceLock<bool> = std::sync::OnceLock::new();

/// Install the `AddRR` arm of RM fusion's opt-out from a TRACKED compiler option
/// (`-Ztrust-ir-cg-args=no-x86-add-fuse`). DEFAULT ON.
pub fn set_add_fuse_disabled(disabled: bool) -> bool {
    match ADD_FUSE.set(disabled) {
        Ok(()) => true,
        Err(requested) => ADD_FUSE.get() == Some(&requested),
    }
}

fn add_fuse_enabled() -> bool {
    if let Some(disabled) = ADD_FUSE.get() {
        return !*disabled;
    }
    !crate::tcg_env_flag("TCG_NO_X86_ADD_FUSE")
}

/// The load kinds the fusion accepts, mapped to their fused opcode. Every EA
/// component must be a VReg — a PReg (or other) base/index would make
/// condition E's redef scan vacuously pass over an address the pass cannot
/// track (adversarial-review FAIL_CLOSED_GAP); refuse those shapes outright.
/// The fused RM opcode for an `(anchor, load)` pair, or `None` when that
/// combination has no RM form.
///
/// `ImulRR` has both a plain and a SIB RM form. `AddRR` has only the plain
/// `AddRM` — there is no `AddRMSib` in the opcode set — so a SIB-formed load
/// feeding an add is refused rather than mis-spelled.
fn rm_fuse_opcode(anchor: X86Opcode, load: X86Opcode) -> Option<X86Opcode> {
    match (anchor, load) {
        (X86Opcode::ImulRR, X86Opcode::MovRM) => Some(X86Opcode::ImulRM),
        (X86Opcode::ImulRR, X86Opcode::MovRMSib) => Some(X86Opcode::ImulRMSib),
        (X86Opcode::AddRR, X86Opcode::MovRM) => Some(X86Opcode::AddRM),
        _ => None,
    }
}

fn imul_fuse_load_kind(
    inst: &X86ISelInst,
    anchor: X86Opcode,
) -> Option<(VReg, X86ISelOperand, X86Opcode)> {
    if inst.proof_origin.is_some() || inst.flags != inst.opcode.default_flags() {
        return None;
    }
    match inst.opcode {
        X86Opcode::MovRMSib => match inst.operands.as_slice() {
            [
                X86ISelOperand::VReg(t),
                sib @ X86ISelOperand::SibMemAddr { base, index, .. },
            ] if t.class == RegClass::Gpr64
                && matches!(base.as_ref(), X86ISelOperand::VReg(b) if b.class == RegClass::Gpr64)
                && matches!(index.as_ref(), X86ISelOperand::VReg(i) if i.class == RegClass::Gpr64) =>
            {
                Some((
                    *t,
                    sib.clone(),
                    rm_fuse_opcode(anchor, X86Opcode::MovRMSib)?,
                ))
            }
            _ => None,
        },
        X86Opcode::MovRM => match inst.operands.as_slice() {
            [
                X86ISelOperand::VReg(t),
                mem @ X86ISelOperand::MemAddr { base, .. },
            ] if t.class == RegClass::Gpr64
                && matches!(base.as_ref(), X86ISelOperand::VReg(b) if b.class == RegClass::Gpr64) =>
            {
                Some((*t, mem.clone(), rm_fuse_opcode(anchor, X86Opcode::MovRM)?))
            }
            _ => None,
        },
        _ => None,
    }
}

/// VReg ids the memory operand's EA reads (base + optional index).
fn imul_fuse_ea_reg_ids(mem: &X86ISelOperand) -> Vec<u32> {
    let mut ids = Vec::new();
    match mem {
        X86ISelOperand::MemAddr { base, .. } => {
            if let X86ISelOperand::VReg(b) = base.as_ref() {
                ids.push(b.id);
            }
        }
        X86ISelOperand::SibMemAddr { base, index, .. } => {
            if let X86ISelOperand::VReg(b) = base.as_ref() {
                ids.push(b.id);
            }
            if let X86ISelOperand::VReg(i) = index.as_ref() {
                ids.push(i.id);
            }
        }
        _ => {}
    }
    ids
}

/// Window purity for condition W: pure register ALU only.
fn imul_fuse_window_ok(inst: &X86ISelInst) -> bool {
    let f = inst.flags;
    if f.is_branch()
        || f.is_call()
        || f.is_terminator()
        || f.is_return()
        || f.is_pseudo()
        || f.reads_memory()
        || f.writes_memory()
        || f.has_side_effects()
    {
        // HAS_SIDE_EFFECTS also excludes the compare family and the whole
        // exchange family — stricter than needed (compares are harmless),
        // but the b05 window is empty and fail-closed costs nothing.
        return false;
    }
    true
}

/// `t` locally dead after `j`: later full redef of the id in-block with no
/// use / control flow / pseudo between. The redef acceptance SHARES the
/// per-def DCE tier's hardened predicates (`full_unconditional_overwrite` +
/// `redef_reads_operand0`) rather than re-deriving them — the adversarial
/// review caught this function's first version re-admitting exactly the
/// conditional-write (Cmovcc) and tied-read (Inc/2-op AddRI/...) shadow
/// classes those predicates exist to exclude.
fn imul_fuse_t_dead_after(insts: &[X86ISelInst], j: usize, t: VReg) -> bool {
    let mut k = j + 1;
    while k < insts.len() {
        let w = &insts[k];
        let f = w.flags;
        if f.is_branch() || f.is_call() || f.is_terminator() || f.is_return() || f.is_pseudo() {
            return false;
        }
        // Any mention of the id (any class) in a USE position keeps it; an
        // operand-0 def of the same id at the same class ends the range.
        let defines = crate::effects::x86_produces_value(w.opcode)
            && matches!(w.operands.first(), Some(X86ISelOperand::VReg(d)) if *d == t);
        if defines {
            // The ending redef must be a FULL, UNCONDITIONAL overwrite that
            // does not itself read t — Cmovcc's not-taken lane and every
            // tied form KEEP the loaded value alive.
            if !crate::x86_dce::full_unconditional_overwrite(w.opcode)
                || crate::x86_dce::redef_reads_operand0(w)
            {
                return false;
            }
            return !w
                .operands
                .iter()
                .skip(1)
                .any(|op| operand_mentions_vreg_id_flat(op, t.id));
        }
        if w.operands
            .iter()
            .any(|op| operand_mentions_vreg_id_flat(op, t.id))
        {
            return false;
        }
        k += 1;
    }
    false
}

/// Whether `op` mentions a VReg with register id `id`, at any class: the
/// question `imul_fuse_t_dead_after` asks of each instruction, answered
/// without collecting the instruction's mentions into a set first. Walks the
/// operand exactly as [`collect_operand_mentions_flat`] does.
fn operand_mentions_vreg_id_flat(op: &X86ISelOperand, id: u32) -> bool {
    match op {
        X86ISelOperand::VReg(v) => v.id == id,
        X86ISelOperand::MemAddr { base, .. } => operand_mentions_vreg_id_flat(base, id),
        X86ISelOperand::SibMemAddr { base, index, .. } => {
            operand_mentions_vreg_id_flat(base, id) || operand_mentions_vreg_id_flat(index, id)
        }
        _ => false,
    }
}

fn collect_operand_mentions_flat(op: &X86ISelOperand, out: &mut FxHashSet<VReg>) {
    match op {
        X86ISelOperand::VReg(v) => {
            out.insert(*v);
        }
        X86ISelOperand::MemAddr { base, .. } => collect_operand_mentions_flat(base, out),
        X86ISelOperand::SibMemAddr { base, index, .. } => {
            collect_operand_mentions_flat(base, out);
            collect_operand_mentions_flat(index, out);
        }
        _ => {}
    }
}

/// Run the RM fusion on one block. Returns whether anything changed.
fn imul_fuse_run_on_block(
    func: &mut X86ISelFunction,
    block_id: trust_cg_lower::instructions::Block,
) -> bool {
    let Some(block) = func.blocks.get(&block_id) else {
        return false;
    };
    let insts = &block.insts;

    struct Fusion {
        load_idx: usize,
        imul_idx: usize,
        replacement: Vec<X86ISelInst>,
    }
    let mut fusions: Vec<Fusion> = Vec::new();
    let mut consumed: FxHashSet<usize> = FxHashSet::default();

    for j in 0..insts.len() {
        let anchor = &insts[j];
        // ImulRR was the original anchor; AddRR is the same shape with the same
        // commutativity and the same flag semantics (both write the full flag set
        // at the position the fused op keeps them at), and `AddRM` is a
        // first-class opcode — encoded, covered by the coverage gate, modelled by
        // the post-RA flag dataflow, and carrying labelled addressing proofs. It
        // was simply never CREATED by any peephole, which is why
        // `h3_box_leak`'s `mov (%rax),%rcx ; add %rcx,%r14` stayed two
        // instructions where LLVM emits one `add (%r11),%rdi`.
        let anchor_ok = match anchor.opcode {
            X86Opcode::ImulRR => true,
            X86Opcode::AddRR => add_fuse_enabled(),
            _ => false,
        };
        if !anchor_ok
            || anchor.proof_origin.is_some()
            || anchor.flags != anchor.opcode.default_flags()
        {
            continue;
        }
        let anchor_opcode = anchor.opcode;
        let g64 = |r: &VReg| r.class == RegClass::Gpr64;
        // Decode the anchor form: (d, other_factor, t_candidates).
        let (d, factors): (VReg, Vec<VReg>) = match anchor.operands.as_slice() {
            [X86ISelOperand::VReg(d), X86ISelOperand::VReg(s)] if g64(d) && g64(s) && s != d => {
                (*d, vec![*s])
            }
            [
                X86ISelOperand::VReg(d),
                X86ISelOperand::VReg(s1),
                X86ISelOperand::VReg(s2),
            ] if g64(d) && g64(s1) && g64(s2) => (*d, vec![*s1, *s2]),
            _ => continue,
        };
        let tied = anchor.operands.len() == 2;

        // Try each factor as the load result `t` (commutative).
        'factors: for (fi, &t) in factors.iter().enumerate() {
            // The OTHER factor (3-op) must not be t itself.
            let other: Option<VReg> = if tied {
                None
            } else {
                let o = factors[1 - fi];
                if o.id == t.id {
                    continue;
                }
                Some(o)
            };
            // Find t's nearest def above j.
            let Some(i) = (0..j)
                .rev()
                .find(|&k| local_fold_defines_vreg(&insts[k], t))
            else {
                continue;
            };
            if consumed.contains(&i) || consumed.contains(&j) {
                continue;
            }
            let Some((lt, mem, fused_opcode)) = imul_fuse_load_kind(&insts[i], anchor_opcode)
            else {
                continue;
            };
            if lt != t {
                continue;
            }
            // Condition E: EA regs unredefined in the window; none may be t
            // (the load overwrites t) and none may be d (the emitted
            // `MovRR d, a` — or the fused write itself — must not clobber an
            // address register the fused load still reads; adversarial-review
            // MISCOMPILE class, refused in ALL forms for simplicity).
            let ea_ids = imul_fuse_ea_reg_ids(&mem);
            if ea_ids.iter().any(|&id| id == t.id || id == d.id) {
                continue;
            }
            // Condition W + E over the window (i, j), plus: NO mention of t
            // anywhere in the window — a window reader still consumes the
            // loaded value, and deleting the load would hand it the stale
            // pre-load value (adversarial-review MISCOMPILE class; this is
            // what makes the hand-proof's "consumed ONLY by the fused
            // multiply" premise actually checked).
            for w in &insts[i + 1..j] {
                if !imul_fuse_window_ok(w) {
                    continue 'factors;
                }
                let mut w_mentions = FxHashSet::default();
                for op in &w.operands {
                    collect_operand_mentions_flat(op, &mut w_mentions);
                }
                if w_mentions.iter().any(|m| m.id == t.id) {
                    continue 'factors;
                }
                if ea_ids
                    .iter()
                    .any(|&id| local_fold_defines_vreg(w, VReg::new(id, RegClass::Gpr64)))
                {
                    continue 'factors;
                }
            }
            // Condition D: t locally dead after j.
            if !imul_fuse_t_dead_after(insts, j, t) {
                continue;
            }
            // Build the replacement.
            let mut replacement = Vec::new();
            if let Some(a) = other {
                if a != d {
                    replacement.push(X86ISelInst::new(
                        X86Opcode::MovRR,
                        vec![X86ISelOperand::VReg(d), X86ISelOperand::VReg(a)],
                    ));
                }
                // d == a: the tied ImulRMSib below already reads d.
            } else {
                // Tied anchor [d, t]: d already holds the register factor.
            }
            replacement.push(X86ISelInst::new(
                fused_opcode,
                vec![X86ISelOperand::VReg(d), mem.clone()],
            ));
            consumed.insert(i);
            consumed.insert(j);
            fusions.push(Fusion {
                load_idx: i,
                imul_idx: j,
                replacement,
            });
            break;
        }
    }

    if fusions.is_empty() {
        return false;
    }

    // Rebuild the block: delete each load, splice each replacement at the
    // multiply's position.
    let mut delete: FxHashSet<usize> = FxHashSet::default();
    let mut replace: FxHashMap<usize, Vec<X86ISelInst>> = FxHashMap::default();
    for f in fusions {
        delete.insert(f.load_idx);
        replace.insert(f.imul_idx, f.replacement);
    }
    let block = func.blocks.get_mut(&block_id).expect("block existed above");
    let old = std::mem::take(&mut block.insts);
    let mut rebuilt = Vec::with_capacity(old.len());
    for (idx, inst) in old.into_iter().enumerate() {
        if delete.contains(&idx) {
            continue;
        }
        if let Some(mut rep) = replace.remove(&idx) {
            // Preserve the multiply's proof_origin (None by condition A, but
            // keep the plumbing honest).
            for r in &mut rep {
                r.proof_origin = inst.proof_origin;
            }
            rebuilt.extend(rep);
            continue;
        }
        rebuilt.push(inst);
    }
    block.insts = rebuilt;
    true
}

// ---------------------------------------------------------------------------
// Memory-destination RMW fusion (b1 RMW arc Stage 2; DEFAULT-ON,
// `TCG_NO_X86_RMW_FUSE` opts out; ADMISSION-GATED on the injected proof
// callback)
//
//   i: MovRMSib t, [sib]         (or full-width MovRM t, [mem] -> base form)
//   j: OpRR d, t, s | OpRR d, s, t | tied OpRR d, t   (Op in {Xor, Add};
//                                    tied form: the register operand is d's
//                                    own pre-value, i.e. s := d)
//   k: MovMRSib [sib'], d        (or MovMR) with sib' STRUCTURALLY IDENTICAL
//                                 to sib
//     =>  delete i and j; replace k with:  OpMRSib [sib], s  (or OpMR)
// ---------------------------------------------------------------------------
//
// HAND-PROOF (semantic equivalence): the fused `OpMRSib [ea], s` at k
// computes `mem[ea] := load64(ea) Op s` and writes Op's flags there. The
// unfused triple computed `t := load64(ea)` at i, `d := t Op s` at j (writing
// Op's flags at j), and `mem[ea] := d` at k. Equality needs exactly:
//   (1) `load64(ea)` yields the same value at i and k — the windows (i,j) and
//       (j,k) admit NO memory-writing instruction, no call, and no other
//       memory op at all (W1/W2), and the EA registers have no defs in either
//       window (E); the two memory operands are STRUCTURALLY IDENTICAL VReg
//       terms, so same registers + same values = same address. Structural EA
//       identity IS the entire alias argument — no may-alias reasoning exists
//       or is needed.
//   (2) `s` has the same value at j and k — no def of s in the windows (W).
//       (Tied form: s is d itself, whose only def in [i, k] WAS j — deleted.)
//   (3) the values of `t` and `d` are consumed ONLY inside the triple — `t`
//       locally dead after j and `d` locally dead after k (D, the shared
//       per-def window machinery; the fused form defines no register).
//   (4) RFLAGS: Op's flag-write MOVES from j down to k. This is the NOVEL
//       hazard relative to imul_fuse (which moved the flag-neutral load while
//       its flag-writing anchor stayed put): the window (j,k) must contain no
//       flag-READER (it would observe Op's flags in the unfused stream and
//       stale flags in the fused one) and no flag-WRITER (its flags would
//       survive at block exit in the unfused stream but be overwritten by the
//       moved Op-write in the fused one). With W2 empty of both, the exit
//       flag VALUES are identical: same Op over the same operand values, and
//       nothing between j and k touches or observes RFLAGS. No flags-deadness
//       analysis is needed at all.
//   (5) Fault equivalence: same EA (1), no control flow / pseudos in the
//       windows — the fused RMW faults iff the load/store pair did.
//
// SIDE CONDITIONS (all fail-closed, extending imul_fuse's A/B/W/E/D):
//   A. Anchor j: `XorRR`/`AddRR` with default flags, no proof_origin,
//      all-Gpr64 VReg operands; forms `[d, t, s]` / `[d, s, t]` (commutative)
//      or tied `[d, t]` (s := d). `s != t` (the value would be needed twice
//      but the load is deleted); `t != d` (fail-closed; the deadness scan
//      cannot separate the two uses of one id).
//   B. Load i: the NEAREST prior def of `t`, a `MovRMSib` (-> SIB RMW form)
//      or full-width `MovRM` (-> base form) with default flags and no
//      proof_origin; every EA component a Gpr64 VReg (PReg EA refused) —
//      shared acceptance with `imul_fuse_load_kind`.
//   C. Store k: same-family store (`MovMRSib` for `MovRMSib`, `MovMR` for
//      `MovRM`) with default flags, no proof_origin; value operand is exactly
//      `d`; memory operand STRUCTURALLY EQUAL to the load's (same base/index
//      VReg id+class, same scale, same disp).
//   W1. Window (i,j): pure register ALU only (`imul_fuse_window_ok`), no
//      mention of `t`, no def of the EA regs or of `s`.
//   W2. Window (j,k): W1 PLUS no flag-reader AND no flag-writer
//      (`x86_reads_flags` / `x86_writes_flags`), and no mention of `d`
//      (a use would consume the deleted ALU result; a def would change the
//      stored value).
//   E. The EA regs exclude `t` (the load overwrites it) and `d` (the ALU
//      writes it between load and store — structural identity would not be
//      value identity).
//   D. `t` locally dead after j; `d` locally dead after k — both via the
//      shared hardened `imul_fuse_t_dead_after` (full-unconditional-overwrite
//      + tied/conditional-write refusal).
//   P. ADMISSION: the fused opcode is created ONLY if the injected callback
//      admits it (proof-backed `reconstruction_discharges_valid` in
//      production; `|_| false` when absent). Architecture-enforced
//      fail-closed: no admission, no emission.
// ---------------------------------------------------------------------------

/// DEFAULT-ON (same record as imul_fuse); `TCG_NO_X86_RMW_FUSE` is the
/// forensic opt-out. Read through the lock-guarded process-env shim so the
/// kill-switch test can override it without racing parallel test threads.
static RMW_FUSE_SDEF: std::sync::OnceLock<bool> = std::sync::OnceLock::new();

/// Install the opt-out for allowing a def of the fused instruction's REGISTER
/// operand `s` inside the RMW fusion's W1 window
/// (`-Ztrust-ir-cg-args=no-x86-rmw-fuse-sdef`). DEFAULT ON — see the condition's
/// comment for why the old refusal was stricter than the rewrite needs.
pub fn set_rmw_fuse_sdef_disabled(disabled: bool) -> bool {
    match RMW_FUSE_SDEF.set(disabled) {
        Ok(()) => true,
        Err(requested) => RMW_FUSE_SDEF.get() == Some(&requested),
    }
}

fn rmw_fuse_sdef_enabled() -> bool {
    if let Some(disabled) = RMW_FUSE_SDEF.get() {
        return !*disabled;
    }
    !crate::tcg_env_flag("TCG_NO_X86_RMW_FUSE_SDEF")
}

static RMW_FUSE_TRACE: std::sync::OnceLock<bool> = std::sync::OnceLock::new();

/// Install the RMW-fusion decline trace (`-Ztrust-ir-cg-args=trace-x86-rmw-fuse`).
/// Diagnostics only — no codegen effect.
pub fn set_rmw_fuse_trace_enabled(enabled: bool) -> bool {
    match RMW_FUSE_TRACE.set(enabled) {
        Ok(()) => true,
        Err(requested) => RMW_FUSE_TRACE.get() == Some(&requested),
    }
}

fn rmw_fuse_trace_enabled() -> bool {
    RMW_FUSE_TRACE.get().copied().unwrap_or(false) || crate::tcg_env_flag("TCG_X86_RMW_FUSE_TRACE")
}

static RMW_FUSE_DISABLED: std::sync::OnceLock<bool> = std::sync::OnceLock::new();

/// Install the memory-destination RMW fusion's opt-out from a TRACKED compiler
/// option, once (`-Ztrust-ir-cg-args=no-x86-rmw-fuse`). DEFAULT ON.
/// `TCG_NO_X86_RMW_FUSE` remains the in-process channel for tests; `trustc`
/// refuses it.
pub fn set_rmw_fuse_disabled(disabled: bool) -> bool {
    match RMW_FUSE_DISABLED.set(disabled) {
        Ok(()) => true,
        Err(requested) => RMW_FUSE_DISABLED.get() == Some(&requested),
    }
}

fn rmw_fuse_enabled() -> bool {
    !RMW_FUSE_DISABLED.get().copied().unwrap_or(false)
        && crate::env_lock::var_os("TCG_NO_X86_RMW_FUSE").is_none()
}

/// The load kinds the RMW fusion accepts, mapped to the REQUIRED same-family
/// store opcode. Shares `imul_fuse_load_kind`'s hardened acceptance (64-bit
/// forms only, default flags, no proof_origin, VReg-only EA components — a
/// PReg base/index would make the E redef scan vacuously pass over an address
/// the pass cannot track; refused outright).
fn rmw_fuse_load_kind(inst: &X86ISelInst) -> Option<(VReg, X86ISelOperand, X86Opcode)> {
    // Own acceptance, WIDER than `imul_fuse_load_kind` in exactly one way:
    // a `StackSlot` EA base is admitted (b1's hot `t[j] ^= s` arm indexes a
    // STACK array, so its SIB base is a slot, not a vreg). This is sound
    // under the same E-condition machinery: `imul_fuse_ea_reg_ids` returns
    // only the VReg components, and a stack slot cannot be redefined at all,
    // so the redef scan over the ids it DOES return is complete. A `PReg`
    // base/index stays refused (untrackable — the original
    // adversarial-review FAIL_CLOSED_GAP).
    if inst.proof_origin.is_some() || inst.flags != inst.opcode.default_flags() {
        return None;
    }
    let base_ok = |b: &X86ISelOperand| {
        matches!(b, X86ISelOperand::VReg(v) if v.class == RegClass::Gpr64)
            || matches!(b, X86ISelOperand::StackSlot(_))
    };
    match inst.opcode {
        X86Opcode::MovRMSib => match inst.operands.as_slice() {
            [
                X86ISelOperand::VReg(t),
                sib @ X86ISelOperand::SibMemAddr { base, index, .. },
            ] if t.class == RegClass::Gpr64
                && base_ok(base.as_ref())
                && matches!(index.as_ref(), X86ISelOperand::VReg(i) if i.class == RegClass::Gpr64) =>
            {
                Some((*t, sib.clone(), X86Opcode::MovMRSib))
            }
            _ => None,
        },
        X86Opcode::MovRM => match inst.operands.as_slice() {
            [
                X86ISelOperand::VReg(t),
                mem @ X86ISelOperand::MemAddr { base, .. },
            ] if t.class == RegClass::Gpr64 && base_ok(base.as_ref()) => {
                Some((*t, mem.clone(), X86Opcode::MovMR))
            }
            _ => None,
        },
        _ => None,
    }
}

/// Def sites of FUNCTION-WIDE single-def vregs: id -> (opcode, operands).
/// A single-def vreg holds one value for the whole execution after its def.
/// Canonical spelling is therefore position-independent only while the
/// canonical root is not redefined between the two memory operations; the
/// caller enforces that temporal condition with [`rmw_fuse_ea_reg_ids`].
fn rmw_fuse_single_def_sites(
    func: &X86ISelFunction,
) -> FxHashMap<u32, (X86Opcode, Vec<X86ISelOperand>)> {
    use crate::effects::x86_produces_value;
    let mut sites: FxHashMap<u32, Option<(X86Opcode, Vec<X86ISelOperand>)>> = FxHashMap::default();
    for block in func.blocks.values() {
        for inst in &block.insts {
            if !x86_produces_value(inst.opcode) {
                continue;
            }
            if let Some(X86ISelOperand::VReg(d)) = inst.operands.first() {
                match sites.entry(d.id) {
                    std::collections::hash_map::Entry::Vacant(e) => {
                        e.insert(Some((inst.opcode, inst.operands.clone())));
                    }
                    std::collections::hash_map::Entry::Occupied(mut e) => {
                        e.insert(None); // multi-def: disqualified
                    }
                }
            }
        }
    }
    sites
        .into_iter()
        .filter_map(|(id, v)| v.map(|v| (id, v)))
        .collect()
}

/// The whole-function facts the RMW matcher consults: the single-def site
/// index and the function-wide use/def counts. A PURE function of `func`, so
/// one build is valid for as long as `func` is unchanged — see
/// [`rmw_fuse_run_on_block_with_maps`].
struct RmwFuseFnMaps {
    sites: FxHashMap<u32, (X86Opcode, Vec<X86ISelOperand>)>,
    fn_uses: FxHashMap<VReg, u32>,
    fn_defs: FxHashMap<VReg, u32>,
}

impl RmwFuseFnMaps {
    fn build(func: &X86ISelFunction) -> Self {
        let sites = rmw_fuse_single_def_sites(func);
        let (fn_uses, fn_defs) = function_use_def_counts(func);
        RmwFuseFnMaps {
            sites,
            fn_uses,
            fn_defs,
        }
    }

    /// Every entry, rendered and sorted, so two builds compare as values.
    #[cfg(any(test, debug_assertions))]
    fn canonical_view(&self) -> [Vec<String>; 3] {
        [
            sorted_debug_entries(&self.sites),
            sorted_debug_entries(&self.fn_uses),
            sorted_debug_entries(&self.fn_defs),
        ]
    }
}

/// Canonicalize a SIB (index, scale) pair through single-def `MovRR` copy
/// chains and single-def `ImulRRI x{2,4,8}` scale folds, returning the root
/// id and the effective hardware scale. Fail-closed at every step: a
/// multi-def link, a non-copy/non-scale def, or a scale outside {1,2,4,8}
/// stops the walk at the current vreg.
fn rmw_fuse_canon_index(
    sites: &FxHashMap<u32, (X86Opcode, Vec<X86ISelOperand>)>,
    mut v: VReg,
    mut scale: u8,
) -> (u32, u8) {
    for _ in 0..16 {
        let Some((op, operands)) = sites.get(&v.id) else {
            return (v.id, scale);
        };
        match (op, operands.as_slice()) {
            (X86Opcode::MovRR, [X86ISelOperand::VReg(_), X86ISelOperand::VReg(src)])
                if src.class == RegClass::Gpr64 =>
            {
                v = *src;
            }
            (
                X86Opcode::ImulRRI,
                [
                    X86ISelOperand::VReg(_),
                    X86ISelOperand::VReg(src),
                    X86ISelOperand::Imm(k),
                ],
            ) if src.class == RegClass::Gpr64 && matches!(*k, 2 | 4 | 8) => {
                let ns = (scale as i64) * *k;
                if !matches!(ns, 1 | 2 | 4 | 8) {
                    return (v.id, scale);
                }
                scale = ns as u8;
                v = *src;
            }
            _ => return (v.id, scale),
        }
    }
    (v.id, scale)
}

/// Every register whose value can affect an EA accepted by
/// [`rmw_fuse_same_ea`]. In addition to the syntactically mentioned base and
/// index, include the canonical index root. The latter is load-bearing: a
/// copy alias can retain the root's old value across a tied/conditional root
/// write, while a later store using the root observes its new value. Scanning
/// only the syntactic alias would then equate two different addresses.
fn rmw_fuse_ea_reg_ids(
    sites: &FxHashMap<u32, (X86Opcode, Vec<X86ISelOperand>)>,
    mem: &X86ISelOperand,
) -> Vec<u32> {
    let mut ids = imul_fuse_ea_reg_ids(mem);
    if let X86ISelOperand::SibMemAddr { index, scale, .. } = mem
        && let X86ISelOperand::VReg(index) = index.as_ref()
    {
        ids.push(rmw_fuse_canon_index(sites, *index, *scale).0);
    }
    ids.sort_unstable();
    ids.dedup();
    ids
}

/// Condition C's EA equivalence: same base operand (structural — VReg id or
/// StackSlot index), same displacement, and (index, scale) pairs that
/// canonicalize to the same (root, effective scale). The b1 shapes this
/// admits: a store index that is a pure copy-chain alias of the load index,
/// and a store using `index = j*8, scale 1` against a load's
/// `index = j, scale 8`.
fn rmw_fuse_same_ea(
    sites: &FxHashMap<u32, (X86Opcode, Vec<X86ISelOperand>)>,
    load_mem: &X86ISelOperand,
    store_mem: &X86ISelOperand,
) -> bool {
    if load_mem == store_mem {
        return true;
    }
    match (load_mem, store_mem) {
        (
            X86ISelOperand::SibMemAddr {
                base: lb,
                index: li,
                scale: ls,
                disp: ld,
            },
            X86ISelOperand::SibMemAddr {
                base: sb,
                index: si,
                scale: ss,
                disp: sd,
            },
        ) if lb == sb && ld == sd => {
            let (X86ISelOperand::VReg(li), X86ISelOperand::VReg(si)) = (li.as_ref(), si.as_ref())
            else {
                return false;
            };
            rmw_fuse_canon_index(sites, *li, *ls) == rmw_fuse_canon_index(sites, *si, *ss)
        }
        _ => false,
    }
}

/// The fused memory-destination opcode for (ALU anchor, store form), or None
/// for any pair outside the two proven commutative families.
fn rmw_fuse_fused_opcode(alu: X86Opcode, store: X86Opcode) -> Option<X86Opcode> {
    match (alu, store) {
        (X86Opcode::XorRR, X86Opcode::MovMRSib) => Some(X86Opcode::XorMRSib),
        (X86Opcode::XorRR, X86Opcode::MovMR) => Some(X86Opcode::XorMR),
        (X86Opcode::AddRR, X86Opcode::MovMRSib) => Some(X86Opcode::AddMRSib),
        (X86Opcode::AddRR, X86Opcode::MovMR) => Some(X86Opcode::AddMR),
        _ => None,
    }
}

/// Window purity for condition W2: W1's pure-register-ALU rule PLUS no
/// flag-reader and no flag-writer — the ALU's flag-write moves from j down to
/// k across this window (hand-proof item 4). `imul_fuse_window_ok` alone
/// admits Setcc/Cmovcc (EMPTY default flags) and every flag-writing ALU.
fn rmw_fuse_w2_ok(inst: &X86ISelInst) -> bool {
    imul_fuse_window_ok(inst) && !x86_reads_flags(inst.opcode) && !x86_writes_flags(inst.opcode)
}

/// Build the whole-function maps and fuse one block. Equivalent to
/// [`rmw_fuse_run_on_block_with_maps`] with a freshly built map set; kept for
/// the unit tests, which exercise one block of a fixed function.
#[cfg(test)]
fn rmw_fuse_run_on_block(
    func: &mut X86ISelFunction,
    block_id: trust_cg_lower::instructions::Block,
    admit: ReconstructionAdmit,
) -> bool {
    rmw_fuse_run_on_block_sdef(func, block_id, admit, rmw_fuse_sdef_enabled())
}

/// [`rmw_fuse_run_on_block`] with the W1 `s`-def relaxation chosen explicitly,
/// so the tests drive both arms without touching process-global state.
#[cfg(test)]
fn rmw_fuse_run_on_block_sdef(
    func: &mut X86ISelFunction,
    block_id: trust_cg_lower::instructions::Block,
    admit: ReconstructionAdmit,
    allow_s_def_in_w1: bool,
) -> bool {
    let maps = RmwFuseFnMaps::build(func);
    rmw_fuse_run_on_block_with_maps(func, block_id, admit, &maps, allow_s_def_in_w1)
}

/// Run the RMW fusion on one block. Returns whether anything changed.
///
/// `admit` is the fail-closed proof admission (condition P): the fused opcode
/// is never constructed unless `admit(fused_opcode)`.
fn rmw_fuse_run_on_block_with_maps(
    func: &mut X86ISelFunction,
    block_id: trust_cg_lower::instructions::Block,
    admit: ReconstructionAdmit,
    // Whole-function facts for the CURRENT state of `func`, owned by the
    // caller. This routine mutates `func` ONLY when it returns `true` (see the
    // `fusions.is_empty()` early return below), so the caller may reuse one
    // build across consecutive blocks that fused nothing and rebuild the
    // instant one does — handing every block exactly the maps a per-block
    // build would have produced, which is what keeps the emitted bytes
    // identical to the per-block rebuild.
    maps: &RmwFuseFnMaps,
    allow_s_def_in_w1: bool,
) -> bool {
    let sites = &maps.sites;
    let fn_uses = &maps.fn_uses;
    let fn_defs = &maps.fn_defs;
    // The block is looked up ONCE, mutably, and held for the whole pass: the
    // match phase below reads it through the shared `insts` reborrow (every
    // function-wide fact it needs — `sites`, `fn_uses`, `fn_defs` — is a
    // caller-owned snapshot borrowed from `maps`, never from `func`), and the
    // apply phase writes through the same binding once `insts` is dead. There
    // is therefore no second lookup whose failure would have to be asserted
    // against.
    let func_name = func.name.clone();
    let Some(block) = func.blocks.get_mut(&block_id) else {
        return false;
    };
    let insts = &block.insts;

    struct Fusion {
        load_idx: usize,
        alu_idx: usize,
        store_idx: usize,
        replacement: X86ISelInst,
    }
    let mut fusions: Vec<Fusion> = Vec::new();
    let mut consumed: FxHashSet<usize> = FxHashSet::default();

    // Decline trace (`-Ztrust-ir-cg-args=trace-x86-rmw-fuse`, diagnostics only).
    // Every condition below used to decline in SILENCE, and this pass has
    // fifteen of them: window purity, the EA redef scan, the `sdef` rule, the
    // two deadness scans, canonical-EA equality. Reading the output cannot tell
    // you which one fired, so a lost fusion was not debuggable — the same gap
    // `trace-vectorize-bail` closed for the vectorizer. Reported once per
    // (anchor, form) so a candidate that fails on its first source and fuses on
    // its second shows both lines.
    let trace = rmw_fuse_trace_enabled();
    let rmw_trace = |j: usize, op: X86Opcode, why: &str| {
        if trace {
            eprintln!("rmw-fuse-bail[{func_name}/{block_id:?}/anchor={j}:{op:?}]: {why}");
        }
    };

    for j in 0..insts.len() {
        let anchor = &insts[j];
        if !matches!(anchor.opcode, X86Opcode::XorRR | X86Opcode::AddRR)
            || anchor.proof_origin.is_some()
            || anchor.flags != anchor.opcode.default_flags()
        {
            continue;
        }
        let g64 = |r: &VReg| r.class == RegClass::Gpr64;
        // Decode the anchor form into (d, [(t_candidate, s_for_that_t)]).
        // Tied `[d, t]`: d := d Op t, so the fused register source is d's own
        // pre-value (s := d).
        let (d, forms): (VReg, Vec<(VReg, VReg)>) = match anchor.operands.as_slice() {
            [X86ISelOperand::VReg(d), X86ISelOperand::VReg(t)] if g64(d) && g64(t) && t != d => {
                (*d, vec![(*t, *d)])
            }
            [
                X86ISelOperand::VReg(d),
                X86ISelOperand::VReg(s1),
                X86ISelOperand::VReg(s2),
            ] if g64(d) && g64(s1) && g64(s2) => (*d, vec![(*s1, *s2), (*s2, *s1)]),
            _ => continue,
        };

        // Try each source as the load result `t` (commutative).
        'forms: for &(t, s) in &forms {
            // Condition A: s != t (the loaded value would be needed twice but
            // the load is deleted); t != d (fail-closed — one id playing both
            // roles defeats the two deadness scans).
            if s.id == t.id || t.id == d.id {
                rmw_trace(
                    j,
                    anchor.opcode,
                    "condition A: the loaded value and the fused source are one id, or t aliases d",
                );
                continue;
            }
            // Find t's nearest def above j (condition B).
            let Some(i) = (0..j)
                .rev()
                .find(|&x| local_fold_defines_vreg(&insts[x], t))
            else {
                rmw_trace(
                    j,
                    anchor.opcode,
                    "no definition of the load temp above the ALU",
                );
                continue;
            };
            if consumed.contains(&i) || consumed.contains(&j) {
                rmw_trace(
                    j,
                    anchor.opcode,
                    "the load or the ALU is already consumed by another fusion",
                );
                continue;
            }
            let Some((lt, mem, store_opcode)) = rmw_fuse_load_kind(&insts[i]) else {
                rmw_trace(
                    j,
                    anchor.opcode,
                    "the temp's def is not an accepted load form (rmw_fuse_load_kind)",
                );
                continue;
            };
            if lt != t {
                rmw_trace(
                    j,
                    anchor.opcode,
                    "the load defines a different vreg than this form's temp",
                );
                continue;
            }
            // Condition P: the proof admission gate. No admission, no fusion —
            // the opcode is never constructed, so it can never be emitted.
            let Some(fused_opcode) = rmw_fuse_fused_opcode(anchor.opcode, store_opcode) else {
                rmw_trace(
                    j,
                    anchor.opcode,
                    "no fused memory-destination opcode for this (ALU, store) pair",
                );
                continue;
            };
            if !admit(fused_opcode) {
                rmw_trace(
                    j,
                    anchor.opcode,
                    "the proof admission gate refused the fused opcode",
                );
                continue;
            }
            // Condition E: EA regs exclude t (overwritten by the load) and d
            // (overwritten by the ALU) — structural EA identity must be VALUE
            // identity at both the load's and the store's position.
            // Include canonical roots as well as the registers spelled in the
            // load. Otherwise `alias <- root; load [alias]; root += 1; store
            // [root]` is falsely considered one EA: the alias still holds the
            // old root while the store observes the new one.
            let ea_ids = rmw_fuse_ea_reg_ids(sites, &mem);
            if ea_ids.iter().any(|&id| id == t.id || id == d.id) {
                rmw_trace(
                    j,
                    anchor.opcode,
                    "condition E: an EA register is the load temp or the ALU def",
                );
                continue;
            }
            // Condition W1 over (i,j): pure register ALU, no mention of t, no
            // def of the EA regs.
            //
            // `s` IS ALLOWED TO BE DEFINED HERE, and that relaxation is what lets
            // `b1_mispredict`'s hot loop fuse. The replacement is spliced at the
            // STORE's position (see the rebuild below), which is the LATEST of the
            // three, so the fused instruction reads `s` there — after any def of
            // `s` between the load and the ALU. What actually has to hold is that
            // `s` carries from the ALU to the store unchanged, and the W2 window
            // below already refuses a def of `s` on exactly that stretch. A def
            // in W1 is not deleted either: only the load and the ALU are, so `s`
            // is still computed where it was.
            //
            // b1's shape, which the old condition declined:
            //   MovRMSib t, [slot + j*8]     ; the load
            //   MovRR    s, acc              ; a def of `s` -- this is the one
            //   AddRR    d, t, s             ; the anchor
            //   MovMRSib [slot + j'*8], d    ; the store (j' a copy of j)
            // The `s` def is a pure register copy: it cannot touch memory (the
            // window is `imul_fuse_window_ok`, which excludes every memory op),
            // cannot mention `t`, and cannot define an EA register — all still
            // checked. `no-x86-rmw-fuse-sdef` restores the stricter window.
            for w in &insts[i + 1..j] {
                if !imul_fuse_window_ok(w) {
                    rmw_trace(
                        j,
                        anchor.opcode,
                        "W1 window impurity between the load and the ALU",
                    );
                    continue 'forms;
                }
                let mut w_mentions = FxHashSet::default();
                for op in &w.operands {
                    collect_operand_mentions_flat(op, &mut w_mentions);
                }
                if w_mentions.iter().any(|m| m.id == t.id) {
                    rmw_trace(
                        j,
                        anchor.opcode,
                        "W1 between load and ALU mentions the load temp",
                    );
                    continue 'forms;
                }
                let must_not_define: Vec<u32> = if allow_s_def_in_w1 {
                    ea_ids.clone()
                } else {
                    ea_ids
                        .iter()
                        .copied()
                        .chain(std::iter::once(s.id))
                        .collect()
                };
                if must_not_define
                    .iter()
                    .any(|&id| local_fold_defines_vreg(w, VReg::new(id, RegClass::Gpr64)))
                {
                    rmw_trace(
                        j,
                        anchor.opcode,
                        "W1 defines a register the fusion may not have redefined (the sdef rule)",
                    );
                    continue 'forms;
                }
            }
            // Find the store k (condition C), walking forward under W2. The
            // first instruction that is neither the matching store nor a
            // W2-clean window member aborts the candidate — in particular ANY
            // other memory op (imul_fuse_window_ok excludes it) and ANY
            // flag-reader or flag-writer (rmw_fuse_w2_ok).
            let mut store_idx = None;
            for (k, w) in insts.iter().enumerate().skip(j + 1) {
                let is_matching_store = w.opcode == store_opcode
                    && w.proof_origin.is_none()
                    && w.flags == store_opcode.default_flags()
                    && matches!(
                        w.operands.as_slice(),
                        // EA equivalence (condition C): structural identity,
                        // OR the same address under single-def copy-chain /
                        // scale-fold canonicalization (`rmw_fuse_same_ea`).
                        // The FUSED instruction keeps the LOAD's operand
                        // spelling either way. Value operand exactly d.
                        [m, X86ISelOperand::VReg(v)]
                            if rmw_fuse_same_ea(sites, &mem, m) && *v == d
                    );
                if is_matching_store {
                    store_idx = Some(k);
                    break;
                }
                // W2 window member: W1 conditions PLUS the flag fence, PLUS
                // no mention of d (a use would consume the deleted ALU
                // result; a def would change the stored value).
                if !rmw_fuse_w2_ok(w) {
                    break;
                }
                let mut w_mentions = FxHashSet::default();
                for op in &w.operands {
                    collect_operand_mentions_flat(op, &mut w_mentions);
                }
                if w_mentions.iter().any(|m| m.id == t.id || m.id == d.id) {
                    break;
                }
                if ea_ids
                    .iter()
                    .chain(std::iter::once(&s.id))
                    .any(|&id| local_fold_defines_vreg(w, VReg::new(id, RegClass::Gpr64)))
                {
                    break;
                }
            }
            let Some(k) = store_idx else {
                rmw_trace(
                    j,
                    anchor.opcode,
                    "no matching store of the ALU def to the same EA after the ALU",
                );
                continue;
            };
            if consumed.contains(&k) {
                rmw_trace(
                    j,
                    anchor.opcode,
                    "the matching store is already consumed by another fusion",
                );
                continue;
            }
            // Condition D: t locally dead after j; d locally dead after k.
            // Condition D. The block-local redef rule OR the function-wide
            // single-def/single-use fallback: the matched load is t's ONLY
            // def and the matched anchor its ONLY use (respectively ALU/
            // store for d), so deleting the pair leaves the vreg with zero
            // defs and zero uses — vacuously dead. This is the b1 hot-block
            // reality: t and d are simply never touched again before the
            // block ends, which the redef rule cannot see. (The tied form
            // keeps the strict rule for d: there s == d, and d's pre-value
            // is READ by the fused instruction.)
            let whole_fn_dead = |x: VReg| {
                fn_defs.get(&x).copied().unwrap_or(0) == 1
                    && fn_uses.get(&x).copied().unwrap_or(0) == 1
            };
            if !(imul_fuse_t_dead_after(insts, j, t) || whole_fn_dead(t)) {
                rmw_trace(j, anchor.opcode, "the load temp is not dead after the ALU");
                continue;
            }
            if !(imul_fuse_t_dead_after(insts, k, d) || (s != d && whole_fn_dead(d))) {
                rmw_trace(j, anchor.opcode, "the ALU def is not dead after the store");
                continue;
            }
            // Build the replacement: `OpMR[Sib] [mem], s` with the opcode's
            // default flags (`X86ISelInst::new` applies them).
            let replacement =
                X86ISelInst::new(fused_opcode, vec![mem.clone(), X86ISelOperand::VReg(s)]);
            consumed.insert(i);
            consumed.insert(j);
            consumed.insert(k);
            fusions.push(Fusion {
                load_idx: i,
                alu_idx: j,
                store_idx: k,
                replacement,
            });
            break;
        }
    }

    if fusions.is_empty() {
        return false;
    }

    if crate::env_lock::var_os("TCG_X86_RMW_FUSE_LOG").is_some() {
        eprintln!(
            "x86-rmw-fuse: fused {} rmw triple(s) in `{}` block #{:?}",
            fusions.len(),
            func.name,
            block_id.0,
        );
    }

    // Rebuild the block: delete each load and ALU, splice each replacement at
    // the store's position.
    let mut delete: FxHashSet<usize> = FxHashSet::default();
    let mut replace: FxHashMap<usize, X86ISelInst> = FxHashMap::default();
    for f in fusions {
        delete.insert(f.load_idx);
        delete.insert(f.alu_idx);
        replace.insert(f.store_idx, f.replacement);
    }
    let old = std::mem::take(&mut block.insts);
    let mut rebuilt = Vec::with_capacity(old.len());
    for (idx, inst) in old.into_iter().enumerate() {
        if delete.contains(&idx) {
            continue;
        }
        if let Some(mut rep) = replace.remove(&idx) {
            // Preserve the store's proof_origin (None by condition C, but
            // keep the plumbing honest).
            rep.proof_origin = inst.proof_origin;
            rebuilt.push(rep);
            continue;
        }
        rebuilt.push(inst);
    }
    block.insts = rebuilt;
    true
}

fn simplify_inst_gated(
    insts: &[X86ISelInst],
    index: usize,
    zeroidiom_used: Option<&FxHashSet<VReg>>,
    admit_constmul_shift: ConstMulShiftAdmit,
    certificate_free_imul: bool,
) -> Option<PeepholeEdit> {
    let inst = &insts[index];

    if !is_safe_local_candidate(inst) && !is_safe_flag_preserving_candidate(inst) {
        return None;
    }

    match inst.opcode {
        X86Opcode::MovRR
        | X86Opcode::MovRR32
        | X86Opcode::MovssRR
        | X86Opcode::MovsdRR
        | X86Opcode::MovdqaRR => {
            let (dst, src) = copy_vregs(inst)?;
            (dst == src).then_some(PeepholeEdit::Remove)
        }
        X86Opcode::Lea => {
            let (dst, src) = zero_disp_lea_vregs(inst)?;
            Some(movrr_or_remove(dst, src))
        }
        X86Opcode::MovRI => {
            let dst = movri_zero_vreg(inst)?;
            // Zero-idiom gate: an unread zero def stays MovRI (DCE-removable)
            // instead of becoming `XorRR d, d`, whose formal self-USE would
            // pin every def of the id in the function-wide DCE use-set.
            if let Some(used) = zeroidiom_used
                && !used.contains(&dst)
            {
                return None;
            }
            flags_written_here_are_dead(insts, index)
                .then_some(PeepholeEdit::Replace(xorrr_zero(dst)))
        }
        X86Opcode::CmpRI | X86Opcode::CmpRI8 => {
            let src = cmp_zero_vreg(inst)?;
            Some(PeepholeEdit::Replace(test_rr(src)))
        }
        X86Opcode::TestRI => {
            let src = test_ri_all_ones_vreg(inst)?;
            Some(PeepholeEdit::Replace(test_rr(src)))
        }
        X86Opcode::AddRR => {
            let (dst, src) = addrr_duplicate_gpr64_sources(inst)?;
            if can_replace_flag_writer(insts, index) {
                Some(PeepholeEdit::Replace(lea_sib_double(dst, src)))
            } else {
                None
            }
        }
        X86Opcode::AddRI | X86Opcode::SubRI => {
            let (dst, src, imm) = ri_vregs_and_imm(inst)?;
            if !can_replace_flag_writer(insts, index) {
                return None;
            }

            match (inst.opcode, imm, dst == src) {
                (_, 0, _) => Some(movrr_or_remove(dst, src)),
                (X86Opcode::AddRI, 1, true) => Some(PeepholeEdit::Replace(inc_vreg(dst))),
                (X86Opcode::SubRI, 1, true) => Some(PeepholeEdit::Replace(dec_vreg(dst))),
                _ => None,
            }
        }
        X86Opcode::OrRI | X86Opcode::ShlRI | X86Opcode::ShrRI | X86Opcode::SarRI => {
            let (dst, src, imm) = ri_vregs_and_imm(inst)?;
            if imm == 0 && can_replace_flag_writer(insts, index) {
                Some(movrr_or_remove(dst, src))
            } else {
                None
            }
        }
        X86Opcode::XorRI => {
            let (dst, src, imm) = ri_vregs_and_imm(inst)?;
            if !can_replace_flag_writer(insts, index) {
                return None;
            }

            match imm {
                0 => Some(movrr_or_remove(dst, src)),
                -1 if dst == src => Some(PeepholeEdit::Replace(not_vreg(dst))),
                _ => None,
            }
        }
        X86Opcode::AndRI => {
            let (dst, src, imm) = ri_vregs_and_imm(inst)?;
            if !can_replace_flag_writer(insts, index) {
                return None;
            }

            match imm {
                -1 => Some(movrr_or_remove(dst, src)),
                0 => Some(PeepholeEdit::Replace(xorrr_zero(dst))),
                _ => None,
            }
        }
        X86Opcode::ImulRRI => {
            let (dst, src, imm) = ri_vregs_and_imm(inst)?;
            // A certificate-free compile lets a plain store pass in the
            // flags scan; one that keeps certificates uses the historical
            // scan, which stops at every store.
            let flags_dead = if certificate_free_imul {
                imul_flags_are_dead(insts, index)
            } else {
                flags_written_here_are_dead(insts, index)
            };
            if !flags_dead {
                return None;
            }

            match imm {
                -1 if dst == src => Some(PeepholeEdit::Replace(neg_vreg(dst))),
                0 => Some(PeepholeEdit::Replace(xorrr_zero(dst))),
                1 => Some(movrr_or_remove(dst, src)),
                // Small-constant strength reduction (critical-cycle scope,
                // re-scoped from the 2026-08 suite-level null: on p5's
                // loop-carried recurrence the 3-cycle IMUL is the cycle's
                // longest link and a 1-cycle LEA measured -8%; off the
                // cycle it is ~free either way, so firing unconditionally
                // costs nothing). d = s*{3,5,9} is one LEA [s + s*{2,4,8}];
                // d = s*7 is SHL d,s,3 ; SUB d,d,s using d itself as the
                // temporary (requires d != s). The flags guard above
                // already proved the IMUL's flag results are dead, and
                // every replacement opcode is inside the proof perimeter.
                // d = s*2 is the doubling LEA [s + s*1] the `AddRR d, s, s`
                // arm below also produces: one 1-cycle LEA for the 3-cycle
                // IMUL, no flags written (the IMUL's are dead by the guard
                // above). 64-bit only, the width `lea_sib_double` encodes.
                // Measured on the TY kernel `ty_bfs_kernel` (`y * 2` stored
                // to the successor state): 1.083 to 1.065 of LLVM by a hand
                // edit of the linked binary, LLVM and gcc both emit the LEA.
                // Certificate-free compiles only (`certificate_free_imul`).
                2 if certificate_free_imul
                    && dst != src
                    && dst.class == RegClass::Gpr64
                    && src.class == RegClass::Gpr64 =>
                {
                    Some(PeepholeEdit::Replace(lea_sib_double(dst, src)))
                }
                3 | 5 | 9 if dst != src => Some(PeepholeEdit::Replace(lea_sib_scaled(
                    dst,
                    src,
                    (imm - 1) as u8,
                ))),
                // d = s*7 as TWO dependent LEAs: d = s + s*2 (=3s), then
                // d = s + d*2 (=7s), reusing d as the temporary (d != s).
                // 2 cycles, ZERO reg-reg movs, no flags written.
                //
                // ⚑ SCOPE OF THE RECORDED NULL (corrected 2026-09-01). The
                // earlier note here said "the ShlRI+SubRR shape measured NULL
                // on p5" without naming the site, which read as a general
                // verdict on SHL+SUB. It is not. The a74e7cd6 measurement was
                // about THIS arm — p5's `st.b.wrapping_mul(7)` — where the
                // double-LEA replaced SHL+SUB and the suite row did not move.
                // p5's OTHER multiply, `st.a.wrapping_mul(31)`, was never
                // rewritten at all (it fell through to `_ => None`), and the
                // stated mechanism cannot apply to it: there the SHL's
                // two-address MovRR READS the loop-carried value and WRITES a
                // dead-after-one-use temp, so it is not on the carried path.
                // The `2^a ± 1` arm below claims that site.
                7 if dst != src => Some(PeepholeEdit::ReplaceTwo(
                    lea_sib_scaled(dst, src, 2),
                    X86ISelInst::new(
                        X86Opcode::LeaSib,
                        vec![
                            X86ISelOperand::VReg(dst),
                            X86ISelOperand::SibMemAddr {
                                base: Box::new(X86ISelOperand::VReg(src)),
                                index: Box::new(X86ISelOperand::VReg(dst)),
                                scale: 2,
                                disp: 0,
                            },
                        ],
                    ),
                )),
                // d = s * (2^a ± 1)  ->  SHL d, s, a ; ADD/SUB d, d, s.
                //
                // Reaches the constants the LEA arms above cannot express
                // (31, 33, 63, 65, ...) — on p5's `st.a.wrapping_mul(31)` the
                // rewrite is what rustc-LLVM and gcc-16 both emit, `mov`
                // included. The measured mechanism is PORT CONTENTION, not
                // latency: p5's recurrence has ~4 cycles of slack over IMUL's
                // 3-cycle latency, but its four dependent LEAs already
                // saturate p1/p5 and `IMUL r64,r64,imm` is p1-EXCLUSIVE. The
                // replacement issues elsewhere (`mov` renamed away, `shl` on
                // p0/p6, `sub` on p0156).
                //
                // ⚑ This is NOT unconditionally throughput-safe the way the
                // AArch64 `mul_shift_reduce` is: AArch64 has a 3-address
                // shift, so its form is 2 instructions for 1, whereas here it
                // is 2 PLUS a possible two-address MovRR — up to +2 uops for
                // one IMUL. The ONE-SHIFT restriction in
                // `constmul_shift_decompose` (only `2^a ± 1`, never `24 =
                // 16+8` or `576`) is what bounds that exposure.
                //
                // Preconditions: `d != s` (with `d == s` the second
                // instruction would read a clobbered value); the IMUL's flags
                // proven dead by the guard above (the replacement writes
                // RFLAGS only at the original position, so the SAME full
                // overwrite still dominates every reader); and the ALGEBRAIC
                // identity `x·(2^a ± 1) ≡ (x<<a) ± x (mod 2^W)` discharged by
                // the injected admission (fail-closed: no proof ⇒ the IMUL
                // stands). Kill switch: `TCG_NO_X86_CONSTMUL_SHIFT`.
                _ if constmul_shift_enabled() && dst != src => {
                    constmul_shift_reduce(dst, src, imm, admit_constmul_shift)
                }
                _ => None,
            }
        }
        X86Opcode::SubRR => {
            let (dst, lhs, rhs) = rr_vregs(inst)?;
            if lhs == rhs && can_replace_flag_writer(insts, index) {
                Some(PeepholeEdit::Replace(xorrr_zero(dst)))
            } else {
                None
            }
        }
        X86Opcode::XorRR => {
            let (dst, lhs, rhs) = rr_vregs(inst)?;
            if lhs == rhs
                && !is_canonical_two_operand_xor_zero(inst)
                && can_replace_flag_writer(insts, index)
            {
                Some(PeepholeEdit::Replace(xorrr_zero(dst)))
            } else {
                None
            }
        }
        X86Opcode::OrRR | X86Opcode::AndRR => {
            let (dst, lhs, rhs) = rr_vregs(inst)?;
            if lhs == rhs && can_replace_flag_writer(insts, index) {
                Some(movrr_or_remove(dst, lhs))
            } else {
                None
            }
        }
        _ => None,
    }
}

fn cmp_zero_vreg(inst: &X86ISelInst) -> Option<VReg> {
    match inst.operands.as_slice() {
        [X86ISelOperand::VReg(src), X86ISelOperand::Imm(0)] if is_supported_gpr(*src) => Some(*src),
        _ => None,
    }
}

fn test_ri_all_ones_vreg(inst: &X86ISelInst) -> Option<VReg> {
    match inst.operands.as_slice() {
        [X86ISelOperand::VReg(src), X86ISelOperand::Imm(-1)] if is_supported_gpr(*src) => {
            Some(*src)
        }
        _ => None,
    }
}

fn addrr_duplicate_gpr64_sources(inst: &X86ISelInst) -> Option<(VReg, VReg)> {
    match inst.operands.as_slice() {
        [X86ISelOperand::VReg(dst), X86ISelOperand::VReg(rhs)]
            if *dst == *rhs && dst.class == RegClass::Gpr64 =>
        {
            Some((*dst, *rhs))
        }
        [
            X86ISelOperand::VReg(dst),
            X86ISelOperand::VReg(lhs),
            X86ISelOperand::VReg(rhs),
        ] if *lhs == *rhs && dst.class == RegClass::Gpr64 && lhs.class == RegClass::Gpr64 => {
            Some((*dst, *lhs))
        }
        _ => None,
    }
}

fn zero_disp_lea_vregs(inst: &X86ISelInst) -> Option<(VReg, VReg)> {
    match inst.operands.as_slice() {
        [
            X86ISelOperand::VReg(dst),
            X86ISelOperand::MemAddr { base, disp },
        ] if *disp == 0 => match base.as_ref() {
            X86ISelOperand::VReg(src) if same_supported_class(*dst, *src) => Some((*dst, *src)),
            _ => None,
        },
        _ => None,
    }
}

fn copy_vregs(inst: &X86ISelInst) -> Option<(VReg, VReg)> {
    let expected_class = copy_opcode_class(inst.opcode)?;
    match inst.operands.as_slice() {
        [X86ISelOperand::VReg(dst), X86ISelOperand::VReg(src)]
            if dst.class == expected_class && src.class == expected_class =>
        {
            Some((*dst, *src))
        }
        _ => None,
    }
}

fn copy_opcode_class(opcode: X86Opcode) -> Option<RegClass> {
    match opcode {
        X86Opcode::MovRR => Some(RegClass::Gpr64),
        X86Opcode::MovRR32 => Some(RegClass::Gpr32),
        X86Opcode::MovssRR => Some(RegClass::Fpr32),
        X86Opcode::MovsdRR => Some(RegClass::Fpr64),
        X86Opcode::MovdqaRR => Some(RegClass::Fpr128),
        _ => None,
    }
}

fn ri_vregs_and_imm(inst: &X86ISelInst) -> Option<(VReg, VReg, i64)> {
    match inst.operands.as_slice() {
        [X86ISelOperand::VReg(dst), X86ISelOperand::Imm(imm)] if is_supported_gpr(*dst) => {
            Some((*dst, *dst, *imm))
        }
        [
            X86ISelOperand::VReg(dst),
            X86ISelOperand::VReg(src),
            X86ISelOperand::Imm(imm),
        ] if same_supported_class(*dst, *src) => Some((*dst, *src, *imm)),
        _ => None,
    }
}

fn movri_zero_vreg(inst: &X86ISelInst) -> Option<VReg> {
    match inst.operands.as_slice() {
        [X86ISelOperand::VReg(dst), X86ISelOperand::Imm(0)] if is_supported_gpr(*dst) => Some(*dst),
        _ => None,
    }
}

fn rr_vregs(inst: &X86ISelInst) -> Option<(VReg, VReg, VReg)> {
    match inst.operands.as_slice() {
        [X86ISelOperand::VReg(dst), X86ISelOperand::VReg(rhs)]
            if same_supported_class(*dst, *rhs) =>
        {
            Some((*dst, *dst, *rhs))
        }
        [
            X86ISelOperand::VReg(dst),
            X86ISelOperand::VReg(lhs),
            X86ISelOperand::VReg(rhs),
        ] if same_supported_class(*dst, *lhs) && same_supported_class(*lhs, *rhs) => {
            Some((*dst, *lhs, *rhs))
        }
        _ => None,
    }
}

fn test_rr(src: VReg) -> X86ISelInst {
    X86ISelInst::new(
        X86Opcode::TestRR,
        vec![X86ISelOperand::VReg(src), X86ISelOperand::VReg(src)],
    )
}

/// Kill switch for the `IMUL r,r,2^a±1` -> `SHL ; ADD/SUB` arm alone (any
/// value disables), so it can be paired-A/B'd independently of the LEA arms.
///
/// NOT memoized — a SEMANTIC gate, and the in-process kill-switch tests flip it
/// between calls. (Only pure log/trace gates are cached in this file.)
fn constmul_shift_enabled() -> bool {
    std::env::var_os("TCG_NO_X86_CONSTMUL_SHIFT").is_none()
}

/// Decompose a multiplier into the ONE-SHIFT two-term form `2^a + t` with
/// `t ∈ {+1, -1}` and `1 <= a < width`. Returns `(a, plus_one)`, or `None`
/// (BAIL) for anything else.
///
/// Ported from `mul_shift_reduce::decompose`, keeping its restrictions:
///
/// * the `b != 0` ONE-SHIFT bail — the smaller power must be `2^0`, so the
///   sequence is a single shift plus one add/sub. A two-shift form (`24 =
///   16 + 8`, `576`, `14`) would be 3 ALU ops for one MUL and is a measured
///   throughput regression in matmul's index math;
/// * a leading POSITIVE `2^a` term. That additionally excludes `1 - 2^a`,
///   which AArch64 does admit but x86 cannot express without a
///   `SubRR [dst, src, dst]` — a `dst == rhs` alias that routes into the
///   two-address scratch path (the s31226 P0 class) for zero suite sites.
///
/// A pure power of two (`c == 2^a`) also BAILS: Stage 1 deliberately does not
/// claim `IMUL $2` / `IMUL $8`, whose blast radius is the copy-bloat-sensitive
/// b1 + h-family.
fn constmul_shift_decompose(c: i128, width: u32) -> Option<(u32, bool)> {
    // `|c| <= 1` is mul by 0/1/-1: degenerate, handled by the arms above.
    if c.abs() < 2 {
        return None;
    }
    let w = i128::from(width);
    for a in 1..w {
        let pa: i128 = 1i128 << a;
        // Pure power of two — NOT claimed by Stage 1.
        if c == pa {
            return None;
        }
        for &sa in &[1i128, -1i128] {
            let rem = c - sa * pa;
            if rem == 0 {
                continue;
            }
            let mag = rem.unsigned_abs();
            if !mag.is_power_of_two() {
                continue;
            }
            let b = mag.trailing_zeros();
            if (a as u32) <= b || b >= width {
                continue; // distinct powers, b < a, both in range
            }
            // ONE-SHIFT restriction (see the doc comment).
            if b != 0 {
                continue;
            }
            if sa < 0 {
                continue; // excludes (-,-) and (-,+) == `1 - 2^a`
            }
            return Some((a as u32, rem > 0));
        }
    }
    None
}

/// Build `SHL d, s, a ; ADD/SUB d, d, s` for `d = s * (2^a ± 1)`, or `None` if
/// the multiplier is not of that shape / the identity is not admitted.
///
/// The caller has already established `dst != src`, that the IMUL's RFLAGS are
/// dead, and that both kill switches are off.
fn constmul_shift_reduce(
    dst: VReg,
    src: VReg,
    imm: i64,
    admit_constmul_shift: ConstMulShiftAdmit,
) -> Option<PeepholeEdit> {
    let width: u32 = match dst.class {
        RegClass::Gpr64 => 64,
        RegClass::Gpr32 => 32,
        _ => return None,
    };
    // Sign-extend at the OPERATION width: a 32-bit `-3` arrives as the
    // zero-extended `0xFFFF_FFFD`; reading it as `-3` finds the compact
    // decomposition. `x * c ≡ x * (c mod 2^W) (mod 2^W)`, so re-signing the low
    // `W` bits is value-preserving (same re-signing as `mul_shift_reduce`).
    let c: i128 = if width == 32 {
        i128::from(imm as i32)
    } else {
        i128::from(imm)
    };
    let (a, plus_one) = constmul_shift_decompose(c, width)?;
    // FAIL-CLOSED on the algebraic obligation: no discharge, no rewrite.
    if !admit_constmul_shift(width, a, plus_one) {
        return None;
    }
    let shl = X86ISelInst::new(
        X86Opcode::ShlRI,
        vec![
            X86ISelOperand::VReg(dst),
            X86ISelOperand::VReg(src),
            X86ISelOperand::Imm(i64::from(a)),
        ],
    );
    let combine = X86ISelInst::new(
        if plus_one {
            X86Opcode::AddRR
        } else {
            X86Opcode::SubRR
        },
        vec![
            X86ISelOperand::VReg(dst),
            X86ISelOperand::VReg(dst),
            X86ISelOperand::VReg(src),
        ],
    );
    Some(PeepholeEdit::ReplaceTwo(shl, combine))
}

/// `dst = src + src*scale` — the single-LEA form of `src * (scale+1)` for
/// scale in {2, 4, 8}.
fn lea_sib_scaled(dst: VReg, src: VReg, scale: u8) -> X86ISelInst {
    debug_assert!(matches!(scale, 2 | 4 | 8));
    X86ISelInst::new(
        X86Opcode::LeaSib,
        vec![
            X86ISelOperand::VReg(dst),
            X86ISelOperand::SibMemAddr {
                base: Box::new(X86ISelOperand::VReg(src)),
                index: Box::new(X86ISelOperand::VReg(src)),
                scale,
                disp: 0,
            },
        ],
    )
}

fn lea_sib_double(dst: VReg, src: VReg) -> X86ISelInst {
    X86ISelInst::new(
        X86Opcode::LeaSib,
        vec![
            X86ISelOperand::VReg(dst),
            X86ISelOperand::SibMemAddr {
                base: Box::new(X86ISelOperand::VReg(src)),
                index: Box::new(X86ISelOperand::VReg(src)),
                scale: 1,
                disp: 0,
            },
        ],
    )
}

fn movrr_or_remove(dst: VReg, src: VReg) -> PeepholeEdit {
    if dst == src {
        PeepholeEdit::Remove
    } else {
        PeepholeEdit::Replace(X86ISelInst::new(
            movrr_opcode_for_class(dst.class),
            vec![X86ISelOperand::VReg(dst), X86ISelOperand::VReg(src)],
        ))
    }
}

fn movrr_opcode_for_class(class: RegClass) -> X86Opcode {
    match class {
        RegClass::Gpr32 => X86Opcode::MovRR32,
        _ => X86Opcode::MovRR,
    }
}

fn xorrr_zero(dst: VReg) -> X86ISelInst {
    X86ISelInst::new(
        X86Opcode::XorRR,
        vec![X86ISelOperand::VReg(dst), X86ISelOperand::VReg(dst)],
    )
}

fn is_canonical_two_operand_xor_zero(inst: &X86ISelInst) -> bool {
    matches!(
        inst.operands.as_slice(),
        [X86ISelOperand::VReg(dst), X86ISelOperand::VReg(src)] if dst == src
    )
}

fn not_vreg(dst: VReg) -> X86ISelInst {
    X86ISelInst::new(X86Opcode::Not, vec![X86ISelOperand::VReg(dst)])
}

fn neg_vreg(dst: VReg) -> X86ISelInst {
    X86ISelInst::new(X86Opcode::Neg, vec![X86ISelOperand::VReg(dst)])
}

fn inc_vreg(dst: VReg) -> X86ISelInst {
    X86ISelInst::new(X86Opcode::Inc, vec![X86ISelOperand::VReg(dst)])
}

fn dec_vreg(dst: VReg) -> X86ISelInst {
    X86ISelInst::new(X86Opcode::Dec, vec![X86ISelOperand::VReg(dst)])
}

fn is_safe_local_candidate(inst: &X86ISelInst) -> bool {
    let flags = inst.flags;

    x86_inst_effect(inst).is_pure()
        && !flags.is_call()
        && !flags.is_branch()
        && !flags.is_terminator()
        && !flags.is_return()
        && !flags.has_side_effects()
        && !flags.reads_memory()
        && !flags.writes_memory()
        && !flags.is_pseudo()
        && !matches!(
            inst.opcode,
            X86Opcode::Phi | X86Opcode::StackAlloc | X86Opcode::Nop
        )
}

fn is_safe_flag_preserving_candidate(inst: &X86ISelInst) -> bool {
    let flags = inst.flags;
    let is_supported_identity = match inst.opcode {
        X86Opcode::CmpRI | X86Opcode::CmpRI8 => cmp_zero_vreg(inst).is_some(),
        X86Opcode::TestRI => test_ri_all_ones_vreg(inst).is_some(),
        _ => false,
    };

    is_supported_identity
        && inst.flags == inst.opcode.default_flags()
        && x86_inst_effect(inst).is_pure()
        && !flags.is_call()
        && !flags.is_branch()
        && !flags.is_terminator()
        && !flags.is_return()
        && !flags.reads_memory()
        && !flags.writes_memory()
        && !flags.is_pseudo()
}

fn can_replace_flag_writer(insts: &[X86ISelInst], index: usize) -> bool {
    match condition_flag_overwrite(&insts[index]) {
        FlagOverwrite::None => true,
        FlagOverwrite::Partial => false,
        FlagOverwrite::Full => flags_written_here_are_dead(insts, index),
    }
}

/// Forensic opt-out that reverts `flags_written_here_are_dead` to bailing at a
/// PARTIAL flag overwrite.
///
/// NOT memoized: like every other kill switch here it must stay observable to
/// an in-process flip (cf. `x86_tied_copy_elide_kill_switch_reverts_the_arm`
/// in the codegen pipeline, which pins exactly that contract). Instead the
/// read is HOISTED out of the scan below — it used to sit inside the loop
/// body, one `getenv` per scanned instruction, i.e. O(n^2) environment scans
/// per block in the worst case.
fn strict_partial_flags_enabled() -> bool {
    std::env::var_os("TCG_X86_STRICT_PARTIAL_FLAGS").is_some()
}

fn flags_written_here_are_dead(insts: &[X86ISelInst], index: usize) -> bool {
    let strict_partial = strict_partial_flags_enabled();
    for inst in &insts[index + 1..] {
        if x86_reads_flags(inst.opcode) {
            return false;
        }

        match condition_flag_overwrite(inst) {
            // A PARTIAL flag writer reads nothing and only shrinks the set
            // of insts[index]'s flags still observable, so the scan may
            // continue through it: the deadness claim still rests on
            // reaching a FULL overwrite before any reader. (Bailing here
            // was fail-closed but over-conservative — a RolRI emitted by
            // our own rotate_idiom sat between p5's ImulRRI $7 and its
            // XorRR full overwrite, vetoing the constmul reduction on the
            // loop-carried critical path.) TCG_X86_STRICT_PARTIAL_FLAGS
            // reverts to the old bail for isolation A/Bs.
            FlagOverwrite::Partial if strict_partial => {
                return false;
            }
            FlagOverwrite::None | FlagOverwrite::Partial => {}
            FlagOverwrite::Full => return true,
        }

        if instruction_may_export_flags(inst) {
            return false;
        }
    }

    false
}

/// Whether the RFLAGS an `ImulRRI` at `insts[index]` writes are dead, for
/// its strength reductions: [`flags_written_here_are_dead`], except that a
/// plain store ([`is_plain_store_keeping_flags`]) does not end the scan.
/// `flags_written_here_are_dead` stops at every instruction with side
/// effects, and every store carries `HAS_SIDE_EFFECTS`; a `MOV` store neither
/// reads nor writes RFLAGS and transfers no control, so the flags stay
/// exactly as observable after it as before it, and the deadness claim still
/// needs a FULL overwrite before any reader, control transfer or other
/// side-effecting instruction. Measured case: TY's `ty_bfs_kernel` stores
/// between `y * 2` and the next full flag writer.
fn imul_flags_are_dead(insts: &[X86ISelInst], index: usize) -> bool {
    let strict_partial = strict_partial_flags_enabled();
    for inst in &insts[index + 1..] {
        if x86_reads_flags(inst.opcode) {
            return false;
        }
        match condition_flag_overwrite(inst) {
            FlagOverwrite::Partial if strict_partial => return false,
            FlagOverwrite::None | FlagOverwrite::Partial => {}
            FlagOverwrite::Full => return true,
        }
        if instruction_may_export_flags(inst) && !is_plain_store_keeping_flags(inst) {
            return false;
        }
    }
    false
}

/// A non-volatile `MOV` store (GPR, scalar FP or vector, any addressing
/// form) that is not also a call, branch, terminator or return. Such an
/// instruction neither reads nor writes RFLAGS. Volatile stores and every
/// other side-effecting instruction keep ending the scan.
fn is_plain_store_keeping_flags(inst: &X86ISelInst) -> bool {
    use X86Opcode::*;
    let flags = inst.flags;
    matches!(
        inst.opcode,
        MovMR8
            | MovMR16
            | MovMR32
            | MovMR
            | MovMRSib
            | MovMR8Sib
            | MovMR32Sib
            | MovsdMR
            | MovssMR
            | MovdquMR
            | MovdquMRSib
            | MovdqaMR
    ) && !flags.is_call()
        && !flags.is_branch()
        && !flags.is_terminator()
        && !flags.is_return()
}

fn instruction_may_export_flags(inst: &X86ISelInst) -> bool {
    let flags = inst.flags;

    flags.is_call()
        || flags.is_branch()
        || flags.is_terminator()
        || flags.is_return()
        || flags.has_side_effects()
}

fn same_supported_class(lhs: VReg, rhs: VReg) -> bool {
    lhs.class == rhs.class && is_supported_gpr(lhs) && is_supported_gpr(rhs)
}

fn is_supported_gpr(vreg: VReg) -> bool {
    matches!(vreg.class, RegClass::Gpr64 | RegClass::Gpr32)
}

// ---------------------------------------------------------------------------
// Immediate folding: MovRI + ALU-RR consumer -> ALU-RI
// ---------------------------------------------------------------------------

/// Fold a uniquely-defined `MovRI vreg, imm` constant into the immediate slot
/// of its ALU consumers: `AndRR/AddRR/SubRR d, l, v` becomes
/// `AndRI/AddRI/SubRI d, l, imm`, `CmpRR a, v` becomes `CmpRI a, imm`, and
/// `ImulRR d, l, v` becomes `ImulRRI d, l, imm`. ISel materializes EVERY
/// constant operand into a vreg; under register pressure the allocator spills
/// the constant, so a hot loop pays a stack reload per iteration for `x & 1`
/// where LLVM emits one `and $1`. This rewrite removes the register use;
/// the now-dead `MovRI` is cleaned up by the DCE pass that follows.
///
/// The constant may also be read through a chain of uniquely-defined plain
/// `MovRR` copies rooted at such a `MovRI` (the shape CSE leaves behind when
/// it canonicalizes duplicate constant materializations — see the chase loop
/// below): each copy provably holds the root immediate, so its consumers fold
/// identically. This is what lets the OPT-7 SIB address fold (further down in
/// this same peephole invocation) anchor on `imul idx, $8` scale-defs in
/// LICM+CSE-processed loop bodies.
///
/// Soundness:
///   * The constant vreg must have EXACTLY ONE def in the whole function
///     (counted conservatively: any instruction whose first operand is the
///     vreg counts as a def, whether or not the opcode really writes it —
///     over-counting only suppresses folds). With a single def, every
///     reachable use observes the same immediate value, so substituting the
///     immediate at any use is exact; the def site is not moved or removed.
///   * The immediate must be representable as a sign-extended imm32
///     (`imm == i64::from(imm as i32)`) — the encoder emits ALU imm32 forms
///     whose 64-bit semantics sign-extend, so this gate makes the folded form
///     bit-identical to the register form at both operand widths.
///   * Only the pure-source operand is folded (never the dst-also-src slot),
///     and only for opcodes whose RI form computes the identical result AND
///     identical RFLAGS as the RR form for equal operand values (same
///     hardware operation, immediate addressing mode) — no dead-flags
///     analysis is needed.
///   * For the commutative And/Add/Imul, a constant in the LHS slot is folded
///     by swapping the register operand into the LHS position.
///
/// Every emitted opcode (AndRI/AddRI/SubRI/CmpRI/ImulRRI) is already produced
/// by ISel on existing paths, so the per-instruction proof-certificate surface
/// and the encoder cover them; a gap would fail closed downstream, never
/// miscompile.
fn fold_unique_const_into_imm_forms(func: &mut X86ISelFunction) -> bool {
    // Conservative def counts: any first-operand vreg occurrence counts.
    let mut def_counts: FxHashMap<VReg, usize> = FxHashMap::default();
    for block_id in &func.block_order {
        let Some(block) = func.blocks.get(block_id) else {
            continue;
        };
        for inst in &block.insts {
            if let Some(X86ISelOperand::VReg(v)) = inst.operands.first() {
                *def_counts.entry(*v).or_insert(0) += 1;
            }
        }
    }

    // Collect uniquely-defined MovRI constants with imm32-representable values.
    let mut consts: FxHashMap<VReg, i64> = FxHashMap::default();
    for block_id in &func.block_order {
        let Some(block) = func.blocks.get(block_id) else {
            continue;
        };
        for inst in &block.insts {
            if inst.opcode != X86Opcode::MovRI || inst.operands.len() != 2 {
                continue;
            }
            let (Some(X86ISelOperand::VReg(v)), Some(X86ISelOperand::Imm(imm))) =
                (inst.operands.first(), inst.operands.get(1))
            else {
                continue;
            };
            if def_counts.get(v).copied() == Some(1)
                && is_supported_gpr(*v)
                && *imm == i64::from(*imm as i32)
            {
                consts.insert(*v, *imm);
            }
        }
    }
    if consts.is_empty() {
        return false;
    }

    // See through uniquely-defined `MovRR` copies of a proven constant. CSE
    // canonicalizes duplicate `MovRI k` materializations into `MovRR` copies
    // of one canonical constant vreg (and LICM hoists the whole group out of
    // loops), so a loop-body ALU consumer typically reads the constant
    // through such a copy:
    //
    //   preheader:  c = mov $8      ; MovRI root (single def)
    //               t = mov c       ; MovRR copy (CSE-inserted, single def)
    //   loop body:  d = imul x, t   ; consumer — foldable to `imul x, $8`
    //
    // Soundness: `t`'s ONLY definition in the whole function (same
    // conservative def count as above) is a plain default-flags register
    // copy whose source is itself a uniquely-defined constant, chased
    // transitively to a single-def `MovRI` root. A single-def vreg has one
    // static value assignment, so any read of `t` that observes a defined
    // value observes exactly the root immediate (definite initialization at
    // the original reads is the frontend's existing obligation and is
    // unchanged — no def is moved or removed here, and no new read is
    // introduced). Substituting the immediate at a use is therefore exact.
    //
    // Termination: the fixpoint only ever grows `consts` with vregs whose
    // sole def copies an existing member, so copy cycles (which have no
    // `MovRI` root) never enter, and each pass either adds a vreg or stops —
    // bounded by the number of copy instructions.
    loop {
        let mut grew = false;
        for block_id in &func.block_order {
            let Some(block) = func.blocks.get(block_id) else {
                continue;
            };
            for inst in &block.insts {
                if inst.opcode != X86Opcode::MovRR || inst.flags != X86Opcode::MovRR.default_flags()
                {
                    continue;
                }
                let [X86ISelOperand::VReg(d), X86ISelOperand::VReg(s)] = inst.operands.as_slice()
                else {
                    continue;
                };
                if d.class == RegClass::Gpr64
                    && s.class == RegClass::Gpr64
                    && def_counts.get(d).copied() == Some(1)
                    && !consts.contains_key(d)
                    && let Some(imm) = consts.get(s).copied()
                {
                    consts.insert(*d, imm);
                    grew = true;
                }
            }
        }
        if !grew {
            break;
        }
    }

    let const_imm = |op: &X86ISelOperand| -> Option<i64> {
        match op {
            X86ISelOperand::VReg(v) => consts.get(v).copied(),
            _ => None,
        }
    };

    let mut changed = false;
    let block_ids = func.block_order.clone();
    for block_id in block_ids {
        let Some(block) = func.blocks.get_mut(&block_id) else {
            continue;
        };
        for inst in &mut block.insts {
            match inst.opcode {
                // Three-address commutative ALU: [dst, lhs, rhs].
                X86Opcode::AndRR | X86Opcode::AddRR | X86Opcode::ImulRR
                    if inst.operands.len() == 3 =>
                {
                    let ri = match inst.opcode {
                        X86Opcode::AndRR => X86Opcode::AndRI,
                        X86Opcode::AddRR => X86Opcode::AddRI,
                        _ => X86Opcode::ImulRRI,
                    };
                    if let Some(imm) = const_imm(&inst.operands[2]) {
                        inst.opcode = ri;
                        inst.operands[2] = X86ISelOperand::Imm(imm);
                        changed = true;
                    } else if let Some(imm) = const_imm(&inst.operands[1]) {
                        // Commutative: swap the register operand into the LHS
                        // slot, fold the constant into the immediate slot.
                        inst.opcode = ri;
                        inst.operands[1] = inst.operands[2].clone();
                        inst.operands[2] = X86ISelOperand::Imm(imm);
                        changed = true;
                    }
                }
                // Three-address subtraction: only the RHS is foldable.
                X86Opcode::SubRR if inst.operands.len() == 3 => {
                    if let Some(imm) = const_imm(&inst.operands[2]) {
                        inst.opcode = X86Opcode::SubRI;
                        inst.operands[2] = X86ISelOperand::Imm(imm);
                        changed = true;
                    }
                }
                // Compare: [a, b]; only the second operand is foldable.
                X86Opcode::CmpRR if inst.operands.len() == 2 => {
                    if let Some(imm) = const_imm(&inst.operands[1]) {
                        inst.opcode = X86Opcode::CmpRI;
                        inst.operands[1] = X86ISelOperand::Imm(imm);
                        changed = true;
                    }
                }
                _ => {}
            }
        }
    }
    changed
}

// ---------------------------------------------------------------------------
// Scaled-index (SIB) address-mode fold
//   imul index, {1,2,4,8}  ; scaled = index * scale     (or shl index, {0..3})
//   add  base, scaled      ; addr   = base + scaled
//   mov  r, [addr]         ; MovRM  (load)   ->  MovRMSib r, [base+index*scale]
//   mov  [addr], r         ; MovMR  (store)  ->  MovMRSib [base+index*scale], r
// ---------------------------------------------------------------------------
//
// x86-64 SIB addressing computes the effective address `base + index*scale +
// disp` inside a single load/store operand for scale in {1,2,4,8}. Generic
// trust_ir array indexing lowers as a separate integer multiply (or shift) to
// scale the index, an add to reach the element, and then a plain `[reg]`
// load/store — three instructions per element access, on the critical path of
// every loop iteration. This fold collapses the address computation into the
// memory operand, matching what LLVM (and a hand assembler) emit:
// `mov (%base,%index,8), %r`.
//
// The fold is *by construction* address-preserving: the SIB operand
// `base + index*scale + 0` is the byte-exact effective address the deleted
// `add` produced from `imul/shl`. It only ever fires on the exact opcodes and
// operand shapes below; anything unrecognized is left UNFOLDED (plain MemAddr),
// never miscompiled. `select_array_gep` already emits this very
// `X86ISelOperand::SibMemAddr` shape for LeaSib, so the whole downstream path
// (regalloc SIB resolution, encoder, decode_check, lowering certs) is exercised
// and re-verified per-compile on every emitted MovRMSib/MovMRSib instance.
//
// HAND-PROOF (semantic equivalence):
//   - The scale-def computes `scaled = index * scale`, with scale a power of
//     two in {1,2,4,8}. For `ImulRRI [scaled, index, k]` that is `index * k`
//     directly; for `ShlRI [scaled, index, sh]` (sh in 0..=3) that is
//     `index << sh = index * 2^sh` (no shift-count wrap, and the SIB scale is
//     exactly `1 << sh`). x86 `imul`/`shl` produce the low 64 bits of the
//     mathematical product, and SIB scaling likewise computes `index*scale`
//     modulo 2^64, so the two coincide bit-for-bit.
//   - The add computes `addr = base + scaled` (mod 2^64), the same value the
//     SIB unit forms as `base + index*scale`.
//   - The memory op dereferences `[addr + 0]`; the rewritten op dereferences
//     `[base + index*scale + 0]`. Same address, same access width, same value.
//
// SIDE CONDITIONS (each must hold or the fold is skipped):
//   1. The scale-def is `ImulRRI [scaled, index, k]` with k in {1,2,4,8}, OR
//      `ShlRI [scaled, index, sh]` with sh in {0,1,2,3}. Both at opcode-default
//      flags, no memory side effects, `scaled`/`index` supported Gpr64 vregs.
//   2. The add is `AddRR [addr, X, Y]` (three-address ISel form) where {X,Y} =
//      {base, scaled} in either order (ADD is commutative). `base` is a
//      supported Gpr64 vreg distinct from `scaled`; `addr`/`base` are Gpr64.
//      Default flags, no memory side effects.
//   3. The memory op is a `MovRM`/`MovMR` (64-bit) or `MovRM32`/`MovMR32`
//      (32-bit, X10) `[addr + 0]` load/store with the base VReg equal to
//      `addr` and disp == 0. The rewrite preserves the access width exactly
//      (MovRMSib/MovMRSib are the REX.W forms; MovRM32Sib/MovMR32Sib the
//      32-bit forms with identical zero-extension/store semantics);
//      8/16-bit and float forms are left alone.
//   4. Program order within the block: scale-def precedes add precedes memory
//      op. `base`, `index` are not redefined between their producer and the
//      memory op (guaranteed by the single-def / single-use guards plus the
//      no-intervening-redef check).
//   5. `scaled` is defined exactly once (by the scale-def) and used exactly
//      once (by the add) across the whole function. `addr` is defined exactly
//      once (by the add) and used exactly once (by the memory op) across the
//      whole function. This makes deleting the scale-def and add invisible.
//   6. The RFLAGS written by the deleted scale-def and add are DEAD (no reader
//      before the next full overwrite). `imul`/`shl`/`add` all clobber RFLAGS;
//      MovRMSib/MovMRSib do not, so we may only erase these flag writers when
//      nothing downstream consumes the flags they produced.
//   7. `index != base` is NOT required (SIB permits base==index); but the SIB
//      index register is never RSP because these are pre-regalloc vregs and
//      regalloc never assigns RSP to an ordinary vreg.
//
// PROOF PROVENANCE: hand-proved peephole. The rewritten load/store keeps its
// own `proof_origin`, so source-location reporting is unchanged.

/// One memory op (load or store) on the shared `[addr + 0]` to rewrite to SIB.
#[derive(Debug, Clone)]
struct SibMemRewrite {
    mem_idx: usize,
    new_opcode: X86Opcode,
    /// dst for a load, src for a store — carried through unchanged.
    value_operand: X86ISelOperand,
    is_load: bool,
}

/// A whole fold: an `imul/shl` scale-def + an `AddRR` address-def, plus every
/// memory op on the resulting address that gets rewritten to a SIB operand.
#[derive(Debug)]
struct SibAddrFoldEdit {
    /// Index of the imul/shl scale-def (to delete), or `None` for a SCALE-1
    /// address (`base + index`), where there is no scale-def to begin with —
    /// see the scale-1 arm of `try_sib_addr_fold_from_add`.
    scale_def_idx: Option<usize>,
    /// Index of the AddRR address-def (to delete).
    add_idx: usize,
    /// Shared SIB memory operand `base + index*scale + 0`.
    sib: X86ISelOperand,
    /// The memory ops (>=1) on the address, each rewritten to carry `sib`.
    mem_rewrites: Vec<SibMemRewrite>,
    /// Indices of pure `MovRR [t, addr]` address copies that become dead once
    /// the mem ops carry the SIB operand directly (also deleted).
    copy_deletes: Vec<usize>,
}

/// The whole-function VReg use/def counts, packaged with the `use_count` /
/// `def_count` accessors their consumers expect.
///
/// Field-for-field EXACTLY `function_use_def_counts`: `vreg_uses_in_block`'s
/// use convention, and "operand 0 of a value-producing opcode" for defs.
/// [`SibFoldVRegMaps`] holds one for its counts. Existing as a named type
/// lets ONE build serve several consumers instead of each pass rebuilding its
/// own copy.
///
/// A PURE function of `func`, so a built copy stays exactly correct until
/// `func` is next mutated — and no longer. Callers that hold one across a
/// rewrite MUST drop it; see the cache discipline in `run_impl`.
pub(crate) struct FnUseDefCounts {
    uses: FxHashMap<VReg, u32>,
    defs: FxHashMap<VReg, u32>,
}

impl FnUseDefCounts {
    fn build(func: &X86ISelFunction) -> Self {
        let (uses, defs) = function_use_def_counts(func);
        FnUseDefCounts { uses, defs }
    }

    #[inline]
    fn def_count(&self, v: VReg) -> u32 {
        self.defs.get(&v).copied().unwrap_or(0)
    }

    #[inline]
    fn use_count(&self, v: VReg) -> u32 {
        self.uses.get(&v).copied().unwrap_or(0)
    }

    /// Every count, rendered and sorted, so two builds compare as values.
    #[cfg(any(test, debug_assertions))]
    fn canonical_view(&self) -> [Vec<String>; 2] {
        [
            sorted_debug_entries(&self.uses),
            sorted_debug_entries(&self.defs),
        ]
    }
}

/// Whole-function VReg maps precomputed ONCE per `sib_addr_fold_run_on_block`
/// invocation, replacing the per-anchor whole-function scans that made the
/// pass O(n^2) on a single large function (matmul's 15920-inst body).
///
/// `func` is IMMUTABLE across the entire anchor loop — all edits are collected
/// into a `Vec` and applied only AFTER the loop — so every per-anchor
/// whole-function def count / use count / cross-block escape
/// scan returns the IDENTICAL answer within one invocation. Precomputing them
/// once yields the SAME verdicts and therefore the SAME edit set (byte-
/// identical codegen). The maps MUST be rebuilt per invocation (the function
/// DOES mutate between block invocations via the end-of-loop edits) and MUST
/// NOT be hoisted across invocations.
struct SibFoldVRegMaps {
    /// Function-wide definition and use counts: `function_vreg_def_count`'s
    /// predicate for defs, `vreg_uses_in_block`'s convention (which reads
    /// addressing regs inside memory operands too) for uses.
    counts: FnUseDefCounts,
    /// For each VReg, the distinct blocks that MENTION it (any operand, per
    /// `instruction_mentions_vreg`). A VReg no block mentions has no entry or
    /// an empty list; the two read the same.
    mention_blocks: FxHashMap<VReg, Vec<trust_cg_lower::instructions::Block>>,
}

/// One block's part of [`SibFoldVRegMaps`]: its instructions' use and def
/// counts, and the VRegs it mentions.
struct SibFoldBlockPart {
    uses: FxHashMap<VReg, u32>,
    defs: FxHashMap<VReg, u32>,
    mentions: FxHashSet<VReg>,
}

impl SibFoldBlockPart {
    /// The part of `block_id` as `func` holds it now (empty for a missing
    /// block, which contributes nothing to a build either).
    fn of(func: &X86ISelFunction, block_id: trust_cg_lower::instructions::Block) -> Self {
        let mut part = SibFoldBlockPart {
            uses: FxHashMap::default(),
            defs: FxHashMap::default(),
            mentions: FxHashSet::default(),
        };
        if let Some(block) = func.blocks.get(&block_id) {
            for inst in &block.insts {
                count_inst_uses_defs(inst, &mut part.uses, &mut part.defs);
                for op in &inst.operands {
                    collect_operand_mentions_flat(op, &mut part.mentions);
                }
            }
        }
        part
    }
}

impl SibFoldVRegMaps {
    /// Build the maps in two O(n) passes over every block/inst.
    fn build(func: &X86ISelFunction) -> Self {
        let counts = FnUseDefCounts::build(func);
        let mut mention_blocks: FxHashMap<VReg, Vec<trust_cg_lower::instructions::Block>> =
            FxHashMap::default();
        for (bid, block) in &func.blocks {
            for inst in &block.insts {
                // Every VReg any operand mentions (same predicate as
                // `instruction_mentions_vreg`).
                for op in &inst.operands {
                    collect_operand_mentions(op, *bid, &mut mention_blocks);
                }
            }
        }
        SibFoldVRegMaps {
            counts,
            mention_blocks,
        }
    }

    /// Replace `block_id`'s part `before` by its part `after`: the maps then
    /// equal a [`SibFoldVRegMaps::build`] of the function whose only change is
    /// that block, up to entries that read as absent (a zero count, an empty
    /// mention list).
    fn replace_block_part(
        &mut self,
        block_id: trust_cg_lower::instructions::Block,
        before: &SibFoldBlockPart,
        after: &SibFoldBlockPart,
    ) {
        fn shift(
            counts: &mut FxHashMap<VReg, u32>,
            before: &FxHashMap<VReg, u32>,
            after: &FxHashMap<VReg, u32>,
        ) {
            for (v, n) in before {
                let entry = counts.entry(*v).or_insert(0);
                *entry = entry
                    .checked_sub(*n)
                    .expect("a block's counts are part of the function's");
            }
            for (v, n) in after {
                *counts.entry(*v).or_insert(0) += *n;
            }
        }
        shift(&mut self.counts.uses, &before.uses, &after.uses);
        shift(&mut self.counts.defs, &before.defs, &after.defs);
        for v in before.mentions.difference(&after.mentions) {
            if let Some(blocks) = self.mention_blocks.get_mut(v) {
                blocks.retain(|b| *b != block_id);
            }
        }
        for v in after.mentions.difference(&before.mentions) {
            let blocks = self.mention_blocks.entry(*v).or_default();
            if !blocks.contains(&block_id) {
                blocks.push(block_id);
            }
        }
    }

    /// The maps' entries that a reader can tell apart (`use_count`,
    /// `def_count`, `escapes`): non-zero counts and the set of mentioning
    /// blocks, in a canonical order.
    #[cfg(any(test, debug_assertions))]
    fn canonical_view(&self) -> (Vec<String>, Vec<String>, Vec<String>) {
        let counts = |m: &FxHashMap<VReg, u32>| {
            let mut v: Vec<String> = m
                .iter()
                .filter(|(_, n)| **n != 0)
                .map(|(k, n)| format!("{k:?}={n}"))
                .collect();
            v.sort();
            v
        };
        let mut mentions: Vec<String> = self
            .mention_blocks
            .iter()
            .filter(|(_, blocks)| !blocks.is_empty())
            .map(|(k, blocks)| {
                let mut b: Vec<u32> = blocks.iter().map(|b| b.0).collect();
                b.sort_unstable();
                format!("{k:?}:{b:?}")
            })
            .collect();
        mentions.sort();
        (
            counts(&self.counts.uses),
            counts(&self.counts.defs),
            mentions,
        )
    }

    #[inline]
    fn def_count(&self, v: VReg) -> u32 {
        self.counts.def_count(v)
    }

    #[inline]
    fn use_count(&self, v: VReg) -> u32 {
        self.counts.use_count(v)
    }

    /// True iff `v` is mentioned in any block other than `block_id`. Replaces
    /// `func.blocks.iter().any(|(id, b)| id != block_id && b.insts.iter()
    /// .any(|i| instruction_mentions_vreg(i, v)))`.
    #[inline]
    fn escapes(&self, v: VReg, block_id: trust_cg_lower::instructions::Block) -> bool {
        // The list holds DISTINCT blocks, so two entries cannot both be
        // `block_id`.
        match self.mention_blocks.get(&v).map(Vec::as_slice) {
            None | Some([]) => false,
            Some([only]) => *only != block_id,
            Some(_) => true,
        }
    }
}

/// Record, into `mention_blocks`, that block `bid` mentions every VReg
/// referenced by `op` (walking `MemAddr`/`SibMemAddr` addressing regs) —
/// mirroring `operand_mentions_vreg`/`instruction_mentions_vreg`.
fn collect_operand_mentions(
    op: &X86ISelOperand,
    bid: trust_cg_lower::instructions::Block,
    mention_blocks: &mut FxHashMap<VReg, Vec<trust_cg_lower::instructions::Block>>,
) {
    match op {
        X86ISelOperand::VReg(v) => {
            // A block's instructions are visited together, so the last entry
            // is the only one that can already be `bid`: the list stays a
            // list of distinct blocks.
            let blocks = mention_blocks.entry(*v).or_default();
            if blocks.last() != Some(&bid) {
                blocks.push(bid);
            }
        }
        X86ISelOperand::MemAddr { base, .. } => {
            collect_operand_mentions(base, bid, mention_blocks);
        }
        X86ISelOperand::SibMemAddr { base, index, .. } => {
            collect_operand_mentions(base, bid, mention_blocks);
            collect_operand_mentions(index, bid, mention_blocks);
        }
        _ => {}
    }
}

/// Build the whole-function maps and fold one block. Equivalent to
/// [`sib_addr_fold_run_on_block_with_maps`] with a freshly built map set; kept
/// for the unit tests, which exercise one block of a fixed function.
#[cfg(test)]
fn sib_addr_fold_run_on_block(
    func: &mut X86ISelFunction,
    block_id: trust_cg_lower::instructions::Block,
) -> bool {
    let maps = SibFoldVRegMaps::build(func);
    sib_addr_fold_run_on_block_with_maps(func, block_id, &maps)
}

fn sib_addr_fold_run_on_block_with_maps(
    func: &mut X86ISelFunction,
    block_id: trust_cg_lower::instructions::Block,
    // Whole-function VReg maps for the CURRENT state of `func`. `func` is
    // immutable across the anchor loop below, so these replace the O(n)
    // per-anchor scans that made the loop O(n^2), with byte-identical results.
    //
    // The caller owns the lifetime because `SibFoldVRegMaps::build` is a pure
    // function of `func` and this routine mutates `func` ONLY when it returns
    // `true` (see the `edits.is_empty()` early return below). The caller may
    // therefore reuse one build across consecutive blocks that changed
    // nothing and rebuild the instant one does — handing every block exactly
    // the maps `build(func)` would have produced at that point, which is what
    // keeps the emitted bytes identical to the per-block rebuild.
    maps: &SibFoldVRegMaps,
) -> bool {
    let Some(block) = func.blocks.get(&block_id) else {
        return false;
    };
    // The anchor scan only reads `func`; every edit owns its operands.
    let insts: &[X86ISelInst] = &block.insts;

    let mut edits: Vec<SibAddrFoldEdit> = Vec::new();
    let mut consumed: FxHashSet<usize> = FxHashSet::default();

    // Anchor on each address-producing instruction feeding memory ops:
    //   (1) `LeaSib d, [base+index*scale+disp]` (already a formed SIB address,
    //       e.g. from `select_array_gep`) — the primary array-indexing case.
    //   (2) `imul/shl` + `AddRR` (a materialized base+index*scale, when the
    //       address was lowered as generic integer arithmetic).
    // Deleting the address producer is attempted once, so anchoring on the
    // producer (not each memory op) naturally handles a load+store that share
    // one address (`c[i] = c[i] + ..`).
    for anchor_idx in 0..insts.len() {
        if consumed.contains(&anchor_idx) {
            continue;
        }
        let edit = try_sib_addr_fold_from_leasib(block_id, insts, anchor_idx, maps)
            .or_else(|| try_sib_addr_fold_from_add(block_id, insts, anchor_idx, maps));
        if let Some(edit) = edit {
            if let Some(scale_def_idx) = edit.scale_def_idx {
                consumed.insert(scale_def_idx);
            }
            consumed.insert(edit.add_idx);
            for r in &edit.mem_rewrites {
                consumed.insert(r.mem_idx);
            }
            for &c in &edit.copy_deletes {
                consumed.insert(c);
            }
            edits.push(edit);
        }
    }

    if edits.is_empty() {
        return false;
    }

    // Rewrite every memory op in place, then delete the scale-def + add of each
    // fired edit in descending index order so earlier indices stay valid.
    let mut to_delete: Vec<usize> = Vec::new();
    // `sib_addr_fold_run_on_block` opens with
    // `let Some(block) = func.blocks.get(&block_id) else { return false }`;
    // the anchor scan between there and here only reads `func`.
    let block = func.blocks.get_mut(&block_id).expect("block existed above");
    for edit in &edits {
        for r in &edit.mem_rewrites {
            let mem = &mut block.insts[r.mem_idx];
            mem.opcode = r.new_opcode;
            mem.flags = r.new_opcode.default_flags();
            mem.operands = if r.is_load {
                vec![r.value_operand.clone(), edit.sib.clone()]
            } else {
                vec![edit.sib.clone(), r.value_operand.clone()]
            };
        }
        if let Some(scale_def_idx) = edit.scale_def_idx {
            to_delete.push(scale_def_idx);
        }
        to_delete.push(edit.add_idx);
        for &c in &edit.copy_deletes {
            to_delete.push(c);
        }
    }
    to_delete.sort_unstable();
    to_delete.dedup();
    for idx in to_delete.into_iter().rev() {
        block.insts.remove(idx);
    }

    true
}

/// SIB scale for an `ImulRRI`/`ShlRI` scale-def, or `None` if it is not a
/// power-of-two-scale shape encodable as an x86 SIB scale.
///
/// Returns `(scale, index_vreg)` where `scale in {1,2,4,8}`.
fn sib_scale_def(inst: &X86ISelInst) -> Option<(u8, VReg)> {
    match inst.opcode {
        X86Opcode::ImulRRI => {
            // [scaled, index, Imm(k)]
            if inst.flags != X86Opcode::ImulRRI.default_flags() {
                return None;
            }
            match inst.operands.as_slice() {
                [
                    X86ISelOperand::VReg(_dst),
                    X86ISelOperand::VReg(index),
                    X86ISelOperand::Imm(k),
                ] => {
                    let scale = u8::try_from(*k).ok()?;
                    if matches!(scale, 1 | 2 | 4 | 8) && index.class == RegClass::Gpr64 {
                        Some((scale, *index))
                    } else {
                        None
                    }
                }
                _ => None,
            }
        }
        X86Opcode::ShlRI => {
            // [scaled, index, Imm(sh)]  (three-address form only)
            if inst.flags != X86Opcode::ShlRI.default_flags() {
                return None;
            }
            match inst.operands.as_slice() {
                [
                    X86ISelOperand::VReg(_dst),
                    X86ISelOperand::VReg(index),
                    X86ISelOperand::Imm(sh),
                ] => {
                    let scale: u8 = match sh {
                        0 => 1,
                        1 => 2,
                        2 => 4,
                        3 => 8,
                        _ => return None,
                    };
                    if index.class == RegClass::Gpr64 {
                        Some((scale, *index))
                    } else {
                        None
                    }
                }
                _ => None,
            }
        }
        _ => None,
    }
}

/// The defined VReg (operand 0) of a value-producing scale-def / add.
fn def_vreg(inst: &X86ISelInst) -> Option<VReg> {
    match inst.operands.first() {
        Some(X86ISelOperand::VReg(v)) => Some(*v),
        _ => None,
    }
}

/// Count total definitions of `vreg` (operand 0 of value-producing insts)
/// across the whole function. Uses the same predicate as
/// `SibFoldVRegMaps::def_count`, which the SIB fold precomputes in bulk
/// instead of calling this per anchor.
fn function_vreg_def_count(func: &X86ISelFunction, vreg: VReg) -> u32 {
    use crate::effects::x86_produces_value;
    let mut count = 0u32;
    for block in func.blocks.values() {
        for inst in &block.insts {
            if x86_produces_value(inst.opcode)
                && matches!(inst.operands.first(), Some(X86ISelOperand::VReg(v)) if *v == vreg)
            {
                count += 1;
            }
        }
    }
    count
}

/// Are the RFLAGS written by `insts[index]` dead — i.e. no later instruction
/// reads them before they are fully overwritten or the block ends?
///
/// This is the SIB-fold-specific variant of `flags_written_here_are_dead`. The
/// difference: a plain memory load/store neither reads nor exports RFLAGS, so
/// it is transparent here (the fusion-pass version conservatively bails on any
/// `has_side_effects()`, which a store carries via `WRITES_MEMORY`, and would
/// wrongly block folding a store's own address computation). We still bail on
/// genuine flag readers and on call/branch/terminator/return boundaries, past
/// which RFLAGS may be observed via the ABI or control flow. A `Full` overwrite
/// makes the earlier flags provably dead.
///
/// A `Partial` overwriter (imul/shl/...) is TRANSPARENT to this deadness
/// question. What we must prove is that no instruction ever OBSERVES the
/// deleted writer's flag output. Observation happens only through a flag
/// reader (the reader set is closed over the opcode enum:
/// `Cmovcc/Cmovcc32/Setcc/Jcc/AdcRR/SbbRR`, all caught by `x86_reads_flags`
/// above, `Jcc` additionally by the branch boundary) or past a control-flow /
/// ABI boundary (also caught above). A partial overwriter does neither: it
/// writes SOME flag bits as a function of its register operands (which the
/// fold does not change) and reads none. Any reader downstream of the next
/// `Full` overwrite observes only that overwriter's flags; any reader BEFORE
/// it still returns `false` here. So scanning through a partial overwrite,
/// looking only for readers / boundaries / the next full overwrite, is sound.
fn sib_fold_flags_dead(insts: &[X86ISelInst], index: usize) -> bool {
    for inst in &insts[index + 1..] {
        if x86_reads_flags(inst.opcode) {
            return false;
        }
        // Control-flow / ABI boundaries may expose RFLAGS.
        let flags = inst.flags;
        if flags.is_call() || flags.is_branch() || flags.is_terminator() || flags.is_return() {
            return false;
        }
        match condition_flag_overwrite(inst) {
            FlagOverwrite::None | FlagOverwrite::Partial => {}
            FlagOverwrite::Full => return true,
        }
    }
    // Fell off the end of the block without a full overwrite. Conservatively
    // treat the flags as potentially live-out and refuse.
    false
}

/// Recognize a plain 64-bit `MovRM`/`MovMR` on `[addr + 0]`. Returns
/// `(is_load, addr_vreg, value_operand, new_opcode)`.
/// Whether the scalar-FP arm of the SIB address fold is active. Default-ON;
/// `TCG_NO_X86_SIB_FP_FOLD` disables it so an A/B runs inside one dylib.
fn sib_fp_fold_enabled() -> bool {
    std::env::var_os("TCG_NO_X86_SIB_FP_FOLD").is_none()
}

fn sib_foldable_mem_op(inst: &X86ISelInst) -> Option<(bool, VReg, X86ISelOperand, X86Opcode)> {
    // A proof-origin-carrying MOV (a volatile/atomic load or store) keeps its
    // STRONGER AtomicLoad/AtomicStore proof and TSO-ordering semantics; folding
    // it into a plain MovRMSib/MovMRSib would drop that origin and re-route it to
    // the weaker plain-value memory proof. Never fold those — only plain
    // value-load/store MOVs (no proof origin) are foldable.
    if inst.proof_origin.is_some() {
        return None;
    }
    match inst.opcode {
        X86Opcode::MovRM => {
            if inst.flags != X86Opcode::MovRM.default_flags() {
                return None;
            }
            match inst.operands.as_slice() {
                [
                    dst @ X86ISelOperand::VReg(_),
                    X86ISelOperand::MemAddr { base, disp },
                ] if *disp == 0 => {
                    let X86ISelOperand::VReg(addr) = base.as_ref() else {
                        return None;
                    };
                    Some((true, *addr, dst.clone(), X86Opcode::MovRMSib))
                }
                _ => None,
            }
        }
        X86Opcode::MovMR => {
            if inst.flags != X86Opcode::MovMR.default_flags() {
                return None;
            }
            match inst.operands.as_slice() {
                [
                    X86ISelOperand::MemAddr { base, disp },
                    src @ X86ISelOperand::VReg(_),
                ] if *disp == 0 => {
                    let X86ISelOperand::VReg(addr) = base.as_ref() else {
                        return None;
                    };
                    Some((false, *addr, src.clone(), X86Opcode::MovMRSib))
                }
                _ => None,
            }
        }
        // 32-bit siblings (X10): identical shape, width fixed by the opcode —
        // the rewrite targets MovRM32Sib/MovMR32Sib, whose zero-extension /
        // store-width semantics exactly match MovRM32/MovMR32.
        X86Opcode::MovRM32 => {
            if inst.flags != X86Opcode::MovRM32.default_flags() {
                return None;
            }
            match inst.operands.as_slice() {
                [
                    dst @ X86ISelOperand::VReg(_),
                    X86ISelOperand::MemAddr { base, disp },
                ] if *disp == 0 => {
                    let X86ISelOperand::VReg(addr) = base.as_ref() else {
                        return None;
                    };
                    Some((true, *addr, dst.clone(), X86Opcode::MovRM32Sib))
                }
                _ => None,
            }
        }
        X86Opcode::MovMR32 => {
            if inst.flags != X86Opcode::MovMR32.default_flags() {
                return None;
            }
            match inst.operands.as_slice() {
                [
                    X86ISelOperand::MemAddr { base, disp },
                    src @ X86ISelOperand::VReg(_),
                ] if *disp == 0 => {
                    let X86ISelOperand::VReg(addr) = base.as_ref() else {
                        return None;
                    };
                    Some((false, *addr, src.clone(), X86Opcode::MovMR32Sib))
                }
                _ => None,
            }
        }
        // 8-bit siblings: the shape is identical once more and the access WIDTH
        // is fixed by the opcode, exactly as for the 32-bit pair. These are what
        // let a BYTE array participate in indexed addressing at all — the whole
        // `&[u8]` / `Vec<u8>` / `[u8; N]` class previously fell through here and
        // paid a base-`Lea` plus an `Add` on every single element access.
        X86Opcode::MovRM8 => {
            if inst.flags != X86Opcode::MovRM8.default_flags() {
                return None;
            }
            match inst.operands.as_slice() {
                [
                    dst @ X86ISelOperand::VReg(_),
                    X86ISelOperand::MemAddr { base, disp },
                ] if *disp == 0 => {
                    let X86ISelOperand::VReg(addr) = base.as_ref() else {
                        return None;
                    };
                    Some((true, *addr, dst.clone(), X86Opcode::MovRM8Sib))
                }
                _ => None,
            }
        }
        // The zero-extending byte load folds to its SIB sibling the same way:
        // same `[dst, [addr + 0]]` shape, width and extension fixed by the
        // opcode. There is no 16-bit SIB sibling, so `MovzxRM16` stays put.
        X86Opcode::MovzxRM8 => {
            if inst.flags != X86Opcode::MovzxRM8.default_flags() {
                return None;
            }
            match inst.operands.as_slice() {
                [
                    dst @ X86ISelOperand::VReg(_),
                    X86ISelOperand::MemAddr { base, disp },
                ] if *disp == 0 => {
                    let X86ISelOperand::VReg(addr) = base.as_ref() else {
                        return None;
                    };
                    Some((true, *addr, dst.clone(), X86Opcode::MovzxRM8Sib))
                }
                _ => None,
            }
        }
        X86Opcode::MovMR8 => {
            if inst.flags != X86Opcode::MovMR8.default_flags() {
                return None;
            }
            match inst.operands.as_slice() {
                [
                    X86ISelOperand::MemAddr { base, disp },
                    src @ X86ISelOperand::VReg(_),
                ] if *disp == 0 => {
                    let X86ISelOperand::VReg(addr) = base.as_ref() else {
                        return None;
                    };
                    Some((false, *addr, src.clone(), X86Opcode::MovMR8Sib))
                }
                _ => None,
            }
        }
        // Scalar-FP LOADS: identical shape again, width fixed by the opcode.
        // b11_float_dot pays three instructions per element access (imul/mov/add)
        // purely to form an address these can carry in their operand.
        //
        // LOADS ONLY. There is deliberately no MovsdMRSib/MovssMRSib opcode, so
        // MovsdMR/MovssMR must fall through to `None` here rather than be folded
        // into an opcode that does not exist.
        //
        // Kill switch (`TCG_NO_X86_SIB_FP_FOLD`) so the fold can be A/B'd inside a
        // SINGLE dylib. Comparing two separately-built dylibs across sweeps is not
        // a controlled experiment on this box — between-sweep ratio drift is
        // comparable to the effect being measured.
        X86Opcode::MovsdRM if sib_fp_fold_enabled() => {
            if inst.flags != X86Opcode::MovsdRM.default_flags() {
                return None;
            }
            match inst.operands.as_slice() {
                [
                    dst @ X86ISelOperand::VReg(_),
                    X86ISelOperand::MemAddr { base, disp },
                ] if *disp == 0 => {
                    let X86ISelOperand::VReg(addr) = base.as_ref() else {
                        return None;
                    };
                    Some((true, *addr, dst.clone(), X86Opcode::MovsdRMSib))
                }
                _ => None,
            }
        }
        X86Opcode::MovssRM if sib_fp_fold_enabled() => {
            if inst.flags != X86Opcode::MovssRM.default_flags() {
                return None;
            }
            match inst.operands.as_slice() {
                [
                    dst @ X86ISelOperand::VReg(_),
                    X86ISelOperand::MemAddr { base, disp },
                ] if *disp == 0 => {
                    let X86ISelOperand::VReg(addr) = base.as_ref() else {
                        return None;
                    };
                    Some((true, *addr, dst.clone(), X86Opcode::MovssRMSib))
                }
                _ => None,
            }
        }
        // PACKED 128-bit siblings: the same shape once more, with the access
        // width (128) fixed by the opcode exactly as it is for MovdquRM/MovdquMR.
        // BOTH directions are covered here, unlike the scalar-FP pair above:
        // `MovdquMRSib` exists (there is no MovsdMRSib), and the store is the
        // one that matters — the vectorizer's packed fill/copy bodies are stores.
        //
        // The ALIGNED family (MovdqaRM/MovdqaMR) is deliberately NOT folded: its
        // proof carries the honest `ea % 16 == 0` precondition, and moving the
        // address into a base+index*scale operand is exactly the rewrite that
        // could invalidate it (the fold does not know the index is a multiple of
        // 16). MOVDQU carries no alignment precondition, so the same rewrite is
        // unconditionally address-preserving there.
        X86Opcode::MovdquRM => {
            if inst.flags != X86Opcode::MovdquRM.default_flags() {
                return None;
            }
            match inst.operands.as_slice() {
                [
                    dst @ X86ISelOperand::VReg(_),
                    X86ISelOperand::MemAddr { base, disp },
                ] if *disp == 0 => {
                    let X86ISelOperand::VReg(addr) = base.as_ref() else {
                        return None;
                    };
                    Some((true, *addr, dst.clone(), X86Opcode::MovdquRMSib))
                }
                _ => None,
            }
        }
        X86Opcode::MovdquMR => {
            if inst.flags != X86Opcode::MovdquMR.default_flags() {
                return None;
            }
            match inst.operands.as_slice() {
                [
                    X86ISelOperand::MemAddr { base, disp },
                    src @ X86ISelOperand::VReg(_),
                ] if *disp == 0 => {
                    let X86ISelOperand::VReg(addr) = base.as_ref() else {
                        return None;
                    };
                    Some((false, *addr, src.clone(), X86Opcode::MovdquMRSib))
                }
                _ => None,
            }
        }
        _ => None,
    }
}

/// If `ptr` is used (function-wide) ONLY as the base of foldable 64-bit
/// `[ptr + 0]` load/stores in the SAME block, all occurring after `after_idx`,
/// return the SIB rewrites for them. Otherwise `None`. This models a copied
/// address pointer whose only consumers are memory ops we can fold.
fn collect_pointer_mem_ops(
    insts: &[X86ISelInst],
    ptr: VReg,
    after_idx: usize,
    maps: &SibFoldVRegMaps,
) -> Option<Vec<SibMemRewrite>> {
    // ptr must be defined exactly once (the copy) function-wide.
    if maps.def_count(ptr) != 1 {
        return None;
    }
    let total = maps.use_count(ptr);
    if total == 0 {
        return None;
    }
    let mut rewrites = Vec::new();
    let mut matched = 0u32;
    for (i, inst) in insts.iter().enumerate() {
        let uses_here = vreg_uses_in_inst(inst, ptr);
        if uses_here == 0 {
            continue;
        }
        matched += uses_here;
        match sib_foldable_mem_op(inst) {
            Some((is_load, base, value_operand, new_opcode))
                if base == ptr && uses_here == 1 && i > after_idx =>
            {
                rewrites.push(SibMemRewrite {
                    mem_idx: i,
                    new_opcode,
                    value_operand,
                    is_load,
                });
            }
            _ => return None,
        }
    }
    // All function-wide uses of ptr must be the mem ops we just folded (no
    // out-of-block reader, no arithmetic use).
    if matched != total || rewrites.is_empty() {
        return None;
    }
    Some(rewrites)
}

/// Collect every foldable [ptr+0] 64-bit mem op on `ptr`, seeing through a
/// single pure `MovRR [t, ptr]` copy. Returns `(mem_rewrites, copy_deletes)` if
/// EVERY function-wide use of `ptr` (and of each copy dest) is such a mem op in
/// THIS block after `after_idx`; otherwise `None`.
fn collect_addr_consumers(
    insts: &[X86ISelInst],
    addr_vreg: VReg,
    after_idx: usize,
    maps: &SibFoldVRegMaps,
) -> Option<(Vec<SibMemRewrite>, Vec<usize>)> {
    let addr_total_uses = maps.use_count(addr_vreg);
    if addr_total_uses == 0 {
        return None;
    }
    let mut mem_rewrites: Vec<SibMemRewrite> = Vec::new();
    let mut copy_deletes: Vec<usize> = Vec::new();
    let mut matched_uses = 0u32;
    for (i, inst) in insts.iter().enumerate() {
        let uses_here = vreg_uses_in_inst(inst, addr_vreg);
        if uses_here == 0 {
            continue;
        }
        matched_uses += uses_here;
        // (a) direct foldable [addr+0] mem op.
        if let Some((is_load, base, value_operand, new_opcode)) = sib_foldable_mem_op(inst)
            && base == addr_vreg
            && uses_here == 1
            && i > after_idx
        {
            mem_rewrites.push(SibMemRewrite {
                mem_idx: i,
                new_opcode,
                value_operand,
                is_load,
            });
            continue;
        }
        // (b) pure `MovRR [t, addr]` copy of the address. Either its result `t`
        // is DEAD (a redundant copy DCE would remove — treat as a no-op and
        // delete it), or `t` feeds only foldable [t+0] mem ops (a two-address
        // artifact — fold those too). Both let us delete the copy.
        if inst.opcode == X86Opcode::MovRR
            && inst.flags == X86Opcode::MovRR.default_flags()
            && uses_here == 1
            && i > after_idx
            && let [X86ISelOperand::VReg(t), X86ISelOperand::VReg(src)] = inst.operands.as_slice()
            && *src == addr_vreg
            && t.class == RegClass::Gpr64
            && maps.def_count(*t) == 1
        {
            let t_uses = maps.use_count(*t);
            if t_uses == 0 {
                // Dead copy: deleting it is unconditionally safe.
                copy_deletes.push(i);
                continue;
            }
            if let Some(mut copy_mem) = collect_pointer_mem_ops(insts, *t, i, maps) {
                copy_deletes.push(i);
                mem_rewrites.append(&mut copy_mem);
                continue;
            }
        }
        return None;
    }
    if matched_uses != addr_total_uses || mem_rewrites.is_empty() {
        return None;
    }
    Some((mem_rewrites, copy_deletes))
}

/// Try to form a SIB fold anchored on a `LeaSib [addr, SibMemAddr{..}]` at
/// `lea_idx`. Every use of `addr` (through at most one copy) must be a foldable
/// 64-bit `[addr + 0]` load/store in this block; those are rewritten to carry
/// the LeaSib's SIB operand and the LeaSib (+ copies) is deleted.
fn try_sib_addr_fold_from_leasib(
    block_id: trust_cg_lower::instructions::Block,
    insts: &[X86ISelInst],
    lea_idx: usize,
    maps: &SibFoldVRegMaps,
) -> Option<SibAddrFoldEdit> {
    let lea = insts.get(lea_idx)?;
    if lea.opcode != X86Opcode::LeaSib || lea.flags != X86Opcode::LeaSib.default_flags() {
        return None;
    }
    // LeaSib operands: [dst, SibMemAddr{base, index, scale, disp}].
    let (addr_vreg, sib, base_vreg, index_vreg) = match lea.operands.as_slice() {
        [
            X86ISelOperand::VReg(dst),
            sib @ X86ISelOperand::SibMemAddr {
                base,
                index,
                scale,
                disp,
            },
        ] => {
            // Only fold SIB-legal scales; select_array_gep only ever emits these
            // (1/2/4/8), but re-check defensively. disp is preserved exactly.
            if !matches!(*scale, 1 | 2 | 4 | 8) {
                return None;
            }
            let _ = disp;
            let (X86ISelOperand::VReg(b), X86ISelOperand::VReg(ix)) =
                (base.as_ref(), index.as_ref())
            else {
                return None;
            };
            (*dst, sib.clone(), *b, *ix)
        }
        _ => return None,
    };
    if addr_vreg.class != RegClass::Gpr64 {
        return None;
    }
    // addr must be defined exactly once (this LeaSib).
    if maps.def_count(addr_vreg) != 1 {
        return None;
    }

    let (mem_rewrites, copy_deletes) = collect_addr_consumers(insts, addr_vreg, lea_idx, maps)?;

    // base/index must not be redefined between the LeaSib and the last mem op,
    // or the SIB operand would read a different value than the LeaSib formed.
    let last_mem_idx = mem_rewrites
        .iter()
        .map(|r| r.mem_idx)
        .chain(copy_deletes.iter().copied())
        .max()
        .unwrap_or(lea_idx);
    let redef = insts[lea_idx + 1..=last_mem_idx].iter().any(|inst| {
        if let Some(d) = def_vreg(inst) {
            crate::effects::x86_produces_value(inst.opcode) && (d == base_vreg || d == index_vreg)
        } else {
            false
        }
    });
    if redef {
        return None;
    }

    // Cross-block liveness: addr must not be mentioned in any other block.
    if maps.escapes(addr_vreg, block_id) {
        return None;
    }

    // LeaSib has a single producer; reuse both index fields as that producer so
    // the shared deletion logic removes it exactly once (dedup handles the dup).
    Some(SibAddrFoldEdit {
        scale_def_idx: Some(lea_idx),
        add_idx: lea_idx,
        sib,
        mem_rewrites,
        copy_deletes,
    })
}

/// Try to form a SIB fold anchored on the `AddRR` at `add_idx`. The add must
/// compute `addr = base + scaled` where `scaled = index * scale` (a nearby
/// `imul`/`shl`), and EVERY use of `addr` in the function must be a plain
/// 64-bit `[addr + 0]` load/store in THIS block. Those memory ops are then all
/// rewritten to share the SIB operand `base + index*scale + 0`.
fn try_sib_addr_fold_from_add(
    block_id: trust_cg_lower::instructions::Block,
    insts: &[X86ISelInst],
    add_idx: usize,
    maps: &SibFoldVRegMaps,
) -> Option<SibAddrFoldEdit> {
    let add = insts.get(add_idx)?;

    // --- Side condition 2: AddRR [addr, X, Y] three-address form, default flags. ---
    if add.opcode != X86Opcode::AddRR || add.flags != X86Opcode::AddRR.default_flags() {
        return None;
    }
    let (addr_vreg, x, y) = match add.operands.as_slice() {
        [
            X86ISelOperand::VReg(dst),
            X86ISelOperand::VReg(x),
            X86ISelOperand::VReg(y),
        ] => (*dst, *x, *y),
        _ => return None,
    };
    if addr_vreg.class != RegClass::Gpr64 {
        return None;
    }

    // --- addr must be defined exactly once (this add). ---
    if maps.def_count(addr_vreg) != 1 {
        return None;
    }

    // --- Collect every memory op on `addr`; ALL uses of addr must be foldable
    // 64-bit loads/stores on [addr + 0] in THIS block (seeing through at most
    // one MovRR copy). If addr is used anywhere else (arithmetic, another
    // block, a non-zero-disp/narrow/float access), we cannot delete the add. ---
    let (mem_rewrites, copy_deletes) = collect_addr_consumers(insts, addr_vreg, add_idx, maps)?;

    // One of {x, y} is `scaled` (produced by an in-block, once-defined,
    // once-used scale-def), the other is `base`. Try both orderings.
    for (scaled_candidate, base_candidate) in [(x, y), (y, x)] {
        if scaled_candidate == base_candidate
            || base_candidate.class != RegClass::Gpr64
            || scaled_candidate.class != RegClass::Gpr64
        {
            continue;
        }

        // --- scaled: defined once, used once (by this add), function-wide. ---
        if maps.def_count(scaled_candidate) != 1 || maps.use_count(scaled_candidate) != 1 {
            continue;
        }

        // Locate the scale-def for `scaled_candidate`, earlier in THIS block.
        let mut scale_def_idx = None;
        for (i, inst) in insts.iter().enumerate().take(add_idx) {
            if def_vreg(inst) == Some(scaled_candidate) && sib_scale_def(inst).is_some() {
                scale_def_idx = Some(i);
            }
        }
        let Some(scale_def_idx) = scale_def_idx else {
            continue;
        };
        let (scale, index) = match sib_scale_def(&insts[scale_def_idx]) {
            Some(v) => v,
            None => continue,
        };

        // --- Order: scale-def < add < every memory op. ---
        if scale_def_idx >= add_idx {
            continue;
        }
        let last_mem_idx = mem_rewrites
            .iter()
            .map(|r| r.mem_idx)
            .chain(copy_deletes.iter().copied())
            .max()
            .unwrap_or(add_idx);

        // --- Side condition 4: base/index not redefined anywhere from the
        // scale-def up to (and including) the last memory op — otherwise the
        // SIB operand would read a different value than the deleted imul/add
        // computed. ---
        let window_redefs_base_or_index =
            insts[scale_def_idx + 1..=last_mem_idx].iter().any(|inst| {
                if let Some(d) = def_vreg(inst) {
                    crate::effects::x86_produces_value(inst.opcode)
                        && (d == base_candidate || d == index)
                } else {
                    false
                }
            });
        if window_redefs_base_or_index {
            continue;
        }

        // --- Side condition 6: the RFLAGS written by the scale-def and the add
        // must be dead (no reader before the next full overwrite). ---
        if !sib_fold_flags_dead(insts, scale_def_idx) || !sib_fold_flags_dead(insts, add_idx) {
            continue;
        }

        // --- Cross-block liveness: scaled and addr must not be mentioned in any
        // other block (their sole uses are in this block by the counts above,
        // but re-check defensively). ---
        if maps.escapes(scaled_candidate, block_id) || maps.escapes(addr_vreg, block_id) {
            continue;
        }

        // All side conditions hold. Build the shared SIB operand.
        let sib = X86ISelOperand::SibMemAddr {
            base: Box::new(X86ISelOperand::VReg(base_candidate)),
            index: Box::new(X86ISelOperand::VReg(index)),
            scale,
            disp: 0,
        };
        return Some(SibAddrFoldEdit {
            scale_def_idx: Some(scale_def_idx),
            add_idx,
            sib,
            mem_rewrites: mem_rewrites.clone(),
            copy_deletes: copy_deletes.clone(),
        });
    }

    // --- SCALE-1 fallback: `addr = base + index` with NO scale-def at all. ---
    //
    // A byte-element array indexes at scale 1, so ISel emits a bare `AddRR`
    // with nothing to strength-reduce and the loop above finds no scale-def.
    // That is why byte-indexed access (`&[u8]`, `Vec<u8>`, `[u8; N]`) never
    // formed a SIB address: it fell through this function AND through
    // `sib_base_lea_fold`, which only folds the base of an ALREADY-SIB operand.
    //
    // The side conditions here are STRICTLY WEAKER than the scaled path, and
    // deliberately so: there is no scale-def to delete, so `x`/`y` need NOT be
    // single-def/single-use. They only have to still hold the same values where
    // the SIB operand reads them, which is exactly the no-redef window below.
    // A proof-origin-carrying AddRR is a CARRIER (bounds/overflow check),
    // not plain address arithmetic; deleting it would drop the check. The
    // memory ops are screened the same way inside `sib_foldable_mem_op`.
    if add.proof_origin.is_none()
        && x.class == RegClass::Gpr64
        && y.class == RegClass::Gpr64
        && x != y
    {
        let last_mem_idx = mem_rewrites
            .iter()
            .map(|r| r.mem_idx)
            .chain(copy_deletes.iter().copied())
            .max()
            .unwrap_or(add_idx);

        // Neither operand may be redefined between the add and the last memory
        // op, or the SIB would read a different value than the deleted add did.
        let window_redefs = insts[add_idx + 1..=last_mem_idx].iter().any(|inst| {
            if let Some(d) = def_vreg(inst) {
                crate::effects::x86_produces_value(inst.opcode) && (d == x || d == y)
            } else {
                false
            }
        });
        // Same two remaining conditions as the scaled path: the add's RFLAGS
        // must be dead (deleting it must not remove a flag someone reads), and
        // the address vreg must not be referenced from another block.
        if !window_redefs
            && sib_fold_flags_dead(insts, add_idx)
            && !maps.escapes(addr_vreg, block_id)
        {
            return Some(SibAddrFoldEdit {
                scale_def_idx: None,
                add_idx,
                sib: X86ISelOperand::SibMemAddr {
                    base: Box::new(X86ISelOperand::VReg(x)),
                    index: Box::new(X86ISelOperand::VReg(y)),
                    scale: 1,
                    disp: 0,
                },
                mem_rewrites,
                copy_deletes,
            });
        }
    }

    None
}

/// Redundant self-zero-test elision.
///
/// Deletes `TestRR v, v` (or `CmpRI v, 0`) when:
///   1. the NEAREST preceding in-block def of `v` is an ALU op that sets ZF
///      according to its result (`And/Or/Xor/Add/Sub`, register or immediate
///      forms) with `v` as its destination — after it, `ZF == (v == 0)`,
///      exactly what the self-test would recompute;
///   2. no instruction BETWEEN that def and the test writes flags or
///      may redefine any width view of `v`; the establishing ALU definition
///      itself must match the test's exact typed register;
///   3. every flag READER before the next full overwrite consumes only ZF
///      (`Jcc`/`Setcc`/`Cmovcc` with `E`/`NE`). Readers after a full overwrite
///      observe the new flags.
///      Without an in-block overwrite, outgoing flags must also be dead in
///      every successor, as established by the CFG liveness analysis.
///   4. the test and the scanned window have default flags and no proof
///      annotation. Removing or crossing proof-bound instructions requires a
///      separate evidence transport which this pass does not provide.
///
/// The CF/OF difference between the ALU op and `test` (ADD/SUB set them
/// arithmetically; `test` clears them) is invisible to E/NE consumers, which
/// read ZF only.
fn redundant_self_test_elision_run_on_block(
    func: &mut X86ISelFunction,
    block_id: trust_cg_lower::instructions::Block,
) -> bool {
    use trust_cg_ir::X86CondCode;

    fn zf_per_result_def(op: X86Opcode) -> bool {
        matches!(
            op,
            X86Opcode::AndRR
                | X86Opcode::AndRI
                | X86Opcode::OrRR
                | X86Opcode::XorRR
                | X86Opcode::XorRI
                | X86Opcode::AddRR
                | X86Opcode::AddRI
                | X86Opcode::SubRR
                | X86Opcode::SubRI
        )
    }
    fn zf_only_cc(cc: X86CondCode) -> bool {
        matches!(cc, X86CondCode::E | X86CondCode::NE)
    }

    let Some(block) = func.blocks.get(&block_id) else {
        return false;
    };
    let n = block.insts.len();
    let mut delete_at: Option<usize> = None;
    let mut live_in = None;

    'scan: for i in 0..n {
        let inst = &block.insts[i];
        if inst.proof_origin.is_some() || inst.flags != inst.opcode.default_flags() {
            continue;
        }
        // The self-zero-test shapes.
        let v = match inst.opcode {
            X86Opcode::TestRR => match inst.operands.as_slice() {
                [X86ISelOperand::VReg(a), X86ISelOperand::VReg(b)] if a == b => *a,
                _ => continue,
            },
            X86Opcode::CmpRI => match inst.operands.as_slice() {
                [X86ISelOperand::VReg(a), X86ISelOperand::Imm(0)] => *a,
                _ => continue,
            },
            _ => continue,
        };
        // (1)+(2): walk back to the nearest def of v; nothing in between may
        // write flags or redefine v.
        let mut j = i;
        let mut found_def = false;
        while j > 0 {
            j -= 1;
            let prev = &block.insts[j];
            if prev.proof_origin.is_some() || prev.flags != prev.opcode.default_flags() {
                continue 'scan;
            }
            let defines_v = crate::effects::x86_may_defined_vregs(prev).any(|d| d.id == v.id);
            if defines_v {
                if !zf_per_result_def(prev.opcode)
                    || !matches!(prev.operands.first(), Some(X86ISelOperand::VReg(d)) if *d == v)
                {
                    continue 'scan;
                }
                found_def = true;
                break;
            }
            if x86_writes_flags(prev.opcode) || flags_barrier_for_cfg_scan(prev) {
                continue 'scan;
            }
        }
        if !found_def {
            continue;
        }
        // (3): every reader before a full overwrite must be ZF-only. Partial
        // writers may preserve CF/OF, whose values differ after this rewrite.
        let mut flags_overwritten = false;
        for later in &block.insts[i + 1..n] {
            if later.proof_origin.is_some() || later.flags != later.opcode.default_flags() {
                continue 'scan;
            }
            if x86_reads_flags(later.opcode) {
                let cc_ok = match later.opcode {
                    X86Opcode::Jcc | X86Opcode::Setcc => {
                        matches!(
                            later.operands.first().or(later.operands.get(1)),
                            Some(X86ISelOperand::CondCode(cc)) if zf_only_cc(*cc)
                        ) || matches!(
                            later.operands.get(1),
                            Some(X86ISelOperand::CondCode(cc)) if zf_only_cc(*cc)
                        )
                    }
                    X86Opcode::Cmovcc | X86Opcode::Cmovcc32 => matches!(
                        later.operands.iter().find(|o| matches!(o, X86ISelOperand::CondCode(_))),
                        Some(X86ISelOperand::CondCode(cc)) if zf_only_cc(*cc)
                    ),
                    _ => false, // ADC/SBB-style consumers: refuse.
                };
                if !cc_ok {
                    continue 'scan;
                }
            }
            if condition_flag_overwrite(later) == FlagOverwrite::Full {
                flags_overwritten = true;
                break; // later readers see the new flags, not ours.
            }
            if flags_barrier_for_cfg_scan(later) {
                continue 'scan;
            }
        }
        if !flags_overwritten && !block.successors.is_empty() {
            let live_in = live_in.get_or_insert_with(|| flags_live_in_by_block(func));
            if block
                .successors
                .iter()
                .any(|succ| live_in.get(succ).copied().unwrap_or(true))
            {
                continue;
            }
        }
        delete_at = Some(i);
        break;
    }

    if let Some(i) = delete_at
        && let Some(block) = func.blocks.get_mut(&block_id)
    {
        block.insts.remove(i);
        return true;
    }
    false
}

// ---------------------------------------------------------------------------
// Local address-chain fold (X9 slice 2)
//
//   mov  t0, base           ; MovRR copy hop
//   add  t0, #imm           ; AddRI (tied or 3-op)   -> disp accumulation
//   mov  t1, t0             ; MovRR copy hop
//   add  t1, idx            ; AddRR (tied or 3-op)   -> scale-1 index
//   mov  r, [t1 + d0]       ; MovRM -> MovRMSib r, [base + idx*1 + (d0+imm)]
// ---------------------------------------------------------------------------
//
// The SIB fold above anchors on the scale-def/add pair and requires
// FUNCTION-WIDE single-def/single-use intermediates — sound and precise for
// raw ISel output, but blind in a post-unroll body where verbatim clones
// REUSE vreg ids (every intermediate has one def PER CLONE, so def_count is
// the trip count). This fold instead anchors on each 64-bit `MovRM`/`MovMR`
// whose address is a plain `[vreg + disp]` and resolves the address with
// LOCAL nearest-reaching-def reasoning inside the block.
//
// HAND-PROOF (semantic equivalence). The resolver walks the address vreg's
// def chain upward: at each step it holds a triple (v, pos, disp[, index])
// with the invariant
//
//   value(anchor address at mem_idx) = value(v at pos) + index*scale + disp
//
// Nearest-def hops preserve the invariant: `nearest_local_def_before(pos, v)`
// returning `def_idx` means no def of `v` exists in (def_idx, pos), so
// value(v at pos) = the value `def_idx` computed:
//   - `MovRR d, s` (class-exact copy): value(d) = value(s at def_idx).
//   - `AddRI d, s, k` / tied `AddRI d, k`: value(d) = value(s at def_idx) + k
//     (mod 2^64; SIB address arithmetic is likewise mod 2^64, and the i64
//     disp accumulation is checked to stay in i32).
//   - `AddRR d, s1, s2` / tied `AddRR d, s`: value(d) = value(s1) + value(s2),
//     both read at def_idx; one side becomes the SIB index (scale 1).
// The rewritten operand reads the FINAL base (and index) registers AT THE
// MEMORY OP, so for exactly those two vregs we additionally require no def
// in [capture_pos, mem_idx) — checked explicitly (`no_def_in_range`). The
// intermediate temps do not appear in the rewritten operand and need no such
// check; their values were consumed at their capture positions.
//
// The fold REWRITES ONLY — it deletes nothing. The now-unused chain
// instructions are swept by DCE (the default-on per-def local tier handles the
// multi-def post-unroll ids), which owns the flags-deadness obligations for
// removing the flag-writing adds. Rewriting alone never changes flags: the
// memory op computed no flags before and computes none after.
//
// SIDE CONDITIONS (each checked, fail-closed):
//   1. Anchor: full-width `MovRM [dst, MemAddr{VReg a, d0}]` or
//      `MovMR [MemAddr{VReg a, d0}, src]`, default flags, no proof_origin
//      (atomics/volatile keep their stronger proofs), all Gpr64.
//   2. Chain links: `MovRR`(Gpr64=Gpr64) / `AddRI` / `AddRR` with default
//      flags, no proof_origin, VReg/Imm operands only, all Gpr64. Anything
//      else terminates resolution (the current vreg becomes the base).
//   3. At most ONE index side (first `AddRR` met), scale fixed at 1. A
//      second `AddRR` terminates resolution.
//   4. Final disp must fit i32 (checked i64 accumulation, then try_into).
//   5. Final base and index: no def in [capture_pos, mem_idx) — includes
//      Xchg/Cmpxchg hidden defs via `local_fold_defines_vreg`, which treats
//      any VReg operand of those opcodes as a potential def.
//   6. The rewrite fires only if at least one link was consumed AND the
//      shape actually changed (avoids `changed=true` fixpoint churn).
// ---------------------------------------------------------------------------

/// Set once by [`set_sib_scale1_fold_disabled`]; `true` disables the SIB
/// scale-1 index fold.
static SIB_SCALE1_FOLD_DISABLED: std::sync::OnceLock<bool> = std::sync::OnceLock::new();

/// Install this fold's opt-out from a TRACKED compiler option, once
/// (`-Ztrust-ir-cg-args=no-x86-sib-scale1-fold`). `true` disables the fold.
///
/// Under `trustc` the `TCG_NO_X86_SIB_SCALE1_FOLD` variable is REFUSED before the
/// backend loads, so this setter is the only channel that reaches the fold there —
/// and without it the fold could not be A/B'd through the bridge at all.
pub fn set_sib_scale1_fold_disabled(disabled: bool) -> bool {
    match SIB_SCALE1_FOLD_DISABLED.set(disabled) {
        Ok(()) => true,
        Err(requested) => SIB_SCALE1_FOLD_DISABLED.get() == Some(&requested),
    }
}

/// Whether the scale-1 index fold proves flag-deadness with the CROSS-BLOCK
/// [`X86FlagLiveness`] analysis rather than the block-local scan. DEFAULT ON;
/// `-Ztrust-ir-cg-args=no-x86-sib-crossblock-flags` is the isolating A/B lever —
/// `no-x86-sib-scale1-fold` cannot isolate it, because that disables the whole
/// fold rather than just the widened proof.
fn sib_crossblock_flag_proof_enabled() -> bool {
    if let Some(disabled) = SIB_CROSSBLOCK_FLAGS_DISABLED.get() {
        return !*disabled;
    }
    !crate::tcg_env_flag("TCG_NO_X86_SIB_CROSSBLOCK_FLAGS")
}

static SIB_CROSSBLOCK_FLAGS_DISABLED: std::sync::OnceLock<bool> = std::sync::OnceLock::new();

/// Install the cross-block flag-proof opt-out from a TRACKED compiler option.
pub fn set_sib_crossblock_flags_disabled(disabled: bool) -> bool {
    match SIB_CROSSBLOCK_FLAGS_DISABLED.set(disabled) {
        Ok(()) => true,
        Err(requested) => SIB_CROSSBLOCK_FLAGS_DISABLED.get() == Some(&requested),
    }
}

fn sib_scale1_index_fold_enabled() -> bool {
    if let Some(disabled) = SIB_SCALE1_FOLD_DISABLED.get() {
        return !*disabled;
    }
    !crate::tcg_env_flag("TCG_NO_X86_SIB_SCALE1_FOLD")
}

/// Whether block `block_id` holds an instruction the scale-1 index fold can
/// start from: no proof origin, a register destination, and a
/// [`sib_scale_def`] multiply by 2, 4 or 8. [`sib_scale1_index_fold_run_on_block`]
/// skips every other instruction before reading the counts or the flags.
fn block_has_sib_scale_candidate(
    func: &X86ISelFunction,
    block_id: trust_cg_lower::instructions::Block,
) -> bool {
    func.blocks.get(&block_id).is_some_and(|block| {
        block.insts.iter().any(|def| {
            def.proof_origin.is_none()
                && matches!(def.operands.first(), Some(X86ISelOperand::VReg(_)))
                && sib_scale_def(def).is_some_and(|(scale, _)| scale != 1)
        })
    })
}

/// Fold a power-of-two `imul`/`shl` scale-def INTO the scale field of a memory
/// op that already carries a SIB operand with `scale == 1`.
///
/// # The shape, and why the existing fold cannot reach it
///
/// [`sib_addr_fold_run_on_block_with_maps`] anchors on a formed
/// `LeaSib d,[base+index*scale+disp]`, or on an `imul`/`shl` followed by an
/// `AddRR` that materialises `base + index*scale`. A frontend that lowers an
/// element address as an explicit stride multiply and then lets the SIB do the
/// base addition emits NEITHER:
///
/// ```text
///   imul  scaled, index, 8          ; ImulRRI
///   mov   dst, [base + scaled*1]    ; MovRMSib, scale == 1
/// ```
///
/// There is no `LeaSib` and no `AddRR`, so the fold has no anchor and the
/// multiply survives into the hot loop. This arm supplies that anchor:
///
/// ```text
///   mov   dst, [base + index*8]     ; the multiply is free in the SIB
/// ```
///
/// # Why the rewrite is exact
///
/// `imul` with 64-bit operands yields the low 64 bits, i.e. `index * k` modulo
/// 2^64, and SIB address computation is also modulo 2^64. So `(index * k) * 1`
/// and `index * k` are the SAME value for every input INCLUDING the wrapping
/// ones — this is an equality, not an approximation, and it is why the arm needs
/// no range or non-overflow side condition.
///
/// # Side conditions (any failure leaves the code alone)
///
/// * The memory op's SIB scale is exactly 1, and its index is a VReg.
/// * That index is globally single-def, its def is in THIS block before the
///   memory op, and [`sib_scale_def`] reads it as a power-of-two `ImulRRI`/
///   `ShlRI` with scale in `{2,4,8}` (scale 1 would be a no-op rewrite).
/// * The def carries no `proof_origin` and default flags — the same cleanliness
///   the sibling folds require, so a proof-carrying instruction is never moved.
/// * The scale-def's SOURCE register is not redefined between the def and the
///   memory op. Without this the rewritten SIB would read a later value of the
///   source instead of the one that was multiplied.
/// * The index is used exactly once (by this memory op), and the scale-def's
///   RFLAGS are dead there, so deleting the multiply is observationally
///   invisible. A multi-use index is left alone rather than partially rewritten.
fn sib_scale1_index_fold_run_on_block(
    func: &mut X86ISelFunction,
    block_id: trust_cg_lower::instructions::Block,
    counts: &FnUseDefCounts,
    flags: &X86FlagLiveness,
) -> bool {
    let Some(block) = func.blocks.get(&block_id) else {
        return false;
    };
    let insts = block.insts.clone();
    // scale-def index -> (new scale, source vreg, every memory op to rewrite)
    let mut edits: Vec<(usize, u8, VReg, Vec<usize>)> = Vec::new();

    for (def_idx, def) in insts.iter().enumerate() {
        if def.proof_origin.is_some() {
            continue;
        }
        let Some(X86ISelOperand::VReg(scaled)) = def.operands.first() else {
            continue;
        };
        let scaled = *scaled;
        if counts.def_count(scaled) != 1 {
            continue;
        }
        let Some((new_scale, src)) = sib_scale_def(def) else {
            continue;
        };
        if new_scale == 1 {
            continue;
        }
        // Every appearance of `scaled` must be a scale-1 SIB index, and every
        // one of its uses must be in THIS block. A use anywhere else -- in
        // another block, as a plain register operand, or as a SIB base -- means
        // the multiply is still needed, so rewriting would keep it and gain
        // nothing while raising register pressure.
        let mut mem_uses: Vec<usize> = Vec::new();
        let mut appearances: u32 = 0;
        let mut disqualified = false;
        for (use_idx, inst) in insts.iter().enumerate().skip(def_idx + 1) {
            let (as_scale1_index, elsewhere) = scale1_index_appearances(inst, scaled);
            appearances += as_scale1_index + elsewhere;
            if elsewhere > 0 || as_scale1_index > 1 {
                disqualified = true;
                break;
            }
            if as_scale1_index == 1 {
                if inst.proof_origin.is_some() {
                    disqualified = true;
                    break;
                }
                mem_uses.push(use_idx);
            }
        }
        if disqualified || mem_uses.is_empty() || appearances != counts.use_count(scaled) {
            continue;
        }
        // The multiplied SOURCE must not be redefined between the multiply and
        // the LAST rewritten use; otherwise the rewritten SIB would index on a
        // later value than the one that was multiplied.
        let last_use = *mem_uses.last().expect("non-empty");
        if insts[def_idx + 1..last_use]
            .iter()
            .any(|i| local_fold_defines_vreg(i, src))
        {
            continue;
        }
        // Deleting the multiply must not lose observable flags.
        //
        // This used the block-LOCAL `sib_fold_flags_dead`, which refuses at the
        // block terminator. That is where `b1_mispredict` lost: its
        // `ImulRRI v91, v89, 8` is the second-to-last instruction of its block and
        // the `AndRI _, _, 6` that discharges the flag obligation is in the
        // fall-through SUCCESSOR, so the scale-8 arm could never fire and the
        // multiply plus its feeding copy stayed in the hot loop.
        // `sib_fold_falls_back_to_scale_1_and_retains_the_chain_when_flags_may_be_live`
        // pins that fallback, and its doc names the remedy: "only by widening the
        // flag-deadness proof". [`X86FlagLiveness`] IS that widening — the
        // cross-block RFLAGS analysis written for this exact shape, already the
        // basis of x86 DCE's flag reasoning — so this asks it instead.
        //
        // The snapshot stays valid while this pass mutates the function, by the
        // argument in that module: every deletion here is justified by "the flags
        // this instruction writes are dead", which cannot move a block's entry
        // verdict from dead to live. The caller re-analyzes after a block changes
        // anyway, so the question does not arise.
        let flags_dead = if sib_crossblock_flag_proof_enabled() {
            flags.flags_dead_after(&insts, block_id, def_idx)
        } else {
            sib_fold_flags_dead(&insts, def_idx)
        };
        if !flags_dead {
            continue;
        }
        edits.push((def_idx, new_scale, src, mem_uses));
    }

    if edits.is_empty() {
        return false;
    }
    let block = func.blocks.get_mut(&block_id).expect("block existed above");
    let mut to_delete: Vec<usize> = Vec::new();
    for (def_idx, new_scale, src, mem_uses) in edits {
        for mem_idx in mem_uses {
            if let Some(slot) = block.insts[mem_idx]
                .operands
                .iter_mut()
                .find(|o| matches!(o, X86ISelOperand::SibMemAddr { .. }))
                && let X86ISelOperand::SibMemAddr { index, scale, .. } = slot
            {
                **index = X86ISelOperand::VReg(src);
                *scale = new_scale;
            }
        }
        to_delete.push(def_idx);
    }
    to_delete.sort_unstable();
    to_delete.dedup();
    for idx in to_delete.into_iter().rev() {
        block.insts.remove(idx);
    }
    true
}

/// Count how `v` appears in `inst`, split into "as the index of a scale-1 SIB
/// operand" and "anywhere else".
///
/// The split is the safety condition for retiring the multiply that defines `v`.
/// Only the first kind can be rewritten to index on the pre-multiply source; any
/// appearance of the second kind (a plain register operand, a SIB BASE, or the
/// index of a SIB whose scale is not 1) still needs `v`'s multiplied value, so
/// the multiply must stay and the fold declines. `MovMRSib [base+v*1], v` — a
/// store OF the index THROUGH the index — is exactly the case this rejects.
fn scale1_index_appearances(inst: &X86ISelInst, v: VReg) -> (u32, u32) {
    let mut as_scale1_index = 0;
    let mut elsewhere = 0;
    for op in &inst.operands {
        match op {
            X86ISelOperand::VReg(u) if *u == v => elsewhere += 1,
            X86ISelOperand::MemAddr { base, .. } => {
                if matches!(base.as_ref(), X86ISelOperand::VReg(u) if *u == v) {
                    elsewhere += 1;
                }
            }
            X86ISelOperand::SibMemAddr {
                base, index, scale, ..
            } => {
                if matches!(base.as_ref(), X86ISelOperand::VReg(u) if *u == v) {
                    elsewhere += 1;
                }
                if matches!(index.as_ref(), X86ISelOperand::VReg(u) if *u == v) {
                    if *scale == 1 {
                        as_scale1_index += 1;
                    } else {
                        elsewhere += 1;
                    }
                }
            }
            _ => {}
        }
    }
    (as_scale1_index, elsewhere)
}

// SIB-base LEA fold: folds each stack-slot base-`Lea` into its indexed SIB
// memory operand, eliminating the redundant per-access `leaq -N(%rbp)`
// (trust-cg had 0 folded indexed accesses vs LLVM's 11-22 on the sort
// cluster). Composes with the default-on cmov-swap: cmov-swap models the
// folded `StackSlot`-SIB bases (`x86_cmov_swap.rs` `sib_base`), so the
// swap-diamond bench (b06) keeps cmov-swap AND the tighter addressing.
// Measured (cmov+fold vs cmov-only): b06 ~1.5 (was 2.35 pre-fix), b07 −14% /
// b18 −15% / b05 −10%; composed geomean ~0.95-0.98.
//
// Byte-element SIB addressing has two halves that are only useful together:
//   * the 8-bit `MovRM8`/`MovzxRM8`/`MovMR8` arms of `sib_foldable_mem_op`, and
//   * the SCALE-1 arm of `try_sib_addr_fold_from_add` (a byte array indexes at
//     scale 1, so ISel emits a bare `AddRR` with no scale-def to anchor on).
// Together they let `&[u8]` / `Vec<u8>` / `[u8; N]` element accesses carry
// their address in the memory operand instead of paying a base-`Lea` plus an
// `Add` per access; `sib_base_lea_fold` then folds the stack-slot base into
// the SIB displacement.

/// Run the SIB-base LEA fold over `func` (the body of the `X86SibBaseFold` pass).
/// Builds the function-wide clean base-`Lea` and `MovRR`-copy indices, then folds
/// each already-SIB-formed indexed load/store's base into its `StackSlot` (or
/// same-block VReg) base, leaving the now-dead base-`Lea`s for DCE. Extracted so
/// it can run LATE — after cmov-swap / if-convert, whose diamond recognizers
/// match the PRE-fold addressing (see the note in `run_impl`). Returns whether
/// anything changed. The measured evidence is in the comment above it.
///
/// `counts` must describe `func` AS IT IS ON ENTRY — the caller supplies it so
/// one build can serve several passes. This pass consults only
/// `def_count`/`use_count`, which is exactly `FnUseDefCounts`; it never needs
/// the mention-block half of [`SibFoldVRegMaps`].
pub(crate) fn sib_base_lea_fold(func: &mut X86ISelFunction, counts: &FnUseDefCounts) -> bool {
    let maps = counts;
    // Function-wide index of clean, single-def base-`Lea`s (the `&arr` LEA is
    // loop-invariant, hoisted to a preheader; a block-local scan would miss it).
    let mut lea_defs: FxHashMap<VReg, LeaBaseDef> = FxHashMap::default();
    for block_id in &func.block_order {
        let Some(block) = func.blocks.get(block_id) else {
            continue;
        };
        for (idx, inst) in block.insts.iter().enumerate() {
            if inst.opcode != X86Opcode::Lea
                || inst.proof_origin.is_some()
                || inst.flags != inst.opcode.default_flags()
            {
                continue;
            }
            if let [
                X86ISelOperand::VReg(d),
                X86ISelOperand::MemAddr { base, disp },
            ] = inst.operands.as_slice()
                && maps.def_count(*d) == 1
            {
                lea_defs.insert(
                    *d,
                    LeaBaseDef {
                        base: base.as_ref().clone(),
                        disp: *disp,
                        block: *block_id,
                        idx,
                    },
                );
            }
        }
    }
    // Function-wide index of clean, single-def register copies (`MovRR b, s`):
    // the SIB base is a COPY of the `&arr` LEA, resolved through this chain.
    let mut copy_src: FxHashMap<VReg, VReg> = FxHashMap::default();
    for block in func.blocks.values() {
        for inst in &block.insts {
            if inst.opcode == X86Opcode::MovRR
                && inst.proof_origin.is_none()
                && inst.flags == inst.opcode.default_flags()
                && let [X86ISelOperand::VReg(d), X86ISelOperand::VReg(s)] = inst.operands.as_slice()
                && d.class == RegClass::Gpr64
                && s.class == RegClass::Gpr64
                && maps.def_count(*d) == 1
            {
                copy_src.insert(*d, *s);
            }
        }
    }
    let mut changed = false;
    for block_id in func.block_order.clone() {
        if sib_base_lea_fold_run_on_block(func, block_id, maps, &lea_defs, &copy_src) {
            changed = true;
        }
    }
    changed
}

/// Conservative "may define this vreg" for the local fold's redef scans.
/// Operand-0 defs of value producers, plus EVERY VReg operand of the
/// exchange family (hidden second defs invisible to the operand-0 model —
/// the same hazard the unroller refuses). Matching is CLASS-BLIND on the id:
/// a VReg with the same id at a different class is an aliased width view of
/// the same underlying register (the dirty-high-bits class), so a narrow def
/// must stop the resolver / poison the window exactly like a full def.
fn local_fold_defines_vreg(inst: &X86ISelInst, v: VReg) -> bool {
    if crate::effects::x86_may_defined_vregs(inst).any(|d| d.id == v.id) {
        return true;
    }
    // ANY instruction with a VReg operand 0 matching the id is treated as a
    // POTENTIAL def (fail-closed) — NOT gated on `x86_produces_value`, which
    // excluded StackAlloc until it was taught that StackAlloc writes its
    // operand-0 vreg (the allocated address); gating on a classifier would
    // let the resolver walk past any def it misses to a stale one
    // (adversarial-review finding). Treating a use-position operand 0
    // (e.g. CmpRR's) as a def merely terminates resolution early:
    // conservative, never wrong.
    matches!(inst.operands.first(), Some(X86ISelOperand::VReg(d)) if d.id == v.id)
}

/// Nearest def of `v` strictly before `pos` in the block, or None (live-in).
fn nearest_local_def_before(insts: &[X86ISelInst], pos: usize, v: VReg) -> Option<usize> {
    (0..pos)
        .rev()
        .find(|&i| local_fold_defines_vreg(&insts[i], v))
}

/// True iff some inst in [from, to) may define `v`.
fn no_def_in_range(insts: &[X86ISelInst], from: usize, to: usize, v: VReg) -> bool {
    !insts[from..to]
        .iter()
        .any(|inst| local_fold_defines_vreg(inst, v))
}

/// A resolved local address chain: `base + index*1 + disp` with capture
/// positions for the final-operand redef checks.
struct LocalChainAddr {
    base: VReg,
    base_captured_at: usize,
    index: Option<(VReg, usize)>,
    /// Narrowed to the SIB displacement width at construction: the chain is
    /// accumulated in `i64` and refused outright if it does not fit, so no
    /// consumer has to re-check (or assert) the range.
    disp: i32,
    links_consumed: usize,
}

/// One link of the resolvable chain dialect.
enum LocalChainLink {
    /// `MovRR d, s`: continue with s read at the link.
    Copy(VReg),
    /// `AddRI d, s, k` or tied `AddRI d, k` (s == d resolved above the link).
    AddImm(VReg, i64),
    /// `AddRR d, s1, s2` or tied `AddRR d, s`: base continues via .0, index .1.
    AddReg(VReg, VReg),
}

/// Classify `inst` (which defines `v`) as a resolvable chain link. Fail-closed:
/// default flags only, no proof_origin, Gpr64 everywhere.
fn classify_local_chain_link(inst: &X86ISelInst, v: VReg) -> Option<LocalChainLink> {
    if inst.proof_origin.is_some() || inst.flags != inst.opcode.default_flags() {
        return None;
    }
    let g64 = |r: &VReg| r.class == RegClass::Gpr64;
    match inst.opcode {
        X86Opcode::MovRR => match inst.operands.as_slice() {
            [X86ISelOperand::VReg(d), X86ISelOperand::VReg(s)] if *d == v && g64(d) && g64(s) => {
                Some(LocalChainLink::Copy(*s))
            }
            _ => None,
        },
        X86Opcode::AddRI => match inst.operands.as_slice() {
            // Tied: d := d + k — the source is d's value ABOVE the link.
            [X86ISelOperand::VReg(d), X86ISelOperand::Imm(k)] if *d == v && g64(d) => {
                Some(LocalChainLink::AddImm(*d, *k))
            }
            // Three-address: d := s + k.
            [
                X86ISelOperand::VReg(d),
                X86ISelOperand::VReg(s),
                X86ISelOperand::Imm(k),
            ] if *d == v && g64(d) && g64(s) => Some(LocalChainLink::AddImm(*s, *k)),
            _ => None,
        },
        X86Opcode::AddRR => match inst.operands.as_slice() {
            // Tied: d := d + s — base continues as d above, index is s.
            [X86ISelOperand::VReg(d), X86ISelOperand::VReg(s)] if *d == v && g64(d) && g64(s) => {
                Some(LocalChainLink::AddReg(*d, *s))
            }
            // Three-address: d := s1 + s2.
            [
                X86ISelOperand::VReg(d),
                X86ISelOperand::VReg(s1),
                X86ISelOperand::VReg(s2),
            ] if *d == v && g64(d) && g64(s1) && g64(s2) => Some(LocalChainLink::AddReg(*s1, *s2)),
            _ => None,
        },
        // `Lea d, [s + k]`: d := s + sign_extend(k), the value `AddRI d, s, k`
        // computes, with no flag write. This is how the selector spells a
        // constant field offset (`StructGep`), and what the constant-index SIB
        // fold leaves behind a derived base. Only a Gpr64 register base is a
        // link: a `StackSlot` base, or any other base operand, ends resolution
        // at `d`.
        X86Opcode::Lea => match inst.operands.as_slice() {
            [
                X86ISelOperand::VReg(d),
                X86ISelOperand::MemAddr { base, disp },
            ] if *d == v && g64(d) => match base.as_ref() {
                X86ISelOperand::VReg(s) if g64(s) => {
                    Some(LocalChainLink::AddImm(*s, i64::from(*disp)))
                }
                _ => None,
            },
            _ => None,
        },
        _ => None,
    }
}

const LOCAL_CHAIN_MAX_LINKS: usize = 8;

/// Resolve the address vreg `start` (read by the memory op at `mem_idx` with
/// starting displacement `start_disp`) into `base + index*1 + disp` by local
/// nearest-def chain walking. See the module comment for the invariant proof.
fn resolve_local_addr_chain(
    insts: &[X86ISelInst],
    mem_idx: usize,
    start: VReg,
    start_disp: i64,
) -> Option<LocalChainAddr> {
    let mut v = start;
    let mut pos = mem_idx;
    let mut disp = start_disp;
    let mut index: Option<(VReg, usize)> = None;
    let mut links = 0usize;

    while links < LOCAL_CHAIN_MAX_LINKS {
        let Some(def_idx) = nearest_local_def_before(insts, pos, v) else {
            break; // live-in: finalize with v as base captured at pos.
        };
        match classify_local_chain_link(&insts[def_idx], v) {
            Some(LocalChainLink::Copy(s)) => {
                v = s;
                pos = def_idx;
            }
            Some(LocalChainLink::AddImm(s, k)) => {
                disp = disp.checked_add(k)?;
                v = s;
                pos = def_idx;
            }
            Some(LocalChainLink::AddReg(s1, s2)) if index.is_none() => {
                index = Some((s2, def_idx));
                v = s1;
                pos = def_idx;
            }
            // Second AddRR (index already taken) or unrecognized def:
            // finalize with the current v as base. Note: for a def we could
            // not classify, v's value at pos IS that def's result — the base
            // capture position stays `pos` (below the def), which is exactly
            // where the chain read it.
            _ => break,
        }
        links += 1;
    }

    // Final-operand validity: base (and index) must hold the same value at
    // the memory op as at their capture positions.
    if !no_def_in_range(insts, pos, mem_idx, v) {
        return None;
    }
    if let Some((iv, ipos)) = index {
        if !no_def_in_range(insts, ipos, mem_idx, iv) {
            return None;
        }
        // SIB base==index is legal; RSP-index impossible pre-regalloc.
        let _ = iv;
    }

    let disp = i32::try_from(disp).ok()?;
    Some(LocalChainAddr {
        base: v,
        base_captured_at: pos,
        index,
        disp,
        links_consumed: links,
    })
}

/// Anchor recognizer: MovRM/MovMR (64-bit) or MovRM32/MovMR32 (32-bit) on
/// `[VReg + disp]`. Returns (is_load, addr_vreg, disp, value_operand, width32).
fn local_fold_anchor(inst: &X86ISelInst) -> Option<(bool, VReg, i32, X86ISelOperand, bool)> {
    if inst.proof_origin.is_some() {
        return None;
    }
    if inst.flags != inst.opcode.default_flags() {
        return None;
    }
    match inst.opcode {
        X86Opcode::MovRM | X86Opcode::MovRM32 => {
            let width32 = inst.opcode == X86Opcode::MovRM32;
            let want = if width32 {
                RegClass::Gpr32
            } else {
                RegClass::Gpr64
            };
            match inst.operands.as_slice() {
                [
                    dst @ X86ISelOperand::VReg(d),
                    X86ISelOperand::MemAddr { base, disp },
                ] if d.class == want => match base.as_ref() {
                    X86ISelOperand::VReg(a) if a.class == RegClass::Gpr64 => {
                        Some((true, *a, *disp, dst.clone(), width32))
                    }
                    _ => None,
                },
                _ => None,
            }
        }
        X86Opcode::MovMR | X86Opcode::MovMR32 => {
            let width32 = inst.opcode == X86Opcode::MovMR32;
            let want = if width32 {
                RegClass::Gpr32
            } else {
                RegClass::Gpr64
            };
            match inst.operands.as_slice() {
                [
                    X86ISelOperand::MemAddr { base, disp },
                    src @ X86ISelOperand::VReg(s),
                ] if s.class == want => match base.as_ref() {
                    X86ISelOperand::VReg(a) if a.class == RegClass::Gpr64 => {
                        Some((false, *a, *disp, src.clone(), width32))
                    }
                    _ => None,
                },
                _ => None,
            }
        }
        _ => None,
    }
}

/// Run the local address-chain fold on one block. Rewrites memory operands in
/// place; never deletes instructions (DCE owns the sweep). Returns whether
/// anything changed.
fn addr_chain_fold_run_on_block(
    func: &mut X86ISelFunction,
    block_id: trust_cg_lower::instructions::Block,
) -> bool {
    let Some(block) = func.blocks.get(&block_id) else {
        return false;
    };
    let insts = &block.insts;

    // Collect rewrites first (immutable scan), apply after.
    struct Rewrite {
        mem_idx: usize,
        new_opcode: X86Opcode,
        new_addr: X86ISelOperand,
        is_load: bool,
        value_operand: X86ISelOperand,
    }
    let mut rewrites: Vec<Rewrite> = Vec::new();

    for mem_idx in 0..insts.len() {
        let Some((is_load, addr, d0, value_operand, width32)) = local_fold_anchor(&insts[mem_idx])
        else {
            continue;
        };
        let Some(chain) = resolve_local_addr_chain(insts, mem_idx, addr, i64::from(d0)) else {
            continue;
        };
        if chain.links_consumed == 0 {
            continue;
        }
        let disp = chain.disp;
        let (new_opcode, new_addr) = match chain.index {
            Some((iv, _)) => (
                match (is_load, width32) {
                    (true, false) => X86Opcode::MovRMSib,
                    (false, false) => X86Opcode::MovMRSib,
                    (true, true) => X86Opcode::MovRM32Sib,
                    (false, true) => X86Opcode::MovMR32Sib,
                },
                X86ISelOperand::SibMemAddr {
                    base: Box::new(X86ISelOperand::VReg(chain.base)),
                    index: Box::new(X86ISelOperand::VReg(iv)),
                    scale: 1,
                    disp,
                },
            ),
            None => (
                match (is_load, width32) {
                    (true, false) => X86Opcode::MovRM,
                    (false, false) => X86Opcode::MovMR,
                    (true, true) => X86Opcode::MovRM32,
                    (false, true) => X86Opcode::MovMR32,
                },
                X86ISelOperand::MemAddr {
                    base: Box::new(X86ISelOperand::VReg(chain.base)),
                    disp,
                },
            ),
        };
        // No-progress guard: identical opcode + address = nothing to do.
        if new_opcode == insts[mem_idx].opcode {
            let same = match (
                &new_addr,
                insts[mem_idx].operands.iter().find(|op| {
                    matches!(
                        op,
                        X86ISelOperand::MemAddr { .. } | X86ISelOperand::SibMemAddr { .. }
                    )
                }),
            ) {
                (a, Some(b)) => a == b,
                _ => false,
            };
            if same {
                continue;
            }
        }
        let _ = chain.base_captured_at;
        rewrites.push(Rewrite {
            mem_idx,
            new_opcode,
            new_addr,
            is_load,
            value_operand,
        });
    }

    if rewrites.is_empty() {
        return false;
    }

    // `addr_chain_fold_run_on_block` opens with
    // `let Some(block) = func.blocks.get(&block_id) else { return false }`;
    // the rewrite-collection scan between there and here only reads `func`.
    let block = func.blocks.get_mut(&block_id).expect("block existed above");
    for r in rewrites {
        let mem = &mut block.insts[r.mem_idx];
        mem.opcode = r.new_opcode;
        mem.flags = r.new_opcode.default_flags();
        mem.operands = if r.is_load {
            vec![r.value_operand, r.new_addr]
        } else {
            vec![r.new_addr, r.value_operand]
        };
    }
    true
}

/// Depth bound of [`local_const_value`]: a constant index is at most a
/// strength-reduced multiply of a multiply of a literal.
const LOCAL_CONST_MAX_DEPTH: usize = 4;

/// The 64-bit value `v` holds immediately before `insts[pos]`, when the
/// instructions of this block alone determine it as a compile-time constant.
///
/// `v` must be a `Gpr64` register. Its nearest reaching definition in the
/// block is found CLASS-BLIND ([`nearest_local_def_before`]: any instruction
/// that may write the id at any width, or carries it as operand 0), so a
/// narrow write between a constant definition and `pos` ends the walk at an
/// instruction no arm below accepts. A register with no definition in the
/// block (live-in) is not a constant here.
///
/// The accepted definitions, each with default flags, no `proof_origin`, and
/// `Gpr64` registers throughout:
///
/// * `MovRI v, k`: the value is `k`.
/// * `LeaSib v, [x + y*s + d]` with `s` in `{1,2,4,8}`: `x + y*s + d` modulo
///   2^64, which is what a 64-bit `lea` computes, with `x` and `y` read
///   immediately before the `lea`.
/// * `ImulRRI v, x, k` with `k` a sign-extended 32-bit immediate, and the
///   three-address `ImulRR v, x, y`: the low 64 bits of the product, which is
///   the wrapping product for every pair of operands.
///
/// Nothing is rewritten on the strength of this value except by the caller,
/// so the multiply forms need no flag condition: their instructions stay in
/// place until they are dead.
fn local_const_value(insts: &[X86ISelInst], pos: usize, v: VReg, depth: usize) -> Option<i64> {
    if depth == 0 || v.class != RegClass::Gpr64 {
        return None;
    }
    let def_idx = nearest_local_def_before(insts, pos, v)?;
    let inst = &insts[def_idx];
    if inst.proof_origin.is_some() || inst.flags != inst.opcode.default_flags() {
        return None;
    }
    let g64 = |r: &VReg| r.class == RegClass::Gpr64;
    let source = |r: &VReg| local_const_value(insts, def_idx, *r, depth - 1);
    match (inst.opcode, inst.operands.as_slice()) {
        (X86Opcode::MovRI, [X86ISelOperand::VReg(d), X86ISelOperand::Imm(k)]) if *d == v => {
            Some(*k)
        }
        (
            X86Opcode::LeaSib,
            [
                X86ISelOperand::VReg(d),
                X86ISelOperand::SibMemAddr {
                    base,
                    index,
                    scale,
                    disp,
                },
            ],
        ) if *d == v && matches!(*scale, 1 | 2 | 4 | 8) => match (base.as_ref(), index.as_ref()) {
            (X86ISelOperand::VReg(x), X86ISelOperand::VReg(y)) if g64(x) && g64(y) => Some(
                source(x)?
                    .wrapping_add(source(y)?.wrapping_mul(i64::from(*scale)))
                    .wrapping_add(i64::from(*disp)),
            ),
            _ => None,
        },
        (
            X86Opcode::ImulRRI,
            [
                X86ISelOperand::VReg(d),
                X86ISelOperand::VReg(x),
                X86ISelOperand::Imm(k),
            ],
        ) if *d == v && g64(x) && i32::try_from(*k).is_ok() => Some(source(x)?.wrapping_mul(*k)),
        (
            X86Opcode::ImulRR,
            [
                X86ISelOperand::VReg(d),
                X86ISelOperand::VReg(x),
                X86ISelOperand::VReg(y),
            ],
        ) if *d == v && g64(x) && g64(y) => Some(source(x)?.wrapping_mul(source(y)?)),
        _ => None,
    }
}

/// Fold a block-local constant SIB index into the displacement:
///
/// ```text
///   mov  i, 3                       ; or any `local_const_value` form
///   mov  dst, [base + i*8 + 16]     ; MovRMSib
/// ```
///
/// becomes `mov dst, [base + 40]` (`MovRM`). Stores and the 32-bit forms
/// likewise. The instruction keeps its position and its base register, so no
/// register is read at a new program point.
///
/// # Why the rewrite is exact
///
/// The SIB operand addresses `base + i*scale + sext(disp)` modulo 2^64. With
/// `i` equal to the constant `K` the offset is `K*scale + disp`. The fold
/// fires only when that sum is exact in `i64` and fits a sign-extended 32-bit
/// displacement, so the new operand `[base + disp']` names the same address.
///
/// # Side conditions (any failure leaves the instruction alone)
///
/// * The anchor is `MovRMSib`/`MovMRSib` over a `Gpr64` value or
///   `MovRM32Sib`/`MovMR32Sib` over a `Gpr32` value, with default flags and no
///   `proof_origin`, exactly two operands.
/// * Its base and index are `Gpr64` virtual registers and its scale is 1, 2,
///   4 or 8. A stack-slot or physical-register base is left to its own folds.
/// * [`local_const_value`] names the index's value at the anchor.
/// * `K*scale + disp` does not overflow `i64` and fits `i32`.
///
/// Rewrite-only: never deletes instructions (DCE owns the sweep). Returns
/// whether anything changed.
fn sib_const_index_fold_run_on_block(
    func: &mut X86ISelFunction,
    block_id: trust_cg_lower::instructions::Block,
) -> bool {
    let Some(block) = func.blocks.get(&block_id) else {
        return false;
    };
    let insts = &block.insts;

    let mut rewrites: Vec<(usize, X86Opcode, usize, X86ISelOperand)> = Vec::new();
    for (mem_idx, inst) in insts.iter().enumerate() {
        let (new_opcode, addr_slot, value_class) = match inst.opcode {
            X86Opcode::MovRMSib => (X86Opcode::MovRM, 1, RegClass::Gpr64),
            X86Opcode::MovMRSib => (X86Opcode::MovMR, 0, RegClass::Gpr64),
            X86Opcode::MovRM32Sib => (X86Opcode::MovRM32, 1, RegClass::Gpr32),
            X86Opcode::MovMR32Sib => (X86Opcode::MovMR32, 0, RegClass::Gpr32),
            _ => continue,
        };
        if inst.proof_origin.is_some()
            || inst.flags != inst.opcode.default_flags()
            || inst.operands.len() != 2
        {
            continue;
        }
        if !matches!(&inst.operands[1 - addr_slot], X86ISelOperand::VReg(r) if r.class == value_class)
        {
            continue;
        }
        let X86ISelOperand::SibMemAddr {
            base,
            index,
            scale,
            disp,
        } = &inst.operands[addr_slot]
        else {
            continue;
        };
        let (X86ISelOperand::VReg(b), X86ISelOperand::VReg(i)) = (base.as_ref(), index.as_ref())
        else {
            continue;
        };
        if b.class != RegClass::Gpr64 || !matches!(*scale, 1 | 2 | 4 | 8) {
            continue;
        }
        let Some(k) = local_const_value(insts, mem_idx, *i, LOCAL_CONST_MAX_DEPTH) else {
            continue;
        };
        let Some(new_disp) = k
            .checked_mul(i64::from(*scale))
            .and_then(|offset| offset.checked_add(i64::from(*disp)))
            .and_then(|offset| i32::try_from(offset).ok())
        else {
            continue;
        };
        rewrites.push((
            mem_idx,
            new_opcode,
            addr_slot,
            X86ISelOperand::MemAddr {
                base: Box::new(X86ISelOperand::VReg(*b)),
                disp: new_disp,
            },
        ));
    }

    if rewrites.is_empty() {
        return false;
    }

    // The scan above only reads `func`, and the block was found at entry.
    let block = func.blocks.get_mut(&block_id).expect("block existed above");
    for (mem_idx, new_opcode, addr_slot, new_addr) in rewrites {
        let mem = &mut block.insts[mem_idx];
        mem.opcode = new_opcode;
        mem.flags = new_opcode.default_flags();
        mem.operands[addr_slot] = new_addr;
    }
    true
}

/// A clean, single-def base-`Lea` recorded function-wide for the SIB-base fold:
/// `Lea b, [MemAddr{ base, disp }]` located at (`block`, `idx`).
struct LeaBaseDef {
    base: X86ISelOperand,
    disp: i32,
    block: trust_cg_lower::instructions::Block,
    idx: usize,
}

/// Fold a base-defining `Lea` into the BASE of an already-formed indexed SIB
/// memory operand.
///
/// After `sib_addr_fold`/`addr_chain_fold` have formed the SIB load, a stack
/// array access is still `Lea b, [MemAddr{ Base, d0 }]` (Base a `StackSlot` or
/// gpr64 `VReg`) feeding a single
/// `Mov*Sib dst, [SibMemAddr{ base: b, index, scale, disp: d1 }]`. This
/// substitutes `Base` for `b` and folds `d0` into the SIB displacement, yielding
/// `Mov*Sib [Base + index*scale + (d0+d1)]` and leaving the now-dead `Lea` for
/// DCE. It eliminates the redundant `leaq -N(%rbp)` trust-cg recomputes on every
/// stack/local-array access (which LLVM folds natively into
/// `disp(%rbp,idx,scale)`), the dominant instruction-count gap on the
/// sort/matmul cluster.
///
/// # Soundness (rewrite-only; the per-instruction reconstruction gate already
/// covers the `SibMemAddr{ base: StackSlot|VReg, .. }` family — base-agnostic EA
/// proof — so there is no new SMT obligation; this is the pass's hand-proof):
///   original EA = (frame(Base) + sext(d0)) + index*scale + sext(d1)
///   folded   EA =  frame(Base) + index*scale + sext(d0 + d1)
/// These are equal iff `sext(d0 + d1) == sext(d0) + sext(d1)` in 64 bits, i.e.
/// iff the integer sum `d0 + d1` fits in `i32` — the ONLY wrap concern, closed by
/// the mandatory `checked_add` + `i32::try_from` bail. `b` is required single-def
/// + single-use function-wide (the `Lea` is its only def, this load its only
///   use), so the substitution has no other reader and the `Lea` is trivially dead.
///   A `StackSlot` base is frame-invariant (same value at Lea and anchor with no
///   range check); a `VReg` base must not be redefined between the `Lea` and the
///   anchor (`no_def_in_range`). Both instructions must carry default flags and no
///   `proof_origin` (preserves atomic/volatile load/store proofs). The index is
///   untouched.
///   Resolve `b` through single-def `MovRR` copies (`copy_src`) to the clean
///   `StackSlot`/`VReg`-based `Lea` that ultimately defines its value, if any.
///   Bounded to avoid cycles. A copy preserves its source's value, so for a
///   frame-invariant `StackSlot` LEA the resolved base holds the same address.
fn resolve_sib_base_lea<'a>(
    mut b: VReg,
    lea_defs: &'a FxHashMap<VReg, LeaBaseDef>,
    copy_src: &FxHashMap<VReg, VReg>,
) -> Option<&'a LeaBaseDef> {
    for _ in 0..16 {
        if let Some(ld) = lea_defs.get(&b) {
            return Some(ld);
        }
        match copy_src.get(&b) {
            Some(&s) => b = s,
            None => return None,
        }
    }
    None
}

fn sib_base_lea_fold_run_on_block(
    func: &mut X86ISelFunction,
    block_id: trust_cg_lower::instructions::Block,
    maps: &FnUseDefCounts,
    lea_defs: &FxHashMap<VReg, LeaBaseDef>,
    copy_src: &FxHashMap<VReg, VReg>,
) -> bool {
    let Some(block) = func.blocks.get(&block_id) else {
        return false;
    };
    let insts = &block.insts;

    struct Rewrite {
        mem_idx: usize,
        new_addr: X86ISelOperand,
    }
    let mut rewrites: Vec<Rewrite> = Vec::new();

    for mem_idx in 0..insts.len() {
        let anchor = &insts[mem_idx];
        if anchor.proof_origin.is_some() || anchor.flags != anchor.opcode.default_flags() {
            continue;
        }
        if !matches!(
            anchor.opcode,
            X86Opcode::MovRM32Sib
                | X86Opcode::MovRMSib
                | X86Opcode::MovMR32Sib
                | X86Opcode::MovMRSib
                | X86Opcode::MovRM8Sib
                | X86Opcode::MovMR8Sib
                | X86Opcode::MovzxRM8Sib
                // Scalar-FP SIB loads participate too: a stack-allocated float
                // array (`let a = [0f64; N]`) otherwise re-materializes its
                // base LEA per access exactly like the GPR case.
                | X86Opcode::MovsdRMSib
                | X86Opcode::MovssRMSib
        ) {
            continue;
        }
        // Extract the SIB operand; its base must be a Gpr64 VReg `b`.
        let Some((b, index_op, scale, d1)) = anchor.operands.iter().find_map(|op| match op {
            X86ISelOperand::SibMemAddr {
                base,
                index,
                scale,
                disp,
            } => match base.as_ref() {
                X86ISelOperand::VReg(b) if b.class == RegClass::Gpr64 => {
                    Some((*b, index.clone(), *scale, *disp))
                }
                _ => None,
            },
            _ => None,
        }) else {
            continue;
        };

        // Resolve `b` (possibly a `MovRR` copy of the base) to the clean `Lea`
        // that defines its value.
        let Some(lea) = resolve_sib_base_lea(b, lea_defs, copy_src) else {
            continue;
        };

        // Base foldability:
        //  - `StackSlot`: frame-invariant, so substituting it into this SIB
        //    operand is sound regardless of which block the `Lea` is in, how many
        //    `MovRR` copies separate `b` from the `Lea`, and how many times `b` is
        //    used (each SIB use folds independently; once all uses of the copy
        //    chain are folded, the copies + `Lea` go dead and DCE sweeps them).
        //  - Gpr64 `VReg`: a register base can be clobbered, so restrict to the
        //    DIRECT (uncopied) case: `b` itself is the `Lea`, same block, single
        //    function-wide use, no redef between the `Lea` and the anchor.
        let base_ok = match &lea.base {
            X86ISelOperand::StackSlot(_) => true,
            X86ISelOperand::VReg(r) if r.class == RegClass::Gpr64 => {
                lea_defs.contains_key(&b)
                    && lea.block == block_id
                    && lea.idx < mem_idx
                    && maps.use_count(b) == 1
                    && no_def_in_range(insts, lea.idx + 1, mem_idx, *r)
            }
            _ => false,
        };
        if !base_ok {
            continue;
        }

        // Fold the displacements; bail if the i32 SIB disp would overflow (the
        // only wrap concern — see the soundness note).
        let Some(new_disp) = i64::from(lea.disp)
            .checked_add(i64::from(d1))
            .and_then(|s| i32::try_from(s).ok())
        else {
            continue;
        };

        rewrites.push(Rewrite {
            mem_idx,
            new_addr: X86ISelOperand::SibMemAddr {
                base: Box::new(lea.base.clone()),
                index: index_op,
                scale,
                disp: new_disp,
            },
        });
    }

    if rewrites.is_empty() {
        return false;
    }

    // `sib_base_lea_fold_run_on_block` opens with
    // `let Some(block) = func.blocks.get(&block_id) else { return false }`;
    // the rewrite-collection scan between there and here only reads `func`.
    let block = func.blocks.get_mut(&block_id).expect("block existed above");
    for r in rewrites {
        for op in block.insts[r.mem_idx].operands.iter_mut() {
            if matches!(op, X86ISelOperand::SibMemAddr { .. }) {
                *op = r.new_addr;
                break;
            }
        }
    }
    true
}

#[cfg(test)]
mod tests {
    use super::*;

    use trust_cg_ir::regs::{RegClass, VReg};
    use trust_cg_ir::x86_64_regs::RAX;
    use trust_cg_ir::{InstFlags, X86CondCode};
    use trust_cg_lower::function::Signature;
    use trust_cg_lower::instructions::Block;
    use trust_cg_lower::types::Type;
    use trust_cg_lower::x86_64_isel::X86ProofOrigin;

    use crate::X86PassManager;

    fn vreg(id: u32) -> X86ISelOperand {
        X86ISelOperand::VReg(VReg::new(id, RegClass::Gpr64))
    }

    fn vreg32(id: u32) -> X86ISelOperand {
        X86ISelOperand::VReg(VReg::new(id, RegClass::Gpr32))
    }

    fn vreg_class(id: u32, class: RegClass) -> X86ISelOperand {
        X86ISelOperand::VReg(VReg::new(id, class))
    }

    fn make_func(insts: Vec<X86ISelInst>) -> X86ISelFunction {
        let sig = Signature {
            params: vec![],
            returns: vec![Type::I64],
        };
        let mut func = X86ISelFunction::new("x86_peephole_test".to_string(), sig);
        let entry = Block(0);
        func.ensure_block(entry);
        func.next_vreg = 16;
        for inst in insts {
            func.push_inst(entry, inst);
        }
        func
    }

    fn entry_insts(func: &X86ISelFunction) -> &[X86ISelInst] {
        &func.blocks.get(&Block(0)).unwrap().insts
    }

    fn entry_opcodes(func: &X86ISelFunction) -> Vec<X86Opcode> {
        entry_insts(func).iter().map(|inst| inst.opcode).collect()
    }

    /// REPRODUCER for the dead address chain measured in `b1_mispredict`'s hot
    /// loop (`reports/perf/2026-09-28-linux-x86-64-first-runtime/`): after the SIB
    /// fold rewrites a store's address into `[slot + index*8]`, the `imul`/`add`
    /// chain that computed the old address should be swept.
    ///
    /// The shipped code keeps `movq %r13,%rcx ; addq %rax,%rcx` in that loop with
    /// nothing reading it, and the cause was NOT established by reading — frame
    /// lowering only rewrites operands, and DCE runs immediately after this pass
    /// with `AddRR` in its pure flag-writing allowlist. This test asks the question
    /// directly on the exact shape, so the answer is a pass/fail rather than an
    /// argument.
    #[test]
    fn sib_fold_retires_the_whole_address_chain_when_flags_are_dead() {
        // v1 = &slot0 ; v3 = v2 * 8 ; v4 = v1 + v3 ; v5 = v4 ; [v5] = v6
        let mut func = make_func(vec![
            X86ISelInst::new(
                X86Opcode::Lea,
                vec![
                    vreg(1),
                    X86ISelOperand::MemAddr {
                        base: Box::new(X86ISelOperand::StackSlot(0)),
                        disp: 0,
                    },
                ],
            ),
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(7), X86ISelOperand::Imm(8)]),
            X86ISelInst::new(X86Opcode::ImulRR, vec![vreg(3), vreg(2), vreg(7)]),
            X86ISelInst::new(X86Opcode::AddRR, vec![vreg(4), vreg(1), vreg(3)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(5), vreg(4)]),
            X86ISelInst::new(
                X86Opcode::MovMR,
                vec![
                    X86ISelOperand::MemAddr {
                        base: Box::new(vreg(5)),
                        disp: 0,
                    },
                    vreg(6),
                ],
            ),
        ]);
        func.stack_slots = vec![trust_cg_lower::function::StackSlotInfo::new(128, 8)];
        // The latch of a real loop body: a FULL flag overwrite after the store,
        // then the terminator. The DCE flag obligation
        // (`flags_written_here_are_dead`) is discharged by that overwrite and
        // NOT by the terminator — see the companion test below, which drops the
        // `cmp` and pins that the sweep then correctly declines.
        func.push_inst(
            Block(0),
            X86ISelInst::new(X86Opcode::CmpRR, vec![vreg(8), vreg(9)]),
        );
        func.push_inst(Block(0), X86ISelInst::new(X86Opcode::Ret, vec![]));

        let before = entry_opcodes(&func);
        let mut pm = X86PassManager::new()
            .with_pass(Box::new(crate::X86Peephole::default()))
            .with_pass(Box::new(crate::X86DeadCodeElimination));
        pm.run_once(&mut func);
        let after = entry_opcodes(&func);

        let store_folded = entry_insts(&func)
            .iter()
            .any(|i| matches!(i.opcode, X86Opcode::MovMRSib));
        for i in entry_insts(&func) {
            eprintln!("[sib-fold-dce]   {:?} {:?}", i.opcode, i.operands);
        }
        let imuls = after.iter().filter(|o| **o == X86Opcode::ImulRR).count();
        let adds = after.iter().filter(|o| **o == X86Opcode::AddRR).count();

        // Record what actually happened either way: this test exists to ANSWER
        // the question, so a decline is as informative as a fold.
        eprintln!(
            "[sib-fold-dce] before={before:?}\n[sib-fold-dce] after={after:?}\n\
             [sib-fold-dce] store_folded_to_sib={store_folded} imul_left={imuls} add_left={adds}"
        );

        assert!(
            store_folded,
            "the store must fold to a SIB address for this test to mean anything: {after:?}"
        );
        assert_eq!(
            adds, 0,
            "the scale-8 arm supersedes the address computation, so no `add` remains: \
             {after:?}"
        );
        assert_eq!(
            imuls, 0,
            "the scale-8 arm scales inside the SIB operand, so the explicit `imul` is \
             retired too: {after:?}"
        );
        assert_eq!(
            after.iter().filter(|o| **o == X86Opcode::Lea).count(),
            0,
            "the SIB operand names the slot directly, so the `lea` that materialised \
             its address is retired as well: {after:?}"
        );
        // Exactness, not just a count: the surviving store must address the slot
        // with the RAW index at scale 8. Folding the PRE-SCALED index at scale 1
        // would also erase the `add`, but only by keeping the `imul` alive — and
        // asserting on counts alone would not tell the two apart.
        let store = entry_insts(&func)
            .iter()
            .find(|i| i.opcode == X86Opcode::MovMRSib)
            .expect("the folded store")
            .clone();
        match &store.operands[0] {
            X86ISelOperand::SibMemAddr {
                base,
                index,
                scale,
                disp,
            } => {
                assert_eq!(**base, X86ISelOperand::StackSlot(0), "slot base: {store:?}");
                assert_eq!(
                    **index,
                    vreg(2),
                    "the RAW index, not the product: {store:?}"
                );
                assert_eq!(*scale, 8, "scaled inside the operand: {store:?}");
                assert_eq!(*disp, 0);
            }
            other => panic!("expected a SIB address, got {other:?}"),
        }
    }

    /// The FALLBACK arm, and its cost, pinned exactly.
    ///
    /// `sib_fold_flags_dead` is what selects between the two arms, and it needs a
    /// FULL flag overwrite before any flag reader, refusing at a call, branch,
    /// terminator, or the end of the block. Drop the `cmp` from the companion test
    /// above and that proof fails, so the scale-8 arm cannot fire: the fold takes
    /// the scale-1 arm instead, addressing the slot with the PRE-SCALED index. The
    /// `imul` therefore stays live, and the `add` — whose VALUE nothing reads any
    /// more — stays too, because its RFLAGS write is exactly what could not be
    /// proven dead.
    ///
    /// This is the shape the `b1_mispredict` benchmark ships
    /// (`imul $8,%rsi,%rax` / `add %rax,%rcx` / `mov %rbx,-0xa8(%rbp,%rax,1)`), so
    /// this test is where to start when revisiting that sequence. Deleting the
    /// `add` here would need its flags proven dead, which is the same obligation
    /// that already failed — so the cost is NOT recoverable by a dead-code pass,
    /// only by widening the flag-deadness proof or by scaling inside the operand.
    /// (A DCE tier for value-dead flag-writing ALU was written and measured for
    /// this: it fires zero times on the codegen corpus, because whenever its flag
    /// obligation holds the scale-8 arm has already retired the chain. It was not
    /// kept.)
    #[test]
    fn sib_fold_falls_back_to_scale_1_and_retains_the_chain_when_flags_may_be_live() {
        let mut func = make_func(vec![
            X86ISelInst::new(
                X86Opcode::Lea,
                vec![
                    vreg(1),
                    X86ISelOperand::MemAddr {
                        base: Box::new(X86ISelOperand::StackSlot(0)),
                        disp: 0,
                    },
                ],
            ),
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(7), X86ISelOperand::Imm(8)]),
            X86ISelInst::new(X86Opcode::ImulRR, vec![vreg(3), vreg(2), vreg(7)]),
            X86ISelInst::new(X86Opcode::AddRR, vec![vreg(4), vreg(1), vreg(3)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(5), vreg(4)]),
            X86ISelInst::new(
                X86Opcode::MovMR,
                vec![
                    X86ISelOperand::MemAddr {
                        base: Box::new(vreg(5)),
                        disp: 0,
                    },
                    vreg(6),
                ],
            ),
        ]);
        func.stack_slots = vec![trust_cg_lower::function::StackSlotInfo::new(128, 8)];
        // No flag overwrite and no terminator: flags fall off the block end.
        let mut pm = X86PassManager::new()
            .with_pass(Box::new(crate::X86Peephole::default()))
            .with_pass(Box::new(crate::X86DeadCodeElimination));
        pm.run_once(&mut func);
        let after = entry_opcodes(&func);

        assert_eq!(
            after.iter().filter(|o| **o == X86Opcode::AddRR).count(),
            1,
            "the `add`'s destination is unread, but its RFLAGS write may be live-out, \
             so no pass here is entitled to delete it: {after:?}"
        );
        let store = entry_insts(&func)
            .iter()
            .find(|i| i.opcode == X86Opcode::MovMRSib)
            .expect("the fallback arm still folds the store")
            .clone();
        match &store.operands[0] {
            X86ISelOperand::SibMemAddr { index, scale, .. } => {
                assert_eq!(
                    *scale, 1,
                    "the fallback arm addresses at scale 1: {store:?}"
                );
                assert_eq!(
                    **index,
                    vreg(3),
                    "and with the PRE-SCALED product as the index, which is what keeps \
                     the `imul` live: {store:?}"
                );
            }
            other => panic!("expected a SIB address, got {other:?}"),
        }
        assert_eq!(
            after
                .iter()
                .filter(|o| matches!(o, X86Opcode::ImulRR | X86Opcode::ImulRRI))
                .count(),
            1,
            "the `imul` is live: the SIB operand reads its product: {after:?}"
        );
    }

    #[test]
    fn cfg_analysis_preserves_flags_across_partial_writes() {
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::AddRR, vec![vreg(0), vreg(1), vreg(2)]),
            X86ISelInst::new(X86Opcode::Inc, vec![vreg(3)]),
            X86ISelInst::new(X86Opcode::Jmp, vec![X86ISelOperand::Block(Block(1))]),
        ]);
        func.ensure_block(Block(1));
        func.blocks.get_mut(&Block(0)).unwrap().successors = vec![Block(1)];
        func.push_inst(Block(1), X86ISelInst::new(X86Opcode::Dec, vec![vreg(4)]));
        func.push_inst(
            Block(1),
            X86ISelInst::new(
                X86Opcode::Setcc,
                vec![vreg32(5), X86ISelOperand::CondCode(X86CondCode::B)],
            ),
        );
        let live_in = flags_live_in_by_block(&func);
        assert!(live_in[&Block(1)], "DEC preserves incoming carry");
        assert!(!flags_dead_at(&func, &live_in, Block(0), 0));
    }

    #[test]
    fn self_test_preserves_flags_across_partial_writes() {
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::AddRR, vec![vreg(0), vreg(1), vreg(2)]),
            X86ISelInst::new(X86Opcode::TestRR, vec![vreg(0), vreg(0)]),
            X86ISelInst::new(X86Opcode::Inc, vec![vreg(3)]),
            X86ISelInst::new(
                X86Opcode::Setcc,
                vec![vreg32(4), X86ISelOperand::CondCode(X86CondCode::B)],
            ),
        ]);
        assert!(!redundant_self_test_elision_run_on_block(
            &mut func,
            Block(0)
        ));
        assert_eq!(entry_insts(&func)[1].opcode, X86Opcode::TestRR);
    }

    #[test]
    fn self_test_preserves_flags_read_in_successor() {
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::AddRR, vec![vreg(0), vreg(1), vreg(2)]),
            X86ISelInst::new(X86Opcode::TestRR, vec![vreg(0), vreg(0)]),
            X86ISelInst::new(X86Opcode::Jmp, vec![X86ISelOperand::Block(Block(1))]),
        ]);
        func.ensure_block(Block(1));
        func.blocks.get_mut(&Block(0)).unwrap().successors = vec![Block(1)];
        func.push_inst(
            Block(1),
            X86ISelInst::new(
                X86Opcode::Setcc,
                vec![vreg32(4), X86ISelOperand::CondCode(X86CondCode::B)],
            ),
        );
        assert!(!redundant_self_test_elision_run_on_block(
            &mut func,
            Block(0)
        ));
        // A full overwrite at successor entry makes the self-test removable.
        func.blocks.get_mut(&Block(1)).unwrap().insts.insert(
            0,
            X86ISelInst::new(X86Opcode::AddRR, vec![vreg(5), vreg(1), vreg(2)]),
        );
        assert!(redundant_self_test_elision_run_on_block(
            &mut func,
            Block(0)
        ));
    }

    #[test]
    fn self_test_preserves_flags_across_call_barriers() {
        for call_index in [1, 2] {
            let mut func = make_func(vec![
                X86ISelInst::new(X86Opcode::AddRR, vec![vreg(0), vreg(1), vreg(2)]),
                X86ISelInst::new(X86Opcode::TestRR, vec![vreg(0), vreg(0)]),
                X86ISelInst::new(
                    X86Opcode::Setcc,
                    vec![vreg32(3), X86ISelOperand::CondCode(X86CondCode::E)],
                ),
            ]);
            func.blocks
                .get_mut(&Block(0))
                .unwrap()
                .insts
                .insert(call_index, X86ISelInst::new(X86Opcode::Call, vec![]));
            assert!(
                !redundant_self_test_elision_run_on_block(&mut func, Block(0)),
                "call at {call_index} must block self-test elision"
            );
        }
    }

    fn self_test_window(test: X86ISelInst, middle: Option<X86ISelInst>) -> X86ISelFunction {
        let mut insts = vec![X86ISelInst::new(
            X86Opcode::AddRR,
            vec![test.operands[0].clone(), vreg(1), vreg(2)],
        )];
        insts.extend(middle);
        insts.push(test);
        insts.push(X86ISelInst::new(
            X86Opcode::Setcc,
            vec![vreg32(4), X86ISelOperand::CondCode(X86CondCode::E)],
        ));
        insts.push(X86ISelInst::new(X86Opcode::Ret, vec![]));
        make_func(insts)
    }

    #[test]
    fn self_test_refuses_narrow_alias_redefinition() {
        for test in [
            X86ISelInst::new(X86Opcode::TestRR, vec![vreg(0), vreg(0)]),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(0), X86ISelOperand::Imm(0)]),
        ] {
            // ADD result 1 leaves ZF=0; copying a zero through the 32-bit
            // alias changes the whole register without changing flags. The
            // following test MUST set ZF=1 before SETE.
            let mut func = self_test_window(
                test,
                Some(X86ISelInst::new(
                    X86Opcode::MovRR32,
                    vec![vreg32(0), vreg32(3)],
                )),
            );
            assert!(!redundant_self_test_elision_run_on_block(
                &mut func,
                Block(0)
            ));
            assert_eq!(entry_insts(&func).len(), 5);
        }
    }

    #[test]
    fn self_test_refuses_wide_alias_redefinition() {
        let test = X86ISelInst::new(X86Opcode::TestRR, vec![vreg32(0), vreg32(0)]);
        let mut func = self_test_window(
            test,
            Some(X86ISelInst::new(X86Opcode::MovRR, vec![vreg(0), vreg(3)])),
        );
        let anchor = &mut func.blocks.get_mut(&Block(0)).unwrap().insts[0];
        anchor.operands = vec![vreg32(0), vreg32(1), vreg32(2)];
        assert!(!redundant_self_test_elision_run_on_block(
            &mut func,
            Block(0)
        ));
        assert_eq!(entry_insts(&func).len(), 5);
    }

    #[test]
    fn self_test_preserves_proof_metadata() {
        for annotated_at in 0..4 {
            let mut func = self_test_window(
                X86ISelInst::new(X86Opcode::TestRR, vec![vreg(0), vreg(0)]),
                Some(X86ISelInst::new(X86Opcode::MovRR, vec![vreg(6), vreg(7)])),
            );
            func.blocks.get_mut(&Block(0)).unwrap().insts[annotated_at].proof_origin =
                Some(X86ProofOrigin::AtomicLoad);
            let before = entry_insts(&func).to_vec();
            assert!(
                !redundant_self_test_elision_run_on_block(&mut func, Block(0)),
                "proof-annotated instruction at {annotated_at} cannot be removed or crossed"
            );
            let after = entry_insts(&func);
            assert_eq!(before.len(), after.len());
            for (before, after) in before.iter().zip(after) {
                assert_eq!(before.opcode, after.opcode);
                assert_eq!(before.operands, after.operands);
                assert_eq!(before.flags, after.flags);
                assert_eq!(before.proof_origin, after.proof_origin);
            }
        }
    }

    #[test]
    fn self_test_preserves_custom_flags() {
        for guarded_at in 0..4 {
            let mut func = self_test_window(
                X86ISelInst::new(X86Opcode::TestRR, vec![vreg(0), vreg(0)]),
                Some(X86ISelInst::new(X86Opcode::MovRR, vec![vreg(6), vreg(7)])),
            );
            let guarded = &mut func.blocks.get_mut(&Block(0)).unwrap().insts[guarded_at];
            guarded.flags = guarded.flags.union(InstFlags::READS_MEMORY);
            let before = entry_insts(&func).to_vec();
            assert!(!redundant_self_test_elision_run_on_block(
                &mut func,
                Block(0)
            ));
            assert!(writeback_instructions_unchanged(
                &before,
                entry_insts(&func)
            ));
        }
    }

    #[test]
    fn self_test_requires_exact_shape_and_definition_width() {
        let mut extra = X86ISelInst::new(X86Opcode::TestRR, vec![vreg(0), vreg(0)]);
        extra.operands.push(vreg(8));
        let mut malformed = self_test_window(extra, None);
        assert!(!redundant_self_test_elision_run_on_block(
            &mut malformed,
            Block(0)
        ));

        let mut mixed = self_test_window(
            X86ISelInst::new(X86Opcode::TestRR, vec![vreg32(0), vreg32(0)]),
            None,
        );
        mixed.blocks.get_mut(&Block(0)).unwrap().insts[0].operands[0] = vreg(0);
        // A nonzero 64-bit result may have zero low bits. It cannot establish
        // ZF for a narrower test even though the canonical register ID agrees.
        assert!(!redundant_self_test_elision_run_on_block(
            &mut mixed,
            Block(0)
        ));
    }

    #[test]
    fn self_test_keeps_secondary_exchange_writes() {
        let mut func = self_test_window(
            X86ISelInst::new(X86Opcode::TestRR, vec![vreg(0), vreg(0)]),
            Some(X86ISelInst::new(X86Opcode::Xchg, vec![vreg(7), vreg(0)])),
        );
        assert!(!redundant_self_test_elision_run_on_block(
            &mut func,
            Block(0)
        ));
        assert_eq!(entry_insts(&func).len(), 5);
    }

    #[test]
    fn self_test_removes_only_redundant_unannotated_tests() {
        for test in [
            X86ISelInst::new(X86Opcode::TestRR, vec![vreg(0), vreg(0)]),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(0), X86ISelOperand::Imm(0)]),
        ] {
            let mut func = self_test_window(
                test,
                Some(X86ISelInst::new(X86Opcode::MovRR, vec![vreg(6), vreg(7)])),
            );
            let before = entry_insts(&func).to_vec();
            assert!(redundant_self_test_elision_run_on_block(
                &mut func,
                Block(0)
            ));
            let expected = [
                before[0].clone(),
                before[1].clone(),
                before[3].clone(),
                before[4].clone(),
            ];
            assert!(writeback_instructions_unchanged(
                &expected,
                entry_insts(&func)
            ));
        }
    }

    #[test]
    fn self_test_policy_isolated_public_optimizer() {
        const CHILD: &str = "CG_SELF_TEST_POLICY_CASE";
        const TEST: &str = "x86_peephole::tests::self_test_policy_isolated_public_optimizer";
        let Ok(case) = std::env::var(CHILD) else {
            let mut failures = Vec::new();
            for case in [
                "default",
                "zero",
                "one",
                "empty",
                "installed_on",
                "installed_off",
            ] {
                let mut command = std::process::Command::new(std::env::current_exe().unwrap());
                command.args(["--exact", TEST, "--nocapture", "--test-threads=1"]);
                for (key, _) in std::env::vars_os() {
                    if key.to_string_lossy().starts_with("TCG_")
                        || key.to_string_lossy().starts_with("TRUST_CG_")
                    {
                        command.env_remove(key);
                    }
                }
                command.env(CHILD, case);
                match case {
                    "zero" | "installed_on" => {
                        command.env("TCG_X86_TEST_ELIDE", "0");
                    }
                    "one" | "installed_off" => {
                        command.env("TCG_X86_TEST_ELIDE", "1");
                    }
                    "empty" => {
                        command.env("TCG_X86_TEST_ELIDE", "");
                    }
                    _ => {}
                }
                let output = command.output().unwrap();
                println!(
                    "case {case}:\n{}{}",
                    String::from_utf8_lossy(&output.stdout),
                    String::from_utf8_lossy(&output.stderr)
                );
                if !output.status.success() {
                    failures.push(case);
                }
            }
            assert!(failures.is_empty(), "failed cases: {failures:?}");
            return;
        };
        if case.starts_with("installed_") {
            let enabled = case == "installed_on";
            assert!(set_test_elide_enabled(enabled));
            assert!(set_test_elide_enabled(enabled));
            assert!(!set_test_elide_enabled(!enabled));
        }
        let enabled = matches!(case.as_str(), "one" | "empty" | "installed_on");
        for clobber in [false, true] {
            let mut func = self_test_window(
                X86ISelInst::new(X86Opcode::TestRR, vec![vreg(0), vreg(0)]),
                clobber.then(|| X86ISelInst::new(X86Opcode::MovRR32, vec![vreg32(0), vreg32(3)])),
            );
            X86Peephole::default().run_on_function(&mut func);
            assert_eq!(
                entry_opcodes(&func).contains(&X86Opcode::TestRR),
                !enabled || clobber
            );
        }
    }

    // ---- sib_base_lea_fold tests -----------------------------------------

    fn lea_base(dst: u32, base: X86ISelOperand, disp: i32) -> X86ISelInst {
        X86ISelInst::new(
            X86Opcode::Lea,
            vec![
                vreg(dst),
                X86ISelOperand::MemAddr {
                    base: Box::new(base),
                    disp,
                },
            ],
        )
    }

    fn movrm32_sib(dst: u32, base: u32, index: u32, scale: u8, disp: i32) -> X86ISelInst {
        X86ISelInst::new(
            X86Opcode::MovRM32Sib,
            vec![
                vreg32(dst),
                X86ISelOperand::SibMemAddr {
                    base: Box::new(vreg(base)),
                    index: Box::new(vreg(index)),
                    scale,
                    disp,
                },
            ],
        )
    }

    fn run_sib_base_fold(func: &mut X86ISelFunction) -> bool {
        let maps = FnUseDefCounts::build(func);
        let mut lea_defs: FxHashMap<VReg, LeaBaseDef> = FxHashMap::default();
        for (block_id, block) in &func.blocks {
            for (idx, inst) in block.insts.iter().enumerate() {
                if inst.opcode == X86Opcode::Lea
                    && inst.proof_origin.is_none()
                    && inst.flags == inst.opcode.default_flags()
                    && let [
                        X86ISelOperand::VReg(d),
                        X86ISelOperand::MemAddr { base, disp },
                    ] = inst.operands.as_slice()
                    && maps.def_count(*d) == 1
                {
                    lea_defs.insert(
                        *d,
                        LeaBaseDef {
                            base: base.as_ref().clone(),
                            disp: *disp,
                            block: *block_id,
                            idx,
                        },
                    );
                }
            }
        }
        let mut copy_src: FxHashMap<VReg, VReg> = FxHashMap::default();
        for block in func.blocks.values() {
            for inst in &block.insts {
                if inst.opcode == X86Opcode::MovRR
                    && let [X86ISelOperand::VReg(d), X86ISelOperand::VReg(s)] =
                        inst.operands.as_slice()
                    && maps.def_count(*d) == 1
                {
                    copy_src.insert(*d, *s);
                }
            }
        }
        sib_base_lea_fold_run_on_block(func, Block(0), &maps, &lea_defs, &copy_src)
    }

    fn sib_addr(inst: &X86ISelInst) -> (&X86ISelOperand, &X86ISelOperand, u8, i32) {
        for op in &inst.operands {
            if let X86ISelOperand::SibMemAddr {
                base,
                index,
                scale,
                disp,
            } = op
            {
                return (base.as_ref(), index.as_ref(), *scale, *disp);
            }
        }
        panic!("no SibMemAddr operand");
    }

    #[test]
    fn sib_base_fold_stackslot_folds_and_leaves_lea_for_dce() {
        // Lea b(2), [StackSlot(3) + 8]; MovRM32Sib d, [b + idx(1)*4 + 16]
        //   => MovRM32Sib d, [StackSlot(3) + idx*4 + 24]
        let mut func = make_func(vec![
            lea_base(2, X86ISelOperand::StackSlot(3), 8),
            movrm32_sib(10, 2, 1, 4, 16),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(run_sib_base_fold(&mut func));
        let insts = entry_insts(&func);
        let (base, index, scale, disp) = sib_addr(&insts[1]);
        assert_eq!(*base, X86ISelOperand::StackSlot(3));
        assert_eq!(*index, vreg(1));
        assert_eq!(scale, 4);
        assert_eq!(disp, 24); // 8 + 16
        // The Lea is left in place (dead) for DCE to sweep.
        assert_eq!(insts[0].opcode, X86Opcode::Lea);
    }

    /// A stack-allocated f64 array (`let a = [0f64; N]`) must fold its base LEA
    /// exactly like the GPR case — this is b11_float_dot's actual shape.
    #[test]
    fn sib_base_fold_folds_scalar_fp_load() {
        let mut func = make_func(vec![
            lea_base(2, X86ISelOperand::StackSlot(3), 8),
            X86ISelInst::new(
                X86Opcode::MovsdRMSib,
                vec![
                    vreg(10),
                    X86ISelOperand::SibMemAddr {
                        base: Box::new(vreg(2)),
                        index: Box::new(vreg(1)),
                        scale: 8,
                        disp: 16,
                    },
                ],
            ),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(run_sib_base_fold(&mut func));
        let insts = entry_insts(&func);
        let (base, index, scale, disp) = sib_addr(&insts[1]);
        assert_eq!(*base, X86ISelOperand::StackSlot(3));
        assert_eq!(*index, vreg(1));
        assert_eq!(scale, 8);
        assert_eq!(disp, 24); // 8 + 16
        assert_eq!(insts[1].opcode, X86Opcode::MovsdRMSib);
    }

    /// The address fold must turn a scalar-FP load's plain base into a SIB
    /// operand, and must REFUSE to do so for the STORE form — there is
    /// deliberately no MovsdMRSib opcode to fold into.
    #[test]
    fn sib_addr_fold_admits_fp_load_and_refuses_fp_store() {
        let load = X86ISelInst::new(
            X86Opcode::MovsdRM,
            vec![
                vreg(10),
                X86ISelOperand::MemAddr {
                    base: Box::new(vreg(2)),
                    disp: 0,
                },
            ],
        );
        let folded = sib_foldable_mem_op(&load).expect("MovsdRM must be foldable");
        assert_eq!(folded.3, X86Opcode::MovsdRMSib);
        assert!(folded.0, "load must be flagged as a load");

        let store = X86ISelInst::new(
            X86Opcode::MovsdMR,
            vec![
                X86ISelOperand::MemAddr {
                    base: Box::new(vreg(2)),
                    disp: 0,
                },
                vreg(10),
            ],
        );
        assert!(
            sib_foldable_mem_op(&store).is_none(),
            "MovsdMR must NOT fold — no MovsdMRSib opcode exists to fold into"
        );
    }

    #[test]
    fn sib_base_fold_vreg_base_no_redef_folds() {
        // Lea b(2), [base_vreg(5) + 4]; MovRM32Sib d, [b + idx(1)*8 + 0]
        //   => base becomes vreg(5), disp 4.
        let mut func = make_func(vec![
            lea_base(2, vreg(5), 4),
            movrm32_sib(10, 2, 1, 8, 0),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(run_sib_base_fold(&mut func));
        let (base, _index, scale, disp) = sib_addr(&entry_insts(&func)[1]);
        assert_eq!(*base, vreg(5));
        assert_eq!(scale, 8);
        assert_eq!(disp, 4);
    }

    #[test]
    fn sib_base_fold_declines_vreg_base_redefined_between() {
        // A redefinition of the base vreg(5) between the Lea and the anchor
        // makes the substitution unsound -> decline.
        let mut func = make_func(vec![
            lea_base(2, vreg(5), 4),
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(5), X86ISelOperand::Imm(1)]),
            movrm32_sib(10, 2, 1, 4, 0),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(!run_sib_base_fold(&mut func));
    }

    #[test]
    fn sib_base_fold_multiuse_stackslot_folds_all() {
        // A StackSlot base is frame-invariant, so ALL of b(2)'s SIB uses fold
        // independently (the single Lea then goes dead for DCE).
        let mut func = make_func(vec![
            lea_base(2, X86ISelOperand::StackSlot(3), 0),
            movrm32_sib(10, 2, 1, 4, 0),
            movrm32_sib(11, 2, 1, 4, 4),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(run_sib_base_fold(&mut func));
        let insts = entry_insts(&func);
        for i in [1usize, 2] {
            let (base, _idx, _scale, _disp) = sib_addr(&insts[i]);
            assert_eq!(*base, X86ISelOperand::StackSlot(3));
        }
    }

    #[test]
    fn sib_base_fold_through_copy_of_stackslot_lea() {
        // The ISel materializes the base as a copy: Lea b, [StackSlot]; MovRR c, b;
        // MovRM32Sib d, [c + idx*4 + 8]. The fold resolves c -> b -> StackSlot.
        let mut func = make_func(vec![
            lea_base(2, X86ISelOperand::StackSlot(3), 0),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(4), vreg(2)]),
            movrm32_sib(10, 4, 1, 4, 8),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(run_sib_base_fold(&mut func));
        let (base, _idx, _scale, disp) = sib_addr(&entry_insts(&func)[2]);
        assert_eq!(*base, X86ISelOperand::StackSlot(3));
        assert_eq!(disp, 8);
    }

    #[test]
    fn sib_base_fold_declines_multiuse_vreg_base() {
        // A Gpr64 VReg base with TWO uses -> not single-use -> decline (a
        // register base could be clobbered; only StackSlot bases go multi-use).
        let mut func = make_func(vec![
            lea_base(2, vreg(5), 0),
            movrm32_sib(10, 2, 1, 4, 0),
            movrm32_sib(11, 2, 1, 4, 4),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(!run_sib_base_fold(&mut func));
    }

    #[test]
    fn sib_base_fold_declines_disp_overflow() {
        // d0 + d1 overflows i32 -> the sext-distributivity precondition fails.
        let mut func = make_func(vec![
            lea_base(2, X86ISelOperand::StackSlot(3), i32::MAX),
            movrm32_sib(10, 2, 1, 4, 1),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(!run_sib_base_fold(&mut func));
    }

    #[test]
    fn imm_fold_and_add_sub_cmp_imul() {
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(0), X86ISelOperand::Imm(7)]),
            X86ISelInst::new(X86Opcode::AndRR, vec![vreg(1), vreg(2), vreg(0)]),
            X86ISelInst::new(X86Opcode::AddRR, vec![vreg(3), vreg(2), vreg(0)]),
            X86ISelInst::new(X86Opcode::SubRR, vec![vreg(4), vreg(2), vreg(0)]),
            X86ISelInst::new(X86Opcode::ImulRR, vec![vreg(5), vreg(2), vreg(0)]),
            X86ISelInst::new(X86Opcode::CmpRR, vec![vreg(2), vreg(0)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(fold_unique_const_into_imm_forms(&mut func));
        let insts = entry_insts(&func);
        assert_eq!(insts[1].opcode, X86Opcode::AndRI);
        assert_eq!(insts[1].operands[2], X86ISelOperand::Imm(7));
        assert_eq!(insts[2].opcode, X86Opcode::AddRI);
        assert_eq!(insts[3].opcode, X86Opcode::SubRI);
        assert_eq!(insts[4].opcode, X86Opcode::ImulRRI);
        assert_eq!(insts[5].opcode, X86Opcode::CmpRI);
        assert_eq!(insts[5].operands[1], X86ISelOperand::Imm(7));
    }

    #[test]
    fn imm_fold_commutative_lhs_swaps() {
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(0), X86ISelOperand::Imm(9)]),
            X86ISelInst::new(X86Opcode::AddRR, vec![vreg(1), vreg(0), vreg(2)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(fold_unique_const_into_imm_forms(&mut func));
        let insts = entry_insts(&func);
        assert_eq!(insts[1].opcode, X86Opcode::AddRI);
        assert_eq!(insts[1].operands[1], vreg(2));
        assert_eq!(insts[1].operands[2], X86ISelOperand::Imm(9));
    }

    #[test]
    fn imm_fold_skips_multi_def_and_non_imm32() {
        // v0 defined twice -> no fold; v3's constant does not fit sext-imm32.
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(0), X86ISelOperand::Imm(7)]),
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(0), X86ISelOperand::Imm(8)]),
            X86ISelInst::new(
                X86Opcode::MovRI,
                vec![vreg(3), X86ISelOperand::Imm(0x1_0000_0000)],
            ),
            X86ISelInst::new(X86Opcode::AndRR, vec![vreg(1), vreg(2), vreg(0)]),
            X86ISelInst::new(X86Opcode::AddRR, vec![vreg(4), vreg(2), vreg(3)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(!fold_unique_const_into_imm_forms(&mut func));
        let insts = entry_insts(&func);
        assert_eq!(insts[3].opcode, X86Opcode::AndRR);
        assert_eq!(insts[4].opcode, X86Opcode::AddRR);
    }

    #[test]
    fn imm_fold_sub_rhs_only_never_lhs() {
        // Subtraction is not commutative: a constant LHS must NOT be folded.
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(0), X86ISelOperand::Imm(5)]),
            X86ISelInst::new(X86Opcode::SubRR, vec![vreg(1), vreg(0), vreg(2)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(!fold_unique_const_into_imm_forms(&mut func));
        assert_eq!(entry_insts(&func)[1].opcode, X86Opcode::SubRR);
    }

    #[test]
    fn imm_fold_negative_imm32_folds() {
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(0), X86ISelOperand::Imm(-2)]),
            X86ISelInst::new(X86Opcode::CmpRR, vec![vreg(2), vreg(0)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(fold_unique_const_into_imm_forms(&mut func));
        let insts = entry_insts(&func);
        assert_eq!(insts[1].opcode, X86Opcode::CmpRI);
        assert_eq!(insts[1].operands[1], X86ISelOperand::Imm(-2));
    }

    #[test]
    fn imm_fold_sees_through_single_def_copy_chain() {
        // CSE's canonical-constant shape: MovRI root, then single-def MovRR
        // copies; consumers read the constant through the chain (depth 2
        // here). Both the imul and the cmp must fold.
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(0), X86ISelOperand::Imm(8)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(1), vreg(0)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(2), vreg(1)]),
            X86ISelInst::new(X86Opcode::ImulRR, vec![vreg(3), vreg(4), vreg(2)]),
            X86ISelInst::new(X86Opcode::CmpRR, vec![vreg(5), vreg(1)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(fold_unique_const_into_imm_forms(&mut func));
        let insts = entry_insts(&func);
        assert_eq!(insts[3].opcode, X86Opcode::ImulRRI);
        assert_eq!(insts[3].operands[2], X86ISelOperand::Imm(8));
        assert_eq!(insts[4].opcode, X86Opcode::CmpRI);
        assert_eq!(insts[4].operands[1], X86ISelOperand::Imm(8));
    }

    #[test]
    fn imm_fold_refutes_multi_def_copy_link() {
        // The copy dest v1 is defined twice -> its value is not a single
        // static assignment; consumers must NOT fold through it.
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(0), X86ISelOperand::Imm(8)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(1), vreg(0)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(1), vreg(2)]),
            X86ISelInst::new(X86Opcode::ImulRR, vec![vreg(3), vreg(4), vreg(1)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(!fold_unique_const_into_imm_forms(&mut func));
        assert_eq!(entry_insts(&func)[3].opcode, X86Opcode::ImulRR);
    }

    #[test]
    fn imm_fold_refutes_copy_of_multi_def_root() {
        // The MovRI root v0 is defined twice -> the copy v1 does not hold a
        // provable constant; the consumer must NOT fold.
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(0), X86ISelOperand::Imm(8)]),
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(0), X86ISelOperand::Imm(9)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(1), vreg(0)]),
            X86ISelInst::new(X86Opcode::ImulRR, vec![vreg(3), vreg(4), vreg(1)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(!fold_unique_const_into_imm_forms(&mut func));
        assert_eq!(entry_insts(&func)[3].opcode, X86Opcode::ImulRR);
    }

    #[test]
    fn imm_fold_copy_cycle_terminates_without_folding() {
        // A single-def copy CYCLE (v1 = mov v2; v2 = mov v1) has no MovRI
        // root: the chase must terminate and must not credit a constant.
        // (v0's unrelated constant keeps `consts` non-empty so the chase
        // loop actually runs.)
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(0), X86ISelOperand::Imm(7)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(1), vreg(2)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(2), vreg(1)]),
            X86ISelInst::new(X86Opcode::ImulRR, vec![vreg(3), vreg(4), vreg(1)]),
            X86ISelInst::new(X86Opcode::AndRR, vec![vreg(5), vreg(6), vreg(0)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        // The direct v0 use still folds; the cycle-fed imul must not.
        assert!(fold_unique_const_into_imm_forms(&mut func));
        let insts = entry_insts(&func);
        assert_eq!(insts[3].opcode, X86Opcode::ImulRR);
        assert_eq!(insts[4].opcode, X86Opcode::AndRI);
    }

    #[test]
    fn imm_fold_refutes_non_gpr64_copy_link() {
        // Only plain Gpr64 MovRR links are chased: a Gpr32 MovRR32 copy of a
        // (Gpr32) constant is not a chase link, so the 32-bit consumer keeps
        // its register operand (direct MovRI uses keep folding either way —
        // this pins that the CHAIN is opcode/class-guarded).
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg32(0), X86ISelOperand::Imm(8)]),
            X86ISelInst::new(X86Opcode::MovRR32, vec![vreg32(1), vreg32(0)]),
            X86ISelInst::new(X86Opcode::ImulRR, vec![vreg32(3), vreg32(4), vreg32(1)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(!fold_unique_const_into_imm_forms(&mut func));
        assert_eq!(entry_insts(&func)[2].opcode, X86Opcode::ImulRR);
    }

    #[test]
    fn x86_peephole_removes_self_movrr_through_pass_manager() {
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(0), vreg(0)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut pm = X86PassManager::new().with_pass(Box::new(X86Peephole::default()));

        assert!(pm.run_once(&mut func));

        assert_eq!(entry_opcodes(&func), vec![X86Opcode::Ret]);
    }

    #[test]
    fn x86_peephole_removes_self_movrr32() {
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::MovRR32, vec![vreg32(0), vreg32(0)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut peephole = X86Peephole::default();

        assert!(peephole.run_on_function(&mut func));

        assert_eq!(entry_opcodes(&func), vec![X86Opcode::Ret]);
    }

    #[test]
    fn x86_peephole_removes_self_xmm_copies() {
        for (opcode, class) in [
            (X86Opcode::MovssRR, RegClass::Fpr32),
            (X86Opcode::MovsdRR, RegClass::Fpr64),
            (X86Opcode::MovdqaRR, RegClass::Fpr128),
        ] {
            let reg = |id| vreg_class(id, class);
            let mut func = make_func(vec![
                X86ISelInst::new(opcode, vec![reg(0), reg(0)]),
                X86ISelInst::new(X86Opcode::Ret, vec![]),
            ]);
            let mut peephole = X86Peephole::default();

            assert!(
                peephole.run_on_function(&mut func),
                "{opcode:?} self-copy should be removed"
            );

            assert_eq!(entry_opcodes(&func), vec![X86Opcode::Ret]);
        }
    }

    #[test]
    fn x86_peephole_rewrites_zero_disp_lea_to_movrr() {
        let mut func = make_func(vec![
            X86ISelInst::new(
                X86Opcode::Lea,
                vec![
                    vreg(2),
                    X86ISelOperand::MemAddr {
                        base: Box::new(vreg(1)),
                        disp: 0,
                    },
                ],
            ),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut peephole = X86Peephole::default();

        assert!(peephole.run_on_function(&mut func));

        let insts = entry_insts(&func);
        assert_eq!(entry_opcodes(&func), vec![X86Opcode::MovRR, X86Opcode::Ret]);
        assert_eq!(insts[0].operands, vec![vreg(2), vreg(1)]);
    }

    #[test]
    fn x86_peephole_preserves_proof_origin_on_replace() {
        let mut func = make_func(vec![
            X86ISelInst::new(
                X86Opcode::Lea,
                vec![
                    vreg(2),
                    X86ISelOperand::MemAddr {
                        base: Box::new(vreg(1)),
                        disp: 0,
                    },
                ],
            )
            .with_proof_origin(X86ProofOrigin::AtomicLoad),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut peephole = X86Peephole::default();

        assert!(peephole.run_on_function(&mut func));

        let insts = entry_insts(&func);
        assert_eq!(insts[0].opcode, X86Opcode::MovRR);
        assert_eq!(insts[0].operands, vec![vreg(2), vreg(1)]);
        assert_eq!(insts[0].proof_origin, Some(X86ProofOrigin::AtomicLoad));
    }

    #[test]
    fn x86_peephole_rewrites_cmp_zero_to_test_rr_even_when_flags_are_read() {
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(1), X86ISelOperand::Imm(0)])
                .with_proof_origin(X86ProofOrigin::AtomicLoad),
            X86ISelInst::new(
                X86Opcode::Setcc,
                vec![vreg(2), X86ISelOperand::CondCode(X86CondCode::E)],
            ),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut peephole = X86Peephole::default();

        assert!(peephole.run_on_function(&mut func));

        let insts = entry_insts(&func);
        assert_eq!(
            entry_opcodes(&func),
            vec![X86Opcode::TestRR, X86Opcode::Setcc, X86Opcode::Ret]
        );
        assert_eq!(insts[0].operands, vec![vreg(1), vreg(1)]);
        assert_eq!(insts[0].proof_origin, Some(X86ProofOrigin::AtomicLoad));
    }

    #[test]
    fn x86_peephole_rewrites_cmp_ri8_zero_to_test_rr() {
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::CmpRI8, vec![vreg32(1), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(
                X86Opcode::Setcc,
                vec![vreg32(2), X86ISelOperand::CondCode(X86CondCode::NE)],
            ),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut peephole = X86Peephole::default();

        assert!(peephole.run_on_function(&mut func));

        let insts = entry_insts(&func);
        assert_eq!(
            entry_opcodes(&func),
            vec![X86Opcode::TestRR, X86Opcode::Setcc, X86Opcode::Ret]
        );
        assert_eq!(insts[0].operands, vec![vreg32(1), vreg32(1)]);
    }

    #[test]
    fn x86_peephole_rewrites_testri_all_ones_to_test_rr_even_when_flags_are_read() {
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::TestRI, vec![vreg(1), X86ISelOperand::Imm(-1)])
                .with_proof_origin(X86ProofOrigin::AtomicLoad),
            X86ISelInst::new(
                X86Opcode::Setcc,
                vec![vreg32(2), X86ISelOperand::CondCode(X86CondCode::E)],
            ),
            X86ISelInst::new(X86Opcode::TestRI, vec![vreg32(3), X86ISelOperand::Imm(-1)]),
            X86ISelInst::new(
                X86Opcode::Setcc,
                vec![vreg32(4), X86ISelOperand::CondCode(X86CondCode::NE)],
            ),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut peephole = X86Peephole::default();

        assert!(peephole.run_on_function(&mut func));

        let insts = entry_insts(&func);
        assert_eq!(
            entry_opcodes(&func),
            vec![
                X86Opcode::TestRR,
                X86Opcode::Setcc,
                X86Opcode::TestRR,
                X86Opcode::Setcc,
                X86Opcode::Ret,
            ]
        );
        assert_eq!(insts[0].operands, vec![vreg(1), vreg(1)]);
        assert_eq!(insts[0].proof_origin, Some(X86ProofOrigin::AtomicLoad));
        assert_eq!(insts[2].operands, vec![vreg32(3), vreg32(3)]);
    }

    #[test]
    fn x86_peephole_preserves_unsupported_testri_all_ones_forms() {
        let mem = X86ISelOperand::MemAddr {
            base: Box::new(vreg(0)),
            disp: 0,
        };
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::TestRI, vec![vreg(1), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(X86Opcode::TestRI, vec![vreg(2), X86ISelOperand::Imm(-2)]),
            X86ISelInst::new(
                X86Opcode::TestRI,
                vec![vreg_class(3, RegClass::Fpr64), X86ISelOperand::Imm(-1)],
            ),
            X86ISelInst::new(
                X86Opcode::TestRI,
                vec![X86ISelOperand::PReg(RAX), X86ISelOperand::Imm(-1)],
            ),
            X86ISelInst::new(X86Opcode::TestRI, vec![mem, X86ISelOperand::Imm(-1)]),
            X86ISelInst::with_flags(
                X86Opcode::TestRI,
                vec![vreg(4), X86ISelOperand::Imm(-1)],
                X86Opcode::TestRI
                    .default_flags()
                    .union(InstFlags::READS_MEMORY),
            ),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut peephole = X86Peephole::default();

        assert!(!peephole.run_on_function(&mut func));

        assert_eq!(
            entry_opcodes(&func),
            vec![
                X86Opcode::TestRI,
                X86Opcode::TestRI,
                X86Opcode::TestRI,
                X86Opcode::TestRI,
                X86Opcode::TestRI,
                X86Opcode::TestRI,
                X86Opcode::Ret,
            ]
        );
    }

    #[test]
    fn x86_peephole_preserves_unsupported_cmp_zero_forms() {
        let mem = X86ISelOperand::MemAddr {
            base: Box::new(vreg(0)),
            disp: 0,
        };
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(1), X86ISelOperand::Imm(1)]),
            X86ISelInst::new(X86Opcode::CmpRI8, vec![vreg(2), X86ISelOperand::Imm(-1)]),
            X86ISelInst::new(
                X86Opcode::CmpRI,
                vec![X86ISelOperand::PReg(RAX), X86ISelOperand::Imm(0)],
            ),
            X86ISelInst::new(X86Opcode::CmpRI, vec![mem, X86ISelOperand::Imm(0)]),
            X86ISelInst::with_flags(
                X86Opcode::CmpRI,
                vec![vreg(3), X86ISelOperand::Imm(0)],
                InstFlags::HAS_SIDE_EFFECTS.union(InstFlags::READS_MEMORY),
            ),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut peephole = X86Peephole::default();

        assert!(!peephole.run_on_function(&mut func));

        assert_eq!(
            entry_opcodes(&func),
            vec![
                X86Opcode::CmpRI,
                X86Opcode::CmpRI8,
                X86Opcode::CmpRI,
                X86Opcode::CmpRI,
                X86Opcode::CmpRI,
                X86Opcode::Ret,
            ]
        );
        assert_eq!(
            entry_insts(&func)[4].flags,
            InstFlags::HAS_SIDE_EFFECTS.union(InstFlags::READS_MEMORY)
        );
    }

    #[test]
    fn x86_peephole_removes_zero_disp_self_lea() {
        let mut func = make_func(vec![
            X86ISelInst::new(
                X86Opcode::Lea,
                vec![
                    vreg(2),
                    X86ISelOperand::MemAddr {
                        base: Box::new(vreg(2)),
                        disp: 0,
                    },
                ],
            ),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut peephole = X86Peephole::default();

        assert!(peephole.run_on_function(&mut func));

        assert_eq!(entry_opcodes(&func), vec![X86Opcode::Ret]);
    }

    #[test]
    fn x86_peephole_preserves_non_identity_lea_forms() {
        let mut func = make_func(vec![
            X86ISelInst::new(
                X86Opcode::Lea,
                vec![
                    vreg(2),
                    X86ISelOperand::MemAddr {
                        base: Box::new(vreg(1)),
                        disp: 8,
                    },
                ],
            ),
            X86ISelInst::new(
                X86Opcode::Lea,
                vec![
                    vreg(3),
                    X86ISelOperand::MemAddr {
                        base: Box::new(X86ISelOperand::PReg(RAX)),
                        disp: 0,
                    },
                ],
            ),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut peephole = X86Peephole::default();

        assert!(!peephole.run_on_function(&mut func));

        assert_eq!(
            entry_opcodes(&func),
            vec![X86Opcode::Lea, X86Opcode::Lea, X86Opcode::Ret]
        );
    }

    #[test]
    fn x86_peephole_rewrites_three_operand_double_add_to_lea_when_flags_die() {
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::AddRR, vec![vreg(4), vreg(1), vreg(1)]),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(4), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut peephole = X86Peephole::default();

        assert!(peephole.run_on_function(&mut func));

        let insts = entry_insts(&func);
        assert_eq!(
            entry_opcodes(&func),
            vec![X86Opcode::LeaSib, X86Opcode::TestRR, X86Opcode::Ret]
        );
        assert_eq!(insts[0].operands[0], vreg(4));
        assert_eq!(
            insts[0].operands[1],
            X86ISelOperand::SibMemAddr {
                base: Box::new(vreg(1)),
                index: Box::new(vreg(1)),
                scale: 1,
                disp: 0,
            }
        );
    }

    #[test]
    fn x86_peephole_rewrites_two_operand_self_add_to_lea_when_flags_die() {
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::AddRR, vec![vreg(2), vreg(2)]),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(2), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut peephole = X86Peephole::default();

        assert!(peephole.run_on_function(&mut func));

        let insts = entry_insts(&func);
        assert_eq!(
            entry_opcodes(&func),
            vec![X86Opcode::LeaSib, X86Opcode::TestRR, X86Opcode::Ret]
        );
        assert_eq!(insts[0].operands[0], vreg(2));
        assert_eq!(
            insts[0].operands[1],
            X86ISelOperand::SibMemAddr {
                base: Box::new(vreg(2)),
                index: Box::new(vreg(2)),
                scale: 1,
                disp: 0,
            }
        );
    }

    #[test]
    fn x86_peephole_preserves_double_add_when_flags_are_read() {
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::AddRR, vec![vreg(4), vreg(1), vreg(1)]),
            X86ISelInst::new(
                X86Opcode::Setcc,
                vec![vreg(5), X86ISelOperand::CondCode(X86CondCode::E)],
            ),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut peephole = X86Peephole::default();

        assert!(!peephole.run_on_function(&mut func));

        assert_eq!(
            entry_opcodes(&func),
            vec![X86Opcode::AddRR, X86Opcode::Setcc, X86Opcode::Ret]
        );
    }

    #[test]
    fn x86_peephole_preserves_unsupported_double_add_forms() {
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::AddRR, vec![vreg32(4), vreg32(1), vreg32(1)]),
            X86ISelInst::new(X86Opcode::AddRR, vec![vreg(5), vreg(2), vreg(3)]),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(5), X86ISelOperand::Imm(1)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut peephole = X86Peephole::default();

        assert!(!peephole.run_on_function(&mut func));

        assert_eq!(
            entry_opcodes(&func),
            vec![
                X86Opcode::AddRR,
                X86Opcode::AddRR,
                X86Opcode::CmpRI,
                X86Opcode::Ret,
            ]
        );
    }

    #[test]
    fn x86_peephole_rewrites_zero_immediate_identities_when_flags_die() {
        let mut func = make_func(vec![
            X86ISelInst::new(
                X86Opcode::AddRI,
                vec![vreg(2), vreg(0), X86ISelOperand::Imm(0)],
            ),
            X86ISelInst::new(
                X86Opcode::SubRI,
                vec![vreg(3), vreg(1), X86ISelOperand::Imm(0)],
            ),
            X86ISelInst::new(
                X86Opcode::OrRI,
                vec![vreg(4), vreg(1), X86ISelOperand::Imm(0)],
            ),
            X86ISelInst::new(
                X86Opcode::XorRI,
                vec![vreg(5), vreg(1), X86ISelOperand::Imm(0)],
            ),
            X86ISelInst::new(
                X86Opcode::ShlRI,
                vec![vreg(6), vreg(1), X86ISelOperand::Imm(0)],
            ),
            X86ISelInst::new(
                X86Opcode::ShrRI,
                vec![vreg(7), vreg(1), X86ISelOperand::Imm(0)],
            ),
            X86ISelInst::new(
                X86Opcode::SarRI,
                vec![vreg(8), vreg(1), X86ISelOperand::Imm(0)],
            ),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(8), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut peephole = X86Peephole::default();

        assert!(peephole.run_on_function(&mut func));

        assert_eq!(
            entry_opcodes(&func),
            vec![
                X86Opcode::MovRR,
                X86Opcode::MovRR,
                X86Opcode::MovRR,
                X86Opcode::MovRR,
                X86Opcode::MovRR,
                X86Opcode::MovRR,
                X86Opcode::MovRR,
                X86Opcode::TestRR,
                X86Opcode::Ret,
            ]
        );
        assert_eq!(entry_insts(&func)[0].operands, vec![vreg(2), vreg(0)]);
        assert_eq!(entry_insts(&func)[6].operands, vec![vreg(8), vreg(1)]);
    }

    #[test]
    fn x86_peephole_materializes_gpr32_identity_as_movrr32() {
        let mut func = make_func(vec![
            X86ISelInst::new(
                X86Opcode::OrRI,
                vec![vreg32(2), vreg32(1), X86ISelOperand::Imm(0)],
            ),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg32(2), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut peephole = X86Peephole::default();

        assert!(peephole.run_on_function(&mut func));

        let insts = entry_insts(&func);
        assert_eq!(insts[0].opcode, X86Opcode::MovRR32);
        assert_eq!(insts[0].operands, vec![vreg32(2), vreg32(1)]);
    }

    #[test]
    fn x86_peephole_rewrites_movri_zero_to_xor_zero_when_introduced_flags_die() {
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(2), X86ISelOperand::Imm(0)])
                .with_proof_origin(X86ProofOrigin::AtomicLoad),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(2), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg32(4), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg32(4), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut peephole = X86Peephole::default();

        assert!(peephole.run_on_function(&mut func));

        let insts = entry_insts(&func);
        assert_eq!(
            entry_opcodes(&func),
            vec![
                X86Opcode::XorRR,
                X86Opcode::TestRR,
                X86Opcode::XorRR,
                X86Opcode::TestRR,
                X86Opcode::Ret,
            ]
        );
        assert_eq!(insts[0].operands, vec![vreg(2), vreg(2)]);
        assert_eq!(insts[0].proof_origin, Some(X86ProofOrigin::AtomicLoad));
        assert_eq!(insts[2].operands, vec![vreg32(4), vreg32(4)]);
    }

    #[test]
    fn x86_peephole_preserves_movri_zero_when_introduced_flags_are_read_or_live_out() {
        let mut read_func = make_func(vec![
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(1), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(
                X86Opcode::Setcc,
                vec![vreg32(2), X86ISelOperand::CondCode(X86CondCode::E)],
            ),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut branch_func = make_func(vec![
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(1), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(
                X86Opcode::Jcc,
                vec![
                    X86ISelOperand::CondCode(X86CondCode::E),
                    X86ISelOperand::Block(Block(1)),
                ],
            ),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut live_out_func = make_func(vec![
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(1), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut partial_func = make_func(vec![
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(1), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(X86Opcode::Inc, vec![vreg(2)]),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(1), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut peephole = X86Peephole::default();

        assert!(!peephole.run_on_function(&mut read_func));
        assert!(!peephole.run_on_function(&mut branch_func));
        assert!(!peephole.run_on_function(&mut live_out_func));
        assert!(peephole.run_on_function(&mut partial_func));

        assert_eq!(
            entry_opcodes(&read_func),
            vec![X86Opcode::MovRI, X86Opcode::Setcc, X86Opcode::Ret]
        );
        assert_eq!(
            entry_opcodes(&branch_func),
            vec![X86Opcode::MovRI, X86Opcode::Jcc, X86Opcode::Ret]
        );
        assert_eq!(
            entry_opcodes(&live_out_func),
            vec![X86Opcode::MovRI, X86Opcode::Ret]
        );
        // The partial writer (Inc) reads no flags, so the deadness scan
        // continues through it to the CmpRI full overwrite: the zero-idiom
        // rewrite fires. (This pinned fail-closed-at-partial before the
        // scan was widened; a reader between would still decline — see
        // constmul_declines_when_reader_follows_partial_writer.)
        assert_eq!(
            entry_opcodes(&partial_func),
            vec![
                X86Opcode::XorRR,
                X86Opcode::Inc,
                X86Opcode::TestRR,
                X86Opcode::Ret,
            ]
        );
        assert_eq!(
            entry_insts(&partial_func)[0].operands,
            vec![vreg(1), vreg(1)]
        );
    }

    #[test]
    fn x86_peephole_preserves_unsupported_movri_zero_forms() {
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(2), X86ISelOperand::Imm(1)]),
            X86ISelInst::new(
                X86Opcode::MovRI,
                vec![vreg_class(3, RegClass::Fpr64), X86ISelOperand::Imm(0)],
            ),
            X86ISelInst::new(
                X86Opcode::MovRI,
                vec![X86ISelOperand::PReg(RAX), X86ISelOperand::Imm(0)],
            ),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut peephole = X86Peephole::default();

        assert!(!peephole.run_on_function(&mut func));

        assert_eq!(
            entry_opcodes(&func),
            vec![
                X86Opcode::MovRI,
                X86Opcode::MovRI,
                X86Opcode::MovRI,
                X86Opcode::Ret,
            ]
        );
    }

    #[test]
    fn x86_peephole_rewrites_self_add_sub_one_to_inc_dec_when_flags_die() {
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::AddRI, vec![vreg(1), X86ISelOperand::Imm(1)])
                .with_proof_origin(X86ProofOrigin::AtomicLoad),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(1), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(
                X86Opcode::SubRI,
                vec![vreg(2), vreg(2), X86ISelOperand::Imm(1)],
            )
            .with_proof_origin(X86ProofOrigin::AtomicLoad),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(2), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(X86Opcode::AddRI, vec![vreg32(3), X86ISelOperand::Imm(1)]),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg32(3), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(
                X86Opcode::SubRI,
                vec![vreg32(4), vreg32(4), X86ISelOperand::Imm(1)],
            ),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg32(4), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut peephole = X86Peephole::default();

        assert!(peephole.run_on_function(&mut func));

        let insts = entry_insts(&func);
        assert_eq!(
            entry_opcodes(&func),
            vec![
                X86Opcode::Inc,
                X86Opcode::TestRR,
                X86Opcode::Dec,
                X86Opcode::TestRR,
                X86Opcode::Inc,
                X86Opcode::TestRR,
                X86Opcode::Dec,
                X86Opcode::TestRR,
                X86Opcode::Ret,
            ]
        );
        assert_eq!(insts[0].operands, vec![vreg(1)]);
        assert_eq!(insts[0].proof_origin, Some(X86ProofOrigin::AtomicLoad));
        assert_eq!(insts[2].operands, vec![vreg(2)]);
        assert_eq!(insts[2].proof_origin, Some(X86ProofOrigin::AtomicLoad));
        assert_eq!(insts[4].operands, vec![vreg32(3)]);
        assert_eq!(insts[6].operands, vec![vreg32(4)]);
    }

    #[test]
    fn x86_peephole_preserves_add_sub_one_when_flags_are_read_or_live_out() {
        let mut add_read_func = make_func(vec![
            X86ISelInst::new(X86Opcode::AddRI, vec![vreg(1), X86ISelOperand::Imm(1)]),
            X86ISelInst::new(
                X86Opcode::Setcc,
                vec![vreg32(2), X86ISelOperand::CondCode(X86CondCode::B)],
            ),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut sub_read_func = make_func(vec![
            X86ISelInst::new(X86Opcode::SubRI, vec![vreg(1), X86ISelOperand::Imm(1)]),
            X86ISelInst::new(
                X86Opcode::Setcc,
                vec![vreg32(2), X86ISelOperand::CondCode(X86CondCode::B)],
            ),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut add_live_out_func = make_func(vec![
            X86ISelInst::new(X86Opcode::AddRI, vec![vreg(1), X86ISelOperand::Imm(1)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut sub_live_out_func = make_func(vec![
            X86ISelInst::new(X86Opcode::SubRI, vec![vreg(1), X86ISelOperand::Imm(1)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut peephole = X86Peephole::default();

        assert!(!peephole.run_on_function(&mut add_read_func));
        assert!(!peephole.run_on_function(&mut sub_read_func));
        assert!(!peephole.run_on_function(&mut add_live_out_func));
        assert!(!peephole.run_on_function(&mut sub_live_out_func));

        assert_eq!(
            entry_opcodes(&add_read_func),
            vec![X86Opcode::AddRI, X86Opcode::Setcc, X86Opcode::Ret]
        );
        assert_eq!(
            entry_opcodes(&sub_read_func),
            vec![X86Opcode::SubRI, X86Opcode::Setcc, X86Opcode::Ret]
        );
        assert_eq!(
            entry_opcodes(&add_live_out_func),
            vec![X86Opcode::AddRI, X86Opcode::Ret]
        );
        assert_eq!(
            entry_opcodes(&sub_live_out_func),
            vec![X86Opcode::SubRI, X86Opcode::Ret]
        );
    }

    #[test]
    fn x86_peephole_preserves_unsupported_and_nonself_add_sub_one_forms() {
        let mut func = make_func(vec![
            X86ISelInst::new(
                X86Opcode::AddRI,
                vec![vreg(2), vreg(1), X86ISelOperand::Imm(1)],
            ),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(2), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(
                X86Opcode::SubRI,
                vec![vreg(4), vreg(3), X86ISelOperand::Imm(1)],
            ),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(4), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(X86Opcode::AddRI, vec![vreg(5), X86ISelOperand::Imm(2)]),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(5), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(X86Opcode::SubRI, vec![vreg(6), X86ISelOperand::Imm(2)]),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(6), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(
                X86Opcode::AddRI,
                vec![X86ISelOperand::PReg(RAX), X86ISelOperand::Imm(1)],
            ),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(7), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(
                X86Opcode::AddRI,
                vec![vreg_class(8, RegClass::Fpr64), X86ISelOperand::Imm(1)],
            ),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(8), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(
                X86Opcode::AddRI,
                vec![vreg(10), vreg32(9), X86ISelOperand::Imm(1)],
            ),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(10), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut peephole = X86Peephole::default();

        assert!(peephole.run_on_function(&mut func));

        let insts = entry_insts(&func);
        assert_eq!(
            entry_opcodes(&func),
            vec![
                X86Opcode::AddRI,
                X86Opcode::TestRR,
                X86Opcode::SubRI,
                X86Opcode::TestRR,
                X86Opcode::AddRI,
                X86Opcode::TestRR,
                X86Opcode::SubRI,
                X86Opcode::TestRR,
                X86Opcode::AddRI,
                X86Opcode::TestRR,
                X86Opcode::AddRI,
                X86Opcode::TestRR,
                X86Opcode::AddRI,
                X86Opcode::TestRR,
                X86Opcode::Ret,
            ]
        );
        assert_eq!(
            insts[0].operands,
            vec![vreg(2), vreg(1), X86ISelOperand::Imm(1)]
        );
        assert_eq!(
            insts[2].operands,
            vec![vreg(4), vreg(3), X86ISelOperand::Imm(1)]
        );
        assert_eq!(insts[4].operands, vec![vreg(5), X86ISelOperand::Imm(2)]);
        assert_eq!(
            insts[8].operands,
            vec![X86ISelOperand::PReg(RAX), X86ISelOperand::Imm(1)]
        );
        assert_eq!(
            insts[10].operands,
            vec![vreg_class(8, RegClass::Fpr64), X86ISelOperand::Imm(1)]
        );
        assert_eq!(
            insts[12].operands,
            vec![vreg(10), vreg32(9), X86ISelOperand::Imm(1)]
        );
    }

    #[test]
    fn x86_peephole_rewrites_and_and_equal_rr_identities() {
        let mut func = make_func(vec![
            X86ISelInst::new(
                X86Opcode::AndRI,
                vec![vreg(1), vreg(0), X86ISelOperand::Imm(-1)],
            ),
            X86ISelInst::new(
                X86Opcode::AndRI,
                vec![vreg(2), vreg(0), X86ISelOperand::Imm(0)],
            )
            .with_proof_origin(X86ProofOrigin::AtomicLoad),
            X86ISelInst::new(X86Opcode::SubRR, vec![vreg(3), vreg(0), vreg(0)]),
            X86ISelInst::new(X86Opcode::XorRR, vec![vreg(4), vreg(0), vreg(0)]),
            X86ISelInst::new(X86Opcode::OrRR, vec![vreg(5), vreg(0), vreg(0)]),
            X86ISelInst::new(X86Opcode::AndRR, vec![vreg(6), vreg(0), vreg(0)]),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(6), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut peephole = X86Peephole::default();

        assert!(peephole.run_on_function(&mut func));

        let insts = entry_insts(&func);
        assert_eq!(
            entry_opcodes(&func),
            vec![
                X86Opcode::MovRR,
                X86Opcode::XorRR,
                X86Opcode::XorRR,
                X86Opcode::XorRR,
                X86Opcode::MovRR,
                X86Opcode::MovRR,
                X86Opcode::TestRR,
                X86Opcode::Ret,
            ]
        );
        assert_eq!(insts[0].operands, vec![vreg(1), vreg(0)]);
        assert_eq!(insts[1].operands, vec![vreg(2), vreg(2)]);
        assert_eq!(insts[1].proof_origin, Some(X86ProofOrigin::AtomicLoad));
        assert_eq!(insts[2].operands, vec![vreg(3), vreg(3)]);
        assert_eq!(insts[3].operands, vec![vreg(4), vreg(4)]);
        assert_eq!(insts[5].operands, vec![vreg(6), vreg(0)]);
    }

    #[test]
    fn x86_peephole_leaves_canonical_two_operand_xor_zero_unchanged() {
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::XorRR, vec![vreg(1), vreg(1)])
                .with_proof_origin(X86ProofOrigin::AtomicLoad),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(1), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut peephole = X86Peephole::default();

        assert!(peephole.run_on_function(&mut func));

        let insts = entry_insts(&func);
        assert_eq!(
            entry_opcodes(&func),
            vec![X86Opcode::XorRR, X86Opcode::TestRR, X86Opcode::Ret]
        );
        assert_eq!(insts[0].operands, vec![vreg(1), vreg(1)]);
        assert_eq!(insts[0].proof_origin, Some(X86ProofOrigin::AtomicLoad));
    }

    #[test]
    fn x86_peephole_preserves_self_zero_rr_when_flags_are_read() {
        let mut sub_func = make_func(vec![
            X86ISelInst::new(X86Opcode::SubRR, vec![vreg(3), vreg(0), vreg(0)]),
            X86ISelInst::new(
                X86Opcode::Setcc,
                vec![vreg(5), X86ISelOperand::CondCode(X86CondCode::E)],
            ),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut xor_func = make_func(vec![
            X86ISelInst::new(X86Opcode::XorRR, vec![vreg(4), vreg(1), vreg(1)]),
            X86ISelInst::new(
                X86Opcode::Setcc,
                vec![vreg(5), X86ISelOperand::CondCode(X86CondCode::E)],
            ),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut peephole = X86Peephole::default();

        assert!(!peephole.run_on_function(&mut sub_func));
        assert!(!peephole.run_on_function(&mut xor_func));

        assert_eq!(
            entry_opcodes(&sub_func),
            vec![X86Opcode::SubRR, X86Opcode::Setcc, X86Opcode::Ret]
        );
        assert_eq!(
            entry_opcodes(&xor_func),
            vec![X86Opcode::XorRR, X86Opcode::Setcc, X86Opcode::Ret]
        );
        assert_eq!(
            entry_insts(&sub_func)[0].operands,
            vec![vreg(3), vreg(0), vreg(0)]
        );
        assert_eq!(
            entry_insts(&xor_func)[0].operands,
            vec![vreg(4), vreg(1), vreg(1)]
        );
    }

    #[test]
    fn x86_peephole_rewrites_and_zero_two_operand_and_gpr32_to_xor_zero() {
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::AndRI, vec![vreg(1), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(X86Opcode::AndRI, vec![vreg32(2), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg32(2), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut peephole = X86Peephole::default();

        assert!(peephole.run_on_function(&mut func));

        let insts = entry_insts(&func);
        assert_eq!(
            entry_opcodes(&func),
            vec![
                X86Opcode::XorRR,
                X86Opcode::XorRR,
                X86Opcode::TestRR,
                X86Opcode::Ret,
            ]
        );
        assert_eq!(insts[0].operands, vec![vreg(1), vreg(1)]);
        assert_eq!(insts[1].operands, vec![vreg32(2), vreg32(2)]);
    }

    #[test]
    fn x86_peephole_preserves_and_zero_when_flags_are_read() {
        let mut func = make_func(vec![
            X86ISelInst::new(
                X86Opcode::AndRI,
                vec![vreg(1), vreg(0), X86ISelOperand::Imm(0)],
            ),
            X86ISelInst::new(
                X86Opcode::Setcc,
                vec![vreg(2), X86ISelOperand::CondCode(X86CondCode::E)],
            ),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut peephole = X86Peephole::default();

        assert!(!peephole.run_on_function(&mut func));

        assert_eq!(
            entry_opcodes(&func),
            vec![X86Opcode::AndRI, X86Opcode::Setcc, X86Opcode::Ret]
        );
    }

    #[test]
    fn x86_peephole_preserves_unsupported_and_zero_forms() {
        let mut func = make_func(vec![
            X86ISelInst::new(
                X86Opcode::AndRI,
                vec![vreg(1), X86ISelOperand::PReg(RAX), X86ISelOperand::Imm(0)],
            ),
            X86ISelInst::new(
                X86Opcode::AndRI,
                vec![vreg(2), vreg32(1), X86ISelOperand::Imm(0)],
            ),
            X86ISelInst::new(
                X86Opcode::AndRI,
                vec![vreg_class(3, RegClass::Fpr32), X86ISelOperand::Imm(0)],
            ),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(0), X86ISelOperand::Imm(1)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut peephole = X86Peephole::default();

        assert!(!peephole.run_on_function(&mut func));

        assert_eq!(
            entry_opcodes(&func),
            vec![
                X86Opcode::AndRI,
                X86Opcode::AndRI,
                X86Opcode::AndRI,
                X86Opcode::CmpRI,
                X86Opcode::Ret,
            ]
        );
    }

    #[test]
    fn x86_peephole_rewrites_xor_allones_self_to_not_when_flags_die() {
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::XorRI, vec![vreg(1), X86ISelOperand::Imm(-1)])
                .with_proof_origin(X86ProofOrigin::AtomicLoad),
            X86ISelInst::new(
                X86Opcode::XorRI,
                vec![vreg(2), vreg(2), X86ISelOperand::Imm(-1)],
            ),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(2), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut peephole = X86Peephole::default();

        assert!(peephole.run_on_function(&mut func));

        let insts = entry_insts(&func);
        assert_eq!(
            entry_opcodes(&func),
            vec![
                X86Opcode::Not,
                X86Opcode::Not,
                X86Opcode::TestRR,
                X86Opcode::Ret,
            ]
        );
        assert_eq!(insts[0].operands, vec![vreg(1)]);
        assert_eq!(insts[0].proof_origin, Some(X86ProofOrigin::AtomicLoad));
        assert_eq!(insts[1].operands, vec![vreg(2)]);
    }

    #[test]
    fn x86_peephole_rewrites_xor_allones_gpr32_self_to_not() {
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::XorRI, vec![vreg32(1), X86ISelOperand::Imm(-1)]),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg32(1), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut peephole = X86Peephole::default();

        assert!(peephole.run_on_function(&mut func));

        let insts = entry_insts(&func);
        assert_eq!(
            entry_opcodes(&func),
            vec![X86Opcode::Not, X86Opcode::TestRR, X86Opcode::Ret]
        );
        assert_eq!(insts[0].operands, vec![vreg32(1)]);
    }

    #[test]
    fn x86_peephole_preserves_unsupported_xor_allones_forms() {
        let mut func = make_func(vec![
            X86ISelInst::new(
                X86Opcode::XorRI,
                vec![vreg(1), vreg(0), X86ISelOperand::Imm(-1)],
            ),
            X86ISelInst::new(X86Opcode::XorRI, vec![vreg(2), X86ISelOperand::Imm(1)]),
            X86ISelInst::new(
                X86Opcode::XorRI,
                vec![X86ISelOperand::PReg(RAX), X86ISelOperand::Imm(-1)],
            ),
            X86ISelInst::new(X86Opcode::XorRI, vec![vreg(3), X86ISelOperand::Imm(-1)]),
            X86ISelInst::new(
                X86Opcode::Setcc,
                vec![vreg(4), X86ISelOperand::CondCode(X86CondCode::E)],
            ),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut peephole = X86Peephole::default();

        assert!(!peephole.run_on_function(&mut func));

        assert_eq!(
            entry_opcodes(&func),
            vec![
                X86Opcode::XorRI,
                X86Opcode::XorRI,
                X86Opcode::XorRI,
                X86Opcode::XorRI,
                X86Opcode::Setcc,
                X86Opcode::Ret,
            ]
        );
    }

    #[test]
    fn x86_peephole_rewrites_imul_rri_one_to_copy_when_flags_die() {
        let mut func = make_func(vec![
            X86ISelInst::new(
                X86Opcode::ImulRRI,
                vec![vreg(2), vreg(1), X86ISelOperand::Imm(1)],
            )
            .with_proof_origin(X86ProofOrigin::AtomicLoad),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(2), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(
                X86Opcode::ImulRRI,
                vec![vreg32(4), vreg32(3), X86ISelOperand::Imm(1)],
            ),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg32(4), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut peephole = X86Peephole::default();

        assert!(peephole.run_on_function(&mut func));

        let insts = entry_insts(&func);
        assert_eq!(
            entry_opcodes(&func),
            vec![
                X86Opcode::MovRR,
                X86Opcode::TestRR,
                X86Opcode::MovRR32,
                X86Opcode::TestRR,
                X86Opcode::Ret,
            ]
        );
        assert_eq!(insts[0].operands, vec![vreg(2), vreg(1)]);
        assert_eq!(insts[0].proof_origin, Some(X86ProofOrigin::AtomicLoad));
        assert_eq!(insts[2].operands, vec![vreg32(4), vreg32(3)]);
    }

    #[test]
    fn x86_peephole_rewrites_imul_rri_two_to_a_doubling_lea_when_flags_die() {
        // Each IMUL is followed by a full flag overwrite (`add`), so its
        // flags are dead. A certificate-free compile.
        let rewritten = |imul: X86ISelInst| {
            let mut func = make_func(vec![
                imul,
                X86ISelInst::new(X86Opcode::AddRR, vec![vreg(8), vreg(7), vreg(6)]),
                X86ISelInst::new(X86Opcode::Ret, vec![]),
            ]);
            X86Peephole::default()
                .with_certificate_free_imul_reductions(true)
                .run_on_function(&mut func);
            entry_insts(&func)[0].clone()
        };
        let doubled = rewritten(X86ISelInst::new(
            X86Opcode::ImulRRI,
            vec![vreg(2), vreg(1), X86ISelOperand::Imm(2)],
        ));
        assert_eq!(doubled.opcode, X86Opcode::LeaSib);
        assert_eq!(
            doubled.operands,
            lea_sib_double(VReg::new(2, RegClass::Gpr64), VReg::new(1, RegClass::Gpr64)).operands
        );
        // 32-bit: not rewritten (the doubling LEA is 64-bit).
        assert_eq!(
            rewritten(X86ISelInst::new(
                X86Opcode::ImulRRI,
                vec![vreg32(4), vreg32(3), X86ISelOperand::Imm(2)],
            ))
            .opcode,
            X86Opcode::ImulRRI
        );
        // Mixed classes: not rewritten, whichever operand is not 64-bit
        // (each class check is pinned on its own).
        assert_eq!(
            rewritten(X86ISelInst::new(
                X86Opcode::ImulRRI,
                vec![vreg(4), vreg32(3), X86ISelOperand::Imm(2)],
            ))
            .opcode,
            X86Opcode::ImulRRI
        );
        assert_eq!(
            rewritten(X86ISelInst::new(
                X86Opcode::ImulRRI,
                vec![vreg32(4), vreg(3), X86ISelOperand::Imm(2)],
            ))
            .opcode,
            X86Opcode::ImulRRI
        );
        // d == s: not rewritten.
        assert_eq!(
            rewritten(X86ISelInst::new(
                X86Opcode::ImulRRI,
                vec![vreg(5), vreg(5), X86ISelOperand::Imm(2)],
            ))
            .opcode,
            X86Opcode::ImulRRI
        );
    }

    /// A compile that keeps proof certificates (every constructor's default)
    /// withholds both certificate-free IMUL reductions: `x * 2` keeps its
    /// IMUL even with dead flags, and a store between an IMUL and the next
    /// full flag writer keeps an otherwise reducible IMUL (`x * 3`, the
    /// pre-existing scaled-LEA arm) because the historical scan stops at it.
    /// The same functions are reduced once the reductions are enabled.
    #[test]
    fn x86_peephole_withholds_the_certificate_free_imul_reductions_by_default() {
        let first = |imm: i64, store: bool, certificate_free: bool| {
            let mut insts = vec![X86ISelInst::new(
                X86Opcode::ImulRRI,
                vec![vreg(2), vreg(1), X86ISelOperand::Imm(imm)],
            )];
            if store {
                insts.push(store_of(2, 9, X86Opcode::MovMR));
            }
            insts.push(X86ISelInst::new(
                X86Opcode::AddRR,
                vec![vreg(8), vreg(7), vreg(6)],
            ));
            insts.push(X86ISelInst::new(X86Opcode::Ret, vec![]));
            let mut func = make_func(insts);
            X86Peephole::default()
                .with_certificate_free_imul_reductions(certificate_free)
                .run_on_function(&mut func);
            entry_opcodes(&func)[0]
        };
        // The doubling-LEA arm.
        assert_eq!(first(2, false, false), X86Opcode::ImulRRI);
        assert_eq!(first(2, false, true), X86Opcode::LeaSib);
        // The store-passing scan (the x3 arm itself is not new).
        assert_eq!(first(3, false, false), X86Opcode::LeaSib);
        assert_eq!(first(3, true, false), X86Opcode::ImulRRI);
        assert_eq!(first(3, true, true), X86Opcode::LeaSib);
        // `X86Peephole::new` and `with_admissions` withhold them too.
        for mut peephole in [
            X86Peephole::new(|_| false),
            X86Peephole::with_admissions(|_| false, |_, _, _| false),
        ] {
            let mut func = make_func(vec![
                X86ISelInst::new(
                    X86Opcode::ImulRRI,
                    vec![vreg(2), vreg(1), X86ISelOperand::Imm(2)],
                ),
                X86ISelInst::new(X86Opcode::AddRR, vec![vreg(8), vreg(7), vreg(6)]),
                X86ISelInst::new(X86Opcode::Ret, vec![]),
            ]);
            peephole.run_on_function(&mut func);
            assert_eq!(entry_opcodes(&func)[0], X86Opcode::ImulRRI);
        }
    }

    #[test]
    fn x86_peephole_keeps_imul_rri_two_when_its_flags_are_read() {
        let mut func = make_func(vec![
            X86ISelInst::new(
                X86Opcode::ImulRRI,
                vec![vreg(2), vreg(1), X86ISelOperand::Imm(2)],
            ),
            X86ISelInst::new(
                X86Opcode::Jcc,
                vec![
                    X86ISelOperand::CondCode(X86CondCode::O),
                    X86ISelOperand::Block(Block(1)),
                ],
            ),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut peephole = X86Peephole::default().with_certificate_free_imul_reductions(true);
        peephole.run_on_function(&mut func);
        assert_eq!(entry_opcodes(&func)[0], X86Opcode::ImulRRI);
    }

    fn store_of(value: u32, base: u32, opcode: X86Opcode) -> X86ISelInst {
        X86ISelInst::new(
            opcode,
            vec![
                X86ISelOperand::MemAddr {
                    base: Box::new(vreg(base)),
                    disp: 0,
                },
                vreg(value),
            ],
        )
    }

    /// A plain store between the IMUL and the next full flag writer does not
    /// hide the flags' death (TY's `ty_bfs_kernel` shape: `y * 2` stored, then
    /// an `add`); a volatile store does, and so does a flag reader after the
    /// store, and a block that ends without a full overwrite.
    #[test]
    fn x86_peephole_imul_rri_flags_die_past_a_plain_store_only() {
        let imul = || {
            X86ISelInst::new(
                X86Opcode::ImulRRI,
                vec![vreg(2), vreg(1), X86ISelOperand::Imm(2)],
            )
        };
        let add = X86ISelInst::new(X86Opcode::AddRR, vec![vreg(4), vreg(3), vreg(1)]);
        let first = |insts: Vec<X86ISelInst>| {
            let mut func = make_func(insts);
            X86Peephole::default()
                .with_certificate_free_imul_reductions(true)
                .run_on_function(&mut func);
            entry_opcodes(&func)[0]
        };
        let ret = || X86ISelInst::new(X86Opcode::Ret, vec![]);
        assert_eq!(
            first(vec![
                imul(),
                store_of(2, 9, X86Opcode::MovMR),
                add.clone(),
                ret()
            ]),
            X86Opcode::LeaSib
        );
        assert_eq!(
            first(vec![
                imul(),
                store_of(2, 9, X86Opcode::VolatileMovMR),
                add.clone(),
                ret()
            ]),
            X86Opcode::ImulRRI
        );
        assert_eq!(
            first(vec![
                imul(),
                store_of(2, 9, X86Opcode::MovMR),
                X86ISelInst::new(
                    X86Opcode::Jcc,
                    vec![
                        X86ISelOperand::CondCode(X86CondCode::O),
                        X86ISelOperand::Block(Block(1)),
                    ],
                ),
                ret()
            ]),
            X86Opcode::ImulRRI
        );
        assert_eq!(
            first(vec![imul(), store_of(2, 9, X86Opcode::MovMR), ret()]),
            X86Opcode::ImulRRI
        );
    }

    #[test]
    fn x86_peephole_removes_self_imul_rri_one_when_flags_die() {
        let mut func = make_func(vec![
            X86ISelInst::new(
                X86Opcode::ImulRRI,
                vec![vreg(2), vreg(2), X86ISelOperand::Imm(1)],
            ),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(2), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut peephole = X86Peephole::default();

        assert!(peephole.run_on_function(&mut func));

        assert_eq!(
            entry_opcodes(&func),
            vec![X86Opcode::TestRR, X86Opcode::Ret]
        );
    }

    #[test]
    fn x86_peephole_rewrites_imul_rri_zero_to_xor_zero_when_flags_die() {
        let mut func = make_func(vec![
            X86ISelInst::new(
                X86Opcode::ImulRRI,
                vec![vreg(2), vreg(1), X86ISelOperand::Imm(0)],
            )
            .with_proof_origin(X86ProofOrigin::AtomicLoad),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(2), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(
                X86Opcode::ImulRRI,
                vec![vreg32(4), vreg32(3), X86ISelOperand::Imm(0)],
            ),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg32(4), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(
                X86Opcode::ImulRRI,
                vec![vreg(6), vreg(6), X86ISelOperand::Imm(0)],
            ),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(6), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut peephole = X86Peephole::default();

        assert!(peephole.run_on_function(&mut func));

        let insts = entry_insts(&func);
        assert_eq!(
            entry_opcodes(&func),
            vec![
                X86Opcode::XorRR,
                X86Opcode::TestRR,
                X86Opcode::XorRR,
                X86Opcode::TestRR,
                X86Opcode::XorRR,
                X86Opcode::TestRR,
                X86Opcode::Ret,
            ]
        );
        assert_eq!(insts[0].operands, vec![vreg(2), vreg(2)]);
        assert_eq!(insts[0].proof_origin, Some(X86ProofOrigin::AtomicLoad));
        assert_eq!(insts[2].operands, vec![vreg32(4), vreg32(4)]);
        assert_eq!(insts[4].operands, vec![vreg(6), vreg(6)]);
    }

    #[test]
    fn x86_peephole_preserves_imul_rri_zero_when_flags_are_read_or_live_out() {
        let mut read_func = make_func(vec![
            X86ISelInst::new(
                X86Opcode::ImulRRI,
                vec![vreg(2), vreg(1), X86ISelOperand::Imm(0)],
            ),
            X86ISelInst::new(
                X86Opcode::Setcc,
                vec![vreg32(3), X86ISelOperand::CondCode(X86CondCode::O)],
            ),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut live_out_func = make_func(vec![
            X86ISelInst::new(
                X86Opcode::ImulRRI,
                vec![vreg(2), vreg(1), X86ISelOperand::Imm(0)],
            ),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut peephole = X86Peephole::default();

        assert!(!peephole.run_on_function(&mut read_func));
        assert!(!peephole.run_on_function(&mut live_out_func));

        assert_eq!(
            entry_opcodes(&read_func),
            vec![X86Opcode::ImulRRI, X86Opcode::Setcc, X86Opcode::Ret]
        );
        assert_eq!(
            entry_opcodes(&live_out_func),
            vec![X86Opcode::ImulRRI, X86Opcode::Ret]
        );
    }

    #[test]
    fn x86_peephole_rewrites_self_imul_rri_minus_one_to_neg_when_flags_die() {
        let mut func = make_func(vec![
            X86ISelInst::new(
                X86Opcode::ImulRRI,
                vec![vreg(2), vreg(2), X86ISelOperand::Imm(-1)],
            )
            .with_proof_origin(X86ProofOrigin::AtomicLoad),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(2), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(X86Opcode::ImulRRI, vec![vreg32(4), X86ISelOperand::Imm(-1)]),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg32(4), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut peephole = X86Peephole::default();

        assert!(peephole.run_on_function(&mut func));

        let insts = entry_insts(&func);
        assert_eq!(
            entry_opcodes(&func),
            vec![
                X86Opcode::Neg,
                X86Opcode::TestRR,
                X86Opcode::Neg,
                X86Opcode::TestRR,
                X86Opcode::Ret,
            ]
        );
        assert_eq!(insts[0].operands, vec![vreg(2)]);
        assert_eq!(insts[0].proof_origin, Some(X86ProofOrigin::AtomicLoad));
        assert_eq!(insts[2].operands, vec![vreg32(4)]);
    }

    #[test]
    fn x86_peephole_preserves_non_self_and_non_minus_one_imul_rri() {
        let mut func = make_func(vec![
            X86ISelInst::new(
                X86Opcode::ImulRRI,
                vec![vreg(2), vreg(1), X86ISelOperand::Imm(-1)],
            ),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(2), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(
                X86Opcode::ImulRRI,
                vec![vreg(4), vreg(4), X86ISelOperand::Imm(-2)],
            ),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(4), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut peephole = X86Peephole::default();

        assert!(peephole.run_on_function(&mut func));

        let insts = entry_insts(&func);
        assert_eq!(
            entry_opcodes(&func),
            vec![
                X86Opcode::ImulRRI,
                X86Opcode::TestRR,
                X86Opcode::ImulRRI,
                X86Opcode::TestRR,
                X86Opcode::Ret,
            ]
        );
        assert_eq!(
            insts[0].operands,
            vec![vreg(2), vreg(1), X86ISelOperand::Imm(-1)]
        );
        assert_eq!(
            insts[2].operands,
            vec![vreg(4), vreg(4), X86ISelOperand::Imm(-2)]
        );
    }

    #[test]
    fn x86_peephole_preserves_self_imul_rri_minus_one_when_flags_are_read_or_live_out() {
        let mut read_func = make_func(vec![
            X86ISelInst::new(
                X86Opcode::ImulRRI,
                vec![vreg(2), vreg(2), X86ISelOperand::Imm(-1)],
            ),
            X86ISelInst::new(
                X86Opcode::Setcc,
                vec![vreg32(3), X86ISelOperand::CondCode(X86CondCode::O)],
            ),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut live_out_func = make_func(vec![
            X86ISelInst::new(
                X86Opcode::ImulRRI,
                vec![vreg(2), vreg(2), X86ISelOperand::Imm(-1)],
            ),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut peephole = X86Peephole::default();

        assert!(!peephole.run_on_function(&mut read_func));
        assert!(!peephole.run_on_function(&mut live_out_func));

        assert_eq!(
            entry_opcodes(&read_func),
            vec![X86Opcode::ImulRRI, X86Opcode::Setcc, X86Opcode::Ret]
        );
        assert_eq!(
            entry_opcodes(&live_out_func),
            vec![X86Opcode::ImulRRI, X86Opcode::Ret]
        );
    }

    #[test]
    fn x86_peephole_preserves_imul_rri_one_when_flags_are_read_or_live_out() {
        let mut read_func = make_func(vec![
            X86ISelInst::new(
                X86Opcode::ImulRRI,
                vec![vreg(2), vreg(1), X86ISelOperand::Imm(1)],
            ),
            X86ISelInst::new(
                X86Opcode::Setcc,
                vec![vreg32(3), X86ISelOperand::CondCode(X86CondCode::O)],
            ),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut live_out_func = make_func(vec![
            X86ISelInst::new(
                X86Opcode::ImulRRI,
                vec![vreg(2), vreg(1), X86ISelOperand::Imm(1)],
            ),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut peephole = X86Peephole::default();

        assert!(!peephole.run_on_function(&mut read_func));
        assert!(!peephole.run_on_function(&mut live_out_func));

        assert_eq!(
            entry_opcodes(&read_func),
            vec![X86Opcode::ImulRRI, X86Opcode::Setcc, X86Opcode::Ret]
        );
        assert_eq!(
            entry_opcodes(&live_out_func),
            vec![X86Opcode::ImulRRI, X86Opcode::Ret]
        );
    }

    #[test]
    fn x86_peephole_preserves_non_identity_imul_rri_immediates() {
        // 6: none of the IMUL reductions applies (2, 3, 5, 7, 9 and 2^a +/- 1
        // are reduced).
        let mut func = make_func(vec![
            X86ISelInst::new(
                X86Opcode::ImulRRI,
                vec![vreg(2), vreg(1), X86ISelOperand::Imm(6)],
            ),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(2), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut peephole = X86Peephole::default();

        assert!(peephole.run_on_function(&mut func));

        assert_eq!(
            entry_opcodes(&func),
            vec![X86Opcode::ImulRRI, X86Opcode::TestRR, X86Opcode::Ret]
        );
    }

    #[test]
    fn x86_peephole_preserves_identity_when_flags_are_read() {
        let mut func = make_func(vec![
            X86ISelInst::new(
                X86Opcode::AddRI,
                vec![vreg(1), vreg(0), X86ISelOperand::Imm(0)],
            ),
            X86ISelInst::new(
                X86Opcode::Setcc,
                vec![vreg(2), X86ISelOperand::CondCode(X86CondCode::E)],
            ),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut peephole = X86Peephole::default();

        assert!(!peephole.run_on_function(&mut func));

        assert_eq!(
            entry_opcodes(&func),
            vec![X86Opcode::AddRI, X86Opcode::Setcc, X86Opcode::Ret]
        );
    }

    #[test]
    fn x86_peephole_does_not_treat_not_as_flag_kill() {
        let mut func = make_func(vec![
            X86ISelInst::new(
                X86Opcode::AddRI,
                vec![vreg(1), vreg(0), X86ISelOperand::Imm(0)],
            ),
            X86ISelInst::new(X86Opcode::Not, vec![vreg(2)]),
            X86ISelInst::new(
                X86Opcode::Setcc,
                vec![vreg(3), X86ISelOperand::CondCode(X86CondCode::E)],
            ),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut peephole = X86Peephole::default();

        assert!(!peephole.run_on_function(&mut func));

        assert_eq!(
            entry_opcodes(&func),
            vec![
                X86Opcode::AddRI,
                X86Opcode::Not,
                X86Opcode::Setcc,
                X86Opcode::Ret,
            ]
        );
    }

    #[test]
    fn x86_peephole_does_not_treat_inc_dec_as_full_flag_kills() {
        for opcode in [X86Opcode::Inc, X86Opcode::Dec] {
            let mut func = make_func(vec![
                X86ISelInst::new(
                    X86Opcode::AddRI,
                    vec![vreg(1), vreg(0), X86ISelOperand::Imm(0)],
                ),
                X86ISelInst::new(opcode, vec![vreg(2)]),
                X86ISelInst::new(
                    X86Opcode::Setcc,
                    vec![vreg(3), X86ISelOperand::CondCode(X86CondCode::B)],
                ),
                X86ISelInst::new(X86Opcode::Ret, vec![]),
            ]);
            let mut peephole = X86Peephole::default();

            assert!(
                !peephole.run_on_function(&mut func),
                "{:?} must not prove CF dead",
                opcode
            );

            assert_eq!(
                entry_opcodes(&func),
                vec![X86Opcode::AddRI, opcode, X86Opcode::Setcc, X86Opcode::Ret,]
            );
        }
    }

    #[test]
    fn x86_peephole_does_not_treat_shift_zero_as_flag_kill() {
        let mut func = make_func(vec![
            X86ISelInst::new(
                X86Opcode::AddRI,
                vec![vreg(1), vreg(0), X86ISelOperand::Imm(0)],
            ),
            X86ISelInst::new(
                X86Opcode::ShlRI,
                vec![vreg(3), vreg(2), X86ISelOperand::Imm(0)],
            ),
            X86ISelInst::new(
                X86Opcode::Setcc,
                vec![vreg(4), X86ISelOperand::CondCode(X86CondCode::E)],
            ),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut peephole = X86Peephole::default();

        assert!(peephole.run_on_function(&mut func));

        assert_eq!(
            entry_opcodes(&func),
            vec![
                X86Opcode::AddRI,
                X86Opcode::MovRR,
                X86Opcode::Setcc,
                X86Opcode::Ret,
            ]
        );
        assert_eq!(
            entry_insts(&func)[0].operands,
            vec![vreg(1), vreg(0), X86ISelOperand::Imm(0)]
        );
        assert_eq!(entry_insts(&func)[1].operands, vec![vreg(3), vreg(2)]);
    }

    #[test]
    fn x86_peephole_preserves_identity_when_flags_may_export_to_branch_or_return() {
        let mut branch_func = make_func(vec![
            X86ISelInst::new(
                X86Opcode::AddRI,
                vec![vreg(1), vreg(0), X86ISelOperand::Imm(0)],
            ),
            X86ISelInst::new(
                X86Opcode::Jcc,
                vec![
                    X86ISelOperand::CondCode(X86CondCode::E),
                    X86ISelOperand::Block(Block(1)),
                ],
            ),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut return_func = make_func(vec![
            X86ISelInst::new(
                X86Opcode::AddRI,
                vec![vreg(1), vreg(0), X86ISelOperand::Imm(0)],
            ),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut peephole = X86Peephole::default();

        assert!(!peephole.run_on_function(&mut branch_func));
        assert!(!peephole.run_on_function(&mut return_func));

        assert_eq!(
            entry_opcodes(&branch_func),
            vec![X86Opcode::AddRI, X86Opcode::Jcc, X86Opcode::Ret]
        );
        assert_eq!(
            entry_opcodes(&return_func),
            vec![X86Opcode::AddRI, X86Opcode::Ret]
        );
    }

    #[test]
    fn x86_peephole_preserves_fixed_memory_and_side_effect_candidates() {
        let mem = X86ISelOperand::MemAddr {
            base: Box::new(vreg(0)),
            disp: 8,
        };
        let mut func = make_func(vec![
            X86ISelInst::new(
                X86Opcode::AndRI,
                vec![vreg(1), X86ISelOperand::PReg(RAX), X86ISelOperand::Imm(-1)],
            ),
            X86ISelInst::new(
                X86Opcode::AndRI,
                vec![vreg(2), mem, X86ISelOperand::Imm(-1)],
            ),
            X86ISelInst::with_flags(
                X86Opcode::AddRI,
                vec![vreg(3), vreg(0), X86ISelOperand::Imm(0)],
                InstFlags::HAS_SIDE_EFFECTS,
            ),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(3), X86ISelOperand::Imm(1)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut peephole = X86Peephole::default();

        assert!(!peephole.run_on_function(&mut func));

        assert_eq!(
            entry_opcodes(&func),
            vec![
                X86Opcode::AndRI,
                X86Opcode::AndRI,
                X86Opcode::AddRI,
                X86Opcode::CmpRI,
                X86Opcode::Ret,
            ]
        );
        assert_eq!(entry_insts(&func)[2].flags, InstFlags::HAS_SIDE_EFFECTS);
    }

    // -----------------------------------------------------------------------
    // Setcc/Movzx pair retention
    // -----------------------------------------------------------------------
    //
    // A `Setcc %D; Movzx %D,%D` pair whose bool is not consumed by a branch
    // must survive the peephole intact: every register model reads `Setcc` as
    // a pure def, which is only true while the Movzx follows it. These shapes
    // were rewritten by the retired setcc-flag-hoist into
    // `XorRR %D,%D; [flag_writer]; Setcc %D` (Movzx deleted), which the
    // allocator could not see depended on %D[31:8].

    #[test]
    fn x86_peephole_keeps_setcc_movzx_pair() {
        let setcc = |d: u32, cc: X86CondCode| {
            X86ISelInst::new(
                X86Opcode::Setcc,
                vec![vreg32(d), X86ISelOperand::CondCode(cc)],
            )
        };
        let movzx = |d: u32| X86ISelInst::new(X86Opcode::Movzx, vec![vreg32(d), vreg32(d)]);
        let cases = vec![
            // Canonical icmp pair, bool consumed only outside the block.
            vec![
                X86ISelInst::new(X86Opcode::CmpRR, vec![vreg(1), vreg(2)]),
                setcc(10, X86CondCode::E),
                movzx(10),
                X86ISelInst::new(X86Opcode::Ret, vec![]),
            ],
            // TestRR flag writer.
            vec![
                X86ISelInst::new(X86Opcode::TestRR, vec![vreg(1), vreg(1)]),
                setcc(10, X86CondCode::NE),
                movzx(10),
                X86ISelInst::new(X86Opcode::Ret, vec![]),
            ],
            // Two independent windows.
            vec![
                X86ISelInst::new(X86Opcode::CmpRR, vec![vreg(1), vreg(2)]),
                setcc(10, X86CondCode::E),
                movzx(10),
                X86ISelInst::new(X86Opcode::CmpRR, vec![vreg(3), vreg(4)]),
                setcc(11, X86CondCode::NE),
                movzx(11),
                X86ISelInst::new(X86Opcode::Ret, vec![]),
            ],
        ];
        for insts in cases {
            let mut func = make_func(insts.clone());
            X86Peephole::default().run_on_function(&mut func);
            let shape = |insts: &[X86ISelInst]| {
                insts
                    .iter()
                    .map(|inst| (inst.opcode, inst.operands.clone()))
                    .collect::<Vec<_>>()
            };
            assert_eq!(
                shape(entry_insts(&func)),
                shape(&insts),
                "the Setcc/Movzx pair must be left intact"
            );
        }
    }

    #[test]
    fn x86_peephole_fuses_condbr_lowering_shape_into_direct_jcc() {
        // The BCP hot path lowers `condbr (icmp eq a, b), then, else` to
        //   CmpRR a, b ; Setcc E, %D ; Movzx %D, %D ;
        //   CmpRI %D, 0 ; Jcc NE, then ; Jmp else
        // The cmp-setcc-branch fusion (which runs before the
        // single-instruction cmp-zero->test rewrite) recognizes that the
        // boolean %D is single-use and dead after the branch, and collapses the
        // whole chain to a direct `CmpRR a, b ; Jcc E, then ; Jmp else`. This
        // was previously the "V1 conservative" decline case; the fusion lifts it.
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::CmpRR, vec![vreg(1), vreg(2)]),
            X86ISelInst::new(
                X86Opcode::Setcc,
                vec![vreg32(20), X86ISelOperand::CondCode(X86CondCode::E)],
            ),
            X86ISelInst::new(X86Opcode::Movzx, vec![vreg32(20), vreg32(20)]),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg32(20), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(
                X86Opcode::Jcc,
                vec![
                    X86ISelOperand::CondCode(X86CondCode::NE),
                    X86ISelOperand::Block(Block(1)),
                ],
            ),
            X86ISelInst::new(X86Opcode::Jmp, vec![X86ISelOperand::Block(Block(2))]),
        ]);
        let mut peephole = X86Peephole::default();
        assert!(peephole.run_on_function(&mut func));
        // The boolean materialization (Setcc/Movzx/zero-test) is gone; only the
        // comparison and a direct conditional jump on its flags remain.
        assert_eq!(
            entry_opcodes(&func),
            vec![X86Opcode::CmpRR, X86Opcode::Jcc, X86Opcode::Jmp],
        );
        let insts = entry_insts(&func);
        assert_eq!(insts[0].operands, vec![vreg(1), vreg(2)]);
        // Jcc NE on (eq-bool != 0) becomes Jcc E (branch when eq holds).
        assert_eq!(
            insts[1].operands,
            vec![
                X86ISelOperand::CondCode(X86CondCode::E),
                X86ISelOperand::Block(Block(1)),
            ]
        );
    }

    // -----------------------------------------------------------------------
    // AND-power-of-2 + CMP-zero + Jcc -> BT + Jcc tests
    // -----------------------------------------------------------------------
    //
    // See `try_and_pow2_bt_branch` for the hand-proof and side conditions.

    #[test]
    fn x86_peephole_and_pow2_bt_branch_fires_on_two_operand_form_jcc_ne() {
        // AndRI %1, #4 (1<<2) ; CmpRI %1, 0 ; Jcc NE, bb1
        //   -> BtRI %1, #2 ; Jcc B, bb1   (B = CF set = bit 2 was set)
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::AndRI, vec![vreg(1), X86ISelOperand::Imm(4)])
                .with_proof_origin(X86ProofOrigin::AtomicLoad),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(1), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(
                X86Opcode::Jcc,
                vec![
                    X86ISelOperand::CondCode(X86CondCode::NE),
                    X86ISelOperand::Block(Block(1)),
                ],
            ),
            X86ISelInst::new(X86Opcode::Jmp, vec![X86ISelOperand::Block(Block(2))]),
        ]);
        let mut peephole = X86Peephole::default();

        assert!(peephole.run_on_function(&mut func));

        let insts = entry_insts(&func);
        assert_eq!(
            entry_opcodes(&func),
            vec![X86Opcode::BtRI, X86Opcode::Jcc, X86Opcode::Jmp]
        );
        assert_eq!(insts[0].operands, vec![vreg(1), X86ISelOperand::Imm(2)]);
        // proof_origin must transfer from the original AND.
        assert_eq!(insts[0].proof_origin, Some(X86ProofOrigin::AtomicLoad));
        // Jcc must use the inverted-to-CF condition: NE -> B (carry set).
        assert_eq!(
            insts[1].operands,
            vec![
                X86ISelOperand::CondCode(X86CondCode::B),
                X86ISelOperand::Block(Block(1)),
            ]
        );
    }

    #[test]
    fn x86_peephole_and_pow2_bt_branch_fires_on_three_operand_form_jcc_e() {
        // AndRI %3, %2, #1 (1<<0) ; CmpRI %3, 0 ; Jcc E, bb1
        //   -> BtRI %2, #0 ; Jcc AE, bb1     (AE = CF clear = bit 0 was 0)
        let mut func = make_func(vec![
            X86ISelInst::new(
                X86Opcode::AndRI,
                vec![vreg(3), vreg(2), X86ISelOperand::Imm(1)],
            ),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(3), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(
                X86Opcode::Jcc,
                vec![
                    X86ISelOperand::CondCode(X86CondCode::E),
                    X86ISelOperand::Block(Block(1)),
                ],
            ),
            X86ISelInst::new(X86Opcode::Jmp, vec![X86ISelOperand::Block(Block(2))]),
        ]);
        let mut peephole = X86Peephole::default();

        assert!(peephole.run_on_function(&mut func));

        let insts = entry_insts(&func);
        assert_eq!(
            entry_opcodes(&func),
            vec![X86Opcode::BtRI, X86Opcode::Jcc, X86Opcode::Jmp]
        );
        // BT reads the AND's source register, not its destination.
        assert_eq!(insts[0].operands, vec![vreg(2), X86ISelOperand::Imm(0)]);
        assert_eq!(
            insts[1].operands,
            vec![
                X86ISelOperand::CondCode(X86CondCode::AE),
                X86ISelOperand::Block(Block(1)),
            ]
        );
    }

    #[test]
    fn x86_peephole_and_pow2_bt_branch_fires_on_b1_condition_lowering_shape() {
        // Mirrors `normalize_condition_operand` + `emit_condition_zero_test`
        // for B1 conditions: Movzx; AndRI %d, %d, 1; CmpRI %d, 0; Jcc NE.
        // The peephole should fire on the AND/CMP/Jcc triple, leaving the
        // Movzx untouched.
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::Movzx, vec![vreg32(5), vreg32(4)]),
            X86ISelInst::new(
                X86Opcode::AndRI,
                vec![vreg32(5), vreg32(5), X86ISelOperand::Imm(1)],
            ),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg32(5), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(
                X86Opcode::Jcc,
                vec![
                    X86ISelOperand::CondCode(X86CondCode::NE),
                    X86ISelOperand::Block(Block(1)),
                ],
            ),
            X86ISelInst::new(X86Opcode::Jmp, vec![X86ISelOperand::Block(Block(2))]),
        ]);
        let mut peephole = X86Peephole::default();

        assert!(peephole.run_on_function(&mut func));

        let insts = entry_insts(&func);
        assert_eq!(
            entry_opcodes(&func),
            vec![
                X86Opcode::Movzx,
                X86Opcode::BtRI,
                X86Opcode::Jcc,
                X86Opcode::Jmp,
            ]
        );
        // BT reads the Movzx destination directly (AndRI's three-op form had
        // %5 as both dst and src).
        assert_eq!(insts[1].operands, vec![vreg32(5), X86ISelOperand::Imm(0)]);
        assert_eq!(
            insts[2].operands,
            vec![
                X86ISelOperand::CondCode(X86CondCode::B),
                X86ISelOperand::Block(Block(1)),
            ]
        );
    }

    #[test]
    fn x86_peephole_and_pow2_bt_branch_declines_when_dst_has_other_uses() {
        // %3 is consumed by an AddRI after the Jcc - single-use side
        // condition fails.
        let mut func = make_func(vec![
            X86ISelInst::new(
                X86Opcode::AndRI,
                vec![vreg(3), vreg(2), X86ISelOperand::Imm(4)],
            ),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(3), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(
                X86Opcode::Jcc,
                vec![
                    X86ISelOperand::CondCode(X86CondCode::NE),
                    X86ISelOperand::Block(Block(1)),
                ],
            ),
            X86ISelInst::new(
                X86Opcode::AddRI,
                vec![vreg(4), vreg(3), X86ISelOperand::Imm(1)],
            ),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut peephole = X86Peephole::default();
        peephole.run_on_function(&mut func);

        let opcodes = entry_opcodes(&func);
        // The AND/CMP/JCC triple must remain (no BtRI introduced).
        assert!(
            !opcodes.contains(&X86Opcode::BtRI),
            "BtRI must not appear when %dst escapes: {opcodes:?}"
        );
        assert_eq!(opcodes[0], X86Opcode::AndRI);
    }

    #[test]
    fn x86_peephole_and_pow2_bt_branch_declines_on_non_power_of_two_imm() {
        // imm=5 has two bits set; refuse to fire.
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::AndRI, vec![vreg(1), X86ISelOperand::Imm(5)]),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(1), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(
                X86Opcode::Jcc,
                vec![
                    X86ISelOperand::CondCode(X86CondCode::NE),
                    X86ISelOperand::Block(Block(1)),
                ],
            ),
            X86ISelInst::new(X86Opcode::Jmp, vec![X86ISelOperand::Block(Block(2))]),
        ]);
        let mut peephole = X86Peephole::default();
        peephole.run_on_function(&mut func);

        let opcodes = entry_opcodes(&func);
        assert!(!opcodes.contains(&X86Opcode::BtRI));
        // The original AndRI must remain (we did not fire the BT rewrite).
        // The cmp-zero -> test-rr single-instruction rewrite may still fire,
        // which is unrelated to this side-condition check.
        assert_eq!(opcodes[0], X86Opcode::AndRI);
        assert!(matches!(opcodes[1], X86Opcode::CmpRI | X86Opcode::TestRR));
        assert_eq!(opcodes[2], X86Opcode::Jcc);
    }

    #[test]
    fn x86_peephole_and_pow2_bt_branch_declines_on_zero_imm() {
        // imm=0 is not a power of two; the existing simplifier turns
        // AndRI #0 into xor; we must not fire BT.
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::AndRI, vec![vreg(1), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(1), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(
                X86Opcode::Jcc,
                vec![
                    X86ISelOperand::CondCode(X86CondCode::NE),
                    X86ISelOperand::Block(Block(1)),
                ],
            ),
            X86ISelInst::new(X86Opcode::Jmp, vec![X86ISelOperand::Block(Block(2))]),
        ]);
        let mut peephole = X86Peephole::default();
        peephole.run_on_function(&mut func);

        assert!(!entry_opcodes(&func).contains(&X86Opcode::BtRI));
    }

    #[test]
    fn x86_peephole_and_pow2_bt_branch_declines_on_negative_imm() {
        // imm=-1 has all bits set, count_ones() is 64; refuse.
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::AndRI, vec![vreg(1), X86ISelOperand::Imm(-1)]),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(1), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(
                X86Opcode::Jcc,
                vec![
                    X86ISelOperand::CondCode(X86CondCode::NE),
                    X86ISelOperand::Block(Block(1)),
                ],
            ),
            X86ISelInst::new(X86Opcode::Jmp, vec![X86ISelOperand::Block(Block(2))]),
        ]);
        let mut peephole = X86Peephole::default();
        peephole.run_on_function(&mut func);

        assert!(!entry_opcodes(&func).contains(&X86Opcode::BtRI));
    }

    #[test]
    fn x86_peephole_and_pow2_bt_branch_declines_when_jcc_is_not_e_or_ne() {
        // Jcc S (sign) cannot be expressed as a CF predicate after BT
        // because BT leaves SF undefined. Refuse.
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::AndRI, vec![vreg(1), X86ISelOperand::Imm(8)]),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(1), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(
                X86Opcode::Jcc,
                vec![
                    X86ISelOperand::CondCode(X86CondCode::S),
                    X86ISelOperand::Block(Block(1)),
                ],
            ),
            X86ISelInst::new(X86Opcode::Jmp, vec![X86ISelOperand::Block(Block(2))]),
        ]);
        let mut peephole = X86Peephole::default();
        peephole.run_on_function(&mut func);

        assert!(!entry_opcodes(&func).contains(&X86Opcode::BtRI));
    }

    #[test]
    fn x86_peephole_and_pow2_bt_branch_declines_when_cmp_is_against_nonzero() {
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::AndRI, vec![vreg(1), X86ISelOperand::Imm(4)]),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(1), X86ISelOperand::Imm(1)]),
            X86ISelInst::new(
                X86Opcode::Jcc,
                vec![
                    X86ISelOperand::CondCode(X86CondCode::NE),
                    X86ISelOperand::Block(Block(1)),
                ],
            ),
            X86ISelInst::new(X86Opcode::Jmp, vec![X86ISelOperand::Block(Block(2))]),
        ]);
        let mut peephole = X86Peephole::default();
        peephole.run_on_function(&mut func);

        assert!(!entry_opcodes(&func).contains(&X86Opcode::BtRI));
    }

    #[test]
    fn x86_peephole_and_pow2_bt_branch_declines_on_intervening_flag_write() {
        // AndRI ... ; AddRI (writes flags) ; CmpRI ; Jcc - the intervening
        // AddRI breaks the adjacency requirement.
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::AndRI, vec![vreg(1), X86ISelOperand::Imm(4)]),
            X86ISelInst::new(
                X86Opcode::AddRI,
                vec![vreg(5), vreg(6), X86ISelOperand::Imm(1)],
            ),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(1), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(
                X86Opcode::Jcc,
                vec![
                    X86ISelOperand::CondCode(X86CondCode::NE),
                    X86ISelOperand::Block(Block(1)),
                ],
            ),
            X86ISelInst::new(X86Opcode::Jmp, vec![X86ISelOperand::Block(Block(2))]),
        ]);
        let mut peephole = X86Peephole::default();
        peephole.run_on_function(&mut func);

        assert!(!entry_opcodes(&func).contains(&X86Opcode::BtRI));
    }

    #[test]
    fn x86_peephole_and_pow2_bt_branch_declines_when_cmp_uses_different_vreg() {
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::AndRI, vec![vreg(1), X86ISelOperand::Imm(4)]),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(2), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(
                X86Opcode::Jcc,
                vec![
                    X86ISelOperand::CondCode(X86CondCode::NE),
                    X86ISelOperand::Block(Block(1)),
                ],
            ),
            X86ISelInst::new(X86Opcode::Jmp, vec![X86ISelOperand::Block(Block(2))]),
        ]);
        let mut peephole = X86Peephole::default();
        peephole.run_on_function(&mut func);

        assert!(!entry_opcodes(&func).contains(&X86Opcode::BtRI));
    }

    #[test]
    fn x86_peephole_and_pow2_bt_branch_declines_on_gpr32_with_bit_above_31() {
        // imm = 1 << 32 with a Gpr32 AndRI would attempt to test bit 32 of
        // a 32-bit register. Refuse. (And the AndRI on a Gpr32 with a
        // signed-i64 imm of 1<<32 is itself ill-formed; this just exercises
        // the bit-index guard.)
        let mut func = make_func(vec![
            X86ISelInst::new(
                X86Opcode::AndRI,
                vec![vreg32(1), X86ISelOperand::Imm(1_i64 << 32)],
            ),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg32(1), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(
                X86Opcode::Jcc,
                vec![
                    X86ISelOperand::CondCode(X86CondCode::NE),
                    X86ISelOperand::Block(Block(1)),
                ],
            ),
            X86ISelInst::new(X86Opcode::Jmp, vec![X86ISelOperand::Block(Block(2))]),
        ]);
        let mut peephole = X86Peephole::default();
        peephole.run_on_function(&mut func);

        assert!(!entry_opcodes(&func).contains(&X86Opcode::BtRI));
    }

    #[test]
    fn x86_peephole_and_pow2_bt_branch_handles_two_independent_windows() {
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::AndRI, vec![vreg(1), X86ISelOperand::Imm(2)]),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(1), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(
                X86Opcode::Jcc,
                vec![
                    X86ISelOperand::CondCode(X86CondCode::NE),
                    X86ISelOperand::Block(Block(1)),
                ],
            ),
            X86ISelInst::new(X86Opcode::AndRI, vec![vreg(3), X86ISelOperand::Imm(8)]),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(3), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(
                X86Opcode::Jcc,
                vec![
                    X86ISelOperand::CondCode(X86CondCode::E),
                    X86ISelOperand::Block(Block(2)),
                ],
            ),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut peephole = X86Peephole::default();

        assert!(peephole.run_on_function(&mut func));

        let insts = entry_insts(&func);
        assert_eq!(
            entry_opcodes(&func),
            vec![
                X86Opcode::BtRI,
                X86Opcode::Jcc,
                X86Opcode::BtRI,
                X86Opcode::Jcc,
                X86Opcode::Ret,
            ]
        );
        assert_eq!(insts[0].operands, vec![vreg(1), X86ISelOperand::Imm(1)]);
        assert_eq!(
            insts[1].operands[0],
            X86ISelOperand::CondCode(X86CondCode::B)
        );
        assert_eq!(insts[2].operands, vec![vreg(3), X86ISelOperand::Imm(3)]);
        assert_eq!(
            insts[3].operands[0],
            X86ISelOperand::CondCode(X86CondCode::AE)
        );
    }

    #[test]
    fn x86_peephole_and_pow2_bt_branch_declines_when_dst_escapes_to_other_block() {
        // %1 is used in a successor block via a Movzx; the rewrite would
        // erase the AND write-back and the successor would see the pre-AND
        // value. Refuse.
        let sig = Signature {
            params: vec![],
            returns: vec![Type::I64],
        };
        let mut func = X86ISelFunction::new("bt_branch_cross_block".to_string(), sig);
        let entry = Block(0);
        let other = Block(1);
        func.ensure_block(entry);
        func.ensure_block(other);
        func.next_vreg = 16;

        for inst in [
            X86ISelInst::new(X86Opcode::AndRI, vec![vreg(1), X86ISelOperand::Imm(4)]),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(1), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(
                X86Opcode::Jcc,
                vec![
                    X86ISelOperand::CondCode(X86CondCode::NE),
                    X86ISelOperand::Block(other),
                ],
            ),
            X86ISelInst::new(X86Opcode::Jmp, vec![X86ISelOperand::Block(other)]),
        ] {
            func.push_inst(entry, inst);
        }
        // Successor block reads %1 - the cross-block liveness guard should
        // suppress the rewrite.
        func.push_inst(
            other,
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(2), vreg(1)]),
        );
        func.push_inst(other, X86ISelInst::new(X86Opcode::Ret, vec![]));

        let mut peephole = X86Peephole::default();
        peephole.run_on_function(&mut func);

        let entry_block = &func.blocks[&entry];
        let opcodes: Vec<_> = entry_block.insts.iter().map(|i| i.opcode).collect();
        assert!(
            !opcodes.contains(&X86Opcode::BtRI),
            "BtRI must not appear when %dst escapes to another block: {opcodes:?}"
        );
    }

    #[test]
    fn x86_peephole_and_pow2_bt_branch_declines_on_andri_with_side_effects() {
        // AndRI flagged with HAS_SIDE_EFFECTS beyond the opcode default must
        // not be rewritten - we cannot prove the foreign effect is local.
        let mut func = make_func(vec![
            X86ISelInst::with_flags(
                X86Opcode::AndRI,
                vec![vreg(1), X86ISelOperand::Imm(4)],
                X86Opcode::AndRI
                    .default_flags()
                    .union(InstFlags::HAS_SIDE_EFFECTS),
            ),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(1), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(
                X86Opcode::Jcc,
                vec![
                    X86ISelOperand::CondCode(X86CondCode::NE),
                    X86ISelOperand::Block(Block(1)),
                ],
            ),
            X86ISelInst::new(X86Opcode::Jmp, vec![X86ISelOperand::Block(Block(2))]),
        ]);
        let mut peephole = X86Peephole::default();
        peephole.run_on_function(&mut func);

        assert!(!entry_opcodes(&func).contains(&X86Opcode::BtRI));
    }

    // -----------------------------------------------------------------------
    // cmp + setcc + (normalize) + zero-test + Jcc  ->  cmp + Jcc fusion
    // -----------------------------------------------------------------------

    /// Build the exact ISel output for `Icmp(cc) ; CondBr` of a B1 condition:
    ///   CmpRR lhs, rhs
    ///   Setcc %D, cc
    ///   Movzx %D, %D
    ///   Movzx %D2, %D              ; normalize (B1 -> Gpr64)
    ///   AndRI %D2, %D2, 1          ; normalize mask
    ///   CmpRI %D2, 0               ; zero-test
    ///   Jcc {NE|E}, then ; Jmp else
    fn icmp_condbr_shape(cc: X86CondCode, jcc_cc: X86CondCode) -> X86ISelFunction {
        make_func(vec![
            X86ISelInst::new(X86Opcode::CmpRR, vec![vreg(2), vreg(3)]),
            X86ISelInst::new(
                X86Opcode::Setcc,
                vec![vreg32(5), X86ISelOperand::CondCode(cc)],
            ),
            X86ISelInst::new(X86Opcode::Movzx, vec![vreg32(5), vreg32(5)]),
            X86ISelInst::new(X86Opcode::Movzx, vec![vreg(6), vreg32(5)]),
            X86ISelInst::new(
                X86Opcode::AndRI,
                vec![vreg(6), vreg(6), X86ISelOperand::Imm(1)],
            ),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(6), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(
                X86Opcode::Jcc,
                vec![
                    X86ISelOperand::CondCode(jcc_cc),
                    X86ISelOperand::Block(Block(1)),
                ],
            ),
            X86ISelInst::new(X86Opcode::Jmp, vec![X86ISelOperand::Block(Block(2))]),
        ])
    }

    #[test]
    fn cmp_branch_fusion_fires_on_full_b1_condbr_shape_jcc_ne() {
        // Branch-when-true (Jcc NE on the bool) collapses to Jcc <cc>.
        let mut func = icmp_condbr_shape(X86CondCode::B, X86CondCode::NE);
        let mut peephole = X86Peephole::default();
        assert!(peephole.run_on_function(&mut func));

        assert_eq!(
            entry_opcodes(&func),
            vec![X86Opcode::CmpRR, X86Opcode::Jcc, X86Opcode::Jmp],
        );
        let insts = entry_insts(&func);
        // The Cmp operands are untouched; the Jcc now tests the original cc.
        assert_eq!(insts[0].operands, vec![vreg(2), vreg(3)]);
        assert_eq!(
            insts[1].operands,
            vec![
                X86ISelOperand::CondCode(X86CondCode::B),
                X86ISelOperand::Block(Block(1)),
            ]
        );
    }

    #[test]
    fn cmp_branch_fusion_inverts_cc_on_jcc_e() {
        // Branch-when-false (Jcc E on the bool) collapses to Jcc <cc.invert()>.
        let mut func = icmp_condbr_shape(X86CondCode::B, X86CondCode::E);
        let mut peephole = X86Peephole::default();
        assert!(peephole.run_on_function(&mut func));

        let insts = entry_insts(&func);
        assert_eq!(insts[1].opcode, X86Opcode::Jcc);
        assert_eq!(
            insts[1].operands,
            vec![
                X86ISelOperand::CondCode(X86CondCode::AE), // B.invert() == AE
                X86ISelOperand::Block(Block(1)),
            ]
        );
    }

    #[test]
    fn cmp_branch_fusion_fires_on_direct_testrr_shape() {
        // Without the normalize pair: Cmp; Setcc; Movzx; TestRR %D,%D; Jcc NE.
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::CmpRR, vec![vreg(2), vreg(3)]),
            X86ISelInst::new(
                X86Opcode::Setcc,
                vec![vreg32(5), X86ISelOperand::CondCode(X86CondCode::L)],
            ),
            X86ISelInst::new(X86Opcode::Movzx, vec![vreg32(5), vreg32(5)]),
            X86ISelInst::new(X86Opcode::TestRR, vec![vreg32(5), vreg32(5)]),
            X86ISelInst::new(
                X86Opcode::Jcc,
                vec![
                    X86ISelOperand::CondCode(X86CondCode::NE),
                    X86ISelOperand::Block(Block(1)),
                ],
            ),
            X86ISelInst::new(X86Opcode::Jmp, vec![X86ISelOperand::Block(Block(2))]),
        ]);
        let mut peephole = X86Peephole::default();
        assert!(peephole.run_on_function(&mut func));

        assert_eq!(
            entry_opcodes(&func),
            vec![X86Opcode::CmpRR, X86Opcode::Jcc, X86Opcode::Jmp],
        );
        assert_eq!(
            entry_insts(&func)[1].operands,
            vec![
                X86ISelOperand::CondCode(X86CondCode::L),
                X86ISelOperand::Block(Block(1)),
            ]
        );
    }

    #[test]
    fn cmp_branch_fusion_declines_when_bool_escapes_to_later_use() {
        // %D2 is read again after the Jcc; the bool is not dead -> refuse.
        let mut func = icmp_condbr_shape(X86CondCode::B, X86CondCode::NE);
        // Append an instruction that reads %6 (the normalized bool) after Jmp.
        func.push_inst(
            Block(0),
            X86ISelInst::new(
                X86Opcode::AddRI,
                vec![vreg(7), vreg(6), X86ISelOperand::Imm(1)],
            ),
        );
        let mut peephole = X86Peephole::default();
        peephole.run_on_function(&mut func);
        // CmpRR/Setcc must survive (no fusion).
        let opcodes = entry_opcodes(&func);
        assert!(opcodes.contains(&X86Opcode::Setcc));
    }

    #[test]
    fn cmp_branch_fusion_declines_when_flag_writer_not_full() {
        // ImulRR only partially overwrites flags -> the new Jcc cannot rely on
        // its RFLAGS, so the fusion must refuse.
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::ImulRR, vec![vreg(2), vreg(3)]),
            X86ISelInst::new(
                X86Opcode::Setcc,
                vec![vreg32(5), X86ISelOperand::CondCode(X86CondCode::E)],
            ),
            X86ISelInst::new(X86Opcode::Movzx, vec![vreg32(5), vreg32(5)]),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg32(5), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(
                X86Opcode::Jcc,
                vec![
                    X86ISelOperand::CondCode(X86CondCode::NE),
                    X86ISelOperand::Block(Block(1)),
                ],
            ),
            X86ISelInst::new(X86Opcode::Jmp, vec![X86ISelOperand::Block(Block(2))]),
        ]);
        let mut peephole = X86Peephole::default();
        peephole.run_on_function(&mut func);
        assert!(entry_opcodes(&func).contains(&X86Opcode::Setcc));
    }

    #[test]
    fn cmp_branch_fusion_preserves_proof_origin_on_new_jcc() {
        let mut func = icmp_condbr_shape(X86CondCode::A, X86CondCode::NE);
        // Tag the original Jcc with a proof origin.
        {
            let block = func.blocks.get_mut(&Block(0)).unwrap();
            let jcc_idx = block
                .insts
                .iter()
                .position(|i| i.opcode == X86Opcode::Jcc)
                .unwrap();
            block.insts[jcc_idx].proof_origin = Some(X86ProofOrigin::AtomicLoad);
        }
        let mut peephole = X86Peephole::default();
        assert!(peephole.run_on_function(&mut func));
        let insts = entry_insts(&func);
        let new_jcc = insts.iter().find(|i| i.opcode == X86Opcode::Jcc).unwrap();
        assert!(new_jcc.proof_origin.is_some());
    }

    // ===================================================================
    // SIB address-mode fold tests
    // ===================================================================

    fn mem_addr(base: X86ISelOperand, disp: i32) -> X86ISelOperand {
        X86ISelOperand::MemAddr {
            base: Box::new(base),
            disp,
        }
    }

    /// Canonical foldable STORE window (models a loop body):
    ///   imul v10, v1(index), 8      ; scaled = index*8
    ///   add  v11, v2(base), v10     ; addr = base + scaled
    ///   mov  [v11 + 0], v3          ; store  ->  MovMRSib [base+index*8], v3
    ///   cmp  v4, v5                 ; a later full-flag overwrite (loop cond)
    ///   ret
    /// The trailing CmpRR fully overwrites RFLAGS before the terminator, so the
    /// imul/add flags are provably dead — the same situation a real loop's
    /// compare-and-branch creates.
    fn foldable_store_window(scale_op: X86Opcode, scale_imm: i64) -> X86ISelFunction {
        make_func(vec![
            X86ISelInst::new(
                scale_op,
                vec![vreg(10), vreg(1), X86ISelOperand::Imm(scale_imm)],
            ),
            X86ISelInst::new(X86Opcode::AddRR, vec![vreg(11), vreg(2), vreg(10)]),
            X86ISelInst::new(X86Opcode::MovMR, vec![mem_addr(vreg(11), 0), vreg(3)]),
            X86ISelInst::new(X86Opcode::CmpRR, vec![vreg(4), vreg(5)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ])
    }

    #[test]
    fn sib_fold_imul_store() {
        let mut func = foldable_store_window(X86Opcode::ImulRRI, 8);
        assert!(sib_addr_fold_run_on_block(&mut func, Block(0)));
        let insts = entry_insts(&func);
        // imul + add erased; store rewritten to MovMRSib.
        assert_eq!(
            entry_opcodes(&func),
            vec![X86Opcode::MovMRSib, X86Opcode::CmpRR, X86Opcode::Ret]
        );
        match &insts[0].operands.as_slice() {
            [
                X86ISelOperand::SibMemAddr {
                    base,
                    index,
                    scale,
                    disp,
                },
                src,
            ] => {
                assert_eq!(base.as_ref(), &vreg(2), "base");
                assert_eq!(index.as_ref(), &vreg(1), "index");
                assert_eq!(*scale, 8, "scale");
                assert_eq!(*disp, 0, "disp");
                assert_eq!(src, &vreg(3), "stored value preserved");
            }
            other => panic!("unexpected operands: {other:?}"),
        }
    }

    fn sib_maps_view(maps: &SibFoldVRegMaps) -> (Vec<String>, Vec<String>, Vec<String>) {
        maps.canonical_view()
    }

    /// The incremental refresh `run_impl` applies after a SIB fold gives the
    /// maps a whole-function rebuild gives: the counts the fold moves, the
    /// mentioning-block sets of the VRegs it removes from its block (`v10`,
    /// `v11`), and those of VRegs another block also mentions (`v1`, `v3` in
    /// block 1). A refresh that leaves the maps as they were, or forgets the
    /// mention sets, fails here.
    #[test]
    fn sib_fold_maps_refresh_matches_rebuild() {
        let mut func = foldable_store_window(X86Opcode::ImulRRI, 8);
        func.ensure_block(Block(1));
        func.push_inst(
            Block(1),
            X86ISelInst::new(X86Opcode::AddRR, vec![vreg(12), vreg(1), vreg(3)]),
        );
        func.push_inst(Block(1), X86ISelInst::new(X86Opcode::Ret, vec![]));
        let mut maps = SibFoldVRegMaps::build(&func);
        let before = SibFoldBlockPart::of(&func, Block(0));
        let stale = sib_maps_view(&maps);
        assert!(sib_addr_fold_run_on_block_with_maps(
            &mut func,
            Block(0),
            &maps
        ));
        maps.replace_block_part(Block(0), &before, &SibFoldBlockPart::of(&func, Block(0)));
        let rebuilt = sib_maps_view(&SibFoldVRegMaps::build(&func));
        assert_ne!(
            stale, rebuilt,
            "the fold must change the maps for this test to bite"
        );
        assert_eq!(sib_maps_view(&maps), rebuilt);
    }

    #[test]
    fn sib_fold_imul_load() {
        // imul v10, v1, 4 ; add v11, v2, v10 ; mov v3, [v11] -> MovRMSib
        let mut func = make_func(vec![
            X86ISelInst::new(
                X86Opcode::ImulRRI,
                vec![vreg(10), vreg(1), X86ISelOperand::Imm(4)],
            ),
            X86ISelInst::new(X86Opcode::AddRR, vec![vreg(11), vreg(2), vreg(10)]),
            X86ISelInst::new(X86Opcode::MovRM, vec![vreg(3), mem_addr(vreg(11), 0)]),
            X86ISelInst::new(X86Opcode::CmpRR, vec![vreg(4), vreg(5)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(sib_addr_fold_run_on_block(&mut func, Block(0)));
        let insts = entry_insts(&func);
        assert_eq!(
            entry_opcodes(&func),
            vec![X86Opcode::MovRMSib, X86Opcode::CmpRR, X86Opcode::Ret]
        );
        match insts[0].operands.as_slice() {
            [
                dst,
                X86ISelOperand::SibMemAddr {
                    base,
                    index,
                    scale,
                    disp,
                },
            ] => {
                assert_eq!(dst, &vreg(3), "load dst preserved");
                assert_eq!(base.as_ref(), &vreg(2));
                assert_eq!(index.as_ref(), &vreg(1));
                assert_eq!(*scale, 4);
                assert_eq!(*disp, 0);
            }
            other => panic!("unexpected operands: {other:?}"),
        }
    }

    #[test]
    fn sib_fold_shl_store() {
        // shl v10, v1, 3 (=*8) folds identically to imul *8.
        let mut func = foldable_store_window(X86Opcode::ShlRI, 3);
        assert!(sib_addr_fold_run_on_block(&mut func, Block(0)));
        let insts = entry_insts(&func);
        assert_eq!(insts[0].opcode, X86Opcode::MovMRSib);
        if let X86ISelOperand::SibMemAddr { scale, index, .. } = &insts[0].operands[0] {
            assert_eq!(*scale, 8);
            assert_eq!(index.as_ref(), &vreg(1));
        } else {
            panic!("expected SibMemAddr");
        }
    }

    #[test]
    fn sib_fold_add_operands_commute() {
        // add v11, v10(scaled), v2(base) — scaled first. Must still fold and
        // pick v2 as base, v1 as index.
        let mut func = make_func(vec![
            X86ISelInst::new(
                X86Opcode::ImulRRI,
                vec![vreg(10), vreg(1), X86ISelOperand::Imm(8)],
            ),
            X86ISelInst::new(X86Opcode::AddRR, vec![vreg(11), vreg(10), vreg(2)]),
            X86ISelInst::new(X86Opcode::MovMR, vec![mem_addr(vreg(11), 0), vreg(3)]),
            X86ISelInst::new(X86Opcode::CmpRR, vec![vreg(4), vreg(5)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(sib_addr_fold_run_on_block(&mut func, Block(0)));
        let insts = entry_insts(&func);
        if let X86ISelOperand::SibMemAddr { base, index, .. } = &insts[0].operands[0] {
            assert_eq!(base.as_ref(), &vreg(2), "base is the non-scaled operand");
            assert_eq!(index.as_ref(), &vreg(1));
        } else {
            panic!("expected SibMemAddr");
        }
    }

    // ---- REFUTATION tests: unsound/unrecognized shapes must NOT fold ----

    /// scale 3 is not a legal x86 SIB scale. The PROPERTY is that no scale-3
    /// SIB is ever emitted and the `imul` computing the product SURVIVES —
    /// NOT that no fold happens at all.
    ///
    /// ⚑ This test used to assert the LIMIT (`!fired`, opcodes unchanged). The
    /// scale-1 arm legitimately folds this shape to `[base + product*1]`,
    /// keeping the imul and deleting only the add: same effective address, one
    /// fewer instruction. Re-scoped to the property it is actually defending.
    #[test]
    fn sib_refute_wrong_scale_3() {
        let mut func = foldable_store_window(X86Opcode::ImulRRI, 3);
        sib_addr_fold_run_on_block(&mut func, Block(0));
        let ops = entry_opcodes(&func);
        assert!(
            ops.contains(&X86Opcode::ImulRRI),
            "the imul computes the index and must NOT be deleted: {ops:?}"
        );
        for inst in entry_insts(&func) {
            for op in &inst.operands {
                if let X86ISelOperand::SibMemAddr { scale, .. } = op {
                    assert_eq!(*scale, 1, "illegal SIB scale emitted");
                }
            }
        }
    }

    /// The scale-1 arm on its canonical shape: `addr = base + index` with NO
    /// scale-def at all (a BYTE array indexes at scale 1). The add is deleted,
    /// the byte store carries `[base + index*1]`, and nothing else moves.
    #[test]
    fn sib_scale1_byte_store_folds() {
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::AddRR, vec![vreg(11), vreg(2), vreg(10)]),
            X86ISelInst::new(X86Opcode::MovMR8, vec![mem_addr(vreg(11), 0), vreg(3)]),
            X86ISelInst::new(X86Opcode::CmpRR, vec![vreg(4), vreg(5)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(sib_addr_fold_run_on_block(&mut func, Block(0)));
        assert_eq!(
            entry_opcodes(&func),
            vec![X86Opcode::MovMR8Sib, X86Opcode::CmpRR, X86Opcode::Ret]
        );
        let store = &entry_insts(&func)[0];
        match &store.operands[0] {
            X86ISelOperand::SibMemAddr {
                base,
                index,
                scale,
                disp,
            } => {
                assert_eq!(**base, vreg(2));
                assert_eq!(**index, vreg(10));
                assert_eq!(*scale, 1);
                assert_eq!(*disp, 0);
            }
            other => panic!("expected SibMemAddr, got {other:?}"),
        }
    }

    /// Byte LOAD sibling of the above.
    #[test]
    fn sib_scale1_byte_load_folds() {
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::AddRR, vec![vreg(11), vreg(2), vreg(10)]),
            X86ISelInst::new(X86Opcode::MovRM8, vec![vreg(3), mem_addr(vreg(11), 0)]),
            X86ISelInst::new(X86Opcode::CmpRR, vec![vreg(4), vreg(5)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(sib_addr_fold_run_on_block(&mut func, Block(0)));
        assert_eq!(
            entry_opcodes(&func),
            vec![X86Opcode::MovRM8Sib, X86Opcode::CmpRR, X86Opcode::Ret]
        );
    }

    /// REFUTE: an operand redefined between the add and the memory op means the
    /// SIB would read a DIFFERENT value than the deleted add did.
    #[test]
    fn sib_scale1_refute_index_redefined_before_use() {
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::AddRR, vec![vreg(11), vreg(2), vreg(10)]),
            // v10 redefined between the add and the store:
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(10), X86ISelOperand::Imm(7)]),
            X86ISelInst::new(X86Opcode::MovMR8, vec![mem_addr(vreg(11), 0), vreg(3)]),
            X86ISelInst::new(X86Opcode::CmpRR, vec![vreg(4), vreg(5)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(!sib_addr_fold_run_on_block(&mut func, Block(0)));
    }

    /// REFUTE: same, for the BASE operand.
    #[test]
    fn sib_scale1_refute_base_redefined_before_use() {
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::AddRR, vec![vreg(11), vreg(2), vreg(10)]),
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(2), X86ISelOperand::Imm(7)]),
            X86ISelInst::new(X86Opcode::MovMR8, vec![mem_addr(vreg(11), 0), vreg(3)]),
            X86ISelInst::new(X86Opcode::CmpRR, vec![vreg(4), vreg(5)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(!sib_addr_fold_run_on_block(&mut func, Block(0)));
    }

    /// REFUTE: the add's RFLAGS are read before being overwritten, so deleting
    /// the add would drop a flag definition someone depends on.
    #[test]
    fn sib_scale1_refute_live_flags() {
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::AddRR, vec![vreg(11), vreg(2), vreg(10)]),
            X86ISelInst::new(X86Opcode::MovMR8, vec![mem_addr(vreg(11), 0), vreg(3)]),
            // Reads the flags the add wrote, with no intervening full overwrite.
            X86ISelInst::new(
                X86Opcode::Jcc,
                vec![
                    X86ISelOperand::CondCode(X86CondCode::E),
                    X86ISelOperand::Block(Block(1)),
                ],
            ),
        ]);
        assert!(!sib_addr_fold_run_on_block(&mut func, Block(0)));
    }

    #[test]
    fn sib_refute_nonzero_disp() {
        // A non-zero displacement on the mov is not modeled by this fold
        // (the deleted add produced base+scaled+0, not +disp) -> no fold.
        let mut func = make_func(vec![
            X86ISelInst::new(
                X86Opcode::ImulRRI,
                vec![vreg(10), vreg(1), X86ISelOperand::Imm(8)],
            ),
            X86ISelInst::new(X86Opcode::AddRR, vec![vreg(11), vreg(2), vreg(10)]),
            X86ISelInst::new(X86Opcode::MovMR, vec![mem_addr(vreg(11), 16), vreg(3)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(!sib_addr_fold_run_on_block(&mut func, Block(0)));
    }

    /// scaled (v10) is used by the add AND by a second consumer. The PROPERTY
    /// is that the `imul` is NOT DELETED — dropping it would destroy the second
    /// use's value. Re-scoped from `!fired`: the scale-1 arm may legitimately
    /// fold the ADDRESS here (it keeps the imul and deletes only the add).
    #[test]
    fn sib_refute_scaled_used_twice() {
        let mut func = make_func(vec![
            X86ISelInst::new(
                X86Opcode::ImulRRI,
                vec![vreg(10), vreg(1), X86ISelOperand::Imm(8)],
            ),
            X86ISelInst::new(X86Opcode::AddRR, vec![vreg(11), vreg(2), vreg(10)]),
            // second use of scaled v10:
            X86ISelInst::new(X86Opcode::AddRR, vec![vreg(12), vreg(10), vreg(4)]),
            X86ISelInst::new(X86Opcode::MovMR, vec![mem_addr(vreg(11), 0), vreg(3)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        sib_addr_fold_run_on_block(&mut func, Block(0));
        let ops = entry_opcodes(&func);
        assert!(
            ops.contains(&X86Opcode::ImulRRI),
            "imul feeding a second consumer must survive: {ops:?}"
        );
        assert!(
            ops.contains(&X86Opcode::AddRR),
            "the second consumer's add must survive: {ops:?}"
        );
    }

    #[test]
    fn sib_refute_addr_used_twice() {
        // addr (v11) used by the store AND a later inst -> not single-use.
        let mut func = make_func(vec![
            X86ISelInst::new(
                X86Opcode::ImulRRI,
                vec![vreg(10), vreg(1), X86ISelOperand::Imm(8)],
            ),
            X86ISelInst::new(X86Opcode::AddRR, vec![vreg(11), vreg(2), vreg(10)]),
            X86ISelInst::new(X86Opcode::MovMR, vec![mem_addr(vreg(11), 0), vreg(3)]),
            // second use of addr v11:
            X86ISelInst::new(X86Opcode::AddRR, vec![vreg(12), vreg(11), vreg(4)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(!sib_addr_fold_run_on_block(&mut func, Block(0)));
    }

    #[test]
    fn sib_refute_add_flags_live() {
        // A flag-reader (Setcc) between the add and the terminator makes the
        // add's RFLAGS live -> deleting the add would change the flags the
        // Setcc consumes. Must NOT fold.
        let mut func = make_func(vec![
            X86ISelInst::new(
                X86Opcode::ImulRRI,
                vec![vreg(10), vreg(1), X86ISelOperand::Imm(8)],
            ),
            X86ISelInst::new(X86Opcode::AddRR, vec![vreg(11), vreg(2), vreg(10)]),
            X86ISelInst::new(X86Opcode::MovMR, vec![mem_addr(vreg(11), 0), vreg(3)]),
            X86ISelInst::new(
                X86Opcode::Setcc,
                vec![vreg32(5), X86ISelOperand::CondCode(X86CondCode::E)],
            ),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(!sib_addr_fold_run_on_block(&mut func, Block(0)));
    }

    #[test]
    fn sib_fold_partial_flag_overwrite_is_transparent() {
        // The matmul j-loop shape: another address's ImulRR (a PARTIAL flag
        // overwrite, no flag read) sits between the folded add and the next
        // FULL overwrite (AddRR). Nothing reads flags in between, so the
        // deleted imul/add flags are unobservable and the fold must fire.
        let mut func = make_func(vec![
            X86ISelInst::new(
                X86Opcode::ImulRRI,
                vec![vreg(10), vreg(1), X86ISelOperand::Imm(8)],
            ),
            X86ISelInst::new(X86Opcode::AddRR, vec![vreg(11), vreg(2), vreg(10)]),
            X86ISelInst::new(X86Opcode::MovRM, vec![vreg(3), mem_addr(vreg(11), 0)]),
            X86ISelInst::new(X86Opcode::ImulRR, vec![vreg(4), vreg(5), vreg(6)]),
            X86ISelInst::new(X86Opcode::AddRR, vec![vreg(7), vreg(8), vreg(9)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(sib_addr_fold_run_on_block(&mut func, Block(0)));
        assert_eq!(
            entry_opcodes(&func),
            vec![
                X86Opcode::MovRMSib,
                X86Opcode::ImulRR,
                X86Opcode::AddRR,
                X86Opcode::Ret
            ]
        );
    }

    #[test]
    fn sib_refute_partial_overwrite_then_flag_reader() {
        // A partial overwrite is transparent, but a flag READER after it
        // (before any full overwrite) can still observe surviving bits of
        // the deleted add's flags. Must NOT fold.
        let mut func = make_func(vec![
            X86ISelInst::new(
                X86Opcode::ImulRRI,
                vec![vreg(10), vreg(1), X86ISelOperand::Imm(8)],
            ),
            X86ISelInst::new(X86Opcode::AddRR, vec![vreg(11), vreg(2), vreg(10)]),
            X86ISelInst::new(X86Opcode::MovRM, vec![vreg(3), mem_addr(vreg(11), 0)]),
            X86ISelInst::new(X86Opcode::ImulRR, vec![vreg(4), vreg(5), vreg(6)]),
            X86ISelInst::new(
                X86Opcode::Setcc,
                vec![vreg32(7), X86ISelOperand::CondCode(X86CondCode::E)],
            ),
            X86ISelInst::new(X86Opcode::CmpRR, vec![vreg(8), vreg(9)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(!sib_addr_fold_run_on_block(&mut func, Block(0)));
    }

    #[test]
    fn sib_refute_partial_overwrite_then_block_end() {
        // A partial overwrite never PROVES deadness: with no full overwrite
        // before the end of the block the flags stay potentially live-out.
        // Must NOT fold.
        let mut func = make_func(vec![
            X86ISelInst::new(
                X86Opcode::ImulRRI,
                vec![vreg(10), vreg(1), X86ISelOperand::Imm(8)],
            ),
            X86ISelInst::new(X86Opcode::AddRR, vec![vreg(11), vreg(2), vreg(10)]),
            X86ISelInst::new(X86Opcode::MovMR, vec![mem_addr(vreg(11), 0), vreg(3)]),
            X86ISelInst::new(X86Opcode::ImulRR, vec![vreg(4), vreg(5), vreg(6)]),
        ]);
        assert!(!sib_addr_fold_run_on_block(&mut func, Block(0)));
    }

    #[test]
    fn sib_fold_end_to_end_const_copy_scale_via_run_impl() {
        // Integration pin of the matmul j-loop miss: the scale-8 reaches the
        // imul through a CSE-inserted single-def MovRR copy of a MovRI. The
        // imm-fold (which runs earlier in this same peephole invocation)
        // rewrites the ImulRR to ImulRRI $8, and the SIB fold then collapses
        // the triple: load rewritten to MovRMSib, imul+add+dead-copy erased.
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(0), X86ISelOperand::Imm(8)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(1), vreg(0)]),
            X86ISelInst::new(X86Opcode::ImulRR, vec![vreg(10), vreg(2), vreg(1)]),
            X86ISelInst::new(X86Opcode::AddRR, vec![vreg(11), vreg(3), vreg(10)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(12), vreg(11)]),
            X86ISelInst::new(X86Opcode::MovRM, vec![vreg(4), mem_addr(vreg(11), 0)]),
            X86ISelInst::new(X86Opcode::ImulRR, vec![vreg(5), vreg(4), vreg(6)]),
            X86ISelInst::new(X86Opcode::AddRR, vec![vreg(7), vreg(8), vreg(5)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(run_impl(&mut func, |_| false, |_, _, _| false, false));
        let opcodes = entry_opcodes(&func);
        assert!(
            opcodes.contains(&X86Opcode::MovRMSib),
            "expected a SIB load, got {opcodes:?}"
        );
        // The scale imul (folded to ImulRRI by the imm-fold, then consumed by
        // the SIB fold) and the address AddRR are erased; the unrelated
        // trailing value ImulRR/AddRR pair survives.
        assert!(
            !opcodes.contains(&X86Opcode::ImulRRI),
            "scale imul must be erased, got {opcodes:?}"
        );
        assert_eq!(
            opcodes.iter().filter(|op| **op == X86Opcode::AddRR).count(),
            1,
            "address add must be erased (value add survives), got {opcodes:?}"
        );
        let insts = entry_insts(&func);
        let sib = insts
            .iter()
            .find(|inst| inst.opcode == X86Opcode::MovRMSib)
            .expect("sib load present");
        match sib.operands.as_slice() {
            [
                dst,
                X86ISelOperand::SibMemAddr {
                    base,
                    index,
                    scale,
                    disp,
                },
            ] => {
                assert_eq!(dst, &vreg(4));
                assert_eq!(base.as_ref(), &vreg(3));
                assert_eq!(index.as_ref(), &vreg(2));
                assert_eq!(*scale, 8);
                assert_eq!(*disp, 0);
            }
            other => panic!("unexpected operands: {other:?}"),
        }
    }

    #[test]
    fn sib_refute_narrow_load() {
        // MovRM32 (32-bit load) is NOT the 64-bit MovRM; MovRMSib encodes a
        // 64-bit MOV only, so a narrow load must not fold.
        let mut func = make_func(vec![
            X86ISelInst::new(
                X86Opcode::ImulRRI,
                vec![vreg(10), vreg(1), X86ISelOperand::Imm(8)],
            ),
            X86ISelInst::new(X86Opcode::AddRR, vec![vreg(11), vreg(2), vreg(10)]),
            X86ISelInst::new(X86Opcode::MovRM32, vec![vreg32(3), mem_addr(vreg(11), 0)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(!sib_addr_fold_run_on_block(&mut func, Block(0)));
    }

    #[test]
    fn sib_refute_index_redefined_before_store() {
        // index v1 is redefined between the imul and the store -> the SIB
        // operand would read the NEW v1, not the value the imul scaled. No fold.
        let mut func = make_func(vec![
            X86ISelInst::new(
                X86Opcode::ImulRRI,
                vec![vreg(10), vreg(1), X86ISelOperand::Imm(8)],
            ),
            X86ISelInst::new(X86Opcode::AddRR, vec![vreg(11), vreg(2), vreg(10)]),
            // clobber index v1:
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(1), X86ISelOperand::Imm(99)]),
            X86ISelInst::new(X86Opcode::MovMR, vec![mem_addr(vreg(11), 0), vreg(3)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(!sib_addr_fold_run_on_block(&mut func, Block(0)));
    }

    /// scaled v10 is mentioned in ANOTHER block. The PROPERTY is that the
    /// `imul` defining it is NOT DELETED — the other block reads that value.
    /// Re-scoped from `!fired` for the same reason as the two tests above.
    #[test]
    fn sib_refute_scaled_escapes_block() {
        let mut func = foldable_store_window(X86Opcode::ImulRRI, 8);
        func.ensure_block(Block(1));
        func.block_order.push(Block(1));
        func.push_inst(
            Block(1),
            X86ISelInst::new(X86Opcode::AddRR, vec![vreg(12), vreg(10), vreg(4)]),
        );
        sib_addr_fold_run_on_block(&mut func, Block(0));
        let ops = entry_opcodes(&func);
        assert!(
            ops.contains(&X86Opcode::ImulRRI),
            "imul whose result escapes the block must survive: {ops:?}"
        );
    }

    #[test]
    fn sib_fold_end_to_end_via_run_impl() {
        // The full peephole entrypoint fires the fold at its scheduled slot.
        let mut func = foldable_store_window(X86Opcode::ImulRRI, 8);
        let mut peephole = X86Peephole::default();
        assert!(peephole.run_on_function(&mut func));
        assert!(entry_opcodes(&func).contains(&X86Opcode::MovMRSib));
        assert!(!entry_opcodes(&func).contains(&X86Opcode::ImulRRI));
    }

    #[test]
    fn sib_fold_shared_addr_load_and_store() {
        // The matmul `c[j] = c[j] + ..` shape: ONE address feeds a LOAD then a
        // STORE. addr (v11) is used TWICE (load base + store base). Both fold to
        // SIB sharing base+index*8, and the single imul+add is deleted once.
        //   imul v10, v1, 8
        //   add  v11, v2, v10        ; addr = base + index*8
        //   mov  v3, [v11]           ; LOAD  c[j]        -> MovRMSib
        //   ... (v3 combined into v6) ...
        //   mov  [v11], v6           ; STORE c[j]        -> MovMRSib
        //   cmp  v4, v5              ; full-flag overwrite before terminator
        //   ret
        let mut func = make_func(vec![
            X86ISelInst::new(
                X86Opcode::ImulRRI,
                vec![vreg(10), vreg(1), X86ISelOperand::Imm(8)],
            ),
            X86ISelInst::new(X86Opcode::AddRR, vec![vreg(11), vreg(2), vreg(10)]),
            X86ISelInst::new(X86Opcode::MovRM, vec![vreg(3), mem_addr(vreg(11), 0)]),
            X86ISelInst::new(X86Opcode::AddRR, vec![vreg(6), vreg(3), vreg(7)]),
            X86ISelInst::new(X86Opcode::MovMR, vec![mem_addr(vreg(11), 0), vreg(6)]),
            X86ISelInst::new(X86Opcode::CmpRR, vec![vreg(4), vreg(5)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(sib_addr_fold_run_on_block(&mut func, Block(0)));
        let ops = entry_opcodes(&func);
        // imul + address-add erased; the intermediate value-add (v6) survives.
        assert!(!ops.contains(&X86Opcode::ImulRRI), "imul erased");
        assert_eq!(
            ops,
            vec![
                X86Opcode::MovRMSib, // folded load
                X86Opcode::AddRR,    // value add (v6 = v3 + v7) survives
                X86Opcode::MovMRSib, // folded store
                X86Opcode::CmpRR,
                X86Opcode::Ret,
            ]
        );
        // Load-before-store order preserved.
        let insts = entry_insts(&func);
        assert!(insts[0].opcode == X86Opcode::MovRMSib);
        assert!(insts[2].opcode == X86Opcode::MovMRSib);
        // Both share base=v2, index=v1, scale=8.
        for (idx, want_load) in [(0usize, true), (2usize, false)] {
            let sib_op = if want_load {
                &insts[idx].operands[1]
            } else {
                &insts[idx].operands[0]
            };
            match sib_op {
                X86ISelOperand::SibMemAddr {
                    base,
                    index,
                    scale,
                    disp,
                } => {
                    assert_eq!(base.as_ref(), &vreg(2));
                    assert_eq!(index.as_ref(), &vreg(1));
                    assert_eq!(*scale, 8);
                    assert_eq!(*disp, 0);
                }
                other => panic!("op {idx} not SIB: {other:?}"),
            }
        }
    }

    fn sib_op(base: u32, index: u32, scale: u8, disp: i32) -> X86ISelOperand {
        X86ISelOperand::SibMemAddr {
            base: Box::new(vreg(base)),
            index: Box::new(vreg(index)),
            scale,
            disp,
        }
    }

    #[test]
    fn sib_fold_from_leasib_load() {
        // The array-indexing shape: select_array_gep emits LeaSib, the element
        // load reads [addr]. Fold to MovRMSib carrying the LeaSib's SIB operand;
        // the LeaSib dies.
        //   lea v11, [v2 + v1*8]      ; LeaSib
        //   mov v3, [v11]             ; load  -> MovRMSib v3, [v2+v1*8]
        //   cmp v4, v5 ; ret
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::LeaSib, vec![vreg(11), sib_op(2, 1, 8, 0)]),
            X86ISelInst::new(X86Opcode::MovRM, vec![vreg(3), mem_addr(vreg(11), 0)]),
            X86ISelInst::new(X86Opcode::CmpRR, vec![vreg(4), vreg(5)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(sib_addr_fold_run_on_block(&mut func, Block(0)));
        assert_eq!(
            entry_opcodes(&func),
            vec![X86Opcode::MovRMSib, X86Opcode::CmpRR, X86Opcode::Ret]
        );
        if let X86ISelOperand::SibMemAddr {
            base,
            index,
            scale,
            disp,
        } = &entry_insts(&func)[0].operands[1]
        {
            assert_eq!(base.as_ref(), &vreg(2));
            assert_eq!(index.as_ref(), &vreg(1));
            assert_eq!(*scale, 8);
            assert_eq!(*disp, 0);
        } else {
            panic!("expected SibMemAddr");
        }
    }

    /// The full pass reaches a block whose only SIB-fold anchor is a `LeaSib`
    /// (the SIB loop skips blocks with neither a `LeaSib` nor an `AddRR`).
    /// Fails when `LeaSib` is missing from that block filter.
    #[test]
    fn sib_fold_from_leasib_load_via_run_impl() {
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::LeaSib, vec![vreg(11), sib_op(2, 1, 8, 0)]),
            X86ISelInst::new(X86Opcode::MovRM, vec![vreg(3), mem_addr(vreg(11), 0)]),
            X86ISelInst::new(X86Opcode::CmpRR, vec![vreg(4), vreg(5)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(run_impl(&mut func, |_| false, |_, _, _| false, false));
        let opcodes = entry_opcodes(&func);
        assert!(opcodes.contains(&X86Opcode::MovRMSib), "{opcodes:?}");
        assert!(!opcodes.contains(&X86Opcode::LeaSib), "{opcodes:?}");
    }

    #[test]
    fn sib_fold_from_leasib_shared_load_store_with_disp() {
        // LeaSib with a non-zero disp feeding a shared load+store (the matmul
        // `c[i] = c[i] + ..` shape). Disp is preserved exactly.
        //   lea v11, [v2 + v1*4 + 16]
        //   mov v3, [v11]     ; LOAD  -> MovRMSib
        //   add v6, v3, v7
        //   mov [v11], v6     ; STORE -> MovMRSib
        //   cmp v4, v5 ; ret
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::LeaSib, vec![vreg(11), sib_op(2, 1, 4, 16)]),
            X86ISelInst::new(X86Opcode::MovRM, vec![vreg(3), mem_addr(vreg(11), 0)]),
            X86ISelInst::new(X86Opcode::AddRR, vec![vreg(6), vreg(3), vreg(7)]),
            X86ISelInst::new(X86Opcode::MovMR, vec![mem_addr(vreg(11), 0), vreg(6)]),
            X86ISelInst::new(X86Opcode::CmpRR, vec![vreg(4), vreg(5)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(sib_addr_fold_run_on_block(&mut func, Block(0)));
        let insts = entry_insts(&func);
        assert_eq!(insts[0].opcode, X86Opcode::MovRMSib);
        assert_eq!(insts[2].opcode, X86Opcode::MovMRSib);
        // Disp 16 preserved on both.
        for (idx, want_load) in [(0usize, true), (2usize, false)] {
            let op = if want_load {
                &insts[idx].operands[1]
            } else {
                &insts[idx].operands[0]
            };
            if let X86ISelOperand::SibMemAddr { scale, disp, .. } = op {
                assert_eq!(*scale, 4);
                assert_eq!(*disp, 16, "disp preserved");
            } else {
                panic!("expected SibMemAddr");
            }
        }
    }

    #[test]
    fn sib_fold_from_leasib_packed_v128_store_and_load() {
        // THE `v2_memfill` VECTOR-BODY SHAPE. The vectorizer emits
        //   lea  v11, [v2 + v1*1]     ; LeaSib (base + iv)
        //   movdqu [v11], x20         ; 16-byte packed store
        // and the packed store previously had no SIB form at all, so the LeaSib
        // survived into the hot loop. It must now fold to one MovdquMRSib
        // carrying the LeaSib's SIB operand, with the LeaSib deleted. The
        // matching LOAD direction (v1_saxpy's `movdqu x,[px]`) folds the same way.
        let x128 = |id: u32| vreg_class(id, RegClass::Fpr128);
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::LeaSib, vec![vreg(11), sib_op(2, 1, 1, 0)]),
            X86ISelInst::new(X86Opcode::MovdquMR, vec![mem_addr(vreg(11), 0), x128(20)]),
            X86ISelInst::new(X86Opcode::LeaSib, vec![vreg(12), sib_op(3, 1, 4, 16)]),
            X86ISelInst::new(X86Opcode::MovdquRM, vec![x128(21), mem_addr(vreg(12), 0)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(sib_addr_fold_run_on_block(&mut func, Block(0)));
        assert_eq!(
            entry_opcodes(&func),
            vec![
                X86Opcode::MovdquMRSib,
                X86Opcode::MovdquRMSib,
                X86Opcode::Ret
            ]
        );
        let insts = entry_insts(&func);
        // Store: [SibMemAddr, value]; scale 1 / disp 0 preserved, value intact.
        if let X86ISelOperand::SibMemAddr {
            base,
            index,
            scale,
            disp,
        } = &insts[0].operands[0]
        {
            assert_eq!(base.as_ref(), &vreg(2));
            assert_eq!(index.as_ref(), &vreg(1));
            assert_eq!(*scale, 1);
            assert_eq!(*disp, 0);
        } else {
            panic!("expected SibMemAddr on the packed store");
        }
        assert_eq!(insts[0].operands[1], x128(20));
        // Load: [value, SibMemAddr]; scale 4 / disp 16 preserved exactly.
        assert_eq!(insts[1].operands[0], x128(21));
        if let X86ISelOperand::SibMemAddr { scale, disp, .. } = &insts[1].operands[1] {
            assert_eq!(*scale, 4);
            assert_eq!(*disp, 16);
        } else {
            panic!("expected SibMemAddr on the packed load");
        }
    }

    #[test]
    fn sib_fold_refuses_aligned_movdqa_packed_moves() {
        // MOVDQA's proof carries the honest `ea % 16 == 0` precondition, and this
        // fold does not know that base+index*scale stays 16-aligned. There is
        // deliberately no MovdqaRMSib/MovdqaMRSib to fold into, and
        // `sib_foldable_mem_op` must decline both directions rather than
        // silently re-route an aligned move onto the unaligned opcode.
        let x128 = |id: u32| vreg_class(id, RegClass::Fpr128);
        let load = X86ISelInst::new(X86Opcode::MovdqaRM, vec![x128(20), mem_addr(vreg(2), 0)]);
        let store = X86ISelInst::new(X86Opcode::MovdqaMR, vec![mem_addr(vreg(2), 0), x128(20)]);
        assert!(
            sib_foldable_mem_op(&load).is_none(),
            "MovdqaRM must not fold"
        );
        assert!(
            sib_foldable_mem_op(&store).is_none(),
            "MovdqaMR must not fold"
        );
        // Volatile packed moves keep their stronger ordering proof and must also
        // decline (they carry different default flags AND a different opcode).
        let vol = X86ISelInst::new(
            X86Opcode::VolatileMovdquMR,
            vec![mem_addr(vreg(2), 0), x128(20)],
        );
        assert!(
            sib_foldable_mem_op(&vol).is_none(),
            "VolatileMovdquMR must not fold into a plain SIB store"
        );
    }

    #[test]
    fn sib_refute_leasib_addr_escapes_arithmetic() {
        // LeaSib address also feeds an arithmetic add -> cannot delete the lea.
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::LeaSib, vec![vreg(11), sib_op(2, 1, 8, 0)]),
            X86ISelInst::new(X86Opcode::MovMR, vec![mem_addr(vreg(11), 0), vreg(3)]),
            X86ISelInst::new(X86Opcode::AddRR, vec![vreg(12), vreg(11), vreg(4)]),
            X86ISelInst::new(X86Opcode::CmpRR, vec![vreg(5), vreg(6)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(!sib_addr_fold_run_on_block(&mut func, Block(0)));
    }

    #[test]
    fn sib_refute_leasib_base_redefined() {
        // base v2 redefined between the lea and the store -> the SIB operand
        // would read the NEW v2. No fold.
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::LeaSib, vec![vreg(11), sib_op(2, 1, 8, 0)]),
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(2), X86ISelOperand::Imm(99)]),
            X86ISelInst::new(X86Opcode::MovMR, vec![mem_addr(vreg(11), 0), vreg(3)]),
            X86ISelInst::new(X86Opcode::CmpRR, vec![vreg(5), vreg(6)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(!sib_addr_fold_run_on_block(&mut func, Block(0)));
    }

    #[test]
    fn sib_fold_through_movrr_copy() {
        // Two-address-fixup artifact: the AddRR result (v11) is COPIED via
        // MovRR to v12, and v12 is the store base. The fold must see through the
        // copy: rewrite the store to SIB base+index*8 and delete imul+add+copy.
        //   imul v10, v1, 8
        //   add  v11, v2, v10
        //   mov  v12, v11        ; MovRR copy of the address
        //   mov  [v12], v3       ; store via the copy
        //   cmp  v4, v5
        //   ret
        let mut func = make_func(vec![
            X86ISelInst::new(
                X86Opcode::ImulRRI,
                vec![vreg(10), vreg(1), X86ISelOperand::Imm(8)],
            ),
            X86ISelInst::new(X86Opcode::AddRR, vec![vreg(11), vreg(2), vreg(10)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(12), vreg(11)]),
            X86ISelInst::new(X86Opcode::MovMR, vec![mem_addr(vreg(12), 0), vreg(3)]),
            X86ISelInst::new(X86Opcode::CmpRR, vec![vreg(4), vreg(5)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(sib_addr_fold_run_on_block(&mut func, Block(0)));
        let ops = entry_opcodes(&func);
        assert_eq!(
            ops,
            vec![X86Opcode::MovMRSib, X86Opcode::CmpRR, X86Opcode::Ret],
            "imul+add+copy erased, store -> MovMRSib"
        );
        if let X86ISelOperand::SibMemAddr {
            base, index, scale, ..
        } = &entry_insts(&func)[0].operands[0]
        {
            assert_eq!(base.as_ref(), &vreg(2));
            assert_eq!(index.as_ref(), &vreg(1));
            assert_eq!(*scale, 8);
        } else {
            panic!("expected SibMemAddr");
        }
    }

    #[test]
    fn sib_fold_with_dead_addr_copy() {
        // The exact ISel shape seen in the wild: the AddRR address (v11) is used
        // by a DEAD MovRR copy (v12 unused) AND directly by the load. The dead
        // copy must be deleted and the load folded.
        //   imul v10, v1, 8
        //   add  v11, v2, v10
        //   mov  v12, v11        ; DEAD copy (v12 never used)
        //   mov  v3, [v11]       ; load via addr directly -> MovRMSib
        //   cmp v4, v5 ; ret
        let mut func = make_func(vec![
            X86ISelInst::new(
                X86Opcode::ImulRRI,
                vec![vreg(10), vreg(1), X86ISelOperand::Imm(8)],
            ),
            X86ISelInst::new(X86Opcode::AddRR, vec![vreg(11), vreg(2), vreg(10)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(12), vreg(11)]), // dead
            X86ISelInst::new(X86Opcode::MovRM, vec![vreg(3), mem_addr(vreg(11), 0)]),
            X86ISelInst::new(X86Opcode::CmpRR, vec![vreg(4), vreg(5)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(sib_addr_fold_run_on_block(&mut func, Block(0)));
        // imul + add + dead copy erased; load -> MovRMSib.
        assert_eq!(
            entry_opcodes(&func),
            vec![X86Opcode::MovRMSib, X86Opcode::CmpRR, X86Opcode::Ret]
        );
    }

    #[test]
    fn sib_refute_copy_used_in_arithmetic() {
        // The copy dest v12 is used by the store AND by arithmetic -> the copy
        // is not purely an address, so we must not delete it. No fold.
        let mut func = make_func(vec![
            X86ISelInst::new(
                X86Opcode::ImulRRI,
                vec![vreg(10), vreg(1), X86ISelOperand::Imm(8)],
            ),
            X86ISelInst::new(X86Opcode::AddRR, vec![vreg(11), vreg(2), vreg(10)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(12), vreg(11)]),
            X86ISelInst::new(X86Opcode::MovMR, vec![mem_addr(vreg(12), 0), vreg(3)]),
            X86ISelInst::new(X86Opcode::AddRR, vec![vreg(13), vreg(12), vreg(4)]),
            X86ISelInst::new(X86Opcode::CmpRR, vec![vreg(6), vreg(7)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(!sib_addr_fold_run_on_block(&mut func, Block(0)));
    }

    #[test]
    fn sib_refute_addr_used_in_arithmetic() {
        // addr (v11) feeds a store AND an arithmetic ADD (escapes into a value).
        // Deleting the address-add would drop the arithmetic use -> must NOT
        // fold (not every use of addr is a foldable mem op).
        let mut func = make_func(vec![
            X86ISelInst::new(
                X86Opcode::ImulRRI,
                vec![vreg(10), vreg(1), X86ISelOperand::Imm(8)],
            ),
            X86ISelInst::new(X86Opcode::AddRR, vec![vreg(11), vreg(2), vreg(10)]),
            X86ISelInst::new(X86Opcode::MovMR, vec![mem_addr(vreg(11), 0), vreg(3)]),
            // arithmetic use of the address value:
            X86ISelInst::new(X86Opcode::AddRR, vec![vreg(12), vreg(11), vreg(4)]),
            X86ISelInst::new(X86Opcode::CmpRR, vec![vreg(6), vreg(7)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(!sib_addr_fold_run_on_block(&mut func, Block(0)));
    }

    // -----------------------------------------------------------------------
    // Local address-chain fold (TCG_X86_ADDR_CHAIN_FOLD) — called directly,
    // bypassing the env gate.
    // -----------------------------------------------------------------------

    fn mem(base: u32, disp: i32) -> X86ISelOperand {
        X86ISelOperand::MemAddr {
            base: Box::new(vreg(base)),
            disp,
        }
    }

    #[test]
    fn addr_chain_fold_three_op_addri_to_disp() {
        // AddRI v2, v1, 0x10 ; MovRM v3, [v2+0]  ->  MovRM v3, [v1+0x10]
        let mut func = make_func(vec![
            X86ISelInst::new(
                X86Opcode::AddRI,
                vec![vreg(2), vreg(1), X86ISelOperand::Imm(0x10)],
            ),
            X86ISelInst::new(X86Opcode::MovRM, vec![vreg(3), mem(2, 0)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(addr_chain_fold_run_on_block(&mut func, Block(0)));
        let insts = entry_insts(&func);
        assert_eq!(insts[1].opcode, X86Opcode::MovRM);
        assert_eq!(insts[1].operands, vec![vreg(3), mem(1, 0x10)]);
        // Rewrite-only: the AddRI stays (DCE owns the sweep).
        assert_eq!(insts[0].opcode, X86Opcode::AddRI);
    }

    #[test]
    fn addr_chain_fold_tied_addri_through_copy() {
        // MovRR v2, v1 ; AddRI v2, 0x20 (tied) ; MovRM v3, [v2+4]
        //   ->  MovRM v3, [v1+0x24]
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(2), vreg(1)]),
            X86ISelInst::new(X86Opcode::AddRI, vec![vreg(2), X86ISelOperand::Imm(0x20)]),
            X86ISelInst::new(X86Opcode::MovRM, vec![vreg(3), mem(2, 4)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(addr_chain_fold_run_on_block(&mut func, Block(0)));
        assert_eq!(entry_insts(&func)[2].operands, vec![vreg(3), mem(1, 0x24)]);
    }

    #[test]
    fn addr_chain_fold_addrr_becomes_sib_index() {
        // AddRR v4, v1, v2 ; MovRM v3, [v4+8]
        //   ->  MovRMSib v3, [v1 + v2*1 + 8]
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::AddRR, vec![vreg(4), vreg(1), vreg(2)]),
            X86ISelInst::new(X86Opcode::MovRM, vec![vreg(3), mem(4, 8)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(addr_chain_fold_run_on_block(&mut func, Block(0)));
        let insts = entry_insts(&func);
        assert_eq!(insts[1].opcode, X86Opcode::MovRMSib);
        assert_eq!(
            insts[1].operands,
            vec![
                vreg(3),
                X86ISelOperand::SibMemAddr {
                    base: Box::new(vreg(1)),
                    index: Box::new(vreg(2)),
                    scale: 1,
                    disp: 8,
                },
            ]
        );
    }

    #[test]
    fn addr_chain_fold_b05_two_level_shape() {
        // The exact post-unroll b05 a-side shape:
        //   AddRR v5, v1, v2      (row base = r15 + rdi)
        //   MovRR v6, v5
        //   AddRI v6, 0x10        (tied: += k*8)
        //   MovRM v7, [v6+0]
        // -> MovRMSib v7, [v1 + v2*1 + 0x10]
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::AddRR, vec![vreg(5), vreg(1), vreg(2)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(6), vreg(5)]),
            X86ISelInst::new(X86Opcode::AddRI, vec![vreg(6), X86ISelOperand::Imm(0x10)]),
            X86ISelInst::new(X86Opcode::MovRM, vec![vreg(7), mem(6, 0)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(addr_chain_fold_run_on_block(&mut func, Block(0)));
        assert_eq!(
            entry_insts(&func)[3].operands,
            vec![
                vreg(7),
                X86ISelOperand::SibMemAddr {
                    base: Box::new(vreg(1)),
                    index: Box::new(vreg(2)),
                    scale: 1,
                    disp: 0x10,
                },
            ]
        );
    }

    #[test]
    fn addr_chain_fold_store_anchor() {
        // AddRI v2, v1, 8 ; MovMR [v2+0], v3  ->  MovMR [v1+8], v3
        let mut func = make_func(vec![
            X86ISelInst::new(
                X86Opcode::AddRI,
                vec![vreg(2), vreg(1), X86ISelOperand::Imm(8)],
            ),
            X86ISelInst::new(X86Opcode::MovMR, vec![mem(2, 0), vreg(3)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(addr_chain_fold_run_on_block(&mut func, Block(0)));
        assert_eq!(entry_insts(&func)[1].operands, vec![mem(1, 8), vreg(3)]);
    }

    #[test]
    fn addr_chain_fold_refuses_base_redef_in_window() {
        // The final base v1 is redefined between the chain and the load:
        // folding would read the NEW v1. Must refuse.
        let mut func = make_func(vec![
            X86ISelInst::new(
                X86Opcode::AddRI,
                vec![vreg(2), vreg(1), X86ISelOperand::Imm(8)],
            ),
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(1), X86ISelOperand::Imm(99)]),
            X86ISelInst::new(X86Opcode::MovRM, vec![vreg(3), mem(2, 0)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(!addr_chain_fold_run_on_block(&mut func, Block(0)));
    }

    #[test]
    fn addr_chain_fold_refuses_narrow_alias_redef_in_window() {
        // A Gpr32 def of the same id is an aliased width view: must count as
        // a redef of the 64-bit base (dirty-high-bits class).
        let mut func = make_func(vec![
            X86ISelInst::new(
                X86Opcode::AddRI,
                vec![vreg(2), vreg(1), X86ISelOperand::Imm(8)],
            ),
            X86ISelInst::new(
                X86Opcode::MovRI,
                vec![vreg_class(1, RegClass::Gpr32), X86ISelOperand::Imm(7)],
            ),
            X86ISelInst::new(X86Opcode::MovRM, vec![vreg(3), mem(2, 0)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(!addr_chain_fold_run_on_block(&mut func, Block(0)));
    }

    #[test]
    fn addr_chain_fold_second_addrr_partial_fold() {
        // Two AddRRs: only the nearest becomes the index; the second
        // terminates resolution with its def as the base (partial fold).
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::AddRR, vec![vreg(4), vreg(1), vreg(2)]),
            X86ISelInst::new(X86Opcode::AddRR, vec![vreg(5), vreg(4), vreg(3)]),
            X86ISelInst::new(X86Opcode::MovRM, vec![vreg(6), mem(5, 0)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(addr_chain_fold_run_on_block(&mut func, Block(0)));
        assert_eq!(
            entry_insts(&func)[2].operands,
            vec![
                vreg(6),
                X86ISelOperand::SibMemAddr {
                    base: Box::new(vreg(4)),
                    index: Box::new(vreg(3)),
                    scale: 1,
                    disp: 0,
                },
            ]
        );
    }

    #[test]
    fn addr_chain_fold_uses_nearest_def() {
        // Multi-def id (post-unroll clone shape): the NEAREST def wins.
        let mut func = make_func(vec![
            X86ISelInst::new(
                X86Opcode::AddRI,
                vec![vreg(2), vreg(1), X86ISelOperand::Imm(8)],
            ),
            X86ISelInst::new(
                X86Opcode::AddRI,
                vec![vreg(2), vreg(1), X86ISelOperand::Imm(16)],
            ),
            X86ISelInst::new(X86Opcode::MovRM, vec![vreg(3), mem(2, 0)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(addr_chain_fold_run_on_block(&mut func, Block(0)));
        assert_eq!(entry_insts(&func)[2].operands, vec![vreg(3), mem(1, 16)]);
    }

    fn lea_link(dst: X86ISelOperand, base: X86ISelOperand, disp: i32) -> X86ISelInst {
        X86ISelInst::new(
            X86Opcode::Lea,
            vec![
                dst,
                X86ISelOperand::MemAddr {
                    base: Box::new(base),
                    disp,
                },
            ],
        )
    }

    #[test]
    fn addr_chain_fold_lea_displacement_link_folds_for_load_and_store() {
        // Lea v2, [v1+0x18] ; MovRM v3, [v2+0]   ->  MovRM v3, [v1+0x18]
        // Lea v4, [v1-8]    ; MovMR [v4+4], v3   ->  MovMR [v1-4], v3
        let mut func = make_func(vec![
            lea_link(vreg(2), vreg(1), 0x18),
            X86ISelInst::new(X86Opcode::MovRM, vec![vreg(3), mem(2, 0)]),
            lea_link(vreg(4), vreg(1), -8),
            X86ISelInst::new(X86Opcode::MovMR, vec![mem(4, 4), vreg(3)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(addr_chain_fold_run_on_block(&mut func, Block(0)));
        let insts = entry_insts(&func);
        assert_eq!(insts[1].opcode, X86Opcode::MovRM);
        assert_eq!(insts[1].operands, vec![vreg(3), mem(1, 0x18)]);
        assert_eq!(insts[3].opcode, X86Opcode::MovMR);
        assert_eq!(insts[3].operands, vec![mem(1, -4), vreg(3)]);
        // Rewrite-only: both Leas stay for DCE.
        assert_eq!(insts[0].opcode, X86Opcode::Lea);
        assert_eq!(insts[2].opcode, X86Opcode::Lea);
    }

    #[test]
    fn addr_chain_fold_lea_link_refuses_base_redef_in_window() {
        // v1 is redefined between the Lea and the load, at full width and
        // through a Gpr32 view of the same id. Folding would read the new v1.
        for redef in [vreg(1), vreg_class(1, RegClass::Gpr32)] {
            let mut func = make_func(vec![
                lea_link(vreg(2), vreg(1), 8),
                X86ISelInst::new(X86Opcode::MovRI, vec![redef, X86ISelOperand::Imm(99)]),
                X86ISelInst::new(X86Opcode::MovRM, vec![vreg(3), mem(2, 0)]),
                X86ISelInst::new(X86Opcode::Ret, vec![]),
            ]);
            assert!(!addr_chain_fold_run_on_block(&mut func, Block(0)));
        }
    }

    #[test]
    fn addr_chain_fold_lea_link_requires_gpr64_register_base_and_dest() {
        // A stack-slot base is not a register link.
        let mut func = make_func(vec![
            lea_link(vreg(2), X86ISelOperand::StackSlot(0), 8),
            X86ISelInst::new(X86Opcode::MovRM, vec![vreg(3), mem(2, 0)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(!addr_chain_fold_run_on_block(&mut func, Block(0)));

        // A Gpr32 base register is not a 64-bit address source.
        let mut func = make_func(vec![
            lea_link(vreg(2), vreg_class(1, RegClass::Gpr32), 8),
            X86ISelInst::new(X86Opcode::MovRM, vec![vreg(3), mem(2, 0)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(!addr_chain_fold_run_on_block(&mut func, Block(0)));

        // A Gpr32 Lea result is a narrow view of v2, not the address read.
        let mut func = make_func(vec![
            lea_link(vreg_class(2, RegClass::Gpr32), vreg(1), 8),
            X86ISelInst::new(X86Opcode::MovRM, vec![vreg(3), mem(2, 0)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(!addr_chain_fold_run_on_block(&mut func, Block(0)));
    }

    #[test]
    fn addr_chain_fold_lea_link_refuses_disp_overflow_and_non_default_flags() {
        let mut func = make_func(vec![
            lea_link(vreg(2), vreg(1), i32::MAX),
            X86ISelInst::new(X86Opcode::MovRM, vec![vreg(3), mem(2, 8)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(!addr_chain_fold_run_on_block(&mut func, Block(0)));

        // A link whose flags differ from the opcode default is not classified.
        let mut flagged = lea_link(vreg(2), vreg(1), 8);
        flagged.flags = X86Opcode::MovMR.default_flags();
        assert_ne!(flagged.flags, X86Opcode::Lea.default_flags());
        let mut func = make_func(vec![
            flagged,
            X86ISelInst::new(X86Opcode::MovRM, vec![vreg(3), mem(2, 0)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(!addr_chain_fold_run_on_block(&mut func, Block(0)));
    }

    fn sib_operand(
        base: X86ISelOperand,
        index: X86ISelOperand,
        scale: u8,
        disp: i32,
    ) -> X86ISelOperand {
        X86ISelOperand::SibMemAddr {
            base: Box::new(base),
            index: Box::new(index),
            scale,
            disp,
        }
    }

    fn movri(dst: X86ISelOperand, value: i64) -> X86ISelInst {
        X86ISelInst::new(X86Opcode::MovRI, vec![dst, X86ISelOperand::Imm(value)])
    }

    /// `prefix` (which defines the index v2), then
    /// `MovRMSib v3, [v1 + v2*scale + disp]`, then `Ret`. Runs the
    /// constant-index fold and returns the load as it stands afterwards.
    fn const_index_load(prefix: Vec<X86ISelInst>, scale: u8, disp: i32) -> (bool, X86ISelInst) {
        let load_idx = prefix.len();
        let mut insts = prefix;
        insts.push(X86ISelInst::new(
            X86Opcode::MovRMSib,
            vec![vreg(3), sib_operand(vreg(1), vreg(2), scale, disp)],
        ));
        insts.push(X86ISelInst::new(X86Opcode::Ret, vec![]));
        let mut func = make_func(insts);
        let changed = sib_const_index_fold_run_on_block(&mut func, Block(0));
        (changed, entry_insts(&func)[load_idx].clone())
    }

    #[test]
    fn sib_const_index_fold_rewrites_every_anchor_form_to_base_plus_disp() {
        // mov v2, 3 ; <op> [v1 + v2*8 + 16]  ->  <op> [v1 + 40]
        let cases = [
            (X86Opcode::MovRMSib, X86Opcode::MovRM, true, vreg(3)),
            (X86Opcode::MovMRSib, X86Opcode::MovMR, false, vreg(3)),
            (X86Opcode::MovRM32Sib, X86Opcode::MovRM32, true, vreg32(3)),
            (X86Opcode::MovMR32Sib, X86Opcode::MovMR32, false, vreg32(3)),
        ];
        for (sib_opcode, plain_opcode, is_load, value) in cases {
            let addr = sib_operand(vreg(1), vreg(2), 8, 16);
            let operands = if is_load {
                vec![value.clone(), addr]
            } else {
                vec![addr, value.clone()]
            };
            let anchor = X86ISelInst::new(sib_opcode, operands);
            let mut func = make_func(vec![
                movri(vreg(2), 3),
                anchor,
                X86ISelInst::new(X86Opcode::Ret, vec![]),
            ]);
            assert!(
                sib_const_index_fold_run_on_block(&mut func, Block(0)),
                "{sib_opcode:?}"
            );
            let insts = entry_insts(&func);
            // Rewrite-only: the constant stays for DCE.
            assert_eq!(insts.len(), 3);
            assert_eq!(insts[0].opcode, X86Opcode::MovRI);
            assert_eq!(insts[1].opcode, plain_opcode);
            assert_eq!(insts[1].flags, plain_opcode.default_flags());
            let expected = if is_load {
                vec![value, mem(1, 40)]
            } else {
                vec![mem(1, 40), value]
            };
            assert_eq!(insts[1].operands, expected, "{sib_opcode:?}");
            // A second run has nothing left to do.
            assert!(!sib_const_index_fold_run_on_block(&mut func, Block(0)));
        }
    }

    #[test]
    fn sib_const_index_fold_displacement_is_exact_at_the_i32_bounds() {
        let max = i64::from(i32::MAX);
        let min = i64::from(i32::MIN);
        // (index constant, scale, starting disp, expected disp or None)
        let cases: [(i64, u8, i32, Option<i32>); 9] = [
            (0, 8, 0, Some(0)),
            (-2, 8, 4, Some(-12)),
            (max, 1, 0, Some(i32::MAX)),
            (min, 1, 0, Some(i32::MIN)),
            (max, 1, 1, None),
            (min, 1, -1, None),
            (1 << 29, 4, 0, None),
            (i64::MAX, 2, 0, None),
            (i64::MIN, 1, -1, None),
        ];
        for (k, scale, disp, expected) in cases {
            let (changed, load) = const_index_load(vec![movri(vreg(2), k)], scale, disp);
            match expected {
                Some(new_disp) => {
                    assert!(changed, "{k}*{scale}+{disp}");
                    assert_eq!(load.opcode, X86Opcode::MovRM);
                    assert_eq!(load.operands, vec![vreg(3), mem(1, new_disp)]);
                }
                None => {
                    assert!(!changed, "{k}*{scale}+{disp}");
                    assert_eq!(load.opcode, X86Opcode::MovRMSib);
                    assert_eq!(
                        load.operands,
                        vec![vreg(3), sib_operand(vreg(1), vreg(2), scale, disp)]
                    );
                }
            }
        }
    }

    #[test]
    fn sib_const_index_fold_reads_lea_and_multiply_constants() {
        // The strength-reduced literal index: mov v5, 8 ; lea v2, [v5 + v5*2].
        let lea3 = X86ISelInst::new(
            X86Opcode::LeaSib,
            vec![vreg(2), sib_operand(vreg(5), vreg(5), 2, 0)],
        );
        let (changed, load) = const_index_load(vec![movri(vreg(5), 8), lea3], 1, 0);
        assert!(changed);
        assert_eq!(load.operands, vec![vreg(3), mem(1, 24)]);

        // lea with distinct sources and a displacement: 7 + 5*4 - 3 = 24.
        let lea = X86ISelInst::new(
            X86Opcode::LeaSib,
            vec![vreg(2), sib_operand(vreg(5), vreg(6), 4, -3)],
        );
        let (changed, load) =
            const_index_load(vec![movri(vreg(5), 7), movri(vreg(6), 5), lea], 1, 0);
        assert!(changed);
        assert_eq!(load.operands, vec![vreg(3), mem(1, 24)]);

        // imul v2, v5, 8 with v5 = 6.
        let imul_ri = X86ISelInst::new(
            X86Opcode::ImulRRI,
            vec![vreg(2), vreg(5), X86ISelOperand::Imm(8)],
        );
        let (changed, load) = const_index_load(vec![movri(vreg(5), 6), imul_ri], 1, 0);
        assert!(changed);
        assert_eq!(load.operands, vec![vreg(3), mem(1, 48)]);

        // imul v2, v5, v6 with v5 = -7, v6 = 8.
        let imul_rr = X86ISelInst::new(X86Opcode::ImulRR, vec![vreg(2), vreg(5), vreg(6)]);
        let (changed, load) =
            const_index_load(vec![movri(vreg(5), -7), movri(vreg(6), 8), imul_rr], 1, 0);
        assert!(changed);
        assert_eq!(load.operands, vec![vreg(3), mem(1, -56)]);

        // A product that wraps is the wrapping product: (2^62 * 4) = 0 mod 2^64.
        let imul_wrap = X86ISelInst::new(
            X86Opcode::ImulRRI,
            vec![vreg(2), vreg(5), X86ISelOperand::Imm(4)],
        );
        let (changed, load) = const_index_load(vec![movri(vreg(5), 1 << 62), imul_wrap], 8, 8);
        assert!(changed);
        assert_eq!(load.operands, vec![vreg(3), mem(1, 8)]);
    }

    #[test]
    fn sib_const_index_fold_declines_an_index_that_is_not_a_local_constant() {
        let imul_ri = |imm: i64| {
            X86ISelInst::new(
                X86Opcode::ImulRRI,
                vec![vreg(2), vreg(5), X86ISelOperand::Imm(imm)],
            )
        };
        let flagged = |mut inst: X86ISelInst| {
            inst.flags = X86Opcode::MovMR.default_flags();
            assert_ne!(inst.flags, inst.opcode.default_flags());
            inst
        };
        let with_origin = |mut inst: X86ISelInst| {
            inst.proof_origin = Some(X86ProofOrigin::AtomicLoad);
            inst
        };
        let cases: Vec<(&str, Vec<X86ISelInst>)> = vec![
            ("live-in index", vec![]),
            (
                "index copied from a constant",
                vec![
                    movri(vreg(5), 3),
                    X86ISelInst::new(X86Opcode::MovRR, vec![vreg(2), vreg(5)]),
                ],
            ),
            (
                "narrow write after the constant",
                vec![movri(vreg(2), 3), movri(vreg32(2), 1)],
            ),
            (
                "narrow tied write after the constant",
                vec![
                    movri(vreg(2), 3),
                    X86ISelInst::new(X86Opcode::AddRI, vec![vreg32(2), X86ISelOperand::Imm(1)]),
                ],
            ),
            ("Gpr32 constant definition", vec![movri(vreg32(2), 3)]),
            (
                "constant definition with a proof origin",
                vec![with_origin(movri(vreg(2), 3))],
            ),
            (
                "constant definition with non-default flags",
                vec![flagged(movri(vreg(2), 3))],
            ),
            (
                "multiply by an immediate outside i32",
                vec![movri(vreg(5), 0), imul_ri(i64::from(i32::MAX) + 1)],
            ),
            ("multiply of a live-in", vec![imul_ri(8)]),
            (
                "multiply source redefined narrow",
                vec![movri(vreg(5), 3), movri(vreg32(5), 1), imul_ri(8)],
            ),
            (
                "tied multiply",
                vec![
                    movri(vreg(2), 3),
                    movri(vreg(5), 8),
                    X86ISelInst::new(X86Opcode::ImulRR, vec![vreg(2), vreg(5)]),
                ],
            ),
            (
                "multiply with a Gpr32 source",
                vec![
                    movri(vreg(5), 3),
                    movri(vreg(6), 8),
                    X86ISelInst::new(X86Opcode::ImulRR, vec![vreg(2), vreg32(5), vreg(6)]),
                ],
            ),
            (
                "lea over a stack-slot base",
                vec![
                    movri(vreg(5), 3),
                    X86ISelInst::new(
                        X86Opcode::LeaSib,
                        vec![
                            vreg(2),
                            sib_operand(X86ISelOperand::StackSlot(0), vreg(5), 1, 0),
                        ],
                    ),
                ],
            ),
            (
                "lea with a Gpr32 index",
                vec![
                    movri(vreg(5), 3),
                    X86ISelInst::new(
                        X86Opcode::LeaSib,
                        vec![vreg(2), sib_operand(vreg(5), vreg32(5), 1, 0)],
                    ),
                ],
            ),
            (
                "lea with a scale that is not 1, 2, 4 or 8",
                vec![
                    movri(vreg(5), 3),
                    X86ISelInst::new(
                        X86Opcode::LeaSib,
                        vec![vreg(2), sib_operand(vreg(5), vreg(5), 3, 0)],
                    ),
                ],
            ),
            (
                "chain deeper than the bound",
                vec![
                    movri(vreg(5), 1),
                    X86ISelInst::new(
                        X86Opcode::ImulRRI,
                        vec![vreg(6), vreg(5), X86ISelOperand::Imm(2)],
                    ),
                    X86ISelInst::new(
                        X86Opcode::ImulRRI,
                        vec![vreg(7), vreg(6), X86ISelOperand::Imm(2)],
                    ),
                    X86ISelInst::new(
                        X86Opcode::ImulRRI,
                        vec![vreg(8), vreg(7), X86ISelOperand::Imm(2)],
                    ),
                    X86ISelInst::new(
                        X86Opcode::ImulRRI,
                        vec![vreg(2), vreg(8), X86ISelOperand::Imm(2)],
                    ),
                ],
            ),
        ];
        for (name, prefix) in cases {
            let (changed, load) = const_index_load(prefix, 1, 0);
            assert!(!changed, "{name}");
            assert_eq!(load.opcode, X86Opcode::MovRMSib, "{name}");
        }

        // A Gpr32 index over its own Gpr32 constant is not a 64-bit constant:
        // the definition matches the register exactly, and only the class
        // requirement on the resolved register declines it.
        let mut func = make_func(vec![
            movri(vreg32(2), 3),
            X86ISelInst::new(
                X86Opcode::MovRMSib,
                vec![vreg(3), sib_operand(vreg(1), vreg32(2), 8, 0)],
            ),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(!sib_const_index_fold_run_on_block(&mut func, Block(0)));
        assert_eq!(entry_insts(&func)[1].opcode, X86Opcode::MovRMSib);

        // The deepest accepted chain is one link shorter than the refused one.
        let (changed, load) = const_index_load(
            vec![
                movri(vreg(6), 1),
                X86ISelInst::new(
                    X86Opcode::ImulRRI,
                    vec![vreg(7), vreg(6), X86ISelOperand::Imm(2)],
                ),
                X86ISelInst::new(
                    X86Opcode::ImulRRI,
                    vec![vreg(8), vreg(7), X86ISelOperand::Imm(2)],
                ),
                X86ISelInst::new(
                    X86Opcode::ImulRRI,
                    vec![vreg(2), vreg(8), X86ISelOperand::Imm(2)],
                ),
            ],
            1,
            0,
        );
        assert!(changed);
        assert_eq!(load.operands, vec![vreg(3), mem(1, 8)]);
    }

    #[test]
    fn sib_const_index_fold_uses_the_constant_reaching_the_anchor() {
        // The nearest definition decides: 3 is overwritten by 5 before the load.
        let (changed, load) = const_index_load(vec![movri(vreg(2), 3), movri(vreg(2), 5)], 8, 0);
        assert!(changed);
        assert_eq!(load.operands, vec![vreg(3), mem(1, 40)]);

        // A constant assigned AFTER the load does not reach it.
        let mut func = make_func(vec![
            X86ISelInst::new(
                X86Opcode::MovRMSib,
                vec![vreg(3), sib_operand(vreg(1), vreg(2), 8, 0)],
            ),
            movri(vreg(2), 3),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(!sib_const_index_fold_run_on_block(&mut func, Block(0)));

        // A multiply reads its source as it stood AT the multiply: v5 is 6
        // there and is 100 by the time of the load.
        let (changed, load) = const_index_load(
            vec![
                movri(vreg(5), 6),
                X86ISelInst::new(
                    X86Opcode::ImulRRI,
                    vec![vreg(2), vreg(5), X86ISelOperand::Imm(8)],
                ),
                movri(vreg(5), 100),
            ],
            1,
            0,
        );
        assert!(changed);
        assert_eq!(load.operands, vec![vreg(3), mem(1, 48)]);
    }

    #[test]
    fn sib_const_index_fold_declines_an_anchor_outside_its_dialect() {
        let load = |value: X86ISelOperand, addr: X86ISelOperand| {
            X86ISelInst::new(X86Opcode::MovRMSib, vec![value, addr])
        };
        let mut flagged = load(vreg(3), sib_operand(vreg(1), vreg(2), 8, 0));
        flagged.flags = X86Opcode::MovMR.default_flags();
        assert_ne!(flagged.flags, X86Opcode::MovRMSib.default_flags());
        let mut with_origin = load(vreg(3), sib_operand(vreg(1), vreg(2), 8, 0));
        with_origin.proof_origin = Some(X86ProofOrigin::AtomicLoad);
        let cases: Vec<(&str, X86ISelInst)> = vec![
            ("non-default flags", flagged),
            ("proof origin", with_origin),
            (
                "stack-slot base",
                load(
                    vreg(3),
                    sib_operand(X86ISelOperand::StackSlot(0), vreg(2), 8, 0),
                ),
            ),
            (
                "Gpr32 base",
                load(vreg(3), sib_operand(vreg32(1), vreg(2), 8, 0)),
            ),
            (
                "Gpr32 index",
                load(vreg(3), sib_operand(vreg(1), vreg32(2), 8, 0)),
            ),
            (
                "Gpr32 value on the 64-bit form",
                load(vreg32(3), sib_operand(vreg(1), vreg(2), 8, 0)),
            ),
            (
                "Gpr64 value on the 32-bit form",
                X86ISelInst::new(
                    X86Opcode::MovRM32Sib,
                    vec![vreg(3), sib_operand(vreg(1), vreg(2), 8, 0)],
                ),
            ),
            (
                "scale that is not 1, 2, 4 or 8",
                load(vreg(3), sib_operand(vreg(1), vreg(2), 3, 0)),
            ),
            (
                "a third operand",
                X86ISelInst::new(
                    X86Opcode::MovRMSib,
                    vec![vreg(3), sib_operand(vreg(1), vreg(2), 8, 0), vreg(4)],
                ),
            ),
            (
                "an opcode outside the four anchors",
                X86ISelInst::new(
                    X86Opcode::LeaSib,
                    vec![vreg(3), sib_operand(vreg(1), vreg(2), 8, 0)],
                ),
            ),
        ];
        for (name, anchor) in cases {
            let before = anchor.clone();
            let mut func = make_func(vec![
                movri(vreg(2), 3),
                anchor,
                X86ISelInst::new(X86Opcode::Ret, vec![]),
            ]);
            assert!(
                !sib_const_index_fold_run_on_block(&mut func, Block(0)),
                "{name}"
            );
            let after = &entry_insts(&func)[1];
            assert_eq!(after.opcode, before.opcode, "{name}");
            assert_eq!(after.operands, before.operands, "{name}");
            assert_eq!(after.flags, before.flags, "{name}");
        }
    }

    #[test]
    fn peephole_folds_a_literal_element_index_to_a_displacement() {
        // The selector's stream for `*p.gep[3]` over 8-byte elements spelled as
        // a byte offset: mov v5, 8 ; lea v2, [v5 + v5*2] ; lea v4, [v1 + v2*1] ;
        // mov v3, [v4]. The whole pass leaves one `mov v3, [v1 + 24]` reading v1.
        let mut func = make_func(vec![
            movri(vreg(5), 8),
            X86ISelInst::new(
                X86Opcode::LeaSib,
                vec![vreg(2), sib_operand(vreg(5), vreg(5), 2, 0)],
            ),
            X86ISelInst::new(
                X86Opcode::LeaSib,
                vec![vreg(4), sib_operand(vreg(1), vreg(2), 1, 0)],
            ),
            X86ISelInst::new(X86Opcode::MovRM, vec![vreg(3), mem(4, 0)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut peephole = X86Peephole::default();
        assert!(peephole.run_on_function(&mut func));
        let loads: Vec<_> = entry_insts(&func)
            .iter()
            .filter(|inst| inst.opcode == X86Opcode::MovRM)
            .collect();
        assert_eq!(loads.len(), 1, "{:?}", entry_insts(&func));
        assert_eq!(loads[0].operands, vec![vreg(3), mem(1, 24)]);
        assert!(
            !entry_insts(&func)
                .iter()
                .any(|inst| matches!(inst.opcode, X86Opcode::MovRMSib | X86Opcode::MovMRSib)),
            "{:?}",
            entry_insts(&func)
        );
    }

    #[test]
    fn addr_chain_fold_refuses_disp_overflow() {
        let mut func = make_func(vec![
            X86ISelInst::new(
                X86Opcode::AddRI,
                vec![vreg(2), vreg(1), X86ISelOperand::Imm(i64::from(i32::MAX))],
            ),
            X86ISelInst::new(X86Opcode::MovRM, vec![vreg(3), mem(2, 8)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(!addr_chain_fold_run_on_block(&mut func, Block(0)));
    }

    #[test]
    fn addr_chain_fold_refuses_narrow_class_chain() {
        // Gpr32 chain members never fold (64-bit MOV forms only).
        let mut func = make_func(vec![
            X86ISelInst::new(
                X86Opcode::AddRI,
                vec![
                    vreg_class(2, RegClass::Gpr32),
                    vreg_class(1, RegClass::Gpr32),
                    X86ISelOperand::Imm(8),
                ],
            ),
            X86ISelInst::new(
                X86Opcode::MovRM,
                vec![
                    vreg(3),
                    X86ISelOperand::MemAddr {
                        base: Box::new(vreg_class(2, RegClass::Gpr32)),
                        disp: 0,
                    },
                ],
            ),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(!addr_chain_fold_run_on_block(&mut func, Block(0)));
    }

    // -----------------------------------------------------------------------
    // RM fusion (TCG_X86_IMUL_FUSE) — called directly, bypassing the env gate.
    // -----------------------------------------------------------------------

    #[test]
    fn imul_fuse_three_op_b05_shape() {
        // MovRMSib t(5),[1+2+8]; ImulRR d(6), a(4), t(5); t dead (redef by
        // next step's load)  ->  MovRR d,a ; ImulRMSib d,[sib].
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::MovRMSib, vec![vreg(5), sib_op(1, 2, 1, 8)]),
            X86ISelInst::new(X86Opcode::ImulRR, vec![vreg(6), vreg(4), vreg(5)]),
            X86ISelInst::new(X86Opcode::AddRR, vec![vreg(7), vreg(3), vreg(6)]),
            X86ISelInst::new(X86Opcode::MovRMSib, vec![vreg(5), sib_op(1, 2, 1, 16)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(8), vreg(5)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(imul_fuse_run_on_block(&mut func, Block(0)));
        let ops = entry_opcodes(&func);
        assert_eq!(
            ops,
            vec![
                X86Opcode::MovRR,
                X86Opcode::ImulRMSib,
                X86Opcode::AddRR,
                X86Opcode::MovRMSib,
                X86Opcode::MovRR,
                X86Opcode::Ret
            ]
        );
        let insts = entry_insts(&func);
        assert_eq!(insts[0].operands, vec![vreg(6), vreg(4)]);
        assert_eq!(insts[1].operands, vec![vreg(6), sib_op(1, 2, 1, 8)]);
    }

    #[test]
    fn imul_fuse_tied_direct() {
        // Tied ImulRR d, t with d != t: fuses to the bare ImulRMSib d,[sib].
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::MovRMSib, vec![vreg(5), sib_op(1, 2, 1, 0)]),
            X86ISelInst::new(X86Opcode::ImulRR, vec![vreg(6), vreg(5)]),
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(5), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(8), vreg(6)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(9), vreg(5)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(imul_fuse_run_on_block(&mut func, Block(0)));
        let insts = entry_insts(&func);
        assert_eq!(insts[0].opcode, X86Opcode::ImulRMSib);
        assert_eq!(insts[0].operands, vec![vreg(6), sib_op(1, 2, 1, 0)]);
    }

    #[test]
    fn imul_fuse_base_disp_load_fuses_to_imulrm() {
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::MovRM, vec![vreg(5), mem(1, 16)]),
            X86ISelInst::new(X86Opcode::ImulRR, vec![vreg(6), vreg(4), vreg(5)]),
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(5), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(8), vreg(6)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(9), vreg(5)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(imul_fuse_run_on_block(&mut func, Block(0)));
        let insts = entry_insts(&func);
        assert_eq!(insts[0].opcode, X86Opcode::MovRR);
        assert_eq!(insts[1].opcode, X86Opcode::ImulRM);
        assert_eq!(insts[1].operands, vec![vreg(6), mem(1, 16)]);
    }

    #[test]
    fn imul_fuse_refuses_store_in_window() {
        // A store between load and multiply may alias the loaded address.
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::MovRMSib, vec![vreg(5), sib_op(1, 2, 1, 0)]),
            X86ISelInst::new(X86Opcode::MovMR, vec![mem(3, 0), vreg(4)]),
            X86ISelInst::new(X86Opcode::ImulRR, vec![vreg(6), vreg(4), vreg(5)]),
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(5), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(8), vreg(6)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(9), vreg(5)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(!imul_fuse_run_on_block(&mut func, Block(0)));
    }

    #[test]
    fn imul_fuse_refuses_trap_pseudo_in_window() {
        // Moving the (potentially informative) load past a trap changes
        // which abort fires first: fail closed.
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::MovRMSib, vec![vreg(5), sib_op(1, 2, 1, 0)]),
            X86ISelInst::new(
                X86Opcode::TrapBoundsCheckExact,
                vec![vreg(4), vreg(4), X86ISelOperand::Imm(24)],
            ),
            X86ISelInst::new(X86Opcode::ImulRR, vec![vreg(6), vreg(4), vreg(5)]),
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(5), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(8), vreg(6)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(9), vreg(5)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(!imul_fuse_run_on_block(&mut func, Block(0)));
    }

    #[test]
    fn imul_fuse_refuses_ea_reg_redef_in_window() {
        // The SIB base is redefined between load and multiply: the fused EA
        // would read the NEW base. Refuse.
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::MovRMSib, vec![vreg(5), sib_op(1, 2, 1, 0)]),
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(1), X86ISelOperand::Imm(9)]),
            X86ISelInst::new(X86Opcode::ImulRR, vec![vreg(6), vreg(4), vreg(5)]),
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(5), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(8), vreg(6)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(9), vreg(5)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(!imul_fuse_run_on_block(&mut func, Block(0)));
    }

    #[test]
    fn imul_fuse_refuses_live_t() {
        // t is read again after the multiply: not locally dead. Refuse.
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::MovRMSib, vec![vreg(5), sib_op(1, 2, 1, 0)]),
            X86ISelInst::new(X86Opcode::ImulRR, vec![vreg(6), vreg(4), vreg(5)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(8), vreg(5)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(!imul_fuse_run_on_block(&mut func, Block(0)));
    }

    #[test]
    fn imul_fuse_refuses_t_use_in_window() {
        // A window instruction reads t: deleting the load would hand it the
        // stale pre-load value (adversarial-review class 1).
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::MovRMSib, vec![vreg(5), sib_op(1, 2, 1, 0)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(7), vreg(5)]),
            X86ISelInst::new(X86Opcode::ImulRR, vec![vreg(6), vreg(4), vreg(5)]),
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(5), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(8), vreg(6)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(9), vreg(7)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(10), vreg(5)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(!imul_fuse_run_on_block(&mut func, Block(0)));
    }

    #[test]
    fn imul_fuse_refuses_dst_in_ea() {
        // The anchor's destination IS the SIB base: the emitted MovRR d,a
        // would clobber the address before the fused load reads it
        // (adversarial-review class 2).
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::MovRMSib, vec![vreg(5), sib_op(6, 2, 1, 0)]),
            X86ISelInst::new(X86Opcode::ImulRR, vec![vreg(6), vreg(4), vreg(5)]),
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(5), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(8), vreg(6)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(9), vreg(5)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(!imul_fuse_run_on_block(&mut func, Block(0)));
    }

    #[test]
    fn imul_fuse_refuses_cmovcc_redef_of_t() {
        // Cmovcc writes t CONDITIONALLY: the not-taken lane keeps the loaded
        // value, so it must not end t's live range (adversarial-review
        // class 3 — the conditional-write shadow class, again).
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::MovRMSib, vec![vreg(5), sib_op(1, 2, 1, 0)]),
            X86ISelInst::new(X86Opcode::ImulRR, vec![vreg(6), vreg(4), vreg(5)]),
            X86ISelInst::new(
                X86Opcode::Cmovcc,
                vec![vreg(5), vreg(7), X86ISelOperand::CondCode(X86CondCode::AE)],
            ),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(8), vreg(6)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(9), vreg(5)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(!imul_fuse_run_on_block(&mut func, Block(0)));
    }

    #[test]
    fn imul_fuse_refuses_tied_redef_of_t() {
        // A tied 2-operand AddRI reads t through operand 0: not a killing
        // redef (adversarial-review class 3, tied family).
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::MovRMSib, vec![vreg(5), sib_op(1, 2, 1, 0)]),
            X86ISelInst::new(X86Opcode::ImulRR, vec![vreg(6), vreg(4), vreg(5)]),
            X86ISelInst::new(X86Opcode::AddRI, vec![vreg(5), X86ISelOperand::Imm(3)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(8), vreg(6)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(9), vreg(5)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(!imul_fuse_run_on_block(&mut func, Block(0)));
    }

    #[test]
    fn imul_fuse_refuses_preg_ea_component() {
        // A PReg EA base is an address the pass cannot track: fail closed
        // (adversarial-review class 4).
        let mut func = make_func(vec![
            X86ISelInst::new(
                X86Opcode::MovRMSib,
                vec![
                    vreg(5),
                    X86ISelOperand::SibMemAddr {
                        base: Box::new(X86ISelOperand::PReg(trust_cg_ir::x86_64_regs::RDI)),
                        index: Box::new(vreg(2)),
                        scale: 1,
                        disp: 0,
                    },
                ],
            ),
            X86ISelInst::new(X86Opcode::ImulRR, vec![vreg(6), vreg(4), vreg(5)]),
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(5), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(8), vreg(6)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(9), vreg(5)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(!imul_fuse_run_on_block(&mut func, Block(0)));
    }

    #[test]
    fn imul_fuse_refuses_t_squared() {
        // Both factors are the load result: the value is needed twice but
        // the load is deleted. Refuse.
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::MovRMSib, vec![vreg(5), sib_op(1, 2, 1, 0)]),
            X86ISelInst::new(X86Opcode::ImulRR, vec![vreg(6), vreg(5), vreg(5)]),
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(5), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(8), vreg(6)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(9), vreg(5)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(!imul_fuse_run_on_block(&mut func, Block(0)));
    }

    // -----------------------------------------------------------------------
    // Memory-destination RMW fusion (TCG_NO_X86_RMW_FUSE) — called directly,
    // bypassing the env gate; the admission callback is |_| true except where
    // the admission gate itself is under test.
    // -----------------------------------------------------------------------

    /// The b1 arm-1 accept shape: load / ALU / same-address store, with the
    /// postlude that makes `t`(5) and `d`(6) locally dead (killing redefs
    /// with downstream readers, mirroring the imul_fuse tests).
    fn rmw_triple(
        load_mem: X86ISelOperand,
        alu: X86ISelInst,
        store_mem: X86ISelOperand,
    ) -> Vec<X86ISelInst> {
        let load_op = match load_mem {
            X86ISelOperand::SibMemAddr { .. } => X86Opcode::MovRMSib,
            _ => X86Opcode::MovRM,
        };
        let store_op = match store_mem {
            X86ISelOperand::SibMemAddr { .. } => X86Opcode::MovMRSib,
            _ => X86Opcode::MovMR,
        };
        vec![
            X86ISelInst::new(load_op, vec![vreg(5), load_mem]),
            alu,
            X86ISelInst::new(store_op, vec![store_mem, vreg(6)]),
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(5), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(6), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(8), vreg(6)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(9), vreg(5)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]
    }

    #[test]
    fn rmw_fuse_block_tail_without_redefs_fuses() {
        // The REAL b1 hot block: nothing touches t or d again before the
        // block ends — no redefs for the block-local rule to find. The
        // function-wide single-def/single-use fallback must admit it.
        let sib_i = |id: u32| X86ISelOperand::SibMemAddr {
            base: Box::new(X86ISelOperand::StackSlot(0)),
            index: Box::new(vreg(id)),
            scale: 8,
            disp: 0,
        };
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(45), vreg(44)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(51), vreg(45)]),
            X86ISelInst::new(X86Opcode::MovRMSib, vec![vreg(63), sib_i(44)]),
            X86ISelInst::new(X86Opcode::XorRR, vec![vreg(64), vreg(63), vreg(46)]),
            X86ISelInst::new(X86Opcode::MovMRSib, vec![sib_i(51), vreg(64)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(65), vreg(38)]),
            X86ISelInst::new(X86Opcode::Jmp, vec![X86ISelOperand::Block(Block(0))]),
        ]);
        assert!(rmw_fuse_run_on_block(&mut func, Block(0), |_| true));
        let ops = entry_opcodes(&func);
        assert!(
            ops.contains(&X86Opcode::XorMRSib),
            "the untouched-tail b1 shape must fuse: {ops:?}"
        );
        assert!(!ops.contains(&X86Opcode::XorRR));
    }

    #[test]
    fn rmw_fuse_copy_chain_alias_store_index_fuses() {
        // b1 arm 1's REAL pre-peephole shape: the store indexes through a
        // pure copy chain of the load's index (v51 <- v45 <- v44).
        let sib_i = |id: u32| X86ISelOperand::SibMemAddr {
            base: Box::new(X86ISelOperand::StackSlot(0)),
            index: Box::new(vreg(id)),
            scale: 8,
            disp: 0,
        };
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(45), vreg(44)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(51), vreg(45)]),
            X86ISelInst::new(X86Opcode::MovRMSib, vec![vreg(5), sib_i(44)]),
            X86ISelInst::new(X86Opcode::XorRR, vec![vreg(6), vreg(5), vreg(4)]),
            X86ISelInst::new(X86Opcode::MovMRSib, vec![sib_i(51), vreg(6)]),
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(5), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(6), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(8), vreg(6)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(9), vreg(5)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(rmw_fuse_run_on_block(&mut func, Block(0), |_| true));
        let ops = entry_opcodes(&func);
        assert!(
            ops.contains(&X86Opcode::XorMRSib),
            "copy-chain-alias store EA must fuse: {ops:?}"
        );
    }

    #[test]
    fn rmw_fuse_scale_folded_store_index_fuses() {
        // b1 arm 2's shape: load at [slot + j*8], store at [slot + (j*8)*1]
        // with the *8 as a single-def ImulRRI.
        let mut func = make_func(vec![
            X86ISelInst::new(
                X86Opcode::ImulRRI,
                vec![vreg(93), vreg(44), X86ISelOperand::Imm(8)],
            ),
            X86ISelInst::new(
                X86Opcode::MovRMSib,
                vec![
                    vreg(5),
                    X86ISelOperand::SibMemAddr {
                        base: Box::new(X86ISelOperand::StackSlot(0)),
                        index: Box::new(vreg(44)),
                        scale: 8,
                        disp: 0,
                    },
                ],
            ),
            X86ISelInst::new(X86Opcode::AddRR, vec![vreg(6), vreg(5), vreg(4)]),
            X86ISelInst::new(
                X86Opcode::MovMRSib,
                vec![
                    X86ISelOperand::SibMemAddr {
                        base: Box::new(X86ISelOperand::StackSlot(0)),
                        index: Box::new(vreg(93)),
                        scale: 1,
                        disp: 0,
                    },
                    vreg(6),
                ],
            ),
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(5), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(6), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(8), vreg(6)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(9), vreg(5)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(rmw_fuse_run_on_block(&mut func, Block(0), |_| true));
        assert!(
            entry_opcodes(&func).contains(&X86Opcode::AddMRSib),
            "scale-folded store EA must fuse: {:?}",
            entry_opcodes(&func)
        );
    }

    #[test]
    fn rmw_fuse_fuses_when_the_register_operand_is_defined_before_the_alu() {
        // b1_mispredict's hot-loop shape, which the pre-2026-09-29 W1 window
        // declined: the fused register operand `s` is DEFINED between the load
        // and the ALU.
        //
        //   MovRMSib t, [slot + j*8]      ; the load
        //   MovRR    s, acc               ; <- the def of `s` W1 used to refuse
        //   AddRR    d, t, s              ; the anchor
        //   MovMRSib [slot + j'*8], d     ; the store, j' a copy-alias of j
        //
        // Sound because the replacement is spliced at the STORE's position, the
        // latest of the three, so the fused instruction reads `s` AFTER that def;
        // and the W2 window still refuses a redef of `s` between the ALU and the
        // store, which is the stretch that actually has to carry.
        let sib_i = |id: u32| X86ISelOperand::SibMemAddr {
            base: Box::new(X86ISelOperand::StackSlot(0)),
            index: Box::new(vreg(id)),
            scale: 8,
            disp: 0,
        };
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(44), X86ISelOperand::Imm(3)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(51), vreg(44)]),
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(4), X86ISelOperand::Imm(7)]),
            X86ISelInst::new(X86Opcode::MovRMSib, vec![vreg(5), sib_i(44)]),
            // The def of `s` inside W1.
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(7), vreg(4)]),
            X86ISelInst::new(X86Opcode::AddRR, vec![vreg(6), vreg(5), vreg(7)]),
            X86ISelInst::new(X86Opcode::MovMRSib, vec![sib_i(51), vreg(6)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let mut off = func.clone();

        assert!(
            rmw_fuse_run_on_block_sdef(&mut func, Block(0), |_| true, true),
            "a def of `s` in W1 must not block the fusion"
        );
        let ops = entry_opcodes(&func);
        assert!(
            ops.contains(&X86Opcode::AddMRSib),
            "expected the memory-destination add: {ops:?}"
        );
        assert!(
            !ops.contains(&X86Opcode::MovRMSib),
            "the load is deleted: {ops:?}"
        );
        assert!(
            !ops.contains(&X86Opcode::AddRR),
            "the register add is deleted: {ops:?}"
        );

        // FALSIFIABILITY: the stricter window still declines the same fixture, so
        // the relaxation is what decides.
        assert!(
            !rmw_fuse_run_on_block_sdef(&mut off, Block(0), |_| true, false),
            "`no-x86-rmw-fuse-sdef` must restore the refusal"
        );
        assert!(!entry_opcodes(&off).contains(&X86Opcode::AddMRSib));
    }

    #[test]
    fn rmw_fuse_still_refuses_a_redef_of_s_between_the_alu_and_the_store() {
        // THE CONDITION THAT REMAINS. `s` must carry unchanged from the ALU to the
        // store, because the fused instruction reads it at the store's position.
        // A redef on that stretch must decline even with the relaxation on.
        let sib_i = |id: u32| X86ISelOperand::SibMemAddr {
            base: Box::new(X86ISelOperand::StackSlot(0)),
            index: Box::new(vreg(id)),
            scale: 8,
            disp: 0,
        };
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(44), X86ISelOperand::Imm(3)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(51), vreg(44)]),
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(4), X86ISelOperand::Imm(7)]),
            X86ISelInst::new(X86Opcode::MovRMSib, vec![vreg(5), sib_i(44)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(7), vreg(4)]),
            X86ISelInst::new(X86Opcode::AddRR, vec![vreg(6), vreg(5), vreg(7)]),
            // Clobbers `s` between the ALU and the store.
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(7), X86ISelOperand::Imm(9)]),
            X86ISelInst::new(X86Opcode::MovMRSib, vec![sib_i(51), vreg(6)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(
            !rmw_fuse_run_on_block_sdef(&mut func, Block(0), |_| true, true),
            "a redef of `s` between the ALU and the store must decline"
        );
        assert!(!entry_opcodes(&func).contains(&X86Opcode::AddMRSib));
    }

    #[test]
    fn rmw_fuse_refuses_multi_def_alias_index() {
        // The store's index alias has a SECOND def: canonicalization must
        // fail closed and the triple must stay unfused.
        let sib_i = |id: u32| X86ISelOperand::SibMemAddr {
            base: Box::new(X86ISelOperand::StackSlot(0)),
            index: Box::new(vreg(id)),
            scale: 8,
            disp: 0,
        };
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(51), vreg(44)]),
            X86ISelInst::new(X86Opcode::MovRMSib, vec![vreg(5), sib_i(44)]),
            X86ISelInst::new(X86Opcode::XorRR, vec![vreg(6), vreg(5), vreg(4)]),
            X86ISelInst::new(X86Opcode::MovMRSib, vec![sib_i(51), vreg(6)]),
            // Second def of the alias AFTER the store: multi-def, refused.
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(51), vreg(4)]),
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(5), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(6), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(8), vreg(6)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(9), vreg(5)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(!rmw_fuse_run_on_block(&mut func, Block(0), |_| true));
    }

    #[test]
    fn rmw_fuse_refuses_alias_when_canonical_root_changes_in_window() {
        // v51 captures the OLD value of v44 for the load. The tied AddRI then
        // changes v44 before the store. Position-independent copy-chain
        // canonicalization alone says both indices have root v44, but the
        // addresses differ in time and fusing would write the wrong slot.
        let sib_i = |id: u32| X86ISelOperand::SibMemAddr {
            base: Box::new(X86ISelOperand::StackSlot(0)),
            index: Box::new(vreg(id)),
            scale: 8,
            disp: 0,
        };
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(51), vreg(44)]),
            X86ISelInst::new(X86Opcode::MovRMSib, vec![vreg(5), sib_i(51)]),
            X86ISelInst::new(X86Opcode::AddRI, vec![vreg(44), X86ISelOperand::Imm(1)]),
            X86ISelInst::new(X86Opcode::XorRR, vec![vreg(6), vreg(5), vreg(4)]),
            X86ISelInst::new(X86Opcode::MovMRSib, vec![sib_i(44), vreg(6)]),
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(5), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(6), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(
            !rmw_fuse_run_on_block(&mut func, Block(0), |_| true),
            "an intervening write to the canonical EA root must fail closed"
        );
    }

    #[test]
    fn rmw_fuse_stackslot_base_sib_fuses() {
        // b1's REAL hot arm: the table is a STACK array, so the SIB base is
        // a StackSlot. The slot cannot be redefined; the E-scan covers the
        // VReg index.
        let slot_sib = || X86ISelOperand::SibMemAddr {
            base: Box::new(X86ISelOperand::StackSlot(3)),
            index: Box::new(vreg(2)),
            scale: 8,
            disp: -160,
        };
        let mut func = make_func(rmw_triple(
            slot_sib(),
            X86ISelInst::new(X86Opcode::XorRR, vec![vreg(6), vreg(5), vreg(4)]),
            slot_sib(),
        ));
        assert!(rmw_fuse_run_on_block(&mut func, Block(0), |_| true));
        let ops = entry_opcodes(&func);
        assert!(
            ops.contains(&X86Opcode::XorMRSib),
            "stack-slot-based triple must fuse: {ops:?}"
        );
        assert!(!ops.contains(&X86Opcode::MovRMSib));
    }

    #[test]
    fn rmw_fuse_xor_three_op_b1_shape() {
        // MovRMSib t(5),[1+2*8-160]; XorRR d(6),t(5),s(4); MovMRSib [same],d
        //   ->  XorMRSib [1+2*8-160], s(4); load and ALU deleted.
        let mut func = make_func(rmw_triple(
            sib_op(1, 2, 8, -160),
            X86ISelInst::new(X86Opcode::XorRR, vec![vreg(6), vreg(5), vreg(4)]),
            sib_op(1, 2, 8, -160),
        ));
        assert!(rmw_fuse_run_on_block(&mut func, Block(0), |_| true));
        assert_eq!(
            entry_opcodes(&func),
            vec![
                X86Opcode::XorMRSib,
                X86Opcode::MovRI,
                X86Opcode::MovRI,
                X86Opcode::MovRR,
                X86Opcode::MovRR,
                X86Opcode::Ret
            ]
        );
        let insts = entry_insts(&func);
        assert_eq!(insts[0].operands, vec![sib_op(1, 2, 8, -160), vreg(4)]);
        assert_eq!(insts[0].flags, X86Opcode::XorMRSib.default_flags());
        assert_eq!(insts[0].proof_origin, None);
    }

    #[test]
    fn rmw_fuse_xor_commuted_operands() {
        // Commuted anchor `XorRR d, s, t` fuses identically.
        let mut func = make_func(rmw_triple(
            sib_op(1, 2, 8, -160),
            X86ISelInst::new(X86Opcode::XorRR, vec![vreg(6), vreg(4), vreg(5)]),
            sib_op(1, 2, 8, -160),
        ));
        assert!(rmw_fuse_run_on_block(&mut func, Block(0), |_| true));
        let insts = entry_insts(&func);
        assert_eq!(insts[0].opcode, X86Opcode::XorMRSib);
        assert_eq!(insts[0].operands, vec![sib_op(1, 2, 8, -160), vreg(4)]);
    }

    #[test]
    fn rmw_fuse_add_tied_form() {
        // Tied `AddRR d, t`: d := d + t, so the fused register source is d's
        // own pre-value.
        let mut func = make_func(rmw_triple(
            sib_op(1, 2, 8, 0),
            X86ISelInst::new(X86Opcode::AddRR, vec![vreg(6), vreg(5)]),
            sib_op(1, 2, 8, 0),
        ));
        assert!(rmw_fuse_run_on_block(&mut func, Block(0), |_| true));
        let insts = entry_insts(&func);
        assert_eq!(insts[0].opcode, X86Opcode::AddMRSib);
        assert_eq!(insts[0].operands, vec![sib_op(1, 2, 8, 0), vreg(6)]);
    }

    #[test]
    fn rmw_fuse_add_base_disp_form() {
        // Full-width MovRM/MovMR pair fuses to the base+disp AddMR.
        let mut func = make_func(rmw_triple(
            mem(1, 16),
            X86ISelInst::new(X86Opcode::AddRR, vec![vreg(6), vreg(5), vreg(4)]),
            mem(1, 16),
        ));
        assert!(rmw_fuse_run_on_block(&mut func, Block(0), |_| true));
        let insts = entry_insts(&func);
        assert_eq!(insts[0].opcode, X86Opcode::AddMR);
        assert_eq!(insts[0].operands, vec![mem(1, 16), vreg(4)]);
    }

    #[test]
    fn rmw_fuse_refuses_store_in_load_alu_window() {
        // A store between load and ALU may alias the loaded address.
        let mut insts = rmw_triple(
            sib_op(1, 2, 8, 0),
            X86ISelInst::new(X86Opcode::XorRR, vec![vreg(6), vreg(5), vreg(4)]),
            sib_op(1, 2, 8, 0),
        );
        insts.insert(
            1,
            X86ISelInst::new(X86Opcode::MovMR, vec![mem(3, 0), vreg(4)]),
        );
        let mut func = make_func(insts);
        assert!(!rmw_fuse_run_on_block(&mut func, Block(0), |_| true));
    }

    #[test]
    fn rmw_fuse_refuses_store_in_alu_store_window() {
        // A store between ALU and the anchor store may alias the RMW address.
        let mut insts = rmw_triple(
            sib_op(1, 2, 8, 0),
            X86ISelInst::new(X86Opcode::XorRR, vec![vreg(6), vreg(5), vreg(4)]),
            sib_op(1, 2, 8, 0),
        );
        insts.insert(
            2,
            X86ISelInst::new(X86Opcode::MovMR, vec![mem(3, 0), vreg(4)]),
        );
        let mut func = make_func(insts);
        assert!(!rmw_fuse_run_on_block(&mut func, Block(0), |_| true));
    }

    #[test]
    fn rmw_fuse_refuses_flag_reader_in_alu_store_window() {
        // The ALU's flag-write moves from j down to k: a window Setcc/Cmovcc
        // would observe the ALU flags in the unfused stream and stale flags
        // in the fused one (the NOVEL W2 hazard; `imul_fuse_window_ok` alone
        // admits both — EMPTY default flags).
        for reader in [
            X86ISelInst::new(
                X86Opcode::Setcc,
                vec![vreg(11), X86ISelOperand::CondCode(X86CondCode::E)],
            ),
            X86ISelInst::new(
                X86Opcode::Cmovcc,
                vec![
                    vreg(11),
                    vreg(12),
                    X86ISelOperand::CondCode(X86CondCode::AE),
                ],
            ),
        ] {
            let mut insts = rmw_triple(
                sib_op(1, 2, 8, 0),
                X86ISelInst::new(X86Opcode::XorRR, vec![vreg(6), vreg(5), vreg(4)]),
                sib_op(1, 2, 8, 0),
            );
            insts.insert(2, reader);
            let mut func = make_func(insts);
            assert!(!rmw_fuse_run_on_block(&mut func, Block(0), |_| true));
        }
    }

    #[test]
    fn rmw_fuse_refuses_flag_writer_in_alu_store_window() {
        // A window flag-writer's flags survive at exit in the unfused stream
        // but would be overwritten by the moved ALU-write in the fused one.
        let mut insts = rmw_triple(
            sib_op(1, 2, 8, 0),
            X86ISelInst::new(X86Opcode::XorRR, vec![vreg(6), vreg(5), vreg(4)]),
            sib_op(1, 2, 8, 0),
        );
        insts.insert(
            2,
            X86ISelInst::new(X86Opcode::AddRR, vec![vreg(11), vreg(12), vreg(13)]),
        );
        let mut func = make_func(insts);
        assert!(!rmw_fuse_run_on_block(&mut func, Block(0), |_| true));
    }

    #[test]
    fn rmw_fuse_refuses_ea_reg_redef_in_window() {
        // The SIB base is redefined between ALU and store: the store's
        // structurally-identical EA no longer VALUE-matches the load's.
        // (MovRI writes no flags, so this isolates the E condition from W2's
        // flag fence.)
        let mut insts = rmw_triple(
            sib_op(1, 2, 8, 0),
            X86ISelInst::new(X86Opcode::XorRR, vec![vreg(6), vreg(5), vreg(4)]),
            sib_op(1, 2, 8, 0),
        );
        insts.insert(
            2,
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(1), X86ISelOperand::Imm(9)]),
        );
        let mut func = make_func(insts);
        assert!(!rmw_fuse_run_on_block(&mut func, Block(0), |_| true));
    }

    #[test]
    fn rmw_fuse_refuses_t_use_in_window() {
        // A window instruction reads t: deleting the load would hand it the
        // stale pre-load value.
        let mut insts = rmw_triple(
            sib_op(1, 2, 8, 0),
            X86ISelInst::new(X86Opcode::XorRR, vec![vreg(6), vreg(5), vreg(4)]),
            sib_op(1, 2, 8, 0),
        );
        insts.insert(
            1,
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(7), vreg(5)]),
        );
        let mut func = make_func(insts);
        assert!(!rmw_fuse_run_on_block(&mut func, Block(0), |_| true));
    }

    #[test]
    fn rmw_fuse_refuses_live_d_after_store() {
        // d is read after the store: the fused form defines no register, so
        // the ALU result would vanish. Refuse (condition D).
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::MovRMSib, vec![vreg(5), sib_op(1, 2, 8, 0)]),
            X86ISelInst::new(X86Opcode::XorRR, vec![vreg(6), vreg(5), vreg(4)]),
            X86ISelInst::new(X86Opcode::MovMRSib, vec![sib_op(1, 2, 8, 0), vreg(6)]),
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(5), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(8), vreg(6)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(9), vreg(5)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(!rmw_fuse_run_on_block(&mut func, Block(0), |_| true));
    }

    #[test]
    fn rmw_fuse_refuses_mismatched_store_ea() {
        // Structural EA identity is the entire alias argument: any component
        // mismatch (scale, disp, index, base) refuses.
        for store_sib in [
            sib_op(1, 2, 4, 0),
            sib_op(1, 2, 8, 8),
            sib_op(1, 3, 8, 0),
            sib_op(3, 2, 8, 0),
        ] {
            let mut func = make_func(rmw_triple(
                sib_op(1, 2, 8, 0),
                X86ISelInst::new(X86Opcode::XorRR, vec![vreg(6), vreg(5), vreg(4)]),
                store_sib,
            ));
            assert!(!rmw_fuse_run_on_block(&mut func, Block(0), |_| true));
        }
    }

    #[test]
    fn rmw_fuse_refuses_preg_ea_component() {
        // A PReg EA base is an address the pass cannot track: fail closed.
        let preg_sib = || X86ISelOperand::SibMemAddr {
            base: Box::new(X86ISelOperand::PReg(trust_cg_ir::x86_64_regs::RDI)),
            index: Box::new(vreg(2)),
            scale: 8,
            disp: 0,
        };
        let mut func = make_func(rmw_triple(
            preg_sib(),
            X86ISelInst::new(X86Opcode::XorRR, vec![vreg(6), vreg(5), vreg(4)]),
            preg_sib(),
        ));
        assert!(!rmw_fuse_run_on_block(&mut func, Block(0), |_| true));
    }

    #[test]
    fn rmw_fuse_refuses_proof_origin() {
        // A proof-carrying anchor or store must never be rewritten.
        for tagged in [1_usize, 2] {
            let mut insts = rmw_triple(
                sib_op(1, 2, 8, 0),
                X86ISelInst::new(X86Opcode::XorRR, vec![vreg(6), vreg(5), vreg(4)]),
                sib_op(1, 2, 8, 0),
            );
            insts[tagged] = insts[tagged]
                .clone()
                .with_proof_origin(X86ProofOrigin::AtomicLoad);
            let mut func = make_func(insts);
            assert!(!rmw_fuse_run_on_block(&mut func, Block(0), |_| true));
        }
    }

    #[test]
    fn rmw_fuse_refuses_s_equals_t() {
        // Both ALU sources are the load result: the value is needed twice
        // but the load is deleted. Refuse.
        let mut func = make_func(rmw_triple(
            sib_op(1, 2, 8, 0),
            X86ISelInst::new(X86Opcode::XorRR, vec![vreg(6), vreg(5), vreg(5)]),
            sib_op(1, 2, 8, 0),
        ));
        assert!(!rmw_fuse_run_on_block(&mut func, Block(0), |_| true));
    }

    #[test]
    fn rmw_fuse_admission_gate_is_fail_closed() {
        // The proof admission callback is consulted with the EXACT fused
        // opcode; a closed or wrong-opcode admission never fires.
        let shape = || {
            make_func(rmw_triple(
                sib_op(1, 2, 8, 0),
                X86ISelInst::new(X86Opcode::XorRR, vec![vreg(6), vreg(5), vreg(4)]),
                sib_op(1, 2, 8, 0),
            ))
        };
        let mut closed = shape();
        assert!(!rmw_fuse_run_on_block(&mut closed, Block(0), |_| false));
        let mut wrong_opcode = shape();
        assert!(!rmw_fuse_run_on_block(&mut wrong_opcode, Block(0), |op| op == X86Opcode::AddMRSib));
        let mut exact = shape();
        assert!(rmw_fuse_run_on_block(&mut exact, Block(0), |op| op == X86Opcode::XorMRSib));
        assert_eq!(entry_insts(&exact)[0].opcode, X86Opcode::XorMRSib);
    }

    #[test]
    fn rmw_fuse_default_pass_admission_is_closed() {
        // `X86Peephole::default()` carries the closed `|_| false` admission:
        // the full pass never creates an RMW opcode without an injected proof
        // gate (env gate untouched — the fusion declines on admission alone).
        let mut func = make_func(rmw_triple(
            sib_op(1, 2, 8, 0),
            X86ISelInst::new(X86Opcode::XorRR, vec![vreg(6), vreg(5), vreg(4)]),
            sib_op(1, 2, 8, 0),
        ));
        let mut peephole = X86Peephole::default();
        peephole.run_on_function(&mut func);
        assert!(
            !entry_opcodes(&func)
                .iter()
                .any(|op| matches!(op, X86Opcode::XorMRSib | X86Opcode::XorMR)),
            "closed default admission must never create an RMW opcode"
        );
    }

    #[test]
    fn rmw_fuse_kill_switch_and_default_on() {
        // Full-pass runs under the lock-guarded env shim: default-ON fuses
        // (with an open admission), TCG_NO_X86_RMW_FUSE=1 disables.
        let shape = || {
            make_func(rmw_triple(
                sib_op(1, 2, 8, 0),
                X86ISelInst::new(X86Opcode::XorRR, vec![vreg(6), vreg(5), vreg(4)]),
                sib_op(1, 2, 8, 0),
            ))
        };
        crate::env_lock::with_env_overrides_removed(&["TCG_NO_X86_RMW_FUSE"], || {
            assert!(rmw_fuse_enabled());
            let mut func = shape();
            X86Peephole::new(|_| true).run_on_function(&mut func);
            assert!(entry_opcodes(&func).contains(&X86Opcode::XorMRSib));
        });
        crate::env_lock::with_env_overrides(&[("TCG_NO_X86_RMW_FUSE", "1")], || {
            assert!(!rmw_fuse_enabled());
            let mut func = shape();
            X86Peephole::new(|_| true).run_on_function(&mut func);
            assert!(!entry_opcodes(&func).contains(&X86Opcode::XorMRSib));
        });
    }

    // -----------------------------------------------------------------------
    // Variable-count rotate idiom (TCG_NO_X86_ROTATE_VAR_IDIOM) — called
    // directly, bypassing the env gate; the admission callback is |_| true
    // except where the admission gate itself is under test.
    // -----------------------------------------------------------------------

    fn rcx() -> X86ISelOperand {
        X86ISelOperand::PReg(trust_cg_ir::x86_64_regs::RCX)
    }

    /// The v1 bridge `bitmanip_rotate` expansion in one block. Ids: c=1 x=2
    /// z=3 eff=4 neg=5 compl=6 lo=7 hi=8 d=9 out=10.
    fn rotate_var_v1_shape() -> Vec<X86ISelInst> {
        vec![
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(3), imm(0)]),
            X86ISelInst::new(X86Opcode::AndRI, vec![vreg(4), vreg(1), imm(63)]),
            X86ISelInst::new(X86Opcode::SubRR, vec![vreg(5), vreg(3), vreg(4)]),
            X86ISelInst::new(X86Opcode::AndRI, vec![vreg(6), vreg(5), imm(63)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![rcx(), vreg(4)]),
            X86ISelInst::new(X86Opcode::ShlRR, vec![vreg(7), vreg(2)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![rcx(), vreg(6)]),
            X86ISelInst::new(X86Opcode::ShrRR, vec![vreg(8), vreg(2)]),
            X86ISelInst::new(X86Opcode::OrRR, vec![vreg(9), vreg(7), vreg(8)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(10), vreg(9)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]
    }

    fn run_rotate_var(func: &mut X86ISelFunction, admit: ReconstructionAdmit) -> bool {
        let live_in = flags_live_in_by_block(func);
        rotate_var_idiom_run_on_block(func, Block(0), &live_in, admit)
    }

    /// Source operands of every remaining `MovRR/... -> PReg(RCX)` CL setup.
    fn cl_mov_sources(func: &X86ISelFunction) -> Vec<X86ISelOperand> {
        entry_insts(func)
            .iter()
            .filter(|w| {
                matches!(
                    w.operands.first(),
                    Some(X86ISelOperand::PReg(p)) if *p == trust_cg_ir::x86_64_regs::RCX
                )
            })
            .map(|w| w.operands[1].clone())
            .collect()
    }

    #[test]
    fn rotate_var_v1_full_expansion_fuses() {
        let mut func = make_func(rotate_var_v1_shape());
        assert!(run_rotate_var(&mut func, |_| true));
        let ops = entry_opcodes(&func);
        assert!(ops.contains(&X86Opcode::RolRCl), "{ops:?}");
        for gone in [X86Opcode::ShlRR, X86Opcode::ShrRR, X86Opcode::SubRR] {
            assert!(!ops.contains(&gone), "{gone:?} must be deleted: {ops:?}");
        }
        // The compl AndRI is deleted with its chain; eff's AndRI is left
        // (now dead) for the DCE pass that follows the peephole.
        assert_eq!(
            ops.iter().filter(|&&o| o == X86Opcode::AndRI).count(),
            1,
            "{ops:?}"
        );
        // Exactly ONE CL mov remains, and the v1 count chain is a single
        // low-6-transparent AndRI, so the feed walks back to the RAW count.
        assert_eq!(cl_mov_sources(&func), vec![vreg(1)]);
        // The rotate carries the Stage-1 pre-RA operand schema: [dst, src].
        let rol = entry_insts(&func)
            .iter()
            .find(|w| w.opcode == X86Opcode::RolRCl)
            .unwrap();
        assert_eq!(rol.operands.as_slice(), &[vreg(9), vreg(2)]);
    }

    #[test]
    fn rotate_var_opaque_count_chain_keeps_eff_feed() {
        // eff's own def is NOT a low-6 link (mask 62): the walk stops at eff,
        // the kept CL mov is untouched, and the collapse still fires — the
        // reconstruction obligation is TOTAL in CL, so any feed is exact as
        // long as both count chains share its low 6 bits (here e == f1).
        let mut shape = rotate_var_v1_shape();
        shape[1] = X86ISelInst::new(X86Opcode::AndRI, vec![vreg(4), vreg(1), imm(62)]);
        let mut func = make_func(shape);
        assert!(run_rotate_var(&mut func, |_| true));
        assert!(entry_opcodes(&func).contains(&X86Opcode::RolRCl));
        assert_eq!(cl_mov_sources(&func), vec![vreg(4)]);
    }

    #[test]
    fn rotate_var_p6_block4_chain_fuses_to_raw_feed() {
        // The EXACT p6 Block(4) pre-RA shape (x86-cse dump, design §2), with
        // the two LICM-hoisted uniquely-defined constants at the block top.
        // The v2 low-6 chain walk must feed CL the RAW count (v25) so the
        // whole [1]-[6] masking chain dies to DCE — the binary-patch ceiling.
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(63), imm(0)]),
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(59), imm(0xFFFF_FFFF)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(53), vreg(25)]),
            X86ISelInst::new(X86Opcode::AndRI, vec![vreg(55), vreg(53), imm(63)]),
            X86ISelInst::new(X86Opcode::MovRR32, vec![vreg32(56), vreg(55)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(57), vreg(7)]),
            X86ISelInst::new(X86Opcode::MovRR32, vec![vreg(58), vreg32(56)]),
            X86ISelInst::new(X86Opcode::AndRR, vec![vreg(60), vreg(58), vreg(59)]),
            X86ISelInst::new(X86Opcode::AndRI, vec![vreg(62), vreg(60), imm(63)]),
            X86ISelInst::new(X86Opcode::SubRR, vec![vreg(64), vreg(63), vreg(62)]),
            X86ISelInst::new(X86Opcode::AndRI, vec![vreg(65), vreg(64), imm(63)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![rcx(), vreg(62)]),
            X86ISelInst::new(X86Opcode::ShlRR, vec![vreg(66), vreg(57)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![rcx(), vreg(65)]),
            X86ISelInst::new(X86Opcode::ShrRR, vec![vreg(67), vreg(57)]),
            X86ISelInst::new(X86Opcode::OrRR, vec![vreg(68), vreg(66), vreg(67)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(70), vreg(68)]),
            X86ISelInst::new(X86Opcode::Jmp, vec![X86ISelOperand::Block(Block(0))]),
        ]);
        assert!(run_rotate_var(&mut func, |_| true));
        let ops = entry_opcodes(&func);
        assert!(ops.contains(&X86Opcode::RolRCl), "{ops:?}");
        for gone in [X86Opcode::ShlRR, X86Opcode::ShrRR, X86Opcode::SubRR] {
            assert!(!ops.contains(&gone), "{gone:?} must be deleted: {ops:?}");
        }
        assert_eq!(cl_mov_sources(&func), vec![vreg(25)]);
        let rol = entry_insts(&func)
            .iter()
            .find(|w| w.opcode == X86Opcode::RolRCl)
            .unwrap();
        assert_eq!(rol.operands.as_slice(), &[vreg(68), vreg(57)]);
    }

    #[test]
    fn rotate_var_raw_count_feed_fuses() {
        // CL is fed the RAW count directly; only the complement path masks.
        // Hardware masks CL mod 64 (the Stage-1 masked machine model), and
        // (0 - c) & 63 == (0 - (c & 63)) & 63, so both chains share the root
        // c itself.
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(3), imm(0)]),
            X86ISelInst::new(X86Opcode::SubRR, vec![vreg(5), vreg(3), vreg(1)]),
            X86ISelInst::new(X86Opcode::AndRI, vec![vreg(6), vreg(5), imm(63)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![rcx(), vreg(1)]),
            X86ISelInst::new(X86Opcode::ShlRR, vec![vreg(7), vreg(2)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![rcx(), vreg(6)]),
            X86ISelInst::new(X86Opcode::ShrRR, vec![vreg(8), vreg(2)]),
            X86ISelInst::new(X86Opcode::OrRR, vec![vreg(9), vreg(7), vreg(8)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(run_rotate_var(&mut func, |_| true));
        assert!(entry_opcodes(&func).contains(&X86Opcode::RolRCl));
        assert_eq!(cl_mov_sources(&func), vec![vreg(1)]);
    }

    #[test]
    fn rotate_var_refuses_flags_live_at_or() {
        // A Jcc consuming the OR's flags: RolRCl leaves SF/ZF/PF untouched
        // where OR defines them — the rewrite must refuse.
        let mut shape = rotate_var_v1_shape();
        shape.truncate(9); // drop the trailing copy + Ret
        shape.push(X86ISelInst::new(
            X86Opcode::Jcc,
            vec![
                X86ISelOperand::CondCode(X86CondCode::E),
                X86ISelOperand::Block(Block(0)),
            ],
        ));
        shape.push(X86ISelInst::new(X86Opcode::Ret, vec![]));
        let mut func = make_func(shape);
        assert!(!run_rotate_var(&mut func, |_| true));
        assert!(!entry_opcodes(&func).contains(&X86Opcode::RolRCl));
    }

    #[test]
    fn rotate_var_refuses_x_redefined_in_window() {
        // x is overwritten between the shifts: the rotate would read the NEW
        // value at the OR's position.
        let mut shape = rotate_var_v1_shape();
        shape.insert(6, X86ISelInst::new(X86Opcode::MovRI, vec![vreg(2), imm(5)]));
        let mut func = make_func(shape);
        assert!(!run_rotate_var(&mut func, |_| true));
    }

    #[test]
    fn rotate_var_refuses_multi_use_lo() {
        // lo has a second reader: deleting the SHL would leave it undefined.
        let mut shape = rotate_var_v1_shape();
        shape.insert(
            9,
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(11), vreg(7)]),
        );
        let mut func = make_func(shape);
        assert!(!run_rotate_var(&mut func, |_| true));
    }

    #[test]
    fn rotate_var_refuses_missing_compl_mask() {
        // The second CL mov reads the raw negation (no AndRI 63): not the
        // proven complement shape.
        let mut shape = rotate_var_v1_shape();
        shape.remove(3); // drop compl = AndRI(neg, 63)
        shape[5].operands[1] = vreg(5); // CL2 <- neg directly
        let mut func = make_func(shape);
        assert!(!run_rotate_var(&mut func, |_| true));
    }

    #[test]
    fn rotate_var_refuses_wrong_compl_mask_31() {
        // (0 - e) & 31 is a DIFFERENT rotate count than (0 - e) & 63.
        let mut shape = rotate_var_v1_shape();
        shape[3] = X86ISelInst::new(X86Opcode::AndRI, vec![vreg(6), vreg(5), imm(31)]);
        let mut func = make_func(shape);
        assert!(!run_rotate_var(&mut func, |_| true));
    }

    #[test]
    fn rotate_var_refuses_rcx_clobber_between_cl_mov_and_shift() {
        // An RCX write between the CL setup and its shift: the count the SHL
        // consumed is not the kept mov's value.
        let mut shape = rotate_var_v1_shape();
        shape.insert(5, X86ISelInst::new(X86Opcode::MovRI, vec![rcx(), imm(7)]));
        let mut func = make_func(shape);
        assert!(!run_rotate_var(&mut func, |_| true));
    }

    #[test]
    fn rotate_var_refuses_rcx_reader_after_or() {
        // A later CL consumer without its own RCX setup would observe the
        // feed value instead of compl after the rewrite (the deleted second
        // CL mov no longer executes) — the forward scan must refuse.
        let mut shape = rotate_var_v1_shape();
        shape.insert(
            9,
            X86ISelInst::new(X86Opcode::ShlRR, vec![vreg(12), vreg(13)]),
        );
        let mut func = make_func(shape);
        assert!(!run_rotate_var(&mut func, |_| true));
    }

    #[test]
    fn rotate_var_admission_gate_is_fail_closed() {
        // The proof admission callback is consulted with EXACTLY RolRCl; a
        // closed or wrong-opcode admission never fires.
        let mut closed = make_func(rotate_var_v1_shape());
        assert!(!run_rotate_var(&mut closed, |_| false));
        let mut wrong = make_func(rotate_var_v1_shape());
        assert!(!run_rotate_var(&mut wrong, |op| op == X86Opcode::RolRI));
        let mut exact = make_func(rotate_var_v1_shape());
        assert!(run_rotate_var(&mut exact, |op| op == X86Opcode::RolRCl));
        assert!(entry_opcodes(&exact).contains(&X86Opcode::RolRCl));
    }

    #[test]
    fn rotate_var_default_pass_admission_is_closed() {
        // `X86Peephole::default()` carries the closed `|_| false` admission:
        // the full pass never creates a RolRCl without an injected proof gate.
        let mut func = make_func(rotate_var_v1_shape());
        X86Peephole::default().run_on_function(&mut func);
        assert!(
            !entry_opcodes(&func).contains(&X86Opcode::RolRCl),
            "closed default admission must never create RolRCl"
        );
    }

    /// The whole-function maps of the rotate-var and RMW loops are built only
    /// for blocks holding an anchor (`OrRR`; `XorRR`/`AddRR`). A function whose
    /// entry block has no anchor, an `AddRR`-anchored RMW triple in block 1
    /// and a rotate in block 2 must still fuse both: fails when an anchor
    /// opcode is missing from the gates (the `AddRR` arm is not reached by
    /// the single-block kill-switch tests, which use `XorRR`).
    #[test]
    fn peephole_lazy_fn_maps_still_reach_every_anchor_block() {
        crate::env_lock::with_env_overrides_removed(
            &["TCG_NO_X86_RMW_FUSE", "TCG_NO_X86_ROTATE_VAR_IDIOM"],
            || {
                let mut func = make_func(vec![X86ISelInst::new(
                    X86Opcode::MovRR,
                    vec![vreg(20), vreg(21)],
                )]);
                func.ensure_block(Block(1));
                func.block_order.push(Block(1));
                for inst in rmw_triple(
                    sib_op(1, 2, 8, 0),
                    X86ISelInst::new(X86Opcode::AddRR, vec![vreg(6), vreg(5)]),
                    sib_op(1, 2, 8, 0),
                ) {
                    func.push_inst(Block(1), inst);
                }
                // The rotate's ids, shifted clear of the RMW triple's.
                let shift = |op: X86ISelOperand| match op {
                    X86ISelOperand::VReg(v) => vreg(v.id + 30),
                    other => other,
                };
                func.ensure_block(Block(2));
                func.block_order.push(Block(2));
                for inst in rotate_var_v1_shape() {
                    let operands = inst.operands.into_iter().map(shift).collect();
                    func.push_inst(Block(2), X86ISelInst::new(inst.opcode, operands));
                }
                func.next_vreg = 64;
                X86Peephole::new(|_| true).run_on_function(&mut func);
                let opcodes = |b: u32| -> Vec<X86Opcode> {
                    func.blocks[&Block(b)]
                        .insts
                        .iter()
                        .map(|i| i.opcode)
                        .collect()
                };
                assert!(
                    opcodes(1).contains(&X86Opcode::AddMRSib),
                    "AddRR-anchored RMW triple in block 1 must fuse: {:?}",
                    opcodes(1)
                );
                assert!(
                    opcodes(2).contains(&X86Opcode::RolRCl),
                    "rotate in block 2 must fuse: {:?}",
                    opcodes(2)
                );
            },
        );
    }

    /// `inst` with every register id it names, including address registers,
    /// moved up by `by`, so copies of one shape can share a function.
    fn shift_vreg_ids(inst: X86ISelInst, by: u32) -> X86ISelInst {
        fn shift(op: X86ISelOperand, by: u32) -> X86ISelOperand {
            match op {
                X86ISelOperand::VReg(v) => X86ISelOperand::VReg(VReg::new(v.id + by, v.class)),
                X86ISelOperand::MemAddr { base, disp } => X86ISelOperand::MemAddr {
                    base: Box::new(shift(*base, by)),
                    disp,
                },
                X86ISelOperand::SibMemAddr {
                    base,
                    index,
                    scale,
                    disp,
                } => X86ISelOperand::SibMemAddr {
                    base: Box::new(shift(*base, by)),
                    index: Box::new(shift(*index, by)),
                    scale,
                    disp,
                },
                other => other,
            }
        }
        let operands = inst.operands.into_iter().map(|op| shift(op, by)).collect();
        X86ISelInst::new(inst.opcode, operands)
    }

    /// Each lazily built whole-function fact (rotate-var maps, RMW-fuse maps,
    /// the scale-1 fold's use/def counts and flag liveness) is dropped after a
    /// rewrite: two copies of each fold's shape in separate blocks, so the
    /// second block reads facts built after the first block's rewrite. The
    /// test and debug builds compare every reused build with a fresh one, so
    /// a loop that keeps its facts across a rewrite fails here (mutations D,
    /// E and F of the throughput-2 report).
    #[test]
    fn peephole_lazy_fn_facts_are_rebuilt_after_each_rewrite() {
        crate::env_lock::with_env_overrides_removed(
            &[
                "TCG_NO_X86_RMW_FUSE",
                "TCG_NO_X86_ROTATE_VAR_IDIOM",
                "TCG_NO_X86_SIB_SCALE1_FOLD",
            ],
            || {
                let scale1_window = || {
                    vec![
                        X86ISelInst::new(
                            X86Opcode::ImulRRI,
                            vec![vreg(10), vreg(1), X86ISelOperand::Imm(8)],
                        ),
                        X86ISelInst::new(X86Opcode::MovRMSib, vec![vreg(3), sib_of(2, 10, 1, 0)]),
                        X86ISelInst::new(X86Opcode::CmpRR, vec![vreg(4), vreg(5)]),
                        X86ISelInst::new(X86Opcode::Ret, vec![]),
                    ]
                };
                let rmw = || {
                    rmw_triple(
                        sib_op(1, 2, 8, 0),
                        X86ISelInst::new(X86Opcode::AddRR, vec![vreg(6), vreg(5)]),
                        sib_op(1, 2, 8, 0),
                    )
                };
                let shapes: [Vec<X86ISelInst>; 6] = [
                    rotate_var_v1_shape(),
                    rotate_var_v1_shape(),
                    rmw(),
                    rmw(),
                    scale1_window(),
                    scale1_window(),
                ];
                let mut func = make_func(Vec::new());
                for (index, shape) in shapes.into_iter().enumerate() {
                    let block = Block(index as u32);
                    if index > 0 {
                        func.ensure_block(block);
                        func.block_order.push(block);
                    }
                    for inst in shape {
                        func.push_inst(block, shift_vreg_ids(inst, 32 * index as u32));
                    }
                }
                func.next_vreg = 512;
                X86Peephole::new(|_| true).run_on_function(&mut func);
                let opcodes = |b: u32| -> Vec<X86Opcode> {
                    func.blocks[&Block(b)]
                        .insts
                        .iter()
                        .map(|i| i.opcode)
                        .collect()
                };
                for b in [0, 1] {
                    assert!(
                        opcodes(b).contains(&X86Opcode::RolRCl),
                        "rotate in block {b} must fuse: {:?}",
                        opcodes(b)
                    );
                }
                for b in [2, 3] {
                    assert!(
                        opcodes(b).contains(&X86Opcode::AddMRSib),
                        "RMW triple in block {b} must fuse: {:?}",
                        opcodes(b)
                    );
                }
                for b in [4, 5] {
                    assert!(
                        !opcodes(b).contains(&X86Opcode::ImulRRI),
                        "stride in block {b} must fold into the SIB scale: {:?}",
                        opcodes(b)
                    );
                }
            },
        );
    }

    #[test]
    fn rotate_var_kill_switch_and_default_on() {
        // Full-pass runs under the lock-guarded env shim: default-ON fuses
        // (with an open admission), TCG_NO_X86_ROTATE_VAR_IDIOM=1 disables.
        crate::env_lock::with_env_overrides_removed(&["TCG_NO_X86_ROTATE_VAR_IDIOM"], || {
            assert!(rotate_var_idiom_enabled());
            let mut func = make_func(rotate_var_v1_shape());
            X86Peephole::new(|_| true).run_on_function(&mut func);
            assert!(entry_opcodes(&func).contains(&X86Opcode::RolRCl));
        });
        crate::env_lock::with_env_overrides(&[("TCG_NO_X86_ROTATE_VAR_IDIOM", "1")], || {
            assert!(!rotate_var_idiom_enabled());
            let mut func = make_func(rotate_var_v1_shape());
            X86Peephole::new(|_| true).run_on_function(&mut func);
            assert!(!entry_opcodes(&func).contains(&X86Opcode::RolRCl));
        });
    }

    #[test]
    fn zeroidiom_gate_declines_unread_zero_and_allows_read_zero() {
        // Unread MovRI-0 must stay MovRI (DCE-removable) under the gate;
        // a read zero still becomes the XorRR zero idiom.
        let unread = make_func(vec![
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(1), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(2), X86ISelOperand::Imm(0)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(3), vreg(2)]),
            // Full flag overwrite so the XorRR rewrite's flag obligation is
            // dischargeable in this toy block (as in any real body).
            X86ISelInst::new(X86Opcode::AddRR, vec![vreg(4), vreg(3), vreg(3)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(5), vreg(4)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let used = peephole_function_use_set(&unread);
        let insts = &unread.blocks.get(&Block(0)).unwrap().insts;
        // v1 unread -> gate declines.
        assert!(simplify_inst_gated(insts, 0, Some(&used), |_, _, _| false, false).is_none());
        // v2 read -> rewrite proceeds.
        assert!(matches!(
            simplify_inst_gated(insts, 1, Some(&used), |_, _, _| false, false),
            Some(PeepholeEdit::Replace(_))
        ));
        // Ungated behavior unchanged: both rewrite.
        assert!(simplify_inst(insts, 0).is_some());
    }

    #[test]
    fn addr_chain_fold_tied_addrr_dead_end_refuses() {
        // Tied `AddRR v1, v2` with v1 live-in: the base would have to be v1's
        // pre-add value, but v1 at the mem op holds the SUM. The capture
        // position makes no_def_in_range see the add's own def -> refuse.
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::AddRR, vec![vreg(1), vreg(2)]),
            X86ISelInst::new(X86Opcode::MovRM, vec![vreg(3), mem(1, 0)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(!addr_chain_fold_run_on_block(&mut func, Block(0)));
    }

    // ---- latch-advance collapse + commutative dying-source swap ----

    fn imm(v: i64) -> X86ISelOperand {
        X86ISelOperand::Imm(v)
    }

    #[test]
    fn latch_collapse_reaches_across_the_other_carried_copies() {
        // b1_mispredict's ACTUAL latch: the ISel interleaves the loop's other
        // carried copies between the advance, the write-back and the compare, so
        // an adjacency-only matcher declined it.
        //
        //   AddRI n,c,1 ; MovRR x,y ; MovRR c,n ; MovRR z,w ; CmpRI n,K ; Jcc
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::AddRI, vec![vreg(109), vreg(9), imm(1)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(11), vreg(29)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(9), vreg(109)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(10), vreg(107)]),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(109), imm(60000000)]),
            X86ISelInst::new(
                X86Opcode::Jcc,
                vec![
                    X86ISelOperand::CondCode(X86CondCode::B),
                    X86ISelOperand::Block(Block(0)),
                ],
            ),
        ]);
        let (uses, defs) = function_use_def_counts(&func);
        assert!(latch_advance_collapse_run_on_block(
            &mut func,
            Block(0),
            &uses,
            &defs,
            true
        ));
        let insts = entry_insts(&func);
        assert_eq!(insts.len(), 5, "only the write-back is gone");
        assert_eq!(insts[0].opcode, X86Opcode::AddRI);
        assert_eq!(insts[0].operands[0], vreg(9), "in-place advance on c");
        assert_eq!(insts[0].operands[1], vreg(9));
        // The unrelated copies are untouched and keep their order.
        assert_eq!(insts[1].operands.as_slice(), [vreg(11), vreg(29)]);
        assert_eq!(insts[2].operands.as_slice(), [vreg(10), vreg(107)]);
        assert_eq!(insts[3].opcode, X86Opcode::CmpRI);
        assert_eq!(insts[3].operands[0], vreg(9), "compare rewritten to read c");
    }

    #[test]
    fn latch_collapse_window_is_off_by_default() {
        // FALSIFIABILITY for the gate: with the widened window OFF — the DEFAULT
        // — both new shapes decline, so the default stream is exactly what it was
        // before the widening. The measurement that keeps it off is in
        // `latch_advance_window_enabled`'s doc (b1 +0.39%, h3_box_leak -1.7%).
        let non_adjacent = || {
            make_func(vec![
                X86ISelInst::new(X86Opcode::AddRI, vec![vreg(109), vreg(9), imm(1)]),
                X86ISelInst::new(X86Opcode::MovRR, vec![vreg(11), vreg(29)]),
                X86ISelInst::new(X86Opcode::MovRR, vec![vreg(9), vreg(109)]),
                X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(109), imm(100)]),
                X86ISelInst::new(
                    X86Opcode::Jcc,
                    vec![
                        X86ISelOperand::CondCode(X86CondCode::B),
                        X86ISelOperand::Block(Block(0)),
                    ],
                ),
            ])
        };
        let mut off = non_adjacent();
        let (uses, defs) = function_use_def_counts(&off);
        assert!(
            !latch_advance_collapse_run_on_block(&mut off, Block(0), &uses, &defs, false),
            "the non-adjacent shape must decline with the window OFF"
        );
        assert_eq!(entry_insts(&off).len(), 5);

        // And the same fixture DOES collapse with it on, so the gate is what
        // decides and the refutation above is not vacuous.
        let mut on = non_adjacent();
        let (uses, defs) = function_use_def_counts(&on);
        assert!(latch_advance_collapse_run_on_block(
            &mut on,
            Block(0),
            &uses,
            &defs,
            true
        ));
        assert_eq!(entry_insts(&on).len(), 4);
    }

    #[test]
    fn widened_latch_collapse_refuses_a_flag_reader_before_the_write_back() {
        // Rewriting the flag-NEUTRAL `Lea` spelling to `AddRI` makes the advance
        // a flag WRITER. A flag reader between the advance and the write-back
        // would then read the advance's flags instead of the ones live-in to the
        // advance — so the widened window must decline this shape. The stretch is
        // empty in the strict window, which is why only the widened path needs it.
        let lea_shape = || {
            make_func(vec![
                X86ISelInst::new(
                    X86Opcode::Lea,
                    vec![
                        vreg(109),
                        X86ISelOperand::MemAddr {
                            base: Box::new(vreg(9)),
                            disp: 1,
                        },
                    ],
                ),
                // Reads RFLAGS, and mentions neither `c` nor `n`, so the existing
                // scans admit it.
                X86ISelInst::new(
                    X86Opcode::Setcc,
                    vec![vreg(11), X86ISelOperand::CondCode(X86CondCode::E)],
                ),
                X86ISelInst::new(X86Opcode::MovRR, vec![vreg(9), vreg(109)]),
                X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(109), imm(100)]),
                X86ISelInst::new(
                    X86Opcode::Jcc,
                    vec![
                        X86ISelOperand::CondCode(X86CondCode::B),
                        X86ISelOperand::Block(Block(0)),
                    ],
                ),
            ])
        };
        let mut func = lea_shape();
        let (uses, defs) = function_use_def_counts(&func);
        assert!(
            !latch_advance_collapse_run_on_block(&mut func, Block(0), &uses, &defs, true),
            "a flag reader between a `Lea` advance and the write-back must decline"
        );
        assert_eq!(entry_insts(&func).len(), 5);

        // NON-VACUOUS, and it pins the condition to the SPELLING: the identical
        // shape with an `AddRI` advance still collapses, because that spelling
        // already wrote the flags at that position and the rewrite keeps the
        // write exactly where it was.
        let mut addri = make_func(vec![
            X86ISelInst::new(X86Opcode::AddRI, vec![vreg(109), vreg(9), imm(1)]),
            X86ISelInst::new(
                X86Opcode::Setcc,
                vec![vreg(11), X86ISelOperand::CondCode(X86CondCode::E)],
            ),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(9), vreg(109)]),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(109), imm(100)]),
            X86ISelInst::new(
                X86Opcode::Jcc,
                vec![
                    X86ISelOperand::CondCode(X86CondCode::B),
                    X86ISelOperand::Block(Block(0)),
                ],
            ),
        ]);
        let (uses, defs) = function_use_def_counts(&addri);
        assert!(
            latch_advance_collapse_run_on_block(&mut addri, Block(0), &uses, &defs, true),
            "the `AddRI` spelling introduces no new flag write, so it still collapses"
        );
        assert_eq!(entry_insts(&addri).len(), 4);
    }

    #[test]
    fn latch_collapse_refuses_when_c_is_read_before_the_write_back() {
        // THE SOUNDNESS CONDITION of the widened window. After the rewrite `c` is
        // clobbered at the advance, so any reader of `c` between the advance and
        // the write-back would observe the ADVANCED value instead of the old one.
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::AddRI, vec![vreg(109), vreg(9), imm(1)]),
            // This reads `c` — the collapse must decline.
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(11), vreg(9)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(9), vreg(109)]),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(109), imm(100)]),
            X86ISelInst::new(
                X86Opcode::Jcc,
                vec![
                    X86ISelOperand::CondCode(X86CondCode::B),
                    X86ISelOperand::Block(Block(0)),
                ],
            ),
        ]);
        let (uses, defs) = function_use_def_counts(&func);
        assert!(
            !latch_advance_collapse_run_on_block(&mut func, Block(0), &uses, &defs, true),
            "a read of c before the write-back must decline"
        );
        assert_eq!(entry_insts(&func).len(), 5, "nothing removed");
    }

    #[test]
    fn latch_collapse_refuses_when_c_is_redefined_before_the_compare() {
        // The compare is rewritten to read `c`, so `c` must still hold the
        // advanced value when it is reached.
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::AddRI, vec![vreg(109), vreg(9), imm(1)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(9), vreg(109)]),
            // Clobbers `c` between the write-back and the compare.
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(9), imm(7)]),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(109), imm(100)]),
            X86ISelInst::new(
                X86Opcode::Jcc,
                vec![
                    X86ISelOperand::CondCode(X86CondCode::B),
                    X86ISelOperand::Block(Block(0)),
                ],
            ),
        ]);
        let (uses, defs) = function_use_def_counts(&func);
        assert!(
            !latch_advance_collapse_run_on_block(&mut func, Block(0), &uses, &defs, true),
            "a redefinition of c before the compare must decline"
        );
        assert_eq!(entry_insts(&func).len(), 5, "nothing removed");
    }

    #[test]
    fn latch_collapse_accepts_the_lea_spelling_of_the_advance() {
        // `Lea n,[c+1] ; MovRR c,n ; CmpRI n,K ; Jcc` — the shape
        // `b1_mispredict` ships (`lea 0x1(%rdi),%rax ; mov %rax,%rdi ;
        // cmp $K,%rax ; jb`), present in 8 of the 18 beat-llvm programs. The
        // `AddRI` spelling was already handled; this is the flag-neutral one.
        //
        // Folding `Lea` to `AddRI` INTRODUCES a flag write, discharged by the
        // window itself: the matched `Cmp` is immediately after (the `MovRR`
        // between them is deleted) and fully overwrites the flags before the
        // matched `Jcc` reads them.
        let mut func = make_func(vec![
            X86ISelInst::new(
                X86Opcode::Lea,
                vec![
                    vreg(5),
                    X86ISelOperand::MemAddr {
                        base: Box::new(vreg(1)),
                        disp: 1,
                    },
                ],
            ),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(1), vreg(5)]),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(5), imm(0x3938700)]),
            X86ISelInst::new(
                X86Opcode::Jcc,
                vec![
                    X86ISelOperand::CondCode(X86CondCode::B),
                    X86ISelOperand::Block(Block(0)),
                ],
            ),
        ]);
        let (uses, defs) = function_use_def_counts(&func);
        assert!(latch_advance_collapse_run_on_block(
            &mut func,
            Block(0),
            &uses,
            &defs,
            true
        ));
        let insts = entry_insts(&func);
        assert_eq!(insts.len(), 3, "the MovRR write-back is gone");
        assert_eq!(
            insts[0].opcode,
            X86Opcode::AddRI,
            "the Lea is rebuilt as the in-place AddRI"
        );
        assert_eq!(insts[0].operands[0], vreg(1), "in-place advance");
        assert_eq!(insts[0].operands[1], vreg(1));
        assert_eq!(insts[0].operands[2], imm(1), "displacement carried across");
        assert_eq!(insts[1].opcode, X86Opcode::CmpRI);
        assert_eq!(insts[1].operands[0], vreg(1), "compare reads c");
    }

    #[test]
    fn latch_collapse_refuses_a_lea_whose_temp_escapes_the_window() {
        // FALSIFIABILITY for the arm above: `n` must exist only inside the
        // window (one def, exactly two uses). Give the temp a third use and the
        // collapse must decline, because deleting the write-back would leave
        // that reader looking at a vreg nothing defines.
        let mut func = make_func(vec![
            X86ISelInst::new(
                X86Opcode::Lea,
                vec![
                    vreg(5),
                    X86ISelOperand::MemAddr {
                        base: Box::new(vreg(1)),
                        disp: 1,
                    },
                ],
            ),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(1), vreg(5)]),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(5), imm(100)]),
            X86ISelInst::new(
                X86Opcode::Jcc,
                vec![
                    X86ISelOperand::CondCode(X86CondCode::B),
                    X86ISelOperand::Block(Block(0)),
                ],
            ),
            // The extra use.
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(9), vreg(5)]),
        ]);
        let (uses, defs) = function_use_def_counts(&func);
        assert!(!latch_advance_collapse_run_on_block(
            &mut func,
            Block(0),
            &uses,
            &defs,
            true
        ));
        assert_eq!(entry_insts(&func).len(), 5, "nothing removed");
    }

    #[test]
    fn latch_collapse_rewrites_the_counted_loop_latch() {
        // AddRI n,c,1 ; MovRR c,n ; CmpRI n,100 ; Jcc  ->  in-place advance.
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::AddRI, vec![vreg(5), vreg(1), imm(1)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(1), vreg(5)]),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(5), imm(100)]),
            X86ISelInst::new(
                X86Opcode::Jcc,
                vec![
                    X86ISelOperand::CondCode(X86CondCode::B),
                    X86ISelOperand::Block(Block(0)),
                ],
            ),
        ]);
        let (uses, defs) = function_use_def_counts(&func);
        assert!(latch_advance_collapse_run_on_block(
            &mut func,
            Block(0),
            &uses,
            &defs,
            true
        ));
        let insts = entry_insts(&func);
        assert_eq!(insts.len(), 3, "the MovRR write-back is gone");
        assert_eq!(insts[0].opcode, X86Opcode::AddRI);
        assert_eq!(insts[0].operands[0], vreg(1), "in-place advance");
        assert_eq!(insts[1].opcode, X86Opcode::CmpRI);
        assert_eq!(insts[1].operands[0], vreg(1), "compare reads c");
    }

    #[test]
    fn latch_collapse_declines_when_the_fresh_vreg_escapes() {
        // An extra read of n after the window keeps the original shape.
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::AddRI, vec![vreg(5), vreg(1), imm(1)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(1), vreg(5)]),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(5), imm(100)]),
            X86ISelInst::new(
                X86Opcode::Jcc,
                vec![
                    X86ISelOperand::CondCode(X86CondCode::B),
                    X86ISelOperand::Block(Block(0)),
                ],
            ),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(9), vreg(5)]),
        ]);
        let (uses, defs) = function_use_def_counts(&func);
        assert!(!latch_advance_collapse_run_on_block(
            &mut func,
            Block(0),
            &uses,
            &defs,
            true
        ));
        assert_eq!(entry_insts(&func).len(), 5);
    }

    #[test]
    fn latch_collapse_declines_a_bound_equal_to_the_counter() {
        // CmpRR n, c would read c's OLD value pre-collapse; decline.
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::AddRI, vec![vreg(5), vreg(1), imm(1)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(1), vreg(5)]),
            X86ISelInst::new(X86Opcode::CmpRR, vec![vreg(5), vreg(1)]),
            X86ISelInst::new(
                X86Opcode::Jcc,
                vec![
                    X86ISelOperand::CondCode(X86CondCode::B),
                    X86ISelOperand::Block(Block(0)),
                ],
            ),
        ]);
        let (uses, defs) = function_use_def_counts(&func);
        assert!(!latch_advance_collapse_run_on_block(
            &mut func,
            Block(0),
            &uses,
            &defs,
            true
        ));
    }

    #[test]
    fn commute_swaps_the_dying_source_first() {
        // x (vreg 1) is read twice; t (vreg 5) dies at the xor: swap so the
        // two-address tie copies the dying t.
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::ShlRI, vec![vreg(5), vreg(1), imm(13)]),
            X86ISelInst::new(X86Opcode::XorRR, vec![vreg(6), vreg(1), vreg(5)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(9), vreg(1)]),
        ]);
        let (uses, defs) = function_use_def_counts(&func);
        assert!(commute_dying_source_run_on_block(
            &mut func,
            Block(0),
            &uses,
            &defs
        ));
        let insts = entry_insts(&func);
        assert_eq!(insts[1].operands[1], vreg(5), "dying t first (tied)");
        assert_eq!(insts[1].operands[2], vreg(1), "live x second");
    }

    #[test]
    fn commute_leaves_an_already_dying_first_source() {
        // Both sources dying, or s1 dying: no churn.
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::ShlRI, vec![vreg(5), vreg(1), imm(13)]),
            X86ISelInst::new(X86Opcode::ShlRI, vec![vreg(6), vreg(1), imm(7)]),
            X86ISelInst::new(X86Opcode::XorRR, vec![vreg(7), vreg(5), vreg(6)]),
        ]);
        let (uses, defs) = function_use_def_counts(&func);
        assert!(!commute_dying_source_run_on_block(
            &mut func,
            Block(0),
            &uses,
            &defs
        ));
    }

    #[test]
    fn constmul_three_becomes_one_lea() {
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::ImulRRI, vec![vreg(2), vreg(1), imm(3)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(9), vreg(2)]),
            // A full flag overwrite proves the IMUL's flags dead.
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(9), imm(0)]),
        ]);
        let mut pass = X86Peephole::default();
        assert!(pass.run(&mut func));
        let ops = entry_opcodes(&func);
        assert!(ops.contains(&X86Opcode::LeaSib), "3x -> one LEA: {ops:?}");
        assert!(!ops.contains(&X86Opcode::ImulRRI));
    }

    #[test]
    fn constmul_seven_becomes_two_leas() {
        // d = 7s as lea d,[s+s*2] (=3s) then lea d,[s+d*2] (=7s): 2 cycles,
        // no reg-reg mov on the chain, d doubles as the temporary.
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::ImulRRI, vec![vreg(2), vreg(1), imm(7)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(9), vreg(2)]),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(9), imm(0)]),
        ]);
        let mut pass = X86Peephole::default();
        assert!(pass.run(&mut func));
        let insts = entry_insts(&func);
        let first = insts
            .iter()
            .position(|i| i.opcode == X86Opcode::LeaSib)
            .expect("lea d,[s+s*2]");
        assert_eq!(insts[first].operands[0], vreg(2));
        assert_eq!(
            insts[first].operands[1],
            X86ISelOperand::SibMemAddr {
                base: Box::new(vreg(1)),
                index: Box::new(vreg(1)),
                scale: 2,
                disp: 0,
            }
        );
        assert_eq!(
            insts[first + 1].opcode,
            X86Opcode::LeaSib,
            "then lea d,[s+d*2]"
        );
        assert_eq!(
            insts[first + 1].operands[1],
            X86ISelOperand::SibMemAddr {
                base: Box::new(vreg(1)),
                index: Box::new(vreg(2)),
                scale: 2,
                disp: 0,
            }
        );
        assert!(!entry_opcodes(&func).contains(&X86Opcode::ImulRRI));
    }

    #[test]
    fn constmul_declines_when_imul_flags_are_read() {
        // A Jcc consuming the IMUL's flags: the rewrite would change them.
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::ImulRRI, vec![vreg(2), vreg(1), imm(3)]),
            X86ISelInst::new(
                X86Opcode::Jcc,
                vec![
                    X86ISelOperand::CondCode(X86CondCode::O),
                    X86ISelOperand::Block(Block(0)),
                ],
            ),
        ]);
        let mut pass = X86Peephole::default();
        pass.run(&mut func);
        assert!(
            entry_opcodes(&func).contains(&X86Opcode::ImulRRI),
            "flag-consumed IMUL must survive"
        );
    }

    #[test]
    fn constmul_declines_tied_seven() {
        // d == s: d-as-temp would destroy the source; keep the IMUL.
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::ImulRRI, vec![vreg(1), vreg(1), imm(7)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(9), vreg(1)]),
        ]);
        let mut pass = X86Peephole::default();
        pass.run(&mut func);
        assert!(entry_opcodes(&func).contains(&X86Opcode::ImulRRI));
    }

    #[test]
    fn constmul_seven_fires_through_partial_flag_writer() {
        // The p5_struct_acc hot-block shape: a RolRI (partial CF/OF writer,
        // reads no flags) sits between the IMUL and the XorRR full
        // overwrite. The deadness scan must continue THROUGH the partial
        // writer and fire on the full overwrite.
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::ImulRRI, vec![vreg(2), vreg(1), imm(7)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(3), vreg(2)]),
            X86ISelInst::new(X86Opcode::RolRI, vec![vreg(4), vreg(3), imm(9)]),
            X86ISelInst::new(X86Opcode::XorRR, vec![vreg(5), vreg(6), vreg(4)]),
        ]);
        let mut pass = X86Peephole::default();
        assert!(pass.run(&mut func));
        let ops = entry_opcodes(&func);
        assert!(ops.contains(&X86Opcode::LeaSib), "7x fires: {ops:?}");
        assert!(!ops.contains(&X86Opcode::ImulRRI));
    }

    #[test]
    fn constmul_declines_when_reader_follows_partial_writer() {
        // A flags reader after the partial writer with NO full overwrite in
        // between: the reader could still observe the IMUL's SF/ZF/PF, so
        // the scan must still fail closed.
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::ImulRRI, vec![vreg(2), vreg(1), imm(7)]),
            X86ISelInst::new(X86Opcode::RolRI, vec![vreg(4), vreg(3), imm(9)]),
            X86ISelInst::new(
                X86Opcode::Jcc,
                vec![
                    X86ISelOperand::CondCode(X86CondCode::S),
                    X86ISelOperand::Block(Block(0)),
                ],
            ),
        ]);
        let mut pass = X86Peephole::default();
        pass.run(&mut func);
        assert!(
            entry_opcodes(&func).contains(&X86Opcode::ImulRRI),
            "reader past a partial writer must keep the IMUL"
        );
    }

    // ---- constmul 2^a +/- 1 -> SHL ; ADD/SUB -----------------------------

    /// The p5_struct_acc shape: `IMUL d, s, $31` with dead flags and `d != s`
    /// becomes `SHL d, s, 5 ; SUB d, d, s`.
    #[test]
    fn constmul_thirty_one_becomes_shl_sub() {
        let insts = vec![
            X86ISelInst::new(X86Opcode::ImulRRI, vec![vreg(2), vreg(1), imm(31)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(9), vreg(2)]),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(9), imm(0)]),
        ];
        let Some(PeepholeEdit::ReplaceTwo(shl, sub)) = simplify_inst_constmul_admitted(&insts, 0)
        else {
            panic!("x31 must rewrite to SHL+SUB");
        };
        assert_eq!(shl.opcode, X86Opcode::ShlRI);
        assert_eq!(shl.operands, vec![vreg(2), vreg(1), imm(5)]);
        assert_eq!(sub.opcode, X86Opcode::SubRR);
        assert_eq!(sub.operands, vec![vreg(2), vreg(2), vreg(1)]);
    }

    /// `2^a + 1` takes the ADD form. `33 = 32 + 1`.
    #[test]
    fn constmul_thirty_three_becomes_shl_add() {
        let insts = vec![
            X86ISelInst::new(X86Opcode::ImulRRI, vec![vreg(2), vreg(1), imm(33)]),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(9), imm(0)]),
        ];
        let Some(PeepholeEdit::ReplaceTwo(shl, add)) = simplify_inst_constmul_admitted(&insts, 0)
        else {
            panic!("x33 must rewrite to SHL+ADD");
        };
        assert_eq!(shl.operands, vec![vreg(2), vreg(1), imm(5)]);
        assert_eq!(add.opcode, X86Opcode::AddRR);
        assert_eq!(add.operands, vec![vreg(2), vreg(2), vreg(1)]);
    }

    /// The ONE-SHIFT restriction: two-shift constants (`24 = 16+8`,
    /// `126 = 128-2`, `13`) and the pure powers of two Stage 1 deliberately
    /// leaves alone must all keep the IMUL.
    #[test]
    fn constmul_shift_bails_on_two_shift_and_power_of_two_constants() {
        for c in [24i64, 126, 13, 14, 100, 576, 61, 37, 8, 4096] {
            let insts = vec![
                X86ISelInst::new(X86Opcode::ImulRRI, vec![vreg(2), vreg(1), imm(c)]),
                X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(9), imm(0)]),
            ];
            assert!(
                simplify_inst_constmul_admitted(&insts, 0).is_none(),
                "x{c} must NOT be claimed by the one-shift arm"
            );
        }
        // x2: no arm claims it when certificates are kept; in a
        // certificate-free compile the doubling-LEA arm claims it before the
        // one-shift arm.
        let insts = vec![
            X86ISelInst::new(X86Opcode::ImulRRI, vec![vreg(2), vreg(1), imm(2)]),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(9), imm(0)]),
        ];
        assert!(simplify_inst_constmul_admitted(&insts, 0).is_none());
        assert!(matches!(
            simplify_inst_constmul_admitted_certificate_free(&insts, 0),
            Some(PeepholeEdit::Replace(ref lea)) if lea.opcode == X86Opcode::LeaSib
        ));
    }

    /// `1 - 2^a` (e.g. `-31`) is excluded on x86: it would need
    /// `SUB d, s, d`, the `dst == rhs` alias that routes into the two-address
    /// scratch path.
    #[test]
    fn constmul_shift_bails_on_one_minus_two_pow_a() {
        let insts = vec![
            X86ISelInst::new(X86Opcode::ImulRRI, vec![vreg(2), vreg(1), imm(-31)]),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(9), imm(0)]),
        ];
        assert!(simplify_inst_constmul_admitted(&insts, 0).is_none());
    }

    /// `d == s`: the SHL would clobber the source the ADD/SUB still needs.
    #[test]
    fn constmul_shift_declines_tied_destination() {
        let insts = vec![
            X86ISelInst::new(X86Opcode::ImulRRI, vec![vreg(1), vreg(1), imm(31)]),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(9), imm(0)]),
        ];
        assert!(simplify_inst_constmul_admitted(&insts, 0).is_none());
    }

    /// Live IMUL flags: the guard the arm shares with the LEA arms.
    #[test]
    fn constmul_shift_declines_when_imul_flags_are_read() {
        let insts = vec![
            X86ISelInst::new(X86Opcode::ImulRRI, vec![vreg(2), vreg(1), imm(31)]),
            X86ISelInst::new(
                X86Opcode::Jcc,
                vec![
                    X86ISelOperand::CondCode(X86CondCode::O),
                    X86ISelOperand::Block(Block(0)),
                ],
            ),
        ];
        assert!(simplify_inst_constmul_admitted(&insts, 0).is_none());
    }

    /// FAIL-CLOSED on the proof: an undischarged algebraic obligation leaves
    /// the IMUL standing. This is what `X86Peephole::default` / `::new` see.
    #[test]
    fn constmul_shift_fails_closed_without_the_admission() {
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::ImulRRI, vec![vreg(2), vreg(1), imm(31)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(9), vreg(2)]),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(9), imm(0)]),
        ]);
        let mut pass = X86Peephole::default();
        pass.run(&mut func);
        let ops = entry_opcodes(&func);
        assert!(
            ops.contains(&X86Opcode::ImulRRI),
            "unadmitted identity must keep the IMUL: {ops:?}"
        );
        assert!(!ops.contains(&X86Opcode::ShlRI));
    }

    /// End to end through the pass with the admission wired: the IMUL is gone
    /// and the SHL+SUB pair is in the block.
    ///
    /// ⚑ The `TCG_NO_X86_CONSTMUL_SHIFT` kill switch is deliberately NOT
    /// exercised here. trust-cg-opt has no process-wide env test lock (the
    /// codegen crate's `env_lock` is not available), and every other test in
    /// this module reaches the same arm, so mutating the variable in-process
    /// would race them. The switch is read UNCACHED per call
    /// (`constmul_shift_enabled`) and is validated by the paired A/B that
    /// gates landing.
    #[test]
    fn constmul_shift_fires_through_the_pass_when_admitted() {
        let mut func = make_func(vec![
            X86ISelInst::new(X86Opcode::ImulRRI, vec![vreg(2), vreg(1), imm(31)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(9), vreg(2)]),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(9), imm(0)]),
        ]);
        assert!(X86Peephole::with_admissions(|_| false, |_, _, _| true).run(&mut func));
        let ops = entry_opcodes(&func);
        assert!(ops.contains(&X86Opcode::ShlRI), "arm fires: {ops:?}");
        assert!(ops.contains(&X86Opcode::SubRR));
        assert!(!ops.contains(&X86Opcode::ImulRRI));
    }

    /// Width is taken from the DESTINATION class and the immediate re-signed
    /// at that width: a 32-bit `-31` arrives zero-extended as `0xFFFF_FFE1`
    /// and must still be REFUSED (it is `1 - 2^5`), not misread as a huge
    /// positive constant.
    #[test]
    fn constmul_shift_resigns_the_immediate_at_gpr32_width() {
        let claimed = vec![
            X86ISelInst::new(X86Opcode::ImulRRI, vec![vreg32(2), vreg32(1), imm(31)]),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg32(9), imm(0)]),
        ];
        let Some(PeepholeEdit::ReplaceTwo(shl, _)) = simplify_inst_constmul_admitted(&claimed, 0)
        else {
            panic!("32-bit x31 must rewrite");
        };
        assert_eq!(shl.operands[2], imm(5));

        let resigned = vec![
            X86ISelInst::new(
                X86Opcode::ImulRRI,
                vec![vreg32(2), vreg32(1), imm(0xFFFF_FFE1u32 as i64)],
            ),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg32(9), imm(0)]),
        ];
        assert!(simplify_inst_constmul_admitted(&resigned, 0).is_none());
    }

    /// The decomposer itself, pinned independently of the pass plumbing.
    #[test]
    fn constmul_shift_decompose_claims_exactly_two_pow_a_plus_minus_one() {
        assert_eq!(constmul_shift_decompose(31, 64), Some((5, false)));
        assert_eq!(constmul_shift_decompose(33, 64), Some((5, true)));
        assert_eq!(constmul_shift_decompose(3, 64), Some((1, true)));
        assert_eq!(constmul_shift_decompose(7, 64), Some((3, false)));
        assert_eq!(constmul_shift_decompose(63, 32), Some((6, false)));
        // Two-shift, pure powers, `1 - 2^a`, and the degenerate multipliers.
        for c in [24i128, 576, 14, 13, 100, 126, 2, 8, -31, -3, 0, 1, -1] {
            assert_eq!(
                constmul_shift_decompose(c, 64),
                None,
                "x{c} must not decompose"
            );
        }
        // Shift amount must stay in range at the operation width: `2^32 + 1`
        // would need `a = 32`, which is not `< width`.
        assert_eq!(constmul_shift_decompose((1i128 << 32) + 1, 32), None);
        assert_eq!(
            constmul_shift_decompose((1i128 << 31) - 1, 32),
            Some((31, false))
        );
    }

    #[test]
    fn lea_disp_fold_merges_the_add_one() {
        // lea (c,c,2),t ; add t,1 -> x  ==>  lea 1(c,c,2),x
        let mut func = make_func(vec![
            X86ISelInst::new(
                X86Opcode::LeaSib,
                vec![
                    vreg(5),
                    X86ISelOperand::SibMemAddr {
                        base: Box::new(vreg(1)),
                        index: Box::new(vreg(1)),
                        scale: 2,
                        disp: 0,
                    },
                ],
            ),
            X86ISelInst::new(X86Opcode::AddRI, vec![vreg(6), vreg(5), imm(1)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(9), vreg(6)]),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(9), imm(0)]),
        ]);
        let (uses, defs) = function_use_def_counts(&func);
        assert!(lea_disp_fold_run_on_block(
            &mut func,
            Block(0),
            &uses,
            &defs
        ));
        let insts = entry_insts(&func);
        assert_eq!(insts[0].opcode, X86Opcode::LeaSib);
        assert_eq!(insts[0].operands[0], vreg(6), "LEA now defines x");
        assert!(
            matches!(
                &insts[0].operands[1],
                X86ISelOperand::SibMemAddr { disp: 1, .. }
            ),
            "displacement folded"
        );
        assert_ne!(insts[1].opcode, X86Opcode::AddRI, "the AddRI is gone");
    }

    #[test]
    fn lea_disp_fold_declines_a_multi_use_lea() {
        // t read again later: keep both instructions.
        let mut func = make_func(vec![
            X86ISelInst::new(
                X86Opcode::LeaSib,
                vec![
                    vreg(5),
                    X86ISelOperand::SibMemAddr {
                        base: Box::new(vreg(1)),
                        index: Box::new(vreg(1)),
                        scale: 2,
                        disp: 0,
                    },
                ],
            ),
            X86ISelInst::new(X86Opcode::AddRI, vec![vreg(6), vreg(5), imm(1)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(9), vreg(5)]),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(9), imm(0)]),
        ]);
        let (uses, defs) = function_use_def_counts(&func);
        assert!(!lea_disp_fold_run_on_block(
            &mut func,
            Block(0),
            &uses,
            &defs
        ));
    }

    #[test]
    fn lea_disp_fold_declines_when_add_flags_are_read() {
        let mut func = make_func(vec![
            X86ISelInst::new(
                X86Opcode::LeaSib,
                vec![
                    vreg(5),
                    X86ISelOperand::SibMemAddr {
                        base: Box::new(vreg(1)),
                        index: Box::new(vreg(1)),
                        scale: 2,
                        disp: 0,
                    },
                ],
            ),
            X86ISelInst::new(X86Opcode::AddRI, vec![vreg(6), vreg(5), imm(1)]),
            X86ISelInst::new(
                X86Opcode::Jcc,
                vec![
                    X86ISelOperand::CondCode(X86CondCode::O),
                    X86ISelOperand::Block(Block(0)),
                ],
            ),
        ]);
        let (uses, defs) = function_use_def_counts(&func);
        assert!(!lea_disp_fold_run_on_block(
            &mut func,
            Block(0),
            &uses,
            &defs
        ));
    }

    // ===================================================================
    // SIB scale-1 index fold (the explicit-stride-multiply dialect)
    // ===================================================================

    fn sib_of(base_id: u32, index_id: u32, scale: u8, disp: i32) -> X86ISelOperand {
        X86ISelOperand::SibMemAddr {
            base: Box::new(vreg(base_id)),
            index: Box::new(vreg(index_id)),
            scale,
            disp,
        }
    }

    /// The shape the existing fold has no anchor for: an explicit stride
    /// multiply feeding a SIB that ALREADY does the base addition at scale 1.
    ///   imul v10, v1(index), k
    ///   mov  v3, [v2 + v10*1]
    ///   cmp  v4, v5        ; full-flag overwrite => the imul's flags are dead
    ///   ret
    fn scale1_load_window(scale_op: X86Opcode, imm: i64, sib_scale: u8) -> X86ISelFunction {
        make_func(vec![
            X86ISelInst::new(scale_op, vec![vreg(10), vreg(1), X86ISelOperand::Imm(imm)]),
            X86ISelInst::new(
                X86Opcode::MovRMSib,
                vec![vreg(3), sib_of(2, 10, sib_scale, 0)],
            ),
            X86ISelInst::new(X86Opcode::CmpRR, vec![vreg(4), vreg(5)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ])
    }

    fn only_sib(func: &X86ISelFunction) -> (u8, u32) {
        for inst in entry_insts(func) {
            for op in &inst.operands {
                if let X86ISelOperand::SibMemAddr { index, scale, .. } = op
                    && let X86ISelOperand::VReg(v) = index.as_ref()
                {
                    return (*scale, v.id);
                }
            }
        }
        panic!("no SIB operand found");
    }

    #[test]
    fn scale1_fold_moves_an_imul_stride_into_the_sib_scale() {
        let mut func = scale1_load_window(X86Opcode::ImulRRI, 8, 1);
        let counts = FnUseDefCounts::build(&func);
        let flags = X86FlagLiveness::analyze(&func);
        assert!(sib_scale1_index_fold_run_on_block(
            &mut func,
            Block(0),
            &counts,
            &flags
        ));
        let insts = entry_insts(&func);
        assert_eq!(
            insts
                .iter()
                .filter(|i| i.opcode == X86Opcode::ImulRRI)
                .count(),
            0,
            "the multiply is retired"
        );
        // The SIB now scales the ORIGINAL index by 8.
        assert_eq!(only_sib(&func), (8, 1));
    }

    /// The full pass builds the fold's counts and flag liveness only for a
    /// block with a candidate multiply; both spellings must still be found
    /// and folded through `run_on_function`. Fails when the candidate
    /// predicate misses a spelling the fold accepts.
    #[test]
    fn scale1_fold_candidate_gate_admits_both_spellings_through_the_pass() {
        crate::env_lock::with_env_overrides_removed(&["TCG_NO_X86_SIB_SCALE1_FOLD"], || {
            for (op, imm) in [(X86Opcode::ImulRRI, 8), (X86Opcode::ShlRI, 3)] {
                let mut func = scale1_load_window(op, imm, 1);
                assert!(block_has_sib_scale_candidate(&func, Block(0)));
                X86Peephole::default().run_on_function(&mut func);
                assert!(
                    !entry_opcodes(&func).contains(&op),
                    "{op:?} stride must be folded: {:?}",
                    entry_opcodes(&func)
                );
                assert_eq!(only_sib(&func), (8, 1));
            }
            // A multiply by 1 is no candidate (the fold skips scale 1).
            let unit = scale1_load_window(X86Opcode::ImulRRI, 1, 1);
            assert!(!block_has_sib_scale_candidate(&unit, Block(0)));
        });
    }

    #[test]
    fn scale1_fold_handles_the_shl_spelling() {
        let mut func = scale1_load_window(X86Opcode::ShlRI, 3, 1);
        let counts = FnUseDefCounts::build(&func);
        let flags = X86FlagLiveness::analyze(&func);
        assert!(sib_scale1_index_fold_run_on_block(
            &mut func,
            Block(0),
            &counts,
            &flags
        ));
        assert_eq!(only_sib(&func), (8, 1));
    }

    #[test]
    fn scale1_fold_declines_when_the_sib_scale_is_not_one() {
        // `[base + (index*8)*2]` is not `[base + index*8]`; only scale 1 is a
        // pure pass-through of the pre-scaled value.
        let mut func = scale1_load_window(X86Opcode::ImulRRI, 8, 2);
        let counts = FnUseDefCounts::build(&func);
        let flags = X86FlagLiveness::analyze(&func);
        assert!(!sib_scale1_index_fold_run_on_block(
            &mut func,
            Block(0),
            &counts,
            &flags
        ));
        assert_eq!(only_sib(&func), (2, 10), "untouched");
    }

    #[test]
    fn scale1_fold_declines_a_non_power_of_two_stride() {
        // A stride of 24 (a 24-byte element) has no SIB encoding.
        let mut func = scale1_load_window(X86Opcode::ImulRRI, 24, 1);
        let counts = FnUseDefCounts::build(&func);
        let flags = X86FlagLiveness::analyze(&func);
        assert!(!sib_scale1_index_fold_run_on_block(
            &mut func,
            Block(0),
            &counts,
            &flags
        ));
        assert_eq!(only_sib(&func), (1, 10), "untouched");
    }

    #[test]
    fn scale1_fold_declines_when_the_multiplied_source_is_redefined_between() {
        // `imul v10, v1, 8 ; v1 = ... ; mov v3,[v2+v10*1]` — rewriting the SIB to
        // index on v1 would read the NEW v1, not the value that was multiplied.
        let mut func = make_func(vec![
            X86ISelInst::new(
                X86Opcode::ImulRRI,
                vec![vreg(10), vreg(1), X86ISelOperand::Imm(8)],
            ),
            X86ISelInst::new(X86Opcode::MovRI, vec![vreg(1), X86ISelOperand::Imm(7)]),
            X86ISelInst::new(X86Opcode::MovRMSib, vec![vreg(3), sib_of(2, 10, 1, 0)]),
            X86ISelInst::new(X86Opcode::CmpRR, vec![vreg(4), vreg(5)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let counts = FnUseDefCounts::build(&func);
        let flags = X86FlagLiveness::analyze(&func);
        assert!(
            !sib_scale1_index_fold_run_on_block(&mut func, Block(0), &counts, &flags),
            "a redefined stride source must block the fold"
        );
        assert_eq!(only_sib(&func), (1, 10), "untouched");
    }

    #[test]
    fn scale1_fold_declines_when_the_multiply_flags_are_live() {
        // No full-flag overwrite before a flag READER: deleting the imul would
        // change what the reader sees.
        let mut func = make_func(vec![
            X86ISelInst::new(
                X86Opcode::ImulRRI,
                vec![vreg(10), vreg(1), X86ISelOperand::Imm(8)],
            ),
            X86ISelInst::new(X86Opcode::MovRMSib, vec![vreg(3), sib_of(2, 10, 1, 0)]),
            X86ISelInst::new(
                X86Opcode::Jcc,
                vec![
                    X86ISelOperand::CondCode(X86CondCode::O),
                    X86ISelOperand::Block(Block(1)),
                ],
            ),
        ]);
        let counts = FnUseDefCounts::build(&func);
        let flags = X86FlagLiveness::analyze(&func);
        assert!(
            !sib_scale1_index_fold_run_on_block(&mut func, Block(0), &counts, &flags),
            "live multiply flags must block the fold"
        );
        assert_eq!(only_sib(&func), (1, 10), "untouched");
    }

    #[test]
    fn scale1_fold_rewrites_every_use_of_a_shared_index() {
        // `c[i] = c[i] + ..` — a load and a store share one pre-scaled index.
        // Both SIBs are rewritten and the single multiply retires. This is the
        // read-modify-write shape a matmul inner loop presents.
        let mut func = make_func(vec![
            X86ISelInst::new(
                X86Opcode::ImulRRI,
                vec![vreg(10), vreg(1), X86ISelOperand::Imm(8)],
            ),
            X86ISelInst::new(X86Opcode::MovRMSib, vec![vreg(3), sib_of(2, 10, 1, 0)]),
            X86ISelInst::new(X86Opcode::MovMRSib, vec![sib_of(2, 10, 1, 0), vreg(3)]),
            X86ISelInst::new(X86Opcode::CmpRR, vec![vreg(4), vreg(5)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let counts = FnUseDefCounts::build(&func);
        let flags = X86FlagLiveness::analyze(&func);
        assert!(sib_scale1_index_fold_run_on_block(
            &mut func,
            Block(0),
            &counts,
            &flags
        ));
        let insts = entry_insts(&func);
        assert_eq!(
            insts
                .iter()
                .filter(|i| i.opcode == X86Opcode::ImulRRI)
                .count(),
            0,
            "the shared multiply retires once every use is rewritten"
        );
        // BOTH memory ops now index on the original vreg at scale 8.
        let sibs: Vec<(u8, u32)> = insts
            .iter()
            .flat_map(|i| i.operands.iter())
            .filter_map(|o| match o {
                X86ISelOperand::SibMemAddr { index, scale, .. } => match index.as_ref() {
                    X86ISelOperand::VReg(v) => Some((*scale, v.id)),
                    _ => None,
                },
                _ => None,
            })
            .collect();
        assert_eq!(sibs, vec![(8, 1), (8, 1)]);
    }

    #[test]
    fn scale1_fold_declines_when_the_index_is_also_the_stored_value() {
        // `mov [base + v*1], v` — the multiplied value is BOTH the address index
        // and the datum. Retiring the multiply would store the wrong number.
        let mut func = make_func(vec![
            X86ISelInst::new(
                X86Opcode::ImulRRI,
                vec![vreg(10), vreg(1), X86ISelOperand::Imm(8)],
            ),
            X86ISelInst::new(X86Opcode::MovMRSib, vec![sib_of(2, 10, 1, 0), vreg(10)]),
            X86ISelInst::new(X86Opcode::CmpRR, vec![vreg(4), vreg(5)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let counts = FnUseDefCounts::build(&func);
        let flags = X86FlagLiveness::analyze(&func);
        assert!(
            !sib_scale1_index_fold_run_on_block(&mut func, Block(0), &counts, &flags),
            "an index that is also the stored value must block the fold"
        );
        assert_eq!(only_sib(&func), (1, 10), "untouched");
    }

    #[test]
    fn scale1_fold_declines_when_the_index_is_used_as_a_sib_base() {
        // As a BASE the value is not scaled by the SIB, so it still needs the
        // multiply.
        let mut func = make_func(vec![
            X86ISelInst::new(
                X86Opcode::ImulRRI,
                vec![vreg(10), vreg(1), X86ISelOperand::Imm(8)],
            ),
            X86ISelInst::new(X86Opcode::MovRMSib, vec![vreg(3), sib_of(10, 2, 1, 0)]),
            X86ISelInst::new(X86Opcode::CmpRR, vec![vreg(4), vreg(5)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let counts = FnUseDefCounts::build(&func);
        let flags = X86FlagLiveness::analyze(&func);
        assert!(!sib_scale1_index_fold_run_on_block(
            &mut func,
            Block(0),
            &counts,
            &flags
        ));
    }

    #[test]
    fn scale1_fold_declines_when_a_use_escapes_the_block() {
        // The whole-function use count exceeds what this block accounts for, so
        // some other block still needs the multiplied value.
        let mut func = make_func(vec![
            X86ISelInst::new(
                X86Opcode::ImulRRI,
                vec![vreg(10), vreg(1), X86ISelOperand::Imm(8)],
            ),
            X86ISelInst::new(X86Opcode::MovRMSib, vec![vreg(3), sib_of(2, 10, 1, 0)]),
            X86ISelInst::new(X86Opcode::CmpRR, vec![vreg(4), vreg(5)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        // A second block consuming the pre-scaled value.
        let b1 = Block(1);
        func.ensure_block(b1);
        func.push_inst(
            b1,
            X86ISelInst::new(X86Opcode::AddRR, vec![vreg(7), vreg(8), vreg(10)]),
        );
        let counts = FnUseDefCounts::build(&func);
        let flags = X86FlagLiveness::analyze(&func);
        assert!(
            !sib_scale1_index_fold_run_on_block(&mut func, Block(0), &counts, &flags),
            "a use outside this block must block the fold"
        );
        assert_eq!(only_sib(&func), (1, 10), "untouched");
    }

    #[test]
    fn scale1_fold_preserves_the_displacement() {
        let mut func = scale1_load_window(X86Opcode::ImulRRI, 4, 1);
        // Give the SIB a non-zero displacement.
        {
            let block = func.blocks.get_mut(&Block(0)).unwrap();
            for op in block.insts[1].operands.iter_mut() {
                if let X86ISelOperand::SibMemAddr { disp, .. } = op {
                    *disp = 24;
                }
            }
        }
        let counts = FnUseDefCounts::build(&func);
        let flags = X86FlagLiveness::analyze(&func);
        assert!(sib_scale1_index_fold_run_on_block(
            &mut func,
            Block(0),
            &counts,
            &flags
        ));
        let insts = entry_insts(&func);
        let found = insts.iter().any(|i| {
            i.operands.iter().any(|o| {
                matches!(
                    o,
                    X86ISelOperand::SibMemAddr {
                        scale: 4,
                        disp: 24,
                        ..
                    }
                )
            })
        });
        assert!(found, "scale folded to 4 AND displacement 24 preserved");
    }

    // ===================================================================
    // Two-address increment collapse (lea + write-back -> add)
    // ===================================================================

    #[test]
    fn writeback_policy_isolated_public_optimizer() {
        const CHILD: &str = "CG_WRITEBACK_POLICY_CASE";
        const TEST: &str = "x86_peephole::tests::writeback_policy_isolated_public_optimizer";
        let Ok(case) = std::env::var(CHILD) else {
            let mut failures = Vec::new();
            for case in [
                "default",
                "zero",
                "one",
                "empty",
                "installed_on",
                "installed_off",
            ] {
                let mut command = std::process::Command::new(std::env::current_exe().unwrap());
                command.args(["--exact", TEST, "--nocapture", "--test-threads=1"]);
                for (key, _) in std::env::vars_os() {
                    if key.to_string_lossy().starts_with("TCG_")
                        || key.to_string_lossy().starts_with("TRUST_CG_")
                    {
                        command.env_remove(key);
                    }
                }
                command.env(CHILD, case);
                match case {
                    "zero" | "installed_off" => {
                        command.env("TCG_NO_X86_LEA_WRITEBACK", "0");
                    }
                    "one" | "installed_on" => {
                        command.env("TCG_NO_X86_LEA_WRITEBACK", "1");
                    }
                    "empty" => {
                        command.env("TCG_NO_X86_LEA_WRITEBACK", "");
                    }
                    _ => {}
                }
                let output = command.output().unwrap();
                println!(
                    "case {case}:\n{}{}",
                    String::from_utf8_lossy(&output.stdout),
                    String::from_utf8_lossy(&output.stderr)
                );
                if !output.status.success() {
                    failures.push(case);
                }
            }
            assert!(failures.is_empty(), "failed cases: {failures:?}");
            return;
        };
        if case.starts_with("installed_") {
            let disabled = case == "installed_off";
            assert!(set_lea_writeback_disabled(disabled));
            assert!(set_lea_writeback_disabled(disabled));
            assert!(!set_lea_writeback_disabled(!disabled));
        }
        let enabled = matches!(case.as_str(), "default" | "zero" | "installed_on");
        let mut func = make_func(vec![
            X86ISelInst::new(
                X86Opcode::AddRI,
                vec![vreg(10), vreg(1), X86ISelOperand::Imm(17)],
            ),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(1), vreg(10)]),
            X86ISelInst::new(
                X86Opcode::Cmovcc,
                vec![vreg(2), vreg(1), X86ISelOperand::CondCode(X86CondCode::B)],
            ),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        X86Peephole::default().run_on_function(&mut func);
        assert_eq!(
            entry_insts(&func)
                .iter()
                .any(|i| i.opcode == X86Opcode::AddRI
                    && i.operands == vec![vreg(1), vreg(1), X86ISelOperand::Imm(17)]),
            enabled
        );
        assert_eq!(entry_opcodes(&func).contains(&X86Opcode::MovRR), !enabled);
    }

    fn writeback_instructions_unchanged(before: &[X86ISelInst], after: &[X86ISelInst]) -> bool {
        before.len() == after.len()
            && before.iter().zip(after).all(|(a, b)| {
                a.opcode == b.opcode
                    && a.operands == b.operands
                    && a.flags == b.flags
                    && a.proof_origin == b.proof_origin
            })
    }

    #[test]
    fn writeback_rejects_extra_operands() {
        let mut rewritten = Vec::new();
        for extra_at in [0, 1] {
            let mut pair = vec![
                lea_disp(10, 1, 1),
                X86ISelInst::new(X86Opcode::MovRR, vec![vreg(1), vreg(10)]),
            ];
            pair[extra_at]
                .operands
                .push(X86ISelOperand::PReg(trust_cg_ir::x86_64_regs::RAX));
            pair.push(X86ISelInst::new(
                X86Opcode::CmpRI,
                vec![vreg(1), X86ISelOperand::Imm(7)],
            ));
            let func = run_lea_writeback(pair.clone());
            if !writeback_instructions_unchanged(&pair, entry_insts(&func)) {
                rewritten.push(extra_at);
            }
        }
        assert!(
            rewritten.is_empty(),
            "malformed instructions rewritten at {rewritten:?}"
        );
    }

    #[test]
    fn writeback_preserves_origins_and_fixed_registers() {
        for guarded_at in [0, 1] {
            for origin in [true, false] {
                let mut pair = vec![
                    lea_disp(10, 1, 1),
                    X86ISelInst::new(X86Opcode::MovRR, vec![vreg(1), vreg(10)]),
                ];
                if origin {
                    pair[guarded_at].proof_origin =
                        Some(trust_cg_lower::x86_64_isel::X86ProofOrigin::AtomicLoad);
                } else {
                    pair[guarded_at].operands[0] =
                        X86ISelOperand::PReg(trust_cg_ir::x86_64_regs::RAX);
                }
                pair.push(X86ISelInst::new(
                    X86Opcode::CmpRI,
                    vec![vreg(1), X86ISelOperand::Imm(7)],
                ));
                let func = run_lea_writeback(pair.clone());
                assert!(
                    writeback_instructions_unchanged(&pair, entry_insts(&func)),
                    "changed guarded instruction: position={guarded_at}, origin={origin}"
                );
            }
        }
    }

    #[test]
    fn writeback_preserves_signed_displacement_edges() {
        for disp in [i32::MIN, -1, 1, i32::MAX] {
            for use_lea in [true, false] {
                let first = if use_lea {
                    lea_disp(10, 1, disp)
                } else {
                    X86ISelInst::new(
                        X86Opcode::AddRI,
                        vec![vreg(10), vreg(1), X86ISelOperand::Imm(i64::from(disp))],
                    )
                };
                let func = run_lea_writeback(vec![
                    first,
                    X86ISelInst::new(X86Opcode::MovRR, vec![vreg(1), vreg(10)]),
                    X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(1), X86ISelOperand::Imm(7)]),
                ]);
                assert_eq!(entry_insts(&func).len(), 2);
                assert_eq!(
                    entry_insts(&func)[0].operands,
                    vec![vreg(1), vreg(1), X86ISelOperand::Imm(i64::from(disp))]
                );
            }
        }
    }

    fn lea_disp(dst: u32, base: u32, disp: i32) -> X86ISelInst {
        X86ISelInst::new(
            X86Opcode::Lea,
            vec![
                vreg(dst),
                X86ISelOperand::MemAddr {
                    base: Box::new(vreg(base)),
                    disp,
                },
            ],
        )
    }

    fn run_lea_writeback(insts: Vec<X86ISelInst>) -> X86ISelFunction {
        let mut func = make_func(insts);
        let counts = FnUseDefCounts::build(&func);
        lea_writeback_collapse_run_on_block(&mut func, Block(0), &counts);
        func
    }

    #[test]
    fn lea_writeback_becomes_an_in_place_add() {
        // `lea tmp,[base+1] ; mov base,tmp` with the flags dead (the trailing
        // CmpRI fully overwrites them before any reader).
        let func = run_lea_writeback(vec![
            lea_disp(10, 1, 1),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(1), vreg(10)]),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(1), X86ISelOperand::Imm(7)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let ops = entry_opcodes(&func);
        assert!(!ops.contains(&X86Opcode::Lea), "the lea is gone");
        assert!(
            !ops.contains(&X86Opcode::MovRR),
            "the write-back copy is gone"
        );
        let add = entry_insts(&func)
            .iter()
            .find(|i| i.opcode == X86Opcode::AddRI)
            .expect("an in-place add replaced the pair");
        assert_eq!(
            add.operands,
            vec![vreg(1), vreg(1), X86ISelOperand::Imm(1)],
            "adds the displacement to the base in place"
        );
    }

    #[test]
    fn lea_writeback_is_refused_when_the_flags_are_live() {
        // THE condition: `Lea` writes no flags, `AddRI` writes all of them. A
        // reader before any full overwrite must block the rewrite.
        let func = run_lea_writeback(vec![
            lea_disp(10, 1, 1),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(1), vreg(10)]),
            X86ISelInst::new(
                X86Opcode::Cmovcc,
                vec![vreg(2), vreg(3), X86ISelOperand::CondCode(X86CondCode::B)],
            ),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        let ops = entry_opcodes(&func);
        assert!(ops.contains(&X86Opcode::Lea), "flag-neutral lea retained");
        assert!(ops.contains(&X86Opcode::MovRR));
        assert!(!ops.contains(&X86Opcode::AddRI));
    }

    #[test]
    fn lea_writeback_is_refused_when_the_temporary_has_another_reader() {
        let func = run_lea_writeback(vec![
            lea_disp(10, 1, 1),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(1), vreg(10)]),
            // A second consumer of the pre-increment value.
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(4), vreg(10)]),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(1), X86ISelOperand::Imm(7)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(entry_opcodes(&func).contains(&X86Opcode::Lea));
    }

    #[test]
    fn lea_writeback_is_refused_for_a_zero_displacement_copy() {
        // `lea tmp,[base+0] ; mov base,tmp` is a plain copy, not an increment;
        // other passes own it and an `add $0` would be strictly worse.
        let func = run_lea_writeback(vec![
            lea_disp(10, 1, 0),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(1), vreg(10)]),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(1), X86ISelOperand::Imm(7)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(entry_opcodes(&func).contains(&X86Opcode::Lea));
        assert!(!entry_opcodes(&func).contains(&X86Opcode::AddRI));
    }

    #[test]
    fn lea_writeback_is_refused_for_a_scaled_index_address() {
        // A SIB address adds a RUNTIME index, which is not an immediate add.
        let func = run_lea_writeback(vec![
            X86ISelInst::new(X86Opcode::LeaSib, vec![vreg(10), sib_of(1, 2, 8, 1)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(1), vreg(10)]),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(1), X86ISelOperand::Imm(7)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(!entry_opcodes(&func).contains(&X86Opcode::AddRI));
    }

    #[test]
    fn lea_writeback_is_refused_when_the_pair_is_not_adjacent() {
        // An instruction between them could read `base`, which after the fold
        // already holds the incremented value.
        let func = run_lea_writeback(vec![
            lea_disp(10, 1, 1),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(5), vreg(1)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(1), vreg(10)]),
            X86ISelInst::new(X86Opcode::CmpRI, vec![vreg(1), X86ISelOperand::Imm(7)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(entry_opcodes(&func).contains(&X86Opcode::Lea));
        assert!(!entry_opcodes(&func).contains(&X86Opcode::AddRI));
    }

    #[test]
    fn addri_writeback_folds_even_with_the_flags_live() {
        // The `AddRI` spelling needs NO flag condition, and this is the test that
        // says so: the rewrite keeps the SAME flag write at the SAME position with
        // the identical result, so a downstream reader is unaffected. (The `Lea`
        // spelling in the sibling test must refuse the same shape, because there
        // folding would INTRODUCE a flag write.)
        let func = run_lea_writeback(vec![
            X86ISelInst::new(
                X86Opcode::AddRI,
                vec![vreg(10), vreg(1), X86ISelOperand::Imm(1)],
            ),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(1), vreg(10)]),
            X86ISelInst::new(
                X86Opcode::Cmovcc,
                vec![vreg(2), vreg(3), X86ISelOperand::CondCode(X86CondCode::B)],
            ),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert!(
            !entry_opcodes(&func).contains(&X86Opcode::MovRR),
            "the write-back copy is retired"
        );
        let add = entry_insts(&func)
            .iter()
            .find(|i| i.opcode == X86Opcode::AddRI)
            .expect("an in-place add remains");
        assert_eq!(add.operands, vec![vreg(1), vreg(1), X86ISelOperand::Imm(1)]);
    }

    #[test]
    fn addri_writeback_is_refused_when_the_temporary_is_read_again() {
        let func = run_lea_writeback(vec![
            X86ISelInst::new(
                X86Opcode::AddRI,
                vec![vreg(10), vreg(1), X86ISelOperand::Imm(1)],
            ),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(1), vreg(10)]),
            X86ISelInst::new(X86Opcode::MovRR, vec![vreg(4), vreg(10)]),
            X86ISelInst::new(X86Opcode::Ret, vec![]),
        ]);
        assert_eq!(
            entry_insts(&func)
                .iter()
                .filter(|i| i.opcode == X86Opcode::MovRR)
                .count(),
            2,
            "a second reader of the temporary blocks the fold"
        );
    }
}
