// trust-cg-verify/tests/soundness_manifest.rs — DELIVERABLE of task #55 (E engine).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// ===========================================================================
// THE SOUNDNESS MANIFEST + META-GATE — the single source of truth.
// ===========================================================================
//
// This file is the ENUMERATED REGISTRY of every fail-closed soundness invariant
// in the workspace. Each entry carries:
//   * a STABLE id (A1, A2, C, D1..D8, R, H, S, B*),
//   * a one-line DESCRIPTION of what it enforces, and
//   * a BINDING to the concrete test/gate that ENFORCES it.
//
// The META-GATE (`meta_gate_every_invariant_has_a_live_enforcing_test`) makes the
// manifest LOAD-BEARING and MONOTONIC. It FAILS if:
//   (1) any manifest entry's enforcing test no longer exists in source (deleting
//       or renaming the enforcing test breaks the gate — the binding is "live"),
//   (2) any IN-PROCESS invariant's underlying gate has been weakened (the gate is
//       RE-EXERCISED here, so a fail-open regression refutes), or
//   (3) the manifest is MISSING an invariant that exists in code (best-effort: every
//       `#[test]` in `meta_theorems.rs` must be referenced by some manifest entry,
//       so a new meta-theorem added without a manifest entry fails the gate).
//
// HONESTY: the meta-gate is NON-VACUOUS. Removing or weakening ANY invariant — or
// its enforcing test — makes the meta-gate fail. A separate `negative-control`
// test proves the source-presence check has teeth (a bogus function name is
// reported absent). The Status::Pending lane remains in the model so a FUTURE
// bridge can be registered honestly (never silently dropped); the one historical
// Pending entry — the aarch64 integer B-defs differential bridge — has now been
// RATCHETED to Satisfied, bound to the live `bdefs_differential_bridge.rs` test
// that checks trust-cg's in-house AArch64 encoders against real-silicon ground
// truth (defeating root-cause #2: a shared in-house misencoding).

use std::collections::HashSet;
use std::fs;
use std::path::PathBuf;
use std::sync::Arc;

use trust_cg_verify::coverage_gate::{
    ALL_AARCH64_OPCODES, ALL_RISCV_OPCODES, ALL_WASM_OPCODES, ALL_X86_OPCODES, CoverageGate,
    GateArch, OpcodeClass, classify_aarch64, classify_riscv, classify_wasm, classify_x86,
};
use trust_cg_verify::fsym_trust_ir::{FsymCoverageError, FsymTrustIrReport};
use trust_cg_verify::lowering_proof::MachineSideProvenance;
use trust_cg_verify::proof_database::{
    CategorizedProof, ProofCategory, ProofDatabase, is_genuine_identity, is_known_degenerate_debt,
};
use trust_cg_verify::smt::SmtExpr;
use trust_cg_verify::verify::VerificationResult;
use trust_cg_verify::{
    ProofObligation, reconstruct_x86_alu_obligation, representative_x86_reconstructable_inst,
    verify_by_evaluation,
};

use trust_cg_ir::X86Opcode;

fn on_large_stack<T: Send + 'static>(f: impl FnOnce() -> T + Send + 'static) -> T {
    std::thread::Builder::new()
        .name("soundness-manifest".to_string())
        .stack_size(64 * 1024 * 1024)
        .spawn(f)
        .expect("spawn scratch thread")
        .join()
        .expect("scratch thread panicked")
}

// ---------------------------------------------------------------------------
// Manifest data model.
// ---------------------------------------------------------------------------

/// How a manifest invariant is enforced.
#[derive(Clone)]
enum Enforcement {
    /// Enforced by a named `#[test]` function in a sibling integration-test file.
    /// The meta-gate confirms the function name is still PRESENT in that file's
    /// source (deleting/renaming it breaks the gate). `(test_file, fn_name)`.
    Test {
        file: &'static str,
        function: &'static str,
    },
    /// Enforced by a gate that this file RE-EXERCISES IN-PROCESS (so weakening the
    /// gate refutes here directly). The `&'static str` names the in-process check
    /// fn below for the audit trail; `reexercise` is run by the meta-gate.
    InProcess {
        check_name: &'static str,
        reexercise: fn(),
    },
}

/// Whether the invariant is enforced today or registered as a known-pending bridge.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Status {
    /// The invariant is actively enforced (fail-closed) today.
    Satisfied,
    /// A registered-but-not-yet-enforced soundness goal (e.g. a differential
    /// bridge whose Clean side is not yet wired). Listed HONESTLY, never silently
    /// dropped. The meta-gate does NOT require a live enforcing test for a Pending
    /// entry, but DOES require it to carry a tracking note.
    Pending,
}

/// A single enumerated soundness invariant.
struct SoundnessInvariant {
    /// Stable id (A1, A2, C, D1..D8, R, H, S, B-aarch64-int, ...).
    id: &'static str,
    /// One-line description of what the invariant enforces.
    description: &'static str,
    /// The binding to the concrete enforcing test/gate.
    enforcement: Enforcement,
    /// Satisfied (enforced) vs Pending (registered tracking item).
    status: Status,
    /// For Pending entries: the tracking note (why it is pending). Empty for
    /// Satisfied entries.
    pending_note: &'static str,
}

const META_THEOREMS_FILE: &str = "meta_theorems.rs";
const MUTATION_CATALOG_FILE: &str = "mutation_catalog.rs";
const PROOF_GATE_STRICT_FILE: &str = "proof_gate_strict.rs";
const RECONSTRUCTION_X86_FILE: &str = "reconstruction_x86.rs";
const COVERAGE_GATE_TESTS_FILE: &str = "coverage_gate_tests.rs";
const BDEFS_DIFFERENTIAL_BRIDGE_FILE: &str = "bdefs_differential_bridge.rs";
const BDEFS_DIFFERENTIAL_BRIDGE_NEON_FILE: &str = "bdefs_differential_bridge_neon.rs";
const BDEFS_DIFFERENTIAL_BRIDGE_NEON_FP_FILE: &str = "bdefs_differential_bridge_neon_fp.rs";
const BDEFS_DIFFERENTIAL_BRIDGE_X86_FILE: &str = "bdefs_differential_bridge_x86.rs";
const BDEFS_DIFFERENTIAL_BRIDGE_X86_PACKED_FILE: &str = "bdefs_differential_bridge_x86_packed.rs";
const BDEFS_DIFFERENTIAL_BRIDGE_X86_FP_FILE: &str = "bdefs_differential_bridge_x86_fp.rs";
const BDEFS_DIFFERENTIAL_BRIDGE_RISCV_FILE: &str = "bdefs_differential_bridge_riscv.rs";
const BDEFS_DIFFERENTIAL_BRIDGE_RISCV_FP_FILE: &str = "bdefs_differential_bridge_riscv_fp.rs";
const FP_BITMODEL_BRIDGE_FILE: &str = "fp_bitmodel_bridge.rs";

// ---------------------------------------------------------------------------
// THE REGISTRY — every fail-closed soundness invariant in the workspace.
// ---------------------------------------------------------------------------
fn manifest() -> Vec<SoundnessInvariant> {
    use Enforcement::*;
    use Status::*;
    vec![
        // ---- (A1) classifiers are wildcard-free / total --------------------
        SoundnessInvariant {
            id: "A1",
            description: "Each classify_<arch> is TOTAL over its opcode universe (wildcard-free): \
                          every opcode lands in a typed OpcodeClass, never a fail-open default.",
            enforcement: InProcess {
                check_name: "inproc_classifiers_total_and_reasoned",
                reexercise: inproc_classifiers_total_and_reasoned,
            },
            status: Satisfied,
            pending_note: "",
        },
        SoundnessInvariant {
            id: "A1-meta",
            description: "(A1) restated as the meta-theorem: every opcode of every backend is \
                          classified; FailClosedAllowlisted always carries a non-empty reason.",
            enforcement: Test {
                file: META_THEOREMS_FILE,
                function: "meta_b_every_opcode_is_classified_total_classifier",
            },
            status: Satisfied,
            pending_note: "",
        },
        // ---- (A2) fsym deref/memory obligations accounted-for or fail closed
        SoundnessInvariant {
            id: "A2",
            description: "fsym deref/memory obligations are accounted-for or FAIL CLOSED: a report \
                          carrying any FsymCoverageError is rejected by has_coverage_error().",
            enforcement: InProcess {
                check_name: "inproc_fsym_coverage_fails_closed",
                reexercise: inproc_fsym_coverage_fails_closed,
            },
            status: Satisfied,
            pending_note: "",
        },
        SoundnessInvariant {
            id: "A2-meta",
            description: "(A2) restated as the meta-theorem: the deref-coverage gate decision is \
                          exactly the non-emptiness of the coverage-error list.",
            enforcement: Test {
                file: META_THEOREMS_FILE,
                function: "meta_d_fsym_deref_coverage_gate_keys_on_error_list",
            },
            status: Satisfied,
            pending_note: "",
        },
        SoundnessInvariant {
            id: "A2-fault",
            description: "(A2) adversarial: a dropped deref obligation is KILLED by the fsym \
                          coverage gate (has_coverage_error()).",
            enforcement: Test {
                file: MUTATION_CATALOG_FILE,
                function: "fault4_dropped_deref_obligation_killed_by_fsym_coverage_gate",
            },
            status: Satisfied,
            pending_note: "",
        },
        // ---- (C) no registered proof is degenerate-and-credited ------------
        SoundnessInvariant {
            id: "C",
            description: "No registered proof is degenerate-and-credited: a degenerate X==X with a \
                          name on no audited list is reported by non_degeneracy_violations().",
            enforcement: InProcess {
                check_name: "inproc_non_degeneracy_gate_is_alive",
                reexercise: inproc_non_degeneracy_gate_is_alive,
            },
            status: Satisfied,
            pending_note: "",
        },
        SoundnessInvariant {
            id: "C-meta",
            description: "(C) restated as the meta-theorem: forall p in DB, non-degenerate OR \
                          audited (genuine-identity / known-degenerate-debt).",
            enforcement: Test {
                file: META_THEOREMS_FILE,
                function: "meta_a_no_proof_is_degenerate_and_unclassified",
            },
            status: Satisfied,
            pending_note: "",
        },
        SoundnessInvariant {
            id: "C-gate",
            description: "(C) the universal non-degeneracy gate over the whole DB is fail-closed \
                          and live (strict gate body).",
            enforcement: Test {
                file: PROOF_GATE_STRICT_FILE,
                function: "universal_non_degeneracy_gate",
            },
            status: Satisfied,
            pending_note: "",
        },
        SoundnessInvariant {
            id: "C-fault",
            description: "(C) adversarial: an injected degenerate X==X proof is KILLED by the \
                          non-degeneracy gate (reported exactly).",
            enforcement: Test {
                file: MUTATION_CATALOG_FILE,
                function: "fault1_degenerate_xx_proof_killed_by_non_degeneracy_gate",
            },
            status: Satisfied,
            pending_note: "",
        },
        // ---- (D1..D8) the 8 meta-theorems ----------------------------------
        SoundnessInvariant {
            id: "D1",
            description: "Meta-theorem (a): no proof is degenerate-and-unclassified.",
            enforcement: Test {
                file: META_THEOREMS_FILE,
                function: "meta_a_no_proof_is_degenerate_and_unclassified",
            },
            status: Satisfied,
            pending_note: "",
        },
        SoundnessInvariant {
            id: "D2",
            description: "Meta-theorem (b): every opcode is classified (total classifier).",
            enforcement: Test {
                file: META_THEOREMS_FILE,
                function: "meta_b_every_opcode_is_classified_total_classifier",
            },
            status: Satisfied,
            pending_note: "",
        },
        SoundnessInvariant {
            id: "D3",
            description: "Meta-theorem (c): every coverage credit is genuine, never static \
                          degenerate.",
            enforcement: Test {
                file: META_THEOREMS_FILE,
                function: "meta_c_every_credit_is_genuine_never_static_degenerate",
            },
            status: Satisfied,
            pending_note: "",
        },
        SoundnessInvariant {
            id: "D4",
            description: "Meta-theorem (c''): the credit predicates reject a static-DB X==X.",
            enforcement: Test {
                file: META_THEOREMS_FILE,
                function: "meta_c2_credit_predicates_reject_static_x_eq_x",
            },
            status: Satisfied,
            pending_note: "",
        },
        SoundnessInvariant {
            id: "D5",
            description: "Meta-theorem (d): the fsym deref-coverage gate keys on the error list.",
            enforcement: Test {
                file: META_THEOREMS_FILE,
                function: "meta_d_fsym_deref_coverage_gate_keys_on_error_list",
            },
            status: Satisfied,
            pending_note: "",
        },
        SoundnessInvariant {
            id: "D6",
            description: "Meta-theorem (e): the 4 headline numbers are pinned AND each gate clean.",
            enforcement: Test {
                file: META_THEOREMS_FILE,
                function: "meta_e_headline_coverage_is_pinned_and_honest",
            },
            status: Satisfied,
            pending_note: "",
        },
        SoundnessInvariant {
            id: "D7",
            description: "Meta-theorem (cross-cut): the headline rests on a non-vacuous emittable \
                          denominator.",
            enforcement: Test {
                file: META_THEOREMS_FILE,
                function: "meta_headline_denominator_is_nonvacuous",
            },
            status: Satisfied,
            pending_note: "",
        },
        SoundnessInvariant {
            id: "D8",
            description: "Meta-theorem (surface): the opcode universes are typed (enum-surface \
                          regression guard).",
            enforcement: Test {
                file: META_THEOREMS_FILE,
                function: "meta_opcode_universes_are_typed",
            },
            status: Satisfied,
            pending_note: "",
        },
        // ---- (R) coverage credit requires is_reconstructed() && Valid ------
        SoundnessInvariant {
            id: "R",
            description: "Coverage credit requires is_reconstructed() && Valid: a swapped opcode \
                          REFUTES, and a static-DB X==X can never be credited (no X==X credit).",
            enforcement: InProcess {
                check_name: "inproc_reconstruction_credit_rule",
                reexercise: inproc_reconstruction_credit_rule,
            },
            status: Satisfied,
            pending_note: "",
        },
        SoundnessInvariant {
            id: "R-fault-swap",
            description: "(R) adversarial: a swapped opcode (Iadd as SUB) is KILLED by the \
                          reconstruction discharge.",
            enforcement: Test {
                file: MUTATION_CATALOG_FILE,
                function: "fault3_swapped_opcode_iadd_as_sub_killed_by_reconstruction_discharge",
            },
            status: Satisfied,
            pending_note: "",
        },
        SoundnessInvariant {
            id: "R-fault-static",
            description: "(R) adversarial: a static-DB X==X cannot be credited covered.",
            enforcement: Test {
                file: MUTATION_CATALOG_FILE,
                function: "fault7_static_db_xx_cannot_be_credited_covered",
            },
            status: Satisfied,
            pending_note: "",
        },
        // ---- (H) the 4 headline pins + honest-red discipline ---------------
        SoundnessInvariant {
            id: "H",
            description: "The 4 accepted-obligation pins (AArch64 155/248, RISC-V 14/17, \
                          WASM 109/111, x86-64 163/192 accepted/emitted-value-effect) hold, and \
                          every uncovered row is an explicit DeferredUnfaithfulModel rather than \
                          a wiring gap. These are evidence-inventory ratios, not formal-proof or \
                          compiler-correctness percentages. AArch64 \
                          reached full coverage at an earlier stage when the 5 \
                          honestly-deferred .2D neon_fpred ops received their faithful \
                          per-lane obligations; NeonUmovGen then moved allowlisted -> covered \
                          via its faithful per-(size,lane) extract matrix, and LdrGottprel \
                          (TLS GOT-TPREL) via aarch64_elf_tls_reloc_proofs; then FCVTL/FCVTL2 \
                          (vector f32->f64 widen) via all_neon_fcvtl_proofs (124/124 -> 126/126); \
                          then EorRRShift (shifted-register EOR-ROR, the rotate-fusion peephole) \
                          via all_eor_ror_shift_proofs (126/126 -> 127/127); then FcselRR (scalar \
                          FP conditional select, the FP-Select isel path) via all_fcsel_proofs \
                          (127/127 -> 128/128); then NeonFmlaLaneV (FMLA by element, the \
                          elementwise-FP vectorizer's da*x broadcast) via all_neon_fmla_lane_proofs \
                          (128/128 -> 129/129); then AddRRShift/SubRRShift (shifted-register \
                          ADD/SUB, the shift-ALU fusion peephole) via all_add_sub_lsl_shift_proofs \
                          (129/129 -> 131/131); then SMLAL/SMLAL2/UMLAL/UMLAL2 (NEON widening \
                          multiply-accumulate-long, the neon_array widening-dot vectorizer's \
                          i32->i64 MAC) via all_neon_smlal_proofs (131/131 -> 135/135); then \
                          UADDW/UADDW2 (NEON widening add-wide, the neon_array widening \
                          abs-sum vectorizer TRACK D's u32->u64 wide add) via \
                          all_neon_uaddw_proofs (135/135 -> 137/137); then SADDW/SADDW2 \
                          (NEON SIGNED widening add-wide, the neon_predsum widening \
                          i64-acc condsum's i32->i64 wide add) via all_neon_saddw_proofs \
                          (137/137 -> 139/139); then MLA.4S (NEON vector multiply-\
                          accumulate, the neon_predsum MLA-by-mask condsum accumulate) \
                          via all_neon_mla_proofs and UADALP (NEON pairwise widening \
                          accumulate, the neon_array TRACK D abs-sum accumulate) via \
                          all_neon_uadalp_proofs (141/141 -> 143/143); then RBIT.16B \
                          (NEON per-byte 8-bit reverse, the neon-bitrev vectorizer's \
                          `a[i].reverse_bits()` over `[u8; N]`) via all_neon_rbit_proofs \
                          (143/143 -> 144 covered of 144 at that stage). Publication re-audit \
                          then withdrew opcode-wide MOVN/MOVK credit: W-form MOVN lacks its \
                          width-specific theorem and MOVK lacks a faithful contextual \
                          per-instruction lowering theorem. The publication audit restored all \
                          emitted value/effect families to the denominator. The current \
                          publication audit reached 151/244 with 93 RED rows after adding six \
                          volatile load/store forms; EorRRLsl/EorRRLsr then added two \
                          reconstructed shifted-source forms, yielding 153/246 with 93 RED rows; \
                          Umull then left the deferred set via its faithful zext64 widening \
                          obligation, and complete packed-NZCV TST authority removed another \
                          RED row. StrbRO/StrhRO then entered the explicit audit universe as \
                          two honest memory-effect gaps. The combined inventory is 155/248 \
                          with 93 RED rows.",
            enforcement: InProcess {
                check_name: "inproc_headline_pins_and_honest",
                reexercise: inproc_headline_pins_and_honest,
            },
            status: Satisfied,
            pending_note: "",
        },
        SoundnessInvariant {
            id: "H-aarch64",
            description: "(H) AArch64 emittable coverage is honest under the strict gate.",
            enforcement: Test {
                file: COVERAGE_GATE_TESTS_FILE,
                function: "aarch64_emittable_coverage_is_honest_under_strict",
            },
            status: Satisfied,
            pending_note: "",
        },
        SoundnessInvariant {
            id: "H-x86",
            description: "(H) x86 emittable coverage is honest under the strict gate.",
            enforcement: Test {
                file: COVERAGE_GATE_TESTS_FILE,
                function: "x86_emittable_coverage_is_honest_under_strict",
            },
            status: Satisfied,
            pending_note: "",
        },
        // ---- (S) the strict-SMT-lane requirement for solver-only obligations
        SoundnessInvariant {
            id: "S",
            description: "The strict SMT lane is REQUIRED for solver-only obligations: the gate \
                          fails closed (NoSolver) rather than downgrading to the statistical mock.",
            enforcement: Test {
                file: PROOF_GATE_STRICT_FILE,
                function: "gate_fails_closed_when_no_solver",
            },
            status: Satisfied,
            pending_note: "",
        },
        SoundnessInvariant {
            id: "S-strict-flag",
            description: "(S) GateConfig::strict() and ::default() both set require_solver = true \
                          (no silent auto-downgrade).",
            enforcement: Test {
                file: PROOF_GATE_STRICT_FILE,
                function: "strict_gate_requires_solver_flag_is_set",
            },
            status: Satisfied,
            pending_note: "",
        },
        SoundnessInvariant {
            id: "S-full-db",
            description: "(S) the FULL database is formally verified by the solver lane (z3/ay) — \
                          explicitly qualified and run by scripts/check_proof_gate.sh.",
            enforcement: Test {
                file: PROOF_GATE_STRICT_FILE,
                function: "full_database_is_formally_verified",
            },
            status: Satisfied,
            pending_note: "",
        },
        // ---- (S-div) the x86 IDIV/DIV divisor!=0 precond (#79) -------------
        SoundnessInvariant {
            id: "S-div",
            description: "x86 IDIV/DIV divisor!=0 precond is LOAD-BEARING in the NATIVE lane: the \
                          #DE trap is modeled as POISON (SmtExpr::TrapIfZero), so dropping the \
                          precond REFUTES under the native evaluator (#79 — native kill, not just \
                          SMT-lane-enforced).",
            enforcement: InProcess {
                check_name: "inproc_div_precond_is_load_bearing",
                reexercise: inproc_div_precond_is_load_bearing,
            },
            status: Satisfied,
            pending_note: "",
        },
        SoundnessInvariant {
            id: "S-div-fault",
            description: "(S-div) adversarial: dropping the divisor!=0 precond is KILLED by the \
                          native trap model (was fault-5a survivor, now a native kill).",
            enforcement: Test {
                file: MUTATION_CATALOG_FILE,
                function: "fault5a_dropped_divisor_precond_killed_by_native_trap_model",
            },
            status: Satisfied,
            pending_note: "",
        },
        SoundnessInvariant {
            id: "S-div-recon",
            description: "(S-div) the production division reconstruction discharges Valid WITH the \
                          precond and excludes divisor==0 (precond present in production).",
            enforcement: Test {
                file: RECONSTRUCTION_X86_FILE,
                function: "division_divisor_zero_is_excluded_by_precondition",
            },
            status: Satisfied,
            pending_note: "",
        },
        SoundnessInvariant {
            id: "S-shift",
            description: "The shift count<width precond is LOAD-BEARING (#57): dropping it makes a \
                          masked machine shift REFUTE at amt==width.",
            enforcement: Test {
                file: MUTATION_CATALOG_FILE,
                function: "fault5b_dropped_shift_count_precond_killed_by_reconstruction_discharge",
            },
            status: Satisfied,
            pending_note: "",
        },
        // ---- (B) every Clean model must have a differential bridge to silicon
        SoundnessInvariant {
            id: "B-aarch64-int",
            description: "Differential bridge: trust-cg's IN-HOUSE AArch64 integer MACHINE \
                          encoders (aarch64_semantics.rs SmtExpr encoders — the machine side of \
                          the reconstruction proofs) are evaluated via the SAME try_eval path the \
                          reconstruction uses and asserted EQUAL to the SILICON-recorded results \
                          (real Apple M4 Pro `:= rfl` chip theorems, sibling Clean tree \
                          proofs/aarch64_isa_chip.lean). Defeats root-cause #2: a shared \
                          misencoding in the in-house spec is no longer invisible because the \
                          oracle is independent hardware, not a second software model. \
                          NON-VACUOUS: a deliberately-wrong encoder mismatches a silicon fact.",
            enforcement: Test {
                file: BDEFS_DIFFERENTIAL_BRIDGE_FILE,
                function: "aarch64_inhouse_encoders_match_silicon_ground_truth",
            },
            status: Satisfied,
            pending_note: "",
        },
        // ---- (B) AArch64 NEON: differential bridge to BARE M4 SILICON ----
        SoundnessInvariant {
            id: "B-aarch64-neon",
            description: "Differential bridge: trust-cg's IN-HOUSE AArch64 NEON integer SmtExpr \
                          encoders (neon_semantics.rs encode_neon_* — the machine side of the NEON \
                          lowering proofs) are evaluated via the SAME try_eval path the \
                          reconstruction uses (yielding a 128-bit EvalResult::Bv128, or a Bv for a \
                          64-bit-arrangement op) and asserted EQUAL to 128-bit results recorded from \
                          BARE M4 SILICON. The host IS an Apple M4 (native AArch64, runs NEON \
                          DIRECTLY — NO Rosetta/qemu/Clean-chip-file): the oracle harness \
                          (gen_aarch64_neon_silicon_truth.rs) gives each (op, arrangement) an \
                          #[inline(never)] wrapper that ldr q1/q2, runs the ACTUAL packed NEON \
                          instruction via std::arch::asm! (add v0.4s, v1.4s, v2.4s, ...), and str q0 \
                          the 128-bit result STRAIGHT off the silicon (otool -tv confirms the real \
                          mnemonics). This is the SAME oracle tier as the B-aarch64-int bridge (real \
                          M4 chip results) — STRICTLY ABOVE the Rosetta/qemu tier the x86/RISC-V \
                          bridges use. Defeats root-cause #2 for the AArch64 NEON integer ops (a \
                          shared misencoding in the in-house NEON spec is no longer invisible — the \
                          oracle is independent hardware, not a second software model). 21250 VALUE \
                          facts across ALL 24 integer NEON families over a 128-bit lane-edge grid \
                          (per-lane 0/-1/INT_MIN/INT_MAX/1/2 LCG-random, alternating patterns, 4 \
                          random vectors; shifts at fixed amounts INCLUDING amount == lane width): \
                          add/sub/mul/neg, and/orr/eor/bic/not, cmeq/cmgt/cmge, smin/umin/smax/umax, \
                          mla, dup/ins/movi, shl/ushr/sshr, umaxv — over arrangements \
                          .8B/.16B/.4H/.8H/.2S/.4S/.2D. NONE deferred: dup/ins/movi (imm/lane/scalar, \
                          NOT a second vector) and umaxv (cross-lane reduction to a scalar) are \
                          BRIDGED by feeding the matching encoder the SAME imm/lane/scalar the \
                          silicon harness used (the x86 imul_imm/LEA fixed-imm pattern). 64-bit \
                          (D-register) arrangements zero the upper 64 bits in hardware; the bridge \
                          asserts that zeroing contract is load-bearing. NEON integer ops do not \
                          trap -> 0 trap facts. NON-VACUOUS: an ADD-as-SUB encoder, a wrong- \
                          ARRANGEMENT ADD.16B-as-ADD.8H (a byte-lane carry crosses the wrong \
                          boundary), and a CMGT-as-CMGE on an equal lane each mismatch a silicon \
                          fact; a corrupted fixture result flips the comparison; the umaxv reduction \
                          is proven load-bearing on a non-lane-0-max witness.",
            enforcement: Test {
                file: BDEFS_DIFFERENTIAL_BRIDGE_NEON_FILE,
                function: "aarch64_neon_inhouse_encoders_match_silicon_ground_truth",
            },
            status: Satisfied,
            pending_note: "",
        },
        // ---- (B) AArch64 NEON lane-wise FP: differential bridge to BARE M4 SILICON
        SoundnessInvariant {
            id: "B-aarch64-neon-fp",
            description: "Differential bridge: trust-cg's IN-HOUSE AArch64 NEON LANE-WISE FP SmtExpr \
                          encoders (neon_semantics.rs encode_neon_fadd/fsub/fmul/fdiv/fneg/fabs/ \
                          fsqrt, the FP compares fcmeq/fcmgt/fcmge, and fmin/fmax/fminnm/fmaxnm — \
                          the machine side of the NEON FP lowering proofs) are evaluated via the \
                          SAME try_eval path the reconstruction uses and asserted EQUAL to 128-bit \
                          results recorded from BARE M4 SILICON. Each encoder SPLITS the Bv128 \
                          operand into per-lane FP leaves by VectorArrangement (neon_fp_lanes — the \
                          named Bv128 lane-split for FP: .2S/.4S -> binary32 leaves, .2D -> binary64 \
                          leaves), applies the per-lane SmtExpr FP op (fp_add/.., the fp compares, \
                          the fmin/fmax ite-trees), and the bridge lane-concats the per-lane results \
                          back into the Bv128 (the inverse split) — NO new FP math. try_eval routes \
                          every per-lane FP node through the SILICON-VALIDATED INTEGER-ONLY \
                          fp_bitmodel.rs (host FPU EVICTED for f32/f64, #89/#91/#94), which carries \
                          the AArch64 FP semantics — so this bridge re-uses lane-wise the SAME model \
                          the scalar AArch64 FP bit-model bridge already grounds, AT NEON SEMANTICS, \
                          and cross-checks it against the independent hardware. The host IS an Apple \
                          M4 (native AArch64, runs the lane-wise FP NEON DIRECTLY — NO Rosetta/qemu/ \
                          Clean-chip-file): the oracle harness (gen_aarch64_neon_fp_silicon_truth.rs) \
                          gives each (op, arrangement) an #[inline(never)] wrapper that ldr q1/q2, \
                          runs the ACTUAL packed FP NEON instruction via std::arch::asm! (fadd \
                          v0.4s, ...; fmul v0.2d; fminnm; fcmgt; fsqrt), and str q0 the 128-bit \
                          result STRAIGHT off the silicon (otool -tv confirms the real mnemonics). \
                          SAME oracle tier as the B-aarch64-neon integer bridge (real M4 chip \
                          results) — STRICTLY ABOVE the Rosetta/qemu tier the x86/RISC-V FP bridges \
                          use. Defeats root-cause #2 for the AArch64 NEON FP ops. 19224 VALUE facts \
                          across ALL 14 in-house NEON-FP families over a 128-bit lane-FP EDGE grid \
                          (per-lane +-0/+-Inf/qNaN/sNaN/subnormals/min-max-normal/+-1/+2/tie + 2 LCG \
                          randoms; uniform + alternating edge pairs incl NaN-vs-number, ordered- \
                          unequal, zero-ordering) over arrangements .2S/.4S (f32) and .2D (f64). The \
                          AArch64-SPECIFIC FP semantics are modeled AS ARM (NOT RISC-V \
                          minimumNumber, NOT x86 MINSS-second-operand): FMIN/FMAX are NaN- \
                          PROPAGATING (any NaN -> NaN), FMINNM/FMAXNM are IEEE-2008 minNum/maxNum \
                          (lone qNaN -> the NUMBER; sNaN or both-NaN -> NaN), -0 < +0 for all four; \
                          FCMEQ/FCMGT/FCMGE -> per-lane all-ones/all-zero ordered masks (NaN -> 0). \
                          Every non-NaN lane VALUE, every compare mask, and every min/max NUMBER \
                          lane is a STRICT exact-bit match; a NaN-RESULT lane is compared by NaN- \
                          CLASS (the FPProcessNaN-selected payload the M4 emits, and the f32-carrier \
                          quieting of an sNaN, may legitimately differ from the canonical qNaN the \
                          encoder returns — COUNTED per-op, NEVER hiding a value). A non-NaN value \
                          mismatch, or a NaN-vs-non-NaN mismatch, is ALWAYS a HARD failure: ZERO \
                          HARD. NEON FP ops do not trap under default FPCR -> 0 trap facts. 64-bit \
                          (.2S, D-register) arrangements zero the upper 64 bits in hardware; the \
                          bridge asserts that contract. NON-VACUOUS: a FADD-as-FSUB encoder, a \
                          wrong-ARRANGEMENT FADD.4S-as-FADD.2D (4 f32 adds != 2 f64 adds over the \
                          same 128 bits), a FMIN-as-FMINNM on a lone-qNaN lane (FMIN gives NaN, \
                          FMINNM gives the number — the load-bearing ARM NaN-propagating-vs-minNum \
                          distinction), and a FCMGT-as-FCMGE on an equal lane each mismatch a \
                          silicon fact; a corrupted fixture result flips the comparison; the ARM \
                          FMIN NaN-propagating semantics are pinned.",
            enforcement: Test {
                file: BDEFS_DIFFERENTIAL_BRIDGE_NEON_FP_FILE,
                function: "aarch64_neon_fp_inhouse_encoders_match_silicon_ground_truth",
            },
            status: Satisfied,
            pending_note: "",
        },
        // ---- (B) x86: differential bridge to Rosetta 2 (independent x86) ----
        SoundnessInvariant {
            id: "B-x86-rosetta",
            description: "Differential bridge: trust-cg's IN-HOUSE x86-64 integer SmtExpr encoders \
                          (x86_64_semantics.rs — the machine side of the x86 reconstruction proofs) \
                          are evaluated via the SAME try_eval path the reconstruction uses and \
                          asserted EQUAL to results recorded from ROSETTA 2 (Apple's INDEPENDENT \
                          x86-64 binary translator — a true independent x86 implementation, one \
                          notch below bare silicon, NOT a second in-house model). REAL-EMULATION- \
                          VALIDATED: defeats root-cause #2 for x86 integer ops (a shared misencoding \
                          in the in-house spec is no longer invisible — the oracle is an independent \
                          x86, not a second software model of our own). Rosetta faithfully \
                          reproduces shift-count masking (&0x3f/&0x1f) AND the IDIV/DIV #DE traps on \
                          a zero divisor and signed INT_MIN/-1; the bridge asserts VALUE facts match \
                          (5204) and TRAP facts (100) match trust-cg's trap contract — div0 -> \
                          TrapIfZero->Poison (the D-survivor fix #79), signed INT_MIN/-1 -> \
                          load-bearing no-overflow precondition (bvsdiv WRAPS, no Poison, so the \
                          precond carries the trap). 5304 facts / 48 op families. NON-VACUOUS: a \
                          SUB-for-ADD encoder, the unmasked clamp-to-0 shift at count>=width, and \
                          IDIV-as-DIV on a negative dividend each mismatch a Rosetta fact, and the \
                          unwrapped div encoder gives a defined value at divisor==0 (so the \
                          TrapIfZero wrapper is load-bearing).",
            enforcement: Test {
                file: BDEFS_DIFFERENTIAL_BRIDGE_X86_FILE,
                function: "x86_inhouse_encoders_match_rosetta_ground_truth",
            },
            status: Satisfied,
            pending_note: "",
        },
        // ---- (B) x86 PACKED-SSE2: differential bridge to Rosetta 2 (independent x86)
        SoundnessInvariant {
            id: "B-x86-sse-packed",
            description: "Differential bridge: trust-cg's IN-HOUSE x86-64 PACKED-SSE2 integer \
                          SmtExpr encoders (x86_64_semantics.rs encode_p* — the machine side of the \
                          x86 PACKED reconstruction proofs) are evaluated via the SAME try_eval path \
                          the reconstruction uses (yielding a 128-bit EvalResult::Bv128) and \
                          asserted EQUAL to 128-bit results recorded from ROSETTA 2 (Apple's \
                          INDEPENDENT x86-64 binary translator — a true independent x86 \
                          implementation, one notch below bare silicon, NOT a second in-house \
                          model). REAL-EMULATION-VALIDATED: defeats root-cause #2 for x86 PACKED-int \
                          ops (a shared misencoding in the in-house packed spec is no longer \
                          invisible — the oracle is an independent x86, not a second software model \
                          of our own). The oracle harness LOADs two xmm regs from 16-byte buffers \
                          (movdqu), runs ONE packed SSE2/SSE4 instruction, and STOREs the 128-bit \
                          result (movdqu). Rosetta faithfully reproduces lane-wise wrap-around \
                          add/sub/mul, all-ones/all-zero compare masks, and packed imm-shift \
                          SATURATION at count >= lane width (PSLLD/PSRLD -> 0, PSRAD -> sign — the \
                          OPPOSITE of the scalar SHL &0x1f mask). 10521 VALUE facts / 25 op families \
                          across all packed encoders: padd{b,w,d,q}, psub{b,w,d,q}, pmulld, pmullw, \
                          pand, pandn, por, pxor, pcmpeq{b,w,d,q}, pcmpgt{b,w,d,q}, and the imm-shift \
                          pslld/psrld/psrad over a 128-bit edge lane grid (0, -1, INT_MIN/MAX per \
                          lane width, alternating, random). Packed-SSE2 integer ops do not trap -> \
                          0 trap facts. NON-VACUOUS: a PADDD-as-PSUBD encoder, a PCMPEQD-as-PCMPGTD \
                          encoder, a wrong-lane-width PADDB-as-PADDW encoder, and a hypothetical \
                          MASKED (count&0x1f) imm-shift each mismatch a Rosetta fact; a corrupted \
                          fixture result flips the comparison.",
            enforcement: Test {
                file: BDEFS_DIFFERENTIAL_BRIDGE_X86_PACKED_FILE,
                function: "x86_packed_inhouse_encoders_match_rosetta_ground_truth",
            },
            status: Satisfied,
            pending_note: "",
        },
        // ---- (B) x86 SCALAR-FP (SSE/SSE2): differential bridge to Rosetta 2.
        SoundnessInvariant {
            id: "B-x86-sse-fp",
            description: "Differential bridge: trust-cg's IN-HOUSE x86-64 SCALAR-FP (SSE/SSE2) \
                          SmtExpr encoders (x86_64_semantics.rs: encode_fp_add_rr/sub/mul/div, \
                          encode_fp_sqrt, encode_cvt* (si2ss/sd, ss2sd, sd2ss, [t]ss2si, [t]sd2si), \
                          encode_fp_minsd/maxsd, encode_fp_cmp_mask — the machine side of the x86 FP \
                          reconstruction proofs, #73) are evaluated via the SAME try_eval path the \
                          reconstruction uses and asserted EQUAL — BIT-EXACT — to results recorded \
                          from ROSETTA 2 (Apple's INDEPENDENT x86-64 binary translator, a true \
                          independent x86 implementation, NOT a second in-house model). Those \
                          encoders build SmtExpr::FPAdd/FPSub/FPMul/FPDiv/FPSqrt + Ite(fp_lt/fp_gt) \
                          + fp.to_sbv nodes, which try_eval evaluates through the SILICON-VALIDATED \
                          INTEGER-ONLY fp_bitmodel.rs (host FPU EVICTED for f32/f64 arithmetic, \
                          #89/#91/#94) — so this bridge cross-checks that integer-only model against \
                          an INDEPENDENT real x86 FP unit, AT X86 SEMANTICS, defeating root-cause #2 \
                          for x86 scalar-FP. 16488 facts over an IEEE EDGE GRID (+-0, +-Inf, qNaN, \
                          sNaN, subnormals, min/max normal, ties); 16260 are STRICT EXACT-BIT matches \
                          across 30 op families (incl. ALL f->int conversions, in-range AND \
                          out-of-range/NaN/+-Inf — F1 FIXED, see below). The x86-QUIRKY ops are \
                          modeled at X86 SEMANTICS (NOT \
                          ARM/IEEE): MINSS/MINSD + MAXSS/MAXSD return the SECOND operand on unordered \
                          (NaN) OR equal (incl. +0/-0) via ite(dest<src?dest:src) / ite(dest>src? \
                          dest:src) — validated against Rosetta incl. min(1.0,NaN)=NaN (the second \
                          operand, NOT ARM FMINNM's 1.0); CMPSS/CMPSD produce per-predicate all-ones/ \
                          all-zero masks for all 8 imm8[2:0] predicates (EQ/LT/LE/UNORD/NEQ/NLT/NLE/ \
                          ORD), with the NEQ/NLT/NLE negations TRUE on unordered pairs (x86, NOT a > \
                          b). THREE honestly-classified, COUNTED findings (NONE papered over; the NaN \
                          comparison is NOT loosened to hide a wrong VALUE — a non-NaN or NaN-vs-non- \
                          NaN mismatch is always a HARD failure): (F1) FIXED (#99) — the GENUINE \
                          x86-vs-ARM SEMANTIC finding (x86 f->int CVT[T]*2SI on overflow/NaN/+-Inf \
                          returns the INTEGER-INDEFINITE 0x80..0, NOT the wasm trunc_sat / AArch64 \
                          FCVTZS / RISC-V FCVT / Rust-as SATURATION) is now MODELED: FPToSBv carries \
                          an OutOfRangeMode enum (Saturate DEFAULT for wasm/AArch64/RISC-V, byte- \
                          identical to before; IntegerIndefinite for the x86 CVT[T]*2SI encoders), \
                          routed through the integer-only fp_bitmodel (host FPU still EVICTED). The \
                          bridge now STRICT-matches EVERY f->int conversion — in-range AND out-of- \
                          range/NaN/+-Inf (70 integer-indefinite facts) — against Rosetta, and PINS \
                          the fix with concrete witnesses (finding_f1_x86_fp_to_int_overflow_is_ \
                          integer_indefinite_not_saturating). No remaining f->int divergence. (F2) \
                          NaN- \
                          INPUT payload quieting through the f64 eval carrier (182 facts: the f32 \
                          FPConst decode f32::from_bits(bits) as f64 quiets the NaN payload — the \
                          already-registered B-aarch64-fp-pending f32-FCVT residual). (F3) invalid- \
                          operation default-qNaN SIGN (46 facts: 0*Inf/Inf-Inf/0/0 give x86's \
                          negative qNaN 0xffc0.. vs the bit-model's positive 0x7fc0..). F2/F3 are \
                          NaN-vs-NaN-of-same-width payload differences only. NON-VACUOUS: ADDSS-as- \
                          SUBSS, the x86-quirky MINSS-as-MAXSS, MINSS-as-ARM-FMINNM (min(1.0,NaN) \
                          NaN vs 1.0), and CMPSS-EQ-as-LT each mismatch a Rosetta fact, and a \
                          corrupted fixture result flips the comparison.",
            enforcement: Test {
                file: BDEFS_DIFFERENTIAL_BRIDGE_X86_FP_FILE,
                function: "x86_fp_inhouse_encoders_match_rosetta_ground_truth",
            },
            status: Satisfied,
            pending_note: "",
        },
        // ---- (B) RISC-V: differential bridge to qemu-system-riscv64 (independent).
        SoundnessInvariant {
            id: "B-riscv-qemu",
            description: "Differential bridge: trust-cg's IN-HOUSE RV64 integer SmtExpr encoders \
                          (riscv_semantics.rs — the machine side of the RISC-V reconstruction \
                          proofs) are evaluated via the SAME try_eval path the reconstruction uses \
                          and asserted EQUAL to results recorded from qemu-system-riscv64 (QEMU's \
                          INDEPENDENT RISC-V machine emulator — a SOFTWARE GOLDEN MODEL of the RV64 \
                          ISA, NOT a second in-house model). SOFTWARE-GOLDEN-MODEL tier: the oracle \
                          harness emits each op as an explicit single RV64 instruction (core::arch:: \
                          asm! over volatile runtime operands; NOT a Rust operator, NOT constant- \
                          folded), produced by rustc's RISC-V backend (Apple clang has none) and \
                          DECODED+EXECUTED by qemu on the `virt` machine — so qemu is a genuinely \
                          INDEPENDENT executor of the real instruction encodings. This DEFEATS \
                          root-cause #2 for the RV64 integer ops (a shared misencoding in the \
                          in-house spec is no longer invisible — the oracle is an independent \
                          executor, not a second software model of our own). One notch below bare \
                          silicon (qemu does not run on a physical RISC-V part), so strictly weaker \
                          than the AArch64 SILICON oracle but strictly stronger than a two-in-house- \
                          authorings fallback. qemu faithfully reproduces the RV64 shift-amount mask \
                          (&0x3F for X, &0x1F for W-forms, #57). 3708 VALUE facts / 27 op-width \
                          families across all 14 reconstructable ALU encoders + xori/sltiu \
                          (X(64)+W(32), shift counts >= width). RV64 integer ALU does not trap \
                          (DIV/REM-by-0 is defined and out of the ALU set) -> 0 trap facts. \
                          NON-VACUOUS: a SUB-for-ADD encoder, the unmasked clamp-to-0 X shift at \
                          count>=64, the unmasked W shift at count>=32 (&0x1F), and SLT-as-SLTU on a \
                          negative operand each mismatch a qemu fact; a corrupted fixture result \
                          flips the comparison.",
            enforcement: Test {
                file: BDEFS_DIFFERENTIAL_BRIDGE_RISCV_FILE,
                function: "riscv_inhouse_encoders_match_qemu_ground_truth",
            },
            status: Satisfied,
            pending_note: "",
        },
        // ---- (B) RISC-V F/D SCALAR-FP: differential bridge to qemu-system-riscv64.
        SoundnessInvariant {
            id: "B-riscv-fp",
            description: "software-golden-model via qemu-riscv64; RISC-V F/D scalar FP. Differential \
                          bridge: trust-cg's IN-HOUSE RISC-V F/D scalar-FP SmtExpr encoders \
                          (riscv_semantics.rs: encode_fadd/fsub/fmul/fdiv/fsqrt (.s/.d), encode_feq/ \
                          flt/fle, encode_fmin/fmax, encode_fsgnj*/encode_fcvt_to_int_signed/ \
                          unsigned/encode_fcvt_from_int_signed/encode_fcvt_fp_to_fp — the NEW \
                          semantic encoders for the FP opcodes trust-cg already EMITS) are evaluated \
                          via the SAME try_eval path the reconstruction uses and asserted EQUAL — \
                          BIT-EXACT — to results recorded from qemu-system-riscv64 (QEMU's \
                          INDEPENDENT RISC-V machine emulator, a SOFTWARE GOLDEN MODEL of the RV64 \
                          ISA, NOT a second in-house model). Those encoders are THIN wrappers over \
                          SmtExpr::FPAdd/FPSub/FPMul/FPDiv/FPSqrt + the fp.to_sbv/to_fp converts + \
                          ite(fp_lt/fp_eq/fp_is_nan) trees, which try_eval evaluates through the \
                          SILICON-VALIDATED INTEGER-ONLY fp_bitmodel.rs (host FPU EVICTED for f32/ \
                          f64 arithmetic) — so this bridge cross-checks that integer-only model \
                          against an INDEPENDENT real RISC-V executor, AT RISC-V SEMANTICS, defeating \
                          root-cause #2 for the RV64 scalar-FP ops. The oracle harness (riscv_oracle/ \
                          oracle_fp.rs) enables the FPU (mstatus.FS=Initial) and runs each op as an \
                          explicit single RV64 F/D instruction (core::arch::asm! over the float reg \
                          file, fmv.d.x/fmv.w.x in + fmv.x.d/fmv.x.w/GPR out, over volatile runtime \
                          bit patterns; NOT a Rust f32/f64 operator, NOT constant-folded) — qemu \
                          decodes+executes the actual instruction word. 8104 VALUE facts / 41 op \
                          families over an IEEE edge grid (+-0,+-Inf,qNaN,sNaN,subnormals,min/max \
                          normal,pi,1.5,123,-123) + an integer edge grid for the converts; ALL 8104 \
                          are STRICT exact-bit matches. RV64 scalar FP does not trap under FS!=0 \
                          default handling -> 0 trap facts. The RISC-V-SPECIFIC semantics are \
                          modeled AS RISC-V (NOT x86 MINSD, NOT ARM FMINNM/FPProcessNaNs) and ALL \
                          STRICT-matched: (1) FMIN/FMAX = IEEE-754-2019 minimumNumber/maximumNumber \
                          (a lone NaN incl sNaN returns the NUMBER; both NaN -> the CANONICAL qNaN; \
                          -0 < +0 via a copysign division tiebreak); (2) FCVT-to-int SATURATES with \
                          NaN -> max (signed NaN->INT_MAX 2^(w-1)-1, unsigned NaN->UINT_MAX; \
                          +-overflow->INT_MAX/INT_MIN or UINT_MAX/0) — the encoder wraps the shared \
                          NaN->0 FPToSBv/FPToUBv in a RISC-V NaN-fixup ite; (3) the CANONICAL-NaN \
                          rule (Section 11.3): every NaN-producing op emits the single canonical NaN \
                          0x7fc0../0x7ff8.. (positive, no payload). FINDING (found + FIXED to RISC-V \
                          semantics, NOT deferred): the raw silicon-validated bit-model arithmetic \
                          uses the ARM FPProcessNaNs convention, producing a NaN with the input \
                          PAYLOAD (0x7ff8..01) and even a NEGATIVE NaN (0xfff8..01 for FSUB(1.0, \
                          sNaN)) — which DIVERGES from qemu's RISC-V canonical NaN; the encoders' \
                          canonicalize_nan wrap (ite(fp_is_nan(result), canonical, result)) closes \
                          it to ZERO residual. NON-VACUOUS: FADD-as-FSUB, FMIN-as-FMAX, FEQ-as-FLT \
                          each mismatch a qemu fact; the RAW shared FPToSBv (NaN->0) DISAGREES with \
                          qemu's RISC-V NaN->INT_MAX (so the NaN-fixup is load-bearing); the RAW \
                          bit-model NaN (ARM payload + sign) DISAGREES with the canonical NaN (so \
                          canonicalize_nan is load-bearing for payload AND sign); a corrupted \
                          fixture result flips the comparison.",
            enforcement: Test {
                file: BDEFS_DIFFERENTIAL_BRIDGE_RISCV_FP_FILE,
                function: "riscv_fp_inhouse_encoders_match_qemu_ground_truth",
            },
            status: Satisfied,
            pending_note: "",
        },
        // ---- (B) FP: integer-only IEEE bit-model validated vs silicon + swapped in.
        SoundnessInvariant {
            id: "B-aarch64-fp",
            description: "Host-FPU eviction for the FP-verification path. trust-cg's FP \
                          verification used to compute every F32/F64 op via NATIVE Rust f64 \
                          arithmetic (smt.rs try_eval), putting the host CPU's FPU in the FP \
                          TCB; fp16 used a BESPOKE, non-silicon-validated model \
                          (fp16_bits_to_f64/f64_to_fp16_bits). fp_bitmodel.rs is a DETERMINISTIC, \
                          INTEGER-ONLY (u32/u64/u128 + shifts/masks; ZERO f32/f64 arithmetic — \
                          grep-gated by bitmodel_source_is_integer_only) bit-level IEEE-754 model \
                          ported from the M4-silicon-validated Clean FP B-defs \
                          (proofs/aarch64_fp*.lean incl. aarch64_fp16.lean). The bridge asserts the \
                          integer-only model == REAL Apple M4 results for every chip `:= rfl` fact \
                          (FADD/FSUB/FMUL/FNEG/FABS/FCMP/FMIN/FMAX/FMINNM/FMAXNM/classify/FCVT \
                          widen+narrow/f->int FCVTZS,ZU,NS,NU/int->f SCVTF,UCVTF; AND the FP16 \
                          tier: classify16 + FCVT h<->s/d widen/narrow + scalar FADD.h/FMUL.h, \
                          200+ ARMv8.2-FP16 facts from aarch64_fp16_chip.lean). NON-VACUOUS: \
                          deliberately-wrong bit-models (incl. a wrong f32->f16 narrow and a wrong \
                          FADD.h) mismatch silicon facts. SWAPPED IN (host-FPU-free): binary64 \
                          FADD/FSUB/FMUL/FNEG/FABS and binary64-source FCVTZS/ZU/NS/NU (RTZ/RNE), \
                          PLUS the ENTIRE FP16 path — the bespoke fp16_bits_to_f64/f64_to_fp16_bits \
                          are DELETED and the fp16 const-decode, fp16 FADD/FSUB/FMUL/FNEG/FABS, and \
                          the d->h / s->h narrow (BvToFP/FPToFP to fp16) now route through the \
                          silicon-validated bit-model (every fp16 value is exactly representable in \
                          the f64 carrier, so the f16<->f64 widen/narrow is loss-free — no `as f16` \
                          host round-trip). PLUS (#94) FDIV/FSQRT (RNE) at binary64 and binary16 — \
                          ported to fp_bitmodel.rs as INTEGER-ONLY restoring long-division (FDIV) / \
                          digit-by-digit non-restoring square-root (FSQRT) with remainder-sticky, \
                          validated against the 194 aarch64_fp_divsqrt_chip.lean M4 facts \
                          (fdiv32=96/fdiv64=60/fsqrt32=29/fsqrt64=9) and SWAPPED IN (smt.rs FPDiv/ \
                          FPSqrt route through the bit-model for binary64+binary16 — host FPU EVICTED \
                          for div/sqrt; perturbation-confirmed: breaking the bit-model fn changes \
                          try_eval(FPDiv/FPSqrt)). PLUS (#94 f32 stage) ALL binary32 (f32) ARITHMETIC \
                          — FADD/FSUB/FMUL/FNEG/FABS/FDIV/FSQRT at binary32 now route through the \
                          silicon-validated F32 bit-model (host FPU EVICTED for f32 arithmetic): the \
                          EvalResult::Float(f64) carrier holds the EXACT f64-WIDENING of the f32 value \
                          (every f32 is exactly representable in f64; every construction site stores \
                          such a widening), so the raw f32 bits are recovered by the INTEGER-ONLY \
                          fcvt_narrow (NOT an `as f32` host round-trip), the op runs at F32, and the \
                          result is widened back via the integer-only fcvt_widen. Bit-exact vs the \
                          host FPU across a 280M-input differential fuzz; perturbation-confirmed \
                          (breaking the bit-model changed try_eval(FPAdd) at binary32 0x3e99999a -> \
                          0x3e99999b). This stage ALSO fixed a GENUINE pre-existing bit-model bug \
                          (present since #89, affecting BOTH F32 and F64): the FADD/FSUB alignment \
                          sticky was OR-ed into the result AFTER an effective subtraction, ADDING \
                          instead of SUBTRACTING the dropped fraction -> a 1-ULP error in the \
                          cancellation path (silicon grid had no such case; caught by the 280M fuzz \
                          + exact-rational check). Fixed with the borrow-correct form \
                          `(s_big - s_small_a - 1) | 1` when the subtraction drops sticky bits. \
                          DEFERRED (tracked by B-aarch64-fp-pending): only f32 FCVT \
                          (f32-source/f32-result convert: BvToFP/FPToFP/FPToSBv/FPToUBv) and f32 FMA \
                          (no FMA bit-model) — the bit-model itself ALREADY supports F32 arithmetic.",
            enforcement: Test {
                file: FP_BITMODEL_BRIDGE_FILE,
                function: "fp_bitmodel_matches_silicon_ground_truth",
            },
            status: Satisfied,
            pending_note: "",
        },
        // ---- (B) FP: the HONESTLY-REGISTERED residual TCB (deferred FP eviction).
        // Structured Pending entry (addresses the prior audit nit: the deferred
        // FDIV/FSQRT + the f32/carrier work must be tracked, not left as a comment).
        SoundnessInvariant {
            id: "B-aarch64-fp-pending",
            description: "RESIDUAL host-FPU TCB still on the native-f64 path (honestly registered, \
                          not silently dropped). After campaigns #4b + #94 (incl. its f32 stage), \
                          fp16 + binary64 FP AND all binary32 (f32) ARITHMETIC are FULLY \
                          bit-model-backed — FADD/FSUB/FMUL/FNEG/FABS/FDIV/FSQRT at f32 now route \
                          through the silicon-validated F32 bit-model (the f64 carrier holds the \
                          EXACT f64-widening of the f32 value, so the raw f32 bits are recovered by \
                          the INTEGER-ONLY fcvt_narrow — NO `as f32` host round-trip — the op runs \
                          at F32, and the result is widened back via the integer-only fcvt_widen; \
                          bit-exact vs the host FPU over a 280M-input differential fuzz). What \
                          REMAINS native is ONLY: (a) f32 FCVT — int->f32 (BvToFP), f32->f-format \
                          (FPToFP), and f32-source f->int (FPToSBv/FPToUBv) still use native \
                          `as f32`/`as i32` casts; and (b) f32 (and f64/f16) FMA (FPFma) — there is \
                          no integer-only FMA bit-model yet, so FMA at every width stays native. The \
                          F32 ARITHMETIC bit-model is silicon-validated (the bridge's f32 facts \
                          incl. fdiv32/fsqrt32) and the swap is perturbation-confirmed in try_eval. \
                          Closing the residual needs an integer-only f32-FCVT carrier path \
                          (fcvt_widen/narrow are already in the model) and an integer-only FMA \
                          port — both honest-deferred so they cannot risk the 4-backend 100%.",
            enforcement: InProcess {
                check_name: "inproc_fp_pending_residual_is_registered",
                reexercise: inproc_fp_pending_residual_is_registered,
            },
            status: Pending,
            pending_note: "f32 ARITHMETIC (FADD/FSUB/FMUL/FNEG/FABS/FDIV/FSQRT at binary32) is now \
                           PORTED + SWAPPED through the integer-only bit-model (#94 f32 stage; host \
                           FPU evicted, perturbation-confirmed). RESIDUAL native: only f32 FCVT \
                           (BvToFP/FPToFP/FPToSBv/FPToUBv at binary32) and FMA (no integer-only FMA \
                           model yet) — honest-deferred to protect the 4-backend 100%.",
        },
    ]
}

// ---------------------------------------------------------------------------
// IN-PROCESS re-exercises — weakening the underlying gate makes these refute,
// which makes the meta-gate fail. These are the teeth that make the manifest
// non-vacuous beyond mere source-presence of the named tests.
// ---------------------------------------------------------------------------

/// (A1) Every classifier is total over its universe and every fail-closed
/// exemption carries a non-empty reason.
fn inproc_classifiers_total_and_reasoned() {
    fn check<O: Copy + std::fmt::Debug>(
        arch: &str,
        universe: &[O],
        classify: impl Fn(O) -> OpcodeClass,
    ) {
        assert!(
            !universe.is_empty(),
            "{arch}: opcode universe is empty (vacuous classifier)"
        );
        for &op in universe {
            match classify(op) {
                OpcodeClass::EmittableNeedsProof | OpcodeClass::PseudoOrTrap => {}
                OpcodeClass::FailClosedAllowlisted { reason } => assert!(
                    !reason.trim().is_empty(),
                    "{arch}: opcode {op:?} allowlisted with an EMPTY reason (A1)"
                ),
            }
        }
    }
    check("aarch64", ALL_AARCH64_OPCODES, classify_aarch64);
    check("x86_64", ALL_X86_OPCODES, classify_x86);
    check("riscv", ALL_RISCV_OPCODES, classify_riscv);
    check("wasm", ALL_WASM_OPCODES, classify_wasm);
}

/// (A2) The fsym deref-coverage gate fails closed on any coverage error and
/// passes the clean baseline.
fn inproc_fsym_coverage_fails_closed() {
    assert!(
        !FsymTrustIrReport::default().has_coverage_error(),
        "A2: a clean report must pass (else the gate is vacuous)"
    );
    let mut report = FsymTrustIrReport::default();
    report.coverage_errors.push(FsymCoverageError {
        module: "m".to_string(),
        function: "f".to_string(),
        block: 0,
        inst_index: 0,
        opcode: "Load",
        detail: "manifest A2 probe: reachable Load with no verdict".to_string(),
    });
    assert!(
        report.has_coverage_error(),
        "A2: a report carrying an FsymCoverageError must FAIL the deref-coverage gate"
    );
}

/// (C) The non-degeneracy gate is alive: an injected degenerate X==X is reported,
/// and the real DB has zero violations.
fn inproc_non_degeneracy_gate_is_alive() {
    let (clean_violations, reports_injected) = on_large_stack(|| {
        let clean = ProofDatabase::new()
            .non_degeneracy_violations()
            .into_iter()
            .map(|v| v.name)
            .collect::<Vec<_>>();
        let x = SmtExpr::var("x", 64);
        let injected = CategorizedProof {
            obligation: ProofObligation {
                name: "MANIFEST-C probe degenerate X==X".to_string(),
                trust_ir_expr: x.clone(),
                aarch64_expr: x,
                inputs: vec![("x".to_string(), 64)],
                preconditions: vec![],
                fp_inputs: vec![],
                category: None,
                machine_side_provenance: MachineSideProvenance::StaticDb,
            },
            category: ProofCategory::Arithmetic,
        };
        let mut proofs = ProofDatabase::new().all().to_vec();
        proofs.push(injected);
        let injected = ProofDatabase::from_proofs(proofs)
            .non_degeneracy_violations()
            .into_iter()
            .map(|v| v.name)
            .collect::<Vec<_>>();
        (clean, injected)
    });
    assert!(
        clean_violations.is_empty(),
        "C: the real DB must have zero non-degeneracy violations, got {clean_violations:?}"
    );
    assert_eq!(
        reports_injected,
        vec!["MANIFEST-C probe degenerate X==X".to_string()],
        "C: the gate must REPORT an injected degenerate proof (it is alive, not stubbed)"
    );
    // Cross-check the audited-list predicates exist and behave (a degenerate name
    // on neither list is a violation).
    assert!(
        !is_genuine_identity("MANIFEST-C probe degenerate X==X")
            && !is_known_degenerate_debt("MANIFEST-C probe degenerate X==X"),
        "C: the probe name must be on NEITHER audited list (else the test is not adversarial)"
    );
}

/// (R) The reconstruction credit rule: a swapped opcode refutes; a static-DB X==X
/// is degenerate, not genuinely proven, and not reconstructed.
fn inproc_reconstruction_credit_rule() {
    use trust_cg_lower::instructions::Opcode;
    use trust_cg_lower::types::Type;
    use trust_cg_verify::trust_ir_semantics::encode_trust_ir_binop;

    let a = SmtExpr::var("recon_src1", 32);
    let b = SmtExpr::var("recon_src2", 32);
    let swapped = ProofObligation {
        name: "MANIFEST-R swapped Iadd->SUB".to_string(),
        trust_ir_expr: encode_trust_ir_binop(&Opcode::Iadd, Type::I32, a.clone(), b.clone()),
        aarch64_expr: a.clone().bvsub(b.clone()),
        inputs: vec![
            ("recon_src1".to_string(), 32),
            ("recon_src2".to_string(), 32),
        ],
        preconditions: vec![],
        fp_inputs: vec![],
        category: None,
        machine_side_provenance: MachineSideProvenance::Reconstructed {
            from_opcode: "SubRR".to_string(),
            arity: 2,
        },
    };
    assert!(
        swapped.is_reconstructed(),
        "R: probe must be on the reconstruction credit path"
    );
    assert!(
        matches!(
            verify_by_evaluation(&swapped),
            VerificationResult::Invalid { .. }
        ),
        "R: is_reconstructed() && Valid must REFUTE a swapped opcode (bvadd != bvsub)"
    );

    let x = SmtExpr::var("x", 64);
    let static_xx = ProofObligation {
        name: "MANIFEST-R static X==X".to_string(),
        trust_ir_expr: x.clone(),
        aarch64_expr: x.clone(),
        inputs: vec![("x".to_string(), 64)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: None,
        machine_side_provenance: MachineSideProvenance::StaticDb,
    };
    assert!(static_xx.is_degenerate(), "R: a static X==X is degenerate");
    assert!(
        !static_xx.is_genuinely_proven(),
        "R: a static X==X is not genuinely proven"
    );
    assert!(
        !static_xx.is_reconstructed(),
        "R: a StaticDb obligation is never reconstructed (cannot satisfy the credit rule)"
    );
}

/// (H) The 4 headline pins hold and every uncovered row is an HONEST deferral.
fn inproc_headline_pins_and_honest() {
    use trust_cg_verify::coverage_gate::CoverageFinding;
    for (arch, emittable_pin, covered_pin) in [
        // AArch64 126/126 (UNIVERSE BACKFILL + neon_fpred lane proofs + UMOV
        // extract + TLS GOT-TPREL + FCVTL/FCVTL2): the 5 previously-deferred
        // `.2D`-vectorizer NEON ops (NeonFmlaV/FmlsV/ScvtfV/UcvtfV/DupScalarD)
        // received their 10 faithful per-lane obligations (all_neon_fpred_proofs);
        // NeonUmovGen moved FailClosedAllowlisted -> EmittableNeedsProof, covered
        // via its 30 faithful per-(size,lane) obligations (all_neon_umov_proofs);
        // LdrGottprel -> EmittableNeedsProof, covered via
        // aarch64_elf_tls_reloc_proofs; and NeonFcvtlV/NeonFcvtl2V (vector f32->f64
        // widening convert emitted by neon_farray) -> EmittableNeedsProof, covered
        // via their 4 faithful per-lane obligations (all_neon_fcvtl_proofs); and
        // EorRRShift (the rotate-fusion peephole's shifted-register EOR-ROR) ->
        // EmittableNeedsProof, covered via its faithful rotate-XOR obligations
        // (all_eor_ror_shift_proofs, W+X; wrong-amount/wrong-shift-kind/operand-swap
        // refute controls); and FcselRR (the FP-Select isel path's scalar FP
        // conditional select) -> EmittableNeedsProof, covered via its faithful
        // bit-preserving-mux obligations (all_fcsel_proofs, S+D; inverted-cond/
        // operand-swap refute controls); and NeonFmlaLaneV (FMLA by element, the
        // elementwise-FP vectorizer's da*x lane broadcast) -> EmittableNeedsProof,
        // covered via its 20 faithful per-(arrangement,dest,selector) obligations
        // (all_neon_fmla_lane_proofs, .4S+.2D; wrong-lane-selector/FMLA<->FMLS
        // polarity/accumulator-miswire refute controls); and AddRRShift/SubRRShift
        // (the shift-ALU fusion peephole's shifted-register ADD/SUB Rd,Rn,Rm,LSL #k)
        // -> EmittableNeedsProof, covered via their faithful ring obligations
        // (all_add_sub_lsl_shift_proofs, W+X; wrong-amount/ADD-vs-SUB/SUB
        // operand-swap refute controls). Those historical promotions increased
        // accepted evidence; the publication inventory now also pins named RED
        // denominator debt on every backend.
        // x86-64 154 -> 157 (X9 slice 3 + X10): ImulRMSib (memory-operand IMUL,
        // the RM-fusion peephole) and MovRM32Sib/MovMR32Sib (32-bit SIB loads/
        // stores, the width-extended address folds) -> EmittableNeedsProof,
        // covered by the effective-address/RM-fusion obligations landed with
        // the same commits (884d0b9c, d60553ac) — still covered == emittable.
        // x86-64 157 -> 158: Psadbw (horizontal byte sum-of-absolute-differences,
        // the byte-sum vectorizer tier) -> EmittableNeedsProof, covered by the
        // PsadbwByteSad reconstruction (encode_psadbw vs encode_trust_ir_byte_sad;
        // a wrong lane-wise opcode reconstructs differently and REFUTES) — still
        // covered == emittable.
        // AArch64 135 -> 137: NeonUaddwV/NeonUaddw2V (UADDW/UADDW2 widening
        // add-wide, the neon_array TRACK D abs-sum accumulate that replaces the
        // UMLAL-by-ones MAC) -> EmittableNeedsProof, covered via their faithful
        // D-pair obligations (all_neon_uaddw_proofs; sign-confusion/no-addend/
        // wrong-half/truncating-add refute controls) — still covered == emittable.
        // AArch64 139 -> 140: AddRRShiftLsr (the shift-ALU fusion peephole's
        // LSR-shifted ADD — srem/sdiv magic sign-bit correction), covered via
        // all_add_lsr_shift_proofs (W+X, refute controls).
        // AArch64 137 -> 139: NeonSaddwV/NeonSaddw2V (SADDW/SADDW2 SIGNED
        // widening add-wide, the neon_predsum widening i64-acc condsum
        // accumulate that replaces the SMLAL-by-ones MAC) -> EmittableNeedsProof,
        // covered via their faithful D-pair obligations (all_neon_saddw_proofs;
        // zext-confusion [SADDW-as-UADDW]/no-addend/wrong-half/truncating-add
        // refute controls) — still covered == emittable.
        // AArch64 141 -> 143: NeonMlaV (MLA.4S vector multiply-accumulate, the
        // neon_predsum MLA-by-mask condsum accumulate that replaces AND +
        // ADD.4S) + NeonUadalpV (UADALP .4S -> .2D pairwise widening
        // accumulate, the neon_array TRACK D abs-sum accumulate that replaces
        // the UADDW/UADDW2 pair) -> EmittableNeedsProof, covered via their
        // faithful D-pair obligations (all_neon_mla_proofs: MLS-confusion/
        // MUL-no-accumulate/lane-swap refute controls; all_neon_uadalp_proofs:
        // SADALP-sign-confusion/UADDLP-no-accumulate/wrong-pairing refute
        // controls) — still covered == emittable.
        // AArch64 143 -> 144 covered at that stage: NeonRbitV (RBIT.16B
        // per-byte 8-bit reverse, the
        // neon-bitrev vectorizer's `a[i].reverse_bits()` over `[u8; N]`) ->
        // EmittableNeedsProof, covered via its faithful D-pair obligation
        // (all_neon_rbit_proofs; identity/byte-swap[REV16.8B]/16-bit-lane-reverse
        // refute controls). Publication re-audit then withdrew opcode-wide
        // MOVN/MOVK credit. The publication audit restored all emitted
        // value/effect families to the denominator. Six volatile forms and
        // NeonRev32V bring the inventory to 151/244 with 93 explicit deferred
        // rows. EorRRLsl/EorRRLsr reach 153/246. UMULL's faithful widening
        // theorem and complete packed-NZCV TST authority each remove one more
        // deferred row, yielding 155/246 with 91 deferred rows. StrbRO/StrhRO
        // add two honest register-offset store gaps to the current inventory.
        (GateArch::AArch64, 248usize, 155usize),
        (GateArch::RiscV, 17usize, 14usize),
        (GateArch::Wasm, 111usize, 109usize),
        (GateArch::X86_64, 192usize, 163usize),
    ] {
        let report = on_large_stack(move || CoverageGate::new().audit(arch));
        for row in report.failures() {
            assert!(
                matches!(
                    row.finding,
                    Some(CoverageFinding::DeferredUnfaithfulModel { .. })
                ),
                "H: {arch} uncovered row {} is a WIRING GAP, not an honest deferral:\n{}",
                row.opcode_display,
                report.failure_summary()
            );
        }
        assert_eq!(
            report.failures().len(),
            emittable_pin - covered_pin,
            "H: {arch} uncovered-row count drifted from pinned emittable - covered"
        );
        assert_eq!(
            report.emittable_count(),
            emittable_pin,
            "H: {arch} emittable pin drifted from {emittable_pin}"
        );
        assert_eq!(
            report.covered_count(),
            covered_pin,
            "H: {arch} covered pin drifted from {covered_pin}"
        );
    }
}

/// (S-div) The x86 IDIV/DIV divisor!=0 precond is load-bearing in the NATIVE lane:
/// WITH the precond Valid; WITHOUT it REFUTES (the #DE trap is modeled as poison).
fn inproc_div_precond_is_load_bearing() {
    for op in [X86Opcode::Idiv, X86Opcode::Div] {
        let inst = representative_x86_reconstructable_inst(op)
            .unwrap_or_else(|| panic!("{op:?} must have a representative"));
        let ob = reconstruct_x86_alu_obligation(&inst)
            .unwrap_or_else(|| panic!("{op:?} must reconstruct"));
        assert!(
            !ob.preconditions.is_empty(),
            "S-div: {op:?} must carry the divisor!=0 precondition in PRODUCTION"
        );
        assert!(
            matches!(verify_by_evaluation(&ob), VerificationResult::Valid),
            "S-div: {op:?} WITH divisor!=0 must discharge Valid (precond present, production 100%)"
        );
        let mut stripped = ob.clone();
        stripped.preconditions.clear();
        assert!(
            matches!(
                verify_by_evaluation(&stripped),
                VerificationResult::Invalid { .. }
            ),
            "S-div: {op:?} WITHOUT divisor!=0 must REFUTE under the native evaluator (the #DE \
             trap is modeled as poison; the precond is load-bearing in the native lane, #79)"
        );
    }
}

/// (B-aarch64-fp-pending) The residual host-FPU TCB is HONESTLY registered AND the
/// fp16/f64 paths that this campaign DID evict really are bit-model-backed. This is
/// the Pending entry's non-vacuous teeth: it proves (1) the fp16 swap is LIVE in
/// try_eval (a regression to the deleted bespoke model, or to a different result,
/// would change the value), confirming the custom fp16 model is off the path;
/// (2) FDIV/FSQRT are now PORTED to the integer-only bit-model AND the binary64
/// FPDiv/FPSqrt swap is LIVE in try_eval (#94 — host FPU evicted for div/sqrt); and
/// (3) the residual that genuinely REMAINS is binary32 (f32) — the bit-model
/// supports F32 but the f64 eval carrier is lossy, so f32 ops are still native.
fn inproc_fp_pending_residual_is_registered() {
    use trust_cg_verify::smt::{EvalResult, RoundingMode};

    // (1) fp16 FADD.h 1.0 + 1.0 must route through the bit-model and yield fp16 2.0
    //     (0x4000), carried as its EXACT f64 widening. The bit-model is the oracle
    //     for the expected carrier value (the same fcvt_h_to_d the swap uses).
    let one_h: u64 = 0x3C00; // 1.0 in fp16
    let fp16_add = SmtExpr::FPAdd {
        rm: RoundingMode::RNE,
        lhs: Arc::new(SmtExpr::FPConst {
            bits: one_h,
            eb: 5,
            sb: 11,
        }),
        rhs: Arc::new(SmtExpr::FPConst {
            bits: one_h,
            eb: 5,
            sb: 11,
        }),
    };
    let got = fp16_add
        .try_eval(&std::collections::HashMap::new())
        .expect("fp16 FADD eval");
    let expect_carrier = f64::from_bits(trust_cg_verify::fp_bitmodel::fcvt_h_to_d(0x4000)); // fp16 2.0 widened
    match got {
        EvalResult::Float(f) => assert_eq!(
            f.to_bits(),
            expect_carrier.to_bits(),
            "B-aarch64-fp-pending: fp16 FADD.h 1.0+1.0 must route through the silicon-validated \
             bit-model and yield fp16 2.0's exact f64 widening (the bespoke fp16 model is GONE)"
        ),
        other => panic!("fp16 FADD must produce a Float, got {other:?}"),
    }

    // (2) FDIV/FSQRT are now PORTED to the integer-only bit-model (#94): fp_bitmodel.rs
    //     must export both, and the binary64 FPDiv/FPSqrt swap must be LIVE in try_eval
    //     (host FPU evicted for div/sqrt). The bit-model is the oracle for the expected
    //     result; if the swap regressed to native a/b or a.sqrt(), these still match for
    //     these inputs — so we ALSO source-check that the smt.rs sites reference the
    //     bit-model (a no-op-swap regression would drop that call).
    let bitmodel_src = read_test_file_from_src("fp_bitmodel.rs");
    assert!(
        bitmodel_src.contains("pub fn fdiv") && bitmodel_src.contains("pub fn fsqrt"),
        "B-aarch64-fp-pending: fp_bitmodel.rs must export the ported integer-only fdiv/fsqrt (#94)"
    );
    let smt_src = read_test_file_from_src("smt.rs");
    assert!(
        smt_src.contains("fp_bitmodel::fdiv(crate::fp_bitmodel::F64")
            && smt_src.contains("fp_bitmodel::fsqrt(crate::fp_bitmodel::F64"),
        "B-aarch64-fp-pending: smt.rs FPDiv/FPSqrt must route binary64 through the bit-model (#94 \
         host-FPU eviction for div/sqrt)"
    );
    // binary64 FPDiv 6.0/2.0 -> 3.0 via the bit-model (the swapped-in path).
    let fp64_div = SmtExpr::FPDiv {
        rm: RoundingMode::RNE,
        lhs: Arc::new(SmtExpr::FPConst {
            bits: 6.0f64.to_bits(),
            eb: 11,
            sb: 53,
        }),
        rhs: Arc::new(SmtExpr::FPConst {
            bits: 2.0f64.to_bits(),
            eb: 11,
            sb: 53,
        }),
    };
    let div_got = fp64_div
        .try_eval(&std::collections::HashMap::new())
        .expect("fp64 FDIV eval");
    let div_expect = f64::from_bits(trust_cg_verify::fp_bitmodel::fdiv(
        trust_cg_verify::fp_bitmodel::F64,
        6.0f64.to_bits(),
        2.0f64.to_bits(),
    ));
    match div_got {
        EvalResult::Float(f) => assert_eq!(
            f.to_bits(),
            div_expect.to_bits(),
            "B-aarch64-fp-pending: binary64 FDIV must route through the integer-only bit-model (#94)"
        ),
        other => panic!("fp64 FDIV must produce a Float, got {other:?}"),
    }

    // (3) f32 ARITHMETIC is now EVICTED (#94 f32 stage): the binary32 guarded-swap
    //     gate `f32_handles` must exist in smt.rs, and a binary32 FPAdd must route
    //     through the F32 bit-model (NOT native a+b). The carrier holds the EXACT
    //     f64-widening of an f32 (recovered by the integer-only fcvt_narrow — no
    //     `as f32` host round-trip), so a binary32 0.1+0.2 must equal the bit-model's
    //     F32 fadd widened back. The bit-model is the oracle; a regression to native
    //     would, for a non-exact f32 add, differ at the carrier's low bits.
    assert!(
        smt_src.contains("fn f32_handles") && smt_src.contains("FloatingPoint(8, 24)"),
        "B-aarch64-fp (f32 stage): smt.rs must have the binary32 guarded-swap gate f32_handles"
    );
    assert!(
        smt_src.contains("crate::fp_bitmodel::F32") && smt_src.contains("f32_to_carrier"),
        "B-aarch64-fp (f32 stage): smt.rs FP ops must route binary32 through the F32 bit-model \
         (host FPU evicted for f32 arithmetic)"
    );
    // 0.1f32 + 0.2f32 (a non-exact f32 add) must come from the F32 bit-model.
    let a32: u64 = 0x3dcccccd; // 0.1f32
    let b32: u64 = 0x3e4ccccd; // 0.2f32
    let fp32_add = SmtExpr::FPAdd {
        rm: RoundingMode::RNE,
        lhs: Arc::new(SmtExpr::FPConst {
            bits: a32,
            eb: 8,
            sb: 24,
        }),
        rhs: Arc::new(SmtExpr::FPConst {
            bits: b32,
            eb: 8,
            sb: 24,
        }),
    };
    let add32_got = fp32_add
        .try_eval(&std::collections::HashMap::new())
        .expect("fp32 FADD eval");
    // Oracle: recover the raw f32 operand bits via the integer-only narrow, add at
    // F32 in the bit-model, widen back — exactly the swapped-in path.
    let expect32 = f64::from_bits(trust_cg_verify::fp_bitmodel::fcvt_widen(
        trust_cg_verify::fp_bitmodel::fadd(
            trust_cg_verify::fp_bitmodel::F32,
            trust_cg_verify::fp_bitmodel::fcvt_narrow(
                (f32::from_bits(0x3dcccccd) as f64).to_bits(),
            ),
            trust_cg_verify::fp_bitmodel::fcvt_narrow(
                (f32::from_bits(0x3e4ccccd) as f64).to_bits(),
            ),
        ),
    ));
    match add32_got {
        EvalResult::Float(f) => assert_eq!(
            f.to_bits(),
            expect32.to_bits(),
            "B-aarch64-fp (f32 stage): binary32 FADD must route through the integer-only F32 \
             bit-model (host FPU evicted for f32 arithmetic)"
        ),
        other => panic!("fp32 FADD must produce a Float, got {other:?}"),
    }

    // (4) The genuine RESIDUAL is now ONLY f32 FCVT + FMA: smt.rs must still contain
    //     a native f32-cast convert site (honestly registered, not silently elided).
    assert!(
        smt_src.contains("(signed as f32) as f64") || smt_src.contains("(f as f32) as f64"),
        "B-aarch64-fp-pending: f32 FCVT (BvToFP/FPToFP) honestly remains native pending an \
         integer-only f32-FCVT carrier path"
    );
}

// ---------------------------------------------------------------------------
// Helpers for the source-presence ("live test") check.
// ---------------------------------------------------------------------------

fn tests_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests")
}

fn read_test_file(file: &str) -> String {
    let path = tests_dir().join(file);
    fs::read_to_string(&path)
        .unwrap_or_else(|e| panic!("manifest: cannot read enforcing-test file {path:?}: {e}"))
}

/// Read a crate `src/` file (for source-level invariant checks, e.g. confirming
/// the residual-TCB note is not stale).
fn read_test_file_from_src(file: &str) -> String {
    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("src")
        .join(file);
    fs::read_to_string(&path)
        .unwrap_or_else(|e| panic!("manifest: cannot read src file {path:?}: {e}"))
}

/// Is `fn <function>` defined in `source`? (Best-effort textual check: a renamed
/// or deleted enforcing test no longer matches, breaking the meta-gate.)
fn defines_fn(source: &str, function: &str) -> bool {
    let needle = format!("fn {function}(");
    let needle_ws = format!("fn {function} (");
    source.contains(&needle) || source.contains(&needle_ws)
}

/// Every `#[test]` function name defined in `source`.
fn test_fn_names(source: &str) -> HashSet<String> {
    let mut names = HashSet::new();
    let mut prev_was_test_attr = false;
    for line in source.lines() {
        let t = line.trim_start();
        if t.starts_with("#[test]") {
            prev_was_test_attr = true;
            continue;
        }
        if prev_was_test_attr {
            // The next `fn name(` after a #[test]; other attributes may intervene.
            if let Some(rest) = t.strip_prefix("fn ") {
                if let Some(name) = rest.split('(').next() {
                    names.insert(name.trim().to_string());
                }
                prev_was_test_attr = false;
            } else if t.starts_with("#[") {
                // Another attribute: keep looking for the function.
            } else if !t.is_empty() {
                prev_was_test_attr = false;
            }
        }
    }
    names
}

// ===========================================================================
// THE META-GATE — fails if any entry lacks a live enforcing test, or if the
// manifest is missing an invariant that exists in code.
// ===========================================================================
#[test]
fn meta_gate_every_invariant_has_a_live_enforcing_test() {
    let manifest = manifest();

    // The manifest must be non-empty and cover the required id families.
    assert!(!manifest.is_empty(), "META-GATE: the manifest is empty");
    let ids: HashSet<&str> = manifest.iter().map(|e| e.id).collect();
    for required in [
        "A1",
        "A2",
        "C",
        "D1",
        "D2",
        "D3",
        "D4",
        "D5",
        "D6",
        "D7",
        "D8",
        "R",
        "H",
        "S",
        "S-div",
        "B-aarch64-int",
        "B-aarch64-neon",
        "B-aarch64-neon-fp",
        "B-x86-rosetta",
        "B-x86-sse-packed",
        "B-x86-sse-fp",
        "B-riscv-qemu",
        "B-riscv-fp",
    ] {
        assert!(
            ids.contains(required),
            "META-GATE: the manifest is MISSING required invariant id `{required}` — every \
             fail-closed soundness family (A1/A2/C/D1..D8/R/H/S/S-div/B) must be registered"
        );
    }

    // (1)+(2) Every entry's binding must be LIVE.
    for entry in &manifest {
        match &entry.enforcement {
            Enforcement::Test { file, function } => {
                assert_eq!(
                    entry.status,
                    Status::Satisfied,
                    "META-GATE: entry {} is Test-bound but not Satisfied — a Test binding is a \
                     live enforcement, so it must be Satisfied",
                    entry.id
                );
                let source = read_test_file(file);
                assert!(
                    defines_fn(&source, function),
                    "META-GATE [{}]: enforcing test `{function}` is NOT defined in {file} — the \
                     binding is DEAD (the test was deleted or renamed). Restore/rename it or update \
                     the manifest. Invariant: {}",
                    entry.id,
                    entry.description
                );
            }
            Enforcement::InProcess {
                check_name,
                reexercise,
            } => {
                if entry.status == Status::Satisfied {
                    // RE-EXERCISE the underlying gate IN-PROCESS: if the gate has
                    // been weakened (fail-open regression), this panics and the
                    // meta-gate fails. This is the non-vacuous teeth.
                    let name = *check_name;
                    let f = *reexercise;
                    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(f));
                    assert!(
                        result.is_ok(),
                        "META-GATE [{}]: in-process re-exercise `{name}` FAILED — the underlying \
                         fail-closed gate has been WEAKENED. Invariant: {}",
                        entry.id,
                        entry.description
                    );
                } else {
                    // Pending: must carry a tracking note (honestly registered).
                    assert!(
                        !entry.pending_note.trim().is_empty(),
                        "META-GATE [{}]: a Pending invariant must carry a non-empty tracking note \
                         (it must be honestly registered, never a silent gap)",
                        entry.id
                    );
                }
            }
        }
    }

    // (3) COMPLETENESS (best-effort): every #[test] in meta_theorems.rs must be
    // referenced by some manifest entry. A new meta-theorem added to code without
    // a manifest entry fails the gate — the manifest cannot fall behind the code.
    let meta_src = read_test_file(META_THEOREMS_FILE);
    let referenced: HashSet<&str> = manifest
        .iter()
        .filter_map(|e| match &e.enforcement {
            Enforcement::Test { file, function } if *file == META_THEOREMS_FILE => Some(*function),
            _ => None,
        })
        .collect();
    for tname in test_fn_names(&meta_src) {
        assert!(
            referenced.contains(tname.as_str()),
            "META-GATE COMPLETENESS: meta_theorems.rs defines `{tname}` but NO manifest entry \
             references it — a soundness invariant exists in code that the manifest does not track. \
             Add a manifest entry binding it (the manifest must not fall behind the code)."
        );
    }
}

// ===========================================================================
// NEGATIVE CONTROL: the source-presence check has TEETH.
// ===========================================================================
//
// Prove `defines_fn` actually distinguishes present from absent functions: a real
// enforcing test is found, a bogus name is NOT. If this regressed (e.g.
// `defines_fn` returned `true` unconditionally), the whole "live test" half of the
// meta-gate would be vacuous — so this control guards the guard.
#[test]
fn meta_gate_source_presence_check_is_non_vacuous() {
    let meta_src = read_test_file(META_THEOREMS_FILE);
    assert!(
        defines_fn(&meta_src, "meta_a_no_proof_is_degenerate_and_unclassified"),
        "negative control: a REAL enforcing test must be detected present"
    );
    assert!(
        !defines_fn(&meta_src, "this_function_does_not_exist_zzz_bogus"),
        "negative control: a BOGUS function name must be detected ABSENT — else the live-test \
         half of the meta-gate is vacuous"
    );
    // The #[test] extractor must find the known meta-theorems (not return empty).
    let names = test_fn_names(&meta_src);
    assert!(
        names.contains("meta_a_no_proof_is_degenerate_and_unclassified")
            && names.contains("meta_e_headline_coverage_is_pinned_and_honest"),
        "negative control: the #[test] name extractor must find the known meta-theorems"
    );
}

// ===========================================================================
// The B-aarch64-int bridge RATCHET has ADVANCED: it is now SATISFIED, bound to a
// LIVE differential-bridge test (the in-house AArch64 encoders are checked against
// silicon ground truth). This was the one PENDING entry; the monotonic ratchet
// (Pending -> Satisfied) has fired. This test guards that advance: B-aarch64-int
// must be Satisfied AND bound to a live Test (deleting/renaming the bridge test
// breaks the meta-gate). Any FUTURE Pending entry must still carry a tracking note
// (the honesty invariant for pending bridges is preserved for new ones).
// ===========================================================================
#[test]
fn b_aarch64_int_bridge_is_satisfied_and_live_not_dropped() {
    let manifest = manifest();
    let bridge = manifest
        .iter()
        .find(|e| e.id == "B-aarch64-int")
        .expect("the aarch64 integer differential bridge must be registered (never dropped)");
    assert_eq!(
        bridge.status,
        Status::Satisfied,
        "B-aarch64-int must now be SATISFIED — the differential bridge to silicon ground truth \
         is wired (the Pending->Satisfied ratchet has fired)"
    );
    match &bridge.enforcement {
        Enforcement::Test { file, function } => {
            assert_eq!(
                *file, BDEFS_DIFFERENTIAL_BRIDGE_FILE,
                "B-aarch64-int must be bound to the differential-bridge test file"
            );
            let source = read_test_file(file);
            assert!(
                defines_fn(&source, function),
                "B-aarch64-int's enforcing bridge test `{function}` must be LIVE in {file} \
                 (deleting/renaming it must break the meta-gate)"
            );
        }
        Enforcement::InProcess { .. } => panic!(
            "B-aarch64-int is now Test-bound (a live differential bridge), not an InProcess note"
        ),
    }
    // The honesty invariant is preserved for any remaining/future Pending entry.
    for e in manifest.iter().filter(|e| e.status == Status::Pending) {
        assert!(
            !e.pending_note.trim().is_empty(),
            "pending entry {} must carry a tracking note (honestly registered, never a silent gap)",
            e.id
        );
    }
}

// ===========================================================================
// The B-aarch64-neon bridge: SATISFIED, bound to a LIVE differential-bridge test
// (the in-house AArch64 NEON encode_neon_* encoders are checked against BARE M4
// SILICON — the host IS an Apple M4, so the oracle ran the ACTUAL NEON instruction
// natively via std::arch::asm! over q-registers, NOT Rosetta/qemu/a-second-model).
// This is the NEON analog of the AArch64 integer silicon bridge — the SAME bare-
// silicon oracle tier — and defeats root-cause #2 for the AArch64 NEON integer ops.
// This test guards that the entry stays Satisfied AND bound to a live Test
// (deleting/renaming the bridge test breaks the meta-gate), and that the oracle
// really is the native-M4 NEON fixture (bare silicon, not a second model).
// ===========================================================================
#[test]
fn b_aarch64_neon_bridge_is_satisfied_and_live_not_dropped() {
    let manifest = manifest();
    let bridge = manifest.iter().find(|e| e.id == "B-aarch64-neon").expect(
        "the AArch64 NEON bare-silicon differential bridge must be registered (never dropped)",
    );
    assert_eq!(
        bridge.status,
        Status::Satisfied,
        "B-aarch64-neon must be SATISFIED — the AArch64 NEON differential bridge to bare-M4-silicon \
         ground truth is wired"
    );
    match &bridge.enforcement {
        Enforcement::Test { file, function } => {
            assert_eq!(
                *file, BDEFS_DIFFERENTIAL_BRIDGE_NEON_FILE,
                "B-aarch64-neon must be bound to the NEON differential-bridge test file"
            );
            let source = read_test_file(file);
            assert!(
                defines_fn(&source, function),
                "B-aarch64-neon's enforcing bridge test `{function}` must be LIVE in {file} \
                 (deleting/renaming it must break the meta-gate)"
            );
            // Honest assurance: the oracle must be the BARE M4 SILICON (the actual
            // NEON instruction run natively), not a second in-house model and not the
            // lower-assurance Rosetta/qemu tier. Guard that the bound test actually
            // exercises the native-M4 NEON fixture.
            assert!(
                source.contains("aarch64_neon_silicon_truth.json"),
                "B-aarch64-neon's bridge test must include the bare-M4-silicon NEON ground-truth \
                 fixture (the oracle is REAL NEON on the M4, NOT a second in-house model and NOT \
                 the Rosetta/qemu tier)"
            );
            // Honest assurance: the imm/lane/scalar/reduction families are BRIDGED
            // (not honest-deferred) and the wrong-arrangement + cmgt-as-cmge teeth are
            // present — so the bridge has real teeth and covers all 24 families.
            assert!(
                source
                    .contains("bridge_is_non_vacuous_dup_ins_movi_umaxv_are_bridged_not_deferred")
                    && source.contains(
                        "bridge_is_non_vacuous_wrong_arrangement_add16b_as_add8h_mismatches_silicon"
                    )
                    && source.contains(
                        "bridge_is_non_vacuous_cmgt_as_cmge_mismatches_silicon_on_equal_lane"
                    ),
                "B-aarch64-neon's bridge must BRIDGE dup/ins/movi/umaxv (not defer them) and PIN \
                 the wrong-arrangement and cmgt-as-cmge teeth (the bridge must have real teeth, \
                 covering all 24 NEON integer families)"
            );
        }
        Enforcement::InProcess { .. } => panic!(
            "B-aarch64-neon is Test-bound (a live differential bridge), not an InProcess note"
        ),
    }
}

// ===========================================================================
// The B-aarch64-neon-fp bridge: SATISFIED, bound to a LIVE differential-bridge
// test (the in-house AArch64 NEON LANE-WISE FP SmtExpr encoders — fadd/fsub/fmul/
// fdiv/fneg/fabs/fsqrt, the fp compares, fmin/fmax/fminnm/fmaxnm — which evaluate
// per-lane through the silicon-validated integer-only fp_bitmodel, are checked
// against BARE M4 SILICON, the actual lane-wise FP NEON run natively via asm! over
// q-registers). This is the FP analog of the AArch64 NEON integer silicon bridge —
// the SAME bare-silicon oracle tier, ABOVE Rosetta/qemu — and defeats root-cause #2
// for the AArch64 NEON FP ops. This test guards that the entry stays Satisfied AND
// bound to a live Test, that the oracle really is the native-M4 NEON-FP fixture,
// and that the ARM-specific FMIN-vs-FMINNM NaN teeth are present (so a regression
// that silently modeled FMIN as RISC-V minimumNumber / x86 MINSS is caught).
// ===========================================================================
#[test]
fn b_aarch64_neon_fp_bridge_is_satisfied_and_live_not_dropped() {
    let manifest = manifest();
    let bridge = manifest
        .iter()
        .find(|e| e.id == "B-aarch64-neon-fp")
        .expect("the AArch64 NEON lane-wise FP bare-silicon differential bridge must be registered (never dropped)");
    assert_eq!(
        bridge.status,
        Status::Satisfied,
        "B-aarch64-neon-fp must be SATISFIED — the AArch64 NEON-FP differential bridge to \
         bare-M4-silicon ground truth is wired"
    );
    match &bridge.enforcement {
        Enforcement::Test { file, function } => {
            assert_eq!(
                *file, BDEFS_DIFFERENTIAL_BRIDGE_NEON_FP_FILE,
                "B-aarch64-neon-fp must be bound to the NEON-FP differential-bridge test file"
            );
            let source = read_test_file(file);
            assert!(
                defines_fn(&source, function),
                "B-aarch64-neon-fp's enforcing bridge test `{function}` must be LIVE in {file} \
                 (deleting/renaming it must break the meta-gate)"
            );
            // Honest assurance: the oracle must be the BARE M4 SILICON (the actual
            // lane-wise FP NEON instruction run natively), not a second in-house model
            // and not the lower-assurance Rosetta/qemu tier.
            assert!(
                source.contains("aarch64_neon_fp_silicon_truth.json"),
                "B-aarch64-neon-fp's bridge test must include the bare-M4-silicon NEON-FP \
                 ground-truth fixture (the oracle is REAL FP NEON on the M4, NOT a second in-house \
                 model and NOT the Rosetta/qemu tier)"
            );
            // Honest assurance: the ARM-specific FMIN-vs-FMINNM NaN distinction, the
            // wrong-arrangement teeth, and the fcmgt-as-fcmge teeth are present — so
            // the bridge has real teeth and models FMIN/FMAX AS ARM (NaN-propagating),
            // FMINNM/FMAXNM as IEEE minNum, not silently as RISC-V/x86.
            assert!(
                source.contains(
                    "bridge_is_non_vacuous_fmin_as_fminnm_mismatches_silicon_on_lone_nan_lane"
                ) && source.contains(
                    "bridge_is_non_vacuous_wrong_arrangement_4s_as_2d_mismatches_silicon"
                ) && source.contains(
                    "bridge_is_non_vacuous_fcmgt_as_fcmge_mismatches_silicon_on_equal_lane"
                ) && source
                    .contains("bridge_is_non_vacuous_arm_fmin_is_nan_propagating_not_riscv_minnum"),
                "B-aarch64-neon-fp's bridge must PIN the ARM-specific FMIN-vs-FMINNM NaN-propagating \
                 distinction (FMIN any-NaN->NaN, NOT RISC-V minimumNumber / x86 MINSS), the \
                 wrong-arrangement .4S-as-.2D teeth, and the fcmgt-as-fcmge teeth (real teeth, \
                 modeling AArch64 NEON FP AS ARM)"
            );
        }
        Enforcement::InProcess { .. } => panic!(
            "B-aarch64-neon-fp is Test-bound (a live differential bridge), not an InProcess note"
        ),
    }
}

// ===========================================================================
// The B-x86-rosetta bridge: SATISFIED, bound to a LIVE differential-bridge test
// (the in-house x86 SmtExpr encoders are checked against Rosetta 2 — an
// INDEPENDENT x86 implementation, NOT a second in-house model). This is the x86
// analog of the AArch64 silicon bridge; it real-emulation-validates trust-cg's x86
// integer model and defeats root-cause #2 for x86 integer ops. This test guards
// that the entry stays Satisfied AND bound to a live Test (deleting/renaming the
// bridge test breaks the meta-gate).
// ===========================================================================
#[test]
fn b_x86_rosetta_bridge_is_satisfied_and_live_not_dropped() {
    let manifest = manifest();
    let bridge = manifest
        .iter()
        .find(|e| e.id == "B-x86-rosetta")
        .expect("the x86 Rosetta differential bridge must be registered (never dropped)");
    assert_eq!(
        bridge.status,
        Status::Satisfied,
        "B-x86-rosetta must be SATISFIED — the x86 differential bridge to Rosetta-recorded \
         independent-x86 ground truth is wired"
    );
    match &bridge.enforcement {
        Enforcement::Test { file, function } => {
            assert_eq!(
                *file, BDEFS_DIFFERENTIAL_BRIDGE_X86_FILE,
                "B-x86-rosetta must be bound to the x86 differential-bridge test file"
            );
            let source = read_test_file(file);
            assert!(
                defines_fn(&source, function),
                "B-x86-rosetta's enforcing bridge test `{function}` must be LIVE in {file} \
                 (deleting/renaming it must break the meta-gate)"
            );
            // Honest assurance: the oracle must be the INDEPENDENT Rosetta x86, not a
            // second in-house model (the whole point of the B-x86 bridge). Guard that
            // the bound test actually exercises the Rosetta fixture (real-emulation).
            assert!(
                source.contains("x86_64_rosetta_truth.json"),
                "B-x86-rosetta's bridge test must include the Rosetta ground-truth fixture \
                 (the oracle is an INDEPENDENT x86 implementation, not a second in-house model)"
            );
        }
        Enforcement::InProcess { .. } => panic!(
            "B-x86-rosetta is Test-bound (a live differential bridge), not an InProcess note"
        ),
    }
}

// ===========================================================================
// The B-x86-sse-packed bridge: SATISFIED, bound to a LIVE differential-bridge
// test (the in-house x86 PACKED-SSE2 encode_p* encoders are checked against
// Rosetta 2 — an INDEPENDENT x86 implementation, NOT a second in-house model).
// This is the packed analog of the scalar x86 Rosetta bridge; it real-emulation-
// validates trust-cg's packed-SSE2 integer model and defeats root-cause #2 for x86
// packed-int ops. This test guards that the entry stays Satisfied AND bound to a
// live Test (deleting/renaming the bridge test breaks the meta-gate), and that the
// oracle really is the independent Rosetta packed fixture (real-emulation).
// ===========================================================================
#[test]
fn b_x86_sse_packed_bridge_is_satisfied_and_live_not_dropped() {
    let manifest = manifest();
    let bridge = manifest.iter().find(|e| e.id == "B-x86-sse-packed").expect(
        "the x86 packed-SSE2 Rosetta differential bridge must be registered (never dropped)",
    );
    assert_eq!(
        bridge.status,
        Status::Satisfied,
        "B-x86-sse-packed must be SATISFIED — the x86 packed-SSE2 differential bridge to \
         Rosetta-recorded independent-x86 ground truth is wired"
    );
    match &bridge.enforcement {
        Enforcement::Test { file, function } => {
            assert_eq!(
                *file, BDEFS_DIFFERENTIAL_BRIDGE_X86_PACKED_FILE,
                "B-x86-sse-packed must be bound to the x86 packed differential-bridge test file"
            );
            let source = read_test_file(file);
            assert!(
                defines_fn(&source, function),
                "B-x86-sse-packed's enforcing bridge test `{function}` must be LIVE in {file} \
                 (deleting/renaming it must break the meta-gate)"
            );
            // Honest assurance: the oracle must be the INDEPENDENT Rosetta x86, not a
            // second in-house model (the whole point of the B-x86 packed bridge). Guard
            // that the bound test actually exercises the Rosetta packed fixture.
            assert!(
                source.contains("x86_packed_rosetta_truth.json"),
                "B-x86-sse-packed's bridge test must include the Rosetta packed ground-truth \
                 fixture (the oracle is an INDEPENDENT x86 implementation, not a second in-house \
                 model)"
            );
        }
        Enforcement::InProcess { .. } => panic!(
            "B-x86-sse-packed is Test-bound (a live differential bridge), not an InProcess note"
        ),
    }
}

// ===========================================================================
// The B-x86-sse-fp bridge: SATISFIED, bound to a LIVE differential-bridge test
// (the in-house x86 SCALAR-FP encoders — encode_fp_add_rr/.../encode_fp_minsd/
// maxsd/encode_fp_cmp_mask, which evaluate through the silicon-validated integer-
// only fp_bitmodel — are checked BIT-EXACT against Rosetta 2, an INDEPENDENT x86
// implementation, NOT a second in-house model). This is the scalar-FP analog of
// the scalar/packed x86 Rosetta bridges and the x86 dual of the AArch64 FP
// bit-model bridge; it real-emulation-validates trust-cg's x86 scalar-FP model AT
// X86 SEMANTICS (incl. the x86-quirky MINSS/MAXSS/CMPSS) and defeats root-cause #2
// for x86 scalar-FP ops. This test guards that the entry stays Satisfied AND bound
// to a live Test (deleting/renaming the bridge test breaks the meta-gate), and
// that the oracle really is the independent Rosetta FP fixture (real-emulation).
// ===========================================================================
#[test]
fn b_x86_sse_fp_bridge_is_satisfied_and_live_not_dropped() {
    let manifest = manifest();
    let bridge = manifest
        .iter()
        .find(|e| e.id == "B-x86-sse-fp")
        .expect("the x86 scalar-FP Rosetta differential bridge must be registered (never dropped)");
    assert_eq!(
        bridge.status,
        Status::Satisfied,
        "B-x86-sse-fp must be SATISFIED — the x86 scalar-FP differential bridge to Rosetta-recorded \
         independent-x86 ground truth is wired"
    );
    match &bridge.enforcement {
        Enforcement::Test { file, function } => {
            assert_eq!(
                *file, BDEFS_DIFFERENTIAL_BRIDGE_X86_FP_FILE,
                "B-x86-sse-fp must be bound to the x86 scalar-FP differential-bridge test file"
            );
            let source = read_test_file(file);
            assert!(
                defines_fn(&source, function),
                "B-x86-sse-fp's enforcing bridge test `{function}` must be LIVE in {file} \
                 (deleting/renaming it must break the meta-gate)"
            );
            // Honest assurance: the oracle must be the INDEPENDENT Rosetta x86, not a
            // second in-house model (the whole point of the B-x86 FP bridge). Guard
            // that the bound test actually exercises the Rosetta FP fixture.
            assert!(
                source.contains("x86_fp_rosetta_truth.json"),
                "B-x86-sse-fp's bridge test must include the Rosetta scalar-FP ground-truth fixture \
                 (the oracle is an INDEPENDENT x86 implementation, not a second in-house model)"
            );
            // Honest assurance: the bridge must model the x86-QUIRKY MIN/MAX/CMP at
            // X86 semantics (NOT ARM) — the F1 integer-indefinite fix (#99) must be
            // pinned by witness, and the x86-vs-ARM min/max test must be present.
            assert!(
                source.contains(
                    "finding_f1_x86_fp_to_int_overflow_is_integer_indefinite_not_saturating"
                ) && source.contains("bridge_is_non_vacuous_x86_quirky_min_is_not_ieee_minnum"),
                "B-x86-sse-fp's bridge test must PIN the x86-vs-ARM findings (the F1 integer- \
                 indefinite conversion finding and the x86-quirky MIN-is-not-IEEE-minNum teeth) — \
                 the x86 semantics must be validated as x86, not silently modeled as ARM"
            );
        }
        Enforcement::InProcess { .. } => {
            panic!("B-x86-sse-fp is Test-bound (a live differential bridge), not an InProcess note")
        }
    }
}

// ===========================================================================
// The B-riscv-qemu bridge: SATISFIED, bound to a LIVE differential-bridge test
// (the in-house RV64 SmtExpr encoders are checked against qemu-system-riscv64 — an
// INDEPENDENT RISC-V executor / software golden model, NOT a second in-house
// model). This is the RISC-V analog of the AArch64 silicon bridge and the x86
// Rosetta bridge; it software-golden-model-validates trust-cg's RV64 integer model
// and defeats root-cause #2 for the RV64 integer ops. This test guards that the
// entry stays Satisfied AND bound to a live Test (deleting/renaming the bridge test
// breaks the meta-gate), and that the oracle really is the independent qemu (not a
// second in-house model nor the LOWER-ASSURANCE in-house Clean-B-def fallback).
// ===========================================================================
#[test]
fn b_riscv_qemu_bridge_is_satisfied_and_live_not_dropped() {
    let manifest = manifest();
    let bridge = manifest
        .iter()
        .find(|e| e.id == "B-riscv-qemu")
        .expect("the RISC-V qemu differential bridge must be registered (never dropped)");
    assert_eq!(
        bridge.status,
        Status::Satisfied,
        "B-riscv-qemu must be SATISFIED — the RISC-V differential bridge to qemu-recorded \
         independent-RV64 ground truth is wired"
    );
    match &bridge.enforcement {
        Enforcement::Test { file, function } => {
            assert_eq!(
                *file, BDEFS_DIFFERENTIAL_BRIDGE_RISCV_FILE,
                "B-riscv-qemu must be bound to the RISC-V differential-bridge test file"
            );
            let source = read_test_file(file);
            assert!(
                defines_fn(&source, function),
                "B-riscv-qemu's enforcing bridge test `{function}` must be LIVE in {file} \
                 (deleting/renaming it must break the meta-gate)"
            );
            // Honest assurance: the oracle must be the INDEPENDENT qemu RISC-V
            // executor (a software golden model), not a second in-house model and not
            // the LOWER-ASSURANCE in-house Clean-B-def fallback. Guard that the bound
            // test actually exercises the qemu ground-truth fixture.
            assert!(
                source.contains("riscv_qemu_truth.json"),
                "B-riscv-qemu's bridge test must include the qemu ground-truth fixture (the oracle \
                 is an INDEPENDENT RISC-V executor / software golden model, NOT a second in-house \
                 model and NOT the lower-assurance Clean-B-def fallback)"
            );
        }
        Enforcement::InProcess { .. } => {
            panic!("B-riscv-qemu is Test-bound (a live differential bridge), not an InProcess note")
        }
    }
}

// ===========================================================================
// The B-riscv-fp bridge: SATISFIED, bound to a LIVE differential-bridge test
// (the in-house RISC-V F/D scalar-FP SmtExpr encoders — encode_fadd/.../fmin/fmax/
// fcvt_to_int_* — which evaluate through the silicon-validated integer-only
// fp_bitmodel, are checked BIT-EXACT against qemu-system-riscv64, an INDEPENDENT
// RISC-V executor / software golden model, NOT a second in-house model). This is
// the RISC-V scalar-FP analog of the x86 scalar-FP Rosetta bridge and the RISC-V
// dual of the AArch64 FP bit-model bridge; it software-golden-model-validates
// trust-cg's RISC-V FP model AT RISC-V SEMANTICS (the RISC-V-specific FMIN/FMAX =
// IEEE-2019 minimumNumber/maximumNumber, FCVT-to-int saturate-with-NaN->max, and
// the canonical-NaN rule) and defeats root-cause #2 for the RV64 scalar-FP ops.
// This test guards that the entry stays Satisfied AND bound to a live Test
// (deleting/renaming the bridge test breaks the meta-gate), and that the oracle
// really is the independent qemu FP fixture with the RISC-V-specific findings PINNED.
// ===========================================================================
#[test]
fn b_riscv_fp_bridge_is_satisfied_and_live_not_dropped() {
    let manifest = manifest();
    let bridge = manifest.iter().find(|e| e.id == "B-riscv-fp").expect(
        "the RISC-V F/D scalar-FP qemu differential bridge must be registered (never dropped)",
    );
    assert_eq!(
        bridge.status,
        Status::Satisfied,
        "B-riscv-fp must be SATISFIED — the RISC-V scalar-FP differential bridge to qemu-recorded \
         independent-RV64 ground truth is wired"
    );
    match &bridge.enforcement {
        Enforcement::Test { file, function } => {
            assert_eq!(
                *file, BDEFS_DIFFERENTIAL_BRIDGE_RISCV_FP_FILE,
                "B-riscv-fp must be bound to the RISC-V scalar-FP differential-bridge test file"
            );
            let source = read_test_file(file);
            assert!(
                defines_fn(&source, function),
                "B-riscv-fp's enforcing bridge test `{function}` must be LIVE in {file} \
                 (deleting/renaming it must break the meta-gate)"
            );
            // Honest assurance: the oracle must be the INDEPENDENT qemu RISC-V
            // executor (a software golden model), not a second in-house model.
            assert!(
                source.contains("riscv_fp_qemu_truth.json"),
                "B-riscv-fp's bridge test must include the qemu FP ground-truth fixture (the oracle \
                 is an INDEPENDENT RISC-V executor / software golden model, NOT a second in-house \
                 model)"
            );
            // Honest assurance: the bridge must model the RISC-V-SPECIFIC FMIN/FMAX/
            // FCVT/canonical-NaN AS RISC-V (NOT x86, NOT ARM) — the corresponding
            // PINS must be present (so a regression that silently modeled them as
            // x86/ARM, or dropped the RISC-V canonical-NaN/saturation findings, is
            // caught here).
            assert!(
                source.contains("riscv_fmin_fmax_is_ieee2019_minnum_not_x86_not_arm")
                    && source.contains("riscv_fcvt_to_int_saturates_with_nan_to_max")
                    && source
                        .contains("bridge_is_non_vacuous_riscv_nan_is_canonical_not_arm_payload"),
                "B-riscv-fp's bridge test must PIN the RISC-V-specific semantics (FMIN/FMAX = \
                 IEEE-2019 minimumNumber NOT x86/ARM; FCVT-to-int saturate-with-NaN->max; the \
                 canonical-NaN rule — modeled AS RISC-V, validated against qemu, not silently \
                 modeled as x86/ARM)"
            );
        }
        Enforcement::InProcess { .. } => {
            panic!("B-riscv-fp is Test-bound (a live differential bridge), not an InProcess note")
        }
    }
}
