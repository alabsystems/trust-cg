// trust-cg-verify/tests/proof_gate_strict.rs - Strict formal-proof gate test (P0)
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// This is the fail-closed AY + Clean gate. The full-database test fails when
// either proof tool is unavailable, when AY finds a counterexample or errors, or if
// any result falls back to statistical evaluation. Timeout/unknown results are
// explicit solver-capacity PENDING entries: they are reported but are neither
// proofs nor soundness failures. Only the narrow audited allowlist below may
// remain pending; a new timeout/unknown fails the full-database floor closed.
//
// The always-on tests assert the gate contract without requiring a solver.
// `representative_arithmetic_is_formally_verified` is a six-obligation smoke.
// `scripts/check_proof_gate.sh` defaults to the full-database zero-soundness /
// no-statistical-fallback floor and prints the verified/pending split.
//
// Run the full database directly (external solver lane):
//   TRUST_CG_RUN_FORMAL_PROOF_TESTS=1 \
//     scripts/trust_cargo.sh test -p trust-cg-verify --test proof_gate_strict \
//       full_database_is_formally_verified -- --test-threads=1
//
// The supported solver route is the external AY subprocess lane. There is no
// native-AY Cargo feature; Clean independently checks promoted certificates.
//
// The solver-gated bodies use an explicit
// `TRUST_CG_RUN_FORMAL_PROOF_TESTS=1` qualification gate, so the plain
// `scripts/trust_cargo.sh test -p trust-cg-verify --tests` lane does not require a solver. The
// default package-lane contract (no solver => fail closed, never a downgrade)
// is asserted by the always-on `gate_fails_closed_*` / `strict_gate_*` tests.
//
// Historical bugs this locks in (all OUTSIDE the per-instruction SMT core, but
// the gate makes the SMT core itself the mandatory floor and removes the
// statistical-downgrade escape hatch that let them ship):
//   - The select_auto_mode() silent downgrade to MockOnly (the P0 gap itself).
//   - #51 / #66 carrier hygiene (SAR/IDIV sign-ext, SHR/unsigned-DIV zero-ext):
//     the division/shift obligations are discharged formally, not sampled.
//   - #68-fneg (select_fneg emitted 0.0-x with no proof): the FP-lowering
//     obligations now MUST be formally Verified, so an unproven encoder change
//     surfaces as a gate failure rather than a statistical near-miss.
//   - #67 overflow / INT_MIN edge cases: a 64-bit edge that 100K random samples
//     can miss is now decided by the solver.
//
// Reference: crates/trust-cg-verify/src/proof_gate.rs,
//            crates/trust-cg-verify/src/proof_database.rs,
//            crates/trust-cg-verify/src/ay_bridge.rs

use trust_cg_verify::ay_bridge::{AYConfig, ay_available, proof_toolchain_unavailable_reason};
use trust_cg_verify::proof_database::{
    GENUINE_IDENTITY_ALLOWLIST, KNOWN_DEGENERATE_PENDING_FIX, ProofDatabase,
};
use trust_cg_verify::proof_gate::{
    FailureClass, GateConfig, GateError, GateReport, native_ay_compiled,
};

/// Run `f` on a 64 MiB stack so `ProofDatabase::new()` does not overflow the
/// default 8 MiB test-thread stack (proof_database.rs #205).
fn on_large_stack<T: Send + 'static>(f: impl FnOnce() -> T + Send + 'static) -> T {
    std::thread::Builder::new()
        .name("universal-gate".to_string())
        .stack_size(64 * 1024 * 1024)
        .spawn(f)
        .expect("spawn large-stack universal-gate thread")
        .join()
        .expect("universal-gate thread panicked")
}

const FORMAL_PROOF_TEST_ENV: &str = "TRUST_CG_RUN_FORMAL_PROOF_TESTS";

/// An AY executable without a capable Clean checker cannot discharge this
/// floor. Report the actual missing component while keeping the gate closed.
#[track_caller]
fn require_formal_proof_toolchain(gate: &GateConfig, floor: &str) {
    assert!(
        gate.solver_available(),
        "AY + Clean proof toolchain unavailable for {floor}: {}",
        proof_toolchain_unavailable_reason()
            .unwrap_or_else(|| "availability changed during the check".to_string()),
    );
}

/// Audited full-database obligations that may remain formally PENDING because
/// their bit-blasts exceed the strict gate's current solver budget. This is an
/// upper bound, not a claim that they must time out: an entry that AY proves is
/// credited as `Verified`, while any pending name outside this list fails the
/// gate. Keep exact registered names so a rename cannot silently inherit debt.
const SOLVER_CAPACITY_PENDING_ALLOWLIST: &[&str] = &[
    "x86_64: Sdiv_I32 -> IDIV r32 (quotient)",
    "x86_64: Sdiv_I64 -> IDIV r64 (quotient)",
    "x86_64: Srem_I32 -> IDIV r32 (remainder)",
    "x86_64: Srem_I64 -> IDIV r64 (remainder)",
    "x86_64: V2I64 even-dword widening Umul -> PMULUDQ xmm,xmm",
];

/// Exact static corpus cardinality after removing duplicate registrations.
/// A change requires auditing both the capacity allowlist and the documented
/// full-gate scope; silently shrinking the database is not a green gate. Audit
/// a change name-by-name: dump `ProofDatabase::new()`'s registered names with
/// the `proof_database_inventory` example (`--format tsv`) at the base and at
/// the new revision, and diff the sorted lists. The per-increase history is archived in
/// `docs/archive/session-reports/2026-09-proof-gate-count-ladders.md`.
///
/// Every named lane below is bound live to the function that produces it, so an
/// unrelated replacement cannot inherit its cardinality credit:
///
/// | lane | producer | pinned by |
/// |---|---|---|
/// | AArch64 ELF relocations | `aarch64_elf_reloc_proofs` | `aarch64_elf_relocation_corpus_addition_is_exact_live_and_nondegenerate` |
/// | ADRP + LDR/STR `:lo12:` | `aarch64_elf_reloc_proofs::aarch64_elf_ldst_lo12_proofs` | `aarch64_elf_ldst_lo12_corpus_addition_is_exact_live_and_nondegenerate` |
/// | standalone ROR-immediate and TST NZCV | `lowering_proof::all_ror_immediate_proofs`, `cmp_combine_proofs::proof_tst_nzcv_effect` | `aarch64_standalone_rotate_and_tst_corpus_addition_is_exact_live_and_nondegenerate` |
/// | source-bound leaf frame | `source_bound_frame::frame_obligation` | `source_bound_leaf_frame_corpus_addition_is_exact_live_and_nondegenerate` |
/// | decoded-word values | `aarch64_value_decode_proofs::all_a64_value_decode_proofs` | `aarch64_value_decode_corpus_addition_is_exact_live_and_nondegenerate` |
/// | NZCV producer/consumer | `aarch64_flag_consumer_proofs::all_flag_consumer_proofs` | `aarch64_flag_consumer_corpus_addition_is_exact_live_and_nondegenerate` |
/// | i128 checked multiply | `checked_mul_i128_proofs::all_checked_mul_i128_proofs` | `checked_mul_i128_corpus_addition_is_exact_live_and_nondegenerate` |
/// | atomic perimeter | `atomic_proofs::all_atomic_proofs` | `atomic_perimeter_corpus_addition_is_exact_live_and_nondegenerate` |
/// | CMP -> CSEL select | `aarch64_select_proofs::all_select_cmp_csel_proofs` | `select_cmp_csel_corpus_addition_is_exact_live_and_nondegenerate` |
/// | decoded-word CSET | `aarch64_value_decode_proofs::all_a64_cset_value_decode_proofs` | `cset_value_decode_corpus_addition_is_exact_live_and_nondegenerate` |
///
/// Other families counted here without a dedicated lane test, and why each is
/// non-degenerate (its two halves are computed differently):
///
///   * wasm narrow-width rows (`wasm_value_domain::narrow_width_proofs`, via
///     `register_wasm_proofs` into `ProofCategory::WasmLowering`): four narrow
///     domains x (6 binary ops + 1 shift + 1 renormalization) = 32. SOURCE
///     computes at the narrow width and lifts into the `i32` carrier, MACHINE
///     computes at `i32` and re-normalizes. The wasm per-opcode obligations
///     (sub-word / FP memory, sign extension) are NOT counted here: they are
///     reconstruction-credited through `GateArch::WasmValueDomain`, the rule
///     that keeps every backend's reconstructions out of the static database.
///   * the four UGE rows (`Icmp_UGE_I32/I64`, `CondBr_UGE_I32/I64`), genuine
///     theorems with the adder carry-out C flag (`nzcv.rs`).
///   * the four checked-i128 carry-chain overflow-bit rows
///     (`Checked{S,U}{add,sub}_I128 overflow bit`): the final NZCV of
///     `ADDS;ADCS`/`SUBS;SBCS` rebuilt from limb arithmetic vs the native
///     128-bit overflow definition.
///   * x86-64 const-multiply strength reduction
///     (`x86_64: ConstMul_Shift_{Add,Sub}_{I32,I64}`): SOURCE is the multiply,
///     MACHINE the shift/add or shift/sub pair.
///   * the AArch64 narrow-return demanded-bits row
///     (`I8_RETURN_DEMANDED_BITS_PROOF_ID` in
///     `trust-cg-opt/src/i8_return_demanded_bits.rs`):
///     `low8(UXTB(ANDW(Xn,#255))) == low8(Xn)`.
///
/// The whole-instruction packed-NZCV pair (`proof_tst_packed_nzcv` at both
/// widths) is registered separately from the standalone TST lane; do not let
/// it absorb that lane's credit.
const EXPECTED_STATIC_PROOF_OBLIGATION_COUNT: usize = 2_507;

/// Size of the decoded-word `CSET` lane: exactly
/// `aarch64_value_decode_proofs::all_a64_cset_value_decode_proofs()`, 14
/// condition codes x destination width {Wd, Xd}. `AL`/`NV` are absent because
/// the alias cannot carry them (neither complements the other, and the encoder
/// refuses a condition above 13). Registered in `ProofCategory::Comparison`
/// after the Icmp/CondBr families, the `Select_*` CSEL family AND the NZCV
/// producer/consumer family, so first-match query resolution is unchanged
/// (`cset_family_registration_does_not_shadow_the_comparison_families`). Each
/// row's machine side is the Arm ARM effect of the independently decoded
/// conditional-select word (`aarch64_csel_semantics`, whose decoder knows
/// nothing of the CSET alias); its intent side takes its predicate from
/// `nzcv::eval_condition`'s per-mnemonic table. The alias's inversion, its two
/// zero registers and its increment are all load-bearing, and every row is
/// decided exhaustively over all sixteen packed NZCV states.
const CSET_VALUE_DECODE_CORPUS_ADDITION_LEN: usize = 28;

/// Size of the i128 checked-multiply idiom lane: exactly
/// `checked_mul_i128_proofs::all_checked_mul_i128_proofs()`, registered in
/// `Arithmetic`. The `Imul I128` low-product row states the 128-bit `bvmul`
/// against the `MUL; UMULH; MADD; MADD` limb chain; the five overflow-flag rows
/// state trust-ir's checked-multiply semantics (the exact 256-bit product does
/// not fit) against the expansions the adapter emits: the guarded
/// `__udivti3`/`__divti3` division identity (AArch64), the division-free limb
/// check and, for a constant operand, the limit compare (x86-64, OD-224). Like the 64-bit checked-multiply rows, their
/// terms are beyond the strict gate's solver budget.
const CHECKED_MUL_I128_CORPUS_ADDITION_LEN: usize = 6;

/// Size of the decoded-word value-obligation lane: exactly
/// `aarch64_value_decode_proofs::all_a64_value_decode_proofs()`, one row per
/// emitted MovR/FMOV/SMULL/BFM/RBIT/`ADD LSL #12`/MRS form, the half-precision
/// FCVT forms, the typed post-allocation copies `MOVWrr`/`MOVXrr`, the
/// zero-register sources, the FEAT_FP16 `FMOV Wd, Hn` / `FMOV Hd, Wn`, and the
/// `MOV Vd.16B, Vn.16B` vector register copy. Each machine side is the Arm ARM
/// semantics of an independently decoded captured encoder word (for FCVT,
/// against an independently written IEEE 754 convertFormat intent), so the
/// halves are computed differently.
const AARCH64_VALUE_DECODE_CORPUS_ADDITION_LEN: usize = 30;

/// Size of the NZCV producer/consumer lane: exactly
/// `aarch64_flag_consumer_proofs::all_flag_consumer_proofs()`, registered in
/// `ProofCategory::Comparison` after the Icmp/CondBr and `Select_*` families
/// (only the decoded-word CSET family is registered after it): 2 FCMP
/// packed-NZCV rows, 28 FCMP -> CSET rows and 384 CSEL/CSINC/CSNEG-over-producer
/// rows. Each machine side executes an independently decoded captured word
/// over the producer's NZCV model; each source side is a TrustIR
/// predicate/select.
const AARCH64_FLAG_CONSUMER_CORPUS_ADDITION_LEN: usize = 414;
/// How many of the 414 each per-form producer family mints: the packed-NZCV
/// FCMP obligations, the FCMP -> CSET family, and the CSEL/CSINC/CSNEG select
/// forms. Measured on this tree; see `aarch64_flag_consumer_corpus_addition_*`.
const AARCH64_FLAG_CONSUMER_FAMILY_COUNTS: (usize, usize, usize) = (2, 28, 384);

/// Size of the conditional-select lane: exactly
/// `aarch64_select_proofs::all_select_cmp_csel_proofs()`, 10 conditions x
/// cmp{32,64} x sel{32,64} (the comparison and select widths are independent).
/// Registered in `ProofCategory::Comparison` after the Icmp/CondBr families and
/// before the NZCV producer/consumer family, whose `"a64 nzcv ..."` queries no
/// `Select_*` name contains, so first-match query resolution is unchanged. Each
/// row's machine side is the Arm ARM semantics of an independently decoded CSEL
/// word, so a wrong condition or a swapped arm refutes.
const SELECT_CMP_CSEL_CORPUS_ADDITION_LEN: usize = 40;

/// The four atomic-perimeter rows: exactly the rows `atomic_proofs`'s own count
/// pin names, bound live below. All four register once, in
/// `ProofCategory::AtomicOperations`, and are structurally non-degenerate.
const ATOMIC_PERIMETER_CORPUS_ADDITION: &[&str] = &[
    "SWP_I64: mem[addr] = operand",
    "AtomicLoad_I128: single-copy (one paired access)",
    "DMB_ISH: orders prior load before subsequent load",
    "DMB_ISHLD: orders prior load before subsequent load",
];

const AARCH64_ELF_LDST_LO12_CORPUS_ADDITION: &[&str] = &[
    "ELF AArch64: R_AARCH64_LDST8_ABS_LO12_NC ADRP+LDR/STR == S+A (byte access)",
    "ELF AArch64: R_AARCH64_LDST16_ABS_LO12_NC ADRP+LDR/STR == S+A (2-aligned access)",
    "ELF AArch64: R_AARCH64_LDST32_ABS_LO12_NC ADRP+LDR/STR == S+A (4-aligned access)",
    "ELF AArch64: R_AARCH64_LDST64_ABS_LO12_NC ADRP+LDR/STR == S+A (8-aligned access)",
    "ELF AArch64: R_AARCH64_LDST128_ABS_LO12_NC ADRP+LDR/STR == S+A (16-aligned access)",
];

const AARCH64_ELF_RELOCATION_CORPUS_ADDITION: &[&str] = &[
    "ELF AArch64: R_AARCH64_CALL26 BL == S+A (PC-relative call)",
    "ELF AArch64: R_AARCH64_JUMP26 B == S+A (PC-relative tail jump)",
    "ELF AArch64: R_AARCH64_PREL32 word + P == S+A (PC-relative data)",
    "ELF AArch64: R_AARCH64_ABS64 == S + A (abs64 pointer slot)",
    "ELF AArch64: R_AARCH64_ADR_PREL_PG_HI21 ADRP == page(S+A)",
    "ELF AArch64: R_AARCH64_ADD_ABS_LO12_NC ADRP+ADD == S+A",
    "ELF AArch64: R_AARCH64_ADR_GOT_PAGE ADRP == page(G+A) (GOT slot page)",
    "ELF AArch64: R_AARCH64_LD64_GOT_LO12_NC ADRP+LDR == G+A (GOT slot address)",
];

/// The ten standalone ROR-immediate rows: exactly
/// `lowering_proof::all_ror_immediate_proofs()` (registered through
/// `all_bitwise_shift_proofs` into `ProofCategory::Arithmetic`), bound live
/// below. SOURCE is the frontend rotate blend, MACHINE the ROR shifted operand;
/// the halves coincide in the opposite OR order, so the rows are
/// non-degenerate.
const ROR_IMMEDIATE_CORPUS_ADDITION: &[&str] = &[
    "RorRI_I32 k=1 -> ROR #1 (32-bit): frontend rotate blend == ROR shifted operand",
    "RorRI_I32 k=7 -> ROR #7 (32-bit): frontend rotate blend == ROR shifted operand",
    "RorRI_I32 k=16 -> ROR #16 (32-bit): frontend rotate blend == ROR shifted operand",
    "RorRI_I32 k=25 -> ROR #25 (32-bit): frontend rotate blend == ROR shifted operand",
    "RorRI_I32 k=31 -> ROR #31 (32-bit): frontend rotate blend == ROR shifted operand",
    "RorRI_I64 k=1 -> ROR #1 (64-bit): frontend rotate blend == ROR shifted operand",
    "RorRI_I64 k=13 -> ROR #13 (64-bit): frontend rotate blend == ROR shifted operand",
    "RorRI_I64 k=32 -> ROR #32 (64-bit): frontend rotate blend == ROR shifted operand",
    "RorRI_I64 k=51 -> ROR #51 (64-bit): frontend rotate blend == ROR shifted operand",
    "RorRI_I64 k=63 -> ROR #63 (64-bit): frontend rotate blend == ROR shifted operand",
];

/// The twenty standalone per-condition TST NZCV rows: exactly
/// `cmp_combine_proofs::proof_tst_nzcv_effect(64)` followed by `(32)`
/// (registered through `all_cmp_combine_proofs_with_variants` into
/// `ProofCategory::CmpCombine`), bound live below. They use the disjointness
/// characterization rather than a degenerate direct-Z formulation. HS/LO are
/// deliberately absent — `eval_condition`
/// reduces both of their sides to a bare constant, which STRICT #61 credits
/// zero — so the C-clear fact is carried by the composite readers HI and LS.
const TST_NZCV_CONSUMER_CORPUS_ADDITION: &[&str] = &[
    "TST w64: EQ ≡ (Rn & Rm) == 0",
    "TST w64: NE ≡ (Rn & Rm) != 0",
    "TST w64: MI ≡ (Rn & Rm) <s 0",
    "TST w64: PL ≡ (Rn & Rm) >=s 0",
    "TST w64: GE ≡ (Rn & Rm) >=s 0 (V is cleared)",
    "TST w64: LT ≡ (Rn & Rm) <s 0 (V is cleared)",
    "TST w64: GT ≡ (Rn & Rm) >s 0 (V is cleared)",
    "TST w64: LE ≡ (Rn & Rm) <=s 0 (V is cleared)",
    "TST w64: HI is always FALSE (C is cleared)",
    "TST w64: LS is always TRUE (C is cleared)",
    "TST w32: EQ ≡ (Rn & Rm) == 0",
    "TST w32: NE ≡ (Rn & Rm) != 0",
    "TST w32: MI ≡ (Rn & Rm) <s 0",
    "TST w32: PL ≡ (Rn & Rm) >=s 0",
    "TST w32: GE ≡ (Rn & Rm) >=s 0 (V is cleared)",
    "TST w32: LT ≡ (Rn & Rm) <s 0 (V is cleared)",
    "TST w32: GT ≡ (Rn & Rm) >s 0 (V is cleared)",
    "TST w32: LE ≡ (Rn & Rm) <=s 0 (V is cleared)",
    "TST w32: HI is always FALSE (C is cleared)",
    "TST w32: LS is always TRUE (C is cleared)",
];

#[test]
fn solver_capacity_pending_allowlist_is_narrow_unique_and_live() {
    on_large_stack(|| {
        use std::collections::HashSet;

        assert_eq!(
            SOLVER_CAPACITY_PENDING_ALLOWLIST.len(),
            5,
            "capacity debt may change only through an explicit audit"
        );
        let unique: HashSet<&str> = SOLVER_CAPACITY_PENDING_ALLOWLIST.iter().copied().collect();
        assert_eq!(
            unique.len(),
            SOLVER_CAPACITY_PENDING_ALLOWLIST.len(),
            "capacity-pending allowlist contains duplicate names"
        );

        let db = ProofDatabase::new();
        assert_eq!(
            db.len(),
            EXPECTED_STATIC_PROOF_OBLIGATION_COUNT,
            "static proof corpus changed; audit the strict-gate scope and capacity allowlist"
        );
        assert_eq!(
            db.len(),
            EXPECTED_STATIC_PROOF_OBLIGATION_COUNT,
            "static corpus cardinality changed; audit its registrations and floor"
        );
        println!("static proof corpus: {} unique obligations", db.len());
        let registered: HashSet<&str> = db
            .all()
            .iter()
            .map(|proof| proof.obligation.name.as_str())
            .collect();
        assert_eq!(
            registered.len(),
            db.len(),
            "registered static proof names must be globally unique because capacity authority is name-bound"
        );
        let ambiguous_or_dead: Vec<(&str, usize)> = SOLVER_CAPACITY_PENDING_ALLOWLIST
            .iter()
            .copied()
            .map(|name| {
                let registrations = db
                    .all()
                    .iter()
                    .filter(|proof| proof.obligation.name == name)
                    .count();
                (name, registrations)
            })
            .filter(|(_, registrations)| *registrations != 1)
            .collect();
        assert!(
            ambiguous_or_dead.is_empty(),
            "each name-bound capacity exception must identify exactly one registered proof: \
             {ambiguous_or_dead:?}"
        );
    });
}

#[test]
fn aarch64_elf_relocation_corpus_addition_is_exact_live_and_nondegenerate() {
    on_large_stack(|| {
        use std::collections::HashSet;
        use trust_cg_verify::aarch64_elf_reloc_proofs::aarch64_elf_relocation_proofs;

        let expected: HashSet<String> = AARCH64_ELF_RELOCATION_CORPUS_ADDITION
            .iter()
            .map(|name| (*name).to_string())
            .collect();
        assert_eq!(
            expected.len(),
            AARCH64_ELF_RELOCATION_CORPUS_ADDITION.len(),
            "AArch64 ELF relocation corpus ratchet contains duplicate names"
        );

        let lane = aarch64_elf_relocation_proofs();
        let lane_names: HashSet<String> = lane.iter().map(|proof| proof.name.clone()).collect();
        assert_eq!(
            lane_names, expected,
            "the eight-obligation corpus increase must remain exactly the audited AArch64 ELF relocation lane"
        );
        assert!(
            lane.iter().all(|proof| proof.is_genuinely_proven()),
            "every newly credited AArch64 ELF relocation obligation must be structurally non-degenerate"
        );

        let db = ProofDatabase::new();
        for name in AARCH64_ELF_RELOCATION_CORPUS_ADDITION {
            let registrations: Vec<_> = db
                .all()
                .iter()
                .filter(|proof| proof.obligation.name == *name)
                .collect();
            assert_eq!(
                registrations.len(),
                1,
                "new corpus row {name:?} must identify exactly one live registration"
            );
            assert!(
                registrations[0].obligation.is_genuinely_proven(),
                "registered corpus row {name:?} must remain structurally non-degenerate"
            );
            assert!(
                !SOLVER_CAPACITY_PENDING_ALLOWLIST.contains(name),
                "new corpus row {name:?} may not silently inherit solver-capacity debt"
            );
        }
    });
}

/// The five LDST lo12 rows, bound LIVE to the
/// lane that produces them.
#[test]
fn aarch64_elf_ldst_lo12_corpus_addition_is_exact_live_and_nondegenerate() {
    on_large_stack(|| {
        use std::collections::HashSet;
        use trust_cg_verify::aarch64_elf_reloc_proofs::aarch64_elf_ldst_lo12_proofs;
        use trust_cg_verify::proof_database::ProofCategory;

        let lane = aarch64_elf_ldst_lo12_proofs();
        let lane_names: HashSet<&str> = lane.iter().map(|proof| proof.name.as_str()).collect();
        let expected: HashSet<&str> = AARCH64_ELF_LDST_LO12_CORPUS_ADDITION
            .iter()
            .copied()
            .collect();
        assert_eq!(expected.len(), AARCH64_ELF_LDST_LO12_CORPUS_ADDITION.len());
        assert_eq!(
            lane_names, expected,
            "the five-obligation LDST lo12 increase must remain exactly the audited lane"
        );
        let db = ProofDatabase::new();
        for name in AARCH64_ELF_LDST_LO12_CORPUS_ADDITION {
            let registrations: Vec<_> = db
                .all()
                .iter()
                .filter(|proof| proof.obligation.name == *name)
                .collect();
            assert_eq!(
                registrations.len(),
                1,
                "corpus row {name:?} must identify exactly one live registration"
            );
            assert_eq!(registrations[0].category, ProofCategory::MachOEmission);
            assert!(
                registrations[0].obligation.is_genuinely_proven(),
                "registered corpus row {name:?} must remain structurally non-degenerate"
            );
            assert!(
                !SOLVER_CAPACITY_PENDING_ALLOWLIST.contains(name),
                "new corpus row {name:?} may not silently inherit solver-capacity debt"
            );
        }
    });
}

/// The thirty decoded-word value rows, bound LIVE to
/// `all_a64_value_decode_proofs`: each must be registered exactly once, in the
/// category its form files it under, structurally non-degenerate and off the
/// capacity allowlist, so an unrelated replacement cannot inherit the
/// cardinality credit.
///
/// MEASURED 2026-09-25 at `08860ff7f`: that paragraph overstated what the body
/// below enforced. A lane-length pin plus per-row uniqueness, category,
/// non-degeneracy and allowlist checks are satisfied by ANY seventeen
/// uniquely-named non-degenerate rows the lane chooses to emit, because the
/// audited set was READ OFF the producer instead of being stated. Deleting the
/// audited `SMULL` decoded-word row and filling its slot with the body of the
/// pre-existing Arithmetic lemma `Imul_I128 hi -> MUL+UMULH+MADD+MADD`
/// (registered since 2026-08-11, a month before this lane landed) under a fresh
/// name left the whole 32-test gate GREEN with the corpus total still at 2,045 —
/// exactly the laundering this ratchet exists to refuse. A NAME-IDENTICAL
/// substitution of a pre-existing row does fail, but only because it registers
/// twice; the fresh-name variant slipped through.
///
/// The `AUDITED` table below closes that: each row is now stated by name and
/// bound to the INDIVIDUAL per-form producer (`a64_value_form_obligation_for`,
/// added by `5398c274f` for the seventeen and extended form by form for the
/// FCVT, typed-copy, zero-source, W<->H and ORR (vector) rows), so a
/// substitution fails on the PRODUCER rather than on the category. Nothing
/// here was weakened or removed.
#[test]
fn aarch64_value_decode_corpus_addition_is_exact_live_and_nondegenerate() {
    on_large_stack(|| {
        use std::collections::HashSet;
        use trust_cg_verify::aarch64_value_decode_proofs::{
            A64ValueForm, a64_value_form_obligation_for, all_a64_value_decode_proofs,
        };
        use trust_cg_verify::proof_database::ProofCategory;

        let lane = all_a64_value_decode_proofs();
        assert_eq!(
            lane.len(),
            AARCH64_VALUE_DECODE_CORPUS_ADDITION_LEN,
            "the decoded-word value lane must remain exactly the audited thirty forms"
        );
        let lane_names: HashSet<&str> = lane
            .iter()
            .map(|(_, obligation)| obligation.name.as_str())
            .collect();
        assert_eq!(lane_names.len(), lane.len(), "lane names must be unique");

        // PRODUCER BINDING. Every assertion above reads its audited set OFF the
        // producer, so it credits whatever the lane emits. State the thirty
        // instead, in `A64ValueForm::ALL` order, and bind each to the individual
        // per-form producer that `5398c274f` added: the lane's Nth row must be
        // exactly what `a64_value_form_obligation_for(form, <that form's own
        // captured canonical encoder word>, None)` mints, under the audited name
        // and in the audited category.
        const AUDITED: [(A64ValueForm, ProofCategory, &str);
            AARCH64_VALUE_DECODE_CORPUS_ADDITION_LEN] = [
            (
                A64ValueForm::MovW,
                ProofCategory::BitwiseShift,
                "A64 decoded MOV Wd, Wn (ORR Wd, WZR, Wm word) == Wn zero-extended: the W \
                 write clears Xd[63:32]",
            ),
            (
                A64ValueForm::MovX,
                ProofCategory::BitwiseShift,
                "A64 decoded MOV Xd, Xn (ORR Xd, XZR, Xm word) == Xn",
            ),
            (
                A64ValueForm::MovXFromSp,
                ProofCategory::BitwiseShift,
                "A64 decoded MOV Xd, SP (ADD Xd, SP, #0 word) == SP",
            ),
            (
                A64ValueForm::MovWFromZr,
                ProofCategory::BitwiseShift,
                "A64 decoded MOV Wd, WZR (ORR Wd, WZR, WZR word) == 0, the W write clears \
                 Xd[63:32]",
            ),
            (
                A64ValueForm::MovXFromZr,
                ProofCategory::BitwiseShift,
                "A64 decoded MOV Xd, XZR (ORR Xd, XZR, XZR word) == 0",
            ),
            (
                A64ValueForm::MovWrr,
                ProofCategory::BitwiseShift,
                "A64 decoded MOVWrr Wd, Wn (ORR Wd, WZR, Wm word; the opcode fixes the W \
                 width) == Wn zero-extended: the W write clears Xd[63:32]",
            ),
            (
                A64ValueForm::MovWrrFromZr,
                ProofCategory::BitwiseShift,
                "A64 decoded MOVWrr Wd, ZR (ORR Wd, WZR, WZR word; the opcode fixes the W \
                 width) == 0, the W write clears Xd[63:32]",
            ),
            (
                A64ValueForm::MovXrr,
                ProofCategory::BitwiseShift,
                "A64 decoded MOVXrr Xd, Xn (ORR Xd, XZR, Xm word; the opcode fixes the X \
                 width) == Xn",
            ),
            (
                A64ValueForm::MovXrrFromZr,
                ProofCategory::BitwiseShift,
                "A64 decoded MOVXrr Xd, ZR (ORR Xd, XZR, XZR word; the opcode fixes the X \
                 width) == 0",
            ),
            (
                A64ValueForm::FmovS,
                ProofCategory::FloatingPoint,
                "A64 decoded FMOV Sd, Sn word == Sn bits, Vd[127:32] zero",
            ),
            (
                A64ValueForm::FmovD,
                ProofCategory::FloatingPoint,
                "A64 decoded FMOV Dd, Dn word == Dn bits, Vd[127:64] zero",
            ),
            (
                A64ValueForm::FmovWFromS,
                ProofCategory::FpConversion,
                "A64 decoded FMOV Wd, Sn word == Sn bits, Xd[63:32] zero",
            ),
            (
                A64ValueForm::FmovXFromD,
                ProofCategory::FpConversion,
                "A64 decoded FMOV Xd, Dn word == Dn bits",
            ),
            (
                A64ValueForm::FmovWFromH,
                ProofCategory::FpConversion,
                "A64 decoded FMOV Wd, Hn word (FEAT_FP16) == Hn bits, Xd[63:16] zero",
            ),
            (
                A64ValueForm::FmovSFromW,
                ProofCategory::FpConversion,
                "A64 decoded FMOV Sd, Wn word == Wn bits, Vd[127:32] zero",
            ),
            (
                A64ValueForm::FmovDFromX,
                ProofCategory::FpConversion,
                "A64 decoded FMOV Dd, Xn word == Xn bits, Vd[127:64] zero",
            ),
            (
                A64ValueForm::FmovHFromW,
                ProofCategory::FpConversion,
                "A64 decoded FMOV Hd, Wn word (FEAT_FP16) == Wn[15:0], Vd[127:16] zero",
            ),
            (
                A64ValueForm::MovV16B,
                ProofCategory::FloatingPoint,
                "A64 decoded MOV Vd.16B, Vn.16B (ORR Vd.16B, Vn.16B, Vn.16B word) == Vn, \
                 all 128 bits",
            ),
            (
                A64ValueForm::Smull,
                ProofCategory::Arithmetic,
                "A64 decoded SMULL Xd, Wn, Wm (SMADDL Xd, Wn, Wm, XZR word) == \
                 sext64(Wn) * sext64(Wm)",
            ),
            (
                A64ValueForm::BfmInsertW,
                ProofCategory::BitwiseShift,
                "A64 decoded BFM Wd, Wn insert (immr = (32 - lsb) mod 32, imms = width - 1) == \
                 InsertBits(lsb, width), Xd[63:32] zero",
            ),
            (
                A64ValueForm::BfmInsertX,
                ProofCategory::BitwiseShift,
                "A64 decoded BFM Xd, Xn insert (immr = (64 - lsb) mod 64, imms = width - 1) == \
                 InsertBits(lsb, width)",
            ),
            (
                A64ValueForm::RbitW,
                ProofCategory::BitwiseShift,
                "A64 decoded RBIT Wd, Wn word == SWAR bit reversal, Xd[63:32] zero",
            ),
            (
                A64ValueForm::RbitX,
                ProofCategory::BitwiseShift,
                "A64 decoded RBIT Xd, Xn word == SWAR bit reversal",
            ),
            (
                A64ValueForm::AddLsl12W,
                ProofCategory::Arithmetic,
                "A64 decoded ADD Wd, Wn, #imm12, LSL #12 word == Wn + imm12 * 4096, \
                 Xd[63:32] zero",
            ),
            (
                A64ValueForm::AddLsl12X,
                ProofCategory::Arithmetic,
                "A64 decoded ADD Xd, Xn, #imm12, LSL #12 word == Xn + imm12 * 4096",
            ),
            (
                A64ValueForm::MrsTpidrEl0,
                ProofCategory::AddressMode,
                "A64 decoded MRS Xt, TPIDR_EL0 word == the TPIDR_EL0 system register",
            ),
            (
                A64ValueForm::FcvtSFromH,
                ProofCategory::FpConversion,
                "A64 decoded FCVT Sd, Hn word (Arm FPConvert, default FPCR) == IEEE 754 \
                 binary16 -> binary32 convertFormat, exact, NaN quieted with its payload, \
                 Vd[127:32] zero",
            ),
            (
                A64ValueForm::FcvtDFromH,
                ProofCategory::FpConversion,
                "A64 decoded FCVT Dd, Hn word (Arm FPConvert, default FPCR) == IEEE 754 \
                 binary16 -> binary64 convertFormat, exact, NaN quieted with its payload, \
                 Vd[127:64] zero",
            ),
            (
                A64ValueForm::FcvtHFromS,
                ProofCategory::FpConversion,
                "A64 decoded FCVT Hd, Sn word (Arm FPConvert, default FPCR) == IEEE 754 \
                 binary32 -> binary16 convertFormat, roundTiesToEven, overflow to infinity, \
                 NaN quieted with its high payload, Vd[127:16] zero",
            ),
            (
                A64ValueForm::FcvtHFromD,
                ProofCategory::FpConversion,
                "A64 decoded FCVT Hd, Dn word (Arm FPConvert, default FPCR) == IEEE 754 \
                 binary64 -> binary16 convertFormat, roundTiesToEven, overflow to infinity, \
                 NaN quieted with its high payload, Vd[127:16] zero",
            ),
        ];

        for (index, ((lane_category, lane_obligation), (form, audited_category, audited_name))) in
            lane.iter().zip(AUDITED.iter()).enumerate()
        {
            let canonical = form.canonical().unwrap_or_else(|| {
                panic!("audited form {form:?} (row {index}) has no captured encoder word")
            });
            let produced = a64_value_form_obligation_for(*form, canonical.word, None)
                .unwrap_or_else(|error| {
                    panic!(
                        "audited form {form:?} (row {index}) no longer mints its \
                         decoded-word obligation: {error:?}"
                    )
                });
            assert_eq!(
                produced.name.as_str(),
                *audited_name,
                "audited row {index} ({form:?}) must keep the obligation name its \
                 originating commit registered"
            );
            assert_eq!(
                lane_obligation, &produced,
                "audited row {audited_name:?} must be EXACTLY what its own per-form \
                 producer mints from that form's captured encoder word — a substituted \
                 obligation may not inherit its share of the lane's cardinality credit"
            );
            assert_eq!(
                lane_category, audited_category,
                "audited row {audited_name:?} must stay in its audited category"
            );
        }

        let db = ProofDatabase::new();
        for (category, obligation) in &lane {
            let name = obligation.name.as_str();
            let registrations: Vec<_> = db
                .all()
                .iter()
                .filter(|proof| proof.obligation.name == name)
                .collect();
            assert_eq!(
                registrations.len(),
                1,
                "corpus row {name:?} must identify exactly one live registration"
            );
            assert_eq!(registrations[0].category, *category, "{name:?}");
            assert!(
                registrations[0].obligation.is_genuinely_proven(),
                "registered corpus row {name:?} must remain structurally non-degenerate"
            );
            assert!(
                !SOLVER_CAPACITY_PENDING_ALLOWLIST.contains(&name),
                "new corpus row {name:?} may not silently inherit solver-capacity debt"
            );
        }
    });
}

#[test]
fn checked_mul_i128_corpus_addition_is_exact_live_and_nondegenerate() {
    on_large_stack(|| {
        use std::collections::HashSet;
        use trust_cg_verify::checked_mul_i128_proofs::{
            CheckedMulI128Form, all_checked_mul_i128_proofs,
            proof_checked_smul_i128_limb_check_flag, proof_checked_smul_i128_overflow_flag,
            proof_checked_umul_i128_const_limit_flag, proof_checked_umul_i128_limb_check_flag,
            proof_checked_umul_i128_overflow_flag, proof_imul_i128_low_product_chain,
        };
        use trust_cg_verify::proof_database::ProofCategory;

        let lane = all_checked_mul_i128_proofs();
        assert_eq!(
            lane.len(),
            CHECKED_MUL_I128_CORPUS_ADDITION_LEN,
            "the i128 checked-multiply idiom lane must remain exactly the audited six rows"
        );
        let lane_names: HashSet<&str> = lane.iter().map(|o| o.name.as_str()).collect();
        assert_eq!(lane_names.len(), lane.len(), "lane names must be unique");
        // PRODUCER BINDING (the `494a96e76` / `fb76822f0` / `fba592707` rule). The
        // assertions below used to read every name OFF the producer and check only
        // that SOME registration carries it, so any obligation registered under an
        // audited name in `Arithmetic` inherited the credit. State the three names,
        // and require each row — and its one live registration — to be exactly what
        // that form's OWN producer mints, compared as a whole `ProofObligation`.
        const AUDITED: [(CheckedMulI128Form, &str); CHECKED_MUL_I128_CORPUS_ADDITION_LEN] = [
            (
                CheckedMulI128Form::LowProductChain,
                "Imul_I128 low-product chain -> MUL+UMULH+MADD+MADD (128-bit product vs limb chain)",
            ),
            (
                CheckedMulI128Form::UnsignedFlag,
                "CheckedUmul_I128 overflow flag -> guarded __udivti3 division identity (exact \
                 256-bit product high half)",
            ),
            (
                CheckedMulI128Form::SignedFlag,
                "CheckedSmul_I128 overflow flag -> guarded __divti3 division identity (exact \
                 256-bit signed product)",
            ),
            (
                CheckedMulI128Form::UnsignedFlagLimbCheck,
                "CheckedUmul_I128 overflow flag -> division-free limb check (x86-64: two I64 \
                 CheckedUmul + carry + both-high test; exact 256-bit product high half)",
            ),
            (
                CheckedMulI128Form::SignedFlagLimbCheck,
                "CheckedSmul_I128 overflow flag -> division-free limb check on the magnitudes \
                 (x86-64: unsigned core + sign check; exact 256-bit signed product)",
            ),
            (
                CheckedMulI128Form::UnsignedFlagConstLimit,
                "CheckedUmul_I128 overflow flag -> constant-operand limit compare (x86-64: the \
                 other operand >u (2^128 - 1) / C; exact 256-bit product high half)",
            ),
        ];
        assert_eq!(
            CheckedMulI128Form::ALL.to_vec(),
            AUDITED.iter().map(|(form, _)| *form).collect::<Vec<_>>(),
            "the audited forms are CheckedMulI128Form::ALL, in registration order"
        );
        let db = ProofDatabase::new();
        for ((form, obligation), (audited_form, audited_name)) in CheckedMulI128Form::ALL
            .iter()
            .zip(&lane)
            .zip(AUDITED.iter())
        {
            assert_eq!(form, audited_form);
            let name = obligation.name.as_str();
            assert_eq!(
                name, *audited_name,
                "{form:?}: the row is not the audited one"
            );
            let produced = match form {
                CheckedMulI128Form::LowProductChain => proof_imul_i128_low_product_chain(),
                CheckedMulI128Form::UnsignedFlag => proof_checked_umul_i128_overflow_flag(),
                CheckedMulI128Form::SignedFlag => proof_checked_smul_i128_overflow_flag(),
                CheckedMulI128Form::UnsignedFlagLimbCheck => {
                    proof_checked_umul_i128_limb_check_flag()
                }
                CheckedMulI128Form::SignedFlagLimbCheck => {
                    proof_checked_smul_i128_limb_check_flag()
                }
                CheckedMulI128Form::UnsignedFlagConstLimit => {
                    proof_checked_umul_i128_const_limit_flag()
                }
            };
            assert_eq!(
                obligation, &produced,
                "{form:?}: the lane row is not what the form's own producer mints"
            );
            let registrations: Vec<_> = db
                .all()
                .iter()
                .filter(|proof| proof.obligation.name == name)
                .collect();
            assert_eq!(
                registrations.len(),
                1,
                "corpus row {name:?} must identify exactly one live registration"
            );
            assert_eq!(
                registrations[0].category,
                ProofCategory::Arithmetic,
                "{name:?}"
            );
            assert_eq!(
                &registrations[0].obligation, &produced,
                "{name:?}: the live registration is not the producer's obligation"
            );
            assert!(
                registrations[0].obligation.is_genuinely_proven(),
                "registered corpus row {name:?} must remain structurally non-degenerate"
            );
            assert!(
                !SOLVER_CAPACITY_PENDING_ALLOWLIST.contains(&name),
                "new corpus row {name:?} may not silently inherit solver-capacity debt"
            );
            // The gate's query for this form resolves to THIS row and no other
            // Arithmetic row, in registration order.
            let hits: Vec<_> = db
                .by_category(ProofCategory::Arithmetic)
                .into_iter()
                .filter(|p| p.obligation.name.to_lowercase().contains(form.query()))
                .collect();
            assert_eq!(
                hits.len(),
                1,
                "{form:?}: query {:?} must be unique",
                form.query()
            );
            assert_eq!(hits[0].obligation.name, name);
        }
    });
}

#[test]
fn aarch64_flag_consumer_corpus_addition_is_exact_live_and_nondegenerate() {
    on_large_stack(|| {
        use std::collections::HashSet;
        use trust_cg_verify::aarch64_flag_consumer_proofs::all_flag_consumer_proofs;
        use trust_cg_verify::proof_database::ProofCategory;

        let lane = all_flag_consumer_proofs();
        assert_eq!(
            lane.len(),
            AARCH64_FLAG_CONSUMER_CORPUS_ADDITION_LEN,
            "the NZCV producer/consumer lane must remain exactly the audited 414 forms"
        );
        let lane_names: HashSet<&str> = lane
            .iter()
            .map(|(_, obligation)| obligation.name.as_str())
            .collect();
        assert_eq!(lane_names.len(), lane.len(), "lane names must be unique");

        // PRODUCER BINDING (the `494a96e76` / `fb76822f0` / `fba592707` rule).
        // Everything below reads the audited set OFF `all_flag_consumer_proofs`,
        // which drops any form whose producer refuses (`if let Ok(..)`) — so a
        // form could fall out and another take its place with the count intact.
        // Rebuild the lane from the INDIVIDUAL per-form producers, pin how many
        // each family mints, and require the lane to be exactly that sequence.
        {
            use trust_cg_verify::aarch64_flag_consumer_proofs::{
                SelectForm, fcmp_cset_obligation, fcmp_packed_obligation, select_obligation,
            };
            let mut expected = Vec::new();
            let (mut packed, mut cset, mut select) = (0usize, 0usize, 0usize);
            for width in [32, 64] {
                if let Ok(ob) = fcmp_packed_obligation(width) {
                    expected.push(ob);
                    packed += 1;
                }
            }
            for width in [32, 64] {
                for cc in 0..14u8 {
                    if let Ok(ob) = fcmp_cset_obligation(width, cc) {
                        expected.push(ob);
                        cset += 1;
                    }
                }
            }
            for form in SelectForm::all() {
                if let Ok(ob) = select_obligation(form) {
                    expected.push(ob);
                    select += 1;
                }
            }
            assert_eq!(
                (packed, cset, select),
                AARCH64_FLAG_CONSUMER_FAMILY_COUNTS,
                "(packed NZCV, FCMP->CSET, select) forms minted by the per-form producers \
                 moved: a form that starts refusing must not be replaced silently"
            );
            assert_eq!(lane.len(), expected.len());
            for (index, ((_, row), produced)) in lane.iter().zip(&expected).enumerate() {
                assert_eq!(
                    row, produced,
                    "row {index} ({:?}) is not what its per-form producer mints",
                    row.name
                );
            }
        }

        let db = ProofDatabase::new();
        for (category, obligation) in &lane {
            let name = obligation.name.as_str();
            assert_eq!(*category, ProofCategory::Comparison, "{name:?}");
            let registrations: Vec<_> = db
                .all()
                .iter()
                .filter(|proof| proof.obligation.name == name)
                .collect();
            assert_eq!(
                registrations.len(),
                1,
                "corpus row {name:?} must identify exactly one live registration"
            );
            assert_eq!(registrations[0].category, *category, "{name:?}");
            assert_eq!(&registrations[0].obligation, obligation, "{name:?}");
            assert!(
                registrations[0].obligation.is_genuinely_proven(),
                "registered corpus row {name:?} must remain structurally non-degenerate"
            );
            assert!(
                !SOLVER_CAPACITY_PENDING_ALLOWLIST.contains(&name),
                "new corpus row {name:?} may not silently inherit solver-capacity debt"
            );
        }
    });
}

/// The twenty-eight decoded-word CSET rows, bound LIVE to
/// the INDIVIDUAL PER-FORM PRODUCER that mints each one.
///
/// A name+category+non-degeneracy pin is NOT sufficient — that is the exact
/// substitution hole `494a96e76`, `fb76822f0` and `fba592707` closed on three
/// other lanes: any unrelated obligation registered under the audited name in
/// the audited category would inherit the cardinality credit. So every audited
/// row must be EXACTLY what `a64_cset_form_obligation_for(form, form.word(),
/// None)` produces for that form's own word, compared as a whole
/// `ProofObligation` (both sides, inputs and preconditions included).
#[test]
fn cset_value_decode_corpus_addition_is_exact_live_and_nondegenerate() {
    on_large_stack(|| {
        use std::collections::HashSet;
        use trust_cg_verify::aarch64_value_decode_proofs::{
            A64_CSET_FORMS, A64CSetForm, a64_cset_form_obligation_for,
            all_a64_cset_value_decode_proofs,
        };
        use trust_cg_verify::proof_database::ProofCategory;
        use trust_cg_verify::verify::VerificationStrength;

        let lane = all_a64_cset_value_decode_proofs();
        assert_eq!(
            lane.len(),
            CSET_VALUE_DECODE_CORPUS_ADDITION_LEN,
            "the decoded-word CSET lane must remain exactly the audited twenty-eight forms"
        );
        let lane_names: HashSet<&str> = lane
            .iter()
            .map(|(_, obligation)| obligation.name.as_str())
            .collect();
        assert_eq!(lane_names.len(), lane.len(), "lane names must be unique");

        // PRODUCER BINDING. `AUDITED` states the twenty-eight rows instead of
        // reading them off the producer, and each is bound to the per-form
        // producer applied to THAT form's own encoder word.
        const AUDITED: [(A64CSetForm, ProofCategory, &str); CSET_VALUE_DECODE_CORPUS_ADDITION_LEN] = [
            (
                A64_CSET_FORMS[0],
                ProofCategory::Comparison,
                "A64 decoded CSET Xd, EQ (CSINC Xd, XZR, XZR, NE word) \
                 == ConditionHolds(EQ) ? 1 : 0",
            ),
            (
                A64_CSET_FORMS[1],
                ProofCategory::Comparison,
                "A64 decoded CSET Xd, NE (CSINC Xd, XZR, XZR, EQ word) \
                 == ConditionHolds(NE) ? 1 : 0",
            ),
            (
                A64_CSET_FORMS[2],
                ProofCategory::Comparison,
                "A64 decoded CSET Xd, HS (CSINC Xd, XZR, XZR, LO word) \
                 == ConditionHolds(HS) ? 1 : 0",
            ),
            (
                A64_CSET_FORMS[3],
                ProofCategory::Comparison,
                "A64 decoded CSET Xd, LO (CSINC Xd, XZR, XZR, HS word) \
                 == ConditionHolds(LO) ? 1 : 0",
            ),
            (
                A64_CSET_FORMS[4],
                ProofCategory::Comparison,
                "A64 decoded CSET Xd, MI (CSINC Xd, XZR, XZR, PL word) \
                 == ConditionHolds(MI) ? 1 : 0",
            ),
            (
                A64_CSET_FORMS[5],
                ProofCategory::Comparison,
                "A64 decoded CSET Xd, PL (CSINC Xd, XZR, XZR, MI word) \
                 == ConditionHolds(PL) ? 1 : 0",
            ),
            (
                A64_CSET_FORMS[6],
                ProofCategory::Comparison,
                "A64 decoded CSET Xd, VS (CSINC Xd, XZR, XZR, VC word) \
                 == ConditionHolds(VS) ? 1 : 0",
            ),
            (
                A64_CSET_FORMS[7],
                ProofCategory::Comparison,
                "A64 decoded CSET Xd, VC (CSINC Xd, XZR, XZR, VS word) \
                 == ConditionHolds(VC) ? 1 : 0",
            ),
            (
                A64_CSET_FORMS[8],
                ProofCategory::Comparison,
                "A64 decoded CSET Xd, HI (CSINC Xd, XZR, XZR, LS word) \
                 == ConditionHolds(HI) ? 1 : 0",
            ),
            (
                A64_CSET_FORMS[9],
                ProofCategory::Comparison,
                "A64 decoded CSET Xd, LS (CSINC Xd, XZR, XZR, HI word) \
                 == ConditionHolds(LS) ? 1 : 0",
            ),
            (
                A64_CSET_FORMS[10],
                ProofCategory::Comparison,
                "A64 decoded CSET Xd, GE (CSINC Xd, XZR, XZR, LT word) \
                 == ConditionHolds(GE) ? 1 : 0",
            ),
            (
                A64_CSET_FORMS[11],
                ProofCategory::Comparison,
                "A64 decoded CSET Xd, LT (CSINC Xd, XZR, XZR, GE word) \
                 == ConditionHolds(LT) ? 1 : 0",
            ),
            (
                A64_CSET_FORMS[12],
                ProofCategory::Comparison,
                "A64 decoded CSET Xd, GT (CSINC Xd, XZR, XZR, LE word) \
                 == ConditionHolds(GT) ? 1 : 0",
            ),
            (
                A64_CSET_FORMS[13],
                ProofCategory::Comparison,
                "A64 decoded CSET Xd, LE (CSINC Xd, XZR, XZR, GT word) \
                 == ConditionHolds(LE) ? 1 : 0",
            ),
            (
                A64_CSET_FORMS[14],
                ProofCategory::Comparison,
                "A64 decoded CSET Wd, EQ (CSINC Wd, WZR, WZR, NE word) \
                 == ConditionHolds(EQ) ? 1 : 0, Xd[63:32] zero",
            ),
            (
                A64_CSET_FORMS[15],
                ProofCategory::Comparison,
                "A64 decoded CSET Wd, NE (CSINC Wd, WZR, WZR, EQ word) \
                 == ConditionHolds(NE) ? 1 : 0, Xd[63:32] zero",
            ),
            (
                A64_CSET_FORMS[16],
                ProofCategory::Comparison,
                "A64 decoded CSET Wd, HS (CSINC Wd, WZR, WZR, LO word) \
                 == ConditionHolds(HS) ? 1 : 0, Xd[63:32] zero",
            ),
            (
                A64_CSET_FORMS[17],
                ProofCategory::Comparison,
                "A64 decoded CSET Wd, LO (CSINC Wd, WZR, WZR, HS word) \
                 == ConditionHolds(LO) ? 1 : 0, Xd[63:32] zero",
            ),
            (
                A64_CSET_FORMS[18],
                ProofCategory::Comparison,
                "A64 decoded CSET Wd, MI (CSINC Wd, WZR, WZR, PL word) \
                 == ConditionHolds(MI) ? 1 : 0, Xd[63:32] zero",
            ),
            (
                A64_CSET_FORMS[19],
                ProofCategory::Comparison,
                "A64 decoded CSET Wd, PL (CSINC Wd, WZR, WZR, MI word) \
                 == ConditionHolds(PL) ? 1 : 0, Xd[63:32] zero",
            ),
            (
                A64_CSET_FORMS[20],
                ProofCategory::Comparison,
                "A64 decoded CSET Wd, VS (CSINC Wd, WZR, WZR, VC word) \
                 == ConditionHolds(VS) ? 1 : 0, Xd[63:32] zero",
            ),
            (
                A64_CSET_FORMS[21],
                ProofCategory::Comparison,
                "A64 decoded CSET Wd, VC (CSINC Wd, WZR, WZR, VS word) \
                 == ConditionHolds(VC) ? 1 : 0, Xd[63:32] zero",
            ),
            (
                A64_CSET_FORMS[22],
                ProofCategory::Comparison,
                "A64 decoded CSET Wd, HI (CSINC Wd, WZR, WZR, LS word) \
                 == ConditionHolds(HI) ? 1 : 0, Xd[63:32] zero",
            ),
            (
                A64_CSET_FORMS[23],
                ProofCategory::Comparison,
                "A64 decoded CSET Wd, LS (CSINC Wd, WZR, WZR, HI word) \
                 == ConditionHolds(LS) ? 1 : 0, Xd[63:32] zero",
            ),
            (
                A64_CSET_FORMS[24],
                ProofCategory::Comparison,
                "A64 decoded CSET Wd, GE (CSINC Wd, WZR, WZR, LT word) \
                 == ConditionHolds(GE) ? 1 : 0, Xd[63:32] zero",
            ),
            (
                A64_CSET_FORMS[25],
                ProofCategory::Comparison,
                "A64 decoded CSET Wd, LT (CSINC Wd, WZR, WZR, GE word) \
                 == ConditionHolds(LT) ? 1 : 0, Xd[63:32] zero",
            ),
            (
                A64_CSET_FORMS[26],
                ProofCategory::Comparison,
                "A64 decoded CSET Wd, GT (CSINC Wd, WZR, WZR, LE word) \
                 == ConditionHolds(GT) ? 1 : 0, Xd[63:32] zero",
            ),
            (
                A64_CSET_FORMS[27],
                ProofCategory::Comparison,
                "A64 decoded CSET Wd, LE (CSINC Wd, WZR, WZR, GT word) \
                 == ConditionHolds(LE) ? 1 : 0, Xd[63:32] zero",
            ),
        ];

        for (index, ((lane_category, lane_obligation), (form, audited_category, audited_name))) in
            lane.iter().zip(AUDITED.iter()).enumerate()
        {
            assert_eq!(
                *form, A64_CSET_FORMS[index],
                "audited row {index} must stay bound to the form the lane registers at that \
                 position"
            );
            let produced =
                a64_cset_form_obligation_for(*form, form.word(), None).unwrap_or_else(|error| {
                    panic!(
                        "audited form {form:?} (row {index}) no longer mints its \
                         decoded-word obligation: {error:?}"
                    )
                });
            assert_eq!(
                produced.name.as_str(),
                *audited_name,
                "audited row {index} ({form:?}) must keep the obligation name its \
                 originating commit registered"
            );
            assert_eq!(
                lane_obligation, &produced,
                "audited row {audited_name:?} must be EXACTLY what its own per-form \
                 producer mints from that form's encoder word — a substituted \
                 obligation may not inherit its share of the +28 cardinality credit"
            );
            assert_eq!(
                lane_category, audited_category,
                "audited row {audited_name:?} must stay in its audited category"
            );
        }

        let db = ProofDatabase::new();
        for (category, obligation) in &lane {
            let name = obligation.name.as_str();
            let registrations: Vec<_> = db
                .all()
                .iter()
                .filter(|proof| proof.obligation.name == name)
                .collect();
            assert_eq!(
                registrations.len(),
                1,
                "corpus row {name:?} must identify exactly one live registration"
            );
            assert_eq!(registrations[0].category, *category, "{name:?}");
            assert!(
                registrations[0].obligation.is_genuinely_proven(),
                "registered corpus row {name:?} must remain structurally non-degenerate"
            );
            assert!(
                !SOLVER_CAPACITY_PENDING_ALLOWLIST.contains(&name),
                "new corpus row {name:?} may not silently inherit solver-capacity debt"
            );
            // The whole point of the family: the only free input is the packed
            // NZCV, so the discharge is COMPLETE over the input domain rather
            // than sampled. A row that loses that property has acquired an extra
            // free input, which means one of the two zero registers went away.
            assert_eq!(
                VerificationStrength::for_obligation_with_config(
                    obligation,
                    &trust_cg_verify::lowering_proof::VerificationConfig::default()
                ),
                VerificationStrength::Exhaustive,
                "corpus row {name:?} is no longer decided exhaustively"
            );
        }
    });
}

/// The decoded-word CSET family is registered in `ProofCategory::Comparison`,
/// where the walk resolves a query by the FIRST case-insensitive substring
/// match. Registering it must not change what any PRE-EXISTING token resolves
/// to — the opcode-level `"cmp"` token, every `icmp_<cond>_<width>` citation,
/// every `select_*` citation, and every NZCV producer/consumer form's own
/// `"a64 nzcv ..."` query.
#[test]
fn cset_family_registration_does_not_shadow_the_comparison_families() {
    on_large_stack(|| {
        use trust_cg_verify::proof_database::ProofCategory;
        let db = ProofDatabase::new();
        let first_containing = |token: &str| -> Option<String> {
            db.all()
                .iter()
                .filter(|p| p.category == ProofCategory::Comparison)
                .find(|p| p.obligation.name.to_lowercase().contains(token))
                .map(|p| p.obligation.name.clone())
        };
        let cmp = first_containing("cmp").expect("the `cmp` token must still resolve");
        assert!(
            cmp.starts_with("Icmp_"),
            "the opcode-level `cmp` token now resolves to `{cmp}`"
        );
        for cond in [
            "eq", "ne", "slt", "sge", "sgt", "sle", "ult", "uge", "ugt", "ule",
        ] {
            for width in ["i32", "i64"] {
                let token = format!("icmp_{cond}_{width}");
                let hit = first_containing(&token)
                    .unwrap_or_else(|| panic!("`{token}` no longer resolves"));
                assert!(
                    hit.to_lowercase().starts_with(&token),
                    "`{token}` now resolves to `{hit}`"
                );
            }
        }
        for cmp_width in [32u32, 64] {
            for sel_width in [32u32, 64] {
                let token = format!("select_eq_nzcv{cmp_width}_sel{sel_width}");
                let hit = first_containing(&token)
                    .unwrap_or_else(|| panic!("`{token}` no longer resolves"));
                assert!(
                    hit.to_lowercase().starts_with(&token),
                    "`{token}` now resolves to `{hit}`"
                );
            }
        }
        // The NZCV producer/consumer family registers before this one: each of
        // its rows must still be the first row its own query prefix reaches.
        for (_, obligation) in
            trust_cg_verify::aarch64_flag_consumer_proofs::all_flag_consumer_proofs()
        {
            let query = obligation
                .name
                .split_once(':')
                .map(|(head, _)| format!("{}:", head.to_lowercase()))
                .unwrap_or_else(|| panic!("{:?} has no query prefix", obligation.name));
            let hit =
                first_containing(&query).unwrap_or_else(|| panic!("`{query}` does not resolve"));
            assert_eq!(
                hit, obligation.name,
                "`{query}` resolves to a different row"
            );
        }
        // And every CSET form's own token resolves to ITS OWN row.
        for form in trust_cg_verify::aarch64_value_decode_proofs::A64_CSET_FORMS {
            let hit = first_containing(form.query)
                .unwrap_or_else(|| panic!("`{}` does not resolve", form.query));
            assert_eq!(
                hit, form.name,
                "`{}` resolves to a different row",
                form.query
            );
        }
    });
}

/// The four atomic-perimeter rows, bound LIVE by name.
///
/// `atomic_proofs`'s own cardinality pin audits them locally; binding them
/// by name here means the total cannot go green again by swapping one of them
/// for something unrelated.
#[test]
fn atomic_perimeter_corpus_addition_is_exact_live_and_nondegenerate() {
    on_large_stack(|| {
        use std::collections::HashSet;
        use trust_cg_verify::atomic_proofs::{
            all_atomic_proofs, proof_atomic_load_single_copy_i128, proof_dmb_ish_orders_loads,
            proof_dmb_ishld_orders_loads, proof_swp_updates_mem_i64,
        };
        use trust_cg_verify::lowering_proof::ProofObligation;
        use trust_cg_verify::proof_database::ProofCategory;

        let unique: HashSet<&str> = ATOMIC_PERIMETER_CORPUS_ADDITION.iter().copied().collect();
        assert_eq!(
            unique.len(),
            ATOMIC_PERIMETER_CORPUS_ADDITION.len(),
            "the atomic-perimeter addition contains duplicate names"
        );

        // Bound to the INDIVIDUAL PRODUCER of each audited row, not merely to
        // the atomic lane as a whole.
        //
        // Membership in `all_atomic_proofs()` is far too weak to hold this
        // audit: mutation-measured, replacing `DMB_ISHLD` in the list above
        // with the long-standing `SWP_I32: mem[addr] = operand` satisfies a
        // lane-level check, a category check, an exactly-one-registration
        // check and a non-degeneracy check all at once — so the +4 cardinality
        // credit could be silently inherited by four rows that PREDATE the
        // increase, which is precisely the laundering this ratchet exists to
        // prevent. Pinning each name to the constructor its originating commit
        // added closes that.
        let producers: [(&str, ProofObligation); 4] = [
            ("SWP_I64: mem[addr] = operand", proof_swp_updates_mem_i64()),
            (
                "AtomicLoad_I128: single-copy (one paired access)",
                proof_atomic_load_single_copy_i128(),
            ),
            (
                "DMB_ISH: orders prior load before subsequent load",
                proof_dmb_ish_orders_loads(),
            ),
            (
                "DMB_ISHLD: orders prior load before subsequent load",
                proof_dmb_ishld_orders_loads(),
            ),
        ];
        let producer_names: HashSet<&str> = producers.iter().map(|(name, _)| *name).collect();
        assert_eq!(
            producer_names, unique,
            "the audited atomic-perimeter names must be exactly the four the \
             originating constructors produce"
        );
        for (name, produced) in &producers {
            assert_eq!(
                produced.name, *name,
                "the constructor the originating commit added no longer produces \
                 {name:?}; the cardinality credit has been orphaned"
            );
        }

        // Still assert lane membership: a row can be produced and yet dropped
        // from the registry, which would leave the total short.
        let lane_names: HashSet<String> = all_atomic_proofs().into_iter().map(|p| p.name).collect();
        for name in ATOMIC_PERIMETER_CORPUS_ADDITION {
            assert!(
                lane_names.contains(*name),
                "audited atomic-perimeter row {name:?} is no longer produced by \
                 `all_atomic_proofs`; the cardinality credit has been orphaned"
            );
        }

        let db = ProofDatabase::new();
        for name in ATOMIC_PERIMETER_CORPUS_ADDITION {
            let registrations: Vec<_> = db
                .all()
                .iter()
                .filter(|proof| proof.obligation.name == *name)
                .collect();
            assert_eq!(
                registrations.len(),
                1,
                "corpus row {name:?} must identify exactly one live registration"
            );
            assert_eq!(
                registrations[0].category,
                ProofCategory::AtomicOperations,
                "{name:?} must stay in the atomic lane"
            );
            assert!(
                registrations[0].obligation.is_genuinely_proven(),
                "registered corpus row {name:?} must remain structurally non-degenerate"
            );
            assert!(
                !SOLVER_CAPACITY_PENDING_ALLOWLIST.contains(name),
                "new corpus row {name:?} may not silently inherit solver-capacity debt"
            );
        }
    });
}

/// The forty CMP -> CSEL select rows, bound LIVE to the
/// module that produces them.
///
/// The cardinality alone would be satisfied by any forty rows; what makes this
/// lane worth its count is that each machine side is a DECODED CSEL word
/// rather than a restatement of the spec, so the check is that every row is
/// registered exactly once, in `Comparison`, and is structurally
/// non-degenerate — the property the retracted `CmpSelectCombine` entries
/// failed.
#[test]
fn select_cmp_csel_corpus_addition_is_exact_live_and_nondegenerate() {
    on_large_stack(|| {
        use std::collections::HashSet;
        use trust_cg_verify::aarch64_select_proofs::all_select_cmp_csel_proofs;
        use trust_cg_verify::proof_database::ProofCategory;

        let lane = all_select_cmp_csel_proofs();
        assert_eq!(
            lane.len(),
            SELECT_CMP_CSEL_CORPUS_ADDITION_LEN,
            "the conditional-select lane must remain exactly the audited forty forms"
        );
        let lane_names: HashSet<&str> = lane.iter().map(|o| o.name.as_str()).collect();
        assert_eq!(lane_names.len(), lane.len(), "lane names must be unique");
        let db = ProofDatabase::new();
        for obligation in &lane {
            let name = obligation.name.as_str();
            let registrations: Vec<_> = db
                .all()
                .iter()
                .filter(|proof| proof.obligation.name == name)
                .collect();
            assert_eq!(
                registrations.len(),
                1,
                "corpus row {name:?} must identify exactly one live registration"
            );
            assert_eq!(
                registrations[0].category,
                ProofCategory::Comparison,
                "{name:?} must stay in the comparison lane"
            );
            assert!(
                registrations[0].obligation.is_genuinely_proven(),
                "registered corpus row {name:?} must remain structurally non-degenerate"
            );
            assert!(
                !SOLVER_CAPACITY_PENDING_ALLOWLIST.contains(&name),
                "new corpus row {name:?} may not silently inherit solver-capacity debt"
            );
        }
    });
}

/// The single source-bound leaf-frame row, bound LIVE to the
/// CONSTRUCTOR that produces it — not merely to the name and category.
///
/// MEASURED HOLE, closed here (2026-09-25). This gate used to check only that
/// `FRAME_OBLIGATION_NAME` resolved to exactly one live registration, sat in
/// `ProofCategory::FrameLayout`, was structurally non-degenerate
/// (`is_genuinely_proven`, i.e. `trust_ir_expr != aarch64_expr`) and was off
/// the capacity allowlist. Every one of those four is satisfied by any
/// long-standing row in the same category: substituting the audited name for
/// the pre-existing `"FrameLayout: distinct slots have non-overlapping memory"`
/// — which is registered at `2f9250df`, the commit that pinned 1,978, where
/// `source_bound_frame.rs` did not yet exist at all — left this test GREEN, so
/// the +1 cardinality credit was inheritable by a row that predates the
/// increase. That is exactly the laundering the ratchet exists to prevent.
///
/// The fix is to bind the row to `source_bound_frame::frame_obligation()`, the
/// constructor `69f2030a` ("Discharge and export exact source-bound AArch64
/// leaf frames") added in the same commit as the registration and the name
/// constant. `ProofObligation` derives `PartialEq` over its FULL content (both
/// expression trees, inputs, preconditions, fp_inputs, category, provenance
/// and name — see `lowering_proof.rs`), so equality against the producer's
/// output makes a substitution fail on the PRODUCER rather than on the
/// category. Pinning only the cardinality would additionally let this row be
/// deleted and an unrelated one added while 1,979 still read green.
#[test]
fn source_bound_leaf_frame_corpus_addition_is_exact_live_and_nondegenerate() {
    on_large_stack(|| {
        use trust_cg_verify::proof_database::ProofCategory;
        use trust_cg_verify::source_bound_frame::{FRAME_OBLIGATION_NAME, frame_obligation};

        // PRODUCER BINDING, checked before anything else so a substituted row
        // reports the producer mismatch rather than a downstream symptom.
        let produced = frame_obligation();
        assert_eq!(
            produced.name, FRAME_OBLIGATION_NAME,
            "the audited leaf-frame corpus row must be the one \
             `source_bound_frame::frame_obligation()` produces; a name this constructor does \
             not emit cannot inherit the 1,978 -> 1,979 cardinality credit"
        );

        let db = ProofDatabase::new();
        let registrations: Vec<_> = db
            .all()
            .iter()
            .filter(|proof| proof.obligation.name == FRAME_OBLIGATION_NAME)
            .collect();
        assert_eq!(
            registrations.len(),
            1,
            "the source-bound leaf-frame corpus row {FRAME_OBLIGATION_NAME:?} must identify \
             exactly one live registration"
        );
        assert_eq!(
            registrations[0].category,
            ProofCategory::FrameLayout,
            "corpus row {FRAME_OBLIGATION_NAME:?} must stay in the frame-layout category it was \
             audited in"
        );
        assert!(
            registrations[0].obligation.is_genuinely_proven(),
            "registered corpus row {FRAME_OBLIGATION_NAME:?} must remain structurally \
             non-degenerate"
        );
        assert!(
            !SOLVER_CAPACITY_PENDING_ALLOWLIST.contains(&FRAME_OBLIGATION_NAME),
            "new corpus row {FRAME_OBLIGATION_NAME:?} may not silently inherit solver-capacity \
             debt"
        );
        // The registered row must be the producer's output in FULL, not just
        // something sharing its name: a pre-existing FrameLayout obligation
        // renamed at the registration site would satisfy every assertion above.
        assert_eq!(
            registrations[0].obligation, produced,
            "corpus row {FRAME_OBLIGATION_NAME:?} must be exactly the obligation \
             `source_bound_frame::frame_obligation()` builds — same source and machine \
             expression trees, inputs, preconditions and provenance — so the increase cannot \
             be credited to a pre-existing row"
        );
        // The SOURCE side of this theorem is the constant `true` (the machine
        // side carries the whole FP/LR envelope), which is what makes a
        // content-blind category check so weak here. State it, so a reshaped
        // producer that quietly moves the obligation is visible too.
        assert_eq!(
            produced.trust_ir_expr,
            trust_cg_verify::smt::SmtExpr::bool_const(true),
            "the leaf-frame theorem's source side is the constant `true`; a producer that \
             changes it is a different obligation and must be re-audited"
        );
    });
}

#[test]
fn aarch64_standalone_rotate_and_tst_corpus_addition_is_exact_live_and_nondegenerate() {
    on_large_stack(|| {
        use std::collections::HashSet;
        use trust_cg_verify::cmp_combine_proofs::proof_tst_nzcv_effect;
        use trust_cg_verify::lowering_proof::all_ror_immediate_proofs;

        // The +30 is TWO families, and each is pinned to the function that
        // produces it. Checking only the union would let one family shrink
        // while the other grew and still report a green 1,907.
        let ror_expected: HashSet<String> = ROR_IMMEDIATE_CORPUS_ADDITION
            .iter()
            .map(|name| (*name).to_string())
            .collect();
        assert_eq!(
            ror_expected.len(),
            ROR_IMMEDIATE_CORPUS_ADDITION.len(),
            "ROR-immediate corpus ratchet contains duplicate names"
        );
        assert_eq!(
            ROR_IMMEDIATE_CORPUS_ADDITION.len(),
            10,
            "the ROR-immediate half of the increase is five amounts x {{W, X}}"
        );
        let ror_lane = all_ror_immediate_proofs();
        let ror_live: HashSet<String> = ror_lane.iter().map(|proof| proof.name.clone()).collect();
        assert_eq!(
            ror_live, ror_expected,
            "the ten-obligation ROR-immediate increase must remain exactly the audited \
             standalone rotate lane"
        );

        let tst_expected: HashSet<String> = TST_NZCV_CONSUMER_CORPUS_ADDITION
            .iter()
            .map(|name| (*name).to_string())
            .collect();
        assert_eq!(
            tst_expected.len(),
            TST_NZCV_CONSUMER_CORPUS_ADDITION.len(),
            "TST NZCV corpus ratchet contains duplicate names"
        );
        assert_eq!(
            TST_NZCV_CONSUMER_CORPUS_ADDITION.len(),
            20,
            "the TST half of the increase is ten conditions x {{w64, w32}}"
        );
        let tst_lane: Vec<_> = proof_tst_nzcv_effect(64)
            .into_iter()
            .chain(proof_tst_nzcv_effect(32))
            .collect();
        let tst_live: HashSet<String> = tst_lane.iter().map(|proof| proof.name.clone()).collect();
        assert_eq!(
            tst_live, tst_expected,
            "the twenty-obligation TST increase must remain exactly the audited standalone \
             per-condition NZCV lane at both emitted widths"
        );

        assert!(
            ror_lane
                .iter()
                .chain(tst_lane.iter())
                .all(|proof| proof.is_genuinely_proven()),
            "every newly credited rotate/TST obligation must be structurally non-degenerate"
        );

        let db = ProofDatabase::new();
        for name in ROR_IMMEDIATE_CORPUS_ADDITION
            .iter()
            .chain(TST_NZCV_CONSUMER_CORPUS_ADDITION.iter())
        {
            let registrations: Vec<_> = db
                .all()
                .iter()
                .filter(|proof| proof.obligation.name == *name)
                .collect();
            assert_eq!(
                registrations.len(),
                1,
                "new corpus row {name:?} must identify exactly one live registration"
            );
            assert!(
                registrations[0].obligation.is_genuinely_proven(),
                "registered corpus row {name:?} must remain structurally non-degenerate"
            );
            assert!(
                !SOLVER_CAPACITY_PENDING_ALLOWLIST.contains(name),
                "new corpus row {name:?} may not silently inherit solver-capacity debt"
            );
        }
    });
}

/// Keep external-solver proof campaigns out of the ordinary hermetic test lane
/// without hiding them from libtest. The opt-in must be the exact value `1`;
/// every other value is a visible runtime SKIP, never qualified proof evidence.
/// A fresh temporary directory with mode exactly 0700 whatever the umask, for
/// a child's cache root (`XDG_CACHE_HOME`): AY's identity rule refuses its
/// private copy beneath any directory others may write.
fn private_tempdir(prefix: &str) -> tempfile::TempDir {
    let directory = tempfile::Builder::new()
        .prefix(prefix)
        .tempdir()
        .expect("private tempdir");
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        std::fs::set_permissions(directory.path(), std::fs::Permissions::from_mode(0o700))
            .expect("make the tempdir 0700");
    }
    directory
}

fn formal_proof_test_enabled(test_name: &str) -> bool {
    if matches!(std::env::var(FORMAL_PROOF_TEST_ENV).as_deref(), Ok("1")) {
        true
    } else {
        eprintln!(
            "SKIP: {test_name}: external-solver campaign not requested; \
             set {FORMAL_PROOF_TEST_ENV}=1 to run"
        );
        false
    }
}

// ---------------------------------------------------------------------------
// (i) No silent downgrade: the gate fails closed without a solver.
//
// These run on EVERY lane (no solver required) because they assert the
// *contract*: absent a solver, `discharge` returns Err, never a downgraded Ok.
// ---------------------------------------------------------------------------

#[test]
fn gate_fails_closed_when_no_solver() {
    // ALWAYS-ON, deterministic on EVERY machine: inject `available = false` into
    // the testable core so the single most important P0 guarantee — no solver =>
    // Err(NoSolver), never a downgraded Ok — is asserted unconditionally, even
    // on a normal dev/CI box that has a solver installed. Passing `false`
    // short-circuits before any solver call, so no real solver is invoked.
    //
    // (The previous version of this test early-returned whenever a solver was
    // present, so on every normal machine this guarantee was NEVER asserted.)
    let db = ProofDatabase::new();
    let result = GateConfig::strict().discharge_with_availability(&db, false);
    match result {
        Err(GateError::NoSolver { .. }) => {
            // Correct: refused to downgrade to statistical mock.
        }
        Err(other) => panic!("expected NoSolver, got a different gate error: {}", other),
        Ok(_) => panic!(
            "STRICT GATE REGRESSION: discharge_with_availability(.., false) returned Ok. \
             This is exactly the P0 silent-downgrade bug — the gate must fail closed \
             when no solver is available."
        ),
    }
}

/// A non-strict gate (require_solver = false) must NOT fail closed on absence of
/// a solver — it is the explicit opt-out. This pins that `discharge_with_
/// availability` keys the NoSolver decision on `require_solver`, so the always-on
/// test above is genuinely testing the strict path's fail-closed behaviour and
/// not a blanket reject.
#[test]
fn non_strict_gate_does_not_fail_closed_on_no_solver() {
    let gate = GateConfig {
        ay_config: AYConfig::default(),
        require_solver: false,
    };
    // Empty DB so we don't actually invoke a solver; the point is only that the
    // NoSolver branch is NOT taken when require_solver = false even with
    // available = false. We therefore expect EmptyDatabase, never NoSolver.
    let db = ProofDatabase::from_proofs(vec![]);
    match gate.discharge_with_availability(&db, false) {
        Err(GateError::EmptyDatabase) => {}
        Err(GateError::NoSolver { .. }) => panic!(
            "non-strict gate must not return NoSolver: require_solver = false is the opt-out"
        ),
        other => panic!("expected EmptyDatabase for non-strict empty-DB gate, got {other:?}"),
    }
}

#[test]
fn strict_gate_requires_solver_flag_is_set() {
    // The strict constructor must request a solver. If this flips, the whole
    // gate degrades to the old auto-mode behaviour.
    assert!(
        GateConfig::strict().require_solver,
        "GateConfig::strict() must set require_solver = true"
    );
    assert!(
        GateConfig::default().require_solver,
        "GateConfig::default() must be strict"
    );
}

/// Real-environment smoke (always on, no solver required): when this machine
/// genuinely has NO solver, the PUBLIC `discharge()` (which probes the real
/// environment) must itself fail closed — a final guard that the production
/// entry point, not just the injected core, honours the contract. When a solver
/// IS present this is a no-op (the formal smoke / full-DB tests below cover the
/// solver path). The injected-core test above is the deterministic guarantee;
/// this confirms `discharge()` delegates to it faithfully.
#[test]
fn real_discharge_fails_closed_when_environment_has_no_solver() {
    if native_ay_compiled() || ay_available() {
        eprintln!(
            "solver present; real-environment no-solver branch is a no-op here \
             (deterministic contract covered by gate_fails_closed_when_no_solver)"
        );
        return;
    }
    let db = ProofDatabase::new();
    match GateConfig::strict().discharge(&db) {
        Err(GateError::NoSolver { .. }) => {}
        Ok(_) => {
            panic!("STRICT GATE REGRESSION: real discharge() returned Ok with no solver present")
        }
        Err(other) => panic!("expected NoSolver from real discharge(), got: {}", other),
    }
}

/// A trust-cg-verify built from an OVERLAY toolchain (scripts/assemble_trust_overlay.py)
/// checks proofs only with the overlay's own `bin/clean`, through the PRODUCTION
/// discovery (`resolve_proof_checker`, the authority path's discovery under
/// this build's recorded policy), and refuses a capable checker with other
/// bytes, including an explicit `TCG_EXTERNAL_CLEAN_CHECKER`. Before the pin, an
/// overlay whose `bin/clean` lacked carcara-verify silently verified with the
/// aterm package (`store/clean/8606`). Always on and solver-free, but it
/// exercises the pin only when this binary was built from an overlay; an
/// ordinary build asserts that nothing is pinned.
#[test]
fn overlay_build_checks_proofs_only_with_its_own_clean() {
    use trust_cg_verify::ay_identity::ToolchainAyRecord;
    use trust_cg_verify::obligation_cert_store::resolve_proof_checker;
    const OVERRIDES: [&str; 2] = ["TCG_EXTERNAL_CLEAN_CHECKER", "TCG_CLEAN_CHECKER"];

    let record = ToolchainAyRecord::recorded();
    let Some(pin) = record.pinned_clean_sha256() else {
        assert!(record.overlay().is_none());
        eprintln!(
            "not built from an overlay toolchain ({}): no checker pin to exercise here \
             (obligation_cert_store::tests::the_authority_path_applies_the_recorded_overlay_pin \
             drives the same discovery under a fixture overlay record in every build)",
            record.build_sysroot().display()
        );
        return;
    };
    let overlay = record
        .overlay()
        .expect("a pinned build whose manifest was refused cannot run the formal gate");
    assert_eq!(pin, overlay.clean_sha256());
    let own = record.build_sysroot().join("bin").join("clean");

    let resolved =
        trust_cg_process_env::with_env_overrides_removed(&OVERRIDES, resolve_proof_checker);
    assert_eq!(
        resolved,
        Ok((own.clone(), pin.to_owned())),
        "an overlay build must resolve exactly its own bin/clean"
    );

    // A wrapper that runs the overlay's own Clean passes the control probe,
    // but its bytes are not the manifest's: refused, never a fallback.
    let dir = tempfile::tempdir().expect("tempdir");
    let wrapper = dir.path().join("clean");
    std::fs::write(
        &wrapper,
        format!("#!/bin/sh\nexec '{}' \"$@\"\n", own.display()),
    )
    .expect("write the wrapper checker");
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        std::fs::set_permissions(&wrapper, std::fs::Permissions::from_mode(0o755))
            .expect("chmod the wrapper checker");
    }
    let wrapper_text = wrapper.to_str().expect("utf-8 tempdir");
    for variable in OVERRIDES {
        let refused = trust_cg_process_env::with_env_overrides_removed(&OVERRIDES, || {
            trust_cg_process_env::with_env_overrides(
                &[(variable, wrapper_text)],
                resolve_proof_checker,
            )
        });
        let reason = refused.expect_err("an overlay build must refuse another checker");
        assert!(
            reason.contains("never falls back") && reason.contains(pin),
            "{variable}: {reason}"
        );
    }

    // The pin is on the bytes, not the path: the overlay's own file named
    // explicitly is accepted.
    let own_text = own.to_str().expect("utf-8 sysroot");
    let explicit = trust_cg_process_env::with_env_overrides_removed(&OVERRIDES, || {
        trust_cg_process_env::with_env_overrides(
            &[("TCG_EXTERNAL_CLEAN_CHECKER", own_text)],
            resolve_proof_checker,
        )
    });
    assert_eq!(explicit, Ok((own, pin.to_owned())));
}

/// With `TRUST_CG_PROOF_IDENTITY_OUT` set, a real formal run records the proof
/// tools that RAN, where they ran: every `clean` line names the checker this
/// build resolves (`resolve_proof_checker`, the authority path's discovery)
/// with its digest, and every `ay` line the admitted AY. It runs
/// `representative_arithmetic_is_formally_verified` in a child test process,
/// with the variable in that process's environment (so every worker thread
/// sees it, as under `scripts/trust_cargo.sh`) and a fresh cache (so AY solves
/// and Clean checks each proof instead of a stored certificate being
/// consumed without a solve).
#[test]
fn a_real_proof_check_records_the_tools_that_ran() {
    use trust_cg_verify::ay_identity::{ToolchainAyRecord, resolve_for_process};
    use trust_cg_verify::obligation_cert_store::resolve_proof_checker;
    use trust_cg_verify::proof_tool_record::{PROOF_IDENTITY_OUT_ENV, SCHEMA};
    if !formal_proof_test_enabled("a_real_proof_check_records_the_tools_that_ran") {
        return;
    }
    let gate = GateConfig::strict_with_ay(AYConfig::default());
    require_formal_proof_toolchain(&gate, "the proof-tool record");
    let (checker, checker_sha) = resolve_proof_checker().expect("a capable checker resolves");
    let ay = resolve_for_process().expect("an admitted AY resolves");

    // The child's XDG_CACHE_HOME is an ancestor of AY's private copy, which
    // the identity rule refuses beneath a directory others may write. It is
    // made 0700 whatever the umask, as every trust-cg cache directory is:
    // tempfile's default `0777 & !umask` is 0775 under umask 0002, where AY
    // was refused in the child and this leg of the attested soundness gate
    // failed (X-HOST-P13 second audit).
    let cache = private_tempdir("cache");
    let records = tempfile::tempdir().expect("record tempdir");
    let out = records.path().join("identity.jsonl");
    let child = std::process::Command::new(std::env::current_exe().expect("test binary"))
        .args([
            "--exact",
            "representative_arithmetic_is_formally_verified",
            "--nocapture",
            "--test-threads=1",
        ])
        .env(PROOF_IDENTITY_OUT_ENV, &out)
        .env(FORMAL_PROOF_TEST_ENV, "1")
        .env("XDG_CACHE_HOME", cache.path())
        .output()
        .expect("run the representative smoke");
    assert!(
        child.status.success(),
        "the representative smoke failed:\n{}\n{}",
        String::from_utf8_lossy(&child.stdout),
        String::from_utf8_lossy(&child.stderr)
    );

    let text = std::fs::read_to_string(&out).expect("the run wrote a proof-tool record");
    let rows: Vec<serde_json::Value> = text
        .lines()
        .map(|line| serde_json::from_str(line).expect("one JSON object per line"))
        .collect();
    let overlay_manifest = ToolchainAyRecord::recorded()
        .overlay()
        .map(|overlay| overlay.manifest_sha256().to_owned());
    for row in &rows {
        assert_eq!(row["schema"], SCHEMA, "{row}");
        assert_eq!(
            row["toolchain_overlay_manifest_sha256"],
            serde_json::json!(overlay_manifest),
            "{row}"
        );
    }
    let role = |name: &str| -> Vec<&serde_json::Value> {
        rows.iter().filter(|row| row["role"] == name).collect()
    };
    let cleans = role("clean");
    assert!(!cleans.is_empty(), "no checker recorded:\n{text}");
    for row in cleans {
        assert_eq!(row["path"], checker.display().to_string(), "{row}");
        assert_eq!(row["sha256"], checker_sha.as_str(), "{row}");
    }
    let ays = role("ay");
    assert!(!ays.is_empty(), "no solver recorded:\n{text}");
    for row in ays {
        assert_eq!(row["path"], ay.path().display().to_string(), "{row}");
        assert_eq!(row["sha256"], ay.sha256(), "{row}");
    }
    assert_eq!(
        rows.len(),
        2,
        "exactly one checker and one solver ran:\n{text}"
    );
}

// ---------------------------------------------------------------------------
// (ii) + (iii) Formal discharge of the FULL database.
//
// This gate requires aterm's AY solver and a capable independent Clean checker.
// Its explicit environment qualification keeps the plain
// `scripts/trust_cargo.sh test -p trust-cg-verify --tests` lane hermetic; the CI wrapper
// (scripts/check_proof_gate.sh) enables the campaign.
// ---------------------------------------------------------------------------

#[test]
fn full_database_is_formally_verified() {
    if !formal_proof_test_enabled("full_database_is_formally_verified") {
        return;
    }

    // Both proof tools MUST be usable. A missing component is a hard failure,
    // not an opt-out or permission to downgrade the proof requirement.
    let gate = GateConfig::strict();
    require_formal_proof_toolchain(&gate, "full database");

    let db = ProofDatabase::new();
    assert!(!db.is_empty(), "proof database must be non-empty");

    let report = match gate.discharge(&db) {
        Ok(report) => report, // all verified — the ideal outcome
        Err(GateError::NotAllVerified(report)) => report,
        Err(GateError::NoSolver { detail, .. }) => {
            panic!(
                "STRICT GATE FAILED: no solver at discharge time: {}",
                detail
            )
        }
        Err(GateError::EmptyDatabase) => panic!("STRICT GATE FAILED: empty database"),
        Err(GateError::Scheduling { detail, .. }) => {
            panic!("STRICT GATE FAILED: scheduling: {detail}")
        }
    };

    // Preserve counts and per-category results even when an early assertion
    // fails; a failed campaign is evidence too, not an absent measurement.
    println!("{report}");
    // Counterexamples and solver/checker errors are hard failures. A passing
    // gate covers represented obligations, not every possible compiler defect.
    let soundness = report.soundness_failures();
    assert!(
        soundness.is_empty(),
        "STRICT GATE FAILED (SOUNDNESS): {} obligation(s) the solver DISPROVED or could not run:\n{}",
        soundness.len(),
        soundness
            .iter()
            .map(|r| format!("  [{:?}] {} -- {}", r.category, r.name, r.detail()))
            .collect::<Vec<_>>()
            .join("\n"),
    );

    // PROOF AUTHORITY: solver `unsat` is only a candidate. A proof-bearing
    // success gate must separately require every such candidate to have an
    // exact, hole-free Alethe proof accepted by the independent checker.
    let evidence = report.proof_evidence_summary();
    println!(
        "STRICT PROOF EVIDENCE: checked={} artifacts_emitted={} holey={} \
         checker_rejected={} missing={} solver_unsat_uncertified={} \
         capacity_or_other_pending={}",
        evidence.checked_accepted,
        evidence.artifacts_emitted(),
        evidence.holey,
        evidence.checker_rejected,
        evidence.missing,
        evidence.solver_unsat_uncertified,
        evidence.capacity_or_other_pending,
    );
    assert_eq!(
        evidence.failures(),
        0,
        "STRICT GATE FAILED (PROOF EVIDENCE): holey/rejected/missing/uncertified \
         UNSAT artifacts are never Formal/Certified authority: {evidence:?}"
    );

    // No obligation passed via anything but a formal `Verified`.
    assert_no_statistical_fallback(&report);

    // Solver-capacity PENDING (Timeout/Unknown) is REPORTED, never a pass. The
    // five audited wide x86 bit-vector rows may remain pending; any NEW pending
    // row is a gate failure. A known row may graduate to `Verified`, so the
    // observed pending set may be a subset of the allowlist, never a superset.
    // This preserves load tolerance without letting solver/checker regressions
    // silently widen the formal floor.
    let pending = report.failures_in_class(FailureClass::SolverCapacity);
    let unexpected: Vec<_> = pending
        .iter()
        .copied()
        .filter(|result| !SOLVER_CAPACITY_PENDING_ALLOWLIST.contains(&result.name.as_str()))
        .collect();
    assert!(
        unexpected.is_empty(),
        "STRICT GATE FAILED (UNALLOWLISTED PENDING): {} new timeout/unknown obligation(s):\n{}",
        unexpected.len(),
        unexpected
            .iter()
            .map(|r| format!("  [{:?}] {} -- {}", r.category, r.name, r.detail()))
            .collect::<Vec<_>>()
            .join("\n"),
    );
    if pending.is_empty() {
        assert_eq!(report.verified(), report.total());
        println!(
            "STRICT GATE OK: all {} obligations formally Verified (0 soundness failures).",
            report.total()
        );
    } else {
        println!(
            "STRICT GATE OK: {}/{} formally Verified, 0 soundness failures; \
             {} solver-capacity PENDING (timeouts/unknown — reported, not a pass; \
             audited allowlist only):\n{}",
            report.verified(),
            report.total(),
            pending.len(),
            report.pending_summary(),
        );
    }
}

/// Assert no result counts as a pass via anything but a formal `Verified`.
///
/// The strict gate never calls the statistical mock evaluator, so this can only
/// fail if the gate implementation regresses to admit a non-formal outcome as
/// passing. It is the explicit lock for requirement (iii).
fn assert_no_statistical_fallback(report: &GateReport) {
    // The strict gate counts an obligation as passing ONLY when it is formally
    // `Verified` (never a statistical-mock pass). Lock that property in a way that
    // is compatible with allowlisted solver-capacity PENDING obligations: the
    // number of formally-valid results must equal the reported verified count
    // (nothing non-formal is counted as a pass), and every non-verified result
    // must carry a real failure outcome rather than a silent pass.
    let formally_valid = report
        .results
        .iter()
        .filter(|r| r.is_formally_valid())
        .count();
    assert_eq!(
        formally_valid,
        report.verified(),
        "strict gate counted a non-formal result as verified (statistical-mock fallback?)"
    );
    for r in &report.results {
        assert!(
            r.is_formally_valid() || r.failure_kind().is_some(),
            "obligation '{}' is neither formally Verified nor a recognized failure outcome \
             (possible non-formal pass): {}",
            r.name,
            r.detail(),
        );
    }
}

// ---------------------------------------------------------------------------
// Smaller formal lane: discharge a representative subset so a solver-equipped
// dev box gets fast signal without the full-database wall-clock cost.
// It shares the explicit external-solver qualification used by the full lane.
// ---------------------------------------------------------------------------

#[test]
fn representative_arithmetic_is_formally_verified() {
    if !formal_proof_test_enabled("representative_arithmetic_is_formally_verified") {
        return;
    }

    use trust_cg_verify::proof_database::{CategorizedProof, ProofCategory};

    let gate = GateConfig::strict_with_ay(AYConfig::default().with_timeout(60_000));
    require_formal_proof_toolchain(&gate, "representative arithmetic smoke");

    let full = ProofDatabase::new();
    let subset: Vec<CategorizedProof> = full
        .by_category(ProofCategory::Arithmetic)
        .into_iter()
        .take(6)
        .cloned()
        .collect();
    assert!(!subset.is_empty(), "no arithmetic proofs to discharge");
    let db = ProofDatabase::from_proofs(subset);

    let report = gate
        .discharge(&db)
        .unwrap_or_else(|e| panic!("representative arithmetic gate failed: {}", e));
    assert!(report.all_verified());
    assert_no_statistical_fallback(&report);
}

/// Reproduce the packaged AY self-check refusal on the canonical byte-select
/// theorem without hiding it behind the full database's runtime.
#[test]
fn pblendvb_canonical_mask_is_formally_verified() {
    if !formal_proof_test_enabled("pblendvb_canonical_mask_is_formally_verified") {
        return;
    }
    let name = "x86_64: V128BoolSelect canonical byte mask -> PBLENDVB";
    let proofs: Vec<_> = ProofDatabase::new()
        .all()
        .iter()
        .filter(|proof| proof.obligation.name == name)
        .cloned()
        .collect();
    assert_eq!(
        proofs.len(),
        1,
        "the exact registered obligation must remain live"
    );
    let gate = GateConfig::strict_with_ay(AYConfig::default());
    let db = ProofDatabase::from_proofs(proofs);
    let report = match gate.discharge(&db) {
        Ok(report) => report,
        Err(GateError::NotAllVerified(report)) => {
            use trust_cg_verify::ay_bridge::{generate_smt2_query, generate_smt2_query_raw};
            let obligation = &db.all()[0].obligation;
            println!(
                "BEGIN PBLENDVB SIMPLIFIED SMT2\n{}END PBLENDVB SIMPLIFIED SMT2",
                generate_smt2_query(obligation, &AYConfig::default())
            );
            println!(
                "BEGIN PBLENDVB RAW SMT2\n{}END PBLENDVB RAW SMT2",
                generate_smt2_query_raw(obligation, &AYConfig::default())
            );
            report
        }
        Err(error) => panic!("canonical PBLENDVB gate could not run: {error}"),
    };
    println!("{report}");
    assert!(
        report.all_verified(),
        "canonical PBLENDVB proof was refused"
    );
    assert_no_statistical_fallback(&report);
}

/// Full symbolic FABS masks and register slices need checked certificates.
#[test]
fn aarch64_fabs_full_bit_bindings_are_formally_verified() {
    if !formal_proof_test_enabled("aarch64_fabs_full_bit_bindings_are_formally_verified") {
        return;
    }
    let gate = GateConfig::strict_with_ay(AYConfig::default().with_timeout(60_000));
    require_formal_proof_toolchain(&gate, "full raw-bit FABS obligations");
    let full = ProofDatabase::new();
    let subset = full
        .all()
        .iter()
        .filter(|proof| {
            matches!(
                proof.obligation.name.as_str(),
                "Fabs_F32 -> FABS Sd" | "Fabs_F64 -> FABS Dd"
            )
        })
        .cloned()
        .collect::<Vec<_>>();
    assert_eq!(subset.len(), 2);
    assert!(
        subset
            .iter()
            .all(|proof| proof.obligation.is_genuinely_proven())
    );
    let report = gate
        .discharge(&ProofDatabase::from_proofs(subset))
        .expect("both FABS widths need independently checked certificates");
    println!("{report}");
    assert!(report.all_verified());
    assert_no_statistical_fallback(&report);
}

/// Formal floor for the live packed-integer and FP bindings introduced by
/// #1111. The CSEL/CSINC/CSNEG self-identities were subsequently withdrawn;
/// retain them as explicit opcode-unmapped controls instead of looking up
/// nonexistent proofs. Their evidence is now per instruction (the NZCV
/// producer/consumer family binds each select to its reaching producer), which
/// is sampled/finite evaluation, not a formal floor this test could assert.
#[test]
fn wired_packed_csel_fp_bindings_are_formally_verified() {
    if !formal_proof_test_enabled("wired_packed_csel_fp_bindings_are_formally_verified") {
        return;
    }

    use trust_cg_ir::AArch64Opcode;
    use trust_cg_verify::coverage_gate::{OpcodeClass, classify_aarch64};
    use trust_cg_verify::function_verifier::FunctionVerifier;
    use trust_cg_verify::proof_database::CategorizedProof;

    for opcode in [
        AArch64Opcode::Csel,
        AArch64Opcode::Csinc,
        AArch64Opcode::Csneg,
    ] {
        assert!(matches!(
            classify_aarch64(opcode),
            OpcodeClass::EmittableNeedsProof
        ));
        assert!(
            FunctionVerifier::opcode_to_proof_query(opcode).is_none(),
            "{opcode:?}: a withdrawn self-identity cannot supply a value proof"
        );
    }

    // The EXACT proof-name substrings the coverage gate / verifiers now bind for
    // the newly-wired opcodes. Width/lane-exact, single-instruction lowerings.
    let wired_names: &[&str] = &[
        // x86 bitwise.
        "V128 Band -> PAND xmm,xmm",
        "V128 Bor -> POR xmm,xmm",
        // x86 lane-exact add/sub.
        "V16I8Add -> PADDB",
        "V8I16Add -> PADDW",
        "V4I32Add -> PADDD",
        "V2I64Add -> PADDQ",
        "V16I8Sub -> PSUBB",
        "V8I16Sub -> PSUBW",
        "V4I32Sub -> PSUBD",
        "V2I64Sub -> PSUBQ",
        // x86 lane-exact eq/sgt compare masks.
        "V16I8Icmp_Eq -> PCMPEQB",
        "V8I16Icmp_Eq -> PCMPEQW",
        "V4I32Icmp_Eq -> PCMPEQD",
        "V16I8Icmp_Sgt -> PCMPGTB",
        "V8I16Icmp_Sgt -> PCMPGTW",
        "V4I32Icmp_Sgt -> PCMPGTD",
        // x86 uniform-immediate dword shifts.
        "V4I32 Ishl uniform immediate -> PSLLD",
        "V4I32 Ushr uniform immediate -> PSRLD",
        "V4I32 Sshr uniform immediate -> PSRAD",
        // x86 uniform-immediate qword shifts + the PMULUDQ faithful lane model
        // (the SSE2 vectorizer's packed 64-bit multiply compose).
        "V2I64 Ishl uniform immediate -> PSLLQ",
        "V2I64 Ushr uniform immediate -> PSRLQ",
        "V2I64 even-dword widening Umul -> PMULUDQ",
        // AArch64 FP trio, BOTH widths.
        "Fabs_F32 -> FABS Sd",
        "Fabs_F64 -> FABS Dd",
        "Fsqrt_F32 -> FSQRT Sd",
        "Fsqrt_F64 -> FSQRT Dd",
        "Fdiv_F32 -> FDIV Sd",
        "Fdiv_F64 -> FDIV Dd",
    ];

    let gate = GateConfig::strict_with_ay(AYConfig::default().with_timeout(60_000));
    require_formal_proof_toolchain(&gate, "#1111 wired-bindings formal floor");

    let full = ProofDatabase::new();
    let all = full.all();
    let mut subset: Vec<CategorizedProof> = Vec::with_capacity(wired_names.len());
    for want in wired_names {
        let found = all
            .iter()
            .find(|p| p.obligation.name.contains(want))
            .unwrap_or_else(|| {
                panic!("#1111 wired binding {want:?} resolves to NO registered proof")
            });
        subset.push((*found).clone());
    }
    assert_eq!(
        subset.len(),
        wired_names.len(),
        "every wired binding must resolve to exactly one registered obligation"
    );

    let db = ProofDatabase::from_proofs(subset);
    let report = match gate.discharge(&db) {
        Ok(report) => report,
        Err(GateError::NotAllVerified(report)) => report,
        Err(e) => panic!("#1111 wired-bindings gate errored: {e}"),
    };

    // Every live binding still requires an independently checked certificate.
    let soundness = report.soundness_failures();
    assert!(
        soundness.is_empty(),
        "#1111 WIRED-BINDINGS SOUNDNESS FAILURE: {} obligation(s) AY disproved or the proof route could not check:\n{}",
        soundness.len(),
        soundness
            .iter()
            .map(|r| format!("  [{:?}] {} -- {}", r.category, r.name, r.detail()))
            .collect::<Vec<_>>()
            .join("\n"),
    );
    assert_no_statistical_fallback(&report);
    // These are all small, fast obligations: every one should formally verify.
    assert_eq!(
        report.verified(),
        report.total(),
        "every #1111 wired binding must FORMALLY verify (no solver-capacity pending expected)"
    );
}

/// FORMAL floor for the AArch64 16-byte scalar-pair aggregate eightbyte
/// placement proof (added 2026-06-23). The obligation discharges THROUGH the
/// symbolic byte-array memory model (store the two eightbytes at offsets 0/8,
/// re-load into X0/X1, assert reassembly), so it must verify FORMALLY via AY —
/// not merely statistically — with ZERO soundness failures. This pins that the
/// eightbyte→register placement and the `+8` offset are genuinely proven (a
/// wrong/swapped offset refutes), unlike the retracted degenerate pair identity.
#[test]
fn aggregate_placement_proofs_are_formally_verified() {
    if !formal_proof_test_enabled("aggregate_placement_proofs_are_formally_verified") {
        return;
    }

    let gate = GateConfig::strict_with_ay(AYConfig::default().with_timeout(60_000));
    require_formal_proof_toolchain(&gate, "aggregate-placement formal floor");

    // Both memory-model aggregate-placement proofs: GPR scalar-pair (X0/X1) and
    // FP HFA lanes (S0..S3). Each discharges THROUGH the symbolic byte-array.
    let wanted: &[&str] = &[
        "16-byte aggregate scalar-pair eightbyte placement",
        "4xF32 HFA lane placement",
    ];
    let full = ProofDatabase::new();
    let all = full.all();
    let subset: Vec<_> = wanted
        .iter()
        .map(|want| {
            all.iter()
                .find(|p| p.obligation.name.contains(want))
                .unwrap_or_else(|| {
                    panic!("aggregate placement proof {want:?} resolves to NO registered proof")
                })
                .clone()
        })
        .collect();
    let db = ProofDatabase::from_proofs(subset);

    let report = match gate.discharge(&db) {
        Ok(report) => report,
        Err(GateError::NotAllVerified(report)) => report,
        Err(e) => panic!("aggregate-placement gate errored: {e}"),
    };

    let soundness = report.soundness_failures();
    assert!(
        soundness.is_empty(),
        "AGGREGATE-PLACEMENT SOUNDNESS FAILURE: {} obligation(s) AY DISPROVED or could not run:\n{}",
        soundness.len(),
        soundness
            .iter()
            .map(|r| format!("  [{:?}] {} -- {}", r.category, r.name, r.detail()))
            .collect::<Vec<_>>()
            .join("\n"),
    );
    assert_no_statistical_fallback(&report);
    assert_eq!(
        report.verified(),
        report.total(),
        "both aggregate placement proofs (scalar-pair + HFA) must FORMALLY verify via AY"
    );
}

/// FORMAL floor for the AArch64 Mach-O DATA relocation selection proofs
/// (ARM64_RELOC_PAGE21 / ARM64_RELOC_PAGEOFF12 for the local global read,
/// ARM64_RELOC_GOT_LOAD_PAGE21 / ARM64_RELOC_GOT_LOAD_PAGEOFF12 for the
/// function-pointer / extern-symbol GOT load, ARM64_RELOC_UNSIGNED in both its
/// extern abs64 form — compact-unwind / FDE / TLS-descriptor / data slots —
/// and its section-based DWARF-debug rebase form, and the
/// ARM64_RELOC_SUBTRACTOR+UNSIGNED difference pair) added for symbolic
/// data-relocation emission on aarch64-apple-darwin. These obligations encode
/// the LINKER-applied + runtime ADRP/ADD/LDR page arithmetic (resp. the
/// linker's in-place slot application) and assert it equals the intended
///   address (`S + A` for the global / abs64 slot, `G + A` — the GOT slot
///   address — for the GOT rows, `SectFinal + off` for the section-based
///   rebase, `(A + ADDEND) - B` for the difference pair), so they must verify
///   FORMALLY via AY (not merely statistically) with ZERO soundness failures.
///   A wrong relocation row miscompiles EVERY global / fn-pointer access — the
///   cardinal sin — so this pins that each row form is genuinely proven. The
///   negative controls (each row with the wrong r_pcrel / a missing section
///   base / swapped SUBTRACTOR operand roles) must be REFUTED by AY, witnessing
///   that the positive proofs are real equivalences and not tautologies.
#[test]
fn aarch64_macho_data_reloc_proofs_are_formally_verified() {
    if !formal_proof_test_enabled("aarch64_macho_data_reloc_proofs_are_formally_verified") {
        return;
    }

    use trust_cg_verify::aarch64_macho_data_reloc_proofs::{
        aarch64_macho_data_relocation_negative_controls, aarch64_macho_data_relocation_proofs,
    };
    use trust_cg_verify::ay_bridge::{AYResult, verify_with_ay};
    use trust_cg_verify::proof_database::CategorizedProof;

    let gate = GateConfig::strict_with_ay(AYConfig::default().with_timeout(60_000));
    require_formal_proof_toolchain(&gate, "AArch64 Mach-O data-reloc formal floor");

    // (a) The 7 positive obligations must FORMALLY verify through the strict gate
    //     (resolved by name from the registered ProofDatabase — confirms they are
    //     actually wired into the DB the coverage gate consumes).
    let wanted: &[&str] = &[
        "ARM64_RELOC_PAGE21 ADRP == page(S+A)",
        "ARM64_RELOC_PAGEOFF12 ADRP+ADD == S+A",
        "ARM64_RELOC_GOT_LOAD_PAGE21 ADRP == page(G+A)",
        "ARM64_RELOC_GOT_LOAD_PAGEOFF12 ADRP+LDR == G+A",
        "ARM64_RELOC_UNSIGNED == S + A (extern abs64 pointer slot)",
        "SECTION-BASED ARM64_RELOC_UNSIGNED rebase == SectFinal + off",
        "ARM64_RELOC_SUBTRACTOR(B)+UNSIGNED(A) == A - B",
    ];
    let full = ProofDatabase::new();
    let all = full.all();
    let subset: Vec<CategorizedProof> = wanted
        .iter()
        .map(|want| {
            all.iter()
                .find(|p| p.obligation.name.contains(want))
                .unwrap_or_else(|| {
                    panic!(
                        "AArch64 Mach-O data-reloc proof {want:?} resolves to NO registered proof"
                    )
                })
                .clone()
        })
        .collect();
    assert_eq!(
        subset.len(),
        wanted.len(),
        "every AArch64 Mach-O data-reloc proof must resolve to exactly one registered obligation"
    );
    let db = ProofDatabase::from_proofs(subset);
    let report = match gate.discharge(&db) {
        Ok(report) => report,
        Err(GateError::NotAllVerified(report)) => report,
        Err(e) => panic!("AArch64 Mach-O data-reloc gate errored: {e}"),
    };
    let soundness = report.soundness_failures();
    assert!(
        soundness.is_empty(),
        "AARCH64 MACHO DATA-RELOC SOUNDNESS FAILURE: {} obligation(s) AY DISPROVED or could not run:\n{}",
        soundness.len(),
        soundness
            .iter()
            .map(|r| format!("  [{:?}] {} -- {}", r.category, r.name, r.detail()))
            .collect::<Vec<_>>()
            .join("\n"),
    );
    assert_no_statistical_fallback(&report);
    assert_eq!(
        report.verified(),
        report.total(),
        "all AArch64 Mach-O data-reloc proofs (PAGE21 + PAGEOFF12 + GOT_LOAD_PAGE21 + \
         GOT_LOAD_PAGEOFF12 + extern UNSIGNED + section-based UNSIGNED rebase + \
         SUBTRACTOR+UNSIGNED pair) must FORMALLY verify via AY"
    );

    // (b) Soundness witness: each NEGATIVE control (a malformed relocation row
    //     with the wrong r_pcrel) must be REFUTED by AY.
    let config = AYConfig::default().with_timeout(60_000);
    for obligation in aarch64_macho_data_relocation_negative_controls() {
        let result = verify_with_ay(&obligation, &config);
        assert!(
            matches!(result, AYResult::CounterExample(_)),
            "AArch64 Mach-O data-reloc NEGATIVE control '{}' returned {}; \
             a wrong encoding must produce a CounterExample",
            obligation.name,
            result
        );
    }

    // (c) Sanity: the public positive-proof list is exactly the 7 we discharged.
    assert_eq!(aarch64_macho_data_relocation_proofs().len(), 7);
}

/// FORMAL floor for the AArch64 Mach-O CALL (BRANCH26) relocation proof added for
/// symbolic direct-call emission on aarch64-apple-darwin. The obligation encodes
/// the LINKER-applied + runtime PC-relative branch displacement and asserts it
/// equals the intended call target `S + A`, so it must verify FORMALLY via AY (not
/// merely statistically) with ZERO soundness failures. A wrong call-relocation row
/// miscompiles EVERY direct extern call (drop's `__rust_dealloc`,
/// `_Unwind_Resume`/personality) — so this pins the formal-evidence lane. It does
/// not promote the production inventory row; the negative control (a BRANCH26
/// with the wrong r_pcrel, i.e. an absolute row) must be REFUTED by AY.
#[test]
fn aarch64_macho_call_reloc_proofs_are_formally_verified() {
    if !formal_proof_test_enabled("aarch64_macho_call_reloc_proofs_are_formally_verified") {
        return;
    }

    use trust_cg_verify::aarch64_macho_call_reloc_proofs::{
        aarch64_macho_call_relocation_negative_controls, aarch64_macho_call_relocation_proofs,
    };
    use trust_cg_verify::ay_bridge::{AYResult, verify_with_ay};

    let gate = GateConfig::strict_with_ay(AYConfig::default().with_timeout(60_000));
    require_formal_proof_toolchain(&gate, "AArch64 Mach-O call-reloc formal floor");

    // (a) The positive obligation must FORMALLY verify through the strict gate,
    //     resolved by name from the registered ProofDatabase (confirms it is wired
    //     into the DB the coverage gate consumes).
    let want = "ARM64_RELOC_BRANCH26 BL == S+A";
    let full = ProofDatabase::new();
    let all = full.all();
    let found = all
        .iter()
        .find(|p| p.obligation.name.contains(want))
        .unwrap_or_else(|| {
            panic!("AArch64 Mach-O call-reloc proof {want:?} resolves to NO registered proof")
        });
    let db = ProofDatabase::from_proofs(vec![found.clone()]);
    let report = match gate.discharge(&db) {
        Ok(report) => report,
        Err(GateError::NotAllVerified(report)) => report,
        Err(e) => panic!("AArch64 Mach-O call-reloc gate errored: {e}"),
    };
    let soundness = report.soundness_failures();
    assert!(
        soundness.is_empty(),
        "AARCH64 MACHO CALL-RELOC SOUNDNESS FAILURE: {} obligation(s) AY DISPROVED or could not run:\n{}",
        soundness.len(),
        soundness
            .iter()
            .map(|r| format!("  [{:?}] {} -- {}", r.category, r.name, r.detail()))
            .collect::<Vec<_>>()
            .join("\n"),
    );
    assert_no_statistical_fallback(&report);
    assert_eq!(
        report.verified(),
        report.total(),
        "the AArch64 Mach-O BRANCH26 call-reloc proof must FORMALLY verify via AY"
    );

    // (b) Soundness witness: the NEGATIVE control (an absolute, wrong-r_pcrel
    //     BRANCH26 row) must be REFUTED by AY.
    let config = AYConfig::default().with_timeout(60_000);
    for obligation in aarch64_macho_call_relocation_negative_controls() {
        let result = verify_with_ay(&obligation, &config);
        assert!(
            matches!(result, AYResult::CounterExample(_)),
            "AArch64 Mach-O call-reloc NEGATIVE control '{}' returned {}; \
             a wrong (absolute) encoding must produce a CounterExample",
            obligation.name,
            result
        );
    }

    // (c) Sanity: the public positive-proof list is exactly the 1 we discharged.
    assert_eq!(aarch64_macho_call_relocation_proofs().len(), 1);
}

/// FORMAL floor for the AArch64 Mach-O TLVP (thread-local descriptor) relocation
/// proofs added for the Darwin TLV-descriptor access on aarch64-apple-darwin.
/// These obligations encode the LINKER-applied + runtime ADRP/LDR page arithmetic
/// for the `ARM64_RELOC_TLVP_LOAD_PAGE21` / `ARM64_RELOC_TLVP_LOAD_PAGEOFF12`
/// rows and assert it equals the intended `tlv_descriptor` slot address `D + A`,
/// so they must verify FORMALLY via AY (not merely statistically) with ZERO
/// soundness failures. The negative controls (a TLVP PAGE21 with the wrong
/// r_pcrel, a TLVP PAGEOFF12 with the wrong r_pcrel) must be REFUTED by AY,
/// witnessing the positive proofs are real equivalences and not tautologies.
///
/// NOTE: these proofs certify the relocation ADDRESS ARITHMETIC. The FULL Darwin
/// TLV access is now ALSO emitted by the backend (the `select_tls_ref` TLV
/// sequence — ADRP/LDR to the `tlv_descriptor`, load the thunk, `BLR` through it —
/// plus the `__thread_data`/`__thread_vars` section emission with the
/// `__tlv_bootstrap`/init `ARM64_RELOC_UNSIGNED` relocations), verified
/// end-to-end by link+run
/// (`e2e_aarch64_thread_local_read_is_correct_and_per_thread`). Those are formal
/// evidence and regression coverage, not production Certified authority: this
/// floor pins the page+pageoff arithmetic only. The production relocation
/// registry stays empty until an independently checked gate report is bound to
/// the exact emitted object.
#[test]
fn aarch64_macho_tlvp_reloc_proofs_are_formally_verified() {
    if !formal_proof_test_enabled("aarch64_macho_tlvp_reloc_proofs_are_formally_verified") {
        return;
    }

    use trust_cg_verify::aarch64_macho_tlvp_reloc_proofs::{
        aarch64_macho_tlvp_relocation_negative_controls, aarch64_macho_tlvp_relocation_proofs,
    };
    use trust_cg_verify::ay_bridge::{AYResult, verify_with_ay};
    use trust_cg_verify::proof_database::CategorizedProof;

    let gate = GateConfig::strict_with_ay(AYConfig::default().with_timeout(60_000));
    require_formal_proof_toolchain(&gate, "AArch64 Mach-O TLVP-reloc formal floor");

    // (a) The 2 positive obligations must FORMALLY verify through the strict gate
    //     (resolved by name from the registered ProofDatabase — confirms they are
    //     actually wired into the DB the coverage gate consumes).
    let wanted: &[&str] = &[
        "ARM64_RELOC_TLVP_LOAD_PAGE21 ADRP == page(D+A)",
        "ARM64_RELOC_TLVP_LOAD_PAGEOFF12 ADRP+LDR == D+A",
    ];
    let full = ProofDatabase::new();
    let all = full.all();
    let subset: Vec<CategorizedProof> = wanted
        .iter()
        .map(|want| {
            all.iter()
                .find(|p| p.obligation.name.contains(want))
                .unwrap_or_else(|| {
                    panic!(
                        "AArch64 Mach-O TLVP-reloc proof {want:?} resolves to NO registered proof"
                    )
                })
                .clone()
        })
        .collect();
    assert_eq!(
        subset.len(),
        wanted.len(),
        "every AArch64 Mach-O TLVP-reloc proof must resolve to exactly one registered obligation"
    );
    let db = ProofDatabase::from_proofs(subset);
    let report = match gate.discharge(&db) {
        Ok(report) => report,
        Err(GateError::NotAllVerified(report)) => report,
        Err(e) => panic!("AArch64 Mach-O TLVP-reloc gate errored: {e}"),
    };
    let soundness = report.soundness_failures();
    assert!(
        soundness.is_empty(),
        "AARCH64 MACHO TLVP-RELOC SOUNDNESS FAILURE: {} obligation(s) AY DISPROVED or could not run:\n{}",
        soundness.len(),
        soundness
            .iter()
            .map(|r| format!("  [{:?}] {} -- {}", r.category, r.name, r.detail()))
            .collect::<Vec<_>>()
            .join("\n"),
    );
    assert_no_statistical_fallback(&report);
    assert_eq!(
        report.verified(),
        report.total(),
        "both AArch64 Mach-O TLVP-reloc proofs (TLVP_LOAD_PAGE21 + TLVP_LOAD_PAGEOFF12) must FORMALLY verify via AY"
    );

    // (b) Soundness witness: each NEGATIVE control (a malformed TLVP relocation
    //     row with the wrong r_pcrel) must be REFUTED by AY.
    let config = AYConfig::default().with_timeout(60_000);
    for obligation in aarch64_macho_tlvp_relocation_negative_controls() {
        let result = verify_with_ay(&obligation, &config);
        assert!(
            matches!(result, AYResult::CounterExample(_)),
            "AArch64 Mach-O TLVP-reloc NEGATIVE control '{}' returned {}; \
             a wrong encoding must produce a CounterExample",
            obligation.name,
            result
        );
    }

    // (c) Sanity: the public positive-proof list is exactly the 2 we discharged.
    assert_eq!(aarch64_macho_tlvp_relocation_proofs().len(), 2);
}

/// FORMAL evidence lane for the AArch64 ELF TLS local-exec (TLSLE) relocation
/// obligations. These obligations encode the LINKER-patched +
/// runtime ADD arithmetic for the `R_AARCH64_TLSLE_ADD_TPREL_HI12` (first ADD,
/// `LSL #12`) / `R_AARCH64_TLSLE_ADD_TPREL_LO12_NC` (second ADD) rows and assert
/// the `MRS; ADD; ADD` local-exec sequence reconstructs the thread-local address
/// `TP + TPREL(S+A)`, so they must verify FORMALLY via AY (not merely
/// statistically) with ZERO soundness failures. A wrong bit-field placement /
/// dropped `LSL #12` / dropped ABI range check miscompiles EVERY local-exec
/// thread-local access — so this pins the two TLSLE rows (and the two TLSIE
/// GOT-indirect rows, whose wrong page/scale/alignment likewise miscompiles
/// every initial-exec access) as solver-backed formal evidence. They do not
/// promote production Certified inventory rows: AY is in this lane's trusted
/// computing base, and the current inventory cannot represent that authority
/// distinction or bind this report to an emitted object. The negative controls
/// (dropped `LSL #12`, wrong low slice,
/// missing range check, dropped PC-page subtraction, dropped slot alignment)
/// must be REFUTED by AY.
#[test]
fn aarch64_elf_tls_reloc_proofs_are_formally_verified() {
    if !formal_proof_test_enabled("aarch64_elf_tls_reloc_proofs_are_formally_verified") {
        return;
    }

    use trust_cg_verify::aarch64_elf_tls_reloc_proofs::{
        aarch64_elf_tls_relocation_negative_controls, aarch64_elf_tls_relocation_proofs,
    };
    use trust_cg_verify::ay_bridge::{AYResult, verify_with_ay};
    use trust_cg_verify::proof_database::CategorizedProof;

    let gate = GateConfig::strict_with_ay(AYConfig::default().with_timeout(60_000));
    require_formal_proof_toolchain(&gate, "AArch64 ELF TLSLE-reloc formal floor");

    // (a) The 5 positive obligations must FORMALLY verify through the strict gate
    //     (resolved by name from the registered ProofDatabase — confirms they are
    //     actually wired into the DB the coverage gate consumes).
    let wanted: &[&str] = &[
        "R_AARCH64_TLSLE_ADD_TPREL_HI12 ADD(LSL#12)",
        "R_AARCH64_TLSLE_ADD_TPREL_LO12_NC ADD;ADD",
        "TLSLE local-exec MRS;ADD;ADD == TP + TPREL(S+A)",
        "R_AARCH64_TLSIE_ADR_GOTTPREL_PAGE21 ADRP == page(G+A)",
        "R_AARCH64_TLSIE_LD64_GOTTPREL_LO12_NC ADRP+LDR == G+A",
    ];
    let full = ProofDatabase::new();
    let all = full.all();
    let subset: Vec<CategorizedProof> = wanted
        .iter()
        .map(|want| {
            all.iter()
                .find(|p| p.obligation.name.contains(want))
                .unwrap_or_else(|| {
                    panic!("AArch64 ELF TLSLE-reloc proof {want:?} resolves to NO registered proof")
                })
                .clone()
        })
        .collect();
    assert_eq!(
        subset.len(),
        wanted.len(),
        "every AArch64 ELF TLSLE-reloc proof must resolve to exactly one registered obligation"
    );
    let db = ProofDatabase::from_proofs(subset);
    let report = match gate.discharge(&db) {
        Ok(report) => report,
        Err(GateError::NotAllVerified(report)) => report,
        Err(e) => panic!("AArch64 ELF TLSLE-reloc gate errored: {e}"),
    };
    let soundness = report.soundness_failures();
    assert!(
        soundness.is_empty(),
        "AARCH64 ELF TLSLE-RELOC SOUNDNESS FAILURE: {} obligation(s) AY DISPROVED or could not run:\n{}",
        soundness.len(),
        soundness
            .iter()
            .map(|r| format!("  [{:?}] {} -- {}", r.category, r.name, r.detail()))
            .collect::<Vec<_>>()
            .join("\n"),
    );
    assert_no_statistical_fallback(&report);
    assert_eq!(
        report.verified(),
        report.total(),
        "all AArch64 ELF TLS-reloc proofs (TLSLE HI12 + LO12_NC + exact-address-under-range, \
         TLSIE GOTTPREL page + slot address) must FORMALLY verify via AY"
    );

    // (b) Soundness witness: each NEGATIVE control (dropped LSL#12, wrong low
    //     slice, missing ABI range check) must be REFUTED by AY.
    let config = AYConfig::default().with_timeout(60_000);
    for obligation in aarch64_elf_tls_relocation_negative_controls() {
        let result = verify_with_ay(&obligation, &config);
        assert!(
            matches!(result, AYResult::CounterExample(_)),
            "AArch64 ELF TLSLE-reloc NEGATIVE control '{}' returned {}; \
             a wrong encoding / dropped range check must produce a CounterExample",
            obligation.name,
            result
        );
    }

    // (c) Sanity: the public positive-proof list is exactly the 5 we discharged
    //     (3 TLSLE + 2 TLSIE).
    assert_eq!(aarch64_elf_tls_relocation_proofs().len(), 5);
}

/// FORMAL floor for the fused `ADRP + LDR/STR #:lo12:` rows
/// (`R_AARCH64_LDST{8,16,32,64,128}_ABS_LO12_NC`). The five registered
/// positives must verify through the strict AY + Clean gate under their
/// access-size alignment precondition, and each negative control (a dropped
/// alignment precondition, or the byte field scaled as a halfword) must be
/// REFUTED by AY.
#[test]
fn aarch64_elf_ldst_lo12_rows_are_formally_verified() {
    if !formal_proof_test_enabled("aarch64_elf_ldst_lo12_rows_are_formally_verified") {
        return;
    }
    on_large_stack(|| {
        use trust_cg_verify::aarch64_elf_reloc_proofs::aarch64_elf_ldst_lo12_negative_controls;
        use trust_cg_verify::ay_bridge::{AYResult, verify_with_ay};

        let gate = GateConfig::strict_with_ay(AYConfig::default().with_timeout(60_000));
        require_formal_proof_toolchain(&gate, "AArch64 ELF LDST lo12 formal floor");

        // Soundness witnesses first: each negative control must be REFUTED.
        let config = AYConfig::default().with_timeout(60_000);
        let controls = aarch64_elf_ldst_lo12_negative_controls();
        assert_eq!(controls.len(), 5);
        for obligation in controls {
            let result = verify_with_ay(&obligation, &config);
            assert!(
                matches!(result, AYResult::CounterExample(_)),
                "LDST lo12 NEGATIVE control '{}' returned {result}; a dropped alignment \
                 precondition or wrong field scale must produce a CounterExample",
                obligation.name
            );
        }

        let subset: Vec<_> = ProofDatabase::new()
            .all()
            .iter()
            .filter(|proof| {
                AARCH64_ELF_LDST_LO12_CORPUS_ADDITION.contains(&proof.obligation.name.as_str())
            })
            .cloned()
            .collect();
        assert_eq!(
            subset.len(),
            AARCH64_ELF_LDST_LO12_CORPUS_ADDITION.len(),
            "every LDST lo12 row must resolve to exactly one registered obligation"
        );
        let db = ProofDatabase::from_proofs(subset);
        let report = match gate.discharge(&db) {
            Ok(report) => report,
            Err(GateError::NotAllVerified(report)) => report,
            Err(error) => panic!("AArch64 ELF LDST lo12 gate errored: {error}"),
        };
        let soundness = report.soundness_failures();
        assert!(
            soundness.is_empty(),
            "AARCH64 ELF LDST LO12 SOUNDNESS FAILURE:\n{}",
            soundness
                .iter()
                .map(|r| format!("  [{:?}] {} -- {}", r.category, r.name, r.detail()))
                .collect::<Vec<_>>()
                .join("\n"),
        );
        assert_no_statistical_fallback(&report);
        assert_eq!(
            report.verified(),
            report.total(),
            "all five LDST lo12 rows must FORMALLY verify via AY:\n{}",
            report
                .failures()
                .iter()
                .map(|r| format!("  [{:?}] {} -- {}", r.category, r.name, r.detail()))
                .collect::<Vec<_>>()
                .join("\n")
        );
    });
}

/// FORMAL floor for the coroutine-suspend (yield) frame save/restore proofs. The
/// `Inst::CoroSuspend` lowering macro-expands to "store i64 next_state into
/// frame[state_slot]; return value". These obligations discharge THROUGH the
/// symbolic byte-array memory model (QF_ABV) — the state store at byte offset
/// `state_slot*8` reloads `next_state`, and the state store preserves the
/// independently-yielded return `value` (disjoint slot) — so they must verify
/// FORMALLY via AY (not merely statistically) with ZERO soundness failures. A
/// wrong store offset (`state_slot*4`) or an aliasing value placement REFUTES, so
/// this pins the suspend glue wires the resume-state and yielded value correctly.
#[test]
fn coroutine_frame_proofs_are_formally_verified() {
    if !formal_proof_test_enabled("coroutine_frame_proofs_are_formally_verified") {
        return;
    }

    use trust_cg_verify::ay_bridge::{AYResult, verify_with_ay};
    use trust_cg_verify::coroutine_frame_proofs::{
        all_coroutine_frame_proofs, coroutine_frame_negative_controls,
    };
    use trust_cg_verify::proof_database::CategorizedProof;

    let gate = GateConfig::strict_with_ay(AYConfig::default().with_timeout(60_000));
    require_formal_proof_toolchain(&gate, "coroutine-frame formal floor");

    // (a) The 2 positive obligations must FORMALLY verify through the strict gate
    //     (resolved by name from the registered ProofDatabase — confirms they are
    //     wired into the DB the coverage gate consumes).
    let wanted: &[&str] = &[
        "CoroSuspend: state store at frame[state_slot] (offset slot*8) reloads next_state",
        "CoroSuspend: state store preserves the yielded value (disjoint slot)",
    ];
    let full = ProofDatabase::new();
    let all = full.all();
    let subset: Vec<CategorizedProof> = wanted
        .iter()
        .map(|want| {
            all.iter()
                .find(|p| p.obligation.name.contains(want))
                .unwrap_or_else(|| {
                    panic!("coroutine-frame proof {want:?} resolves to NO registered proof")
                })
                .clone()
        })
        .collect();
    assert_eq!(
        subset.len(),
        wanted.len(),
        "every coroutine-frame proof must resolve to exactly one registered obligation"
    );
    let db = ProofDatabase::from_proofs(subset);
    let report = match gate.discharge(&db) {
        Ok(report) => report,
        Err(GateError::NotAllVerified(report)) => report,
        Err(e) => panic!("coroutine-frame gate errored: {e}"),
    };
    let soundness = report.soundness_failures();
    assert!(
        soundness.is_empty(),
        "COROUTINE-FRAME SOUNDNESS FAILURE: {} obligation(s) AY DISPROVED or could not run:\n{}",
        soundness.len(),
        soundness
            .iter()
            .map(|r| format!("  [{:?}] {} -- {}", r.category, r.name, r.detail()))
            .collect::<Vec<_>>()
            .join("\n"),
    );
    assert_no_statistical_fallback(&report);
    assert_eq!(
        report.verified(),
        report.total(),
        "both coroutine-frame proofs (state save + value independence) must FORMALLY verify via AY"
    );

    // (b) Soundness witness: each NEGATIVE control (a wrong store offset, an
    //     aliasing value placement) must be REFUTED by AY.
    let config = AYConfig::default().with_timeout(60_000);
    for obligation in coroutine_frame_negative_controls() {
        let result = verify_with_ay(&obligation, &config);
        assert!(
            matches!(result, AYResult::CounterExample(_)),
            "coroutine-frame NEGATIVE control '{}' returned {}; a wrong placement must \
             produce a CounterExample",
            obligation.name,
            result
        );
    }

    // (c) Sanity: the public positive-proof list is exactly the 2 we discharged.
    assert_eq!(all_coroutine_frame_proofs().len(), 2);
}

/// FORMAL floor for the Darwin aarch64 TLV thunk-call (indirect descriptor
/// resolver) proof. The emitted `select_tls_ref` Tlv sequence loads the resolver
/// from the materialized descriptor and invokes it with the descriptor address;
/// this obligation proves the emitted sequence passes the CORRECT descriptor
/// argument (the ADRP/LDR page+pageoff reconstruction of `D`) through the
/// argument-sensitive thunk model `thunk(arg) = arg + thunk_off`, so it must
/// verify FORMALLY via AY with ZERO soundness failures. The negative controls (a
/// wrong call argument `D+8`, a dropped indirection returning `D`) must be REFUTED
/// by AY, witnessing the positive proof is a real equivalence (not a tautology).
/// This complements the TLVP relocation lane (which proves the address arithmetic
/// that materializes `D`).
#[test]
fn aarch64_tlv_thunk_proof_is_formally_verified() {
    if !formal_proof_test_enabled("aarch64_tlv_thunk_proof_is_formally_verified") {
        return;
    }

    use trust_cg_verify::aarch64_tlv_thunk_proofs::{
        aarch64_tlv_thunk_negative_controls, aarch64_tlv_thunk_proofs,
    };
    use trust_cg_verify::ay_bridge::{AYResult, verify_with_ay};

    let gate = GateConfig::strict_with_ay(AYConfig::default().with_timeout(60_000));
    require_formal_proof_toolchain(&gate, "TLV thunk-call formal floor");

    // (a) The positive obligation must FORMALLY verify through the strict gate,
    //     resolved by name from the registered ProofDatabase.
    let want = "TLV thunk-call: emitted ADRP/LDR/LDR/BLR computes thunk(D) == &var";
    let full = ProofDatabase::new();
    let all = full.all();
    let found = all
        .iter()
        .find(|p| p.obligation.name.contains(want))
        .unwrap_or_else(|| panic!("TLV thunk-call proof {want:?} resolves to NO registered proof"));
    let db = ProofDatabase::from_proofs(vec![found.clone()]);
    let report = match gate.discharge(&db) {
        Ok(report) => report,
        Err(GateError::NotAllVerified(report)) => report,
        Err(e) => panic!("TLV thunk-call gate errored: {e}"),
    };
    let soundness = report.soundness_failures();
    assert!(
        soundness.is_empty(),
        "TLV THUNK-CALL SOUNDNESS FAILURE: {} obligation(s) AY DISPROVED or could not run:\n{}",
        soundness.len(),
        soundness
            .iter()
            .map(|r| format!("  [{:?}] {} -- {}", r.category, r.name, r.detail()))
            .collect::<Vec<_>>()
            .join("\n"),
    );
    assert_no_statistical_fallback(&report);
    assert_eq!(
        report.verified(),
        report.total(),
        "the TLV thunk-call proof must FORMALLY verify via AY"
    );

    // (b) Soundness witness: each NEGATIVE control (wrong call argument, missing
    //     indirection) must be REFUTED by AY.
    let config = AYConfig::default().with_timeout(60_000);
    for obligation in aarch64_tlv_thunk_negative_controls() {
        let result = verify_with_ay(&obligation, &config);
        assert!(
            matches!(result, AYResult::CounterExample(_)),
            "TLV thunk-call NEGATIVE control '{}' returned {}; a wrong indirection must \
             produce a CounterExample",
            obligation.name,
            result
        );
    }

    // (c) Sanity: the public positive-proof list is exactly the 1 we discharged.
    assert_eq!(aarch64_tlv_thunk_proofs().len(), 1);
}

/// FORMAL floor for the aarch64 LSDA EH call-site / catch-all dispatch encoding
/// proofs. For a `catch(...)` landing pad, the personality dispatches an in-range
/// exception to the landing pad ONLY with a POSITIVE type filter (match-any NULL
/// TType slot), and a PC past the half-open call-site range does NOT dispatch.
/// These obligations encode the personality's range/dispatch reconstruction and
/// must verify FORMALLY via AY with ZERO soundness failures. The negative controls
/// (a cleanup `type_filter=0` catch-all that does NOT dispatch, a closed-range
/// over-claim at the boundary) must be REFUTED by AY — witnessing the
/// catch-vs-cleanup type-filter distinction and the half-open range bound are
/// load-bearing (a wrong encoding silently drops the catch and terminates).
#[test]
fn aarch64_eh_lsda_proofs_are_formally_verified() {
    if !formal_proof_test_enabled("aarch64_eh_lsda_proofs_are_formally_verified") {
        return;
    }

    use trust_cg_verify::aarch64_eh_lsda_proofs::{
        aarch64_eh_lsda_negative_controls, aarch64_eh_lsda_proofs,
    };
    use trust_cg_verify::ay_bridge::{AYResult, verify_with_ay};
    use trust_cg_verify::proof_database::CategorizedProof;

    let gate = GateConfig::strict_with_ay(AYConfig::default().with_timeout(60_000));
    require_formal_proof_toolchain(&gate, "LSDA EH formal floor");

    // (a) The 2 positive obligations must FORMALLY verify through the strict gate.
    let wanted: &[&str] = &[
        "LSDA EH: catch(...) in-range dispatch lands on func_start+landing_pad",
        "LSDA EH: out-of-range PC (region end) does not dispatch (half-open range)",
    ];
    let full = ProofDatabase::new();
    let all = full.all();
    let subset: Vec<CategorizedProof> = wanted
        .iter()
        .map(|want| {
            all.iter()
                .find(|p| p.obligation.name.contains(want))
                .unwrap_or_else(|| panic!("LSDA EH proof {want:?} resolves to NO registered proof"))
                .clone()
        })
        .collect();
    assert_eq!(
        subset.len(),
        wanted.len(),
        "every LSDA EH proof must resolve to exactly one registered obligation"
    );
    let db = ProofDatabase::from_proofs(subset);
    let report = match gate.discharge(&db) {
        Ok(report) => report,
        Err(GateError::NotAllVerified(report)) => report,
        Err(e) => panic!("LSDA EH gate errored: {e}"),
    };
    let soundness = report.soundness_failures();
    assert!(
        soundness.is_empty(),
        "LSDA EH SOUNDNESS FAILURE: {} obligation(s) AY DISPROVED or could not run:\n{}",
        soundness.len(),
        soundness
            .iter()
            .map(|r| format!("  [{:?}] {} -- {}", r.category, r.name, r.detail()))
            .collect::<Vec<_>>()
            .join("\n"),
    );
    assert_no_statistical_fallback(&report);
    assert_eq!(
        report.verified(),
        report.total(),
        "both LSDA EH proofs (catch-all dispatch + out-of-range non-dispatch) must FORMALLY verify via AY"
    );

    // (b) Soundness witness: each NEGATIVE control (cleanup type-filter, closed
    //     range over-claim) must be REFUTED by AY.
    let config = AYConfig::default().with_timeout(60_000);
    for obligation in aarch64_eh_lsda_negative_controls() {
        let result = verify_with_ay(&obligation, &config);
        assert!(
            matches!(result, AYResult::CounterExample(_)),
            "LSDA EH NEGATIVE control '{}' returned {}; a wrong encoding must produce a \
             CounterExample",
            obligation.name,
            result
        );
    }

    // (c) Sanity: the public positive-proof list is exactly the 2 we discharged.
    assert_eq!(aarch64_eh_lsda_proofs().len(), 2);
}

/// FORMAL floor for the aarch64 LSDA EH call-site TABLE COVERAGE / PARTITION
/// proofs — the invariant the abstract dispatch proof
/// (`aarch64_eh_lsda_proofs_are_formally_verified`) ASSUMES and that
/// `resolve_eh_offsets` filler synthesis (pipeline.rs:6720-6802) establishes.
/// The resolved call-site table covers `[0, code_len)` EXACTLY ONCE (no gap =>
/// the personality never `std::terminate()`s on an in-flight PC; no overlap =>
/// `scan_eh_table` selects a single record), and an Invoke PC maps to a region
/// carrying the Invoke's own landing pad (not a filler's 0). These obligations
/// encode the reconstructed HEAD/explicit/TAIL table over a bounded `forall pc`
/// and MUST verify FORMALLY via AY with ZERO soundness failures and NO
/// statistical fallback. The negative controls (a dropped tail filler leaving a
/// gap; a zero-pad filler over the Invoke PC) MUST be REFUTED by AY — witnessing
/// the filler coverage and the explicit-region-pad-wins invariants are
/// load-bearing (the real cleanup-PC-terminate bug `resolve_eh_offsets` fixes).
#[test]
fn aarch64_eh_coverage_proofs_are_formally_verified() {
    if !formal_proof_test_enabled("aarch64_eh_coverage_proofs_are_formally_verified") {
        return;
    }

    use trust_cg_verify::aarch64_eh_coverage_proofs::{
        aarch64_eh_coverage_negative_controls, aarch64_eh_coverage_proofs,
    };
    use trust_cg_verify::ay_bridge::{AYResult, verify_with_ay};
    use trust_cg_verify::proof_database::CategorizedProof;

    let gate = GateConfig::strict_with_ay(AYConfig::default().with_timeout(60_000));
    require_formal_proof_toolchain(&gate, "LSDA EH coverage formal floor");

    // (a) The 2 positive obligations must FORMALLY verify through the strict gate.
    let wanted: &[&str] = &[
        "LSDA EH: resolved call-site table covers [0,code_len) exactly once (partition)",
        "LSDA EH: Invoke PC maps to region with the Invoke's landing pad (not 0)",
    ];
    let full = ProofDatabase::new();
    let all = full.all();
    let subset: Vec<CategorizedProof> = wanted
        .iter()
        .map(|want| {
            all.iter()
                .find(|p| p.obligation.name.contains(want))
                .unwrap_or_else(|| {
                    panic!("LSDA EH coverage proof {want:?} resolves to NO registered proof")
                })
                .clone()
        })
        .collect();
    assert_eq!(
        subset.len(),
        wanted.len(),
        "every LSDA EH coverage proof must resolve to exactly one registered obligation"
    );
    let db = ProofDatabase::from_proofs(subset);
    let report = match gate.discharge(&db) {
        Ok(report) => report,
        Err(GateError::NotAllVerified(report)) => report,
        Err(e) => panic!("LSDA EH coverage gate errored: {e}"),
    };
    let soundness = report.soundness_failures();
    assert!(
        soundness.is_empty(),
        "LSDA EH coverage SOUNDNESS FAILURE: {} obligation(s) AY DISPROVED or could not run:\n{}",
        soundness.len(),
        soundness
            .iter()
            .map(|r| format!("  [{:?}] {} -- {}", r.category, r.name, r.detail()))
            .collect::<Vec<_>>()
            .join("\n"),
    );
    assert_no_statistical_fallback(&report);
    assert_eq!(
        report.verified(),
        report.total(),
        "both LSDA EH coverage proofs (total coverage/partition + Invoke->pad mapping) must \
         FORMALLY verify via AY"
    );

    // (b) Soundness witness: each NEGATIVE control (dropped tail filler => gap;
    //     zero-pad filler over the Invoke PC => selects 0) must be REFUTED by AY.
    let config = AYConfig::default().with_timeout(60_000);
    for obligation in aarch64_eh_coverage_negative_controls() {
        let result = verify_with_ay(&obligation, &config);
        assert!(
            matches!(result, AYResult::CounterExample(_)),
            "LSDA EH coverage NEGATIVE control '{}' returned {}; a wrong table (gap / zero-pad \
             filler over an Invoke PC) must produce a CounterExample",
            obligation.name,
            result
        );
    }

    // (c) Sanity: the public positive-proof list is exactly the 2 we discharged.
    assert_eq!(aarch64_eh_coverage_proofs().len(), 2);
}

/// The AY this test binary executes, for the soundness gate's attestation
/// record: `scripts/soundness_attestation.py build` requires exactly one such
/// line in this target's log, admitted by the toolchain route, and binds its
/// SHA-256 to the `bin/ay` its preflight probed in the Trust package. It only
/// reports; the formal tests fail on their own when no AY is admitted.
#[test]
fn executed_ay_identity_is_reported() {
    match trust_cg_verify::ay_identity::resolve_for_process() {
        Ok(ay) => println!(
            "proof_gate_strict: executed-ay sha256={} route={} ay={}",
            ay.sha256(),
            ay.route().as_str(),
            ay.path().display()
        ),
        Err(refusal) => println!("proof_gate_strict: executed-ay unresolved: {refusal}"),
    }
}

/// FORMAL floor for the #67 checked-overflow DETECTION obligations, at HONEST
/// per-strength granularity (ZERO soundness failures everywhere):
///   - the 4 add/sub i64 obligations (AddsRR/SubsRR carriers) discharge FORMALLY
///     and fast via AY plus independent Clean checking — verified()==total();
///   - the 2 mul i64 obligations carry a GENUINE (non-degenerate) 64-bit
///     equivalence theorem that is SMT-hard (128-bit bvmul) — every non-verified
///     one is SolverCapacity PENDING (timeout/unknown), NEVER a 64-bit formal
///     claim and NEVER a counterexample;
///   - the 2 width-8 mul-equivalence anchors discharge FORMALLY at width-8,
///     witnessing the honest "exhaustive/formal at w=8, 64-bit pending" claim
///     that backs the Smulh/Umulh allowlist reason.
///     All obligations are asserted structurally non-degenerate (X != X-side). The
///     AY is the one `trust_cg_verify::ay_identity` admits: the `bin/ay` of the
///     Trust toolchain that built this test, by the SHA-256 recorded at build
///     time. Testing a different AY build means building with the toolchain that
///     ships it; `AY_SOLVER_PATH` can only name another copy of those bytes.
#[test]
fn wired_checked_overflow_bindings_are_formally_verified() {
    if !formal_proof_test_enabled("wired_checked_overflow_bindings_are_formally_verified") {
        return;
    }

    use trust_cg_verify::proof_database::CategorizedProof;

    // HONEST per-strength split (#67). Each obligation packs `overflow_b1 ::
    // value_iN` and models the real AArch64 flag predicate; all are
    // non-degenerate (trust_ir_expr != aarch64_expr).
    //
    //  - FORMAL_NAMES: the 4 add/sub i64 obligations. These discharge FORMALLY
    //    via ay and fast (no multiply hardness) — they MUST verify==total.
    //  - MUL_I64_NAMES: the 2 mul i64 obligations. The genuine 64-bit
    //    equivalence theorem is SMT-hard (128-bit bvmul times out). They carry
    //    ZERO soundness failures, but their FORMAL discharge is capacity-pending
    //    — we EXPECT them in FailureClass::SolverCapacity and do NOT claim a
    //    64-bit formal proof.
    //  - MUL_I8_ANCHOR_NAMES: the 2 width-8 mul-equivalence proofs. These are the
    //    HONEST mul evidence and MUST formally verify at width-8.
    let formal_names: &[&str] = &[
        "CheckedSadd_I64 -> ADDS+CSET_VS",
        "CheckedSsub_I64 -> SUBS+CSET_VS",
        "CheckedUadd_I64 -> ADDS+CSET_HS",
        "CheckedUsub_I64 -> SUBS+CSET_LO",
    ];
    let mul_i64_names: &[&str] = &[
        "CheckedSmul_I64 -> MUL+SMULH+ASR+CMP+CSET_NE",
        "CheckedUmul_I64 -> MUL+UMULH+CMP0+CSET_NE",
    ];
    let mul_i8_anchor_names: &[&str] = &[
        "CheckedSmul_I8 exact product overflow",
        "CheckedUmul_I8 exact product overflow",
    ];

    let gate = GateConfig::strict_with_ay(AYConfig::default().with_timeout(60_000));
    require_formal_proof_toolchain(&gate, "#67 wired checked-overflow formal floor");

    let full = ProofDatabase::new();
    let all = full.all();
    let resolve = |want: &str| -> CategorizedProof {
        all.iter()
            .find(|p| p.obligation.name.contains(want))
            .unwrap_or_else(|| {
                panic!(
                    "#67 wired checked-overflow binding {want:?} resolves to NO registered proof"
                )
            })
            .clone()
    };

    // STRUCTURAL NON-DEGENERACY (f81e45b / X==X guard) over EVERY checked-overflow
    // obligation involved here — add/sub AND mul, i64 AND i8 — so an X==X can
    // never silently pass for any of them regardless of which gate binds them.
    for want in formal_names
        .iter()
        .chain(mul_i64_names)
        .chain(mul_i8_anchor_names)
    {
        let p = resolve(want);
        assert_ne!(
            p.obligation.trust_ir_expr, p.obligation.aarch64_expr,
            "#67 DEGENERATE (X==X) checked-overflow proof {want:?}: proves nothing"
        );
    }

    // (1) add/sub i64: MUST formally verify, verified()==total(), zero pending.
    let formal_subset: Vec<CategorizedProof> = formal_names.iter().map(|w| resolve(w)).collect();
    let formal_report = match gate.discharge(&ProofDatabase::from_proofs(formal_subset)) {
        Ok(report) => report,
        Err(GateError::NotAllVerified(report)) => report,
        Err(e) => panic!("#67 add/sub checked-overflow gate errored: {e}"),
    };
    assert!(
        formal_report.soundness_failures().is_empty(),
        "#67 ADD/SUB SOUNDNESS FAILURE: {}",
        formal_report
            .soundness_failures()
            .iter()
            .map(|r| format!("  [{:?}] {} -- {}", r.category, r.name, r.detail()))
            .collect::<Vec<_>>()
            .join("\n"),
    );
    assert_no_statistical_fallback(&formal_report);
    assert_eq!(
        formal_report.verified(),
        formal_report.total(),
        "every #67 add/sub checked-overflow binding MUST formally verify (they are not SMT-hard)"
    );

    // (2) mul i64: ZERO soundness failures, but FORMAL discharge is capacity-
    //     pending (timeout/unknown). We require NO counterexample, and that every
    //     non-verified mul is SolverCapacity PENDING — NOT a 64-bit formal claim.
    let mul_subset: Vec<CategorizedProof> = mul_i64_names.iter().map(|w| resolve(w)).collect();
    let mul_report = match gate.discharge(&ProofDatabase::from_proofs(mul_subset)) {
        Ok(report) => report,
        Err(GateError::NotAllVerified(report)) => report,
        Err(e) => panic!("#67 mul checked-overflow gate errored: {e}"),
    };
    assert!(
        mul_report.soundness_failures().is_empty(),
        "#67 MUL SOUNDNESS FAILURE (counterexample/error — NOT mere capacity): {}",
        mul_report
            .soundness_failures()
            .iter()
            .map(|r| format!("  [{:?}] {} -- {}", r.category, r.name, r.detail()))
            .collect::<Vec<_>>()
            .join("\n"),
    );
    assert_no_statistical_fallback(&mul_report);
    let mul_pending = mul_report.failures_in_class(FailureClass::SolverCapacity);
    // Every mul i64 that did not formally verify must be SolverCapacity PENDING
    // (timeout/unknown), never a silent pass. Empirically both time out, but we
    // tolerate a faster machine formally verifying them too — what we forbid is
    // counting them as a 64-bit formal claim when they are merely capacity-bound.
    assert_eq!(
        mul_report.verified() + mul_pending.len(),
        mul_report.total(),
        "#67 mul i64: every non-verified obligation must be SolverCapacity PENDING, \
         never a silent/non-formal pass"
    );

    // (3) width-8 mul-equivalence anchor: MUST formally verify.
    let anchor_subset: Vec<CategorizedProof> =
        mul_i8_anchor_names.iter().map(|w| resolve(w)).collect();
    let anchor_report = match gate.discharge(&ProofDatabase::from_proofs(anchor_subset)) {
        Ok(report) => report,
        Err(GateError::NotAllVerified(report)) => report,
        Err(e) => panic!("#67 width-8 mul-anchor gate errored: {e}"),
    };
    assert!(
        anchor_report.soundness_failures().is_empty(),
        "#67 WIDTH-8 MUL-ANCHOR SOUNDNESS FAILURE: {}",
        anchor_report
            .soundness_failures()
            .iter()
            .map(|r| format!("  [{:?}] {} -- {}", r.category, r.name, r.detail()))
            .collect::<Vec<_>>()
            .join("\n"),
    );
    assert_no_statistical_fallback(&anchor_report);
    assert_eq!(
        anchor_report.verified(),
        anchor_report.total(),
        "the width-8 mul-equivalence anchor MUST formally verify (exhaustive/formal at w=8)"
    );
}

// ===========================================================================
// UNIVERSAL NON-DEGENERACY GATE (Strategy C, task #53)
// ===========================================================================
//
// Generalizes the per-family `assert_ne` guards (the #67 checked-overflow
// family above, and the RISC-V comparison idioms in coverage_gate_tests.rs)
// to EVERY proof in `ProofDatabase::new()`.
//
// A lowering proof whose `trust_ir_expr` is STRUCTURALLY identical to its
// machine (`aarch64_expr`) side (`SmtExpr` derives `PartialEq`) proves nothing
// — the f81e45b X==X lie — UNLESS the lowering genuinely IS a 1:1 identity
// built by INDEPENDENT encoders (e.g. `Iadd -> ADD`: both independently denote
// `bvadd`; a wrong opcode `Iadd -> SUB` would yield `bvadd == bvsub` and
// refute). Those audited genuine identities live on
// `GENUINE_IDENTITY_ALLOWLIST`; the audited SUSPICIOUS self-equalities that
// still need a faithful re-derivation live on the SHRINKING debt ledger
// `KNOWN_DEGENERATE_PENDING_FIX` (which is NOT a genuineness claim).
//
// The gate is FAIL-CLOSED: a degenerate proof on NEITHER list is a violation
// and FAILS the build, so a FUTURE degenerate proof can never silently
// register.

/// Pinned length of the genuine-identity allowlist. Bump deliberately ONLY when
/// a new audited genuine 1:1 identity lowering is added (and never to silence a
/// suspicious self-equality — those go on the debt ledger, or better, get
/// fixed).
///
/// HONESTY (task #61): lowered 461 -> 433. The auditor found 28 MIS-FILED entries
/// that were never genuine independent-encoder identities — the 16 CAS/atomic-RMW
/// "returns old value" self-equalities (both sides via `encode_load_le` => X==X)
/// and the 12 scalar shift proofs (`bvshl==bvshl` / `bvlshr==bvlshr` /
/// `bvashr==bvashr`; the #57 precondition is added identically to both sides and
/// is cosmetic). They were moved to the DEBT ledger below, where they belong.
// +6 (2026-06-27): the AArch64 FRINT round-to-integral family — Ffloor/Fceil/
// Ftrunc x {F32,F64} -> FRINTM/FRINTP/FRINTZ. Single-instruction 1:1 identities
// in the same audited category as Fneg/Fabs/Fsqrt (machine side opcode-keyed via
// encode_frint{m,p,z}); on-host execution proves the lowerings bit-exact.
// -20 (2026-06-28): the scalar-FP gap closure made encode_fcmp FAITHFUL (FCMP→
// NZCV then CSET reading from_floatcc(cond), via the nzcv flag table). The 20
// Fcmp conditions whose CSET flag-reading is STRUCTURALLY DISTINCT from the
// source predicate — GE/GT/LE/Ord and ALL the Unordered-* forms x {F32,F64} —
// became GENUINELY PROVEN (no longer X==X) and were removed from the allowlist.
// Only the 8 that read a single flag equal to the source (Eq/NE/LT/Uno x
// {F32,F64}) remain as audited 1:1 identities.
// +1 (419 -> 420): SLICE 3 -- "x86_64: SeqCst fence -> MFENCE single-thread
// identity". MFENCE's single-thread semantics IS the (register, memory) identity
// (writes no register / no memory), so its faithful obligation is necessarily
// structurally degenerate -- the same audited class as AtomicLoad/reg-reg copy,
// witnessed non-vacuous by refuting clobber-register / clobber-memory negative
// controls. NOT the retracted #62 encoding tautology.
// +2 (420 -> 422): the Faulhaber closed-form BASE CASES "ClosedForm: sum_i m=1"
// and "ClosedForm: sum_i2 m=1" (9736a62 registered them unclassified and the
// non-degeneracy gate correctly FIRED red). At m=1 both sides fold to `x + 0`,
// structurally X==X -- but only because s1_of(1)/s2_of(1) are CORRECT (a wrong
// constant would have produced distinct sides and refuted at registration);
// the m>=2 siblings carry the family's genuine refutability. Audited-genuine,
// same footing as the MFENCE / AtomicLoad identities.
// -2 (422 -> 420): the two Faulhaber m=1 base cases were RETRACTED from the
// allowlist because their obligations are now GENUINELY non-degenerate. The
// closed-form side of `proof_sum_i`/`proof_sum_i2` is now the EXPRESSION TREE
// `s1_expr`/`s2_expr` (`m(m-1)/2`, `m(m-1)(2m-1)/6`) instead of a pre-folded
// constant, so even at m=1 (`x + (1·0 >> 1)`) it is structurally distinct from
// the loop fold and refutes a wrong closed form -- it no longer belongs on the
// degenerate-identity allowlist.
// -4 (420 -> 416): Sdiv_I32/I64 -> SDIVWrr/Xrr and Udiv_I32/I64 -> UDIVWrr/Xrr
// removed 2026-07-12. Their AArch64 division-lowering proofs are no longer
// degenerate (a genuine machine model, not an X==X identity), so the four
// identity exemptions were DEAD and masking a possible regression per
// genuine_allowlist_is_tight_and_live. Coverage of those opcodes still holds
// through the now-genuine proofs.
// -2 (416 -> 414): ordered AArch64 Fcmp_NE_F32/F64 now have an explicit NaN
// guard, so their non-degenerate obligations no longer qualify for exemptions.
// -2 (414 -> 412): FABS F32/F64 compare full symbolic input masks with
// independently encoded register slices; neither is an identity obligation.
const GENUINE_ALLOWLIST_LEN: usize = 412;

/// Pinned UPPER BOUND on the known-degenerate debt ledger. This is a RATCHET:
/// the ledger may only SHRINK as suspicious proofs are given faithful
/// independent-encoder obligations (task #53 follow-up). It must NEVER grow to
/// admit a NEW degenerate proof — fix the proof instead.
///
/// HONESTY (task #61): raised 440 -> 468 ONCE, to absorb a RECLASSIFICATION
/// (not new debt) of 28 mis-filed entries removed from GENUINE_IDENTITY_ALLOWLIST.
///
/// CAPSTONE (task #62): lowered 468 -> 0. Every degenerate-debt proof has now been
/// RETRACTED — the non-lowering vacuous families were DELETED from the proof
/// builders, and the reconstruction-superseded static lowerings were removed
/// because operand reconstruction is the genuine coverage. The debt ledger is
/// EMPTY: the database contains zero degenerate-debt proofs. The ratchet now pins
/// it at zero — a new degenerate proof can never be admitted; it must be given a
/// faithful independent-encoder obligation instead.
const DEBT_LEDGER_MAX_LEN: usize = 0;

/// THE universal non-degeneracy gate. Iterates EVERY registered proof and
/// requires each to be EITHER non-degenerate (`trust_ir_expr != aarch64_expr`,
/// so a wrong machine choice would refute) OR classified — on
/// `GENUINE_IDENTITY_ALLOWLIST` (audited genuine identity) or on the disclosed,
/// shrinking `KNOWN_DEGENERATE_PENDING_FIX` debt ledger. An unclassified
/// degenerate proof FAILS (fail-closed).
#[test]
fn universal_non_degeneracy_gate() {
    let violations = on_large_stack(|| {
        ProofDatabase::new()
            .non_degeneracy_violations()
            .into_iter()
            .map(|v| v.name)
            .collect::<Vec<_>>()
    });
    assert!(
        violations.is_empty(),
        "UNIVERSAL NON-DEGENERACY GATE FAILED (Strategy C, task #53): {} degenerate \
         proof(s) have trust_ir_expr STRUCTURALLY identical to their machine side and are \
         on NEITHER the audited GENUINE_IDENTITY_ALLOWLIST NOR the KNOWN_DEGENERATE_PENDING_FIX \
         debt ledger. A degenerate proof proves nothing (the f81e45b X==X lie) unless the \
         lowering is a genuine independent-encoder 1:1 identity. FIX each by giving it a \
         faithful independent machine-side obligation (so a wrong opcode/instruction/placement \
         refutes); do NOT add a self-equality to the genuine allowlist. Offending proofs:\n{}",
        violations.len(),
        violations.join("\n")
    );
}

/// The genuine allowlist must be TIGHT and LIVE: every name on it must be (a)
/// actually registered in the database and (b) actually degenerate. A name that
/// is non-degenerate (or absent) is a DEAD entry — it would mask a future
/// regression where that proof silently becomes a degenerate X==X yet still
/// "passes" because it is pre-allowlisted. Dead entries must be removed.
#[test]
fn genuine_allowlist_is_tight_and_live() {
    use std::collections::HashSet;
    let degen: HashSet<String> = on_large_stack(|| {
        ProofDatabase::new()
            .degenerate_proof_names()
            .into_iter()
            .collect()
    });

    assert_eq!(
        GENUINE_IDENTITY_ALLOWLIST.len(),
        GENUINE_ALLOWLIST_LEN,
        "GENUINE_IDENTITY_ALLOWLIST length changed; update GENUINE_ALLOWLIST_LEN \
         deliberately (only for a genuinely-audited new 1:1 identity)."
    );

    // No duplicate names within the allowlist.
    let unique: HashSet<&&str> = GENUINE_IDENTITY_ALLOWLIST.iter().collect();
    assert_eq!(
        unique.len(),
        GENUINE_IDENTITY_ALLOWLIST.len(),
        "GENUINE_IDENTITY_ALLOWLIST contains duplicate names"
    );

    let dead: Vec<&str> = GENUINE_IDENTITY_ALLOWLIST
        .iter()
        .copied()
        .filter(|n| !degen.contains(*n))
        .collect();
    assert!(
        dead.is_empty(),
        "GENUINE_IDENTITY_ALLOWLIST has {} DEAD entr(y/ies) — either not registered or no longer \
         degenerate (so the exemption is masking a possible regression). Remove them:\n{}",
        dead.len(),
        dead.join("\n")
    );
}

/// The debt ledger is a RATCHET that may only shrink, must be disjoint from the
/// genuine allowlist (a suspicious proof can never be silently reclassified as
/// genuine), and must be LIVE (every entry actually registered and degenerate).
#[test]
fn debt_ledger_is_disjoint_shrinking_and_live() {
    use std::collections::HashSet;
    let degen: HashSet<String> = on_large_stack(|| {
        ProofDatabase::new()
            .degenerate_proof_names()
            .into_iter()
            .collect()
    });

    assert!(
        KNOWN_DEGENERATE_PENDING_FIX.len() == DEBT_LEDGER_MAX_LEN,
        "KNOWN_DEGENERATE_PENDING_FIX GREW to {} (cap {}). The debt ledger is a fail-closed \
         RATCHET: it may only shrink as suspicious proofs are made non-degenerate. Raising the \
         cap to admit a new degenerate proof is forbidden — fix the proof instead.",
        KNOWN_DEGENERATE_PENDING_FIX.len(),
        DEBT_LEDGER_MAX_LEN
    );

    // No duplicates within the ledger.
    let ledger: HashSet<&&str> = KNOWN_DEGENERATE_PENDING_FIX.iter().collect();
    assert_eq!(
        ledger.len(),
        KNOWN_DEGENERATE_PENDING_FIX.len(),
        "KNOWN_DEGENERATE_PENDING_FIX contains duplicate names"
    );

    // Disjoint from the genuine allowlist: a suspicious proof must never be
    // dressed up as a genuine identity.
    let genuine: HashSet<&&str> = GENUINE_IDENTITY_ALLOWLIST.iter().collect();
    let overlap: Vec<&str> = KNOWN_DEGENERATE_PENDING_FIX
        .iter()
        .copied()
        .filter(|n| genuine.contains(&n))
        .collect();
    assert!(
        overlap.is_empty(),
        "name(s) appear on BOTH GENUINE_IDENTITY_ALLOWLIST and KNOWN_DEGENERATE_PENDING_FIX — a \
         suspicious proof must never be silently reclassified as genuine:\n{}",
        overlap.join("\n")
    );

    // Live: every ledger entry must be a currently-registered, degenerate proof.
    let dead: Vec<&str> = KNOWN_DEGENERATE_PENDING_FIX
        .iter()
        .copied()
        .filter(|n| !degen.contains(*n))
        .collect();
    assert!(
        dead.is_empty(),
        "KNOWN_DEGENERATE_PENDING_FIX has {} DEAD entr(y/ies) — fixed or removed proofs must be \
         deleted from the ledger (and DEBT_LEDGER_MAX_LEN lowered):\n{}",
        dead.len(),
        dead.join("\n")
    );
}

/// PROVES THE GATE HAS TEETH (fail-closed): inject a synthetic degenerate proof
/// (`X == X`) whose name is on NEITHER list and confirm the universal gate
/// reports it as a violation. This is the negative test that locks in that a
/// future degenerate proof cannot silently slip through.
#[test]
fn universal_gate_fails_closed_on_injected_degenerate_proof() {
    use trust_cg_verify::lowering_proof::ProofObligation;
    use trust_cg_verify::proof_database::{CategorizedProof, ProofCategory};
    use trust_cg_verify::smt::SmtExpr;

    let x = SmtExpr::var("x", 64);
    let injected = CategorizedProof {
        obligation: ProofObligation {
            machine_side_provenance:
                trust_cg_verify::lowering_proof::MachineSideProvenance::StaticDb,
            name: "INJECTED degenerate X==X (must fail the gate)".to_string(),
            trust_ir_expr: x.clone(),
            aarch64_expr: x, // structurally identical -> degenerate, no independent model
            inputs: vec![("x".to_string(), 64)],
            preconditions: vec![],
            fp_inputs: vec![],
            category: None,
        },
        category: ProofCategory::Arithmetic,
    };

    let db = on_large_stack(|| {
        let mut proofs: Vec<CategorizedProof> = ProofDatabase::new().all().to_vec();
        proofs.push(injected);
        ProofDatabase::from_proofs(proofs)
    });

    let violations: Vec<String> = db
        .non_degeneracy_violations()
        .into_iter()
        .map(|v| v.name)
        .collect();
    assert_eq!(
        violations,
        vec!["INJECTED degenerate X==X (must fail the gate)".to_string()],
        "the universal gate must report EXACTLY the injected degenerate proof as a violation \
         (and nothing else): otherwise the gate is not fail-closed, or the real registry \
         regressed. Got: {violations:?}"
    );
}

/// Compare real checked obligations under the same admitted solver/config.
/// This is an outcome/order check, not a timing comparison: the second arm
/// may reuse independently checked certificates from the first arm.
#[test]
fn admitted_parallel_discharge_matches_sequential_results() {
    if !formal_proof_test_enabled("admitted_parallel_discharge_matches_sequential_results") {
        return;
    }
    on_large_stack(|| {
        use trust_cg_verify::proof_database::ProofCategory;
        let gate = GateConfig::strict();
        require_formal_proof_toolchain(&gate, "parallel discharge comparison");
        let full = ProofDatabase::new();
        let proofs = full
            .by_category(ProofCategory::Arithmetic)
            .into_iter()
            .take(6)
            .cloned()
            .collect::<Vec<_>>();
        assert_eq!(proofs.len(), 6);
        let db = ProofDatabase::from_proofs(proofs);
        let sequential = gate
            .discharge_with_worker_limit(&db, std::num::NonZeroUsize::new(1).unwrap())
            .unwrap_or_else(|error| panic!("sequential comparison refused: {error}"));
        let parallel = gate
            .discharge_with_worker_limit(&db, std::num::NonZeroUsize::new(3).unwrap())
            .unwrap_or_else(|error| panic!("admitted parallel comparison refused: {error}"));
        assert_no_statistical_fallback(&sequential);
        assert_no_statistical_fallback(&parallel);
        assert_eq!(sequential.results.len(), 6);
        assert_eq!(parallel.results.len(), 6);
        assert_eq!(sequential.solver, parallel.solver);
        for (index, (left, right)) in sequential.results.iter().zip(&parallel.results).enumerate() {
            assert_eq!(left.name, db.all()[index].obligation.name);
            assert_eq!(left.name, right.name);
            assert_eq!(left.category, right.category);
            assert_eq!(left.ay_result, right.ay_result);
            assert!(sequential.all_verified() && parallel.all_verified());
        }
        eprintln!(
            "parallel comparison: 6/6 real checked obligations match; admission CARGO_BUILD_JOBS={:?}; requested limits1/3; no speed claim",
            std::env::var("CARGO_BUILD_JOBS").ok()
        );
    });
}
