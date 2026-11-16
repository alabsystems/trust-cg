-- Sentinel Certified-Elimination Kernel — decide() contract, formalized for Clean.
--
-- Production boundary (2026-11-10): elimination certificates now retain the exact
-- minted operand list and recheck compares it with the observed list. Thus the
-- production operand-drift check does not require fingerprint collision freedom.
-- Section IV below remains the older lossy fingerprint MODEL; its conditional
-- collision-resistance theorem is not a proof of this new exact production gate.
-- Porting that gate and its list comparison into Trust remains required.
--
-- Author: Andrew Yates
-- Copyright 2026 Andrew Yates | License: Apache-2.0
--
-- This file formalizes the soundness contract of the Rust kernel
-- `trust_cg_ir::guard::decide` (crates/trust-cg-ir/src/guard.rs). It is authored in
-- Clean's native Lean4 subset (Init arithmetic; checked tactic proofs; finite inductives — no Bool/Nat/Option
-- matching, which Clean's elaborator routes through an unavailable Decidable instance) and is
-- checked by:
--
--     python3 scripts/tests/sentinel_clean_unit_test.py -v
--
-- This compiles this entire file as a Trust Clean module and checks same-route
-- true/false theorem controls. The Rust lane is explicitly unverified: these
-- declaration checks do not establish the model-to-production correspondence.
--
-- The Rust kernel returns Eliminate iff ALL FIVE gates hold:
--   (1) the guard kind is proof-eliminable;
--   (2) the receipt has a non-empty operand identity;
--   (3) the operand fingerprint is self-consistent;
--   (4) the receipt references an obligation that is Discharged/Certified in the evidence;
--   (5) for the Certified tier, the receipt's lineage digest is present and equals the
--       evidence's lineage digest.
-- Otherwise it returns Keep. "Keep" is the structural fail-safe default.
--
-- We model gates (1)-(3) as a two-valued Flag, the obligation reference (4) and receipt lineage
-- (5) as small inductives, lineage digests as an opaque finite type, and evidence lookup as a
-- total function. We prove: (a) totality; (b) that EVERY gate-failure forces Keep, general over
-- all other inputs (the soundness-critical fail-safe property); (c) Eliminate/Keep on concrete
-- witnesses of the discharged and certified paths.
--
-- ===========================================================================================
-- EXTENSION: three further soundness sections, each a TRUSTED HAND-MIRROR of guard.rs (the
-- correspondence between these Lean definitions and the Rust source is established by hand and is
-- trusted; we prove properties of the Lean MODEL, not of the compiled Rust). The cited line
-- ranges are against crates/trust-cg-ir/src/guard.rs.
--
--   (I)  PER-KIND FAIL-SAFE. `GKind` is a 6-constructor inductive mirroring `GuardKind`
--        (guard.rs:119-132, discriminants 1..6 at :137-146). `gkindEliminable` returns yes for
--        every kind, mirroring `is_eliminable_by_proof` returning true for ALL variants
--        (guard.rs:151-161). We re-run `cekDecide` per kind (`cekDecideK`) and prove every
--        gate-failure path yields Keep, for EVERY kind.
--
--   (II) STRICT-SUBSET / never-eliminate-the-unproven. `legacyDecide` models the legacy
--        keep-and-trap behavior: it NEVER eliminates (always Keep — it preserves the runtime
--        trap). We prove `cekDecide = Eliminate` happens ONLY where the obligation was
--        Discharged/Certified in the evidence, i.e. the kernel eliminates only a guard whose trap
--        legacy would have kept — so behavior is preserved (the discharged proof makes the kept
--        trap dead). With absent evidence the result is Keep (= legacyDecide). The HEADLINE is a
--        UNIVERSAL Flag-EQUALITY: `cekDecideEliminates` (Flag.yes iff Eliminate) equals a
--        tier-faithful discharge predicate for ALL evidence (and, in companion lemmas, for ALL
--        receipt/evidence lineage digests). This is a forall-quantified iff — strictly stronger
--        than the concrete witnesses (which are also kept). The Prop IMPLICATION form
--        `cekDecide = Eliminate -> discharged` is what the Clean elaborator rejects; the
--        computable Flag-EQUALITY form succeeds. See note below.
--
--   (III) RECHECK SOUNDNESS. `cekRecheck` models `recheck_elimination` (guard.rs:612-670), the
--        independent "different path" re-validator, by deferring to the same verdict: it Accepts
--        only when `cekDecide` would Eliminate, and Rejects otherwise. The HEADLINE is a UNIVERSAL
--        verdict-agreement equality over ALL inputs (`cekRecheck_iff_cekDecide`, global rfl): recheck
--        accepts EXACTLY when decide eliminates. So recheck never accepts an elimination decide would
--        not make.
--
--   (IV) OPERAND-DRIFT DETECTION (this section closes the gap §III formerly left open). We add an
--        `Operand` inductive mirroring `GuardOperandRef` (Reg Nat | Imm Int, guard.rs:212-217), a
--        recursive `Operands` list, and a TOTAL deterministic `fnvFingerprint : Operands -> Fp`
--        modeling the FNV-128 operand fingerprint (guard.rs:250-267). `Fp` is a FINITE codomain, so
--        `fnvFingerprint` is genuinely LOSSY (non-injective) — collision-resistance is therefore a
--        REAL assumption, never a free lemma. `cekRecheckWithDrift` re-checks the observed-vs-cert
--        fingerprint comparison (mirroring guard.rs:633) BEFORE delegating to the §III verdict logic.
--        Two headline theorems:
--          * SAFETY (axiom-free, pure computation): `cekRecheck_rejects_on_fingerprint_mismatch` —
--            when the fingerprint comparison reports mismatch, recheck Rejects regardless of every
--            downstream gate. This is the fail-safe "never Eliminate on fingerprint drift" guarantee;
--            it needs NO axiom (the trusted core stays at propext / Quot.sound / Classical.choice).
--          * COMPLETENESS (collision-resistance as an EXPLICIT HYPOTHESIS, not a global axiom):
--            `drift_detected` — if the observed operands differ from the minted operands, recheck
--            Rejects, PROVIDED `CollisionResistant` (distinct operand lists hash distinct, i.e. FNV
--            is collision-free over the relevant domain). The hypothesis NAMES exactly what stays in
--            the TCB (FNV collision-freedom over the finite real operand domain) and keeps the 3-axiom
--            core intact — we never add an `axiom` for it.

-- The kernel's two outputs.
inductive Verdict where
  | keep
  | eliminate

-- A boolean gate result, modeled as a finite inductive (Clean matches these directly).
inductive Flag where
  | yes
  | no

-- Obligation ids (an opaque finite domain suffices to exercise lookup).
inductive ObId where
  | o1
  | o2

-- Lineage digests (opaque; only equality matters).
inductive Digest where
  | dA
  | dB

-- Discharge tier of an obligation found in the evidence table.
inductive Evid where
  | absent                          -- not discharged (Pending/Failed/missing) => keep
  | discharged                      -- Discharged/Trusted tier: eliminate (no lineage needed)
  | certified (lineage : Digest)    -- Certified tier: eliminate iff receipt lineage matches

-- The receipt's obligation reference (gate 4).
inductive ObRef where
  | noObligation
  | obligation (id : ObId)

-- The receipt's claimed lineage digest (gate 5, Certified tier).
inductive LinRef where
  | noLineage
  | lineage (digest : Digest)

-- Equality verdict for lineage digests.
inductive Cmp where
  | eq
  | ne

-- Decidable equality of digests (non-recursive; finite match).
def digestCmp (a b : Digest) : Cmp :=
  match a with
  | Digest.dA => match b with
    | Digest.dA => Cmp.eq
    | Digest.dB => Cmp.ne
  | Digest.dB => match b with
    | Digest.dA => Cmp.ne
    | Digest.dB => Cmp.eq

-- Faithful mirror of `decide`: five sequential gates; Keep is the default at every gate.
def cekDecide (eliminable opsNonempty consistent : Flag)
    (oblig : ObRef) (recLineage : LinRef) (lookup : ObId -> Evid) : Verdict :=
  match eliminable with
  | Flag.no => Verdict.keep
  | Flag.yes =>
    match opsNonempty with
    | Flag.no => Verdict.keep
    | Flag.yes =>
      match consistent with
      | Flag.no => Verdict.keep
      | Flag.yes =>
        match oblig with
        | ObRef.noObligation => Verdict.keep
        | ObRef.obligation id =>
          match lookup id with
          | Evid.absent => Verdict.keep
          | Evid.discharged => Verdict.eliminate
          | Evid.certified l =>
            match recLineage with
            | LinRef.noLineage => Verdict.keep
            | LinRef.lineage r =>
              match digestCmp r l with
              | Cmp.eq => Verdict.eliminate
              | Cmp.ne => Verdict.keep

-- A TOTAL computable eliminate-flag: Flag.yes iff `cekDecide` returns Eliminate. This is the
-- decidable companion to `cekDecide` that lets us state the strict-subset contract as a
-- COMPUTABLE Flag-EQUALITY (decidable, rfl-checkable) rather than as a Prop implication
-- `cekDecide = eliminate -> ...` (whose Prop-motive case-split on the Verdict inductive the Clean
-- term-mode elaborator rejects). See section (II) below.
def cekDecideEliminates (eliminable opsNonempty consistent : Flag)
    (oblig : ObRef) (recLineage : LinRef) (lookup : ObId -> Evid) : Flag :=
  match cekDecide eliminable opsNonempty consistent oblig recLineage lookup with
  | Verdict.eliminate => Flag.yes
  | Verdict.keep => Flag.no

-- (a) Totality. `cekDecide` returns a Verdict for every input (Clean enforces def totality).
theorem cekDecide_total (e o c : Flag) (ob : ObRef) (rl : LinRef) (lk : ObId -> Evid) :
    cekDecide e o c ob rl lk = cekDecide e o c ob rl lk :=
  rfl

-- (b) FAIL-SAFE DEFAULT. Each gate, when it fails, forces Keep regardless of all later inputs.
-- Each lemma is universally quantified over every remaining argument: one proof covers all
-- cases, so no downstream condition can override a failed gate.

-- Gate 1: a non-eliminable guard kind is always kept.
theorem keep_if_not_eliminable (o c : Flag) (ob : ObRef) (rl : LinRef) (lk : ObId -> Evid) :
    cekDecide Flag.no o c ob rl lk = Verdict.keep :=
  rfl

-- Gate 2: an empty operand identity is always kept.
theorem keep_if_no_operands (c : Flag) (ob : ObRef) (rl : LinRef) (lk : ObId -> Evid) :
    cekDecide Flag.yes Flag.no c ob rl lk = Verdict.keep :=
  rfl

-- Gate 3: an inconsistent operand fingerprint is always kept.
theorem keep_if_inconsistent (ob : ObRef) (rl : LinRef) (lk : ObId -> Evid) :
    cekDecide Flag.yes Flag.yes Flag.no ob rl lk = Verdict.keep :=
  rfl

-- Gate 4: a receipt with no bound obligation is always kept.
theorem keep_if_no_obligation (rl : LinRef) (lk : ObId -> Evid) :
    cekDecide Flag.yes Flag.yes Flag.yes ObRef.noObligation rl lk = Verdict.keep :=
  rfl

-- (c) JUSTIFIED ELIMINATION on concrete witnesses.

-- Evidence: obligation o1 is Discharged; o2 absent.
def lkDischarged : ObId -> Evid :=
  fun id => match id with
    | ObId.o1 => Evid.discharged
    | ObId.o2 => Evid.absent

-- Discharged tier eliminates (no lineage required).
theorem eliminate_when_discharged :
    cekDecide Flag.yes Flag.yes Flag.yes (ObRef.obligation ObId.o1) LinRef.noLineage lkDischarged
      = Verdict.eliminate :=
  rfl

-- An obligation absent from the evidence is kept (gate 4, evidence side).
theorem keep_when_obligation_absent :
    cekDecide Flag.yes Flag.yes Flag.yes (ObRef.obligation ObId.o2) LinRef.noLineage lkDischarged
      = Verdict.keep :=
  rfl

-- Evidence: obligation o1 is Certified with lineage digest dA.
def lkCertified : ObId -> Evid :=
  fun id => match id with
    | ObId.o1 => Evid.certified Digest.dA
    | ObId.o2 => Evid.absent

-- Certified tier eliminates ONLY when the receipt's lineage matches the evidence's.
theorem eliminate_when_certified_lineage_match :
    cekDecide Flag.yes Flag.yes Flag.yes (ObRef.obligation ObId.o1) (LinRef.lineage Digest.dA)
      lkCertified = Verdict.eliminate :=
  rfl

-- Certified tier keeps when the receipt's lineage mismatches (gate 5).
theorem keep_when_certified_lineage_mismatch :
    cekDecide Flag.yes Flag.yes Flag.yes (ObRef.obligation ObId.o1) (LinRef.lineage Digest.dB)
      lkCertified = Verdict.keep :=
  rfl

-- Certified tier keeps when the receipt carries no lineage at all (gate 5).
theorem keep_when_certified_no_receipt_lineage :
    cekDecide Flag.yes Flag.yes Flag.yes (ObRef.obligation ObId.o1) LinRef.noLineage
      lkCertified = Verdict.keep :=
  rfl

-- ===========================================================================================
-- (I) PER-KIND FAIL-SAFE over the guard-kind taxonomy.
--
-- TRUSTED HAND-MIRROR of guard.rs. `GKind` mirrors `GuardKind` (guard.rs:119-132), one
-- constructor per variant, in discriminant order 1..6 (guard.rs:137-146).
-- ===========================================================================================

-- Mirror of GuardKind's six variants (guard.rs:119-132).
inductive GKind where
  | boundsCheck        -- discriminant 1
  | nullPtr            -- discriminant 2
  | divZero            -- discriminant 3
  | shiftRange         -- discriminant 4
  | signedOverflow     -- discriminant 5
  | unsignedOverflow   -- discriminant 6

-- Mirror of `is_eliminable_by_proof` (guard.rs:151-161): TRUE for every guard kind.
def gkindEliminable (k : GKind) : Flag :=
  match k with
  | GKind.boundsCheck => Flag.yes
  | GKind.nullPtr => Flag.yes
  | GKind.divZero => Flag.yes
  | GKind.shiftRange => Flag.yes
  | GKind.signedOverflow => Flag.yes
  | GKind.unsignedOverflow => Flag.yes

-- decide() parameterized by the guard kind: gate 1 is computed from the kind, exactly as
-- guard.rs:543 calls `receipt.kind.is_eliminable_by_proof()`.
def cekDecideK (k : GKind) (opsNonempty consistent : Flag)
    (oblig : ObRef) (recLineage : LinRef) (lookup : ObId -> Evid) : Verdict :=
  cekDecide (gkindEliminable k) opsNonempty consistent oblig recLineage lookup

-- Every guard kind is eliminable (the gate-1 predicate holds universally), mirroring the Rust
-- `is_eliminable_by_proof` always-true property. One proof per kind (rfl over a free GKind would
-- stay stuck, so we pin each constructor).
theorem gkind_eliminable_boundsCheck : gkindEliminable GKind.boundsCheck = Flag.yes := rfl
theorem gkind_eliminable_nullPtr : gkindEliminable GKind.nullPtr = Flag.yes := rfl
theorem gkind_eliminable_divZero : gkindEliminable GKind.divZero = Flag.yes := rfl
theorem gkind_eliminable_shiftRange : gkindEliminable GKind.shiftRange = Flag.yes := rfl
theorem gkind_eliminable_signedOverflow : gkindEliminable GKind.signedOverflow = Flag.yes := rfl
theorem gkind_eliminable_unsignedOverflow :
    gkindEliminable GKind.unsignedOverflow = Flag.yes := rfl

-- PER-KIND FAIL-SAFE (gate 2: empty operands). For EVERY guard kind, an empty operand identity
-- forces Keep, regardless of every later input. One rfl per kind (the per-gate style of the spec).
theorem keep_no_ops_boundsCheck (c : Flag) (ob : ObRef) (rl : LinRef) (lk : ObId -> Evid) :
    cekDecideK GKind.boundsCheck Flag.no c ob rl lk = Verdict.keep := rfl
theorem keep_no_ops_nullPtr (c : Flag) (ob : ObRef) (rl : LinRef) (lk : ObId -> Evid) :
    cekDecideK GKind.nullPtr Flag.no c ob rl lk = Verdict.keep := rfl
theorem keep_no_ops_divZero (c : Flag) (ob : ObRef) (rl : LinRef) (lk : ObId -> Evid) :
    cekDecideK GKind.divZero Flag.no c ob rl lk = Verdict.keep := rfl
theorem keep_no_ops_shiftRange (c : Flag) (ob : ObRef) (rl : LinRef) (lk : ObId -> Evid) :
    cekDecideK GKind.shiftRange Flag.no c ob rl lk = Verdict.keep := rfl
theorem keep_no_ops_signedOverflow (c : Flag) (ob : ObRef) (rl : LinRef) (lk : ObId -> Evid) :
    cekDecideK GKind.signedOverflow Flag.no c ob rl lk = Verdict.keep := rfl
theorem keep_no_ops_unsignedOverflow (c : Flag) (ob : ObRef) (rl : LinRef) (lk : ObId -> Evid) :
    cekDecideK GKind.unsignedOverflow Flag.no c ob rl lk = Verdict.keep := rfl

-- PER-KIND FAIL-SAFE (gate 3: inconsistent fingerprint). For EVERY guard kind, an inconsistent
-- operand fingerprint forces Keep, regardless of obligation/lineage/evidence.
theorem keep_inconsistent_boundsCheck (ob : ObRef) (rl : LinRef) (lk : ObId -> Evid) :
    cekDecideK GKind.boundsCheck Flag.yes Flag.no ob rl lk = Verdict.keep := rfl
theorem keep_inconsistent_nullPtr (ob : ObRef) (rl : LinRef) (lk : ObId -> Evid) :
    cekDecideK GKind.nullPtr Flag.yes Flag.no ob rl lk = Verdict.keep := rfl
theorem keep_inconsistent_divZero (ob : ObRef) (rl : LinRef) (lk : ObId -> Evid) :
    cekDecideK GKind.divZero Flag.yes Flag.no ob rl lk = Verdict.keep := rfl
theorem keep_inconsistent_shiftRange (ob : ObRef) (rl : LinRef) (lk : ObId -> Evid) :
    cekDecideK GKind.shiftRange Flag.yes Flag.no ob rl lk = Verdict.keep := rfl
theorem keep_inconsistent_signedOverflow (ob : ObRef) (rl : LinRef) (lk : ObId -> Evid) :
    cekDecideK GKind.signedOverflow Flag.yes Flag.no ob rl lk = Verdict.keep := rfl
theorem keep_inconsistent_unsignedOverflow (ob : ObRef) (rl : LinRef) (lk : ObId -> Evid) :
    cekDecideK GKind.unsignedOverflow Flag.yes Flag.no ob rl lk = Verdict.keep := rfl

-- PER-KIND FAIL-SAFE (gate 4: no bound obligation). For EVERY guard kind, a receipt with no bound
-- obligation forces Keep. Since the kind IS eliminable, this exercises that the SAME default holds
-- after gate 1 passes for each kind.
theorem keep_no_oblig_boundsCheck (rl : LinRef) (lk : ObId -> Evid) :
    cekDecideK GKind.boundsCheck Flag.yes Flag.yes ObRef.noObligation rl lk = Verdict.keep := rfl
theorem keep_no_oblig_nullPtr (rl : LinRef) (lk : ObId -> Evid) :
    cekDecideK GKind.nullPtr Flag.yes Flag.yes ObRef.noObligation rl lk = Verdict.keep := rfl
theorem keep_no_oblig_divZero (rl : LinRef) (lk : ObId -> Evid) :
    cekDecideK GKind.divZero Flag.yes Flag.yes ObRef.noObligation rl lk = Verdict.keep := rfl
theorem keep_no_oblig_shiftRange (rl : LinRef) (lk : ObId -> Evid) :
    cekDecideK GKind.shiftRange Flag.yes Flag.yes ObRef.noObligation rl lk = Verdict.keep := rfl
theorem keep_no_oblig_signedOverflow (rl : LinRef) (lk : ObId -> Evid) :
    cekDecideK GKind.signedOverflow Flag.yes Flag.yes ObRef.noObligation rl lk = Verdict.keep := rfl
theorem keep_no_oblig_unsignedOverflow (rl : LinRef) (lk : ObId -> Evid) :
    cekDecideK GKind.unsignedOverflow Flag.yes Flag.yes ObRef.noObligation rl lk = Verdict.keep :=
  rfl

-- ===========================================================================================
-- (II) STRICT-SUBSET REFINEMENT: the kernel never eliminates more than is proven.
--
-- TRUSTED HAND-MIRROR. `legacyDecide` is the pre-kernel behavior: keep-and-trap. It NEVER
-- eliminates (always Keep — the runtime trap is preserved at every site). The kernel `cekDecide`
-- eliminates only at sites where the obligation is Discharged/Certified in the evidence, i.e. a
-- STRICT SUBSET of legacy's kept sites whose trap the discharged proof renders dead. With absent
-- evidence the kernel agrees with legacy (Keep).
--
-- TERM-MODE NOTE (corrected): the form that the Clean elaborator REJECTS is the Prop IMPLICATION
--   `cekDecide ... = eliminate -> evidence-was-discharged`
-- (a Prop-motive case-split on the Verdict inductive). The equivalent COMPUTABLE Flag-EQUALITY
-- form, however, IS accepted and is what we use for the HEADLINE universal theorem below: we wrap
-- the verdict as a total `cekDecideEliminates : ... -> Flag` and prove, UNIVERSALLY over the finite
-- evidence (and, in a companion lemma, over the finite receipt-lineage), that the kernel eliminates
-- EXACTLY when the obligation's tier is discharge-justified. This is a forall-quantified iff over
-- ALL evidence — strictly stronger than the concrete witnesses (which we also keep below).
--
-- TIER-FAITHFUL RHS (important): the headline does NOT use raw `evidDischarged` on the no-lineage
-- scenario, because `evidDischarged (certified _) = yes` while `cekDecide` KEEPS a certified
-- obligation whose RECEIPT carries no lineage (gate 5). The universal RHS is therefore tier-aware:
-- the certified leaf maps to Keep when the receipt has no lineage, and is handled by the companion
-- lineage lemma when it does. Using raw `evidDischarged` here would make the theorem FALSE on the
-- certified leaf; the tier-aware match is the faithful invariant.
--
-- We ALSO keep the concrete-witness equalities below: every concrete Eliminate decision is matched
-- by (a) legacyDecide = Keep at the same site, and (b) the evidence there being Discharged/Certified;
-- every absent-evidence site is Keep in BOTH.
-- ===========================================================================================

-- Legacy keep-and-trap: never eliminates a guard (always preserves the runtime trap).
def legacyDecide (eliminable opsNonempty consistent : Flag)
    (oblig : ObRef) (recLineage : LinRef) (lookup : ObId -> Evid) : Verdict :=
  Verdict.keep

-- "Was this obligation proven?" — Discharged/Certified count as proven; absent does not.
-- Mirrors the evidence.lookup result (guard.rs:566) feeding the Discharged/Certified tiers (:577).
def evidDischarged (e : Evid) : Flag :=
  match e with
  | Evid.absent => Flag.no
  | Evid.discharged => Flag.yes
  | Evid.certified _ => Flag.yes

-- legacy ALWAYS keeps, for every input (universal — no gate match needed).
theorem legacy_always_keeps (e o c : Flag) (ob : ObRef) (rl : LinRef) (lk : ObId -> Evid) :
    legacyDecide e o c ob rl lk = Verdict.keep := rfl

-- REFINEMENT, discharged path. The kernel eliminates here (reuses lkDischarged from above)...
theorem strict_subset_discharged_kernel_eliminates :
    cekDecide Flag.yes Flag.yes Flag.yes (ObRef.obligation ObId.o1) LinRef.noLineage lkDischarged
      = Verdict.eliminate := rfl
-- ...while legacy would have KEPT (trapped) at the very same site...
theorem strict_subset_discharged_legacy_keeps :
    legacyDecide Flag.yes Flag.yes Flag.yes (ObRef.obligation ObId.o1) LinRef.noLineage lkDischarged
      = Verdict.keep := rfl
-- ...and the eliminated site's evidence really was Discharged (proven): the trap is dead.
theorem strict_subset_discharged_was_proven :
    evidDischarged (lkDischarged ObId.o1) = Flag.yes := rfl

-- REFINEMENT, certified path. Kernel eliminates only on lineage match (reuses lkCertified)...
theorem strict_subset_certified_kernel_eliminates :
    cekDecide Flag.yes Flag.yes Flag.yes (ObRef.obligation ObId.o1) (LinRef.lineage Digest.dA)
      lkCertified = Verdict.eliminate := rfl
theorem strict_subset_certified_legacy_keeps :
    legacyDecide Flag.yes Flag.yes Flag.yes (ObRef.obligation ObId.o1) (LinRef.lineage Digest.dA)
      lkCertified = Verdict.keep := rfl
theorem strict_subset_certified_was_proven :
    evidDischarged (lkCertified ObId.o1) = Flag.yes := rfl

-- WHERE NOTHING IS PROVEN, THE KERNEL AGREES WITH LEGACY (both Keep) — the core of
-- "never eliminate more than is proven": absent evidence => Keep, matching legacyDecide.
theorem strict_subset_absent_kernel_keeps :
    cekDecide Flag.yes Flag.yes Flag.yes (ObRef.obligation ObId.o2) LinRef.noLineage lkDischarged
      = Verdict.keep := rfl
theorem strict_subset_absent_is_unproven :
    evidDischarged (lkDischarged ObId.o2) = Flag.no := rfl

-- -------------------------------------------------------------------------------------------
-- HEADLINE UNIVERSAL STRICT-SUBSET (forall evidence). This is the quantified iff the prior
-- attempt could not state as a Prop implication. With all upstream gates passing and a bound
-- obligation, the kernel eliminates EXACTLY when the looked-up evidence is discharge-justified,
-- quantified over ALL evidence `e` (the lookup table is `fun _ => e`, so gate-4 lookup reduces to
-- e). The RHS is tier-faithful: the certified leaf with NO receipt lineage keeps (gate 5), so it
-- maps to Flag.no here; the certified-WITH-lineage case is the companion lemma below.
-- Proven by a single-level match over the finite Evid with each leaf rfl (a global rfl would stay
-- stuck — cekDecideEliminates reduces via Verdict.casesOn while the RHS reduces via Evid.casesOn,
-- so the two normal forms do not meet against a free `e`; cf. the per-kind note at gate 1 above).
theorem cekDecideEliminates_iff_discharged (e : Evid) :
    cekDecideEliminates Flag.yes Flag.yes Flag.yes (ObRef.obligation ObId.o1) LinRef.noLineage
      (fun _ => e)
      = (match e with
         | Evid.absent => Flag.no
         | Evid.discharged => Flag.yes
         | Evid.certified _ => Flag.no) :=
  match e with
  | Evid.absent => rfl
  | Evid.discharged => rfl
  | Evid.certified _ => rfl

-- Tier-faithful gate-5 specification as a TOTAL helper (single-level match). The kernel eliminates
-- a certified obligation EXACTLY when the receipt's claimed lineage digest `r` compares equal to
-- the evidence's lineage digest `l`. Quantifying over the DIGEST directly (rather than over LinRef
-- with a nested digestCmp match) keeps everything single-level: when `r` is a concrete digest,
-- `digestCmp r l` reduces, so each leaf is a closed rfl — whereas leaving `digestCmp r l` stuck
-- under a free `r` would make the outer Verdict.casesOn and the helper's Cmp.casesOn fail to meet.
def digestEliminates (r l : Digest) : Flag :=
  match digestCmp r l with
  | Cmp.eq => Flag.yes
  | Cmp.ne => Flag.no

-- COMPANION UNIVERSAL #1 (forall receipt lineage digest `r`), at fixed certified-dA evidence and a
-- receipt that DOES carry a lineage. Captures gate 5 universally over the receipt's claimed digest:
-- the kernel eliminates the certified obligation EXACTLY when `r` matches the evidence digest dA.
-- Single-level match over the finite Digest; each leaf rfl (digestCmp reduces on a concrete `r`).
theorem cekDecideEliminates_certified_iff_lineage (r : Digest) :
    cekDecideEliminates Flag.yes Flag.yes Flag.yes (ObRef.obligation ObId.o1)
      (LinRef.lineage r) (fun _ => Evid.certified Digest.dA)
      = digestEliminates r Digest.dA :=
  match r with
  | Digest.dA => rfl
  | Digest.dB => rfl

-- COMPANION UNIVERSAL #2 (forall evidence lineage digest `l`), at a receipt carrying lineage dA.
-- Symmetric coverage of gate 5: eliminate EXACTLY when the receipt digest dA matches the evidence
-- digest `l`. Together with #1 this exhausts the certified-tier lineage comparison universally.
theorem cekDecideEliminates_certified_iff_evidence_lineage (l : Digest) :
    cekDecideEliminates Flag.yes Flag.yes Flag.yes (ObRef.obligation ObId.o1)
      (LinRef.lineage Digest.dA) (fun _ => Evid.certified l)
      = digestEliminates Digest.dA l :=
  match l with
  | Digest.dA => rfl
  | Digest.dB => rfl

-- COMPANION UNIVERSAL #3 (forall evidence digest `l`): a certified obligation whose RECEIPT carries
-- NO lineage is ALWAYS kept (gate 5), regardless of the evidence's lineage digest. This is the
-- tier-faithfulness witness that distinguishes the headline from raw `evidDischarged` (which would
-- wrongly say `yes` here). Single-level match over the finite Digest; each leaf rfl.
theorem cekDecideEliminates_certified_no_receipt_lineage_keeps (l : Digest) :
    cekDecideEliminates Flag.yes Flag.yes Flag.yes (ObRef.obligation ObId.o1)
      LinRef.noLineage (fun _ => Evid.certified l)
      = Flag.no :=
  match l with
  | Digest.dA => rfl
  | Digest.dB => rfl

-- ===========================================================================================
-- (III) RECHECK SOUNDNESS: the independent re-validator accepts no elimination decide would not.
--
-- TRUSTED HAND-MIRROR of `recheck_elimination` (guard.rs:612-670). The Rust re-checker walks a
-- "different path" (re-derives the operand fingerprint, re-confirms status/lineage). The MODEL
-- captures the soundness-relevant invariant only: cekRecheck Accepts exactly when cekDecide would
-- Eliminate, and Rejects otherwise. So recheck never accepts an elimination decide would not make.
-- The HEADLINE `cekRecheck_iff_cekDecide` states this UNIVERSALLY over all inputs (global rfl).
--
-- SCOPE (updated): this section models verdict agreement only (accept iff decide eliminates). The
-- FNV operand-fingerprint re-derivation (guard.rs:633) and its operand-DRIFT detection are now
-- modeled and PROVEN in section (IV) below: drift-detection SAFETY is machine-checked AXIOM-FREE
-- (`cekRecheck_rejects_on_fingerprint_mismatch`), and drift-detection COMPLETENESS is proven
-- relative to an EXPLICIT collision-resistance hypothesis (`drift_detected`) that keeps the trusted
-- core at exactly three axioms. The certificate validation hash (guard.rs:617) remains out of model
-- scope (it is an internal-consistency self-check, not an operand-soundness gate).
-- ===========================================================================================

-- Re-check outcome: mirror of RecheckOutcome {Valid, Rejected{..}} (guard.rs:600-606).
inductive Recheck where
  | accept
  | reject

-- Re-validate by deferring to the kernel verdict: accept iff decide would eliminate.
def cekRecheck (eliminable opsNonempty consistent : Flag)
    (oblig : ObRef) (recLineage : LinRef) (lookup : ObId -> Evid) : Recheck :=
  match cekDecide eliminable opsNonempty consistent oblig recLineage lookup with
  | Verdict.eliminate => Recheck.accept
  | Verdict.keep => Recheck.reject

-- SOUNDNESS (reject side, fail-safe): a non-eliminable kind is rejected by recheck, regardless of
-- every later input (universal over the downstream args — gate 1 pinned to Flag.no).
theorem recheck_reject_if_not_eliminable
    (o c : Flag) (ob : ObRef) (rl : LinRef) (lk : ObId -> Evid) :
    cekRecheck Flag.no o c ob rl lk = Recheck.reject := rfl

-- Recheck rejects when the obligation is absent from evidence (decide keeps there too).
theorem recheck_reject_when_absent :
    cekRecheck Flag.yes Flag.yes Flag.yes (ObRef.obligation ObId.o2) LinRef.noLineage lkDischarged
      = Recheck.reject := rfl

-- Recheck rejects a certified-tier lineage mismatch (decide keeps; recheck must NOT accept).
theorem recheck_reject_certified_mismatch :
    cekRecheck Flag.yes Flag.yes Flag.yes (ObRef.obligation ObId.o1) (LinRef.lineage Digest.dB)
      lkCertified = Recheck.reject := rfl

-- SOUNDNESS (accept side): recheck accepts the discharged elimination — exactly the site where
-- decide eliminates (cf. eliminate_when_discharged above).
theorem recheck_accept_discharged :
    cekRecheck Flag.yes Flag.yes Flag.yes (ObRef.obligation ObId.o1) LinRef.noLineage lkDischarged
      = Recheck.accept := rfl

-- Recheck accepts the matched certified elimination — exactly the site decide eliminates.
theorem recheck_accept_certified_match :
    cekRecheck Flag.yes Flag.yes Flag.yes (ObRef.obligation ObId.o1) (LinRef.lineage Digest.dA)
      lkCertified = Recheck.accept := rfl

-- -------------------------------------------------------------------------------------------
-- HEADLINE UNIVERSAL RECHECK SOUNDNESS (forall ALL inputs). Recheck agrees with decide on EVERY
-- input: it Accepts exactly when the kernel would Eliminate and Rejects exactly when it would Keep.
-- This is fully universal over all six arguments (no pinned gate, no concrete witness) and closes by
-- a single global rfl, because `cekRecheck` is DEFINITIONALLY the match on `cekDecide`'s verdict —
-- the two sides share the same normal form. So recheck never accepts an elimination decide would not
-- make, and never rejects one it would: exact verdict agreement, universally.
theorem cekRecheck_iff_cekDecide
    (g1 g2 g3 : Flag) (ob : ObRef) (rl : LinRef) (lk : ObId -> Evid) :
    cekRecheck g1 g2 g3 ob rl lk
      = (match cekDecide g1 g2 g3 ob rl lk with
         | Verdict.eliminate => Recheck.accept
         | Verdict.keep => Recheck.reject) :=
  rfl

-- ===========================================================================================
-- (IV) OPERAND-DRIFT DETECTION — closing the §III gap.
--
-- TRUSTED HAND-MIRROR of guard.rs. We model the operand list a guard is a claim ABOUT, its FNV
-- operand fingerprint (`fingerprint_operands`, guard.rs:250-267), and the re-checker's operand-drift
-- gate (`recheck_elimination`, the fingerprint re-derivation at guard.rs:633). The §III model only
-- captured verdict agreement; this section adds the operand-fingerprint re-derivation §III lacked,
-- and PROVES both the fail-safe SAFETY direction (axiom-free) and the COMPLETENESS direction (under
-- an explicit, named collision-resistance hypothesis — NOT a global axiom).
-- ===========================================================================================

-- An operand, mirroring `GuardOperandRef` (guard.rs:212-217): a register id, or an immediate.
-- (Nat for the reg id ~ u32; Int for the immediate ~ i64 — the kernel uses both only by value.)
inductive Operand where
  | reg (id : Nat)
  | imm (value : Int)

-- The ordered operand list a guard is a claim about (mirrors `Vec<GuardOperandRef>`,
-- guard.rs:227). A small recursive inductive — Clean elaborates structural recursion over it.
inductive Operands where
  | nil
  | cons (head : Operand) (tail : Operands)

-- The fingerprint codomain. DELIBERATELY FINITE: a real 128-bit FNV digest is finite too, so it is
-- genuinely LOSSY over the unbounded operand domain — distinct operand lists CAN collide. Modeling
-- the codomain as finite is what makes collision-resistance an honest ASSUMPTION below (an injective
-- `fnvFingerprint` would make collision-freedom a free lemma and misrepresent the real hash).
inductive Fp where
  | a
  | b
  | c
  | d

-- Fold one operand into the running digest: a deterministic, content-sensitive step (it depends on
-- BOTH the operand's tag — reg vs imm — and a coarse projection of its value), mirroring that
-- `fingerprint_operands` mixes the per-operand tag byte (0/1) and the value (guard.rs:255-264).
def fpStep (acc : Fp) (o : Operand) : Fp :=
  match o with
  | Operand.reg _ =>
    match acc with
    | Fp.a => Fp.b
    | Fp.b => Fp.c
    | Fp.c => Fp.d
    | Fp.d => Fp.a
  | Operand.imm _ =>
    match acc with
    | Fp.a => Fp.c
    | Fp.b => Fp.d
    | Fp.c => Fp.a
    | Fp.d => Fp.b

-- TOTAL deterministic fingerprint of an ordered operand list — the model of `fingerprint_operands`
-- (guard.rs:250-267). It need not replicate FNV's bit-mixing; it must be a deterministic FUNCTION of
-- the operand list, which (being a Lean function) it is by construction. Structural recursion over
-- `Operands`; Clean accepts it (cf. the recursion probes in this codebase).
def fnvFingerprint (ops : Operands) : Fp :=
  match ops with
  | Operands.nil => Fp.a
  | Operands.cons h t => fpStep (fnvFingerprint t) h

-- Computable equality verdict for fingerprints, in the same `Cmp` style as `digestCmp` (the model
-- never matches on Bool/Decidable; it routes equality through a finite-inductive comparison).
def fpCmp (x y : Fp) : Cmp :=
  match x with
  | Fp.a => match y with
    | Fp.a => Cmp.eq
    | Fp.b => Cmp.ne
    | Fp.c => Cmp.ne
    | Fp.d => Cmp.ne
  | Fp.b => match y with
    | Fp.a => Cmp.ne
    | Fp.b => Cmp.eq
    | Fp.c => Cmp.ne
    | Fp.d => Cmp.ne
  | Fp.c => match y with
    | Fp.a => Cmp.ne
    | Fp.b => Cmp.ne
    | Fp.c => Cmp.eq
    | Fp.d => Cmp.ne
  | Fp.d => match y with
    | Fp.a => Cmp.ne
    | Fp.b => Cmp.ne
    | Fp.c => Cmp.ne
    | Fp.d => Cmp.eq

-- The DRIFT-AWARE re-checker: mirror of `recheck_elimination` (guard.rs:612-670) with the operand
-- fingerprint re-derivation gate (guard.rs:633) made explicit. `fpMatch` is the re-checker's
-- comparison of the fingerprint re-derived from the OBSERVED operands against the certificate's
-- stored `operand_fingerprint`. On mismatch (`Cmp.ne`) it Rejects — the fail-safe; on match
-- (`Cmp.eq`) it DELEGATES to the §III verdict-agreement re-checker `cekRecheck`. So drift is caught
-- BEFORE the verdict logic, exactly as the Rust gate precedes the evidence re-confirmation.
def cekRecheckWithDrift (fpMatch : Cmp)
    (eliminable opsNonempty consistent : Flag)
    (oblig : ObRef) (recLineage : LinRef) (lookup : ObId -> Evid) : Recheck :=
  match fpMatch with
  | Cmp.ne => Recheck.reject
  | Cmp.eq => cekRecheck eliminable opsNonempty consistent oblig recLineage lookup

-- The DELEGATION law: when the observed and certificate fingerprints compare equal, the drift-aware
-- re-checker is exactly the §III re-checker (no behavior change on the matching path). Global rfl.
theorem cekRecheckWithDrift_match_delegates
    (g1 g2 g3 : Flag) (ob : ObRef) (rl : LinRef) (lk : ObId -> Evid) :
    cekRecheckWithDrift Cmp.eq g1 g2 g3 ob rl lk = cekRecheck g1 g2 g3 ob rl lk :=
  rfl

-- ===========================================================================================
-- SAFETY DIRECTION (AXIOM-FREE). The fail-safe operand-drift guarantee: when the fingerprint
-- comparison reports mismatch, recheck Rejects regardless of EVERY downstream gate. Pure
-- computation — a single rfl, universally over all remaining arguments. NO new axiom: this is the
-- "never Eliminate on a fingerprint mismatch" property, proven by reduction alone.
-- ===========================================================================================
theorem cekRecheckWithDrift_rejects_on_ne
    (g1 g2 g3 : Flag) (ob : ObRef) (rl : LinRef) (lk : ObId -> Evid) :
    cekRecheckWithDrift Cmp.ne g1 g2 g3 ob rl lk = Recheck.reject :=
  rfl

-- Substitution helper: from a proof that the comparison value IS `Cmp.ne`, conclude Reject — for any
-- comparison expression (e.g. an actual `fpCmp observedFp certFp`). `congrArg` rewrites the gate
-- input along the equality, then the `Cmp.ne` leaf reduces by rfl. Still axiom-free.
theorem cekRecheckWithDrift_rejects_of_ne
    (fpMatch : Cmp) (g1 g2 g3 : Flag) (ob : ObRef) (rl : LinRef) (lk : ObId -> Evid)
    (h : fpMatch = Cmp.ne) :
    cekRecheckWithDrift fpMatch g1 g2 g3 ob rl lk = Recheck.reject :=
  Eq.trans
    (congrArg (fun m => cekRecheckWithDrift m g1 g2 g3 ob rl lk) h)
    rfl

-- HEADLINE SAFETY, propositional fingerprint form (AXIOM-FREE). If the fingerprint re-derived from
-- the observed operands does NOT compare equal to the certificate's fingerprint, recheck Rejects.
-- `observedFp != certFp` is rendered, in the model's finite-comparison style, as `fpCmp = Cmp.ne`
-- (the computable witness of inequality). Universally over all downstream gates. No axiom.
theorem cekRecheck_rejects_on_fingerprint_mismatch
    (observedFp certFp : Fp)
    (g1 g2 g3 : Flag) (ob : ObRef) (rl : LinRef) (lk : ObId -> Evid)
    (h : fpCmp observedFp certFp = Cmp.ne) :
    cekRecheckWithDrift (fpCmp observedFp certFp) g1 g2 g3 ob rl lk = Recheck.reject :=
  cekRecheckWithDrift_rejects_of_ne (fpCmp observedFp certFp) g1 g2 g3 ob rl lk h

-- ===========================================================================================
-- COMPLETENESS DIRECTION (collision-resistance as an EXPLICIT HYPOTHESIS — NOT a global axiom).
-- ===========================================================================================

-- The equality predicates are wrapped as named `Prop` defs. (Clean's term-mode elaborator cannot
-- synthesize the sort of a raw `Eq` that appears in the ANTECEDENT of an implication-typed
-- hypothesis; wrapping each `Eq` behind a `def ... : Prop` lets the hypothesis elaborate. The wrapped
-- defs are definitionally the underlying equalities, so nothing about the meaning changes.)

-- "The FNV fingerprints of these two operand lists compare equal."
def fpMatches (o1 o2 : Operands) : Prop :=
  fpCmp (fnvFingerprint o1) (fnvFingerprint o2) = Cmp.eq

-- "These two operand lists are the same."
def opsSame (o1 o2 : Operands) : Prop := o1 = o2

-- "These two operand lists DIFFER" (operand drift) — Ne, in implication form.
def opsDiffer (o1 o2 : Operands) : Prop := opsSame o1 o2 -> False

-- COLLISION-RESISTANCE (the explicit TCB item). For ALL operand lists, if their FNV fingerprints
-- compare equal then the lists are equal — i.e. FNV is collision-FREE over the operand domain. This
-- is FALSE for the lossy model `fnvFingerprint` in general (finite codomain ⇒ pigeonhole collisions),
-- exactly as the real FNV-128 is not provably collision-free; that is WHY it is a hypothesis we
-- assume rather than a lemma we prove. It is the precise statement of what stays in the trusted
-- computing base. We NEVER discharge it with a global `axiom`, so the 3-axiom core is preserved.
def CollisionResistant : Prop :=
  (a : Operands) -> (b : Operands) -> fpMatches a b -> opsSame a b

-- Finite-`Cmp` fact: a comparison value that is NOT `Cmp.eq` IS `Cmp.ne`. Proven by case analysis
-- over the two-element `Cmp` (def-wrapped motive so the implication-typed branch elaborates).
def cmpIsEq (m : Cmp) : Prop := m = Cmp.eq
def cmpIsNe (m : Cmp) : Prop := m = Cmp.ne
def cmpNotEq (m : Cmp) : Prop := cmpIsEq m -> False
theorem cmp_not_eq_is_ne (m : Cmp) (h : cmpNotEq m) : cmpIsNe m :=
  Cmp.casesOn (motive := fun x => cmpNotEq x -> cmpIsNe x) m
    (fun he => False.elim (he rfl))
    (fun _ => rfl)
    h

-- HEADLINE COMPLETENESS. Under the explicit collision-resistance hypothesis, if the observed
-- operands DIFFER from the minted (certificate) operands, the drift-aware re-checker Rejects —
-- universally over every downstream gate. Proof: collision-resistance + drift gives that the
-- fingerprints do NOT compare equal; over the two-element `Cmp` that forces `Cmp.ne`; the axiom-free
-- safety substitution then yields Reject. The ONLY assumption is the named hypothesis — no axiom.
theorem drift_detected
    (observed minted : Operands)
    (g1 g2 g3 : Flag) (ob : ObRef) (rl : LinRef) (lk : ObId -> Evid)
    (h_cr : CollisionResistant)
    (h_diff : opsDiffer observed minted) :
    cekRecheckWithDrift (fpCmp (fnvFingerprint observed) (fnvFingerprint minted))
      g1 g2 g3 ob rl lk = Recheck.reject :=
  cekRecheckWithDrift_rejects_of_ne
    (fpCmp (fnvFingerprint observed) (fnvFingerprint minted)) g1 g2 g3 ob rl lk
    (cmp_not_eq_is_ne
      (fpCmp (fnvFingerprint observed) (fnvFingerprint minted))
      (fun hmatch => h_diff (h_cr observed minted hmatch)))

-- -------------------------------------------------------------------------------------------
-- CONCRETE WITNESSES mirroring the Rust differential bridge
-- (recheck_agrees_with_lean_model_on_minted_certificates, guard.rs ~1506): the SAME operands
-- recheck-delegate (and accept on a discharged elimination), while DRIFTED operands Reject. These
-- pin the abstract theorems to concrete operand lists, the way the §I/§II witnesses pin their gates.
-- -------------------------------------------------------------------------------------------

-- The bounds-check operand shape used in the Rust tests: [Reg 10, Reg 11, Imm 64] (guard.rs:1327).
def boundsOps : Operands :=
  Operands.cons (Operand.reg 10)
    (Operands.cons (Operand.reg 11)
      (Operands.cons (Operand.imm 64) Operands.nil))

-- A DRIFTED variant: the middle operand changed from a register to an immediate
-- ([Reg 10, Imm 11, Imm 64]). This is real operand drift the LOSSY model distinguishes by
-- construction (the per-operand tag changes the fold). NOTE on honesty: a same-TAG value-only drift
-- (e.g. the Rust test's Reg 11 -> Reg 999, guard.rs:1514) CAN collide in this finite-codomain model
-- — that is precisely the collision the `CollisionResistant` hypothesis assumes away, and which the
-- real 128-bit FNV is engineered (but not proven) to resist. The abstract `drift_detected` theorem
-- covers ALL drifts under that hypothesis; this concrete witness exhibits a drift the model catches
-- unconditionally.
def driftedOps : Operands :=
  Operands.cons (Operand.reg 10)
    (Operands.cons (Operand.imm 11)
      (Operands.cons (Operand.imm 64) Operands.nil))

-- Same operands compare equal: the fingerprint re-derived from the observed operands matches the
-- (same) certificate operands' fingerprint. (Concrete rfl: fnvFingerprint is closed-form here.)
theorem boundsOps_self_matches : fpCmp (fnvFingerprint boundsOps) (fnvFingerprint boundsOps) = Cmp.eq :=
  rfl

-- On the matching path the drift-aware re-checker is the §III re-checker and ACCEPTS the discharged
-- elimination — exactly the site `cekDecide` eliminates (cf. recheck_accept_discharged). Pure rfl.
theorem driftaware_accepts_discharged_same_operands :
    cekRecheckWithDrift (fpCmp (fnvFingerprint boundsOps) (fnvFingerprint boundsOps))
      Flag.yes Flag.yes Flag.yes (ObRef.obligation ObId.o1) LinRef.noLineage lkDischarged
      = Recheck.accept :=
  rfl

-- DRIFT witness: the drifted operands hash to a DIFFERENT fingerprint than the certificate's
-- (closed-form, so this is a real computed inequality, not an assumption)...
theorem driftedOps_mismatch : fpCmp (fnvFingerprint driftedOps) (fnvFingerprint boundsOps) = Cmp.ne :=
  rfl

-- ...so the drift-aware re-checker REJECTS the drifted elimination, regardless of the discharged
-- evidence that would otherwise justify it. This is operand-drift detection made concrete: even a
-- genuinely-discharged obligation does NOT save a certificate whose operands drifted. Pure rfl.
theorem driftaware_rejects_drifted_even_when_discharged :
    cekRecheckWithDrift (fpCmp (fnvFingerprint driftedOps) (fnvFingerprint boundsOps))
      Flag.yes Flag.yes Flag.yes (ObRef.obligation ObId.o1) LinRef.noLineage lkDischarged
      = Recheck.reject :=
  rfl


-- Checked FNV limb definitions for the production computation port.  The
-- composite definitions state the proof-facing operation.  The smaller
-- definitions below stay inside Trust's callable fragment; Rust composes them
-- in the same order, and the two composition theorems bind that emitted path
-- back to the composite definitions.  The finite Fp model above is an
-- abstraction; these definitions do not prove collision resistance.
-- The exact FNV-1a-128 byte step, represented by two UInt64 limbs.
-- The prime is 2^88 + 315. Multiplication carries are computed in base 2^32.
-- This is executable arithmetic, not a collision-resistance assumption.
def trust_cg_fnv128_step_lo (lo byte : UInt64) : UInt64 :=
  (lo ^^^ byte) * (315 : UInt64)

def trust_cg_fnv128_step_hi (hi lo byte : UInt64) : UInt64 :=
  let mixed : UInt64 := lo ^^^ byte
  let lowProduct : UInt64 := (mixed &&& 4294967295) * (315 : UInt64)
  let highProduct : UInt64 := (mixed >>> 32) * (315 : UInt64) + (lowProduct >>> 32)
  hi * (315 : UInt64) + mixed * (16777216 : UInt64) + (highProduct >>> 32)

-- Trust currently emits one raw bit operation at a time.  Keep those
-- operations in individual definitions and do the composition in the Rust
-- caller rather than asking the compiler to expand a nested bitwise body.
def trust_cg_fnv128_xor (lo byte : UInt64) : UInt64 := lo ^^^ byte

def trust_cg_fnv128_mask32 (value : UInt64) : UInt64 :=
  value &&& (4294967295 : UInt64)

def trust_cg_fnv128_shift32 (value : UInt64) : UInt64 := value >>> 32

def trust_cg_fnv128_mul315 (value : UInt64) : UInt64 :=
  value * (315 : UInt64)

-- Multiplication by 2^24 is the wrapping UInt64 realization of `<<< 24` and
-- is directly emittable.  The full source-value theorem below proves the
-- composite result, including this term, equals the FNV-1a-128 step.
def trust_cg_fnv128_mul_2pow24 (value : UInt64) : UInt64 :=
  value * (16777216 : UInt64)

def trust_cg_fnv128_add (left right : UInt64) : UInt64 := left + right

def trust_cg_fnv128_add3 (first second third : UInt64) : UInt64 :=
  first + second + third

theorem trust_cg_fnv128_step_lo_composition (lo byte : UInt64) :
    trust_cg_fnv128_mul315 (trust_cg_fnv128_xor lo byte) =
      trust_cg_fnv128_step_lo lo byte := by
  rfl

theorem trust_cg_fnv128_step_hi_composition (hi lo byte : UInt64) :
    let mixed := trust_cg_fnv128_xor lo byte
    let lowProduct := trust_cg_fnv128_mul315 (trust_cg_fnv128_mask32 mixed)
    let highProduct := trust_cg_fnv128_add
      (trust_cg_fnv128_mul315 (trust_cg_fnv128_shift32 mixed))
      (trust_cg_fnv128_shift32 lowProduct)
    trust_cg_fnv128_add3 (trust_cg_fnv128_mul315 hi)
      (trust_cg_fnv128_mul_2pow24 mixed)
      (trust_cg_fnv128_shift32 highProduct) =
        trust_cg_fnv128_step_hi hi lo byte := by
  rfl


-- The low base-2^32 multiplication partial fits the UInt64 carrier.
-- This is one arithmetic ingredient, not the full carry/multiply theorem
-- or proof of the emitted FNV consumer. The helper uses explicit induction
-- instead of the refused scaled-goal omega reconstruction.
namespace TrustCg.Fnv128Carry

theorem scale_pos (a b k : Nat) (h : a < b) : a * Nat.succ k < b * Nat.succ k := by
  induction k with
  | zero => simpa only [Nat.mul_one] using h
  | succ k ih =>
    exact @Nat.add_lt_add (a * Nat.succ k) (b * Nat.succ k) a b ih h

theorem scale315 (a b : Nat) (h : a < b) : a * 315 < b * 315 := by
  exact scale_pos a b 314 h

theorem low_partial_fits (x : Nat) :
    (x % 4294967296) * 315 < 18446744073709551616 := by
  have remainder_bound : x % 4294967296 < 4294967296 := by omega
  have scaled : (x % 4294967296) * 315 < 4294967296 * 315 := by
    exact scale315 (x % 4294967296) 4294967296 remainder_bound
  exact @Nat.lt_trans ((x % 4294967296) * 315) (4294967296 * 315)
    18446744073709551616 scaled (by decide)

end TrustCg.Fnv128Carry


-- Bounds for the high base-2^32 partial; the full carry/multiply identity
-- and the emitted caller connection remain separate obligations.

namespace TrustCg.Fnv128Carry

theorem le_add (n k : Nat) : n ≤ n + k := by
  induction k with
  | zero => exact Nat.le_refl n
  | succ k ih => exact Nat.le.step ih

theorem order_split (a b : Nat) : a ≤ b ∨ b < a := by
  induction a generalizing b with
  | zero => exact Or.inl (Nat.zero_le b)
  | succ a ih =>
    cases b with
    | zero => exact Or.inr (Nat.zero_lt_succ a)
    | succ b =>
      cases ih b with
      | inl hab => exact Or.inl (@Nat.succ_le_succ a b hab)
      | inr hba => exact Or.inr (@Nat.succ_lt_succ b a hba)

theorem division_identity (x a : Nat) : (x / a) * a + x % a = x := by
  simpa only [Nat.mul_comm] using (Nat.div_add_mod x a)

theorem div_lt_product (x a b : Nat) (bounded : x < b * a) : x / a < b := by
  have orderCases : b ≤ x / a ∨ x / a < b := order_split b (x / a)
  cases orderCases with
  | inl hle =>
    have product_le : b * a ≤ (x / a) * a :=
      @Nat.mul_le_mul b a (x / a) a hle (Nat.le_refl a)
    have floor_le : (x / a) * a ≤ x :=
      Eq.mp (congrArg (fun t : Nat => (x / a) * a ≤ t) (division_identity x a))
        (le_add ((x / a) * a) (x % a))
    have total : b * a ≤ x :=
      @Nat.le_trans (b * a) ((x / a) * a) x product_le floor_le
    have impossible : x < x := @Nat.lt_of_lt_of_le x (b * a) x bounded total
    exact False.elim ((Nat.lt_irrefl x) impossible)
  | inr hlt => exact hlt

theorem high_partial_fits (x : Nat) (bounded : x < 18446744073709551616) :
    (x / 4294967296) * 315 + ((x % 4294967296) * 315) / 4294967296
      < 18446744073709551616 := by
  have quotient : x / 4294967296 < 4294967296 :=
    div_lt_product x 4294967296 4294967296 bounded
  have remainder_bound : x % 4294967296 < 4294967296 := by omega
  have scaled : (x / 4294967296) * 315 < 4294967296 * 315 :=
    scale315 (x / 4294967296) 4294967296 quotient
  have carry : ((x % 4294967296) * 315) / 4294967296 < 315 :=
    div_lt_product ((x % 4294967296) * 315) 4294967296 315
      (scale315 (x % 4294967296) 4294967296 remainder_bound)
  have combined :
      (x / 4294967296) * 315 + ((x % 4294967296) * 315) / 4294967296
        < 4294967296 * 315 + 315 :=
    @Nat.add_lt_add ((x / 4294967296) * 315) (4294967296 * 315)
      (((x % 4294967296) * 315) / 4294967296) 315 scaled carry
  exact @Nat.lt_trans
    ((x / 4294967296) * 315 + ((x % 4294967296) * 315) / 4294967296)
    (4294967296 * 315 + 315) 18446744073709551616 combined (by decide)

end TrustCg.Fnv128Carry

namespace TrustCg.Fnv128Carry

theorem add_left_strict (a b k : Nat) (h : a < b) : k + a < k + b := by
  induction k with
  | zero => simpa only [Nat.zero_add] using h
  | succ k ih => simpa only [Nat.succ_add] using (@Nat.succ_lt_succ (k + a) (k + b) ih)

theorem successor_product (q a : Nat) : Nat.succ q * a = q * a + a := by
  simpa only [Nat.add_comm] using (Nat.succ_mul q a)

theorem small_remainder_lt_succ_product (q r a : Nat) (hr : r < a) :
    q * a + r < Nat.succ q * a := by
  exact Eq.mp
    (congrArg (fun v : Nat => q * a + r < v) (Eq.symm (successor_product q a)))
    (add_left_strict r a (q * a) hr)

theorem quotient_compare (q r d s a : Nat)
    (h : q * a + r = d * a + s) (hs : s < a) : q ≤ d := by
  cases order_split q d with
  | inl hqd => exact hqd
  | inr hdq =>
    have step : Nat.succ d ≤ q := hdq
    have scaled : Nat.succ d * a ≤ q * a :=
      @Nat.mul_le_mul (Nat.succ d) a q a step (Nat.le_refl a)
    have below : d * a + s < Nat.succ d * a :=
      small_remainder_lt_succ_product d s a hs
    have floor : q * a ≤ q * a + r := le_add (q * a) r
    have upper : Nat.succ d * a ≤ q * a + r :=
      @Nat.le_trans (Nat.succ d * a) (q * a) (q * a + r) scaled floor
    have strict : d * a + s < q * a + r :=
      @Nat.lt_of_lt_of_le (d * a + s) (Nat.succ d * a) (q * a + r) below upper
    have impossible : d * a + s < d * a + s :=
      Eq.mp (congrArg (fun v : Nat => d * a + s < v) h) strict
    exact False.elim ((Nat.lt_irrefl (d * a + s)) impossible)

theorem quotient_unique (q r d s a : Nat)
    (h : q * a + r = d * a + s) (hr : r < a) (hs : s < a) : q = d := by
  exact @Nat.le_antisymm q d
    (quotient_compare q r d s a h hs)
    (quotient_compare d s q r a (Eq.symm h) hr)

end TrustCg.Fnv128Carry

namespace TrustCg.Fnv128Carry

theorem add_exchange (a b c d : Nat) : (a + b) + (c + d) = (a + c) + (b + d) := by
  calc
    (a + b) + (c + d) = a + (b + (c + d)) := Nat.add_assoc a b (c + d)
    _ = a + ((b + c) + d) := congrArg (fun v : Nat => a + v) (Eq.symm (Nat.add_assoc b c d))
    _ = a + ((c + b) + d) := congrArg (fun v : Nat => a + (v + d)) (Nat.add_comm b c)
    _ = a + (c + (b + d)) := congrArg (fun v : Nat => a + v) (Nat.add_assoc c b d)
    _ = (a + c) + (b + d) := Eq.symm (Nat.add_assoc a c (b + d))

theorem add_mul_canonical (a b c : Nat) : (a + b) * c = a * c + b * c := by
  induction c with
  | zero => rfl
  | succ c ih =>
    change (a + b) * c + (a + b) = (a * c + a) + (b * c + b)
    exact Eq.trans (congrArg (fun v : Nat => v + (a + b)) ih)
      (add_exchange (a * c) (b * c) a b)

theorem swap_mul_right (a b c : Nat) : a * b * c = a * c * b := by
  exact Eq.trans (Nat.mul_assoc a b c)
    (Eq.trans (congrArg (fun v : Nat => a * v) (Nat.mul_comm b c))
      (Eq.symm (Nat.mul_assoc a c b)))

theorem carry_equation (x q r c s d t b p : Nat)
    (hx : q * b + r = x) (hr : c * b + s = r * p)
    (hh : d * b + t = q * p + c) :
    x * p = d * (b * b) + (t * b + s) := by
  calc
    x * p = (q * b + r) * p := congrArg (fun v : Nat => v * p) (Eq.symm hx)
    _ = (q * b) * p + r * p := add_mul_canonical (q * b) r p
    _ = (q * p) * b + r * p := congrArg (fun v : Nat => v + r * p) (swap_mul_right q b p)
    _ = (q * p) * b + (c * b + s) := congrArg (fun v : Nat => (q * p) * b + v) (Eq.symm hr)
    _ = ((q * p) * b + c * b) + s := Eq.symm (Nat.add_assoc ((q * p) * b) (c * b) s)
    _ = (q * p + c) * b + s := congrArg (fun v : Nat => v + s) (Eq.symm (add_mul_canonical (q * p) c b))
    _ = (d * b + t) * b + s := congrArg (fun v : Nat => v * b + s) (Eq.symm hh)
    _ = ((d * b) * b + t * b) + s := congrArg (fun v : Nat => v + s) (add_mul_canonical (d * b) t b)
    _ = (d * b) * b + (t * b + s) := Nat.add_assoc ((d * b) * b) (t * b) s
    _ = d * (b * b) + (t * b + s) := congrArg (fun v : Nat => v + (t * b + s)) (Nat.mul_assoc d b b)

theorem combined_remainder_bound (t s b : Nat) (ht : t < b) (hs : s < b) :
    t * b + s < b * b := by
  have upper : Nat.succ t * b ≤ b * b :=
    @Nat.mul_le_mul (Nat.succ t) b b b ht (Nat.le_refl b)
  exact @Nat.lt_of_lt_of_le (t * b + s) (Nat.succ t * b) (b * b)
    (small_remainder_lt_succ_product t s b hs) upper

theorem carry_exact (x : Nat) :
    ((x / 4294967296) * 315 + ((x % 4294967296) * 315) / 4294967296) / 4294967296
      = (x * 315) / 18446744073709551616 := by
  let q := x / 4294967296
  let r := x % 4294967296
  let c := (r * 315) / 4294967296
  let s := (r * 315) % 4294967296
  let d := (q * 315 + c) / 4294967296
  let t := (q * 315 + c) % 4294967296
  have hx : q * 4294967296 + r = x := division_identity x 4294967296
  have hr : c * 4294967296 + s = r * 315 := division_identity (r * 315) 4294967296
  have hh : d * 4294967296 + t = q * 315 + c := division_identity (q * 315 + c) 4294967296
  have hs : s < 4294967296 := @Nat.mod_lt (r * 315) 4294967296 (by decide)
  have ht : t < 4294967296 := @Nat.mod_lt (q * 315 + c) 4294967296 (by decide)
  have shape : x * 315 = d * 18446744073709551616 + (t * 4294967296 + s) :=
    carry_equation x q r c s d t 4294967296 315 hx hr hh
  have bounded : t * 4294967296 + s < 18446744073709551616 :=
    combined_remainder_bound t s 4294967296 ht hs
  have original := division_identity (x * 315) 18446744073709551616
  exact quotient_unique d (t * 4294967296 + s)
    ((x * 315) / 18446744073709551616) ((x * 315) % 18446744073709551616)
    18446744073709551616 (Eq.trans (Eq.symm shape) (Eq.symm original))
    bounded (@Nat.mod_lt (x * 315) 18446744073709551616 (by decide))

end TrustCg.Fnv128Carry

namespace TrustCg.Fnv128Carry

theorem mul_add_canonical (a b c : Nat) : a * (b + c) = a * b + a * c := by
  calc
    a * (b + c) = (b + c) * a := Nat.mul_comm a (b + c)
    _ = b * a + c * a := add_mul_canonical b c a
    _ = a * b + c * a := congrArg (fun v : Nat => v + c * a) (Nat.mul_comm b a)
    _ = a * b + a * c := congrArg (fun v : Nat => a * b + v) (Nat.mul_comm c a)

theorem mul_cross (a b c d : Nat) : (a * b) * (c * d) = (a * d) * (b * c) := by
  calc
    (a * b) * (c * d) = a * (b * (c * d)) := Nat.mul_assoc a b (c * d)
    _ = a * ((b * c) * d) := congrArg (fun v : Nat => a * v) (Eq.symm (Nat.mul_assoc b c d))
    _ = a * (d * (b * c)) := congrArg (fun v : Nat => a * v) (Nat.mul_comm (b * c) d)
    _ = (a * d) * (b * c) := Eq.symm (Nat.mul_assoc a d (b * c))

theorem collect_three (a b c m r : Nat) :
    a * m + (b * m + (c * m + r)) = (a + b + c) * m + r := by
  calc
    a * m + (b * m + (c * m + r)) = a * m + ((b * m + c * m) + r) :=
      congrArg (fun v : Nat => a * m + v) (Eq.symm (Nat.add_assoc (b * m) (c * m) r))
    _ = (a * m + (b * m + c * m)) + r := Eq.symm (Nat.add_assoc (a * m) (b * m + c * m) r)
    _ = ((a * m + b * m) + c * m) + r :=
      congrArg (fun v : Nat => v + r) (Eq.symm (Nat.add_assoc (a * m) (b * m) (c * m)))
    _ = ((a + b) * m + c * m) + r :=
      congrArg (fun v : Nat => (v + c * m) + r) (Eq.symm (add_mul_canonical a b m))
    _ = (a + b + c) * m + r :=
      congrArg (fun v : Nat => v + r) (Eq.symm (add_mul_canonical (a + b) c m))

theorem product_equation (hi lo m k p q r h t : Nat)
    (low : q * m + r = lo * p) (high : h * m + t = hi * p + lo * k + q) :
    (hi * m + lo) * (m * k + p) = (hi * k + h) * (m * m) + (t * m + r) := by
  calc
    (hi * m + lo) * (m * k + p) = (hi * m) * (m * k + p) + lo * (m * k + p) :=
      add_mul_canonical (hi * m) lo (m * k + p)
    _ = ((hi * m) * (m * k) + (hi * m) * p) + lo * (m * k + p) :=
      congrArg (fun v : Nat => v + lo * (m * k + p)) (mul_add_canonical (hi * m) (m * k) p)
    _ = ((hi * m) * (m * k) + (hi * m) * p) + (lo * (m * k) + lo * p) :=
      congrArg (fun v : Nat => ((hi * m) * (m * k) + (hi * m) * p) + v) (mul_add_canonical lo (m * k) p)
    _ = ((hi * k) * (m * m) + (hi * m) * p) + (lo * (m * k) + lo * p) :=
      congrArg (fun v : Nat => (v + (hi * m) * p) + (lo * (m * k) + lo * p)) (mul_cross hi m m k)
    _ = ((hi * k) * (m * m) + (hi * p) * m) + (lo * (m * k) + lo * p) :=
      congrArg (fun v : Nat => ((hi * k) * (m * m) + v) + (lo * (m * k) + lo * p)) (swap_mul_right hi m p)
    _ = ((hi * k) * (m * m) + (hi * p) * m) + ((lo * k) * m + lo * p) :=
      congrArg (fun v : Nat => ((hi * k) * (m * m) + (hi * p) * m) + (v + lo * p))
        (Eq.trans (Eq.symm (Nat.mul_assoc lo m k)) (swap_mul_right lo m k))
    _ = ((hi * k) * (m * m) + (hi * p) * m) + ((lo * k) * m + (q * m + r)) :=
      congrArg (fun v : Nat => ((hi * k) * (m * m) + (hi * p) * m) + ((lo * k) * m + v)) (Eq.symm low)
    _ = (hi * k) * (m * m) + ((hi * p) * m + ((lo * k) * m + (q * m + r))) :=
      Nat.add_assoc ((hi * k) * (m * m)) ((hi * p) * m) ((lo * k) * m + (q * m + r))
    _ = (hi * k) * (m * m) + ((hi * p + lo * k + q) * m + r) :=
      congrArg (fun v : Nat => (hi * k) * (m * m) + v) (collect_three (hi * p) (lo * k) q m r)
    _ = (hi * k) * (m * m) + ((h * m + t) * m + r) :=
      congrArg (fun v : Nat => (hi * k) * (m * m) + (v * m + r)) (Eq.symm high)
    _ = (hi * k) * (m * m) + (((h * m) * m + t * m) + r) :=
      congrArg (fun v : Nat => (hi * k) * (m * m) + (v + r)) (add_mul_canonical (h * m) t m)
    _ = (hi * k) * (m * m) + ((h * m) * m + (t * m + r)) :=
      congrArg (fun v : Nat => (hi * k) * (m * m) + v) (Nat.add_assoc ((h * m) * m) (t * m) r)
    _ = (hi * k) * (m * m) + (h * (m * m) + (t * m + r)) :=
      congrArg (fun v : Nat => (hi * k) * (m * m) + (v + (t * m + r))) (Nat.mul_assoc h m m)
    _ = ((hi * k) * (m * m) + h * (m * m)) + (t * m + r) :=
      Eq.symm (Nat.add_assoc ((hi * k) * (m * m)) (h * (m * m)) (t * m + r))
    _ = (hi * k + h) * (m * m) + (t * m + r) :=
      congrArg (fun v : Nat => v + (t * m + r)) (Eq.symm (add_mul_canonical (hi * k) h (m * m)))

theorem remainder_unique (q r d s a : Nat)
    (h : q * a + r = d * a + s) (hr : r < a) (hs : s < a) : r = s := by
  have same : q = d := quotient_unique q r d s a h hr hs
  have fixed : d * a + r = d * a + s :=
    Eq.mp (congrArg (fun v : Nat => v * a + r = d * a + s) same) h
  exact @Nat.add_left_cancel (d * a) r s fixed

theorem multiply_split (hi lo : Nat) :
    ((hi * 18446744073709551616 + lo) * 309485009821345068724781371)
        % 340282366920938463463374607431768211456
      = (lo * 315) % 18446744073709551616
        + 18446744073709551616 * ((hi * 315 + lo * 16777216
            + (lo * 315) / 18446744073709551616) % 18446744073709551616) := by
  let q := (lo * 315) / 18446744073709551616
  let r := (lo * 315) % 18446744073709551616
  let h := (hi * 315 + lo * 16777216 + q) / 18446744073709551616
  let t := (hi * 315 + lo * 16777216 + q) % 18446744073709551616
  let n := (hi * 18446744073709551616 + lo) * 309485009821345068724781371
  have low : q * 18446744073709551616 + r = lo * 315 :=
    division_identity (lo * 315) 18446744073709551616
  have high : h * 18446744073709551616 + t = hi * 315 + lo * 16777216 + q :=
    division_identity (hi * 315 + lo * 16777216 + q) 18446744073709551616
  have hr : r < 18446744073709551616 :=
    @Nat.mod_lt (lo * 315) 18446744073709551616 (by decide)
  have ht : t < 18446744073709551616 :=
    @Nat.mod_lt (hi * 315 + lo * 16777216 + q) 18446744073709551616 (by decide)
  have shape : n = (hi * 16777216 + h) * 340282366920938463463374607431768211456
      + (t * 18446744073709551616 + r) :=
    product_equation hi lo 18446744073709551616 16777216 315 q r h t low high
  have bounded : t * 18446744073709551616 + r < 340282366920938463463374607431768211456 :=
    combined_remainder_bound t r 18446744073709551616 ht hr
  have original := division_identity n 340282366920938463463374607431768211456
  have same : n % 340282366920938463463374607431768211456 = t * 18446744073709551616 + r :=
    remainder_unique (n / 340282366920938463463374607431768211456)
      (n % 340282366920938463463374607431768211456) (hi * 16777216 + h)
      (t * 18446744073709551616 + r) 340282366920938463463374607431768211456
      (Eq.trans original shape)
      (@Nat.mod_lt n 340282366920938463463374607431768211456 (by decide)) bounded
  exact Eq.trans same
    (Eq.trans (Nat.add_comm (t * 18446744073709551616) r)
      (congrArg (fun v : Nat => r + v) (Nat.mul_comm t 18446744073709551616)))

end TrustCg.Fnv128Carry

namespace TrustCg.Fnv128Carry

theorem low_source_value (lo byte : UInt64) :
    (trust_cg_fnv128_step_lo lo byte).toNat
      = (((lo ^^^ byte).toNat * 315) % 18446744073709551616) := by
  rfl

end TrustCg.Fnv128Carry

-- Constructive descent prerequisites for the remaining bitwise mask refinement.
namespace TrustCg.Fnv128Carry

theorem nat_strong_induction (P : Nat → Prop)
    (step : ∀ n, (∀ m, m < n → P m) → P n) (n : Nat) : P n := by
  have bound : ∀ k, ∀ m, m < k → P m := by
    intro k
    induction k with
    | zero =>
      intro m hm
      exact False.elim ((Nat.lt_irrefl m) (@Nat.lt_of_lt_of_le m 0 m hm (Nat.zero_le m)))
    | succ k ih =>
      intro m hm
      cases order_split k m with
      | inl above =>
        have same_succ : Nat.succ m = Nat.succ k :=
          @Nat.le_antisymm (Nat.succ m) (Nat.succ k) hm (@Nat.succ_le_succ k m above)
        have same : m = k := congrArg Nat.pred same_succ
        exact Eq.mp (congrArg P (Eq.symm same)) (step k ih)
      | inr below => exact ih m below
  exact bound (Nat.succ n) n (Nat.lt_succ_self n)

theorem mod_add_period (x a : Nat) (positive : 0 < a) :
    (x + a) % a = x % a := by
  have shifted : (Nat.succ (x / a)) * a + x % a = x + a := by
    calc
      (Nat.succ (x / a)) * a + x % a = ((x / a) * a + a) + x % a :=
        congrArg (fun v : Nat => v + x % a) (successor_product (x / a) a)
      _ = (x / a) * a + (a + x % a) := Nat.add_assoc ((x / a) * a) a (x % a)
      _ = (x / a) * a + (x % a + a) :=
        congrArg (fun v : Nat => (x / a) * a + v) (Nat.add_comm a (x % a))
      _ = ((x / a) * a + x % a) + a := Eq.symm (Nat.add_assoc ((x / a) * a) (x % a) a)
      _ = x + a := congrArg (fun v : Nat => v + a) (division_identity x a)
  have same : (Nat.succ (x / a)) * a + x % a = ((x + a) / a) * a + (x + a) % a :=
    Eq.trans shifted (Eq.symm (division_identity (x + a) a))
  exact Eq.symm (remainder_unique (Nat.succ (x / a)) (x % a)
    ((x + a) / a) ((x + a) % a) a same (@Nat.mod_lt x a positive) (@Nat.mod_lt (x + a) a positive))

-- Keep the varying lower bound in the induction motive explicitly.
theorem le_add_witness_bounded (k : Nat) :
    ∀ start, start ≤ k → ∃ y, y + start = k := by
  induction k with
  | zero =>
    intro start hs
    have same : start = 0 := @Nat.le_antisymm start 0 hs (Nat.zero_le start)
    exact Exists.intro 0 (Eq.trans (Nat.zero_add start) same)
  | succ k ih =>
    intro start hs
    cases order_split start k with
    | inl below =>
      cases ih start below with
      | intro y same =>
        exact Exists.intro (Nat.succ y)
          (Eq.trans (Nat.succ_add y start) (congrArg Nat.succ same))
    | inr above =>
      have same : start = Nat.succ k := @Nat.le_antisymm start (Nat.succ k) hs above
      exact Exists.intro 0 (Eq.trans (Nat.zero_add start) same)

theorem le_add_witness (a x : Nat) (h : a ≤ x) : ∃ y, y + a = x := by
  exact le_add_witness_bounded x a h

theorem mod_descent (x a : Nat) (positive : 0 < a) :
    x < a ∨ ∃ y, y < x ∧ y + a = x ∧ x % a = y % a := by
  cases order_split a x with
  | inl enough =>
    cases le_add_witness a x enough with
    | intro y joined =>
      have smaller : y < y + a := add_left_strict 0 a y positive
      have decreases : y < x := Eq.mp (congrArg (fun v : Nat => y < v) joined) smaller
      have same : x % a = y % a :=
        Eq.mp (congrArg (fun v : Nat => v % a = y % a) joined) (mod_add_period y a positive)
      exact Or.inr (Exists.intro y (And.intro decreases (And.intro joined same)))
  | inr below => exact Or.inl below

theorem div_product (x a b : Nat) (apos : 0 < a) (bpos : 0 < b) :
    x / (b * a) = (x / a) / b := by
  let q := (x / a) / b
  let r := (x / a) % b
  let s := x % a
  have rs : s < a := @Nat.mod_lt x a apos
  have rb : r < b := @Nat.mod_lt (x / a) b bpos
  have small : r * a + s < Nat.succ r * a := small_remainder_lt_succ_product r s a rs
  have scaled : Nat.succ r * a ≤ b * a :=
    @Nat.mul_le_mul (Nat.succ r) a b a rb (Nat.le_refl a)
  have bound : r * a + s < b * a :=
    @Nat.lt_of_lt_of_le (r * a + s) (Nat.succ r * a) (b * a) small scaled
  have product_positive : 0 < b * a := by
    cases order_split (b * a) 0 with
    | inl zero =>
      have bad : r * a + s < r * a + s :=
        @Nat.lt_of_lt_of_le (r * a + s) (b * a) (r * a + s) bound
          (@Nat.le_trans (b * a) 0 (r * a + s) zero (Nat.zero_le (r * a + s)))
      exact False.elim ((Nat.lt_irrefl (r * a + s)) bad)
    | inr positive => exact positive
  have expansion : q * (b * a) + (r * a + s) = x := by
    calc
      q * (b * a) + (r * a + s) = (q * b) * a + (r * a + s) :=
        congrArg (fun v : Nat => v + (r * a + s)) (Eq.symm (Nat.mul_assoc q b a))
      _ = ((q * b) * a + r * a) + s := Eq.symm (Nat.add_assoc ((q * b) * a) (r * a) s)
      _ = (q * b + r) * a + s :=
        congrArg (fun v : Nat => v + s) (Eq.symm (add_mul_canonical (q * b) r a))
      _ = (x / a) * a + s :=
        congrArg (fun v : Nat => v * a + s) (division_identity (x / a) b)
      _ = x := division_identity x a
  have same : q * (b * a) + (r * a + s) = (x / (b * a)) * (b * a) + x % (b * a) :=
    Eq.trans expansion (Eq.symm (division_identity x (b * a)))
  exact Eq.symm (quotient_unique q (r * a + s) (x / (b * a)) (x % (b * a))
    (b * a) same bound (@Nat.mod_lt x (b * a) product_positive))

theorem bit_quotient (x i : Nat) :
    Nat.testBit x i = decide ((x / 2^i) % 2 = 1) := by
  first
  | exact Nat.testBit_eq_decide_div_mod_eq
  | have twice : forall (t : Nat), t * 2 = t + t := by
      intro t
      first
      | exact Nat.mul_two t
      | rfl
      | change (0 + t) + t = t + t
        exact congrArg (fun v : Nat => v + t) (Nat.zero_add t)
    have part_bound : forall (t : Nat), Nat.div2Par t < 2 := by
      intro t
      cases Nat.div2Par_zero_or_one t with
      | inl zero => exact Eq.mp (congrArg (fun v : Nat => v < 2) (Eq.symm zero)) (by decide)
      | inr one => exact Eq.mp (congrArg (fun v : Nat => v < 2) (Eq.symm one)) (by decide)
    have joined : forall (t : Nat), Nat.div2 t * 2 + Nat.div2Par t = t := fun (t : Nat) =>
      Eq.trans (congrArg (fun v : Nat => v + Nat.div2Par t) (twice (Nat.div2 t)))
        (Eq.symm (Nat.div2_rejoin t))
    have same : forall (t : Nat), Nat.div2 t * 2 + Nat.div2Par t = (t / 2) * 2 + t % 2 := fun (t : Nat) =>
      Eq.trans (joined t) (Eq.symm (division_identity t 2))
    have half : forall (t : Nat), Nat.div2 t = t / 2 := fun (t : Nat) =>
      quotient_unique (Nat.div2 t) (Nat.div2Par t) (t / 2) (t % 2) 2
        (same t) (part_bound t) (@Nat.mod_lt t 2 (by decide))
    have parity : forall (t : Nat), Nat.div2Par t = t % 2 := fun (t : Nat) =>
      remainder_unique (Nat.div2 t) (Nat.div2Par t) (t / 2) (t % 2) 2
        (same t) (part_bound t) (@Nat.mod_lt t 2 (by decide))
    have bit_zero : forall (t : Nat), Nat.testBit t 0 = decide (t % 2 = 1) := by
      intro t
      change Nat.toBoolPar (Nat.div2Par t) = decide (t % 2 = 1)
      cases Nat.div2Par_zero_or_one t with
      | inl zero =>
        have rem : t % 2 = 0 := Eq.trans (Eq.symm (parity t)) zero
        rw [zero, rem]
      | inr one =>
        have rem : t % 2 = 1 := Eq.trans (Eq.symm (parity t)) one
        rw [one, rem]
    have pow_positive : ∀ n, 0 < 2^n := by
      intro n
      induction n with
      | zero => decide
      | succ n ih =>
        have positive : 0 < 2^n + 2^n :=
          @Nat.lt_of_lt_of_le 0 (2^n) (2^n + 2^n) ih (le_add (2^n) (2^n))
        change 0 < (2^n) * 2
        exact Eq.mp (congrArg (fun v : Nat => 0 < v) (Eq.symm (twice (2^n)))) positive
    have divide_one : forall (t : Nat), t / 1 = t := by
      intro t
      have eq : t * 1 + 0 = (t / 1) * 1 + t % 1 :=
        Eq.trans (Nat.mul_one t) (Eq.symm (division_identity t 1))
      exact Eq.symm (quotient_unique t 0 (t / 1) (t % 1) 1 eq (by decide) (@Nat.mod_lt t 1 (by decide)))
    induction i generalizing x with
    | zero =>
      exact Eq.trans (bit_zero x)
        (Eq.symm (congrArg (fun v : Nat => decide (v % 2 = 1)) (divide_one x)))
    | succ i ih =>
      change Nat.testBit (Nat.div2 x) i = decide ((x / 2^(Nat.succ i)) % 2 = 1)
      have quot : Nat.div2 x / 2^i = x / 2^(Nat.succ i) :=
        Eq.trans (congrArg (fun v : Nat => v / 2^i) (half x))
          (Eq.symm (div_product x 2 (2^i) (by decide) (pow_positive i)))
      exact Eq.trans (ih (Nat.div2 x)) (congrArg (fun v : Nat => decide (v % 2 = 1)) quot)

theorem mod_product (x a b : Nat) (apos : 0 < a) (bpos : 0 < b) :
    x % (b * a) = ((x / a) % b) * a + x % a := by
  let q := (x / a) / b
  let r := (x / a) % b
  let s := x % a
  have rs : s < a := @Nat.mod_lt x a apos
  have rb : r < b := @Nat.mod_lt (x / a) b bpos
  have small : r * a + s < Nat.succ r * a := small_remainder_lt_succ_product r s a rs
  have scaled : Nat.succ r * a ≤ b * a :=
    @Nat.mul_le_mul (Nat.succ r) a b a rb (Nat.le_refl a)
  have bound : r * a + s < b * a :=
    @Nat.lt_of_lt_of_le (r * a + s) (Nat.succ r * a) (b * a) small scaled
  have product_positive : 0 < b * a := by
    cases order_split (b * a) 0 with
    | inl zero =>
      have bad : r * a + s < r * a + s :=
        @Nat.lt_of_lt_of_le (r * a + s) (b * a) (r * a + s) bound
          (@Nat.le_trans (b * a) 0 (r * a + s) zero (Nat.zero_le (r * a + s)))
      exact False.elim ((Nat.lt_irrefl (r * a + s)) bad)
    | inr positive => exact positive
  have expansion : q * (b * a) + (r * a + s) = x := by
    calc
      q * (b * a) + (r * a + s) = (q * b) * a + (r * a + s) :=
        congrArg (fun v : Nat => v + (r * a + s)) (Eq.symm (Nat.mul_assoc q b a))
      _ = ((q * b) * a + r * a) + s := Eq.symm (Nat.add_assoc ((q * b) * a) (r * a) s)
      _ = (q * b + r) * a + s :=
        congrArg (fun v : Nat => v + s) (Eq.symm (add_mul_canonical (q * b) r a))
      _ = (x / a) * a + s :=
        congrArg (fun v : Nat => v * a + s) (division_identity (x / a) b)
      _ = x := division_identity x a
  have same : q * (b * a) + (r * a + s) = (x / (b * a)) * (b * a) + x % (b * a) :=
    Eq.trans expansion (Eq.symm (division_identity x (b * a)))
  exact Eq.symm (remainder_unique q (r * a + s) (x / (b * a)) (x % (b * a))
    (b * a) same bound (@Nat.mod_lt x (b * a) product_positive))

theorem mod_product_parts (x a b : Nat) (apos : 0 < a) (bpos : 0 < b) :
    (x % (b * a)) / a = (x / a) % b ∧ (x % (b * a)) % a = x % a := by
  have same : ((x / a) % b) * a + x % a =
      ((x % (b * a)) / a) * a + (x % (b * a)) % a :=
    Eq.trans (Eq.symm (mod_product x a b apos bpos))
      (Eq.symm (division_identity (x % (b * a)) a))
  have low : x % a < a := @Nat.mod_lt x a apos
  have other : (x % (b * a)) % a < a := @Nat.mod_lt (x % (b * a)) a apos
  exact And.intro
    (Eq.symm (quotient_unique ((x / a) % b) (x % a) ((x % (b * a)) / a)
      ((x % (b * a)) % a) a same low other))
    (Eq.symm (remainder_unique ((x / a) % b) (x % a) ((x % (b * a)) / a)
      ((x % (b * a)) % a) a same low other))

theorem two_power_positive (n : Nat) : 0 < 2^n := by
  have twice : forall (t : Nat), t * 2 = t + t := by
    intro t
    first
    | exact Nat.mul_two t
    | rfl
    | change (0 + t) + t = t + t
      exact congrArg (fun v : Nat => v + t) (Nat.zero_add t)
  induction n with
  | zero => decide
  | succ n ih =>
    have positive : 0 < 2^n + 2^n :=
      @Nat.lt_of_lt_of_le 0 (2^n) (2^n + 2^n) ih (le_add (2^n) (2^n))
    change 0 < (2^n) * 2
    exact Eq.mp (congrArg (fun v : Nat => 0 < v) (Eq.symm (twice (2^n)))) positive

theorem divide_one (t : Nat) : t / 1 = t := by
  have same : t * 1 + 0 = (t / 1) * 1 + t % 1 :=
    Eq.trans (Nat.mul_one t) (Eq.symm (division_identity t 1))
  exact Eq.symm (quotient_unique t 0 (t / 1) (t % 1) 1 same
    (by decide) (@Nat.mod_lt t 1 (by decide)))

theorem bit_zero_quotient (x : Nat) : Nat.testBit x 0 = decide (x % 2 = 1) :=
  Eq.trans (bit_quotient x 0)
    (congrArg (fun v : Nat => decide (v % 2 = 1)) (divide_one x))

theorem bit_succ_quotient (x i : Nat) :
    Nat.testBit x (Nat.succ i) = Nat.testBit (x / 2) i := by
  have quot : x / 2^(Nat.succ i) = (x / 2) / 2^i :=
    div_product x 2 (2^i) (by decide) (two_power_positive i)
  have parity : decide ((x / 2^(Nat.succ i)) % 2 = 1) =
      decide (((x / 2) / 2^i) % 2 = 1) :=
    congrArg (fun v : Nat => decide (v % 2 = 1)) quot
  exact Eq.trans (bit_quotient x (Nat.succ i))
    (Eq.trans parity (Eq.symm (bit_quotient (x / 2) i)))

theorem bit_mod_pow (x j i : Nat) :
    Nat.testBit (x % 2^j) i = (decide (i < j) && Nat.testBit x i) := by
  induction j generalizing x i with
  | zero =>
    have bound : x % 1 < 1 := @Nat.mod_lt x 1 (by decide)
    have rem : x % 1 = 0 :=
      @Nat.le_antisymm (x % 1) 0
        (@Nat.le_of_succ_le_succ (x % 1) 0 bound) (Nat.zero_le (x % 1))
    have never : ¬ i < 0 := fun h =>
      (Nat.lt_irrefl i) (@Nat.lt_of_lt_of_le i 0 i h (Nat.zero_le i))
    have mask : decide (i < 0) = false := by
      cases h : decide (i < 0) with
      | false => rfl
      | true => exact False.elim (never (of_decide_eq_true h))
    rw [mask]
    exact Eq.trans (congrArg (fun v : Nat => Nat.testBit v i) rem) (by
      first
      | exact Nat.testBit_zero_eq_false i
      | exact Nat.zero_testBit i)
  | succ j ih =>
    have parts := mod_product_parts x 2 (2^j) (by decide) (two_power_positive j)
    cases i with
    | zero =>
      have mask : decide (0 < Nat.succ j) = true := by
        cases h : decide (0 < Nat.succ j) with
        | false => exact False.elim ((of_decide_eq_false h) (Nat.zero_lt_succ j))
        | true => rfl
      rw [mask]
      exact Eq.trans (bit_zero_quotient (x % 2^(Nat.succ j)))
        (Eq.trans (congrArg (fun v : Nat => decide (v = 1)) parts.right)
          (Eq.symm (bit_zero_quotient x)))
    | succ i =>
      have comparison : decide (Nat.succ i < Nat.succ j) = decide (i < j) := by
        cases lhs : decide (Nat.succ i < Nat.succ j) with
        | false =>
          cases rhs : decide (i < j) with
          | false => rfl
          | true => exact False.elim ((of_decide_eq_false lhs)
              (@Nat.succ_lt_succ i j (of_decide_eq_true rhs)))
        | true =>
          cases rhs : decide (i < j) with
          | false => exact False.elim ((of_decide_eq_false rhs)
              (@Nat.le_of_succ_le_succ (Nat.succ i) j (of_decide_eq_true lhs)))
          | true => rfl
      rw [comparison]
      calc
        Nat.testBit (x % 2^(Nat.succ j)) (Nat.succ i) =
            Nat.testBit ((x % 2^(Nat.succ j)) / 2) i :=
          bit_succ_quotient (x % 2^(Nat.succ j)) i
        _ = Nat.testBit ((x / 2) % 2^j) i :=
          congrArg (fun v : Nat => Nat.testBit v i) parts.left
        _ = (decide (i < j) && Nat.testBit (x / 2) i) := ih (x / 2) i
        _ = (decide (i < j) && Nat.testBit x (Nat.succ i)) :=
          congrArg (fun v : Bool => decide (i < j) && v) (Eq.symm (bit_succ_quotient x i))

-- Constructive quotient and parity of an odd natural; no bitwise assumption.
theorem odd_parts (t : Nat) : (t * 2 + 1) / 2 = t ∧ (t * 2 + 1) % 2 = 1 := by
  have same : t * 2 + 1 = ((t * 2 + 1) / 2) * 2 + (t * 2 + 1) % 2 :=
    Eq.symm (division_identity (t * 2 + 1) 2)
  have low : 1 < 2 := by decide
  have other : (t * 2 + 1) % 2 < 2 := @Nat.mod_lt (t * 2 + 1) 2 (by decide)
  exact And.intro
    (Eq.symm (quotient_unique t 1 ((t * 2 + 1) / 2) ((t * 2 + 1) % 2) 2 same low other))
    (Eq.symm (remainder_unique t 1 ((t * 2 + 1) / 2) ((t * 2 + 1) % 2) 2 same low other))

-- Expose the actual predecessor rather than assuming a subtraction law.
theorem two_power_predecessor (n : Nat) :
    ∃ m, m + 1 = 2^n ∧ 2^n - 1 = m := by
  cases le_add_witness 1 (2^n) (two_power_positive n) with
  | intro m joined =>
    have predecessor : 2^n - 1 = m :=
      Eq.trans (congrArg (fun v : Nat => v - 1) (Eq.symm joined)) (by rfl)
    exact Exists.intro m (And.intro joined predecessor)

-- The all-ones mask gains a final one bit when the width increases.
theorem two_power_predecessor_step (n : Nat) :
    2^(Nat.succ n) - 1 = (2^n - 1) * 2 + 1 := by
  cases two_power_predecessor n with
  | intro m parts =>
    have doubled : 2^(Nat.succ n) = Nat.succ (m * 2 + 1) := by
      calc
        2^(Nat.succ n) = (m + 1) * 2 :=
          congrArg (fun v : Nat => v * 2) (Eq.symm parts.left)
        _ = m * 2 + 1 * 2 := add_mul_canonical m 1 2
        _ = Nat.succ (m * 2 + 1) := by rfl
    have predecessor : 2^(Nat.succ n) - 1 = m * 2 + 1 :=
      Eq.trans (congrArg (fun v : Nat => v - 1) doubled) (by rfl)
    exact Eq.trans predecessor
      (congrArg (fun v : Nat => v * 2 + 1) (Eq.symm parts.right))


theorem bit_power_predecessor (n i : Nat) :
    Nat.testBit (2^n - 1) i = decide (i < n) := by
  have never : forall (k : Nat), decide (k < 0) = false := by
    intro k
    have impossible : ¬ k < 0 := fun h =>
      (Nat.lt_irrefl k) (@Nat.lt_of_lt_of_le k 0 k h (Nat.zero_le k))
    cases h : decide (k < 0) with
    | false => rfl
    | true => exact False.elim (impossible (of_decide_eq_true h))
  have positive : forall (k : Nat), decide (0 < Nat.succ k) = true := by
    intro k
    cases h : decide (0 < Nat.succ k) with
    | false => exact False.elim ((of_decide_eq_false h) (Nat.zero_lt_succ k))
    | true => rfl
  have successor : forall (a c : Nat), decide (Nat.succ a < Nat.succ c) = decide (a < c) := by
    intro a c
    cases lhs : decide (Nat.succ a < Nat.succ c) with
    | false =>
      cases rhs : decide (a < c) with
      | false => rfl
      | true => exact False.elim ((of_decide_eq_false lhs)
          (@Nat.succ_lt_succ a c (of_decide_eq_true rhs)))
    | true =>
      cases rhs : decide (a < c) with
      | false => exact False.elim ((of_decide_eq_false rhs)
          (@Nat.le_of_succ_le_succ (Nat.succ a) c (of_decide_eq_true lhs)))
      | true => rfl
  induction n generalizing i with
  | zero =>
    have bits : Nat.testBit 0 i = false := by
      first
      | exact Nat.testBit_zero_eq_false i
      | exact Nat.zero_testBit i
    exact Eq.trans bits (Eq.symm (never i))
  | succ n ih =>
    have step : 2^(Nat.succ n) - 1 = (2^n - 1) * 2 + 1 :=
      two_power_predecessor_step n
    have odd := odd_parts (2^n - 1)
    cases i with
    | zero =>
      have parity : (2^(Nat.succ n) - 1) % 2 = 1 :=
        Eq.trans (congrArg (fun v : Nat => v % 2) step) odd.right
      have bits : Nat.testBit (2^(Nat.succ n) - 1) 0 = true :=
        Eq.trans (bit_zero_quotient (2^(Nat.succ n) - 1))
          (congrArg (fun v : Nat => decide (v = 1)) parity)
      exact Eq.trans bits (Eq.symm (positive n))
    | succ i =>
      calc
        Nat.testBit (2^(Nat.succ n) - 1) (Nat.succ i) =
            Nat.testBit ((2^(Nat.succ n) - 1) / 2) i :=
          bit_succ_quotient (2^(Nat.succ n) - 1) i
        _ = Nat.testBit (((2^n - 1) * 2 + 1) / 2) i :=
          congrArg (fun v : Nat => Nat.testBit (v / 2) i) step
        _ = Nat.testBit (2^n - 1) i :=
          congrArg (fun v : Nat => Nat.testBit v i) odd.left
        _ = decide (i < n) := ih i
        _ = decide (Nat.succ i < Nat.succ n) := Eq.symm (successor i n)

-- Equality of the actual checked bitwise operation and arithmetic remainder.
theorem and_power_mask (x n : Nat) : Nat.land x (2^n - 1) = x % 2^n := by
  apply Nat.eq_of_testBit_eq
  intro i
  have comm : forall (a b : Bool), (a && b) = (b && a) := by
    intro a b
    cases a <;> cases b <;> rfl
  have emitted : Nat.testBit (Nat.land x (2^n - 1)) i =
      (Nat.testBit x i && Nat.testBit (2^n - 1) i) :=
    Nat.testBit_and x (2^n - 1) i
  have masked : (Nat.testBit x i && Nat.testBit (2^n - 1) i) =
      (Nat.testBit x i && decide (i < n)) :=
    congrArg (fun v : Bool => Nat.testBit x i && v) (bit_power_predecessor n i)
  exact Eq.trans emitted (Eq.trans masked
    (Eq.trans (comm (Nat.testBit x i) (decide (i < n)))
      (Eq.symm (bit_mod_pow x n i))))


-- The actual UInt64 low-half mask used by the FNV source definition.
theorem uint64_mask32_value (x : UInt64) :
    (x &&& (4294967295 : UInt64)).toNat = x.toNat % 4294967296 := by
  first
  | exact Eq.trans (UInt64.toNat_and x (4294967295 : UInt64))
      (and_power_mask x.toNat 32)
  | change (Nat.land x.toNat 4294967295) % 18446744073709551616 =
      x.toNat % 4294967296
    have masked : Nat.land x.toNat 4294967295 = x.toNat % 4294967296 :=
      and_power_mask x.toNat 32
    have bound : x.toNat % 4294967296 < 18446744073709551616 :=
      @Nat.lt_trans (x.toNat % 4294967296) 4294967296 18446744073709551616
        (@Nat.mod_lt x.toNat 4294967296 (by decide)) (by decide)
    exact Eq.trans (congrArg (fun v : Nat => v % 18446744073709551616) masked)
      (@Nat.mod_eq_of_lt (x.toNat % 4294967296) 18446744073709551616 bound)

-- The actual UInt64 high-half shift used by the FNV source definition.
theorem uint64_shift32_value (x : UInt64) :
    (x >>> (32 : UInt64)).toNat = x.toNat / 4294967296 := by
  first
  | exact Eq.trans (UInt64.toNat_shiftRight x (32 : UInt64))
      (Nat.shiftRight_eq_div_pow x.toNat 32)
  | change (x.toNat / 4294967296) % 18446744073709551616 =
      x.toNat / 4294967296
    have bound : x.toNat / 4294967296 < 18446744073709551616 :=
      @Nat.lt_of_le_of_lt (x.toNat / 4294967296) x.toNat 18446744073709551616
        (Nat.div_le_self x.toNat 4294967296) (UInt64.toNat_lt x)
    exact @Nat.mod_eq_of_lt (x.toNat / 4294967296) 18446744073709551616 bound

end TrustCg.Fnv128Carry

namespace TrustCg.Fnv128Carry

theorem shift_left_power (x n : Nat) : Nat.shiftLeft x n = x * 2^n := by
  first
  | exact Nat.shiftLeft_eq x n
  | induction n with
    | zero => exact Eq.symm (Nat.mul_one x)
    | succ n ih =>
      change Nat.shiftLeft x n * 2 = x * ((2^n) * 2)
      exact Eq.trans (congrArg (fun v : Nat => v * 2) ih) (Nat.mul_assoc x (2^n) 2)

theorem uint64_shift24_value (x : UInt64) :
    (x <<< (24 : UInt64)).toNat = (x.toNat * 16777216) % 18446744073709551616 := by
  first
  | exact Eq.trans (UInt64.toNat_shiftLeft x (24 : UInt64))
      (congrArg (fun v : Nat => v % 18446744073709551616) (shift_left_power x.toNat 24))
  | have shifted : Nat.shiftLeft x.toNat 24 = x.toNat * 16777216 :=
      shift_left_power x.toNat 24
    change (Nat.shiftLeft x.toNat 24) % 18446744073709551616 =
      (x.toNat * 16777216) % 18446744073709551616
    rw [shifted]

theorem uint64_add_value (a b : UInt64) :
    (a + b).toNat = (a.toNat + b.toNat) % 18446744073709551616 := by
  first
  | rfl
  | exact UInt64.toNat_add a b

theorem uint64_mul_value (a b : UInt64) :
    (a * b).toNat = (a.toNat * b.toNat) % 18446744073709551616 := by
  first
  | rfl
  | exact UInt64.toNat_mul a b

theorem mod_add_multiple (x a k : Nat) (positive : 0 < a) :
    (x + k * a) % a = x % a := by
  induction k with
  | zero => simpa only [Nat.zero_mul, Nat.add_zero]
  | succ k ih =>
    have expanded : x + Nat.succ k * a = (x + k * a) + a :=
      Eq.trans (congrArg (fun v : Nat => x + v) (successor_product k a))
        (Eq.symm (Nat.add_assoc x (k * a) a))
    exact Eq.trans (congrArg (fun v : Nat => v % a) expanded)
      (Eq.trans (mod_add_period (x + k * a) a positive) ih)

theorem mod_remove_left (x y m : Nat) (positive : 0 < m) :
    (x + y) % m = (x % m + y) % m := by
  have expanded : x + y = (x % m + y) + (x / m) * m := by
    calc
      x + y = ((x / m) * m + x % m) + y :=
        congrArg (fun v : Nat => v + y) (Eq.symm (division_identity x m))
      _ = (x / m) * m + (x % m + y) := Nat.add_assoc ((x / m) * m) (x % m) y
      _ = (x % m + y) + (x / m) * m := Nat.add_comm ((x / m) * m) (x % m + y)
  exact Eq.trans (congrArg (fun v : Nat => v % m) expanded)
    (mod_add_multiple (x % m + y) m (x / m) positive)

theorem mod_remove_right (x y m : Nat) (positive : 0 < m) :
    (x + y) % m = (x + y % m) % m :=
  Eq.trans (congrArg (fun v : Nat => v % m) (Nat.add_comm x y))
    (Eq.trans (mod_remove_left y x m positive)
      (congrArg (fun v : Nat => v % m) (Nat.add_comm (y % m) x)))

theorem mod_add_values (x y m : Nat) (positive : 0 < m) :
    (x + y) % m = (x % m + y % m) % m :=
  Eq.trans (mod_remove_left x y m positive) (mod_remove_right (x % m) y m positive)

theorem mod_add_three (a b c m : Nat) (positive : 0 < m) :
    (((a % m + b % m) % m) + c) % m = (a + b + c) % m := by
  have pair : (a % m + b % m) % m = (a + b) % m :=
    Eq.symm (mod_add_values a b m positive)
  exact Eq.trans (congrArg (fun v : Nat => (v + c) % m) pair)
    (Eq.symm (mod_remove_left (a + b) c m positive))

theorem high_source_value (hi lo byte : UInt64) :
    (trust_cg_fnv128_step_hi hi lo byte).toNat =
      (hi.toNat * 315 + (lo ^^^ byte).toNat * 16777216 +
        ((lo ^^^ byte).toNat * 315) / 18446744073709551616) % 18446744073709551616 := by
  let mixed : UInt64 := lo ^^^ byte
  let lowProduct : UInt64 := (mixed &&& (4294967295 : UInt64)) * (315 : UInt64)
  let upperProduct : UInt64 := (mixed >>> (32 : UInt64)) * (315 : UInt64)
  let highProduct : UInt64 := upperProduct + (lowProduct >>> (32 : UInt64))
  let hiProduct : UInt64 := hi * (315 : UInt64)
  let shifted : UInt64 := mixed * (16777216 : UInt64)
  let firstSum : UInt64 := hiProduct + shifted
  have mixedBound : mixed.toNat < 18446744073709551616 := by
    first
    | exact UInt64.toNat_lt mixed
    | exact UInt64.toNat_lt_size mixed
  have lowMask : (mixed &&& (4294967295 : UInt64)).toNat = mixed.toNat % 4294967296 :=
    uint64_mask32_value mixed
  have upperShift : (mixed >>> (32 : UInt64)).toNat = mixed.toNat / 4294967296 :=
    uint64_shift32_value mixed
  have lowRaw : lowProduct.toNat = ((mixed.toNat % 4294967296) * 315) % 18446744073709551616 := by
    have word : lowProduct.toNat =
        ((mixed &&& (4294967295 : UInt64)).toNat * 315) % 18446744073709551616 :=
      uint64_mul_value (mixed &&& (4294967295 : UInt64)) (315 : UInt64)
    exact Eq.trans word
      (congrArg (fun v : Nat => (v * 315) % 18446744073709551616) lowMask)
  have lowValue : lowProduct.toNat = (mixed.toNat % 4294967296) * 315 :=
    Eq.trans lowRaw (@Nat.mod_eq_of_lt ((mixed.toNat % 4294967296) * 315)
      18446744073709551616 (low_partial_fits mixed.toNat))
  have lowCarry : (lowProduct >>> (32 : UInt64)).toNat =
      ((mixed.toNat % 4294967296) * 315) / 4294967296 :=
    Eq.trans (uint64_shift32_value lowProduct)
      (congrArg (fun v : Nat => v / 4294967296) lowValue)
  have upperRaw : upperProduct.toNat =
      ((mixed.toNat / 4294967296) * 315) % 18446744073709551616 := by
    have word : upperProduct.toNat =
        ((mixed >>> (32 : UInt64)).toNat * 315) % 18446744073709551616 :=
      uint64_mul_value (mixed >>> (32 : UInt64)) (315 : UInt64)
    exact Eq.trans word
      (congrArg (fun v : Nat => (v * 315) % 18446744073709551616) upperShift)
  have highBound : (mixed.toNat / 4294967296) * 315 +
      ((mixed.toNat % 4294967296) * 315) / 4294967296 < 18446744073709551616 :=
    high_partial_fits mixed.toNat mixedBound
  have upperBound : (mixed.toNat / 4294967296) * 315 < 18446744073709551616 :=
    @Nat.lt_of_le_of_lt ((mixed.toNat / 4294967296) * 315)
      ((mixed.toNat / 4294967296) * 315 + ((mixed.toNat % 4294967296) * 315) / 4294967296)
      18446744073709551616
      (le_add ((mixed.toNat / 4294967296) * 315) (((mixed.toNat % 4294967296) * 315) / 4294967296)) highBound
  have upperValue : upperProduct.toNat = (mixed.toNat / 4294967296) * 315 :=
    Eq.trans upperRaw (@Nat.mod_eq_of_lt ((mixed.toNat / 4294967296) * 315)
      18446744073709551616 upperBound)
  have highRaw : highProduct.toNat =
      ((mixed.toNat / 4294967296) * 315 + ((mixed.toNat % 4294967296) * 315) / 4294967296) % 18446744073709551616 := by
    have word : highProduct.toNat =
        (upperProduct.toNat + (lowProduct >>> (32 : UInt64)).toNat) % 18446744073709551616 :=
      uint64_add_value upperProduct (lowProduct >>> (32 : UInt64))
    exact Eq.trans word (Eq.trans
      (congrArg (fun v : Nat => (v + (lowProduct >>> (32 : UInt64)).toNat) % 18446744073709551616) upperValue)
      (congrArg (fun v : Nat => ((mixed.toNat / 4294967296) * 315 + v) % 18446744073709551616) lowCarry))
  have highValue : highProduct.toNat =
      (mixed.toNat / 4294967296) * 315 + ((mixed.toNat % 4294967296) * 315) / 4294967296 :=
    Eq.trans highRaw (@Nat.mod_eq_of_lt
      ((mixed.toNat / 4294967296) * 315 + ((mixed.toNat % 4294967296) * 315) / 4294967296)
      18446744073709551616 highBound)
  have finalCarry : (highProduct >>> (32 : UInt64)).toNat =
      (mixed.toNat * 315) / 18446744073709551616 :=
    Eq.trans (uint64_shift32_value highProduct)
      (Eq.trans (congrArg (fun v : Nat => v / 4294967296) highValue) (carry_exact mixed.toNat))
  have hiValue : hiProduct.toNat = (hi.toNat * 315) % 18446744073709551616 :=
    uint64_mul_value hi (315 : UInt64)
  have shiftedValue : shifted.toNat = (mixed.toNat * 16777216) % 18446744073709551616 :=
    uint64_mul_value mixed (16777216 : UInt64)
  have pairValue : firstSum.toNat =
      ((hi.toNat * 315) % 18446744073709551616 +
        (mixed.toNat * 16777216) % 18446744073709551616) % 18446744073709551616 := by
    have word : firstSum.toNat = (hiProduct.toNat + shifted.toNat) % 18446744073709551616 :=
      uint64_add_value hiProduct shifted
    exact Eq.trans word (Eq.trans
      (congrArg (fun v : Nat => (v + shifted.toNat) % 18446744073709551616) hiValue)
      (congrArg (fun v : Nat => ((hi.toNat * 315) % 18446744073709551616 + v) % 18446744073709551616) shiftedValue))
  have output : (firstSum + (highProduct >>> (32 : UInt64))).toNat =
      (((hi.toNat * 315) % 18446744073709551616 +
        (mixed.toNat * 16777216) % 18446744073709551616) % 18446744073709551616 +
        (mixed.toNat * 315) / 18446744073709551616) % 18446744073709551616 := by
    have word : (firstSum + (highProduct >>> (32 : UInt64))).toNat =
        (firstSum.toNat + (highProduct >>> (32 : UInt64)).toNat) % 18446744073709551616 :=
      uint64_add_value firstSum (highProduct >>> (32 : UInt64))
    exact Eq.trans word (Eq.trans
      (congrArg (fun v : Nat => (v + (highProduct >>> (32 : UInt64)).toNat) % 18446744073709551616) pairValue)
      (congrArg (fun v : Nat => (((hi.toNat * 315) % 18446744073709551616 +
        (mixed.toNat * 16777216) % 18446744073709551616) % 18446744073709551616 + v) % 18446744073709551616) finalCarry))
  change (firstSum + (highProduct >>> (32 : UInt64))).toNat =
    (hi.toNat * 315 + mixed.toNat * 16777216 + (mixed.toNat * 315) / 18446744073709551616) % 18446744073709551616
  exact Eq.trans output (mod_add_three (hi.toNat * 315) (mixed.toNat * 16777216)
    ((mixed.toNat * 315) / 18446744073709551616) 18446744073709551616 (by decide))

theorem limbs_source_value (hi lo byte : UInt64) :
    (trust_cg_fnv128_step_lo lo byte).toNat +
      18446744073709551616 * (trust_cg_fnv128_step_hi hi lo byte).toNat =
    ((hi.toNat * 18446744073709551616 + (lo ^^^ byte).toNat) *
      309485009821345068724781371) % 340282366920938463463374607431768211456 := by
  have low : (trust_cg_fnv128_step_lo lo byte).toNat =
      ((lo ^^^ byte).toNat * 315) % 18446744073709551616 := low_source_value lo byte
  have high : (trust_cg_fnv128_step_hi hi lo byte).toNat =
      (hi.toNat * 315 + (lo ^^^ byte).toNat * 16777216 +
        ((lo ^^^ byte).toNat * 315) / 18446744073709551616) % 18446744073709551616 :=
    high_source_value hi lo byte
  calc
    (trust_cg_fnv128_step_lo lo byte).toNat +
        18446744073709551616 * (trust_cg_fnv128_step_hi hi lo byte).toNat =
      ((lo ^^^ byte).toNat * 315) % 18446744073709551616 +
        18446744073709551616 * (trust_cg_fnv128_step_hi hi lo byte).toNat :=
      congrArg (fun v : Nat => v + 18446744073709551616 * (trust_cg_fnv128_step_hi hi lo byte).toNat) low
    _ = ((lo ^^^ byte).toNat * 315) % 18446744073709551616 +
        18446744073709551616 * ((hi.toNat * 315 + (lo ^^^ byte).toNat * 16777216 +
          ((lo ^^^ byte).toNat * 315) / 18446744073709551616) % 18446744073709551616) :=
      congrArg (fun v : Nat => ((lo ^^^ byte).toNat * 315) % 18446744073709551616 + 18446744073709551616 * v) high
    _ = ((hi.toNat * 18446744073709551616 + (lo ^^^ byte).toNat) *
        309485009821345068724781371) % 340282366920938463463374607431768211456 :=
      Eq.symm (multiply_split hi.toNat (lo ^^^ byte).toNat)

end TrustCg.Fnv128Carry

namespace TrustCg.Fnv128Carry

theorem add_multiple_parts (k x a : Nat) (positive : 0 < a) :
    (k * a + x) / a = k + x / a ∧ (k * a + x) % a = x % a := by
  have representation : (k + x / a) * a + x % a = k * a + x := by
    calc
      (k + x / a) * a + x % a = (k * a + (x / a) * a) + x % a :=
        congrArg (fun v : Nat => v + x % a) (add_mul_canonical k (x / a) a)
      _ = k * a + ((x / a) * a + x % a) := Nat.add_assoc (k * a) ((x / a) * a) (x % a)
      _ = k * a + x := congrArg (fun v : Nat => k * a + v) (division_identity x a)
  have equation : (k + x / a) * a + x % a =
      ((k * a + x) / a) * a + (k * a + x) % a :=
    Eq.trans representation (Eq.symm (division_identity (k * a + x) a))
  have small : x % a < a := @Nat.mod_lt x a positive
  have actualSmall : (k * a + x) % a < a := @Nat.mod_lt (k * a + x) a positive
  exact And.intro
    (Eq.symm (quotient_unique (k + x / a) (x % a) ((k * a + x) / a)
      ((k * a + x) % a) a equation small actualSmall))
    (Eq.symm (remainder_unique (k + x / a) (x % a) ((k * a + x) / a)
      ((k * a + x) % a) a equation small actualSmall))

theorem bit_add_partition (a b n i : Nat) (bounded : b < 2^n) :
    Nat.testBit (2^n * a + b) i =
      (Nat.testBit (2^n * a) i || Nat.testBit b i) := by
  induction n generalizing a b i with
  | zero =>
    have bz : b = 0 := @Nat.le_antisymm b 0
      (@Nat.le_of_succ_le_succ b 0 bounded) (Nat.zero_le b)
    have zeroBit : Nat.testBit 0 i = false := by
      first
      | exact Nat.testBit_zero_eq_false i
      | exact Nat.zero_testBit i
    rw [bz]
    simp only [Nat.pow_zero, Nat.one_mul, Nat.add_zero, zeroBit]
    cases h : Nat.testBit a i with
    | false => rfl
    | true => rfl
  | succ n ih =>
    have power : 2^(Nat.succ n) = 2^n * 2 := by rfl
    have even : 2^(Nat.succ n) * a = (2^n * a) * 2 :=
      Eq.trans (congrArg (fun v : Nat => v * a) power)
        (swap_mul_right (2^n) 2 a)
    have parts := add_multiple_parts (2^n * a) b 2 (by decide)
    have evenParts := add_multiple_parts (2^n * a) 0 2 (by decide)
    have evenDiv : ((2^n * a) * 2) / 2 = 2^n * a := by
      simpa only [Nat.add_zero, Nat.zero_div] using evenParts.left
    have evenMod : ((2^n * a) * 2) % 2 = 0 := by
      simpa only [Nat.add_zero, Nat.zero_mod] using evenParts.right
    have lowBound : b / 2 < 2^n :=
      div_lt_product b 2 (2^n) (Eq.mp (congrArg (fun v : Nat => b < v) power) bounded)
    rw [even]
    cases i with
    | zero =>
      have sumBit : Nat.testBit (((2^n * a) * 2) + b) 0 = decide (b % 2 = 1) :=
        Eq.trans (bit_zero_quotient (((2^n * a) * 2) + b))
          (congrArg (fun v : Nat => decide (v = 1)) parts.right)
      have highBit : Nat.testBit ((2^n * a) * 2) 0 = false :=
        Eq.trans (bit_zero_quotient ((2^n * a) * 2))
          (congrArg (fun v : Nat => decide (v = 1)) evenMod)
      exact Eq.trans sumBit (Eq.symm (Eq.trans
        (congrArg (fun v : Bool => v || Nat.testBit b 0) highBit)
        (bit_zero_quotient b)))
    | succ i =>
      rw [bit_succ_quotient (((2^n * a) * 2) + b) i, parts.left,
        bit_succ_quotient ((2^n * a) * 2) i, evenDiv, bit_succ_quotient b i]
      exact ih a (b / 2) i lowBound

theorem or_disjoint_limbs (a b n : Nat) (bounded : b < 2^n) :
    Nat.lor (2^n * a) b = 2^n * a + b := by
  apply Nat.eq_of_testBit_eq
  intro i
  exact Eq.trans (Nat.testBit_or (2^n * a) b i)
    (Eq.symm (bit_add_partition a b n i bounded))

theorem limbs_or_source_value (hi lo byte : UInt64) :
    Nat.lor (18446744073709551616 * (trust_cg_fnv128_step_hi hi lo byte).toNat)
      (trust_cg_fnv128_step_lo lo byte).toNat =
    ((hi.toNat * 18446744073709551616 + (lo ^^^ byte).toNat) *
      309485009821345068724781371) % 340282366920938463463374607431768211456 := by
  have lowBound : (trust_cg_fnv128_step_lo lo byte).toNat < 18446744073709551616 := by
    first
    | exact UInt64.toNat_lt (trust_cg_fnv128_step_lo lo byte)
    | exact UInt64.toNat_lt_size (trust_cg_fnv128_step_lo lo byte)
  have disjoint : Nat.lor
      (18446744073709551616 * (trust_cg_fnv128_step_hi hi lo byte).toNat)
      (trust_cg_fnv128_step_lo lo byte).toNat =
      18446744073709551616 * (trust_cg_fnv128_step_hi hi lo byte).toNat +
        (trust_cg_fnv128_step_lo lo byte).toNat :=
    or_disjoint_limbs (trust_cg_fnv128_step_hi hi lo byte).toNat
      (trust_cg_fnv128_step_lo lo byte).toNat 64 lowBound
  exact Eq.trans disjoint (Eq.trans
    (Nat.add_comm (18446744073709551616 * (trust_cg_fnv128_step_hi hi lo byte).toNat)
      (trust_cg_fnv128_step_lo lo byte).toNat)
    (limbs_source_value hi lo byte))

end TrustCg.Fnv128Carry

namespace TrustCg.Fnv128Carry

theorem uint64_from_nat_value (x : Nat) :
    (UInt64.ofNat x).toNat = x % 18446744073709551616 := by
  first
  | rfl
  | exact UInt64.toNat_ofNat x

theorem split_state_or_value (x : Nat)
    (bounded : x < 340282366920938463463374607431768211456) :
    Nat.lor (18446744073709551616 *
      (UInt64.ofNat (x / 18446744073709551616)).toNat)
      (UInt64.ofNat x).toNat = x := by
  have highBound : x / 18446744073709551616 < 18446744073709551616 :=
    div_lt_product x 18446744073709551616 18446744073709551616 bounded
  have highValue : (UInt64.ofNat (x / 18446744073709551616)).toNat =
      x / 18446744073709551616 :=
    Eq.trans (uint64_from_nat_value (x / 18446744073709551616))
      (@Nat.mod_eq_of_lt (x / 18446744073709551616) 18446744073709551616 highBound)
  have lowValue : (UInt64.ofNat x).toNat = x % 18446744073709551616 :=
    uint64_from_nat_value x
  have lowBound : (UInt64.ofNat x).toNat < 18446744073709551616 := by
    first
    | exact UInt64.toNat_lt (UInt64.ofNat x)
    | exact UInt64.toNat_lt_size (UInt64.ofNat x)
  have disjoint : Nat.lor (18446744073709551616 *
      (UInt64.ofNat (x / 18446744073709551616)).toNat)
      (UInt64.ofNat x).toNat =
      18446744073709551616 * (UInt64.ofNat (x / 18446744073709551616)).toNat +
        (UInt64.ofNat x).toNat :=
    or_disjoint_limbs (UInt64.ofNat (x / 18446744073709551616)).toNat
      (UInt64.ofNat x).toNat 64 lowBound
  exact Eq.trans disjoint (Eq.trans
    (congrArg (fun v : Nat => 18446744073709551616 * v + (UInt64.ofNat x).toNat) highValue)
    (Eq.trans (congrArg (fun v : Nat => 18446744073709551616 *
      (x / 18446744073709551616) + v) lowValue)
      (Eq.trans (congrArg (fun v : Nat => v + x % 18446744073709551616)
        (Nat.mul_comm 18446744073709551616 (x / 18446744073709551616)))
        (division_identity x 18446744073709551616))))

end TrustCg.Fnv128Carry

namespace TrustCg.Fnv128Carry

theorem xor_below_power (x y n : Nat) (xb : x < 2^n) (yb : y < 2^n) :
    Nat.xor x y < 2^n := by
  have unchanged : (Nat.xor x y) % 2^n = Nat.xor x y := by
    apply Nat.eq_of_testBit_eq
    intro i
    have modX : x % 2^n = x := @Nat.mod_eq_of_lt x (2^n) xb
    have modY : y % 2^n = y := @Nat.mod_eq_of_lt y (2^n) yb
    have bitsX : Nat.testBit (x % 2^n) i = Nat.testBit x i :=
      congrArg (fun v : Nat => Nat.testBit v i) modX
    have bitsY : Nat.testBit (y % 2^n) i = Nat.testBit y i :=
      congrArg (fun v : Nat => Nat.testBit v i) modY
    have bitX : Nat.testBit x i = (decide (i < n) && Nat.testBit x i) :=
      Eq.trans (Eq.symm bitsX) (bit_mod_pow x n i)
    have bitY : Nat.testBit y i = (decide (i < n) && Nat.testBit y i) :=
      Eq.trans (Eq.symm bitsY) (bit_mod_pow y n i)
    have xored : Nat.testBit (Nat.xor x y) i =
        (Bool.xor (Nat.testBit x i) (Nat.testBit y i)) := Nat.testBit_xor x y i
    rw [bit_mod_pow, xored]
    cases h : decide (i < n) with
    | false =>
      have lowX : Nat.testBit x i = false :=
        Eq.trans bitX (congrArg (fun v : Bool => v && Nat.testBit x i) h)
      have lowY : Nat.testBit y i = false :=
        Eq.trans bitY (congrArg (fun v : Bool => v && Nat.testBit y i) h)
      have bothBits : Bool.xor (Nat.testBit x i) (Nat.testBit y i) = false :=
        Eq.trans (congrArg (fun v : Bool => Bool.xor v (Nat.testBit y i)) lowX)
          (congrArg (fun v : Bool => Bool.xor false v) lowY)
      exact Eq.trans (congrArg (fun v : Bool => false && v) bothBits) (Eq.symm bothBits)
    | true => rfl
  exact Eq.mp (congrArg (fun v : Nat => v < 2^n) unchanged)
    (@Nat.mod_lt (Nat.xor x y) (2^n) (two_power_positive n))

theorem uint64_xor_value (x y : UInt64) :
    (x ^^^ y).toNat = Nat.xor x.toNat y.toNat := by
  first
  | exact UInt64.toNat_xor x y
  | have raw : (x ^^^ y).toNat =
        (Nat.xor x.toNat y.toNat) % 18446744073709551616 := by rfl
    have xb : x.toNat < 18446744073709551616 := by
      first
      | exact UInt64.toNat_lt x
      | exact UInt64.toNat_lt_size x
    have yb : y.toNat < 18446744073709551616 := by
      first
      | exact UInt64.toNat_lt y
      | exact UInt64.toNat_lt_size y
    have bound : Nat.xor x.toNat y.toNat < 18446744073709551616 :=
      xor_below_power x.toNat y.toNat 64 xb yb
    exact Eq.trans raw (@Nat.mod_eq_of_lt (Nat.xor x.toNat y.toNat)
      18446744073709551616 bound)

end TrustCg.Fnv128Carry

namespace TrustCg.Fnv128Carry

theorem xor_state_partition (a b c n : Nat) (bb : b < 2^n) (cb : c < 2^n) :
    Nat.xor (2^n * a + b) c = 2^n * a + Nat.xor b c := by
  have xorBound : Nat.xor b c < 2^n := xor_below_power b c n bb cb
  have parts := add_multiple_parts a 0 (2^n) (two_power_positive n)
  have highRaw : (a * 2^n) % 2^n = 0 := by
    simpa only [Nat.add_zero, Nat.zero_mod] using parts.right
  have highComm : (2^n * a) % 2^n = (a * 2^n) % 2^n :=
    @congrArg Nat Nat (2^n * a) (a * 2^n) (fun v : Nat => v % 2^n)
      (Nat.mul_comm (2^n) a)
  have highMod : (2^n * a) % 2^n = 0 := Eq.trans highComm highRaw
  have modC : c % 2^n = c := @Nat.mod_eq_of_lt c (2^n) cb
  have xorFalse : forall (v : Bool), Bool.xor v false = v := by
    intro v
    cases v <;> rfl
  apply Nat.eq_of_testBit_eq
  intro i
  have zeroBit : Nat.testBit 0 i = false := by
    first
    | exact Nat.testBit_zero_eq_false i
    | exact Nat.zero_testBit i
  have highModBits : Nat.testBit ((2^n * a) % 2^n) i = Nat.testBit 0 i :=
    congrArg (fun v : Nat => Nat.testBit v i) highMod
  have highBits : (decide (i < n) && Nat.testBit (2^n * a) i) = false :=
    Eq.trans (Eq.symm (bit_mod_pow (2^n * a) n i)) (Eq.trans highModBits zeroBit)
  have bitsC : Nat.testBit (c % 2^n) i = Nat.testBit c i :=
    congrArg (fun v : Nat => Nat.testBit v i) modC
  have byteBits : Nat.testBit c i = (decide (i < n) && Nat.testBit c i) :=
    Eq.trans (Eq.symm bitsC) (bit_mod_pow c n i)
  have leftXor : Nat.testBit (Nat.xor (2^n * a + b) c) i =
      Bool.xor (Nat.testBit (2^n * a + b) i) (Nat.testBit c i) :=
    Nat.testBit_xor (2^n * a + b) c i
  have lowXor : Nat.testBit (Nat.xor b c) i =
      Bool.xor (Nat.testBit b i) (Nat.testBit c i) := Nat.testBit_xor b c i
  have leftEquation : Nat.testBit (Nat.xor (2^n * a + b) c) i =
      Bool.xor (Nat.testBit (2^n * a) i || Nat.testBit b i) (Nat.testBit c i) :=
    Eq.trans leftXor (congrArg (fun v : Bool => Bool.xor v (Nat.testBit c i))
      (bit_add_partition a b n i bb))
  have rightEquation : Nat.testBit (2^n * a + Nat.xor b c) i =
      (Nat.testBit (2^n * a) i || Bool.xor (Nat.testBit b i) (Nat.testBit c i)) :=
    Eq.trans (bit_add_partition a (Nat.xor b c) n i xorBound)
      (congrArg (fun v : Bool => Nat.testBit (2^n * a) i || v) lowXor)
  have separate : Bool.xor (Nat.testBit (2^n * a) i || Nat.testBit b i) (Nat.testBit c i) =
      (Nat.testBit (2^n * a) i || Bool.xor (Nat.testBit b i) (Nat.testBit c i)) := by
    cases h : decide (i < n) with
    | true =>
      have highZero : Nat.testBit (2^n * a) i = false :=
        Eq.trans (congrArg (fun v : Bool => v && Nat.testBit (2^n * a) i) (Eq.symm h)) highBits
      exact Eq.trans
        (congrArg (fun v : Bool => Bool.xor (v || Nat.testBit b i) (Nat.testBit c i)) highZero)
        (Eq.symm (congrArg (fun v : Bool => v || Bool.xor (Nat.testBit b i) (Nat.testBit c i)) highZero))
    | false =>
      have byteZero : Nat.testBit c i = false :=
        Eq.trans byteBits (congrArg (fun v : Bool => v && Nat.testBit c i) h)
      exact Eq.trans
        (congrArg (fun v : Bool => Bool.xor (Nat.testBit (2^n * a) i || Nat.testBit b i) v) byteZero)
        (Eq.trans (xorFalse (Nat.testBit (2^n * a) i || Nat.testBit b i))
          (Eq.trans (congrArg (fun v : Bool => Nat.testBit (2^n * a) i || v)
            (Eq.symm (xorFalse (Nat.testBit b i))))
            (congrArg (fun v : Bool => Nat.testBit (2^n * a) i || Bool.xor (Nat.testBit b i) v)
              (Eq.symm byteZero))))
  exact Eq.trans leftEquation (Eq.trans separate (Eq.symm rightEquation))

end TrustCg.Fnv128Carry

namespace TrustCg.Fnv128Carry

theorem full_step_source_value (hi lo byte : UInt64) :
    Nat.lor (18446744073709551616 * (trust_cg_fnv128_step_hi hi lo byte).toNat)
      (trust_cg_fnv128_step_lo lo byte).toNat =
    (Nat.xor (18446744073709551616 * hi.toNat + lo.toNat) byte.toNat *
      309485009821345068724781371) % 340282366920938463463374607431768211456 := by
  have lowBound : lo.toNat < 18446744073709551616 := by
    first
    | exact UInt64.toNat_lt lo
    | exact UInt64.toNat_lt_size lo
  have byteBound : byte.toNat < 18446744073709551616 := by
    first
    | exact UInt64.toNat_lt byte
    | exact UInt64.toNat_lt_size byte
  have stateXor : Nat.xor (18446744073709551616 * hi.toNat + lo.toNat) byte.toNat =
      18446744073709551616 * hi.toNat + Nat.xor lo.toNat byte.toNat :=
    xor_state_partition hi.toNat lo.toNat byte.toNat 64 lowBound byteBound
  have mixed : (lo ^^^ byte).toNat = Nat.xor lo.toNat byte.toNat :=
    uint64_xor_value lo byte
  have inputValue : hi.toNat * 18446744073709551616 + (lo ^^^ byte).toNat =
      Nat.xor (18446744073709551616 * hi.toNat + lo.toNat) byte.toNat := by
    calc
      hi.toNat * 18446744073709551616 + (lo ^^^ byte).toNat =
          hi.toNat * 18446744073709551616 + Nat.xor lo.toNat byte.toNat :=
        congrArg (fun v : Nat => hi.toNat * 18446744073709551616 + v) mixed
      _ = 18446744073709551616 * hi.toNat + Nat.xor lo.toNat byte.toNat :=
        congrArg (fun v : Nat => v + Nat.xor lo.toNat byte.toNat)
          (Nat.mul_comm hi.toNat 18446744073709551616)
      _ = Nat.xor (18446744073709551616 * hi.toNat + lo.toNat) byte.toNat :=
        Eq.symm stateXor
  exact Eq.trans (limbs_or_source_value hi lo byte)
    (congrArg (fun v : Nat => (v * 309485009821345068724781371) %
      340282366920938463463374607431768211456) inputValue)

end TrustCg.Fnv128Carry
