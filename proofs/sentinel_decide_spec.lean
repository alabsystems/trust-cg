-- Sentinel Certified-Elimination Kernel — decide() contract, formalized for Clean.
--
-- Author: Andrew Yates
-- Copyright 2026 Andrew Yates | License: Apache-2.0
--
-- This file formalizes the soundness contract of the Rust kernel
-- `trust_cg_ir::guard::decide` (crates/trust-cg-ir/src/guard.rs). It is authored in
-- Clean's native Lean4 subset (Init only; term-mode; finite inductives — no Bool/Nat/Option
-- matching, which Clean's elaborator routes through an unavailable Decidable instance) and is
-- checked by:
--
--     cargo run --locked -p clean --bin clean -- check proofs/sentinel_decide_spec.lean
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

def main : Nat := 0
