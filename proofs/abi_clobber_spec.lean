-- AArch64 ABI call-clobber completeness — caller/callee-saved partition, formalized for Clean.
--
-- Author: Andrew Yates
-- Copyright 2026 Andrew Yates | License: Apache-2.0
--
-- This file formalizes the AAPCS64 (ARM 64-bit Procedure Call Standard) call-clobber
-- convention as a TOTAL, EXHAUSTIVE finite enumeration and proves the two structural
-- properties the register allocator depends on for soundness:
--
--   (a) DISJOINTNESS   — no architectural register is BOTH caller-saved AND callee-saved.
--   (b) COMPLETENESS / TILING — every architectural register is EXACTLY ONE of
--       caller-saved or callee-saved (the two classes partition the whole bank).
--
-- Why this matters. `trust-cg-regalloc`'s `aarch64_caller_saved_regs()` /
-- `aarch64_callee_saved_regs()` (crates/trust-cg-regalloc/src/call_clobber.rs) drive
-- call-crossing save/restore. If a volatile (caller-saved) register were OMITTED from the
-- clobber set, a value live across a call could survive in a register the callee freely
-- overwrites — a silent miscompile. If a callee-saved register were WRONGLY included, the
-- allocator would emit needless save/restore (a perf bug) and, worse, could treat a
-- preserved register as clobbered. The two properties below rule out BOTH failure modes at
-- the level of the convention itself; a differential weld test in trust-cg-regalloc pins the
-- REAL Rust accessors to exactly this partition (see call_clobber.rs tests).
--
-- It is authored in Clean's native Lean4 subset (Init only; term-mode; finite inductives —
-- no Bool/Nat/Option matching, which Clean's elaborator routes through an unavailable
-- Decidable instance) and is checked by:
--
--     $HOME/clean/target/debug/clean check proofs/abi_clobber_spec.lean
--
-- MODELING. AAPCS64 is a fixed finite convention, so we enumerate the architectural register
-- file directly: the 31 general-purpose registers X0..X30 as a 31-constructor inductive `Gpr`,
-- and the 32 SIMD/FP registers V0..V31 as a 32-constructor inductive `Fpr`. (X31 is SP/XZR — not
-- an allocatable GPR — and is deliberately outside the bank, matching the regalloc model which
-- never allocates it.) The AAPCS64 callee-saved sets are X19..X28 and V8..V15; everything else in
-- each bank is caller-saved (volatile). `Saved` is the two-valued partition class. We define the
-- convention as TOTAL classifier functions `gprClass`/`fprClass`, derive the caller/callee
-- membership Flags, and prove disjointness and tiling per-register by `rfl` (one closed-form
-- computation per constructor — the convention is decided, not assumed). The headline cross-bank
-- statements are UNIVERSAL Flag-equalities quantified over every register.
--
-- NOTE on the 128/64/32/16/8-bit aliases. The Rust `PReg` model encodes width-aliased views
-- (X/W, V/Q/D/S/H) of the SAME architectural register at distinct encodings. The CONVENTION,
-- however, is a property of the underlying architectural register, not of a width view: if Xn is
-- callee-saved then Wn is too, and if Vn is caller-saved then every Dn/Sn/Hn view is too. So we
-- model one classifier per architectural register; the Rust differential test then checks that
-- EVERY width-alias encoding of each register lands in the class this spec assigns it. This keeps
-- the spec the faithful ground truth and the alias bookkeeping in the test where it belongs.

-- ===========================================================================================
-- Core finite types.

-- The two partition classes. Caller-saved = volatile (clobbered by a call); callee-saved =
-- preserved across a call by the callee.
inductive Saved where
  | caller
  | callee

-- A two-valued membership flag (Clean matches finite inductives directly; we never route through
-- Bool/Decidable). `yes` = "is in this class".
inductive Flag where
  | yes
  | no

-- The 31 allocatable general-purpose registers, X0..X30. (X31 = SP/XZR is intentionally absent;
-- it is not part of the allocatable GPR bank.) AAPCS64: X19..X28 are callee-saved; the rest are
-- caller-saved. X16/X17 (IP0/IP1), X18 (platform), X29 (FP) and X30 (LR) are all caller-saved
-- per the convention as modeled by the regalloc clobber set.
inductive Gpr where
  | x0  | x1  | x2  | x3  | x4  | x5  | x6  | x7
  | x8  | x9  | x10 | x11 | x12 | x13 | x14 | x15
  | x16 | x17 | x18 | x19 | x20 | x21 | x22 | x23
  | x24 | x25 | x26 | x27 | x28 | x29 | x30

-- The 32 SIMD/FP registers, V0..V31. AAPCS64: V8..V15 are callee-saved (the lower 64 bits, but
-- the convention CLASS is callee-saved); the rest are caller-saved.
inductive Fpr where
  | v0  | v1  | v2  | v3  | v4  | v5  | v6  | v7
  | v8  | v9  | v10 | v11 | v12 | v13 | v14 | v15
  | v16 | v17 | v18 | v19 | v20 | v21 | v22 | v23
  | v24 | v25 | v26 | v27 | v28 | v29 | v30 | v31

-- ===========================================================================================
-- The convention, as TOTAL classifiers (the ground-truth mirror of AAPCS64).

-- GPR classification: X19..X28 are callee-saved; every other GPR is caller-saved.
def gprClass (g : Gpr) : Saved :=
  match g with
  | Gpr.x0  => Saved.caller | Gpr.x1  => Saved.caller | Gpr.x2  => Saved.caller
  | Gpr.x3  => Saved.caller | Gpr.x4  => Saved.caller | Gpr.x5  => Saved.caller
  | Gpr.x6  => Saved.caller | Gpr.x7  => Saved.caller | Gpr.x8  => Saved.caller
  | Gpr.x9  => Saved.caller | Gpr.x10 => Saved.caller | Gpr.x11 => Saved.caller
  | Gpr.x12 => Saved.caller | Gpr.x13 => Saved.caller | Gpr.x14 => Saved.caller
  | Gpr.x15 => Saved.caller | Gpr.x16 => Saved.caller | Gpr.x17 => Saved.caller
  | Gpr.x18 => Saved.caller
  | Gpr.x19 => Saved.callee | Gpr.x20 => Saved.callee | Gpr.x21 => Saved.callee
  | Gpr.x22 => Saved.callee | Gpr.x23 => Saved.callee | Gpr.x24 => Saved.callee
  | Gpr.x25 => Saved.callee | Gpr.x26 => Saved.callee | Gpr.x27 => Saved.callee
  | Gpr.x28 => Saved.callee
  | Gpr.x29 => Saved.caller | Gpr.x30 => Saved.caller

-- FPR classification: V8..V15 are callee-saved; every other FPR is caller-saved.
def fprClass (f : Fpr) : Saved :=
  match f with
  | Fpr.v0  => Saved.caller | Fpr.v1  => Saved.caller | Fpr.v2  => Saved.caller
  | Fpr.v3  => Saved.caller | Fpr.v4  => Saved.caller | Fpr.v5  => Saved.caller
  | Fpr.v6  => Saved.caller | Fpr.v7  => Saved.caller
  | Fpr.v8  => Saved.callee | Fpr.v9  => Saved.callee | Fpr.v10 => Saved.callee
  | Fpr.v11 => Saved.callee | Fpr.v12 => Saved.callee | Fpr.v13 => Saved.callee
  | Fpr.v14 => Saved.callee | Fpr.v15 => Saved.callee
  | Fpr.v16 => Saved.caller | Fpr.v17 => Saved.caller | Fpr.v18 => Saved.caller
  | Fpr.v19 => Saved.caller | Fpr.v20 => Saved.caller | Fpr.v21 => Saved.caller
  | Fpr.v22 => Saved.caller | Fpr.v23 => Saved.caller | Fpr.v24 => Saved.caller
  | Fpr.v25 => Saved.caller | Fpr.v26 => Saved.caller | Fpr.v27 => Saved.caller
  | Fpr.v28 => Saved.caller | Fpr.v29 => Saved.caller | Fpr.v30 => Saved.caller
  | Fpr.v31 => Saved.caller

-- ===========================================================================================
-- Membership predicates, derived from the SINGLE classifier (so disjointness/tiling are not
-- assumed — they FOLLOW from each register having exactly one class).

-- "is callee-saved" for a class value.
def isCallee (s : Saved) : Flag :=
  match s with
  | Saved.callee => Flag.yes
  | Saved.caller => Flag.no

-- "is caller-saved" is the COMPLEMENT of callee-saved — this is the definitional content of
-- `is_caller_saved = not is_callee_saved` from the task. We define it by negating `isCallee`
-- (not by an independent classifier), so caller/callee can never disagree by construction; the
-- theorems below confirm the negation tiles the bank.
def notFlag (b : Flag) : Flag :=
  match b with
  | Flag.yes => Flag.no
  | Flag.no => Flag.yes

def isCaller (s : Saved) : Flag := notFlag (isCallee s)

-- Per-bank membership: classify the register, then read off the flag.
def gprIsCallee (g : Gpr) : Flag := isCallee (gprClass g)
def gprIsCaller (g : Gpr) : Flag := isCaller (gprClass g)
def fprIsCallee (f : Fpr) : Flag := isCallee (fprClass f)
def fprIsCaller (f : Fpr) : Flag := isCaller (fprClass f)

-- Logical AND / OR on flags, for the disjointness/tiling headlines.
def andFlag (a b : Flag) : Flag :=
  match a with
  | Flag.no => Flag.no
  | Flag.yes => b

def orFlag (a b : Flag) : Flag :=
  match a with
  | Flag.yes => Flag.yes
  | Flag.no => b

-- ===========================================================================================
-- (a) DISJOINTNESS — no register is BOTH caller- AND callee-saved.
--
-- Because `isCaller = notFlag isCallee`, for ANY class value the AND of the two flags is `no`.
-- This is the GENERAL fact; the per-register corollaries follow by definitional unfolding. We
-- state it three ways: the class-level general lemma, and the two UNIVERSAL per-bank Flag-
-- equalities (quantified over EVERY register — one proof covers the whole bank, since the
-- AND-with-its-own-negation is `no` no matter which branch the classifier took).

-- General: a flag AND its negation is always `no`.
theorem and_self_not_no_yes : andFlag Flag.yes (notFlag Flag.yes) = Flag.no := rfl
theorem and_self_not_no_no  : andFlag Flag.no  (notFlag Flag.no)  = Flag.no := rfl

-- Class-level: for either class, caller AND callee is `no`.
theorem disjoint_class_caller : andFlag (isCaller Saved.caller) (isCallee Saved.caller) = Flag.no := rfl
theorem disjoint_class_callee : andFlag (isCaller Saved.callee) (isCallee Saved.callee) = Flag.no := rfl

-- UNIVERSAL GPR disjointness: for EVERY general-purpose register, caller AND callee = `no`.
-- The proof is rfl after casing the (single) classifier: whichever class `gprClass g` yields,
-- `isCaller` is its negation, so the AND collapses to `no`. We discharge it via the general
-- complement fact, generic over the register.
theorem gpr_disjoint (g : Gpr) : andFlag (gprIsCaller g) (gprIsCallee g) = Flag.no := by
  cases g <;> rfl

-- UNIVERSAL FPR disjointness: for EVERY SIMD/FP register, caller AND callee = `no`.
theorem fpr_disjoint (f : Fpr) : andFlag (fprIsCaller f) (fprIsCallee f) = Flag.no := by
  cases f <;> rfl

-- ===========================================================================================
-- (b) COMPLETENESS / TILING — every register is EXACTLY ONE of caller/callee-saved.
--
-- Two halves combine into "exactly one":
--   COVER : caller OR callee = `yes`  (at least one) — every register IS classified.
--   The disjointness above gives "at most one". Together: exactly one. Because `isCaller` is the
--   negation of `isCallee`, the OR is `yes` for ANY class value, so a SINGLE universal proof
--   covers each whole bank.

-- General: a flag OR its negation is always `yes` (excluded middle, decided here).
theorem or_self_not_yes_yes : orFlag Flag.yes (notFlag Flag.yes) = Flag.yes := rfl
theorem or_self_not_yes_no  : orFlag Flag.no  (notFlag Flag.no)  = Flag.yes := rfl

-- Class-level cover.
theorem cover_class_caller : orFlag (isCaller Saved.caller) (isCallee Saved.caller) = Flag.yes := rfl
theorem cover_class_callee : orFlag (isCaller Saved.callee) (isCallee Saved.callee) = Flag.yes := rfl

-- UNIVERSAL GPR cover: EVERY general-purpose register is caller- OR callee-saved.
theorem gpr_cover (g : Gpr) : orFlag (gprIsCaller g) (gprIsCallee g) = Flag.yes := by
  cases g <;> rfl

-- UNIVERSAL FPR cover: EVERY SIMD/FP register is caller- OR callee-saved.
theorem fpr_cover (f : Fpr) : orFlag (fprIsCaller f) (fprIsCallee f) = Flag.yes := by
  cases f <;> rfl

-- EXACTLY-ONE, packaged: caller is the EXACT complement of callee for every register. The
-- combination of `..._cover` (≥1) and `..._disjoint` (≤1) is precisely this equality
-- `gprIsCaller g = notFlag (gprIsCallee g)`, the formal statement of "is_caller_saved =
-- not is_callee_saved" tiling the bank with no overlap and no gap.
theorem gpr_caller_is_not_callee (g : Gpr) : gprIsCaller g = notFlag (gprIsCallee g) := by
  cases g <;> rfl

theorem fpr_caller_is_not_callee (f : Fpr) : fprIsCaller f = notFlag (fprIsCallee f) := by
  cases f <;> rfl

-- ===========================================================================================
-- (c) CONCRETE WITNESSES — pin the AAPCS64 boundary cases the differential weld test enumerates.
-- These are the exact registers whose misclassification would be a miscompile (volatile dropped
-- from the clobber set) or a needless-save (preserved reg wrongly clobbered). Each is a closed-
-- form rfl, so the spec independently fixes the convention at every boundary.

-- GPR caller-saved boundaries: X0 (first arg/volatile), X18 (last before callee block),
-- X29 (FP) and X30 (LR) are caller-saved in this model; X15 mid-range volatile.
theorem x0_caller  : gprIsCaller Gpr.x0  = Flag.yes := rfl
theorem x15_caller : gprIsCaller Gpr.x15 = Flag.yes := rfl
theorem x18_caller : gprIsCaller Gpr.x18 = Flag.yes := rfl
theorem x29_caller : gprIsCaller Gpr.x29 = Flag.yes := rfl
theorem x30_caller : gprIsCaller Gpr.x30 = Flag.yes := rfl

-- GPR callee-saved boundaries: X19 (first callee), X28 (last callee).
theorem x19_callee : gprIsCallee Gpr.x19 = Flag.yes := rfl
theorem x28_callee : gprIsCallee Gpr.x28 = Flag.yes := rfl
-- And X18/X29 are NOT callee-saved (the boundary on either side of the callee block).
theorem x18_not_callee : gprIsCallee Gpr.x18 = Flag.no := rfl
theorem x29_not_callee : gprIsCallee Gpr.x29 = Flag.no := rfl

-- FPR caller-saved boundaries: V0, V7 (last before callee block), V16 (first after), V31 (last).
theorem v0_caller  : fprIsCaller Fpr.v0  = Flag.yes := rfl
theorem v7_caller  : fprIsCaller Fpr.v7  = Flag.yes := rfl
theorem v16_caller : fprIsCaller Fpr.v16 = Flag.yes := rfl
theorem v31_caller : fprIsCaller Fpr.v31 = Flag.yes := rfl

-- FPR callee-saved boundaries: V8 (first callee), V15 (last callee). V7/V16 NOT callee-saved.
theorem v8_callee  : fprIsCallee Fpr.v8  = Flag.yes := rfl
theorem v15_callee : fprIsCallee Fpr.v15 = Flag.yes := rfl
theorem v7_not_callee  : fprIsCallee Fpr.v7  = Flag.no := rfl
theorem v16_not_callee : fprIsCallee Fpr.v16 = Flag.no := rfl

def main : Nat := 0
