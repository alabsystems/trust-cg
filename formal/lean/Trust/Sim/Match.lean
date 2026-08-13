/-
  Sim.Match — the simulation-matching core of trust-cg's correctness development.

  This module is the connective tissue between the per-instruction certificates
  (Cert.*, packaged as `InstrCert`) and the forward-simulation cases (Sim.ForwardSim.*).
  It does NOT redefine R, Val, Loc, MachState, or SrcState — those live in `Trust.Model`,
  the single source of truth, and are imported.

  What lives here:
    1. denoteLoc CHARACTERIZATION lemmas — one per (ValKind, Loc) pair, exposing the
       low-w truncate / pair-concat / xmm / spill-readLE shapes so downstream Cert.*
       authors can rewrite a `denoteLoc (exec m) ..` goal into raw BitVec algebra that
       `bv_decide` discharges.  These are all `rfl`/definitional — the preamble's
       `denoteLoc` already pattern-matches exactly these cases.
    2. WidthFaithful (carrier-hygiene) helper lemmas — introduce / eliminate / per-name
       forms, plus the soundness consequence the consumer site needs: a width-faithful
       narrow reg reads back AT FULL WIDTH as the canonical extension of its low-w bits.
    3. R constructor + projection helpers — `R.mk'`, and the four field accessors named
       so a ForwardSim case can pull exactly one conjunct.
    4. clobberOf instance machinery + the recombination bridge — re-export of
       `cert_reestablishes_R` specialized to the dispatch path, plus the
       validator-backed `Preserves`→carrier framing lemmas.

  Copyright 2026 Andrew Yates. Apache 2.0.
-/
import Trust.Model
import Trust.Cert.Obligation

namespace Trust
namespace Sim

open Trust

/-! ###################################################################################
    ## 1. denoteLoc characterization lemmas.

    The preamble's `denoteLoc` is a nested match on `ValKind` then `Loc`.  Each lemma
    below pins ONE leaf to its closed BitVec form.  They are definitional (`rfl`); their
    value is that a Cert.* author proving e.g. `lowerAdd_correct` can `rw` the `denoteLoc`
    on the post-state into a `BitVec` expression and finish by `bv_decide`, never having
    to unfold the match by hand.  Naming: `denote_<kind>_<loc>`.
    ################################################################################### -/

/-- A narrow int in a GPR reads back as the low-`w` truncation of the full 64-bit reg.
    This is THE carrier-hygiene-relevant leaf: the high `(64-w)` bits are dropped here,
    so the read is sound regardless of dirty carrier bits; a >w consumer must instead use
    `widthFaithful_readback64` below (which needs the `carrier` conjunct of R). -/
@[simp] theorem denote_int_reg (m : MachState) (r : GPR) (w : Nat) (h : w ≤ 64) :
    denoteLoc m (.reg r) (.int w h) = .int w h ((m.regs r).truncate w) := rfl

/-- A narrow int read off an i128 register pair takes the low limb, truncated to `w`. -/
@[simp] theorem denote_int_pair (m : MachState) (lo hi : GPR) (w : Nat) (h : w ≤ 64) :
    denoteLoc m (.pair lo hi) (.int w h) = .int w h ((m.regs lo).truncate w) := rfl

/-- A narrow int viewed in an XMM takes the low `w` bits of the 128-bit lane. -/
@[simp] theorem denote_int_xmm (m : MachState) (x : XMM) (w : Nat) (h : w ≤ 64) :
    denoteLoc m (.xmm x) (.int w h) = .int w h ((m.xmms x).truncate w) := rfl

/-- A narrow int in a spill slot: read 8 LE bytes off the frame base, then truncate to `w`. -/
@[simp] theorem denote_int_spill (m : MachState) (s : FrameSlot) (w : Nat) (h : w ≤ 64) :
    denoteLoc m (.spill s) (.int w h)
      = .int w h ((readBytes m (BitVec.ofInt 64 s.byteOff) 8).truncate w) := rfl

/-- An i128 in a register pair is the concat `hi ++ lo` (high limb in `hi`). -/
@[simp] theorem denote_i128_pair (m : MachState) (lo hi : GPR) :
    denoteLoc m (.pair lo hi) .i128 = .i128 ((m.regs hi ++ m.regs lo).cast (by omega)) := rfl

/-- An i128 in a SINGLE gpr is zero-extended into the high limb (the lowering only does
    this for values it has proven fit in 64 bits). -/
@[simp] theorem denote_i128_reg (m : MachState) (r : GPR) :
    denoteLoc m (.reg r) .i128 = .i128 (((BitVec.zero 64) ++ m.regs r).cast (by omega)) := rfl

/-- An i128 in a spill slot is 16 LE bytes off the frame base. -/
@[simp] theorem denote_i128_spill (m : MachState) (s : FrameSlot) :
    denoteLoc m (.spill s) .i128 = .i128 (readBytes m (BitVec.ofInt 64 s.byteOff) 16) := rfl

/-- An i128 in an XMM is the full 128-bit lane. -/
@[simp] theorem denote_i128_xmm (m : MachState) (x : XMM) :
    denoteLoc m (.xmm x) .i128 = .i128 (m.xmms x) := rfl

/-- An f64 in an XMM is the low 64 bits of the lane (scalar SSE convention). -/
@[simp] theorem denote_f64_xmm (m : MachState) (x : XMM) :
    denoteLoc m (.xmm x) .f64 = .f64 ((m.xmms x).truncate 64) := rfl

/-- An f64 spilled is 8 LE bytes off the frame base. -/
@[simp] theorem denote_f64_spill (m : MachState) (s : FrameSlot) :
    denoteLoc m (.spill s) .f64 = .f64 (readBytes m (BitVec.ofInt 64 s.byteOff) 8) := rfl

/-- An f32 in an XMM is the low 32 bits of the lane. -/
@[simp] theorem denote_f32_xmm (m : MachState) (x : XMM) :
    denoteLoc m (.xmm x) .f32 = .f32 ((m.xmms x).truncate 32) := rfl

/-- An f32 spilled is 4 LE bytes off the frame base. -/
@[simp] theorem denote_f32_spill (m : MachState) (s : FrameSlot) :
    denoteLoc m (.spill s) .f32 = .f32 (readBytes m (BitVec.ofInt 64 s.byteOff) 4) := rfl

/-! ### readBytes little-endian shape lemmas.

    The spill cases denote through `readBytes`.  These two lemmas expose its recursion so
    a Cert.Mem author can unfold a fixed-width frame read into a concrete byte concat that
    `bv_decide` sees as plain BitVec algebra.  Both definitional. -/

@[simp] theorem readBytes_zero (m : MachState) (a : BitVec 64) :
    readBytes m a 0 = BitVec.nil := rfl

@[simp] theorem readBytes_succ (m : MachState) (a : BitVec 64) (n : Nat) :
    readBytes m a (n+1)
      = ((readBytes m (a + 1) n) ++ m.mem a).cast (by omega) := rfl

/-! ###################################################################################
    ## 2. WidthFaithful (carrier-hygiene) helpers.

    `WidthFaithful lay s m` says: for every live narrow int in a GPR, the FULL 64-bit
    register equals the 64-bit `setWidth` of its own low-`w` truncation — i.e. the high
    carrier bits are the canonical extension and a >w consumer reads a sound value.

    The introduction form (`widthFaithful_intro`) is what a Cert.* `carrierOk` field
    produces; the per-name elimination (`widthFaithful_at`) and the readback consequence
    (`widthFaithful_readback64`) are what a wide consumer site uses.
    ################################################################################### -/

/-- INTRO: assemble `WidthFaithful` from the per-live-name obligation.  This is the shape
    a Cert.* author proves to fill `InstrCert.carrierOk`. -/
theorem widthFaithful_intro {lay : Layout} {s : SrcState} {m : MachState}
    (hpt : ∀ v, Live s v →
      match lay.kind v, lay.asgn v with
      | .int w _, .reg r => (m.regs r) = ((m.regs r).truncate w).setWidth 64
      | _, _ => True) :
    WidthFaithful lay s m := hpt

/-- ELIM (raw): pull the per-name carrier obligation back out of `WidthFaithful`. -/
theorem widthFaithful_at {lay : Layout} {s : SrcState} {m : MachState}
    (hwf : WidthFaithful lay s m) (v : VName) (hv : Live s v) :
    match lay.kind v, lay.asgn v with
    | .int w _, .reg r => (m.regs r) = ((m.regs r).truncate w).setWidth 64
    | _, _ => True := hwf v hv

/-- ELIM (specialized to a known narrow reg assignment): the CONSUMER-SITE lemma.
    If `v` is a live `int w` value assigned to GPR `r`, carrier-hygiene gives the full
    64-bit readback as the `setWidth 64` of the low-`w` bits — exactly the fact a >w reader
    relies on (otherwise it would see dirty high bits).  This is where the `carrier`
    conjunct of R is *consumed*. -/
theorem widthFaithful_readback64 {lay : Layout} {s : SrcState} {m : MachState}
    (hwf : WidthFaithful lay s m) (v : VName) (hv : Live s v)
    (w : Nat) (hw : w ≤ 64) (r : GPR)
    (hk : lay.kind v = .int w hw) (ha : lay.asgn v = .reg r) :
    (m.regs r) = ((m.regs r).truncate w).setWidth 64 := by
  have h := hwf v hv
  rw [hk, ha] at h
  exact h

/-- The per-name carrier obligation, as a standalone predicate, so the discharge lemmas
    below can speak about exactly the body `WidthFaithful` quantifies. -/
def carrierAt (lay : Layout) (m : MachState) (v : VName) : Prop :=
  match lay.kind v, lay.asgn v with
  | .int w _, .reg r => (m.regs r) = ((m.regs r).truncate w).setWidth 64
  | _, _ => True

/-- `WidthFaithful` is exactly the universal closure of `carrierAt` over live names — the
    bridge between the preamble's inline match and the per-name lemmas here. -/
theorem widthFaithful_iff_carrierAt {lay : Layout} {s : SrcState} {m : MachState} :
    WidthFaithful lay s m ↔ ∀ v, Live s v → carrierAt lay m v := Iff.rfl

/-- A value whose ASSIGNMENT is an XMM imposes no carrier obligation — `carrierAt` is
    `True` there (the WidthFaithful body's catch-all branch).  This is what a Cert.* author
    for a float/SSE-result value uses to discharge that name's carrier goal: no narrow-reg
    re-extension is owed for an xmm-resident value. -/
theorem carrierAt_xmm {lay : Layout} {m : MachState} (v : VName) (x : XMM)
    (ha : lay.asgn v = .xmm x) : carrierAt lay m v := by
  unfold carrierAt; rw [ha]; cases lay.kind v <;> trivial

/-- A value assigned to a register PAIR (an i128 reg-pair result) owes no narrow-reg
    carrier obligation either — `carrierAt` is `True` for a pair assignment. -/
theorem carrierAt_pair {lay : Layout} {m : MachState} (v : VName) (lo hi : GPR)
    (ha : lay.asgn v = .pair lo hi) : carrierAt lay m v := by
  unfold carrierAt; rw [ha]; cases lay.kind v <;> trivial

/-- A spilled value owes no narrow-reg carrier obligation (its hygiene is a memory-content
    fact, carried by `memAgree`, not by the register width invariant). -/
theorem carrierAt_spill {lay : Layout} {m : MachState} (v : VName) (sl : FrameSlot)
    (ha : lay.asgn v = .spill sl) : carrierAt lay m v := by
  unfold carrierAt; rw [ha]; cases lay.kind v <;> trivial

/-- A full-width (`w = 64`) int in a GPR is automatically width-faithful: truncate-to-64
    then setWidth-64 is the identity, so the carrier equation holds for ANY register
    contents.  Wide (i64/u64) carriers therefore need no re-extend — discharged by
    `bv_decide`. -/
theorem carrierAt_int64_reg {lay : Layout} {m : MachState} (v : VName) (r : GPR)
    (hk : lay.kind v = .int 64 (by omega)) (ha : lay.asgn v = .reg r) :
    carrierAt lay m v := by
  unfold carrierAt; rw [hk, ha]
  bv_decide

/-! ###################################################################################
    ## 3. R constructor + projection helpers.

    The four conjuncts of R already have accessors (`R.realize`, `R.carrier`,
    `R.memAgree`, `R.pcSync`).  We add a smart constructor `R.mk'` (same as the
    anonymous structure literal but named, so cases read uniformly) and re-export the
    projections under `Sim`-local names a ForwardSim case can call without `R.`-qualifying.
    ################################################################################### -/

/-- Smart constructor for `R` from its four component facts.  Identical content to the
    anonymous-structure form; named so every ForwardSim case rebuilds R the same way and
    so refactors to the conjunct list happen in ONE place. -/
def R.mk' {lay : Layout} {s : SrcState} {m : MachState}
    (hrealize  : ∀ v, Live s v → denoteLoc m (lay.asgn v) (lay.kind v) = s.env v)
    (hcarrier  : WidthFaithful lay s m)
    (hmemAgree : agreeOn s.mem m (lay.nonFrame))
    (hpcSync   : m.rip = lay.entryAddr (lay.lowerOf s.pc)) :
    R lay s m :=
  { realize := hrealize, carrier := hcarrier, memAgree := hmemAgree, pcSync := hpcSync }

/-- Projection: realize (every live value denotes at its assigned Loc/kind). -/
theorem R.realize_of {lay : Layout} {s : SrcState} {m : MachState}
    (hR : R lay s m) : ∀ v, Live s v → denoteLoc m (lay.asgn v) (lay.kind v) = s.env v :=
  hR.realize

/-- Projection: carrier (the WidthFaithful invariant). -/
theorem R.carrier_of {lay : Layout} {s : SrcState} {m : MachState}
    (hR : R lay s m) : WidthFaithful lay s m := hR.carrier

/-- Projection: memAgree (off-frame memory agreement). -/
theorem R.memAgree_of {lay : Layout} {s : SrcState} {m : MachState}
    (hR : R lay s m) : agreeOn s.mem m (lay.nonFrame) := hR.memAgree

/-- Projection: pcSync (machine rip at the lowered current block entry). -/
theorem R.pcSync_of {lay : Layout} {s : SrcState} {m : MachState}
    (hR : R lay s m) : m.rip = lay.entryAddr (lay.lowerOf s.pc) := hR.pcSync

/-- A single live value, denoted: the per-name specialization of `realize`, the form a
    Cert.* `value` author actually applies (one source name at a time). -/
theorem R.denote_live {lay : Layout} {s : SrcState} {m : MachState}
    (hR : R lay s m) (v : VName) (hv : Live s v) :
    denoteLoc m (lay.asgn v) (lay.kind v) = s.env v := hR.realize v hv

/-! ###################################################################################
    ## 4. The recombination bridge + clobber framing.

    `cert_reestablishes_R` (in Cert.Obligation) is the ONE place R is rebuilt from a cert.
    Here we (a) re-export it under the `Sim` namespace as the name ForwardSim cases call,
    and (b) provide the `Preserves`→frame lemmas that let a Cert.* author derive the
    carrier/realize/mem facts for the UNTOUCHED part of the state from the regalloc
    clobber bound — the "frame rule" half of every pure-op case.
    ################################################################################### -/

/-- THE bridge a ForwardSim per-opcode case invokes: given the instruction's `InstrCert`
    and a starting match `R`, get BOTH the real `x86StepPlus` run AND the re-established
    `R` at the source successor.  Thin re-export of the contract's `cert_reestablishes_R`
    so the dispatch site does not reach across module namespaces. -/
theorem matchStep
    {lay : Layout} {step : LoweredStep} {s s' : SrcState} {m : MachState}
    (cert : InstrCert lay step s s') (hR : R lay s m) :
    x86StepPlus m step.event (step.exec m) ∧ R lay s' (step.exec m) :=
  cert_reestablishes_R cert hR

/-- The forward-sim existential, packaged from a cert: this is exactly the witness a
    ForwardSim case supplies to close `∃ m', x86StepPlus m ev m' ∧ R lay s' m'`.  The
    event MUST be the cert's `step.event` (the observable the lowered op emits). -/
theorem matchStep_exists
    {lay : Layout} {step : LoweredStep} {s s' : SrcState} {m : MachState}
    (cert : InstrCert lay step s s') (hR : R lay s m) :
    ∃ m', x86StepPlus m step.event m' ∧ R lay s' m' :=
  ⟨step.exec m, matchStep cert hR⟩

/-! ### Frame lemmas: from a `Preserves` clobber bound, untouched resources are unchanged.

    These are the projections of `Preserves` a Cert.* author uses to argue that values
    NOT in the instruction's clobber set keep their old denotation (the regalloc_validator
    guarantee: distinct live values get distinct regs, so a write to the def reg cannot
    perturb another live value's reg).  Each is a trivial `Preserves` field access, named
    for the resource it frames. -/

/-- A GPR outside the clobber set is unchanged across the step. -/
theorem preserves_gpr {cl : ClobberSet} {m m' : MachState}
    (hp : Preserves cl m m') (r : GPR) (hr : ¬ cl.gprs r) :
    m'.regs r = m.regs r := hp.1 r hr

/-- An XMM outside the clobber set is unchanged. -/
theorem preserves_xmm {cl : ClobberSet} {m m' : MachState}
    (hp : Preserves cl m m') (x : XMM) (hx : ¬ cl.xmms x) :
    m'.xmms x = m.xmms x := hp.2.1 x hx

/-- EFLAGS are unchanged when the step is not flag-clobbering. -/
theorem preserves_flags {cl : ClobberSet} {m m' : MachState}
    (hp : Preserves cl m m') (hf : ¬ cl.flags) :
    m'.flags = m.flags := hp.2.2.1 hf

/-- A frame byte outside the written frame region is unchanged — the spill-frame half of
    memory non-interference. -/
theorem preserves_frame {cl : ClobberSet} {m m' : MachState}
    (hp : Preserves cl m m') (a : BitVec 64) (ha : ¬ cl.frame a) :
    m'.mem a = m.mem a := hp.2.2.2 a ha

/-- FRAME-RULE for `realize`: a live value `v` whose assigned GPR is NOT clobbered keeps
    its old narrow denotation across the step.  This is the half of every pure-op case
    that handles the values the instruction did not define.  The hypothesis
    `hdistinct` is the regalloc_validator output: `v`'s reg is disjoint from the clobber
    set.  Stated for the `int/reg` shape (the common live carrier); analogous shapes for
    pair/xmm/spill follow the same `preserves_*` access and are mechanical. -/
theorem realize_framed_int_reg
    {lay : Layout} {m m' : MachState} {cl : ClobberSet}
    (hp : Preserves cl m m')
    (v : VName) (w : Nat) (hw : w ≤ 64) (r : GPR)
    (hk : lay.kind v = .int w hw) (ha : lay.asgn v = .reg r)
    (hdistinct : ¬ cl.gprs r) :
    denoteLoc m' (lay.asgn v) (lay.kind v) = denoteLoc m (lay.asgn v) (lay.kind v) := by
  rw [hk, ha, denote_int_reg, denote_int_reg, preserves_gpr hp r hdistinct]

/-- FRAME-RULE for carrier-hygiene: a narrow live value in an unclobbered GPR stays
    width-faithful across the step (its reg is bit-for-bit unchanged, so the low-w /
    setWidth equation transports verbatim).  This discharges the per-name carrier goal of
    `carrierOk` for every value the instruction did not touch. -/
theorem widthFaithful_framed_int_reg
    {m m' : MachState} {cl : ClobberSet}
    (hp : Preserves cl m m')
    (w : Nat) (r : GPR) (hdistinct : ¬ cl.gprs r)
    (hold : (m.regs r) = ((m.regs r).truncate w).setWidth 64) :
    (m'.regs r) = ((m'.regs r).truncate w).setWidth 64 := by
  rw [preserves_gpr hp r hdistinct]; exact hold

/-- FRAME-RULE for memAgree: if off-frame memory agreed before, and the step only wrote
    addresses inside the frame clobber set, then off-frame agreement is preserved — PROVIDED
    every off-frame address is outside the frame clobber set.  This is the memory
    non-interference obligation, `nonFrame ⊆ ¬frame` being the regalloc/frame-layout fact
    the validator certifies.  Stated as: with that disjointness, `memOk` follows from the
    incoming `memAgree`. -/
theorem memAgree_framed
    {lay : Layout} {s : SrcState} {m m' : MachState} {cl : ClobberSet}
    (hp : Preserves cl m m')
    (hagree : agreeOn s.mem m (lay.nonFrame))
    (hdisj : ∀ a, lay.nonFrame a → ¬ cl.frame a) :
    agreeOn s.mem m' (lay.nonFrame) := by
  intro a ha
  rw [hagree a ha, preserves_frame hp a (hdisj a ha)]

/-! ###################################################################################
    ## 5. Worked bv_decide cert shapes (validation harness).

    These are NOT the production Cert.* lemmas (those live in Cert.Arith / Cert.Compare),
    but minimal worked instances proving that the `denote_*` rewrite lemmas above feed
    straight into `bv_decide`.  They mirror the two established shapes the spec names:
      * `lowerAdd_correct`  : i128 ADD+ADC value cert.
      * `lowerCmp_correct`  : Cmp→Ordering value cert (cases on signedness, then bv_decide).
    Keeping a live `bv_decide` here pins that the toolchain's kernel-checked bitblasting
    path is wired and that the characterization lemmas are in the right normal form.
    ################################################################################### -/

/-- i128 ADD+ADC, value level: the lowered two-limb add denotes as the 128-bit sum.
    `lowerAddI128` models the (lo,hi) limbs the encoder emits; the cert is the equality
    of its concatenation to the full-width sum.  Discharged by `bv_decide` (kernel
    bitblasting + LRAT) — the SMT solver is NOT in the TCB.  This is the `lowerAdd_correct`
    shape: `denote (lowerAdd a b) = denote a + denote b`. -/
def lowerAddI128 (alo ahi blo bhi : BitVec 64) : BitVec 64 × BitVec 64 :=
  let lo := alo + blo
  let carry : BitVec 64 := if alo + blo < alo then 1 else 0   -- unsigned add carry-out
  let hi := ahi + bhi + carry
  (lo, hi)

theorem lowerAddI128_correct (alo ahi blo bhi : BitVec 64) :
    (((lowerAddI128 alo ahi blo bhi).2 ++ (lowerAddI128 alo ahi blo bhi).1) : BitVec 128)
      = (ahi ++ alo) + (bhi ++ blo) := by
  unfold lowerAddI128
  bv_decide

/-- Cmp→Ordering (i8 result: gt ? 1 : (lt ? -1 : 0)), value level, for the SIGNED case.
    This is the `lowerCmp_correct` shape; the production lemma cases on `signed` first,
    we exhibit the signed leaf.

    FIX (adversarial review): the previous statement equated `lowerCmpSignedI8 a b` to a
    verbatim copy of its own definitional body — a VACUOUS `body = body` tautology that
    proved nothing about the comparison and carried no native `bv_decide` axiom.  The cert
    a composition needs is that each of the three Ordering outputs is produced EXACTLY under
    the intended signed relation, stated with the relation predicates (`a.slt b`, `b.slt a`)
    independently of the `if`-tree.  `bv_decide` now discharges each leaf against that
    independent spec (and rejects the swapped/wrong variant with a counterexample). -/
def lowerCmpSignedI8 (a b : BitVec 64) : BitVec 8 :=
  if a.slt b then (-1 : BitVec 8) else if b.slt a then 1 else 0

theorem lowerCmpSignedI8_correct (a b : BitVec 64) :
    (lowerCmpSignedI8 a b = (-1 : BitVec 8) ↔ a.slt b) ∧
    (lowerCmpSignedI8 a b = (1 : BitVec 8) ↔ (¬ a.slt b ∧ b.slt a)) ∧
    (lowerCmpSignedI8 a b = (0 : BitVec 8) ↔ (¬ a.slt b ∧ ¬ b.slt a)) := by
  unfold lowerCmpSignedI8
  by_cases h1 : a.slt b <;> by_cases h2 : b.slt a <;> simp_all <;> bv_decide

/-- Carrier re-extension at the VALUE level.  IMPORTANT FIDELITY POINT: the preamble's
    `WidthFaithful` carrier equation uses `.setWidth 64`, which is ZERO-extension.  So the
    model's carrier invariant is the *clean-upper* (zero-extended) hygiene — a register is
    width-faithful for an 8-bit value iff its high 56 bits are 0.  The producer that
    establishes it is a MOVZX (zero-extend), and `bv_decide` confirms the round trip:
    `(zext bits).truncate 8` is `bits` and `setWidth 64` of that reproduces the
    zero-extended register.  (A MOVSX/sign-extend producer would VIOLATE this carrier
    shape when the sign bit is set — `bv_decide` rejects that, see the note below — which
    is exactly why a signed narrow consumer must re-extend per its own signedness rather
    than rely on this zero-carrier invariant.) -/
theorem carrier_movzx8_widthFaithful (bits : BitVec 8) :
    (BitVec.setWidth 64 bits)
      = ((BitVec.setWidth 64 bits).truncate 8).setWidth 64 := by
  bv_decide

/-- The dual negative fact, machine-checked: a SIGN-extended 8-bit value is NOT in general
    width-faithful under the zero-extension carrier equation — there is a witness (top bit
    set) where it fails.  We record it as the decidable inequality of the two extensions on
    that witness, so the asymmetry between the model's zero-carrier and a signed value is a
    proven fact, not a comment.  `0x80` sign-extends to all-ones-high, zero-extends to
    zero-high; they differ. -/
theorem signExtend_ne_setWidth_witness :
    (BitVec.signExtend 64 (0x80 : BitVec 8)) ≠ (BitVec.setWidth 64 (0x80 : BitVec 8)) := by
  bv_decide

end Sim
end Trust
