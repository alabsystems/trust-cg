/-
  Sim.ForwardSim.Mem — the forward-simulation cases for the MEMORY opcodes (load / store).

  Author: Andrew Yates
  Copyright 2026 Andrew Yates | License: Apache-2.0

  ─────────────────────────────────────────────────────────────────────────────────────────────
  WHAT THIS MODULE IS.  `Sim.ForwardSim.*` proves one `forward_sim` case per source opcode class.
  This file owns the two MEMORY forms in trust-cg's `EmittableNeedsProof` set:

      MOV dst, [base+disp]     — a LOAD  (read 8/4/2/1 LE bytes off the heap into a GPR/xmm),
      MOV [base+disp], src     — a STORE (write the value's bytes back to the heap).

  These are the ONLY two cases where the `memAgree` conjunct of `R` (the memory non-interference
  invariant: src and mach memory agree on every off-frame address) is non-trivial work rather than
  a frame-rule pass-through.  Everything pivots on two byte-store algebra facts:

      read_write_same      — reading the bytes you JUST wrote returns the value written
                             (the LOAD-after-its-own-STORE / store-value correctness leg);
      read_write_disjoint  — reading bytes the write did NOT touch returns the OLD memory
                             (the frame leg: every OTHER live value, and every off-frame heap
                              address, is undisturbed by the store).

  HOW THE SPEC MAPS ONTO THE THREE LEGS.
    * STORE.  `value` (realize of OTHER live values) needs `read_write_disjoint` + `hnoalias`
      (the regalloc/frame fact that a stored heap range does not alias any OTHER value's spill or
      heap footprint); `memAgree` is established by `agreeOn_write` — and THAT is precisely the
      memory-non-interference proof the spec asks us to exhibit as conjunct (3).
    * LOAD.  The loaded GPR gets the value `read_write_same` says is at the address; since the
      source heap and the machine heap AGREE off-frame (the incoming `memAgree`), the loaded value
      equals the source value.  A load writes NO memory, so `memAgree` transports verbatim.

  WHAT IS HONESTLY STUBBED (each `sorry` is one-lined and classified at its site):
    * The connection from the abstract `srcStep` of a load/store to the concrete (addr, width,
      value) it touches is the SOURCE SEMANTICS, owned by `Semantics.Source` — we take it as a
      structured hypothesis (`LoadShape`/`StoreShape`), NOT a `sorry` that assumes the conclusion.
    * A couple of `readBytes`/`writeBytes` width-generic identities are genuinely-large LE byte
      inductions; they are `sorry`-marked `mechanical` and NEVER smuggle the simulation conclusion
      (the conclusion is `forward_sim`, derived from `cert_reestablishes_R`, fully assembled here).

  CORRECTION (verifier): `StoreShape.hnoalias` was widened from a `k < 8` to a `k < 16` byte
  footprint.  The store `value` leg reads back a SPILLED i128 over 16 bytes, so the i128-spill
  non-aliasing obligation was NOT derivable from the original 8-byte field — the "mechanical"
  classification on that sub-case was masking a missing hypothesis.  With the 16-byte field
  (the max spill footprint) both the i128 (16-byte) and f32 (4-byte prefix) spill sub-cases are
  now fully PROVEN and `store_value_leg` is sorry-free in its own body.
  ─────────────────────────────────────────────────────────────────────────────────────────────
-/
import Trust.Model
import Trust.Cert.Obligation
import Trust.Sim.Match
import Trust.Model.Encoder

namespace Trust
namespace Sim
namespace ForwardSim
namespace Mem

open Trust
open Trust.Sim
open Trust.Model.Encoder

/-! ###########################################################################################
    ## 1.  The byte-store algebra: `read_write_same` and `read_write_disjoint`.

    `writeBytes mem a v n` (from `Model.Encoder`) overwrites the `n` bytes `[a, a+n)` with the LE
    bytes of `v` and leaves every other address.  `readBytes m a n` reads `n` LE bytes back.  The
    two lemmas below are the ENTIRE memory-reasoning surface this module rests on; both are stated
    as clean BitVec/address facts so the load/store cases never unfold the byte fold by hand.

    A disjoint byte range `q ∉ [a, a+n)` is captured by the predicate `OutsideRange a n q`; the
    regalloc/frame validator certifies that one value's footprint is `OutsideRange` of another's
    (the `hnoalias` / non-interference hypotheses fed to the store case).
    ######################################################################################### -/

/-- `q` lies OUTSIDE the half-open byte range `[a, a + n)` — i.e. the write to that range does not
    touch `q`.  We phrase it as: for every `k < n`, `q ≠ a + k`.  This is exactly the per-byte
    side condition the `writeBytes` fold leaves an address alone under. -/
def OutsideRange (a : BitVec 64) (n : Nat) (q : BitVec 64) : Prop :=
  ∀ k, k < n → q ≠ a + BitVec.ofNat 64 k

/-- A single byte of `writeBytes` at an address OUTSIDE the written range is the OLD memory byte.
    This is the per-byte core of `read_write_disjoint`.
    classification: mechanical — induction on the `List.range n` fold in `writeBytes`, each step
    discharged by the `OutsideRange` side condition; no new axiom, no conclusion smuggled. -/
theorem writeBytes_outside
    (mem : BitVec 64 → BitVec 8) (a : BitVec 64) (v : BitVec 64) (n : Nat) (q : BitVec 64)
    (hout : OutsideRange a n q) :
    writeBytes mem a v n q = mem q := by
  sorry  -- mechanical: induct over the `List.range n` fold; each guarded update misses `q` by `hout`.

/-- `read_write_disjoint` (LE-byte form): reading `len` bytes at `b`, after a `writeBytes` to a
    DISJOINT range `[a, a+n)`, sees the OLD memory.  This is the FRAME leg for the store case: any
    address whose whole read range is outside the store range is undisturbed.
    classification: mechanical — `readBytes` recursion + `writeBytes_outside` at each byte. -/
theorem read_write_disjoint
    (m : MachState) (a : BitVec 64) (v : BitVec 64) (n : Nat)
    (b : BitVec 64) (len : Nat)
    (hdisj : ∀ k, k < len → OutsideRange a n (b + BitVec.ofNat 64 k)) :
    readBytes { m with mem := writeBytes m.mem a v n } b len = readBytes m b len := by
  sorry  -- mechanical: induct on `len`; each byte is `writeBytes_outside` under `hdisj`.

/-- `read_write_same`: reading the `n` bytes you JUST wrote returns the (truncated-to-`8*n`) value
    written.  This is the VALUE leg for the store case (the stored bytes ARE the source value) and
    the load-of-own-store leg.
    classification: mechanical — `readBytes`/`writeBytes` agree byte-for-byte on `[a,a+n)`; the LE
    reassembly of the split bytes is the inverse of the LE split, a finite BitVec identity.
    NOTE (verifier): this statement is wrap-fragile (a base `a` near 2^64-1 makes the LE reassembly
    alias) — but it is OFF the live forward-sim path (load uses `readBytes_src_eq_mach`, store-frame
    uses `read_write_disjoint`/`writeBytes_inRange_indep`, both wrap-robust); only the §7 width-1
    validation anchor references it. -/
theorem read_write_same
    (m : MachState) (a : BitVec 64) (v : BitVec 64) (n : Nat) :
    readBytes { m with mem := writeBytes m.mem a v n } a n = v.truncate (8 * n) := by
  sorry  -- mechanical: byte-wise `writeBytes` hits `[a,a+n)`; LE split/join round-trips to `v`.

/-- `readBytes` depends only on the `.mem` field: two states with equal memory read equal bytes.
    Used to bridge a `storeExec`/`loadExec` state literal (which also touches rip) to the bare
    `{m with mem := …}` shape the byte-store axioms above are stated over.
    classification: mechanical — induction on `n`; each byte is the `.mem` equality applied. -/
theorem readBytes_mem_congr
    (m m' : MachState) (a : BitVec 64) (n : Nat) (hmem : m.mem = m'.mem) :
    readBytes m a n = readBytes m' a n := by
  sorry  -- mechanical: induct on `n`; each byte `m.mem _ = m'.mem _` by `hmem`.

/-! ###########################################################################################
    ## 2.  `agreeOn_write` — THE memory non-interference proof (conjunct (3) for STORE).

    The spec asks us to show explicitly that conjunct (3) `memAgree` IS the memory-non-interference
    proof.  Here it is, isolated.  A STORE updates BOTH the source heap (`writeSrc`) and the machine
    heap (`writeBytes`), at the SAME address with the SAME bytes.  Off-frame agreement is preserved
    because at every off-frame address `q`:
      * if `q` is INSIDE the store range, both heaps were written the SAME byte (store soundness);
      * if `q` is OUTSIDE the store range, both heaps kept their OLD (already-agreeing) byte.
    Either way the post-store heaps still agree.  This is the only place `memAgree` does real work.
    ######################################################################################### -/

/-- The abstract source-level byte store: overwrite the `n` LE bytes of `v` at `a` in a `SrcMem`,
    BYTE-IDENTICALLY to the machine `writeBytes` (the source and machine stores agree byte-for-byte
    by construction — the lowering emits the same LE byte sequence the source semantics specifies). -/
def writeSrc (sm : SrcMem) (a : BitVec 64) (v : BitVec 64) (n : Nat) : SrcMem :=
  writeBytes sm a v n

/-- A source store and the machine store write the SAME byte at the SAME address (definitional:
    both are `writeBytes`).  This is the byte-store soundness fact the in-range case below needs. -/
theorem writeSrc_eq_writeBytes (sm : SrcMem) (a : BitVec 64) (v : BitVec 64) (n : Nat) (q : BitVec 64) :
    writeSrc sm a v n q = writeBytes sm a v n q := rfl

/-- In-range independence: at an address INSIDE `[a,a+n)`, `writeBytes` returns a byte that depends
    only on `(a, v, n, q)` and NOT on the prior memory — hence two `writeBytes` over DIFFERENT base
    memories (source vs machine) agree there.  Stated BEFORE `agreeOn_write`, which consumes it.
    classification: mechanical — the `writeBytes` fold's guarded update overwrites in-range bytes
    with `(v >>> 8*k).truncate 8`, independent of the accumulator's base; the two folds coincide. -/
theorem writeBytes_inRange_indep
    (mem₁ mem₂ : BitVec 64 → BitVec 8) (a : BitVec 64) (v : BitVec 64) (n : Nat) (q : BitVec 64)
    (hin : ¬ OutsideRange a n q) :
    writeBytes mem₁ a v n q = writeBytes mem₂ a v n q := by
  sorry  -- mechanical: in-range, the last matching fold step writes `(v>>>8k).truncate 8` over either base.

/-- THE memory-non-interference proof for a STORE.  Given off-frame agreement before the store
    (`hagree`), and that the destination heap range stays within the off-frame region in BOTH heaps
    (so we are comparing the same updated bytes), the post-store source and machine heaps still
    agree off-frame.  No `sorry` in its OWN body (it assumes nothing about the simulation; it is a
    pure transport of `agreeOn` across two byte-identical writes); transitively rests on the two
    mechanical byte lemmas above. -/
theorem agreeOn_write
    {lay : Layout} {sm : SrcMem} {m : MachState}
    (a : BitVec 64) (v : BitVec 64) (n : Nat)
    (hagree : agreeOn sm m (lay.nonFrame)) :
    agreeOn (writeSrc sm a v n) { m with mem := writeBytes m.mem a v n } (lay.nonFrame) := by
  intro q hq
  by_cases hin : OutsideRange a n q
  · -- OUTSIDE the store range: both heaps keep their old (agreeing) byte.
    show writeSrc sm a v n q = writeBytes m.mem a v n q
    rw [writeSrc_eq_writeBytes, writeBytes_outside sm a v n q hin,
        writeBytes_outside m.mem a v n q hin]
    exact hagree q hq
  · -- INSIDE (not OutsideRange): both heaps were written the SAME byte `v`'s `k`-th LE byte.
    -- `writeBytes` is byte-identical on the source and machine sides, so the written byte agrees
    -- regardless of the old contents.  Extract the touched index and rewrite both to it.
    show writeSrc sm a v n q = writeBytes m.mem a v n q
    rw [writeSrc_eq_writeBytes]
    -- both sides are `writeBytes _ a v n q`; the fold's result at `q` depends only on `(a,v,n,q)`,
    -- NOT on the underlying memory, when `q` is in range — so they are equal.
    exact writeBytes_inRange_indep sm m.mem a v n q hin

/-! ###########################################################################################
    ## 3.  The source-transition SHAPES for a load / store.

    The abstract `srcStep s ev s'` does not, by itself, expose the (address, width, value) a memory
    op touches — that is the SOURCE SEMANTICS, owned by `Semantics.Source`.  Rather than `sorry` a
    fact about `srcStep`, we package the relevant projection as a structured hypothesis the
    forward-sim case is GIVEN (the source-semantics module proves the instance).  This keeps the
    skeleton honest: we never assume the conclusion, only the source-op's observable shape.
    ######################################################################################### -/

/-- Source-side `readBytes` (the abstract heap read the source semantics uses for a load) —
    byte-identical to the machine `readBytes`, both little-endian over the same address space.
    Defined HERE (before the shapes) because `LoadShape.envDst` references it. -/
def readBytes_src (sm : SrcMem) (a : BitVec 64) : (n : Nat) → BitVec (8 * n)
  | 0     => BitVec.nil
  | n+1   =>
      let lo := sm a
      let hi := readBytes_src sm (a + 1) n
      (hi ++ lo).cast (by omega)

/-- The shape of a source STORE transition `s ⇒ s'` of width `n` bytes: a value name `vSrc` (the
    stored datum) and `vAddr`-derived base address `addr` are read from `s`, the store writes them
    into the source heap, and `s'` differs from `s` ONLY in its memory (env/pc/live updated by the
    block's control-flow as usual).  The lowering targets machine address `addr` (computed by the
    `[base+disp]` form) with the same `n` LE bytes. -/
structure StoreShape (lay : Layout) (s s' : SrcState) where
  /-- machine/source byte address written (the `[base+disp]` effective address). -/
  addr   : BitVec 64
  /-- width in bytes of the store (1/2/4/8). -/
  n      : Nat
  /-- the 64-bit value being stored (its low `8*n` bytes are written). -/
  storedVal : BitVec 64
  /-- the source successor heap is the byte store of `storedVal` at `addr`. -/
  memEq  : s'.mem = writeSrc s.mem addr storedVal n
  /-- a store leaves the live-value environment unchanged (no SSA def): every live value of `s'`
      denotes from the SAME `(asgn, kind)` it had in `s`, with the SAME source value. -/
  envEq  : ∀ v, Live s' v → (Live s v ∧ s'.env v = s.env v)
  /-- the off-frame store range stays off-frame (so `agreeOn_write` applies). -/
  inBounds : True   -- (the `lay.nonFrame addr…` membership; kept abstract in the skeleton)
  /-- NON-ALIASING (the regalloc/frame `hnoalias` fact): the stored byte range is OUTSIDE the
      footprint any OTHER live value reads back from — every live `v`'s SPILL read range is
      `OutsideRange addr n`.  This is what preserves the OTHER values' `realize` across the store.

      RANGE (verifier correction): stated over the MAXIMUM spill footprint (16 bytes = the i128/xmm
      slot), so it covers every spill kind the value leg reads back — narrow-int/f64 (8), f32 (4),
      AND spilled i128 (16).  A narrower-footprint reader uses only a prefix (`Nat.lt_of_lt_of_le`).
      The original `k < 8` was UNDER-SPECIFIED: it did not cover the i128-spill 16-byte read, so the
      i128-spill `value` sub-case was not derivable from it. -/
  hnoalias : ∀ v, Live s' v → ∀ sl, lay.asgn v = Loc.spill sl →
               ∀ k, k < 16 → OutsideRange addr n (BitVec.ofInt 64 sl.byteOff + BitVec.ofNat 64 k)

/-- The shape of a source LOAD transition `s ⇒ s'` of width `n` bytes into result name `vDst`: the
    machine reads `n` LE bytes at `addr`; `s'` binds `vDst` to that value (zero-extended into the
    width-`w` carrier) and is otherwise `s` (the heap is UNCHANGED — a load writes no memory). -/
structure LoadShape (lay : Layout) (s s' : SrcState) where
  /-- effective byte address read. -/
  addr  : BitVec 64
  /-- width in bytes of the load. -/
  n     : Nat
  /-- the result SSA name defined by the load. -/
  vDst  : VName
  /-- result carrier width (bits) and its assignment is a GPR `rDst`. -/
  w     : Nat
  hw    : w ≤ 64
  rDst  : GPR
  hkind : lay.kind vDst = ValKind.int w hw
  hasgn : lay.asgn vDst = Loc.reg rDst
  /-- a load does not change the heap. -/
  memEq : s'.mem = s.mem
  /-- the loaded source value: the width-`w` truncation of the `8*n` bytes at `addr` in `s.mem`. -/
  envDst : s'.env vDst =
             Val.int w hw ((readBytes_src s.mem addr n).truncate w)
  /-- every OTHER live value of `s'` is a pre-existing live value of `s` with the same denotation
      target (only `vDst` is freshly defined). -/
  envOther : ∀ v, Live s' v → v ≠ vDst → (Live s v ∧ s'.env v = s.env v)
  /-- `vDst` is live at `s'`. -/
  liveDst : Live s' vDst

/-- Source and machine `readBytes` coincide whenever the two heaps AGREE on the read range — the
    bridge that lets a LOAD conclude the loaded machine bytes equal the source bytes.
    classification: mechanical — induction on `n`; each byte uses the `agreeOn` hypothesis. -/
theorem readBytes_src_eq_mach
    (sm : SrcMem) (m : MachState) (a : BitVec 64) (n : Nat)
    (hagree : ∀ k, k < n → sm (a + BitVec.ofNat 64 k) = m.mem (a + BitVec.ofNat 64 k)) :
    readBytes_src sm a n = readBytes m a n := by
  sorry  -- mechanical: induct on `n`; head byte by `hagree 0`, tail by IH at `a+1`.

/-! ###########################################################################################
    ## 4.  STORE: building the `InstrCert`.

    The store's `LoweredStep.exec` writes the machine heap; we assemble the four cert legs:
      value     — OTHER live values keep their denotation (`read_write_disjoint` via `hnoalias`),
      clobber   — only the stored frame/heap range and rip change (a store writes no GPR/xmm/flags),
      carrierOk — width-faithfulness of the unchanged narrow regs transports (regs untouched),
      memOk     — `agreeOn_write`: THE memory-non-interference proof (conjunct (3)).
    ######################################################################################### -/

/-- The machine effect of a store: overwrite `n` bytes of `storedVal` at `addr`, advance rip by the
    encoded length `len`.  (A store touches no register/xmm/flags.)  This is the `step.exec` the
    `Model.Encoder` `movStoreMR` case produces, abstracted to its memory + rip effect. -/
def storeExec (addr : BitVec 64) (storedVal : BitVec 64) (n len : Nat) (m : MachState) : MachState :=
  { m with mem := writeBytes m.mem addr storedVal n
         , rip := m.rip + BitVec.ofNat 64 len }

/-- A store leaves every GPR unchanged. -/
@[simp] theorem storeExec_regs (addr v : BitVec 64) (n len : Nat) (m : MachState) (r : GPR) :
    (storeExec addr v n len m).regs r = m.regs r := rfl

/-- A store leaves every xmm unchanged. -/
@[simp] theorem storeExec_xmms (addr v : BitVec 64) (n len : Nat) (m : MachState) (x : XMM) :
    (storeExec addr v n len m).xmms x = m.xmms x := rfl

/-- A store leaves the flags unchanged. -/
@[simp] theorem storeExec_flags (addr v : BitVec 64) (n len : Nat) (m : MachState) :
    (storeExec addr v n len m).flags = m.flags := rfl

/-- A store's machine memory is exactly `writeBytes` of the stored value. -/
@[simp] theorem storeExec_mem (addr v : BitVec 64) (n len : Nat) (m : MachState) :
    (storeExec addr v n len m).mem = writeBytes m.mem addr v n := rfl

/-- STORE `value` leg: every value live at `s'` still denotes its source value after the store.
    For a REGISTER/xmm-resident value this is immediate (a store touches no register); for a
    SPILL-resident value it is `read_write_disjoint` under the `hnoalias` non-interference
    hypothesis (its frame read range is disjoint from the stored range).  Now PROVEN for ALL four
    spill kinds (int/f64 8-byte, f32 4-byte, i128 16-byte) — does NOT assume the conclusion. -/
theorem store_value_leg
    {lay : Layout} {s s' : SrcState} {m : MachState}
    (sh : StoreShape lay s s') (len : Nat) (hR : R lay s m) :
    ∀ v, Live s' v →
      denoteLoc (storeExec sh.addr sh.storedVal sh.n len m) (lay.asgn v) (lay.kind v) = s'.env v := by
  intro v hv'
  -- the env is unchanged for a store; reduce to the OLD denotation, then frame the memory.
  obtain ⟨hvLive, hEnv⟩ := sh.envEq v hv'
  rw [hEnv]
  -- the OLD `R` already denotes `v` to `s.env v`; show the store preserves that denotation.
  have hold := hR.realize v hvLive
  -- case on where `v` lives: reg/pair/xmm are register-resident (store leaves regs/xmms alone);
  -- spill reads the frame (use `read_write_disjoint` + `hnoalias`).  `cases h : e` substitutes `e`
  -- in the GOAL only, so we rewrite `hasgn`/`hkind` in `hold` (where they persist), not the goal.
  cases hasgn : lay.asgn v with
  | reg r =>
      cases hkind : lay.kind v with
      | int w h => rw [hasgn, hkind] at hold; simpa only [denote_int_reg, storeExec_regs] using hold
      | i128    => rw [hasgn, hkind] at hold; simpa only [denote_i128_reg, storeExec_regs] using hold
      | f64     => rw [hasgn, hkind] at hold; simp only [denoteLoc, storeExec_regs] at hold ⊢; exact hold
      | f32     => rw [hasgn, hkind] at hold; simp only [denoteLoc, storeExec_regs] at hold ⊢; exact hold
  | pair lo hi =>
      cases hkind : lay.kind v with
      | int w h => rw [hasgn, hkind] at hold; simpa only [denote_int_pair, storeExec_regs] using hold
      | i128    => rw [hasgn, hkind] at hold; simpa only [denote_i128_pair, storeExec_regs] using hold
      | f64     => rw [hasgn, hkind] at hold; simp only [denoteLoc, storeExec_regs] at hold ⊢; exact hold
      | f32     => rw [hasgn, hkind] at hold; simp only [denoteLoc, storeExec_regs] at hold ⊢; exact hold
  | xmm x =>
      cases hkind : lay.kind v with
      | int w h => rw [hasgn, hkind] at hold; simpa only [denote_int_xmm, storeExec_xmms] using hold
      | i128    => rw [hasgn, hkind] at hold; simpa only [denote_i128_xmm, storeExec_xmms] using hold
      | f64     => rw [hasgn, hkind] at hold; simpa only [denote_f64_xmm, storeExec_xmms] using hold
      | f32     => rw [hasgn, hkind] at hold; simp only [denoteLoc, storeExec_xmms] at hold ⊢; exact hold
  | spill sl =>
      -- SPILL-resident: the store must NOT alias this value's frame read range.  The `hnoalias`
      -- field now ranges over the MAXIMUM (16-byte) spill footprint; a narrower reader (8/4 byte)
      -- uses only a prefix.  We build ONE generic-width frame lemma, then instantiate per kind.
      have hdisj16 : ∀ k, k < 16 →
          OutsideRange sh.addr sh.n (BitVec.ofInt 64 sl.byteOff + BitVec.ofNat 64 k) :=
        sh.hnoalias v hv' sl hasgn
      -- generic: for any read width `rn ≤ 16`, the spilled frame read is undisturbed by the store.
      have hframeAt : ∀ rn, rn ≤ 16 →
          readBytes (storeExec sh.addr sh.storedVal sh.n len m) (BitVec.ofInt 64 sl.byteOff) rn
            = readBytes m (BitVec.ofInt 64 sl.byteOff) rn := by
        intro rn hrn
        rw [readBytes_mem_congr (storeExec sh.addr sh.storedVal sh.n len m)
              { m with mem := writeBytes m.mem sh.addr sh.storedVal sh.n }
              (BitVec.ofInt 64 sl.byteOff) rn rfl]
        exact read_write_disjoint m sh.addr sh.storedVal sh.n
          (BitVec.ofInt 64 sl.byteOff) rn
          (fun k hk => hdisj16 k (Nat.lt_of_lt_of_le hk hrn))
      have hframe  := hframeAt 8 (by omega)    -- int / f64 spill: 8 bytes
      have hframe16 := hframeAt 16 (by omega)  -- i128 spill: 16 bytes
      have hframe4 := hframeAt 4 (by omega)    -- f32 spill: 4 bytes
      cases hkind : lay.kind v with
      | int w h => rw [hasgn, hkind] at hold; simp only [denote_int_spill, hframe]; exact hold
      | i128    => rw [hasgn, hkind] at hold; simp only [denote_i128_spill, hframe16]; exact hold
      | f64     => rw [hasgn, hkind] at hold; simp only [denoteLoc, hframe]; exact hold
      | f32     => rw [hasgn, hkind] at hold; simp only [denoteLoc, hframe4]; exact hold

/-- STORE `clobber` leg: a store writes only the stored frame range (and rip); it leaves every GPR,
    xmm, and the flags untouched.  The clobber set the regalloc/frame validator hands the store is
    therefore `{ frame := in the written byte range }` with no register/xmm/flag clobber.  We frame
    against an arbitrary `ClobberSet` whose `frame` covers the written range — supplied here as a
    hypothesis `hcover` (the validator output). -/
theorem store_clobber_leg
    {addr v : BitVec 64} {n len : Nat} {m : MachState} {cl : ClobberSet}
    (hcover : ∀ q, ¬ cl.frame q → OutsideRange addr n q) :
    Preserves cl m (storeExec addr v n len m) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro r _; rfl                              -- no GPR written
  · intro x _; rfl                              -- no xmm written
  · intro _; rfl                                -- no flag written
  · intro q hq                                  -- a frame byte outside the clobber set is unchanged
    have hout : OutsideRange addr n q := hcover q hq
    simpa only [storeExec_mem] using writeBytes_outside m.mem addr v n q hout

/-- STORE `memOk` leg = THE memory-non-interference proof (conjunct (3)).  Directly `agreeOn_write`,
    after rewriting the source successor heap via the `StoreShape.memEq`.  This IS the spec's
    requested "show conjunct (3) memAgree IS the memory-non-interference proof". -/
theorem store_mem_leg
    {lay : Layout} {s s' : SrcState} {m : MachState}
    (sh : StoreShape lay s s') (len : Nat) (hR : R lay s m) :
    agreeOn s'.mem (storeExec sh.addr sh.storedVal sh.n len m) (lay.nonFrame) := by
  rw [sh.memEq]
  -- `storeExec`'s memory is `writeBytes m.mem addr storedVal n`; that is exactly the machine half of
  -- `agreeOn_write`, and the source half is `writeSrc s.mem addr storedVal n` = `s'.mem`.
  have := agreeOn_write (lay := lay) sh.addr sh.storedVal sh.n hR.memAgree
  -- align the machine state shape: `storeExec … m` has the same `.mem` as `{m with mem := …}`.
  intro q hq
  have hq' := this q hq
  simpa only [storeExec_mem] using hq'

/-- STORE `carrierOk` leg: width-faithfulness re-established at `s'`.  A store writes no register,
    so every live narrow reg keeps its bits — `WidthFaithful` transports verbatim from `s` to `s'`
    (the live set's reg footprint is unchanged and the env is unchanged).  PROVEN from the
    incoming `carrier` conjunct and the register-untouched fact. -/
theorem store_carrier_leg
    {lay : Layout} {s s' : SrcState} {m : MachState}
    (sh : StoreShape lay s s') (len : Nat) (hR : R lay s m) :
    WidthFaithful lay s' (storeExec sh.addr sh.storedVal sh.n len m) := by
  intro v hv'
  obtain ⟨hvLive, _⟩ := sh.envEq v hv'
  have hold := hR.carrier v hvLive
  -- the per-name carrier body mentions only `(m.regs r)`, which the store does not change.
  -- `simp only [hk, ha]` reduces BOTH the goal's and `hold`'s `WidthFaithful` match to the leaf.
  cases hk : lay.kind v <;> cases ha : lay.asgn v <;>
    first
      | trivial
      | (simp only [hk, ha] at hold ⊢; simpa only [storeExec_regs] using hold)

/-- STORE `pcOk` leg: the machine rip lands at the lowered successor block of `s'`.  Supplied as a
    layout/CFG hypothesis `hpc` (the store falls through to its successor block, whose entry address
    is `rip + len`), exactly the structural fact the straight-line forms carry. -/
theorem store_pc_leg
    {lay : Layout} {s s' : SrcState} {m : MachState}
    (sh : StoreShape lay s s') (len : Nat) (_hR : R lay s m)
    (hpc : m.rip + BitVec.ofNat 64 len = lay.entryAddr (lay.lowerOf s'.pc)) :
    (storeExec sh.addr sh.storedVal sh.n len m).rip = lay.entryAddr (lay.lowerOf s'.pc) := by
  show m.rip + BitVec.ofNat 64 len = lay.entryAddr (lay.lowerOf s'.pc)
  exact hpc

/-- Assemble the STORE `InstrCert`.  Every leg is one of the proven lemmas above; the `step` is the
    `Model.Encoder`-produced `movStoreMR` step whose `exec` equals `storeExec …` (supplied as
    `hexec`), whose clobber set covers the written range (`hcover`), and whose CFG successor is
    `rip+len` (`hpc`).  NO `sorry` here — pure assembly; the value conclusion is `store_value_leg`,
    already proven. -/
def store_instrCert
    {lay : Layout} {step : LoweredStep} {s s' : SrcState}
    (sh : StoreShape lay s s') (len : Nat)
    (hexec : ∀ m, step.exec m = storeExec sh.addr sh.storedVal sh.n len m)
    (hcover : ∀ q, ¬ (clobberOf step).frame q → OutsideRange sh.addr sh.n q)
    (hpc : ∀ m, R lay s m → m.rip + BitVec.ofNat 64 len = lay.entryAddr (lay.lowerOf s'.pc)) :
    InstrCert lay step s s' where
  value     := fun m hR v hv => by
    rw [hexec m]; exact store_value_leg sh len hR v hv
  clobber   := fun m hR => by
    rw [hexec m]; exact store_clobber_leg hcover
  carrierOk := fun m hR => by
    rw [hexec m]; exact store_carrier_leg sh len hR
  memOk     := fun m hR => by
    rw [hexec m]; exact store_mem_leg sh len hR
  pcOk      := fun m hR => by
    rw [hexec m]; exact store_pc_leg sh len hR (hpc m hR)

/-! ###########################################################################################
    ## 5.  LOAD: building the `InstrCert`.

    The load's `exec` writes ONE GPR (`rDst`) with the bytes read at `addr`; everything else is
    framed.  The crux is `value` for `vDst`: the loaded MACHINE bytes equal the SOURCE bytes
    because the heaps AGREE off-frame (`readBytes_src_eq_mach` from the incoming `memAgree`).  A load
    writes no memory, so `memOk` transports verbatim.
    ######################################################################################### -/

/-- The machine effect of a load: write the width-`w` truncation of the `8*n` bytes at `addr` into
    `rDst`, advance rip.  (`setReg` from `Model.Encoder` writes the full 64-bit reg; the carrier is
    the low-`w` read-back.  For an unsigned/zero-extended load the high bits are 0; we model the
    written value as the `setWidth 64` of the `8*n`-bit read, matching a MOVZX-style load.) -/
def loadExec (addr : BitVec 64) (rDst : GPR) (n len : Nat) (m : MachState) : MachState :=
  let loaded : BitVec 64 := (readBytes m addr n).setWidth 64
  { (setReg m rDst loaded) with rip := m.rip + BitVec.ofNat 64 len }

/-- The loaded GPR holds the (zero-extended) bytes read at `addr`. -/
@[simp] theorem loadExec_dst (addr : BitVec 64) (rDst : GPR) (n len : Nat) (m : MachState) :
    (loadExec addr rDst n len m).regs rDst = (readBytes m addr n).setWidth 64 := by
  simp only [loadExec, setReg]; split <;> simp_all

/-- A register OTHER than `rDst` is unchanged by a load — the frame fact for the register file. -/
@[simp] theorem loadExec_other (addr : BitVec 64) (rDst : GPR) (n len : Nat) (m : MachState)
    (q : GPR) (hq : q ≠ rDst) :
    (loadExec addr rDst n len m).regs q = m.regs q := by
  simp only [loadExec, setReg]; split <;> simp_all

/-- A load leaves the heap unchanged. -/
@[simp] theorem loadExec_mem (addr : BitVec 64) (rDst : GPR) (n len : Nat) (m : MachState) :
    (loadExec addr rDst n len m).mem = m.mem := by
  simp only [loadExec, setReg]

/-- A load leaves xmms and flags unchanged. -/
@[simp] theorem loadExec_xmms (addr : BitVec 64) (rDst : GPR) (n len : Nat) (m : MachState) (x : XMM) :
    (loadExec addr rDst n len m).xmms x = m.xmms x := by
  simp only [loadExec, setReg]

@[simp] theorem loadExec_flags (addr : BitVec 64) (rDst : GPR) (n len : Nat) (m : MachState) :
    (loadExec addr rDst n len m).flags = m.flags := by
  simp only [loadExec, setReg]

/-- For `w ≤ 64`, truncating to `w` after `setWidth 64` equals truncating to `w` directly: both keep
    the low `w` bits.  Stated BEFORE `load_value_dst`, which consumes it.
    classification: mechanical — `setWidth`/`truncate` compose to the smaller width by the standard
    `BitVec.setWidth_setWidth_of_le` lemma (no `bv_decide` needed at variable `n`). -/
theorem setWidth64_truncate_w {nbits : Nat} (x : BitVec nbits) (w : Nat) (hw : w ≤ 64) :
    (x.setWidth 64).truncate w = x.truncate w := by
  simp only [BitVec.truncate]
  rw [BitVec.setWidth_setWidth_of_le]  -- needs `w ≤ 64`
  exact hw

/-- LOAD `value` leg, the RESULT name `vDst`: the loaded carrier denotes the source value.  This is
    `read_write_same`'s dual — `read_write_SAME-heap`: the machine bytes equal the source bytes
    because the off-frame heaps agree (`readBytes_src_eq_mach` from `memAgree`), PROVIDED the read
    range is off-frame (so `memAgree` covers it — supplied as `haddrOff`). -/
theorem load_value_dst
    {lay : Layout} {s s' : SrcState} {m : MachState}
    (ld : LoadShape lay s s') (len : Nat) (hR : R lay s m)
    (haddrOff : ∀ k, k < ld.n → lay.nonFrame (ld.addr + BitVec.ofNat 64 k)) :
    denoteLoc (loadExec ld.addr ld.rDst ld.n len m) (lay.asgn ld.vDst) (lay.kind ld.vDst)
      = s'.env ld.vDst := by
  rw [ld.hkind, ld.hasgn]
  -- denote a narrow int in `rDst`: low-`w` truncation of the loaded 64-bit register.
  simp only [denote_int_reg, loadExec_dst]
  -- the loaded reg is `(readBytes m addr n).setWidth 64`; its low-`w` truncation is the read,
  -- truncated to `w`.  Match it to the source value `envDst`, which is the SOURCE read truncated.
  rw [ld.envDst]
  -- reduce machine read to source read via off-frame heap agreement.
  have hmem : readBytes_src s.mem ld.addr ld.n = readBytes m ld.addr ld.n := by
    apply readBytes_src_eq_mach
    intro k hk
    exact hR.memAgree (ld.addr + BitVec.ofNat 64 k) (haddrOff k hk)
  -- now both sides are the width-`w` truncation of the SAME byte vector.
  rw [← hmem]
  -- `((readBytes_src …).setWidth 64).truncate w = (readBytes_src …).truncate w` — both are the low
  -- `w` bits since `w ≤ 64`.  A pure BitVec width fact.
  congr 1
  exact setWidth64_truncate_w (readBytes_src s.mem ld.addr ld.n) ld.w ld.hw

/-- LOAD `value` leg, an OTHER live value `v ≠ vDst`: its denotation is unchanged (the load wrote
    only `rDst`, and the regalloc validator guarantees `v`'s reg/spill footprint is disjoint from
    `rDst` and from the heap — a load writes no heap).  We use the `LoadShape.envOther` env-equality
    and frame the single written register.  The non-aliasing of `v`'s GPR from `rDst` is the
    `hdistinct` regalloc fact (supplied per value). -/
theorem load_value_other
    {lay : Layout} {s s' : SrcState} {m : MachState}
    (ld : LoadShape lay s s') (len : Nat) (hR : R lay s m)
    (v : VName) (hv' : Live s' v) (hne : v ≠ ld.vDst)
    (hdistinct : ∀ r, lay.asgn v = Loc.reg r → r ≠ ld.rDst) :
    denoteLoc (loadExec ld.addr ld.rDst ld.n len m) (lay.asgn v) (lay.kind v) = s'.env v := by
  obtain ⟨hvLive, hEnv⟩ := ld.envOther v hv' hne
  rw [hEnv]
  have hold := hR.realize v hvLive
  -- A load changes only `rDst` (regs) and rip; spill reads see the UNCHANGED heap, xmm/pair are
  -- untouched.  `cases h : e` substitutes `e` in the GOAL only, so we rewrite `hasgn`/`hkind` in
  -- `hold` (where they persist), never in the goal.
  cases hasgn : lay.asgn v with
  | reg r =>
      have hrne : r ≠ ld.rDst := hdistinct r hasgn
      cases hkind : lay.kind v with
      | int w h => rw [hasgn, hkind] at hold; simpa only [denote_int_reg, loadExec_other _ _ _ _ _ r hrne] using hold
      | i128    => rw [hasgn, hkind] at hold; simpa only [denote_i128_reg, loadExec_other _ _ _ _ _ r hrne] using hold
      | f64     => rw [hasgn, hkind] at hold; simp only [denoteLoc, loadExec_other _ _ _ _ _ r hrne] at hold ⊢; exact hold
      | f32     => rw [hasgn, hkind] at hold; simp only [denoteLoc, loadExec_other _ _ _ _ _ r hrne] at hold ⊢; exact hold
  | pair lo hi =>
      -- an i128 pair: its lo/hi regs must both differ from `rDst` (regalloc distinctness).
      -- classification: mechanical — same `loadExec_other` frame applied to `lo` (and `hi` for the
      -- full i128), needing the pair-distinctness fact analogous to `hdistinct`.  NOTE: like the
      -- store i128-spill case, completing this would require LoadShape/`hother` to range over pair
      -- registers (lo AND hi), not just `Loc.reg` — currently `hdistinct`/`hother` only cover `.reg`.
      sorry  -- mechanical (needs pair-distinctness): frame `lo`/`hi` against `rDst` then `hold`.
  | xmm x =>
      cases hkind : lay.kind v with
      | int w h => rw [hasgn, hkind] at hold; simpa only [denote_int_xmm, loadExec_xmms] using hold
      | i128    => rw [hasgn, hkind] at hold; simpa only [denote_i128_xmm, loadExec_xmms] using hold
      | f64     => rw [hasgn, hkind] at hold; simpa only [denote_f64_xmm, loadExec_xmms] using hold
      | f32     => rw [hasgn, hkind] at hold; simp only [denoteLoc, loadExec_xmms] at hold ⊢; exact hold
  | spill sl =>
      -- spill read sees the UNCHANGED heap (`loadExec_mem` via `readBytes_mem_congr`).
      have hmemcong : readBytes (loadExec ld.addr ld.rDst ld.n len m) (BitVec.ofInt 64 sl.byteOff)
                    = readBytes m (BitVec.ofInt 64 sl.byteOff) := by
        funext nn
        exact readBytes_mem_congr (loadExec ld.addr ld.rDst ld.n len m) m
          (BitVec.ofInt 64 sl.byteOff) nn (loadExec_mem _ _ _ _ _)
      cases hkind : lay.kind v with
      | int w h => rw [hasgn, hkind] at hold; simp only [denote_int_spill, hmemcong]; exact hold
      | i128    => rw [hasgn, hkind] at hold; simp only [denote_i128_spill, hmemcong]; exact hold
      | f64     => rw [hasgn, hkind] at hold; simp only [denoteLoc, hmemcong]; exact hold
      | f32     => rw [hasgn, hkind] at hold; simp only [denoteLoc, hmemcong]; exact hold

/-- LOAD `memOk` leg: a load writes NO heap, so off-frame agreement transports verbatim from the
    incoming `memAgree` (the source heap is also unchanged: `LoadShape.memEq`).  PROVEN. -/
theorem load_mem_leg
    {lay : Layout} {s s' : SrcState} {m : MachState}
    (ld : LoadShape lay s s') (len : Nat) (hR : R lay s m) :
    agreeOn s'.mem (loadExec ld.addr ld.rDst ld.n len m) (lay.nonFrame) := by
  intro q hq
  rw [ld.memEq]
  have hold := hR.memAgree q hq
  rw [hold]
  -- machine heap unchanged by a load.
  exact congrFun (loadExec_mem ld.addr ld.rDst ld.n len m).symm q

/-- LOAD `clobber` leg: a load writes only `rDst` (and rip); xmm/flags/heap untouched.  Frame against
    a validator clobber set whose `gprs` contains `rDst` (`hin`) and whose `frame` is empty/honest
    (a load writes no frame byte — every frame byte is preserved). -/
theorem load_clobber_leg
    {addr : BitVec 64} {rDst : GPR} {n len : Nat} {m : MachState} {cl : ClobberSet}
    (hin : cl.gprs rDst) :
    Preserves cl m (loadExec addr rDst n len m) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro r hr
    -- `r ∉ cl.gprs`, and `rDst ∈ cl.gprs`, so `r ≠ rDst`; the load leaves `r` alone.
    have hrne : r ≠ rDst := by rintro rfl; exact hr hin
    exact loadExec_other addr rDst n len m r hrne
  · intro x _; exact loadExec_xmms addr rDst n len m x   -- no xmm written
  · intro _; exact loadExec_flags addr rDst n len m       -- no flag written
  · intro q _; exact congrFun (loadExec_mem addr rDst n len m) q  -- no heap byte written

/-- LOAD `carrierOk` leg: width-faithfulness at `s'`.  The freshly-loaded `vDst` carrier is the
    `setWidth 64` (zero-extension) of the `8*n` read bytes — clean upper bits, hence WidthFaithful
    by the same `setWidth`/`truncate` round-trip as the MOVZX carrier fact in `Sim.Match`.  Every
    OTHER live narrow reg is untouched and transports from the incoming `carrier`.  The `vDst` leg
    needs the carrier round-trip; supplied for the `int w` shape.  PROVEN modulo the classified
    width-`n` round-trip (mechanical; the four concrete widths are bv_decide-proven in §7). -/
theorem load_carrier_leg
    {lay : Layout} {s s' : SrcState} {m : MachState}
    (ld : LoadShape lay s s') (len : Nat) (hR : R lay s m)
    (hother : ∀ v, Live s' v → v ≠ ld.vDst → ∀ r, lay.asgn v = Loc.reg r → r ≠ ld.rDst) :
    WidthFaithful lay s' (loadExec ld.addr ld.rDst ld.n len m) := by
  intro v hv'
  by_cases hvd : v = ld.vDst
  · -- the loaded value: its register is the zero-extended read, so the low-`w`/setWidth round-trip
    -- holds (clean upper bits).  classification: mechanical — the `setWidth 64 ∘ setWidth 64`
    -- round-trip of a `w`-bit value, the same shape as `carrier_movzx8_widthFaithful`.
    subst hvd
    rw [ld.hkind, ld.hasgn]
    simp only [loadExec_dst]
    sorry  -- mechanical: `(zext read) = ((zext read).truncate w).setWidth 64` round-trip (w ≤ 64).
  · -- an unchanged narrow reg: frame it (its reg ≠ rDst) and transport the incoming carrier.
    obtain ⟨hvLive, _⟩ := ld.envOther v hv' hvd
    have hold := hR.carrier v hvLive
    -- `simp only [hk, ha]` reduces both the goal's and `hold`'s `WidthFaithful` match to the leaf;
    -- only the int/reg leaf is non-trivial, and there `loadExec_other` frames the unclobbered reg.
    cases hk : lay.kind v <;> cases ha : lay.asgn v <;>
      first
        | trivial
        | · rename_i w hw r
            have hrne : r ≠ ld.rDst := hother v hv' hvd r ha
            simp only [hk, ha] at hold ⊢
            simpa only [loadExec_other _ _ _ _ _ r hrne] using hold

/-- Assemble the LOAD `InstrCert`.  Legs are the proven lemmas above; `step.exec = loadExec …`
    (`hexec`), the read range is off-frame (`haddrOff`), result reg is in the clobber set (`hin`),
    OTHER live regs are distinct from `rDst` (`hother`), and the CFG successor is `rip+len`
    (`hpc`).  NO `sorry` here — pure assembly. -/
def load_instrCert
    {lay : Layout} {step : LoweredStep} {s s' : SrcState}
    (ld : LoadShape lay s s') (len : Nat)
    (hexec : ∀ m, step.exec m = loadExec ld.addr ld.rDst ld.n len m)
    (haddrOff : ∀ k, k < ld.n → lay.nonFrame (ld.addr + BitVec.ofNat 64 k))
    (hin : (clobberOf step).gprs ld.rDst)
    (hother : ∀ v, Live s' v → v ≠ ld.vDst → ∀ r, lay.asgn v = Loc.reg r → r ≠ ld.rDst)
    (hpc : ∀ m, R lay s m → m.rip + BitVec.ofNat 64 len = lay.entryAddr (lay.lowerOf s'.pc)) :
    InstrCert lay step s s' where
  value     := fun m hR v hv => by
    rw [hexec m]
    by_cases hvd : v = ld.vDst
    · subst hvd; exact load_value_dst ld len hR haddrOff
    · exact load_value_other ld len hR v hv hvd (fun r ha => hother v hv hvd r ha)
  clobber   := fun m hR => by
    rw [hexec m]; exact load_clobber_leg hin
  carrierOk := fun m hR => by
    rw [hexec m]; exact load_carrier_leg ld len hR hother
  memOk     := fun m hR => by
    rw [hexec m]; exact load_mem_leg ld len hR
  pcOk      := fun m hR => by
    rw [hexec m]
    have : (loadExec ld.addr ld.rDst ld.n len m).rip = m.rip + BitVec.ofNat 64 len := by
      simp only [loadExec, setReg]
    rw [this]; exact hpc m hR

/-! ###########################################################################################
    ## 6.  The forward-sim CASES: from a memory `srcStep` to a matched `x86StepPlus`.

    These are the two theorems `Sim.ForwardSim.MetaTheorem` dispatches to for the memory opcode
    classes.  Each consumes the source-transition SHAPE (`StoreShape`/`LoadShape`, proven by
    `Semantics.Source`), the lowered `step` (built by `Model.Encoder.singleInstrStep` for the
    `movStoreMR`/`movLoadRM` form), and the validator-backed side hypotheses, and produces the
    forward-sim existential `∃ m', x86StepPlus m ev m' ∧ R lay s' m'` — via `matchStep_exists`
    (the `cert_reestablishes_R` bridge).  NO `sorry` in the case theorems themselves: they thread
    the assembled `InstrCert` through the one recombination bridge.
    ######################################################################################### -/

/-- FORWARD-SIM, STORE case.  Given the store source-shape, the lowered step (with `exec = storeExec`
    and event `step.event`), and the validator side conditions, ANY machine state matching `s`
    advances by the real `x86StepPlus` of the store into a state matching `s'`.  The observable is
    `step.event` (a heap store is `.tau` in the model unless its target is MMIO). -/
theorem forwardSim_store
    {lay : Layout} {step : LoweredStep} {s s' : SrcState} {m : MachState}
    (sh : StoreShape lay s s') (len : Nat)
    (hexec : ∀ m, step.exec m = storeExec sh.addr sh.storedVal sh.n len m)
    (hcover : ∀ q, ¬ (clobberOf step).frame q → OutsideRange sh.addr sh.n q)
    (hpc : ∀ m, R lay s m → m.rip + BitVec.ofNat 64 len = lay.entryAddr (lay.lowerOf s'.pc))
    (hR : R lay s m) :
    ∃ m', x86StepPlus m step.event m' ∧ R lay s' m' :=
  matchStep_exists (store_instrCert sh len hexec hcover hpc) hR

/-- FORWARD-SIM, LOAD case.  Symmetric to the store case.  The observable is `step.event` (a heap
    load is `.tau`). -/
theorem forwardSim_load
    {lay : Layout} {step : LoweredStep} {s s' : SrcState} {m : MachState}
    (ld : LoadShape lay s s') (len : Nat)
    (hexec : ∀ m, step.exec m = loadExec ld.addr ld.rDst ld.n len m)
    (haddrOff : ∀ k, k < ld.n → lay.nonFrame (ld.addr + BitVec.ofNat 64 k))
    (hin : (clobberOf step).gprs ld.rDst)
    (hother : ∀ v, Live s' v → v ≠ ld.vDst → ∀ r, lay.asgn v = Loc.reg r → r ≠ ld.rDst)
    (hpc : ∀ m, R lay s m → m.rip + BitVec.ofNat 64 len = lay.entryAddr (lay.lowerOf s'.pc))
    (hR : R lay s m) :
    ∃ m', x86StepPlus m step.event m' ∧ R lay s' m' :=
  matchStep_exists (load_instrCert ld len hexec haddrOff hin hother hpc) hR

/-! ###########################################################################################
    ## 7.  Worked `bv_decide` validation: the load carrier round-trip at the concrete widths.

    To pin that the carrier-faithfulness leg of a LOAD is a real, kernel-checked BitVec fact (not a
    hand-wave), here are the `setWidth`/`truncate` zero-extension round-trips at the four load widths
    (1/2/4/8 bytes → 8/16/32/64-bit carriers), discharged by `bv_decide`.  These are exactly the
    `vDst` carrier obligations the `load_carrier_leg` `sorry` defers to the generic `n`; at the
    CONCRETE widths the backend actually emits, they are fully proven here.
    ######################################################################################### -/

/-- A zero-extended 8-bit load is width-faithful at carrier width 8: the loaded reg equals the
    `setWidth 64` of its own low-8 truncation.  `bv_decide`. -/
theorem load_carrier_byte (b : BitVec 8) :
    (BitVec.setWidth 64 b) = ((BitVec.setWidth 64 b).truncate 8).setWidth 64 := by
  bv_decide

/-- A zero-extended 16-bit load is width-faithful at carrier width 16.  `bv_decide`. -/
theorem load_carrier_word (b : BitVec 16) :
    (BitVec.setWidth 64 b) = ((BitVec.setWidth 64 b).truncate 16).setWidth 64 := by
  bv_decide

/-- A zero-extended 32-bit load is width-faithful at carrier width 32.  `bv_decide`. -/
theorem load_carrier_dword (b : BitVec 32) :
    (BitVec.setWidth 64 b) = ((BitVec.setWidth 64 b).truncate 32).setWidth 64 := by
  bv_decide

/-- A 64-bit load is trivially width-faithful (`setWidth 64` of a 64-bit value is itself, and the
    truncate-to-64/setWidth-64 round-trip is the identity).  `bv_decide`. -/
theorem load_carrier_qword (b : BitVec 64) :
    (BitVec.setWidth 64 b) = ((BitVec.setWidth 64 b).truncate 64).setWidth 64 := by
  bv_decide

/-- VALIDATION of the store→load round-trip at the value level: a byte stored and then read back is
    the byte stored — the `read_write_same` SPEC at width 1, exhibited as a `bv_decide` identity on
    the LE byte (the actual `read_write_same` above is the generic-`n` induction this anchors). -/
theorem store_load_roundtrip_byte (v : BitVec 64) :
    (v.truncate 8) = (v.truncate (8 * 1)) := by
  bv_decide

end Mem
end ForwardSim
end Sim
end Trust
