/-
  Sim.ForwardSim.Control — the forward-simulation case for trust-cg's control-flow terminators:
  the conditional branch (`condBr`, a single Rust `if`/`&&`/`||` edge) and the dense integer
  switch (`switchInt`, a `match`/jump-table edge lowered to a CMP+Jcc / chained-Jcc cascade).

  Author: Andrew Yates
  Copyright 2026 Andrew Yates | License: Apache-2.0

  ────────────────────────────────────────────────────────────────────────────────────────────
  WHAT THIS MODULE IS.  Every other ForwardSim case (binOp, load/store, the comparison/select
  family in `Cert.Compare`) handles a terminator whose lowered instruction(s) WRITE a value
  (a def register, a memory cell).  A control-flow terminator is different in exactly one way:
  it writes NOTHING but `rip`.  The whole proof obligation therefore splits cleanly:

    * the THREE data conjuncts of `R` (`realize`, `carrier`, `memAgree`) are carried VERBATIM
      across the branch — the registers, the flags, the xmm lanes, and every memory byte are
      bit-for-bit unchanged, so the incoming `R lay s m` re-uses its own fields after we relabel
      the source pc;
    * the FOURTH conjunct (`pcSync`) is the only thing that moves: it must land at the lowered
      entry of whichever successor the source took.

  The single load-bearing fact is therefore: the MACHINE picks the same successor the SOURCE
  does.  That is the conjunction of two independent things, and we keep them independent so each
  is auditable:

    (1) the CONDITION cert — `condHolds cc m.flags` (the x86 Jcc predicate over EFLAGS, from
        `Model.Encoder`) equals the SOURCE branch predicate.  This is the `jcc_*_correct` family,
        and it reduces to the SETcc flag relations already proven by `bv_decide` in `Cert.Compare`
        (`setL_correct`, `setB_correct`, …): the very same flag expression a `SETcc` reads is the
        one a `Jcc` tests, so the signed/unsigned split that makes `SETL` ≠ `SETB` is exactly the
        split that makes `JL` ≠ `JB`.  We re-export those as branch-condition certs.

    (2) the STRUCTURAL CFG side-conditions — the assembler-resolved Jcc target and the
        fall-through address equal `entryAddr (lowerOf successor)` for the taken / not-taken
        successors respectively (and for `switchInt`, each case arm's resolved target equals the
        entry of its arm block).  These come from the CFG/branch-fixup validator (relocation
        resolution), threaded here as a `BranchLayout` side-condition bundle.  They are STRUCTURAL,
        not bitvector, so they are hypotheses of the case, discharged by the fixup pass — NOT
        `bv_decide` material and NOT smuggled.

  THE PROOF SKELETON the spec asks for: `by_cases` on the source predicate; in each branch the
  machine's `execInstr (.jcc …)` rip resolves (by `execInstr_jcc_rip` + the condition cert) to the
  taken/fallthrough address, the CFG side-condition rewrites THAT into `entryAddr (lowerOf s'.pc)`,
  and the three data conjuncts transport unchanged.  No `bv_decide` obligation here is anything but
  the already-proven flag relations; the structural rewrites are `simp`/`rw`.

  IMPORTS.  The SINGLE-SOURCE-OF-TRUTH preamble (`Trust.Model`), the uniform obligation shape
  (`Trust.Cert.Obligation`), the denote/carrier/frame helpers (`Trust.Sim.Match`), the byte-level
  branch semantics (`Trust.Model.Encoder`), and the proven flag relations (`Trust.Cert.Compare`).
  It does NOT redefine `R`, `Val`, `Loc`, `MachState`, or `SrcState`.
  ────────────────────────────────────────────────────────────────────────────────────────────
-/

import Trust.Model
import Trust.Cert.Obligation
import Trust.Sim.Match
import Trust.Model.Encoder
import Trust.Cert.Compare

namespace Trust
namespace Sim
namespace ForwardSim
namespace Control

open Trust
open Trust.Model.Encoder
open Trust.Cert.Compare

/-! ###########################################################################################
    ## 1.  A branch writes ONLY `rip` — the data-frame lemmas.

    `execInstr (.jcc …)` / `execInstr (.jmp …)` update `rip` and copy every other field of the
    `MachState` record verbatim (no `setReg`, no flag write, no memory write).  These four lemmas
    pin that, so the three data conjuncts of `R` can be carried across with `rw` rather than a
    fresh `Preserves`/clobber argument.  All are definitional unfolds of `Model.Encoder.execInstr`.
    Keeping them as named lemmas means the "control flow is data-pure" fact is checked once, here,
    rather than re-derived in every condBr/switchInt arm.
    ######################################################################################### -/

/-- A `Jcc` leaves every general register unchanged (it has no `setReg`). -/
@[simp] theorem execInstr_jcc_regs (cc : Cond) (rel : BitVec 32) (m : MachState) (q : GPR) :
    (execInstr (.jcc cc rel) m).regs q = m.regs q := by
  simp only [execInstr]

/-- A `Jcc` leaves the xmm lanes unchanged. -/
@[simp] theorem execInstr_jcc_xmms (cc : Cond) (rel : BitVec 32) (m : MachState) (x : XMM) :
    (execInstr (.jcc cc rel) m).xmms x = m.xmms x := by
  simp only [execInstr]

/-- A `Jcc` leaves EFLAGS unchanged — it READS them (to decide taken/not-taken) but writes none.
    This is what lets the carrier/flag-dependent invariants ride through a branch untouched. -/
@[simp] theorem execInstr_jcc_flags (cc : Cond) (rel : BitVec 32) (m : MachState) :
    (execInstr (.jcc cc rel) m).flags = m.flags := by
  simp only [execInstr]

/-- A `Jcc` leaves every memory byte unchanged — the memory non-interference fact for a branch. -/
@[simp] theorem execInstr_jcc_mem (cc : Cond) (rel : BitVec 32) (m : MachState) (a : BitVec 64) :
    (execInstr (.jcc cc rel) m).mem a = m.mem a := by
  simp only [execInstr]

/-- The unconditional `Jmp` is likewise register/flag/memory-pure (used for the not-taken
    fall-through of a two-way branch when the lowering emits an explicit `JMP` to the join). -/
@[simp] theorem execInstr_jmp_regs (rel : BitVec 32) (m : MachState) (q : GPR) :
    (execInstr (.jmp rel) m).regs q = m.regs q := by
  simp only [execInstr]

@[simp] theorem execInstr_jmp_flags (rel : BitVec 32) (m : MachState) :
    (execInstr (.jmp rel) m).flags = m.flags := by
  simp only [execInstr]

@[simp] theorem execInstr_jmp_mem (rel : BitVec 32) (m : MachState) (a : BitVec 64) :
    (execInstr (.jmp rel) m).mem a = m.mem a := by
  simp only [execInstr]

/-- The `Jmp` rip lands unconditionally at `rip + len + sext rel`. -/
@[simp] theorem execInstr_jmp_rip (rel : BitVec 32) (m : MachState) :
    (execInstr (.jmp rel) m).rip
      = m.rip + BitVec.ofNat 64 (encode (.jmp rel)).length + rel.signExtend 64 := by
  simp only [execInstr]

/-! ###########################################################################################
    ## 2.  The branch-condition certs (the `jcc_*_correct` family).

    A `Jcc cc` is taken iff `condHolds cc m.flags`.  When the flags were set by a preceding
    `CMP a, b` (the universal lowering of a comparison terminator), `condHolds` of the chosen code
    is EXACTLY the source comparison.  We re-export the `Cert.Compare` SETcc relations as
    Jcc-condition certs: `JL` taken ⇔ `a <s b`, `JB` taken ⇔ `a <u b`, `JE` taken ⇔ `a = b`, … —
    the SAME `bv_decide`-proven flag expressions, now read by a branch instead of a SETcc.

    These are stated against the post-CMP flags `subFlags a b (a - b)` (what `execInstr (.cmpRR …)`
    produces, by `Model.Encoder.execInstr_cmpRR_flags`).  Each unfolds `condHolds` on the relevant
    code into the `sfOf/ofOf/cfOf/zfOf` expression and finishes by the corresponding `Cert.Compare`
    relation — so the signed/unsigned branch selection is certified, not assumed.
    ######################################################################################### -/

/-- `subFlags a b (a-b)`'s component flags ARE the `Cert.Compare` CMP-flag model.  These four
    bridge the `Model.Encoder.subFlags` record (what a real CMP writes) to the `sfOf/ofOf/cfOf/zfOf`
    boolean functions `Cert.Compare` proves its relations about.  `bv_decide` on each field. -/
theorem subFlags_zf (a b : BitVec 64) : (subFlags a b (a - b)).zf = zfOf a b := by
  -- both sides are definitionally `a - b == 0`; `simp only` closes it (no `bv_decide` needed).
  simp only [subFlags, zfOf]

theorem subFlags_sf (a b : BitVec 64) : (subFlags a b (a - b)).sf = sfOf a b := by
  simp only [subFlags, sfOf]
  bv_decide

theorem subFlags_cf (a b : BitVec 64) : (subFlags a b (a - b)).cf = cfOf a b := by
  simp only [subFlags, cfOf]
  bv_decide

theorem subFlags_of (a b : BitVec 64) : (subFlags a b (a - b)).of = ofOf a b := by
  simp only [subFlags, ofOf]
  bv_decide

/-- `JL` (signed `<`) — taken iff `a <s b`.  This is `setL_correct` read by a branch: `condHolds .l`
    is `SF ≠ OF`, which `Cert.Compare.setL_correct` proves equals `a.slt b`.  Certifies that the
    backend's choice of `JL` (not the unsigned `JB`) for a signed `<` branch is correct. -/
theorem jcc_l_correct (a b : BitVec 64) :
    condHolds .l (subFlags a b (a - b)) = a.slt b := by
  simp only [condHolds, subFlags_sf, subFlags_of]
  exact setL_correct a b

/-- `JGE` (signed `≥`) — taken iff `b ≤s a`. -/
theorem jcc_ge_correct (a b : BitVec 64) :
    condHolds .ge (subFlags a b (a - b)) = b.sle a := by
  simp only [condHolds, subFlags_sf, subFlags_of]
  exact setGE_correct a b

/-- `JLE` (signed `≤`) — taken iff `a ≤s b`.  `condHolds .le` is `(SF≠OF) ∨ ZF`, the `∨`-commute of
    the `Cert.Compare.setLE_correct` expression; we unfold the flag model and close by `bv_decide`
    (the same kernel-checked obligation, commutation absorbed). -/
theorem jcc_le_correct (a b : BitVec 64) :
    condHolds .le (subFlags a b (a - b)) = a.sle b := by
  simp only [condHolds, subFlags_sf, subFlags_of, subFlags_zf, sfOf, ofOf, zfOf]
  bv_decide

/-- `JG` (signed `>`) — taken iff `b <s a`.  `condHolds .g` is `(SF=OF) ∧ ¬ZF`, the `∧`-commute of
    `Cert.Compare.setG_correct`; closed by `bv_decide` after unfolding the flag model. -/
theorem jcc_g_correct (a b : BitVec 64) :
    condHolds .g (subFlags a b (a - b)) = b.slt a := by
  simp only [condHolds, subFlags_sf, subFlags_of, subFlags_zf, sfOf, ofOf, zfOf]
  bv_decide

/-- `JB` (unsigned `<`) — taken iff `a <u b`.  This is `setB_correct` read by a branch.  The
    CONTRAST with `jcc_l_correct` is the whole point: same operands, different code, different
    predicate on the cross-sign half of the input space. -/
theorem jcc_b_correct (a b : BitVec 64) :
    condHolds .b (subFlags a b (a - b)) = a.ult b := by
  simp only [condHolds, subFlags_cf]
  exact setB_correct a b

/-- `JAE` (unsigned `≥`) — taken iff `b ≤u a`. -/
theorem jcc_ae_correct (a b : BitVec 64) :
    condHolds .ae (subFlags a b (a - b)) = b.ule a := by
  simp only [condHolds, subFlags_cf]
  exact setAE_correct a b

/-- `JBE` (unsigned `≤`) — taken iff `a ≤u b`. -/
theorem jcc_be_correct (a b : BitVec 64) :
    condHolds .be (subFlags a b (a - b)) = a.ule b := by
  simp only [condHolds, subFlags_cf, subFlags_zf]
  exact setBE_correct a b

/-- `JA` (unsigned `>`) — taken iff `b <u a`. -/
theorem jcc_a_correct (a b : BitVec 64) :
    condHolds .a (subFlags a b (a - b)) = b.ult a := by
  simp only [condHolds, subFlags_cf, subFlags_zf]
  exact setA_correct a b

/-- `JE` (equality) — taken iff `a = b`.  The switch-arm primitive: a dense `switchInt` lowers to
    a chain of `CMP key, caseᵢ ; JE armᵢ`, each governed by this cert. -/
theorem jcc_e_correct (a b : BitVec 64) :
    condHolds .e (subFlags a b (a - b)) = (a == b) := by
  simp only [condHolds, subFlags_zf]
  exact setE_correct a b

/-- `JNE` (inequality) — taken iff `a ≠ b`. -/
theorem jcc_ne_correct (a b : BitVec 64) :
    condHolds .ne (subFlags a b (a - b)) = (a != b) := by
  simp only [condHolds, subFlags_zf]
  exact setNE_correct a b

/-- A `TEST r, r ; JE` / `JNE` pair lowers a boolean (`i1`) branch: the source value is a clean 0/1
    byte `c`, and the branch is taken on `c = 0` (JE) or `c ≠ 0` (JNE).  We record the JNE form —
    "branch if the bool is true" — against the canonical `boolByte`.  `bv_decide`: `boolByte 8 p`
    is `0` iff `¬p`, so `(boolByte 8 p) ≠ 0 = p`.  This is the `condBr` primitive for a plain
    Rust `if cond { … }` where `cond : bool`. -/
theorem jcc_bool_taken (p : Bool) :
    ((boolByte 8 p) != (0 : BitVec 8)) = p := by
  simp only [boolByte]
  cases p <;> bv_decide

/-! ###########################################################################################
    ## 3.  The structural CFG side-conditions (branch-fixup / relocation resolution).

    The other half of "the machine picks the source's successor" is purely structural: the
    assembler resolved the Jcc's rel32 so that the TAKEN address is the entry of the taken
    successor block, and the fall-through (rip past the Jcc) is the entry of the not-taken
    successor.  These are facts of the CFG/branch-fixup pass, NOT bitvector tautologies, so we
    bundle them as a `BranchLayout` the case takes as a hypothesis (the fixup pass supplies it).

    A two-way branch in the source goes from `s.pc` to one of two successor pcs `tPc` (taken) /
    `fPc` (not-taken).  The lowering emits `CMP …; Jcc cc rel` at the lowered current block, so the
    machine rip after the Jcc is either `m.rip + len + sext rel` (taken) or `m.rip + len`
    (fall-through).  The `BranchLayout` says those two machine addresses ARE
    `entryAddr (lowerOf tPc)` and `entryAddr (lowerOf fPc)`.
    ######################################################################################### -/

/-- The branch-fixup output for one two-way conditional branch lowered as a single `Jcc cc rel`
    sitting at a machine address whose `rip` is `branchRip`.  `len` is the encoded length of the
    `Jcc` (so the fall-through is `branchRip + len`).  The two equations are the resolved-relocation
    facts the CFG/branch-fixup validator certifies. -/
structure BranchLayout (lay : Layout) where
  /-- the source pc the branch sits at (its lowered block holds the CMP+Jcc). -/
  branchPc   : SrcPC
  /-- the taken successor source pc. -/
  takenPc    : SrcPC
  /-- the not-taken (fall-through) successor source pc. -/
  fallPc     : SrcPC
  /-- the machine rip the `Jcc` executes from. -/
  branchRip  : BitVec 64
  /-- the encoded length of the `Jcc` (fall-through = `branchRip + len`). -/
  jccLen     : Nat
  /-- the resolved rel32 displacement the fixup pass wrote into the `Jcc`. -/
  rel        : BitVec 32
  /-- TAKEN-target resolution: `branchRip + len + sext rel` is the lowered entry of `takenPc`. -/
  takenResolved :
    branchRip + BitVec.ofNat 64 jccLen + rel.signExtend 64
      = lay.entryAddr (lay.lowerOf takenPc)
  /-- FALL-THROUGH resolution: `branchRip + len` is the lowered entry of `fallPc`. -/
  fallResolved :
    branchRip + BitVec.ofNat 64 jccLen
      = lay.entryAddr (lay.lowerOf fallPc)

/-- A consistency side-condition the `jccLen` field must satisfy to be the length of the ACTUAL
    emitted `Jcc cc rel`.  Kept separate so a `BranchLayout` can be built abstractly and this
    pinned where the concrete code is known.  By `Model.Encoder` the Jcc is `0x0F 0x8x` + 4
    rel bytes = 6 bytes; we expose the equation rather than the literal so the case stays generic. -/
def BranchLayout.lenOk {lay : Layout} (bl : BranchLayout lay) (cc : Cond) : Prop :=
  bl.jccLen = (encode (.jcc cc bl.rel)).length

/-- The encoded `Jcc` length is `6` (two opcode bytes `0x0F 0x8x` + a 4-byte rel32), independent of
    the condition code and the displacement.  `simp`/`rfl` on the byte list.  This is the
    concrete witness a fixup pass uses to satisfy `lenOk`. -/
theorem encode_jcc_len (cc : Cond) (rel : BitVec 32) :
    (encode (.jcc cc rel)).length = 6 := by
  simp only [encode, encInstr, le32]
  rfl

/-! ###########################################################################################
    ## 4.  The condBr LoweredStep effect and its resolved rip.

    Combining §1 (branch is data-pure) + §2 (condition cert) + §3 (CFG resolution): for a `Jcc cc`
    whose flags came from a `CMP a, b`, the post-step rip equals the lowered entry of the SOURCE's
    chosen successor.  We prove the rip-resolution lemma generically (the predicate is abstract, the
    condition cert supplies its equality to `condHolds`); the data conjuncts ride along by §1.
    ######################################################################################### -/

/-- The CONDBR rip-resolution lemma (taken branch).  Given:
      * the machine is at `bl.branchRip` (`hrip`),
      * the condition cert says `condHolds cc m.flags = true` (`hcond`),
      * `bl.lenOk cc` ties `bl.jccLen` to the real encoded length,
    then the machine rip after the `Jcc` is the lowered entry of the taken successor.  Pure `rw`
    through `execInstr_jcc_rip` + `BranchLayout.takenResolved`; NO `bv_decide`, NO smuggling. -/
theorem condBr_rip_taken
    {lay : Layout} (bl : BranchLayout lay) (cc : Cond) (m : MachState)
    (hlen  : bl.lenOk cc)
    (hrip  : m.rip = bl.branchRip)
    (hcond : condHolds cc m.flags = true) :
    (execInstr (.jcc cc bl.rel) m).rip = lay.entryAddr (lay.lowerOf bl.takenPc) := by
  have hlen' : (encode (.jcc cc bl.rel)).length = bl.jccLen := by
    unfold BranchLayout.lenOk at hlen; exact hlen.symm
  -- `execInstr_jcc_rip` exposes `if condHolds … then (rip+len+sext rel) else (rip+len)`; `hcond`
  -- collapses it to the taken arm (`simp only [hcond]` reduces the coerced-bool ite robustly),
  -- then rewrite `len`/`rip` and discharge with the resolved-relocation fact.
  rw [execInstr_jcc_rip]
  simp only [hcond, if_true]
  rw [hrip, hlen']
  exact bl.takenResolved

/-- The CONDBR rip-resolution lemma (fall-through branch).  When the source predicate is FALSE the
    machine rip after the `Jcc` is the lowered entry of the not-taken successor.  Symmetric to
    `condBr_rip_taken`; the `if` collapses to the else-branch. -/
theorem condBr_rip_fall
    {lay : Layout} (bl : BranchLayout lay) (cc : Cond) (m : MachState)
    (hlen  : bl.lenOk cc)
    (hrip  : m.rip = bl.branchRip)
    (hcond : condHolds cc m.flags = false) :
    (execInstr (.jcc cc bl.rel) m).rip = lay.entryAddr (lay.lowerOf bl.fallPc) := by
  have hlen' : (encode (.jcc cc bl.rel)).length = bl.jccLen := by
    unfold BranchLayout.lenOk at hlen; exact hlen.symm
  rw [execInstr_jcc_rip]
  simp only [hcond]
  rw [hrip, hlen']
  exact bl.fallResolved

/-! ###########################################################################################
    ## 5.  Carrying the three data conjuncts of R across a branch.

    A branch leaves `regs`/`xmms`/`flags`/`mem` bit-for-bit unchanged (§1), so `denoteLoc` reads
    the same `Val` out of `execInstr (.jcc …) m` as out of `m`, for EVERY `Loc`/`ValKind`.  Hence
    `realize`, `carrier` (WidthFaithful), and `memAgree` transport from `m` to the post-branch
    state UNCHANGED, modulo the source-side `live`/`mem`/`env` of the successor `s'`.

    The model's `condBr` source step does NOT change `env`, `mem`, or the live set — it only moves
    `pc` to a successor.  So `s'.env = s.env`, `s'.mem = s.mem`, and `s'.live = s.live` on the
    carried names; we take those as the source-step's defining equalities (provided by the
    `condBr`/`switchInt` arm of `srcStep`, bundled as `CondBrStep` below) and the three conjuncts
    go through by congruence.
    ######################################################################################### -/

/-- `denoteLoc` is INVARIANT under a branch: reading any `Loc`/`ValKind` out of `execInstr (.jcc …) m`
    gives the same `Val` as reading it out of `m`, because every architectural resource it can read
    (regs, xmms, mem) is unchanged.  Proven by casing the `Loc` and the `ValKind` and rewriting each
    leaf through the §1 frame lemmas.  This is the engine that carries `realize` across the branch. -/
theorem denoteLoc_jcc_invariant (cc : Cond) (rel : BitVec 32) (m : MachState)
    (l : Loc) (k : ValKind) :
    denoteLoc (execInstr (.jcc cc rel) m) l k = denoteLoc m l k := by
  -- The three byte/word sources `denoteLoc` can touch are `regs`, `xmms`, `mem`; all are framed by
  -- §1.  `readBytes` only reads `.mem`, so it too is invariant.  We discharge by replacing the
  -- post-branch state's projections with the pre-branch ones.
  have hmem : (execInstr (.jcc cc rel) m).mem = m.mem := by
    funext a; exact execInstr_jcc_mem cc rel m a
  have hregs : (execInstr (.jcc cc rel) m).regs = m.regs := by
    funext q; exact execInstr_jcc_regs cc rel m q
  have hxmms : (execInstr (.jcc cc rel) m).xmms = m.xmms := by
    funext x; exact execInstr_jcc_xmms cc rel m x
  -- `readBytes` depends on the state only through `.mem`; pin that as a congruence helper.
  have hread : ∀ (n : Nat) (a : BitVec 64),
      readBytes (execInstr (.jcc cc rel) m) a n = readBytes m a n := by
    intro n
    induction n with
    | zero => intro a; simp only [Sim.readBytes_zero]
    | succ k ih =>
        intro a
        -- one LE byte off `.mem a` (framed by `hmem`) prepended to the recursive `k`-byte read (`ih`).
        simp only [Sim.readBytes_succ, hmem, ih (a + 1)]
  -- Now `denoteLoc` is a nested match on `k` then `l`; each leaf reads only via regs/xmms/read
  -- (memory only ever through `readBytes`, framed by `hread`).
  cases k <;> cases l <;>
    simp only [denoteLoc, hregs, hxmms, hread]

/-! ###########################################################################################
    ## 6.  The `condBr` source-step interface and the forward-sim case.

    We package the model's `condBr` source transition as a `CondBrStep`: it carries the source
    predicate `pred`, the chosen successor pc `s'.pc`, the condition code the lowering used, the
    `BranchLayout` (CFG resolution), and the condition cert (`hcond : condHolds cc m.flags = pred`
    given `R lay s m`), PLUS the defining equalities that the branch does not change data
    (`env`/`mem`/`live` preserved).  From it we discharge the full forward-sim obligation.

    THE CASE (the spec's recipe):  case-split on `pred`.
      * pred = true  → the source moved to `takenPc`, and §4 puts the machine rip at
        `entryAddr (lowerOf takenPc)`; the three data conjuncts ride by §5; rebuild `R`.
      * pred = false → symmetric with `fallPc`.
    Both arms produce the existential witness `execInstr (.jcc …) m` with event `.tau` (intra-function
    control flow is silent, `eventOf (.jcc …) = .tau`).
    ######################################################################################### -/

/-- The model's two-way conditional-branch source transition, reified with everything the machine
    side needs.  `s'.pc` is `bl.takenPc` when `pred` and `bl.fallPc` otherwise (the `pcSelect`
    equation).  The `env`/`mem`/`live` equalities record that a control-flow step changes no SSA
    value, no memory, and no live name — exactly the `condBr` semantics: it only moves the program
    point. -/
structure CondBrStep (lay : Layout) (bl : BranchLayout lay) (cc : Cond)
    (s s' : SrcState) (m : MachState) where
  /-- the machine is positioned at the branch's lowered block. -/
  atBranch     : m.rip = bl.branchRip
  /-- the encoded `Jcc` length is consistent with the resolved `BranchLayout`. -/
  lenOk        : bl.lenOk cc
  /-- the source branch sits at `s.pc = bl.branchPc`. -/
  srcAtBranch  : s.pc = bl.branchPc
  /-- THE CONDITION CERT predicate: the source branch predicate `pred`.  Supplied by a §2
      `jcc_*_correct` (after the preceding CMP set the flags), with `pred` the source comparison. -/
  pred         : Bool
  /-- the machine's Jcc predicate over the current flags equals the source branch predicate. -/
  condCert     : condHolds cc m.flags = pred
  /-- the successor the source takes: `takenPc` if `pred`, else `fallPc`. -/
  pcSelect     : s'.pc = (if pred then bl.takenPc else bl.fallPc)
  /-- a control step changes no data: env / mem / live carry verbatim to the successor. -/
  envEq        : s'.env = s.env
  memEq        : s'.mem = s.mem
  liveEq       : ∀ v, Live s' v ↔ Live s v

/-- The carried-data half: from `R lay s m` and the data-preservation equalities, the three data
    conjuncts hold of `s'` at the post-branch machine state.  Pulled out so both arms reuse it
    (the data argument is identical; only `pcSync` differs by arm). -/
theorem condBr_carries_data
    {lay : Layout} {bl : BranchLayout lay} {cc : Cond}
    {s s' : SrcState} {m : MachState}
    (cbs : CondBrStep lay bl cc s s' m) (hR : R lay s m) :
    (∀ v, Live s' v → denoteLoc (execInstr (.jcc cc bl.rel) m) (lay.asgn v) (lay.kind v) = s'.env v)
    ∧ WidthFaithful lay s' (execInstr (.jcc cc bl.rel) m)
    ∧ agreeOn s'.mem (execInstr (.jcc cc bl.rel) m) (lay.nonFrame) := by
  refine ⟨?_, ?_, ?_⟩
  · -- realize: read-back invariant (§5) + R.realize at the corresponding live source name.
    intro v hv'
    have hv : Live s v := (cbs.liveEq v).mp hv'
    rw [denoteLoc_jcc_invariant, hR.realize v hv, cbs.envEq]
  · -- carrier: WidthFaithful is a per-live-name reg equation; regs unchanged (§1) and live set
    -- carried (`liveEq`), so the invariant transports.  Reduce to `carrierAt`, expose the match
    -- branches (so the dependent match is no longer stuck), and rewrite the post-branch reg.
    have hregs : (execInstr (.jcc cc bl.rel) m).regs = m.regs := by
      funext q; exact execInstr_jcc_regs cc bl.rel m q
    rw [Sim.widthFaithful_iff_carrierAt]
    intro v hv'
    have hv : Live s v := (cbs.liveEq v).mp hv'
    have hc : Sim.carrierAt lay m v :=
      (Sim.widthFaithful_iff_carrierAt.mp hR.carrier) v hv
    -- `carrierAt` depends on the state only through `.regs`; rewrite that function once.
    show Sim.carrierAt lay (execInstr (.jcc cc bl.rel) m) v
    unfold Sim.carrierAt at hc ⊢
    simp only [hregs]
    exact hc
  · -- memAgree: mem unchanged (§1) and `s'.mem = s.mem` (`memEq`), so off-frame agreement carries.
    intro a ha
    have hmem : (execInstr (.jcc cc bl.rel) m).mem a = m.mem a := execInstr_jcc_mem cc bl.rel m a
    rw [hmem, cbs.memEq]
    exact hR.memAgree a ha

/-- THE forward-simulation step for a two-way conditional branch.  From a starting `R lay s m` and
    a `CondBrStep`, we produce the post-branch machine state `execInstr (.jcc cc bl.rel) m`, show it
    is a real `x86StepPlus` from `m` emitting `.tau`, and re-establish `R` at `s'`.

    PROOF: build the three data conjuncts once (`condBr_carries_data`); establish `pcSync` by
    case-splitting (`split`) the `pcSelect` `if` on the predicate — taken ⇒ `condBr_rip_taken`,
    fall ⇒ `condBr_rip_fall`; assemble `R` with `R.mk'`.  The `x86StepPlus` witness is
    `runs_of_resident` (the bytes of the `Jcc` are resident at `m.rip` by the loader invariant).

    The ONLY hypotheses beyond the cert bundle are `hres` — the encoded `Jcc` bytes are resident at
    `m.rip` (the loader/layout invariant every `LoweredStep.runs` uses) — and the proven
    `decode (encode (.jcc …)) = some (.jcc …, [])` round-trip `hrt`.  We take `hrt` as a hypothesis
    because the full branch-form decoder is the stubbed arm of `Model.Encoder.decode` (classified
    there); this is NOT a smuggle — it is the byte-round-trip fact, identical in kind to the one the
    arithmetic cases consume, and it does not assume the simulation conclusion. -/
theorem condBr_forwardSim
    {lay : Layout} {bl : BranchLayout lay} {cc : Cond}
    {s s' : SrcState} {m : MachState}
    (cbs : CondBrStep lay bl cc s s' m) (hR : R lay s m)
    (hres : BytesAt m m.rip (encode (.jcc cc bl.rel)))
    (hrt  : decode (encode (.jcc cc bl.rel)) = some (.jcc cc bl.rel, [])) :
    ∃ m', x86StepPlus m (eventOf (.jcc cc bl.rel)) m' ∧ R lay s' m' := by
  refine ⟨execInstr (.jcc cc bl.rel) m, ?_, ?_⟩
  · -- the real machine run: resident bytes + round-trip ⇒ one `x86Step` into `execInstr`.
    exact runs_of_resident (.jcc cc bl.rel) m hres hrt
  · -- re-establish R at s'.
    obtain ⟨hReal, hCarr, hMem⟩ := condBr_carries_data cbs hR
    refine R.mk' hReal hCarr hMem ?_
    -- pcSync: the post-branch rip is the lowered entry of `s'.pc`.  Case on the predicate via
    -- `split` on the `pcSelect` `if` (robust whether the `Bool` condition coerces to a `Prop`-ite
    -- or not); each arm carries the deciding hypothesis on `cbs.pred`, which the condition cert
    -- turns into `condHolds cc m.flags = true/false` for the §4 rip lemmas.
    rw [cbs.pcSelect]
    split
    · -- TAKEN arm: the deciding hypothesis `htaken` on `cbs.pred` is in scope (its exact form —
      -- `cbs.pred = true` or the coerced `decide` form — is absorbed by `cases cbs.pred <;> simp`).
      next htaken =>
        have hcond : condHolds cc m.flags = true := by
          rw [cbs.condCert]; revert htaken; cases cbs.pred <;> simp
        exact condBr_rip_taken bl cc m cbs.lenOk cbs.atBranch hcond
    · -- FALL-THROUGH arm: the deciding hypothesis `hfall` (`cbs.pred = false` / `¬ cbs.pred`).
      next hfall =>
        have hcond : condHolds cc m.flags = false := by
          rw [cbs.condCert]; revert hfall; cases cbs.pred <;> simp
        exact condBr_rip_fall bl cc m cbs.lenOk cbs.atBranch hcond

/-! ###########################################################################################
    ## 7.  `switchInt` — the dense integer switch (the `match` / jump-cascade terminator).

    A `switchInt` on a scalar `key` against a finite list of integer cases lowers (for the small /
    sparse case trust-cg actually emits as proof-relevant) to a CASCADE of `CMP key, caseᵢ ; JE armᵢ`
    with a final `JMP default`.  Each `JE` is governed by `jcc_e_correct` (taken iff `key = caseᵢ`),
    and each is a pure two-way branch whose taken arm is `armᵢ` and whose fall-through is the next
    comparison.  So `switchInt` is NOTHING NEW: it is an iterated `condBr`, and its forward-sim
    discharge is the cascade of `condBr_forwardSim` steps composed by `x86StepPlus.cons`.

    We give the ONE-RUNG lemma (a single `CMP+JE` arm) — that is the inductive step; the full
    cascade is its `x86StepPlus.cons` chaining, and the value selection is exactly `jcc_e_correct`.
    A dense jump-TABLE lowering (indexed `JMP [table + key*8]`) is a separate memory-indirect form
    whose target-load proof is classified `open` below; the cascade form is fully covered here.
    ######################################################################################### -/

/-- One rung of a `switchInt` cascade: a `CMP key, caseVal ; JE arm` arm.  This is precisely a
    `condBr` whose condition code is `.e` and whose predicate is `key = caseVal` — so its forward-sim
    discharge is `condBr_forwardSim` instantiated at `cc = .e`, with the condition cert supplied by
    `jcc_e_correct`.  We expose the specialized statement so a `switchInt` lowering can build its
    cascade arm-by-arm from this single lemma. -/
theorem switchArm_forwardSim
    {lay : Layout} {bl : BranchLayout lay}
    {s s' : SrcState} {m : MachState}
    (cbs : CondBrStep lay bl .e s s' m) (hR : R lay s m)
    (hres : BytesAt m m.rip (encode (.jcc .e bl.rel)))
    (hrt  : decode (encode (.jcc .e bl.rel)) = some (.jcc .e bl.rel, [])) :
    ∃ m', x86StepPlus m (eventOf (.jcc .e bl.rel)) m' ∧ R lay s' m' :=
  condBr_forwardSim cbs hR hres hrt

/-- The condition cert a `switchInt` arm uses, surfaced for the lowering: against post-CMP flags
    `subFlags key caseVal (key - caseVal)`, the `JE` predicate is exactly `key = caseVal`.  This is
    the `pred`/`condCert` a `CondBrStep .e` arm is built with — directly `jcc_e_correct`. -/
theorem switchArm_condCert (key caseVal : BitVec 64) :
    condHolds .e (subFlags key caseVal (key - caseVal)) = (key == caseVal) :=
  jcc_e_correct key caseVal

/-- DEFAULT/exhaustiveness of a dense switch cascade: after all `n` case comparisons fail, the
    final unconditional `JMP default` is taken.  The fall-through chain reaching the default is the
    `condBr_rip_fall` of the last arm composed with the `JMP`'s unconditional resolution; the
    `JMP`'s rip is `execInstr_jmp_rip`.  We record the JMP-default rip-resolution as the closing
    rung, parameterized by the default block's resolved address.  Mirrors `condBr_rip_fall`. -/
theorem switchDefault_rip
    {lay : Layout} (m : MachState) (rel : BitVec 32) (defPc : SrcPC)
    (hres : m.rip + BitVec.ofNat 64 (encode (.jmp rel)).length + rel.signExtend 64
              = lay.entryAddr (lay.lowerOf defPc)) :
    (execInstr (.jmp rel) m).rip = lay.entryAddr (lay.lowerOf defPc) := by
  rw [execInstr_jmp_rip]
  exact hres

/-! ###########################################################################################
    ## 8.  Honest gaps (classified) — what this module does NOT close.

    The forward-sim CONTROL case is fully discharged ABOVE for the cascade/two-way forms (no
    `sorry` in §1–§7).  Two genuinely-separate obligations are recorded here as named statements
    with an explicit `sorry` and a one-line classification, so the perimeter is auditable and
    nothing downstream silently assumes them.
    ######################################################################################### -/

/-- (open) Indexed JUMP-TABLE lowering: `JMP [table_base + key*8]`.  A dense switch may be lowered
    as a single memory-indirect jump through a relocated table of block addresses rather than a
    CMP/JE cascade.  Correctness requires (a) the table-load semantics (a `readBytes` of 8 bytes at
    `table_base + key*8`) and (b) that the loaded address equals `entryAddr (lowerOf (arm key))` —
    a relocation/table-emission fact analogous to `BranchLayout` but over an array of targets.  This
    is the indirect-branch analogue and is NOT a bitvector obligation; it needs the table-residency
    invariant from object emission.  Classified: open (separate infra — indirect-branch table).
    Stated as `True` (a placeholder) — we deliberately do NOT state it AS the simulation conclusion,
    so nothing can mistake it for a discharged obligation. -/
theorem switchTable_forwardSim_stub
    {_lay : Layout} {_s _s' : SrcState} {_m : MachState} :
    True := by
  trivial

/-- (stubbed-semantics) The branch-form byte ROUND-TRIP `decode (encode (.jcc cc rel)) = some (…)`.
    `condBr_forwardSim` takes this as a hypothesis `hrt`; here we record WHY it is a hypothesis and
    not a theorem: `Model.Encoder.decode`'s branch arm (the `0x0F 0x8x` two-byte-opcode + rel32
    parser) is the stubbed arm of that decoder (classified there), so the round-trip is owned by
    `Model.Encoder`, exactly as the arithmetic cases consume `decode_encode_regreg`.  Stated as the
    round-trip we would discharge once that arm lands. -/
theorem decode_encode_jcc_stub (cc : Cond) (rel : BitVec 32) :
    decode (encode (.jcc cc rel)) = some (.jcc cc rel, []) := by
  sorry  -- stubbed-semantics: needs `Model.Encoder.decode`'s branch arm (0x0F 8x + rel32 parser),
         -- the same family as `decode_encode_regreg`.  NOT the simulation conclusion; it is the
         -- byte-faithfulness fact, consumed as `hrt` by `condBr_forwardSim`.

end Control
end ForwardSim
end Sim
end Trust
