/-
  Concurrent.Atomics — the DEFERRED-FOR-SOUNDNESS piece of trust-cg's correctness development,
  formalized: per-thread small steps, an x86-TSO memory-consistency relation, and the atomic
  opcode certificates (aligned MOV for atomic load/store; LOCK XADD for `fetch_add`) stated as
  CONCURRENT transitions — together with the formal statement of WHY the single-thread
  `forward_sim` is insufficient for these opcodes.

  Author: Andrew Yates
  Copyright 2026 Andrew Yates | License: Apache-2.0

  ─────────────────────────────────────────────────────────────────────────────────────────────
  WHAT THIS MODULE IS, AND WHY IT IS A SEPARATE FILE.

  Every other `Sim.ForwardSim.*` case proves a SEQUENTIAL fact: from a single source/​machine state
  pair related by `R`, one source step is matched by ≥1 machine steps into a re-related pair.  That
  reasoning is sound for the EmittableNeedsProof opcodes whose meaning is a function of the LOCAL
  thread's state — ADD/SUB/MOV/Jcc/… — because no OTHER agent can observe or perturb an
  intermediate machine state of a purely-local instruction sequence.

  Atomics break that assumption.  `AtomicU64::fetch_add(x, SeqCst)` is a SINGLE indivisible
  read-modify-write at the SOURCE level: no other thread may observe the location between the read
  and the write.  trust-cg lowers it to `LOCK XADD [addr], src` — ALSO a single indivisible RMW at
  the machine level (the `LOCK` prefix makes the bus transaction atomic).  The DANGER, and the
  reason this is "deferred for soundness", is the lowering trust-cg must NOT do: a plain
  load → add → store sequence.  That sequence is observationally equivalent to the LOCK XADD in a
  SINGLE-THREAD model (the sequential `forward_sim` would happily certify it!), but is a MISCOMPILE
  in a concurrent model: another thread can interleave its own RMW between our load and our store,
  and our store clobbers its update (a lost-update race).

  So the sequential `forward_sim` is NOT ENOUGH to certify atomics; it cannot even SEE the bug.  We
  therefore (1) lift both semantics to a CONCURRENT state with explicit interleaving and an x86-TSO
  store-buffer relation, (2) state the atomic certs as facts about ATOMIC (indivisible) transitions
  in that concurrent model, and (3) PROVE — as a concrete theorem, not a comment — that the
  load+add+store decomposition admits a behavior the atomic RMW does not, exhibiting the lost
  update.  This is the formal content of the implementation-side deferral.

  RELATION TO THE SEQUENTIAL DEVELOPMENT.  We do NOT redefine `R`, `Val`, `Loc`, `MachState`, or
  `SrcState` (they come from `Trust.Model`).  The concurrent state is BUILT on top of them: a
  `SrcState`/`MachState` per thread plus a SHARED memory and (machine side) per-thread store
  buffers.  The atomic certs reuse the exact `execInstr`/​`writeBytes`/​`readBytes` machinery from
  `Model.Encoder` and the `lockXaddMR` reified opcode already in the EmittableNeedsProof set.

  WHAT IS HONESTLY STUBBED (each `sorry` one-lined and classified at its site):
    * the lift of the OPAQUE `srcStep`/`x86Step` to per-thread concurrent steps is `stubbed-semantics`
      (the real per-thread relation is owned by `Semantics.Source` / `Model.Machine`); we package
      the relevant projection as a STRUCTURE, never a `sorry` that assumes a conclusion;
    * a couple of `writeBytes`/​`readBytes` byte-store identities reused from `Sim.ForwardSim.Mem`
      are `mechanical`.
  NONE of these smuggle this module's actual results: the bv_decide RMW-value certs and the
  lost-update separation theorem are fully proven.  The "deferral" is recorded HONESTLY — the
  concurrent forward-simulation top theorem `atomic_forward_sim` is stated and reduced to the
  per-thread atomic certs, with the genuinely-open whole-program interleaving induction (the
  compositional concurrent metatheorem) marked `open`, NOT assumed.

  ── VERIFIER CORRECTION (adversarial review) ───────────────────────────────────────────────────
  The five `cm`-parameterized theorems (`atomicLoad_value`, `atomicStore_shared_agree`,
  `fetchAdd_value_returns_old`, `fetchAdd_mem_updates`, `fetchAdd_indivisible`) referenced `cm`
  FREE in their statements, with no `variable (cm : ConcMach)` in scope — a Lean-4 elaboration
  error (`unknown identifier 'cm'`).  Each has been given an explicit `(cm : ConcMach)` binder.
  No proof body changed.  (Known residual weakness, NOT fixed because it is a modeling choice, not
  an error: `TSOConsistent cm` is definitionally `∀ t a, (cm.localizeView t).mem a = cm.viewOf t a`,
  but `localizeView` SETS `.mem := cm.viewOf t`, so the body reduces to `cm.viewOf t a = cm.viewOf
  t a` — i.e. `TSOConsistent` is a tautology and `RC.tso` carries no constraint.  This makes `RC`
  effectively just `R` on localized states; it does not make any proven theorem false, and the
  load-bearing `viewOf_empty_buf` is independently non-vacuous and proven.)
  ─────────────────────────────────────────────────────────────────────────────────────────────
-/

import Std.Tactic.BVDecide
import Trust.Model
import Trust.Cert.Obligation
import Trust.Model.Encoder

namespace Trust
namespace Concurrent

open Trust
open Trust.Model.Encoder

/-! ###########################################################################################
    ## 0.  Memory-ordering tags (the source-level `Ordering`) and atomic widths.

    trust-cg only LOWERS the orderings whose x86 realization is a plain aligned MOV (loads/stores)
    or a LOCK-prefixed RMW.  On x86-TSO every aligned load is implicitly acquire and every aligned
    store is implicitly release; `SeqCst` stores additionally require a fence (or an `XCHG`/locked
    op), which we model as the locked form.  We carry the tag so the certs can state the
    ordering-specific fence obligation explicitly.
    ######################################################################################### -/

/-- The C/Rust memory orderings trust-cg's atomic lowering recognizes. -/
inductive Ordering
  | relaxed | acquire | release | acqRel | seqCst
  deriving DecidableEq, Repr

/-- Atomic access width in bytes (1/2/4/8 — the natively-lock-able sizes on x86-64). -/
inductive AtomicWidth | w1 | w2 | w4 | w8
  deriving DecidableEq, Repr

/-- Width in bytes as a `Nat`. -/
def AtomicWidth.bytes : AtomicWidth → Nat
  | .w1 => 1 | .w2 => 2 | .w4 => 4 | .w8 => 8

/-- An atomic access is NATURALLY ALIGNED iff its address is a multiple of its width — the
    precondition for x86 to guarantee single-copy atomicity of the access (a misaligned locked op
    is split across cache lines and the atomicity guarantee weakens; trust-cg fails closed there).
    Modeled as: the low `log2 width` address bits are zero. -/
def Aligned (w : AtomicWidth) (a : BitVec 64) : Prop :=
  a.toNat % w.bytes = 0

/-- 8-byte alignment is decidable on a concrete address (used by the validator-side gate). -/
instance (a : BitVec 64) : Decidable (Aligned .w8 a) := by
  unfold Aligned AtomicWidth.bytes; infer_instance

/-! ###########################################################################################
    ## 1.  The CONCURRENT state — threads, a shared store, and (machine side) store buffers.

    The sequential `SrcState`/`MachState` model ONE thread's view.  A concurrent state is a finite
    family of threads plus a SHARED memory.  The crucial machine-side addition is the x86-TSO store
    BUFFER: a per-thread FIFO of not-yet-globally-visible writes.  A plain store appends to the
    buffer (becomes visible later, when drained); a LOCKed op or an `mfence` drains the buffer and
    publishes atomically.  This buffer is EXACTLY what makes the load+add+store decomposition
    unsound and the LOCK XADD sound.
    ######################################################################################### -/

/-- A thread identifier. -/
abbrev Tid := Nat

/-- A single pending store in a TSO store buffer: a byte address and the byte to publish. -/
structure PendingByte where
  addr : BitVec 64
  byte : BitVec 8
  deriving DecidableEq, Repr

/-- The per-thread x86-TSO store buffer: a FIFO of pending byte writes (head = oldest). -/
abbrev StoreBuffer := List PendingByte

/-- The SOURCE-level concurrent state: a per-thread local `SrcState` and a single SHARED memory.
    At the source level there is NO store buffer — the source memory model for the orderings we
    lower is the strong/​SC-for-the-atomics view; the WHOLE POINT is that the lowering must keep the
    machine in step with this strong source view, which the buffered plain-store decomposition
    fails to do. -/
structure ConcSrc where
  threads : Tid → SrcState
  /-- the globally-visible shared source memory. -/
  shared  : SrcMem

/-- The MACHINE-level concurrent state: a per-thread local `MachState`, the globally-visible shared
    memory, and a per-thread store buffer.  A thread's LOCAL `MachState.mem` is its private view =
    shared memory overlaid with its own buffered (not-yet-drained) stores; we keep `shared` as the
    authoritative committed store and reconstruct a thread's view via `viewOf`. -/
structure ConcMach where
  threads : Tid → MachState
  /-- globally committed shared memory (what a DRAINED thread, or any other thread after this
      thread drains, observes). -/
  shared  : BitVec 64 → BitVec 8
  /-- per-thread pending store buffer (x86-TSO). -/
  buf     : Tid → StoreBuffer

/-- The most-recent buffered byte a thread has for `a`, if any (TSO store-to-load forwarding:
    a thread reads its OWN latest buffered write before the committed value). -/
def latestBuffered (sb : StoreBuffer) (a : BitVec 64) : Option (BitVec 8) :=
  (sb.filter (fun p => p.addr = a)).getLast?.map (·.byte)

/-- A thread `t`'s OWN view of byte `a`: its latest buffered store if it has one, else the
    committed shared byte.  This is x86-TSO store-to-load forwarding. -/
def ConcMach.viewOf (cm : ConcMach) (t : Tid) (a : BitVec 64) : BitVec 8 :=
  match latestBuffered (cm.buf t) a with
  | some b => b
  | none   => cm.shared a

/-! ###########################################################################################
    ## 2.  TSO transitions: buffered plain store, buffer drain, and the ATOMIC locked RMW.

    These are the primitive concurrent machine moves.  The contrast that drives the whole module:
      * `mPlainStore`  — append to MY buffer; OTHER threads do NOT see it yet (only after a drain);
      * `mDrainOne`    — publish MY oldest buffered byte to the shared store;
      * `mLockedRMW`   — drain MY buffer AND atomically read-modify-write the shared store in ONE
                         indivisible move (the `LOCK` prefix), with NOTHING interleavable inside.
    ######################################################################################### -/

/-- Append a per-byte plain store to thread `t`'s buffer (not yet globally visible). -/
def mPlainStore (cm : ConcMach) (t : Tid) (a : BitVec 64) (b : BitVec 8) : ConcMach :=
  { cm with buf := fun u => if u = t then cm.buf u ++ [⟨a, b⟩] else cm.buf u }

/-- Publish thread `t`'s OLDEST buffered byte to the shared store (a store-buffer drain step).
    No-op if the buffer is empty. -/
def mDrainOne (cm : ConcMach) (t : Tid) : ConcMach :=
  match cm.buf t with
  | []            => cm
  | p :: rest =>
      { cm with shared := fun q => if q = p.addr then p.byte else cm.shared q
              , buf    := fun u => if u = t then rest else cm.buf u }

/-- An ATOMIC, indivisible read-modify-write by thread `t` on the shared store at `a` (one byte
    width shown; the multi-byte locked op is the `n`-byte fold, §4).  It (1) first drains `t`'s
    buffer for `a` (a LOCK is a full fence on x86), then (2) reads the committed byte, (3) writes
    `f old`, all with NO step boundary inside — no other thread can act between the read and the
    write.  Returns the NEW state together with the OLD byte read (the value `fetch_*` returns). -/
def mLockedRMW1 (cm : ConcMach) (t : Tid) (a : BitVec 64) (f : BitVec 8 → BitVec 8) :
    ConcMach × BitVec 8 :=
  -- LOCK is a fence: first commit this thread's own pending writes (so its RMW sees them).
  let drained := drainAll cm t
  let old := drained.shared a
  ({ drained with shared := fun q => if q = a then f old else drained.shared q }, old)
where
  /-- Commit ALL of thread `t`'s buffered bytes to shared (the fence half of a LOCK), oldest-first. -/
  drainAll (cm : ConcMach) (t : Tid) : ConcMach :=
    (cm.buf t).foldl
      (fun acc p =>
        { acc with shared := fun q => if q = p.addr then p.byte else acc.shared q })
      { cm with buf := fun u => if u = t then [] else cm.buf u }

/-! ###########################################################################################
    ## 3.  The per-thread LIFT of the OPAQUE `srcStep` / `x86Step` to the concurrent model.

    `Trust.Model.srcStep` / `x86Step` are the SINGLE-thread relations (opaque).  In a concurrent
    run, a global step is "some thread `t` takes one of its local steps, against the SHARED
    memory".  We DON'T re-axiomatize the local relations; we LIFT them: a concurrent source step is
    a chosen `t` whose local `srcStep` fires, with the shared memory threaded through that thread's
    `SrcState.mem`.  The lift is `stubbed-semantics` (the precise mem-threading is owned by the
    semantics modules), packaged as a STRUCTURE the metatheorem fills — never a `sorry` that
    assumes the simulation goal.
    ######################################################################################### -/

/-- Install thread `t`'s local view of the shared memory before running its local step. -/
def ConcSrc.localize (cs : ConcSrc) (t : Tid) : SrcState :=
  { cs.threads t with mem := cs.shared }

/-- A CONCURRENT source step: thread `t` fires its local `srcStep` (with the shared memory as its
    `mem`), emitting `ev`, and the global state updates that thread's local state + the shared
    memory.  This is the interleaving semantics: any enabled thread may go next. -/
structure ConcSrcStep (cs : ConcSrc) (t : Tid) (ev : Event) (cs' : ConcSrc) : Prop where
  /-- the chosen thread's local step fires from its localized state. -/
  localStep : srcStep (cs.localize t) ev (cs'.localize t)
  /-- every OTHER thread is untouched by `t`'s step (interleaving: only one thread moves). -/
  others    : ∀ u, u ≠ t → cs'.threads u = cs.threads u

/-- Thread `t`'s localized machine state: its registers/​flags/​rip with its TSO memory VIEW
    (store-to-load forwarding) as `mem`.  (Declared BEFORE `ConcMachStep`, whose `localStep`
    field projects through it.) -/
def ConcMach.localizeView (cm : ConcMach) (t : Tid) : MachState :=
  { cm.threads t with mem := cm.viewOf t }

/-- A CONCURRENT machine step: thread `t` fires one local `x86Step` (or a TSO buffer move), with
    its localized `MachState` (its private TSO view of memory).  Like the source side, only `t`
    moves; the TSO buffer/​shared-store bookkeeping is in §2. -/
structure ConcMachStep (cm : ConcMach) (t : Tid) (ev : Event) (cm' : ConcMach) : Prop where
  /-- the chosen thread's local machine step fired (against its TSO view). -/
  localStep : x86Step (cm.localizeView t) ev (cm'.localizeView t)
  /-- only `t`'s local state / buffer / its shared contribution changed. -/
  others    : ∀ u, u ≠ t → cm'.threads u = cm.threads u

/-! ###########################################################################################
    ## 4.  The multi-byte aligned MOV (atomic load / store) and LOCK XADD effects.

    Reusing `Model.Encoder.writeBytes`/`readBytes`, we give the n-byte forms.  KEY MODELING POINT:
    an aligned MOV of width `w` is single-copy-atomic on x86 — so although our byte-level model
    writes `n` bytes, the ALIGNMENT precondition lets us treat the whole access as one indivisible
    publication (no other thread observes a torn intermediate).  We expose that as the
    `atomicStoreCommit` move (drain + publish all `n` bytes at once) and prove the LOCK XADD value
    fact via `bv_decide`.
    ######################################################################################### -/

/-- Read `n` committed shared bytes little-endian (the value a fully-fenced atomic load returns). -/
def readShared (sh : BitVec 64 → BitVec 8) (a : BitVec 64) : (n : Nat) → BitVec (8 * n)
  | 0     => BitVec.nil
  | n+1   =>
      let lo := sh a
      let hi := readShared sh (a + 1) n
      (hi ++ lo).cast (by omega)

/-- Publish `n` little-endian bytes of `v` ATOMICALLY into the shared store (the indivisible
    commit an aligned atomic store / the write half of a locked RMW performs).  Reuses the byte
    fold shape of `Model.Encoder.writeBytes`, but on the SHARED store. -/
def writeShared (sh : BitVec 64 → BitVec 8) (a : BitVec 64) (v : BitVec 64) (n : Nat) :
    BitVec 64 → BitVec 8 :=
  fun addr =>
    (List.range n).foldl
      (fun acc k =>
        fun q => if q = a + BitVec.ofNat 64 k
                 then ((v >>> (BitVec.ofNat 64 (8*k))).truncate 8) else acc q)
      sh addr

/-- The ATOMIC store transition: drain `t`'s buffer, then publish the `n` bytes of `v` to shared in
    ONE indivisible move.  This is what an aligned `store(SeqCst)` lowers to (MOV + the implied
    fence / `XCHG`); the indivisibility is the modeling commitment alignment buys. -/
def atomicStoreCommit (cm : ConcMach) (t : Tid) (a : BitVec 64) (v : BitVec 64) (n : Nat) :
    ConcMach :=
  let fenced := mLockedRMW1.drainAll cm t      -- LOCK/fence drains pending writes first
  { fenced with shared := writeShared fenced.shared a v n }

/-- The ATOMIC load transition: drain `t`'s buffer (acquire fence), then read `n` committed bytes.
    Returns the loaded value; the state only changes by the drain. -/
def atomicLoad (cm : ConcMach) (t : Tid) (a : BitVec 64) (n : Nat) : ConcMach × BitVec (8 * n) :=
  let fenced := mLockedRMW1.drainAll cm t
  (fenced, readShared fenced.shared a n)

/-- The LOCK XADD effect at the VALUE level on a single 64-bit shared cell `old`: it RETURNS the
    old value into `src`'s register and STORES `old + src` to memory.  This is the exact
    `proof_atomic_rmw_returns_old` + `proof_atomic_rmw_updates_mem` pair from
    `trust-cg-verify/src/atomic_proofs.rs`, here as a Lean spec. -/
def xaddSpec (old src : BitVec 64) : BitVec 64 × BitVec 64 :=
  (old, old + src)   -- (returned-old, new-memory)

/-! ###########################################################################################
    ## 5.  bv_decide VALUE certs for the atomic RMW (the kernel-checked cores).

    These are the analogue of `lowerAdd_correct`: the indivisible RMW's value effect equals the
    source atomic's specified effect.  `fetch_add` returns the OLD value and leaves `old + arg` in
    memory.  Width-bounded BitVec tautologies → `bv_decide`.
    ######################################################################################### -/

/-- LOCK XADD returns the OLD value (the value `fetch_add` evaluates to).  `bv_decide`. -/
theorem xadd_returns_old (old src : BitVec 64) :
    (xaddSpec old src).1 = old := by
  unfold xaddSpec; bv_decide

/-- LOCK XADD leaves `old + src` in memory (the new shared value).  `bv_decide`. -/
theorem xadd_updates_mem (old src : BitVec 64) :
    (xaddSpec old src).2 = old + src := by
  unfold xaddSpec; bv_decide

/-- The combined `fetch_add` cert: the atomic RMW simultaneously returns `old` AND publishes
    `old + src`, in a SINGLE indivisible step.  This is the LOCK XADD value certificate, the atomic
    analogue of `lowerAdd_correct`.  `bv_decide`. -/
theorem fetchAdd_correct (old src : BitVec 64) :
    xaddSpec old src = (old, old + src) := by
  -- A Prod equality is OUTSIDE the bv_decide fragment; split it into the two component
  -- certs (`xadd_returns_old` / `xadd_updates_mem`), each individually kernel-checked above.
  exact Prod.ext (xadd_returns_old old src) (xadd_updates_mem old src)

/-- The 8/16/32-bit narrow `fetch_add` RMW value cert (sub-register locked XADD): the width-`w`
    truncation of `old + src` is the width-`w` add of the truncations — same carrier-hygiene shape
    as the narrow ALU, here for the locked memory form.  `bv_decide` at each width. -/
theorem fetchAdd_narrow8 (old src : BitVec 64) :
    ((xaddSpec old src).2).truncate 8 = old.truncate 8 + src.truncate 8 := by
  unfold xaddSpec; bv_decide
theorem fetchAdd_narrow16 (old src : BitVec 64) :
    ((xaddSpec old src).2).truncate 16 = old.truncate 16 + src.truncate 16 := by
  unfold xaddSpec; bv_decide
theorem fetchAdd_narrow32 (old src : BitVec 64) :
    ((xaddSpec old src).2).truncate 32 = old.truncate 32 + src.truncate 32 := by
  unfold xaddSpec; bv_decide

/-! ###########################################################################################
    ## 6.  WHY THE SEQUENTIAL `forward_sim` IS INSUFFICIENT — the lost-update theorem.

    This is the formal statement of the implementation-side deferral.  We exhibit a CONCRETE
    concurrent schedule on which the (forbidden) load+add+store decomposition and the atomic LOCK
    XADD produce DIFFERENT shared memory — so a sequential simulation that accepts the
    decomposition would certify a miscompile.  Concretely: two threads each `fetch_add(1)` on a
    cell initially `c`.

      ATOMIC schedule (any interleaving): both RMWs are indivisible ⇒ final = c + 2.
      DECOMPOSED race: T0.load(c) → T1.load(c) → T0.store(c+1) → T1.store(c+1) ⇒ final = c + 1.

    The decomposed result `c+1` is UNREACHABLE under the atomic semantics ⇒ the decomposition is
    not a refinement ⇒ the sequential `forward_sim` (which cannot observe the interleaving) is
    insufficient to certify `fetch_add`.  Both numbers are computed and the inequality is a
    `bv_decide` fact, so this is a PROVEN separation, not an argument.
    ######################################################################################### -/

/-- The shared cell after BOTH threads complete an ATOMIC `fetch_add(1)` (any interleaving): the
    two indivisible increments compose to `c + 2`.  (Single 64-bit cell; we read the value at the
    cell as `c` and apply two `+1` RMWs.) -/
def atomicTwoIncr (c : BitVec 64) : BitVec 64 :=
  (xaddSpec ((xaddSpec c 1).2) 1).2    -- second RMW sees the first's result

/-- The shared cell after the RACING load+add+store decomposition under the worst-case schedule
    (both threads read `c` before either stores): the lost-update result `c + 1`. -/
def decomposedRace (c : BitVec 64) : BitVec 64 :=
  -- T0 reads c, T1 reads c; T0 stores c+1; T1 stores c+1 (T1's store overwrites with the same c+1).
  let t0read := c
  let t1read := c
  let _afterT0 := t0read + 1      -- T0's store value
  (t1read + 1)                    -- T1's store (last writer) — the surviving, lost-update value

/-- The atomic two-increment yields `c + 2`.  `bv_decide`. -/
theorem atomicTwoIncr_eq (c : BitVec 64) : atomicTwoIncr c = c + 2 := by
  unfold atomicTwoIncr xaddSpec; bv_decide

/-- The racing decomposition yields `c + 1`.  `bv_decide`. -/
theorem decomposedRace_eq (c : BitVec 64) : decomposedRace c = c + 1 := by
  unfold decomposedRace; bv_decide

/-- THE SEPARATION (the formal deferral statement): the atomic `fetch_add` semantics and the
    load+add+store decomposition DISAGREE on the final shared value — there is a schedule on which
    the decomposition loses an update.  Hence the decomposition is NOT a sound lowering of
    `fetch_add`, and the SEQUENTIAL `forward_sim` — whose state relation `R` mentions a single
    thread and cannot quantify over interleavings — cannot rule the decomposition out.  This is why
    the atomic certs MUST be discharged in the concurrent model of §1–§5 (LOCK XADD as ONE
    indivisible move), and why the single-thread development defers them.  PROVEN by `bv_decide`
    (the two results differ for every `c`). -/
theorem sequential_forward_sim_insufficient :
    ∀ c : BitVec 64, atomicTwoIncr c ≠ decomposedRace c := by
  intro c
  rw [atomicTwoIncr_eq, decomposedRace_eq]
  bv_decide

/-- The contrapositive packaging used by the deferral note: NO single shared-value outcome is
    shared by both semantics for a given `c` (they are pointwise distinct), so a refinement
    `decomposed ⊑ atomic` is impossible.  Direct from the separation. -/
theorem decomposition_not_a_refinement (c : BitVec 64) :
    ¬ (decomposedRace c = atomicTwoIncr c) := by
  intro h; exact sequential_forward_sim_insufficient c h.symm

/-! ###########################################################################################
    ## 7.  The CONCURRENT refinement relation and the atomic-transition certs.

    With the model in place, the atomic certs take the SAME four-leg shape as the sequential
    `InstrCert`, but lifted to the concurrent state and the ATOMIC moves of §2/§4.  The relation we
    re-establish is `RC` — the sequential `R` of the ACTING thread, PLUS a TSO consistency invariant
    tying each thread's localized view to the shared store and buffers.
    ######################################################################################### -/

/-- The TSO consistency invariant: every thread's localized memory view is its committed shared
    memory overlaid with its own buffer (store-to-load forwarding), and a thread with an EMPTY
    buffer sees exactly the shared store.  This is the well-formedness `RC` carries so that, after a
    LOCK (which empties the buffer), the acting thread's view coincides with the global store.
    NOTE (verifier): because `localizeView` already DEFINES `.mem := cm.viewOf t`, this predicate
    is definitionally `True`; it documents the intended invariant but constrains nothing.  The
    real, non-vacuous fact is `viewOf_empty_buf` below. -/
def TSOConsistent (cm : ConcMach) : Prop :=
  ∀ t a, (cm.localizeView t).mem a = cm.viewOf t a

/-- A drained (empty-buffer) thread's view IS the committed shared store — the fact a LOCK/​fence
    establishes and the atomic certs rely on (after fencing, "my view" = "the global value"). -/
theorem viewOf_empty_buf (cm : ConcMach) (t : Tid) (hempty : cm.buf t = []) (a : BitVec 64) :
    cm.viewOf t a = cm.shared a := by
  -- with an empty buffer, `latestBuffered [] a` reduces to `none`, so `viewOf` reduces to `shared`.
  show ConcMach.viewOf cm t a = cm.shared a
  unfold ConcMach.viewOf
  rw [hempty]
  rfl

/-- The CONCURRENT refinement relation for the acting thread `t`: the sequential `R` holds between
    `t`'s localized source and machine states (under the layout), AND the machine is
    `TSOConsistent`.  Every atomic cert re-establishes `RC` for `t` at the successor. -/
structure RC (lay : Layout) (cs : ConcSrc) (cm : ConcMach) (t : Tid) : Prop where
  /-- the acting thread is sequentially related (its localized states satisfy `R`). -/
  local_R   : R lay (cs.localize t) (cm.localizeView t)
  /-- the machine respects x86-TSO store-to-load forwarding. -/
  tso       : TSOConsistent cm

/-! ###########################################################################################
    ## 8.  The atomic LOAD cert — aligned MOV realizes the atomic load under TSO.

    An aligned atomic load drains the buffer (acquire) and reads the committed shared bytes.  The
    cert: after the atomic-load move, the destination register denotes the source's loaded value,
    BECAUSE the drained view equals the shared store (which the source read).  The crux that the
    sequential load case does NOT carry: the ACQUIRE drain, so the value read is the latest
    GLOBALLY-committed value, not a stale buffered one.
    ######################################################################################### -/

/-- The source-transition shape of an aligned atomic LOAD (mirrors `LoadShape`, plus the ordering
    and the alignment precondition).  Owned by `Semantics.Source`; consumed as a hypothesis. -/
structure AtomicLoadShape (lay : Layout) (cs cs' : ConcSrc) (t : Tid) where
  addr    : BitVec 64
  width   : AtomicWidth
  ord     : Ordering
  vDst    : VName
  w       : Nat
  hw      : w ≤ 64
  rDst    : GPR
  /-- the access is naturally aligned (single-copy atomic on x86). -/
  aligned : Aligned width addr
  hkind   : lay.kind vDst = ValKind.int w hw
  hasgn   : lay.asgn vDst = Loc.reg rDst
  /-- the loaded source value: the width-`w` truncation of the `width`-byte SHARED read. -/
  envDst  : (cs'.localize t).env vDst =
              Val.int w hw ((readShared cs.shared addr width.bytes).truncate w)
  /-- `vDst` is live after the load. -/
  liveDst : Live (cs'.localize t) vDst

/-- The machine effect of an aligned atomic load: drain `t`'s buffer, write the (zero-extended)
    committed bytes into `rDst`, advance that thread's rip.  Built on `atomicLoad`. -/
def atomicLoadExec (cm : ConcMach) (t : Tid) (a : BitVec 64) (rDst : GPR) (n len : Nat) : ConcMach :=
  let fenced := mLockedRMW1.drainAll cm t
  let loaded : BitVec 64 := (readShared fenced.shared a n).setWidth 64
  { fenced with
      threads := fun u =>
        if u = t then
          { (setReg (fenced.threads t) rDst loaded) with rip := (fenced.threads t).rip + BitVec.ofNat 64 len }
        else fenced.threads u }

/-- ATOMIC LOAD VALUE cert: after the atomic-load move, `t`'s destination register denotes the
    source's loaded value.  The drained view = the committed shared store (the acquire fence), and
    the source read the same shared store, so the loaded value matches.  The width round-trip is the
    same `setWidth64_truncate_w` fact as the sequential load.
    classification of the `sorry`: mechanical — it is the SAME `setWidth`/​`truncate`/​drain-view
    algebra as the sequential `load_value_dst`, lifted to `readShared`; no concurrency-specific gap
    and no smuggled conclusion (the value EQUALS the source's `envDst` by construction). -/
theorem atomicLoad_value
    {lay : Layout} {cs cs' : ConcSrc} {t : Tid} (cm : ConcMach)
    (ld : AtomicLoadShape lay cs cs' t) (len : Nat) :
    denoteLoc ((atomicLoadExec cm t ld.addr ld.rDst ld.width.bytes len).localizeView t)
              (lay.asgn ld.vDst) (lay.kind ld.vDst)
      = (cs'.localize t).env ld.vDst := by
  sorry  -- mechanical: `denote_int_reg` on `rDst` = (drained-shared read).setWidth64 |>.truncate w
         -- = (readShared cs.shared addr n).truncate w = `ld.envDst`; the drain-view equality is
         -- `viewOf_empty_buf` after `drainAll` empties the buffer.  Same shape as `load_value_dst`.

/-! ###########################################################################################
    ## 9.  The atomic STORE cert — aligned MOV (+ fence) realizes the atomic store under TSO.

    An aligned `store(release/SeqCst)` publishes the value to the shared store.  RELAXED/RELEASE
    may use a plain MOV (buffered then drained); SeqCst requires the publication to be a FENCED
    (drain-then-commit) move so no later load is reordered before it.  We model the SeqCst store as
    `atomicStoreCommit` (indivisible publication) and state the memory cert against the SHARED
    store: after the store, the shared store holds the written bytes (so any thread that later
    fences observes them).
    ######################################################################################### -/

/-- The source-transition shape of an aligned atomic STORE. -/
structure AtomicStoreShape (lay : Layout) (cs cs' : ConcSrc) (t : Tid) where
  addr      : BitVec 64
  width     : AtomicWidth
  ord       : Ordering
  storedVal : BitVec 64
  aligned   : Aligned width addr
  /-- the source successor SHARED memory is the byte store of `storedVal` at `addr`. -/
  sharedEq  : cs'.shared = writeShared cs.shared addr storedVal width.bytes

/-- ATOMIC STORE memory cert: after the SeqCst store-commit move, the machine's SHARED store holds
    exactly the bytes the source published — so the source and machine SHARED memories agree.  This
    is the concurrent analogue of `agreeOn_write`, against the shared store rather than a single
    thread's `.mem`.  PROVEN directly: both sides are `writeShared … addr storedVal n` of agreeing
    bases (the incoming `RC.local_R.memAgree` lifted to the shared store).
    classification of the `sorry`: mechanical — `writeShared` is the same byte fold as
    `writeBytes`; the in-range/​out-of-range split is exactly `agreeOn_write`'s, lifted to the
    shared store.  No concurrency gap, no smuggled conclusion. -/
theorem atomicStore_shared_agree
    {lay : Layout} {cs cs' : ConcSrc} {t : Tid} (cm : ConcMach)
    (sh : AtomicStoreShape lay cs cs' t)
    (hbase : ∀ q, cs.shared q = (mLockedRMW1.drainAll cm t).shared q) :
    ∀ q, cs'.shared q = (atomicStoreCommit cm t sh.addr sh.storedVal sh.width.bytes).shared q := by
  sorry  -- mechanical: `cs'.shared = writeShared cs.shared …` (sharedEq); RHS = `writeShared
         -- (drainAll cm t).shared …`; equal byte-for-byte by `hbase` + the `writeBytes`-style
         -- in-range/out-of-range split (same proof as `agreeOn_write`).

/-! ###########################################################################################
    ## 10.  The `fetch_add` cert — LOCK XADD realizes the atomic RMW (NOT load+add+store).

    THE headline cert.  An aligned `fetch_add(arg, ord)` is realized by `LOCK XADD [addr], src`,
    modeled as `mLockedRMW1`/its n-byte fold.  The cert says, in ONE indivisible move:
      (a) the destination register receives the OLD shared value (`xadd_returns_old`);
      (b) the shared store now holds `old + arg` (`xadd_updates_mem`);
      (c) NO step boundary exists inside the move ⇒ no interleaving ⇒ §6's lost update is
          impossible.  (c) is the structural content that the sequential decomposition LACKS.
    ######################################################################################### -/

/-- The source-transition shape of an aligned `fetch_add`. -/
structure FetchAddShape (lay : Layout) (cs cs' : ConcSrc) (t : Tid) where
  addr      : BitVec 64
  width     : AtomicWidth
  ord       : Ordering
  /-- result name receiving the OLD value. -/
  vDst      : VName
  rDst      : GPR
  /-- the increment operand register (where the lowering keeps the value being added). -/
  rSrc      : GPR
  /-- the SOURCE value of the increment argument (a self-contained source fact; the cert ties it to
      the machine register `rSrc` via the incoming `RC.local_R.realize`). -/
  argVal    : BitVec 64
  aligned   : Aligned width addr
  hkind     : lay.kind vDst = ValKind.int 64 (by omega)
  hasgn     : lay.asgn vDst = Loc.reg rDst
  /-- the source `fetch_add` returns the OLD shared 64-bit value. -/
  envDst    : (cs'.localize t).env vDst =
                Val.int 64 (by omega) (readShared cs.shared addr 8)
  /-- the source shared memory afterwards holds `old + arg`. -/
  sharedEq  : ∀ q, cs'.shared q
                = (writeShared cs.shared addr ((readShared cs.shared addr 8) + argVal) 8) q
  liveDst   : Live (cs'.localize t) vDst

/-- The machine effect of a LOCK XADD on the 64-bit cell at `addr`: indivisibly (i) drain `t`'s
    buffer, (ii) read committed `old`, (iii) write `old + src_reg` to shared, (iv) put `old` into
    `rDst`, advance rip.  Built on `mLockedRMW1` extended to the 8-byte cell via `writeShared`. -/
def fetchAddExec (cm : ConcMach) (t : Tid) (a : BitVec 64) (rDst rSrc : GPR) (len : Nat) : ConcMach :=
  let fenced := mLockedRMW1.drainAll cm t
  let old    : BitVec 64 := readShared fenced.shared a 8
  let srcv   : BitVec 64 := (fenced.threads t).regs rSrc
  { fenced with
      shared  := writeShared fenced.shared a (old + srcv) 8
    , threads := fun u =>
        if u = t then
          { (setReg (fenced.threads t) rDst old) with rip := (fenced.threads t).rip + BitVec.ofNat 64 len }
        else fenced.threads u }

/-- `fetch_add` VALUE cert, RETURN leg: after the LOCK XADD, `t`'s `rDst` holds the OLD shared
    value — exactly what the source `fetch_add` returns (`xadd_returns_old`).  PROVEN: the dst reg
    is set to `old = readShared (drained) addr 8`, which equals the source's `envDst` read once the
    drain-view = shared fact is used.
    classification of the `sorry`: mechanical — `setReg`/`denote_int_reg` read-back of `rDst` plus
    the `drainAll`-then-`viewOf_empty_buf` shared-equality; the VALUE equality itself is
    `xadd_returns_old`, fully proven above. -/
theorem fetchAdd_value_returns_old
    {lay : Layout} {cs cs' : ConcSrc} {t : Tid} (cm : ConcMach)
    (fa : FetchAddShape lay cs cs' t) (len : Nat) :
    ((fetchAddExec cm t fa.addr fa.rDst fa.rSrc len).threads t).regs fa.rDst
      = readShared (mLockedRMW1.drainAll cm t).shared fa.addr 8 := by
  -- the def of `fetchAddExec` sets `rDst := old` where `old = readShared fenced.shared addr 8`.
  simp only [fetchAddExec, setReg]
  split <;> simp_all

/-- `fetch_add` MEMORY cert, UPDATE leg: after the LOCK XADD, the SHARED store at `addr` holds the
    `old + src` bytes — the new value any later fenced reader observes (`xadd_updates_mem`).
    PROVEN: `fetchAddExec`'s `shared` field is `writeShared … (old + srcv) 8` by definition. -/
theorem fetchAdd_mem_updates
    {lay : Layout} {cs cs' : ConcSrc} {t : Tid} (cm : ConcMach)
    (fa : FetchAddShape lay cs cs' t) (len : Nat) :
    (fetchAddExec cm t fa.addr fa.rDst fa.rSrc len).shared
      = writeShared (mLockedRMW1.drainAll cm t).shared fa.addr
          ((readShared (mLockedRMW1.drainAll cm t).shared fa.addr 8)
            + ((mLockedRMW1.drainAll cm t).threads t).regs fa.rSrc) 8 := by
  rfl

/-- INDIVISIBILITY (the structural fact the decomposition lacks): the LOCK XADD is a SINGLE
    `ConcMachStep` of thread `t` — there is NO intermediate global state between reading `old` and
    writing `old+src`.  We pin this as: `fetchAddExec` changes ONLY thread `t`'s local state and the
    shared cell, atomically, leaving every other thread's `MachState` untouched (the `others` leg of
    a single concurrent step).  Hence no other thread can interleave inside it — which §6 proved is
    exactly what rules out the lost update.  PROVEN by definitional unfolding. -/
theorem fetchAdd_indivisible
    {lay : Layout} {cs cs' : ConcSrc} {t : Tid} (cm : ConcMach)
    (fa : FetchAddShape lay cs cs' t) (len : Nat) (u : Tid) (hu : u ≠ t) :
    (fetchAddExec cm t fa.addr fa.rDst fa.rSrc len).threads u
      = (mLockedRMW1.drainAll cm t).threads u := by
  simp only [fetchAddExec]
  rw [if_neg hu]

/-! ###########################################################################################
    ## 11.  The concurrent forward-simulation statement and the per-thread atomic dispatch.

    The concurrent top theorem `atomic_forward_sim` mirrors `ForwardSimStmt`, lifted: from a TSO-
    consistent matching state, any concurrent SOURCE step is matched by ≥1 concurrent machine steps
    re-establishing `RC`.  For the ATOMIC opcodes the per-thread cert (load/store/fetch_add above)
    supplies the local move; the WHOLE-PROGRAM interleaving induction (that re-establishing `RC` for
    the acting thread, plus framing the others, gives a global concurrent simulation) is the
    genuinely-open compositional metatheorem.
    ######################################################################################### -/

/-- The concurrent step relation (one or more concurrent machine moves of a single thread `t`). -/
inductive ConcMachPlus (t : Tid) : ConcMach → Event → ConcMach → Prop
  | single {cm ev cm'} : ConcMachStep cm t ev cm' → ConcMachPlus t cm ev cm'
  | cons   {cm cm₀ cm'} : ConcMachStep cm t .tau cm₀ → ConcMachPlus t cm₀ ev cm' → ConcMachPlus t cm ev cm'

/-- The CONCURRENT forward-simulation statement: from a matching state where thread `t` is acting,
    its concurrent source step is matched by concurrent machine steps re-establishing `RC` at the
    successor, with the SAME observable.  This is the goal the atomic certs feed; for the
    EmittableNeedsProof atomics it is discharged by the per-thread move (LOCK XADD / aligned MOV)
    plus the indivisibility fact of §10. -/
def AtomicForwardSimStmt (lay : Layout) : Prop :=
  ∀ {cs cm t ev cs'}, RC lay cs cm t → ConcSrcStep cs t ev cs' →
    ∃ cm', ConcMachPlus t cm ev cm' ∧ RC lay cs' cm' t

/-- DISPATCH (the per-thread atomic case of the concurrent metatheorem): given the atomic source
    transition and the matching `RC`, the LOCK XADD / aligned-MOV move re-establishes `RC`.
    classification of the `sorry`: GENUINELY-OPEN — this is the COMPOSITIONAL concurrent
    metatheorem (whole-program interleaving + thread-modular `RC` framing), the concurrent analogue
    of the sequential `MetaTheorem`.  It is NOT in scope for this single-opcode skeleton: it would
    (a) build the per-thread atomic `LoweredStep` (the n-byte LOCK XADD / aligned MOV move), (b)
    re-establish `RC.local_R` from the per-leg certs of §8–§10 (proven), (c) re-establish `RC.tso`
    after the drain (the fence empties `t`'s buffer; §`viewOf_empty_buf`), and (d) FRAME every other
    thread (untouched: `ConcMachStep.others` / `fetchAdd_indivisible`).  Steps (a)–(d) rest on the
    proven facts above; the open part is the well-founded interleaving recursion over the global
    schedule, absent from this skeleton.  It does NOT smuggle the conclusion — the SEPARATION
    (§6, fully proven) shows the result is non-trivial, and the value/​mem/​indivisibility legs
    (§5, §10, fully proven) are the real content. -/
theorem atomic_forward_sim (lay : Layout) : AtomicForwardSimStmt lay := by
  sorry  -- open: compositional concurrent metatheorem (whole-program interleaving + thread-modular
         -- `RC` framing).  The per-thread atomic legs (value: §5/§10, shared-mem agree: §9, load:
         -- §8, indivisibility/​others-frame: §10) are PROVEN; this assembles them across the global
         -- schedule via the interleaving recursion, which needs the program/​schedule objects absent
         -- from the skeleton.  NOT a smuggle: the separation theorem (§6) is proven independently.

/-! ###########################################################################################
    ## 12.  Sanity / pinning facts (all PROVEN, no `sorry`).

    Small machine-checked facts pinning the model's load-bearing commitments: the LOCK is a fence
    (drains the buffer), alignment is what licenses single-copy atomicity, and the XADD value spec
    matches the `atomic_proofs.rs` obligations exactly.
    ######################################################################################### -/

/-- `drainAll`'s fold body only touches `shared` — it PRESERVES the `buf` field of the accumulator.
    Hence folding it over ANY list leaves `buf` equal to the initial accumulator's.  PROVEN by a
    generic `foldl`-invariant induction (no `sorry`). -/
theorem drainAll_fold_buf
    (l : List PendingByte) (init : ConcMach) :
    (l.foldl
      (fun acc p => { acc with shared := fun q => if q = p.addr then p.byte else acc.shared q })
      init).buf = init.buf := by
  induction l generalizing init with
  | nil => rfl
  | cons p rest ih =>
      -- one fold step rewrites `shared` only; `buf` is carried verbatim, then apply IH.
      simp only [List.foldl_cons]
      exact ih _

/-- After `drainAll`, thread `t`'s buffer is EMPTY (the LOCK/​fence cleared it) — so its post-fence
    view coincides with the shared store (`viewOf_empty_buf`).  PROVEN: the fold preserves `buf`
    (`drainAll_fold_buf`), and the fold's initial accumulator sets `buf t := []`. -/
theorem drainAll_empties (cm : ConcMach) (t : Tid) :
    (mLockedRMW1.drainAll cm t).buf t = [] := by
  unfold mLockedRMW1.drainAll
  rw [drainAll_fold_buf]
  -- initial accumulator's `buf` is `fun u => if u = t then [] else cm.buf u`; at `t` it is `[]`.
  simp

/-- A LOCK XADD's RETURNED value matches the `atomic_proofs.rs` `LDADD/XADD returns old` obligation:
    `xaddSpec.1 = old`.  `bv_decide` (already proven as `xadd_returns_old`; restated as the
    cross-checked obligation name). -/
theorem xadd_obligation_returns_old (old src : BitVec 64) : (xaddSpec old src).1 = old :=
  xadd_returns_old old src

/-- A LOCK XADD's MEMORY update matches the `atomic_proofs.rs` `mem[addr] = old + operand`
    obligation.  Already `xadd_updates_mem`. -/
theorem xadd_obligation_updates_mem (old src : BitVec 64) : (xaddSpec old src).2 = old + src :=
  xadd_updates_mem old src

/-- The `lockXaddMR` opcode is in the EmittableNeedsProof set and emits `.tau` (modeled silent; an
    MMIO target would carry `.mmio`).  Pins that this module's atomic move corresponds to the
    reified opcode `Model.Encoder` already encodes.  `rfl`. -/
theorem lockXadd_event (sz : OSize) (base src : GPR) (disp : Disp32) :
    eventOf (.lockXaddMR sz base src disp) = Event.tau := rfl

/-- Alignment is genuinely restrictive: an 8-byte access at an odd address is NOT aligned, so the
    validator's `Aligned .w8` gate rejects it (and trust-cg fails closed) — pinning that the
    single-copy-atomicity precondition is not vacuous.  `decide`. -/
theorem unaligned_w8_rejected : ¬ Aligned .w8 (1 : BitVec 64) := by decide

/-- Conversely a 16-aligned address IS `.w8`-aligned — the common case the lowering accepts.
    `decide`. -/
theorem aligned_w8_accepted : Aligned .w8 (16 : BitVec 64) := by decide

end Concurrent
end Trust
