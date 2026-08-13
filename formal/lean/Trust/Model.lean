/-
  Model preamble — the SINGLE SOURCE OF TRUTH for trust-cg's Lean correctness development.
  Every downstream module imports this. Do NOT redefine R, Val, Loc, MachState, or SrcState elsewhere.
  Copyright 2026 Andrew Yates. Apache 2.0.
-/
import Std.Tactic.BVDecide

namespace Trust

/-! ## Locations and the architectural register files -/

/-- 16 general-purpose registers (rax..r15) named symbolically. -/
inductive GPR
  | rax | rcx | rdx | rbx | rsp | rbp | rsi | rdi
  | r8 | r9 | r10 | r11 | r12 | r13 | r14 | r15
  deriving DecidableEq, Repr

/-- 16 SSE registers (xmm0..xmm15). -/
inductive XMM
  | x0 | x1 | x2 | x3 | x4 | x5 | x6 | x7
  | x8 | x9 | x10 | x11 | x12 | x13 | x14 | x15
  deriving DecidableEq, Repr

/-- A frame slot is a byte offset from the canonical frame base (negative = below). -/
structure FrameSlot where
  byteOff : Int
  width   : Nat            -- size in bytes occupied (8 for a GPR spill, 16 for i128/xmm)
  deriving DecidableEq, Repr

/-- Where a lowered value physically lives. `pair` is an i128 register pair (lo,hi). -/
inductive Loc
  | reg   (r : GPR)
  | pair  (lo hi : GPR)
  | xmm   (x : XMM)
  | spill (slot : FrameSlot)
  deriving DecidableEq, Repr

/-! ## Values: width-indexed bitvectors -/

/-- A source/lowered semantic value. `int` carries its proven width bound. -/
inductive Val
  | int  (w : Nat) (h : w ≤ 64) (bits : BitVec w)
  | i128 (bits : BitVec 128)
  | f64  (bits : BitVec 64)
  | f32  (bits : BitVec 32)

/-- The *kind* (shape) a value will occupy, independent of its bits.
    `asgn v` gives the Loc; `kind v` gives how to read it back. -/
inductive ValKind
  | int  (w : Nat) (h : w ≤ 64)
  | i128
  | f64
  | f32
  deriving Repr

/-! ## Machine state -/

/-- x86 EFLAGS subset that trust-cg's EmittableNeedsProof set reads/writes. -/
structure Flags where
  cf : Bool    -- carry
  zf : Bool    -- zero
  sf : Bool    -- sign
  of : Bool    -- overflow
  pf : Bool    -- parity
  deriving DecidableEq, Repr

/-- Concrete x86-64 machine state. Registers are full 64-bit; xmm full 128-bit.
    `mem` is a byte-addressed store; `rip` is the program counter. -/
structure MachState where
  regs  : GPR → BitVec 64
  xmms  : XMM → BitVec 128
  flags : Flags
  mem   : BitVec 64 → BitVec 8        -- little-endian byte store
  rip   : BitVec 64

/-- Read `n` little-endian bytes from `mem` at address `a`. -/
def readBytes (m : MachState) (a : BitVec 64) : (n : Nat) → BitVec (8 * n)
  | 0     => BitVec.nil
  | n+1   =>
      let lo := m.mem a
      let hi := readBytes m (a + 1) n
      (hi ++ lo).cast (by omega)

/-- denoteLoc: read a `Val` of the requested `ValKind` out of the machine.
    KEY DESIGN POINT: the `.reg`/`.int` case truncates to the low `w` bits —
    the high carrier bits of `m.regs r` are GARBAGE and may be dirty.
    Consumers reading >w bits must rely on the `carrier` conjunct of R. -/
def denoteLoc (m : MachState) (l : Loc) : ValKind → Val
  | .int w h =>
      match l with
      | .reg r     => .int w h ((m.regs r).truncate w)
      | .spill s   => .int w h ((readBytes m (BitVec.ofInt 64 s.byteOff) 8).truncate w)
      | .pair lo _ => .int w h ((m.regs lo).truncate w)   -- narrow read of a pair's lo
      | .xmm x     => .int w h ((m.xmms x).truncate w)
  | .i128 =>
      match l with
      | .pair lo hi => .i128 ((m.regs hi ++ m.regs lo).cast (by omega))
      | .reg r      => .i128 (((BitVec.zero 64) ++ m.regs r).cast (by omega))
      | .spill s    => .i128 (readBytes m (BitVec.ofInt 64 s.byteOff) 16)
      | .xmm x      => .i128 (m.xmms x)
  | .f64 =>
      match l with
      | .xmm x   => .f64 ((m.xmms x).truncate 64)
      | .reg r   => .f64 (m.regs r)
      | .spill s => .f64 ((readBytes m (BitVec.ofInt 64 s.byteOff) 8))
      | .pair lo _ => .f64 (m.regs lo)
  | .f32 =>
      match l with
      | .xmm x   => .f32 ((m.xmms x).truncate 32)
      | .reg r   => .f32 ((m.regs r).truncate 32)
      | .spill s => .f32 ((readBytes m (BitVec.ofInt 64 s.byteOff) 4))
      | .pair lo _ => .f32 ((m.regs lo).truncate 32)

/-! ## Source machine (the IR being refined) -/

/-- Abstract source SSA value name. -/
abbrev VName := Nat

/-- Abstract source program point / basic-block label. -/
abbrev SrcPC := Nat

/-- The source-level abstract memory: byte store, same address space as MachState. -/
abbrev SrcMem := BitVec 64 → BitVec 8

/-- Source program state: an environment of live SSA values, a memory, a PC. -/
structure SrcState where
  env  : VName → Val
  mem  : SrcMem
  pc   : SrcPC
  live : VName → Prop          -- which names are currently live
  -- No `deriving Inhabited`: `env : VName → Val` cannot be defaulted (`Val` has no canonical
  -- inhabitant) and `live` is a function into `Prop`. The refinement development never needs
  -- `Inhabited SrcState`; a manual instance can be supplied downstream if ever required.

/-- `Live s v` : abbreviation used throughout the R conjuncts. -/
abbrev Live (s : SrcState) (v : VName) : Prop := s.live v

/-! ## Observable events (for the simulation relation's labels) -/

inductive Event
  | tau                                    -- silent internal step
  | call   (target : BitVec 64)
  | ret
  | mmio   (addr : BitVec 64) (val : BitVec 64) (isWrite : Bool)
  | trap                                   -- fail-closed / UD2 / fault
  deriving Repr

/-! ## The lowering layout: connects source names/pcs to machine resources -/

/-- Static assignment produced by regalloc + the lowering. `asgn`/`kind` are total
    on live names; `lowerOf`/`entryAddr` map source PCs to machine entry addresses;
    `nonFrame` is the set of addresses NOT owned by the spill frame (where src/mach mem must agree). -/
structure Layout where
  asgn      : VName → Loc
  kind      : VName → ValKind
  lowerOf   : SrcPC → SrcPC               -- source pc → lowered block id
  entryAddr : SrcPC → BitVec 64           -- lowered block id → machine entry address
  nonFrame  : BitVec 64 → Prop            -- addresses outside the spill frame

/-- `agreeOn s m p` : src and mach memory agree on every address satisfying `p`. -/
def agreeOn (sm : SrcMem) (m : MachState) (p : BitVec 64 → Prop) : Prop :=
  ∀ a, p a → sm a = m.mem a

/-! ## Carrier-hygiene (WidthFaithful) invariant -/

/-- A live narrow int value is WidthFaithful iff its *full physical 64-bit register*
    holds the correctly-extended (sign/zero per its declared signedness) value, so a
    consumer that reads >w bits sees a sound extension rather than dirty garbage.
    Concretely the per-name obligation: the physical contents equal the canonical
    extension of the low-w truncation. Producers that leave dirty high bits must be
    bracketed by a re-extend before any wide consumer (the carrier_hygiene validator). -/
def WidthFaithful (lay : Layout) (s : SrcState) (m : MachState) : Prop :=
  ∀ v, Live s v →
    match lay.kind v, lay.asgn v with
    | .int w _, .reg r =>
        -- high (64-w) bits are the canonical zero/sign extension of the low w bits
        -- (signedness is recorded in the source value; modeled here as: read-back at 64 is determined by low w)
        (m.regs r) = ((m.regs r).truncate w).setWidth 64
    | _, _ => True

/-! ## THE refinement relation R (four conjuncts) — do NOT redefine downstream -/

structure R (lay : Layout) (s : SrcState) (m : MachState) : Prop where
  /-- realize: every live source value is denotable at its assigned Loc/kind. -/
  realize  : ∀ v, Live s v → denoteLoc m (lay.asgn v) (lay.kind v) = s.env v
  /-- carrier: the carrier_hygiene / WidthFaithful invariant. -/
  carrier  : WidthFaithful lay s m
  /-- memAgree: src and mach memory agree off the spill frame (memory non-interference). -/
  memAgree : agreeOn s.mem m (lay.nonFrame)
  /-- pcSync: the machine PC sits at the entry of the lowered current block. -/
  pcSync   : m.rip = lay.entryAddr (lay.lowerOf s.pc)

/-! ## Small-step signatures -/

/-- Source small-step: `srcStep s ev s'`. Defined by the Semantics.Source module. -/
opaque srcStep : SrcState → Event → SrcState → Prop

/-- Machine single small-step: `x86Step m ev m'`. Defined by Model.Machine (decode∘execute). -/
opaque x86Step : MachState → Event → MachState → Prop

/-- Transitive (one-or-more) machine step: a single source instruction lowers to ≥1 x86 ops. -/
inductive x86StepPlus : MachState → Event → MachState → Prop
  | single {m ev m'} : x86Step m ev m' → x86StepPlus m ev m'
  | cons   {m m₀ m'} : x86Step m .tau m₀ → x86StepPlus m₀ ev m' → x86StepPlus m ev m'

/-! ## bv_decide enum-encoding anchor.

    `bv_decide` reflects a `DecidableEq` enum (like `GPR`) into a `BitVec` by generating a
    global `<Type>.enumToBitVec`. It generates this the FIRST time a `bv_decide` goal mentions
    the enum and REUSES an existing one thereafter. Both `Sim.Match` and `Model.Encoder`
    invoke `bv_decide` over `GPR`, so without a shared definition each would generate its own
    `Trust.GPR.enumToBitVec` and any module importing BOTH would hit a duplicate-declaration
    clash. Anchoring the generation here (the single base every module imports) makes both
    downstream modules reuse this one copy. Content-free: a trivially-true `bv_decide` fact. -/
private theorem gpr_enumToBitVec_anchor (a b : GPR) (h : a = b) : b = a := by bv_decide

/-! ## The top-level forward-simulation statement (proved in Sim.ForwardSim.* / MetaTheorem). -/

/-- forward_sim contract: from a matching state, any source step is matched by ≥1 machine
    steps landing in a re-matched state with the same observable event. -/
def ForwardSimStmt (lay : Layout) : Prop :=
  ∀ {s m ev s'}, R lay s m → srcStep s ev s' →
    ∃ m', x86StepPlus m ev m' ∧ R lay s' m'

end Trust
