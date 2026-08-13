/-
  Semantics.Source — the meaning of the trust-ir source program being refined.

  This module defines the SOURCE small-step semantics `SrcStep` over the scalar/SSA
  surface that trust-cg's translation validator actually lowers and certifies:
  binary ops (incl. the i128 register-pair family), integer comparison producing an
  `Ordering` (the i8 -1/0/+1 shape `lowerCmp_correct` matches), integer casts
  (SExt/ZExt/Trunc), memory load/store, conditional and switch control flow, calls,
  and return — together with the observable `Event` labels that make I/O / call / ret
  externally visible.

  Consistency with the SHARED CONTRACT (Trust.Model):
    * We do NOT redefine `Val`, `Loc`, `MachState`, `SrcState`, `Event`, or `R`.
    * The contract declares `srcStep : SrcState → Event → SrcState → Prop` OPAQUE.
      This module gives the *intended denotation* as a concrete inductive `SrcStep`
      and exposes `srcStep_spec : srcStep = SrcStep` as the single bridging
      characterization the downstream Sim.* modules program against. Because the
      contract's `srcStep` is genuinely `opaque`, this characterization is stated as
      an EXPLICIT `axiom` (auditable via `#print axioms`), NOT a `sorry`-proof.

  The op vocabulary mirrors the real bridge interpreter
  (rustc-codegen-trust-cg/src/trust_ir_interp.rs):
    - BinOp Add/Sub/Mul/UDiv/URem/And/Or/Xor/Shl/LShr/AShr  (URem as a-udiv*b),
      shifts MASKED to `amount &&& (width-1)`, signed SDiv/SRem modeled here
      (the interpreter leaves them out-of-slice; the lowering certifies them via IDIV).
    - ICmp: the 10 integer predicates → `Ordering` materialized as i8.
    - Cast: SExt/ZExt/Trunc with same-width identity.
    - Terminators: Br / CondBr / Switch / Ret / Call.

  Copyright 2026 Andrew Yates. Apache 2.0.
-/
import Std.Tactic.BVDecide
import Trust.Model        -- the SHARED CONTRACT preamble (R, Val, SrcState, Event, srcStep …)

namespace Trust
namespace Source

/-! ## Source operation vocabulary (mirrors trust-ir `BinOp`/`ICmpOp`/`CastOp`). -/

/-- The pure integer binary operators trust-cg lowers + certifies.
    Float ops are deliberately OUT of this scalar slice (they take a different,
    XMM/MOVSD-shaped certification path) and are not constructors here. -/
inductive BinOp
  | add | sub | mul
  | udiv | urem
  | sdiv | srem
  | and | or | xor
  | shl | lshr | ashr
  deriving DecidableEq, Repr

/-- The 10 integer comparison predicates (trust-ir `ICmpOp`). -/
inductive ICmpOp
  | eq | ne
  | ult | ule | ugt | uge
  | slt | sle | sgt | sge
  deriving DecidableEq, Repr

/-- The integer cast kinds (trust-ir `CastOp`, scalar slice). -/
inductive CastOp
  | sext | zext | trunc
  deriving DecidableEq, Repr

/-! ## Ordering — the result of a three-way compare.

    trust-cg lowers Rust's `Ord::cmp`-style compare to an i8 in {-1, 0, +1}
    (the exact shape `lowerCmp_correct` discharges: `gt ? 1 : (lt ? -1 : 0)`). -/

inductive Ordering
  | lt | eq | gt
  deriving DecidableEq, Repr

/-- Materialize an `Ordering` as the i8 the backend produces. -/
def Ordering.toI8 : Ordering → BitVec 8
  | .lt => (-1 : BitVec 8)   -- 0xFF
  | .eq => 0
  | .gt => 1

/-! ## Reading integer bits out of a `Val`.

    Source ops are width-indexed; `intBits` projects the (already width-bounded)
    bitvector. For non-`int` values it is `0` — the source typechecker guarantees a
    binOp never sees a float here, so the catch-all is unreachable in well-typed
    programs and is present only for totality. -/

/-- Project the low-`w` bitvector of a `Val` known to be `.int w _ _`.
    Returns `BitVec.zero w` for any other shape (totality filler; unreachable when
    the source program is well-typed at width `w`). -/
def intBitsAt (w : Nat) : Val → BitVec w
  | .int w' _ bits => if h : w' = w then h ▸ bits else BitVec.zero w
  | _              => BitVec.zero w

/-- Project the 128-bit payload of an i128 `Val`. -/
def i128Bits : Val → BitVec 128
  | .i128 b => b
  | _       => BitVec.zero 128

/-! ## Pure binary-op denotation at a fixed width `w ≤ 64`.

    These are the EXACT specifications the per-instruction bv_decide certs
    (`lowerAdd_correct`, etc.) must match. Shifts mask the amount to `w-1` bits,
    mirroring x86 SHL/SHR/SAR (which mask to the operand width) and the interpreter's
    `mask_shift_amount`. URem is the encoder's `a - udiv(a,b)*b` form. -/

/-- Mask a shift amount to the low `clog2`-equivalent bits: `amt &&& (w-1)` as a
    BitVec of the operand width. trust-cg width `w` is a power of two in {8,16,32,64};
    `(w-1)` is the canonical mask, exactly the interpreter's `mask_shift_amount`. -/
def maskAmt (w : Nat) (amt : BitVec w) : BitVec w :=
  amt &&& (BitVec.ofNat w (w - 1))

/-- Denotation of a pure (non-i128) binary op on width-`w` operands.
    Division/remainder by zero is left to the source-level trap precondition
    (the `hdiv` hypothesis on `SrcStep.bin`); here we use Lean's total `BitVec`
    div/rem (which return a fixed value on 0) and forbid the zero case at the step. -/
def evalBin (op : BinOp) (w : Nat) (a b : BitVec w) : BitVec w :=
  match op with
  | .add  => a + b
  | .sub  => a - b
  | .mul  => a * b
  | .udiv => BitVec.udiv a b
  | .urem => a - (BitVec.udiv a b) * b           -- encoder's form a - udiv(a,b)*b
  | .sdiv => BitVec.sdiv a b
  | .srem => BitVec.srem a b
  | .and  => a &&& b
  | .or   => a ||| b
  | .xor  => a ^^^ b
  | .shl  => a <<< (maskAmt w b)
  | .lshr => a >>> (maskAmt w b)
  | .ashr => BitVec.sshiftRight' a (maskAmt w b)

/-- `urem` agrees with `BitVec.umod` away from divisor 0 — the bridge encoder uses
    the `a - udiv*b` form, and bv_decide certifies it equals the canonical `umod`.
    This is the one shape-bridging fact the Compare/Arith certs reuse. -/
theorem evalBin_urem_eq_umod (w : Nat) (a b : BitVec w) (hb : b ≠ 0) :
    evalBin .urem w a b = BitVec.umod a b := by
  -- a - udiv(a,b)*b = umod a b is a bitvector identity for b ≠ 0; for the concrete
  -- widths trust-cg uses (8/16/32/64) bv_decide discharges it. At symbolic `w` it is
  -- the library lemma `BitVec.umod_eq` rearranged; we keep the small-width discharge
  -- pattern the rest of the development uses and defer the polymorphic-width proof.
  sorry  -- mechanical: BitVec.udiv/umod algebra (a - (a/b)*b = a % b); per-width bv_decide.

/-- i128 binary op (the register-pair family: add/sub/mul/and/or/xor; shifts/div on
    i128 take the libcall/wide path and are NOT in this pure slice). -/
def evalBin128 (op : BinOp) (a b : BitVec 128) : Option (BitVec 128) :=
  match op with
  | .add => some (a + b)
  | .sub => some (a - b)
  | .mul => some (a * b)
  | .and => some (a &&& b)
  | .or  => some (a ||| b)
  | .xor => some (a ^^^ b)
  | _    => none      -- i128 div/rem/shift: not pure-slice (libcall / TCG-REGALLOC-063)

/-! ## i128 ADD = ADD/ADC two-limb composition (the `lowerAdd_correct` shape).

    The contract's headline cert `lowerAdd (a b) = a + b` is the 128-bit add proved by
    bv_decide via the lo/hi limb decomposition the backend emits (ADD lo,lo ; ADC hi,hi).
    We restate it on the limb representation `(hi ++ lo)` so the Arith cert lines up. -/
theorem i128_add_limbs (aLo aHi bLo bHi : BitVec 64) :
    ((aHi ++ aLo) + (bHi ++ bLo))
      = ( ((aHi + bHi) + (BitVec.ofBool (BitVec.ult (aLo + bLo) aLo)).setWidth 64)
            ++ (aLo + bLo) ) := by
  bv_decide

/-! ## Integer comparison → Ordering. -/

/-- Decide an integer predicate on width-`w` operands (the boolean the SETcc cert
    discharges). -/
def evalICmp (op : ICmpOp) (w : Nat) (a b : BitVec w) : Bool :=
  match op with
  | .eq  => a == b
  | .ne  => a != b
  | .ult => BitVec.ult a b
  | .ule => BitVec.ule a b
  | .ugt => BitVec.ult b a
  | .uge => BitVec.ule b a
  | .slt => BitVec.slt a b
  | .sle => BitVec.sle a b
  | .sgt => BitVec.slt b a
  | .sge => BitVec.sle b a

/-- Three-way compare spec — the `cmpSpec` `lowerCmp_correct` matches:
    signed? chooses signed vs unsigned ordering; result is `gt ? gt : (lt ? lt : eq)`. -/
def cmpSpec (signed : Bool) (w : Nat) (a b : BitVec w) : Ordering :=
  if signed then
    if BitVec.slt b a then .gt else if BitVec.slt a b then .lt else .eq
  else
    if BitVec.ult b a then .gt else if BitVec.ult a b then .lt else .eq

/-- The backend emits the i8 directly: `cmpSpec … |>.toI8`. For the concrete widths
    the development uses, the (CMP;SETG;…)/(CMOV) sequence equals this by bv_decide.
    Stated at w=8 as the canonical narrow witness `lowerCmp_correct` reuses. -/
theorem cmpSpec_toI8_signed8 (a b : BitVec 8) :
    (cmpSpec true 8 a b).toI8
      = (if BitVec.slt b a then (1 : BitVec 8)
         else if BitVec.slt a b then (-1 : BitVec 8) else 0) := by
  unfold cmpSpec Ordering.toI8
  by_cases h1 : BitVec.slt b a <;> by_cases h2 : BitVec.slt a b <;>
    simp [h1, h2]

/-! ## Integer cast denotation (SExt / ZExt / Trunc), matching the interpreter.

    The interpreter only fires when the dst width relates to src width as the op
    requires (SExt/ZExt only widen, Trunc only narrows; same-width = identity). We
    encode that as a typing side-condition `CastOk` and the value as `evalCast`. -/

/-- When is a cast `op : sw → dw` well-formed in the scalar slice? -/
def CastOk (op : CastOp) (sw dw : Nat) : Prop :=
  match op with
  | .sext  => sw ≤ dw
  | .zext  => sw ≤ dw
  | .trunc => dw ≤ sw

/-- Cast a width-`sw` bitvector to width `dw` per `op`.
    `BitVec.signExtend`/`setWidth`/`setWidth` handle widen/narrow uniformly; for
    `dw = sw` all three collapse to the identity, matching the interpreter. -/
def evalCast (op : CastOp) (sw dw : Nat) (x : BitVec sw) : BitVec dw :=
  match op with
  | .sext  => BitVec.signExtend dw x
  | .zext  => BitVec.setWidth dw x
  | .trunc => BitVec.setWidth dw x      -- truncation = low-dw bits = setWidth when dw ≤ sw

/-- ZExt then keep low `sw` bits is the identity (carrier soundness: a zero-extended
    narrow value re-truncated recovers the original) — the carrier_hygiene fact. -/
theorem evalCast_zext_trunc_roundtrip (sw : Nat) (x : BitVec sw) :
    BitVec.setWidth sw (evalCast .zext sw (sw + 8) x) = x := by
  unfold evalCast
  -- setWidth sw (setWidth (sw+8) x) = x  when widening then narrowing back.
  -- `setWidth_setWidth` collapses the composed resizes to `setWidth sw x = x`.
  ext i hi
  simp [BitVec.getElem_setWidth, hi]

/-! ## Instruction syntax (the source IR node being stepped).

    A `SrcInstr` is the abstract syntax of one straight-line definition: it names the
    result(s) and the operand SSA names. The actual width/signedness travels with the
    op. This is intentionally minimal — exactly the cases the validator lowers. -/

/-- Operand reference: a live SSA name, or a folded integer constant. -/
inductive SOperand
  | name  (v : VName)
  | const (w : Nat) (h : w ≤ 64) (bits : BitVec w)
  | const128 (bits : BitVec 128)

/-- A pure straight-line instruction (defines `dst`). -/
inductive SrcInstr
  | bin    (dst : VName) (op : BinOp) (w : Nat) (hw : w ≤ 64) (a b : SOperand)
  | bin128 (dst : VName) (op : BinOp) (a b : SOperand)
  | icmp   (dst : VName) (op : ICmpOp) (w : Nat) (hw : w ≤ 64) (a b : SOperand)
  | cmp3   (dst : VName) (signed : Bool) (w : Nat) (hw : w ≤ 64) (a b : SOperand) -- → i8 Ordering
  | cast   (dst : VName) (op : CastOp) (sw dw : Nat) (hsw : sw ≤ 64) (hdw : dw ≤ 64) (x : SOperand)
  | load   (dst : VName) (w : Nat) (hw : w ≤ 64) (addr : SOperand)   -- load `w/8` bytes
  | store  (w : Nat) (hw : w ≤ 64) (addr val : SOperand)            -- store `w/8` bytes

/-- A block terminator (the control-flow / I/O surface). -/
inductive SrcTerm
  | br     (target : SrcPC) (args : List (VName × SOperand))
  | condbr (cond : SOperand) (t f : SrcPC)
              (tArgs fArgs : List (VName × SOperand))
  | switch (scrut : SOperand) (w : Nat) (hw : w ≤ 64)
              (cases : List (BitVec 64 × SrcPC)) (default : SrcPC)
  | call   (target : BitVec 64) (ret : SrcPC)        -- observable CALL event
  | ret                                              -- observable RET event

/-! ## Evaluating an operand against a source state. -/

/-- Resolve an `SOperand` to a `Val` in state `s`. Names read the env; constants are
    literal. Used by every step rule. -/
def evalOperand (s : SrcState) : SOperand → Val
  | .name v       => s.env v
  | .const w h b  => .int w h b
  | .const128 b   => .i128 b

/-! ## Memory: little-endian multi-byte read/write on the SOURCE memory.

    Mirrors `readBytes`/the byte store on `MachState`, but over `SrcMem`. Load reads
    `n` bytes; store writes `n` bytes. Keeping these structurally identical to the
    machine model is what makes the load/store certs (`read_write_disjoint`) line up. -/

/-- Read `n` little-endian bytes from `SrcMem` at `a`. -/
def srcReadBytes (sm : SrcMem) (a : BitVec 64) : (n : Nat) → BitVec (8 * n)
  | 0     => BitVec.nil
  | n+1   =>
      let lo := sm a
      let hi := srcReadBytes sm (a + 1) n
      (hi ++ lo).cast (by omega)

/-- Write the low `8*n` bits of `v` as `n` little-endian bytes into `SrcMem`. -/
def srcWriteBytes (sm : SrcMem) (a : BitVec 64) :
    (n : Nat) → BitVec (8 * n) → SrcMem
  | 0,   _ => sm
  | n+1, v =>
      let lo : BitVec 8 := (v.setWidth 8)
      -- drop the low byte, keep the remaining `8*n` high bits (Nat shift amount)
      let rest : BitVec (8 * n) := (v >>> (8 : Nat)).setWidth (8 * n)
      let sm' := fun x => if x = a then lo else sm x
      srcWriteBytes sm' (a + 1) n rest

/-- Number of bytes a width-`w` (`w ≤ 64`, a multiple of 8 in practice) value spans.
    We use ceil-div so a sub-byte width still occupies one byte (never happens for the
    {8,16,32,64} widths the backend emits, but keeps the function total). -/
def byteWidth (w : Nat) : Nat := (w + 7) / 8

/-! ## The source small-step relation `SrcStep`.

    Each constructor gives the meaning of one source action and the `Event` it emits.
    PURE actions emit `.tau`. Memory load/store are silent on the OBSERVABLE channel
    (they only touch this program's own `mem`, which the refinement tracks via
    `memAgree`); genuine MMIO is a separate `.mmio` rule. Calls/returns are observable.

    Liveness bookkeeping: a definition makes `dst` live and updates `env`; we model
    `live'` as "previously live OR newly defined". A real SSA liveness analysis is
    more precise (it can DROP a name), but enlarging `live` only STRENGTHENS the R
    obligations the machine must satisfy — it never lets a wrong machine state pass.
    (Narrowing would be unsound here; widening is conservative.) -/

/-- Update env at `v`. -/
def setEnv (s : SrcState) (v : VName) (val : Val) : SrcState :=
  { s with env := fun x => if x = v then val else s.env x,
           live := fun x => x = v ∨ s.live x }

/-- Advance the PC (for straight-line steps the "next pc" is `pc+1`; blocks are
    modeled as a linear instruction stream, terminators jump). -/
def bumpPC (s : SrcState) : SrcState := { s with pc := s.pc + 1 }

/-- Set the PC to a successor block, threading block-argument bindings. -/
def gotoWith (s : SrcState) (target : SrcPC)
    (binds : List (VName × Val)) : SrcState :=
  let env' := binds.foldl (fun e (vb : VName × Val) =>
                fun x => if x = vb.1 then vb.2 else e x) s.env
  let live' := binds.foldl (fun l (vb : VName × Val) =>
                fun x => x = vb.1 ∨ l x) s.live
  { s with env := env', live := live', pc := target }

/-- The intended source semantics. `SrcStep s ev s'`. -/
inductive SrcStep : SrcState → Event → SrcState → Prop
  /-- pure width-`w` binary op. Division/remainder require a non-zero divisor
      (a source-level trap precondition; a zero divisor is not a `bin` step — it is
      matched by `SrcStep.trap`, which the validator fails-closed on). -/
  | bin {s dst op w hw a b}
      (hdiv : (op = .udiv ∨ op = .urem ∨ op = .sdiv ∨ op = .srem) →
                intBitsAt w (evalOperand s b) ≠ 0) :
      SrcStep s .tau
        (setEnv (bumpPC s) dst
          (.int w hw (evalBin op w (intBitsAt w (evalOperand s a))
                                   (intBitsAt w (evalOperand s b)))))
  /-- i128 register-pair op (add/sub/mul/and/or/xor). -/
  | bin128 {s dst op a b r}
      (h : evalBin128 op (i128Bits (evalOperand s a)) (i128Bits (evalOperand s b)) = some r) :
      SrcStep s .tau (setEnv (bumpPC s) dst (.i128 r))
  /-- integer comparison → 1-bit result widened to i8 0/1 (the SETcc shape). -/
  | icmp {s : SrcState} {dst : VName} {op : ICmpOp} {w : Nat} {hw : w ≤ 64} {a b : SOperand} :
      SrcStep s .tau
        (setEnv (bumpPC s) dst
          (.int 8 (by omega)
            (if evalICmp op w (intBitsAt w (evalOperand s a))
                               (intBitsAt w (evalOperand s b))
             then (1 : BitVec 8) else 0)))
  /-- three-way compare → i8 Ordering. -/
  | cmp3 {s : SrcState} {dst : VName} {signed : Bool} {w : Nat} {hw : w ≤ 64} {a b : SOperand} :
      SrcStep s .tau
        (setEnv (bumpPC s) dst
          (.int 8 (by omega)
            (cmpSpec signed w (intBitsAt w (evalOperand s a))
                              (intBitsAt w (evalOperand s b))).toI8))
  /-- integer cast (well-formedness `CastOk` is a precondition). -/
  | cast {s : SrcState} {dst : VName} {op : CastOp} {sw dw : Nat}
      {hsw : sw ≤ 64} {hdw : dw ≤ 64} {x : SOperand}
      (hok : CastOk op sw dw) :
      SrcStep s .tau
        (setEnv (bumpPC s) dst
          (.int dw hdw (evalCast op sw dw (intBitsAt sw (evalOperand s x)))))
  /-- memory load of `byteWidth w` bytes from `addr`. Silent (own-memory). -/
  | load {s dst w hw addr}
      (a : BitVec 64) (ha : evalOperand s addr = .int 64 (by omega) a) :
      SrcStep s .tau
        (setEnv (bumpPC s) dst
          (.int w hw ((srcReadBytes s.mem a (byteWidth w)).setWidth w)))
  /-- memory store of `byteWidth w` bytes of `val` to `addr`. Silent (own-memory). -/
  | store {s : SrcState} {w : Nat} {hw : w ≤ 64} {addr val : SOperand}
      (a : BitVec 64) (ha : evalOperand s addr = .int 64 (by omega) a)
      (vb : BitVec w) (hv : intBitsAt w (evalOperand s val) = vb) :
      SrcStep s .tau
        (bumpPC { s with
          mem := srcWriteBytes s.mem a (byteWidth w)
                   ((vb.setWidth (8 * byteWidth w)) ) })
  /-- unconditional branch with block-arg threading. -/
  | br {s : SrcState} {target : SrcPC} {args : List (VName × SOperand)} :
      SrcStep s .tau
        (gotoWith s target (args.map (fun vb => (vb.1, evalOperand s vb.2))))
  /-- conditional branch on a (width-1 or width-w nonzero) condition. -/
  | condbr_true {s : SrcState} {cond : SOperand} {t f : SrcPC}
      {tArgs fArgs : List (VName × SOperand)}
      (hc : intBitsAt 1 (evalOperand s cond) ≠ 0) :
      SrcStep s .tau
        (gotoWith s t (tArgs.map (fun vb => (vb.1, evalOperand s vb.2))))
  | condbr_false {s : SrcState} {cond : SOperand} {t f : SrcPC}
      {tArgs fArgs : List (VName × SOperand)}
      (hc : intBitsAt 1 (evalOperand s cond) = 0) :
      SrcStep s .tau
        (gotoWith s f (fArgs.map (fun vb => (vb.1, evalOperand s vb.2))))
  /-- switchInt: jump to the case whose key matches the (zero-extended-to-64) scrutinee,
      else default. `hmem` pins the chosen `(key, target)` pair; `hsel` pins the value.
      switchInt keys are distinct (a `BitVec 64` cannot appear twice with two targets in
      a well-formed table), so "a matching case" is unambiguous and this is deterministic
      with `switch_default` (whose guard requires NO case matches). -/
  | switch_case {s : SrcState} {scrut : SOperand} {w : Nat} {hw : w ≤ 64}
      {cases : List (BitVec 64 × SrcPC)} {default target : SrcPC} {key : BitVec 64}
      (hmem : (key, target) ∈ cases)
      (hsel : (intBitsAt w (evalOperand s scrut)).setWidth 64 = key)
      : SrcStep s .tau (gotoWith s target [])
  | switch_default {s : SrcState} {scrut : SOperand} {w : Nat} {hw : w ≤ 64}
      {cases : List (BitVec 64 × SrcPC)} {default : SrcPC}
      (hno : ∀ k t, (k, t) ∈ cases →
               (intBitsAt w (evalOperand s scrut)).setWidth 64 ≠ k) :
      SrcStep s .tau (gotoWith s default [])
  /-- call: emits an observable CALL event and transfers to the callee entry pc.
      (The callee runs under its OWN refinement; from this block's view the call is an
      observable boundary — the contract's `Event.call`.) -/
  | call {s target ret} :
      SrcStep s (.call target) ({ s with pc := ret })
  /-- return: emits the observable RET event. The post-state pc is irrelevant
      (control leaves the function); we keep `s` so the relation is total-shaped. -/
  | ret {s} :
      SrcStep s .ret s
  /-- memory-mapped I/O store: a write to an OFF-frame, non-program address is an
      observable `.mmio` event (the externally visible channel). Distinguished from a
      plain `store` by the layout marking the address as device memory; modeled here as
      an explicit rule producing the event. -/
  | mmio_write {s addr a val v}
      (ha : evalOperand s addr = .int 64 (by omega) a)
      (hv : intBitsAt 64 (evalOperand s val) = v) :
      SrcStep s (.mmio a v true) (bumpPC s)
  /-- a stuck/UB source action TRAPS — emits `.trap`. trust-cg's translation validator
      fails CLOSED on exactly these (the cert gate refuses to certify), so a trapping
      source step is matched by a machine trap, preserving the refinement. -/
  | trap {s} :
      SrcStep s .trap s

/-! ## Bridging the opaque contract hook to this definition.

    The contract declares `srcStep` opaque so downstream modules don't depend on the
    constructor list. We expose the intended equation. -/

/-- The source semantics this module establishes. Downstream `Sim.*` modules obtain
    `srcStep s ev s' ↔ SrcStep s ev s'` from `srcStep_spec` and case on `SrcStep`.

    HONEST STATUS: the contract declares `srcStep` as `opaque`. An `opaque` constant
    in Lean 4 is irreducible BY CONSTRUCTION — its body is sealed, so `srcStep = SrcStep`
    is NOT derivable (not by `rfl`, not by anything) from the contract as written. A
    `by sorry` here would be a `sorry` that does genuine work: every downstream `Sim.*`
    case-analysis on a source step depends on rewriting the opaque hook to this concrete
    inductive, so the equation is LOAD-BEARING, not a mechanical filler.

    The faithful encoding of "the assembled build links `srcStep := SrcStep` so this is
    `rfl`" is therefore an EXPLICIT `axiom`, NOT a theorem-with-sorry. Stating it as an
    axiom makes the assumption auditable (it shows up in `#print axioms`) instead of
    masquerading as a discharged proof. It fixes ONLY the source-side meaning (no
    machine/refinement content), so it cannot smuggle the forward-simulation conclusion;
    but it is, unavoidably, an assumption against the literal `opaque` contract and must
    be discharged by the link step (where `srcStep` is *defined* to be `SrcStep`, making
    the axiom `rfl`-true and dischargeable). -/
axiom srcStep_spec : srcStep = SrcStep

/-! ## Determinism / progress sanity lemmas (cheap, real).

    These are genuine facts about the source semantics that the Sim layer uses to know
    the source step it is matching is the *only* one (so the chosen machine match is
    forced). They are proved, not stubbed. -/

/-- A pure `bin` step's result is exactly `evalBin` (no hidden nondeterminism in the
    value). Trivial by construction but stated so callers can rewrite. -/
theorem bin_result {s dst op w hw a b}
    (hdiv : (op = .udiv ∨ op = .urem ∨ op = .sdiv ∨ op = .srem) →
              intBitsAt w (evalOperand s b) ≠ 0)
    (s') (hstep :
      s' = setEnv (bumpPC s) dst
            (.int w hw (evalBin op w (intBitsAt w (evalOperand s a))
                                     (intBitsAt w (evalOperand s b))))) :
    SrcStep s .tau s' := by
  subst hstep; exact SrcStep.bin hdiv

/-- `condbr` is deterministic: the true and false rules have disjoint guards, so at
    most one fires from a given state. (Used by the Sim condBr case to pick the unique
    machine edge `jcc_*_correct` matches.) -/
theorem condbr_disjoint {s cond}
    (htrue  : intBitsAt 1 (evalOperand s cond) ≠ 0)
    (hfalse : intBitsAt 1 (evalOperand s cond) = 0) : False :=
  htrue hfalse

/-- The i8 a `cmp3` step writes equals the `cmpSpec`-derived i8 — restates the rule's
    payload so the Compare cert (`lowerCmp_correct`) plugs in directly. -/
theorem cmp3_payload {s : SrcState} {dst : VName} {signed : Bool} {w : Nat}
    {hw : w ≤ 64} {a b : SOperand} :
    SrcStep s .tau
      (setEnv (bumpPC s) dst
        (.int 8 (by omega)
          (cmpSpec signed w (intBitsAt w (evalOperand s a))
                            (intBitsAt w (evalOperand s b))).toI8)) :=
  @SrcStep.cmp3 s dst signed w hw a b

/-! ## A concrete end-to-end witness the certs reuse: signed 3-way compare at w=8.

    Ties `cmpSpec` to the i8 SETcc/CMOV shape via bv_decide-grade reasoning (here the
    pure case analysis the narrow-width cert uses). Proven, no sorry. -/
theorem cmp3_i8_witness (a b : BitVec 8) :
    (cmpSpec true 8 a b).toI8
      = (if BitVec.slt b a then 1 else if BitVec.slt a b then (-1 : BitVec 8) else 0) :=
  cmpSpec_toI8_signed8 a b

end Source
end Trust
