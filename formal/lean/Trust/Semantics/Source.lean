/-
  Semantics.Source — the meaning of the trust-ir source program being refined.

  This module defines the SOURCE small-step semantics `SrcStep` over the scalar/SSA
  surface that trust-cg's translation validator actually lowers and certifies:
  binary ops (incl. the i128 register-pair family), integer comparison producing an
  `Ordering` (the i8 -1/0/+1 shape `lowerCmp_correct` matches), integer casts
  (SExt/ZExt/Trunc), memory load/store, conditional and switch control flow, calls,
  and return — together with the observable `Event` labels that make I/O / call / ret
  externally visible.

  Consistency with the SHARED CONTRACT (Trust.Model.Core):
    * We do NOT redefine `Val`, `Loc`, `MachState`, `SrcState`, `Event`, or `R`.
    * `Trust.Model` (the link step) DEFINES `srcStep p := SrcStep p`, so the equation
      `Source.srcStep_spec p : srcStep p = SrcStep p` is `rfl` there. While the contract
      declared `srcStep` opaque, that equation was an explicit axiom.
    * `SrcStep p` fetches the exact instruction at the current PC in `p`.
      Returns and operation-local faults terminate. No rule can introduce an
      unrelated call, return, trap or MMIO action.

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
import Trust.Model.Core   -- the SHARED CONTRACT preamble (R, Val, SrcState, Event …)

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

    These are the value specifications the instruction certs must match. Shifts
    retain OD-57's selected masked refinement outside the TrustIR-defined range;
    the interpreter itself reports out-of-range shifts as undefined behavior.
    For admitted power-of-two widths the in-range values agree. URem is the
    encoder's `a - udiv(a,b)*b` form. -/

/-- Mask a shift amount to the low `clog2`-equivalent bits: `amt &&& (w-1)` as a
    BitVec of the operand width. trust-cg width `w` is a power of two in {8,16,32,64};
    `(w-1)` is the canonical mask, exactly the interpreter's `mask_shift_amount`. -/
def maskAmt (w : Nat) (amt : BitVec w) : BitVec w :=
  amt &&& (BitVec.ofNat w (w - 1))

/-- Denotation of a pure (non-i128) binary op on width-`w` operands.
    Division/remainder by zero is left to the source-level trap precondition
    (the division guard in `execute`); Lean's total `BitVec` denotations are
    used only after excluding zero divisors and signed MIN / -1 overflow. -/
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

/-- `urem` agrees with `BitVec.umod` away from divisor zero. Natural-number
    quotient/remainder decomposition proves the encoder's subtraction form at
    every width, including the modular subtraction bookkeeping. -/
theorem evalBin_urem_eq_umod (w : Nat) (a b : BitVec w) (hb : b ≠ 0) :
    evalBin .urem w a b = BitVec.umod a b := by
  have hprod := Nat.div_mul_le_self a.toNat b.toNat
  have hsum := Nat.mod_add_div a.toNat b.toNat
  rw [Nat.mul_comm] at hsum
  have hbound := a.isLt
  have hprodmod : (a.toNat / b.toNat * b.toNat) % 2 ^ w = a.toNat / b.toNat * b.toNat :=
    Nat.mod_eq_of_lt (by omega)
  have hcalc : 2 ^ w - a.toNat / b.toNat * b.toNat + a.toNat =
      2 ^ w + a.toNat % b.toNat := by omega
  apply BitVec.eq_of_toNat_eq
  simp only [evalBin, BitVec.udiv_eq, BitVec.umod_eq, BitVec.toNat_sub,
    BitVec.toNat_mul, BitVec.toNat_udiv, BitVec.toNat_umod]
  rw [hprodmod, hcalc, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]

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

/-- An immutable program position selects exactly one operation. -/
inductive CodeItem
  | instr (instruction : SrcInstr)
  | term (terminator : SrcTerm)
  | mmioWrite (address value : SOperand)
  | trap

/-- The source instruction map is a semantic input, not mutable source memory. -/
structure Program where
  code : SrcPC → Option CodeItem

def Program.ofList (items : List CodeItem) : Program :=
  ⟨fun pc => items[pc]?⟩

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

/-- Faults are selected by the fetched operation or invalid control, and terminate. -/
def fault (s : SrcState) : Event × SrcState := (.trap, { s with halted := true })

def hasIntWidth (w : Nat) : Val → Bool
  | .int actual _ _ => actual == w
  | _ => false

/-- Comparisons materialize canonical i8 0/1; B1 constants use width one. -/
def hasBool : Val → Bool
  | .int w _ bits => decide (w = 1 ∨ w = 8) && decide (bits.toNat ≤ 1)
  | _ => false

/-- Read a canonical boolean after `hasBool` has established its representation. -/
def boolValue : Val → Bool
  | .int _ _ bits => bits.toNat == 1
  | _ => false

def hasI128 : Val → Bool
  | .i128 _ => true
  | _ => false

def needsNonzeroDivisor : BinOp → Bool
  | .udiv | .urem | .sdiv | .srem => true
  | _ => false

/-- TrustIR signed division AND remainder are undefined at MIN / -1 (OD-178). -/
def signedDivOverflow (op : BinOp) (w : Nat) (a b : BitVec w) : Bool :=
  match op with
  | .sdiv | .srem => decide (0 < w) &&
      (a == BitVec.ofNat w (2 ^ (w - 1))) && (b == -1)
  | _ => false

def divisionFault (op : BinOp) (w : Nat) (a b : BitVec w) : Bool :=
  (needsNonzeroDivisor op && (b == 0)) || signedDivOverflow op w a b

def castAllowed (op : CastOp) (sw dw : Nat) : Bool :=
  match op with
  | .sext | .zext => decide (sw ≤ dw)
  | .trunc => decide (dw ≤ sw)

theorem castAllowed_iff (op : CastOp) (sw dw : Nat) :
    castAllowed op sw dw = true ↔ CastOk op sw dw := by
  cases op <;> simp [castAllowed, CastOk]

def addressOperand (s : SrcState) (operand : SOperand) : Option (BitVec 64) :=
  if hasIntWidth 64 (evalOperand s operand) then some (intBitsAt 64 (evalOperand s operand))
  else none

/-- Execute the selected operation. Existing arithmetic denotations are unchanged.
    Ill-typed operands, invalid casts, zero divisors, signed division overflow and unsupported i128 operations
    fault at that operation. Duplicate switch keys are malformed and fault too. -/
def execute (item : CodeItem) (s : SrcState) : Event × SrcState :=
  match item with
  | .instr (.bin dst op w hw a b) =>
      if hasIntWidth w (evalOperand s a) && hasIntWidth w (evalOperand s b) then
        if divisionFault op w (intBitsAt w (evalOperand s a))
            (intBitsAt w (evalOperand s b)) then fault s
        else (.tau, setEnv (bumpPC s) dst
          (.int w hw (evalBin op w (intBitsAt w (evalOperand s a))
            (intBitsAt w (evalOperand s b)))))
      else fault s
  | .instr (.bin128 dst op a b) =>
      if hasI128 (evalOperand s a) && hasI128 (evalOperand s b) then
        match evalBin128 op (i128Bits (evalOperand s a)) (i128Bits (evalOperand s b)) with
        | some result => (.tau, setEnv (bumpPC s) dst (.i128 result))
        | none => fault s
      else fault s
  | .instr (.icmp dst op w _ a b) =>
      if hasIntWidth w (evalOperand s a) && hasIntWidth w (evalOperand s b) then
        (.tau, setEnv (bumpPC s) dst (.int 8 (by omega)
          (if evalICmp op w (intBitsAt w (evalOperand s a))
            (intBitsAt w (evalOperand s b)) then 1 else 0)))
      else fault s
  | .instr (.cmp3 dst signed w _ a b) =>
      if hasIntWidth w (evalOperand s a) && hasIntWidth w (evalOperand s b) then
        (.tau, setEnv (bumpPC s) dst (.int 8 (by omega)
          (cmpSpec signed w (intBitsAt w (evalOperand s a))
            (intBitsAt w (evalOperand s b))).toI8))
      else fault s
  | .instr (.cast dst op sw dw _ hdw x) =>
      if hasIntWidth sw (evalOperand s x) && castAllowed op sw dw then
        (.tau, setEnv (bumpPC s) dst
          (.int dw hdw (evalCast op sw dw (intBitsAt sw (evalOperand s x)))))
      else fault s
  | .instr (.load dst w hw addr) =>
      match addressOperand s addr with
      | some a => (.tau, setEnv (bumpPC s) dst
          (.int w hw ((srcReadBytes s.mem a (byteWidth w)).setWidth w)))
      | none => fault s
  | .instr (.store w _ addr val) =>
      match addressOperand s addr with
      | some a =>
          if hasIntWidth w (evalOperand s val) then
            (.tau, bumpPC { s with mem := srcWriteBytes s.mem a (byteWidth w) ((intBitsAt w (evalOperand s val)).setWidth (8 * byteWidth w)) })
          else fault s
      | none => fault s
  | .term (.br target args) =>
      (.tau, gotoWith s target (args.map (fun vb => (vb.1, evalOperand s vb.2))))
  | .term (.condbr cond t f tArgs fArgs) =>
      if hasBool (evalOperand s cond) then
        if boolValue (evalOperand s cond) then
          (.tau, gotoWith s t (tArgs.map (fun vb => (vb.1, evalOperand s vb.2))))
        else (.tau, gotoWith s f (fArgs.map (fun vb => (vb.1, evalOperand s vb.2))))
      else fault s
  | .term (.switch scrut w _ cases default) =>
      if hasIntWidth w (evalOperand s scrut) then
        if (cases.map Prod.fst).Nodup then
          let key := (intBitsAt w (evalOperand s scrut)).setWidth 64
          match cases.find? (fun row => row.1 == key) with
          | some (_, target) => (.tau, gotoWith s target [])
          | none => (.tau, gotoWith s default [])
        else fault s
      else fault s
  | .term (.call target ret) => (.call target, { s with pc := ret })
  | .term .ret => (.ret, { s with halted := true })
  | .mmioWrite addr val =>
      match addressOperand s addr with
      | some a =>
          if hasIntWidth 64 (evalOperand s val) then
            (.mmio a (intBitsAt 64 (evalOperand s val)) true, bumpPC s)
          else fault s
      | none => fault s
  | .trap => fault s

/-- Fetch at the actual program counter. Missing code faults; terminal states do not step. -/
def nextStep (p : Program) (s : SrcState) : Option (Event × SrcState) :=
  if s.halted then none
  else some (match p.code s.pc with
    | some item => execute item s
    | none => fault s)

/-- Program-indexed source transition; it has no unfetched instruction rule. -/
def SrcStep (p : Program) (s : SrcState) (event : Event) (s' : SrcState) : Prop :=
  nextStep p s = some (event, s')

theorem step_deterministic {p : Program} {s s₁ s₂ : SrcState} {e₁ e₂ : Event}
    (h₁ : SrcStep p s e₁ s₁) (h₂ : SrcStep p s e₂ s₂) : e₁ = e₂ ∧ s₁ = s₂ := by
  change nextStep p s = some (e₁, s₁) at h₁
  change nextStep p s = some (e₂, s₂) at h₂
  have hp := Option.some.inj (h₁.symm.trans h₂)
  exact ⟨congrArg Prod.fst hp, congrArg Prod.snd hp⟩

/-- Every running state has the fetched step or a local fault, never an empty transition domain. -/
theorem running_has_step (p : Program) (s : SrcState) (hrun : s.halted = false) :
    ∃ event s', SrcStep p s event s' := by
  let result := match p.code s.pc with
    | some item => execute item s
    | none => fault s
  refine ⟨result.1, result.2, ?_⟩
  change (if s.halted then none else some result) = some (result.1, result.2)
  simp [hrun]

theorem halted_no_step {p : Program} {s s' : SrcState} {event : Event}
    (hh : s.halted = true) : ¬ SrcStep p s event s' := by
  simp [SrcStep, nextStep, hh]

theorem ret_step {p : Program} {s : SrcState}
    (hrun : s.halted = false) (hfetch : p.code s.pc = some (.term .ret)) :
    SrcStep p s .ret { s with halted := true } := by
  simp [SrcStep, nextStep, hrun, hfetch, execute]

theorem trap_step {p : Program} {s : SrcState}
    (hrun : s.halted = false) (hfetch : p.code s.pc = some .trap) :
    SrcStep p s .trap { s with halted := true } := by
  simp [SrcStep, nextStep, hrun, hfetch, execute, fault]

theorem missing_code_traps {p : Program} {s : SrcState}
    (hrun : s.halted = false) (hfetch : p.code s.pc = none) :
    SrcStep p s .trap { s with halted := true } := by
  simp [SrcStep, nextStep, hrun, hfetch, fault]

theorem ret_cannot_trap {p : Program} {s s' : SrcState}
    (hrun : s.halted = false) (hfetch : p.code s.pc = some (.term .ret)) :
    ¬ SrcStep p s .trap s' := by
  intro h
  have he := (step_deterministic (ret_step hrun hfetch) h).1
  cases he

/-- Operand and fault guards must be discharged for the fetched binary operation. -/
theorem bin_result {p : Program} {s : SrcState} {dst : VName} {op : BinOp}
    {w : Nat} {hw : w ≤ 64} {a b : SOperand}
    (hrun : s.halted = false)
    (hfetch : p.code s.pc = some (.instr (.bin dst op w hw a b)))
    (hargs : (hasIntWidth w (evalOperand s a) && hasIntWidth w (evalOperand s b)) = true)
    (hdiv : divisionFault op w (intBitsAt w (evalOperand s a))
      (intBitsAt w (evalOperand s b)) = false) :
    SrcStep p s .tau (setEnv (bumpPC s) dst
      (.int w hw (evalBin op w (intBitsAt w (evalOperand s a))
        (intBitsAt w (evalOperand s b))))) := by
  simp only [SrcStep, nextStep, hrun, hfetch, execute, hargs, hdiv,
    Bool.false_eq_true, ↓reduceIte]

theorem condbr_disjoint {s cond}
    (htrue : boolValue (evalOperand s cond) = true)
    (hfalse : boolValue (evalOperand s cond) = false) : False := by
  rw [htrue] at hfalse
  cases hfalse

theorem cmp3_payload {p : Program} {s : SrcState} {dst : VName} {signed : Bool}
    {w : Nat} {hw : w ≤ 64} {a b : SOperand}
    (hrun : s.halted = false)
    (hfetch : p.code s.pc = some (.instr (.cmp3 dst signed w hw a b)))
    (hargs : (hasIntWidth w (evalOperand s a) && hasIntWidth w (evalOperand s b)) = true) :
    SrcStep p s .tau (setEnv (bumpPC s) dst (.int 8 (by omega)
      (cmpSpec signed w (intBitsAt w (evalOperand s a))
        (intBitsAt w (evalOperand s b))).toI8)) := by
  simp [SrcStep, nextStep, hrun, hfetch, execute, hargs]

/-! ## A concrete end-to-end witness the certs reuse: signed 3-way compare at w=8.

    Ties `cmpSpec` to the i8 SETcc/CMOV shape via bv_decide-grade reasoning (here the
    pure case analysis the narrow-width cert uses). Proven, no sorry. -/
theorem cmp3_i8_witness (a b : BitVec 8) :
    (cmpSpec true 8 a b).toI8
      = (if BitVec.slt b a then 1 else if BitVec.slt a b then (-1 : BitVec 8) else 0) :=
  cmpSpec_toI8_signed8 a b

end Source
end Trust
