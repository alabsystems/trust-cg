/-
  A64.Machine — an A64 machine state and instruction semantics for the integer subset
  (start of ledger X-LEAN-P1).

  Author: Andrew Yates
  Copyright 2026 Andrew Yates | License: Apache-2.0

  ─────────────────────────────────────────────────────────────────────────────────────────────
  WHAT THIS IS.  `MachState` holds X0..X30, SP, PC, NZCV and a byte-addressed memory.  Register
  number 31 reads as zero and discards writes (XZR/WZR) except in the operand positions the Arm
  ARM gives to SP (`readXSP` / `writeXSP`).  A 32-bit (`sf = 0`) form computes on the low 32
  bits and zero-extends its result into the X register.

  `exec : Instr → MachState → Option MachState` transcribes the Arm ARM (DDI 0487) decode and
  operation pseudocode of every `Trust.A64.Instr` class, with these boundaries:

    * `none` means "outside the model": an invalid instruction, a SIMD&FP (`V = 1`) access, an
      exception-generating instruction (BRK), or an encoding the Arm ARM makes CONSTRAINED
      UNPREDICTABLE (a write-back whose base is also a transfer register, LDP with `Rt = Rt2`).
      Nothing returns an arbitrary choice for such an encoding.
    * Memory is a single flat little-endian byte map with no alignment faults, no translation,
      no other observers and no ordering: barriers are no-ops on this single-threaded state.
    * `step` fetches the 4-byte word at PC from the same memory, decodes it with
      `Trust.A64.decode` and executes it.

  The flag semantics is the Arm ARM `AddWithCarry` (`C = UInt(result) != unsigned_sum`,
  `V = SInt(result) != signed_sum`) and `ConditionHolds`; the condition certificates below prove
  that every condition trust-cg's `AArch64CC::from_intcc` selects after `CMP a, b` is exactly
  the integer comparison it lowers, for every width `w ≥ 1`.  In particular `SUBS`'s C flag is
  NOT-borrow (`C = 1 ↔ b ≤ a` unsigned), the opposite of x86's CF.

  The condition field proof connects to the Rust encoder and layout passes through the
  Trust-compiled toggle and complementability functions. A forward simulation from trust-cg
  source or IR semantics to `step` remains the X-LEAN-P1 capstone. No `sorry`, no `axiom`.
  ─────────────────────────────────────────────────────────────────────────────────────────────
-/
import Trust.A64.Encoding
import Trust.A64.Bitmask
import Trust.A64.ConditionBits
import Trust.A64.ConditionalTrap

namespace Trust
namespace A64

/-! ## State -/

/-- The NZCV condition flags. -/
structure NZCV where
  n : Bool
  z : Bool
  c : Bool
  v : Bool
  deriving DecidableEq, Repr

/-- A64 machine state for the integer subset. -/
structure MachState where
  /-- X0..X30. -/
  x : Fin 31 → BitVec 64
  sp : BitVec 64
  pc : BitVec 64
  nzcv : NZCV
  /-- Byte-addressed little-endian memory. -/
  mem : BitVec 64 → BitVec 8

namespace MachState

/-- `X[r]` where register 31 is the zero register. -/
def readX (s : MachState) (r : Reg) : BitVec 64 :=
  if h : r.val < 31 then s.x ⟨r.val, h⟩ else 0

/-- `X[r]` where register 31 is SP. -/
def readXSP (s : MachState) (r : Reg) : BitVec 64 :=
  if h : r.val < 31 then s.x ⟨r.val, h⟩ else s.sp

/-- `X[r] = v` where register 31 is the zero register (the write is discarded). -/
def writeX (s : MachState) (r : Reg) (v : BitVec 64) : MachState :=
  if h : r.val < 31 then { s with x := fun i => if i = ⟨r.val, h⟩ then v else s.x i } else s

/-- `X[r] = v` where register 31 is SP. -/
def writeXSP (s : MachState) (r : Reg) (v : BitVec 64) : MachState :=
  if h : r.val < 31 then { s with x := fun i => if i = ⟨r.val, h⟩ then v else s.x i }
  else { s with sp := v }

/-- Fall through to the next instruction. -/
def advance (s : MachState) : MachState := { s with pc := s.pc + 4 }

/-- Read `k` bytes little-endian at `addr` (wrapping) as a natural number. -/
def readMem (s : MachState) (addr : BitVec 64) : Nat → Nat
  | 0 => 0
  | k + 1 => (s.mem addr).toNat + 256 * s.readMem (addr + 1) k

/-- Write the low `k` bytes of `v` little-endian at `addr` (wrapping). -/
def writeMem (s : MachState) (addr : BitVec 64) (v : Nat) : Nat → MachState
  | 0 => s
  | k + 1 =>
    let s' : MachState :=
      { s with mem := fun a => if a = addr then BitVec.ofNat 8 v else s.mem a }
    s'.writeMem (addr + 1) (v / 256) k

end MachState

/-! ## Arm ARM shared pseudocode -/

/-- `AddWithCarry(x, y, carry_in)` (Arm ARM J1): the result and its NZCV. -/
def addWithCarry {w : Nat} (x y : BitVec w) (cin : Bool) : BitVec w × NZCV :=
  let usum : Nat := x.toNat + y.toNat + cin.toNat
  let ssum : Int := x.toInt + y.toInt + (cin.toNat : Int)
  let result : BitVec w := BitVec.ofNat w usum
  (result, { n := result.msb, z := result == 0#w, c := result.toNat != usum,
             v := result.toInt != ssum })

/-- The reference `ConditionHolds(cond)` pseudocode (Arm ARM J1). -/
private def condHoldsSpec (cond : Fin 16) (f : NZCV) : Bool :=
  let base := match cond.val / 2 with
    | 0 => f.z
    | 1 => f.c
    | 2 => f.n
    | 3 => f.v
    | 4 => f.c && !f.z
    | 5 => f.n == f.v
    | 6 => f.n == f.v && !f.z
    | _ => true
  if cond.val % 2 = 1 && cond.val != 15 then !base else base

/-- `ConditionHolds` reads the condition's bit from the Trust-compiled truth mask. -/
def condHolds (cond : Fin 16) (f : NZCV) : Bool :=
  let mask := trust_cg_a64_cond_truth_mask f.n.toUInt32 f.z.toUInt32 f.c.toUInt32 f.v.toUInt32
  mask.toBitVec.getLsbD cond.val

private theorem condHolds_table_matches :
    ∀ (cond : Fin 16) (n z c v : Bool),
      condHolds cond ⟨n, z, c, v⟩ = condHoldsSpec cond ⟨n, z, c, v⟩ := by
  decide +kernel

theorem condHolds_matches_spec (cond : Fin 16) (f : NZCV) :
    condHolds cond f = condHoldsSpec cond f := by
  cases f with
  | mk n z c v => exact condHolds_table_matches cond n z c v

/-- The register width of `sf`. -/
def datasize (sf : Fin 2) : Nat := if sf.val = 1 then 64 else 32

/-- `ShiftReg` (Arm ARM): LSL, LSR, ASR, ROR by `amount`. -/
def shiftReg {w : Nat} (x : BitVec w) (shift : Fin 4) (amount : Nat) : BitVec w :=
  match shift.val with
  | 0 => x <<< amount
  | 1 => x >>> amount
  | 2 => x.sshiftRight amount
  | _ => x.rotateRight amount

/-- `ExtendReg(reg, exttype, shift, N)` for the 64-bit register value `v`. -/
def extendReg (w : Nat) (v : BitVec 64) (option : Fin 8) (shift : Nat) : BitVec w :=
  let len := Nat.min (8 * 2 ^ (option.val % 4)) (w - shift)
  let low : BitVec len := v.setWidth len
  let ext : BitVec w := if option.val < 4 then low.setWidth w else low.signExtend w
  ext <<< shift

/-- Sign-extend a `k`-bit field to an integer. -/
def sext (k : Nat) (v : Nat) : Int := (BitVec.ofNat k v).toInt

/-- Count the leading zero bits of a `w`-bit value. -/
def clzBits (w v : Nat) : Nat := if v = 0 then w else w - (Nat.log2 v + 1)

/-- `BitReverse` of a `w`-bit value. -/
def bitRev (w v : Nat) : Nat :=
  (List.range w).foldl (fun acc i => acc + (v / 2 ^ i % 2) * 2 ^ (w - 1 - i)) 0

/-- `Poly32Mod2(data, poly)` (Arm ARM) of an `n`-bit `data`, `n > 32`. -/
def poly32Mod2 (n data poly : Nat) : Nat :=
  ((List.range (n - 32)).foldl (fun d k =>
    let i := n - 1 - k
    if d / 2 ^ i % 2 = 1 then d ^^^ (poly * 2 ^ (i - 32)) else d) data) % 2 ^ 32

/-- CRC32 (`castagnoli = false`) or CRC32C of the low `8 << sz` bits of `val` into `acc`. -/
def crc32 (castagnoli : Bool) (sz : Nat) (acc val : Nat) : Nat :=
  let size := 8 * 2 ^ sz
  let poly := if castagnoli then 0x1EDC6F41 else 0x04C11DB7
  let tempacc := bitRev 32 (acc % 2 ^ 32) * 2 ^ size
  let tempval := bitRev size (val % 2 ^ size) * 2 ^ 32
  bitRev 32 (poly32Mod2 (32 + size) (tempacc ^^^ tempval) poly)

/-- Reverse the bytes within each `c`-byte container of a `bytes`-byte value. -/
def revBytes (c bytes v : Nat) : Nat :=
  (List.range bytes).foldl (fun acc i =>
    let container := i / c
    let j := container * c + (c - 1 - i % c)
    acc + (v / 256 ^ i % 256) * 256 ^ j) 0

/-! ## Instruction semantics -/

namespace Exec

open MachState

/-- Add/subtract with an operand already shifted/extended/immediate. -/
def addSub {w : Nat} (op : Fin 2) (x y : BitVec w) : BitVec w × NZCV :=
  if op.val = 0 then addWithCarry x y false else addWithCarry x (~~~y) true

/-- Flags of a logical result (ANDS/BICS): N, Z from the result, C = V = 0. -/
def logicFlags {w : Nat} (r : BitVec w) : NZCV := ⟨r.msb, r == 0#w, false, false⟩

/-- The logical operation of `opc` (AND, ORR, EOR, ANDS). -/
def logicOp {w : Nat} (opc : Fin 4) (x y : BitVec w) : BitVec w :=
  match opc.val with
  | 1 => x ||| y
  | 2 => x ^^^ y
  | _ => x &&& y

/-- Load `bytes` bytes and extend them as `opc` (01 zero-extend, 10 sign-extend to 64,
    11 sign-extend to 32) into a 64-bit register value. -/
def loadValue (bytes : Nat) (opc : Fin 4) (raw : Nat) : BitVec 64 :=
  match opc.val with
  | 2 => (BitVec.ofNat (8 * bytes) raw).signExtend 64
  | 3 => ((BitVec.ofNat (8 * bytes) raw).signExtend 32).setWidth 64
  | _ => BitVec.ofNat 64 raw

/-- A single-register integer load or store at `addr` (`size`/`opc` as in the encoding). -/
def transfer (size opc : Fin 4) (rt : Reg) (addr : BitVec 64) (s : MachState) : MachState :=
  let bytes := 2 ^ size.val
  if opc.val = 0 then s.writeMem addr (s.readX rt).toNat bytes
  else s.writeX rt (loadValue bytes opc (s.readMem addr bytes))

end Exec

open MachState Exec

/-- The operation of a valid instruction (see the module header for `none`). -/
def execValid (i : Instr) (s : MachState) : Option MachState :=
  match i with
  | .addSubShifted sf op S shift rm imm6 rn rd =>
    let w := datasize sf
    let x : BitVec w := (s.readX rn).setWidth w
    let y : BitVec w := shiftReg ((s.readX rm).setWidth w) shift imm6.val
    let r := addSub op x y
    let s := if S.val = 1 then { s with nzcv := r.2 } else s
    some (s.writeX rd (r.1.setWidth 64)).advance
  | .addSubImm sf op S sh imm12 rn rd =>
    let w := datasize sf
    let x : BitVec w := (s.readXSP rn).setWidth w
    let y : BitVec w := BitVec.ofNat w (imm12.val * 2 ^ (12 * sh.val))
    let r := addSub op x y
    if S.val = 1 then some ({ s with nzcv := r.2 }.writeX rd (r.1.setWidth 64)).advance
    else some (s.writeXSP rd (r.1.setWidth 64)).advance
  | .addSubExt sf op S rm option imm3 rn rd =>
    let w := datasize sf
    let x : BitVec w := (s.readXSP rn).setWidth w
    let y : BitVec w := extendReg w (s.readX rm) option imm3.val
    let r := addSub op x y
    if S.val = 1 then some ({ s with nzcv := r.2 }.writeX rd (r.1.setWidth 64)).advance
    else some (s.writeXSP rd (r.1.setWidth 64)).advance
  | .addSubCarry sf op S rm rn rd =>
    let w := datasize sf
    let x : BitVec w := (s.readX rn).setWidth w
    let y : BitVec w := (s.readX rm).setWidth w
    let r := addWithCarry x (if op.val = 0 then y else ~~~y) s.nzcv.c
    let s := if S.val = 1 then { s with nzcv := r.2 } else s
    some (s.writeX rd (r.1.setWidth 64)).advance
  | .logicalShifted sf opc shift n rm imm6 rn rd =>
    let w := datasize sf
    let x : BitVec w := (s.readX rn).setWidth w
    let y0 : BitVec w := shiftReg ((s.readX rm).setWidth w) shift imm6.val
    let y := if n.val = 1 then ~~~y0 else y0
    let r := logicOp opc x y
    let s := if opc.val = 3 then { s with nzcv := logicFlags r } else s
    some (s.writeX rd (r.setWidth 64)).advance
  | .logicalImm sf opc n immr imms rn rd =>
    let w := datasize sf
    match decodeBitMasks n.val imms.val immr.val true w with
    | none => none
    | some (wmask, _) =>
      let x : BitVec w := (s.readX rn).setWidth w
      let r := logicOp opc x (BitVec.ofNat w wmask)
      if opc.val = 3 then some ({ s with nzcv := logicFlags r }.writeX rd (r.setWidth 64)).advance
      else some (s.writeXSP rd (r.setWidth 64)).advance
  | .moveWide sf opc hw imm16 rd =>
    let w := datasize sf
    let pos := 16 * hw.val
    let imm : BitVec w := BitVec.ofNat w (imm16.val * 2 ^ pos)
    let r : BitVec w :=
      match opc.val with
      | 0 => ~~~imm
      | 3 => ((s.readX rd).setWidth w &&& ~~~(BitVec.ofNat w (0xFFFF * 2 ^ pos))) ||| imm
      | _ => imm
    some (s.writeX rd (r.setWidth 64)).advance
  | .bitfield sf opc n immr imms rn rd =>
    let w := datasize sf
    match decodeBitMasks n.val imms.val immr.val false w with
    | none => none
    | some (wm, tm) =>
      let wmask := BitVec.ofNat w wm
      let tmask := BitVec.ofNat w tm
      let src : BitVec w := (s.readX rn).setWidth w
      let dst : BitVec w := (s.readX rd).setWidth w
      let rot := src.rotateRight immr.val
      let r : BitVec w :=
        match opc.val with
        | 0 =>
          let bot := rot &&& wmask
          let top : BitVec w := if src.getLsbD imms.val then BitVec.allOnes w else 0#w
          (top &&& ~~~tmask) ||| (bot &&& tmask)
        | 1 =>
          let bot := (dst &&& ~~~wmask) ||| (rot &&& wmask)
          (dst &&& ~~~tmask) ||| (bot &&& tmask)
        | _ => (rot &&& wmask) &&& tmask
      some (s.writeX rd (r.setWidth 64)).advance
  | .extract sf _ rm imms rn rd =>
    let w := datasize sf
    let hiPart := ((s.readX rn).setWidth w).toNat
    let loPart := ((s.readX rm).setWidth w).toNat
    let r : BitVec w := BitVec.ofNat w ((hiPart * 2 ^ w + loPart) / 2 ^ imms.val)
    some (s.writeX rd (r.setWidth 64)).advance
  | .condSelect sf op rm cond o2 rn rd =>
    let w := datasize sf
    let x : BitVec w := (s.readX rn).setWidth w
    let y0 : BitVec w := (s.readX rm).setWidth w
    let y := if op.val = 1 then ~~~y0 else y0
    let y := if o2.val = 1 then y + 1 else y
    let r := if condHolds cond s.nzcv then x else y
    some (s.writeX rd (r.setWidth 64)).advance
  | .dataProc2 sf rm opcode rn rd =>
    if 16 ≤ opcode.val then
      -- CRC32/CRC32C: the accumulator is Wn, the result Wd (zero-extended).
      let r := crc32 (opcode.val / 4 % 2 == 1) (opcode.val % 4) (s.readX rn).toNat (s.readX rm).toNat
      some (s.writeX rd (BitVec.ofNat 64 r)).advance
    else
    let w := datasize sf
    let x : BitVec w := (s.readX rn).setWidth w
    let y : BitVec w := (s.readX rm).setWidth w
    let r : BitVec w :=
      match opcode.val with
      | 2 => BitVec.ofNat w (x.toNat / y.toNat)
      | 3 => BitVec.ofInt w (x.toInt.tdiv y.toInt)
      | 8 => x <<< (y.toNat % w)
      | 9 => x >>> (y.toNat % w)
      | 10 => x.sshiftRight (y.toNat % w)
      | _ => x.rotateRight (y.toNat % w)
    some (s.writeX rd (r.setWidth 64)).advance
  | .dataProc1 sf opcode rn rd =>
    let w := datasize sf
    let x : BitVec w := (s.readX rn).setWidth w
    let r : BitVec w :=
      match opcode.val with
      | 0 => x.reverse
      | 1 => BitVec.ofNat w (revBytes 2 (w / 8) x.toNat)
      | 2 => BitVec.ofNat w (revBytes 4 (w / 8) x.toNat)
      | 3 => BitVec.ofNat w (revBytes 8 (w / 8) x.toNat)
      | 4 => BitVec.ofNat w (clzBits w x.toNat)
      | _ =>
        -- CLS(x) = CLZ(x<w-1:1> EOR x<w-2:0>) over w-1 bits.
        BitVec.ofNat w (clzBits (w - 1) (((x >>> 1) ^^^ x).toNat % 2 ^ (w - 1)))
    some (s.writeX rd (r.setWidth 64)).advance
  | .dataProc3 sf op31 rm o0 ra rn rd =>
    match op31.val with
    | 0 =>
      let w := datasize sf
      let x : BitVec w := (s.readX rn).setWidth w
      let y : BitVec w := (s.readX rm).setWidth w
      let a : BitVec w := (s.readX ra).setWidth w
      let r := if o0.val = 0 then a + x * y else a - x * y
      some (s.writeX rd (r.setWidth 64)).advance
    | 1 | 5 =>
      let ext (v : BitVec 64) : Int :=
        if op31.val = 1 then (v.setWidth 32).toInt else ((v.setWidth 32).toNat : Int)
      let prod := ext (s.readX rn) * ext (s.readX rm)
      let a := (s.readX ra).toInt
      let r := BitVec.ofInt 64 (if o0.val = 0 then a + prod else a - prod)
      some (s.writeX rd r).advance
    | 2 =>
      let r := BitVec.ofInt 64 ((s.readX rn).toInt * (s.readX rm).toInt / 2 ^ 64)
      some (s.writeX rd r).advance
    | _ =>
      let r := BitVec.ofNat 64 ((s.readX rn).toNat * (s.readX rm).toNat / 2 ^ 64)
      some (s.writeX rd r).advance
  | .branchImm op imm26 =>
    let target := s.pc + BitVec.ofInt 64 (4 * sext 26 imm26.val)
    let s := if op.val = 1 then s.writeX 30 (s.pc + 4) else s
    some { s with pc := target }
  | .condBranch imm19 cond =>
    if condHolds cond s.nzcv then some { s with pc := s.pc + BitVec.ofInt 64 (4 * sext 19 imm19.val) }
    else some s.advance
  | .compareBranch sf op imm19 rt =>
    let w := datasize sf
    let isZero := (s.readX rt).setWidth w == 0#w
    if isZero == (op.val = 0) then
      some { s with pc := s.pc + BitVec.ofInt 64 (4 * sext 19 imm19.val) }
    else some s.advance
  | .testBranch b5 op b40 imm14 rt =>
    let bit := (s.readX rt).getLsbD (32 * b5.val + b40.val)
    if bit == (op.val = 1) then
      some { s with pc := s.pc + BitVec.ofInt 64 (4 * sext 14 imm14.val) }
    else some s.advance
  | .branchReg opc rn =>
    let target := s.readX rn
    let s := if opc.val = 1 then s.writeX 30 (s.pc + 4) else s
    some { s with pc := target }
  | .pcRel op immlo immhi rd =>
    let imm := sext 21 (immhi.val * 4 + immlo.val)
    let base := if op.val = 1 then s.pc &&& ~~~(0xFFF#64) else s.pc
    let offset := if op.val = 1 then imm * 4096 else imm
    some (s.writeX rd (base + BitVec.ofInt 64 offset)).advance
  | .brk _ => none
  | .nop => some s.advance
  | .barrier _ _ => some s.advance
  | .loadLiteral opc v imm19 rt =>
    if v.val = 1 then none else
    let addr := s.pc + BitVec.ofInt 64 (4 * sext 19 imm19.val)
    match opc.val with
    | 0 => some (transfer 2 1 rt addr s).advance
    | 1 => some (transfer 3 1 rt addr s).advance
    | _ => some (transfer 2 2 rt addr s).advance
  | .loadStoreUImm size v opc imm12 rn rt =>
    if v.val = 1 then none else
    let addr := s.readXSP rn + BitVec.ofNat 64 (imm12.val * 2 ^ size.val)
    some (transfer size opc rt addr s).advance
  | .loadStoreImm9 size v opc imm9 idx rn rt =>
    if v.val = 1 then none else
    let wback := idx.val != 0
    if wback && rn.val == rt.val && rn.val != 31 then none else
    let base := s.readXSP rn
    let offset := BitVec.ofInt 64 (sext 9 imm9.val)
    let addr := if idx.val = 1 then base else base + offset
    let s := transfer size opc rt addr s
    let s := if wback then s.writeXSP rn (base + offset) else s
    some s.advance
  | .loadStoreRegOff size v opc rm option sbit rn rt =>
    if v.val = 1 then none else
    let addr := s.readXSP rn + extendReg 64 (s.readX rm) option (if sbit.val = 1 then size.val else 0)
    some (transfer size opc rt addr s).advance
  | .loadStorePair opc v mode l imm7 rt2 rn rt =>
    if v.val = 1 then none else
    let wback := mode.val = 1 || mode.val = 3
    if l.val = 1 && rt.val == rt2.val then none else
    if wback && (rn.val == rt.val || rn.val == rt2.val) && rn.val != 31 then none else
    let size : Fin 4 := if opc.val = 2 then 3 else 2
    let bytes : Nat := 2 ^ size.val
    let ext : Fin 4 := if opc.val = 1 then 2 else 1
    let base := s.readXSP rn
    let offset := BitVec.ofInt 64 (sext 7 imm7.val * (bytes : Int))
    let addr := if mode.val = 1 then base else base + offset
    let s :=
      if l.val = 1 then
        let v1 := loadValue bytes ext (s.readMem addr bytes)
        let v2 := loadValue bytes ext (s.readMem (addr + BitVec.ofNat 64 bytes) bytes)
        (s.writeX rt v1).writeX rt2 v2
      else
        let d1 := (s.readX rt).toNat
        let d2 := (s.readX rt2).toNat
        (s.writeMem addr d1 bytes).writeMem (addr + BitVec.ofNat 64 bytes) d2 bytes
    let s := if wback then s.writeXSP rn (base + offset) else s
    some s.advance

/-- Execute an instruction: `none` for an invalid one (see `execValid` for the rest). -/
def exec (i : Instr) (s : MachState) : Option MachState :=
  if i.valid then execValid i s else none

/-- Fetch the word at PC, decode it with the instruction-word model, execute it. -/
def step (s : MachState) : Option MachState :=
  match decodeNat (s.readMem s.pc 4) with
  | some i => exec i s
  | none => none

/-! ## Condition certificates: CMP + ConditionHolds = the integer comparison -/

/-- The flags `CMP a, b` (`SUBS ZR, a, b`) writes: `AddWithCarry(a, NOT b, 1)`. -/
def cmpFlags {w : Nat} (a b : BitVec w) : NZCV := (addWithCarry a (~~~b) true).2

/-- The unsigned sum of `a + NOT b + 1`, reduced modulo `P = 2^w`. -/
theorem sub_usum_mod {P a b : Nat} (ha : a < P) (hb : b < P) :
    (a + (P - 1 - b) + 1) % P = if b ≤ a then a - b else a + P - b := by
  split
  · have : a + (P - 1 - b) + 1 = (a - b) + P := by omega
    rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  · rw [Nat.mod_eq_of_lt (by omega)]; omega

/-- The value `CMP`/`SUBS` computes is `a - b`. -/
theorem cmp_result {w : Nat} (a b : BitVec w) : (addWithCarry a (~~~b) true).1 = a - b := by
  have hP := Nat.two_pow_pos w
  have ha := a.isLt
  have hb := b.isLt
  simp only [addWithCarry, BitVec.toNat_not, Bool.toNat_true]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, sub_usum_mod ha hb, BitVec.toNat_sub]
  split
  · rw [show 2 ^ w - b.toNat + a.toNat = (a.toNat - b.toNat) + 2 ^ w by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  · rw [Nat.mod_eq_of_lt (by omega)]; omega

/-- **Z after CMP**: set exactly when the operands are equal. -/
theorem cmp_z {w : Nat} (a b : BitVec w) : (cmpFlags a b).z = decide (a = b) := by
  have hP := Nat.two_pow_pos w
  have ha := a.isLt
  have hb := b.isLt
  simp only [cmpFlags, addWithCarry, BitVec.toNat_not, Bool.toNat_true]
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_eq, BitVec.toNat_eq, BitVec.toNat_eq,
    BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.zero_mod, sub_usum_mod ha hb]
  generalize a.toNat = A at *
  generalize b.toNat = B at *
  generalize 2 ^ w = P at *
  split <;> omega

/-- **C after CMP is NOT-borrow**: set exactly when `b ≤ a` unsigned.  (x86's CF after
    `CMP a, b` is the borrow `a < b`, the negation.) -/
theorem cmp_c {w : Nat} (a b : BitVec w) : (cmpFlags a b).c = decide (b.toNat ≤ a.toNat) := by
  have hP := Nat.two_pow_pos w
  have ha := a.isLt
  have hb := b.isLt
  simp only [cmpFlags, addWithCarry, BitVec.toNat_ofNat, BitVec.toNat_not, Bool.toNat_true]
  rw [sub_usum_mod ha hb]
  generalize a.toNat = A at *
  generalize b.toNat = B at *
  generalize 2 ^ w = P at *
  rw [Bool.eq_iff_iff, bne_iff_ne, decide_eq_true_eq]
  split <;> omega

/-- **N after CMP** is the sign bit of `a - b`. -/
theorem cmp_n {w : Nat} (a b : BitVec w) : (cmpFlags a b).n = (a - b).msb := by
  simp only [cmpFlags]
  rw [← cmp_result a b]
  rfl

/-- **V after CMP** is signed overflow of `a - b`. -/
theorem cmp_v {w : Nat} (hw : 0 < w) (a b : BitVec w) :
    (cmpFlags a b).v = decide ((a - b).toInt ≠ a.toInt - b.toInt) := by
  have hP := Nat.two_pow_pos w
  have hH : 2 ^ w = 2 * 2 ^ (w - 1) := by
    rw [← Nat.pow_succ']; congr 1; omega
  have ha := a.isLt
  have hb := b.isLt
  rw [← cmp_result a b]
  simp only [cmpFlags, addWithCarry, BitVec.toNat_not, Bool.toNat_true,
    BitVec.toInt_eq_toNat_cond, BitVec.toNat_ofNat]
  rw [sub_usum_mod ha hb]
  rw [hH] at ha hb ⊢
  repeat' split
  all_goals (rw [Bool.eq_iff_iff]; simp only [decide_eq_true_eq, bne_iff_ne, ne_eq]; omega)

/-- **GE after CMP**: `N = V` exactly when `b ≤ a` signed. -/
theorem cmp_ge {w : Nat} (hw : 0 < w) (a b : BitVec w) :
    ((cmpFlags a b).n = (cmpFlags a b).v) ↔ b.toInt ≤ a.toInt := by
  have hP := Nat.two_pow_pos w
  have hH : 2 ^ w = 2 * 2 ^ (w - 1) := by
    rw [← Nat.pow_succ']; congr 1; omega
  have ha := a.isLt
  have hb := b.isLt
  simp only [cmpFlags, addWithCarry, BitVec.toNat_not, Bool.toNat_true, BitVec.msb_eq_decide,
    BitVec.toInt_eq_toNat_cond, BitVec.toNat_ofNat]
  rw [sub_usum_mod ha hb]
  rw [hH] at ha hb ⊢
  repeat' split
  all_goals (rw [Bool.eq_iff_iff]; simp only [decide_eq_true_eq, bne_iff_ne, ne_eq]; omega)

/-- The signed-integer value of a bit vector is injective. -/
theorem toInt_eq_iff {w : Nat} (a b : BitVec w) : a.toInt = b.toInt ↔ a = b :=
  BitVec.toInt_inj

/-- trust-cg's integer comparison predicates (`trust_ir::IntCC`). -/
inductive IntCC where
  | eq | ne | slt | sge | sgt | sle | ult | uge | ugt | ule
  deriving DecidableEq, Repr

/-- The condition trust-cg's `AArch64CC::from_intcc` selects for each predicate
    (`crates/trust-cg-lower/src/isel.rs`), as its 4-bit encoding. -/
def IntCC.cond : IntCC → Fin 16
  | .eq => 0     -- EQ
  | .ne => 1     -- NE
  | .slt => 11   -- LT
  | .sge => 10   -- GE
  | .sgt => 12   -- GT
  | .sle => 13   -- LE
  | .ult => 3    -- LO (CC)
  | .uge => 2    -- HS (CS)
  | .ugt => 8    -- HI
  | .ule => 9    -- LS

/-- The comparison a predicate denotes on `w`-bit operands. -/
def IntCC.eval {w : Nat} : IntCC → BitVec w → BitVec w → Bool
  | .eq, a, b => decide (a = b)
  | .ne, a, b => decide (a ≠ b)
  | .slt, a, b => decide (a.toInt < b.toInt)
  | .sge, a, b => decide (b.toInt ≤ a.toInt)
  | .sgt, a, b => decide (b.toInt < a.toInt)
  | .sle, a, b => decide (a.toInt ≤ b.toInt)
  | .ult, a, b => decide (a.toNat < b.toNat)
  | .uge, a, b => decide (b.toNat ≤ a.toNat)
  | .ugt, a, b => decide (b.toNat < a.toNat)
  | .ule, a, b => decide (a.toNat ≤ b.toNat)

/-- The flag expression `ConditionHolds` reads for each condition trust-cg emits. -/
theorem condHolds_eq (f : NZCV) : condHolds 0 f = f.z := condHolds_matches_spec 0 f
theorem condHolds_ne (f : NZCV) : condHolds 1 f = !f.z := condHolds_matches_spec 1 f
theorem condHolds_hs (f : NZCV) : condHolds 2 f = f.c := condHolds_matches_spec 2 f
theorem condHolds_lo (f : NZCV) : condHolds 3 f = !f.c := condHolds_matches_spec 3 f
theorem condHolds_hi (f : NZCV) : condHolds 8 f = (f.c && !f.z) := condHolds_matches_spec 8 f
theorem condHolds_ls (f : NZCV) : condHolds 9 f = !(f.c && !f.z) := condHolds_matches_spec 9 f
theorem condHolds_mi (f : NZCV) : condHolds 4 f = f.n := condHolds_matches_spec 4 f
theorem condHolds_vs (f : NZCV) : condHolds 6 f = f.v := condHolds_matches_spec 6 f
theorem condHolds_ge (f : NZCV) : condHolds 10 f = (f.n == f.v) := condHolds_matches_spec 10 f
theorem condHolds_lt (f : NZCV) : condHolds 11 f = !(f.n == f.v) := condHolds_matches_spec 11 f
theorem condHolds_gt (f : NZCV) :
    condHolds 12 f = (f.n == f.v && !f.z) := condHolds_matches_spec 12 f
theorem condHolds_le (f : NZCV) :
    condHolds 13 f = !(f.n == f.v && !f.z) := condHolds_matches_spec 13 f

/-- **The condition certificate.**  After `CMP a, b` at any width `w ≥ 1`, the Arm ARM
    `ConditionHolds` of the condition trust-cg selects for an integer predicate is exactly that
    predicate. -/
theorem cmp_condition_cert {w : Nat} (hw : 0 < w) (p : IntCC) (a b : BitVec w) :
    condHolds p.cond (cmpFlags a b) = p.eval a b := by
  have hz := cmp_z a b
  have hc := cmp_c a b
  have hge := cmp_ge hw a b
  have hnat : a = b ↔ a.toNat = b.toNat := BitVec.toNat_eq
  have hint : a = b ↔ a.toInt = b.toInt := (toInt_eq_iff a b).symm
  cases p
  · rw [IntCC.cond, condHolds_eq, hz, IntCC.eval]
  · rw [IntCC.cond, condHolds_ne, hz, IntCC.eval, decide_not]
  · rw [IntCC.cond, condHolds_lt, IntCC.eval, Bool.eq_iff_iff]
    simp only [Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq, decide_eq_true_eq]
    rw [hge]; omega
  · rw [IntCC.cond, condHolds_ge, IntCC.eval, Bool.eq_iff_iff]
    simp only [beq_iff_eq, decide_eq_true_eq]
    exact hge
  · rw [IntCC.cond, condHolds_gt, IntCC.eval, Bool.eq_iff_iff]
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', decide_eq_true_eq, hz,
      decide_eq_false_iff_not, hint]
    rw [hge]; omega
  · rw [IntCC.cond, condHolds_le, IntCC.eval, Bool.eq_iff_iff]
    simp only [Bool.not_eq_true', Bool.and_eq_false_iff, beq_eq_false_iff_ne, ne_eq,
      Bool.not_eq_false', hz, decide_eq_true_eq, hint]
    rw [hge]; omega
  · rw [IntCC.cond, condHolds_lo, hc, IntCC.eval, Bool.eq_iff_iff]
    simp only [Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq]
    omega
  · rw [IntCC.cond, condHolds_hs, hc, IntCC.eval]
  · rw [IntCC.cond, condHolds_hi, hc, hz, IntCC.eval, Bool.eq_iff_iff]
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not,
      hnat]
    omega
  · rw [IntCC.cond, condHolds_ls, hc, hz, IntCC.eval, Bool.eq_iff_iff]
    simp only [Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not,
      Bool.not_eq_false', decide_eq_true_eq, hnat]
    omega

/-- A condition number as a 4-bit field. -/
def fin4 (c : Nat) : Fin 16 := ⟨c % 16, Nat.mod_lt _ (by decide)⟩

/-- `CSET` uses `invert(cond)`, the condition with bit 0 flipped: for every condition except
    AL/NV it is the logical complement. -/
theorem condHolds_invert :
    ∀ c, c < 14 → ∀ n z cf v : Bool,
      condHolds (fin4 (c ^^^ 1)) ⟨n, z, cf, v⟩ = !condHolds (fin4 c) ⟨n, z, cf, v⟩ := by
  decide +kernel

theorem condToggle_toNat : ∀ cc : Fin 16,
    (trust_cg_a64_cond_toggle (UInt32.ofNat cc.val)).toNat = cc.val ^^^ 1 := by
  decide +kernel

theorem condComplementable_iff : ∀ cc : Fin 16,
    (trust_cg_a64_cond_complementable (UInt32.ofNat cc.val) = 1) ↔ cc.val < 14 := by
  decide +kernel

/-- The two condition encodings without a complement always take their edge. -/
theorem condHolds_unconditional :
    ∀ cc : Fin 16, trust_cg_a64_cond_complementable (UInt32.ofNat cc.val) ≠ 1 →
      ∀ n z c v : Bool, condHolds cc ⟨n, z, c, v⟩ = true := by
  decide +kernel

/-- The exact encoding toggle negates the condition when a logical complement exists. -/
theorem condHolds_compiled_invert (cc : Fin 16) (f : NZCV)
    (complementable : trust_cg_a64_cond_complementable (UInt32.ofNat cc.val) = 1) :
    condHolds (fin4 (trust_cg_a64_cond_toggle (UInt32.ofNat cc.val)).toNat) f = !condHolds cc f := by
  have hc := (condComplementable_iff cc).mp complementable
  have hfin : fin4 cc.val = cc := Fin.ext (Nat.mod_eq_of_lt cc.isLt)
  rw [condToggle_toNat]
  cases f with
  | mk n z c v => simpa only [hfin] using condHolds_invert cc.val hc n z c v

/-- Swapping branch and fallthrough destinations together with the condition preserves the edge. -/
theorem condHolds_swap_edges {α : Type} (cc : Fin 16) (f : NZCV) (taken fallthrough : α)
    (complementable : trust_cg_a64_cond_complementable (UInt32.ofNat cc.val) = 1) :
    (if condHolds cc f then taken else fallthrough) =
      (if condHolds (fin4 (trust_cg_a64_cond_toggle (UInt32.ofNat cc.val)).toNat) f
        then fallthrough else taken) := by
  rw [condHolds_compiled_invert cc f complementable]
  cases condHolds cc f <;> rfl

/-- A lowered integer comparison selects the same destination after the layout edge swap. -/
theorem cmp_swap_edges {α : Type} {w : Nat} (hw : 0 < w)
    (p : IntCC) (a b : BitVec w) (taken fallthrough : α) :
    (if p.eval a b then taken else fallthrough) =
      (if condHolds (fin4 (trust_cg_a64_cond_toggle (UInt32.ofNat p.cond.val)).toNat) (cmpFlags a b)
        then fallthrough else taken) := by
  rw [← cmp_condition_cert hw p a b]
  exact condHolds_swap_edges p.cond (cmpFlags a b) taken fallthrough (by cases p <;> decide)

/-- B.HS after CMP at 64 bits takes the exit opposite to the unsigned continuation. -/
theorem cmp64_bhs_exit (counter bound : UInt64) :
    condHolds 2 (cmpFlags counter.toBitVec bound.toBitVec) =
      !(decide (counter < bound) : Bool) := by
  have hs := cmp_condition_cert (by decide : 0 < 64) .uge counter.toBitVec bound.toBitVec
  change condHolds 2 (cmpFlags counter.toBitVec bound.toBitVec) =
    decide (bound.toNat ≤ counter.toNat) at hs
  rw [hs, Bool.eq_iff_iff]
  simp only [decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not,
    UInt64.lt_iff_toNat_lt]
  exact Nat.not_lt.symm

/-- At a matched finite header visit, CMP64 and B.HS select the source trap suffix.
    The return events are observations of corresponding calls on the exit continuation. -/
theorem cmp64_bhs_trap_after_matched_steps
    (source machine sourceIncrement machineIncrement sourceBound machineBound : UInt64)
    (steps : Nat) (sourceReturned machineReturned : Bool)
    (entry : source = machine) (increment : sourceIncrement = machineIncrement)
    (bound : sourceBound = machineBound) (returnMatches : sourceReturned = machineReturned) :
    (if (decide (trust_cg_a64_trap_source_counter_after source sourceIncrement steps <
      sourceBound) : Bool) then false else sourceReturned) =
      trust_cg_a64_trap_after_return
        (condHolds 2 (cmpFlags
          (trust_cg_a64_trap_machine_counter_after machine machineIncrement steps).toBitVec
          machineBound.toBitVec)) machineReturned := by
  rw [cmp64_bhs_exit]
  exact trust_cg_a64_trap_after_matched_steps source machine sourceIncrement machineIncrement
    sourceBound machineBound steps sourceReturned machineReturned entry increment bound returnMatches

/-! ## Alias semantics -/

@[simp] theorem MachState.readX_zr (s : MachState) : s.readX 31 = 0 := rfl
@[simp] theorem MachState.writeX_zr (s : MachState) (v : BitVec 64) : s.writeX 31 v = s := rfl

/-- `CMP Xn|Wn, Xm|Wm` (`SUBS ZR, Rn, Rm`) writes exactly the `cmpFlags` of its operands at the
    instruction's width, leaves every register unchanged, and falls through. -/
theorem exec_cmp (sf : Fin 2) (rn rm : Reg) (s : MachState) :
    exec (.addSubShifted sf 1 1 0 rm 0 rn 31) s =
      some { s with
        nzcv := cmpFlags ((s.readX rn).setWidth (datasize sf))
                  ((s.readX rm).setWidth (datasize sf)),
        pc := s.pc + 4 } := by
  have hv : (Instr.addSubShifted sf 1 1 0 rm 0 rn 31).valid = true := by
    simp only [Instr.valid]; decide +revert
  simp only [exec, hv, if_true, execValid, addSub, cmpFlags]
  simp [shiftReg, MachState.advance]

/-- `CSET Rd, cond` (`CSINC Rd, ZR, ZR, invert(cond)`) writes 1 when `cond` holds and 0
    otherwise, for every condition trust-cg emits (`cond < 14`), and falls through. -/
theorem exec_cset (sf : Fin 2) (c : Nat) (hc : c < 14) (rd : Reg) (s : MachState) :
    exec (.condSelect sf 0 31 (fin4 (c ^^^ 1)) 1 31 rd) s =
      some (s.writeX rd (if condHolds (fin4 c) s.nzcv then 1#64 else 0#64)).advance := by
  have hinv := condHolds_invert c hc s.nzcv.n s.nzcv.z s.nzcv.c s.nzcv.v
  simp only [exec, Instr.valid, if_true, execValid, MachState.readX_zr]
  rw [show (⟨s.nzcv.n, s.nzcv.z, s.nzcv.c, s.nzcv.v⟩ : NZCV) = s.nzcv from rfl] at hinv
  rw [hinv]
  rcases sf with ⟨_ | _ | _, hsf⟩
  · cases condHolds (fin4 c) s.nzcv <;> rfl
  · cases condHolds (fin4 c) s.nzcv <;> rfl
  · omega

/-! ## TST and CMN -/

/-- The flags `TST a, b` (`ANDS ZR, a, b`) writes. -/
def tstFlags {w : Nat} (a b : BitVec w) : NZCV := Exec.logicFlags (a &&& b)

/-- After `TST a, b`: EQ holds exactly when `a AND b = 0`, MI exactly when the result's sign
    bit is set, and C and V are clear (so HS and VS never hold). -/
theorem tst_conditions {w : Nat} (a b : BitVec w) :
    condHolds 0 (tstFlags a b) = decide (a &&& b = 0#w) ∧
    condHolds 1 (tstFlags a b) = !decide (a &&& b = 0#w) ∧
    condHolds 4 (tstFlags a b) = (a &&& b).msb ∧
    condHolds 2 (tstFlags a b) = false ∧ condHolds 6 (tstFlags a b) = false := by
  have hbeq : (a &&& b == 0#w) = decide (a &&& b = 0#w) := by
    rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_eq]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [tstFlags, Exec.logicFlags, condHolds_eq, condHolds_ne, condHolds_hs,
      condHolds_mi, condHolds_vs, hbeq]

/-- The flags `CMN a, b` (`ADDS ZR, a, b`) writes: `AddWithCarry(a, b, 0)`. -/
def cmnFlags {w : Nat} (a b : BitVec w) : NZCV := (addWithCarry a b false).2

/-- **C after CMN** is the unsigned carry out of `a + b`. -/
theorem cmn_c {w : Nat} (a b : BitVec w) :
    (cmnFlags a b).c = decide (2 ^ w ≤ a.toNat + b.toNat) := by
  have ha := a.isLt
  have hb := b.isLt
  simp only [cmnFlags, addWithCarry, BitVec.toNat_ofNat, Bool.toNat_false, Nat.add_zero]
  rw [Bool.eq_iff_iff, bne_iff_ne, decide_eq_true_eq]
  constructor
  · intro h
    rcases Nat.lt_or_ge (a.toNat + b.toNat) (2 ^ w) with hlt | hge
    · exact absurd (Nat.mod_eq_of_lt hlt) h
    · exact hge
  · intro h heq
    have := Nat.mod_lt (a.toNat + b.toNat) (Nat.two_pow_pos w)
    omega

/-- **Z after CMN**: set exactly when `a + b` wraps to zero. -/
theorem cmn_z {w : Nat} (a b : BitVec w) : (cmnFlags a b).z = decide (a + b = 0#w) := by
  simp only [cmnFlags, addWithCarry, Bool.toNat_false, Nat.add_zero]
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_eq]
  constructor <;> intro h <;>
    (apply BitVec.eq_of_toNat_eq; have := congrArg BitVec.toNat h;
     simp only [BitVec.toNat_ofNat, BitVec.toNat_add] at this ⊢; exact this)

/-- `CMP Xn|SP, #imm{, LSL #12}` (`SUBS ZR, Rn|SP, #imm`) writes the `cmpFlags` of the
    register (SP for 31) and the shifted immediate, and changes nothing else but PC. -/
theorem exec_cmp_imm (sf sh : Fin 2) (imm12 : Fin 4096) (rn : Reg) (s : MachState) :
    exec (.addSubImm sf 1 1 sh imm12 rn 31) s =
      some { s with
        nzcv := cmpFlags ((s.readXSP rn).setWidth (datasize sf))
                  (BitVec.ofNat (datasize sf) (imm12.val * 2 ^ (12 * sh.val))),
        pc := s.pc + 4 } := by
  simp only [exec, Instr.valid, if_true, execValid, addSub, cmpFlags]
  simp [MachState.advance]

/-- `TST Xn|Wn, Xm|Wm` (`ANDS ZR, Rn, Rm`) writes exactly the `tstFlags` of its operands. -/
theorem exec_tst (sf : Fin 2) (rn rm : Reg) (s : MachState) :
    exec (.logicalShifted sf 3 0 0 rm 0 rn 31) s =
      some { s with
        nzcv := tstFlags ((s.readX rn).setWidth (datasize sf))
                  ((s.readX rm).setWidth (datasize sf)),
        pc := s.pc + 4 } := by
  have hv : (Instr.logicalShifted sf 3 0 0 rm 0 rn 31).valid = true := by
    simp only [Instr.valid]; decide +revert
  simp only [exec, hv, if_true, execValid, tstFlags]
  simp +decide [shiftReg, Exec.logicOp, MachState.advance]

/-! ## Fetch, decode, execute -/

/-- If the word at PC is the model's encoding of a valid instruction, one machine step
    executes that instruction (`step` decodes with the instruction-word model). -/
theorem step_of_fetch (s : MachState) (i : Instr) (hv : i.valid = true)
    (hfetch : s.readMem s.pc 4 = encodeNat i) : step s = exec i s := by
  simp only [step, hfetch, decodeNat_encodeNat i hv]

end A64
end Trust
