/-
  A64.Corpus — the emitter-facing golden corpus: which A64 instruction each trust-cg AArch64
  emitter opcode shape denotes (ledger X-LEAN-P3).

  Author: Andrew Yates
  Copyright 2026 Andrew Yates | License: Apache-2.0

  ─────────────────────────────────────────────────────────────────────────────────────────────
  A `Golden` is one emitter input — an `AArch64Opcode` variant (`Shape`, named exactly as the
  Rust enum variant) and its `MachOperand` list (`Opnd`) — together with the `Instr` the Lean
  model says that input must encode.  The `Spec` functions below are that statement, one per
  shape, written from the Arm ARM alias definitions (CMP is SUBS with `Rd = 31`, CSET is CSINC
  of the inverted condition, LSL #k is UBFM, MOV is ORR from the zero register or ADD #0 when
  SP is involved, and so on) and from the emitter's documented operand conventions.

  `corpus` enumerates the inputs.  `scripts/GenA64Golden.lean` renders each entry together
  with `encode` of its instruction into `Trust/A64/EncoderGolden.lean`, whose kernel-checked
  theorems re-establish that every rendered line is a `corpus` entry and that every word is the
  model's encoding (and decodes back).  The Rust test
  `crates/trust-cg-codegen/tests/lean_a64_encode_golden_binding.rs` then feeds every line's
  shape and operands to the production `encode_instruction` and to the ENC-5 decode-check.

  Register operands use the hardware numbers the emitter's `PReg` encodes: `x n` is `PReg(n)`,
  `w n` is `PReg(32 + n)`, `sp`/`wsp` are `PReg(31)`/`PReg(63)`, `xzr`/`wzr` are
  `PReg(160)`/`PReg(161)`.  `mem b off` is `MachOperand::MemOp { base: PReg(b), offset }`.
  ─────────────────────────────────────────────────────────────────────────────────────────────
-/
import Trust.A64.Encoding
import Trust.A64.Bitmask

namespace Trust
namespace A64

/-- A `MachOperand` as the golden corpus spells it. -/
inductive Opnd where
  | x (n : Nat)
  | w (n : Nat)
  | sp
  | wsp
  | xzr
  | wzr
  | imm (v : Int)
  | mem (base : Nat) (off : Int)
  /-- Scalar SIMD&FP `S n` (`PReg(128 + n)`) and `D n` (`PReg(96 + n)`). -/
  | s (n : Nat)
  | d (n : Nat)
  deriving DecidableEq, Repr

/-- The emitter opcodes (`trust_cg_ir::AArch64Opcode` variant names) the corpus binds. -/
inductive Shape where
  | AddRR | AddRI | AddRIShift12 | SubRR | SubRI | AddsRR | AddsRI | SubsRR | SubsRI
  | AddRRShift | SubRRShift | AddRRShiftLsr | Neg
  | CmpRR | CmpRI | CMPWrr | CMPXrr | CMPWri | CMPXri
  | MulRR | Madd | Msub | Smull | Umull | Smulh | Umulh | SDiv | UDiv
  | Adc | Sbc | Adcs | Sbcs
  | AndRR | OrrRR | EorRR | BicRR | OrnRR | EorRRShift | EorRRLsl | EorRRLsr
  | AndRI | OrrRI | EorRI | Tst
  | LslRR | LsrRR | AsrRR | LslRI | LsrRI | AsrRI | RorRI | Rbit
  | MovR | MOVWrr | MOVXrr | MovI | Movz | MOVZWi | MOVZXi | Movn | Movk
  | Csel | Csinc | Csinv | Csneg | CSet
  | Ubfm | Sbfm | Bfm | Sxtw | Uxtw | Sxtb | Sxth | Uxtb | Uxth
  | B | Bl | BL | BCond | Bcc | Cbz | Cbnz | Tbz | Tbnz | Br | Blr | BLR | Ret
  | LdrRI | StrRI | LdrbRI | LdrhRI | LdrsbRI | LdrshRI | StrbRI | StrhRI | STRWui | STRXui
  | LdrPreIndex | StrPreIndex | LdrPostIndex | StrPostIndex | LdrLiteral
  | LdpRI | StpRI | StpPreIndex | LdpPostIndex
  | LdrRO | StrRO | LdrbRO | LdrhRO | StrbRO | StrhRO | LdrswRO
  | Adr | Adrp | Brk | Dmb | Dsb | Isb | Nop | AlignNop
  | VolatileLdrRI | VolatileStrRI | VolatileLdrbRI | VolatileLdrhRI | VolatileStrbRI
  | VolatileStrhRI | TailCall | AddPCRel | STRSui | STRDui
  | Crc32B | Crc32H | Crc32W | Crc32X | Crc32Cb | Crc32Ch | Crc32Cw | Crc32Cx
  deriving DecidableEq, Repr

/-- One emitter input and the instruction it denotes. -/
structure Golden where
  shape : Shape
  operands : List Opnd
  instr : Instr
  deriving DecidableEq, Repr

/-! ## Field helpers -/

/-- The low `k` bits of `a` as a `k`-bit field. -/
def fin (k a : Nat) : Fin (2 ^ k) := ⟨a % 2 ^ k, Nat.mod_lt _ (Nat.two_pow_pos k)⟩

/-- A signed value as a `k`-bit two's-complement field. -/
def sfield (k : Nat) (v : Int) : Fin (2 ^ k) := fin k (v % (2 ^ k : Int)).toNat

/-- The 5-bit hardware number of a register operand (SP and the zero registers are 31). -/
def Opnd.hw : Opnd → Fin 32
  | .x n => fin 5 n
  | .w n => fin 5 n
  | .mem b _ => fin 5 b
  | .s n => fin 5 n
  | .d n => fin 5 n
  | _ => 31

/-- `sf` of a register operand: 1 for an X view, 0 for a W view (the emitter's
    `sf_from_operand`). -/
def Opnd.sf : Opnd → Fin 2
  | .w _ | .wsp | .wzr => 0
  | _ => 1

/-- The register is SP (either view). -/
def Opnd.isSp : Opnd → Bool
  | .sp | .wsp => true
  | _ => false

/-- An X (`sf = 1`) or W (`sf = 0`) numbered register. -/
def gpr (sf : Fin 2) (n : Nat) : Opnd := if sf.val = 1 then .x n else .w n

/-- The zero register of a width. -/
def zr (sf : Fin 2) : Opnd := if sf.val = 1 then .xzr else .wzr

/-- The register width in bits. -/
def regBits (sf : Fin 2) : Nat := if sf.val = 1 then 64 else 32

/-- The emitter's `Imm` for a logical immediate: `DecodeBitMasks` of the fields at the
    register width, as the two's-complement `i64` the operand carries. -/
def maskImm (sf : Fin 2) (n immr imms : Nat) : Int :=
  let v := (logicalImmValue n immr imms (regBits sf)).getD 0
  if v ≥ 2 ^ 63 then (v : Int) - 2 ^ 64 else v

/-! ## The emitter-shape specification -/

namespace Spec

/-- `ADD/SUB/ADDS/SUBS Rd, Rn, Rm` (shifted register, LSL #0). -/
def addSubRR (s : Shape) (op S : Fin 2) (d n m : Opnd) : Golden :=
  ⟨s, [d, n, m], .addSubShifted d.sf op S 0 m.hw 0 n.hw d.hw⟩

/-- `ADD/SUB/ADDS/SUBS Rd|SP, Rn|SP, #imm12{, LSL #12}`. -/
def addSubRI (s : Shape) (op S sh : Fin 2) (d n : Opnd) (imm : Nat) : Golden :=
  ⟨s, [d, n, .imm imm], .addSubImm d.sf op S sh (fin 12 imm) n.hw d.hw⟩

/-- `ADD/SUB Rd, Rn, Rm, <shift> #k`. -/
def addSubShift (s : Shape) (op : Fin 2) (shift : Fin 4) (d n m : Opnd) (k : Nat) : Golden :=
  ⟨s, [d, n, m, .imm k], .addSubShifted d.sf op 0 shift m.hw (fin 6 k) n.hw d.hw⟩

/-- `NEG Rd, Rm` = `SUB Rd, ZR, Rm`. -/
def neg (d m : Opnd) : Golden := ⟨.Neg, [d, m], .addSubShifted d.sf 1 0 0 m.hw 0 31 d.hw⟩

/-- `CMP Rn, Rm` = `SUBS ZR, Rn, Rm`. -/
def cmpRR (s : Shape) (n m : Opnd) : Golden :=
  ⟨s, [n, m], .addSubShifted n.sf 1 1 0 m.hw 0 n.hw 31⟩

/-- `CMP Rn|SP, #imm12` = `SUBS ZR, Rn|SP, #imm12`. -/
def cmpRI (s : Shape) (n : Opnd) (imm : Nat) : Golden :=
  ⟨s, [n, .imm imm], .addSubImm n.sf 1 1 0 (fin 12 imm) n.hw 31⟩

/-- `SUBS Xd|XZR, SP, Xm` = `SUBS Xd, SP, Xm, UXTX #0` (extended register). -/
def subsFromSp (d m : Opnd) : Golden :=
  ⟨.SubsRR, [d, .sp, m], .addSubExt 1 1 1 m.hw 3 0 31 d.hw⟩

/-- `MUL Rd, Rn, Rm` = `MADD Rd, Rn, Rm, ZR`. -/
def mul (d n m : Opnd) : Golden := ⟨.MulRR, [d, n, m], .dataProc3 d.sf 0 m.hw 0 31 n.hw d.hw⟩

/-- `MADD` (`o0 = 0`) / `MSUB` (`o0 = 1`) `Rd, Rn, Rm, Ra`. -/
def mulAdd (s : Shape) (o0 : Fin 2) (d n m a : Opnd) : Golden :=
  ⟨s, [d, n, m, a], .dataProc3 d.sf 0 m.hw o0 a.hw n.hw d.hw⟩

/-- `SMULL`/`UMULL Xd, Wn, Wm` (`SMADDL`/`UMADDL` with `Ra = XZR`) and `SMULH`/`UMULH Xd, Xn,
    Xm` (`Ra` field 31). -/
def mulLong (s : Shape) (op31 : Fin 8) (d n m : Opnd) : Golden :=
  ⟨s, [d, n, m], .dataProc3 1 op31 m.hw 0 31 n.hw d.hw⟩

/-- Data-processing (2 source): `UDIV`, `SDIV`, `LSLV`, `LSRV`, `ASRV`. -/
def dp2 (s : Shape) (opcode : Fin 64) (d n m : Opnd) : Golden :=
  ⟨s, [d, n, m], .dataProc2 d.sf m.hw opcode n.hw d.hw⟩

/-- `ADC/ADCS/SBC/SBCS Rd, Rn, Rm`. -/
def carry (s : Shape) (op S : Fin 2) (d n m : Opnd) : Golden :=
  ⟨s, [d, n, m], .addSubCarry d.sf op S m.hw n.hw d.hw⟩

/-- `AND/ORR/EOR/BIC/ORN Rd, Rn, Rm` (shifted register, LSL #0). -/
def logicRR (s : Shape) (opc : Fin 4) (inv : Fin 2) (d n m : Opnd) : Golden :=
  ⟨s, [d, n, m], .logicalShifted d.sf opc 0 inv m.hw 0 n.hw d.hw⟩

/-- `EOR Rd, Rn, Rm, <shift> #k`. -/
def eorShift (s : Shape) (shift : Fin 4) (d n m : Opnd) (k : Nat) : Golden :=
  ⟨s, [d, n, m, .imm k], .logicalShifted d.sf 2 shift 0 m.hw (fin 6 k) n.hw d.hw⟩

/-- `AND/ORR/EOR Rd|SP, Rn, #mask` from the canonical `N:immr:imms` of `mask`. -/
def logicRI (s : Shape) (opc : Fin 4) (d n : Opnd) (bn immr imms : Nat) : Golden :=
  ⟨s, [d, n, .imm (maskImm d.sf bn immr imms)],
    .logicalImm d.sf opc (fin 1 bn) (fin 6 immr) (fin 6 imms) n.hw d.hw⟩

/-- `TST Rn, #mask` = `ANDS ZR, Rn, #mask`. -/
def tstRI (n : Opnd) (bn immr imms : Nat) : Golden :=
  ⟨.Tst, [n, .imm (maskImm n.sf bn immr imms)],
    .logicalImm n.sf 3 (fin 1 bn) (fin 6 immr) (fin 6 imms) n.hw 31⟩

/-- `TST Rn, Rm` = `ANDS ZR, Rn, Rm`. -/
def tstRR (n m : Opnd) : Golden := ⟨.Tst, [n, m], .logicalShifted n.sf 3 0 0 m.hw 0 n.hw 31⟩

/-- `MOV Rd, Rm` = `ORR Rd, ZR, Rm`. -/
def movOrr (sf : Fin 2) (d m : Opnd) : Instr := .logicalShifted sf 1 0 0 m.hw 0 31 d.hw

/-- `MOV` between general registers at width `sf`: `ADD Rd, Rn, #0` when SP is involved,
    otherwise `ORR Rd, ZR, Rm`. -/
def movR (s : Shape) (sf : Fin 2) (d m : Opnd) : Golden :=
  ⟨s, [d, m], if d.isSp || m.isSp then .addSubImm sf 0 0 0 0 m.hw d.hw else movOrr sf d m⟩

/-- `LSL Rd, Rn, #k` = `UBFM Rd, Rn, #(-k MOD size), #(size-1-k)`; `MOV` for `k = 0`. -/
def lslRI (d n : Opnd) (k : Nat) : Golden :=
  let size := regBits d.sf
  ⟨.LslRI, [d, n, .imm k],
    if k = 0 then movOrr d.sf d n
    else .bitfield d.sf 2 d.sf (fin 6 ((size - k) % size)) (fin 6 (size - 1 - k)) n.hw d.hw⟩

/-- `LSR` (`opc = 10`, UBFM) / `ASR` (`opc = 00`, SBFM) `Rd, Rn, #k` =
    `xBFM Rd, Rn, #k, #(size-1)`; `MOV` for `k = 0`. -/
def shiftRightRI (s : Shape) (opc : Fin 4) (d n : Opnd) (k : Nat) : Golden :=
  ⟨s, [d, n, .imm k],
    if k = 0 then movOrr d.sf d n
    else .bitfield d.sf opc d.sf (fin 6 k) (fin 6 (regBits d.sf - 1)) n.hw d.hw⟩

/-- `ROR Rd, Rn, #k` = `EXTR Rd, Rn, Rn, #k`; `MOV` for `k = 0`. -/
def rorRI (d n : Opnd) (k : Nat) : Golden :=
  ⟨.RorRI, [d, n, .imm k],
    if k = 0 then movOrr d.sf d n else .extract d.sf d.sf n.hw (fin 6 k) n.hw d.hw⟩

/-- `RBIT Rd, Rn`. -/
def rbit (d n : Opnd) : Golden := ⟨.Rbit, [d, n], .dataProc1 d.sf 0 n.hw d.hw⟩

/-- Move wide: `MOVN` (`opc = 00`), `MOVZ` (`10`), `MOVK` (`11`) `Rd, #imm16{, LSL #shift}`. -/
def moveWide (s : Shape) (opc : Fin 4) (d : Opnd) (imm : Nat) (shift : Option Nat) : Golden :=
  ⟨s, [d, .imm imm] ++ (match shift with | some k => [.imm k] | none => []),
    .moveWide d.sf opc (fin 2 (shift.getD 0 / 16)) (fin 16 imm) d.hw⟩

/-- `CSEL/CSINC/CSINV/CSNEG Rd, Rn, Rm, cond`. -/
def condSel (s : Shape) (op o2 : Fin 2) (d n m : Opnd) (cond : Nat) : Golden :=
  ⟨s, [d, n, m, .imm cond], .condSelect d.sf op m.hw (fin 4 cond) o2 n.hw d.hw⟩

/-- `CSET Rd, cond` = `CSINC Rd, ZR, ZR, invert(cond)`. -/
def cset (d : Opnd) (cond : Nat) : Golden :=
  ⟨.CSet, [d, .imm cond], .condSelect d.sf 0 31 (fin 4 (cond ^^^ 1)) 1 31 d.hw⟩

/-- `SBFM/BFM/UBFM Rd, Rn, #immr, #imms` (`N = sf`). -/
def bfm (s : Shape) (opc : Fin 4) (d n : Opnd) (immr imms : Nat) : Golden :=
  ⟨s, [d, n, .imm immr, .imm imms],
    .bitfield d.sf opc d.sf (fin 6 immr) (fin 6 imms) n.hw d.hw⟩

/-- `SXTB/SXTH/SXTW Xd, Xn` = `SBFM Xd, Xn, #0, #imms`. -/
def sext (s : Shape) (imms : Nat) (d n : Opnd) : Golden :=
  ⟨s, [d, n], .bitfield 1 0 1 0 (fin 6 imms) n.hw d.hw⟩

/-- `UXTB/UXTH Wd, Wn` = `UBFM Wd, Wn, #0, #imms`. -/
def zext (s : Shape) (imms : Nat) (d n : Opnd) : Golden :=
  ⟨s, [d, n], .bitfield 0 2 0 0 (fin 6 imms) n.hw d.hw⟩

/-- `UXTW` = `MOV Wd, Wn` (`ORR Wd, WZR, Wn`) whatever views the operands carry. -/
def uxtw (d n : Opnd) : Golden := ⟨.Uxtw, [d, n], movOrr 0 d n⟩

/-- `B`/`BL` with a signed word offset. -/
def branch (s : Shape) (op : Fin 2) (off : Int) : Golden :=
  ⟨s, [.imm off], .branchImm op (sfield 26 off)⟩

/-- `B.cond` with a signed word offset. -/
def bcond (s : Shape) (cond : Nat) (off : Int) : Golden :=
  ⟨s, [.imm cond, .imm off], .condBranch (sfield 19 off) (fin 4 cond)⟩

/-- `CBZ`/`CBNZ Rt, offset`. -/
def cbranch (s : Shape) (op : Fin 2) (t : Opnd) (off : Int) : Golden :=
  ⟨s, [t, .imm off], .compareBranch t.sf op (sfield 19 off) t.hw⟩

/-- `TBZ`/`TBNZ Rt, #bit, offset`. -/
def tbranch (s : Shape) (op : Fin 2) (t : Opnd) (bit : Nat) (off : Int) : Golden :=
  ⟨s, [t, .imm bit, .imm off], .testBranch (fin 1 (bit / 32)) op (fin 5 bit) (sfield 14 off) t.hw⟩

/-- `BR`/`BLR Xn`. -/
def breg (s : Shape) (opc : Fin 16) (n : Opnd) : Golden := ⟨s, [n], .branchReg opc n.hw⟩

/-- `RET` (X30). -/
def ret : Golden := ⟨.Ret, [], .branchReg 2 30⟩

/-- A scalar immediate-offset access: the scaled unsigned `imm12` form when the byte offset is
    non-negative, aligned and in range, otherwise the unscaled signed `imm9` form (LDUR/STUR);
    `v = 1` for a SIMD&FP register. -/
def ldstImmV (size : Fin 4) (v : Fin 2) (opc : Fin 4) (scale : Nat) (t : Opnd) (base : Nat)
    (off : Int) : Instr :=
  if 0 ≤ off ∧ off % scale = 0 ∧ off / scale ≤ 4095 then
    .loadStoreUImm size v opc (fin 12 (off / scale).toNat) (fin 5 base) t.hw
  else .loadStoreImm9 size v opc (sfield 9 off) 0 (fin 5 base) t.hw

/-- A general-purpose scalar immediate-offset access (`ldstImmV` with `v = 0`). -/
def ldstImm (size opc : Fin 4) (scale : Nat) (t : Opnd) (base : Nat) (off : Int) : Instr :=
  ldstImmV size 0 opc scale t base off

/-- `LDR/STR Rt, [Xn|SP, #off]` (`MemOp`): the access size is the transfer register's. -/
def ldrStr (s : Shape) (opc : Fin 4) (t : Opnd) (base : Nat) (off : Int) : Golden :=
  ⟨s, [t, .mem base off],
    if t.sf.val = 1 then ldstImm 3 opc 8 t base off else ldstImm 2 opc 4 t base off⟩

/-- A byte/halfword access of fixed size; `opc` may depend on the transfer register. -/
def ldstNarrow (s : Shape) (size opc : Fin 4) (scale : Nat) (t : Opnd) (base : Nat) (off : Int) :
    Golden :=
  ⟨s, [t, .mem base off], ldstImm size opc scale t base off⟩

/-- `STR Wt|Xt, [Xn|SP, #off]` typed aliases (fixed size). -/
def strTyped (s : Shape) (size : Fin 4) (scale : Nat) (t : Opnd) (base : Nat) (off : Int) :
    Golden :=
  ⟨s, [t, .mem base off], ldstImm size 0 scale t base off⟩

/-- `STR St|Dt, [Xn|SP, #off]` typed aliases (`V = 1`, fixed size). -/
def strFpTyped (s : Shape) (size : Fin 4) (scale : Nat) (t : Opnd) (base : Nat) (off : Int) :
    Golden :=
  ⟨s, [t, .mem base off], ldstImmV size 1 0 scale t base off⟩

/-- `CRC32{B,H,W,X}` (`c = 0`) / `CRC32C{...}` (`c = 1`) `Wd, Wn, Wm|Xm` with size `sz`. -/
def crc (s : Shape) (c sz : Nat) (d n m : Opnd) : Golden :=
  ⟨s, [d, n, m], .dataProc2 (if sz = 3 then 1 else 0) m.hw (fin 6 (16 + 4 * c + sz)) n.hw d.hw⟩

/-- `LDR/STR Rt, [Xn|SP, #imm9]!` (pre-index, `idx = 11`) / `[Xn|SP], #imm9` (post, `01`). -/
def ldstWb (s : Shape) (opc : Fin 4) (idx : Fin 4) (t base : Opnd) (off : Int) : Golden :=
  ⟨s, [t, base, .imm off],
    .loadStoreImm9 (if t.sf.val = 1 then 3 else 2) 0 opc (sfield 9 off) idx base.hw t.hw⟩

/-- `LDR Xt, label` (literal, `opc = 01`). -/
def ldrLit (t : Opnd) (off : Int) : Golden :=
  ⟨.LdrLiteral, [t, .imm off], .loadLiteral 1 0 (sfield 19 off) t.hw⟩

/-- `LDP/STP Rt, Rt2, [Xn|SP{, #off}]{!}` and post-index: `mode` 10 offset, 11 pre, 01 post. -/
def pair (s : Shape) (l : Fin 2) (mode : Fin 4) (t t2 base : Opnd) (off : Int) : Golden :=
  let scale : Int := if t.sf.val = 1 then 8 else 4
  ⟨s, [t, t2, base, .imm off],
    .loadStorePair (if t.sf.val = 1 then 2 else 0) 0 mode l (sfield 7 (off / scale)) t2.hw
      base.hw t.hw⟩

/-- The register-offset `option:S` of the emitter's packed mode operand
    (`4|5` UXTW, `6|7` LSL, `12|13` SXTW, `14|15` SXTX; low bit = scaled). -/
def roMode (mode : Option Nat) : Fin 8 × Fin 2 :=
  match mode with
  | none => (3, 0)
  | some k => (fin 3 (k / 2), fin 1 k)

/-- `LDR/STR Rt, [Xn|SP, Rm{, extend {#amount}}]`; `size = none` takes the transfer width. -/
def regOff (s : Shape) (size : Option (Fin 4)) (opc : Fin 4) (t base m : Opnd)
    (mode : Option Nat) : Golden :=
  ⟨s, [t, base, m] ++ (match mode with | some k => [.imm k] | none => []),
    .loadStoreRegOff (size.getD (if t.sf.val = 1 then 3 else 2)) 0 opc m.hw (roMode mode).1
      (roMode mode).2 base.hw t.hw⟩

/-- `LDRSW Xt, [Xn|SP, Xm, LSL #2]`. -/
def ldrswRO (t base m : Opnd) : Golden :=
  ⟨.LdrswRO, [t, base, m], .loadStoreRegOff 2 0 2 m.hw 3 1 base.hw t.hw⟩

/-- `ADR` (`op = 0`) / `ADRP` (`op = 1`) `Xd, #imm21`. -/
def adr (s : Shape) (op : Fin 2) (d : Opnd) (imm : Int) : Golden :=
  let raw := (imm % (2 ^ 21 : Int)).toNat
  ⟨s, [d, .imm imm], .pcRel op (fin 2 raw) (fin 19 (raw / 4)) d.hw⟩

/-- `BRK #imm16`; an operand-free `Brk` is `BRK #1`. -/
def brk (imm : Option Nat) : Golden :=
  ⟨.Brk, (match imm with | some v => [.imm v] | none => []), .brk (fin 16 (imm.getD 1))⟩

/-- `DSB` (`op2 = 100`), `DMB` (`101`), `ISB` (`110`) with option `CRm`. -/
def barrier (s : Shape) (op2 : Fin 8) (crm : Nat) : Golden :=
  ⟨s, [.imm crm], .barrier (fin 4 crm) op2⟩

/-- `NOP`. -/
def nop (s : Shape) : Golden := ⟨s, [], .nop⟩

end Spec

/-! ## The corpus -/

open Spec

/-- Register triples exercised by the three-register forms (W and X views). -/
def triples : List (Nat × Nat × Nat) := [(0, 1, 2), (30, 29, 28), (17, 9, 3)]

/-- Both widths. -/
def widths : List (Fin 2) := [1, 0]

/-- Three-register shapes over both widths and the register triples. -/
def rrr (f : Opnd → Opnd → Opnd → Golden) : List Golden :=
  widths.flatMap fun sf => triples.map fun (d, n, m) => f (gpr sf d) (gpr sf n) (gpr sf m)

/-- Arithmetic: add/subtract, compare, negate. -/
def corpusArith : List Golden :=
  rrr (addSubRR .AddRR 0 0) ++ rrr (addSubRR .SubRR 1 0) ++
  rrr (addSubRR .AddsRR 0 1) ++ rrr (addSubRR .SubsRR 1 1) ++
  [addSubRR .AddsRR 0 1 .xzr (.x 1) (.x 2), addSubRR .SubsRR 1 1 .wzr (.w 3) (.w 4),
   addSubRR .SubRR 1 0 (.x 5) .xzr (.x 6)] ++
  (widths.flatMap fun sf =>
    [(.AddRI, 0, 0, 0), (.SubRI, 1, 0, 0), (.AddsRI, 0, 1, 0), (.SubsRI, 1, 1, 0),
     (.AddRIShift12, 0, 0, 1)].flatMap fun ((s : Shape), op, S, sh) =>
      [(0, 1, 0), (2, 3, 1), (30, 29, 4095), (7, 8, 2048)].map fun (d, n, imm) =>
        addSubRI s op S sh (gpr sf d) (gpr sf n) imm) ++
  [addSubRI .AddRI 0 0 0 .sp .sp 16, addSubRI .SubRI 1 0 0 .sp .sp 4095,
   addSubRI .AddRI 0 0 0 (.x 29) .sp 32, addSubRI .AddRI 0 0 0 .sp (.x 9) 0,
   addSubRI .AddRIShift12 0 0 1 .sp .sp 1, addSubRI .SubsRI 1 1 0 .xzr .sp 8,
   addSubRI .AddRI 0 0 0 .wsp .wsp 4] ++
  (widths.flatMap fun sf =>
    [(.AddRRShift, 0, 0), (.SubRRShift, 1, 0), (.AddRRShiftLsr, 0, 1)].flatMap
      fun ((s : Shape), op, shift) =>
        [(0, 1, 2, 1), (30, 29, 28, regBits sf - 1), (5, 6, 7, 12)].map fun (d, n, m, k) =>
          addSubShift s op shift (gpr sf d) (gpr sf n) (gpr sf m) k) ++
  (widths.flatMap fun sf => [(0, 1), (30, 2), (12, 12)].map fun (d, m) =>
    neg (gpr sf d) (gpr sf m)) ++
  (widths.flatMap fun sf => [(0, 1), (30, 29), (5, 5)].map fun (n, m) =>
    cmpRR .CmpRR (gpr sf n) (gpr sf m)) ++
  [cmpRR .CMPWrr (.w 1) (.w 2), cmpRR .CMPXrr (.x 3) (.x 4), cmpRR .CmpRR (.x 7) .xzr] ++
  (widths.flatMap fun sf => [(0, 0), (1, 1), (30, 4095), (9, 64)].map fun (n, imm) =>
    cmpRI .CmpRI (gpr sf n) imm) ++
  [cmpRI .CmpRI .sp 0, cmpRI .CmpRI .sp 4095, cmpRI .CMPWri (.w 5) 7, cmpRI .CMPXri (.x 6) 9,
   cmpRI .CMPXri .sp 16, cmpRI .CmpRI .wsp 3] ++
  [subsFromSp .xzr (.x 0), subsFromSp (.x 9) (.x 16), subsFromSp (.x 30) (.x 30)]

/-- Multiply, divide, multiply-add, long and high multiplies, carries. -/
def corpusMul : List Golden :=
  rrr mul ++ rrr (dp2 .SDiv 3) ++ rrr (dp2 .UDiv 2) ++
  (widths.flatMap fun sf => [(0, 1, 2, 3), (30, 29, 28, 27), (4, 5, 6, 31)].flatMap
    fun (d, n, m, a) =>
      let ra := if a = 31 then zr sf else gpr sf a
      [mulAdd .Madd 0 (gpr sf d) (gpr sf n) (gpr sf m) ra,
       mulAdd .Msub 1 (gpr sf d) (gpr sf n) (gpr sf m) ra]) ++
  ([(0, 1, 2), (30, 29, 28), (8, 8, 8)].flatMap fun (d, n, m) =>
    [mulLong .Smull 1 (.x d) (.w n) (.w m), mulLong .Umull 5 (.x d) (.w n) (.w m),
     mulLong .Smulh 2 (.x d) (.x n) (.x m), mulLong .Umulh 6 (.x d) (.x n) (.x m)]) ++
  rrr (carry .Adc 0 0) ++ rrr (carry .Sbc 1 0) ++ rrr (carry .Adcs 0 1) ++
  rrr (carry .Sbcs 1 1)

/-- Logical register and immediate forms, TST. -/
def corpusLogic : List Golden :=
  rrr (logicRR .AndRR 0 0) ++ rrr (logicRR .OrrRR 1 0) ++ rrr (logicRR .EorRR 2 0) ++
  rrr (logicRR .BicRR 0 1) ++ rrr (logicRR .OrnRR 1 1) ++
  (widths.flatMap fun sf =>
    [(.EorRRShift, 3), (.EorRRLsl, 0), (.EorRRLsr, 1)].flatMap fun ((s : Shape), shift) =>
      [(0, 1, 2, 1), (30, 29, 28, regBits sf - 1), (4, 4, 5, 13)].map fun (d, n, m, k) =>
        eorShift s shift (gpr sf d) (gpr sf n) (gpr sf m) k) ++
  -- (N, immr, imms) per width: 64-bit uses every element size; 32-bit has N = 0.
  ([(.AndRI, 0), (.OrrRI, 1), (.EorRI, 2)].flatMap fun ((s : Shape), opc) =>
    [(1, 0, 0), (1, 0, 62), (1, 63, 62), (1, 4, 31), (0, 0, 0b111100), (0, 1, 0b111000),
     (0, 0, 0b110101), (0, 3, 0b100111), (0, 16, 0b001111), (0, 31, 0b011110)].map
      fun (bn, immr, imms) => logicRI s opc (.x 3) (.x 4) bn immr imms) ++
  ([(.AndRI, 0), (.OrrRI, 1), (.EorRI, 2)].flatMap fun ((s : Shape), opc) =>
    [(0, 0, 0), (0, 0, 30), (0, 31, 30), (0, 1, 0b111100), (0, 2, 0b101011),
     (0, 8, 0b000111)].map fun (bn, immr, imms) => logicRI s opc (.w 5) (.w 6) bn immr imms) ++
  [logicRI .AndRI 0 .sp (.x 1) 1 0 60, logicRI .OrrRI 1 (.x 7) .xzr 0 0 0b111100,
   logicRI .OrrRI 1 (.w 7) .wzr 0 0 30] ++
  [tstRI (.x 0) 1 0 0, tstRI (.x 30) 0 0 0b111100, tstRI (.w 9) 0 1 3, tstRI (.w 2) 0 0 0,
   tstRR (.x 1) (.x 2), tstRR (.w 3) (.w 4), tstRR (.x 30) (.x 30)]

/-- Shifts, rotates, bit reversal, extensions and bitfield moves. -/
def corpusShift : List Golden :=
  rrr (dp2 .LslRR 8) ++ rrr (dp2 .LsrRR 9) ++ rrr (dp2 .AsrRR 10) ++
  (widths.flatMap fun sf => [(0, 1, 0), (2, 3, 1), (30, 29, regBits sf - 1), (4, 4, 17)].flatMap
    fun (d, n, k) =>
      [lslRI (gpr sf d) (gpr sf n) k, shiftRightRI .LsrRI 2 (gpr sf d) (gpr sf n) k,
       shiftRightRI .AsrRI 0 (gpr sf d) (gpr sf n) k, rorRI (gpr sf d) (gpr sf n) k]) ++
  (widths.flatMap fun sf => [(0, 1), (30, 29), (7, 7)].map fun (d, n) =>
    rbit (gpr sf d) (gpr sf n)) ++
  ([(0, 1), (30, 29), (14, 14)].flatMap fun (d, n) =>
    [sext .Sxtw 31 (.x d) (.x n), sext .Sxtb 7 (.x d) (.x n), sext .Sxth 15 (.x d) (.x n),
     zext .Uxtb 7 (.w d) (.w n), zext .Uxth 15 (.w d) (.w n), uxtw (.x d) (.x n),
     uxtw (.w d) (.w n)]) ++
  (widths.flatMap fun sf =>
    [(.Ubfm, 2), (.Sbfm, 0), (.Bfm, 1)].flatMap fun ((s : Shape), opc) =>
      [(0, 1, 0, 7), (30, 29, regBits sf - 1, regBits sf - 1), (3, 4, 5, 2)].map
        fun (d, n, immr, imms) => bfm s opc (gpr sf d) (gpr sf n) immr imms)

/-- Register moves, move-wide constants, conditional selects and sets. -/
def corpusMove : List Golden :=
  (widths.flatMap fun sf => [(0, 1), (30, 29), (17, 17)].flatMap fun (d, m) =>
    [movR .MovR sf (gpr sf d) (gpr sf m),
     movR (if sf.val = 1 then .MOVXrr else .MOVWrr) sf (gpr sf d) (gpr sf m)]) ++
  [movR .MovR 1 .sp (.x 29), movR .MovR 1 (.x 29) .sp, movR .MOVXrr 1 (.x 3) .sp,
   movR .MOVWrr 0 (.w 3) .wsp, movR .MovR 1 (.x 4) .xzr, movR .MovR 0 (.w 4) .wzr] ++
  (widths.flatMap fun sf => [(0, 0), (1, 1), (30, 0xFFFF), (9, 0x1234)].flatMap
    fun (d, imm) =>
      [moveWide .MovI 2 (gpr sf d) imm none, moveWide .Movz 2 (gpr sf d) imm none,
       moveWide .Movz 2 (gpr sf d) imm (some 0), moveWide .Movn 0 (gpr sf d) imm none,
       moveWide .Movn 0 (gpr sf d) imm (some 0), moveWide .Movk 3 (gpr sf d) imm none,
       moveWide .Movk 3 (gpr sf d) imm (some 16)]) ++
  ([(0, 0x1234), (30, 0xFFFF), (5, 1)].flatMap fun (d, imm) =>
    [moveWide .Movk 3 (.x d) imm (some 32), moveWide .Movk 3 (.x d) imm (some 48),
     moveWide .MOVZXi 2 (.x d) imm none, moveWide .MOVZWi 2 (.w d) imm none]) ++
  (widths.flatMap fun sf =>
    [(.Csel, 0, 0), (.Csinc, 0, 1), (.Csinv, 1, 0), (.Csneg, 1, 1)].flatMap
      fun ((s : Shape), op, o2) =>
        [(0, 1, 2, 0), (30, 29, 28, 13), (3, 4, 5, 11), (6, 7, 8, 15)].map fun (d, n, m, c) =>
          condSel s op o2 (gpr sf d) (gpr sf n) (gpr sf m) c) ++
  (widths.flatMap fun sf => (List.range 14).map fun c => cset (gpr sf (c + 1)) c)

/-- Branches. -/
def corpusBranch : List Golden :=
  ([0, 1, -1, 33554431, -33554432, 0x123456].flatMap fun off =>
    [branch .B 0 off, branch .Bl 1 off, branch .BL 1 off]) ++
  ((List.range 16).map fun c => bcond .BCond c 2) ++
  ([0, 1, -1, 262143, -262144].flatMap fun off => [bcond .BCond 0 off, bcond .Bcc 11 off]) ++
  (widths.flatMap fun sf => [(0, 0), (30, 262143), (7, -262144), (1, -2)].flatMap
    fun (t, off) => [cbranch .Cbz 0 (gpr sf t) off, cbranch .Cbnz 1 (gpr sf t) off]) ++
  ([(0, 0, 0), (30, 63, 8191), (3, 32, -8192), (4, 31, -1), (5, 5, 100)].flatMap
    fun (t, bit, off) =>
      [tbranch .Tbz 0 (.x t) bit off, tbranch .Tbnz 1 (.x t) bit off]) ++
  ([(6, 31, 7), (7, 0, -7)].flatMap fun (t, bit, off) =>
    [tbranch .Tbz 0 (.w t) bit off, tbranch .Tbnz 1 (.w t) bit off]) ++
  ([0, 16, 30].flatMap fun n =>
    [breg .Br 0 (.x n), breg .Blr 1 (.x n), breg .BLR 1 (.x n)]) ++ [ret]

/-- Loads and stores. -/
def corpusMemory : List Golden :=
  -- LDR/STR (W and X), unsigned-scaled and unscaled offsets.
  ([(.LdrRI, 1), (.StrRI, 0)].flatMap fun ((s : Shape), opc) =>
    [(.x 0, 1, 0), (.x 1, 31, 8), (.x 30, 2, 32760), (.x 3, 4, -8), (.x 5, 6, 12),
     (.x 7, 31, -256), (.x 8, 9, 255), (.w 0, 1, 0), (.w 2, 31, 4), (.w 3, 4, 16380),
     (.w 5, 6, -4), (.w 7, 8, 2), (.xzr, 1, 16), (.wzr, 2, 8)].map fun (t, b, off) =>
      ldrStr s opc t b off) ++
  -- Narrow loads and stores.
  ([(.LdrbRI, (0 : Fin 4), (1 : Fin 4), (1 : Nat)), (.LdrhRI, 1, 1, 2), (.StrbRI, 0, 0, 1),
    (.StrhRI, 1, 0, 2)].flatMap fun ((s : Shape), size, opc, scale) =>
    [((.w 0 : Opnd), 1, (0 : Int)), (.w 1, 31, ((4095 * scale : Nat) : Int)), (.w 2, 3, -1),
     (.x 4, 5, (scale : Int)), (.wzr, 6, ((2 * scale : Nat) : Int))].map fun (t, b, off) =>
      ldstNarrow s size opc scale t b off) ++
  ([(.LdrsbRI, (0 : Fin 4), (1 : Nat)), (.LdrshRI, 1, 2)].flatMap
    fun ((s : Shape), size, scale) =>
      [((.x 0 : Opnd), 1, (0 : Int)), (.x 2, 31, ((2 * scale : Nat) : Int)), (.x 3, 4, -3),
       (.w 5, 6, (scale : Int)), (.w 7, 8, -16)].map fun (t, b, off) =>
        ldstNarrow s size (if t.sf.val = 1 then 2 else 3) scale t b off) ++
  [strTyped .STRWui 2 4 (.w 1) 31 8, strTyped .STRWui 2 4 (.w 2) 3 (-4),
   strTyped .STRXui 3 8 (.x 1) 31 16, strTyped .STRXui 3 8 (.x 2) 3 (-16)] ++
  -- Pre/post-index writeback.
  ([(.LdrPreIndex, 1, 3), (.StrPreIndex, 0, 3), (.LdrPostIndex, 1, 1), (.StrPostIndex, 0, 1)]
    |>.flatMap fun ((s : Shape), opc, idx) =>
      [(.x 0, .sp, -16), (.x 1, .x 2, 8), (.w 3, .x 4, 255), (.w 5, .sp, -256),
       (.x 30, .x 29, 0)].map fun (t, b, off) => ldstWb s opc idx t b off) ++
  [ldrLit (.x 0) 0, ldrLit (.x 1) 1, ldrLit (.x 2) (-1), ldrLit (.x 30) 262143,
   ldrLit (.x 3) (-262144)] ++
  -- Pairs.
  ([(.LdpRI, (1 : Fin 2), (2 : Fin 4)), (.StpRI, 0, 2), (.StpPreIndex, 0, 3),
    (.LdpPostIndex, 1, 1)].flatMap fun ((s : Shape), l, mode) =>
    [(.x 29, .x 30, .sp, -16), (.x 0, .x 1, .x 2, 0), (.x 3, .x 4, .sp, 504),
     (.x 5, .x 6, .x 7, -512), (.w 8, .w 9, .x 10, 4), (.w 11, .w 12, .sp, -256),
     (.w 13, .w 14, .x 15, 252)].map fun (t, t2, b, off) => pair s l mode t t2 b off) ++
  -- Register offset.
  ([(.LdrRO, (none : Option (Fin 4)), (1 : Fin 4)), (.StrRO, none, 0)].flatMap
    fun ((s : Shape), size, opc) =>
      [(.x 0, .x 1, .x 2, none), (.x 3, .sp, .x 4, some 7), (.w 5, .x 6, .w 7, some 4),
       (.w 8, .x 9, .w 10, some 13), (.x 11, .x 12, .x 13, some 15),
       (.x 14, .x 15, .x 16, some 6)].map fun (t, b, m, mode) =>
        regOff s size opc t b m mode) ++
  ([(.LdrbRO, (some 0 : Option (Fin 4)), (1 : Fin 4)), (.LdrhRO, some 1, 1),
    (.StrbRO, some 0, 0), (.StrhRO, some 1, 0)].flatMap fun ((s : Shape), size, opc) =>
      [(.w 0, .x 1, .x 2, none), (.w 3, .sp, .x 4, some 7), (.w 5, .x 6, .w 7, some 12)].map
        fun (t, b, m, mode) => regOff s size opc t b m mode) ++
  [ldrswRO (.x 0) (.x 1) (.x 2), ldrswRO (.x 30) .sp (.x 29)]

/-- PC-relative addresses, traps, barriers and NOPs. -/
def corpusSystem : List Golden :=
  ([0, 1, -1, 1048575, -1048576, 0x2345].flatMap fun imm =>
    [adr .Adr 0 (.x 0) imm, adr .Adrp 1 (.x 16) imm]) ++
  [brk none, brk (some 0), brk (some 1), brk (some 0x534c), brk (some 0xFFFF)] ++
  ([0xF, 0xB, 0x9, 0xA, 0x3].flatMap fun crm =>
    [barrier .Dmb 5 crm, barrier .Dsb 4 crm, barrier .Isb 6 crm]) ++
  [nop .Nop, nop .AlignNop]

/-- Volatile, tail-call, page-offset, FP-store and CRC32 shapes that share the classes above. -/
def corpusMore : List Golden :=
  [ldrStr .VolatileLdrRI 1 (.x 0) 1 8, ldrStr .VolatileLdrRI 1 (.w 2) 3 (-4),
   ldrStr .VolatileStrRI 0 (.x 4) 31 32760, ldrStr .VolatileStrRI 0 (.w 5) 6 4,
   ldstNarrow .VolatileLdrbRI 0 1 1 (.w 7) 8 4095, ldstNarrow .VolatileLdrhRI 1 1 2 (.w 9) 10 (-2),
   ldstNarrow .VolatileStrbRI 0 0 1 (.w 11) 12 0, ldstNarrow .VolatileStrhRI 1 0 2 (.w 13) 31 2,
   branch .TailCall 0 0, branch .TailCall 0 (-33554432), branch .TailCall 0 0x1FFFFFF,
   addSubRI .AddPCRel 0 0 0 (.x 16) (.x 16) 0, addSubRI .AddPCRel 0 0 0 (.x 0) (.x 1) 4095,
   strFpTyped .STRSui 2 4 (.s 0) 31 8, strFpTyped .STRSui 2 4 (.s 31) 3 (-4),
   strFpTyped .STRSui 2 4 (.s 7) 5 16380, strFpTyped .STRDui 3 8 (.d 8) 31 16,
   strFpTyped .STRDui 3 8 (.d 15) 4 (-256), strFpTyped .STRDui 3 8 (.d 31) 6 32760] ++
  ([(.Crc32B, 0, 0), (.Crc32H, 0, 1), (.Crc32W, 0, 2), (.Crc32X, 0, 3), (.Crc32Cb, 1, 0),
    (.Crc32Ch, 1, 1), (.Crc32Cw, 1, 2), (.Crc32Cx, 1, 3)].flatMap fun ((s : Shape), c, sz) =>
    [(0, 1, 2), (30, 29, 28)].map fun (d, n, m) =>
      crc s c sz (.w d) (.w n) (if sz = 3 then .x m else .w m))

/-- The whole golden corpus. -/
def corpus : List Golden :=
  corpusArith ++ corpusMul ++ corpusLogic ++ corpusShift ++ corpusMove ++ corpusBranch ++
  corpusMemory ++ corpusSystem ++ corpusMore

/-! ## Golden rows -/

/-- One row of `Trust/A64/EncoderGolden.lean`: an emitter input, the instruction it denotes,
    and that instruction's word. -/
structure GoldenRow where
  shape : Shape
  operands : List Opnd
  instr : Instr
  word : UInt32
  deriving DecidableEq, Repr

/-- The corpus entry a row records. -/
def GoldenRow.golden (r : GoldenRow) : Golden := ⟨r.shape, r.operands, r.instr⟩

/-- A row is sound when its word is the model's encoding of its instruction, the model decodes
    the word back to that instruction, and the instruction is valid. -/
def GoldenRow.sound (r : GoldenRow) : Bool :=
  encode r.instr == r.word && decode r.word == some r.instr && r.instr.valid

end A64
end Trust
