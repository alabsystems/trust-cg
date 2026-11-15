/- Definition bindings and kernel-checked hostile controls for the SWAR value proof. -/
import Trust.Cert.BitManip
open Trust.Cert.BitManip
open Trust.Cert.BitManip.Internal

-- These rfl checks pin the exact operation order, masks and fold shifts.
example (x : BitVec 32) : popcnt32Swar x = (
    let a := x - ((x >>> 1) &&& 0x55555555)
    let b := (a &&& 0x33333333) + ((a >>> 2) &&& 0x33333333)
    let c := (b + (b >>> 4)) &&& 0x0f0f0f0f
    let d := c + (c >>> 8)
    let e := d + (d >>> 16)
    e &&& 0x3f) := rfl
example (x : BitVec 64) : popcnt64Swar x = (
    let a := x - ((x >>> 1) &&& 0x5555555555555555)
    let b := (a &&& 0x3333333333333333) + ((a >>> 2) &&& 0x3333333333333333)
    let c := (b + (b >>> 4)) &&& 0x0f0f0f0f0f0f0f0f
    let d := c + (c >>> 8)
    let e := d + (d >>> 16)
    let f := e + (e >>> 32)
    f &&& 0x7f) := rfl

example : popcnt32Swar 0 = 0 := by decide
example : popcnt32Swar 0xffffffff = 32 := by decide
example : popcnt32Swar 0x01010101 = 4 := by decide
example : popcnt64Swar 0 = 0 := by decide
example : popcnt64Swar 0xffffffffffffffff = 64 := by decide
example : popcnt64Swar 0x8000000000000000 = 1 := by decide
example : popcnt64Swar 0x0101010101010101 = 8 := by decide

def wrongMask32 (x : BitVec 32) := fold32 (byteCore x 0x55555554 0x33333333 0x0f0f0f0f)
def droppedFold8 (x : BitVec 32) :=
  let c := byteCore x 0x55555555 0x33333333 0x0f0f0f0f
  (c + (c >>> 16)) &&& 0x3f
def misplacedFold16 (x : BitVec 32) :=
  let c := byteCore x 0x55555555 0x33333333 0x0f0f0f0f
  let d := c + (c >>> 8)
  (d + (d >>> 12)) &&& 0x3f
def droppedFold32 (x : BitVec 64) :=
  let c := byteCore x 0x5555555555555555 0x3333333333333333 0x0f0f0f0f0f0f0f0f
  let d := c + (c >>> 8)
  (d + (d >>> 16)) &&& 0x7f
def wrongFinalMask64 (x : BitVec 64) := popcnt64Swar x &&& 0x3f

example : wrongMask32 2 ≠ (2 : BitVec 32).cpop := by decide
example : droppedFold8 0x100 ≠ (0x100 : BitVec 32).cpop := by decide
example : misplacedFold16 0x10000 ≠ (0x10000 : BitVec 32).cpop := by decide
example : droppedFold32 0x0100000000000000 ≠ (0x0100000000000000 : BitVec 64).cpop := by decide
example : wrongFinalMask64 0xffffffffffffffff ≠ (0xffffffffffffffff : BitVec 64).cpop := by decide
-- The byte-count bound in the internal fold theorem is a real premise.
example : fold32 (pack32 0 0 0 64) ≠ BitVec.ofNat 32 64 := by decide
example : fold64 (pack64 0 0 0 0 0 0 0 128) ≠ BitVec.ofNat 64 128 := by decide

#eval IO.println "BITMANIP-CHECKS bindings=2 boundaries=7 mutations=5 invalid_byte_counts=2"
