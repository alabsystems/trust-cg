/- Copyright 2026 Andrew Yates | License: Apache-2.0 -/

/-- Pack the bounded fields of an A64 logical-immediate word. -/
def trust_cg_a64_logical_imm_word (sf opc n immr imms rn rd : UInt32) : UInt32 :=
  0x12000000 + sf * 0x80000000 + opc * 0x20000000 + n * 0x00400000
    + immr * 65536 + imms * 1024 + rn * 32 + rd

theorem trust_cg_a64_logical_imm_word_body (sf opc n immr imms rn rd : UInt32) :
    trust_cg_a64_logical_imm_word sf opc n immr imms rn rd =
      (0x12000000 + sf * 0x80000000 + opc * 0x20000000 + n * 0x00400000
        + immr * 65536 + imms * 1024 + rn * 32 + rd) := rfl

/-- Only a 64-bit element sets N. -/
def trust_cg_a64_logical_imm_n (elementWidth : UInt32) : UInt32 := elementWidth >>> 6

/-- The element-size prefix and run length in the six-bit imms field. -/
def trust_cg_a64_logical_imm_imms (elementWidth n onesLen : UInt32) : UInt32 :=
  63 - elementWidth * 2 + onesLen + n * 64

theorem trust_cg_a64_logical_imm_imms_body (elementWidth n onesLen : UInt32) :
    trust_cg_a64_logical_imm_imms elementWidth n onesLen =
      (63 - elementWidth * 2 + onesLen + n * 64) := rfl

def trust_cg_a64_logical_imm_pow_index (exponent : UInt64) : UInt64 := exponent % 8

def trust_cg_a64_logical_imm_pow_group (exponent : UInt64) : UInt64 := exponent >>> 3

/-- The low factor of 2^i, selected by i % 8. -/
def trust_cg_a64_logical_imm_pow_lo (index : UInt64) : UInt64 :=
  if index < 4 then
    if index < 2 then (if index < 1 then 1 else 2)
    else (if index < 3 then 4 else 8)
  else
    if index < 6 then (if index < 5 then 16 else 32)
    else (if index < 7 then 64 else 128)

/-- The high factor of 2^i, selected by i / 8. At i = 64 the word wraps to zero. -/
def trust_cg_a64_logical_imm_pow_hi (index : UInt64) : UInt64 :=
  if index < 4 then
    if index < 2 then (if index < 1 then 1 else 0x100)
    else (if index < 3 then 0x10000 else 0x1000000)
  else
    if index < 6 then (if index < 5 then 0x100000000 else 0x10000000000)
    else if index < 7 then 0x1000000000000
    else if index < 8 then 0x100000000000000 else 0

/-- Multiply either the factors of a power or an element by its repeat coefficient. -/
def trust_cg_a64_logical_imm_mul (x y : UInt64) : UInt64 := x * y

/-- Number of ones carried across the low boundary by rotation. -/
def trust_cg_a64_logical_imm_wrap_count (onesLen rotation : UInt64) : UInt64 :=
  if onesLen < rotation then onesLen else rotation

/-- Combine the low ones with the high ones from the wrapped part of the run. -/
def trust_cg_a64_logical_imm_rotate (lowPower wrapPower highShiftPower : UInt64) : UInt64 :=
  lowPower - 1 + (wrapPower - 1) * highShiftPower

theorem trust_cg_a64_logical_imm_rotate_body (lowPower wrapPower highShiftPower : UInt64) :
    trust_cg_a64_logical_imm_rotate lowPower wrapPower highShiftPower =
      (lowPower - 1 + (wrapPower - 1) * highShiftPower) := rfl

/-- All ones below a power of two, including an all-ones word when the power wraps. -/
def trust_cg_a64_logical_imm_mask (power : UInt64) : UInt64 := power - 1

def trust_cg_a64_logical_imm_extract (value mask : UInt64) : UInt64 := value &&& mask

/-- A one in the low bit of every element at the selected register width. -/
def trust_cg_a64_logical_imm_repeat_factor (registerWidth elementWidth : UInt64) : UInt64 :=
  if registerWidth < 64 then
    if elementWidth < 8 then
      if elementWidth < 4 then 0x55555555 else 0x11111111
    else if elementWidth < 16 then 0x01010101
    else if elementWidth < 32 then 0x00010001 else 1
  else
    if elementWidth < 8 then
      if elementWidth < 4 then 0x5555555555555555 else 0x1111111111111111
    else if elementWidth < 16 then 0x0101010101010101
    else if elementWidth < 32 then 0x0001000100010001
    else if elementWidth < 64 then 0x0000000100000001 else 1

theorem trust_cg_a64_logical_imm_repeat_factor_64_2 :
    trust_cg_a64_logical_imm_repeat_factor 64 2 = 0x5555555555555555 := rfl
