/- Single-source register-bit computation, compiled by Trust through clean mod.
   The encoder and the formal register model consume this same definition. -/
def trust_cg_x86_low3 (reg : UInt8) : UInt8 := reg &&& 7

theorem trust_cg_x86_low3_body (reg : UInt8) :
    trust_cg_x86_low3 reg = (reg &&& 7) := rfl

/-- The same high-register decision used by the production REX encoder. -/
def trust_cg_x86_is_extended (reg : UInt8) : UInt8 :=
  if reg < 8 then 0 else 1

theorem trust_cg_x86_is_extended_body (reg : UInt8) :
    trust_cg_x86_is_extended reg = (if reg < 8 then 0 else 1) := rfl

/-- The production and model REX byte, including its mandatory 0100 prefix. -/
def trust_cg_x86_rex_byte (w r x b : UInt8) : UInt8 :=
  0x40 + w * 8 + r * 4 + x * 2 + b

theorem trust_cg_x86_rex_byte_body (w r x b : UInt8) :
    trust_cg_x86_rex_byte w r x b =
      (0x40 + w * 8 + r * 4 + x * 2 + b) := rfl

/-- Pack the disjoint fields of a ModR/M or SIB byte.
    The middle and low fields each occupy three bits. -/
def trust_cg_x86_pack_fields (high middle low : UInt8) : UInt8 :=
  high * 64 + middle * 8 + low

theorem trust_cg_x86_pack_fields_body (high middle low : UInt8) :
    trust_cg_x86_pack_fields high middle low =
      (high * 64 + middle * 8 + low) := rfl

/-- Pack the bytes of `SHR r64, imm8` in little-endian order.
    The inputs are one REX.B bit, three register bits, and the raw immediate byte. -/
def trust_cg_x86_shr64_word (regHigh regLow imm : UInt32) : UInt32 :=
  0x00E8C148 + regHigh + regLow * 65536 + imm * 16777216

theorem trust_cg_x86_shr64_word_body (regHigh regLow imm : UInt32) :
    trust_cg_x86_shr64_word regHigh regLow imm =
      (0x00E8C148 + regHigh + regLow * 65536 + imm * 16777216) := rfl

/-- Pack the REX.W+B and B8+rd bytes of MOVABS in little-endian order. -/
def trust_cg_x86_movabs_prefix (regHigh regLow : UInt16) : UInt16 :=
  0xB848 + regHigh + regLow * 256

theorem trust_cg_x86_movabs_prefix_body (regHigh regLow : UInt16) :
    trust_cg_x86_movabs_prefix regHigh regLow =
      (0xB848 + regHigh + regLow * 256) := rfl
