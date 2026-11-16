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
