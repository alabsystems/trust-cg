/- Single-source register-bit computation, compiled by Trust through clean mod.
   The encoder and the formal register model consume this same definition. -/
def trust_cg_x86_low3 (reg : UInt8) : UInt8 := reg &&& 7

theorem trust_cg_x86_low3_body (reg : UInt8) :
    trust_cg_x86_low3 reg = (reg &&& 7) := rfl
