/-- Pack the top three bits and the remaining fields of ADD or SUB immediate. -/
def trust_cg_a64_add_sub_imm_word (sfOpS sh imm12 rn rd : UInt32) : UInt32 :=
  0x11000000 + sfOpS * 0x20000000 + sh * 0x00400000 + imm12 * 1024 + rn * 32 + rd

theorem trust_cg_a64_add_sub_imm_word_body (sfOpS sh imm12 rn rd : UInt32) :
    trust_cg_a64_add_sub_imm_word sfOpS sh imm12 rn rd =
      (0x11000000 + sfOpS * 0x20000000 + sh * 0x00400000 + imm12 * 1024 + rn * 32 + rd) := rfl
