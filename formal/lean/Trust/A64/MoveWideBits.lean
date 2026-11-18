/-- Pack the top three bits and the remaining fields of MOVN, MOVZ, or MOVK. -/
def trust_cg_a64_move_wide_word (sfOpc hw imm16 rd : UInt32) : UInt32 :=
  0x12800000 + sfOpc * 0x20000000 + hw * 0x00200000 + imm16 * 32 + rd

theorem trust_cg_a64_move_wide_word_body (sfOpc hw imm16 rd : UInt32) :
    trust_cg_a64_move_wide_word sfOpc hw imm16 rd =
      (0x12800000 + sfOpc * 0x20000000 + hw * 0x00200000 + imm16 * 32 + rd) := rfl
