/- Copyright 2026 Andrew Yates | License: Apache-2.0 -/

/-- Accept ordinary fallthrough (0) and direct calls (1) in the prefix, and a trap (2)
    in the final row. The position and the return flag use 0 or 1. -/
def trust_cg_a64_closed_callee_row (kind terminal : UInt32) : UInt32 :=
  if terminal = 0 then
    if kind = 0 then 1 else if kind = 1 then 1 else 0
  else if terminal = 1 then
    if kind = 2 then 1 else 0
  else 0

theorem trust_cg_a64_closed_callee_row_body (kind terminal : UInt32) :
    trust_cg_a64_closed_callee_row kind terminal =
      (if terminal = 0 then
        if kind = 0 then 1 else if kind = 1 then 1 else 0
      else if terminal = 1 then
        if kind = 2 then 1 else 0
      else 0) := rfl
