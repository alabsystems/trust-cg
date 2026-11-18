/- Copyright 2026 Andrew Yates | License: Apache-2.0 -/

/-- Normalize one equality-to-false layer of a Boolean guard. -/
def trust_cg_a64_zero_guard_not (test : Bool) : Bool := !test

theorem trust_cg_a64_zero_guard_not_body (test : Bool) :
    trust_cg_a64_zero_guard_not test = !test := rfl

theorem trust_cg_a64_zero_guard_eq_false (test : Bool) :
    (test == false) = trust_cg_a64_zero_guard_not test := by
  cases test <;> rfl

theorem trust_cg_a64_zero_guard_not_twice (test : Bool) :
    trust_cg_a64_zero_guard_not (trust_cg_a64_zero_guard_not test) = test := by
  cases test <;> rfl

theorem trust_cg_a64_zero_guard_double_eq_false (test : Bool) :
    ((test == false) == false) = test := by
  rw [trust_cg_a64_zero_guard_eq_false, trust_cg_a64_zero_guard_eq_false,
    trust_cg_a64_zero_guard_not_twice]

/-- A repeated 64-bit zero test on the default edge cannot trap on true. -/
theorem trust_cg_a64_zero_guard_no_trap (value : UInt64)
    (default_edge : (value == 0) = false) :
    (((value == 0) == false) == false) = false :=
  (trust_cg_a64_zero_guard_double_eq_false (value == 0)).trans default_edge

theorem trust_cg_a64_zero_guard_contradiction (value : UInt64)
    (default_edge : (value == 0) = false)
    (trap_edge : (((value == 0) == false) == false) = true) : False := by
  have impossible : false = true :=
    (trust_cg_a64_zero_guard_no_trap value default_edge).symm.trans trap_edge
  cases impossible
