/- Copyright 2026 Andrew Yates | License: Apache-2.0 -/

/-- Toggle the low bit of a condition encoding. -/
def trust_cg_a64_cond_toggle (cc : UInt32) : UInt32 := cc ^^^ 1

theorem trust_cg_a64_cond_toggle_body (cc : UInt32) :
    trust_cg_a64_cond_toggle cc = (cc ^^^ 1) := rfl

/-- EQ through LE have logical complements. AL and NV both hold unconditionally. -/
def trust_cg_a64_cond_complementable (cc : UInt32) : UInt32 := if cc < 14 then 1 else 0

theorem trust_cg_a64_cond_complementable_body (cc : UInt32) :
    trust_cg_a64_cond_complementable cc = (if cc < 14 then 1 else 0) := rfl

/-- Bit `cc` gives the truth of condition `cc` for four flags encoded as 0 or 1.
    AL and NV are both set. Each other pair starts with its odd bit set;
    subtracting the pair's low bit moves truth to its even bit. -/
def trust_cg_a64_cond_truth_mask (n z c v : UInt32) : UInt32 :=
  0xEAAA - z - 4 * c - 16 * n - 64 * v - 256 * c * (1 - z)
    - (1024 + 4096 * (1 - z)) * (1 - n - v + 2 * n * v)

theorem trust_cg_a64_cond_truth_mask_body (n z c v : UInt32) :
    trust_cg_a64_cond_truth_mask n z c v =
      (0xEAAA - z - 4 * c - 16 * n - 64 * v - 256 * c * (1 - z)
        - (1024 + 4096 * (1 - z)) * (1 - n - v + 2 * n * v)) := rfl
