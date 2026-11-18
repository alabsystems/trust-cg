/- Copyright 2026 Andrew Yates | License: Apache-2.0 -/

/-- The paired register update has zero delta when both five-bit source fields match. -/
def trust_cg_a64_euclidean_register_update (b r nextASrc nextBSrc : UInt32) : UInt32 :=
  32 * b + r - (32 * nextASrc + nextBSrc)

theorem trust_cg_a64_euclidean_register_update_body (b r nextASrc nextBSrc : UInt32) :
    trust_cg_a64_euclidean_register_update b r nextASrc nextBSrc =
      (32 * b + r - (32 * nextASrc + nextBSrc)) := rfl
