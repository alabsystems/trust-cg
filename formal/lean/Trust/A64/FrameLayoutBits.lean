/-- The two's-complement alignment mask for a positive power of two. -/
def trust_cg_a64_frame_alignment_mask (alignment : UInt32) : UInt32 :=
  0 - alignment

/-- Apply the mask to either an unsigned size or a signed FP-relative cursor. -/
def trust_cg_a64_frame_apply_mask (offset mask : UInt32) : UInt32 :=
  offset &&& mask

theorem trust_cg_a64_frame_align_down_body (offset alignment : UInt32) :
    trust_cg_a64_frame_apply_mask offset (trust_cg_a64_frame_alignment_mask alignment) =
      (offset &&& (0 - alignment)) := rfl

/-- The Darwin startup frame has a 16-byte FP/LR record and an 8-byte local.
    Add the alignment bias to the frame size before rounding down. -/
theorem trust_cg_a64_startup_frame_layout :
    trust_cg_a64_frame_apply_mask (16 + 8 + 15) (trust_cg_a64_frame_alignment_mask 16) = 32 ∧
    trust_cg_a64_frame_apply_mask (0 - 8) (trust_cg_a64_frame_alignment_mask 8) = (0 - 8) :=
  And.intro rfl rfl
