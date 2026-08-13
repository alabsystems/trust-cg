/-
  Model.EncoderGolden — ENC-4 golden-vector binding of the Lean byte encoder to the real backend.

  Author: Andrew Yates
  Copyright 2026 Andrew Yates | License: Apache-2.0

  ─────────────────────────────────────────────────────────────────────────────────────────────
  WHAT THIS IS.  `Model.Encoder.encode` is the Lean model's byte-level x86-64 emitter; the
  `x86Step_decode` keystone axiom is only end-to-end meaningful if those model bytes are the bytes
  the REAL backend (`crates/trust-cg-codegen/src/x86_64/encode.rs`) actually writes.  Nothing
  forces the two to stay in step — the model could drift and keep proving things about an encoding
  the backend no longer emits.  This module is the ANCHOR that stops that drift:

    * Each `g_<op>_<pair>` theorem below pins `encode <Instr>` to an EXACT, human-auditable byte
      list, KERNEL-CHECKED by `decide` (`lake build` fails closed if the model's `encode` ever
      produces different bytes).  These are the keystone-reachable b64 reg/reg ALU forms — exactly
      the set `decode`/`x86Step_decode` vouches for.
    * The Rust test `crates/trust-cg-codegen/tests/lean_encode_golden_binding.rs` PARSES this very
      file, and asserts the real `encode.rs` emits byte-for-byte the SAME lists.

  So the golden literals here are the single shared anchor:  encode.rs  ==  (these bytes)  ==  the
  Lean model's `encode`.  A drift on EITHER leg — the model's `encode`, or the backend's emitter —
  fails a gate.  Adds NO axiom and NO `sorry` (each proof is a closed `decide`; `#print axioms`
  shows only `propext, Quot.sound`), so the ENC-1 sorry/axiom baselines are undisturbed.

  DO NOT hand-edit the byte lists to "make it pass".  A changed byte here that lake still accepts
  means the MODEL changed; the Rust leg will then reject unless the backend changed the same way —
  which is the whole point.
  ─────────────────────────────────────────────────────────────────────────────────────────────
-/
import Trust.Model.Encoder

namespace Trust
namespace Model
namespace Encoder

/-! ## Golden vectors: `encode` of the keystone-reachable b64 reg/reg ALU forms.

    Format is RIGID (one theorem per line, `= ([ ... ] : List UInt8) := by decide`) because the
    Rust binding test parses these lines.  Do not reflow. -/

theorem g_movRR_rax_rcx : encode (.movRR .b64 .rax .rcx) = ([0x48, 0x89, 0xC8] : List UInt8) := by decide
theorem g_addRR_rax_rcx : encode (.addRR .b64 .rax .rcx) = ([0x48, 0x01, 0xC8] : List UInt8) := by decide
theorem g_adcRR_rax_rcx : encode (.adcRR .b64 .rax .rcx) = ([0x48, 0x11, 0xC8] : List UInt8) := by decide
theorem g_subRR_rax_rcx : encode (.subRR .b64 .rax .rcx) = ([0x48, 0x29, 0xC8] : List UInt8) := by decide
theorem g_sbbRR_rax_rcx : encode (.sbbRR .b64 .rax .rcx) = ([0x48, 0x19, 0xC8] : List UInt8) := by decide
theorem g_cmpRR_rax_rcx : encode (.cmpRR .b64 .rax .rcx) = ([0x48, 0x39, 0xC8] : List UInt8) := by decide
theorem g_testRR_rax_rcx : encode (.testRR .b64 .rax .rcx) = ([0x48, 0x85, 0xC8] : List UInt8) := by decide
theorem g_andRR_rax_rcx : encode (.andRR .b64 .rax .rcx) = ([0x48, 0x21, 0xC8] : List UInt8) := by decide
theorem g_orRR_rax_rcx : encode (.orRR .b64 .rax .rcx) = ([0x48, 0x09, 0xC8] : List UInt8) := by decide
theorem g_xorRR_rax_rcx : encode (.xorRR .b64 .rax .rcx) = ([0x48, 0x31, 0xC8] : List UInt8) := by decide
theorem g_movRR_r8_rdx : encode (.movRR .b64 .r8 .rdx) = ([0x49, 0x89, 0xD0] : List UInt8) := by decide
theorem g_addRR_r8_rdx : encode (.addRR .b64 .r8 .rdx) = ([0x49, 0x01, 0xD0] : List UInt8) := by decide
theorem g_adcRR_r8_rdx : encode (.adcRR .b64 .r8 .rdx) = ([0x49, 0x11, 0xD0] : List UInt8) := by decide
theorem g_subRR_r8_rdx : encode (.subRR .b64 .r8 .rdx) = ([0x49, 0x29, 0xD0] : List UInt8) := by decide
theorem g_sbbRR_r8_rdx : encode (.sbbRR .b64 .r8 .rdx) = ([0x49, 0x19, 0xD0] : List UInt8) := by decide
theorem g_cmpRR_r8_rdx : encode (.cmpRR .b64 .r8 .rdx) = ([0x49, 0x39, 0xD0] : List UInt8) := by decide
theorem g_testRR_r8_rdx : encode (.testRR .b64 .r8 .rdx) = ([0x49, 0x85, 0xD0] : List UInt8) := by decide
theorem g_andRR_r8_rdx : encode (.andRR .b64 .r8 .rdx) = ([0x49, 0x21, 0xD0] : List UInt8) := by decide
theorem g_orRR_r8_rdx : encode (.orRR .b64 .r8 .rdx) = ([0x49, 0x09, 0xD0] : List UInt8) := by decide
theorem g_xorRR_r8_rdx : encode (.xorRR .b64 .r8 .rdx) = ([0x49, 0x31, 0xD0] : List UInt8) := by decide
theorem g_movRR_rdx_r9 : encode (.movRR .b64 .rdx .r9) = ([0x4C, 0x89, 0xCA] : List UInt8) := by decide
theorem g_addRR_rdx_r9 : encode (.addRR .b64 .rdx .r9) = ([0x4C, 0x01, 0xCA] : List UInt8) := by decide
theorem g_adcRR_rdx_r9 : encode (.adcRR .b64 .rdx .r9) = ([0x4C, 0x11, 0xCA] : List UInt8) := by decide
theorem g_subRR_rdx_r9 : encode (.subRR .b64 .rdx .r9) = ([0x4C, 0x29, 0xCA] : List UInt8) := by decide
theorem g_sbbRR_rdx_r9 : encode (.sbbRR .b64 .rdx .r9) = ([0x4C, 0x19, 0xCA] : List UInt8) := by decide
theorem g_cmpRR_rdx_r9 : encode (.cmpRR .b64 .rdx .r9) = ([0x4C, 0x39, 0xCA] : List UInt8) := by decide
theorem g_testRR_rdx_r9 : encode (.testRR .b64 .rdx .r9) = ([0x4C, 0x85, 0xCA] : List UInt8) := by decide
theorem g_andRR_rdx_r9 : encode (.andRR .b64 .rdx .r9) = ([0x4C, 0x21, 0xCA] : List UInt8) := by decide
theorem g_orRR_rdx_r9 : encode (.orRR .b64 .rdx .r9) = ([0x4C, 0x09, 0xCA] : List UInt8) := by decide
theorem g_xorRR_rdx_r9 : encode (.xorRR .b64 .rdx .r9) = ([0x4C, 0x31, 0xCA] : List UInt8) := by decide
theorem g_movRR_r15_r8 : encode (.movRR .b64 .r15 .r8) = ([0x4D, 0x89, 0xC7] : List UInt8) := by decide
theorem g_addRR_r15_r8 : encode (.addRR .b64 .r15 .r8) = ([0x4D, 0x01, 0xC7] : List UInt8) := by decide
theorem g_adcRR_r15_r8 : encode (.adcRR .b64 .r15 .r8) = ([0x4D, 0x11, 0xC7] : List UInt8) := by decide
theorem g_subRR_r15_r8 : encode (.subRR .b64 .r15 .r8) = ([0x4D, 0x29, 0xC7] : List UInt8) := by decide
theorem g_sbbRR_r15_r8 : encode (.sbbRR .b64 .r15 .r8) = ([0x4D, 0x19, 0xC7] : List UInt8) := by decide
theorem g_cmpRR_r15_r8 : encode (.cmpRR .b64 .r15 .r8) = ([0x4D, 0x39, 0xC7] : List UInt8) := by decide
theorem g_testRR_r15_r8 : encode (.testRR .b64 .r15 .r8) = ([0x4D, 0x85, 0xC7] : List UInt8) := by decide
theorem g_andRR_r15_r8 : encode (.andRR .b64 .r15 .r8) = ([0x4D, 0x21, 0xC7] : List UInt8) := by decide
theorem g_orRR_r15_r8 : encode (.orRR .b64 .r15 .r8) = ([0x4D, 0x09, 0xC7] : List UInt8) := by decide
theorem g_xorRR_r15_r8 : encode (.xorRR .b64 .r15 .r8) = ([0x4D, 0x31, 0xC7] : List UInt8) := by decide

end Encoder
end Model
end Trust
