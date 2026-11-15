/-
  GenA64Golden — render `Trust/A64/EncoderGolden.lean` from `Trust.A64.corpus`.

  Author: Andrew Yates
  Copyright 2026 Andrew Yates | License: Apache-2.0

  Run from `formal/lean` after `lake build Trust.A64.Corpus`:

      lake env lean --run scripts/GenA64Golden.lean > Trust/A64/EncoderGolden.lean

  Every word printed here is `encode` of the row's instruction, computed by the compiled Lean
  model; the generated module re-checks every row in the kernel.
-/
import Trust.A64.Corpus

open Trust.A64

def hexDigit (n : Nat) : Char := "0123456789ABCDEF".toList.getD n '0'

def hex8 (w : UInt32) : String :=
  "0x" ++ String.ofList ((List.range 8).reverse.map fun k => hexDigit (w.toNat / 16 ^ k % 16))

def renderInt (v : Int) : String := if v < 0 then s!"({v})" else s!"{v}"

def renderOpnd : Opnd → String
  | .x n => s!".x {n}"
  | .w n => s!".w {n}"
  | .sp => ".sp"
  | .wsp => ".wsp"
  | .xzr => ".xzr"
  | .wzr => ".wzr"
  | .imm v => s!".imm {renderInt v}"
  | .mem b off => s!".mem {b} {renderInt off}"
  | .s n => s!".s {n}"
  | .d n => s!".d {n}"

def stripPrefix (pfx : String) (s : String) : String :=
  s.replace pfx ""

def renderInstr (i : Instr) : String :=
  "." ++ stripPrefix "Trust.A64.Instr." (Std.Format.pretty (repr i) 100000)

def renderShape (s : Shape) : String :=
  "." ++ stripPrefix "Trust.A64.Shape." (Std.Format.pretty (repr s) 1000)

def header : String := "/-
  A64.EncoderGolden — GENERATED golden corpus binding the Lean A64 encoder model to the Rust
  AArch64 emitter (ledger X-LEAN-P3).  DO NOT EDIT: regenerate from `formal/lean` with

      lake env lean --run scripts/GenA64Golden.lean > Trust/A64/EncoderGolden.lean

  Author: Andrew Yates
  Copyright 2026 Andrew Yates | License: Apache-2.0

  Each row is `⟨shape, operands, instruction, word⟩`: an emitter input (`AArch64Opcode` variant
  and `MachOperand` list), the A64 instruction `Trust.A64.Corpus` says it denotes, and that
  instruction's 32-bit word.  The kernel checks, by evaluation:

    * `goldenRows_are_corpus` — the rows are exactly `Trust.A64.corpus`, in order (so no row can
      be hand-edited, added or dropped without changing the corpus definition);
    * `goldenRows_sound` — every word is `encode` of its instruction, `decode` maps it back, and
      the instruction is `valid`.

  `crates/trust-cg-codegen/tests/lean_a64_encode_golden_binding.rs` parses the rows (one per
  line, rigid format) and requires the production `encode_instruction` to emit each word for
  its shape and operands, and the ENC-5 decode-check to accept it.  This binds the enumerated
  rows only; it is not a proof about the Rust emitter.
-/
import Trust.A64.Corpus

namespace Trust
namespace A64

/-- The generated golden rows (one per line; the Rust binding parses this layout). -/
def goldenRows : List GoldenRow := ["

def footer (n : Nat) : String := s!"]

theorem goldenRows_are_corpus : goldenRows.map GoldenRow.golden = corpus := by decide +kernel

theorem goldenRows_sound : goldenRows.all GoldenRow.sound = true := by decide +kernel

/-- Control: the check is not vacuous — flipping any one bit of every word makes every row
    unsound (bits 0, 5, 10, 16, 21, 24, 29 and 31 are checked). -/
theorem goldenRows_refuse_corrupted_words :
    ([0x1, 0x20, 0x400, 0x10000, 0x200000, 0x1000000, 0x20000000, 0x80000000] : List UInt32).all
      (fun mask => !(goldenRows.map fun r => \{ r with word := r.word ^^^ mask }).any
        GoldenRow.sound) =
      true := by decide +kernel

theorem goldenRows_length : goldenRows.length = {n} := by decide +kernel

end A64
end Trust"

def main : IO Unit := do
  let rows := corpus
  IO.println header
  let n := rows.length
  let mut k := 0
  for g in rows do
    k := k + 1
    let ops := ", ".intercalate (g.operands.map renderOpnd)
    let sep := if k == n then "" else ","
    IO.println s!"  ⟨{renderShape g.shape}, [{ops}], {renderInstr g.instr}, {hex8 (encode g.instr)}⟩{sep}"
  IO.println (footer n)
