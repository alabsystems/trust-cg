import Lean
import Trust.Model.EncoderStep
import Trust.Model.ShrGolden
open Trust Trust.Model.Encoder Lean Elab Command

private def shrState : MachState :=
  { filledMachState 0 with
    regs := fun r => if r = .rax then 0x8000000000000003 else 19
    mem := fun a => if a = 0 then 0x48 else if a = 1 then 0xC1
      else if a = 2 then 0xE8 else if a = 3 then 2 else 0 }

private theorem shrResident :
    BytesAt shrState shrState.rip (encode (.shrRI .b64 .rax 2)) :=
  ⟨rfl, rfl, rfl, rfl, True.intro⟩

private def post (choice : Bool) : MachState :=
  execInstrChoice (.shrRI .b64 .rax 2) shrState choice

-- Both choices really execute from the same nonempty resident-byte state.
example (choice : Bool) : x86Step shrState Event.tau (post choice) :=
  x86Step_decode_choice shrState (.shrRI .b64 .rax 2) choice shrResident
    (decode_encode_shrRI .rax 2 [])
example : (post true).flags.of = true := by decide
example : (post false).flags.of = false := by decide
example : post true ≠ post false := by
  intro h
  have := congrArg (fun m : MachState => m.flags.of) h
  contradiction
example : (execInstr (.jcc .o 7) (post true)).rip ≠
    (execInstr (.jcc .o 7) (post false)).rip := by decide
example : (post true).regs .rax = 0x2000000000000000 := by decide
example : (post false).regs .rax = (post true).regs .rax := by decide
example : (post true).regs .rcx = 19 := by decide
example : (post true).flags.cf = true := by decide
example : (post true).flags.sf = false := by decide
example : (post true).flags.zf = false := by decide
example : (post true).flags.pf = true := by decide
example : (post true).rip = 4 := by decide

-- All defined count-one flags, including original sign bit for overflow.
example : shrFlags64 (filledMachState 0).flags 0x8000000000000003 1 false =
    { cf := true, zf := false, sf := false, of := true, pf := false } := by decide
example : shrFlags64 (filledMachState 0).flags 1 1 true =
    { cf := true, zf := true, sf := false, of := false, pf := true } := by decide

-- Masked-zero counts preserve incoming flags; 65 and 255 exercise wraparound.
example (old : Flags) : shrFlags64 old 123 64 true = old := rfl
example (old : Flags) : shrFlags64 old 123 128 false = old := rfl
example : (execInstrChoice (.shrRI .b64 .rax 64) shrState true).regs .rax =
    shrState.regs .rax := by decide
example : (execInstrChoice (.shrRI .b64 .rax 65) shrState false).regs .rax =
    0x4000000000000001 := by decide
example : (execInstrChoice (.shrRI .b64 .rax 255) shrState true).regs .rax = 1 := by decide

-- Reject truncation, wrong width, memory mode, other shifts, and count-register forms.
example : ([[], [0x48], [0x48, 0xC1], [0x48, 0xC1, 0xE8],
    [0x40, 0xC1, 0xE8, 1], [0x48, 0xC1, 0x28, 1],
    [0x48, 0xC1, 0xE0, 1], [0x48, 0xC1, 0xF8, 1],
    [0x48, 0xD3, 0xE8]] : List (List UInt8)).all (fun bs => (decode bs).isNone) = true := by decide

elab "#audit_shr" : command => do
  let env ← getEnv
  let names := [``shrCount64_lt, ``encode_shrRI_immediate, ``decode_encode_shrRI,
    ``execInstrChoice_false, ``execInstrChoice_shrRI_regs,
    ``execInstrChoice_shrRI_flags, ``execInstrChoice_shrRI_frame,
    ``x86Step_decode_choice, ``shrResident]
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  for name in names do
    unless env.contains name do throwError "missing {name}"
    let axioms := (← liftCoreM (Lean.collectAxioms name)).toList
    let extra := axioms.filter fun ax => !allowed.contains ax
    unless extra.isEmpty do throwError "forbidden axioms in {name}: {extra}"
  logInfo "SHR-CHECKS axioms=foundational-only declarations=9 prefixes=16 backend_cases=4096 resident_choices=2 decoder_refusals=9"
#audit_shr
