import Lean
import Trust.Model.EncoderStep
import Trust.Model.MovabsGolden
open Trust Trust.Model.Encoder Lean Elab Command

private def maskState : MachState :=
  { filledMachState 0 with mem := fun a =>
      if a = 0 then 0x49 else if a = 1 then 0xBF else if a.toNat < 10 then 0x55 else 0 }

private theorem maskResident :
    BytesAt maskState maskState.rip (encode (.movabsRI .r15 0x5555555555555555)) := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, True.intro⟩

private def maskStep : LoweredStep :=
  singleInstrStep_movabsRI .r15 0x5555555555555555 ⟨maskState, maskResident⟩

example : x86StepPlus maskState Event.tau (maskStep.exec maskState) :=
  maskStep.runs maskState maskResident
example : (maskStep.exec maskState).regs .r15 = 0x5555555555555555 := by decide
example : (maskStep.exec maskState).rip = 10 := by decide
example : (maskStep.exec maskState).regs .rax = maskState.regs .rax := by decide
example : ¬ maskStep.entry (filledMachState 0) := by
  intro h
  exact (by decide : (0 : BitVec 8) ≠ 0x49) h.1

-- Every truncated immediate (0 through 7 bytes), low and high register banks.
example : ([0x48, 0x49] : List UInt8).all (fun rex =>
    (List.range 8).all (fun n =>
      (decode ([rex, 0xBF] ++ (List.replicate n 0x55))).isNone)) = true := by decide
-- Missing REX.W continues to be refused.
example : (List.range 16).all (fun n =>
    (decode ([if n < 8 then 0x40 else 0x41, UInt8.ofNat (0xB8 + n % 8)] ++
      List.replicate 8 0x55)).isNone) = true := by decide
-- Wrong opcode family does not become an immediate move.
example : (decode ([0x48, 0xB0] ++ List.replicate 8 0x55)).isNone = true := by decide

elab "#audit_movabs" : command => do
  let env ← getEnv
  let names := [``ofLe64_le64, ``decode_encode_movabsRI,
    ``execInstr_movabsRI_regs, ``execInstr_movabsRI_frame, ``execInstr_movabsRI_rip,
    ``singleInstrStep_movabsRI, ``maskResident]
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  for name in names do
    unless env.contains name do throwError "missing {name}"
    let axioms := (← liftCoreM (Lean.collectAxioms name)).toList
    let extra := axioms.filter fun ax => !allowed.contains ax
    unless extra.isEmpty do throwError "forbidden axiom in {name}: {extra}"
  logInfo "MOVABS-CHECKS axioms=foundational-only declarations=7 golden_vectors=96 truncated=16 nonwide=16 resident_execution=1"
#audit_movabs
