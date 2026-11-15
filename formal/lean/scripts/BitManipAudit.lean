/- Focused audit: the SWAR value proof may use only the three foundational axioms. -/
import Lean
import Trust.Cert.BitManip
open Lean Elab Command

#check (Trust.Cert.BitManip.popcnt32_swar_correct :
  ∀ x : BitVec 32, Trust.Cert.BitManip.popcnt32Swar x = x.cpop)
#check (Trust.Cert.BitManip.popcnt64_swar_correct :
  ∀ x : BitVec 64, Trust.Cert.BitManip.popcnt64Swar x = x.cpop)

elab "#audit_bitmanip" : command => do
  let env ← getEnv
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  let mut checked := 0
  let mut problems : Array String := #[]
  for (name, _) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    let mod := env.header.moduleNames[index.toNat]!
    unless (`Trust.Cert.BitManip).isPrefixOf mod do continue
    if name.isInternal then continue
    checked := checked + 1
    let axioms := (← liftCoreM (Lean.collectAxioms name)).toList
    let extra := axioms.filter fun ax => !allowed.contains ax
    unless extra.isEmpty do problems := problems.push s!"{name}: {extra}"
  if checked == 0 then throwError "BITMANIP-AUDIT empty declaration census"
  for name in [`Trust.Cert.BitManip.popcnt32_swar_correct,
      `Trust.Cert.BitManip.popcnt64_swar_correct] do
    unless env.contains name do throwError "BITMANIP-AUDIT missing {name}"
  unless problems.isEmpty do throwError m!"BITMANIP-AUDIT forbidden dependencies: {problems}"
  logInfo s!"BITMANIP-AUDIT declarations={checked} sorryAx=0 project_axioms=0 native_axioms=0 widths=32,64"

#audit_bitmanip
