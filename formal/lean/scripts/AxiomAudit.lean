/-
  AxiomAudit — the soundness gate's environment audit of the `Trust` library.

  Run from `formal/lean` after `lake build`:

      lake env lean scripts/AxiomAudit.lean

  It walks every declaration of every `Trust.*` module, collects the axioms each depends on
  (what `#print axioms` shows), and FAILS (non-zero exit) when

    * any declaration depends on `sorryAx`, however the `sorry` was written (`by sorry`,
      `:= sorry`, `admit`, a macro) — the source-line `sorry` count misses these;
    * any declaration depends on an axiom other than Lean's `propext`, `Classical.choice` and
      `Quot.sound` or a `bv_decide` native-evaluation axiom (`<decl>._native.bv_decide.ax_*`),
      however that axiom was declared;
    * the capstone `Trust.MetaTheorem.compile_refines` depends on anything beyond the three
      standard axioms;
    * the walk finds no declaration or no capstone (a vacuous audit).

  `bv_decide` native-evaluation axioms are additional trusted dependencies (they trust the
  compiled evaluator); the audit counts them and the declarations using them but does not pin the
  number. On success it prints one `AXIOM-AUDIT` line the gate checks.
  Copyright 2026 Andrew Yates. Apache 2.0.
-/
import Lean
import Trust

open Lean Elab Command

namespace TrustAxiomAudit

def standardAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- `bv_decide`'s per-proof native-evaluation axioms are named `<decl>._native.bv_decide.ax_*`. -/
def isBvDecideNative (n : Name) : Bool :=
  (n.toString.splitOn "._native.bv_decide.ax_").length == 2

def capstone : Name := `Trust.MetaTheorem.compile_refines

elab "#audit_trust_axioms" : command => do
  let env ← getEnv
  let mut total := 0
  let mut sorryUsers : Array Name := #[]
  let mut projectAxiomUsers : Array (Name × List Name) := #[]
  let mut natives : Std.HashSet Name := {}
  let mut nativeUsers := 0
  for (n, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? n | continue
    let mod := env.header.moduleNames[idx.toNat]!
    unless (`Trust).isPrefixOf mod do continue
    if n.isInternal then continue
    total := total + 1
    let axs := (← liftCoreM (Lean.collectAxioms n)).toList
    if axs.contains ``sorryAx then
      sorryUsers := sorryUsers.push n
    let project := axs.filter fun a =>
      !standardAxioms.contains a && !isBvDecideNative a && a != ``sorryAx
    unless project.isEmpty do
      projectAxiomUsers := projectAxiomUsers.push (n, project)
    let nat := axs.filter isBvDecideNative
    unless nat.isEmpty do
      nativeUsers := nativeUsers + 1
      for a in nat do natives := natives.insert a
  if total == 0 then
    throwError "AXIOM-AUDIT FAIL: no declaration of a Trust.* module was found (vacuous audit)"
  unless env.contains capstone do
    throwError "AXIOM-AUDIT FAIL: the capstone {capstone} is not in the environment"
  let cap := (← liftCoreM (Lean.collectAxioms capstone)).toList
  let capExtra := cap.filter fun a => !standardAxioms.contains a
  let mut problems : Array String := #[]
  for n in sorryUsers do
    problems := problems.push s!"sorryAx <- {n}"
  for (n, axs) in projectAxiomUsers do
    problems := problems.push s!"project axiom(s) {axs} <- {n}"
  unless capExtra.isEmpty do
    problems := problems.push s!"capstone {capstone} depends on {capExtra}"
  unless problems.isEmpty do
    throwError m!"AXIOM-AUDIT FAIL: {problems.size} finding(s):\n{"\n".intercalate problems.toList}"
  logInfo s!"AXIOM-AUDIT declarations={total} sorryAx=0 project_axioms=0 \
    native_bv_decide_axioms={natives.size} native_dependents={nativeUsers} capstone={cap}"

end TrustAxiomAudit

#audit_trust_axioms
