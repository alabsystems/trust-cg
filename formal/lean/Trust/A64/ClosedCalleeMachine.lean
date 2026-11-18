/- Copyright 2026 Andrew Yates | License: Apache-2.0 -/

import Trust.A64.ClosedCallee
import Trust.A64.Machine

namespace Trust
namespace A64

/-- Independent architectural classifier for the straight-line closed-callee profile.
    Unknown and out-of-profile instructions are classified as 3. -/
def closedCalleeKind : Instr → UInt32
  | .pcRel op .. => if op.val = 1 then 0 else 3
  | .addSubImm sf _ s .. => if sf.val = 1 && s.val = 0 then 0 else 3
  | .addSubShifted sf op s shift .. =>
      if sf.val = 1 && op.val = 0 && s.val = 0 && shift.val = 0 then 0 else 3
  | .logicalShifted _ opc shift n _ imm6 rn _ =>
      if opc.val = 1 && shift.val = 0 && n.val = 0 && imm6.val = 0 && rn.val = 31 then 0 else 3
  | .moveWide sf opc .. => if sf.val = 1 && (opc.val = 2 || opc.val = 3) then 0 else 3
  | .loadStoreUImm size v opc .. => if size.val = 3 && v.val = 0 && opc.val ≤ 1 then 0 else 3
  | .loadStorePair opc v mode l _ rt2 rn rt =>
      if opc.val = 2 && v.val = 0 && l.val = 0 &&
        (mode.val = 2 || (mode.val = 3 && (rn.val = 31 || (rn ≠ rt && rn ≠ rt2))))
      then 0 else 3
  | .bitfield sf opc n _ imms .. =>
      if sf.val = 1 && opc.val = 2 && n.val = 1 && imms.val = 63 then 0 else 3
  | .dataProc3 sf op31 _ o0 ra .. =>
      if (sf.val = 1 && op31.val = 6 && o0.val = 0 && ra.val = 31) ||
        (sf.val = 0 && op31.val = 0 && o0.val = 1) then 0 else 3
  | .branchImm op _ => if op.val = 1 then 1 else 3
  | .brk imm16 => if imm16.val = 1 then 2 else 3
  | _ => 3

def closedCalleeWordKind (word : UInt32) : UInt32 :=
  match decode word with
  | some i => closedCalleeKind i
  | none => 3

private theorem closedCallee_prefix (kind : UInt32) :
    trust_cg_a64_closed_callee_row kind 0 = 1 ↔ kind = 0 ∨ kind = 1 := by
  by_cases h : kind = 0 <;> simp [trust_cg_a64_closed_callee_row, h]

private theorem closedCallee_last (kind : UInt32) :
    trust_cg_a64_closed_callee_row kind 1 = 1 ↔ kind = 2 := by
  simp [trust_cg_a64_closed_callee_row]

private theorem writeX_pc (s : MachState) (r : Reg) (v : BitVec 64) :
    (s.writeX r v).pc = s.pc := by
  unfold MachState.writeX
  split <;> rfl

private theorem writeXSP_pc (s : MachState) (r : Reg) (v : BitVec 64) :
    (s.writeXSP r v).pc = s.pc := by
  unfold MachState.writeXSP
  split <;> rfl

private theorem writeMem_pc (s : MachState) (addr : BitVec 64) (v bytes : Nat) :
    (s.writeMem addr v bytes).pc = s.pc := by
  induction bytes generalizing s addr v with
  | zero => rfl
  | succ bytes ih => simp [MachState.writeMem, ih]

private theorem transfer_pc (size opc : Fin 4) (r : Reg) (addr : BitVec 64) (s : MachState) :
    (Exec.transfer size opc r addr s).pc = s.pc := by
  unfold Exec.transfer
  split <;> simp only [writeMem_pc, writeX_pc]

private theorem unknown_ne_fallthrough : (3 : UInt32) ≠ 0 := by decide
private theorem call_ne_fallthrough : (1 : UInt32) ≠ 0 := by decide
private theorem trap_ne_fallthrough : (2 : UInt32) ≠ 0 := by decide

/-- Successful execution of any admitted ordinary instruction advances its PC by one word. -/
theorem closedCallee_exec_advance (i : Instr) (s t : MachState)
    (kind : closedCalleeKind i = 0) (executed : exec i s = some t) :
    t.pc = s.pc + 4 := by
  have pc := congrArg (Option.map MachState.pc) executed
  simp only [exec, Option.map_some] at pc
  split at pc <;> try contradiction
  cases i <;> simp only [closedCalleeKind, unknown_ne_fallthrough] at kind
  all_goals try (split at kind <;> simp_all only [unknown_ne_fallthrough, call_ne_fallthrough,
      trap_ne_fallthrough])
  all_goals
    simp only [execValid] at pc
    repeat' (split at pc <;> try contradiction)
    all_goals
      simp only [Option.map_some, Option.some.injEq, MachState.advance, writeX_pc,
        writeXSP_pc, writeMem_pc, transfer_pc] at pc
      exact pc.symm

/-- The additional ordinary data instructions in the caller CFG profile. -/
def closedCallerExtra : Instr → Bool
  | .addSubShifted sf op s shift _ _ _ rd =>
      sf.val = 1 && op.val = 1 && s.val = 1 && shift.val = 0 && rd.val = 31
  | .dataProc3 sf op31 _ _ _ _ _ => sf.val = 1 && op31.val = 0
  | .dataProc2 sf _ opcode _ _ => sf.val = 1 && opcode.val = 2
  | .logicalImm sf opc n immr imms _ _ =>
      sf.val = 1 && opc.val = 1 && n.val = 1 && immr.val = 0 && imms.val = 0
  | _ => false

/-- The caller's additional data instructions also preserve ordinary fallthrough. -/
theorem closedCaller_extra_exec_advance (i : Instr) (s t : MachState)
    (supported : closedCallerExtra i = true) (executed : exec i s = some t) :
    t.pc = s.pc + 4 := by
  have pc := congrArg (Option.map MachState.pc) executed
  simp only [exec, Option.map_some] at pc
  split at pc <;> try contradiction
  cases i <;> simp [closedCallerExtra] at supported
  all_goals
    simp only [execValid] at pc
    repeat' (split at pc <;> try contradiction)
    all_goals
      simp only [Option.map_some, Option.some.injEq, MachState.advance, writeX_pc,
        writeXSP_pc] at pc
      exact pc.symm

/-- The exact admitted BRK has no architectural successor in this machine model. -/
theorem closedCallee_exec_trap (i : Instr) (s : MachState)
    (kind : closedCalleeKind i = 2) : exec i s = none := by
  cases i <;> simp [closedCalleeKind, exec, execValid] at kind ⊢ <;>
    split at kind <;> simp_all

private theorem closedCallee_bl_kind (imm26 : Fin 67108864) :
    closedCalleeKind (.branchImm 1 imm26) = 1 := rfl

/-- BL installs PC+4 in X30 before entering its decoded target. -/
theorem closedCallee_bl_link (imm26 : Fin 67108864) (s t : MachState)
    (executed : exec (.branchImm 1 imm26) s = some t) :
    t.readX 30 = s.pc + 4 := by
  have lrLive : (30 : Reg).val < 31 := by decide
  simpa [exec, Instr.valid, execValid, MachState.readX, MachState.writeX, lrLive] using
    congrArg (Option.map (fun next => next.readX 30)) executed.symm

/-- BL enters the target of the signed displacement decoded from the instruction. -/
theorem closedCallee_bl_target (imm26 : Fin 67108864) (s t : MachState)
    (executed : exec (.branchImm 1 imm26) s = some t) :
    t.pc = s.pc + BitVec.ofInt 64 (4 * sext 26 imm26.val) := by
  simpa [exec, Instr.valid, execValid] using
    congrArg (Option.map MachState.pc) executed.symm

/-- An ordinary external call may return to this activation only at its actual link address. -/
def OrdinaryCallReturn (returns : MachState → MachState → Prop) : Prop :=
  ∀ entry resumed, returns entry resumed → resumed.pc = entry.readX 30

/-- Successful transfers in the current activation. The address predicate is supplied
    by the linked extent check. Calls with no ordinary return have no local successor. -/
inductive ClosedCalleeStep (external : BitVec 64 → Prop)
    (returns : MachState → MachState → Prop) : Instr → MachState → MachState → Prop
  | ordinary {i s t} (notBL : ∀ imm26, i ≠ .branchImm 1 imm26)
      (executed : exec i s = some t) : ClosedCalleeStep external returns i s t
  | call {imm26 s entry resumed} (executed : exec (.branchImm 1 imm26) s = some entry)
      (outside : external entry.pc) (returned : returns entry resumed) :
      ClosedCalleeStep external returns (.branchImm 1 imm26) s resumed

private theorem closedCallee_kind_call (i : Instr) (kind : closedCalleeKind i = 1) :
    ∃ imm26, i = .branchImm 1 imm26 := by
  cases i <;> simp [closedCalleeKind] at kind
  all_goals try (split at kind <;> simp_all)
  rename_i op displacement
  have opIsLink : op = 1 := Fin.ext kind
  exact ⟨displacement, congrArg (fun op => Instr.branchImm op displacement) opIsLink⟩

/-- Every admitted prefix successor, including an ordinary BL return, is PC+4. -/
theorem closedCallee_prefix_pc {external : BitVec 64 → Prop}
    {returns : MachState → MachState → Prop} (abi : OrdinaryCallReturn returns)
    {i s t} (admitted : trust_cg_a64_closed_callee_row (closedCalleeKind i) 0 = 1)
    (step : ClosedCalleeStep external returns i s t) : t.pc = s.pc + 4 := by
  cases step with
  | ordinary notBL executed =>
    rcases (closedCallee_prefix _).mp admitted with kind | kind
    · exact closedCallee_exec_advance _ _ _ kind executed
    · obtain ⟨imm26, eq⟩ := closedCallee_kind_call _ kind
      exact (notBL imm26 eq).elim
  | call executed _ returned =>
    rw [abi _ _ returned]
    exact closedCallee_bl_link _ _ _ executed

/-- A final admitted trap never continues within the activation. -/
theorem closedCallee_last_no_step {external : BitVec 64 → Prop}
    {returns : MachState → MachState → Prop} {i s t}
    (admitted : trust_cg_a64_closed_callee_row (closedCalleeKind i) 1 = 1)
    (step : ClosedCalleeStep external returns i s t) : False := by
  have kind := (closedCallee_last _).mp admitted
  cases step with
  | ordinary _ executed => simp [closedCallee_exec_trap _ _ kind] at executed
  | call _ _ _ => simp [closedCallee_bl_kind] at kind

/-- Check the same row decision as Rust across a nonempty immutable decoded byte extent. -/
def closedCalleeWords : List UInt32 → Bool
  | [] => false
  | [word] => trust_cg_a64_closed_callee_row (closedCalleeWordKind word) 1 == 1
  | word :: next :: tail =>
      (trust_cg_a64_closed_callee_row (closedCalleeWordKind word) 0 == 1) &&
        closedCalleeWords (next :: tail)

/-- The immutable image maps consecutive instruction addresses to these words. -/
def closedCalleeExtent (image : BitVec 64 → Option UInt32) (pc : BitVec 64) :
    List UInt32 → Prop
  | [] => True
  | word :: tail => image pc = some word ∧ closedCalleeExtent image (pc + 4) tail

/-- Trace of an ordinary return of the current activation from the actual decoded PC.
    Every instruction must be fetched from the bound image in the architectural memory. -/
inductive ClosedCalleeReturns (image : BitVec 64 → Option UInt32)
    (external : BitVec 64 → Prop) (returns : MachState → MachState → Prop) : MachState → Prop
  | ret {word s rn t} (atPC : image s.pc = some word)
      (fetched : s.readMem s.pc 4 = word.toNat)
      (decoded : decode word = some (.branchReg 2 rn))
      (executed : exec (.branchReg 2 rn) s = some t) :
      ClosedCalleeReturns image external returns s
  | next {word i s t} (atPC : image s.pc = some word)
      (fetched : s.readMem s.pc 4 = word.toNat)
      (decoded : decode word = some i) (execution : ClosedCalleeStep external returns i s t)
      (after : ClosedCalleeReturns image external returns t) :
      ClosedCalleeReturns image external returns s

/-- An accepted immutable callee has no normal return to its caller. Each external call
    may return to its own link address or leave no local continuation. -/
theorem closedCallee_no_normal_return {image : BitVec 64 → Option UInt32}
    {external : BitVec 64 → Prop}
    {returns : MachState → MachState → Prop} {words : List UInt32} {s : MachState}
    (abi : OrdinaryCallReturn returns) (accepted : closedCalleeWords words = true)
    (placed : closedCalleeExtent image s.pc words) :
    ¬ ClosedCalleeReturns image external returns s := by
  induction words generalizing s with
  | nil => simp [closedCalleeWords] at accepted
  | cons first tail ih =>
    rcases placed with ⟨firstPC, restPC⟩
    intro trace
    cases trace with
    | ret atPC _ decoded _ =>
      have same := Option.some.inj (firstPC.symm.trans atPC)
      rw [← same] at decoded
      cases tail <;> simp [closedCalleeWords, closedCalleeWordKind, decoded,
        closedCalleeKind, trust_cg_a64_closed_callee_row] at accepted
    | @next _ i _ _ atPC _ decoded execution after =>
      have same := Option.some.inj (firstPC.symm.trans atPC)
      rw [← same] at decoded
      cases tail with
      | nil =>
        have terminal : trust_cg_a64_closed_callee_row (closedCalleeKind i) 1 = 1 := by
          simpa [closedCalleeWords, closedCalleeWordKind, decoded] using accepted
        exact closedCallee_last_no_step terminal execution
      | cons next tail =>
        simp only [closedCalleeWords, Bool.and_eq_true, beq_iff_eq] at accepted
        have advance := closedCallee_prefix_pc abi
          (by simpa [closedCalleeWordKind, decoded] using accepted.1) execution
        exact ih accepted.2 (by simpa only [advance] using restPC) after

end A64
end Trust
