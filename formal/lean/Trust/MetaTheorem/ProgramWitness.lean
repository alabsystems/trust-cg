/-
  An inhabited, program-indexed compiler contract: the source's unconditional self-loop
  is simulated by the resident x86 JMP -5 (e9 fb ff ff ff), for every finite run.
  This is a model witness, not a claim that the Rust compiler produced this program.
  Copyright 2026 Andrew Yates. Apache 2.0.
-/
import Trust.MetaTheorem.CompileRefines
import Trust.Model.EncoderStep
import Trust.MetaTheorem.Vacuity

namespace Trust.MetaTheorem.ProgramWitness

open Trust Trust.Model.Encoder Trust.Sim.ForwardSim

def machine : MachState :=
  { filledMachState 0 with
    mem := fun a => if a = 0 then 0xe9 else if a = 1 then 0xfb
      else if a = 2 ∨ a = 3 ∨ a = 4 then 0xff else 0 }

theorem resident : BytesAt machine machine.rip (encode (.jmp (-5))) := by
  change BytesAt machine 0 [0xe9, 0xfb, 0xff, 0xff, 0xff]
  exact ⟨rfl, rfl, rfl, rfl, rfl, trivial⟩

def step : LoweredStep :=
  singleInstrStep (.jmp (-5)) ⟨machine, resident⟩
    (by simpa using decode_encode_jmp (-5) [])

theorem effect (m : MachState) : step.exec m = m := by
  change { m with rip := m.rip + 5 + (-5 : BitVec 32).signExtend 64 } = m
  have hz : (5 : BitVec 64) + (-5 : BitVec 32).signExtend 64 = 0 := by decide
  rw [BitVec.add_assoc, hz]
  simp

def source : SrcState :=
  { env := fun _ => .int 64 (by omega) 0, mem := machine.mem
  , pc := 0, live := fun v => v = 0 }

def code : Source.Program := ⟨fun _ => some (.term (.br 0 []))⟩

def layout : Layout :=
  { asgn := fun _ => .reg .rax, kind := fun _ => .int 64 (by omega)
  , lowerOf := id, entryAddr := fun _ => 0, nonFrame := fun _ => True }

theorem initial : R layout source machine where
  realize := by intro v hv; rfl
  carrier := by intro v hv; rfl
  memAgree := by intro a ha; rfl
  pcSync := rfl

def transition : PureTransition layout source source where
  vDst := 0
  w := 64
  hw := by omega
  rDst := .rax
  hkind := rfl
  hasgn := rfl
  liveDst := rfl
  envOther := by intro v hv hn; exact False.elim (hn hv)
  otherRegDistinct := by intro v hv hn; exact False.elim (hn hv)
  otherPairDistinct := by intro v hv hn; exact False.elim (hn hv)

def frame : PureFrame layout step source source transition where
  entryReady := by
    intro m hR
    have hp : m.rip = 0 := hR.pcSync
    have hm : ∀ a, m.mem a = machine.mem a := fun a => (hR.memAgree a trivial).symm
    change BytesAt m m.rip [0xe9, 0xfb, 0xff, 0xff, 0xff]
    rw [hp]
    exact ⟨hm 0, hm 1, hm 2, hm 3, hm 4, trivial⟩
  dstDenotes := by
    intro m hR
    rw [effect]
    exact hR.realize 0 rfl
  dstCarrier := by intro m hR; rw [effect]; simp [transition]
  execOtherReg := by intro m r hr; rw [effect]
  execXmms := by intro m x; rw [effect]
  execMem := by intro m a; rw [effect]
  pcAdvance := by intro m hR; rw [effect]; exact hR.pcSync

def operation : OpKind layout source source :=
  .pure step transition frame
    (by intro m hR; rw [effect]; exact ⟨fun _ _ => rfl, fun _ _ => rfl,
      fun _ => rfl, fun _ _ => rfl⟩)
    (fun _ => rfl) rfl

theorem source_step : srcStep code source .tau source := by
  simp [srcStep, Source.SrcStep, Source.nextStep, code, source, Source.execute,
    Source.gotoWith]

/-- One actual source step is forced to the fetched branch and cannot become an observable. -/
theorem source_step_only {ev : Event} {s' : SrcState}
    (h : srcStep code source ev s') : ev = .tau ∧ s' = source :=
  Source.step_deterministic h source_step

def program : Program :=
  { sourceCode := code, entryS := source, entryM := machine, lay := layout, rEntry := initial }

/-- The premise holds for all finite source runs, not just a selected certified trace. -/
theorem certified : Certified_compile program := by
  have certify : ∀ {start evs sf}, srcRun code start evs sf → start = source →
      CertRun code layout start evs sf := by
    intro start evs sf hrun
    induction hrun with
    | nil => intro hs; exact CertRun.nil
    | cons hstep rest ih =>
        intro hs
        subst hs
        obtain ⟨rfl, rfl⟩ := source_step_only hstep
        exact CertRun.cons hstep operation rfl (ih rfl)
  intro sf evs hrun
  exact certify hrun rfl

theorem nonempty_certified_run : CertRun code layout source [.tau] source :=
  CertRun.cons source_step operation rfl CertRun.nil

theorem actual_machine_step : x86StepPlus machine .tau machine := by
  have h := step.runs machine resident
  change x86StepPlus machine .tau (step.exec machine) at h
  rw [effect] at h
  exact h

theorem refinement : Refines (x86Sem program) (srcSem program) :=
  compile_refines program certified

/-! Dispatch and terminal-state controls use finite programs with observable outcomes. -/

def arithmeticCode : Source.Program := Source.Program.ofList
  [.instr (.bin 0 .add 64 (by omega) (.const 64 (by omega) 40) (.const 64 (by omega) 2)),
   .term .ret]

def arithmeticMid : SrcState := Source.setEnv (Source.bumpPC source) 0 (.int 64 (by omega) 42)

def arithmeticFinal : SrcState := { arithmeticMid with halted := true }

theorem arithmetic_step : srcStep arithmeticCode source .tau arithmeticMid := rfl

theorem arithmetic_return : srcStep arithmeticCode arithmeticMid .ret arithmeticFinal := rfl

theorem arithmetic_trace : srcRun arithmeticCode source [.tau, .ret] arithmeticFinal :=
  srcRun.cons arithmetic_step (srcRun.cons arithmetic_return srcRun.nil)

theorem arithmetic_does_not_call (target : BitVec 64) (s' : SrcState) :
    ¬ srcStep arithmeticCode source (.call target) s' := by
  intro h
  cases (Source.step_deterministic arithmetic_step h).1

theorem return_does_not_trap (s' : SrcState) :
    ¬ srcStep arithmeticCode arithmeticMid .trap s' :=
  Source.ret_cannot_trap rfl rfl

theorem returned_state_is_terminal (event : Event) (s' : SrcState) :
    ¬ srcStep arithmeticCode arithmeticFinal event s' := Source.halted_no_step rfl

def divideByZero : Source.Program := Source.Program.ofList
  [.instr (.bin 0 .udiv 64 (by omega) (.const 64 (by omega) 42) (.const 64 (by omega) 0))]

theorem division_fault_is_local :
    srcStep divideByZero source .trap { source with halted := true } := rfl

def wrongWidth : Source.Program := Source.Program.ofList
  [.instr (.bin 0 .add 64 (by omega) (.const 32 (by omega) 40) (.const 64 (by omega) 2))]

theorem operand_width_mismatch_faults :
    srcStep wrongWidth source .trap { source with halted := true } := rfl

theorem missing_instruction_faults :
    srcStep (Source.Program.ofList []) source .trap { source with halted := true } := rfl

/-- A fixed instruction map cannot borrow the step of a different program. -/
theorem programs_cannot_exchange_steps : ¬ srcStep arithmeticCode source .tau source := by
  intro h
  have states := (Source.step_deterministic arithmetic_step h).2
  have pcs := congrArg SrcState.pc states
  change (1 : Nat) = 0 at pcs
  omega

def compareBranchCode : Source.Program := Source.Program.ofList
  [.instr (.icmp 0 .eq 64 (by omega) (.const 64 (by omega) 4) (.const 64 (by omega) 4)),
   .term (.condbr (.name 0) 3 2 [] []), .trap, .term .ret]

def compareMid : SrcState := Source.setEnv (Source.bumpPC source) 0 (.int 8 (by omega) 1)

def compareTaken : SrcState := { compareMid with pc := 3 }

theorem comparison_can_feed_a_branch :
    srcRun compareBranchCode source [.tau, .tau, .ret]
      { compareTaken with halted := true } :=
  srcRun.cons (by rfl) (srcRun.cons (by rfl) (srcRun.cons (by rfl) srcRun.nil))

def noncanonicalBoolean : Source.Program := Source.Program.ofList
  [.term (.condbr (.const 8 (by omega) 2) 3 2 [] [])]

theorem noncanonical_boolean_faults :
    srcStep noncanonicalBoolean source .trap { source with halted := true } := rfl

def falseBranchCode : Source.Program := Source.Program.ofList
  [.instr (.icmp 0 .eq 64 (by omega) (.const 64 (by omega) 4) (.const 64 (by omega) 5)),
   .term (.condbr (.name 0) 3 2 [] []), .term .ret, .trap]

def falseMid : SrcState := Source.setEnv (Source.bumpPC source) 0 (.int 8 (by omega) 0)

def falseTaken : SrcState := { falseMid with pc := 2 }

theorem false_comparison_takes_the_other_arm :
    srcRun falseBranchCode source [.tau, .tau, .ret]
      { falseTaken with halted := true } :=
  srcRun.cons (by rfl) (srcRun.cons (by rfl) (srcRun.cons (by rfl) srcRun.nil))

theorem one_bit_condition_is_supported :
    srcStep (Source.Program.ofList [.term (.condbr (.const 1 (by omega) 1) 3 2 [] [])])
      source .tau { source with pc := 3 } := rfl

def trappingProgram : Program := { program with sourceCode := ⟨fun _ => some .trap⟩ }

/-- A real matching initial state does not hide the missing observable machine step. -/
theorem trapping_program_not_certified : ¬ Certified_compile trappingProgram :=
  Vacuity.certified_compile_unsatisfiable trappingProgram rfl rfl

theorem trapping_program_not_refined :
    ¬ Refines (x86Sem trappingProgram) (srcSem trappingProgram) :=
  Vacuity.not_refines trappingProgram rfl rfl

def signedOverflowCode (op : Source.BinOp) : Source.Program := Source.Program.ofList
  [.instr (.bin 0 op 8 (by omega) (.const 8 (by omega) (-128)) (.const 8 (by omega) (-1)))]

theorem signed_division_overflow_faults :
    srcStep (signedOverflowCode .sdiv) source .trap { source with halted := true } := rfl

theorem signed_remainder_overflow_faults :
    srcStep (signedOverflowCode .srem) source .trap { source with halted := true } := rfl

def signedNeighborCode : Source.Program := Source.Program.ofList
  [.instr (.bin 0 .sdiv 8 (by omega) (.const 8 (by omega) (-127)) (.const 8 (by omega) (-1)))]

theorem signed_division_neighbor_is_defined :
    srcStep signedNeighborCode source .tau
      (Source.setEnv (Source.bumpPC source) 0 (.int 8 (by omega) 127)) := rfl

def signedMinimumByOne : Source.Program := Source.Program.ofList
  [.instr (.bin 0 .sdiv 8 (by omega) (.const 8 (by omega) (-128)) (.const 8 (by omega) 1))]

theorem signed_minimum_by_one_is_defined :
    srcStep signedMinimumByOne source .tau
      (Source.setEnv (Source.bumpPC source) 0 (.int 8 (by omega) (-128))) := rfl

theorem unsigned_boundary_is_not_a_signed_fault :
    srcStep (signedOverflowCode .udiv) source .tau
      (Source.setEnv (Source.bumpPC source) 0 (.int 8 (by omega) 0)) ∧
    srcStep (signedOverflowCode .urem) source .tau
      (Source.setEnv (Source.bumpPC source) 0 (.int 8 (by omega) 128)) := by
  constructor <;> rfl

def signedWordOverflowCode (op : Source.BinOp) : Source.Program := Source.Program.ofList
  [.instr (.bin 0 op 64 (by omega)
    (.const 64 (by omega) (-9223372036854775808)) (.const 64 (by omega) (-1)))]

theorem signed_word_division_and_remainder_overflow_fault :
    srcStep (signedWordOverflowCode .sdiv) source .trap { source with halted := true } ∧
    srcStep (signedWordOverflowCode .srem) source .trap { source with halted := true } := by
  constructor <;> rfl

end Trust.MetaTheorem.ProgramWitness
