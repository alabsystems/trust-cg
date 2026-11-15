-- Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0
-- Conditional scalar transport component. Production admission remains separate.
-- Imports the pinned TrustIR SignatureAbi and Return semantics.
import TrustIr.Semantics.Control
import TrustIr.Semantics.Arith

namespace TrustIr.TypedAbiScalarLeafDraft

/-- The same complete word decoder as the Rust test-only draft. The equation
    checks every instruction bit; W writes, SP/ZR and shifted ORR refuse. -/
structure Move where
  destination : Nat
  source : Nat
  deriving Repr, DecidableEq

def decodeMove (word : Nat) : Option Move :=
  let destination := word % 32
  let source := (word / 65536) % 32
  if destination < 18 ∧ source < 18 ∧
      word = 0xaa0003e0 + destination + source * 65536 then
    some { destination, source }
  else none

abbrev Origins := Nat → Option Nat
/-- Hardware bitpatterns use the existing TrustIR modulo-width Int encoding.
    Known source arguments are seeded with truncateUnsigned value 64. -/
abbrev Registers := Nat → Int

def write {α : Type} (state : Nat → α) (destination : Nat) (value : α) : Nat → α :=
  fun register => if register = destination then value else state register

/-- Abstract execution mirrors route_words exactly. Unknown scratch registers
    remain unknown, even though hardware contains arbitrary bits there. -/
def runOrigins : List Nat → Origins → Option Origins
  | [], state => some state
  | word :: rest, state => do
      let instruction ← decodeMove word
      let origin ← state instruction.source
      runOrigins rest (write state instruction.destination (some origin))

/-- Actual 64-bit copy semantics of the decoded unshifted ORR alias.
    The body does not touch SP, flags or memory. Frame effects are separate. -/
def runRegisters : List Nat → Registers → Option Registers
  | [], state => some state
  | word :: rest, state => do
      let instruction ← decodeMove word
      runRegisters rest
        (write state instruction.destination (state instruction.source))

def seedOrigins (count : Nat) : Origins :=
  fun register => if register < count then some register else none

/-- Every known register has the value of its particular source argument.
    Inputs are independent bitpatterns; no aggregate/checksum condition occurs. -/
def Realizes (inputs : Nat → Int) (origins : Origins) (registers : Registers) : Prop :=
  ∀ register input, origins register = some input → registers register = inputs input

theorem seed_realizes (count : Nat) (inputs : Nat → Int) (registers : Registers)
    (entry : ∀ index, index < count → registers index = inputs index) :
    Realizes inputs (seedOrigins count) registers := by
  intro register input known
  by_cases inside : register < count
  · simp [seedOrigins, inside] at known
    subst input
    exact entry register inside
  · simp [seedOrigins, inside] at known

theorem move_realizes (inputs : Nat → Int) (origins : Origins)
    (registers : Registers) (instruction : Move) (origin : Nat)
    (known : origins instruction.source = some origin)
    (before : Realizes inputs origins registers) :
    Realizes inputs (write origins instruction.destination (some origin))
      (write registers instruction.destination (registers instruction.source)) := by
  intro register input after
  by_cases destination : register = instruction.destination
  · subst register
    simp [write] at after
    subst input
    simpa [write] using before instruction.source origin known
  · have old : origins register = some input := by simpa [write, destination] using after
    simpa [write, destination] using before register input old

/-- Refinement of the complete origin checker to decoded body execution. -/
theorem run_refines (words : List Nat) (inputs : Nat → Int)
    (origins final : Origins) (registers : Registers)
    (checked : runOrigins words origins = some final)
    (before : Realizes inputs origins registers) :
    ∃ output, runRegisters words registers = some output ∧ Realizes inputs final output := by
  induction words generalizing origins registers with
  | nil =>
      simp [runOrigins] at checked
      subst final
      exact ⟨registers, rfl, before⟩
  | cons word rest induction =>
      cases decoded : decodeMove word with
      | none => simp [runOrigins, decoded] at checked
      | some instruction =>
          cases known : origins instruction.source with
          | none => simp [runOrigins, decoded, known] at checked
          | some origin =>
              have next : runOrigins rest
                  (write origins instruction.destination (some origin)) = some final := by
                simpa [runOrigins, decoded, known] using checked
              obtain ⟨output, result, realizes⟩ := induction _ _ next
                (move_realizes inputs origins registers instruction origin known before)
              exact ⟨output, by simpa [runRegisters, decoded] using result, realizes⟩

theorem decoded_destination_bound (word : Nat) (instruction : Move)
    (checked : decodeMove word = some instruction) : instruction.destination < 18 := by
  dsimp [decodeMove] at checked
  split at checked
  · rename_i admitted
    have equal := Option.some.inj checked
    cases equal
    exact admitted.1
  · cases checked

/-- Caller scratch may change. Every register outside X0..X17 is unchanged by
    this whole body, so protected registers cannot be hidden in a move alias. -/
theorem protected_registers (words : List Nat) (registers output : Registers)
    (executed : runRegisters words registers = some output)
    (register : Nat) (outside : 18 ≤ register) : output register = registers register := by
  induction words generalizing registers with
  | nil =>
      simp [runRegisters] at executed
      subst output
      rfl
  | cons word rest induction =>
      cases decoded : decodeMove word with
      | none => simp [runRegisters, decoded] at executed
      | some instruction =>
          have bound := decoded_destination_bound word instruction decoded
          have distinct : register ≠ instruction.destination := by
            intro equal
            subst register
            exact Nat.not_lt_of_ge outside bound
          have next : runRegisters rest
              (write registers instruction.destination (registers instruction.source)) = some output := by
            simpa [runRegisters, decoded] using executed
          simpa [write, distinct] using induction _ next

def scalar64Core (argument : AbiArgument) : Bool :=
  match argument.mode with
  | .Direct scalar =>
      argument.size == 8 && argument.align == 8 &&
      scalar.register.regClass == .Integer && scalar.register.bytes == 8 &&
      scalar.sourceOffset == 0 && scalar.sourceBytes == 8 && scalar.valueBits == 64 &&
      scalar.attributes.extension == .None && !scalar.attributes.inReg &&
      !scalar.attributes.noAlias && !scalar.attributes.nonnull &&
      !scalar.attributes.readonly && !scalar.attributes.writable &&
      !scalar.attributes.noFree && scalar.attributes.capture == .Any &&
      scalar.attributes.pointeeSize == 0 && scalar.attributes.pointeeAlign.isNone
  | _ => false

def parameter64 (argument : AbiArgument) (index : Nat) : Bool :=
  match argument.bindings with
  | [binding] =>
      match binding.place with
      | .Parameter actual => scalar64Core argument && actual == index &&
          binding.sourceOffset == 0 && binding.sourceBytes == 8 &&
          binding.carrierOffset == 0 && binding.carrierBytes == 8
      | _ => false
  | _ => false

def result64 (argument : AbiArgument) : Bool :=
  match argument.bindings with
  | [binding] =>
      match binding.place with
      | .Result index => scalar64Core argument && index == 0 &&
          binding.sourceOffset == 0 && binding.sourceBytes == 8 &&
          binding.carrierOffset == 0 && binding.carrierBytes == 8
      | _ => false
  | _ => false

def parameterBindingIndex (argument : AbiArgument) : Option Nat :=
  match argument.bindings with
  | [binding] => match binding.place with
      | .Parameter index => some index
      | _ => none
  | _ => none

def resultBindingIndex (argument : AbiArgument) : Option Nat :=
  match argument.bindings with
  | [binding] => match binding.place with
      | .Result index => some index
      | _ => none
  | _ => none

def parameterScope (arguments : List AbiArgument) (count : Nat) : Bool :=
  (List.range count).all fun index =>
    match arguments[index]? with
    | some argument => parameter64 argument index
    | none => false

/-- Interpretation consumes the actual retained SignatureAbi, including every
    source argument. Target/frontend measurement is mandatory external custody;
    this scope predicate does not certify those producer identity claims. -/
def scalarHeader (abi : SignatureAbi) (count : Nat) : Bool :=
  decide (1 ≤ count ∧ count ≤ 8) && abi.target.triple.startsWith "aarch64-" &&
  abi.target.pointerBytes == 8 && abi.target.littleEndian &&
  (abi.convention == "C" || abi.convention == "Rust") && abi.sourceAbi == abi.convention &&
  ((abi.convention == "C" && abi.loweredConvention == .C) ||
    (abi.convention == "Rust" && abi.loweredConvention == .Rust)) &&
  !abi.canUnwind && !abi.variadic && abi.fixedCount == count

def scalarScope (abi : SignatureAbi) (count : Nat) : Bool :=
  scalarHeader abi count &&
    (abi.arguments.length == count &&
      (parameterScope abi.arguments count && result64 abi.result))

theorem parameter64_binds_position (argument : AbiArgument) (index : Nat)
    (checked : parameter64 argument index = true) :
    parameterBindingIndex argument = some index := by
  cases argument with
  | mk size align mode bindings =>
      cases bindings with
      | nil => simp [parameter64] at checked
      | cons binding rest =>
          cases rest with
          | cons other tail => simp [parameter64] at checked
          | nil =>
              cases binding with
              | mk place sourceOffset sourceBytes carrierOffset carrierBytes =>
                  cases place <;> simp_all [parameter64, parameterBindingIndex]

theorem result64_binds_zero (argument : AbiArgument)
    (checked : result64 argument = true) : resultBindingIndex argument = some 0 := by
  cases argument with
  | mk size align mode bindings =>
      cases bindings with
      | nil => simp [result64] at checked
      | cons binding rest =>
          cases rest with
          | cons other tail => simp [result64] at checked
          | nil =>
              cases binding with
              | mk place sourceOffset sourceBytes carrierOffset carrierBytes =>
                  cases place <;> simp_all [result64, resultBindingIndex]

theorem scope_result_position (abi : SignatureAbi) (count : Nat)
    (checked : scalarScope abi count = true) : resultBindingIndex abi.result = some 0 := by
  simp only [scalarScope, Bool.and_eq_true] at checked
  exact result64_binds_zero abi.result checked.2.2.2

private theorem range_member (count index : Nat) (inside : index < count) :
    index ∈ List.range count := by
  have loop_member (n : Nat) (rest : List Nat) :
      index ∈ List.range.loop n rest ↔ index < n ∨ index ∈ rest := by
    induction n generalizing rest with
    | zero =>
        change index ∈ rest ↔ index < 0 ∨ index ∈ rest
        constructor
        · exact Or.inr
        · intro present
          cases present with
          | inl impossible => exact False.elim (Nat.not_lt_zero _ impossible)
          | inr old => exact old
    | succ n induction =>
        rw [List.range.loop, induction]
        simp only [List.mem_cons]
        constructor
        · intro present
          rcases present with lower | equal | old
          · exact Or.inl (Nat.lt_trans lower (Nat.lt_succ_self n))
          · exact Or.inl (equal ▸ Nat.lt_succ_self n)
          · exact Or.inr old
        · intro present
          cases present with
          | inl bound =>
              cases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ bound) with
              | inl lower => exact Or.inl lower
              | inr equal => exact Or.inr (Or.inl equal)
          | inr old => exact Or.inr (Or.inr old)
  exact (loop_member count []).2 (Or.inl inside)

theorem parameter_scope_binds_all (arguments : List AbiArgument) (count index : Nat)
    (argument : AbiArgument) (checked : parameterScope arguments count = true)
    (inside : index < count) (source : arguments[index]? = some argument) :
    parameterBindingIndex argument = some index := by
  have all := List.all_eq_true.mp checked index (range_member count index inside)
  simp [source] at all
  exact parameter64_binds_position argument index all

/-- Entry interpretation is indexed through actual descriptor bindings. It
    does not assume that a raw SSA id or a carrier number is a source index. -/
def EntryTransport (abi : SignatureAbi) (inputs : Nat → Int)
    (registers : Registers) : Prop :=
  ∀ source argument carrier, abi.arguments[source]? = some argument →
    parameterBindingIndex argument = some carrier → registers carrier = inputs source

private theorem list_get_some {α : Type} (values : List α) (index : Nat)
    (inside : index < values.length) : ∃ value, values[index]? = some value := by
  exact ⟨values[index]'inside, getElem?_pos values index inside⟩

/-- Refinement of every retained source Parameter binding to actual X0..X7
    entry positions, independent of the backend's allocation classifier. -/
theorem scope_entry_positions (abi : SignatureAbi) (count : Nat)
    (inputs : Nat → Int) (registers : Registers)
    (scope : scalarScope abi count = true)
    (transport : EntryTransport abi inputs registers) :
    ∀ index, index < count → registers index = inputs index := by
  simp only [scalarScope, Bool.and_eq_true] at scope
  have checked : parameterScope abi.arguments count = true := scope.2.2.1
  have countEq : abi.arguments.length = count := by simpa using scope.2.1
  intro index inside
  have present : index < abi.arguments.length := by simpa [countEq] using inside
  obtain ⟨argument, lookup⟩ := list_get_some abi.arguments index present
  exact transport index argument index lookup
    (parameter_scope_binds_all abi.arguments count index argument checked inside lookup)

/-- Source values are bound by their real ValueIds and their positions in the
    actual entry block. No arithmetic property of an SSA number is used. -/
def EntryBindings (state : MachineState) (ids : List ValueId)
    (values : Nat → Int) : Prop :=
  ∀ index id, ids[index]? = some id →
    state.lookupValue id = some (.int 64 (values index))

theorem actual_return (state : MachineState) (id : ValueId) (value : Int)
    (source : state.lookupValue id = some (.int 64 value)) :
    Sem.run (semReturn [id]) state = .ok (.Ret [.int 64 value], state) := by
  have lookup : Sem.run (Sem.lookupValue id) state = .ok (.int 64 value, state) := by
    simp [Sem.run, Sem.lookupValue, source, Sem.getState, bind, StateT.bind,
      StateT.get, StateT.run, pure, StateT.pure, Except.bind, Except.pure]
  simp only [semReturn, List.mapM, List.mapM.loop, Sem.run_bind, lookup,
    Except.bind, Sem.run_pure, List.reverse_cons, List.reverse_nil, List.nil_append]

theorem returned_value_defined (state : MachineState) (value : Int) :
    Sem.run (Sem.rejectPoisonValues [.int 64 value] "return") state = .ok ((), state) := rfl

/-- Conditional whole-copy-body transport theorem. It connects the real
    SignatureAbi source census, actual Return ValueId, all decoded machine
    words and arbitrary independent inputs. The official typed evaluator and
    production proof refusals are unchanged. Complete frame replay, frontend /
    target custody and refinement of the Rust extractor remain mandatory. -/
theorem scalar_leaf_return (abi : SignatureAbi) (count position : Nat)
    (ids : List ValueId) (id : ValueId) (words : List Nat)
    (values : Nat → Int) (state : MachineState)
    (registers : Registers) (final : Origins)
    (scope : scalarScope abi count = true)
    (_count : ids.length = count) (_inside : position < count)
    (sourceId : ids[position]? = some id)
    (sourceValues : EntryBindings state ids values)
    (entry : EntryTransport abi (fun index => truncateUnsigned (values index) 64) registers)
    (checked : runOrigins words (seedOrigins count) = some final)
    (returned : final 0 = some position) :
    ∃ output, runRegisters words registers = some output ∧
      output 0 = truncateUnsigned (values position) 64 ∧
      resultBindingIndex abi.result = some 0 ∧
      Sem.run (semReturn [id]) state = .ok
        (.Ret [.int 64 (values position)], state) := by
  let inputs := fun index => truncateUnsigned (values index) 64
  obtain ⟨output, executed, realizes⟩ := run_refines words inputs
    (seedOrigins count) final registers checked (seed_realizes count inputs registers
      (scope_entry_positions abi count inputs registers scope entry))
  have result : output 0 = inputs position := realizes 0 position returned
  exact ⟨output, executed, result, scope_result_position abi count scope,
    actual_return state id (values position) (sourceValues position id sourceId)⟩

end TrustIr.TypedAbiScalarLeafDraft
