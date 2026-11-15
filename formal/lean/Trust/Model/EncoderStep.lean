/-
  Model.EncoderStep — the `x86Step_decode` keystone and the `LoweredStep` builders over it.

  Author: Andrew Yates
  Copyright 2026 Andrew Yates | License: Apache-2.0

  `Trust.Model` defines `x86Step` as fetch∘decode∘execInstr over `Model.Encoder`. The keystone
  `x86Step_decode` (resident encoded bytes that round-trip through `decode` take one `x86Step`
  into `execInstr`) was an explicit axiom while `x86Step` was opaque; here it is a theorem whose
  proof exhibits the fetched bytes. It says nothing about hardware: that the model's
  `decode`/`execInstr` are what an x86-64 processor does remains a modelling assumption outside
  Lean, bound only by the enumerated encoder golden matrix (for `encode`) and by nothing for
  `execInstr`.
-/
import Trust.Model
import Trust.Cert.Obligation
import Trust.Model.Encoder

namespace Trust
namespace Model
namespace Encoder

open Trust

/-! ## 1.  The keystone, now a theorem of the definition. -/

/-- THE BRIDGE. Resident encoded bytes that `decode` reads back completely take one model
    `x86Step` into `execInstr`. Proved from the definition of `x86Step`; formerly an axiom. -/
theorem x86Step_decode
    (m : MachState) (i : Instr)
    (hfetch : BytesAt m m.rip (encode i))
    (hdec   : decode (encode i) = some (i, [])) :
    x86Step m (eventOf i) (execInstr i m) :=
  ⟨encode i, i, hfetch, hdec, rfl, false, (execInstrChoice_false i m).symm⟩

/-- Resident bytes permit every represented architectural OF choice. -/
theorem x86Step_decode_choice
    (m : MachState) (i : Instr) (undefinedOF : Bool)
    (hfetch : BytesAt m m.rip (encode i))
    (hdec : decode (encode i) = some (i, [])) :
    x86Step m (eventOf i) (execInstrChoice i m undefinedOF) :=
  ⟨encode i, i, hfetch, hdec, rfl, undefinedOF, rfl⟩

theorem step_emitted
    (m : MachState) (i : Instr)
    (hfetch : BytesAt m m.rip (encode i))
    (hrt    : decode (encode i) = some (i, [])) :
    x86Step m (eventOf i) (execInstr i m) :=
  x86Step_decode m i hfetch hrt

theorem stepPlus_emitted
    (m : MachState) (i : Instr)
    (hfetch : BytesAt m m.rip (encode i))
    (hrt    : decode (encode i) = some (i, [])) :
    x86StepPlus m (eventOf i) (execInstr i m) :=
  x86StepPlus.single (step_emitted m i hfetch hrt)

theorem runs_of_resident
    (i : Instr) (m : MachState)
    (hres : BytesAt m m.rip (encode i))
    (hrt  : decode (encode i) = some (i, [])) :
    x86StepPlus m (eventOf i) (execInstr i m) :=
  stepPlus_emitted m i hres hrt

/-! ## 2. Building a lowered step on resident encoded bytes.

    Residency is an entry condition, not a claim about every possible memory.
    Each instruction certificate must establish it for its incoming matching
    state. A concrete resident-state witness rules out an empty admission domain.
    `ResidentEverywhere` is retained only as a refuted negative control. -/

def ResidentEverywhere (i : Instr) : Prop := ∀ m, BytesAt m m.rip (encode i)

def singleInstrStep
    (i : Instr)
    (hres : ∃ m, BytesAt m m.rip (encode i))
    (hrt  : decode (encode i) = some (i, [])) :
    LoweredStep :=
  { exec  := execInstr i
  , event := eventOf i
  , entry := fun m => BytesAt m m.rip (encode i)
  , entry_nonempty := hres
  , runs  := fun m hm => stepPlus_emitted m i hm hrt }

def singleInstrStep_regreg
    (i : Instr)
    (hform : ∃ sz dst src,
        sz = OSize.b64 ∧
        (i = .movRR sz dst src ∨ i = .addRR sz dst src ∨ i = .adcRR sz dst src ∨
         i = .subRR sz dst src ∨ i = .sbbRR sz dst src ∨ i = .cmpRR sz dst src ∨
         i = .testRR sz dst src ∨ i = .andRR sz dst src ∨ i = .orRR sz dst src ∨
         i = .xorRR sz dst src))
    (hres : ∃ m, BytesAt m m.rip (encode i)) :
    LoweredStep :=
  singleInstrStep i hres (decode_encode_regreg i hform)

/-- Full-width immediate load on an explicitly nonempty resident-byte domain. -/
def singleInstrStep_movabsRI
    (dst : GPR) (imm : BitVec 64)
    (hres : ∃ m, BytesAt m m.rip (encode (.movabsRI dst imm))) : LoweredStep :=
  singleInstrStep (.movabsRI dst imm) hres (decode_encode_movabsRI dst imm [])

/-- The machine state whose registers, flags and `rip` are zero and whose every memory byte is
    `fill`. -/
def filledMachState (fill : BitVec 8) : MachState :=
  { regs := fun _ => 0, xmms := fun _ => 0
  , flags := { cf := false, zf := false, sf := false, of := false, pf := false }
  , mem := fun _ => fill, rip := 0 }

/-- Every encoding is at least one byte long. -/
theorem encode_ne_nil (i : Instr) : encode i ≠ [] := by
  cases i <;> simp [encode, encInstr, le32, le8]

/-- No instruction is resident in every machine state (a state whose memory is all `0x00` and one
    whose memory is all `0x01` disagree on the first byte), so `ResidentEverywhere` is never
    satisfiable. The guarded `singleInstrStep` requires only one resident witness. -/
theorem not_residentEverywhere (i : Instr) : ¬ ResidentEverywhere i := by
  intro h
  cases henc : encode i with
  | nil => exact encode_ne_nil i henc
  | cons b rest =>
      have h0 := h (filledMachState 0)
      have h1 := h (filledMachState 1)
      rw [henc] at h0 h1
      have e0 : (0 : BitVec 8) = BitVec.ofNat 8 b.toNat := h0.1
      have e1 : (1 : BitVec 8) = BitVec.ofNat 8 b.toNat := h1.1
      have : (0 : BitVec 8) = 1 := e0.trans e1.symm
      exact absurd this (by decide)

/-! ## 3. A concrete, non-vacuous resident execution. -/

/-- `48 89 c0` is the actual modeled encoding of `MOV RAX,RAX`, at address zero. -/
def movSelfState : MachState :=
  { filledMachState 0 with
    mem := fun a => if a = 0 then 0x48 else if a = 1 then 0x89 else if a = 2 then 0xc0 else 0 }

theorem movSelfState_resident :
    BytesAt movSelfState movSelfState.rip (encode (.movRR .b64 .rax .rax)) := by
  exact ⟨rfl, rfl, rfl, True.intro⟩

/-- Unlike `ResidentEverywhere`, this constructor has an actual resident-state witness. -/
def movSelfStep : LoweredStep :=
  singleInstrStep_regreg (.movRR .b64 .rax .rax)
    ⟨.b64, .rax, .rax, rfl, Or.inl rfl⟩ ⟨movSelfState, movSelfState_resident⟩

theorem loweredStep_nonempty : Nonempty LoweredStep := ⟨movSelfStep⟩

theorem movSelfStep_runs :
    x86StepPlus movSelfState Event.tau (movSelfStep.exec movSelfState) :=
  movSelfStep.runs movSelfState movSelfState_resident

theorem movSelfStep_advances : (movSelfStep.exec movSelfState).rip = 3 := by
  decide

theorem movSelfStep_preserves_memory (a : BitVec 64) :
    (movSelfStep.exec movSelfState).mem a = movSelfState.mem a := by
  rfl

theorem movSelfStep_rejects_zero_memory : ¬ movSelfStep.entry (filledMachState 0) := by
  intro h
  have hfirst : (0 : BitVec 8) = 0x48 := h.1
  exact (by decide : (0 : BitVec 8) ≠ 0x48) hfirst


/-! ## 4. A resident instruction certificate with an actual incoming matching state. -/

def movWitnessLayout : Layout :=
  { asgn := fun _ => .reg .rax, kind := fun _ => .int 64 (by omega), lowerOf := id
  , entryAddr := fun block => BitVec.ofNat 64 (3 * block), nonFrame := fun _ => True }

def movWitnessSource : SrcState :=
  { env := fun _ => .int 64 (by omega) 0, mem := movSelfState.mem
  , pc := 0, live := fun v => v = 0 }

def movWitnessSuccessor : SrcState := { movWitnessSource with pc := 1 }

theorem movSelfStep_effect (m : MachState) :
    movSelfStep.exec m = { m with rip := m.rip + 3 } := by
  change { m with regs := fun q => if q = GPR.rax then m.regs .rax else m.regs q,
                  rip := m.rip + 3 } = _
  have hr : (fun q => if q = GPR.rax then m.regs .rax else m.regs q) = m.regs := by
    funext q
    split <;> simp_all
  rw [hr]

theorem movWitness_initial : R movWitnessLayout movWitnessSource movSelfState where
  realize := by intro v hv; rfl
  carrier := by intro v hv; rfl
  memAgree := by intro a ha; rfl
  pcSync := rfl

/-- Every guard and semantic leg is discharged; no certificate field is left as an assumption. -/
def movWitnessCert :
    InstrCert movWitnessLayout movSelfStep movWitnessSource movWitnessSuccessor where
  entryReady := by
    intro m hR
    have hp : m.rip = 0 := hR.pcSync
    have hm : ∀ a, m.mem a = movSelfState.mem a :=
      fun a => (hR.memAgree a True.intro).symm
    change BytesAt m m.rip [0x48, 0x89, 0xc0]
    rw [hp]
    exact ⟨hm 0, hm 1, hm 2, True.intro⟩
  value := by
    intro m hR v hv
    rw [movSelfStep_effect]
    exact hR.realize v hv
  clobber := by
    intro m hR
    rw [movSelfStep_effect]
    exact ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ => rfl, fun _ _ => rfl⟩
  carrierOk := by
    intro m hR
    rw [movSelfStep_effect]
    exact hR.carrier
  memOk := by
    intro m hR
    rw [movSelfStep_effect]
    exact hR.memAgree
  pcOk := by
    intro m hR
    rw [movSelfStep_effect]
    have hp : m.rip = 0 := hR.pcSync
    change m.rip + 3 = 3
    simp [hp]

/-- The uniform certificate bridge executes on a concrete matching, code-resident input. -/
theorem movWitness_certified_execution :
    x86StepPlus movSelfState Event.tau (movSelfStep.exec movSelfState) ∧
      R movWitnessLayout movWitnessSuccessor (movSelfStep.exec movSelfState) :=
  cert_reestablishes_R movWitnessCert movWitness_initial

end Encoder
end Model
end Trust
