/- Copyright 2026 Andrew Yates | License: Apache-2.0 -/

/-- Wrapping addition used by a matched I64 counter step. -/
def trust_cg_a64_trap_counter_step (counter increment : UInt64) : UInt64 :=
  counter + increment

theorem trust_cg_a64_trap_counter_step_body (counter increment : UInt64) :
    trust_cg_a64_trap_counter_step counter increment = counter + increment := rfl

/-- A trap following a call executes when the exit edge is taken and the call returns. -/
def trust_cg_a64_trap_after_return (exitTaken returned : Bool) : Bool :=
  exitTaken && returned

theorem trust_cg_a64_trap_after_return_body (exitTaken returned : Bool) :
    trust_cg_a64_trap_after_return exitTaken returned = (exitTaken && returned) := rfl

theorem trust_cg_a64_trap_counter_step_sync
    (source machine sourceIncrement machineIncrement : UInt64)
    (counter : source = machine) (increment : sourceIncrement = machineIncrement) :
    source + sourceIncrement = trust_cg_a64_trap_counter_step machine machineIncrement := by
  rw [counter, increment]
  rfl

def trust_cg_a64_trap_source_counter_after (initial increment : UInt64) (steps : Nat) : UInt64 :=
  Nat.rec initial (fun _ counter => counter + increment) steps

def trust_cg_a64_trap_machine_counter_after (initial increment : UInt64) (steps : Nat) : UInt64 :=
  Nat.rec initial (fun _ counter => trust_cg_a64_trap_counter_step counter increment) steps

/-- Equal initial counters and increments give equal counters after any finite number of
    matched back edges. The arithmetic is modular at every step. -/
theorem trust_cg_a64_trap_counter_sync (source machine sourceIncrement machineIncrement : UInt64)
    (steps : Nat) (entry : source = machine) (increment : sourceIncrement = machineIncrement) :
    trust_cg_a64_trap_source_counter_after source sourceIncrement steps =
      trust_cg_a64_trap_machine_counter_after machine machineIncrement steps := by
  rw [entry, increment]
  rfl

theorem trust_cg_a64_trap_counter_guard_sync
    (source machine sourceIncrement machineIncrement sourceBound machineBound : UInt64)
    (steps : Nat) (entry : source = machine) (increment : sourceIncrement = machineIncrement)
    (bound : sourceBound = machineBound) :
    (decide (trust_cg_a64_trap_source_counter_after source sourceIncrement steps < sourceBound) :
      Bool) =
      decide (trust_cg_a64_trap_machine_counter_after machine machineIncrement steps < machineBound) := by
  rw [trust_cg_a64_trap_counter_sync source machine sourceIncrement machineIncrement
    steps entry increment, bound]

/-- The source continues on true. The machine takes the complementary exit edge and traps
    on its return continuation. This compares corresponding normal-return events. -/
theorem trust_cg_a64_trap_continuation_sync
    (sourceContinue machineExit sourceReturned machineReturned : Bool)
    (exitMatches : machineExit = !sourceContinue)
    (returnMatches : sourceReturned = machineReturned) :
    (if sourceContinue then false else sourceReturned) =
      trust_cg_a64_trap_after_return machineExit machineReturned := by
  rw [exitMatches, returnMatches]
  cases sourceContinue <;> cases machineReturned <;> rfl

/-- Trap agreement at a matched header visit, with an unsigned bound and corresponding
    call return events. The visit count describes the matched finite prefix. -/
theorem trust_cg_a64_trap_after_matched_steps
    (source machine sourceIncrement machineIncrement sourceBound machineBound : UInt64)
    (steps : Nat) (sourceReturned machineReturned : Bool)
    (entry : source = machine) (increment : sourceIncrement = machineIncrement)
    (bound : sourceBound = machineBound) (returnMatches : sourceReturned = machineReturned) :
    (if (decide (trust_cg_a64_trap_source_counter_after source sourceIncrement steps <
      sourceBound) : Bool) then false else sourceReturned) =
      trust_cg_a64_trap_after_return
        (!(decide (trust_cg_a64_trap_machine_counter_after machine machineIncrement steps <
          machineBound) : Bool)) machineReturned :=
  trust_cg_a64_trap_continuation_sync _ _ _ _
    (congrArg (fun test : Bool => !test)
      (trust_cg_a64_trap_counter_guard_sync source machine sourceIncrement machineIncrement
        sourceBound machineBound steps entry increment bound).symm)
    returnMatches
