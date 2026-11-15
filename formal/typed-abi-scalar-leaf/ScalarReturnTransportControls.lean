-- Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0
-- Pure kernel controls for the conditional scalar transport component.
import ScalarReturnTransport
import TrustIr.Semantics.Eval

namespace TrustIr.TypedAbiScalarLeafDraft

def fixtureAttributes : AbiAttributes :=
  { extension := .None, inReg := false, noAlias := false, nonnull := false,
    readonly := false, noUndef := true, writable := false, noFree := false,
    capture := .Any, pointeeSize := 0, pointeeAlign := none }

def fixtureScalar : AbiScalar :=
  { register := { regClass := .Integer, bytes := 8 }, sourceOffset := 0,
    sourceBytes := 8, valueBits := 64, attributes := fixtureAttributes }

def fixtureArgument (place : AbiBindingPlace) : AbiArgument :=
  { size := 8, align := 8, mode := .Direct fixtureScalar,
    bindings :=
      [{ place := place, sourceOffset := 0, sourceBytes := 8, carrierOffset := 0, carrierBytes := 8 }] }

/-- A test claim, not measured target/frontend authority. -/
def fixtureAbi : SignatureAbi :=
  { target :=
      { triple := "aarch64-unknown-linux-gnu"
        dataLayout := "e-p:64:64"
        abi := "aapcs64"
        cpu := "fixture-baseline"
        features := []
        targetSpec := "sha256:0000000000000000000000000000000000000000000000000000000000000000"
        pointerBytes := 8
        littleEndian := true },
    frontend := { name := "trustc", revision := "0000000000000000000000000000000000000000" },
    convention := "C", loweredConvention := .C, sourceAbi := "C", canUnwind := false,
    variadic := false, fixedCount := 2,
    arguments := [fixtureArgument (.Parameter 0), fixtureArgument (.Parameter 1)],
    result := fixtureArgument (.Result 0) }

example : scalarScope fixtureAbi 2 = true := by decide
example : decodeMove 0xaa0103f1 = some { destination := 17, source := 1 } := by decide
example : decodeMove 0x2a0103f1 = none := by decide
example : decodeMove 0xaa0107f1 = none := by decide
example : decodeMove 0xaa1f03e0 = none := by decide
example : decodeMove 0xaa0103f3 = none := by decide

example : ((runOrigins [0xaa0103f1, 0xaa1103e0] (seedOrigins 2)).bind
    (fun registers => registers 0)) = some 1 := by decide
example : ((runOrigins [0xaa0003f1, 0xaa1103e0] (seedOrigins 2)).bind
    (fun registers => registers 0)) = some 0 := by decide
example : runOrigins [0xaa0203e0] (seedOrigins 2) = none := rfl

example : parameter64 (fixtureArgument (.Parameter 1)) 0 = false := by decide
example : parameter64 { fixtureArgument (.Parameter 0) with bindings := [] } 0 = false := by decide
example : parameter64 { fixtureArgument (.Parameter 0) with bindings :=
    [{ place := .Parameter 0, sourceOffset := 0, sourceBytes := 8, carrierOffset := 1, carrierBytes := 8 }] } 0 = false := by decide
example : result64 (fixtureArgument (.HiddenResult 0)) = false := by decide
example : scalarScope { fixtureAbi with variadic := true } 2 = false := by decide
example : scalarScope { fixtureAbi with canUnwind := true } 2 = false := by decide
example : scalarScope { fixtureAbi with loweredConvention := .Rust } 2 = false := by decide
example : scalarScope { fixtureAbi with fixedCount := 1 } 2 = false := by decide
example : scalarScope { fixtureAbi with target := { fixtureAbi.target with littleEndian := false } } 2
    = false := by decide
example : scalarScope { fixtureAbi with arguments :=
    [fixtureArgument (.Parameter 1), fixtureArgument (.Parameter 0)] } 2 = false := by decide
example : scalar64Core { fixtureArgument (.Parameter 0) with
    mode := .Direct { fixtureScalar with attributes := { fixtureAttributes with extension := .Sign } } }
    = false := by decide
example : scalar64Core { fixtureArgument (.Parameter 0) with
    mode := .Direct { fixtureScalar with valueBits := 32 } } = false := by decide

/-- Negative and unsigned high-bit inputs use the actual modulo-width encoder. -/
example : truncateUnsigned (-1) 64 = 18446744073709551615 := by decide
example : truncateUnsigned 9223372036854775808 64 = 9223372036854775808 := by decide

/-- Actual source ValueId is 91, not ABI position 0 or 1. -/
def sourceState : MachineState :=
  { MachineState.empty with locals := ValueMap.empty.set (ValueId.mk 91) (.int 64 (-1)) }

example : Sem.run (semReturn [ValueId.mk 91]) sourceState =
    .ok (.Ret [.int 64 (-1)], sourceState) := by
  apply actual_return
  simp [sourceState, MachineState.lookupValue, ValueMap.empty, ValueMap.get, ValueMap.set]

/-- Official executable and indirect-call guards remain fail closed. -/
example (abi : SignatureAbi) (state : MachineState) :
    Sem.run (requireUntypedAbi (some abi)) state =
      .error (.unsupported .interproceduralCall "typed ABI transport semantics unsupported") := rfl
example (sig : FuncTyDef) (body : FuncBody) (abi : SignatureAbi) :
    checkIndirectSignature { sig with abi := some abi } body =
      .error "typed ABI transport semantics unsupported" := rfl

#print axioms seed_realizes
#print axioms move_realizes
#print axioms run_refines
#print axioms decoded_destination_bound
#print axioms protected_registers
#print axioms parameter64_binds_position
#print axioms result64_binds_zero
#print axioms scope_entry_positions
#print axioms scope_result_position
#print axioms parameter_scope_binds_all
#print axioms actual_return
#print axioms returned_value_defined
#print axioms scalar_leaf_return

end TrustIr.TypedAbiScalarLeafDraft
