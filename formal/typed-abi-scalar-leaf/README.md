# Conditional scalar return transport

This component carries forward the Lean portion of the retained
`7e198a82d8fd86eacfb2a973a44bcd9c35c9cf72` draft. Its theorem statements,
descriptor predicates and decoded copy model are preserved. Lean 4.8 repairs
replace an unbounded simplifier step with explicit constructor reasoning,
avoid a reserved binder name, prove range membership from the core definition,
and use the core bounded list-lookup theorem. Control literals use valid
Lean 4.8 layout.

The component imports the real TrustIR `Control`, `Arith` and `Eval` semantics.
The retained component's recorded qualification used the backend's then-published TrustIR pin,
`bfeee98bf1968b7e17a2694fa1fd5e7b94947eaa`, and its declared
`leanprover/lean4:v4.8.0` toolchain. The old draft's archived `af531667` semantics
are useful historical comparison evidence, not a replacement dependency pin.
The backend pin has since advanced independently. This recorded component
qualification does not apply to another TrustIR revision; rerun the kernel
checks below against the integration's exact pin before claiming that scope.

## Proven relation and its limits

`scalar_leaf_return` relates a real source Return ValueId and its defined I64
value to the result of a complete decoded copy sequence. The signature retains
all source Parameter bindings and Result(0), direct eight-byte scalar carriers,
one to eight arguments, nonvariadic/non-unwinding C or Rust convention, and the
bounded little-endian AArch64 header predicate. Negative and high-bit values
use TrustIR's actual `truncateUnsigned` encoding.

The entry-register relation is an explicit premise. Target/frontend identity,
the actual AArch64 ABI classifier, refinement of decoded ORR copies to independent
instruction semantics, source-to-LIR extraction, Rust checker refinement, and
complete frame/SP/private-memory/return-continuation authority remain separate
obligations. The copy theorem preserves registers outside X0 through X17;
that result alone does not establish a whole native calling contract.

The Rust extractor and its broader consumer changes still need a deliberate
forward port. Production typed applicability refusals and publication gates
remain in force. This formal component grants no compiler, cache, emitted-code,
performance or whole-corpus authority.

## Reproduce the kernel checks

Use the exact pinned Lean 4.8 binaries and the exact pinned TrustIR semantics.
Some development environments route the unqualified `lean` name to another
tool, so name the selected Lean and Lake executables explicitly.

1. In the pinned TrustIR `lean/trust_ir-semantics` project, run the selected
   Lake executable with `build TrustIr`.
2. In this directory, set `LEAN_PATH` for each Lean subprocess to that exact
   project's `.lake/build/lib` plus this directory. Compile
   `ScalarReturnTransport.lean` and `ScalarReturnTransportControls.lean` with
   the selected Lean executable, producing their matching `.olean` files.
3. Check all thirteen printed theorem axiom inventories. The permitted core
   inventory is `propext`, `Classical.choice` and `Quot.sound`; `sorryAx`,
   native evaluation axioms and additional assumptions are not admitted.
4. Run each file in `negative/` separately. All three must fail because their
   asserted source, width or metadata equality is false. Missing imports or
   unavailable tools do not count as successful negative controls.

Positive controls cover real Return semantics, descriptor bindings, decoded
moves, high-bit encodings, malformed scalar scopes, and the existing typed
execution and indirect-call refusals. The three negative files preserve the
original deliberately false statements. Constructed fixtures are regression
inputs, not captured production compiler bodies.
