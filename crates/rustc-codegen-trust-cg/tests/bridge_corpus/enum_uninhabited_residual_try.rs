// CORPUS FIXTURE — `?` whose RESIDUAL TYPE IS UNINHABITED, so the `from_residual`
// call is dead code.
//
// `core::array::from_fn` is `try_from_fn(NeverShortCircuit::wrap_mut_1(cb)).0`,
// and `Iterator::fold` is `try_fold::<_, _, NeverShortCircuit<_>>`.
// `NeverShortCircuit<T>`'s `Try::Residual` is `NeverShortCircuitResidual`, an
// EMPTY enum, and std's impl is literally
// `fn from_residual(never: NeverShortCircuitResidual) -> Self { match never {} }`.
// No value of an uninhabited type exists, so control can never reach that call —
// rustc simply does not always prune the `?` desugaring's Break arm, and the
// bridge lowers every CFG-reachable block including the dynamically dead ones.
//
// Measured on the unpatched integration backend: this fixture COMPILES at
// `-Copt-level=0` and fails closed at `-Copt-level=2` with
// `from_residual for an unmodeled Try type core::ops::try_trait::
// NeverShortCircuit (only Result/Option are lowered)` — an OPT-LEVEL-DEPENDENT
// refusal, which is the worst kind to leave in place. The `library/core` census
// counted 4 roots in this family (2 named `NeverShortCircuit`, 2 named
// `ControlFlow`, all in the same `try_from_fn` / `try_fold` chain).
//
// The values are checked against LLVM at both levels, so the dead-block model
// (an `Unreachable` where the impossible call was) is falsified if any of these
// blocks was in fact live.
//
// All correct -> exit 7.
#![no_std]
#![no_main]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! {
    loop {}
}

// `core`'s `-Copt-level=0` object references the personality routine even under
// `-Cpanic=abort`; a `no_std` binary has no libstd to supply it. Both backends
// link against this same stub, so the differential stays apples-to-apples.
#[no_mangle]
pub extern "C" fn rust_eh_personality() {}

use core::hint::black_box;

/// `array::from_fn` -> `try_from_fn::<NeverShortCircuit<u8>, 4, _>`.
#[inline(never)]
fn make(seed: u8) -> [u8; 4] {
    core::array::from_fn(|i| seed.wrapping_add(i as u8))
}

/// `Iterator::fold` -> `try_fold::<_, _, NeverShortCircuit<u32>>`.
#[inline(never)]
fn total(xs: &[u8]) -> u32 {
    xs.iter().fold(0u32, |a, b| a + u32::from(*b))
}

/// `Iterator::position` / `take_while` drive `try_fold` with a real
/// `ControlFlow` residual, the other half of the same chain.
#[inline(never)]
fn first_big(xs: &[u8]) -> usize {
    xs.iter().take_while(|b| **b < 12).count()
}

#[no_mangle]
pub extern "C" fn main() -> i32 {
    let a = make(black_box(10));
    let t = total(&a);
    let c = first_big(&a);
    if a[0] == 10 && a[3] == 13 && t == 46 && c == 2 {
        7
    } else {
        13
    }
}
