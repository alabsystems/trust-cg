# Captured nonleaf entry wrapper

This is the unchanged 335-byte `main` module captured by the maintained
`dump-aarch64-prepared` observer during the O0 `b1_mispredict` native bridge
attempt on 2026-11-08. SHA-256:
`93ea449463b5ff823f0975ac7b9b51e16696b45bbb4f048b9879eb46c64dd459`.

The final captured AArch64 function has a 16-byte FP/LR frame and one direct
call to the monomorphized `std::rt::lang_start::<()>`. Its proof context is
empty. The call ABI facts describe AAPCS64 register preservation, zero stack
arguments, and no hidden result pointer. They supply no callee memory-write
contract or saved-slot preservation proof.

The regression compiles this exact input diagnostically, then requests real
proof promotion and requires the call to remain unproved. Both invocations
use explicit test-only raw-body permission, which grants no proof, Rust NoUB,
frontend, installed-image, or performance authority. This snapshot is input,
not proof authority. A future positive requires actual callee evidence; the
existing leaf frame theorem alone must never supply it.

The unchanged 1263-byte `lang_start.trust_irbin` is the isolated
`std::rt::lang_start::<()>` module from the same attempt. SHA-256:
`bee80af8fb92368f9674cb6d7ff4f2ebaa0a6c92eac42d2e1263abb94e2b1930`.
It is one of the nine diagnosed refusals: a 32-byte frame with one direct call
to the external `std::rt::lang_start_internal`. The C entry wrapper above was
captured too, but is not one of those nine diagnosed functions. The regression
checks the same diagnostic-success/proof-refusal distinction for both inputs.
