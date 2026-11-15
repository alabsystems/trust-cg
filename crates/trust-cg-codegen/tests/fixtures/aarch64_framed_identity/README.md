# Captured framed identity

This unchanged 329-byte TrustIR module was captured from the real O0 `b1_mispredict` proof-required bridge compilation at CG `adaf378f80df05e09a7f77d48e4dce1b145f16fb`, using the maintained tracked `dump-aarch64-prepared` observer. Its SHA-256 is `2e89a9608cba4e145d775fc0f73ef099a77169d438e90cdf154726c266f73f6d`.

It is the actual monomorphized `core::hint::black_box::<u64>` body: copy the input, jump to the return block, and return the copy. The captured AArch64 body has a 16-byte FP/LR frame and one B+1 between its blocks. Before the repair its sole uncovered opcode was that B.

The snapshot is diagnostic input, not proof or encoding authority. The regression runs the real compiler and certificate-promotion policy. Its explicit test-only raw-body licence grants no Rust NoUB, frontend, whole-compiler or performance claim.
