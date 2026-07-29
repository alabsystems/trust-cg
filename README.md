# trust-cg

A proof-oriented compiler backend in Rust for AArch64 and x86-64, with bounded RISC-V 64 AOT and WebAssembly paths.

trust-cg is made by [ALab](https://alab.systems). Its source code is not published:
this repository carries trust-cg's binary releases, their release notes, and its
license.

## Install

Install it with aterm's package manager, which verifies every signed binary:

```sh
aterm pkg install trust-cg
```

Every release is listed under [Releases](https://github.com/alabsystems/trust-cg/releases),
and its notes are in `release-notes/`.

## License

trust-cg is licensed under the ALab Academic Use License 1.0 (`LICENSE`). It may be used
free of charge for non-commercial teaching, academic research and personal
study. Any other use, including any use by or for a company, needs a
commercial license from ALab: see [alab.systems](https://alab.systems).

Third-party components keep their own licenses; see `NOTICE`.
