# Bind and execute the original scalar-cell C-driver PIEs

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

The linked-image checker previously accepted only static executables, while
the original native ABI drivers link as Linux position-independent executables
with a dynamic loader and real C callbacks. It now checks that supported PIE
format, retaining the same exact caller words and uniquely resolved direct
callback targets. `is_position_independent()` distinguishes the address model;
ELF virtual addresses need a common aligned, non-wrapping runtime load bias.

The six C fixtures are generated unchanged from the maintained private bridge
driver generator. They retain its globals, observations, helper calls, libc
calls and byte comparisons. The extraction source, original harness snapshot,
six generated Rust inputs, compiler command, source hashes and all C drivers
are retained. The f32 read driver also matches the original blocked bridge
run byte for byte. No leaf substitute or reduced observation set is used.

## Checked boundary

The parser checks one Linux AArch64 interpreter and dynamic header, the exact
dynamic section/file mapping, bounded dynamic strings and symbols, and both
ordinary and PLT RELA tables. The supported ABS64, GLOB_DAT, JUMP_SLOT and
RELATIVE relocation destinations must be aligned, disjoint eight-byte extents
entirely within writable non-executable loads. Dynamic tables and reserved GOT
slots cannot be overwritten by relocations; relocation/symbol/string tables
must themselves be file-backed and non-writable. The loader's DEBUG and GOT
slots also have checked writable extents. The relocation kinds and widths
follow [Arm AAELF64](https://github.com/ARM-software/abi-aa/blob/main/aaelf64/aaelf64.rst).
Unknown dynamic tags, TEXTREL, REL/RELR, COPY, IRELATIVE, image-defined IFUNCs,
TLS extensions and unsupported flags are refused. Static images retain their
stricter profile. A high-virtual-address regression checks mapping arithmetic
without an overflowing intermediate sum, plus range and permission failures.

This is **diagnostic correspondence and bounded native testing**. It grants no
production instruction proof credit. Callers are emitted with pipeline
verification disabled; the proof-enabled private ABI gate still refuses
`[TCG-PROOF-465]`. There is no callback semantic/ABI theorem, complete ELF or
loader validation, initializer/dependency theorem, or full-system completion.
In particular, checking these relocation write extents does not prove all
effects of the runtime loader, dependencies or their IFUNC resolvers.

## Executed evidence

The final run uses the exact combined source above parent `c6501b5fc`, which
includes incoming AY byte-identity changes. Immutable Trust `ae9c2c1da`, genuine
developmental `targo --unverified`, one build job and a 16 GiB group limit are
recorded. No solver query is run by this qualification. GNU cc/ld build the
PIEs with `-O0 -fPIE -pie -Wl,-z,now -Wl,-z,noexecstack -Wl,--build-id=none`;
the original caller captures retain their O0–O3 settings. Actual compiler,
assembler, linker, loader and libc executable hashes are recorded.

- All 24 original callers bind to their real C callback bodies and execute
  successfully: 408 calls and 5,712 checks in each qualification round.
- All 52 PIE metadata/relocation mutations are refused, including attempted
  writes into caller/callback text, dynamic metadata and reserved GOT slots;
  duplicate writes; unsupported resolver/copy relocations; and overflow.
- All seven linked-image integration tests pass, retaining the prior 24
  static callers, sixteen chained variants, 144 wrong-target controls,
  66 static metadata controls and 1,024 bounded corruptions.
- The high-address unit regression, all five original object/byte integration
  tests, the verifier all-targets check and maintained root formatting pass.
  Listed and executed test names agree, with none ignored in these Rust runs.
- The maintained Linux target minimum increases from five to seven. Its
  inventory and AArch64/x86-64 runner/host-matrix tests pass. The full
  168-family floor and private ABI bridge are not rerun or relabeled here.

The first run passed on parent `f76ef2863`. Review then found the intermediate
address-sum overflow; the second fixes it and passes the new regression on the
combined incoming main. The initial formatting syntax error and its corrected
run are retained. The first runner/result also retain a contradictory inherited
sentence denying native execution; its separately archived scope clarification
corrects that sentence without rewriting the original records. Actual native
stdout and stderr are retained for every executed PIE in both rounds.

`records/` preserves both runs' sources, commands, output and process-guard
results. Each deterministic tar contains every generated link input, linked
image and native output. `manifest.json` and `inventory.json` bind raw and
compressed sizes and SHA-256 digests. The extraction binary is identified by
hash in its capture result; its source and generated bytes are archived.

## Reproduction

On Linux AArch64 with genuine Trust, `cc`, `as` and `ld.lld` available:

```sh
targo --unverified test --locked -j 1 -p trust-cg-verify --lib source_bound_frame::cell_link::dynamic::tests:: -- --test-threads=1
targo --unverified test --locked -j 1 -p trust-cg-verify --test aarch64_scalar_cell_link -- --include-ignored --test-threads=1 --nocapture
targo --unverified test --locked -j 1 -p trust-cg-verify --test aarch64_scalar_cell_bytes -- --include-ignored --test-threads=1
targo --unverified check --locked -j 1 -p trust-cg-verify --all-targets
bash scripts/check_fmt.sh
```

The retained runner also binds exact tool hashes, uses `--offline`, compares
listed/executed names, and checks source hashes before and after every command.
Missing tools fail instead of skipping the tests.
