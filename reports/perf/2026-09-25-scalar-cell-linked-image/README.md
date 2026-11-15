# Bind scalar-cell callers to a static linked image

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> The gzipped captures were removed earlier; their last commit is
> `ea8492fd9315ed8863af166657fed1b75bcf2c93`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

The checked relocatable caller previously stopped at ET_REL bytes and CALL26
records. `check_aarch64_scalar_cell_link` now independently reads a bounded
static AArch64 ELF64 executable, checks every unchanged non-call instruction,
and resolves every BL directly to its uniquely named ordinary callback.
The returned value immutably retains the checked object, image, caller range,
and each distinct callback's exact address and bytes.

## Supported boundary

The parser requires disjoint load pages even at 64 KiB, unique file-backed RX
function mappings agreeing with executable sections, and bounded header,
section and symbol tables. It refuses dynamic loading, residual relocation
sections (including RELR), unknown section kinds, ambiguous/weak/IFUNC/alternate-PCS
targets, writable code mappings, overlapping caller/callback extents, thunks,
and changed caller words or call
destinations. Its static ELF profile is deliberately narrower than all valid
Linux images. The Rust parser and correspondence check are not kernel proofs.

Callback bodies remain **unproved endpoints**. This check does not establish
their memory footprint, C ABI preservation, control behavior or return, a
loader theorem, entrypoint behavior, native execution, or instruction proof
admission. The private ABI gate's `[TCG-PROOF-465]` calling-frame refusal remains
open. Callback semantic authority and independent replay of the separate
conditional memory model are still required before production admission.

## Executed evidence

Qualification ran on Linux AArch64 using immutable Trust ae9c2c1d, explicitly
developmental `targo --unverified`, one build job, and a 16 GiB process-group
limit. GNU assembler 2.42 and LLD 22.1.6 produced real provider objects and
static images. Their executable hashes, versions and resolved paths are
retained. The providers are small assembly link fixtures (`str s0/d0,[x0]`
and `ret`), not proved C providers, and the images were not executed.

- All 24 original scalar-cell captures pass source/object/image binding at
  their recorded O0–O3 settings. Alternating link order checks twelve forward
  and twelve backward calls.
- Sixteen synthetic source extensions check two- and sixteen-call chains at
  O0/O3 for f32/f64, with repeated and distinct callbacks. All 144 mutations
  redirecting a call to another valid callback or a decoy are refused.
- Both O0 read callers refuse every replaced instruction word and changed
  branch opcode/displacement. All 66 named metadata, load, symbol, dynamic
  header and truncation controls are refused. Another 1,024 deterministic
  single-byte corruptions complete without panicking; irrelevant mutations
  may remain valid and are not counted as required refusals.
- The five new integration tests, all five existing scalar-cell object/byte
  integration tests, `trust-cg-verify --all-targets`, and the maintained root
  formatting gate pass. Listed and executed test names agree, with none
  ignored. These results do not claim the full workspace or system gate.
- The maintained Linux floor now requires this target with a minimum of five
  executed passes. Its exact target inventory passes; 57 Linux AArch64/x86-64
  runner and host-matrix tests pass. The existing non-Linux `/proc` refusal
  control is skipped on this Linux host (58 tests discovered). The complete
  168-family floor was not rerun for this diagnostic-only extension.

The first run passed four new integration tests plus the existing five and
all-targets. Final review added the chained-call cases; the second run repeated
the complete qualification with all five new tests. Review then found that
RELR sections were unhandled. The third run adds relocation-section controls
and fails with `accepted residual table section kind 19` (four tests pass,
one fails). The fourth run restricts the accepted section kinds and passes
all tests, including RELR and an unsupported packed-relocation extension.
All four source snapshots, actual command transcripts, guard outcomes, and
every generated caller object,
provider assembly/object and linked image are retained losslessly under
`records/` (each run's complete link inputs are a deterministic tar archive).
`manifest.json` and the maintained `inventory.json` bind raw and compressed
byte counts and SHA-256 digests. The final three changed Rust source hashes
are in the fourth run's `results.json`; its parent revision is
`0842f4fc0bfbcfbd4446c442d04b859b771bfd62`.

## Reproduction

On Linux AArch64 with genuine Trust, `as` and `ld.lld` on PATH:

```sh
targo --unverified test --locked -j 1 -p trust-cg-verify --test aarch64_scalar_cell_link -- --include-ignored --test-threads=1 --nocapture
targo --unverified test --locked -j 1 -p trust-cg-verify --test aarch64_scalar_cell_bytes -- --include-ignored --test-threads=1
targo --unverified check --locked -j 1 -p trust-cg-verify --all-targets
bash scripts/check_fmt.sh
```

The retained runners also pass `--offline`, bind the exact Trust executables
and cache, preserve temporary link inputs, and verify source hashes before
and after every command. Missing fixture tools fail rather than skip.
