# Thin reference arguments to C varargs on Linux AArch64 — 2026-09-29

Direct canonical-C variadic calls now admit thin Rust references when rustc's
actual call `FnAbi` classifies the argument as one direct eight-byte scalar.
The reference keeps its Rust type and its referent's real storage. The bridge
traces whole-reference copies and reborrows from anonymous arguments to local
referents, gives eligible aggregates their rustc-layout memory slots and scalar
leaves their existing cells, and refuses unresolved snapshot bindings. This
preserves pointer identity as well as writes through mutable and shared
interior-mutable references. The admission remains Linux AArch64 only.

Implementation commit: `186ab2ee3`, parent `958aff3da`. Main integration:
`36ff04a3b`, incorporating `85ae55bfc`, then `268cdbba2`, incorporating
`4726b6917`. Production code is in
[variadic.rs](../../../crates/rustc-codegen-trust-cg/src/variadic.rs) and the
memory/cell prepasses in [lib.rs](../../../crates/rustc-codegen-trust-cg/src/lib.rs).
The permanent cases live in
[residual_conversion.rs](../../../crates/rustc-codegen-trust-cg/tests/support/residual_conversion.rs)
and its `variadic_references`, `variadic_reference_unwind` and
`negative_variadic_wide_references` fixtures.

## Results

| Qualification | Result |
| --- | --- |
| Corrected backend, old + new LLVM/CG O0–O3, abort/unwind matrix | 80 native executions; 1,982,480 checks; 2,048 caught panics |
| Merged backend, same matrix | Same 80 executions and counts |
| Final x86-only integration, new reference matrix | 32 executions; 1,032,192 checks; 1,024 caught panics; same 8 wide-pointer refusals and 2 LLVM controls |
| New reference portion, corrected and first merged backend | 32 executions; 1,032,192 checks; 1,024 caught panics |
| Existing indirect/aggregate/i128 vararg negatives, each backend | 6 refusals and 6 successful LLVM controls |
| Wide reference/raw-pointer negatives, each backend | 8 failed roots in 2 refused compilations; 2 successful LLVM controls |
| Strict bridge, corrected and both merged builds O0/O2 | 16/12 functions; 13/8 refined; 5/5 memo hits; zero skips or unmodeled shapes |
| Machine proof, all three qualified backends O0/O2 | `TCG-PROOF-465` retained |
| Incoming main focused tests on this Linux host | 785 test executions passed (773 selected tests plus 12 subprocess executions) |

The new native cases cover shared/promoted scalar references, local and
forwarded mutable scalars and structs, shared `UnsafeCell` mutation, ten mutable
references overflowing argument registers, scalar/aggregate/projected-field
pointer identity, and branch-selected/reborrowed aliases. The C-unwind case
mutates a record before calling a panicking Rust callback; `Drop` must observe
the changed fields on both normal and cleanup paths. The independent `va_list`
consumer is compiled by GCC 13.3. LLVM builds the test drivers and runtime.

The first merge brought AY private-copy first-start accounting and x86 vector
comparison admission/selector tests, without changing bridge, AArch64 selector
or optimizer production code. The second adds opt-in x86 ALU copy propagation
and peephole-entry diagnostics; both switches default off. It changes bridge
option installation but no MIR lowering or AArch64 selector code. The final
build received the new reference native matrix, strict/machine checks, and
x86 copy-propagation/peephole tests. Linux qualification does not execute macOS's
first-start assessment path or native x86 instructions. Strict refinement
checks do not establish complete calling-convention, memory, or unwind proofs.

## Completed std census

Same frontend, recorded environment, working directory and LLVM dependencies;
commands differ only by backend and output directory. Both completed with exit
1 and no timeout. They are lowering-failure censuses, not successful std builds.

| Backend | Failed roots | Seconds (not a benchmark) |
| --- | ---: | ---: |
| Prior raw-pointer vararg backend | 200 | 719.101 |
| Corrected reference backend | 196 | 713.708 |

The four removed roots are `FileDesc::set_nonblocking`,
`Socket::set_nonblocking`, `PidFd::pid`, and `PidFd::exit_for_reaped_child`.
No roots were added; every remaining diagnostic string is unchanged. The final
main integration has a rebuilt native/strict qualification but no additional
full std census. O0 std was not rerun (last recorded census: 197 failed roots).

## Rejected prototype and open boundaries

The first type-gate-only prototype passed value and mutation checks but failed
pointer identity: `let r = &a; c_variadic(0, r, r)` allocated two argument
snapshots. LLVM passed; CG O0/O2 exited 8. Its 196-root std census is exploratory
and is not qualification evidence. The corrected backend promotes actual
referent storage and refuses any unresolved temporary-address binding.

A separate baseline reproducer also confirms an older miscompile in ordinary
fixed C and Rust calls: duplicate shared scalar references compare unequal
(128 of 128 inputs on both routes at O0/O2). This anonymous-vararg repair does
not fix that broader call-argument snapshot path. It is the next correctness
work item, recorded locally in `target/fixed-reference-identity-investigation`.
No general reference ABI correctness claim follows from this milestone.

Slice, `str`, trait-object references, raw fat pointers, aggregate values,
128-bit anonymous values, nonempty indirect variadic calls and variadic
function definitions remain outside this admitted surface. Full CG std,
self-hosting, complete machine proofs and performance superiority over
LLVM/Clang remain unfinished. These concurrent diagnostic builds are not
performance measurements.

## Reproduction and retained evidence

```sh
targo --unverified test --manifest-path crates/rustc-codegen-trust-cg/Cargo.toml --locked --test aarch64_c_fnabi_aggregate_linux --no-run --message-format=json
```

Freeze the emitted bridge dylib and test executable. Set
`TCG_TEST_BACKEND_PATH`, `TCG_TEST_BACKEND_SHA256`, and
`C_FNABI_LINUX_KEEP_ARTIFACTS=1`; run the executable with
`residual_conversion::no_proof_variadic --test-threads=1 --nocapture`.
The harness checks the backend digest throughout. Local scripts and exact
command receipts are in `target/variadic-reference-investigation`. Builds use
the pinned rustc-private sysroot/LLVM SDK, two jobs and incremental off; proof
runs use a private cache. Raw logs, sources, objects, ELF files and JSON
manifests remain under `target/`, as required by the development-record policy.
The initial syntax-invalid probe was rejected by both compilers and is not
counted; the corrected baseline and failed first prototype are retained.

Trust frontend: `ae9c2c1daa0fc80afbfd380e493f5581ac714acb`, 1.99.0-dev,
LLVM 22.1.2, native `aarch64-unknown-linux-gnu`. Both Cargo graphs resolve
TrustIR `8e81e98aa92d78934548ec435218ce530294f2c5`, Clean
`7330fa6cef4f16de5f449a4fce0404ab51269ffb`, AY
`f28345ff184e33551e9b9d9f509f831461dd8b24`. Packaged checker: AY 0.27.0,
build 10454, commit `657ce1821183b2076bb994167f830bde5d8e0509`; Clean 0.9.0.

## Artifact identities

| Artifact | SHA-256 |
| --- | --- |
| Baseline backend | `4ed1b9c565af06e3b6129506301d747fb5cebbd05c2eaa56d1c0407dd407905f` |
| first backend | `93aac2d6c1ad03867710d4008db2aa63654d9a34e456b062566f7eedee53c214` |
| second backend | `496bfad942f6e16433a956a1c7241be7143f3c8f017e371c2db859a59725f49f` |
| merged backend | `39834451f7dba4331fc0091489aaeb4ffc36ae7ceb9d17aa9e454498cc921347` |
| merged2 backend | `23065482ee898b3d78a8733e4660fd49cbbd930625d146c28fc5c7889f6a4081` |
| Native harness | `b56a47fbb5daab71657dc6fb57cfecec52f04e5f583c602bd87575ffc3bd3444` |
| trustc executable | `b2d4fa4bb1ce8106539d7c2967f1eb3f3f613293b8c905de586fbb4f5ffa4212` |
| targo executable | `4d877f14d86c786a1c077d5423f14304493d56ecf058447d6d8244cbb8a446ba` |
| ay executable | `81efc9f3bc4058062a64de75b4dd9827217a7b5f7b315f257b757bff818de0c5` |
| clean executable | `2d0c4b4be1513b5b59f0d4fd21c7f0e9a249693a7dd3d5fad14d702aa0e27f19` |
| cc executable | `a20520ee21543f243d40636a9181a142c45ecd989de31ab86b99a8ea5ada870d` |
| trust-cg-verify-lib.test | `8bf238bf963be225b5674ca8f7c43fa771d0cbc64b2ccec9dcded1bd85823dea` |
| trust-cg-lower-lib.test | `e16e86e87da9a488826b1a5b003a9231f03115c8e2f5897f2eec1dde2eb9490f` |
| trust-cg-lower-x86_vector_icmp_admission.test | `10c57c521be964fe0e867f9ffd6320e755248bbb8ac122f59786af200ffb07a8` |
| trust-cg-opt-lib-merged2.test | `815513acd4344be6dc8d0e6feaa9ed6c986b01f58dcaf51025b5d6b583e5edf4` |
| Local `native-final-artifacts-manifest.json` | `1231eb2f036b26341f7d68ac1126b8496ccb388baa0b0f4bbd77d5858320c2d5` |
| Local `strict-final-summary.json` | `4daabdea405cbec41bbc7d83672dc3df0d6a4fe4d89aef6ac371785a8847f302` |
| Local `qualification-source-manifest.json` | `efff47e6366cfcf0df52a94230df99c643d4e0661746b839f21d11574fcc57c0` |
| Local `merged-source-manifest.json` | `c7cfb3c1c971945f32806439b998f464e21a3aa4df9af879e929ec73d7b8966c` |
| Local `merged2-source-manifest.json` | `b2ddfe976276896e8bfd12d95606429a1ae7f27df660ffffe215f8156bfa44fd` |
| Local `std-O2-baseline-results.json` | `7b7bae29ede76980e544e1f6af437ac80078ebacab73c4a4cf1be07feeeaa2ee` |
| Local `std-O2-second-results.json` | `ceeadd99f7171ff4b91410dcf2cd6e0f4062c4a9d8e5afa0d5ec2a1a4ec2f93d` |
| Local `std-delta-second.json` | `09512d87ed4f53fbbc82553f64873ca0b384d5300044c2ec9534e2064de589b9` |
| Local `root-merged-results.json` | `a2047c446ff760dbc73decd8fbe423b23d41e5ae117b67521b9d9c4eee9b0f0b` |
| Local `root-merged2-results.json` | `b4df71ce29ced7526b42d4267e2f2689a4815a4de12c81fb608bb7946b411ac6` |

### Native executable identities

Paths are relative to each retained test directory.

| Matrix / case | ELF SHA-256 |
| --- | --- |
| second/scalar-abort/cg-O0/native.elf | `1d062d52f301104a266ee780f8a9c777a36f017110d1067044b47e7b7fa4457e` |
| second/scalar-abort/cg-O1/native.elf | `b5e88651b39b7f64d37277b2c68dbc3e5da8e7f017c110b07becfdb5873942c5` |
| second/scalar-abort/cg-O2/native.elf | `7b94e093884362e0a33ff45a660914528ce40926f313bcb9fbb7e16d33cbc46d` |
| second/scalar-abort/cg-O3/native.elf | `e97dbf8e0189a939664b4a338a14a10c97fb3657b35e83d8719f1936b14013ee` |
| second/scalar-abort/llvm-O0/native.elf | `42deed6f6f924cfe6c451b3d9cc530d4f03f89c2ed95832a9ea380f00ec6ee6d` |
| second/scalar-abort/llvm-O1/native.elf | `b8ff31e220fc386aeb391108ec3b2c3cef43a58c864591d0eab82a5019ab5fc4` |
| second/scalar-abort/llvm-O2/native.elf | `245834e60e98a66c3d9f7235915ad2d87a96a9045f8bee01be6691da12da6ab6` |
| second/scalar-abort/llvm-O3/native.elf | `4bbe5f9d0b63a5058b8d6e60aba7371176da77f08461a06d6662f40ea5915e24` |
| second/scalar-unwind/cg-O0/native.elf | `f3495faeae5dc8be060aec0eefa0fee36f79678c5b502806a60b7559cbb865c2` |
| second/scalar-unwind/cg-O1/native.elf | `5b06ecc9845b47310f56ce808cf117aba8ec76962e8bc8a526603782368861bf` |
| second/scalar-unwind/cg-O2/native.elf | `11a224a98b1306bf6e9c85049d3b75fdc33cadf4d180927dedc2f14e771f6f9f` |
| second/scalar-unwind/cg-O3/native.elf | `6d9bc7fbca4dbd7d69e075f1dd41ee11d6ab292a501d884002905d3bfcc5eb7c` |
| second/scalar-unwind/llvm-O0/native.elf | `4a4563780b8bc5de25a88d74e5b46e89bce658fc05d158a001ce74594385e0e8` |
| second/scalar-unwind/llvm-O1/native.elf | `1d053d55373f87fa2fd7fef95da392753768eef40fe738fb15dd1f5c1a502e5b` |
| second/scalar-unwind/llvm-O2/native.elf | `532191602d07e44f07c241123edc2ff0b652535a1ce517d5ef77129aaf8378a4` |
| second/scalar-unwind/llvm-O3/native.elf | `84af972eee223783fe1db046089457acbb99e3bd6ef6b2d7b6579dfa75843fe3` |
| second/unwind-abort/cg-O0/native.elf | `6afab84661c91fe2d147d12907539d2de97b24e33f7eeab745039af63c9302fe` |
| second/unwind-abort/cg-O1/native.elf | `0cac6a07dda5d849f3d471ef9c39de2410a3c92b8cbc2f1532747a68c08d66e6` |
| second/unwind-abort/cg-O2/native.elf | `87c6b4d046fa51e4a3e181671198e7cfe00aa396f17194c1b38e77a4d09e6432` |
| second/unwind-abort/cg-O3/native.elf | `63a061e9aacecc933b40de53866a475041df4c7032a232c4d46c86071b630745` |
| second/unwind-abort/llvm-O0/native.elf | `fb6a554797234aa37fc78bec2f880a39e6824ee87d12c34c5ac408d5465cc6cd` |
| second/unwind-abort/llvm-O1/native.elf | `3ae3941da4c0085a2a67f0cf36e9112904078d83de0f4ef24a5fccb22d44df5b` |
| second/unwind-abort/llvm-O2/native.elf | `3ae3941da4c0085a2a67f0cf36e9112904078d83de0f4ef24a5fccb22d44df5b` |
| second/unwind-abort/llvm-O3/native.elf | `3ae3941da4c0085a2a67f0cf36e9112904078d83de0f4ef24a5fccb22d44df5b` |
| second/unwind-unwind/cg-O0/native.elf | `1aa817253b28d74537db419fc67a0d0d98e9e115db27d9d4f320b57d0632c283` |
| second/unwind-unwind/cg-O1/native.elf | `7ca962dc01f55089268038aedba783911796409eceff5548281173231bd7e693` |
| second/unwind-unwind/cg-O2/native.elf | `a2c84d3eb3efacba2d0a6acc112eba0d539a7f05a93807a627b374f52609f373` |
| second/unwind-unwind/cg-O3/native.elf | `d0978ab927899c8e9dd6bec106acd00baf9649187d9182dd6ebcb7bc717a8d73` |
| second/unwind-unwind/llvm-O0/native.elf | `4eae9266c419bdca6df6ea1669e14d21d0d02760ba602f741097eec23c37b592` |
| second/unwind-unwind/llvm-O1/native.elf | `879ca5d3a49515d1d793eab901a0d76e03c06b39c413e77c6a56622ef04efb90` |
| second/unwind-unwind/llvm-O2/native.elf | `879ca5d3a49515d1d793eab901a0d76e03c06b39c413e77c6a56622ef04efb90` |
| second/unwind-unwind/llvm-O3/native.elf | `879ca5d3a49515d1d793eab901a0d76e03c06b39c413e77c6a56622ef04efb90` |
| second/abort/cg-O0/native.elf | `e4b672f178c3b31431666b91f7fc4515ddedd33d3d1ecb7e273a2fc05863f8b0` |
| second/abort/cg-O1/native.elf | `ed62e2ade3c2de0927febff8020e8afd27e8944cf99c6aee6fe4a2c640061f22` |
| second/abort/cg-O2/native.elf | `6a22de884851be8bf67fb8c4c99781170e4083e6b86d3a5fbb3346262492092b` |
| second/abort/cg-O3/native.elf | `7a982f2250f3177376af1c25358fb833cbeb256e0ad3da68f2f56b7585e5c204` |
| second/abort/llvm-O0/native.elf | `eab3c509a1068e5cc61379485d4c86f0819377fbe39e263c1ea60bddf56847e2` |
| second/abort/llvm-O1/native.elf | `9dfc37b1ef42698a4537d72978321cadc68b742ee9d26406cac729996903f804` |
| second/abort/llvm-O2/native.elf | `9dfc37b1ef42698a4537d72978321cadc68b742ee9d26406cac729996903f804` |
| second/abort/llvm-O3/native.elf | `9dfc37b1ef42698a4537d72978321cadc68b742ee9d26406cac729996903f804` |
| second/unwind/cg-O0/native.elf | `ee7d78e1a36853770a5231a0bf5867a1811c170240eb6aa57399c3419270574d` |
| second/unwind/cg-O1/native.elf | `49221a9b7cde1130d021c3d96e95a1d8adda6a3d06a479e80d71e4f715ea4ae5` |
| second/unwind/cg-O2/native.elf | `b734fbc04407f35a695c668171fe7c30442dee5afc6fee112746c9a5e924ae62` |
| second/unwind/cg-O3/native.elf | `f162e099152e1b405c7609df3e9cbfe530e84580cb385dd74d0e1656678bd418` |
| second/unwind/llvm-O0/native.elf | `a992e26273138f9b6cadc4cfce770b11a4682d1312aa858df39acc8022873202` |
| second/unwind/llvm-O1/native.elf | `746cea4ec20300246506820df028c2c4c9299d3a3d8855dd02f09c5511630bd8` |
| second/unwind/llvm-O2/native.elf | `746cea4ec20300246506820df028c2c4c9299d3a3d8855dd02f09c5511630bd8` |
| second/unwind/llvm-O3/native.elf | `746cea4ec20300246506820df028c2c4c9299d3a3d8855dd02f09c5511630bd8` |
| second/scalar-abort/cg-O0/native.elf | `a22131776d8474e4f5bb8628f2f9ba7ba76371e22c53364c7b42c1d2a0573569` |
| second/scalar-abort/cg-O1/native.elf | `4974f56f1d42a1c1aa39443ca65b36f2edcb38a42b7f725fbb56b82b850e996a` |
| second/scalar-abort/cg-O2/native.elf | `5af391bd05b5756ff8762691819dcd4267754d114fd3195402f1e2de9ecb2fc1` |
| second/scalar-abort/cg-O3/native.elf | `4f912232d65d5c5b3bd0e848df5b654003e5f84c3fa3e30ae08d87fc45e68c1c` |
| second/scalar-abort/llvm-O0/native.elf | `8b7eaa46e23e2dad75a09047f54b8c38d43ee451e9bb76f10e8ce310cb0d4975` |
| second/scalar-abort/llvm-O1/native.elf | `95c0079859d2eb2b9d383f1be4a12d40808fdea40d17f03c3ceec02aa79f9114` |
| second/scalar-abort/llvm-O2/native.elf | `95c0079859d2eb2b9d383f1be4a12d40808fdea40d17f03c3ceec02aa79f9114` |
| second/scalar-abort/llvm-O3/native.elf | `95c0079859d2eb2b9d383f1be4a12d40808fdea40d17f03c3ceec02aa79f9114` |
| second/scalar-unwind/cg-O0/native.elf | `c8cb74500de271b7bbb257e54b616bef6383f825316974f0179e4dc16ac8a463` |
| second/scalar-unwind/cg-O1/native.elf | `2708db1a465f00b8ded8ec77f95513d0fec893330be688b6a8ac13299297fbff` |
| second/scalar-unwind/cg-O2/native.elf | `aad845f21492435b2c8a6d71882b240fab90b48822adf212e9a8556bb7174133` |
| second/scalar-unwind/cg-O3/native.elf | `8f0950d57784176ef3932541157e9a2e1dff876a5ebc22bcc562c801f0d29dd0` |
| second/scalar-unwind/llvm-O0/native.elf | `6c433276b8b570a70b75c1e3a774afd41f4be435b4079ff9a8ae59ffeeeab3c5` |
| second/scalar-unwind/llvm-O1/native.elf | `75fd84b2864508f20a63f54e39cba8ef038ea7d8f90162d18baaed78ca18655b` |
| second/scalar-unwind/llvm-O2/native.elf | `75fd84b2864508f20a63f54e39cba8ef038ea7d8f90162d18baaed78ca18655b` |
| second/scalar-unwind/llvm-O3/native.elf | `75fd84b2864508f20a63f54e39cba8ef038ea7d8f90162d18baaed78ca18655b` |
| second/unwind-abort/cg-O0/native.elf | `75e178b7c74540c439e7af986fa951e13f8546ee7cdcfd576a023cb54e51e3bb` |
| second/unwind-abort/cg-O1/native.elf | `d9f404ec8d070d63aec41bd87c7345c3891a59d5b73d81974d7c6e8ee29f3f06` |
| second/unwind-abort/cg-O2/native.elf | `1bc814d5f266ae32a0cd9e522661fb4be2e98efcf168fe1ccb284d2e776e2378` |
| second/unwind-abort/cg-O3/native.elf | `c81bc92ded06cd22a22cc532c0e77006d8796273fab82f3347073e372aee8a9b` |
| second/unwind-abort/llvm-O0/native.elf | `9769c3f3deb9d4c934b5ed54559cbf63bd9ecfc5b5f15bd1ac13067a044834bb` |
| second/unwind-abort/llvm-O1/native.elf | `e53c9dbd921dedc1d0a14efdbbc77dacd78a6a5439a913c3cfddbec8eb8c2064` |
| second/unwind-abort/llvm-O2/native.elf | `91d85b775d37c08344db0149a7bebfce3fc493bc44b346a419d771ce23436a05` |
| second/unwind-abort/llvm-O3/native.elf | `91d85b775d37c08344db0149a7bebfce3fc493bc44b346a419d771ce23436a05` |
| second/unwind-unwind/cg-O0/native.elf | `0caef0820255cfe6ec171be3304aae6a84d11a6966c9028b66afcd0a4876f8dd` |
| second/unwind-unwind/cg-O1/native.elf | `761ca557a025e65c898f032222224cca193899f84a0c0c3f982bdce14a724aa9` |
| second/unwind-unwind/cg-O2/native.elf | `ac93f0d26c0c0b7652f909f4d6f98fde266cd0779bad4ed0b76cc6736c7627e5` |
| second/unwind-unwind/cg-O3/native.elf | `39da7d4d188d51f6154b84f6258171b6121e8ace8c1c97f96cce39094268dd78` |
| second/unwind-unwind/llvm-O0/native.elf | `a7818d020ecc68fad25a6e768a2ef0acc89da33cb7e8cd1b6c47ab4313df5ed4` |
| second/unwind-unwind/llvm-O1/native.elf | `663fc46295278dcd842e583ec0fea491c966de38932046e73f375ba01afd8753` |
| second/unwind-unwind/llvm-O2/native.elf | `5c06d0657bd5f33550e5b0d021dcd688a321a6430ee5297cf69b3bb2c8322305` |
| second/unwind-unwind/llvm-O3/native.elf | `5c06d0657bd5f33550e5b0d021dcd688a321a6430ee5297cf69b3bb2c8322305` |
| merged/scalar-abort/cg-O0/native.elf | `089b9f5528ce976adc090184aa907b105d5c631cff9b3e5f838530433f069d06` |
| merged/scalar-abort/cg-O1/native.elf | `e2948f9cb0a8bf0465462f9ab25a6cd8c8ebbeb6054d783378f56add44b26223` |
| merged/scalar-abort/cg-O2/native.elf | `9f326ec7a72411b82bf7b21efa8835f258c76cad5f7ebd0963186730f29c7af6` |
| merged/scalar-abort/cg-O3/native.elf | `900a934319f31b697ac21cb9eb62a7709f38a3a9f0cab792198ada1c222dfc6a` |
| merged/scalar-abort/llvm-O0/native.elf | `23f998de1d9a1461c86cb4a30213c0d971fb1acca2cecc1d1732b520982b3b0a` |
| merged/scalar-abort/llvm-O1/native.elf | `004ac955237ca6ef9c88cb2c6ae5a7a323894697edbc02acec43540e46308221` |
| merged/scalar-abort/llvm-O2/native.elf | `d279411fb59bd4f81d1ac7d73b14233de3ec3414444116f61750615ca74d0573` |
| merged/scalar-abort/llvm-O3/native.elf | `23bd81cf6f4205764c3e79c1c2b10cb2249a94066a3a5ae718dc7e42bfd448b6` |
| merged/scalar-unwind/cg-O0/native.elf | `54e5d9804a712ecd6f9fa406326c4a12ed645f258b5af72b852a44ca46ace7ac` |
| merged/scalar-unwind/cg-O1/native.elf | `9dc066fd2349f13a9d8e8762c6e19b8befb291fed4765fdf5322cb8af22d1545` |
| merged/scalar-unwind/cg-O2/native.elf | `fb4974e179649713cbf75f7f9cb4da0c606f21d936028ff73faf5ebe828a61f8` |
| merged/scalar-unwind/cg-O3/native.elf | `b07b74b8a7d7f4c7848ef65f540df08c580f5f9271bc2511d30c1d916f017e97` |
| merged/scalar-unwind/llvm-O0/native.elf | `7fe95e33821ee92c0eca30801ce77cbd86ac598e60e45f373aa44d9345f5eda0` |
| merged/scalar-unwind/llvm-O1/native.elf | `1506689aeb6b4f1d2644407c597a5637ef2f222f502bc384ff68f0e3d826bcec` |
| merged/scalar-unwind/llvm-O2/native.elf | `7ec6276878ed86424f14814f1acbe941c52d478e8700857fd64e3d8d60b8c24c` |
| merged/scalar-unwind/llvm-O3/native.elf | `5c083e3a61c5424e592721856a3e12de53f80b8beddf35edcc89561474a9c56e` |
| merged/unwind-abort/cg-O0/native.elf | `70bbf5f275265a4b4512b4697f1e1e87f6ad5ee16e06d899810d9dafbf242250` |
| merged/unwind-abort/cg-O1/native.elf | `c7a327bcd8294fc55df94d1546a3bd22097f2210dc3e04f43f2380a209dd8a4f` |
| merged/unwind-abort/cg-O2/native.elf | `d38d26eeda927d3d9aec20e412615e09238d2f010b96ab15569a2d4a9192f133` |
| merged/unwind-abort/cg-O3/native.elf | `98e7b0e5d76a84efb53125541a13ed541d343884aa3fc44a077e6553c60a2b9a` |
| merged/unwind-abort/llvm-O0/native.elf | `f5585d935239e26c6017e0053029d2b15abdb79f91b7f8504508c523753526c4` |
| merged/unwind-abort/llvm-O1/native.elf | `0308991ec79ae58107cb435dc51e3ad34494365da186d2142e9f58e8376bd114` |
| merged/unwind-abort/llvm-O2/native.elf | `0308991ec79ae58107cb435dc51e3ad34494365da186d2142e9f58e8376bd114` |
| merged/unwind-abort/llvm-O3/native.elf | `0308991ec79ae58107cb435dc51e3ad34494365da186d2142e9f58e8376bd114` |
| merged/unwind-unwind/cg-O0/native.elf | `fea4c75ddb4b88df3230eae01353618b3d37cd0e29aadc77739566f8cd9392ee` |
| merged/unwind-unwind/cg-O1/native.elf | `8eac0719b206dde7e81e1bc0d44beb96c73aa13847c1dcaf88cb08c18f432b78` |
| merged/unwind-unwind/cg-O2/native.elf | `c267e25f5d1a24abdbc0c85e13d22427fbb7ff68ffc405a88002de9047a8b9c8` |
| merged/unwind-unwind/cg-O3/native.elf | `29d1d422715307628a9a0e82a0efa61bcfbb5766905788f23507707a417fc1c1` |
| merged/unwind-unwind/llvm-O0/native.elf | `2fbeeeb3017a79d21e96c26320bc8f781e361d65599d8cbcbc1d0699a6b83647` |
| merged/unwind-unwind/llvm-O1/native.elf | `d44b22e045b14d08cb996199997b3e4683564f67e26ba1e8af55b3735edaf559` |
| merged/unwind-unwind/llvm-O2/native.elf | `d44b22e045b14d08cb996199997b3e4683564f67e26ba1e8af55b3735edaf559` |
| merged/unwind-unwind/llvm-O3/native.elf | `d44b22e045b14d08cb996199997b3e4683564f67e26ba1e8af55b3735edaf559` |
| merged/abort/cg-O0/native.elf | `de46634936d8886228736d33e9b014dbb47f6a285ba158e39f7282de8602328c` |
| merged/abort/cg-O1/native.elf | `5a162a92aa29ad98f940f163e08ab560df57024ba813cdba5ae09868d8b3670c` |
| merged/abort/cg-O2/native.elf | `69ec517a2ce8125ef0f22df4a43bee8877b1f43e0a3796b42ae719048ecc1e0c` |
| merged/abort/cg-O3/native.elf | `390340b372408f14211e377f048e7f2cdf64ae664881cd6cc1597071991e599a` |
| merged/abort/llvm-O0/native.elf | `87a5a11ba5c330997d829bde76771329d6aee5a0464cba8322c83610b04ca130` |
| merged/abort/llvm-O1/native.elf | `aeb4244cfed2cc437b12ece747b9dd1da79f1d74ec86d540d8c9ec6ff4253d1f` |
| merged/abort/llvm-O2/native.elf | `aeb4244cfed2cc437b12ece747b9dd1da79f1d74ec86d540d8c9ec6ff4253d1f` |
| merged/abort/llvm-O3/native.elf | `aeb4244cfed2cc437b12ece747b9dd1da79f1d74ec86d540d8c9ec6ff4253d1f` |
| merged/unwind/cg-O0/native.elf | `c0d8d8522781df11c314b7e0969877d64a57253966c68e0ad441ab9f6098f973` |
| merged/unwind/cg-O1/native.elf | `bd7de5a4b974778456973a9cb361dde6490ff754d32606c9255bc722e4a36388` |
| merged/unwind/cg-O2/native.elf | `12d080a2c3de092e0c17ec20f3aa7deff6574d19ce6a51f04b1cf427903655fb` |
| merged/unwind/cg-O3/native.elf | `93348adccab29280c523158bd581d6f1de7948d11a3d908b28e6f840dbc2bef5` |
| merged/unwind/llvm-O0/native.elf | `34eca7a155201e307e85cd15f6033888a31f517d58ee617eabb5359085a18e18` |
| merged/unwind/llvm-O1/native.elf | `d90f50289b55274af60508b04f1a697da8c64be1e90a06af07ab783544c9bb8f` |
| merged/unwind/llvm-O2/native.elf | `d90f50289b55274af60508b04f1a697da8c64be1e90a06af07ab783544c9bb8f` |
| merged/unwind/llvm-O3/native.elf | `d90f50289b55274af60508b04f1a697da8c64be1e90a06af07ab783544c9bb8f` |
| merged/scalar-abort/cg-O0/native.elf | `6ebcc37c05a570094ea909e173ad71597be709a9448ffb4418d083373782256b` |
| merged/scalar-abort/cg-O1/native.elf | `f5c5134f0ec674c6029a4cedb4a6b21e17400a5bc9abc9e09ceb4b6d4936b93f` |
| merged/scalar-abort/cg-O2/native.elf | `3b3f455fd7e798b4423aa73769511c37b0bc5385c43b85093359614ddb82e735` |
| merged/scalar-abort/cg-O3/native.elf | `7c7894ad6f09976a6fdffd4b1690dc3ed9b42b81a50cb7e618fef65ee53728da` |
| merged/scalar-abort/llvm-O0/native.elf | `4fd10af7f6e582a45171b9e82a7e932631043e64ba608fef07868099d8c6d79a` |
| merged/scalar-abort/llvm-O1/native.elf | `9984deb470ad2890f7d4930e69edd7436349f4a1743c8ad32a3a537985d814a7` |
| merged/scalar-abort/llvm-O2/native.elf | `9984deb470ad2890f7d4930e69edd7436349f4a1743c8ad32a3a537985d814a7` |
| merged/scalar-abort/llvm-O3/native.elf | `9984deb470ad2890f7d4930e69edd7436349f4a1743c8ad32a3a537985d814a7` |
| merged/scalar-unwind/cg-O0/native.elf | `1ef89360bb9c16a82ab24c454d326ae5daedf38ea84a97bb735b80f9d58040ef` |
| merged/scalar-unwind/cg-O1/native.elf | `046a14d5a306ac6c27d15fcc245762c1784ae6effb15d5a7a238528c08487ec0` |
| merged/scalar-unwind/cg-O2/native.elf | `98a3830219a16348c83aabfecbb4ede1bd0f3a3be91f4e611bff72626054927b` |
| merged/scalar-unwind/cg-O3/native.elf | `e27d9d51ea0d2fc2a2e96cb85cb83d39f36d794b4344d35692e593a342f1fb9f` |
| merged/scalar-unwind/llvm-O0/native.elf | `bac924f92e62832c90fe0a3b15b901a9abd7ead19c12d642e0657aad94906286` |
| merged/scalar-unwind/llvm-O1/native.elf | `9250a6f3103e7b32e5a10ce6bfdb2d605d55f033913574ec65580bc195874404` |
| merged/scalar-unwind/llvm-O2/native.elf | `9250a6f3103e7b32e5a10ce6bfdb2d605d55f033913574ec65580bc195874404` |
| merged/scalar-unwind/llvm-O3/native.elf | `9250a6f3103e7b32e5a10ce6bfdb2d605d55f033913574ec65580bc195874404` |
| merged/unwind-abort/cg-O0/native.elf | `9db07edcd04880a4f71a285266856abfeb4f4baa7b6fde050570015eba86874e` |
| merged/unwind-abort/cg-O1/native.elf | `b996360ae00d5c0ff8e782ca6f326f325c4524f12a189f8fe4826a529dc18ee4` |
| merged/unwind-abort/cg-O2/native.elf | `4f13664df0d61626f55564e7bbbcfc3439242921eeaa87a227c33805ea249846` |
| merged/unwind-abort/cg-O3/native.elf | `9cb4ba50b739adeea7d79b8995a53a91f93819e46128f774fd9df1ee3cbd17fc` |
| merged/unwind-abort/llvm-O0/native.elf | `81e3400b32f35d2479eeadecba7a6081b75d0ac77ccd0e5bc8b74028f68f28d4` |
| merged/unwind-abort/llvm-O1/native.elf | `eb5178ed69021ac7ed69c09d534ac1a92af22b8159e99dfc53b026b0e76abba2` |
| merged/unwind-abort/llvm-O2/native.elf | `5b8df0b694ecf48817c039f41c8ab8a8af6d6625df4836d8050d7f8926f1b6eb` |
| merged/unwind-abort/llvm-O3/native.elf | `5b8df0b694ecf48817c039f41c8ab8a8af6d6625df4836d8050d7f8926f1b6eb` |
| merged/unwind-unwind/cg-O0/native.elf | `53aaba9ad4bafb2145cd927734bce6f61930ea3b3134dc9ce68f2b53c2f6b286` |
| merged/unwind-unwind/cg-O1/native.elf | `1a09287344e6593c69792667436be4e02bd6520be1ff1054e33d495a5961e456` |
| merged/unwind-unwind/cg-O2/native.elf | `e29e123f23ef9f95f2fbf7a9fc69dcbf69a9d4e4b2676dab65b646595418e196` |
| merged/unwind-unwind/cg-O3/native.elf | `8ea16a5c9e89b087f926c64d911d7d63e45587f3cf612a1c76cd8f8bc8767df0` |
| merged/unwind-unwind/llvm-O0/native.elf | `99984ec6c4bd6aeb74944a0fbb8e692772120679195d90d3b2453920f20b77bc` |
| merged/unwind-unwind/llvm-O1/native.elf | `2eae23932790aa14a064a39b9191841a47758cfe189ebba1cfd42ebf4a5286f2` |
| merged/unwind-unwind/llvm-O2/native.elf | `cc1e3d6e7db690a78cd690f8c31e7801f665f5f3f48e7a0d5697468b49ccd83c` |
| merged/unwind-unwind/llvm-O3/native.elf | `cc1e3d6e7db690a78cd690f8c31e7801f665f5f3f48e7a0d5697468b49ccd83c` |
| merged2/scalar-abort/cg-O0/native.elf | `949397ee70f27bb1a7ff592a2455d3189ee760074cfb144c153f549f7d237b3f` |
| merged2/scalar-abort/cg-O1/native.elf | `ffcc4bfc3bb15bc22b89be71c2a4c0aa66a33683194e80e447dc29b289b0d02c` |
| merged2/scalar-abort/cg-O2/native.elf | `341f4966f591cfed53b6ae5b3edf3851c0cae045f6f2355c485caff1ad14107b` |
| merged2/scalar-abort/cg-O3/native.elf | `afb60bbfcdbbb8cd89848db39c55372cc617c94d827e9e6b5479a9e3b9b512a0` |
| merged2/scalar-abort/llvm-O0/native.elf | `35078b9d89b8ca57c3872e5f4daaa3d00fb3997c907e51fd07ba8a039bf8abee` |
| merged2/scalar-abort/llvm-O1/native.elf | `a4858a406a8f4cff2e1b4467112591c172a91c4ff935dfa8c7cc3802c91d481a` |
| merged2/scalar-abort/llvm-O2/native.elf | `a4858a406a8f4cff2e1b4467112591c172a91c4ff935dfa8c7cc3802c91d481a` |
| merged2/scalar-abort/llvm-O3/native.elf | `a4858a406a8f4cff2e1b4467112591c172a91c4ff935dfa8c7cc3802c91d481a` |
| merged2/scalar-unwind/cg-O0/native.elf | `c2f6e49942b8d8bcc5d216af52382ee066e0d793396e319bb6aa36dfb28238fe` |
| merged2/scalar-unwind/cg-O1/native.elf | `edc98ec6bb3cad85bc42a895e280fc87668756d22d1d29936bc9b433f45f2794` |
| merged2/scalar-unwind/cg-O2/native.elf | `69612ef25bc2cb83b18f737aaaabca8e37282be50f2bc843b594edc5640778aa` |
| merged2/scalar-unwind/cg-O3/native.elf | `2cf158f00d087904a1af4339c8cc678449361966aaf8b95c2034ec469e4d4ef1` |
| merged2/scalar-unwind/llvm-O0/native.elf | `309c6f2652a7e9484a08cf1c2c8f314c92da1141e582fdbc33c1eee6d5c4290b` |
| merged2/scalar-unwind/llvm-O1/native.elf | `7342980aba682922737860ebca2ccc97070189f8de5fb2e8328f4ed08ca82fae` |
| merged2/scalar-unwind/llvm-O2/native.elf | `7342980aba682922737860ebca2ccc97070189f8de5fb2e8328f4ed08ca82fae` |
| merged2/scalar-unwind/llvm-O3/native.elf | `7342980aba682922737860ebca2ccc97070189f8de5fb2e8328f4ed08ca82fae` |
| merged2/unwind-abort/cg-O0/native.elf | `e087dc27d9fe251b6829c3adc108b4e195222933b3c09567cc4259fa27fd5518` |
| merged2/unwind-abort/cg-O1/native.elf | `c72c64acb79072977f9a2a2d9f1f7b7ca6a9af4f93587298187045e13798a3c7` |
| merged2/unwind-abort/cg-O2/native.elf | `2f6b56ed7560bf9eba758262a39fe7d933ace26bb409149cd00663f926216c88` |
| merged2/unwind-abort/cg-O3/native.elf | `9c8bb80472f1aa366fee98569398bd78cb49dc729f27dc79966675f8c933913a` |
| merged2/unwind-abort/llvm-O0/native.elf | `c797c6a5735b365a5432bece85646f9c79e594ccc01aa97c7457ce87352e52cd` |
| merged2/unwind-abort/llvm-O1/native.elf | `e109e4e240bdc95f25a2ed3366318d51933f632b41281aed28e63f2163ab77d1` |
| merged2/unwind-abort/llvm-O2/native.elf | `209b8d10e53b921ffc35ebbef8c00e63c35434aa913c6ba95140a1e40e140295` |
| merged2/unwind-abort/llvm-O3/native.elf | `209b8d10e53b921ffc35ebbef8c00e63c35434aa913c6ba95140a1e40e140295` |
| merged2/unwind-unwind/cg-O0/native.elf | `8d14c67edbc5b5e0a21357844515416d8c456af46602c33c469f6247f97cf4f9` |
| merged2/unwind-unwind/cg-O1/native.elf | `c179621c80ba53ef613e83203b3e4641642b25be566227efdeb90dbbcf9827a5` |
| merged2/unwind-unwind/cg-O2/native.elf | `e3682865b066444d09cdab4920f06f93c5e840dbb5928b839249eaaac34490bc` |
| merged2/unwind-unwind/cg-O3/native.elf | `dcf64684528de3191f51726807779d6ddad75ace1943c3a20f988e02d40e2999` |
| merged2/unwind-unwind/llvm-O0/native.elf | `27ce1bf8c757d7528db4e361f4f08d815e7db6b70f25da4ce03a94fbf8709411` |
| merged2/unwind-unwind/llvm-O1/native.elf | `84338e57085264dee04630b2b56cf6f7b92cda73cf6a05f1a01b0c3b919aa485` |
| merged2/unwind-unwind/llvm-O2/native.elf | `889a346ca85c07d536f7c2a87f2834748a661058245ecc7bef393a2689015f13` |
| merged2/unwind-unwind/llvm-O3/native.elf | `889a346ca85c07d536f7c2a87f2834748a661058245ecc7bef393a2689015f13` |

### Exact baseline census command

The corrected invocation changes only backend and output directory.

```sh
/home/ayates/trust-cg-soundness-20260914/trust-authored-qualified-20260924/trust-ae9c2c1d/bin/trustc --crate-name std --edition=2024 std/src/lib.rs --error-format=json --json=diagnostic-rendered-ansi,artifacts,future-incompat --crate-type dylib --crate-type rlib --emit=dep-info,link -C embed-bitcode=no -C codegen-units=1 --warn=unexpected_cfgs --check-cfg 'cfg(feature, values(any()))' --check-cfg 'cfg(target_has_reliable_f16)' --check-cfg 'cfg(target_has_reliable_f16_math)' --check-cfg 'cfg(target_has_reliable_f128)' --check-cfg 'cfg(target_has_reliable_f128_math)' --cfg 'feature="addr2line"' --cfg 'feature="backtrace"' --cfg 'feature="miniz_oxide"' --cfg 'feature="object"' --cfg 'feature="panic-unwind"' --check-cfg 'cfg(docsrs,test)' --check-cfg 'cfg(feature, values("addr2line", "backtrace", "backtrace-trace-only", "compiler-builtins-c", "compiler-builtins-mem", "debug_refcell", "llvm-libunwind", "llvm_enzyme", "miniz_oxide", "object", "optimize_for_size", "panic-unwind", "system-llvm-libunwind", "windows_raw_dylib"))' -C metadata=2151fd1de3847f13 --out-dir $HOME/trust-cg/target/variadic-reference-investigation/std-O2-baseline --target aarch64-unknown-linux-gnu -C strip=debuginfo -L dependency=$HOME/trust-cg/target/std-build-investigation/llvm-resolve/target/aarch64-unknown-linux-gnu/debug/deps -L dependency=$HOME/trust-cg/target/std-build-investigation/llvm-resolve/target/debug/deps --extern priv:addr2line=$HOME/trust-cg/target/std-build-investigation/llvm-resolve/target/aarch64-unknown-linux-gnu/debug/deps/libaddr2line-12c7738545273db2.rlib --extern alloc=$HOME/trust-cg/target/std-build-investigation/llvm-resolve/target/aarch64-unknown-linux-gnu/debug/deps/liballoc-74b6f64c7e901880.rlib --extern priv:cfg_if=$HOME/trust-cg/target/std-build-investigation/llvm-resolve/target/aarch64-unknown-linux-gnu/debug/deps/libcfg_if-5b0a02a5eaac4739.rlib --extern core=$HOME/trust-cg/target/std-build-investigation/llvm-resolve/target/aarch64-unknown-linux-gnu/debug/deps/libcore-eaac2a498319830d.rlib --extern priv:hashbrown=$HOME/trust-cg/target/std-build-investigation/llvm-resolve/target/aarch64-unknown-linux-gnu/debug/deps/libhashbrown-ebb0e293be97ce62.rlib --extern libc=$HOME/trust-cg/target/std-build-investigation/llvm-resolve/target/aarch64-unknown-linux-gnu/debug/deps/liblibc-1db47c455d786c7a.rlib --extern priv:miniz_oxide=$HOME/trust-cg/target/std-build-investigation/llvm-resolve/target/aarch64-unknown-linux-gnu/debug/deps/libminiz_oxide-7392aa5c5bcbb032.rlib --extern priv:object=$HOME/trust-cg/target/std-build-investigation/llvm-resolve/target/aarch64-unknown-linux-gnu/debug/deps/libobject-a6517f9eb710ccae.rlib --extern priv:panic_abort=$HOME/trust-cg/target/std-build-investigation/llvm-resolve/target/aarch64-unknown-linux-gnu/debug/deps/libpanic_abort-79c82d310bffce8a.rlib --extern priv:panic_unwind=$HOME/trust-cg/target/std-build-investigation/llvm-resolve/target/aarch64-unknown-linux-gnu/debug/deps/libpanic_unwind-780ac334bb08e854.rlib --extern priv:rustc_demangle=$HOME/trust-cg/target/std-build-investigation/llvm-resolve/target/aarch64-unknown-linux-gnu/debug/deps/librustc_demangle-d615677db4ffd5d8.rlib --extern std_detect=$HOME/trust-cg/target/std-build-investigation/llvm-resolve/target/aarch64-unknown-linux-gnu/debug/deps/libstd_detect-b1e1c14d8899ece2.rlib --extern priv:unwind=$HOME/trust-cg/target/std-build-investigation/llvm-resolve/target/aarch64-unknown-linux-gnu/debug/deps/libunwind-a3d565b6442598f4.rlib -Z unstable-options -Ztrust-verify=off -Zforce-unstable-if-unmarked -Ccodegen-units=1 --verbose --cfg backtrace_in_libstd --check-cfg 'cfg(netbsd10)' --check-cfg 'cfg(no_global_oom_handling)' --check-cfg 'cfg(restricted_std)' --check-cfg 'cfg(backtrace_in_libstd)' --check-cfg 'cfg(vxworks_lt_25_09)' -Copt-level=2 -Zcodegen-backend=$HOME/trust-cg/target/variadic-call-investigation/merged2-backend.so '-Ztrust-ir-cg-args=diag-json no-proof-certs time-codegen=20 time-lower'
```

### Incoming main test commands

```sh
$HOME/trust-cg/target/variadic-reference-investigation/trust-cg-verify-lib.test ay_identity::tests --test-threads=1 --nocapture
$HOME/trust-cg/target/variadic-reference-investigation/trust-cg-verify-lib.test ay_bridge::subprocess_tests --test-threads=1 --nocapture
$HOME/trust-cg/target/variadic-reference-investigation/trust-cg-lower-lib.test x86_vector_icmp_gate_tests --test-threads=1 --nocapture
$HOME/trust-cg/target/variadic-reference-investigation/trust-cg-lower-lib.test x86_64_isel::tests:: --test-threads=1 --nocapture
$HOME/trust-cg/target/variadic-reference-investigation/trust-cg-lower-x86_vector_icmp_admission.test '' --test-threads=1 --nocapture
$HOME/trust-cg/target/variadic-reference-investigation/trust-cg-opt-lib-merged2.test x86_copy_prop::tests --test-threads=1 --nocapture
$HOME/trust-cg/target/variadic-reference-investigation/trust-cg-opt-lib-merged2.test x86_peephole::tests --test-threads=1 --nocapture
```
