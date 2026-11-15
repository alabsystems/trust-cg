# Stable thin-reference call arguments on Linux AArch64 — 2026-09-29

The bridge now gives eligible referents of thin reference call arguments their
actual local storage. Previously a shared scalar argument was copied into a
fresh temporary for each argument: `let r = &a; same_address(r, r)` returned
false through both fixed C and Rust calls. The baseline fails every tested input
at O0/O2; LLVM returns true. Whole-reference copies, reborrows, branch-selected
aliases, projected fields, indirect calls and raw addresses returned across calls
need the same storage, regardless of whether the callee returns a reference.

Implementation: `1db859a208f07e25e23ae08d242707676b064ae9`, based on synced `b69df860f`. The shared prepass is
[call_references.rs](../../../crates/rustc-codegen-trust-cg/src/call_references.rs).
It extends the prior anonymous-vararg analysis to all thin-reference call
arguments on Linux AArch64. Existing rustc-layout slots handle aggregates;
existing scalar cells handle supported leaves. Dead formatting locals owned by
interception remain excluded; intercepted collection carriers and scalar values
needing Drop do not gain an unsupported cell. The common argument path rejects
remaining scalarized borrow bindings with `TCG-REF-ARG-STORAGE`. The call-argument prepass and refusal are scoped to Linux AArch64. The anonymous-vararg refusal keeps its existing code.

The permanent corpus in
[residual_conversion.rs](../../../crates/rustc-codegen-trust-cg/tests/support/residual_conversion.rs)
and its `reference_identity*` fixtures checks 25 cases. Independent GCC C
functions observe identity and shared interior mutation; Rust helpers observe
identity through ordinary calls. Existing aggregate/projected and vararg
fixtures retain mutation, register/stack overflow and unwind coverage.

## Qualified results

| Check | Result |
| --- | --- |
| Final LLVM/CG O0–O3, abort/unwind combined matrix | 128 native executions; 5,783,568 checks; 2,048 caught panics |
| New identity, enum and address-storage portion | 16 executions; 1,638,400 checks |
| Existing projected reference portion | 32 executions; 2,162,688 checks |
| Existing scalar/pointer/reference vararg portion | 80 executions; 1,982,480 checks; 2,048 caught panics |
| Unsupported scalar Drop storage | 2 named refusals; 2 successful LLVM controls |
| Existing vararg negatives | 6 old refusals plus 8 wide-pointer roots in 2 refused compilations; 8 successful LLVM controls |
| Strict bridge, O0 | 39 functions; 20 refined; 12 memo hits; zero skipped/unmodeled |
| Strict bridge, O2 | 28 functions; 6 refined; 3 memo hits; zero skipped/unmodeled |
| Machine-proof mode, O0/O2 | `TCG-PROOF-465` remains |
| Baseline and final CG core/alloc, O0 and O2 | All four mixed-runtime builds succeeded; 5 native consumers per build passed |

Each mixed-runtime set checks 81,097 UTF-8/value observations through each of
LLVM and CG consumer code, 21,504 formatting checks, and 112 caught panics with
matching Drop observations. The linked core and alloc are CG-built at the
stated optimization level; the rest of std and the executable drivers are
LLVM-built. Dynamic-loader logs and library/ELF hashes bind that boundary.
This is not an all-CG runtime or self-host result. Bridge refinement counts
are not complete memory, ABI, unwind or machine-code proofs.

## Caught O0 regression and correction

The first prototype passed the 17 original identity cases, all 112 existing
projected/vararg native runs, and the O2 mixed runtime. But its O0 core build
refused `Ordering::cmp`: promoting the derived comparison's discriminant
temporaries exposed an unimplemented `Rvalue::Discriminant` scalar-cell store.
The unchanged baseline O0 core and mixed consumers passed. A small derived
`repr(i8)`/`repr(u32)` enum corpus reproduced the first backend's O0 refusal;
LLVM O0/O2 and CG O2 compiled it.

The correction routes whole-cell discriminant assignments through the existing
`lower_discriminant` path, whose assignment completion already stores into the
cell. It reuses rustc's tag/niche decoding and signed widening. Any constant
binding published after assignment is cleared so the addressable result keeps
reading its cell. The permanent matrix now includes signed negative and high
unsigned discriminants, and the final O0 core/alloc runtime passes. The first
prototype's logs and census are retained; its O0 failure is not counted as a
successful build.

## Reference values stored in cells and wrapper fields

The broader prepass also exposed unsupported stores of shared reborrows, field
borrows, and projected pointer fields. Focused LLVM/CG O0/O2 comparisons bind
each correction to a pre-fix refusal. The final native corpus adds shared
reborrows from mutable references and raw pointers, raw/reference fields in
one-pointer structs, repeated field-address comparisons and nested field
references. Independent C helpers read through those pointers and observe
values after pointer-field replacement.

A stored thin reborrow now copies the source's runtime pointer; a borrowed
scalar-cell field uses the original cell address. Field admission keeps the
existing exact layout witness: zero offset, one field at every level, the full
allocation's size and alignment, and the same allocated leaf type. Pointer
storage metadata is enabled for Linux AArch64; partial, padded, differently
aligned and competing-memory-slot projections retain their guards. The three
existing scalar-cell layout unit tests pass. A speculative projected-call-result
change was discarded because its supposed reproducer already compiled before
that change; it is absent from the final implementation.

## Complete O2 std censuses

All four use the same frontend, LLVM dependency artifacts, working directory
and recorded environment; only backend and output directory differ. All exited
1 with complete diagnostics and no timeout. None is a successful std build,
and elapsed time under concurrent work is not a benchmark.

| Backend | Failed roots | Seconds (not a benchmark) |
| --- | ---: | ---: |
| Baseline | 196 | 769.155 |
| First prototype, before O0 discriminant repair | 239 | 764.644 |
| Discriminant-corrected prototype | 239 | 712.696 |
| Final corrected backend | 207 | 714.284 |

By root identity, the final change removes 2 roots,
adds 13, and changes 40 remaining diagnostics.
The failed-root count therefore increases from 196 to 207. Twelve added roots
now refuse at `TCG-REF-ARG-STORAGE` because the argument still has only a
scalarized borrow binding. The thirteenth is an unresolved capability regression:
`ControlFlow<()>::eq` stores a reference to a projected zero-sized payload
into a cell, and that store path cannot yet produce its address. These are not
successful compilations. The removed roots are `Thread::new` and
`BufReader<StdinRaw>::read_buf_exact`. The 32-root reduction from the 239-root
prototype reflects the reborrow and field-storage corrections above.
The exact delta is transcribed below. Full std O0 was not rerun in this
milestone; the O0 results above concern the mixed CG-core/alloc runtime.

## Remaining boundaries

This closes the tested thin-reference call snapshot defect. It does not make
all reference lowering correct. A separate probe on the final backend confirms
that two shared `&dyn Trait` coercions from the same scalar still materialize
separate data addresses: LLVM passes, CG fails all 256 inputs at O0/O2. Copying
one already-coerced trait object twice passes the control. That coercion path
is the next correctness repair (`target/trait-reference-identity-investigation`).
The constant-trait-object unsize refusal is also still open.

An unresolved scalarized thin reference now refuses instead of changing
identity. The permanent negative uses a scalar wrapper with Drop whose real
storage is not admitted by this prepass. Other unsupported alias/projection
shapes retain existing refusals. Full CG std, self-hosting, complete machine
proofs, and compile/runtime superiority over LLVM and Clang remain unfinished.

## Reproduction and evidence

```sh
targo --unverified test --manifest-path crates/rustc-codegen-trust-cg/Cargo.toml --locked --test aarch64_c_fnabi_aggregate_linux --no-run --message-format=json
```

Freeze the bridge and test executable from Cargo's JSON artifacts. Set
`TCG_TEST_BACKEND_PATH`, `TCG_TEST_BACKEND_SHA256`, and
`C_FNABI_LINUX_KEEP_ARTIFACTS=1`, then run the executable with:

```text
residual_conversion::no_proof_reference_identity residual_conversion::no_proof_projected residual_conversion::no_proof_variadic --test-threads=1 --nocapture
```

Exact build, proof, native, std and mixed-runtime commands are in the local
receipts under `target/fixed-reference-identity-investigation`. Builds use two
jobs, incremental off, the pinned rustc-private sysroot and LLVM SDK; proof
runs use a private cache. Raw logs, JSON, objects and executables stay under
`target/`; this tracked record contains the narrative and artifact identities.

Trust frontend `ae9c2c1daa0fc80afbfd380e493f5581ac714acb`, 1.99.0-dev,
LLVM 22.1.2, host `aarch64-unknown-linux-gnu`. Cargo source pins: TrustIR
`8e81e98aa92d78934548ec435218ce530294f2c5`, Clean
`7330fa6cef4f16de5f449a4fce0404ab51269ffb`, AY
`f28345ff184e33551e9b9d9f509f831461dd8b24`. Packaged AY 0.27.0 build10454
is commit `657ce1821183b2076bb994167f830bde5d8e0509`; packaged Clean is 0.9.0.

## Artifact identities

| Artifact | SHA-256 |
| --- | --- |
| Baseline backend | `23065482ee898b3d78a8733e4660fd49cbbd930625d146c28fc5c7889f6a4081` |
| first backend | `0ff55ff02a80c8b0a861f55dc6f8b5b3a0c1a24a909ace36721610bfa81c9922` |
| second backend | `c563328d2b5777aae5c73f31e9a5e52b658291b8b05d9ff72819dd99916399cd` |
| third backend | `a41376feaba8aad742c8074270cb524d738cb394cae1c093cc1555712bc4821e` |
| fourth backend | `99d843857a7434bacbb843d44743e476aecefa106282e74f28c102acc2c39a4d` |
| fifth backend | `b7f8f435749f2d1e58792e49127cc1357b70531774e2153ad897115b75347274` |
| Local `native-first.test` | `6d9351529b98d5d34181bfaa3c2282ff2ce4a9bba8e61316856daa0e5ee0325e` |
| Local `native-sixth.test` | `e905a8f6a8ad2b08183610bef61657d637a625378e12ff1ceae2a6225f87bc1d` |
| Local `native-fifth-artifacts-manifest.json` | `1154938258208b217dfa8663503b449db24bb59467f016780a0e78b55eef13d4` |
| Local `mixed-fifth-native-manifest.json` | `f57dc12ef2ca21ee8e0fc2d68d5c4e029dea4249db3ad9680a810173f4c21165` |
| Local `strict-fifth-summary.json` | `256577d81116494055e50f557fd075c510d29b01fd6d92aa5116865395381e79` |
| Local `qualification-fifth-source-manifest.json` | `031f84582c0b52904e57c23ae114106efaa352159bbc1a36c3e8d65261d7f755` |
| Local `fifth-source-manifest.json` | `30c098af5db52dbbc27cd1b40cf2066264e9440173ce527fb2843c5deba85bb2` |
| Local `std-O2-baseline-results.json` | `4a4bcec5e1c94ad49ad3c63a6179802601785de193ab50ac629576f0babb8b34` |
| Local `std-O2-first-results.json` | `3e4b0e40271237377dd58cb64f6e5f59abb4c55538075a57d93742019d95387c` |
| Local `std-O2-second-results.json` | `74837f5400b13a08910a747923299fdf8fca3087569ca45008b25eecde35b291` |
| Local `std-O2-fifth-results.json` | `3af687b21a4fa3e8c5175c42869aa4bca3553e7052ba0ae310c446200355aef4` |
| Local `std-delta-fifth.json` | `24a34eb512ecadee2aeefeaab0a187b7e984bf8d6956c358d08e667f34cda5b9` |
| trustc executable | `b2d4fa4bb1ce8106539d7c2967f1eb3f3f613293b8c905de586fbb4f5ffa4212` |
| targo executable | `4d877f14d86c786a1c077d5423f14304493d56ecf058447d6d8244cbb8a446ba` |
| ay executable | `81efc9f3bc4058062a64de75b4dd9827217a7b5f7b315f257b757bff818de0c5` |
| clean executable | `2d0c4b4be1513b5b59f0d4fd21c7f0e9a249693a7dd3d5fad14d702aa0e27f19` |
| cc executable | `a20520ee21543f243d40636a9181a142c45ecd989de31ab86b99a8ea5ada870d` |
| Local `mixed-baseline-O0-results.json` | `cb1fb4a4fd705c40b6cf20f1f143758dd8a5f78bb6e7f75e962bc5ab836565ee` |
| Local `mixed-baseline-O0-dynamic-results.json` | `033fe0e9cfb371f78d16bb71a123e034638dbf5172615d5355327bfec354830b` |
| Local `mixed-baseline-O0-dynamic-sysroot.json` | `34d5f11b69f8266dc3150fae66eddbaf8585fa95053758b19eab187e0d109f28` |
| Local `mixed-baseline-O2-results.json` | `2caf72d0accef78b31832d803b6751491287b73f1d18ee972e5bf278caf2b245` |
| Local `mixed-baseline-O2-dynamic-results.json` | `3b613d668d3b945b133ea77376131eb5ca49286874e6d3a71aa7f63b2a77ed7c` |
| Local `mixed-baseline-O2-dynamic-sysroot.json` | `22043eec00b96bd6e16c591412ea8845a3c925dbe22cbe35560154ae144c9104` |
| Local `mixed-fifth-O0-results.json` | `6e00a5fad57be6eb77fe19e8bb5e9d5c94ccff230553a0816d1ebde95e5d413f` |
| Local `mixed-fifth-O0-dynamic-results.json` | `4be39c59585a28978af53550accbd60a804bfd6b7c8b552dfbdc7cf323b57c2c` |
| Local `mixed-fifth-O0-dynamic-sysroot.json` | `3fbf8b4785aaa48d65168839d1896c6913a17547693df32447f0aa1dc0bddc12` |
| Local `mixed-fifth-O2-results.json` | `887bcf8171e426d925377f990e6a3a2d9bff7a3527d87f2599bf9bcf605b8ba8` |
| Local `mixed-fifth-O2-dynamic-results.json` | `c2f3c858894db7b524303e161465164b0a98a307461357b00ee6e18c1921a144` |
| Local `mixed-fifth-O2-dynamic-sysroot.json` | `0027dc14819b50cd0a4c46c6100444007931ea0e1108990eced2de723dcdbe53` |

### Final native executable identities

Paths are relative to the retained test directory.

| Case | ELF SHA-256 |
| --- | --- |
| aggregate-reference-abort/cg-O0/native.elf | `bf6863ce0c1c59743439a8c48dda8b583f19936aa06e2b11180a271235dad0ee` |
| aggregate-reference-abort/cg-O1/native.elf | `1adae38dfaff17a0f1d36f4cd6592c4933e9ac552f43c07a4425838eaa7b12e5` |
| aggregate-reference-abort/cg-O2/native.elf | `d6ec1a8ba04d1a78c0a0102688ab485a95ff58d73ba706226fd27e21fbd03c60` |
| aggregate-reference-abort/cg-O3/native.elf | `d6ec1a8ba04d1a78c0a0102688ab485a95ff58d73ba706226fd27e21fbd03c60` |
| aggregate-reference-abort/llvm-O0/native.elf | `7affe550bded4306e88abe672e5256ec47872f70e2ce6ecd3717d973d951267b` |
| aggregate-reference-abort/llvm-O1/native.elf | `bd35ec390604dd3ab8cbe2da32a5cf5f0a8157c4c08183af57ecf9f0501388ff` |
| aggregate-reference-abort/llvm-O2/native.elf | `6cdf89fe77a0835c92a9e1ba2e5a903efab277eddf5c4983e35da003991c3c07` |
| aggregate-reference-abort/llvm-O3/native.elf | `6cdf89fe77a0835c92a9e1ba2e5a903efab277eddf5c4983e35da003991c3c07` |
| aggregate-reference-unwind/cg-O0/native.elf | `31a8660d02444238ae0f6d23fe205a084f2ae8726fc2205690b332ed3f8e0221` |
| aggregate-reference-unwind/cg-O1/native.elf | `a63249da158bd0c056a4a90358e5cef0fbc54bb6f88ed2a7c5f34091a8fbe877` |
| aggregate-reference-unwind/cg-O2/native.elf | `bc92397eeac58e4fe17c0a5ae3e4c6bd37feba535dcb70cb0c5de21c91dcb294` |
| aggregate-reference-unwind/cg-O3/native.elf | `bc92397eeac58e4fe17c0a5ae3e4c6bd37feba535dcb70cb0c5de21c91dcb294` |
| aggregate-reference-unwind/llvm-O0/native.elf | `e6523d019eaa26da6d64511e95b0a75a41ee9d1589bc0ba18a2cdbbf4417939c` |
| aggregate-reference-unwind/llvm-O1/native.elf | `0f4de7a29c8c0863b09dd4af4df5b3dd13315589156db3b720620a195c4874e6` |
| aggregate-reference-unwind/llvm-O2/native.elf | `33ee07693b541ec254783e62aad2ede33fb2ec59a850cd892e4f98675288faff` |
| aggregate-reference-unwind/llvm-O3/native.elf | `33ee07693b541ec254783e62aad2ede33fb2ec59a850cd892e4f98675288faff` |
| projected-reference-abort/cg-O0/native.elf | `2a725113937c2a4e7e79d28b7d41b0b9ae9553aefb57dd3c8cee8dc943cdbc13` |
| projected-reference-abort/cg-O1/native.elf | `203f00e7c0496571ff17d604bf69ca86bd2119c0fe3a9fabdc668eb34b64246f` |
| projected-reference-abort/cg-O2/native.elf | `d396f6a3ece7b1f6c39ce839aa246c2f10202da87a7fdc26a8929c16a413130e` |
| projected-reference-abort/cg-O3/native.elf | `d396f6a3ece7b1f6c39ce839aa246c2f10202da87a7fdc26a8929c16a413130e` |
| projected-reference-abort/llvm-O0/native.elf | `5e89e9e26a1df2061e5893e18fbb566fc5b7d496499f24d0a163cae511fa991b` |
| projected-reference-abort/llvm-O1/native.elf | `cbbe1f3ca0a13b5c31a4f6e8c12b292b3a99bf06b413851103909926b0393357` |
| projected-reference-abort/llvm-O2/native.elf | `26d2f7c8405a25586e21467e15564317a69cb2fb5aac0aaf0c8c699a81c45e6b` |
| projected-reference-abort/llvm-O3/native.elf | `26d2f7c8405a25586e21467e15564317a69cb2fb5aac0aaf0c8c699a81c45e6b` |
| projected-reference-unwind/cg-O0/native.elf | `6639231f1d459279b4f230181f00b5330e749f0ff66869c4aaeaa5607d659d04` |
| projected-reference-unwind/cg-O1/native.elf | `ecc9bc1d4d5e6a8682914491b697dd6e7a13f72bd35dd2ee9c74fd1fd05e954d` |
| projected-reference-unwind/cg-O2/native.elf | `821ae02634a1359cdaef6d5841ae3a37f310ddca27709d69ad13f45b464719fb` |
| projected-reference-unwind/cg-O3/native.elf | `821ae02634a1359cdaef6d5841ae3a37f310ddca27709d69ad13f45b464719fb` |
| projected-reference-unwind/llvm-O0/native.elf | `a2073536c676e68e61476c13905c8a9fc9fa87b4c6b392b6a4d0ec698a6b51d4` |
| projected-reference-unwind/llvm-O1/native.elf | `00c2c02eba56ff82cc32d41263d10705e6a7c40be1c98b6671a43c3de3c4cfb9` |
| projected-reference-unwind/llvm-O2/native.elf | `12d376bfcf5330fa86dbe5d27dc25518666251a7c8edc29f03c8f9bdc55b2386` |
| projected-reference-unwind/llvm-O3/native.elf | `12d376bfcf5330fa86dbe5d27dc25518666251a7c8edc29f03c8f9bdc55b2386` |
| abort/cg-O0/native.elf | `0f977511819fa0f25b985d6c4d4d1591e4fabf93b0f4362d7808879f262c8a72` |
| abort/cg-O1/native.elf | `a47e387cb91e342ef2a85ae9f64e01cfa7c0338469b0b2d5b757e8df9d9c8c46` |
| abort/cg-O2/native.elf | `c3c75eb456763773b32aaa1a453bc6f0b594187ab26198e73ed25389093dbbd5` |
| abort/cg-O3/native.elf | `81793144207fba24c4d0ee93147b75f79676fa44126c3ba186cb4d54abaa45eb` |
| abort/llvm-O0/native.elf | `5b04c54957270d1eff860ca1d24e7052943dda97aea809b18a0a33082d4cd667` |
| abort/llvm-O1/native.elf | `19c5dd4283a6b34871ebfad9f9fa3648dc646a38ae63cd108bb409799b7f4edf` |
| abort/llvm-O2/native.elf | `07d4644cc0acc2923367f24e16da319e495175530fede216ceb7ed914dcde15a` |
| abort/llvm-O3/native.elf | `07d4644cc0acc2923367f24e16da319e495175530fede216ceb7ed914dcde15a` |
| unwind/cg-O0/native.elf | `e46c0aa41e6e503eed113e4e4f7a1d5b56a89f07ba5ef804a68875d6523198e1` |
| unwind/cg-O1/native.elf | `23789e4efdccd2de45cc85388351181810f9c6ea8831c078dbf7df8f452db956` |
| unwind/cg-O2/native.elf | `a45898244a77bf0e1b551038706c6fa7389ad8dc88a711a12f610cf62b544071` |
| unwind/cg-O3/native.elf | `4bc4b8607e756d3d244f7535ac781e4698d9aaf6041cd7add508ffb81cdbf46e` |
| unwind/llvm-O0/native.elf | `1f9e19aca09c18c9ecf82e06f8ee35ec4d08223688a6ebf7b7d97065ca684321` |
| unwind/llvm-O1/native.elf | `89ba32e269b34aa78f9aaf9cdb728c63545f380b3d69cccf479b9b82923f3156` |
| unwind/llvm-O2/native.elf | `f862113fcb27aa347b122a57aea80afa46b342b8da6f65b389e0c909caf3fa57` |
| unwind/llvm-O3/native.elf | `f862113fcb27aa347b122a57aea80afa46b342b8da6f65b389e0c909caf3fa57` |
| scalar-abort/cg-O0/native.elf | `37c5c83cd1cfb4da2873ff516c1605d04350def47219354a37055f9a398d693a` |
| scalar-abort/cg-O1/native.elf | `400b24b43f17ba40d0ae3e627d576fb88670be59c9c4ce8ad96ba33a8eca085a` |
| scalar-abort/cg-O2/native.elf | `9c1eba63c8e771828099a133e74c31be9590b55bace8685beb645eb435ae73e4` |
| scalar-abort/cg-O3/native.elf | `bfca090d1e04b21a5f59dd94c27e19ff663e1e22f701468f8527b0c1c8c746b3` |
| scalar-abort/llvm-O0/native.elf | `cc3971a4ecf1bb51e7f6463b60f289623f726b3854e2d61cef149fa403088f42` |
| scalar-abort/llvm-O1/native.elf | `5883873b6c620bbce915fdaf616dac3c4488be1628e32a6014502ae4b174b948` |
| scalar-abort/llvm-O2/native.elf | `9c786ffe25960eb02edde2824160df837755606f2eea515fbd01a66247df7a72` |
| scalar-abort/llvm-O3/native.elf | `bc4641b1eeb4175c50c16266a30b50aa38c1673f63330cdbb747821bd4c964a9` |
| scalar-unwind/cg-O0/native.elf | `cdd8a1cb639beb2b9bb90a195ae2b2da5ab4256326bf7246746bf2166f2e9fb2` |
| scalar-unwind/cg-O1/native.elf | `b20d60120db2fea3ad7d903608b10eeab3acd0f5e020feb399d29c884fea923f` |
| scalar-unwind/cg-O2/native.elf | `3cdbbac4072e2b41f3c9ddf57464a820347687dc9b07b59176c8d8d8b9a2eb71` |
| scalar-unwind/cg-O3/native.elf | `b045bbcb80acabb1251da0ad41d0edb052d757eaba5e794012b653a51f401a7d` |
| scalar-unwind/llvm-O0/native.elf | `7334dfe0308f5917e9b2f67e9125507bdd98b7e0743260071559a7d328015174` |
| scalar-unwind/llvm-O1/native.elf | `7a60235fda5669e8776ba4365489eb2933397657f4a8ad090fc5da9882afc45f` |
| scalar-unwind/llvm-O2/native.elf | `c12652299fba52eefbd8c7e7dc7907601806ede5bba98c8d37635f26afc76cc8` |
| scalar-unwind/llvm-O3/native.elf | `6bb301a759719be6d377fecf0bd2b080822c433ff405d5a6f0ca502bbcf4521f` |
| unwind-abort/cg-O0/native.elf | `8fd05b3dc8e400345588634ed47db71a3f9433e4b9f1f542a1c64f4cc3f04f7d` |
| unwind-abort/cg-O1/native.elf | `86ee6f69f155feee6edf5a7ef4e36770f0254a2af7e6f5d374153fd7877cca2b` |
| unwind-abort/cg-O2/native.elf | `ad59105104bd7a4dbd90520b7c0ad325581a2e30eb91e648323c6ca373e84593` |
| unwind-abort/cg-O3/native.elf | `aa8147eea4f03938e046f79b7c1d787079d479229251eb99c102aecbf9fab90e` |
| unwind-abort/llvm-O0/native.elf | `5de8802cad79f0b0b1430200ee17505c896a98cd3997aab08d39e0a86db12976` |
| unwind-abort/llvm-O1/native.elf | `d3ab249d17dad8450745e88edcecc4b07d88238d74521c22fe8bd3c808ad4859` |
| unwind-abort/llvm-O2/native.elf | `d3ab249d17dad8450745e88edcecc4b07d88238d74521c22fe8bd3c808ad4859` |
| unwind-abort/llvm-O3/native.elf | `d3ab249d17dad8450745e88edcecc4b07d88238d74521c22fe8bd3c808ad4859` |
| unwind-unwind/cg-O0/native.elf | `44fb866b77c28b4f835cd4289ecb30f28919ad6790258e92d2c425069c6a94b3` |
| unwind-unwind/cg-O1/native.elf | `bc615001aac4a38540b1f7a106954b4e94a5ac667646888e6c0076c6979c7a32` |
| unwind-unwind/cg-O2/native.elf | `d52dfd8ffd9583d03119985b2a7c2dac66648753972dc7f623408e6edfce4d18` |
| unwind-unwind/cg-O3/native.elf | `3a74fe0d99bd3d8dc9c42d6997431dfc461a707f74d0e07baabe22f7401cb522` |
| unwind-unwind/llvm-O0/native.elf | `2afbc6dd723c1cfc1effa51bf41225bcc7e71ff26e31533bcff83c080a44168e` |
| unwind-unwind/llvm-O1/native.elf | `8405aa2cc7dfdcb54fb98ae0c04cf286cb6ba4fcc83cb7c1e0764b82a9eef202` |
| unwind-unwind/llvm-O2/native.elf | `8405aa2cc7dfdcb54fb98ae0c04cf286cb6ba4fcc83cb7c1e0764b82a9eef202` |
| unwind-unwind/llvm-O3/native.elf | `8405aa2cc7dfdcb54fb98ae0c04cf286cb6ba4fcc83cb7c1e0764b82a9eef202` |
| abort/cg-O0/native.elf | `e1c854c5a76ff1a29f4e6124ea25f063fbdb43677e457a072809b2ce7ce40850` |
| abort/cg-O1/native.elf | `c09eee7b0963b840b3980ad4492b28ea6b9f0b57844942fa3e2c3f42d1b7a552` |
| abort/cg-O2/native.elf | `c7f412ff3e6308bb5782199050def5ed1dfd194167f01b6cb3d42bf989a6f273` |
| abort/cg-O3/native.elf | `60655353fb347abffeea49c8d93194e0b38559135e956aa456223c15dde6ca5a` |
| abort/llvm-O0/native.elf | `65fbdc3a6450cfb87d2a809d88e06e315b9329afec9e14ce4f67195806fcece9` |
| abort/llvm-O1/native.elf | `70804f8afe77ab4e46ac2c77ea4a4546fb81e81193b9aa3e0da212b8d0f4b4d9` |
| abort/llvm-O2/native.elf | `70804f8afe77ab4e46ac2c77ea4a4546fb81e81193b9aa3e0da212b8d0f4b4d9` |
| abort/llvm-O3/native.elf | `70804f8afe77ab4e46ac2c77ea4a4546fb81e81193b9aa3e0da212b8d0f4b4d9` |
| unwind/cg-O0/native.elf | `65d268dd1e0361ed2bd7fca92885b598e62451c48012760abfb6853dcc91a3cf` |
| unwind/cg-O1/native.elf | `711e964d46c339c484c47b33002ef0a5c89390bda699532724d1c24e2aecffb9` |
| unwind/cg-O2/native.elf | `088025a285dc2fee03e66c51633e9bed828636346ae71a3c2f016b2c6b52098d` |
| unwind/cg-O3/native.elf | `ee85744b41f7132d6145867faab040ebbd0c0f340ea99fde5a1d1a418a6c7666` |
| unwind/llvm-O0/native.elf | `a84392aa8967704e5fd9623b7405aa9934de4ed07c6e983bc8bfde6a084538ff` |
| unwind/llvm-O1/native.elf | `783fe8a7dd5583521e3e685afae335657fc4e151896ae8c97290a47416d5a23d` |
| unwind/llvm-O2/native.elf | `783fe8a7dd5583521e3e685afae335657fc4e151896ae8c97290a47416d5a23d` |
| unwind/llvm-O3/native.elf | `783fe8a7dd5583521e3e685afae335657fc4e151896ae8c97290a47416d5a23d` |
| scalar-abort/cg-O0/native.elf | `25ddce1dc83cd92620e3711b65184772fe1196a3e7f1941026daa09d3a260abc` |
| scalar-abort/cg-O1/native.elf | `f64f578420834a315a7ddb3e37f2c556279faf7a46b54f2ed52cdb8e4a7828ab` |
| scalar-abort/cg-O2/native.elf | `11f26a1396e6db98f043efccc2180014dc173aa9c4863c4164e27a26ce3809d6` |
| scalar-abort/cg-O3/native.elf | `76ac0e6a3562ba3e8ab42439207f094b4204020f94890c3d976be01c31aff231` |
| scalar-abort/llvm-O0/native.elf | `a92838926b5547d09b29903711de28622deb0780fef46319ecdbb59aada78e37` |
| scalar-abort/llvm-O1/native.elf | `cb6883cca85c563ded7047e1609ad2b288effc5211e473dc25e893c6990bbc81` |
| scalar-abort/llvm-O2/native.elf | `cb6883cca85c563ded7047e1609ad2b288effc5211e473dc25e893c6990bbc81` |
| scalar-abort/llvm-O3/native.elf | `cb6883cca85c563ded7047e1609ad2b288effc5211e473dc25e893c6990bbc81` |
| scalar-unwind/cg-O0/native.elf | `f5e3167d1a5cfa38d99905025d844db008155a8cd46959abd0d9d9ccfb8922e9` |
| scalar-unwind/cg-O1/native.elf | `6575124b3f895b7730285d922bf0c52892098109de7d596c259ec7b76a5a3d77` |
| scalar-unwind/cg-O2/native.elf | `25a09c569d8ceca694d03ecefa9741ec04dd159eea672eb2113ab77ac1416769` |
| scalar-unwind/cg-O3/native.elf | `8a7e7e824a23d464a19a1be10e9acbb3d67c83dec9e912c72054ddd99b5ed450` |
| scalar-unwind/llvm-O0/native.elf | `a6a93a42568e27ebb78f7efe242d08d7397761f2ed3177689b1ad930f392f936` |
| scalar-unwind/llvm-O1/native.elf | `9dbd62c619bf2b8ea87b3ec8a1441fcd66d59affc6febac429f763c4021be600` |
| scalar-unwind/llvm-O2/native.elf | `9dbd62c619bf2b8ea87b3ec8a1441fcd66d59affc6febac429f763c4021be600` |
| scalar-unwind/llvm-O3/native.elf | `9dbd62c619bf2b8ea87b3ec8a1441fcd66d59affc6febac429f763c4021be600` |
| unwind-abort/cg-O0/native.elf | `c7eecf645f5f13a1b43cbfabb3633ebe543b3b3023b0432d7afa31919dda7714` |
| unwind-abort/cg-O1/native.elf | `834bb9f1e86480c50ff7a5531ec90e286ea12c10d9c6cbeff6eaa5f75e1ea478` |
| unwind-abort/cg-O2/native.elf | `0076b90c7ff93dd08ca49903dee2e06a1662e93fda386ca3b1fcbe66e0a49718` |
| unwind-abort/cg-O3/native.elf | `0b72e8d7411af5418b7c2a3f4f3199fc0c297450ca4674b444084afd31ec74a1` |
| unwind-abort/llvm-O0/native.elf | `a64d5034e9baac6c1f02f4e1468a0826a0afb0a6d2a8407e6509e6b5f610fb99` |
| unwind-abort/llvm-O1/native.elf | `79de0d25a6bbe793d42f986007935c8121825a65674aeac4ba804971866d3054` |
| unwind-abort/llvm-O2/native.elf | `93c47a0bdb95909d7876a05e7acd731b81e65680ba6c11eceb17bc2f502d6f7b` |
| unwind-abort/llvm-O3/native.elf | `93c47a0bdb95909d7876a05e7acd731b81e65680ba6c11eceb17bc2f502d6f7b` |
| unwind-unwind/cg-O0/native.elf | `1d83c7707da380443aaafaa0b4a911291d5b75ab9a7a053ec698f98626a43cc8` |
| unwind-unwind/cg-O1/native.elf | `554f516c69b24866c04f215dcc883569de219270cf4a3c9aabdff75cbbbf8615` |
| unwind-unwind/cg-O2/native.elf | `373aa040d0f3a1cfe17ad667cd437ed6023e36aa70b3bc78562eedbd0cf93fff` |
| unwind-unwind/cg-O3/native.elf | `f8d7975d2d97d30027ed0a7400029ee9da062f4d08612b21ec80e6374a345c24` |
| unwind-unwind/llvm-O0/native.elf | `85b51f50f60ccc491b56e03975901fa91fee42017a38e9e392dfa9b66734cdfd` |
| unwind-unwind/llvm-O1/native.elf | `34b948949be3460b91554dacf42365f7f17675bc3e5b7407fb770f218744fc97` |
| unwind-unwind/llvm-O2/native.elf | `700e9ff381441b06bac61a9105ce9ac07d1f8e4aa5f2d4fc1efa23181a2a26de` |
| unwind-unwind/llvm-O3/native.elf | `700e9ff381441b06bac61a9105ce9ac07d1f8e4aa5f2d4fc1efa23181a2a26de` |

### Mixed-runtime executable identities

| Case | ELF SHA-256 |
| --- | --- |
| mixed-baseline-O0-dynamic-llvm/native.elf | `6bda32a217fbffa27dac721f0361fd2122b96f97ede6dd5e28ae383e0e61c5a8` |
| mixed-baseline-O0-dynamic-cg/native.elf | `03c7ee39440070a5c82aa66a6ba13fb3cb5ac79baa567a229061029a1e8ba6c0` |
| mixed-baseline-O0-dynamic-real-runtime/native.elf | `9dd7f5c4f5a9106085ec9e9de55d03f758cd7d60f9eec6997194e3043001a0e8` |
| mixed-baseline-O0-dynamic-mixed-core-panic/native.elf | `597f7d81eb3da9f076005b1e81be4986ff22eb9e0797a8ab33debb8bef65dec2` |
| mixed-baseline-O0-dynamic-core-reference-format/native.elf | `13e720ebf878861486527f807f6b732163ad4f98c5c6ce6ff06513176202915b` |
| mixed-baseline-O2-dynamic-llvm/native.elf | `db52b75aab2ba3a61e09d2ae6491871177b633e0f79be848e5935975f0358225` |
| mixed-baseline-O2-dynamic-cg/native.elf | `f361b367c1df038c196e96af5276b26161d76016248ce1c8219b9ac4885896a9` |
| mixed-baseline-O2-dynamic-real-runtime/native.elf | `01c797737b21472c4fdde802fb751e7128442eb113a9e5ad027f201f89ed9ee6` |
| mixed-baseline-O2-dynamic-mixed-core-panic/native.elf | `9b94f9694a7d69685c9b696794db1a3743807a402f98fbad19efb53faa66d141` |
| mixed-baseline-O2-dynamic-core-reference-format/native.elf | `bd2202799b1f194617469eaa0e6f3575fdbfe4fd33dcdb7f6dc4ba6f7d150a97` |
| mixed-fifth-O0-dynamic-llvm/native.elf | `f810de021dac906fbe1a24d7d49c5afe1812873c8c0687ccb5020c2bb6205086` |
| mixed-fifth-O0-dynamic-cg/native.elf | `da90cb87dc6fc82033933eeb926b01bd738c5278f0dfef1ab5c784cd4552e1c8` |
| mixed-fifth-O0-dynamic-real-runtime/native.elf | `9dd7f5c4f5a9106085ec9e9de55d03f758cd7d60f9eec6997194e3043001a0e8` |
| mixed-fifth-O0-dynamic-mixed-core-panic/native.elf | `597f7d81eb3da9f076005b1e81be4986ff22eb9e0797a8ab33debb8bef65dec2` |
| mixed-fifth-O0-dynamic-core-reference-format/native.elf | `13e720ebf878861486527f807f6b732163ad4f98c5c6ce6ff06513176202915b` |
| mixed-fifth-O2-dynamic-llvm/native.elf | `e8b57e193ee3255234980e56794ed3fb4e59550e7524025a4472a92018991617` |
| mixed-fifth-O2-dynamic-cg/native.elf | `7de8d7d5d098145a58ad50cd2ab25b07e3cd568c5edf10027c10c4d6bd6f4b2b` |
| mixed-fifth-O2-dynamic-real-runtime/native.elf | `01c797737b21472c4fdde802fb751e7128442eb113a9e5ad027f201f89ed9ee6` |
| mixed-fifth-O2-dynamic-mixed-core-panic/native.elf | `9b94f9694a7d69685c9b696794db1a3743807a402f98fbad19efb53faa66d141` |
| mixed-fifth-O2-dynamic-core-reference-format/native.elf | `bd2202799b1f194617469eaa0e6f3575fdbfe4fd33dcdb7f6dc4ba6f7d150a97` |

### Exact baseline census command

The other invocations substitute only the backend and output directory.

```sh
/home/ayates/trust-cg-soundness-20260914/trust-authored-qualified-20260924/trust-ae9c2c1d/bin/trustc --crate-name std --edition=2024 std/src/lib.rs --error-format=json --json=diagnostic-rendered-ansi,artifacts,future-incompat --crate-type dylib --crate-type rlib --emit=dep-info,link -C embed-bitcode=no -C codegen-units=1 --warn=unexpected_cfgs --check-cfg 'cfg(feature, values(any()))' --check-cfg 'cfg(target_has_reliable_f16)' --check-cfg 'cfg(target_has_reliable_f16_math)' --check-cfg 'cfg(target_has_reliable_f128)' --check-cfg 'cfg(target_has_reliable_f128_math)' --cfg 'feature="addr2line"' --cfg 'feature="backtrace"' --cfg 'feature="miniz_oxide"' --cfg 'feature="object"' --cfg 'feature="panic-unwind"' --check-cfg 'cfg(docsrs,test)' --check-cfg 'cfg(feature, values("addr2line", "backtrace", "backtrace-trace-only", "compiler-builtins-c", "compiler-builtins-mem", "debug_refcell", "llvm-libunwind", "llvm_enzyme", "miniz_oxide", "object", "optimize_for_size", "panic-unwind", "system-llvm-libunwind", "windows_raw_dylib"))' -C metadata=2151fd1de3847f13 --out-dir $HOME/trust-cg/target/fixed-reference-identity-investigation/std-O2-baseline --target aarch64-unknown-linux-gnu -C strip=debuginfo -L dependency=$HOME/trust-cg/target/std-build-investigation/llvm-resolve/target/aarch64-unknown-linux-gnu/debug/deps -L dependency=$HOME/trust-cg/target/std-build-investigation/llvm-resolve/target/debug/deps --extern priv:addr2line=$HOME/trust-cg/target/std-build-investigation/llvm-resolve/target/aarch64-unknown-linux-gnu/debug/deps/libaddr2line-12c7738545273db2.rlib --extern alloc=$HOME/trust-cg/target/std-build-investigation/llvm-resolve/target/aarch64-unknown-linux-gnu/debug/deps/liballoc-74b6f64c7e901880.rlib --extern priv:cfg_if=$HOME/trust-cg/target/std-build-investigation/llvm-resolve/target/aarch64-unknown-linux-gnu/debug/deps/libcfg_if-5b0a02a5eaac4739.rlib --extern core=$HOME/trust-cg/target/std-build-investigation/llvm-resolve/target/aarch64-unknown-linux-gnu/debug/deps/libcore-eaac2a498319830d.rlib --extern priv:hashbrown=$HOME/trust-cg/target/std-build-investigation/llvm-resolve/target/aarch64-unknown-linux-gnu/debug/deps/libhashbrown-ebb0e293be97ce62.rlib --extern libc=$HOME/trust-cg/target/std-build-investigation/llvm-resolve/target/aarch64-unknown-linux-gnu/debug/deps/liblibc-1db47c455d786c7a.rlib --extern priv:miniz_oxide=$HOME/trust-cg/target/std-build-investigation/llvm-resolve/target/aarch64-unknown-linux-gnu/debug/deps/libminiz_oxide-7392aa5c5bcbb032.rlib --extern priv:object=$HOME/trust-cg/target/std-build-investigation/llvm-resolve/target/aarch64-unknown-linux-gnu/debug/deps/libobject-a6517f9eb710ccae.rlib --extern priv:panic_abort=$HOME/trust-cg/target/std-build-investigation/llvm-resolve/target/aarch64-unknown-linux-gnu/debug/deps/libpanic_abort-79c82d310bffce8a.rlib --extern priv:panic_unwind=$HOME/trust-cg/target/std-build-investigation/llvm-resolve/target/aarch64-unknown-linux-gnu/debug/deps/libpanic_unwind-780ac334bb08e854.rlib --extern priv:rustc_demangle=$HOME/trust-cg/target/std-build-investigation/llvm-resolve/target/aarch64-unknown-linux-gnu/debug/deps/librustc_demangle-d615677db4ffd5d8.rlib --extern std_detect=$HOME/trust-cg/target/std-build-investigation/llvm-resolve/target/aarch64-unknown-linux-gnu/debug/deps/libstd_detect-b1e1c14d8899ece2.rlib --extern priv:unwind=$HOME/trust-cg/target/std-build-investigation/llvm-resolve/target/aarch64-unknown-linux-gnu/debug/deps/libunwind-a3d565b6442598f4.rlib -Z unstable-options -Ztrust-verify=off -Zforce-unstable-if-unmarked -Ccodegen-units=1 --verbose --cfg backtrace_in_libstd --check-cfg 'cfg(netbsd10)' --check-cfg 'cfg(no_global_oom_handling)' --check-cfg 'cfg(restricted_std)' --check-cfg 'cfg(backtrace_in_libstd)' --check-cfg 'cfg(vxworks_lt_25_09)' -Copt-level=2 -Zcodegen-backend=$HOME/trust-cg/target/variadic-reference-investigation/merged2-backend.so '-Ztrust-ir-cg-args=diag-json no-proof-certs time-codegen=20 time-lower'
```

### Removed roots

- `_RNvMs0_NtNtNtCsiYI7VriWazq_3std3sys6thread4unixNtB5_6Thread3new (reachable Rust-internal monomorphization, not a std-internal shim)`: [TCG-SSA-071] _RNvMs0_NtNtNtCsiYI7VriWazq_3std3sys6thread4unixNtB5_6Thread3new: trust-ir ssa/loop-completeness check failed: edge bb40->bb41 passes 1 arg(s) to a block with 0 param(s)
- `_RNvXs3_NtNtNtCsiYI7VriWazq_3std2io8buffered9bufreaderINtB5_9BufReaderNtNtB9_5stdio8StdinRawENtB9_4Read14read_buf_exactBb_ (reachable Rust-internal monomorphization, not a std-internal shim)`: [TCG-SCALAR-CELL-LAYOUT] projected cell must be an exact zero-offset, full-allocation primitive scalar field chain

### Added roots

- `_RNvMs3_NtNtNtNtCsiYI7VriWazq_3std3sys3net10connection6socketNtB5_9TcpStream15connect_timeout (reachable Rust-internal monomorphization, not a std-internal shim)`: [TCG-REF-ARG-STORAGE] call reference argument 0 has no stable referent address; a temporary would change pointer identity
- `_RNvMsD_NtCsiYI7VriWazq_3std2fsNtB5_10DirBuilder14create_dir_all (reachable Rust-internal monomorphization, not a std-internal shim)`: [TCG-REF-ARG-STORAGE] call reference argument 0 has no stable referent address; a temporary would change pointer identity
- `_RNvMsi_NtNtNtCsiYI7VriWazq_3std3sys2fs4unixNtB5_4File15try_lock_shared (reachable Rust-internal monomorphization, not a std-internal shim)`: [TCG-REF-ARG-STORAGE] call reference argument 0 has no stable referent address; a temporary would change pointer identity
- `_RNvMsi_NtNtNtCsiYI7VriWazq_3std3sys2fs4unixNtB5_4File8try_lock (reachable Rust-internal monomorphization, not a std-internal shim)`: [TCG-REF-ARG-STORAGE] call reference argument 0 has no stable referent address; a temporary would change pointer identity
- `_RNvNtNtCsiYI7VriWazq_3std3sys2fs24set_permissions_nofollow (reachable Rust-internal monomorphization, not a std-internal shim)`: [TCG-REF-ARG-STORAGE] call reference argument 0 has no stable referent address; a temporary would change pointer identity
- `_RNvNtNtCsiYI7VriWazq_3std6thread9functions12park_timeout (reachable Rust-internal monomorphization, not a std-internal shim)`: [TCG-REF-ARG-STORAGE] call reference argument 0 has no stable referent address; a temporary would change pointer identity
- `_RNvNtNtCsiYI7VriWazq_3std6thread9functions4park (reachable Rust-internal monomorphization, not a std-internal shim)`: [TCG-REF-ARG-STORAGE] call reference argument 0 has no stable referent address; a temporary would change pointer identity
- `_RNvNtNtNtCsiYI7VriWazq_3std12backtrace_rs9symbolize5gimli4mmap (reachable Rust-internal monomorphization, not a std-internal shim)`: [TCG-REF-ARG-STORAGE] call reference argument 0 has no stable referent address; a temporary would change pointer identity
- `_RNvNtNtNtCsiYI7VriWazq_3std3sys2fs4unix27open_to_and_set_permissions (reachable Rust-internal monomorphization, not a std-internal shim)`: [TCG-REF-ARG-STORAGE] call reference argument 0 has no stable referent address; a temporary would change pointer identity
- `_RNvNtNtNtCsiYI7VriWazq_3std3sys2fs4unix9open_from (reachable Rust-internal monomorphization, not a std-internal shim)`: [TCG-REF-ARG-STORAGE] call reference argument 0 has no stable referent address; a temporary would change pointer identity
- `_RNvNvMs3_NtNtNtNtCsiYI7VriWazq_3std3sys3net10connection6socketNtB7_9TcpStream7connect5inner (reachable Rust-internal monomorphization, not a std-internal shim)`: [TCG-REF-ARG-STORAGE] call reference argument 0 has no stable referent address; a temporary would change pointer identity
- `_RNvNvMs7_NtNtNtNtCsiYI7VriWazq_3std3sys3net10connection6socketNtB7_11TcpListener4bind5inner (reachable Rust-internal monomorphization, not a std-internal shim)`: [TCG-REF-ARG-STORAGE] call reference argument 0 has no stable referent address; a temporary would change pointer identity
- `_RNvXs9_NtNtCs6JUzFDSTeYc_4core3ops12control_flowINtB5_11ControlFlowuENtNtB9_3cmp9PartialEq2eqCsiYI7VriWazq_3std (reachable Rust-internal monomorphization, not a std-internal shim)`: Place deref memory store from Rvalue::Ref (projected source's base is not a reference to a memory-eligible aggregate)

### Changed diagnostics

- `_RINvNtNtNtNtCsiYI7VriWazq_3std3sys2io11kernel_copy5linux10fd_to_metaNtNtBa_2fs4FileEBa_ (reachable Rust-internal monomorphization, not a std-internal shim)`: before: Rvalue::Ref source projection is not scalar-bindable; after: [TCG-SCALAR-CELL-LAYOUT] projected cell must be an exact zero-offset, full-allocation scalar field chain
- `_RINvNtNtNtNtCsiYI7VriWazq_3std3sys2io11kernel_copy5linux10fd_to_metaNtNtNtBa_2io5stdio10StderrLockEBa_ (reachable Rust-internal monomorphization, not a std-internal shim)`: before: Rvalue::Ref source projection is not scalar-bindable; after: [TCG-SCALAR-CELL-LAYOUT] projected cell must be an exact zero-offset, full-allocation scalar field chain
- `_RINvNtNtNtNtCsiYI7VriWazq_3std3sys2io11kernel_copy5linux10fd_to_metaNtNtNtBa_2io5stdio10StdoutLockEBa_ (reachable Rust-internal monomorphization, not a std-internal shim)`: before: Rvalue::Ref source projection is not scalar-bindable; after: [TCG-SCALAR-CELL-LAYOUT] projected cell must be an exact zero-offset, full-allocation scalar field chain
- `_RINvNtNtNtNtCsiYI7VriWazq_3std3sys2io11kernel_copy5linux10fd_to_metaNtNtNtBa_2io5stdio9StdinLockEBa_ (reachable Rust-internal monomorphization, not a std-internal shim)`: before: Rvalue::Ref source projection is not scalar-bindable; after: [TCG-SCALAR-CELL-LAYOUT] projected cell must be an exact zero-offset, full-allocation scalar field chain
- `_RNCNvNtNtNtNtCsiYI7VriWazq_3std3sys6thread4unix7cgroups8quota_v1s0_0Bb_ (reachable Rust-internal monomorphization, not a std-internal shim)`: before: [TCG-REGALLOC-063] rustc_codegen_trust_cg: Trust Codegen object emission failed: pipeline error: register allocation failed: register allocation translation validation failed: __trust_cg_private.std.dd100f41ba537b6e-cgu.0.3557 (1 error(s)): spill-slot init: reload of slot26 at BlockId(33)/InstId(608) is not definitely initialized — control reaches it via predecessor BlockId(16) on a path with no dominating store to slot26 (split-connector placement); after: [TCG-REF-ARG-STORAGE] call reference argument 0 has no stable referent address; a temporary would change pointer identity
- `_RNCNvNtNtNtNtCsiYI7VriWazq_3std3sys6thread4unix7cgroups8quota_v20Bb_ (reachable Rust-internal monomorphization, not a std-internal shim)`: before: [TCG-REGALLOC-063] rustc_codegen_trust_cg: Trust Codegen object emission failed: pipeline error: instruction selection failed: value Value(3) not defined before use; after: [TCG-REF-ARG-STORAGE] call reference argument 0 has no stable referent address; a temporary would change pointer identity
- `_RNvMNtNtNtNtCsiYI7VriWazq_3std3sys2fs4unix3dirNtB2_3Dir8metadata (reachable Rust-internal monomorphization, not a std-internal shim)`: before: Rvalue::Ref source projection is not scalar-bindable; after: [TCG-SCALAR-CELL-LAYOUT] projected cell must be an exact zero-offset, full-allocation scalar field chain
- `_RNvMNtNtNtNtCsiYI7VriWazq_3std3sys7process4unix4unixNtNtB4_6common7Command11posix_spawn (reachable Rust-internal monomorphization, not a std-internal shim)`: before: [TCG-SSA-071] _RNvMNtNtNtNtCsiYI7VriWazq_3std3sys7process4unix4unixNtNtB4_6common7Command11posix_spawn: trust-ir ssa/loop-completeness check failed: edge bb23->bb135 passes 0 arg(s) to a block with 1 param(s); after: [TCG-REF-ARG-STORAGE] call reference argument 0 has no stable referent address; a temporary would change pointer identity
- `_RNvMNtNtNtNtCsiYI7VriWazq_3std3sys7process4unix4unixNtNtB4_6common7Command5spawn (reachable Rust-internal monomorphization, not a std-internal shim)`: before: Rvalue::RawPtr (unsupported &raw shape: source local _114 projection [Deref] type &'{erased} core::io::Error; base bound=false entry_arg=false); after: [TCG-REF-ARG-STORAGE] call reference argument 1 has no stable referent address; a temporary would change pointer identity
- `_RNvMNtNtNtNtNtCsiYI7VriWazq_3std3sys3net10connection6socket4unixNtB2_6Socket15connect_timeout (reachable Rust-internal monomorphization, not a std-internal shim)`: before: [TCG-SSA-071] _RNvMNtNtNtNtNtCsiYI7VriWazq_3std3sys3net10connection6socket4unixNtB2_6Socket15connect_timeout: trust-ir ssa/loop-completeness check failed: edge bb80->bb81 passes 1 arg(s) to a block with 0 param(s); after: [TCG-REF-ARG-STORAGE] call reference argument 0 has no stable referent address; a temporary would change pointer identity
- `_RNvMs0_NtNtCsiYI7VriWazq_3std4sync7barrierNtB5_7Barrier4wait (reachable Rust-internal monomorphization, not a std-internal shim)`: before: [TCG-SSA-071] _RNvMs0_NtNtCsiYI7VriWazq_3std4sync7barrierNtB5_7Barrier4wait: trust-ir ssa/loop-completeness check failed: edge bb2->bb8 passes 0 arg(s) to a block with 1 param(s); after: [TCG-REF-ARG-STORAGE] call reference argument 1 has no stable referent address; a temporary would change pointer identity
- `_RNvNtNtCsiYI7VriWazq_3std6thread7current18current_or_unnamed (reachable Rust-internal monomorphization, not a std-internal shim)`: before: Rvalue::Ref source projection is not scalar-bindable; after: [TCG-SCALAR-CELL-LAYOUT] projected cell must be an exact zero-offset, full-allocation scalar field chain
- `_RNvNtNtCsiYI7VriWazq_3std6thread7current7current (reachable Rust-internal monomorphization, not a std-internal shim)`: before: Rvalue::Ref source projection is not scalar-bindable; after: [TCG-SCALAR-CELL-LAYOUT] projected cell must be an exact zero-offset, full-allocation scalar field chain
- `_RNvNtNtNtNtCsiYI7VriWazq_3std12backtrace_rs9symbolize5gimli19parse_running_mmaps10parse_maps (reachable Rust-internal monomorphization, not a std-internal shim)`: before: [TCG-SSA-071] _RNvNtNtNtNtCsiYI7VriWazq_3std12backtrace_rs9symbolize5gimli19parse_running_mmaps10parse_maps: trust-ir ssa/loop-completeness check failed: edge bb8->bb14 passes 0 arg(s) to a block with 1 param(s); after: [TCG-REF-ARG-STORAGE] call reference argument 0 has no stable referent address; a temporary would change pointer identity
- `_RNvNtNtNtNtCsiYI7VriWazq_3std3sys6thread4unix7cgroups5quota (reachable Rust-internal monomorphization, not a std-internal shim)`: before: [TCG-SSA-071] _RNvNtNtNtNtCsiYI7VriWazq_3std3sys6thread4unix7cgroups5quota: trust-ir ssa/loop-completeness check failed: edge bb37->bb38 passes 1 arg(s) to a block with 0 param(s); after: [TCG-REF-ARG-STORAGE] call reference argument 0 has no stable referent address; a temporary would change pointer identity
- `_RNvNtNtNtNtCsiYI7VriWazq_3std3sys7process4unix6common11read_output (reachable Rust-internal monomorphization, not a std-internal shim)`: before: Place projection; after: [TCG-REF-ARG-STORAGE] call reference argument 0 has no stable referent address; a temporary would change pointer identity
- `_RNvNvNtCsiYI7VriWazq_3std2fs4read5inner (reachable Rust-internal monomorphization, not a std-internal shim)`: before: [TCG-SSA-071] _RNvNvNtCsiYI7VriWazq_3std2fs4read5inner: trust-ir ssa/loop-completeness check failed: edge bb13->bb10 passes 0 arg(s) to a block with 1 param(s); after: [TCG-REF-ARG-STORAGE] call reference argument 0 has no stable referent address; a temporary would change pointer identity
- `_RNvNvNtCsiYI7VriWazq_3std2fs5write5inner (reachable Rust-internal monomorphization, not a std-internal shim)`: before: [TCG-REGALLOC-063] rustc_codegen_trust_cg: Trust Codegen object emission failed: pipeline error: instruction selection failed: value Value(35) not defined before use; after: [TCG-REF-ARG-STORAGE] call reference argument 0 has no stable referent address; a temporary would change pointer identity
- `_RNvXNtNtNtCsiYI7VriWazq_3std2os4unix2ioNtNtNtB8_2io5stdio6StdoutNtB2_8StdioExt7take_fd (reachable Rust-internal monomorphization, not a std-internal shim)`: before: [TCG-REGALLOC-063] rustc_codegen_trust_cg: Trust Codegen object emission failed: pipeline error: instruction selection failed: value Value(7) not defined before use; after: [TCG-REF-ARG-STORAGE] call reference argument 0 has no stable referent address; a temporary would change pointer identity
- `_RNvXs1_NtNtNtCsiYI7VriWazq_3std3sys5stdio4unixNtB5_6StdoutNtNtBb_2io5Write14write_vectored (reachable Rust-internal monomorphization, not a std-internal shim)`: before: Rvalue::Ref source projection is not scalar-bindable; after: [TCG-SCALAR-CELL-LAYOUT] projected cell must be an exact zero-offset, full-allocation scalar field chain
- `_RNvXs1_NtNtNtCsiYI7VriWazq_3std3sys5stdio4unixNtB5_6StdoutNtNtBb_2io5Write5write (reachable Rust-internal monomorphization, not a std-internal shim)`: before: Rvalue::Ref source projection is not scalar-bindable; after: [TCG-SCALAR-CELL-LAYOUT] projected cell must be an exact zero-offset, full-allocation scalar field chain
- `_RNvXs2_NtNtNtCsiYI7VriWazq_3std2os4unix2ioNtNtNtBb_2io5stdio6StderrNtB5_8StdioExt7take_fd (reachable Rust-internal monomorphization, not a std-internal shim)`: before: [TCG-REGALLOC-063] rustc_codegen_trust_cg: Trust Codegen object emission failed: pipeline error: instruction selection failed: value Value(7) not defined before use; after: [TCG-REF-ARG-STORAGE] call reference argument 0 has no stable referent address; a temporary would change pointer identity
- `_RNvXs3_NtNtNtCsiYI7VriWazq_3std3sys5stdio4unixNtB5_6StderrNtNtBb_2io5Write14write_vectored (reachable Rust-internal monomorphization, not a std-internal shim)`: before: Rvalue::Ref source projection is not scalar-bindable; after: [TCG-SCALAR-CELL-LAYOUT] projected cell must be an exact zero-offset, full-allocation scalar field chain
- `_RNvXs3_NtNtNtCsiYI7VriWazq_3std3sys5stdio4unixNtB5_6StderrNtNtBb_2io5Write5write (reachable Rust-internal monomorphization, not a std-internal shim)`: before: Rvalue::Ref source projection is not scalar-bindable; after: [TCG-SCALAR-CELL-LAYOUT] projected cell must be an exact zero-offset, full-allocation scalar field chain
- `_RNvXs_NtNtNtCsiYI7VriWazq_3std3sys5stdio4unixNtB4_5StdinNtNtBa_2io4Read13read_vectored (reachable Rust-internal monomorphization, not a std-internal shim)`: before: Rvalue::Ref source projection is not scalar-bindable; after: [TCG-SCALAR-CELL-LAYOUT] projected cell must be an exact zero-offset, full-allocation scalar field chain
- `_RNvXs_NtNtNtCsiYI7VriWazq_3std3sys5stdio4unixNtB4_5StdinNtNtBa_2io4Read4read (reachable Rust-internal monomorphization, not a std-internal shim)`: before: Rvalue::Ref source projection is not scalar-bindable; after: [TCG-SCALAR-CELL-LAYOUT] projected cell must be an exact zero-offset, full-allocation scalar field chain
- `_RNvXs_NtNtNtCsiYI7VriWazq_3std3sys5stdio4unixNtB4_5StdinNtNtBa_2io4Read8read_buf (reachable Rust-internal monomorphization, not a std-internal shim)`: before: Rvalue::Ref source projection is not scalar-bindable; after: [TCG-SCALAR-CELL-LAYOUT] projected cell must be an exact zero-offset, full-allocation scalar field chain
- `_RNvXsc_NtNtNtCsiYI7VriWazq_3std3sys2fs4unixNtB5_9DirStreamNtNtNtCs6JUzFDSTeYc_4core3ops4drop4Drop4drop (reachable Rust-internal monomorphization, not a std-internal shim)`: before: Rvalue::RawPtr (unsupported &raw shape: source local _12 projection [Deref] type &'{erased} core::io::Error; base bound=false entry_arg=false); after: [TCG-REF-ARG-STORAGE] call reference argument 0 has no stable referent address; a temporary would change pointer identity
- `_RNvXsf_NtNtCsiYI7VriWazq_3std2io5stdioRNtB5_6StdoutNtB7_5Write14write_vectored (reachable Rust-internal monomorphization, not a std-internal shim)`: before: [TCG-REGALLOC-063] rustc_codegen_trust_cg: Trust Codegen object emission failed: pipeline error: instruction selection failed: value Value(16) not defined before use; after: [TCG-REF-ARG-STORAGE] call reference argument 0 has no stable referent address; a temporary would change pointer identity
- `_RNvXsf_NtNtCsiYI7VriWazq_3std2io5stdioRNtB5_6StdoutNtB7_5Write18write_all_vectored (reachable Rust-internal monomorphization, not a std-internal shim)`: before: [TCG-REGALLOC-063] rustc_codegen_trust_cg: Trust Codegen object emission failed: pipeline error: instruction selection failed: value Value(16) not defined before use; after: [TCG-REF-ARG-STORAGE] call reference argument 0 has no stable referent address; a temporary would change pointer identity
- `_RNvXsf_NtNtCsiYI7VriWazq_3std2io5stdioRNtB5_6StdoutNtB7_5Write5flush (reachable Rust-internal monomorphization, not a std-internal shim)`: before: [TCG-REGALLOC-063] rustc_codegen_trust_cg: Trust Codegen object emission failed: pipeline error: instruction selection failed: value Value(6) not defined before use; after: [TCG-REF-ARG-STORAGE] call reference argument 0 has no stable referent address; a temporary would change pointer identity
- `_RNvXsf_NtNtCsiYI7VriWazq_3std2io5stdioRNtB5_6StdoutNtB7_5Write5write (reachable Rust-internal monomorphization, not a std-internal shim)`: before: [TCG-REGALLOC-063] rustc_codegen_trust_cg: Trust Codegen object emission failed: pipeline error: instruction selection failed: value Value(16) not defined before use; after: [TCG-REF-ARG-STORAGE] call reference argument 0 has no stable referent address; a temporary would change pointer identity
- `_RNvXsf_NtNtCsiYI7VriWazq_3std2io5stdioRNtB5_6StdoutNtB7_5Write9write_all (reachable Rust-internal monomorphization, not a std-internal shim)`: before: [TCG-REGALLOC-063] rustc_codegen_trust_cg: Trust Codegen object emission failed: pipeline error: instruction selection failed: value Value(16) not defined before use; after: [TCG-REF-ARG-STORAGE] call reference argument 0 has no stable referent address; a temporary would change pointer identity
- `_RNvXsf_NtNtCsiYI7VriWazq_3std2io5stdioRNtB5_6StdoutNtB7_5Write9write_fmt (reachable Rust-internal monomorphization, not a std-internal shim)`: before: [TCG-REGALLOC-063] rustc_codegen_trust_cg: Trust Codegen object emission failed: pipeline error: instruction selection failed: value Value(21) not defined before use; after: [TCG-REF-ARG-STORAGE] call reference argument 0 has no stable referent address; a temporary would change pointer identity
- `_RNvXsp_NtNtCsiYI7VriWazq_3std2io5stdioRNtB5_6StderrNtB7_5Write14write_vectored (reachable Rust-internal monomorphization, not a std-internal shim)`: before: [TCG-REGALLOC-063] rustc_codegen_trust_cg: Trust Codegen object emission failed: pipeline error: instruction selection failed: value Value(16) not defined before use; after: [TCG-REF-ARG-STORAGE] call reference argument 0 has no stable referent address; a temporary would change pointer identity
- `_RNvXsp_NtNtCsiYI7VriWazq_3std2io5stdioRNtB5_6StderrNtB7_5Write18write_all_vectored (reachable Rust-internal monomorphization, not a std-internal shim)`: before: [TCG-REGALLOC-063] rustc_codegen_trust_cg: Trust Codegen object emission failed: pipeline error: instruction selection failed: value Value(16) not defined before use; after: [TCG-REF-ARG-STORAGE] call reference argument 0 has no stable referent address; a temporary would change pointer identity
- `_RNvXsp_NtNtCsiYI7VriWazq_3std2io5stdioRNtB5_6StderrNtB7_5Write5flush (reachable Rust-internal monomorphization, not a std-internal shim)`: before: [TCG-REGALLOC-063] rustc_codegen_trust_cg: Trust Codegen object emission failed: pipeline error: instruction selection failed: value Value(6) not defined before use; after: [TCG-REF-ARG-STORAGE] call reference argument 0 has no stable referent address; a temporary would change pointer identity
- `_RNvXsp_NtNtCsiYI7VriWazq_3std2io5stdioRNtB5_6StderrNtB7_5Write5write (reachable Rust-internal monomorphization, not a std-internal shim)`: before: [TCG-REGALLOC-063] rustc_codegen_trust_cg: Trust Codegen object emission failed: pipeline error: instruction selection failed: value Value(16) not defined before use; after: [TCG-REF-ARG-STORAGE] call reference argument 0 has no stable referent address; a temporary would change pointer identity
- `_RNvXsp_NtNtCsiYI7VriWazq_3std2io5stdioRNtB5_6StderrNtB7_5Write9write_all (reachable Rust-internal monomorphization, not a std-internal shim)`: before: [TCG-REGALLOC-063] rustc_codegen_trust_cg: Trust Codegen object emission failed: pipeline error: instruction selection failed: value Value(16) not defined before use; after: [TCG-REF-ARG-STORAGE] call reference argument 0 has no stable referent address; a temporary would change pointer identity
- `_RNvXsp_NtNtCsiYI7VriWazq_3std2io5stdioRNtB5_6StderrNtB7_5Write9write_fmt (reachable Rust-internal monomorphization, not a std-internal shim)`: before: [TCG-REGALLOC-063] rustc_codegen_trust_cg: Trust Codegen object emission failed: pipeline error: instruction selection failed: value Value(21) not defined before use; after: [TCG-REF-ARG-STORAGE] call reference argument 0 has no stable referent address; a temporary would change pointer identity

## Incoming main integration

After implementation and documentation commits, remote main advanced twice.
Merge `2e5cddd188aea19b4e988a0d11f258e316eb46cb` incorporates the FRINTN
ENC-5 decoder and census changes from `c05ef0773`; all 13 decoder census tests
and the affected coverage-gate test pass. The Linux/Darwin Python gate suites
ran 98 tests: 97 passed and one skipped.

The rebuilt merged backend is `f1af1399ca283dbec33ae0fa19586691c2f8a141029ab747eb692e5895497ab5`. With the same frozen native harness,
both reference-identity tests pass: 16 native executions and 1,638,400 checks,
plus two named storage refusals and two LLVM controls. The full 128-execution
matrix and std census above remain bound to the pre-merge fifth backend.

Merge `2703d0d811325dc8319230aa8efb09e6949fbc9f` additionally incorporates main `c83bda01a`'s ARC oracle and
inventory corrections. This second intake changes tests and documentation only;
production sources and Cargo inputs match the merged backend build. All six
Linux ARC tests and all 15 construct-inventory tests pass. The ARC native rows
exercise the C driver's model; the corrected oracle uses a CleanHeap twin and
does not establish that ARC operations on the compiled malloc-origin cells are
defined in TrustIR.

Local integration receipt `integration-final.json` has SHA-256
`08a555cd7ff615be74c44f0e41a0f8f496071193d9003780e2bcec4d31cf4692`. The merged native artifact manifest has
SHA-256 `49220a25196f2122a9822ec6e6b168eaef609d1eea20ef6fe133cb2df5626f8c`.

A third intake, merge `7bb77c3727dc1ba239b6f5b1e6dc96ae434de9f6`, includes
main `fc84c4c54` and its x86 vectorization legality repair `a9dd0f1db`. The only
production change is in `trust-cg-opt/src/x86_vectorize.rs`; all 147 tests in
that module pass. The AArch64 backend measurements above predate this x86
intake. Local `incoming-x86-vectorize.log` has SHA-256
`80b19fe1f0d181d531107ca09a908494eb407242057a5707490212be9f039049`.
