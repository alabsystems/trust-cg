# Direct C variadic calls on Linux AArch64 — 2026-09-29

The rustc-private bridge now lowers direct canonical-C variadic calls with
promoted 32/64-bit integers, `f64`, and thin raw pointers. It preserves the
fixed declaration and queries rustc's call `FnAbi` using the actual anonymous
operand types. Every admitted anonymous argument must have the matching sized
scalar layout and `PassMode::Direct`. Fixed arguments use the existing lowering;
tail arguments retain their mutable-reference reload bookkeeping. The shared
ordinary-call exact-arity check is unchanged.

This is diagnostic codegen support. Full CG std, self-hosting, machine-proof
completion, and superiority over LLVM/Clang remain open. No performance claim
is made from these concurrent, unoptimized backend builds or census durations.
Anonymous references, aggregates and 128-bit values remain outside this bounded
path. Nonempty indirect variadic calls retain their arity refusal. Zero-extra
direct, function-pointer and constant-address calls execute correctly. Other
targets retain their previous admission rules.

## Source and integration

- Implementation: `a8a32d069` (parent `b73602ee5`). The qualified build captured
  that patch before the commit; the first prototype differs only in formatting.
- First main merge: `0a686f828`, incorporating remote `b8d659caf`.
- Pointer-mutation fixtures and diagnostic census: `6a0c3a98b`.
- Second main merge: `5e06169d1`, incorporating remote `8d85bf68f`.
- Production code: [variadic.rs](../../../crates/rustc-codegen-trust-cg/src/variadic.rs).
  Permanent tests are in [residual_conversion.rs](../../../crates/rustc-codegen-trust-cg/tests/support/residual_conversion.rs)
  and its `variadic_*` / `negative_variadic_*` fixtures.

The first main merge includes stricter i128 CSET/CSEL provenance and Mach-O
relocation inventory binding, plus repository/documentation cleanup. The second
adds a derived-bit-vector query fallback that still requires independently
checked UNSAT; an exact-query counterexample remains final. No proof gate was
disabled for either integration.

## Results and boundaries

| Run | Result |
| --- | --- |
| Qualified backend, LLVM/CG O0–O3, abort/unwind | 32 executions; 753,680 checks; 1,024 caught panics |
| First merged backend, same matrix | Same 32 executions and counts |
| First merged backend, raw-pointer/fixed-reference mutation | 16 executions; 196,608 checks |
| Final merged backend, combined vararg matrix | 48 executions; 950,288 checks; 1,024 caught panics |
| Vararg negative controls, each qualified/merged/final backend | 6 expected refusals; 6 successful LLVM controls |
| First merged backend, existing from-end indexing regression | 16 executions; 391,424 checks; 4 expected refusals |
| Strict bridge, O0/O2, first/merged/final backends | 16/12 functions; 13/13 refined; 2/4 memo hits; 0 skips or unmodeled shapes |
| Machine-proof mode, O0/O2, all three backends | `TCG-PROOF-465` refusals retained |
| First incoming main qualification | 85 focused Rust test executions passed |
| Second incoming main qualification | 27 focused Rust test executions passed |
| Updated repository scripts | 267 unittest cases completed, 1 skipped, overall OK |

The C oracle consumes `va_list` compiled by GCC 13.3. Cases exercise shared
extern declarations at several arities, integer/FPR register exhaustion,
interleaved stack arguments, a fixed `f32`, signed/unsigned promoted scalars,
thin pointers, `open`/`fcntl`/`syscall`, callback unwinding through C with a Rust
cleanup guard, and mutation observed by the caller. LLVM compiles the Rust
driver and standard runtime; this matrix does not claim an all-CG runtime.
Bridge refinement counts concern scalar operation selection, not a complete
proof of operand wiring, calling convention, memory or unwinding.

The first incoming main tests cover condition admission (10), i128 data flow
(5), provenance (12), source-bound diamonds (10), NZCV consumers (40), Mach-O
digest/compile binding (5), ELF digest (1) and LSDA shape checks (2). Initial
diamond and unwind filter spellings selected zero tests; corrected filters
ran the 10 and 2 tests counted here. Zero-selected filters carry no credit.

## Completed std censuses

The isolated O2 std runs use the same frontend, LLVM-built dependency artifacts,
working directory and recorded environment. Commands differ only in backend
and output directory. Every census exited 1 with complete diagnostics; none
timed out. These are lowering-failure censuses, not successful std builds.

| Backend | Failed roots | Seconds (not a benchmark) |
| --- | ---: | ---: |
| Baseline | 216 | 734.794 |
| Qualified direct-vararg fix | 200 | 763.826 |
| First main merge | 200 | 733.282 |

The fix removes 16 roots, adds none, and changes four diagnostics from arity
failure to the explicit anonymous-reference refusal: `FileDesc::set_nonblocking`,
`Socket::set_nonblocking`, `PidFd::pid`, and `PidFd::exit_for_reaped_child`.
The other 196 remaining diagnostics are unchanged. All 200 diagnostic strings
are identical between the qualified and first merged censuses. The final
query-replay-only merge was rebuilt and received the full vararg native/strict
matrix; it has no separate full std census in this record. The prior O0 census
remains 197; this milestone does not rerun O0 std.

## Reproduction and local evidence

Build the bridge integration target with the pinned Trust package:

```sh
targo --unverified test --manifest-path crates/rustc-codegen-trust-cg/Cargo.toml --locked --test aarch64_c_fnabi_aggregate_linux --no-run --message-format=json
```

Freeze the emitted test executable and bridge dylib from the Cargo JSON records.
Run the executable with `residual_conversion::no_proof_variadic --test-threads=1
--nocapture`, setting `TCG_TEST_BACKEND_PATH` and `TCG_TEST_BACKEND_SHA256` to
that exact dylib and `C_FNABI_LINUX_KEEP_ARTIFACTS=1`. The harness recompiles its
embedded C/Rust fixtures and verifies the backend digest throughout.

The session used the rustc-private sysroot and LLVM SDK paths recorded in
`target/variadic-call-investigation/env.py`; builds used two jobs, incremental
off, and a private proof-cache directory. Exact build, strict, std, native and
unit commands are in the local JSON receipts. Development payloads stay out of
tree under the current evidence policy. Their location is
`target/variadic-call-investigation/`; the identities below bind the results.
Failed preliminary object-archive naming/link experiments remain there and
are not counted as successful executions.

## Identities

Trust frontend: `ae9c2c1daa0fc80afbfd380e493f5581ac714acb`, 1.99.0-dev,
LLVM 22.1.2, host `aarch64-unknown-linux-gnu`.
Both Cargo graphs resolve TrustIR `8e81e98aa92d78934548ec435218ce530294f2c5`,
Clean `7330fa6cef4f16de5f449a4fce0404ab51269ffb`, and AY
`f28345ff184e33551e9b9d9f509f831461dd8b24`. Those source pins differ from the
packaged checker binary identities: AY 0.27.0 build 10454, commit
`657ce1821183b2076bb994167f830bde5d8e0509`; Clean 0.9.0.

| Artifact | SHA-256 |
| --- | --- |
| baseline backend | `c16e04f9de9232dae5bd80ce3b8afc9c47549414b0bc470fb6861080e819815a` |
| first backend | `4159455512db4073f416d759666c0669da6340bfa3e39191e7577b42f23e1062` |
| qualified backend | `2099ec65945c5408f752fffc74837c30ca4e954d8809621ecd8e5c7b085445d5` |
| merged backend | `f267c0d727aed4499131601ff21bf9c2c782c3f723b9a33513dea2acc01b8aca` |
| merged2 backend | `4ed1b9c565af06e3b6129506301d747fb5cebbd05c2eaa56d1c0407dd407905f` |
| native-first.test | `16b93dbc802015fcae9b4766364413bf080bc3ad1a9b70bd8bd61ad6c5af6835` |
| native-mutation.test | `56d6b78e3ea328c96ea0844f950f9df21338fb06de01bfec010dd492a08b3bcf` |
| trust_cg_verify-merged.test | `919167db42b7b15d4ab5ca09cb679ed3ea90e3a3b31497496bbcf057b06f8822` |
| aarch64_nzcv_consumer_binding-merged.test | `ad3b2061c0e8512b5860f72481c200a56eb71dd473ebb7d7c8a34eb36ea140a7` |
| trust_cg_codegen-merged.test | `74297f2cf6c37464e327b0fa1999fe9290ceaeb0a79f9d699f76ffe80930f18f` |
| trust_cg_verify-merged2.test | `c666a17c147de4ed6a390e85368eae2d0924460f43a1241d5391606bed727dd3` |
| trustc executable | `b2d4fa4bb1ce8106539d7c2967f1eb3f3f613293b8c905de586fbb4f5ffa4212` |
| targo executable | `4d877f14d86c786a1c077d5423f14304493d56ecf058447d6d8244cbb8a446ba` |
| ay executable | `81efc9f3bc4058062a64de75b4dd9827217a7b5f7b315f257b757bff818de0c5` |
| clean executable | `2d0c4b4be1513b5b59f0d4fd21c7f0e9a249693a7dd3d5fad14d702aa0e27f19` |
| cc executable | `a20520ee21543f243d40636a9181a142c45ecd989de31ab86b99a8ea5ada870d` |
| Local `native-final-artifacts-manifest.json` | `8886bbf7a753a80f0c59f9465bd76017753c310fc39fc471612183be5eecfcb5` |
| Local `strict-final-summary.json` | `46c8cf9c959ea684fb87d704f1366bfade48b3ff4e59cd4c481000f223b36275` |
| Local `cohort-identity.json` | `a432cfdd17d9d3474147db9e77587c3b19a829635fc49cfe093f21053a33f442` |
| Local `qualification-source-manifest.json` | `fb579fe7f61d9833d3f0719fc3335b086552a2617665e8e1322b96fbc543928e` |
| Local `merged-source-manifest.json` | `904466e78e45005367735c8ac6723a6bd9de7937983a732ffb9b7460e0eca85d` |
| Local `merged2-source-manifest.json` | `16072580c260582568ecbf5805393bcf71c1faffea7ef11937de0d0e7ea75e49` |
| Local `std-O2-baseline-results.json` | `9abc4f99fa13b58e38bf956160c583f3aa319922dc43c143638cc7af1370a50c` |
| Local `std-O2-qualified-results.json` | `042fd9584aac56d9b7b4c3999672c88cdf5cff7c19d180fef37393fbefe33d18` |
| Local `std-O2-merged-results.json` | `2a4a3e52ec97d8138b5ee6a3ceccb10dd59285d774140caddc8e157f642e6e93` |
| Local `std-delta-qualified.json` | `6c811051f250520a54444c23ab3cb1f330b53303a55d31f410a75815b8ecc4e1` |

### Native executable identities

Rows identify every ELF counted above, relative to its retained test directory.

| Matrix / case | ELF SHA-256 |
| --- | --- |
| qualified/scalar-abort/cg-O0/native.elf | `23ff45433e768c3072b067743d5d4dca4392341119791be49baee071020e88bf` |
| qualified/scalar-abort/cg-O1/native.elf | `ef7282a0edea84e3632e673dbd7c53c4e4bb855bb698a922fbe3e703ae6b7bed` |
| qualified/scalar-abort/cg-O2/native.elf | `d4f60a254fd891ba4103264ad239e24c8361afd2ee171e88df4944f95b9a669d` |
| qualified/scalar-abort/cg-O3/native.elf | `ce55911d82d1eab294fddbf37d4cc84a43d6f27dd7fca920969e2ba81bf7af41` |
| qualified/scalar-abort/llvm-O0/native.elf | `84ab6f02eee83f8af671b28b223ce221e87ce1563c516df1ca7cd37d8cdcb077` |
| qualified/scalar-abort/llvm-O1/native.elf | `7c22956d7fcebd2ffc82059e48315acb0f4b999caa2c1656e076628dcd5660b6` |
| qualified/scalar-abort/llvm-O2/native.elf | `ebc9472d6879ba3c3d9ee58292a43065fc59f7527b6a6e39a608be451c9c93c2` |
| qualified/scalar-abort/llvm-O3/native.elf | `eac67e130f3739db4d22d8e918a67c25d61c15a6746caf53a68da2541235a70e` |
| qualified/scalar-unwind/cg-O0/native.elf | `9d4d0ac95fb5400ae16fed6260da239aaa63772a252f2053cf695404ae9c3929` |
| qualified/scalar-unwind/cg-O1/native.elf | `ce15773def8ad8d60682a1bd2e316c3cbc5e22b1b1803c6b819fc866df229a09` |
| qualified/scalar-unwind/cg-O2/native.elf | `0edb5df71fe1705f45a301c767003fdafdda24f1b5010c7a57e47b5b6be54731` |
| qualified/scalar-unwind/cg-O3/native.elf | `e52e18e71e138e9323cf7f446a4b9f268043d2f743e58f8106efd5f406300d5e` |
| qualified/scalar-unwind/llvm-O0/native.elf | `209b4dbfb6be5d4cd8bd620f6d85affaf0b783a0908a7f475d5203647c4579e3` |
| qualified/scalar-unwind/llvm-O1/native.elf | `6a70c8b55c6a2f381d2066fb6b518c01610c67c7f802084cd859f426b813dcaf` |
| qualified/scalar-unwind/llvm-O2/native.elf | `b8a7f59b41a23f6abb9fcfdb9f74054edf93a0da1f603852da3758b800b1ab4f` |
| qualified/scalar-unwind/llvm-O3/native.elf | `3a10687977f39efe3d6043ac4d5509e3fec8baabc7e01889335a66c49b9cfbd9` |
| qualified/unwind-abort/cg-O0/native.elf | `820d55e82b089bd14d50096fd3ed2ddc06991505c393a16e858091d4a5a21a9a` |
| qualified/unwind-abort/cg-O1/native.elf | `f538f5b720a9d9634a3f8018a469bb81ba8858dba1c1a213182df29bfc25eb26` |
| qualified/unwind-abort/cg-O2/native.elf | `ff80b1dec1a4033b45346f7a335c4fa61b55657356ba1ffa656af6911117cbcd` |
| qualified/unwind-abort/cg-O3/native.elf | `7d69e18ee33f8666f529a5c66eba787d058225538e7748c7be04ee822ccab2fd` |
| qualified/unwind-abort/llvm-O0/native.elf | `31b8096c63299bae5687d56665b9b13a3792dd4ae5192b5846ea765ed7959384` |
| qualified/unwind-abort/llvm-O1/native.elf | `b330e53fabb9dd56bee26b045ee1c40018cc55bba39bc72e4863731c4e057484` |
| qualified/unwind-abort/llvm-O2/native.elf | `b330e53fabb9dd56bee26b045ee1c40018cc55bba39bc72e4863731c4e057484` |
| qualified/unwind-abort/llvm-O3/native.elf | `b330e53fabb9dd56bee26b045ee1c40018cc55bba39bc72e4863731c4e057484` |
| qualified/unwind-unwind/cg-O0/native.elf | `c448f4c8bd33f11bc15e645850964ccdc7474a2eb3a76244525f7a44f1a357e0` |
| qualified/unwind-unwind/cg-O1/native.elf | `534c9b936969199fff005deb45ce5808cddfef7c84c43a2cedcb9904cfe71b4f` |
| qualified/unwind-unwind/cg-O2/native.elf | `3c3747be32515e218f4a90497e9d75a0844e7c0437311a0a28d2aa6b55da53be` |
| qualified/unwind-unwind/cg-O3/native.elf | `10af5e026aa563ca3e7cd7c2e1ed71137dbd22f3599c6ab8bd5e19bf02c4d099` |
| qualified/unwind-unwind/llvm-O0/native.elf | `b2782cfa05f3ef4d23ffd13fca6c76f01aab082bf54270f445e3ea4a2d84c82d` |
| qualified/unwind-unwind/llvm-O1/native.elf | `37bcf881423f38c8a5202712207f186ff33bbeec28f91fe7b808ef6a27653a5f` |
| qualified/unwind-unwind/llvm-O2/native.elf | `37bcf881423f38c8a5202712207f186ff33bbeec28f91fe7b808ef6a27653a5f` |
| qualified/unwind-unwind/llvm-O3/native.elf | `37bcf881423f38c8a5202712207f186ff33bbeec28f91fe7b808ef6a27653a5f` |
| merged/scalar-abort/cg-O0/native.elf | `15a97e1b60aae856be072f29d9e7b724b03211f116a8ba3b09c7feb910b62e77` |
| merged/scalar-abort/cg-O1/native.elf | `d7a3364e628127ca11cb01eaf4cf2d0e9e540696dfef3530482dca4de2a9c876` |
| merged/scalar-abort/cg-O2/native.elf | `f3daa0548c5c036fd2f7bc5ceaa6d872b2d562960f48429d0fce1688ed0569b4` |
| merged/scalar-abort/cg-O3/native.elf | `6e49e256f28e9818eb653c0028320cd53b74dc659078082b30c2d66c9135e933` |
| merged/scalar-abort/llvm-O0/native.elf | `ce49b07f6bcf73354f69b92556cce58d8478e8caba06371bd53cf405b3f172dc` |
| merged/scalar-abort/llvm-O1/native.elf | `1e6b96409c0a4e4ac36d4307adff092d302190fcb11395936d8ebbb6613f0596` |
| merged/scalar-abort/llvm-O2/native.elf | `ffd4643c507b21268223eb7a3468a995925ff66b0e0617c0f8d0c3b3632bf8f8` |
| merged/scalar-abort/llvm-O3/native.elf | `a236801b38a5638f29d87400eb0440d338d28c503a26773d25c8611e30fbc27d` |
| merged/scalar-unwind/cg-O0/native.elf | `b6ecf95dbdf267a2b11ebd82a55f14baca1b399b10d6a2d32b3c25e5f22be294` |
| merged/scalar-unwind/cg-O1/native.elf | `0158c7de3dfcba41b5b817ea050c69d1b1c7f0ee5161a0985e6f339e08f7dd50` |
| merged/scalar-unwind/cg-O2/native.elf | `a3cb2e424b832cbcfafeb9eb861f4cc24c364575f55d41abd802d07959ce0610` |
| merged/scalar-unwind/cg-O3/native.elf | `055963a0a5a7057555f81989df11119d68d02790ff3dc37d98294552b0131746` |
| merged/scalar-unwind/llvm-O0/native.elf | `7a78f3ee90b583f1e3d808823fff424e7334e42bf77373a05e88f5ecc1d3bd81` |
| merged/scalar-unwind/llvm-O1/native.elf | `a427c0c08793e9b264280fbf154e47a782a087983ff832c778d8cbae6ff54268` |
| merged/scalar-unwind/llvm-O2/native.elf | `675580aefd374f155c600cc21dc9896190a95949bb8c5389f90eee49d7323785` |
| merged/scalar-unwind/llvm-O3/native.elf | `4750309dfbe5ec18629dd44ccfdf5018e246befef277438105764f74fffd0b4c` |
| merged/unwind-abort/cg-O0/native.elf | `d25c9c5fd205ca6872bf9bd5f0ee6a7b5fd63aa9f7ce67775249305015f8e59b` |
| merged/unwind-abort/cg-O1/native.elf | `b54d3f5ab0ef340dd00db079f093a1413a2e09786b56853f3a395f9ead381180` |
| merged/unwind-abort/cg-O2/native.elf | `ab2ec00527acf7989c12720807b0ae82628891c1a26d547270a50f61498b7ebc` |
| merged/unwind-abort/cg-O3/native.elf | `419b6c0ca455da2670714761a7faee0b7179687498e162fc0ea1c98fb96a23d4` |
| merged/unwind-abort/llvm-O0/native.elf | `752ed27bf8a2e88cf80de1abd1868f5f61ee73e48ac4d205896ff3eca10858a0` |
| merged/unwind-abort/llvm-O1/native.elf | `21c03522853a29d3c890f072a4b7c0f170cbb8fbd52b065162f8e556b3bf7366` |
| merged/unwind-abort/llvm-O2/native.elf | `21c03522853a29d3c890f072a4b7c0f170cbb8fbd52b065162f8e556b3bf7366` |
| merged/unwind-abort/llvm-O3/native.elf | `21c03522853a29d3c890f072a4b7c0f170cbb8fbd52b065162f8e556b3bf7366` |
| merged/unwind-unwind/cg-O0/native.elf | `e660ca33bb2b68b4ec732a05a73a75645b1c8e87b450f07327beb0634827564b` |
| merged/unwind-unwind/cg-O1/native.elf | `efc255041ed8228adb2f657e87d1a4be204b0ecafc85c5bd234bcbf925810b52` |
| merged/unwind-unwind/cg-O2/native.elf | `952762bbde5bc070f75152cb650a39d2341e987735bc60bc40a4bfa5831664e1` |
| merged/unwind-unwind/cg-O3/native.elf | `4909b7aa8eece7f0922309d1e5a3a558451e415ece277ea40b8e19e360b1eb45` |
| merged/unwind-unwind/llvm-O0/native.elf | `3e5531321bc4594e27c7e7a05855cd34d393993ef689ef642f4a659046166417` |
| merged/unwind-unwind/llvm-O1/native.elf | `0a3022b5afdf499838eaa67b242365dece8ce9d4f19e82c2f266811e840b2b38` |
| merged/unwind-unwind/llvm-O2/native.elf | `0a3022b5afdf499838eaa67b242365dece8ce9d4f19e82c2f266811e840b2b38` |
| merged/unwind-unwind/llvm-O3/native.elf | `0a3022b5afdf499838eaa67b242365dece8ce9d4f19e82c2f266811e840b2b38` |
| mutation/abort/cg-O0/native.elf | `5fe0a054bbab0d1ac547d631f19ee116c886a73786e0b473ba95e36ef972d931` |
| mutation/abort/cg-O1/native.elf | `d22e369ca46fe0e2e2a0d844d3a1d9f5f1e77947c55cbe5784da11767b514ba9` |
| mutation/abort/cg-O2/native.elf | `95ab4f446b2980a3591b17b014f33e28f7d687e58f8a4c336b0b983c62cf94e5` |
| mutation/abort/cg-O3/native.elf | `0ca032c2d05dd912f6f64db23dcec3db933b4940dfc35bddc888076c30c291a4` |
| mutation/abort/llvm-O0/native.elf | `655171f82828238fdd6c358aa2c64749b5d6ac04138e859b2d55f3418a5d9bf4` |
| mutation/abort/llvm-O1/native.elf | `539b499c3b212223add15036f0ce5032fc9b2f83222e581864396f3bfcb400a0` |
| mutation/abort/llvm-O2/native.elf | `539b499c3b212223add15036f0ce5032fc9b2f83222e581864396f3bfcb400a0` |
| mutation/abort/llvm-O3/native.elf | `539b499c3b212223add15036f0ce5032fc9b2f83222e581864396f3bfcb400a0` |
| mutation/unwind/cg-O0/native.elf | `808b464aa9181a4b0179dd55e74e065d9fde21db199f2cc62baa8a3dc32e00b7` |
| mutation/unwind/cg-O1/native.elf | `f955dcc26b0e863c0d6fa9df2aa3d25ed51cf07e2aa142e9fdfd9af1190b6cc5` |
| mutation/unwind/cg-O2/native.elf | `651293205a2246a9099acaea4b6476b06bccaca808c80b46f4751308941db893` |
| mutation/unwind/cg-O3/native.elf | `454087b7fa14d6aa8486970c1ec8e01ecb844fd8bd875f12ab78e43b235e805f` |
| mutation/unwind/llvm-O0/native.elf | `4b22295ec16bfef079b5c447e12b912ffc36e816274c94d2b16c63a7879ac5e0` |
| mutation/unwind/llvm-O1/native.elf | `5feaf166a0b60c0192082585511e7e9c80e8b2b60b8b4c95d05676e2b817cde0` |
| mutation/unwind/llvm-O2/native.elf | `5feaf166a0b60c0192082585511e7e9c80e8b2b60b8b4c95d05676e2b817cde0` |
| mutation/unwind/llvm-O3/native.elf | `5feaf166a0b60c0192082585511e7e9c80e8b2b60b8b4c95d05676e2b817cde0` |
| indexing/abort/cg-O0/native.elf | `1bb5d26412c84d5341b67ab0f55f901d2cf0a157c2ef99246c995a25c72c0d2d` |
| indexing/abort/cg-O1/native.elf | `5352868f0e7b07755ba74a6104a89b9116102009e4be23f2ba0e7a9b5f3029f4` |
| indexing/abort/cg-O2/native.elf | `8f8cef104c94481c3e6fe51cd44a9848ed88aa86dc96b5fee8e059b502921f42` |
| indexing/abort/cg-O3/native.elf | `7df45c19beb886f6113d5f0611f58e3135d67f35eb7314b3fa4dfc5f3d40548d` |
| indexing/abort/llvm-O0/native.elf | `b0fa8d8e826d8738f30cad84bcb8f0cf199a36962e6ad35362ed238bd2cf7fb5` |
| indexing/abort/llvm-O1/native.elf | `49913675d33527c60f52defa7963007a2dceff3dc9c24975e5c185dd7f2a708a` |
| indexing/abort/llvm-O2/native.elf | `06ee329c53ce5a2616591485e57cd25ba56221beb5318d10264e1e2db3e2a491` |
| indexing/abort/llvm-O3/native.elf | `06ee329c53ce5a2616591485e57cd25ba56221beb5318d10264e1e2db3e2a491` |
| indexing/unwind/cg-O0/native.elf | `358daaca7884b4d7275ae8c7ff34366c6acf83bcce5b64aa8126e7683addeadd` |
| indexing/unwind/cg-O1/native.elf | `8d6b6c7e74bbf37e9a5c342b87c63e42f8015ca408d2a22a1b4a627329467924` |
| indexing/unwind/cg-O2/native.elf | `08af38d2ce7a64f6ffb5772758250a877169f27e3615c2410a86367c62eae228` |
| indexing/unwind/cg-O3/native.elf | `6a78848dbaa2bde7b2d45ad8561977ee854abcf79b65f4b42de0dc9cbae425d4` |
| indexing/unwind/llvm-O0/native.elf | `80562db160867c8b96de9f25b99cb0546ca3eea0afc359b6ba615e39beaa7c90` |
| indexing/unwind/llvm-O1/native.elf | `68ec6c7595f1d6d6e4353617f5b5136420ef3cab8653e6051cceb11fc8862a67` |
| indexing/unwind/llvm-O2/native.elf | `796fd836f234e6ef0e54bbcb426b8ba45dcbd3a1da4e655e151b2c80e32bb582` |
| indexing/unwind/llvm-O3/native.elf | `796fd836f234e6ef0e54bbcb426b8ba45dcbd3a1da4e655e151b2c80e32bb582` |
| merged2/scalar-abort/cg-O0/native.elf | `e7ffc829b69c1f00e9970e35111a0a199714a01e1f5f30549d4d8e34e8eeb555` |
| merged2/scalar-abort/cg-O1/native.elf | `16dc621363366f90070736e10d57a2db90d5809ee414055bbe7f8aa3e20441d6` |
| merged2/scalar-abort/cg-O2/native.elf | `94173381e8594b6491a210d25b066b9873e73d4e7a7a208389cd5e574411e7a5` |
| merged2/scalar-abort/cg-O3/native.elf | `44bbdf3ff85eb300935a3510d9efd70a517f4794f7100a2386874f53d7493d2b` |
| merged2/scalar-abort/llvm-O0/native.elf | `71f14fce9ef7b0e302aa01b8f4296005d3f185699ffbd003af8edc77dd95d81d` |
| merged2/scalar-abort/llvm-O1/native.elf | `dea141fb3a07b6f6958298c1ec71c089ed94335623f9e370c9643450983ec785` |
| merged2/scalar-abort/llvm-O2/native.elf | `cae0780c6519e33057582e9eae0960d09c1a2ac474c22317ed4ef816d9496256` |
| merged2/scalar-abort/llvm-O3/native.elf | `bd1f12bf4832f4e7169fb9b79adbf10366bdf23b8db2924912b59309b023f51e` |
| merged2/scalar-unwind/cg-O0/native.elf | `5daeae1a897c94cebfbf3d1aa2080f4b3bad7527f53a75666d0ba90fd1f69317` |
| merged2/scalar-unwind/cg-O1/native.elf | `ffe658d3e668e9a0b6f625666bd2292c0e652ce7012fb0f6a385f6eeeb39e14c` |
| merged2/scalar-unwind/cg-O2/native.elf | `03687596aa19d577cf1ae84f6da441f2edaef930d40a2de4df59a3d4f3ff4600` |
| merged2/scalar-unwind/cg-O3/native.elf | `94af088efefc51dc7fd8718425cf5708e1371f5e2e8d1264f1fc752028ed1627` |
| merged2/scalar-unwind/llvm-O0/native.elf | `0969c2b89c1dbf9be060a399fbd4f8d63b6e78470093b4832d5e399b00329693` |
| merged2/scalar-unwind/llvm-O1/native.elf | `3389ba11e22585dbdf8c76f0a31326add899625d3cd76e67ff2bc56b608c46dd` |
| merged2/scalar-unwind/llvm-O2/native.elf | `bafcbc625caedb64fa62c3b80f08d252d2655a35ffba97b433cf82e0aeeb1387` |
| merged2/scalar-unwind/llvm-O3/native.elf | `b102080a1b4db4218dfc90061adc2db6bed75868a33b89069510e98d830523b0` |
| merged2/unwind-abort/cg-O0/native.elf | `c6800119fb80cbde8ea0cf2b037192c832317ce9c80f4f93dc1d9349f9610037` |
| merged2/unwind-abort/cg-O1/native.elf | `e02954d31ac9192eea740c20c154f11c42a82f219cf84fa652c626f50ca2c837` |
| merged2/unwind-abort/cg-O2/native.elf | `e62de589036bec900baecd45ac055e6cb9cb87d42d03ead0019db6f73680b5f5` |
| merged2/unwind-abort/cg-O3/native.elf | `6e27ca3dcbd8f53a94052e1c5c5210c968656f7f2a3a12c6186410a023dac2a9` |
| merged2/unwind-abort/llvm-O0/native.elf | `7d47247ea9d181899792b80ace7de8e7320481551fe683c70b0dcf0a64327760` |
| merged2/unwind-abort/llvm-O1/native.elf | `aa59385f35a4c9a8ddbd4c589f829d0a75bd57ba025e46dc02957fa9a70287f8` |
| merged2/unwind-abort/llvm-O2/native.elf | `aa59385f35a4c9a8ddbd4c589f829d0a75bd57ba025e46dc02957fa9a70287f8` |
| merged2/unwind-abort/llvm-O3/native.elf | `aa59385f35a4c9a8ddbd4c589f829d0a75bd57ba025e46dc02957fa9a70287f8` |
| merged2/unwind-unwind/cg-O0/native.elf | `78dfc2f6a68ae12f9283ceb5932eb65c8d4a474c318040fc84b156675fb03c76` |
| merged2/unwind-unwind/cg-O1/native.elf | `4e2bb462995799c84652d782970693ee50e4a1600d0b5dabc622d3de97c675e4` |
| merged2/unwind-unwind/cg-O2/native.elf | `6309ef929d679407ddd5aa4dffee6f6ec95c70f8958bc17db6df31d94f496907` |
| merged2/unwind-unwind/cg-O3/native.elf | `b7047be4ba3ad3ffa417dad230fd1efe6219e6b854f7ebd16d7a9ce0b053c259` |
| merged2/unwind-unwind/llvm-O0/native.elf | `5a2ca0723a59e01ed10a297c7aa5a1db64992df8f2cdaa371879078f6b4e9fdd` |
| merged2/unwind-unwind/llvm-O1/native.elf | `29452c326bfd69d323d055665c9f9f9bcde0719bd2d8f38a88ea2cbaf7a09fb2` |
| merged2/unwind-unwind/llvm-O2/native.elf | `29452c326bfd69d323d055665c9f9f9bcde0719bd2d8f38a88ea2cbaf7a09fb2` |
| merged2/unwind-unwind/llvm-O3/native.elf | `29452c326bfd69d323d055665c9f9f9bcde0719bd2d8f38a88ea2cbaf7a09fb2` |
| merged2/abort/cg-O0/native.elf | `55f2d44be0fd4e4cf2f68ab27bf945dd57b6a62e0dccade9e5f443cb26eead5a` |
| merged2/abort/cg-O1/native.elf | `70cc446c2278c88c41ecfe31330450d51d4b09bcec49559dd0035430d52191fc` |
| merged2/abort/cg-O2/native.elf | `6a8b4edceca1c3a6b714a27f36ffe3a11c35f0b791e28a4310766118f835cdfa` |
| merged2/abort/cg-O3/native.elf | `bd4ce9146a136cc13f6ed3925a9ab8fe92a08b846e04df22f0d7b5cc3ed343bc` |
| merged2/abort/llvm-O0/native.elf | `722bff79ca6c97c4fe630a5bcbc18bb5c6bca0ec346a271c5ee98547fbe6aa7e` |
| merged2/abort/llvm-O1/native.elf | `eefecb5f6c6a4f1d2645a788df01f7e2752cf1fa34ef1698d617fb60a5ac475c` |
| merged2/abort/llvm-O2/native.elf | `eefecb5f6c6a4f1d2645a788df01f7e2752cf1fa34ef1698d617fb60a5ac475c` |
| merged2/abort/llvm-O3/native.elf | `eefecb5f6c6a4f1d2645a788df01f7e2752cf1fa34ef1698d617fb60a5ac475c` |
| merged2/unwind/cg-O0/native.elf | `bcd51d7aa97d884aa227d6b8d491385d6b49b4cbc8ef435120cead1f2c91cce6` |
| merged2/unwind/cg-O1/native.elf | `0b7f92bbf2820e192de06184a464b78da13c1fa97eb03bfa409d26e4e36afedf` |
| merged2/unwind/cg-O2/native.elf | `8d8882c9015fe161caf4c182a36cdf18cd741220b5ce990fd3b940e525ae9b43` |
| merged2/unwind/cg-O3/native.elf | `db54f03f86ed6ca1a9126381bd00bae198f46cfc209fc20e43445659e3d2ae6d` |
| merged2/unwind/llvm-O0/native.elf | `94dff6e571c34284000754613e30f1882d478f307eeccfb65da43e249adc63e0` |
| merged2/unwind/llvm-O1/native.elf | `7fc02bd1f6b0cbcb173a4dd39cba55d61da6b7034265812b70b9e3f56a7a242c` |
| merged2/unwind/llvm-O2/native.elf | `7fc02bd1f6b0cbcb173a4dd39cba55d61da6b7034265812b70b9e3f56a7a242c` |
| merged2/unwind/llvm-O3/native.elf | `7fc02bd1f6b0cbcb173a4dd39cba55d61da6b7034265812b70b9e3f56a7a242c` |

### Exact census invocation

The other two invocations substitute only backend and output directory.

```sh
/home/ayates/trust-cg-soundness-20260914/trust-authored-qualified-20260924/trust-ae9c2c1d/bin/trustc --crate-name std --edition=2024 std/src/lib.rs --error-format=json --json=diagnostic-rendered-ansi,artifacts,future-incompat --crate-type dylib --crate-type rlib --emit=dep-info,link -C embed-bitcode=no -C codegen-units=1 --warn=unexpected_cfgs --check-cfg 'cfg(feature, values(any()))' --check-cfg 'cfg(target_has_reliable_f16)' --check-cfg 'cfg(target_has_reliable_f16_math)' --check-cfg 'cfg(target_has_reliable_f128)' --check-cfg 'cfg(target_has_reliable_f128_math)' --cfg 'feature="addr2line"' --cfg 'feature="backtrace"' --cfg 'feature="miniz_oxide"' --cfg 'feature="object"' --cfg 'feature="panic-unwind"' --check-cfg 'cfg(docsrs,test)' --check-cfg 'cfg(feature, values("addr2line", "backtrace", "backtrace-trace-only", "compiler-builtins-c", "compiler-builtins-mem", "debug_refcell", "llvm-libunwind", "llvm_enzyme", "miniz_oxide", "object", "optimize_for_size", "panic-unwind", "system-llvm-libunwind", "windows_raw_dylib"))' -C metadata=2151fd1de3847f13 --out-dir $HOME/trust-cg/target/variadic-call-investigation/std-O2-baseline --target aarch64-unknown-linux-gnu -C strip=debuginfo -L dependency=$HOME/trust-cg/target/std-build-investigation/llvm-resolve/target/aarch64-unknown-linux-gnu/debug/deps -L dependency=$HOME/trust-cg/target/std-build-investigation/llvm-resolve/target/debug/deps --extern priv:addr2line=$HOME/trust-cg/target/std-build-investigation/llvm-resolve/target/aarch64-unknown-linux-gnu/debug/deps/libaddr2line-12c7738545273db2.rlib --extern alloc=$HOME/trust-cg/target/std-build-investigation/llvm-resolve/target/aarch64-unknown-linux-gnu/debug/deps/liballoc-74b6f64c7e901880.rlib --extern priv:cfg_if=$HOME/trust-cg/target/std-build-investigation/llvm-resolve/target/aarch64-unknown-linux-gnu/debug/deps/libcfg_if-5b0a02a5eaac4739.rlib --extern core=$HOME/trust-cg/target/std-build-investigation/llvm-resolve/target/aarch64-unknown-linux-gnu/debug/deps/libcore-eaac2a498319830d.rlib --extern priv:hashbrown=$HOME/trust-cg/target/std-build-investigation/llvm-resolve/target/aarch64-unknown-linux-gnu/debug/deps/libhashbrown-ebb0e293be97ce62.rlib --extern libc=$HOME/trust-cg/target/std-build-investigation/llvm-resolve/target/aarch64-unknown-linux-gnu/debug/deps/liblibc-1db47c455d786c7a.rlib --extern priv:miniz_oxide=$HOME/trust-cg/target/std-build-investigation/llvm-resolve/target/aarch64-unknown-linux-gnu/debug/deps/libminiz_oxide-7392aa5c5bcbb032.rlib --extern priv:object=$HOME/trust-cg/target/std-build-investigation/llvm-resolve/target/aarch64-unknown-linux-gnu/debug/deps/libobject-a6517f9eb710ccae.rlib --extern priv:panic_abort=$HOME/trust-cg/target/std-build-investigation/llvm-resolve/target/aarch64-unknown-linux-gnu/debug/deps/libpanic_abort-79c82d310bffce8a.rlib --extern priv:panic_unwind=$HOME/trust-cg/target/std-build-investigation/llvm-resolve/target/aarch64-unknown-linux-gnu/debug/deps/libpanic_unwind-780ac334bb08e854.rlib --extern priv:rustc_demangle=$HOME/trust-cg/target/std-build-investigation/llvm-resolve/target/aarch64-unknown-linux-gnu/debug/deps/librustc_demangle-d615677db4ffd5d8.rlib --extern std_detect=$HOME/trust-cg/target/std-build-investigation/llvm-resolve/target/aarch64-unknown-linux-gnu/debug/deps/libstd_detect-b1e1c14d8899ece2.rlib --extern priv:unwind=$HOME/trust-cg/target/std-build-investigation/llvm-resolve/target/aarch64-unknown-linux-gnu/debug/deps/libunwind-a3d565b6442598f4.rlib -Z unstable-options -Ztrust-verify=off -Zforce-unstable-if-unmarked -Ccodegen-units=1 --verbose --cfg backtrace_in_libstd --check-cfg 'cfg(netbsd10)' --check-cfg 'cfg(no_global_oom_handling)' --check-cfg 'cfg(restricted_std)' --check-cfg 'cfg(backtrace_in_libstd)' --check-cfg 'cfg(vxworks_lt_25_09)' -Copt-level=2 -Zcodegen-backend=$HOME/trust-cg/target/slice-from-end-investigation/merged-4-backend.so '-Ztrust-ir-cg-args=diag-json no-proof-certs time-codegen=20 time-lower'
```

### Removed std roots

- `_RNCNvMNtNtNtNtCsiYI7VriWazq_3std3sys2fs4unix3dirNtB4_3Dir11open_file_c0Bc_ (reachable Rust-internal monomorphization, not a std-internal shim)`
- `_RNCNvMNtNtNtNtCsiYI7VriWazq_3std3sys2fs4unix3dirNtB4_3Dir11open_with_c0Bc_ (reachable Rust-internal monomorphization, not a std-internal shim)`
- `_RNCNvMsi_NtNtNtCsiYI7VriWazq_3std3sys2fs4unixNtB7_4File6open_c0Bd_ (reachable Rust-internal monomorphization, not a std-internal shim)`
- `_RNCNvNvNtNtNtCsiYI7VriWazq_3std3sys3pal4unix4init21sanitize_standard_fds0Bb_ (reachable Rust-internal monomorphization, not a std-internal shim)`
- `_RNvMNtNtNtCsiYI7VriWazq_3std3sys2fd4unixNtB2_8FileDesc11set_cloexec (reachable Rust-internal monomorphization, not a std-internal shim)`
- `_RNvMNtNtNtNtCsiYI7VriWazq_3std3sys7process4unix4unixNtNtB4_6common7Command10send_pidfd (reachable Rust-internal monomorphization, not a std-internal shim)`
- `_RNvMNtNtNtNtCsiYI7VriWazq_3std3sys7process4unix5pidfdNtB2_5PidFd11send_signal (reachable Rust-internal monomorphization, not a std-internal shim)`
- `_RNvMNtNtNtNtCsiYI7VriWazq_3std3sys7process4unix5pidfdNtB2_5PidFd15current_process (reachable Rust-internal monomorphization, not a std-internal shim)`
- `_RNvMNtNtNtNtCsiYI7VriWazq_3std3sys7process4unix5pidfdNtB2_5PidFd25send_process_group_signal (reachable Rust-internal monomorphization, not a std-internal shim)`
- `_RNvMs0_NtNtNtCsiYI7VriWazq_3std2os2fd5ownedNtB5_10BorrowedFd18try_clone_to_owned (reachable Rust-internal monomorphization, not a std-internal shim)`
- `_RNvNtNtNtNtCsiYI7VriWazq_3std3sys3pal4unix5futex10futex_wait (reachable Rust-internal monomorphization, not a std-internal shim)`
- `_RNvNtNtNtNtCsiYI7VriWazq_3std3sys3pal4unix5futex10futex_wake (reachable Rust-internal monomorphization, not a std-internal shim)`
- `_RNvNtNtNtNtCsiYI7VriWazq_3std3sys3pal4unix5futex14futex_wake_all (reachable Rust-internal monomorphization, not a std-internal shim)`
- `_RNvNvNtNtNtCsiYI7VriWazq_3std3sys2fs4unix9try_statx5statx (reachable Rust-internal monomorphization, not a std-internal shim)`
- `_RNvNvNtNtNtCsiYI7VriWazq_3std3sys6random5linux9getrandom9getrandom (reachable Rust-internal monomorphization, not a std-internal shim)`
- `_RNvNvNtNtNtNtCsiYI7VriWazq_3std3sys2io11kernel_copy5linux18copy_regular_files15copy_file_range (reachable Rust-internal monomorphization, not a std-internal shim)`
