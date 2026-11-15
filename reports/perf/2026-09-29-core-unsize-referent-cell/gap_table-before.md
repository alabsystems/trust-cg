# trust-ir-cg census: `core`
* emitted objects in `obj/`: 1269 (per-function/per-batch objects the backend DID produce; not a success count of mono items)

* compiler: `rustc 1.99.0-dev (3a3e781fe 2026-09-14) (trustc 0.1.0)` at `$HOME/trust/build/x86_64-unknown-linux-gnu/stage2/bin/trustc`
* backend: `/home/ayates/trust-cg-wt-cleanprof/target-bridge/release/librustc_codegen_trust_cg.so`; panic=abort; opt-level=3
* repo rev: `ceb94fe99cbc7db4bbe617b53fd04a61acbd4467`; trust-cg rev: `9da5e2376931cfca79f60e82c0acda9633af01c7`
* exit code: `1`; wall: 89s
* typed refusals (JSON): **0** across **0** functions; distinct codes: 0
* failed roots (externally required, fail-closed): **15**; distinct reasons: 4
* skipped internal functions (dropped as unreachable — for a LIBRARY every one is a missing symbol downstream): **0**; distinct reasons: 0
* trapping stubs emitted for dynamic-dispatch shims (link, but TRAP if reached): **0**; distinct reasons: 0
* harness errors (non-backend `error:` lines): 0

## Failed roots by reason

| rank | reason | count | example symbol |
|---:|---|---:|---|
| 1 | `[TCG-DYN-REF-IDENTITY]` | 10 | `_RINvMs5_NtNtCs5j7F4uy8uKG_4core3fmt8buildersNtB6_9DebugList7entriesNtNvXsd_NtBa` |
| 2 | `Rvalue::Ref aggregate source is unsupported ADT` | 2 | `_RNvMNtCs5j7F4uy8uKG_4core3stre12escape_debug` |
| 3 | `Ty::[u<n>` | 2 | `_RNvXs6_NtNtCs5j7F4uy8uKG_4core3net11socket_addrNtB5_12SocketAddrV4NtNtB9_3fmt7D` |
| 4 | `Rvalue::RawPtr` | 1 | `_RNvXs6_NtNtCs5j7F4uy8uKG_4core3net7ip_addrNtB5_8Ipv4AddrNtNtB9_3fmt7Display3fmt` |

## Skipped internal functions by reason

| rank | reason | count | example symbol |
|---:|---|---:|---|

## Trapping stubs by reason

| rank | reason | count | example symbol |
|---:|---|---:|---|

## Typed diagnostic codes

| rank | code | count | example function | example why |
|---:|---|---:|---|---|
