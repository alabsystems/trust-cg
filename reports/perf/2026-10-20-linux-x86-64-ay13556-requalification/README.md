# `x86_64-unknown-linux-gnu` re-qualified on AY build 13556

2026-10-20. Author: Andrew Yates. Host: `x86_64-unknown-linux-gnu`, 18 CPUs.

## Why this run exists

`QUALIFIED_AY` moved to AY 0.27.0 build 13556 (`ebde49de3`) on 2026-10-19
(OD-190). `QUALIFIED_AY` is one AY for every host, and the per-host outcome
tables are evidence about a PAIR, so the pair check refused this host until it
re-measured its own outcomes with that build. LIMITATIONS.md said so in those
words. This is that re-measurement for the Linux x86-64 host.

## The pair

```
ay       0.27.0 build 13556 commit ebde49de3c2c3b03f3b1a4e5dc60a5b37aa870a0
         sha256 393e1bc94cde02ca2223c565305d3a07f4e1c22d239ad442b932723f2d11d136
         route=toolchain-pinned-ay, the build compiler's sysroot bin/ay
         ($HOME/trust/build/x86_64-unknown-linux-gnu/stage2)
clean    $HOME/trust/first-party/clean/target/release/clean
         sha256 9547de6425a0a520fa40493a03e7307c5ef15f5616b397fdd7392e9f361d6cb8
```

Both match the host's rows of `QUALIFIED_AY` and
`QUALIFIED_CLEAN_SHA256_BY_HOST`, so `assert_qualification_replayer` admits the
pair. The AY is an unverified local build of its own checkout at that commit
(`git rev-list --count HEAD` = 13556, which is the banner's `build.increment`);
it is not a release input. The previous build, 12713, is kept beside it as
`bin/ay.build12713.bak`.

## What moved, and it is all one direction

`-p trust-cg-verify --lib x86_source_bound_body` read **366 passed, 4 failed**
(1381.8 s). All four were this host's own gap lanes, each failing because an
obligation the host had RECORDED as a gap now certifies — a strengthening the
lanes refuse to pass silently:

```
slice-10: left: []                              right: [("MulU64", "Timeout")]
slice-14: left: [("UdivConst","Timeout"),        right: [... , ("GuardedUdiv","Timeout"),
                 ("UremConst32","Timeout")]              ("GuardThenCall","Timeout")]
```

Build 13556 is the whole difference. No source, no fixture and no deadline
moved with it.

### Slice 10 `MulU64` — now this host's `CERTIFIED_HERE_BY_HOST` entry

| run | 1-minute load | result |
| ---: | ---: | --- |
| 1 | 0.47 | `Verified` 13 549 ms |
| 2 | 0.62 | `Verified` 13 594 ms |
| 3 | 0.88 | `Verified` 13 524 ms |

13.52-13.59 s against the lane's 30 s deadline. Under build 12713 this host
timed out on it. `aarch64-apple-darwin` already certified it (16.95 s,
2026-10-19); the Darwin x86-64 reference pair still times out, so it stays a
gap of the table and this host now has its own entry.

### Slice 14 `GuardedUdiv` and `GuardThenCall` — removed from `ALSO_UNCERTIFIED_HERE_BY_HOST`

| run | load | `GuardedUdiv` | `GuardThenCall` | `UdivConst` | `UremConst32` |
| ---: | ---: | --- | --- | --- | --- |
| 1 | 0.64 | `Verified` 174 ms | `Verified` 109 ms | `Timeout` 30 009 ms | `Timeout` 30 010 ms |
| 2 | 0.98 | `Verified` 166 ms | `Verified` 109 ms | `Timeout` 30 009 ms | `Timeout` 30 009 ms |
| 3 | 1.86 | `Verified` 170 ms | `Verified` 109 ms | `Timeout` 30 010 ms | `Timeout` 30 009 ms |

Under 12713 both needed a 300 s budget on this host (2026-10-15, 916 s for the
slice). Under 13556 they take 0.1-0.2 s. **Neither becomes deadline-bound**:
0.1-0.2 s against 30 s is not near the deadline, unlike the Darwin AArch64
host's rows, which sit at 2-164 s and therefore carry
`DEADLINE_BOUND_HERE_BY_HOST` entries. `ALSO_UNCERTIFIED_HERE_BY_HOST` is now
empty.

Slice 14's own recorded gaps `UdivConst` and `UremConst32` are unchanged: they
time out at 30.01 s on every run, at every load measured.

## What this does NOT establish

* Nothing here is an x86-64 NATIVE result. These lanes replay the x86-64 body
  theorems' queries with AY and Clean; the strength is solver-backed and
  independently replayed, not exhaustive and not native execution.
* The outcomes are evidence about THIS PAIR on THIS HOST. They say nothing
  about `aarch64-apple-darwin`, whose entries remain build 12713's and whose
  pair check still refuses it until it re-measures.
* No proof grade, soundness record or release authority changes. The tables
  moved in the strengthening direction only; the `recorded_gaps` baseline is
  untouched.
* A heavier load can still push a near-deadline obligation past 30 s. That
  risk is why the record refuses an unmeasured answer, and it is why the three
  runs above print their load.

## Reproduce

```sh
# the pair, and every x86-64 body lane
PATH=/usr/bin:/bin:$PATH CC=/usr/bin/gcc RUST_MIN_STACK=134217728 \
  scripts/trust_cargo.sh test -p trust-cg-verify --lib x86_source_bound_body

# the two gap lanes alone, with their per-obligation timings
scripts/trust_cargo.sh test -p trust-cg-verify --lib slice10_qualification -- --nocapture
scripts/trust_cargo.sh test -p trust-cg-verify --lib slice14_qualification -- --nocapture
```

`commands/requalify.sh` runs all three and prints the load before each.
