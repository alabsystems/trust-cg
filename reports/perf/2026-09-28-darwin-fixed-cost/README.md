# Darwin arm64 bridge compile: per-process fixed cost (L14-P5)

> **Payload removed.** This record's logs, captures, JSON files, inventories
> and `records/` are no longer in the tree; Markdown and reproducer sources
> stay. The last commit that contains them is `2e07d67a791aff374037cd25494d46afa668af1d`.
> Recover a file with `git show <sha>:<path>`. References below to removed
> files describe that commit.

Measurement only, on one shared host. It is not a ledger row, not evidence
for a `run.py` gate, and proves nothing about correctness. It records the
before/after effect of the L14-P5 fixed-cost change described in
[CHANGELOG.md](../../../CHANGELOG.md) and [ARCHITECTURE.md](../../../ARCHITECTURE.md).

## Setup

| Item | Value |
| --- | --- |
| host | Apple M4 Max, 16 CPUs, macOS 26.6.2, shared with other agents' builds |
| driver | Trust package 9192 `bin/trustc` (commit `321aaeda75478038420d97830f14724c33c8dc39`), explicit unverified frontend lane `-Ztrust-verify=off` |
| base backend | built from main `e29e8006d`, sha256 `9dedf9eed8634dbffc5177c9e90ac42769f0391d87d6a07bdb654cdb93389af7` |
| head backend | built from the L14-P5 branch at `9b8a3ffea` (before its merge of later main), sha256 `24a643010d11bbb86dba0bde0990cfbcbe9458f47a7ecd3906361ba9f59c2203` |
| backend build | in `crates/rustc-codegen-trust-cg`: `CARGO_TARGET_DIR=target-bridge RUSTC=<trust 9192>/bin/trustc <trust 9192>/bin/targo --unverified build --release --locked` |
| load | 1-minute load 4.6 to 7.0 across the run, recorded before every compile |

Programs: [`programs/trivial.rs`](programs/trivial.rs) (`fn main(){}`, a
binary), `p3_gcd`, `p1_xorshift` and `m1_call_chain` from
[`benchmarks/beat-llvm/progs`](../../../benchmarks/beat-llvm/progs), all with the
`no-proof-certs` knob, and [`programs/id32.rs`](programs/id32.rs), a
one-function `no_std` library compiled with certificates on.

Command (run from the repository root):

```sh
R=reports/perf/2026-09-28-darwin-fixed-cost P=benchmarks/beat-llvm/progs
python3 $R/measure.py --driver "<trust 9192>/bin/trustc" \
  --backend base=<base dylib> --backend head=<head dylib> \
  --program $R/programs/trivial.rs:bin:no-proof-certs \
  --program $P/p3_gcd.rs:bin:no-proof-certs \
  --program $P/p1_xorshift.rs:bin:no-proof-certs \
  --program $P/m1_call_chain.rs:bin:no-proof-certs \
  --program $R/programs/id32.rs:lib: \
  --n 5 --work <new private directory> --out results.json
```

[`measure.py`](measure.py) runs every compile under `/usr/bin/time -l`,
alternates the backend order each iteration, gives every cold compile a fresh
0700 `XDG_CACHE_HOME`, and pre-warms one private root per backend for the warm
lane. `results.json` holds every raw sample (home and scratch
paths replaced by placeholders) and the medians below.

## Results (medians of 5)

Instructions retired and peak memory footprint are the decision metrics.

| Program | Lane | Base instr. | Head instr. | Base wall | Head wall | Base footprint | Head footprint | LLVM instr. / wall |
| --- | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| `trivial` | warm | 4,819 M | 4,616 M | 0.36 s | 0.30 s | 61.0 MB | 60.9 MB | 3,944 M / 0.30 s |
| `trivial` | cold | 5,082 M | 4,846 M | 1.05 s | 1.02 s | 136.8 MB | 61.1 MB | |
| `p3_gcd` | warm | 5,011 M | 4,810 M | 0.41 s | 0.37 s | 65.6 MB | 65.5 MB | 4,015 M / 0.29 s |
| `p3_gcd` | cold | 5,309 M | 5,072 M | 1.26 s | 1.17 s | 138.6 MB | 65.7 MB | |
| `p1_xorshift` | warm | 4,983 M | 4,782 M | 0.43 s | 0.35 s | 65.6 MB | 65.6 MB | 4,031 M / 0.30 s |
| `p1_xorshift` | cold | 5,277 M | 5,043 M | 1.25 s | 1.19 s | 138.5 MB | 65.8 MB | |
| `m1_call_chain` | warm | 5,021 M | 4,820 M | 0.41 s | 0.38 s | 66.0 MB | 65.9 MB | 4,016 M / 0.31 s |
| `m1_call_chain` | cold | 5,323 M | 5,088 M | 1.29 s | 1.18 s | 138.6 MB | 65.8 MB | |
| `id32` (certificates on) | warm | 4,731 M | 4,527 M | 0.34 s | 0.28 s | 67.4 MB | 66.4 MB | 3,867 M / 0.27 s |
| `id32` (certificates on) | cold | 4,986 M | 4,750 M | 0.34 s | 0.28 s | 135.1 MB | 68.8 MB | |

The LLVM lane is the same driver without `-Zcodegen-backend`; it has no proof
cache, so it has one lane.

## Cold wall time depends on the host's scan queue

A cold compile writes a new AY private copy, and on macOS the first start of
that new executable waits for Gatekeeper's XProtect scan. `syspolicyd` runs
those scans one at a time for every process on the host. In this run's 95 s
window (`/usr/bin/log show --start "2026-09-28 17:08:15" --end
"2026-09-28 17:09:51" --predicate 'process == "syspolicyd"'`) it completed 153
scans (`GK evaluateScanResult`), 51 of them for this run's AY copies (signing
identifier `ay-55554944…`) and the rest for other processes' new executables.

The head backend starts a copy it has just published once, on its background
warm thread, so the scan overlaps the front end. A reviewer's syspolicyd trace
showed the scan starting 0.35-0.56 s into a head compile against 0.70-0.73 s
for base when the queue was idle. When other scans were queued, both started
after about 1.26-1.32 s. The same reviewer's interleaved run at load 6.8 to 8.5
measured cold `trivial` medians of 1.25 s (base) and 1.31 s (head), with both
lanes bimodal. The cold wall column above is therefore a property of this run's
queue, not of the backend. No cold wall gain is claimed; instructions retired
and peak footprint reproduced within 0.5% in that independent run.
