#!/bin/zsh
# Run the offline census probe (census_probe.rs registered as a test submodule of
# trust-cg-verify, the test binary built with scripts/trust_cargo.sh) over dumped
# core trust-ir modules.
# usage: probe.sh <test-binary> <dump dir> <names-file|all> <out.tsv> [smt2 dir]
BIN="${1:?test binary}"
export TCG_PROBE_DUMP="${2:?dump dir}"
[ "$3" != "all" ] && export TCG_PROBE_NAMES="$3"
export TCG_PROBE_OUT="${4:?out.tsv}"
[ -n "$5" ] && export TCG_PROBE_SMT2="$5"
RUST_MIN_STACK=67108864 nice "$BIN" census_probe_shapes --ignored --nocapture --test-threads=1
