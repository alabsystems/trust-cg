#!/bin/sh
# The host qualification of the x86-64 body lane, every lane its record
# depends on, as one command:
#   qualify.sh <overlay> <dump dir>
# It tests the trust-cg checkout this script is in. CARGO_TARGET_DIR is the
# caller's (keep one per worktree), else that checkout's target/.
#
# 1. `--lib _qualification`, one process, --test-threads=1: every lane that
#    reads the host's qualification record, the credit lanes included. The
#    record's witness (`assert_qualification_replayer`) refuses a lane this
#    filter does not select, so such a lane fails wherever it runs.
# 2. The explicit lane, by exact name: it is `#[ignore]`d (minutes per label)
#    and replays each deadline-bound label with the record's 300 s budget.
# Both run; the exit status is nonzero when either fails, or when either ran
# another number of lanes than the record names (LANES, then 1): libtest
# passes a filter or an exact name that selects nothing. A lane that finds
# no AY, or no checker this build accepts, fails, naming what is missing.
#
# The overlay's bin/clean is the only checker its build accepts; the run
# names it explicitly too. No TCG_X86_BODY_QUALIFY_AY: the overlay build
# records its AY, so the override is not consulted.
#
# Until 2026-10-17 this script ran step 1 alone, from the round's own
# worktree, with a filter that did not select slice 1's and slice 4's credit
# lanes (the record's "Every lane fails closed").
OV=${1:?overlay}
DUMP=${2:?dump dir}
TREE=$(cd "$(dirname "$0")" && git rev-parse --show-toplevel) || exit 2
cd "$TREE" || exit 2
: "${CARGO_TARGET_DIR:=$TREE/target}"
export CARGO_TARGET_DIR
EXPLICIT=x86_source_bound_body::tests::host_qualification_replays_each_deadline_bound_label_with_the_recorded_budget
# The lanes `--lib _qualification` runs (the record's "Fail closed"): a lane
# added to or dropped from the record changes this with the record.
LANES=36

# counted <name> <expected passes> <command...>: runs the command with its
# output passed through, and exits nonzero unless it exits 0 and its one
# libtest summary reads exactly <expected passes> passed.
counted() {
  name=$1 expected=$2
  shift 2
  { "$@" 2>&1; echo "qualify.sh: $name exit $?"; } | awk -v name="$name" -v expected="$expected" '
    { print; fflush() }
    /^test result: / { summaries++; for (i = 1; i < NF; i++) if ($(i + 1) ~ /^passed;?$/) passed = $i }
    $0 == "qualify.sh: " name " exit 0" { ok = 1 }
    END {
      if (!ok) exit 1
      if (summaries != 1 || passed != expected) {
        printf "qualify.sh: %s ran %s lanes (%d summaries), the record names %s\n", name, passed + 0, summaries, expected
        exit 1
      }
    }'
}

env TRUST_TARGO="$OV/bin/targo" \
  build-slot -- scripts/trust_cargo.sh test --locked -p trust-cg-verify --lib --no-run || exit 2
counted lanes "$LANES" env TRUST_TARGO="$OV/bin/targo" \
  TCG_EXTERNAL_CLEAN_CHECKER="$OV/bin/clean" TCG_X86_BODY_QUALIFY_DUMP="$DUMP" \
  build-slot -- scripts/trust_cargo.sh test --locked -p trust-cg-verify --lib _qualification \
  -- --nocapture --test-threads=1
lanes=$?
counted explicit 1 env TRUST_TARGO="$OV/bin/targo" \
  TCG_EXTERNAL_CLEAN_CHECKER="$OV/bin/clean" \
  build-slot -- scripts/trust_cargo.sh test --locked -p trust-cg-verify --lib "$EXPLICIT" \
  -- --ignored --exact --nocapture
explicit=$?
echo "qualify.sh: --lib _qualification status $lanes; explicit lane status $explicit"
[ "$lanes" -eq 0 ] && [ "$explicit" -eq 0 ]
