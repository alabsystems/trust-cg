#!/bin/zsh
# The move's gates on the x86-stage1-ay13556 overlay (targo --unverified, nice 19, -j2,
# --no-fail-fast), each step's complete output kept in <out dir>:
#   verify.log    the full x86 body suite: trust-cg-verify --lib x86_source_bound_body,
#                 x86_source_bound_envelope and diag:: (every slice's qualification and credit
#                 test included);
#   codegen.log   codegen --test x86_source_bound_body --test must_refuse_corpus;
#   lower.log     trust-cg-lower --lib;
#   fmt.log, docs.log, hosts.log   scripts/check_fmt.sh (pack 6808's targo),
#                 scripts/check_documentation.py --check, scripts/full_test_matrix_hosts.py --check.
# usage: gates.sh <worktree> <out dir>
W="${1:?worktree}"; OUT="${2:?out dir}"
cd "$W" || exit 9
mkdir -p "$OUT"
OVERLAY=$HOME/.local/share/trust-overlays/x86-stage1-ay13556
export TRUST_TARGO=$OVERLAY/bin/targo
export CARGO_TARGET_DIR=$HOME/tcg-scratch/stage1-targets/$(basename "$PWD")
export TCG_X86_BODY_QUALIFY_AY=$OVERLAY/bin/ay
export TCG_EXTERNAL_CLEAN_CHECKER=$OVERLAY/bin/clean
TC=scripts/trust_cargo.sh
prune() { rm -rf "$CARGO_TARGET_DIR/debug/incremental"; }
step() { echo "$1 exit=$2 $(date +%H:%M:%S) load=$(uptime | sed 's/.*averages: //')" >> "$OUT/summary.txt"; }
while [ -e $HOME/tcg-scratch/quiet.request ] || pgrep -f "[t]rust_ir_cg_census" >/dev/null; do sleep 60; done
nice -n 19 bash $TC test -p trust-cg-verify --lib -j2 --no-fail-fast -- x86_source_bound_body \
  x86_source_bound_envelope diag:: > "$OUT/verify.log" 2>&1; step verify $?; prune
nice -n 19 bash $TC test -p trust-cg-codegen --test x86_source_bound_body --test must_refuse_corpus \
  -j2 --no-fail-fast > "$OUT/codegen.log" 2>&1; step codegen $?; prune
nice -n 19 bash $TC test -p trust-cg-lower --lib -j2 --no-fail-fast > "$OUT/lower.log" 2>&1; step lower $?; prune
TRUST_TARGO="$HOME/Library/Application Support/aterm/pkg/store/trust/6808/bin/targo" \
  bash scripts/check_fmt.sh > "$OUT/fmt.log" 2>&1; step fmt $?
python3 scripts/check_documentation.py --check > "$OUT/docs.log" 2>&1; step docs $?
python3 scripts/full_test_matrix_hosts.py --check > "$OUT/hosts.log" 2>&1; step hosts $?
echo "GATES-DONE $(date)" >> "$OUT/summary.txt"
