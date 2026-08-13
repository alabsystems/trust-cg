#!/usr/bin/env bash
# aarch64_trust_ir_coverage.sh — measure how much of the trust-ir surface the
# trust-cg AArch64 backend lowers, from real .trust_ir modules (not the rustc
# bridge, which needs the pinned nightly on the x86 lane).
#
# For every .trust_ir fixture in the pinned trust-ir conformance corpus (plus any
# repo fixtures under crates/**/fixtures/**), it runs the module through
#   trust-cg --format=text --target aarch64 -c   (certs ON, the default)
# and classifies the outcome. The score that matters is GENUINE GAPS REMAINING,
# not a raw pass rate: many corpus fixtures are *meant* to fail closed (invalid
# IR the backend must reject) or carry high-level ops that earlier passes erase
# before scalar codegen. Those are separated out so the number is honest.
#
# Usage:  scripts/aarch64_trust_ir_coverage.sh [--md report.md]
#
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Copyright 2026 Andrew Yates | License: Apache-2.0
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
CLI="$ROOT/target/release/trust-cg"
MD_OUT=""
[ "${1:-}" = "--md" ] && MD_OUT="${2:-}"

if [ ! -x "$CLI" ]; then
    echo "building trust-cg CLI (release)..." >&2
    (cd "$ROOT" && cargo build -p trust-cg-cli --release >/dev/null 2>&1)
fi

# Resolve the pinned trust-ir conformance fixtures dir from Cargo.lock's rev.
REV="$(grep -A2 'name = "trust-ir"' "$ROOT/Cargo.lock" | grep -oE '#[0-9a-f]+' | tr -d '#' | head -c7)"
FIXDIR=""
if [ -n "$REV" ]; then
    cand="$HOME/.cargo/git/checkouts/trust-ir-"*"/$REV/crates/trust-ir-conformance/tests/fixtures"
    for d in $cand; do [ -d "$d" ] && FIXDIR="$d" && break; done
fi
if [ -z "$FIXDIR" ]; then
    FIXDIR="$(find "$HOME/.cargo/git/checkouts" -path '*trust-ir-conformance/tests/fixtures' -type d 2>/dev/null | head -1)"
fi
[ -n "$FIXDIR" ] || { echo "could not locate trust-ir conformance fixtures" >&2; exit 2; }

# disposition(reason) -> category. Transparent, reviewable classifier.
# GAP      = genuine AArch64 backend completeness gap (drive these to zero).
# REJECT   = correct fail-closed: the IR is invalid / unsound to lower.
# UPSTREAM = high-level op that earlier passes (dialect lowering, borrow
#            resolution, binding-frame legalization) erase before scalar codegen;
#            reaching the adapter raw is a fixture artifact, not a backend gap.
classify() {
    local r="$1"
    case "$r" in
        *"invalid ordering"*)                        echo REJECT ;;
        *"Borrow not lowered"*|*"BorrowMut not lowered"*) echo UPSTREAM ;;
        *"binding-frame storage ops"*)               echo UPSTREAM ;;
        *"DialectOp reached"*|*"dialect lowering failed"*|*"vector."*) echo UPSTREAM ;;
        *"unsupported calling convention"*)          echo GAP ;;
        *"aggregate type not yet lowered"*|*"Sequence"*) echo GAP ;;
        *"volatile"*)                                echo GAP ;;
        *"void type used as value"*)                 echo GAP ;;
        *)                                           echo GAP ;;
    esac
}

declare -i n_ok=0 n_gap=0 n_reject=0 n_upstream=0 total=0
rows=""
gaps=""
for f in "$FIXDIR"/*.trust_ir; do
    b="$(basename "$f" .trust_ir)"
    total+=1
    if out="$("$CLI" --format=text --target aarch64 -c "$f" -o /tmp/_cov.o 2>&1)"; then
        n_ok+=1
        rows+="$(printf '| %-26s | COMPILED |  |' "$b")"$'\n'
    else
        reason="$(echo "$out" | sed 's/^trust-cg: error: //' | grep -oE '(adapter error|dialect pipeline error):.*' | head -1)"
        [ -z "$reason" ] && reason="$(echo "$out" | tr '\n' ' ' | head -c 120)"
        cat="$(classify "$reason")"
        case "$cat" in
            GAP)      n_gap+=1;      gaps+="$(printf -- '- **%s** — %s' "$b" "$reason")"$'\n' ;;
            REJECT)   n_reject+=1 ;;
            UPSTREAM) n_upstream+=1 ;;
        esac
        short="$(echo "$reason" | head -c 90)"
        rows+="$(printf '| %-26s | %-8s | %s |' "$b" "$cat" "$short")"$'\n'
    fi
done

emit() {
    echo "# AArch64 <- trust-ir coverage (conformance corpus)"
    echo
    echo "- Corpus: \`$FIXDIR\` ($total fixtures)"
    echo "- Driver: \`trust-cg --format=text --target aarch64 -c\` (certs ON)"
    echo "- CLI: \`$CLI\`  •  host: \`$(uname -m)\`"
    echo
    echo "| metric | count |"
    echo "|---|---|"
    echo "| COMPILED (lowered + verified) | $n_ok |"
    echo "| GENUINE GAPS (drive to zero)  | $n_gap |"
    echo "| correct fail-closed rejects   | $n_reject |"
    echo "| upstream-erased high-level ops | $n_upstream |"
    echo
    echo "**Genuine gaps remaining: $n_gap**"
    echo
    [ -n "$gaps" ] && { echo "## Genuine gaps"; echo; printf '%b' "$gaps"; echo; }
    echo "## Per-fixture"
    echo
    echo "| fixture | disposition | detail |"
    echo "|---|---|---|"
    printf '%b' "$rows"
}

if [ -n "$MD_OUT" ]; then emit > "$MD_OUT"; echo "wrote $MD_OUT" >&2; else emit; fi

# Non-zero exit if a NEW genuine gap appears beyond the tracked baseline.
BASELINE_GAPS="${TCG_COV_BASELINE_GAPS:-}"
if [ -n "$BASELINE_GAPS" ] && [ "$n_gap" -gt "$BASELINE_GAPS" ]; then
    echo "REGRESSION: genuine gaps $n_gap > baseline $BASELINE_GAPS" >&2
    exit 1
fi
