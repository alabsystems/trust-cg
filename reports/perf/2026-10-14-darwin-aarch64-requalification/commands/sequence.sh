#!/bin/bash
# How the 2026-10-14 requalification's campaign.sh invocations were sequenced:
# host identity first, then the evidence lane behind the strict quiet wait, the
# diagnostic lane behind the same wait, the scaling harnesses behind a looser
# one, the canary and sentinel (fail-closed verdicts, no timing gate) with no
# wait, then the L14-P7 larger corpus behind the looser wait. The ledger append
# (step 13) ran afterwards as its own invocation, once the evidence results had
# been read (EVIDENCE_JSON names them).
#
# Usage: SCALING_WORK=<scratch dir> TRUST_CHECKOUT=<trust checkout> \
#        sequence.sh <checkout> <campaign-dir> <trust-package>
set -u
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
bash "$HERE/hostinfo.sh" "$1" "$3" > "$2/host.txt" 2>&1
QUIET_MAX1=4.0 QUIET_MAX5=6.0 STEPS="01" bash "$HERE/campaign.sh" "$@"
QUIET_MAX1=4.0 QUIET_MAX5=6.0 STEPS="04" bash "$HERE/campaign.sh" "$@"
QUIET_MAX1=5.0 QUIET_MAX5=7.0 STEPS="06 07" bash "$HERE/campaign.sh" "$@"
QUIET_MAX1=1000 QUIET_MAX5=1000 STEPS="08 09" bash "$HERE/campaign.sh" "$@"
QUIET_MAX1=5.0 QUIET_MAX5=7.0 STEPS="10" bash "$HERE/campaign.sh" "$@"
