#!/bin/bash
# After an eligible evidence attempt (attempt 3): the rest of the same-revision
# set, so every L14-P1 measurement shares the evidence row's revision. The
# diagnostic lane and its load-robust companion behind the strict quiet wait,
# the scaling harnesses behind the looser one, the canary and sentinel with no
# wait. The ledger append (step 13) runs afterwards, and the L14-P7 corpus
# (step 10) after the append's commit.
#
# Usage: SCALING_WORK=<scratch dir> sequence3.sh <checkout> <campaign-dir> <trust-package>
set -u
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
QUIET_MAX1=4.0 QUIET_MAX5=6.0 STEPS="04" bash "$HERE/campaign.sh" "$@"
QUIET_MAX1=4.0 QUIET_MAX5=6.0 STEPS="14" bash "$HERE/campaign.sh" "$@"
QUIET_MAX1=5.0 QUIET_MAX5=7.0 STEPS="06 07" bash "$HERE/campaign.sh" "$@"
QUIET_MAX1=1000 QUIET_MAX5=1000 STEPS="08 09" bash "$HERE/campaign.sh" "$@"
