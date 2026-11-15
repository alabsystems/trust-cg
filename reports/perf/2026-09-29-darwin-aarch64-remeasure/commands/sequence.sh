#!/bin/bash
# How the 2026-09-29 re-measure's campaign.sh invocations were sequenced after
# the first full run (README "Attempts"): the evidence lane again behind the
# strict quiet wait, then the scaling harnesses behind a looser one, then the
# canary and sentinel (fail-closed verdicts, no timing gate) with no wait,
# then the two repeats. Each line was run as its own invocation, in order.
#
# Usage: SCALING_WORK=<scratch dir> sequence.sh <checkout> <campaign-dir> <trust-package>
set -u
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
QUIET_MAX1=4.0 QUIET_MAX5=6.0 STEPS="01" bash "$HERE/campaign.sh" "$@"
QUIET_MAX1=5.0 QUIET_MAX5=7.0 STEPS="06 07" bash "$HERE/campaign.sh" "$@"
QUIET_MAX1=1000 QUIET_MAX5=1000 STEPS="08 09" bash "$HERE/campaign.sh" "$@"
# Repeats (not evidence): the scaling gate's large/xlarge and the diagnostic lane.
QUIET_MAX1=4.0 QUIET_MAX5=6.0 STEPS="11 12" bash "$HERE/campaign.sh" "$@"
