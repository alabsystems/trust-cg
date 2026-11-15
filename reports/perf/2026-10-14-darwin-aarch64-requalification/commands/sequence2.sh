#!/bin/bash
# The sequence after the first evidence attempt ended LOADED (sequence.sh's
# first two lines ran; it was stopped while waiting before step 04): the
# evidence step repeated behind a stricter quiet wait until an attempt is
# eligible (evidence_until_quiet.sh), then the diagnostic lane and its
# load-robust companion behind the strict wait, the scaling harnesses behind a
# looser one, the canary and sentinel with no wait, and the L14-P7 larger
# corpus behind the looser wait. The ledger append (step 13) runs afterwards.
#
# Usage: SCALING_WORK=<scratch dir> TRUST_CHECKOUT=<trust checkout> \
#        sequence2.sh <checkout> <campaign-dir> <trust-package>
set -u
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
FIRST_ATTEMPT=2 MAX_ATTEMPTS=8 bash "$HERE/evidence_until_quiet.sh" "$@"
QUIET_MAX1=4.0 QUIET_MAX5=6.0 STEPS="04" bash "$HERE/campaign.sh" "$@"
QUIET_MAX1=4.0 QUIET_MAX5=6.0 STEPS="14" bash "$HERE/campaign.sh" "$@"
QUIET_MAX1=5.0 QUIET_MAX5=7.0 STEPS="06 07" bash "$HERE/campaign.sh" "$@"
QUIET_MAX1=1000 QUIET_MAX5=1000 STEPS="08 09" bash "$HERE/campaign.sh" "$@"
QUIET_MAX1=5.0 QUIET_MAX5=7.0 STEPS="10" bash "$HERE/campaign.sh" "$@"
