#!/bin/zsh
# Stage 3's claims (claims_seq.py: in order, stopping at the first that does not certify,
# as the bridge replays them), then the whole-core regression check, one-shot only.
# One solver at a time (replay19.py's gate).
S=$HOME/tcg-scratch/s19; R=$S/replay
cd $R
echo "== s3b claims $(date +%H:%M)"
python3 claims_seq.py $S/redump/s3b_mapped $S/redump/s3b_mapped_claims
echo "S3B-DONE $(date)"
echo "== regress $(date +%H:%M)"
S19_CENSUS_LOG=$HOME/tcg-scratch/runs/census-s20/stderr.log python3 regress.py prepare $S/all/base20 $S/all/s3b $S/regress/s3b
python3 measure.py run $S/regress/s3b/queries s3b-regress --fresh-only
python3 regress.py report $S/regress/s3b
echo "CHAIN-MEAS4-DONE $(date)"
