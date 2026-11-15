#!/bin/zsh
# Slice 18 stage 1: the census-s17 single theorems re-dumped through the REAL builder (probe-B,
# the canonical cascade), replayed offline on AY 12713 + Clean 5f09e36c: one-shot, then the
# resident leg on those the one-shot route certifies. Sequential, quiet.request-aware.
R=$HOME/tcg-scratch/s18/replay
AY=$HOME/.local/share/trust-overlays/x86-stage1-ay12713/bin/ay
CLEAN=$HOME/.local/share/trust-overlays/x86-stage1-ay12713/bin/clean
Q=$HOME/tcg-scratch/s18/redump/B_mapped
cd $R
files=($(cat singles91.txt))
echo "== B one-shot ${#files} $(date)"
python3 $R/run_replays.py --ay $AY --clean $CLEAN --route fresh --label B-12713 --qdir $Q --out $R/b_12713_fresh.jsonl $files
cert=($(python3 -c "import json; print(' '.join(json.loads(l)['query'] for l in open('$R/b_12713_fresh.jsonl') if json.loads(l)['outcome']=='certified'))"))
echo "== B resident ${#cert} $(date)"
python3 $R/run_replays.py --ay $AY --clean $CLEAN --route resident --label B-12713-resident --qdir $Q --out $R/b_12713_resident.jsonl $cert
echo "CHAIN-B-DONE $(date)"
