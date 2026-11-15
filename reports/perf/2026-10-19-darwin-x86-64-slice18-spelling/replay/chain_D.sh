#!/bin/zsh
# Slice 18 stage 3: census-s17's split bodies' parts re-dumped through the REAL builder (probe-D,
# each part spelled again, OD-189), named by their region's original part, replayed offline on
# AY 12713 + Clean 5f09e36c: one-shot, then the resident leg on what certifies.
R=$HOME/tcg-scratch/s18/replay
AY=$HOME/.local/share/trust-overlays/x86-stage1-ay12713/bin/ay
CLEAN=$HOME/.local/share/trust-overlays/x86-stage1-ay12713/bin/clean
Q=$HOME/tcg-scratch/s18/redump/D_parts
cd $R
files=($(cat parts253.txt))
echo "== D one-shot ${#files} $(date)"
python3 $R/run_replays.py --ay $AY --clean $CLEAN --route fresh --label D-12713 --qdir $Q --out $R/d_12713_fresh.jsonl $files
cert=($(python3 -c "import json; print(' '.join(json.loads(l)['query'] for l in open('$R/d_12713_fresh.jsonl') if json.loads(l)['outcome']=='certified'))"))
echo "== D resident ${#cert} $(date)"
python3 $R/run_replays.py --ay $AY --clean $CLEAN --route resident --label D-12713-resident --qdir $Q --out $R/d_12713_resident.jsonl $cert
echo "CHAIN-D-DONE $(date)"
