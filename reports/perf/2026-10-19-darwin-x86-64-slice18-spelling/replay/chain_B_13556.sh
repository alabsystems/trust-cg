#!/bin/zsh
# Slice 18 stage 1, for the coordinator: the canonical spelling's real bytes of census-s17's 91
# single theorems (probe-B) replayed offline on AY main ebde49de3 (build 13556) with Clean
# 5f09e36c: one-shot, then the resident leg on what certifies. Sequential, quiet.request-aware.
R=$HOME/tcg-scratch/s18/replay
AY=$HOME/tcg-scratch/ay-cert/bin/ay-main-ebde49de3
CLEAN=$HOME/.local/share/trust-overlays/x86-stage1-ay12713/bin/clean
Q=$HOME/tcg-scratch/s18/redump/B_mapped
cd $R
files=($(cat singles91.txt))
echo "== B one-shot 13556 ${#files} $(date)"
python3 $R/run_replays.py --ay $AY --clean $CLEAN --route fresh --label B-13556 --qdir $Q --out $R/b_13556_fresh.jsonl $files
cert=($(python3 -c "import json; print(' '.join(json.loads(l)['query'] for l in open('$R/b_13556_fresh.jsonl') if json.loads(l)['outcome']=='certified'))"))
echo "== B resident 13556 ${#cert} $(date)"
python3 $R/run_replays.py --ay $AY --clean $CLEAN --route resident --label B-13556-resident --qdir $Q --out $R/b_13556_resident.jsonl $cert
echo "CHAIN-B13556-DONE $(date)"
