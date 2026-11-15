#!/bin/zsh
# Slice 19 AY chain on the merged trees (origin/main fc03f94f2), one solver at a time;
# replay19.py's gate before every query (quiet.request, a census, any other AY).
# Waits for chain_merged.sh's probe dumps (or its death).
S=$HOME/tcg-scratch/s19; R=$S/replay
until grep -q "CHAIN-PROBES-DONE" $S/logs/chain_merged.log 2>/dev/null || ! pgrep -f "[c]hain_merged.sh" >/dev/null; do sleep 30; done
grep -q "CHAIN-PROBES-DONE" $S/logs/chain_merged.log || { echo "chain_merged died before its probes"; exit 1; }
cd $R
echo "== wide $(date +%H:%M)"
for tag in base20 s1b s3b; do python3 measure.py run $S/redump/wide_${tag}_mapped wide-$tag --fresh-only; done
echo "== s1b $(date +%H:%M)"; python3 measure.py run $S/redump/s1b_mapped s1b
echo "S1B-DONE $(date)"
echo "== s2b $(date +%H:%M)"; python3 measure.py run $S/redump/s2b_mapped s2b
echo "S2B-DONE $(date)"
echo "== s3b $(date +%H:%M)"; python3 measure.py run $S/redump/s3b_mapped s3b
python3 - <<'PY'
import json, os, shutil, hashlib
S = os.path.expanduser('~/tcg-scratch/s19')
fresh = {}
for l in open(f'{S}/replay/results/fresh.jsonl'):
    r = json.loads(l); fresh[r['sha']] = r['outcome']
src, dst = f'{S}/redump/s3b_mapped_claims', f'{S}/redump/s3b_claims_needed'
shutil.rmtree(dst, ignore_errors=True); os.makedirs(dst)
n = 0
claims = sorted(os.listdir(src)) if os.path.isdir(src) else []
for f in sorted(os.listdir(f'{S}/redump/s3b_mapped')):
    s = hashlib.sha256(open(f'{S}/redump/s3b_mapped/{f}', 'rb').read()).hexdigest()
    if fresh.get(s) == 'certified':
        continue
    for c in claims:
        if c.startswith(f[:-5] + '.c') and c.endswith('.smt2'):
            shutil.copyfile(f'{src}/{c}', f'{dst}/{c}'); n += 1
print('claims needed', n)
PY
python3 measure.py run $S/redump/s3b_claims_needed s3b-claims
echo "S3B-DONE $(date)"
until grep -q "CHAIN-ALL-DONE" $S/logs/chain_merged.log 2>/dev/null || ! pgrep -f "[c]hain_merged.sh" >/dev/null; do sleep 30; done
grep -q "CHAIN-ALL-DONE" $S/logs/chain_merged.log || { echo "chain_merged died before the whole-core probes"; exit 1; }
echo "== regress $(date +%H:%M)"
S19_CENSUS_LOG=$HOME/tcg-scratch/runs/census-s20/stderr.log python3 regress.py prepare $S/all/base20 $S/all/s3b $S/regress/s3b
python3 measure.py run $S/regress/s3b/queries s3b-regress --fresh-only
python3 regress.py report $S/regress/s3b
echo "CHAIN-MEAS2-DONE $(date)"
