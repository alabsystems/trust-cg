cd ~/tcg-scratch/wt-od233 || exit 9
export CARGO_TARGET_DIR=$HOME/tcg-scratch/stage1-targets/wt-od233-own
echo "== gate6 at $(git -C ~/tcg-scratch/wt-od233 rev-parse HEAD) $(date +%T)"
git -C ~/tcg-scratch/wt-od233 status --short
echo "== fmt"
TRUST_TARGO="$HOME/Library/Application Support/aterm/pkg/store/trust/6808/bin/targo" bash scripts/check_fmt.sh; echo "fmt-exit=$?"
echo "== docs"
python3 scripts/check_documentation.py --check; echo "docs-exit=$?"
echo "== matrix"
TRUST_TARGO=$HOME/.local/share/trust-overlays/x86-stage1-ay13556-t011/bin/targo python3 scripts/full_test_matrix_hosts.py --check; echo "matrix-exit=$?"
echo "== gate6 done $(date +%T)"
