#!/usr/bin/env bash
# Fetch the optional Kissat benchmark reference at trust-cg's audited revision.
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
dest="$repo_root/third_party/kissat"
url="https://github.com/arminbiere/kissat.git"
revision="8af8e56f174b778aef3aa45af9f739b2a5f492c2"

if git -C "$dest" rev-parse --is-inside-work-tree >/dev/null 2>&1; then
    git -C "$dest" fetch --quiet origin "$revision"
elif [ -e "$dest" ]; then
    echo "fetch-kissat: $dest exists but is not a Git checkout" >&2
    exit 1
else
    git clone --filter=blob:none --no-checkout "$url" "$dest"
    git -C "$dest" fetch --quiet origin "$revision"
fi

git -C "$dest" checkout --quiet --detach "$revision"
actual="$(git -C "$dest" rev-parse HEAD)"
[ "$actual" = "$revision" ] || {
    echo "fetch-kissat: expected $revision, got $actual" >&2
    exit 1
}

echo "Kissat ready at $dest ($actual)"
