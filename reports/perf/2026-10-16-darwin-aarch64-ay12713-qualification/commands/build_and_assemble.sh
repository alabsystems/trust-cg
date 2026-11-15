#!/bin/sh
# The commands that built the replayer pair and the overlays, as run on
# 2026-10-16 (aarch64-apple-darwin). R is the scratch root; nothing is
# installed into a toolchain or package store.
R=$HOME/scratch.noindex/round3-20261016
PKG="$HOME/Library/Application Support/aterm/pkg/store"

# trust-cg worktree on origin/main 190b3e53d, submodules from the shared modules.
git -C ~/trust-cg worktree add -b qual/aarch64-darwin-20261016 "$R/trust-cg" origin/main
for p in drat-trim kissat microsat; do
  git -C "$R/trust-cg" submodule update --init \
    --reference ~/trust-cg/.git/modules/third_party/$p third_party/$p
done

# AY b1b0b9de0 (build 12713, QUALIFIED_AY): a worktree, built from a sibling
# directory whose .cargo/config.toml is AY's minus its Trust-lane config block
# (trust-cg scripts/check_x86_icmp_certificates.py strip_trust_lane_config),
# so the checkout stays clean and the banner's build number is git's.
git -C ~/ay worktree add --detach "$R/ay" b1b0b9de07af146c1244633189f92971a3347db9
mkdir -p "$R/ay-build/.cargo"   # config.toml written by strip_trust_lane_config
cd "$R/ay-build" && CARGO_TARGET_DIR="$R/ay-target" build-slot -- \
  targo --unverified build --release --locked --manifest-path "$R/ay/Cargo.toml" -p ay --features cli

# Clean 92bcc8979 (the revision trust-cg's Cargo.lock pins), with carcara-verify.
git -C ~/clean worktree add --detach "$R/clean-92bc" 92bcc897908b248154ace880a6c518a3d9c09634
cd "$R/clean-92bc" && CARGO_TARGET_DIR="$R/clean-target" build-slot -- \
  "$R/trust-cg/scripts/trust_cargo.sh" build --locked --release -p clean --bin clean --features clean/carcara-verify

# Clean 8606, the package checker an ordinary build here selects: its binary
# embeds 8da2da391, whose rev-list count is 8606; the worktree is only the
# assembler's source label.
git -C ~/clean worktree add --detach "$R/clean-src" 8da2da391b410d89bb3c2b3e37742312e06b8977

cd "$R/trust-cg"
# The measured overlay with the package Clean (measure 0, not the recorded pair).
python3 scripts/assemble_trust_overlay.py --pack "$PKG/trust/9192" \
  --ay "$R/ay-target/release/ay" --ay-src "$R/ay" \
  --clean "$PKG/clean/8606/bin/clean" --clean-src "$R/clean-src" \
  --out "$R/overlay-ay12713-clean8606" \
  --require-ay-ancestor b1b0b9de07af146c1244633189f92971a3347db9 \
  --require-clean-ancestor 8da2da391b410d89bb3c2b3e37742312e06b8977
# The recorded pair's overlay.
python3 scripts/assemble_trust_overlay.py --pack "$PKG/trust/9192" \
  --ay "$R/ay-target/release/ay" --ay-src "$R/ay" \
  --clean "$R/clean-target/release/clean" --clean-src "$R/clean-92bc" \
  --out "$R/overlay-ay12713-clean92bc" \
  --require-ay-ancestor b1b0b9de07af146c1244633189f92971a3347db9 \
  --require-clean-ancestor 92bcc897908b248154ace880a6c518a3d9c09634
