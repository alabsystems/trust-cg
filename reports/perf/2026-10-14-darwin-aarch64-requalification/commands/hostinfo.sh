#!/bin/bash
# Host identity and toolchain versions for the Darwin arm64 requalification record.
set -u
export PATH="$HOME/.cargo/bin:$HOME/Library/Application Support/aterm/pkg/bin:/opt/homebrew/bin:$PATH"
WT="$1"
PKG="$2"
DYLIB="$WT/crates/rustc-codegen-trust-cg/target-bridge/release/librustc_codegen_trust_cg.dylib"
echo "# Host identity and toolchains — $(date -u +%FT%TZ)"
echo "## machine"
for key in hw.model machdep.cpu.brand_string hw.ncpu hw.physicalcpu hw.logicalcpu hw.nperflevels \
  hw.perflevel0.name hw.perflevel0.physicalcpu hw.perflevel1.name hw.perflevel1.physicalcpu \
  hw.memsize hw.pagesize; do
  printf '%s: %s\n' "$key" "$(sysctl -n "$key" 2>/dev/null)"
done
echo "memory_gib: $(python3 -c "print($(sysctl -n hw.memsize)/2**30)")"
echo "## operating system"
sw_vers
uname -srvm
echo "## power"
pmset -g batt | sed -n 1,2p
pmset -g | grep -E "powermode|lowpowermode" || true
echo "## Trust package (every measured lane)"
echo "package: $PKG"
"$PKG/bin/trustc" -vV
"$PKG/bin/targo" --version
echo "## independent proof checker candidates (as the backend reported them)"
"$HOME/Library/Application Support/aterm/pkg/store/clean/current/bin/clean" --version 2>&1 | head -1
echo "managed clean: $(readlink "$HOME/Library/Application Support/aterm/pkg/store/clean/current")"
"$PKG/bin/clean" --version 2>&1 | head -1
echo "## linker and C toolchain"
cc --version 2>&1 | head -2
ld -v 2>&1 | head -1
xcrun --show-sdk-version 2>/dev/null | sed 's/^/macOS SDK: /'
echo "## harness interpreter"
python3 --version
echo "## bridge backend"
echo "path: $DYLIB"
stat -f 'bytes: %z  mtime: %Sm' -t '%FT%T%z' "$DYLIB"
shasum -a 256 "$DYLIB" | awk '{print "sha256: " $1}'
echo "build: cd crates/rustc-codegen-trust-cg && CARGO_TARGET_DIR=target-bridge RUSTC=$PKG/bin/trustc TRUST_TARGO=$PKG/bin/targo ../../scripts/trust_cargo.sh build --release --locked (= $PKG/bin/targo --unverified build --release --locked)"
echo "## source"
git -C "$WT" rev-parse HEAD
git -C "$WT" log -1 --format='%H %cI %s'
grep -E '^trust-ir ' "$WT/Cargo.toml" | head -1
