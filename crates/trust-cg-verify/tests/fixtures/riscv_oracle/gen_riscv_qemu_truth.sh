#!/usr/bin/env bash
# gen_riscv_qemu_truth.sh — REGENERATOR for riscv_qemu_truth.json.
#
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Copyright 2026 Andrew Yates | License: Apache-2.0
#
# ===========================================================================
# What this does
# ===========================================================================
# Builds the bare-metal RV64 oracle harness (oracle.rs) with rustc's RISC-V
# backend, runs it under qemu-system-riscv64 (an INDEPENDENT RISC-V executor —
# a software golden model of the ISA), captures the JSON it prints over the UART,
# splices in the live qemu version + date, validates the @@ORACLE_OK@@ sentinel
# (no silent truncation), and writes the committed fixture
#   crates/trust-cg-verify/tests/fixtures/riscv_qemu_truth.json
# consumed by tests/bdefs_differential_bridge_riscv.rs.
#
# ===========================================================================
# Prerequisites (all user-level)
# ===========================================================================
#   * qemu-system-riscv64        (brew install qemu)   — the independent executor
#   * rustc + riscv64gc-unknown-none-elf target
#       (rustup target add riscv64gc-unknown-none-elf) — the RV64 code producer
#       (Apple clang has no RISC-V backend; rustc's bundled LLVM does)
#   * rust-lld (bundled in the rustc toolchain rustlib/<host>/bin)
#
# ===========================================================================
# Usage
# ===========================================================================
#   crates/trust-cg-verify/tests/fixtures/riscv_oracle/gen_riscv_qemu_truth.sh
#
set -euo pipefail

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
OUT="$(cd "$HERE/.." && pwd)/riscv_qemu_truth.json"

export PATH="$HOME/.cargo/bin:$PATH"
RUSTBIN="$(rustc --print sysroot)/lib/rustlib/$(rustc -vV | sed -n 's/host: //p')/bin"
export PATH="$RUSTBIN:$PATH"   # rust-lld linker

TARGET="riscv64gc-unknown-none-elf"
ELF="$HERE/oracle.elf"
RAW="$HERE/oracle_raw.out"

echo "[1/4] building RV64 oracle ELF (rustc $TARGET)..."
rustc --edition 2021 --target "$TARGET" \
  -C panic=abort -C opt-level=2 \
  -C link-arg=-T"$HERE/virt.ld" -C link-arg=-no-pie \
  -o "$ELF" "$HERE/oracle.rs"

file "$ELF" | grep -qi "RISC-V" || { echo "ERROR: produced ELF is not RISC-V"; exit 2; }

echo "[2/4] running under qemu-system-riscv64 (independent executor)..."
qemu-system-riscv64 -machine virt -nographic -bios none \
  -kernel "$ELF" -monitor none -serial stdio > "$RAW" 2>/dev/null

grep -q "@@ORACLE_OK" "$RAW" || {
  echo "ERROR: oracle did not emit the @@ORACLE_OK@@ sentinel — incomplete/failed run:";
  tail -5 "$RAW"; exit 3;
}
OKCOUNT="$(grep -o '@@ORACLE_OK [0-9]*@@' "$RAW" | grep -o '[0-9]*')"
echo "      oracle reported a CLEAN run of $OKCOUNT facts."

echo "[3/4] splicing provenance (qemu version + date)..."
QEMU_VER="$(qemu-system-riscv64 --version | head -1)"
DATE="$(date -u +%Y-%m-%dT%H:%M:%SZ)"

# Strip the trailing @@ sentinel line(s) -> pure JSON, then splice the version +
# date placeholders. Done with sed (robust on the large file; the bash ${//}
# parameter expansion mishandles multi-hundred-KB strings).
TMP="$HERE/oracle_spliced.json"
sed -e '/@@ORACLE/d' \
    -e "s|@QEMU_VERSION@|$QEMU_VER|" \
    -e "s|@DATE@|$DATE|" \
    "$RAW" > "$TMP"

echo "[4/4] validating + writing $OUT..."
# Validate it is well-formed JSON and the accounting agrees, via python3.
python3 -c '
import sys, json
with open(sys.argv[1]) as f:
    d = json.load(f)
acc = d["_accounting"]
assert acc["total_attempted"] == acc["emitted"], "accounting: attempted != emitted (silent truncation)"
assert acc["emitted"] == len(d["facts"]), "accounting: emitted != len(facts)"
assert acc["trap_facts"] == 0, "RV64 integer ALU produces no traps"
n = len(d["facts"])
print("  validated %d facts, accounting consistent." % n)
' "$TMP"

mv "$TMP" "$OUT"
rm -f "$ELF" "$RAW"
echo "DONE: wrote $OUT"
echo "      oracle: $QEMU_VER"
