#!/bin/bash
# Writes PAYLOADS.md from scripts/payloads24c.py's table rows.
D=$(cd "$(dirname "$0")/.." && pwd)
{
cat <<'HEAD'
# Payload inventory

This record follows the durable evidence policy
([docs/linux-aarch64-completion.md](../../../docs/linux-aarch64-completion.md#durable-evidence-policy)):
a dated record keeps its Markdown narrative and reproducer sources in tree, and
its payloads (logs, outcome tables, queries, dumps, job files) out of it. These
payloads were never committed. They are held on the measuring host (the x86_64
Mac of the README) under `~/tcg-scratch`, at the paths below, and are bound
here by size and SHA-256. `scripts/payloads24c.py` regenerates the table
(`scripts/write_payloads.sh` this file). The README states the numbers each
one carries.

| Path (under `~/tcg-scratch`) | Bytes | SHA-256 |
| --- | ---: | --- |
HEAD
python3 -I "$D/scripts/payloads24c.py"
} > "$D/PAYLOADS.md"
