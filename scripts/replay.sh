#!/usr/bin/env bash
# Independent replay of the release declarations: Lean axiom audit -> lean4export ->
# Nanoda (standard axioms) -> Comparator statement check -> receipt in replay/receipts/.
# Tools and options: replay/TOOLS.md, `scripts/replay.sh --help`.
set -euo pipefail
cd "$(dirname "$0")/.."
exec python3 replay/replay.py "$@"
