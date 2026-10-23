#!/usr/bin/env bash
# Compile the Lean library module by module (never `lake build`; see scripts/build.py).
set -euo pipefail
cd "$(dirname "$0")/.."
exec python3 scripts/build.py "$@"
