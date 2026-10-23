#!/usr/bin/env bash
# Axiom and statement audit of the release declarations (see scripts/audit.py).
set -euo pipefail
cd "$(dirname "$0")/.."
exec python3 scripts/audit.py "$@"
