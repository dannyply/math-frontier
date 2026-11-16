#!/usr/bin/env bash
# Build a paper PDF with Tectonic from cached TeX resources:
#   scripts/build-paper.sh powerful-counting [--allow-downloads]
# Output: build/papers/<name>/main.pdf (copy it to papers/<name>/main.pdf to install).
set -euo pipefail
cd "$(dirname "$0")/.."
name="${1:?paper name}"
out="build/papers/$name"
mkdir -p "$out"
if [[ "${2:-}" == "--allow-downloads" ]]; then
  nice -n 10 tectonic --untrusted --keep-logs --outdir "$out" "papers/$name/main.tex" >"$out/build.stdout" 2>&1
else
  nice -n 10 tectonic --untrusted --keep-logs --outdir "$out" --only-cached "papers/$name/main.tex" >"$out/build.stdout" 2>&1
fi
grep -qi "overfull\|undefined" "$out/main.log" && { echo "layout warnings in $out/main.log" >&2; exit 1; }
echo "built $out/main.pdf"
