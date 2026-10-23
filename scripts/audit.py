#!/usr/bin/env python3
"""Axiom and statement audit of the release declarations.

Runs `lake env lean replay/AuditRelease.lean` on the names in release/manifest.json and
checks, for every declaration: it exists, its module is the manifest's, its axioms are
exactly the manifest's (a subset of propext, Classical.choice, Quot.sound), and the
sha256 of its full pp.all type equals the manifest's statement_sha256. The rendering must
contain no elision and no two declarations may share a fingerprint. Writes audit/axioms.json.

  scripts/audit.sh                    check against the manifest
  scripts/audit.sh --update-manifest  write the audited statement hashes into the manifest
                                      (only after a deliberate statement or fingerprint change)
"""
from __future__ import annotations

import hashlib
import json
import os
import subprocess
import sys
import tempfile
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent


def main() -> int:
    manifest = json.loads((REPO / "release/manifest.json").read_text())
    standard = set(manifest["standard_axioms"])
    entries = {d["name"]: d for d in manifest["declarations"]}
    with tempfile.NamedTemporaryFile("w", suffix=".txt", delete=False) as f:
        f.write("\n".join(entries) + "\n")
        names_file = f.name
    try:
        p = subprocess.run(["nice", "-n", "10", "lake", "env", "lean", "replay/AuditRelease.lean"],
                           cwd=REPO, capture_output=True, text=True,
                           env={**os.environ, "REPLAY_DECLS_FILE": names_file})
    finally:
        os.unlink(names_file)
    rows = {}
    for line in p.stdout.splitlines():
        if line.startswith("REPLAY-AUDIT "):
            r = json.loads(line[len("REPLAY-AUDIT "):])
            rows[r["name"]] = r
    update = "--update-manifest" in sys.argv
    failures, out = [], []
    for name, e in entries.items():
        r = rows.get(name)
        if not r or not r.get("found"):
            failures.append(f"{name}: not found")
            continue
        sha = hashlib.sha256(r["type_pp_all"].encode()).hexdigest()
        if r.get("pp_truncated", True):
            failures.append(f"{name}: statement rendering is truncated")
        if update:
            e["statement_sha256"] = sha
        problems = [k for k, ok in [
            ("module", r["module"] == e["module"]),
            ("axioms", sorted(r["axioms"]) == sorted(e["axioms"])),
            ("non-standard axiom", set(r["axioms"]) <= standard),
            ("statement_sha256", sha == e["statement_sha256"])] if not ok]
        if problems:
            failures.append(f"{name}: {', '.join(problems)}")
        out.append({"name": name, "module": r["module"], "axioms": sorted(r["axioms"]),
                    "statement_sha256": sha})
    seen: dict[str, str] = {}
    for row in out:
        other = seen.setdefault(row["statement_sha256"], row["name"])
        if other != row["name"]:
            failures.append(f"{row['name']}: same statement fingerprint as {other}")
    if p.returncode or "error:" in p.stdout or "warning:" in p.stdout:
        failures.append("AuditRelease.lean did not elaborate cleanly:\n" + p.stdout[-2000:] + p.stderr[-2000:])
    if failures:
        print("\n".join(failures), file=sys.stderr)
        return 1
    if update:
        (REPO / "release/manifest.json").write_text(json.dumps(manifest, indent=1, ensure_ascii=False) + "\n")
        print("manifest statement hashes updated")
    (REPO / "audit").mkdir(exist_ok=True)
    (REPO / "audit/axioms.json").write_text(json.dumps(
        {"standard_axioms": sorted(standard), "declarations": out}, indent=1) + "\n")
    print(f"audit passed: {len(out)} declarations, standard axioms only, statements match the manifest")
    return 0


if __name__ == "__main__":
    sys.exit(main())
