#!/usr/bin/env python3
"""Regression test for the statement fingerprint.

Elaborates the negative-control statement (Theorem 1.2 with 77/320 replaced by 76/320)
under a fresh name next to the release declaration counting_thm_k3, renders both with the
fingerprint options of replay/AuditRelease.lean, and checks that neither rendering is
truncated, that the two fingerprints differ, and that the release fingerprint equals the
manifest's statement_sha256.
"""
from __future__ import annotations

import hashlib
import json
import re
import subprocess
import sys
import tempfile
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
TARGET = "JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.Erdos137Final.counting_thm_k3"
OPTIONS = "(o.setBool `pp.all true).set `pp.maxSteps (1000000000 : Nat)"


def main() -> int:
    audit_src = (REPO / "replay/AuditRelease.lean").read_text()
    if OPTIONS not in audit_src:
        print("replay/AuditRelease.lean does not use the fingerprint options this test checks",
              file=sys.stderr)
        return 1
    control = (REPO / "replay/negative-control/CountingNegativeControl.lean").read_text()
    control = re.sub(r"^import .*$", "", control, flags=re.M)
    control = control.replace(f"theorem {TARGET}", "theorem FingerprintTest.k3_strong", 1)
    if "FingerprintTest.k3_strong" not in control:
        print("negative control does not restate counting_thm_k3", file=sys.stderr)
        return 1
    probe = f"""import JocelynWorkspace
{control}
open Lean Elab Command Meta
run_cmd do
  let env ← getEnv
  for n in [`{TARGET}, `FingerprintTest.k3_strong] do
    let some ci := env.find? n | throwError "missing {{n}}"
    let s ← liftTermElabM <| withOptions (fun o => {OPTIONS}) do
      return (← ppExpr ci.type).pretty 100000
    IO.println ("FINGERPRINT " ++ n.toString ++ " " ++ toString (decide ((s.splitOn "⋯").length > 1)))
    IO.println ("TEXT " ++ (toJson s).compress)
"""
    with tempfile.TemporaryDirectory() as tmp:
        path = Path(tmp) / "FingerprintProbe.lean"
        path.write_text(probe)
        p = subprocess.run(["nice", "-n", "10", "lake", "env", "lean", str(path)],
                           cwd=REPO, capture_output=True, text=True)
    if p.returncode != 0:
        print("probe failed:\n" + p.stdout[-3000:] + p.stderr[-2000:], file=sys.stderr)
        return 1
    lines = p.stdout.splitlines()
    rows = []
    for i, line in enumerate(lines):
        if line.startswith("FINGERPRINT "):
            _, name, truncated = line.split(" ")
            text = json.loads(lines[i + 1][len("TEXT "):])
            rows.append((name, truncated == "true", text))
    if len(rows) != 2:
        print("probe did not elaborate:\n" + p.stdout[-3000:] + p.stderr[-2000:], file=sys.stderr)
        return 1
    (real, real_trunc, real_text), (_, ctl_trunc, ctl_text) = rows
    manifest = json.loads((REPO / "release/manifest.json").read_text())
    expected = next(d["statement_sha256"] for d in manifest["declarations"] if d["name"] == TARGET)
    failures = []
    if real_trunc or ctl_trunc:
        failures.append("a rendering is truncated")
    if real_text == ctl_text:
        failures.append("77/320 and 76/320 statements render identically")
    if failures:
        print("\n".join(failures), file=sys.stderr)
        return 1
    fresh = hashlib.sha256(real_text.encode()).hexdigest()
    if fresh != expected:
        print(f"fresh fingerprint {fresh[:12]} differs from the manifest {expected[:12]}",
              file=sys.stderr)
        return 1
    if hashlib.sha256(ctl_text.encode()).hexdigest() == expected:
        print("the 76/320 statement has the manifest fingerprint", file=sys.stderr)
        return 1
    print("fingerprint test passed: untruncated renderings, 76/320 and 77/320 differ, "
          f"manifest fingerprint {expected[:12]}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
