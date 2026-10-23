#!/usr/bin/env python3
"""Compile the Lean library module by module, in import order.

Each module is compiled with `lake env lean -o <olean> -i <ilean> <file>` into
.lake/build/lib/lean. `lake build` is deliberately not used: with linked dependency
packages it can try to rebuild Mathlib in place. Fails on any error, warning or
`sorry`. Writes audit/build.json unless `--no-record` is given (the replay driver passes
it, so that a replay does not modify tracked files).
"""
from __future__ import annotations

import json
import re
import subprocess
import sys
import time
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
ROOT = "JocelynWorkspace"
IMPORT = re.compile(r"^(?:public |private )?import\s+([\w.]+)", re.M)


def source(module: str) -> Path:
    return REPO / (module.replace(".", "/") + ".lean")


def repo_imports(module: str) -> list[str]:
    return [m for m in IMPORT.findall(source(module).read_text())
            if m == ROOT or m.startswith(ROOT + ".")]


def order() -> list[str]:
    seen: set[str] = set()
    out: list[str] = []

    def visit(m: str) -> None:
        if m in seen:
            return
        seen.add(m)
        for d in repo_imports(m):
            visit(d)
        out.append(m)

    visit(ROOT)
    return out


def main() -> int:
    rows = []
    for m in order():
        out = REPO / ".lake/build/lib/lean" / m.replace(".", "/")
        out.parent.mkdir(parents=True, exist_ok=True)
        t = time.time()
        p = subprocess.run(["nice", "-n", "10", "lake", "env", "lean",
                            "-o", f"{out}.olean", "-i", f"{out}.ilean",
                            str(source(m).relative_to(REPO))],
                           cwd=REPO, capture_output=True, text=True)
        text = p.stdout + p.stderr
        row = {"module": m, "returncode": p.returncode, "elapsed_s": round(time.time() - t, 1),
               "warnings": text.count("warning:"), "errors": text.count("error:"),
               "sorry": "sorry" in text}
        rows.append(row)
        print(f"{m}: rc={p.returncode} {row['elapsed_s']}s", flush=True)
        if p.returncode or row["warnings"] or row["errors"] or row["sorry"]:
            print(text[-4000:], file=sys.stderr)
            return 1
    if "--no-record" in sys.argv:
        print(f"built {len(rows)} modules, no warnings")
        return 0
    (REPO / "audit").mkdir(exist_ok=True)
    (REPO / "audit/build.json").write_text(json.dumps(
        {"toolchain": (REPO / "lean-toolchain").read_text().strip(), "modules": rows},
        indent=1) + "\n")
    print(f"built {len(rows)} modules, no warnings")
    return 0


if __name__ == "__main__":
    sys.exit(main())
