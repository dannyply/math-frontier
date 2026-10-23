#!/usr/bin/env python3
"""Independent replay of the release declarations of math-frontier.

Pipeline (Python 3 standard library only):

  (a) Lean axiom audit: `lake env lean replay/AuditRelease.lean` (Lean.collectAxioms plus
      the pp.all statement text for every declaration).
  (b) Export: lean4export dumps the declarations and their transitive dependencies from the
      built `JocelynWorkspace` environment. It runs under `lake env`, with the kernel
      primitive roots the Jocelyn harness uses.
  (c) Nanoda, a second kernel written in Rust, independent of Lean's C++ kernel:
        pass "standard": permitted axioms = propext, Classical.choice, Quot.sound only;
        pass "native":   those three plus exactly the declaration's own
                         `._native.native_decide.ax_*` axioms, read from its export.
      `unpermitted_axiom_hard_error` is on, so Nanoda rejects an export that contains any
      other axiom, whether or not a declaration uses it.
  (d) Optional Comparator statement check against a statements file (`--statements`).
  (e) A machine-readable receipt under replay/receipts/. Receipts contain no absolute
      paths: repository files are recorded relative to the repository root, the work
      directory as `<work>`, tools outside the repository by file name and sha256.

The declarations come from release/manifest.json (the single source of truth), unless
`--decls` or `--release-audit` is given. Every Lean audit row is cross-checked against the
manifest: statement hash (`statement_sha256` = sha256 of the pp.all type), exact axiom set,
exact native_decide axiom list and evidence level.

Dependency mode. By default the run is a clean-clone run and fails if `.lake/packages` (or
any package in it) is a symbolic link, because then the checked Mathlib is not the one a
fresh clone would fetch from lake-manifest.json. `--local-deps` accepts linked packages;
the receipt then records `dependency_mode: "local-deps"` and the label `non-clean-deps`.

Declarations with only standard axioms (L1) are exported together into one export. If that
export fails Nanoda, the driver re-checks each L1 declaration on its own, so failures are
attributed to single declarations. Each declaration that uses native_decide axioms (L2) gets
its own export. Nanoda then proves, independently of Lean's collectAxioms, that the
declaration's dependency closure contains no axiom beyond the standard three and the named
native ones.

Bounded scratch (default): each statements file is prepared and compared on its own, and
its exports and compilation directory are deleted immediately (`--combined-statements`
compares all files against one combined export instead). Without `--statements`, every
file under replay/statements/ is compared. Every occurrence
of a duplicate reference is compared and retained in the receipt; one failure fails the
run. It cannot be combined with the read-only reference cache or --keep-exports.
`--l1-batch-size N` checks sequential groups of at most N roots with a fresh Nanoda per
group (and serial individual attribution on failure). `--max-export-mib N` adds a hard
export-file byte limit; root counts alone cannot bound a transitive dependency closure.
Neither mode reuses proof or comparison verdicts.

Tool binaries come from environment variables (REPLAY_EXPORTER, REPLAY_NANODA,
REPLAY_COMPARATOR), then `--tools-json` (the harness's jocelyn.proof-replay-tools.v1 file),
then replay/_tools/. See replay/TOOLS.md.
"""

from __future__ import annotations

import argparse
import concurrent.futures
import datetime as dt
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import threading
import time
from pathlib import Path

from reference_cache import ReferenceCache, ReferenceCacheError, validate_outputs

SCHEMA = "math-frontier.replay-receipt.v1"
STANDARD_AXIOMS = ["propext", "Classical.choice", "Quot.sound"]
NATIVE_RE = re.compile(r"\._native\.native_decide\.ax_")
# Kernel primitive roots, as in the Jocelyn harness's proof_replay.rs EXPORT_ROOTS and in the
# ComparatorWorker primitiveTargets. They are exported in every file, so a kernel extension
# (Nat/String literals) cannot silently change meaning.
EXPORT_ROOTS = [
    "Nat", "String", "String.mk", "Char", "Quot", "Quot.mk", "Quot.lift", "Quot.ind",
    "propext", "Quot.sound", "Classical.choice", "Nat.add", "Nat.sub", "Nat.mul", "Nat.pow",
    "Nat.gcd", "Nat.div", "Nat.mod", "Nat.beq", "Nat.ble", "Nat.land", "Nat.lor", "Nat.xor",
    "Nat.shiftLeft", "Nat.shiftRight", "String.ofList", "Char.ofNat", "List", "eagerReduce",
]
# 63 MiB, the harness's INDEPENDENT_KERNEL_STACK_BYTES. Nanoda recurses deeply.
NANODA_STACK_BYTES = 63 * 1024 * 1024
REPLAY_DIR = Path(__file__).resolve().parent
REPO = REPLAY_DIR.parent
LOG_LOCK = threading.Lock()


def log(msg: str) -> None:
    with LOG_LOCK:
        print(f"[replay {dt.datetime.now().strftime('%H:%M:%S')}] {msg}", file=sys.stderr, flush=True)


def sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def sha256_text(text: str) -> str:
    return hashlib.sha256(text.encode()).hexdigest()


def run(cmd, *, cwd=REPO, env=None, stdout_path=None, timeout=None, preexec=None):
    """Run a command. Returns (returncode, stdout_text_or_None, stderr_text, elapsed_s)."""
    t0 = time.monotonic()
    if stdout_path is not None:
        with open(stdout_path, "wb") as out:
            p = subprocess.run(cmd, cwd=cwd, env=env, stdout=out, stderr=subprocess.PIPE,
                               timeout=timeout, preexec_fn=preexec)
        stdout = None
    else:
        p = subprocess.run(cmd, cwd=cwd, env=env, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                           timeout=timeout, preexec_fn=preexec)
        stdout = p.stdout.decode(errors="replace")
    return p.returncode, stdout, p.stderr.decode(errors="replace"), time.monotonic() - t0


# ---------------------------------------------------------------------------------------
# Declaration list
# ---------------------------------------------------------------------------------------

def declarations_from_release_audit(path: Path) -> list[str]:
    names = []
    for line in path.read_text().splitlines():
        m = re.match(r"^\s*#print\s+axioms\s+(\S+)\s*$", line)
        if m:
            names.append(m.group(1))
    return names


def load_manifest(path: Path) -> dict:
    return json.loads(path.read_text())


def declarations_from_manifest(path: Path) -> list[str]:
    return [d["name"] for d in load_manifest(path)["declarations"]]


# ---------------------------------------------------------------------------------------
# Path redaction (receipts must not contain absolute user paths)
# ---------------------------------------------------------------------------------------

class Redactor:
    def __init__(self, work: Path, receipts: Path | None = None, tools_json: Path | None = None):
        self.pairs = [(str(work), "<work>"), (str(work.resolve()), "<work>"),
                      (str(REPO) + "/", ""), (str(REPO), "."),
                      (str(REPO.resolve()) + "/", ""), (str(REPO.resolve()), ".")]
        if receipts is not None:
            self.pairs += [(str(receipts), "<receipts>"), (str(receipts.resolve()), "<receipts>")]
        if tools_json is not None:
            name = f"<external>/{tools_json.name}"
            self.pairs += [(str(tools_json), name), (str(tools_json.resolve()), name)]
        home = os.path.expanduser("~")
        if home and home != "/":
            self.pairs.append((home, "~"))
        # longest first, so the work dir (possibly inside the repo) wins
        self.pairs.sort(key=lambda p: -len(p[0]))

    def text(self, s: str) -> str:
        for a, b in self.pairs:
            s = s.replace(a, b)
        return s

    def __call__(self, obj):
        if isinstance(obj, str):
            return self.text(obj)
        if isinstance(obj, list):
            return [self(x) for x in obj]
        if isinstance(obj, dict):
            return {self.text(k) if isinstance(k, str) else k: self(v) for k, v in obj.items()}
        if isinstance(obj, (set, frozenset)):
            return sorted(self(x) for x in obj)
        return obj


def display_path(p: Path) -> str:
    """Repository-relative path, or `<external>/<name>` outside the repository."""
    try:
        return str(p.resolve().relative_to(REPO.resolve()))
    except ValueError:
        return f"<external>/{p.name}"


# ---------------------------------------------------------------------------------------
# Tools
# ---------------------------------------------------------------------------------------

def resolve_tools(args) -> dict:
    lock = json.loads((REPLAY_DIR / "tools.lock.json").read_text())
    harness = {}
    if args.tools_json:
        harness = json.loads(Path(args.tools_json).read_text())
    tools = {}
    for key, env_var, harness_key, default in [
        ("exporter", "REPLAY_EXPORTER", "exporter", "lean4export"),
        ("kernel", "REPLAY_NANODA", "kernel", "bin/nanoda_bin"),
        ("comparator", "REPLAY_COMPARATOR", "comparator", "replay-comparator"),
    ]:
        path = os.environ.get(env_var)
        origin = f"env:{env_var}"
        if not path and harness_key in harness:
            path, origin = harness[harness_key]["path"], "tools-json"
        if not path:
            path, origin = str(REPLAY_DIR / "_tools" / default), "replay/_tools"
        p = Path(path)
        entry = {"path": str(p), "display_path": display_path(p), "origin": origin,
                 "source_repository": lock["tools"][key]["repository"],
                 "source_commit": lock["tools"][key]["commit"]}
        if p.is_file():
            entry["sha256"] = sha256_file(p)
            expected = harness.get(harness_key, {}).get("sha256")
            if expected and expected != entry["sha256"]:
                raise SystemExit(f"{key}: sha256 {entry['sha256']} != tools-json {expected}")
            if harness.get("source_commits", {}).get(harness_key) not in (None, entry["source_commit"]):
                raise SystemExit(f"{key}: tools-json source commit differs from tools.lock.json")
        else:
            entry["sha256"] = None
        tools[key] = entry
    return tools


# ---------------------------------------------------------------------------------------
# Export scanning (names + axiom/declaration records only)
# ---------------------------------------------------------------------------------------

DECL_PREFIXES = ('{"axiom":', '{"def":', '{"thm":', '{"opaque":', '{"quot":', '{"inductive":')


def scan_export(path: Path) -> dict:
    """Stream an lean4export 3.x ndjson file. Return its metadata, its declaration count and
    its axioms as raw (Nanoda-style) names. Expression and level lines are skipped unparsed."""
    names: dict[int, tuple[int, str]] = {0: (-1, "")}
    cache: dict[int, str] = {0: ""}

    def render(i: int) -> str:
        if i in cache:
            return cache[i]
        pre, comp = names[i]
        head = render(pre)
        s = comp if not head else head + "." + comp
        cache[i] = s
        return s

    meta = None
    axioms: list[str] = []
    declared: set[str] = set()
    lines = 0
    size = 0
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for raw in f:
            lines += 1
            size += len(raw)
            h.update(raw)
            if raw.startswith(b'{"in":'):
                obj = json.loads(raw)
                if "str" in obj:
                    names[obj["in"]] = (obj["str"]["pre"], obj["str"]["str"])
                else:
                    names[obj["in"]] = (obj["num"]["pre"], str(obj["num"]["i"]))
            elif raw.startswith(b'{"meta":'):
                meta = json.loads(raw)["meta"]
            elif raw.startswith(tuple(p.encode() for p in DECL_PREFIXES)):
                obj = json.loads(raw)
                (kind, body), = obj.items()
                if kind == "inductive":
                    for group in ("types", "ctors", "recs"):
                        for item in body[group]:
                            declared.add(render(item["name"]))
                else:
                    n = render(body["name"])
                    declared.add(n)
                    if kind == "axiom":
                        axioms.append(n)
    return {"meta": meta, "sha256": h.hexdigest(), "bytes": size, "lines": lines,
            "declarations": len(declared), "declared_names": declared, "axioms": sorted(axioms)}


# ---------------------------------------------------------------------------------------
# Stages
# ---------------------------------------------------------------------------------------

class Replay:
    def __init__(self, args):
        self.args = args
        self.work = Path(args.work_dir).resolve()
        self.reference_cache = None
        if args.reference_cache:
            validate_outputs(args.reference_cache, self.work, args.receipt_dir, args.receipt_name)
        self.work.mkdir(parents=True, exist_ok=True)
        self.tools = resolve_tools(args)
        self.runs: list[dict] = []
        self.runs_lock = threading.Lock()
        self.checked_names: set[str] = set()  # declarations in exports that Nanoda passed
        self.base_env = dict(os.environ)

    # -- environment -------------------------------------------------------------------
    def lake(self, *cmd, **kw):
        return run(["lake", "env", *cmd], **kw)

    def preflight(self) -> dict:
        info = {}
        rc, out, _, _ = run(["git", "rev-parse", "HEAD"])
        info["git_head"] = out.strip() if rc == 0 else None
        rc, out, _, _ = run(["git", "status", "--porcelain", "--untracked-files=no"])
        info["git_tracked_dirty"] = bool(out.strip()) if rc == 0 else None
        info["git_tracked_changes"] = [l[3:] for l in out.splitlines()] if rc == 0 else None
        rc, out, _, _ = run(["git", "status", "--porcelain"])
        info["git_untracked"] = [l[3:] for l in out.splitlines() if l.startswith("??")] if rc == 0 else None
        info["lean_toolchain"] = (REPO / "lean-toolchain").read_text().strip()
        manifest = json.loads((REPO / "lake-manifest.json").read_text())
        info["dependencies"] = {p["name"]: p["rev"] for p in manifest["packages"]}
        pk = REPO / ".lake" / "packages"
        linked = []
        if pk.is_symlink():
            linked.append(".lake/packages")
        if pk.exists():
            linked += [f".lake/packages/{c.name}" for c in sorted(pk.iterdir()) if c.is_symlink()]
        info["packages_symlinked"] = linked
        info["dependency_mode"] = "local-deps" if self.args.local_deps else "clean-clone"
        if linked and not self.args.local_deps:
            raise SystemExit(
                "clean-clone mode: " + ", ".join(linked) + " is a symbolic link, so the checked "
                "dependencies are not the ones a fresh clone fetches from lake-manifest.json. "
                "Use a clean clone (`lake exe cache get`), or pass --local-deps to accept the "
                "linked packages (recorded in the receipt).")
        # Revisions actually checked out under .lake/packages (clean or linked).
        checked_out = {}
        for name in info["dependencies"]:
            d = pk / name
            if d.exists():
                rc, out, _, _ = run(["git", "-C", str(d), "rev-parse", "HEAD"])
                checked_out[name] = out.strip() if rc == 0 else None
        info["dependencies_checked_out"] = checked_out
        info["dependencies_match_manifest"] = all(
            checked_out.get(k) == v for k, v in info["dependencies"].items())
        rc, out, err, _ = self.lake("lean", "--version")
        if rc != 0:
            raise SystemExit(f"lake env lean --version failed: {err}")
        info["lean_version"] = out.strip()
        rc, out, _, _ = self.lake("lean", "--githash")
        info["lean_githash"] = out.strip()
        info["labels"] = [x for x, bad in [("dirty", info["git_tracked_dirty"]),
                                           ("non-clean-deps", bool(linked)),
                                           ("deps-differ-from-manifest",
                                            not info["dependencies_match_manifest"])] if bad]
        return info

    def check_disk(self, what: str) -> None:
        free = shutil.disk_usage(self.work).free
        self.min_free_seen = min(getattr(self, "min_free_seen", free), free)
        if free < self.args.min_free_gib * 2**30:
            raise SystemExit(f"free disk {free / 2**30:.1f} GiB < --min-free-gib "
                             f"{self.args.min_free_gib} before {what}; aborting")

    def build(self) -> dict:
        # Module-by-module compilation (scripts/build.py), never `lake build`: with linked
        # dependency packages `lake build` can try to rebuild Mathlib in place.
        log("scripts/build.py (module by module)")
        logf = self.work / "build.log"
        rc, out, err, el = run([sys.executable, "scripts/build.py", "--no-record"], stdout_path=logf)
        text = logf.read_text(errors="replace")
        tail = text.splitlines()[-3:]
        warnings = sum(1 for l in text.splitlines() if "warning:" in l)
        errors = sum(1 for l in text.splitlines() if "error:" in l)
        if rc != 0:
            raise SystemExit(f"build failed ({rc}); see {logf}\n{err}")
        if warnings and not self.args.allow_warnings:
            raise SystemExit(f"build reported {warnings} warning line(s); see {logf}")
        return {"returncode": rc, "elapsed_s": round(el, 1), "warning_lines": warnings,
                "error_lines": errors, "log_tail": tail}

    # -- (a) Lean axiom audit ----------------------------------------------------------
    def audit(self, decls: list[str]) -> dict[str, dict]:
        log(f"Lean axiom audit of {len(decls)} declarations")
        names_file = self.work / "declarations.txt"
        names_file.write_text("\n".join(decls) + "\n")
        env = dict(self.base_env, REPLAY_DECLS_FILE=str(names_file))
        rc, out, err, el = self.lake("lean", str(REPLAY_DIR / "AuditRelease.lean"), env=env)
        (self.work / "audit.stdout").write_text(out)
        if rc != 0:
            raise SystemExit(f"axiom audit failed ({rc}):\n{out[-4000:]}\n{err[-4000:]}")
        rows = {}
        for line in out.splitlines():
            if line.startswith("REPLAY-AUDIT "):
                row = json.loads(line[len("REPLAY-AUDIT "):])
                rows[row["name"]] = row
        missing = [d for d in decls if d not in rows or not rows[d]["found"]]
        if missing:
            raise SystemExit(f"declarations not found in the built environment: {missing}")
        self.audit_elapsed = el
        return rows

    # -- (b) export --------------------------------------------------------------------
    def export(self, label: str, roots: list[str], module: str = "JocelynWorkspace",
               extra_lean_path: Path | None = None) -> dict:
        self.check_disk(f"export {label}")
        out = self.work / f"{label}.ndjson"
        env = dict(self.base_env)
        cmd = ["lake", "env"]
        if extra_lean_path is not None:
            # lake env overwrites LEAN_PATH, so extend it inside the lake environment.
            cmd += ["sh", "-c", 'LEAN_PATH="$0:$LEAN_PATH" exec "$@"', str(extra_lean_path)]
        cmd += [self.tools["exporter"]["path"], module, "--", *roots, *EXPORT_ROOTS]
        limit_mib = getattr(self.args, "max_export_mib", 0)
        if limit_mib:
            # Set the limit in a fresh Python process, not preexec_fn in a threaded
            # parent. RLIMIT_FSIZE is inherited across exec and enforced while the
            # exporter writes, rather than after a large file has filled the disk.
            cmd = [sys.executable, "-c",
                   "import os,resource,sys; n=int(sys.argv[1]); "
                   "resource.setrlimit(resource.RLIMIT_FSIZE,(n,n)); "
                   "os.execvp(sys.argv[2],sys.argv[2:])",
                   str(limit_mib * 2**20), *cmd]
        try:
            rc, _, err, el = run(cmd, env=env, stdout_path=out, timeout=self.args.export_timeout)
        except subprocess.TimeoutExpired:
            rc, err, el = -1, "timeout", float(self.args.export_timeout)
        rec = {"label": label, "module": module, "roots": roots, "returncode": rc,
               "elapsed_s": round(el, 2), "stderr_tail": err[-2000:], "path": str(out)}
        if limit_mib:
            rec["max_export_bytes"] = limit_mib * 2**20
            # Treat reaching the cap as failure even if an exporter exits zero.
            if out.stat().st_size >= limit_mib * 2**20:
                rec["error"] = "export_size_limit_reached"
                return rec
        if rc != 0:
            rec["error"] = "exporter_failed"
            return rec
        try:
            scan = scan_export(out)
        except (OSError, ValueError, KeyError, RecursionError) as error:
            rec["error"] = f"invalid_export:{error}"
            return rec
        rec.update({k: scan[k] for k in ("sha256", "bytes", "lines", "declarations", "axioms", "meta")})
        rec["_declared_names"] = scan["declared_names"]
        missing = [r for r in roots if r not in scan["declared_names"]]
        if missing:
            rec["error"] = f"roots_missing_from_export:{missing[:5]}"
        return rec

    # -- (c) Nanoda --------------------------------------------------------------------
    def nanoda(self, label: str, export_path: str, permitted: list[str]) -> dict:
        cfg = {
            "export_file_path": export_path,
            "use_stdin": False,
            "permitted_axioms": permitted,
            "unpermitted_axiom_hard_error": True,
            "unsafe_permit_all_axioms": False,
            "nat_extension": True,
            "string_extension": True,
            "num_threads": self.args.nanoda_threads,
            "pp_declars": [],
            "pp_to_stdout": True,
            "print_axioms": False,
            "print_success_message": True,
        }
        cfg_path = self.work / f"{label}.nanoda.json"
        cfg_path.write_text(json.dumps(cfg, indent=1))

        # `ulimit -s` sets soft and hard stack limits (KiB) for Nanoda only. Python's
        # resource.setrlimit rejects this value on macOS, so a shell is used instead.
        cmd = ["sh", "-c", f'ulimit -s {NANODA_STACK_BYTES // 1024} && exec "$0" "$@"',
               self.tools["kernel"]["path"], str(cfg_path)]
        try:
            rc, out, err, el = run(cmd, timeout=self.args.nanoda_timeout)
        except subprocess.TimeoutExpired:
            return {"label": label, "status": "timeout", "permitted_axioms": permitted,
                    "config_sha256": sha256_file(cfg_path)}
        m = re.fullmatch(r"Checked (\d+) declarations with no errors\n", out or "")
        return {"label": label, "status": "pass" if rc == 0 and m else "fail",
                "returncode": rc, "checked_declarations": int(m.group(1)) if m else None,
                "permitted_axioms": permitted, "num_threads": self.args.nanoda_threads,
                "stack_bytes": NANODA_STACK_BYTES, "elapsed_s": round(el, 2),
                "stdout_tail": (out or "")[-2000:], "stderr_tail": err[-2000:],
                "config_sha256": sha256_file(cfg_path)}

    # -- (d) Comparator ----------------------------------------------------------------
    def finish_export(self, rec: dict):
        rec.pop("_declared_names", None)
        if self.reference_cache and rec["path"] in self.reference_cache.protected:
            rec["preserved_read_only"] = True
            return
        if not self.args.keep_exports and os.path.exists(rec["path"]):
            os.remove(rec["path"])
            rec["deleted_after_check"] = True

    def prepare_statements(self, stmt_file: Path, idx: int) -> dict:
        """Compile one statements (challenge) file and export its theorems as reference."""
        if self.reference_cache and idx in self.reference_cache.records:
            log(f"reusing verified read-only reference {display_path(stmt_file)}")
            return self.reference_cache.records[idx]
        text = stmt_file.read_text()
        names = re.findall(r"^\s*(?:theorem|lemma)\s+([^\s:({\[]+)", text, flags=re.M)
        # Theorems are written with their full names inside the namespaces of the file.
        names = [self.qualify(text, n) for n in names]
        mod = f"ReplayStatements{idx}"
        sdir = self.work / f"statements-{idx}"
        if sdir.exists():
            shutil.rmtree(sdir)
        sdir.mkdir()
        olean = sdir / f"{mod}.olean"
        src = sdir / f"{mod}.lean"
        shutil.copyfile(stmt_file, src)
        log(f"compiling statements file {display_path(stmt_file)} ({len(names)} theorems)")
        rc, out, err, el = self.lake("lean", "-R", str(sdir), "-o", str(olean), str(src))
        rec = {"file": display_path(stmt_file), "sha256": sha256_file(stmt_file), "theorems": names,
               "compile_returncode": rc, "compile_elapsed_s": round(el, 2),
               "compile_output_tail": (out + err)[-3000:]}
        if rc != 0:
            rec["error"] = "statements_compile_failed"
            return rec
        if not names:
            rec["error"] = "statements_contain_no_theorems"
            return rec
        exp = self.export(f"reference-statements-{idx}", names, module=mod, extra_lean_path=sdir)
        exp.pop("_declared_names", None)
        rec["reference_export"] = exp
        if "error" in exp:
            rec["error"] = "reference_export_failed:" + exp["error"]
        return rec

    @staticmethod
    def qualify(text: str, short: str) -> str:
        """Full name of a theorem declared as `theorem short` in `text`: the innermost
        enclosing `namespace` blocks (tracked line by line) are prepended."""
        stack: list[str] = []
        for line in text.splitlines():
            m = re.match(r"^\s*namespace\s+(\S+)", line)
            if m:
                stack.append(m.group(1))
                continue
            m = re.match(r"^\s*end\s+(\S+)\s*$", line)
            if m and stack and stack[-1] == m.group(1):
                stack.pop()
                continue
            m = re.match(r"^\s*(?:theorem|lemma)\s+([^\s:({\[]+)", line)
            if m and m.group(1) == short:
                return ".".join(stack + [short]) if stack else short
        return short

    def comparator(self, name: str, reference: str, candidate: str, native: list[str]) -> dict:
        req = {"referenceExport": reference, "candidateExport": candidate, "theoremName": name,
               "memoryMiB": self.args.comparator_memory_mib}
        req_path = self.work / f"comparator-{sha256_text(name)[:16]}.json"
        req_path.write_text(json.dumps(req, indent=1))
        rc, out, err, el = run([self.tools["comparator"]["path"], str(req_path)],
                               timeout=self.args.comparator_timeout)
        res = {"returncode": rc, "elapsed_s": round(el, 2)}
        if rc == 0:
            try:
                diag = json.loads(out.strip().splitlines()[-1])
                res.update(status="match", diagnostics=diag)
            except (ValueError, IndexError):
                res.update(status="error", stdout_tail=out[-1000:])
            return res
        msg = (out + err).strip()
        res["message"] = msg[-1500:]
        m = re.search(r"Illegal axiom detected: '([^']*)'", msg)
        # The worker compares statements (Comparator.compareAt) before it audits axioms
        # (Comparator.checkAxioms), and it admits only the three standard axioms. An
        # "Illegal axiom" error on one of the declaration's own native_decide axioms therefore
        # means the statement matched, and the axiom audit stopped at a disclosed native axiom.
        shown = m.group(1).replace("«", "").replace("»", "") if m else ""
        if m and native and NATIVE_RE.search(shown):
            res["status"] = "match_native_axiom_outside_worker_policy"
            res["illegal_axiom"] = m.group(1)
            res["illegal_axiom_is_declared_native_axiom"] = any(
                shown == a or _display(a) == shown for a in native)
            if not res["illegal_axiom_is_declared_native_axiom"]:
                res["status"] = "error"
        elif "do not match" in msg or "don't match" in msg or "does not match" in msg:
            res["status"] = "mismatch"
        else:
            res["status"] = "error"
        return res


def _display(raw: str) -> str:
    """Approximate Lean's display of a macro-scoped raw name (the `✝` suffix form)."""
    if "._@." in raw:
        return raw.split("._@.")[0] + "✝"
    return raw


# ---------------------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------------------

def classify(row: dict) -> tuple[str, list[str], list[str]]:
    native = [a for a in row["axioms_raw"] if NATIVE_RE.search(a)]
    other = [a for a in row["axioms_raw"] if a not in STANDARD_AXIOMS and not NATIVE_RE.search(a)]
    level = "L1" if not native and not other else ("L2" if not other else "rejected")
    return level, native, other


def manifest_crosscheck(entry: dict | None, row: dict, level: str, native: list[str]) -> dict:
    """Compare one manifest entry with the Lean audit row. Returns {ok, mismatches}."""
    if entry is None:
        return {"ok": None, "mismatches": ["not_in_manifest"]}
    mism = []
    if entry.get("module") != row["module"]:
        mism.append("module")
    if entry.get("statement_sha256") != sha256_text(row["type_pp_all"]):
        mism.append("statement_sha256")
    if row.get("pp_truncated", True):
        mism.append("statement_rendering_truncated")
    if sorted(entry.get("axioms", [])) != sorted(row["axioms"]):
        mism.append("axioms")
    if sorted(entry.get("native_axioms", [])) != sorted(native):
        mism.append("native_axioms")
    lvl = entry.get("evidence_level")
    if (lvl == "lean_nanoda_with_named_native_decide") != (level == "L2"):
        mism.append("evidence_level")
    return {"ok": not mism, "mismatches": mism}


def statement_failed(rec: dict) -> bool:
    """A compiled challenge is unusable if its export failed, too."""
    return "error" in rec or "error" in rec.get("reference_export", {})


def comparison_passed(result: dict) -> bool:
    return (result.get("status") == "match" or
            (result.get("status") == "match_native_axiom_outside_worker_policy" and
             result.get("illegal_axiom_is_declared_native_axiom") is True))


def compare_streamed_statements(R, files: list[Path], decls: list[str], per: dict) -> list[dict]:
    """Fresh comparisons for every matching occurrence, with per-file scratch lifetime.

    A later duplicate never overwrites an earlier failure. Records contain every
    comparison, including errors from reference compilation/export and candidate export.
    The outer finally also cleans partial outputs if preparation raises or disk aborts.
    """
    statements = []
    selected = set(decls)
    for idx, file in enumerate(files):
        rec = {"file": display_path(file), "theorems": [], "comparisons": []}
        candidate = None
        reference = None
        try:
            try:
                rec = R.prepare_statements(file, idx)
                rec["comparisons"] = []
            except (OSError, ValueError, subprocess.SubprocessError) as error:
                rec["error"] = f"statements_preparation_failed:{error}"
            statements.append(rec)
            reference = rec.get("reference_export")
            if statement_failed(rec):
                rec.setdefault("error", "reference_export_failed:" +
                               rec.get("reference_export", {}).get("error", "unknown"))
            targets = [n for n in rec.get("theorems", []) if n in selected]
            if targets and not statement_failed(rec):
                label = f"comparator-candidates-{idx}"
                try:
                    candidate = R.export(label, list(dict.fromkeys(targets)))
                except (OSError, ValueError, subprocess.SubprocessError) as error:
                    candidate = {"label": label, "path": str(R.work / f"{label}.ndjson"),
                                 "error": f"candidate_export_failed:{error}"}
                R.runs.append({"label": label, "declarations": list(dict.fromkeys(targets)),
                               "export": candidate})
            for name in targets:
                if statement_failed(rec):
                    result = {"status": "error", "message": rec["error"]}
                elif candidate is None or "error" in candidate:
                    result = {"status": "error", "message": (candidate or {}).get(
                        "error", "candidate_export_missing")}
                else:
                    try:
                        log(f"comparator {name} (statements file {idx})")
                        result = R.comparator(name, reference["path"], candidate["path"],
                                              per[name]["native_axioms_raw"])
                    except (OSError, ValueError, subprocess.SubprocessError) as error:
                        result = {"status": "error", "message": f"comparator_failed:{error}"}
                verdict = {"file": rec["file"], "statement_file_index": idx,
                           "name": name, **result}
                rec["comparisons"].append(verdict)
                per[name].setdefault("comparator_comparisons", []).append(verdict)
                prior = per[name].get("comparator")
                if prior is None or comparison_passed(prior):
                    per[name]["comparator"] = dict(result)
        finally:
            if candidate is not None:
                R.finish_export(candidate)
            if reference is not None:
                R.finish_export(reference)
            # Includes incomplete exports not yet returned by prepare_statements.
            for label in (f"reference-statements-{idx}", f"comparator-candidates-{idx}"):
                path = R.work / f"{label}.ndjson"
                if path.exists():
                    path.unlink()
            scratch = R.work / f"statements-{idx}"
            if scratch.exists():
                shutil.rmtree(scratch)
            rec["stream_scratch_removed"] = True
    return statements


def check_standard_groups(R, names: list[str], per: dict, check_group) -> None:
    """Attribute each root to a fresh kernel run, keeping bounded mode serial."""
    size = getattr(R.args, "l1_batch_size", 0)
    batches = [names[i:i + size] for i in range(0, len(names), size)] if size else [names]
    for idx, batch in enumerate(batches):
        if not batch:
            continue
        label = f"standard-batch-{idx}" if size else "standard-combined"
        grp = check_group(label, batch, STANDARD_AXIOMS, False)
        R.runs.append(grp)
        if grp.get("nanoda", {}).get("status") == "pass":
            for name in batch:
                per[name]["nanoda_standard"] = {"status": "pass", "run": label}
                per[name]["nanoda_native"] = {"status": "not_applicable"}
            continue
        log(f"{label} did not pass; re-checking its declarations individually")

        def one(name):
            return name, check_group(f"standard-{sha256_text(name)[:12]}",
                                     [name], STANDARD_AXIOMS, False)

        # No parallel fallback can multiply the scratch footprint in batch mode.
        with concurrent.futures.ThreadPoolExecutor(1 if size else R.args.jobs) as executor:
            for name, group in executor.map(one, batch):
                R.runs.append(group)
                per[name]["nanoda_standard"] = {
                    "status": group.get("nanoda", {}).get("status", "export_failed"),
                    "run": group["label"]}
                per[name]["nanoda_native"] = {"status": "not_applicable"}


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    src = ap.add_mutually_exclusive_group()
    src.add_argument("--manifest", default=None,
                     help="release manifest (default release/manifest.json)")
    src.add_argument("--release-audit", default=None,
                     help="Lean file whose `#print axioms X` lines list the declarations")
    src.add_argument("--decls", help="text file, one declaration per line")
    ap.add_argument("--only", nargs="*", help="restrict to these declaration names")
    ap.add_argument("--local-deps", action="store_true",
                    help="accept a symlinked .lake/packages (recorded in the receipt as local-deps)")
    ap.add_argument("--tools-json", help="harness jocelyn.proof-replay-tools.v1 JSON with tool paths and sha256")
    ap.add_argument("--work-dir", default=str(REPLAY_DIR / "_work"))
    ap.add_argument("--receipt-dir", default=str(REPLAY_DIR / "receipts"))
    ap.add_argument("--receipt-name", default=None, help="receipt file name (default replay-<time>-<head>.json)")
    ap.add_argument("--statements", nargs="+",
                    help="Lean statements (challenge) files or directories of them for the Comparator check")
    ap.add_argument("--reference-cache",
                    help="read-only interrupted-run references bound to the committed preservation inventory")
    ap.add_argument("--stream-statements", action="store_true", default=True,
                    help="prepare, compare and remove one statements file at a time; no verdict "
                         "reuse (default)")
    ap.add_argument("--combined-statements", dest="stream_statements", action="store_false",
                    help="compare all statement files against one combined candidate export")
    ap.add_argument("--l1-batch-size", type=int, default=0,
                    help="maximum L1 roots per serial fresh-kernel export (0: combined default)")
    ap.add_argument("--max-export-mib", type=int, default=0,
                    help="hard export-file size cap in MiB (0: no cap; cap hit fails export)")
    ap.add_argument("--skip-build", action="store_true")
    ap.add_argument("--allow-warnings", action="store_true", help="do not fail on build warnings")
    ap.add_argument("--jobs", type=int, default=2, help="parallel per-declaration export+Nanoda jobs")
    ap.add_argument("--nanoda-threads", type=int, default=4)
    ap.add_argument("--nanoda-timeout", type=int, default=7200)
    ap.add_argument("--export-timeout", type=int, default=3600)
    ap.add_argument("--comparator-timeout", type=int, default=3600)
    ap.add_argument("--comparator-memory-mib", type=int, default=6144)
    ap.add_argument("--min-free-gib", type=float, default=6.0,
                    help="abort before an export when free disk is below this (default 6)")
    ap.add_argument("--keep-exports", action="store_true", help="keep .ndjson exports (they are large)")
    ap.add_argument("--no-standard-probe", action="store_true",
                    help="skip the expected-to-fail standard-axioms-only Nanoda run on L2 exports")
    args = ap.parse_args()
    if not args.statements and not args.reference_cache:
        # Default: every statement directory, so a plain run checks every declaration.
        args.statements = [str(p) for p in sorted((REPLAY_DIR / "statements").iterdir())
                           if p.is_dir() or p.suffix == ".lean"]
    if args.l1_batch_size < 0 or args.max_export_mib < 0:
        ap.error("--l1-batch-size and --max-export-mib must be nonnegative")
    if args.stream_statements and (args.reference_cache or args.keep_exports):
        args.stream_statements = False
    os.chdir(REPO)
    if args.reference_cache and not args.statements:
        ap.error("--reference-cache requires the full original --statements list")

    t_start = time.monotonic()
    started = dt.datetime.now(dt.timezone.utc).isoformat(timespec="seconds")
    manifest_path = Path(args.manifest) if args.manifest else REPO / "release" / "manifest.json"
    manifest = load_manifest(manifest_path) if manifest_path.exists() else None
    if args.decls:
        decls, decl_source = [l.strip() for l in Path(args.decls).read_text().splitlines() if l.strip()], args.decls
    elif args.release_audit:
        decls, decl_source = declarations_from_release_audit(Path(args.release_audit)), args.release_audit
    else:
        if manifest is None:
            raise SystemExit(f"{manifest_path} not found")
        decls, decl_source = [d["name"] for d in manifest["declarations"]], str(manifest_path)
    if args.only:
        decls = [d for d in decls if d in set(args.only)]
    dups = sorted({d for d in decls if decls.count(d) > 1})
    decls = list(dict.fromkeys(decls))
    by_name = {d["name"]: d for d in manifest["declarations"]} if manifest else {}

    R = Replay(args)
    redact = Redactor(R.work, Path(args.receipt_dir),
                      Path(args.tools_json) if args.tools_json else None)
    for k, t in R.tools.items():
        if t["sha256"] is None and (k != "comparator" or args.statements):
            raise SystemExit(f"tool {k} not found at {t['path']} (see replay/TOOLS.md)")
    pre = R.preflight()
    log(f"Lean {pre['lean_githash']}; dependency mode {pre['dependency_mode']}; labels={pre['labels']}")
    R.check_disk("start")
    files: list[Path] = []
    for a in args.statements or []:
        pa = Path(a).resolve()
        files += sorted(pa.glob("*.lean")) if pa.is_dir() else [pa]
    if args.statements and not files:
        ap.error("--statements did not select any Lean files")
    if args.reference_cache:
        if args.only or args.decls or args.release_audit or args.manifest:
            ap.error("--reference-cache requires the full default release manifest")
        try:
            R.reference_cache = ReferenceCache(
                args.reference_cache, REPO, files, pre, R.tools,
                scan_export=scan_export, sha256_file=sha256_file, qualify=R.qualify,
                export_roots=EXPORT_ROOTS, standard_axioms=STANDARD_AXIOMS)
        except (ReferenceCacheError, KeyError, OSError, ValueError, subprocess.CalledProcessError) as error:
            raise SystemExit(f"reference cache rejected: {error}") from error
        for cache_path in {str(Path(args.reference_cache).absolute()), str(Path(args.reference_cache).resolve())}:
            redact.pairs.insert(0, (cache_path, "<reference-cache>"))
        log(f"verified {len(R.reference_cache.records)} reusable references; no proof verdicts reused")
    build = None if args.skip_build else R.build()

    audit = R.audit(decls)
    per: dict[str, dict] = {}
    for d in decls:
        row = audit[d]
        level, native, other = classify(row)
        per[d] = {"name": d, "module": row["module"], "kind": row["kind"], "evidence_level": level,
                  "manifest_evidence_level": by_name.get(d, {}).get("evidence_level"),
                  "lean_axioms": row["axioms"], "lean_axioms_raw": row["axioms_raw"],
                  "native_axioms_raw": native, "other_axioms": other,
                  "statement_sha256": sha256_text(row["type_pp_all"]),
                  "statement_pp_sha256": sha256_text(row["type_pp"])}
        if manifest is not None:
            per[d]["manifest_check"] = manifest_crosscheck(by_name.get(d), row, level, native)
    (R.work / "audit.json").write_text(json.dumps(audit, indent=1))

    statements = None
    ref_of: dict[str, str] = {}
    if args.statements and not args.stream_statements:
        statements = [R.prepare_statements(f, i) for i, f in enumerate(files)]
        for rec in statements:
            ref = rec.get("reference_export", {})
            if "error" in rec or "error" in ref:
                continue
            for n in rec["theorems"]:
                ref_of[n] = ref["path"]
    stmt_names = {n for rec in (statements or []) for n in rec.get("theorems", [])}

    def check_group(label: str, names: list[str], permitted: list[str], probe_standard: bool) -> dict:
        log(f"export {label} ({len(names)} roots)")
        exp = R.export(label, names)
        run_rec = {"label": label, "declarations": names, "export": exp}
        if "error" in exp:
            R.finish_export(exp)
            return run_rec
        try:
            unexpected = [a for a in exp["axioms"] if a not in permitted]
            run_rec["export_axioms_outside_permitted"] = unexpected
            if probe_standard:
                log(f"nanoda {label} standard-only (expected to reject native axioms)")
                run_rec["nanoda_standard"] = R.nanoda(label + ".standard", exp["path"], STANDARD_AXIOMS)
            log(f"nanoda {label} permitted={len(permitted)} axioms")
            run_rec["nanoda"] = R.nanoda(label, exp["path"], permitted)
            if run_rec["nanoda"]["status"] == "pass" and unexpected:
                run_rec["nanoda"]["status"] = "export_axiom_policy_mismatch"
            if run_rec["nanoda"]["status"] == "pass":
                with R.runs_lock:
                    R.checked_names |= exp["_declared_names"]
            return run_rec
        finally:
            R.finish_export(exp)

    l1 = [d for d in decls if per[d]["evidence_level"] == "L1"]
    l2 = [d for d in decls if per[d]["evidence_level"] == "L2"]
    rejected = [d for d in decls if per[d]["evidence_level"] == "rejected"]
    passes = {}

    # Nanoda pass "standard": every declaration with standard axioms only, in one export.
    t0 = time.monotonic()
    check_standard_groups(R, l1, per, check_group)
    passes["standard"] = {"declarations": len(l1), "permitted_axioms": STANDARD_AXIOMS,
                          "elapsed_s": round(time.monotonic() - t0, 1)}

    # Nanoda pass "named-native": each declaration that uses native_decide, with exactly its
    # own named native_decide axioms permitted in addition to the standard three.
    t0 = time.monotonic()
    def one_l2(d):
        permitted = STANDARD_AXIOMS + per[d]["native_axioms_raw"]
        return d, check_group(f"native-{sha256_text(d)[:12]}", [d], permitted, not args.no_standard_probe)

    with concurrent.futures.ThreadPoolExecutor(args.jobs) as ex:
        for d, g in ex.map(one_l2, l2):
            R.runs.append(g)
            exp_native = sorted(a for a in g["export"].get("axioms", []) if a not in STANDARD_AXIOMS)
            per[d]["export_native_axioms_match_lean_audit"] = exp_native == sorted(per[d]["native_axioms_raw"])
            per[d]["nanoda_standard"] = ({"status": g["nanoda_standard"]["status"], "run": g["label"] + ".standard",
                                          "expected": "fail"} if "nanoda_standard" in g else {"status": "skipped"})
            per[d]["nanoda_native"] = {"status": g.get("nanoda", {}).get("status", "export_failed"),
                                       "run": g["label"], "permitted_native_axioms": len(per[d]["native_axioms_raw"])}
    passes["named_native"] = {"declarations": len(l2),
                              "status": "run" if l2 else "not_applicable_no_native_decide_declarations",
                              "elapsed_s": round(time.monotonic() - t0, 1)}
    for d in rejected:
        per[d]["nanoda_standard"] = per[d]["nanoda_native"] = {"status": "not_run_rejected_axioms"}

    # Comparator: one candidate export holding just the declarations that the statements file
    # restates. This keeps it small, because the worker parses the whole export per theorem.
    targets = [d for d in decls if d in ref_of]
    t0 = time.monotonic()
    if args.stream_statements:
        statements = compare_streamed_statements(R, files, decls, per)
        stmt_names = {n for rec in statements for n in rec.get("theorems", [])}
        targets = [d for d in decls if "comparator_comparisons" in per[d]]
    if R.reference_cache:
        R.reference_cache.verify_unchanged()
    if targets and not args.stream_statements:
        log(f"export comparator-candidates ({len(targets)} roots)")
        exp = R.export("comparator-candidates", targets)
        R.runs.append({"label": "comparator-candidates", "declarations": targets, "export": exp})
        for n in targets:
            if "error" in exp:
                per[n]["comparator"] = {"status": "error", "message": exp["error"]}
                continue
            log(f"comparator {n}")
            per[n]["comparator"] = R.comparator(n, ref_of[n], exp["path"], per[n]["native_axioms_raw"])
        R.finish_export(exp)
    for rec in statements or []:
        if rec.get("reference_export", {}).get("path"):
            R.finish_export(rec["reference_export"])
    if R.reference_cache:
        R.reference_cache.verify_unchanged()
    if statements is not None:
        passes["comparator"] = {"statement_files": len(statements), "theorems": len(targets),
                                "files_failed_to_compile": [r["file"] for r in statements
                                                            if r.get("error") == "statements_compile_failed"],
                                "statement_files_failed": [r["file"] for r in statements if statement_failed(r)],
                                "mode": "streaming" if args.stream_statements else "combined",
                                "comparison_occurrences": sum(len(per[d].get("comparator_comparisons", []))
                                                              for d in decls) if args.stream_statements else len(targets),
                                "elapsed_s": round(time.monotonic() - t0, 1)}

    # Summary
    def st(d, k):
        return per[d].get(k, {}).get("status")
    manifest_failures = [d for d in decls if per[d].get("manifest_check", {}).get("ok") is False]
    counts = {
        "declarations": len(decls),
        "duplicates_in_source": dups,
        "L1_standard_axioms_only": len(l1),
        "L2_named_native_axioms": len(l2),
        "rejected_other_axioms": len(rejected),
        "manifest_mismatches": {d: per[d]["manifest_check"]["mismatches"] for d in manifest_failures},
        "nanoda_pass_standard_only": sum(st(d, "nanoda_standard") == "pass" for d in decls),
        "nanoda_pass_with_named_native_axioms": sum(st(d, "nanoda_native") == "pass" for d in l2),
        "nanoda_standard_only_rejected_native_as_expected": sum(st(d, "nanoda_standard") == "fail" for d in l2),
        "failures": [d for d in decls if not (st(d, "nanoda_standard") == "pass" or
                                              (d in l2 and st(d, "nanoda_native") == "pass"))],
        "distinct_native_axioms": len({a for d in l2 for a in per[d]["native_axioms_raw"]}),
        "nanoda_runs": sum(1 for r in R.runs for k in ("nanoda", "nanoda_standard") if k in r),
        "nanoda_checked_declarations_total": sum(r[k].get("checked_declarations") or 0
                                                  for r in R.runs for k in ("nanoda",) if k in r),
        "nanoda_distinct_declarations_checked": len(R.checked_names),
        "export_bytes_total": sum(r["export"].get("bytes", 0) for r in R.runs),
        "export_bytes_max": max((r["export"].get("bytes", 0) for r in R.runs), default=0),
    }
    if statements is not None:
        cs = [per[d]["comparator"]["status"] for d in decls if "comparator" in per[d]]
        counts["comparator"] = {s: cs.count(s) for s in sorted(set(cs))}
        counts["comparator_failures"] = [d for d in decls if "comparator" in per[d]
                                         and not comparison_passed(per[d]["comparator"])]
        counts["comparator_statements_without_release_declaration"] = sorted(stmt_names - set(decls))
        counts["comparator_statement_files_failed"] = [r["file"] for r in statements if statement_failed(r)]

    elapsed = time.monotonic() - t_start
    tools = {k: {kk: vv for kk, vv in t.items() if kk != "path"} for k, t in R.tools.items()}
    receipt = {
        "schema": SCHEMA,
        "started_utc": started,
        "elapsed_s": round(elapsed, 1),
        "repository": pre,
        "declaration_source": decl_source,
        "manifest_sha256": sha256_file(manifest_path) if manifest is not None else None,
        "tools": tools,
        "driver": {"path": "replay/replay.py", "sha256": sha256_file(Path(__file__)),
                   "reference_cache_helper_sha256": sha256_file(REPLAY_DIR / "reference_cache.py"),
                   "audit_script_sha256": sha256_file(REPLAY_DIR / "AuditRelease.lean"),
                   "export_roots": EXPORT_ROOTS, "standard_axioms": STANDARD_AXIOMS,
                   "statement_mode": "streaming" if args.stream_statements else "combined",
                   "l1_batch_size": args.l1_batch_size,
                   "max_export_mib": args.max_export_mib,
                   "proof_verdicts_reused": False,
                   "argv": sys.argv[1:], "host": os.uname().sysname + "-" + os.uname().machine,
                   "min_free_disk_gib_seen": round(getattr(R, "min_free_seen", 0) / 2**30, 2)},
        "build": build,
        "lean_audit_elapsed_s": round(R.audit_elapsed, 1),
        "passes": passes,
        "counts": counts,
        "declarations": [per[d] for d in decls],
        "runs": R.runs,
        "statements": statements,
        "reference_cache": R.reference_cache.metadata if R.reference_cache else None,
    }
    receipt = redact(receipt)
    rdir = Path(args.receipt_dir)
    rdir.mkdir(parents=True, exist_ok=True)
    stamp = dt.datetime.now().strftime("%Y%m%dT%H%M%S")
    out = rdir / (args.receipt_name or f"replay-{stamp}-{(pre['git_head'] or 'nohead')[:8]}.json")
    text = json.dumps(receipt, indent=1, default=sorted) + "\n"
    leaks = [m for m in ("/Users/", "/home/", "/private/") if m in text]
    if leaks:
        log(f"warning: receipt still contains {leaks}; check redaction")
    out.write_text(text)
    log(f"receipt: {display_path(out)}")
    print(json.dumps({"receipt": display_path(out), **{k: v for k, v in counts.items()},
                      "elapsed_s": round(elapsed, 1)}, indent=1))
    bad = (counts["failures"] or rejected or counts.get("comparator_failures") or manifest_failures
           or counts.get("comparator_statement_files_failed"))
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
