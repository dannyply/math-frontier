"""Read-only reuse of references bound to the committed interrupted-run inventory.

This does not cache proof verdicts. All candidate exports, Nanoda checks and
comparisons still run. Invalid requested reuse raises before any fresh export.
"""
from __future__ import annotations

import copy
import hashlib
import json
import re
import subprocess
from pathlib import Path


class ReferenceCacheError(ValueError):
    pass


def require(condition, message):
    if not condition:
        raise ReferenceCacheError(message)


def disjoint_outputs(cache: Path, outputs):
    cache = cache.resolve()
    for output in outputs:
        output = Path(output).resolve()
        require(not (output.is_relative_to(cache) or cache.is_relative_to(output)),
                f"reference cache overlaps output directory: {output}")


def validate_outputs(cache, work, receipts, receipt_name):
    disjoint_outputs(Path(cache), [work, receipts])
    if receipt_name is not None:
        require(receipt_name not in ("", ".", "..") and Path(receipt_name).name == receipt_name,
                "cache-mode receipt name must be a simple file name")
    for output in (work, receipts):
        output = Path(output)
        require(not output.exists() or (output.is_dir() and not any(output.iterdir())),
                f"cache-mode output directory must be new or empty: {output}")


# This is an approval for one concrete integration, not a general cache migration.
# Changing these anchors requires another reviewed contract amendment.
APPEND_ONLY_SCOPE = {
    "cache_source_commit": "727cf863a8a2b1b444941be98eaabd5efb76c6fa",
    "baseline_commit": "811d55a82e3de308e8a6634ffbcc5cbc885279d6",
    "baseline_manifest_sha256": "f122f59dea19ef82986974b5c2e6065cc56ebbcff9eac234d90967eb5b57cea4",
    "expansion_commit": "cab4018bd8705b064022ee8ed61b7752cca92ca3",
    "expansion_manifest_sha256": "49565953c729bd75a0b0a5e9dc0e6bfe76c0f86af635b3b2c3f0beb2caa05f7e",
    "old_declarations": 228,
    "added_declarations": 4,
    "old_definitions": 7,
    "old_reference_files": 39,
}
BUILD_INPUTS = ("lean-toolchain", "lake-manifest.json", "lakefile.toml", "lakefile.lean")


def approved_append_only_scope(repo, source, manifest_bytes, *, git, blob):
    """Accept only the byte-bound, explicitly approved four-result extension."""
    scope = APPEND_ONLY_SCOPE
    require(source == scope["cache_source_commit"],
            "manifest differs from interrupted run outside approved append-only source")
    base, expanded = scope["baseline_commit"], scope["expansion_commit"]
    for older, newer in ((source, base), (base, expanded), (expanded, "HEAD")):
        git("merge-base", "--is-ancestor", older, newer)
    old_bytes = blob(base, "release/manifest.json")
    new_bytes = blob(expanded, "release/manifest.json")
    require(hashlib.sha256(old_bytes).hexdigest() == scope["baseline_manifest_sha256"],
            "approved baseline manifest binding changed")
    require(hashlib.sha256(new_bytes).hexdigest() == scope["expansion_manifest_sha256"]
            and manifest_bytes == new_bytes,
            "manifest differs from approved append-only snapshot")
    old, new = json.loads(old_bytes), json.loads(new_bytes)
    n, extra = scope["old_declarations"], scope["added_declarations"]
    require(len(old["declarations"]) == n and len(new["declarations"]) == n + extra
            and new["declarations"][:n] == old["declarations"],
            "old declaration metadata changed or declaration scope is not append-only")
    require(len(old["definitions"]) == scope["old_definitions"]
            and new["definitions"] == old["definitions"], "old definition metadata changed")
    names = [d["name"] for d in new["declarations"]]
    require(len(set(names)) == len(names), "duplicate declaration in append-only scope")
    # The baseline's only changes since the cache producer were evidence/docs.
    require(not git("diff", "--name-only", source, base, "--", "*.lean", *BUILD_INPUTS).strip(),
            "original Lean sources or build inputs changed at append-only baseline")
    # Compare the working tree as well as HEAD; a stale caller's preflight is insufficient.
    require(not git("diff", "--name-only", expanded, "--", "*.lean", *BUILD_INPUTS).strip(),
            "Lean sources or build inputs differ from approved append-only snapshot")
    registry_path = "release/latest-formal-support.json"
    registry_bytes = blob(expanded, registry_path)
    require((repo / registry_path).read_bytes() == registry_bytes,
            "append-only endpoint registry changed")
    registry = json.loads(registry_bytes)
    claims = registry["claims"]
    require(registry["base_commit"] == base and len(claims) == extra
            and [d["name"] for d in new["declarations"][n:]] == [c["name"] for c in claims],
            "append-only registry does not match declaration suffix")
    statement_paths = [c["statement_file"] for c in claims]
    source_paths = [c["source_path"] for c in claims]
    require(len(set(statement_paths)) == extra and len(set(source_paths)) == extra,
            "duplicate append-only source or statement path")
    additions = source_paths + statement_paths + [
        "JocelynWorkspace/Formalization/Latest.lean", "replay/LatestFormalSupportStatementAudit.lean"]
    require(len(set(additions)) == 2 * extra + 2, "overlapping append-only source paths")
    for path in additions:
        require(not Path(path).is_absolute() and ".." not in Path(path).parts
                and path.endswith(".lean"), "invalid append-only source path")
    expected = {p: "A" for p in additions}
    expected.update({"JocelynWorkspace/Formalization.lean": "M", "ReleaseAudit.lean": "M"})
    changes = git("diff", "--no-renames", "--name-status", base, expanded,
                  "--", "*.lean", *BUILD_INPUTS).decode().splitlines()
    actual = {line.split("\t")[1]: line.split("\t")[0] for line in changes}
    require(actual == expected and len(actual) == len(changes),
            "approved expansion contains unexpected Lean or build-input changes")
    importer = "JocelynWorkspace/Formalization.lean"
    require(blob(expanded, importer) == blob(base, importer)
            + b"import JocelynWorkspace.Formalization.Latest\n",
            "original importer was changed rather than appended")
    require(blob(expanded, "ReleaseAudit.lean") == blob(base, "ReleaseAudit.lean")
            + "".join(f"#print axioms {c['name']}\n" for c in claims).encode(),
            "original axiom audit was changed rather than appended")
    require(blob(expanded, "JocelynWorkspace/Formalization/Latest.lean")
            == "".join(f"import {c['module']}\n" for c in claims).encode(),
            "new importer differs from the exact endpoint scope")
    for claim in claims:
        require(hashlib.sha256(blob(expanded, claim["source_path"])).hexdigest()
                == claim["integrated_source_sha256"], "integrated endpoint source binding changed")
    # Preserve the cache producer's status record and the successful earlier replay evidence.
    provenance = ["release/formal-support-replay-status.json",
                  "release/formal-support-replay-completion.json",
                  "replay/receipts/release-curated.json", "replay/receipts/negative-control-curated.json"]
    for path in provenance:
        require((repo / path).read_bytes() == blob(expanded, path),
                f"append-only provenance changed: {path}")
    return {
        "contract": "approved-append-only-232-v1",
        **scope,
        "registry_sha256": hashlib.sha256(registry_bytes).hexdigest(),
        "appended_statement_files": statement_paths,
        "original_declaration_metadata_preserved": n,
        "original_definitions_preserved": scope["old_definitions"],
        "original_lean_changes": "only exact importer and generated-audit appends",
    }


# Separate approval for the exact three-result successor. The original 232
# contract is deliberately unchanged and remains independently testable.
SUCCESSOR_SCOPE = {
    "expansion_commit": "2fe8f288ff15a8aa1b2ebcb2a5281fa64bf70433",
    "expansion_manifest_sha256": "4479831dd1802f491c97742c5907f473f15f991ba5e86caa6047145b15128b18",
    "promoted_commit": "f30cc76989f5a4dcba7b5b29fa040fad51d96978",
    "promoted_manifest_sha256": "88d70ddaef397eb75d4ca909f1579c762894077baa0a26c50551cb450f144451",
    "latest_registry_sha256": "39771037ae8c2e2defe9aeffa46ce08d106d03ad653fc3a82d738f84c577a625",
    "successor_registry_sha256": "eabb51bde02b5cf649aa009232d790e79cbe61f50df937d12d8119b3e02129ae",
    "added_declarations": 3,
}


def approved_successor_scope(repo, source, manifest_bytes, *, git, blob):
    """Validate both exact integrations, never a general append-only exemption."""
    old_scope, scope = APPEND_ONLY_SCOPE, SUCCESSOR_SCOPE
    require(source == old_scope["cache_source_commit"], "unapproved successor cache source")
    base, first = old_scope["baseline_commit"], old_scope["expansion_commit"]
    promoted, final = scope["promoted_commit"], scope["expansion_commit"]
    for older, newer in ((source, base), (base, first), (first, promoted),
                         (promoted, final), (final, "HEAD")):
        git("merge-base", "--is-ancestor", older, newer)
    manifests = []
    for commit, digest in ((base, old_scope["baseline_manifest_sha256"]),
                           (first, old_scope["expansion_manifest_sha256"]),
                           (promoted, scope["promoted_manifest_sha256"]),
                           (final, scope["expansion_manifest_sha256"])):
        data = blob(commit, "release/manifest.json")
        require(hashlib.sha256(data).hexdigest() == digest, "successor manifest snapshot binding changed")
        manifests.append(json.loads(data))
    require(manifest_bytes == blob(final, "release/manifest.json"),
            "manifest differs from approved successor snapshot")
    original, pending, prior, current = manifests
    n, a, b = old_scope["old_declarations"], old_scope["added_declarations"], scope["added_declarations"]
    require([len(m["declarations"]) for m in manifests] == [n, n+a, n+a, n+a+b]
            and all(m["declarations"][:n] == original["declarations"] for m in manifests)
            and current["declarations"][:n+a] == prior["declarations"],
            "original declaration metadata changed or successor is not append-only")
    require(len(original["definitions"]) == old_scope["old_definitions"]
            and all(m["definitions"] == original["definitions"] for m in manifests),
            "original definition metadata changed")
    names = [d["name"] for d in current["declarations"]]
    require(len(names) == len(set(names)), "duplicate successor declaration")
    require(not git("diff", "--name-only", source, base, "--", "*.lean", *BUILD_INPUTS).strip(),
            "original Lean sources or build inputs changed at baseline")
    require(not git("diff", "--name-only", final, "--", "*.lean", *BUILD_INPUTS).strip(),
            "Lean sources or build inputs differ from approved successor snapshot")
    latest_path, successor_path = "release/latest-formal-support.json", "release/successor-formal-support.json"
    registries = []
    for path, digest in ((latest_path, scope["latest_registry_sha256"]),
                         (successor_path, scope["successor_registry_sha256"])):
        data = blob(final, path)
        require(hashlib.sha256(data).hexdigest() == digest and (repo / path).read_bytes() == data,
                "successor endpoint registry binding changed")
        registries.append(json.loads(data))
    first_registry = json.loads(blob(first, latest_path))
    latest, successor = registries
    require(first_registry["base_commit"] == base and len(first_registry["claims"]) == a
            and len(latest["claims"]) == a and len(successor["claims"]) == b,
            "successor registry counts or original baseline changed")
    # Only the already completed four-result replay grade changed in its registry.
    for before, after in zip(first_registry["claims"], latest["claims"]):
        require({k:v for k,v in before.items() if k != "release_replay"}
                == {k:v for k,v in after.items() if k != "release_replay"},
                "prior endpoint identity or source binding changed")
    require([d["name"] for d in pending["declarations"][n:]]
            == [c["name"] for c in first_registry["claims"]]
            == [d["name"] for d in prior["declarations"][n:]]
            and names[n:] == [c["name"] for c in latest["claims"] + successor["claims"]],
            "successor registry does not match exact declaration suffix")
    appended = []
    all_paths = set()
    for older, newer, claims, label in ((base, first, first_registry["claims"], "Latest"),
                                       (first, final, successor["claims"], "Successor")):
        sources = [c["source_path"] for c in claims]
        statements = [c["statement_file"] for c in claims]
        additions = sources + statements + [f"JocelynWorkspace/Formalization/{label}.lean",
                                             f"replay/{label}FormalSupportStatementAudit.lean"]
        require(len(set(additions)) == len(additions) and not all_paths.intersection(additions),
                "duplicate successor source or statement path")
        all_paths.update(additions)
        for path in additions:
            require(not Path(path).is_absolute() and ".." not in Path(path).parts
                    and path.endswith(".lean"), "invalid successor source path")
        expected = {p: "A" for p in additions}
        expected.update({"JocelynWorkspace/Formalization.lean": "M", "ReleaseAudit.lean": "M"})
        changes = git("diff", "--no-renames", "--name-status", older, newer,
                      "--", "*.lean", *BUILD_INPUTS).decode().splitlines()
        actual = {line.split("\t")[1]: line.split("\t")[0] for line in changes}
        require(actual == expected and len(actual) == len(changes),
                "successor contains unexpected Lean or build-input changes")
        importer = "JocelynWorkspace/Formalization.lean"
        require(blob(newer, importer) == blob(older, importer)
                + f"import JocelynWorkspace.Formalization.{label}\n".encode(),
                "original importer changed rather than exact append")
        require(blob(newer, "ReleaseAudit.lean") == blob(older, "ReleaseAudit.lean")
                + "".join(f"#print axioms {c['name']}\n" for c in claims).encode(),
                "original axiom audit changed rather than exact append")
        require(blob(newer, f"JocelynWorkspace/Formalization/{label}.lean")
                == "".join(f"import {c['module']}\n" for c in claims).encode(),
                "successor importer differs from exact endpoint scope")
        for claim in claims:
            require(hashlib.sha256(blob(newer, claim["source_path"])).hexdigest()
                    == claim["integrated_source_sha256"], "successor integrated source binding changed")
        appended.extend(statements)
    provenance = ["release/formal-support-replay-status.json",
                  "release/formal-support-replay-completion.json",
                  "replay/receipts/release-curated.json", "replay/receipts/negative-control-curated.json"]
    for path in provenance:
        require((repo / path).read_bytes() == blob(first, path) == blob(final, path),
                f"successor historical provenance changed: {path}")
    for path in ("release/latest-formal-support-replay-completion.json",
                 "replay/receipts/release-latest-formal-support.json",
                 "replay/receipts/negative-control-latest-formal-support.json"):
        require((repo / path).read_bytes() == blob(promoted, path) == blob(final, path),
                f"successor prior replay provenance changed: {path}")
    return {"contract": "approved-append-only-235-v1", **old_scope,
            "successor_scope": dict(scope), "appended_statement_files": appended,
            "original_declaration_metadata_preserved": n,
            "prior_declaration_metadata_preserved": n+a,
            "original_definitions_preserved": old_scope["old_definitions"],
            "original_lean_changes": "only exact Latest and Successor importer/audit appends"}


class ReferenceCache:
    def __init__(self, root, repo, files, preflight, tools, *, scan_export,
                 sha256_file, qualify, export_roots, standard_axioms):
        self.root, self.repo = Path(root).resolve(), Path(repo).resolve()
        self.sha = sha256_file
        self.records = {}
        self.protected = set()
        self.bindings = {}

        def git(*args):
            return subprocess.check_output(["git", *args], cwd=self.repo)

        def blob(commit, path):
            return git("show", f"{commit}:{path}")

        def load(path):
            return json.loads(path.read_text())

        def bound_file(relative, digest):
            path = self.root / relative
            require(path.resolve().is_relative_to(self.root) and not path.is_symlink(),
                    f"cache path escapes its root: {relative}")
            require(path.is_file() and self.sha(path) == digest,
                    f"cache file hash mismatch or missing: {relative}")
            return path

        require(not preflight["git_tracked_dirty"] and not preflight["git_untracked"],
                "reference reuse requires a clean repository")
        require(preflight["dependencies_match_manifest"], "dependency pins do not match")
        status_path = self.repo / "release/formal-support-replay-status.json"
        status = load(status_path)
        require(status["schema"] == "erdos137.formal-support-replay-status.v1",
                "unsupported cache status schema")
        source = status["source_commit"]
        require(re.fullmatch(r"[0-9a-f]{40}", source), "invalid cache source commit")
        require(hashlib.sha256(blob(source, "replay/replay.py")).hexdigest()
                == status["driver_sha256"], "producer driver binding changed")
        manifest_bytes = (self.repo / "release/manifest.json").read_bytes()
        append_only = None
        if hashlib.sha256(manifest_bytes).hexdigest() != status["manifest_sha256"]:
            validator = (approved_successor_scope if hashlib.sha256(manifest_bytes).hexdigest()
                         == SUCCESSOR_SCOPE["expansion_manifest_sha256"] else approved_append_only_scope)
            append_only = validator(self.repo, source, manifest_bytes, git=git, blob=blob)
        else:
            changed = git("diff", "--name-only", source, "HEAD", "--", "*.lean", *BUILD_INPUTS)
            require(not changed.strip(), "Lean sources or build inputs changed since cached run")

        inventory_path = bound_file("preserved-artifacts.json", status["preservation_inventory"]["sha256"])
        inventory = load(inventory_path)
        require(inventory["schema"] == "curated-replay-preserved-artifacts.v1",
                "unsupported inventory schema")
        require(source.startswith(inventory["source_commit"]), "inventory source mismatch")
        entries = {item["path"]: item for item in inventory["files"]}
        require(len(entries) == len(inventory["files"]) == status["preservation_inventory"]["files"],
                "inventory has duplicate or missing entries")
        statements_path = bound_file("statements.json", entries["statements.json"]["sha256"])
        ordered = load(statements_path)
        actual = [str(Path(f).resolve().relative_to(self.repo)) for f in files]
        expected = ordered + (append_only["appended_statement_files"] if append_only else [])
        require(actual == expected and len(set(actual)) == len(actual)
                and len(ordered) == status["reference_files_total"],
                "statement file order or scope differs from cached run and approved suffix")
        if append_only:
            require(len(ordered) == append_only["old_reference_files"],
                    "original statement file count differs from approved scope")

        receipt_path = self.repo / "replay/receipts/release.json"
        receipt = load(receipt_path)
        require(receipt_path.read_bytes() == blob(source, "replay/receipts/release.json"),
                "historical receipt differs from preserved source")
        require(receipt["schema"] == "erdos137.replay-receipt.v1", "unknown historical receipt schema")
        old = receipt["repository"]
        require(not old["git_tracked_dirty"], "historical receipt had dirty sources")
        require(receipt["driver"]["export_roots"] == export_roots
                and receipt["driver"]["standard_axioms"] == standard_axioms,
                "primitive roots or axiom policy changed")
        require(receipt["driver"]["sha256"] == status["driver_sha256"],
                "historical exporter driver differs")
        for field in ("lean_githash", "lean_toolchain", "dependencies", "dependencies_checked_out"):
            require(preflight[field] == old[field], f"historical environment mismatch: {field}")
        for key in ("exporter", "kernel", "comparator"):
            require(tools[key]["sha256"] == receipt["tools"][key]["sha256"]
                    and tools[key]["source_commit"] == receipt["tools"][key]["source_commit"],
                    f"historical tool mismatch: {key}")
        for name in preflight["dependencies"]:
            # A matching commit alone does not bind a locally edited dependency.
            dirty = subprocess.check_output(["git", "status", "--porcelain", "--untracked-files=all"],
                                            cwd=self.repo / ".lake/packages" / name)
            require(not dirty.strip(), f"dependency has local changes: {name}")

        checked_imports = set()

        def check_imports(text):
            for line in re.findall(r"^(?:public\s+)?import\s+(.+)$", text, re.M):
                for module in line.split("--", 1)[0].split():
                    if not module.startswith("JocelynWorkspace") or module in checked_imports:
                        continue
                    checked_imports.add(module)
                    path = module.replace(".", "/") + ".lean"
                    current = (self.repo / path).read_bytes()
                    require(current == blob(old["git_head"], path), f"historical import changed: {module}")
                    check_imports(current.decode())

        historical = {item["file"]: item for item in receipt["statements"]}
        require(len(historical) == len(receipt["statements"]), "duplicate historical reference files")
        count = status["completed_reference_exports"]
        require(0 < count < len(ordered), "invalid completed-reference count")
        require(ordered[count] == status["interrupted_reference_file"], "interrupted-file boundary mismatch")
        for index, filename in enumerate(ordered[:count]):
            prior = historical[filename]
            exp = prior["reference_export"]
            require(prior["compile_returncode"] == 0 and not prior.get("error")
                    and exp["returncode"] == 0 and not exp.get("error"),
                    f"reference lacks successful historical compile/export: {filename}")
            text = (self.repo / filename).read_text()
            require(self.sha(self.repo / filename) == prior["sha256"], f"statement source changed: {filename}")
            saved = f"work/statements-{index}/ReplayStatements{index}.lean"
            source_path = bound_file(saved, entries[saved]["sha256"])
            require(source_path.read_bytes() == (self.repo / filename).read_bytes(),
                    f"saved statement source differs: {filename}")
            check_imports(text)
            names = [qualify(text, n) for n in re.findall(r"^\s*(?:theorem|lemma)\s+([^\s:({\[]+)", text, re.M)]
            require(names == prior["theorems"] == exp["roots"], f"reference roots changed: {filename}")
            require(exp["module"] == f"ReplayStatements{index}", f"reference module/index changed: {filename}")
            rel = f"work/reference-statements-{index}.ndjson"
            path = bound_file(rel, entries[rel]["sha256"])
            require(path.stat().st_size == entries[rel]["bytes"] == exp["bytes"] > 0
                    and entries[rel]["sha256"] == exp["sha256"], f"historical export identity mismatch: {filename}")
            scan = scan_export(path)
            require(all(scan[k] == exp[k] for k in ("sha256", "bytes", "lines", "declarations", "axioms", "meta")),
                    f"reference scan differs from historical receipt: {filename}")
            require(set(names + export_roots) <= scan["declared_names"], f"reference is missing roots: {filename}")
            require(scan["meta"]["lean"]["githash"] == preflight["lean_githash"], "export Lean version mismatch")
            record = copy.deepcopy(prior)
            record.update(compile_elapsed_s=0, compile_output_tail="", compile_origin="historical_successful_receipt")
            record["reference_export"].pop("deleted_after_check", None)
            record["reference_export"].update(path=str(path), elapsed_s=0, reused_read_only=True)
            record["reference_reuse"] = {"source_commit": source, "historical_source_commit": old["git_head"],
                                         "historical_receipt_sha256": self.sha(receipt_path),
                                         "historical_compile_elapsed_s": prior["compile_elapsed_s"],
                                         "historical_export_elapsed_s": exp["elapsed_s"]}
            self.records[index] = record
            self.protected.add(str(path))
            self.bindings[path] = exp["sha256"]
        self.metadata = {"source_commit": source, "historical_source_commit": old["git_head"],
                         "inventory_sha256": self.sha(inventory_path), "historical_receipt_sha256": self.sha(receipt_path),
                         "references_reused": len(self.records), "proof_verdicts_reused": 0,
                         "historical_repo_imports_checked": len(checked_imports)}
        if append_only:
            self.metadata["append_only_scope"] = append_only

    def verify_unchanged(self):
        for path, digest in self.bindings.items():
            require(not path.is_symlink() and path.resolve().is_relative_to(self.root)
                    and path.is_file() and self.sha(path) == digest,
                    f"cached reference changed during replay: {path.name}")
