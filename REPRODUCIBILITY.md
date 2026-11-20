# Reproducing the mathematics and verification

The repository contains admitted results for Papers 0 and 1. Consult
[RESULTS.md](RESULTS.md) and the registry records before interpreting a check:
a successful compilation is not an independent kernel replay, and an existing
Paper 0 receipt does not cover Paper 1's claims.

Paper 1's appendix maps its theorem numbers to A1–A4 and A11–A13 and
distinguishes written cubic deductions from the exact replayed statements.
The [bidirectional review](verification/consecutive-counting/bidirectional-review.json)
records the English-to-Lean and Lean-to-English correspondence, including
supporting statements whose written scope exceeds a particular formal interface.
The commands below check the shared library, whose receipt also covers other
results. A Paper 1 manuscript source package reproduces the typeset paper,
not the Lean replay. A whole-repository archive has a broader scope than a
Paper 1-only deposit. See
[publication scope](PAPERS.md#citation-and-publication).

## Library and statement audit

Use a Git checkout at the exact release tag or commit. The admission check
compares the source bytes with the original replay commits and therefore
requires Git history. GitHub source ZIP/TAR downloads omit that history;
restore it from the corresponding repository before running the registry
check. The source archive alone still supplies the mathematical files and
replay tools.

The pins are Lean 4.33.1 and Mathlib commit
`0df444a360eaa60ab8c11dca51a86af692955474`, recorded in
`lean-toolchain` and `lake-manifest.json`.

```sh
lake exe cache get
scripts/build.sh --no-record
scripts/audit.sh
python3 scripts/test_fingerprint.py
python3 scripts/registry.py check
python3 scripts/registry.py generate --check
```

Run the module build serially at the script's reduced process priority. It
rejects errors, warnings and proof holes. `--no-record` preserves the tracked
build receipt. The audit regenerates `audit/axioms.json`; check
`git status --short` before replay and resolve any differing audit in the
committed tree. `--no-record` alone does not ensure that the whole command
sequence leaves a clean tree. The axiom audit checks complete type fingerprints and permits
only `propext`, `Classical.choice` and `Quot.sound`; named literature results
remain theorem hypotheses, not added axioms. A candidate registry check
validates structure and referenced files; it does not report admission.

## Independent replay

Build or supply the pinned exporter, Nanoda kernel and Comparator as described
in [replay/TOOLS.md](replay/TOOLS.md). Comparator is required for repository
admission even though the generic driver can run without it. Use a clean,
committed source tree and put output receipts outside that tree:

```sh
R=$(mktemp -d)
scripts/replay.sh --skip-build --jobs 1 --nanoda-threads 1 \
  --max-export-mib 4096 --receipt-dir "$R" --receipt-name consecutive-counting.json
scripts/replay.sh --skip-build --jobs 1 --nanoda-threads 1 --max-export-mib 4096 \
  --receipt-dir "$R" \
  --only JocelynWorkspace.Formalization.PowerfulCounting.ConsecutiveCounting.A13 \
  --statements replay/negative-control/ConsecutiveCountingNegative.lean \
  --receipt-name consecutive-counting-negative.json
```

The first command covers the 29 selected manifest declarations and their
dependency closures. The committed shared receipt records a broader 38-interface
check at its recorded source commit; each selected declaration and all bound
proof files are unchanged. The independent statement file retains its full
checked contents; the driver compares the declarations selected by the manifest. The second must reject the deliberately false strengthening of
A13 with a Comparator mismatch. A nonzero exit for a missing dependency,
resource limit or failed compilation is not a successful negative control.
The committed receipts use this serial, streamed statement-comparison mode
with pinned local dependencies. The release target selects the formal
interfaces used by the two listed papers; verification does not assert publication.

For the Paper 0 negative control, select
`JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.Erdos137Final.counting_thm_k3`
and use `replay/negative-control/CountingNegativeControl.lean`.
Locally linked pinned dependency caches require `--local-deps`, which is
recorded in the receipt. Reference exports, candidate exports and scratch
space all require disk headroom; `--max-export-mib` bounds an export, not the
whole working set. Keep the driver's disk guard enabled.

After both appropriate runs, copy the receipts into `replay/receipts/` and use
`python3 scripts/registry.py bind <result-id>`. Binding requires the checked
source files to agree with the receipt commits. An admitted record additionally
requires every admission item, including manuscript reviews, to be complete.

### Counting paper — v1.0.1

The counting release v1.0.1 passes a fresh rebuild and independent Nanoda replay:
all 31 project modules compile without warnings, all 22 release declarations
pass, and all 22 statement comparisons match. A negative control correctly
rejects an altered statement. The accompanying
[AI source audit](verification/powerful-counting/source-audit.json) found no
mismatch in the six external literature premises and records the source-access
qualifications.

The [replay receipt](replay/receipts/powerful-counting-clean.json) and
[negative-control receipt](replay/receipts/powerful-counting-clean-negative.json)
verify counting release commit `171d380dab8481b9a5b412e0991c7374b94f8b7f`.
The [verification setup](verification/powerful-counting/replay-context.json)
records the project rebuild using private copies of pinned dependency caches;
Mathlib and the other dependency libraries were not rebuilt from source.

## Papers

```sh
scripts/build-paper.sh powerful-counting
scripts/build-paper.sh powerful-polynomial-values
```

Each command builds the named TeX source using cached Tectonic resources and
writes `build/papers/<id>/main.pdf`. It does not replace the supplied PDF in
`papers/<id>/`. If resources are absent, `--allow-downloads` enables resource
retrieval. A successful typeset build does not certify the mathematical text
or change the verification status. The main manuscript references are
listed in [PAPERS.md](PAPERS.md).

## Exact arithmetic supplements

Paper 0 supplies its certificates under
[papers/powerful-counting/supplementary](papers/powerful-counting/supplementary/README).
Run `certificates.py` and `endpoint_cert.py` there to reproduce the recorded
exact calculations.
