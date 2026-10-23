# Admission checklist

A result enters this repository only when every item below is done and recorded
in its registry record (`registry/<id>.json`, field `admission`). Results are
admitted one at a time, each in its own commit. A record whose checklist is
incomplete has status `candidate` and is listed as such.

## 1. Statement

- The paper states the result exactly, with the hypotheses it uses.
- Each claimed statement has a Lean declaration, listed in `release/manifest.json`
  and in the record's `claims`.
- **Blind statement-faithfulness review.** A reviewer who has not read the paper
  translates each headline Lean statement into ordinary mathematics, then
  compares the translation with the paper. Any place where the paper claims more
  than the Lean statement proves blocks admission until either the paper or the
  Lean statement is corrected.

## 2. External inputs

- A result from the literature that is not proved in the repository enters the Lean
  statements only as a named premise, listed in the record's `hypotheses`.
- Each premise is compared with the source text itself (not a summary or a
  citation of it), and the record says what was compared, where in the source,
  and whether the Lean form is an instance, a weakening or a consequence of the
  source statement. A premise compared only with a restatement says so in
  `open`.
- A premise must not be stronger than what the source proves.

## 3. Proof

- `scripts/build.sh` compiles the library with no errors, warnings or `sorry`.
  It compiles module by module with `lake env lean`; `lake build` is not used.
- `scripts/audit.sh` passes: every declaration depends only on `propext`,
  `Classical.choice` and `Quot.sound`; its statement fingerprint, the sha256 of
  the complete `pp.all` rendering of its type, equals the manifest's; no
  rendering is truncated and no two declarations share a fingerprint.
  `scripts/test_fingerprint.py` passes.
- No `native_decide` and no added axioms.

## 4. Independent replay

- `scripts/replay.sh` (the sequence in the README) on a committed tree with no
  untracked files: Nanoda replays
  every declaration of the result with only the three standard axioms permitted,
  and Comparator matches each declaration against its independent statement file
  under `replay/statements/<id>/`.
- A negative control (a deliberately strengthened statement under
  `replay/negative-control/`) is rejected by Comparator.
- Both receipts are committed under `replay/receipts/` and named in the record.

## 5. Paper

- Written proofs of the new steps follow the routes of the Lean proofs; an
  appendix maps each statement to its Lean declarations.
- The written proofs and the appendix names are reviewed against the Lean
  sources by an independent reviewer.
- The verification section states what the kernel checks, which premises are
  assumed, and points to this repository's receipt.
- The disclosure states how the results were produced and that all reviews are
  AI reviews unless a human review is named.
- `scripts/build-paper.sh <id>` builds without layout warnings.

## 6. Registration

- `scripts/registry.py bind <id>` records the hashes of the result's Lean
  modules, dependency pins, statement files, manifest entries and verification
  tools, and refuses unless they are identical to the commit both receipts
  were produced at. A later change to any of them makes `scripts/registry.py check` fail
  until the result is replayed and bound again; documentation and the paper
  are not bound.
- The record's `status` becomes `admitted` and `scripts/registry.py check`
  passes; `scripts/registry.py generate` updates the table in `RESULTS.md`.
- Shipped files contain no chronology: no run or campaign names, no
  "previously" or "now", no dates of discovery. History lives in git.
- Only the strongest form of a result is registered. A stronger result replaces
  a weaker one; a dominated statement stays only as a lemma that a proof uses.
- Grades are stated exactly: numerical checks are labelled numerical, explicit
  results are labelled explicit where a non-explicit result covers more, and
  open items are listed in the record.
