# Registry record (`frontier.result.v1`)

One JSON file per result, `registry/<id>.json`. The core fields are the same in
every domain repository; each domain adds a section for its own evidence (here
`lean`).

| Field | Meaning |
|---|---|
| `schema` | `frontier.result.v1` |
| `id` | short formal-result identifier; manuscript directory names may differ |
| `domain` | `math` |
| `title`, `summary` | the result in one line and in one paragraph |
| `status` | `candidate` until every admission item is done, then `admitted` |
| `grade` | `lean` or `conditional-lean` |
| `grade_note` | what the grade covers for this result |
| `paper` | paths of the primary manuscript source, PDF, supplementary files and citation |
| `papers` (optional) | complete manuscript partition: each entry has `title`, `tex`, `pdf`, `citation`, `claims`; every claim label occurs exactly once, and the first entry matches `paper` |
| `papers[].listed` (optional) | boolean, default `true`; selects manuscripts for the reader-facing results index without changing admission or removing artifacts |
| `claims` | one entry per paper statement: `label`, `paper_ref`, human-readable `statement` summary, Lean `declarations`, `assumes` (hypothesis ids), `headline` |
| `hypotheses` | one entry per external premise: `source`, `lean_form`, `relation` (instance, weakening, consequence), `compared_against`, `comparison`, `reviewer`, and `open` if the source text itself was not compared |
| `lean` | statement-file directory, negative control, replay receipt and negative-control receipt |
| `admission` | one item per checklist section of `ADMISSION.md`, each with `status` and `note` |
| `evidence_binding` | written by `scripts/registry.py bind`: sha256 of the result's Lean modules, dependency pins, statement files, negative control and verification tools, and of its manifest entries |
| `open_items` | what remains open about the result or its evidence |
| `reviews` | who reviewed what; AI unless a human reviewer is named |

`scripts/registry.py check` validates the records against `release/manifest.json`,
the audit and the receipts; `scripts/registry.py generate` writes the table in `RESULTS.md`.

[PAPERS.md](../PAPERS.md) supplies the reader-facing map. A `papers` partition
requires all referenced artifacts to exist. It changes presentation, not proof
scope: all claims still belong to the same formal result and must satisfy its
admission requirements. The existence of a PDF does not certify manuscript
review or publication. A paper's
citation path may be under `citations/`; it need not be in the manuscript's
directory. A manifest entry or a successful candidate registry check does not
establish release replay or publication.

When `listed` is `false`, the generated results index omits that manuscript's
links and claims and computes its premise list from the selected claims only.
If only part of a result is listed, the index uses the selected manuscript
titles; if none is listed, it omits the row. Validation still checks every
claim and artifact, including unlisted ones. This flag controls navigation,
not file access, archive contents or publication status.

The `statement` field is a summary, not a substitute for the full Lean type.
The mapped declaration and independent statement file determine the exact
quantifiers, parameter domains, definitions and premise dependencies.
