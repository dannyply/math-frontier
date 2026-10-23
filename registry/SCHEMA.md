# Registry record (`frontier.result.v1`)

One JSON file per result, `registry/<id>.json`. The core fields are the same in
every domain repository; each domain adds a section for its own evidence (here
`lean`).

| Field | Meaning |
|---|---|
| `schema` | `frontier.result.v1` |
| `id` | short identifier; also names the paper directory and statement directory |
| `domain` | `math` |
| `title`, `summary` | the result in one line and in one paragraph |
| `status` | `candidate` until every admission item is done, then `admitted` |
| `grade` | `lean` or `conditional-lean` |
| `grade_note` | what the grade covers for this result |
| `paper` | paths of the paper source, PDF, supplementary files and citation |
| `claims` | one entry per paper statement: `label`, `paper_ref`, `statement`, Lean `declarations`, `assumes` (hypothesis ids), `headline` |
| `hypotheses` | one entry per external premise: `source`, `lean_form`, `relation` (instance, weakening, consequence), `compared_against`, `comparison`, `reviewer`, and `open` if the source text itself was not compared |
| `lean` | statement-file directory, negative control, replay receipt and negative-control receipt |
| `admission` | one item per checklist section of `ADMISSION.md`, each with `status` and `note` |
| `evidence_binding` | written by `scripts/registry.py bind`: sha256 of the result's Lean modules, dependency pins, statement files, negative control and verification tools, and of its manifest entries |
| `open_items` | what remains open about the result or its evidence |
| `reviews` | who reviewed what; AI unless a human reviewer is named |

`scripts/registry.py check` validates the records against `release/manifest.json`,
the audit and the receipts; `scripts/registry.py generate` writes the table in `RESULTS.md`.
