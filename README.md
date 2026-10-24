# math-frontier

Can an AI research system built outside a lab, by one person, around models that
anyone can use, do real mathematical research? Not answer exam questions or
reproduce known proofs, but take an open problem, find its own way in, and come
back with something new that holds up to scrutiny?

This repository is an attempt to answer that question with evidence rather than
claims. Every result in it was obtained by running [Jocelyn](JOCELYN.md), an
independently developed agentic research harness, on a mathematical problem. I
chose the problem and set the objective of each research run; AI assistants
turned my instructions into the run's brief, including what was already known.
The harness did the mathematics: the ideas, the proofs and
their formal verification. I used AI coding assistants to help write up and
check the results; [who did what](#who-did-what) says exactly how.

## Why

There are many AI research systems, built by frontier labs and by open projects
alike. What is still scarce is evidence: results that are new, that hold up
when checked, and whose making is documented well enough to be judged. Without
that, it is hard to tell what any of these systems can really do, or whether
serious research with AI needs the resources of a large lab.

This repository is my contribution to that evidence. Jocelyn was built by one
person, on models anyone can subscribe to, with open tools: Lean, Mathlib and
standard computer algebra. Each result here is checked by machines rather than
taken on trust, so it can be judged on its merits. If results like these hold
up, they support a simple claim: with careful orchestration and strict
standards of evidence, real progress on hard questions is within reach of
ordinary people, not only of large labs.

Jocelyn is a starting point, not the end goal, and systems like it are the
least capable they will ever be: the models improve, and so can the
orchestration around them. If it holds up, later versions of it could let
anyone take on the research that matters most to them, instead of waiting for
it to become someone else's priority. Its code is not public yet, because
it is not ready for others to use. I have chosen to let the results come
first: if they hold up, they make the case for the work of turning the harness
into something anyone can pick up.

## What makes a result count

Saying that an AI "proved something" is cheap. For a result to be included here,
three things have to hold.

**It is correct, and checked by machines rather than taken on trust.** Every
theorem is proved in [Lean](https://lean-lang.org), a proof assistant whose
kernel checks each logical step. The proofs are then replayed by a second,
independently written kernel, and each formal statement is compared, symbol by
symbol, with a copy written separately from the proof. Where a result rests on a
theorem from the literature, that theorem appears as an explicit, named
assumption and is checked against the source text.

**It says what the paper says.** A reviewer that has not seen the paper
translates each formal statement back into ordinary mathematics, and the
translation is compared with the paper. Any gap between what the paper claims
and what Lean proves is fixed before the result is admitted.

**It is new and worth having.** Each result improves on what was known, as far
as a literature search can establish, and the paper says exactly which earlier
results it builds on and improves.

The full checklist is in [ADMISSION.md](ADMISSION.md).

## The results

**Counting powerful products of consecutive integers.** A number is *powerful*
if every prime that divides it does so at least twice, as in 72 = 2³·3². Erdős
asked whether a product of three or more consecutive integers can ever be
powerful; nobody knows. This paper asks how often it can happen. For pairs of
consecutive powerful numbers it lowers the best exponent we know of from
Reuss's 29/100 to 1/4. For products of three or more consecutive integers it gives the
bound x^(77/320+ε), below what follows from earlier work, and the same bound
uniformly over all widths. The new step bounds the points on the auxiliary
curves of Heath-Brown's determinant method using the
Castryck–Cluckers–Dittmann–Nguyen bound for integral points on curves.
[Paper](papers/powerful-counting/main.pdf) ·
[record](registry/powerful-counting.json)

[RESULTS.md](RESULTS.md) lists every result with its exact statements and assumptions.

## What is and is not claimed

- The formal proofs are checked by two independent kernels. A reader still has
  to trust two things: that each formal statement says what its English version
  says, which is reviewed but cannot be machine-checked, and the theorems from
  the literature that a result assumes, which are named and compared with their
  sources.
- All reviews are by AI systems. No human mathematician has reviewed these
  results.
- Novelty rests on literature searches and is not certified. If you know of
  earlier work that anticipates a result here, that is exactly the kind of
  correction this repository wants.
- These are contributions to open problems, not solutions of them.

## Layout

| Path | Contents |
|---|---|
| `RESULTS.md` | every admitted result with its exact statements and assumptions |
| `papers/<id>/` | the paper, its PDF, citation and supplementary scripts |
| `registry/` | one record per result: claims, Lean declarations, assumptions and how each was checked |
| `JocelynWorkspace/` | Lean sources |
| `release/manifest.json` | every formal statement with its hash, axioms and evidence level |
| `replay/` | independent statement files, negative controls, replay tooling and receipts |
| `audit/` | build record and axiom audit |

## Reproducing the checks

Lean 4.33.1 with Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`
(`lean-toolchain`, `lake-manifest.json`). From a fresh clone:

```sh
lake exe cache get                    # Mathlib's prebuilt files for the pinned commit
scripts/build.sh --no-record          # compile module by module; fails on any warning
scripts/audit.sh                      # axioms and full statement fingerprints against the manifest
python3 scripts/test_fingerprint.py   # changing an exponent changes the fingerprint
python3 scripts/registry.py check     # committed receipts, fingerprints and evidence binding
```

`--no-record` leaves the tracked build record `audit/build.json` untouched, so
the tree stays as committed. The independent replay needs three tools built
once, as described in [replay/TOOLS.md](replay/TOOLS.md). It writes its
receipts outside the repository, so that both runs start from the committed
tree:

```sh
R=$(mktemp -d)
scripts/replay.sh --skip-build --receipt-dir "$R" --receipt-name powerful-counting.json
scripts/replay.sh --skip-build --receipt-dir "$R" \
  --only JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.Erdos137Final.counting_thm_k3 \
  --statements replay/negative-control/CountingNegativeControl.lean \
  --receipt-name powerful-counting-negative.json   # must fail with a Comparator mismatch
```

To register a replay, copy both receipts into `replay/receipts/`, then run
`python3 scripts/registry.py bind <id>`; it refuses unless every bound source
is identical to the commit both receipts were produced at. The replay never
runs `lake build`; without `--skip-build` it compiles with `scripts/build.py`.
The exact-arithmetic certificates are reproduced by
`python3 certificates.py && python3 endpoint_cert.py` in
`papers/powerful-counting/supplementary/`, and the paper by
`scripts/build-paper.sh powerful-counting`.

## License and citation

Code, Lean sources and scripts: Apache License 2.0 ([LICENSE](LICENSE)). Papers and
documentation: CC BY 4.0 ([LICENSE-papers.md](LICENSE-papers.md)). To cite the
repository or a paper, see [CITATION.cff](CITATION.cff) and each paper's
`citation.bib`.

## Who did what

The results and their proofs, written and formal, were produced by AI systems
working in the Jocelyn harness. Much of the writing up and checking was done
with AI coding assistants from several providers, which I operated outside the
harness:
revising the paper, the reviews of the written proofs and of the formal
statements, the corrections that followed, and packaging the proofs for this
repository, including the independent replay. I built the harness, chose the
problems, set the objectives of each research run, decided what is admitted
here and take responsibility for it. [JOCELYN.md](JOCELYN.md)
describes the harness.
