# math-frontier

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.23614471.svg)](https://doi.org/10.5281/zenodo.23614471)

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
standard computer algebra. Each admitted result here is checked by machines rather than
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

Saying that an AI "proved something" is cheap. For a result to be admitted here,
three things have to hold.

**It is correct, and checked by machines rather than taken on trust.** Every
admitted theorem is proved in [Lean](https://lean-lang.org), a proof assistant whose
kernel checks each logical step. The proofs are then replayed by a second,
independently written kernel, and each formal statement is compared, symbol by
symbol, with a copy written separately from the proof. Where a result rests on a
theorem from the literature, that theorem appears as an explicit, named
assumption and is checked against the source text.

**It says what the paper says.** A reviewer that has not seen the paper
translates each formal statement back into ordinary mathematics, and the
translation is compared with the paper. Any gap between what the paper claims
and what Lean proves is fixed before the result is admitted.

**It is new and worth having.** Each paper identifies its advances against the
literature and distinguishes them from supporting lemmas, known consequences
and formalized applications. Novelty is assessed by a documented search.

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
[DOI 10.5281/zenodo.23614742](https://doi.org/10.5281/zenodo.23614742) ·
[record](registry/powerful-counting.json)

**Powerful values of quadratic polynomials.** How often does a quadratic
polynomial take a powerful value? Building on the counting framework above,
this paper gives the bound x^(293/1220+ε) for integral quadratics with positive
leading coefficient and nonsquare discriminant. It also makes the estimates
uniform as the coefficients vary, allowing them to be used inside other
proofs and yielding new bounds for pairs of numbers with prescribed prime
multiplicities. The counting framework becomes a tool for further discovery.
[Paper 1, manuscript v1.0.1](papers/powerful-polynomial-values/main.pdf) ·
[Zenodo v1.0.0](https://doi.org/10.5281/zenodo.24292371) ·
[record](registry/consecutive-counting.json) ·
[connection to the counting paper](DISCOVERY.md)

Papers 0 and 1 are published preprints with admitted formal interfaces. [PAPERS.md](PAPERS.md) gives the scope and status of Papers 0 and 1;
[RESULTS.md](RESULTS.md) lists the claims, assumptions and formal statements.

## What is and is not claimed

- The admitted formal proofs are checked by two independent kernels. A reader still has
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
| `RESULTS.md` | admitted results, assumptions and formal statements |
| `PAPERS.md` | Paper 0 and standalone Paper 1 |
| `DISCOVERY.md` | how the powerful-product framework supports further results |
| `REPRODUCIBILITY.md` | build, audit, replay and paper reproduction instructions |
| `papers/<id>/` | manuscript source, supplied PDF and paper-specific supplementary files |
| `citations/` | paper-specific citation records |
| `registry/` | one record per result: claims, Lean declarations, assumptions and how each was checked |
| `JocelynWorkspace/` | Lean sources; admission status is determined by the registry |
| `release/manifest.json` | verification targets and statement fingerprints; presence alone is not admission |
| `replay/` | independent statement files, negative controls, replay tooling and receipts |
| `audit/` | build record and axiom audit |

## Reproducing the checks

[REPRODUCIBILITY.md](REPRODUCIBILITY.md) gives the pinned dependencies and commands
for building the Lean proofs, auditing assumptions, replaying the statements in
an independent kernel, running negative controls and rebuilding the papers.

## License and citation

Code, Lean sources and scripts: Apache License 2.0 ([LICENSE](LICENSE)). Papers and
documentation: CC BY 4.0 ([LICENSE-papers.md](LICENSE-papers.md)). To cite the
repository or a paper, see [CITATION.cff](CITATION.cff) and the
[paper-specific citation records](PAPERS.md#citation-and-publication).

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
