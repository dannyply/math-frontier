# Jocelyn

Jocelyn is a research harness: software that turns general-purpose AI models
into a working research team. I developed it independently, outside
any lab, around commercially available models. Jocelyn is not
a model itself. It decides how models work together, what tools they use, how
long they work, and above all what counts as a result.

## Why it exists

Language models can write convincing mathematics, and convincing is not the
same as correct. A model will state a lemma that is false, cite a theorem that
says something else, or announce a proof with a gap in the middle. Used alone, a
model is a source of ideas and drafts, not of results.

Jocelyn is built on the opposite assumption from a chat window: nothing a model
says is taken as true. Ideas are cheap and plentiful; what the harness has to
supply is the discipline that turns some of them into knowledge. The question
behind it is whether that discipline, built by one person around tools that
anyone can use, is enough for authentic research. The README explains why that
question matters and why the results come before the harness itself is
released.

## How a research run works

**A brief, not a recipe.** I choose a problem and give my instructions, and an
AI assistant turns them into a brief in the structure Jocelyn works from: the
objective, what is already known (the exact frontier, including approaches that
have failed), and the facts the run may rely on. The brief says what to achieve,
never how. The method is the harness's to find.

**A team, not a single agent.** A lead agent reads the brief, forms a plan and
directs helper agents that pursue different lines of attack in parallel:
searching the literature, running computations, attempting proofs, formalizing
arguments, and reviewing each other's work. Runs last hours, within budgets of
time, compute and tool use that the harness enforces. Models from several
providers can take part.

**Tools that check rather than persuade.** The agents work with the tools a
mathematician would want, used in ways that produce checkable output:

- the Lean proof assistant with the Mathlib library, for formal proofs;
- exact arithmetic and computer algebra, for computations whose results are
  certificates rather than impressions;
- literature search with access to source texts, so that cited theorems are
  read rather than recalled;
- separate compute for long calculations.

**Evidence levels instead of confidence.** Every claim the team makes is
recorded with how it is supported: a model's proposal, a computation, a written
proof reviewed by another agent, or a Lean proof checked by the kernel. A claim
becomes *established* only when it passes the checks for its level; a Lean
proof, for example, must compile with no gaps and no added axioms and survive an
independent replay. Discovery and acceptance are deliberately separate, so an
agent's enthusiasm cannot promote its own work.

**Memory of what failed.** Dead ends are recorded as carefully as successes.
Later runs on the same problem start from the established frontier and know
which routes have already been closed, and why.

**A person in the loop, on the record.** I can send guidance while a run is
under way, for example to redirect effort or to supply a
source the agents could not reach. That guidance is part of the run's record.

## From a run to a result

A run ends with a ledger of established claims, open leads and closed routes.
Turning that into a result someone else can rely on is a separate step, which I
do with AI agents, including AI coding assistants that work outside the
harness: writing the paper, reviewing the written proofs against the
Lean proofs, checking each external theorem against its source, and checking
that each formal statement says what the paper says. In this repository a
result is admitted only after that work and an independent replay of every
proof; [ADMISSION.md](ADMISSION.md) gives the checklist.

## What Jocelyn is not

- **Not autonomous in choosing what matters.** I choose the problems, set
  each run's objective and decide what is published.
- **Not a substitute for human review.** The checks above establish that formal
  proofs are correct and that statements match. They do not replace the
  judgement of mathematicians about significance and novelty, and no human
  mathematician has reviewed the results published here.
- **Not limited to mathematics.** The same harness is used on problems in other
  fields. Results from other domains are published in their own repositories,
  with checks suited to their kind of evidence.
