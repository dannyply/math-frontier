# Papers and their formal statements

**Paper 1, _Powerful values of quadratic polynomials_, is the standalone
manuscript for the polynomial-value results and their mixed-full applications.**
Paper 1 is the intended standalone deposit. Paper 0 is the published
powerful-product paper that supplies the counting framework.

The paper numbers are a reading guide, not versions of one paper. Paper 1
uses its own theorem numbering; the A-labels are stable identifiers in the shared
Lean interface. Its appendix supplies the correspondence.

| Paper | Manuscript | Claims | Evidence and publication status |
|---|---|---|---|
| 0 | [Counting powerful products of consecutive integers](papers/powerful-counting/main.pdf) | Theorems 1.1–1.3 and supporting release declarations | Admitted result; [published preprint](https://doi.org/10.5281/zenodo.23614742) |
| 1 | [Powerful values of quadratic polynomials](papers/powerful-polynomial-values/main.pdf) · [TeX](papers/powerful-polynomial-values/main.tex) | A1–A4, A11–A13 | Written manuscript with independent AI statement and proof-route reviews; admitted with integrated Lean/Comparator/Nanoda verification; no deposition asserted |

## Paper 1 and the role of Paper 0

Paper 0 turns arithmetic configurations into points on auxiliary curves, with
controlled degree, height and multiplicity. Paper 1 develops the arithmetic
reductions and component counts needed for polynomial values. For fixed
quadratics, A1 has exponent `293/1220+ε`. A2 treats the varying family `n²+a²`;
A3 gives a coefficient-uniform quadratic estimate with exponent `389/1600` and
absolute positive constants. A4 records supporting formalized cubic applications:
its general bound is derivable from classical estimates, and its cube-coefficient
case follows from A1. The [prior-art note](verification/consecutive-counting/prior-art.md)
separates these consequences from the quadratic improvements.

Paper 1 presents A1, A3 and A2 as Theorems 1.1, 1.2 and 1.3; A12 and A13
as Theorems 1.5 and 1.6. A11 is included in the positive-shift theorem.
Corollary 1.4 gives the general cubic estimate and the stronger written
cube-coefficient consequence of Theorem 1.1. That stronger consequence and
the explicit classical coefficient exponent 180 are proved in the paper,
but are not additional independently replayed declarations. The appendix
distinguishes them from the retained A4 interface.

The coefficient dependence in A3 is essential to A11–A13: it allows one to sum
bounds for varying quadratics inside mixed-full counting arguments. A13 also
uses Paper 0's width-three bound directly. A square substitution changes its
exponent `77/320` to `77/640`. [DISCOVERY.md](DISCOVERY.md) explains this
connection, including the differences between direct theorem reuse and an
extension of the method.

Paper 1 uses Stewart's Thue estimate, the
Castryck–Cluckers–Dittmann–Nguyen affine-curve estimate and Gelfond's
factor-height inequality as published theorems. In Lean they remain explicit
hypotheses in their stated formal forms. Its classical cubic argument also
uses Evertse–Silverman; the written quadratic-fibre estimate uses
Vaughan–Wooley. The formal development supplies that fibre estimate
by a direct Pell argument. Its mixed-full
applications retain their own orientation and shift restrictions: the
s-full member is counted, with positive shifts to the r-full member in A12
and the reverse neighbour in A13. They are not a theorem for every signed
shift in both orientations.

## Reading the verification status

The [Paper 0 registry](registry/powerful-counting.json) binds its admitted
claims to committed replay receipts. The [shared registry](registry/consecutive-counting.json)
maps claims to their Lean declarations and external premises. The
publication manifest selects 29 verification targets: 22 for Paper 0 and
seven for Paper 1. Each is covered by the bound receipts. The retained shared
replay checks 38 interfaces; its broader scope is preserved as recorded evidence.

The integrated build and axiom/type audit pass for the complete library. The
[release replay](replay/receipts/consecutive-counting.json) records standard-axiom
Nanoda verification and exact statement matches for all 38 targets. The
[negative control](replay/receipts/consecutive-counting-negative.json) records the
expected rejection of a deliberately false strengthening at the same clean
source commit. The registry binds each result to its checked sources and tools.

Paper 1 has independent AI statement and proof-route reviews,
including extracted proof chains and selected source checks. These are not a
line-by-line audit of every Lean proof body; no human mathematical review is
claimed. Named literature results remain explicit theorem premises.
Paper 1 also has a [bidirectional statement review](verification/consecutive-counting/bidirectional-review.json)
covering all 66 numbered items, its seven formal headline interfaces and the
three named literature predicates. The review distinguishes direct matches,
composed formal routes and written refinements.

## Citation and publication

| Object | Citation |
|---|---|
| Paper 0 | [BibTeX](papers/powerful-counting/citation.bib); DOI `10.5281/zenodo.23614742` |
| Paper 1 | [BibTeX](citations/powerful-polynomial-values.bib); unpublished manuscript, no paper DOI assigned here |
| Repository | [CITATION.cff](CITATION.cff); concept DOI `10.5281/zenodo.23614471` |

Paper 1 has a complete verification section and final PDF and can be
deposited separately. The Paper 0 DOI and repository concept DOI must not be
used as Paper 1's DOI.

For a Paper 1-only deposit, the manuscript, citation and any accompanying
source package should identify Paper 1 and its statement-to-formal-interface
mapping. Use a dedicated manuscript source package rather than a
whole-repository archive, whose contents have a broader scope. The manuscript
source package is separate from the shared Lean verification library and its
replay evidence.
No new DOI, release date or publication event is asserted by this guide.

Before deposit, record the full repository commit and the SHA-256 hashes of
the submitted PDF, TeX source and source archive. Check the verification
manifest and receipts at that commit, and identify any accompanying code
archive by its version-specific DOI; a moving branch or concept DOI is not
an exact version pin. Test the replay entry point from the extracted code
archive using its documented pinned dependencies. Keep that code package
distinct from the Paper 1-only manuscript package.
