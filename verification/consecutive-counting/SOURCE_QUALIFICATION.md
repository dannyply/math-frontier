# Named literature inputs

These predicates are explicit arguments of the Lean theorems. Independent source comparisons support their stated forms; the external theorems themselves are not proved inside Lean. Source hashes identify the exact inspected texts. All reviews are AI reviews.

Paper 1 uses Stewart, Castryck–Cluckers–Dittmann–Nguyen and Gelfond.

## Stewart's Thue bound

C. L. Stewart, JAMS4 (1991),793–835, Theorem1 p795 and consequence p796.

[Source](https://uwaterloo.ca/pure-mathematics/sites/default/files/uploads/documents/s0894-0347-1991-1119199-x_0.pdf). SHA-256: `8824ab3dbe963c8d070aad1f1d593ce6217fed686665ca99d422c192f0e9eba7`.

**Lean form:** StewartHyp: content-one squarefree homogeneous binary forms of degree q>=3; ordered primitive integer pairs, signed nonzero m, bound2800*q^(1+omega(|m|)).

**Comparison:** The p796 consequence uses g=|m| and counts coprime integer pairs of both signs. Content1 and squarefree homogeneous form give the nonzero discriminant condition in characteristic0. Reducible squarefree forms are included; omega counts distinct prime factors.

## Uniform affine-curve count

Castryck–Cluckers–Dittmann–Nguyen, arXiv1904.13109v1, Theorem3.

[Source](https://arxiv.org/html/1904.13109v1). SHA-256: `0ba5979ceec573318f7b4d43b8e6d70b23ae6224487b8657756500c98f5b3540`.

**Lean form:** CCDNThm3 in all natural ambient dimensions N>=2, positive degree d, integral affine curve represented by prime ideal and linear filtered Hilbert dimension.

**Comparison:** Quantifier order c=c(N), all degrees, B>=1, c*d^3*B^(1/d)*(log B+d); no extra smoothness or geometric irreducibility assumption.

## Gelfond factor-height inequality

Bombieri–Gubler, Heights in Diophantine Geometry, Cambridge2006, Lemma1.6.11, printed p27.

[Source](https://api.pageplace.de/preview/DT0400.9780511138096_A23689664/preview-9780511138096_A23689664.pdf). SHA-256: `91d2c7d2c97a02319d33d355185c7fe1d899813c2bea93835d8bc14ea94d238a`.

**Lean form:** GelfondHyp for every natural number n of variables; factor coefficients bounded by exp(c_n*totalDegree(F))*height(F).

**Comparison:** Apply product-height lower bound to G and its nonzero integral cofactor, whose coefficient norm is at least1. Sum of partial degrees <=n totalDegree(F); c_n=n log2 works. n=0 is the integer case.

## Logical scope

The predicates concern literature estimates rather than assume the counting conclusions. Their simultaneous satisfaction is supported by those source theorems and the documented conversions; no additional Lean axiom or formal proof of the literature predicates is introduced. The same exact premise subsets are used in the manuscript, registry and independent statement files.
