# Prior art for the quadratic-value paper

This note distinguishes the contributions in **Powerful values of quadratic
polynomials** from consequences of existing results. It is a written comparison
with independent AI checks of the derived implications. It is not a new Lean
verification, a human review, or an exhaustive certification of novelty.
The formal declarations retain their named Stewart, Castryck–Cluckers–Dittmann–Nguyen
and Gelfond premises. The comparison deductions below are not additional admitted
Lean results.

The labels A1–A4 and A11–A13 below identify the retained formal interfaces.
Paper 1 uses conventional theorem numbering, with the correspondence in its
appendix. Its cubic corollary states the stronger written cube-coefficient
consequence derived below; that statement is distinguished from the weaker
formal A4(ii) interface.

## Verdicts and scope

| Claim | Verdict against the literature checked |
|---|---|
| A1: fixed integral quadratic, positive leading coefficient, nonsquare discriminant; exponent `293/1220+ε` | **STANDS.** Smaller than the checked general `2/5+ε` comparator and the published `29/100+ε` for `n²+a²`. No stronger nonconjectural bound was located. |
| A2: growing `a` in `n²+a²` | **STANDS with its stated range.** Improves `29/100` for `0≤κ<289/1050`; agrees at the endpoint. Its uniform range is shorter than the comparator's `κ≤29/100`. |
| A3: `K L^ν N^(389/1600)` with absolute `K,ν` | **NARROWED positioning.** The combination of the exponent and polynomial coefficient dependence is distinct; polynomial dependence alone follows from classical inputs at exponent `2/5+ε`. |
| A4(i): `Cε A^B T^(3/5+ε)` | **Known consequence / formalized application.** The bound follows from Evertse–Silverman and elementary field estimates, with a coarse absolute `B=180`. This precise corollary is derived here, not attributed verbatim to that paper. |
| A4(ii): cube coefficient | **DOMINATED internally.** A stronger bound follows from A1 by a fixed-quadratic substitution, without A3's coefficient uniformity. |
| A11 | **Supporting specialization.** Follows from the positive-shift theorem A12 with `h=1`; not an independent advance. |
| A12–A13 | **STAND in the qualified cases.** The novelty claim is restricted to `(r,s)=(2,6),(3,6),(2,8),(3,8),(4,8)`, for which the literature search found no prior bound stronger than `Y^(1/s)`. Positive shifts in A12 and the reverse neighbour in A13 retain their exact orientation: the s-full member is the bounded variable. Other displayed pairs illustrate the coefficient-uniform quadratic estimate; no best-known bound is claimed for them. |
| Method | **Extension and combination.** Determinant methods, quadratic norm decompositions, Thue estimates and curve-point estimates are established tools. Novelty is not claimed for their invention or for every intermediate lemma. No claim of a uniquely new general method is certified by this audit. |

The seven formal labels are not seven independent discoveries. A1, A2 and A3
have different uniformity/range content; A11 and A4 supply supporting interfaces.
The collection's formal correctness and its novelty are separate questions.

## Exact comparisons

Put `α=293/1220` and `β=389/1600`. Then
`α=0.2401639344…`, `β=0.243125`, and `β−α=289/97600`.
For a fixed quadratic, A1 is stronger than A3 after choosing a sufficiently
small ε; it does not control A1's constants as the coefficients vary.

| κ | Θ(κ) | `29/100−Θ(κ)` |
|---|---|---|
| 0 | 293/1220 | 76/1525 |
| 1/28 | 137/560 | 127/2800 |
| 19/73 | 104/365 | 37/7300 |
| 289/1050 | 29/100 | 0 |

The branches meet at the two internal breakpoints and are increasing. These
are exact rational comparisons, not floating-point evidence. Unknown implied
constants prevent a numerical finite-N crossover claim. The conjectural
`N^ε` bound under abc is a different assumption class.

## Derived comparison: cube coefficients

Let `Q(u)=u²−u+1`. We have `u³+1=(u+1)Q(u)` and
`gcd(u+1,Q(u)) | 3`. If `u³+1` is powerful, every prime other than 3
dividing Q has valuation at least two. Thus **9Q is powerful**. Multiplication
by 3 alone does not always work, because it can introduce a prime of valuation
one when 3 does not divide Q.

The fixed positive quadratic `9u²−9u+9` has nonsquare discriminant `−243`.
The injection `t ↦ u=at`, followed by dropping the condition `a | u`, gives

    #{1≤t≤T : 1+a³t³ powerful} ≤ Cε (aT)^(293/1220+ε).

Taking `ε=289/97600` proves the exponent in A4(ii) with coefficient power
`A^(389/4800)` for `A=a³`; smaller positive ε gives a strictly smaller T
exponent. Applying the same reduction to a fixed-quadratic comparator gives
`(aT)^(2/5+ε)` from Saito, or approximately `(aT)^(0.4769+ε)` from
Wongcharoenbhorn–Meemark. These are deductions, not corollaries explicitly
located in those sources.

## Derived comparison: coefficient-uniform cubic and quadratic bounds

Here all constants are independent of the polynomial coefficients unless
their dependence is displayed. Evertse–Silverman, Theorem 1, over Q bounds
the number of S-integral x for which a separable polynomial F has a nonzero
n-th-power value. If S includes the infinite place and every prime of its
discriminant, write `s=|S|`. For a field L of degree M containing the required
roots, their bounds are

    n=3, at least two roots:   17^(M(6+s)) 3^(2Ms+κ₃(L));
    n=2, at least three roots: 7^(M(4+9s)) 4^κ₂(L).

Here κ is the relevant rank of the ideal class group. If its order is h,
`3^κ₃≤h` and `4^κ₂≤h²`. For degrees at most six, Minkowski's theorem and
`ζ_L(2)≤ζ(2)^6` give the coarse uniform estimate `h_L≪|D_L|`:
count ideals of norm at most `c√|D_L|`, bounding that count by
`c²|D_L| ζ_L(2)`. Also `C^ω(k)≤Cη k^η` for any fixed C and positive η.

For `P_A(t)=1+At³`, its splitting field is
`L=Q(α,ζ₃)`, `α³=−A²`, with degree at most six and
`|D_L|≤3^9 A^8`. If A is not a cube, this follows from the integral order
generated by α and ζ₃, of absolute discriminant `(27A⁴)²3³`; if A is a cube the
field is just `Q(ζ₃)`. Applying the square estimate to `qP_A` and the cube
estimate to `k²P_A` yields

    #{t∈Z : P_A(t)∈q Z² \ {0}} ≤ Cη A^178 q^η,
    #{t∈Z : P_A(t)∈k Z³ \ {0}} ≤ Cη A^62 k^η.

For example, the first uses `s≤2+ω(A)+ω(q)`, class-number loss `A^16`,
and `7^(54ω(A))≤A^162`; the second uses
`17^6 3^12<2^54`. Write `P_A(t)=e²d³≤2AT³`. At least one of e,d
is at most `U=(2AT³)^(1/5)`. Summing the cube fibres for `e≤U` with `k=e²`,
and square fibres for `d≤U` with `q=d`, gives

    Cη A^178 U^(1+2η)
      = C'η A^(178+1/5+2η/5) T^(3/5+6η/5).

Choose `η=min(5ε/6,1)`. This proves `Cε A^180 T^(3/5+ε)` with an
absolute exponent 180 chosen independently of ε, as required in A4(i).

For `Q(n)=an²+bn+c` in A3's range, `0<|Δ|≤5L²` and
the quadratic root field has discriminant at most `20L²`, hence class
number `≪L²`. The cube estimate applied to `k²Q` gives `Cη L^38 k^η`.
For a square fibre, completing the square gives

    (2an+b)²−4aqv²=Δ,     |2an+b|, |v|≤3LN.

Vaughan–Wooley Lemma 3.5 bounds its solutions by `Cη(L⁴qN)^η`;
the right-hand side is nonzero, and signs or a zero first coordinate cost
only a fixed factor. Split `Q(n)=e²d³≤3LN²` at `U=(3LN²)^(1/5)`.
The contributions are at most

    Cη L^(38+1/5+2η/5) N^(2/5+4η/5),
    Cη L^(1/5+21η/5) N^(2/5+7η/5).

Taking `η=min(5ε/7,1/4)` proves `Cε L^39 N^(2/5+ε)`.
Neither this bound nor the cubic one is asserted with sharp coefficient
powers. They establish that polynomial coefficient loss itself is not novel.

## Primary sources and nearby questions

- W. Wongcharoenbhorn and Y. Meemark, *Square-full values of quadratic
  polynomials*, **Bull. Aust. Math. Soc. 113** (2026), 40–54.
  [Author manuscript](https://arxiv.org/abs/2405.06968v2), Theorems A/B,
  Remark 4.5 and Proposition 3.7. Theorem A gives `29/100` uniformly for
  `n²+a²`; B gives approximately `0.4769` for nonzero discriminant.
- J.-C. Puchta, *On the powerfull part of n²+1*, **Arch. Math. (Brno) 39**
  (2003), 187–189. [Author PDF](https://www.mathematik.uni-rostock.de/storages/uni-rostock/Alle_MNF/Mathematik/Struktur/Lehrstuehle/Algebra/papers/powerfull.pdf),
  Corollary 3: `2/5` with a logarithmic factor.
- Y. Saito, *Shared prime support, small radicals, and square-full polynomial
  values*, [unrefereed manuscript](https://doi.org/10.5281/zenodo.21942580),
  Theorem 1.3: `X^(d/5+ε)` for a fixed separable polynomial of degree d.
  Its status is kept separate from journal publications.
- J.-H. Evertse and J. H. Silverman, *Uniform bounds for the number of
  solutions to Yⁿ=f(X)*, **Math. Proc. Cambridge Philos. Soc. 100** (1986),
  237–248. [Published PDF](https://ir.cwi.nl/pub/1788/1788D.pdf), Theorem 1.
- R. C. Vaughan and T. D. Wooley, *Further improvements in Waring's problem*,
  **Acta Math. 174** (1995), 147–240.
  [Author PDF](https://www.math.purdue.edu/~twooley/publ/1995%20fiwp.pdf), Lemma 3.5.
- J. S. Milne, *Algebraic Number Theory*, version 3.08,
  [author notes](https://www.jmilne.org/math/CourseNotes/ANT.pdf), Theorem 4.3.
- J.-M. De Koninck, N. Doyon and F. Luca, *Powerful Values of Quadratic
  Polynomials*, **J. Integer Seq. 14** (2011), Article 11.3.3.
  [Published PDF](https://cs.uwaterloo.ca/journals/JIS/VOL14/DeKoninck/dek.pdf),
  Theorem 1: almost every k admits infinitely many powerful values of n²+k.
  This existence theorem does not dominate the upper bounds. Its title is
  the same as Paper 1's; the shared title is not evidence of mathematical duplication.
- H. Pasten, *Powerful values of polynomials and a conjecture of Vojta*,
  **J. Number Theory 133** (2013), 2964–2998.
  [Author PDF](https://people.math.harvard.edu/~hpasten/preprints/PowJNT.pdf),
  Theorem 2.1 and Corollary 2.2: conditional restrictions on consecutive
  powerful values, not a nonconjectural pointwise counting competitor.
- S. Salami, *On powerful values of polynomials over number fields*,
  [arXiv:1707.05349v5](https://arxiv.org/abs/1707.05349v5), Theorems 1.1–1.2:
  conditional polynomial-family finiteness under a quantitative Vojta hypothesis.
- S. Streeter, *Campana points and powerful values of norm forms*,
  **Math. Z. 301** (2022), 627–664.
  [Author manuscript](https://arxiv.org/abs/2009.01106v2), Theorem 1.1 and
  Corollary 1.3. The multivariable anticanonical-height count does not yield
  A1 by restricting to a one-variable slice.
- S. S. Pohl, *S-squareful values of binary quadratic forms*,
  [arXiv:2610.20316v1](https://arxiv.org/abs/2610.20316v1), Theorem 1.2:
  an ambient two-variable asymptotic with prime exceptions, not a thin-slice bound.
- O. Trifonov, *Lattice points close to a smooth curve and squarefull numbers
  in short intervals. II*, [arXiv:2609.17715v1](https://arxiv.org/abs/2609.17715v1),
  Theorems 1–2. Short-interval density and general lattice-point estimates
  are relevant methods, not a stated competitor to A1–A3.
- R. de la Bretèche, V. Y. Wang and M. W. Xu, *Random multiplicative functions
  and making squares from polynomial values*,
  [arXiv:2607.06398v1](https://arxiv.org/abs/2607.06398v1), Lemmas 3.2–3.3
  and 6.2: fibre estimates and large-square-divisor bounds; these do not give
  the exponent of A1 by direct application.

## Search limits

The search includes cached primary literature, arXiv metadata and manuscripts,
zbMATH Open, title/keyword variants, backward references and forward-citation
services. Citation indexes have incomplete coverage: zero indexed citations
cannot establish the absence of follow-up work. Broad arXiv title searches
returned truncated result sets; targeted searches supplement them. Some
publisher/problem pages were inaccessible. The principal comparison theorems
were read in primary PDFs, including author manuscripts where the publisher
page was unavailable. Abstract-only discoveries are not treated as checked
theorems. There is no MathSciNet-wide or human-expert certification.

This note covers the claims of the quadratic-value paper. It does not certify
the novelty of its cited inputs. A future comparison should start
from the derived `L^39 N^(2/5+ε)` and `A^180 T^(3/5+ε)` bounds and the
fixed-quadratic cube reduction, retaining their written status.
