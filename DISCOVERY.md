# What the counting paper makes possible

The powerful-product paper supplies more than the bounds for which it is named.
Its central construction turns a difficult integer-counting problem into a
controlled count of points on an affine curve. Paper 1
uses that construction: it extends the method, makes its
constants uniform in new parameters, and combines it with additional arithmetic
arguments to reach different families of problems.

This is the scientific connection between
[Counting powerful products of consecutive integers](papers/powerful-counting/main.pdf)
and [Paper 1: Powerful values of quadratic polynomials](papers/powerful-polynomial-values/main.pdf).
Paper 1 stands alone relative to its cited inputs. The distinction between a
direct use of a proved theorem and an extension of its method matters.

## The reusable construction

In the powerful-product paper, approximate determinant arguments place solutions
on auxiliary curves. For a component of bidegree `(alpha, beta)`, a lift through
twelve monomials gives an affine curve of degree `2 alpha + 3 beta`, with point
height bounded by `L₁³ T₁²`. The Castryck–Cluckers–Dittmann–Nguyen estimate then
converts that geometry into a counting bound. Component estimates, lattice
moments and summation support the powerful-product exponent `77/320` for
fixed widths. The pair exponent `1/4` also uses Reuss and Heath-Brown inputs;
extending the product bound uniformly over all widths uses Tao. These distinct
premises are recorded in the published result, and are not silently removed or
imported wholesale into Paper 1.

The reusable asset is this controlled passage from arithmetic solutions to
curves and back to the original count. The degree, height, multiplicities,
exceptional components and summation losses are essential parts of it. A new
problem needs those quantities justified again; inserting a new exponent into
an optimization table is not enough.

## The quadratic-value results

| Direction | Result and paper | What extends the counting framework |
|---|---|---|
| Powerful values of polynomials (Paper 1) | A1 bounds powerful values of every fixed integral quadratic with positive leading coefficient and nonsquare discriminant by `N^(293/1220+ε)`. A2 controls the growing-coefficient family `n²+a²`. | Quadratic norm decompositions and refined determinant estimates connect the curve-counting method to polynomial values. |
| Uniform families and their consequences (Paper 1) | A3 gives `K L^B N^(389/1600)` uniformly over admissible quadratics of coefficient height at most `L`, with absolute positive `K,B`. A11–A13 use this estimate for mixed-full neighbours. | Controlling coefficient losses makes the estimate usable inside another proof, where the polynomial varies with the objects being counted. The gain is the combination of the exponent below `1/4` and polynomial coefficient dependence; weaker bounds with polynomial dependence follow from classical estimates. |

## A concrete chain of reusable results

The coefficient-uniform quadratic theorem A3 feeds directly into A11–A13:

1. Specialize A3 to `A t²+1`, `A t²+h` or the nonsplit family `A t²−H`.
2. Retain explicit dependence on the coefficient `A`; the positive constants
   can be chosen before the later counting variables.
3. Apply canonical full-number decompositions and split the population into
   ranges where those uniform estimates can be summed.
4. Obtain savings below `X^(1/s)` for the specified mixed-full neighbours with
   `s=6` or `s=8` and `2≤r<s`.

The cubic statements in A4 are supporting formalized applications. Its general
bound follows from classical Evertse–Silverman estimates, and its cube-coefficient
case follows from A1. Paper 1's Corollary 1.4 states the stronger written
cube-coefficient consequence of A1; its appendix distinguishes this deduction
from the retained formal A4 statement. They are not counted as independent discoveries.
The [prior-art note](verification/consecutive-counting/prior-art.md) gives the
comparison deductions and the precise scope of the mixed-full improvements.

A13 also directly uses the powerful-product width-three estimate: for a square
`n=m²`, the proof controls the product `(m−1)m(m+1)`. Substituting `m≤√X` turns
`77/320` into `77/640`, which is below the square-branch allowance `49/400`.
This is a precise example of one proved counting result supplying a component
of another proof.

## What this evidence establishes

The scientific advance is a broader set of statements and reusable proof
components, not merely more formalized lines. Paper 1's seven formal
interfaces have integrated Lean/Comparator/Nanoda evidence. The A13 interface
explicitly states the positive constants and saving
constructed inside its proof.

The [powerful-product result](registry/powerful-counting.json) is admitted under
the repository checklist. [Paper 1's shared formal library](registry/consecutive-counting.json)
has passed its integrated build, axiom/type audit, combined independent replay
and statement negative control. Paper 1 has independent AI
statement and proof-route reviews. The reviews compare statements
and extracted proof chains, with selected source checks; they are not a
line-by-line audit of every Lean proof body. All external premises are named,
and no human review is claimed. The scientific connections above do not
waive those checks or assert that every displayed statement is a best-known
result across every parameter range.
