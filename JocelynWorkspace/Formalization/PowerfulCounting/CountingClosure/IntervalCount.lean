import JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.LemmaP

/-!
# The per-interval count of Proposition 5.6 and its auxiliary steps.

Part of the counting closure; the release theorems are in `JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure`.
-/

namespace JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.dupNamespace false
set_option linter.unnecessarySimpa false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.deprecated false

namespace C04

set_option maxHeartbeats 4000000

theorem JocelynClaims.claim_f56115864eb7c92e5ad231b172657146b77a9332843b622b2b96df6831dbf036 :
(∀ (D E x M ρ0 : ℝ), 1 / 2 ≤ D → 1 / 2 ≤ E → 1 < x → 1 ≤ M →
    D / (2 * E) ≤ ρ0 → ρ0 ≤ 2 * D / E →
  (∀ h : ℤ, 3 * |(h : ℝ)| * M ≤ x →
    ∀ d e u v : ℕ, D < (d : ℝ) → (d : ℝ) ≤ 2 * D → E < (e : ℝ) → (e : ℝ) ≤ 2 * E →
      x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ) < (u : ℝ) → (u : ℝ) < 2 * (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)) →
      x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ) < (v : ℝ) → (v : ℝ) < 2 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ)) →
      (e : ℤ) ^ 3 * (v : ℤ) ^ 2 - (d : ℤ) ^ 3 * (u : ℤ) ^ 2 = h →
      ρ0 < (d : ℝ) / (e : ℝ) → (d : ℝ) / (e : ℝ) ≤ ρ0 * (1 + 1 / M) →
        0 < (d : ℝ) - ρ0 * (e : ℝ) ∧ (d : ℝ) - ρ0 * (e : ℝ) ≤ 4 * D / M ∧
        |(v : ℝ) - ρ0 ^ (3 / 2 : ℝ) * (u : ℝ)| ≤ 17 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ)) / M) ∧
  (∀ h : ℤ, 9 * (h : ℝ) ^ 2 ≤ x → M ≤ x ^ (1 / 2 : ℝ) → 3 * |(h : ℝ)| * M ≤ x) ∧
  (∃ b1 b2 : ℤ × ℤ, (b1.1 * b2.2 - b1.2 * b2.1 = 1 ∨ b1.1 * b2.2 - b1.2 * b2.1 = -1) ∧
    Real.sqrt ((M / (4 * D) * ((b1.1 : ℝ) - ρ0 * (b1.2 : ℝ))) ^ 2 + ((b1.2 : ℝ) / (2 * E)) ^ 2) ≤
      Real.sqrt ((M / (4 * D) * ((b2.1 : ℝ) - ρ0 * (b2.2 : ℝ))) ^ 2 + ((b2.2 : ℝ) / (2 * E)) ^ 2) ∧
    |M / (4 * D) * ((b1.1 : ℝ) - ρ0 * (b1.2 : ℝ)) * (M / (4 * D) * ((b2.1 : ℝ) - ρ0 * (b2.2 : ℝ))) +
        (b1.2 : ℝ) / (2 * E) * ((b2.2 : ℝ) / (2 * E))| ≤
      ((M / (4 * D) * ((b1.1 : ℝ) - ρ0 * (b1.2 : ℝ))) ^ 2 + ((b1.2 : ℝ) / (2 * E)) ^ 2) / 2) ∧
  (∀ b1 b2 : ℤ × ℤ, (b1.1 * b2.2 - b1.2 * b2.1 = 1 ∨ b1.1 * b2.2 - b1.2 * b2.1 = -1) →
    Real.sqrt ((M / (4 * D) * ((b1.1 : ℝ) - ρ0 * (b1.2 : ℝ))) ^ 2 + ((b1.2 : ℝ) / (2 * E)) ^ 2) ≤
      Real.sqrt ((M / (4 * D) * ((b2.1 : ℝ) - ρ0 * (b2.2 : ℝ))) ^ 2 + ((b2.2 : ℝ) / (2 * E)) ^ 2) →
    |M / (4 * D) * ((b1.1 : ℝ) - ρ0 * (b1.2 : ℝ)) * (M / (4 * D) * ((b2.1 : ℝ) - ρ0 * (b2.2 : ℝ))) +
        (b1.2 : ℝ) / (2 * E) * ((b2.2 : ℝ) / (2 * E))| ≤
      ((M / (4 * D) * ((b1.1 : ℝ) - ρ0 * (b1.2 : ℝ))) ^ 2 + ((b1.2 : ℝ) / (2 * E)) ^ 2) / 2 →
    2 / Real.sqrt ((M / (4 * D) * ((b2.1 : ℝ) - ρ0 * (b2.2 : ℝ))) ^ 2 + ((b2.2 : ℝ) / (2 * E)) ^ 2) ≤
      2 / Real.sqrt ((M / (4 * D) * ((b1.1 : ℝ) - ρ0 * (b1.2 : ℝ))) ^ 2 + ((b1.2 : ℝ) / (2 * E)) ^ 2) ∧
    27 * (D * E / M) ≤
      2 / Real.sqrt ((M / (4 * D) * ((b1.1 : ℝ) - ρ0 * (b1.2 : ℝ))) ^ 2 + ((b1.2 : ℝ) / (2 * E)) ^ 2) *
      (2 / Real.sqrt ((M / (4 * D) * ((b2.1 : ℝ) - ρ0 * (b2.2 : ℝ))) ^ 2 + ((b2.2 : ℝ) / (2 * E)) ^ 2)) ∧
    2 / Real.sqrt ((M / (4 * D) * ((b1.1 : ℝ) - ρ0 * (b1.2 : ℝ))) ^ 2 + ((b1.2 : ℝ) / (2 * E)) ^ 2) *
      (2 / Real.sqrt ((M / (4 * D) * ((b2.1 : ℝ) - ρ0 * (b2.2 : ℝ))) ^ 2 + ((b2.2 : ℝ) / (2 * E)) ^ 2)) ≤
      32 * (D * E / M) ∧
    5 * Real.sqrt (D * E / M) ≤
      2 / Real.sqrt ((M / (4 * D) * ((b1.1 : ℝ) - ρ0 * (b1.2 : ℝ))) ^ 2 + ((b1.2 : ℝ) / (2 * E)) ^ 2) ∧
    (∀ d' e' : ℤ, |(d' : ℝ) - ρ0 * (e' : ℝ)| ≤ 4 * D / M → |(e' : ℝ)| ≤ 2 * E →
      ∃ l : ℤ × ℤ, d' = l.1 * b1.1 + l.2 * b2.1 ∧ e' = l.1 * b1.2 + l.2 * b2.2 ∧
        |(l.1 : ℝ)| ≤ 2 / Real.sqrt ((M / (4 * D) * ((b1.1 : ℝ) - ρ0 * (b1.2 : ℝ))) ^ 2 +
          ((b1.2 : ℝ) / (2 * E)) ^ 2) ∧
        |(l.2 : ℝ)| ≤ 2 / Real.sqrt ((M / (4 * D) * ((b2.1 : ℝ) - ρ0 * (b2.2 : ℝ))) ^ 2 +
          ((b2.2 : ℝ) / (2 * E)) ^ 2)) ∧
    (∀ z : ℤ × ℤ, ∃! l : ℤ × ℤ, z.1 = l.1 * b1.1 + l.2 * b2.1 ∧ z.2 = l.1 * b1.2 + l.2 * b2.2) ∧
    (∀ l : ℤ × ℤ, Int.gcd (l.1 * b1.1 + l.2 * b2.1) (l.1 * b1.2 + l.2 * b2.2) = Int.gcd l.1 l.2)) ∧
  (∃ c1 c2 : ℤ × ℤ, (c1.1 * c2.2 - c1.2 * c2.1 = 1 ∨ c1.1 * c2.2 - c1.2 * c2.1 = -1) ∧
    Real.sqrt ((M / (17 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ))) * ((c1.1 : ℝ) - ρ0 ^ (3 / 2 : ℝ) * (c1.2 : ℝ))) ^ 2 +
        ((c1.2 : ℝ) / (2 * (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)))) ^ 2) ≤
      Real.sqrt ((M / (17 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ))) * ((c2.1 : ℝ) - ρ0 ^ (3 / 2 : ℝ) * (c2.2 : ℝ))) ^ 2 +
        ((c2.2 : ℝ) / (2 * (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)))) ^ 2) ∧
    |M / (17 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ))) * ((c1.1 : ℝ) - ρ0 ^ (3 / 2 : ℝ) * (c1.2 : ℝ)) *
        (M / (17 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ))) * ((c2.1 : ℝ) - ρ0 ^ (3 / 2 : ℝ) * (c2.2 : ℝ))) +
        (c1.2 : ℝ) / (2 * (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ))) *
          ((c2.2 : ℝ) / (2 * (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ))))| ≤
      ((M / (17 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ))) * ((c1.1 : ℝ) - ρ0 ^ (3 / 2 : ℝ) * (c1.2 : ℝ))) ^ 2 +
        ((c1.2 : ℝ) / (2 * (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)))) ^ 2) / 2) ∧
  (∀ c1 c2 : ℤ × ℤ, (c1.1 * c2.2 - c1.2 * c2.1 = 1 ∨ c1.1 * c2.2 - c1.2 * c2.1 = -1) →
    Real.sqrt ((M / (17 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ))) * ((c1.1 : ℝ) - ρ0 ^ (3 / 2 : ℝ) * (c1.2 : ℝ))) ^ 2 +
        ((c1.2 : ℝ) / (2 * (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)))) ^ 2) ≤
      Real.sqrt ((M / (17 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ))) * ((c2.1 : ℝ) - ρ0 ^ (3 / 2 : ℝ) * (c2.2 : ℝ))) ^ 2 +
        ((c2.2 : ℝ) / (2 * (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)))) ^ 2) →
    |M / (17 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ))) * ((c1.1 : ℝ) - ρ0 ^ (3 / 2 : ℝ) * (c1.2 : ℝ)) *
        (M / (17 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ))) * ((c2.1 : ℝ) - ρ0 ^ (3 / 2 : ℝ) * (c2.2 : ℝ))) +
        (c1.2 : ℝ) / (2 * (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ))) *
          ((c2.2 : ℝ) / (2 * (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ))))| ≤
      ((M / (17 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ))) * ((c1.1 : ℝ) - ρ0 ^ (3 / 2 : ℝ) * (c1.2 : ℝ))) ^ 2 +
        ((c1.2 : ℝ) / (2 * (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)))) ^ 2) / 2 →
    2 / Real.sqrt ((M / (17 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ))) * ((c2.1 : ℝ) - ρ0 ^ (3 / 2 : ℝ) * (c2.2 : ℝ))) ^ 2 +
        ((c2.2 : ℝ) / (2 * (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)))) ^ 2) ≤
      2 / Real.sqrt ((M / (17 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ))) * ((c1.1 : ℝ) - ρ0 ^ (3 / 2 : ℝ) * (c1.2 : ℝ))) ^ 2 +
        ((c1.2 : ℝ) / (2 * (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)))) ^ 2) ∧
    117 * ((x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)) * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ)) / M) ≤
      2 / Real.sqrt ((M / (17 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ))) * ((c1.1 : ℝ) - ρ0 ^ (3 / 2 : ℝ) * (c1.2 : ℝ))) ^ 2 +
        ((c1.2 : ℝ) / (2 * (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)))) ^ 2) *
      (2 / Real.sqrt ((M / (17 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ))) * ((c2.1 : ℝ) - ρ0 ^ (3 / 2 : ℝ) * (c2.2 : ℝ))) ^ 2 +
        ((c2.2 : ℝ) / (2 * (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)))) ^ 2)) ∧
    2 / Real.sqrt ((M / (17 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ))) * ((c1.1 : ℝ) - ρ0 ^ (3 / 2 : ℝ) * (c1.2 : ℝ))) ^ 2 +
        ((c1.2 : ℝ) / (2 * (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)))) ^ 2) *
      (2 / Real.sqrt ((M / (17 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ))) * ((c2.1 : ℝ) - ρ0 ^ (3 / 2 : ℝ) * (c2.2 : ℝ))) ^ 2 +
        ((c2.2 : ℝ) / (2 * (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)))) ^ 2)) ≤
      136 * ((x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)) * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ)) / M) ∧
    10 * Real.sqrt ((x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)) * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ)) / M) ≤
      2 / Real.sqrt ((M / (17 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ))) * ((c1.1 : ℝ) - ρ0 ^ (3 / 2 : ℝ) * (c1.2 : ℝ))) ^ 2 +
        ((c1.2 : ℝ) / (2 * (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)))) ^ 2) ∧
    (∀ v' u' : ℤ, |(v' : ℝ) - ρ0 ^ (3 / 2 : ℝ) * (u' : ℝ)| ≤ 17 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ)) / M →
      |(u' : ℝ)| ≤ 2 * (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)) →
      ∃ l : ℤ × ℤ, v' = l.1 * c1.1 + l.2 * c2.1 ∧ u' = l.1 * c1.2 + l.2 * c2.2 ∧
        |(l.1 : ℝ)| ≤ 2 / Real.sqrt ((M / (17 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ))) *
          ((c1.1 : ℝ) - ρ0 ^ (3 / 2 : ℝ) * (c1.2 : ℝ))) ^ 2 +
          ((c1.2 : ℝ) / (2 * (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)))) ^ 2) ∧
        |(l.2 : ℝ)| ≤ 2 / Real.sqrt ((M / (17 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ))) *
          ((c2.1 : ℝ) - ρ0 ^ (3 / 2 : ℝ) * (c2.2 : ℝ))) ^ 2 +
          ((c2.2 : ℝ) / (2 * (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)))) ^ 2)) ∧
    (∀ z : ℤ × ℤ, ∃! l : ℤ × ℤ, z.1 = l.1 * c1.1 + l.2 * c2.1 ∧ z.2 = l.1 * c1.2 + l.2 * c2.2) ∧
    (∀ l : ℤ × ℤ, Int.gcd (l.1 * c1.1 + l.2 * c2.1) (l.1 * c1.2 + l.2 * c2.2) = Int.gcd l.1 l.2))) →
∀ (D E x M ρ0 : ℝ), 1 / 2 ≤ D → 1 / 2 ≤ E → 1 < x → 1 ≤ M → D / (2 * E) ≤ ρ0 → ρ0 ≤ 2 * D / E →
  ∀ h : ℤ, 3 * |(h : ℝ)| * M ≤ x →
  let U : ℝ := x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ);
  let V : ℝ := x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ);
  let Lb : ℤ × ℤ → ℝ := fun b => 2 / Real.sqrt ((M / (4 * D) * ((b.1 : ℝ) - ρ0 * (b.2 : ℝ))) ^ 2 + ((b.2 : ℝ) / (2 * E)) ^ 2);
  let Tc : ℤ × ℤ → ℝ := fun c => 2 / Real.sqrt ((M / (17 * V) * ((c.1 : ℝ) - ρ0 ^ (3 / 2 : ℝ) * (c.2 : ℝ))) ^ 2 + ((c.2 : ℝ) / (2 * U)) ^ 2);
  (∀ d e u v : ℕ, D < (d : ℝ) → (d : ℝ) ≤ 2 * D → E < (e : ℝ) → (e : ℝ) ≤ 2 * E →
    U < (u : ℝ) → (u : ℝ) < 2 * U → V < (v : ℝ) → (v : ℝ) < 2 * V →
    (e : ℤ) ^ 3 * (v : ℤ) ^ 2 - (d : ℤ) ^ 3 * (u : ℤ) ^ 2 = h →
    ρ0 < (d : ℝ) / (e : ℝ) → (d : ℝ) / (e : ℝ) ≤ ρ0 * (1 + 1 / M) →
      0 < (d : ℝ) - ρ0 * (e : ℝ) ∧ (d : ℝ) - ρ0 * (e : ℝ) ≤ 4 * D / M ∧
      |(v : ℝ) - ρ0 ^ (3 / 2 : ℝ) * (u : ℝ)| ≤ 17 * V / M) ∧
  ∃ b1 b2 c1 c2 : ℤ × ℤ, (b1.1 * b2.2 - b1.2 * b2.1 = 1 ∨ b1.1 * b2.2 - b1.2 * b2.1 = -1) ∧
    (c1.1 * c2.2 - c1.2 * c2.1 = 1 ∨ c1.1 * c2.2 - c1.2 * c2.1 = -1) ∧ Lb b2 ≤ Lb b1 ∧ Tc c2 ≤ Tc c1 ∧
    (∀ d' e' : ℤ, |(d' : ℝ) - ρ0 * (e' : ℝ)| ≤ 4 * D / M → |(e' : ℝ)| ≤ 2 * E →
      ∃ l : ℤ × ℤ, d' = l.1 * b1.1 + l.2 * b2.1 ∧ e' = l.1 * b1.2 + l.2 * b2.2 ∧
        |(l.1 : ℝ)| ≤ Lb b1 ∧ |(l.2 : ℝ)| ≤ Lb b2) ∧
    (∀ v' u' : ℤ, |(v' : ℝ) - ρ0 ^ (3 / 2 : ℝ) * (u' : ℝ)| ≤ 17 * V / M → |(u' : ℝ)| ≤ 2 * U →
      ∃ l : ℤ × ℤ, v' = l.1 * c1.1 + l.2 * c2.1 ∧ u' = l.1 * c1.2 + l.2 * c2.2 ∧
        |(l.1 : ℝ)| ≤ Tc c1 ∧ |(l.2 : ℝ)| ≤ Tc c2) := by
  intro hred D E x M ρ0 hD hE hx hM hρ1 hρ2 h h3 U V Lb Tc
  obtain ⟨hr1, hr2, ⟨b1, b2, hbdet, hbn, hbi⟩, hr4, ⟨c1, c2, hcdet, hcn, hci⟩, hr6⟩ :=
    hred D E x M ρ0 hD hE hx hM hρ1 hρ2
  have hr4' := hr4 b1 b2 hbdet hbn hbi
  have hr6' := hr6 c1 c2 hcdet hcn hci
  exact ⟨hr1 h h3, b1, b2, c1, c2, hbdet, hcdet, hr4'.1, hr6'.1, hr4'.2.2.2.2.1, hr6'.2.2.2.2.1⟩

end C04

namespace C05

set_option maxHeartbeats 4000000

theorem JocelynClaims.claim_d96752184b235d650a46f2dff4a9ef38dc21eb534d570eb142527cc4534496ac :
let SW : ℤ → ℝ → ℝ → ℝ → Set (ℕ × ℕ × ℕ × ℕ) := fun h D E x => {w | D < (w.1 : ℝ) ∧ (w.1 : ℝ) ≤ 2 * D ∧ E < (w.2.1 : ℝ) ∧ (w.2.1 : ℝ) ≤ 2 * E ∧ x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ) < (w.2.2.1 : ℝ) ∧ (w.2.2.1 : ℝ) < 2 * (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)) ∧ x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ) < (w.2.2.2 : ℝ) ∧ (w.2.2.2 : ℝ) < 2 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ)) ∧ (w.2.1 : ℤ) ^ 3 * (w.2.2.2 : ℤ) ^ 2 - (w.1 : ℤ) ^ 3 * (w.2.2.1 : ℤ) ^ 2 = h};
let StewartHyp : Prop := ∀ q : ℕ, 3 ≤ q → ∀ a : Fin (q + 1) → ℤ, Finset.univ.gcd a = 1 → Squarefree (∑ i : Fin (q + 1), MvPolynomial.C (a i : ℚ) * MvPolynomial.X (0 : Fin 2) ^ (i : ℕ) * MvPolynomial.X (1 : Fin 2) ^ (q - (i : ℕ))) → ∀ m : ℤ, m ≠ 0 → {rs : ℤ × ℤ | Int.gcd rs.1 rs.2 = 1 ∧ ∑ i : Fin (q + 1), a i * rs.1 ^ (i : ℕ) * rs.2 ^ (q - (i : ℕ)) = m}.encard ≤ ((2800 * q ^ (1 + m.natAbs.primeFactors.card) : ℕ) : ℕ∞);
(let StewartHyp : Prop := ∀ q : ℕ, 3 ≤ q → ∀ a : Fin (q + 1) → ℤ, Finset.univ.gcd a = 1 → Squarefree (∑ i : Fin (q + 1), MvPolynomial.C (a i : ℚ) * MvPolynomial.X (0 : Fin 2) ^ (i : ℕ) * MvPolynomial.X (1 : Fin 2) ^ (q - (i : ℕ))) → ∀ m : ℤ, m ≠ 0 → {rs : ℤ × ℤ | Int.gcd rs.1 rs.2 = 1 ∧ ∑ i : Fin (q + 1), a i * rs.1 ^ (i : ℕ) * rs.2 ^ (q - (i : ℕ)) = m}.encard ≤ ((2800 * q ^ (1 + m.natAbs.primeFactors.card) : ℕ) : ℕ∞);
let SW : ℤ → ℝ → ℝ → ℝ → Set (ℕ × ℕ × ℕ × ℕ) := fun h D E x => {w | D < (w.1 : ℝ) ∧ (w.1 : ℝ) ≤ 2 * D ∧ E < (w.2.1 : ℝ) ∧ (w.2.1 : ℝ) ≤ 2 * E ∧ x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ) < (w.2.2.1 : ℝ) ∧ (w.2.2.1 : ℝ) < 2 * (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)) ∧ x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ) < (w.2.2.2 : ℝ) ∧ (w.2.2.2 : ℝ) < 2 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ)) ∧ (w.2.1 : ℤ) ^ 3 * (w.2.2.2 : ℤ) ^ 2 - (w.1 : ℤ) ^ 3 * (w.2.2.1 : ℤ) ^ 2 = h};
((∀ h : ℤ, h ≠ 0 → ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ d e : ℕ, 0 < d → 0 < e → ∀ Z : ℝ, 2 ≤ Z →
      {uv : ℕ × ℕ | (uv.1 : ℝ) ≤ Z ∧ (uv.2 : ℝ) ≤ Z ∧
          (e : ℤ) ^ 3 * (uv.2 : ℤ) ^ 2 - (d : ℤ) ^ 3 * (uv.1 : ℤ) ^ 2 = h}.Finite ∧
      ({uv : ℕ × ℕ | (uv.1 : ℝ) ≤ Z ∧ (uv.2 : ℝ) ≤ Z ∧
          (e : ℤ) ^ 3 * (uv.2 : ℤ) ^ 2 - (d : ℤ) ^ 3 * (uv.1 : ℤ) ^ 2 = h}.ncard : ℝ)
        ≤ C * ((d : ℝ) * e * Z) ^ ε) ∧
  (∀ h : ℤ, h ≠ 0 → ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ D E x : ℝ, 1 / 2 ≤ D → 1 / 2 ≤ E → 1 < x →
      (SW h D E x).Finite ∧
      ((SW h D E x).ncard : ℝ) ≤ C * x ^ (Real.log (D * E) / Real.log x + ε)) ∧
  (StewartHyp →
    (∀ h : ℤ, h ≠ 0 → ∀ G₀ : ℝ, 1 ≤ G₀ → ∀ u v : ℕ, 0 < u → 0 < v →
      {de : ℕ × ℕ | ((Nat.gcd de.1 de.2 : ℕ) : ℝ) ≤ G₀ ∧
          (de.2 : ℤ) ^ 3 * (v : ℤ) ^ 2 - (de.1 : ℤ) ^ 3 * (u : ℤ) ^ 2 = h}.Finite ∧
      ({de : ℕ × ℕ | ((Nat.gcd de.1 de.2 : ℕ) : ℝ) ≤ G₀ ∧
          (de.2 : ℤ) ^ 3 * (v : ℤ) ^ 2 - (de.1 : ℤ) ^ 3 * (u : ℤ) ^ 2 = h}.ncard : ℝ)
        ≤ G₀ * 2800 * 3 ^ (1 + h.natAbs.primeFactors.card)) ∧
    (∀ h : ℤ, h ≠ 0 → ∀ G₀ : ℝ, 1 ≤ G₀ → ∃ C : ℝ, 0 < C ∧
      ∀ D E x : ℝ, 1 / 2 ≤ D → 1 / 2 ≤ E → 1 < x →
        {w | w ∈ SW h D E x ∧ ((Nat.gcd w.1 w.2.1 : ℕ) : ℝ) ≤ G₀}.Finite ∧
        ({w | w ∈ SW h D E x ∧ ((Nat.gcd w.1 w.2.1 : ℕ) : ℝ) ≤ G₀}.ncard : ℝ) ≤
          C * x ^ (Real.log ((x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)) *
            (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ))) / Real.log x)))) ∧
((∀ h : ℤ, h ≠ 0 → ∀ G : Finset ℕ, ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ D E x : ℝ, 1 / 2 ≤ D → 1 / 2 ≤ E → 1 < x → ∀ a b : ℤ, (a, b) ≠ (0, 0) →
      {w | w ∈ SW h D E x ∧ a * (w.1 : ℤ) + b * (w.2.1 : ℤ) = 0 ∧ Nat.gcd w.1 w.2.1 ∈ G}.Finite ∧
      ({w | w ∈ SW h D E x ∧ a * (w.1 : ℤ) + b * (w.2.1 : ℤ) = 0 ∧ Nat.gcd w.1 w.2.1 ∈ G}.ncard : ℝ)
        ≤ C * x ^ ε) ∧
  (StewartHyp → ∀ h : ℤ, h ≠ 0 → ∀ G : Finset ℕ, ∃ C : ℝ, 0 < C ∧
    ∀ D E x : ℝ, 1 / 2 ≤ D → 1 / 2 ≤ E → 1 < x → ∀ a b : ℤ, (a, b) ≠ (0, 0) →
      {w | w ∈ SW h D E x ∧ a * (w.2.2.2 : ℤ) + b * (w.2.2.1 : ℤ) = 0 ∧
          Nat.gcd w.1 w.2.1 ∈ G ∧ Nat.gcd w.2.2.1 w.2.2.2 ∈ G}.Finite ∧
      ({w | w ∈ SW h D E x ∧ a * (w.2.2.2 : ℤ) + b * (w.2.2.1 : ℤ) = 0 ∧
          Nat.gcd w.1 w.2.1 ∈ G ∧ Nat.gcd w.2.2.1 w.2.2.2 ∈ G}.ncard : ℝ) ≤ C) ∧
  (∀ h : ℤ, h ≠ 0 → ∀ G : Finset ℕ, ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 < C ∧ ∀ D E x : ℝ, 1 / 2 ≤ D → 1 / 2 ≤ E → 1 < x → ∀ d₀ e₀ : ℕ,
      {w | w ∈ SW h D E x ∧ ∃ γ ∈ G, w.1 = γ * d₀ ∧ w.2.1 = γ * e₀}.Finite ∧
      ({w | w ∈ SW h D E x ∧ ∃ γ ∈ G, w.1 = γ * d₀ ∧ w.2.1 = γ * e₀}.ncard : ℝ) ≤
        C * x ^ ε) ∧
  (StewartHyp → ∀ h : ℤ, h ≠ 0 → ∀ G : Finset ℕ,
    ∃ C : ℝ, 0 < C ∧ ∀ D E x : ℝ, 1 / 2 ≤ D → 1 / 2 ≤ E → 1 < x → ∀ u₀ v₀ : ℕ,
      {w | w ∈ SW h D E x ∧ Nat.gcd w.1 w.2.1 ∈ G ∧
          ∃ γ ∈ G, w.2.2.1 = γ * u₀ ∧ w.2.2.2 = γ * v₀}.Finite ∧
      ({w | w ∈ SW h D E x ∧ Nat.gcd w.1 w.2.1 ∈ G ∧
          ∃ γ ∈ G, w.2.2.1 = γ * u₀ ∧ w.2.2.2 = γ * v₀}.ncard : ℝ) ≤ C)) ∧
((∀ c δ ε : ℝ, 0 < c → c ≤ 1 / 10 → 0 < δ → δ ≤ 1 / 100 → 0 < ε →
    ∃ C X₀ : ℝ, 0 < C ∧ 1 < X₀ ∧ ∀ x : ℝ, X₀ ≤ x → ∀ h : ℤ, 1 ≤ |h| →
      ((|h| : ℤ) : ℝ) ≤ x ^ (δ / 4) → ∀ D E : ℝ, 1 / 2 ≤ D → 1 / 2 ≤ E →
        {w | w ∈ SW h D E x ∧ Nat.gcd w.1 w.2.1 = 1 ∧ Nat.gcd w.2.2.1 w.2.2.2 = 1}.Finite ∧
        ({w | w ∈ SW h D E x ∧ Nat.gcd w.1 w.2.1 = 1 ∧ Nat.gcd w.2.2.1 w.2.2.2 = 1}.ncard : ℝ) ≤
          C * x ^ (Real.log (D * E) / Real.log x + ε)) ∧
  (StewartHyp →
    ∀ c δ ε : ℝ, 0 < c → c ≤ 1 / 10 → 0 < δ → δ ≤ 1 / 100 → 0 < ε →
    ∃ C X₀ : ℝ, 0 < C ∧ 1 < X₀ ∧ ∀ x : ℝ, X₀ ≤ x → ∀ h : ℤ, 1 ≤ |h| →
      ((|h| : ℤ) : ℝ) ≤ x ^ (δ / 4) → ∀ D E : ℝ, 1 / 2 ≤ D → 1 / 2 ≤ E →
        ({w | w ∈ SW h D E x ∧ Nat.gcd w.1 w.2.1 = 1 ∧ Nat.gcd w.2.2.1 w.2.2.2 = 1}.ncard : ℝ) ≤
          C * x ^ (Real.log ((x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)) *
            (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ))) / Real.log x + ε)))) →
StewartHyp →
((∀ h : ℤ, h ≠ 0 → ∀ D E x : ℝ, 1 / 2 ≤ D → 1 / 2 ≤ E → 1 < x → (SW h D E x).Finite) ∧
  (∀ h : ℤ, h ≠ 0 → ∀ G : Finset ℕ, ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ D E x : ℝ, 1 / 2 ≤ D → 1 / 2 ≤ E → 1 < x → ∀ a b : ℤ, (a, b) ≠ (0, 0) →
      {w | w ∈ SW h D E x ∧ a * (w.1 : ℤ) + b * (w.2.1 : ℤ) = 0 ∧ Nat.gcd w.1 w.2.1 ∈ G}.Finite ∧
      ({w | w ∈ SW h D E x ∧ a * (w.1 : ℤ) + b * (w.2.1 : ℤ) = 0 ∧ Nat.gcd w.1 w.2.1 ∈ G}.ncard : ℝ)
        ≤ C * x ^ ε) ∧
  (∀ h : ℤ, h ≠ 0 → ∀ G : Finset ℕ, ∃ C : ℝ, 0 < C ∧
    ∀ D E x : ℝ, 1 / 2 ≤ D → 1 / 2 ≤ E → 1 < x → ∀ a b : ℤ, (a, b) ≠ (0, 0) →
      {w | w ∈ SW h D E x ∧ a * (w.2.2.2 : ℤ) + b * (w.2.2.1 : ℤ) = 0 ∧
          Nat.gcd w.1 w.2.1 ∈ G ∧ Nat.gcd w.2.2.1 w.2.2.2 ∈ G}.Finite ∧
      ({w | w ∈ SW h D E x ∧ a * (w.2.2.2 : ℤ) + b * (w.2.2.1 : ℤ) = 0 ∧
          Nat.gcd w.1 w.2.1 ∈ G ∧ Nat.gcd w.2.2.1 w.2.2.2 ∈ G}.ncard : ℝ) ≤ C)) := by
  intro SW StewartHyp hbank hst
  dsimp only at hbank
  obtain ⟨⟨_, hSW, _⟩, ⟨hL1, hL2, _, _⟩, _⟩ := hbank
  refine ⟨fun h hh D E x hD hE hx => ?_, hL1, hL2 hst⟩
  obtain ⟨C, _, hC⟩ := hSW h hh 1 one_pos
  exact (hC D E x hD hE hx).1

end C05

namespace C06

set_option maxHeartbeats 4000000

namespace PcIntvBr

lemma vec_len_pos_gen (k β ρ : ℝ) (hk : 0 < k) (hβ : 0 < β) (b : ℤ × ℤ) (hb : b ≠ 0) :
    0 < 2 / Real.sqrt ((k * ((b.1 : ℝ) - ρ * (b.2 : ℝ))) ^ 2 + ((b.2 : ℝ) / β) ^ 2) := by
  apply div_pos (by norm_num)
  apply Real.sqrt_pos.mpr
  by_cases h2 : b.2 = 0
  · have h1 : b.1 ≠ 0 := by
      intro h1
      exact hb (Prod.ext h1 h2)
    have hP : k * ((b.1 : ℝ) - ρ * (b.2 : ℝ)) ≠ 0 := by
      rw [h2]
      simp only [Int.cast_zero, mul_zero, sub_zero]
      have : (b.1 : ℝ) ≠ 0 := by exact_mod_cast h1
      exact mul_ne_zero hk.ne' this
    have := lt_of_le_of_ne (sq_nonneg (k * ((b.1 : ℝ) - ρ * (b.2 : ℝ))))
      (Ne.symm (pow_ne_zero 2 hP))
    nlinarith [sq_nonneg ((b.2 : ℝ) / β)]
  · have hQ : (b.2 : ℝ) / β ≠ 0 := by
      have : (b.2 : ℝ) ≠ 0 := by exact_mod_cast h2
      exact div_ne_zero this hβ.ne'
    have := lt_of_le_of_ne (sq_nonneg ((b.2 : ℝ) / β)) (Ne.symm (pow_ne_zero 2 hQ))
    nlinarith [sq_nonneg (k * ((b.1 : ℝ) - ρ * (b.2 : ℝ)))]

lemma ne_zero_of_det (b1 b2 : ℤ × ℤ)
    (h : b1.1 * b2.2 - b1.2 * b2.1 = 1 ∨ b1.1 * b2.2 - b1.2 * b2.1 = -1) : b1 ≠ 0 ∧ b2 ≠ 0 := by
  constructor
  · rintro rfl
    simp at h
  · rintro rfl
    simp at h

end PcIntvBr

theorem JocelynClaims.claim_40f41d3d402f4f4a9ea8a5f265718b559a3a38d576a83b1f81b83de669aaa781 :
let CCDN12 : ℝ → Prop := fun c => (∀ d : ℕ, 1 ≤ d → ∀ I : Ideal (MvPolynomial (Fin 12) ℚ), I.IsPrime →
      ringKrullDim (MvPolynomial (Fin 12) ℚ ⧸ I) = 1 →
      (∃ e : ℤ, ∃ s₀ : ℕ, ∀ s : ℕ, s₀ ≤ s →
        (Module.finrank ℚ (Submodule.map (Ideal.Quotient.mkₐ ℚ I).toLinearMap
          (MvPolynomial.restrictTotalDegree (Fin 12) ℚ s)) : ℤ) = (d : ℤ) * (s : ℤ) + e) →
      ∀ B : ℝ, 1 ≤ B →
        ((({P : Fin 12 → ℤ | (∀ f ∈ I, MvPolynomial.eval (fun i => (P i : ℚ)) f = 0) ∧
            ∀ i, |(P i : ℝ)| ≤ B} : Set (Fin 12 → ℤ)).ncard : ℕ) : ℝ) ≤
          c * (d : ℝ) ^ 3 * B ^ ((1 : ℝ) / (d : ℝ)) * (Real.log B + (d : ℝ)));
(∀ c : ℝ,
    (∀ d : ℕ, 1 ≤ d → ∀ I : Ideal (MvPolynomial (Fin 12) ℚ), I.IsPrime →
      ringKrullDim (MvPolynomial (Fin 12) ℚ ⧸ I) = 1 →
      (∃ e : ℤ, ∃ s₀ : ℕ, ∀ s : ℕ, s₀ ≤ s →
        (Module.finrank ℚ (Submodule.map (Ideal.Quotient.mkₐ ℚ I).toLinearMap
          (MvPolynomial.restrictTotalDegree (Fin 12) ℚ s)) : ℤ) = (d : ℤ) * (s : ℤ) + e) →
      ∀ B : ℝ, 1 ≤ B →
        ((({P : Fin 12 → ℤ | (∀ f ∈ I, MvPolynomial.eval (fun i => (P i : ℚ)) f = 0) ∧
            ∀ i, |(P i : ℝ)| ≤ B} : Set (Fin 12 → ℤ)).ncard : ℕ) : ℝ) ≤
          c * (d : ℝ) ^ 3 * B ^ ((1 : ℝ) / (d : ℝ)) * (Real.log B + (d : ℝ))) →
    ∀ (h : ℤ), h ≠ 0 → ∀ (𝒢 : Finset ℕ), (∀ g ∈ 𝒢, 0 < g) →
    ∀ (α β : ℕ) (G : MvPolynomial (Fin 4) ℤ), 10 ≤ 2 * α + 3 * β → G ≠ 0 →
      (∀ m ∈ G.support, m 0 + m 1 = α ∧ m 2 + m 3 = β) →
      Irreducible (MvPolynomial.map (Int.castRingHom ℚ) G) →
    ∀ (D E x M ρ0 : ℝ) (b1 b2 c1 c2 : ℤ × ℤ),
      (b1.1 * b2.2 - b1.2 * b2.1 = 1 ∨ b1.1 * b2.2 - b1.2 * b2.1 = -1) →
      (c1.1 * c2.2 - c1.2 * c2.1 = 1 ∨ c1.1 * c2.2 - c1.2 * c2.1 = -1) →
    ∀ (L₁ L₂ T₁ T₂ : ℝ), L₂ ≤ L₁ → 0 < L₂ → T₂ ≤ T₁ → 0 < T₂ →
      (∀ d e u v : ℕ, D < (d : ℝ) → (d : ℝ) ≤ 2 * D → E < (e : ℝ) → (e : ℝ) ≤ 2 * E →
        x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ) < (u : ℝ) → (u : ℝ) < 2 * (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)) →
        x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ) < (v : ℝ) → (v : ℝ) < 2 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ)) →
        (e : ℤ) ^ 3 * (v : ℤ) ^ 2 - (d : ℤ) ^ 3 * (u : ℤ) ^ 2 = h →
        ρ0 < (d : ℝ) / (e : ℝ) → (d : ℝ) / (e : ℝ) ≤ ρ0 * (1 + 1 / M) →
          0 < (d : ℝ) - ρ0 * (e : ℝ) ∧ (d : ℝ) - ρ0 * (e : ℝ) ≤ 4 * D / M ∧
          |(v : ℝ) - ρ0 ^ (3 / 2 : ℝ) * (u : ℝ)| ≤ 17 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ)) / M) →
      (∀ d' e' : ℤ, |(d' : ℝ) - ρ0 * (e' : ℝ)| ≤ 4 * D / M → |(e' : ℝ)| ≤ 2 * E →
        ∃ l : ℤ × ℤ, d' = l.1 * b1.1 + l.2 * b2.1 ∧ e' = l.1 * b1.2 + l.2 * b2.2 ∧
          |(l.1 : ℝ)| ≤ L₁ ∧ |(l.2 : ℝ)| ≤ L₂) →
      (∀ v' u' : ℤ,
        |(v' : ℝ) - ρ0 ^ (3 / 2 : ℝ) * (u' : ℝ)| ≤ 17 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ)) / M →
        |(u' : ℝ)| ≤ 2 * (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)) →
        ∃ l : ℤ × ℤ, v' = l.1 * c1.1 + l.2 * c2.1 ∧ u' = l.1 * c1.2 + l.2 * c2.2 ∧
          |(l.1 : ℝ)| ≤ T₁ ∧ |(l.2 : ℝ)| ≤ T₂) →
      (({q : ℕ × ℕ × ℕ × ℕ | ((D < (q.1 : ℝ) ∧ (q.1 : ℝ) ≤ 2 * D ∧ E < (q.2.1 : ℝ) ∧ (q.2.1 : ℝ) ≤ 2 * E ∧
            x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ) < (q.2.2.1 : ℝ) ∧
            (q.2.2.1 : ℝ) < 2 * (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)) ∧
            x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ) < (q.2.2.2 : ℝ) ∧
            (q.2.2.2 : ℝ) < 2 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ)) ∧
            (q.2.1 : ℤ) ^ 3 * (q.2.2.2 : ℤ) ^ 2 - (q.1 : ℤ) ^ 3 * (q.2.2.1 : ℤ) ^ 2 = h) ∧
            Nat.gcd q.1 q.2.1 ∈ 𝒢 ∧ Nat.gcd q.2.2.1 q.2.2.2 ∈ 𝒢) ∧
          ρ0 < (q.1 : ℝ) / (q.2.1 : ℝ) ∧ (q.1 : ℝ) / (q.2.1 : ℝ) ≤ ρ0 * (1 + 1 / M) ∧
          MvPolynomial.eval ![(q.1 : ℤ), (q.2.1 : ℤ), (q.2.2.2 : ℤ), (q.2.2.1 : ℤ)] G = 0} :
            Set (ℕ × ℕ × ℕ × ℕ)).ncard : ℝ) ≤
        (𝒢.card : ℝ) ^ 2 * (2 * |c| * ((2 * α + 3 * β : ℕ) : ℝ) ^ 3 *
          (1 + (L₁ ^ 3 * T₁ ^ 2) ^ ((1 : ℝ) / 10)) *
          (Real.log (max 1 (L₁ ^ 3 * T₁ ^ 2)) + ((2 * α + 3 * β : ℕ) : ℝ)))) →
(∀ (D E x M ρ0 : ℝ), 1 / 2 ≤ D → 1 / 2 ≤ E → 1 < x → 1 ≤ M → D / (2 * E) ≤ ρ0 → ρ0 ≤ 2 * D / E →
  ∀ h : ℤ, 3 * |(h : ℝ)| * M ≤ x →
  let U : ℝ := x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ);
  let V : ℝ := x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ);
  let Lb : ℤ × ℤ → ℝ := fun b => 2 / Real.sqrt ((M / (4 * D) * ((b.1 : ℝ) - ρ0 * (b.2 : ℝ))) ^ 2 + ((b.2 : ℝ) / (2 * E)) ^ 2);
  let Tc : ℤ × ℤ → ℝ := fun c => 2 / Real.sqrt ((M / (17 * V) * ((c.1 : ℝ) - ρ0 ^ (3 / 2 : ℝ) * (c.2 : ℝ))) ^ 2 + ((c.2 : ℝ) / (2 * U)) ^ 2);
  (∀ d e u v : ℕ, D < (d : ℝ) → (d : ℝ) ≤ 2 * D → E < (e : ℝ) → (e : ℝ) ≤ 2 * E →
    U < (u : ℝ) → (u : ℝ) < 2 * U → V < (v : ℝ) → (v : ℝ) < 2 * V →
    (e : ℤ) ^ 3 * (v : ℤ) ^ 2 - (d : ℤ) ^ 3 * (u : ℤ) ^ 2 = h →
    ρ0 < (d : ℝ) / (e : ℝ) → (d : ℝ) / (e : ℝ) ≤ ρ0 * (1 + 1 / M) →
      0 < (d : ℝ) - ρ0 * (e : ℝ) ∧ (d : ℝ) - ρ0 * (e : ℝ) ≤ 4 * D / M ∧
      |(v : ℝ) - ρ0 ^ (3 / 2 : ℝ) * (u : ℝ)| ≤ 17 * V / M) ∧
  ∃ b1 b2 c1 c2 : ℤ × ℤ, (b1.1 * b2.2 - b1.2 * b2.1 = 1 ∨ b1.1 * b2.2 - b1.2 * b2.1 = -1) ∧
    (c1.1 * c2.2 - c1.2 * c2.1 = 1 ∨ c1.1 * c2.2 - c1.2 * c2.1 = -1) ∧ Lb b2 ≤ Lb b1 ∧ Tc c2 ≤ Tc c1 ∧
    (∀ d' e' : ℤ, |(d' : ℝ) - ρ0 * (e' : ℝ)| ≤ 4 * D / M → |(e' : ℝ)| ≤ 2 * E →
      ∃ l : ℤ × ℤ, d' = l.1 * b1.1 + l.2 * b2.1 ∧ e' = l.1 * b1.2 + l.2 * b2.2 ∧
        |(l.1 : ℝ)| ≤ Lb b1 ∧ |(l.2 : ℝ)| ≤ Lb b2) ∧
    (∀ v' u' : ℤ, |(v' : ℝ) - ρ0 ^ (3 / 2 : ℝ) * (u' : ℝ)| ≤ 17 * V / M → |(u' : ℝ)| ≤ 2 * U →
      ∃ l : ℤ × ℤ, v' = l.1 * c1.1 + l.2 * c2.1 ∧ u' = l.1 * c1.2 + l.2 * c2.2 ∧
        |(l.1 : ℝ)| ≤ Tc c1 ∧ |(l.2 : ℝ)| ≤ Tc c2)) →
(∃ c : ℝ, CCDN12 c) →
∃ c : ℝ, ∀ (D E x M ρ0 : ℝ), 1 / 2 ≤ D → 1 / 2 ≤ E → 1 < x → 1 ≤ M → D / (2 * E) ≤ ρ0 → ρ0 ≤ 2 * D / E →
  ∀ h : ℤ, h ≠ 0 → 3 * |(h : ℝ)| * M ≤ x →
  let U : ℝ := x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ);
  let V : ℝ := x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ);
  let Lb : ℤ × ℤ → ℝ := fun b => 2 / Real.sqrt ((M / (4 * D) * ((b.1 : ℝ) - ρ0 * (b.2 : ℝ))) ^ 2 + ((b.2 : ℝ) / (2 * E)) ^ 2);
  let Tc : ℤ × ℤ → ℝ := fun c => 2 / Real.sqrt ((M / (17 * V) * ((c.1 : ℝ) - ρ0 ^ (3 / 2 : ℝ) * (c.2 : ℝ))) ^ 2 + ((c.2 : ℝ) / (2 * U)) ^ 2);
  ∃ b1 c1 : ℤ × ℤ, b1 ≠ 0 ∧ c1 ≠ 0 ∧
    ∀ (𝒢 : Finset ℕ), (∀ g ∈ 𝒢, 0 < g) → ∀ (α β : ℕ) (G : MvPolynomial (Fin 4) ℤ), 10 ≤ 2 * α + 3 * β →
      (∀ m ∈ G.support, m 0 + m 1 = α ∧ m 2 + m 3 = β) →
      Irreducible (MvPolynomial.map (Int.castRingHom ℚ) G) →
      (({q : ℕ × ℕ × ℕ × ℕ | ((D < (q.1 : ℝ) ∧ (q.1 : ℝ) ≤ 2 * D ∧ E < (q.2.1 : ℝ) ∧ (q.2.1 : ℝ) ≤ 2 * E ∧
            U < (q.2.2.1 : ℝ) ∧ (q.2.2.1 : ℝ) < 2 * U ∧ V < (q.2.2.2 : ℝ) ∧ (q.2.2.2 : ℝ) < 2 * V ∧
            (q.2.1 : ℤ) ^ 3 * (q.2.2.2 : ℤ) ^ 2 - (q.1 : ℤ) ^ 3 * (q.2.2.1 : ℤ) ^ 2 = h) ∧
            Nat.gcd q.1 q.2.1 ∈ 𝒢 ∧ Nat.gcd q.2.2.1 q.2.2.2 ∈ 𝒢) ∧
          ρ0 < (q.1 : ℝ) / (q.2.1 : ℝ) ∧ (q.1 : ℝ) / (q.2.1 : ℝ) ≤ ρ0 * (1 + 1 / M) ∧
          MvPolynomial.eval ![(q.1 : ℤ), (q.2.1 : ℤ), (q.2.2.2 : ℤ), (q.2.2.1 : ℤ)] G = 0} :
            Set (ℕ × ℕ × ℕ × ℕ)).ncard : ℝ) ≤
        (𝒢.card : ℝ) ^ 2 * (2 * |c| * ((2 * α + 3 * β : ℕ) : ℝ) ^ 3 *
          (1 + (Lb b1 ^ 3 * Tc c1 ^ 2) ^ ((1 : ℝ) / 10)) *
          (Real.log (max 1 (Lb b1 ^ 3 * Tc c1 ^ 2)) + ((2 * α + 3 * β : ℕ) : ℝ))) := by
  intro CCDN12 hbr hIR hccdn
  obtain ⟨cc, hcc⟩ := hccdn
  refine ⟨cc, ?_⟩
  intro D E x M ρ0 hD hE hx hM hρ1 hρ2 h hh h3 U V Lb Tc
  have hD0 : 0 < D := by linarith
  have hE0 : 0 < E := by linarith
  have hx0 : 0 < x := by linarith
  have hM0 : 0 < M := by linarith
  have hU0 : 0 < U := by
    show 0 < x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)
    positivity
  have hV0 : 0 < V := by
    show 0 < x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ)
    positivity
  obtain ⟨hi, b1, b2, c1, c2, hb, hc, hL, hT, rb, rc⟩ := hIR D E x M ρ0 hD hE hx hM hρ1 hρ2 h h3
  obtain ⟨hb1, hb2⟩ := PcIntvBr.ne_zero_of_det b1 b2 hb
  obtain ⟨hc1, hc2⟩ := PcIntvBr.ne_zero_of_det c1 c2 hc
  have hkL : 0 < M / (4 * D) := by positivity
  have hkT : 0 < M / (17 * V) := div_pos hM0 (by linarith)
  have pL : 0 < Lb b2 :=
    PcIntvBr.vec_len_pos_gen (M / (4 * D)) (2 * E) ρ0 hkL (by linarith) b2 hb2
  have pT : 0 < Tc c2 :=
    PcIntvBr.vec_len_pos_gen (M / (17 * V)) (2 * U) (ρ0 ^ (3 / 2 : ℝ)) hkT (by linarith) c2 hc2
  refine ⟨b1, c1, hb1, hc1, ?_⟩
  intro 𝒢 h𝒢 α β G h10 hhom hirr
  have hG0 : G ≠ 0 := by
    rintro rfl
    simp at hirr
  exact hbr cc hcc h hh 𝒢 h𝒢 α β G h10 hG0 hhom hirr D E x M ρ0 b1 b2 c1 c2 hb hc
    (Lb b1) (Lb b2) (Tc c1) (Tc c2) hL pL hT pT hi rb rc

end C06

namespace C07

set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace PcIntv
open MvPolynomial

noncomputable def hom4 (A B : ℕ) (m : Fin 2 →₀ ℕ) : Fin 4 →₀ ℕ :=
  Finsupp.single 0 (m 0) + Finsupp.single 1 (A - m 0) + Finsupp.single 2 (m 1) +
    Finsupp.single 3 (B - m 1)

lemma hom4_apply (A B : ℕ) (m : Fin 2 →₀ ℕ) :
    hom4 A B m 0 = m 0 ∧ hom4 A B m 1 = A - m 0 ∧ hom4 A B m 2 = m 1 ∧ hom4 A B m 3 = B - m 1 := by
  simp [hom4, Finsupp.single_apply]

lemma hom4_inj (A B : ℕ) : Function.Injective (hom4 A B) := by
  intro m m' h
  have h0 : hom4 A B m 0 = hom4 A B m' 0 := by rw [h]
  have h2 : hom4 A B m 2 = hom4 A B m' 2 := by rw [h]
  rw [(hom4_apply A B m).1, (hom4_apply A B m').1] at h0
  rw [(hom4_apply A B m).2.2.1, (hom4_apply A B m').2.2.1] at h2
  ext i
  fin_cases i
  · simpa using h0
  · simpa using h2

noncomputable def homog (A B : ℕ) (C : MvPolynomial (Fin 2) ℤ) : MvPolynomial (Fin 4) ℤ :=
  ∑ m ∈ C.support, monomial (hom4 A B m) (C.coeff m)

lemma homog_coeff (A B : ℕ) (C : MvPolynomial (Fin 2) ℤ) (n : Fin 4 →₀ ℕ) :
    (homog A B C).coeff n = ∑ m ∈ C.support, if hom4 A B m = n then C.coeff m else 0 := by
  unfold homog
  rw [coeff_sum]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [coeff_monomial]

lemma homog_coeff_hom (A B : ℕ) (C : MvPolynomial (Fin 2) ℤ) (m0 : Fin 2 →₀ ℕ) :
    (homog A B C).coeff (hom4 A B m0) = C.coeff m0 := by
  rw [homog_coeff, Finset.sum_eq_single m0]
  · rw [if_pos rfl]
  · intro b _ hb
    rw [if_neg]
    intro h
    exact hb (hom4_inj A B h)
  · intro h0
    rw [if_pos rfl]
    exact notMem_support_iff.mp h0

lemma homog_coeff_not (A B : ℕ) (C : MvPolynomial (Fin 2) ℤ) (n : Fin 4 →₀ ℕ)
    (hn : n ∉ Set.range (hom4 A B)) : (homog A B C).coeff n = 0 := by
  rw [homog_coeff]
  apply Finset.sum_eq_zero
  intro m _
  rw [if_neg]
  intro h
  exact hn ⟨m, h⟩

lemma homog_ne_zero (A B : ℕ) (C : MvPolynomial (Fin 2) ℤ) (hC : C ≠ 0) : homog A B C ≠ 0 := by
  intro h0
  apply hC
  ext m
  rw [← homog_coeff_hom A B C m, h0, coeff_zero, coeff_zero]

lemma homog_bihom (A B : ℕ) (C : MvPolynomial (Fin 2) ℤ)
    (hs : ∀ m ∈ C.support, m 0 ≤ A ∧ m 1 ≤ B) :
    ∀ n ∈ (homog A B C).support, n 0 + n 1 = A ∧ n 2 + n 3 = B := by
  intro n hn
  have hc : (homog A B C).coeff n ≠ 0 := mem_support_iff.mp hn
  by_cases hr : n ∈ Set.range (hom4 A B)
  · obtain ⟨m, rfl⟩ := hr
    rw [homog_coeff_hom] at hc
    obtain ⟨hA, hB⟩ := hs m (mem_support_iff.mpr hc)
    obtain ⟨h0, h1, h2, h3⟩ := hom4_apply A B m
    rw [h0, h1, h2, h3]
    omega
  · exact absurd (homog_coeff_not A B C n hr) hc

lemma homog_coeff_bound (A B : ℕ) (C : MvPolynomial (Fin 2) ℤ) (H : ℝ)
    (hH : ∀ m, |((C.coeff m : ℤ) : ℝ)| ≤ H) (h0 : 0 ≤ H) :
    ∀ n, |(((homog A B C).coeff n : ℤ) : ℝ)| ≤ H := by
  intro n
  by_cases hn : n ∈ Set.range (hom4 A B)
  · obtain ⟨m, rfl⟩ := hn
    rw [homog_coeff_hom]
    exact hH m
  · rw [homog_coeff_not A B C n hn]
    simpa using h0

lemma term_eq (a b : ℝ) (hb : b ≠ 0) (k A : ℕ) (hk : k ≤ A) :
    b ^ A * (a / b) ^ k = a ^ k * b ^ (A - k) := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [Nat.add_sub_cancel_left, pow_add, div_pow]
  field_simp

lemma homog_eval (A B : ℕ) (C : MvPolynomial (Fin 2) ℤ)
    (hs : ∀ m ∈ C.support, m 0 ≤ A ∧ m 1 ≤ B) (d e v u : ℤ) (he : e ≠ 0) (hu : u ≠ 0) :
    ((eval ![d, e, v, u] (homog A B C) : ℤ) : ℝ) =
      (e : ℝ) ^ A * (u : ℝ) ^ B * eval₂ (Int.castRingHom ℝ) ![(d : ℝ) / e, (v : ℝ) / u] C := by
  unfold homog
  rw [map_sum, eval₂_eq', Finset.mul_sum, Int.cast_sum]
  refine Finset.sum_congr rfl (fun m hm => ?_)
  obtain ⟨h0, h1, h2, h3⟩ := hom4_apply A B m
  obtain ⟨hA, hB⟩ := hs m hm
  have z0 : (![d, e, v, u] : Fin 4 → ℤ) 0 = d := rfl
  have z1 : (![d, e, v, u] : Fin 4 → ℤ) 1 = e := rfl
  have z2 : (![d, e, v, u] : Fin 4 → ℤ) 2 = v := rfl
  have z3 : (![d, e, v, u] : Fin 4 → ℤ) 3 = u := rfl
  have y0 : (![(d : ℝ) / e, (v : ℝ) / u] : Fin 2 → ℝ) 0 = (d : ℝ) / e := rfl
  have y1 : (![(d : ℝ) / e, (v : ℝ) / u] : Fin 2 → ℝ) 1 = (v : ℝ) / u := rfl
  rw [eval_monomial, Finsupp.prod_fintype _ _ (fun i => pow_zero _)]
  simp only [Fin.prod_univ_four, Fin.prod_univ_two, h0, h1, h2, h3, z0, z1, z2, z3, y0, y1,
    eq_intCast, Int.cast_mul, Int.cast_pow]
  have he' : (e : ℝ) ≠ 0 := by exact_mod_cast he
  have hu' : (u : ℝ) ≠ 0 := by exact_mod_cast hu
  have t1 := term_eq (d : ℝ) (e : ℝ) he' (m 0) A hA
  have t2 := term_eq (v : ℝ) (u : ℝ) hu' (m 1) B hB
  linear_combination (-(((C.coeff m : ℤ) : ℝ) * ((d : ℝ) ^ (m 0) * (e : ℝ) ^ (A - m 0)))) * t2 +
    (-(((C.coeff m : ℤ) : ℝ) * ((u : ℝ) ^ B * ((v : ℝ) / u) ^ (m 1)))) * t1

theorem homog_pkg (A B : ℕ) (C : MvPolynomial (Fin 2) ℤ) (H : ℝ) (hC : C ≠ 0)
    (hH : ∀ m, |((C.coeff m : ℤ) : ℝ)| ≤ H) (hs : ∀ m ∈ C.support, m 0 ≤ A ∧ m 1 ≤ B) :
    ∃ G : MvPolynomial (Fin 4) ℤ, G ≠ 0 ∧ (∀ n ∈ G.support, n 0 + n 1 = A ∧ n 2 + n 3 = B) ∧
      (∀ n, |((G.coeff n : ℤ) : ℝ)| ≤ H) ∧
      ∀ d e v u : ℕ, e ≠ 0 → u ≠ 0 →
        eval₂ (Int.castRingHom ℝ) ![(d : ℝ) / (e : ℝ), (v : ℝ) / (u : ℝ)] C = 0 →
        eval ![(d : ℤ), (e : ℤ), (v : ℤ), (u : ℤ)] G = 0 := by
  have hH0 : 0 ≤ H := le_trans (abs_nonneg _) (hH 0)
  refine ⟨homog A B C, homog_ne_zero A B C hC, homog_bihom A B C hs,
    homog_coeff_bound A B C H hH hH0, ?_⟩
  intro d e v u he hu h0
  have he' : (e : ℤ) ≠ 0 := by exact_mod_cast he
  have hu' : (u : ℤ) ≠ 0 := by exact_mod_cast hu
  have := homog_eval A B C hs (d : ℤ) (e : ℤ) (v : ℤ) (u : ℤ) he' hu'
  simp only [Int.cast_natCast] at this
  rw [h0, mul_zero] at this
  exact_mod_cast this

lemma rpow_eq_of_log (x y r : ℝ) (hx : 0 < x) (hy : 0 < y) (h : Real.log y = r * Real.log x) :
    x ^ r = y := by
  rw [Real.rpow_def_of_pos hx, mul_comm, ← h, Real.exp_log hy]

lemma neg_rpow_le_four (D : ℝ) (hD : 1 / 2 ≤ D) : D ^ (-3 / 2 : ℝ) ≤ 4 := by
  have hD0 : 0 < D := by linarith
  rw [neg_div, Real.rpow_neg hD0.le]
  have h1 : (1 / 2 : ℝ) ^ (3 / 2 : ℝ) ≤ D ^ (3 / 2 : ℝ) :=
    Real.rpow_le_rpow (by norm_num) hD (by norm_num)
  have h2 : (1 / 2 : ℝ) ^ (2 : ℝ) ≤ (1 / 2 : ℝ) ^ (3 / 2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) (by norm_num)
  rw [Real.rpow_two] at h2
  have h3 : (1 / 4 : ℝ) ≤ D ^ (3 / 2 : ℝ) := by nlinarith
  have h4 : 0 < D ^ (3 / 2 : ℝ) := by positivity
  rw [inv_le_comm₀ h4 (by norm_num)]
  linarith

lemma two_pow_eighth : (256 : ℝ) ^ (1 / 8 : ℝ) = 2 := by
  rw [show (256 : ℝ) = 2 ^ ((8 : ℕ) : ℝ) by rw [Real.rpow_natCast]; norm_num,
    ← Real.rpow_mul (by norm_num)]
  norm_num

theorem window_params (x D E c δ : ℝ) (hx : 1 < x) (hD : 1 / 2 ≤ D) (hE : 1 / 2 ≤ E) (hc : 0 < c)
    (hδ : 0 < δ) (hδ1 : δ < 1) (s t : ℝ)
    (hs : s = Real.log D / Real.log x + Real.log E / Real.log x) (ht : t = 1 - 3 * s / 2)
    (hcs : c ≤ s) (hct : c ≤ t) (M : ℕ) (hM : M = ⌈x ^ ((1 + δ) * (9 / 8 * s * t))⌉₊) :
    x ^ c ≤ D * E ∧
    x ^ c ≤ x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ) * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ)) ∧
    x ^ (c ^ 2) ≤ (M : ℝ) ∧
    (9 / 8 : ℝ) * (1 + δ) * Real.log (D * E) *
        Real.log (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ) * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ))) /
        Real.log x ≤ Real.log (M : ℝ) ∧
    1 ≤ (M : ℝ) ∧ (256 ≤ x → (M : ℝ) ≤ x ^ (1 / 2 : ℝ)) ∧ D ≤ 2 * x ∧ E ≤ 2 * x ∧
    x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ) ≤ 4 * x ∧ x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ) ≤ 4 * x := by
  have hx0 : 0 < x := by linarith
  have hD0 : 0 < D := by linarith
  have hE0 : 0 < E := by linarith
  have hlx : 0 < Real.log x := Real.log_pos hx
  have hlDE : Real.log (D * E) = s * Real.log x := by
    rw [Real.log_mul hD0.ne' hE0.ne', hs]
    field_simp
  have hU0 : 0 < x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ) := by positivity
  have hV0 : 0 < x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ) := by positivity
  have hlUV : Real.log (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ) * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ))) =
      t * Real.log x := by
    rw [Real.log_mul hU0.ne' hV0.ne', Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_rpow hx0, Real.log_rpow hD0,
      Real.log_rpow hE0, ht, hs]
    field_simp
    ring
  have hDE : x ^ s = D * E := rpow_eq_of_log x _ s hx0 (by positivity) hlDE
  have hUV : x ^ t = x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ) * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ)) :=
    rpow_eq_of_log x _ t hx0 (by positivity) hlUV
  have hs0 : 0 < s := lt_of_lt_of_le hc hcs
  have ht0 : 0 < t := lt_of_lt_of_le hc hct
  have hst : s * t ≤ 1 / 6 := by rw [ht]; nlinarith [sq_nonneg (s - 1 / 3)]
  have hm0 : 0 ≤ 9 / 8 * s * t := by positivity
  have hm1 : (1 + δ) * (9 / 8 * s * t) ≤ 3 / 8 := by
    nlinarith [mul_le_mul_of_nonneg_left hst (by linarith : (0 : ℝ) ≤ 1 + δ), mul_pos hs0 ht0]
  have hc2 : c ^ 2 ≤ (1 + δ) * (9 / 8 * s * t) := by
    nlinarith [mul_le_mul hcs hct hc.le hs0.le, mul_pos hδ (mul_pos hs0 ht0)]
  set y := x ^ ((1 + δ) * (9 / 8 * s * t)) with hy
  have hy0 : 0 < y := by positivity
  have hyM : y ≤ (M : ℝ) := by rw [hM]; exact Nat.le_ceil y
  have hMy : (M : ℝ) < y + 1 := by rw [hM]; exact Nat.ceil_lt_add_one hy0.le
  have hM1 : 1 ≤ (M : ℝ) := by
    have : 0 < M := by rw [hM]; exact Nat.ceil_pos.mpr hy0
    exact_mod_cast this
  have hs23 : s ≤ 1 := by nlinarith
  have hDEx : D * E ≤ x := by
    rw [← hDE]
    calc x ^ s ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx.le hs23
      _ = x := Real.rpow_one x
  have hxh : x ^ (1 / 2 : ℝ) ≤ x := by
    calc x ^ (1 / 2 : ℝ) ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx.le (by norm_num)
      _ = x := Real.rpow_one x
  have hxh0 : 0 ≤ x ^ (1 / 2 : ℝ) := by positivity
  refine ⟨?_, ?_, ?_, ?_, hM1, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hDE]; exact Real.rpow_le_rpow_of_exponent_le hx.le hcs
  · rw [← hUV]; exact Real.rpow_le_rpow_of_exponent_le hx.le hct
  · exact le_trans (Real.rpow_le_rpow_of_exponent_le hx.le hc2) hyM
  · rw [hlDE, hlUV]
    have hly : Real.log y = (1 + δ) * (9 / 8 * s * t) * Real.log x := by
      rw [hy, Real.log_rpow hx0]
    have hle : Real.log y ≤ Real.log (M : ℝ) := Real.log_le_log hy0 hyM
    have heq : 9 / 8 * (1 + δ) * (s * Real.log x) * (t * Real.log x) / Real.log x =
        (1 + δ) * (9 / 8 * s * t) * Real.log x := by
      rw [div_eq_iff hlx.ne']
      ring
    rw [heq, ← hly]
    exact hle
  · intro hx256
    have h38 : y ≤ x ^ (3 / 8 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx.le hm1
    have h8 : (2 : ℝ) ≤ x ^ (1 / 8 : ℝ) := by
      rw [← two_pow_eighth]
      exact Real.rpow_le_rpow (by norm_num) hx256 (by norm_num)
    have h38' : (1 : ℝ) ≤ x ^ (3 / 8 : ℝ) := Real.one_le_rpow hx.le (by norm_num)
    have hsplit : x ^ (1 / 2 : ℝ) = x ^ (3 / 8 : ℝ) * x ^ (1 / 8 : ℝ) := by
      rw [← Real.rpow_add hx0]; norm_num
    rw [hsplit]
    nlinarith [mul_le_mul_of_nonneg_left h8 (by linarith : (0 : ℝ) ≤ x ^ (3 / 8 : ℝ))]
  · nlinarith [mul_nonneg hD0.le (sub_nonneg.mpr hE)]
  · nlinarith [mul_nonneg hE0.le (sub_nonneg.mpr hD)]
  · have := neg_rpow_le_four D hD
    have hD' : 0 ≤ D ^ (-3 / 2 : ℝ) := by positivity
    nlinarith [mul_le_mul hxh this hD' (by linarith)]
  · have := neg_rpow_le_four E hE
    have hE' : 0 ≤ E ^ (-3 / 2 : ℝ) := by positivity
    nlinarith [mul_le_mul hxh this hE' (by linarith)]

lemma two_div_norm_le (P Q a b : ℝ) (ha : 0 < a) (hb : 0 < b) (h : a ≤ |P| ∨ b ≤ |Q|) :
    2 / Real.sqrt (P ^ 2 + Q ^ 2) ≤ 2 / a + 2 / b := by
  have hP : |P| ≤ Real.sqrt (P ^ 2 + Q ^ 2) := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg Q])
  have hQ : |Q| ≤ Real.sqrt (P ^ 2 + Q ^ 2) := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg P])
  have h2a : 0 ≤ 2 / a := by positivity
  have h2b : 0 ≤ 2 / b := by positivity
  rcases h with h | h
  · have : 2 / Real.sqrt (P ^ 2 + Q ^ 2) ≤ 2 / a :=
      div_le_div_of_nonneg_left (by norm_num) ha (le_trans h hP)
    linarith
  · have : 2 / Real.sqrt (P ^ 2 + Q ^ 2) ≤ 2 / b :=
      div_le_div_of_nonneg_left (by norm_num) hb (le_trans h hQ)
    linarith

lemma vec_len_le_gen (k β ρ : ℝ) (hk : 0 < k) (hβ : 0 < β) (b : ℤ × ℤ) (hb : b ≠ 0) :
    2 / Real.sqrt ((k * ((b.1 : ℝ) - ρ * (b.2 : ℝ))) ^ 2 + ((b.2 : ℝ) / β) ^ 2) ≤
      2 / k + 2 * β := by
  have key := two_div_norm_le (k * ((b.1 : ℝ) - ρ * (b.2 : ℝ))) ((b.2 : ℝ) / β)
    k (1 / β) hk (by positivity) ?_
  · have e2 : 2 / (1 / β) = 2 * β := by rw [div_div_eq_mul_div, div_one]
    rw [e2] at key
    exact key
  by_cases h2 : b.2 = 0
  · left
    have h1 : b.1 ≠ 0 := by
      intro h1
      exact hb (Prod.ext h1 h2)
    rw [h2]
    simp only [Int.cast_zero, mul_zero, sub_zero]
    rw [abs_mul, abs_of_pos hk]
    have h3 : (1 : ℝ) ≤ |(b.1 : ℝ)| := by
      rw [← Int.cast_abs]
      exact_mod_cast Int.one_le_abs h1
    nlinarith
  · right
    rw [abs_div, abs_of_pos hβ]
    have h3 : (1 : ℝ) ≤ |(b.2 : ℝ)| := by
      rw [← Int.cast_abs]
      exact_mod_cast Int.one_le_abs h2
    exact div_le_div_of_nonneg_right h3 hβ.le

lemma vec_len_pos_gen (k β ρ : ℝ) (hk : 0 < k) (hβ : 0 < β) (b : ℤ × ℤ) (hb : b ≠ 0) :
    0 < 2 / Real.sqrt ((k * ((b.1 : ℝ) - ρ * (b.2 : ℝ))) ^ 2 + ((b.2 : ℝ) / β) ^ 2) := by
  apply div_pos (by norm_num)
  apply Real.sqrt_pos.mpr
  by_cases h2 : b.2 = 0
  · have h1 : b.1 ≠ 0 := by
      intro h1
      exact hb (Prod.ext h1 h2)
    have hP : k * ((b.1 : ℝ) - ρ * (b.2 : ℝ)) ≠ 0 := by
      rw [h2]
      simp only [Int.cast_zero, mul_zero, sub_zero]
      have : (b.1 : ℝ) ≠ 0 := by exact_mod_cast h1
      exact mul_ne_zero hk.ne' this
    have := lt_of_le_of_ne (sq_nonneg (k * ((b.1 : ℝ) - ρ * (b.2 : ℝ))))
      (Ne.symm (pow_ne_zero 2 hP))
    nlinarith [sq_nonneg ((b.2 : ℝ) / β)]
  · have hQ : (b.2 : ℝ) / β ≠ 0 := by
      have : (b.2 : ℝ) ≠ 0 := by exact_mod_cast h2
      exact div_ne_zero this hβ.ne'
    have := lt_of_le_of_ne (sq_nonneg ((b.2 : ℝ) / β)) (Ne.symm (pow_ne_zero 2 hQ))
    nlinarith [sq_nonneg (k * ((b.1 : ℝ) - ρ * (b.2 : ℝ)))]

lemma log_le_rpow_div (y ε : ℝ) (hy : 0 < y) (hε : 0 < ε) : Real.log y ≤ y ^ ε / ε := by
  have h0 : 0 < y ^ ε := Real.rpow_pos_of_pos hy _
  have h5 := Real.log_le_sub_one_of_pos h0
  rw [Real.log_rpow hy] at h5
  rw [le_div_iff₀ hε]
  nlinarith

lemma log_absorb (Y Cb x ε dd : ℝ) (hY : 0 ≤ Y) (hCb : 1 ≤ Cb) (hx : 1 ≤ x) (hε : 0 < ε)
    (hYx : Y ≤ Cb * x ^ 5) (hdd : 0 ≤ dd) :
    Real.log (max 1 Y) + dd ≤ (Real.log Cb + 5 / ε + dd) * x ^ ε := by
  have hx0 : 0 < x := by linarith
  have hx5 : 1 ≤ x ^ 5 := one_le_pow₀ hx
  have hmax : max 1 Y ≤ Cb * x ^ 5 := max_le (by nlinarith) hYx
  have hl1 : Real.log (max 1 Y) ≤ Real.log (Cb * x ^ 5) :=
    Real.log_le_log (lt_of_lt_of_le one_pos (le_max_left _ _)) hmax
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow] at hl1
  have hlx := log_le_rpow_div x ε hx0 hε
  have hxe : 1 ≤ x ^ ε := Real.one_le_rpow hx hε.le
  have hlC : 0 ≤ Real.log Cb := Real.log_nonneg hCb
  have h5 : (5 : ℝ) * (x ^ ε / ε) = 5 / ε * x ^ ε := by ring
  have hlx0 : 0 ≤ Real.log x := Real.log_nonneg hx
  push_cast at hl1
  nlinarith [mul_le_mul_of_nonneg_left hxe hlC, mul_le_mul_of_nonneg_left hxe hdd]

lemma bridge_finish (N cc d K0 ε x Y Cb Cp : ℝ) (hd0 : 0 ≤ d) (hd : d ≤ 5 * K0) (hY : 0 ≤ Y)
    (hCb : 1 ≤ Cb) (hx : 1 ≤ x) (hε : 0 < ε) (hYx : Y ≤ Cb * x ^ 5)
    (hCp : N ^ 2 * (2 * |cc| * (5 * K0) ^ 3 * (Real.log Cb + 5 / ε + 5 * K0)) ≤ Cp) :
    N ^ 2 * (2 * |cc| * d ^ 3 * (1 + Y ^ ((1 : ℝ) / 10)) * (Real.log (max 1 Y) + d)) ≤
      Cp * x ^ ε * (1 + Y ^ ((1 : ℝ) / 10)) := by
  have hl := log_absorb Y Cb x ε d hY hCb hx hε hYx hd0
  have hxe : 1 ≤ x ^ ε := Real.one_le_rpow hx hε.le
  have hP0 : 0 ≤ 1 + Y ^ ((1 : ℝ) / 10) := by
    have := Real.rpow_nonneg hY ((1 : ℝ) / 10); linarith
  have hd3 : d ^ 3 ≤ (5 * K0) ^ 3 := pow_le_pow_left₀ hd0 hd 3
  have hc0 : 0 ≤ 2 * |cc| := by positivity
  have hA1 : 2 * |cc| * d ^ 3 * (1 + Y ^ ((1 : ℝ) / 10)) ≤
      2 * |cc| * (5 * K0) ^ 3 * (1 + Y ^ ((1 : ℝ) / 10)) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hd3 hc0) hP0
  have hlCb : 0 ≤ Real.log Cb := Real.log_nonneg hCb
  have hA2 : Real.log (max 1 Y) + d ≤ (Real.log Cb + 5 / ε + 5 * K0) * x ^ ε :=
    le_trans hl (mul_le_mul_of_nonneg_right (by linarith) (by linarith))
  have hlm : 0 ≤ Real.log (max 1 Y) := Real.log_nonneg (le_max_left _ _)
  have hK0 : 0 ≤ (5 * K0) ^ 3 := pow_nonneg (by linarith) 3
  have hA3 : 2 * |cc| * d ^ 3 * (1 + Y ^ ((1 : ℝ) / 10)) * (Real.log (max 1 Y) + d) ≤
      2 * |cc| * (5 * K0) ^ 3 * (1 + Y ^ ((1 : ℝ) / 10)) *
        ((Real.log Cb + 5 / ε + 5 * K0) * x ^ ε) :=
    mul_le_mul hA1 hA2 (by linarith) (mul_nonneg (mul_nonneg hc0 hK0) hP0)
  have hA4 := mul_le_mul_of_nonneg_left hA3 (sq_nonneg N)
  have hE : N ^ 2 * (2 * |cc| * (5 * K0) ^ 3 * (1 + Y ^ ((1 : ℝ) / 10)) *
        ((Real.log Cb + 5 / ε + 5 * K0) * x ^ ε)) =
      N ^ 2 * (2 * |cc| * (5 * K0) ^ 3 * (Real.log Cb + 5 / ε + 5 * K0)) * x ^ ε *
        (1 + Y ^ ((1 : ℝ) / 10)) := by ring
  rw [hE] at hA4
  have hA5 : N ^ 2 * (2 * |cc| * (5 * K0) ^ 3 * (Real.log Cb + 5 / ε + 5 * K0)) * x ^ ε *
        (1 + Y ^ ((1 : ℝ) / 10)) ≤ Cp * x ^ ε * (1 + Y ^ ((1 : ℝ) / 10)) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCp (by linarith)) hP0
  linarith

lemma three_h_M (x hh M : ℝ) (hx : 0 < x) (h9 : 9 * hh ^ 2 ≤ x) (hM : M ≤ x ^ (1 / 2 : ℝ))
    (hM0 : 0 ≤ M) : 3 * |hh| * M ≤ x := by
  have hs : x ^ (1 / 2 : ℝ) = Real.sqrt x := by rw [Real.sqrt_eq_rpow]
  rw [hs] at hM
  have h1 : 3 * |hh| ≤ Real.sqrt x := by
    have e : 3 * |hh| = Real.sqrt ((3 * |hh|) ^ 2) := (Real.sqrt_sq (by positivity)).symm
    rw [e]
    exact Real.sqrt_le_sqrt (by nlinarith [sq_abs hh])
  calc 3 * |hh| * M ≤ Real.sqrt x * M := mul_le_mul_of_nonneg_right h1 hM0
    _ ≤ Real.sqrt x * Real.sqrt x := mul_le_mul_of_nonneg_left hM (Real.sqrt_nonneg _)
    _ = x := Real.mul_self_sqrt hx.le

lemma ncard_le_of_sub {α : Type*} (S T : Set α) (hST : S ⊆ T) (hT : T.Finite) (B : ℝ)
    (hB : (T.ncard : ℝ) ≤ B) : (S.ncard : ℝ) ≤ B :=
  le_trans (by exact_mod_cast Set.ncard_le_ncard hST hT) hB

theorem ncard_biUnion_le' {α ι : Type*} [DecidableEq ι] (I : Finset ι) (A : ι → Set α) :
    (⋃ i ∈ I, A i).ncard ≤ ∑ i ∈ I, (A i).ncard := by
  induction I using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.set_biUnion_insert]
    exact (Set.ncard_union_le _ _).trans (by omega)

lemma cover_bound {α : Type*} (S : Set α) (k : ℕ) (P : Fin k → Set α) (hfin : ∀ i, (P i).Finite)
    (hcov : ∀ q ∈ S, ∃ i, q ∈ P i) (Bd : ℝ) (hB : ∀ i, ((P i).ncard : ℝ) ≤ Bd) :
    (S.ncard : ℝ) ≤ k * Bd := by
  classical
  have hU : (⋃ i ∈ (Finset.univ : Finset (Fin k)), P i).Finite :=
    Set.Finite.biUnion (Finset.univ : Finset (Fin k)).finite_toSet (fun i _ => hfin i)
  have hsub : S ⊆ ⋃ i ∈ (Finset.univ : Finset (Fin k)), P i := by
    intro q hq
    obtain ⟨i, hi⟩ := hcov q hq
    exact Set.mem_biUnion (Finset.mem_coe.mpr (Finset.mem_univ i)) hi
  have h1 : S.ncard ≤ ∑ i ∈ (Finset.univ : Finset (Fin k)), (P i).ncard :=
    (Set.ncard_le_ncard hsub hU).trans (ncard_biUnion_le' Finset.univ P)
  have h2 : (S.ncard : ℝ) ≤ ∑ i ∈ (Finset.univ : Finset (Fin k)), ((P i).ncard : ℝ) := by
    exact_mod_cast h1
  have h3 : ∑ i ∈ (Finset.univ : Finset (Fin k)), ((P i).ncard : ℝ) ≤
      ∑ _i ∈ (Finset.univ : Finset (Fin k)), Bd := Finset.sum_le_sum (fun i _ => hB i)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h3
  linarith

def Sint (h : ℤ) (G : Finset ℕ) (D E x ρ M : ℝ) : Set (ℕ × ℕ × ℕ × ℕ) :=
  {q : ℕ × ℕ × ℕ × ℕ | ((D < (q.1 : ℝ) ∧ (q.1 : ℝ) ≤ 2 * D ∧ E < (q.2.1 : ℝ) ∧ (q.2.1 : ℝ) ≤ 2 * E ∧
          x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ) < (q.2.2.1 : ℝ) ∧
          (q.2.2.1 : ℝ) < 2 * (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)) ∧
          x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ) < (q.2.2.2 : ℝ) ∧
          (q.2.2.2 : ℝ) < 2 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ)) ∧
          (q.2.1 : ℤ) ^ 3 * (q.2.2.2 : ℤ) ^ 2 - (q.1 : ℤ) ^ 3 * (q.2.2.1 : ℤ) ^ 2 = h) ∧
          Nat.gcd q.1 q.2.1 ∈ G ∧ Nat.gcd q.2.2.1 q.2.2.2 ∈ G) ∧
        ρ < (q.1 : ℝ) / (q.2.1 : ℝ) ∧ (q.1 : ℝ) / (q.2.1 : ℝ) ≤ ρ * (1 + 1 / M)}

def Spiece (h : ℤ) (G : Finset ℕ) (D E x ρ M : ℝ) (F : MvPolynomial (Fin 4) ℤ) :
    Set (ℕ × ℕ × ℕ × ℕ) :=
  {q : ℕ × ℕ × ℕ × ℕ | ((D < (q.1 : ℝ) ∧ (q.1 : ℝ) ≤ 2 * D ∧ E < (q.2.1 : ℝ) ∧ (q.2.1 : ℝ) ≤ 2 * E ∧
          x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ) < (q.2.2.1 : ℝ) ∧
          (q.2.2.1 : ℝ) < 2 * (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)) ∧
          x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ) < (q.2.2.2 : ℝ) ∧
          (q.2.2.2 : ℝ) < 2 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ)) ∧
          (q.2.1 : ℤ) ^ 3 * (q.2.2.2 : ℤ) ^ 2 - (q.1 : ℤ) ^ 3 * (q.2.2.1 : ℤ) ^ 2 = h) ∧
          Nat.gcd q.1 q.2.1 ∈ G ∧ Nat.gcd q.2.2.1 q.2.2.2 ∈ G) ∧
        ρ < (q.1 : ℝ) / (q.2.1 : ℝ) ∧ (q.1 : ℝ) / (q.2.1 : ℝ) ≤ ρ * (1 + 1 / M) ∧
        MvPolynomial.eval ![(q.1 : ℤ), (q.2.1 : ℤ), (q.2.2.2 : ℤ), (q.2.2.1 : ℤ)] F = 0}

lemma Spiece_filter (h : ℤ) (G : Finset ℕ) (D E x ρ M : ℝ) (F : MvPolynomial (Fin 4) ℤ)
    (hD : 0 ≤ D) (hU : 0 ≤ x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)) :
    Spiece h (G.filter (fun g => 0 < g)) D E x ρ M F = Spiece h G D E x ρ M F := by
  ext q
  constructor
  · rintro ⟨⟨hw, hg1, hg2⟩, hr⟩
    exact ⟨⟨hw, (Finset.mem_filter.mp hg1).1, (Finset.mem_filter.mp hg2).1⟩, hr⟩
  · rintro ⟨⟨hw, hg1, hg2⟩, hr⟩
    have hq1 : 0 < q.1 := by
      have : (0 : ℝ) < q.1 := lt_of_le_of_lt hD hw.1
      exact_mod_cast this
    have hq3 : 0 < q.2.2.1 := by
      have : (0 : ℝ) < q.2.2.1 := lt_of_le_of_lt hU hw.2.2.2.2.1
      exact_mod_cast this
    exact ⟨⟨hw, Finset.mem_filter.mpr ⟨hg1, Nat.gcd_pos_of_pos_left _ hq1⟩,
      Finset.mem_filter.mpr ⟨hg2, Nat.gcd_pos_of_pos_left _ hq3⟩⟩, hr⟩

noncomputable def B7 (c δ : ℝ) : ℕ := Nat.ceil (max (4/c) (32*(1+c^(-1/2:ℝ))/(c*δ)))
noncomputable def K07 (c δ : ℝ) : ℕ := Nat.floor (2*(B7 c δ:ℝ)/c)

theorem lemma7_clean (c δ hcap : ℝ) (hc : 0 < c) (hc1 : c < 1) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hcap0 : 0 ≤ hcap) :
    ∃ K0 κ : ℕ, ∃ X : ℝ, 1 < X ∧ ∀ (x D E ρ₀ : ℝ) (M : ℕ) (h : ℤ),
      X ≤ x → (1 / 2 : ℝ) ≤ D → (1 / 2 : ℝ) ≤ E → h ≠ 0 → |(h : ℝ)| ≤ hcap →
      x ^ c ≤ D * E →
      x ^ c ≤ x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ) * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ)) →
      x ^ (c ^ 2) ≤ (M : ℝ) → (M : ℝ) ≤ x →
      (9 / 8 : ℝ) * (1 + δ) * Real.log (D * E) *
          Real.log (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ) * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ))) /
          Real.log x ≤ Real.log (M : ℝ) →
      D / (2 * E) ≤ ρ₀ → ρ₀ ≤ 2 * D / E →
      ∃ A B : ℕ, A ≤ K0 ∧ B ≤ K0 ∧ ∃ C : MvPolynomial (Fin 2) ℤ, C ≠ 0 ∧
        (∀ m, |((C.coeff m : ℤ) : ℝ)| ≤ x ^ κ) ∧ (∀ m ∈ C.support, m 0 ≤ A ∧ m 1 ≤ B) ∧
        ∀ (w : Fin 4 → ℕ), D < (w 0 : ℝ) ∧ (w 0 : ℝ) ≤ 2 * D ∧ E < (w 1 : ℝ) ∧ (w 1 : ℝ) ≤ 2 * E ∧
          x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ) < (w 3 : ℝ) ∧
          (w 3 : ℝ) < 2 * (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)) ∧
          x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ) < (w 2 : ℝ) ∧
          (w 2 : ℝ) < 2 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ)) ∧
          ρ₀ < (w 0 : ℝ) / (w 1 : ℝ) ∧ (w 0 : ℝ) / (w 1 : ℝ) ≤ ρ₀ * (1 + 1 / (M : ℝ)) ∧
          (w 1 : ℝ) ^ 3 * (w 2 : ℝ) ^ 2 - (w 0 : ℝ) ^ 3 * (w 3 : ℝ) ^ 2 = (h : ℝ) →
          MvPolynomial.eval₂ (Int.castRingHom ℝ) ![(w 0 : ℝ) / (w 1 : ℝ), (w 2 : ℝ) / (w 3 : ℝ)] C = 0 := by
  have L := JocelynWorkspace.Formalization.PowerfulCounting.Paper3OriginalActualAuxiliaryPolynomial.JocelynClaims.claim_1d348efff0ed2d7d1daabd2d1147ea25df132caf1901a51df249fe2af2a5231b
    c δ hcap hc hc1 hδ hδ1 hcap0
  dsimp only at L
  obtain ⟨X, hX, hK⟩ := L
  refine ⟨K07 c δ, 2 * K07 c δ * (K07 c δ + 1) ^ 2 + 1, X, hX, ?_⟩
  intro x D E ρ₀ M h hXx hD hE hh hhc hDE hUV hM1 hM2 hlog hρ1 hρ2
  obtain ⟨hA, hB, C, hC0, hCh, hCs, hCv⟩ :=
    hK x D E ρ₀ M h hXx hD hE hh hhc hDE hUV hM1 hM2 hlog hρ1 hρ2
  exact ⟨_, _, hA, hB, C, hC0, hCh, hCs, hCv⟩

end PcIntv

open PcIntv in
theorem JocelynClaims.claim_7120078522372a7ae07be48f26ad006600fb959a2f32549f1b6dfc448875d107 :
let SW : ℤ → ℝ → ℝ → ℝ → Set (ℕ × ℕ × ℕ × ℕ) := fun h D E x => {w | D < (w.1 : ℝ) ∧ (w.1 : ℝ) ≤ 2 * D ∧ E < (w.2.1 : ℝ) ∧ (w.2.1 : ℝ) ≤ 2 * E ∧ x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ) < (w.2.2.1 : ℝ) ∧ (w.2.2.1 : ℝ) < 2 * (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)) ∧ x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ) < (w.2.2.2 : ℝ) ∧ (w.2.2.2 : ℝ) < 2 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ)) ∧ (w.2.1 : ℤ) ^ 3 * (w.2.2.2 : ℤ) ^ 2 - (w.1 : ℤ) ^ 3 * (w.2.2.1 : ℤ) ^ 2 = h};
let StewartHyp : Prop := ∀ q : ℕ, 3 ≤ q → ∀ a : Fin (q + 1) → ℤ, Finset.univ.gcd a = 1 → Squarefree (∑ i : Fin (q + 1), MvPolynomial.C (a i : ℚ) * MvPolynomial.X (0 : Fin 2) ^ (i : ℕ) * MvPolynomial.X (1 : Fin 2) ^ (q - (i : ℕ))) → ∀ m : ℤ, m ≠ 0 → {rs : ℤ × ℤ | Int.gcd rs.1 rs.2 = 1 ∧ ∑ i : Fin (q + 1), a i * rs.1 ^ (i : ℕ) * rs.2 ^ (q - (i : ℕ)) = m}.encard ≤ ((2800 * q ^ (1 + m.natAbs.primeFactors.card) : ℕ) : ℕ∞);
let Gelfond : Prop := (∀ n : ℕ, ∃ c : ℝ, 0 ≤ c ∧ ∀ (F G : MvPolynomial (Fin n) ℤ), F ≠ 0 → G ∣ F →
  ∀ H : ℝ, (∀ m, |((F.coeff m : ℤ) : ℝ)| ≤ H) →
    ∀ m, |((G.coeff m : ℤ) : ℝ)| ≤ Real.exp (c * (F.totalDegree : ℝ)) * H);
((∀ (q : ℕ), 3 ≤ q → ∀ (a : Fin (q + 1) → ℤ), Finset.univ.gcd a = 1 →
  Squarefree (∑ i : Fin (q + 1), MvPolynomial.C ((a i : ℤ) : ℚ) *
    MvPolynomial.X (0 : Fin 2) ^ (i : ℕ) * MvPolynomial.X (1 : Fin 2) ^ (q - (i : ℕ))) →
  ∀ (m : ℤ), m ≠ 0 →
    {rs : ℤ × ℤ | Int.gcd rs.1 rs.2 = 1 ∧
        ∑ i : Fin (q + 1), a i * rs.1 ^ (i : ℕ) * rs.2 ^ (q - (i : ℕ)) = m}.encard ≤
      ((2800 * q ^ (1 + m.natAbs.primeFactors.card) : ℕ) : ℕ∞)) →
∀ (h : ℤ), h ≠ 0 → ∀ (𝒢 : Finset ℕ), (∀ g ∈ 𝒢, 0 < g) →
∀ (K : ℝ) (α β : ℕ), 1 ≤ α → 1 ≤ β → min α β = 1 →
∀ (ε : ℝ), 0 < ε →
∃ Cst : ℝ, 0 < Cst ∧ ∀ x : ℝ, 1 ≤ x →
  ∀ G : MvPolynomial (Fin 4) ℤ,
    (∀ m ∈ G.support, m 0 + m 1 = α ∧ m 2 + m 3 = β) →
    Irreducible (MvPolynomial.map (Int.castRingHom ℂ) G) →
    (∀ m : Fin 4 →₀ ℕ, |((G.coeff m : ℤ) : ℝ)| ≤ x ^ K) →
    {w : ℕ × ℕ × ℕ × ℕ |
        MvPolynomial.eval ![(w.1 : ℤ), (w.2.1 : ℤ), (w.2.2.2 : ℤ), (w.2.2.1 : ℤ)] G = 0 ∧
        (w.2.1 : ℤ) ^ 3 * (w.2.2.2 : ℤ) ^ 2 - (w.1 : ℤ) ^ 3 * (w.2.2.1 : ℤ) ^ 2 = h ∧
        Nat.gcd w.1 w.2.1 ∈ 𝒢 ∧ Nat.gcd w.2.2.1 w.2.2.2 ∈ 𝒢}.Finite ∧
    (({w : ℕ × ℕ × ℕ × ℕ |
        MvPolynomial.eval ![(w.1 : ℤ), (w.2.1 : ℤ), (w.2.2.2 : ℤ), (w.2.2.1 : ℤ)] G = 0 ∧
        (w.2.1 : ℤ) ^ 3 * (w.2.2.2 : ℤ) ^ 2 - (w.1 : ℤ) ^ 3 * (w.2.2.1 : ℤ) ^ 2 = h ∧
        Nat.gcd w.1 w.2.1 ∈ 𝒢 ∧ Nat.gcd w.2.2.1 w.2.2.2 ∈ 𝒢}.ncard : ℝ) ≤ Cst * x ^ ε)) →
((∀ n : ℕ, ∃ c : ℝ, 0 ≤ c ∧ ∀ (F G : MvPolynomial (Fin n) ℤ), F ≠ 0 → G ∣ F →
  ∀ H : ℝ, (∀ m, |((F.coeff m : ℤ) : ℝ)| ≤ H) →
    ∀ m, |((G.coeff m : ℤ) : ℝ)| ≤ Real.exp (c * (F.totalDegree : ℝ)) * H) →
∃ c : ℝ, 0 ≤ c ∧ ∀ (F : MvPolynomial (Fin 4) ℤ) (a b : ℕ), F ≠ 0 →
  (∀ m ∈ F.support, m 0 + m 1 = a ∧ m 2 + m 3 = b) →
  ∃ (k : ℕ) (Gs : Fin k → MvPolynomial (Fin 4) ℤ) (dg : Fin k → ℕ × ℕ),
    k ≤ a + b ∧ (∀ j, Gs j ∣ F) ∧ (∀ j, Irreducible (Gs j)) ∧
    (∀ j, ∀ m ∈ (Gs j).support, m 0 + m 1 = (dg j).1 ∧ m 2 + m 3 = (dg j).2) ∧
    (∀ j, (dg j).1 ≤ a ∧ (dg j).2 ≤ b) ∧
    (∀ w : Fin 4 → ℤ, MvPolynomial.eval w F = 0 → ∃ j, MvPolynomial.eval w (Gs j) = 0) ∧
    (∀ H : ℝ, (∀ m, |((F.coeff m : ℤ) : ℝ)| ≤ H) →
      ∀ j m, |(((Gs j).coeff m : ℤ) : ℝ)| ≤ Real.exp (c * ((a + b : ℕ) : ℝ)) * H) ∧
    (∀ j,
      ((dg j).2 = 0 ∧ 2 ≤ (dg j).1 ∧
          ∀ w : Fin 4 → ℤ, MvPolynomial.eval w (Gs j) = 0 → w 0 = 0 ∧ w 1 = 0) ∨
      ((dg j).1 = 0 ∧ 2 ≤ (dg j).2 ∧
          ∀ w : Fin 4 → ℤ, MvPolynomial.eval w (Gs j) = 0 → w 2 = 0 ∧ w 3 = 0) ∨
      (dg j = (1, 0) ∧ ∃ p q : ℤ, (p, q) ≠ (0, 0) ∧
          Gs j = MvPolynomial.C p * MvPolynomial.X 0 + MvPolynomial.C q * MvPolynomial.X 1) ∨
      (dg j = (0, 1) ∧ ∃ p q : ℤ, (p, q) ≠ (0, 0) ∧
          Gs j = MvPolynomial.C p * MvPolynomial.X 2 + MvPolynomial.C q * MvPolynomial.X 3) ∨
      (1 ≤ (dg j).1 ∧ 1 ≤ (dg j).2 ∧ min (dg j).1 (dg j).2 = 1 ∧
          Irreducible (MvPolynomial.map (Int.castRingHom ℂ) (Gs j))) ∨
      (2 ≤ (dg j).1 ∧ 2 ≤ (dg j).2 ∧
          Irreducible (MvPolynomial.map (Int.castRingHom ℚ) (Gs j))))) →
((∀ h : ℤ, h ≠ 0 → ∀ D E x : ℝ, 1 / 2 ≤ D → 1 / 2 ≤ E → 1 < x → (SW h D E x).Finite) ∧
  (∀ h : ℤ, h ≠ 0 → ∀ G : Finset ℕ, ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ D E x : ℝ, 1 / 2 ≤ D → 1 / 2 ≤ E → 1 < x → ∀ a b : ℤ, (a, b) ≠ (0, 0) →
      {w | w ∈ SW h D E x ∧ a * (w.1 : ℤ) + b * (w.2.1 : ℤ) = 0 ∧ Nat.gcd w.1 w.2.1 ∈ G}.Finite ∧
      ({w | w ∈ SW h D E x ∧ a * (w.1 : ℤ) + b * (w.2.1 : ℤ) = 0 ∧ Nat.gcd w.1 w.2.1 ∈ G}.ncard : ℝ)
        ≤ C * x ^ ε) ∧
  (∀ h : ℤ, h ≠ 0 → ∀ G : Finset ℕ, ∃ C : ℝ, 0 < C ∧
    ∀ D E x : ℝ, 1 / 2 ≤ D → 1 / 2 ≤ E → 1 < x → ∀ a b : ℤ, (a, b) ≠ (0, 0) →
      {w | w ∈ SW h D E x ∧ a * (w.2.2.2 : ℤ) + b * (w.2.2.1 : ℤ) = 0 ∧
          Nat.gcd w.1 w.2.1 ∈ G ∧ Nat.gcd w.2.2.1 w.2.2.2 ∈ G}.Finite ∧
      ({w | w ∈ SW h D E x ∧ a * (w.2.2.2 : ℤ) + b * (w.2.2.1 : ℤ) = 0 ∧
          Nat.gcd w.1 w.2.1 ∈ G ∧ Nat.gcd w.2.2.1 w.2.2.2 ∈ G}.ncard : ℝ) ≤ C)) →
(∃ c : ℝ, ∀ (D E x M ρ0 : ℝ), 1 / 2 ≤ D → 1 / 2 ≤ E → 1 < x → 1 ≤ M → D / (2 * E) ≤ ρ0 → ρ0 ≤ 2 * D / E →
  ∀ h : ℤ, h ≠ 0 → 3 * |(h : ℝ)| * M ≤ x →
  let U : ℝ := x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ);
  let V : ℝ := x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ);
  let Lb : ℤ × ℤ → ℝ := fun b => 2 / Real.sqrt ((M / (4 * D) * ((b.1 : ℝ) - ρ0 * (b.2 : ℝ))) ^ 2 + ((b.2 : ℝ) / (2 * E)) ^ 2);
  let Tc : ℤ × ℤ → ℝ := fun c => 2 / Real.sqrt ((M / (17 * V) * ((c.1 : ℝ) - ρ0 ^ (3 / 2 : ℝ) * (c.2 : ℝ))) ^ 2 + ((c.2 : ℝ) / (2 * U)) ^ 2);
  ∃ b1 c1 : ℤ × ℤ, b1 ≠ 0 ∧ c1 ≠ 0 ∧
    ∀ (𝒢 : Finset ℕ), (∀ g ∈ 𝒢, 0 < g) → ∀ (α β : ℕ) (G : MvPolynomial (Fin 4) ℤ), 10 ≤ 2 * α + 3 * β →
      (∀ m ∈ G.support, m 0 + m 1 = α ∧ m 2 + m 3 = β) →
      Irreducible (MvPolynomial.map (Int.castRingHom ℚ) G) →
      (({q : ℕ × ℕ × ℕ × ℕ | ((D < (q.1 : ℝ) ∧ (q.1 : ℝ) ≤ 2 * D ∧ E < (q.2.1 : ℝ) ∧ (q.2.1 : ℝ) ≤ 2 * E ∧
            U < (q.2.2.1 : ℝ) ∧ (q.2.2.1 : ℝ) < 2 * U ∧ V < (q.2.2.2 : ℝ) ∧ (q.2.2.2 : ℝ) < 2 * V ∧
            (q.2.1 : ℤ) ^ 3 * (q.2.2.2 : ℤ) ^ 2 - (q.1 : ℤ) ^ 3 * (q.2.2.1 : ℤ) ^ 2 = h) ∧
            Nat.gcd q.1 q.2.1 ∈ 𝒢 ∧ Nat.gcd q.2.2.1 q.2.2.2 ∈ 𝒢) ∧
          ρ0 < (q.1 : ℝ) / (q.2.1 : ℝ) ∧ (q.1 : ℝ) / (q.2.1 : ℝ) ≤ ρ0 * (1 + 1 / M) ∧
          MvPolynomial.eval ![(q.1 : ℤ), (q.2.1 : ℤ), (q.2.2.2 : ℤ), (q.2.2.1 : ℤ)] G = 0} :
            Set (ℕ × ℕ × ℕ × ℕ)).ncard : ℝ) ≤
        (𝒢.card : ℝ) ^ 2 * (2 * |c| * ((2 * α + 3 * β : ℕ) : ℝ) ^ 3 *
          (1 + (Lb b1 ^ 3 * Tc c1 ^ 2) ^ ((1 : ℝ) / 10)) *
          (Real.log (max 1 (Lb b1 ^ 3 * Tc c1 ^ 2)) + ((2 * α + 3 * β : ℕ) : ℝ)))) →
StewartHyp → Gelfond →
(∀ h : ℤ, h ≠ 0 → ∀ c : ℝ, 0 < c → c < 1 → ∀ δ : ℝ, 0 < δ → δ < 1 → ∀ G : Finset ℕ, ∀ ε : ℝ, 0 < ε →
      ∃ C X0 : ℝ, 0 < C ∧ ∀ D E x : ℝ, 1 / 2 ≤ D → 1 / 2 ≤ E → 1 < x → X0 ≤ x →
        let a : ℝ := Real.log D / Real.log x;
        let b : ℝ := Real.log E / Real.log x;
        let s : ℝ := a + b;
        let t : ℝ := 1 - 3 * s / 2;
        let m : ℝ := 9 / 8 * s * t;
        let M : ℕ := ⌈x ^ ((1 + δ) * m)⌉₊;
        let U : ℝ := x ^ ((1 : ℝ) / 2) * D ^ (-(3 : ℝ) / 2);
        let V : ℝ := x ^ ((1 : ℝ) / 2) * E ^ (-(3 : ℝ) / 2);
        let ρ₀ : ℕ → ℝ := fun j => D / (2 * E) * (1 + 1 / (M : ℝ)) ^ j;
        let ω₀ : ℕ → ℝ := fun j => ρ₀ j ^ ((3 : ℝ) / 2);
        let nrm : ℝ → ℝ → ℝ := fun p q => Real.sqrt (p ^ 2 + q ^ 2);
        let L₁ : ℤ × ℤ → ℕ → ℝ := fun v j => 2 / nrm ((M : ℝ) / (4 * D) * ((v.1 : ℝ) - ρ₀ j * (v.2 : ℝ))) ((v.2 : ℝ) / (2 * E));
        let T₁ : ℤ × ℤ → ℕ → ℝ := fun w j => 2 / nrm ((M : ℝ) / (17 * V) * ((w.1 : ℝ) - ω₀ j * (w.2 : ℝ))) ((w.2 : ℝ) / (2 * U));
        c ≤ s → c ≤ t →
        ∀ j : ℕ, D / (2 * E) ≤ ρ₀ j → ρ₀ j ≤ 2 * D / E →
          ∃ v w : ℤ × ℤ, v ≠ 0 ∧ w ≠ 0 ∧
            (({q | (q ∈ SW h D E x ∧ Nat.gcd q.1 q.2.1 ∈ G ∧ Nat.gcd q.2.2.1 q.2.2.2 ∈ G) ∧
                ρ₀ j < (q.1 : ℝ) / (q.2.1 : ℝ) ∧ (q.1 : ℝ) / (q.2.1 : ℝ) ≤ ρ₀ j * (1 + 1 / (M : ℝ))} :
                Set (ℕ × ℕ × ℕ × ℕ)).ncard : ℝ) ≤
              C * x ^ ε * (1 + (L₁ v j ^ 3 * T₁ w j ^ 2) ^ ((1 : ℝ) / 10))) := by
  intro SW StewartHyp Gelfond hlow hcl hIB hIBR hstew hgel
  have hlow' := hlow hstew
  obtain ⟨cG, hcG0, hCL⟩ := hcl hgel
  obtain ⟨hSWfin, hLin1, hLin2'⟩ := hIB
  obtain ⟨cc, hBR⟩ := hIBR
  intro h hh c hc0 hc1 δ hδ0 hδ1 G ε hε
  obtain ⟨K0, κ, X7, hX7, hL7⟩ := lemma7_clean c δ |(h : ℝ)| hc0 hc1 hδ0 hδ1 (abs_nonneg _)
  set G' : Finset ℕ := G.filter (fun g => 0 < g) with hG'def
  have hG' : ∀ g ∈ G', 0 < g := fun g hg => (Finset.mem_filter.mp hg).2
  obtain ⟨C1, hC1, hL1⟩ := hLin1 h hh G ε hε
  obtain ⟨C2, hC2, hL2⟩ := hLin2' h hh G
  have hlowC : ∀ α β : ℕ, ∃ Cst : ℝ, 0 < Cst ∧ ∀ x : ℝ, 1 ≤ x → ∀ F : MvPolynomial (Fin 4) ℤ,
      1 ≤ α → 1 ≤ β → min α β = 1 → (∀ m ∈ F.support, m 0 + m 1 = α ∧ m 2 + m 3 = β) →
      Irreducible (MvPolynomial.map (Int.castRingHom ℂ) F) →
      (∀ m : Fin 4 →₀ ℕ, |((F.coeff m : ℤ) : ℝ)| ≤ x ^ ((κ : ℝ) + 1)) →
      ∀ D E ρ M : ℝ, 0 ≤ D → 0 ≤ x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ) →
        ((Spiece h G D E x ρ M F).ncard : ℝ) ≤ Cst * x ^ ε := by
    intro α β
    by_cases hab : 1 ≤ α ∧ 1 ≤ β ∧ min α β = 1
    · obtain ⟨Cst, hCst, hb⟩ := hlow' h hh G' hG' ((κ : ℝ) + 1) α β hab.1 hab.2.1 hab.2.2 ε hε
      refine ⟨Cst, hCst, fun x hx F _ _ _ hFh hFi hFc D E ρ M hD hU => ?_⟩
      obtain ⟨hfin, hbd⟩ := hb x hx F hFh hFi hFc
      rw [← Spiece_filter h G D E x ρ M F hD hU]
      refine ncard_le_of_sub _ _ ?_ hfin _ hbd
      intro q hq
      obtain ⟨⟨⟨_, _, _, _, _, _, _, _, heq⟩, hg1, hg2⟩, _, _, hev⟩ := hq
      exact ⟨hev, heq, hg1, hg2⟩
    · exact ⟨1, one_pos, fun x _ F h1 h2 h3 => absurd ⟨h1, h2, h3⟩ hab⟩
  choose Cst hCst hCstb using hlowC
  set Clow : ℝ := ∑ α ∈ Finset.range (K0 + 1), ∑ β ∈ Finset.range (K0 + 1), Cst α β with hClow
  have hClow0 : 0 ≤ Clow :=
    Finset.sum_nonneg (fun α _ => Finset.sum_nonneg (fun β _ => (hCst α β).le))
  have hCstle : ∀ α β, α ≤ K0 → β ≤ K0 → Cst α β ≤ Clow := by
    intro α β hα hβ
    have h1 : Cst α β ≤ ∑ β' ∈ Finset.range (K0 + 1), Cst α β' :=
      Finset.single_le_sum (f := fun β' => Cst α β') (fun β' _ => (hCst α β').le)
        (Finset.mem_range.mpr (by omega))
    have h2 : ∑ β' ∈ Finset.range (K0 + 1), Cst α β' ≤ Clow :=
      Finset.single_le_sum (f := fun α' => ∑ β' ∈ Finset.range (K0 + 1), Cst α' β')
        (fun α' _ => Finset.sum_nonneg (fun β' _ => (hCst α' β').le))
        (Finset.mem_range.mpr (by omega))
    linarith
  set Cb : ℝ := (24 : ℝ) ^ 3 * 152 ^ 2 with hCb
  have hCb1 : 1 ≤ Cb := by rw [hCb]; norm_num
  set Cbr : ℝ := (G'.card : ℝ) ^ 2 * (2 * |cc| * (5 * (K0 : ℝ)) ^ 3 *
    (Real.log Cb + 5 / ε + 5 * (K0 : ℝ))) with hCbr
  have hCbr0 : 0 ≤ Cbr := by
    have : 0 ≤ Real.log Cb := Real.log_nonneg hCb1
    rw [hCbr]
    positivity
  set Cp : ℝ := C1 + C2 + Clow + Cbr + 1 with hCp
  have hCp0 : 0 < Cp := by rw [hCp]; linarith
  set Hc : ℝ := Real.exp (cG * (2 * (K0 : ℝ))) with hHc
  refine ⟨(2 * (K0 : ℝ) + 1) * Cp, max (max X7 256) (max (9 * (h : ℝ) ^ 2) Hc),
    mul_pos (by positivity) hCp0, ?_⟩
  intro D E x hD hE hx hX0
  intro a b s t m M U V ρ₀ ω₀ nrm L₁ T₁ hcs hct j hj1 hj2
  have hx7 : X7 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hX0
  have hx256 : (256 : ℝ) ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hX0
  have hxh : 9 * (h : ℝ) ^ 2 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hX0
  have hxHc : Hc ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hX0
  have hx0 : 0 < x := by linarith
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have hD0 : 0 < D := by linarith
  have hE0 : 0 < E := by linarith
  obtain ⟨wp1, wp2, wp3, wp4, wp5, wp6, wp7, wp8, wp9, wp10⟩ :=
    window_params x D E c δ hx hD hE hc0 hδ0 hδ1 s t rfl rfl hcs hct M rfl
  have hMh : (M : ℝ) ≤ x ^ (1 / 2 : ℝ) := wp6 hx256
  have hxhalf : x ^ (1 / 2 : ℝ) ≤ x := by
    calc x ^ (1 / 2 : ℝ) ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
      _ = x := Real.rpow_one x
  have hMx : (M : ℝ) ≤ x := le_trans hMh hxhalf
  obtain ⟨A, B, hA, hB, C7, hC70, hC7h, hC7s, hC7v⟩ :=
    hL7 x D E (ρ₀ j) M h hx7 hD hE hh le_rfl wp1 wp2 wp3 hMx wp4 hj1 hj2
  obtain ⟨GI, hGI0, hGIh, hGIc, hGIv⟩ := homog_pkg A B C7 (x ^ κ) hC70 hC7h hC7s
  obtain ⟨k, Gs, dg, hk, -, hirr, hhom, hdeg, hcov, hht, hcase⟩ := hCL GI A B hGI0 hGIh
  have hht' := hht (x ^ κ) hGIc
  have hKb : ∀ i m, |(((Gs i).coeff m : ℤ) : ℝ)| ≤ x ^ ((κ : ℝ) + 1) := by
    intro i m
    have h1 := hht' i m
    have h2 : Real.exp (cG * ((A + B : ℕ) : ℝ)) ≤ Hc := by
      rw [hHc]
      apply Real.exp_le_exp.mpr
      apply mul_le_mul_of_nonneg_left _ hcG0
      push_cast
      have : (A : ℝ) ≤ K0 := by exact_mod_cast hA
      have : (B : ℝ) ≤ K0 := by exact_mod_cast hB
      linarith
    have h3 : x ^ ((κ : ℝ) + 1) = x ^ κ * x := by
      rw [Real.rpow_add hx0, Real.rpow_natCast, Real.rpow_one]
    rw [h3]
    have h4 : 0 ≤ x ^ κ := by positivity
    calc |(((Gs i).coeff m : ℤ) : ℝ)| ≤ Real.exp (cG * ((A + B : ℕ) : ℝ)) * x ^ κ := h1
      _ ≤ Hc * x ^ κ := mul_le_mul_of_nonneg_right h2 h4
      _ ≤ x * x ^ κ := mul_le_mul_of_nonneg_right hxHc h4
      _ = x ^ κ * x := by ring
  have hM1 : (1 : ℝ) ≤ (M : ℝ) := wp5
  have h3hM : 3 * |(h : ℝ)| * (M : ℝ) ≤ x := three_h_M x (h : ℝ) (M : ℝ) hx0 hxh hMh (Nat.cast_nonneg _)
  obtain ⟨b1, c1, hb1ne, hc1ne, hb3⟩ := hBR D E x (M : ℝ) (ρ₀ j) hD hE hx hM1 hj1 hj2 h hh h3hM
  have hU0 : 0 < x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ) := by positivity
  have hV0 : 0 < x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ) := by positivity
  have hkL : 0 < (M : ℝ) / (4 * D) := by positivity
  have hkT : 0 < (M : ℝ) / (17 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ))) := by positivity
  have hLbp : 0 < L₁ b1 j := vec_len_pos_gen ((M : ℝ) / (4 * D)) (2 * E) (ρ₀ j) hkL (by positivity) b1 hb1ne
  have hTcp : 0 < T₁ c1 j := vec_len_pos_gen ((M : ℝ) / (17 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ))))
    (2 * (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ))) (ρ₀ j ^ (3 / 2 : ℝ)) hkT (by positivity) c1 hc1ne
  have hLb24 : L₁ b1 j ≤ 24 * x := by
    have hv : L₁ b1 j ≤ 2 / ((M : ℝ) / (4 * D)) + 2 * (2 * E) :=
      vec_len_le_gen ((M : ℝ) / (4 * D)) (2 * E) (ρ₀ j) hkL (by positivity) b1 hb1ne
    have e1 : 2 / ((M : ℝ) / (4 * D)) ≤ 8 * D := by
      rw [div_le_iff₀ hkL]
      have : 8 * D * ((M : ℝ) / (4 * D)) = 2 * M := by field_simp; ring
      rw [this]
      linarith
    linarith
  have hTc152 : T₁ c1 j ≤ 152 * x := by
    have hv : T₁ c1 j ≤ 2 / ((M : ℝ) / (17 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ)))) +
        2 * (2 * (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ))) :=
      vec_len_le_gen ((M : ℝ) / (17 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ))))
        (2 * (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ))) (ρ₀ j ^ (3 / 2 : ℝ)) hkT (by positivity) c1 hc1ne
    have e1 : 2 / ((M : ℝ) / (17 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ)))) ≤
        34 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ)) := by
      rw [div_le_iff₀ hkT]
      have : 34 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ)) *
          ((M : ℝ) / (17 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ)))) = 2 * M := by
        field_simp; ring
      rw [this]
      linarith
    linarith
  have hYnn : 0 ≤ L₁ b1 j ^ 3 * T₁ c1 j ^ 2 := by
    have := hLbp.le
    have := hTcp.le
    positivity
  have hYb : L₁ b1 j ^ 3 * T₁ c1 j ^ 2 ≤ Cb * x ^ 5 := by
    have a1 : L₁ b1 j ^ 3 ≤ (24 * x) ^ 3 := pow_le_pow_left₀ hLbp.le hLb24 3
    have a2 : T₁ c1 j ^ 2 ≤ (152 * x) ^ 2 := pow_le_pow_left₀ hTcp.le hTc152 2
    calc L₁ b1 j ^ 3 * T₁ c1 j ^ 2 ≤ (24 * x) ^ 3 * (152 * x) ^ 2 :=
          mul_le_mul a1 a2 (pow_nonneg hTcp.le 2) (pow_nonneg (by linarith) 3)
      _ = Cb * x ^ 5 := by rw [hCb]; ring
  have hxe : 1 ≤ x ^ ε := Real.one_le_rpow hx1 hε.le
  have hP1 : 1 ≤ 1 + (L₁ b1 j ^ 3 * T₁ c1 j ^ 2) ^ ((1 : ℝ) / 10) := by
    have := Real.rpow_nonneg hYnn ((1 : ℝ) / 10)
    linarith
  have hbase : ∀ Z : ℝ, Z ≤ Cp →
      Z * x ^ ε ≤ Cp * x ^ ε * (1 + (L₁ b1 j ^ 3 * T₁ c1 j ^ 2) ^ ((1 : ℝ) / 10)) := by
    intro Z hZ
    have h1 : Z * x ^ ε ≤ Cp * x ^ ε := mul_le_mul_of_nonneg_right hZ (by linarith)
    have h2 : 0 ≤ Cp * x ^ ε := mul_nonneg hCp0.le (by linarith)
    nlinarith
  have hRHS0 : 0 ≤ Cp * x ^ ε * (1 + (L₁ b1 j ^ 3 * T₁ c1 j ^ 2) ^ ((1 : ℝ) / 10)) :=
    mul_nonneg (mul_nonneg hCp0.le (by linarith)) (by linarith)
  have hpiece : ∀ i, ((Spiece h G D E x (ρ₀ j) (M : ℝ) (Gs i)).ncard : ℝ) ≤
      Cp * x ^ ε * (1 + (L₁ b1 j ^ 3 * T₁ c1 j ^ 2) ^ ((1 : ℝ) / 10)) := by
    intro i
    obtain ⟨hdA, hdB⟩ := hdeg i
    rcases hcase i with ⟨_, _, hz⟩ | ⟨_, _, hz⟩ | ⟨_, p0, q0, hpq, hF⟩ | ⟨_, p0, q0, hpq, hF⟩ |
        ⟨h1, h2, h3, hirrC⟩ | ⟨h1, h2, hirrQ⟩
    · refine le_trans (ncard_le_of_sub _ (∅ : Set (ℕ × ℕ × ℕ × ℕ)) ?_ Set.finite_empty 0 (by simp)) hRHS0
      intro q hq
      obtain ⟨⟨⟨hd1, _⟩, _⟩, _, _, hev⟩ := hq
      have h0 : (q.1 : ℤ) = 0 := (hz _ hev).1
      have h0' : (q.1 : ℝ) = 0 := by exact_mod_cast h0
      exact absurd hd1 (by rw [h0']; linarith)
    · refine le_trans (ncard_le_of_sub _ (∅ : Set (ℕ × ℕ × ℕ × ℕ)) ?_ Set.finite_empty 0 (by simp)) hRHS0
      intro q hq
      obtain ⟨⟨⟨_, _, _, _, _, _, hv1, _⟩, _⟩, _, _, hev⟩ := hq
      have h0 : (q.2.2.2 : ℤ) = 0 := (hz _ hev).1
      have h0' : (q.2.2.2 : ℝ) = 0 := by exact_mod_cast h0
      exact absurd hv1 (by rw [h0']; linarith)
    · obtain ⟨hfin1, hbd1⟩ := hL1 D E x hD hE hx p0 q0 hpq
      refine le_trans (ncard_le_of_sub _ _ ?_ hfin1 _ hbd1) (hbase C1 (by rw [hCp]; linarith))
      intro q hq
      obtain ⟨⟨hw, hg1, hg2⟩, _, _, hev⟩ := hq
      rw [hF] at hev
      refine ⟨hw, ?_, hg1⟩
      simpa using hev
    · obtain ⟨hfin2, hbd2⟩ := hL2 D E x hD hE hx p0 q0 hpq
      refine le_trans (ncard_le_of_sub _ _ ?_ hfin2 _ hbd2) ?_
      · intro q hq
        obtain ⟨⟨hw, hg1, hg2⟩, _, _, hev⟩ := hq
        rw [hF] at hev
        refine ⟨hw, ?_, hg1, hg2⟩
        simpa using hev
      · exact le_trans (le_mul_of_one_le_right hC2.le hxe) (hbase C2 (by rw [hCp]; linarith))
    · have hb := hCstb (dg i).1 (dg i).2 x hx1 (Gs i) h1 h2 h3 (hhom i) hirrC (hKb i) D E (ρ₀ j)
        (M : ℝ) hD0.le hU0.le
      refine le_trans hb (hbase _ ?_)
      have := hCstle (dg i).1 (dg i).2 (by omega) (by omega)
      rw [hCp]
      linarith
    · have h10 : 10 ≤ 2 * (dg i).1 + 3 * (dg i).2 := by omega
      have hbo := hb3 G' hG' (dg i).1 (dg i).2 (Gs i) h10 (hhom i) hirrQ
      rw [← Spiece_filter h G D E x (ρ₀ j) (M : ℝ) (Gs i) hD0.le hU0.le]
      refine le_trans hbo ?_
      have hd5 : (((2 * (dg i).1 + 3 * (dg i).2 : ℕ)) : ℝ) ≤ 5 * (K0 : ℝ) := by
        have : 2 * (dg i).1 + 3 * (dg i).2 ≤ 5 * K0 := by omega
        exact_mod_cast this
      exact bridge_finish (G'.card : ℝ) cc _ (K0 : ℝ) ε x (L₁ b1 j ^ 3 * T₁ c1 j ^ 2) Cb Cp
        (Nat.cast_nonneg _) hd5 hYnn hCb1 hx1 hε hYb (by rw [hCp]; linarith)
  have hfinP : ∀ i, (Spiece h G D E x (ρ₀ j) (M : ℝ) (Gs i)).Finite := by
    intro i
    refine (hSWfin h hh D E x hD hE hx).subset ?_
    intro q hq
    obtain ⟨⟨hw, _, _⟩, _⟩ := hq
    exact hw
  have hcovS : ∀ q ∈ Sint h G D E x (ρ₀ j) (M : ℝ),
      ∃ i, q ∈ Spiece h G D E x (ρ₀ j) (M : ℝ) (Gs i) := by
    intro q hq
    obtain ⟨⟨⟨hd1, hd2, he1, he2, hu1, hu2, hv1, hv2, heq⟩, hg1, hg2⟩, hr1', hr2'⟩ := hq
    have he0 : q.2.1 ≠ 0 := by
      have : (0 : ℝ) < q.2.1 := by linarith
      have : 0 < q.2.1 := by exact_mod_cast this
      omega
    have hu0 : q.2.2.1 ≠ 0 := by
      have : (0 : ℝ) < q.2.2.1 := lt_trans hU0 hu1
      have : 0 < q.2.2.1 := by exact_mod_cast this
      omega
    have heqR : (q.2.1 : ℝ) ^ 3 * (q.2.2.2 : ℝ) ^ 2 - (q.1 : ℝ) ^ 3 * (q.2.2.1 : ℝ) ^ 2 = (h : ℝ) := by
      have := congrArg (fun z : ℤ => (z : ℝ)) heq
      push_cast at this
      exact this
    have h7 := hC7v ![q.1, q.2.1, q.2.2.2, q.2.2.1]
      ⟨hd1, hd2, he1, he2, hu1, hu2, hv1, hv2, hr1', hr2', heqR⟩
    have hz := hGIv q.1 q.2.1 q.2.2.2 q.2.2.1 he0 hu0 h7
    obtain ⟨i, hi⟩ := hcov _ hz
    exact ⟨i, ⟨⟨hd1, hd2, he1, he2, hu1, hu2, hv1, hv2, heq⟩, hg1, hg2⟩, hr1', hr2', hi⟩
  refine ⟨b1, c1, hb1ne, hc1ne, ?_⟩
  have key := cover_bound (Sint h G D E x (ρ₀ j) (M : ℝ)) k
    (fun i => Spiece h G D E x (ρ₀ j) (M : ℝ) (Gs i)) hfinP hcovS _ hpiece
  have hkK : (k : ℝ) ≤ 2 * (K0 : ℝ) + 1 := by
    have : k ≤ 2 * K0 + 1 := by omega
    exact_mod_cast this
  calc _ ≤ (k : ℝ) * (Cp * x ^ ε * (1 + (L₁ b1 j ^ 3 * T₁ c1 j ^ 2) ^ ((1 : ℝ) / 10))) := key
    _ ≤ (2 * (K0 : ℝ) + 1) * (Cp * x ^ ε * (1 + (L₁ b1 j ^ 3 * T₁ c1 j ^ 2) ^ ((1 : ℝ) / 10))) :=
        mul_le_mul_of_nonneg_right hkK hRHS0
    _ = (2 * (K0 : ℝ) + 1) * Cp * x ^ ε * (1 + (L₁ b1 j ^ 3 * T₁ c1 j ^ 2) ^ ((1 : ℝ) / 10)) := by
        ring

end C07

end JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure
