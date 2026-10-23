import Mathlib

theorem JocelynWorkspace.Erdos137.WidthThree.CentralSet.SmallGapExclusion.small_gap_exclusion : ∀ (n f1 f2 f3 d1 d2 d3 u1 u2 u3 : ℕ), 1 ≤ n →
      (∀ p : ℕ, p.Prime → p ∣ (n + 1) * (n + 2) * (n + 3) → p ^ 2 ∣ (n + 1) * (n + 2) * (n + 3)) →
      (f1 = 1 ∨ f1 = 2) → (f2 = 1 ∨ f2 = 2) → (f3 = 1 ∨ f3 = 2) →
      Odd d1 → Squarefree d1 → Odd d2 → Squarefree d2 → Odd d3 → Squarefree d3 →
      n + 1 = f1 * d1 ^ 3 * u1 ^ 2 → n + 2 = f2 * d2 ^ 3 * u2 ^ 2 → n + 3 = f3 * d3 ^ 3 * u3 ^ 2 →
      (n + 3) ^ 19 < d1 ^ 100 → d1 ^ 100 < (n + 3) ^ 21 →
      (n + 3) ^ 19 < d2 ^ 100 → d2 ^ 100 < (n + 3) ^ 21 →
      (n + 3) ^ 19 < d3 ^ 100 → d3 ^ 100 < (n + 3) ^ 21 →
      ¬ (max |(d1 : ℝ) - (d2 : ℝ)| |(d3 : ℝ) - (d2 : ℝ)| ≤ ((n + 3 : ℕ) : ℝ) ^ ((32 : ℝ) / 1000)) := by sorry
