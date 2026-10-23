import Mathlib

theorem JocelynWorkspace.Formalization.PowerfulCounting.StrictWindows.JocelynClaims.claim_f0cfddddf4e562b8ee8b00a4b8f6c47db3028e8425650db4312e3bcc8f4e26ef :
∃ N : ℕ, ∃ A : ℝ, 1 ≤ A ∧ ∀ h : ℤ, h ≠ 0 → ∃ X₀ : ℝ, ∀ D E x : ℝ,
  1 / 2 ≤ D → 1 / 2 ≤ E → X₀ ≤ x →
  ∃ 𝒲 : Finset (ℝ × ℝ × ℝ), 𝒲.card ≤ N ∧
    (∀ W ∈ 𝒲, 1 / 2 ≤ W.1 ∧ 1 / 2 ≤ W.2.1 ∧ 1 < W.2.2 ∧
      D ≤ A * W.1 ∧ W.1 ≤ A * D ∧ E ≤ A * W.2.1 ∧ W.2.1 ≤ A * E ∧
      x ≤ A * W.2.2 ∧ W.2.2 ≤ A * x) ∧
    ∀ d e u v : ℕ, D < (d : ℝ) → (d : ℝ) ≤ 2 * D → E < (e : ℝ) → (e : ℝ) ≤ 2 * E →
      x / 2 < (d : ℝ) ^ 3 * (u : ℝ) ^ 2 → (d : ℝ) ^ 3 * (u : ℝ) ^ 2 ≤ 2 * x →
      (e : ℤ) ^ 3 * (v : ℤ) ^ 2 - (d : ℤ) ^ 3 * (u : ℤ) ^ 2 = h →
      ∃ W ∈ 𝒲,
        W.1 < (d : ℝ) ∧ (d : ℝ) ≤ 2 * W.1 ∧ W.2.1 < (e : ℝ) ∧ (e : ℝ) ≤ 2 * W.2.1 ∧
        W.2.2 ^ ((1 : ℝ) / 2) * W.1 ^ (-(3 : ℝ) / 2) < (u : ℝ) ∧
        (u : ℝ) < 2 * (W.2.2 ^ ((1 : ℝ) / 2) * W.1 ^ (-(3 : ℝ) / 2)) ∧
        W.2.2 ^ ((1 : ℝ) / 2) * W.2.1 ^ (-(3 : ℝ) / 2) < (v : ℝ) ∧
        (v : ℝ) < 2 * (W.2.2 ^ ((1 : ℝ) / 2) * W.2.1 ^ (-(3 : ℝ) / 2)) ∧
        (e : ℤ) ^ 3 * (v : ℤ) ^ 2 - (d : ℤ) ^ 3 * (u : ℤ) ^ 2 = h := by sorry
