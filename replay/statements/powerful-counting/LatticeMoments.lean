import Mathlib

theorem JocelynWorkspace.Formalization.PowerfulCounting.LatticeMoments.JocelynClaims.claim_de91d4e3bef4d0cbba6edddabc77ad8eded6df2ba7fc0116292af012ccd3b48a :
∀ θ : ℝ, 0 < θ → θ < 2 → ∃ C : ℝ, 0 < C ∧
∀ (D E x : ℝ), 1 / 2 ≤ D → 1 / 2 ≤ E → 1 < x →
∀ (M : ℕ), 1 ≤ M →
  let U : ℝ := x ^ ((1 : ℝ) / 2) * D ^ (-(3 : ℝ) / 2);
  let V : ℝ := x ^ ((1 : ℝ) / 2) * E ^ (-(3 : ℝ) / 2);
  let ρ₀ : ℕ → ℝ := fun j => D / (2 * E) * (1 + 1 / (M : ℝ)) ^ j;
  let ω₀ : ℕ → ℝ := fun j => ρ₀ j ^ ((3 : ℝ) / 2);
  let J : Set ℕ := {j : ℕ | D / (2 * E) ≤ ρ₀ j ∧ ρ₀ j ≤ 2 * D / E};
  let nrm : ℝ → ℝ → ℝ := fun p q => Real.sqrt (p ^ 2 + q ^ 2);
  let L₁ : (ℕ → ℤ × ℤ) → ℕ → ℝ := fun b j =>
    2 / nrm ((M : ℝ) / (4 * D) * (((b j).1 : ℝ) - ρ₀ j * ((b j).2 : ℝ))) (((b j).2 : ℝ) / (2 * E));
  let T₁ : (ℕ → ℤ × ℤ) → ℕ → ℝ := fun c j =>
    2 / nrm ((M : ℝ) / (17 * V) * (((c j).1 : ℝ) - ω₀ j * ((c j).2 : ℝ))) (((c j).2 : ℝ) / (2 * U));
  let Lst : ℝ := max ((D * E / M) ^ ((1 : ℝ) / 2)) (32 * (D + E) / M);
  let Tst : ℝ := max ((U * V / M) ^ ((1 : ℝ) / 2)) (194 * (U + V) / M);
  (∀ b : ℕ → ℤ × ℤ, (∀ j ∈ J, b j ≠ 0) → ∑ᶠ j ∈ J, L₁ b j ^ θ ≤ C * M * Lst ^ θ) ∧
  (∀ c : ℕ → ℤ × ℤ, (∀ j ∈ J, c j ≠ 0) → ∑ᶠ j ∈ J, T₁ c j ^ θ ≤ C * M * Tst ^ θ) := by sorry
