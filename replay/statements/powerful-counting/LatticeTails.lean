import Mathlib

theorem JocelynWorkspace.Formalization.PowerfulCounting.LatticeTails.JocelynClaims.claim_d31e9b77d0f9dd7614934ea632cc8dcd6919398027eb82ef33c69bc75aa5c7c7 :
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
  StrictMono ρ₀ ∧ J.Finite ∧ (J.ncard : ℝ) ≤ 3 * M + 1 ∧
  (∀ b : ℕ → ℤ × ℤ, (∀ j ∈ J, b j ≠ 0) → ∀ L : ℝ, 32 * (D + E) / M ≤ L →
    (({j : ℕ | j ∈ J ∧ L ≤ L₁ b j} : Set ℕ).ncard : ℝ) ≤ 720 * (D * E) / L ^ 2) ∧
  (∀ c : ℕ → ℤ × ℤ, (∀ j ∈ J, c j ≠ 0) → ∀ T : ℝ, 194 * (U + V) / M ≤ T →
    (({j : ℕ | j ∈ J ∧ T ≤ T₁ c j} : Set ℕ).ncard : ℝ) ≤ 7000 * (U * V) / T ^ 2) := by sorry
