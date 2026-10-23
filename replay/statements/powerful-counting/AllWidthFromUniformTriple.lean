import Mathlib

theorem JocelynWorkspace.Formalization.PowerfulCounting.AllWidthFromUniformTriple.JocelynClaims.claim_2be59d9f161441036f3a5e723e095513f55f8e966c487d9815574cd2d95ecab2 :
let powerful : ℕ → Prop := fun m => ∀ p : ℕ, p.Prime → p ∣ m → p ^ 2 ∣ m;
(∃ n₀ : ℕ, ∀ n k : ℕ, n₀ ≤ n → 3 ≤ k →
    powerful (Finset.prod (Finset.Icc 1 k) (fun i => n + i)) →
    (k : ℝ) ≤ Real.exp (Real.log (n : ℝ) ^ ((7 : ℝ) / 10))) →
(∀ ε : ℝ, 0 < ε → ∃ η C : ℝ, 0 < η ∧ ∀ y : ℝ, 2 ≤ y →
    ∀ f₁ f₂ f₃ : ℕ, 1 ≤ f₁ → 1 ≤ f₂ → 1 ≤ f₃ →
    (f₁ : ℝ) ≤ y ^ η → (f₂ : ℝ) ≤ y ^ η → (f₃ : ℝ) ≤ y ^ η →
    (({N : ℕ | (N : ℝ) ≤ y ∧
        (∃ q : ℕ, 0 < q ∧ powerful q ∧ N + 1 = f₁ * q) ∧
        (∃ q : ℕ, 0 < q ∧ powerful q ∧ N + 2 = f₂ * q) ∧
        (∃ q : ℕ, 0 < q ∧ powerful q ∧ N + 3 = f₃ * q)} : Set ℕ).ncard : ℝ)
      ≤ C * y ^ ((77 : ℝ) / 320 + ε)) →
(∀ ε : ℝ, 0 < ε → ∃ C X0 : ℝ, 0 < C ∧ 1 ≤ X0 ∧ ∀ x : ℝ, X0 ≤ x →
    (({n : ℕ | (n : ℝ) ≤ x ∧ ∃ k : ℕ, 3 ≤ k ∧
      powerful (Finset.prod (Finset.Icc 1 k) (fun i => n + i))} : Set ℕ).ncard : ℝ)
      ≤ C * x ^ ((77 : ℝ) / 320 + ε)) := by sorry
