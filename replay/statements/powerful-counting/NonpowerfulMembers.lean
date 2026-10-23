import Mathlib

theorem JocelynWorkspace.Formalization.PowerfulCounting.NonpowerfulMembers.JocelynClaims.claim_ceda7068de057b3d0d054ad2d5782ee486080d60f8cb605131c0e153f0538465 :
let powerful : ℕ → Prop := fun m => ∀ p : ℕ, p.Prime → p ∣ m → p ^ 2 ∣ m;
(∃ n₀ : ℕ, ∀ n k : ℕ, n₀ ≤ n → 3 ≤ k →
    powerful (Finset.prod (Finset.Icc 1 k) (fun i => n + i)) →
    (k : ℝ) ≤ Real.exp (Real.log (n : ℝ) ^ ((7 : ℝ) / 10))) →
(∀ ε : ℝ, 0 < ε → ∃ C X0 : ℝ, 0 < C ∧ 1 ≤ X0 ∧ ∀ x : ℝ, X0 ≤ x →
    (({n : ℕ | (n : ℝ) ≤ x ∧ ∃ k : ℕ, 3 ≤ k ∧
      powerful (Finset.prod (Finset.Icc 1 k) (fun i => n + i))} : Set ℕ).ncard : ℝ)
      ≤ C * x ^ ((77 : ℝ) / 320 + ε)) →
(∀ ε : ℝ, 0 < ε → ∃ C X0 : ℝ, 0 < C ∧ 1 ≤ X0 ∧ ∀ x : ℝ, X0 ≤ x →
    (({z : ℕ | 0 < z ∧ (z : ℝ) ≤ x ∧ ¬ powerful z ∧
      ∃ N K : ℕ, 1 ≤ K ∧ N < z ∧ z ≤ N + K ∧
        powerful (Finset.prod (Finset.Icc 1 K) (fun i => N + i))} : Set ℕ).ncard : ℝ)
      ≤ C * x ^ ((77 : ℝ) / 320 + ε)) := by sorry
