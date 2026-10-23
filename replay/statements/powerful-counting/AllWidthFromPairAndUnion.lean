import Mathlib

theorem JocelynWorkspace.Formalization.PowerfulCounting.AllWidthFromPairAndUnion.JocelynClaims.claim_fdb026ef91db27804011331a018c434c83ba1a1ce0d9de16bfd4e6f508f5c5f0 :
let powerful : ℕ → Prop := fun m => ∀ p : ℕ, p.Prime → p ∣ m → p ^ 2 ∣ m;
(∀ ε : ℝ, 0 < ε → ∃ C X0 : ℝ, 0 < C ∧ 1 ≤ X0 ∧ ∀ x : ℝ, X0 ≤ x →
    (({n : ℕ | 0 < n ∧ (n : ℝ) ≤ x ∧ powerful n ∧ powerful (n + 1)} : Set ℕ).ncard : ℝ)
      ≤ C * x ^ ((1 : ℝ) / 4 + ε)) →
(∀ ε : ℝ, 0 < ε → ∃ C X0 : ℝ, 0 < C ∧ 1 ≤ X0 ∧ ∀ x : ℝ, X0 ≤ x →
    (({n : ℕ | (n : ℝ) ≤ x ∧ ∃ k : ℕ, 3 ≤ k ∧
      powerful (Finset.prod (Finset.Icc 1 k) (fun i => n + i))} : Set ℕ).ncard : ℝ)
      ≤ C * x ^ ((77 : ℝ) / 320 + ε)) →
(∀ ε : ℝ, 0 < ε → ∃ C X0 : ℝ, 0 < C ∧ 1 ≤ X0 ∧ ∀ x : ℝ, X0 ≤ x →
    (({n : ℕ | (n : ℝ) ≤ x ∧ ∃ k : ℕ, 2 ≤ k ∧
      powerful (Finset.prod (Finset.Icc 1 k) (fun i => n + i))} : Set ℕ).ncard : ℝ)
      ≤ C * x ^ ((1 : ℝ) / 4 + ε)) := by sorry
