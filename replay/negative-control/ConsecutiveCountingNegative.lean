import Mathlib
import JocelynWorkspace.Formalization.PowerfulCounting.FormalABV3

theorem JocelynWorkspace.Formalization.PowerfulCounting.ConsecutiveCounting.A13 :
(let StewartHyp : Prop := FormalAB.S94d17769.ConsecutiveCountingTargetsAB.StewartHyp;
let CCDNThm3 : Prop := FormalAB.S94d17769.ConsecutiveCountingTargetsAB.CCDNThm3;
let GelfondHyp : Prop := FormalAB.S94d17769.ConsecutiveCountingTargetsAB.GelfondHyp;
let kFull : ℕ → ℕ → Prop := fun k m => ∀ p : ℕ, p.Prime → p ∣ m → p ^ k ∣ m;
let ZkFull : ℕ → ℤ → Prop := fun k m => ∀ p : ℕ, p.Prime → (p : ℤ) ∣ m → (p : ℤ) ^ k ∣ m;
let deltaS : ℕ → ℝ → ℝ := fun s C1 => min ((1 / (1600 * (C1 + 1))) / (4 * (s : ℝ) * ((s : ℝ) + 1))) ((1 / (s : ℝ) - 49 / 400) / 2);
StewartHyp → CCDNThm3 → GelfondHyp →
∃ KH BH : ℕ → ℝ,
 (∀ H : ℕ, 1 ≤ H → 0 < KH H ∧ 0 < BH H) ∧
 (∀ s : ℕ, (s = 6 ∨ s = 8) → 0 < deltaS s (BH 1)) ∧
 (∀ H : ℕ, 1 ≤ H → ∀ A : ℕ, 1 ≤ A → ¬ IsSquare (A * H) → ∀ T : ℝ, 2 ≤ T →
  (({t : ℕ | 1 ≤ t ∧ (t : ℝ) ≤ T ∧ 1 ≤ (A : ℤ) * t ^ 2 - H ∧
    ZkFull 2 ((A : ℤ) * t ^ 2 - H)} : Set ℕ).ncard : ℝ)
   ≤ KH H * (A : ℝ) ^ BH H * T ^ ((389 : ℝ) / 1600)) ∧
 (∀ s r : ℕ, (s = 6 ∨ s = 8) → 2 ≤ r → r < s → ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ X : ℝ, 2 ≤ X →
  (({n : ℕ | 2 ≤ n ∧ (n : ℝ) ≤ X ∧ kFull s n ∧ kFull r (n - 1)} : Set ℕ).ncard : ℝ)
   ≤ C * X ^ (1 / (s : ℝ) - deltaS s (BH 1) + ε))) ∧ False := by sorry
