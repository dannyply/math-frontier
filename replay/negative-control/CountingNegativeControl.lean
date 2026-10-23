import Mathlib

/-!
# Comparator negative control

`counting_thm_k3` stated with the exponent `77/320` replaced by `76/320`, a stronger statement
than the one proved. Comparator must reject it as a statement mismatch.
-/

theorem JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.Erdos137Final.counting_thm_k3 :
let powerful : ℕ → Prop := fun m => ∀ p : ℕ, p.Prime → p ∣ m → p ^ 2 ∣ m;
let StewartHyp : Prop := ∀ q : ℕ, 3 ≤ q → ∀ a : Fin (q + 1) → ℤ, Finset.univ.gcd a = 1 → Squarefree (∑ i : Fin (q + 1), MvPolynomial.C (a i : ℚ) * MvPolynomial.X (0 : Fin 2) ^ (i : ℕ) * MvPolynomial.X (1 : Fin 2) ^ (q - (i : ℕ))) → ∀ m : ℤ, m ≠ 0 → {rs : ℤ × ℤ | Int.gcd rs.1 rs.2 = 1 ∧ ∑ i : Fin (q + 1), a i * rs.1 ^ (i : ℕ) * rs.2 ^ (q - (i : ℕ)) = m}.encard ≤ ((2800 * q ^ (1 + m.natAbs.primeFactors.card) : ℕ) : ℕ∞);
let CCDN12 : ℝ → Prop := fun c => (∀ d : ℕ, 1 ≤ d → ∀ I : Ideal (MvPolynomial (Fin 12) ℚ), I.IsPrime →
      ringKrullDim (MvPolynomial (Fin 12) ℚ ⧸ I) = 1 →
      (∃ e : ℤ, ∃ s₀ : ℕ, ∀ s : ℕ, s₀ ≤ s →
        (Module.finrank ℚ (Submodule.map (Ideal.Quotient.mkₐ ℚ I).toLinearMap
          (MvPolynomial.restrictTotalDegree (Fin 12) ℚ s)) : ℤ) = (d : ℤ) * (s : ℤ) + e) →
      ∀ B : ℝ, 1 ≤ B →
        ((({P : Fin 12 → ℤ | (∀ f ∈ I, MvPolynomial.eval (fun i => (P i : ℚ)) f = 0) ∧
            ∀ i, |(P i : ℝ)| ≤ B} : Set (Fin 12 → ℤ)).ncard : ℕ) : ℝ) ≤
          c * (d : ℝ) ^ 3 * B ^ ((1 : ℝ) / (d : ℝ)) * (Real.log B + (d : ℝ)));
let Gelfond : Prop := (∀ n : ℕ, ∃ c : ℝ, 0 ≤ c ∧ ∀ (F G : MvPolynomial (Fin n) ℤ), F ≠ 0 → G ∣ F →
  ∀ H : ℝ, (∀ m, |((F.coeff m : ℤ) : ℝ)| ≤ H) →
    ∀ m, |((G.coeff m : ℤ) : ℝ)| ≤ Real.exp (c * (F.totalDegree : ℝ)) * H);
StewartHyp → (∃ c : ℝ, CCDN12 c) → Gelfond →
  (∀ k : ℕ, 3 ≤ k → ∀ ε : ℝ, 0 < ε → ∃ C X0 : ℝ, 0 < C ∧ 1 ≤ X0 ∧ ∀ x : ℝ, X0 ≤ x →
    (({n : ℕ | (n : ℝ) ≤ x ∧ powerful (Finset.prod (Finset.Icc 1 k) (fun i => n + i))} : Set ℕ).ncard : ℝ) ≤ C * x ^ ((76 : ℝ) / 320 + ε)) ∧
  (∀ k : ℕ, 3 ≤ k → ∀ ε : ℝ, 0 < ε → ∃ C X0 : ℝ, 0 < C ∧ 1 ≤ X0 ∧ ∀ x : ℝ, X0 ≤ x →
    (({n : ℕ | (n : ℝ) ≤ x ∧ powerful (Finset.prod (Finset.Icc 1 k) (fun i => n + i)) ∧ ∀ i ∈ Finset.Icc 1 3, ((n : ℝ) + 3) ^ ((19 : ℝ) / 100) < ((∏ p ∈ (n + i).primeFactors with k ≤ p ∧ Odd ((n + i).factorization p), p : ℕ) : ℝ) ∧ ((∏ p ∈ (n + i).primeFactors with k ≤ p ∧ Odd ((n + i).factorization p), p : ℕ) : ℝ) < ((n : ℝ) + 3) ^ ((21 : ℝ) / 100)} : Set ℕ).ncard : ℝ) ≤ C * x ^ ((38059 : ℝ) / 160000 + ε)) := by sorry
