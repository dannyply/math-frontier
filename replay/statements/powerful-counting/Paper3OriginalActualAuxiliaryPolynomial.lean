import Mathlib

theorem JocelynWorkspace.Formalization.PowerfulCounting.Paper3OriginalActualAuxiliaryPolynomial.JocelynClaims.claim_1d348efff0ed2d7d1daabd2d1147ea25df132caf1901a51df249fe2af2a5231b :
∀ (c δ hcap : ℝ), 0 < c → c < 1 → 0 < δ → δ < 1 → 0 ≤ hcap →
  let B := Nat.ceil (max (4/c) (32*(1+c^(-1/2:ℝ))/(c*δ)))
  let K0 := Nat.floor (2*(B:ℝ)/c)
  let κ := 2*K0*(K0+1)^2+1
  ∃ X : ℝ, 1 < X ∧ ∀ (x D E ρ₀ : ℝ) (M : ℕ) (h : ℤ),
  let U := x^(1/2:ℝ)*D^(-3/2:ℝ)
  let V := x^(1/2:ℝ)*E^(-3/2:ℝ)
  X ≤ x → (1/2:ℝ) ≤ D → (1/2:ℝ) ≤ E → h ≠ 0 → |(h:ℝ)| ≤ hcap →
  x^c ≤ D*E → x^c ≤ U*V → x^(c^2) ≤ (M:ℝ) → (M:ℝ) ≤ x →
  (9/8:ℝ)*(1+δ)*Real.log (D*E)*Real.log (U*V)/Real.log x ≤ Real.log (M:ℝ) →
  D/(2*E) ≤ ρ₀ → ρ₀ ≤ 2*D/E →
  let ν := Real.log (U*V)/Real.log (D*E)
  let A := Nat.floor ((B:ℝ)*ν)
  let H := (A+1)*(B+1)
  let ep : Fin H ≃ (Fin (A+1) × Fin (B+1)) :=
    (Fintype.equivFinOfCardEq (by simp [H]) :
      (Fin (A+1) × Fin (B+1)) ≃ Fin H).symm
  A ≤ K0 ∧ B ≤ K0 ∧
  ∃ C : MvPolynomial (Fin 2) ℤ, C ≠ 0 ∧
    (∀ m, |((C.coeff m:ℤ):ℝ)| ≤ x^κ) ∧
    (∀ m ∈ C.support, m 0 ≤ A ∧ m 1 ≤ B) ∧
    (∀ (w : Fin 4 → ℕ), D < (w 0:ℝ) ∧ (w 0:ℝ) ≤ 2*D ∧ E < (w 1:ℝ) ∧ (w 1:ℝ) ≤ 2*E ∧
      U < (w 3:ℝ) ∧ (w 3:ℝ) < 2*U ∧ V < (w 2:ℝ) ∧ (w 2:ℝ) < 2*V ∧
      ρ₀ < (w 0:ℝ)/(w 1:ℝ) ∧ (w 0:ℝ)/(w 1:ℝ) ≤ ρ₀*(1+1/(M:ℝ)) ∧
      (w 1:ℝ)^3*(w 2:ℝ)^2-(w 0:ℝ)^3*(w 3:ℝ)^2=(h:ℝ) →
      MvPolynomial.eval₂ (Int.castRingHom ℝ)
        (![(w 0:ℝ)/(w 1:ℝ),(w 2:ℝ)/(w 3:ℝ)]) C = 0) := by sorry
