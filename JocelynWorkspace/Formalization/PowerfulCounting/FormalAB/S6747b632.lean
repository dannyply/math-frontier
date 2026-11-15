-- Source SHA-256: a52e2d20eed234db046bd163ea11f8d117a4c54923b972c301dea2a6b2a812d5
import Mathlib
import JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.LemmaP

namespace FormalAB.S6747b632

set_option maxHeartbeats 1000000
set_option linter.all false
  
namespace A1ArithmeticInterface

abbrev QPair := ℚ × ℚ
abbrev ZPair := Fin 2 → ℤ

def qmul (Δ : ℤ) (u v : QPair) : QPair :=
  (u.1 * v.1 + (Δ : ℚ) * u.2 * v.2, u.1 * v.2 + u.2 * v.1)

def qpow (Δ : ℤ) (u : QPair) : ℕ → QPair
  | 0 => (1, 0)
  | k + 1 => qmul Δ (qpow Δ u k) u

def qnorm (Δ : ℤ) (u : QPair) : ℚ := u.1 ^ 2 - (Δ : ℚ) * u.2 ^ 2

def absNorm (Δ : ℤ) (u : QPair) : ℝ := |(qnorm Δ u : ℝ)|

def linear (p q : QPair) (y : ZPair) : QPair :=
  (p.1 * (y 0 : ℚ) + q.1 * (y 1 : ℚ),
   p.2 * (y 0 : ℚ) + q.2 * (y 1 : ℚ))

def height (y : ZPair) : ℝ := max |(y 0 : ℝ)| |(y 1 : ℝ)|

def primitive (y : ZPair) : Prop := Int.gcd (y 0) (y 1) = 1

def biformEval (c : Fin 4 → Fin 3 → ℤ) (y x : ZPair) : ℤ :=
  ∑ i : Fin 4, ∑ j : Fin 3,
    c i j * y 0 ^ (i : ℕ) * y 1 ^ (3 - (i : ℕ)) *
      x 0 ^ (j : ℕ) * x 1 ^ (2 - (j : ℕ))

structure CoverType (Δ : ℤ) where
  gamma : QPair
  p : QPair
  q : QPair
  r : QPair
  s : QPair
  rhs : ℤ
  coeff : Fin 4 → Fin 3 → ℤ
  gamma_norm_ne_zero : qnorm Δ gamma ≠ 0
  ybasis_det_ne_zero : p.1 * q.2 - p.2 * q.1 ≠ 0
  xbasis_det_ne_zero : r.1 * s.2 - r.2 * s.1 ≠ 0
  rhs_pos : 0 < rhs
  coeff_ne_zero : ∃ i j, coeff i j ≠ 0
  coefficient_identity : ∀ y x : ZPair,
    (biformEval coeff y x : ℚ) = (rhs : ℚ) *
      (qmul Δ gamma (qmul Δ (qpow Δ (linear p q y) 3)
        (qpow Δ (linear r s x) 2))).2

end A1ArithmeticInterface
namespace A1ArithmeticInterface
def qcoeff (Δ : ℤ) (gamma p q r s : QPair) (i : Fin 4) (j : Fin 3) : ℚ :=
  (Nat.choose 3 (i : ℕ) : ℚ) * (Nat.choose 2 (j : ℕ) : ℚ) *
    (qmul Δ gamma (qmul Δ
      (qmul Δ (qpow Δ p (i : ℕ)) (qpow Δ q (3 - (i : ℕ))))
      (qmul Δ (qpow Δ r (j : ℕ)) (qpow Δ s (2 - (j : ℕ)))))).2

def qbiformEval (c : Fin 4 → Fin 3 → ℚ) (y x : ZPair) : ℚ :=
  ∑ i : Fin 4, ∑ j : Fin 3,
    c i j * (y 0 : ℚ) ^ (i : ℕ) * (y 1 : ℚ) ^ (3 - (i : ℕ)) *
      (x 0 : ℚ) ^ (j : ℕ) * (x 1 : ℚ) ^ (2 - (j : ℕ))

theorem qcoeff_identity (Δ : ℤ) (gamma p q r s : QPair) (y x : ZPair) :
    qbiformEval (qcoeff Δ gamma p q r s) y x =
      (qmul Δ gamma (qmul Δ (qpow Δ (linear p q y) 3)
        (qpow Δ (linear r s x) 2))).2 := by
  simp only [qbiformEval, Fin.sum_univ_succ, Fin.sum_univ_zero]
  norm_num [qcoeff, qmul, qpow, linear]
  <;> ring

end A1ArithmeticInterface
namespace A1QuadraticField

theorem rational_nonsquare (Δ : ℤ) (hΔ : ¬ IsSquare Δ) :
    ∀ r : ℚ, r ^ 2 ≠ (Δ : ℚ) + 0 * r := by
  intro r hr
  apply hΔ
  apply Rat.isSquare_intCast_iff.mp
  exact ⟨r, by simpa only [zero_mul, add_zero, pow_two] using hr.symm⟩

end A1QuadraticField
noncomputable section
namespace A1AntiTraceCharts
structure Data where
  γ₁ : ℂ
  γ₂ : ℂ
  p₁ : ℂ
  q₁ : ℂ
  p₂ : ℂ
  q₂ : ℂ
  r₁ : ℂ
  s₁ : ℂ
  r₂ : ℂ
  s₂ : ℂ
  scale : ℂ
end A1AntiTraceCharts

namespace A1ArithmeticChartSupplier

open A1ArithmeticInterface
abbrev Data := A1AntiTraceCharts.Data

noncomputable def root (Δ : ℤ) : ℂ := Complex.sqrt (Δ : ℂ)

def embed (ζ : ℂ) (positive : Bool) (u : QPair) : ℂ :=
  (u.1 : ℂ) + (if positive then ζ else -ζ) * (u.2 : ℂ)

def data {Δ : ℤ} (ζ : ℂ) (t : CoverType Δ)
    (swapY swapX : Bool) : Data :=
  let py := if swapY then t.q else t.p
  let qy := if swapY then t.p else t.q
  let rx := if swapX then t.s else t.r
  let sx := if swapX then t.r else t.s
  { γ₁ := embed ζ true t.gamma
    γ₂ := embed ζ false t.gamma
    p₁ := embed ζ true py
    q₁ := embed ζ true qy
    p₂ := embed ζ false py
    q₂ := embed ζ false qy
    r₁ := embed ζ true rx
    s₁ := embed ζ true sx
    r₂ := embed ζ false rx
    s₂ := embed ζ false sx
    scale := 2 * ζ }

end A1ArithmeticChartSupplier
end
noncomputable section

namespace A1ArithmeticToComponent

open A1ArithmeticInterface
open A1ArithmeticChartSupplier

def integerBiform (c : Fin 4 → Fin 3 → ℤ) : MvPolynomial (Fin 4) ℤ :=
  ∑ i : Fin 4, ∑ j : Fin 3,
    MvPolynomial.C (c i j) *
      MvPolynomial.X 0 ^ (i : ℕ) *
      MvPolynomial.X 1 ^ (3 - (i : ℕ)) *
      MvPolynomial.X 2 ^ (j : ℕ) *
      MvPolynomial.X 3 ^ (2 - (j : ℕ))

def yEmbeddingMatrix (d : Data) : Matrix (Fin 2) (Fin 2) ℂ :=
  ![![d.p₁, d.q₁], ![d.p₂, d.q₂]]

def xEmbeddingMatrix (d : Data) : Matrix (Fin 2) (Fin 2) ℂ :=
  ![![d.r₁, d.s₁], ![d.r₂, d.s₂]]

def ActualComponentPresentation (Δ : ℤ) (t : CoverType Δ) : Prop :=
  let ζ : ℂ := root Δ
  let d : Data := data ζ t false false
  let c : Fin 4 → Fin 3 → ℤ := t.coeff
  let scale : ℂ := d.scale / (t.rhs : ℂ)
  let F : MvPolynomial (Fin 4) ℤ := integerBiform c
  ζ ^ 2 = (Δ : ℂ) ∧ ζ ≠ 0 ∧
  d.γ₁ ≠ 0 ∧ d.γ₂ ≠ 0 ∧ scale ≠ 0 ∧
  (yEmbeddingMatrix d).det ≠ 0 ∧
  (xEmbeddingMatrix d).det ≠ 0 ∧
  d.p₁ * d.q₂ - d.p₂ * d.q₁ ≠ 0 ∧
  d.r₁ * d.s₂ - d.r₂ * d.s₁ ≠ 0 ∧
  (∃ i j, c i j ≠ 0) ∧ F ≠ 0 ∧
  (∀ y x : ZPair,
    MvPolynomial.eval ![y 0, y 1, x 0, x 1] F =
      biformEval t.coeff y x) ∧
  (∀ i : Fin 4, ∀ j : Fin 3,
    scale * (c i j : ℂ) =
      d.γ₁ *
        (Nat.choose 3 (i : ℕ) : ℂ) *
        d.p₁ ^ (i : ℕ) * d.q₁ ^ (3 - (i : ℕ)) *
        (Nat.choose 2 (j : ℕ) : ℂ) *
        d.r₁ ^ (j : ℕ) * d.s₁ ^ (2 - (j : ℕ)) -
      d.γ₂ *
        (Nat.choose 3 (i : ℕ) : ℂ) *
        d.p₂ ^ (i : ℕ) * d.q₂ ^ (3 - (i : ℕ)) *
        (Nat.choose 2 (j : ℕ) : ℂ) *
        d.r₂ ^ (j : ℕ) * d.s₂ ^ (2 - (j : ℕ)))

def ActualArithmeticComponentSupplier : Prop :=
  ∀ A B C : ℤ, 0 < A → ¬ IsSquare (B ^ 2 - 4 * A * C) →
    ∀ t : CoverType (B ^ 2 - 4 * A * C),
      ActualComponentPresentation (B ^ 2 - 4 * A * C) t

end A1ArithmeticToComponent

end

namespace A1ArithmeticToComponent

open A1ArithmeticInterface
open A1ArithmeticChartSupplier

noncomputable section

theorem actualArithmeticComponentSupplier_attempt :
    ActualArithmeticComponentSupplier := by
  classical
  intro A B C hA hdis t
  let Δ : ℤ := B ^ 2 - 4 * A * C
  let ζ : ℂ := root Δ
  let d : Data := data ζ t false false

  have unisolvence :
      ∀ a : Fin 4 → Fin 3 → ℚ,
        (∀ u v : ℤ,
          (∑ i : Fin 4, ∑ j : Fin 3,
            a i j * (u : ℚ) ^ (i : ℕ) * (v : ℚ) ^ (j : ℕ)) = 0) →
        ∀ i j, a i j = 0 := by
    intro a ha i j
    have h00 := ha 0 0
    have h01 := ha 0 1
    have h0m := ha 0 (-1)
    have h10 := ha 1 0
    have h11 := ha 1 1
    have h1m := ha 1 (-1)
    have hm0 := ha (-1) 0
    have hm1 := ha (-1) 1
    have hmm := ha (-1) (-1)
    have h20 := ha 2 0
    have h21 := ha 2 1
    have h2m := ha 2 (-1)
    norm_num [Fin.sum_univ_succ, Fin.sum_univ_zero] at h00 h01 h0m h10 h11 h1m hm0 hm1 hmm h20 h21 h2m
    have hthree : (Fin.succ (2 : Fin 3) : Fin 4) = (3 : Fin 4) := by decide
    simp only [hthree] at h10 h11 h1m hm0 hm1 hmm h20 h21 h2m
    fin_cases i <;> fin_cases j
    · change a (0 : Fin 4) (0 : Fin 3) = 0
      linear_combination (1 : ℚ) * h00
    · change a (0 : Fin 4) (1 : Fin 3) = 0
      linear_combination (1 / 2 : ℚ) * h01 + (-1 / 2 : ℚ) * h0m
    · change a (0 : Fin 4) (2 : Fin 3) = 0
      linear_combination (-1 : ℚ) * h00 + (1 / 2 : ℚ) * h01 + (1 / 2 : ℚ) * h0m
    · change a (1 : Fin 4) (0 : Fin 3) = 0
      linear_combination (-1 / 2 : ℚ) * h00 + (1 : ℚ) * h10 + (-1 / 3 : ℚ) * hm0 + (-1 / 6 : ℚ) * h20
    · change a (1 : Fin 4) (1 : Fin 3) = 0
      linear_combination (-1 / 4 : ℚ) * h01 + (1 / 4 : ℚ) * h0m + (1 / 2 : ℚ) * h11 + (-1 / 2 : ℚ) * h1m + (-1 / 6 : ℚ) * hm1 + (1 / 6 : ℚ) * hmm + (-1 / 12 : ℚ) * h21 + (1 / 12 : ℚ) * h2m
    · change a (1 : Fin 4) (2 : Fin 3) = 0
      linear_combination (1 / 2 : ℚ) * h00 + (-1 / 4 : ℚ) * h01 + (-1 / 4 : ℚ) * h0m + (-1 : ℚ) * h10 + (1 / 2 : ℚ) * h11 + (1 / 2 : ℚ) * h1m + (1 / 3 : ℚ) * hm0 + (-1 / 6 : ℚ) * hm1 + (-1 / 6 : ℚ) * hmm + (1 / 6 : ℚ) * h20 + (-1 / 12 : ℚ) * h21 + (-1 / 12 : ℚ) * h2m
    · change a (2 : Fin 4) (0 : Fin 3) = 0
      linear_combination (-1 : ℚ) * h00 + (1 / 2 : ℚ) * h10 + (1 / 2 : ℚ) * hm0
    · change a (2 : Fin 4) (1 : Fin 3) = 0
      linear_combination (-1 / 2 : ℚ) * h01 + (1 / 2 : ℚ) * h0m + (1 / 4 : ℚ) * h11 + (-1 / 4 : ℚ) * h1m + (1 / 4 : ℚ) * hm1 + (-1 / 4 : ℚ) * hmm
    · change a (2 : Fin 4) (2 : Fin 3) = 0
      linear_combination (1 : ℚ) * h00 + (-1 / 2 : ℚ) * h01 + (-1 / 2 : ℚ) * h0m + (-1 / 2 : ℚ) * h10 + (1 / 4 : ℚ) * h11 + (1 / 4 : ℚ) * h1m + (-1 / 2 : ℚ) * hm0 + (1 / 4 : ℚ) * hm1 + (1 / 4 : ℚ) * hmm
    · change a (3 : Fin 4) (0 : Fin 3) = 0
      linear_combination (1 / 2 : ℚ) * h00 + (-1 / 2 : ℚ) * h10 + (-1 / 6 : ℚ) * hm0 + (1 / 6 : ℚ) * h20
    · change a (3 : Fin 4) (1 : Fin 3) = 0
      linear_combination (1 / 4 : ℚ) * h01 + (-1 / 4 : ℚ) * h0m + (-1 / 4 : ℚ) * h11 + (1 / 4 : ℚ) * h1m + (-1 / 12 : ℚ) * hm1 + (1 / 12 : ℚ) * hmm + (1 / 12 : ℚ) * h21 + (-1 / 12 : ℚ) * h2m
    · change a (3 : Fin 4) (2 : Fin 3) = 0
      linear_combination (-1 / 2 : ℚ) * h00 + (1 / 4 : ℚ) * h01 + (1 / 4 : ℚ) * h0m + (1 / 2 : ℚ) * h10 + (-1 / 4 : ℚ) * h11 + (-1 / 4 : ℚ) * h1m + (1 / 6 : ℚ) * hm0 + (-1 / 12 : ℚ) * hm1 + (-1 / 12 : ℚ) * hmm + (-1 / 6 : ℚ) * h20 + (1 / 12 : ℚ) * h21 + (1 / 12 : ℚ) * h2m

  have evaluationClearing : ∀ u v : ℤ,
      (∑ i : Fin 4, ∑ j : Fin 3,
        (t.coeff i j : ℚ) * (u : ℚ) ^ (i : ℕ) * (v : ℚ) ^ (j : ℕ)) =
      (t.rhs : ℚ) *
        (∑ i : Fin 4, ∑ j : Fin 3,
          qcoeff Δ t.gamma t.p t.q t.r t.s i j *
            (u : ℚ) ^ (i : ℕ) * (v : ℚ) ^ (j : ℕ)) := by
    intro u v
    have he := t.coefficient_identity (![u, 1]) (![v, 1])
    rw [← qcoeff_identity] at he
    simp only [biformEval, qbiformEval] at he
    push_cast at he
    simpa using he
  let diff : Fin 4 → Fin 3 → ℚ := fun i j =>
    (t.coeff i j : ℚ) -
      (t.rhs : ℚ) * qcoeff Δ t.gamma t.p t.q t.r t.s i j
  have diffZero : ∀ i j, diff i j = 0 := by
    apply unisolvence diff
    intro u v
    change (∑ i : Fin 4, ∑ j : Fin 3,
      ((t.coeff i j : ℚ) -
        (t.rhs : ℚ) * qcoeff Δ t.gamma t.p t.q t.r t.s i j) *
        (u : ℚ) ^ (i : ℕ) * (v : ℚ) ^ (j : ℕ)) = 0
    calc
      _ = (∑ i : Fin 4, ∑ j : Fin 3,
            (t.coeff i j : ℚ) * (u : ℚ) ^ (i : ℕ) * (v : ℚ) ^ (j : ℕ)) -
          (t.rhs : ℚ) *
            (∑ i : Fin 4, ∑ j : Fin 3,
              qcoeff Δ t.gamma t.p t.q t.r t.s i j *
                (u : ℚ) ^ (i : ℕ) * (v : ℚ) ^ (j : ℕ)) := by
        simp only [sub_mul, Finset.sum_sub_distrib, Finset.mul_sum, mul_assoc]
      _ = 0 := sub_eq_zero.mpr (evaluationClearing u v)
  have coefficientClearing : ∀ i j,
      (t.coeff i j : ℚ) =
        (t.rhs : ℚ) * qcoeff Δ t.gamma t.p t.q t.r t.s i j := by
    intro i j
    exact sub_eq_zero.mp (diffZero i j)

  have integerEvaluation : ∀ y x : ZPair,
      MvPolynomial.eval ![y 0, y 1, x 0, x 1]
        (integerBiform t.coeff) = biformEval t.coeff y x := by
    intro y x
    simp [integerBiform, biformEval]
  have polynomialNonzero : integerBiform t.coeff ≠ 0 := by
    intro hF
    have zeroCoefficients : ∀ i j, (t.coeff i j : ℚ) = 0 := by
      apply unisolvence (fun i j => (t.coeff i j : ℚ))
      intro u v
      have he := integerEvaluation (![u, 1]) (![v, 1])
      rw [hF] at he
      have hz : biformEval t.coeff (![u, 1]) (![v, 1]) = 0 := by
        simpa only [map_zero] using he.symm
      have hzq : (biformEval t.coeff (![u, 1]) (![v, 1]) : ℚ) = 0 := by
        exact_mod_cast hz
      simp only [biformEval] at hzq
      push_cast at hzq
      simpa using hzq
    obtain ⟨i, j, hij⟩ := t.coeff_ne_zero
    apply hij
    exact_mod_cast zeroCoefficients i j

  have hDelta0 : Δ ≠ 0 := by
    intro hz
    apply hdis
    change IsSquare Δ
    rw [hz]
    exact ⟨0, by ring⟩
  have hζ2 : ζ ^ 2 = (Δ : ℂ) := by
    dsimp only [ζ, root]
    rw [Complex.sqrt.eq_1]
    exact Complex.cpow_nat_inv_pow (Δ : ℂ) (n := 2) (by norm_num)
  have hζ0 : ζ ≠ 0 := by
    intro hz
    have hz' : (Δ : ℂ) = 0 := by simpa [hz] using hζ2.symm
    exact hDelta0 (by exact_mod_cast hz')
  have hscale : (2 : ℂ) * ζ ≠ 0 := mul_ne_zero (by norm_num) hζ0
  have embedMul : ∀ (positive : Bool) (u v : QPair),
      embed ζ positive (qmul Δ u v) =
        embed ζ positive u * embed ζ positive v := by
    intro positive u v
    cases positive
    · dsimp [embed, qmul]
      push_cast
      linear_combination -(u.2 : ℂ) * (v.2 : ℂ) * hζ2
    · dsimp [embed, qmul]
      push_cast
      linear_combination -(u.2 : ℂ) * (v.2 : ℂ) * hζ2
  have embedPow : ∀ (positive : Bool) (u : QPair) (k : ℕ),
      embed ζ positive (qpow Δ u k) = embed ζ positive u ^ k := by
    intro positive u k
    induction k with
    | zero => simp [qpow, embed]
    | succ k ih =>
      rw [qpow, embedMul, ih, pow_succ]
  have embedNorm : ∀ u : QPair,
      embed ζ true u * embed ζ false u = (qnorm Δ u : ℂ) := by
    intro u
    dsimp [embed, qnorm]
    push_cast
    linear_combination -(u.2 : ℂ) ^ 2 * hζ2
  have embedDet : ∀ p q : QPair,
      embed ζ true p * embed ζ false q - embed ζ false p * embed ζ true q =
        -(2 * ζ) * ((p.1 * q.2 - p.2 * q.1 : ℚ) : ℂ) := by
    intro p q
    dsimp [embed]
    push_cast
    ring

  have hg : embed ζ true t.gamma * embed ζ false t.gamma ≠ 0 := by
    rw [embedNorm]
    exact_mod_cast t.gamma_norm_ne_zero
  have hγ₁ : d.γ₁ ≠ 0 := (mul_ne_zero_iff.mp hg).1
  have hγ₂ : d.γ₂ ≠ 0 := (mul_ne_zero_iff.mp hg).2
  have hyDet : d.p₁ * d.q₂ - d.p₂ * d.q₁ ≠ 0 := by
    change embed ζ true t.p * embed ζ false t.q -
      embed ζ false t.p * embed ζ true t.q ≠ 0
    rw [embedDet]
    apply mul_ne_zero (neg_ne_zero.mpr hscale)
    exact_mod_cast t.ybasis_det_ne_zero
  have hxDet : d.r₁ * d.s₂ - d.r₂ * d.s₁ ≠ 0 := by
    change embed ζ true t.r * embed ζ false t.s -
      embed ζ false t.r * embed ζ true t.s ≠ 0
    rw [embedDet]
    apply mul_ne_zero (neg_ne_zero.mpr hscale)
    exact_mod_cast t.xbasis_det_ne_zero
  have hyMatrix : (yEmbeddingMatrix d).det ≠ 0 := by
    rw [Matrix.det_fin_two]
    simpa [yEmbeddingMatrix, mul_comm] using hyDet
  have hxMatrix : (xEmbeddingMatrix d).det ≠ 0 := by
    rw [Matrix.det_fin_two]
    simpa [xEmbeddingMatrix, mul_comm] using hxDet
  have hrhs : (t.rhs : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt t.rhs_pos)
  have hcomponentScale : d.scale / (t.rhs : ℂ) ≠ 0 := by
    change (2 * ζ) / (t.rhs : ℂ) ≠ 0
    exact div_ne_zero hscale hrhs

  have embedTrace : ∀ u : QPair,
      embed ζ true u - embed ζ false u = (2 * ζ) * (u.2 : ℂ) := by
    intro u
    dsimp [embed]
    ring

  have embeddedCoefficient : ∀ i : Fin 4, ∀ j : Fin 3,
      (2 * ζ) * (qcoeff Δ t.gamma t.p t.q t.r t.s i j : ℂ) =
        embed ζ true t.gamma *
          (Nat.choose 3 (i : ℕ) : ℂ) *
          embed ζ true t.p ^ (i : ℕ) *
          embed ζ true t.q ^ (3 - (i : ℕ)) *
          (Nat.choose 2 (j : ℕ) : ℂ) *
          embed ζ true t.r ^ (j : ℕ) *
          embed ζ true t.s ^ (2 - (j : ℕ)) -
        embed ζ false t.gamma *
          (Nat.choose 3 (i : ℕ) : ℂ) *
          embed ζ false t.p ^ (i : ℕ) *
          embed ζ false t.q ^ (3 - (i : ℕ)) *
          (Nat.choose 2 (j : ℕ) : ℂ) *
          embed ζ false t.r ^ (j : ℕ) *
          embed ζ false t.s ^ (2 - (j : ℕ)) := by
    intro i j
    have ht := embedTrace (qmul Δ t.gamma (qmul Δ
      (qmul Δ (qpow Δ t.p (i : ℕ)) (qpow Δ t.q (3 - (i : ℕ))))
      (qmul Δ (qpow Δ t.r (j : ℕ)) (qpow Δ t.s (2 - (j : ℕ))))))
    simp only [embedMul, embedPow] at ht
    dsimp only [qcoeff]
    push_cast at ht ⊢
    linear_combination
      -((Nat.choose 3 (i : ℕ) : ℂ) *
        (Nat.choose 2 (j : ℕ) : ℂ)) * ht

  have actualCoefficients : ∀ i : Fin 4, ∀ j : Fin 3,
      (d.scale / (t.rhs : ℂ)) * (t.coeff i j : ℂ) =
        d.γ₁ * (Nat.choose 3 (i : ℕ) : ℂ) *
          d.p₁ ^ (i : ℕ) * d.q₁ ^ (3 - (i : ℕ)) *
          (Nat.choose 2 (j : ℕ) : ℂ) *
          d.r₁ ^ (j : ℕ) * d.s₁ ^ (2 - (j : ℕ)) -
        d.γ₂ * (Nat.choose 3 (i : ℕ) : ℂ) *
          d.p₂ ^ (i : ℕ) * d.q₂ ^ (3 - (i : ℕ)) *
          (Nat.choose 2 (j : ℕ) : ℂ) *
          d.r₂ ^ (j : ℕ) * d.s₂ ^ (2 - (j : ℕ)) := by
    intro i j
    have hc : (t.coeff i j : ℂ) =
        (t.rhs : ℂ) * (qcoeff Δ t.gamma t.p t.q t.r t.s i j : ℂ) := by
      have hh := congrArg (fun r : ℚ => (r : ℂ)) (coefficientClearing i j)
      push_cast at hh
      exact hh
    change ((2 * ζ) / (t.rhs : ℂ)) * (t.coeff i j : ℂ) = _
    rw [hc]
    calc
      ((2 * ζ) / (t.rhs : ℂ)) *
          ((t.rhs : ℂ) * (qcoeff Δ t.gamma t.p t.q t.r t.s i j : ℂ)) =
          (2 * ζ) * (qcoeff Δ t.gamma t.p t.q t.r t.s i j : ℂ) := by
        field_simp [hrhs] <;> ring
      _ = _ := embeddedCoefficient i j

  change ActualComponentPresentation Δ t
  dsimp only [ActualComponentPresentation]
  exact ⟨hζ2, hζ0, hγ₁, hγ₂, hcomponentScale, hyMatrix, hxMatrix,
    hyDet, hxDet, t.coeff_ne_zero, polynomialNonzero, integerEvaluation,
    actualCoefficients⟩

end

end A1ArithmeticToComponent

#print axioms A1ArithmeticToComponent.actualArithmeticComponentSupplier_attempt

set_option maxHeartbeats 1000000
set_option linter.all false
namespace A1XAxisCubicAlgebra
open MvPolynomial
noncomputable section

theorem independent_cubes
    (k₁ k₂ a b c d : ℂ) (hk₁ : k₁ ≠ 0) (hk₂ : k₂ ≠ 0)
    (hdet : a*d-c*b ≠ 0) :
    let U : MvPolynomial (Fin 2) ℂ := C a * X 0 + C b * X 1
    let V : MvPolynomial (Fin 2) ℂ := C c * X 0 + C d * X 1
    C k₁ * U^3 - C k₂ * V^3 ≠ 0 ∧
      Squarefree (C k₁ * U^3 - C k₂ * V^3) := by
  classical
  let U : MvPolynomial (Fin 2) ℂ := C a * X 0 + C b * X 1
  let V : MvPolynomial (Fin 2) ℂ := C c * X 0 + C d * X 1
  let F := C k₁ * U^3 - C k₂ * V^3
  have hF : F ≠ 0 := by
    intro hz
    have he : eval ![d,-c] F = k₁ * (a*d-c*b)^3 := by
      simp [F,U,V]
      ring
    have hz' : eval ![d,-c] F = 0 := by rw [hz]; simp
    exact (mul_ne_zero hk₁ (pow_ne_zero 3 hdet)) (he.symm.trans hz')
  refine ⟨hF, (squarefree_iff_no_irreducibles hF).mpr ?_⟩
  intro P hP hsq
  have hprime : Prime P := hP.prime
  have hder : ∀ i : Fin 2, P ∣ (pderiv i) F := by
    intro i
    rcases hsq with ⟨G,hG⟩
    refine ⟨2 * ((pderiv i) P) * G + P * ((pderiv i) G), ?_⟩
    rw [hG]
    simp only [pderiv_mul]
    ring
  rcases hder 0 with ⟨G₀,hG₀⟩
  rcases hder 1 with ⟨G₁,hG₁⟩
  have hUraw : P ∣ C (3*k₁*(a*d-c*b)) * U^2 := by
    refine ⟨C d * G₀ - C c * G₁, ?_⟩
    calc
      C (3*k₁*(a*d-c*b)) * U^2 =
          C d * (pderiv 0) F - C c * (pderiv 1) F := by
        simp [F,U,V,pderiv_mul,pderiv_pow,map_ofNat]
        ring
      _ = P * (C d * G₀ - C c * G₁) := by rw [hG₀,hG₁]; ring
  have hVraw : P ∣ C (3*k₂*(a*d-c*b)) * V^2 := by
    refine ⟨C b * G₀ - C a * G₁, ?_⟩
    calc
      C (3*k₂*(a*d-c*b)) * V^2 =
          C b * (pderiv 0) F - C a * (pderiv 1) F := by
        simp [F,U,V,pderiv_mul,pderiv_pow,map_ofNat]
        ring
      _ = P * (C b * G₀ - C a * G₁) := by rw [hG₀,hG₁]; ring
  have hUunit : IsUnit (C (3*k₁*(a*d-c*b)) : MvPolynomial (Fin 2) ℂ) :=
    (isUnit_iff_ne_zero.mpr (mul_ne_zero (mul_ne_zero (by norm_num) hk₁) hdet)).map C
  have hVunit : IsUnit (C (3*k₂*(a*d-c*b)) : MvPolynomial (Fin 2) ℂ) :=
    (isUnit_iff_ne_zero.mpr (mul_ne_zero (mul_ne_zero (by norm_num) hk₂) hdet)).map C
  have hPU : P ∣ U := hprime.dvd_of_dvd_pow (hUunit.dvd_mul_left.mp hUraw)
  have hPV : P ∣ V := hprime.dvd_of_dvd_pow (hVunit.dvd_mul_left.mp hVraw)
  rcases hPU with ⟨J,hJ⟩
  rcases hPV with ⟨K,hK⟩
  have hdetUnit : IsUnit (C (a*d-c*b) : MvPolynomial (Fin 2) ℂ) :=
    (isUnit_iff_ne_zero.mpr hdet).map C
  have hX₀raw : P ∣ C (a*d-c*b) * X 0 := by
    refine ⟨C d * J - C b * K, ?_⟩
    calc
      C (a*d-c*b) * X 0 = C d * U - C b * V := by simp [U,V]; ring
      _ = P * (C d * J - C b * K) := by rw [hJ,hK]; ring
  have hX₁raw : P ∣ C (a*d-c*b) * X 1 := by
    refine ⟨C a * K - C c * J, ?_⟩
    calc
      C (a*d-c*b) * X 1 = C a * V - C c * U := by simp [U,V]; ring
      _ = P * (C a * K - C c * J) := by rw [hJ,hK]; ring
  have hPX₀ : P ∣ (X 0 : MvPolynomial (Fin 2) ℂ) := hdetUnit.dvd_mul_left.mp hX₀raw
  have hPX₁ : P ∣ (X 1 : MvPolynomial (Fin 2) ℂ) := hdetUnit.dvd_mul_left.mp hX₁raw
  have hX₀P : (X 0 : MvPolynomial (Fin 2) ℂ) ∣ P :=
    hP.dvd_symm MvPolynomial.X_prime.irreducible hPX₀
  have hbad := (eval (![0,1] : Fin 2 → ℂ)).map_dvd (hX₀P.trans hPX₁)
  norm_num at hbad

end
end A1XAxisCubicAlgebra
#print axioms A1XAxisCubicAlgebra.independent_cubes

noncomputable section

namespace A1ArithmeticAxis
open A1ArithmeticInterface A1ArithmeticChartSupplier

def xAxisCoeff {Δ : ℤ} (t : CoverType Δ) (x : ZPair) (i : Fin 4) : ℤ :=
  ∑ j : Fin 3,
    t.coeff i j * x 0 ^ (j : ℕ) * x 1 ^ (2 - (j : ℕ))

def xAxisCubic {Δ : ℤ} (t : CoverType Δ) (x : ZPair) :
    MvPolynomial (Fin 2) ℤ :=
  ∑ i : Fin 4,
    MvPolynomial.C (xAxisCoeff t x i) *
      MvPolynomial.X 0 ^ (i : ℕ) *
      MvPolynomial.X 1 ^ (3 - (i : ℕ))

def ActualXAxisCubicSquarefreeStatement : Prop :=
  ∀ A B C : ℤ, 0 < A → ¬ IsSquare (B^2-4*A*C) →
    ∀ t : CoverType (B^2-4*A*C),
      ∀ x : ZPair, x ≠ 0 →
        xAxisCubic t x ≠ 0 ∧
        Squarefree
          (MvPolynomial.map (Int.castRingHom ℚ) (xAxisCubic t x))

end A1ArithmeticAxis

end

namespace A1ArithmeticAxis
open A1ArithmeticInterface A1ArithmeticChartSupplier A1ArithmeticToComponent
noncomputable section

theorem actualXAxisCubicSquarefree_attempt :
    ActualXAxisCubicSquarefreeStatement := by
  classical
  intro A B C hA hdis t x hx
  let Δ : ℤ := B^2-4*A*C
  let ζ : ℂ := root Δ
  let d : Data := data ζ t false false
  let κ : ℂ := d.scale / (t.rhs : ℂ)
  have presentation : ActualComponentPresentation Δ t :=
    actualArithmeticComponentSupplier_attempt A B C hA hdis t
  rcases presentation with
    ⟨hζ2, hζ0, hγ₁, hγ₂, hκ, hyMatrix, hxMatrix,
      hyDet, hxDet, hcoeffNonzero, hF, hEval, hcoeff⟩
  have anisotropic : ∀ u : QPair, qnorm Δ u = 0 → u = (0,0) := by
    intro u hu
    by_cases hb : u.2 = 0
    · have hs : u.1^2 = 0 := by
        simpa only [qnorm,hb,zero_pow (by norm_num : 2 ≠ 0),mul_zero,sub_zero] using hu
      have ha : u.1 = 0 := by
        have hm : u.1*u.1 = 0 := by simpa only [pow_two] using hs
        rcases mul_eq_zero.mp hm with h | h <;> exact h
      exact Prod.ext ha hb
    · exfalso
      apply A1QuadraticField.rational_nonsquare Δ hdis (u.1/u.2)
      rw [zero_mul,add_zero,div_pow]
      apply (div_eq_iff (pow_ne_zero 2 hb)).2
      dsimp only [qnorm] at hu
      linear_combination hu
  have hXpair : linear t.r t.s x ≠ (0,0) := by
    intro hz
    have hf := congrArg Prod.fst hz
    have hs := congrArg Prod.snd hz
    change t.r.1*(x 0 : ℚ)+t.s.1*(x 1 : ℚ)=0 at hf
    change t.r.2*(x 0 : ℚ)+t.s.2*(x 1 : ℚ)=0 at hs
    have hzero0 : (t.r.1*t.s.2-t.r.2*t.s.1)*(x 0 : ℚ)=0 := by
      linear_combination t.s.2*hf-t.s.1*hs
    have hzero1 : (t.r.1*t.s.2-t.r.2*t.s.1)*(x 1 : ℚ)=0 := by
      linear_combination -t.r.2*hf+t.r.1*hs
    have hx0 : (x 0 : ℚ)=0 := (mul_eq_zero.mp hzero0).resolve_left t.xbasis_det_ne_zero
    have hx1 : (x 1 : ℚ)=0 := (mul_eq_zero.mp hzero1).resolve_left t.xbasis_det_ne_zero
    apply hx
    funext i
    fin_cases i
    · exact_mod_cast hx0
    · exact_mod_cast hx1
  have hXnorm : qnorm Δ (linear t.r t.s x) ≠ 0 := by
    intro hz
    exact hXpair (anisotropic _ hz)
  have embedNorm : ∀ u : QPair,
      embed ζ true u * embed ζ false u = (qnorm Δ u : ℂ) := by
    intro u
    dsimp [embed,qnorm]
    push_cast
    linear_combination -(u.2 : ℂ)^2*hζ2
  have hX₁Identity :
      embed ζ true (linear t.r t.s x) =
        d.r₁*(x 0 : ℂ)+d.s₁*(x 1 : ℂ) := by
    dsimp [embed,linear,d,data]
    push_cast
    ring
  have hX₂Identity :
      embed ζ false (linear t.r t.s x) =
        d.r₂*(x 0 : ℂ)+d.s₂*(x 1 : ℂ) := by
    dsimp [embed,linear,d,data]
    push_cast
    ring
  have hXproduct :
      embed ζ true (linear t.r t.s x) *
        embed ζ false (linear t.r t.s x) ≠ 0 := by
    rw [embedNorm]
    exact_mod_cast hXnorm
  have hX₁ : d.r₁*(x 0 : ℂ)+d.s₁*(x 1 : ℂ) ≠ 0 := by
    rw [←hX₁Identity]
    exact (mul_ne_zero_iff.mp hXproduct).1
  have hX₂ : d.r₂*(x 0 : ℂ)+d.s₂*(x 1 : ℂ) ≠ 0 := by
    rw [←hX₂Identity]
    exact (mul_ne_zero_iff.mp hXproduct).2
  let X₁ : ℂ := d.r₁*(x 0 : ℂ)+d.s₁*(x 1 : ℂ)
  let X₂ : ℂ := d.r₂*(x 0 : ℂ)+d.s₂*(x 1 : ℂ)
  let k₁ : ℂ := d.γ₁*X₁^2
  let k₂ : ℂ := d.γ₂*X₂^2
  have hk₁ : k₁ ≠ 0 := mul_ne_zero hγ₁ (pow_ne_zero 2 hX₁)
  have hk₂ : k₂ ≠ 0 := mul_ne_zero hγ₂ (pow_ne_zero 2 hX₂)
  have axisCoefficient : ∀ i : Fin 4,
      κ*(xAxisCoeff t x i : ℂ) =
        k₁*(Nat.choose 3 (i : ℕ) : ℂ)*
          d.p₁^(i : ℕ)*d.q₁^(3-(i : ℕ)) -
        k₂*(Nat.choose 3 (i : ℕ) : ℂ)*
          d.p₂^(i : ℕ)*d.q₂^(3-(i : ℕ)) := by
    intro i
    calc
      κ*(xAxisCoeff t x i : ℂ) =
          ∑ j : Fin 3, (κ*(t.coeff i j : ℂ))*
            (x 0 : ℂ)^(j : ℕ)*(x 1 : ℂ)^(2-(j : ℕ)) := by
        simp only [xAxisCoeff]
        push_cast
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = ∑ j : Fin 3,
          (d.γ₁*(Nat.choose 3 (i : ℕ) : ℂ)*
              d.p₁^(i : ℕ)*d.q₁^(3-(i : ℕ))*
              (Nat.choose 2 (j : ℕ) : ℂ)*
              d.r₁^(j : ℕ)*d.s₁^(2-(j : ℕ)) -
            d.γ₂*(Nat.choose 3 (i : ℕ) : ℂ)*
              d.p₂^(i : ℕ)*d.q₂^(3-(i : ℕ))*
              (Nat.choose 2 (j : ℕ) : ℂ)*
              d.r₂^(j : ℕ)*d.s₂^(2-(j : ℕ)))*
            (x 0 : ℂ)^(j : ℕ)*(x 1 : ℂ)^(2-(j : ℕ)) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [hcoeff i j]
      _ = _ := by
        dsimp only [k₁,k₂,X₁,X₂]
        norm_num [Fin.sum_univ_succ,Fin.sum_univ_zero] <;> ring
  let P := xAxisCubic t x
  let Pc := MvPolynomial.map (Int.castRingHom ℂ) P
  let U : MvPolynomial (Fin 2) ℂ :=
    MvPolynomial.C d.p₁ * MvPolynomial.X 0 +
      MvPolynomial.C d.q₁ * MvPolynomial.X 1
  let V : MvPolynomial (Fin 2) ℂ :=
    MvPolynomial.C d.p₂ * MvPolynomial.X 0 +
      MvPolynomial.C d.q₂ * MvPolynomial.X 1
  have hpoly :
      MvPolynomial.C κ * Pc =
        MvPolynomial.C k₁ * U^3 - MvPolynomial.C k₂ * V^3 := by
    have hc0 := congrArg (MvPolynomial.C : ℂ →+* MvPolynomial (Fin 2) ℂ)
      (axisCoefficient (0 : Fin 4))
    have hc1 := congrArg (MvPolynomial.C : ℂ →+* MvPolynomial (Fin 2) ℂ)
      (axisCoefficient (1 : Fin 4))
    have hc2 := congrArg (MvPolynomial.C : ℂ →+* MvPolynomial (Fin 2) ℂ)
      (axisCoefficient (2 : Fin 4))
    have hc3 := congrArg (MvPolynomial.C : ℂ →+* MvPolynomial (Fin 2) ℂ)
      (axisCoefficient (3 : Fin 4))
    norm_num at hc0 hc1 hc2 hc3
    simp only [map_mul,map_sub,map_pow,map_ofNat] at hc0 hc1 hc2 hc3
    dsimp only [Pc,P,U,V]
    simp [xAxisCubic,Fin.sum_univ_succ,Fin.sum_univ_zero]
    linear_combination
      MvPolynomial.X 1^3 * hc0 +
      (MvPolynomial.X 0*MvPolynomial.X 1^2) * hc1 +
      (MvPolynomial.X 0^2*MvPolynomial.X 1) * hc2 +
      MvPolynomial.X 0^3 * hc3
  have hgeneric :=
    A1XAxisCubicAlgebra.independent_cubes k₁ k₂ d.p₁ d.q₁ d.p₂ d.q₂ hk₁ hk₂ hyDet
  change (MvPolynomial.C k₁ * U^3 - MvPolynomial.C k₂ * V^3 ≠ 0 ∧
    Squarefree (MvPolynomial.C k₁ * U^3 - MvPolynomial.C k₂ * V^3)) at hgeneric
  have hPc : Pc ≠ 0 := by
    intro hz
    apply hgeneric.1
    rw [←hpoly,hz,mul_zero]
  have hP : P ≠ 0 := by
    intro hz
    apply hPc
    simp only [Pc,hz,map_zero]
  have hPcSq : Squarefree Pc :=
    Squarefree.of_mul_right (by rw [hpoly]; exact hgeneric.2)
  refine ⟨hP,?_⟩
  let f : ℚ →+* ℂ := algebraMap ℚ ℂ
  let φ : MvPolynomial (Fin 2) ℚ →+* MvPolynomial (Fin 2) ℂ :=
    MvPolynomial.map f
  have hφinj : Function.Injective φ :=
    MvPolynomial.map_injective f (algebraMap ℚ ℂ).injective
  have hmap :
      φ (MvPolynomial.map (Int.castRingHom ℚ) P) = Pc := by
    ext m
    simp [φ,Pc,f,MvPolynomial.coeff_map]
  intro D hD
  have hDmap : φ D * φ D ∣ Pc := by
    change D * D ∣ MvPolynomial.map (Int.castRingHom ℚ) P at hD
    rcases hD with ⟨E,hE⟩
    refine ⟨φ E, ?_⟩
    calc
      Pc = φ (MvPolynomial.map (Int.castRingHom ℚ) P) := hmap.symm
      _ = φ (D * D * E) := congrArg φ hE
      _ = φ D * φ D * φ E := by simp only [map_mul]
  have hDunit : IsUnit (φ D) := hPcSq (φ D) hDmap
  rcases MvPolynomial.isUnit_iff_eq_C_of_isReduced.mp hDunit with ⟨c,hc,hDc⟩
  have hDc0 : φ D = MvPolynomial.C (f (MvPolynomial.coeff 0 D)) := by
    have he := congrArg (MvPolynomial.coeff 0) hDc
    simp [φ,MvPolynomial.coeff_map] at he
    change f (MvPolynomial.coeff 0 D) = c at he
    exact hDc.trans (congrArg MvPolynomial.C he.symm)
  have hDconst : D = MvPolynomial.C (MvPolynomial.coeff 0 D) := by
    apply hφinj
    simpa only [φ,MvPolynomial.map_C] using hDc0
  have hc0 : MvPolynomial.coeff 0 D ≠ 0 := by
    intro hz
    have hzmap : φ D = 0 := by simpa only [hz,map_zero,MvPolynomial.C_0] using hDc0
    exact hDunit.ne_zero hzmap
  rw [hDconst]
  exact (isUnit_iff_ne_zero.mpr hc0).map MvPolynomial.C

end
end A1ArithmeticAxis
#print axioms A1ArithmeticAxis.actualXAxisCubicSquarefree_attempt

namespace JocelynClaims
theorem claim_60dcdbe97b5a1e2b8583668b710b2c100e54010e5fbba95b57893ebfebd760ed :
let QPair := ℚ × ℚ
let ZPair := Fin 2 → ℤ
let qmul : ℤ → QPair → QPair → QPair := fun Δ u v =>
  (u.1*v.1+(Δ : ℚ)*u.2*v.2,u.1*v.2+u.2*v.1)
let qpow : ℤ → QPair → ℕ → QPair := fun Δ u k =>
  Nat.rec (1,0) (fun _ w => qmul Δ w u) k
let qnorm : ℤ → QPair → ℚ := fun Δ u => u.1^2-(Δ : ℚ)*u.2^2
let linear : QPair → QPair → ZPair → QPair := fun p q y =>
  (p.1*(y 0 : ℚ)+q.1*(y 1 : ℚ),p.2*(y 0 : ℚ)+q.2*(y 1 : ℚ))
let biformEval : (Fin 4 → Fin 3 → ℤ) → ZPair → ZPair → ℤ := fun coeff y x =>
  ∑ i : Fin 4, ∑ j : Fin 3,
    coeff i j*y 0^(i : ℕ)*y 1^(3-(i : ℕ))*x 0^(j : ℕ)*x 1^(2-(j : ℕ))
∀ A B C : ℤ, 0 < A → ¬ IsSquare (B^2-4*A*C) →
  ∀ gamma p q r s : QPair, ∀ rhs : ℤ, ∀ coeff : Fin 4 → Fin 3 → ℤ,
    qnorm (B^2-4*A*C) gamma ≠ 0 →
    p.1*q.2-p.2*q.1 ≠ 0 →
    r.1*s.2-r.2*s.1 ≠ 0 →
    0 < rhs →
    (∃ i j, coeff i j ≠ 0) →
    (∀ y x : ZPair,
      (biformEval coeff y x : ℚ) = (rhs : ℚ)*
        (qmul (B^2-4*A*C) gamma
          (qmul (B^2-4*A*C)
            (qpow (B^2-4*A*C) (linear p q y) 3)
            (qpow (B^2-4*A*C) (linear r s x) 2))).2) →
    ∀ x : ZPair, x ≠ 0 →
      let P : MvPolynomial (Fin 2) ℤ :=
        ∑ i : Fin 4,
          MvPolynomial.C
            (∑ j : Fin 3, coeff i j*x 0^(j : ℕ)*x 1^(2-(j : ℕ)))*
          MvPolynomial.X 0^(i : ℕ)*MvPolynomial.X 1^(3-(i : ℕ))
      P ≠ 0 ∧ Squarefree (MvPolynomial.map (Int.castRingHom ℚ) P) := by
  dsimp only
  intro A B C hA hdis gamma p q r s rhs coeff hgamma hp hq hrhs hc he x hx
  let t : A1ArithmeticInterface.CoverType (B^2-4*A*C) :=
    { gamma := gamma
      p := p
      q := q
      r := r
      s := s
      rhs := rhs
      coeff := coeff
      gamma_norm_ne_zero := hgamma
      ybasis_det_ne_zero := hp
      xbasis_det_ne_zero := hq
      rhs_pos := hrhs
      coeff_ne_zero := hc
      coefficient_identity := by
        intro y x
        exact he y x }
  have h :=
    A1ArithmeticAxis.actualXAxisCubicSquarefree_attempt
      A B C hA hdis t x hx
  simpa only [A1ArithmeticAxis.xAxisCubic,A1ArithmeticAxis.xAxisCoeff,t] using h
end JocelynClaims
#print axioms JocelynClaims.claim_60dcdbe97b5a1e2b8583668b710b2c100e54010e5fbba95b57893ebfebd760ed

namespace A1OriginalAxisCounts
open A1ArithmeticInterface

def LiteralStewartHyp : Prop :=
  ∀ q : ℕ, 3 ≤ q → ∀ a : Fin (q+1) → ℤ, Finset.univ.gcd a = 1 →
    Squarefree (∑ i : Fin (q+1), MvPolynomial.C (a i : ℚ) *
      MvPolynomial.X (0 : Fin 2)^(i : ℕ) *
      MvPolynomial.X (1 : Fin 2)^(q-(i : ℕ))) →
    ∀ m : ℤ, m ≠ 0 →
      {rs : ℤ×ℤ | Int.gcd rs.1 rs.2 = 1 ∧
        ∑ i : Fin (q+1), a i*rs.1^(i : ℕ)*rs.2^(q-(i : ℕ)) = m}.encard ≤
        ((2800*q^(1+m.natAbs.primeFactors.card) : ℕ) : ℕ∞)

def OriginalCubicFibreCountStatement : Prop :=
  LiteralStewartHyp →
  ∀ A B C : ℤ, 0 < A → ¬ IsSquare (B^2-4*A*C) →
    ∀ t : CoverType (B^2-4*A*C),
      ∃ K : ℕ, K =
        t.rhs.natAbs.divisors.card *
          (2*(2800*3^(1+t.rhs.natAbs.primeFactors.card))) ∧
        ∀ x : ZPair, x ≠ 0 →
          let S : Set (ℤ×ℤ) :=
            {uv | Int.gcd uv.1 uv.2 = 1 ∧
              biformEval t.coeff (![uv.1,uv.2]) x = t.rhs}
          S.Finite ∧ S.ncard ≤ K

def OriginalNormBoxFallbackStatement : Prop :=
  LiteralStewartHyp →
  ∀ A B C : ℤ, 0 < A → ¬ IsSquare (B^2-4*A*C) →
    ∀ t : CoverType (B^2-4*A*C),
      ∀ ε H : ℝ, 0 < ε → 1 ≤ H →
      ∃ K : ℝ, 0 < K ∧
        ∀ N D E : ℝ, 2 ≤ N →
          H⁻¹ ≤ D → H⁻¹ ≤ E → D^3*E^2 ≤ H*N^2 →
          let S : Set (ZPair×ZPair) :=
            {z | primitive z.1 ∧ primitive z.2 ∧
              biformEval t.coeff z.1 z.2 = t.rhs ∧
              height z.1^2 ≤ H*D ∧ height z.2^2 ≤ H*E}
          S.Finite ∧ (S.ncard : ℝ) ≤ K*N^ε*min D E

end A1OriginalAxisCounts

namespace A1OriginalAxisCounts
open A1ArithmeticInterface A1ArithmeticAxis
open JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure
noncomputable section

theorem original_cubic_fibre_count : OriginalCubicFibreCountStatement := by
  classical
  intro hSt A B C hA hdis t
  let K : ℕ := t.rhs.natAbs.divisors.card *
    (2*(2800*3^(1+t.rhs.natAbs.primeFactors.card)))
  refine ⟨K,rfl,?_⟩
  intro x hx
  let S : Set (ℤ×ℤ) :=
    {uv | Int.gcd uv.1 uv.2 = 1 ∧
      biformEval t.coeff (![uv.1,uv.2]) x = t.rhs}
  change S.Finite ∧ S.ncard ≤ K
  by_cases hS : S.Nonempty
  · obtain ⟨uv₀,huv₀⟩ := hS
    let a : Fin 4 → ℤ := xAxisCoeff t x
    let g : ℤ := Finset.univ.gcd a
    let b : Fin 4 → ℤ := fun i => a i / g
    have hga : ∀ i : Fin 4, g ∣ a i := by
      intro i
      exact Finset.gcd_dvd (Finset.mem_univ i)
    have hcoeff : ∀ i : Fin 4, a i = g * b i := by
      intro i
      exact (Int.mul_ediv_cancel_of_dvd (hga i)).symm
    have heval : ∀ uv : ℤ×ℤ,
        biformEval t.coeff (![uv.1,uv.2]) x =
          ∑ i : Fin 4, a i*uv.1^(i : ℕ)*uv.2^(3-(i : ℕ)) := by
      intro uv
      dsimp only [biformEval,a,xAxisCoeff]
      simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.head_cons,
        Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    let Qeval : ℤ×ℤ → ℤ := fun uv =>
      ∑ i : Fin 4, b i*uv.1^(i : ℕ)*uv.2^(3-(i : ℕ))
    have hevalScale : ∀ uv : ℤ×ℤ,
        biformEval t.coeff (![uv.1,uv.2]) x = g * Qeval uv := by
      intro uv
      rw [heval uv]
      dsimp only [Qeval]
      simp_rw [hcoeff]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    have hgDvd : g ∣ t.rhs :=
      ⟨Qeval uv₀,huv₀.2.symm.trans (hevalScale uv₀)⟩
    have hg0 : g ≠ 0 := by
      intro hz
      rw [hz,zero_dvd_iff] at hgDvd
      exact t.rhs_pos.ne' hgDvd
    have hb : Finset.univ.gcd b = 1 := by
      obtain ⟨i,hi,hai⟩ := Finset.gcd_ne_zero_iff.mp hg0
      simpa only [b,g] using
        (Finset.gcd_div_eq_one (f := a) (s := Finset.univ) hi hai)
    let Q : MvPolynomial (Fin 2) ℚ :=
      ∑ i : Fin 4, MvPolynomial.C (b i : ℚ) *
        MvPolynomial.X 0^(i : ℕ)*MvPolynomial.X 1^(3-(i : ℕ))
    have hpolyScale :
        MvPolynomial.map (Int.castRingHom ℚ) (xAxisCubic t x) =
          MvPolynomial.C (g : ℚ)*Q := by
      calc
        MvPolynomial.map (Int.castRingHom ℚ) (xAxisCubic t x) =
            ∑ i : Fin 4, MvPolynomial.C (a i : ℚ) *
              MvPolynomial.X 0^(i : ℕ)*MvPolynomial.X 1^(3-(i : ℕ)) := by
          simp [xAxisCubic,a]
        _ = MvPolynomial.C (g : ℚ)*Q := by
          dsimp only [Q]
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          rw [hcoeff i]
          push_cast
          rw [map_mul]
          ring
    have haxis := actualXAxisCubicSquarefree_attempt A B C hA hdis t x hx
    have hQsq : Squarefree Q :=
      Squarefree.of_mul_right (by rw [←hpolyScale]; exact haxis.2)
    have hgm : g*(t.rhs/g) = t.rhs := Int.mul_ediv_cancel_of_dvd hgDvd
    have hm0 : t.rhs/g ≠ 0 := by
      intro hz
      have h := hgm
      rw [hz,mul_zero] at h
      exact t.rhs_pos.ne' h.symm
    have hmDvd : t.rhs/g ∣ t.rhs := Int.ediv_dvd_of_dvd hgDvd
    have hlevel : ∀ uv ∈ S, Qeval uv = t.rhs/g := by
      intro uv huv
      apply mul_left_cancel₀ hg0
      calc
        g*Qeval uv = biformEval t.coeff (![uv.1,uv.2]) x :=
          (hevalScale uv).symm
        _ = t.rhs := huv.2
        _ = g*(t.rhs/g) := hgm.symm
    have hStAll := hSt 3 (by norm_num) b hb hQsq
    have hStDivided := hStAll (t.rhs/g) hm0
    have hLevelFinite :
        {uv : ℤ×ℤ | Int.gcd uv.1 uv.2 = 1 ∧ Qeval uv = t.rhs/g}.Finite :=
      Set.finite_of_encard_le_coe hStDivided
    have hSfin : S.Finite := hLevelFinite.subset (by
      intro uv huv
      exact ⟨huv.1,hlevel uv huv⟩)
    obtain ⟨Tf,hTfmem,hTfcard⟩ :=
      C01.PcLowdegRed.count_T Qeval 3 (by norm_num)
        hStAll t.rhs t.rhs_pos.ne'
    have hSsub : S ⊆ (↑Tf : Set (ℤ×ℤ)) := by
      intro uv huv
      apply hTfmem uv huv.1
      rw [hlevel uv huv]
      exact hmDvd
    refine ⟨hSfin,?_⟩
    calc
      S.ncard ≤ (↑Tf : Set (ℤ×ℤ)).ncard :=
        Set.ncard_le_ncard_of_injOn id (fun uv huv => hSsub huv)
          (fun _ _ _ _ h => h) (Finset.finite_toSet Tf)
      _ = Tf.card := Set.ncard_coe_finset Tf
      _ ≤ K := hTfcard
  · have hEmpty : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hS
    simp [hEmpty]

end
end A1OriginalAxisCounts
#print axioms A1OriginalAxisCounts.original_cubic_fibre_count

namespace JocelynClaims
theorem claim_527cb1df679f67f11fd73bfe9e403493f6c4372f78e8917e460bb4e16d6dcc75 :
(
  let LiteralStewartHyp : Prop := (
    ∀ q : ℕ, 3 ≤ q → ∀ a : Fin (q+1) → ℤ, Finset.univ.gcd a = 1 →
      Squarefree (∑ i : Fin (q+1), MvPolynomial.C (a i : ℚ) *
        MvPolynomial.X (0 : Fin 2)^(i : ℕ) *
        MvPolynomial.X (1 : Fin 2)^(q-(i : ℕ))) →
      ∀ m : ℤ, m ≠ 0 →
        {rs : ℤ×ℤ | Int.gcd rs.1 rs.2 = 1 ∧
          ∑ i : Fin (q+1), a i*rs.1^(i : ℕ)*rs.2^(q-(i : ℕ)) = m}.encard ≤
          ((2800*q^(1+m.natAbs.primeFactors.card) : ℕ) : ℕ∞)
  );
  LiteralStewartHyp →
  let QPair : Type := (ℚ × ℚ);
  let ZPair : Type := (Fin 2 → ℤ);
  let qmul : ℤ → QPair → QPair → QPair := (fun Δ u v =>
    (u.1*v.1+(Δ : ℚ)*u.2*v.2,u.1*v.2+u.2*v.1));
  let qpow : ℤ → QPair → ℕ → QPair := (fun Δ u k =>
    Nat.rec (1,0) (fun _ w => qmul Δ w u) k);
  let qnorm : ℤ → QPair → ℚ := (fun Δ u => u.1^2-(Δ : ℚ)*u.2^2);
  let linear : QPair → QPair → ZPair → QPair := (fun p q y =>
    (p.1*(y 0 : ℚ)+q.1*(y 1 : ℚ),p.2*(y 0 : ℚ)+q.2*(y 1 : ℚ)));
  let biformEval : (Fin 4 → Fin 3 → ℤ) → ZPair → ZPair → ℤ := (fun coeff y x =>
    ∑ i : Fin 4, ∑ j : Fin 3,
      coeff i j*y 0^(i : ℕ)*y 1^(3-(i : ℕ))*x 0^(j : ℕ)*x 1^(2-(j : ℕ)));
  ∀ A B C : ℤ, 0 < A → ¬ IsSquare (B^2-4*A*C) →
    ∀ gamma p q r s : QPair, ∀ rhs : ℤ, ∀ coeff : Fin 4 → Fin 3 → ℤ,
      qnorm (B^2-4*A*C) gamma ≠ 0 →
      p.1*q.2-p.2*q.1 ≠ 0 →
      r.1*s.2-r.2*s.1 ≠ 0 →
      0 < rhs →
      (∃ i j, coeff i j ≠ 0) →
      (∀ y x : ZPair,
        (biformEval coeff y x : ℚ) = (rhs : ℚ)*
          (qmul (B^2-4*A*C) gamma
            (qmul (B^2-4*A*C)
              (qpow (B^2-4*A*C) (linear p q y) 3)
              (qpow (B^2-4*A*C) (linear r s x) 2))).2) →
      ∃ K : ℕ, K = rhs.natAbs.divisors.card *
        (2*(2800*3^(1+rhs.natAbs.primeFactors.card))) ∧
        ∀ x : ZPair, x ≠ 0 →
          let S : Set (ℤ×ℤ) := ({uv | Int.gcd uv.1 uv.2 = 1 ∧ biformEval coeff (![uv.1,uv.2]) x = rhs});
          S.Finite ∧ S.ncard ≤ K
) := by
  dsimp only
  intro hSt A B C hA hdis gamma p q r s rhs coeff hgamma hp hq hrhs hc he
  let t : A1ArithmeticInterface.CoverType (B^2-4*A*C) :=
    { gamma := gamma
      p := p
      q := q
      r := r
      s := s
      rhs := rhs
      coeff := coeff
      gamma_norm_ne_zero := hgamma
      ybasis_det_ne_zero := hp
      xbasis_det_ne_zero := hq
      rhs_pos := hrhs
      coeff_ne_zero := hc
      coefficient_identity := by
        intro y x
        exact he y x }
  exact A1OriginalAxisCounts.original_cubic_fibre_count hSt A B C hA hdis t
end JocelynClaims
#print axioms JocelynClaims.claim_527cb1df679f67f11fd73bfe9e403493f6c4372f78e8917e460bb4e16d6dcc75
