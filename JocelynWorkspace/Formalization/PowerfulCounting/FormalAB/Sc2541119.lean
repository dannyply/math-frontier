-- Source SHA-256: 4ae0ff536180a75cf27231078e5757e86cd5525f9e71e382b680f5b3eaade0bc
import Mathlib
import JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.LemmaP

namespace FormalAB.Sc2541119

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

namespace JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure
namespace C08
namespace PcPell

open Finset
set_option maxHeartbeats 400000

noncomputable def pellBox (N : ℤ) (K : ℕ) : Finset (ℤ × ℤ) :=
  ((Icc (-(K:ℤ)) K) ×ˢ (Icc (-(K:ℤ)) K)).filter (fun p : ℤ × ℤ => p.1 ^ 2 - N * p.2 ^ 2 = 1)

lemma pow_x_ge {d : ℤ} (hd : 0 < d) (a : Pell.Solution₁ d) (hax : 2 ≤ a.x) (hay : 0 < a.y) :
    ∀ n : ℕ, (2:ℤ) ^ n ≤ (a ^ n).x ∧ 0 ≤ (a ^ n).y := by
  intro n
  induction n with
  | zero => simp
  | succ k ih =>
    obtain ⟨hx, hy⟩ := ih
    have h2k : (0:ℤ) < 2 ^ k := by positivity
    have hx0 : 0 < (a ^ k).x := lt_of_lt_of_le h2k hx
    rw [pow_succ a k, Pell.Solution₁.x_mul, Pell.Solution₁.y_mul]
    refine ⟨?_, ?_⟩
    · have h1 : 0 ≤ d * ((a ^ k).y * a.y) := mul_nonneg hd.le (mul_nonneg hy hay.le)
      have h2 : (2:ℤ) ^ k * 2 ≤ (a ^ k).x * a.x := by nlinarith
      calc (2:ℤ) ^ (k + 1) = 2 ^ k * 2 := by ring
        _ ≤ (a ^ k).x * a.x := h2
        _ ≤ (a ^ k).x * a.x + d * ((a ^ k).y * a.y) := by linarith
    · have h1 : 0 ≤ (a ^ k).x * a.y := mul_nonneg hx0.le hay.le
      have h2 : 0 ≤ (a ^ k).y * a.x := mul_nonneg hy (by linarith)
      linarith

lemma zpow_x_eq {d : ℤ} (a : Pell.Solution₁ d) (n : ℤ) : (a ^ n).x = (a ^ n.natAbs).x := by
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg n
  · simp
  · simp [zpow_neg]

theorem pellBox_card (N : ℤ) (hN : 0 < N) (K : ℕ) (hK : 1 ≤ K) :
    ((pellBox N K).card : ℝ) ≤ 4 * (Real.log K / Real.log 2) + 2 := by
  classical
  set S := pellBox N K with hS
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogK : 0 ≤ Real.log K := Real.log_nonneg (by exact_mod_cast hK)
  have hq : 0 ≤ Real.log K / Real.log 2 := div_nonneg hlogK hlog2.le
  by_cases hsq : IsSquare N
  · obtain ⟨r, hr⟩ := hsq
    have hr0 : r ≠ 0 := by
      rintro rfl
      simp at hr
      omega
    have hsub : S ⊆ {((1:ℤ), (0:ℤ)), ((-1:ℤ), (0:ℤ))} := by
      intro p hp
      rw [hS, pellBox, Finset.mem_filter] at hp
      have heq := hp.2
      rw [hr] at heq
      have hfac : (p.1 - r * p.2) * (p.1 + r * p.2) = 1 := by linear_combination heq
      rcases Int.eq_one_or_neg_one_of_mul_eq_one' hfac with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have hy : r * p.2 = 0 := by linarith
        have hy' : p.2 = 0 := (mul_eq_zero.mp hy).resolve_left hr0
        have hx : p.1 = 1 := by rw [hy'] at h1; linarith
        simp [Prod.ext_iff, hx, hy']
      · have hy : r * p.2 = 0 := by linarith
        have hy' : p.2 = 0 := (mul_eq_zero.mp hy).resolve_left hr0
        have hx : p.1 = -1 := by rw [hy'] at h1; linarith
        simp [Prod.ext_iff, hx, hy']
    have hc : S.card ≤ 2 := by
      calc S.card ≤ ({((1:ℤ), (0:ℤ)), ((-1:ℤ), (0:ℤ))} : Finset (ℤ × ℤ)).card :=
            Finset.card_le_card hsub
        _ ≤ 2 := Finset.card_le_two
    have : (S.card : ℝ) ≤ 2 := by exact_mod_cast hc
    linarith
  · obtain ⟨a, ha⟩ := Pell.IsFundamental.exists_of_not_isSquare hN hsq
    have hax : 2 ≤ a.x := ha.1
    have hay : 0 < a.y := ha.2.1
    set M : ℕ := ⌊Real.log K / Real.log 2⌋₊ with hM
    let f : ℤ × Bool → ℤ × ℤ := fun q =>
      if q.2 then ((a ^ q.1).x, (a ^ q.1).y) else (-(a ^ q.1).x, -(a ^ q.1).y)
    have hsub : S ⊆ ((Icc (-(M:ℤ)) M) ×ˢ (Finset.univ : Finset Bool)).image f := by
      intro p hp
      rw [hS, pellBox, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc] at hp
      obtain ⟨⟨⟨hx1, hx2⟩, _⟩, heq⟩ := hp
      let b : Pell.Solution₁ N := Pell.Solution₁.mk p.1 p.2 heq
      have hbx : b.x = p.1 := Pell.Solution₁.x_mk _ _ _
      have hby : b.y = p.2 := Pell.Solution₁.y_mk _ _ _
      obtain ⟨n, hn⟩ := ha.eq_zpow_or_neg_zpow b
      have hxpos : 0 < (a ^ n).x := Pell.Solution₁.x_zpow_pos ha.x_pos n
      have hgrow : (2:ℤ) ^ n.natAbs ≤ (a ^ n).x := by
        rw [zpow_x_eq]
        exact (pow_x_ge hN a hax hay n.natAbs).1
      have hpabs : |p.1| ≤ K := abs_le.mpr ⟨hx1, hx2⟩
      have habs : |p.1| = (a ^ n).x := by
        rcases hn with hn | hn
        · have h1 : p.1 = (a ^ n).x := by rw [← hbx, hn]
          rw [h1, abs_of_pos hxpos]
        · have h1 : p.1 = -(a ^ n).x := by rw [← hbx, hn, Pell.Solution₁.x_neg]
          rw [h1, abs_neg, abs_of_pos hxpos]
      have hle : (2:ℤ) ^ n.natAbs ≤ K := by linarith
      have hnM : n.natAbs ≤ M := by
        apply Nat.le_floor
        have h2 : ((2:ℝ) ^ n.natAbs) ≤ (K:ℝ) := by exact_mod_cast hle
        have h3 : Real.log ((2:ℝ) ^ n.natAbs) ≤ Real.log K :=
          Real.log_le_log (by positivity) h2
        rw [Real.log_pow] at h3
        rw [le_div_iff₀ hlog2]
        exact h3
      have hnabs : |n| ≤ (M:ℤ) := by
        rw [Int.abs_eq_natAbs]
        exact_mod_cast hnM
      have hnI : n ∈ Icc (-(M:ℤ)) M := Finset.mem_Icc.mpr (abs_le.mp hnabs)
      rw [Finset.mem_image]
      rcases hn with hn | hn
      · refine ⟨(n, true), Finset.mem_product.mpr ⟨hnI, Finset.mem_univ _⟩, ?_⟩
        simp only [f, if_true]
        rw [← hn, hbx, hby]
      · refine ⟨(n, false), Finset.mem_product.mpr ⟨hnI, Finset.mem_univ _⟩, ?_⟩
        simp only [f, Bool.false_eq_true, if_false]
        rw [← Pell.Solution₁.x_neg, ← Pell.Solution₁.y_neg, ← hn, hbx, hby]
    have hcardI : (Icc (-(M:ℤ)) M).card = 2 * M + 1 := by
      rw [Int.card_Icc]
      have : (M:ℤ) + 1 - -(M:ℤ) = ((2 * M + 1 : ℕ) : ℤ) := by push_cast; ring
      rw [this, Int.toNat_natCast]
    have hc : S.card ≤ (2 * M + 1) * 2 := by
      calc S.card ≤ (((Icc (-(M:ℤ)) M) ×ˢ (Finset.univ : Finset Bool)).image f).card :=
            Finset.card_le_card hsub
        _ ≤ ((Icc (-(M:ℤ)) M) ×ˢ (Finset.univ : Finset Bool)).card := Finset.card_image_le
        _ = (2 * M + 1) * 2 := by
            rw [Finset.card_product, hcardI, Finset.card_univ, Fintype.card_bool]
    have hMle : (M : ℝ) ≤ Real.log K / Real.log 2 := Nat.floor_le hq
    have hc' : (S.card : ℝ) ≤ ((2 * M + 1) * 2 : ℕ) := by exact_mod_cast hc
    push_cast at hc'
    linarith

lemma int_dvd_iff_zmod (X : ℤ) (h : ℤ) [NeZero h.natAbs] :
    ((X : ZMod h.natAbs) = 0) ↔ h ∣ X := by
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd, Int.natAbs_dvd]

end PcPell
end C08
end JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure

noncomputable section
namespace A1QuadraticComponents

def SignedBinaryQuadraticCountStatement : Prop :=
  ∀ h : ℤ, h ≠ 0 →
  ∀ ε : ℝ, 0 < ε →
  ∃ C : ℝ, 0 < C ∧
    ∀ H Z : ℝ, 1 ≤ H → 2 ≤ Z →
    ∀ a b c : ℤ,
      |(a : ℝ)| ≤ H → |(b : ℝ)| ≤ H → |(c : ℝ)| ≤ H →
      b ^ 2 - 4 * a * c ≠ 0 →
      let S : Set (ℤ × ℤ) :=
        {uv | Int.gcd uv.1 uv.2 = 1 ∧
          |(uv.1 : ℝ)| ≤ Z ∧ |(uv.2 : ℝ)| ≤ Z ∧
          a * uv.1 ^ 2 + b * uv.1 * uv.2 + c * uv.2 ^ 2 = h}
      S.Finite ∧ (S.ncard : ℝ) ≤ C * (H * Z) ^ ε

open JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure

set_option maxHeartbeats 2000000 in
theorem signed_binary_quadratic_count : SignedBinaryQuadraticCountStatement := by
  classical
  intro h hh ε hε
  have htwo : 2 * h ≠ 0 := mul_ne_zero (by norm_num) hh
  let m : ℕ := (2 * h).natAbs
  have hm : m ≠ 0 := Int.natAbs_ne_zero.mpr htwo
  letI : NeZero m := ⟨hm⟩
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog7 : 0 < Real.log 7 := Real.log_pos (by norm_num)
  let Aε : ℝ := 4 * (Real.log 7 / Real.log 2) + 4 + 8 / (ε * Real.log 2)
  have hAε : 0 < Aε := by dsimp only [Aε]; positivity
  refine ⟨(m : ℝ) ^ 2 * Aε + 1, by positivity, ?_⟩
  intro H Z hH hZ a b c ha hb hc hD
  let D : ℤ := b ^ 2 - 4 * a * c
  let S : Set (ℤ × ℤ) :=
    {uv | Int.gcd uv.1 uv.2 = 1 ∧
      |(uv.1 : ℝ)| ≤ Z ∧ |(uv.2 : ℝ)| ≤ Z ∧
      a * uv.1 ^ 2 + b * uv.1 * uv.2 + c * uv.2 ^ 2 = h}
  change S.Finite ∧ (S.ncard : ℝ) ≤ ((m : ℝ) ^ 2 * Aε + 1) * (H * Z) ^ ε
  have hH₀ : 0 ≤ H := by linarith
  have hZ₀ : 0 ≤ Z := by linarith
  have hHZ : 1 ≤ H * Z := by nlinarith
  have hHZ₀ : 0 < H * Z := by nlinarith
  have hZsq : 1 ≤ Z ^ 2 := by nlinarith
  have hHZsq : 1 ≤ H * Z ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hH) (sq_nonneg Z)]
  let K : ℕ := ⌈6 * H * Z ^ 2⌉₊
  have hKge : 6 * H * Z ^ 2 ≤ (K : ℝ) := Nat.le_ceil _
  have hKR : 1 ≤ (K : ℝ) := by nlinarith
  have hK : 1 ≤ K := by exact_mod_cast hKR
  have hKpos : 0 < (K : ℝ) := by linarith
  have hKupper : (K : ℝ) ≤ 7 * (H * Z) ^ 2 := by
    have hceil : (K : ℝ) < 6 * H * Z ^ 2 + 1 :=
      Nat.ceil_lt_add_one (by positivity)
    have hHsq : H ≤ H ^ 2 := by nlinarith
    have ht := mul_le_mul_of_nonneg_right hHsq (sq_nonneg Z)
    nlinarith
  have hlogK : Real.log K ≤ Real.log 7 + 2 * Real.log (H * Z) := by
    calc
      Real.log K ≤ Real.log (7 * (H * Z) ^ 2) :=
        Real.log_le_log hKpos hKupper
      _ = Real.log 7 + 2 * Real.log (H * Z) := by
        rw [Real.log_mul (by norm_num) (pow_ne_zero 2 hHZ₀.ne'),
          Real.log_pow] <;> norm_num
  let U : ℝ := 4 * (Real.log K / Real.log 2) + 4
  have hU₄ : 4 ≤ U := by
    have ht : 0 ≤ Real.log K / Real.log 2 :=
      div_nonneg (Real.log_nonneg hKR) hlog2.le
    dsimp only [U]
    linarith

  have hPellCard :
      ((C08.PcPell.pellBox D K).card : ℝ) ≤ U := by
    rcases lt_trichotomy D 0 with hneg | hzero | hpos
    · have hsub : C08.PcPell.pellBox D K ⊆
          ({((1 : ℤ), 0), ((-1 : ℤ), 0), ((0 : ℤ), 1), ((0 : ℤ), -1)} :
            Finset (ℤ × ℤ)) := by
        intro xy hxy
        have heq : xy.1 ^ 2 - D * xy.2 ^ 2 = 1 :=
          (Finset.mem_filter.mp hxy).2
        have hsq : xy.1 ^ 2 + xy.2 ^ 2 ≤ 1 := by
          nlinarith [mul_nonneg (show 0 ≤ -D - 1 by omega) (sq_nonneg xy.2)]
        have hxb : -1 ≤ xy.1 ∧ xy.1 ≤ 1 := by
          constructor <;> nlinarith [sq_nonneg xy.2]
        have hyb : -1 ≤ xy.2 ∧ xy.2 ≤ 1 := by
          constructor <;> nlinarith [sq_nonneg xy.1]
        have hx : xy.1 = -1 ∨ xy.1 = 0 ∨ xy.1 = 1 := by omega
        have hy : xy.2 = -1 ∨ xy.2 = 0 ∨ xy.2 = 1 := by omega
        rcases hx with hx | hx | hx <;> rcases hy with hy | hy | hy
        all_goals first
          | simpa [Prod.ext_iff, hx, hy]
          | exfalso; simp [hx, hy] at heq <;> omega
      have hcard : (C08.PcPell.pellBox D K).card ≤ 4 := by
        calc
          (C08.PcPell.pellBox D K).card ≤
              ({((1 : ℤ), 0), ((-1 : ℤ), 0), ((0 : ℤ), 1), ((0 : ℤ), -1)} :
                Finset (ℤ × ℤ)).card := Finset.card_le_card hsub
          _ ≤ 4 := by decide
      exact (by exact_mod_cast hcard : ((C08.PcPell.pellBox D K).card : ℝ) ≤ 4).trans hU₄
    · exact (hD hzero).elim
    · have ht := C08.PcPell.pellBox_card D hpos K hK
      dsimp only [U]
      linarith

  let Zb : ℕ := ⌈Z⌉₊
  have hZZb : Z ≤ (Zb : ℝ) := Nat.le_ceil _
  let Box : Finset (ℤ × ℤ) :=
    Finset.Icc (-(Zb : ℤ)) Zb ×ˢ Finset.Icc (-(Zb : ℤ)) Zb
  have hSbox : S ⊆ (↑Box : Set (ℤ × ℤ)) := by
    intro uv huv
    have hu : |uv.1| ≤ (Zb : ℤ) := by exact_mod_cast huv.2.1.trans hZZb
    have hv : |uv.2| ≤ (Zb : ℤ) := by exact_mod_cast huv.2.2.1.trans hZZb
    exact Finset.mem_product.mpr
      ⟨Finset.mem_Icc.mpr (abs_le.mp hu), Finset.mem_Icc.mpr (abs_le.mp hv)⟩
  have hSfin : S.Finite := (Finset.finite_toSet Box).subset hSbox
  let T : Finset (ℤ × ℤ) := hSfin.toFinset
  let label : (ℤ × ℤ) → ZMod m × ZMod m := fun uv => (uv.1, uv.2)
  let Fz : (ZMod m × ZMod m) → Finset (ℤ × ℤ) :=
    fun z => T.filter (fun uv => label uv = z)
  have hTmem : ∀ uv, uv ∈ T ↔ uv ∈ S := fun uv => hSfin.mem_toFinset

  have hfiber : ∀ z : ZMod m × ZMod m, ((Fz z).card : ℝ) ≤ U := by
    intro z
    rcases (Fz z).eq_empty_or_nonempty with hfempty | ⟨w, hw⟩
    · rw [hfempty, Finset.card_empty, Nat.cast_zero]
      linarith
    have hFmem : ∀ uv ∈ Fz z, uv ∈ S ∧ label uv = z := by
      intro uv huv
      obtain ⟨ht, hl⟩ := Finset.mem_filter.mp huv
      exact ⟨(hTmem uv).mp ht, hl⟩
    have hwS := (hFmem w hw).1
    have hwEq : a * w.1 ^ 2 + b * w.1 * w.2 + c * w.2 ^ 2 = h := hwS.2.2.2
    let P : (ℤ × ℤ) → ℤ := fun uv =>
      2 * a * uv.1 * w.1 + b * (uv.1 * w.2 + uv.2 * w.1) +
        2 * c * uv.2 * w.2
    let R : (ℤ × ℤ) → ℤ := fun uv => uv.1 * w.2 - uv.2 * w.1
    let φ : (ℤ × ℤ) → ℤ × ℤ := fun uv => (P uv / (2 * h), R uv / (2 * h))

    have hdiv : ∀ uv ∈ Fz z, 2 * h ∣ P uv ∧ 2 * h ∣ R uv := by
      intro uv huv
      have hlabels : label uv = label w :=
        (hFmem uv huv).2.trans (hFmem w hw).2.symm
      have huCast : (uv.1 : ZMod m) = (w.1 : ZMod m) :=
        congrArg Prod.fst hlabels
      have hvCast : (uv.2 : ZMod m) = (w.2 : ZMod m) :=
        congrArg Prod.snd hlabels
      have hud : 2 * h ∣ uv.1 - w.1 := by
        apply (C08.PcPell.int_dvd_iff_zmod (uv.1 - w.1) (2 * h)).mp
        simpa only [Int.cast_sub, sub_eq_zero] using huCast
      have hvd : 2 * h ∣ uv.2 - w.2 := by
        apply (C08.PcPell.int_dvd_iff_zmod (uv.2 - w.2) (2 * h)).mp
        simpa only [Int.cast_sub, sub_eq_zero] using hvCast
      have hPdiff : P uv - 2 * h =
          (2 * a * w.1 + b * w.2) * (uv.1 - w.1) +
            (b * w.1 + 2 * c * w.2) * (uv.2 - w.2) := by
        dsimp only [P]
        linear_combination 2 * hwEq
      have hPdvd : 2 * h ∣ P uv - 2 * h := by
        rw [hPdiff]
        exact dvd_add (dvd_mul_of_dvd_right hud _) (dvd_mul_of_dvd_right hvd _)
      have hPd : 2 * h ∣ P uv := by
        have he : P uv = (P uv - 2 * h) + 2 * h := by ring
        rw [he]
        exact dvd_add hPdvd (dvd_refl _)
      have hRd : 2 * h ∣ R uv := by
        have he : R uv = w.2 * (uv.1 - w.1) - w.1 * (uv.2 - w.2) := by
          dsimp only [R]
          ring
        rw [he]
        exact dvd_sub (dvd_mul_of_dvd_right hud _) (dvd_mul_of_dvd_right hvd _)
      exact ⟨hPd, hRd⟩

    have hcancel : ∀ uv ∈ Fz z,
        (2 * h) * (φ uv).1 = P uv ∧ (2 * h) * (φ uv).2 = R uv := by
      intro uv huv
      obtain ⟨hp, hr⟩ := hdiv uv huv
      exact ⟨by simpa only [φ, mul_comm] using Int.ediv_mul_cancel hp,
        by simpa only [φ, mul_comm] using Int.ediv_mul_cancel hr⟩

    have hnorm : ∀ uv ∈ Fz z, (φ uv).1 ^ 2 - D * (φ uv).2 ^ 2 = 1 := by
      intro uv huv
      have huEq := (hFmem uv huv).1.2.2.2
      have hpolar : (P uv) ^ 2 - D * (R uv) ^ 2 =
          4 * (a * uv.1 ^ 2 + b * uv.1 * uv.2 + c * uv.2 ^ 2) *
            (a * w.1 ^ 2 + b * w.1 * w.2 + c * w.2 ^ 2) := by
        dsimp only [P, R, D]
        ring
      rw [huEq, hwEq] at hpolar
      obtain ⟨hp, hr⟩ := hcancel uv huv
      apply mul_left_cancel₀ (pow_ne_zero 2 htwo)
      calc
        (2 * h) ^ 2 * ((φ uv).1 ^ 2 - D * (φ uv).2 ^ 2) =
            ((2 * h) * (φ uv).1) ^ 2 - D * ((2 * h) * (φ uv).2) ^ 2 := by ring
        _ = 4 * h * h := by rw [hp, hr, hpolar]
        _ = (2 * h) ^ 2 * 1 := by ring

    have hbounds : ∀ uv ∈ Fz z,
        |((φ uv).1 : ℝ)| ≤ (K : ℝ) ∧ |((φ uv).2 : ℝ)| ≤ (K : ℝ) := by
      intro uv huv
      have huS := (hFmem uv huv).1
      have hu : |(uv.1 : ℝ)| ≤ Z := huS.2.1
      have hv : |(uv.2 : ℝ)| ≤ Z := huS.2.2.1
      have hwu : |(w.1 : ℝ)| ≤ Z := hwS.2.1
      have hwv : |(w.2 : ℝ)| ≤ Z := hwS.2.2.1
      have hPform : (P uv : ℝ) =
          2 * (a : ℝ) * uv.1 * w.1 + (b : ℝ) * uv.1 * w.2 +
            (b : ℝ) * uv.2 * w.1 + 2 * (c : ℝ) * uv.2 * w.2 := by
        dsimp only [P]
        push_cast
        ring
      have hprod : ∀ (t : ℝ) (x y : ℤ),
          |t| ≤ H → |(x : ℝ)| ≤ Z → |(y : ℝ)| ≤ Z →
          |t * x * y| ≤ H * Z ^ 2 := by
        intro t x y ht hx hy
        have hxy : |(x : ℝ)| * |(y : ℝ)| ≤ Z * Z :=
          mul_le_mul hx hy (abs_nonneg _) hZ₀
        have hmain : |t| * (|(x : ℝ)| * |(y : ℝ)|) ≤ H * (Z * Z) :=
          mul_le_mul ht hxy (mul_nonneg (abs_nonneg _) (abs_nonneg _)) hH₀
        simpa only [abs_mul, mul_assoc, pow_two] using hmain
      have hprod2 : ∀ (t : ℝ) (x y : ℤ),
          |t| ≤ H → |(x : ℝ)| ≤ Z → |(y : ℝ)| ≤ Z →
          |2 * t * x * y| ≤ 2 * H * Z ^ 2 := by
        intro t x y ht hx hy
        have hmain := mul_le_mul_of_nonneg_left (hprod t x y ht hx hy)
          (show (0 : ℝ) ≤ 2 by norm_num)
        have heq : 2 * t * (x : ℝ) * y = 2 * (t * x * y) := by ring
        rw [heq, abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)]
        simpa only [mul_assoc] using hmain
      have ht1 := hprod2 (a : ℝ) uv.1 w.1 ha hu hwu
      have ht2 := hprod (b : ℝ) uv.1 w.2 hb hu hwv
      have ht3 := hprod (b : ℝ) uv.2 w.1 hb hv hwu
      have ht4 := hprod2 (c : ℝ) uv.2 w.2 hc hv hwv
      have hPbound : |(P uv : ℝ)| ≤ 6 * H * Z ^ 2 := by
        rw [hPform]
        calc
          |2 * (a : ℝ) * uv.1 * w.1 + (b : ℝ) * uv.1 * w.2 +
              (b : ℝ) * uv.2 * w.1 + 2 * (c : ℝ) * uv.2 * w.2| ≤
              |2 * (a : ℝ) * uv.1 * w.1| + |(b : ℝ) * uv.1 * w.2| +
                |(b : ℝ) * uv.2 * w.1| + |2 * (c : ℝ) * uv.2 * w.2| := by
            calc
              _ ≤ |2 * (a : ℝ) * uv.1 * w.1 + (b : ℝ) * uv.1 * w.2 +
                (b : ℝ) * uv.2 * w.1| + |2 * (c : ℝ) * uv.2 * w.2| := abs_add_le _ _
              _ ≤ (|2 * (a : ℝ) * uv.1 * w.1 + (b : ℝ) * uv.1 * w.2| +
                |(b : ℝ) * uv.2 * w.1|) + |2 * (c : ℝ) * uv.2 * w.2| :=
                add_le_add (abs_add_le _ _) le_rfl
              _ ≤ _ := add_le_add (add_le_add (abs_add_le _ _) le_rfl) le_rfl
          _ ≤ 2 * H * Z ^ 2 + H * Z ^ 2 + H * Z ^ 2 + 2 * H * Z ^ 2 :=
            add_le_add (add_le_add (add_le_add ht1 ht2) ht3) ht4
          _ = 6 * H * Z ^ 2 := by ring
      have hRbound : |(R uv : ℝ)| ≤ 6 * H * Z ^ 2 := by
        calc
          |(R uv : ℝ)| = |(uv.1 : ℝ) * w.2 - (uv.2 : ℝ) * w.1| := by
            simp only [R, Int.cast_sub, Int.cast_mul]
          _ ≤ |(uv.1 : ℝ) * w.2| + |(uv.2 : ℝ) * w.1| := by
            simpa only [sub_eq_add_neg, abs_neg] using
              abs_add_le ((uv.1 : ℝ) * w.2) (-((uv.2 : ℝ) * w.1))
          _ ≤ Z * Z + Z * Z := by
            rw [abs_mul, abs_mul]
            exact add_le_add (mul_le_mul hu hwv (abs_nonneg _) hZ₀)
              (mul_le_mul hv hwu (abs_nonneg _) hZ₀)
          _ ≤ 6 * H * Z ^ 2 := by
            have ht := mul_le_mul_of_nonneg_right hH (sq_nonneg Z)
            nlinarith only [ht, sq_nonneg Z]
      have hdenI : 1 ≤ |2 * h| := by
        have ht : 0 < |2 * h| := abs_pos.mpr htwo
        omega
      have hden : (1 : ℝ) ≤ |((2 * h : ℤ) : ℝ)| := by exact_mod_cast hdenI
      obtain ⟨hp, hr⟩ := hcancel uv huv
      have hpabs : |((2 * h : ℤ) : ℝ)| * |((φ uv).1 : ℝ)| = |(P uv : ℝ)| := by
        simpa only [Int.cast_mul, abs_mul] using congrArg (fun z : ℤ => |(z : ℝ)|) hp
      have hrabs : |((2 * h : ℤ) : ℝ)| * |((φ uv).2 : ℝ)| = |(R uv : ℝ)| := by
        simpa only [Int.cast_mul, abs_mul] using congrArg (fun z : ℤ => |(z : ℝ)|) hr
      constructor
      · calc
          |((φ uv).1 : ℝ)| ≤ |((2 * h : ℤ) : ℝ)| * |((φ uv).1 : ℝ)| := by
            simpa only [one_mul] using
              mul_le_mul_of_nonneg_right hden (abs_nonneg ((φ uv).1 : ℝ))
          _ = |(P uv : ℝ)| := hpabs
          _ ≤ 6 * H * Z ^ 2 := hPbound
          _ ≤ (K : ℝ) := hKge
      · calc
          |((φ uv).2 : ℝ)| ≤ |((2 * h : ℤ) : ℝ)| * |((φ uv).2 : ℝ)| := by
            simpa only [one_mul] using
              mul_le_mul_of_nonneg_right hden (abs_nonneg ((φ uv).2 : ℝ))
          _ = |(R uv : ℝ)| := hrabs
          _ ≤ 6 * H * Z ^ 2 := hRbound
          _ ≤ (K : ℝ) := hKge

    have hφmem : ∀ uv ∈ Fz z, φ uv ∈ C08.PcPell.pellBox D K := by
      intro uv huv
      obtain ⟨hu, hv⟩ := hbounds uv huv
      have huI : |(φ uv).1| ≤ (K : ℤ) := by exact_mod_cast hu
      have hvI : |(φ uv).2| ≤ (K : ℤ) := by exact_mod_cast hv
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_product.mpr
        ⟨Finset.mem_Icc.mpr (abs_le.mp huI), Finset.mem_Icc.mpr (abs_le.mp hvI)⟩,
        hnorm uv huv⟩

    have hinj : Set.InjOn φ (↑(Fz z) : Set (ℤ × ℤ)) := by
      intro uv huv uv' huv' heq
      obtain ⟨hp, hr⟩ := hcancel uv huv
      obtain ⟨hp', hr'⟩ := hcancel uv' huv'
      have hPeq : P uv = P uv' := by
        rw [← hp, ← hp', congrArg Prod.fst heq]
      have hReq : R uv = R uv' := by
        rw [← hr, ← hr', congrArg Prod.snd heq]
      have hU : 2 * h * (uv.1 - uv'.1) = 0 := by
        dsimp only [P, R] at hPeq hReq
        linear_combination w.1 * hPeq + (b * w.1 + 2 * c * w.2) * hReq -
          2 * (uv.1 - uv'.1) * hwEq
      have hV : 2 * h * (uv.2 - uv'.2) = 0 := by
        dsimp only [P, R] at hPeq hReq
        linear_combination w.2 * hPeq - (2 * a * w.1 + b * w.2) * hReq -
          2 * (uv.2 - uv'.2) * hwEq
      exact Prod.ext (sub_eq_zero.mp ((mul_eq_zero.mp hU).resolve_left htwo))
        (sub_eq_zero.mp ((mul_eq_zero.mp hV).resolve_left htwo))
    have hcard : (Fz z).card ≤ (C08.PcPell.pellBox D K).card :=
      Finset.card_le_card_of_injOn φ hφmem hinj
    exact (by exact_mod_cast hcard :
      ((Fz z).card : ℝ) ≤ ((C08.PcPell.pellBox D K).card : ℝ)).trans hPellCard

  have hTunion : T = (Finset.univ : Finset (ZMod m × ZMod m)).biUnion Fz := by
    ext uv
    constructor
    · intro huv
      exact Finset.mem_biUnion.mpr
        ⟨label uv, Finset.mem_univ _, Finset.mem_filter.mpr ⟨huv, rfl⟩⟩
    · intro huv
      obtain ⟨z, hz, huv⟩ := Finset.mem_biUnion.mp huv
      exact (Finset.mem_filter.mp huv).1
  have hTcard : (T.card : ℝ) ≤ (m : ℝ) ^ 2 * U := by
    calc
      (T.card : ℝ) ≤
          ((∑ z ∈ (Finset.univ : Finset (ZMod m × ZMod m)), (Fz z).card : ℕ) : ℝ) := by
        have ht : T.card ≤ ∑ z ∈ (Finset.univ : Finset (ZMod m × ZMod m)),
            (Fz z).card := by
          rw [hTunion]
          exact Finset.card_biUnion_le
        exact_mod_cast ht
      _ = ∑ z ∈ (Finset.univ : Finset (ZMod m × ZMod m)), ((Fz z).card : ℝ) := by
        simp only [Nat.cast_sum]
      _ ≤ ∑ z ∈ (Finset.univ : Finset (ZMod m × ZMod m)), U :=
        Finset.sum_le_sum (fun z hz => hfiber z)
      _ = (m : ℝ) ^ 2 * U := by
        simp [Fintype.card_prod, ZMod.card, pow_two] <;> ring
  have hpown : 1 ≤ (H * Z) ^ ε := Real.one_le_rpow hHZ hε.le
  have hlogn : Real.log (H * Z) ≤ (H * Z) ^ ε / ε :=
    Real.log_le_rpow_div hHZ₀.le hε
  have hbase₀ : 0 ≤ (4 / Real.log 2) * Real.log 7 + 4 := by positivity
  have hUbound : U ≤ Aε * (H * Z) ^ ε := by
    calc
      U = (4 / Real.log 2) * Real.log K + 4 := by dsimp only [U]; ring
      _ ≤ (4 / Real.log 2) * (Real.log 7 + 2 * Real.log (H * Z)) + 4 :=
        add_le_add
          (mul_le_mul_of_nonneg_left hlogK (by positivity)) le_rfl
      _ = ((4 / Real.log 2) * Real.log 7 + 4) +
          (8 / Real.log 2) * Real.log (H * Z) := by ring
      _ ≤ ((4 / Real.log 2) * Real.log 7 + 4) * (H * Z) ^ ε +
          (8 / Real.log 2) * ((H * Z) ^ ε / ε) := by
        apply add_le_add
        · simpa only [mul_one] using mul_le_mul_of_nonneg_left hpown hbase₀
        · exact mul_le_mul_of_nonneg_left hlogn (by positivity)
      _ = Aε * (H * Z) ^ ε := by
        dsimp only [Aε]
        field_simp [hlog2.ne', hε.ne'] <;> ring
  refine ⟨hSfin, ?_⟩
  rw [Set.ncard_eq_toFinset_card S hSfin]
  change (T.card : ℝ) ≤ ((m : ℝ) ^ 2 * Aε + 1) * (H * Z) ^ ε
  calc
    (T.card : ℝ) ≤ (m : ℝ) ^ 2 * U := hTcard
    _ ≤ (m : ℝ) ^ 2 * (Aε * (H * Z) ^ ε) :=
      mul_le_mul_of_nonneg_left hUbound (sq_nonneg _)
    _ = ((m : ℝ) ^ 2 * Aε) * (H * Z) ^ ε := by ring
    _ ≤ ((m : ℝ) ^ 2 * Aε + 1) * (H * Z) ^ ε :=
      mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by norm_num))
        (Real.rpow_nonneg hHZ₀.le _)

#print axioms signed_binary_quadratic_count

end A1QuadraticComponents

theorem JocelynClaims.claim_fd1d9a9a5f6f7f3ebb97f65e48e01ad6025b2df3fd61822ba8f1818a3717b7b9 :
∀ h : ℤ, h ≠ 0 → ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ H Z : ℝ, 1 ≤ H → 2 ≤ Z → ∀ a b c : ℤ, |(a : ℝ)| ≤ H → |(b : ℝ)| ≤ H → |(c : ℝ)| ≤ H → b ^ 2 - 4 * a * c ≠ 0 → let S : Set (ℤ × ℤ) := {uv | Int.gcd uv.1 uv.2 = 1 ∧ |(uv.1 : ℝ)| ≤ Z ∧ |(uv.2 : ℝ)| ≤ Z ∧ a * uv.1 ^ 2 + b * uv.1 * uv.2 + c * uv.2 ^ 2 = h} ; S.Finite ∧ (S.ncard : ℝ) ≤ C * (H * Z) ^ ε := by
  exact A1QuadraticComponents.signed_binary_quadratic_count

#print axioms JocelynClaims.claim_fd1d9a9a5f6f7f3ebb97f65e48e01ad6025b2df3fd61822ba8f1818a3717b7b9

noncomputable section
namespace A1ArithmeticAxis

open A1ArithmeticInterface
open A1ArithmeticChartSupplier

def yAxisCoeff {Δ : ℤ} (t : CoverType Δ) (y : ZPair) (j : Fin 3) : ℤ :=
  ∑ i : Fin 4,
    t.coeff i j * y 0 ^ (i : ℕ) * y 1 ^ (3 - (i : ℕ))

def yAxisDiscriminant {Δ : ℤ} (t : CoverType Δ) (y : ZPair) : ℤ :=
  yAxisCoeff t y 1 ^ 2 -
    4 * yAxisCoeff t y 2 * yAxisCoeff t y 0

def ActualYAxisNonvanishingStatement : Prop :=
  ∀ A B C : ℤ, 0 < A → ¬ IsSquare (B ^ 2 - 4 * A * C) →
    let Δ : ℤ := B ^ 2 - 4 * A * C
    let ζ : ℂ := root Δ
    ∀ t : CoverType Δ,
      let d : Data := data ζ t false false
      ∀ y : ZPair, y ≠ 0 →
        d.p₁ * (y 0 : ℂ) + d.q₁ * (y 1 : ℂ) ≠ 0 ∧
        d.p₂ * (y 0 : ℂ) + d.q₂ * (y 1 : ℂ) ≠ 0 ∧
        yAxisDiscriminant t y ≠ 0

end A1ArithmeticAxis

end

namespace A1ArithmeticAxis

open A1ArithmeticInterface
open A1ArithmeticChartSupplier
open A1ArithmeticToComponent

noncomputable section

theorem actualYAxisNonvanishing_attempt :
    ActualYAxisNonvanishingStatement := by
  classical
  intro A B C hA hdis
  dsimp only
  intro t y hy
  let Δ : ℤ := B ^ 2 - 4 * A * C
  let ζ : ℂ := root Δ
  let d : Data := data ζ t false false
  let κ : ℂ := d.scale / (t.rhs : ℂ)

  have presentation : ActualComponentPresentation Δ t :=
    actualArithmeticComponentSupplier_attempt A B C hA hdis t
  rcases presentation with
    ⟨hζ2, hζ0, hγ₁, hγ₂, hκ, hyMatrix, hxMatrix,
      hyDet, hxDet, hcoeffNonzero, hF, hEval, hcoeff⟩

  have anisotropic : ∀ u : QPair, qnorm Δ u = 0 → u = (0, 0) := by
    intro u hu
    by_cases hb : u.2 = 0
    · have hs : u.1 ^ 2 = 0 := by
        simpa only [qnorm, hb, zero_pow (by norm_num : 2 ≠ 0), mul_zero,
          sub_zero] using hu
      have ha : u.1 = 0 := by
        have hm : u.1 * u.1 = 0 := by simpa only [pow_two] using hs
        rcases mul_eq_zero.mp hm with h | h <;> exact h
      exact Prod.ext ha hb
    · exfalso
      apply A1QuadraticField.rational_nonsquare Δ hdis (u.1 / u.2)
      rw [zero_mul, add_zero, div_pow]
      apply (div_eq_iff (pow_ne_zero 2 hb)).2
      dsimp only [qnorm] at hu
      linear_combination hu

  have hYpair : linear t.p t.q y ≠ (0, 0) := by
    intro hz
    have hfirst := congrArg Prod.fst hz
    have hsecond := congrArg Prod.snd hz
    change t.p.1 * (y 0 : ℚ) + t.q.1 * (y 1 : ℚ) = 0 at hfirst
    change t.p.2 * (y 0 : ℚ) + t.q.2 * (y 1 : ℚ) = 0 at hsecond
    have hzero0 :
        (t.p.1 * t.q.2 - t.p.2 * t.q.1) * (y 0 : ℚ) = 0 := by
      linear_combination t.q.2 * hfirst - t.q.1 * hsecond
    have hzero1 :
        (t.p.1 * t.q.2 - t.p.2 * t.q.1) * (y 1 : ℚ) = 0 := by
      linear_combination -(t.p.2) * hfirst + t.p.1 * hsecond
    have hy0 : (y 0 : ℚ) = 0 :=
      (mul_eq_zero.mp hzero0).resolve_left t.ybasis_det_ne_zero
    have hy1 : (y 1 : ℚ) = 0 :=
      (mul_eq_zero.mp hzero1).resolve_left t.ybasis_det_ne_zero
    apply hy
    funext i
    fin_cases i
    · exact_mod_cast hy0
    · exact_mod_cast hy1
  have hYnorm : qnorm Δ (linear t.p t.q y) ≠ 0 := by
    intro hz
    exact hYpair (anisotropic _ hz)

  have embedNorm : ∀ u : QPair,
      embed ζ true u * embed ζ false u = (qnorm Δ u : ℂ) := by
    intro u
    dsimp [embed, qnorm]
    push_cast
    linear_combination -(u.2 : ℂ) ^ 2 * hζ2
  have hY₁Identity :
      embed ζ true (linear t.p t.q y) =
        d.p₁ * (y 0 : ℂ) + d.q₁ * (y 1 : ℂ) := by
    dsimp [embed, linear, d, data]
    push_cast
    ring
  have hY₂Identity :
      embed ζ false (linear t.p t.q y) =
        d.p₂ * (y 0 : ℂ) + d.q₂ * (y 1 : ℂ) := by
    dsimp [embed, linear, d, data]
    push_cast
    ring
  have hYproduct :
      embed ζ true (linear t.p t.q y) *
        embed ζ false (linear t.p t.q y) ≠ 0 := by
    rw [embedNorm]
    exact_mod_cast hYnorm
  have hY₁ : d.p₁ * (y 0 : ℂ) + d.q₁ * (y 1 : ℂ) ≠ 0 := by
    rw [← hY₁Identity]
    exact (mul_ne_zero_iff.mp hYproduct).1
  have hY₂ : d.p₂ * (y 0 : ℂ) + d.q₂ * (y 1 : ℂ) ≠ 0 := by
    rw [← hY₂Identity]
    exact (mul_ne_zero_iff.mp hYproduct).2

  let Y₁ : ℂ := d.p₁ * (y 0 : ℂ) + d.q₁ * (y 1 : ℂ)
  let Y₂ : ℂ := d.p₂ * (y 0 : ℂ) + d.q₂ * (y 1 : ℂ)
  let k₁ : ℂ := d.γ₁ * Y₁ ^ 3
  let k₂ : ℂ := d.γ₂ * Y₂ ^ 3
  have hk₁ : k₁ ≠ 0 := mul_ne_zero hγ₁ (pow_ne_zero 3 hY₁)
  have hk₂ : k₂ ≠ 0 := mul_ne_zero hγ₂ (pow_ne_zero 3 hY₂)
  have hdetX : d.r₁ * d.s₂ - d.r₂ * d.s₁ ≠ 0 := hxDet

  have axisCoefficient : ∀ j : Fin 3,
      κ * (yAxisCoeff t y j : ℂ) =
        k₁ * (Nat.choose 2 (j : ℕ) : ℂ) *
          d.r₁ ^ (j : ℕ) * d.s₁ ^ (2 - (j : ℕ)) -
        k₂ * (Nat.choose 2 (j : ℕ) : ℂ) *
          d.r₂ ^ (j : ℕ) * d.s₂ ^ (2 - (j : ℕ)) := by
    intro j
    calc
      κ * (yAxisCoeff t y j : ℂ) =
          ∑ i : Fin 4, (κ * (t.coeff i j : ℂ)) *
            (y 0 : ℂ) ^ (i : ℕ) * (y 1 : ℂ) ^ (3 - (i : ℕ)) := by
        simp only [yAxisCoeff]
        push_cast
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = ∑ i : Fin 4,
          (d.γ₁ * (Nat.choose 3 (i : ℕ) : ℂ) *
              d.p₁ ^ (i : ℕ) * d.q₁ ^ (3 - (i : ℕ)) *
              (Nat.choose 2 (j : ℕ) : ℂ) *
              d.r₁ ^ (j : ℕ) * d.s₁ ^ (2 - (j : ℕ)) -
            d.γ₂ * (Nat.choose 3 (i : ℕ) : ℂ) *
              d.p₂ ^ (i : ℕ) * d.q₂ ^ (3 - (i : ℕ)) *
              (Nat.choose 2 (j : ℕ) : ℂ) *
              d.r₂ ^ (j : ℕ) * d.s₂ ^ (2 - (j : ℕ))) *
            (y 0 : ℂ) ^ (i : ℕ) * (y 1 : ℂ) ^ (3 - (i : ℕ)) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hcoeff i j]
      _ = _ := by
        dsimp only [k₁, k₂, Y₁, Y₂]
        norm_num [Fin.sum_univ_succ, Fin.sum_univ_zero] <;> ring

  have hquadraticA :
      κ * (yAxisCoeff t y 2 : ℂ) = k₁ * d.r₁ ^ 2 - k₂ * d.r₂ ^ 2 := by
    have h := axisCoefficient (2 : Fin 3)
    norm_num at h
    exact h
  have hquadraticB :
      κ * (yAxisCoeff t y 1 : ℂ) =
        2 * (k₁ * d.r₁ * d.s₁ - k₂ * d.r₂ * d.s₂) := by
    have h := axisCoefficient (1 : Fin 3)
    norm_num at h
    linear_combination h
  have hquadraticC :
      κ * (yAxisCoeff t y 0 : ℂ) = k₁ * d.s₁ ^ 2 - k₂ * d.s₂ ^ 2 := by
    have h := axisCoefficient (0 : Fin 3)
    norm_num at h
    exact h

  have discriminantCast :
      (yAxisDiscriminant t y : ℂ) =
        (yAxisCoeff t y 1 : ℂ) ^ 2 -
          4 * (yAxisCoeff t y 2 : ℂ) * (yAxisCoeff t y 0 : ℂ) := by
    dsimp only [yAxisDiscriminant]
    push_cast
    rfl
  have discriminantIdentity :
      κ ^ 2 * (yAxisDiscriminant t y : ℂ) =
        4 * k₁ * k₂ * (d.r₁ * d.s₂ - d.r₂ * d.s₁) ^ 2 := by
    rw [discriminantCast]
    calc
      κ ^ 2 *
          ((yAxisCoeff t y 1 : ℂ) ^ 2 -
            4 * (yAxisCoeff t y 2 : ℂ) * (yAxisCoeff t y 0 : ℂ)) =
          (κ * (yAxisCoeff t y 1 : ℂ)) ^ 2 -
            4 * (κ * (yAxisCoeff t y 2 : ℂ)) *
              (κ * (yAxisCoeff t y 0 : ℂ)) := by ring
      _ = _ := by
        rw [hquadraticB, hquadraticA, hquadraticC]
        ring
  have discriminantNonzeroComplex : (yAxisDiscriminant t y : ℂ) ≠ 0 := by
    have hright :
        (4 : ℂ) * k₁ * k₂ * (d.r₁ * d.s₂ - d.r₂ * d.s₁) ^ 2 ≠ 0 :=
      mul_ne_zero
        (mul_ne_zero (mul_ne_zero (by norm_num) hk₁) hk₂)
        (pow_ne_zero 2 hdetX)
    have hleft : κ ^ 2 * (yAxisDiscriminant t y : ℂ) ≠ 0 := by
      rw [discriminantIdentity]
      exact hright
    exact (mul_ne_zero_iff.mp hleft).2
  have discriminantNonzero : yAxisDiscriminant t y ≠ 0 := by
    exact_mod_cast discriminantNonzeroComplex
  exact ⟨hY₁, hY₂, discriminantNonzero⟩

end
end A1ArithmeticAxis

#print axioms A1ArithmeticAxis.actualYAxisNonvanishing_attempt

set_option maxHeartbeats 1000000
set_option linter.all false
noncomputable section
namespace A1OriginalAxisCounts

theorem square_box_card (R : ℝ) (hR : 1 ≤ R) :
    ∃ U : Finset (ℤ×ℤ),
      (∀ uv : ℤ×ℤ, (uv.1 : ℝ)^2 ≤ R → (uv.2 : ℝ)^2 ≤ R → uv ∈ U) ∧
      (U.card : ℝ) ≤ 25*R := by
  classical
  have hR0 : 0 ≤ R := by linarith
  have hsqrt : 1 ≤ Real.sqrt R := by
    have h := Real.sqrt_le_sqrt hR
    simpa using h
  let k : ℕ := Nat.ceil (Real.sqrt R)
  have hkLo : Real.sqrt R ≤ (k : ℝ) := Nat.le_ceil _
  have hkHi : (k : ℝ) ≤ Real.sqrt R + 1 :=
    le_of_lt (Nat.ceil_lt_add_one (Real.sqrt_nonneg R))
  let I : Finset ℤ := Finset.Icc (-(k : ℤ)) (k : ℤ)
  let U : Finset (ℤ×ℤ) := I ×ˢ I
  have hmem : ∀ z : ℤ, (z : ℝ)^2 ≤ R → z ∈ I := by
    intro z hz
    have habs : |(z : ℝ)| ≤ Real.sqrt R := by
      apply (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg R)).mp
      simpa only [sq_abs,Real.sq_sqrt hR0] using hz
    have habsK : |(z : ℝ)| ≤ (k : ℝ) := habs.trans hkLo
    have hlo : - (k : ℝ) ≤ (z : ℝ) := (abs_le.mp habsK).1
    have hhi : (z : ℝ) ≤ (k : ℝ) := (abs_le.mp habsK).2
    apply Finset.mem_Icc.mpr
    constructor
    · exact_mod_cast hlo
    · exact_mod_cast hhi
  have hIcard : I.card = 2*k+1 := by
    have h := Int.card_Icc_of_le (-(k : ℤ)) (k : ℤ) (by omega)
    dsimp only [I]
    omega
  have hUcard : (U.card : ℝ) = (2*(k : ℝ)+1)^2 := by
    simp only [U,Finset.card_product,hIcard]
    push_cast
    ring
  refine ⟨U,?_,?_⟩
  · intro uv hu hv
    exact Finset.mem_product.mpr ⟨hmem uv.1 hu,hmem uv.2 hv⟩
  · rw [hUcard]
    have hlen : 2*(k : ℝ)+1 ≤ 5*Real.sqrt R := by linarith
    have hs : (2*(k : ℝ)+1)^2 ≤ (5*Real.sqrt R)^2 :=
      (sq_le_sq₀ (by positivity) (by positivity)).mpr hlen
    nlinarith [Real.sq_sqrt hR0]

end A1OriginalAxisCounts
#print axioms A1OriginalAxisCounts.square_box_card

end

namespace A1OriginalAxisCounts
open A1ArithmeticInterface

theorem coordinate_le_height (y : ZPair) (i : Fin 2) :
    |(y i : ℝ)| ≤ height y := by
  fin_cases i
  · exact le_max_left _ _
  · exact le_max_right _ _

theorem height_nonneg (y : ZPair) : 0 ≤ height y :=
  (abs_nonneg (y 0 : ℝ)).trans (le_max_left _ _)

theorem height_box_card (R : ℝ) (hR : 1 ≤ R) :
    ∃ U : Finset ZPair,
      (∀ y : ZPair, height y^2 ≤ R → y ∈ U) ∧
      (U.card : ℝ) ≤ 25*R := by
  classical
  obtain ⟨I,hImem,hIcard⟩ := square_box_card R hR
  let U : Finset ZPair := I.image (fun uv : ℤ×ℤ => ![uv.1,uv.2])
  refine ⟨U,?_,?_⟩
  · intro y hy
    apply Finset.mem_image.mpr
    refine ⟨(y 0,y 1),hImem (y 0,y 1) ?_ ?_,?_⟩
    · have h := (sq_le_sq₀ (abs_nonneg _) (height_nonneg y)).mpr
        (coordinate_le_height y 0)
      have hh : (y 0 : ℝ)^2 ≤ height y^2 := by simpa only [sq_abs] using h
      exact hh.trans hy
    · have h := (sq_le_sq₀ (abs_nonneg _) (height_nonneg y)).mpr
        (coordinate_le_height y 1)
      have hh : (y 1 : ℝ)^2 ≤ height y^2 := by simpa only [sq_abs] using h
      exact hh.trans hy
    · funext i
      fin_cases i <;> rfl
  · have hcard : U.card ≤ I.card := Finset.card_image_le
    exact (by exact_mod_cast hcard : (U.card : ℝ) ≤ I.card).trans hIcard

theorem original_box_scale_bounds
    (H N D E : ℝ) (hH : 1 ≤ H) (hN : 2 ≤ N)
    (hD : H⁻¹ ≤ D) (hE : H⁻¹ ≤ E) (hDE : D^3*E^2 ≤ H*N^2) :
    1 ≤ H*D ∧ 1 ≤ H*E ∧
      H*D ≤ (H^3*N)^2 ∧ H*E ≤ (H^3*N)^2 := by
  have hHpos : 0 < H := lt_of_lt_of_le zero_lt_one hH
  have hHD : 1 ≤ H*D := by
    calc
      1 = H*H⁻¹ := (mul_inv_cancel₀ hHpos.ne').symm
      _ ≤ H*D := mul_le_mul_of_nonneg_left hD hHpos.le
  have hHE : 1 ≤ H*E := by
    calc
      1 = H*H⁻¹ := (mul_inv_cancel₀ hHpos.ne').symm
      _ ≤ H*E := mul_le_mul_of_nonneg_left hE hHpos.le
  have hprod : (H*D)^3*(H*E)^2 ≤ H^6*N^2 := by
    calc
      (H*D)^3*(H*E)^2 = H^5*(D^3*E^2) := by ring
      _ ≤ H^5*(H*N^2) :=
        mul_le_mul_of_nonneg_left hDE (pow_nonneg hHpos.le 5)
      _ = H^6*N^2 := by ring
  have hHD0 : 0 ≤ H*D := by linarith
  have hHE0 : 0 ≤ H*E := by linarith
  have hHD2 : 1 ≤ (H*D)^2 := by nlinarith [sq_nonneg (H*D-1)]
  have hHE2 : 1 ≤ (H*E)^2 := by nlinarith [sq_nonneg (H*E-1)]
  have hHD3 : H*D ≤ (H*D)^3 := by
    have hh := mul_nonneg (sub_nonneg.mpr hHD2) hHD0
    nlinarith only [hh]
  have hHEsquare : H*E ≤ (H*E)^2 := by
    nlinarith [sq_nonneg (H*E-1)]
  have hU : H*D ≤ H^6*N^2 := by
    calc
      H*D ≤ (H*D)^3 := hHD3
      _ ≤ (H*D)^3*(H*E)^2 := by
        simpa only [mul_one] using
          mul_le_mul_of_nonneg_left hHE2 (pow_nonneg hHD0 3)
      _ ≤ H^6*N^2 := hprod
  have hV : H*E ≤ H^6*N^2 := by
    calc
      H*E ≤ (H*E)^2 := hHEsquare
      _ ≤ (H*D)^3*(H*E)^2 := by
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right (hHD.trans hHD3) (sq_nonneg (H*E))
      _ ≤ H^6*N^2 := hprod
  refine ⟨hHD,hHE,?_,?_⟩
  · calc H*D ≤ H^6*N^2 := hU
         _ = (H^3*N)^2 := by ring
  · calc H*E ≤ H^6*N^2 := hV
         _ = (H^3*N)^2 := by ring

theorem homogeneous_cubic_coeff_bound
    (c : Fin 4 → Fin 3 → ℤ) (y : ZPair) (Z : ℝ)
    (hZ : 0 ≤ Z) (hy : height y ≤ Z) (j : Fin 3) :
    |((∑ i : Fin 4, c i j*y 0^(i : ℕ)*y 1^(3-(i : ℕ)) : ℤ) : ℝ)| ≤
      (1+∑ i : Fin 4, ∑ k : Fin 3, |(c i k : ℝ)|)*Z^3 := by
  have hy0 : |(y 0 : ℝ)| ≤ Z := (coordinate_le_height y 0).trans hy
  have hy1 : |(y 1 : ℝ)| ≤ Z := (coordinate_le_height y 1).trans hy
  have hmon : ∀ i : Fin 4,
      |(y 0 : ℝ)|^(i : ℕ)*|(y 1 : ℝ)|^(3-(i : ℕ)) ≤ Z^3 := by
    intro i
    have hi : (i : ℕ) ≤ 3 := by omega
    calc
      |(y 0 : ℝ)|^(i : ℕ)*|(y 1 : ℝ)|^(3-(i : ℕ)) ≤
          Z^(i : ℕ)*Z^(3-(i : ℕ)) := by gcongr
      _ = Z^3 := by rw [←pow_add,Nat.add_sub_of_le hi]
  have hsum : (∑ i : Fin 4, |(c i j : ℝ)|) ≤
      (∑ i : Fin 4, ∑ k : Fin 3, |(c i k : ℝ)|) := by
    apply Finset.sum_le_sum
    intro i _
    exact Finset.single_le_sum (fun k _ => abs_nonneg (c i k : ℝ)) (Finset.mem_univ j)
  push_cast
  calc
    |∑ i : Fin 4, (c i j : ℝ)*(y 0 : ℝ)^(i : ℕ)*(y 1 : ℝ)^(3-(i : ℕ))| ≤
        ∑ i : Fin 4, |(c i j : ℝ)*(y 0 : ℝ)^(i : ℕ)*(y 1 : ℝ)^(3-(i : ℕ))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin 4, |(c i j : ℝ)| * Z^3 := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul,abs_mul,abs_pow,abs_pow]
      calc
        |(c i j : ℝ)| * |(y 0 : ℝ)|^(i : ℕ)*|(y 1 : ℝ)|^(3-(i : ℕ)) =
            |(c i j : ℝ)| * (|(y 0 : ℝ)|^(i : ℕ)*|(y 1 : ℝ)|^(3-(i : ℕ))) := by ring
        _ ≤ |(c i j : ℝ)| * Z^3 :=
          mul_le_mul_of_nonneg_left (hmon i) (abs_nonneg _)
    _ = (∑ i : Fin 4, |(c i j : ℝ)|)*Z^3 := by rw [Finset.sum_mul]
    _ ≤ (1+∑ i : Fin 4, ∑ k : Fin 3, |(c i k : ℝ)|)*Z^3 :=
      mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg hZ 3)

end A1OriginalAxisCounts
#print axioms A1OriginalAxisCounts.height_box_card
#print axioms A1OriginalAxisCounts.original_box_scale_bounds
#print axioms A1OriginalAxisCounts.homogeneous_cubic_coeff_bound

namespace A1OriginalAxisCounts
open A1ArithmeticInterface

theorem vector_pair_eta (y : ZPair) : (![y 0,y 1] : ZPair) = y := by
  funext i
  fin_cases i <;> rfl

theorem coordinate_preimage_count
    (S : Set ZPair) (T : Set (ℤ×ℤ)) (hT : T.Finite)
    (hMap : ∀ y ∈ S, (y 0,y 1) ∈ T) :
    S.Finite ∧ S.ncard ≤ T.ncard := by
  classical
  have hSfin : S.Finite :=
    (hT.image (fun uv : ℤ×ℤ => (![uv.1,uv.2] : ZPair))).subset (by
      intro y hy
      exact ⟨(y 0,y 1),hMap y hy,vector_pair_eta y⟩)
  refine ⟨hSfin,?_⟩
  refine Set.ncard_le_ncard_of_injOn (fun y : ZPair => (y 0,y 1)) hMap ?_ hT
  · intro y _ z _ he
    funext i
    fin_cases i
    · exact congrArg Prod.fst he
    · exact congrArg Prod.snd he

end A1OriginalAxisCounts
#print axioms A1OriginalAxisCounts.coordinate_preimage_count

set_option maxHeartbeats 1000000
set_option linter.all false
noncomputable section
namespace A1OriginalAxisCounts

theorem fibre_sum_count {α β : Type*}
    (S : Set (α×β)) (I : Finset α) (B : ℝ)
    (hI : ∀ z ∈ S, z.1 ∈ I)
    (hf : ∀ u ∈ I,
      {v : β | (u,v) ∈ S}.Finite ∧
        ({v : β | (u,v) ∈ S}.ncard : ℝ) ≤ B) :
    S.Finite ∧ (S.ncard : ℝ) ≤ (I.card : ℝ)*B := by
  classical
  let V : α → Finset β := fun u =>
    if hu : u ∈ I then (hf u hu).1.toFinset else ∅
  let T : Finset (α×β) := I.biUnion (fun u => (V u).image (fun v => (u,v)))
  have hSub : S ⊆ (↑T : Set (α×β)) := by
    intro z hz
    rcases z with ⟨u,v⟩
    have hu : u ∈ I := hI (u,v) hz
    apply Finset.mem_biUnion.mpr
    refine ⟨u,hu,Finset.mem_image.mpr ⟨v,?_,rfl⟩⟩
    dsimp only [V]
    rw [dif_pos hu,Set.Finite.mem_toFinset]
    exact hz
  have hFin : S.Finite := (Finset.finite_toSet T).subset hSub
  have hScard : S.ncard ≤ T.card := by
    calc
      S.ncard ≤ (↑T : Set (α×β)).ncard :=
        Set.ncard_le_ncard_of_injOn id (fun z hz => hSub hz)
          (fun _ _ _ _ he => he) (Finset.finite_toSet T)
      _ = T.card := Set.ncard_coe_finset T
  have hTcard : T.card ≤ ∑ u ∈ I, (V u).card :=
    Finset.card_biUnion_le.trans
      (Finset.sum_le_sum (fun _ _ => Finset.card_image_le))
  have hVcard : ∀ u ∈ I, ((V u).card : ℝ) ≤ B := by
    intro u hu
    dsimp only [V]
    rw [dif_pos hu,←Set.ncard_eq_toFinset_card _ (hf u hu).1]
    exact (hf u hu).2
  refine ⟨hFin,?_⟩
  calc
    (S.ncard : ℝ) ≤ (T.card : ℝ) := by exact_mod_cast hScard
    _ ≤ ∑ u ∈ I, ((V u).card : ℝ) := by exact_mod_cast hTcard
    _ ≤ ∑ u ∈ I, B := Finset.sum_le_sum hVcard
    _ = (I.card : ℝ)*B := by simp [Finset.sum_const]

end A1OriginalAxisCounts
#print axioms A1OriginalAxisCounts.fibre_sum_count

end

namespace A1OriginalAxisCounts
open A1ArithmeticInterface A1ArithmeticAxis
noncomputable section

theorem primitive_ne_zero (y : ZPair) (hy : primitive y) : y ≠ 0 := by
  intro hz
  simp [primitive,hz] at hy

theorem original_y_axis_eval {Δ : ℤ} (t : CoverType Δ) (y x : ZPair) :
    biformEval t.coeff y x =
      yAxisCoeff t y 2*x 0^2 + yAxisCoeff t y 1*x 0*x 1 +
        yAxisCoeff t y 0*x 1^2 := by
  norm_num [biformEval,yAxisCoeff,Fin.sum_univ_succ]
  <;> ring

theorem quadratic_scale_rpow (B R N ε : ℝ)
    (hB : 0 ≤ B) (hR : 0 ≤ R) (hN : 0 ≤ N) :
    ((B*N^3)*(R*N))^(ε/4) =
      (B*R)^(ε/4)*N^ε := by
  rw [show (B*N^3)*(R*N) = (B*R)*N^4 by ring,
    Real.mul_rpow (mul_nonneg hB hR) (pow_nonneg hN 4),
    ←Real.rpow_natCast_mul hN]
  congr 1
  congr 1
  norm_num
  ring

theorem original_norm_box_fallback : OriginalNormBoxFallbackStatement := by
  classical
  intro hSt A B C hA hdis t ε H hε hH
  obtain ⟨Kc,hKc,hCubic⟩ := original_cubic_fibre_count hSt A B C hA hdis t
  obtain ⟨Cq,hCq,hQuad⟩ :=
    A1QuadraticComponents.signed_binary_quadratic_count t.rhs t.rhs_pos.ne'
      (ε/4) (by positivity)
  let M : ℝ := 1 + ∑ i : Fin 4, ∑ j : Fin 3, |(t.coeff i j : ℝ)|
  have hM : 1 ≤ M := by
    dsimp only [M]
    have hh : 0 ≤ ∑ i : Fin 4, ∑ j : Fin 3, |(t.coeff i j : ℝ)| :=
      Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => abs_nonneg _))
    linarith
  have hHpos : 0 < H := by linarith
  let R : ℝ := H^3+1
  let Bc : ℝ := 1+M*H^9
  have hR : 1 ≤ R := by dsimp only [R]; nlinarith [pow_nonneg hHpos.le 3]
  have hBc : 1 ≤ Bc := by
    dsimp only [Bc]
    have hh : 0 ≤ M*H^9 := mul_nonneg (by linarith) (pow_nonneg hHpos.le 9)
    linarith
  let Fq : ℝ := Cq*(Bc*R)^(ε/4)
  have hFq : 0 < Fq := by dsimp only [Fq]; positivity
  let K : ℝ := 1+25*H*(Fq+(Kc : ℝ))
  have hK : 0 < K := by dsimp only [K]; positivity
  refine ⟨K,hK,?_⟩
  intro N D E hN hD hE hDE
  let S : Set (ZPair×ZPair) :=
    {z | primitive z.1 ∧ primitive z.2 ∧
      biformEval t.coeff z.1 z.2 = t.rhs ∧
      height z.1^2 ≤ H*D ∧ height z.2^2 ≤ H*E}
  change S.Finite ∧ (S.ncard : ℝ) ≤ K*N^ε*min D E
  have hNpos : 0 < N := by linarith
  obtain ⟨hHD,hHE,hDupper,hEupper⟩ :=
    original_box_scale_bounds H N D E hH hN hD hE hDE
  have hDpos : 0 ≤ D := (inv_nonneg.mpr hHpos.le).trans hD
  have hEpos : 0 ≤ E := (inv_nonneg.mpr hHpos.le).trans hE
  have hpow : 1 ≤ N^ε := Real.one_le_rpow (by linarith) hε.le
  have hpow0 : 0 ≤ N^ε := by positivity
  have hZ : 2 ≤ R*N := by
    calc
      2 ≤ N := hN
      _ ≤ R*N := by simpa only [one_mul] using
        mul_le_mul_of_nonneg_right hR hNpos.le
  have hCoeffCap : 1 ≤ Bc*N^3 := by
    have hN3 : 1 ≤ N^3 := one_le_pow₀ (by linarith)
    nlinarith
  have hYn : ∀ y : ZPair, height y^2 ≤ H*D → height y ≤ H^3*N := by
    intro y hy
    exact (sq_le_sq₀ (height_nonneg y) (by positivity)).mp (hy.trans hDupper)
  have hXn : ∀ x : ZPair, height x^2 ≤ H*E → height x ≤ R*N := by
    intro x hx
    have hh : height x ≤ H^3*N :=
      (sq_le_sq₀ (height_nonneg x) (by positivity)).mp (hx.trans hEupper)
    exact hh.trans (by dsimp only [R]; nlinarith)
  have hCoeff : ∀ y : ZPair, height y^2 ≤ H*D → ∀ j : Fin 3,
      |(yAxisCoeff t y j : ℝ)| ≤ Bc*N^3 := by
    intro y hy j
    have hh := homogeneous_cubic_coeff_bound t.coeff y (H^3*N)
      (by positivity) (hYn y hy) j
    calc
      |(yAxisCoeff t y j : ℝ)| ≤ M*(H^3*N)^3 := hh
      _ ≤ Bc*N^3 := by
        dsimp only [Bc]
        have hn3 : 0 ≤ N^3 := by positivity
        nlinarith only [hn3]

  obtain ⟨IY,hIYmem,hIYcard⟩ := height_box_card (H*D) hHD
  obtain ⟨IX,hIXmem,hIXcard⟩ := height_box_card (H*E) hHE

  have hfY : ∀ y ∈ IY,
      {x : ZPair | (y,x) ∈ S}.Finite ∧
        ({x : ZPair | (y,x) ∈ S}.ncard : ℝ) ≤ Fq*N^ε := by
    intro y _
    by_cases hy : primitive y ∧ height y^2 ≤ H*D
    · have hDisc : yAxisDiscriminant t y ≠ 0 :=
        (actualYAxisNonvanishing_attempt A B C hA hdis t y
          (primitive_ne_zero y hy.1)).2.2
      obtain ⟨hTfin,hTcard⟩ := hQuad (Bc*N^3) (R*N) hCoeffCap hZ
        (yAxisCoeff t y 2) (yAxisCoeff t y 1) (yAxisCoeff t y 0)
        (hCoeff y hy.2 2) (hCoeff y hy.2 1) (hCoeff y hy.2 0) hDisc
      let T : Set (ℤ×ℤ) :=
        {uv | Int.gcd uv.1 uv.2 = 1 ∧
          |(uv.1 : ℝ)| ≤ R*N ∧ |(uv.2 : ℝ)| ≤ R*N ∧
          yAxisCoeff t y 2*uv.1^2 + yAxisCoeff t y 1*uv.1*uv.2 +
            yAxisCoeff t y 0*uv.2^2 = t.rhs}
      change T.Finite at hTfin
      change (T.ncard : ℝ) ≤ Cq*((Bc*N^3)*(R*N))^(ε/4) at hTcard
      obtain ⟨hFfin,hFcard⟩ := coordinate_preimage_count
        {x : ZPair | (y,x) ∈ S} T hTfin (by
          intro x hx
          refine ⟨hx.2.1,?_,?_,?_⟩
          · exact (coordinate_le_height x 0).trans (hXn x hx.2.2.2.2)
          · exact (coordinate_le_height x 1).trans (hXn x hx.2.2.2.2)
          · exact (original_y_axis_eval t y x).symm.trans hx.2.2.1)
      refine ⟨hFfin,?_⟩
      calc
        ({x : ZPair | (y,x) ∈ S}.ncard : ℝ) ≤ (T.ncard : ℝ) := by
          exact_mod_cast hFcard
        _ ≤ Cq*((Bc*N^3)*(R*N))^(ε/4) := hTcard
        _ = Fq*N^ε := by
          rw [quadratic_scale_rpow Bc R N ε (by linarith) (by linarith) hNpos.le]
          dsimp only [Fq]
          ring
    · have hEmpty : {x : ZPair | (y,x) ∈ S} = ∅ := by
        ext x
        exact ⟨(fun hx => False.elim (hy ⟨hx.1,hx.2.2.2.1⟩)),(fun hx => False.elim hx)⟩
      simp only [hEmpty,Set.finite_empty,Set.ncard_empty,Nat.cast_zero,true_and]
      positivity
  obtain ⟨hSfin,hSD⟩ := fibre_sum_count S IY (Fq*N^ε)
    (by intro z hz; exact hIYmem z.1 hz.2.2.2.1) hfY

  let SwapS : Set (ZPair×ZPair) := {z | (z.2,z.1) ∈ S}
  have hfX : ∀ x ∈ IX,
      {y : ZPair | (x,y) ∈ SwapS}.Finite ∧
        ({y : ZPair | (x,y) ∈ SwapS}.ncard : ℝ) ≤ (Kc : ℝ) := by
    intro x _
    by_cases hx : primitive x
    · obtain ⟨hTfin,hTcard⟩ := hCubic x (primitive_ne_zero x hx)
      let T : Set (ℤ×ℤ) :=
        {uv | Int.gcd uv.1 uv.2 = 1 ∧
          biformEval t.coeff (![uv.1,uv.2]) x = t.rhs}
      obtain ⟨hFfin,hFcard⟩ := coordinate_preimage_count
        {y : ZPair | (x,y) ∈ SwapS} T hTfin (by
          intro y hy
          refine ⟨hy.1,?_⟩
          simpa only [vector_pair_eta] using hy.2.2.1)
      exact ⟨hFfin,by exact_mod_cast hFcard.trans hTcard⟩
    · have hEmpty : {y : ZPair | (x,y) ∈ SwapS} = ∅ := by
        ext y
        exact ⟨(fun hy => False.elim (hx hy.2.1)),(fun hy => False.elim hy)⟩
      simp only [hEmpty,Set.finite_empty,Set.ncard_empty,Nat.cast_zero,true_and]
      positivity
  obtain ⟨hSwapFin,hSE⟩ := fibre_sum_count SwapS IX (Kc : ℝ)
    (by intro z hz; exact hIXmem z.1 hz.2.2.2.2) hfX
  have hSwapCard : S.ncard ≤ SwapS.ncard := by
    refine Set.ncard_le_ncard_of_injOn Prod.swap
      (fun z hz => hz) ?_ hSwapFin
    intro z _ w _ he
    exact Prod.swap_injective he
  have hSE' : (S.ncard : ℝ) ≤ (IX.card : ℝ)*(Kc : ℝ) :=
    (by exact_mod_cast hSwapCard : (S.ncard : ℝ) ≤ SwapS.ncard).trans hSE
  have hSD' : (S.ncard : ℝ) ≤ 25*H*D*(Fq*N^ε) :=
    hSD.trans (mul_le_mul_of_nonneg_right (by simpa only [mul_assoc] using hIYcard) (by positivity))
  have hSE'' : (S.ncard : ℝ) ≤ 25*H*E*(Kc : ℝ) :=
    hSE'.trans (mul_le_mul_of_nonneg_right (by simpa only [mul_assoc] using hIXcard) (by positivity))
  have hKD : 25*H*Fq ≤ K := by
    dsimp only [K]
    nlinarith [show 0 ≤ (Kc : ℝ) by positivity]
  have hKE : 25*H*(Kc : ℝ) ≤ K := by
    dsimp only [K]
    nlinarith
  have hBoundD : (S.ncard : ℝ) ≤ K*N^ε*D := by
    calc
      (S.ncard : ℝ) ≤ 25*H*D*(Fq*N^ε) := hSD'
      _ = (25*H*Fq)*(N^ε*D) := by ring
      _ ≤ K*(N^ε*D) := mul_le_mul_of_nonneg_right hKD (mul_nonneg hpow0 hDpos)
      _ = K*N^ε*D := by ring
  have hBoundE : (S.ncard : ℝ) ≤ K*N^ε*E := by
    calc
      (S.ncard : ℝ) ≤ 25*H*E*(Kc : ℝ) := hSE''
      _ = (25*H*(Kc : ℝ))*E := by ring
      _ ≤ (25*H*(Kc : ℝ))*N^ε*E := by
        apply mul_le_mul_of_nonneg_right _ hEpos
        simpa only [mul_one] using
          mul_le_mul_of_nonneg_left hpow (by positivity : 0 ≤ 25*H*(Kc : ℝ))
      _ ≤ K*N^ε*E := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hKE hpow0) hEpos
  refine ⟨hSfin,?_⟩
  rcases le_total D E with h | h
  · simpa only [min_eq_left h] using hBoundD
  · simpa only [min_eq_right h] using hBoundE

end
end A1OriginalAxisCounts
#print axioms A1OriginalAxisCounts.original_norm_box_fallback

namespace JocelynClaims
theorem claim_fee060ec8efc629cff44be0054c59b3c8de32bece45eb04411bf448f78267e84 : (
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
  let primitive : ZPair → Prop := (fun y => Int.gcd (y 0) (y 1) = 1);
  let height : ZPair → ℝ := (fun y => max |(y 0 : ℝ)| |(y 1 : ℝ)|);
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
      ∀ ε H : ℝ, 0 < ε → 1 ≤ H →
        ∃ K : ℝ, 0 < K ∧
          ∀ N D E : ℝ, 2 ≤ N →
            H⁻¹ ≤ D → H⁻¹ ≤ E → D^3*E^2 ≤ H*N^2 →
            let S : Set (ZPair×ZPair) := ({z | primitive z.1 ∧ primitive z.2 ∧
                biformEval coeff z.1 z.2 = rhs ∧
                height z.1^2 ≤ H*D ∧ height z.2^2 ≤ H*E});
            S.Finite ∧ (S.ncard : ℝ) ≤ K*N^ε*min D E
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
  exact A1OriginalAxisCounts.original_norm_box_fallback hSt A B C hA hdis t
end JocelynClaims
#print axioms JocelynClaims.claim_fee060ec8efc629cff44be0054c59b3c8de32bece45eb04411bf448f78267e84
