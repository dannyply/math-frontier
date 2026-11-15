-- Source SHA-256: c950e2257195d992b5e3c346a0f671dac06d994f46f47f3773d094b04f331683
import Mathlib
import JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.LemmaP
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB

namespace FormalAB.Sb4a69aed

noncomputable section
namespace A5NormalFormHeightBudgetProof
open MvPolynomial
set_option maxHeartbeats 1800000
abbrev M2Z := MvPolynomial (Fin 2) ℤ
noncomputable abbrev X₀ : M2Z := MvPolynomial.X 0
noncomputable abbrev X₁ : M2Z := MvPolynomial.X 1
noncomputable abbrev m30 : Fin 2 →₀ ℕ := Finsupp.single 0 3
noncomputable abbrev m21 : Fin 2 →₀ ℕ := Finsupp.single 0 2 + Finsupp.single 1 1
noncomputable abbrev m12 : Fin 2 →₀ ℕ := Finsupp.single 0 1 + Finsupp.single 1 2
noncomputable abbrev m03 : Fin 2 →₀ ℕ := Finsupp.single 1 3

theorem monomial_mixed (r : ℤ) (i j : ℕ) :
    MvPolynomial.monomial
        (Finsupp.single (0 : Fin 2) i + Finsupp.single (1 : Fin 2) j) r =
      MvPolynomial.C r *
        (MvPolynomial.X (0 : Fin 2)) ^ i *
        (MvPolynomial.X (1 : Fin 2)) ^ j := by
  calc
    MvPolynomial.monomial
        (Finsupp.single (0 : Fin 2) i + Finsupp.single (1 : Fin 2) j) r =
      MvPolynomial.monomial (Finsupp.single (0 : Fin 2) i) r *
        MvPolynomial.monomial (Finsupp.single (1 : Fin 2) j) (1 : ℤ) := by
          rw [MvPolynomial.monomial_mul]
          simp
    _ = _ := by
      rw [← MvPolynomial.C_mul_X_pow_eq_monomial,
        ← MvPolynomial.C_mul_X_pow_eq_monomial]
      simp [mul_assoc]

theorem cubic_coefficients (u v w z : ℤ) :
    let F : M2Z := C u * X₀ ^ 3 + C v * X₀ ^ 2 * X₁ +
      C w * X₀ * X₁ ^ 2 + C z * X₁ ^ 3;
    coeff m30 F = u ∧ coeff m21 F = v ∧ coeff m12 F = w ∧ coeff m03 F = z := by
  intro F
  have h30 : (C u * X₀ ^ 3 : M2Z) = monomial m30 u := by
    simpa [m30, X₀, X₁] using (monomial_mixed u 3 0).symm
  have h21 : (C v * X₀ ^ 2 * X₁ : M2Z) = monomial m21 v := by
    simpa [m21, X₀, X₁] using (monomial_mixed v 2 1).symm
  have h12 : (C w * X₀ * X₁ ^ 2 : M2Z) = monomial m12 w := by
    simpa [m12, X₀, X₁] using (monomial_mixed w 1 2).symm
  have h03 : (C z * X₁ ^ 3 : M2Z) = monomial m03 z := by
    simpa [m03, X₀, X₁] using (monomial_mixed z 0 3).symm
  have hF : F = monomial m30 u + monomial m21 v +
      monomial m12 w + monomial m03 z := by
    dsimp only [F]
    rw [h30, h21, h12, h03]
  have hdistinct01 : m30 ≠ m21 := by
    intro h
    have h0 := congrArg (fun z : Fin 2 →₀ ℕ => z 0) h
    norm_num [m30, m21, m12, m03, Finsupp.add_apply] at h0
  have hdistinct02 : m30 ≠ m12 := by
    intro h
    have h0 := congrArg (fun z : Fin 2 →₀ ℕ => z 0) h
    norm_num [m30, m21, m12, m03, Finsupp.add_apply] at h0
  have hdistinct03 : m30 ≠ m03 := by
    intro h
    have h0 := congrArg (fun z : Fin 2 →₀ ℕ => z 0) h
    norm_num [m30, m21, m12, m03, Finsupp.add_apply] at h0
  have hdistinct12 : m21 ≠ m12 := by
    intro h
    have h0 := congrArg (fun z : Fin 2 →₀ ℕ => z 0) h
    norm_num [m30, m21, m12, m03, Finsupp.add_apply] at h0
  have hdistinct13 : m21 ≠ m03 := by
    intro h
    have h0 := congrArg (fun z : Fin 2 →₀ ℕ => z 0) h
    norm_num [m30, m21, m12, m03, Finsupp.add_apply] at h0
  have hdistinct23 : m12 ≠ m03 := by
    intro h
    have h0 := congrArg (fun z : Fin 2 →₀ ℕ => z 0) h
    norm_num [m30, m21, m12, m03, Finsupp.add_apply] at h0

  simp only [hF, MvPolynomial.coeff_add, MvPolynomial.coeff_monomial]
  simp [hdistinct01, hdistinct02, hdistinct03, hdistinct12, hdistinct13, hdistinct23,
    Ne.symm hdistinct01, Ne.symm hdistinct02, Ne.symm hdistinct03,
    Ne.symm hdistinct12, Ne.symm hdistinct13, Ne.symm hdistinct23]

theorem normal_coefficients
    (P Q : M2Z) (a b c A B : ℤ)
    (hP : P = (C A * X₀ + C B * X₁) * X₁ ^ 2 -
      C c * (C a * X₀ + C b * X₁) ^ 2 * C (a ^ 2) *
        (C a * X₀ + C (3 * b) * X₁))
    (hQ : Q = (C A * X₀ + C B * X₁) * X₀ ^ 2 +
      C c * (C a * X₀ + C b * X₁) ^ 2 * C (b ^ 2) *
        (C (3 * a) * X₀ + C b * X₁)) :
    coeff m30 P = -c * a ^ 5 ∧
    coeff m03 Q = c * b ^ 5 ∧
    coeff m12 P = A - 7 * c * a ^ 3 * b ^ 2 ∧
    coeff m30 Q = A + 3 * c * a ^ 3 * b ^ 2 ∧
    coeff m03 P = B - 3 * c * a ^ 2 * b ^ 3 ∧
    coeff m21 Q = B + 7 * c * a ^ 2 * b ^ 3 := by
  have hp : P =
      C (-c * a ^ 5) * X₀ ^ 3 +
      C (-(5 * c * a ^ 4 * b)) * X₀ ^ 2 * X₁ +
      C (A - 7 * c * a ^ 3 * b ^ 2) * X₀ * X₁ ^ 2 +
      C (B - 3 * c * a ^ 2 * b ^ 3) * X₁ ^ 3 := by
    rw [hP]
    simp [ map_mul, map_pow, map_neg, map_sub] ; ring
  have hq : Q =
      C (A + 3 * c * a ^ 3 * b ^ 2) * X₀ ^ 3 +
      C (B + 7 * c * a ^ 2 * b ^ 3) * X₀ ^ 2 * X₁ +
      C (5 * c * a * b ^ 4) * X₀ * X₁ ^ 2 +
      C (c * b ^ 5) * X₁ ^ 3 := by
    rw [hQ]
    simp [map_add, map_mul, map_pow, ] ; ring
  have hcP := cubic_coefficients (-c * a ^ 5) (-(5 * c * a ^ 4 * b))
    (A - 7 * c * a ^ 3 * b ^ 2) (B - 3 * c * a ^ 2 * b ^ 3)
  have hcQ := cubic_coefficients (A + 3 * c * a ^ 3 * b ^ 2)
    (B + 7 * c * a ^ 2 * b ^ 3) (5 * c * a * b ^ 4) (c * b ^ 5)
  simp only [← hp] at hcP
  simp only [← hq] at hcQ
  exact ⟨hcP.1, hcQ.2.2.2, hcP.2.2.1, hcQ.1, hcP.2.2.2, hcQ.2.1⟩

theorem int_abs_one (z : ℤ) (hz : z ≠ 0) : (1 : ℝ) ≤ |(z : ℝ)| := by
  have h : (1 : ℤ) ≤ |z| := by
    rcases le_total 0 z with h | h
    · rw [abs_of_nonneg h]
      omega
    · rw [abs_of_nonpos h]
      omega
  exact_mod_cast h

theorem int_abs_le_fifth (z : ℤ) :
    |(z : ℝ)| ≤ |(z : ℝ)| ^ 5 := by
  by_cases hz : z = 0
  · simp [hz]
  have h1 := int_abs_one z hz
  have h2 : (1 : ℝ) ≤ |(z : ℝ)| ^ 2 := by
    nlinarith only [h1, sq_nonneg (|(z : ℝ)| - 1)]
  have h4 : (1 : ℝ) ≤ |(z : ℝ)| ^ 4 := by
    nlinarith only [h2, sq_nonneg (|(z : ℝ)| ^ 2 - 1)]
  have hh := mul_le_mul_of_nonneg_left h4 (abs_nonneg (z : ℝ))
  nlinarith only [hh]

theorem normal_form_height_budget :
∀ H : ℝ, 1 ≤ H →
  ∀ (P Q : MvPolynomial (Fin 2) ℤ) (a b c A₀ B₀ : ℤ),
    Int.gcd a b = 1 → c ≠ 0 →
    (∀ m : Fin 2 →₀ ℕ,
      |((MvPolynomial.coeff m P : ℤ) : ℝ)| ≤ H ∧
      |((MvPolynomial.coeff m Q : ℤ) : ℝ)| ≤ H) →
    let X₀ : MvPolynomial (Fin 2) ℤ := MvPolynomial.X (0 : Fin 2);
    let X₁ : MvPolynomial (Fin 2) ℤ := MvPolynomial.X (1 : Fin 2);
    P =
      (MvPolynomial.C A₀ * X₀ + MvPolynomial.C B₀ * X₁) * X₁ ^ 2 -
        MvPolynomial.C c *
          (MvPolynomial.C a * X₀ + MvPolynomial.C b * X₁) ^ 2 *
          MvPolynomial.C (a ^ 2) *
          (MvPolynomial.C a * X₀ + MvPolynomial.C (3 * b) * X₁) →
    Q =
      (MvPolynomial.C A₀ * X₀ + MvPolynomial.C B₀ * X₁) * X₀ ^ 2 +
        MvPolynomial.C c *
          (MvPolynomial.C a * X₀ + MvPolynomial.C b * X₁) ^ 2 *
          MvPolynomial.C (b ^ 2) *
          (MvPolynomial.C (3 * a) * X₀ + MvPolynomial.C b * X₁) →
    |(a : ℝ)| ≤ H ∧
    |(b : ℝ)| ≤ H ∧
    |(c : ℝ)| ≤ H ∧
    |((a * B₀ - b * A₀ : ℤ) : ℝ)| ≤ 20 * H ^ 8
 := by
  intro H hH P Q a b c A B hab hc hCoeffs X₀ X₁ hP hQ
  obtain ⟨hp30, hq03, hp12, hq30, hp03, hq21⟩ :=
    normal_coefficients P Q a b c A B hP hQ
  have hp30R : ((coeff m30 P : ℤ) : ℝ) = -(c : ℝ) * (a : ℝ) ^ 5 := by
    exact_mod_cast hp30
  have hq03R : ((coeff m03 Q : ℤ) : ℝ) = (c : ℝ) * (b : ℝ) ^ 5 := by
    exact_mod_cast hq03
  have hca5 : |(c : ℝ)| * |(a : ℝ)| ^ 5 ≤ H := by
    have hh := (hCoeffs m30).1
    rw [hp30R, abs_mul, abs_neg, abs_pow] at hh
    exact hh
  have hcb5 : |(c : ℝ)| * |(b : ℝ)| ^ 5 ≤ H := by
    have hh := (hCoeffs m03).2
    rw [hq03R, abs_mul, abs_pow] at hh
    exact hh
  have hc1 := int_abs_one c hc
  have ha5 : |(a : ℝ)| ^ 5 ≤ H := by
    calc
      |(a : ℝ)| ^ 5 = 1 * |(a : ℝ)| ^ 5 := by ring
      _ ≤ |(c : ℝ)| * |(a : ℝ)| ^ 5 :=
        mul_le_mul_of_nonneg_right hc1 (pow_nonneg (abs_nonneg (a : ℝ)) 5)
      _ ≤ H := hca5
  have hb5 : |(b : ℝ)| ^ 5 ≤ H := by
    calc
      |(b : ℝ)| ^ 5 = 1 * |(b : ℝ)| ^ 5 := by ring
      _ ≤ |(c : ℝ)| * |(b : ℝ)| ^ 5 :=
        mul_le_mul_of_nonneg_right hc1 (pow_nonneg (abs_nonneg (b : ℝ)) 5)
      _ ≤ H := hcb5
  have ha : |(a : ℝ)| ≤ H := (int_abs_le_fifth a).trans ha5
  have hb : |(b : ℝ)| ≤ H := (int_abs_le_fifth b).trans hb5
  have habnz : a ≠ 0 ∨ b ≠ 0 := by
    by_contra hz
    push Not at hz
    rcases hz with ⟨ha0, hb0⟩
    simp [ha0, hb0] at hab
  have hcH : |(c : ℝ)| ≤ H := by
    rcases habnz with ha0 | hb0
    · have h1 : (1 : ℝ) ≤ |(a : ℝ)| ^ 5 :=
        (int_abs_one a ha0).trans (int_abs_le_fifth a)
      calc
        |(c : ℝ)| = |(c : ℝ)| * 1 := by ring
        _ ≤ |(c : ℝ)| * |(a : ℝ)| ^ 5 :=
          mul_le_mul_of_nonneg_left h1 (abs_nonneg (c : ℝ))
        _ ≤ H := hca5
    · have h1 : (1 : ℝ) ≤ |(b : ℝ)| ^ 5 :=
        (int_abs_one b hb0).trans (int_abs_le_fifth b)
      calc
        |(c : ℝ)| = |(c : ℝ)| * 1 := by ring
        _ ≤ |(c : ℝ)| * |(b : ℝ)| ^ 5 :=
          mul_le_mul_of_nonneg_left h1 (abs_nonneg (c : ℝ))
        _ ≤ H := hcb5
  have hAZ : 10 * A = 3 * coeff m12 P + 7 * coeff m30 Q := by
    rw [hp12, hq30]
    ring
  have hBZ : 10 * B = 7 * coeff m03 P + 3 * coeff m21 Q := by
    rw [hp03, hq21]
    ring
  have hAR : 10 * (A : ℝ) =
      3 * ((coeff m12 P : ℤ) : ℝ) + 7 * ((coeff m30 Q : ℤ) : ℝ) := by
    exact_mod_cast hAZ
  have hBR : 10 * (B : ℝ) =
      7 * ((coeff m03 P : ℤ) : ℝ) + 3 * ((coeff m21 Q : ℤ) : ℝ) := by
    exact_mod_cast hBZ
  obtain ⟨hp12lo, hp12hi⟩ := abs_le.mp (hCoeffs m12).1
  obtain ⟨hq30lo, hq30hi⟩ := abs_le.mp (hCoeffs m30).2
  obtain ⟨hp03lo, hp03hi⟩ := abs_le.mp (hCoeffs m03).1
  obtain ⟨hq21lo, hq21hi⟩ := abs_le.mp (hCoeffs m21).2
  have hA : |(A : ℝ)| ≤ H := by
    apply abs_le.mpr
    constructor <;> linarith only [hAR, hp12lo, hp12hi, hq30lo, hq30hi]
  have hB : |(B : ℝ)| ≤ H := by
    apply abs_le.mpr
    constructor <;> linarith only [hBR, hp03lo, hp03hi, hq21lo, hq21hi]
  have hHnonneg : 0 ≤ H := by linarith
  have hAB : |(a : ℝ)| * |(B : ℝ)| ≤ H * H :=
    mul_le_mul ha hB (abs_nonneg (B : ℝ)) hHnonneg
  have hBA : |(b : ℝ)| * |(A : ℝ)| ≤ H * H :=
    mul_le_mul hb hA (abs_nonneg (A : ℝ)) hHnonneg
  have htriangle : |(a : ℝ) * (B : ℝ) - (b : ℝ) * (A : ℝ)| ≤
      |(a : ℝ)| * |(B : ℝ)| + |(b : ℝ)| * |(A : ℝ)| := by
    have hn : |(-((b : ℝ) * (A : ℝ)))| = |(b : ℝ) * (A : ℝ)| := abs_neg _
    have hh := abs_add_le ((a : ℝ) * (B : ℝ)) (-((b : ℝ) * (A : ℝ)))
    rw [hn] at hh
    have hs : |(a : ℝ) * (B : ℝ) - (b : ℝ) * (A : ℝ)| ≤
        |(a : ℝ) * (B : ℝ)| + |(b : ℝ) * (A : ℝ)| := by
      simpa only [sub_eq_add_neg] using hh
    simpa only [abs_mul] using hs
  have hDeltaCast : ((a * B - b * A : ℤ) : ℝ) =
      (a : ℝ) * (B : ℝ) - (b : ℝ) * (A : ℝ) := by
    push_cast ; rfl
  have hDelta2 : |((a * B - b * A : ℤ) : ℝ)| ≤ 2 * H ^ 2 := by
    rw [hDeltaCast]
    nlinarith only [htriangle, hAB, hBA]
  have hH2 : (1 : ℝ) ≤ H ^ 2 := by
    nlinarith only [hH, sq_nonneg (H - 1)]
  have hH4 : H ^ 2 ≤ H ^ 4 := by
    have hh := mul_nonneg (sq_nonneg H) (by linarith only [hH2] : 0 ≤ H ^ 2 - 1)
    nlinarith only [hh]
  have hH8 : H ^ 4 ≤ H ^ 8 := by
    have hh := mul_nonneg (pow_nonneg hHnonneg 4)
      (by linarith only [hH2, hH4] : 0 ≤ H ^ 4 - 1)
    nlinarith only [hh]
  have hDelta : |((a * B - b * A : ℤ) : ℝ)| ≤ 20 * H ^ 8 := by
    nlinarith only [hDelta2, hH4, hH8, pow_nonneg hHnonneg 8]
  exact ⟨ha, hb, hcH, hDelta⟩

#print axioms cubic_coefficients
#print axioms normal_coefficients
#print axioms int_abs_le_fifth
end A5NormalFormHeightBudgetProof

namespace JocelynClaims
theorem claim_865afc155d79460ad2c12968c3a161c0b4b5cbe21101703a05307c82603bc9ce :
∀ H : ℝ, 1 ≤ H →
  ∀ (P Q : MvPolynomial (Fin 2) ℤ) (a b c A₀ B₀ : ℤ),
    Int.gcd a b = 1 → c ≠ 0 →
    (∀ m : Fin 2 →₀ ℕ,
      |((MvPolynomial.coeff m P : ℤ) : ℝ)| ≤ H ∧
      |((MvPolynomial.coeff m Q : ℤ) : ℝ)| ≤ H) →
    let X₀ : MvPolynomial (Fin 2) ℤ := MvPolynomial.X (0 : Fin 2);
    let X₁ : MvPolynomial (Fin 2) ℤ := MvPolynomial.X (1 : Fin 2);
    P =
      (MvPolynomial.C A₀ * X₀ + MvPolynomial.C B₀ * X₁) * X₁ ^ 2 -
        MvPolynomial.C c *
          (MvPolynomial.C a * X₀ + MvPolynomial.C b * X₁) ^ 2 *
          MvPolynomial.C (a ^ 2) *
          (MvPolynomial.C a * X₀ + MvPolynomial.C (3 * b) * X₁) →
    Q =
      (MvPolynomial.C A₀ * X₀ + MvPolynomial.C B₀ * X₁) * X₀ ^ 2 +
        MvPolynomial.C c *
          (MvPolynomial.C a * X₀ + MvPolynomial.C b * X₁) ^ 2 *
          MvPolynomial.C (b ^ 2) *
          (MvPolynomial.C (3 * a) * X₀ + MvPolynomial.C b * X₁) →
    |(a : ℝ)| ≤ H ∧
    |(b : ℝ)| ≤ H ∧
    |(c : ℝ)| ≤ H ∧
    |((a * B₀ - b * A₀ : ℤ) : ℝ)| ≤ 20 * H ^ 8
 := by
  exact A5NormalFormHeightBudgetProof.normal_form_height_budget
end JocelynClaims
#print axioms A5NormalFormHeightBudgetProof.normal_form_height_budget
#print axioms JocelynClaims.claim_865afc155d79460ad2c12968c3a161c0b4b5cbe21101703a05307c82603bc9ce
