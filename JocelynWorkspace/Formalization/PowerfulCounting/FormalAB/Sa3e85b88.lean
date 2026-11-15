-- Source SHA-256: a20033e7e10a69ce57cda7459520ae33f31067c1b14cd524e4766a4e19b4d7ad
import Mathlib
import JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.LemmaP
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB

namespace FormalAB.Sa3e85b88

noncomputable section
namespace A5PolynomialDiameter
open Polynomial Set
set_option maxHeartbeats 1500000

theorem positive_curvature_diameter
    (p : Polynomial ℝ) (a b L U k : ℝ) (hab : a < b) (_hk : 0 < k)
    (hvals : ∀ t : ℝ, a ≤ t → t ≤ b → L ≤ p.eval t ∧ p.eval t ≤ U)
    (hcurv : ∀ t : ℝ, a < t → t < b → k ≤ p.derivative.derivative.eval t) :
    k * (b - a) ^ 2 ≤ 8 * (U - L) := by
  let r : Polynomial ℝ := p - C (k / 2) * X ^ 2
  have hrsecond (t : ℝ) :
      r.derivative.derivative.eval t = p.derivative.derivative.eval t - k := by
    norm_num [r, Polynomial.derivative_mul]
  have hderiv : deriv (fun t : ℝ => r.eval t) =
      (fun t : ℝ => r.derivative.eval t) := by
    funext t
    exact Polynomial.deriv r
  have hconv : ConvexOn ℝ (Icc a b) (fun t : ℝ => r.eval t) := by
    apply convexOn_of_deriv2_nonneg (convex_Icc a b) r.continuous.continuousOn
    · intro t ht
      exact (r.hasDerivAt t).differentiableAt.differentiableWithinAt
    · rw [hderiv]
      intro t ht
      exact (r.derivative.hasDerivAt t).differentiableAt.differentiableWithinAt
    · intro t ht
      change 0 ≤ deriv (deriv (fun t : ℝ => r.eval t)) t
      rw [hderiv, Polynomial.deriv, hrsecond]
      have htt : a < t ∧ t < b := by simpa only [interior_Icc, Set.mem_Ioo] using ht
      have hh := hcurv t htt.1 htt.2
      linarith
  have hmid :
      r.eval ((1 / 2 : ℝ) • a + (1 / 2 : ℝ) • b) ≤
        (1 / 2 : ℝ) • r.eval a + (1 / 2 : ℝ) • r.eval b :=
    hconv.2 (show a ∈ Icc a b from ⟨le_rfl, hab.le⟩)
      (show b ∈ Icc a b from ⟨hab.le, le_rfl⟩)
      (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  simp only [smul_eq_mul] at hmid
  have harg : (1 / 2 : ℝ) * a + (1 / 2 : ℝ) * b = (a + b) / 2 := by ring
  rw [harg] at hmid
  simp only [r, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X] at hmid
  have ha := hvals a le_rfl hab.le
  have hb := hvals b hab.le le_rfl
  have hm := hvals ((a + b) / 2) (by linarith) (by linarith)
  nlinarith only [hmid, ha.2, hb.2, hm.1]

theorem polynomial_curvature_diameter :
∀ (p : Polynomial ℝ) (a b L U k : ℝ),
  a < b → 0 < k →
  (∀ t : ℝ, a ≤ t → t ≤ b → L ≤ p.eval t ∧ p.eval t ≤ U) →
  ((∀ t : ℝ, a < t → t < b → k ≤ p.derivative.derivative.eval t) ∨
   (∀ t : ℝ, a < t → t < b → p.derivative.derivative.eval t ≤ -k)) →
  k * (b - a) ^ 2 ≤ 8 * (U - L)
 := by
  intro p a b L U k hab hk hvals hcurv
  rcases hcurv with hpos | hneg
  · exact positive_curvature_diameter p a b L U k hab hk hvals hpos
  · have hminusvals : ∀ t : ℝ, a ≤ t → t ≤ b →
        -U ≤ (-p).eval t ∧ (-p).eval t ≤ -L := by
      intro t hta htb
      have hh := hvals t hta htb
      simp only [Polynomial.eval_neg]
      constructor <;> linarith
    have hminuscurv : ∀ t : ℝ, a < t → t < b →
        k ≤ (-p).derivative.derivative.eval t := by
      intro t hta htb
      have hh := hneg t hta htb
      simp only [Polynomial.derivative_neg, Polynomial.eval_neg]
      linarith
    have hh := positive_curvature_diameter (-p) a b (-U) (-L) k hab hk
      hminusvals hminuscurv
    linarith only [hh]
end A5PolynomialDiameter

namespace JocelynClaims
theorem claim_3e75905b2d0f06455e160821601d7b7ded491039a7f5b69aba31febcf9b0c31f :
∀ (p : Polynomial ℝ) (a b L U k : ℝ),
  a < b → 0 < k →
  (∀ t : ℝ, a ≤ t → t ≤ b → L ≤ p.eval t ∧ p.eval t ≤ U) →
  ((∀ t : ℝ, a < t → t < b → k ≤ p.derivative.derivative.eval t) ∨
   (∀ t : ℝ, a < t → t < b → p.derivative.derivative.eval t ≤ -k)) →
  k * (b - a) ^ 2 ≤ 8 * (U - L)
 := by
  exact A5PolynomialDiameter.polynomial_curvature_diameter
end JocelynClaims
#print axioms A5PolynomialDiameter.polynomial_curvature_diameter
#print axioms JocelynClaims.claim_3e75905b2d0f06455e160821601d7b7ded491039a7f5b69aba31febcf9b0c31f
