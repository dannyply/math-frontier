-- Source SHA-256: a3b101141d91282fa5075f20243e6a549903cfd9fa8c436ca4d04889f707ef51
import Mathlib
import JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.LemmaP
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB

namespace FormalAB.S7d3914ac

set_option maxHeartbeats 700000
 
noncomputable section
namespace A3PolynomialTaylor
open FormalAB.S61c6e1a7.A1UniformTaylor
open MvPolynomial

def scaleV (t : ℝ) :
    MvPolynomial (Fin 2) ℝ →+* MvPolynomial (Fin 2) ℝ :=
  MvPolynomial.eval₂Hom MvPolynomial.C
    (fun i => if i = 0 then MvPolynomial.X 0 else
      MvPolynomial.C t * MvPolynomial.X 1)

theorem scaleV_monomial (t : ℝ) (d : Fin 2 →₀ ℕ) (a : ℝ) :
    scaleV t (MvPolynomial.monomial d a) =
      MvPolynomial.C (t ^ (d 1)) * MvPolynomial.monomial d a := by
  have hm : MvPolynomial.monomial d a =
      MvPolynomial.C a * MvPolynomial.X (0 : Fin 2) ^ (d 0) *
        MvPolynomial.X (1 : Fin 2) ^ (d 1) := by
    simp only [MvPolynomial.monomial_eq, Finsupp.prod_pow, Fin.prod_univ_two]
    ring
  calc
    scaleV t (MvPolynomial.monomial d a) =
        MvPolynomial.C a * MvPolynomial.X (0 : Fin 2) ^ (d 0) *
          (MvPolynomial.C t * MvPolynomial.X (1 : Fin 2)) ^ (d 1) := by
      unfold scaleV
      rw [MvPolynomial.eval₂Hom_monomial, Finsupp.prod_pow, Fin.prod_univ_two]
      norm_num
      ; ring
    _ = MvPolynomial.C (t ^ (d 1)) *
        (MvPolynomial.C a * MvPolynomial.X (0 : Fin 2) ^ (d 0) *
          MvPolynomial.X (1 : Fin 2) ^ (d 1)) := by
      rw [mul_pow, map_pow]
      ring
    _ = _ := by rw [← hm]

theorem coeff_scaleV (t : ℝ) (P : MvPolynomial (Fin 2) ℝ)
    (d : Fin 2 →₀ ℕ) :
    MvPolynomial.coeff d (scaleV t P) =
      t ^ (d 1) * MvPolynomial.coeff d P := by
  induction P using MvPolynomial.induction_on' with
  | monomial u a =>
      simp only [scaleV_monomial, MvPolynomial.coeff_C_mul,
        MvPolynomial.coeff_monomial]
      split_ifs with h
      · subst u
        rfl
      · simp
  | add p q hp hq =>
      rw [map_add, MvPolynomial.coeff_add, hp, hq, MvPolynomial.coeff_add]
      ring

#print axioms coeff_scaleV
theorem algebraMap_real_C (a : ℝ) :
    algebraMap ℝ (MvPolynomial (Fin 2) ℝ) a = MvPolynomial.C a := rfl

theorem scaleV_C (t a : ℝ) :
    scaleV t (MvPolynomial.C a) = MvPolynomial.C a := by
  unfold scaleV
  rw [MvPolynomial.eval₂Hom_C]

theorem scaleV_X0 (t : ℝ) :
    scaleV t (MvPolynomial.X (0 : Fin 2)) = MvPolynomial.X 0 := by
  simp [scaleV]

theorem scaleV_X1 (t : ℝ) :
    scaleV t (MvPolynomial.X (1 : Fin 2)) =
      MvPolynomial.C t * MvPolynomial.X 1 := by
  simp [scaleV]

theorem scaleV_aeval (t : ℝ) (F : Polynomial ℝ) :
    scaleV t (Polynomial.aeval
      (MvPolynomial.X (0 : Fin 2) : MvPolynomial (Fin 2) ℝ) F) =
    Polynomial.aeval
      (MvPolynomial.X (0 : Fin 2) : MvPolynomial (Fin 2) ℝ) F := by
  induction F using Polynomial.induction_on' with
  | monomial n a =>
    rw [← Polynomial.C_mul_X_pow_eq_monomial]
    simp only [map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X,
      algebraMap_real_C, scaleV_C, scaleV_X0]
  | add F G hF hG =>
    simp only [map_add, hF, hG]

theorem coefficientPolynomial_div (ell : ℕ)
    (c : Fin (ell + 1) → ℝ) (H : ℝ) :
    coefficientPolynomial ell (fun n => c n / H) =
      Polynomial.C H⁻¹ * coefficientPolynomial ell c := by
  simp only [coefficientPolynomial, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Polynomial.C_mul_monomial]
  congr 1
  simp only [div_eq_mul_inv]
  ring

theorem scaleV_normalized (ell : ℕ)
    (c : Fin (ell + 1) → ℝ) (H α β : ℝ) (a b : ℕ) :
    scaleV H⁻¹ (normalizedGraph
      (coefficientPolynomial ell (fun n => c n / H)) (α / H) (β / H) a b) =
      MvPolynomial.C ((H⁻¹) ^ (a + b)) *
        normalizedGraph (coefficientPolynomial ell c) α β a b := by
  have hlin :
      MvPolynomial.C (α / H) +
        MvPolynomial.C (β / H) * MvPolynomial.X (0 : Fin 2) =
      MvPolynomial.C H⁻¹ *
        (MvPolynomial.C α + MvPolynomial.C β * MvPolynomial.X 0) := by
    simp only [div_eq_mul_inv, map_mul]
    ring
  simp only [normalizedGraph, map_mul, map_pow, map_add,
    scaleV_C, scaleV_X0, scaleV_X1, scaleV_aeval]
  rw [hlin, coefficientPolynomial_div, map_mul, Polynomial.aeval_C]
  simp only [algebraMap_real_C]
  rw [← mul_add]
  simp only [ pow_add,  mul_pow]
  ring

theorem normalized_coeff_growth
    (ell A B : ℕ) (Kc : ℝ) (hKc : 0 ≤ Kc)
    (hunit :
      ∀ c : Fin (ell + 1) → ℝ, (∀ n, |c n| ≤ 1) →
      ∀ α β : ℝ, |α| ≤ 1 → |β| ≤ 1 →
      ∀ a b : ℕ, a ≤ A → b ≤ B →
      ∀ d : Fin 2 →₀ ℕ,
        |MvPolynomial.coeff d
          (normalizedGraph (coefficientPolynomial ell c) α β a b)| ≤ Kc)
    (H : ℝ) (hH : 1 ≤ H) (c : Fin (ell + 1) → ℝ)
    (hc : ∀ n, |c n| ≤ H) (α β : ℝ) (hα : |α| ≤ H) (hβ : |β| ≤ H)
    (a b : ℕ) (ha : a ≤ A) (hb : b ≤ B) (d : Fin 2 →₀ ℕ) :
    |MvPolynomial.coeff d
      (normalizedGraph (coefficientPolynomial ell c) α β a b)| ≤
        Kc * H ^ (A + B + 1) := by
  have hHpos : 0 < H := lt_of_lt_of_le zero_lt_one hH
  have hHne : H ≠ 0 := ne_of_gt hHpos
  have hc1 : ∀ n, |c n / H| ≤ 1 := by
    intro n
    rw [abs_div, abs_of_pos hHpos]
    exact (div_le_one hHpos).mpr (hc n)
  have hα1 : |α / H| ≤ 1 := by
    rw [abs_div, abs_of_pos hHpos]
    exact (div_le_one hHpos).mpr hα
  have hβ1 : |β / H| ≤ 1 := by
    rw [abs_div, abs_of_pos hHpos]
    exact (div_le_one hHpos).mpr hβ
  have hunitd := hunit (fun n => c n / H) hc1
    (α / H) (β / H) hα1 hβ1 a b ha hb d
  have hId :
      normalizedGraph (coefficientPolynomial ell c) α β a b =
      MvPolynomial.C (H ^ (a + b)) *
        scaleV H⁻¹ (normalizedGraph
          (coefficientPolynomial ell (fun n => c n / H)) (α / H) (β / H) a b) := by
    rw [scaleV_normalized, ← mul_assoc, ← map_mul, ← mul_pow,
      mul_inv_cancel₀ hHne, one_pow, map_one, one_mul]
  rw [hId, MvPolynomial.coeff_C_mul, coeff_scaleV]
  simp only [abs_mul, abs_pow, abs_inv, abs_of_pos hHpos]
  have hInv0 : 0 ≤ H⁻¹ := inv_nonneg.mpr hHpos.le
  have hInv1 : H⁻¹ ≤ 1 := by
    have hmul := mul_inv_cancel₀ hHne
    nlinarith [mul_nonneg (sub_nonneg.mpr hH) hInv0]
  have hInvPow : (H⁻¹) ^ (d 1) ≤ 1 := pow_le_one₀ hInv0 hInv1
  have hPow : H ^ (a + b) ≤ H ^ (A + B + 1) :=
    pow_le_pow_right₀ hH (by omega)
  calc
    H ^ (a + b) * ((H⁻¹) ^ (d 1) *
        |MvPolynomial.coeff d
          (normalizedGraph (coefficientPolynomial ell
            (fun n => c n / H)) (α / H) (β / H) a b)|) ≤
        H ^ (a + b) * (1 * Kc) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul hInvPow hunitd (abs_nonneg _) (by norm_num))
        (pow_nonneg hHpos.le _)
    _ ≤ Kc * H ^ (A + B + 1) := by
      nlinarith [mul_le_mul_of_nonneg_right hPow hKc]

#print axioms normalized_coeff_growth

def PolynomialHeightTaylorGraphStatement : Prop :=
  ∀ ell A B : ℕ,
    ∃ K : ℝ, 0 < K ∧
      ∀ r H : ℝ, 0 < r → 1 ≤ H →
      ∀ f : ℝ → ℝ,
        ContDiffOn ℝ (ell + 1) f (Set.Ioo (-r) r) →
        (∀ n : ℕ, n ≤ ell + 1 →
          ∀ x ∈ Set.Ioo (-r) r, |iteratedDeriv n f x| ≤ H) →
        ∀ α β : ℝ, |α| ≤ H → |β| ≤ H →
        ∀ a b : ℕ, a ≤ A → b ≤ B →
          let P := normalizedGraph (taylorPolynomial ell f) α β a b
          (∀ d : Fin 2 →₀ ℕ,
            |MvPolynomial.coeff d P| ≤ K * H ^ (A + B + 1)) ∧
          (∀ d ∈ P.support,
            d (0 : Fin 2) ≤ a + b * ell ∧ d (1 : Fin 2) ≤ b) ∧
          (∀ u v : ℝ, |u| ≤ min (r / 2) 1 → |v| ≤ 1 →
            |(α + β * u) ^ a * (f u + v) ^ b -
              MvPolynomial.eval (fun s : Fin 2 => if s = 0 then u else v) P| ≤
              K * H ^ (A + B + 1) * |u| ^ (ell + 1))

theorem polynomialHeightTaylorGraph : PolynomialHeightTaylorGraphStatement := by
  intro ell A B
  obtain ⟨Kc, hKc, hunit⟩ :=
    uniform_coefficient_graph_bound ell A B 1 1 (by norm_num) (by norm_num)
  let Ke : ℝ := (2 : ℝ) ^ A * (B : ℝ) * ((ell : ℝ) + 3) ^ B
  let K : ℝ := Kc + Ke + 1
  have hKe0 : 0 ≤ Ke := by dsimp [Ke]; positivity
  have hK : 0 < K := by dsimp [K]; linarith
  have hKcK : Kc ≤ K := by dsimp [K]; linarith
  have hKeK : Ke ≤ K := by dsimp [K]; linarith
  refine ⟨K, hK, ?_⟩
  intro r H hr hH f hf hd α β hα hβ a b ha hb
  have hHpos : 0 < H := lt_of_lt_of_le zero_lt_one hH
  have hH0 : 0 ≤ H := hHpos.le
  let c : Fin (ell + 1) → ℝ :=
    fun n => iteratedDeriv (n : ℕ) f 0 / ((n : ℕ).factorial : ℝ)
  have h0 : (0 : ℝ) ∈ Set.Ioo (-r) r := ⟨by linarith, hr⟩
  have hc : ∀ n, |c n| ≤ H := by
    intro n
    exact taylorScalarCoeff_bound hH0
      (hd n (by have := n.isLt; omega) 0 h0)
  have hcf : ∀ n ≤ ell, |iteratedDeriv n f 0| ≤ H :=
    fun n hn => hd n (by omega) 0 h0
  have heq : taylorPolynomial ell f = coefficientPolynomial ell c :=
    taylorPolynomial_eq_coefficients ell f
  refine ⟨?_, ?_, ?_⟩
  · intro d
    rw [heq]
    exact (normalized_coeff_growth ell A B Kc hKc.le hunit
      H hH c hc α β hα hβ a b ha hb d).trans
      (mul_le_mul_of_nonneg_right hKcK (pow_nonneg hH0 _))
  · rw [heq]
    exact normalizedGraph_support ell c α β a b
  · intro u v hu hv
    have hur : |u| ≤ r / 2 := hu.trans (min_le_left _ _)
    have hu1 : |u| ≤ 1 := hu.trans (min_le_right _ _)
    have huI : u ∈ Set.Ioo (-r) r := by
      have hat := abs_le.mp hur
      constructor <;> linarith
    have hfu : |f u| ≤ H := by simpa using hd 0 (by omega) u huI
    have hF := taylorPolynomial_eval_bound ell f H u hH0 hcf hu1
    have hxy := scalar_taylor_remainder ell r H hr hH0 f hf hd u hur
    let U : ℝ := 2 * H
    let S : ℝ := ((ell : ℝ) + 3) * H
    have hU : 1 ≤ U := by dsimp [U]; linarith
    have hU0 : 0 ≤ U := zero_le_one.trans hU
    have hS : 1 ≤ S := by
      dsimp [S]
      nlinarith [mul_nonneg (Nat.cast_nonneg ell : (0 : ℝ) ≤ ell) hH0]
    have hS0 : 0 ≤ S := zero_le_one.trans hS
    have haff : |α + β * u| ≤ U := by
      calc
        _ ≤ |α| + |β * u| := abs_add_le _ _
        _ = |α| + |β| * |u| := by rw [abs_mul]
        _ ≤ H + H * 1 :=
          add_le_add hα (mul_le_mul hβ hu1 (abs_nonneg _) hH0)
        _ = U := by dsimp [U]; ring
    have hxS : |f u + v| ≤ S := by
      have hh := (abs_add_le (f u) v).trans (add_le_add hfu hv)
      dsimp [S]
      nlinarith [mul_nonneg (Nat.cast_nonneg ell : (0 : ℝ) ≤ ell) hH0]
    have hFS : |(taylorPolynomial ell f).eval u + v| ≤ S := by
      have hh := (abs_add_le ((taylorPolynomial ell f).eval u) v).trans
        (add_le_add hF hv)
      dsimp [S]
      nlinarith
    have hE : 0 ≤ H * |u| ^ (ell + 1) := by positivity
    have herr := normalizedGraph_error_bound (taylorPolynomial ell f)
      α β u v (f u) U S (H * |u| ^ (ell + 1)) a b
      hU0 hS hE haff hxS hFS hxy
    have hUa : U ^ a ≤ U ^ A := pow_le_pow_right₀ hU ha
    have hSb : S ^ b ≤ S ^ B := pow_le_pow_right₀ hS hb
    have hbR : (b : ℝ) ≤ B := by exact_mod_cast hb
    have hprod0 : U ^ a * ((b : ℝ) * S ^ b * H) ≤
        U ^ A * (B : ℝ) * S ^ B * H := by
      simpa only [mul_assoc] using mul_le_mul
        (mul_le_mul
          (mul_le_mul hUa hbR (Nat.cast_nonneg _) (pow_nonneg hU0 _))
          hSb (pow_nonneg hS0 _) (by positivity))
        le_rfl hH0 (by positivity)
    have hform : U ^ A * (B : ℝ) * S ^ B * H =
        Ke * H ^ (A + B + 1) := by
      dsimp [U, S, Ke]
      simp only [mul_pow, pow_add, pow_one]
      ring
    calc
      _ ≤ U ^ a * ((b : ℝ) * S ^ b * (H * |u| ^ (ell + 1))) := herr
      _ = (U ^ a * ((b : ℝ) * S ^ b * H)) * |u| ^ (ell + 1) := by ring
      _ ≤ (Ke * H ^ (A + B + 1)) * |u| ^ (ell + 1) :=
        mul_le_mul_of_nonneg_right (hprod0.trans_eq hform)
          (pow_nonneg (abs_nonneg _) _)
      _ ≤ K * H ^ (A + B + 1) * |u| ^ (ell + 1) := by
        gcongr

#print axioms polynomialHeightTaylorGraph

end A3PolynomialTaylor

namespace JocelynClaims

theorem claim_84ae2eb54a1990451db292dbe4e667b093a1ae115d5814ef4364ef56097697bd :
∀ ell A B : ℕ,
    ∃ K : ℝ, 0 < K ∧
      ∀ r H : ℝ, 0 < r → 1 ≤ H →
      ∀ f : ℝ → ℝ,
        ContDiffOn ℝ (ell + 1) f (Set.Ioo (-r) r) →
        (∀ n : ℕ, n ≤ ell + 1 →
          ∀ x ∈ Set.Ioo (-r) r, |iteratedDeriv n f x| ≤ H) →
        ∀ α β : ℝ, |α| ≤ H → |β| ≤ H →
        ∀ a b : ℕ, a ≤ A → b ≤ B →
          let P := FormalAB.S61c6e1a7.A1UniformTaylor.normalizedGraph (FormalAB.S61c6e1a7.A1UniformTaylor.taylorPolynomial ell f) α β a b
          (∀ d : Fin 2 →₀ ℕ,
            |MvPolynomial.coeff d P| ≤ K * H ^ (A + B + 1)) ∧
          (∀ d ∈ P.support,
            d (0 : Fin 2) ≤ a + b * ell ∧ d (1 : Fin 2) ≤ b) ∧
          (∀ u v : ℝ, |u| ≤ min (r / 2) 1 → |v| ≤ 1 →
            |(α + β * u) ^ a * (f u + v) ^ b -
              MvPolynomial.eval (fun s : Fin 2 => if s = 0 then u else v) P| ≤
              K * H ^ (A + B + 1) * |u| ^ (ell + 1)) := by
  exact A3PolynomialTaylor.polynomialHeightTaylorGraph

end JocelynClaims

#print axioms JocelynClaims.claim_84ae2eb54a1990451db292dbe4e667b093a1ae115d5814ef4364ef56097697bd
