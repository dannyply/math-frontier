-- Source SHA-256: 30df05dccc33995bd2b25816f24a5f7c7c569609f76ecfea4f700a1331fced61
import Mathlib
import JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.LemmaP
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB

namespace FormalAB.S7c60f425

set_option maxHeartbeats 3000000
set_option maxRecDepth 8000

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

namespace A3PolynomialOriginalDeterminant
noncomputable section

abbrev q : ℕ := 4096
abbrev Rect := FormalAB.S61c6e1a7.A1OriginalDeterminant.Rect q

def mu : ℝ := 19 / 100
def J : ℕ := (3 * q + 1) * (2 * q + 1)
def gap : ℝ := 19 * (q : ℝ) ^ 3 / 1440

def PolynomialOriginalDeterminantStatement : Prop :=
  ∃ ell : ℕ,
    (J : ℝ) * (q : ℝ) + gap + 1 < mu * ((ell : ℝ) + 1) ∧
    ∀ (B : ℝ) (E : ℕ), 1 ≤ B →
      ∃ (C : ℝ) (K : ℕ), 2 ≤ C ∧ 1 ≤ K ∧
        ∀ (A T r center : ℝ) (f : ℝ → ℝ)
          (y1 y2 x1 x2 : Rect → ℤ) (u v : Rect → ℝ),
          1 ≤ A → C * A ^ K ≤ T →
          (B * A ^ E)⁻¹ ≤ r →
          |center| ≤ B * A ^ E →
          ContDiffOn ℝ (ell + 1) f (Set.Ioo (-r) r) →
          (∀ n : ℕ, n ≤ ell + 1 →
            ∀ t ∈ Set.Ioo (-r) r,
              |iteratedDeriv n f t| ≤ B * A ^ E) →
          (∀ i, y2 i ≠ 0 ∧ x2 i ≠ 0) →
          (∀ i, u i = (y1 i : ℝ) / (y2 i : ℝ) - center) →
          (∀ i, v i = (x1 i : ℝ) / (x2 i : ℝ) - f (u i)) →
          (∀ i, |u i| ≤ (B * A ^ E) * T ^ (-mu)) →
          (∀ i, |v i| ≤ (B * A ^ E) * T ^ (-(1 : ℝ))) →
          (∀ i, |(y2 i : ℝ) ^ (3 * q) * (x2 i : ℝ) ^ (2 * q)| ≤
            (B * A ^ E) * T ^ (q : ℝ)) →
          |(FormalAB.S61c6e1a7.A1OriginalDeterminant.rawEval
              q y1 y2 x1 x2).det| ≤
              C * A ^ K * T ^ (-((J : ℝ) * (q : ℝ)) - gap) ∧
            (FormalAB.S61c6e1a7.A1OriginalDeterminant.clearedEval
              q y1 y2 x1 x2).det = 0

end
end A3PolynomialOriginalDeterminant

namespace A3PolynomialDeterminantCore
noncomputable section
open FormalAB.S61c6e1a7.A1OriginalDeterminant
open scoped BigOperators

def determinantCost (q L : ℕ) (Cu Cv Ccoeff Crem : ℝ) : ℝ :=
  let h := Fintype.card (FormalAB.S61c6e1a7.A1OriginalDeterminant.Rect q)
  let Jet := {m : ℕ × ℕ // m ∈ FormalAB.S61c6e1a7.A1OriginalDeterminant.jets L}
  (2 : ℝ) ^ h *
    ((Fintype.card Jet : ℝ) ^ h * (h.factorial : ℝ) * Ccoeff ^ h *
      (∑ σ : FormalAB.S61c6e1a7.A1OriginalDeterminant.Rect q → Jet,
        ∏ i, Cu ^ (σ i).val.1 * Cv ^ (σ i).val.2) +
      (h.factorial : ℝ) * Crem *
        (Ccoeff * (∑ m : Jet, Cu ^ m.val.1 * Cv ^ m.val.2) + Crem + 1) ^ h)

theorem weighted_det {I:Type*} [Fintype I] [DecidableEq I]
    (Q:Matrix I I ℝ) (w:I → ℝ)
    (hw : ∀ i,0 < w i) (hQ : ∀ i j,|Q i j| ≤ w i) :
    |Q.det| ≤ ((Fintype.card I).factorial:ℝ) * ∏ i,w i := by
  let B:Matrix I I ℝ := fun i j => Q i j/w i
  have hB : ∀ i j,|B i j| ≤ (1:ℝ) := by
    intro i j
    dsimp [B]
    rw [abs_div,abs_of_pos (hw i)]
    exact (div_le_one (hw i)).mpr (hQ i j)
  have hBd : |B.det| ≤ ((Fintype.card I).factorial:ℝ) := by
    simpa [nsmul_eq_mul] using
      (Matrix.det_le (abv := AbsoluteValue.abs) hB)
  have hmat:(Matrix.of fun i j => w i*B i j) = Q := by
    ext i j
    dsimp [B]
    field_simp [ne_of_gt (hw i)]
  have hd:Q.det = (∏ i,w i)*B.det := by
    rw [← hmat]
    exact Matrix.det_mul_column w B
  have hwprod:0 < ∏ i,w i :=
    Finset.prod_pos (fun i _ => hw i)
  rw [hd,abs_mul,abs_of_pos hwprod]
  calc
    _ ≤ (∏ i,w i)*((Fintype.card I).factorial:ℝ) :=
      mul_le_mul_of_nonneg_left hBd (le_of_lt hwprod)
    _ = _ := by ring
theorem det_expansion
    {I K:Type*} [Fintype I] [Fintype K]
    [DecidableEq I] [DecidableEq K]
    (V:Matrix I K ℝ) (C:Matrix K I ℝ) :
    (V*C).det =
      ∑ σ:I → K,
        (∏ i,V i (σ i)) *
          (Matrix.of fun i j => C (σ i) j).det := by
  have he :=
    (Matrix.detRowAlternating (n := I) (R := ℝ)).toMultilinearMap.map_sum
      (fun (i:I) (k:K) => (V i k:ℝ) • (fun j:I => C k j))
  have hrows :
      (fun i:I => ∑ k:K,
        (V i k:ℝ) • (fun j:I => C k j)) =
      (fun (i:I) (j:I) => ∑ k:K,V i k*C k j) := by
    funext i j
    simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  rw [hrows] at he
  change (Matrix.of fun i j => ∑ k,V i k*C k j).det =
    ∑ σ:I → K,
      (Matrix.of fun i j => V i (σ i)*C (σ i) j).det at he
  have hmul:V*C =
      Matrix.of (fun i j => ∑ k,V i k*C k j) := by
    ext i j
    exact Matrix.mul_apply
  rw [hmul,he]
  apply Finset.sum_congr rfl
  intro σ hσ
  exact Matrix.det_mul_column (fun i => V i (σ i))
    (Matrix.of fun i j => C (σ i) j)
theorem signed_original_row_identity
    (q:ℕ) (y1 y2 x1 x2:Rect q → ℤ)
    (i ab:Rect q) (hy:y2 i ≠ 0) (hx:x2 i ≠ 0) :
    ((clearedEval q y1 y2 x1 x2 i ab:ℤ):ℝ) =
      (y2 i:ℝ) ^ (3*q)*(x2 i:ℝ) ^ (2*q) *
        rawEval q y1 y2 x1 x2 i ab := by
  have ha:ab.1.val ≤ 3*q :=
    Nat.lt_succ_iff.mp ab.1.isLt
  have hb:ab.2.val ≤ 2*q :=
    Nat.lt_succ_iff.mp ab.2.isLt
  have hy' : (y2 i:ℝ) ≠ 0 := by exact_mod_cast hy
  have hx' : (x2 i:ℝ) ≠ 0 := by exact_mod_cast hx
  have hpowY :
      (y2 i:ℝ) ^ (3*q) =
        (y2 i:ℝ) ^ (3*q - ab.1.val) *
          (y2 i:ℝ) ^ ab.1.val := by
    rw [← pow_add,Nat.sub_add_cancel ha]
  have hpowX :
      (x2 i:ℝ) ^ (2*q) =
        (x2 i:ℝ) ^ (2*q - ab.2.val) *
          (x2 i:ℝ) ^ ab.2.val := by
    rw [← pow_add,Nat.sub_add_cancel hb]
  simp only [clearedEval,rawEval,Int.cast_mul,Int.cast_pow]
  rw [hpowY,hpowX,div_pow,div_pow]
  field_simp [hy',hx']
theorem weighted_matrix_det
    {I K:Type*} [Fintype I] [Fintype K]
    [DecidableEq I] [DecidableEq K]
    (V:Matrix I K ℝ) (C:Matrix K I ℝ)
    (w:K → ℝ) (C₀ R:ℝ)
    (hC₀:0 < C₀) (hR:0 ≤ R)
    (hw : ∀ k,0 ≤ w k)
    (hV : ∀ i k,|V i k| ≤ w k)
    (hC : ∀ k j,|C k j| ≤ C₀)
    (hminor : ∀ σ:I → K,
      (Matrix.of fun i j => C (σ i) j).det ≠ 0 →
      (∏ i,w (σ i)) ≤ R) :
    |(V*C).det| ≤
      (Fintype.card K:ℝ) ^ (Fintype.card I) *
        ((Fintype.card I).factorial:ℝ)*C₀ ^ (Fintype.card I)*R := by
  rw [det_expansion V C]
  let H:ℝ := ((Fintype.card I).factorial:ℝ)*C₀ ^ (Fintype.card I)
  have hH:0 ≤ H := by dsimp [H]; positivity
  calc
    |∑ σ:I → K,(∏ i,V i (σ i)) *
        (Matrix.of fun i j => C (σ i) j).det|
      ≤ ∑ σ:I → K,
          |(∏ i,V i (σ i)) *
            (Matrix.of fun i j => C (σ i) j).det| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ σ:I → K,H*R := by
      apply Finset.sum_le_sum
      intro σ hσ
      by_cases hz:(Matrix.of fun i j => C (σ i) j).det = 0
      · simpa only [hz,mul_zero,abs_zero] using (mul_nonneg hH hR)
      · have hprod :
            |∏ i,V i (σ i)| ≤ ∏ i,w (σ i) := by
          rw [Finset.abs_prod]
          exact Finset.prod_le_prod
            (fun i hi => abs_nonneg _)
            (fun i hi => hV i (σ i))
        have hdet :
            |(Matrix.of fun i j => C (σ i) j).det| ≤ H := by
          have hh := weighted_det
            (Matrix.of fun i j => C (σ i) j)
            (fun _:I => C₀)
            (fun _ => hC₀)
            (fun i j => hC (σ i) j)
          simpa [H] using hh
        rw [abs_mul]
        calc
          |∏ i,V i (σ i)| *
              |(Matrix.of fun i j => C (σ i) j).det|
            ≤ (∏ i,w (σ i))*H :=
                mul_le_mul hprod hdet (abs_nonneg _)
                  (Finset.prod_nonneg (fun i _ => hw (σ i)))
          _ ≤ R*H :=
                mul_le_mul_of_nonneg_right (hminor σ hz) hH
          _ = H*R := by ring
    _ = (Fintype.card K:ℝ) ^ (Fintype.card I) *
        ((Fintype.card I).factorial:ℝ)*C₀ ^ (Fintype.card I)*R := by
      simp [H,nsmul_eq_mul]
      ring
theorem det_two_sum_rows
    {I:Type*} [Fintype I] [DecidableEq I]
    (F R:Matrix I I ℝ) :
    (F+R).det =
      ∑ σ:I → Bool,
        (Matrix.of fun i j => if σ i then R i j else F i j).det := by
  have he :=
    (Matrix.detRowAlternating (n := I) (R := ℝ)).toMultilinearMap.map_sum
      (fun (i:I) (b:Bool) =>
        if b then (fun j:I => R i j) else (fun j:I => F i j))
  have hrows :
      (fun i:I => ∑ b:Bool,
        if b then (fun j:I => R i j) else (fun j:I => F i j)) =
      (fun i:I => fun j:I => F i j+R i j) := by
    funext i j
    simp [add_comm]
  rw [hrows] at he
  calc
    (F+R).det = (Matrix.of fun i j => F i j+R i j).det := rfl
    _ = ∑ σ:I → Bool,
        (Matrix.of fun i j =>
          (if σ i then (fun j:I => R i j) else (fun j:I => F i j)) j).det := he
    _ = ∑ σ:I → Bool,
        (Matrix.of fun i j => if σ i then R i j else F i j).det := by
      apply Finset.sum_congr rfl
      intro σ hσ
      congr 1
      funext i j
      cases h:σ i <;> simp [h]
theorem rpow_finset_sum
    {I:Type*} [DecidableEq I]
    (s:Finset I) (X:ℝ) (hX:0 < X) (g:I → ℝ) :
    (∏ i ∈ s,X ^ g i) = X ^ (∑ i ∈ s,g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      simp [hi,ih,Real.rpow_add hX]
theorem jet_value_bound
    (μ X Cu Cv:ℝ) (a b:ℕ)
    (hX:1 ≤ X) (hCu:0 ≤ Cu) (_hCv:0 ≤ Cv)
    (u v:ℝ)
    (hu : |u| ≤ Cu*X ^ (-μ))
    (hv : |v| ≤ Cv*X ^ (-(1:ℝ))) :
    |u ^ a*v ^ b| ≤
      Cu ^ a*Cv ^ b *
        X ^ (-(μ*(a:ℝ)+(b:ℝ))) := by
  have hXp:0 < X := lt_of_lt_of_le zero_lt_one hX
  calc
    |u ^ a*v ^ b| = |u| ^ a * |v| ^ b := by rw [abs_mul,abs_pow,abs_pow]
    _ ≤ (Cu*X ^ (-μ)) ^ a*(Cv*X ^ (-(1:ℝ))) ^ b := by
      gcongr
    _ = Cu ^ a*Cv ^ b *
        X ^ (-(μ*(a:ℝ)+(b:ℝ))) := by
      rw [mul_pow,mul_pow]
      have hU:(X ^ (-μ)) ^ a = X ^ (-(μ*(a:ℝ))) := by
        rw [← Real.rpow_natCast,← Real.rpow_mul (le_of_lt hXp)]
        congr 1
        ring
      have hV:(X ^ (-(1:ℝ))) ^ b = X ^ (-(b:ℝ)) := by
        rw [← Real.rpow_natCast,← Real.rpow_mul (le_of_lt hXp)]
        congr 1
        ring
      rw [hU,hV]
      calc
        Cu ^ a*X ^ (-(μ*(a:ℝ))) *
            (Cv ^ b*X ^ (-(b:ℝ))) =
          Cu ^ a*Cv ^ b *
            (X ^ (-(μ*(a:ℝ)))*X ^ (-(b:ℝ))) := by ring
        _ = Cu ^ a*Cv ^ b *
            X ^ (-(μ*(a:ℝ)+(b:ℝ))) := by
          rw [← Real.rpow_add hXp]
          congr 1
          ring
theorem finite_weighted_det
    {I K:Type*} [Fintype I] [Fintype K]
    [DecidableEq I] [DecidableEq K]
    (V:Matrix I K ℝ) (C:Matrix K I ℝ)
    (g c:K → ℝ) (T C₀ X:ℝ)
    (hX:1 ≤ X) (hC₀:0 < C₀)
    (hc : ∀ k,0 ≤ c k)
    (hV : ∀ i k,|V i k| ≤ c k*X ^ (-g k))
    (hC : ∀ k j,|C k j| ≤ C₀)
    (hminor : ∀ σ:I → K,
      (Matrix.of fun i j => C (σ i) j).det ≠ 0 →
      T ≤ ∑ i:I,g (σ i)) :
    |(V*C).det| ≤
      (Fintype.card K:ℝ) ^ (Fintype.card I) *
        ((Fintype.card I).factorial:ℝ)*C₀ ^ (Fintype.card I) *
        (∑ σ:I → K,∏ i:I,c (σ i))*X ^ (-T) := by
  let w:K → ℝ := fun k => c k*X ^ (-g k)
  let Ksum:ℝ := ∑ σ:I → K,∏ i:I,c (σ i)
  have hXp:0 < X := lt_of_lt_of_le zero_lt_one hX
  have hw : ∀ k,0 ≤ w k := by
    intro k
    dsimp [w]
    have hck := hc k
    positivity
  have hKterm : ∀ σ:I → K,0 ≤ ∏ i:I,c (σ i) := by
    intro σ
    exact Finset.prod_nonneg (fun i hi => hc (σ i))
  have hKsum:0 ≤ Ksum := by
    dsimp [Ksum]
    exact Finset.sum_nonneg (fun σ hσ => hKterm σ)
  have hR:0 ≤ Ksum*X ^ (-T) := by positivity
  have hprod (σ:I → K)
      (hσ:(Matrix.of fun i j => C (σ i) j).det ≠ 0) :
      (∏ i,w (σ i)) ≤ Ksum*X ^ (-T) := by
    have hweight := hminor σ hσ
    have hpow:X ^ (-(∑ i:I,g (σ i))) ≤ X ^ (-T) := by
      gcongr
    have hsingle:(∏ i:I,c (σ i)) ≤ Ksum := by
      dsimp [Ksum]
      exact Finset.single_le_sum
        (fun τ hτ => hKterm τ) (Finset.mem_univ σ)
    have hfactor :
        (∏ i,w (σ i)) =
          (∏ i:I,c (σ i)) *
            X ^ (-(∑ i:I,g (σ i))) := by
      simp only [w,Finset.prod_mul_distrib]
      rw [rpow_finset_sum (Finset.univ:Finset I) X hXp
        (fun i => -g (σ i))]
      congr 1
      simp
    rw [hfactor]
    exact mul_le_mul hsingle hpow (by positivity) hKsum
  have hh := weighted_matrix_det V C w C₀
    (Ksum*X ^ (-T)) hC₀ hR hw
    (by simpa only [w] using hV) hC hprod
  simpa [Ksum,mul_assoc] using hh
theorem prod_bool_row_bound
    {I:Type*} [Fintype I] [DecidableEq I]
    (σ:I → Bool) (e M:ℝ)
    (hσ : ∃ i,σ i = true)
    (he:0 < e) (hM:1 ≤ M) (heM:e ≤ M) :
    (∏ i,if σ i then e else M) ≤ e*M ^ (Fintype.card I) := by
  rcases hσ with ⟨i₀,hi₀⟩
  let w:I → ℝ := fun i => if σ i then e else M
  have hnonneg : ∀ i,0 ≤ w i := by
    intro i
    dsimp [w]
    split_ifs <;> linarith
  have hle : ∀ i,w i ≤ M := by
    intro i
    dsimp [w]
    split_ifs <;> linarith
  have hrest :
      (∏ i ∈ (Finset.univ:Finset I).erase i₀,w i) ≤
        M ^ (Fintype.card I) := by
    calc
      _ ≤ ∏ i ∈ (Finset.univ:Finset I).erase i₀,M :=
        Finset.prod_le_prod
          (fun i hi => hnonneg i)
          (fun i hi => hle i)
      _ = M ^ ((Finset.univ:Finset I).erase i₀).card := by simp
      _ ≤ M ^ (Fintype.card I) := by
        apply pow_le_pow_right₀ hM
        exact Finset.card_le_card (Finset.erase_subset _ _)
  calc
    (∏ i,if σ i then e else M) =
        w i₀ * ∏ i ∈ (Finset.univ:Finset I).erase i₀,w i := by
          simpa [w] using
            (Finset.mul_prod_erase (Finset.univ:Finset I)
              (Finset.mem_univ i₀) (f := w)).symm
    _ = e * ∏ i ∈ (Finset.univ:Finset I).erase i₀,w i := by
          simp [w,hi₀]
    _ ≤ e*M ^ (Fintype.card I) :=
          mul_le_mul_of_nonneg_left hrest (le_of_lt he)
theorem det_two_sum_bound
    {I:Type*} [Fintype I] [DecidableEq I]
    (F R:Matrix I I ℝ) (e M:ℝ)
    (he:0 < e) (hM:1 ≤ M) (heM:e ≤ M)
    (hF : ∀ i j,|F i j| ≤ M)
    (hR : ∀ i j,|R i j| ≤ e) :
    |(F+R).det| ≤
      (2:ℝ) ^ (Fintype.card I) *
        (|F.det| + ((Fintype.card I).factorial:ℝ) *
          e*M ^ (Fintype.card I)) := by
  rw [det_two_sum_rows F R]
  calc
    |∑ σ:I → Bool,
      (Matrix.of fun i j => if σ i then R i j else F i j).det|
      ≤ ∑ σ:I → Bool,
        |(Matrix.of fun i j => if σ i then R i j else F i j).det| :=
          Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ σ:I → Bool,
        (|F.det| + ((Fintype.card I).factorial:ℝ) *
          e*M ^ (Fintype.card I)) := by
      apply Finset.sum_le_sum
      intro σ hσ
      by_cases hz:σ = fun _ => false
      · subst σ
        simp
        have hterm:0 ≤ ((Fintype.card I).factorial:ℝ) *
            e*M ^ (Fintype.card I) := by positivity
        change |F.det| ≤ |F.det| +
          ((Fintype.card I).factorial:ℝ)*e * M ^ (Fintype.card I)
        exact le_add_of_nonneg_right (by positivity)
      · have htrue : ∃ i,σ i = true := by
          by_contra hn
          apply hz
          funext i
          cases hbi:σ i with
          | false => rfl
          | true => exact False.elim (hn ⟨i,hbi⟩)
        let w:I → ℝ := fun i => if σ i then e else M
        have hw : ∀ i,0 < w i := by
          intro i
          dsimp [w]
          split_ifs <;> linarith
        have hrow : ∀ i j,
            |(Matrix.of fun i j => if σ i then R i j else F i j) i j| ≤ w i := by
          intro i j
          dsimp [w]
          split_ifs
          · exact hR i j
          · exact hF i j
        have hd := weighted_det
          (Matrix.of fun i j => if σ i then R i j else F i j)
          w hw hrow
        have hp := prod_bool_row_bound σ e M htrue he hM heM
        calc
          |(Matrix.of fun i j => if σ i then R i j else F i j).det|
            ≤ ((Fintype.card I).factorial:ℝ) * ∏ i,w i := hd
          _ ≤ ((Fintype.card I).factorial:ℝ) *
              (e*M ^ (Fintype.card I)) := by
                gcongr
          _ ≤ |F.det| + ((Fintype.card I).factorial:ℝ) *
              e*M ^ (Fintype.card I) := by
                have hterm:0 ≤ ((Fintype.card I).factorial:ℝ) *
                    e*M ^ (Fintype.card I) := by positivity
                linarith [abs_nonneg F.det]
    _ = (2:ℝ) ^ (Fintype.card I) *
        (|F.det| + ((Fintype.card I).factorial:ℝ) *
          e*M ^ (Fintype.card I)) := by
      simp [nsmul_eq_mul]
      ring
theorem jet_weight_nonneg
    (μ:ℝ) (hμ:0 ≤ μ) (m:ℕ × ℕ) :
    0 ≤ weight μ m := by
  dsimp [weight]
  positivity
theorem rpow_neg_weight_le_one
    (X μ:ℝ) (hX:1 ≤ X)
    (hμ:0 ≤ μ) (m:ℕ × ℕ) :
    X ^ (-weight μ m) ≤ 1 := by
  have hw:0 ≤ weight μ m := jet_weight_nonneg μ hμ m
  calc
    X ^ (-weight μ m) ≤ X ^ (0:ℝ) := by
      gcongr
      linarith
    _ = 1 := by simp
theorem raw_jet_entry_bound
    {I K:Type*} [Fintype K]
    (V:Matrix I K ℝ) (C:Matrix K I ℝ)
    (c:K → ℝ) (C₀:ℝ)
    (hc : ∀ k,0 ≤ c k)
    (hV : ∀ i k,|V i k| ≤ c k)
    (hC : ∀ k j,|C k j| ≤ C₀) :
    ∀ i j,|(V*C) i j| ≤ C₀ * ∑ k:K,c k := by
  intro i j
  rw [Matrix.mul_apply]
  calc
    |∑ k:K,V i k*C k j|
      ≤ ∑ k:K,|V i k*C k j| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k:K,c k*C₀ := by
      apply Finset.sum_le_sum
      intro k hk
      rw [abs_mul]
      exact mul_le_mul (hV i k) (hC k j) (abs_nonneg _) (hc k)
    _ = C₀ * ∑ k:K,c k := by
      rw [← Finset.sum_mul]
      ring
theorem original_minor_bounds
    (μ:ℝ) (q L:ℕ) (δ Cu Cv Ccoeff Crem Cden X:ℝ)
    (hμlo:(57:ℝ)/305 < μ) (hμhi:μ < 1/5)
    (_hq:1 ≤ q) (_hδ:0 < δ)
    (hCu:0 < Cu) (hCv:0 < Cv)
    (hCcoeff:0 < Ccoeff) (hCrem:0 < Crem)
    (hCden:0 < Cden)
    (hL:(Fintype.card (Rect q):ℝ)*(q:ℝ)+δ + 1 <
      μ*((L:ℝ)+1))
    (hX:2 ≤ X)
    (y1 y2 x1 x2:Rect q → ℤ)
    (center:ℝ) (f:ℝ → ℝ)
    (u v:Rect q → ℝ)
    (coeff:(ℕ × ℕ) → Rect q → ℝ)
    (hden : ∀ i,y2 i ≠ 0 ∧ x2 i ≠ 0)
    (_hu0 : ∀ i,u i = (y1 i:ℝ)/(y2 i:ℝ) - center)
    (_hv0 : ∀ i,v i = (x1 i:ℝ)/(x2 i:ℝ) - f (u i))
    (hu : ∀ i,|u i| ≤ Cu*X ^ (-μ))
    (hv : ∀ i,|v i| ≤ Cv*X ^ (-(1:ℝ)))
    (hrow : ∀ i,|(y2 i:ℝ) ^ (3*q) *
                    (x2 i:ℝ) ^ (2*q)| ≤ Cden*X ^ (q:ℝ))
    (hcoeff : ∀ m ∈ jets L,∀ ab,|coeff m ab| ≤ Ccoeff)
    (hTaylor : ∀ i ab,
      |rawEval q y1 y2 x1 x2 i ab -
        ∑ m ∈ jets L,coeff m ab*u i ^ m.1*v i ^ m.2|
        ≤ Crem*X ^ (-(μ*((L:ℝ)+1))))
    (hmargin : ∀ σ:Rect q → ℕ × ℕ,
      (∀ i,σ i ∈ jets L) →
      Matrix.det (fun i ab:Rect q => coeff (σ i) ab) ≠ 0 →
      (Fintype.card (Rect q):ℝ)*(q:ℝ)+δ ≤
        ∑ i:Rect q,weight μ (σ i)) :
    |(rawEval q y1 y2 x1 x2).det| ≤
      determinantCost q L Cu Cv Ccoeff Crem *
        X ^ (-((Fintype.card (Rect q) : ℝ) * (q : ℝ) + δ)) ∧
    |((clearedEval q y1 y2 x1 x2).det : ℝ)| ≤
      Cden ^ (Fintype.card (Rect q)) *
        determinantCost q L Cu Cv Ccoeff Crem * X ^ (-δ) := by
  classical
  let J := Rect q
  let K := {m:ℕ × ℕ // m ∈ jets L}
  let H := Fintype.card J
  let T:ℝ := (H:ℝ)*(q:ℝ)+δ
  let c:K → ℝ := fun m => Cu ^ m.val.1*Cv ^ m.val.2
  let V:Matrix J K ℝ := fun i m => u i ^ m.val.1*v i ^ m.val.2
  let C:Matrix K J ℝ := fun m ab => coeff m.val ab
  let F:Matrix J J ℝ := V*C
  let E:Matrix J J ℝ := rawEval q y1 y2 x1 x2
  let R:Matrix J J ℝ := E - F
  let e:ℝ := Crem*X ^ (-(μ*((L:ℝ)+1)))
  let M:ℝ := Ccoeff*(∑ m:K,c m)+Crem+1
  have hXp:0 < X := by linarith
  have hX1:1 ≤ X := by linarith
  have hμ:0 < μ := by linarith [hμlo]
  have hc : ∀ m:K,0 ≤ c m := by
    intro m
    dsimp [c]
    positivity
  have hV : ∀ i m,|V i m| ≤ c m*X ^ (-weight μ m.val) := by
    intro i m
    simpa only [V,c,weight] using
      jet_value_bound μ X Cu Cv m.val.1 m.val.2 hX1
        (le_of_lt hCu) (le_of_lt hCv) (u i) (v i) (hu i) (hv i)
  have hC : ∀ m ab,|C m ab| ≤ Ccoeff := by
    intro m ab
    exact hcoeff m.val m.property ab
  have hCm : ∀ σ:J → K,
      (Matrix.of fun i ab => C (σ i) ab).det ≠ 0 →
      T ≤ ∑ i:J,weight μ (σ i).val := by
    intro σ hz
    change Matrix.det (fun i ab:J => coeff (σ i).val ab) ≠ 0 at hz
    exact hmargin (fun i => (σ i).val)
      (fun i => (σ i).property) hz
  have hFexpr (i ab:J) :
      F i ab =
        ∑ m ∈ jets L,coeff m ab*u i ^ m.1*v i ^ m.2 := by
    change (∑ m:K,V i m*C m ab) = _
    have hs := Finset.sum_coe_sort (jets L)
      (fun m:ℕ × ℕ => coeff m ab*u i ^ m.1*v i ^ m.2)
    first
    | simpa only [V,C,mul_comm,mul_left_comm,mul_assoc] using hs
  have hR : ∀ i ab,|R i ab| ≤ e := by
    intro i ab
    simpa [R,E,e,hFexpr] using hTaylor i ab
  have hV0 : ∀ i m,|V i m| ≤ c m := by
    intro i m
    calc
      |V i m| ≤ c m*X ^ (-weight μ m.val) := hV i m
      _ ≤ c m*1 := by
        apply mul_le_mul_of_nonneg_left _ (hc m)
        exact rpow_neg_weight_le_one X μ hX1 (le_of_lt hμ) m.val
      _ = c m := by ring
  have hF0 : ∀ i ab,|F i ab| ≤ Ccoeff * ∑ m:K,c m :=
    raw_jet_entry_bound V C c Ccoeff hc hV0 hC
  have hM:1 ≤ M := by
    dsimp [M]
    have hs:0 ≤ ∑ m:K,c m :=
      Finset.sum_nonneg (fun m hm => hc m)
    nlinarith [hCcoeff]
  have hF : ∀ i ab,|F i ab| ≤ M := by
    intro i ab
    have hh := hF0 i ab
    dsimp [M]
    linarith [hCrem]
  have he:0 < e := by
    dsimp [e]
    positivity
  have hErrPow:X ^ (-(μ*((L:ℝ)+1))) ≤ 1 := by
    calc
      _ ≤ X ^ (0:ℝ) := Real.rpow_le_rpow_of_exponent_le hX1
        (neg_nonpos.mpr (mul_nonneg hμ.le (by positivity)))
      _ = 1 := by simp
  have heM:e ≤ M := by
    have hh:e ≤ Crem := by
      dsimp [e]
      nlinarith [hErrPow,hCrem]
    dsimp [M]
    have hs:0 ≤ ∑ m:K,c m :=
      Finset.sum_nonneg (fun m hm => hc m)
    nlinarith [hCcoeff]
  have hFdet := finite_weighted_det V C
    (fun m:K => weight μ m.val) c T Ccoeff X
    hX1 hCcoeff hc hV hC hCm
  have hEeq:E = F+R := by
    ext i ab
    dsimp [R]
    simp []
  have hEbound := det_two_sum_bound F R e M he hM heM hF hR
  have hErrDecay :
      X ^ (-(μ*((L:ℝ)+1))) ≤ X ^ (-T) := by
    gcongr
    dsimp [T,H] at *
    linarith [hL]
  let Ksum:ℝ := ∑ σ:J → K,∏ i:J,c (σ i)
  let Cjet:ℝ := (Fintype.card K:ℝ) ^ H *
      (H.factorial:ℝ)*Ccoeff ^ H*Ksum
  let Ctot:ℝ := (2:ℝ) ^ H *
      (Cjet+(H.factorial:ℝ)*Crem*M ^ H)
  have hKsum:0 ≤ Ksum := by
    dsimp [Ksum]
    apply Finset.sum_nonneg
    intro σ hσ
    exact Finset.prod_nonneg (fun i hi => hc (σ i))
  have hCjet:0 ≤ Cjet := by
    change 0 ≤ (Fintype.card K:ℝ) ^ H *
      (H.factorial:ℝ)*Ccoeff ^ H*Ksum
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _)
        (Nat.cast_nonneg _)) (pow_nonneg hCcoeff.le _)) hKsum
  have hCtot:0 ≤ Ctot := by
    change 0 ≤ (2:ℝ) ^ H *
      (Cjet+(H.factorial:ℝ)*Crem*M ^ H)
    exact mul_nonneg (pow_nonneg (by norm_num) _)
      (add_nonneg hCjet (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hCrem.le)
        (pow_nonneg (le_trans (by norm_num:(0:ℝ) ≤ 1) hM) _)))
  have hFdecay : |F.det| ≤ Cjet*X ^ (-T) := by
    simpa [F,Cjet,Ksum,H,T,J,K,c] using hFdet
  have hEdecay : |E.det| ≤ Ctot*X ^ (-T) := by
    rw [← hEeq] at hEbound
    calc
      |E.det| ≤ (2:ℝ) ^ H *
          (|F.det| + (H.factorial:ℝ)*e * M ^ H) := by
        simpa [H] using hEbound
      _ ≤ (2:ℝ) ^ H *
          (Cjet*X ^ (-T) +
            (H.factorial:ℝ)*Crem*M ^ H*X ^ (-T)) := by
        have hcoef:0 ≤ (H.factorial:ℝ)*Crem*M ^ H :=
          mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hCrem.le)
            (pow_nonneg (le_trans (by norm_num:(0:ℝ) ≤ 1) hM) _)
        have hterm :
            (H.factorial:ℝ)*e * M ^ H ≤
              (H.factorial:ℝ)*Crem*M ^ H*X ^ (-T) := by
          dsimp [e]
          calc
            (H.factorial:ℝ)*(Crem*X ^ (-(μ*((L:ℝ)+1))))*M ^ H =
                ((H.factorial:ℝ)*Crem*M ^ H) *
                  X ^ (-(μ*((L:ℝ)+1))) := by ring
            _ ≤ ((H.factorial:ℝ)*Crem*M ^ H)*X ^ (-T) :=
              mul_le_mul_of_nonneg_left hErrDecay hcoef
        exact mul_le_mul_of_nonneg_left
          (add_le_add hFdecay hterm) (by positivity)
      _ = Ctot*X ^ (-T) := by dsimp [Ctot]; ring
  let d:J → ℝ := fun i =>
    (y2 i:ℝ) ^ (3*q)*(x2 i:ℝ) ^ (2*q)
  have hZmat :
      (fun i ab:J => ((clearedEval q y1 y2 x1 x2 i ab:ℤ):ℝ)) =
        (fun i ab:J => d i*E i ab) := by
    funext i ab
    exact signed_original_row_identity q y1 y2 x1 x2 i ab
      (hden i).1 (hden i).2
  have hZdet :
      ((clearedEval q y1 y2 x1 x2).det:ℝ) =
        (∏ i:J,d i)*E.det := by
    have hcast :
        ((clearedEval q y1 y2 x1 x2).det:ℝ) =
        (Matrix.of fun i ab:J =>
          ((clearedEval q y1 y2 x1 x2 i ab:ℤ):ℝ)).det := by
      change (Int.castRingHom ℝ) ((clearedEval q y1 y2 x1 x2).det) =
        ((clearedEval q y1 y2 x1 x2).map (Int.castRingHom ℝ)).det
      exact RingHom.map_det _ _
    rw [hcast,hZmat]
    exact Matrix.det_mul_column d E
  have hdprod :
      |∏ i:J,d i| ≤ Cden ^ H*X ^ ((H:ℝ)*(q:ℝ)) := by
    rw [Finset.abs_prod]
    calc
      (∏ i:J,|d i|) ≤ ∏ i:J,Cden*X ^ (q:ℝ) :=
        Finset.prod_le_prod (fun i hi => abs_nonneg _) (fun i hi => hrow i)
      _ = (Cden*X ^ (q:ℝ)) ^ H := by simp [H]
      _ = Cden ^ H*X ^ ((H:ℝ)*(q:ℝ)) := by
        have hpow:(X ^ (q:ℝ)) ^ H =
            X ^ ((q:ℝ)*(H:ℝ)) := by
          rw [← Real.rpow_natCast,← Real.rpow_mul (le_of_lt hXp)]
        rw [mul_pow,hpow]
        congr 1
        ring
  have hfinal :
      |((clearedEval q y1 y2 x1 x2).det:ℝ)| ≤
        Cden ^ H*Ctot*X ^ (-δ) := by
    rw [hZdet,abs_mul]
    calc
      |∏ i:J,d i| * |E.det| ≤
          (Cden ^ H*X ^ ((H:ℝ)*(q:ℝ))) *
            (Ctot*X ^ (-T)) := by
        gcongr
      _ = Cden ^ H*Ctot*X ^ (-δ) := by
        calc
          (Cden ^ H*X ^ ((H:ℝ)*(q:ℝ))) *
              (Ctot*X ^ (-T)) =
              Cden ^ H*Ctot *
                (X ^ ((H:ℝ)*(q:ℝ))*X ^ (-T)) := by ring
          _ = Cden ^ H*Ctot*X ^ (-δ) := by
              rw [← Real.rpow_add hXp]
              congr 1
              dsimp [T]
              ring
  constructor
  · simpa [determinantCost,H,J,K,M,c,Cjet,Ctot,Ksum,T,mul_assoc] using hEdecay
  · simpa [determinantCost,H,J,K,M,c,Cjet,Ctot,Ksum,mul_assoc] using hfinal

def PolyGrowth (F : ℝ → ℝ) : Prop :=
  ∃ d : ℕ, ∃ C : ℝ, 0 < C ∧
    ∀ H : ℝ, 1 ≤ H → 0 ≤ F H ∧ F H ≤ C * H ^ d

theorem growth_const (c : ℝ) (hc : 0 ≤ c) :
    PolyGrowth (fun _ => c) := by
  refine ⟨0, c + 1, by linarith, ?_⟩
  intro H hH
  simpa only [pow_zero, mul_one] using
    (show 0 ≤ c ∧ c ≤ c + 1 from ⟨hc, by linarith⟩)

theorem growth_power (n : ℕ) :
    PolyGrowth (fun H => H ^ n) := by
  refine ⟨n, 1, by norm_num, ?_⟩
  intro H hH
  exact ⟨pow_nonneg (by linarith) _, by simp⟩

theorem growth_add {F G : ℝ → ℝ}
    (hF : PolyGrowth F) (hG : PolyGrowth G) :
    PolyGrowth (fun H => F H + G H) := by
  obtain ⟨d, C, hC, hF⟩ := hF
  obtain ⟨e, D, hD, hG⟩ := hG
  refine ⟨d + e, C + D, by linarith, ?_⟩
  intro H hH
  obtain ⟨hF0, hFu⟩ := hF H hH
  obtain ⟨hG0, hGu⟩ := hG H hH
  refine ⟨add_nonneg hF0 hG0, ?_⟩
  calc
    F H + G H ≤ C * H ^ d + D * H ^ e := add_le_add hFu hGu
    _ ≤ C * H ^ (d + e) + D * H ^ (d + e) :=
      add_le_add
        (mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ hH (by omega : d ≤ d + e)) hC.le)
        (mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ hH (by omega : e ≤ d + e)) hD.le)
    _ = (C + D) * H ^ (d + e) := by ring

theorem growth_mul {F G : ℝ → ℝ}
    (hF : PolyGrowth F) (hG : PolyGrowth G) :
    PolyGrowth (fun H => F H * G H) := by
  obtain ⟨d, C, hC, hF⟩ := hF
  obtain ⟨e, D, hD, hG⟩ := hG
  refine ⟨d + e, C * D, mul_pos hC hD, ?_⟩
  intro H hH
  obtain ⟨hF0, hFu⟩ := hF H hH
  obtain ⟨hG0, hGu⟩ := hG H hH
  refine ⟨mul_nonneg hF0 hG0, ?_⟩
  calc
    F H * G H ≤ (C * H ^ d) * (D * H ^ e) :=
      mul_le_mul hFu hGu hG0 (by positivity)
    _ = (C * D) * H ^ (d + e) := by rw [pow_add]; ring

theorem growth_pow {F : ℝ → ℝ}
    (hF : PolyGrowth F) (n : ℕ) :
    PolyGrowth (fun H => F H ^ n) := by
  obtain ⟨d, C, hC, hF⟩ := hF
  refine ⟨d * n, C ^ n, pow_pos hC n, ?_⟩
  intro H hH
  obtain ⟨hF0, hFu⟩ := hF H hH
  refine ⟨pow_nonneg hF0 _, ?_⟩
  calc
    F H ^ n ≤ (C * H ^ d) ^ n := by gcongr
    _ = C ^ n * H ^ (d * n) := by rw [mul_pow, ← pow_mul]

theorem growth_sum {ι : Type*} (s : Finset ι)
    (F : ι → ℝ → ℝ) (hF : ∀ i ∈ s, PolyGrowth (F i)) :
    PolyGrowth (fun H => ∑ i ∈ s, F i H) := by
  classical
  revert hF
  induction s using Finset.induction_on with
  | empty =>
      intro _
      simpa using growth_const 0 (by norm_num)
  | @insert i s hi ih =>
      intro hF
      have hg := growth_add (hF i (Finset.mem_insert_self _ _))
        (ih (fun j hj => hF j (Finset.mem_insert_of_mem hj)))
      simpa only [Finset.sum_insert hi] using hg

theorem growth_prod {ι : Type*} (s : Finset ι)
    (F : ι → ℝ → ℝ) (hF : ∀ i ∈ s, PolyGrowth (F i)) :
    PolyGrowth (fun H => ∏ i ∈ s, F i H) := by
  classical
  revert hF
  induction s using Finset.induction_on with
  | empty =>
      intro _
      simpa using growth_const 1 (by norm_num)
  | @insert i s hi ih =>
      intro hF
      have hg := growth_mul (hF i (Finset.mem_insert_self _ _))
        (ih (fun j hj => hF j (Finset.mem_insert_of_mem hj)))
      simpa only [Finset.prod_insert hi] using hg

def remainderEnvelope (q L : ℕ) (K0 H : ℝ) : ℝ :=
  K0 * H ^ (3 * q + 2 * q + 1) *
    (H ^ (L + 1) + (((3 * q + 2 * q * L + 1) * (2 * q + 1) : ℕ) : ℝ) *
      H ^ (3 * q + 2 * q * L) * H ^ (2 * q))

theorem growth_remainder (q L : ℕ) (K0 : ℝ) (hK0 : 0 < K0) :
    PolyGrowth (fun H => remainderEnvelope q L K0 H) := by
  exact growth_mul (growth_mul (growth_const K0 hK0.le)
    (growth_power (3 * q + 2 * q + 1)))
    (growth_add (growth_power (L + 1))
      (growth_mul
        (growth_mul (growth_const _ (Nat.cast_nonneg _))
          (growth_power (3 * q + 2 * q * L)))
        (growth_power (2 * q))))

theorem growth_determinant_cost (q L : ℕ) (K0 : ℝ) (hK0 : 0 < K0) :
    PolyGrowth (fun H => determinantCost q L H H
      (K0 * H ^ (3 * q + 2 * q + 1)) (remainderEnvelope q L K0 H)) := by
  classical
  let Jet := {m : ℕ × ℕ // m ∈ jets L}
  let h := Fintype.card (Rect q)
  have hcoeff : PolyGrowth (fun H => K0 * H ^ (3 * q + 2 * q + 1)) :=
    growth_mul (growth_const K0 hK0.le) (growth_power _)
  have hrem := growth_remainder q L K0 hK0
  have hm (m : Jet) :
      PolyGrowth (fun H => H ^ m.val.1 * H ^ m.val.2) :=
    growth_mul (growth_power _) (growth_power _)
  have hsum : PolyGrowth (fun H =>
      ∑ m : Jet, H ^ m.val.1 * H ^ m.val.2) := by
    simpa using growth_sum Finset.univ
      (fun m : Jet => fun H : ℝ => H ^ m.val.1 * H ^ m.val.2)
      (fun m _ => hm m)
  have hprodsum : PolyGrowth (fun H =>
      ∑ σ : Rect q → Jet, ∏ i : Rect q,
        H ^ (σ i).val.1 * H ^ (σ i).val.2) := by
    apply growth_sum Finset.univ
    intro σ _
    apply growth_prod Finset.univ
    intro i _
    exact hm (σ i)
  have hM := growth_add (growth_add (growth_mul hcoeff hsum) hrem)
    (growth_const 1 (by norm_num))
  have hjet := growth_mul
    (growth_mul
      (growth_mul
        (growth_const ((Fintype.card Jet : ℝ) ^ h) (by positivity))
        (growth_const (h.factorial : ℝ) (Nat.cast_nonneg _)))
      (growth_pow hcoeff h))
    hprodsum
  have herr := growth_mul
    (growth_mul (growth_const (h.factorial : ℝ) (Nat.cast_nonneg _)) hrem)
    (growth_pow hM h)
  have hall := growth_mul (growth_const ((2 : ℝ) ^ h) (by positivity))
    (growth_add hjet herr)
  simpa only [determinantCost, h, Jet] using hall

theorem polynomial_chart_minor_bounds
    (μ : ℝ) (q L : ℕ) (δ : ℝ)
    (hμlo : (57 : ℝ) / 305 < μ) (hμhi : μ < 1 / 5)
    (hq : 1 ≤ q) (hδ : 0 < δ)
    (hqlarge : 2 * (FormalAB.S61c6e1a7.A1FiniteQuantitative.lossA μ +
      FormalAB.S61c6e1a7.A1FiniteQuantitative.lossB μ) /
      FormalAB.S61c6e1a7.A1FiniteQuantitative.rho μ < (q : ℝ))
    (hδmargin : δ <
      FormalAB.S61c6e1a7.A1FiniteQuantitative.rho μ * (q : ℝ) ^ 3 / 2)
    (hL : (Fintype.card (Rect q) : ℝ) * (q : ℝ) + δ + 1 <
      μ * ((L : ℝ) + 1)) :
    ∃ K0 : ℝ, 0 < K0 ∧
      ∀ (H X r center : ℝ) (f : ℝ → ℝ)
        (y1 y2 x1 x2 : Rect q → ℤ) (u v : Rect q → ℝ),
        1 ≤ H → 2 ≤ X → 0 < r → |center| ≤ H →
        ContDiffOn ℝ (L + 1) f (Set.Ioo (-r) r) →
        (∀ n : ℕ, n ≤ L + 1 → ∀ t ∈ Set.Ioo (-r) r,
          |iteratedDeriv n f t| ≤ H) →
        (∀ i, y2 i ≠ 0 ∧ x2 i ≠ 0) →
        (∀ i, u i = (y1 i : ℝ) / (y2 i : ℝ) - center) →
        (∀ i, v i = (x1 i : ℝ) / (x2 i : ℝ) - f (u i)) →
        (∀ i, |u i| ≤ H * X ^ (-μ)) →
        (∀ i, |v i| ≤ H * X ^ (-(1 : ℝ))) →
        (∀ i, |u i| ≤ min (r / 2) 1) →
        (∀ i, |v i| ≤ 1) →
        (∀ i, |(y2 i : ℝ) ^ (3 * q) * (x2 i : ℝ) ^ (2 * q)| ≤
          H * X ^ (q : ℝ)) →
        |(rawEval q y1 y2 x1 x2).det| ≤
          determinantCost q L H H
            (K0 * H ^ (3 * q + 2 * q + 1)) (remainderEnvelope q L K0 H) *
            X ^ (-((Fintype.card (Rect q) : ℝ) * (q : ℝ) + δ)) ∧
        |((clearedEval q y1 y2 x1 x2).det : ℝ)| ≤
          H ^ (Fintype.card (Rect q)) *
            determinantCost q L H H
              (K0 * H ^ (3 * q + 2 * q + 1)) (remainderEnvelope q L K0 H) *
            X ^ (-δ) := by
  obtain ⟨K0, hK0, hGraph⟩ :=
    A3PolynomialTaylor.polynomialHeightTaylorGraph L (3 * q) (2 * q)
  refine ⟨K0, hK0, ?_⟩
  intro H X r center f y1 y2 x1 x2 u v hH hX hr hcenter hf hder hden
    hu0 hv0 hu hv husmall hvsmall hrow
  have hHp : 0 < H := lt_of_lt_of_le zero_lt_one hH
  let F := FormalAB.S61c6e1a7.A1UniformTaylor.taylorPolynomial L f
  let coeff : (ℕ × ℕ) → Rect q → ℝ :=
    fun m ab => MvPolynomial.coeff
      (FormalAB.S61c6e1a7.A1UniformTaylor.pairExponent m.1 m.2)
      (FormalAB.S61c6e1a7.A1UniformTaylor.normalizedGraph F center 1
        ab.1.val ab.2.val)
  have hdata (ab : Rect q) :=
    hGraph r H hr hH f hf hder center 1 hcenter
      (by simpa using hH) ab.1.val ab.2.val
      (Nat.lt_succ_iff.mp ab.1.isLt) (Nat.lt_succ_iff.mp ab.2.isLt)
  have hcoeffAll (ab : Rect q) (d : Fin 2 →₀ ℕ) :
      |MvPolynomial.coeff d
        (FormalAB.S61c6e1a7.A1UniformTaylor.normalizedGraph F center 1
          ab.1.val ab.2.val)| ≤ K0 * H ^ (3 * q + 2 * q + 1) :=
    (hdata ab).1 d
  have hsupport (ab : Rect q) (d : Fin 2 →₀ ℕ)
      (hd : d ∈
        (FormalAB.S61c6e1a7.A1UniformTaylor.normalizedGraph F center 1
          ab.1.val ab.2.val).support) :
      d 0 ≤ ab.1.val + ab.2.val * L ∧ d 1 ≤ ab.2.val :=
    (hdata ab).2.1 d hd
  have hgraphErr (i : Rect q) (ab : Rect q) :
      |(center + u i) ^ ab.1.val * (f (u i) + v i) ^ ab.2.val -
        MvPolynomial.eval (fun s : Fin 2 => if s = 0 then u i else v i)
          (FormalAB.S61c6e1a7.A1UniformTaylor.normalizedGraph F center 1
            ab.1.val ab.2.val)| ≤
      (K0 * H ^ (3 * q + 2 * q + 1)) * |u i| ^ (L + 1) := by
    simpa only [one_mul] using
      (hdata ab).2.2 (u i) (v i) (husmall i) (hvsmall i)
  have hraw (i ab : Rect q) :
      rawEval q y1 y2 x1 x2 i ab =
        (center + u i) ^ ab.1.val * (f (u i) + v i) ^ ab.2.val := by
    have hy : (y1 i : ℝ) / (y2 i : ℝ) = center + u i := by
      linarith only [hu0 i]
    have hx : (x1 i : ℝ) / (x2 i : ℝ) = f (u i) + v i := by
      linarith only [hv0 i]
    simp only [rawEval, hy, hx]
  have hTaylor (i ab : Rect q) :
      |rawEval q y1 y2 x1 x2 i ab -
        ∑ m ∈ jets L, coeff m ab * u i ^ m.1 * v i ^ m.2| ≤
        remainderEnvelope q L K0 H * X ^ (-(μ * ((L : ℝ) + 1))) := by
    have ht := normalizedGraph_total_degree_tail q L μ H H
      (K0 * H ^ (3 * q + 2 * q + 1)) X center (u i) (v i) f F
      (by linarith) (by linarith) hHp.le hHp.le (by positivity)
      hX (hu i) (hv i) hcoeffAll hsupport (hgraphErr i) ab
    simpa only [hraw i ab, coeff, remainderEnvelope, max_eq_right hH] using ht
  have hmargin (σ : Rect q → ℕ × ℕ)
      (_hσ : ∀ i, σ i ∈ jets L)
      (hdet : Matrix.det (fun i ab : Rect q => coeff (σ i) ab) ≠ 0) :
      (Fintype.card (Rect q) : ℝ) * (q : ℝ) + δ ≤
        ∑ i : Rect q, weight μ (σ i) := by
    let σ' : Rect q → Fin 2 →₀ ℕ :=
      fun i => FormalAB.S61c6e1a7.A1UniformTaylor.pairExponent (σ i).1 (σ i).2
    have hm := affine_graph_minor_margin μ center q F hμlo hμhi hq
      hqlarge σ' (by simpa only [coeff, σ'] using hdet)
    have hw : (∑ i : Rect q,
        FormalAB.S61c6e1a7.A1WeightedJet.weight μ (σ' i)) =
        ∑ i : Rect q, weight μ (σ i) := by
      apply Finset.sum_congr rfl
      intro i _
      simp [σ', FormalAB.S61c6e1a7.A1UniformTaylor.pairExponent,
        FormalAB.S61c6e1a7.A1WeightedJet.weight, weight]
    rw [hw] at hm
    push_cast at hm
    linarith only [hm, hδmargin]
  apply original_minor_bounds μ q L δ H H
    (K0 * H ^ (3 * q + 2 * q + 1)) (remainderEnvelope q L K0 H) H X
    hμlo hμhi hq hδ hHp hHp (by positivity)
    (by dsimp [remainderEnvelope]; positivity) hHp hL hX
    y1 y2 x1 x2 center f u v coeff hden hu0 hv0 hu hv hrow
  · intro m _ ab
    exact hcoeffAll ab _
  · exact hTaylor
  · exact hmargin

theorem sampling_bounds (μ H T r : ℝ)
    (hμ : (1 : ℝ) / 10 ≤ μ) (hH : 1 ≤ H) (hT : 2 ≤ T)
    (hTr : H ≤ T) (hTs : (2 * H ^ 2) ^ 10 ≤ T)
    (hr : H⁻¹ ≤ r) :
    H * T ^ (-μ) ≤ min (r / 2) 1 ∧
      H * T ^ (-(1 : ℝ)) ≤ 1 := by
  have hHp : 0 < H := by linarith
  have hTp : 0 < T := by linarith
  have hT1 : 1 ≤ T := by linarith
  have hb : 1 ≤ 2 * H ^ 2 := by nlinarith [sq_nonneg (H - 1)]
  have hb0 : 0 ≤ 2 * H ^ 2 := by positivity
  have hbase : 2 * H ^ 2 ≤ T ^ μ := by
    calc
      2 * H ^ 2 = (2 * H ^ 2) ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ ≤ (2 * H ^ 2) ^ ((10 : ℝ) * μ) :=
        Real.rpow_le_rpow_of_exponent_le hb (by linarith)
      _ = ((2 * H ^ 2) ^ (10 : ℕ)) ^ μ := by
        rw [Real.rpow_mul hb0]
        exact congrArg (fun z : ℝ => z ^ μ) (Real.rpow_natCast (2 * H ^ 2) 10)
      _ ≤ T ^ μ := Real.rpow_le_rpow (by positivity) hTs (by linarith)
  have hpowp : 0 < T ^ μ := Real.rpow_pos_of_pos hTp μ
  have hratio : H / T ^ μ ≤ 1 / (2 * H) := by
    apply (div_le_div_iff₀ hpowp (by positivity : 0 < 2 * H)).mpr
    nlinarith only [hbase]
  have hneg : H * T ^ (-μ) = H / T ^ μ := by
    rw [Real.rpow_neg hTp.le]
    rfl
  have hradius : 1 / (2 * H) ≤ r / 2 := by
    have heq : 1 / (2 * H) = H⁻¹ / 2 := by
      field_simp [ne_of_gt hHp]

    rw [heq]
    linarith only [hr]
  have hone : 1 / (2 * H) ≤ 1 :=
    (div_le_one (by positivity : 0 < 2 * H)).mpr (by linarith)
  constructor
  · rw [hneg]
    exact le_min (hratio.trans hradius) (hratio.trans hone)
  · simpa only [Real.rpow_neg_one, div_eq_mul_inv] using
      (div_le_one hTp).mpr hTr

end
end A3PolynomialDeterminantCore

namespace A3PolynomialOriginalDeterminant
open A3PolynomialDeterminantCore
open scoped BigOperators
noncomputable section

theorem polynomialOriginalDeterminant :
    PolynomialOriginalDeterminantStatement := by
  have hcard :
      Fintype.card (FormalAB.S61c6e1a7.A1OriginalDeterminant.Rect q) = J := by
    simp only [FormalAB.S61c6e1a7.A1OriginalDeterminant.Rect,
      Fintype.card_prod, Fintype.card_fin, J]
  have hμlo : (57 : ℝ) / 305 < mu := by norm_num [mu]
  have hμhi : mu < 1 / 5 := by norm_num [mu]
  have hμp : 0 < mu := by norm_num [mu]
  have hq : 1 ≤ q := by norm_num [q]
  have hgap : 0 < gap := by norm_num [gap, q]
  have hgap1 : 1 ≤ gap := by norm_num [gap, q]
  have hqlarge :
      2 * (FormalAB.S61c6e1a7.A1FiniteQuantitative.lossA mu +
        FormalAB.S61c6e1a7.A1FiniteQuantitative.lossB mu) /
        FormalAB.S61c6e1a7.A1FiniteQuantitative.rho mu < (q : ℝ) := by
    norm_num [FormalAB.S61c6e1a7.A1FiniteQuantitative.lossA,
      FormalAB.S61c6e1a7.A1FiniteQuantitative.lossB,
      FormalAB.S61c6e1a7.A1FiniteQuantitative.b,
      FormalAB.S61c6e1a7.A1FiniteQuantitative.rho, mu, q]
  have hmargin :
      gap < FormalAB.S61c6e1a7.A1FiniteQuantitative.rho mu * (q : ℝ) ^ 3 / 2 := by
    norm_num [FormalAB.S61c6e1a7.A1FiniteQuantitative.rho, mu, gap, q]
  obtain ⟨ell, hell⟩ := exists_nat_gt
    (((J : ℝ) * (q : ℝ) + gap + 1) / mu)
  have horder :
      (J : ℝ) * (q : ℝ) + gap + 1 < mu * ((ell : ℝ) + 1) := by
    have hh := (div_lt_iff₀ hμp).mp hell
    nlinarith only [hh, hμp]
  have horder' :
      (Fintype.card (FormalAB.S61c6e1a7.A1OriginalDeterminant.Rect q) : ℝ) *
        (q : ℝ) + gap + 1 < mu * ((ell : ℝ) + 1) := by
    simpa only [hcard] using horder
  obtain ⟨K0, hK0, hBounds⟩ :=
    polynomial_chart_minor_bounds mu q ell gap hμlo hμhi hq hgap
      hqlarge hmargin horder'
  obtain ⟨d, C0, hC0, hCost⟩ := growth_determinant_cost q ell K0 hK0
  refine ⟨ell, horder, ?_⟩
  intro B E hB
  let n : ℕ := J
  let k : ℕ := 20 + d + n + 1
  let D0 : ℝ := 1024 + 2 * C0 + 2
  let C : ℝ := D0 * B ^ k + C0 * B ^ d + 2
  have hB0 : 0 ≤ B := by linarith
  have hD0 : 0 < D0 := by dsimp [D0]; linarith
  have hD1024 : (1024 : ℝ) ≤ D0 := by dsimp [D0]; linarith
  have hDC : C0 < D0 := by dsimp [D0]; linarith
  have hC2 : 2 ≤ C := by
    dsimp [C]
    have ha := mul_nonneg hD0.le (pow_nonneg hB0 k)
    have hb := mul_nonneg hC0.le (pow_nonneg hB0 d)
    linarith
  have hC0D : D0 * B ^ k ≤ C := by
    dsimp [C]
    have hb := mul_nonneg hC0.le (pow_nonneg hB0 d)
    linarith
  have hC0c : C0 * B ^ d ≤ C := by
    dsimp [C]
    have ha := mul_nonneg hD0.le (pow_nonneg hB0 k)
    linarith
  have hkd : d ≤ k := by dsimp [k]; omega
  have hk20 : 20 ≤ k := by dsimp [k]; omega
  have hkn : d + n ≤ k := by dsimp [k]; omega
  have hk1 : 1 ≤ k := by omega
  have hEd : E * d ≤ E * k + 1 :=
    (Nat.mul_le_mul_left E hkd).trans (by omega)
  refine ⟨C, E * k + 1, hC2, by omega, ?_⟩
  intro A T r center f y1 y2 x1 x2 u v hA hT hr hcenter hf hder hden
    hu0 hv0 hu hv hrow
  let H : ℝ := B * A ^ E
  have hA0 : 0 ≤ A := by linarith
  have hAp : 0 < A := by linarith
  have hAE : 1 ≤ A ^ E := by
    calc
      1 = A ^ 0 := by simp
      _ ≤ A ^ E := pow_le_pow_right₀ hA (Nat.zero_le E)
  have hH : 1 ≤ H := by
    dsimp [H]
    simpa only [one_mul] using
      mul_le_mul hB hAE (by norm_num : (0 : ℝ) ≤ 1) hB0
  have hHp : 0 < H := by linarith
  have hBig : D0 * H ^ k ≤ T := by
    calc
      D0 * H ^ k = (D0 * B ^ k) * A ^ (E * k) := by
        dsimp [H]
        rw [mul_pow, ← pow_mul]
        ring
      _ ≤ C * A ^ (E * k + 1) :=
        mul_le_mul hC0D
          (pow_le_pow_right₀ hA (by omega))
          (pow_nonneg hA0 _) (by linarith)
      _ ≤ T := hT
  have hHk1 : 1 ≤ H ^ k := by
    calc
      1 = H ^ 0 := by simp
      _ ≤ H ^ k := pow_le_pow_right₀ hH (Nat.zero_le k)
  have hT2 : 2 ≤ T := by
    have hh : D0 ≤ D0 * H ^ k := by nlinarith only [hHk1, hD0]
    exact (show 2 ≤ D0 by linarith).trans (hh.trans hBig)
  have hTp : 0 < T := by linarith
  have hHT : H ≤ T := by
    have hh : H ≤ H ^ k := by
      simpa only [pow_one] using pow_le_pow_right₀ hH hk1
    have hb : H ^ k ≤ D0 * H ^ k := by
      nlinarith only [hD1024, hHk1]
    exact hh.trans (hb.trans hBig)
  have hTs : (2 * H ^ 2) ^ 10 ≤ T := by
    calc
      (2 * H ^ 2) ^ 10 = (1024 : ℝ) * H ^ 20 := by
        rw [mul_pow, ← pow_mul]
        norm_num
      _ ≤ D0 * H ^ k :=
        mul_le_mul hD1024 (pow_le_pow_right₀ hH hk20)
          (pow_nonneg hHp.le _) hD0.le
      _ ≤ T := hBig
  have hrH : H⁻¹ ≤ r := hr
  have hrp : 0 < r := (inv_pos.mpr hHp).trans_le hrH
  obtain ⟨hus, hvs⟩ :=
    sampling_bounds mu H T r (by norm_num [mu]) hH hT2 hHT hTs hrH
  have hChart := hBounds H T r center f y1 y2 x1 x2 u v hH hT2 hrp
    hcenter hf hder hden hu0 hv0 hu hv
    (fun i => (hu i).trans hus) (fun i => (hv i).trans hvs) hrow
  rw [hcard] at hChart
  obtain ⟨hcost0, hcostup⟩ := hCost H hH
  have hCoeff : C0 * H ^ d ≤ C * A ^ (E * k + 1) := by
    calc
      C0 * H ^ d = (C0 * B ^ d) * A ^ (E * d) := by
        dsimp [H]
        rw [mul_pow, ← pow_mul]
        ring
      _ ≤ C * A ^ (E * k + 1) :=
        mul_le_mul hC0c (pow_le_pow_right₀ hA hEd)
          (pow_nonneg hA0 _) (by linarith)
  have hRaw :
      |(FormalAB.S61c6e1a7.A1OriginalDeterminant.rawEval
        q y1 y2 x1 x2).det| ≤
        C * A ^ (E * k + 1) *
          T ^ (-((Fintype.card
            (FormalAB.S61c6e1a7.A1OriginalDeterminant.Rect q) : ℝ) *
              (q : ℝ) + gap)) := by
    simpa only [hcard] using
      (hChart.1.trans
        (mul_le_mul_of_nonneg_right (hcostup.trans hCoeff) (Real.rpow_nonneg hTp.le _)))
  have hClear :
      |((FormalAB.S61c6e1a7.A1OriginalDeterminant.clearedEval
        q y1 y2 x1 x2).det : ℝ)| ≤
        C0 * H ^ (d + n) * T ^ (-gap) := by
    calc
      _ ≤ H ^ n * determinantCost q ell H H
          (K0 * H ^ (3 * q + 2 * q + 1))
          (remainderEnvelope q ell K0 H) * T ^ (-gap) := hChart.2
      _ ≤ H ^ n * (C0 * H ^ d) * T ^ (-gap) := by
        gcongr
      _ = C0 * H ^ (d + n) * T ^ (-gap) := by rw [pow_add]; ring
  have hNumerator : C0 * H ^ (d + n) < T := by
    calc
      C0 * H ^ (d + n) < D0 * H ^ (d + n) :=
        mul_lt_mul_of_pos_right hDC (pow_pos hHp _)
      _ ≤ D0 * H ^ k :=
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hH hkn) hD0.le
      _ ≤ T := hBig
  have hDecay : T ^ (-gap) ≤ T ^ (-(1 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ T) (by linarith only [hgap1])
  have hSmall :
      |((FormalAB.S61c6e1a7.A1OriginalDeterminant.clearedEval
        q y1 y2 x1 x2).det : ℝ)| < 1 := by
    calc
      _ ≤ C0 * H ^ (d + n) * T ^ (-gap) := hClear
      _ ≤ C0 * H ^ (d + n) * T ^ (-(1 : ℝ)) :=
        mul_le_mul_of_nonneg_left hDecay (by positivity)
      _ = (C0 * H ^ (d + n)) / T := by
        rw [Real.rpow_neg_one]
        rfl
      _ < 1 := (div_lt_one hTp).mpr hNumerator
  constructor
  · have he :
        -((J : ℝ) * (q : ℝ) + gap) = -((J : ℝ) * (q : ℝ)) - gap := by ring
    simpa only [hcard, he] using hRaw
  · have hInt :
        |(FormalAB.S61c6e1a7.A1OriginalDeterminant.clearedEval
          q y1 y2 x1 x2).det| < (1 : ℤ) := by
      exact_mod_cast hSmall
    have hnonneg := abs_nonneg
      (FormalAB.S61c6e1a7.A1OriginalDeterminant.clearedEval q y1 y2 x1 x2).det
    have hz :
        |(FormalAB.S61c6e1a7.A1OriginalDeterminant.clearedEval
          q y1 y2 x1 x2).det| = 0 := by omega
    exact abs_eq_zero.mp hz

end
end A3PolynomialOriginalDeterminant
#print axioms A3PolynomialOriginalDeterminant.polynomialOriginalDeterminant

namespace JocelynClaims
theorem claim_a784ea0d4882079f077167e52b8b095db4d6b6a3bb097a313cf37b8ae344b161 :
let q : ℕ := 4096;
let Rect := FormalAB.S61c6e1a7.A1OriginalDeterminant.Rect q;
let mu : ℝ := 19 / 100;
let J : ℕ := (3 * q + 1) * (2 * q + 1);
let gap : ℝ := 19 * (q : ℝ) ^ 3 / 1440;
∃ ell : ℕ,
    (J : ℝ) * (q : ℝ) + gap + 1 < mu * ((ell : ℝ) + 1) ∧
    ∀ (B : ℝ) (E : ℕ), 1 ≤ B →
      ∃ (C : ℝ) (K : ℕ), 2 ≤ C ∧ 1 ≤ K ∧
        ∀ (A T r center : ℝ) (f : ℝ → ℝ)
          (y1 y2 x1 x2 : Rect → ℤ) (u v : Rect → ℝ),
          1 ≤ A → C * A ^ K ≤ T →
          (B * A ^ E)⁻¹ ≤ r →
          |center| ≤ B * A ^ E →
          ContDiffOn ℝ (ell + 1) f (Set.Ioo (-r) r) →
          (∀ n : ℕ, n ≤ ell + 1 →
            ∀ t ∈ Set.Ioo (-r) r,
              |iteratedDeriv n f t| ≤ B * A ^ E) →
          (∀ i, y2 i ≠ 0 ∧ x2 i ≠ 0) →
          (∀ i, u i = (y1 i : ℝ) / (y2 i : ℝ) - center) →
          (∀ i, v i = (x1 i : ℝ) / (x2 i : ℝ) - f (u i)) →
          (∀ i, |u i| ≤ (B * A ^ E) * T ^ (-mu)) →
          (∀ i, |v i| ≤ (B * A ^ E) * T ^ (-(1 : ℝ))) →
          (∀ i, |(y2 i : ℝ) ^ (3 * q) * (x2 i : ℝ) ^ (2 * q)| ≤
            (B * A ^ E) * T ^ (q : ℝ)) →
          |(FormalAB.S61c6e1a7.A1OriginalDeterminant.rawEval
              q y1 y2 x1 x2).det| ≤
              C * A ^ K * T ^ (-((J : ℝ) * (q : ℝ)) - gap) ∧
            (FormalAB.S61c6e1a7.A1OriginalDeterminant.clearedEval
              q y1 y2 x1 x2).det = 0 :=
  A3PolynomialOriginalDeterminant.polynomialOriginalDeterminant
end JocelynClaims
#print axioms JocelynClaims.claim_a784ea0d4882079f077167e52b8b095db4d6b6a3bb097a313cf37b8ae344b161
