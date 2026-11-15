-- Source SHA-256: 0b0bfb18c4755ae5c10cd92942b0b9f9aa94072e4cb6b6dfb7090a33e9b841aa
import Mathlib
import JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.LemmaP
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB

namespace FormalAB.Sa57df17a

set_option maxRecDepth 5000
set_option maxHeartbeats 1000000
set_option pp.maxSteps 1000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace ConsecutiveCountingA5OriginalAffineInterval
open Polynomial

noncomputable def originalDPoly
    (b m d₀ r₀ J : ℤ) : Polynomial ℝ :=
  C (((m * d₀ + b * r₀ : ℤ) : ℝ)) +
    C (((b * J : ℤ) : ℝ)) * X

noncomputable def originalEPoly
    (a m e₀ r₀ J : ℤ) : Polynomial ℝ :=
  C (((m * e₀ - a * r₀ : ℤ) : ℝ)) -
    C (((a * J : ℤ) : ℝ)) * X

noncomputable def originalQPoly
    (a b c m d₀ e₀ r₀ J A₀ B₀ : ℤ) : Polynomial ℝ :=
  (C (A₀ : ℝ) * originalDPoly b m d₀ r₀ J +
    C (B₀ : ℝ) * originalEPoly a m e₀ r₀ J) *
      C (((c : ℝ) * (m : ℝ) ^ 2)⁻¹)

noncomputable def originalUPoly
    (a b c m d₀ e₀ r₀ J A₀ B₀ : ℤ) : Polynomial ℝ :=
  (originalQPoly a b c m d₀ e₀ r₀ J A₀ B₀ *
      (originalEPoly a m e₀ r₀ J) ^ 2 -
    C ((a : ℝ) ^ 2) *
      (C (a : ℝ) * originalDPoly b m d₀ r₀ J +
        C ((3 * b : ℤ) : ℝ) *
          originalEPoly a m e₀ r₀ J)) *
      C (((m : ℝ) ^ 3)⁻¹)

noncomputable def originalPiPoly
    (a b m d₀ e₀ r₀ J : ℤ) : Polynomial ℝ :=
  originalDPoly b m d₀ r₀ J *
    originalEPoly a m e₀ r₀ J

noncomputable def originalSPoly
    (a b m d₀ e₀ r₀ J : ℤ) : Polynomial ℝ :=
  C (b : ℝ) * originalEPoly a m e₀ r₀ J -
    C (a : ℝ) * originalDPoly b m d₀ r₀ J

noncomputable def originalQr
    (a b c m A₀ B₀ : ℤ) : ℝ :=
  (((A₀ * b - B₀ * a : ℤ) : ℝ)) /
    ((c : ℝ) * (m : ℝ) ^ 2)

noncomputable def originalNPoly
    (a b c m d₀ e₀ r₀ J A₀ B₀ : ℤ) : Polynomial ℝ :=
  (originalDPoly b m d₀ r₀ J) ^ 2 *
    originalUPoly a b c m d₀ e₀ r₀ J A₀ B₀

def OriginalAffineIntervalAlgebraStatement : Prop :=
  let delta : ℝ := 1 / 100000;
  ∀ a b c m d₀ e₀ r₀ J A₀ B₀ : ℤ,
    c ≠ 0 → m ≠ 0 → 0 < J →
    a * d₀ + b * e₀ = 1 →
    a * B₀ - b * A₀ ≠ 0 →
    let d : Polynomial ℝ := originalDPoly b m d₀ r₀ J;
    let e : Polynomial ℝ := originalEPoly a m e₀ r₀ J;
    let q : Polynomial ℝ := originalQPoly a b c m d₀ e₀ r₀ J A₀ B₀;
    let Pi : Polynomial ℝ := originalPiPoly a b m d₀ e₀ r₀ J;
    let S : Polynomial ℝ := originalSPoly a b m d₀ e₀ r₀ J;
    let N : Polynomial ℝ := originalNPoly a b c m d₀ e₀ r₀ J A₀ B₀;
    let q_r : ℝ := originalQr a b c m A₀ B₀;
    let g : ℝ := |((a * b : ℤ) : ℝ)|;
    (1 ≤ (J : ℝ) ∧
      q_r ≠ 0 ∧
      Polynomial.C (a : ℝ) * d + Polynomial.C (b : ℝ) * e =
        Polynomial.C (m : ℝ) ∧
      q.derivative = Polynomial.C (q_r * (J : ℝ))) ∧
    ∀ C_ratio D E M ρ₀ s t : ℝ,
      0 < C_ratio → 0 < D → 0 < E → 0 < M →
      (∀ z : ℝ, z = s ∨ z = t →
        D / 2 < d.eval z ∧ d.eval z ≤ D ∧
        E / 2 < e.eval z ∧ e.eval z ≤ E ∧
        ρ₀ < d.eval z / e.eval z ∧
        d.eval z / e.eval z ≤ ρ₀ + C_ratio * D / (E * M)) →
      (t - s) * |(m : ℝ)| * (J : ℝ) * M ≤ C_ratio * (D * E) ∧
      ((m : ℝ) ^ 2 ≤ delta * g * (D * E) →
        a * b < 0 ∧ 1 ≤ g ∧
        S ^ 2 = Polynomial.C ((m : ℝ) ^ 2) +
          Polynomial.C (4 * g) * Pi ∧
        Pi.derivative = Polynomial.C (J : ℝ) * S ∧
        S.derivative = Polynomial.C (2 * g * (J : ℝ)) ∧
        Polynomial.C ((m : ℝ) ^ 3) * N =
          q * Pi ^ 2 -
            (Polynomial.C ((m : ℝ) ^ 3 / 2) -
              Polynomial.C ((m : ℝ) ^ 2 / 2) * S +
              Polynomial.C g * Pi * S))

theorem deep_entry_from_positive_box
    (a b m : ℤ) (D E d e : ℝ)
    (hm : m ≠ 0) (hD : 0 < D) (hE : 0 < E)
    (hd : D / 2 < d) (he : E / 2 < e)
    (hlevel : (a : ℝ) * d + (b : ℝ) * e = (m : ℝ))
    (hdeep : (m : ℝ) ^ 2 ≤
      (1 / 100000 : ℝ) * |((a * b : ℤ) : ℝ)| * (D * E)) :
    a * b < 0 ∧ 1 ≤ |((a * b : ℤ) : ℝ)| := by
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  have hmsq : 0 < (m : ℝ) ^ 2 := sq_pos_of_ne_zero hmR
  have hdpos : 0 < d := lt_trans (half_pos hD) hd
  have hepos : 0 < e := lt_trans (half_pos hE) he
  have hhalf₁ : (D / 2) * (E / 2) < d * (E / 2) :=
    mul_lt_mul_of_pos_right hd (half_pos hE)
  have hhalf₂ : d * (E / 2) < d * e :=
    mul_lt_mul_of_pos_left he hdpos
  have hbox : D * E ≤ 4 * d * e := by
    nlinarith only [hhalf₁, hhalf₂]
  have hform :
      (m : ℝ) ^ 2 =
        ((a : ℝ) * d - (b : ℝ) * e) ^ 2 +
          4 * ((a * b : ℤ) : ℝ) * d * e := by
    rw [← hlevel]
    push_cast
    ring
  have hab : a * b < 0 := by
    by_contra hnot
    have habZ : 0 ≤ a * b := le_of_not_gt hnot
    have habR : 0 ≤ ((a * b : ℤ) : ℝ) := by
      exact_mod_cast habZ
    have hdeep' :
        (m : ℝ) ^ 2 ≤
          (1 / 100000 : ℝ) * ((a * b : ℤ) : ℝ) * (D * E) := by
      simpa only [abs_of_nonneg habR] using hdeep
    have hmul := mul_le_mul_of_nonneg_left hbox habR
    have hlow :
        ((a * b : ℤ) : ℝ) * (D * E) ≤ (m : ℝ) ^ 2 := by
      nlinarith only [hmul, hform,
        sq_nonneg ((a : ℝ) * d - (b : ℝ) * e)]
    nlinarith only [hlow, hdeep', hmsq]
  refine ⟨hab, ?_⟩
  have habR : ((a * b : ℤ) : ℝ) < 0 := by exact_mod_cast hab
  have habZ₁ : a * b ≤ -1 := by omega
  have habR₁ : ((a * b : ℤ) : ℝ) ≤ -1 := by
    exact_mod_cast habZ₁
  rw [abs_of_neg habR]
  linarith only [habR₁]

theorem original_g_eq_neg_product
    (a b : ℤ) (hab : a * b < 0) :
    |((a * b : ℤ) : ℝ)| = -(a : ℝ) * (b : ℝ) := by
  have habR : ((a * b : ℤ) : ℝ) < 0 := by exact_mod_cast hab
  rw [abs_of_neg habR]
  push_cast
  ring

theorem original_affine_level
    (a b m d₀ e₀ r₀ J : ℤ)
    (hbez : a * d₀ + b * e₀ = 1) :
    C (a : ℝ) * originalDPoly b m d₀ r₀ J +
      C (b : ℝ) * originalEPoly a m e₀ r₀ J =
        C (m : ℝ) := by
  have hbezR :
      (a : ℝ) * (d₀ : ℝ) + (b : ℝ) * (e₀ : ℝ) = 1 := by
    exact_mod_cast hbez
  have hbezC :
      C (a : ℝ) * C (d₀ : ℝ) +
        C (b : ℝ) * C (e₀ : ℝ) = (1 : Polynomial ℝ) := by
    simpa only [map_add, map_mul, map_one] using
      congrArg (fun z : ℝ => (C z : Polynomial ℝ)) hbezR
  calc
    _ = C (m : ℝ) *
        (C (a : ℝ) * C (d₀ : ℝ) +
          C (b : ℝ) * C (e₀ : ℝ)) := by
      simp only [originalDPoly, originalEPoly,
        Int.cast_add, Int.cast_sub, Int.cast_mul,
        map_add, map_sub, map_mul]
      ring
    _ = C (m : ℝ) := by rw [hbezC]; ring

theorem original_qr_ne
    (a b c m A₀ B₀ : ℤ)
    (hc : c ≠ 0) (hm : m ≠ 0)
    (hDelta : a * B₀ - b * A₀ ≠ 0) :
    originalQr a b c m A₀ B₀ ≠ 0 := by
  have hnumZ : A₀ * b - B₀ * a ≠ 0 := by
    intro hz
    apply hDelta
    calc
      a * B₀ - b * A₀ = -(A₀ * b - B₀ * a) := by ring
      _ = 0 := by rw [hz]; ring
  have hnumR : ((A₀ * b - B₀ * a : ℤ) : ℝ) ≠ 0 := by
    exact_mod_cast hnumZ
  have hcR : (c : ℝ) ≠ 0 := by exact_mod_cast hc
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  exact div_ne_zero hnumR (mul_ne_zero hcR (pow_ne_zero 2 hmR))

theorem original_q_derivative
    (a b c m d₀ e₀ r₀ J A₀ B₀ : ℤ) :
    (originalQPoly a b c m d₀ e₀ r₀ J A₀ B₀).derivative =
      C (originalQr a b c m A₀ B₀ * (J : ℝ)) := by
  simp only [originalQPoly, originalDPoly, originalEPoly, originalQr,
    derivative_add, derivative_sub, derivative_mul, derivative_C,
    derivative_X, Int.cast_add, Int.cast_sub, Int.cast_mul,
    div_eq_mul_inv, map_add, map_sub, map_mul,
    zero_mul, mul_zero, zero_add, add_zero, zero_sub, mul_one, one_mul] <;> ring

theorem original_Pi_derivative
    (a b m d₀ e₀ r₀ J : ℤ) :
    (originalPiPoly a b m d₀ e₀ r₀ J).derivative =
      C (J : ℝ) * originalSPoly a b m d₀ e₀ r₀ J := by
  simp only [originalPiPoly, originalSPoly, originalDPoly, originalEPoly,
    derivative_add, derivative_sub, derivative_mul, derivative_C,
    derivative_X, Int.cast_add, Int.cast_sub, Int.cast_mul,
    map_add, map_sub, map_mul,
    zero_mul, mul_zero, zero_add, add_zero, zero_sub, mul_one, one_mul]
  ring

theorem original_S_derivative
    (a b m d₀ e₀ r₀ J : ℤ) :
    (originalSPoly a b m d₀ e₀ r₀ J).derivative =
      C (-(2 : ℝ) * (a : ℝ) * (b : ℝ) * (J : ℝ)) := by
  have hCtwo : (C (2 : ℝ) : Polynomial ℝ) = 2 := by
    calc
      C (2 : ℝ) = C ((1 : ℝ) + 1) := by congr 1 <;> norm_num
      _ = C (1 : ℝ) + C (1 : ℝ) := by rw [map_add]
      _ = 2 := by simp only [map_one] <;> norm_num
  simp only [originalSPoly, originalDPoly, originalEPoly,
    derivative_add, derivative_sub, derivative_mul, derivative_C,
    derivative_X, Int.cast_add, Int.cast_sub, Int.cast_mul,
    map_add, map_sub, map_mul, map_neg,
    zero_mul, mul_zero, zero_add, add_zero, zero_sub, mul_one, one_mul]
  rw [hCtwo] <;> ring

theorem squared_from_original_level
    (a b m g : ℝ) (d e : Polynomial ℝ)
    (hlevel : C a * d + C b * e = C m)
    (hg : g = -a * b) :
    (C b * e - C a * d) ^ 2 =
      C (m ^ 2) + C (4 * g) * (d * e) := by
  apply Polynomial.funext
  intro z
  have hz :
      a * d.eval z + b * e.eval z = m := by
    simpa only [eval_add, eval_mul, eval_C] using
      congrArg (fun p : Polynomial ℝ => p.eval z) hlevel
  simp only [eval_pow, eval_sub, eval_add, eval_mul, eval_C]
  calc
    _ = (a * d.eval z + b * e.eval z) ^ 2 +
        4 * g * (d.eval z * e.eval z) := by rw [hg]; ring
    _ = m ^ 2 + 4 * g * (d.eval z * e.eval z) := by rw [hz]

theorem real_original_H3
    (a b m g d e : ℝ)
    (hlevel : a * d + b * e = m)
    (hg : g = -a * b) :
    (a * d) ^ 2 * (a * d + 3 * b * e) =
      m ^ 3 / 2 - m ^ 2 * (b * e - a * d) / 2 +
        g * (d * e) * (b * e - a * d) := by
  rw [← hlevel, hg]
  ring

theorem signed_numerator_from_original_level
    (a b m g : ℝ) (d e q : Polynomial ℝ)
    (hm : m ≠ 0)
    (hlevel : C a * d + C b * e = C m)
    (hg : g = -a * b) :
    C (m ^ 3) *
        (d ^ 2 *
          ((q * e ^ 2 - C (a ^ 2) *
            (C a * d + C (3 * b) * e)) * C ((m ^ 3)⁻¹))) =
      q * (d * e) ^ 2 -
        (C (m ^ 3 / 2) - C (m ^ 2 / 2) * (C b * e - C a * d) +
          C g * (d * e) * (C b * e - C a * d)) := by
  apply Polynomial.funext
  intro z
  have hz :
      a * d.eval z + b * e.eval z = m := by
    simpa only [eval_add, eval_mul, eval_C] using
      congrArg (fun p : Polynomial ℝ => p.eval z) hlevel
  simp only [eval_mul, eval_sub, eval_add, eval_pow, eval_C]
  calc
    _ = q.eval z * (d.eval z * e.eval z) ^ 2 -
        (a * d.eval z) ^ 2 * (a * d.eval z + 3 * b * e.eval z) := by
      field_simp [hm] <;> ring
    _ = q.eval z * (d.eval z * e.eval z) ^ 2 -
        (m ^ 3 / 2 - m ^ 2 / 2 * (b * e.eval z - a * d.eval z) +
          g * (d.eval z * e.eval z) * (b * e.eval z - a * d.eval z)) := by
      rw [real_original_H3 a b m g (d.eval z) (e.eval z) hz hg]
      ring

theorem cell_diameter_from_cross
    (dx dy ex ey m J E h x y : ℝ)
    (hcross : dy * ex - dx * ey = m * J * (y - x))
    (hex : 0 < ex) (hey : 0 < ey)
    (hexE : ex ≤ E) (heyE : ey ≤ E)
    (hm : m ≠ 0) (hJ : 0 < J) (hxy : x ≤ y)
    (hh : 0 ≤ h)
    (hwindow : |dy / ey - dx / ex| ≤ h) :
    y - x ≤ h * E ^ 2 / (|m| * J) := by
  have hr : dy / ey - dx / ex =
      m * J * (y - x) / (ex * ey) := by
    field_simp
    nlinarith [hcross]
  have habs : |dy / ey - dx / ex| =
      |m| * J * (y - x) / (ex * ey) := by
    rw [hr]
    simp only [abs_div, abs_mul, abs_of_pos hJ,
      abs_of_nonneg (sub_nonneg.mpr hxy),
      abs_of_pos (mul_pos hex hey)] <;> ring
  rw [habs] at hwindow
  have hmul : |m| * J * (y - x) ≤ h * (ex * ey) :=
    (div_le_iff₀ (mul_pos hex hey)).mp hwindow
  have hprod : ex * ey ≤ E ^ 2 := by
    have h1 : ex * ey ≤ E * ey :=
      mul_le_mul_of_nonneg_right hexE hey.le
    have h2 : E * ey ≤ E * E :=
      mul_le_mul_of_nonneg_left heyE (le_trans hey.le heyE)
    nlinarith [h1, h2]
  have htotal : |m| * J * (y - x) ≤ h * E ^ 2 :=
    le_trans hmul (mul_le_mul_of_nonneg_left hprod hh)
  have hmJ : 0 < |m| * J := mul_pos (abs_pos.mpr hm) hJ
  apply (le_div_iff₀ hmJ).2
  nlinarith [htotal]

theorem original_affine_crossdifference
    (a b m d₀ e₀ r₀ J : ℤ)
    (hbez : a * d₀ + b * e₀ = 1) (s t : ℝ) :
    (originalDPoly b m d₀ r₀ J).eval t *
        (originalEPoly a m e₀ r₀ J).eval s -
      (originalDPoly b m d₀ r₀ J).eval s *
        (originalEPoly a m e₀ r₀ J).eval t =
      (m : ℝ) * (J : ℝ) * (t - s) := by
  have hbezR :
      (a : ℝ) * (d₀ : ℝ) + (b : ℝ) * (e₀ : ℝ) = 1 := by
    exact_mod_cast hbez
  calc
    _ = (m : ℝ) *
        ((a : ℝ) * (d₀ : ℝ) + (b : ℝ) * (e₀ : ℝ)) *
        (J : ℝ) * (t - s) := by
      simp only [originalDPoly, originalEPoly,
        eval_add, eval_sub, eval_mul, eval_C, eval_X,
        Int.cast_add, Int.cast_sub, Int.cast_mul]
      ring
    _ = (m : ℝ) * (J : ℝ) * (t - s) := by rw [hbezR]; ring

theorem original_pair_cell
    (a b m d₀ e₀ r₀ J : ℤ)
    (hm : m ≠ 0) (hJ : 0 < J)
    (hbez : a * d₀ + b * e₀ = 1)
    (C_ratio D E M ρ₀ s t : ℝ)
    (hC : 0 < C_ratio) (hD : 0 < D) (hE : 0 < E) (hM : 0 < M)
    (hes : 0 < (originalEPoly a m e₀ r₀ J).eval s)
    (het : 0 < (originalEPoly a m e₀ r₀ J).eval t)
    (hesE : (originalEPoly a m e₀ r₀ J).eval s ≤ E)
    (hetE : (originalEPoly a m e₀ r₀ J).eval t ≤ E)
    (hrsL : ρ₀ <
      (originalDPoly b m d₀ r₀ J).eval s /
        (originalEPoly a m e₀ r₀ J).eval s)
    (hrsU :
      (originalDPoly b m d₀ r₀ J).eval s /
        (originalEPoly a m e₀ r₀ J).eval s ≤
          ρ₀ + C_ratio * D / (E * M))
    (hrtL : ρ₀ <
      (originalDPoly b m d₀ r₀ J).eval t /
        (originalEPoly a m e₀ r₀ J).eval t)
    (hrtU :
      (originalDPoly b m d₀ r₀ J).eval t /
        (originalEPoly a m e₀ r₀ J).eval t ≤
          ρ₀ + C_ratio * D / (E * M)) :
    (t - s) * |(m : ℝ)| * (J : ℝ) * M ≤ C_ratio * (D * E) := by
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  have hJR : 0 < (J : ℝ) := by exact_mod_cast hJ
  by_cases hst : s ≤ t
  · have hcross := original_affine_crossdifference
      a b m d₀ e₀ r₀ J hbez s t
    have hwindow :
        |(originalDPoly b m d₀ r₀ J).eval t /
            (originalEPoly a m e₀ r₀ J).eval t -
          (originalDPoly b m d₀ r₀ J).eval s /
            (originalEPoly a m e₀ r₀ J).eval s| ≤
          C_ratio * D / (E * M) := by
      rw [abs_le]
      constructor <;> linarith only [hrsL, hrsU, hrtL, hrtU]
    have hwidth := cell_diameter_from_cross
      ((originalDPoly b m d₀ r₀ J).eval s)
      ((originalDPoly b m d₀ r₀ J).eval t)
      ((originalEPoly a m e₀ r₀ J).eval s)
      ((originalEPoly a m e₀ r₀ J).eval t)
      (m : ℝ) (J : ℝ) E (C_ratio * D / (E * M)) s t
      hcross hes het hesE hetE hmR hJR hst (by positivity) hwindow
    have hmul :
        (t - s) * (|(m : ℝ)| * (J : ℝ)) ≤
          (C_ratio * D / (E * M)) * E ^ 2 :=
      (le_div_iff₀ (mul_pos (abs_pos.mpr hmR) hJR)).mp hwidth
    calc
      (t - s) * |(m : ℝ)| * (J : ℝ) * M =
          ((t - s) * (|(m : ℝ)| * (J : ℝ))) * M := by ring
      _ ≤ ((C_ratio * D / (E * M)) * E ^ 2) * M :=
        mul_le_mul_of_nonneg_right hmul hM.le
      _ = C_ratio * (D * E) := by
        field_simp [ne_of_gt hE, ne_of_gt hM]
  · have hts : t - s ≤ 0 := by linarith
    have hnonpos :
        (t - s) * |(m : ℝ)| * (J : ℝ) * M ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg
          (mul_nonpos_of_nonpos_of_nonneg hts (abs_nonneg _)) hJR.le) hM.le
    exact hnonpos.trans (by positivity)

theorem original_affine_interval_algebra :
    OriginalAffineIntervalAlgebraStatement := by
  dsimp only [OriginalAffineIntervalAlgebraStatement]
  intro a b c m d₀ e₀ r₀ J A₀ B₀ hc hm hJ hbez hDelta
  let d : Polynomial ℝ := originalDPoly b m d₀ r₀ J
  let e : Polynomial ℝ := originalEPoly a m e₀ r₀ J
  let q : Polynomial ℝ := originalQPoly a b c m d₀ e₀ r₀ J A₀ B₀
  let Pi : Polynomial ℝ := originalPiPoly a b m d₀ e₀ r₀ J
  let S : Polynomial ℝ := originalSPoly a b m d₀ e₀ r₀ J
  let N : Polynomial ℝ := originalNPoly a b c m d₀ e₀ r₀ J A₀ B₀
  let q_r : ℝ := originalQr a b c m A₀ B₀
  let g : ℝ := |((a * b : ℤ) : ℝ)|
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  have hJoneZ : (1 : ℤ) ≤ J := by omega
  have hJone : (1 : ℝ) ≤ (J : ℝ) := by exact_mod_cast hJoneZ
  have hqr : q_r ≠ 0 := original_qr_ne a b c m A₀ B₀ hc hm hDelta
  have hlevel : C (a : ℝ) * d + C (b : ℝ) * e = C (m : ℝ) :=
    original_affine_level a b m d₀ e₀ r₀ J hbez
  have hqderiv : q.derivative = C (q_r * (J : ℝ)) :=
    original_q_derivative a b c m d₀ e₀ r₀ J A₀ B₀
  refine ⟨⟨hJone, hqr, hlevel, hqderiv⟩, ?_⟩
  intro C_ratio D E M ρ₀ s t hC hD hE hM hendpoints
  rcases hendpoints s (Or.inl rfl) with
    ⟨hdsL, hdsU, hesL, hesU, hrsL, hrsU⟩
  rcases hendpoints t (Or.inr rfl) with
    ⟨hdtL, hdtU, hetL, hetU, hrtL, hrtU⟩
  have hespos : 0 < e.eval s := lt_trans (half_pos hE) hesL
  have hetpos : 0 < e.eval t := lt_trans (half_pos hE) hetL
  refine ⟨?_, ?_⟩
  · exact original_pair_cell a b m d₀ e₀ r₀ J hm hJ hbez
      C_ratio D E M ρ₀ s t hC hD hE hM
      hespos hetpos hesU hetU hrsL hrsU hrtL hrtU
  · intro hdeep
    have hlevels :
        (a : ℝ) * d.eval s + (b : ℝ) * e.eval s = (m : ℝ) := by
      simpa only [eval_add, eval_mul, eval_C] using
        congrArg (fun p : Polynomial ℝ => p.eval s) hlevel
    obtain ⟨hab, hg₁⟩ := deep_entry_from_positive_box
      a b m D E (d.eval s) (e.eval s)
      hm hD hE hdsL hesL hlevels hdeep
    have hg : g = -(a : ℝ) * (b : ℝ) :=
      original_g_eq_neg_product a b hab
    have hsquare :
        S ^ 2 = C ((m : ℝ) ^ 2) + C (4 * g) * Pi := by
      exact squared_from_original_level
        (a : ℝ) (b : ℝ) (m : ℝ) g d e hlevel hg
    have hPi : Pi.derivative = C (J : ℝ) * S :=
      original_Pi_derivative a b m d₀ e₀ r₀ J
    have hS : S.derivative = C (2 * g * (J : ℝ)) := by
      calc
        S.derivative = C (-(2 : ℝ) * (a : ℝ) * (b : ℝ) * (J : ℝ)) :=
          original_S_derivative a b m d₀ e₀ r₀ J
        _ = C (2 * g * (J : ℝ)) := by congr 1; rw [hg]; ring
    have hN :
        C ((m : ℝ) ^ 3) * N =
          q * Pi ^ 2 -
            (C ((m : ℝ) ^ 3 / 2) -
              C ((m : ℝ) ^ 2 / 2) * S + C g * Pi * S) := by
      simpa only [N, Pi, S, d, e, q,
        originalNPoly, originalUPoly, originalPiPoly, originalSPoly,
        Int.cast_mul, Int.cast_ofNat] using
          signed_numerator_from_original_level
            (a : ℝ) (b : ℝ) (m : ℝ) g d e q hmR hlevel hg
    exact ⟨hab, hg₁, hsquare, hPi, hS, hN⟩

end ConsecutiveCountingA5OriginalAffineInterval

namespace JocelynClaims

theorem claim_38b3ece0876ba8e7eb5509d6e33bcf9b65b705370f7fb7d9f7ada061cce3632a :
  let delta : ℝ := 1 / 100000;
    ∀ a b c m d₀ e₀ r₀ J A₀ B₀ : ℤ,
      c ≠ 0 → m ≠ 0 → 0 < J →
      a * d₀ + b * e₀ = 1 →
      a * B₀ - b * A₀ ≠ 0 →
      let d : Polynomial ℝ :=
        Polynomial.C (((m * d₀ + b * r₀ : ℤ) : ℝ)) +
          Polynomial.C (((b * J : ℤ) : ℝ)) * Polynomial.X;
      let e : Polynomial ℝ :=
        Polynomial.C (((m * e₀ - a * r₀ : ℤ) : ℝ)) -
          Polynomial.C (((a * J : ℤ) : ℝ)) * Polynomial.X;
      let q : Polynomial ℝ :=
        (Polynomial.C (A₀ : ℝ) * d + Polynomial.C (B₀ : ℝ) * e) *
          Polynomial.C (((c : ℝ) * (m : ℝ) ^ 2)⁻¹);
      let Pi : Polynomial ℝ := d * e;
      let S : Polynomial ℝ :=
        Polynomial.C (b : ℝ) * e - Polynomial.C (a : ℝ) * d;
      let N : Polynomial ℝ :=
        d ^ 2 *
          ((q * e ^ 2 - Polynomial.C ((a : ℝ) ^ 2) *
            (Polynomial.C (a : ℝ) * d +
              Polynomial.C ((3 * b : ℤ) : ℝ) * e)) *
            Polynomial.C (((m : ℝ) ^ 3)⁻¹));
      let q_r : ℝ :=
        (((A₀ * b - B₀ * a : ℤ) : ℝ)) /
          ((c : ℝ) * (m : ℝ) ^ 2);
      let g : ℝ := |((a * b : ℤ) : ℝ)|;
      (1 ≤ (J : ℝ) ∧
        q_r ≠ 0 ∧
        Polynomial.C (a : ℝ) * d + Polynomial.C (b : ℝ) * e =
          Polynomial.C (m : ℝ) ∧
        q.derivative = Polynomial.C (q_r * (J : ℝ))) ∧
      ∀ C_ratio D E M ρ₀ s t : ℝ,
        0 < C_ratio → 0 < D → 0 < E → 0 < M →
        (∀ z : ℝ, z = s ∨ z = t →
          D / 2 < d.eval z ∧ d.eval z ≤ D ∧
          E / 2 < e.eval z ∧ e.eval z ≤ E ∧
          ρ₀ < d.eval z / e.eval z ∧
          d.eval z / e.eval z ≤ ρ₀ + C_ratio * D / (E * M)) →
        (t - s) * |(m : ℝ)| * (J : ℝ) * M ≤ C_ratio * (D * E) ∧
        ((m : ℝ) ^ 2 ≤ delta * g * (D * E) →
          a * b < 0 ∧ 1 ≤ g ∧
          S ^ 2 = Polynomial.C ((m : ℝ) ^ 2) +
            Polynomial.C (4 * g) * Pi ∧
          Pi.derivative = Polynomial.C (J : ℝ) * S ∧
          S.derivative = Polynomial.C (2 * g * (J : ℝ)) ∧
          Polynomial.C ((m : ℝ) ^ 3) * N =
            q * Pi ^ 2 -
              (Polynomial.C ((m : ℝ) ^ 3 / 2) -
                Polynomial.C ((m : ℝ) ^ 2 / 2) * S +
                Polynomial.C g * Pi * S)) := by
  exact ConsecutiveCountingA5OriginalAffineInterval.original_affine_interval_algebra

end JocelynClaims

#print axioms JocelynClaims.claim_38b3ece0876ba8e7eb5509d6e33bcf9b65b705370f7fb7d9f7ada061cce3632a
