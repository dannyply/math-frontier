import JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.PellThueCounts

/-!
# Lemma 5.4: reduced coordinates and their heights.

Part of the counting closure; the release theorems are in `JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure`.
-/

namespace JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.dupNamespace false
set_option linter.unnecessarySimpa false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.deprecated false

namespace C09

set_option maxHeartbeats 400000

namespace PcPellRed

lemma rpow_half_sq (x : ℝ) (hx : 0 ≤ x) : (x ^ (1 / 2 : ℝ)) ^ 2 = x := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]; norm_num

lemma rpow_neg32_sq_mul (D : ℝ) (hD : 0 < D) : (D ^ (-3 / 2 : ℝ)) ^ 2 * D ^ 3 = 1 := by
  rw [← Real.rpow_natCast (D ^ (-3 / 2 : ℝ)) 2, ← Real.rpow_mul hD.le,
    ← Real.rpow_natCast D 3, ← Real.rpow_add hD]
  norm_num

lemma rpow32_sq (r : ℝ) (hr : 0 ≤ r) : (r ^ (3 / 2 : ℝ)) ^ 2 = r ^ 3 := by
  rw [← Real.rpow_natCast (r ^ (3 / 2 : ℝ)) 2, ← Real.rpow_mul hr, ← Real.rpow_natCast r 3]
  norm_num

lemma U_sq_cube (x D : ℝ) (hx : 0 ≤ x) (hD : 0 < D) :
    (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)) ^ 2 * D ^ 3 = x := by
  rw [mul_pow, mul_assoc, rpow_neg32_sq_mul D hD, mul_one, rpow_half_sq x hx]

lemma key_UV (x D E : ℝ) (hD : 0 < D) (hE : 0 < E) :
    (2 * D / E) ^ (3 / 2 : ℝ) * (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)) =
      (2 : ℝ) ^ (3 / 2 : ℝ) * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ)) := by
  have h1 : (2 * D / E) ^ (3 / 2 : ℝ) =
      (2 : ℝ) ^ (3 / 2 : ℝ) * D ^ (3 / 2 : ℝ) * E ^ (-3 / 2 : ℝ) := by
    rw [Real.div_rpow (by positivity) hE.le, Real.mul_rpow (by norm_num) hD.le]
    rw [show (-3 / 2 : ℝ) = -(3 / 2 : ℝ) by norm_num, Real.rpow_neg hE.le]
    ring
  have h2 : D ^ (3 / 2 : ℝ) * D ^ (-3 / 2 : ℝ) = 1 := by
    rw [← Real.rpow_add hD]; norm_num
  rw [h1]
  calc (2 : ℝ) ^ (3 / 2 : ℝ) * D ^ (3 / 2 : ℝ) * E ^ (-3 / 2 : ℝ) *
        (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ))
      = (2 : ℝ) ^ (3 / 2 : ℝ) * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ)) *
          (D ^ (3 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)) := by ring
    _ = _ := by rw [h2, mul_one]

lemma two_rpow32_le : (2 : ℝ) ^ (3 / 2 : ℝ) ≤ 17 / 6 := by
  have h0 : (0 : ℝ) ≤ (2 : ℝ) ^ (3 / 2 : ℝ) := by positivity
  have hsq : ((2 : ℝ) ^ (3 / 2 : ℝ)) ^ 2 = 8 := by rw [rpow32_sq 2 (by norm_num)]; norm_num
  nlinarith [hsq]

lemma poly_upper (y : ℝ) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    (1 + y) ^ 3 * (1 + y / 3) ≤ (1 + 3 * y) ^ 2 := by
  have h2 : y ^ 2 ≤ y := by nlinarith
  have h3 : y ^ 3 ≤ y ^ 2 := by nlinarith
  have h4 : y ^ 4 ≤ y ^ 3 := by nlinarith
  nlinarith [h2, h3, h4]

lemma le_of_sq_le_sq_nn (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a ^ 2 ≤ b ^ 2) : a ≤ b := by
  by_contra hc
  push Not at hc
  have h1 : 0 < a - b := by linarith
  have h2 : 0 < a + b := by linarith
  nlinarith [mul_pos h1 h2]

set_option maxHeartbeats 2000000 in

theorem reduced_i (D E x M ρ0 : ℝ) (hD : 1 / 2 ≤ D) (hE : 1 / 2 ≤ E) (hx : 1 < x) (hM : 1 ≤ M)
    (hρl : D / (2 * E) ≤ ρ0) (hρu : ρ0 ≤ 2 * D / E) (h : ℤ) (hhM : 3 * |(h : ℝ)| * M ≤ x)
    (d e u v : ℕ) (hd1 : D < (d : ℝ)) (hd2 : (d : ℝ) ≤ 2 * D) (he1 : E < (e : ℝ))
    (he2 : (e : ℝ) ≤ 2 * E)
    (hu1 : x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ) < (u : ℝ))
    (hu2 : (u : ℝ) < 2 * (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)))
    (heq : (e : ℤ) ^ 3 * (v : ℤ) ^ 2 - (d : ℤ) ^ 3 * (u : ℤ) ^ 2 = h)
    (hr1 : ρ0 < (d : ℝ) / (e : ℝ)) (hr2 : (d : ℝ) / (e : ℝ) ≤ ρ0 * (1 + 1 / M)) :
    0 < (d : ℝ) - ρ0 * (e : ℝ) ∧ (d : ℝ) - ρ0 * (e : ℝ) ≤ 4 * D / M ∧
      |(v : ℝ) - ρ0 ^ (3 / 2 : ℝ) * (u : ℝ)| ≤ 17 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ)) / M := by
  have hD0 : 0 < D := by linarith
  have hE0 : 0 < E := by linarith
  have hx0 : 0 < x := by linarith
  have hM0 : 0 < M := by linarith
  have hMne : M ≠ 0 := hM0.ne'
  have hEne : E ≠ 0 := hE0.ne'
  have he0 : (0 : ℝ) < e := by linarith
  have hd0 : (0 : ℝ) < d := by linarith
  have hρ0 : 0 < ρ0 := lt_of_lt_of_le (by positivity) hρl
  have hU0 : 0 < x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ) := by positivity
  have hu0 : (0 : ℝ) < u := lt_trans hU0 hu1
  have hv0 : (0 : ℝ) ≤ v := Nat.cast_nonneg v
  have hlin1 : ρ0 * e < d := by rwa [lt_div_iff₀ he0] at hr1
  have hlin2 : (d : ℝ) ≤ ρ0 * (1 + 1 / M) * e := by rwa [div_le_iff₀ he0] at hr2
  have hA : 0 < (d : ℝ) - ρ0 * e := by linarith
  have hB : (d : ℝ) - ρ0 * e ≤ 4 * D / M := by
    have h1 : (d : ℝ) - ρ0 * e ≤ ρ0 * e / M := by
      have : ρ0 * (1 + 1 / M) * e = ρ0 * e + ρ0 * e / M := by field_simp
      linarith
    have h2 : ρ0 * e ≤ 2 * D / E * (2 * E) := mul_le_mul hρu he2 he0.le (by positivity)
    have h3 : 2 * D / E * (2 * E) = 4 * D := by field_simp; ring
    rw [h3] at h2
    calc (d : ℝ) - ρ0 * e ≤ ρ0 * e / M := h1
      _ ≤ 4 * D / M := div_le_div_of_nonneg_right h2 hM0.le
  refine ⟨hA, hB, ?_⟩
  have heqR : (e : ℝ) ^ 3 * (v : ℝ) ^ 2 = (d : ℝ) ^ 3 * (u : ℝ) ^ 2 + (h : ℝ) := by
    have := congrArg (fun z : ℤ => (z : ℝ)) heq
    push_cast at this
    linarith
  have hY : x < (d : ℝ) ^ 3 * (u : ℝ) ^ 2 := by
    have h1 := U_sq_cube x D hx0.le hD0
    have h2 : (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)) ^ 2 < (u : ℝ) ^ 2 := by nlinarith
    have h3 : D ^ 3 < (d : ℝ) ^ 3 := pow_lt_pow_left₀ hd1 hD0.le (by norm_num)
    have h4 : (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)) ^ 2 * D ^ 3 < (u : ℝ) ^ 2 * (d : ℝ) ^ 3 :=
      mul_lt_mul'' h2 h3 (by positivity) (by positivity)
    linarith
  have hYpos : 0 < (d : ℝ) ^ 3 * (u : ℝ) ^ 2 := lt_trans hx0 hY
  have habs : |(h : ℝ)| ≤ (d : ℝ) ^ 3 * (u : ℝ) ^ 2 * ((1 / M) / 3) := by
    have k : 3 * M * |(h : ℝ)| ≤ (d : ℝ) ^ 3 * (u : ℝ) ^ 2 := by linarith
    rw [show (d : ℝ) ^ 3 * (u : ℝ) ^ 2 * ((1 / M) / 3) = (d : ℝ) ^ 3 * (u : ℝ) ^ 2 / (3 * M) by
      field_simp]
    rw [le_div_iff₀ (by positivity)]
    linarith
  have hhl : -((d : ℝ) ^ 3 * (u : ℝ) ^ 2 * ((1 / M) / 3)) ≤ (h : ℝ) := by
    linarith [neg_abs_le (h : ℝ)]
  have hhu : (h : ℝ) ≤ (d : ℝ) ^ 3 * (u : ℝ) ^ 2 * ((1 / M) / 3) := by
    linarith [le_abs_self (h : ℝ)]
  have hω00 : 0 ≤ ρ0 ^ (3 / 2 : ℝ) := by positivity
  have hω0sq : (ρ0 ^ (3 / 2 : ℝ)) ^ 2 = ρ0 ^ 3 := rpow32_sq ρ0 hρ0.le
  have hωle : ρ0 ^ (3 / 2 : ℝ) ≤ (2 * D / E) ^ (3 / 2 : ℝ) :=
    Real.rpow_le_rpow hρ0.le hρu (by norm_num)
  have hy0 : 0 < 1 / M := by positivity
  have hy1 : 1 / M ≤ 1 := by rw [div_le_one hM0]; exact hM
  generalize hy : 1 / M = y at hy0 hy1 hhl hhu hlin2
  generalize hω : ρ0 ^ (3 / 2 : ℝ) = ω0 at hω00 hω0sq hωle ⊢
  have hd3l : ρ0 ^ 3 * (e : ℝ) ^ 3 < (d : ℝ) ^ 3 := by
    have := pow_lt_pow_left₀ hlin1 (by positivity) (by norm_num : (3 : ℕ) ≠ 0)
    rw [mul_pow] at this; exact this
  have hd3u : (d : ℝ) ^ 3 ≤ ρ0 ^ 3 * (1 + y) ^ 3 * (e : ℝ) ^ 3 := by
    have := pow_le_pow_left₀ hd0.le hlin2 3
    rw [mul_pow, mul_pow] at this; exact this
  have e3 : (0 : ℝ) < (e : ℝ) ^ 3 := by positivity
  have hu2' : (0 : ℝ) ≤ (u : ℝ) ^ 2 := sq_nonneg _
  have P0 : 0 ≤ ρ0 ^ 3 * (e : ℝ) ^ 3 * (u : ℝ) ^ 2 := by positivity
  have hlow : ω0 * (1 - y) * u ≤ v := by
    have hnn : 0 ≤ ω0 * (1 - y) * u := by
      have : 0 ≤ 1 - y := by linarith
      positivity
    apply le_of_sq_le_sq_nn _ _ hnn hv0
    have k1 : (d : ℝ) ^ 3 * (u : ℝ) ^ 2 * (1 - y / 3) ≤ (e : ℝ) ^ 3 * (v : ℝ) ^ 2 := by
      rw [heqR]; nlinarith
    have a1 : (1 - y) ^ 2 ≤ 1 - y / 3 := by nlinarith
    have a2 : ρ0 ^ 3 * (e : ℝ) ^ 3 * (u : ℝ) ^ 2 ≤ (d : ℝ) ^ 3 * (u : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_right hd3l.le hu2'
    have k2 : ρ0 ^ 3 * (e : ℝ) ^ 3 * (u : ℝ) ^ 2 * (1 - y) ^ 2 ≤
        (d : ℝ) ^ 3 * (u : ℝ) ^ 2 * (1 - y / 3) := by
      calc ρ0 ^ 3 * (e : ℝ) ^ 3 * (u : ℝ) ^ 2 * (1 - y) ^ 2
          ≤ ρ0 ^ 3 * (e : ℝ) ^ 3 * (u : ℝ) ^ 2 * (1 - y / 3) := mul_le_mul_of_nonneg_left a1 P0
        _ ≤ (d : ℝ) ^ 3 * (u : ℝ) ^ 2 * (1 - y / 3) :=
            mul_le_mul_of_nonneg_right a2 (by linarith)
    have k3 : (e : ℝ) ^ 3 * (ω0 * (1 - y) * u) ^ 2 =
        ρ0 ^ 3 * (e : ℝ) ^ 3 * (u : ℝ) ^ 2 * (1 - y) ^ 2 := by
      rw [mul_pow, mul_pow, hω0sq]; ring
    have k4 : (e : ℝ) ^ 3 * (ω0 * (1 - y) * u) ^ 2 ≤ (e : ℝ) ^ 3 * (v : ℝ) ^ 2 := by linarith
    exact le_of_mul_le_mul_left k4 e3
  have hupp : (v : ℝ) ≤ ω0 * (1 + 3 * y) * u := by
    have hnn : 0 ≤ ω0 * (1 + 3 * y) * u := by positivity
    apply le_of_sq_le_sq_nn _ _ hv0 hnn
    have k1 : (e : ℝ) ^ 3 * (v : ℝ) ^ 2 ≤ (d : ℝ) ^ 3 * (u : ℝ) ^ 2 * (1 + y / 3) := by
      rw [heqR]; nlinarith
    have a1 := poly_upper y hy0.le hy1
    have a2 : (d : ℝ) ^ 3 * (u : ℝ) ^ 2 ≤ ρ0 ^ 3 * (e : ℝ) ^ 3 * (u : ℝ) ^ 2 * (1 + y) ^ 3 := by
      have := mul_le_mul_of_nonneg_right hd3u hu2'
      linarith [this]
    have k2 : (d : ℝ) ^ 3 * (u : ℝ) ^ 2 * (1 + y / 3) ≤
        ρ0 ^ 3 * (e : ℝ) ^ 3 * (u : ℝ) ^ 2 * (1 + 3 * y) ^ 2 := by
      calc (d : ℝ) ^ 3 * (u : ℝ) ^ 2 * (1 + y / 3)
          ≤ ρ0 ^ 3 * (e : ℝ) ^ 3 * (u : ℝ) ^ 2 * (1 + y) ^ 3 * (1 + y / 3) :=
            mul_le_mul_of_nonneg_right a2 (by linarith)
        _ = ρ0 ^ 3 * (e : ℝ) ^ 3 * (u : ℝ) ^ 2 * ((1 + y) ^ 3 * (1 + y / 3)) := by ring
        _ ≤ ρ0 ^ 3 * (e : ℝ) ^ 3 * (u : ℝ) ^ 2 * (1 + 3 * y) ^ 2 :=
            mul_le_mul_of_nonneg_left a1 P0
    have k3 : (e : ℝ) ^ 3 * (ω0 * (1 + 3 * y) * u) ^ 2 =
        ρ0 ^ 3 * (e : ℝ) ^ 3 * (u : ℝ) ^ 2 * (1 + 3 * y) ^ 2 := by
      rw [mul_pow, mul_pow, hω0sq]; ring
    have k4 : (e : ℝ) ^ 3 * (v : ℝ) ^ 2 ≤ (e : ℝ) ^ 3 * (ω0 * (1 + 3 * y) * u) ^ 2 := by linarith
    exact le_of_mul_le_mul_left k4 e3
  have hp : 0 ≤ y * (ω0 * u) := mul_nonneg hy0.le (mul_nonneg hω00 hu0.le)
  have habs2 : |(v : ℝ) - ω0 * u| ≤ 3 * y * (ω0 * u) := by
    rw [abs_le]
    constructor
    · have : ω0 * (1 - y) * u = ω0 * u - y * (ω0 * u) := by ring
      linarith
    · have : ω0 * (1 + 3 * y) * u = ω0 * u + 3 * (y * (ω0 * u)) := by ring
      linarith
  have hkey := key_UV x D E hD0 hE0
  have h2le := two_rpow32_le
  have hV0 : 0 < x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ) := by positivity
  have hW0 : 0 ≤ (2 * D / E) ^ (3 / 2 : ℝ) := by positivity
  have hsz : 3 * (ω0 * u) ≤ 17 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ)) := by
    have s1 : ω0 * u ≤ (2 * D / E) ^ (3 / 2 : ℝ) * (2 * (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ))) :=
      mul_le_mul hωle hu2.le hu0.le hW0
    have s2 : (2 * D / E) ^ (3 / 2 : ℝ) * (2 * (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ))) =
        2 * ((2 : ℝ) ^ (3 / 2 : ℝ) * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ))) := by
      rw [← hkey]; ring
    rw [s2] at s1
    have s3 : (2 : ℝ) ^ (3 / 2 : ℝ) * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ)) ≤
        17 / 6 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ)) := mul_le_mul_of_nonneg_right h2le hV0.le
    linarith
  calc |(v : ℝ) - ω0 * u| ≤ 3 * y * (ω0 * u) := habs2
    _ = y * (3 * (ω0 * u)) := by ring
    _ ≤ y * (17 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ))) := mul_le_mul_of_nonneg_left hsz hy0.le
    _ = 17 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ)) / M := by rw [← hy]; ring

lemma gram_bounds (p1 q1 p2 q2 Δ : ℝ) (hΔ : (p1 * q2 - q1 * p2) ^ 2 = Δ ^ 2)
    (hle : p1 ^ 2 + q1 ^ 2 ≤ p2 ^ 2 + q2 ^ 2)
    (hip : |p1 * p2 + q1 * q2| ≤ (p1 ^ 2 + q1 ^ 2) / 2) :
    Δ ^ 2 ≤ (p1 ^ 2 + q1 ^ 2) * (p2 ^ 2 + q2 ^ 2) ∧
      3 * ((p1 ^ 2 + q1 ^ 2) * (p2 ^ 2 + q2 ^ 2)) ≤ 4 * Δ ^ 2 := by
  have hlag : (p1 ^ 2 + q1 ^ 2) * (p2 ^ 2 + q2 ^ 2) - (p1 * p2 + q1 * q2) ^ 2 = Δ ^ 2 := by
    rw [← hΔ]; ring
  have hN1 : 0 ≤ p1 ^ 2 + q1 ^ 2 := by positivity
  have hP2 : (p1 * p2 + q1 * q2) ^ 2 ≤ ((p1 ^ 2 + q1 ^ 2) / 2) ^ 2 := by
    have := abs_le.mp hip
    nlinarith [this.1, this.2]
  have hN1N2 : (p1 ^ 2 + q1 ^ 2) ^ 2 ≤ (p1 ^ 2 + q1 ^ 2) * (p2 ^ 2 + q2 ^ 2) := by
    rw [sq]; exact mul_le_mul_of_nonneg_left hle hN1
  constructor
  · nlinarith [sq_nonneg (p1 * p2 + q1 * q2)]
  · nlinarith

lemma coord_lower (p1 q1 p2 q2 l1 l2 : ℝ)
    (hle : p1 ^ 2 + q1 ^ 2 ≤ p2 ^ 2 + q2 ^ 2)
    (hip : |p1 * p2 + q1 * q2| ≤ (p1 ^ 2 + q1 ^ 2) / 2) :
    (l1 ^ 2 * (p1 ^ 2 + q1 ^ 2) + l2 ^ 2 * (p2 ^ 2 + q2 ^ 2)) / 2 ≤
      (l1 * p1 + l2 * p2) ^ 2 + (l1 * q1 + l2 * q2) ^ 2 := by
  have hexp : (l1 * p1 + l2 * p2) ^ 2 + (l1 * q1 + l2 * q2) ^ 2 =
      l1 ^ 2 * (p1 ^ 2 + q1 ^ 2) + l2 ^ 2 * (p2 ^ 2 + q2 ^ 2) +
        2 * (l1 * l2) * (p1 * p2 + q1 * q2) := by
    ring
  rw [hexp]
  set N1 := p1 ^ 2 + q1 ^ 2 with hN1def
  set N2 := p2 ^ 2 + q2 ^ 2 with hN2def
  set P := p1 * p2 + q1 * q2 with hPdef
  have hN1 : 0 ≤ N1 := by rw [hN1def]; positivity
  have hP := abs_le.mp hip
  have k1 : 0 ≤ (l1 - l2) ^ 2 * N1 := mul_nonneg (sq_nonneg _) hN1
  have k1' : 0 ≤ (l1 + l2) ^ 2 * N1 := mul_nonneg (sq_nonneg _) hN1
  have k2 : 0 ≤ l2 ^ 2 * (N2 - N1) := mul_nonneg (sq_nonneg _) (by linarith)
  rcases le_total 0 (l1 * l2) with h | h
  · have k3 : l1 * l2 * (-(N1 / 2)) ≤ l1 * l2 * P := mul_le_mul_of_nonneg_left hP.1 h
    nlinarith
  · have k3 : l1 * l2 * (N1 / 2) ≤ l1 * l2 * P := mul_le_mul_of_nonpos_left hP.2 h
    nlinarith

lemma unimod_coords (b1 b2 : ℤ × ℤ)
    (hdet : b1.1 * b2.2 - b1.2 * b2.1 = 1 ∨ b1.1 * b2.2 - b1.2 * b2.1 = -1) (z : ℤ × ℤ) :
    z.1 = ((b1.1 * b2.2 - b1.2 * b2.1) * (z.1 * b2.2 - z.2 * b2.1)) * b1.1 +
        ((b1.1 * b2.2 - b1.2 * b2.1) * (b1.1 * z.2 - b1.2 * z.1)) * b2.1 ∧
      z.2 = ((b1.1 * b2.2 - b1.2 * b2.1) * (z.1 * b2.2 - z.2 * b2.1)) * b1.2 +
        ((b1.1 * b2.2 - b1.2 * b2.1) * (b1.1 * z.2 - b1.2 * z.1)) * b2.2 := by
  have hsq : (b1.1 * b2.2 - b1.2 * b2.1) * (b1.1 * b2.2 - b1.2 * b2.1) = 1 := by
    rcases hdet with h | h <;> rw [h] <;> norm_num
  constructor
  · linear_combination (-z.1) * hsq
  · linear_combination (-z.2) * hsq

noncomputable def nsq (α ρ c : ℝ) (b : ℤ × ℤ) : ℝ :=
  (α * ((b.1 : ℝ) - ρ * (b.2 : ℝ))) ^ 2 + ((b.2 : ℝ) / c) ^ 2

noncomputable def ipT (α ρ c : ℝ) (b b' : ℤ × ℤ) : ℝ :=
  α * ((b.1 : ℝ) - ρ * (b.2 : ℝ)) * (α * ((b'.1 : ℝ) - ρ * (b'.2 : ℝ))) + (b.2 : ℝ) / c * ((b'.2 : ℝ) / c)

lemma nsq_nonneg (α ρ c : ℝ) (b : ℤ × ℤ) : 0 ≤ nsq α ρ c b := by unfold nsq; positivity

lemma nsq_pos (α ρ c : ℝ) (hα : 0 < α) (hc : 0 < c) (b : ℤ × ℤ) (hb : b ≠ 0) : 0 < nsq α ρ c b := by
  rcases (nsq_nonneg α ρ c b).lt_or_eq with h | h
  · exact h
  · exfalso
    apply hb
    unfold nsq at h
    have h2 : ((b.2 : ℝ) / c) ^ 2 = 0 := by
      nlinarith [sq_nonneg (α * ((b.1 : ℝ) - ρ * (b.2 : ℝ))), sq_nonneg ((b.2 : ℝ) / c)]
    have h1 : (α * ((b.1 : ℝ) - ρ * (b.2 : ℝ))) ^ 2 = 0 := by
      nlinarith [sq_nonneg (α * ((b.1 : ℝ) - ρ * (b.2 : ℝ))), sq_nonneg ((b.2 : ℝ) / c)]
    have e2 : (b.2 : ℝ) = 0 := by
      have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h2
      rcases div_eq_zero_iff.mp this with h' | h'
      · exact h'
      · exact absurd h' hc.ne'
    have e1 : (b.1 : ℝ) = 0 := by
      have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h1
      rw [e2, mul_zero, sub_zero] at this
      rcases mul_eq_zero.mp this with h' | h'
      · exact absurd h' hα.ne'
      · exact h'
    ext
    · exact_mod_cast e1
    · exact_mod_cast e2

lemma nsq_smul (α ρ c : ℝ) (k : ℤ) (b : ℤ × ℤ) :
    nsq α ρ c (k * b.1, k * b.2) = (k : ℝ) ^ 2 * nsq α ρ c b := by
  unfold nsq; push_cast; ring

lemma box_of_nsq (α ρ c R : ℝ) (hα : 0 < α) (hc : 0 < c) (b : ℤ × ℤ) (hb : nsq α ρ c b ≤ R) :
    |(b.1 : ℝ)| ≤ Real.sqrt R / α + |ρ| * (c * Real.sqrt R) ∧ |(b.2 : ℝ)| ≤ c * Real.sqrt R := by
  unfold nsq at hb
  have h2 : ((b.2 : ℝ) / c) ^ 2 ≤ R := by nlinarith [sq_nonneg (α * ((b.1 : ℝ) - ρ * (b.2 : ℝ)))]
  have h1 : (α * ((b.1 : ℝ) - ρ * (b.2 : ℝ))) ^ 2 ≤ R := by nlinarith [sq_nonneg ((b.2 : ℝ) / c)]
  have a2 : |(b.2 : ℝ) / c| ≤ Real.sqrt R := Real.abs_le_sqrt h2
  have a1 : |α * ((b.1 : ℝ) - ρ * (b.2 : ℝ))| ≤ Real.sqrt R := Real.abs_le_sqrt h1
  have b2 : |(b.2 : ℝ)| ≤ c * Real.sqrt R := by
    rw [abs_div, abs_of_pos hc, div_le_iff₀ hc] at a2; linarith
  refine ⟨?_, b2⟩
  have b1' : |(b.1 : ℝ) - ρ * (b.2 : ℝ)| ≤ Real.sqrt R / α := by
    rw [abs_mul, abs_of_pos hα] at a1
    rw [le_div_iff₀ hα]; linarith
  have : |(b.1 : ℝ)| ≤ |(b.1 : ℝ) - ρ * (b.2 : ℝ)| + |ρ * (b.2 : ℝ)| := by
    have := abs_add_le ((b.1 : ℝ) - ρ * (b.2 : ℝ)) (ρ * (b.2 : ℝ))
    simpa using this
  rw [abs_mul] at this
  have : |ρ| * |(b.2 : ℝ)| ≤ |ρ| * (c * Real.sqrt R) := mul_le_mul_of_nonneg_left b2 (abs_nonneg ρ)
  linarith

lemma exists_shortest (α ρ c : ℝ) (hα : 0 < α) (hc : 0 < c) :
    ∃ b1 : ℤ × ℤ, b1 ≠ 0 ∧ ∀ b : ℤ × ℤ, b ≠ 0 → nsq α ρ c b1 ≤ nsq α ρ c b := by
  classical
  set R := nsq α ρ c (1, 0) with hR
  set B1 : ℕ := ⌈Real.sqrt R / α + |ρ| * (c * Real.sqrt R)⌉₊ with hB1
  set B2 : ℕ := ⌈c * Real.sqrt R⌉₊ with hB2
  set F : Finset (ℤ × ℤ) := ((Finset.Icc (-(B1 : ℤ)) B1) ×ˢ (Finset.Icc (-(B2 : ℤ)) B2)).filter
    (fun b => b ≠ 0 ∧ nsq α ρ c b ≤ R) with hF
  have hmem : ∀ b : ℤ × ℤ, b ≠ 0 → nsq α ρ c b ≤ R → b ∈ F := by
    intro b hb0 hbR
    obtain ⟨k1, k2⟩ := box_of_nsq α ρ c R hα hc b hbR
    have l1 : |(b.1 : ℝ)| ≤ (B1 : ℝ) := le_trans k1 (Nat.le_ceil _)
    have l2 : |(b.2 : ℝ)| ≤ (B2 : ℝ) := le_trans k2 (Nat.le_ceil _)
    have l1' : |b.1| ≤ (B1 : ℤ) := by
      have : ((|b.1| : ℤ) : ℝ) ≤ ((B1 : ℤ) : ℝ) := by push_cast; exact l1
      exact_mod_cast this
    have l2' : |b.2| ≤ (B2 : ℤ) := by
      have : ((|b.2| : ℤ) : ℝ) ≤ ((B2 : ℤ) : ℝ) := by push_cast; exact l2
      exact_mod_cast this
    rw [hF, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
    exact ⟨⟨abs_le.mp l1', abs_le.mp l2'⟩, hb0, hbR⟩
  have hne : F.Nonempty := ⟨(1, 0), hmem (1, 0) (by simp) le_rfl⟩
  obtain ⟨b1, hb1F, hb1min⟩ := F.exists_min_image (nsq α ρ c) hne
  have hb1 := (Finset.mem_filter.mp hb1F).2
  refine ⟨b1, hb1.1, ?_⟩
  intro b hb
  by_cases hbR : nsq α ρ c b ≤ R
  · exact hb1min b (hmem b hb hbR)
  · push Not at hbR; linarith [hb1.2]

theorem exists_reduced (α ρ c : ℝ) (hα : 0 < α) (hc : 0 < c) :
    ∃ b1 b2 : ℤ × ℤ, (b1.1 * b2.2 - b1.2 * b2.1 = 1 ∨ b1.1 * b2.2 - b1.2 * b2.1 = -1) ∧
      Real.sqrt (nsq α ρ c b1) ≤ Real.sqrt (nsq α ρ c b2) ∧
      |ipT α ρ c b1 b2| ≤ nsq α ρ c b1 / 2 := by
  obtain ⟨b1, hb10, hmin⟩ := exists_shortest α ρ c hα hc
  have hN1 : 0 < nsq α ρ c b1 := nsq_pos α ρ c hα hc b1 hb10
  have hprim : Int.gcd b1.1 b1.2 = 1 := by
    by_contra hg
    set g := Int.gcd b1.1 b1.2 with hgdef
    have hg0 : g ≠ 0 := by
      intro h0
      apply hb10
      have := Int.gcd_eq_zero_iff.mp h0
      ext
      · exact this.1
      · exact this.2
    have hg2 : 2 ≤ g := by omega
    obtain ⟨p, hp⟩ : (g : ℤ) ∣ b1.1 := Int.gcd_dvd_left ..
    obtain ⟨q, hq⟩ : (g : ℤ) ∣ b1.2 := Int.gcd_dvd_right ..
    have hpq0 : (p, q) ≠ (0 : ℤ × ℤ) := by
      intro h0
      apply hb10
      simp only [Prod.mk_eq_zero] at h0
      ext
      · simp [hp, h0.1]
      · simp [hq, h0.2]
    have hscale : nsq α ρ c b1 = ((g : ℤ) : ℝ) ^ 2 * nsq α ρ c (p, q) := by
      have : b1 = ((g : ℤ) * (p, q).1, (g : ℤ) * (p, q).2) := by
        ext
        · exact hp
        · exact hq
      rw [this, nsq_smul]
    have hpos := nsq_pos α ρ c hα hc (p, q) hpq0
    have hge := hmin (p, q) hpq0
    have hg2R : (4 : ℝ) ≤ ((g : ℤ) : ℝ) ^ 2 := by
      have : (2 : ℝ) ≤ ((g : ℤ) : ℝ) := by exact_mod_cast hg2
      nlinarith
    have k := mul_le_mul_of_nonneg_right hg2R hpos.le
    linarith
  have hbez : b1.1 * Int.gcdA b1.1 b1.2 + b1.2 * Int.gcdB b1.1 b1.2 = 1 := by
    have := Int.gcd_eq_gcd_ab b1.1 b1.2
    rw [hprim, Nat.cast_one] at this
    exact this.symm
  set w : ℤ × ℤ := (-Int.gcdB b1.1 b1.2, Int.gcdA b1.1 b1.2) with hw
  have hdetw : b1.1 * w.2 - b1.2 * w.1 = 1 := by
    rw [hw]; linear_combination hbez
  set k : ℤ := round (ipT α ρ c b1 w / nsq α ρ c b1) with hk
  set b2 : ℤ × ℤ := (w.1 - k * b1.1, w.2 - k * b1.2) with hb2
  have hdet : b1.1 * b2.2 - b1.2 * b2.1 = 1 := by
    rw [hb2]; linear_combination hdetw
  have hb20 : b2 ≠ 0 := by
    intro h0
    rw [h0] at hdet
    simp at hdet
  have hip : ipT α ρ c b1 b2 = ipT α ρ c b1 w - (k : ℝ) * nsq α ρ c b1 := by
    rw [hb2]; unfold ipT nsq; push_cast; ring
  refine ⟨b1, b2, Or.inl hdet, Real.sqrt_le_sqrt (hmin b2 hb20), ?_⟩
  rw [hip]
  have hr := abs_sub_round (ipT α ρ c b1 w / nsq α ρ c b1)
  rw [← hk] at hr
  have e : ipT α ρ c b1 w - (k : ℝ) * nsq α ρ c b1 =
      (ipT α ρ c b1 w / nsq α ρ c b1 - (k : ℝ)) * nsq α ρ c b1 := by
    rw [sub_mul, div_mul_cancel₀ _ hN1.ne']
  rw [e, abs_mul, abs_of_pos hN1]
  have := mul_le_mul_of_nonneg_right hr hN1.le
  linarith

set_option maxHeartbeats 2000000 in
theorem side (α ρ c B : ℝ) (hα : 0 < α) (hc : 0 < c) (hB : α * B = 1) (b1 b2 : ℤ × ℤ)
    (hdet : b1.1 * b2.2 - b1.2 * b2.1 = 1 ∨ b1.1 * b2.2 - b1.2 * b2.1 = -1)
    (hle : Real.sqrt (nsq α ρ c b1) ≤ Real.sqrt (nsq α ρ c b2))
    (hip : |α * ((b1.1 : ℝ) - ρ * (b1.2 : ℝ)) * (α * ((b2.1 : ℝ) - ρ * (b2.2 : ℝ))) +
        (b1.2 : ℝ) / c * ((b2.2 : ℝ) / c)| ≤ nsq α ρ c b1 / 2) :
    2 / Real.sqrt (nsq α ρ c b2) ≤ 2 / Real.sqrt (nsq α ρ c b1) ∧
    (∀ A : ℝ, 0 ≤ A → A ^ 2 ≤ 12 →
      A * (c / α) ≤ 2 / Real.sqrt (nsq α ρ c b1) * (2 / Real.sqrt (nsq α ρ c b2))) ∧
    2 / Real.sqrt (nsq α ρ c b1) * (2 / Real.sqrt (nsq α ρ c b2)) ≤ 4 * (c / α) ∧
    (∀ A : ℝ, 0 ≤ A → A ^ 2 ≤ 12 → Real.sqrt (A * (c / α)) ≤ 2 / Real.sqrt (nsq α ρ c b1)) ∧
    (∀ z : ℤ × ℤ, |(z.1 : ℝ) - ρ * (z.2 : ℝ)| ≤ B → |(z.2 : ℝ)| ≤ c →
      ∃ l : ℤ × ℤ, z.1 = l.1 * b1.1 + l.2 * b2.1 ∧ z.2 = l.1 * b1.2 + l.2 * b2.2 ∧
        |(l.1 : ℝ)| ≤ 2 / Real.sqrt (nsq α ρ c b1) ∧ |(l.2 : ℝ)| ≤ 2 / Real.sqrt (nsq α ρ c b2)) := by
  have hcne : c ≠ 0 := hc.ne'
  have hαne : α ≠ 0 := hα.ne'
  set p1 := α * ((b1.1 : ℝ) - ρ * (b1.2 : ℝ)) with hp1
  set q1 := (b1.2 : ℝ) / c with hq1
  set p2 := α * ((b2.1 : ℝ) - ρ * (b2.2 : ℝ)) with hp2
  set q2 := (b2.2 : ℝ) / c with hq2
  have hN1e : nsq α ρ c b1 = p1 ^ 2 + q1 ^ 2 := rfl
  have hN2e : nsq α ρ c b2 = p2 ^ 2 + q2 ^ 2 := rfl
  rw [hN1e, hN2e] at hle ⊢
  rw [hN1e] at hip
  have hN10 : 0 ≤ p1 ^ 2 + q1 ^ 2 := by positivity
  have hN20 : 0 ≤ p2 ^ 2 + q2 ^ 2 := by positivity
  have hle' : p1 ^ 2 + q1 ^ 2 ≤ p2 ^ 2 + q2 ^ 2 := by
    have := pow_le_pow_left₀ (Real.sqrt_nonneg _) hle 2
    rwa [Real.sq_sqrt hN10, Real.sq_sqrt hN20] at this
  have hΔ0 : 0 < α / c := div_pos hα hc
  have hdetR : (((b1.1 : ℤ) : ℝ) * ((b2.2 : ℤ) : ℝ) - ((b1.2 : ℤ) : ℝ) * ((b2.1 : ℤ) : ℝ)) ^ 2 = 1 := by
    rcases hdet with h | h
    · have := congrArg (fun t : ℤ => (t : ℝ)) h
      push_cast at this
      rw [this]; norm_num
    · have := congrArg (fun t : ℤ => (t : ℝ)) h
      push_cast at this
      rw [this]; norm_num
  have hΔ : (p1 * q2 - q1 * p2) ^ 2 = (α / c) ^ 2 := by
    have e : p1 * q2 - q1 * p2 =
        (α / c) * (((b1.1 : ℤ) : ℝ) * ((b2.2 : ℤ) : ℝ) - ((b1.2 : ℤ) : ℝ) * ((b2.1 : ℤ) : ℝ)) := by
      rw [hp1, hq1, hp2, hq2]; field_simp; ring
    rw [e, mul_pow, hdetR, mul_one]
  obtain ⟨hlo, hhi⟩ := gram_bounds p1 q1 p2 q2 (α / c) hΔ hle' hip
  have hcl0 : ∀ l1 l2 : ℝ, (l1 ^ 2 * (p1 ^ 2 + q1 ^ 2) + l2 ^ 2 * (p2 ^ 2 + q2 ^ 2)) / 2 ≤
      (l1 * p1 + l2 * p2) ^ 2 + (l1 * q1 + l2 * q2) ^ 2 :=
    fun l1 l2 => coord_lower p1 q1 p2 q2 l1 l2 hle' hip
  generalize hN1g : p1 ^ 2 + q1 ^ 2 = N1 at hN10 hle' hlo hhi hle hcl0 ⊢
  generalize hN2g : p2 ^ 2 + q2 ^ 2 = N2 at hN20 hle' hlo hhi hle hcl0 ⊢
  generalize hΔg : α / c = Δ at hΔ0 hlo hhi
  have hN1p : 0 < N1 := by
    rcases lt_or_eq_of_le hN10 with h | h
    · exact h
    · exfalso
      rw [← h, zero_mul] at hlo
      have := pow_pos hΔ0 2
      linarith
  have hN2p : 0 < N2 := lt_of_lt_of_le hN1p hle'
  have s1 : 0 < Real.sqrt N1 := Real.sqrt_pos.mpr hN1p
  have s2 : 0 < Real.sqrt N2 := Real.sqrt_pos.mpr hN2p
  have sq1 : Real.sqrt N1 ^ 2 = N1 := Real.sq_sqrt hN10
  have sq2 : Real.sqrt N2 ^ 2 = N2 := Real.sq_sqrt hN20
  have hprod : 2 / Real.sqrt N1 * (2 / Real.sqrt N2) = 4 / (Real.sqrt N1 * Real.sqrt N2) := by
    rw [div_mul_div_comm]; norm_num
  have hS2 : (Real.sqrt N1 * Real.sqrt N2) ^ 2 = N1 * N2 := by rw [mul_pow, sq1, sq2]
  have hS0 : 0 < Real.sqrt N1 * Real.sqrt N2 := mul_pos s1 s2
  have hcα : c / α = 1 / Δ := by rw [← hΔg]; field_simp
  have hND : N1 * N2 / Δ ^ 2 ≤ 4 / 3 := by
    rw [div_le_iff₀ (by positivity)]; linarith
  have hN1sq : N1 ^ 2 ≤ N1 * N2 := by rw [sq]; exact mul_le_mul_of_nonneg_left hle' hN10
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact div_le_div_of_nonneg_left (by norm_num) s1 hle
  · intro A hA hA2
    rw [hprod, hcα, le_div_iff₀ hS0]
    have hX2 : (A * (1 / Δ) * (Real.sqrt N1 * Real.sqrt N2)) ^ 2 ≤ 4 ^ 2 := by
      have e : (A * (1 / Δ) * (Real.sqrt N1 * Real.sqrt N2)) ^ 2 =
          A ^ 2 * ((Real.sqrt N1 * Real.sqrt N2) ^ 2 / Δ ^ 2) := by ring
      rw [e, hS2]
      calc A ^ 2 * (N1 * N2 / Δ ^ 2) ≤ A ^ 2 * (4 / 3) := mul_le_mul_of_nonneg_left hND (sq_nonneg A)
        _ ≤ 4 ^ 2 := by nlinarith
    have hpos : 0 ≤ A * (1 / Δ) * (Real.sqrt N1 * Real.sqrt N2) := by
      have : 0 ≤ 1 / Δ := by positivity
      exact mul_nonneg (mul_nonneg hA this) hS0.le
    exact le_of_sq_le_sq_nn _ _ hpos (by norm_num) hX2
  · rw [hprod, hcα, div_le_iff₀ hS0]
    have hS : Δ ≤ Real.sqrt N1 * Real.sqrt N2 := by
      apply le_of_sq_le_sq_nn _ _ hΔ0.le hS0.le
      rw [hS2]; exact hlo
    have h4 : 4 * (1 / Δ) * Δ = 4 := by field_simp
    calc (4 : ℝ) = 4 * (1 / Δ) * Δ := h4.symm
      _ ≤ 4 * (1 / Δ) * (Real.sqrt N1 * Real.sqrt N2) :=
          mul_le_mul_of_nonneg_left hS (by positivity)
  · intro A hA hA2
    have hL : 0 ≤ 2 / Real.sqrt N1 := by positivity
    rw [show 2 / Real.sqrt N1 = Real.sqrt ((2 / Real.sqrt N1) ^ 2) from (Real.sqrt_sq hL).symm]
    apply Real.sqrt_le_sqrt
    rw [div_pow, sq1, hcα, le_div_iff₀ hN1p]
    have hX2 : (A * (1 / Δ) * N1) ^ 2 ≤ (2 ^ 2) ^ 2 := by
      have e : (A * (1 / Δ) * N1) ^ 2 = A ^ 2 * (N1 ^ 2 / Δ ^ 2) := by ring
      have h1 : N1 ^ 2 / Δ ^ 2 ≤ N1 * N2 / Δ ^ 2 :=
        div_le_div_of_nonneg_right hN1sq (by positivity)
      rw [e]
      calc A ^ 2 * (N1 ^ 2 / Δ ^ 2) ≤ A ^ 2 * (4 / 3) :=
            mul_le_mul_of_nonneg_left (le_trans h1 hND) (sq_nonneg A)
        _ ≤ (2 ^ 2) ^ 2 := by nlinarith
    have hpos : 0 ≤ A * (1 / Δ) * N1 := by
      have : 0 ≤ 1 / Δ := by positivity
      exact mul_nonneg (mul_nonneg hA this) hN10
    exact le_of_sq_le_sq_nn _ _ hpos (by norm_num) hX2
  · intro z hz1 hz2
    obtain ⟨e1, e2⟩ := unimod_coords b1 b2 hdet z
    set l1 := (b1.1 * b2.2 - b1.2 * b2.1) * (z.1 * b2.2 - z.2 * b2.1) with hl1
    set l2 := (b1.1 * b2.2 - b1.2 * b2.1) * (b1.1 * z.2 - b1.2 * z.1) with hl2
    refine ⟨(l1, l2), e1, e2, ?_⟩
    have e1R : (z.1 : ℝ) = (l1 : ℝ) * (b1.1 : ℝ) + (l2 : ℝ) * (b2.1 : ℝ) := by
      have := congrArg (fun t : ℤ => (t : ℝ)) e1; push_cast at this; exact this
    have e2R : (z.2 : ℝ) = (l1 : ℝ) * (b1.2 : ℝ) + (l2 : ℝ) * (b2.2 : ℝ) := by
      have := congrArg (fun t : ℤ => (t : ℝ)) e2; push_cast at this; exact this
    have T1 : α * ((z.1 : ℝ) - ρ * (z.2 : ℝ)) = (l1 : ℝ) * p1 + (l2 : ℝ) * p2 := by
      rw [e1R, e2R, hp1, hp2]; ring
    have T2 : (z.2 : ℝ) / c = (l1 : ℝ) * q1 + (l2 : ℝ) * q2 := by
      rw [e2R, hq1, hq2]; field_simp
    have hb1 : |α * ((z.1 : ℝ) - ρ * (z.2 : ℝ))| ≤ 1 := by
      rw [abs_mul, abs_of_pos hα, ← hB]
      exact mul_le_mul_of_nonneg_left hz1 hα.le
    have hb2 : |(z.2 : ℝ) / c| ≤ 1 := by
      rw [abs_div, abs_of_pos hc, div_le_one hc]; exact hz2
    have a1 : (α * ((z.1 : ℝ) - ρ * (z.2 : ℝ))) ^ 2 ≤ 1 := by
      rw [← sq_abs]; nlinarith [abs_nonneg (α * ((z.1 : ℝ) - ρ * (z.2 : ℝ)))]
    have a2 : ((z.2 : ℝ) / c) ^ 2 ≤ 1 := by
      rw [← sq_abs]; nlinarith [abs_nonneg ((z.2 : ℝ) / c)]
    rw [T1] at a1
    rw [T2] at a2
    have hcl := hcl0 (l1 : ℝ) (l2 : ℝ)
    have k1 : 0 ≤ (l2 : ℝ) ^ 2 * N2 := mul_nonneg (sq_nonneg _) hN20
    have k2 : 0 ≤ (l1 : ℝ) ^ 2 * N1 := mul_nonneg (sq_nonneg _) hN10
    have hl1N : (l1 : ℝ) ^ 2 * N1 ≤ 4 := by linarith
    have hl2N : (l2 : ℝ) ^ 2 * N2 ≤ 4 := by linarith
    constructor
    · show |((l1 : ℤ) : ℝ)| ≤ 2 / Real.sqrt N1
      rw [le_div_iff₀ s1]
      apply le_of_sq_le_sq_nn _ _ (by positivity) (by norm_num)
      rw [mul_pow, sq_abs, sq1]; linarith
    · show |((l2 : ℤ) : ℝ)| ≤ 2 / Real.sqrt N2
      rw [le_div_iff₀ s2]
      apply le_of_sq_le_sq_nn _ _ (by positivity) (by norm_num)
      rw [mul_pow, sq_abs, sq2]; linarith

lemma unimod_unique (b1 b2 : ℤ × ℤ)
    (hdet : b1.1 * b2.2 - b1.2 * b2.1 = 1 ∨ b1.1 * b2.2 - b1.2 * b2.1 = -1) (z : ℤ × ℤ) :
    ∃! l : ℤ × ℤ, z.1 = l.1 * b1.1 + l.2 * b2.1 ∧ z.2 = l.1 * b1.2 + l.2 * b2.2 := by
  obtain ⟨h1, h2⟩ := unimod_coords b1 b2 hdet z
  refine ⟨((b1.1 * b2.2 - b1.2 * b2.1) * (z.1 * b2.2 - z.2 * b2.1),
    (b1.1 * b2.2 - b1.2 * b2.1) * (b1.1 * z.2 - b1.2 * z.1)), ⟨h1, h2⟩, ?_⟩
  rintro ⟨m1, m2⟩ ⟨k1, k2⟩
  have hsq : (b1.1 * b2.2 - b1.2 * b2.1) * (b1.1 * b2.2 - b1.2 * b2.1) = 1 := by
    rcases hdet with h | h <;> rw [h] <;> norm_num
  have k1' : z.1 = m1 * b1.1 + m2 * b2.1 := k1
  have k2' : z.2 = m1 * b1.2 + m2 * b2.2 := k2
  have f1 : m1 = (b1.1 * b2.2 - b1.2 * b2.1) * (z.1 * b2.2 - z.2 * b2.1) := by
    rw [k1', k2']
    linear_combination (-m1) * hsq
  have f2 : m2 = (b1.1 * b2.2 - b1.2 * b2.1) * (b1.1 * z.2 - b1.2 * z.1) := by
    rw [k1', k2']
    linear_combination (-m2) * hsq
  rw [f1, f2]

lemma unimod_gcd (b1 b2 : ℤ × ℤ)
    (hdet : b1.1 * b2.2 - b1.2 * b2.1 = 1 ∨ b1.1 * b2.2 - b1.2 * b2.1 = -1) (l : ℤ × ℤ) :
    Int.gcd (l.1 * b1.1 + l.2 * b2.1) (l.1 * b1.2 + l.2 * b2.2) = Int.gcd l.1 l.2 := by
  have hsq : (b1.1 * b2.2 - b1.2 * b2.1) * (b1.1 * b2.2 - b1.2 * b2.1) = 1 := by
    rcases hdet with h | h <;> rw [h] <;> norm_num
  have hl1 : l.1 = (b1.1 * b2.2 - b1.2 * b2.1) *
      ((l.1 * b1.1 + l.2 * b2.1) * b2.2 - (l.1 * b1.2 + l.2 * b2.2) * b2.1) := by
    linear_combination (-l.1) * hsq
  have hl2 : l.2 = (b1.1 * b2.2 - b1.2 * b2.1) *
      (b1.1 * (l.1 * b1.2 + l.2 * b2.2) - b1.2 * (l.1 * b1.1 + l.2 * b2.1)) := by
    linear_combination (-l.2) * hsq
  set z1 := l.1 * b1.1 + l.2 * b2.1 with hz1
  set z2 := l.1 * b1.2 + l.2 * b2.2 with hz2
  have d1 : ((Int.gcd l.1 l.2 : ℕ) : ℤ) ∣ l.1 := Int.gcd_dvd_left ..
  have d2 : ((Int.gcd l.1 l.2 : ℕ) : ℤ) ∣ l.2 := Int.gcd_dvd_right ..
  have d3 : ((Int.gcd z1 z2 : ℕ) : ℤ) ∣ z1 := Int.gcd_dvd_left ..
  have d4 : ((Int.gcd z1 z2 : ℕ) : ℤ) ∣ z2 := Int.gcd_dvd_right ..
  have g1 : Int.gcd l.1 l.2 ∣ Int.gcd z1 z2 := by
    show Int.gcd l.1 l.2 ∣ Nat.gcd z1.natAbs z2.natAbs
    apply Nat.dvd_gcd
    · apply Int.natCast_dvd.mp
      rw [hz1]
      exact dvd_add (dvd_mul_of_dvd_left d1 _) (dvd_mul_of_dvd_left d2 _)
    · apply Int.natCast_dvd.mp
      rw [hz2]
      exact dvd_add (dvd_mul_of_dvd_left d1 _) (dvd_mul_of_dvd_left d2 _)
  have g2 : Int.gcd z1 z2 ∣ Int.gcd l.1 l.2 := by
    show Int.gcd z1 z2 ∣ Nat.gcd l.1.natAbs l.2.natAbs
    apply Nat.dvd_gcd
    · apply Int.natCast_dvd.mp
      rw [hl1]
      exact dvd_mul_of_dvd_right (dvd_sub (dvd_mul_of_dvd_left d3 _) (dvd_mul_of_dvd_left d4 _)) _
    · apply Int.natCast_dvd.mp
      rw [hl2]
      exact dvd_mul_of_dvd_right (dvd_sub (dvd_mul_of_dvd_right d4 _) (dvd_mul_of_dvd_right d3 _)) _
  exact Nat.dvd_antisymm g2 g1

lemma sqrt_const_mul (k t : ℝ) (hk : 0 ≤ k) : Real.sqrt (k ^ 2 * t) = k * Real.sqrt t := by
  rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hk]

end PcPellRed

set_option maxHeartbeats 4000000 in
theorem JocelynClaims.claim_cc8735567a5fed524cde1b554d578ea3fe6e246fab4b3b5b936e3bca5256f8f8 : ∀ (D E x M ρ0 : ℝ), 1 / 2 ≤ D → 1 / 2 ≤ E → 1 < x → 1 ≤ M →
    D / (2 * E) ≤ ρ0 → ρ0 ≤ 2 * D / E →
  (∀ h : ℤ, 3 * |(h : ℝ)| * M ≤ x →
    ∀ d e u v : ℕ, D < (d : ℝ) → (d : ℝ) ≤ 2 * D → E < (e : ℝ) → (e : ℝ) ≤ 2 * E →
      x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ) < (u : ℝ) → (u : ℝ) < 2 * (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)) →
      x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ) < (v : ℝ) → (v : ℝ) < 2 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ)) →
      (e : ℤ) ^ 3 * (v : ℤ) ^ 2 - (d : ℤ) ^ 3 * (u : ℤ) ^ 2 = h →
      ρ0 < (d : ℝ) / (e : ℝ) → (d : ℝ) / (e : ℝ) ≤ ρ0 * (1 + 1 / M) →
        0 < (d : ℝ) - ρ0 * (e : ℝ) ∧ (d : ℝ) - ρ0 * (e : ℝ) ≤ 4 * D / M ∧
        |(v : ℝ) - ρ0 ^ (3 / 2 : ℝ) * (u : ℝ)| ≤ 17 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ)) / M) ∧
  (∀ h : ℤ, 9 * (h : ℝ) ^ 2 ≤ x → M ≤ x ^ (1 / 2 : ℝ) → 3 * |(h : ℝ)| * M ≤ x) ∧
  (∃ b1 b2 : ℤ × ℤ, (b1.1 * b2.2 - b1.2 * b2.1 = 1 ∨ b1.1 * b2.2 - b1.2 * b2.1 = -1) ∧
    Real.sqrt ((M / (4 * D) * ((b1.1 : ℝ) - ρ0 * (b1.2 : ℝ))) ^ 2 + ((b1.2 : ℝ) / (2 * E)) ^ 2) ≤
      Real.sqrt ((M / (4 * D) * ((b2.1 : ℝ) - ρ0 * (b2.2 : ℝ))) ^ 2 + ((b2.2 : ℝ) / (2 * E)) ^ 2) ∧
    |M / (4 * D) * ((b1.1 : ℝ) - ρ0 * (b1.2 : ℝ)) * (M / (4 * D) * ((b2.1 : ℝ) - ρ0 * (b2.2 : ℝ))) +
        (b1.2 : ℝ) / (2 * E) * ((b2.2 : ℝ) / (2 * E))| ≤
      ((M / (4 * D) * ((b1.1 : ℝ) - ρ0 * (b1.2 : ℝ))) ^ 2 + ((b1.2 : ℝ) / (2 * E)) ^ 2) / 2) ∧
  (∀ b1 b2 : ℤ × ℤ, (b1.1 * b2.2 - b1.2 * b2.1 = 1 ∨ b1.1 * b2.2 - b1.2 * b2.1 = -1) →
    Real.sqrt ((M / (4 * D) * ((b1.1 : ℝ) - ρ0 * (b1.2 : ℝ))) ^ 2 + ((b1.2 : ℝ) / (2 * E)) ^ 2) ≤
      Real.sqrt ((M / (4 * D) * ((b2.1 : ℝ) - ρ0 * (b2.2 : ℝ))) ^ 2 + ((b2.2 : ℝ) / (2 * E)) ^ 2) →
    |M / (4 * D) * ((b1.1 : ℝ) - ρ0 * (b1.2 : ℝ)) * (M / (4 * D) * ((b2.1 : ℝ) - ρ0 * (b2.2 : ℝ))) +
        (b1.2 : ℝ) / (2 * E) * ((b2.2 : ℝ) / (2 * E))| ≤
      ((M / (4 * D) * ((b1.1 : ℝ) - ρ0 * (b1.2 : ℝ))) ^ 2 + ((b1.2 : ℝ) / (2 * E)) ^ 2) / 2 →
    2 / Real.sqrt ((M / (4 * D) * ((b2.1 : ℝ) - ρ0 * (b2.2 : ℝ))) ^ 2 + ((b2.2 : ℝ) / (2 * E)) ^ 2) ≤
      2 / Real.sqrt ((M / (4 * D) * ((b1.1 : ℝ) - ρ0 * (b1.2 : ℝ))) ^ 2 + ((b1.2 : ℝ) / (2 * E)) ^ 2) ∧
    27 * (D * E / M) ≤
      2 / Real.sqrt ((M / (4 * D) * ((b1.1 : ℝ) - ρ0 * (b1.2 : ℝ))) ^ 2 + ((b1.2 : ℝ) / (2 * E)) ^ 2) *
      (2 / Real.sqrt ((M / (4 * D) * ((b2.1 : ℝ) - ρ0 * (b2.2 : ℝ))) ^ 2 + ((b2.2 : ℝ) / (2 * E)) ^ 2)) ∧
    2 / Real.sqrt ((M / (4 * D) * ((b1.1 : ℝ) - ρ0 * (b1.2 : ℝ))) ^ 2 + ((b1.2 : ℝ) / (2 * E)) ^ 2) *
      (2 / Real.sqrt ((M / (4 * D) * ((b2.1 : ℝ) - ρ0 * (b2.2 : ℝ))) ^ 2 + ((b2.2 : ℝ) / (2 * E)) ^ 2)) ≤
      32 * (D * E / M) ∧
    5 * Real.sqrt (D * E / M) ≤
      2 / Real.sqrt ((M / (4 * D) * ((b1.1 : ℝ) - ρ0 * (b1.2 : ℝ))) ^ 2 + ((b1.2 : ℝ) / (2 * E)) ^ 2) ∧
    (∀ d' e' : ℤ, |(d' : ℝ) - ρ0 * (e' : ℝ)| ≤ 4 * D / M → |(e' : ℝ)| ≤ 2 * E →
      ∃ l : ℤ × ℤ, d' = l.1 * b1.1 + l.2 * b2.1 ∧ e' = l.1 * b1.2 + l.2 * b2.2 ∧
        |(l.1 : ℝ)| ≤ 2 / Real.sqrt ((M / (4 * D) * ((b1.1 : ℝ) - ρ0 * (b1.2 : ℝ))) ^ 2 +
          ((b1.2 : ℝ) / (2 * E)) ^ 2) ∧
        |(l.2 : ℝ)| ≤ 2 / Real.sqrt ((M / (4 * D) * ((b2.1 : ℝ) - ρ0 * (b2.2 : ℝ))) ^ 2 +
          ((b2.2 : ℝ) / (2 * E)) ^ 2)) ∧
    (∀ z : ℤ × ℤ, ∃! l : ℤ × ℤ, z.1 = l.1 * b1.1 + l.2 * b2.1 ∧ z.2 = l.1 * b1.2 + l.2 * b2.2) ∧
    (∀ l : ℤ × ℤ, Int.gcd (l.1 * b1.1 + l.2 * b2.1) (l.1 * b1.2 + l.2 * b2.2) = Int.gcd l.1 l.2)) ∧
  (∃ c1 c2 : ℤ × ℤ, (c1.1 * c2.2 - c1.2 * c2.1 = 1 ∨ c1.1 * c2.2 - c1.2 * c2.1 = -1) ∧
    Real.sqrt ((M / (17 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ))) * ((c1.1 : ℝ) - ρ0 ^ (3 / 2 : ℝ) * (c1.2 : ℝ))) ^ 2 +
        ((c1.2 : ℝ) / (2 * (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)))) ^ 2) ≤
      Real.sqrt ((M / (17 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ))) * ((c2.1 : ℝ) - ρ0 ^ (3 / 2 : ℝ) * (c2.2 : ℝ))) ^ 2 +
        ((c2.2 : ℝ) / (2 * (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)))) ^ 2) ∧
    |M / (17 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ))) * ((c1.1 : ℝ) - ρ0 ^ (3 / 2 : ℝ) * (c1.2 : ℝ)) *
        (M / (17 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ))) * ((c2.1 : ℝ) - ρ0 ^ (3 / 2 : ℝ) * (c2.2 : ℝ))) +
        (c1.2 : ℝ) / (2 * (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ))) *
          ((c2.2 : ℝ) / (2 * (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ))))| ≤
      ((M / (17 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ))) * ((c1.1 : ℝ) - ρ0 ^ (3 / 2 : ℝ) * (c1.2 : ℝ))) ^ 2 +
        ((c1.2 : ℝ) / (2 * (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)))) ^ 2) / 2) ∧
  (∀ c1 c2 : ℤ × ℤ, (c1.1 * c2.2 - c1.2 * c2.1 = 1 ∨ c1.1 * c2.2 - c1.2 * c2.1 = -1) →
    Real.sqrt ((M / (17 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ))) * ((c1.1 : ℝ) - ρ0 ^ (3 / 2 : ℝ) * (c1.2 : ℝ))) ^ 2 +
        ((c1.2 : ℝ) / (2 * (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)))) ^ 2) ≤
      Real.sqrt ((M / (17 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ))) * ((c2.1 : ℝ) - ρ0 ^ (3 / 2 : ℝ) * (c2.2 : ℝ))) ^ 2 +
        ((c2.2 : ℝ) / (2 * (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)))) ^ 2) →
    |M / (17 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ))) * ((c1.1 : ℝ) - ρ0 ^ (3 / 2 : ℝ) * (c1.2 : ℝ)) *
        (M / (17 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ))) * ((c2.1 : ℝ) - ρ0 ^ (3 / 2 : ℝ) * (c2.2 : ℝ))) +
        (c1.2 : ℝ) / (2 * (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ))) *
          ((c2.2 : ℝ) / (2 * (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ))))| ≤
      ((M / (17 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ))) * ((c1.1 : ℝ) - ρ0 ^ (3 / 2 : ℝ) * (c1.2 : ℝ))) ^ 2 +
        ((c1.2 : ℝ) / (2 * (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)))) ^ 2) / 2 →
    2 / Real.sqrt ((M / (17 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ))) * ((c2.1 : ℝ) - ρ0 ^ (3 / 2 : ℝ) * (c2.2 : ℝ))) ^ 2 +
        ((c2.2 : ℝ) / (2 * (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)))) ^ 2) ≤
      2 / Real.sqrt ((M / (17 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ))) * ((c1.1 : ℝ) - ρ0 ^ (3 / 2 : ℝ) * (c1.2 : ℝ))) ^ 2 +
        ((c1.2 : ℝ) / (2 * (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)))) ^ 2) ∧
    117 * ((x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)) * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ)) / M) ≤
      2 / Real.sqrt ((M / (17 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ))) * ((c1.1 : ℝ) - ρ0 ^ (3 / 2 : ℝ) * (c1.2 : ℝ))) ^ 2 +
        ((c1.2 : ℝ) / (2 * (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)))) ^ 2) *
      (2 / Real.sqrt ((M / (17 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ))) * ((c2.1 : ℝ) - ρ0 ^ (3 / 2 : ℝ) * (c2.2 : ℝ))) ^ 2 +
        ((c2.2 : ℝ) / (2 * (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)))) ^ 2)) ∧
    2 / Real.sqrt ((M / (17 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ))) * ((c1.1 : ℝ) - ρ0 ^ (3 / 2 : ℝ) * (c1.2 : ℝ))) ^ 2 +
        ((c1.2 : ℝ) / (2 * (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)))) ^ 2) *
      (2 / Real.sqrt ((M / (17 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ))) * ((c2.1 : ℝ) - ρ0 ^ (3 / 2 : ℝ) * (c2.2 : ℝ))) ^ 2 +
        ((c2.2 : ℝ) / (2 * (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)))) ^ 2)) ≤
      136 * ((x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)) * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ)) / M) ∧
    10 * Real.sqrt ((x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)) * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ)) / M) ≤
      2 / Real.sqrt ((M / (17 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ))) * ((c1.1 : ℝ) - ρ0 ^ (3 / 2 : ℝ) * (c1.2 : ℝ))) ^ 2 +
        ((c1.2 : ℝ) / (2 * (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)))) ^ 2) ∧
    (∀ v' u' : ℤ, |(v' : ℝ) - ρ0 ^ (3 / 2 : ℝ) * (u' : ℝ)| ≤ 17 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ)) / M →
      |(u' : ℝ)| ≤ 2 * (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)) →
      ∃ l : ℤ × ℤ, v' = l.1 * c1.1 + l.2 * c2.1 ∧ u' = l.1 * c1.2 + l.2 * c2.2 ∧
        |(l.1 : ℝ)| ≤ 2 / Real.sqrt ((M / (17 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ))) *
          ((c1.1 : ℝ) - ρ0 ^ (3 / 2 : ℝ) * (c1.2 : ℝ))) ^ 2 +
          ((c1.2 : ℝ) / (2 * (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)))) ^ 2) ∧
        |(l.2 : ℝ)| ≤ 2 / Real.sqrt ((M / (17 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ))) *
          ((c2.1 : ℝ) - ρ0 ^ (3 / 2 : ℝ) * (c2.2 : ℝ))) ^ 2 +
          ((c2.2 : ℝ) / (2 * (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)))) ^ 2)) ∧
    (∀ z : ℤ × ℤ, ∃! l : ℤ × ℤ, z.1 = l.1 * c1.1 + l.2 * c2.1 ∧ z.2 = l.1 * c1.2 + l.2 * c2.2) ∧
    (∀ l : ℤ × ℤ, Int.gcd (l.1 * c1.1 + l.2 * c2.1) (l.1 * c1.2 + l.2 * c2.2) = Int.gcd l.1 l.2)) := by
  intro D E x M ρ0 hD hE hx hM hρl hρu
  have hD0 : 0 < D := by linarith
  have hE0 : 0 < E := by linarith
  have hx0 : 0 < x := by linarith
  have hM0 : 0 < M := by linarith
  have hDne : D ≠ 0 := hD0.ne'
  have hEne : E ≠ 0 := hE0.ne'
  have hMne : M ≠ 0 := hM0.ne'
  have hU0 : 0 < x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ) := by positivity
  have hV0 : 0 < x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ) := by positivity
  have hα1 : 0 < M / (4 * D) := by positivity
  have hc1 : 0 < 2 * E := by positivity
  have hα2 : 0 < M / (17 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ))) := by positivity
  have hc2 : 0 < 2 * (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)) := by positivity
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h hh d e u v hd1 hd2 he1 he2 hu1 hu2 _ _ heq hr1 hr2
    exact PcPellRed.reduced_i D E x M ρ0 hD hE hx hM hρl hρu h hh d e u v hd1 hd2 he1 he2
      hu1 hu2 heq hr1 hr2
  · intro h h9 hMx
    have hs : (x ^ (1 / 2 : ℝ)) ^ 2 = x := PcPellRed.rpow_half_sq x hx0.le
    have hs0 : 0 ≤ x ^ (1 / 2 : ℝ) := by positivity
    have h3 : 3 * |(h : ℝ)| ≤ x ^ (1 / 2 : ℝ) := by
      apply PcPellRed.le_of_sq_le_sq_nn _ _ (by positivity) hs0
      rw [mul_pow, sq_abs, hs]; nlinarith
    calc 3 * |(h : ℝ)| * M ≤ x ^ (1 / 2 : ℝ) * x ^ (1 / 2 : ℝ) :=
          mul_le_mul h3 hMx hM0.le hs0
      _ = x := by rw [← sq, hs]
  · exact PcPellRed.exists_reduced (M / (4 * D)) ρ0 (2 * E) hα1 hc1
  · intro b1 b2 hdet hle hip
    have hB : M / (4 * D) * (4 * D / M) = 1 := by
      rw [div_mul_div_comm, mul_comm M]; exact div_self (mul_ne_zero (by positivity) hMne)
    obtain ⟨a1, a2, a3, a4, a5⟩ :=
      PcPellRed.side (M / (4 * D)) ρ0 (2 * E) (4 * D / M) hα1 hc1 hB b1 b2 hdet hle hip
    have hcα : 2 * E / (M / (4 * D)) = 8 * (D * E / M) := by
      rw [div_div_eq_mul_div]; ring
    refine ⟨a1, ?_, ?_, ?_, ?_, PcPellRed.unimod_unique b1 b2 hdet, PcPellRed.unimod_gcd b1 b2 hdet⟩
    · have := a2 (27 / 8) (by norm_num) (by norm_num)
      rw [hcα] at this
      have e : (27 / 8 : ℝ) * (8 * (D * E / M)) = 27 * (D * E / M) := by ring
      rw [e] at this
      exact this
    · have := a3
      rw [hcα] at this
      have e : (4 : ℝ) * (8 * (D * E / M)) = 32 * (D * E / M) := by ring
      rw [e] at this
      exact this
    · have := a4 (25 / 8) (by norm_num) (by norm_num)
      rw [hcα] at this
      have e : (25 / 8 : ℝ) * (8 * (D * E / M)) = 5 ^ 2 * (D * E / M) := by ring
      rw [e, PcPellRed.sqrt_const_mul 5 _ (by norm_num)] at this
      exact this
    · intro d' e' hz1 hz2
      exact a5 (d', e') hz1 hz2
  · exact PcPellRed.exists_reduced (M / (17 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ))))
      (ρ0 ^ (3 / 2 : ℝ)) (2 * (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ))) hα2 hc2
  · intro c1 c2 hdet hle hip
    have hB : M / (17 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ))) *
        (17 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ)) / M) = 1 := by
      rw [div_mul_div_comm, mul_comm M]; exact div_self (mul_ne_zero (by positivity) hMne)
    obtain ⟨a1, a2, a3, a4, a5⟩ := PcPellRed.side (M / (17 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ))))
      (ρ0 ^ (3 / 2 : ℝ)) (2 * (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)))
      (17 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ)) / M) hα2 hc2 hB c1 c2 hdet hle hip
    have hcα : 2 * (x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)) / (M / (17 * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ)))) =
        34 * ((x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)) * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ)) / M) := by
      rw [div_div_eq_mul_div]; ring
    refine ⟨a1, ?_, ?_, ?_, ?_, PcPellRed.unimod_unique c1 c2 hdet, PcPellRed.unimod_gcd c1 c2 hdet⟩
    · have := a2 (117 / 34) (by norm_num) (by norm_num)
      rw [hcα] at this
      have e : (117 / 34 : ℝ) * (34 * ((x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)) *
          (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ)) / M)) =
          117 * ((x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)) * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ)) / M) := by ring
      rw [e] at this
      exact this
    · have := a3
      rw [hcα] at this
      have e : (4 : ℝ) * (34 * ((x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)) *
          (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ)) / M)) =
          136 * ((x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)) * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ)) / M) := by ring
      rw [e] at this
      exact this
    · have := a4 (50 / 17) (by norm_num) (by norm_num)
      rw [hcα] at this
      have e : (50 / 17 : ℝ) * (34 * ((x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)) *
          (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ)) / M)) =
          10 ^ 2 * ((x ^ (1 / 2 : ℝ) * D ^ (-3 / 2 : ℝ)) * (x ^ (1 / 2 : ℝ) * E ^ (-3 / 2 : ℝ)) / M) := by ring
      rw [e, PcPellRed.sqrt_const_mul 10 _ (by norm_num)] at this
      exact this
    · intro v' u' hz1 hz2
      exact a5 (v', u') hz1 hz2

end C09

end JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure
