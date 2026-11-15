-- Source SHA-256: d410f0f5e8079544c21cef5ee5d4c265bd5996c503d8d467bc17b0538b8a5001
import Mathlib
import JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.LemmaP

namespace FormalAB.Sc8731f9d

namespace A3ActualTraceDerivatives

def tracePhi
    (pPlus pMinus qPlus qMinus rPlus rMinus tPlus tMinus : ℝ)
    (s w : ℝ) : ℝ :=
  16 * ((pPlus + qPlus * s) ^ 3 * (rPlus + tPlus * w) ^ 2 +
    (pMinus + qMinus * s) ^ 3 * (rMinus + tMinus * w) ^ 2)

def ActualPointPartialLowerBound : Prop :=
  ∀ b : ℕ, 1 ≤ b →
  ∀ c0 C0 : ℝ, 0 < c0 → 1 ≤ C0 →
  ∃ c C : ℝ, 0 < c ∧ 1 ≤ C ∧
    ∀ L : ℝ, 2 ≤ L →
    ∀ T : ℝ, C * L ^ (16 * (b + 1)) ≤ T →
    ∀ pPlus pMinus qPlus qMinus rPlus rMinus tPlus tMinus : ℝ,
    ∀ s w : ℝ,
      (|pPlus| ≤ C0 * L ^ b ∧ |pMinus| ≤ C0 * L ^ b ∧
        |qPlus| ≤ C0 * L ^ b ∧ |qMinus| ≤ C0 * L ^ b ∧
        |rPlus| ≤ C0 * L ^ b ∧ |rMinus| ≤ C0 * L ^ b ∧
        |tPlus| ≤ C0 * L ^ b ∧ |tMinus| ≤ C0 * L ^ b) →
      1 ≤ |pPlus * qMinus - pMinus * qPlus| →
      1 ≤ |rPlus * tMinus - rMinus * tPlus| →
      (c0 / L ^ b ≤ |pPlus + qPlus * s| ∧
        |pPlus + qPlus * s| ≤ C0 * L ^ b) →
      (c0 / L ^ b ≤ |pMinus + qMinus * s| ∧
        |pMinus + qMinus * s| ≤ C0 * L ^ b) →
      (c0 / L ^ b ≤ |rPlus + tPlus * w| ∧
        |rPlus + tPlus * w| ≤ C0 * L ^ b) →
      (c0 / L ^ b ≤ |rMinus + tMinus * w| ∧
        |rMinus + tMinus * w| ≤ C0 * L ^ b) →
      |tracePhi pPlus pMinus qPlus qMinus rPlus rMinus tPlus tMinus s w|
        ≤ C0 * L ^ (5 * b) / T →
      c / L ^ (6 * b + 10) ≤
          |deriv (fun z : ℝ =>
            tracePhi pPlus pMinus qPlus qMinus rPlus rMinus tPlus tMinus z w) s| ∧
        c / L ^ (6 * b + 10) ≤
          |deriv (fun z : ℝ =>
            tracePhi pPlus pMinus qPlus qMinus rPlus rMinus tPlus tMinus s z) w|

end A3ActualTraceDerivatives

namespace A3ActualTraceDerivatives

theorem affine_hasDerivAt (p q x : ℝ) :
    HasDerivAt (fun z : ℝ => p + q * z) q x := by
  have hp : HasDerivAt (fun _ : ℝ => p) (0 : ℝ) x := hasDerivAt_const x p
  have hq : HasDerivAt (fun _ : ℝ => q) (0 : ℝ) x := hasDerivAt_const x q
  have hi : HasDerivAt (fun z : ℝ => z) (1 : ℝ) x := hasDerivAt_id x
  convert hp.add (hq.mul hi) using 1 <;> first | rfl | ring

theorem deriv_tracePhi_s
    (pPlus pMinus qPlus qMinus rPlus rMinus tPlus tMinus s w : ℝ) :
    deriv (fun z : ℝ =>
      tracePhi pPlus pMinus qPlus qMinus rPlus rMinus tPlus tMinus z w) s =
      48 * ((pPlus + qPlus * s) ^ 2 * qPlus * (rPlus + tPlus * w) ^ 2 +
        (pMinus + qMinus * s) ^ 2 * qMinus * (rMinus + tMinus * w) ^ 2) := by
  have hP := affine_hasDerivAt pPlus qPlus s
  have hM := affine_hasDerivAt pMinus qMinus s
  dsimp only [tracePhi]
  convert ((((hP.pow 3).mul_const ((rPlus + tPlus * w) ^ 2)).add
    ((hM.pow 3).mul_const ((rMinus + tMinus * w) ^ 2))).const_mul 16).deriv
    using 1 <;>
    first
    | rfl
    | (solve | congr 1)
    | ring

theorem deriv_tracePhi_w
    (pPlus pMinus qPlus qMinus rPlus rMinus tPlus tMinus s w : ℝ) :
    deriv (fun z : ℝ =>
      tracePhi pPlus pMinus qPlus qMinus rPlus rMinus tPlus tMinus s z) w =
      32 * ((pPlus + qPlus * s) ^ 3 * (rPlus + tPlus * w) * tPlus +
        (pMinus + qMinus * s) ^ 3 * (rMinus + tMinus * w) * tMinus) := by
  have hP := affine_hasDerivAt rPlus tPlus w
  have hM := affine_hasDerivAt rMinus tMinus w
  dsimp only [tracePhi]
  convert ((((hP.pow 2).const_mul ((pPlus + qPlus * s) ^ 3)).add
    ((hM.pow 2).const_mul ((pMinus + qMinus * s) ^ 3))).const_mul 16).deriv
    using 1 <;>
    first
    | rfl
    | (solve | congr 1)
    | ring

theorem scaled_four_factor_lower
    {c0 H a1 a2 a3 a4 : ℝ} (hc0 : 0 < c0) (hH : 0 < H)
    (h1 : c0 / H ≤ |a1|) (h2 : c0 / H ≤ |a2|)
    (h3 : c0 / H ≤ |a3|) (h4 : c0 / H ≤ |a4|) :
    c0 ^ 4 ≤ |a1 * a2 * a3 * a4| * H ^ 4 := by
  have h1' := (div_le_iff₀ hH).mp h1
  have h2' := (div_le_iff₀ hH).mp h2
  have h3' := (div_le_iff₀ hH).mp h3
  have h4' := (div_le_iff₀ hH).mp h4
  calc
    c0 ^ 4 = c0 * c0 * c0 * c0 := by ring
    _ ≤ (|a1| * H) * (|a2| * H) * (|a3| * H) * (|a4| * H) := by
      gcongr
    _ = |a1 * a2 * a3 * a4| * H ^ 4 := by
      simp only [abs_mul]
      ring

theorem partial_lower_of_scaled_residual
    {c0 C0 H N k det a1 a2 a3 a4 coeff denom R d : ℝ}
    (hc0 : 0 < c0) (_hC0 : 0 < C0) (hH : 0 < H)
    (hN : 4 ≤ N) (hk : |k| ≤ 3) (hdet : 1 ≤ |det|)
    (h1 : c0 / H ≤ |a1|) (h2 : c0 / H ≤ |a2|)
    (h3 : c0 / H ≤ |a3|) (h4 : c0 / H ≤ |a4|)
    (hcoeff : |coeff| ≤ C0 * H) (hdenom : |denom| ≤ C0 * H)
    (hR : C0 * H ^ 5 * |R| ≤ c0 ^ 4)
    (hidentity : N * det * (a1 * a2 * a3 * a4) =
      k * coeff * R - denom * d) :
    c0 ^ 4 ≤ C0 * H ^ 5 * |d| := by
  have hNnonneg : 0 ≤ N := by linarith
  have hprod := scaled_four_factor_lower hc0 hH h1 h2 h3 h4
  have hprodNonneg : 0 ≤ |a1 * a2 * a3 * a4| * H ^ 4 := by positivity
  have hdetGrow : |a1 * a2 * a3 * a4| * H ^ 4 ≤
      |det| * (|a1 * a2 * a3 * a4| * H ^ 4) := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hdet hprodNonneg
  have hmain : N * c0 ^ 4 ≤
      (N * |det| * |a1 * a2 * a3 * a4|) * H ^ 4 := by
    calc
      N * c0 ^ 4 ≤ N * (|a1 * a2 * a3 * a4| * H ^ 4) :=
        mul_le_mul_of_nonneg_left hprod hNnonneg
      _ ≤ N * (|det| * (|a1 * a2 * a3 * a4| * H ^ 4)) :=
        mul_le_mul_of_nonneg_left hdetGrow hNnonneg
      _ = (N * |det| * |a1 * a2 * a3 * a4|) * H ^ 4 := by ring
  have habs : N * |det| * |a1 * a2 * a3 * a4| ≤
      |k| * |coeff| * |R| + |denom| * |d| := by
    calc
      N * |det| * |a1 * a2 * a3 * a4| =
          |N * det * (a1 * a2 * a3 * a4)| := by
        simp only [abs_mul, abs_of_nonneg hNnonneg]
      _ = |k * coeff * R - denom * d| := congrArg abs hidentity
      _ ≤ |k * coeff * R| + |denom * d| := by
        simpa only [sub_eq_add_neg, abs_neg] using
          abs_add_le (k * coeff * R) (-(denom * d))
      _ = |k| * |coeff| * |R| + |denom| * |d| := by
        simp only [abs_mul]
  have herr : |k| * |coeff| * |R| * H ^ 4 ≤ 3 * c0 ^ 4 := by
    calc
      |k| * |coeff| * |R| * H ^ 4 ≤
          3 * (C0 * H) * |R| * H ^ 4 := by gcongr
      _ = 3 * (C0 * H ^ 5 * |R|) := by ring
      _ ≤ 3 * c0 ^ 4 := mul_le_mul_of_nonneg_left hR (by norm_num)
  have hden : |denom| * |d| * H ^ 4 ≤ C0 * H ^ 5 * |d| := by
    calc
      |denom| * |d| * H ^ 4 ≤ (C0 * H) * |d| * H ^ 4 := by gcongr
      _ = C0 * H ^ 5 * |d| := by ring
  have hsum : (|k| * |coeff| * |R| + |denom| * |d|) * H ^ 4 ≤
      3 * c0 ^ 4 + C0 * H ^ 5 * |d| := by
    calc
      (|k| * |coeff| * |R| + |denom| * |d|) * H ^ 4 =
          |k| * |coeff| * |R| * H ^ 4 + |denom| * |d| * H ^ 4 := by ring
      _ ≤ 3 * c0 ^ 4 + C0 * H ^ 5 * |d| := add_le_add herr hden
  have hfour : 4 * c0 ^ 4 ≤
      3 * c0 ^ 4 + C0 * H ^ 5 * |d| :=
    (mul_le_mul_of_nonneg_right hN (le_of_lt (pow_pos hc0 4))).trans
      (hmain.trans ((mul_le_mul_of_nonneg_right habs (by positivity)).trans hsum))
  linarith only [hfour]

theorem actual_point_partial_lower_bound : ActualPointPartialLowerBound := by
  intro b hb c0 C0 hc0 hC0
  have hC0pos : 0 < C0 := by linarith
  have hc4 : 0 < c0 ^ 4 := pow_pos hc0 4
  let c : ℝ := c0 ^ 4 / C0
  let C : ℝ := 1 + C0 ^ 2 / c0 ^ 4
  have hc : 0 < c := div_pos hc4 hC0pos
  have hC : 1 ≤ C := by
    dsimp only [C]
    have hnonneg : 0 ≤ C0 ^ 2 / c0 ^ 4 := by positivity
    linarith
  have hCpos : 0 < C := by linarith
  have hCscale : C0 ^ 2 ≤ C * c0 ^ 4 := by
    have hratio : C0 ^ 2 / c0 ^ 4 ≤ C := by dsimp only [C]; linarith
    exact (div_le_iff₀ hc4).mp hratio
  refine ⟨c, C, hc, hC, ?_⟩
  intro L hL T hT pPlus pMinus qPlus qMinus rPlus rMinus tPlus tMinus s w
    hcoeff hdetU hdetV hUP hUM hVP hVM hPhi
  have hLpos : 0 < L := by linarith
  have hLone : 1 ≤ L := by linarith
  let H : ℝ := L ^ b
  have hHpos : 0 < H := pow_pos hLpos b
  have hHpow (n : ℕ) : H ^ n = L ^ (n * b) := by
    dsimp only [H]
    rw [← pow_mul, Nat.mul_comm b n]
  have hHlarge : H ^ 10 ≤ L ^ (16 * (b + 1)) := by
    rw [hHpow 10]
    exact pow_le_pow_right₀ hLone (by omega)
  have hTsmall : C * H ^ 10 ≤ T :=
    (mul_le_mul_of_nonneg_left hHlarge (le_of_lt hCpos)).trans hT
  have hTpos : 0 < T := lt_of_lt_of_le (mul_pos hCpos (pow_pos hHpos 10)) hTsmall
  have hbudget : C0 ^ 2 * H ^ 10 ≤ c0 ^ 4 * T := by
    calc
      C0 ^ 2 * H ^ 10 ≤ (C * c0 ^ 4) * H ^ 10 :=
        mul_le_mul_of_nonneg_right hCscale (by positivity)
      _ = c0 ^ 4 * (C * H ^ 10) := by ring
      _ ≤ c0 ^ 4 * T := mul_le_mul_of_nonneg_left hTsmall (le_of_lt hc4)
  let UP : ℝ := pPlus + qPlus * s
  let UM : ℝ := pMinus + qMinus * s
  let VP : ℝ := rPlus + tPlus * w
  let VM : ℝ := rMinus + tMinus * w
  let R : ℝ := tracePhi pPlus pMinus qPlus qMinus rPlus rMinus tPlus tMinus s w
  let Ds : ℝ := deriv (fun z : ℝ =>
    tracePhi pPlus pMinus qPlus qMinus rPlus rMinus tPlus tMinus z w) s
  let Dw : ℝ := deriv (fun z : ℝ =>
    tracePhi pPlus pMinus qPlus qMinus rPlus rMinus tPlus tMinus s z) w
  have hRsmall : |R| ≤ C0 * H ^ 5 / T := by
    simpa only [hHpow 5] using hPhi
  have hRscaled : C0 * H ^ 5 * |R| ≤ c0 ^ 4 := by
    calc
      C0 * H ^ 5 * |R| ≤ C0 * H ^ 5 * (C0 * H ^ 5 / T) :=
        mul_le_mul_of_nonneg_left hRsmall (by positivity)
      _ = C0 ^ 2 * H ^ 10 / T := by ring
      _ ≤ c0 ^ 4 := (div_le_iff₀ hTpos).mpr hbudget
  rcases hcoeff with ⟨hpPlus, hpMinus, hqPlus, hqMinus, hrPlus, hrMinus, htPlus, htMinus⟩
  have hidentityS :
      (48 : ℝ) * (pPlus * qMinus - pMinus * qPlus) * (UP * UP * VP * VP) =
        3 * qMinus * R - UM * Ds := by
    dsimp only [UP, UM, VP, R, Ds]
    rw [deriv_tracePhi_s]
    dsimp only [tracePhi]
    ring
  have hidentityW :
      (32 : ℝ) * (rPlus * tMinus - rMinus * tPlus) * (UP * UP * UP * VP) =
        2 * tMinus * R - VM * Dw := by
    dsimp only [UP, VP, VM, R, Dw]
    rw [deriv_tracePhi_w]
    dsimp only [tracePhi]
    ring
  have hs : c0 ^ 4 ≤ C0 * H ^ 5 * |Ds| :=
    partial_lower_of_scaled_residual hc0 hC0pos hHpos
      (by norm_num : (4 : ℝ) ≤ 48) (by norm_num : |(3 : ℝ)| ≤ 3) hdetU
      hUP.1 hUP.1 hVP.1 hVP.1 hqMinus hUM.2 hRscaled hidentityS
  have hw : c0 ^ 4 ≤ C0 * H ^ 5 * |Dw| :=
    partial_lower_of_scaled_residual hc0 hC0pos hHpos
      (by norm_num : (4 : ℝ) ≤ 32) (by norm_num : |(2 : ℝ)| ≤ 3) hdetV
      hUP.1 hUP.1 hUP.1 hVP.1 htMinus hVM.2 hRscaled hidentityW
  have hHtarget : H ^ 5 ≤ L ^ (6 * b + 10) := by
    rw [hHpow 5]
    exact pow_le_pow_right₀ hLone (by omega)
  have hfinal (d : ℝ) (hd : c0 ^ 4 ≤ C0 * H ^ 5 * |d|) :
      c / L ^ (6 * b + 10) ≤ |d| := by
    apply (div_le_iff₀ (pow_pos hLpos (6 * b + 10))).mpr
    change c0 ^ 4 / C0 ≤ |d| * L ^ (6 * b + 10)
    apply (div_le_iff₀ hC0pos).mpr
    calc
      c0 ^ 4 ≤ C0 * H ^ 5 * |d| := hd
      _ ≤ C0 * L ^ (6 * b + 10) * |d| := by gcongr
      _ = (|d| * L ^ (6 * b + 10)) * C0 := by ring
  exact ⟨hfinal Ds hs, hfinal Dw hw⟩

end A3ActualTraceDerivatives

namespace A3LocalComplexGraph

def realTracePhi
    (pPlus pMinus qPlus qMinus rPlus rMinus tPlus tMinus s w : ℝ) : ℝ :=
  16 * ((pPlus + qPlus * s) ^ 3 * (rPlus + tPlus * w) ^ 2 +
    (pMinus + qMinus * s) ^ 3 * (rMinus + tMinus * w) ^ 2)

def complexTracePhi
    (pPlus pMinus qPlus qMinus rPlus rMinus tPlus tMinus : ℝ)
    (s w : ℂ) : ℂ :=
  16 * (((pPlus : ℂ) + (qPlus : ℂ) * s) ^ 3 *
      ((rPlus : ℂ) + (tPlus : ℂ) * w) ^ 2 +
    ((pMinus : ℂ) + (qMinus : ℂ) * s) ^ 3 *
      ((rMinus : ℂ) + (tMinus : ℂ) * w) ^ 2)

def LocalHolomorphicGraph : Prop :=
  ∀ b : ℕ, 1 ≤ b →
  ∀ c0 C0 : ℝ, 0 < c0 → 1 ≤ C0 →
  ∃ cS cW : ℝ,
    0 < cS ∧ 0 < cW ∧ cS ≤ 1 / 2 ∧ cW ≤ 1 / 2 ∧
    ∀ L : ℝ, 2 ≤ L →
    ∀ pPlus pMinus qPlus qMinus rPlus rMinus tPlus tMinus : ℝ,
    ∀ s0 w0 : ℝ,
      |s0| ≤ 1 → |w0| ≤ 3 / 2 →
      (|pPlus| ≤ C0 * L ^ b ∧ |pMinus| ≤ C0 * L ^ b ∧
        |qPlus| ≤ C0 * L ^ b ∧ |qMinus| ≤ C0 * L ^ b ∧
        |rPlus| ≤ C0 * L ^ b ∧ |rMinus| ≤ C0 * L ^ b ∧
        |tPlus| ≤ C0 * L ^ b ∧ |tMinus| ≤ C0 * L ^ b) →
      1 ≤ |pPlus * qMinus - pMinus * qPlus| →
      1 ≤ |rPlus * tMinus - rMinus * tPlus| →
      (c0 / L ^ b ≤ |pPlus + qPlus * s0| ∧
        |pPlus + qPlus * s0| ≤ C0 * L ^ b) →
      (c0 / L ^ b ≤ |pMinus + qMinus * s0| ∧
        |pMinus + qMinus * s0| ≤ C0 * L ^ b) →
      (c0 / L ^ b ≤ |rPlus + tPlus * w0| ∧
        |rPlus + tPlus * w0| ≤ C0 * L ^ b) →
      (c0 / L ^ b ≤ |rMinus + tMinus * w0| ∧
        |rMinus + tMinus * w0| ≤ C0 * L ^ b) →
      realTracePhi pPlus pMinus qPlus qMinus rPlus rMinus tPlus tMinus s0 w0 = 0 →
      ∃ f : ℂ → ℂ,
        f (s0 : ℂ) = (w0 : ℂ) ∧
        DifferentiableOn ℂ f
          (Metric.ball (s0 : ℂ) (cS / L ^ (100 * (b + 1)))) ∧
        (∀ z ∈ Metric.ball (s0 : ℂ) (cS / L ^ (100 * (b + 1))),
          complexTracePhi pPlus pMinus qPlus qMinus rPlus rMinus tPlus tMinus
              z (f z) = 0 ∧
            ‖f z - (w0 : ℂ)‖ < cW / L ^ (30 * (b + 1)) ∧
            ‖f z‖ ≤ 2) ∧
        (∀ z ∈ Metric.ball (s0 : ℂ) (cS / L ^ (100 * (b + 1))),
          ∀ v : ℂ, ‖v - (w0 : ℂ)‖ < cW / L ^ (30 * (b + 1)) →
            complexTracePhi pPlus pMinus qPlus qMinus rPlus rMinus tPlus tMinus
                z v = 0 → v = f z) ∧
        (∀ x : ℝ, |x - s0| < cS / L ^ (100 * (b + 1)) →
          (f (x : ℂ)).im = 0)

end A3LocalComplexGraph

namespace A3LocalComplexGraph

structure CoeffData where
  uP : ℂ
  uM : ℂ
  qP : ℂ
  qM : ℂ
  vP : ℂ
  vM : ℂ
  tP : ℂ
  tM : ℂ

def translatedPhi (d : CoeffData) (z w : ℂ) : ℂ :=
  16 * ((d.uP + d.qP * z) ^ 3 * (d.vP + d.tP * w) ^ 2 +
    (d.uM + d.qM * z) ^ 3 * (d.vM + d.tM * w) ^ 2)

def coefA (d : CoeffData) (z : ℂ) : ℂ :=
  16 * ((d.uP + d.qP * z) ^ 3 * d.tP ^ 2 +
    (d.uM + d.qM * z) ^ 3 * d.tM ^ 2)

def coefB (d : CoeffData) (z : ℂ) : ℂ :=
  32 * ((d.uP + d.qP * z) ^ 3 * d.vP * d.tP +
    (d.uM + d.qM * z) ^ 3 * d.vM * d.tM)

def coefC (d : CoeffData) (z : ℂ) : ℂ :=
  16 * ((d.uP + d.qP * z) ^ 3 * d.vP ^ 2 +
    (d.uM + d.qM * z) ^ 3 * d.vM ^ 2)

theorem translated_quadratic (d : CoeffData) (z w : ℂ) :
    translatedPhi d z w = coefA d z * w ^ 2 + coefB d z * w + coefC d z := by
  dsimp [translatedPhi, coefA, coefB, coefC]
  ring

theorem coefficients_entire (d : CoeffData) :
    Differentiable ℂ (coefA d) ∧ Differentiable ℂ (coefB d) ∧
      Differentiable ℂ (coefC d) := by
  constructor
  · unfold coefA
    fun_prop
  constructor
  · unfold coefB
    fun_prop
  · unfold coefC
    fun_prop

def CoeffBounds (d : CoeffData) (H : ℝ) : Prop :=
  ‖d.uP‖ ≤ H ∧ ‖d.uM‖ ≤ H ∧ ‖d.qP‖ ≤ H ∧ ‖d.qM‖ ≤ H ∧
  ‖d.vP‖ ≤ H ∧ ‖d.vM‖ ≤ H ∧ ‖d.tP‖ ≤ H ∧ ‖d.tM‖ ≤ H

theorem affine_norm_bound {u q z : ℂ} {H : ℝ}
    (hH : 0 ≤ H) (hu : ‖u‖ ≤ H) (hq : ‖q‖ ≤ H) (hz : ‖z‖ ≤ 1) :
    ‖u + q * z‖ ≤ 2 * H := by
  calc
    ‖u + q * z‖ ≤ ‖u‖ + ‖q * z‖ := norm_add_le _ _
    _ = ‖u‖ + ‖q‖ * ‖z‖ := by rw [norm_mul]
    _ ≤ H + H * 1 := by gcongr
    _ = 2 * H := by ring

theorem affine_cube_difference_bound {u q z : ℂ} {H : ℝ}
    (hH : 0 ≤ H) (hu : ‖u‖ ≤ H) (hq : ‖q‖ ≤ H) (hz : ‖z‖ ≤ 1) :
    ‖(u + q * z) ^ 3 - u ^ 3‖ ≤ 7 * H ^ 3 * ‖z‖ := by
  have haff := affine_norm_bound hH hu hq hz
  have hbracket : ‖(u + q * z) ^ 2 + (u + q * z) * u + u ^ 2‖ ≤ 7 * H ^ 2 := by
    calc
      ‖(u + q * z) ^ 2 + (u + q * z) * u + u ^ 2‖ ≤
          ‖(u + q * z) ^ 2 + (u + q * z) * u‖ + ‖u ^ 2‖ := norm_add_le _ _
      _ ≤ (‖(u + q * z) ^ 2‖ + ‖(u + q * z) * u‖) + ‖u ^ 2‖ := by
        gcongr
        exact norm_add_le _ _
      _ = ‖u + q * z‖ ^ 2 + ‖u + q * z‖ * ‖u‖ + ‖u‖ ^ 2 := by
        rw [norm_pow, norm_mul, norm_pow]
      _ ≤ (2 * H) ^ 2 + (2 * H) * H + H ^ 2 := by gcongr
      _ = 7 * H ^ 2 := by ring
  have hid : (u + q * z) ^ 3 - u ^ 3 =
      (q * z) * ((u + q * z) ^ 2 + (u + q * z) * u + u ^ 2) := by ring
  rw [hid, norm_mul, norm_mul]
  calc
    ‖q‖ * ‖z‖ * ‖(u + q * z) ^ 2 + (u + q * z) * u + u ^ 2‖ ≤
        H * ‖z‖ * (7 * H ^ 2) := by gcongr
    _ = 7 * H ^ 3 * ‖z‖ := by ring

theorem coefA_bound {d : CoeffData} {H : ℝ} {z : ℂ}
    (hH : 0 ≤ H) (hb : CoeffBounds d H) (hz : ‖z‖ ≤ 1) :
    ‖coefA d z‖ ≤ 256 * H ^ 5 := by
  rcases hb with ⟨huP, huM, hqP, hqM, hvP, hvM, htP, htM⟩
  have hP := affine_norm_bound hH huP hqP hz
  have hM := affine_norm_bound hH huM hqM hz
  calc
    ‖coefA d z‖ =
        16 * ‖(d.uP + d.qP * z) ^ 3 * d.tP ^ 2 +
          (d.uM + d.qM * z) ^ 3 * d.tM ^ 2‖ := by
      simp [coefA]
    _ ≤ 16 * (‖(d.uP + d.qP * z) ^ 3 * d.tP ^ 2‖ +
        ‖(d.uM + d.qM * z) ^ 3 * d.tM ^ 2‖) := by
      gcongr
      exact norm_add_le _ _
    _ = 16 * (‖d.uP + d.qP * z‖ ^ 3 * ‖d.tP‖ ^ 2 +
        ‖d.uM + d.qM * z‖ ^ 3 * ‖d.tM‖ ^ 2) := by simp only [norm_mul, norm_pow]
    _ ≤ 16 * ((2 * H) ^ 3 * H ^ 2 + (2 * H) ^ 3 * H ^ 2) := by gcongr
    _ = 256 * H ^ 5 := by ring

theorem stable_quadratic_equation {A B C B0 S : ℂ}
    (hB0 : B0 ≠ 0)
    (hS : S ^ 2 = (B ^ 2 - 4 * A * C) / B0 ^ 2)
    (hden : B + B0 * S ≠ 0) :
    A * (-2 * C / (B + B0 * S)) ^ 2 +
      B * (-2 * C / (B + B0 * S)) + C = 0 := by
  have hs : B0 ^ 2 * S ^ 2 = B ^ 2 - 4 * A * C := by
    have hh := (eq_div_iff (pow_ne_zero 2 hB0)).mp hS
    simpa only [mul_comm] using hh
  field_simp [hden]
  linear_combination C * hs

theorem coefB_difference_bound {d : CoeffData} {H : ℝ} {z : ℂ}
    (hH : 0 ≤ H) (hb : CoeffBounds d H) (hz : ‖z‖ ≤ 1) :
    ‖coefB d z - coefB d 0‖ ≤ 448 * H ^ 5 * ‖z‖ := by
  rcases hb with ⟨huP, huM, hqP, hqM, hvP, hvM, htP, htM⟩
  have hP := affine_cube_difference_bound hH huP hqP hz
  have hM := affine_cube_difference_bound hH huM hqM hz
  have hid : coefB d z - coefB d 0 =
      32 * (((d.uP + d.qP * z) ^ 3 - d.uP ^ 3) * d.vP * d.tP +
        ((d.uM + d.qM * z) ^ 3 - d.uM ^ 3) * d.vM * d.tM) := by
    dsimp [coefB]
    ring
  calc
    ‖coefB d z - coefB d 0‖ =
        32 * ‖((d.uP + d.qP * z) ^ 3 - d.uP ^ 3) * d.vP * d.tP +
          ((d.uM + d.qM * z) ^ 3 - d.uM ^ 3) * d.vM * d.tM‖ := by
      rw [hid, norm_mul]
      norm_num
    _ ≤ 32 * (‖(d.uP + d.qP * z) ^ 3 - d.uP ^ 3‖ * ‖d.vP‖ * ‖d.tP‖ +
        ‖(d.uM + d.qM * z) ^ 3 - d.uM ^ 3‖ * ‖d.vM‖ * ‖d.tM‖) := by
      have hh := norm_add_le
        (((d.uP + d.qP * z) ^ 3 - d.uP ^ 3) * d.vP * d.tP)
        (((d.uM + d.qM * z) ^ 3 - d.uM ^ 3) * d.vM * d.tM)
      simpa only [norm_mul] using mul_le_mul_of_nonneg_left hh (by norm_num : (0 : ℝ) ≤ 32)
    _ ≤ 32 * ((7 * H ^ 3 * ‖z‖) * H * H + (7 * H ^ 3 * ‖z‖) * H * H) := by gcongr
    _ = 448 * H ^ 5 * ‖z‖ := by ring

theorem coefC_difference_bound {d : CoeffData} {H : ℝ} {z : ℂ}
    (hH : 0 ≤ H) (hb : CoeffBounds d H) (hz : ‖z‖ ≤ 1) :
    ‖coefC d z - coefC d 0‖ ≤ 224 * H ^ 5 * ‖z‖ := by
  rcases hb with ⟨huP, huM, hqP, hqM, hvP, hvM, htP, htM⟩
  have hP := affine_cube_difference_bound hH huP hqP hz
  have hM := affine_cube_difference_bound hH huM hqM hz
  have hid : coefC d z - coefC d 0 =
      16 * (((d.uP + d.qP * z) ^ 3 - d.uP ^ 3) * d.vP ^ 2 +
        ((d.uM + d.qM * z) ^ 3 - d.uM ^ 3) * d.vM ^ 2) := by
    dsimp [coefC]
    ring
  calc
    ‖coefC d z - coefC d 0‖ =
        16 * ‖((d.uP + d.qP * z) ^ 3 - d.uP ^ 3) * d.vP ^ 2 +
          ((d.uM + d.qM * z) ^ 3 - d.uM ^ 3) * d.vM ^ 2‖ := by
      rw [hid, norm_mul]
      norm_num
    _ ≤ 16 * (‖(d.uP + d.qP * z) ^ 3 - d.uP ^ 3‖ * ‖d.vP‖ ^ 2 +
        ‖(d.uM + d.qM * z) ^ 3 - d.uM ^ 3‖ * ‖d.vM‖ ^ 2) := by
      have hh := norm_add_le
        (((d.uP + d.qP * z) ^ 3 - d.uP ^ 3) * d.vP ^ 2)
        (((d.uM + d.qM * z) ^ 3 - d.uM ^ 3) * d.vM ^ 2)
      simpa only [norm_mul, norm_pow] using mul_le_mul_of_nonneg_left hh (by norm_num : (0 : ℝ) ≤ 16)
    _ ≤ 16 * ((7 * H ^ 3 * ‖z‖) * H ^ 2 + (7 * H ^ 3 * ‖z‖) * H ^ 2) := by gcongr
    _ = 224 * H ^ 5 * ‖z‖ := by ring

theorem principal_sqrt_square (z : ℂ) : Complex.sqrt z ^ 2 = z := by
  change (z ^ ((2 : ℂ)⁻¹)) ^ (2 : ℕ) = z
  exact Complex.cpow_nat_inv_pow z (by norm_num : (2 : ℕ) ≠ 0)

theorem principal_sqrt_re_nonneg (z : ℂ) : 0 ≤ (Complex.sqrt z).re := by
  change 0 ≤ (z ^ ((2 : ℂ)⁻¹)).re
  rw [Complex.cpow_inv_two_re]
  exact Real.sqrt_nonneg _

theorem principal_sqrt_near_one (z : ℂ) :
    ‖Complex.sqrt z - 1‖ ≤ ‖z - 1‖ := by
  have hre := principal_sqrt_re_nonneg z
  have hden : (1 : ℝ) ≤ ‖Complex.sqrt z + 1‖ := by
    have hh := Complex.re_le_norm (Complex.sqrt z + 1)
    simp only [Complex.add_re, Complex.one_re] at hh
    linarith
  have hid : (Complex.sqrt z - 1) * (Complex.sqrt z + 1) = z - 1 := by
    calc
      (Complex.sqrt z - 1) * (Complex.sqrt z + 1) = Complex.sqrt z ^ 2 - 1 := by ring
      _ = z - 1 := by rw [principal_sqrt_square]
  calc
    ‖Complex.sqrt z - 1‖ = ‖Complex.sqrt z - 1‖ * 1 := by ring
    _ ≤ ‖Complex.sqrt z - 1‖ * ‖Complex.sqrt z + 1‖ :=
      mul_le_mul_of_nonneg_left hden (norm_nonneg _)
    _ = ‖z - 1‖ := by rw [← norm_mul, hid]

theorem slitPlane_of_near_one {z : ℂ} (hz : ‖z - 1‖ ≤ (1 : ℝ) / 4) :
    z ∈ Complex.slitPlane := by
  apply Complex.mem_slitPlane_iff.mpr
  left
  have hh := Complex.re_le_norm (1 - z)
  rw [norm_sub_rev] at hh
  simp only [Complex.sub_re, Complex.one_re] at hh
  linarith

noncomputable def normalizedDiscriminant (A B C B0 : ℂ) : ℂ :=
  (B ^ 2 - 4 * A * C) / B0 ^ 2

theorem normalizedDiscriminant_near_one {A B C B0 : ℂ}
    (hB0 : B0 ≠ 0)
    (hB : ‖B - B0‖ ≤ ‖B0‖ / 16)
    (hAC : ‖4 * A * C‖ ≤ ‖B0‖ ^ 2 / 16) :
    ‖normalizedDiscriminant A B C B0 - 1‖ ≤ (1 : ℝ) / 4 := by
  have hb : 0 < ‖B0‖ := norm_pos_iff.mpr hB0
  have hplus : ‖B - B0 + 2 * B0‖ ≤ ‖B0‖ / 16 + 2 * ‖B0‖ := by
    calc
      ‖B - B0 + 2 * B0‖ ≤ ‖B - B0‖ + ‖2 * B0‖ := norm_add_le _ _
      _ = ‖B - B0‖ + 2 * ‖B0‖ := by norm_num [norm_mul]
      _ ≤ ‖B0‖ / 16 + 2 * ‖B0‖ := add_le_add hB (le_refl _)
  have hsquare : ‖B ^ 2 - B0 ^ 2‖ ≤ 33 * ‖B0‖ ^ 2 / 256 := by
    have hid : B ^ 2 - B0 ^ 2 = (B - B0) * (B - B0 + 2 * B0) := by ring
    rw [hid, norm_mul]
    calc
      ‖B - B0‖ * ‖B - B0 + 2 * B0‖ ≤
          (‖B0‖ / 16) * (‖B0‖ / 16 + 2 * ‖B0‖) := by gcongr
      _ = 33 * ‖B0‖ ^ 2 / 256 := by ring
  have hnum : ‖B ^ 2 - B0 ^ 2 - 4 * A * C‖ ≤ 49 * ‖B0‖ ^ 2 / 256 := by
    have ht : ‖B ^ 2 - B0 ^ 2 - 4 * A * C‖ ≤
        ‖B ^ 2 - B0 ^ 2‖ + ‖4 * A * C‖ := by
      calc
        ‖B ^ 2 - B0 ^ 2 - 4 * A * C‖ =
            ‖(B ^ 2 - B0 ^ 2) + (-(4 * A * C))‖ := by congr 1
        _ ≤ ‖B ^ 2 - B0 ^ 2‖ + ‖-(4 * A * C)‖ := norm_add_le _ _
        _ = ‖B ^ 2 - B0 ^ 2‖ + ‖4 * A * C‖ := by rw [norm_neg]
    linarith
  have hid : normalizedDiscriminant A B C B0 - 1 =
      (B ^ 2 - B0 ^ 2 - 4 * A * C) / B0 ^ 2 := by
    dsimp [normalizedDiscriminant]
    field_simp
    ring
  rw [hid, norm_div, norm_pow]
  apply (div_le_iff₀ (pow_pos hb 2)).mpr
  nlinarith [sq_nonneg ‖B0‖]

theorem root_denominator_lower {B B0 S : ℂ}
    (hB : ‖B - B0‖ ≤ ‖B0‖ / 16)
    (hS : ‖S - 1‖ ≤ (1 : ℝ) / 4) :
    ‖B0‖ ≤ ‖B + B0 * S‖ := by
  have herr : ‖2 * B0 - (B + B0 * S)‖ ≤ ‖B0‖ / 16 + ‖B0‖ / 4 := by
    have hid : 2 * B0 - (B + B0 * S) = (B0 - B) + B0 * (1 - S) := by ring
    rw [hid]
    calc
      ‖(B0 - B) + B0 * (1 - S)‖ ≤ ‖B0 - B‖ + ‖B0 * (1 - S)‖ := norm_add_le _ _
      _ = ‖B - B0‖ + ‖B0‖ * ‖S - 1‖ := by rw [norm_sub_rev B0 B, norm_mul, norm_sub_rev 1 S]
      _ ≤ ‖B0‖ / 16 + ‖B0‖ * (1 / 4) := by gcongr
      _ = ‖B0‖ / 16 + ‖B0‖ / 4 := by ring
  have hh := norm_sub_norm_le (2 * B0) (B + B0 * S)
  have hn : ‖(2 : ℂ) * B0‖ = 2 * ‖B0‖ := by norm_num [norm_mul]
  rw [hn] at hh
  have hb : 0 ≤ ‖B0‖ := norm_nonneg _
  linarith

theorem quadratic_local_branch
    (A B C : ℂ → ℂ) (B0 : ℂ) (rS rW : ℝ)
    (hA : Differentiable ℂ A) (hB : Differentiable ℂ B)
    (hC : Differentiable ℂ C) (hB0 : B0 ≠ 0)
    (hCzero : C 0 = 0) (hrW : 0 < rW)
    (hsmall : ∀ z ∈ Metric.ball (0 : ℂ) rS,
      ‖B z - B0‖ ≤ ‖B0‖ / 16 ∧
      ‖4 * A z * C z‖ ≤ ‖B0‖ ^ 2 / 16 ∧
      ‖C z‖ ≤ ‖B0‖ * rW / 8 ∧
      ‖A z‖ * (2 * rW) ≤ ‖B0‖ / 8) :
    ∃ g : ℂ → ℂ,
      g 0 = 0 ∧
      DifferentiableOn ℂ g (Metric.ball (0 : ℂ) rS) ∧
      (∀ z ∈ Metric.ball (0 : ℂ) rS,
        A z * g z ^ 2 + B z * g z + C z = 0 ∧ ‖g z‖ < rW) ∧
      (∀ z ∈ Metric.ball (0 : ℂ) rS,
        ∀ v : ℂ, ‖v‖ < rW →
          A z * v ^ 2 + B z * v + C z = 0 → v = g z) := by
  let D : ℂ → ℂ := fun z => normalizedDiscriminant (A z) (B z) (C z) B0
  let S : ℂ → ℂ := fun z => Complex.sqrt (D z)
  let den : ℂ → ℂ := fun z => B z + B0 * S z
  let g : ℂ → ℂ := fun z => -2 * C z / den z
  have hb : 0 < ‖B0‖ := norm_pos_iff.mpr hB0
  have hnear (z : ℂ) (hz : z ∈ Metric.ball (0 : ℂ) rS) :
      ‖D z - 1‖ ≤ (1 : ℝ) / 4 :=
    normalizedDiscriminant_near_one hB0 (hsmall z hz).1 (hsmall z hz).2.1
  have hsnear (z : ℂ) (hz : z ∈ Metric.ball (0 : ℂ) rS) :
      ‖S z - 1‖ ≤ (1 : ℝ) / 4 :=
    (principal_sqrt_near_one (D z)).trans (hnear z hz)
  have hdenlower (z : ℂ) (hz : z ∈ Metric.ball (0 : ℂ) rS) :
      ‖B0‖ ≤ ‖den z‖ :=
    root_denominator_lower (hsmall z hz).1 (hsnear z hz)
  have hdenne (z : ℂ) (hz : z ∈ Metric.ball (0 : ℂ) rS) : den z ≠ 0 :=
    norm_pos_iff.mp (hb.trans_le (hdenlower z hz))
  have hDdiff : Differentiable ℂ D := by
    dsimp [D, normalizedDiscriminant]
    fun_prop
  have hSdiff (z : ℂ) (hz : z ∈ Metric.ball (0 : ℂ) rS) :
      DifferentiableAt ℂ S z :=
    (Complex.differentiableAt_sqrt (slitPlane_of_near_one (hnear z hz))).comp z (hDdiff z)
  have hdenDiff (z : ℂ) (hz : z ∈ Metric.ball (0 : ℂ) rS) :
      DifferentiableAt ℂ den z := by
    have hc : DifferentiableAt ℂ (fun _ : ℂ => B0) z := differentiableAt_const B0
    exact (hB z).add (hc.mul (hSdiff z hz))
  have hgsmall (z : ℂ) (hz : z ∈ Metric.ball (0 : ℂ) rS) : ‖g z‖ ≤ rW / 4 := by
    have hnorm : ‖g z‖ = 2 * ‖C z‖ / ‖den z‖ := by simp [g]
    rw [hnorm]
    apply (div_le_iff₀ (hb.trans_le (hdenlower z hz))).mpr
    have hnum : 2 * ‖C z‖ ≤ ‖B0‖ * rW / 4 := by linarith [(hsmall z hz).2.2.1]
    calc
      2 * ‖C z‖ ≤ ‖B0‖ * rW / 4 := hnum
      _ = (rW / 4) * ‖B0‖ := by ring
      _ ≤ (rW / 4) * ‖den z‖ :=
        mul_le_mul_of_nonneg_left (hdenlower z hz) (by positivity)
  have hgeq (z : ℂ) (hz : z ∈ Metric.ball (0 : ℂ) rS) :
      A z * g z ^ 2 + B z * g z + C z = 0 := by
    exact stable_quadratic_equation hB0 (principal_sqrt_square (D z)) (hdenne z hz)
  refine ⟨g, ?_, ?_, ?_, ?_⟩
  · simp only [g, hCzero, mul_zero, zero_div]
  · intro z hz
    have hc : DifferentiableAt ℂ (fun _ : ℂ => (-2 : ℂ)) z := differentiableAt_const (-2 : ℂ)
    exact ((hc.mul (hC z)).div (hdenDiff z hz) (hdenne z hz)).differentiableWithinAt
  · intro z hz
    exact ⟨hgeq z hz, lt_of_le_of_lt (hgsmall z hz) (by linarith)⟩
  · intro z hz v hv hveq
    have hg := hgsmall z hz
    have hfacnorm : ‖A z * (v + g z) + B z - B0‖ ≤ ‖B0‖ / 8 + ‖B0‖ / 16 := by
      have hid : A z * (v + g z) + B z - B0 =
          A z * (v + g z) + (B z - B0) := by ring
      rw [hid]
      calc
        ‖A z * (v + g z) + (B z - B0)‖ ≤
            ‖A z * (v + g z)‖ + ‖B z - B0‖ := norm_add_le _ _
        _ = ‖A z‖ * ‖v + g z‖ + ‖B z - B0‖ := by rw [norm_mul]
        _ ≤ ‖A z‖ * (‖v‖ + ‖g z‖) + ‖B z - B0‖ := by
          gcongr
          exact norm_add_le _ _
        _ ≤ ‖A z‖ * (2 * rW) + ‖B0‖ / 16 := by gcongr <;> first | exact (hsmall z hz).1 | linarith
        _ ≤ ‖B0‖ / 8 + ‖B0‖ / 16 :=
          add_le_add (hsmall z hz).2.2.2 (le_refl _)
    have hfacne : A z * (v + g z) + B z ≠ 0 := by
      intro hzero
      have hh : ‖B0‖ ≤ ‖B0‖ / 8 + ‖B0‖ / 16 := by
        simpa only [hzero, zero_sub, norm_neg] using hfacnorm
      linarith
    have hid : (v - g z) * (A z * (v + g z) + B z) = 0 := by
      linear_combination hveq - hgeq z hz
    exact sub_eq_zero.mp ((mul_eq_zero.mp hid).resolve_right hfacne)

theorem quantitative_radii {K E : ℝ} (hK : 1 ≤ K) (hE : 1 ≤ E) :
    let rS : ℝ := 1 / (512 * K ^ 4 * E ^ 100)
    let rW : ℝ := 1 / (32 * K ^ 2 * E ^ 30)
    0 < rS ∧ 0 < rW ∧ rS ≤ 1 ∧
    (K * E ^ 5) * rS ≤ (1 / (K * E ^ 10)) / 16 ∧
    4 * (K * E ^ 5) ^ 2 * rS ≤ (1 / (K * E ^ 10)) ^ 2 / 16 ∧
    (K * E ^ 5) * rS ≤ (1 / (K * E ^ 10)) * rW / 8 ∧
    (K * E ^ 5) * (2 * rW) ≤ (1 / (K * E ^ 10)) / 8 := by
  let rS : ℝ := 1 / (512 * K ^ 4 * E ^ 100)
  let rW : ℝ := 1 / (32 * K ^ 2 * E ^ 30)
  have hKpos : 0 < K := by linarith
  have hEpos : 0 < E := by linarith
  have hKn : K ≠ 0 := ne_of_gt hKpos
  have hEn : E ≠ 0 := ne_of_gt hEpos
  have hK13 : K ≤ K ^ 3 := by
    simpa only [pow_one] using pow_le_pow_right₀ hK (by decide : 1 ≤ 3)
  have hE1095 : E ^ 10 ≤ E ^ 95 := pow_le_pow_right₀ hE (by decide)
  have hE2090 : E ^ 20 ≤ E ^ 90 := pow_le_pow_right₀ hE (by decide)
  have hE4095 : E ^ 40 ≤ E ^ 95 := pow_le_pow_right₀ hE (by decide)
  have hE1025 : E ^ 10 ≤ E ^ 25 := pow_le_pow_right₀ hE (by decide)
  have hK4 : 1 ≤ K ^ 4 := one_le_pow₀ hK
  have hE100 : 1 ≤ E ^ 100 := one_le_pow₀ hE
  have hden : 1 ≤ 512 * K ^ 4 * E ^ 100 := by
    calc
      (1 : ℝ) ≤ 512 * 1 * 1 := by norm_num
      _ ≤ 512 * K ^ 4 * E ^ 100 := by gcongr
  have hsmallS : rS ≤ 1 := by
    dsimp only [rS]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 512 * K ^ 4 * E ^ 100)).mpr
    simpa only [one_mul] using hden
  refine ⟨by positivity, by positivity, hsmallS, ?_, ?_, ?_, ?_⟩
  · calc
      (K * E ^ 5) * rS = 1 / (512 * K ^ 3 * E ^ 95) := by
        dsimp [rS]; field_simp
      _ ≤ 1 / (16 * K * E ^ 10) := by
        apply one_div_le_one_div_of_le (by positivity)
        gcongr ; norm_num
      _ = (1 / (K * E ^ 10)) / 16 := by ring
  · calc
      4 * (K * E ^ 5) ^ 2 * rS = 1 / (128 * K ^ 2 * E ^ 90) := by
        dsimp [rS]; field_simp ; ring
      _ ≤ 1 / (16 * K ^ 2 * E ^ 20) := by
        apply one_div_le_one_div_of_le (by positivity)
        gcongr ; norm_num
      _ = (1 / (K * E ^ 10)) ^ 2 / 16 := by
        field_simp
  · calc
      (K * E ^ 5) * rS = 1 / (512 * K ^ 3 * E ^ 95) := by
        dsimp [rS]; field_simp
      _ ≤ 1 / (256 * K ^ 3 * E ^ 40) := by
        apply one_div_le_one_div_of_le (by positivity)
        gcongr ; norm_num
      _ = (1 / (K * E ^ 10)) * rW / 8 := by
        dsimp [rW]; field_simp ; ring
  · calc
      (K * E ^ 5) * (2 * rW) = 1 / (16 * K * E ^ 25) := by
        dsimp [rW]; field_simp ; ring
      _ ≤ 1 / (8 * K * E ^ 10) := by
        apply one_div_le_one_div_of_le (by positivity)
        gcongr ; norm_num
      _ = (1 / (K * E ^ 10)) / 8 := by ring

theorem graph_for_coeffData {d : CoeffData} {K E H : ℝ}
    (hK : 1 ≤ K) (hE : 1 ≤ E) (hH : 0 ≤ H)
    (hb : CoeffBounds d H) (hscale : 1024 * H ^ 5 ≤ K * E ^ 5)
    (hzero : translatedPhi d 0 0 = 0)
    (hbeta : 1 / (K * E ^ 10) ≤ ‖coefB d 0‖) :
    let rS : ℝ := 1 / (512 * K ^ 4 * E ^ 100)
    let rW : ℝ := 1 / (32 * K ^ 2 * E ^ 30)
    ∃ g : ℂ → ℂ,
      g 0 = 0 ∧ DifferentiableOn ℂ g (Metric.ball (0 : ℂ) rS) ∧
      (∀ z ∈ Metric.ball (0 : ℂ) rS, translatedPhi d z (g z) = 0 ∧ ‖g z‖ < rW) ∧
      (∀ z ∈ Metric.ball (0 : ℂ) rS, ∀ v : ℂ, ‖v‖ < rW →
        translatedPhi d z v = 0 → v = g z) := by
  let rS : ℝ := 1 / (512 * K ^ 4 * E ^ 100)
  let rW : ℝ := 1 / (32 * K ^ 2 * E ^ 30)
  have hKpos : 0 < K := by linarith
  have hEpos : 0 < E := by linarith
  obtain ⟨hrSpos, hrWpos, hrSone, h1, h2, h3, h4⟩ := quantitative_radii hK hE
  have h256 : 256 * H ^ 5 ≤ K * E ^ 5 := by
    calc
      256 * H ^ 5 ≤ 1024 * H ^ 5 := by gcongr ; norm_num
      _ ≤ K * E ^ 5 := hscale
  have h448 : 448 * H ^ 5 ≤ K * E ^ 5 := by
    calc
      448 * H ^ 5 ≤ 1024 * H ^ 5 := by gcongr ; norm_num
      _ ≤ K * E ^ 5 := hscale
  have h224 : 224 * H ^ 5 ≤ K * E ^ 5 := by
    calc
      224 * H ^ 5 ≤ 1024 * H ^ 5 := by gcongr ; norm_num
      _ ≤ K * E ^ 5 := hscale
  have hA_bd (z : ℂ) (hz : ‖z‖ ≤ 1) : ‖coefA d z‖ ≤ K * E ^ 5 :=
    (coefA_bound hH hb hz).trans h256
  have hB_bd (z : ℂ) (hz : ‖z‖ ≤ 1) :
      ‖coefB d z - coefB d 0‖ ≤ K * E ^ 5 * ‖z‖ :=
    (coefB_difference_bound hH hb hz).trans
      (mul_le_mul_of_nonneg_right h448 (norm_nonneg _))
  have hCzero : coefC d 0 = 0 := by
    simpa [translatedPhi, coefC] using hzero
  have hC_bd (z : ℂ) (hz : ‖z‖ ≤ 1) : ‖coefC d z‖ ≤ K * E ^ 5 * ‖z‖ := by
    have hh := (coefC_difference_bound hH hb hz).trans
      (mul_le_mul_of_nonneg_right h224 (norm_nonneg _))
    simpa only [hCzero, sub_zero] using hh
  have hBne : coefB d 0 ≠ 0 :=
    norm_pos_iff.mp (lt_of_lt_of_le (by positivity : (0 : ℝ) < 1 / (K * E ^ 10)) hbeta)
  have hsmall : ∀ z ∈ Metric.ball (0 : ℂ) rS,
      ‖coefB d z - coefB d 0‖ ≤ ‖coefB d 0‖ / 16 ∧
      ‖4 * coefA d z * coefC d z‖ ≤ ‖coefB d 0‖ ^ 2 / 16 ∧
      ‖coefC d z‖ ≤ ‖coefB d 0‖ * rW / 8 ∧
      ‖coefA d z‖ * (2 * rW) ≤ ‖coefB d 0‖ / 8 := by
    intro z hz
    have hzlt : ‖z‖ < rS := by simpa only [Metric.mem_ball, dist_zero_right] using hz
    have hzle : ‖z‖ ≤ rS := le_of_lt hzlt
    have hz1 : ‖z‖ ≤ 1 := hzle.trans hrSone
    have ha := hA_bd z hz1
    have hbz := hB_bd z hz1
    have hc := hC_bd z hz1
    refine ⟨?_, ?_, ?_, ?_⟩
    · calc
        ‖coefB d z - coefB d 0‖ ≤ K * E ^ 5 * ‖z‖ := hbz
        _ ≤ K * E ^ 5 * rS := by gcongr
        _ ≤ (1 / (K * E ^ 10)) / 16 := h1
        _ ≤ ‖coefB d 0‖ / 16 := by gcongr
    · calc
        ‖4 * coefA d z * coefC d z‖ = 4 * ‖coefA d z‖ * ‖coefC d z‖ := by simp []
        _ ≤ 4 * (K * E ^ 5) * ((K * E ^ 5) * ‖z‖) := by gcongr
        _ = 4 * (K * E ^ 5) ^ 2 * ‖z‖ := by ring
        _ ≤ 4 * (K * E ^ 5) ^ 2 * rS := by gcongr
        _ ≤ (1 / (K * E ^ 10)) ^ 2 / 16 := h2
        _ ≤ ‖coefB d 0‖ ^ 2 / 16 := by gcongr
    · calc
        ‖coefC d z‖ ≤ K * E ^ 5 * ‖z‖ := hc
        _ ≤ K * E ^ 5 * rS := by gcongr
        _ ≤ (1 / (K * E ^ 10)) * rW / 8 := h3
        _ ≤ ‖coefB d 0‖ * rW / 8 := by gcongr
    · calc
        ‖coefA d z‖ * (2 * rW) ≤ (K * E ^ 5) * (2 * rW) := by gcongr
        _ ≤ (1 / (K * E ^ 10)) / 8 := h4
        _ ≤ ‖coefB d 0‖ / 8 := by gcongr
  obtain ⟨g, hg0, hgDiff, hgEq, hgUnique⟩ :=
    quadratic_local_branch (coefA d) (coefB d) (coefC d) (coefB d 0) rS rW
      (coefficients_entire d).1 (coefficients_entire d).2.1
      (coefficients_entire d).2.2 hBne hCzero hrWpos hsmall
  refine ⟨g, hg0, hgDiff, ?_, ?_⟩
  · intro z hz
    refine ⟨?_, (hgEq z hz).2⟩
    rw [translated_quadratic]
    exact (hgEq z hz).1
  · intro z hz v hv heq
    apply hgUnique z hz v hv
    rwa [translated_quadratic] at heq

end A3LocalComplexGraph

namespace A3LocalComplexGraph

theorem local_holomorphic_graph : LocalHolomorphicGraph := by
  intro b hb c0 C0 hc0 hC0
  have hC0pos : 0 < C0 := by linarith
  obtain ⟨delta, threshold, hdelta, hthreshold, hpartials⟩ :=
    A3ActualTraceDerivatives.actual_point_partial_lower_bound b hb c0 C0 hc0 hC0
  let M : ℝ := 1024 * C0 ^ 5
  let K : ℝ := 1 + M + 1 / delta
  have hMpos : 0 < M := by dsimp [M]; positivity
  have hK : 1 ≤ K := by
    dsimp only [K]
    have hi : 0 < 1 / delta := by positivity
    linarith
  have hKpos : 0 < K := by linarith
  have hMK : M ≤ K := by
    dsimp only [K]
    have hi : 0 < 1 / delta := by positivity
    linarith
  have hdeltaK : 1 / K ≤ delta := by
    have hi : 1 / delta ≤ K := by dsimp only [K]; linarith
    have hh : 1 ≤ K * delta := (div_le_iff₀ hdelta).mp hi
    exact (div_le_iff₀ hKpos).mpr (by nlinarith)
  let cS : ℝ := 1 / (512 * K ^ 4)
  let cW : ℝ := 1 / (32 * K ^ 2)
  have hcS : 0 < cS := by dsimp [cS]; positivity
  have hcW : 0 < cW := by dsimp [cW]; positivity
  have hcSupper : cS ≤ 1 / 2 := by
    dsimp only [cS]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 512 * K ^ 4)).mpr
    have hh : 1 ≤ K ^ 4 := one_le_pow₀ hK
    linarith
  have hcWupper : cW ≤ 1 / 2 := by
    dsimp only [cW]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 32 * K ^ 2)).mpr
    have hh : 1 ≤ K ^ 2 := one_le_pow₀ hK
    linarith
  refine ⟨cS, cW, hcS, hcW, hcSupper, hcWupper, ?_⟩
  intro L hL pPlus pMinus qPlus qMinus rPlus rMinus tPlus tMinus s0 w0
    hs0 hw0 hcoeff hdetU hdetV hUP hUM hVP hVM hzero
  have hLpos : 0 < L := by linarith
  have hLone : 1 ≤ L := by linarith
  let E : ℝ := L ^ (b + 1)
  have hE : 1 ≤ E := one_le_pow₀ hLone
  have hEpos : 0 < E := by linarith
  have hEpow (n : ℕ) : E ^ n = L ^ (n * (b + 1)) := by
    dsimp only [E]
    rw [← pow_mul, Nat.mul_comm (b + 1) n]
  have hLbE : L ^ b ≤ E :=
    pow_le_pow_right₀ hLone (Nat.le_succ b)
  have hcap : C0 * L ^ b ≤ C0 * E :=
    mul_le_mul_of_nonneg_left hLbE (le_of_lt hC0pos)
  let d : CoeffData := {
    uP := ((pPlus + qPlus * s0 : ℝ) : ℂ)
    uM := ((pMinus + qMinus * s0 : ℝ) : ℂ)
    qP := (qPlus : ℂ)
    qM := (qMinus : ℂ)
    vP := ((rPlus + tPlus * w0 : ℝ) : ℂ)
    vM := ((rMinus + tMinus * w0 : ℝ) : ℂ)
    tP := (tPlus : ℂ)
    tM := (tMinus : ℂ) }
  have htranslate (z v : ℂ) :
      complexTracePhi pPlus pMinus qPlus qMinus rPlus rMinus tPlus tMinus z v =
        translatedPhi d (z - (s0 : ℂ)) (v - (w0 : ℂ)) := by
    dsimp [complexTracePhi, translatedPhi, d]
    push_cast
    ring
  have hcenter :
      complexTracePhi pPlus pMinus qPlus qMinus rPlus rMinus tPlus tMinus
        (s0 : ℂ) (w0 : ℂ) = 0 := by
    have hh := hzero
    dsimp [realTracePhi] at hh
    dsimp [complexTracePhi]
    exact_mod_cast hh
  have hzeroD : translatedPhi d 0 0 = 0 := by
    have hh := hcenter
    rw [htranslate] at hh
    simpa only [sub_self] using hh
  have hzeroOwned :
      A3ActualTraceDerivatives.tracePhi
        pPlus pMinus qPlus qMinus rPlus rMinus tPlus tMinus s0 w0 = 0 := hzero
  let T : ℝ := threshold * L ^ (16 * (b + 1))
  have hTpos : 0 < T := by
    dsimp only [T]
    exact mul_pos (by linarith) (pow_pos hLpos _)
  have hresidual :
      |A3ActualTraceDerivatives.tracePhi
        pPlus pMinus qPlus qMinus rPlus rMinus tPlus tMinus s0 w0|
        ≤ C0 * L ^ (5 * b) / T := by
    rw [hzeroOwned, abs_zero]
    positivity
  have hparts := hpartials L hL T (le_refl _)
    pPlus pMinus qPlus qMinus rPlus rMinus tPlus tMinus s0 w0
    hcoeff hdetU hdetV hUP hUM hVP hVM hresidual
  have hBderiv : coefB d 0 =
      ((deriv (fun z : ℝ =>
        A3ActualTraceDerivatives.tracePhi
          pPlus pMinus qPlus qMinus rPlus rMinus tPlus tMinus s0 z) w0 : ℝ) : ℂ) := by
    rw [A3ActualTraceDerivatives.deriv_tracePhi_w]
    dsimp [coefB, d]
    push_cast
    ring
  have hLderivative : L ^ (6 * b + 10) ≤ E ^ 10 := by
    rw [hEpow 10]
    exact pow_le_pow_right₀ hLone (by omega)
  have hbeta : 1 / (K * E ^ 10) ≤ ‖coefB d 0‖ := by
    calc
      1 / (K * E ^ 10) = (1 / K) / E ^ 10 := by ring
      _ ≤ delta / E ^ 10 := by gcongr
      _ ≤ delta / L ^ (6 * b + 10) := by gcongr
      _ ≤ ‖coefB d 0‖ := by
        rw [hBderiv, Complex.norm_real, Real.norm_eq_abs]
        exact hparts.2
  rcases hcoeff with ⟨hpPlus, hpMinus, hqPlus, hqMinus, hrPlus, hrMinus, htPlus, htMinus⟩
  have hbounds : CoeffBounds d (C0 * E) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · change ‖((pPlus + qPlus * s0 : ℝ) : ℂ)‖ ≤ C0 * E
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact hUP.2.trans hcap
    · change ‖((pMinus + qMinus * s0 : ℝ) : ℂ)‖ ≤ C0 * E
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact hUM.2.trans hcap
    · simpa [d, Complex.norm_real, Real.norm_eq_abs] using hqPlus.trans hcap
    · simpa [d, Complex.norm_real, Real.norm_eq_abs] using hqMinus.trans hcap
    · change ‖((rPlus + tPlus * w0 : ℝ) : ℂ)‖ ≤ C0 * E
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact hVP.2.trans hcap
    · change ‖((rMinus + tMinus * w0 : ℝ) : ℂ)‖ ≤ C0 * E
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact hVM.2.trans hcap
    · simpa [d, Complex.norm_real, Real.norm_eq_abs] using htPlus.trans hcap
    · simpa [d, Complex.norm_real, Real.norm_eq_abs] using htMinus.trans hcap
  have hscale : 1024 * (C0 * E) ^ 5 ≤ K * E ^ 5 := by
    calc
      1024 * (C0 * E) ^ 5 = M * E ^ 5 := by dsimp only [M]; ring
      _ ≤ K * E ^ 5 := mul_le_mul_of_nonneg_right hMK (by positivity)
  obtain ⟨g, hg0, hgDiff, hgEq, hgUnique⟩ :=
    graph_for_coeffData hK hE (by positivity : 0 ≤ C0 * E) hbounds hscale hzeroD hbeta
  have hrS : 1 / (512 * K ^ 4 * E ^ 100) =
      cS / L ^ (100 * (b + 1)) := by
    rw [hEpow 100]
    dsimp only [cS]
    ring
  have hrW : 1 / (32 * K ^ 2 * E ^ 30) =
      cW / L ^ (30 * (b + 1)) := by
    rw [hEpow 30]
    dsimp only [cW]
    ring
  rw [hrS] at hgDiff
  rw [hrS, hrW] at hgEq hgUnique
  let f : ℂ → ℂ := fun z => (w0 : ℂ) + g (z - (s0 : ℂ))
  have hmap (z : ℂ)
      (hz : z ∈ Metric.ball (s0 : ℂ) (cS / L ^ (100 * (b + 1)))) :
      z - (s0 : ℂ) ∈ Metric.ball (0 : ℂ) (cS / L ^ (100 * (b + 1))) := by
    simpa only [Metric.mem_ball, dist_eq_norm, sub_zero] using hz
  have hWrad : cW / L ^ (30 * (b + 1)) ≤ 1 / 2 := by
    have hh : 1 ≤ L ^ (30 * (b + 1)) := one_le_pow₀ hLone
    calc
      cW / L ^ (30 * (b + 1)) ≤ cW / 1 := by gcongr
      _ = cW := div_one _
      _ ≤ 1 / 2 := hcWupper
  have hGraph (z : ℂ)
      (hz : z ∈ Metric.ball (s0 : ℂ) (cS / L ^ (100 * (b + 1)))) :
      complexTracePhi pPlus pMinus qPlus qMinus rPlus rMinus tPlus tMinus z (f z) = 0 ∧
        ‖f z - (w0 : ℂ)‖ < cW / L ^ (30 * (b + 1)) ∧ ‖f z‖ ≤ 2 := by
    obtain ⟨heq, hnorm⟩ := hgEq (z - (s0 : ℂ)) (hmap z hz)
    refine ⟨?_, ?_, ?_⟩
    · rw [htranslate]
      simpa only [f, add_sub_cancel_left] using heq
    · simpa only [f, add_sub_cancel_left] using hnorm
    · calc
        ‖f z‖ ≤ ‖(w0 : ℂ)‖ + ‖g (z - (s0 : ℂ))‖ := norm_add_le _ _
        _ = |w0| + ‖g (z - (s0 : ℂ))‖ := by rw [Complex.norm_real, Real.norm_eq_abs]
        _ ≤ 2 := by linarith
  have hUnique (z : ℂ)
      (hz : z ∈ Metric.ball (s0 : ℂ) (cS / L ^ (100 * (b + 1))))
      (v : ℂ) (hv : ‖v - (w0 : ℂ)‖ < cW / L ^ (30 * (b + 1)))
      (heq : complexTracePhi pPlus pMinus qPlus qMinus rPlus rMinus tPlus tMinus z v = 0) :
      v = f z := by
    have hh : translatedPhi d (z - (s0 : ℂ)) (v - (w0 : ℂ)) = 0 := by
      rwa [← htranslate]
    have hval := hgUnique (z - (s0 : ℂ)) (hmap z hz) (v - (w0 : ℂ)) hv hh
    dsimp only [f]
    linear_combination hval
  refine ⟨f, ?_, ?_, hGraph, hUnique, ?_⟩
  · simp only [f, sub_self, hg0, add_zero]
  · intro z hz
    have hgat : DifferentiableAt ℂ g (z - (s0 : ℂ)) :=
      hgDiff.differentiableAt (Metric.isOpen_ball.mem_nhds (hmap z hz))
    have hshift : DifferentiableAt ℂ (fun y : ℂ => y - (s0 : ℂ)) z := by fun_prop
    have hconst : DifferentiableAt ℂ (fun _ : ℂ => (w0 : ℂ)) z := differentiableAt_const (w0 : ℂ)
    exact (hconst.add (hgat.comp z hshift)).differentiableWithinAt
  · intro x hx
    have hxball : (x : ℂ) ∈ Metric.ball (s0 : ℂ) (cS / L ^ (100 * (b + 1))) := by
      simpa only [Metric.mem_ball, dist_eq_norm, ← Complex.ofReal_sub,
        Complex.norm_real, Real.norm_eq_abs] using hx
    have hconjBound :
        ‖(starRingEnd ℂ) (f (x : ℂ)) - (w0 : ℂ)‖ < cW / L ^ (30 * (b + 1)) := by
      have hid : (starRingEnd ℂ) (f (x : ℂ)) - (w0 : ℂ) =
          (starRingEnd ℂ) (f (x : ℂ) - (w0 : ℂ)) := by simp
      rw [hid, Complex.norm_conj]
      exact (hGraph (x : ℂ) hxball).2.1
    have hconjZero :
        complexTracePhi pPlus pMinus qPlus qMinus rPlus rMinus tPlus tMinus
          (x : ℂ) ((starRingEnd ℂ) (f (x : ℂ))) = 0 := by
      have hh := congrArg (starRingEnd ℂ) (hGraph (x : ℂ) hxball).1
      simpa [complexTracePhi] using hh
    exact Complex.conj_eq_iff_im.mp
      (hUnique (x : ℂ) hxball ((starRingEnd ℂ) (f (x : ℂ))) hconjBound hconjZero)

end A3LocalComplexGraph

namespace JocelynClaims

theorem claim_ea314455809978934d8a98061e79710124c8b05a7df40f29f7178fbfe799111a : (let realTracePhi : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ := (fun pPlus pMinus qPlus qMinus rPlus rMinus tPlus tMinus s w => 16 * ((pPlus + qPlus * s) ^ 3 * (rPlus + tPlus * w) ^ 2 + (pMinus + qMinus * s) ^ 3 * (rMinus + tMinus * w) ^ 2)); let complexTracePhi : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℂ → ℂ → ℂ := (fun pPlus pMinus qPlus qMinus rPlus rMinus tPlus tMinus s w => 16 * (((pPlus : ℂ) + (qPlus : ℂ) * s) ^ 3 * ((rPlus : ℂ) + (tPlus : ℂ) * w) ^ 2 + ((pMinus : ℂ) + (qMinus : ℂ) * s) ^ 3 * ((rMinus : ℂ) + (tMinus : ℂ) * w) ^ 2)); ∀ b : ℕ, 1 ≤ b → ∀ c0 C0 : ℝ, 0 < c0 → 1 ≤ C0 → ∃ cS cW : ℝ, 0 < cS ∧ 0 < cW ∧ cS ≤ 1 / 2 ∧ cW ≤ 1 / 2 ∧ ∀ L : ℝ, 2 ≤ L → ∀ pPlus pMinus qPlus qMinus rPlus rMinus tPlus tMinus : ℝ, ∀ s0 w0 : ℝ, |s0| ≤ 1 → |w0| ≤ 3 / 2 → (|pPlus| ≤ C0 * L ^ b ∧ |pMinus| ≤ C0 * L ^ b ∧ |qPlus| ≤ C0 * L ^ b ∧ |qMinus| ≤ C0 * L ^ b ∧ |rPlus| ≤ C0 * L ^ b ∧ |rMinus| ≤ C0 * L ^ b ∧ |tPlus| ≤ C0 * L ^ b ∧ |tMinus| ≤ C0 * L ^ b) → 1 ≤ |pPlus * qMinus - pMinus * qPlus| → 1 ≤ |rPlus * tMinus - rMinus * tPlus| → (c0 / L ^ b ≤ |pPlus + qPlus * s0| ∧ |pPlus + qPlus * s0| ≤ C0 * L ^ b) → (c0 / L ^ b ≤ |pMinus + qMinus * s0| ∧ |pMinus + qMinus * s0| ≤ C0 * L ^ b) → (c0 / L ^ b ≤ |rPlus + tPlus * w0| ∧ |rPlus + tPlus * w0| ≤ C0 * L ^ b) → (c0 / L ^ b ≤ |rMinus + tMinus * w0| ∧ |rMinus + tMinus * w0| ≤ C0 * L ^ b) → realTracePhi pPlus pMinus qPlus qMinus rPlus rMinus tPlus tMinus s0 w0 = 0 → ∃ f : ℂ → ℂ, f (s0 : ℂ) = (w0 : ℂ) ∧ DifferentiableOn ℂ f (Metric.ball (s0 : ℂ) (cS / L ^ (100 * (b + 1)))) ∧ (∀ z ∈ Metric.ball (s0 : ℂ) (cS / L ^ (100 * (b + 1))), complexTracePhi pPlus pMinus qPlus qMinus rPlus rMinus tPlus tMinus z (f z) = 0 ∧ ‖f z - (w0 : ℂ)‖ < cW / L ^ (30 * (b + 1)) ∧ ‖f z‖ ≤ 2) ∧ (∀ z ∈ Metric.ball (s0 : ℂ) (cS / L ^ (100 * (b + 1))), ∀ v : ℂ, ‖v - (w0 : ℂ)‖ < cW / L ^ (30 * (b + 1)) → complexTracePhi pPlus pMinus qPlus qMinus rPlus rMinus tPlus tMinus z v = 0 → v = f z) ∧ (∀ x : ℝ, |x - s0| < cS / L ^ (100 * (b + 1)) → (f (x : ℂ)).im = 0)) := by
  change A3LocalComplexGraph.LocalHolomorphicGraph
  exact A3LocalComplexGraph.local_holomorphic_graph

end JocelynClaims

#print axioms JocelynClaims.claim_ea314455809978934d8a98061e79710124c8b05a7df40f29f7178fbfe799111a
