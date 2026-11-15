-- Source SHA-256: d3822d0268f92a03b1a6d5867d251c40a7a573bc1cd61bb9a342a0b50f6daa55
import Mathlib
import JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.LemmaP

namespace FormalAB.S96394400

set_option linter.all false

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

def ActualPointNearbyZero : Prop :=
  ∀ b : ℕ, 1 ≤ b →
  ∀ c0 C0 : ℝ, 0 < c0 → 1 ≤ C0 →
  ∃ c C : ℝ, 0 < c ∧ c ≤ 1 ∧ 1 ≤ C ∧
    ∀ L : ℝ, 2 ≤ L →
    ∀ T : ℝ, C * L ^ (64 * (b + 1)) ≤ T →
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
      ∃ w0 : ℝ,
        tracePhi pPlus pMinus qPlus qMinus rPlus rMinus tPlus tMinus s w0 = 0 ∧
        |w0 - w| ≤ c / L ^ (30 * (b + 1)) ∧
        |w0 - w| ≤ C * L ^ (20 * (b + 1)) / T ∧
        (c0 / (2 * L ^ b) ≤ |pPlus + qPlus * s| ∧
          |pPlus + qPlus * s| ≤ 2 * C0 * L ^ b) ∧
        (c0 / (2 * L ^ b) ≤ |pMinus + qMinus * s| ∧
          |pMinus + qMinus * s| ≤ 2 * C0 * L ^ b) ∧
        (c0 / (2 * L ^ b) ≤ |rPlus + tPlus * w0| ∧
          |rPlus + tPlus * w0| ≤ 2 * C0 * L ^ b) ∧
        (c0 / (2 * L ^ b) ≤ |rMinus + tMinus * w0| ∧
          |rMinus + tMinus * w0| ≤ 2 * C0 * L ^ b) ∧
        c / L ^ (6 * b + 10) ≤
          |deriv (fun z : ℝ =>
            tracePhi pPlus pMinus qPlus qMinus rPlus rMinus tPlus tMinus z w0) s| ∧
        c / L ^ (6 * b + 10) ≤
          |deriv (fun z : ℝ =>
            tracePhi pPlus pMinus qPlus qMinus rPlus rMinus tPlus tMinus s z) w0|

def NearbyZeroFromOwnedPartials : Prop :=
  ActualPointPartialLowerBound → ActualPointNearbyZero

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

namespace A3ActualTraceDerivatives
noncomputable section
set_option maxHeartbeats 1000000

lemma quadratic_small_root (a b d : ℝ) (hb : b ≠ 0)
    (hdisc : 4*a*d ≤ b^2) :
    ∃ z : ℝ, a*z^2+b*z+d=0 ∧ |z| ≤ 2*|d|/|b| := by
  let h : ℝ := -2*d/b
  let g : ℝ → ℝ := fun t => a*(t*h)^2+b*(t*h)+d
  have hb2 : 0 < b^2 := sq_pos_of_ne_zero hb
  have hfac : 4*a*d/b^2-1 ≤ 0 := by
    have hh : 4*a*d/b^2 ≤ 1 :=
      (div_le_iff₀ hb2).2 (by simpa using hdisc)
    linarith
  have hg0 : g 0 = d := by simp [g]
  have hg1 : g 1 = d*(4*a*d/b^2-1) := by
    dsimp [g,h]
    field_simp
    <;> ring
  have hmem : (0:ℝ) ∈ Set.uIcc (g 0) (g 1) := by
    rw [hg0,hg1,Set.mem_uIcc]
    by_cases hd : 0 ≤ d
    · exact Or.inr ⟨mul_nonpos_of_nonneg_of_nonpos hd hfac,hd⟩
    · exact Or.inl ⟨le_of_lt (lt_of_not_ge hd),
        mul_nonneg_of_nonpos_of_nonpos (le_of_lt (lt_of_not_ge hd)) hfac⟩
  have hg : Continuous g := by dsimp [g]; fun_prop
  obtain ⟨t,ht,hzero⟩ := intermediate_value_uIcc hg.continuousOn hmem
  have ht' : 0 ≤ t ∧ t ≤ 1 := by
    simpa only [Set.uIcc_of_le (by norm_num : (0:ℝ)≤1),Set.mem_Icc] using ht
  refine ⟨t*h,hzero,?_⟩
  calc
    |t*h| = |t| *|h| := abs_mul _ _
    _ ≤ 1*|h| := mul_le_mul_of_nonneg_right
      (by simpa only [abs_of_nonneg ht'.1] using ht'.2) (abs_nonneg _)
    _ = 2*|d|/|b| := by dsimp [h]; simp [abs_div,abs_mul]

lemma trace_w_derivative
    (pPlus pMinus qPlus qMinus rPlus rMinus tPlus tMinus s w : ℝ) :
    deriv (fun z : ℝ =>
      tracePhi pPlus pMinus qPlus qMinus rPlus rMinus tPlus tMinus s z) w =
      32 * ((pPlus+qPlus*s)^3*(rPlus+tPlus*w)*tPlus +
        (pMinus+qMinus*s)^3*(rMinus+tMinus*w)*tMinus) := by
  have hpp : HasDerivAt (fun _ : ℝ => rPlus) (0:ℝ) w := hasDerivAt_const w rPlus
  have hpt : HasDerivAt (fun _ : ℝ => tPlus) (0:ℝ) w := hasDerivAt_const w tPlus
  have hmp : HasDerivAt (fun _ : ℝ => rMinus) (0:ℝ) w := hasDerivAt_const w rMinus
  have hmt : HasDerivAt (fun _ : ℝ => tMinus) (0:ℝ) w := hasDerivAt_const w tMinus
  have hi : HasDerivAt (fun z : ℝ => z) (1:ℝ) w := hasDerivAt_id w
  have hp : HasDerivAt (fun z : ℝ => rPlus+tPlus*z) tPlus w := by
    convert hpp.add (hpt.mul hi) using 1 <;> first | rfl | ring
  have hm : HasDerivAt (fun z : ℝ => rMinus+tMinus*z) tMinus w := by
    convert hmp.add (hmt.mul hi) using 1 <;> first | rfl | ring
  have hh := ((((hp.pow 2).const_mul ((pPlus+qPlus*s)^3)).add
    ((hm.pow 2).const_mul ((pMinus+qMinus*s)^3))).const_mul 16).deriv
  convert hh using 1 <;> dsimp [tracePhi] <;> ring

lemma trace_w_taylor
    (pPlus pMinus qPlus qMinus rPlus rMinus tPlus tMinus s w z : ℝ) :
    tracePhi pPlus pMinus qPlus qMinus rPlus rMinus tPlus tMinus s (w+z) =
      (16*((pPlus+qPlus*s)^3*tPlus^2+(pMinus+qMinus*s)^3*tMinus^2))*z^2+
      (32*((pPlus+qPlus*s)^3*(rPlus+tPlus*w)*tPlus+
        (pMinus+qMinus*s)^3*(rMinus+tMinus*w)*tMinus))*z+
      tracePhi pPlus pMinus qPlus qMinus rPlus rMinus tPlus tMinus s w := by
  dsimp [tracePhi]
  ring

#print axioms quadratic_small_root
#print axioms trace_w_derivative
#print axioms trace_w_taylor
end
end A3ActualTraceDerivatives

namespace A3ActualTraceDerivatives
noncomputable section
set_option maxHeartbeats 1000000

lemma quadratic_height_window
    (a b d R T C0 m c C : ℝ)
    (hR : 1 ≤ R) (hC0 : 0 < C0) (hm : 0 < m) (hc : 0 < c) (hT : 0 < T)
    (ha : |a| ≤ 32*C0^5*R^5)
    (hb : m/R^8 ≤ |b|)
    (hd : |d| ≤ C0*R^5/T)
    (hT1 : (128*C0^6/m^2)*R^26 ≤ T)
    (hT2 : (2*C0/(m*c))*R^43 ≤ T)
    (hC : 2*C0/m ≤ C) :
    ∃ z : ℝ, a*z^2+b*z+d=0 ∧ |z| ≤ c/R^30 ∧
      |z| ≤ C*R^20/T := by
  have hR0 : 0 < R := by linarith
  have hb0 : 0 < |b| := (div_pos hm (pow_pos hR0 _)).trans_le hb
  have hbne : b ≠ 0 := abs_pos.mp hb0
  have hdisc : 4*a*d ≤ b^2 := by
    calc
      4*a*d ≤ 4*|a| *|d| := by
        have hh := le_abs_self (a*d)
        rw [abs_mul] at hh
        nlinarith
      _ ≤ 4*(32*C0^5*R^5)*(C0*R^5/T) := by
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left ha (by norm_num)) hd
          (abs_nonneg d) (by positivity)
      _ = ((m/R^8)^2)*((128*C0^6/m^2)*R^26)/T := by
        field_simp
        <;> ring
      _ ≤ (m/R^8)^2 := by
        apply (div_le_iff₀ hT).2
        exact mul_le_mul_of_nonneg_left hT1 (sq_nonneg _)
      _ ≤ b^2 := by
        have hsq : (m/R^8)^2 ≤ |b|^2 :=
          pow_le_pow_left₀ (by positivity) hb 2
        simpa only [sq_abs] using hsq
  obtain ⟨z,hzero,hz⟩ := quadratic_small_root a b d hbne hdisc
  have hdist : 2*|d|/|b| ≤ (2*C0/m)*R^13/T := by
    apply (div_le_iff₀ hb0).2
    calc
      2*|d| ≤ 2*(C0*R^5/T) := mul_le_mul_of_nonneg_left hd (by norm_num)
      _ = ((2*C0/m)*R^13/T)*(m/R^8) := by
        field_simp
        <;> ring
      _ ≤ ((2*C0/m)*R^13/T)*|b| :=
        mul_le_mul_of_nonneg_left hb (by positivity)
  refine ⟨z,hzero,?_,?_⟩
  · apply hz.trans (hdist.trans ?_)
    apply (div_le_iff₀ hT).2
    calc
      (2*C0/m)*R^13 = (c/R^30)*((2*C0/(m*c))*R^43) := by
        field_simp
        <;> ring
      _ ≤ (c/R^30)*T := mul_le_mul_of_nonneg_left hT2 (by positivity)
  · apply hz.trans (hdist.trans ?_)
    apply div_le_div_of_nonneg_right _ hT.le
    calc
      (2*C0/m)*R^13 ≤ C*R^13 :=
        mul_le_mul_of_nonneg_right hC (by positivity)
      _ ≤ C*R^20 := mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ hR (by omega)) (by
          have hp : 0 < 2*C0/m := by positivity
          linarith)

lemma quadratic_trace_coefficient_bound
    (U V t u C0 R : ℝ) (hC0 : 0 ≤ C0) (hR : 0 ≤ R)
    (hU : |U| ≤ C0*R) (hV : |V| ≤ C0*R)
    (ht : |t| ≤ C0*R) (hu : |u| ≤ C0*R) :
    |16*(U^3*t^2+V^3*u^2)| ≤ 32*C0^5*R^5 := by
  calc
    |16*(U^3*t^2+V^3*u^2)| =
        16*|U^3*t^2+V^3*u^2| := by rw [abs_mul]; norm_num
    _ ≤ 16*(|U^3*t^2|+|V^3*u^2|) :=
      mul_le_mul_of_nonneg_left (abs_add_le _ _) (by norm_num)
    _ = 16*(|U|^3*|t|^2+|V|^3*|u|^2) := by simp only [abs_mul,abs_pow]
    _ ≤ 16*((C0*R)^3*(C0*R)^2+(C0*R)^3*(C0*R)^2) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply add_le_add
      · exact mul_le_mul (pow_le_pow_left₀ (abs_nonneg U) hU _)
          (pow_le_pow_left₀ (abs_nonneg t) ht _) (by positivity) (by positivity)
      · exact mul_le_mul (pow_le_pow_left₀ (abs_nonneg V) hV _)
          (pow_le_pow_left₀ (abs_nonneg u) hu _) (by positivity) (by positivity)
    _ = _ := by ring

#print axioms quadratic_height_window
#print axioms quadratic_trace_coefficient_bound
end
end A3ActualTraceDerivatives

namespace A3ActualTraceDerivatives
noncomputable section
set_option maxHeartbeats 1000000

lemma fixed_threshold_gate
    {R C T K : ℝ} (hR : 1 ≤ R) (hC0 : 0 ≤ C)
    (hKC : K ≤ C) (hT : C*R^64 ≤ T)
    (j : ℕ) (hj : j ≤ 64) : K*R^j ≤ T := by
  calc
    K*R^j ≤ C*R^j := mul_le_mul_of_nonneg_right hKC (by positivity)
    _ ≤ C*R^64 := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hR hj) hC0
    _ ≤ T := hT

lemma factor_perturbation
    (V t z c0 C0 U R c : ℝ)
    (hU : 1 ≤ U) (hR : 1 ≤ R) (hUR : U ≤ R)
    (hc0 : 0 < c0) (hC0 : 1 ≤ C0) (hc : 0 < c)
    (hc1 : c ≤ 1) (hcsmall : c ≤ c0/(2*C0))
    (hV : c0/U ≤ |V| ∧ |V| ≤ C0*U)
    (ht : |t| ≤ C0*U) (hz : |z| ≤ c/R^30) :
    c0/(2*U) ≤ |V+t*z| ∧ |V+t*z| ≤ 2*C0*U := by
  have hU0 : 0 < U := by linarith
  have hR0 : 0 < R := by linarith
  have hC00 : 0 < C0 := by linarith
  have hz1 : |z| ≤ 1 := hz.trans
    ((div_le_one (pow_pos hR0 _)).2 (hc1.trans (one_le_pow₀ hR)))
  have hU2 : U^2 ≤ R^30 :=
    (pow_le_pow_left₀ hU0.le hUR 2).trans (pow_le_pow_right₀ hR (by omega))
  have hrat : U/R^30 ≤ 1/U :=
    (div_le_div_iff₀ (pow_pos hR0 _) hU0).2 (by simpa [pow_two] using hU2)
  have hcC : C0*c ≤ c0/2 := by
    have hh := (le_div_iff₀ (by positivity : 0<2*C0)).1 hcsmall
    linarith
  have hpert : |t*z| ≤ c0/(2*U) := by
    calc
      |t*z| = |t| * |z| := abs_mul _ _
      _ ≤ (C0*U)*(c/R^30) :=
        mul_le_mul ht hz (abs_nonneg z) (by positivity)
      _ = (C0*c)*(U/R^30) := by ring
      _ ≤ (c0/2)*(U/R^30) := mul_le_mul_of_nonneg_right hcC (by positivity)
      _ ≤ (c0/2)*(1/U) := mul_le_mul_of_nonneg_left hrat (by positivity)
      _ = _ := by ring
  have hnear : |(V+t*z)-V| ≤ c0/(2*U) := by
    simpa only [add_sub_cancel_left] using hpert
  have hreverse : |V|-|V+t*z| ≤ c0/(2*U) := by
    apply (abs_sub_abs_le_abs_sub V (V+t*z)).trans
    simpa only [abs_sub_comm] using hnear
  have hhalf : c0/U = 2*(c0/(2*U)) := by ring
  constructor
  · linarith [hV.1]
  · calc
      |V+t*z| ≤ |V|+|t*z| := abs_add_le _ _
      _ ≤ C0*U+(C0*U)*1 := add_le_add hV.2 (by
        rw [abs_mul]
        exact mul_le_mul ht hz1 (abs_nonneg z) (by positivity))
      _ = _ := by ring

end
end A3ActualTraceDerivatives

namespace A3ActualTraceDerivatives
noncomputable section
set_option maxHeartbeats 2000000

theorem nearby_zero_from_owned_partials : NearbyZeroFromOwnedPartials := by
  intro hPart b hb c0 C0 hc0 hC0
  obtain ⟨m,J,hm,hJ,hfirst⟩ := hPart b hb c0 C0 hc0 hC0
  obtain ⟨m2,J2,hm2,hJ2,hsecond⟩ :=
    hPart b hb (c0/2) (2*C0) (by positivity) (by linarith)
  have hC00 : 0 < C0 := by linarith
  let c : ℝ := min 1 (min m2 (c0/(2*C0)))
  have hc : 0 < c := lt_min (by norm_num) (lt_min hm2 (by positivity))
  have hc1 : c ≤ 1 := min_le_left _ _
  have hcm2 : c ≤ m2 := (min_le_right _ _).trans (min_le_left _ _)
  have hcsmall : c ≤ c0/(2*C0) := (min_le_right _ _).trans (min_le_right _ _)
  let K1 : ℝ := 128*C0^6/m^2
  let K2 : ℝ := 2*C0/(m*c)
  let P : ℝ := 2*C0/m
  have hK1 : 0 ≤ K1 := by dsimp [K1]; positivity
  have hK2 : 0 ≤ K2 := by dsimp [K2]; positivity
  have hP : 0 ≤ P := by dsimp [P]; positivity
  let C : ℝ := 1+J+J2+K1+K2+P
  have hC : 1 ≤ C := by dsimp [C]; linarith
  have hJC : J ≤ C := by dsimp [C]; linarith
  have hJ2C : J2 ≤ C := by dsimp [C]; linarith
  have hK1C : K1 ≤ C := by dsimp [C]; linarith
  have hK2C : K2 ≤ C := by dsimp [C]; linarith
  have hPC : P ≤ C := by dsimp [C]; linarith
  refine ⟨c,C,hc,hc1,hC,?_⟩
  intro L hL T hT pp pm qp qm rp rm tp tm s w
    hcoeff hdetY hdetX hUp hUm hVp hVm hres
  have hL1 : 1 ≤ L := by linarith
  have hL0 : 0 < L := by linarith
  let U : ℝ := L^b
  let R : ℝ := L^(b+1)
  have hU : 1 ≤ U := one_le_pow₀ hL1
  have hR : 1 ≤ R := one_le_pow₀ hL1
  have hU0 : 0 < U := by linarith
  have hR0 : 0 < R := by linarith
  have hUR : U ≤ R := pow_le_pow_right₀ hL1 (by omega)
  have hCR0 : 0 ≤ C := by linarith
  have powerR (j : ℕ) : R^j=L^(j*(b+1)) := by
    dsimp [R]
    rw [←pow_mul]
    congr 1
    exact Nat.mul_comm _ _
  have hTR : C*R^64 ≤ T := by simpa only [powerR] using hT
  have hT0 : 0 < T :=
    (mul_pos (by linarith : 0<C) (pow_pos hR0 _)).trans_le hTR
  have hFirstThreshold : J*L^(16*(b+1)) ≤ T := by
    rw [←powerR 16]
    exact fixed_threshold_gate hR hCR0 hJC hTR 16 (by omega)
  have hSecondThreshold : J2*L^(16*(b+1)) ≤ T := by
    rw [←powerR 16]
    exact fixed_threshold_gate hR hCR0 hJ2C hTR 16 (by omega)
  have hparts := hfirst L hL T hFirstThreshold
    pp pm qp qm rp rm tp tm s w hcoeff hdetY hdetX hUp hUm hVp hVm hres
  let Up : ℝ := pp+qp*s
  let Um : ℝ := pm+qm*s
  let Vp : ℝ := rp+tp*w
  let Vm : ℝ := rm+tm*w
  let a : ℝ := 16*(Up^3*tp^2+Um^3*tm^2)
  let beta : ℝ := 32*(Up^3*Vp*tp+Um^3*Vm*tm)
  let d : ℝ := tracePhi pp pm qp qm rp rm tp tm s w
  have hbeta : m/L^(6*b+10) ≤ |beta| := by
    simpa only [trace_w_derivative,beta,Up,Um,Vp,Vm] using hparts.2
  have hden : L^(6*b+10) ≤ R^8 := by
    rw [powerR]
    exact pow_le_pow_right₀ hL1 (by omega)
  have hbetaR : m/R^8 ≤ |beta| := by
    apply le_trans _ hbeta
    apply (div_le_div_iff₀ (pow_pos hR0 _) (pow_pos hL0 _)).2
    exact mul_le_mul_of_nonneg_left hden hm.le
  have hcoeff0 := hcoeff
  rcases hcoeff with ⟨hpp,hpm,hqp,hqm,hrp,hrm,htp,htm⟩
  have hC0UR : C0*U ≤ C0*R := mul_le_mul_of_nonneg_left hUR hC00.le
  have ha : |a| ≤ 32*C0^5*R^5 := by
    exact quadratic_trace_coefficient_bound Up Um tp tm C0 R hC00.le hR0.le
      (hUp.2.trans hC0UR) (hUm.2.trans hC0UR)
      (htp.trans hC0UR) (htm.trans hC0UR)
  have hpow5 : L^(5*b) ≤ R^5 := by
    rw [powerR]
    exact pow_le_pow_right₀ hL1 (by omega)
  have hd : |d| ≤ C0*R^5/T := by
    apply hres.trans
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hpow5 hC00.le) hT0.le
  have hGate1 : K1*R^26 ≤ T :=
    fixed_threshold_gate hR hCR0 hK1C hTR 26 (by omega)
  have hGate2 : K2*R^43 ≤ T :=
    fixed_threshold_gate hR hCR0 hK2C hTR 43 (by omega)
  obtain ⟨z,hzero,hzr,hzd⟩ :=
    quadratic_height_window a beta d R T C0 m c C
      hR hC00 hm hc hT0 ha hbetaR hd hGate1 hGate2 hPC
  have hUp0 : c0/(2*U) ≤ |Up| ∧ |Up| ≤ 2*C0*U := by
    have hh : c0/U=2*(c0/(2*U)) := by ring
    have hnonneg : 0 ≤ c0/(2*U) := by positivity
    have hnonneg2 : 0 ≤ C0*U := by positivity
    constructor <;> linarith [hUp.1,hUp.2]
  have hUm0 : c0/(2*U) ≤ |Um| ∧ |Um| ≤ 2*C0*U := by
    have hh : c0/U=2*(c0/(2*U)) := by ring
    have hnonneg : 0 ≤ c0/(2*U) := by positivity
    have hnonneg2 : 0 ≤ C0*U := by positivity
    constructor <;> linarith [hUm.1,hUm.2]
  have hVp0 : c0/(2*U) ≤ |rp+tp*(w+z)| ∧ |rp+tp*(w+z)| ≤ 2*C0*U := by
    have heq : rp+tp*(w+z)=Vp+tp*z := by dsimp [Vp]; ring
    rw [heq]
    exact factor_perturbation Vp tp z c0 C0 U R c
      hU hR hUR hc0 hC0 hc hc1 hcsmall hVp htp hzr
  have hVm0 : c0/(2*U) ≤ |rm+tm*(w+z)| ∧ |rm+tm*(w+z)| ≤ 2*C0*U := by
    have heq : rm+tm*(w+z)=Vm+tm*z := by dsimp [Vm]; ring
    rw [heq]
    exact factor_perturbation Vm tm z c0 C0 U R c
      hU hR hUR hc0 hC0 hc hc1 hcsmall hVm htm hzr
  have htracezero : tracePhi pp pm qp qm rp rm tp tm s (w+z)=0 := by
    rw [trace_w_taylor]
    simpa only [a,beta,d,Up,Um,Vp,Vm] using hzero
  have hdouble (v : ℝ) (hv : |v| ≤ C0*L^b) : |v| ≤ (2*C0)*L^b := by
    have hn : 0 ≤ C0*L^b := by positivity
    linarith
  have hnewcoeff :
      |pp|≤(2*C0)*L^b ∧ |pm|≤(2*C0)*L^b ∧
      |qp|≤(2*C0)*L^b ∧ |qm|≤(2*C0)*L^b ∧
      |rp|≤(2*C0)*L^b ∧ |rm|≤(2*C0)*L^b ∧
      |tp|≤(2*C0)*L^b ∧ |tm|≤(2*C0)*L^b :=
    ⟨hdouble pp hpp,hdouble pm hpm,hdouble qp hqp,hdouble qm hqm,
      hdouble rp hrp,hdouble rm hrm,hdouble tp htp,hdouble tm htm⟩
  have hNewUp : (c0/2)/L^b ≤ |pp+qp*s| ∧ |pp+qp*s| ≤ (2*C0)*L^b := by
    simpa only [U,Up,div_div] using hUp0
  have hNewUm : (c0/2)/L^b ≤ |pm+qm*s| ∧ |pm+qm*s| ≤ (2*C0)*L^b := by
    simpa only [U,Um,div_div] using hUm0
  have hNewVp : (c0/2)/L^b ≤ |rp+tp*(w+z)| ∧ |rp+tp*(w+z)| ≤ (2*C0)*L^b := by
    simpa only [U,div_div] using hVp0
  have hNewVm : (c0/2)/L^b ≤ |rm+tm*(w+z)| ∧ |rm+tm*(w+z)| ≤ (2*C0)*L^b := by
    simpa only [U,div_div] using hVm0
  have hnewparts := hsecond L hL T hSecondThreshold pp pm qp qm rp rm tp tm s (w+z)
    hnewcoeff hdetY hdetX hNewUp hNewUm hNewVp hNewVm
    (by rw [htracezero,abs_zero]; positivity)
  have hpartialsmaller : c/L^(6*b+10) ≤ m2/L^(6*b+10) :=
    div_le_div_of_nonneg_right hcm2 (by positivity)
  refine ⟨w+z,htracezero,?_,?_,hUp0,hUm0,hVp0,hVm0,
    hpartialsmaller.trans hnewparts.1,hpartialsmaller.trans hnewparts.2⟩
  · simpa only [add_sub_cancel_left,powerR] using hzr
  · simpa only [add_sub_cancel_left,powerR] using hzd

#print axioms nearby_zero_from_owned_partials
end
end A3ActualTraceDerivatives

namespace A3ActualTraceDerivatives
theorem actual_point_nearby_zero : ActualPointNearbyZero :=
  nearby_zero_from_owned_partials actual_point_partial_lower_bound
end A3ActualTraceDerivatives
#print axioms A3ActualTraceDerivatives.actual_point_nearby_zero

theorem JocelynClaims.claim_70b2552e0f57232a0031656a3df0e3857d8e732f50cb0228a418af0101c04e33 :
  let tracePhi : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ :=
   (fun pPlus pMinus qPlus qMinus rPlus rMinus tPlus tMinus s w =>
    16 * ((pPlus+qPlus*s)^3*(rPlus+tPlus*w)^2+
      (pMinus+qMinus*s)^3*(rMinus+tMinus*w)^2))
  ∀ b : ℕ, 1 ≤ b →
    ∀ c0 C0 : ℝ, 0 < c0 → 1 ≤ C0 →
    ∃ c C : ℝ, 0 < c ∧ c ≤ 1 ∧ 1 ≤ C ∧
      ∀ L : ℝ, 2 ≤ L →
      ∀ T : ℝ, C * L ^ (64 * (b + 1)) ≤ T →
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
        ∃ w0 : ℝ,
          tracePhi pPlus pMinus qPlus qMinus rPlus rMinus tPlus tMinus s w0 = 0 ∧
          |w0 - w| ≤ c / L ^ (30 * (b + 1)) ∧
          |w0 - w| ≤ C * L ^ (20 * (b + 1)) / T ∧
          (c0 / (2 * L ^ b) ≤ |pPlus + qPlus * s| ∧
            |pPlus + qPlus * s| ≤ 2 * C0 * L ^ b) ∧
          (c0 / (2 * L ^ b) ≤ |pMinus + qMinus * s| ∧
            |pMinus + qMinus * s| ≤ 2 * C0 * L ^ b) ∧
          (c0 / (2 * L ^ b) ≤ |rPlus + tPlus * w0| ∧
            |rPlus + tPlus * w0| ≤ 2 * C0 * L ^ b) ∧
          (c0 / (2 * L ^ b) ≤ |rMinus + tMinus * w0| ∧
            |rMinus + tMinus * w0| ≤ 2 * C0 * L ^ b) ∧
          c / L ^ (6 * b + 10) ≤
            |deriv (fun z : ℝ =>
              tracePhi pPlus pMinus qPlus qMinus rPlus rMinus tPlus tMinus z w0) s| ∧
          c / L ^ (6 * b + 10) ≤
            |deriv (fun z : ℝ =>
              tracePhi pPlus pMinus qPlus qMinus rPlus rMinus tPlus tMinus s z) w0| := by
  change A3ActualTraceDerivatives.ActualPointNearbyZero
  exact A3ActualTraceDerivatives.actual_point_nearby_zero
#print axioms JocelynClaims.claim_70b2552e0f57232a0031656a3df0e3857d8e732f50cb0228a418af0101c04e33
