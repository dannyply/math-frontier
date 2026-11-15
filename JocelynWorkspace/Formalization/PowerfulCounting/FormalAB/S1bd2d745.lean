-- Source SHA-256: a6dc85796116e1a037163038dd13634655108317e7ae8be6bea2170dca24e4bc
import Mathlib
import JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.LemmaP

namespace FormalAB.S1bd2d745

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

namespace JocelynClaims

theorem claim_5116a9f79d2da2bf6321ca2ae10f925d8b9676b4d6a4f32c6b308a84d70b3e0c :
    (let tracePhi : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ := (fun pPlus pMinus qPlus qMinus rPlus rMinus tPlus tMinus s w => 16 * ((pPlus + qPlus * s) ^ 3 * (rPlus + tPlus * w) ^ 2 + (pMinus + qMinus * s) ^ 3 * (rMinus + tMinus * w) ^ 2)); ∀ b : ℕ, 1 ≤ b → ∀ c0 C0 : ℝ, 0 < c0 → 1 ≤ C0 → ∃ c C : ℝ, 0 < c ∧ 1 ≤ C ∧ ∀ L : ℝ, 2 ≤ L → ∀ T : ℝ, C * L ^ (16 * (b + 1)) ≤ T → ∀ pPlus pMinus qPlus qMinus rPlus rMinus tPlus tMinus : ℝ, ∀ s w : ℝ, (|pPlus| ≤ C0 * L ^ b ∧ |pMinus| ≤ C0 * L ^ b ∧ |qPlus| ≤ C0 * L ^ b ∧ |qMinus| ≤ C0 * L ^ b ∧ |rPlus| ≤ C0 * L ^ b ∧ |rMinus| ≤ C0 * L ^ b ∧ |tPlus| ≤ C0 * L ^ b ∧ |tMinus| ≤ C0 * L ^ b) → 1 ≤ |pPlus * qMinus - pMinus * qPlus| → 1 ≤ |rPlus * tMinus - rMinus * tPlus| → (c0 / L ^ b ≤ |pPlus + qPlus * s| ∧ |pPlus + qPlus * s| ≤ C0 * L ^ b) → (c0 / L ^ b ≤ |pMinus + qMinus * s| ∧ |pMinus + qMinus * s| ≤ C0 * L ^ b) → (c0 / L ^ b ≤ |rPlus + tPlus * w| ∧ |rPlus + tPlus * w| ≤ C0 * L ^ b) → (c0 / L ^ b ≤ |rMinus + tMinus * w| ∧ |rMinus + tMinus * w| ≤ C0 * L ^ b) → |tracePhi pPlus pMinus qPlus qMinus rPlus rMinus tPlus tMinus s w| ≤ C0 * L ^ (5 * b) / T → c / L ^ (6 * b + 10) ≤ |deriv (fun z : ℝ => tracePhi pPlus pMinus qPlus qMinus rPlus rMinus tPlus tMinus z w) s| ∧ c / L ^ (6 * b + 10) ≤ |deriv (fun z : ℝ => tracePhi pPlus pMinus qPlus qMinus rPlus rMinus tPlus tMinus s z) w|) := by
  change A3ActualTraceDerivatives.ActualPointPartialLowerBound
  exact A3ActualTraceDerivatives.actual_point_partial_lower_bound

end JocelynClaims

#print axioms A3ActualTraceDerivatives.actual_point_partial_lower_bound
#print axioms JocelynClaims.claim_5116a9f79d2da2bf6321ca2ae10f925d8b9676b4d6a4f32c6b308a84d70b3e0c
