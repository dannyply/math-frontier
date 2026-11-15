-- Source SHA-256: 37e3275810e70739ca20b40d07e24b1e6d5328bcedc3f57d9d214caad35cef2a
import Mathlib
import JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.LemmaP
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB

namespace FormalAB.S5a5b0bd5

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

set_option maxHeartbeats 1000000
set_option maxRecDepth 4000
namespace A5PoweredRangeRecoveryRoot

theorem scale_six (x M W : ℝ) (hx : 0 < x) (hM : 0 < M) (hW : 0 < W) :
    (Real.sqrt x / (Real.sqrt M * W ^ ((1 : ℝ) / 3))) ^ 6 * M ^ 3 * W ^ 2 = x ^ 3 := by
  have hw3 : (W ^ ((1 : ℝ) / 3)) ^ (3 : ℕ) = W := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hW.le]
    norm_num
  have hw6 : (W ^ ((1 : ℝ) / 3)) ^ (6 : ℕ) = W ^ 2 := by
    calc
      _ = ((W ^ ((1 : ℝ) / 3)) ^ (3 : ℕ)) ^ (2 : ℕ) := by ring
      _ = W ^ 2 := by rw [hw3]
  have hx6 : (Real.sqrt x) ^ 6 = x ^ 3 := by
    calc
      _ = ((Real.sqrt x) ^ 2) ^ 3 := by ring
      _ = x ^ 3 := by rw [Real.sq_sqrt hx.le]
  have hm6 : (Real.sqrt M) ^ 6 = M ^ 3 := by
    calc
      _ = ((Real.sqrt M) ^ 2) ^ 3 := by ring
      _ = M ^ 3 := by rw [Real.sq_sqrt hM.le]
  rw [div_pow, mul_pow, hx6, hm6, hw6]
  field_simp

theorem range_cube (x M W c : ℝ) (hx : 1 ≤ x) (_hM : 0 < M)
    (hW : 0 < W) (hc : 0 < c)
    (hr1 : c ^ 3 * W ^ 4 ≤ M ^ 3 * x)
    (hr2 : c ^ 3 * x ^ 4 ≤ M ^ 3 * W ^ 4) :
    c ^ 3 * W ^ 2 ≤ M ^ 3 := by
  by_cases h : x ≤ W ^ 2
  · have hp := mul_le_mul_of_nonneg_left h (show 0 ≤ c ^ 3 * W ^ 2 by positivity)
    have hh : (c ^ 3 * W ^ 2) * x ≤ M ^ 3 * x := by
      nlinarith only [hp, hr1]
    exact (mul_le_mul_iff_left₀ (show 0 < x by linarith)).mp (by nlinarith only [hh])
  · have hw6 : W ^ 6 ≤ x ^ 3 := by
      have ht := pow_le_pow_left₀ (sq_nonneg W) (le_of_lt (lt_of_not_ge h)) 3
      nlinarith only [ht]
    have hxx : x ^ 3 ≤ x ^ 4 := by
      have ht := mul_le_mul_of_nonneg_left hx (show 0 ≤ x ^ 3 by positivity)
      nlinarith only [ht]
    have hh : (c ^ 3 * W ^ 2) * W ^ 4 ≤ M ^ 3 * W ^ 4 := by
      calc
        _ = c ^ 3 * W ^ 6 := by ring
        _ ≤ c ^ 3 * x ^ 3 := mul_le_mul_of_nonneg_left hw6 (by positivity)
        _ ≤ c ^ 3 * x ^ 4 := mul_le_mul_of_nonneg_left hxx (by positivity)
        _ ≤ _ := hr2
    exact (mul_le_mul_iff_left₀ (show 0 < W ^ 4 by positivity)).mp (by nlinarith only [hh])

theorem cancel_right (a b d : ℝ) (hd : 0 < d) (h : a * d ≤ b * d) :
    a ≤ b :=
  (mul_le_mul_iff_left₀ hd).mp (by nlinarith only [h])

theorem coarse_powered (K c x M W L : ℝ)
    (hK : 1 ≤ K) (hc : 0 < c) (hx : 2 ≤ x) (hM : 0 < M) (hW : 0 < W)
    (hL : 0 ≤ L) (hWx : W ≤ K * x)
    (hr1 : c ^ 3 * W ^ 4 ≤ M ^ 3 * x)
    (hr2 : c ^ 3 * x ^ 4 ≤ M ^ 3 * W ^ 4)
    (hcase : L ^ 3 * M ^ 3 ≤ K * x * W ∨
       L ^ 2 * M ^ 2 ≤ K * W ∨
       L ^ 2 * M ^ 2 ≤ K * x ∨
       L ^ 6 * M ^ 3 * W ^ 2 ≤ K * x ^ 3 ∨
       L ^ 11 * M ^ 3 * W ^ 4 ≤ K * x ^ 4) :
    L ^ 6 * M ^ 3 * W ^ 2 ≤ (K ^ 4 / c ^ 3 + K + 1) * x ^ 3 ∨
      L ^ 11 ≤ K / c ^ 3 := by
  have hc3 : 0 < c ^ 3 := by positivity
  have hK0 : 0 ≤ K := by linarith
  have hx0 : 0 ≤ x := by linarith
  have hK24 : K ^ 2 ≤ K ^ 4 := by
    have hp : 1 ≤ K ^ 2 := one_le_pow₀ hK
    have hh := mul_le_mul_of_nonneg_left hp (sq_nonneg K)
    nlinarith only [hh]
  have hK34 : K ^ 3 ≤ K ^ 4 := by
    have hh := mul_le_mul_of_nonneg_left hK (show 0 ≤ K ^ 3 by positivity)
    nlinarith only [hh]
  let T : ℝ := L ^ 6 * M ^ 3 * W ^ 2
  have toA (h : c ^ 3 * T ≤ K ^ 4 * x ^ 3) :
      T ≤ (K ^ 4 / c ^ 3 + K + 1) * x ^ 3 := by
    have hd : T ≤ K ^ 4 * x ^ 3 / c ^ 3 :=
      (le_div_iff₀ hc3).2 (by nlinarith only [h])
    calc
      T ≤ K ^ 4 * x ^ 3 / c ^ 3 := hd
      _ = (K ^ 4 / c ^ 3) * x ^ 3 := by ring
      _ ≤ (K ^ 4 / c ^ 3 + K + 1) * x ^ 3 :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  rcases hcase with h | h | h | h | h
  · have hp2 := pow_le_pow_left₀ (by positivity : 0 ≤ L ^ 3 * M ^ 3) h 2
    have hp2x := mul_le_mul_of_nonneg_right hp2 hx0
    have hR := mul_le_mul_of_nonneg_left hr1 (show 0 ≤ L ^ 6 * M ^ 3 by positivity)
    have hh : (c ^ 3 * T) * W ^ 2 ≤ (K ^ 2 * x ^ 3) * W ^ 2 := by
      dsimp only [T]
      nlinarith only [hp2x, hR]
    have hb := cancel_right (c ^ 3 * T) (K ^ 2 * x ^ 3) (W ^ 2)
      (by positivity) hh
    have hb4 : c ^ 3 * T ≤ K ^ 4 * x ^ 3 :=
      hb.trans (mul_le_mul_of_nonneg_right hK24 (by positivity))
    exact Or.inl (toA hb4)
  · have hp3 := pow_le_pow_left₀ (by positivity : 0 ≤ L ^ 2 * M ^ 2) h 3
    have hp3x := mul_le_mul_of_nonneg_right hp3 hx0
    have hR := mul_le_mul_of_nonneg_left hr1 (show 0 ≤ L ^ 6 * M ^ 3 by positivity)
    have hh : (c ^ 3 * T) * W ^ 2 ≤ (K ^ 3 * W * x) * W ^ 2 := by
      dsimp only [T]
      nlinarith only [hp3x, hR]
    have hb := cancel_right (c ^ 3 * T) (K ^ 3 * W * x) (W ^ 2)
      (by positivity) hh
    have hprod := mul_le_mul_of_nonneg_left hWx (show 0 ≤ K ^ 3 * x by positivity)
    have hxx : x ^ 2 ≤ x ^ 3 := by
      have hp := mul_le_mul_of_nonneg_left (show 1 ≤ x by linarith) (sq_nonneg x)
      nlinarith only [hp]
    have hb4 : c ^ 3 * T ≤ K ^ 4 * x ^ 3 := by
      calc
        c ^ 3 * T ≤ K ^ 3 * W * x := hb
        _ ≤ K ^ 4 * x ^ 2 := by nlinarith only [hprod]
        _ ≤ K ^ 4 * x ^ 3 := mul_le_mul_of_nonneg_left hxx (by positivity)
    exact Or.inl (toA hb4)
  · have hp3 := pow_le_pow_left₀ (by positivity : 0 ≤ L ^ 2 * M ^ 2) h 3
    have hrange := range_cube x M W c (by linarith) hM hW hc hr1 hr2
    have hR := mul_le_mul_of_nonneg_left hrange (show 0 ≤ L ^ 6 * M ^ 3 by positivity)
    have hb : c ^ 3 * T ≤ K ^ 3 * x ^ 3 := by
      dsimp only [T]
      nlinarith only [hp3, hR]
    have hb4 : c ^ 3 * T ≤ K ^ 4 * x ^ 3 :=
      hb.trans (mul_le_mul_of_nonneg_right hK34 (by positivity))
    exact Or.inl (toA hb4)
  · have hp : 0 ≤ K ^ 4 / c ^ 3 := by positivity
    have hcoef : K ≤ K ^ 4 / c ^ 3 + K + 1 := by linarith
    exact Or.inl (h.trans (mul_le_mul_of_nonneg_right hcoef (by positivity)))
  · have hR := mul_le_mul_of_nonneg_left hr2 (show 0 ≤ L ^ 11 by positivity)
    have hh : (c ^ 3 * L ^ 11) * x ^ 4 ≤ K * x ^ 4 := by
      nlinarith only [hR, h]
    have hb := cancel_right (c ^ 3 * L ^ 11) K (x ^ 4) (by positivity) hh
    exact Or.inr ((le_div_iff₀ hc3).2 (by nlinarith only [hb]))

theorem length_recovery :
∀ K c : ℝ, 1 ≤ K → 0 < c →
  ∃ C : ℝ, 1 ≤ C ∧
    ∀ x M W L : ℝ, 2 ≤ x → 0 < M → 0 < W → 0 ≤ L →
      W ≤ K * x →
      c ^ 3 * W ^ 4 ≤ M ^ 3 * x →
      c ^ 3 * x ^ 4 ≤ M ^ 3 * W ^ 4 →
      (L ^ 3 * M ^ 3 ≤ K * x * W ∨
       L ^ 2 * M ^ 2 ≤ K * W ∨
       L ^ 2 * M ^ 2 ≤ K * x ∨
       L ^ 6 * M ^ 3 * W ^ 2 ≤ K * x ^ 3 ∨
       L ^ 11 * M ^ 3 * W ^ 4 ≤ K * x ^ 4) →
      L ≤ C * (1 + Real.sqrt x /
        (Real.sqrt M * W ^ ((1 : ℝ) / 3)))
 := by
  intro K c hK hc
  let A : ℝ := K ^ 4 / c ^ 3 + K + 1
  let C : ℝ := A + K / c ^ 3 + 2
  have hK0 : 0 ≤ K := by linarith
  have hd : 0 ≤ K ^ 4 / c ^ 3 := by positivity
  have he : 0 ≤ K / c ^ 3 := by positivity
  have hA1 : 1 ≤ A := by dsimp only [A]; linarith
  have hC1 : 1 ≤ C := by dsimp only [C]; linarith
  have hCA : A ≤ C := by dsimp only [C]; linarith
  have hCB : K / c ^ 3 ≤ C := by dsimp only [C]; linarith
  have hC6 : C ≤ C ^ 6 := by
    have hp : 1 ≤ C ^ 5 := one_le_pow₀ hC1
    have hh := mul_le_mul_of_nonneg_left hp (show 0 ≤ C by linarith)
    nlinarith only [hh]
  have hC11 : C ≤ C ^ 11 := by
    have hp : 1 ≤ C ^ 10 := one_le_pow₀ hC1
    have hh := mul_le_mul_of_nonneg_left hp (show 0 ≤ C by linarith)
    nlinarith only [hh]
  refine ⟨C, hC1, ?_⟩
  intro x M W L hx hM hW hL hWx hr1 hr2 hcase
  let Z : ℝ := Real.sqrt x / (Real.sqrt M * W ^ ((1 : ℝ) / 3))
  have hZ : 0 ≤ Z := by dsimp only [Z]; positivity
  have hscale : Z ^ 6 * M ^ 3 * W ^ 2 = x ^ 3 :=
    scale_six x M W (by linarith) hM hW
  have hcZ : 0 ≤ C * Z := mul_nonneg (by linarith) hZ
  have hrec := coarse_powered K c x M W L hK hc hx hM hW hL hWx hr1 hr2 hcase
  rcases hrec with hpow | hstat
  · have hA6 : A ≤ C ^ 6 := hCA.trans hC6
    have hh : L ^ 6 * (M ^ 3 * W ^ 2) ≤ (C * Z) ^ 6 * (M ^ 3 * W ^ 2) := by
      calc
        _ = L ^ 6 * M ^ 3 * W ^ 2 := by ring
        _ ≤ A * x ^ 3 := hpow
        _ ≤ C ^ 6 * x ^ 3 := mul_le_mul_of_nonneg_right hA6 (by positivity)
        _ = C ^ 6 * (Z ^ 6 * M ^ 3 * W ^ 2) := by rw [hscale]
        _ = _ := by ring
    have hl6 : L ^ 6 ≤ (C * Z) ^ 6 :=
      cancel_right _ _ _ (by positivity) hh
    have hl : L ≤ C * Z :=
      le_of_pow_le_pow_left₀ (by norm_num : (6 : ℕ) ≠ 0) hcZ hl6
    exact hl.trans (by change C * Z ≤ C * (1 + Z); nlinarith only [hC1])
  · have hL11 : L ^ 11 ≤ C ^ 11 := hstat.trans (hCB.trans hC11)
    have hl : L ≤ C :=
      le_of_pow_le_pow_left₀ (by norm_num : (11 : ℕ) ≠ 0) (by linarith) hL11
    exact hl.trans (by change C ≤ C * (1 + Z); nlinarith only [hcZ])

#print axioms length_recovery
end A5PoweredRangeRecoveryRoot

theorem JocelynClaims.claim_14815d4dd0678e1313331e16716225b64fac0c3a8277eb5dc212df6b7eb966f6 :
∀ K c : ℝ, 1 ≤ K → 0 < c →
  ∃ C : ℝ, 1 ≤ C ∧
    ∀ x M W L : ℝ, 2 ≤ x → 0 < M → 0 < W → 0 ≤ L →
      W ≤ K * x →
      c ^ 3 * W ^ 4 ≤ M ^ 3 * x →
      c ^ 3 * x ^ 4 ≤ M ^ 3 * W ^ 4 →
      (L ^ 3 * M ^ 3 ≤ K * x * W ∨
       L ^ 2 * M ^ 2 ≤ K * W ∨
       L ^ 2 * M ^ 2 ≤ K * x ∨
       L ^ 6 * M ^ 3 * W ^ 2 ≤ K * x ^ 3 ∨
       L ^ 11 * M ^ 3 * W ^ 4 ≤ K * x ^ 4) →
      L ≤ C * (1 + Real.sqrt x /
        (Real.sqrt M * W ^ ((1 : ℝ) / 3)))
 := by
  exact A5PoweredRangeRecoveryRoot.length_recovery
#print axioms JocelynClaims.claim_14815d4dd0678e1313331e16716225b64fac0c3a8277eb5dc212df6b7eb966f6

namespace A5CoarseOriginalPointRoot
set_option maxHeartbeats 1500000

theorem primitive_zero_square
    (a b : ℤ) (d e m : ℝ)
    (hprim : Int.gcd a b = 1)
    (hm : m = (a : ℝ) * d + (b : ℝ) * e)
    (hab : a * b = 0) :
    m ^ 2 = d ^ 2 ∨ m ^ 2 = e ^ 2 := by
  rcases mul_eq_zero.mp hab with ha | hb
  · have hn : b.natAbs = 1 := by simpa only [ha, Int.gcd_zero_left] using hprim
    rcases Int.natAbs_eq_iff.mp hn with hb | hb
    · right
      rw [hm, ha, hb]
      norm_num
    · right
      rw [hm, ha, hb]
      norm_num
  · have hn : a.natAbs = 1 := by simpa only [hb, Int.gcd_zero_right] using hprim
    rcases Int.natAbs_eq_iff.mp hn with ha | ha
    · left
      rw [hm, ha, hb]
      norm_num
    · left
      rw [hm, ha, hb]
      norm_num

theorem coarse_powered_choices
    (C₀ x M W m J L : ℝ) (a b : ℤ) (d e : ℝ)
    (_hC₀ : 0 < C₀) (hx : 2 ≤ x) (hM : 0 < M) (hW : 0 < W)
    (hm : m ≠ 0) (hJ : 1 ≤ J) (hL : 0 ≤ L)
    (hcell : L * |m| * J * M ≤ C₀ * W)
    (hprim : Int.gcd a b = 1) (hd : 0 < d) (he : 0 < e)
    (hlevel : m = (a : ℝ) * d + (b : ℝ) * e)
    (hprod : W / 4 ≤ d * e) (hd2 : d ^ 2 ≤ x) (he2 : e ^ 2 ≤ 2 * x)
    (hcoarse : (1 / 100000 : ℝ) * W ^ 2 ≤ |m| ^ 3 * x ∨
      (1 / 100000 : ℝ) * |((a * b : ℤ) : ℝ)| * W ≤ m ^ 2) :
    L ^ 3 * M ^ 3 ≤ (100000 * C₀ ^ 3) * x * W ∨
    L ^ 2 * M ^ 2 ≤ (100000 * C₀ ^ 2) * W ∨
    L ^ 2 * M ^ 2 ≤ (32 * C₀ ^ 2) * x := by
  have hx0 : 0 < x := by linarith
  have hmu : 0 < |m| := abs_pos.mpr hm
  have hJdrop := mul_le_mul_of_nonneg_left hJ
    (show 0 ≤ L * |m| * M by positivity)
  have hcell0 : L * |m| * M ≤ C₀ * W := by
    nlinarith only [hcell, hJdrop]
  have hp2 := pow_le_pow_left₀
    (show 0 ≤ L * |m| * M by positivity) hcell0 2
  simp only [mul_pow, sq_abs] at hp2
  by_cases hab : a * b = 0
  · right; right
    have hWde : W ≤ 4 * d * e := by linarith only [hprod]
    have hpde := pow_le_pow_left₀ hW.le hWde 2
    have hWsq : W ^ 2 ≤ 16 * d ^ 2 * e ^ 2 := by
      nlinarith only [hpde]
    have hWm : W ^ 2 ≤ 32 * m ^ 2 * x := by
      rcases primitive_zero_square a b d e m hprim hlevel hab with hmd | hme
      · calc
          W ^ 2 ≤ 16 * d ^ 2 * e ^ 2 := hWsq
          _ ≤ 16 * d ^ 2 * (2 * x) :=
            mul_le_mul_of_nonneg_left he2 (by positivity)
          _ = 32 * m ^ 2 * x := by rw [hmd]; ring
      · calc
          W ^ 2 ≤ 16 * d ^ 2 * e ^ 2 := hWsq
          _ ≤ 16 * x * e ^ 2 := by
            have hh := mul_le_mul_of_nonneg_right hd2 (show 0 ≤ 16 * e ^ 2 by positivity)
            nlinarith only [hh]
          _ ≤ 32 * m ^ 2 * x := by
            rw [hme]
            nlinarith only [mul_nonneg hx0.le (sq_nonneg e)]
    have hpW := mul_le_mul_of_nonneg_left hWm (sq_nonneg C₀)
    have hn : m ^ 2 * (L ^ 2 * M ^ 2) ≤
        m ^ 2 * ((32 * C₀ ^ 2) * x) := by
      nlinarith only [hp2, hpW]
    exact le_of_mul_le_mul_left hn (sq_pos_of_ne_zero hm)
  · rcases hcoarse with hlarge | hsmall
    · left
      have hp3 := pow_le_pow_left₀
        (show 0 ≤ L * |m| * M by positivity) hcell0 3
      have hp := mul_le_mul_of_nonneg_right hp3 hx0.le
      have hs := mul_le_mul_of_nonneg_right hlarge
        (show 0 ≤ L ^ 3 * M ^ 3 by positivity)
      have hn : W ^ 2 * (L ^ 3 * M ^ 3) ≤
          W ^ 2 * ((100000 * C₀ ^ 3) * x * W) := by
        nlinarith only [hp, hs]
      exact le_of_mul_le_mul_left hn (pow_pos hW 2)
    · right; left
      have hg : (1 : ℝ) ≤ |((a * b : ℤ) : ℝ)| := by
        exact_mod_cast (Int.one_le_abs hab)
      have hgW := mul_le_mul_of_nonneg_right hg
        (show 0 ≤ (1 / 100000 : ℝ) * W by positivity)
      have hsmall0 : (1 / 100000 : ℝ) * W ≤ m ^ 2 := by
        nlinarith only [hgW, hsmall]
      have hs := mul_le_mul_of_nonneg_right hsmall0
        (show 0 ≤ L ^ 2 * M ^ 2 by positivity)
      have hn : W * (L ^ 2 * M ^ 2) ≤
          W * ((100000 * C₀ ^ 2) * W) := by
        nlinarith only [hp2, hs]
      exact le_of_mul_le_mul_left hn hW

theorem range_cubes
    (x M W c : ℝ) (hx : 0 < x) (_hM : 0 < M) (hW : 0 < W) (hc : 0 < c)
    (hr1 : c * (W ^ ((4 : ℝ) / 3) * x ^ (-(1 : ℝ) / 3)) ≤ M)
    (hr2 : c * (x / W) ^ ((4 : ℝ) / 3) ≤ M) :
    c ^ 3 * W ^ 4 ≤ M ^ 3 * x ∧
    c ^ 3 * x ^ 4 ≤ M ^ 3 * W ^ 4 := by
  have hw : (W ^ ((4 : ℝ) / 3)) ^ (3 : ℕ) = W ^ 4 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hW.le]
    norm_num
  have hxi : (x ^ (-(1 : ℝ) / 3)) ^ (3 : ℕ) = x⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]
    norm_num [Real.rpow_neg_one]
  have hdiv : ((x / W) ^ ((4 : ℝ) / 3)) ^ (3 : ℕ) = (x / W) ^ 4 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (div_pos hx hW).le]
    norm_num
  have hp1 := pow_le_pow_left₀ (by positivity : 0 ≤
    c * (W ^ ((4 : ℝ) / 3) * x ^ (-(1 : ℝ) / 3))) hr1 3
  have hp2 := pow_le_pow_left₀ (by positivity : 0 ≤
    c * (x / W) ^ ((4 : ℝ) / 3)) hr2 3
  have ha : c ^ 3 * W ^ 4 / x ≤ M ^ 3 := by
    simp only [mul_pow] at hp1
    rw [hw, hxi] at hp1
    simpa only [div_eq_mul_inv, mul_assoc] using hp1
  have hb : c ^ 3 * x ^ 4 / W ^ 4 ≤ M ^ 3 := by
    simp only [mul_pow] at hp2
    rw [hdiv, div_pow] at hp2
    simpa only [mul_div_assoc] using hp2
  exact ⟨(div_le_iff₀ hx).mp ha, (div_le_iff₀ (pow_pos hW 4)).mp hb⟩

theorem coarse_original_point_length :
let delta : ℝ := 1 / 100000;
∀ C₀ c₀ : ℝ, 0 < C₀ → 0 < c₀ →
  ∃ C : ℝ, 1 ≤ C ∧
    ∀ x M W m J L : ℝ, ∀ a b : ℤ, ∀ d e : ℝ,
      2 ≤ x → 0 < M → 0 < W → m ≠ 0 →
      1 ≤ J → 0 ≤ L →
      W ≤ C₀ * x →
      c₀ * (W ^ ((4 : ℝ) / 3) * x ^ (-(1 : ℝ) / 3)) ≤ M →
      c₀ * (x / W) ^ ((4 : ℝ) / 3) ≤ M →
      L * |m| * J * M ≤ C₀ * W →
      Int.gcd a b = 1 →
      0 < d → 0 < e →
      m = (a : ℝ) * d + (b : ℝ) * e →
      W / 4 ≤ d * e →
      d ^ 2 ≤ x → e ^ 2 ≤ 2 * x →
      (delta * W ^ 2 ≤ |m| ^ 3 * x ∨
        delta * |((a * b : ℤ) : ℝ)| * W ≤ m ^ 2) →
      L ≤ C * (1 + Real.sqrt x /
        (Real.sqrt M * W ^ ((1 : ℝ) / 3)))
 := by
  dsimp only
  intro C₀ c₀ hC₀ hc₀
  let A : ℝ := 100000 * C₀ ^ 3
  let B : ℝ := 100000 * C₀ ^ 2
  let D : ℝ := 32 * C₀ ^ 2
  let K : ℝ := 1 + C₀ + A + B + D
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hK : 1 ≤ K := by dsimp only [K]; linarith
  have hCK : C₀ ≤ K := by dsimp only [K]; linarith
  have hAK : A ≤ K := by dsimp only [K]; linarith
  have hBK : B ≤ K := by dsimp only [K]; linarith
  have hDK : D ≤ K := by dsimp only [K]; linarith
  obtain ⟨C, hC, hrec⟩ :=
    A5PoweredRangeRecoveryRoot.length_recovery K c₀ hK hc₀
  refine ⟨C, hC, ?_⟩
  intro x M W m J L a b d e hx hM hW hm hJ hL hWx hr1 hr2
    hcell hprim hd he hlevel hprod hd2 he2 hcoarse
  have hx0 : 0 < x := by linarith
  have hrange := range_cubes x M W c₀ hx0 hM hW hc₀ hr1 hr2
  apply hrec x M W L hx hM hW hL
    (hWx.trans (mul_le_mul_of_nonneg_right hCK hx0.le)) hrange.1 hrange.2
  have hchoices := coarse_powered_choices C₀ x M W m J L a b d e
    hC₀ hx hM hW hm hJ hL hcell hprim hd he hlevel hprod hd2 he2 hcoarse
  rcases hchoices with h | h | h
  · left
    exact h.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hAK hx0.le) hW.le)
  · right; left
    exact h.trans (mul_le_mul_of_nonneg_right hBK hW.le)
  · right; right; left
    exact h.trans (mul_le_mul_of_nonneg_right hDK hx0.le)
end A5CoarseOriginalPointRoot
theorem JocelynClaims.claim_ad943653babc9fc0202de5d0410b9c73f58141ac05bd56b58862b151978e8619 :
let delta : ℝ := 1 / 100000;
∀ C₀ c₀ : ℝ, 0 < C₀ → 0 < c₀ →
  ∃ C : ℝ, 1 ≤ C ∧
    ∀ x M W m J L : ℝ, ∀ a b : ℤ, ∀ d e : ℝ,
      2 ≤ x → 0 < M → 0 < W → m ≠ 0 →
      1 ≤ J → 0 ≤ L →
      W ≤ C₀ * x →
      c₀ * (W ^ ((4 : ℝ) / 3) * x ^ (-(1 : ℝ) / 3)) ≤ M →
      c₀ * (x / W) ^ ((4 : ℝ) / 3) ≤ M →
      L * |m| * J * M ≤ C₀ * W →
      Int.gcd a b = 1 →
      0 < d → 0 < e →
      m = (a : ℝ) * d + (b : ℝ) * e →
      W / 4 ≤ d * e →
      d ^ 2 ≤ x → e ^ 2 ≤ 2 * x →
      (delta * W ^ 2 ≤ |m| ^ 3 * x ∨
        delta * |((a * b : ℤ) : ℝ)| * W ≤ m ^ 2) →
      L ≤ C * (1 + Real.sqrt x /
        (Real.sqrt M * W ^ ((1 : ℝ) / 3)))
 := by
  exact A5CoarseOriginalPointRoot.coarse_original_point_length
#print axioms JocelynClaims.claim_ad943653babc9fc0202de5d0410b9c73f58141ac05bd56b58862b151978e8619

set_option linter.all false
set_option pp.maxSteps 100
set_option maxErrors 16
set_option maxRecDepth 4000
noncomputable section
namespace A5DeepNormQs
set_option maxHeartbeats 1500000

theorem cancel_pos {p a b : ℝ} (hp : 0 < p) (h : p * a ≤ p * b) :
    a ≤ b := by
  by_contra! hn
  have hpos := mul_pos hp (sub_pos.mpr hn)
  nlinarith only [h, hpos]

theorem deep_norm_qs :
let delta : ℝ := 1 / 100000;
∀ m g W P S q n x : ℝ,
  m ≠ 0 → 0 < g → 0 < W →
  W / 4 ≤ P → P ≤ W → 2 ≤ x →
  1 ≤ |q| → 0 ≤ n → n ≤ x →
  S ^ 2 = m ^ 2 + 4 * g * P →
  m ^ 3 * n = q * P ^ 2 - m ^ 3 / 2 + m ^ 2 * S / 2 - g * P * S →
  |m| ^ 3 * x ≤ delta * W ^ 2 →
  m ^ 2 ≤ delta * g * W →
  |P * q - g * S| ≤ 98 * delta * g * |S| ∧
  |q * S - 4 * g ^ 2| ≤ 494 * delta * g ^ 2 ∧
  W ≤ 16 * g * |S| ∧
  W ≤ 1280 * g ^ 3 ∧
  |q * S| ≤ 5 * g ^ 2 := by
  dsimp only
  intro m g W P S q n x hm hg hW hPlow hPup hx hq hn hnx hsq hnum hdeep hsmall
  have hP : 0 < P := by linarith
  have hW4 : W ≤ 4 * P := by linarith
  let A : ℝ := |S|
  let E : ℝ := |P * q - g * S|
  have hA : 0 ≤ A := abs_nonneg S
  have hE : 0 ≤ E := abs_nonneg _
  have hA2 : A ^ 2 = S ^ 2 := sq_abs S
  have hN : |n + 1 / 2| ≤ 3 * x / 2 := by
    rw [abs_of_nonneg (by linarith : 0 ≤ n + 1 / 2)]
    linarith
  have hid : P * (P * q - g * S) =
      m ^ 3 * (n + 1 / 2) - m ^ 2 * S / 2 := by
    linear_combination -hnum
  have habs : P * E ≤ |m| ^ 3 * (3 * x / 2) + m ^ 2 * A / 2 := by
    calc
      P * E = |P * (P * q - g * S)| := by
        dsimp only [E]
        rw [abs_mul, abs_of_pos hP]
      _ = |m ^ 3 * (n + 1 / 2) - m ^ 2 * S / 2| := by rw [hid]
      _ ≤ |m ^ 3 * (n + 1 / 2)| + |m ^ 2 * S / 2| := by
        have hneg : |(-(m ^ 2 * S / 2))| = |m ^ 2 * S / 2| := abs_neg _
        have hh := abs_add_le (m ^ 3 * (n + 1 / 2)) (-(m ^ 2 * S / 2))
        rw [hneg] at hh
        simpa only [sub_eq_add_neg] using hh
      _ = |m| ^ 3 * |n + 1 / 2| + m ^ 2 * A / 2 := by
        dsimp only [A]
        simp only [abs_mul, abs_div, abs_pow, sq_abs]
        norm_num
      _ ≤ |m| ^ 3 * (3 * x / 2) + m ^ 2 * A / 2 :=
        add_le_add
          (mul_le_mul_of_nonneg_left hN (pow_nonneg (abs_nonneg m) 3)) le_rfl
  have hfirst_term : |m| ^ 3 * (3 * x / 2) ≤ (3 / 2 : ℝ) * (1 / 100000 : ℝ) * W ^ 2 := by
    nlinarith only [hdeep]
  have hsecond_term : m ^ 2 * A / 2 ≤ (1 / 100000 : ℝ) * g * W * A / 2 := by
    have hh := mul_le_mul_of_nonneg_right hsmall hA
    nlinarith only [hh]
  have habs_prod : P * E ≤ (3 / 2 : ℝ) * (1 / 100000 : ℝ) * W ^ 2 +
      (1 / 100000 : ℝ) * g * W * A / 2 :=
    habs.trans (add_le_add hfirst_term hsecond_term)
  have hWterm : (3 / 2 : ℝ) * (1 / 100000 : ℝ) * W ^ 2 ≤
      6 * (1 / 100000 : ℝ) * W * P := by
    have hh := mul_le_mul_of_nonneg_left hW4
      (by positivity : 0 ≤ (3 / 2 : ℝ) * (1 / 100000 : ℝ) * W)
    nlinarith only [hh]
  have hSterm : (1 / 100000 : ℝ) * g * W * A / 2 ≤
      2 * (1 / 100000 : ℝ) * g * A * P := by
    have hh := mul_le_mul_of_nonneg_left hW4
      (by positivity : 0 ≤ (1 / 100000 : ℝ) * g * A / 2)
    nlinarith only [hh]
  have hpre : E ≤ 6 * (1 / 100000 : ℝ) * W + 2 * (1 / 100000 : ℝ) * g * A := by
    apply cancel_pos hP
    nlinarith only [habs_prod, hWterm, hSterm]
  have hPQ : P * |q| ≤ E + g * A := by
    calc
      P * |q| = |P * q| := by rw [abs_mul, abs_of_pos hP]
      _ = |(P * q - g * S) + g * S| := by congr 1 ; ring
      _ ≤ |P * q - g * S| + |g * S| := abs_add_le _ _
      _ = E + g * A := by
        simp only [abs_mul, abs_of_pos hg]
        rfl
  have hQlower : P ≤ P * |q| := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hq hP.le
  have hboot0 : W / 4 ≤ 6 * (1 / 100000 : ℝ) * W + (1 + 2 * (1 / 100000 : ℝ)) * g * A := by
    nlinarith only [hPlow, hQlower, hPQ, hpre]
  have hboot : W ≤ 16 * g * A := by
    have hga : 0 ≤ g * A := mul_nonneg hg.le hA
    nlinarith only [hboot0, hga]
  have hnorm : E ≤ 98 * (1 / 100000 : ℝ) * g * A := by
    have hh := mul_le_mul_of_nonneg_left hboot
      (by norm_num : (0 : ℝ) ≤ 6 * (1 / 100000 : ℝ))
    nlinarith only [hpre, hh]
  have hSW : S ^ 2 ≤ 5 * g * W := by
    have hh := mul_le_mul_of_nonneg_left hPup (by positivity : 0 ≤ 4 * g)
    have hgw : 0 ≤ g * W := mul_nonneg hg.le hW.le
    nlinarith only [hsq, hsmall, hh, hgw]
  have hSA : A ^ 2 ≤ 5 * g * W := by simpa only [A, sq_abs] using hSW
  have hboot_sq := mul_le_mul hboot hboot hW.le
    (by positivity : 0 ≤ 16 * g * A)
  have hSWscaled := mul_le_mul_of_nonneg_left hSA
    (by positivity : 0 ≤ 256 * g ^ 2)
  have hcoercive : W ≤ 1280 * g ^ 3 := by
    apply cancel_pos hW
    nlinarith only [hboot_sq, hSWscaled]
  have hmP : m ^ 2 ≤ 4 * (1 / 100000 : ℝ) * g * P := by
    have hh := mul_le_mul_of_nonneg_left hW4
      (by positivity : 0 ≤ (1 / 100000 : ℝ) * g)
    nlinarith only [hsmall, hh]
  have hSP : S ^ 2 ≤ 5 * g * P := by
    have hgp : 0 ≤ g * P := mul_nonneg hg.le hP.le
    nlinarith only [hsq, hmP, hgp]
  have hidQS : P * (q * S - 4 * g ^ 2) =
      g * m ^ 2 + (P * q - g * S) * S := by
    linear_combination g * hsq
  have hQSabs : P * |q * S - 4 * g ^ 2| ≤ g * m ^ 2 + E * A := by
    calc
      P * |q * S - 4 * g ^ 2| = |P * (q * S - 4 * g ^ 2)| := by
        rw [abs_mul, abs_of_pos hP]
      _ = |g * m ^ 2 + (P * q - g * S) * S| := by rw [hidQS]
      _ ≤ |g * m ^ 2| + |(P * q - g * S) * S| := abs_add_le _ _
      _ = g * m ^ 2 + E * A := by
        simp only [abs_mul, abs_of_pos hg, abs_of_nonneg (sq_nonneg m)]
        rfl
  have hEmult : E * A ≤ 98 * (1 / 100000 : ℝ) * g * S ^ 2 := by
    calc
      E * A ≤ (98 * (1 / 100000 : ℝ) * g * A) * A :=
        mul_le_mul_of_nonneg_right hnorm hA
      _ = 98 * (1 / 100000 : ℝ) * g * A ^ 2 := by ring
      _ = 98 * (1 / 100000 : ℝ) * g * S ^ 2 := by rw [hA2]
  have hmPmult : g * m ^ 2 ≤ 4 * (1 / 100000 : ℝ) * g ^ 2 * P := by
    have hh := mul_le_mul_of_nonneg_left hmP hg.le
    nlinarith only [hh]
  have hSPmult : 98 * (1 / 100000 : ℝ) * g * S ^ 2 ≤ 490 * (1 / 100000 : ℝ) * g ^ 2 * P := by
    have hh := mul_le_mul_of_nonneg_left hSP
      (by positivity : 0 ≤ 98 * (1 / 100000 : ℝ) * g)
    nlinarith only [hh]
  have hQS : |q * S - 4 * g ^ 2| ≤ 494 * (1 / 100000 : ℝ) * g ^ 2 := by
    apply cancel_pos hP
    nlinarith only [hQSabs, hmPmult, hEmult, hSPmult]
  have hqS_triangle : |q * S| ≤ |q * S - 4 * g ^ 2| + 4 * g ^ 2 := by
    calc
      |q * S| = |(q * S - 4 * g ^ 2) + 4 * g ^ 2| := by congr 1 ; ring
      _ ≤ |q * S - 4 * g ^ 2| + |4 * g ^ 2| := abs_add_le _ _
      _ = |q * S - 4 * g ^ 2| + 4 * g ^ 2 := by
        rw [abs_of_nonneg (by positivity : 0 ≤ 4 * g ^ 2)]
  have hqS : |q * S| ≤ 5 * g ^ 2 := by
    nlinarith only [hQS, hqS_triangle, sq_nonneg g]
  exact ⟨hnorm, hQS, hboot, hcoercive, hqS⟩
end A5DeepNormQs

namespace JocelynClaims
theorem claim_ab923dcf84e9dc87fc5a903dad25d08370ead3efaa3aa1e11af645e658b00e7d :
let delta : ℝ := 1 / 100000;
∀ m g W P S q n x : ℝ,
  m ≠ 0 → 0 < g → 0 < W →
  W / 4 ≤ P → P ≤ W → 2 ≤ x →
  1 ≤ |q| → 0 ≤ n → n ≤ x →
  S ^ 2 = m ^ 2 + 4 * g * P →
  m ^ 3 * n = q * P ^ 2 - m ^ 3 / 2 + m ^ 2 * S / 2 - g * P * S →
  |m| ^ 3 * x ≤ delta * W ^ 2 →
  m ^ 2 ≤ delta * g * W →
  |P * q - g * S| ≤ 98 * delta * g * |S| ∧
  |q * S - 4 * g ^ 2| ≤ 494 * delta * g ^ 2 ∧
  W ≤ 16 * g * |S| ∧
  W ≤ 1280 * g ^ 3 ∧
  |q * S| ≤ 5 * g ^ 2 := by
  exact A5DeepNormQs.deep_norm_qs
end JocelynClaims

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

theorem a5_abs_sub_bound (a b : ℝ) : |a - b| ≤ |a| + |b| := by
  simpa only [sub_zero, zero_sub, abs_neg] using abs_sub_le a 0 b

theorem JocelynClaims.claim_0e87df013ff6ff87c8e1417f336c3d7af8b88e3c61ced563738f8f3a7529574a :
let delta : ℝ := 1 / 100000;
∀ m g W P S q K r J : ℝ,
  m ≠ 0 → 0 < g → 0 < W → 0 < J →
  W / 4 ≤ P →
  S ^ 2 = m ^ 2 + 4 * g * P →
  m ^ 2 ≤ delta * g * W →
  |P * q - g * S| ≤ 98 * delta * g * |S| →
  |q * S| ≤ 5 * g ^ 2 →
  |K| ≤ g ^ 2 / 100 →
  m ^ 3 * r + 2 * g ^ 2 * S =
    4 * S * K - 20 * g * (P * q - g * S) - 6 * m ^ 2 * q →
  g ^ 5 * W * J ^ 4 ≤ m ^ 6 * (J ^ 2 * r) ^ 2 := by
  dsimp only
  intro m g W P S q K r J hm hg hW hJ hP hS hm2 hN hq hK hid
  have hSg : g * W ≤ S ^ 2 := by
    have hh := mul_le_mul_of_nonneg_left hP (show 0 ≤ 4 * g by positivity)
    nlinarith only [hh, hS, sq_nonneg m]
  have hSsqpos : 0 < S ^ 2 := lt_of_lt_of_le (mul_pos hg hW) hSg
  have hSa : 0 < |S| := abs_pos.mpr (by
    intro hh
    simp only [hh, zero_pow (by norm_num : 2 ≠ 0)] at hSsqpos
    exact (lt_irrefl 0 hSsqpos))
  have hqa : m ^ 2 * |q| ≤ 5 * (1 / 100000 : ℝ) * g ^ 2 * |S| := by
    have hmul : (m ^ 2 * |q|) * |S| ≤
        (5 * (1 / 100000 : ℝ) * g ^ 2 * |S|) * |S| := by
      calc
        m ^ 2 * |q| * |S| = m ^ 2 * |q * S| := by rw [abs_mul]; ring
        _ ≤ m ^ 2 * (5 * g ^ 2) := mul_le_mul_of_nonneg_left hq (sq_nonneg m)
        _ ≤ ((1 / 100000 : ℝ) * g * W) * (5 * g ^ 2) :=
          mul_le_mul_of_nonneg_right hm2 (by positivity)
        _ ≤ 5 * (1 / 100000 : ℝ) * g ^ 2 * S ^ 2 := by
          have hh := mul_le_mul_of_nonneg_left hSg
            (show 0 ≤ 5 * (1 / 100000 : ℝ) * g ^ 2 by positivity)
          nlinarith only [hh]
        _ = (5 * (1 / 100000 : ℝ) * g ^ 2 * |S|) * |S| := by
          rw [← sq_abs S]
          ring
    exact le_of_mul_le_mul_right hmul hSa
  have hErr : |4 * S * K - 20 * g * (P * q - g * S) - 6 * m ^ 2 * q|
      ≤ g ^ 2 * |S| := by
    calc
      |4 * S * K - 20 * g * (P * q - g * S) - 6 * m ^ 2 * q|
          ≤ |4 * S * K| + |20 * g * (P * q - g * S)| + |6 * m ^ 2 * q| := by
        exact (a5_abs_sub_bound _ _).trans (add_le_add (a5_abs_sub_bound _ _) (le_refl _))
      _ = 4 * |S| * |K| + 20 * g * |P * q - g * S| + 6 * (m ^ 2 * |q|) := by
        simp only [abs_mul, abs_of_pos hg, abs_of_nonneg (sq_nonneg m)]
        norm_num
        <;> ring
      _ ≤ 4 * |S| * (g ^ 2 / 100) +
          20 * g * (98 * (1 / 100000 : ℝ) * g * |S|) +
          6 * (5 * (1 / 100000 : ℝ) * g ^ 2 * |S|) := by
        gcongr
      _ ≤ g ^ 2 * |S| := by
        nlinarith only [mul_nonneg (sq_nonneg g) (abs_nonneg S)]
  have hMain : 2 * g ^ 2 * |S| ≤
      |m ^ 3 * r| + |4 * S * K - 20 * g * (P * q - g * S) - 6 * m ^ 2 * q| := by
    calc
      2 * g ^ 2 * |S| = |2 * g ^ 2 * S| := by
        rw [abs_mul, abs_of_nonneg (show 0 ≤ 2 * g ^ 2 by positivity)]
      _ = |(4 * S * K - 20 * g * (P * q - g * S) - 6 * m ^ 2 * q) - m ^ 3 * r| := by
        congr 1
        linarith only [hid]
      _ ≤ |4 * S * K - 20 * g * (P * q - g * S) - 6 * m ^ 2 * q| + |m ^ 3 * r| :=
        a5_abs_sub_bound _ _
      _ = _ := by ring
  have hLow : g ^ 2 * |S| ≤ |m ^ 3 * r| := by
    nlinarith only [hMain, hErr]
  have hSquare : g ^ 4 * S ^ 2 ≤ m ^ 6 * r ^ 2 := by
    calc
      g ^ 4 * S ^ 2 = (g ^ 2 * |S|) ^ 2 := by rw [mul_pow, sq_abs]; ring
      _ ≤ |m ^ 3 * r| ^ 2 := by gcongr
      _ = m ^ 6 * r ^ 2 := by rw [sq_abs]; ring
  have hBase : g ^ 5 * W ≤ m ^ 6 * r ^ 2 := by
    calc
      g ^ 5 * W = g ^ 4 * (g * W) := by ring
      _ ≤ g ^ 4 * S ^ 2 := mul_le_mul_of_nonneg_left hSg (by positivity)
      _ ≤ m ^ 6 * r ^ 2 := hSquare
  calc
    g ^ 5 * W * J ^ 4 ≤ (m ^ 6 * r ^ 2) * J ^ 4 :=
      mul_le_mul_of_nonneg_right hBase (by positivity)
    _ = m ^ 6 * (J ^ 2 * r) ^ 2 := by ring

noncomputable section
namespace A5PolynomialDiameter
open Polynomial Set
set_option maxHeartbeats 1500000

theorem positive_curvature_diameter
    (p : Polynomial ℝ) (a b L U k : ℝ) (hab : a < b) (hk : 0 < k)
    (hvals : ∀ t : ℝ, a ≤ t → t ≤ b → L ≤ p.eval t ∧ p.eval t ≤ U)
    (hcurv : ∀ t : ℝ, a < t → t < b → k ≤ p.derivative.derivative.eval t) :
    k * (b - a) ^ 2 ≤ 8 * (U - L) := by
  let r : Polynomial ℝ := p - C (k / 2) * X ^ 2
  have hrsecond (t : ℝ) :
      r.derivative.derivative.eval t = p.derivative.derivative.eval t - k := by
    norm_num [r, Polynomial.derivative_mul] <;> ring
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

set_option maxHeartbeats 400000
namespace JocelynClaims
theorem claim_0357db812536f4b6cb95b812ac7fe480c3f6951543bd0d23ce7fef93a4c0b67e :
(∀ H mu J M W g x A B C : ℝ,
  0 ≤ H → 0 < mu → 0 < J → 0 < M → 0 < W → 0 < g → 0 < x →
  0 ≤ A → 0 ≤ B → 0 ≤ C →
  H * mu * J * M ≤ A * W →
  H ^ 4 * g ^ 5 * W * J ^ 4 ≤ B ^ 2 * x ^ 2 * mu ^ 6 →
  W ≤ C * g ^ 2 * J →
  mu ^ 3 * W ≤ C * g ^ 2 * J ^ 3 →
  H ^ 11 * M ^ 3 * W ^ 4 ≤ A ^ 3 * B ^ 4 * C ^ 5 * x ^ 4 ∧
  (∀ c0 : ℝ, 0 < c0 → c0 ^ 3 * x ^ 4 ≤ M ^ 3 * W ^ 4 →
    H ^ 11 ≤ A ^ 3 * B ^ 4 * C ^ 5 / c0 ^ 3)) := by
  intro H mu J M W g x A B C hH hmu hJ hM hW hg hx hA hB hC hcell hcurv hlin hcub
  have p1 : (H * mu * J * M) ^ 3 ≤ (A * W) ^ 3 :=
    pow_le_pow_left₀ (by positivity) hcell 3
  have p2 : (H ^ 4 * g ^ 5 * W * J ^ 4) ^ 2 ≤
      (B ^ 2 * x ^ 2 * mu ^ 6) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hcurv 2
  have p3 : W ^ 2 ≤ (C * g ^ 2 * J) ^ 2 :=
    pow_le_pow_left₀ hW.le hlin 2
  have p4 : (mu ^ 3 * W) ^ 3 ≤ (C * g ^ 2 * J ^ 3) ^ 3 :=
    pow_le_pow_left₀ (by positivity) hcub 3
  have hp :
      ((H * mu * J * M) ^ 3 * (H ^ 4 * g ^ 5 * W * J ^ 4) ^ 2) *
        (W ^ 2 * (mu ^ 3 * W) ^ 3) ≤
      ((A * W) ^ 3 * (B ^ 2 * x ^ 2 * mu ^ 6) ^ 2) *
        ((C * g ^ 2 * J) ^ 2 * (C * g ^ 2 * J ^ 3) ^ 3) :=
    mul_le_mul
      (mul_le_mul p1 p2 (by positivity) (by positivity))
      (mul_le_mul p3 p4 (by positivity) (by positivity))
      (by positivity) (by positivity)
  have hn :
      (mu ^ 12 * g ^ 10 * J ^ 11 * W ^ 3) * (H ^ 11 * M ^ 3 * W ^ 4) ≤
      (mu ^ 12 * g ^ 10 * J ^ 11 * W ^ 3) *
        (A ^ 3 * B ^ 4 * C ^ 5 * x ^ 4) := by
    convert hp using 1 <;> ring
  have hbound : H ^ 11 * M ^ 3 * W ^ 4 ≤ A ^ 3 * B ^ 4 * C ^ 5 * x ^ 4 :=
    le_of_mul_le_mul_left hn (by positivity)
  refine ⟨hbound, ?_⟩
  intro c0 hc0 hrange
  apply (le_div_iff₀ (pow_pos hc0 3)).2
  have hs : (H ^ 11 * c0 ^ 3) * x ^ 4 ≤ (A ^ 3 * B ^ 4 * C ^ 5) * x ^ 4 := by
    calc
      _ = H ^ 11 * (c0 ^ 3 * x ^ 4) := by ring
      _ ≤ H ^ 11 * (M ^ 3 * W ^ 4) :=
        mul_le_mul_of_nonneg_left hrange (by positivity)
      _ = H ^ 11 * M ^ 3 * W ^ 4 := by ring
      _ ≤ _ := hbound
  exact le_of_mul_le_mul_right hs (pow_pos hx 4)
end JocelynClaims

set_option maxHeartbeats 400000

theorem JocelynClaims.claim_1f317d8a0ffba478c1a12b9c2eafe76b2342b63f773dd5317c6286b87b302a5e :
∀ L mu J M W g x A B C : ℝ,
  0 ≤ L → 0 < mu → 0 < J → 0 < M → 0 < W → 1 ≤ g → 0 < x →
  0 ≤ A → 0 ≤ B → 0 ≤ C →
  L * mu * J * M ≤ A * W →
  L * W * g ^ 2 * J ≤ B * x * mu ^ 3 →
  mu ^ 3 * W ≤ C * g ^ 2 * J ^ 3 →
  L ^ 6 * M ^ 3 * W ^ 2 ≤ A ^ 3 * B ^ 3 * C ^ 2 * x ^ 3 := by
  intro L mu J M W g x A B C hL hmu hJ hM hW hg hx hA hB hC hcell hder hcub
  have hg0 : 0 < g := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hg
  have p1 : (L * mu * J * M) ^ 3 ≤ (A * W) ^ 3 :=
    pow_le_pow_left₀ (by positivity) hcell 3
  have p2 : (L * W * g ^ 2 * J) ^ 3 ≤ (B * x * mu ^ 3) ^ 3 :=
    pow_le_pow_left₀ (by positivity) hder 3
  have p3 : (mu ^ 3 * W) ^ 2 ≤ (C * g ^ 2 * J ^ 3) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hcub 2
  have hp :
      ((L * mu * J * M) ^ 3 * (L * W * g ^ 2 * J) ^ 3) *
        (mu ^ 3 * W) ^ 2 ≤
      ((A * W) ^ 3 * (B * x * mu ^ 3) ^ 3) *
        (C * g ^ 2 * J ^ 3) ^ 2 :=
    mul_le_mul (mul_le_mul p1 p2 (by positivity) (by positivity))
      p3 (by positivity) (by positivity)
  have hn :
      (mu ^ 9 * W ^ 3 * g ^ 4 * J ^ 6) * (L ^ 6 * M ^ 3 * W ^ 2 * g ^ 2) ≤
      (mu ^ 9 * W ^ 3 * g ^ 4 * J ^ 6) * (A ^ 3 * B ^ 3 * C ^ 2 * x ^ 3) := by
    convert hp using 1 <;> ring
  have hbound : L ^ 6 * M ^ 3 * W ^ 2 * g ^ 2 ≤ A ^ 3 * B ^ 3 * C ^ 2 * x ^ 3 :=
    le_of_mul_le_mul_left hn (by positivity)
  have hgg : 1 ≤ g ^ 2 := by nlinarith only [hg, sq_nonneg (g - 1)]
  calc
    L ^ 6 * M ^ 3 * W ^ 2 = (L ^ 6 * M ^ 3 * W ^ 2) * 1 := by ring
    _ ≤ (L ^ 6 * M ^ 3 * W ^ 2) * g ^ 2 :=
      mul_le_mul_of_nonneg_left hgg (by positivity)
    _ ≤ A ^ 3 * B ^ 3 * C ^ 2 * x ^ 3 := hbound

set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

namespace ConsecutiveCountingA5AcceptedIntervalLength

def AcceptedDeepIntervalLengthStatement : Prop :=
  let delta : ℝ := 1 / 100000;
  ∀ C₀ c₀ : ℝ, 0 < C₀ → 0 < c₀ →
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ x M W m J g q_r s t : ℝ,
        2 ≤ x → 0 < M → 0 < W →
        m ≠ 0 → 0 < J → 1 ≤ g → q_r ≠ 0 →
        W ≤ C₀ * x →
        c₀ * (W ^ ((4 : ℝ) / 3) * x ^ (-(1 : ℝ) / 3)) ≤ M →
        c₀ * (x / W) ^ ((4 : ℝ) / 3) ≤ M →
        (t - s) * |m| * J * M ≤ C₀ * W →
        1 ≤ |q_r| * J →
        |m| ^ 3 ≤ |q_r| * J ^ 3 →
        |m| ^ 3 * x ≤ delta * W ^ 2 →
        m ^ 2 ≤ delta * g * W →
        ∀ Pi S q N : Polynomial ℝ,
          let K : Polynomial ℝ :=
            Polynomial.C q_r * Pi +
              Polynomial.C (2 : ℝ) * q * S -
              Polynomial.C (6 * g ^ 2);
          (∀ z : ℝ, s ≤ z → z ≤ t →
            W / 4 ≤ Pi.eval z ∧ Pi.eval z ≤ W ∧
            (S.eval z) ^ 2 = m ^ 2 + 4 * g * Pi.eval z ∧
            1 ≤ |q.eval z| ∧
            0 ≤ N.eval z ∧ N.eval z ≤ x ∧
            m ^ 3 * N.eval z =
              q.eval z * (Pi.eval z) ^ 2 -
                (m ^ 3 / 2 - m ^ 2 * S.eval z / 2 +
                  g * Pi.eval z * S.eval z) ∧
            Pi.derivative.eval z = J * S.eval z ∧
            S.derivative.eval z = 2 * g * J ∧
            q.derivative.eval z = q_r * J) →
          ((∀ z : ℝ, s ≤ z → z ≤ t →
              g ^ 2 / 100 ≤ K.eval z) ∨
            (∀ z : ℝ, s ≤ z → z ≤ t →
              K.eval z ≤ -(g ^ 2 / 100)) ∨
            ((∀ z : ℝ, s ≤ z → z ≤ t →
                |K.eval z| ≤ g ^ 2 / 100) ∧
              ((∀ z : ℝ, s ≤ z → z ≤ t →
                  0 ≤ N.derivative.derivative.eval z) ∨
                (∀ z : ℝ, s ≤ z → z ≤ t →
                  N.derivative.derivative.eval z ≤ 0)))) →
          t - s ≤ C *
            (1 + Real.sqrt x /
              (Real.sqrt M * W ^ ((1 : ℝ) / 3)))

end ConsecutiveCountingA5AcceptedIntervalLength

set_option maxHeartbeats 3000000

namespace A5AcceptedIntervalProof
open Set Filter Polynomial
open scoped Topology

def kpoly (q_r g : ℝ) (Pi S q : Polynomial ℝ) : Polynomial ℝ :=
  C q_r * Pi + C 2 * q * S - C (6 * g ^ 2)

theorem eval_derivative_eq_on_Ioo
    (p q : Polynomial ℝ) (s t z : ℝ)
    (h : ∀ u : ℝ, s < u → u < t → p.eval u = q.eval u)
    (hzs : s < z) (hzt : z < t) :
    p.derivative.eval z = q.derivative.eval z := by
  have he : (fun u : ℝ => p.eval u) =ᶠ[𝓝 z] (fun u : ℝ => q.eval u) :=
    Filter.eventually_of_mem (isOpen_Ioo.mem_nhds ⟨hzs, hzt⟩)
      (fun u hu => h u hu.1 hu.2)
  simpa only [Polynomial.deriv] using he.deriv_eq

theorem derivative_identities
    (m J g q_r s t : ℝ) (Pi S q N : Polynomial ℝ)
    (hsq : ∀ z : ℝ, s ≤ z → z ≤ t →
      (S.eval z) ^ 2 = m ^ 2 + 4 * g * Pi.eval z)
    (hnum : ∀ z : ℝ, s ≤ z → z ≤ t →
      m ^ 3 * N.eval z =
        q.eval z * (Pi.eval z) ^ 2 -
          (m ^ 3 / 2 - m ^ 2 * S.eval z / 2 + g * Pi.eval z * S.eval z))
    (hPi : ∀ z : ℝ, s ≤ z → z ≤ t →
      Pi.derivative.eval z = J * S.eval z)
    (hS : ∀ z : ℝ, s ≤ z → z ≤ t →
      S.derivative.eval z = 2 * g * J)
    (hq : ∀ z : ℝ, s ≤ z → z ≤ t →
      q.derivative.eval z = q_r * J) :
    ∀ z : ℝ, s < z → z < t →
      m ^ 3 * N.derivative.eval z =
          J * Pi.eval z * (kpoly q_r g Pi S q).eval z ∧
      m ^ 3 * N.derivative.derivative.eval z =
          J ^ 2 * (S.eval z * (kpoly q_r g Pi S q).eval z +
            Pi.eval z * (3 * q_r * S.eval z + 4 * g * q.eval z)) := by
  have hfirst : ∀ z : ℝ, s < z → z < t →
      m ^ 3 * N.derivative.eval z =
        J * Pi.eval z * (kpoly q_r g Pi S q).eval z := by
    intro z hzs hzt
    let A : Polynomial ℝ := C (m ^ 3) * N
    let B : Polynomial ℝ :=
      q * Pi ^ 2 - (C (m ^ 3 / 2) - C (m ^ 2 / 2) * S + C g * Pi * S)
    have he : ∀ u : ℝ, s < u → u < t → A.eval u = B.eval u := by
      intro u hus hut
      simpa only [A, B, eval_mul, eval_C, eval_sub, eval_add, eval_pow,
        div_mul_eq_mul_div] using hnum u hus.le hut.le
    have hd := eval_derivative_eq_on_Ioo A B s t z he hzs hzt
    norm_num [A, B, Polynomial.derivative_mul, Polynomial.derivative_pow] at hd
    rw [hPi z hzs.le hzt.le, hS z hzs.le hzt.le, hq z hzs.le hzt.le] at hd
    simp only [kpoly, eval_sub, eval_add, eval_mul, eval_C]
    linear_combination hd - g * J * hsq z hzs.le hzt.le
  intro z hzs hzt
  refine ⟨hfirst z hzs hzt, ?_⟩
  let A : Polynomial ℝ := C (m ^ 3) * N.derivative
  let B : Polynomial ℝ := C J * Pi * kpoly q_r g Pi S q
  have he : ∀ u : ℝ, s < u → u < t → A.eval u = B.eval u := by
    intro u hus hut
    simpa only [A, B, eval_mul, eval_C] using hfirst u hus hut
  have hd := eval_derivative_eq_on_Ioo A B s t z he hzs hzt
  norm_num [A, B, kpoly, Polynomial.derivative_mul] at hd
  rw [hPi z hzs.le hzt.le, hS z hzs.le hzt.le, hq z hzs.le hzt.le] at hd
  simp only [Polynomial.derivative_pow, Polynomial.derivative_C, mul_zero,
    zero_mul, add_zero, zero_add, sub_zero, Polynomial.eval_zero] at hd
  simp only [kpoly, eval_sub, eval_add, eval_mul, eval_C]
  linear_combination hd

theorem derivative_length_bound
    (N : Polynomial ℝ) (s t x B : ℝ) (hst : s < t)
    (hvals : ∀ z : ℝ, s ≤ z → z ≤ t →
      0 ≤ N.eval z ∧ N.eval z ≤ x)
    (hder : ∀ z : ℝ, s < z → z < t →
      B ≤ |N.derivative.eval z|) :
    (t - s) * B ≤ x := by
  obtain ⟨z, hz, he⟩ := exists_deriv_eq_slope (fun u : ℝ => N.eval u) hst
    N.continuous.continuousOn
    (fun u hu => (N.hasDerivAt u).differentiableAt.differentiableWithinAt)
  rw [Polynomial.deriv] at he
  have hmul : N.derivative.eval z * (t - s) = N.eval t - N.eval s :=
    (eq_div_iff (sub_pos.mpr hst).ne').mp he
  have ha := hvals s le_rfl hst.le
  have hb := hvals t hst.le le_rfl
  have habs : |N.eval t - N.eval s| ≤ x :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  calc
    (t - s) * B ≤ (t - s) * |N.derivative.eval z| :=
      mul_le_mul_of_nonneg_left (hder z hz.1 hz.2) (sub_pos.mpr hst).le
    _ = |N.derivative.eval z * (t - s)| := by
      rw [abs_mul, abs_of_pos (sub_pos.mpr hst), mul_comm]
    _ = |N.eval t - N.eval s| := by rw [hmul]
    _ ≤ x := habs

theorem abs_pow_six (m : ℝ) : |m| ^ 6 = m ^ 6 := by
  calc
    |m| ^ 6 = (|m| ^ 2) ^ 3 := by ring
    _ = (m ^ 2) ^ 3 := by rw [sq_abs]
    _ = m ^ 6 := by ring

theorem critical_squared_length
    (N : Polynomial ℝ) (s t x m g W J : ℝ)
    (hst : s < t) (hx : 0 ≤ x) (hm : m ≠ 0)
    (hg : 0 < g) (hW : 0 < W) (hJ : 0 < J)
    (hvals : ∀ z : ℝ, s ≤ z → z ≤ t →
      0 ≤ N.eval z ∧ N.eval z ≤ x)
    (hcurv : ∀ z : ℝ, s < z → z < t →
      g ^ 5 * W * J ^ 4 ≤ m ^ 6 * (N.derivative.derivative.eval z) ^ 2)
    (hsign : (∀ z : ℝ, s ≤ z → z ≤ t →
        0 ≤ N.derivative.derivative.eval z) ∨
      (∀ z : ℝ, s ≤ z → z ≤ t →
        N.derivative.derivative.eval z ≤ 0)) :
    (t - s) ^ 4 * g ^ 5 * W * J ^ 4 ≤ 64 * x ^ 2 * |m| ^ 6 := by
  let k : ℝ := Real.sqrt (g ^ 5 * W) * J ^ 2 / |m| ^ 3
  have hmu : 0 < |m| := abs_pos.mpr hm
  have hk : 0 < k := by dsimp only [k]; positivity
  have hksq : k ^ 2 * |m| ^ 6 = g ^ 5 * W * J ^ 4 := by
    dsimp only [k]
    rw [div_pow, mul_pow, Real.sq_sqrt (by positivity : 0 ≤ g ^ 5 * W)]
    field_simp
    <;> ring
  have hpoint : ∀ z : ℝ, s < z → z < t →
      k ^ 2 ≤ (N.derivative.derivative.eval z) ^ 2 := by
    intro z hzs hzt
    have hh : k ^ 2 * |m| ^ 6 ≤
        (N.derivative.derivative.eval z) ^ 2 * |m| ^ 6 := by
      calc
        _ = g ^ 5 * W * J ^ 4 := hksq
        _ ≤ m ^ 6 * (N.derivative.derivative.eval z) ^ 2 := hcurv z hzs hzt
        _ = _ := by rw [abs_pow_six]; ring
    exact le_of_mul_le_mul_right hh (pow_pos hmu 6)
  have hsigned :
      (∀ z : ℝ, s < z → z < t → k ≤ N.derivative.derivative.eval z) ∨
      (∀ z : ℝ, s < z → z < t → N.derivative.derivative.eval z ≤ -k) := by
    rcases hsign with hp | hn
    · left
      intro z hzs hzt
      exact le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0)
        (hp z hzs.le hzt.le) (hpoint z hzs hzt)
    · right
      intro z hzs hzt
      have hh : k ^ 2 ≤ (-N.derivative.derivative.eval z) ^ 2 := by
        simpa only [neg_sq] using hpoint z hzs hzt
      have hh' := le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0)
        (neg_nonneg.mpr (hn z hzs.le hzt.le)) hh
      linarith only [hh']
  have hd := JocelynClaims.claim_3e75905b2d0f06455e160821601d7b7ded491039a7f5b69aba31febcf9b0c31f
    N s t 0 x k hst hk hvals hsigned
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ k * (t - s) ^ 2) hd 2
  have hmulp := mul_le_mul_of_nonneg_right hp (pow_nonneg hmu.le 6)
  calc
    (t - s) ^ 4 * g ^ 5 * W * J ^ 4 =
        (k * (t - s) ^ 2) ^ 2 * |m| ^ 6 := by
      rw [mul_pow]
      calc
        _ = (t - s) ^ 4 * (g ^ 5 * W * J ^ 4) := by ring
        _ = (t - s) ^ 4 * (k ^ 2 * |m| ^ 6) := by rw [hksq]
        _ = _ := by ring
    _ ≤ (8 * (x - 0)) ^ 2 * |m| ^ 6 := hmulp
    _ = 64 * x ^ 2 * |m| ^ 6 := by ring

#print axioms derivative_identities
#print axioms derivative_length_bound
#print axioms critical_squared_length
end A5AcceptedIntervalProof

namespace A5AcceptedIntervalProof
open Polynomial Set
open scoped Topology

theorem range_cubes
    (x M W c : ℝ) (hx : 0 < x) (_hM : 0 < M) (hW : 0 < W) (hc : 0 < c)
    (hr1 : c * (W ^ ((4 : ℝ) / 3) * x ^ (-(1 : ℝ) / 3)) ≤ M)
    (hr2 : c * (x / W) ^ ((4 : ℝ) / 3) ≤ M) :
    c ^ 3 * W ^ 4 ≤ M ^ 3 * x ∧
    c ^ 3 * x ^ 4 ≤ M ^ 3 * W ^ 4 := by
  have hw : (W ^ ((4 : ℝ) / 3)) ^ (3 : ℕ) = W ^ 4 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hW.le]
    norm_num
  have hxi : (x ^ (-(1 : ℝ) / 3)) ^ (3 : ℕ) = x⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]
    norm_num [Real.rpow_neg_one]
  have hdiv : ((x / W) ^ ((4 : ℝ) / 3)) ^ (3 : ℕ) = (x / W) ^ 4 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (div_pos hx hW).le]
    norm_num
  have hp1 := pow_le_pow_left₀ (by positivity : 0 ≤
    c * (W ^ ((4 : ℝ) / 3) * x ^ (-(1 : ℝ) / 3))) hr1 3
  have hp2 := pow_le_pow_left₀ (by positivity : 0 ≤
    c * (x / W) ^ ((4 : ℝ) / 3)) hr2 3
  have ha : c ^ 3 * W ^ 4 / x ≤ M ^ 3 := by
    simp only [mul_pow] at hp1
    rw [hw, hxi] at hp1
    simpa only [div_eq_mul_inv, mul_assoc] using hp1
  have hb : c ^ 3 * x ^ 4 / W ^ 4 ≤ M ^ 3 := by
    simp only [mul_pow] at hp2
    rw [hdiv, div_pow] at hp2
    simpa only [mul_div_assoc] using hp2
  exact ⟨(div_le_iff₀ hx).mp ha, (div_le_iff₀ (pow_pos hW 4)).mp hb⟩

theorem large_K_bound
    (q_r g W P S q : ℝ) (hP : W / 4 ≤ P)
    (hqS : |q * S| ≤ 5 * g ^ 2)
    (hlarge : 128 * g ^ 2 ≤ |q_r| * W) :
    |q_r| * W / 8 ≤ |q_r * P + 2 * q * S - 6 * g ^ 2| := by
  obtain ⟨hlo, hup⟩ := abs_le.mp hqS
  by_cases hq : 0 ≤ q_r
  · have hp := mul_le_mul_of_nonneg_left hP hq
    rw [abs_of_nonneg hq] at hlarge ⊢
    have hh : q_r * W / 8 ≤ q_r * P + 2 * q * S - 6 * g ^ 2 := by
      nlinarith only [hp, hlo, hlarge]
    exact hh.trans (le_abs_self _)
  · have hqr : q_r < 0 := lt_of_not_ge hq
    have hp := mul_le_mul_of_nonneg_left hP (neg_nonneg.mpr hqr.le)
    rw [abs_of_neg hqr] at hlarge ⊢
    have hh : -q_r * W / 8 ≤ -(q_r * P + 2 * q * S - 6 * g ^ 2) := by
      nlinarith only [hp, hup, hlarge, sq_nonneg g]
    have hnegabs : -(q_r * P + 2 * q * S - 6 * g ^ 2) ≤
        |q_r * P + 2 * q * S - 6 * g ^ 2| := by
      have habs : -|q_r * P + 2 * q * S - 6 * g ^ 2| ≤
          q_r * P + 2 * q * S - 6 * g ^ 2 :=
        (abs_le.mp (le_rfl : |q_r * P + 2 * q * S - 6 * g ^ 2| ≤
          |q_r * P + 2 * q * S - 6 * g ^ 2|)).1
      linarith only [habs]
    exact hh.trans hnegabs

theorem accepted_deep_interval_length :
    ConsecutiveCountingA5AcceptedIntervalLength.AcceptedDeepIntervalLengthStatement := by
  unfold ConsecutiveCountingA5AcceptedIntervalLength.AcceptedDeepIntervalLengthStatement
  dsimp only
  intro C₀ c₀ hC₀ hc₀
  let A6 : ℝ := C₀ ^ 3 * 400 ^ 3 * 128 ^ 2
  let A11 : ℝ := C₀ ^ 3 * 8 ^ 4 * 128 ^ 5
  let K₀ : ℝ := 1 + C₀ + A6 + A11
  have hA6 : 0 ≤ A6 := by dsimp only [A6]; positivity
  have hA11 : 0 ≤ A11 := by dsimp only [A11]; positivity
  have hK₀ : 1 ≤ K₀ := by dsimp only [K₀]; linarith
  have hCK : C₀ ≤ K₀ := by dsimp only [K₀]; linarith
  have h6K : A6 ≤ K₀ := by dsimp only [K₀]; linarith
  have h11K : A11 ≤ K₀ := by dsimp only [K₀]; linarith
  obtain ⟨C, hC, hrecover⟩ :=
    A5PoweredRangeRecoveryRoot.length_recovery K₀ c₀ hK₀ hc₀
  refine ⟨C, hC, ?_⟩
  intro x M W m J g q_r s t hx hM hW hm hJ hg hqr hWx hr1 hr2 hcell
    hI1 hI3 hdeep hsmall Pi S q N
  intro hdata hbranch
  let K : Polynomial ℝ := kpoly q_r g Pi S q
  have hx0 : 0 < x := by linarith
  have hg0 : 0 < g := by linarith
  have hmu : 0 < |m| := abs_pos.mpr hm
  have hZ : 0 ≤ Real.sqrt x / (Real.sqrt M * W ^ ((1 : ℝ) / 3)) := by positivity
  have hC0 : 0 ≤ C := by linarith
  by_cases hts : t ≤ s
  · have hgoal : 0 ≤ C *
        (1 + Real.sqrt x / (Real.sqrt M * W ^ ((1 : ℝ) / 3))) := by positivity
    exact (sub_nonpos.mpr hts).trans hgoal
  have hst : s < t := lt_of_not_ge hts
  have hH : 0 ≤ t - s := (sub_pos.mpr hst).le
  have hvals : ∀ z : ℝ, s ≤ z → z ≤ t →
      0 ≤ N.eval z ∧ N.eval z ≤ x := by
    intro z hzs hzt
    rcases hdata z hzs hzt with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
    exact ⟨h5, h6⟩
  have hsq : ∀ z : ℝ, s ≤ z → z ≤ t →
      (S.eval z) ^ 2 = m ^ 2 + 4 * g * Pi.eval z := by
    intro z hzs hzt
    exact (hdata z hzs hzt).2.2.1
  have hnum : ∀ z : ℝ, s ≤ z → z ≤ t →
      m ^ 3 * N.eval z = q.eval z * (Pi.eval z) ^ 2 -
        (m ^ 3 / 2 - m ^ 2 * S.eval z / 2 + g * Pi.eval z * S.eval z) := by
    intro z hzs hzt
    rcases hdata z hzs hzt with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
    exact h7
  have hPi : ∀ z : ℝ, s ≤ z → z ≤ t →
      Pi.derivative.eval z = J * S.eval z := by
    intro z hzs hzt
    rcases hdata z hzs hzt with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
    exact h8
  have hS : ∀ z : ℝ, s ≤ z → z ≤ t →
      S.derivative.eval z = 2 * g * J := by
    intro z hzs hzt
    rcases hdata z hzs hzt with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
    exact h9
  have hq : ∀ z : ℝ, s ≤ z → z ≤ t →
      q.derivative.eval z = q_r * J := by
    intro z hzs hzt
    rcases hdata z hzs hzt with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
    exact h10
  have hDER := derivative_identities m J g q_r s t Pi S q N hsq hnum hPi hS hq
  have hnorm : ∀ z : ℝ, s ≤ z → z ≤ t →
      |Pi.eval z * q.eval z - g * S.eval z| ≤
          98 * (1 / 100000 : ℝ) * g * |S.eval z| ∧
      |q.eval z * S.eval z - 4 * g ^ 2| ≤
          494 * (1 / 100000 : ℝ) * g ^ 2 ∧
      W ≤ 16 * g * |S.eval z| ∧ W ≤ 1280 * g ^ 3 ∧
      |q.eval z * S.eval z| ≤ 5 * g ^ 2 := by
    intro z hzs hzt
    rcases hdata z hzs hzt with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
    exact JocelynClaims.claim_ab923dcf84e9dc87fc5a903dad25d08370ead3efaa3aa1e11af645e658b00e7d
      m g W (Pi.eval z) (S.eval z) (q.eval z) (N.eval z) x
      hm hg0 hW h1 h2 hx h4 h5 h6 h3
      (by nlinarith only [h7]) hdeep hsmall
  have hAbsDER : ∀ z : ℝ, s < z → z < t →
      |m| ^ 3 * |N.derivative.eval z| = J * Pi.eval z * |K.eval z| := by
    intro z hzs hzt
    have hP : 0 < Pi.eval z := by
      have hh := (hdata z hzs.le hzt.le).1
      linarith
    simpa only [abs_mul, abs_pow, abs_of_pos hJ, abs_of_pos hP, K] using
      congrArg abs (hDER z hzs hzt).1
  by_cases hlarge : 128 * g ^ 2 ≤ |q_r| * W
  · have hd : ∀ z : ℝ, s < z → z < t →
        x ≤ |N.derivative.eval z| := by
      intro z hzs hzt
      have hPlow := (hdata z hzs.le hzt.le).1
      have hPpos : 0 < Pi.eval z := by linarith only [hPlow, hW]
      have hKlow : |q_r| * W / 8 ≤ |K.eval z| := by
        simpa only [K, kpoly, eval_sub, eval_add, eval_mul, eval_C] using
          large_K_bound q_r g W (Pi.eval z) (S.eval z) (q.eval z)
            hPlow (hnorm z hzs.le hzt.le).2.2.2.2 hlarge
      have hp : J * (W / 4) * (|q_r| * W / 8) ≤ J * Pi.eval z * |K.eval z| := by
        gcongr <;> positivity
      have hi := mul_le_mul_of_nonneg_right hI1 (sq_nonneg W)
      have hh : |m| ^ 3 * x ≤ J * Pi.eval z * |K.eval z| := by
        calc
          _ ≤ (1 / 100000 : ℝ) * W ^ 2 := hdeep
          _ ≤ W ^ 2 / 32 := by nlinarith only [sq_nonneg W]
          _ ≤ J * (W / 4) * (|q_r| * W / 8) := by nlinarith only [hi]
          _ ≤ _ := hp
      rw [← hAbsDER z hzs hzt] at hh
      exact le_of_mul_le_mul_left hh (pow_pos hmu 3)
    have hlx := derivative_length_bound N s t x x hst hvals hd
    have hl : t - s ≤ 1 :=
      le_of_mul_le_mul_right (by simpa only [one_mul] using hlx) hx0
    calc
      t - s ≤ 1 := hl
      _ ≤ C := hC
      _ ≤ C * (1 + Real.sqrt x / (Real.sqrt M * W ^ ((1 : ℝ) / 3))) := by
        nlinarith only [mul_nonneg hC0 hZ]
  have hslope : |q_r| * W ≤ 128 * g ^ 2 := (lt_of_not_ge hlarge).le
  have hlin : W ≤ 128 * g ^ 2 * J := by
    have hi := mul_le_mul_of_nonneg_right hI1 hW.le
    have hs := mul_le_mul_of_nonneg_right hslope hJ.le
    nlinarith only [hi, hs]
  have hcub : |m| ^ 3 * W ≤ 128 * g ^ 2 * J ^ 3 := by
    have hi := mul_le_mul_of_nonneg_right hI3 hW.le
    have hs := mul_le_mul_of_nonneg_right hslope (pow_nonneg hJ.le 3)
    nlinarith only [hi, hs]
  have hrange := range_cubes x M W c₀ hx0 hM hW hc₀ hr1 hr2
  have hWxK : W ≤ K₀ * x :=
    hWx.trans (mul_le_mul_of_nonneg_right hCK hx0.le)
  apply hrecover x M W (t - s) hx hM hW hH hWxK hrange.1 hrange.2
  have hnoncritical :
      (∀ z : ℝ, s ≤ z → z ≤ t → g ^ 2 / 100 ≤ |K.eval z|) →
      (t - s) ^ 6 * M ^ 3 * W ^ 2 ≤ K₀ * x ^ 3 := by
    intro hKlow
    let B : ℝ := W * g ^ 2 * J / (400 * |m| ^ 3)
    have hd : ∀ z : ℝ, s < z → z < t →
        B ≤ |N.derivative.eval z| := by
      intro z hzs hzt
      have hPlow := (hdata z hzs.le hzt.le).1
      have hPpos : 0 < Pi.eval z := by linarith only [hPlow, hW]
      have hKpoint := hKlow z hzs.le hzt.le
      have hp : J * (W / 4) * (g ^ 2 / 100) ≤
          J * Pi.eval z * |K.eval z| := by
        gcongr <;> positivity
      apply (div_le_iff₀ (by positivity : 0 < 400 * |m| ^ 3)).2
      nlinarith only [hp, hAbsDER z hzs hzt]
    have hl := derivative_length_bound N s t x B hst hvals hd
    have hder : (t - s) * W * g ^ 2 * J ≤ 400 * x * |m| ^ 3 := by
      calc
        _ = ((t - s) * B) * (400 * |m| ^ 3) := by
          dsimp only [B]
          field_simp
          <;> ring
        _ ≤ x * (400 * |m| ^ 3) :=
          mul_le_mul_of_nonneg_right hl (by positivity)
        _ = _ := by ring
    have hp := JocelynClaims.claim_1f317d8a0ffba478c1a12b9c2eafe76b2342b63f773dd5317c6286b87b302a5e
      (t - s) |m| J M W g x C₀ 400 128
      hH hmu hJ hM hW hg hx0 hC₀.le (by norm_num) (by norm_num) hcell hder hcub
    exact hp.trans (mul_le_mul_of_nonneg_right h6K (pow_nonneg hx0.le 3))
  rcases hbranch with hpos | hneg | hcritical
  · apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inl
    apply hnoncritical
    intro z hzs hzt
    exact (hpos z hzs hzt).trans (le_abs_self _)
  · apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inl
    apply hnoncritical
    intro z hzs hzt
    have hh : g ^ 2 / 100 ≤ -K.eval z := by
      have hnegpoint : K.eval z ≤ -(g ^ 2 / 100) := hneg z hzs hzt
      linarith only [hnegpoint]
    exact hh.trans (by simpa only [_root_.abs_neg] using le_abs_self (-K.eval z))
  · apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
    have hc : ∀ z : ℝ, s < z → z < t →
        g ^ 5 * W * J ^ 4 ≤ m ^ 6 * (N.derivative.derivative.eval z) ^ 2 := by
      intro z hzs hzt
      have hsquared := hsq z hzs.le hzt.le
      have hcancel :
          S.eval z * K.eval z +
              Pi.eval z * (3 * q_r * S.eval z + 4 * g * q.eval z) +
              2 * g ^ 2 * S.eval z =
            4 * S.eval z * K.eval z -
              20 * g * (Pi.eval z * q.eval z - g * S.eval z) -
              6 * m ^ 2 * q.eval z := by
        dsimp only [K, kpoly]
        simp only [eval_sub, eval_add, eval_mul, eval_C]
        linear_combination -6 * q.eval z * hsquared
      have hid :
          m ^ 3 * (N.derivative.derivative.eval z / J ^ 2) + 2 * g ^ 2 * S.eval z =
            4 * S.eval z * K.eval z -
              20 * g * (Pi.eval z * q.eval z - g * S.eval z) -
              6 * m ^ 2 * q.eval z := by
        field_simp [pow_ne_zero 2 hJ.ne']
        linear_combination (hDER z hzs hzt).2 + J ^ 2 * hcancel
      have hh := JocelynClaims.claim_0e87df013ff6ff87c8e1417f336c3d7af8b88e3c61ced563738f8f3a7529574a
        m g W (Pi.eval z) (S.eval z) (q.eval z) (K.eval z)
        (N.derivative.derivative.eval z / J ^ 2) J
        hm hg0 hW hJ (hdata z hzs.le hzt.le).1 hsquared hsmall
        (hnorm z hzs.le hzt.le).1 (hnorm z hzs.le hzt.le).2.2.2.2
        (hcritical.1 z hzs.le hzt.le) hid
      have hdiv : J ^ 2 * (N.derivative.derivative.eval z / J ^ 2) =
          N.derivative.derivative.eval z := by field_simp
      simpa only [hdiv] using hh
    have hcurv := critical_squared_length N s t x m g W J hst hx0.le hm hg0 hW hJ
      hvals hc hcritical.2
    have hp := (JocelynClaims.claim_0357db812536f4b6cb95b812ac7fe480c3f6951543bd0d23ce7fef93a4c0b67e
      (t - s) |m| J M W g x C₀ 8 128
      hH hmu hJ hM hW hg0 hx0 hC₀.le (by norm_num) (by norm_num)
      hcell (by simpa only [show (8 : ℝ) ^ 2 = 64 by norm_num] using hcurv)
      hlin hcub).1
    exact hp.trans (mul_le_mul_of_nonneg_right h11K (pow_nonneg hx0.le 4))

end A5AcceptedIntervalProof

 theorem JocelynClaims.claim_6810bebe9f46765c742849f788f15b91cd6290a518eefedd90044a19dfdd4207 :
let delta : ℝ := 1 / 100000;
  ∀ C₀ c₀ : ℝ, 0 < C₀ → 0 < c₀ →
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ x M W m J g q_r s t : ℝ,
        2 ≤ x → 0 < M → 0 < W →
        m ≠ 0 → 0 < J → 1 ≤ g → q_r ≠ 0 →
        W ≤ C₀ * x →
        c₀ * (W ^ ((4 : ℝ) / 3) * x ^ (-(1 : ℝ) / 3)) ≤ M →
        c₀ * (x / W) ^ ((4 : ℝ) / 3) ≤ M →
        (t - s) * |m| * J * M ≤ C₀ * W →
        1 ≤ |q_r| * J →
        |m| ^ 3 ≤ |q_r| * J ^ 3 →
        |m| ^ 3 * x ≤ delta * W ^ 2 →
        m ^ 2 ≤ delta * g * W →
        ∀ Pi S q N : Polynomial ℝ,
          let K : Polynomial ℝ :=
            Polynomial.C q_r * Pi +
              Polynomial.C (2 : ℝ) * q * S -
              Polynomial.C (6 * g ^ 2);
          (∀ z : ℝ, s ≤ z → z ≤ t →
            W / 4 ≤ Pi.eval z ∧ Pi.eval z ≤ W ∧
            (S.eval z) ^ 2 = m ^ 2 + 4 * g * Pi.eval z ∧
            1 ≤ |q.eval z| ∧
            0 ≤ N.eval z ∧ N.eval z ≤ x ∧
            m ^ 3 * N.eval z =
              q.eval z * (Pi.eval z) ^ 2 -
                (m ^ 3 / 2 - m ^ 2 * S.eval z / 2 +
                  g * Pi.eval z * S.eval z) ∧
            Pi.derivative.eval z = J * S.eval z ∧
            S.derivative.eval z = 2 * g * J ∧
            q.derivative.eval z = q_r * J) →
          ((∀ z : ℝ, s ≤ z → z ≤ t →
              g ^ 2 / 100 ≤ K.eval z) ∨
            (∀ z : ℝ, s ≤ z → z ≤ t →
              K.eval z ≤ -(g ^ 2 / 100)) ∨
            ((∀ z : ℝ, s ≤ z → z ≤ t →
                |K.eval z| ≤ g ^ 2 / 100) ∧
              ((∀ z : ℝ, s ≤ z → z ≤ t →
                  0 ≤ N.derivative.derivative.eval z) ∨
                (∀ z : ℝ, s ≤ z → z ≤ t →
                  N.derivative.derivative.eval z ≤ 0)))) →
          t - s ≤ C *
            (1 + Real.sqrt x /
              (Real.sqrt M * W ^ ((1 : ℝ) / 3))) := by
  exact A5AcceptedIntervalProof.accepted_deep_interval_length
#print axioms JocelynClaims.claim_6810bebe9f46765c742849f788f15b91cd6290a518eefedd90044a19dfdd4207

set_option maxHeartbeats 400000

theorem JocelynClaims.claim_b5c8fea4b0e65ed2f7f25afc46786de245702559815af4387922150b1ac219bf :
∀ x D E : ℝ, ∀ d e u v : ℕ,
  2 ≤ x → 0 < D → 0 < E →
  1 ≤ d → 1 ≤ e → 1 ≤ u → 1 ≤ v →
  e ^ 2 * v = d ^ 2 * u + 1 →
  ((d ^ 2 * u : ℕ) : ℝ) ≤ x →
  D / 2 < (d : ℝ) → (d : ℝ) ≤ D →
  E / 2 < (e : ℝ) → (e : ℝ) ≤ E →
    0 < (d : ℝ) ∧ 0 < (e : ℝ) ∧
    (d : ℝ) ^ 2 ≤ x ∧ (e : ℝ) ^ 2 ≤ 2 * x ∧
    D * E ≤ 8 * x ∧
    D * E / 4 ≤ (d : ℝ) * (e : ℝ) ∧
    (d : ℝ) * (e : ℝ) ≤ D * E := by
  intro x D E d e u v hx hD hE hd he hu hv hF1 hn hdL hdU heL heU
  have hdR : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have heR : (1 : ℝ) ≤ (e : ℝ) := by exact_mod_cast he
  have huR : (1 : ℝ) ≤ (u : ℝ) := by exact_mod_cast hu
  have hvR : (1 : ℝ) ≤ (v : ℝ) := by exact_mod_cast hv
  have hdpos : 0 < (d : ℝ) := lt_of_lt_of_le zero_lt_one hdR
  have hepos : 0 < (e : ℝ) := lt_of_lt_of_le zero_lt_one heR
  have hnR : (d : ℝ) ^ 2 * (u : ℝ) ≤ x := by
    exact_mod_cast hn
  have hF1R : (e : ℝ) ^ 2 * (v : ℝ) =
      (d : ℝ) ^ 2 * (u : ℝ) + 1 := by
    exact_mod_cast hF1
  have hd2 : (d : ℝ) ^ 2 ≤ x := by
    nlinarith [mul_nonneg (sq_nonneg (d : ℝ)) (sub_nonneg.mpr huR)]
  have he2 : (e : ℝ) ^ 2 ≤ 2 * x := by
    nlinarith [mul_nonneg (sq_nonneg (e : ℝ)) (sub_nonneg.mpr hvR)]
  have hde2 : (d : ℝ) * (e : ℝ) ≤ 2 * x := by
    nlinarith [sq_nonneg ((d : ℝ) - (e : ℝ))]
  have hD2 : D ≤ 2 * (d : ℝ) := by linarith
  have hE2 : E ≤ 2 * (e : ℝ) := by linarith
  have hproduct : D * E ≤ (2 * (d : ℝ)) * (2 * (e : ℝ)) :=
    mul_le_mul hD2 hE2 hE.le (by positivity)
  have hW : D * E ≤ 8 * x := by nlinarith only [hproduct, hde2]
  have hW4 : D * E / 4 ≤ (d : ℝ) * (e : ℝ) := by
    nlinarith only [hproduct]
  have hdeW : (d : ℝ) * (e : ℝ) ≤ D * E :=
    mul_le_mul hdU heU hepos.le hD.le
  exact ⟨hdpos, hepos, hd2, he2, hW, hW4, hdeW⟩

#print axioms JocelynClaims.claim_b5c8fea4b0e65ed2f7f25afc46786de245702559815af4387922150b1ac219bf

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

namespace ConsecutiveCountingA5OriginalPairLength
open Polynomial
open ConsecutiveCountingA5OriginalAffineInterval

noncomputable def originalVPoly
    (a b c m d₀ e₀ r₀ J A₀ B₀ : ℤ) : Polynomial ℝ :=
  (originalQPoly a b c m d₀ e₀ r₀ J A₀ B₀ *
      (originalDPoly b m d₀ r₀ J) ^ 2 +
    C ((b : ℝ) ^ 2) *
      (C ((3 * a : ℤ) : ℝ) * originalDPoly b m d₀ r₀ J +
        C (b : ℝ) * originalEPoly a m e₀ r₀ J)) *
      C (((m : ℝ) ^ 3)⁻¹)

theorem real_dyadic_product
    (D E d e : ℝ) (hD : 0 < D) (hE : 0 < E)
    (hdL : D / 2 < d) (hdU : d ≤ D)
    (heL : E / 2 < e) (heU : e ≤ E) :
    D * E / 4 ≤ d * e ∧ d * e ≤ D * E := by
  have hdpos : 0 < d := lt_trans (half_pos hD) hdL
  have hepos : 0 < e := lt_trans (half_pos hE) heL
  have hlow : (D / 2) * (E / 2) ≤ d * e :=
    mul_le_mul hdL.le heL.le (half_pos hE).le hdpos.le
  have hupp : d * e ≤ D * E :=
    mul_le_mul hdU heU hepos.le hD.le
  exact ⟨by nlinarith only [hlow], hupp⟩

theorem original_accepted_pair_length
    (C_ratio c₀ : ℝ) (hC_ratio : 0 < C_ratio) (hc₀ : 0 < c₀) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ x D E M ρ₀ s t : ℝ,
        2 ≤ x → 0 < D → 0 < E → 0 < M → s ≤ t →
        c₀ * ((D * E) ^ ((4 : ℝ) / 3) * x ^ (-(1 : ℝ) / 3)) ≤ M →
        c₀ * (x / (D * E)) ^ ((4 : ℝ) / 3) ≤ M →
        ∀ a b c m d₀ e₀ r₀ J A₀ B₀ : ℤ,
          Int.gcd a b = 1 →
          c ≠ 0 → m ≠ 0 → 0 < J →
          a * d₀ + b * e₀ = 1 →
          a * B₀ - b * A₀ ≠ 0 →
          let d : Polynomial ℝ := originalDPoly b m d₀ r₀ J;
          let e : Polynomial ℝ := originalEPoly a m e₀ r₀ J;
          let q : Polynomial ℝ := originalQPoly a b c m d₀ e₀ r₀ J A₀ B₀;
          let U : Polynomial ℝ := originalUPoly a b c m d₀ e₀ r₀ J A₀ B₀;
          let V : Polynomial ℝ := originalVPoly a b c m d₀ e₀ r₀ J A₀ B₀;
          let Pi : Polynomial ℝ := originalPiPoly a b m d₀ e₀ r₀ J;
          let S : Polynomial ℝ := originalSPoly a b m d₀ e₀ r₀ J;
          let N : Polynomial ℝ := originalNPoly a b c m d₀ e₀ r₀ J A₀ B₀;
          let q_r : ℝ := originalQr a b c m A₀ B₀;
          let g : ℝ := |((a * b : ℤ) : ℝ)|;
          let K : Polynomial ℝ :=
            Polynomial.C q_r * Pi + Polynomial.C (2 : ℝ) * q * S - Polynomial.C (6 * g ^ 2);
          ∀ dn en un vn : ℕ,
            1 ≤ dn → 1 ≤ en → 1 ≤ un → 1 ≤ vn →
            ((en ^ 2 * vn : ℕ) : ℤ) =
              ((dn ^ 2 * un : ℕ) : ℤ) + 1 →
            ((dn ^ 2 * un : ℕ) : ℝ) ≤ x →
            d.eval s = (dn : ℝ) → e.eval s = (en : ℝ) →
            1 ≤ |q_r| * (J : ℝ) →
            |(m : ℝ)| ^ 3 ≤ |q_r| * (J : ℝ) ^ 3 →
            (∀ z : ℝ, s ≤ z → z ≤ t →
              D / 2 < d.eval z ∧ d.eval z ≤ D ∧
              E / 2 < e.eval z ∧ e.eval z ≤ E ∧
              ρ₀ < d.eval z / e.eval z ∧
              d.eval z / e.eval z ≤ ρ₀ + C_ratio * D / (E * M) ∧
              1 ≤ U.eval z ∧ 1 ≤ V.eval z ∧
              1 ≤ |q.eval z| ∧ N.eval z ≤ x) →
            ((∀ z : ℝ, s ≤ z → z ≤ t →
                g ^ 2 / 100 ≤ K.eval z) ∨
              (∀ z : ℝ, s ≤ z → z ≤ t →
                K.eval z ≤ -(g ^ 2 / 100)) ∨
              ((∀ z : ℝ, s ≤ z → z ≤ t →
                  |K.eval z| ≤ g ^ 2 / 100) ∧
                ((∀ z : ℝ, s ≤ z → z ≤ t →
                    0 ≤ N.derivative.derivative.eval z) ∨
                  (∀ z : ℝ, s ≤ z → z ≤ t →
                    N.derivative.derivative.eval z ≤ 0)))) →
            |t - s| ≤ C *
              (1 + Real.sqrt x /
                (Real.sqrt M * (D * E) ^ ((1 : ℝ) / 3))) := by
  let Cwide : ℝ := max C_ratio 8
  have hCwide : 0 < Cwide :=
    lt_of_lt_of_le hC_ratio (le_max_left _ _)
  have hRatioWide : C_ratio ≤ Cwide := le_max_left _ _
  have hEightWide : (8 : ℝ) ≤ Cwide := le_max_right _ _
  obtain ⟨Ccoarse, hCcoarse, hcoarseLength⟩ :=
    JocelynClaims.claim_ad943653babc9fc0202de5d0410b9c73f58141ac05bd56b58862b151978e8619
      Cwide c₀ hCwide hc₀
  obtain ⟨Cdeep, hCdeep, hdeepLength⟩ :=
    JocelynClaims.claim_6810bebe9f46765c742849f788f15b91cd6290a518eefedd90044a19dfdd4207
      Cwide c₀ hCwide hc₀
  let Cstar : ℝ := max Ccoarse Cdeep
  have hCstar : 1 ≤ Cstar := hCcoarse.trans (le_max_left _ _)
  have hCoarseStar : Ccoarse ≤ Cstar := le_max_left _ _
  have hDeepStar : Cdeep ≤ Cstar := le_max_right _ _
  refine ⟨Cstar, hCstar, ?_⟩
  intro x D E M ρ₀ s t hx hD hE hM hst hrange₁ hrange₂
    a b c m d₀ e₀ r₀ J A₀ B₀ hprim hc hm hJ hbez hDelta
  let d : Polynomial ℝ := originalDPoly b m d₀ r₀ J
  let e : Polynomial ℝ := originalEPoly a m e₀ r₀ J
  let q : Polynomial ℝ := originalQPoly a b c m d₀ e₀ r₀ J A₀ B₀
  let U : Polynomial ℝ := originalUPoly a b c m d₀ e₀ r₀ J A₀ B₀
  let V : Polynomial ℝ := originalVPoly a b c m d₀ e₀ r₀ J A₀ B₀
  let Pi : Polynomial ℝ := originalPiPoly a b m d₀ e₀ r₀ J
  let S : Polynomial ℝ := originalSPoly a b m d₀ e₀ r₀ J
  let N : Polynomial ℝ := originalNPoly a b c m d₀ e₀ r₀ J A₀ B₀
  let q_r : ℝ := originalQr a b c m A₀ B₀
  let g : ℝ := |((a * b : ℤ) : ℝ)|
  let K : Polynomial ℝ := Polynomial.C q_r * Pi + Polynomial.C (2 : ℝ) * q * S - Polynomial.C (6 * g ^ 2)
  dsimp only
  intro dn en un vn hdn hen hun hvn hF1 hn hds hes hI₁ hI₃ hclosed hbranch
  let W : ℝ := D * E
  let F : ℝ :=
    1 + Real.sqrt x / (Real.sqrt M * W ^ ((1 : ℝ) / 3))
  have hx0 : 0 < x := by linarith only [hx]
  have hW : 0 < W := mul_pos hD hE
  have hL : 0 ≤ t - s := sub_nonneg.mpr hst
  have hF : 0 ≤ F := by dsimp only [F]; positivity
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  have hJR : 0 < (J : ℝ) := by exact_mod_cast hJ
  rcases hclosed s le_rfl hst with
    ⟨hdsL, hdsU, hesL, hesU, hrsL, hrsU, hUs, hVs, hqs, hNs⟩
  rcases hclosed t hst le_rfl with
    ⟨hdtL, hdtU, hetL, hetU, hrtL, hrtU, hUt, hVt, hqt, hNt⟩
  have hF1Nat : en ^ 2 * vn = dn ^ 2 * un + 1 := by
    exact_mod_cast hF1
  have hdnL : D / 2 < (dn : ℝ) := by rw [← hds]; exact hdsL
  have hdnU : (dn : ℝ) ≤ D := by rw [← hds]; exact hdsU
  have henL : E / 2 < (en : ℝ) := by rw [← hes]; exact hesL
  have henU : (en : ℝ) ≤ E := by rw [← hes]; exact hesU
  obtain ⟨hdnPos, henPos, hdnSq, henSq, hW8, hdnProd, hdnProdUpper⟩ :=
    JocelynClaims.claim_b5c8fea4b0e65ed2f7f25afc46786de245702559815af4387922150b1ac219bf
      x D E dn en un vn hx hD hE hdn hen hun hvn hF1Nat hn
      hdnL hdnU henL henU
  have hWx : W ≤ Cwide * x :=
    hW8.trans (mul_le_mul_of_nonneg_right hEightWide hx0.le)
  rcases
      JocelynClaims.claim_38b3ece0876ba8e7eb5509d6e33bcf9b65b705370f7fb7d9f7ada061cce3632a
        a b c m d₀ e₀ r₀ J A₀ B₀ hc hm hJ hbez hDelta with
    ⟨⟨hJone, hqr, hlevel, hqderiv⟩, hpair⟩
  change C (a : ℝ) * d + C (b : ℝ) * e = C (m : ℝ) at hlevel
  change q.derivative = C (q_r * (J : ℝ)) at hqderiv
  have hendpoints :
      ∀ z : ℝ, z = s ∨ z = t →
        D / 2 < d.eval z ∧ d.eval z ≤ D ∧
        E / 2 < e.eval z ∧ e.eval z ≤ E ∧
        ρ₀ < d.eval z / e.eval z ∧
        d.eval z / e.eval z ≤ ρ₀ + C_ratio * D / (E * M) := by
    intro z hz
    rcases hz with rfl | rfl
    · exact ⟨hdsL, hdsU, hesL, hesU, hrsL, hrsU⟩
    · exact ⟨hdtL, hdtU, hetL, hetU, hrtL, hrtU⟩
  have hpairData :=
    hpair C_ratio D E M ρ₀ s t hC_ratio hD hE hM hendpoints
  have hcell : (t - s) * |(m : ℝ)| * (J : ℝ) * M ≤ Cwide * W :=
    hpairData.1.trans (mul_le_mul_of_nonneg_right hRatioWide hW.le)
  have hlevelNat :
      (m : ℝ) = (a : ℝ) * (dn : ℝ) + (b : ℝ) * (en : ℝ) := by
    have heval := congrArg (fun p : Polynomial ℝ => p.eval s) hlevel
    simp only [eval_add, eval_mul, eval_C] at heval
    change (a : ℝ) * d.eval s + (b : ℝ) * e.eval s = (m : ℝ) at heval
    rw [hds, hes] at heval
    exact heval.symm
  by_cases hcoarse :
      (1 / 100000 : ℝ) * W ^ 2 ≤ |(m : ℝ)| ^ 3 * x ∨
        (1 / 100000 : ℝ) * g * W ≤ (m : ℝ) ^ 2
  · have hlength : t - s ≤ Ccoarse * F :=
      hcoarseLength x M W (m : ℝ) (J : ℝ) (t - s) a b
        (dn : ℝ) (en : ℝ)
        hx hM hW hmR hJone hL hWx hrange₁ hrange₂ hcell hprim
        hdnPos henPos hlevelNat hdnProd hdnSq henSq hcoarse
    have hfinal : t - s ≤ Cstar * F :=
      hlength.trans (mul_le_mul_of_nonneg_right hCoarseStar hF)
    simpa only [abs_of_nonneg hL, F, W] using hfinal
  · have hfirst :
        |(m : ℝ)| ^ 3 * x < (1 / 100000 : ℝ) * W ^ 2 := by
      exact lt_of_not_ge (fun h => hcoarse (Or.inl h))
    have hsecond :
        (m : ℝ) ^ 2 < (1 / 100000 : ℝ) * g * W := by
      exact lt_of_not_ge (fun h => hcoarse (Or.inr h))
    obtain ⟨hab, hg, hsq, hPi, hS, hnum⟩ := hpairData.2 hsecond.le
    change S ^ 2 = C ((m : ℝ) ^ 2) + C (4 * g) * Pi at hsq
    change Pi.derivative = C (J : ℝ) * S at hPi
    change S.derivative = C (2 * g * (J : ℝ)) at hS
    change C ((m : ℝ) ^ 3) * N =
      q * Pi ^ 2 -
        (C ((m : ℝ) ^ 3 / 2) -
          C ((m : ℝ) ^ 2 / 2) * S + C g * Pi * S) at hnum
    have hdata :
        ∀ z : ℝ, s ≤ z → z ≤ t →
          W / 4 ≤ Pi.eval z ∧ Pi.eval z ≤ W ∧
          (S.eval z) ^ 2 = (m : ℝ) ^ 2 + 4 * g * Pi.eval z ∧
          1 ≤ |q.eval z| ∧
          0 ≤ N.eval z ∧ N.eval z ≤ x ∧
          (m : ℝ) ^ 3 * N.eval z =
            q.eval z * (Pi.eval z) ^ 2 -
              ((m : ℝ) ^ 3 / 2 - (m : ℝ) ^ 2 * S.eval z / 2 +
                g * Pi.eval z * S.eval z) ∧
          Pi.derivative.eval z = (J : ℝ) * S.eval z ∧
          S.derivative.eval z = 2 * g * (J : ℝ) ∧
          q.derivative.eval z = q_r * (J : ℝ) := by
      intro z hzs hzt
      rcases hclosed z hzs hzt with
        ⟨hdL, hdU, heL, heU, hrL, hrU, hu, hv, hq, hN⟩
      have hprod := real_dyadic_product D E (d.eval z) (e.eval z)
        hD hE hdL hdU heL heU
      have hPiEval : Pi.eval z = d.eval z * e.eval z := by
        simp only [Pi, d, e, originalPiPoly, eval_mul]
      have hNEval : N.eval z = (d.eval z) ^ 2 * U.eval z := by
        simp only [N, d, U, originalNPoly, eval_mul, eval_pow]
      have hNnonneg : 0 ≤ N.eval z := by
        rw [hNEval]
        exact mul_nonneg (sq_nonneg _) (by linarith only [hu])
      refine ⟨?_, ?_, ?_, hq, hNnonneg, hN, ?_, ?_, ?_, ?_⟩
      · rw [hPiEval]
        exact hprod.1
      · rw [hPiEval]
        exact hprod.2
      · simpa only [eval_pow, eval_add, eval_mul, eval_C] using
          congrArg (fun p : Polynomial ℝ => p.eval z) hsq
      · have heval := congrArg (fun p : Polynomial ℝ => p.eval z) hnum
        simp only [eval_mul, eval_sub, eval_add, eval_pow, eval_C] at heval
        linear_combination heval
      · simpa only [eval_mul, eval_C] using
          congrArg (fun p : Polynomial ℝ => p.eval z) hPi
      · simpa only [eval_C] using
          congrArg (fun p : Polynomial ℝ => p.eval z) hS
      · simpa only [eval_C] using
          congrArg (fun p : Polynomial ℝ => p.eval z) hqderiv
    have hlength : t - s ≤ Cdeep * F :=
      hdeepLength x M W (m : ℝ) (J : ℝ) g q_r s t
        hx hM hW hmR hJR hg hqr hWx hrange₁ hrange₂ hcell
        hI₁ hI₃ hfirst.le hsecond.le Pi S q N hdata hbranch
    have hfinal : t - s ≤ Cstar * F :=
      hlength.trans (mul_le_mul_of_nonneg_right hDeepStar hF)
    simpa only [abs_of_nonneg hL, F, W] using hfinal

#print axioms original_accepted_pair_length

end ConsecutiveCountingA5OriginalPairLength

noncomputable section
namespace A5BothSlopeConstraints
open Polynomial
set_option maxHeartbeats 1200000

theorem C_two : (C (2 : ℚ) : Polynomial ℚ) = 2 := by
  rw [show (2 : ℚ) = 1 + 1 by norm_num, C_add, C_1]
  norm_num

theorem C_three : (C (3 : ℚ) : Polynomial ℚ) = 3 := by
  rw [show (3 : ℚ) = 1 + 1 + 1 by norm_num, C_add, C_add, C_1]
  norm_num

theorem q_identity (a b m : ℚ) (D E Q : Polynomial ℚ)
    (hm : m ≠ 0) (hL : C a * D + C b * E = C m) :
    let U := C ((m ^ 3)⁻¹) *
      (Q * E ^ 2 - C (a ^ 2) * (C a * D + C (3 * b) * E));
    let V := C ((m ^ 3)⁻¹) *
      (Q * D ^ 2 + C (b ^ 2) * (C (3 * a) * D + C b * E));
    Q = C (a ^ 2) * (C a * D + C (3 * b) * E) * V +
      C (b ^ 2) * (C (3 * a) * D + C b * E) * U := by
  dsimp
  have hpoly :
      C (a ^ 2) * (C a * D + C (3 * b) * E) *
          (Q * D ^ 2 + C (b ^ 2) * (C (3 * a) * D + C b * E)) +
      C (b ^ 2) * (C (3 * a) * D + C b * E) *
          (Q * E ^ 2 - C (a ^ 2) * (C a * D + C (3 * b) * E)) =
      Q * (C a * D + C b * E) ^ 3 := by
    simp only [Polynomial.C_mul, Polynomial.C_pow, C_three]
    norm_num ; ring
  symm
  calc
    _ = C ((m ^ 3)⁻¹) *
        (C (a ^ 2) * (C a * D + C (3 * b) * E) *
          (Q * D ^ 2 + C (b ^ 2) * (C (3 * a) * D + C b * E)) +
        C (b ^ 2) * (C (3 * a) * D + C b * E) *
          (Q * E ^ 2 - C (a ^ 2) * (C a * D + C (3 * b) * E))) := by ring
    _ = C ((m ^ 3)⁻¹) * (Q * (C a * D + C b * E) ^ 3) := by rw [hpoly]
    _ = C ((m ^ 3)⁻¹) * (Q * C (m ^ 3)) := by rw [hL, Polynomial.C_pow]
    _ = Q * C ((m ^ 3)⁻¹ * m ^ 3) := by rw [Polynomial.C_mul]; ring
    _ = Q := by simp [pow_ne_zero 3 hm]

theorem affine_cubic_coeff (u0 u1 v0 v1 : ℚ) :
    ((C u0 + C u1 * X) * (C v0 + C v1 * X) ^ 2 : Polynomial ℚ).coeff 3 =
      u1 * v1 ^ 2 := by
  have hpoly : (C u0 + C u1 * X) * (C v0 + C v1 * X) ^ 2 =
      C (u0 * v0 ^ 2) +
      C (2 * u0 * v0 * v1 + u1 * v0 ^ 2) * X +
      C (u0 * v1 ^ 2 + 2 * u1 * v0 * v1) * X ^ 2 +
      C (u1 * v1 ^ 2) * X ^ 3 := by
    simp only [Polynomial.C_add, Polynomial.C_mul, Polynomial.C_pow,  C_two]
    norm_num ; ring
  rw [hpoly]
  norm_num only [Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow,
    Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C] ; simp

theorem normalform_coefficients (a b m db eb J qb qr : ℚ) :
    let D : Polynomial ℚ := C db + C (b * J) * X;
    let E : Polynomial ℚ := C eb - C (a * J) * X;
    let Q : Polynomial ℚ := C qb + C (qr * J) * X;
    let U := C ((m ^ 3)⁻¹) *
      (Q * E ^ 2 - C (a ^ 2) * (C a * D + C (3 * b) * E));
    let V := C ((m ^ 3)⁻¹) *
      (Q * D ^ 2 + C (b ^ 2) * (C (3 * a) * D + C b * E));
    U.coeff 3 = (qr * J ^ 3 / m ^ 3) * a ^ 2 ∧
    V.coeff 3 = (qr * J ^ 3 / m ^ 3) * b ^ 2 := by
  intro D E Q U V
  have he : E = C eb + C (-a * J) * X := by
    dsimp [E]
    simp only [Polynomial.C_mul, Polynomial.C_neg]
    ring
  constructor
  · dsimp [U]
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_sub, Polynomial.coeff_C_mul]
    have hz : (C a * D + C (3 * b) * E).coeff 3 = 0 := by
      norm_num only [D, E, Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_C, Polynomial.coeff_X] ; simp
    rw [hz, mul_zero, sub_zero, he]
    rw [affine_cubic_coeff]
    simp only [div_eq_mul_inv]
    ring
  · dsimp [V]
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_add, Polynomial.coeff_C_mul]
    have hz : (C (3 * a) * D + C b * E).coeff 3 = 0 := by
      norm_num only [D, E, Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_C, Polynomial.coeff_X] ; simp
    rw [hz, mul_zero, add_zero]
    rw [affine_cubic_coeff]
    simp only [div_eq_mul_inv]
    ring

theorem square_bezout (a b : ℤ) (hg : Int.gcd a b = 1) :
    ∃ r s : ℤ, r * a ^ 2 + s * b ^ 2 = 1 := by
  have hbez := Int.gcd_eq_gcd_ab a b
  rw [hg] at hbez
  norm_num at hbez
  let u := Int.gcdA a b
  let v := Int.gcdB a b
  refine ⟨a * u ^ 3 + 3 * b * u ^ 2 * v,
    3 * a * u * v ^ 2 + b * v ^ 3, ?_⟩
  calc
    _ = (a * u + b * v) ^ 3 := by ring
    _ = 1 := by rw [← hbez]; norm_num

theorem clear_denominator (T : ℕ) (U : Polynomial ℚ)
    (hDen : ∀ k : ℕ, ∃ a : ℤ, (T : ℚ) * U.coeff k = (a : ℚ)) :
    ∃ F : Polynomial ℤ,
      Polynomial.map (Int.castRingHom ℚ) F = C (T : ℚ) * U ∧
      F.natDegree ≤ U.natDegree := by
  classical
  choose a ha using hDen
  let F : Polynomial ℤ := ∑ k ∈ U.support, monomial k (a k)
  have hc (k : ℕ) : F.coeff k = if k ∈ U.support then a k else 0 := by
    simp [F, Polynomial.coeff_monomial]
  refine ⟨F, ?_, ?_⟩
  · ext k
    rw [Polynomial.coeff_map, Polynomial.coeff_C_mul, hc]
    by_cases hk : k ∈ U.support
    · rw [if_pos hk]
      change (a k : ℚ) = (T : ℚ) * U.coeff k
      exact (ha k).symm
    · have hz : U.coeff k = 0 := by
        by_contra hn
        exact hk (Polynomial.mem_support_iff.mpr hn)
      simp [hk, hz]
  · apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro k hk
    have hz : U.coeff k = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt hk
    have hnot : k ∉ U.support := fun h => (Polynomial.mem_support_iff.mp h) hz
    rw [hc, if_neg hnot]

theorem integral_lift (U : Polynomial ℚ)
    (h : ∀ k : ℕ, ∃ z : ℤ, U.coeff k = (z : ℚ)) :
    ∃ F : Polynomial ℤ, Polynomial.map (Int.castRingHom ℚ) F = U := by
  obtain ⟨F, hF, _⟩ := clear_denominator 1 U (by simpa using h)
  exact ⟨F, by simpa using hF⟩

theorem int_abs_one (z : ℤ) (hz : z ≠ 0) : (1 : ℝ) ≤ |(z : ℝ)| := by
  have h : (1 : ℤ) ≤ |z| := by
    rcases le_total 0 z with h | h
    · rw [abs_of_nonneg h]
      omega
    · rw [abs_of_nonpos h]
      omega
  exact_mod_cast h

theorem both_slope_constraints :
∀ a b m dBase eBase : ℤ,
  Int.gcd a b = 1 → m ≠ 0 → a * dBase + b * eBase = m →
  ∀ J : ℕ, 0 < J →
  ∀ qBase qr : ℚ, qr ≠ 0 →
  let D : Polynomial ℚ :=
    Polynomial.C (dBase : ℚ) +
      Polynomial.C ((b : ℚ) * (J : ℚ)) * Polynomial.X;
  let E : Polynomial ℚ :=
    Polynomial.C (eBase : ℚ) -
      Polynomial.C ((a : ℚ) * (J : ℚ)) * Polynomial.X;
  let Q : Polynomial ℚ :=
    Polynomial.C qBase + Polynomial.C (qr * (J : ℚ)) * Polynomial.X;
  let U : Polynomial ℚ :=
    Polynomial.C (((m : ℚ) ^ 3)⁻¹) *
      (Q * E ^ 2 - Polynomial.C ((a : ℚ) ^ 2) *
        (Polynomial.C (a : ℚ) * D + Polynomial.C (3 * (b : ℚ)) * E));
  let V : Polynomial ℚ :=
    Polynomial.C (((m : ℚ) ^ 3)⁻¹) *
      (Q * D ^ 2 + Polynomial.C ((b : ℚ) ^ 2) *
        (Polynomial.C (3 * (a : ℚ)) * D + Polynomial.C (b : ℚ) * E));
  (∀ k : ℕ, ∃ z : ℤ, U.coeff k = (z : ℚ)) →
  (∀ k : ℕ, ∃ z : ℤ, V.coeff k = (z : ℚ)) →
  ∃ q0 q1 theta : ℤ,
    qBase = (q0 : ℚ) ∧
    qr * (J : ℚ) = (q1 : ℚ) ∧ q1 ≠ 0 ∧
    qr * (J : ℚ) ^ 3 / (m : ℚ) ^ 3 = (theta : ℚ) ∧ theta ≠ 0 ∧
    U.coeff 3 = (theta : ℚ) * (a : ℚ) ^ 2 ∧
    V.coeff 3 = (theta : ℚ) * (b : ℚ) ^ 2 ∧
    1 ≤ |(qr : ℝ)| * (J : ℝ) ∧
    |(m : ℝ)| ^ 3 ≤ |(qr : ℝ)| * (J : ℝ) ^ 3 := by
  intro a b m dBase eBase hg hm hLevel J hJ qBase qr hqr D E Q U V hU hV
  have hmQ : (m : ℚ) ≠ 0 := by exact_mod_cast hm
  have hJQ : (J : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hJ)
  have hLevelQ : (a : ℚ) * (dBase : ℚ) + (b : ℚ) * (eBase : ℚ) = (m : ℚ) := by
    exact_mod_cast hLevel
  have hL : C (a : ℚ) * D + C (b : ℚ) * E = C (m : ℚ) := by
    calc
      _ = C ((a : ℚ) * (dBase : ℚ) + (b : ℚ) * (eBase : ℚ)) := by
        dsimp [D, E]
        simp only [Polynomial.C_mul, Polynomial.C_add]
        ring
      _ = C (m : ℚ) := by rw [hLevelQ]
  have hQid := q_identity (a : ℚ) (b : ℚ) (m : ℚ) D E Q hmQ hL
  obtain ⟨UZ, hUZ⟩ := integral_lift U hU
  obtain ⟨VZ, hVZ⟩ := integral_lift V hV
  let DZ : Polynomial ℤ := C dBase + C (b * (J : ℤ)) * X
  let EZ : Polynomial ℤ := C eBase - C (a * (J : ℤ)) * X
  let RZ : Polynomial ℤ :=
    C (a ^ 2) * (C a * DZ + C (3 * b) * EZ) * VZ +
      C (b ^ 2) * (C (3 * a) * DZ + C b * EZ) * UZ
  have hDZ : Polynomial.map (Int.castRingHom ℚ) DZ = D := by
    simp only [DZ, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X]
    change C (dBase : ℚ) + C ((b * (J : ℤ) : ℤ) : ℚ) * X =
      C (dBase : ℚ) + C ((b : ℚ) * (J : ℚ)) * X
    push_cast ; rfl
  have hEZ : Polynomial.map (Int.castRingHom ℚ) EZ = E := by
    simp only [EZ, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X]
    change C (eBase : ℚ) - C ((a * (J : ℤ) : ℤ) : ℚ) * X =
      C (eBase : ℚ) - C ((a : ℚ) * (J : ℚ)) * X
    push_cast ; rfl
  have hRZ : Polynomial.map (Int.castRingHom ℚ) RZ = Q := by
    dsimp only [RZ]
    simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, hDZ, hEZ, hUZ, hVZ]
    change C ((a ^ 2 : ℤ) : ℚ) *
        (C (a : ℚ) * D + C ((3 * b : ℤ) : ℚ) * E) * V +
      C ((b ^ 2 : ℤ) : ℚ) *
        (C ((3 * a : ℤ) : ℚ) * D + C (b : ℚ) * E) * U = Q
    push_cast
    exact hQid.symm
  let q0 : ℤ := RZ.coeff 0
  let q1 : ℤ := RZ.coeff 1
  have hq0 : qBase = (q0 : ℚ) := by
    calc
      qBase = Q.coeff 0 := by simp [Q]
      _ = (Polynomial.map (Int.castRingHom ℚ) RZ).coeff 0 := by rw [hRZ]
      _ = (q0 : ℚ) := by rw [Polynomial.coeff_map]; rfl
  have hq1 : qr * (J : ℚ) = (q1 : ℚ) := by
    calc
      qr * (J : ℚ) = Q.coeff 1 := by simp [Q]
      _ = (Polynomial.map (Int.castRingHom ℚ) RZ).coeff 1 := by rw [hRZ]
      _ = (q1 : ℚ) := by rw [Polynomial.coeff_map]; rfl
  have hq1ne : q1 ≠ 0 := by
    intro hz
    have hh : qr * (J : ℚ) = 0 := by simpa [hz] using hq1
    exact (mul_ne_zero hqr hJQ) hh
  have hcoeff := normalform_coefficients
    (a : ℚ) (b : ℚ) (m : ℚ) (dBase : ℚ) (eBase : ℚ) (J : ℚ) qBase qr
  change U.coeff 3 = (qr * (J : ℚ) ^ 3 / (m : ℚ) ^ 3) * (a : ℚ) ^ 2 ∧
    V.coeff 3 = (qr * (J : ℚ) ^ 3 / (m : ℚ) ^ 3) * (b : ℚ) ^ 2 at hcoeff
  obtain ⟨u3, hu3⟩ := hU 3
  obtain ⟨v3, hv3⟩ := hV 3
  obtain ⟨r, s, hBez⟩ := square_bezout a b hg
  have hBezQ : (r : ℚ) * (a : ℚ) ^ 2 + (s : ℚ) * (b : ℚ) ^ 2 = 1 := by
    exact_mod_cast hBez
  let theta : ℤ := r * u3 + s * v3
  have htheta : qr * (J : ℚ) ^ 3 / (m : ℚ) ^ 3 = (theta : ℚ) := by
    calc
      _ = (qr * (J : ℚ) ^ 3 / (m : ℚ) ^ 3) *
          ((r : ℚ) * (a : ℚ) ^ 2 + (s : ℚ) * (b : ℚ) ^ 2) := by rw [hBezQ]; ring
      _ = (r : ℚ) * U.coeff 3 + (s : ℚ) * V.coeff 3 := by
        rw [hcoeff.1, hcoeff.2]
        ring
      _ = (theta : ℚ) := by rw [hu3, hv3]; dsimp [theta]; push_cast; ring
  have htheta_ne : theta ≠ 0 := by
    intro hz
    have hh : qr * (J : ℚ) ^ 3 / (m : ℚ) ^ 3 = 0 := by simpa [hz] using htheta
    exact (div_ne_zero (mul_ne_zero hqr (pow_ne_zero 3 hJQ)) (pow_ne_zero 3 hmQ)) hh
  have hJR : 0 < (J : ℝ) := by exact_mod_cast hJ
  have hq1R : (qr : ℝ) * (J : ℝ) = (q1 : ℝ) := by exact_mod_cast hq1
  have hthetaR : (qr : ℝ) * (J : ℝ) ^ 3 / (m : ℝ) ^ 3 = (theta : ℝ) := by
    exact_mod_cast htheta
  have hfirst := int_abs_one q1 hq1ne
  rw [← hq1R, abs_mul, abs_of_pos hJR] at hfirst
  have hsecond := int_abs_one theta htheta_ne
  rw [← hthetaR, abs_div, abs_mul, abs_pow, abs_pow, abs_of_pos hJR] at hsecond
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  have hpos : 0 < |(m : ℝ)| ^ 3 := pow_pos (abs_pos.mpr hmR) 3
  have hsecond' : |(m : ℝ)| ^ 3 ≤ |(qr : ℝ)| * (J : ℝ) ^ 3 := by
    simpa using (le_div_iff₀ hpos).mp hsecond
  refine ⟨q0, q1, theta, hq0, hq1, hq1ne, htheta, htheta_ne, ?_, ?_, hfirst, hsecond'⟩
  · simpa only [htheta] using hcoeff.1
  · simpa only [htheta] using hcoeff.2

end A5BothSlopeConstraints

namespace JocelynClaims
theorem claim_b20fb00c289b46c6cb005003d0e0086120eafd6e44eca3aad0e9eee1f8d7564f :
∀ a b m dBase eBase : ℤ,
  Int.gcd a b = 1 → m ≠ 0 → a * dBase + b * eBase = m →
  ∀ J : ℕ, 0 < J →
  ∀ qBase qr : ℚ, qr ≠ 0 →
  let D : Polynomial ℚ :=
    Polynomial.C (dBase : ℚ) +
      Polynomial.C ((b : ℚ) * (J : ℚ)) * Polynomial.X;
  let E : Polynomial ℚ :=
    Polynomial.C (eBase : ℚ) -
      Polynomial.C ((a : ℚ) * (J : ℚ)) * Polynomial.X;
  let Q : Polynomial ℚ :=
    Polynomial.C qBase + Polynomial.C (qr * (J : ℚ)) * Polynomial.X;
  let U : Polynomial ℚ :=
    Polynomial.C (((m : ℚ) ^ 3)⁻¹) *
      (Q * E ^ 2 - Polynomial.C ((a : ℚ) ^ 2) *
        (Polynomial.C (a : ℚ) * D + Polynomial.C (3 * (b : ℚ)) * E));
  let V : Polynomial ℚ :=
    Polynomial.C (((m : ℚ) ^ 3)⁻¹) *
      (Q * D ^ 2 + Polynomial.C ((b : ℚ) ^ 2) *
        (Polynomial.C (3 * (a : ℚ)) * D + Polynomial.C (b : ℚ) * E));
  (∀ k : ℕ, ∃ z : ℤ, U.coeff k = (z : ℚ)) →
  (∀ k : ℕ, ∃ z : ℤ, V.coeff k = (z : ℚ)) →
  ∃ q0 q1 theta : ℤ,
    qBase = (q0 : ℚ) ∧
    qr * (J : ℚ) = (q1 : ℚ) ∧ q1 ≠ 0 ∧
    qr * (J : ℚ) ^ 3 / (m : ℚ) ^ 3 = (theta : ℚ) ∧ theta ≠ 0 ∧
    U.coeff 3 = (theta : ℚ) * (a : ℚ) ^ 2 ∧
    V.coeff 3 = (theta : ℚ) * (b : ℚ) ^ 2 ∧
    1 ≤ |(qr : ℝ)| * (J : ℝ) ∧
    |(m : ℝ)| ^ 3 ≤ |(qr : ℝ)| * (J : ℝ) ^ 3 := by
  exact A5BothSlopeConstraints.both_slope_constraints
end JocelynClaims

#print axioms A5BothSlopeConstraints.both_slope_constraints
#print axioms JocelynClaims.claim_b20fb00c289b46c6cb005003d0e0086120eafd6e44eca3aad0e9eee1f8d7564f

namespace A5ActualSignedFamilyIntegerConstraints
open Polynomial
set_option maxHeartbeats 2000000
set_option maxRecDepth 5000

theorem actual_constraints :
∀ a b c m d₀ e₀ r₀ A₀ B₀ : ℤ,
  Int.gcd a b = 1 → c ≠ 0 → m ≠ 0 →
  a * d₀ + b * e₀ = 1 → a * B₀ - b * A₀ ≠ 0 →
  ∀ J : ℕ, 0 < J →
  let X₀ : MvPolynomial (Fin 2) ℤ := MvPolynomial.X (0 : Fin 2);
  let X₁ : MvPolynomial (Fin 2) ℤ := MvPolynomial.X (1 : Fin 2);
  let P : MvPolynomial (Fin 2) ℤ :=
    (MvPolynomial.C A₀ * X₀ + MvPolynomial.C B₀ * X₁) * X₁ ^ 2 -
      MvPolynomial.C c *
        (MvPolynomial.C a * X₀ + MvPolynomial.C b * X₁) ^ 2 *
        MvPolynomial.C (a ^ 2) *
        (MvPolynomial.C a * X₀ + MvPolynomial.C (3 * b) * X₁);
  let Q : MvPolynomial (Fin 2) ℤ :=
    (MvPolynomial.C A₀ * X₀ + MvPolynomial.C B₀ * X₁) * X₀ ^ 2 +
      MvPolynomial.C c *
        (MvPolynomial.C a * X₀ + MvPolynomial.C b * X₁) ^ 2 *
        MvPolynomial.C (b ^ 2) *
        (MvPolynomial.C (3 * a) * X₀ + MvPolynomial.C b * X₁);
  let D : Polynomial ℚ :=
    Polynomial.C ((m * d₀ : ℤ) : ℚ) + Polynomial.C (b : ℚ) * Polynomial.X;
  let E : Polynomial ℚ :=
    Polynomial.C ((m * e₀ : ℤ) : ℚ) - Polynomial.C (a : ℚ) * Polynomial.X;
  let R : Polynomial ℚ :=
    Polynomial.C (r₀ : ℚ) + Polynomial.C (J : ℚ) * Polynomial.X;
  let U : Polynomial ℚ :=
    Polynomial.C (((c : ℚ) * (m : ℚ) ^ 5)⁻¹) *
      MvPolynomial.eval₂ (Int.castRingHom (Polynomial ℚ)) ![D, E] P;
  let V : Polynomial ℚ :=
    Polynomial.C (((c : ℚ) * (m : ℚ) ^ 5)⁻¹) *
      MvPolynomial.eval₂ (Int.castRingHom (Polynomial ℚ)) ![D, E] Q;
  let qBase : ℚ :=
    ((A₀ : ℚ) * ((m * d₀ + b * r₀ : ℤ) : ℚ) +
      (B₀ : ℚ) * ((m * e₀ - a * r₀ : ℤ) : ℚ)) /
        ((c : ℚ) * (m : ℚ) ^ 2);
  let qr : ℚ :=
    ((A₀ : ℚ) * (b : ℚ) - (B₀ : ℚ) * (a : ℚ)) /
      ((c : ℚ) * (m : ℚ) ^ 2);
  (∀ k : ℕ, ∃ z : ℤ, (U.comp R).coeff k = (z : ℚ)) →
  (∀ k : ℕ, ∃ z : ℤ, (V.comp R).coeff k = (z : ℚ)) →
  ∃ q0 q1 theta : ℤ,
    qBase = (q0 : ℚ) ∧
    qr * (J : ℚ) = (q1 : ℚ) ∧ q1 ≠ 0 ∧
    qr * (J : ℚ) ^ 3 / (m : ℚ) ^ 3 = (theta : ℚ) ∧ theta ≠ 0 ∧
    (U.comp R).coeff 3 = (theta : ℚ) * (a : ℚ) ^ 2 ∧
    (V.comp R).coeff 3 = (theta : ℚ) * (b : ℚ) ^ 2 ∧
    1 ≤ |(qr : ℝ)| * (J : ℝ) ∧
    |(m : ℝ)| ^ 3 ≤ |(qr : ℝ)| * (J : ℝ) ^ 3 := by
  intro a b c m d₀ e₀ r₀ A₀ B₀ hab hc hm hbez hDelta J hJ X₀ X₁ P Q D E R U V qBase qr hUInt hVInt
  have hcQ : (c : ℚ) ≠ 0 := by exact_mod_cast hc
  have hmQ : (m : ℚ) ≠ 0 := by exact_mod_cast hm
  have hbezQ : (a : ℚ) * (d₀ : ℚ) + (b : ℚ) * (e₀ : ℚ) = 1 := by
    exact_mod_cast hbez
  let db : ℤ := m * d₀ + b * r₀
  let eb : ℤ := m * e₀ - a * r₀
  have hbase : a * db + b * eb = m := by
    calc
      _ = m * (a * d₀ + b * e₀) := by dsimp only [db, eb]; ring
      _ = m := by rw [hbez]; ring
  have hqr : qr ≠ 0 := by
    have hn : A₀ * b - B₀ * a ≠ 0 := by
      intro hn
      apply hDelta
      linear_combination -hn
    have hnQ : (A₀ : ℚ) * (b : ℚ) - (B₀ : ℚ) * (a : ℚ) ≠ 0 := by
      exact_mod_cast hn
    exact div_ne_zero hnQ (mul_ne_zero hcQ (pow_ne_zero 2 hmQ))
  let DP : Polynomial ℚ := C (db : ℚ) + C ((b : ℚ) * (J : ℚ)) * X
  let EP : Polynomial ℚ := C (eb : ℚ) - C ((a : ℚ) * (J : ℚ)) * X
  let qP : Polynomial ℚ := C qBase + C (qr * (J : ℚ)) * X
  let UN : Polynomial ℚ :=
    C (((m : ℚ) ^ 3)⁻¹) *
      (qP * EP ^ 2 - C ((a : ℚ) ^ 2) *
        (C (a : ℚ) * DP + C (3 * (b : ℚ)) * EP))
  let VN : Polynomial ℚ :=
    C (((m : ℚ) ^ 3)⁻¹) *
      (qP * DP ^ 2 + C ((b : ℚ) ^ 2) *
        (C (3 * (a : ℚ)) * DP + C (b : ℚ) * EP))
  have hD : D.comp R = DP := by
    dsimp only [D, R, DP, db]
    simp only [add_comp, mul_comp, C_comp, X_comp]
    push_cast
    simp only [map_add,  map_mul]
    ring
  have hE : E.comp R = EP := by
    dsimp only [E, R, EP, eb]
    simp only [sub_comp, mul_comp, C_comp, X_comp]
    push_cast
    simp only [ map_sub, map_mul]
    ring
  have hlevel : C (a : ℚ) * DP + C (b : ℚ) * EP = C (m : ℚ) := by
    apply Polynomial.funext
    intro z
    simp only [DP, EP, db, eb, eval_add, eval_sub, eval_mul, eval_C, eval_X,
      Int.cast_add, Int.cast_sub, Int.cast_mul]
    calc
      _ = (m : ℚ) * ((a : ℚ) * (d₀ : ℚ) + (b : ℚ) * (e₀ : ℚ)) := by ring
      _ = (m : ℚ) := by rw [hbezQ]; ring
  have hEll : C (A₀ : ℚ) * DP + C (B₀ : ℚ) * EP =
      C ((c : ℚ) * (m : ℚ) ^ 2) * qP := by
    apply Polynomial.funext
    intro z
    simp only [DP, EP, qP, qBase, qr, db, eb, eval_add, eval_sub,
      eval_mul, eval_C, eval_X, Int.cast_add, Int.cast_sub, Int.cast_mul]
    field_simp [hcQ, hmQ] ; ring
  have evalInt (f : Fin 2 → Polynomial ℚ) (z : ℤ) :
      MvPolynomial.eval₂ (Int.castRingHom (Polynomial ℚ)) f
        (z : MvPolynomial (Fin 2) ℤ) = (z : Polynomial ℚ) := by
    exact map_intCast (MvPolynomial.eval₂Hom (Int.castRingHom (Polynomial ℚ)) f) z
  have hU : U =
      C (((c : ℚ) * (m : ℚ) ^ 5)⁻¹) *
        ((C (A₀ : ℚ) * D + C (B₀ : ℚ) * E) * E ^ 2 -
          C (c : ℚ) * (C (a : ℚ) * D + C (b : ℚ) * E) ^ 2 *
            C ((a : ℚ) ^ 2) * (C (a : ℚ) * D + C (3 * (b : ℚ)) * E)) := by
    simp [U, P, X₀, X₁, evalInt, A5BothSlopeConstraints.C_three] <;> push_cast
  have hV : V =
      C (((c : ℚ) * (m : ℚ) ^ 5)⁻¹) *
        ((C (A₀ : ℚ) * D + C (B₀ : ℚ) * E) * D ^ 2 +
          C (c : ℚ) * (C (a : ℚ) * D + C (b : ℚ) * E) ^ 2 *
            C ((b : ℚ) ^ 2) * (C (3 * (a : ℚ)) * D + C (b : ℚ) * E)) := by
    simp [V, Q, X₀, X₁, evalInt, A5BothSlopeConstraints.C_three] <;> push_cast
  have hUN : U.comp R = UN := by
    rw [hU]
    simp only [mul_comp, sub_comp, add_comp, pow_comp, C_comp, hD, hE]
    rw [hlevel, hEll]
    apply Polynomial.funext
    intro z
    simp only [UN, eval_mul, eval_sub, eval_add, eval_pow, eval_C]
    field_simp [hcQ, hmQ]
  have hVN : V.comp R = VN := by
    rw [hV]
    simp only [mul_comp,  add_comp, pow_comp, C_comp, hD, hE]
    rw [hlevel, hEll]
    apply Polynomial.funext
    intro z
    simp only [VN, eval_mul,  eval_add, eval_pow, eval_C]
    field_simp [hcQ, hmQ]
  have hUNI : ∀ k : ℕ, ∃ z : ℤ, UN.coeff k = (z : ℚ) := by
    simpa only [hUN] using hUInt
  have hVNI : ∀ k : ℕ, ∃ z : ℤ, VN.coeff k = (z : ℚ) := by
    simpa only [hVN] using hVInt
  have h := JocelynClaims.claim_b20fb00c289b46c6cb005003d0e0086120eafd6e44eca3aad0e9eee1f8d7564f
    a b m db eb hab hm hbase J hJ qBase qr hqr hUNI hVNI
  simpa only [hUN, hVN] using h

end A5ActualSignedFamilyIntegerConstraints

namespace JocelynClaims
theorem claim_23901e5a643bd6f3764df51b1a387d0e23f431c522eaa8213ba45390c29b2129 :
∀ a b c m d₀ e₀ r₀ A₀ B₀ : ℤ,
  Int.gcd a b = 1 → c ≠ 0 → m ≠ 0 →
  a * d₀ + b * e₀ = 1 → a * B₀ - b * A₀ ≠ 0 →
  ∀ J : ℕ, 0 < J →
  let X₀ : MvPolynomial (Fin 2) ℤ := MvPolynomial.X (0 : Fin 2);
  let X₁ : MvPolynomial (Fin 2) ℤ := MvPolynomial.X (1 : Fin 2);
  let P : MvPolynomial (Fin 2) ℤ :=
    (MvPolynomial.C A₀ * X₀ + MvPolynomial.C B₀ * X₁) * X₁ ^ 2 -
      MvPolynomial.C c *
        (MvPolynomial.C a * X₀ + MvPolynomial.C b * X₁) ^ 2 *
        MvPolynomial.C (a ^ 2) *
        (MvPolynomial.C a * X₀ + MvPolynomial.C (3 * b) * X₁);
  let Q : MvPolynomial (Fin 2) ℤ :=
    (MvPolynomial.C A₀ * X₀ + MvPolynomial.C B₀ * X₁) * X₀ ^ 2 +
      MvPolynomial.C c *
        (MvPolynomial.C a * X₀ + MvPolynomial.C b * X₁) ^ 2 *
        MvPolynomial.C (b ^ 2) *
        (MvPolynomial.C (3 * a) * X₀ + MvPolynomial.C b * X₁);
  let D : Polynomial ℚ :=
    Polynomial.C ((m * d₀ : ℤ) : ℚ) + Polynomial.C (b : ℚ) * Polynomial.X;
  let E : Polynomial ℚ :=
    Polynomial.C ((m * e₀ : ℤ) : ℚ) - Polynomial.C (a : ℚ) * Polynomial.X;
  let R : Polynomial ℚ :=
    Polynomial.C (r₀ : ℚ) + Polynomial.C (J : ℚ) * Polynomial.X;
  let U : Polynomial ℚ :=
    Polynomial.C (((c : ℚ) * (m : ℚ) ^ 5)⁻¹) *
      MvPolynomial.eval₂ (Int.castRingHom (Polynomial ℚ)) ![D, E] P;
  let V : Polynomial ℚ :=
    Polynomial.C (((c : ℚ) * (m : ℚ) ^ 5)⁻¹) *
      MvPolynomial.eval₂ (Int.castRingHom (Polynomial ℚ)) ![D, E] Q;
  let qBase : ℚ :=
    ((A₀ : ℚ) * ((m * d₀ + b * r₀ : ℤ) : ℚ) +
      (B₀ : ℚ) * ((m * e₀ - a * r₀ : ℤ) : ℚ)) /
        ((c : ℚ) * (m : ℚ) ^ 2);
  let qr : ℚ :=
    ((A₀ : ℚ) * (b : ℚ) - (B₀ : ℚ) * (a : ℚ)) /
      ((c : ℚ) * (m : ℚ) ^ 2);
  (∀ k : ℕ, ∃ z : ℤ, (U.comp R).coeff k = (z : ℚ)) →
  (∀ k : ℕ, ∃ z : ℤ, (V.comp R).coeff k = (z : ℚ)) →
  ∃ q0 q1 theta : ℤ,
    qBase = (q0 : ℚ) ∧
    qr * (J : ℚ) = (q1 : ℚ) ∧ q1 ≠ 0 ∧
    qr * (J : ℚ) ^ 3 / (m : ℚ) ^ 3 = (theta : ℚ) ∧ theta ≠ 0 ∧
    (U.comp R).coeff 3 = (theta : ℚ) * (a : ℚ) ^ 2 ∧
    (V.comp R).coeff 3 = (theta : ℚ) * (b : ℚ) ^ 2 ∧
    1 ≤ |(qr : ℝ)| * (J : ℝ) ∧
    |(m : ℝ)| ^ 3 ≤ |(qr : ℝ)| * (J : ℝ) ^ 3 := by
  exact A5ActualSignedFamilyIntegerConstraints.actual_constraints
end JocelynClaims

#print axioms JocelynClaims.claim_23901e5a643bd6f3764df51b1a387d0e23f431c522eaa8213ba45390c29b2129

namespace ConsecutiveCountingA5SameJQArithmetic
open Polynomial
open ConsecutiveCountingA5OriginalAffineInterval

def rationalQBase
    (a b c m d₀ e₀ r₀ A₀ B₀ : ℤ) : ℚ :=
  ((A₀ : ℚ) * ((m * d₀ + b * r₀ : ℤ) : ℚ) +
    (B₀ : ℚ) * ((m * e₀ - a * r₀ : ℤ) : ℚ)) /
      ((c : ℚ) * (m : ℚ) ^ 2)

def rationalQr (a b c m A₀ B₀ : ℤ) : ℚ :=
  ((A₀ : ℚ) * (b : ℚ) - (B₀ : ℚ) * (a : ℚ)) /
    ((c : ℚ) * (m : ℚ) ^ 2)

theorem original_qr_eq_ratCast
    (a b c m A₀ B₀ : ℤ) :
    originalQr a b c m A₀ B₀ =
      ((rationalQr a b c m A₀ B₀ : ℚ) : ℝ) := by
  dsimp only [originalQr, rationalQr]
  push_cast <;> rfl

theorem original_q_eval_affine
    (a b c m d₀ e₀ r₀ A₀ B₀ : ℤ) (J : ℕ) (s : ℝ) :
    (originalQPoly a b c m d₀ e₀ r₀ (J : ℤ) A₀ B₀).eval s =
      ((rationalQBase a b c m d₀ e₀ r₀ A₀ B₀ : ℚ) : ℝ) +
        ((rationalQr a b c m A₀ B₀ : ℚ) : ℝ) * (J : ℝ) * s := by
  simp only [originalQPoly, originalDPoly, originalEPoly,
    eval_mul, eval_add, eval_sub, eval_C, eval_X]
  dsimp only [rationalQBase, rationalQr]
  push_cast <;> simp only [div_eq_mul_inv] <;> ring

theorem original_q_eval_integer
    (a b c m d₀ e₀ r₀ A₀ B₀ q₀ q₁ : ℤ) (J : ℕ)
    (hbase : rationalQBase a b c m d₀ e₀ r₀ A₀ B₀ = (q₀ : ℚ))
    (hslope : rationalQr a b c m A₀ B₀ * (J : ℚ) = (q₁ : ℚ))
    (t : ℤ) :
    (originalQPoly a b c m d₀ e₀ r₀ (J : ℤ) A₀ B₀).eval (t : ℝ) =
      ((q₀ + q₁ * t : ℤ) : ℝ) := by
  have hbaseR :
      ((rationalQBase a b c m d₀ e₀ r₀ A₀ B₀ : ℚ) : ℝ) =
        (q₀ : ℝ) := by
    exact_mod_cast hbase
  have hslopeR :
      ((rationalQr a b c m A₀ B₀ : ℚ) : ℝ) * (J : ℝ) =
        (q₁ : ℝ) := by
    exact_mod_cast hslope
  rw [original_q_eval_affine, hbaseR, hslopeR]
  push_cast <;> rfl

theorem integer_zero_or_one_abs (z : ℤ) :
    (z : ℝ) = 0 ∨ 1 ≤ |(z : ℝ)| := by
  by_cases hz : z = 0
  · left
    simp only [hz, Int.cast_zero]
  · right
    have h : (1 : ℤ) ≤ |z| := by
      rcases le_total 0 z with h | h
      · rw [abs_of_nonneg h]
        omega
      · rw [abs_of_nonpos h]
        omega
    exact_mod_cast h

theorem integer_affine_zero_unique
    (q₀ q₁ s t : ℤ) (hq₁ : q₁ ≠ 0)
    (hs : ((q₀ + q₁ * s : ℤ) : ℝ) = 0)
    (ht : ((q₀ + q₁ * t : ℤ) : ℝ) = 0) :
    s = t := by
  have hsZ : q₀ + q₁ * s = 0 := by exact_mod_cast hs
  have htZ : q₀ + q₁ * t = 0 := by exact_mod_cast ht
  have hprod : q₁ * (s - t) = 0 := by
    linear_combination hsZ - htZ
  exact sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_left hq₁)

theorem original_integer_q_gap
    (a b c m d₀ e₀ r₀ A₀ B₀ q₀ q₁ : ℤ) (J : ℕ)
    (hbase : rationalQBase a b c m d₀ e₀ r₀ A₀ B₀ = (q₀ : ℚ))
    (hslope : rationalQr a b c m A₀ B₀ * (J : ℚ) = (q₁ : ℚ))
    (t : ℤ) :
    (originalQPoly a b c m d₀ e₀ r₀ (J : ℤ) A₀ B₀).eval (t : ℝ) = 0 ∨
      1 ≤ |(originalQPoly a b c m d₀ e₀ r₀ (J : ℤ) A₀ B₀).eval (t : ℝ)| := by
  rw [original_q_eval_integer a b c m d₀ e₀ r₀ A₀ B₀ q₀ q₁ J hbase hslope t]
  exact integer_zero_or_one_abs (q₀ + q₁ * t)

theorem original_q_zero_unique
    (a b c m d₀ e₀ r₀ A₀ B₀ q₀ q₁ : ℤ) (J : ℕ)
    (hbase : rationalQBase a b c m d₀ e₀ r₀ A₀ B₀ = (q₀ : ℚ))
    (hslope : rationalQr a b c m A₀ B₀ * (J : ℚ) = (q₁ : ℚ))
    (hq₁ : q₁ ≠ 0) (s t : ℤ)
    (hs : (originalQPoly a b c m d₀ e₀ r₀ (J : ℤ) A₀ B₀).eval (s : ℝ) = 0)
    (ht : (originalQPoly a b c m d₀ e₀ r₀ (J : ℤ) A₀ B₀).eval (t : ℝ) = 0) :
    s = t := by
  rw [original_q_eval_integer a b c m d₀ e₀ r₀ A₀ B₀ q₀ q₁ J hbase hslope s] at hs
  rw [original_q_eval_integer a b c m d₀ e₀ r₀ A₀ B₀ q₀ q₁ J hbase hslope t] at ht
  exact integer_affine_zero_unique q₀ q₁ s t hq₁ hs ht

theorem original_q_zero_filter_card
    (a b c m d₀ e₀ r₀ A₀ B₀ q₀ q₁ : ℤ) (J : ℕ)
    (hbase : rationalQBase a b c m d₀ e₀ r₀ A₀ B₀ = (q₀ : ℚ))
    (hslope : rationalQr a b c m A₀ B₀ * (J : ℚ) = (q₁ : ℚ))
    (hq₁ : q₁ ≠ 0) (T : Finset ℤ) :
    (T.filter fun t : ℤ =>
      (originalQPoly a b c m d₀ e₀ r₀ (J : ℤ) A₀ B₀).eval (t : ℝ) = 0).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro s hs t ht
  exact original_q_zero_unique a b c m d₀ e₀ r₀ A₀ B₀ q₀ q₁ J
    hbase hslope hq₁ s t
    (Finset.mem_filter.mp hs).2 (Finset.mem_filter.mp ht).2

theorem original_sameJ_int_constraints
    (a b c m A₀ B₀ : ℤ) (J : ℕ)
    (h₁ : 1 ≤ |((rationalQr a b c m A₀ B₀ : ℚ) : ℝ)| * (J : ℝ))
    (h₃ : |(m : ℝ)| ^ 3 ≤
      |((rationalQr a b c m A₀ B₀ : ℚ) : ℝ)| * (J : ℝ) ^ 3) :
    1 ≤ |originalQr a b c m A₀ B₀| * ((J : ℤ) : ℝ) ∧
    |(m : ℝ)| ^ 3 ≤ |originalQr a b c m A₀ B₀| * ((J : ℤ) : ℝ) ^ 3 := by
  simpa only [original_qr_eq_ratCast, Int.cast_natCast] using And.intro h₁ h₃

theorem original_sameJ_integer_q_join
    (a b c m d₀ e₀ r₀ A₀ B₀ q₀ q₁ : ℤ) (J : ℕ)
    (hbase : rationalQBase a b c m d₀ e₀ r₀ A₀ B₀ = (q₀ : ℚ))
    (hslope : rationalQr a b c m A₀ B₀ * (J : ℚ) = (q₁ : ℚ))
    (hq₁ : q₁ ≠ 0) :
    originalQr a b c m A₀ B₀ =
        ((rationalQr a b c m A₀ B₀ : ℚ) : ℝ) ∧
    (∀ t : ℤ,
      (originalQPoly a b c m d₀ e₀ r₀ (J : ℤ) A₀ B₀).eval (t : ℝ) =
        ((q₀ + q₁ * t : ℤ) : ℝ)) ∧
    (∀ t : ℤ,
      (originalQPoly a b c m d₀ e₀ r₀ (J : ℤ) A₀ B₀).eval (t : ℝ) = 0 ∨
      1 ≤ |(originalQPoly a b c m d₀ e₀ r₀ (J : ℤ) A₀ B₀).eval (t : ℝ)|) ∧
    (∀ T : Finset ℤ,
      (T.filter fun t : ℤ =>
        (originalQPoly a b c m d₀ e₀ r₀ (J : ℤ) A₀ B₀).eval (t : ℝ) = 0).card ≤ 1) := by
  exact ⟨original_qr_eq_ratCast a b c m A₀ B₀,
    original_q_eval_integer a b c m d₀ e₀ r₀ A₀ B₀ q₀ q₁ J hbase hslope,
    original_integer_q_gap a b c m d₀ e₀ r₀ A₀ B₀ q₀ q₁ J hbase hslope,
    original_q_zero_filter_card a b c m d₀ e₀ r₀ A₀ B₀ q₀ q₁ J hbase hslope hq₁⟩

end ConsecutiveCountingA5SameJQArithmetic

namespace ConsecutiveCountingA5PureCubicRange

theorem original_positive_point_bounded
    (x : ℝ) (N : ℕ) (hN : x + 2 < N)
    (d e u v : ℕ)
    (hd : 1 ≤ d) (he : 1 ≤ e) (hu : 1 ≤ u) (hv : 1 ≤ v)
    (hF1 : ((e ^ 2 * v : ℕ) : ℤ) = ((d ^ 2 * u : ℕ) : ℤ) + 1)
    (hx : ((d ^ 2 * u : ℕ) : ℝ) ≤ x) :
    d ≤ N ∧ e ≤ N ∧ u ≤ N ∧ v ≤ N := by
  have hF1nat : e ^ 2 * v = d ^ 2 * u + 1 := by exact_mod_cast hF1
  have hdx : (d : ℝ) ≤ x := by
    have hdu : d ≤ d ^ 2 * u := by
      have hpow : d ≤ d ^ 2 := by nlinarith
      have hmul : d ^ 2 ≤ d ^ 2 * u := by
        have := Nat.mul_le_mul_left (d ^ 2) hu
        simpa using this
      omega
    exact le_trans (by exact_mod_cast hdu) hx
  have hex : (e : ℝ) ≤ x + 1 := by
    have hev : e ≤ e ^ 2 * v := by
      have hpow : e ≤ e ^ 2 := by nlinarith
      have hmul : e ^ 2 ≤ e ^ 2 * v := by
        have := Nat.mul_le_mul_left (e ^ 2) hv
        simpa using this
      omega
    have hrel : ((e ^ 2 * v : ℕ) : ℝ) = ((d ^ 2 * u : ℕ) : ℝ) + 1 := by
      exact_mod_cast hF1nat
    have hle : (e : ℝ) ≤ ((e ^ 2 * v : ℕ) : ℝ) := by exact_mod_cast hev
    exact le_trans hle (by linarith)
  have hux : (u : ℝ) ≤ x := by
    have hdu : u ≤ d ^ 2 * u := by
      have hpow : 1 ≤ d ^ 2 := by nlinarith
      have := Nat.mul_le_mul_right u hpow
      simpa using this
    exact le_trans (by exact_mod_cast hdu) hx
  have hvx : (v : ℝ) ≤ x + 1 := by
    have hev : v ≤ e ^ 2 * v := by
      have hpow : 1 ≤ e ^ 2 := by nlinarith
      have := Nat.mul_le_mul_right v hpow
      simpa using this
    have hrel : ((e ^ 2 * v : ℕ) : ℝ) = ((d ^ 2 * u : ℕ) : ℝ) + 1 := by
      exact_mod_cast hF1nat
    have hle : (v : ℝ) ≤ ((e ^ 2 * v : ℕ) : ℝ) := by exact_mod_cast hev
    exact le_trans hle (by linarith)
  have hdN : d ≤ N := by exact_mod_cast (show (d : ℝ) ≤ N by linarith)
  have heN : e ≤ N := by exact_mod_cast (show (e : ℝ) ≤ N by linarith)
  have huN : u ≤ N := by exact_mod_cast (show (u : ℝ) ≤ N by linarith)
  have hvN : v ≤ N := by exact_mod_cast (show (v : ℝ) ≤ N by linarith)
  exact ⟨hdN,heN,huN,hvN⟩

end ConsecutiveCountingA5PureCubicRange

namespace ConsecutiveCountingA5PureCubicRange

def OriginalS
    (x D E M ρ₀ C₀ : ℝ) (P Q : MvPolynomial (Fin 2) ℤ) :
    Set ((ℕ × ℕ) × (ℕ × ℕ)) :=
  {q | 1 ≤ q.1.1 ∧ 1 ≤ q.1.2 ∧
    1 ≤ q.2.1 ∧ 1 ≤ q.2.2 ∧
    ((q.1.2 ^ 2 * q.2.2 : ℕ) : ℤ) =
      ((q.1.1 ^ 2 * q.2.1 : ℕ) : ℤ) + 1 ∧
    ((q.1.1 ^ 2 * q.2.1 : ℕ) : ℝ) ≤ x ∧
    D / 2 < (q.1.1 : ℝ) ∧ (q.1.1 : ℝ) ≤ D ∧
    E / 2 < (q.1.2 : ℝ) ∧ (q.1.2 : ℝ) ≤ E ∧
    ρ₀ < (q.1.1 : ℝ) / (q.1.2 : ℝ) ∧
    (q.1.1 : ℝ) / (q.1.2 : ℝ) ≤
      ρ₀ + C₀ * D / (E * M) ∧
    (q.2.1 : ℤ) *
        MvPolynomial.eval ![(q.1.1 : ℤ), (q.1.2 : ℤ)] Q =
      (q.2.2 : ℤ) *
        MvPolynomial.eval ![(q.1.1 : ℤ), (q.1.2 : ℤ)] P}

theorem originalS_finite
    (x D E M ρ₀ C₀ : ℝ) (P Q : MvPolynomial (Fin 2) ℤ) :
    (OriginalS x D E M ρ₀ C₀ P Q).Finite := by
  obtain ⟨N, hN⟩ := exists_nat_gt (x + 2)
  let B : Set ((ℕ × ℕ) × (ℕ × ℕ)) :=
    (Set.Iic N ×ˢ Set.Iic N) ×ˢ
      (Set.Iic N ×ˢ Set.Iic N)
  have hB : B.Finite := by
    have hNfin : (Set.Iic N).Finite := Set.finite_Iic N
    exact (hNfin.prod hNfin).prod (hNfin.prod hNfin)
  apply hB.subset
  intro q hq
  change q ∈ B
  rcases hq with ⟨hd,he,hu,hv,hF1,hx,_⟩
  obtain ⟨hdN,heN,huN,hvN⟩ :=
    original_positive_point_bounded x N hN
      q.1.1 q.1.2 q.2.1 q.2.2
      hd he hu hv hF1 hx
  simp only [B, Set.mem_prod, Set.mem_Iic]
  exact ⟨⟨hdN,heN⟩,⟨huN,hvN⟩⟩

theorem original_uv_unique
    (d e u₁ v₁ u₂ v₂ pval qval c m : ℤ)
    (he : e ≠ 0) (hc : c ≠ 0) (hm : m ≠ 0)
    (hdet : e ^ 2 * qval - d ^ 2 * pval = c * m ^ 5)
    (hF1₁ : e ^ 2 * v₁ = d ^ 2 * u₁ + 1)
    (hF1₂ : e ^ 2 * v₂ = d ^ 2 * u₂ + 1)
    (hpar₁ : u₁ * qval = v₁ * pval)
    (hpar₂ : u₂ * qval = v₂ * pval) :
    u₁ = u₂ ∧ v₁ = v₂ := by
  have hdetne : e ^ 2 * qval - d ^ 2 * pval ≠ 0 := by
    rw [hdet]
    exact mul_ne_zero hc (pow_ne_zero 5 hm)
  have hFdiff : e ^ 2 * (v₁ - v₂) = d ^ 2 * (u₁ - u₂) := by
    linarith
  have hPdiff : (u₁ - u₂) * qval = (v₁ - v₂) * pval := by
    linarith
  have hzero :
      (u₁ - u₂) * (e ^ 2 * qval - d ^ 2 * pval) = 0 := by
    calc
      (u₁ - u₂) * (e ^ 2 * qval - d ^ 2 * pval) =
        e ^ 2 * ((u₁ - u₂) * qval) -
          d ^ 2 * ((u₁ - u₂) * pval) := by ring
      _ = e ^ 2 * ((v₁ - v₂) * pval) -
          d ^ 2 * ((u₁ - u₂) * pval) := by rw [hPdiff]
      _ = (e ^ 2 * (v₁ - v₂) -
          d ^ 2 * (u₁ - u₂)) * pval := by ring
      _ = 0 := by rw [hFdiff]; ring
  have hu : u₁ = u₂ := by
    have hh := (mul_eq_zero.mp hzero)
    rcases hh with hh | hh
    · omega
    · exact False.elim (hdetne hh)
  have hv : v₁ = v₂ := by
    have he2 : e ^ 2 ≠ 0 := pow_ne_zero 2 he
    have hh : e ^ 2 * (v₁ - v₂) = 0 := by
      rw [hu] at hFdiff
      simpa using hFdiff
    rcases mul_eq_zero.mp hh with hh | hh
    · exact False.elim (he2 hh)
    · omega
  exact ⟨hu,hv⟩

end ConsecutiveCountingA5PureCubicRange

namespace ConsecutiveCountingA5PureCubicRange

theorem pure_eval_det
    (P Q : MvPolynomial (Fin 2) ℤ)
    (a b c d e : ℤ)
    (hpure : MvPolynomial.X (1 : Fin 2) ^ 2 * Q -
      MvPolynomial.X (0 : Fin 2) ^ 2 * P =
      MvPolynomial.C c *
        (MvPolynomial.C a * MvPolynomial.X 0 +
          MvPolynomial.C b * MvPolynomial.X 1) ^ 5) :
    e ^ 2 * MvPolynomial.eval ![d,e] Q -
      d ^ 2 * MvPolynomial.eval ![d,e] P =
        c * (a * d + b * e) ^ 5 := by
  have h := congrArg (MvPolynomial.eval ![d,e]) hpure
  simpa [MvPolynomial.eval_sub, MvPolynomial.eval_mul,
    MvPolynomial.eval_pow, MvPolynomial.eval_add,
    MvPolynomial.eval_C, MvPolynomial.eval_X] using h

def levelR (d₀ e₀ : ℤ)
    (q : (ℕ × ℕ) × (ℕ × ℕ)) : ℤ :=
  e₀ * (q.1.1 : ℤ) - d₀ * (q.1.2 : ℤ)

def levelT (d₀ e₀ r₀ J : ℤ)
    (q : (ℕ × ℕ) × (ℕ × ℕ)) : ℤ :=
  (levelR d₀ e₀ q - r₀) / J

def FixedProgressionS
    (x D E M ρ₀ C₀ : ℝ) (P Q : MvPolynomial (Fin 2) ℤ)
    (a b m d₀ e₀ r₀ J : ℤ) :
    Set ((ℕ × ℕ) × (ℕ × ℕ)) :=
  {q | q ∈ OriginalS x D E M ρ₀ C₀ P Q ∧
    a * (q.1.1 : ℤ) + b * (q.1.2 : ℤ) = m ∧
    levelR d₀ e₀ q =
      r₀ + J * levelT d₀ e₀ r₀ J q}

theorem fixedProgressionS_finite
    (x D E M ρ₀ C₀ : ℝ) (P Q : MvPolynomial (Fin 2) ℤ)
    (a b m d₀ e₀ r₀ J : ℤ) :
    (FixedProgressionS x D E M ρ₀ C₀ P Q a b m d₀ e₀ r₀ J).Finite := by
  exact (originalS_finite x D E M ρ₀ C₀ P Q).subset (by
    intro q hq
    exact hq.1)

theorem fixed_level_coordinate_unique
    (a b m d₀ e₀ d₁ e₁ d₂ e₂ : ℤ)
    (hbez : a * d₀ + b * e₀ = 1)
    (hlevel₁ : a * d₁ + b * e₁ = m)
    (hlevel₂ : a * d₂ + b * e₂ = m)
    (hr : e₀ * d₁ - d₀ * e₁ =
      e₀ * d₂ - d₀ * e₂) :
    d₁ = d₂ ∧ e₁ = e₂ := by
  have hd₁ : d₁ = m * d₀ +
      b * (e₀ * d₁ - d₀ * e₁) := by
    calc
      d₁ = (a * d₀ + b * e₀) * d₁ := by rw [hbez]; ring
      _ = (a * d₁ + b * e₁) * d₀ +
          b * (e₀ * d₁ - d₀ * e₁) := by ring
      _ = _ := by rw [hlevel₁]
  have hd₂ : d₂ = m * d₀ +
      b * (e₀ * d₂ - d₀ * e₂) := by
    calc
      d₂ = (a * d₀ + b * e₀) * d₂ := by rw [hbez]; ring
      _ = (a * d₂ + b * e₂) * d₀ +
          b * (e₀ * d₂ - d₀ * e₂) := by ring
      _ = _ := by rw [hlevel₂]
  have he₁ : e₁ = m * e₀ -
      a * (e₀ * d₁ - d₀ * e₁) := by
    calc
      e₁ = (a * d₀ + b * e₀) * e₁ := by rw [hbez]; ring
      _ = (a * d₁ + b * e₁) * e₀ -
          a * (e₀ * d₁ - d₀ * e₁) := by ring
      _ = _ := by rw [hlevel₁]
  have he₂ : e₂ = m * e₀ -
      a * (e₀ * d₂ - d₀ * e₂) := by
    calc
      e₂ = (a * d₀ + b * e₀) * e₂ := by rw [hbez]; ring
      _ = (a * d₂ + b * e₂) * e₀ -
          a * (e₀ * d₂ - d₀ * e₂) := by ring
      _ = _ := by rw [hlevel₂]
  rw [hr] at hd₁ he₁
  exact ⟨hd₁.trans hd₂.symm, he₁.trans he₂.symm⟩

end ConsecutiveCountingA5PureCubicRange

namespace ConsecutiveCountingA5PureCubicRange

theorem fixed_progression_levelT_injective
    (x D E M ρ₀ C₀ : ℝ)
    (P Q : MvPolynomial (Fin 2) ℤ)
    (a b c m d₀ e₀ r₀ J : ℤ)
    (hc : c ≠ 0) (hm : m ≠ 0)
    (hbez : a * d₀ + b * e₀ = 1)
    (hpure : MvPolynomial.X (1 : Fin 2) ^ 2 * Q -
      MvPolynomial.X (0 : Fin 2) ^ 2 * P =
      MvPolynomial.C c *
        (MvPolynomial.C a * MvPolynomial.X 0 +
          MvPolynomial.C b * MvPolynomial.X 1) ^ 5)
    (q₁ q₂ : (ℕ × ℕ) × (ℕ × ℕ))
    (hq₁ : q₁ ∈ FixedProgressionS x D E M ρ₀ C₀
      P Q a b m d₀ e₀ r₀ J)
    (hq₂ : q₂ ∈ FixedProgressionS x D E M ρ₀ C₀
      P Q a b m d₀ e₀ r₀ J)
    (ht : levelT d₀ e₀ r₀ J q₁ =
      levelT d₀ e₀ r₀ J q₂) :
    q₁ = q₂ := by
  rcases hq₁ with ⟨hOrig₁,hlevel₁,hprog₁⟩
  rcases hq₂ with ⟨hOrig₂,hlevel₂,hprog₂⟩
  have hr : levelR d₀ e₀ q₁ = levelR d₀ e₀ q₂ := by
    rw [hprog₁, hprog₂, ht]
  have hdeZ := fixed_level_coordinate_unique a b m d₀ e₀
    (q₁.1.1 : ℤ) (q₁.1.2 : ℤ)
    (q₂.1.1 : ℤ) (q₂.1.2 : ℤ)
    hbez hlevel₁ hlevel₂ (by simpa [levelR] using hr)
  have hd : q₁.1.1 = q₂.1.1 := by exact_mod_cast hdeZ.1
  have he : q₁.1.2 = q₂.1.2 := by exact_mod_cast hdeZ.2
  rcases hOrig₁ with
    ⟨_,hepos,_,_,hF1₁,_,_,_,_,_,_,_,hpar₁⟩
  rcases hOrig₂ with
    ⟨_,_,_,_,hF1₂,_,_,_,_,_,_,_,hpar₂⟩
  rw [← hd, ← he] at hF1₂ hpar₂
  have heZ : (q₁.1.2 : ℤ) ≠ 0 := by
    have hne : q₁.1.2 ≠ 0 := by omega
    exact_mod_cast hne
  have hdet := pure_eval_det P Q a b c
    (q₁.1.1 : ℤ) (q₁.1.2 : ℤ) hpure
  rw [hlevel₁] at hdet
  have hF1z₁ :
      (q₁.1.2 : ℤ) ^ 2 * (q₁.2.2 : ℤ) =
        (q₁.1.1 : ℤ) ^ 2 * (q₁.2.1 : ℤ) + 1 := by
    exact_mod_cast hF1₁
  have hF1z₂ :
      (q₁.1.2 : ℤ) ^ 2 * (q₂.2.2 : ℤ) =
        (q₁.1.1 : ℤ) ^ 2 * (q₂.2.1 : ℤ) + 1 := by
    exact_mod_cast hF1₂
  have huv := original_uv_unique
    (q₁.1.1 : ℤ) (q₁.1.2 : ℤ)
    (q₁.2.1 : ℤ) (q₁.2.2 : ℤ)
    (q₂.2.1 : ℤ) (q₂.2.2 : ℤ)
    (MvPolynomial.eval ![(q₁.1.1 : ℤ), (q₁.1.2 : ℤ)] P)
    (MvPolynomial.eval ![(q₁.1.1 : ℤ), (q₁.1.2 : ℤ)] Q)
    c m heZ hc hm hdet hF1z₁ hF1z₂ hpar₁ hpar₂
  have hu : q₁.2.1 = q₂.2.1 := by exact_mod_cast huv.1
  have hv : q₁.2.2 = q₂.2.2 := by exact_mod_cast huv.2
  exact Prod.ext (Prod.ext hd he) (Prod.ext hu hv)

end ConsecutiveCountingA5PureCubicRange

namespace ConsecutiveCountingA5PureCubicRange

theorem fixed_progression_actual_image_card
    (x D E M ρ₀ C₀ : ℝ)
    (P Q : MvPolynomial (Fin 2) ℤ)
    (a b c m d₀ e₀ r₀ J : ℤ)
    (hc : c ≠ 0) (hm : m ≠ 0)
    (hbez : a * d₀ + b * e₀ = 1)
    (hpure : MvPolynomial.X (1 : Fin 2) ^ 2 * Q -
      MvPolynomial.X (0 : Fin 2) ^ 2 * P =
      MvPolynomial.C c *
        (MvPolynomial.C a * MvPolynomial.X 0 +
          MvPolynomial.C b * MvPolynomial.X 1) ^ 5) :
    let sf := (fixedProgressionS_finite x D E M ρ₀ C₀
      P Q a b m d₀ e₀ r₀ J).toFinset
    sf.card = (sf.image (levelT d₀ e₀ r₀ J)).card := by
  classical
  let sf := (fixedProgressionS_finite x D E M ρ₀ C₀
    P Q a b m d₀ e₀ r₀ J).toFinset
  have hmaps : Set.MapsTo (levelT d₀ e₀ r₀ J)
      (↑sf : Set ((ℕ × ℕ) × (ℕ × ℕ)))
      (↑(sf.image (levelT d₀ e₀ r₀ J)) : Set ℤ) := by
    intro q hq
    exact Finset.mem_image.mpr ⟨q, hq, rfl⟩
  have hinj : Set.InjOn (levelT d₀ e₀ r₀ J)
      (↑sf : Set ((ℕ × ℕ) × (ℕ × ℕ))) := by
    intro q₁ hq₁ q₂ hq₂ ht
    exact fixed_progression_levelT_injective x D E M ρ₀ C₀
      P Q a b c m d₀ e₀ r₀ J hc hm hbez hpure
      q₁ q₂ (by simpa [sf] using hq₁)
      (by simpa [sf] using hq₂) ht
  change sf.card = (sf.image (levelT d₀ e₀ r₀ J)).card
  exact le_antisymm
    (Finset.card_le_card_of_injOn
      (levelT d₀ e₀ r₀ J) hmaps hinj)
    Finset.card_image_le

end ConsecutiveCountingA5PureCubicRange

namespace ConsecutiveCountingA5PureCubicRange
theorem original_signed_level_parameter
    (a b d0 e0 d e m : ℤ)
    (hbez : a * d0 + b * e0 = 1)
    (hlevel : a * d + b * e = m) :
    let r : ℤ := e0 * d - d0 * e
    d = m * d0 + b * r ∧
    e = m * e0 - a * r := by
  dsimp
  constructor
  · calc
      d = (a * d0 + b * e0) * d := by rw [hbez]; ring
      _ = (a * d + b * e) * d0 +
            b * (e0 * d - d0 * e) := by ring
      _ = m * d0 + b * (e0 * d - d0 * e) := by rw [hlevel]
  · calc
      e = (a * d0 + b * e0) * e := by rw [hbez]; ring
      _ = (a * d + b * e) * e0 -
            a * (e0 * d - d0 * e) := by ring
      _ = m * e0 - a * (e0 * d - d0 * e) := by rw [hlevel]

end ConsecutiveCountingA5PureCubicRange

namespace ConsecutiveCountingA5PureCubicRange

end ConsecutiveCountingA5PureCubicRange

namespace ConsecutiveCountingA5PureCubicRange
theorem original_int_interval_card
    (S : Finset ℤ) (a b : ℤ)
    (hS : ∀ t ∈ S, a ≤ t ∧ t ≤ b) :
    S.card ≤ (b - a + 1).toNat := by
  have hsub : S ⊆ Finset.Icc a b := by
    intro t ht
    exact Finset.mem_Icc.mpr (hS t ht)
  calc
    S.card ≤ (Finset.Icc a b).card := Finset.card_le_card hsub
    _ = (b - a + 1).toNat := by simp <;> omega

end ConsecutiveCountingA5PureCubicRange

namespace ConsecutiveCountingA5PureCubicRange

theorem integer_pair_diameter_card
    (T : Finset ℤ) (A : ℝ) (hA : 0 ≤ A)
    (hpair : ∀ s ∈ T, ∀ t ∈ T, s ≤ t →
      ((t - s : ℤ) : ℝ) ≤ A) :
    T.card ≤ 2 * Nat.ceil A + 1 := by
  by_cases hT : T = ∅
  · simp [hT]
  have hnon : T.Nonempty := Finset.nonempty_iff_ne_empty.mpr hT
  rcases hnon with ⟨t₀,ht₀⟩
  let c : ℕ := Nat.ceil A
  have hceil : A ≤ (c : ℝ) := Nat.le_ceil A
  have hbound : ∀ t ∈ T,
      t₀ - (c : ℤ) ≤ t ∧ t ≤ t₀ + (c : ℤ) := by
    intro t ht
    by_cases h : t ≤ t₀
    · have hreal : ((t₀ - t : ℤ) : ℝ) ≤ (c : ℝ) :=
        le_trans (hpair t ht t₀ ht₀ h) hceil
      have hint : t₀ - t ≤ (c : ℤ) := by exact_mod_cast hreal
      constructor <;> omega
    · have hlt : t₀ ≤ t := by omega
      have hreal : ((t - t₀ : ℤ) : ℝ) ≤ (c : ℝ) :=
        le_trans (hpair t₀ ht₀ t ht hlt) hceil
      have hint : t - t₀ ≤ (c : ℤ) := by exact_mod_cast hreal
      constructor <;> omega
  have hcard := original_int_interval_card T
    (t₀ - (c : ℤ)) (t₀ + (c : ℤ)) hbound
  have hsimp :
      (t₀ + (c : ℤ) - (t₀ - (c : ℤ)) + 1).toNat =
        2 * c + 1 := by omega
  rw [hsimp] at hcard
  exact hcard

end ConsecutiveCountingA5PureCubicRange

namespace ConsecutiveCountingA5PureCubicRange
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

noncomputable def originalVPoly
    (a b c m d₀ e₀ r₀ J A₀ B₀ : ℤ) : Polynomial ℝ :=
  (originalQPoly a b c m d₀ e₀ r₀ J A₀ B₀ *
      (originalDPoly b m d₀ r₀ J) ^ 2 +
    C ((b : ℝ) ^ 2) *
      (C ((3 * a : ℤ) : ℝ) * originalDPoly b m d₀ r₀ J +
        C (b : ℝ) * originalEPoly a m e₀ r₀ J)) *
      C (((m : ℝ) ^ 3)⁻¹)

theorem originalDPoly_eval
    (b m d₀ r₀ J t : ℤ) :
    eval (t : ℝ) (originalDPoly b m d₀ r₀ J) =
      ((m * d₀ + b * (r₀ + J * t) : ℤ) : ℝ) := by
  simp [originalDPoly, eval_add, eval_mul, eval_C, eval_X]
  push_cast
  ring

theorem originalEPoly_eval
    (a m e₀ r₀ J t : ℤ) :
    eval (t : ℝ) (originalEPoly a m e₀ r₀ J) =
      ((m * e₀ - a * (r₀ + J * t) : ℤ) : ℝ) := by
  simp [originalEPoly, eval_sub, eval_mul, eval_C, eval_X]
  push_cast
  ring

theorem originalQPoly_eval
    (a b c m d₀ e₀ r₀ J A₀ B₀ t : ℤ) :
    eval (t : ℝ)
      (originalQPoly a b c m d₀ e₀ r₀ J A₀ B₀) =
      ((A₀ : ℝ) * ((m * d₀ + b * (r₀ + J * t) : ℤ) : ℝ) +
        (B₀ : ℝ) * ((m * e₀ - a * (r₀ + J * t) : ℤ) : ℝ)) /
        ((c : ℝ) * (m : ℝ) ^ 2) := by
  simp [originalQPoly, eval_add, eval_mul, eval_C,
    originalDPoly_eval, originalEPoly_eval, div_eq_mul_inv]

theorem originalUPoly_eval
    (a b c m d₀ e₀ r₀ J A₀ B₀ t : ℤ) :
    eval (t : ℝ)
      (originalUPoly a b c m d₀ e₀ r₀ J A₀ B₀) =
      (eval (t : ℝ) (originalQPoly a b c m d₀ e₀ r₀ J A₀ B₀) *
          eval (t : ℝ) (originalEPoly a m e₀ r₀ J) ^ 2 -
        (a : ℝ) ^ 2 *
          ((a : ℝ) * eval (t : ℝ)
              (originalDPoly b m d₀ r₀ J) +
            ((3 * b : ℤ) : ℝ) * eval (t : ℝ)
              (originalEPoly a m e₀ r₀ J))) /
        (m : ℝ) ^ 3 := by
  simp [originalUPoly, eval_sub, eval_add, eval_mul,
    eval_pow, eval_C, div_eq_mul_inv]

end ConsecutiveCountingA5PureCubicRange

namespace ConsecutiveCountingA5PureCubicRange
open Polynomial

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

noncomputable def originalKPoly
    (a b c m d₀ e₀ r₀ J A₀ B₀ : ℤ) (g : ℝ) :
    Polynomial ℝ :=
  C (originalQr a b c m A₀ B₀) *
      originalPiPoly a b m d₀ e₀ r₀ J +
    C (2 : ℝ) *
      originalQPoly a b c m d₀ e₀ r₀ J A₀ B₀ *
      originalSPoly a b m d₀ e₀ r₀ J -
    C (6 * g ^ 2)

noncomputable def originalBoundaryRawList
    (x D E M ρ₀ C₀ : ℝ)
    (a b c m d₀ e₀ r₀ J A₀ B₀ : ℤ)
    (g η : ℝ) : List (Polynomial ℝ) := by
  classical
  let d := originalDPoly b m d₀ r₀ J
  let e := originalEPoly a m e₀ r₀ J
  let q := originalQPoly a b c m d₀ e₀ r₀ J A₀ B₀
  let u := originalUPoly a b c m d₀ e₀ r₀ J A₀ B₀
  let v := originalVPoly a b c m d₀ e₀ r₀ J A₀ B₀
  let k := originalKPoly a b c m d₀ e₀ r₀ J A₀ B₀ g
  let h := C₀ * D / (E * M)
  exact
    ([d, e,
      d - C 1, e - C 1,
      d - C (D / 2), C D - d,
      e - C (E / 2), C E - e,
      d - C ρ₀ * e, C (ρ₀ + h) * e - d,
      u - C 1, v - C 1,
      C x - d ^ 2 * u,
      q, q - C 1, -q - C 1,
      k - C (η * g ^ 2), -k - C (η * g ^ 2),
      C (η * g ^ 2) - k, C (η * g ^ 2) + k] :
      List (Polynomial ℝ))

noncomputable def originalBoundaryCandidates
    (x D E M ρ₀ C₀ : ℝ)
    (a b c m d₀ e₀ r₀ J A₀ B₀ : ℤ)
    (g η : ℝ) : Finset (Polynomial ℝ) :=
  (originalBoundaryRawList x D E M ρ₀ C₀
    a b c m d₀ e₀ r₀ J A₀ B₀ g η).toFinset.filter (· ≠ 0)

end ConsecutiveCountingA5PureCubicRange

namespace ConsecutiveCountingA5PureCubicRange
open Polynomial

theorem original_parallel_pq_values
    (d e u v pval qval c m : ℤ)
    (hF1 : e ^ 2 * v = d ^ 2 * u + 1)
    (hparallel : u * qval = v * pval)
    (hdet : e ^ 2 * qval - d ^ 2 * pval = c * m ^ 5) :
    pval = c * m ^ 5 * u ∧
      qval = c * m ^ 5 * v := by
  have hdiff : e ^ 2 * v - d ^ 2 * u = 1 := by
    linarith only [hF1]
  constructor
  · calc
      pval = (e ^ 2 * v - d ^ 2 * u) * pval := by
        rw [hdiff]; ring
      _ = u * (e ^ 2 * qval - d ^ 2 * pval) := by
        linear_combination -(e ^ 2) * hparallel
      _ = c * m ^ 5 * u := by rw [hdet]; ring
  · calc
      qval = (e ^ 2 * v - d ^ 2 * u) * qval := by
        rw [hdiff]; ring
      _ = v * (e ^ 2 * qval - d ^ 2 * pval) := by
        linear_combination -(d ^ 2) * hparallel
      _ = c * m ^ 5 * v := by rw [hdet]; ring

theorem originalVPoly_eval
    (a b c m d₀ e₀ r₀ J A₀ B₀ t : ℤ) :
    eval (t : ℝ)
      (originalVPoly a b c m d₀ e₀ r₀ J A₀ B₀) =
      (eval (t : ℝ) (originalQPoly a b c m d₀ e₀ r₀ J A₀ B₀) *
          eval (t : ℝ) (originalDPoly b m d₀ r₀ J) ^ 2 +
        (b : ℝ) ^ 2 *
          (((3 * a : ℤ) : ℝ) * eval (t : ℝ)
              (originalDPoly b m d₀ r₀ J) +
            (b : ℝ) * eval (t : ℝ)
              (originalEPoly a m e₀ r₀ J))) /
        (m : ℝ) ^ 3 := by
  simp [originalVPoly, eval_add, eval_mul,
    eval_pow, eval_C, div_eq_mul_inv]

theorem originalUPoly_eval_of_normal_identity
    (a b c m d₀ e₀ r₀ J A₀ B₀ t d e u : ℤ)
    (hc : c ≠ 0) (hm : m ≠ 0)
    (hd : d = m * d₀ + b * (r₀ + J * t))
    (he : e = m * e₀ - a * (r₀ + J * t))
    (hU : c * m ^ 5 * u =
      (A₀ * d + B₀ * e) * e ^ 2 -
        c * m ^ 2 * a ^ 2 * (a * d + 3 * b * e)) :
    eval (t : ℝ)
      (originalUPoly a b c m d₀ e₀ r₀ J A₀ B₀) =
        (u : ℝ) := by
  have hcR : (c : ℝ) ≠ 0 := by exact_mod_cast hc
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  have hUR :
      (c : ℝ) * (m : ℝ) ^ 5 * (u : ℝ) =
        ((A₀ : ℝ) * (d : ℝ) + (B₀ : ℝ) * (e : ℝ)) *
            (e : ℝ) ^ 2 -
          (c : ℝ) * (m : ℝ) ^ 2 * (a : ℝ) ^ 2 *
            ((a : ℝ) * (d : ℝ) + 3 * (b : ℝ) * (e : ℝ)) := by
    exact_mod_cast hU
  rw [originalUPoly_eval, originalQPoly_eval,
    originalDPoly_eval, originalEPoly_eval]
  rw [← hd, ← he]
  push_cast
  field_simp [hcR, hmR]
  nlinarith only [hUR]

theorem originalVPoly_eval_of_normal_identity
    (a b c m d₀ e₀ r₀ J A₀ B₀ t d e v : ℤ)
    (hc : c ≠ 0) (hm : m ≠ 0)
    (hd : d = m * d₀ + b * (r₀ + J * t))
    (he : e = m * e₀ - a * (r₀ + J * t))
    (hV : c * m ^ 5 * v =
      (A₀ * d + B₀ * e) * d ^ 2 +
        c * m ^ 2 * b ^ 2 * (3 * a * d + b * e)) :
    eval (t : ℝ)
      (originalVPoly a b c m d₀ e₀ r₀ J A₀ B₀) =
        (v : ℝ) := by
  have hcR : (c : ℝ) ≠ 0 := by exact_mod_cast hc
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  have hVR :
      (c : ℝ) * (m : ℝ) ^ 5 * (v : ℝ) =
        ((A₀ : ℝ) * (d : ℝ) + (B₀ : ℝ) * (e : ℝ)) *
            (d : ℝ) ^ 2 +
          (c : ℝ) * (m : ℝ) ^ 2 * (b : ℝ) ^ 2 *
            (3 * (a : ℝ) * (d : ℝ) + (b : ℝ) * (e : ℝ)) := by
    exact_mod_cast hV
  rw [originalVPoly_eval, originalQPoly_eval,
    originalDPoly_eval, originalEPoly_eval]
  rw [← hd, ← he]
  push_cast
  field_simp [hcR, hmR]
  nlinarith only [hVR]

noncomputable def originalNPoly
    (a b c m d₀ e₀ r₀ J A₀ B₀ : ℤ) : Polynomial ℝ :=
  (originalDPoly b m d₀ r₀ J) ^ 2 *
    originalUPoly a b c m d₀ e₀ r₀ J A₀ B₀

noncomputable def originalBoundaryCandidatesWithCurvature
    (x D E M ρ₀ C₀ : ℝ)
    (a b c m d₀ e₀ r₀ J A₀ B₀ : ℤ)
    (g η : ℝ) : Finset (Polynomial ℝ) := by
  classical
  let n := originalNPoly a b c m d₀ e₀ r₀ J A₀ B₀
  exact
    (insert (derivative (derivative n))
      (originalBoundaryCandidates x D E M ρ₀ C₀
        a b c m d₀ e₀ r₀ J A₀ B₀ g η)).filter (· ≠ 0)

end ConsecutiveCountingA5PureCubicRange

namespace ConsecutiveCountingA5PureCubicRange
open Polynomial

theorem actual_original_point_eval_UV
    (x D E M ρ₀ C₀ : ℝ)
    (P Q : MvPolynomial (Fin 2) ℤ)
    (a b c m d₀ e₀ r₀ J A₀ B₀ : ℤ)
    (hc : c ≠ 0) (hm : m ≠ 0)
    (hbez : a * d₀ + b * e₀ = 1)
    (hpure : MvPolynomial.X (1 : Fin 2) ^ 2 * Q -
      MvPolynomial.X (0 : Fin 2) ^ 2 * P =
      MvPolynomial.C c *
        (MvPolynomial.C a * MvPolynomial.X 0 +
          MvPolynomial.C b * MvPolynomial.X 1) ^ 5)
    (hPnorm : P =
      (MvPolynomial.C A₀ * MvPolynomial.X (0 : Fin 2) +
        MvPolynomial.C B₀ * MvPolynomial.X (1 : Fin 2)) *
          MvPolynomial.X (1 : Fin 2) ^ 2 -
        MvPolynomial.C c *
          (MvPolynomial.C a * MvPolynomial.X (0 : Fin 2) +
            MvPolynomial.C b * MvPolynomial.X (1 : Fin 2)) ^ 2 *
          MvPolynomial.C (a ^ 2) *
          (MvPolynomial.C a * MvPolynomial.X (0 : Fin 2) +
            MvPolynomial.C (3 * b) * MvPolynomial.X (1 : Fin 2)))
    (hQnorm : Q =
      (MvPolynomial.C A₀ * MvPolynomial.X (0 : Fin 2) +
        MvPolynomial.C B₀ * MvPolynomial.X (1 : Fin 2)) *
          MvPolynomial.X (0 : Fin 2) ^ 2 +
        MvPolynomial.C c *
          (MvPolynomial.C a * MvPolynomial.X (0 : Fin 2) +
            MvPolynomial.C b * MvPolynomial.X (1 : Fin 2)) ^ 2 *
          MvPolynomial.C (b ^ 2) *
          (MvPolynomial.C (3 * a) * MvPolynomial.X (0 : Fin 2) +
            MvPolynomial.C b * MvPolynomial.X (1 : Fin 2)))
    (q : (ℕ × ℕ) × (ℕ × ℕ))
    (hq : q ∈ FixedProgressionS x D E M ρ₀ C₀
      P Q a b m d₀ e₀ r₀ J) :
    eval ((levelT d₀ e₀ r₀ J q : ℤ) : ℝ)
        (originalUPoly a b c m d₀ e₀ r₀ J A₀ B₀) =
        (q.2.1 : ℝ) ∧
      eval ((levelT d₀ e₀ r₀ J q : ℤ) : ℝ)
        (originalVPoly a b c m d₀ e₀ r₀ J A₀ B₀) =
        (q.2.2 : ℝ) := by
  rcases hq with ⟨hOrig,hlevel,hprog⟩
  rcases hOrig with
    ⟨_,_,_,_,hF1,_,_,_,_,_,_,_,hparallel⟩
  let d : ℤ := q.1.1
  let e : ℤ := q.1.2
  let u : ℤ := q.2.1
  let v : ℤ := q.2.2
  let t : ℤ := levelT d₀ e₀ r₀ J q
  have hpar := original_signed_level_parameter
    a b d₀ e₀ d e m hbez hlevel
  have hd : d = m * d₀ + b * (r₀ + J * t) := by
    calc
      d = m * d₀ + b * levelR d₀ e₀ q := by
        simpa [d,e,levelR] using hpar.1
      _ = m * d₀ + b * (r₀ + J * t) := by
        rw [hprog]
  have he : e = m * e₀ - a * (r₀ + J * t) := by
    calc
      e = m * e₀ - a * levelR d₀ e₀ q := by
        simpa [d,e,levelR] using hpar.2
      _ = m * e₀ - a * (r₀ + J * t) := by
        rw [hprog]
  have hF1z : e ^ 2 * v = d ^ 2 * u + 1 := by
    simpa only [d,e,u,v,Nat.cast_mul,Nat.cast_pow] using hF1
  have hdet := pure_eval_det P Q a b c d e hpure
  rw [hlevel] at hdet
  have hPQ := original_parallel_pq_values d e u v
    (MvPolynomial.eval ![d,e] P)
    (MvPolynomial.eval ![d,e] Q)
    c m hF1z hparallel hdet
  have hpval :
      MvPolynomial.eval ![d,e] P =
        (A₀ * d + B₀ * e) * e ^ 2 -
          c * m ^ 2 * a ^ 2 * (a * d + 3 * b * e) := by
    have hh := congrArg (MvPolynomial.eval ![d,e]) hPnorm
    simp [MvPolynomial.eval_sub, MvPolynomial.eval_add,
      MvPolynomial.eval_mul, MvPolynomial.eval_pow,
      MvPolynomial.eval_C, MvPolynomial.eval_X] at hh
    rw [hlevel] at hh
    nlinarith only [hh]
  have hqval :
      MvPolynomial.eval ![d,e] Q =
        (A₀ * d + B₀ * e) * d ^ 2 +
          c * m ^ 2 * b ^ 2 * (3 * a * d + b * e) := by
    have hh := congrArg (MvPolynomial.eval ![d,e]) hQnorm
    simp [MvPolynomial.eval_sub, MvPolynomial.eval_add,
      MvPolynomial.eval_mul, MvPolynomial.eval_pow,
      MvPolynomial.eval_C, MvPolynomial.eval_X] at hh
    rw [hlevel] at hh
    nlinarith only [hh]
  have hU : c * m ^ 5 * u =
      (A₀ * d + B₀ * e) * e ^ 2 -
        c * m ^ 2 * a ^ 2 * (a * d + 3 * b * e) := by
    calc
      _ = MvPolynomial.eval ![d,e] P := hPQ.1.symm
      _ = _ := hpval
  have hV : c * m ^ 5 * v =
      (A₀ * d + B₀ * e) * d ^ 2 +
        c * m ^ 2 * b ^ 2 * (3 * a * d + b * e) := by
    calc
      _ = MvPolynomial.eval ![d,e] Q := hPQ.2.symm
      _ = _ := hqval
  constructor
  · exact originalUPoly_eval_of_normal_identity
      a b c m d₀ e₀ r₀ J A₀ B₀ t d e u
      hc hm hd he hU
  · exact originalVPoly_eval_of_normal_identity
      a b c m d₀ e₀ r₀ J A₀ B₀ t d e v
      hc hm hd he hV

end ConsecutiveCountingA5PureCubicRange

open Polynomial
theorem sign_crossing_has_root
    (P : Polynomial ℝ) (x y : ℝ) (hxy : x < y)
    (hx : 0 < Polynomial.eval x P)
    (hy : Polynomial.eval y P < 0) :
    ∃ z : ℝ, x < z ∧ z < y ∧ Polynomial.eval z P = 0 := by
  have hcont : ContinuousOn (fun z : ℝ => Polynomial.eval z P)
      (Set.uIcc x y) := (Polynomial.continuous P).continuousOn
  have hzero : (0 : ℝ) ∈
      Set.uIcc (Polynomial.eval x P) (Polynomial.eval y P) := by
    simp [Set.mem_uIcc, hx.le, hy.le]
  obtain ⟨z, hz, hz0⟩ := (intermediate_value_uIcc hcont) hzero
  have hzy : z ∈ Set.Icc x y := by
    simpa [Set.uIcc_of_le hxy.le] using hz
  rcases hzy with ⟨hxz, hzy⟩
  refine ⟨z, ?_, ?_, hz0⟩
  · exact lt_of_le_of_ne hxz (by
      intro h
      subst z
      linarith)
  · exact lt_of_le_of_ne hzy (by
      intro h
      subst z
      linarith)

theorem rank_strict_of_midpoint
    (R : Finset ℝ) (x y z : ℝ)
    (hxy : x ≤ y) (hz : z ∈ R) (hxz : x < z) (hzy : z ≤ y) :
    (R.filter (fun r => r ≤ x)).card <
      (R.filter (fun r => r ≤ y)).card := by
  apply Finset.card_lt_card
  have hsubset :
      R.filter (fun r => r ≤ x) ⊆ R.filter (fun r => r ≤ y) := by
    intro r hr
    simp only [Finset.mem_filter] at hr ⊢
    exact ⟨hr.1, le_trans hr.2 hxy⟩
  apply (Finset.ssubset_iff_of_subset hsubset).2
  refine ⟨z, ?_, ?_⟩
  · simp [hz, hzy]
  · simp [not_le.mpr hxz]

theorem positive_on_equal_root_rank
    (P : Polynomial ℝ) (R : Finset ℝ) (x y : ℝ)
    (hxy : x < y)
    (hroots : ∀ z : ℝ, Polynomial.eval z P = 0 → z ∈ R)
    (hrank : (R.filter (fun r => r ≤ x)).card =
      (R.filter (fun r => r ≤ y)).card)
    (hx : 0 < Polynomial.eval x P) :
    0 < Polynomial.eval y P := by
  by_contra hnot
  have hy : Polynomial.eval y P ≤ 0 := le_of_not_gt hnot
  by_cases hy0 : Polynomial.eval y P = 0
  · have hs := rank_strict_of_midpoint R x y y hxy.le
      (hroots y hy0) hxy le_rfl
    omega
  · have hyneg : Polynomial.eval y P < 0 :=
      lt_of_le_of_ne hy hy0
    obtain ⟨z, hxz, hzy, hz0⟩ :=
      sign_crossing_has_root P x y hxy hx hyneg
    have hs := rank_strict_of_midpoint R x y z hxy.le
      (hroots z hz0) hxz hzy.le
    omega

theorem polynomial_root_mem_finset
    (P : Polynomial ℝ) (hP : P ≠ 0) (z : ℝ)
    (hz : Polynomial.eval z P = 0) :
    z ∈ P.roots.toFinset := by
  rw [Multiset.mem_toFinset]
  apply (Polynomial.mem_roots hP).2
  exact hz

theorem root_mem_biUnion_of_member
    [DecidableEq ℝ]
    (B : Finset (Polynomial ℝ)) (p : Polynomial ℝ)
    (hp : p ∈ B) (hne : p ≠ 0) (w : ℝ)
    (hw : eval w p = 0) :
    w ∈ B.biUnion (fun f => f.roots.toFinset) := by
  apply Finset.mem_biUnion.mpr
  refine ⟨p, hp, ?_⟩
  rw [Multiset.mem_toFinset]
  exact (Polynomial.mem_roots hne).2 hw

theorem finite_family_root_cover
    (Ps : Finset (Polynomial ℝ))
    (hPs : ∀ P ∈ Ps, P ≠ 0)
    (P : Polynomial ℝ) (hPmem : P ∈ Ps)
    (z : ℝ) (hz : Polynomial.eval z P = 0) :
    z ∈ Ps.biUnion (fun Q => Q.roots.toFinset) := by
  apply Finset.mem_biUnion.mpr
  exact ⟨P, hPmem, polynomial_root_mem_finset P (hPs P hPmem) z hz⟩

theorem positive_on_equal_family_root_rank
    (Ps : Finset (Polynomial ℝ))
    (hPs : ∀ P ∈ Ps, P ≠ 0)
    (P : Polynomial ℝ) (hPmem : P ∈ Ps)
    (x y : ℝ) (hxy : x < y)
    (hrank :
      ((Ps.biUnion (fun Q => Q.roots.toFinset)).filter
        (fun r => r ≤ x)).card =
      ((Ps.biUnion (fun Q => Q.roots.toFinset)).filter
        (fun r => r ≤ y)).card)
    (hx : 0 < Polynomial.eval x P) :
    0 < Polynomial.eval y P := by
  apply positive_on_equal_root_rank P
    (Ps.biUnion (fun Q => Q.roots.toFinset)) x y hxy
    (fun z hz => finite_family_root_cover Ps hPs P hPmem z hz)
    hrank hx

theorem no_root_after_equal_rank
    (R : Finset ℝ) (x y : ℝ) (hxy : x ≤ y)
    (hrank : (R.filter (fun r => r ≤ x)).card =
      (R.filter (fun r => r ≤ y)).card)
    (z : ℝ) (hz : z ∈ R) (hxz : x < z) (hzy : z ≤ y) :
    False := by
  have hs := rank_strict_of_midpoint R x y z hxy hz hxz hzy
  omega

theorem nonneg_on_right_rank_fiber
    (P : Polynomial ℝ) (R : Finset ℝ) (x y z : ℝ)
    (hxy : x < y) (hxz : x < z) (hzy : z ≤ y)
    (hroots : ∀ w : ℝ, Polynomial.eval w P = 0 → w ∈ R)
    (hrank : (R.filter (fun r => r ≤ x)).card =
      (R.filter (fun r => r ≤ y)).card)
    (hy : 0 ≤ Polynomial.eval y P) :
    0 ≤ Polynomial.eval z P := by
  have hyne : Polynomial.eval y P ≠ 0 := by
    intro hzero
    exact no_root_after_equal_rank R x y hxy.le hrank y
      (hroots y hzero) hxy le_rfl
  have hypos : 0 < Polynomial.eval y P :=
    lt_of_le_of_ne hy hyne.symm
  by_cases hzeq : z = y
  · simpa [hzeq] using hy
  have hzylt : z < y := lt_of_le_of_ne hzy hzeq
  by_contra hznot
  have hzneg : Polynomial.eval z P < 0 := lt_of_not_ge hznot
  have hzNeg : 0 < Polynomial.eval z (-P) := by
    simpa using neg_pos.mpr hzneg
  have hyNeg : Polynomial.eval y (-P) < 0 := by
    simp only [Polynomial.eval_neg]
    linarith
  obtain ⟨w, hzw, hwy, hw0⟩ :=
    sign_crossing_has_root (-P) z y hzylt hzNeg hyNeg
  have hw0P : Polynomial.eval w P = 0 := by
    simpa using hw0
  exact no_root_after_equal_rank R x y hxy.le hrank w
    (hroots w hw0P) (lt_trans hxz hzw) hwy.le

theorem root_finset_card_le_natDegree (P : Polynomial ℝ) :
    P.roots.toFinset.card ≤ P.natDegree := by
  exact le_trans (Multiset.toFinset_card_le P.roots) (Polynomial.card_roots' P)

theorem family_root_card_le_degrees
    (Ps : Finset (Polynomial ℝ)) :
    (Ps.biUnion (fun P => P.roots.toFinset)).card ≤
      ∑ P ∈ Ps, P.natDegree := by
  calc
    (Ps.biUnion (fun P => P.roots.toFinset)).card ≤
        ∑ P ∈ Ps, P.roots.toFinset.card :=
      Finset.card_biUnion_le
    _ ≤ ∑ P ∈ Ps, P.natDegree := by
      apply Finset.sum_le_sum
      intro P hP
      exact root_finset_card_le_natDegree P

theorem nonneg_on_equal_rank_interval
    (P : Polynomial ℝ) (R : Finset ℝ) (x y : ℝ)
    (hxy : x < y)
    (hroots : ∀ w : ℝ, Polynomial.eval w P = 0 → w ∈ R)
    (hrank : (R.filter (fun r => r ≤ x)).card =
      (R.filter (fun r => r ≤ y)).card)
    (hx : 0 ≤ Polynomial.eval x P)
    (hy : 0 ≤ Polynomial.eval y P) :
    ∀ z ∈ Set.Icc x y, 0 ≤ Polynomial.eval z P := by
  intro z hz
  rcases hz with ⟨hxz, hzy⟩
  by_cases hzx : z = x
  · simpa [hzx] using hx
  have hxzlt : x < z := lt_of_le_of_ne hxz (Ne.symm hzx)
  exact nonneg_on_right_rank_fiber P R x y z hxy hxzlt hzy
    hroots hrank hy

theorem positive_on_equal_rank_interval
    (P : Polynomial ℝ) (R : Finset ℝ) (x y : ℝ)
    (hxy : x < y)
    (hroots : ∀ w : ℝ, Polynomial.eval w P = 0 → w ∈ R)
    (hrank : (R.filter (fun r => r ≤ x)).card =
      (R.filter (fun r => r ≤ y)).card)
    (hx : 0 < Polynomial.eval x P)
    (hy : 0 < Polynomial.eval y P) :
    ∀ z ∈ Set.Icc x y, 0 < Polynomial.eval z P := by
  intro z hz
  rcases hz with ⟨hxz, hzy⟩
  by_cases hzx : z = x
  · simpa [hzx] using hx
  have hxzlt : x < z := lt_of_le_of_ne hxz (Ne.symm hzx)
  have hnonneg : 0 ≤ Polynomial.eval z P :=
    nonneg_on_right_rank_fiber P R x y z hxy hxzlt hzy
      hroots hrank hy.le
  have hne : Polynomial.eval z P ≠ 0 := by
    intro hz0
    exact no_root_after_equal_rank R x y hxy.le hrank z
      (hroots z hz0) hxzlt hzy
  exact lt_of_le_of_ne hnonneg hne.symm

theorem family_root_rank_le_degrees
    (Ps : Finset (Polynomial ℝ)) (x : ℝ) :
    ((Ps.biUnion (fun P => P.roots.toFinset)).filter
      (fun r => r ≤ x)).card ≤ ∑ P ∈ Ps, P.natDegree := by
  exact le_trans (Finset.card_filter_le
    (Ps.biUnion (fun P => P.roots.toFinset)) (fun r => r ≤ x))
    (family_root_card_le_degrees Ps)

namespace ConsecutiveCountingA5PureCubicRange
open Polynomial

theorem originalBoundary_nonzero
    (x D E M ρ₀ C₀ : ℝ)
    (a b c m d₀ e₀ r₀ J A₀ B₀ : ℤ)
    (g η : ℝ) (p : Polynomial ℝ)
    (hp : p ∈ originalBoundaryCandidatesWithCurvature
      x D E M ρ₀ C₀ a b c m d₀ e₀ r₀ J A₀ B₀ g η) :
    p ≠ 0 := by
  classical
  unfold originalBoundaryCandidatesWithCurvature at hp
  simp only [Finset.mem_filter] at hp
  exact hp.2

end ConsecutiveCountingA5PureCubicRange

namespace ConsecutiveCountingA5PureCubicRange
open Polynomial

theorem actual_original_point_eval_D_E_N
    (a b c m d₀ e₀ r₀ J A₀ B₀ : ℤ)
    (hbez : a * d₀ + b * e₀ = 1)
    (q : (ℕ × ℕ) × (ℕ × ℕ))
    (hlevel : a * (q.1.1 : ℤ) + b * (q.1.2 : ℤ) = m)
    (hprog : levelR d₀ e₀ q =
      r₀ + J * levelT d₀ e₀ r₀ J q)
    (hU :
      eval ((levelT d₀ e₀ r₀ J q : ℤ) : ℝ)
        (originalUPoly a b c m d₀ e₀ r₀ J A₀ B₀) =
          (q.2.1 : ℝ)) :
    eval ((levelT d₀ e₀ r₀ J q : ℤ) : ℝ)
        (originalDPoly b m d₀ r₀ J) = (q.1.1 : ℝ) ∧
      eval ((levelT d₀ e₀ r₀ J q : ℤ) : ℝ)
        (originalEPoly a m e₀ r₀ J) = (q.1.2 : ℝ) ∧
      eval ((levelT d₀ e₀ r₀ J q : ℤ) : ℝ)
        (originalNPoly a b c m d₀ e₀ r₀ J A₀ B₀) =
          ((q.1.1 ^ 2 * q.2.1 : ℕ) : ℝ) := by
  let t : ℤ := levelT d₀ e₀ r₀ J q
  have hpar := original_signed_level_parameter
    a b d₀ e₀ (q.1.1 : ℤ) (q.1.2 : ℤ) m hbez hlevel
  have hd :
      (q.1.1 : ℤ) = m * d₀ + b * (r₀ + J * t) := by
    calc
      (q.1.1 : ℤ) = m * d₀ + b * levelR d₀ e₀ q := by
        simpa [levelR] using hpar.1
      _ = m * d₀ + b * (r₀ + J * t) := by
        rw [hprog]
  have he :
      (q.1.2 : ℤ) = m * e₀ - a * (r₀ + J * t) := by
    calc
      (q.1.2 : ℤ) = m * e₀ - a * levelR d₀ e₀ q := by
        simpa [levelR] using hpar.2
      _ = m * e₀ - a * (r₀ + J * t) := by
        rw [hprog]
  have hD :
      eval (t : ℝ) (originalDPoly b m d₀ r₀ J) =
        (q.1.1 : ℝ) := by
    rw [originalDPoly_eval]
    exact_mod_cast hd.symm
  have hE :
      eval (t : ℝ) (originalEPoly a m e₀ r₀ J) =
        (q.1.2 : ℝ) := by
    rw [originalEPoly_eval]
    exact_mod_cast he.symm
  refine ⟨?_, ?_, ?_⟩
  · exact hD
  · exact hE
  · change
      eval (t : ℝ)
        ((originalDPoly b m d₀ r₀ J) ^ 2 *
          originalUPoly a b c m d₀ e₀ r₀ J A₀ B₀) =
        ((q.1.1 ^ 2 * q.2.1 : ℕ) : ℝ)
    rw [eval_mul, eval_pow, hD]
    rw [show eval (t : ℝ)
      (originalUPoly a b c m d₀ e₀ r₀ J A₀ B₀) =
        (q.2.1 : ℝ) from hU]
    norm_cast

end ConsecutiveCountingA5PureCubicRange

namespace ConsecutiveCountingA5PureCubicRange
open Polynomial

def originalAcceptedPolyAt
    (x D E M ρ₀ C₀ : ℝ)
    (a b c m d₀ e₀ r₀ J A₀ B₀ : ℤ) (z : ℝ) : Prop :=
  let d := originalDPoly b m d₀ r₀ J
  let e := originalEPoly a m e₀ r₀ J
  let u := originalUPoly a b c m d₀ e₀ r₀ J A₀ B₀
  let v := originalVPoly a b c m d₀ e₀ r₀ J A₀ B₀
  let n := originalNPoly a b c m d₀ e₀ r₀ J A₀ B₀
  0 ≤ eval z (d - C 1) ∧
  0 ≤ eval z (e - C 1) ∧
  0 ≤ eval z (u - C 1) ∧
  0 ≤ eval z (v - C 1) ∧
  0 < eval z (d - C (D / 2)) ∧
  0 ≤ eval z (C D - d) ∧
  0 < eval z (e - C (E / 2)) ∧
  0 ≤ eval z (C E - e) ∧
  0 < eval z (d - C ρ₀ * e) ∧
  0 ≤ eval z (C (ρ₀ + C₀ * D / (E * M)) * e - d) ∧
  0 ≤ eval z (C x - n)

theorem actual_original_point_endpoint_accepted
    (x D E M ρ₀ C₀ : ℝ)
    (P Q : MvPolynomial (Fin 2) ℤ)
    (a b c m d₀ e₀ r₀ J A₀ B₀ : ℤ)
    (hc : c ≠ 0) (hm : m ≠ 0)
    (hbez : a * d₀ + b * e₀ = 1)
    (hpure : MvPolynomial.X (1 : Fin 2) ^ 2 * Q -
      MvPolynomial.X (0 : Fin 2) ^ 2 * P =
      MvPolynomial.C c *
        (MvPolynomial.C a * MvPolynomial.X 0 +
          MvPolynomial.C b * MvPolynomial.X 1) ^ 5)
    (hPnorm : P =
      (MvPolynomial.C A₀ * MvPolynomial.X (0 : Fin 2) +
        MvPolynomial.C B₀ * MvPolynomial.X (1 : Fin 2)) *
          MvPolynomial.X (1 : Fin 2) ^ 2 -
        MvPolynomial.C c *
          (MvPolynomial.C a * MvPolynomial.X (0 : Fin 2) +
            MvPolynomial.C b * MvPolynomial.X (1 : Fin 2)) ^ 2 *
          MvPolynomial.C (a ^ 2) *
          (MvPolynomial.C a * MvPolynomial.X (0 : Fin 2) +
            MvPolynomial.C (3 * b) * MvPolynomial.X (1 : Fin 2)))
    (hQnorm : Q =
      (MvPolynomial.C A₀ * MvPolynomial.X (0 : Fin 2) +
        MvPolynomial.C B₀ * MvPolynomial.X (1 : Fin 2)) *
          MvPolynomial.X (0 : Fin 2) ^ 2 +
        MvPolynomial.C c *
          (MvPolynomial.C a * MvPolynomial.X (0 : Fin 2) +
            MvPolynomial.C b * MvPolynomial.X (1 : Fin 2)) ^ 2 *
          MvPolynomial.C (b ^ 2) *
          (MvPolynomial.C (3 * a) * MvPolynomial.X (0 : Fin 2) +
            MvPolynomial.C b * MvPolynomial.X (1 : Fin 2)))
    (q : (ℕ × ℕ) × (ℕ × ℕ))
    (hq : q ∈ FixedProgressionS x D E M ρ₀ C₀
      P Q a b m d₀ e₀ r₀ J) :
    originalAcceptedPolyAt x D E M ρ₀ C₀
      a b c m d₀ e₀ r₀ J A₀ B₀
      ((levelT d₀ e₀ r₀ J q : ℤ) : ℝ) := by
  have hUV := actual_original_point_eval_UV
    x D E M ρ₀ C₀ P Q a b c m d₀ e₀ r₀ J A₀ B₀
    hc hm hbez hpure hPnorm hQnorm q hq
  rcases hq with ⟨hOrig,hlevel,hprog⟩
  have hDEN := actual_original_point_eval_D_E_N
    a b c m d₀ e₀ r₀ J A₀ B₀ hbez q hlevel hprog hUV.1
  rcases hDEN with ⟨hD,hE,hN⟩
  rcases hOrig with
    ⟨hd1,he1,hu1,hv1,_,hx,hdLo,hdHi,heLo,heHi,
      hrLo,hrHi,_⟩
  have hepos : 0 < (q.1.2 : ℝ) := by
    exact_mod_cast (show 0 < q.1.2 by omega)
  have hrLo' : ρ₀ * (q.1.2 : ℝ) < (q.1.1 : ℝ) :=
    (lt_div_iff₀ hepos).mp hrLo
  have hrHi' :
      (q.1.1 : ℝ) ≤
        (ρ₀ + C₀ * D / (E * M)) * (q.1.2 : ℝ) :=
    (div_le_iff₀ hepos).mp hrHi
  have hd1R : (1 : ℝ) ≤ q.1.1 := by exact_mod_cast hd1
  have he1R : (1 : ℝ) ≤ q.1.2 := by exact_mod_cast he1
  have hu1R : (1 : ℝ) ≤ q.2.1 := by exact_mod_cast hu1
  have hv1R : (1 : ℝ) ≤ q.2.2 := by exact_mod_cast hv1
  dsimp [originalAcceptedPolyAt]
  simp only [eval_sub, eval_mul, eval_C,
    hD, hE, hUV.1, hUV.2, hN]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · linarith only [hd1R]
  · linarith only [he1R]
  · linarith only [hu1R]
  · linarith only [hv1R]
  · linarith only [hdLo]
  · linarith only [hdHi]
  · linarith only [heLo]
  · linarith only [heHi]
  · linarith only [hrLo']
  · linarith only [hrHi']
  · linarith only [hx]

end ConsecutiveCountingA5PureCubicRange

namespace ConsecutiveCountingA5PureCubicRange
open Polynomial

theorem boundary_nonneg_on_rank
    (L : List (Polynomial ℝ)) (B : Finset (Polynomial ℝ))
    (R : Finset ℝ) (s t : ℝ) (hst : s < t)
    (hmember : ∀ p : Polynomial ℝ, p ∈ L → p ≠ 0 → p ∈ B)
    (hroot : ∀ p : Polynomial ℝ, p ∈ B → p ≠ 0 →
      ∀ w : ℝ, eval w p = 0 → w ∈ R)
    (hrank : (R.filter (fun r => r ≤ s)).card =
      (R.filter (fun r => r ≤ t)).card)
    (p : Polynomial ℝ) (hp : p ∈ L)
    (hsp : 0 ≤ eval s p) (htp : 0 ≤ eval t p) :
    ∀ z ∈ Set.Icc s t, 0 ≤ eval z p := by
  by_cases hz : p = 0
  · intro z hz'
    simpa [hz]
  exact nonneg_on_equal_rank_interval p R s t hst
    (hroot p (hmember p hp hz) hz) hrank hsp htp

theorem boundary_positive_on_rank
    (L : List (Polynomial ℝ)) (B : Finset (Polynomial ℝ))
    (R : Finset ℝ) (s t : ℝ) (hst : s < t)
    (hmember : ∀ p : Polynomial ℝ, p ∈ L → p ≠ 0 → p ∈ B)
    (hroot : ∀ p : Polynomial ℝ, p ∈ B → p ≠ 0 →
      ∀ w : ℝ, eval w p = 0 → w ∈ R)
    (hrank : (R.filter (fun r => r ≤ s)).card =
      (R.filter (fun r => r ≤ t)).card)
    (p : Polynomial ℝ) (hp : p ∈ L)
    (hsp : 0 < eval s p) (htp : 0 < eval t p) :
    ∀ z ∈ Set.Icc s t, 0 < eval z p := by
  have hne : p ≠ 0 := by
    intro hz
    simp [hz] at hsp
  exact positive_on_equal_rank_interval p R s t hst
    (hroot p (hmember p hp hne) hne) hrank hsp htp

set_option maxHeartbeats 1000000 in
theorem actual_accepted_on_closed_rank_interval
    (x D E M ρ₀ C₀ : ℝ)
    (a b c m d₀ e₀ r₀ J A₀ B₀ : ℤ) (g η s t : ℝ)
    (hst : s < t)
    (hrank :
      (((originalBoundaryCandidatesWithCurvature
        x D E M ρ₀ C₀ a b c m d₀ e₀ r₀ J A₀ B₀ g η).biUnion
          (fun f => f.roots.toFinset)).filter (fun r => r ≤ s)).card =
      (((originalBoundaryCandidatesWithCurvature
        x D E M ρ₀ C₀ a b c m d₀ e₀ r₀ J A₀ B₀ g η).biUnion
          (fun f => f.roots.toFinset)).filter (fun r => r ≤ t)).card)
    (hs : originalAcceptedPolyAt x D E M ρ₀ C₀
      a b c m d₀ e₀ r₀ J A₀ B₀ s)
    (ht : originalAcceptedPolyAt x D E M ρ₀ C₀
      a b c m d₀ e₀ r₀ J A₀ B₀ t) :
    ∀ z ∈ Set.Icc s t,
      originalAcceptedPolyAt x D E M ρ₀ C₀
        a b c m d₀ e₀ r₀ J A₀ B₀ z := by
  classical
  let L := originalBoundaryRawList x D E M ρ₀ C₀
    a b c m d₀ e₀ r₀ J A₀ B₀ g η
  generalize hB : originalBoundaryCandidatesWithCurvature
    x D E M ρ₀ C₀ a b c m d₀ e₀ r₀ J A₀ B₀ g η = B at hrank
  let R := B.biUnion (fun f => f.roots.toFinset)
  change (R.filter (fun r => r ≤ s)).card =
    (R.filter (fun r => r ≤ t)).card at hrank
  have hmember (p : Polynomial ℝ) (hp : p ∈ L)
      (hne : p ≠ 0) : p ∈ B := by
    rw [← hB]
    change p ∈
      (insert
        (derivative (derivative
          (originalNPoly a b c m d₀ e₀ r₀ J A₀ B₀)))
        ((originalBoundaryRawList x D E M ρ₀ C₀
          a b c m d₀ e₀ r₀ J A₀ B₀ g η).toFinset.filter
            (· ≠ 0))).filter (· ≠ 0)
    simp only [Finset.mem_filter, Finset.mem_insert,
      List.mem_toFinset]
    exact ⟨Or.inr ⟨hp,hne⟩,hne⟩
  have hroot (p : Polynomial ℝ) (hp : p ∈ B)
      (hne : p ≠ 0) (w : ℝ) (hw : eval w p = 0) :
      w ∈ R := by
    change w ∈ B.biUnion (fun f => f.roots.toFinset)
    exact root_mem_biUnion_of_member B p hp hne w hw
  have hweak (p : Polynomial ℝ) (hp : p ∈ L)
      (hsp : 0 ≤ eval s p) (htp : 0 ≤ eval t p) :
      ∀ z ∈ Set.Icc s t, 0 ≤ eval z p :=
    boundary_nonneg_on_rank L B R s t hst
      hmember hroot hrank p hp hsp htp
  have hstrict (p : Polynomial ℝ) (hp : p ∈ L)
      (hsp : 0 < eval s p) (htp : 0 < eval t p) :
      ∀ z ∈ Set.Icc s t, 0 < eval z p :=
    boundary_positive_on_rank L B R s t hst
      hmember hroot hrank p hp hsp htp
  dsimp [originalAcceptedPolyAt] at hs ht ⊢
  rcases hs with
    ⟨hs1,hs2,hs3,hs4,hs5,hs6,hs7,hs8,hs9,hs10,hs11⟩
  rcases ht with
    ⟨ht1,ht2,ht3,ht4,ht5,ht6,ht7,ht8,ht9,ht10,ht11⟩
  intro z hz
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hweak _ (by simp [L,originalBoundaryRawList])
      hs1 ht1 z hz
  · exact hweak _ (by simp [L,originalBoundaryRawList])
      hs2 ht2 z hz
  · exact hweak _ (by simp [L,originalBoundaryRawList])
      hs3 ht3 z hz
  · exact hweak _ (by simp [L,originalBoundaryRawList])
      hs4 ht4 z hz
  · exact hstrict _ (by simp [L,originalBoundaryRawList])
      hs5 ht5 z hz
  · exact hweak _ (by simp [L,originalBoundaryRawList])
      hs6 ht6 z hz
  · exact hstrict _ (by simp [L,originalBoundaryRawList])
      hs7 ht7 z hz
  · exact hweak _ (by simp [L,originalBoundaryRawList])
      hs8 ht8 z hz
  · exact hstrict _ (by simp [L,originalBoundaryRawList])
      hs9 ht9 z hz
  · exact hweak _ (by simp [L,originalBoundaryRawList])
      hs10 ht10 z hz
  · exact hweak _ (by
      simp [L,originalBoundaryRawList,originalNPoly])
      hs11 ht11 z hz

end ConsecutiveCountingA5PureCubicRange

namespace ConsecutiveCountingA5PureCubicRange

theorem finite_colored_integer_diameter_count_generic
    (ι : Type*) [Fintype ι] [DecidableEq ι]
    (T : Finset ℤ) (color : ℤ → ι)
    (A : ℝ) (hA : 0 ≤ A)
    (hpair : ∀ s ∈ T, ∀ t ∈ T, color s = color t →
      s ≤ t → ((t - s : ℤ) : ℝ) ≤ A) :
    T.card ≤ Fintype.card ι * (2 * Nat.ceil A + 1) := by
  classical
  let F : ι → Finset ℤ :=
    fun i => T.filter (fun t => color t = i)
  have hcover : T = Finset.univ.biUnion F := by
    ext t
    constructor
    · intro ht
      apply Finset.mem_biUnion.mpr
      exact ⟨color t, Finset.mem_univ _, by
        exact Finset.mem_filter.mpr ⟨ht,rfl⟩⟩
    · intro ht
      obtain ⟨i,_,hti⟩ := Finset.mem_biUnion.mp ht
      exact (Finset.mem_filter.mp hti).1
  have hfiber : ∀ i : ι,
      (F i).card ≤ 2 * Nat.ceil A + 1 := by
    intro i
    apply integer_pair_diameter_card (F i) A hA
    intro s hs t ht hst
    have hs' := Finset.mem_filter.mp hs
    have ht' := Finset.mem_filter.mp ht
    exact hpair s hs'.1 t ht'.1 (hs'.2.trans ht'.2.symm) hst
  calc
    T.card = (Finset.univ.biUnion F).card := by rw [hcover]
    _ ≤ ∑ i ∈ (Finset.univ : Finset ι), (F i).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ i ∈ (Finset.univ : Finset ι),
        (2 * Nat.ceil A + 1) := by
          apply Finset.sum_le_sum
          intro i hi
          exact hfiber i
    _ = Fintype.card ι * (2 * Nat.ceil A + 1) := by simp

theorem finite_colored_integer_diameter_count
    (T : Finset ℤ) (color : ℤ → Fin 636)
    (A : ℝ) (hA : 0 ≤ A)
    (hpair : ∀ s ∈ T, ∀ t ∈ T, color s = color t →
      s ≤ t → ((t - s : ℤ) : ℝ) ≤ A) :
    T.card ≤ 636 * (2 * Nat.ceil A + 1) := by
  simpa using finite_colored_integer_diameter_count_generic
    (Fin 636) T color A hA hpair

end ConsecutiveCountingA5PureCubicRange

namespace ConsecutiveCountingA5PureCubicRange
open Polynomial

theorem boundary_list_card_le_length
    (L : List (Polynomial ℝ)) :
    L.toFinset.card ≤ L.length := by
  classical
  induction L with
  | nil => simp
  | cons p L ih =>
      have hinsert :
          (insert p L.toFinset).card ≤ L.toFinset.card + 1 := by
        by_cases hp : p ∈ L.toFinset
        · simp [hp]
        · simp [hp]
      simpa only [List.toFinset_cons, List.length_cons]
        using le_trans hinsert (Nat.add_le_add_right ih 1)

theorem actual_boundary_family_card_le_21
    (x D E M ρ₀ C₀ : ℝ)
    (a b c m d₀ e₀ r₀ J A₀ B₀ : ℤ)
    (g η : ℝ) :
    (originalBoundaryCandidatesWithCurvature
      x D E M ρ₀ C₀
      a b c m d₀ e₀ r₀ J A₀ B₀ g η).card ≤ 21 := by
  classical
  let L := originalBoundaryRawList
    x D E M ρ₀ C₀ a b c m d₀ e₀ r₀ J A₀ B₀ g η
  let n := originalNPoly a b c m d₀ e₀ r₀ J A₀ B₀
  have hlen : L.length = 20 := by
    dsimp [L, originalBoundaryRawList]
  have hbase :
      (L.toFinset.filter (· ≠ 0)).card ≤ 20 :=
    le_trans (Finset.card_filter_le _ _)
      (by simpa [hlen] using boundary_list_card_le_length L)
  have hinsert :
      (insert (derivative (derivative n))
        (L.toFinset.filter (· ≠ 0))).card ≤
          (L.toFinset.filter (· ≠ 0)).card + 1 := by
    by_cases hp : derivative (derivative n) ∈
        L.toFinset.filter (· ≠ 0)
    · simp [hp]
    · simp [hp]
  change
    ((insert (derivative (derivative n))
      (L.toFinset.filter (· ≠ 0))).filter (· ≠ 0)).card ≤ 21
  exact le_trans (Finset.card_filter_le _ _)
    (le_trans hinsert (by omega))

end ConsecutiveCountingA5PureCubicRange

namespace ConsecutiveCountingA5PureCubicRange
open Polynomial

set_option maxHeartbeats 1000000 in
theorem actual_second_derivative_sign_on_rank_interval
    (x D E M ρ₀ C₀ : ℝ)
    (a b c m d₀ e₀ r₀ J A₀ B₀ : ℤ)
    (g η s t : ℝ) (hst : s < t)
    (hrank :
      (((originalBoundaryCandidatesWithCurvature
        x D E M ρ₀ C₀ a b c m d₀ e₀ r₀ J A₀ B₀ g η).biUnion
          (fun f => f.roots.toFinset)).filter (fun r => r ≤ s)).card =
      (((originalBoundaryCandidatesWithCurvature
        x D E M ρ₀ C₀ a b c m d₀ e₀ r₀ J A₀ B₀ g η).biUnion
          (fun f => f.roots.toFinset)).filter (fun r => r ≤ t)).card) :
    (∀ z ∈ Set.Icc s t,
      0 ≤ eval z
        ((originalNPoly a b c m d₀ e₀ r₀ J A₀ B₀).derivative.derivative)) ∨
    (∀ z ∈ Set.Icc s t,
      eval z
        ((originalNPoly a b c m d₀ e₀ r₀ J A₀ B₀).derivative.derivative) ≤ 0) := by
  classical
  let p : Polynomial ℝ :=
    (originalNPoly a b c m d₀ e₀ r₀ J A₀ B₀).derivative.derivative
  generalize hB : originalBoundaryCandidatesWithCurvature
    x D E M ρ₀ C₀ a b c m d₀ e₀ r₀ J A₀ B₀ g η = B at hrank
  let R := B.biUnion (fun f => f.roots.toFinset)
  change (R.filter (fun r => r ≤ s)).card =
    (R.filter (fun r => r ≤ t)).card at hrank
  by_cases hpzero : p = 0
  · left
    intro z hz
    change 0 ≤ eval z p
    simpa [hpzero]
  have hpB : p ∈ B := by
    rw [← hB]
    change p ∈
      (insert p
        ((originalBoundaryRawList x D E M ρ₀ C₀
          a b c m d₀ e₀ r₀ J A₀ B₀ g η).toFinset.filter
            (· ≠ 0))).filter (· ≠ 0)
    simp [hpzero]
  have hroot : ∀ w : ℝ, eval w p = 0 → w ∈ R := by
    intro w hw
    change w ∈ B.biUnion (fun f => f.roots.toFinset)
    exact root_mem_biUnion_of_member B p hpB hpzero w hw
  have htne : eval t p ≠ 0 := by
    intro hz
    exact no_root_after_equal_rank R s t hst.le hrank t
      (hroot t hz) hst le_rfl
  by_cases htpos : 0 < eval t p
  · have hsnonneg : 0 ≤ eval s p := by
      by_contra hh
      have hsneg : eval s p < 0 := lt_of_not_ge hh
      have hsNegPos : 0 < eval s (-p) := by
        simpa only [eval_neg] using neg_pos.mpr hsneg
      have htNegNeg : eval t (-p) < 0 := by
        simp only [eval_neg]
        linarith
      obtain ⟨w,hsw,hwt,hw0⟩ :=
        sign_crossing_has_root (-p) s t hst hsNegPos htNegNeg
      have hw0P : eval w p = 0 := by
        simpa only [eval_neg, neg_eq_zero] using hw0
      exact no_root_after_equal_rank R s t hst.le hrank w
        (hroot w hw0P) hsw hwt.le
    left
    exact nonneg_on_equal_rank_interval p R s t hst
      hroot hrank hsnonneg htpos.le
  · have htneg : eval t p < 0 :=
      lt_of_le_of_ne (le_of_not_gt htpos) htne
    have hsnonpos : eval s p ≤ 0 := by
      by_contra hh
      have hspos : 0 < eval s p := lt_of_not_ge hh
      obtain ⟨w,hsw,hwt,hw0⟩ :=
        sign_crossing_has_root p s t hst hspos htneg
      exact no_root_after_equal_rank R s t hst.le hrank w
        (hroot w hw0) hsw hwt.le
    have hrootNeg : ∀ w : ℝ, eval w (-p) = 0 → w ∈ R := by
      intro w hw
      apply hroot w
      simpa only [eval_neg, neg_eq_zero] using hw
    have hsNonnegNeg : 0 ≤ eval s (-p) := by
      simp only [eval_neg]
      linarith
    have htNonnegNeg : 0 ≤ eval t (-p) := by
      simp only [eval_neg]
      linarith
    right
    intro z hz
    have hh := nonneg_on_equal_rank_interval (-p) R s t hst
      hrootNeg hrank hsNonnegNeg htNonnegNeg z hz
    simp only [eval_neg] at hh
    linarith

end ConsecutiveCountingA5PureCubicRange

namespace ConsecutiveCountingA5PureCubicRange
open Polynomial

theorem a5deg_add (F G : Polynomial ℝ) (n : ℕ)
    (hF : F.natDegree ≤ n) (hG : G.natDegree ≤ n) :
    (F + G).natDegree ≤ n :=
  (Polynomial.natDegree_add_le F G).trans (max_le hF hG)

theorem a5deg_sub (F G : Polynomial ℝ) (n : ℕ)
    (hF : F.natDegree ≤ n) (hG : G.natDegree ≤ n) :
    (F - G).natDegree ≤ n :=
  (Polynomial.natDegree_sub_le F G).trans (max_le hF hG)

theorem a5deg_mul (F G : Polynomial ℝ) (n k : ℕ)
    (hF : F.natDegree ≤ n) (hG : G.natDegree ≤ k) :
    (F * G).natDegree ≤ n + k :=
  Polynomial.natDegree_mul_le.trans (Nat.add_le_add hF hG)

theorem a5deg_const (r : ℝ) (n : ℕ) :
    (C r).natDegree ≤ n := by
  simp

theorem a5deg_originalD
    (b m d₀ r₀ J : ℤ) :
    (originalDPoly b m d₀ r₀ J).natDegree ≤ 1 := by
  unfold originalDPoly
  exact a5deg_add _ _ 1
    (a5deg_const _ 1)
    (a5deg_mul _ _ 0 1
      (a5deg_const _ 0) (by simp))

theorem a5deg_originalE
    (a m e₀ r₀ J : ℤ) :
    (originalEPoly a m e₀ r₀ J).natDegree ≤ 1 := by
  unfold originalEPoly
  exact a5deg_sub _ _ 1
    (a5deg_const _ 1)
    (a5deg_mul _ _ 0 1
      (a5deg_const _ 0) (by simp))

theorem a5deg_cmul (r : ℝ) (F : Polynomial ℝ)
    (n : ℕ) (hF : F.natDegree ≤ n) :
    (C r * F).natDegree ≤ n := by
  simpa using a5deg_mul (C r) F 0 n (by simp) hF

theorem a5deg_mulc (F : Polynomial ℝ) (r : ℝ)
    (n : ℕ) (hF : F.natDegree ≤ n) :
    (F * C r).natDegree ≤ n := by
  simpa using a5deg_mul F (C r) n 0 hF (by simp)

theorem a5deg_affine_power (F : Polynomial ℝ)
    (hF : F.natDegree ≤ 1) :
    ∀ n : ℕ, (F ^ n).natDegree ≤ n := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ]
      exact a5deg_mul _ _ n 1 ih hF

theorem actual_boundary_raw_degree_le_five
    (x D E M ρ₀ C₀ : ℝ)
    (a b c m d₀ e₀ r₀ J A₀ B₀ : ℤ)
    (g η : ℝ) :
    ∀ p ∈ originalBoundaryRawList
      x D E M ρ₀ C₀ a b c m d₀ e₀ r₀ J A₀ B₀ g η,
      p.natDegree ≤ 5 := by
  classical
  let d := originalDPoly b m d₀ r₀ J
  let e := originalEPoly a m e₀ r₀ J
  let q := originalQPoly a b c m d₀ e₀ r₀ J A₀ B₀
  let u := originalUPoly a b c m d₀ e₀ r₀ J A₀ B₀
  let v := originalVPoly a b c m d₀ e₀ r₀ J A₀ B₀
  let k := originalKPoly a b c m d₀ e₀ r₀ J A₀ B₀ g
  let n := originalNPoly a b c m d₀ e₀ r₀ J A₀ B₀
  let h : ℝ := C₀ * D / (E * M)
  have hd : d.natDegree ≤ 1 :=
    a5deg_originalD b m d₀ r₀ J
  have he : e.natDegree ≤ 1 :=
    a5deg_originalE a m e₀ r₀ J
  have hlin (r s : ℝ) :
      (C r * d + C s * e).natDegree ≤ 1 :=
    a5deg_add _ _ 1 (a5deg_cmul r d 1 hd)
      (a5deg_cmul s e 1 he)
  have hq : q.natDegree ≤ 1 := by
    dsimp [q,originalQPoly]
    exact a5deg_mulc _ _ 1 (hlin (A₀ : ℝ) (B₀ : ℝ))
  have hu : u.natDegree ≤ 3 := by
    dsimp [u,originalUPoly]
    exact a5deg_mulc _ _ 3
      (a5deg_sub _ _ 3
        (a5deg_mul q (e ^ 2) 1 2 hq
          (a5deg_affine_power e he 2))
        (le_trans
          (a5deg_cmul _ _ 1
            (hlin (a : ℝ) ((3 * b : ℤ) : ℝ)))
          (by omega)))
  have hv : v.natDegree ≤ 3 := by
    dsimp [v,originalVPoly]
    exact a5deg_mulc _ _ 3
      (a5deg_add _ _ 3
        (a5deg_mul q (d ^ 2) 1 2 hq
          (a5deg_affine_power d hd 2))
        (le_trans
          (a5deg_cmul _ _ 1
            (hlin ((3 * a : ℤ) : ℝ) (b : ℝ)))
          (by omega)))
  have hpi :
      (originalPiPoly a b m d₀ e₀ r₀ J).natDegree ≤ 2 := by
    dsimp [originalPiPoly]
    exact a5deg_mul d e 1 1 hd he
  have hs :
      (originalSPoly a b m d₀ e₀ r₀ J).natDegree ≤ 1 := by
    dsimp [originalSPoly]
    exact a5deg_sub _ _ 1
      (a5deg_cmul (b : ℝ) e 1 he)
      (a5deg_cmul (a : ℝ) d 1 hd)
  have hk : k.natDegree ≤ 2 := by
    change
      (C (originalQr a b c m A₀ B₀) *
          originalPiPoly a b m d₀ e₀ r₀ J +
        C (2 : ℝ) * q *
          originalSPoly a b m d₀ e₀ r₀ J -
        C (6 * g ^ 2)).natDegree ≤ 2
    exact a5deg_sub _ _ 2
      (a5deg_add _ _ 2
        (a5deg_cmul _ _ 2 hpi)
        (a5deg_mul _ _ 1 1
          (a5deg_cmul (2 : ℝ) q 1 hq) hs))
      (a5deg_const _ 2)
  have hn : n.natDegree ≤ 5 := by
    dsimp [n,originalNPoly]
    exact a5deg_mul _ _ 2 3
      (a5deg_affine_power d hd 2) hu
  let L := originalBoundaryRawList
    x D E M ρ₀ C₀ a b c m d₀ e₀ r₀ J A₀ B₀ g η
  have h1 : d.natDegree ≤ 5 := hd.trans (by omega)
  have h2 : e.natDegree ≤ 5 := he.trans (by omega)
  have h3 : (d - C 1).natDegree ≤ 5 :=
    (a5deg_sub _ _ 1 hd (by simp)).trans (by omega)
  have h4 : (e - C 1).natDegree ≤ 5 :=
    (a5deg_sub _ _ 1 he (by simp)).trans (by omega)
  have h5 : (d - C (D / 2)).natDegree ≤ 5 :=
    (a5deg_sub _ _ 1 hd (by simp)).trans (by omega)
  have h6 : (C D - d).natDegree ≤ 5 :=
    (a5deg_sub _ _ 1 (by simp) hd).trans (by omega)
  have h7 : (e - C (E / 2)).natDegree ≤ 5 :=
    (a5deg_sub _ _ 1 he (by simp)).trans (by omega)
  have h8 : (C E - e).natDegree ≤ 5 :=
    (a5deg_sub _ _ 1 (by simp) he).trans (by omega)
  have h9 : (d - C ρ₀ * e).natDegree ≤ 5 :=
    (a5deg_sub _ _ 1 hd
      (a5deg_cmul ρ₀ e 1 he)).trans (by omega)
  have h10 : (C (ρ₀ + h) * e - d).natDegree ≤ 5 :=
    (a5deg_sub _ _ 1
      (a5deg_cmul (ρ₀ + h) e 1 he) hd).trans (by omega)
  have h11 : (u - C 1).natDegree ≤ 5 :=
    (a5deg_sub _ _ 3 hu (by simp)).trans (by omega)
  have h12 : (v - C 1).natDegree ≤ 5 :=
    (a5deg_sub _ _ 3 hv (by simp)).trans (by omega)
  have h13 : (C x - d ^ 2 * u).natDegree ≤ 5 :=
    a5deg_sub _ _ 5 (by simp)
      (a5deg_mul _ _ 2 3
        (a5deg_affine_power d hd 2) hu)
  have h14 : q.natDegree ≤ 5 := hq.trans (by omega)
  have h15 : (q - C 1).natDegree ≤ 5 :=
    (a5deg_sub _ _ 1 hq (by simp)).trans (by omega)
  have hnegq : (-q).natDegree ≤ 1 := by simpa using hq
  have h16 : (-q - C 1).natDegree ≤ 5 :=
    (a5deg_sub _ _ 1 hnegq (by simp)).trans (by omega)
  let threshold : ℝ := η * g ^ 2
  have h17 : (k - C threshold).natDegree ≤ 5 :=
    (a5deg_sub _ _ 2 hk (by simp)).trans (by omega)
  have hnegk : (-k).natDegree ≤ 2 := by simpa using hk
  have h18 : (-k - C threshold).natDegree ≤ 5 :=
    (a5deg_sub _ _ 2 hnegk (by simp)).trans (by omega)
  have h19 : (C threshold - k).natDegree ≤ 5 :=
    (a5deg_sub _ _ 2 (by simp) hk).trans (by omega)
  have h20 : (C threshold + k).natDegree ≤ 5 :=
    (a5deg_add _ _ 2 (by simp) hk).trans (by omega)
  intro p hp
  change p ∈
    [d, e, d - C 1, e - C 1,
      d - C (D / 2), C D - d,
      e - C (E / 2), C E - e,
      d - C ρ₀ * e, C (ρ₀ + h) * e - d,
      u - C 1, v - C 1,
      C x - d ^ 2 * u, q, q - C 1, -q - C 1,
      k - C (η * g ^ 2), -k - C (η * g ^ 2),
      C (η * g ^ 2) - k, C (η * g ^ 2) + k] at hp
  simp only [List.mem_cons, List.mem_singleton] at hp
  rcases hp with rfl | hp
  · exact h1
  rcases hp with rfl | hp
  · exact h2
  rcases hp with rfl | hp
  · exact h3
  rcases hp with rfl | hp
  · exact h4
  rcases hp with rfl | hp
  · exact h5
  rcases hp with rfl | hp
  · exact h6
  rcases hp with rfl | hp
  · exact h7
  rcases hp with rfl | hp
  · exact h8
  rcases hp with rfl | hp
  · exact h9
  rcases hp with rfl | hp
  · exact h10
  rcases hp with rfl | hp
  · exact h11
  rcases hp with rfl | hp
  · exact h12
  rcases hp with rfl | hp
  · exact h13
  rcases hp with rfl | hp
  · exact h14
  rcases hp with rfl | hp
  · exact h15
  rcases hp with rfl | hp
  · exact h16
  rcases hp with rfl | hp
  · exact h17
  rcases hp with rfl | hp
  · exact h18
  rcases hp with rfl | hp
  · exact h19
  rcases hp with rfl | hp
  · exact h20
  · simp at hp

end ConsecutiveCountingA5PureCubicRange

namespace ConsecutiveCountingA5PureCubicRange
open Polynomial

theorem actual_boundary_family_degree_le_five
    (x D E M ρ₀ C₀ : ℝ)
    (a b c m d₀ e₀ r₀ J A₀ B₀ : ℤ)
    (g η : ℝ) :
    ∀ p ∈ originalBoundaryCandidatesWithCurvature
      x D E M ρ₀ C₀ a b c m d₀ e₀ r₀ J A₀ B₀ g η,
      p.natDegree ≤ 5 := by
  classical
  let n := originalNPoly a b c m d₀ e₀ r₀ J A₀ B₀
  have hd : (originalDPoly b m d₀ r₀ J).natDegree ≤ 1 :=
    a5deg_originalD b m d₀ r₀ J
  have hu : (originalUPoly a b c m d₀ e₀ r₀ J A₀ B₀).natDegree ≤ 3 := by
    have hraw := actual_boundary_raw_degree_le_five
      x D E M ρ₀ C₀ a b c m d₀ e₀ r₀ J A₀ B₀ g η

    let d := originalDPoly b m d₀ r₀ J
    let e := originalEPoly a m e₀ r₀ J
    let q := originalQPoly a b c m d₀ e₀ r₀ J A₀ B₀
    have he : e.natDegree ≤ 1 :=
      a5deg_originalE a m e₀ r₀ J
    have hlin (r s : ℝ) :
        (C r * d + C s * e).natDegree ≤ 1 :=
      a5deg_add _ _ 1 (a5deg_cmul r d 1 hd)
        (a5deg_cmul s e 1 he)
    have hq : q.natDegree ≤ 1 := by
      dsimp [q,originalQPoly]
      exact a5deg_mulc _ _ 1 (hlin (A₀ : ℝ) (B₀ : ℝ))
    dsimp [originalUPoly]
    exact a5deg_mulc _ _ 3
      (a5deg_sub _ _ 3
        (a5deg_mul q (e ^ 2) 1 2 hq
          (a5deg_affine_power e he 2))
        (le_trans
          (a5deg_cmul _ _ 1
            (hlin (a : ℝ) ((3 * b : ℤ) : ℝ)))
          (by omega)))
  have hn : n.natDegree ≤ 5 := by
    dsimp [n,originalNPoly]
    exact a5deg_mul _ _ 2 3
      (a5deg_affine_power _ hd 2) hu
  have hderiv1 :
      n.derivative.natDegree ≤ n.natDegree - 1 :=
    Polynomial.natDegree_derivative_le n
  have hderiv2 :
      n.derivative.derivative.natDegree ≤
        n.derivative.natDegree - 1 :=
    Polynomial.natDegree_derivative_le n.derivative
  have hndd : n.derivative.derivative.natDegree ≤ 3 := by
    omega
  intro p hp
  have hfilter : p ∈
      (insert n.derivative.derivative
        ((originalBoundaryRawList
          x D E M ρ₀ C₀ a b c m d₀ e₀ r₀ J A₀ B₀ g η).toFinset.filter
            (· ≠ 0))).filter (· ≠ 0) := by
    exact hp
  have hin := (Finset.mem_filter.mp hfilter).1
  rcases Finset.mem_insert.mp hin with h | h
  · rw [h]
    exact hndd.trans (by omega)
  · have hraw : p ∈ originalBoundaryRawList
        x D E M ρ₀ C₀ a b c m d₀ e₀ r₀ J A₀ B₀ g η := by
      exact (List.mem_toFinset.mp (Finset.mem_filter.mp h).1)
    exact actual_boundary_raw_degree_le_five
      x D E M ρ₀ C₀ a b c m d₀ e₀ r₀ J A₀ B₀ g η p hraw

theorem actual_boundary_root_card_le_105
    (x D E M ρ₀ C₀ : ℝ)
    (a b c m d₀ e₀ r₀ J A₀ B₀ : ℤ)
    (g η : ℝ) :
    ((originalBoundaryCandidatesWithCurvature
      x D E M ρ₀ C₀
      a b c m d₀ e₀ r₀ J A₀ B₀ g η).biUnion
        (fun p => p.roots.toFinset)).card ≤ 105 := by
  classical
  let B := originalBoundaryCandidatesWithCurvature
    x D E M ρ₀ C₀ a b c m d₀ e₀ r₀ J A₀ B₀ g η
  have hcard : B.card ≤ 21 :=
    actual_boundary_family_card_le_21
      x D E M ρ₀ C₀ a b c m d₀ e₀ r₀ J A₀ B₀ g η
  have hdeg : ∀ p ∈ B, p.natDegree ≤ 5 :=
    actual_boundary_family_degree_le_five
      x D E M ρ₀ C₀ a b c m d₀ e₀ r₀ J A₀ B₀ g η
  calc
    (B.biUnion (fun p => p.roots.toFinset)).card ≤
        ∑ p ∈ B, p.natDegree :=
      family_root_card_le_degrees B
    _ ≤ ∑ p ∈ B, (5 : ℕ) := by
      apply Finset.sum_le_sum
      intro p hp
      exact hdeg p hp
    _ = B.card * 5 := by simp
    _ ≤ 105 := by omega

theorem actual_boundary_rank_le_105
    (x D E M ρ₀ C₀ : ℝ)
    (a b c m d₀ e₀ r₀ J A₀ B₀ : ℤ)
    (g η t : ℝ) :
    (((originalBoundaryCandidatesWithCurvature
      x D E M ρ₀ C₀
      a b c m d₀ e₀ r₀ J A₀ B₀ g η).biUnion
        (fun p => p.roots.toFinset)).filter
          (fun r => r ≤ t)).card ≤ 105 := by
  exact le_trans (Finset.card_filter_le _ _)
    (actual_boundary_root_card_le_105
      x D E M ρ₀ C₀ a b c m d₀ e₀ r₀ J A₀ B₀ g η)

end ConsecutiveCountingA5PureCubicRange

namespace ConsecutiveCountingA5PureCubicRange
open Polynomial

set_option maxHeartbeats 1000000 in
theorem actual_K_branch_on_closed_rank_interval
    (x D E M ρ₀ C₀ : ℝ)
    (a b c m d₀ e₀ r₀ J A₀ B₀ : ℤ)
    (g η s t : ℝ) (hst : s < t)
    (hrank :
      (((originalBoundaryCandidatesWithCurvature
        x D E M ρ₀ C₀ a b c m d₀ e₀ r₀ J A₀ B₀ g η).biUnion
          (fun f => f.roots.toFinset)).filter (fun r => r ≤ s)).card =
      (((originalBoundaryCandidatesWithCurvature
        x D E M ρ₀ C₀ a b c m d₀ e₀ r₀ J A₀ B₀ g η).biUnion
          (fun f => f.roots.toFinset)).filter (fun r => r ≤ t)).card)
    (hbranch :
      ((η * g ^ 2 ≤ eval s
          (originalKPoly a b c m d₀ e₀ r₀ J A₀ B₀ g)) ∧
        (η * g ^ 2 ≤ eval t
          (originalKPoly a b c m d₀ e₀ r₀ J A₀ B₀ g))) ∨
      ((eval s (originalKPoly a b c m d₀ e₀ r₀ J A₀ B₀ g) ≤
          -(η * g ^ 2)) ∧
        (eval t (originalKPoly a b c m d₀ e₀ r₀ J A₀ B₀ g) ≤
          -(η * g ^ 2))) ∨
      ((|eval s (originalKPoly a b c m d₀ e₀ r₀ J A₀ B₀ g)| ≤
          η * g ^ 2) ∧
        (|eval t (originalKPoly a b c m d₀ e₀ r₀ J A₀ B₀ g)| ≤
          η * g ^ 2))) :
    ((∀ z ∈ Set.Icc s t,
        η * g ^ 2 ≤ eval z
          (originalKPoly a b c m d₀ e₀ r₀ J A₀ B₀ g)) ∨
      (∀ z ∈ Set.Icc s t,
        eval z (originalKPoly a b c m d₀ e₀ r₀ J A₀ B₀ g) ≤
          -(η * g ^ 2)) ∨
      (∀ z ∈ Set.Icc s t,
        |eval z (originalKPoly a b c m d₀ e₀ r₀ J A₀ B₀ g)| ≤
          η * g ^ 2)) := by
  classical
  let k := originalKPoly a b c m d₀ e₀ r₀ J A₀ B₀ g
  let θ : ℝ := η * g ^ 2
  let L := originalBoundaryRawList x D E M ρ₀ C₀
    a b c m d₀ e₀ r₀ J A₀ B₀ g η
  generalize hB : originalBoundaryCandidatesWithCurvature
    x D E M ρ₀ C₀ a b c m d₀ e₀ r₀ J A₀ B₀ g η = B at hrank
  let R := B.biUnion (fun f => f.roots.toFinset)
  change (R.filter (fun r => r ≤ s)).card =
    (R.filter (fun r => r ≤ t)).card at hrank
  have hmember (p : Polynomial ℝ) (hp : p ∈ L)
      (hne : p ≠ 0) : p ∈ B := by
    rw [← hB]
    change p ∈
      (insert
        (derivative (derivative
          (originalNPoly a b c m d₀ e₀ r₀ J A₀ B₀)))
        ((originalBoundaryRawList x D E M ρ₀ C₀
          a b c m d₀ e₀ r₀ J A₀ B₀ g η).toFinset.filter
            (· ≠ 0))).filter (· ≠ 0)
    simp only [Finset.mem_filter, Finset.mem_insert,
      List.mem_toFinset]
    exact ⟨Or.inr ⟨hp,hne⟩,hne⟩
  have hroot (p : Polynomial ℝ) (hp : p ∈ B)
      (hne : p ≠ 0) (w : ℝ) (hw : eval w p = 0) :
      w ∈ R := by
    change w ∈ B.biUnion (fun f => f.roots.toFinset)
    exact root_mem_biUnion_of_member B p hp hne w hw
  have hweak (p : Polynomial ℝ) (hp : p ∈ L)
      (hsp : 0 ≤ eval s p) (htp : 0 ≤ eval t p) :
      ∀ z ∈ Set.Icc s t, 0 ≤ eval z p :=
    boundary_nonneg_on_rank L B R s t hst
      hmember hroot hrank p hp hsp htp
  rcases hbranch with ⟨hsK,htK⟩ | ⟨hsK,htK⟩ | ⟨hsK,htK⟩
  · have hsP : 0 ≤ eval s (k - C θ) := by
      simp only [eval_sub,eval_C]
      linarith
    have htP : 0 ≤ eval t (k - C θ) := by
      simp only [eval_sub,eval_C]
      linarith
    have hh := hweak (k - C θ)
      (by simp [L,originalBoundaryRawList,k,θ]) hsP htP
    left
    intro z hz
    have hzP := hh z hz
    simp only [eval_sub,eval_C] at hzP
    linarith
  · have hsP : 0 ≤ eval s (-k - C θ) := by
      simp only [eval_sub,eval_neg,eval_C]
      linarith
    have htP : 0 ≤ eval t (-k - C θ) := by
      simp only [eval_sub,eval_neg,eval_C]
      linarith
    have hh := hweak (-k - C θ)
      (by simp [L,originalBoundaryRawList,k,θ]) hsP htP
    right
    left
    intro z hz
    have hzP := hh z hz
    simp only [eval_sub,eval_neg,eval_C] at hzP
    linarith
  · have hsAbs := abs_le.mp hsK
    have htAbs := abs_le.mp htK
    have hsP1 : 0 ≤ eval s (C θ - k) := by
      simp only [eval_sub,eval_C]
      linarith [hsAbs.2]
    have htP1 : 0 ≤ eval t (C θ - k) := by
      simp only [eval_sub,eval_C]
      linarith [htAbs.2]
    have hsP2 : 0 ≤ eval s (C θ + k) := by
      simp only [eval_add,eval_C]
      linarith [hsAbs.1]
    have htP2 : 0 ≤ eval t (C θ + k) := by
      simp only [eval_add,eval_C]
      linarith [htAbs.1]
    have hh1 := hweak (C θ - k)
      (by simp [L,originalBoundaryRawList,k,θ]) hsP1 htP1
    have hh2 := hweak (C θ + k)
      (by simp [L,originalBoundaryRawList,k,θ]) hsP2 htP2
    right
    right
    intro z hz
    have hz1 := hh1 z hz
    have hz2 := hh2 z hz
    simp only [eval_sub,eval_add,eval_C] at hz1 hz2
    exact abs_le.mpr ⟨by linarith,by linarith⟩

end ConsecutiveCountingA5PureCubicRange

namespace ConsecutiveCountingA5PureCubicRange
open Polynomial

noncomputable def actualKTag (K : Polynomial ℝ) (θ z : ℝ) : Fin 3 :=
  if θ ≤ eval z K then 0
  else if eval z K ≤ -θ then 1
  else 2

theorem actualKTag_same_endpoint_branch
    (K : Polynomial ℝ) (θ s t : ℝ)
    (hsame : actualKTag K θ s = actualKTag K θ t) :
    ((θ ≤ eval s K) ∧ (θ ≤ eval t K)) ∨
      ((eval s K ≤ -θ) ∧ (eval t K ≤ -θ)) ∨
      ((|eval s K| ≤ θ) ∧ (|eval t K| ≤ θ)) := by
  by_cases hs₀ : θ ≤ eval s K
  · have ht₀ : θ ≤ eval t K := by
      by_contra ht₀
      by_cases ht₁ : eval t K ≤ -θ
      · simp [actualKTag, hs₀, ht₀, ht₁] at hsame
      · simp [actualKTag, hs₀, ht₀, ht₁] at hsame
    exact Or.inl ⟨hs₀,ht₀⟩
  · by_cases hs₁ : eval s K ≤ -θ
    · have ht₀ : ¬ θ ≤ eval t K := by
        intro ht₀
        simp [actualKTag, hs₀, hs₁, ht₀] at hsame
      have ht₁ : eval t K ≤ -θ := by
        by_contra ht₁
        simp [actualKTag, hs₀, hs₁, ht₀, ht₁] at hsame
      exact Or.inr (Or.inl ⟨hs₁,ht₁⟩)
    · have ht₀ : ¬ θ ≤ eval t K := by
        intro ht₀
        simp [actualKTag, hs₀, hs₁, ht₀] at hsame
      have ht₁ : ¬ eval t K ≤ -θ := by
        intro ht₁
        simp [actualKTag, hs₀, hs₁, ht₀, ht₁] at hsame
      exact Or.inr (Or.inr
        ⟨abs_le.mpr ⟨by linarith, by linarith⟩,
          abs_le.mpr ⟨by linarith, by linarith⟩⟩)

end ConsecutiveCountingA5PureCubicRange

namespace ConsecutiveCountingA5PureCubicRange
open Polynomial

noncomputable def actualBoundaryColour
    (x D E M ρ₀ C₀ : ℝ)
    (a b c m d₀ e₀ r₀ J A₀ B₀ : ℤ)
    (g η : ℝ) (t : ℤ) : Fin 636 := by
  classical
  let R :=
    (originalBoundaryCandidatesWithCurvature
      x D E M ρ₀ C₀ a b c m d₀ e₀ r₀ J A₀ B₀ g η).biUnion
      (fun p => p.roots.toFinset)
  let rank := (R.filter (fun r => r ≤ (t : ℝ))).card
  let q := originalQPoly a b c m d₀ e₀ r₀ J A₀ B₀
  let k := originalKPoly a b c m d₀ e₀ r₀ J A₀ B₀ g
  let tag := actualKTag k (η * g ^ 2) (t : ℝ)
  have hrank : rank ≤ 105 :=
    actual_boundary_rank_le_105
      x D E M ρ₀ C₀ a b c m d₀ e₀ r₀ J A₀ B₀ g η (t : ℝ)
  have htag : tag.val < 3 := tag.isLt
  refine ⟨rank * 6 +
    (if 0 < eval (t : ℝ) q then 3 else 0) + tag.val, ?_⟩
  split_ifs <;> omega

theorem actualBoundaryColour_same_components
    (x D E M ρ₀ C₀ : ℝ)
    (a b c m d₀ e₀ r₀ J A₀ B₀ : ℤ)
    (g η : ℝ) (s t : ℤ)
    (hcolour :
      actualBoundaryColour x D E M ρ₀ C₀
        a b c m d₀ e₀ r₀ J A₀ B₀ g η s =
      actualBoundaryColour x D E M ρ₀ C₀
        a b c m d₀ e₀ r₀ J A₀ B₀ g η t) :
    let R :=
      (originalBoundaryCandidatesWithCurvature
        x D E M ρ₀ C₀ a b c m d₀ e₀ r₀ J A₀ B₀ g η).biUnion
        (fun p => p.roots.toFinset)
    (R.filter (fun r => r ≤ (s : ℝ))).card =
      (R.filter (fun r => r ≤ (t : ℝ))).card ∧
    ((0 < eval (s : ℝ)
        (originalQPoly a b c m d₀ e₀ r₀ J A₀ B₀)) ↔
      0 < eval (t : ℝ)
        (originalQPoly a b c m d₀ e₀ r₀ J A₀ B₀)) ∧
    actualKTag
        (originalKPoly a b c m d₀ e₀ r₀ J A₀ B₀ g)
        (η * g ^ 2) (s : ℝ) =
      actualKTag
        (originalKPoly a b c m d₀ e₀ r₀ J A₀ B₀ g)
        (η * g ^ 2) (t : ℝ) := by
  classical
  dsimp only
  have hval := congrArg Fin.val hcolour
  dsimp [actualBoundaryColour] at hval
  have hsTag :=
    (actualKTag
      (originalKPoly a b c m d₀ e₀ r₀ J A₀ B₀ g)
      (η * g ^ 2) (s : ℝ)).isLt
  have htTag :=
    (actualKTag
      (originalKPoly a b c m d₀ e₀ r₀ J A₀ B₀ g)
      (η * g ^ 2) (t : ℝ)).isLt
  by_cases hspos :
      0 < eval (s : ℝ)
        (originalQPoly a b c m d₀ e₀ r₀ J A₀ B₀)
  · by_cases htpos :
        0 < eval (t : ℝ)
          (originalQPoly a b c m d₀ e₀ r₀ J A₀ B₀)
    · simp only [if_pos hspos,if_pos htpos] at hval
      refine ⟨by omega, by simp [hspos,htpos], ?_⟩
      apply Fin.ext
      omega
    · simp only [if_pos hspos,if_neg htpos] at hval
      omega
  · by_cases htpos :
        0 < eval (t : ℝ)
          (originalQPoly a b c m d₀ e₀ r₀ J A₀ B₀)
    · simp only [if_neg hspos,if_pos htpos] at hval
      omega
    · simp only [if_neg hspos,if_neg htpos] at hval
      refine ⟨by omega, by simp [hspos,htpos], ?_⟩
      apply Fin.ext
      omega

end ConsecutiveCountingA5PureCubicRange

namespace ConsecutiveCountingA5PureCubicRange
open Polynomial

theorem fields_of_closed_polynomial_signs
    (d e u v n : Polynomial ℝ)
    (x D E ρ h z : ℝ)
    (hsigns :
      0 ≤ eval z (d - C 1) ∧
      0 ≤ eval z (e - C 1) ∧
      0 ≤ eval z (u - C 1) ∧
      0 ≤ eval z (v - C 1) ∧
      0 < eval z (d - C (D / 2)) ∧
      0 ≤ eval z (C D - d) ∧
      0 < eval z (e - C (E / 2)) ∧
      0 ≤ eval z (C E - e) ∧
      0 < eval z (d - C ρ * e) ∧
      0 ≤ eval z (C (ρ + h) * e - d) ∧
      0 ≤ eval z (C x - n)) :
    1 ≤ eval z d ∧ 1 ≤ eval z e ∧
    1 ≤ eval z u ∧ 1 ≤ eval z v ∧
    D / 2 < eval z d ∧ eval z d ≤ D ∧
    E / 2 < eval z e ∧ eval z e ≤ E ∧
    ρ < eval z d / eval z e ∧
    eval z d / eval z e ≤ ρ + h ∧ eval z n ≤ x := by
  simp only [eval_sub, eval_mul, eval_C] at hsigns
  rcases hsigns with
    ⟨hd1, he1, hu1, hv1, hdLo, hdHi, heLo, heHi,
      hrLo, hrHi, hnHi⟩
  have hepos : 0 < eval z e := by linarith only [he1]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · linarith only [hd1]
  · linarith only [he1]
  · linarith only [hu1]
  · linarith only [hv1]
  · linarith only [hdLo]
  · linarith only [hdHi]
  · linarith only [heLo]
  · linarith only [heHi]
  · apply (lt_div_iff₀ hepos).2
    linarith only [hrLo]
  · apply (div_le_iff₀ hepos).2
    linarith only [hrHi]
  · linarith only [hnHi]

theorem abs_eval_ge_one_of_polynomial_gap
    (q : Polynomial ℝ) (z : ℝ)
    (hgap :
      0 ≤ eval z (q - C 1) ∨
      0 ≤ eval z (-q - C 1)) :
    1 ≤ |eval z q| := by
  rcases hgap with hpos | hneg
  · simp only [eval_sub, eval_C] at hpos
    have hq : 0 ≤ eval z q := by linarith only [hpos]
    rw [abs_of_nonneg hq]
    linarith only [hpos]
  · simp only [eval_sub, eval_neg, eval_C] at hneg
    have hq : eval z q ≤ 0 := by linarith only [hneg]
    rw [abs_of_nonpos hq]
    linarith only [hneg]

theorem actual_closed_geometry_pair_length
    (C_ratio c₀ : ℝ) (hC_ratio : 0 < C_ratio) (hc₀ : 0 < c₀) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ x D E M ρ₀ : ℝ,
        2 ≤ x → 0 < D → 0 < E → 0 < M →
        c₀ * ((D * E) ^ ((4 : ℝ) / 3) * x ^ (-(1 : ℝ) / 3)) ≤ M →
        c₀ * (x / (D * E)) ^ ((4 : ℝ) / 3) ≤ M →
        ∀ (P Q : MvPolynomial (Fin 2) ℤ)
          (a b c m d₀ e₀ r₀ J A₀ B₀ : ℤ),
          Int.gcd a b = 1 →
          c ≠ 0 → m ≠ 0 → 0 < J →
          a * d₀ + b * e₀ = 1 →
          a * B₀ - b * A₀ ≠ 0 →
          ∀
            (hpure : MvPolynomial.X (1 : Fin 2) ^ 2 * Q -
              MvPolynomial.X (0 : Fin 2) ^ 2 * P =
              MvPolynomial.C c *
                (MvPolynomial.C a * MvPolynomial.X 0 +
                  MvPolynomial.C b * MvPolynomial.X 1) ^ 5)
            (hPnorm : P =
              (MvPolynomial.C A₀ * MvPolynomial.X (0 : Fin 2) +
                MvPolynomial.C B₀ * MvPolynomial.X (1 : Fin 2)) *
                  MvPolynomial.X (1 : Fin 2) ^ 2 -
                MvPolynomial.C c *
                  (MvPolynomial.C a * MvPolynomial.X (0 : Fin 2) +
                    MvPolynomial.C b * MvPolynomial.X (1 : Fin 2)) ^ 2 *
                  MvPolynomial.C (a ^ 2) *
                  (MvPolynomial.C a * MvPolynomial.X (0 : Fin 2) +
                    MvPolynomial.C (3 * b) * MvPolynomial.X (1 : Fin 2)))
            (hQnorm : Q =
              (MvPolynomial.C A₀ * MvPolynomial.X (0 : Fin 2) +
                MvPolynomial.C B₀ * MvPolynomial.X (1 : Fin 2)) *
                  MvPolynomial.X (0 : Fin 2) ^ 2 +
                MvPolynomial.C c *
                  (MvPolynomial.C a * MvPolynomial.X (0 : Fin 2) +
                    MvPolynomial.C b * MvPolynomial.X (1 : Fin 2)) ^ 2 *
                  MvPolynomial.C (b ^ 2) *
                  (MvPolynomial.C (3 * a) * MvPolynomial.X (0 : Fin 2) +
                    MvPolynomial.C b * MvPolynomial.X (1 : Fin 2)))
            (p₁ p₂ : (ℕ × ℕ) × (ℕ × ℕ)),
            p₁ ∈ FixedProgressionS x D E M ρ₀ C_ratio
              P Q a b m d₀ e₀ r₀ J →
            p₂ ∈ FixedProgressionS x D E M ρ₀ C_ratio
              P Q a b m d₀ e₀ r₀ J →
            let s : ℝ := ((levelT d₀ e₀ r₀ J p₁ : ℤ) : ℝ);
            let t : ℝ := ((levelT d₀ e₀ r₀ J p₂ : ℤ) : ℝ);
            let q : Polynomial ℝ :=
              originalQPoly a b c m d₀ e₀ r₀ J A₀ B₀;
            let q_r : ℝ := originalQr a b c m A₀ B₀;
            let g : ℝ := |((a * b : ℤ) : ℝ)|;
            let K : Polynomial ℝ :=
              originalKPoly a b c m d₀ e₀ r₀ J A₀ B₀ g;
            let N : Polynomial ℝ :=
              originalNPoly a b c m d₀ e₀ r₀ J A₀ B₀;
            s ≤ t →
            1 ≤ |q_r| * (J : ℝ) →
            |(m : ℝ)| ^ 3 ≤ |q_r| * (J : ℝ) ^ 3 →
            (∀ z ∈ Set.Icc s t,
              originalAcceptedPolyAt x D E M ρ₀ C_ratio
                a b c m d₀ e₀ r₀ J A₀ B₀ z) →
            ((∀ z ∈ Set.Icc s t,
                0 ≤ eval z (q - Polynomial.C 1)) ∨
              (∀ z ∈ Set.Icc s t,
                0 ≤ eval z (-q - Polynomial.C 1))) →
            ((∀ z ∈ Set.Icc s t,
                g ^ 2 / 100 ≤ eval z K) ∨
              (∀ z ∈ Set.Icc s t,
                eval z K ≤ -(g ^ 2 / 100)) ∨
              ((∀ z ∈ Set.Icc s t,
                  |eval z K| ≤ g ^ 2 / 100) ∧
                ((∀ z ∈ Set.Icc s t,
                    0 ≤ eval z N.derivative.derivative) ∨
                  (∀ z ∈ Set.Icc s t,
                    eval z N.derivative.derivative ≤ 0)))) →
            |t - s| ≤ C *
              (1 + Real.sqrt x /
                (Real.sqrt M * (D * E) ^ ((1 : ℝ) / 3))) := by
  obtain ⟨Cpair, hCpair, hpair⟩ :=
    ConsecutiveCountingA5OriginalPairLength.original_accepted_pair_length
      C_ratio c₀ hC_ratio hc₀
  refine ⟨Cpair, hCpair, ?_⟩
  intro x D E M ρ₀ hx hD hE hM hrange₁ hrange₂
    P Q a b c m d₀ e₀ r₀ J A₀ B₀ hprim hc hm hJ hbez hDelta
    hpure hPnorm hQnorm p₁ p₂ hp₁ hp₂
  let s : ℝ := ((levelT d₀ e₀ r₀ J p₁ : ℤ) : ℝ)
  let t : ℝ := ((levelT d₀ e₀ r₀ J p₂ : ℤ) : ℝ)
  let q : Polynomial ℝ := originalQPoly a b c m d₀ e₀ r₀ J A₀ B₀
  let q_r : ℝ := originalQr a b c m A₀ B₀
  let g : ℝ := |((a * b : ℤ) : ℝ)|
  let K : Polynomial ℝ := originalKPoly a b c m d₀ e₀ r₀ J A₀ B₀ g
  let N : Polynomial ℝ := originalNPoly a b c m d₀ e₀ r₀ J A₀ B₀
  dsimp only
  intro hst hI₁ hI₃ haccepted hqbranch hbranch
  let d : Polynomial ℝ := originalDPoly b m d₀ r₀ J
  let e : Polynomial ℝ := originalEPoly a m e₀ r₀ J
  let U : Polynomial ℝ := originalUPoly a b c m d₀ e₀ r₀ J A₀ B₀
  let V : Polynomial ℝ := originalVPoly a b c m d₀ e₀ r₀ J A₀ B₀
  have hUV := actual_original_point_eval_UV
    x D E M ρ₀ C_ratio P Q a b c m d₀ e₀ r₀ J A₀ B₀
    hc hm hbez hpure hPnorm hQnorm p₁ hp₁
  rcases hp₁ with ⟨hOrig, hlevel, hprog⟩
  have hDEN := actual_original_point_eval_D_E_N
    a b c m d₀ e₀ r₀ J A₀ B₀ hbez p₁ hlevel hprog hUV.1
  have hds : eval s d = (p₁.1.1 : ℝ) := hDEN.1
  have hes : eval s e = (p₁.1.2 : ℝ) := hDEN.2.1
  rcases hOrig with
    ⟨hdn, hen, hun, hvn, hF1, hn, _⟩
  have hclosed :
      ∀ z : ℝ, s ≤ z → z ≤ t →
        D / 2 < eval z d ∧ eval z d ≤ D ∧
        E / 2 < eval z e ∧ eval z e ≤ E ∧
        ρ₀ < eval z d / eval z e ∧
        eval z d / eval z e ≤ ρ₀ + C_ratio * D / (E * M) ∧
        1 ≤ eval z U ∧ 1 ≤ eval z V ∧
        1 ≤ |eval z q| ∧ eval z N ≤ x := by
    intro z hzs hzt
    have hsigns := haccepted z ⟨hzs, hzt⟩
    have hfields := fields_of_closed_polynomial_signs
      d e U V N x D E ρ₀ (C_ratio * D / (E * M)) z hsigns
    rcases hfields with
      ⟨hd1, he1, hu1, hv1, hdLo, hdHi, heLo, heHi,
        hrLo, hrHi, hnHi⟩
    have hqgap : 1 ≤ |eval z q| := by
      apply abs_eval_ge_one_of_polynomial_gap q z
      rcases hqbranch with hpos | hneg
      · exact Or.inl (hpos z ⟨hzs, hzt⟩)
      · exact Or.inr (hneg z ⟨hzs, hzt⟩)
    exact ⟨hdLo, hdHi, heLo, heHi, hrLo, hrHi,
      hu1, hv1, hqgap, hnHi⟩
  have hbranchPair :
      ((∀ z : ℝ, s ≤ z → z ≤ t →
          g ^ 2 / 100 ≤ eval z K) ∨
        (∀ z : ℝ, s ≤ z → z ≤ t →
          eval z K ≤ -(g ^ 2 / 100)) ∨
        ((∀ z : ℝ, s ≤ z → z ≤ t →
            |eval z K| ≤ g ^ 2 / 100) ∧
          ((∀ z : ℝ, s ≤ z → z ≤ t →
              0 ≤ eval z N.derivative.derivative) ∨
            (∀ z : ℝ, s ≤ z → z ≤ t →
              eval z N.derivative.derivative ≤ 0)))) := by
    rcases hbranch with hpos | hneg | ⟨hsmall, hcurv⟩
    · exact Or.inl (fun z hzs hzt => hpos z ⟨hzs, hzt⟩)
    · exact Or.inr (Or.inl (fun z hzs hzt => hneg z ⟨hzs, hzt⟩))
    · apply Or.inr
      apply Or.inr
      refine ⟨fun z hzs hzt => hsmall z ⟨hzs, hzt⟩, ?_⟩
      rcases hcurv with hnonneg | hnonpos
      · exact Or.inl (fun z hzs hzt => hnonneg z ⟨hzs, hzt⟩)
      · exact Or.inr (fun z hzs hzt => hnonpos z ⟨hzs, hzt⟩)
  have hbound : |t - s| ≤ Cpair *
      (1 + Real.sqrt x /
        (Real.sqrt M * (D * E) ^ ((1 : ℝ) / 3))) :=
    hpair x D E M ρ₀ s t hx hD hE hM hst hrange₁ hrange₂
      a b c m d₀ e₀ r₀ J A₀ B₀ hprim hc hm hJ hbez hDelta
      p₁.1.1 p₁.1.2 p₁.2.1 p₁.2.2 hdn hen hun hvn
      hF1 hn hds hes hI₁ hI₃ hclosed hbranchPair
  exact hbound

#print axioms fields_of_closed_polynomial_signs
#print axioms abs_eval_ge_one_of_polynomial_gap
#print axioms actual_closed_geometry_pair_length

end ConsecutiveCountingA5PureCubicRange

namespace ConsecutiveCountingA5PureCubicRange
open Polynomial

theorem qzero_good_partition_card
    (T : Finset ℤ) (q : Polynomial ℝ) (B : ℕ)
    (hzero : (T.filter fun t : ℤ => q.eval (t : ℝ) = 0).card ≤ 1)
    (hgood : (T.filter fun t : ℤ => q.eval (t : ℝ) ≠ 0).card ≤ B) :
    T.card ≤ B + 1 := by
  classical
  let Z := T.filter fun t : ℤ => q.eval (t : ℝ) = 0
  let G := T.filter fun t : ℤ => q.eval (t : ℝ) ≠ 0
  have hcover : T = Z ∪ G := by
    ext t
    simp only [Z, G, Finset.mem_union, Finset.mem_filter]
    tauto
  have hcard : T.card ≤ Z.card + G.card := by
    rw [hcover]
    exact Finset.card_union_le Z G
  change Z.card ≤ 1 at hzero
  change G.card ≤ B at hgood
  omega

theorem qzero_good_coloured_integer_count
    (T : Finset ℤ) (q : Polynomial ℝ) (color : ℤ → Fin 636)
    (A : ℝ) (hA : 0 ≤ A)
    (hzero : (T.filter fun t : ℤ => q.eval (t : ℝ) = 0).card ≤ 1)
    (hpair : ∀ s ∈ T, ∀ t ∈ T,
      q.eval (s : ℝ) ≠ 0 → q.eval (t : ℝ) ≠ 0 →
      color s = color t → s ≤ t → ((t - s : ℤ) : ℝ) ≤ A) :
    T.card ≤ 636 * (2 * Nat.ceil A + 1) + 1 := by
  classical
  apply qzero_good_partition_card T q _ hzero
  apply finite_colored_integer_diameter_count
    (T.filter fun t : ℤ => q.eval (t : ℝ) ≠ 0) color A hA
  intro s hs t ht hcol hst
  obtain ⟨hsT, hsne⟩ := Finset.mem_filter.mp hs
  obtain ⟨htT, htne⟩ := Finset.mem_filter.mp ht
  exact hpair s hsT t htT hsne htne hcol hst

theorem ceil_636_with_one_uniform_price
    (C F : ℝ) (hC : 1 ≤ C) (hF : 1 ≤ F) :
    ((636 * (2 * Nat.ceil (C * F) + 1) + 1 : ℕ) : ℝ) ≤
      (1272 * C + 1909) * F := by
  have hCF : 0 ≤ C * F :=
    mul_nonneg (le_trans zero_le_one hC) (le_trans zero_le_one hF)
  have hceil : (Nat.ceil (C * F) : ℝ) ≤ C * F + 1 :=
    le_of_lt (Nat.ceil_lt_add_one hCF)
  calc
    _ = 1272 * (Nat.ceil (C * F) : ℝ) + 637 := by
      push_cast <;> ring
    _ ≤ 1272 * (C * F) + 1909 := by linarith only [hceil]
    _ ≤ (1272 * C + 1909) * F := by nlinarith only [hF]

theorem original_range_price_ge_one
    (x M W : ℝ) (hM : 0 < M) (hW : 0 < W) :
    1 ≤ 1 + Real.sqrt x /
      (Real.sqrt M * W ^ ((1 : ℝ) / 3)) := by
  have hden : 0 < Real.sqrt M * W ^ ((1 : ℝ) / 3) :=
    mul_pos (Real.sqrt_pos.2 hM) (Real.rpow_pos_of_pos hW _)
  have hfrac : 0 ≤ Real.sqrt x /
      (Real.sqrt M * W ^ ((1 : ℝ) / 3)) :=
    div_nonneg (Real.sqrt_nonneg x) hden.le
  linarith only [hfrac]

theorem qzero_good_coloured_uniform_price
    (T : Finset ℤ) (q : Polynomial ℝ) (color : ℤ → Fin 636)
    (C F : ℝ) (hC : 1 ≤ C) (hF : 1 ≤ F)
    (hzero : (T.filter fun t : ℤ => q.eval (t : ℝ) = 0).card ≤ 1)
    (hpair : ∀ s ∈ T, ∀ t ∈ T,
      q.eval (s : ℝ) ≠ 0 → q.eval (t : ℝ) ≠ 0 →
      color s = color t → s ≤ t →
      ((t - s : ℤ) : ℝ) ≤ C * F) :
    (T.card : ℝ) ≤ (1272 * C + 1909) * F := by
  have hCF : 0 ≤ C * F :=
    mul_nonneg (le_trans zero_le_one hC) (le_trans zero_le_one hF)
  have hbound := qzero_good_coloured_integer_count
    T q color (C * F) hCF hzero hpair
  have hboundR :
      (T.card : ℝ) ≤
        ((636 * (2 * Nat.ceil (C * F) + 1) + 1 : ℕ) : ℝ) := by
    exact_mod_cast hbound
  exact hboundR.trans (ceil_636_with_one_uniform_price C F hC hF)

end ConsecutiveCountingA5PureCubicRange

namespace ConsecutiveCountingA5PureCubicRange
open Polynomial

theorem fibre_q_gap_on_actual_closed_rank_interval
    (x D E M ρ₀ C₀ : ℝ)
    (a b c m d₀ e₀ r₀ J A₀ B₀ : ℤ)
    (g η s t : ℝ) (hst : s < t)
    (hrank :
      (((originalBoundaryCandidatesWithCurvature
        x D E M ρ₀ C₀ a b c m d₀ e₀ r₀ J A₀ B₀ g η).biUnion
          (fun f => f.roots.toFinset)).filter (fun r => r ≤ s)).card =
      (((originalBoundaryCandidatesWithCurvature
        x D E M ρ₀ C₀ a b c m d₀ e₀ r₀ J A₀ B₀ g η).biUnion
          (fun f => f.roots.toFinset)).filter (fun r => r ≤ t)).card)
    (hgap :
      (1 ≤ eval s (originalQPoly a b c m d₀ e₀ r₀ J A₀ B₀) ∧
        1 ≤ eval t (originalQPoly a b c m d₀ e₀ r₀ J A₀ B₀)) ∨
      (eval s (originalQPoly a b c m d₀ e₀ r₀ J A₀ B₀) ≤ -1 ∧
        eval t (originalQPoly a b c m d₀ e₀ r₀ J A₀ B₀) ≤ -1)) :
    (∀ z ∈ Set.Icc s t,
      0 ≤ eval z
        (originalQPoly a b c m d₀ e₀ r₀ J A₀ B₀ - C 1)) ∨
    (∀ z ∈ Set.Icc s t,
      0 ≤ eval z
        (-originalQPoly a b c m d₀ e₀ r₀ J A₀ B₀ - C 1)) := by
  classical
  let q := originalQPoly a b c m d₀ e₀ r₀ J A₀ B₀
  change (1 ≤ eval s q ∧ 1 ≤ eval t q) ∨
    (eval s q ≤ -1 ∧ eval t q ≤ -1) at hgap
  let L := originalBoundaryRawList x D E M ρ₀ C₀
    a b c m d₀ e₀ r₀ J A₀ B₀ g η
  generalize hB : originalBoundaryCandidatesWithCurvature
    x D E M ρ₀ C₀ a b c m d₀ e₀ r₀ J A₀ B₀ g η = B at hrank
  let R := B.biUnion (fun f => f.roots.toFinset)
  change (R.filter (fun r => r ≤ s)).card =
    (R.filter (fun r => r ≤ t)).card at hrank
  have hmember (p : Polynomial ℝ) (hp : p ∈ L)
      (hne : p ≠ 0) : p ∈ B := by
    rw [← hB]
    change p ∈
      (insert
        (derivative (derivative
          (originalNPoly a b c m d₀ e₀ r₀ J A₀ B₀)))
        ((originalBoundaryRawList x D E M ρ₀ C₀
          a b c m d₀ e₀ r₀ J A₀ B₀ g η).toFinset.filter
            (· ≠ 0))).filter (· ≠ 0)
    simp only [Finset.mem_filter, Finset.mem_insert, List.mem_toFinset]
    exact ⟨Or.inr ⟨hp, hne⟩, hne⟩
  have hBnonzero : ∀ p ∈ B, p ≠ 0 := by
    intro p hp
    rw [← hB] at hp
    exact originalBoundary_nonzero
      x D E M ρ₀ C₀ a b c m d₀ e₀ r₀ J A₀ B₀ g η p hp
  have hroot (p : Polynomial ℝ) (hp : p ∈ B)
      (hne : p ≠ 0) (w : ℝ) (hw : eval w p = 0) :
      w ∈ R :=
    root_mem_biUnion_of_member B p hp hne w hw
  have hweak (p : Polynomial ℝ) (hp : p ∈ L)
      (hsp : 0 ≤ eval s p) (htp : 0 ≤ eval t p) :
      ∀ z ∈ Set.Icc s t, 0 ≤ eval z p :=
    boundary_nonneg_on_rank L B R s t hst
      hmember hroot hrank p hp hsp htp
  rcases hgap with ⟨hs, ht⟩ | ⟨hs, ht⟩
  · have hsP : 0 ≤ eval s (q - C 1) := by
      simp only [eval_sub, eval_C]
      linarith only [hs]
    have htP : 0 ≤ eval t (q - C 1) := by
      simp only [eval_sub, eval_C]
      linarith only [ht]
    left
    exact hweak (q - C 1)
      (by simp [L, originalBoundaryRawList, q]) hsP htP
  · have hsP : 0 ≤ eval s (-q - C 1) := by
      simp only [eval_sub, eval_neg, eval_C]
      linarith only [hs]
    have htP : 0 ≤ eval t (-q - C 1) := by
      simp only [eval_sub, eval_neg, eval_C]
      linarith only [ht]
    right
    exact hweak (-q - C 1)
      (by simp [L, originalBoundaryRawList, q]) hsP htP

end ConsecutiveCountingA5PureCubicRange

namespace JocelynClaims
open Polynomial
open ConsecutiveCountingA5PureCubicRange

theorem claim_fcd806582eb6476367651c9b465c2bcc8589ade4ab91ca64831d3136f30966d6 :
  ∀ C_ratio c₀ : ℝ,
    0 < C_ratio → 0 < c₀ →
      ∃ Cg : ℝ, 1 ≤ Cg ∧
        ∀ x D E M ρ₀ : ℝ,
          2 ≤ x → 0 < D → 0 < E → 0 < M →
          c₀ * ((D * E) ^ ((4 : ℝ) / 3) *
            x ^ (-(1 : ℝ) / 3)) ≤ M →
          c₀ * (x / (D * E)) ^ ((4 : ℝ) / 3) ≤ M →
          ∀ (P Q : MvPolynomial (Fin 2) ℤ)
            (a b c m d₀ e₀ r₀ A₀ B₀ : ℤ),
            Int.gcd a b = 1 →
            c ≠ 0 → m ≠ 0 →
            a * d₀ + b * e₀ = 1 →
            a * B₀ - b * A₀ ≠ 0 →
            ∀ J : ℕ, 0 < J →
              MvPolynomial.X (1 : Fin 2) ^ 2 * Q -
                  MvPolynomial.X (0 : Fin 2) ^ 2 * P =
                MvPolynomial.C c *
                  (MvPolynomial.C a * MvPolynomial.X 0 +
                    MvPolynomial.C b * MvPolynomial.X 1) ^ 5 →
              P =
                (MvPolynomial.C A₀ * MvPolynomial.X (0 : Fin 2) +
                  MvPolynomial.C B₀ * MvPolynomial.X (1 : Fin 2)) *
                    MvPolynomial.X (1 : Fin 2) ^ 2 -
                  MvPolynomial.C c *
                    (MvPolynomial.C a * MvPolynomial.X (0 : Fin 2) +
                      MvPolynomial.C b * MvPolynomial.X (1 : Fin 2)) ^ 2 *
                    MvPolynomial.C (a ^ 2) *
                    (MvPolynomial.C a * MvPolynomial.X (0 : Fin 2) +
                      MvPolynomial.C (3 * b) * MvPolynomial.X (1 : Fin 2)) →
              Q =
                (MvPolynomial.C A₀ * MvPolynomial.X (0 : Fin 2) +
                  MvPolynomial.C B₀ * MvPolynomial.X (1 : Fin 2)) *
                    MvPolynomial.X (0 : Fin 2) ^ 2 +
                  MvPolynomial.C c *
                    (MvPolynomial.C a * MvPolynomial.X (0 : Fin 2) +
                      MvPolynomial.C b * MvPolynomial.X (1 : Fin 2)) ^ 2 *
                    MvPolynomial.C (b ^ 2) *
                    (MvPolynomial.C (3 * a) * MvPolynomial.X (0 : Fin 2) +
                      MvPolynomial.C b * MvPolynomial.X (1 : Fin 2)) →
              let D_m : Polynomial ℚ :=
                Polynomial.C ((m * d₀ : ℤ) : ℚ) +
                  Polynomial.C (b : ℚ) * Polynomial.X;
              let E_m : Polynomial ℚ :=
                Polynomial.C ((m * e₀ : ℤ) : ℚ) -
                  Polynomial.C (a : ℚ) * Polynomial.X;
              let R : Polynomial ℚ :=
                Polynomial.C (r₀ : ℚ) +
                  Polynomial.C (J : ℚ) * Polynomial.X;
              let U_m : Polynomial ℚ :=
                Polynomial.C (((c : ℚ) * (m : ℚ) ^ 5)⁻¹) *
                  MvPolynomial.eval₂
                    (Int.castRingHom (Polynomial ℚ)) ![D_m, E_m] P;
              let V_m : Polynomial ℚ :=
                Polynomial.C (((c : ℚ) * (m : ℚ) ^ 5)⁻¹) *
                  MvPolynomial.eval₂
                    (Int.castRingHom (Polynomial ℚ)) ![D_m, E_m] Q;
              (∀ k : ℕ, ∃ z : ℤ, (U_m.comp R).coeff k = (z : ℚ)) →
              (∀ k : ℕ, ∃ z : ℤ, (V_m.comp R).coeff k = (z : ℚ)) →
              let OriginalS : Set ((ℕ × ℕ) × (ℕ × ℕ)) :=
                {q | 1 ≤ q.1.1 ∧ 1 ≤ q.1.2 ∧
                  1 ≤ q.2.1 ∧ 1 ≤ q.2.2 ∧
                  ((q.1.2 ^ 2 * q.2.2 : ℕ) : ℤ) =
                    ((q.1.1 ^ 2 * q.2.1 : ℕ) : ℤ) + 1 ∧
                  ((q.1.1 ^ 2 * q.2.1 : ℕ) : ℝ) ≤ x ∧
                  D / 2 < (q.1.1 : ℝ) ∧ (q.1.1 : ℝ) ≤ D ∧
                  E / 2 < (q.1.2 : ℝ) ∧ (q.1.2 : ℝ) ≤ E ∧
                  ρ₀ < (q.1.1 : ℝ) / (q.1.2 : ℝ) ∧
                  (q.1.1 : ℝ) / (q.1.2 : ℝ) ≤
                    ρ₀ + C_ratio * D / (E * M) ∧
                  (q.2.1 : ℤ) *
                      MvPolynomial.eval ![(q.1.1 : ℤ), (q.1.2 : ℤ)] Q =
                    (q.2.2 : ℤ) *
                      MvPolynomial.eval ![(q.1.1 : ℤ), (q.1.2 : ℤ)] P};
              let levelR : ((ℕ × ℕ) × (ℕ × ℕ)) → ℤ :=
                fun q => e₀ * (q.1.1 : ℤ) - d₀ * (q.1.2 : ℤ);
              let levelT : ((ℕ × ℕ) × (ℕ × ℕ)) → ℤ :=
                fun q => (levelR q - r₀) / (J : ℤ);
              let S : Set ((ℕ × ℕ) × (ℕ × ℕ)) :=
                {q | q ∈ OriginalS ∧
                  a * (q.1.1 : ℤ) + b * (q.1.2 : ℤ) = m ∧
                  levelR q = r₀ + (J : ℤ) * levelT q};
              S.Finite ∧
                (S.ncard : ℝ) ≤ Cg *
                  (1 + Real.sqrt x /
                    (Real.sqrt M * (D * E) ^ ((1 : ℝ) / 3))) := by
  classical
  intro C_ratio c₀ hC_ratio hc₀
  obtain ⟨Cpair, hCpair, hPairLength⟩ :=
    ConsecutiveCountingA5PureCubicRange.actual_closed_geometry_pair_length
      C_ratio c₀ hC_ratio hc₀
  let Cg : ℝ := 1272 * Cpair + 1909
  have hCg : 1 ≤ Cg := by
    dsimp only [Cg]
    linarith only [hCpair]
  refine ⟨Cg, hCg, ?_⟩
  intro x D E M ρ₀ hx hD hE hM hRange₁ hRange₂
    P Q a b c m d₀ e₀ r₀ A₀ B₀ hab hc hm hbez hDelta J hJ
    hpure hPnorm hQnorm
  intro D_m E_m R U_m V_m hUInt hVInt
  let F : ℝ := 1 + Real.sqrt x /
    (Real.sqrt M * (D * E) ^ ((1 : ℝ) / 3))
  change
    (ConsecutiveCountingA5PureCubicRange.FixedProgressionS
      x D E M ρ₀ C_ratio P Q a b m d₀ e₀ r₀ (J : ℤ)).Finite ∧
    ((ConsecutiveCountingA5PureCubicRange.FixedProgressionS
      x D E M ρ₀ C_ratio P Q a b m d₀ e₀ r₀ (J : ℤ)).ncard : ℝ) ≤ Cg * F
  have hFinite :=
    ConsecutiveCountingA5PureCubicRange.fixedProgressionS_finite
      x D E M ρ₀ C_ratio P Q a b m d₀ e₀ r₀ (J : ℤ)
  refine ⟨hFinite, ?_⟩
  have hUNorm := hUInt
  have hVNorm := hVInt
  dsimp only [U_m] at hUNorm
  dsimp only [V_m] at hVNorm
  rw [hPnorm] at hUNorm
  rw [hQnorm] at hVNorm
  obtain ⟨q₀, q₁, theta, hBase, hSlope, hq₁, hTheta,
      hThetaNe, hU₃, hV₃, hINT₁, hINT₃⟩ :=
    JocelynClaims.claim_23901e5a643bd6f3764df51b1a387d0e23f431c522eaa8213ba45390c29b2129
      a b c m d₀ e₀ r₀ A₀ B₀ hab hc hm hbez hDelta J hJ hUNorm hVNorm
  obtain ⟨hQrCast, hQeval, hQgap, hQzero⟩ :=
    ConsecutiveCountingA5SameJQArithmetic.original_sameJ_integer_q_join
      a b c m d₀ e₀ r₀ A₀ B₀ q₀ q₁ J hBase hSlope hq₁
  obtain ⟨hI₁, hI₃⟩ :=
    ConsecutiveCountingA5SameJQArithmetic.original_sameJ_int_constraints
      a b c m A₀ B₀ J hINT₁ hINT₃
  have hJZ : 0 < (J : ℤ) := by exact_mod_cast hJ
  let q : Polynomial ℝ :=
    ConsecutiveCountingA5PureCubicRange.originalQPoly
      a b c m d₀ e₀ r₀ (J : ℤ) A₀ B₀
  let g : ℝ := |((a * b : ℤ) : ℝ)|
  let K : Polynomial ℝ :=
    ConsecutiveCountingA5PureCubicRange.originalKPoly
      a b c m d₀ e₀ r₀ (J : ℤ) A₀ B₀ g
  let N : Polynomial ℝ :=
    ConsecutiveCountingA5PureCubicRange.originalNPoly
      a b c m d₀ e₀ r₀ (J : ℤ) A₀ B₀
  change ∀ t : ℤ, eval (t : ℝ) q = 0 ∨
    1 ≤ |eval (t : ℝ) q| at hQgap
  change ∀ T : Finset ℤ,
    (T.filter fun t : ℤ => eval (t : ℝ) q = 0).card ≤ 1 at hQzero
  let sf := hFinite.toFinset
  let T : Finset ℤ :=
    sf.image (ConsecutiveCountingA5PureCubicRange.levelT d₀ e₀ r₀ (J : ℤ))
  let color : ℤ → Fin 636 :=
    ConsecutiveCountingA5PureCubicRange.actualBoundaryColour
      x D E M ρ₀ C_ratio a b c m d₀ e₀ r₀ (J : ℤ) A₀ B₀
      g (1 / 100)
  have hF : 1 ≤ F :=
    ConsecutiveCountingA5PureCubicRange.original_range_price_ge_one
      x M (D * E) hM (mul_pos hD hE)
  have hCF : 0 ≤ Cpair * F :=
    mul_nonneg (le_trans zero_le_one hCpair) (le_trans zero_le_one hF)
  have hGoodPair : ∀ s ∈ T, ∀ t ∈ T,
      eval (s : ℝ) q ≠ 0 → eval (t : ℝ) q ≠ 0 →
      color s = color t → s ≤ t →
      ((t - s : ℤ) : ℝ) ≤ Cpair * F := by
    intro s hs t ht hsne htne hcolor hst
    by_cases hEq : s = t
    · subst t
      simpa only [sub_self, Int.cast_zero] using hCF
    have hstZ : s < t := lt_of_le_of_ne hst hEq
    have hstR : (s : ℝ) < (t : ℝ) := by exact_mod_cast hstZ
    obtain ⟨p₁, hp₁, hsp₁⟩ := Finset.mem_image.mp hs
    obtain ⟨p₂, hp₂, htp₂⟩ := Finset.mem_image.mp ht
    have hp₁' :
        p₁ ∈ ConsecutiveCountingA5PureCubicRange.FixedProgressionS
          x D E M ρ₀ C_ratio P Q a b m d₀ e₀ r₀ (J : ℤ) := by
      simpa only [sf, Set.Finite.mem_toFinset] using hp₁
    have hp₂' :
        p₂ ∈ ConsecutiveCountingA5PureCubicRange.FixedProgressionS
          x D E M ρ₀ C_ratio P Q a b m d₀ e₀ r₀ (J : ℤ) := by
      simpa only [sf, Set.Finite.mem_toFinset] using hp₂
    obtain ⟨hrank, hQsign, hKtag⟩ :=
      ConsecutiveCountingA5PureCubicRange.actualBoundaryColour_same_components
        x D E M ρ₀ C_ratio a b c m d₀ e₀ r₀ (J : ℤ) A₀ B₀
        g (1 / 100) s t hcolor
    have hEnd₁ :=
      ConsecutiveCountingA5PureCubicRange.actual_original_point_endpoint_accepted
        x D E M ρ₀ C_ratio P Q a b c m d₀ e₀ r₀ (J : ℤ) A₀ B₀
        hc hm hbez hpure hPnorm hQnorm p₁ hp₁'
    have hEnd₂ :=
      ConsecutiveCountingA5PureCubicRange.actual_original_point_endpoint_accepted
        x D E M ρ₀ C_ratio P Q a b c m d₀ e₀ r₀ (J : ℤ) A₀ B₀
        hc hm hbez hpure hPnorm hQnorm p₂ hp₂'
    rw [hsp₁] at hEnd₁
    rw [htp₂] at hEnd₂
    have hClosed :=
      ConsecutiveCountingA5PureCubicRange.actual_accepted_on_closed_rank_interval
        x D E M ρ₀ C_ratio a b c m d₀ e₀ r₀ (J : ℤ) A₀ B₀
        g (1 / 100) (s : ℝ) (t : ℝ) hstR hrank hEnd₁ hEnd₂
    have hsGap : 1 ≤ |eval (s : ℝ) q| :=
      (hQgap s).resolve_left hsne
    have htGap : 1 ≤ |eval (t : ℝ) q| :=
      (hQgap t).resolve_left htne
    have hQend :
        (1 ≤ eval (s : ℝ) q ∧ 1 ≤ eval (t : ℝ) q) ∨
        (eval (s : ℝ) q ≤ -1 ∧ eval (t : ℝ) q ≤ -1) := by
      by_cases hspos : 0 < eval (s : ℝ) q
      · have htpos : 0 < eval (t : ℝ) q := hQsign.mp hspos
        left
        exact ⟨by simpa only [abs_of_pos hspos] using hsGap,
          by simpa only [abs_of_pos htpos] using htGap⟩
      · have hsnonpos : eval (s : ℝ) q ≤ 0 := le_of_not_gt hspos
        have htnonpos : eval (t : ℝ) q ≤ 0 := by
          apply le_of_not_gt
          intro htpos
          exact hspos (hQsign.mpr htpos)
        rw [abs_of_nonpos hsnonpos] at hsGap
        rw [abs_of_nonpos htnonpos] at htGap
        right
        exact ⟨by linarith only [hsGap], by linarith only [htGap]⟩
    have hQclosed :=
      ConsecutiveCountingA5PureCubicRange.fibre_q_gap_on_actual_closed_rank_interval
        x D E M ρ₀ C_ratio a b c m d₀ e₀ r₀ (J : ℤ) A₀ B₀
        g (1 / 100) (s : ℝ) (t : ℝ) hstR hrank hQend
    have hKend :=
      ConsecutiveCountingA5PureCubicRange.actualKTag_same_endpoint_branch
        K ((1 / 100 : ℝ) * g ^ 2) (s : ℝ) (t : ℝ) hKtag
    have hKclosed :=
      ConsecutiveCountingA5PureCubicRange.actual_K_branch_on_closed_rank_interval
        x D E M ρ₀ C_ratio a b c m d₀ e₀ r₀ (J : ℤ) A₀ B₀
        g (1 / 100) (s : ℝ) (t : ℝ) hstR hrank hKend
    have hThreshold : (1 / 100 : ℝ) * g ^ 2 = g ^ 2 / 100 := by ring
    simp only [hThreshold] at hKclosed
    have hCurv :=
      ConsecutiveCountingA5PureCubicRange.actual_second_derivative_sign_on_rank_interval
        x D E M ρ₀ C_ratio a b c m d₀ e₀ r₀ (J : ℤ) A₀ B₀
        g (1 / 100) (s : ℝ) (t : ℝ) hstR hrank
    have hBranch :
        (∀ z ∈ Set.Icc (s : ℝ) (t : ℝ),
          g ^ 2 / 100 ≤ eval z K) ∨
        (∀ z ∈ Set.Icc (s : ℝ) (t : ℝ),
          eval z K ≤ -(g ^ 2 / 100)) ∨
        ((∀ z ∈ Set.Icc (s : ℝ) (t : ℝ),
          |eval z K| ≤ g ^ 2 / 100) ∧
          ((∀ z ∈ Set.Icc (s : ℝ) (t : ℝ),
            0 ≤ eval z N.derivative.derivative) ∨
          (∀ z ∈ Set.Icc (s : ℝ) (t : ℝ),
            eval z N.derivative.derivative ≤ 0))) := by
      rcases hKclosed with hpos | hneg | hsmall
      · exact Or.inl hpos
      · exact Or.inr (Or.inl hneg)
      · exact Or.inr (Or.inr ⟨hsmall, hCurv⟩)
    have hLength :=
      hPairLength x D E M ρ₀ hx hD hE hM hRange₁ hRange₂
        P Q a b c m d₀ e₀ r₀ (J : ℤ) A₀ B₀
        hab hc hm hJZ hbez hDelta hpure hPnorm hQnorm p₁ p₂ hp₁' hp₂'
    rw [hsp₁, htp₂] at hLength
    have hAbs : |(t : ℝ) - (s : ℝ)| ≤ Cpair * F :=
      hLength hstR.le hI₁ hI₃ hClosed hQclosed hBranch
    rw [abs_of_nonneg (sub_nonneg.mpr hstR.le)] at hAbs
    simpa only [Int.cast_sub] using hAbs
  have hPrice : (T.card : ℝ) ≤ (1272 * Cpair + 1909) * F :=
    ConsecutiveCountingA5PureCubicRange.qzero_good_coloured_uniform_price
      T q color Cpair F hCpair hF (hQzero T) hGoodPair
  have hImageCard :=
    ConsecutiveCountingA5PureCubicRange.fixed_progression_actual_image_card
      x D E M ρ₀ C_ratio P Q a b c m d₀ e₀ r₀ (J : ℤ)
      hc hm hbez hpure
  change sf.card = T.card at hImageCard
  have hSetCoe :
      (↑sf : Set ((ℕ × ℕ) × (ℕ × ℕ))) =
        ConsecutiveCountingA5PureCubicRange.FixedProgressionS
          x D E M ρ₀ C_ratio P Q a b m d₀ e₀ r₀ (J : ℤ) := by
    ext p
    simp only [Finset.mem_coe, sf, Set.Finite.mem_toFinset]
  have hSetCard :
      sf.card =
        (ConsecutiveCountingA5PureCubicRange.FixedProgressionS
          x D E M ρ₀ C_ratio P Q a b m d₀ e₀ r₀ (J : ℤ)).ncard := by
    simpa using congrArg Set.ncard hSetCoe
  calc
    ((ConsecutiveCountingA5PureCubicRange.FixedProgressionS
      x D E M ρ₀ C_ratio P Q a b m d₀ e₀ r₀ (J : ℤ)).ncard : ℝ) =
        (sf.card : ℝ) := by exact_mod_cast hSetCard.symm
    _ = (T.card : ℝ) := by exact_mod_cast hImageCard
    _ ≤ (1272 * Cpair + 1909) * F := hPrice
    _ = Cg * F := rfl

#print axioms claim_fcd806582eb6476367651c9b465c2bcc8589ade4ab91ca64831d3136f30966d6

end JocelynClaims
