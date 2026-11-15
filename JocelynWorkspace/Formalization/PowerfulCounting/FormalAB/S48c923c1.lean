-- Source SHA-256: 74648c7034eb1dafdff0d0887a61fe5b3032fdb81d9a36098118619821b01f1f
import Mathlib
import JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.LemmaP
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB

namespace FormalAB.S48c923c1

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
