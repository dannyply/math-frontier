-- Source SHA-256: 377606d453c0c697564fdbd80dfb3bb86c7863f53fe768ea6bbefd7e318c38aa
import Mathlib
import JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.LemmaP
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB

namespace FormalAB.S2b84589f

open scoped BigOperators
namespace A5SignedLevelBudgetArithmetic
set_option maxHeartbeats 1200000

theorem denominator_primeFactors_subset (A D n : ℕ)
    (hAD : A * D ≠ 0) (hn : n ∣ D) :
    (A * n ^ 5).primeFactors ⊆ (A * D).primeFactors := by
  intro p hp
  obtain ⟨hpp, hpd, _⟩ := Nat.mem_primeFactors.mp hp
  have hpAD : p ∣ A * D := by
    rcases hpp.dvd_mul.mp hpd with hpa | hpn
    · exact dvd_mul_of_dvd_left hpa D
    · have hpn' : p ∣ n := hpp.dvd_of_dvd_pow hpn
      exact dvd_mul_of_dvd_right (dvd_trans hpn' hn) A
  exact Nat.mem_primeFactors.mpr ⟨hpp, hpAD, hAD⟩

theorem weighted_divisor_sum (A D : ℕ) (hAD : A * D ≠ 0)
    (hTwo : 2 ^ (A * D).primeFactors.card ≤ (A * D).divisors.card) :
    (∑ n ∈ D.divisors, (6 : ℝ) ^ ((A * n ^ 5).primeFactors.card)) ≤
      (D.divisors.card : ℝ) * ((A * D).divisors.card : ℝ) ^ 3 := by
  have hterm (n : ℕ) (hn : n ∈ D.divisors) :
      (6 : ℝ) ^ ((A * n ^ 5).primeFactors.card) ≤
        ((A * D).divisors.card : ℝ) ^ 3 := by
    have hcard := Finset.card_le_card
      (denominator_primeFactors_subset A D n hAD (Nat.mem_divisors.mp hn).1)
    have hbase : (6 : ℝ) ^ ((A * n ^ 5).primeFactors.card) ≤
        (8 : ℝ) ^ ((A * n ^ 5).primeFactors.card) := by
      gcongr ; norm_num
    have hexp : (8 : ℝ) ^ ((A * n ^ 5).primeFactors.card) ≤
        (8 : ℝ) ^ ((A * D).primeFactors.card) := by
      gcongr ; first | exact hcard | norm_num
    have heq : (8 : ℝ) ^ ((A * D).primeFactors.card) =
        ((2 : ℝ) ^ ((A * D).primeFactors.card)) ^ 3 := by
      calc
        _ = ((2 : ℝ) ^ 3) ^ ((A * D).primeFactors.card) := by norm_num
        _ = _ := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    have hTwoR : (2 : ℝ) ^ ((A * D).primeFactors.card) ≤
        ((A * D).divisors.card : ℝ) := by exact_mod_cast hTwo
    have hcubed : ((2 : ℝ) ^ ((A * D).primeFactors.card)) ^ 3 ≤
        ((A * D).divisors.card : ℝ) ^ 3 := by
      gcongr
    exact hbase.trans (hexp.trans (heq.le.trans hcubed))
  calc
    _ ≤ ∑ _n ∈ D.divisors, ((A * D).divisors.card : ℝ) ^ 3 :=
      Finset.sum_le_sum hterm
    _ = _ := by simp

theorem fourth_common_rpow (H δ : ℝ) (hH : 0 ≤ H) :
    ((20 * H ^ 9) ^ δ) ^ 4 = 20 ^ (4 * δ) * H ^ (36 * δ) := by
  have fourth (z : ℝ) (hz : 0 ≤ z) :
      (z ^ δ) ^ 4 = z ^ (4 * δ) := by
    calc
      _ = (z ^ δ) ^ (4 : ℝ) := (Real.rpow_natCast (z ^ δ) 4).symm
      _ = z ^ (δ * 4) := (Real.rpow_mul hz δ 4).symm
      _ = _ := by congr 1; ring
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 20) (pow_nonneg hH 9), mul_pow]
  rw [fourth 20 (by norm_num), fourth (H ^ 9) (pow_nonneg hH 9)]
  congr 1
  calc
    (H ^ 9) ^ (4 * δ) = (H ^ (9 : ℝ)) ^ (4 * δ) := congrArg (fun z : ℝ => z ^ (4 * δ)) (Real.rpow_natCast H 9).symm
    _ = H ^ ((9 : ℝ) * (4 * δ)) := (Real.rpow_mul hH 9 (4 * δ)).symm
    _ = _ := by congr 1; ring

#print axioms denominator_primeFactors_subset
#print axioms weighted_divisor_sum
#print axioms fourth_common_rpow
theorem budget_of_divisor_bounds
    (hTwo : ∀ n : ℕ, n ≠ 0 → 2 ^ n.primeFactors.card ≤ n.divisors.card)
    (hDiv : ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, 1 ≤ C ∧
      ∀ n : ℕ, n ≠ 0 → (n.divisors.card : ℝ) ≤ C * (n : ℝ) ^ δ) :
∀ ε : ℝ, 0 < ε →
  ∃ C : ℝ, 1 ≤ C ∧
    ∀ H : ℝ, 1 ≤ H →
      ∀ c Δ : ℤ, c ≠ 0 → Δ ≠ 0 →
        |(c : ℝ)| ≤ H →
        |(Δ : ℝ)| ≤ 20 * H ^ 8 →
        2 * (∑ n ∈ Δ.natAbs.divisors,
          (6 : ℝ) ^ ((c.natAbs * n ^ 5).primeFactors.card)) ≤
          C * H ^ ε
 := by
  intro ε hε
  let δ : ℝ := ε / 36
  have hδ : 0 < δ := div_pos hε (by norm_num)
  obtain ⟨C₀, hC₀, hDiv₀⟩ := hDiv δ hδ
  let B : ℝ := 2 * C₀ ^ 4 * 20 ^ (4 * δ)
  refine ⟨max 1 B, le_max_left 1 B, ?_⟩
  intro H hH c Δ hc hΔ hcH hΔH
  let A : ℕ := c.natAbs
  let D : ℕ := Δ.natAbs
  have hA : A ≠ 0 := ne_of_gt (Int.natAbs_pos.mpr hc)
  have hD : D ≠ 0 := ne_of_gt (Int.natAbs_pos.mpr hΔ)
  have hAD : A * D ≠ 0 := mul_ne_zero hA hD
  have hAc : (A : ℝ) = |(c : ℝ)| := by
    dsimp [A]
    have h := congrArg (fun z : ℤ => (z : ℝ)) (Int.natCast_natAbs c)
    simpa only [Int.cast_natCast, Int.cast_abs] using h
  have hDc : (D : ℝ) = |(Δ : ℝ)| := by
    dsimp [D]
    have h := congrArg (fun z : ℤ => (z : ℝ)) (Int.natCast_natAbs Δ)
    simpa only [Int.cast_natCast, Int.cast_abs] using h
  have hAH : (A : ℝ) ≤ H := by rw [hAc]; exact hcH
  have hDH : (D : ℝ) ≤ 20 * H ^ 8 := by rw [hDc]; exact hΔH
  have hH₀ : 0 ≤ H := by linarith
  have hHpos : 0 < H := by linarith
  have hH89 : H ^ 8 ≤ H ^ 9 := by
    have hh := mul_nonneg (pow_nonneg hH₀ 8) (by linarith : 0 ≤ H - 1)
    nlinarith only [hh]
  let Z : ℝ := 20 * H ^ 9
  have hZpos : 0 < Z := by dsimp [Z]; positivity
  have hDZ : (D : ℝ) ≤ Z := by
    dsimp [Z]
    nlinarith only [hDH, hH89]
  have hADZ : ((A * D : ℕ) : ℝ) ≤ Z := by
    push_cast
    calc
      (A : ℝ) * (D : ℝ) ≤ H * (20 * H ^ 8) :=
        mul_le_mul hAH hDH (Nat.cast_nonneg D) hH₀
      _ = Z := by dsimp [Z]; ring
  have hC₀₀ : 0 ≤ C₀ := by linarith
  let U : ℝ := C₀ * Z ^ δ
  have hU₀ : 0 ≤ U :=
    mul_nonneg hC₀₀ (le_of_lt (Real.rpow_pos_of_pos hZpos δ))
  have hτD : (D.divisors.card : ℝ) ≤ U := by
    calc
      _ ≤ C₀ * (D : ℝ) ^ δ := hDiv₀ D hD
      _ ≤ U := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg D) hDZ hδ.le) hC₀₀
  have hτAD : ((A * D).divisors.card : ℝ) ≤ U := by
    calc
      _ ≤ C₀ * ((A * D : ℕ) : ℝ) ^ δ := hDiv₀ (A * D) hAD
      _ ≤ U := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg (A * D)) hADZ hδ.le) hC₀₀
  have hτAD3 : ((A * D).divisors.card : ℝ) ^ 3 ≤ U ^ 3 := by
    gcongr
  have hproduct : (D.divisors.card : ℝ) *
      ((A * D).divisors.card : ℝ) ^ 3 ≤ U ^ 4 := by
    calc
      _ ≤ U * U ^ 3 :=
        mul_le_mul hτD hτAD3 (by positivity) hU₀
      _ = U ^ 4 := by ring
  have hsum := weighted_divisor_sum A D hAD (hTwo (A * D) hAD)
  have hleft : 2 * (∑ n ∈ D.divisors,
      (6 : ℝ) ^ ((A * n ^ 5).primeFactors.card)) ≤ 2 * U ^ 4 :=
    mul_le_mul_of_nonneg_left (hsum.trans hproduct) (by norm_num)
  have hnormal : 2 * U ^ 4 = B * H ^ ε := by
    dsimp [U, Z, B]
    rw [mul_pow, fourth_common_rpow H δ hH₀]
    have he : 36 * δ = ε := by dsimp [δ]; ring
    rw [he]
    ring
  have hmax : B * H ^ ε ≤ max 1 B * H ^ ε :=
    mul_le_mul_of_nonneg_right (le_max_right 1 B)
      (le_of_lt (Real.rpow_pos_of_pos hHpos ε))
  exact hleft.trans (hnormal.le.trans hmax)

#print axioms budget_of_divisor_bounds

end A5SignedLevelBudgetArithmetic

namespace JocelynClaims
theorem claim_e20043e877cc7f6fa915f18cc7590809a6d647a0fe0e66aac9caa124288a4f2a :
∀ ε : ℝ, 0 < ε →
  ∃ C : ℝ, 1 ≤ C ∧
    ∀ H : ℝ, 1 ≤ H →
      ∀ c Δ : ℤ, c ≠ 0 → Δ ≠ 0 →
        |(c : ℝ)| ≤ H →
        |(Δ : ℝ)| ≤ 20 * H ^ 8 →
        2 * (∑ n ∈ Δ.natAbs.divisors,
          (6 : ℝ) ^ ((c.natAbs * n ^ 5).primeFactors.card)) ≤
          C * H ^ ε
 := by
  exact A5SignedLevelBudgetArithmetic.budget_of_divisor_bounds
    JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.C01.PcLowdegRed.two_pow_card_primeFactors_le
    JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.C01.PcLowdegRed.divisor_bound
end JocelynClaims
#print axioms JocelynClaims.claim_e20043e877cc7f6fa915f18cc7590809a6d647a0fe0e66aac9caa124288a4f2a
