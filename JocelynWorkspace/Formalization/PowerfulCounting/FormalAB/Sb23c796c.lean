-- Source SHA-256: 62e95f8e80e47dc265024f168c82e93dbc52fd99f2a967d4814ea58e59f1ae96
import Mathlib
import JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.LemmaP

namespace FormalAB.Sb23c796c

open Classical
open scoped BigOperators

namespace JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.C08.PcPell
open Finset
set_option maxHeartbeats 400000
set_option linter.all false

theorem prod_primeFactors_le_rpow (n : ℕ) (hn : n ≠ 0) (ε : ℝ) (hε : 0 < ε)
    (g : ℕ → ℕ → ℝ) (A : ℝ) (hA : 1 ≤ A) (P : ℕ)
    (hg0 : ∀ p k, 0 ≤ g p k)
    (hgA : ∀ p k, p.Prime → 1 ≤ k → g p k ≤ A * ((p:ℝ) ^ k) ^ ε)
    (hgP : ∀ p k, p.Prime → 1 ≤ k → P ≤ p → g p k ≤ ((p:ℝ) ^ k) ^ ε) :
    ∏ p ∈ n.primeFactors, g p (n.factorization p) ≤ A ^ P * (n:ℝ) ^ ε := by
  classical
  have hloc : ∀ p ∈ n.primeFactors, g p (n.factorization p) ≤
      (if p < P then A else 1) * ((p:ℝ) ^ (n.factorization p)) ^ ε := by
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hk : 1 ≤ n.factorization p := by
      have := Nat.Prime.factorization_pos_of_dvd hpp hn (Nat.dvd_of_mem_primeFactors hp)
      omega
    split_ifs with hlt
    · exact hgA p _ hpp hk
    · rw [one_mul]; exact hgP p _ hpp hk (not_lt.mp hlt)
  have hprodN : ∏ p ∈ n.primeFactors, p ^ n.factorization p = n := by
    have := Nat.factorization_prod_pow_eq_self hn
    rw [Finsupp.prod, Nat.support_factorization] at this
    exact this
  have hprodR : ∏ p ∈ n.primeFactors, ((p:ℝ) ^ (n.factorization p)) = (n:ℝ) := by
    exact_mod_cast hprodN
  calc ∏ p ∈ n.primeFactors, g p (n.factorization p)
      ≤ ∏ p ∈ n.primeFactors, ((if p < P then A else 1) * ((p:ℝ) ^ (n.factorization p)) ^ ε) :=
        Finset.prod_le_prod (fun p _ => hg0 _ _) hloc
    _ = (∏ p ∈ n.primeFactors, (if p < P then A else 1)) *
          ∏ p ∈ n.primeFactors, ((p:ℝ) ^ (n.factorization p)) ^ ε := Finset.prod_mul_distrib
    _ ≤ A ^ P * (n:ℝ) ^ ε := by
        apply mul_le_mul
        · rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
          apply pow_le_pow_right₀ hA
          calc (n.primeFactors.filter (fun p => p < P)).card ≤ (range P).card := by
                apply Finset.card_le_card
                intro p hp
                rw [Finset.mem_filter] at hp
                exact Finset.mem_range.mpr hp.2
            _ = P := Finset.card_range P
        · rw [Real.finset_prod_rpow _ _ (fun p _ => by positivity), hprodR]
        · exact Finset.prod_nonneg (fun p _ => by positivity)
        · have : (0:ℝ) ≤ A := by linarith
          positivity

lemma rpow_natpow_eq (p : ℝ) (hp : 0 ≤ p) (k : ℕ) (ε : ℝ) :
    (p ^ k) ^ ε = (p ^ ε) ^ k := by
  rw [← Real.rpow_natCast p k, ← Real.rpow_mul hp, mul_comm, Real.rpow_mul hp, Real.rpow_natCast]

theorem card_divisors_le_rpow (ε : ℝ) (hε : 0 < ε) : ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 0 < n →
    (n.divisors.card : ℝ) ≤ C * (n:ℝ) ^ ε := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set c : ℝ := ε * Real.log 2 with hc
  have hc0 : 0 < c := mul_pos hε hl2
  set A : ℝ := max 1 (1 / c) with hAdef
  have hA1 : 1 ≤ A := le_max_left _ _
  have hAc : 1 ≤ A * c := by
    have : 1 / c ≤ A := le_max_right _ _
    have := mul_le_mul_of_nonneg_right this hc0.le
    rwa [one_div, inv_mul_cancel₀ hc0.ne'] at this
  set P : ℕ := ⌈(2:ℝ) ^ (1 / ε)⌉₊ with hP
  refine ⟨A ^ P, by positivity, ?_⟩
  intro n hn
  rw [Nat.card_divisors hn.ne']
  push_cast
  apply prod_primeFactors_le_rpow n hn.ne' ε hε (fun p k => (k:ℝ) + 1) A hA1 P
  · intro p k; positivity
  · intro p k hp hk
    have hp2 : (2:ℝ) ≤ p := by exact_mod_cast hp.two_le
    have hpk : ((p:ℝ) ^ k) ^ ε = (p:ℝ) ^ ((k:ℝ) * ε) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    have h2le : (2:ℝ) ^ ((k:ℝ) * ε) ≤ (p:ℝ) ^ ((k:ℝ) * ε) :=
      Real.rpow_le_rpow (by norm_num) hp2 (by positivity)
    have hexp : (2:ℝ) ^ ((k:ℝ) * ε) = Real.exp ((k:ℝ) * c) := by
      rw [Real.rpow_def_of_pos (by norm_num), hc]
      congr 1
      ring
    have hge : (k:ℝ) * c + 1 ≤ Real.exp ((k:ℝ) * c) := Real.add_one_le_exp _
    have hk0 : (0:ℝ) ≤ k := Nat.cast_nonneg k
    show (k:ℝ) + 1 ≤ A * ((p:ℝ) ^ k) ^ ε
    rw [hpk]
    have h1 : (k:ℝ) + 1 ≤ A * ((k:ℝ) * c + 1) := by
      nlinarith [mul_nonneg hk0 (sub_nonneg.mpr hAc)]
    calc (k:ℝ) + 1 ≤ A * ((k:ℝ) * c + 1) := h1
      _ ≤ A * (p:ℝ) ^ ((k:ℝ) * ε) := by
          apply mul_le_mul_of_nonneg_left _ (by linarith)
          linarith
  · intro p k hp hk hPp
    have hp0 : (0:ℝ) ≤ p := Nat.cast_nonneg p
    have hPle : (2:ℝ) ^ (1 / ε) ≤ (p:ℝ) := by
      have h1 : (2:ℝ) ^ (1 / ε) ≤ (P:ℝ) := Nat.le_ceil _
      have h2 : (P:ℝ) ≤ (p:ℝ) := by exact_mod_cast hPp
      linarith
    have hpe : (2:ℝ) ≤ (p:ℝ) ^ ε := by
      have h := Real.rpow_le_rpow (by positivity) hPle hε.le
      rwa [← Real.rpow_mul (by norm_num), one_div, inv_mul_cancel₀ hε.ne', Real.rpow_one] at h
    show (k:ℝ) + 1 ≤ ((p:ℝ) ^ k) ^ ε
    rw [rpow_natpow_eq _ hp0]
    have hk2 : (k:ℝ) + 1 ≤ (2:ℝ) ^ k := by
      have : k + 1 ≤ 2 ^ k := Nat.lt_two_pow_self
      exact_mod_cast this
    calc (k:ℝ) + 1 ≤ (2:ℝ) ^ k := hk2
      _ ≤ ((p:ℝ) ^ ε) ^ k := pow_le_pow_left₀ (by norm_num) hpe k

end JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.C08.PcPell

namespace ConsecutiveCountingA5Analytic
noncomputable section
set_option maxHeartbeats 1000000
set_option linter.all false

noncomputable def densityCoeff : ArithmeticFunction ℝ :=
  ⟨fun n => (ArithmeticFunction.moebius n : ℝ) *
      (n.divisors.card : ℝ) / (n : ℝ) ^ 2, by simp⟩

theorem densityCoeff_multiplicative : densityCoeff.IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  refine ⟨?_, ?_⟩
  · norm_num [densityCoeff]
  · intro m n hm hn hcop
    have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    have hmu := ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop
    have hcard := hcop.card_divisors_mul
    change (ArithmeticFunction.moebius (m * n) : ℝ) *
        ((m * n).divisors.card : ℝ) / ((m * n : ℕ) : ℝ) ^ 2 =
      ((ArithmeticFunction.moebius m : ℝ) *
        (m.divisors.card : ℝ) / (m : ℝ) ^ 2) *
      ((ArithmeticFunction.moebius n : ℝ) *
        (n.divisors.card : ℝ) / (n : ℝ) ^ 2)
    rw [hmu, hcard]
    push_cast
    field_simp [hmR, hnR] <;> ring

theorem prime_pow_divisor_card (p k : ℕ) (hp : p.Prime) :
    (p ^ k).divisors.card = k + 1 := by
  simpa using (Nat.sum_divisors_prime_pow (α := ℕ) (f := fun _ => 1)
    (k := k) hp)

theorem densityCoeff_prime_pow (p k : ℕ) (hp : p.Prime) :
    densityCoeff (p ^ k) =
      if k = 0 then 1 else if k = 1 then -2 / (p : ℝ) ^ 2 else 0 := by
  by_cases hk0 : k = 0
  · subst k
    norm_num [densityCoeff]
  · by_cases hk1 : k = 1
    · subst k
      have hcard : p.divisors.card = 2 := by
        simpa using prime_pow_divisor_card p 1 hp
      simp [densityCoeff, ArithmeticFunction.moebius_apply_prime hp, hcard]
    · simp [densityCoeff, ArithmeticFunction.moebius_apply_prime_pow hp hk0, hk0, hk1]

theorem unitary_moebius_coefficient (n : ℕ) :
    (∑ d ∈ n.divisors,
      if d.Coprime (n / d) then
        ArithmeticFunction.moebius d * ArithmeticFunction.moebius (n / d)
      else 0) =
      ArithmeticFunction.moebius n * (n.divisors.card : ℤ) := by
  calc
    _ = ∑ _d ∈ n.divisors, ArithmeticFunction.moebius n := by
      apply Finset.sum_congr rfl
      intro d hd
      have hdn : d ∣ n := (Nat.mem_divisors.mp hd).1
      have hprod : d * (n / d) = n := Nat.mul_div_cancel' hdn
      by_cases hcop : d.Coprime (n / d)
      · simp only [if_pos hcop]
        simpa only [hprod] using
          (ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop).symm
      · have hns : ¬ Squarefree n := by
          intro hs
          have hs' : Squarefree (d * (n / d)) := by
            simpa only [hprod] using hs
          exact hcop (Nat.squarefree_mul_iff.mp hs').1
        have hzero : ArithmeticFunction.moebius n = 0 := by
          by_contra hmu
          exact hns (ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp hmu)
        simp [hcop, hzero]
    _ = _ := by simp [mul_comm]

theorem densityCoeff_unitary_sum (n : ℕ) :
    densityCoeff n =
      (∑ d ∈ n.divisors,
        if d.Coprime (n / d) then
          ((ArithmeticFunction.moebius d *
            ArithmeticFunction.moebius (n / d) : ℤ) : ℝ)
        else 0) / (n : ℝ) ^ 2 := by
  have h : (∑ d ∈ n.divisors,
      if d.Coprime (n / d) then
        ((ArithmeticFunction.moebius d *
          ArithmeticFunction.moebius (n / d) : ℤ) : ℝ)
      else 0) =
      (ArithmeticFunction.moebius n : ℝ) * (n.divisors.card : ℝ) := by
    exact_mod_cast unitary_moebius_coefficient n
  change (ArithmeticFunction.moebius n : ℝ) *
      (n.divisors.card : ℝ) / (n : ℝ) ^ 2 = _
  rw [h]

theorem densityCoeff_euler_factor (p : Nat.Primes) :
    (∑' k : ℕ, densityCoeff ((p : ℕ) ^ k)) =
      1 - 2 / ((p : ℕ) : ℝ) ^ 2 := by
  have hsupp : ∀ k ∉ ({0, 1} : Finset ℕ),
      densityCoeff ((p : ℕ) ^ k) = 0 := by
    intro k hk
    have hk0 : k ≠ 0 := by
      intro h
      apply hk
      simp [h]
    have hk1 : k ≠ 1 := by
      intro h
      apply hk
      simp [h]
    simp [densityCoeff_prime_pow _ _ p.property, hk0, hk1]
  calc
    _ = ∑ k ∈ ({0, 1} : Finset ℕ), densityCoeff ((p : ℕ) ^ k) :=
      tsum_eq_sum hsupp
    _ = _ := by
      simp [densityCoeff_prime_pow, p.property, sub_eq_add_neg, neg_div]

theorem densityCoeff_euler_product
    (habs : Summable (fun n : ℕ => ‖densityCoeff n‖)) :
    (∏' p : Nat.Primes, (1 - 2 / ((p : ℕ) : ℝ) ^ 2)) =
      ∑' n : ℕ, densityCoeff n := by
  have h := densityCoeff_multiplicative.eulerProduct_tprod habs
  simpa only [densityCoeff_euler_factor] using h

noncomputable def divisorMajorant (δ : ℝ) (n : ℕ) : ℝ :=
  (n.divisors.card : ℝ) / (n : ℝ) ^ (1 + δ)

theorem divisorMajorant_nonneg (δ : ℝ) (n : ℕ) :
    0 ≤ divisorMajorant δ n := by
  unfold divisorMajorant
  positivity

theorem divisorMajorant_summable (δ : ℝ) (hδ : 0 < δ) :
    Summable (fun n : ℕ => divisorMajorant δ n) := by
  obtain ⟨C, hC, hτ⟩ :=
    JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.C08.PcPell.card_divisors_le_rpow
      (δ / 2) (by linarith)
  have hps : Summable (fun n : ℕ => (n : ℝ) ^ (-1 - δ / 2)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have hmajor : Summable (fun n : ℕ => C * (n : ℝ) ^ (-1 - δ / 2)) :=
    hps.mul_left C
  refine hmajor.of_norm_bounded ?_
  intro n
  rw [Real.norm_eq_abs, abs_of_nonneg (divisorMajorant_nonneg δ n)]
  by_cases hn : n = 0
  · subst n
    simp [divisorMajorant] <;> positivity
  · have hnN : 0 < n := Nat.pos_of_ne_zero hn
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hnN
    change (n.divisors.card : ℝ) / (n : ℝ) ^ (1 + δ) ≤ _
    calc
      _ ≤ (C * (n : ℝ) ^ (δ / 2)) / (n : ℝ) ^ (1 + δ) :=
        div_le_div_of_nonneg_right (hτ n hnN) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      _ = C * (n : ℝ) ^ (-1 - δ / 2) := by
        rw [mul_div_assoc, ← Real.rpow_sub hnR]
        congr 1
        congr 1
        ring

theorem densityCoeff_norm_le_majorant (n : ℕ) :
    ‖densityCoeff n‖ ≤ divisorMajorant 1 n := by
  have hμ : |(ArithmeticFunction.moebius n : ℝ)| ≤ 1 := by
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n)
  have hτ : 0 ≤ (n.divisors.card : ℝ) := Nat.cast_nonneg _
  have hsq : 0 ≤ (n : ℝ) ^ 2 := sq_nonneg _
  have hm : divisorMajorant 1 n =
      (n.divisors.card : ℝ) / (n : ℝ) ^ 2 := by
    norm_num [divisorMajorant]
  rw [hm, Real.norm_eq_abs]
  change |(ArithmeticFunction.moebius n : ℝ) *
      (n.divisors.card : ℝ) / (n : ℝ) ^ 2| ≤
    (n.divisors.card : ℝ) / (n : ℝ) ^ 2
  simp only [abs_div, abs_mul, abs_of_nonneg hτ, abs_of_nonneg hsq]
  calc
    _ ≤ (1 : ℝ) * (n.divisors.card : ℝ) / (n : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hμ hτ) hsq
    _ = _ := by rw [one_mul]

theorem densityCoeff_norm_summable :
    Summable (fun n : ℕ => ‖densityCoeff n‖) := by
  have hmajor := divisorMajorant_summable 1 (by norm_num)
  refine hmajor.of_norm_bounded ?_
  intro n
  simpa only [norm_norm] using densityCoeff_norm_le_majorant n

theorem densityCoeff_euler_identity :
    (∏' p : Nat.Primes, (1 - 2 / ((p : ℕ) : ℝ) ^ 2)) =
      ∑' n : ℕ, densityCoeff n :=
  densityCoeff_euler_product densityCoeff_norm_summable

theorem divisor_card_le_cutoff_majorant
    (δ y : ℝ) (hδ : 0 < δ) (n : ℕ)
    (hn : 0 < n) (hny : (n : ℝ) ≤ y) :
    (n.divisors.card : ℝ) ≤ y ^ (1 + δ) * divisorMajorant δ n := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hpow : 0 < (n : ℝ) ^ (1 + δ) := Real.rpow_pos_of_pos hnR _
  have heq : (n.divisors.card : ℝ) =
      (n : ℝ) ^ (1 + δ) * divisorMajorant δ n := by
    unfold divisorMajorant
    field_simp [hpow.ne'] <;> ring
  rw [heq]
  exact mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow hnR.le hny (by linarith))
    (divisorMajorant_nonneg δ n)

theorem densityCoeff_tail_pointwise
    (δ y : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) (hy : 1 ≤ y)
    (n : ℕ) (hyn : y < (n : ℝ)) :
    ‖densityCoeff n‖ ≤ divisorMajorant δ n / y ^ (1 - δ) := by
  have hyR : 0 < y := by linarith
  have hnR : 0 < (n : ℝ) := lt_trans hyR hyn
  have hnpow : 0 < (n : ℝ) ^ (1 - δ) := Real.rpow_pos_of_pos hnR _
  have hypow : 0 < y ^ (1 - δ) := Real.rpow_pos_of_pos hyR _
  have hbase : y ^ (1 - δ) ≤ (n : ℝ) ^ (1 - δ) :=
    Real.rpow_le_rpow hyR.le hyn.le (by linarith)
  have heq : divisorMajorant 1 n =
      divisorMajorant δ n / (n : ℝ) ^ (1 - δ) := by
    unfold divisorMajorant
    rw [div_div, ← Real.rpow_add hnR]
    have hex : (1 + δ) + (1 - δ) = (1 : ℝ) + 1 := by ring
    rw [hex]
  calc
    ‖densityCoeff n‖ ≤ divisorMajorant 1 n :=
      densityCoeff_norm_le_majorant n
    _ = divisorMajorant δ n / (n : ℝ) ^ (1 - δ) := heq
    _ ≤ divisorMajorant δ n / y ^ (1 - δ) :=
      (div_le_div_iff₀ hnpow hypow).mpr
        (mul_le_mul_of_nonneg_left hbase (divisorMajorant_nonneg δ n))

#print axioms divisorMajorant_summable
#print axioms densityCoeff_euler_identity
#print axioms densityCoeff_tail_pointwise

theorem divisor_sum_subpower (η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ y : ℝ, 1 ≤ y →
      (∑ n ∈ Finset.Icc 1 ⌊y⌋₊, (n.divisors.card : ℝ)) ≤
        C * y ^ (1 + η) := by
  obtain ⟨C, hC, hτ⟩ :=
    JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.C08.PcPell.card_divisors_le_rpow
      η hη
  refine ⟨C, hC, ?_⟩
  intro y hy
  have hy0 : 0 < y := by linarith
  have hfloor : (⌊y⌋₊ : ℝ) ≤ y := Nat.floor_le hy0.le
  calc
    _ ≤ ∑ _n ∈ Finset.Icc 1 ⌊y⌋₊, C * y ^ η := by
      apply Finset.sum_le_sum
      intro n hn
      rcases Finset.mem_Icc.mp hn with ⟨hn1, hnN⟩
      have hn0 : 0 < n := by omega
      have hny : (n : ℝ) ≤ y :=
        le_trans (by exact_mod_cast hnN) hfloor
      exact le_trans (hτ n hn0)
        (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (Nat.cast_nonneg _) hny hη.le) hC.le)
    _ = (⌊y⌋₊ : ℝ) * (C * y ^ η) := by simp [Nat.card_Icc, mul_comm]
    _ ≤ y * (C * y ^ η) :=
      mul_le_mul_of_nonneg_right hfloor (by positivity)
    _ = C * y ^ (1 + η) := by
      rw [Real.rpow_add hy0, Real.rpow_one]
      ring

noncomputable def hyperbolaPairs (y : ℝ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc 1 ⌊y⌋₊) ×ˢ (Finset.Icc 1 ⌊y⌋₊)).filter
    (fun p => p.1 * p.2 ≤ ⌊y⌋₊)

noncomputable def positiveDivisorIndex (y : ℝ) : Finset (Σ _ : ℕ, ℕ) :=
  (Finset.Icc 1 ⌊y⌋₊).sigma (fun m => m.divisors)

def productDivisorMap (p : ℕ × ℕ) : Σ _ : ℕ, ℕ :=
  ⟨p.1 * p.2, p.1⟩

theorem hyperbola_card_le_divisor_sum (y : ℝ) :
    (hyperbolaPairs y).card ≤
      ∑ m ∈ Finset.Icc 1 ⌊y⌋₊, m.divisors.card := by
  have hmaps : ∀ p ∈ hyperbolaPairs y,
      productDivisorMap p ∈ positiveDivisorIndex y := by
    intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hp, hprod⟩
    rcases Finset.mem_product.mp hp with ⟨hd, he⟩
    have hd1 : 1 ≤ p.1 := (Finset.mem_Icc.mp hd).1
    have he1 : 1 ≤ p.2 := (Finset.mem_Icc.mp he).1
    have hprod0 : 0 < p.1 * p.2 := Nat.mul_pos (by omega) (by omega)
    apply Finset.mem_sigma.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨hprod0, hprod⟩, ?_⟩
    exact Nat.mem_divisors.mpr ⟨dvd_mul_right _ _, hprod0.ne'⟩
  have hinj : Set.InjOn productDivisorMap (↑(hyperbolaPairs y) : Set (ℕ × ℕ)) := by
    rintro ⟨d, e⟩ hp ⟨f, g⟩ hq h
    have hd : d = f := congrArg (fun z : Σ _ : ℕ, ℕ => z.2) h
    have hprod : d * e = f * g := congrArg Sigma.fst h
    have hmem := (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1
    have hdpos : 0 < d := by
      have h := (Finset.mem_Icc.mp hmem).1
      omega
    subst f
    have he : e = g := mul_left_cancel₀ hdpos.ne' hprod
    subst g
    rfl
  have hsub : (hyperbolaPairs y).image productDivisorMap ⊆ positiveDivisorIndex y := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨p, hp, rfl⟩
    exact hmaps p hp
  calc
    (hyperbolaPairs y).card = ((hyperbolaPairs y).image productDivisorMap).card :=
      (Finset.card_image_of_injOn hinj).symm
    _ ≤ (positiveDivisorIndex y).card := Finset.card_le_card hsub
    _ = _ := by simp only [positiveDivisorIndex, Finset.card_sigma]

theorem hyperbola_subpower (η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ y : ℝ, 1 ≤ y →
      ((hyperbolaPairs y).card : ℝ) ≤ C * y ^ (1 + η) := by
  obtain ⟨C, hC, hsum⟩ := divisor_sum_subpower η hη
  refine ⟨C, hC, ?_⟩
  intro y hy
  have hcard : ((hyperbolaPairs y).card : ℝ) ≤
      ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, (n.divisors.card : ℝ) := by
    exact_mod_cast hyperbola_card_le_divisor_sum y
  exact le_trans hcard (hsum y hy)

#print axioms hyperbola_subpower

#print axioms densityCoeff_multiplicative
#print axioms unitary_moebius_coefficient

end
end ConsecutiveCountingA5Analytic

open Classical
open scoped BigOperators

namespace ConsecutiveCountingA5CRT
noncomputable section
set_option maxHeartbeats 1500000
set_option maxRecDepth 4000
set_option linter.all false

theorem residue_range_sum (N q r : ℕ) (hq : 0 < q) (hr : r < q) :
    (∑ n ∈ Finset.range N, if n % q = r then (1 : ℕ) else 0) =
      N / q + if r < N % q then 1 else 0 := by
  induction N using Nat.strong_induction_on with
  | h N ih =>
    by_cases hN : N < q
    · rw [Nat.div_eq_of_lt hN, Nat.mod_eq_of_lt hN, zero_add]
      calc
        _ = ∑ n ∈ Finset.range N, if n = r then (1 : ℕ) else 0 := by
          apply Finset.sum_congr rfl
          intro n hn
          rw [Nat.mod_eq_of_lt (lt_trans (Finset.mem_range.mp hn) hN)]
        _ = _ := by simp
    · have hqN : q ≤ N := le_of_not_gt hN
      let M := N - q
      have hM : M < N := by dsimp [M]; omega
      have hNM : N = q + M := by dsimp [M]; omega
      have hfirst :
          (∑ n ∈ Finset.range q, if n % q = r then (1 : ℕ) else 0) = 1 := by
        calc
          _ = ∑ n ∈ Finset.range q, if n = r then (1 : ℕ) else 0 := by
            apply Finset.sum_congr rfl
            intro n hn
            rw [Nat.mod_eq_of_lt (Finset.mem_range.mp hn)]
          _ = 1 := by simp [hr]
      have hdiv : (q + M) / q = 1 + M / q := by
        rw [Nat.add_div] <;>
          simp [hq, hq.ne', not_le_of_gt (Nat.mod_lt M hq)]
      calc
        _ = ∑ n ∈ Finset.range (q + M),
            if n % q = r then (1 : ℕ) else 0 := by rw [hNM]
        _ = 1 + ∑ n ∈ Finset.range M,
            if n % q = r then (1 : ℕ) else 0 := by
          rw [Finset.sum_range_add, hfirst]
          congr 1
          apply Finset.sum_congr rfl
          intro n hn
          simp [Nat.add_mod]
        _ = 1 + (M / q + if r < M % q then 1 else 0) := by rw [ih M hM]
        _ = _ := by
          rw [hNM, hdiv]
          simp only [Nat.add_mod, Nat.mod_self, Nat.zero_add, Nat.mod_mod]
          omega

theorem residue_Icc_bounds (N q r : ℕ) (hq : 0 < q) (hr : r < q) :
    N / q ≤ ((Finset.Icc 1 N).filter (fun n => n % q = r)).card ∧
      ((Finset.Icc 1 N).filter (fun n => n % q = r)).card ≤ N / q + 1 := by
  let K : ℕ := ((Finset.Icc 1 N).filter (fun n => n % q = r)).card
  change N / q ≤ K ∧ K ≤ N / q + 1
  let f : ℕ → ℕ := fun n => if n % q = r then 1 else 0
  have hset : Finset.range (N + 1) = insert 0 (Finset.Icc 1 N) := by
    ext n
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  have hsum :
      (∑ n ∈ Finset.range N, f n) + f N =
        f 0 + ∑ n ∈ Finset.Icc 1 N, f n := by
    rw [← Finset.sum_range_succ, hset, Finset.sum_insert]
    simp
  dsimp only [f] at hsum
  rw [residue_range_sum N q r hq hr] at hsum
  have hcard :
      ((Finset.Icc 1 N).filter (fun n => n % q = r)).card =
        ∑ n ∈ Finset.Icc 1 N, if n % q = r then (1 : ℕ) else 0 := by
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [← hcard] at hsum
  simp only [Nat.zero_mod] at hsum
  change N / q + (if r < N % q then 1 else 0) +
      (if N % q = r then 1 else 0) =
    (if (0 : ℕ) = r then 1 else 0) + K at hsum
  by_cases hr0 : r = 0
  · subst r
    by_cases hrem : N % q = 0
    · simp [hrem] at hsum
      omega
    · have hrempos : 0 < N % q := Nat.pos_of_ne_zero hrem
      simp [hrem, hrempos] at hsum
      omega
  · have h0r : (0 : ℕ) ≠ r := Ne.symm hr0
    simp only [if_neg h0r] at hsum
    by_cases hlt : r < N % q
    · have hne : N % q ≠ r := by omega
      simp only [if_pos hlt, if_neg hne] at hsum
      omega
    · by_cases heq : N % q = r
      · simp only [if_neg hlt, if_pos heq] at hsum
        omega
      · simp only [if_neg hlt, if_neg heq] at hsum
        omega

theorem residue_interval_discrepancy
    (x : ℝ) (hx : 0 ≤ x) (q r : ℕ) (hq : 0 < q) (hr : r < q) :
    |(((Finset.Icc 1 ⌊x⌋₊).filter (fun n => n % q = r)).card : ℝ) -
        x / (q : ℝ)| ≤ 1 := by
  let N := ⌊x⌋₊
  let K := ((Finset.Icc 1 N).filter (fun n => n % q = r)).card
  have hK := residue_Icc_bounds N q r hq hr
  have hKlo : ((N / q : ℕ) : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK.1
  have hKhi : (K : ℝ) ≤ ((N / q : ℕ) : ℝ) + 1 := by exact_mod_cast hK.2
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  have hNlo : (N : ℝ) ≤ x := Nat.floor_le hx
  have hNhi : x < (N : ℝ) + 1 := Nat.lt_floor_add_one x
  have hQlo : N / q * q ≤ N := Nat.div_mul_le_self _ _
  have hQhi : N + 1 ≤ (N / q + 1) * q := by
    have hrem := Nat.mod_lt N hq
    have hdecomp := Nat.mod_add_div N q
    nlinarith
  have hQloR : ((N / q : ℕ) : ℝ) * (q : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast hQlo
  have hQhiR : (N : ℝ) + 1 ≤ (((N / q : ℕ) : ℝ) + 1) * (q : ℝ) := by
    exact_mod_cast hQhi
  have hxlo : ((N / q : ℕ) : ℝ) ≤ x / (q : ℝ) :=
    (le_div_iff₀ hqR).mpr (le_trans hQloR hNlo)
  have hxhi : x / (q : ℝ) < ((N / q : ℕ) : ℝ) + 1 :=
    (div_lt_iff₀ hqR).mpr (lt_of_lt_of_le hNhi hQhiR)
  change |(K : ℝ) - x / (q : ℝ)| ≤ 1
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem dvd_succ_iff_mod_pred (n q : ℕ) (hq : 0 < q) :
    q ∣ n + 1 ↔ n % q = q - 1 := by
  have hmodplus : (n + 1) % q = (n % q + 1) % q := by
    simp only [Nat.add_mod, Nat.mod_mod]
  constructor
  · intro hdvd
    have hz : (n % q + 1) % q = 0 := by
      rw [← hmodplus]
      exact Nat.mod_eq_zero_of_dvd hdvd
    have hrem : n % q < q := Nat.mod_lt n hq
    have heq : n % q + 1 = q := by
      by_contra hne
      have hlt : n % q + 1 < q := by omega
      rw [Nat.mod_eq_of_lt hlt] at hz
      omega
    omega
  · intro hrem
    apply Nat.dvd_of_mod_eq_zero
    rw [hmodplus, hrem]
    have heq : q - 1 + 1 = q := by omega
    rw [heq, Nat.mod_self]

theorem coprime_square_interval_discrepancy
    (x : ℝ) (hx : 0 ≤ x) (d e : ℕ)
    (hd : 0 < d) (he : 0 < e) (hcop : d.Coprime e) :
    |(((Finset.Icc 1 ⌊x⌋₊).filter
        (fun n => d ^ 2 ∣ n ∧ e ^ 2 ∣ n + 1)).card : ℝ) -
        x / (((d * e : ℕ) : ℝ) ^ 2)| ≤ 1 := by
  let D := d ^ 2
  let E := e ^ 2
  let q := D * E
  have hD : 0 < D := pow_pos hd 2
  have hE : 0 < E := pow_pos he 2
  have hq : 0 < q := Nat.mul_pos hD hE
  have hcop' : D.Coprime E := Nat.Coprime.pow 2 2 hcop
  let z := Nat.chineseRemainder hcop' 0 (E - 1)
  let r : ℕ := z.val
  have hrD : r % D = 0 := by
    have h := z.property.1
    change r % D = 0 % D at h
    simpa using h
  have hrE : r % E = E - 1 := by
    have h := z.property.2
    change r % E = (E - 1) % E at h
    simpa only [Nat.mod_eq_of_lt (by omega : E - 1 < E)] using h
  have hr : r < q := Nat.chineseRemainder_lt_mul hcop' 0 (E - 1) hD.ne' hE.ne'
  have hpred : ∀ n : ℕ, (D ∣ n ∧ E ∣ n + 1) ↔ n % q = r := by
    intro n
    constructor
    · rintro ⟨hDn, hEn⟩
      have hnd : n ≡ 0 [MOD D] := by
        change n % D = 0 % D
        simpa using Nat.mod_eq_zero_of_dvd hDn
      have hne : n ≡ E - 1 [MOD E] := by
        change n % E = (E - 1) % E
        rw [Nat.mod_eq_of_lt (by omega : E - 1 < E)]
        exact (dvd_succ_iff_mod_pred n E hE).mp hEn
      have h := Nat.chineseRemainder_modEq_unique hcop' hnd hne
      change n % q = r % q at h
      simpa only [Nat.mod_eq_of_lt hr] using h
    · intro hn
      have hnrepr : n = q * (n / q) + r := by
        have h := Nat.mod_add_div n q
        rw [hn] at h
        omega
      have hnD : n % D = r % D := by
        rw [hnrepr]
        dsimp [q]
        simp [Nat.add_mod, Nat.mul_mod, mul_assoc]
      have hnE : n % E = r % E := by
        rw [hnrepr]
        dsimp [q]
        simp [Nat.add_mod, Nat.mul_mod, mul_assoc]
      constructor
      · exact Nat.dvd_of_mod_eq_zero (hnD.trans hrD)
      · exact (dvd_succ_iff_mod_pred n E hE).mpr (hnE.trans hrE)
  have hset :
      ((Finset.Icc 1 ⌊x⌋₊).filter
        (fun n => d ^ 2 ∣ n ∧ e ^ 2 ∣ n + 1)) =
      ((Finset.Icc 1 ⌊x⌋₊).filter (fun n => n % q = r)) := by
    ext n
    simp only [Finset.mem_filter]
    change (n ∈ Finset.Icc 1 ⌊x⌋₊ ∧ (D ∣ n ∧ E ∣ n + 1)) ↔ _
    rw [hpred n]
  have hqR : (q : ℝ) = (((d * e : ℕ) : ℝ) ^ 2) := by
    dsimp [q, D, E]
    push_cast
    ring
  rw [hset]
  simpa only [hqR] using residue_interval_discrepancy x hx q r hq hr

theorem consecutive_square_divisors_coprime (d e n : ℕ)
    (hd : d ^ 2 ∣ n) (he : e ^ 2 ∣ n + 1) : d.Coprime e := by
  have hd' : d ∣ n := dvd_trans
    (by rw [pow_two]; exact dvd_mul_right _ _) hd
  have he' : e ∣ n + 1 := dvd_trans
    (by rw [pow_two]; exact dvd_mul_right _ _) he
  have hcon : n.Coprime (n + 1) := by
    rw [Nat.coprime_self_add_right]
    exact Nat.coprime_one_right _
  exact Nat.Coprime.of_dvd_right he'
    (Nat.Coprime.of_dvd_left hd' hcon)

theorem noncoprime_square_interval_empty
    (x : ℝ) (d e : ℕ) (hcop : ¬ d.Coprime e) :
    ((Finset.Icc 1 ⌊x⌋₊).filter
      (fun n => d ^ 2 ∣ n ∧ e ^ 2 ∣ n + 1)) = ∅ := by
  ext n
  simp only [Finset.mem_filter, Finset.notMem_empty, iff_false]
  rintro ⟨hn, hd, he⟩
  exact hcop (consecutive_square_divisors_coprime d e n hd he)

theorem square_interval_discrepancy
    (x : ℝ) (hx : 0 ≤ x) (d e : ℕ) (hd : 0 < d) (he : 0 < e) :
    |(((Finset.Icc 1 ⌊x⌋₊).filter
        (fun n => d ^ 2 ∣ n ∧ e ^ 2 ∣ n + 1)).card : ℝ) -
      (if d.Coprime e then x / (((d * e : ℕ) : ℝ) ^ 2) else 0)| ≤ 1 := by
  by_cases hcop : d.Coprime e
  · simpa only [if_pos hcop] using
      coprime_square_interval_discrepancy x hx d e hd he hcop
  · rw [noncoprime_square_interval_empty x d e hcop]
    simp [hcop]

#print axioms square_interval_discrepancy

#print axioms residue_range_sum
#print axioms residue_interval_discrepancy
#print axioms coprime_square_interval_discrepancy

end
end ConsecutiveCountingA5CRT

namespace ConsecutiveCountingA5Analytic
noncomputable section
set_option maxHeartbeats 1500000
set_option maxRecDepth 4000
set_option linter.all false

noncomputable def shortPairSumLocal (x y : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
    ∑ d ∈ n.divisors, ∑ e ∈ (n + 1).divisors,
      if d ^ 2 ∣ n ∧ e ^ 2 ∣ n + 1 ∧ ((d * e : ℕ) : ℝ) ≤ y then
        ((ArithmeticFunction.moebius d * ArithmeticFunction.moebius e : ℤ) : ℝ)
      else 0

def mobiusPairWeight (p : ℕ × ℕ) : ℝ :=
  ((ArithmeticFunction.moebius p.1 * ArithmeticFunction.moebius p.2 : ℤ) : ℝ)

theorem hyperbola_sum_reindex (y : ℝ) (f : ℕ × ℕ → ℝ) :
    (∑ p ∈ hyperbolaPairs y, f p) =
      ∑ m ∈ Finset.Icc 1 ⌊y⌋₊, ∑ d ∈ m.divisors, f (d, m / d) := by
  calc
    _ = ∑ t ∈ positiveDivisorIndex y, f (t.2, t.1 / t.2) := by
      refine Finset.sum_bij (fun p _ => productDivisorMap p) ?_ ?_ ?_ ?_
      · intro p hp
        rcases Finset.mem_filter.mp hp with ⟨hp, hprod⟩
        rcases Finset.mem_product.mp hp with ⟨hd, he⟩
        have hd1 : 1 ≤ p.1 := (Finset.mem_Icc.mp hd).1
        have he1 : 1 ≤ p.2 := (Finset.mem_Icc.mp he).1
        have hprod0 : 0 < p.1 * p.2 := Nat.mul_pos (by omega) (by omega)
        apply Finset.mem_sigma.mpr
        refine ⟨Finset.mem_Icc.mpr ⟨hprod0, hprod⟩, ?_⟩
        exact Nat.mem_divisors.mpr ⟨dvd_mul_right _ _, hprod0.ne'⟩
      · rintro ⟨d, e⟩ hp ⟨f, g⟩ hq h
        have hd : d = f := congrArg (fun z : Σ _ : ℕ, ℕ => z.2) h
        have hprod : d * e = f * g := congrArg Sigma.fst h
        have hmem := (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1
        have hdpos : 0 < d := by
          have h : 1 ≤ d := (Finset.mem_Icc.mp hmem).1
          omega
        subst f
        have he : e = g := mul_left_cancel₀ hdpos.ne' hprod
        subst g
        rfl
      · rintro ⟨m, d⟩ ht
        rcases Finset.mem_sigma.mp ht with ⟨hm, hd⟩
        rcases Finset.mem_Icc.mp hm with ⟨hm1, hmN⟩
        dsimp only at hm1 hmN hd
        have hmpos : 0 < m := by omega
        have hdm : d ∣ m := (Nat.mem_divisors.mp hd).1
        have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdm hmpos
        have hdmle : d ≤ m := Nat.le_of_dvd hmpos hdm
        have hepos : 0 < m / d := Nat.div_pos hdmle hdpos
        have hemle : m / d ≤ m := Nat.div_le_self _ _
        have hprod : d * (m / d) = m := Nat.mul_div_cancel' hdm
        have hp : (d, m / d) ∈ hyperbolaPairs y := by
          apply Finset.mem_filter.mpr
          refine ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, ?_⟩
          · exact Finset.mem_Icc.mpr ⟨by omega, le_trans hdmle hmN⟩
          · exact Finset.mem_Icc.mpr ⟨by omega, le_trans hemle hmN⟩
          · simpa only [hprod] using hmN
        refine ⟨(d, m / d), hp, ?_⟩
        change (⟨d * (m / d), d⟩ : Σ _ : ℕ, ℕ) = ⟨m, d⟩
        rw [hprod]
      · rintro ⟨d, e⟩ hp
        have hmem := (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1
        have hdpos : 0 < d := by
          have h : 1 ≤ d := (Finset.mem_Icc.mp hmem).1
          omega
        change f (d, e) = f (d, (d * e) / d)
        rw [Nat.mul_div_cancel_left e hdpos]
    _ = _ := by simp only [positiveDivisorIndex, Finset.sum_sigma]

theorem hyperbola_density_sum (y : ℝ) :
    (∑ p ∈ hyperbolaPairs y,
      if p.1.Coprime p.2 then
        mobiusPairWeight p / (((p.1 * p.2 : ℕ) : ℝ) ^ 2)
      else 0) =
      ∑ m ∈ Finset.Icc 1 ⌊y⌋₊, densityCoeff m := by
  rw [hyperbola_sum_reindex]
  apply Finset.sum_congr rfl
  intro m hm
  calc
    _ = (∑ d ∈ m.divisors,
        if d.Coprime (m / d) then
          ((ArithmeticFunction.moebius d *
            ArithmeticFunction.moebius (m / d) : ℤ) : ℝ)
        else 0) / (m : ℝ) ^ 2 := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro d hd
      have hprod : d * (m / d) = m :=
        Nat.mul_div_cancel' (Nat.mem_divisors.mp hd).1
      change
        (if d.Coprime (m / d) then
          ((ArithmeticFunction.moebius d *
            ArithmeticFunction.moebius (m / d) : ℤ) : ℝ) /
              (((d * (m / d) : ℕ) : ℝ) ^ 2)
        else 0) =
        (if d.Coprime (m / d) then
          ((ArithmeticFunction.moebius d *
            ArithmeticFunction.moebius (m / d) : ℤ) : ℝ)
        else 0) / (m : ℝ) ^ 2
      by_cases hcop : d.Coprime (m / d)
      · simp only [if_pos hcop, hprod]
      · simp only [if_neg hcop, zero_div]
    _ = densityCoeff m := (densityCoeff_unitary_sum m).symm

theorem short_inner_eq_hyperbola
    (n : ℕ) (hn : 0 < n) (y : ℝ) (hy : 1 ≤ y) (w : ℕ × ℕ → ℝ) :
    (∑ d ∈ n.divisors, ∑ e ∈ (n + 1).divisors,
      if d ^ 2 ∣ n ∧ e ^ 2 ∣ n + 1 ∧ ((d * e : ℕ) : ℝ) ≤ y then
        w (d, e) else 0) =
      ∑ p ∈ hyperbolaPairs y,
        if p.1 ^ 2 ∣ n ∧ p.2 ^ 2 ∣ n + 1 then w p else 0 := by
  let s := (n.divisors ×ˢ (n + 1).divisors).filter (fun p =>
    p.1 ^ 2 ∣ n ∧ p.2 ^ 2 ∣ n + 1 ∧ ((p.1 * p.2 : ℕ) : ℝ) ≤ y)
  let t := (hyperbolaPairs y).filter (fun p =>
    p.1 ^ 2 ∣ n ∧ p.2 ^ 2 ∣ n + 1)
  have hst : s = t := by
    ext p
    constructor
    · intro hp
      rcases Finset.mem_filter.mp hp with ⟨hp, hd₂, he₂, hprod⟩
      rcases Finset.mem_product.mp hp with ⟨hd, he⟩
      have hdpos : 0 < p.1 :=
        Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp hd).1 hn
      have hepos : 0 < p.2 :=
        Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp he).1 (by omega)
      have hprodN : p.1 * p.2 ≤ ⌊y⌋₊ := Nat.le_floor hprod
      have hdle : p.1 ≤ p.1 * p.2 := Nat.le_mul_of_pos_right _ hepos
      have hele : p.2 ≤ p.1 * p.2 := Nat.le_mul_of_pos_left _ hdpos
      apply Finset.mem_filter.mpr
      refine ⟨?_, hd₂, he₂⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, hprodN⟩
      · exact Finset.mem_Icc.mpr ⟨by omega, le_trans hdle hprodN⟩
      · exact Finset.mem_Icc.mpr ⟨by omega, le_trans hele hprodN⟩
    · intro hp
      rcases Finset.mem_filter.mp hp with ⟨hp, hd₂, he₂⟩
      rcases Finset.mem_filter.mp hp with ⟨hpbox, hprod⟩
      have hd : p.1 ∣ n := dvd_trans
        (by rw [pow_two]; exact dvd_mul_right _ _) hd₂
      have he : p.2 ∣ n + 1 := dvd_trans
        (by rw [pow_two]; exact dvd_mul_right _ _) he₂
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_product.mpr
        ⟨Nat.mem_divisors.mpr ⟨hd, hn.ne'⟩,
         Nat.mem_divisors.mpr ⟨he, by omega⟩⟩, hd₂, he₂, ?_⟩
      exact le_trans (by exact_mod_cast hprod)
        (Nat.floor_le (by linarith : 0 ≤ y))
  calc
    _ = ∑ p ∈ n.divisors ×ˢ (n + 1).divisors,
        if p.1 ^ 2 ∣ n ∧ p.2 ^ 2 ∣ n + 1 ∧ ((p.1 * p.2 : ℕ) : ℝ) ≤ y then
          w p else 0 := by rw [Finset.sum_product]
    _ = ∑ p ∈ s, w p := by
      symm
      exact Finset.sum_filter _ _
    _ = ∑ p ∈ t, w p := by rw [hst]
    _ = _ := Finset.sum_filter _ _

theorem shortPairSum_hyperbola (x y : ℝ) (hy : 1 ≤ y) :
    shortPairSumLocal x y =
      ∑ p ∈ hyperbolaPairs y, mobiusPairWeight p *
        (((Finset.Icc 1 ⌊x⌋₊).filter
          (fun n => p.1 ^ 2 ∣ n ∧ p.2 ^ 2 ∣ n + 1)).card : ℝ) := by
  unfold shortPairSumLocal
  calc
    _ = ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ∑ p ∈ hyperbolaPairs y,
        if p.1 ^ 2 ∣ n ∧ p.2 ^ 2 ∣ n + 1 then mobiusPairWeight p else 0 := by
      apply Finset.sum_congr rfl
      intro n hn
      exact short_inner_eq_hyperbola n
        (by have h := (Finset.mem_Icc.mp hn).1; omega) y hy mobiusPairWeight
    _ = ∑ p ∈ hyperbolaPairs y, ∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
        if p.1 ^ 2 ∣ n ∧ p.2 ^ 2 ∣ n + 1 then mobiusPairWeight p else 0 := by
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro p hp
      calc
        _ = ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, mobiusPairWeight p *
            (if p.1 ^ 2 ∣ n ∧ p.2 ^ 2 ∣ n + 1 then (1 : ℝ) else 0) := by
          apply Finset.sum_congr rfl
          intro n hn
          by_cases h : p.1 ^ 2 ∣ n ∧ p.2 ^ 2 ∣ n + 1 <;> simp [h]
        _ = mobiusPairWeight p *
            ∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
              if p.1 ^ 2 ∣ n ∧ p.2 ^ 2 ∣ n + 1 then (1 : ℝ) else 0 := by
          rw [Finset.mul_sum]
        _ = _ := by
          congr 1
          exact_mod_cast (Finset.card_filter
            (fun n => p.1 ^ 2 ∣ n ∧ p.2 ^ 2 ∣ n + 1)
            (Finset.Icc 1 ⌊x⌋₊)).symm

theorem mobiusPairWeight_abs_le (p : ℕ × ℕ) :
    |mobiusPairWeight p| ≤ 1 := by
  have hd : |(ArithmeticFunction.moebius p.1 : ℝ)| ≤ 1 := by
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := p.1)
  have he : |(ArithmeticFunction.moebius p.2 : ℝ)| ≤ 1 := by
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := p.2)
  simp only [mobiusPairWeight, Int.cast_mul, abs_mul]
  simpa using mul_le_mul hd he (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)

theorem shortPairSum_finite_error
    (x y : ℝ) (hx : 0 ≤ x) (hy : 1 ≤ y) :
    |shortPairSumLocal x y -
      x * (∑ m ∈ Finset.Icc 1 ⌊y⌋₊, densityCoeff m)| ≤
        ((hyperbolaPairs y).card : ℝ) := by
  have hmain :
      x * (∑ m ∈ Finset.Icc 1 ⌊y⌋₊, densityCoeff m) =
        ∑ p ∈ hyperbolaPairs y, mobiusPairWeight p *
          (if p.1.Coprime p.2 then
            x / (((p.1 * p.2 : ℕ) : ℝ) ^ 2) else 0) := by
    rw [← hyperbola_density_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    by_cases hcop : p.1.Coprime p.2 <;> simp [hcop] <;> ring
  have herr :
      shortPairSumLocal x y -
        x * (∑ m ∈ Finset.Icc 1 ⌊y⌋₊, densityCoeff m) =
      ∑ p ∈ hyperbolaPairs y, mobiusPairWeight p *
        ((((Finset.Icc 1 ⌊x⌋₊).filter
            (fun n => p.1 ^ 2 ∣ n ∧ p.2 ^ 2 ∣ n + 1)).card : ℝ) -
          (if p.1.Coprime p.2 then
            x / (((p.1 * p.2 : ℕ) : ℝ) ^ 2) else 0)) := by
    rw [shortPairSum_hyperbola x y hy, hmain, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro p hp
    ring
  rw [herr]
  calc
    _ ≤ ∑ p ∈ hyperbolaPairs y,
        |mobiusPairWeight p *
          ((((Finset.Icc 1 ⌊x⌋₊).filter
              (fun n => p.1 ^ 2 ∣ n ∧ p.2 ^ 2 ∣ n + 1)).card : ℝ) -
            (if p.1.Coprime p.2 then
              x / (((p.1 * p.2 : ℕ) : ℝ) ^ 2) else 0))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _p ∈ hyperbolaPairs y, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro p hp
      have hpbox := (Finset.mem_filter.mp hp).1
      have hd : 0 < p.1 := by
        have h := (Finset.mem_Icc.mp (Finset.mem_product.mp hpbox).1).1
        omega
      have he : 0 < p.2 := by
        have h := (Finset.mem_Icc.mp (Finset.mem_product.mp hpbox).2).1
        omega
      have hc := ConsecutiveCountingA5CRT.square_interval_discrepancy
        x hx p.1 p.2 hd he
      rw [abs_mul]
      simpa using mul_le_mul (mobiusPairWeight_abs_le p) hc
        (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
    _ = _ := by simp

#print axioms hyperbola_sum_reindex
#print axioms shortPairSum_hyperbola
#print axioms shortPairSum_finite_error

end
end ConsecutiveCountingA5Analytic

namespace ConsecutiveCountingA5Analytic
noncomputable section
set_option maxHeartbeats 1500000
set_option maxRecDepth 4000
set_option linter.all false

noncomputable def finiteDensityPart (y : ℝ) (n : ℕ) : ℝ :=
  if n ∈ Finset.Icc 1 ⌊y⌋₊ then densityCoeff n else 0

theorem densityCoeff_tail_sum
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) (y : ℝ) (hy : 1 ≤ y) :
    |(∑' n : ℕ, densityCoeff n) -
        (∑ n ∈ Finset.Icc 1 ⌊y⌋₊, densityCoeff n)| ≤
      (∑' n : ℕ, divisorMajorant δ n) / y ^ (1 - δ) := by
  have ha : Summable (fun n : ℕ => densityCoeff n) :=
    densityCoeff_norm_summable.of_norm
  have hsmall : Summable (fun n : ℕ => finiteDensityPart y n) := by
    refine densityCoeff_norm_summable.of_norm_bounded ?_
    intro n
    by_cases hn : n ∈ Finset.Icc 1 ⌊y⌋₊ <;>
      simp [finiteDensityPart, hn]
  have htail := ha.sub hsmall
  have htailnorm : Summable
      (fun n : ℕ => ‖densityCoeff n - finiteDensityPart y n‖) := by
    refine densityCoeff_norm_summable.of_norm_bounded ?_
    intro n
    by_cases hn : n ∈ Finset.Icc 1 ⌊y⌋₊ <;>
      simp [finiteDensityPart, hn]
  have hsmalltsum :
      (∑' n : ℕ, finiteDensityPart y n) =
        ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, densityCoeff n := by
    calc
      _ = ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, finiteDensityPart y n :=
        tsum_eq_sum (fun n hn => by simp [finiteDensityPart, hn])
      _ = _ := by
        apply Finset.sum_congr rfl
        intro n hn
        simp [finiteDensityPart, hn]
  have htailtsum :
      (∑' n : ℕ, densityCoeff n) -
          (∑ n ∈ Finset.Icc 1 ⌊y⌋₊, densityCoeff n) =
        ∑' n : ℕ, (densityCoeff n - finiteDensityPart y n) := by
    rw [ha.tsum_sub hsmall, hsmalltsum]
  have hbound : ∀ n : ℕ,
      ‖densityCoeff n - finiteDensityPart y n‖ ≤
        divisorMajorant δ n / y ^ (1 - δ) := by
    intro n
    by_cases hn : n ∈ Finset.Icc 1 ⌊y⌋₊
    · simp only [finiteDensityPart, if_pos hn, sub_self, norm_zero]
      exact div_nonneg (divisorMajorant_nonneg δ n)
        (Real.rpow_nonneg (by linarith : 0 ≤ y) _)
    · by_cases hn0 : n = 0
      · subst n
        simp [densityCoeff, finiteDensityPart, divisorMajorant]
      · have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
        have hnot : ¬ n ≤ ⌊y⌋₊ := by
          intro hN
          exact hn (Finset.mem_Icc.mpr ⟨by omega, hN⟩)
        have hyn : y < (n : ℝ) := lt_of_not_ge (fun h => hnot (Nat.le_floor h))
        simpa only [finiteDensityPart, if_neg hn, sub_zero] using
          densityCoeff_tail_pointwise δ y hδ hδ1 hy n hyn
  have hmajor := (divisorMajorant_summable δ hδ).div_const (y ^ (1 - δ))
  calc
    _ = ‖∑' n : ℕ, (densityCoeff n - finiteDensityPart y n)‖ := by
      rw [htailtsum, Real.norm_eq_abs]
    _ ≤ ∑' n : ℕ, ‖densityCoeff n - finiteDensityPart y n‖ :=
      norm_tsum_le_tsum_norm htailnorm
    _ ≤ ∑' n : ℕ, divisorMajorant δ n / y ^ (1 - δ) :=
      by
        first
        | exact htailnorm.tsum_le_tsum hbound hmajor
        | exact Summable.tsum_le_tsum hbound htailnorm hmajor
    _ = _ := by rw [tsum_div_const]

theorem short_pair_sqrt_local :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 2 ≤ x →
      |shortPairSumLocal x (Real.sqrt x) -
        x * (∏' p : Nat.Primes, (1 - 2 / ((p : ℕ) : ℝ) ^ 2))| ≤
          C * x ^ ((1 : ℝ) / 2 + ε) := by
  intro ε hε
  let δ : ℝ := min ε ((1 : ℝ) / 2)
  have hδ : 0 < δ := lt_min hε (by norm_num)
  have hδε : δ ≤ ε := min_le_left _ _
  have hδhalf : δ ≤ (1 : ℝ) / 2 := min_le_right _ _
  have hδ1 : δ < 1 := by linarith
  obtain ⟨C0, hC0, hP⟩ := hyperbola_subpower (δ / 2) (by linarith)
  let W : ℝ := ∑' n : ℕ, divisorMajorant δ n
  have hW : 0 ≤ W := tsum_nonneg (divisorMajorant_nonneg δ)
  refine ⟨C0 + W, add_nonneg hC0.le hW, ?_⟩
  intro x hx
  have hxpos : 0 < x := by linarith
  have hx0 : 0 ≤ x := hxpos.le
  have hx1 : 1 ≤ x := by linarith
  have hy0 : 0 ≤ Real.sqrt x := Real.sqrt_nonneg _
  have hysq : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt hx0
  have hy : 1 ≤ Real.sqrt x := by nlinarith
  let A : ℝ := ∑ n ∈ Finset.Icc 1 ⌊Real.sqrt x⌋₊, densityCoeff n
  have herr :
      |shortPairSumLocal x (Real.sqrt x) - x * A| ≤
        ((hyperbolaPairs (Real.sqrt x)).card : ℝ) := by
    simpa only [A] using shortPairSum_finite_error x (Real.sqrt x) hx0 hy
  have htail :
      |(∑' n : ℕ, densityCoeff n) - A| ≤
        W / (Real.sqrt x) ^ (1 - δ) := by
    simpa only [A, W] using densityCoeff_tail_sum δ hδ hδ1 (Real.sqrt x) hy
  have hsmall := hP (Real.sqrt x) hy
  have habsolute :
      |shortPairSumLocal x (Real.sqrt x) -
        x * (∑' n : ℕ, densityCoeff n)| ≤
        C0 * (Real.sqrt x) ^ (1 + δ / 2) +
          x * (W / (Real.sqrt x) ^ (1 - δ)) := by
    calc
      _ = |(shortPairSumLocal x (Real.sqrt x) - x * A) +
          x * (A - (∑' n : ℕ, densityCoeff n))| := by
        congr 1
        ring
      _ ≤ |shortPairSumLocal x (Real.sqrt x) - x * A| +
          |x * (A - (∑' n : ℕ, densityCoeff n))| := abs_add_le _ _
      _ = |shortPairSumLocal x (Real.sqrt x) - x * A| +
          x * |(∑' n : ℕ, densityCoeff n) - A| := by
        rw [abs_mul, abs_of_nonneg hx0, abs_sub_comm A (∑' n : ℕ, densityCoeff n)]
      _ ≤ _ := add_le_add (le_trans herr hsmall)
        (mul_le_mul_of_nonneg_left htail hx0)
  have hpowS :
      (Real.sqrt x) ^ (1 + δ / 2) =
        x ^ ((1 : ℝ) / 2 + δ / 4) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hx0]
    congr 1
    ring
  have hpowT :
      x / (Real.sqrt x) ^ (1 - δ) =
        x ^ ((1 : ℝ) / 2 + δ / 2) := by
    calc
      _ = x ^ (1 : ℝ) / x ^ ((1 - δ) / 2) := by
        rw [Real.rpow_one]
        congr 1
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hx0]
        congr 1
        ring
      _ = x ^ (1 - (1 - δ) / 2) := by rw [Real.rpow_sub hxpos]
      _ = _ := by congr 1; ring
  have hsmallpow :
      x ^ ((1 : ℝ) / 2 + δ / 4) ≤ x ^ ((1 : ℝ) / 2 + ε) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have htailpow :
      x ^ ((1 : ℝ) / 2 + δ / 2) ≤ x ^ ((1 : ℝ) / 2 + ε) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  rw [densityCoeff_euler_identity]
  calc
    _ ≤ C0 * (Real.sqrt x) ^ (1 + δ / 2) +
          x * (W / (Real.sqrt x) ^ (1 - δ)) := habsolute
    _ = C0 * (Real.sqrt x) ^ (1 + δ / 2) +
          W * (x / (Real.sqrt x) ^ (1 - δ)) := by ring
    _ = C0 * x ^ ((1 : ℝ) / 2 + δ / 4) +
          W * x ^ ((1 : ℝ) / 2 + δ / 2) := by rw [hpowS, hpowT]
    _ ≤ C0 * x ^ ((1 : ℝ) / 2 + ε) +
          W * x ^ ((1 : ℝ) / 2 + ε) :=
      add_le_add (mul_le_mul_of_nonneg_left hsmallpow hC0.le)
        (mul_le_mul_of_nonneg_left htailpow hW)
    _ = (C0 + W) * x ^ ((1 : ℝ) / 2 + ε) := by ring

#print axioms densityCoeff_tail_sum
#print axioms short_pair_sqrt_local

end
end ConsecutiveCountingA5Analytic

namespace ConsecutiveCountingA5Source
noncomputable section

def pairDensity (k : ℕ) : ℝ :=
  ∏' p : Nat.Primes, (1 - 2 / ((p : ℕ) : ℝ) ^ k)

noncomputable def shortPairSum (x y : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
    ∑ d ∈ n.divisors, ∑ e ∈ (n + 1).divisors,
      if d ^ 2 ∣ n ∧ e ^ 2 ∣ n + 1 ∧ ((d * e : ℕ) : ℝ) ≤ y then
        ((ArithmeticFunction.moebius d * ArithmeticFunction.moebius e : ℤ) : ℝ)
      else 0

theorem short_pair_sqrt_error :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 2 ≤ x →
      |shortPairSum x (Real.sqrt x) - x * pairDensity 2| ≤
        C * x ^ ((1 : ℝ) / 2 + ε) := by
  simpa only [shortPairSum, pairDensity,
    ConsecutiveCountingA5Analytic.shortPairSumLocal] using
      ConsecutiveCountingA5Analytic.short_pair_sqrt_local

#print axioms short_pair_sqrt_error

end
end ConsecutiveCountingA5Source

namespace JocelynClaims
 theorem claim_61abb56d777f10b8c4c7fb56cb439980c51b50b31e1f22ff1783b1eadefdfeda : let pairDensity : ℕ → ℝ := fun k => tprod (fun p : Nat.Primes => (1 - 2 / ((p : ℕ) : ℝ) ^ k)); let shortPairSum : ℝ → ℝ → ℝ := fun x y => Finset.sum (Finset.Icc 1 ⌊x⌋₊) (fun n => Finset.sum n.divisors (fun d => Finset.sum (n + 1).divisors (fun e => if d ^ 2 ∣ n ∧ e ^ 2 ∣ n + 1 ∧ ((d * e : ℕ) : ℝ) ≤ y then ((ArithmeticFunction.moebius d * ArithmeticFunction.moebius e : ℤ) : ℝ) else 0))); ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 2 ≤ x → |shortPairSum x (Real.sqrt x) - x * pairDensity 2| ≤ C * x ^ ((1 : ℝ) / 2 + ε) := by
  exact ConsecutiveCountingA5Source.short_pair_sqrt_error
end JocelynClaims
#print axioms JocelynClaims.claim_61abb56d777f10b8c4c7fb56cb439980c51b50b31e1f22ff1783b1eadefdfeda
