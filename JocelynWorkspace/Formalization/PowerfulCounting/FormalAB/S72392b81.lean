-- Source SHA-256: 2cbf3f872e4fb358edeede1e38f0c1f8bd28bd937990d615f4fc2e7de00b0271
import Mathlib
import JocelynWorkspace.Formalization.PowerfulCounting.CountingClosure.LemmaP
import JocelynWorkspace.Formalization.PowerfulCounting.FormalAB

namespace FormalAB.S72392b81

open Classical
open scoped BigOperators

namespace ConsecutiveCountingA5Source
noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000
set_option linter.all false

noncomputable def squareDivSum (n : ℕ) : ℤ :=
  ∑ d ∈ n.divisors, if d ^ 2 ∣ n then ArithmeticFunction.moebius d else 0

theorem squareDivSum_mul (a b : ℕ) (hab : a.Coprime b) :
    squareDivSum (a * b) = squareDivSum a * squareDivSum b := by
  unfold squareDivSum
  rw [hab.divisors_mul]
  simp only [Finset.sum_map]
  change (∑ z ∈ (a.divisors ×ˢ b.divisors).attach,
    if (z.val.1 * z.val.2) ^ 2 ∣ a * b then
      ArithmeticFunction.moebius (z.val.1 * z.val.2) else 0) = _
  rw [Finset.sum_attach (s := a.divisors ×ˢ b.divisors)
    (f := fun z : ℕ × ℕ => if (z.1 * z.2) ^ 2 ∣ a * b then
      ArithmeticFunction.moebius (z.1 * z.2) else 0),
    Finset.sum_product, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro e he
  have hda : d ∣ a := (Nat.mem_divisors.mp hd).1
  have heb : e ∣ b := (Nat.mem_divisors.mp he).1
  have hdB : d.Coprime b := Nat.Coprime.of_dvd_left hda hab
  have heA : e.Coprime a := Nat.Coprime.of_dvd_left heb hab.symm
  have hde : d.Coprime e := Nat.Coprime.of_dvd_right heb hdB
  have hcond : (d * e) ^ 2 ∣ a * b ↔ d ^ 2 ∣ a ∧ e ^ 2 ∣ b := by
    constructor
    · intro h
      have hda' : d ^ 2 ∣ a * b := dvd_trans
        (by rw [mul_pow]; exact dvd_mul_right _ _) h
      have heb' : e ^ 2 ∣ a * b := dvd_trans
        (by rw [mul_pow]; exact dvd_mul_left _ _) h
      exact ⟨Nat.Coprime.dvd_of_dvd_mul_right (Nat.Coprime.pow_left 2 hdB) hda',
        Nat.Coprime.dvd_of_dvd_mul_left (Nat.Coprime.pow_left 2 heA) heb'⟩
    · rintro ⟨hd2, he2⟩
      simpa only [mul_pow] using Nat.mul_dvd_mul hd2 he2
  have hmu : ArithmeticFunction.moebius (d * e) =
      ArithmeticFunction.moebius d * ArithmeticFunction.moebius e :=
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hde
  change (if (d * e) ^ 2 ∣ a * b then ArithmeticFunction.moebius (d * e) else 0) =
    (if d ^ 2 ∣ a then ArithmeticFunction.moebius d else 0) *
    (if e ^ 2 ∣ b then ArithmeticFunction.moebius e else 0)
  simp only [hcond, hmu]
  by_cases hd2 : d ^ 2 ∣ a <;> by_cases he2 : e ^ 2 ∣ b <;> simp [hd2, he2]

theorem squareDivSum_prime_pow (p k : ℕ) (hp : p.Prime) :
    squareDivSum (p ^ k) = ArithmeticFunction.moebius (p ^ k) ^ 2 := by
  have hcrit : p ^ 2 ∣ p ^ k ↔ 2 ≤ k := Nat.pow_dvd_pow_iff_le_right hp.one_lt
  have hterm : ∀ j : ℕ,
      (if (p ^ j) ^ 2 ∣ p ^ k then ArithmeticFunction.moebius (p ^ j) else 0) =
        (if j = 0 then (1 : ℤ) else 0) +
        (if j = 1 then (if 2 ≤ k then (-1 : ℤ) else 0) else 0) := by
    intro j
    by_cases hj0 : j = 0
    · subst j
      simp
    · by_cases hj1 : j = 1
      · subst j
        simp [hcrit, ArithmeticFunction.moebius_apply_prime hp]
      · simp [ArithmeticFunction.moebius_apply_prime_pow hp hj0, hj0, hj1]
  have hsum : squareDivSum (p ^ k) = 1 + (if 2 ≤ k then (-1 : ℤ) else 0) := by
    unfold squareDivSum
    rw [Nat.sum_divisors_prime_pow hp]
    calc
      _ = ∑ j ∈ Finset.range (k + 1),
          ((if j = 0 then (1 : ℤ) else 0) +
           (if j = 1 then (if 2 ≤ k then (-1 : ℤ) else 0) else 0)) := by
        apply Finset.sum_congr rfl
        intro j hj
        exact hterm j
      _ = _ := by
        rw [Finset.sum_add_distrib]
        simp only [Finset.sum_ite_eq', Finset.mem_range, Nat.zero_lt_succ, ite_true]
        by_cases hk2 : 2 ≤ k
        · have hk1 : 1 < k + 1 := by omega
          simp [hk1, hk2]
        · simp [hk2]
  rw [hsum]
  by_cases hk0 : k = 0
  · subst k
    norm_num
  · rw [ArithmeticFunction.moebius_apply_prime_pow hp hk0]
    by_cases hk1 : k = 1
    · subst k
      norm_num
    · have hk2 : 2 ≤ k := by omega
      simp [hk1, hk2]

theorem squareDivSum_eq (n : ℕ) :
    squareDivSum n = ArithmeticFunction.moebius n ^ 2 := by
  refine Nat.recOnPosPrimePosCoprime ?_ ?_ ?_ ?_ n
  · intro p k hp hk
    exact squareDivSum_prime_pow p k hp
  · simp [squareDivSum]
  · simp [squareDivSum]
  · intro a b ha hb hab hsa hsb
    rw [squareDivSum_mul a b hab, hsa, hsb,
      ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hab, mul_pow]

def kFree (k : ℕ) (n : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → ¬ p ^ k ∣ n

def kFreePairs (k : ℕ) (x : ℝ) : ℕ :=
  ((Finset.Icc 1 ⌊x⌋₊).filter
    (fun n => kFree k n ∧ kFree k (n + 1))).card

noncomputable def shortPairSum (x y : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
    ∑ d ∈ n.divisors, ∑ e ∈ (n + 1).divisors,
      if d ^ 2 ∣ n ∧ e ^ 2 ∣ n + 1 ∧ ((d * e : ℕ) : ℝ) ≤ y then
        ((ArithmeticFunction.moebius d * ArithmeticFunction.moebius e : ℤ) : ℝ)
      else 0

def largeDivisorTail (x y : ℝ) : Set ((ℕ × ℕ) × (ℕ × ℕ)) :=
  {q | 1 ≤ q.1.1 ∧ 1 ≤ q.1.2 ∧ 1 ≤ q.2.1 ∧ 1 ≤ q.2.2 ∧
    ((q.1.1 ^ 2 * q.2.1 : ℕ) : ℝ) ≤ x ∧
    q.1.2 ^ 2 * q.2.2 = q.1.1 ^ 2 * q.2.1 + 1 ∧
    y < ((q.1.1 * q.1.2 : ℕ) : ℝ)}

theorem squarefree_iff_kFree (n : ℕ) :
    Squarefree n ↔ kFree 2 n := by
  rw [Nat.squarefree_iff_prime_squarefree]
  simp only [kFree, pow_two]

theorem kFree_indicator (n : ℕ) :
    (if kFree 2 n then (1 : ℝ) else 0) =
      ∑ d ∈ n.divisors,
        if d ^ 2 ∣ n then (ArithmeticFunction.moebius d : ℝ) else 0 := by
  have h : (squareDivSum n : ℝ) =
      if kFree 2 n then (1 : ℝ) else 0 := by
    rw [squareDivSum_eq, ArithmeticFunction.moebius_sq]
    by_cases hn : kFree 2 n
    · simp [hn, (squarefree_iff_kFree n).mpr hn]
    · have hns : ¬ Squarefree n := fun hs => hn ((squarefree_iff_kFree n).mp hs)
      simp [hn, hns]
  rw [← h]
  simp [squareDivSum]

noncomputable def divisorTriples (x : ℝ) :
    Finset (Σ _ : ℕ, ℕ × ℕ) :=
  (Finset.Icc 1 ⌊x⌋₊).sigma
    (fun n => n.divisors ×ˢ (n + 1).divisors)

def admissibleTriple (t : Σ _ : ℕ, ℕ × ℕ) : Prop :=
  t.2.1 ^ 2 ∣ t.1 ∧ t.2.2 ^ 2 ∣ t.1 + 1

def pairWeight (t : Σ _ : ℕ, ℕ × ℕ) : ℝ :=
  ((ArithmeticFunction.moebius t.2.1 *
    ArithmeticFunction.moebius t.2.2 : ℤ) : ℝ)

noncomputable def badTriples (x y : ℝ) :
    Finset (Σ _ : ℕ, ℕ × ℕ) :=
  (divisorTriples x).filter (fun t =>
    admissibleTriple t ∧ y < ((t.2.1 * t.2.2 : ℕ) : ℝ))

theorem count_eq_sum (x : ℝ) :
    (kFreePairs 2 x : ℝ) =
      ∑ t ∈ divisorTriples x,
        if admissibleTriple t then pairWeight t else 0 := by
  unfold kFreePairs
  rw [Finset.card_filter]
  push_cast
  simp only [divisorTriples, Finset.sum_sigma, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro n hn
  calc
    (if kFree 2 n ∧ kFree 2 (n + 1) then (1 : ℝ) else 0) =
        (if kFree 2 n then (1 : ℝ) else 0) *
        (if kFree 2 (n + 1) then (1 : ℝ) else 0) := by
      by_cases h₁ : kFree 2 n <;> by_cases h₂ : kFree 2 (n + 1) <;> simp [h₁, h₂]
    _ = _ := by
      rw [kFree_indicator n, kFree_indicator (n + 1), Finset.sum_mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      apply Finset.sum_congr rfl
      intro e he
      by_cases hd₂ : d ^ 2 ∣ n <;> by_cases he₂ : e ^ 2 ∣ n + 1 <;>
        simp [admissibleTriple, pairWeight, hd₂, he₂]

theorem short_eq_sum (x y : ℝ) :
    shortPairSum x y =
      ∑ t ∈ divisorTriples x,
        if admissibleTriple t ∧ ((t.2.1 * t.2.2 : ℕ) : ℝ) ≤ y then
          pairWeight t else 0 := by
  simp only [shortPairSum, divisorTriples, Finset.sum_sigma,
    Finset.sum_product, admissibleTriple, pairWeight, and_assoc]

theorem difference_eq (x y : ℝ) :
    (kFreePairs 2 x : ℝ) - shortPairSum x y =
      ∑ t ∈ badTriples x y, pairWeight t := by
  rw [count_eq_sum, short_eq_sum, ← Finset.sum_sub_distrib]
  simp only [badTriples, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro t ht
  simp only [Nat.cast_mul]
  by_cases ht₁ : admissibleTriple t
  · by_cases ht₂ : (t.2.1 : ℝ) * (t.2.2 : ℝ) ≤ y
    · simp [ht₁, ht₂, not_lt.mpr ht₂]
    · simp [ht₁, ht₂, lt_of_not_ge ht₂]
  · simp [ht₁]

theorem weight_abs_le_one (t : Σ _ : ℕ, ℕ × ℕ) :
    |pairWeight t| ≤ 1 := by
  have hd : |(ArithmeticFunction.moebius t.2.1 : ℝ)| ≤ 1 := by
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := t.2.1)
  have he : |(ArithmeticFunction.moebius t.2.2 : ℝ)| ≤ 1 := by
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := t.2.2)
  dsimp [pairWeight]
  rw [Int.cast_mul, abs_mul]
  simpa using mul_le_mul hd he (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)

theorem difference_le_bad_card (x y : ℝ) :
    |(kFreePairs 2 x : ℝ) - shortPairSum x y| ≤
      ((badTriples x y).card : ℝ) := by
  rw [difference_eq]
  calc
    |∑ t ∈ badTriples x y, pairWeight t| ≤
        ∑ t ∈ badTriples x y, |pairWeight t| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _t ∈ badTriples x y, (1 : ℝ) :=
      Finset.sum_le_sum (fun t ht => weight_abs_le_one t)
    _ = _ := by simp

theorem positive_factor_bounds {d u N : ℕ}
    (hd : 1 ≤ d) (hu : 1 ≤ u) (hN : d ^ 2 * u ≤ N) :
    d ≤ N ∧ u ≤ N := by
  have hd₂ : d ≤ d ^ 2 := by
    simpa only [pow_two] using Nat.le_mul_self d
  have hsq : 0 < d ^ 2 := pow_pos (by omega : 0 < d) 2
  have hdN : d ^ 2 ≤ d ^ 2 * u :=
    Nat.le_mul_of_pos_right _ (by omega)
  have huN : u ≤ d ^ 2 * u := Nat.le_mul_of_pos_left _ hsq
  exact ⟨le_trans hd₂ (le_trans hdN hN), le_trans huN hN⟩

theorem tail_finite (x y : ℝ) :
    (largeDivisorTail x y).Finite := by
  let M := ⌊x⌋₊ + 1
  let box : Finset ((ℕ × ℕ) × (ℕ × ℕ)) :=
    ((Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M)) ×ˢ
      ((Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M))
  apply box.finite_toSet.subset
  rintro ⟨⟨d, e⟩, ⟨u, v⟩⟩ h
  rcases h with ⟨hd, he, hu, hv, hx, heq, hde⟩
  dsimp only at hd he hu hv hx heq hde
  have hn : d ^ 2 * u ≤ ⌊x⌋₊ := Nat.le_floor hx
  have hn' : e ^ 2 * v ≤ ⌊x⌋₊ + 1 := by omega
  rcases positive_factor_bounds hd hu hn with ⟨hdN, huN⟩
  rcases positive_factor_bounds he hv hn' with ⟨heN, hvN⟩
  change ((d, e), (u, v)) ∈ box
  simp only [box, Finset.mem_product, Finset.mem_Icc, M]
  omega

theorem bad_mem {x y : ℝ} {t : Σ _ : ℕ, ℕ × ℕ}
    (ht : t ∈ badTriples x y) :
    1 ≤ t.1 ∧ t.1 ≤ ⌊x⌋₊ ∧
    1 ≤ t.2.1 ∧ 1 ≤ t.2.2 ∧
    t.2.1 ^ 2 ∣ t.1 ∧ t.2.2 ^ 2 ∣ t.1 + 1 ∧
    y < ((t.2.1 * t.2.2 : ℕ) : ℝ) := by
  rcases Finset.mem_filter.mp ht with ⟨ht, hadm, hcut⟩
  rcases Finset.mem_sigma.mp ht with ⟨hn, hde⟩
  rcases Finset.mem_Icc.mp hn with ⟨hn₁, hn₂⟩
  rcases Finset.mem_product.mp hde with ⟨hd, he⟩
  have hdpos := Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp hd).1 (by omega : 0 < t.1)
  have hepos := Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp he).1 (by omega : 0 < t.1 + 1)
  exact ⟨hn₁, hn₂, by omega, by omega, hadm.1, hadm.2, hcut⟩

def tailMap (t : Σ _ : ℕ, ℕ × ℕ) :
    ((ℕ × ℕ) × (ℕ × ℕ)) :=
  ((t.2.1, t.2.2), (t.1 / t.2.1 ^ 2, (t.1 + 1) / t.2.2 ^ 2))

theorem tailMap_mem {x y : ℝ} (hx : 2 ≤ x)
    {t : Σ _ : ℕ, ℕ × ℕ} (ht : t ∈ badTriples x y) :
    tailMap t ∈ largeDivisorTail x y := by
  rcases bad_mem ht with ⟨hn, hnN, hd, he, hd₂, he₂, hcut⟩
  have hnpos : 0 < t.1 := by omega
  have hnpos' : 0 < t.1 + 1 := by omega
  have hdpos : 0 < t.2.1 ^ 2 := pow_pos (by omega) 2
  have hepos : 0 < t.2.2 ^ 2 := pow_pos (by omega) 2
  have hupos : 1 ≤ t.1 / t.2.1 ^ 2 := by
    have := Nat.div_pos (Nat.le_of_dvd hnpos hd₂) hdpos
    omega
  have hvpos : 1 ≤ (t.1 + 1) / t.2.2 ^ 2 := by
    have := Nat.div_pos (Nat.le_of_dvd hnpos' he₂) hepos
    omega
  have hdu := Nat.mul_div_cancel' hd₂
  have hev := Nat.mul_div_cancel' he₂
  change 1 ≤ t.2.1 ∧ 1 ≤ t.2.2 ∧
    1 ≤ t.1 / t.2.1 ^ 2 ∧ 1 ≤ (t.1 + 1) / t.2.2 ^ 2 ∧
    ((t.2.1 ^ 2 * (t.1 / t.2.1 ^ 2) : ℕ) : ℝ) ≤ x ∧
    t.2.2 ^ 2 * ((t.1 + 1) / t.2.2 ^ 2) =
      t.2.1 ^ 2 * (t.1 / t.2.1 ^ 2) + 1 ∧
    y < ((t.2.1 * t.2.2 : ℕ) : ℝ)
  refine ⟨hd, he, hupos, hvpos, ?_, ?_, hcut⟩
  · rw [hdu]
    exact le_trans (by exact_mod_cast hnN)
      (Nat.floor_le (by linarith : 0 ≤ x))
  · rw [hdu, hev]

theorem tailMap_injOn (x y : ℝ) :
    Set.InjOn tailMap (↑(badTriples x y) : Set (Σ _ : ℕ, ℕ × ℕ)) := by
  rintro ⟨n, d, e⟩ ha ⟨m, f, g⟩ hb hab
  have ha' := bad_mem ha
  have hb' := bad_mem hb
  have hd : d = f := congrArg (fun q : ((ℕ × ℕ) × (ℕ × ℕ)) => q.1.1) hab
  have he : e = g := congrArg (fun q : ((ℕ × ℕ) × (ℕ × ℕ)) => q.1.2) hab
  have hu : n / d ^ 2 = m / f ^ 2 :=
    congrArg (fun q : ((ℕ × ℕ) × (ℕ × ℕ)) => q.2.1) hab
  subst f
  subst g
  have hnd : d ^ 2 * (n / d ^ 2) = n := Nat.mul_div_cancel' ha'.2.2.2.2.1
  have hmd : d ^ 2 * (m / d ^ 2) = m := Nat.mul_div_cancel' hb'.2.2.2.2.1
  have hnm : n = m := by
    calc
      n = d ^ 2 * (n / d ^ 2) := hnd.symm
      _ = d ^ 2 * (m / d ^ 2) := congrArg (fun z : ℕ => d ^ 2 * z) hu
      _ = m := hmd
  subst m
  rfl

theorem bad_card_le_tail (x y : ℝ) (hx : 2 ≤ x) :
    (badTriples x y).card ≤ (largeDivisorTail x y).ncard := by
  have himage :
      (↑((badTriples x y).image tailMap) : Set ((ℕ × ℕ) × (ℕ × ℕ))) ⊆
        largeDivisorTail x y := by
    intro q hq
    rcases Finset.mem_image.mp hq with ⟨t, ht, rfl⟩
    exact tailMap_mem hx ht
  calc
    (badTriples x y).card = ((badTriples x y).image tailMap).card :=
      (Finset.card_image_of_injOn (tailMap_injOn x y)).symm
    _ = (↑((badTriples x y).image tailMap) :
        Set ((ℕ × ℕ) × (ℕ × ℕ))).ncard := (Set.ncard_coe_finset _).symm
    _ ≤ _ := Set.ncard_le_ncard himage (tail_finite x y)

theorem finite_truncation :
    ∀ (x y : ℝ), 2 ≤ x → 1 ≤ y →
      (largeDivisorTail x y).Finite ∧
      |(kFreePairs 2 x : ℝ) - shortPairSum x y| ≤
        ((largeDivisorTail x y).ncard : ℝ) := by
  intro x y hx hy
  refine ⟨tail_finite x y, ?_⟩
  exact le_trans (difference_le_bad_card x y)
    (by exact_mod_cast bad_card_le_tail x y hx)

#print axioms squareDivSum_eq
#print axioms finite_truncation

end
end ConsecutiveCountingA5Source

namespace JocelynClaims
 theorem claim_e8bb8e0b462198fe17c1922e04cabbde342a7da1d841c3a8181ba20a4d166b41 : let kFree : ℕ → ℕ → Prop := fun k n => ∀ p : ℕ, p.Prime → ¬ p ^ k ∣ n;
let kFreePairs : ℕ → ℝ → ℕ := fun k x => (by classical exact ((Finset.Icc 1 ⌊x⌋₊).filter (fun n => kFree k n ∧ kFree k (n + 1))).card);
let shortPairSum : ℝ → ℝ → ℝ := fun x y => Finset.sum (Finset.Icc 1 ⌊x⌋₊) (fun n => Finset.sum n.divisors (fun d => Finset.sum (n + 1).divisors (fun e => if d ^ 2 ∣ n ∧ e ^ 2 ∣ n + 1 ∧ ((d * e : ℕ) : ℝ) ≤ y then ((ArithmeticFunction.moebius d * ArithmeticFunction.moebius e : ℤ) : ℝ) else 0)));
let largeDivisorTail : ℝ → ℝ → Set ((ℕ × ℕ) × (ℕ × ℕ)) := fun x y => {q | 1 ≤ q.1.1 ∧ 1 ≤ q.1.2 ∧ 1 ≤ q.2.1 ∧ 1 ≤ q.2.2 ∧ ((q.1.1 ^ 2 * q.2.1 : ℕ) : ℝ) ≤ x ∧ q.1.2 ^ 2 * q.2.2 = q.1.1 ^ 2 * q.2.1 + 1 ∧ y < ((q.1.1 * q.1.2 : ℕ) : ℝ)};
∀ (x y : ℝ), 2 ≤ x → 1 ≤ y → (largeDivisorTail x y).Finite ∧ |(kFreePairs 2 x : ℝ) - shortPairSum x y| ≤ ((largeDivisorTail x y).ncard : ℝ) := by
  exact ConsecutiveCountingA5Source.finite_truncation
end JocelynClaims
#print axioms JocelynClaims.claim_e8bb8e0b462198fe17c1922e04cabbde342a7da1d841c3a8181ba20a4d166b41
